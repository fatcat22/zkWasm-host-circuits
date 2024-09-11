use crate::{
    circuits::{
        ecdsa::{EcdsaChip, EcdsaChipConfig},
        host::{HostOpConfig, HostOpSelector},
    },
    host::{ecdsa, secp256r1, ExternalHostCallEntry, ForeignInst},
    proof::HostExtraInput,
    utils::Limb,
};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region},
    pairing::bn256::Fr,
    plonk::{Advice, Column, ConstraintSystem, Error},
};

struct EcdsaNumberPattern {
    /// The count of `u64` values required to represent this number when split
    count_of_u64: usize,
    /// The maximal actual bit count of the `u64` value represent when split.
    bits_count: usize,
    /// the scheme that merge those `u64` values to assigned values.
    /// The sum of each element in this slice must equal `count_of_u64`.
    /// for example, if the `merge_scheme` is [2, 2, 1], that means
    /// merge the first two u64 to a assigned value, and merge the second two u64
    /// to another assigned value, and make the 5th u64 to another assigned value.
    merge_scheme: &'static [usize],
}

const ECDSA_FIELD_PATTERN: EcdsaNumberPattern = EcdsaNumberPattern {
    count_of_u64: 5,
    bits_count: 54,
    merge_scheme: &[2, 2, 1],
};

const ECDSA_IS_IDENTITY_PATTERN: EcdsaNumberPattern = EcdsaNumberPattern {
    count_of_u64: 1,
    bits_count: 64,
    merge_scheme: &[1],
};

const ECDSA_GROUP_PATTERN: &[&'static EcdsaNumberPattern] = &[
    // pk.x
    &ECDSA_FIELD_PATTERN,
    // pk.y
    &ECDSA_FIELD_PATTERN,
    // pk.is_identity
    &ECDSA_IS_IDENTITY_PATTERN,
    // msg_hash
    &ECDSA_FIELD_PATTERN,
    // r
    &ECDSA_FIELD_PATTERN,
    // s
    &ECDSA_FIELD_PATTERN,
    // r_y
    &ECDSA_FIELD_PATTERN,
    // r_is_identity
    &ECDSA_IS_IDENTITY_PATTERN,
];

/// how many signatures can be verify at a time when k equal 22.
const TOTAL_CONSTRUCTIONS: usize = 170;

impl HostOpSelector for EcdsaChip<Fr> {
    type Config = EcdsaChipConfig;
    type Helper = ();
    fn configure(
        meta: &mut ConstraintSystem<Fr>,
        _shared_advices: &Vec<Column<Advice>>,
    ) -> Self::Config {
        Self::configure(meta)
    }

    fn construct(c: Self::Config) -> Self {
        Self::construct(c)
    }

    fn max_rounds(k: usize) -> usize {
        super::get_max_round(k, TOTAL_CONSTRUCTIONS)
    }

    fn opcodes() -> Vec<Fr> {
        vec![
            Fr::from(ForeignInst::EcdsaNew as u64),
            Fr::from(ForeignInst::EcdsaPush as u64),
        ]
    }

    fn assign(
        region: &Region<Fr>,
        k: usize,
        offset: &mut usize,
        shared_operands: &Vec<Fr>,
        shared_opcodes: &Vec<Fr>,
        config: &HostOpConfig,
    ) -> Result<Vec<Limb<Fr>>, Error> {
        let opcodes = Self::opcodes();
        let chunk_size: usize = ECDSA_GROUP_PATTERN.iter().map(|p| p.count_of_u64).sum();
        let selected_entries =
            super::get_selected_entries(shared_operands, shared_opcodes, &opcodes);
        assert!(selected_entries.len() % chunk_size == 0);
        let total_used_instructions = selected_entries.len() / chunk_size;

        assert_eq!(*offset, 0);

        let mut r = Vec::new();

        r.append(&mut assign_entries(
            region,
            offset,
            config,
            selected_entries,
            true,
        )?);

        let total_avail_rounds = Self::max_rounds(k);
        assert!(total_avail_rounds >= total_used_instructions);
        r.append(&mut assign_default(
            region,
            offset,
            config,
            total_avail_rounds - total_used_instructions,
        )?);

        Ok(r)
    }

    fn synthesize_separate(
        &mut self,
        arg_cells: &Vec<Limb<Fr>>,
        extra: &HostExtraInput<Fr>,
        layouter: &impl Layouter<Fr>,
    ) -> Result<(), Error> {
        self.range_chip.init_table(layouter)?;
        self.verify::<secp256r1::Secp256r1Affine>(extra, &arg_cells, layouter)?;
        Ok(())
    }

    fn synthesize(
        &mut self,
        _offset: &mut usize,
        _arg_cells: &Vec<Limb<Fr>>,
        _extra: &HostExtraInput<Fr>,
        _region: &Region<Fr>,
        _helper: &(),
    ) -> Result<(), Error> {
        Ok(())
    }
}

fn assign_default(
    region: &Region<Fr>,
    offset: &mut usize,
    config: &HostOpConfig,
    default_round: usize,
) -> Result<Vec<Limb<Fr>>, Error> {
    let default_table = build_default_table();
    let default_entries: Vec<((Fr, Fr), Fr)> = default_table
        .into_iter()
        .map(|x| ((Fr::from(x.value), Fr::from(x.op as u64)), Fr::zero()))
        .collect::<Vec<((Fr, Fr), Fr)>>();

    let default_entries = default_entries.repeat(default_round);

    assign_entries(region, offset, config, default_entries, false)
}

fn assign_entries(
    region: &Region<Fr>,
    offset: &mut usize,
    config: &HostOpConfig,
    entries: Vec<((Fr, Fr), Fr)>,
    enable: bool,
) -> Result<Vec<Limb<Fr>>, Error> {
    let chunk_size: usize = ECDSA_GROUP_PATTERN.iter().map(|p| p.count_of_u64).sum();

    let mut result = Vec::new();

    for group in entries.chunks_exact(chunk_size) {
        let mut start = 0;
        for pattern in ECDSA_GROUP_PATTERN {
            let limbs = assign_number(
                region,
                offset,
                config,
                group.get(start..(start + pattern.count_of_u64)).unwrap(),
                pattern,
                enable,
            )?;

            result.extend(limbs.into_iter().map(|(oprand, _)| oprand));
            start += pattern.count_of_u64;
        }
    }

    Ok(result)
}

fn assign_number(
    region: &Region<Fr>,
    offset: &mut usize,
    config: &HostOpConfig,
    group: &[((Fr, Fr), Fr)],
    pattern: &EcdsaNumberPattern,
    enable: bool,
) -> Result<Vec<(Limb<Fr>, Limb<Fr>)>, Error> {
    let mut start = 0;
    let mut result = Vec::new();

    for merge_count in pattern.merge_scheme {
        let limbs = if *merge_count == 1 {
            let ((operand, opcode), index) = *group.get(start).unwrap();
            assign_one(region, offset, config, operand, opcode, index, enable)?
        } else {
            assign_merged(
                region,
                offset,
                config,
                group[start..(start + merge_count)].iter().collect(),
                Fr::from_u128(1u128 << pattern.bits_count),
                enable,
            )?
        };

        result.push(limbs);
        start += merge_count;
    }

    Ok(result)
}

fn assign_one(
    region: &Region<Fr>,
    offset: &mut usize,
    config: &HostOpConfig,
    operand: Fr,
    opcode: Fr,
    index: Fr,
    enable: bool,
) -> Result<(Limb<Fr>, Limb<Fr>), Error> {
    config.assign_one_line(
        region,
        offset,
        operand,
        opcode,
        index,
        operand,
        Fr::zero(),
        enable,
    )
}

fn assign_merged(
    region: &Region<Fr>,
    offset: &mut usize,
    config: &HostOpConfig,
    values: Vec<&((Fr, Fr), Fr)>, //(operand, opcode), index
    indicator: Fr,
    enable: bool,
) -> Result<(Limb<Fr>, Limb<Fr>), Error> {
    config.assign_merged_operands(region, offset, values, indicator, enable)
}

fn build_default_table() -> Vec<ExternalHostCallEntry> {
    let materials = ecdsa::utils::EcdsaSignatureMaterials::<secp256r1::Secp256r1Affine>::default();
    ecdsa::utils::create_ecdsa_call_entries(&materials)
}
