use ark_std::{end_timer, start_timer, Zero};
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    arithmetic::{BaseExt, FieldExt},
    circuit::{AssignedCell, Chip, Layouter, Region},
    plonk::{ConstraintSystem, Error},
};
use halo2ecc_s::circuit::fq12::Fq12ChipOps;
use halo2ecc_s::circuit::integer_chip::IntegerChipOps;
use halo2ecc_s::{
    assign::AssignedValue,
    circuit::{base_chip::BaseChipOps, ecc_chip::EccChipScalarOps},
};
use num_traits::{FromPrimitive, ToPrimitive};
use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

/*
halo2lib 中，base 是 fp, scalar 是 fq
bn254:   base: fq, scalar: Fr
 */
// base rename
use super::secp256r1::Fp as Bn256Fq;
// use halo2_proofs::pairing::bn256::Fq as Bn256Fq;
use super::secp256r1::{self, G1Affine};
// use halo2_proofs::pairing::bn256::G1Affine;

use halo2ecc_s::assign::{AssignedCondition, AssignedFq, AssignedInteger, Cell as ContextCell};
use halo2ecc_s::circuit::ecc_chip::EccBaseIntegerChipWrapper;
use halo2ecc_s::circuit::{ecc_chip::EccChipBaseOps, pairing_chip::PairingChipOps};

use halo2ecc_s::assign::{AssignedFq12, AssignedG2Affine, AssignedPoint};

use halo2ecc_s::{
    circuit::{
        base_chip::{BaseChip, BaseChipConfig},
        range_chip::{RangeChip, RangeChipConfig},
        select_chip::{SelectChip, SelectChipConfig},
    },
    context::{Context, GeneralScalarEccContext, IntegerContext, NativeScalarEccContext},
};

use crate::utils::Limb;
use num_bigint::{BigInt, BigUint};
use std::ops::{AddAssign, Mul};

#[derive(Clone, Debug)]
pub struct Bn256ChipConfig {
    base_chip_config: BaseChipConfig,
    range_chip_config: RangeChipConfig,
    point_select_chip_config: SelectChipConfig,
}

pub struct Bn256PairChip<N: FieldExt> {
    config: Bn256ChipConfig,
    base_chip: BaseChip<N>,
    pub range_chip: RangeChip<N>,
    point_select_chip: SelectChip<N>,
    _marker: PhantomData<N>,
}

impl<N: FieldExt> Chip<N> for Bn256PairChip<N> {
    type Config = Bn256ChipConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

pub fn fr_to_bn(f: &Fr) -> BigUint {
    let mut bytes: Vec<u8> = Vec::new();
    f.write(&mut bytes).unwrap();
    BigUint::from_bytes_le(&bytes[..])
}

pub fn fr_to_bool(f: &Fr) -> bool {
    let mut bytes: Vec<u8> = Vec::new();
    f.write(&mut bytes).unwrap();
    return bytes[0] == 1u8;
}

fn assigned_cells_to_bn256(
    a: &Vec<Limb<Fr>>, //G1 (3 * 2 + 1)
    start: usize,
) -> BigUint {
    let mut bn = BigUint::from(0 as u64);
    for i in start..start + 3 {
        let shift = BigUint::from(2 as u32).pow(108 * (i - start) as u32);
        bn.add_assign(fr_to_bn(&a[i].value).mul(shift.clone()));
    }
    bn
}

fn assemble_biguint(fr_slice: &[Fr; 3]) -> BigUint {
    let mut bn = BigUint::from(0 as u64);
    for (i, fr) in fr_slice.iter().enumerate() {
        let shift = BigUint::from(2 as u32).pow(108 * i as u32);
        bn.add_assign(fr_to_bn(fr).mul(shift.clone()));
    }
    println!(
        "assemble_biguint: fr[0]:{:?}, fr[1]:{:?}, fr[2]:{:?}. result: {:x}",
        fr_slice[0], fr_slice[1], fr_slice[2], bn
    );
    bn
}

fn split_biguint(v: &BigUint) -> [Fr; 3] {
    const BIT_COUNT: u32 = 108;
    const MASK: u128 = (1u128 << BIT_COUNT) - 1;

    let mask = BigUint::from_u128(MASK).unwrap();

    [
        Fr::from_u128((v & (&mask)).to_u128().unwrap()),
        Fr::from_u128(((v >> BIT_COUNT) & mask.clone()).to_u128().unwrap()),
        Fr::from_u128(((v >> BIT_COUNT * 2) & mask.clone()).to_u128().unwrap()), // TODO: assert no more than 40?
    ]
}

fn get_scalar_from_cell(
    // ctx: &mut NativeScalarEccContext<G1Affine>,
    ctx: &mut GeneralScalarEccContext<G1Affine, Fr>,
    a: Fr,
    // ) -> AssignedValue<Fr> {
) -> AssignedInteger<secp256r1::Fq, Fr> {
    println!("get_scalar_from_cell: {:?}", a);
    // let v = ctx.base_integer_chip().base_chip().assign(a);
    // TODO: 参数 a 需要 3 个 Fr, 然后转变成 BigUint, 实现 assign bigint
    let v = ctx
        .scalar_integer_ctx
        .assign_w(&assemble_biguint(&[a, Fr::zero(), Fr::zero()]));
    v
}

fn get_g1_from_cells(
    ctx: &mut GeneralScalarEccContext<G1Affine, Fr>,
    a: &Vec<Limb<Fr>>, //G1 (3 * 2 + 1)
) -> AssignedPoint<G1Affine, Fr> {
    let x_bn = assigned_cells_to_bn256(a, 0);
    let y_bn = assigned_cells_to_bn256(a, 3);
    let is_identity = fr_to_bool(&a[6].value);
    let x = ctx.base_integer_chip().assign_w(&x_bn);
    let y = ctx.base_integer_chip().assign_w(&y_bn);
    AssignedPoint::new(
        x,
        y,
        // AssignedCondition(ctx.0.ctx.borrow_mut().assign(if is_identity {
        // TODO: 确认是用 base_integer_chip 还是 scalar_integer_chip
        AssignedCondition(ctx.base_integer_chip().base_chip().assign(if is_identity {
            Fr::one()
        } else {
            Fr::zero()
        })),
    )
}

fn get_g2_from_cells(
    ctx: &mut GeneralScalarEccContext<G1Affine, Fr>,
    b: &Vec<Limb<Fr>>, //G2 (3 * 4 + 1)
) -> AssignedG2Affine<G1Affine, Fr> {
    let x1_bn = assigned_cells_to_bn256(b, 0);
    let x2_bn = assigned_cells_to_bn256(b, 3);
    let y1_bn = assigned_cells_to_bn256(b, 6);
    let y2_bn = assigned_cells_to_bn256(b, 9);
    let x1 = ctx.base_integer_chip().assign_w(&x1_bn);
    let x2 = ctx.base_integer_chip().assign_w(&x2_bn);
    let y1 = ctx.base_integer_chip().assign_w(&y1_bn);
    let y2 = ctx.base_integer_chip().assign_w(&y2_bn);
    let is_identity = fr_to_bool(&b[12].value);
    AssignedG2Affine::new(
        (x1, x2),
        (y1, y2),
        // AssignedCondition(ctx.0.ctx.borrow_mut().assign(if is_identity {
        // TODO: 确认是用 base_integer_chip 还是 scalar_integer_chip
        AssignedCondition(ctx.base_integer_chip().base_chip().assign(if is_identity {
            Fr::one()
        } else {
            Fr::zero()
        })),
    )
}

fn get_cell_of_ctx(
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    cell: &ContextCell,
) -> AssignedCell<Fr, Fr> {
    cells[cell.region as usize][cell.col][cell.row]
        .clone()
        .unwrap()
}

fn enable_fr_permute(
    region: &Region<Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    fr: &AssignedValue<Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    let limb = fr.cell;
    let limb_assigned = get_cell_of_ctx(cells, &limb);
    region.constrain_equal(input[0].get_the_cell().cell(), limb_assigned.cell())?;
    Ok(())
}

fn enable_scalar_permute(
    region: &Region<Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    scalar: &AssignedInteger<secp256r1::Fq, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    for i in 0..3 {
        let limb = scalar.limbs_le[i].cell;
        let limb_assigned = get_cell_of_ctx(cells, &limb);
        // TODO: constrain_equal for a
        // region.constrain_equal(input[i].get_the_cell().cell(), limb_assigned.cell())?;
    }
    Ok(())
}

// enable base permute
fn enable_fq_permute(
    region: &Region<Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    fq: &AssignedFq<Bn256Fq, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    for i in 0..3 {
        let limb = fq.limbs_le[i].cell;
        let limb_assigned = get_cell_of_ctx(cells, &limb);
        region.constrain_equal(input[i].get_the_cell().cell(), limb_assigned.cell())?;
    }
    Ok(())
}

fn enable_g1affine_permute(
    region: &Region<Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    point: &AssignedPoint<G1Affine, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    let mut inputs = input.chunks(3);
    enable_fq_permute(region, cells, &point.x, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &point.y, &inputs.next().unwrap().to_vec())?;
    let z_limb0 = point.z.0.cell;
    let z_limb0_assigned = get_cell_of_ctx(cells, &z_limb0);
    region.constrain_equal(input[6].get_the_cell().cell(), z_limb0_assigned.cell())?;
    Ok(())
}

fn enable_g2affine_permute(
    region: &Region<Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    point: &AssignedG2Affine<G1Affine, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    let mut inputs = input.chunks(3);
    enable_fq_permute(region, cells, &point.x.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &point.x.1, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &point.y.0, &inputs.next().unwrap().to_vec())?;
    enable_fq_permute(region, cells, &point.y.1, &inputs.next().unwrap().to_vec())?;
    let z_limb0 = point.z.0.cell;
    let z_limb0_assigned = get_cell_of_ctx(cells, &z_limb0);
    region.constrain_equal(input[12].get_the_cell().cell(), z_limb0_assigned.cell())?;
    Ok(())
}

fn enable_fq12_permute(
    region: &Region<Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    fq12: &AssignedFq12<Bn256Fq, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    let mut inputs = input.chunks(3);
    enable_fq_permute(
        region,
        cells,
        &fq12.0 .0 .0,
        &inputs.next().unwrap().to_vec(),
    )?;
    enable_fq_permute(
        region,
        cells,
        &fq12.0 .0 .1,
        &inputs.next().unwrap().to_vec(),
    )?;
    enable_fq_permute(
        region,
        cells,
        &fq12.0 .1 .0,
        &inputs.next().unwrap().to_vec(),
    )?;
    enable_fq_permute(
        region,
        cells,
        &fq12.0 .1 .1,
        &inputs.next().unwrap().to_vec(),
    )?;
    enable_fq_permute(
        region,
        cells,
        &fq12.0 .2 .0,
        &inputs.next().unwrap().to_vec(),
    )?;
    enable_fq_permute(
        region,
        cells,
        &fq12.0 .2 .1,
        &inputs.next().unwrap().to_vec(),
    )?;
    enable_fq_permute(
        region,
        cells,
        &fq12.1 .0 .0,
        &inputs.next().unwrap().to_vec(),
    )?;
    enable_fq_permute(
        region,
        cells,
        &fq12.1 .0 .1,
        &inputs.next().unwrap().to_vec(),
    )?;
    enable_fq_permute(
        region,
        cells,
        &fq12.1 .1 .0,
        &inputs.next().unwrap().to_vec(),
    )?;
    enable_fq_permute(
        region,
        cells,
        &fq12.1 .1 .1,
        &inputs.next().unwrap().to_vec(),
    )?;
    enable_fq_permute(
        region,
        cells,
        &fq12.1 .2 .0,
        &inputs.next().unwrap().to_vec(),
    )?;
    enable_fq_permute(
        region,
        cells,
        &fq12.1 .2 .1,
        &inputs.next().unwrap().to_vec(),
    )?;
    Ok(())
}

impl Bn256PairChip<Fr> {
    pub fn construct(config: <Self as Chip<Fr>>::Config) -> Self {
        Self {
            config: config.clone(),
            point_select_chip: SelectChip::<Fr>::new(config.point_select_chip_config),
            base_chip: BaseChip::new(config.base_chip_config),
            range_chip: RangeChip::<Fr>::new(config.range_chip_config),
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<Fr>) -> <Self as Chip<Fr>>::Config {
        Bn256ChipConfig {
            base_chip_config: BaseChip::configure(cs),
            range_chip_config: RangeChip::<Fr>::configure(cs),
            point_select_chip_config: SelectChip::configure(cs),
        }
    }

    /*
    pub fn load_bn256_pair_circuit(
        &self,
        a: &Vec<Limb<Fr>>,  //G1 (3 * 2 + 1)
        b: &Vec<Limb<Fr>>,  //G2 (3 * 4 + 1)
        ab: &Vec<Limb<Fr>>, // Fq_12 (3 * 12)
        layouter: &impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let context = Rc::new(RefCell::new(Context::new()));
        // let ctx = IntegerContext::<Bn256Fq, Fr>::new(context);
        // let mut ctx = GeneralScalarEccContext::new(ctx);
        let mut ctx = GeneralScalarEccContext::new(context);

        let a_g1 = get_g1_from_cells(&mut ctx, a);
        let b_g2 = get_g2_from_cells(&mut ctx, b);
        let ab_fq12_raw = ctx.pairing(&[(&a_g1, &b_g2)]);
        let ab_fq12 = ctx.fq12_reduce(&ab_fq12_raw);
        let records = Into::<Context<Fr>>::into(ctx).records;

        layouter.assign_region(
            || "base",
            |region| {
                let timer = start_timer!(|| "assign");
                let cells = records.assign_all(
                    &region,
                    &self.base_chip,
                    &self.range_chip,
                    &self.point_select_chip,
                )?;
                enable_g1affine_permute(region, &cells, &a_g1, a)?;
                enable_g2affine_permute(region, &cells, &b_g2, b)?;
                enable_fq12_permute(region, &cells, &ab_fq12, ab)?;
                end_timer!(timer);
                Ok(())
            },
        )?;
        Ok(())
    } */
}

pub struct Bn256SumChip<N: FieldExt> {
    config: Bn256ChipConfig,
    base_chip: BaseChip<N>,
    pub range_chip: RangeChip<N>,
    point_select_chip: SelectChip<N>,
    _marker: PhantomData<N>,
}

impl<N: FieldExt> Chip<N> for Bn256SumChip<N> {
    type Config = Bn256ChipConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl Bn256SumChip<Fr> {
    pub fn construct(config: <Self as Chip<Fr>>::Config) -> Self {
        Self {
            config: config.clone(),
            point_select_chip: SelectChip::<Fr>::new(config.point_select_chip_config),
            base_chip: BaseChip::new(config.base_chip_config),
            range_chip: RangeChip::<Fr>::new(config.range_chip_config),
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<Fr>) -> <Self as Chip<Fr>>::Config {
        Bn256ChipConfig {
            base_chip_config: BaseChip::configure(cs),
            range_chip_config: RangeChip::<Fr>::configure(cs),
            point_select_chip_config: SelectChip::configure(cs),
        }
    }

    /// ls:
    /// index:       0    | 1 |  2 3 4 | 5 6 7 |       8       | 9 10 11  | 12 13 14 |       15           |
    /// meaning: is_reset | a |   g_x  |  g_y  | g_is_identity | result_x | result_y | result_is_identity |
    ///                        \_________ point g ____________/ \__________ point result ________________/
    pub fn load_bn256_sum_circuit(
        &self,
        ls: &Vec<Limb<Fr>>, // n * (new, fr , g1, sum)
        layouter: &impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let context = Rc::new(RefCell::new(Context::new()));
        // let ctx = IntegerContext::<Bn256Fq, Fr>::new(context);
        // let mut ctx = NativeScalarEccContext(ctx, 0);
        let mut ctx = GeneralScalarEccContext::new(context);

        let mut ais = vec![];
        let mut g1s = vec![];
        let mut sums = vec![];
        let identity = ctx.assign_identity();
        let mut sum = identity.clone();
        for group in ls.chunks_exact(16) {
            // using constraint to fix if to reset
            let lhs = if group.get(0).unwrap().value != Fr::zero() {
                identity.clone()
            } else {
                sum
            };
            // assigned_cells_to_bn256(a, start)
            // 3 个 limb 表示 scalar, 7 个 limb 表示 point
            let a = get_scalar_from_cell(&mut ctx, group.get(1).unwrap().value);
            let g = get_g1_from_cells(&mut ctx, &group.get(2..9).unwrap().to_vec());
            let rhs = ctx.ecc_mul(&g, a.clone());
            // let sum_ret = ctx.ecc_add(&lhs, &rhs);
            // let sum_ret = ctx.ecc_reduce(&sum_ret);
            let sum_ret = ctx.ecc_reduce(&rhs);

            // ctx.0.ctx.borrow_mut().enable_permute(&sum_ret.z.0);
            // TODO: 应该用 base_integer_ctx 还是 scalar_integer_ctx?
            ctx.base_integer_chip()
                .base_chip()
                .enable_permute(&sum_ret.z.0);
            // ctx.0
            //     .ctx
            //     .borrow_mut()
            //     .enable_permute(&sum_ret.x.limbs_le[0]);
            ctx.base_integer_chip()
                .base_chip()
                .enable_permute(&sum_ret.x.limbs_le[0]);
            // ctx.0
            //     .ctx
            //     .borrow_mut()
            //     .enable_permute(&sum_ret.x.limbs_le[1]);
            ctx.base_integer_chip()
                .base_chip()
                .enable_permute(&sum_ret.x.limbs_le[1]);
            // ctx.0
            //     .ctx
            //     .borrow_mut()
            //     .enable_permute(&sum_ret.x.limbs_le[2]);
            ctx.base_integer_chip()
                .base_chip()
                .enable_permute(&sum_ret.x.limbs_le[2]);
            // ctx.0
            //     .ctx
            //     .borrow_mut()
            //     .enable_permute(&sum_ret.y.limbs_le[0]);
            ctx.base_integer_chip()
                .base_chip()
                .enable_permute(&sum_ret.y.limbs_le[0]);
            // ctx.0
            //     .ctx
            //     .borrow_mut()
            //     .enable_permute(&sum_ret.y.limbs_le[1]);
            ctx.base_integer_chip()
                .base_chip()
                .enable_permute(&sum_ret.y.limbs_le[1]);
            // ctx.0
            //     .ctx
            //     .borrow_mut()
            //     .enable_permute(&sum_ret.y.limbs_le[2]);
            ctx.base_integer_chip()
                .base_chip()
                .enable_permute(&sum_ret.y.limbs_le[2]);
            sum = ctx.to_point_with_curvature(sum_ret.clone());
            ais.push(a);
            g1s.push(g);
            sums.push(sum_ret);
        }

        let records = Into::<Context<Fr>>::into(ctx).records;
        layouter.assign_region(
            || "base",
            |mut region| {
                let timer = start_timer!(|| "assign");
                let cells = records.assign_all(
                    &mut region,
                    &self.base_chip,
                    &self.range_chip,
                    &self.point_select_chip,
                )?;
                ais.iter().enumerate().for_each(|(i, x)| {
                    // TODO
                    // enable_fr_permute(&mut region, &cells, x, &ls[16 * i + 1..16 * i + 2].to_vec())
                    //    .unwrap()
                    enable_scalar_permute(
                        &mut region,
                        &cells,
                        x,
                        &ls[16 * i + 1..16 * i + 2].to_vec(),
                    )
                    .unwrap();
                });
                g1s.iter().enumerate().for_each(|(i, x)| {
                    enable_g1affine_permute(
                        &mut region,
                        &cells,
                        x,
                        &ls[16 * i + 2..16 * i + 9].to_vec(),
                    )
                    .unwrap()
                });
                sums.iter().enumerate().for_each(|(i, x)| {
                    enable_g1affine_permute(
                        &mut region,
                        &cells,
                        x,
                        &ls[16 * i + 9..16 * i + 16].to_vec(),
                    )
                    .unwrap()
                });
                end_timer!(timer);
                Ok(())
            },
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Num;

    #[test]
    fn test_biguint_fr_convert() {
        // 0x7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978
        // 111110011110010011110110001100010001101 000000110100111101111110100010100101001000111000000000110000010010110101000110101100001111000000100010010110 100111100010011101111111001000011011001101011010011000001011010010001111110001000111011001101001100101111000

        let v = BigUint::from_str_radix(
            "7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978",
            16,
        )
        .unwrap();

        let res = split_biguint(&v);
        assert_eq!(res, [Fr::from_u128(0b100111100010011101111111001000011011001101011010011000001011010010001111110001000111011001101001100101111000), Fr::from_u128(0b000000110100111101111110100010100101001000111000000000110000010010110101000110101100001111000000100010010110), Fr::from_u128(0b111110011110010011110110001100010001101)]);
    }
}

#[cfg(test)]
mod circuits_test {
    use super::*;
    use ff::PrimeField;
    use halo2_proofs::{
        circuit::floor_planner::FlatFloorPlanner,
        dev::MockProver,
        plonk::{Advice, Circuit, Column},
    };
    use num_traits::Num;

    #[derive(Clone)]
    struct TestConfig {
        chip_config: Bn256ChipConfig,
        input: Column<Advice>,
    }

    #[derive(Debug, Default)]
    struct TestCircuit {
        a: Fr,
        g_x: [Fr; 3],
        g_y: [Fr; 3],
        g_is_identity: bool,
        res_x: [Fr; 3],
        res_y: [Fr; 3],
        res_is_identity: bool,
    }

    impl TestCircuit {
        fn assign_input(
            &self,
            input_column: &Column<Advice>,
            layouter: impl Layouter<Fr>,
        ) -> Result<Vec<Limb<Fr>>, Error> {
            layouter.assign_region(
                || "assign input region ",
                |region| {
                    let mut offset = 0;
                    let mut result = Vec::new();

                    let is_reset = Fr::one();

                    let is_reset_cell = Limb::new(
                        Some(region.assign_advice(
                            || "is reset",
                            input_column.clone(),
                            offset,
                            || Ok(is_reset),
                        )?),
                        is_reset,
                    );
                    offset += 1;
                    result.push(is_reset_cell);

                    let a_cell = Limb::new(
                        Some(region.assign_advice(
                            || "a",
                            input_column.clone(),
                            offset,
                            || Ok(self.a),
                        )?),
                        self.a,
                    );
                    offset += 1;
                    result.push(a_cell);

                    for g_x in self.g_x {
                        let cell = Limb::new(
                            Some(region.assign_advice(
                                || "g_x",
                                input_column.clone(),
                                offset,
                                || Ok(g_x),
                            )?),
                            g_x,
                        );
                        offset += 1;
                        result.push(cell);
                    }

                    for g_y in self.g_y {
                        let cell = Limb::new(
                            Some(region.assign_advice(
                                || "g_y",
                                input_column.clone(),
                                offset,
                                || Ok(g_y),
                            )?),
                            g_y,
                        );
                        offset += 1;
                        result.push(cell);
                    }

                    let g_is_identity = if self.g_is_identity {
                        Fr::one()
                    } else {
                        Fr::zero()
                    };
                    let cell = Limb::new(
                        Some(region.assign_advice(
                            || "g_is_identity",
                            input_column.clone(),
                            offset,
                            || Ok(g_is_identity),
                        )?),
                        g_is_identity,
                    );
                    offset += 1;
                    result.push(cell);

                    for res_x in self.res_x {
                        let cell = Limb::new(
                            Some(region.assign_advice(
                                || "res_x",
                                input_column.clone(),
                                offset,
                                || Ok(res_x),
                            )?),
                            res_x,
                        );
                        offset += 1;
                        result.push(cell);
                    }

                    for res_y in self.res_y {
                        let cell = Limb::new(
                            Some(region.assign_advice(
                                || "res_y",
                                input_column.clone(),
                                offset,
                                || Ok(res_y),
                            )?),
                            res_y,
                        );
                        offset += 1;
                        result.push(cell);
                    }

                    let res_is_identity = if self.res_is_identity {
                        Fr::one()
                    } else {
                        Fr::zero()
                    };
                    let cell = Limb::new(
                        Some(region.assign_advice(
                            || "res_is_identity",
                            input_column.clone(),
                            offset,
                            || Ok(res_is_identity),
                        )?),
                        res_is_identity,
                    );
                    offset += 1;
                    result.push(cell);

                    Ok(result)
                },
            )
        }
    }

    impl Circuit<Fr> for TestCircuit {
        type Config = TestConfig;
        type FloorPlanner = FlatFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            let input = meta.advice_column();
            meta.enable_equality(input);

            TestConfig {
                chip_config: Bn256SumChip::configure(meta),
                input,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let chip = Bn256SumChip::construct(config.chip_config);

            let inputs = self.assign_input(&config.input, layouter.namespace(|| "assign input"))?;

            chip.load_bn256_sum_circuit(&inputs, &layouter)
        }
    }

    #[test]
    fn test_prover() {
        // a=0x0000000000000000000000000000000000000000000000000000000000000002,
        // g=(0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296, 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5).
        // is_identity: false
        // g*a=(0x7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978, 0x07775510db8ed040293d9ac69f7430dbba7dade63ce982299e04b79d227873d1).
        // is_identity: false
        let circuit = TestCircuit {
            a: Fr::from_str_vartime("2").unwrap(),
            g_x: split_biguint(
                &BigUint::from_str_radix(
                    "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",
                    16,
                )
                .unwrap(),
            ),
            g_y: split_biguint(
                &BigUint::from_str_radix(
                    "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
                    16,
                )
                .unwrap(),
            ),
            g_is_identity: false,
            res_x: split_biguint(
                &BigUint::from_str_radix(
                    "7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978",
                    16,
                )
                .unwrap(),
            ),
            res_y: split_biguint(
                &BigUint::from_str_radix(
                    "07775510db8ed040293d9ac69f7430dbba7dade63ce982299e04b79d227873d1",
                    16,
                )
                .unwrap(),
            ),
            res_is_identity: false,
        };

        let prover = MockProver::run(23, &circuit, Vec::new()).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
