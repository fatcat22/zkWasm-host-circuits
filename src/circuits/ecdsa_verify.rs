use ark_std::{end_timer, start_timer};
use group::prime::PrimeCurveAffine;
use halo2_proofs::pairing::bn256::Fr;
use halo2_proofs::{
    arithmetic::{BaseExt, FieldExt},
    circuit::{AssignedCell, Chip, Layouter, Region},
    plonk::{ConstraintSystem, Error},
};
use halo2ecc_s::circuit::ecc_chip::EccChipScalarOps;
use halo2ecc_s::circuit::integer_chip::IntegerChipOps;
use num_traits::{FromPrimitive, Num, One, ToPrimitive};
use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

use super::secp256r1::{self, Secp256r1Affine};

use halo2ecc_s::assign::{AssignedCondition, AssignedInteger, Cell as ContextCell};
use halo2ecc_s::circuit::ecc_chip::EccBaseIntegerChipWrapper;
use halo2ecc_s::circuit::ecc_chip::EccChipBaseOps;

use halo2ecc_s::assign::AssignedPoint;

use halo2ecc_s::{
    circuit::{
        base_chip::{BaseChip, BaseChipConfig},
        range_chip::{RangeChip, RangeChipConfig},
        select_chip::{SelectChip, SelectChipConfig},
    },
    context::{Context, GeneralScalarEccContext},
};

use crate::utils::Limb;
use num_bigint::BigUint;
use std::ops::{AddAssign, Mul};

#[derive(Clone, Debug)]
pub struct EcdsaChipConfig {
    base_chip_config: BaseChipConfig,
    range_chip_config: RangeChipConfig,
    point_select_chip_config: SelectChipConfig,
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

fn assigned_cells_to_biguint(
    a: &[Limb<Fr>], //G1 (3 * 2 + 1)
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
    ctx: &mut GeneralScalarEccContext<Secp256r1Affine, Fr>,
    v: &[Limb<Fr>],
) -> AssignedInteger<secp256r1::Fq, Fr> {
    let w = assemble_biguint(&[v[0].value, v[1].value, v[2].value]);

    ctx.scalar_integer_ctx.assign_w(&w)
}

fn get_g1_from_xy_cells(
    ctx: &mut GeneralScalarEccContext<Secp256r1Affine, Fr>,
    x: &[Limb<Fr>], //G1 (3 * 2 + 1)
    y: &[Limb<Fr>], //G1 (3 * 2 + 1)
    is_identity: &Limb<Fr>,
) -> AssignedPoint<Secp256r1Affine, Fr> {
    let x_bn = assigned_cells_to_biguint(x, 0);
    let y_bn = assigned_cells_to_biguint(y, 0);
    let is_identity = fr_to_bool(&is_identity.value);
    let x = ctx.base_integer_chip().assign_w(&x_bn);
    let y = ctx.base_integer_chip().assign_w(&y_bn);
    AssignedPoint::new(
        x,
        y,
        // AssignedCondition(ctx.0.ctx.borrow_mut().assign(if is_identity {
        // TODO: 确认是用 base_integer_chip 还是 scalar_integer_chip
        // TODO: constrain z equals to is_identity paramter
        AssignedCondition(ctx.base_integer_chip().base_chip().assign(if is_identity {
            Fr::one()
        } else {
            Fr::zero()
        })),
    )
}

fn get_g1_from_cells(
    ctx: &mut GeneralScalarEccContext<Secp256r1Affine, Fr>,
    a: &[Limb<Fr>], //G1 (3 * 2 + 1)
) -> AssignedPoint<Secp256r1Affine, Fr> {
    get_g1_from_xy_cells(ctx, &a[0..3], &a[3..6], &a[6])
}

fn get_cell_of_ctx(
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    cell: &ContextCell,
) -> AssignedCell<Fr, Fr> {
    cells[cell.region as usize][cell.col][cell.row]
        .clone()
        .unwrap()
}

fn enable_point_permute(
    ctx: &mut GeneralScalarEccContext<Secp256r1Affine, Fr>,
    point: &AssignedPoint<Secp256r1Affine, Fr>,
) {
    for limb in &point.x.limbs_le {
        ctx.base_integer_chip().base_chip().enable_permute(&limb);
    }
    for limb in &point.y.limbs_le {
        ctx.base_integer_chip().base_chip().enable_permute(&limb);
    }
    ctx.base_integer_chip()
        .base_chip()
        .enable_permute(&point.z.0);
}

fn enable_integer_permute<T: BaseExt>(
    region: &Region<Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    scalar: &AssignedInteger<T, Fr>,
    expect: &AssignedInteger<T, Fr>,
) -> Result<(), Error> {
    for (s_limb, e_limb) in scalar.limbs_le.iter().zip(expect.limbs_le.iter()) {
        let s_cell = get_cell_of_ctx(cells, &s_limb.cell);
        let e_cell = get_cell_of_ctx(cells, &e_limb.cell);
        region.constrain_equal(s_cell.cell(), e_cell.cell())?;
    }
    Ok(())
}

fn enable_g1affine_identity_permute(
    region: &Region<Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    point: &AssignedPoint<Secp256r1Affine, Fr>,
    expect: &AssignedPoint<Secp256r1Affine, Fr>,
) -> Result<(), Error> {
    enable_integer_permute(region, cells, &point.x, &expect.x)?;
    enable_integer_permute(region, cells, &point.y, &expect.y)?;
    // TODO
    // let z_limb0 = point.z.0.cell;
    // let z_limb0_assigned = get_cell_of_ctx(cells, &z_limb0);
    // region.constrain_equal(input[6].get_the_cell().cell(), z_limb0_assigned.cell())?;
    Ok(())
}

pub struct EcdsaChip<N: FieldExt> {
    config: EcdsaChipConfig,
    base_chip: BaseChip<N>,
    pub range_chip: RangeChip<N>,
    point_select_chip: SelectChip<N>,
    _marker: PhantomData<N>,
}

impl<N: FieldExt> Chip<N> for EcdsaChip<N> {
    type Config = EcdsaChipConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl EcdsaChip<Fr> {
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
        EcdsaChipConfig {
            base_chip_config: BaseChip::configure(cs),
            range_chip_config: RangeChip::<Fr>::configure(cs),
            point_select_chip_config: SelectChip::configure(cs),
        }
    }

    /// ls[0]: lambda
    /// ls[i] when i > 0:
    /// index:   0 1 2 | 3 4 5 |        6       |   7 8 9  | 10 11 12 | 13 14 15 | 16 17 18 |       19
    /// meaning:  pk_x | pk_y  | pk_is_identity | msg_hash |    r     |     s    |    r_y   | r_is_identity
    pub fn verify_signatures(
        &self,
        ls: &Vec<Limb<Fr>>,
        layouter: &impl Layouter<Fr>,
    ) -> Result<(), Error> {
        if ls.is_empty() {
            return Ok(());
        }
        let context = Rc::new(RefCell::new(Context::new()));
        let mut ctx = GeneralScalarEccContext::new(context);

        // let mut r_candidates = Vec::new();
        let g = Secp256r1Affine::generator().to_curve();
        // TODO: ctx.assign_nonzero_point is better?
        let g_point = ctx.assign_constant_point(&g);

        // TODO: constrain lambda equals ls[0]
        let ls0 = ls.get(0).map(|v| v.value).unwrap_or(Fr::zero());
        let lambda = ctx.scalar_integer_ctx.assign_w(
            &BigUint::from_str_radix(format!("{:?}", ls0).strip_prefix("0x").unwrap(), 16).unwrap(),
        );

        let mut rlc_coff = ctx.scalar_integer_ctx.assign_w(&BigUint::one());

        let negtive_one = ctx
            .scalar_integer_ctx
            .assign_int_constant(-secp256r1::Fq::one());

        let ls = ls.get(1..).unwrap_or_default();

        let points = ls
            .chunks_exact(20)
            .map(|inputs| {
                let pk = get_g1_from_cells(&mut ctx, &inputs.get(0..7).unwrap().to_vec());
                let res = get_g1_from_xy_cells(
                    &mut ctx,
                    &inputs.get(10..13).unwrap(),
                    &inputs.get(16..19).unwrap(),
                    &inputs.get(19).unwrap(),
                );
                [g_point.clone(), pk, res]
            })
            .flatten()
            .collect::<Vec<_>>();

        let scalars = ls
            .chunks_exact(20)
            .enumerate()
            .map(|(i, inputs)| {
                let msg_hash = get_scalar_from_cell(&mut ctx, inputs.get(7..10).unwrap());
                let r = get_scalar_from_cell(&mut ctx, inputs.get(10..13).unwrap());
                let s = get_scalar_from_cell(&mut ctx, inputs.get(13..16).unwrap());

                // TODO: test if constrain s*s_inv = 1 could save more rows.
                let s_inv = ctx.scalar_integer_ctx.int_unsafe_invert(&s);

                // let u_1 = msg_hash * s_inv;
                let u_1 = ctx.scalar_integer_ctx.int_mul(&msg_hash, &s_inv);
                // let u_2 = r * s_inv;
                let u_2 = ctx.scalar_integer_ctx.int_mul(&r, &s_inv);

                let (u_1, u_2) = if i == 0 {
                    (u_1, u_2)
                } else {
                    let nu_1 = ctx.scalar_integer_ctx.int_mul(&rlc_coff, &u_1);
                    let nu_2 = ctx.scalar_integer_ctx.int_mul(&rlc_coff, &u_2);

                    (nu_1, nu_2)
                };
                let rhs_coff = ctx.scalar_integer_ctx.int_mul(&rlc_coff, &negtive_one);

                rlc_coff = ctx.scalar_integer_ctx.int_mul(&rlc_coff, &lambda);

                [u_1, u_2, rhs_coff]
            })
            .flatten()
            .collect::<Vec<_>>();

        let msm_res = ctx.msm(&points, &scalars);
        let msm_res = ctx.ecc_reduce(&msm_res);
        enable_point_permute(&mut ctx, &msm_res);

        let expect = ctx.assign_constant_point(
            &Secp256r1Affine {
                x: secp256r1::Fp::zero(),
                y: secp256r1::Fp::zero(),
            }
            .to_curve(),
        );
        enable_point_permute(&mut ctx, &expect);

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

                enable_g1affine_identity_permute(&mut region, &cells, &msm_res, &expect)?;

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
    use crate::circuits::secp256r1::{Fq, Secp256r1, Secp256r1Affine};
    use ff::PrimeField;
    use group::{prime::PrimeCurveAffine, Curve};
    use halo2_proofs::{
        arithmetic::CurveAffine,
        circuit::floor_planner::FlatFloorPlanner,
        dev::MockProver,
        plonk::{Advice, Circuit, Column},
    };
    use num_traits::Num;

    #[derive(Clone)]
    struct TestConfig {
        chip_config: EcdsaChipConfig,
        input: Column<Advice>,
    }

    #[derive(Debug, PartialEq, Default)]
    struct ECDSAInput {
        pk_x: [Fr; 3],
        pk_y: [Fr; 3],
        pk_is_identity: bool,
        msg_hash: [Fr; 3],
        r: [Fr; 3],
        s: [Fr; 3],
        r_y: [Fr; 3],
        r_is_identity: bool,
    }

    #[derive(Debug, PartialEq, Default)]
    struct TestCircuit {
        lambda: Fr,
        inputs: Vec<ECDSAInput>,
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

                    if self == &Self::default() {
                        return Ok(Vec::new());
                    }

                    let cell = Limb::new(
                        Some(region.assign_advice(
                            || "lambda",
                            input_column.clone(),
                            offset,
                            || Ok(self.lambda),
                        )?),
                        self.lambda,
                    );
                    offset += 1;
                    result.push(cell);

                    for input in &self.inputs {
                        for x in input.pk_x {
                            let cell = Limb::new(
                                Some(region.assign_advice(
                                    || "pk_x",
                                    input_column.clone(),
                                    offset,
                                    || Ok(x),
                                )?),
                                x,
                            );
                            offset += 1;
                            result.push(cell);
                        }

                        for y in input.pk_y {
                            let cell = Limb::new(
                                Some(region.assign_advice(
                                    || "pk_y",
                                    input_column.clone(),
                                    offset,
                                    || Ok(y),
                                )?),
                                y,
                            );
                            offset += 1;
                            result.push(cell);
                        }

                        let pk_is_identity = if input.pk_is_identity {
                            Fr::one()
                        } else {
                            Fr::zero()
                        };
                        let cell = Limb::new(
                            Some(region.assign_advice(
                                || "pk_is_identity",
                                input_column.clone(),
                                offset,
                                || Ok(pk_is_identity),
                            )?),
                            pk_is_identity,
                        );
                        offset += 1;
                        result.push(cell);

                        for h in input.msg_hash {
                            let cell = Limb::new(
                                Some(region.assign_advice(
                                    || "msg_hash",
                                    input_column.clone(),
                                    offset,
                                    || Ok(h),
                                )?),
                                h,
                            );
                            offset += 1;
                            result.push(cell);
                        }

                        for r_i in input.r {
                            let cell = Limb::new(
                                Some(region.assign_advice(
                                    || "r",
                                    input_column.clone(),
                                    offset,
                                    || Ok(r_i),
                                )?),
                                r_i,
                            );
                            offset += 1;
                            result.push(cell);
                        }

                        for s_i in input.s {
                            let cell = Limb::new(
                                Some(region.assign_advice(
                                    || "s_i",
                                    input_column.clone(),
                                    offset,
                                    || Ok(s_i),
                                )?),
                                s_i,
                            );
                            offset += 1;
                            result.push(cell);
                        }

                        for r_y_i in input.r_y {
                            let cell = Limb::new(
                                Some(region.assign_advice(
                                    || "r_y",
                                    input_column.clone(),
                                    offset,
                                    || Ok(r_y_i),
                                )?),
                                r_y_i,
                            );
                            offset += 1;
                            result.push(cell);
                        }

                        let r_is_identity = if input.r_is_identity {
                            Fr::one()
                        } else {
                            Fr::zero()
                        };
                        let cell = Limb::new(
                            Some(region.assign_advice(
                                || "r_is_identity",
                                input_column.clone(),
                                offset,
                                || Ok(r_is_identity),
                            )?),
                            r_is_identity,
                        );
                        offset += 1;
                        result.push(cell);
                    }

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
                chip_config: EcdsaChip::configure(meta),
                input,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            let chip = EcdsaChip::construct(config.chip_config);

            let inputs = self.assign_input(&config.input, layouter.namespace(|| "assign input"))?;

            chip.range_chip.init_table(&layouter)?;
            chip.verify_signatures(&inputs, &layouter)
        }
    }

    fn from_hex_str<T: PrimeField>(s: &str) -> T {
        T::from_str_vartime(&format!("{}", BigUint::from_str_radix(s, 16).unwrap())).unwrap()
    }

    fn mod_n(x: &secp256r1::Fp) -> secp256r1::Fq {
        let mut x_repr = [0u8; 32];
        x_repr.copy_from_slice(x.to_repr().as_ref());
        let mut x_bytes = [0u8; 64];
        x_bytes[..32].copy_from_slice(&x_repr[..]);
        secp256r1::Fq::from_uniform_bytes(&x_bytes)
    }

    pub fn to_biguint<F: PrimeField>(f: &F) -> BigUint {
        BigUint::from_str_radix(format!("{:?}", f).strip_prefix("0x").unwrap(), 16).unwrap()
    }

    pub fn modulus<F: PrimeField>() -> BigUint {
        to_biguint(&-F::one()) + 1u64
    }

    #[test]
    fn test_prover() {
        let g = Secp256r1::generator();

        let inputs = (0..340)
            .into_iter()
            .map(|_| {
                let sk = Fq::rand();
                let pk = Secp256r1Affine::from(g * sk);
                let msg_hash = Fq::rand();

                let k = Fq::rand();
                let k_inv = k.invert().unwrap();

                let r_affine = Secp256r1Affine::from(g * k);
                let r_point = r_affine.coordinates().unwrap();
                let x = r_point.x();
                let y = r_point.y();
                let x_bigint = to_biguint(x);
                let y_bigint = to_biguint(y);
                let r_is_identity = bool::from(r_affine.is_identity());

                let r = from_hex_str::<Fq>(&format!("{:x}", x_bigint % modulus::<Fq>()));
                let r_y = from_hex_str::<Fq>(&format!("{:x}", y_bigint % modulus::<Fq>()));
                let s = k_inv * (msg_hash + (r * sk));

                let input = ECDSAInput {
                    pk_x: split_biguint(&to_biguint(&pk.x)),
                    pk_y: split_biguint(&to_biguint(&pk.y)),
                    pk_is_identity: false,

                    msg_hash: split_biguint(&to_biguint(&msg_hash)),
                    r: split_biguint(&to_biguint(&r)),
                    s: split_biguint(&to_biguint(&s)),
                    r_y: split_biguint(&to_biguint(&r_y)),
                    r_is_identity,
                };

                // check input data
                // let r_point = (msg_hash * s_inv) * g + (r * s_inv) * pk
                // assert_eq!(r_point.x, r);
                {
                    println!("r: {:?}", r);
                    println!("s: {:?}", s);
                    println!("msghash: {:?}", msg_hash);
                    println!("pk: {:?}", pk);

                    let pk = pk.to_curve();
                    let s_inv = s.invert().unwrap();
                    let u_1 = msg_hash * s_inv;
                    let u_2 = r * s_inv;

                    let v_1 = g * u_1;
                    let v_2 = pk * u_2;

                    let r_point = (v_1 + v_2).to_affine().coordinates().unwrap();
                    let x_candidate = r_point.x();
                    let r_candidate = mod_n(x_candidate);

                    assert_eq!(r, r_candidate);
                }

                input
            })
            .collect();

        let circuit = TestCircuit {
            lambda: Fr::rand(),
            inputs,
        };

        let prover = MockProver::run(23, &circuit, Vec::new()).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
