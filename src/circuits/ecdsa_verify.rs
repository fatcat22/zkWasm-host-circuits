use ark_std::{end_timer, start_timer, Zero};
use ff::PrimeField;
use group::prime::PrimeCurveAffine;
use group::Curve;
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
use num_traits::{FromPrimitive, Num, ToPrimitive};
use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

use super::secp256r1::{self, Secp256r1Affine};

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
    ctx: &mut GeneralScalarEccContext<Secp256r1Affine, Fr>,
    v: &[Limb<Fr>],
) -> (AssignedInteger<secp256r1::Fq, Fr>, secp256r1::Fq) {
    let w = assemble_biguint(&[v[0].value, v[1].value, v[2].value]);

    let v = ctx.scalar_integer_ctx.assign_w(&w);
    (
        v,
        secp256r1::Fq::from_str_vartime(&format!("{}", w)).unwrap(),
    )
}

fn get_g1_from_cells(
    ctx: &mut GeneralScalarEccContext<Secp256r1Affine, Fr>,
    a: &Vec<Limb<Fr>>, //G1 (3 * 2 + 1)
) -> (AssignedPoint<Secp256r1Affine, Fr>, Secp256r1Affine) {
    let x_bn = assigned_cells_to_bn256(a, 0);
    let y_bn = assigned_cells_to_bn256(a, 3);
    let is_identity = fr_to_bool(&a[6].value);
    println!(
        "x_bn:{:x}, y_bn:{:x}, is_identity:{}",
        x_bn, y_bn, is_identity
    );
    let x = ctx.base_integer_chip().assign_w(&x_bn);
    let y = ctx.base_integer_chip().assign_w(&y_bn);
    (
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
        ),
        Secp256r1Affine {
            x: secp256r1::Fp::from_str_vartime(&format!("{}", x_bn)).unwrap(),
            y: secp256r1::Fp::from_str_vartime(&format!("{}", y_bn)).unwrap(),
        },
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

fn enable_integer_permute<T: BaseExt>(
    region: &Region<Fr>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<Fr, Fr>>>>>,
    scalar: &AssignedInteger<T, Fr>,
    input: &Vec<Limb<Fr>>,
) -> Result<(), Error> {
    for i in 0..3 {
        let limb = scalar.limbs_le[i].cell;
        let limb_assigned = get_cell_of_ctx(cells, &limb);
        if let Some(v) = limb_assigned.value() {
            assert_eq!(&input[i].value, v);
        }
        region.constrain_equal(input[i].get_the_cell().cell(), limb_assigned.cell())?;
    }
    Ok(())
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

    /// ls[i]:
    /// index:   0 1 2 | 3 4 5 |        6       |   7 8 9  | 10 11 12 | 13 14 15 |
    /// meaning:  pk_x | pk_y  | pk_is_identity | msg_hash |    r     |     s    |
    pub fn load_bn256_sum_circuit(
        &self,
        ls: &Vec<Limb<Fr>>,
        layouter: &impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let context = Rc::new(RefCell::new(Context::new()));
        let mut ctx = GeneralScalarEccContext::new(context);

        let mut r_candidates = Vec::new();
        let g = Secp256r1Affine::generator().to_curve();
        // TODO: ctx.assign_nonzero_point is better?
        let g_point = ctx.assign_point(&g);
        for group in ls.chunks_exact(16) {
            // using constraint to fix if to reset
            // let lhs = if group.get(0).unwrap().value != Fr::zero() {
            //     identity.clone()
            // } else {
            //     sum
            // };

            let (pk, pk_) = get_g1_from_cells(&mut ctx, &group.get(0..7).unwrap().to_vec());
            let (msg_hash, msg_hash_) = get_scalar_from_cell(&mut ctx, group.get(7..10).unwrap());
            let (r, r_) = get_scalar_from_cell(&mut ctx, group.get(10..13).unwrap());
            let (s, s_) = get_scalar_from_cell(&mut ctx, group.get(13..16).unwrap());

            // TODO: test if constrain s*s_inv = 1 could save more rows.
            let s_inv = ctx.scalar_integer_ctx.int_unsafe_invert(&s);
            // let s_inv_ = s_.invert().unwrap();
            // let s_inv_ = ctx.scalar_integer_ctx.assign_w(
            //     &BigUint::from_str_radix(format!("{:?}", s_inv_).trim_start_matches("0x"), 16)
            //         .unwrap(),
            // );
            // ctx.scalar_integer_ctx.assert_int_equal(&s_inv_, &s_inv);

            // let u_1 = msg_hash * s_inv;
            let u_1 = ctx.scalar_integer_ctx.int_mul(&msg_hash, &s_inv);
            // let u_1_ = msg_hash_ * s_inv_;
            // let u_1_assign_ = ctx.scalar_integer_ctx.assign_w(
            //     &BigUint::from_str_radix(format!("{:?}", u_1_).trim_start_matches("0x"), 16)
            //         .unwrap(),
            // );
            // ctx.scalar_integer_ctx.assert_int_equal(&u_1_assign_, &u_1);

            // let u_2 = r * s_inv;
            let u_2 = ctx.scalar_integer_ctx.int_mul(&r, &s_inv);
            // let u_2_ = r_ * s_inv_;
            // let u_2_assign_ = ctx.scalar_integer_ctx.assign_w(
            //     &BigUint::from_str_radix(format!("{:?}", u_2_).trim_start_matches("0x"), 16)
            //         .unwrap(),
            // );
            // ctx.scalar_integer_ctx.assert_int_equal(&u_2_assign_, &u_2);

            // let v_1 = g * u_1;
            let v_1 = ctx.ecc_mul(&g_point, u_1);
            // let v_1_ = g * u_1_;
            // let v_1_assign_ = ctx.assign_point(&v_1_);
            // ctx.ecc_assert_equal(&v_1_assign_, &v_1);

            // let v_2 = pk * u_2
            let v_2 = ctx.ecc_mul(&pk, u_2);
            // let v_2_ = pk_ * u_2_;
            // let v_2_assign_ = ctx.assign_point(&v_2_);
            // ctx.ecc_assert_equal(&v_2_assign_, &v_2);

            // let r_point = (v_1 + v_2).to_affine().coordinates().unwrap();
            let v1_curvature = ctx.to_point_with_curvature(v_1.clone());
            let r_point = ctx.ecc_add(&v1_curvature, &v_2);
            // let r_point_ = (v_1_ + v_2_).to_affine();
            // let r_point_assign_ = ctx.assign_point(&r_point_.to_curve());
            // ctx.ecc_assert_equal(&r_point_assign_, &r_point);

            let r_candidate = r_point.x;
            let r_candidate = ctx.base_integer_chip().reduce(&r_candidate);
            let r_candidate = AssignedInteger::<secp256r1::Fq, Fr>::new(
                r_candidate.limbs_le,
                r_candidate.native,
                r_candidate.times + 1,
            );
            // TODO: still need enable_scalar_permute?
            ctx.scalar_integer_ctx.assert_int_equal(&r_candidate, &r);

            ctx.scalar_integer_ctx
                .base_chip()
                .enable_permute(&r_candidate.limbs_le[0]);
            ctx.base_integer_chip()
                .base_chip()
                .enable_permute(&r_candidate.limbs_le[1]);
            ctx.base_integer_chip()
                .base_chip()
                .enable_permute(&r_candidate.limbs_le[2]);

            r_candidates.push(r_candidate);
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

                r_candidates
                    .iter()
                    .enumerate()
                    .for_each(|(i, r_candidate)| {
                        enable_integer_permute(
                            &mut region,
                            &cells,
                            &r_candidate,
                            &ls[16 * i + 10..16 * i + 13].to_vec(),
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
    use crate::circuits::secp256r1::{Fp, Fq, Secp256r1, Secp256r1Affine};

    use super::*;
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
        chip_config: Bn256ChipConfig,
        input: Column<Advice>,
    }

    #[derive(Debug, PartialEq, Default)]
    struct TestCircuit {
        pk_x: [Fr; 3],
        pk_y: [Fr; 3],
        pk_is_identity: bool,
        msg_hash: [Fr; 3],
        r: [Fr; 3],
        s: [Fr; 3],
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

                    for x in self.pk_x {
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

                    for y in self.pk_y {
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

                    let pk_is_identity = if self.pk_is_identity {
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

                    for h in self.msg_hash {
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

                    for r_i in self.r {
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

                    for s_i in self.s {
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

            chip.range_chip.init_table(&layouter)?;
            chip.load_bn256_sum_circuit(&inputs, &layouter)
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

    #[test]
    fn test_prover() {
        const PK_X: &'static str =
            "aa8dc881f03127a54e2e0f96213b2d7e4d43eb1462e457577149cb961520249e";
        const PK_Y: &'static str =
            "f1df988ab3fa2f6796d683fdedd8500aed2ab1eb2e94c6d1a0bd9f1be80cb524";
        const MSG_HASH: &'static str =
            "f57c13a4d90f9b859d96f734007124333344cc37fdb25554161e41e75a89a36a";
        const R: &'static str = "7dc054cb09ec97c39c53e2356688ac76d83bdfb091d9c24126d49d355b2bd886";
        const S: &'static str = "0fa6d3a61da64c530036ade71d701564e39c9fa42062d86c9f48cf420caf6f04";

        {
            let msg_hash = from_hex_str::<Fq>(MSG_HASH);
            let r = from_hex_str::<Fq>(R);
            let s = from_hex_str::<Fq>(S);
            let g = Secp256r1::generator();
            let pk_affine = Secp256r1Affine {
                x: from_hex_str(PK_X),
                y: from_hex_str(PK_Y),
            };
            let pk = pk_affine.to_curve();

            // let r_point = (msg_hash * s_inv) * g + (r * s_inv) * pk
            // assert_eq!(r_point.x, r);

            let s_inv = s.invert().unwrap();
            let u_1 = msg_hash * s_inv;
            let u_2 = r * s_inv;

            let v_1 = g * u_1;
            let v_2 = pk * u_2;

            let r_point = (v_1 + v_2).to_affine().coordinates().unwrap();
            println!("r_point.x:{:?}\nr:{:?}", r_point.x(), r);
            let x_candidate = r_point.x();
            let r_candidate = mod_n(x_candidate);

            assert_eq!(r, r_candidate);
        }

        let circuit = TestCircuit {
            pk_x: split_biguint(&BigUint::from_str_radix(PK_X, 16).unwrap()),
            pk_y: split_biguint(&BigUint::from_str_radix(PK_Y, 16).unwrap()),
            pk_is_identity: false,

            msg_hash: split_biguint(&BigUint::from_str_radix(MSG_HASH, 16).unwrap()),
            r: split_biguint(&BigUint::from_str_radix(R, 16).unwrap()),
            s: split_biguint(&BigUint::from_str_radix(S, 16).unwrap()),
        };

        let prover = MockProver::run(23, &circuit, Vec::new()).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
