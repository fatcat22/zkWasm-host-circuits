use ark_std::{end_timer, start_timer};
use ff::Field;
use halo2_proofs::arithmetic::CurveAffine;
use halo2_proofs::plonk::{Column, Instance};
use halo2_proofs::{
    arithmetic::{BaseExt, FieldExt},
    circuit::{AssignedCell, Chip, Layouter, Region},
    plonk::{ConstraintSystem, Error},
};
use halo2ecc_s::circuit::ecc_chip::EccChipScalarOps;
use halo2ecc_s::circuit::integer_chip::IntegerChipOps;
use num_traits::{Num, One};
use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

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

use crate::proof::HostExtraInput;
use crate::utils::Limb;
use num_bigint::BigUint;
use std::ops::{AddAssign, Mul};

#[derive(Clone, Debug)]
pub struct EcdsaChipConfig {
    base_chip_config: BaseChipConfig,
    range_chip_config: RangeChipConfig,
    point_select_chip_config: SelectChipConfig,
    commitment: Column<Instance>,
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

impl<N: FieldExt> EcdsaChip<N> {
    pub fn construct(config: <Self as Chip<N>>::Config) -> Self {
        Self {
            config: config.clone(),
            point_select_chip: SelectChip::<N>::new(config.point_select_chip_config),
            base_chip: BaseChip::new(config.base_chip_config),
            range_chip: RangeChip::<N>::new(config.range_chip_config),
            _marker: PhantomData,
        }
    }

    pub fn configure(cs: &mut ConstraintSystem<N>) -> <Self as Chip<N>>::Config {
        let commitment = cs.instance_column();
        cs.enable_equality(commitment);

        EcdsaChipConfig {
            base_chip_config: BaseChip::configure(cs),
            range_chip_config: RangeChip::<N>::configure(cs),
            point_select_chip_config: SelectChip::configure(cs),
            commitment,
        }
    }

    /// ls[0]: lambda
    /// ls[i] when i > 0:
    /// index:   0 1 2 | 3 4 5 |        6       |   7 8 9  | 10 11 12 | 13 14 15 | 16 17 18 |       19
    /// meaning:  pk_x | pk_y  | pk_is_identity | msg_hash |    r     |     s    |    r_y   | r_is_identity
    pub fn verify<C: CurveAffine>(
        &self,
        extra: &HostExtraInput<N>,
        ls: &Vec<Limb<N>>,
        layouter: &impl Layouter<N>,
    ) -> Result<(), Error> {
        let context = Rc::new(RefCell::new(Context::new()));
        let mut ctx = GeneralScalarEccContext::<C, _>::new(context);

        // prepare some inmutable variables
        let g = ctx.assign_constant_point(&C::generator().to_curve());
        let lambda = BigUint::from_str_radix(
            format!("{:?}", extra.commitment.unwrap_or(N::zero()))
                .strip_prefix("0x")
                .unwrap(),
            16,
        )
        .unwrap();
        let lambda = ctx.scalar_integer_ctx.assign_w(&lambda);

        let negtive_one = ctx
            .scalar_integer_ctx
            .assign_int_constant(-C::ScalarExt::one());

        // collect points for msm
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
                [g.clone(), pk, res]
            })
            .flatten()
            .collect::<Vec<_>>();

        let mut rlc_coff = ctx.scalar_integer_ctx.assign_w(&BigUint::one());

        // collect scalars for msm
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

        assert_eq!(points.len(), scalars.len());
        let result = ctx.msm(&points, &scalars);
        let result = ctx.ecc_reduce(&result);
        enable_point_permute(&mut ctx, &result);

        let expect = ctx.assign_constant_point(
            &C::from_xy(C::Base::zero(), C::Base::zero())
                .unwrap()
                .to_curve(),
        );
        enable_point_permute(&mut ctx, &expect);

        let records = Into::<Context<N>>::into(ctx).records;
        let assigned_lambda_native = layouter.assign_region(
            || "assign ecdsa verify",
            |mut region| {
                let timer = start_timer!(|| "assign ecdsa verify");
                let cells = records.assign_all(
                    &mut region,
                    &self.base_chip,
                    &self.range_chip,
                    &self.point_select_chip,
                )?;

                enable_g1affine_identity_permute(&mut region, &cells, &result, &expect)?;

                end_timer!(timer);
                Ok(get_cell_of_ctx(&cells, &lambda.native.cell))
            },
        )?;

        layouter.constrain_instance(assigned_lambda_native.cell(), self.config.commitment, 0)?;
        Ok(())
    }
}

fn field_to_bn<N: FieldExt>(f: &N) -> BigUint {
    let mut bytes: Vec<u8> = Vec::new();
    f.write(&mut bytes).unwrap();
    BigUint::from_bytes_le(&bytes[..])
}

fn field_to_bool<N: FieldExt>(f: &N) -> bool {
    let mut bytes: Vec<u8> = Vec::new();
    f.write(&mut bytes).unwrap();
    return bytes[0] == 1u8;
}

fn assigned_cells_to_biguint<N: FieldExt>(a: &[Limb<N>]) -> BigUint {
    let mut bn = BigUint::from(0 as u64);
    for i in 0..3 {
        let shift = BigUint::from(2 as u32).pow(108 * i as u32);
        bn.add_assign(field_to_bn(&a[i].value).mul(shift.clone()));
    }
    bn
}

fn assemble_biguint<N: FieldExt>(fr_slice: &[N; 3]) -> BigUint {
    let mut bn = BigUint::from(0 as u64);
    for (i, fr) in fr_slice.iter().enumerate() {
        let shift = BigUint::from(2 as u32).pow(108 * i as u32);
        bn.add_assign(field_to_bn(fr).mul(shift.clone()));
    }
    bn
}

fn get_scalar_from_cell<C: CurveAffine, N: FieldExt>(
    ctx: &mut GeneralScalarEccContext<C, N>,
    v: &[Limb<N>],
) -> AssignedInteger<C::ScalarExt, N> {
    let w = assemble_biguint(&[v[0].value, v[1].value, v[2].value]);

    ctx.scalar_integer_ctx.assign_w(&w)
}

fn get_g1_from_xy_cells<C: CurveAffine, N: FieldExt>(
    ctx: &mut GeneralScalarEccContext<C, N>,
    x: &[Limb<N>], //G1 (3 * 2 + 1)
    y: &[Limb<N>], //G1 (3 * 2 + 1)
    is_identity: &Limb<N>,
) -> AssignedPoint<C, N> {
    let x_bn = assigned_cells_to_biguint(x);
    let y_bn = assigned_cells_to_biguint(y);
    let is_identity = field_to_bool(&is_identity.value);
    let x = ctx.base_integer_chip().assign_w(&x_bn);
    let y = ctx.base_integer_chip().assign_w(&y_bn);
    AssignedPoint::new(
        x,
        y,
        // AssignedCondition(ctx.0.ctx.borrow_mut().assign(if is_identity {
        // TODO: 确认是用 base_integer_chip 还是 scalar_integer_chip
        // TODO: constrain z equals to is_identity paramter
        AssignedCondition(ctx.base_integer_chip().base_chip().assign(if is_identity {
            N::one()
        } else {
            N::zero()
        })),
    )
}

fn get_g1_from_cells<C: CurveAffine, N: FieldExt>(
    ctx: &mut GeneralScalarEccContext<C, N>,
    a: &[Limb<N>],
) -> AssignedPoint<C, N> {
    get_g1_from_xy_cells(ctx, &a[0..3], &a[3..6], &a[6])
}

fn get_cell_of_ctx<N: FieldExt>(
    cells: &Vec<Vec<Vec<Option<AssignedCell<N, N>>>>>,
    cell: &ContextCell,
) -> AssignedCell<N, N> {
    cells[cell.region as usize][cell.col][cell.row]
        .clone()
        .unwrap()
}

fn enable_point_permute<C: CurveAffine, N: FieldExt>(
    ctx: &mut GeneralScalarEccContext<C, N>,
    point: &AssignedPoint<C, N>,
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

fn enable_integer_permute<T: BaseExt, N: FieldExt>(
    region: &Region<N>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<N, N>>>>>,
    scalar: &AssignedInteger<T, N>,
    expect: &AssignedInteger<T, N>,
) -> Result<(), Error> {
    for (s_limb, e_limb) in scalar.limbs_le.iter().zip(expect.limbs_le.iter()) {
        assert_eq!(s_limb.val, e_limb.val);
        let s_cell = get_cell_of_ctx(cells, &s_limb.cell);
        let e_cell = get_cell_of_ctx(cells, &e_limb.cell);
        region.constrain_equal(s_cell.cell(), e_cell.cell())?;
    }
    Ok(())
}

fn enable_g1affine_identity_permute<C: CurveAffine, N: FieldExt>(
    region: &Region<N>,
    cells: &Vec<Vec<Vec<Option<AssignedCell<N, N>>>>>,
    point: &AssignedPoint<C, N>,
    expect: &AssignedPoint<C, N>,
) -> Result<(), Error> {
    enable_integer_permute(region, cells, &point.x, &expect.x)?;
    enable_integer_permute(region, cells, &point.y, &expect.y)?;
    // TODO
    // let z_limb0 = point.z.0.cell;
    // let z_limb0_assigned = get_cell_of_ctx(cells, &z_limb0);
    // region.constrain_equal(input[6].get_the_cell().cell(), z_limb0_assigned.cell())?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::pairing::bn256::Fr;
    use num_traits::Num;

    #[test]
    fn test_split_biguint() {
        // 0x7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978
        // 111110011110010011110110001100010001101 000000110100111101111110100010100101001000111000000000110000010010110101000110101100001111000000100010010110 100111100010011101111111001000011011001101011010011000001011010010001111110001000111011001101001100101111000

        let v = BigUint::from_str_radix(
            "7cf27b188d034f7e8a52380304b51ac3c08969e277f21b35a60b48fc47669978",
            16,
        )
        .unwrap();

        let res = super::circuits_test::split_biguint::<Fr>(&v);
        assert_eq!(res, [Fr::from_u128(0b100111100010011101111111001000011011001101011010011000001011010010001111110001000111011001101001100101111000), Fr::from_u128(0b000000110100111101111110100010100101001000111000000000110000010010110101000110101100001111000000100010010110), Fr::from_u128(0b111110011110010011110110001100010001101)]);
    }
}

#[cfg(test)]
pub mod circuits_test {
    use super::*;
    use crate::host::ecdsa::{self, utils::EcdsaSignatureMaterials};
    use ff::PrimeField;
    use halo2_proofs::{
        arithmetic::CurveAffine,
        circuit::floor_planner::FlatFloorPlanner,
        dev::MockProver,
        plonk::{Advice, Circuit, Column},
    };
    use num_traits::Num;
    use num_traits::{FromPrimitive, ToPrimitive};

    #[derive(Clone)]
    struct TestConfig {
        chip_config: EcdsaChipConfig,
        input: Column<Advice>,
        // commitment: Column<Instance>,
    }

    #[derive(Debug, PartialEq, Clone, Copy)]
    struct ECDSAInput<N, C> {
        pk_x: [N; 3],
        pk_y: [N; 3],
        pk_is_identity: bool,
        msg_hash: [N; 3],
        r: [N; 3],
        s: [N; 3],
        r_y: [N; 3],
        r_is_identity: bool,

        _mark: PhantomData<C>,
    }

    impl<N: FieldExt, C: CurveAffine> Default for ECDSAInput<N, C> {
        fn default() -> Self {
            let m = EcdsaSignatureMaterials::<C>::default();
            Self {
                pk_x: split_biguint(&to_biguint(m.pk.coordinates().unwrap().x())),
                pk_y: split_biguint(&to_biguint(m.pk.coordinates().unwrap().y())),
                pk_is_identity: false,

                msg_hash: split_biguint(&to_biguint(&m.msg_hash)),
                r: split_biguint(&to_biguint(&m.r)),
                s: split_biguint(&to_biguint(&m.s)),
                r_y: split_biguint(&to_biguint(&m.r_y)),
                r_is_identity: m.r_is_identity,

                _mark: PhantomData,
            }
        }
    }

    #[derive(Debug, PartialEq)]
    struct TestCircuit<F, C, const N: usize> {
        extra: HostExtraInput<F>,
        inputs: [ECDSAInput<F, C>; N],
        _marker: PhantomData<C>,
    }

    impl<F: FieldExt, C: CurveAffine, const N: usize> TestCircuit<F, C, N> {
        fn assign(
            &self,
            input_column: &Column<Advice>,
            layouter: impl Layouter<F>,
        ) -> Result<Vec<Limb<F>>, Error> {
            layouter.assign_region(
                || "assign input region ",
                |region| {
                    let mut offset = 0;
                    let mut result = Vec::new();

                    for input in &self.inputs {
                        result.append(&mut Self::assign_input(
                            region,
                            input_column,
                            input,
                            &mut offset,
                        )?);
                    }

                    Ok(result)
                },
            )
        }

        fn assign_cell(
            region: &Region<'_, F>,
            annotation: &str,
            input_column: &Column<Advice>,
            value: F,
            offset: &mut usize,
        ) -> Result<Limb<F>, Error> {
            let l = Limb::new(
                Some(region.assign_advice(
                    || annotation,
                    input_column.clone(),
                    *offset,
                    || Ok(value.clone()),
                )?),
                value,
            );

            *offset += 1;
            Ok(l)
        }

        fn assign_input(
            region: &Region<'_, F>,
            input_column: &Column<Advice>,
            input: &ECDSAInput<F, C>,
            offset: &mut usize,
        ) -> Result<Vec<Limb<F>>, Error> {
            let mut result = Vec::new();

            result.append(
                &mut input
                    .pk_x
                    .iter()
                    .map(|x| Self::assign_cell(region, "pk_x", input_column, *x, offset))
                    .collect::<Result<_, _>>()?,
            );
            result.append(
                &mut input
                    .pk_y
                    .iter()
                    .map(|y| Self::assign_cell(region, "pk_y", input_column, *y, offset))
                    .collect::<Result<_, _>>()?,
            );

            result.push(Self::assign_cell(
                region,
                "pk_is_identity",
                input_column,
                if input.pk_is_identity {
                    F::one()
                } else {
                    F::zero()
                },
                offset,
            )?);

            result.append(
                &mut input
                    .msg_hash
                    .iter()
                    .map(|h| Self::assign_cell(region, "msg_hash", input_column, *h, offset))
                    .collect::<Result<_, _>>()?,
            );
            result.append(
                &mut input
                    .r
                    .iter()
                    .map(|r| Self::assign_cell(region, "r", input_column, *r, offset))
                    .collect::<Result<_, _>>()?,
            );
            result.append(
                &mut input
                    .s
                    .iter()
                    .map(|s| Self::assign_cell(region, "s", input_column, *s, offset))
                    .collect::<Result<_, _>>()?,
            );
            result.append(
                &mut input
                    .r_y
                    .iter()
                    .map(|r_y| Self::assign_cell(region, "r_y", input_column, *r_y, offset))
                    .collect::<Result<_, _>>()?,
            );

            result.push(Self::assign_cell(
                region,
                "r_is_identity",
                input_column,
                if input.r_is_identity {
                    F::one()
                } else {
                    F::zero()
                },
                offset,
            )?);

            Ok(result)
        }
    }

    impl<F: FieldExt, C: CurveAffine, const N: usize> Default for TestCircuit<F, C, N> {
        fn default() -> Self {
            Self {
                extra: Default::default(),
                inputs: [ECDSAInput::default(); N],
                _marker: Default::default(),
            }
        }
    }

    impl<F: FieldExt, C: CurveAffine, const N: usize> Circuit<F> for TestCircuit<F, C, N> {
        type Config = TestConfig;
        type FloorPlanner = FlatFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let input = meta.advice_column();
            // let commitment = meta.instance_column();

            meta.enable_equality(input);
            // meta.enable_equality(commitment);

            TestConfig {
                chip_config: EcdsaChip::configure(meta),
                input,
                // commitment,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = EcdsaChip::<F>::construct(config.chip_config);

            chip.range_chip.init_table(&layouter)?;
            let inputs = self.assign(&config.input, layouter.namespace(|| "synthesize assign"))?;

            chip.verify::<C>(&self.extra, &inputs, &layouter)
        }
    }

    fn from_hex_str<T: PrimeField>(s: &str) -> T {
        T::from_str_vartime(&format!("{}", BigUint::from_str_radix(s, 16).unwrap())).unwrap()
    }

    fn to_biguint<F: ff::Field>(f: &F) -> BigUint {
        BigUint::from_str_radix(format!("{:?}", f).strip_prefix("0x").unwrap(), 16).unwrap()
    }

    fn modulus<F: PrimeField>() -> BigUint {
        to_biguint(&-F::one()) + 1u64
    }

    pub fn split_biguint<N: FieldExt>(v: &BigUint) -> [N; 3] {
        const BIT_COUNT: u32 = 108;
        const MASK: u128 = (1u128 << BIT_COUNT) - 1;

        let mask = BigUint::from_u128(MASK).unwrap();

        [
            N::from_u128((v & (&mask)).to_u128().unwrap()),
            N::from_u128(((v >> BIT_COUNT) & mask.clone()).to_u128().unwrap()),
            N::from_u128(((v >> BIT_COUNT * 2) & mask.clone()).to_u128().unwrap()), // TODO: assert no more than 40?
        ]
    }

    pub fn test_circuits<C: CurveAffine, F: FieldExt, const N: usize>() {
        let g = C::generator();

        let inputs = (0..N)
            .into_iter()
            .map(|_| {
                let sk = C::ScalarExt::rand();
                let pk = C::from(g * sk);
                let msg_hash = C::ScalarExt::rand();

                let k = C::ScalarExt::rand();
                let k_inv = k.invert().unwrap();

                let r_affine = C::from(g * k);
                let r_point = r_affine.coordinates().unwrap();
                let x = r_point.x();
                let y = r_point.y();
                let x_bigint = to_biguint(x);
                let y_bigint = to_biguint(y);
                let r_is_identity = bool::from(r_affine.is_identity());

                let r = from_hex_str::<C::ScalarExt>(&format!(
                    "{:x}",
                    x_bigint % modulus::<C::ScalarExt>()
                ));
                let r_y = from_hex_str::<C::ScalarExt>(&format!(
                    "{:x}",
                    y_bigint % modulus::<C::ScalarExt>()
                ));
                let s = k_inv * (msg_hash + (r * sk));

                let input = ECDSAInput {
                    pk_x: split_biguint(&to_biguint(pk.coordinates().unwrap().x())),
                    pk_y: split_biguint(&to_biguint(pk.coordinates().unwrap().y())),
                    pk_is_identity: false,

                    msg_hash: split_biguint(&to_biguint(&msg_hash)),
                    r: split_biguint(&to_biguint(&r)),
                    s: split_biguint(&to_biguint(&s)),
                    r_y: split_biguint(&to_biguint(&r_y)),
                    r_is_identity,

                    _mark: PhantomData,
                };

                // check input data
                ecdsa::general::verify(pk, &msg_hash, &r, &s).unwrap();

                input
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let circuit = TestCircuit::<_, C, N> {
            extra: HostExtraInput {
                commitment: Some(F::rand()),
            },
            inputs,
            _marker: PhantomData,
        };

        let prover =
            MockProver::run(23, &circuit, vec![vec![circuit.extra.commitment.unwrap()]]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
