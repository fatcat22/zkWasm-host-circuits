use crate::{
    host::{ExternalHostCallEntry, ForeignInst},
    utils::field_to_bn,
};
use ff::{Field, PrimeField};
use halo2_proofs::arithmetic::{BaseExt, CurveAffine};
use num_bigint::BigUint;
use num_traits::{Num, Zero};

#[derive(Debug)]
pub struct EcdsaSignatureMaterials<C: CurveAffine> {
    pub pk: C,
    pub msg_hash: C::ScalarExt,
    pub r: C::ScalarExt,
    pub s: C::ScalarExt,
    pub r_y: C::ScalarExt,
    pub r_is_identity: bool,
}

impl<C: CurveAffine> EcdsaSignatureMaterials<C> {
    pub fn verify(&self) -> Result<(), anyhow::Error> {
        super::general::verify(self.pk.clone(), &self.msg_hash, &self.r, &self.s)
    }

    pub fn sign(sk: C::ScalarExt, msg_hash: C::ScalarExt) -> Self {
        let g = C::generator();
        let pk = C::from(g * sk);

        let k = C::ScalarExt::rand();
        let k_inv = k.invert().unwrap();

        let r_affine = C::from(g * k);
        let r_point = r_affine.coordinates().unwrap();
        let x = r_point.x();
        let y = r_point.y();
        let x_bigint = to_biguint(x);
        let y_bigint = to_biguint(y);
        let r_is_identity = bool::from(r_affine.is_identity());

        let r =
            from_hex_str::<C::ScalarExt>(&format!("{:x}", x_bigint % modulus::<C::ScalarExt>()));
        let r_y =
            from_hex_str::<C::ScalarExt>(&format!("{:x}", y_bigint % modulus::<C::ScalarExt>()));
        let s = k_inv * (msg_hash + (r * sk));

        let result = Self {
            pk,
            msg_hash,
            r,
            s,
            r_y,
            r_is_identity,
        };
        result.verify().expect(&format!("result is: {:?}", result));

        result
    }
}

impl<C: CurveAffine> Default for EcdsaSignatureMaterials<C> {
    fn default() -> Self {
        Self::sign(C::ScalarExt::one(), C::ScalarExt::one())
    }
}

pub fn create_ecdsa_call_entries<C: CurveAffine>(
    materials: &EcdsaSignatureMaterials<C>,
) -> Vec<ExternalHostCallEntry> {
    let mut r = vec![];
    r.append(&mut point_to_args(&materials.pk, ForeignInst::EcdsaPush));
    r.append(&mut field_to_args(
        &materials.msg_hash,
        ForeignInst::EcdsaPush,
    ));
    r.append(&mut field_to_args(&materials.r, ForeignInst::EcdsaPush));
    r.append(&mut field_to_args(&materials.s, ForeignInst::EcdsaPush));
    r.append(&mut field_to_args(&materials.r_y, ForeignInst::EcdsaPush));
    r.push(ExternalHostCallEntry {
        op: ForeignInst::EcdsaPush as usize,
        value: if materials.r_is_identity { 1 } else { 0 },
        is_ret: false,
    });
    r
}

fn point_to_args<C: CurveAffine>(g: &C, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let mut a = field_to_args(g.coordinates().unwrap().x(), op);
    let mut b = field_to_args(g.coordinates().unwrap().y(), op);
    let z: u64 = g.is_identity().unwrap_u8() as u64;
    a.append(&mut b);
    a.append(&mut vec![ExternalHostCallEntry {
        op: op as usize,
        value: z,
        is_ret: false,
    }]);
    a
}

fn field_to_args<F: BaseExt>(f: &F, op: ForeignInst) -> Vec<ExternalHostCallEntry> {
    let result = field_to_u64_array::<F, 5, 54>(f);

    result
        .into_iter()
        .map(|value| ExternalHostCallEntry {
            op: op as usize,
            value,
            is_ret: false,
        })
        .collect()
}

pub fn field_to_u64_array<F: BaseExt, const N: usize, const B: usize>(f: &F) -> [u64; N] {
    assert!(N * B >= 256);
    assert!(B <= 64);

    let mut bn = field_to_bn(f);
    let mut result = [0u64; N];
    for res in result.iter_mut() {
        let d: BigUint = BigUint::from(1u128 << B);
        let r = bn.clone() % d.clone();
        let value = if r.is_zero() {
            0 as u64
        } else {
            r.to_u64_digits()[0]
        };
        bn = bn / d;
        *res = value;
    }

    assert_eq!(bn, BigUint::zero());
    result
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
