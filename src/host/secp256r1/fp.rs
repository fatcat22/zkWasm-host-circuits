use super::{adc, mac, macx, sbb};
use core::fmt;
use core::ops::{Add, Mul, Neg, Sub};
use ff::PrimeField;
use halo2_proofs::arithmetic::{BaseExt, FieldExt, Group};
use halo2curves_axiom::{
    field_arithmetic, field_common, field_specific, impl_add_binop_specify_output,
    impl_binops_additive, impl_binops_additive_specify_output, impl_binops_multiplicative,
    impl_binops_multiplicative_mixed, impl_from_u64, impl_sub_binop_specify_output, impl_sum_prod,
};
use rand::RngCore;
use std::io::{self, Read, Write};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Fp([u64; 4]);

/// Constant representing the modulus
/// p = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
const MODULUS: Fp = Fp([
    0xffffffffffffffff,
    0x00000000ffffffff,
    0x0000000000000000,
    0xffffffff00000001,
]);

/// Constant representing the multiplicative generator of the modulus.
/// It's derived with SageMath with: `GF(MODULUS).primitive_element()`.
const MULTIPLICATIVE_GENERATOR: Fp = Fp::from_raw([0x06, 0x00, 0x00, 0x00]);

/// Constant representing the modolus as static str
const MODULUS_STR: &str = "0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff";

/// INV = -(p^{-1} mod 2^64) mod 2^64
const INV: u64 = 0x1;

/// R = 2^256 mod p
/// 0xfffffffeffffffffffffffffffffffff000000000000000000000001
const R: Fp = Fp([
    0x0000000000000001,
    0xffffffff00000000,
    0xffffffffffffffff,
    0xfffffffe,
]);

/// R^2 = 2^512 mod p
/// 0x4fffffffdfffffffffffffffefffffffbffffffff0000000000000003
const R2: Fp = Fp([
    0x0000000000000003,
    0xfffffffbffffffff,
    0xfffffffffffffffe,
    0x4fffffffd,
]);

/// R^3 = 2^768 mod p
/// 0x180000000100000005fffffffcffffffedfffffff7fffffffd0000000a
const R3: Fp = Fp([
    0xfffffffd0000000a,
    0xffffffedfffffff7,
    0x00000005fffffffc,
    0x1800000001,
]);

/// 1 / 2 mod p
/// 0x7fffffff80000000800000000000000000000000800000000000000000000000
const TWO_INV: Fp = Fp::from_raw([
    0x0000000000000000,
    0x0000000080000000,
    0x8000000000000000,
    0x7fffffff80000000,
]);

const ZETA: Fp = Fp::from_raw([
    0xd964598eb819acce,
    0x2e68c59bdef3e53f,
    0x62388a8e0ef62331,
    0x4d6ea8928adb86cf,
]);

/// Generator of the t-order multiplicative subgroup.
/// Computed by exponentiating Self::MULTIPLICATIVE_GENERATOR by 2^s, where s is Self::S.
/// `0x0000000000000000000000000000000000000000000000000000000000000024`.
const DELTA: Fp = Fp::from_raw([0x24, 0, 0, 0]);

/// Implementations of this trait MUST ensure that this is the generator used to derive Self::ROOT_OF_UNITY.
/// Derived from:
/// ```ignore
/// Zp(Zp(mul_generator)^t) where t = (modulus - 1 )/ 2
/// 115792089237316195423570985008687907853269984665640564039457584007908834671662
/// ```
/// `0xffffffff00000001000000000000000000000000fffffffffffffffffffffffe`
const ROOT_OF_UNITY: Fp = Fp::from_raw([
    0xfffffffffffffffe,
    0x00000000ffffffff,
    0x0000000000000000,
    0xffffffff00000001,
]);

/// Inverse of [`ROOT_OF_UNITY`].
/// `0xffffffff00000001000000000000000000000000fffffffffffffffffffffffe`
const ROOT_OF_UNITY_INV: Fp = Fp::from_raw([
    0xfffffffffffffffe,
    0x00000000ffffffff,
    0x0000000000000000,
    0xffffffff00000001,
]);

impl_binops_additive!(Fp, Fp);
impl_binops_multiplicative!(Fp, Fp);
field_common!(
    Fp,
    MODULUS,
    INV,
    MODULUS_STR,
    TWO_INV,
    ROOT_OF_UNITY_INV,
    DELTA,
    ZETA,
    R,
    R2,
    R3
);
impl_from_u64!(Fp, R2);
field_arithmetic!(Fp, MODULUS, INV, dense);
impl_sum_prod!(Fp);

impl Fp {
    pub const ZERO: Self = Self::zero();
    pub const ONE: Self = Self::one();

    pub const fn size() -> usize {
        32
    }

    fn to_repr(&self) -> [u8; 32] {
        let tmp: [u64; 4] = (*self).into();
        let mut res = [0; 32];
        res[0..8].copy_from_slice(&tmp[0].to_le_bytes());
        res[8..16].copy_from_slice(&tmp[1].to_le_bytes());
        res[16..24].copy_from_slice(&tmp[2].to_le_bytes());
        res[24..32].copy_from_slice(&tmp[3].to_le_bytes());

        res
    }
    pub fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
        debug_assert_eq!(bytes.len(), 32);
        let inner = [0, 8, 16, 24].map(|i| u64::from_le_bytes(bytes[i..i + 8].try_into().unwrap()));
        Self(inner)
    }
    pub fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != 32 {
            return None;
        }
        let elt = Self::from_raw_bytes_unchecked(bytes);
        Self::is_less_than(&elt.0, &MODULUS.0).then(|| elt)
    }
    pub fn to_raw_bytes(&self) -> Vec<u8> {
        let mut res = Vec::with_capacity(32);
        for limb in self.0.iter() {
            res.extend_from_slice(&limb.to_le_bytes());
        }
        res
    }
    pub fn read_raw_unchecked<R: std::io::Read>(reader: &mut R) -> Self {
        let inner = [(); 4].map(|_| {
            let mut buf = [0; 8];
            reader.read_exact(&mut buf).unwrap();
            u64::from_le_bytes(buf)
        });
        Self(inner)
    }
    pub fn read_raw<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut inner = [0u64; 4];
        for limb in inner.iter_mut() {
            let mut buf = [0; 8];
            reader.read_exact(&mut buf)?;
            *limb = u64::from_le_bytes(buf);
        }
        let elt = Self(inner);
        Self::is_less_than(&elt.0, &MODULUS.0)
            .then(|| elt)
            .ok_or_else(|| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    "input number is not less than field modulus",
                )
            })
    }
    pub fn write_raw<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        for limb in self.0.iter() {
            writer.write_all(&limb.to_le_bytes())?;
        }
        Ok(())
    }
}

impl ff::Field for Fp {
    fn one() -> Self {
        Self::one()
    }

    fn zero() -> Self {
        Self::zero()
    }

    fn random(mut rng: impl RngCore) -> Self {
        Self::from_u512([
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
        ])
    }

    fn double(&self) -> Self {
        self.double()
    }

    #[inline(always)]
    fn square(&self) -> Self {
        self.square()
    }

    /// Computes the square root of this element, if it exists.
    fn sqrt(&self) -> CtOption<Self> {
        let tmp = self.pow(&[
            0x0000000000000000,
            0x0000000040000000,
            0x4000000000000000,
            0x3fffffffc0000000,
        ]);

        CtOption::new(tmp, tmp.square().ct_eq(self))
    }

    /// Returns the multiplicative inverse of the
    /// element. If it is zero, the method fails.
    fn invert(&self) -> CtOption<Self> {
        self.invert()
    }

    fn pow_vartime<S: AsRef<[u64]>>(&self, exp: S) -> Self {
        let mut res = Self::one();
        let mut found_one = false;
        for e in exp.as_ref().iter().rev() {
            for i in (0..64).rev() {
                if found_one {
                    res = res.square();
                }

                if ((*e >> i) & 1) == 1 {
                    found_one = true;
                    res *= self;
                }
            }
        }
        res
    }
}

impl ff::PrimeField for Fp {
    type Repr = [u8; 32];

    // const MODULUS: &'static str = MODULUS_STR;
    // const MULTIPLICATIVE_GENERATOR: Self = MULTIPLICATIVE_GENERATOR;
    // const TWO_INV: Self = TWO_INV;
    // const ROOT_OF_UNITY: Self = ROOT_OF_UNITY;
    // const ROOT_OF_UNITY_INV: Self = ROOT_OF_UNITY_INV;
    // const DELTA: Self = DELTA;
    const NUM_BITS: u32 = 256;
    const CAPACITY: u32 = 255;
    const S: u32 = 1;

    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        let mut tmp = Fp([0, 0, 0, 0]);

        tmp.0[0] = u64::from_le_bytes(repr[0..8].try_into().unwrap());
        tmp.0[1] = u64::from_le_bytes(repr[8..16].try_into().unwrap());
        tmp.0[2] = u64::from_le_bytes(repr[16..24].try_into().unwrap());
        tmp.0[3] = u64::from_le_bytes(repr[24..32].try_into().unwrap());

        // Try to subtract the modulus
        let (_, borrow) = sbb(tmp.0[0], MODULUS.0[0], 0);
        let (_, borrow) = sbb(tmp.0[1], MODULUS.0[1], borrow);
        let (_, borrow) = sbb(tmp.0[2], MODULUS.0[2], borrow);
        let (_, borrow) = sbb(tmp.0[3], MODULUS.0[3], borrow);

        // If the element is smaller than MODULUS then the
        // subtraction will underflow, producing a borrow value
        // of 0xffff...ffff. Otherwise, it'll be zero.
        let is_some = (borrow as u8) & 1;

        // Convert to Montgomery form by computing
        // (a.R^0 * R^2) / R = a.R
        tmp *= &R2;

        CtOption::new(tmp, Choice::from(is_some))
    }

    fn to_repr(&self) -> Self::Repr {
        let tmp: [u64; 4] = (*self).into();
        let mut res = [0; 32];
        res[0..8].copy_from_slice(&tmp[0].to_le_bytes());
        res[8..16].copy_from_slice(&tmp[1].to_le_bytes());
        res[16..24].copy_from_slice(&tmp[2].to_le_bytes());
        res[24..32].copy_from_slice(&tmp[3].to_le_bytes());

        res
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr()[0] & 1)
    }

    /// Returns a fixed multiplicative generator of `modulus - 1` order. This element must
    /// also be a quadratic nonresidue.
    ///
    /// It can be calculated using [SageMath] as `GF(modulus).primitive_element()`.
    ///
    /// Implementations of this method MUST ensure that this is the generator used to
    /// derive `Self::root_of_unity`.
    ///
    /// [SageMath]: https://www.sagemath.org/
    fn multiplicative_generator() -> Self {
        MULTIPLICATIVE_GENERATOR
    }

    fn root_of_unity() -> Self {
        ROOT_OF_UNITY
    }
}

impl BaseExt for Fp {
    const MODULUS: &'static str = MODULUS_STR;

    fn from_bytes_wide(bytes: &[u8; 64]) -> Self {
        Self::from_u512([
            u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
            u64::from_le_bytes(bytes[32..40].try_into().unwrap()),
            u64::from_le_bytes(bytes[40..48].try_into().unwrap()),
            u64::from_le_bytes(bytes[48..56].try_into().unwrap()),
            u64::from_le_bytes(bytes[56..64].try_into().unwrap()),
        ])
    }

    fn write<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        let compressed = self.to_repr();
        writer.write_all(&compressed[..])
    }

    /// Reads a normalized, little endian represented field element from a
    /// buffer.
    fn read<R: Read>(reader: &mut R) -> io::Result<Self> {
        let mut compressed = [0u8; 32];
        reader.read_exact(&mut compressed[..])?;
        Option::from(Self::from_repr(compressed))
            .ok_or_else(|| io::Error::new(io::ErrorKind::Other, "invalid point encoding in proof"))
    }
}

impl Group for Fp {
    type Scalar = Self;

    fn group_zero() -> Self {
        Self::zero()
    }
    fn group_add(&mut self, rhs: &Self) {
        *self += *rhs;
    }
    fn group_sub(&mut self, rhs: &Self) {
        *self -= *rhs;
    }
    fn group_scale(&mut self, by: &Self::Scalar) {
        *self *= *by;
    }
}

impl FieldExt for Fp {
    const TWO_INV: Self = TWO_INV;
    const ROOT_OF_UNITY_INV: Self = ROOT_OF_UNITY_INV;
    const DELTA: Self = DELTA;
    const ZETA: Self = ZETA;

    fn from_u128(v: u128) -> Self {
        Self::from_raw([v as u64, (v >> 64) as u64, 0, 0])
    }

    // /// Attempts to convert a little-endian byte representation of
    // /// a scalar into a `Fr`, failing if the input is not canonical.
    // fn from_bytes(bytes: &[u8; 32]) -> CtOption<$field> {
    //     <Self as ff::PrimeField>::from_repr(*bytes)
    // }

    // /// Converts an element of `Fr` into a byte representation in
    // /// little-endian byte order.
    // fn to_bytes(&self) -> [u8; 32] {
    //     <Self as ff::PrimeField>::to_repr(self)
    // }

    /// Gets the lower 128 bits of this field element when expressed
    /// canonically.
    fn get_lower_128(&self) -> u128 {
        #[cfg(all(feature = "asm", target_arch = "x86_64"))]
        let tmp =
            Self::montgomery_reduce(&[self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0]);

        #[cfg(any(not(feature = "asm"), not(target_arch = "x86_64")))]
        let tmp =
            Self::montgomery_reduce(&[self.0[0], self.0[1], self.0[2], self.0[3], 0, 0, 0, 0]);

        u128::from(tmp.0[0]) | (u128::from(tmp.0[1]) << 64)
    }
}

/*
#[cfg(test)]
mod tests {
    use super::*;
    use rand_core::RngCore;

    #[test]
    fn test_from_bytes_wide() {
        let mut rng = rand_core::OsRng;
        let data = [
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
            rng.next_u64(),
        ];

        assert_eq!(Fp::from_bytes_wide(&data).0, secp256r1::Fp::from_raw(data));
    }
}
 */
