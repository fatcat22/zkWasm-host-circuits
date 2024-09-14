use crate::host::secp256r1;

/// how many signatures can be verify at a time when k equal 22.
/// but if k is 23, this value could be 170 (don't no why yet)
pub const TOTAL_ROUNDS: usize = 166;

pub type EcdsaSecp256R1Chip<N> =
    super::general::EcdsaChip<secp256r1::Secp256r1Affine, N, TOTAL_ROUNDS>;

#[cfg(test)]
mod tests {
    use super::super::general::circuits_test;
    use crate::{circuits::ecdsa::secp256r1::TOTAL_ROUNDS, host::secp256r1};
    use halo2_proofs::pairing::bn256::Fr;

    #[test]
    fn test_circuits() {
        const K: usize = 22;
        // see `max_rounds` to know why calculate `ITEM_COUNT` like this.
        // minus 1 because need at least one default value
        const ITEM_COUNT: usize = (1 << (K - 22)) * TOTAL_ROUNDS - 1;

        circuits_test::test_circuits::<secp256r1::Secp256r1Affine, Fr, TOTAL_ROUNDS, ITEM_COUNT>(
            K as u32,
        );
    }
}
