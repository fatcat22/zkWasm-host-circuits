mod general;

pub use general::{EcdsaChip, EcdsaChipConfig};

use crate::utils::Limb;
use halo2_proofs::{arithmetic::FieldExt, circuit::Layouter, plonk::Error};

pub mod secp256r1 {
    use super::*;
    use crate::host::secp256r1;

    pub fn verify<N: FieldExt>(
        chip: &general::EcdsaChip<N>,
        inputs: &Vec<Limb<N>>,
        layouter: &impl Layouter<N>,
    ) -> Result<(), Error> {
        chip.verify::<secp256r1::Secp256r1Affine>(inputs, layouter)
    }

    #[cfg(test)]
    mod tests {
        use super::super::general::circuits_test;
        use crate::host::secp256r1;
        use halo2_proofs::pairing::bn256::Fr;

        #[test]
        fn test_circuits() {
            circuits_test::test_circuits::<secp256r1::Secp256r1Affine, Fr>(340);
        }
    }
}
