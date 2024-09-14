use crate::host::secp256r1;

pub fn verify(
    pk: secp256r1::Secp256r1Affine,
    msg_hash: &secp256r1::Fq,
    r: &secp256r1::Fq,
    s: &secp256r1::Fq,
) -> Result<(), anyhow::Error> {
    super::general::verify(pk, msg_hash, r, s)
}

#[cfg(test)]
mod tests {
    use crate::circuits::ecdsa::secp256r1::TOTAL_ROUNDS;
    use halo2_proofs::pairing::bn256::Fr;

    use super::{super::general::test_helper, *};

    #[test]
    fn generate_ecdsa_input() {
        test_helper::generate_ecdsa_input::<secp256r1::Secp256r1Affine, Fr, _>(
            TOTAL_ROUNDS - 1, // need at least one default value
            "ecdsa_secp256r1.json",
        );
    }
}
