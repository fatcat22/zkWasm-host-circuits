pub mod secp256r1 {
    use super::super::secp256r1;

    pub fn verify(
        pk: secp256r1::Secp256r1Affine,
        msg_hash: &secp256r1::Fq,
        r: &secp256r1::Fq,
        s: &secp256r1::Fq,
    ) -> Result<(), anyhow::Error> {
        super::common::verify(pk, msg_hash, r, s)
    }
}

mod common {
    use anyhow::anyhow;
    use ff::Field;
    use group::Curve;
    use halo2_proofs::arithmetic::{BaseExt, CurveAffine, FieldExt};

    pub fn verify<C: CurveAffine>(
        pk: C,
        msg_hash: &C::ScalarExt,
        r: &C::ScalarExt,
        s: &C::ScalarExt,
    ) -> Result<(), anyhow::Error> {
        // r_point = g * (msg_hash * s_inv) + pk * (r * s_inv)
        // assert_eq!(r_point.x, r);

        let s_inv = Option::<C::ScalarExt>::from(s.invert())
            .ok_or(anyhow!("s.invert failed. s = {:?}", s))?;
        let u_1 = s_inv.clone() * msg_hash;
        let u_2 = s_inv * r;

        let pk = pk.to_curve();
        let g = C::generator().to_curve();
        let v_1 = g * u_1;
        let v_2 = pk * u_2;

        let r_point = (v_1 + v_2).to_affine().coordinates().unwrap();
        let x_candidate = r_point.x();
        let r_candidate: C::ScalarExt = convert(x_candidate);

        if *r == r_candidate {
            Ok(())
        } else {
            Err(anyhow!(
                "ecdsa verify failed. pk:{:?}, msg_hash:{:?}, r:{:?}, s:{:?}",
                pk,
                msg_hash,
                r,
                s
            ))
        }
    }

    fn convert<B: BaseExt, F: FieldExt>(x: &B) -> F {
        let mut x_repr = [0u8; 32];
        x.write(&mut x_repr.as_mut()).unwrap();
        let mut x_bytes = [0u8; 64];
        x_bytes[..32].copy_from_slice(&x_repr[..]);
        F::from_bytes_wide(&x_bytes)
    }
}
