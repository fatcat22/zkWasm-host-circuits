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

    let s_inv =
        Option::<C::ScalarExt>::from(s.invert()).ok_or(anyhow!("s.invert failed. s = {:?}", s))?;
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

#[cfg(test)]
pub mod test_helper {
    use super::super::utils;
    use crate::host::{ExternalHostCallEntryTable, HostExtraInputRaw, HostInput};
    use halo2_proofs::arithmetic::{BaseExt, CurveAffine, FieldExt};
    use std::{fs::File, path::Path};

    pub fn generate_ecdsa_input<C: CurveAffine, N: FieldExt, P: AsRef<Path>>(
        count: usize,
        filename: P,
    ) {
        let inputs = (0..count)
            .into_iter()
            .map(|_| {
                let materials = generate_ecdsa_signature_materials::<C>();
                utils::create_ecdsa_call_entries(&materials)
            })
            .flatten()
            .collect();

        let ecdsa_input = HostInput {
            table: ExternalHostCallEntryTable(inputs),
            extra: HostExtraInputRaw {
                commitment: Some(utils::field_to_u64_array::<N, 4, 64>(&N::rand())),
            },
        };
        let file = File::create(filename).expect("can not create file");
        serde_json::to_writer_pretty(file, &ecdsa_input).expect("can not write to file");
    }

    pub fn generate_ecdsa_signature_materials<C: CurveAffine>() -> utils::EcdsaSignatureMaterials<C>
    {
        let sk = C::ScalarExt::rand();
        let msg_hash = C::ScalarExt::rand();

        utils::EcdsaSignatureMaterials::<C>::sign(sk, msg_hash)
    }
}
