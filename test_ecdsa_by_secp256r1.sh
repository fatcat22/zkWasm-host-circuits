rm ./params/*.data
cargo test secp256r1::tests::generate_ecdsa_input
RUST_BACKTRACE=1 cargo run --release --features cuda -- --input ecdsa_secp256r1.json --opname ecdsasecp256r1 --output output/ --param params/
