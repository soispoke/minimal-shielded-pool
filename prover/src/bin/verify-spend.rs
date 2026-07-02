//! Verify one shielded-pool spend proof against its publics.
//!
//!   verify-spend --proof proof.json --publics publics.json
//!
//! Recomputes the claim from (root, nf, out_cm, ctx) exactly as the pool
//! contract does (the recompute-and-compare from devnet/README.md), then
//! verifies the STARK against it. Exit code 0 iff both hold.

use pool_prover::*;

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).map(|i| args.get(i + 1).cloned().unwrap_or_default())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (Some(proof_path), Some(publics_path)) = (arg(&args, "--proof"), arg(&args, "--publics"))
    else {
        eprintln!("usage: verify-spend --proof proof.json --publics publics.json");
        std::process::exit(2);
    };
    let publics: SpendPublics =
        serde_json::from_str(&std::fs::read_to_string(&publics_path).expect("cannot read publics"))
            .expect("publics JSON does not match the SpendPublics schema");
    let proof = serde_json::from_str(&std::fs::read_to_string(&proof_path).expect("cannot read proof"))
        .expect("proof JSON does not deserialize");

    // the contract's recompute-and-compare: claim must bind the other publics
    let recomputed = {
        use pool_prover as pp;
        let root = pp::from_u32(&publics.root).unwrap();
        let nf = pp::from_u32(&publics.nf).unwrap();
        let out_cm = pp::from_u32(&publics.out_cm).unwrap();
        let ctx = pp::from_u32(&publics.ctx).unwrap();
        pp::to_u32(&pp::tagged(pp::TAG_CLAIM, &pp::h8(&root, &nf), &pp::h8(&out_cm, &ctx)))
    };
    if recomputed != publics.claim {
        eprintln!("REJECTED: claim does not bind the publics");
        std::process::exit(1);
    }

    match verify_spend(publics.depth, &publics.claim, proof) {
        Ok(ms) => {
            eprintln!("OK: claim binds the publics; proof verified in {ms:.1} ms (depth {})",
                      publics.depth);
        }
        Err(e) => {
            eprintln!("REJECTED: {e}");
            std::process::exit(1);
        }
    }
}
