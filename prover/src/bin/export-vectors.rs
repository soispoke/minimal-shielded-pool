//! Regenerate contracts/vectors/poseidon16_vectors.json from leanVM itself.
//!
//!   export-vectors > ../contracts/vectors/poseidon16_vectors.json
//!
//! Same vectors as the original in-leanVM exporter: 32 permute + 32 compress
//! cases (zero, unit, counter, 29 LCG-seeded) and the pool chain from seed
//! 2026. This binary replaces the export_vectors patch: the vectors now come
//! from the same pinned leanVM dependency the prover uses.

use backend::*;
use lean_vm::F;
use pool_prover::{h8, tagged, Lcg};

fn perm(x: [F; 16]) -> [F; 16] {
    poseidon16_permute(x)
}

fn comp(x: [F; 16]) -> [F; 8] {
    poseidon16_compress(x)[..8].try_into().unwrap()
}

fn j16(x: &[F; 16]) -> String {
    let v: Vec<String> = x.iter().map(|e| e.as_canonical_u32().to_string()).collect();
    format!("[{}]", v.join(","))
}

fn j8(x: &[F; 8]) -> String {
    let v: Vec<String> = x.iter().map(|e| e.as_canonical_u32().to_string()).collect();
    format!("[{}]", v.join(","))
}

fn fe(lcg: &mut Lcg) -> F {
    F::new(lcg.next_u32())
}

fn main() {
    let mut out = String::from("{\n");

    let mut cases: Vec<[F; 16]> = vec![[F::ZERO; 16]];
    let mut e1 = [F::ZERO; 16];
    e1[0] = F::ONE;
    cases.push(e1);
    cases.push(core::array::from_fn(|i| F::new(i as u32)));
    let mut lcg = Lcg(42);
    for _ in 0..29 {
        cases.push(core::array::from_fn(|_| fe(&mut lcg)));
    }

    out.push_str("\"permute\":[");
    for (i, c) in cases.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&format!("{{\"in\":{},\"out\":{}}}", j16(c), j16(&perm(*c))));
    }
    out.push_str("],\n\"compress\":[");
    for (i, c) in cases.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&format!("{{\"in\":{},\"out\":{}}}", j16(c), j8(&comp(*c))));
    }
    out.push_str("],\n");

    let mut lcg = Lcg(2026);
    let mut d = || -> [F; 8] { core::array::from_fn(|_| fe(&mut lcg)) };
    let (spend_key, rho, root, out_cm, ctx) = (d(), d(), d(), d(), d());
    let zero8 = [F::ZERO; 8];
    let owner_pk = tagged(1, &spend_key, &zero8);
    let cm = tagged(2, &owner_pk, &rho);
    let nf = tagged(3, &spend_key, &cm);
    let claim = tagged(4, &h8(&root, &nf), &h8(&out_cm, &ctx));
    out.push_str(&format!(
        "\"pool_chain\":{{\"spend_key\":{},\"rho\":{},\"root\":{},\"out_cm\":{},\"ctx\":{},\"owner_pk\":{},\"cm\":{},\"nf\":{},\"claim\":{}}}\n",
        j8(&spend_key), j8(&rho), j8(&root), j8(&out_cm), j8(&ctx),
        j8(&owner_pk), j8(&cm), j8(&nf), j8(&claim)
    ));
    out.push('}');
    println!("{out}");
}
