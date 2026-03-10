//! Fuzz structured polynomial revdot against unstructured dot product.
//!
//! The structured `revdot` (structured.rs:124) pairs (u,v), (v,u), (w,d),
//! (d,w) vectors via `zip` — which silently truncates when vectors have
//! mismatched lengths. This fuzzer exercises the full combinatorial space
//! of independent (u,v,w,d) lengths to verify the structured shortcut
//! always agrees with the naive unstructured computation.
//!
//! Invariant: poly1.revdot(&poly2) == dot(poly1.unstructured(), reverse(poly2.unstructured()))

#![no_main]

use arbitrary::Arbitrary;
use ff::Field;
use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_circuits::polynomials::{TestRank, Rank, structured::Polynomial};

/// Input: two polynomials with independently sized (u,v,w,d) vectors.
#[derive(Arbitrary, Debug)]
struct Input {
    /// Length of each vector for poly1 (clamped to R::n())
    p1_lens: [u8; 4],
    /// Length of each vector for poly2 (clamped to R::n())
    p2_lens: [u8; 4],
    /// Seed values for coefficients
    coeffs: Vec<u64>,
}

fn build_poly(lens: &[u8; 4], coeffs: &mut impl Iterator<Item = Fp>) -> Polynomial<Fp, TestRank> {
    let n = TestRank::n();
    let mut poly = Polynomial::new();
    let clamp = |l: u8| (l as usize) % (n + 1);

    let fwd = poly.forward();
    // a = u, b = v, c = w in forward view
    for _ in 0..clamp(lens[0]) {
        fwd.a.push(coeffs.next().unwrap_or(Fp::ZERO));
    }
    for _ in 0..clamp(lens[1]) {
        fwd.b.push(coeffs.next().unwrap_or(Fp::ZERO));
    }
    for _ in 0..clamp(lens[2]) {
        fwd.c.push(coeffs.next().unwrap_or(Fp::ZERO));
    }
    // d is not exposed via forward view, access via backward where c = d
    drop(fwd);
    let bwd = poly.backward();
    for _ in 0..clamp(lens[3]) {
        bwd.c.push(coeffs.next().unwrap_or(Fp::ZERO));
    }

    poly
}

fuzz_target!(|input: Input| {
    if input.coeffs.is_empty() {
        return;
    }

    let mut coeffs = input.coeffs.iter().map(|&v| Fp::from(v));

    let p1 = build_poly(&input.p1_lens, &mut coeffs);
    let p2 = build_poly(&input.p2_lens, &mut coeffs);

    // Structured revdot
    let structured_result = p1.revdot(&p2);

    // Naive: dot(unstructured(p1), reverse(unstructured(p2)))
    let u1 = p1.unstructured();
    let u2 = p2.unstructured();
    let naive_result = ragu_arithmetic::dot(u1.iter(), u2.iter().rev());

    assert_eq!(
        structured_result, naive_result,
        "revdot mismatch: p1 lens={:?}, p2 lens={:?}",
        input.p1_lens, input.p2_lens
    );
});
