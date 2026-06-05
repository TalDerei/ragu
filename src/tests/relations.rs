use alloc::vec::Vec;

use ff::Field as _;
use pasta_curves::Fp;

use crate::{
    ctx::StepCtx,
    hooks::FrameworkHooks,
    polynomial::Polynomial,
    relations::{enforce_poly_concat, enforce_poly_product},
};

/// Distinct nonzero values, so any reordering or substitution is detectable.
fn values(n: u32) -> Vec<Fp> {
    (0..n)
        .map(|i| Fp::from(u64::from(i) + 1) * Fp::from(7u64))
        .collect()
}

#[test]
fn product_returns_the_union() {
    let a = Polynomial::from_roots(&[Fp::from(1u64), Fp::from(2u64)]);
    let b = Polynomial::from_roots(&[Fp::from(3u64)]);
    let union = a.multiply(&b);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    let product = enforce_poly_product(&mut ctx, &a, &b, union.commit(Fp::ZERO)).unwrap();
    assert_eq!(product, union);
}

#[test]
fn product_rejects_a_wrong_commitment() {
    let a = Polynomial::from_roots(&[Fp::from(1u64), Fp::from(2u64)]);
    let b = Polynomial::from_roots(&[Fp::from(3u64)]);
    let wrong = Polynomial::from_roots(&[Fp::from(4u64)]).commit(Fp::ZERO);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    assert!(enforce_poly_product(&mut ctx, &a, &b, wrong).is_err());
}

#[test]
fn concat_accepts_the_concatenation() {
    let v = values(6);
    let head = Polynomial::from_coeffs(&v[..2]);
    let tail = Polynomial::from_coeffs(&v[2..]);
    // result = head ++ tail is prover-supplied; the shift offset = 2 is a witness
    // the relation confirms against the three committed sequences.
    let result = Polynomial::from_coeffs(&v);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    enforce_poly_concat(&mut ctx, &head, &tail, 2, &result, result.commit(Fp::ZERO)).unwrap();
}

#[test]
fn concat_rejects_mismatched_result_commitment() {
    let v = values(6);
    let head = Polynomial::from_coeffs(&v[..2]);
    let tail = Polynomial::from_coeffs(&v[2..]);
    let result = Polynomial::from_coeffs(&v);
    // A commitment to a different polynomial than the supplied result.
    let wrong_com = Polynomial::from_coeffs(&v[..4]).commit(Fp::ZERO);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    assert!(enforce_poly_concat(&mut ctx, &head, &tail, 2, &result, wrong_com).is_err());
}

#[test]
fn concat_rejects_a_result_that_is_not_the_concatenation() {
    let v = values(6);
    let head = Polynomial::from_coeffs(&v[..2]);
    let tail = Polynomial::from_coeffs(&v[2..]);
    // A self-consistent (poly, commitment) pair, but not head ++ tail.
    let mut bad = v.clone();
    bad.swap(0, 5);
    let result = Polynomial::from_coeffs(&bad);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    assert!(
        enforce_poly_concat(&mut ctx, &head, &tail, 2, &result, result.commit(Fp::ZERO)).is_err()
    );
}

#[test]
fn concat_rejects_a_wrong_offset() {
    // The genuine concatenation with the genuine result commitment, but a wrong
    // shift: only offset = len(head) = 2 satisfies the point-wise identity.
    let v = values(6);
    let head = Polynomial::from_coeffs(&v[..2]);
    let tail = Polynomial::from_coeffs(&v[2..]);
    let result = Polynomial::from_coeffs(&v);
    let result_com = result.commit(Fp::ZERO);

    let mut hooks = FrameworkHooks::new();
    let mut ctx = StepCtx::new(&mut hooks);
    assert!(enforce_poly_concat(&mut ctx, &head, &tail, 2, &result, result_com).is_ok());
    assert!(enforce_poly_concat(&mut ctx, &head, &tail, 3, &result, result_com).is_err());
    assert!(enforce_poly_concat(&mut ctx, &head, &tail, 1, &result, result_com).is_err());
}
