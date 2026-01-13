/// A polynomial-based accumulator that supports efficient set membership and non-membership proofs
use ff::Field;
use ragu_circuits::polynomials::{
    R,
    unstructured::Polynomial,
};
use alloc::vec;
use alloc::vec::Vec;
use arithmetic::CurveAffine;

pub struct ValueAccumulator<F: Field> {
    pub polynomial: Polynomial<F, R<13>>,
    pub current_size: u32,
}

impl<F: Field> ValueAccumulator<F> {
    pub fn new() -> Self {
        Self {
            polynomial: Polynomial::new(),
            current_size: 0,
        }
    }

    /// Insert a value into the accumulator.
    /// Performs O(n) ops per insertion where n is the current size of the accumulator
    pub fn accumulate_value(&mut self, value: F) {
        let neg_value = value.neg();
        let mut new_coeffs: Vec<F> = vec![];

        let mut poly_iter = self.polynomial.iter_coeffs();
        let Some(mut prev) = poly_iter.next() else { return };
        new_coeffs.push(prev.mul(&neg_value));

        for curr in poly_iter.take(self.current_size.saturating_sub(1) as usize) {
            new_coeffs.push(prev.add(&curr.mul(&neg_value)));
            prev = curr;
        }
        self.current_size += 1;
        self.polynomial = Polynomial::from_coeffs(new_coeffs);
    }

    pub fn check_membership(&self, value: F) -> bool {
        self.polynomial.eval(value) == F::ZERO
    }

    pub fn check_non_membership(&self, value: F) -> bool {
        self.polynomial.eval(value) != F::ZERO
    }

    pub fn commit<C: CurveAffine<ScalarExt = F>>(&self, generators: &impl arithmetic::FixedGenerators<C>, blind: F) -> C {
        self.polynomial.commit(C::host_generators(self.params), blind);
    }

}

#[test]
fn test_accumulator() {
    use ragu_pasta::Fp;
    use rand::thread_rng;

    let mut accumulator = ValueAccumulator::<Fp>::new();

    let values = vec![Fp::random(thread_rng()); 10];
    for value in &values {
        accumulator.accumulate_value(*value);
    }

    for i in 0..10 {
        assert!(accumulator.check_membership(values[i]));
    }

    assert_eq!(accumulator.current_size, 10);
}