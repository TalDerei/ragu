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
    /// Each value inserted performs:
    /// (x - value) * polynomial(x)
    /// resulting in a new polynomial with the degree increased by 1
    pub fn insert_value(&mut self, value: F) {
        let neg_value = value.neg();
        let coeffs = self.polynomial.coeffs_mut();
        let len = self.current_size as usize;
        
        for i in (1..len).rev() {
            coeffs[i] = coeffs[i - 1] + coeffs[i] * neg_value;
        }
        
        if len > 0 {
            coeffs[0] = coeffs[0] * neg_value;
        }
        
        self.current_size += 1;
    }

    pub fn check_membership(&self, value: F) -> bool {
        self.polynomial.eval(value) == F::ZERO
    }

    pub fn check_non_membership(&self, value: F) -> bool {
        self.polynomial.eval(value) != F::ZERO
    }

    /*pub fn commit<C: CurveAffine<ScalarExt = F>>(&self, generators: &impl arithmetic::FixedGenerators<C>, blind: F) -> C {
        self.polynomial.commit(C::host_generators(self.params), blind);
    }*/

}

#[test]
fn test_accumulator() {
    use ragu_pasta::Fp;
    use rand::thread_rng;

    let mut accumulator = ValueAccumulator::<Fp>::new();

    let values = vec![Fp::random(thread_rng()); 10];
    for value in &values {
        accumulator.insert_value(*value);
    }

    for i in 0..10 {
        assert!(accumulator.check_membership(values[i]));
    }

    let non_value = vec![Fp::random(thread_rng()); 10];
    for value in &non_value {
        assert!(!accumulator.check_non_membership(*value));
    }

    assert_eq!(accumulator.current_size, 10);
}