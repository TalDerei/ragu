use ff::Field;
use ragu_arithmetic::Coeff;
use ragu_core::{
    Error, Result,
    drivers::{Driver, DriverValue},
    gadgets::Gadget,
    maybe::Maybe,
};

use crate::{Element, consistent::Consistent};

/// An invertible [`Element`].
///
/// This gadget represents a nonzero [`Element`] with a known multiplicative
/// inverse, accessible via [`element`](Self::element) and
/// [`inverse`](Self::inverse).
///
/// Inversion is free, since the inverse is located within the gadget.
#[derive(Gadget)]
pub struct Invertible<'dr, D: Driver<'dr>> {
    element: Element<'dr, D>,
    inverse: Element<'dr, D>,
}

impl<'dr, D: Driver<'dr>> Invertible<'dr, D> {
    /// Allocate an [`Invertible`] field element.
    ///
    /// This will be unsatisfied (and fail to synthesize) if `value` is zero.
    ///
    /// Computing the inverse witness costs a field inversion. If the inverse
    /// is already known, prefer
    /// [`alloc_with_advice`](Invertible::alloc_with_advice).
    ///
    /// This costs one gate and one constraint.
    pub fn alloc(dr: &mut D, value: DriverValue<D, D::F>) -> Result<Self> {
        let inverse_value = D::try_just(|| {
            value
                .snag()
                .invert()
                .into_option()
                .ok_or_else(|| Error::InvalidWitness("division by zero".into()))
        })?;
        Self::alloc_with_advice(dr, value, inverse_value)
    }

    /// Allocate an [`Invertible`] field element given its inverse as advice.
    ///
    /// This will be unsatisfied if `value` is zero or if `inverse_value` is not
    /// really its multiplicative inverse.
    ///
    /// This costs one gate and one constraint.
    pub fn alloc_with_advice(
        dr: &mut D,
        value: DriverValue<D, D::F>,
        inverse_value: DriverValue<D, D::F>,
    ) -> Result<Self> {
        let (a, b, c) = dr.mul(|| {
            Ok((
                Coeff::Arbitrary(*value.snag()),
                Coeff::Arbitrary(*inverse_value.snag()),
                Coeff::One,
            ))
        })?;
        dr.enforce_equal(&c, &D::ONE)?;

        Ok(Self {
            element: Element::promote(a, value),
            inverse: Element::promote(b, inverse_value),
        })
    }

    /// Returns the multiplicative inverse of `self`. This is free.
    pub fn invert(&self) -> Self {
        Self {
            element: self.inverse.clone(),
            inverse: self.element.clone(),
        }
    }

    /// Returns the underlying [`Element`].
    pub fn element(&self) -> &Element<'dr, D> {
        &self.element
    }

    /// Returns the inverse of the underlying [`Element`].
    pub fn inverse(&self) -> &Element<'dr, D> {
        &self.inverse
    }

    /// Consumes the [`Invertible`] and returns the underlying [`Element`],
    /// discarding the inverse.
    pub fn into_element(self) -> Element<'dr, D> {
        self.element
    }

    /// Consumes the [`Invertible`] and returns the inverse [`Element`],
    /// discarding the original.
    pub fn into_inverse(self) -> Element<'dr, D> {
        self.inverse
    }
}

impl<'dr, D: Driver<'dr>> Consistent<'dr, D> for Invertible<'dr, D> {
    fn enforce_consistent(&self, dr: &mut D) -> Result<()> {
        let value = D::just(|| *self.element.value().take());
        let inverse_value = D::just(|| *self.inverse.value().take());
        Self::alloc_with_advice(dr, value, inverse_value)?.enforce_equal(dr, self)
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;

    use super::*;
    use crate::Simulator;

    type F = ragu_pasta::Fp;
    type Sim = Simulator<F>;

    #[test]
    fn test_alloc_nonzero() -> Result<()> {
        let alloc = |a: F| {
            let sim = Sim::simulate(a, |dr, witness| {
                let inv = Invertible::alloc(dr, witness.clone())?;
                assert_eq!(*inv.element().value().take(), *witness.snag());
                assert_eq!(
                    *inv.element().value().take() * inv.inverse().value().take(),
                    F::ONE
                );
                Ok(())
            })?;
            assert_eq!(sim.num_gates(), 1);
            assert_eq!(sim.num_constraints(), 1);
            Ok(())
        };

        alloc(F::from(4578u64))?;
        alloc(F::from(1u64))?;
        Ok(())
    }

    #[test]
    fn test_alloc_zero_fails() {
        let result = Sim::simulate(F::ZERO, |dr, witness| {
            Invertible::alloc(dr, witness.clone())?;
            Ok(())
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_invert_swaps_for_free() -> Result<()> {
        Sim::simulate(F::from(7u64), |dr, witness| {
            let inv = Invertible::alloc(dr, witness.clone())?;
            let a_wire = *inv.element().wire();
            let b_wire = *inv.inverse().wire();

            dr.reset();
            let swapped = inv.invert();

            assert_eq!(*swapped.element().wire(), b_wire);
            assert_eq!(*swapped.inverse().wire(), a_wire);
            Ok(())
        })?;

        let sim = Sim::simulate(F::from(7u64), |dr, witness| {
            let inv = Invertible::alloc(dr, witness.clone())?;
            dr.reset();
            let _ = inv.invert();
            Ok(())
        })?;
        assert_eq!(sim.num_gates(), 0);
        assert_eq!(sim.num_constraints(), 0);

        Ok(())
    }

    #[test]
    fn test_enforce_consistent() -> Result<()> {
        let sim = Sim::simulate(F::from(5u64), |dr, witness| {
            let inv = Invertible::alloc(dr, witness.clone())?;
            dr.reset();
            inv.enforce_consistent(dr)?;
            Ok(())
        })?;
        assert_eq!(sim.num_gates(), 1);
        assert_eq!(sim.num_constraints(), 3);
        Ok(())
    }
}
