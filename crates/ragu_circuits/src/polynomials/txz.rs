//! In-circuit evaluation of the gate polynomial
//! $$t(x, z) = -\sum_{i=0}^{n - 1} x^{4n - 1 - i} (z^{2n - 1 - i} + z^{2n + i})$$
//! as a [`Routine`].

use core::marker::PhantomData;

use ff::Field;
use ragu_arithmetic::geosum;
use ragu_core::{
    Error, Result,
    drivers::{Driver, DriverValue},
    gadgets::{Bound, Kind},
    maybe::Maybe,
    routines::{Prediction, Routine},
};
use ragu_primitives::Element;

use super::Rank;

/// [`Routine`] evaluating $t(x, z)$ at rank `R`.
///
/// Requires $x, z \neq 0$. The auxiliary witness carries the inversions
/// $(x^{-1}, z^{-1})$ from [`Routine::predict`] into [`Routine::execute`], so
/// those witnesses are produced once rather than re-derived at circuit
/// allocation time.
#[derive(Clone)]
pub struct Evaluate<R> {
    _marker: PhantomData<R>,
}

impl<R: Rank> Default for Evaluate<R> {
    fn default() -> Self {
        Self::new()
    }
}

impl<R: Rank> Evaluate<R> {
    /// Creates the routine.
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }
}

impl<F: Field, R: Rank> Routine<F> for Evaluate<R> {
    type Input = Kind![F; (Element<'_, _>, Element<'_, _>)];
    type Output = Kind![F; Element<'_, _>];
    type Aux<'dr> = (F, F);

    fn execute<'dr, D: Driver<'dr, F = F>>(
        &self,
        dr: &mut D,
        input: Bound<'dr, D, Self::Input>,
        aux: DriverValue<D, Self::Aux<'dr>>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        let x = input.0;
        let z = input.1;

        let mut xn = x.clone();
        for _ in 0..R::log2_n() {
            xn = xn.square(dr)?;
        }
        let x2n = xn.square(dr)?;
        let x4n = x2n.square(dr)?;
        let mut zn = z.clone();
        for _ in 0..R::log2_n() {
            zn = zn.square(dr)?;
        }
        let z2n = zn.square(dr)?;

        let (x_inv_val, z_inv_val) = aux.cast();
        let x_inv = x.invert_with(dr, x_inv_val)?;
        let z_inv = z.invert_with(dr, z_inv_val)?;

        let x4n_minus_1 = x4n.mul(dr, &x_inv)?;
        let mut l = x4n_minus_1.mul(dr, &z2n)?;
        let mut r = l.clone();
        let mut xz_step = x_inv.mul(dr, &z)?;
        let mut xzinv_step = x_inv.mul(dr, &z_inv)?;
        for _ in 0..R::log2_n() {
            let l_mul = l.mul(dr, &xz_step)?;
            l = l.add(dr, &l_mul);
            let r_mul = r.mul(dr, &xzinv_step)?;
            r = r.add(dr, &r_mul);
            xz_step = xz_step.square(dr)?;
            xzinv_step = xzinv_step.square(dr)?;
        }
        let r_zinv = r.mul(dr, &z_inv)?;
        let sum = l.add(dr, &r_zinv);
        Ok(sum.negate(dr))
    }

    fn predict<'dr, D: Driver<'dr, F = F>>(
        &self,
        dr: &mut D,
        input: &Bound<'dr, D, Self::Input>,
    ) -> Result<Prediction<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'dr>>>> {
        let n = 1u64 << R::log2_n();

        let aux = D::try_just(|| {
            let x = *input.0.value().take();
            let z = *input.1.value().take();

            let x_inv = x
                .invert()
                .into_option()
                .ok_or_else(|| Error::InvalidWitness("division by zero".into()))?;
            let z_inv = z
                .invert()
                .into_option()
                .ok_or_else(|| Error::InvalidWitness("division by zero".into()))?;

            Ok((x_inv, z_inv))
        })?;

        let output = Element::alloc(
            dr,
            &mut (),
            D::try_just(|| {
                let x = *input.0.value().take();
                let z = *input.1.value().take();
                let (x_inv, z_inv) = *aux.snag();

                // Splitting $(z^{2n - 1 - i} + z^{2n + i})$ gives two geometric
                // sums sharing the prefactor $l_0 = x^{4n - 1} z^{2n}$; the
                // first picks up an extra $z^{-1}$, applied below.
                let l0 = x.pow([4 * n - 1]) * z.pow([2 * n]);
                let l = l0 * geosum(x_inv * z, n as usize);
                let r = l0 * geosum(x_inv * z_inv, n as usize);

                Ok(-(l + r * z_inv))
            })?,
        )?;

        Ok(Prediction::Known(output, aux))
    }
}

#[cfg(test)]
mod tests {
    use ragu_pasta::Fp;
    use ragu_primitives::{Simulator, allocator::Standard};

    use super::*;
    use crate::polynomials::ProductionRank;

    #[test]
    fn simulate_txz() -> Result<()> {
        // ProductionRank (R<13>) has log2_n = 11
        type TestRank = ProductionRank;

        let x = Fp::random(&mut rand::rng());
        let z = Fp::random(&mut rand::rng());
        let evaluator = Evaluate::<TestRank>::new();

        Simulator::simulate((x, z), |dr, witness| {
            let (x, z) = witness.cast();
            let allocator = &mut Standard::new();
            let x = Element::alloc(dr, allocator, x)?;
            let z = Element::alloc(dr, allocator, z)?;

            dr.reset();
            dr.routine(evaluator.clone(), (x, z))?;
            assert_eq!(dr.num_gates(), 76);
            assert_eq!(dr.num_constraints(), 152);

            Ok(())
        })?;

        Ok(())
    }
}
