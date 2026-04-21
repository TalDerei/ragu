//! Loading circuit for the nested section.
//!
//! Final form walks every input of [`PointsStage`] and enforces equality
//! against the corresponding bridge stage values in the same order that
//! `compute_p` accumulates them. In this initial commit the circuit's
//! stage skeleton is in place but no `enforce_equal` calls fire — the
//! bonding polynomial folds to zero so the `grouped_bonding_claim` is
//! trivially satisfied.

use core::marker::PhantomData;

use ragu_arithmetic::CurveAffine;
use ragu_circuits::{
    WithAux,
    polynomials::Rank,
    staging::{MultiStageCircuit, StageBuilder},
};
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    gadgets::Bound,
};

use crate::internal::{
    endoscalar::{EndoscalarStage, PointsStage},
    nested::{NUM_ENDOSCALING_POINTS, stages},
};

/// Loading circuit that loads the entire nested stage hierarchy.
pub struct Circuit<C: CurveAffine, R: Rank> {
    _marker: PhantomData<(C, R)>,
}

impl<C: CurveAffine, R: Rank> Circuit<C, R> {
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }
}

impl<C: CurveAffine, R: Rank> MultiStageCircuit<C::Base, R> for Circuit<C, R> {
    type Last = stages::eval::Stage<C, R>;
    type Instance<'source> = ();
    type Witness<'source> = ();
    type Output = ();
    type Aux<'source> = ();

    fn instance<'dr, 'source: 'dr, D: Driver<'dr, F = C::Base>>(
        &self,
        _dr: &mut D,
        _instance: DriverValue<D, ()>,
    ) -> Result<Bound<'dr, D, ()>> {
        Ok(())
    }

    fn witness<'a, 'dr, 'source: 'dr, D: Driver<'dr, F = C::Base>>(
        &self,
        dr: StageBuilder<'a, 'dr, D, R, (), Self::Last>,
        _witness: DriverValue<D, ()>,
    ) -> Result<WithAux<Bound<'dr, D, ()>, DriverValue<D, ()>>> {
        let dr = dr.skip_stage::<EndoscalarStage>()?;
        let (_points_guard, dr) = dr.add_stage::<PointsStage<C, NUM_ENDOSCALING_POINTS>>()?;
        let (_preamble_guard, dr) = dr.add_stage::<stages::preamble::Stage<C, R>>()?;
        let dr = dr.skip_stage::<stages::s_prime::Stage<C, R>>()?;
        let dr = dr.skip_stage::<stages::inner_error::Stage<C, R>>()?;
        let dr = dr.skip_stage::<stages::outer_error::Stage<C, R>>()?;
        let dr = dr.skip_stage::<stages::ab::Stage<C, R>>()?;
        let dr = dr.skip_stage::<stages::query::Stage<C, R>>()?;
        let dr = dr.skip_stage::<stages::f::Stage<C, R>>()?;
        let dr = dr.skip_stage::<stages::eval::Stage<C, R>>()?;
        let _dr = dr.finish();

        Ok(WithAux::new((), D::unit()))
    }
}
