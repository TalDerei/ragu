//! Copying circuit for the nested section.
//!
//! Final form relates the current step's preamble to a child proof's
//! bridge stages, ensuring that child commitments stashed in
//! [`ChildWitness`](crate::internal::nested::stages::preamble::ChildWitness)
//! match the actual values committed in the child's bridge stages. One
//! instance per child proof ([`Side::Left`] and [`Side::Right`]).
//!
//! In this initial commit the circuit's stage skeleton is in place but
//! no `enforce_equal` calls fire — the bonding polynomial folds to zero
//! so the `grouped_bonding_claim` passes trivially.

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
    Side,
    endoscalar::{EndoscalarStage, PointsStage},
    nested::{NUM_ENDOSCALING_POINTS, stages},
};

/// Copying circuit that relates the current preamble to a child's stages.
pub struct Circuit<C: CurveAffine, R: Rank> {
    side: Side,
    _marker: PhantomData<(C, R)>,
}

impl<C: CurveAffine, R: Rank> Circuit<C, R> {
    pub fn new(side: Side) -> Self {
        Self {
            side,
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
        // `side` is recorded for future enforce_equal dispatch.
        let _ = self.side;
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
