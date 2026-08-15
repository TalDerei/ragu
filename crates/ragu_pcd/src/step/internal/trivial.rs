//! Internal step that bootstraps the recursion.
//!
//! This is the only step that declares [`Bootstrap`] inputs, and therefore the
//! only step whose fuse is treated as the base case. Fusing two synthesized
//! [`trivial_pcd`] dummies through it yields a genuine, verifying `Pcd<()>`,
//! which [`seed`] and [`rerandomize`] then consume as ordinary children.
//!
//! Confining the base case here keeps it off application steps: a step's
//! declared input suffix is a circuit constant, so no application step can
//! present the [`Bootstrap`] suffix, and every fuse other than this one has its
//! child claims enforced.
//!
//! [`trivial_pcd`]: crate::Application::trivial_pcd
//! [`seed`]: crate::Application::seed
//! [`rerandomize`]: crate::Application::rerandomize

use ragu_arithmetic::Cycle;
use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
};
use ragu_primitives::allocator::Standard;

use super::super::{Encoded, Index, Step};
use crate::{Header, header::Bootstrap};
pub(crate) use crate::step::InternalStepIndex::Trivial as INTERNAL_ID;

pub(crate) struct Trivial;

impl Trivial {
    pub fn new() -> Self {
        Trivial
    }
}

impl<C: Cycle> Step<C> for Trivial {
    const INDEX: Index = Index::internal(INTERNAL_ID);

    type Witness<'source> = ();
    type Aux<'source> = ();

    type Left = Bootstrap;
    type Right = Bootstrap;
    type Output = ();

    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = C::CircuitField>, const HEADER_SIZE: usize>(
        &self,
        dr: &mut D,
        _: DriverValue<D, Self::Witness<'source>>,
        left: DriverValue<D, ()>,
        right: DriverValue<D, ()>,
    ) -> Result<(
        (
            Encoded<'dr, D, Self::Left, HEADER_SIZE>,
            Encoded<'dr, D, Self::Right, HEADER_SIZE>,
            Encoded<'dr, D, Self::Output, HEADER_SIZE>,
        ),
        DriverValue<D, <Self::Output as Header<C::CircuitField>>::Data>,
        DriverValue<D, Self::Aux<'source>>,
    )> {
        let allocator = &mut Standard::new();
        let left = Encoded::new(dr, allocator, left)?;
        let right = Encoded::new(dr, allocator, right)?;
        let output = Encoded::from_gadget(());

        Ok(((left, right, output), D::unit(), D::unit()))
    }
}
