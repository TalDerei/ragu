use ragu_arithmetic::Cycle;
use ragu_circuits::{
    polynomials::{Rank, structured},
    registry::CircuitIndex,
};

use crate::{
    Proof,
    internal::{claims::Source, native::RxComponent},
};

pub(crate) struct FuseProofSource<'rx, C: Cycle, R: Rank> {
    pub(crate) left: &'rx Proof<C, R>,
    pub(crate) right: &'rx Proof<C, R>,
}

impl<'rx, C: Cycle, R: Rank> Source for FuseProofSource<'rx, C, R> {
    type RxComponent = RxComponent;
    type Rx = &'rx structured::Polynomial<C::CircuitField, R>;
    type AppCircuitId = CircuitIndex;

    fn rx(&self, component: RxComponent) -> impl Iterator<Item = Self::Rx> {
        [
            self.left.native_rx(component),
            self.right.native_rx(component),
        ]
        .into_iter()
    }

    fn app_circuits(&self) -> impl Iterator<Item = Self::AppCircuitId> {
        [
            self.left.application.circuit_id,
            self.right.application.circuit_id,
        ]
        .into_iter()
    }
}
