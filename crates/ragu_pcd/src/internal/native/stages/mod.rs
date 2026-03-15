//! Native field stages for fuse operations.

pub mod error_m;
pub mod error_n;
pub mod eval;
pub mod preamble;
pub mod query;

#[cfg(test)]
pub mod tests {
    use ff::PrimeField;
    use ragu_circuits::{polynomials::Rank, staging::Stage};
    use ragu_core::{
        drivers::emulator::{Emulator, Wireless},
        gadgets::{Bound, Gadget},
        maybe::Empty,
    };

    pub type R = ragu_circuits::polynomials::ProductionRank;
    pub use crate::internal::native::RevdotParameters;
    pub use crate::internal::tests::HEADER_SIZE;

    pub fn assert_stage_values<F, R, S>(stage: &S)
    where
        F: PrimeField,
        R: Rank,
        S: Stage<F, R>,
        for<'dr> Bound<'dr, Emulator<Wireless<Empty, F>>, S::OutputKind>:
            Gadget<'dr, Emulator<Wireless<Empty, F>>>,
    {
        let mut emulator = Emulator::counter();
        let output = stage
            .witness(&mut emulator, Empty)
            .expect("allocation should succeed");

        assert_eq!(
            output.num_wires().expect("wire counting should succeed"),
            S::values(),
            "Stage::values() does not match actual wire count"
        );
    }
}
