//! Completeness (over-constraint) fuzzing: a correct circuit accepts
//! *every* valid witness, not just the honest one. The rest of the patcher
//! suite chases soundness (a witness wrongly accepted); this is the dual —
//! an over-constrained gadget wrongly *rejects* a witness it should accept.
//!
//! For an anchorless program over the infallible vocabulary, every
//! assignment of the preamble witness is valid: the gadgets compute derived
//! values that satisfy their own constraints by construction, with no anchor
//! pinning anything and no value-dependent failure possible. So ragu's real
//! [`Simulator`] must accept every randomly-sampled witness. A rejection is
//! an over-constraint — a completeness bug.

use proptest::prelude::*;
use ragu_core::maybe::{Always, MaybeKind};
use ragu_pasta::Fp;
use ragu_primitives::{Simulator, allocator::Standard};
use ragu_testing::substrate::{
    Capabilities, Limits, OpSet, Preamble, Program, program_strategy, synthesize_with_witness,
};

/// The infallible, anchorless vocabulary: no value-fallible ops (so no
/// witness can trigger a divide-by-zero rejection) and no anchors (so no
/// witness is pinned to a constant). Every preamble witness is then valid.
fn completeness_opset() -> OpSet {
    OpSet::ALL
        .without(Capabilities::VALUE_FALLIBLE)
        .without(Capabilities::ANCHORS)
}

/// Runs `program` with the given preamble `witness` through ragu's real
/// constraint checker and returns whether it accepts.
fn simulator_accepts(program: &Program, witness: [Fp; Preamble::LEN]) -> bool {
    Simulator::<Fp>::simulate((), |dr, _| {
        synthesize_with_witness(
            dr,
            &mut Standard::new(),
            program,
            Always::maybe_just(move || witness),
            &[],
        )?;
        Ok(())
    })
    .is_ok()
}

proptest! {
    /// Every randomly-sampled preamble witness is accepted by the real
    /// Simulator — the circuit is not over-constrained.
    #[test]
    fn proptest_every_witness_accepted(
        program in program_strategy(completeness_opset(), Limits::default().max_ops),
        witnesses in proptest::collection::vec(
            proptest::collection::vec(any::<u64>(), Preamble::LEN),
            1..6,
        ),
    ) {
        for raw in witnesses {
            let witness: [Fp; Preamble::LEN] =
                core::array::from_fn(|i| Fp::from(raw[i]));
            prop_assert!(
                simulator_accepts(&program, witness),
                "over-constrained: Simulator rejected a valid witness {:?} for {:?}",
                witness,
                program,
            );
        }
    }
}

/// A handcrafted distinct-witness check: a program with real free advice has
/// many satisfying witnesses, and all are accepted.
#[test]
fn distinct_witnesses_all_accepted() {
    use ragu_testing::substrate::Op;

    let program = Program {
        preamble: Preamble {
            seeds: [1, 2, 3, 4],
            large_seeds: [[1, 2, 3, 4], [5, 6, 7, 8]],
            special_seeds: [1, 11],
            constant_mask: 0, // all eight preamble slots are free witness
        },
        ops: vec![
            Op::Add(0, 1),
            Op::Mul(2, 3),
            Op::Square(4),
            Op::Double(5),
            Op::Fold(0, 1, 9),
        ],
    };
    for k in 0..32u64 {
        let witness: [Fp; Preamble::LEN] = core::array::from_fn(|i| Fp::from(k * 8 + i as u64));
        assert!(
            simulator_accepts(&program, witness),
            "over-constrained: witness {witness:?} rejected",
        );
    }
}
