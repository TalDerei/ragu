//! Segment placement within the polynomial layout.
//!
//! Converts per-segment constraint records (from the `metrics` module) into
//! absolute offsets that the `s(X, Y)` evaluators use to position each
//! segment's constraints within the polynomial.
//!
//! # DFS-order indexing convention
//!
//! The floor plan is indexed by DFS synthesis order: `floor_plan[i]` describes
//! where the *i*-th segment (in DFS order) is placed in the polynomial.
//! Currently, offsets must also be the DFS-order prefix sums of the segment
//! sizes. All consumers — the three `s(X, Y)` evaluators, the `rx` evaluator,
//! and `assemble` — depend on this convention.
//!
//! The root segment (index 0) is always pinned at offset 0; see the
//! [`floor_plan`] function for details.
//!
//! ```text
//!  Synthesis trace              Seg
//!  ────────────────────────     ───
//!  ├─ c0 ······················ [0]  (root)
//!  ├─ call RoutineA
//!  │   └─ ···················── [1]
//!  ├─ c1 ······················ [0]  (root)
//!  ├─ call RoutineB
//!  │   ├─ b0 ·················· [2]
//!  │   ├─ call RoutineC
//!  │   │   └─ ················· [3]
//!  │   └─ b1 ·················· [2]
//!  └─ c2 ······················ [0]  (root)
//!
//!  floor_plan indices are DFS encounter order:
//!    [0]  root ── c0 + c1 + c2  (everything outside routines)
//!    [1]  A    ── A's own constraints
//!    [2]  B    ── b0 + b1       (RoutineC excluded)
//!    [3]  C    ── C's own constraints
//! ```
//!
//! See [`SegmentRecord`] for a fully worked example with concrete numbers.

use alloc::vec::Vec;

use ragu_core::{Error, Result};

use super::metrics::SegmentRecord;

/// A segment's placement in a constraint system.
///
/// Each segment in a circuit occupies a contiguous range of gates and
/// constraints. The primary segment boundaries are [`Routine`]
/// calls; index 0 is the root segment (not backed by any [`Routine`]).
/// The floor plan assigns absolute positions (offsets) and sizes to each
/// segment in DFS order.
///
/// The floor plan is indexed by DFS synthesis order: `floor_plan[i]`
/// corresponds to the *i*-th segment encountered during synthesis. Offsets are
/// validated as DFS-order prefix sums over segment sizes. The root segment
/// (index 0) must always be placed at the polynomial origin (both offsets
/// zero).
///
/// A future floor planner that reorders segment positions for alignment or
/// packing must also update the validated invariants consumed by evaluators.
///
/// [`Routine`]: ragu_core::routines::Routine
pub struct ConstraintSegment {
    /// Gate index where this segment's gates begin.
    pub(crate) gate_start: usize,
    /// Y-power index where this segment's constraints begin.
    pub(crate) constraint_start: usize,
    /// Number of gates in this segment.
    pub(crate) num_gates: usize,
    /// Number of constraints in this segment.
    pub(crate) num_constraints: usize,
}

pub(crate) fn validate(floor_plan: &[ConstraintSegment]) -> Result<()> {
    if floor_plan.is_empty() {
        return Err(Error::MalformedFloorPlan {
            reason: "floor plan must contain a root segment",
        });
    }

    let root = &floor_plan[0];
    if root.gate_start != 0 || root.constraint_start != 0 {
        return Err(Error::MalformedFloorPlan {
            reason: "root segment must be placed at the polynomial origin",
        });
    }

    let mut expected_gate_start = 0usize;
    let mut expected_constraint_start = 0usize;
    for seg in floor_plan {
        if seg.gate_start != expected_gate_start {
            return Err(Error::MalformedFloorPlan {
                reason: "gate ranges must be contiguous in DFS order",
            });
        }
        if seg.constraint_start != expected_constraint_start {
            return Err(Error::MalformedFloorPlan {
                reason: "constraint ranges must be contiguous in DFS order",
            });
        }

        expected_gate_start =
            expected_gate_start
                .checked_add(seg.num_gates)
                .ok_or(Error::MalformedFloorPlan {
                    reason: "gate range exceeds usize",
                })?;
        expected_constraint_start = expected_constraint_start
            .checked_add(seg.num_constraints)
            .ok_or(Error::MalformedFloorPlan {
                reason: "constraint range exceeds usize",
            })?;
    }

    Ok(())
}

/// Computes a floor plan from per-segment constraint records.
///
/// Converts per-segment constraint counts into absolute offsets via prefix
/// sum, preserving synthesis (DFS) order.
pub fn floor_plan(segment_records: &[SegmentRecord]) -> Vec<ConstraintSegment> {
    let mut result = Vec::with_capacity(segment_records.len());
    let mut gate_start = 0usize;
    let mut constraint_start = 0usize;
    for record in segment_records {
        result.push(ConstraintSegment {
            gate_start,
            constraint_start,
            num_gates: record.num_gates(),
            num_constraints: record.num_constraints(),
        });
        gate_start += record.num_gates();
        constraint_start += record.num_constraints();
    }

    if !result.is_empty() {
        validate(&result).expect("floor planner must produce a valid floor plan");
    }

    result
}

#[cfg(test)]
mod tests {
    use super::{ConstraintSegment, validate};

    fn seg(
        gate_start: usize,
        constraint_start: usize,
        num_gates: usize,
        num_constraints: usize,
    ) -> ConstraintSegment {
        ConstraintSegment {
            gate_start,
            constraint_start,
            num_gates,
            num_constraints,
        }
    }

    #[test]
    fn accepts_prefix_sum_floor_plan() {
        let floor_plan = [
            seg(0, 0, 2, 3),
            seg(2, 3, 0, 1),
            seg(2, 4, 4, 0),
            seg(6, 4, 1, 2),
        ];

        validate(&floor_plan).unwrap();
    }

    #[test]
    fn rejects_empty_floor_plan() {
        assert!(validate(&[]).is_err());
    }

    #[test]
    fn rejects_nonzero_root_offset() {
        let floor_plan = [seg(0, 1, 1, 1)];

        assert!(validate(&floor_plan).is_err());
    }

    #[test]
    fn rejects_overlapping_range() {
        let floor_plan = [seg(0, 0, 2, 2), seg(1, 2, 1, 1)];

        assert!(validate(&floor_plan).is_err());
    }

    #[test]
    fn rejects_hole_or_reordered_range() {
        let floor_plan = [seg(0, 0, 1, 1), seg(2, 1, 1, 1)];

        assert!(validate(&floor_plan).is_err());
    }
}
