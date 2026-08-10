//! Error-swallowing trust boundary.
//!
//! Circuits are trusted to propagate driver errors with `?`. A malicious
//! circuit can instead drop an error and let synthesis continue. These tests
//! pin what actually happens on each synthesis path when it does: the trace
//! evaluator records nothing for the failed gate, the metrics counter (which
//! never runs closures) still counts it, and the resulting gate-count
//! desynchronization is caught when the trace is assembled against the floor
//! plan.

use alloc::format;

use ragu_arithmetic::ff::Field;
use ragu_core::{
    Error, Result,
    drivers::{Driver, DriverValue},
    gadgets::{Bound, Kind},
    maybe::Maybe,
};
use ragu_pasta::Fp;
use ragu_primitives::{Element, allocator::Standard};

use crate::{
    Circuit, CircuitExt, WithAux, floor_planner, into_wiring_object, polynomials::TestRank,
};

/// Well-behaved reference circuit: allocates `a` and `b`, outputs `(a + b, a - b)`.
///
/// Serves as the control for the error-swallowing circuits below: same shape,
/// same allocations, no dropped errors.
struct WellBehavedCircuit;

impl Circuit<Fp> for WellBehavedCircuit {
    type Instance<'instance> = (Fp, Fp);
    type Output = Kind![Fp; (Element<'_, _>, Element<'_, _>)];
    type Witness<'witness> = (Fp, Fp);
    type Aux<'witness> = ();

    fn instance<'dr, 'instance: 'dr, D: Driver<'dr, F = Fp>>(
        &self,
        dr: &mut D,
        instance: DriverValue<D, Self::Instance<'instance>>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        let allocator = &mut Standard::new();
        let c = Element::alloc(dr, allocator, instance.as_ref().map(|v| v.0))?;
        let d = Element::alloc(dr, allocator, instance.as_ref().map(|v| v.1))?;
        Ok((c, d))
    }

    fn witness<'dr, 'witness: 'dr, D: Driver<'dr, F = Fp>>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, Self::Witness<'witness>>,
    ) -> Result<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'witness>>>> {
        let allocator = &mut Standard::new();
        let a = Element::alloc(dr, allocator, witness.as_ref().map(|w| w.0))?;
        let b = Element::alloc(dr, allocator, witness.as_ref().map(|w| w.1))?;
        let c = a.add(dr, &b);
        let d = a.sub(dr, &b);
        Ok(WithAux::new((c, d), D::unit()))
    }
}

/// Malicious circuit: identical shape to [`WellBehavedCircuit`], but drops the
/// error from a bogus gate placed between the two real allocations.
///
/// Exercises the trust boundary where circuits are expected to propagate driver
/// errors with `?`. The two synthesis paths disagree about whether that gate
/// exists:
///
/// * [`trace`](crate::trace)'s evaluator has `MaybeKind = Always`, so
///   [`gate`](ragu_core::drivers::DriverTypes::gate) evaluates the closure
///   before touching any segment. The closure fails, nothing is recorded, and
///   the swallowed error leaves the trace byte-identical to the well-behaved
///   one.
/// * [`metrics`](crate::metrics)'s counter has `MaybeKind = Empty` and never
///   calls the closure, so it counts the gate.
///
/// The result is a gate-count desynchronization rather than corrupted wire
/// values; see [`test_error_swallowing_desyncs_trace_and_metrics`].
struct ErrorSwallowingCircuit;

impl Circuit<Fp> for ErrorSwallowingCircuit {
    type Instance<'instance> = (Fp, Fp);
    type Output = Kind![Fp; (Element<'_, _>, Element<'_, _>)];
    type Witness<'witness> = (Fp, Fp);
    type Aux<'witness> = ();

    fn instance<'dr, 'instance: 'dr, D: Driver<'dr, F = Fp>>(
        &self,
        dr: &mut D,
        instance: DriverValue<D, Self::Instance<'instance>>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        let allocator = &mut Standard::new();
        let c = Element::alloc(dr, allocator, instance.as_ref().map(|v| v.0))?;
        let d = Element::alloc(dr, allocator, instance.as_ref().map(|v| v.1))?;
        Ok((c, d))
    }

    fn witness<'dr, 'witness: 'dr, D: Driver<'dr, F = Fp>>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, Self::Witness<'witness>>,
    ) -> Result<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'witness>>>> {
        let allocator = &mut Standard::new();
        let a = Element::alloc(dr, allocator, witness.as_ref().map(|w| w.0))?;
        // Swallow the error rather than propagating it with `?`.
        let _ = dr.mul(|| Err(Error::InvalidWitness("swallowed".into())));
        let b = Element::alloc(dr, allocator, witness.as_ref().map(|w| w.1))?;
        let c = a.add(dr, &b);
        let d = a.sub(dr, &b);
        Ok(WithAux::new((c, d), D::unit()))
    }
}

/// Positive control: a circuit that propagates a gate error with `?` causes
/// [`CircuitExt::trace`] to fail, confirming that the trace driver surfaces the
/// error. This is the complement to the [`ErrorSwallowingCircuit`] tests.
#[test]
fn test_propagated_gate_error_caught() {
    struct ErrorPropagatingCircuit;

    impl Circuit<Fp> for ErrorPropagatingCircuit {
        type Instance<'instance> = (Fp, Fp);
        type Output = Kind![Fp; (Element<'_, _>, Element<'_, _>)];
        type Witness<'witness> = (Fp, Fp);
        type Aux<'witness> = ();

        fn instance<'dr, 'instance: 'dr, D: Driver<'dr, F = Fp>>(
            &self,
            dr: &mut D,
            instance: DriverValue<D, Self::Instance<'instance>>,
        ) -> Result<Bound<'dr, D, Self::Output>> {
            let allocator = &mut Standard::new();
            let c = Element::alloc(dr, allocator, instance.as_ref().map(|v| v.0))?;
            let d = Element::alloc(dr, allocator, instance.as_ref().map(|v| v.1))?;
            Ok((c, d))
        }

        fn witness<'dr, 'witness: 'dr, D: Driver<'dr, F = Fp>>(
            &self,
            dr: &mut D,
            witness: DriverValue<D, Self::Witness<'witness>>,
        ) -> Result<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'witness>>>>
        {
            let allocator = &mut Standard::new();
            let a = Element::alloc(dr, allocator, witness.as_ref().map(|w| w.0))?;
            // Propagate the error with `?` — unlike ErrorSwallowingCircuit.
            let _bogus = dr.mul(|| Err(Error::InvalidWitness("propagated".into())))?;
            let b = Element::alloc(dr, allocator, witness.as_ref().map(|w| w.1))?;
            let c = a.add(dr, &b);
            let d = a.sub(dr, &b);
            Ok(WithAux::new((c, d), D::unit()))
        }
    }

    let witness = (Fp::from(3u64), Fp::from(7u64));
    match ErrorPropagatingCircuit.trace(witness) {
        Err(Error::InvalidWitness(err)) => {
            assert_eq!(format!("{err}"), "propagated");
        }
        Err(other) => panic!("expected InvalidWitness, got {other:?}"),
        Ok(_) => panic!("trace should fail when a gate error is propagated with `?`"),
    }
}

/// The trace driver evaluates a gate's closure before recording anything, so a
/// swallowed error leaves no residue: the malicious trace is identical to the
/// well-behaved one, wire for wire.
///
/// Note that `b` and `c` are zero in both traces. [`Standard`] packs two
/// allocations into one gate's unconstrained $A$ and $D$ wires, so allocation
/// never writes to the $B$ or $C$ slots.
#[test]
fn test_error_swallowing_is_invisible_to_trace() {
    let witness = (Fp::from(3u64), Fp::from(7u64));

    let good = WellBehavedCircuit.trace(witness).unwrap().into_output();
    let bad = ErrorSwallowingCircuit.trace(witness).unwrap().into_output();

    assert_eq!(good.segments.len(), 1);
    assert_eq!(bad.segments.len(), 1);

    let (good, bad) = (&good.segments[0], &bad.segments[0]);
    assert_eq!(
        good.a.len(),
        bad.a.len(),
        "the swallowed gate must not appear in the trace"
    );
    assert_eq!(good.a, bad.a);
    assert_eq!(good.b, bad.b);
    assert_eq!(good.c, bad.c);
    assert_eq!(good.d, bad.d);

    // Segment 0 holds the SYSTEM gate plus the one gate that carries both
    // paired allocations in its A and D wires.
    assert_eq!(good.a.len(), 2);
    assert_eq!(good.a[1], Fp::from(3u64));
    assert_eq!(good.d[1], Fp::from(7u64));
    assert_eq!(good.b[1], Fp::ZERO);
    assert_eq!(good.c[1], Fp::ZERO);
}

/// The swallowed error is visible to the metrics driver but not to the trace
/// driver, so the two disagree on the gate count. This desynchronization — not
/// corrupted wire values — is what a swallowed error actually produces. The
/// wiring drivers themselves stay self-consistent throughout: `sx`, `sy` and
/// `sxy` never run witness closures, so the bogus gate perturbs only the gate
/// count, never $s(X, Y)$.
#[test]
fn test_error_swallowing_desyncs_trace_and_metrics() {
    let witness = (Fp::from(3u64), Fp::from(7u64));

    let good_obj = into_wiring_object::<_, _, TestRank>(WellBehavedCircuit).unwrap();
    let bad_obj = into_wiring_object::<_, _, TestRank>(ErrorSwallowingCircuit).unwrap();

    let (good_gates, good_constraints) = good_obj.constraint_counts();
    let (bad_gates, bad_constraints) = bad_obj.constraint_counts();

    assert_eq!(
        good_gates + 1,
        bad_gates,
        "the metrics driver never calls the closure, so it counts the bogus gate"
    );
    assert_eq!(
        good_constraints, bad_constraints,
        "the bogus gate adds no linear constraint"
    );

    let trace = ErrorSwallowingCircuit.trace(witness).unwrap().into_output();
    assert_eq!(
        trace.segments[0].a.len() + 1,
        bad_gates,
        "the trace is one gate short of what the wiring object expects"
    );
}

/// The gate-count desynchronization is caught when the trace is assembled
/// against its own floor plan.
#[test]
#[should_panic(expected = "segment 0 size must match floor plan")]
fn test_error_swallowing_trace_assembly_rejected() {
    let witness = (Fp::from(3u64), Fp::from(7u64));

    let obj = into_wiring_object::<_, _, TestRank>(ErrorSwallowingCircuit).unwrap();
    let plan = floor_planner::floor_plan(obj.segment_records());
    let trace = ErrorSwallowingCircuit.trace(witness).unwrap().into_output();

    let _ = trace.assemble::<TestRank>(&plan, Fp::ZERO);
}
