#![allow(non_snake_case)]

mod identity;
mod segment_order;

use alloc::format;

use ragu_arithmetic::ff::Field;
use ragu_core::{
    Error, Result,
    drivers::{Driver, DriverValue, LinearExpression},
    gadgets::{Bound, Kind},
    maybe::{Always, Maybe},
    routines::{Prediction, Routine},
};
use ragu_pasta::Fp;
use ragu_primitives::{Element, Simulator, allocator::Standard};

use crate::{
    Circuit, CircuitExt, WiringObject, WithAux, floor_planner, into_wiring_object,
    polynomials::{Rank, TestRank},
};

/// Dummy circuit.
pub struct SquareCircuit {
    pub times: usize,
}

impl Circuit<Fp> for SquareCircuit {
    type Instance<'instance> = Fp;
    type Output = Kind![Fp; Element<'_, _>];
    type Witness<'witness> = Fp;
    type Aux<'witness> = ();

    fn instance<'dr, 'instance: 'dr, D: Driver<'dr, F = Fp>>(
        &self,
        dr: &mut D,
        instance: DriverValue<D, Self::Instance<'instance>>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        let allocator = &mut Standard::new();
        Element::alloc(dr, allocator, instance)
    }

    fn witness<'dr, 'witness: 'dr, D: Driver<'dr, F = Fp>>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, Self::Witness<'witness>>,
    ) -> Result<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'witness>>>> {
        let allocator = &mut Standard::new();
        let mut a = Element::alloc(dr, allocator, witness)?;

        for _ in 0..self.times {
            a = a.square(dr)?;
        }

        Ok(WithAux::new(a, D::unit()))
    }
}

fn consistency_checks<R: Rank>(obj: &dyn WiringObject<Fp, R>) {
    let x = Fp::random(&mut ragu_arithmetic::rand::rng());
    let y = Fp::random(&mut ragu_arithmetic::rand::rng());
    let plan = floor_planner::floor_plan(obj.segment_records());

    let sxy_eval = obj.sxy(x, y, &plan);
    let s0y_eval = obj.sxy(Fp::ZERO, y, &plan);
    let sx0_eval = obj.sxy(x, Fp::ZERO, &plan);
    let s00_eval = obj.sxy(Fp::ZERO, Fp::ZERO, &plan);

    let sxY_poly = obj.sx(x, &plan);
    let sXy_poly = obj.sy(y, &plan);
    let s0Y_poly = obj.sx(Fp::ZERO, &plan);
    let sX0_poly = obj.sy(Fp::ZERO, &plan);

    assert_eq!(sxy_eval, sXy_poly.eval(x));
    assert_eq!(sxy_eval, sxY_poly.eval(y));
    assert_eq!(s0y_eval, sXy_poly.eval(Fp::ZERO));
    assert_eq!(sx0_eval, sxY_poly.eval(Fp::ZERO));
    assert_eq!(s0y_eval, s0Y_poly.eval(y));
    assert_eq!(sx0_eval, sX0_poly.eval(x));
    assert_eq!(s00_eval, s0Y_poly.eval(Fp::ZERO));
    assert_eq!(s00_eval, sX0_poly.eval(Fp::ZERO));
}

#[test]
fn test_simple_circuit() {
    // Simple circuit: prove knowledge of a and b such that a^5 = b^2 and a + b = c
    // and a - b = d where c and d are public inputs.
    struct MySimpleCircuit;

    impl Circuit<Fp> for MySimpleCircuit {
        type Instance<'instance> = (Fp, Fp); // Public inputs: c and d
        type Output = Kind![Fp; (Element<'_, _>, Element<'_, _>)];
        type Witness<'witness> = (Fp, Fp); // Witness: a and b
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
            let b = Element::alloc(dr, allocator, witness.as_ref().map(|w| w.1))?;

            let a2 = a.square(dr)?;
            let a4 = a2.square(dr)?;
            let a5 = a4.mul(dr, &a)?;

            let b2 = b.square(dr)?;

            dr.enforce_zero(|lc| lc.add(a5.wire()).sub(b2.wire()))?;

            let c = a.add(dr, &b);
            let d = a.sub(dr, &b);

            Ok(WithAux::new((c, d), D::unit()))
        }
    }

    let trace = MySimpleCircuit
        .trace((
            Fp::from_raw([
                1833481853729904510,
                5119040798866070668,
                13106006979685074791,
                104139735293675522,
            ]),
            Fp::from_raw([
                1114250137190507128,
                15522336584428696251,
                4689053926428793931,
                2277752110332726989,
            ]),
        ))
        .unwrap()
        .into_output();
    type MyRank = TestRank;

    let obj = into_wiring_object::<_, _, MyRank>(MySimpleCircuit).unwrap();
    let plan = floor_planner::floor_plan(obj.segment_records());

    let assignment = trace.assemble(&plan, Fp::ZERO).unwrap();

    consistency_checks::<MyRank>(&*obj);

    let y = Fp::random(&mut ragu_arithmetic::rand::rng());
    let z = Fp::random(&mut ragu_arithmetic::rand::rng());

    let a = assignment.clone();
    let mut b = assignment.clone();
    b.dilate(z);
    b.add_assign(&obj.sy(y, &plan));
    b.add_assign(&MyRank::tz(z));

    let expected = MySimpleCircuit
        .ky(
            (
                Fp::from_raw([
                    2947731990920411638,
                    2194633309585215303,
                    17795060906113868723,
                    2381891845626402511,
                ]),
                Fp::from_raw([
                    11756763772759733511,
                    10513277942061441772,
                    8416953053256280859,
                    2438073643388336437,
                ]),
            ),
            y,
        )
        .unwrap();

    assert_eq!(expected, a.revdot(&b));
}

#[derive(Clone)]
struct TestRoutine;

impl Routine<Fp> for TestRoutine {
    type Input = Kind![Fp; Element<'_, _>];
    type Output = Kind![Fp; Element<'_, _>];
    type Aux<'dr> = Fp;

    fn execute<'dr, D: Driver<'dr, F = Fp>>(
        &self,
        dr: &mut D,
        _input: Bound<'dr, D, Self::Input>,
        aux: DriverValue<D, Self::Aux<'dr>>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        let precomputed_value = aux.take();
        let allocator = &mut Standard::new();
        let element_from_aux = Element::alloc(dr, allocator, D::just(|| precomputed_value))?;
        let other = Element::alloc(dr, allocator, D::just(|| Fp::from(5u64)))?;
        let result = element_from_aux.add(dr, &other);
        Ok(result)
    }

    fn predict<'dr, D: Driver<'dr, F = Fp>>(
        &self,
        _dr: &mut D,
        _input: &Bound<'dr, D, Self::Input>,
    ) -> Result<Prediction<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'dr>>>> {
        Ok(Prediction::Unknown(D::just(|| Fp::from(10u64))))
    }
}

#[test]
fn test_element() {
    let mut simulator = Simulator::<Fp>::new();
    let allocator = &mut Standard::new();
    let input = Element::alloc(
        &mut simulator,
        allocator,
        Always::<Fp>::just(|| Fp::from(5u64)),
    )
    .unwrap();
    let result = simulator.routine(TestRoutine, input).unwrap();
    assert_eq!(*result.value().take(), Fp::from(15u64));
}

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
/// corrupted wire values — is what a swallowed error actually produces.
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

/// `consistency_checks` passes for the malicious circuit: `sx`, `sy` and `sxy`
/// all ignore witness closures and see one self-consistent synthesis. The bogus
/// gate participates in no linear constraint, so it does not perturb $s(X, Y)$
/// at all — the divergence is confined to the gate count.
#[test]
fn test_error_swallowing_consistency_passes() {
    let circuit = into_wiring_object::<_, _, TestRank>(ErrorSwallowingCircuit).unwrap();
    consistency_checks(&*circuit);
}

/// Run [`SquareCircuit`] through `consistency_checks` for small and medium sizes.
#[test]
fn test_square_circuit_consistency() {
    for times in [1, 5] {
        let circuit = into_wiring_object::<_, _, TestRank>(SquareCircuit { times }).unwrap();
        consistency_checks(&*circuit);
    }
}

/// `SquareCircuit { times: 30 }` with `TestRank` (`R<7>`, `n = 32`).
/// Total gates: 1 (SYSTEM) + 1 (allocation) + 30 (squares) = 32 = `n()`.
#[test]
fn test_gate_bound_exact() {
    let result = into_wiring_object::<_, _, TestRank>(SquareCircuit { times: 30 });
    assert!(result.is_ok(), "32 gates should fit exactly in n() = 32");
}

/// `SquareCircuit { times: 31 }` needs 33 gates > `n()` = 32, so it must fail
/// with [`Error::GateBoundExceeded`].
#[test]
fn test_gate_bound_exceeded() {
    match into_wiring_object::<_, _, TestRank>(SquareCircuit { times: 31 }) {
        Err(Error::GateBoundExceeded { limit }) => {
            assert_eq!(limit, TestRank::n());
        }
        other => panic!(
            "expected GateBoundExceeded {{ limit: {} }}, got {:?}",
            TestRank::n(),
            other.map(|_| "(ok)")
        ),
    }
}

/// Circuit with enough `enforce_zero` calls to exceed the constraint bound.
///
/// With `TestRank` (`R<7>`): `num_coeffs` = 128, of which `into_wiring_object`
/// reserves the last slot ($Y^{4n-1}$) for the registry key constraint, leaving
/// 127 usable. Overhead is 2 constraints (1 output + 1 ONE), so 126
/// `enforce_zero` calls give 128 > 127.
#[test]
fn test_constraint_bound_exceeded() {
    struct ManyLinearCircuit;

    impl Circuit<Fp> for ManyLinearCircuit {
        type Instance<'instance> = Fp;
        type Output = Kind![Fp; Element<'_, _>];
        type Witness<'witness> = Fp;
        type Aux<'witness> = ();

        fn instance<'dr, 'instance: 'dr, D: Driver<'dr, F = Fp>>(
            &self,
            dr: &mut D,
            instance: DriverValue<D, Self::Instance<'instance>>,
        ) -> Result<Bound<'dr, D, Self::Output>> {
            let allocator = &mut Standard::new();
            Element::alloc(dr, allocator, instance)
        }

        fn witness<'dr, 'witness: 'dr, D: Driver<'dr, F = Fp>>(
            &self,
            dr: &mut D,
            witness: DriverValue<D, Self::Witness<'witness>>,
        ) -> Result<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'witness>>>>
        {
            let allocator = &mut Standard::new();
            let a = Element::alloc(dr, allocator, witness)?;
            for _ in 0..126 {
                dr.enforce_zero(|lc| lc.add(a.wire()))?;
            }
            Ok(WithAux::new(a, D::unit()))
        }
    }

    let limit = TestRank::num_coeffs() - 1;
    match into_wiring_object::<_, _, TestRank>(ManyLinearCircuit) {
        Err(Error::ConstraintBoundExceeded { limit: reported }) => {
            assert_eq!(reported, limit);
        }
        other => panic!(
            "expected ConstraintBoundExceeded {{ limit: {limit} }}, got {:?}",
            other.map(|_| "(ok)")
        ),
    }
}

/// A routine compatible with all drivers (including `Empty`-typed ones).
/// Allocates two elements and returns their sum with the input, without
/// calling `.take()` on aux.
#[derive(Clone)]
struct SimpleRoutine;

impl Routine<Fp> for SimpleRoutine {
    type Input = Kind![Fp; Element<'_, _>];
    type Output = Kind![Fp; Element<'_, _>];
    type Aux<'dr> = ();

    fn execute<'dr, D: Driver<'dr, F = Fp>>(
        &self,
        dr: &mut D,
        input: Bound<'dr, D, Self::Input>,
        _aux: DriverValue<D, Self::Aux<'dr>>,
    ) -> Result<Bound<'dr, D, Self::Output>> {
        let allocator = &mut Standard::new();
        let elem1 = Element::alloc(dr, allocator, D::just(|| Fp::from(5u64)))?;
        let elem2 = Element::alloc(dr, allocator, D::just(|| Fp::from(7u64)))?;
        let sum = elem1.add(dr, &elem2);
        let result = input.add(dr, &sum);
        Ok(result)
    }

    fn predict<'dr, D: Driver<'dr, F = Fp>>(
        &self,
        _dr: &mut D,
        _input: &Bound<'dr, D, Self::Input>,
    ) -> Result<Prediction<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'dr>>>> {
        Ok(Prediction::Unknown(D::unit()))
    }
}

/// Circuit that calls `dr.routine(SimpleRoutine, input)` in its `witness`
/// method, exercising the per-routine scope save/restore logic in every
/// evaluator.
#[test]
fn test_routine_consistency() {
    struct RoutineCircuit;

    impl Circuit<Fp> for RoutineCircuit {
        type Instance<'instance> = Fp;
        type Output = Kind![Fp; Element<'_, _>];
        type Witness<'witness> = Fp;
        type Aux<'witness> = ();

        fn instance<'dr, 'instance: 'dr, D: Driver<'dr, F = Fp>>(
            &self,
            dr: &mut D,
            instance: DriverValue<D, Self::Instance<'instance>>,
        ) -> Result<Bound<'dr, D, Self::Output>> {
            let allocator = &mut Standard::new();
            Element::alloc(dr, allocator, instance)
        }

        fn witness<'dr, 'witness: 'dr, D: Driver<'dr, F = Fp>>(
            &self,
            dr: &mut D,
            witness: DriverValue<D, Self::Witness<'witness>>,
        ) -> Result<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'witness>>>>
        {
            let allocator = &mut Standard::new();
            let input = Element::alloc(dr, allocator, witness)?;
            let result = dr.routine(SimpleRoutine, input)?;
            Ok(WithAux::new(result, D::unit()))
        }
    }

    let circuit = into_wiring_object::<_, _, TestRank>(RoutineCircuit).unwrap();
    consistency_checks(&*circuit);
}
