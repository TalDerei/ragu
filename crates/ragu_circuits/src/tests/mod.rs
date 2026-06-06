#![allow(non_snake_case)]

mod identity;
mod segment_order;

use ragu_arithmetic::ff::Field;
use ragu_core::{
    Result,
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
#[derive(Clone)]
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

    let sxy_eval = obj.sxy(x, y, &plan).unwrap();
    let s0y_eval = obj.sxy(Fp::ZERO, y, &plan).unwrap();
    let sx0_eval = obj.sxy(x, Fp::ZERO, &plan).unwrap();
    let s00_eval = obj.sxy(Fp::ZERO, Fp::ZERO, &plan).unwrap();

    let sxY_poly = obj.sx(x, &plan).unwrap();
    let sXy_poly = obj.sy(y, &plan).unwrap();
    let s0Y_poly = obj.sx(Fp::ZERO, &plan).unwrap();
    let sX0_poly = obj.sy(Fp::ZERO, &plan).unwrap();

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
fn sxy_rejects_malformed_root_offset() {
    let circuit = SquareCircuit { times: 1 };
    let obj = into_wiring_object::<_, _, TestRank>(circuit.clone()).unwrap();
    let mut plan = floor_planner::floor_plan(obj.segment_records());
    plan[0].constraint_start = 1;

    let result = crate::wiring::sxy::eval::<_, _, TestRank>(
        &crate::raw::CircuitAdapterRef(&circuit),
        Fp::from(3u64),
        Fp::from(5u64),
        &plan,
    );

    assert!(matches!(
        result,
        Err(ragu_core::Error::MalformedFloorPlan { .. })
    ));
}

#[test]
fn sxy_rejects_count_mismatch_that_passes_validate() {
    // A floor plan can pass `validate`'s structural checks (prefix-sum offsets,
    // root at the origin) yet still claim different segment sizes than the
    // circuit synthesizes — a case only the in-`eval` count checks catch. We
    // inflate a root-only plan's constraint count, which still passes
    // `validate`, and confirm `eval` rejects it via the root count check.
    let obj = into_wiring_object::<_, _, TestRank>(SquareCircuit { times: 1 }).unwrap();
    let mut plan = floor_planner::floor_plan(obj.segment_records());

    assert_eq!(
        plan.len(),
        1,
        "SquareCircuit must produce a single root segment"
    );
    plan[0].num_constraints += 1;
    floor_planner::validate(&plan).expect("inflated single-segment plan still passes validate");

    let result = obj.sxy(Fp::from(3u64), Fp::from(5u64), &plan);

    assert!(matches!(
        result,
        Err(ragu_core::Error::MalformedFloorPlan { .. })
    ));
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
    b.add_assign(&obj.sy(y, &plan).unwrap());
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
fn sxy_rejects_too_short_floor_plan() {
    #[derive(Clone)]
    struct PassthroughRoutine;

    impl Routine<Fp> for PassthroughRoutine {
        type Input = Kind![Fp; Element<'_, _>];
        type Output = Kind![Fp; Element<'_, _>];
        type Aux<'dr> = ();

        fn execute<'dr, D: Driver<'dr, F = Fp>>(
            &self,
            _dr: &mut D,
            input: Bound<'dr, D, Self::Input>,
            _aux: DriverValue<D, Self::Aux<'dr>>,
        ) -> Result<Bound<'dr, D, Self::Output>> {
            Ok(input)
        }

        fn predict<'dr, D: Driver<'dr, F = Fp>>(
            &self,
            _dr: &mut D,
            _input: &Bound<'dr, D, Self::Input>,
        ) -> Result<Prediction<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'dr>>>>
        {
            Ok(Prediction::Unknown(D::unit()))
        }
    }

    struct OneRoutineCircuit;

    impl Circuit<Fp> for OneRoutineCircuit {
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
            let output = dr.routine(PassthroughRoutine, input)?;
            Ok(WithAux::new(output, D::unit()))
        }
    }

    let obj = into_wiring_object::<_, _, TestRank>(OneRoutineCircuit).unwrap();
    let mut plan = floor_planner::floor_plan(obj.segment_records());
    assert!(
        plan.len() > 1,
        "test circuit must produce at least one routine segment"
    );
    plan.truncate(1);

    let result = obj.sxy(Fp::from(3u64), Fp::from(5u64), &plan);

    assert!(matches!(
        result,
        Err(ragu_core::Error::MalformedFloorPlan { .. })
    ));
}

/// `sy(0)` returns the plan-independent closed form `s(X, 0) = d[0] = 1` via a
/// fast path that skips the per-segment checks `sx`/`sxy` run, so it accepts a
/// count-mismatched plan they reject yet yields the same correct result.
#[test]
fn sy_at_zero_is_plan_independent() {
    let obj = into_wiring_object::<_, _, TestRank>(SquareCircuit { times: 1 }).unwrap();
    let mut plan = floor_planner::floor_plan(obj.segment_records());
    assert_eq!(
        plan.len(),
        1,
        "SquareCircuit must produce a single root segment"
    );

    plan[0].num_constraints += 1;
    floor_planner::validate(&plan).expect("inflated single-segment plan still passes validate");

    assert!(matches!(
        obj.sxy(Fp::ZERO, Fp::ZERO, &plan),
        Err(ragu_core::Error::MalformedFloorPlan { .. })
    ));
    assert!(matches!(
        obj.sx(Fp::ZERO, &plan),
        Err(ragu_core::Error::MalformedFloorPlan { .. })
    ));

    let x = Fp::random(&mut ragu_arithmetic::rand::rng());
    let sX0 = obj.sy(Fp::ZERO, &plan).expect("sy(0) is plan-independent");
    let honest = floor_planner::floor_plan(obj.segment_records());
    assert_eq!(
        sX0.eval(x),
        obj.sy(Fp::ZERO, &honest).unwrap().eval(x),
        "sy(0) must equal the closed form regardless of the (count-mismatched) plan"
    );
}

/// `sy::eval` sizes the wiring-view allocation from the plan's gate total, so it
/// must reject `total_gates > R::n()` before the resize (mirroring
/// `Trace::assemble`); otherwise a `validate`-passing oversized plan drives an
/// unbounded allocation.
#[test]
fn sy_rejects_oversized_gate_plan() {
    use crate::polynomials::Rank;

    let circuit = SquareCircuit { times: 1 };
    let obj = into_wiring_object::<_, _, TestRank>(circuit.clone()).unwrap();
    let mut plan = floor_planner::floor_plan(obj.segment_records());
    assert_eq!(
        plan.len(),
        1,
        "SquareCircuit must produce a single root segment"
    );

    let oversized = TestRank::n() + 1000;
    plan[0].num_gates = oversized;
    floor_planner::validate(&plan).expect("oversized single-segment plan still passes validate");

    assert!(obj.sx(Fp::from(5u64), &plan).is_err());

    let sy_result = obj.sy(Fp::from(5u64), &plan);
    assert!(
        matches!(sy_result, Err(ragu_core::Error::GateBoundExceeded { .. })),
        "sy must reject total_gates > R::n() with a pre-allocation \
         GateBoundExceeded guard, but returned {:?}",
        sy_result.map(|_| "Ok(poly)")
    );
}

/// `sy::eval` must also reject floor plans whose claimed constraint total
/// occupies the registry-key slot, including before the `y == 0` fast path.
#[test]
fn sy_rejects_oversized_constraint_plan() {
    let obj = into_wiring_object::<_, _, TestRank>(SquareCircuit { times: 1 }).unwrap();
    let mut plan = floor_planner::floor_plan(obj.segment_records());
    assert_eq!(
        plan.len(),
        1,
        "SquareCircuit must produce a single root segment"
    );

    plan[0].num_constraints = TestRank::num_coeffs();
    floor_planner::validate(&plan)
        .expect("oversized single-segment constraint plan still passes validate");

    for y in [Fp::from(5u64), Fp::ZERO] {
        let sy_result = obj.sy(y, &plan);
        assert!(
            matches!(
                sy_result,
                Err(ragu_core::Error::ConstraintBoundExceeded { .. })
            ),
            "sy({y:?}) must reject total_constraints >= R::num_coeffs(), \
             but returned {:?}",
            sy_result.map(|_| "Ok(poly)")
        );
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
