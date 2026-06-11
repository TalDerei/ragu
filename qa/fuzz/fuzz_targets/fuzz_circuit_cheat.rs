//! The "patcher" technique (issue #728): mutate one witness input, repair
//! every downstream wire, and demand the constraint system's verdict match
//! an independent oracle.
//!
//! # What the patcher adds over the existing soundness targets
//!
//! `fuzz_witness_cheat` perturbs a value mid-synthesis, but every
//! downstream gadget recomputes honestly from it, so computational gates
//! self-satisfy and the constraint matrix is never consulted — it is a
//! Simulator-robustness fuzzer, not a soundness oracle (see its header).
//! `fuzz_witness_pinning` mutates one coefficient of the *assembled trace
//! polynomial* and checks the revdot identity; it is the algebraic,
//! single-wire pinning oracle.
//!
//! This target is the *operational* patcher the zksecurity paper
//! describes, adapted to Ragu: begin from a valid witness, mutate one
//! input, then "patch" — let the cheat propagate through every derived
//! wire by recomputing them — so the cheat reaches `enforce_zero`
//! constraints deep in the circuit instead of being a local fingerprint
//! diff. The bug it hunts is the assignment-vs-constraint gap: a witness
//! the circuit *should* reject but accepts.
//!
//! # The substrate and the oracle
//!
//! A fuzzer-chosen program runs over a stack of field elements with real
//! Ragu gadgets in two ways: first through the `Simulator` as a fast
//! synthesis sanity check, then as a temporary `Circuit` whose trace is
//! assembled and checked with the revdot constraint identity. Alongside it
//! the harness keeps a *native* `Fp` shadow of the same stack — this shadow
//! is simultaneously the constraint graph (it records every wire's value)
//! and the oracle (it defines the true semantics independently of Ragu).
//!
//! `Op::Anchor(i)` is the constraint primitive: at honest-build time it
//! captures the native value `v` at stack slot `i`, and in the Ragu
//! program it emits `enforce_zero(elem[i] - v)` — pinning that wire to its
//! honest value. Anchors are satisfiable by construction (honest
//! `elem[i] == v`), so the honest witness always verifies. Arithmetic ops
//! (`Add`/`Sub`/`Mul`/`Double`/`Negate`/`Scale`) are the derived wires the
//! patcher's repair flows through; only `Anchor` can reject a witness.
//!
//! # The patcher step and the differential assertion
//!
//! 1. Honest: evaluate the native shadow from the input seeds; capture the
//!    anchor constants; confirm the Simulator accepts (completeness).
//! 2. Mutate one input by a nonzero delta.
//! 3. Repair: recompute the entire native shadow from the mutated inputs
//!    (the Simulator independently does the same when re-run). Anchors
//!    still reference the *honest* constants, so any anchor downstream of
//!    the cheat now reads a changed value.
//! 4. Compute the native verdict — do all anchors still hold under the
//!    repaired shadow? — and assemble the mutated trace under the same
//!    circuit wiring.
//! 5. Assert the revdot identity verdict matches `native_satisfied`. The
//!    load-bearing direction is **constraint identity accepts while the
//!    oracle says violated**: Ragu accepted a witness that changed a
//!    pinned wire — an under-constrained `enforce_zero`/gadget, i.e. a
//!    soundness bug. The converse (identity rejects while the oracle is
//!    satisfied) is a completeness bug and is equally caught. The
//!    Simulator verdict is also compared to the identity to catch
//!    Simulator-vs-wiring disagreements.
//!
//! Inputs where the cheat reaches no anchor leave both verdicts
//! `satisfied` — correctly no signal, since an unconstrained input is free
//! to change.
//!
//! # Native/Ragu agreement
//!
//! The differential is only as trustworthy as the shadow's fidelity to the
//! gadgets, so the op set is restricted to the deterministic, infallible-
//! in-the-Simulator gadgets whose field semantics the shadow mirrors
//! exactly. `Mul`/`Square` are fallible in the gadget API but in the
//! Simulator only fail the gate check `a*b == c`, which the gadget's own
//! witness makes hold by construction — so they never spuriously reject,
//! and the shadow models them as plain field multiplication. The same
//! native-spec pattern backs `fuzz_circuit_witness`.

#![no_main]

use arbitrary::Arbitrary;
use ff::Field;
use ff::PrimeField;
use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_arithmetic::Coeff;
use ragu_circuits::{
    Circuit, CircuitExt, WithAux,
    polynomials::{Rank, TestRank, sparse},
    registry::{CircuitIndex, Registry, RegistryBuilder},
};
use ragu_core::{
    Result as RaguResult,
    drivers::{Driver, DriverValue},
    gadgets::{Bound, Kind},
    maybe::Maybe,
};
use ragu_primitives::{Element, Simulator, allocator::Standard};

/// Number of free witness inputs the program starts with. The stack only
/// grows from here, so it is never empty and index resolution never hits a
/// zero modulus.
const NUM_INPUTS: usize = 6;

fn special_value(idx: u8) -> Fp {
    match idx % 8 {
        0 => Fp::ZERO,
        1 => Fp::ONE,
        2 => -Fp::ONE,
        3 => Fp::TWO_INV,
        4 => Fp::ROOT_OF_UNITY,
        5 => Fp::MULTIPLICATIVE_GENERATOR,
        6 => Fp::from(1u64 << 32),
        _ => Fp::from(u64::MAX),
    }
}

/// Stack program. Arithmetic ops push one derived wire; `Anchor` pushes
/// nothing and emits a pinning constraint. Operand indices are taken mod
/// the current stack length, so every program is well-formed.
#[derive(Arbitrary, Debug, Clone, Copy)]
enum Op {
    Add(u8, u8),
    Sub(u8, u8),
    Mul(u8, u8),
    Double(u8),
    Negate(u8),
    Scale(u8, u64),
    /// Pin `stack[i]` to its honest value via `enforce_zero(elem - v)`.
    Anchor(u8),
}

#[derive(Arbitrary, Debug)]
struct Input {
    input_seeds: [u64; NUM_INPUTS],
    /// Optional corner-value override per input.
    input_special: [Option<u8>; NUM_INPUTS],
    ops: Vec<Op>,
    /// Which input to mutate (mod `NUM_INPUTS`).
    cheat_input: u8,
    /// Additive perturbation; 0 maps to 1 so the mutation is always real.
    cheat_delta: u64,
}

/// Build the initial free-witness inputs from the seeds.
fn build_inputs(input: &Input) -> [Fp; NUM_INPUTS] {
    let mut out = [Fp::ZERO; NUM_INPUTS];
    for i in 0..NUM_INPUTS {
        out[i] = match input.input_special[i] {
            Some(idx) => special_value(idx),
            None => Fp::from(input.input_seeds[i]),
        };
    }
    out
}

/// Evaluate the native shadow stack and collect, in encounter order, the
/// honest value pinned by each `Anchor`. The shadow doubles as the
/// constraint graph (every wire's value) and the oracle.
///
/// Stack length progression is value-independent (arithmetic pushes one,
/// `Anchor` pushes none), so anchor slot resolution is identical for the
/// honest and mutated inputs.
fn native_anchor_values(ops: &[Op], inputs: &[Fp; NUM_INPUTS]) -> Vec<Fp> {
    let mut stack: Vec<Fp> = inputs.to_vec();
    let mut anchors = Vec::new();
    for op in ops {
        let len = stack.len();
        match *op {
            Op::Add(a, b) => stack.push(stack[a as usize % len] + stack[b as usize % len]),
            Op::Sub(a, b) => stack.push(stack[a as usize % len] - stack[b as usize % len]),
            Op::Mul(a, b) => stack.push(stack[a as usize % len] * stack[b as usize % len]),
            Op::Double(a) => stack.push(stack[a as usize % len].double()),
            Op::Negate(a) => stack.push(-stack[a as usize % len]),
            Op::Scale(a, c) => stack.push(stack[a as usize % len] * Fp::from(c)),
            Op::Anchor(a) => anchors.push(stack[a as usize % len]),
        }
    }
    anchors
}

/// Native oracle verdict: do all anchors still hold when the shadow is
/// recomputed from `inputs`, with each anchor compared against the honest
/// constant in `honest_anchors`?
fn native_satisfied(ops: &[Op], inputs: &[Fp; NUM_INPUTS], honest_anchors: &[Fp]) -> bool {
    let anchors = native_anchor_values(ops, inputs);
    anchors.as_slice() == honest_anchors
}

fn synthesize_stack<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    witness: DriverValue<D, [Fp; NUM_INPUTS]>,
    ops: &[Op],
    honest_anchors: &[Fp],
) -> RaguResult<()> {
    let allocator = &mut Standard::new();
    let mut elems: Vec<Element<'dr, D>> = (0..NUM_INPUTS)
        .map(|i| Element::alloc(dr, allocator, witness.as_ref().map(|wv| wv[i])))
        .collect::<RaguResult<_>>()?;
    let mut anchor_idx = 0usize;
    for op in ops {
        let len = elems.len();
        match *op {
            Op::Add(a, b) => {
                let r = elems[a as usize % len].add(dr, &elems[b as usize % len]);
                elems.push(r);
            }
            Op::Sub(a, b) => {
                let r = elems[a as usize % len].sub(dr, &elems[b as usize % len]);
                elems.push(r);
            }
            Op::Mul(a, b) => {
                let r = elems[a as usize % len].mul(dr, &elems[b as usize % len])?;
                elems.push(r);
            }
            Op::Double(a) => {
                let r = elems[a as usize % len].double(dr);
                elems.push(r);
            }
            Op::Negate(a) => {
                let r = elems[a as usize % len].negate(dr);
                elems.push(r);
            }
            Op::Scale(a, c) => {
                let r = elems[a as usize % len].scale(dr, Coeff::Arbitrary(Fp::from(c)));
                elems.push(r);
            }
            Op::Anchor(a) => {
                let slot = a as usize % len;
                let pin = Element::constant(dr, honest_anchors[anchor_idx]);
                anchor_idx += 1;
                elems[slot].sub(dr, &pin).enforce_zero(dr)?;
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct StackCircuit<'a> {
    ops: &'a [Op],
    honest_anchors: &'a [Fp],
}

impl<'a> Circuit<Fp> for StackCircuit<'a> {
    type Instance<'instance> = ();
    type Output = Kind![Fp; ()];
    type Witness<'witness> = [Fp; NUM_INPUTS];
    type Aux<'witness> = ();

    fn instance<'dr, 'instance: 'dr, D: Driver<'dr, F = Fp>>(
        &self,
        _dr: &mut D,
        _instance: DriverValue<D, Self::Instance<'instance>>,
    ) -> RaguResult<Bound<'dr, D, Self::Output>>
    where
        Self: 'dr,
    {
        Ok(())
    }

    fn witness<'dr, 'witness: 'dr, D: Driver<'dr, F = Fp>>(
        &self,
        dr: &mut D,
        witness: DriverValue<D, Self::Witness<'witness>>,
    ) -> RaguResult<WithAux<Bound<'dr, D, Self::Output>, DriverValue<D, Self::Aux<'witness>>>>
    where
        Self: 'dr,
    {
        synthesize_stack(dr, witness, self.ops, self.honest_anchors)?;
        Ok(WithAux::new((), D::unit()))
    }
}

/// Replay the program through the Ragu `Simulator` with the given inputs,
/// emitting each `Anchor` as `enforce_zero(elem - honest_const)`. Returns
/// whether the Simulator accepted (all gates and constraints held).
fn simulator_accepts(ops: &[Op], inputs: &[Fp; NUM_INPUTS], honest_anchors: &[Fp]) -> bool {
    let sim = Simulator::<Fp>::simulate(*inputs, |dr, w| {
        synthesize_stack(dr, w, ops, honest_anchors)
    });
    sim.is_ok()
}

fn sy_from_registry(
    registry: &Registry<'_, Fp, TestRank>,
    y: Fp,
) -> sparse::Polynomial<Fp, TestRank> {
    let omega_0 = CircuitIndex::new(0).omega_j::<Fp>();
    let mut wy = registry.wy(omega_0, y);
    if y != Fp::ZERO {
        let y_4n_minus_1 = y.pow_vartime([(4 * TestRank::n() - 1) as u64]);
        let mut key_view = sparse::View::<_, TestRank, _>::wiring();
        key_view.c.push(registry.digest() * y_4n_minus_1);
        let key_term = key_view.build();
        wy.sub_assign(&key_term);
    }
    wy
}

fn identity_lhs(
    registry: &Registry<'_, Fp, TestRank>,
    r: &sparse::Polynomial<Fp, TestRank>,
    y: Fp,
    z: Fp,
) -> Fp {
    let mut b = r.clone();
    b.dilate(z);
    b.add_assign(&sy_from_registry(registry, y));
    b.add_assign(&TestRank::tz(z));
    r.revdot(&b)
}

fn evaluation_point(seed: u64, offset: u64) -> Fp {
    let mut point = Fp::from(seed) + Fp::from(offset);
    if point == Fp::ZERO || point == Fp::ONE {
        point += Fp::from(2u64);
    }
    point
}

fn identity_accepts(
    ops: &[Op],
    inputs: &[Fp; NUM_INPUTS],
    honest_anchors: &[Fp],
    input: &Input,
) -> Option<bool> {
    let circuit = StackCircuit {
        ops,
        honest_anchors,
    };
    let registry = RegistryBuilder::<Fp, TestRank>::new()
        .register_circuit(circuit)
        .and_then(|b| b.finalize())
        .ok()?;
    let trace = circuit.trace(*inputs).ok()?.into_output();
    let r = registry
        .assemble_with_alpha(&trace, CircuitIndex::new(0), Fp::ZERO)
        .ok()?;

    let y = evaluation_point(input.input_seeds[0], 2);
    let z = evaluation_point(input.input_seeds[1], 3);
    let y2 = y * Fp::MULTIPLICATIVE_GENERATOR + Fp::from(5u64);
    let z2 = z * Fp::MULTIPLICATIVE_GENERATOR + Fp::from(7u64);

    Some(
        identity_lhs(&registry, &r, y, z) == circuit.ky((), y).ok()?
            && identity_lhs(&registry, &r, y2, z2) == circuit.ky((), y2).ok()?,
    )
}

fuzz_target!(|input: Input| {
    if std::env::var("DEBUG_INPUT").is_ok() {
        eprintln!("{:#?}", input);
        return;
    }

    // Bound program length for throughput.
    if input.ops.is_empty() || input.ops.len() > 64 {
        return;
    }

    let honest_inputs = build_inputs(&input);
    let honest_anchors = native_anchor_values(&input.ops, &honest_inputs);

    // Completeness sanity: the honest witness must verify, and the native
    // oracle must agree. Both hold by construction; a failure here is a
    // bug in Ragu (or the harness) worth surfacing immediately.
    assert!(
        native_satisfied(&input.ops, &honest_inputs, &honest_anchors),
        "honest native oracle disagreed with itself (harness bug): {input:?}"
    );
    assert!(
        simulator_accepts(&input.ops, &honest_inputs, &honest_anchors),
        "Simulator rejected the honest witness — completeness bug. {input:?}"
    );
    let honest_identity =
        match identity_accepts(&input.ops, &honest_inputs, &honest_anchors, &input) {
            Some(v) => v,
            None => return,
        };
    assert!(
        honest_identity,
        "constraint identity rejected the honest witness — completeness bug. {input:?}"
    );

    // Patch: mutate one input, repair downstream (both the native shadow
    // and the Simulator recompute every derived wire from the new input).
    let mut mutated_inputs = honest_inputs;
    let mut delta = Fp::from(input.cheat_delta);
    if delta == Fp::ZERO {
        delta = Fp::ONE;
    }
    mutated_inputs[input.cheat_input as usize % NUM_INPUTS] += delta;

    let oracle = native_satisfied(&input.ops, &mutated_inputs, &honest_anchors);
    let simulator = simulator_accepts(&input.ops, &mutated_inputs, &honest_anchors);
    let identity = match identity_accepts(&input.ops, &mutated_inputs, &honest_anchors, &input) {
        Some(v) => v,
        None => return,
    };

    assert_eq!(
        simulator,
        identity,
        "Simulator and assembled constraint identity disagree after mutating input \
         {} by {delta:?}. Simulator {}, identity {}. Input: {input:?}",
        input.cheat_input as usize % NUM_INPUTS,
        if simulator { "ACCEPTED" } else { "REJECTED" },
        if identity { "ACCEPTED" } else { "REJECTED" },
    );

    assert_eq!(
        identity,
        oracle,
        "PATCHER SOUNDNESS SIGNAL: after mutating input \
         {} by {delta:?} and repairing downstream, the constraint identity {} the \
         witness but the oracle says it is {}. {}. Input: {input:?}",
        input.cheat_input as usize % NUM_INPUTS,
        if identity { "ACCEPTED" } else { "REJECTED" },
        if oracle { "satisfied" } else { "VIOLATED" },
        if identity && !oracle {
            "Ragu accepted a witness that changed a pinned wire — an \
             under-constrained constraint/gadget (the soundness direction)"
        } else {
            "Ragu rejected a witness the oracle accepts — a completeness gap"
        },
    );
});
