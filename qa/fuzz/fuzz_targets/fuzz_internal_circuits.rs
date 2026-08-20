//! The patcher's soundness oracle aimed at the **production internal
//! recursion circuits** (issue #793).
//!
//! Every other patcher target hunts under-constrained advice in *generated*
//! substrate programs. This one hunts it in the circuits that actually carry
//! ragu's recursion — the native `hashes_1`, `hashes_2`, `inner_collapse`,
//! `outer_collapse` and `compute_v`, and the nested endoscaling steps — by
//! capturing them from real fuses and then playing a malicious prover
//! against the constraints they emitted.
//!
//! # Setup, paid once
//!
//! The circuits' honest witnesses exist only mid-fuse, so
//! [`Application::capture_internal_circuits`] runs real fuses and hands each
//! circuit, its [`CircuitSpec`] and its witness to a visitor that records the
//! constraint graph ([`ragu_testing::patcher::capture_staged`]). It does so at
//! three points of a small tree — the base case (a seed over two trivial
//! children), a fuse of two leaves, and a fuse of two such nodes — because
//! the first two are degenerate in their own ways (`outer_collapse` leaves
//! `c` free at the base case; a trivial child accumulator makes every error
//! term zero) and the third is not. That costs some seconds and happens
//! once, in libFuzzer's `init`; every fuzz iteration afterwards works on the
//! captured graphs through a [`Prepared`] probe, which solved the part of
//! each witness the inputs force once and only re-solves what a cheat can
//! still change.
//!
//! # The oracle
//!
//! A circuit's spec declares what it is responsible for: the unified instance
//! slots it covers and the stage values it checks (see
//! [`ragu_pcd::patcher`]). Those are its **outputs**; every other instance
//! wire and every other reserved stage wire is an **input** — received
//! commitments, challenges another circuit derived, stage values another
//! circuit checks. Before any fuzzing, a static check runs
//! [`forced_by`](ragu_testing::patcher::forced_by) twice: granting the inputs
//! and every other free wire except the outputs, it must derive every output
//! — one it cannot reach is an output the circuit never constrains, a finding
//! in itself, and the harness refuses to start; and it reports how many
//! outputs the inputs *alone* force.
//!
//! Then: pin the inputs, let the prover rewrite any other free advice —
//! Poseidon hints, allocator slack, the outputs themselves — and repair the
//! rest of the witness through the captured constraints. If every constraint
//! still holds while an **output** moved, the circuit accepts two witnesses
//! that agree on everything it received and disagree on something it is
//! responsible for. For the hash circuits that is a Fiat–Shamir binding
//! break; for the collapse circuits, a folded claim the prover can choose;
//! for an endoscaling step, an accumulator the prover can steer. Either way
//! it is a soundness bug, and the accepting witness is the evidence.
//!
//! A repaired witness the constraints *reject* is inconclusive — the solver
//! is deliberately bounded — and is never a signal.

#![no_main]

use std::sync::LazyLock;

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use ragu_arithmetic::{
    Cycle,
    ff::{Field, PrimeField},
};
use ragu_circuits::{Circuit, polynomials::ProductionRank};
use ragu_core::Result;
// The fields must come from the cycle's own dependency graph: the fuzz
// crate's direct `pasta_curves` is a distinct instance and would not unify
// with `<Pasta as Cycle>::CircuitField`.
use ragu_pasta::Pasta;
use ragu_pcd::{
    ApplicationBuilder,
    patcher::{CircuitSpec, InternalCircuitVisitor},
};
use ragu_testing::{
    patcher::{Prepared, ProbeOutcome, capture_with_stage_values, discover_free_advice, forced_by},
    pcd::nontrivial::{Hash2, Merge2, WitnessLeaf},
};
use rand::{SeedableRng, rngs::StdRng};

type NativeField = <Pasta as Cycle>::CircuitField;
type NestedField = <Pasta as Cycle>::ScalarField;

/// One captured internal circuit, ready to probe.
struct Captured<F> {
    name: String,
    /// The capture with the input-forced part of its witness solved once.
    prepared: Prepared<F>,
    /// Free advice outside the inputs — the wires a cheat may rewrite.
    cheatable: Vec<usize>,
}

/// Captures one circuit, checks its spec statically, and classifies its
/// wires.
fn collect<'w, F: Field, Cir: Circuit<F>>(
    point: &str,
    spec: &CircuitSpec,
    circuit: &Cir,
    stage_values: &[F],
    make_witness: impl Fn() -> Result<Cir::Witness<'w>>,
) -> Result<Captured<F>> {
    let name = format!("{}@{point}", spec.name);
    let cap = capture_with_stage_values(circuit, make_witness()?, stage_values)?;
    assert_eq!(
        cap.stage_wires.len(),
        2 * spec.reserved_gates,
        "{name}: two stage wires per reserved gate",
    );
    let resolution = spec.resolve(&cap.instance, &cap.stage_wires)?;
    assert!(
        !resolution.outputs.is_empty(),
        "{name}: nothing to watch — the oracle would be vacuous here",
    );

    // The static half: granting the inputs and every other free wire except
    // the outputs, the solver must force every output — else the circuit
    // never constrains it and no cheat can tell us anything about it.
    // Whether the inputs *alone* force it is reported.
    let free = discover_free_advice(&cap.recorder.events, &cap.recorder.values);
    let cheatable: Vec<usize> = free
        .iter()
        .copied()
        .filter(|w| !resolution.inputs.contains(w))
        .collect();
    let mut granted = resolution.inputs.clone();
    granted.extend(
        free.iter()
            .copied()
            .filter(|w| !resolution.outputs.contains(w)),
    );
    let weakly = forced_by(&cap.recorder.events, &cap.recorder.values, &granted);
    let unforced: Vec<usize> = resolution
        .outputs
        .iter()
        .copied()
        .filter(|w| weakly.binary_search(w).is_err())
        .collect();
    assert!(
        unforced.is_empty(),
        "{name}: declared outputs {unforced:?} are not forced even with every hint \
         granted — the circuit never constrains them; fix before fuzzing",
    );
    let strongly = forced_by(
        &cap.recorder.events,
        &cap.recorder.values,
        &resolution.inputs,
    );
    let strongly_forced = resolution
        .outputs
        .iter()
        .filter(|w| strongly.binary_search(w).is_ok())
        .count();

    let prepared = Prepared::new(
        cap.recorder.events,
        cap.recorder.values,
        resolution.inputs,
        resolution.outputs,
    );
    let (residual, total) = prepared.residual_events();
    eprintln!(
        "{name}: {} wires, {} inputs pinned, {} outputs watched ({strongly_forced} forced by \
         the inputs alone), {} cheatable, {residual} of {total} events solved per probe",
        prepared.honest().len(),
        prepared.inputs().len(),
        prepared.outputs().len(),
        cheatable.len(),
    );

    Ok(Captured {
        name,
        prepared,
        cheatable,
    })
}

/// The captured circuits of every visited point, by field.
#[derive(Default)]
struct Collector {
    point: &'static str,
    native: Vec<Captured<NativeField>>,
    nested: Vec<Captured<NestedField>>,
}

impl InternalCircuitVisitor<Pasta> for Collector {
    fn visit<'w, Cir: Circuit<<Pasta as Cycle>::CircuitField>>(
        &mut self,
        spec: &CircuitSpec,
        circuit: &Cir,
        stage_values: &[<Pasta as Cycle>::CircuitField],
        make_witness: impl Fn() -> Result<Cir::Witness<'w>>,
    ) -> Result<()> {
        let captured = collect(self.point, spec, circuit, stage_values, make_witness)?;
        self.native.push(captured);
        Ok(())
    }

    fn visit_nested<'w, Cir: Circuit<<Pasta as Cycle>::ScalarField>>(
        &mut self,
        spec: &CircuitSpec,
        circuit: &Cir,
        stage_values: &[<Pasta as Cycle>::ScalarField],
        make_witness: impl Fn() -> Result<Cir::Witness<'w>>,
    ) -> Result<()> {
        let captured = collect(self.point, spec, circuit, stage_values, make_witness)?;
        self.nested.push(captured);
        Ok(())
    }
}

/// The captured circuits, built from real fuses on first use.
static CIRCUITS: LazyLock<Collector> = LazyLock::new(|| {
    let pasta = Pasta::baked();
    let leaf_step = || WitnessLeaf {
        poseidon_params: Pasta::circuit_poseidon(pasta),
    };
    let hash2 = || Hash2 {
        poseidon_params: Pasta::circuit_poseidon(pasta),
    };
    let merge2 = || Merge2 {
        poseidon_params: Pasta::circuit_poseidon(pasta),
    };
    let app = ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(leaf_step())
        .and_then(|b| b.register(hash2()))
        .and_then(|b| b.register(merge2()))
        .and_then(|b| b.finalize(pasta))
        .expect("application must build");

    let mut rng = StdRng::seed_from_u64(1234);
    let leaf = |rng: &mut StdRng| {
        app.seed(rng, leaf_step(), NativeField::from(42u64))
            .expect("seed must succeed")
            .0
    };
    let node = |rng: &mut StdRng| {
        let (l, r) = (leaf(rng), leaf(rng));
        app.fuse(rng, hash2(), (), l, r)
            .expect("fuse must succeed")
            .0
    };

    let mut collector = Collector {
        point: "seeded",
        ..Default::default()
    };
    app.capture_internal_circuits_seeded(
        &mut rng,
        leaf_step(),
        NativeField::from(42u64),
        &mut collector,
    )
    .expect("capturing the internal circuits at the base case must succeed");

    collector.point = "leaves";
    let (l, r) = (leaf(&mut rng), leaf(&mut rng));
    app.capture_internal_circuits(&mut rng, hash2(), (), l, r, &mut collector)
        .expect("capturing the internal circuits over two leaves must succeed");

    collector.point = "nodes";
    let (l, r) = (node(&mut rng), node(&mut rng));
    app.capture_internal_circuits(&mut rng, merge2(), (), l, r, &mut collector)
        .expect("capturing the internal circuits over two nodes must succeed");
    collector
});

/// How a cheat rewrites its target wire, mirroring the corner cases
/// `fuzz_advice_patcher` found productive.
#[derive(Arbitrary, Debug, Clone, Copy)]
enum Mutation {
    /// `v + δ` for a small delta.
    AddSmall(u64),
    /// `v · m`.
    MulSmall(u64),
    /// `−v`.
    Negate,
    /// Zero — the corner case gadget hints most often mishandle.
    Zero,
    /// Copy another cheatable wire's honest value: the probe for a missing
    /// copy constraint.
    CopyFrom(u16),
}

#[derive(Arbitrary, Debug)]
struct Input {
    /// Which captured circuit to probe (modulo the count, native first).
    circuit: u8,
    /// Coordinated cheats: `(wire index mod cheatable count, mutation)`.
    cheats: Vec<(u16, Mutation)>,
}

// The captures are paid for in `init`, before libFuzzer starts timing units,
// so the first input is not reported as a slow unit and written to
// `artifacts/`.
fuzz_target!(
    init: {
        if std::env::var("DEBUG_INPUT").is_err() {
            LazyLock::force(&CIRCUITS);
        }
    },
    |input: Input| {
        if std::env::var("DEBUG_INPUT").is_ok() {
            eprintln!("{input:#?}");
            return;
        }
        let circuits: &Collector = &CIRCUITS;
        let total = circuits.native.len() + circuits.nested.len();
        if total == 0 {
            return;
        }
        let index = input.circuit as usize % total;
        if index < circuits.native.len() {
            probe(&circuits.native[index], &input);
        } else {
            probe(&circuits.nested[index - circuits.native.len()], &input);
        }
    }
);

/// One fuzz iteration: resolve the cheats onto the captured circuit and
/// probe.
fn probe<F: PrimeField>(circuit: &Captured<F>, input: &Input) {
    if circuit.cheatable.is_empty() {
        return;
    }
    let honest = circuit.prepared.honest();

    // Resolve the cheats onto distinct wires, each nudged off its honest
    // value so every cheat does real work.
    let mut cheats: Vec<(usize, F)> = Vec::new();
    for (raw, mutation) in input.cheats.iter().take(8) {
        let wire = circuit.cheatable[*raw as usize % circuit.cheatable.len()];
        if cheats.iter().any(|(w, _)| *w == wire) {
            continue;
        }
        let mut value = match mutation {
            Mutation::AddSmall(d) => honest[wire] + F::from(*d),
            Mutation::MulSmall(m) => honest[wire] * F::from(*m),
            Mutation::Negate => -honest[wire],
            Mutation::Zero => F::ZERO,
            Mutation::CopyFrom(o) => {
                honest[circuit.cheatable[*o as usize % circuit.cheatable.len()]]
            }
        };
        if value == honest[wire] {
            value += F::ONE;
        }
        cheats.push((wire, value));
    }
    if cheats.is_empty() {
        // Default to one small cheat so every input does work.
        cheats.push((circuit.cheatable[0], honest[circuit.cheatable[0]] + F::ONE));
    }

    if let ProbeOutcome::OutputsMoved { moved, .. } = circuit.prepared.probe(&cheats) {
        panic!(
            "INTERNAL CIRCUIT SOUNDNESS SIGNAL in `{}`: cheating advice {cheats:?} and \
             repairing through the captured constraints left every constraint \
             satisfied, yet the wires {moved:?} this circuit is responsible for moved \
             while every input it receives — instance and stage alike — was held at its \
             honest value. The circuit accepts two witnesses that agree on everything it \
             takes in and disagree on something it vouches for.",
            circuit.name,
        );
    }
}
