//! The patcher's soundness oracle aimed at the **production internal
//! recursion circuits** (issue #793).
//!
//! Every other patcher target hunts under-constrained advice in *generated*
//! substrate programs. This one hunts it in the circuits that actually carry
//! ragu's recursion — `hashes_1`, `hashes_2`, `inner_collapse`,
//! `outer_collapse` and `compute_v` — by capturing them from a real fuse and
//! then playing a malicious prover against the constraints they emitted.
//!
//! # Setup, paid once
//!
//! The circuits' honest witnesses exist only mid-fuse, so
//! [`Application::capture_internal_circuits`] runs one real fuse and hands
//! each circuit and its witness to a visitor that records the constraint
//! graph ([`ragu_testing::patcher::capture`]). That costs a few seconds and
//! happens once, in a [`LazyLock`]; every fuzz iteration afterwards works on
//! the captured graphs, where a repair costs well under a millisecond.
//!
//! # The oracle
//!
//! A circuit's public instance is what the verifier sees in $k(Y)$. Splitting
//! those wires by whether the constraints determine them classifies them
//! without any per-circuit knowledge:
//!
//! * **received** — instance wires the capture reports as *free* advice: the
//!   commitments and challenges the circuit takes in;
//! * **computed** — instance wires that are *derived*: the values this
//!   circuit produces, such as the Fiat–Shamir challenges `hashes_1` squeezes
//!   from the transcript.
//!
//! Pin the received wires (plus the stage wires, which are committed and
//! bonded outside this circuit), let the prover rewrite any other free advice
//! — Poseidon hints, allocator slack, interstitial witness — and repair the
//! rest of the witness through the captured constraints. If every constraint
//! still holds while a **computed** instance wire moved, the circuit accepts
//! two witnesses that agree on everything it received and disagree on
//! something it produced. For the hash circuits that is exactly a
//! Fiat–Shamir binding break; for the others, an output the constraints fail
//! to pin. Either way it is a soundness bug, and the accepting witness is the
//! evidence.
//!
//! A repaired witness the constraints *reject* is inconclusive — the solver
//! is deliberately bounded — and is never a signal.

#![no_main]

use std::sync::LazyLock;

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use ragu_arithmetic::{Cycle, ff::Field};
use ragu_circuits::{Circuit, polynomials::ProductionRank};
use ragu_core::Result;
// `Fp` must come from the cycle's own dependency graph: the fuzz crate's
// direct `pasta_curves` is a distinct instance and would not unify with
// `<Pasta as Cycle>::CircuitField`.
use ragu_pasta::{Fp, Pasta};
use ragu_pcd::{ApplicationBuilder, patcher::InternalCircuitVisitor};
use ragu_testing::{
    patcher::{Event, ProbeOutcome, capture, determinism_probe, discover_free_advice},
    pcd::nontrivial::{Hash2, WitnessLeaf},
};
use rand::{SeedableRng, rngs::StdRng};

/// One captured internal circuit, ready to probe.
struct Captured<F> {
    name: &'static str,
    events: Vec<Event<F>>,
    honest: Vec<F>,
    /// Received instance wires plus stage wires: what the prover must hold.
    inputs: Vec<usize>,
    /// Computed instance wires: what must not move.
    outputs: Vec<usize>,
    /// Free advice outside `inputs` — the wires a cheat may rewrite.
    cheatable: Vec<usize>,
}

/// Captures each visited circuit and classifies its wires.
struct Collector<F>(Vec<Captured<F>>);

impl<F> Default for Collector<F> {
    fn default() -> Self {
        Collector(Vec::new())
    }
}

// The field is written as the cycle's own associated type so the method's
// bound matches the trait's verbatim; spelling it `Cycle<CircuitField = Fp>`
// instead makes rustc reject the impl as having stricter requirements.
impl<C: Cycle> InternalCircuitVisitor<C> for Collector<C::CircuitField> {
    fn visit<'w, Cir: Circuit<C::CircuitField>>(
        &mut self,
        name: &'static str,
        circuit: &Cir,
        make_witness: impl Fn() -> Result<Cir::Witness<'w>>,
    ) -> Result<()> {
        let cap = capture(circuit, make_witness()?)?;
        let free = discover_free_advice(&cap.recorder.events, &cap.recorder.values);

        let mut inputs: Vec<usize> = cap
            .instance
            .iter()
            .copied()
            .filter(|w| free.contains(w))
            .collect();
        inputs.extend(cap.stage_wires.iter().copied());
        let outputs: Vec<usize> = cap
            .instance
            .iter()
            .copied()
            .filter(|w| !free.contains(w))
            .collect();
        let cheatable: Vec<usize> = free
            .iter()
            .copied()
            .filter(|w| !inputs.contains(w))
            .collect();

        self.0.push(Captured {
            name,
            events: cap.recorder.events,
            honest: cap.recorder.values,
            inputs,
            outputs,
            cheatable,
        });
        Ok(())
    }
}

/// The captured circuits, built from one real fuse on first use.
static CIRCUITS: LazyLock<Vec<Captured<Fp>>> = LazyLock::new(|| {
    let pasta = Pasta::baked();
    let app = ApplicationBuilder::<Pasta, ProductionRank, 4>::new()
        .register(WitnessLeaf {
            poseidon_params: Pasta::circuit_poseidon(pasta),
        })
        .and_then(|b| {
            b.register(Hash2 {
                poseidon_params: Pasta::circuit_poseidon(pasta),
            })
        })
        .and_then(|b| b.finalize(pasta))
        .expect("application must build");

    let mut rng = StdRng::seed_from_u64(1234);
    let leaf = |rng: &mut StdRng| {
        app.seed(
            rng,
            WitnessLeaf {
                poseidon_params: Pasta::circuit_poseidon(pasta),
            },
            Fp::from(42u64),
        )
        .expect("seed must succeed")
        .0
    };
    let (left, right) = (leaf(&mut rng), leaf(&mut rng));

    let mut collector = Collector::default();
    app.capture_internal_circuits(
        &mut rng,
        Hash2 {
            poseidon_params: Pasta::circuit_poseidon(pasta),
        },
        (),
        left,
        right,
        &mut collector,
    )
    .expect("capturing the internal circuits must succeed");
    collector.0
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
    /// Which captured circuit to probe (modulo the count).
    circuit: u8,
    /// Coordinated cheats: `(wire index mod cheatable count, mutation)`.
    cheats: Vec<(u16, Mutation)>,
}

fuzz_target!(|input: Input| {
    let circuits: &[Captured<Fp>] = &CIRCUITS;
    if circuits.is_empty() {
        return;
    }
    let circuit = &circuits[input.circuit as usize % circuits.len()];
    if circuit.cheatable.is_empty() || circuit.outputs.is_empty() {
        return;
    }

    // Resolve the cheats onto distinct wires, each nudged off its honest
    // value so every cheat does real work.
    let mut cheats: Vec<(usize, Fp)> = Vec::new();
    for (raw, mutation) in input.cheats.iter().take(8) {
        let wire = circuit.cheatable[*raw as usize % circuit.cheatable.len()];
        if cheats.iter().any(|(w, _)| *w == wire) {
            continue;
        }
        let honest = circuit.honest[wire];
        let mut value = match mutation {
            Mutation::AddSmall(d) => honest + Fp::from(*d),
            Mutation::MulSmall(m) => honest * Fp::from(*m),
            Mutation::Negate => -honest,
            Mutation::Zero => Fp::ZERO,
            Mutation::CopyFrom(o) => {
                circuit.honest[circuit.cheatable[*o as usize % circuit.cheatable.len()]]
            }
        };
        if value == honest {
            value += Fp::ONE;
        }
        cheats.push((wire, value));
    }
    if cheats.is_empty() {
        // Default to one small cheat so every input does work.
        cheats.push((
            circuit.cheatable[0],
            circuit.honest[circuit.cheatable[0]] + Fp::ONE,
        ));
    }

    let outcome = determinism_probe(
        &circuit.events,
        &circuit.honest,
        &circuit.inputs,
        &circuit.outputs,
        &cheats,
    );

    if let ProbeOutcome::OutputsMoved { moved, .. } = outcome {
        panic!(
            "INTERNAL CIRCUIT SOUNDNESS SIGNAL in `{}`: cheating advice {cheats:?} and \
             repairing through the captured constraints left every constraint \
             satisfied, yet the computed instance wires {moved:?} moved while every \
             received instance and stage wire was held at its honest value. The \
             circuit accepts two witnesses that agree on everything it takes in and \
             disagree on something it produces.",
            circuit.name,
        );
    }
});
