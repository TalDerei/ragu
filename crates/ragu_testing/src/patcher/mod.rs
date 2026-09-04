//! The patcher engine: under-constraint hunting over a recorded constraint
//! graph.
//!
//! The *patcher* (after zksecurity's "Towards Fuzzing Zero-Knowledge Proof
//! Circuits") starts from a satisfying witness, lets a malicious prover
//! rewrite some free advice, and then *repairs* the rest of the witness so
//! every constraint the circuit emitted still holds — propagating the cheat
//! exactly as far as the constraints force it and no further. A cheat that
//! survives repair but changes something the circuit's specification says is
//! determined is an under-constrained-advice bug. This module is the
//! driver-level machinery behind that technique; the policy of *what* to
//! cheat and *which* oracle judges the result belongs to the caller (the
//! `fuzz_advice_patcher` target in `qa/fuzz` for generated gadget programs;
//! `ragu_pcd`'s own tests for the internal recursion circuits).
//!
//! # Pieces
//!
//! * [`Recorder`] — a [`Driver`](ragu_core::drivers::Driver) that captures
//!   the constraint graph ragu emits (gates, pooled-allocation `C · D = 0`
//!   constraints, linear-combination wires, `enforce_zero`s) as a flat list
//!   of [`Event`]s over `usize` wires, alongside the honest wire values.
//!   [`TrackingAllocator`] is the production pooling allocator with
//!   bookkeeping of the wires it wastes.
//! * [`analyze_source_shape`] / [`source_lint`] — witness-free source-shape
//!   analysis: executes the same generic circuit code with an `Empty` driver,
//!   then requires its exact event, coefficient, wire, and output shape to
//!   equal concrete synthesis. This is Ragu-level abstract interpretation,
//!   not a general rustc AST/MIR lint.
//! * [`analyze_connectivity`] / [`analyze_component_rank`] — post-synthesis
//!   static checks for isolated or floating subgraphs and locally movable
//!   derived wires. Rank coverage is explicit: components above the caller's
//!   dense-elimination cap are reported as skipped, never called clean.
//! * [`repair`] / [`constraints_hold`] — the repair solver and the
//!   acceptance check over a recorded graph.
//! * [`underconstrained_derived`] — the rank/nullity oracle: derived wires
//!   that can move while every declared free wire is held fixed.
//! * [`determinism_probe`] / [`determinism_sweep`] — the pinned-input
//!   soundness oracle (issue #793's "same inputs give the same outputs"):
//!   pin the declared inputs, cheat the remaining free advice, repair, and
//!   flag any output that moves while every constraint still holds.
//! * [`discover_free_advice`] — structural discovery of the free-advice
//!   candidates a recorded graph exposes (the wires no constraint derives
//!   from earlier ones), with [`allocation_waste`] classifying the wires an
//!   allocator wastes by design so a census can subtract them.
//! * [`Playback`] — the independent cross-check: re-runs the same synthesis
//!   and verifies an injected witness live, so a recorder capture bug cannot
//!   silently corrupt a verdict.
//! * [`capture`] / [`capture_with_stage_values`] / [`playback`] — the
//!   [`Circuit`](ragu_circuits::Circuit) entry points: run a circuit's
//!   `witness` (and its output serialization) through the drivers, exposing
//!   the wires of its public instance. [`capture_with_stage_values`] takes
//!   the honest stage values from a harness that has the stage witnesses, so
//!   even a staged [`MultiStage`](ragu_circuits::staging::MultiStage)
//!   circuit — every internal recursion circuit is one — yields a
//!   self-consistent capture that names its reserved stage wires.
//! * [`forced_by`] — the static half of the pinned-input oracle: the wires
//!   a declared input set determines, so a declared output that is not
//!   among them is flagged before any cheat is tried.
//! * [`Prepared`] — the pinned-input oracle with the input-forced part of
//!   the witness solved once, for harnesses that probe the same capture
//!   thousands of times.
//! * [`selftest`] — a planted under-constrained circuit whose signal must
//!   fire, so the soundness direction is never vacuous.
//!
//! Everything is driven through the `Driver` trait alone; the engine never
//! needs to know how a circuit was produced.

mod analysis;
mod circuit;
mod discover;
mod oracle;
mod recorder;

pub use analysis::{
    ComponentRankReport, ConnectedSubgraph, ConnectivityReport, analyze_component_rank,
    analyze_connectivity,
};
pub use circuit::{
    Capture, SourceLintReport, SourceShape, analyze_source_shape, capture,
    capture_with_stage_values, playback, source_lint,
};
pub use discover::{allocation_waste, discover_free_advice, forced_by};
pub use oracle::{
    Prepared, ProbeOutcome, SweepReport, Violation, determinism_probe, determinism_sweep,
};
pub use recorder::{
    Event, Playback, Recorder, TrackingAllocator, constraints_hold, repair, selftest,
    underconstrained_derived,
};
