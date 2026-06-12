//! Exercise the patcher engine over structured circuit idioms — the deep
//! chains, multiply-accumulate pipelines, decompose/recompose, and
//! conditional gates that random op-soup rarely assembles but real bugs
//! inhabit.

use proptest::prelude::*;
use ragu_pasta::Fp;
use ragu_primitives::{Simulator, allocator::Standard};
use ragu_testing::{
    recorder::{Recorder, TrackingAllocator, constraints_hold, repair, underconstrained_derived},
    substrate::{
        AdviceSlot, IDIOM_BUILDERS, Limits, OpSet, Overrides, Program, deep_chain, idiom_programs,
        idiom_seed_corpus, multiply_accumulate, shadow_eval, synthesize,
    },
};

/// Writes the encoded idiom corpus into the libFuzzer corpus directories of
/// the substrate-based targets. Gated on `WRITE_FUZZ_SEEDS=1` so a normal
/// `cargo test` stays hermetic; run it once to (re)generate the committed
/// seed files:
///
/// ```text
/// WRITE_FUZZ_SEEDS=1 cargo test -p ragu_testing --test idioms write_seed_corpus
/// ```
#[test]
fn write_seed_corpus() {
    if std::env::var("WRITE_FUZZ_SEEDS").is_err() {
        return;
    }
    use std::path::PathBuf;

    let fuzz = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../qa/fuzz/corpus")
        .canonicalize()
        .or_else(|_| {
            // The corpus root may not exist yet; build the path directly.
            Ok::<_, std::io::Error>(
                PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../qa/fuzz/corpus"),
            )
        })
        .unwrap();

    for target in ["fuzz_advice_patcher", "fuzz_completeness"] {
        let dir = fuzz.join(target);
        std::fs::create_dir_all(&dir).unwrap();
        for (i, seed) in idiom_seed_corpus().iter().enumerate() {
            std::fs::write(dir.join(format!("idiom_seed_{i:02}")), seed).unwrap();
        }
    }
}

/// Every idiom encodes and decodes back to itself, so the seed corpus a
/// fuzzer loads is exactly the program built here.
#[test]
fn idioms_round_trip_through_the_decoder() {
    for program in idiom_programs() {
        let bytes = program.encode();
        let decoded = Program::decode(&bytes, OpSet::ALL, Limits::default());
        assert_eq!(
            decoded, program,
            "idiom did not round-trip through encode/decode"
        );
    }
    // The seed corpus is just the encoded battery.
    assert_eq!(idiom_seed_corpus().len(), idiom_programs().len());
    assert!(idiom_seed_corpus().iter().all(|s| !s.is_empty()));
}

/// Every idiom is accepted by ragu's real `Simulator` on its honest witness
/// (no idiom is accidentally over-constrained) and ends in an anchor.
#[test]
fn idioms_are_satisfiable() {
    for program in idiom_programs() {
        let shadow = shadow_eval::<Fp>(&program, Overrides::none());
        let sim = Simulator::<Fp>::simulate((), |dr, _| {
            synthesize(dr, &mut Standard::new(), &program, &shadow.anchors)?;
            Ok(())
        });
        assert!(
            sim.is_ok(),
            "Simulator rejected the honest idiom {program:?}"
        );
        assert!(
            !shadow.anchors.is_empty(),
            "idiom {program:?} has no anchor"
        );
    }
}

/// The rank/nullity oracle is clean on the arithmetic idioms: with the
/// advice and allocator waste held fixed, every derived wire is pinned.
/// (The conditional-gating idiom uses booleans/select, outside this oracle's
/// model, so it is excluded here.)
#[test]
fn idioms_have_no_underconstrained_wires() {
    let arithmetic = [deep_chain as fn(u64) -> Program, multiply_accumulate];
    for build in arithmetic {
        for seed in [1u64, 7, 99, 0xabcd] {
            let program = build(seed);
            let shadow = shadow_eval::<Fp>(&program, Overrides::none());
            let mut rec = Recorder::<Fp>::new();
            let mut alloc = TrackingAllocator::default();
            let stacks = synthesize(&mut rec, &mut alloc, &program, &shadow.anchors).unwrap();
            let mut free = stacks.advice_wires.clone();
            free.extend_from_slice(&rec.extras);
            free.extend_from_slice(&alloc.wasted);
            let movable = underconstrained_derived(&rec.events, &rec.values, &free);
            assert!(
                movable.is_empty(),
                "rank oracle flagged {movable:?} in idiom {program:?}",
            );
        }
    }
}

proptest! {
    /// On the arithmetic idioms the patcher differential is non-vacuous and
    /// sound: cheating the first advice wire propagates through the chain to
    /// the terminal anchor, so ragu rejects exactly when the native oracle
    /// reports the anchor violated.
    #[test]
    fn proptest_idiom_cheat_is_observed(
        which in 0usize..2, // deep_chain, multiply_accumulate (arithmetic)
        seed in any::<u64>(),
        delta in 1u64..1_000_000,
    ) {
        let program = IDIOM_BUILDERS[which](seed);
        let shadow = shadow_eval::<Fp>(&program, Overrides::none());
        let advice_slots: Vec<usize> = shadow
            .advice
            .iter()
            .filter_map(|a| match a {
                AdviceSlot::Elem(i) => Some(*i),
                _ => None,
            })
            .collect();
        prop_assume!(!advice_slots.is_empty());

        let mut rec = Recorder::<Fp>::new();
        let mut alloc = TrackingAllocator::default();
        let stacks = synthesize(&mut rec, &mut alloc, &program, &shadow.anchors).unwrap();
        let slot_wires: Vec<usize> = stacks.elems.iter().map(|e| *e.wire()).collect();

        let slot = advice_slots[0];
        let d = Fp::from(delta);

        // ragu side: cheat, repair, check.
        let mut values = rec.values.clone();
        values[slot_wires[slot]] += d;
        repair(&rec.events, &mut values, &stacks.advice_wires);
        let ragu_accepts = constraints_hold(&rec.events, &values);

        // native side: recompute the chain and compare anchors.
        let overrides = [(slot, shadow.elems[slot] + d)];
        let mutated = shadow_eval::<Fp>(
            &program,
            Overrides { elems: &overrides, ..Overrides::none() },
        );
        prop_assume!(mutated.elems.len() == shadow.elems.len() && mutated.bools == shadow.bools);
        let native_ok = mutated.anchors == shadow.anchors;

        prop_assert_eq!(ragu_accepts, native_ok, "idiom differential disagreed on {:?}", program);
    }
}
