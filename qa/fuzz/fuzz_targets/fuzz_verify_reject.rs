//! Fuzz the verifier with corrupted proofs.
//!
//! Applies fuzzer-chosen [`Corruption`] variants to a valid trivial proof.
//!
//! Invariant: `verify()` never panics. Corrupted proofs are rejected
//! (`Ok(false)`) or produce `Err`.

#![no_main]

use arbitrary::Arbitrary;
use ff::Field;
use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_circuits::polynomials::ProductionRank;
use ragu_pasta::Pasta;
use ragu_pcd::{ApplicationBuilder, Proof, fuzz_utils::Corruption};
use rand::{SeedableRng, rngs::StdRng};

use std::sync::LazyLock;

type C = Pasta;
type R = ProductionRank;
const HEADER_SIZE: usize = 4;

/// Wrapper to satisfy `Sync` for `Application` (which contains a
/// `OnceCell` field — `seeded_trivial` — for memoizing the trivial-proof
/// fixture, breaking auto-`Sync`).
struct SyncApp(ragu_pcd::Application<'static, C, R, HEADER_SIZE>);
// SAFETY: this fuzz body invokes `Application` exclusively through
// `app.test_trivial_proof()` (which only reads from the application,
// initializing `seeded_trivial` on the first call and reading it
// thereafter) and `verify(&proof)` (which takes `&Application` and never
// touches `seeded_trivial`). libfuzzer drives `fuzz_target!` on a single
// thread, so even the `OnceCell` initialization on the very first call
// is uncontended. If this target ever grows to spawn worker threads or
// to mutate `Application` state, the assumption must be revisited.
unsafe impl Sync for SyncApp {}

static APP: LazyLock<SyncApp> = LazyLock::new(|| {
    let pasta = Pasta::baked();
    SyncApp(
        ApplicationBuilder::<C, R, HEADER_SIZE>::new()
            .finalize(pasta)
            .expect("failed to create application"),
    )
});

/// Cached trivial proof. Building one runs the full endoscaling pipeline
/// (hundreds of ms per call), but the result is deterministic from
/// `&APP.0`. Cloning the cached value is ~10000x faster than rebuilding,
/// so per-input work clones, corrupts, and verifies — turning the
/// fuzz_verify_reject hot path into clone + corrupt + verify rather than
/// build + corrupt + verify.
static TRIVIAL_PROOF: LazyLock<Proof<C, R>> = LazyLock::new(|| APP.0.test_trivial_proof());

#[derive(Arbitrary, Debug)]
enum FuzzCorruption {
    PBlind(u64),
    PEval(u64),
    AbC(u64),
    CircuitId,
    ChallengeU(u64),
    ChallengeX(u64),
    ChallengeY(u64),
    LeftHeaderLen(u8),
    RightHeaderLen(u8),
}

#[derive(Arbitrary, Debug)]
struct Input {
    corruption: FuzzCorruption,
    rng_seed: u64,
}

fuzz_target!(|input: Input| {
    // DEBUG_INPUT=1 prints the parsed Arbitrary input and exits — useful for
    // triaging crash artifacts. See README.md "DEBUG_INPUT env var" section.
    if std::env::var("DEBUG_INPUT").is_ok() {
        eprintln!("{:#?}", input);
        return;
    }
    let app = &APP.0;

    let mut proof = TRIVIAL_PROOF.clone();

    // The fixture has challenges equal to one, circuit id zero, and four
    // header elements. Nudge every fuzzer choice away from those values so
    // each variant performs a real corruption before rejection is asserted.
    let nonzero_delta = |v: u64| {
        let v = Fp::from(v);
        if v == Fp::ZERO { Fp::ONE } else { v }
    };
    let changed_challenge = |v: u64| {
        let v = Fp::from(v);
        if v == Fp::ONE { Fp::from(2u64) } else { v }
    };
    let wrong_header_len = |v: u8| {
        let v = v as usize;
        if v == HEADER_SIZE { HEADER_SIZE + 1 } else { v }
    };
    let corruption = match input.corruption {
        FuzzCorruption::PBlind(v) => Corruption::PBlind(nonzero_delta(v)),
        FuzzCorruption::PEval(v) => Corruption::PEval(nonzero_delta(v)),
        FuzzCorruption::AbC(v) => Corruption::AbC(nonzero_delta(v)),
        FuzzCorruption::CircuitId => Corruption::CircuitId(u32::MAX),
        FuzzCorruption::ChallengeU(v) => Corruption::ChallengeU(changed_challenge(v)),
        FuzzCorruption::ChallengeX(v) => Corruption::ChallengeX(changed_challenge(v)),
        FuzzCorruption::ChallengeY(v) => Corruption::ChallengeY(changed_challenge(v)),
        FuzzCorruption::LeftHeaderLen(v) => Corruption::LeftHeaderLen(wrong_header_len(v)),
        FuzzCorruption::RightHeaderLen(v) => Corruption::RightHeaderLen(wrong_header_len(v)),
    };

    proof.corrupt(corruption);

    let pcd = proof.carry::<()>(());
    let rng = StdRng::seed_from_u64(input.rng_seed);

    // Must never panic or accept. Internal computation errors are rejection.
    let result = app.verify(&pcd, rng);
    assert!(
        !matches!(result, Ok(true)),
        "verifier accepted a deliberately corrupted proof: {:?}",
        input.corruption,
    );
});
