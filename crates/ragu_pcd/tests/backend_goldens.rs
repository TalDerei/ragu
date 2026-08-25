//! Golden proof digests and RNG fingerprints (`qa/backend/goldens/`).
//!
//! Drives the nontrivial fixture steps through seed, seed, fuse, and
//! rerandomize with fixed seeds on every selectable backend, recording the
//! proof digest and the caller's RNG state after every step, then the
//! verifier's decision and RNG state on each valid proof and on nine
//! corruptions of the fused one. Every backend must produce the same trace,
//! and the trace must equal the committed golden, so any drift in protocol,
//! transcript, or randomness consumption — on either backend, on any
//! platform CI runs — is a visible diff. The trace is platform-independent,
//! so whichever machine generated the golden, every OS in the CI matrix (and
//! the hand-written AArch64 field arithmetic `native-msm` enables on Apple
//! Silicon) is compared against the same file.
//!
//! Regenerate deliberately with `just goldens_update` (`UPDATE_GOLDENS=1`);
//! the file is frozen-tier, so the diff is the review event.
#![cfg(feature = "unstable-fuzzing")]

use std::fmt::Write as _;

use ragu_acceleration::{AcceleratedBackend, AcceleratedProver};
use ragu_arithmetic::{
    Cycle,
    ff::{Field, PrimeField},
};
use ragu_backend::ReferenceBackend;
use ragu_circuits::polynomials::ProductionRank;
use ragu_pasta::{Fp, Pasta};
use ragu_pcd::{
    Application, ApplicationBuilder, Pcd, SelectableBackend, fuzz_utils::Corruption, header::Header,
};
use ragu_testing::pcd::nontrivial::{Hash2, InternalNode, WitnessLeaf};
use rand::{RngExt, SeedableRng, rngs::StdRng};

const HEADER_SIZE: usize = 4;
const GOLDEN: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../qa/backend/goldens/pasta-r13-h4.txt"
);
const PROOF_SEEDS: [u64; 2] = [0, 1];
const VERIFIER_SEED: u64 = 7;

type App<'params, B> = Application<'params, Pasta, ProductionRank, HEADER_SIZE, B>;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn field_hex<F: PrimeField>(value: &F) -> String {
    hex(value.to_repr().as_ref())
}

/// Four words drawn from the RNG, so a step that consumes a different amount
/// of randomness changes the trace even when it produces the same proof.
fn fingerprint(rng: &mut StdRng) -> String {
    (0..4)
        .map(|_| format!("{:016x}", rng.random::<u64>()))
        .collect::<Vec<_>>()
        .join(",")
}

fn corruptions() -> [(&'static str, Corruption<Fp>); 9] {
    [
        ("p_blind", Corruption::PBlind(Fp::ONE)),
        ("p_eval", Corruption::PEval(Fp::ONE)),
        ("ab_c", Corruption::AbC(Fp::ONE)),
        ("circuit_id", Corruption::CircuitId(u32::MAX)),
        ("challenge_u", Corruption::ChallengeU(Fp::from(12_345))),
        ("challenge_x", Corruption::ChallengeX(Fp::from(23_456))),
        ("challenge_y", Corruption::ChallengeY(Fp::from(34_567))),
        ("left_header_len", Corruption::LeftHeaderLen(0)),
        (
            "right_header_len",
            Corruption::RightHeaderLen(HEADER_SIZE * 2),
        ),
    ]
}

fn record_proof<H: Header<Fp>>(
    out: &mut String,
    seed: u64,
    step: &str,
    pcd: &Pcd<Pasta, ProductionRank, H>,
    rng: &mut StdRng,
) {
    writeln!(
        out,
        "proof[{seed}].{step}: digest={} rng={}",
        hex(&pcd.proof().test_digest()),
        fingerprint(rng)
    )
    .unwrap();
}

fn record_verify<B: SelectableBackend, H: Header<Fp>>(
    out: &mut String,
    app: &App<'_, B>,
    seed: u64,
    target: &str,
    pcd: &Pcd<Pasta, ProductionRank, H>,
) {
    let mut rng = StdRng::seed_from_u64(VERIFIER_SEED);
    let decision = match app.verify(pcd, &mut rng) {
        Ok(true) => "accept",
        Ok(false) => "reject",
        Err(_) => "error",
    };
    writeln!(
        out,
        "verify[{seed}].{target}: {decision} rng={}",
        fingerprint(&mut rng)
    )
    .unwrap();
}

fn trace<B: SelectableBackend>() -> String {
    let pasta = Pasta::baked();
    let poseidon_params = Pasta::circuit_poseidon(pasta);
    let app = ApplicationBuilder::<Pasta, ProductionRank, HEADER_SIZE>::new()
        .with_backend::<B>()
        .register(WitnessLeaf { poseidon_params })
        .unwrap()
        .register(Hash2 { poseidon_params })
        .unwrap()
        .finalize(pasta)
        .unwrap();

    let mut out = String::new();
    writeln!(out, "format: 1").unwrap();
    writeln!(
        out,
        "cycle: pasta; rank: {}; header_size: {HEADER_SIZE}; steps: WitnessLeaf, Hash2; verifier_seed: {VERIFIER_SEED}",
        <ProductionRank as ragu_circuits::polynomials::Rank>::RANK
    )
    .unwrap();
    writeln!(
        out,
        "registry.native: {}",
        field_hex(&app.native_registry().digest())
    )
    .unwrap();

    for seed in PROOF_SEEDS {
        let mut rng = StdRng::seed_from_u64(seed);
        let (leaf1, _) = app
            .seed(&mut rng, WitnessLeaf { poseidon_params }, Fp::from(1))
            .unwrap();
        record_proof(&mut out, seed, "seed(1)", &leaf1, &mut rng);
        let (leaf2, _) = app
            .seed(&mut rng, WitnessLeaf { poseidon_params }, Fp::from(2))
            .unwrap();
        record_proof(&mut out, seed, "seed(2)", &leaf2, &mut rng);
        let (node, _) = app
            .fuse(
                &mut rng,
                Hash2 { poseidon_params },
                (),
                leaf1.clone(),
                leaf2,
            )
            .unwrap();
        record_proof(&mut out, seed, "fuse", &node, &mut rng);
        let rerandomized = app.rerandomize(node.clone(), &mut rng).unwrap();
        record_proof(&mut out, seed, "rerandomize", &rerandomized, &mut rng);
        writeln!(out, "data[{seed}].fuse: {}", field_hex(node.data())).unwrap();

        record_verify(&mut out, &app, seed, "seed(1)", &leaf1);
        record_verify(&mut out, &app, seed, "fuse", &node);
        record_verify(&mut out, &app, seed, "rerandomize", &rerandomized);

        let (proof, data) = node.into_parts();
        for (label, corruption) in corruptions() {
            let mut corrupted = proof.clone();
            corrupted.corrupt(corruption);
            let corrupted = corrupted.carry::<InternalNode>(data);
            record_verify(&mut out, &app, seed, &format!("fuse+{label}"), &corrupted);
        }
    }
    out
}

fn first_difference(expected: &str, actual: &str) -> String {
    for (index, (e, a)) in expected.lines().zip(actual.lines()).enumerate() {
        if e != a {
            return format!("line {}:\n  golden: {e}\n  actual: {a}", index + 1);
        }
    }
    let (e, a) = (expected.lines().count(), actual.lines().count());
    if e == a {
        "every line matches but the files differ byte-for-byte (line endings or trailing whitespace?)"
            .to_string()
    } else {
        format!("line counts differ: golden {e} vs actual {a}")
    }
}

#[test]
fn every_backend_matches_the_golden() {
    let reference = trace::<ReferenceBackend>();
    let accelerated = trace::<AcceleratedBackend>();
    let prover = trace::<AcceleratedProver>();
    assert!(
        reference == accelerated,
        "AcceleratedBackend trace differs from the reference at {}",
        first_difference(&reference, &accelerated)
    );
    assert!(
        reference == prover,
        "AcceleratedProver trace differs from the reference at {}",
        first_difference(&reference, &prover)
    );

    if std::env::var_os("UPDATE_GOLDENS").is_some() {
        assert!(
            std::env::var_os("CI").is_none(),
            "refusing to rewrite goldens under CI"
        );
        std::fs::write(GOLDEN, &reference).expect("write golden");
        return;
    }

    // Checkouts with `core.autocrlf=true` (GitHub's Windows runners) deliver
    // the golden with CRLF line endings; the trace is defined with LF.
    let golden = std::fs::read_to_string(GOLDEN)
        .expect("golden file missing; generate it with `just goldens_update`")
        .replace("\r\n", "\n");
    assert!(
        golden == reference,
        "trace differs from the committed golden (qa/backend/goldens/pasta-r13-h4.txt) at {}\n\
         If the protocol change is intended, regenerate with `just goldens_update` and review the diff.",
        first_difference(&golden, &reference)
    );
}
