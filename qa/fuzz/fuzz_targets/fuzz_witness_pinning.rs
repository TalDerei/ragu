//! Witness-pinning soundness oracle: mutate one coefficient of a
//! satisfying trace polynomial and demand the constraint identity reject.
//!
//! This is the constraint-side counterpart to `fuzz_witness_cheat`. That
//! target perturbs values *during* Simulator execution, where every
//! downstream gadget recomputes honestly from the perturbed input — gates
//! self-satisfy by construction, so the Simulator can never expose an
//! under-constrained gadget. The actual soundness question lives on the
//! wiring side: does the constraint system *pin* every witness value the
//! Rust witness generator assigns, or would a prover-chosen substitute
//! pass verification?
//!
//! In Ragu's algebraic formulation (see `fuzz_circuit_revdot_identity`),
//! "witness w satisfies the constraints" is the identity
//!
//! ```text
//! r.revdot(r + r.dilate(z) + s(X, y) + t(X, z)) == circuit.ky(instance, y)
//! ```
//!
//! holding at random `(y, z)`, where `r` is the assembled trace
//! polynomial. The oracle here:
//!
//! 1. Build a satisfying witness and its assembled `r` (alpha = 0).
//! 2. Sanity: the identity holds honestly at two independent `(y, z)`
//!    points (this subsumes `fuzz_circuit_revdot_identity`'s check).
//! 3. Pick one *occupied* (nonzero) coefficient of `r`, add a fuzzer-
//!    chosen nonzero delta, and rebuild the identity with the mutated
//!    `r'` — same instance, same `ky`, a genuinely different witness.
//! 4. Assert the identity now FAILS at one of the two points. If a
//!    changed witness coefficient still satisfies the constraint
//!    identity, nothing in the constraint system pins that wire: a
//!    malicious prover could substitute it freely. That is the
//!    assignment-vs-constraint gap — panic with the offending degree.
//!
//! # Why this has (essentially) no false positives
//!
//! For a pinned coefficient, the mutated identity defect Δ(y, z) is a
//! nonzero polynomial of degree ≤ 8n in y and z, so it vanishes at a
//! random point with probability ~deg/|F| ≈ 2^-245. The fuzzer chooses
//! `y, z` from u64 seeds, so the only *reachable* structured roots are
//! tiny values; we bail on y, z ∈ {0, 1} and additionally require the
//! defect to vanish at a second, affinely independent point before
//! declaring a bug. Roots expressible in the u64 seed range are not
//! expected to exist (≈ deg·2^64/|F| ≈ 2^-180 of them).
//!
//! Mutation is restricted to coefficients that are live for the chosen
//! circuit. The live-degree mask is computed from probe traces of the same
//! circuit under nonzero satisfying witnesses, then unioned with the current
//! trace's nonzero coefficients. This avoids mutating structural padding and
//! intentionally-dead allocation slots while still allowing zero-valued live
//! wires in the current trace to be mutated.
//!
//! # Circuit coverage
//!
//! `SquareCircuit { times }` and `MySimpleCircuit` from
//! `ragu_testing::circuits`, with the cached single-circuit registries
//! and the `Registry::wy`-minus-key-term derivation of `s(X, y)` shared
//! with `fuzz_circuit_revdot_identity` (valid for unmasked
//! single-circuit registries only — see that target's header).

#![no_main]

use arbitrary::Arbitrary;
use core::cell::OnceCell;
use ff::Field;
use ff::PrimeField;
use libfuzzer_sys::fuzz_target;
use pasta_curves::Fp;
use ragu_circuits::{
    CircuitExt, Trace,
    polynomials::{Rank, TestRank, sparse},
    registry::{CircuitIndex, Registry, RegistryBuilder},
};
use ragu_testing::circuits::{MySimpleCircuit, SquareCircuit};
use std::sync::LazyLock;

#[derive(Arbitrary, Debug)]
enum CircuitChoice {
    /// `SquareCircuit { times }` over a single-Fp witness.
    Square {
        times: u8,
        witness_seed: u64,
        use_special: Option<u8>,
    },
    /// `MySimpleCircuit` over `(a, b = sqrt(a^5))`, satisfying witnesses
    /// only — the identity (and therefore the oracle) is meaningful only
    /// for accepted witnesses.
    Simple {
        a_seed: u64,
        use_special_a: Option<u8>,
    },
}

#[derive(Arbitrary, Debug)]
struct Input {
    circuit: CircuitChoice,
    y_seed: u64,
    z_seed: u64,
    /// Index into the list of nonzero coefficient positions of `r`.
    mutate_idx: u16,
    /// Additive perturbation of the chosen coefficient; 0 maps to 1 so
    /// the mutation is always a real change.
    delta_seed: u64,
}

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

/// Per-`times` registry cache for `SquareCircuit`. Same shape as
/// `fuzz_circuit_revdot_identity.rs`.
struct SquareRegistryCache {
    slots: [OnceCell<Result<Registry<'static, Fp, TestRank>, ()>>; 120],
    live_degrees: [OnceCell<Vec<usize>>; 120],
}

// SAFETY: libfuzzer runs the fuzz target on a single thread.
unsafe impl Sync for SquareRegistryCache {}

static SQUARE_REGISTRY_CACHE: LazyLock<SquareRegistryCache> =
    LazyLock::new(|| SquareRegistryCache {
        slots: [const { OnceCell::new() }; 120],
        live_degrees: [const { OnceCell::new() }; 120],
    });

fn square_registry_for(times: usize) -> Option<&'static Registry<'static, Fp, TestRank>> {
    debug_assert!((1..=120).contains(&times));
    SQUARE_REGISTRY_CACHE.slots[times - 1]
        .get_or_init(|| {
            RegistryBuilder::<Fp, TestRank>::new()
                .register_circuit(SquareCircuit { times })
                .and_then(|b| b.finalize())
                .map_err(|_| ())
        })
        .as_ref()
        .ok()
}

static SIMPLE_REGISTRY: LazyLock<Option<Registry<'static, Fp, TestRank>>> = LazyLock::new(|| {
    RegistryBuilder::<Fp, TestRank>::new()
        .register_circuit(MySimpleCircuit)
        .and_then(|b| b.finalize())
        .ok()
});

fn square_native(witness: Fp, times: usize) -> Fp {
    let mut acc = witness;
    for _ in 0..times {
        acc = acc.square();
    }
    acc
}

/// Try to compute `b = sqrt(a^5)` so that `(a, b)` is a satisfying witness
/// for `MySimpleCircuit`. Returns `None` if `a^5` is a non-residue.
fn derive_satisfying_b(a: Fp) -> Option<Fp> {
    Option::<Fp>::from(a.pow_vartime([5u64]).sqrt())
}

fn add_nonzero_degrees(poly: &sparse::Polynomial<Fp, TestRank>, degrees: &mut Vec<usize>) {
    for (degree, coeff) in poly.iter_coeffs().enumerate() {
        if coeff != Fp::ZERO && !degrees.contains(&degree) {
            degrees.push(degree);
        }
    }
}

fn assembled_trace(
    registry: &Registry<'_, Fp, TestRank>,
    trace: &Trace<Fp>,
) -> Result<sparse::Polynomial<Fp, TestRank>, ()> {
    registry
        .assemble_with_alpha(trace, CircuitIndex::new(0), Fp::ZERO)
        .map_err(|_| ())
}

fn square_live_degrees(
    registry: &'static Registry<'static, Fp, TestRank>,
    times: usize,
) -> &'static [usize] {
    SQUARE_REGISTRY_CACHE.live_degrees[times - 1]
        .get_or_init(|| {
            let circuit = SquareCircuit { times };
            let mut degrees = Vec::new();
            for witness in [Fp::ONE, Fp::from(2u64), Fp::MULTIPLICATIVE_GENERATOR] {
                if let Ok(trace) = circuit.trace(witness) {
                    if let Ok(poly) = assembled_trace(registry, &trace.into_output()) {
                        add_nonzero_degrees(&poly, &mut degrees);
                    }
                }
            }
            degrees.sort_unstable();
            degrees
        })
        .as_slice()
}

fn simple_live_degrees(registry: &Registry<'_, Fp, TestRank>) -> Vec<usize> {
    let circuit = MySimpleCircuit;
    let mut degrees = Vec::new();
    for a in (1u64..=64).map(Fp::from) {
        let Some(b) = derive_satisfying_b(a) else {
            continue;
        };
        if let Ok(trace) = circuit.trace((a, b)) {
            if let Ok(poly) = assembled_trace(registry, &trace.into_output()) {
                add_nonzero_degrees(&poly, &mut degrees);
            }
        }
        if degrees.len() >= TestRank::num_coeffs() {
            break;
        }
    }
    degrees.sort_unstable();
    degrees
}

/// Compute `s(X, y)` for a single-circuit registry by stripping the
/// registry key term from `Registry::wy(omega_0, y)`. Same derivation
/// (and same validity caveats) as `fuzz_circuit_revdot_identity.rs`.
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

/// Evaluate the revdot identity left-hand side for trace polynomial `r`
/// at `(y, z)`.
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

/// Run the pinning oracle for one circuit's satisfying trace.
///
/// `ky` must give `circuit.ky(instance, y)` for arbitrary `y`.
fn check_pinning(
    registry: &Registry<'_, Fp, TestRank>,
    trace: &Trace<Fp>,
    live_degrees: &[usize],
    ky: impl Fn(Fp) -> Fp,
    input: &Input,
    describe: &dyn Fn() -> String,
) {
    let y = Fp::from(input.y_seed);
    let z = Fp::from(input.z_seed);
    // Second, affinely independent evaluation point. Kills the residual
    // false-positive risk of the fuzzer landing on a structured root of
    // the defect polynomial at the primary point.
    let y2 = y * Fp::MULTIPLICATIVE_GENERATOR + Fp::from(3);
    let z2 = z * Fp::MULTIPLICATIVE_GENERATOR + Fp::from(7);

    let r = registry
        .assemble_with_alpha(trace, CircuitIndex::new(0), Fp::ZERO)
        .expect("assemble_with_alpha failed on a registered, satisfying witness");

    // Sanity (honest identity, both points) — same oracle as
    // fuzz_circuit_revdot_identity.
    for (py, pz) in [(y, z), (y2, z2)] {
        let actual = identity_lhs(registry, &r, py, pz);
        let expected = ky(py);
        assert_eq!(
            expected,
            actual,
            "honest identity violated at y={py:?}, z={pz:?}: {}",
            describe()
        );
    }

    // Mutate one live coefficient. Include the current nonzero degrees so
    // unusual fuzzer-selected values can expand coverage beyond the probe set,
    // but do not rely on nonzero-ness alone for zero-valued live wires.
    let mut coeffs: Vec<Fp> = r.iter_coeffs().collect();
    let mut occupied = live_degrees.to_vec();
    for (degree, coeff) in coeffs.iter().enumerate() {
        if *coeff != Fp::ZERO && !occupied.contains(&degree) {
            occupied.push(degree);
        }
    }
    if occupied.is_empty() {
        return;
    }
    occupied.sort_unstable();
    let degree = occupied[input.mutate_idx as usize % occupied.len()];
    let mut delta = Fp::from(input.delta_seed);
    if delta == Fp::ZERO {
        delta = Fp::ONE;
    }
    coeffs[degree] += delta;
    let mutated = sparse::Polynomial::<Fp, TestRank>::from_coeffs(coeffs);

    // The mutated witness must be rejected at at least one of the two
    // points. Surviving both means the constraint system never pins the
    // wire behind this coefficient.
    let survives_1 = identity_lhs(registry, &mutated, y, z) == ky(y);
    let survives_2 = survives_1 && identity_lhs(registry, &mutated, y2, z2) == ky(y2);

    assert!(
        !survives_2,
        "PINNING VIOLATION: trace coefficient at degree {degree} \
         (n = {}) changed by {delta:?} yet the constraint identity still \
         holds at two independent points (y={y:?}, z={z:?}) and \
         (y2={y2:?}, z2={z2:?}). The constraint system does not pin this \
         wire — a malicious prover could substitute it freely. {}",
        TestRank::n(),
        describe()
    );
}

fuzz_target!(|input: Input| {
    if std::env::var("DEBUG_INPUT").is_ok() {
        eprintln!("{:#?}", input);
        return;
    }

    // y, z ∈ {0, 1} collapse too much identity structure (dilate(0),
    // s(X, 0), trivial powers) for the rejection direction of the oracle;
    // those points are exercised by fuzz_circuit_revdot_identity's
    // accept direction instead.
    if input.y_seed < 2 || input.z_seed < 2 {
        return;
    }

    match input.circuit {
        CircuitChoice::Square {
            times,
            witness_seed,
            use_special,
        } => {
            let times = ((times as usize) % 120).max(1);
            let witness: Fp = match use_special {
                Some(idx) => special_value(idx),
                None => Fp::from(witness_seed),
            };

            let registry = match square_registry_for(times) {
                Some(r) => r,
                None => return,
            };
            let circuit = SquareCircuit { times };
            let instance = square_native(witness, times);
            let trace = match circuit.trace(witness) {
                Ok(t) => t.into_output(),
                Err(_) => return,
            };
            check_pinning(
                registry,
                &trace,
                square_live_degrees(registry, times),
                |py| {
                    circuit
                        .ky(instance, py)
                        .expect("SquareCircuit::ky should not fail on Fp instance")
                },
                &input,
                &|| {
                    format!(
                        "SquareCircuit times={times}, witness={witness:?}, instance={instance:?}"
                    )
                },
            );
        }

        CircuitChoice::Simple {
            a_seed,
            use_special_a,
        } => {
            let a: Fp = match use_special_a {
                Some(idx) => special_value(idx),
                None => Fp::from(a_seed),
            };
            let b = match derive_satisfying_b(a) {
                Some(v) => v,
                None => return,
            };

            let registry = match SIMPLE_REGISTRY.as_ref() {
                Some(r) => r,
                None => return,
            };
            let circuit = MySimpleCircuit;
            let instance: (Fp, Fp) = (a + b, a - b);
            let trace = match circuit.trace((a, b)) {
                Ok(t) => t.into_output(),
                Err(_) => return,
            };
            check_pinning(
                registry,
                &trace,
                &simple_live_degrees(registry),
                |py| {
                    circuit
                        .ky(instance, py)
                        .expect("MySimpleCircuit::ky should not fail on (Fp, Fp) instance")
                },
                &input,
                &|| format!("MySimpleCircuit a={a:?}, b={b:?}, instance={instance:?}"),
            );
        }
    }
});
