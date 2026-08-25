# Backend boundary lane

`ragu_backend::Backend` is a seam: every method has a correctness-first
default that delegates to the canonical code in `ragu_arithmetic` and
`ragu_circuits`, and `ragu_acceleration` overrides individual methods with
faster implementations that must be observationally identical. This directory
holds the pins and scripts that make that boundary a CI property rather than a
review convention, so that override work can land on mechanical evidence.

## Tiers

CI (`.github/workflows/rust.yml`, job `detect changes`) classifies every
changed path:

| Tier | Paths | What it means |
|---|---|---|
| **Frozen** | the canonical crates (`ragu_arithmetic`, `ragu_core`, `ragu_circuits`, `ragu_primitives`, `ragu_pcd`, `ragu_pasta`, `ragu_macros`), the contract crate `ragu_backend`, the fixtures crate `ragu_testing`, `crates/ragu_acceleration/Cargo.toml`, the root manifest, `Cargo.lock`, `rust-toolchain.toml`, `.cargo/`, `qa/backend/`, `qa/lean/`, `qa/supply-chain/`, `.github/` | canonical semantics, dependencies, toolchain, and this lane itself; code-owner review |
| **Fast lane** | `crates/ragu_acceleration/{src,tests,benches}/` and its `CHANGELOG.md`/`README.md` | override code only — never dependencies, features, or semantics |

A pull request that touches both tiers fails the `tier mix` job unless it
carries the `boundary-change` label: adding a seam (a `Backend` method) and
filling it (an override) are separate changes. The acceleration manifest is
frozen because a dependency, feature, or build script is a supply-chain
decision, not an optimisation.

Overrides of the kernels `ragu_pcd`'s verifier consults (`sparse_eval`,
`sparse_revdot`, `registry_circuit_y`, `registry_wxy`) live under
`crates/ragu_acceleration/src/verifier/` and carry a stricter bar: the
`verifier` path filter makes mutation testing required for them, and
`census.sh` rejects value-dependent control flow there. Applications choose
whether verification uses accelerated kernels through the sealed
`ragu_pcd::SelectableBackend::Verifier` mapping
(`crates/ragu_pcd/src/backend.rs`).

## Files

| File | Pins / checks | Regenerate |
|---|---|---|
| `deps.py check` | dependency direction (`ragu_acceleration` may depend only on `ragu_backend`, `ragu_arithmetic`, `ragu_circuits`; no frozen crate depends on it except `ragu_pcd`'s sealing edge), default-feature passthrough (a default build of `ragu_pcd` pulls no acceleration dependency), the acceleration-feature list, and `dep-census.txt` | `deps.py update` |
| `deps.py leakage` | enabling an acceleration feature on `ragu_pcd` must not change the features of any package the frozen build already contains, on any supported target, except entries in `feature-leak-allowlist.txt` | edit the allowlist deliberately |
| `census.sh` | every override is `cfg(feature)`-gated with a reference fallback and uses no other `cfg`; `AcceleratedProver` forwards the same overrides; every override has `transitions/<method>.txt` and a test consuming it; verifier-consulted overrides delegate to `src/verifier/`; `verify.rs` uses only `Verifier::<B>`; `unsafe` count matches `unsafe-census.txt` with `// SAFETY:` comments; no build script, ambient entropy/time, unapproved `#[path]`, or cross-crate `include!`; only the two canonical backend-equivalence test includes are allowed, and only `backend.rs` names `ragu_acceleration` in frozen sources | edit the pins deliberately |
| `api-snapshot.sh check` | the `Backend` trait surface equals `api/ragu_backend.txt` and takes no RNG or transcript | `api-snapshot.sh update` |
| `transitions/<method>.txt` | sizes at which an override changes algorithm; the equivalence tests check both sides of each | when the override's algorithm changes |
| `dep-census.txt` | build-script and proc-macro packages reachable from the frozen crates and from the acceleration-exclusive subtree | `deps.py update` |
| `feature-leak-allowlist.txt` | `<triple or *>:<package>:<feature>` leaks accepted as frozen-tier decisions | edit deliberately |
| `unsafe-census.txt` | number of `unsafe` occurrences in `crates/ragu_acceleration/src` | edit deliberately |

Every file here is frozen-tier: changing a pin is the review event.

Run everything locally with `just backend_boundary`; CI runs the same commands
in the `backend boundary` job.
