# FV gadget-gap checklist

Working checklist for closing the formal-verification gaps at the gadget layer
(branch `worktree-fv-gadget-gaps`, based on `fv-reorg`). Scratch document for
the branch — not meant to ship with the PR.

Pipeline for every new instance (see `book/src/fv/circuits/`):

1. Rust: `qa/lean/extraction/src/instances/<name>.rs` — a `CircuitInstance`
   driving the *real* gadget on `ExtractionDriver`; register in
   `instances/mod.rs` and `EXPORT_TARGETS` in `main.rs`.
2. Lean: `Ragu/Circuits/<Area>/<Name>.lean` — Clean reimpl + `Assumptions` +
   `Spec` + `soundness` + `completeness`, no `sorry`.
3. Lean: `Ragu/Instances/<Area>/<Name>.lean` — `formal_instance` at the concrete
   prime with `deserializeInput` / `serializeOutput`.
4. `cargo run -p lean_extraction -- export` (regenerates `Ragu/Instances.lean`
   and `Ragu/Fingerprint/Instances.lean`), then `-- check`.
5. `lake build --wfail` and fingerprint diff:
   `cargo run -p lean_extraction -- fingerprint | sort` vs
   `(cd qa/lean && lake env lean --run Ragu/Fingerprint/Main.lean) | sort`.

## 0. Setup

- [x] Worktree `fv-gadget-gaps` rebased onto `fv-reorg` (extractor lives at
      `qa/lean/extraction/`).
- [x] `qa/lean/.lake/packages` symlinked to the main checkout's prebuilt
      mathlib/clean (avoids a multi-hour rebuild).
- [x] Baseline `lake build --wfail` green in the worktree.
- [x] Baseline fingerprint diff green (32 instances).

## 1. Horner — `ragu_circuits::horner::Horner`  (small; same trace as `Element::fold`)

`Horner::write` is `acc.mul(point).add(value)` per element — byte-identical
trace to `Element::fold` at the same length, so the `Fold` reimpl and proof
carry over. `finish_ky` differs: the last term is the constant `1`, not an
input wire.

- [x] Rust `instances/horner.rs`: `HornerInstanceN3`, `HornerInstanceN7`
      (`fold_revdot.rs` inner length), `HornerInstanceN19` (outer length,
      `NumGroups`) driving `Horner::new` + `write` + `finish`. Digests are
      byte-identical to `FoldN3`/`FoldN7`/`FoldN19`, confirming the trace
      identity.
- [x] Rust `HornerKyInstanceN3` driving `finish_ky`. (Production `k(Y)`
      lengths depend on each circuit's instance size; the Lean proof is
      parametric in `n`, so only the shape is pinned. Add a production-length
      instance if a specific circuit's `k(Y)` is ever in scope.)
- [x] Lean `Ragu/Circuits/Horner/Ky.lean`: `main n := Fold.circuit (n+1)
      ⟨coefficients.push 1, point⟩` as a sub-circuit; spec `output = horner
      (coefficients.push 1) point`; soundness/completeness fall straight out
      of `Fold`'s (axioms: `propext`, `Classical.choice`, `Quot.sound` only).
- [x] Lean instances `Ragu/Instances/Horner/N{3,7,19}.lean` (reuse
      `Circuits.Element.Fold.circuit n`) and `Horner/KyN3.lean`.
- [x] Register, export, build, fingerprint match (37/37).

## 2. Poseidon — `ragu_primitives::poseidon::{Sponge, Permutation}`  (large; the real hole)

Shape (Pasta, both fields): `T = 5`, `RATE = 4`, `α = 5`, `FULL_ROUNDS = 8`
(4 + 4), `PARTIAL_ROUNDS = 56`. One permutation = 64 rounds =
`8·5 + 56·1 = 96` S-boxes = 288 `Mul` gates (864 witnesses, 864 asserts).
Linear layers (round constants, MDS) are gate-free `add`/`multiadd`.

### 2a. Design spike (must settle before writing proofs)

Measured on the Rust side (`poseidon_sponge.rs::tests::trace_stats`,
absorb 1 + squeeze 1 over `PoseidonFp`): 1152 ops = 864 witnesses + 864
asserts (288 `Mul` gates), the largest normalized assert has **63
monomials**, 8556 monomials in total, fingerprint in ~220 ms. So the trace
itself is small; only the *tree shape* of the partial-round expressions is
the hazard.

- [x] **Expression blowup in partial rounds — confirmed, design chosen.**
      In a partial round only `state[0]` is re-materialized by the S-box;
      `state[1..5]` stay linear `Expression` trees that the MDS multiplies 4×
      per round (~4⁵⁶ nodes as trees). Rust survives via the `Arc` DAG plus
      pointer-memoized `fingerprint.rs::normalize`; Lean's
      `Ragu/Fingerprint.lean:91 normalize` is a plain tree walk and Clean
      proofs would unfold the trees. Clean's `Expression` (`var | const |
      add | mul`) ships no normalizer. Plan: a semantics-preserving
      `normalizeLinear : Expression F → Expression F` (collect `const +
      Σ cᵢ·varᵢ` into a sorted, merged assoc list and rebuild an O(#vars)
      tree; return the input unchanged when it is not linear) with
      `eval_normalizeLinear : eval env (normalizeLinear e) = eval env e` for
      *all* `e`, applied to the state words at every round boundary. Because
      the lemma is unconditional, round soundness never needs a linearity
      hypothesis, and the fingerprint is unaffected since it hashes
      polynomial normal forms. Rejected: memoizing the Lean normalizer (fixes
      runtime only, not the proofs) and re-witnessing partial-round words
      (changes the trace).
- [x] **Loop combinators — confirmed blocker.** `Circuit.foldl` requires
      `ConstantOutput` (`Clean/Circuit/Basic.lean:595`: output independent of
      the input). A round's output is linear in its input, so chain the 64
      rounds by explicit structural recursion over the round-constant list
      and prove soundness/completeness by induction, with each round a boxed
      `FormalCircuit (Vector field 5) (Vector field 5)` sub-circuit (outputs
      *may* depend on inputs for ordinary sub-circuits; only loops forbid it).
- [x] **Entry point.** `Permutation` is private in `ragu_primitives`; the
      public surface is `Sponge::{new, absorb, squeeze, save_state, resume}`.
      Fingerprint sponge-level shapes (no Rust API change) and keep the bare
      permutation as a Lean sub-circuit with its own theorem — mirrors Rust
      delegation. `poseidon_sponge.rs` already drives absorb-`N` + squeeze.
- [ ] **Build-time budget.** Prototype `Sbox` + one full round + one partial
      round as boxed sub-circuits and time `lake build`; extrapolate to 64
      rounds before committing (heartbeat timeouts = design signal: add
      `@[irreducible]` seals / explicit outputs, not budget).

### 2b. Parameters

- [x] Round constants (64 × 5) and MDS (5 × 5) for `PoseidonFp` and
      `PoseidonFq` are generated into
      `Ragu/Circuits/Poseidon/Params{Fp,Fq}.lean` by `lean_extraction --
      export` (`generated_poseidon_params` in `main.rs`) and verified by `--
      check`, alongside the two registry files. Elaborates in ~2 s.

### 2c. Lean circuits (`Ragu/Circuits/Poseidon/`)

- [ ] `Sbox.lean`: `x ↦ x⁵` as `Mul ⟨x,x⟩; Mul ⟨x²,x²⟩; Mul ⟨x⁴,x⟩` (order must
      match `poseidon.rs::sbox`: `square`, `square`, `mul(x)`). Spec
      `out = x^5`.
- [ ] `Round.lean`: add round constants → S-box on the first `elems` state
      words (`elems ∈ {5, 1}`) → MDS. Parametric in the round's constants.
- [ ] `Permutation.lean`: 4 full / 56 partial / 4 full rounds, spec = pure
      Lean `poseidon : Vector (F p) 5 → Vector (F p) 5` defined from the same
      parameters. Soundness/completeness by induction on rounds.
- [ ] `Sponge.lean`: absorb-then-squeeze shapes. `Sponge::new` starts from
      all-zero state; `absorb` adds into `state[i]` for the i-th pending
      value; `squeeze` permutes and returns `state[0]` (`get_rate` reverses
      the rate, `pop` takes the last). Spec `out = (poseidon (pad xs))[0]`.
- [ ] Decide which sponge shapes to fingerprint: absorb `k ∈ {1, 4}` +
      squeeze 1 (one permutation); absorb 5 + squeeze (two permutations);
      squeeze 2 (`values.pop` without a new permutation); absorb after
      squeeze (mode switch). The transcript (`ragu_pcd/internal/transcript.rs`)
      and `outer_error.rs` are the production users — match their shapes.
- [ ] `save_state` / `resume` round trip as an instance (state in = 5 wires,
      state out = 5 wires) if a bare-permutation-like statement is wanted.

### 2d. Instances and wiring

- [ ] Rust `instances/poseidon_sponge.rs` (+ Fq variant: `Sponge` is generic
      over the field, so drive both `PoseidonFp` and `PoseidonFq`).
- [ ] Lean `Ragu/Instances/Poseidon/*.lean`, register, export, build,
      fingerprint match.
- [ ] `#print axioms` on the permutation theorems; record anything beyond
      `p_prime`/`q_prime` in `book/src/fv/circuits/assumptions.md`.

## 3. Parametric gadgets — extra production-shape instances (cheap, proofs already exist)

- [x] `Element::fold` at **N = 19** (`NumGroups`, outer layer of
      `fold_two_layer`); the `element_fold.rs` comment already promised it.
- [ ] `NonzeroBank::scope` at **K = 4** (max inputs per `EndoscalingStep`,
      `ragu_pcd/internal/endoscalar.rs:311`) — currently only K = 2.
- [ ] `Element::enforce_root_of_unity` at the production `log2_circuits`
      values (`hashes_1.rs:225`) — currently k = 2 and 5; confirm which k the
      registry actually uses.
- [ ] `Point::{double, add_incomplete, double_and_add_incomplete,
      conditional_endo, conditional_negate}` on the **Fq / Eq** curve —
      currently only `EpAffine` over `Fp`; `Point::alloc` already has both.
- [ ] `Endoscalar::{alloc, extract, group_scale, lift}` over the other field
      if `compute_v`'s nested counterpart runs them there.

## 4. Constraint-free gadgets — optional output-pinning instances

No constraints, so no soundness content; an instance would only pin the
emitted output expression (e.g. that `multipack` really emits `Σ 2ⁱ·bᵢ`).
Low priority; do only if the gallery should be exhaustive.

- [ ] `Boolean::multipack` (`boolean.rs:274`)
- [ ] `Element::sum` / `multiadd`
- [ ] `Boolean::not`, `Point::{endo, negate}`

## 5. Docs

- [ ] `book/src/fv/index.md` "What is verified today": count says 31, the
      registry has 32 (`Endoscalar/Extract` was added after the prose); update
      the count and add Poseidon/Horner to the bullet list when they land.
- [ ] `book/src/fv/circuits/assumptions.md`: any new axioms or preconditions
      (e.g. Poseidon parameter provenance).
- [x] `qa/lean/extraction/src/instances/element_fold.rs` comment: the
      "See N7/N19" reference is now accurate.

## Order of attack

1. §0 baseline → §1 Horner (validates the full loop in the worktree in an
   afternoon) → §3 extra instances (mechanical, can run while §2a spikes).
2. §2a spike → §2b params → §2c Sbox/Round → Permutation → Sponge → §2d.
3. §5 docs last, once counts are final.
