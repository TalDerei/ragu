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
- [x] **Build-time budget.** Non-issue with the boxed design: every layer
      (`Sbox` → `Round.{Full,Partial}` → `Permutation` by induction over the
      schedule → `Sponge.Hash1`) elaborates in seconds; no heartbeat bumps,
      no `@[irreducible]` seals needed. The Lean fingerprint of a 64-round
      instance runs in well under a second thanks to `normalizeLinear`.

### 2b. Parameters

- [x] Round constants (64 × 5) and MDS (5 × 5) for `PoseidonFp` and
      `PoseidonFq` are generated into
      `Ragu/Circuits/Poseidon/Params{Fp,Fq}.lean` by `lean_extraction --
      export` (`generated_poseidon_params` in `main.rs`) and verified by `--
      check`, alongside the two registry files. Elaborates in ~2 s.

### 2c. Lean circuits (`Ragu/Circuits/Poseidon/`)

- [x] `Sbox.lean`: `x ↦ x⁵` as `Mul ⟨x,x⟩; Mul ⟨x²,x²⟩; Mul ⟨x⁴,x⟩` (order
      matches `poseidon.rs::sbox`: `square`, `square`, `mul(x)`). Spec
      `out = x^5`.
- [x] `Linear.lean`: `normalizeLinear` + unconditional `eval_normalizeLinear`
      (see §2a).
- [x] `Round.lean`: `Round.Full` / `Round.Partial` over `fields t` — add
      round constants → S-box on all words / word `0` → MDS (outputs
      normalized). Parametric in `t`, the MDS matrix and the round constants.
- [x] `Permutation.lean`: recursion over a `List RoundSpec` schedule
      (`full rc | part rc`), each round the boxed `AnyRound` sub-circuit; spec
      `out = permuteVal mds rounds state` (pure Lean round function iterated);
      soundness/completeness/`localLength`/`output`/`subcircuitsConsistent`
      all by induction on the list.
- [x] `Sponge.lean`: `schedule full part rcs` (4 full / 56 partial / 4
      full) and `Hash1 k`: absorb `k ≤ RATE` elements into the zero state,
      one permutation, output word `0`. Spec
      `out = (permuteVal mds rounds (initialStateVal xs))[0]`.
- [x] Single-block shapes fingerprinted: absorb `k ∈ {1, 4}` + squeeze 1
      over `Fp`, absorb 1 + squeeze 1 over `Fq`.
- [ ] Multi-op sponge: absorb > `RATE` (second permutation inside `absorb`),
      squeeze 2 (`values.pop` without a new permutation), squeeze > `RATE`
      (re-permute in squeeze mode), absorb after squeeze (mode switch). Plan:
      a `Sponge.Program` circuit parameterized by an op list
      (`absorb | squeeze`) that simulates `Mode`/`values`/`state` exactly
      like `poseidon.rs`, with a value-level sponge machine as spec and
      soundness by induction over the program; instances for the
      transcript's real shapes (`ragu_pcd/internal/transcript.rs`).
- [ ] `save_state` / `resume` round trip as an instance (state in = 5 wires,
      state out = 5 wires) if a bare-permutation-like statement is wanted.

### 2d. Instances and wiring

- [x] Rust `instances/poseidon_sponge.rs`: `PoseidonHash1InstanceFp`,
      `PoseidonHash4InstanceFp`, `PoseidonHash1InstanceFq`.
- [x] Lean `Ragu/Instances/Poseidon/{Hash1Fp,Hash4Fp,Hash1Fq}.lean`,
      registered, exported, built, fingerprints match (40/40).
- [x] `#print axioms`: every Poseidon theorem (`Sbox`, `Linear`, `Round`,
      `Permutation`, `Sponge.Hash1`) depends only on `propext`,
      `Classical.choice`, `Quot.sound` — not even `p_prime`, since the
      circuits are generic in `p`. Nothing new for the assumptions chapter.

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
      registry now has 40; update the count and add Poseidon/Horner to the
      bullet list.
- [ ] `book/src/fv/circuits/assumptions.md`: any new axioms or preconditions
      (e.g. Poseidon parameter provenance).
- [x] `qa/lean/extraction/src/instances/element_fold.rs` comment: the
      "See N7/N19" reference is now accurate.

## Order of attack

1. §0 baseline → §1 Horner (validates the full loop in the worktree in an
   afternoon) → §3 extra instances (mechanical, can run while §2a spikes).
2. §2a spike → §2b params → §2c Sbox/Round → Permutation → Sponge → §2d.
3. §5 docs last, once counts are final.
