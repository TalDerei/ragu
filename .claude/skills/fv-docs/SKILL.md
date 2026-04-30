---
name: fv-docs
description: Explicitly invoked only. Authoritative reference for the Ragu formal-verification project — Clean DSL semantics (Circuit monad, Expression, Operation, ProvableType, FormalCircuit) and Ragu-side concepts (extraction driver, formal instances, input/output serialization, assumptions, CI). Routes to the live in-tree FV docs; the docs are the spec, not opinion. Pair with /fv-review for opinion / pattern-matching guidance. Invoke when the user types `/fv-docs` or asks for the canonical definition of a Clean / Ragu-FV concept.
---

# fv-docs: Ragu Formal Verification reference

The FV documentation lives in the repo. This skill is a routing layer: pick the right doc and `Read` it from the live source — don't paraphrase. The docs are authoritative; they define what `FormalCircuit`, formal instances, `ExtractionDriver`, etc. *mean*.

**Pairing.** For *definitions* → fv-docs (this skill). For *opinion / pitfalls / pattern-matching* (e.g., "should I use `FormalCircuit` or `GeneralFormalCircuit`?", "what's a clean spec style?") → `/fv-review`. Don't compete on the same question.

## Where the docs live

The docs root depends on the branch:

- **`qa/lean/docs/src/`** — `fv-organization` branch and going forward (FV docs co-located with the Lean project at `qa/lean/`).
- **`fv/docs/src/`** — `upstream/main` (as landed in [#689](https://github.com/tachyon-zcash/ragu/pull/689)), prior to the reorg.

Treat `<docs>` below as whichever of the two exists in the current checkout. If unsure, `ls qa/lean/docs/src/ 2>/dev/null || ls fv/docs/src/` resolves it.

## Topic → file (what each doc answers)

**Clean DSL:**
- `<docs>/clean/introduction.md` — what Clean is; soundness vs completeness as concepts; compositionality.
- `<docs>/clean/core/circuit.md` — the `Circuit` monad: `ℕ → α × List (Operation F)`, `bind` semantics, witness offset threading.
- `<docs>/clean/core/mul.md` — minimal worked example: a multiplication circuit walked end-to-end.
- `<docs>/clean/core/provable.md` — `TypeMap`, `ProvableType`, `ProvableStruct`; structured values vs symbolic forms; `field`, `Var`.
- `<docs>/clean/core/expression.md` — `Variable`, `Expression`, `ProverEnvironment`; how symbolic circuits are evaluated.
- `<docs>/clean/core/operations.md` — `FlatOperation` vs `Operation`; witness / assert / lookup; why operations are the ground truth.
- `<docs>/clean/core/formal.md` — the formal-circuit bundle family (`FormalCircuit`, `FormalAssertion`, `GeneralFormalCircuit`, `GeneralFormalCircuit.WithHint`); the prover/verifier precondition split (`Assumptions`, `ProverAssumptions`, `ProverSpec`, `ProverData`, `ProverHint`); structure of `main` / `Assumptions` / `Spec` / `soundness` / `completeness` fields; the formal definitions of soundness and completeness.
- `<docs>/clean/core/example.md` — full worked example tying circuit + provable + expression + formal together (`DivNonzero`).
- `<docs>/clean/core/parameters.md` — compile-time parameters as ordinary Lean function arguments; partial-application instantiation.

**Ragu FV pipeline:**
- `<docs>/ragu/introduction.md` — the two-approach analysis (high-level export vs. low-level trace); why Ragu chose the low-level export with a Lean reimplementation; the formal instance interface and its fields.
- `<docs>/ragu/extraction.md` — `ExtractionDriver`, `MaybeKind = Empty`, `ImplWire = Expr<F>`; how `alloc` / `mul` / `add` / `enforce_zero` / `constant` map to operations.
- `<docs>/ragu/input-outputs-serialization.md` — symbolic input wires, `input_var.get i`, `alloc_input_wires`, `serializeOutput` / `deserializeInput`.
- `<docs>/ragu/assumptions.md` — what the FV does and does not guarantee; trusted core; axiom dependencies (`propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, `Lean.trustCompiler`, `Ragu.Core.Primes.p_prime`).
- `<docs>/ragu/ci.md` — `cargo run -p lean_extraction -- check`, `lean-action` build, `--wfail` (sorry-as-failure); only files imported by `qa/lean/Ragu.lean` are checked.

The mdBook TOC lives at `<docs>/SUMMARY.md` if you want the canonical reading order.

## Term → file (use for definition lookups)

| Term | Defined in |
|---|---|
| `Circuit` (monad), `bind`, witness offset | `clean/core/circuit.md` |
| `Variable`, `Expression`, `ProverEnvironment` | `clean/core/expression.md` |
| `Operation`, `FlatOperation`, `witness`, `assert`, `lookup` | `clean/core/operations.md` |
| `TypeMap`, `ProvableType`, `ProvableStruct`, `field`, `Var` | `clean/core/provable.md` |
| `FormalCircuit`, `FormalAssertion`, `GeneralFormalCircuit`, `GeneralFormalCircuit.WithHint`, `.toWithHint`, `Assumptions`, `ProverAssumptions`, `Spec`, `ProverSpec`, `ProverData`, `ProverHint`, soundness, completeness (formal definitions) | `clean/core/formal.md` |
| Compile-time parameters, partial-application instantiation | `clean/core/parameters.md` |
| `FormalInstance`, `reimplementation`, `same_constraints`, `same_output`, `exportedOperations`, `exportedOutput` | `ragu/introduction.md` |
| `ExtractionDriver`, `MaybeKind`, `ImplWire`, driver-method → op-trace mapping | `ragu/extraction.md` |
| `input_var.get`, `alloc_input_wires`, `serializeOutput`, `deserializeInput` | `ragu/input-outputs-serialization.md` |
| Trust assumptions, axiom dependencies | `ragu/assumptions.md` |
| `--wfail`, `lean_extraction -- check`, what CI verifies | `ragu/ci.md` |

## Reading order (for new readers)

`clean/introduction` → `clean/core/circuit` → `clean/core/provable` → `clean/core/expression` → `clean/core/operations` → `clean/core/formal` → `clean/core/mul` → `clean/core/example` → `clean/core/parameters` → `ragu/introduction` → `ragu/extraction` → `ragu/input-outputs-serialization` → `ragu/assumptions` → `ragu/ci`.

## Out of scope

- Lean syntax basics, tactic strategy, mathlib usage — not in this corpus; consult Lean / mathlib docs.
- Specific gadget proof bodies (e.g., the body of `Point.AddIncomplete.soundness`) — read source under `qa/lean/Ragu/Circuits/...`.
- Opinion on circuit-type choice, naming conventions, spec style, "did the spec lift to high-level operations" — that's `/fv-review`.

## Routing rule of thumb

1. If the question names a term from the **Term → file** table → `Read` that file from the live `<docs>` root.
2. If the question matches a topic but no specific term → consult **Topic → file** for the right doc.
3. If neither matches → the answer probably isn't in this corpus; say so rather than guess.
