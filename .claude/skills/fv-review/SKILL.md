---
name: fv-review
description: Explicitly invoked only. Lessons learned from porting Ragu Rust circuits to Clean Lean formal verification reimpls — when not to formalize an empty circuit, picking FormalCircuit vs FormalAssertion vs GeneralFormalCircuit, mirroring Rust delegation, length polymorphism, naming conventions. Distilled from PR review feedback (mitschabaude et al.) and refined over time. Do NOT auto-trigger on general formal verification, Lean, or Ragu questions; only invoke when the user explicitly types `/fv-review` or asks by name.
---

# Ragu Formal Verification: Lessons Learned

Hints for adding Clean Lean formal verification reimpls to Ragu Rust circuits. Distilled from reviewer feedback. Append new lessons as they emerge.

Sections fall into three groups: **Trust model** frames what's trusted vs untrusted and what reviewers must inspect by hand; **per-reimpl tactics** (Core principle through Watch for false justifications) covers how to write a single reimpl correctly; **workflow** (Per-gadget extension workflow + Workflow checklist) covers how to construct the artifact set across files, plus a per-reimpl quality checklist. Sources at the bottom trace each lesson to a specific PR review thread.

## Trust model

the clean reimplementation and formal instance can be black-boxed and LLM-generated since they’re untrusted. the latter (formal instance) proves that the reimpl equals the autogen using equivalence theorems, and the former (reimpl) proves the soundness / completeness against the spec (loosely an IO contract). so this transitively reduces trust to just manually inspecting that the spec is correct, and assuming the trusted extractor and serialization impl is correct, everything else follows

**Artifact map.** Spelling out trusted/untrusted by artifact:
- *Trusted (must be manually inspected):* Rust circuit instance (`CircuitInstance`), extractor / extraction driver, serialization impl, and — on the Lean side — `Inputs` / `Outputs` struct definitions, `Spec`, `Assumptions`.
- *Untrusted (can be LLM-generated):* Lean reimpl body (`main`), soundness / completeness theorems, formal-instance equivalence proofs. The autogen Lean file (flat op trace) is mechanically extractor-produced, not human-written.

**Subtlety: input/output *struct shape* is part of the trusted spec; wire *order* is not.**
- Wire ordering is checked by the equivalence proof — constraints are tied to specific wires, and both Ragu and Clean derivers map struct fields to wires in field-definition order. Reorder the wires on either side and the formal instance fails.
- The *meaning* assigned to those wires (which wire is `x` vs `y`, which input is "first") is trusted. Extraction operates on raw wires; the high-level struct shape is not preserved through it. A Rust bug — say, `assertLt(x, y)` accidentally checking `x > y` — can be **shadowed** by an inverse Lean bug: define `Inputs := { y, x }` and prove `x < y`. Variable names line up, equivalence still holds, the spec reads exactly like the intended behavior. **Reviewer obligation:** verify both that the spec captures the gadget's *intended* behavior *and* that input/output naming matches what callers actually pass.

**Mitigation: composition surfaces bad specs.** A wrong spec or wrong input order on a leaf gadget tends to surface when that gadget is used as a subcircuit in a parent — the child spec won't compose to the statement the parent needs. A second reason (beyond the proof-composability argument in "Mirror Rust delegation") to lean on subcircuit composition: it catches bugs, not just enables proofs.

## Core principle: don't formalize what has no content

A Rust "circuit" that only builds expressions (e.g., `negate`, `add`, `sub`, `double`, `scale`, `add_coeff`, `sum`, `Point::constant`) emits **no constraints and no witnesses** — it's pure expression manipulation. A Lean reimpl produces an empty body with a trivially-true spec, which proves nothing useful.

**Rule:** before writing a Lean reimpl, check whether the Rust function actually emits operations (witnesses, lookups, asserts). If not, skip it. Don't reflexively mirror every Rust helper as a trivial Lean circuit.

## Pick the right circuit type

Three flavors, in order of specificity:

| Type | Use when | Pitfall |
|---|---|---|
| `FormalCircuit` | Function-like: completeness and soundness share the same assumptions ("constraints work for all valid inputs"). | Default for input → output gadgets. **Both soundness and completeness see `Assumptions`** — so if your spec needs `IsBool input` to make sense, this is the type to reach for. |
| `FormalAssertion` | Assertion-like: constraints intentionally narrow the allowed input (e.g., `enforce_root_of_unity`, `enforce_zero`). | If you reach for `GeneralFormalCircuit` and find yourself with `Assumptions = Spec`, this is what you actually want. |
| `GeneralFormalCircuit` | Most flexible — different completeness vs. soundness assumptions. | Causes duplication when the generality isn't needed. **`Assumptions` is only consulted by completeness, not soundness** — so a spec referring to "boolean inputs" must either bake the bool constraints into the gadget body or downgrade to `FormalCircuit`. Last resort. |

**Heuristic:** `Assumptions = Spec` → `FormalAssertion`. "Function of inputs (under preconditions)" → `FormalCircuit`. Different soundness vs. completeness preconditions → `GeneralFormalCircuit`.

## Specs lift to high-level operations, not low-level constraints

**The single most repeated review note.** A spec is the contract presented to callers; it should describe *what the gadget computes*, not *what equations it emits*. If your spec reads like the constraint system, it's wrong.

**Anti-patterns and rewrites:**

| Gadget | ❌ Constraint-level spec | ✓ Operation-level spec |
|---|---|---|
| `Boolean.And` | `out = a * b ∧ (out = 0 ∨ out = 1)` | `out.val = a.val &&& b.val ∧ IsBool out` |
| `Boolean.ConditionalEnforceEqual` | `cond * (a - b) = 0` | `cond = 1 → a = b` |
| `Boolean.ConditionalSelect` | `out = a + cond * (b - a)` | `out = if cond = 1 then b else a` |
| `Multipack` | raw `field = sum of weighted bits` | `output.val` equals the bit-decomposition encoded by `input` |

The high-level form is what callers reason against. The constraint-level form is what soundness *proves* — internally, not externally.

Reusable building blocks: `IsBool x` (from `Clean.Gadgets.Boolean`) for "0 or 1"; `&&&` / `|||` for bitwise ops on `.val`; `if … then … else …` for conditional outputs; `IsBool.and_eq_val_and` / `IsBool.and_is_bool` to bridge field multiplication to boolean operations in soundness proofs.

## Assumptions encode preconditions, not constraints

`Assumptions` is the *contract the caller must satisfy*. Like `Spec`, it should be a high-level statement, not a math identity from the constraint system.

| ❌ | ✓ |
|---|---|
| `r.x + r.y = 1 ∧ r.x * r.y = 0` | `IsBool input.cond` (or `True` if the precondition is established by the *hint type itself*) |

**A spurious low-level Assumption is almost always a smell that the interface is wrong** — usually the hint type leaks an internal sub-gadget shape. Fix the interface and the bogus Assumption disappears (sometimes to `True`).

## Hint types mirror the Rust interface

If `Rust::alloc` takes `bool`, the Lean reimpl should expose that as the circuit input hint shape — *not* `Row` or any other internal sub-gadget shape.
In current Clean code this usually means an input field such as `Unconstrained Bool` or `UnconstrainedDep SomeType`.

```lean
-- Wrong: leaks the internal multiplication row to every caller
structure Input (F : Type) where
  row : UnconstrainedDep Row F

-- Right: matches Rust's `value: DriverValue<D, bool>` parameter
structure Input (F : Type) where
  value : Unconstrained Bool F
```

If a sub-gadget needs a row, *compute it inside the gadget body* from the higher-level hint:

```lean
let ⟨a, b, c⟩ ← Core.mul fun env =>
  let v : F p := if input.value env then 1 else 0
  ⟨v, 1 - v, 0⟩
```

This keeps the public interface aligned with Rust and prevents Assumption inflation (see previous section).

## Naming conventions

- **No `General*` prefix.** Use plain `circuit`, `Spec`, `Assumptions`, `soundness`, `completeness`. The prefix is noise even when the underlying type is `GeneralFormalCircuit`.
- **Drop unused template arguments.** If a parameter isn't used in a definition, don't take it as an argument at all. For unused arguments in pure props, underscore-prefix them:
  ```lean
  def Assumptions (_input : Unit) (_data : ProverData (F p)) (_hint : ProverHint (F p)) := True
  ```

## Composition: don't wrap in `subcircuit`

A `FormalCircuit` is already callable as a function via its `CoeFun` instance. Don't wrap calls:

```lean
-- Wrong
let acc ← subcircuit (Mul.circuit ⟨input.x0, input.s⟩)

-- Right
let acc ← Mul.circuit ⟨input.x0, input.s⟩
```

## Mirror Rust circuit structure in Lean

The Lean reimpl should mirror the circuit-emitting structure on the Rust side.
If Rust delegates to a sub-gadget (e.g., `Element::invert` calls `Element::invert_with`), Lean should delegate the same way.
If Rust calls the driver primitive `dr.mul()`, Lean should call `Core.mul`.

This keeps the abstraction boundary aligned across Rust and Lean and avoids duplicate proofs.

**Current pattern: use `Core.mul` for env-aware rows.** `Core.mul` takes an `UnconstrainedDep Row` input, so callers can pass a function of the prover environment and compute the row locally from `eval`ed inputs.

## Length polymorphism is supported

Clean has plenty of length-polymorphic circuits. Don't claim "Clean can't express this" as a reason to specialize.

**Pattern:** make the Lean circuit length-polymorphic naturally, even if the Rust↔Lean extraction bridge only checks one fixed length at a time. Extract several concrete instances (e.g., n = 2, 4, 8, 16) for extra confidence.

The Lean formalization should represent the Rust circuit in its **full generality**, regardless of extraction limits.

## Watch for false justifications

Reviewers flag explanatory comments that aren't actually true (literal review verdict: "lie"). If a doc comment claims "Clean doesn't support X" or "this requires dependent types we don't expose", verify against the Clean codebase before writing it — those claims tend to be wrong.

## Per-gadget extension workflow

How the artifacts fit together when adding a new gadget to FV. This is *per-gadget construction*; the **Workflow checklist** below is *per-reimpl quality gates* — different axes, both apply.

**Artifacts per top-level gadget** (e.g., `Point.AddIncomplete`):

| File | Trust | What it is |
|---|---|---|
| `qa/crates/lean_extraction/src/instances/<gadget>.rs` | trusted | Rust `CircuitInstance` impl: thin wrapper that calls Ragu types / gadgets through `ExtractionDriver`. |
| `qa/lean/Ragu/Instances/Autogen/<Module>/<Gadget>.lean` | mechanical (CI-checked) | Extractor-produced flat op trace. Regenerated via `cargo run -p lean_extraction -- export`; `check` enforces byte-equality. |
| `qa/lean/Ragu/Circuits/<Module>/<Gadget>.lean` | reimpl untrusted; `Inputs` / `Outputs` / `Spec` / `Assumptions` trusted | The reimpl: `main`, `Spec`, `Assumptions`, `elaborated`, `soundness`, `completeness`. |
| `qa/lean/Ragu/Instances/<Module>/<Gadget>.lean` | untrusted | `FormalInstance` packaging: proves reimpl ≡ autogen, exposes the spec. |
| circuit input types containing `Unconstrained` / `UnconstrainedDep` | trusted | The hint shape exposed to callers; should mirror the Rust API and avoid leaking internal rows. |

**Sub-gadget carve-out — the scaling lesson.** Gadgets used only as subcircuits inside other gadgets can live **only as Lean reimpls + soundness / completeness**. Their correctness reaches the top via composition: the parent reimpl's proof uses the child's `Spec`. Top-level gadgets — the ones a Ragu consumer composes with — get the full pipeline. Some core gates such as `Core.mul` still have extractor instances because they are useful as direct equivalence anchors, but that should be an intentional choice rather than the default for every helper.

**Canonical per-gadget commit sequence** (PR #642 followed this ~6 times):
1. Reimpl skeleton in `qa/lean/Ragu/Circuits/<Module>/<Gadget>.lean` — `main`, `Spec`, `Assumptions`, `elaborated`.
2. Rust `CircuitInstance` in `qa/crates/lean_extraction/src/instances/<gadget>.rs` (top-level only).
3. Run `cargo run -p lean_extraction -- export` → autogen file appears under `qa/lean/Ragu/Instances/Autogen/<Module>/<Gadget>.lean`.
4. Write `soundness`.
5. Write `completeness` (define honest witness gen if needed).
6. Add formal-instance packaging in `qa/lean/Ragu/Instances/<Module>/<Gadget>.lean` (top-level only).

Steps 1–2 can swap. Sub-gadgets stop after step 5.

**Framework co-evolution is part of the workflow.** Several PR #642 commits are *upstream Clean changes* pulled back into Ragu — the `ProverAssumptions` / `ProverSpec` split, hint-aware `CircuitType` inputs, the `ProverHint` / `Environment` rename, weakening `DivNonzero` assumptions. When Clean can't express what a Ragu reimpl needs — most commonly around hint shape, completeness contracts, or assumption polymorphism — **PR upstream first, bump the dep in `qa/lean/lakefile.lean`, then continue**. Don't paper over with workarounds in Ragu (bogus Assumptions, leaked sub-gadget shapes — see "Hint types mirror the Rust interface"). The positive counterpart to checklist item 11 below.

**Compositionality scales the pipeline ([PR #674](https://github.com/tachyon-zcash/ragu/pull/674#pullrequestreview-4171812720)).** As gadgets get more complex, the *single most important* discipline is delegating to existing Lean sub-gadgets instead of inlining their math. Skipping the step-1 homework — surveying what's already there before writing new `main` / `Spec` — is exactly the failure mode the PR #674 reviewer flagged ("agents missed the compositionality of clean and wrote specs that just repeat the math equations"). The lessons under "Mirror Rust delegation" and "Specs lift to high-level operations" enforce this; the per-gadget workflow only scales if those are followed religiously.

## Workflow checklist

1. **Audit the Rust circuit first** — does it emit operations? If no, skip the Lean reimpl entirely.
2. **Pick the circuit type** — `FormalCircuit` (default), `FormalAssertion` (narrowing input), `GeneralFormalCircuit` (last resort).
3. **Match the Rust hint type** — if Rust takes `bool`, Lean takes `Bool`. Don't expose internal sub-gadget shapes.
4. **Mirror Rust call structure** — delegate to the same sub-gadgets Rust delegates to; use `Core.mul` for Rust `dr.mul()` calls.
5. **Write the spec at the operation level** — boolean / Nat / `if`-`then`-`else` / "input.cond = 1 → output equals X". If your spec reads like the constraint system, rewrite it.
6. **Sanity-check `Assumptions`** — should be a high-level precondition (`IsBool x`, often `True`). A complex math identity in `Assumptions` is a smell; suspect the interface.
7. **For `GeneralFormalCircuit`, remember soundness doesn't see `Assumptions`** — if you need invariants on inputs, either bake them into the constraints or use `FormalCircuit`.
8. **Drop unused parameters**; underscore-prefix unused props arguments.
9. **Use plain names** (`circuit`, `Spec`, `soundness`) — no `General*` prefix.
10. **Run `lake build` after each commit**; audit specs for correctness.
11. **Before claiming a Clean limitation, grep the Clean codebase** — most "limits" are mistaken.

## Sources

- [tachyon-zcash/ragu#642](https://github.com/tachyon-zcash/ragu/pull/642) — clean integration foundation. Trust-model artifact map (r3102920311); input/output struct shape is part of the trusted spec, wire order is not (r3105702381, r3115790860 — `assertLt` shadowed-bug example, composition-as-mitigation side note); per-gadget extension workflow distilled from the 102-commit history (artifact set, sub-gadget carve-out per Tal's approval comment, framework co-evolution via upstream Clean PRs).
- [tachyon-zcash/ragu#672](https://github.com/tachyon-zcash/ragu/pull/672) — mitschabaude review (initial extraction)
- [tachyon-zcash/ragu#674](https://github.com/tachyon-zcash/ragu/pull/674) — mitschabaude review (Boolean gadget). Verdict: "agents missed the compositionality of clean and wrote specs that just repeat the math equations instead of translating them into higher-level programming statements." Threads: r3138867768, r3138904103, r3138963958, r3138965755, r3138972958, r3138991793, r3139002146, r3139003436, r3139007420, r3139012715.

<!-- Append new lessons below this line as they emerge from review feedback. -->
