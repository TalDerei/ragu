# Composable gadget contracts

Ragu's Lean circuits already compose at two levels.

At the circuit level, a parent calls a packaged child such as
`Boolean.Alloc.circuit`. Clean's `CoeFun` instance routes that call through the
appropriate subcircuit constructor. The child operations are nested at the
current offset, its local wires are fresh, and its declared output expressions
are returned to the parent.

At the theorem level, the same packaged value carries `Assumptions`, `Spec`,
`soundness`, and `completeness`. `toSubcircuit` invokes those proofs. In a
parent soundness proof, the child contribution therefore has the form

```text
Child.Assumptions evaluated_input -> Child.Spec evaluated_input evaluated_output
```

and not the child's raw gate equations. The parent must establish the premise
and may then use the postcondition.

The complete call path is:

```text
Parent.main
  -> Child.circuit input
  -> CoeFun / subcircuitWithHintAssertion (or the matching pure/assertion form)
  -> Child.circuit.toSubcircuit
  -> Child.circuit.soundness and Child.circuit.completeness
  -> a nested Subcircuit carrying the child assumptions and specification
```

`circuit_proof_start [Child.circuit, Child.Assumptions, Child.Spec]` normalizes
that packaged boundary so the parent can use it. Mentioning `Child.circuit`
there exposes the record interface; it does not ask the parent to prove the
child's operation trace again.

## Contract surface

The composition checks cover every circuit builder under
`qa/fv/Ragu/Circuits`, including recursive and loop helpers rather than only
simple functions named `main`.

| Wrapper | Count |
| --- | ---: |
| `FormalCircuit` | 25 |
| `FormalAssertion` | 6 |
| `GeneralFormalCircuit` | 4 |
| `GeneralFormalCircuit.WithHint` | 14 |
| **Packaged contracts** | **49** |

Those contracts are distributed as follows:

- Boolean (6): `Alloc`, `And`, `ConditionalEnforceEqual`,
  `ConditionalSelect`, `Consistent`, and `Decompose`.
- Core and element (18): `Core.Mul` plus all 17 element contracts.
- Endoscalar, Horner, and nonzero bank (7): `Endoscalar.Alloc`, `Extract`,
  `GroupScale.Step`, `GroupScale`, `Lift`, `Horner.Ky`, and
  `NonzeroBank.Scope`.
- Point (9): allocation, consistency, conditional endomorphism/negation,
  addition, doubling, and checked/unchecked double-and-add variants.
- Poseidon (9): `Sbox`, both round kinds, `AnyRound`, `Permutation`, `Hash1`,
  `Blocks`, `Squeeze`, and `Ragged`.

There are 49 `soundness` and 49 `completeness` endpoints. Poseidon's internal
`Blocks.loop_soundness` and `Blocks.loop_completeness` bring the pinned theorem
total to 100. Every one is directly pinned in `Ragu.Meta.TrustBoundary`.

The builders contain 49 packaged `main` definitions and one additional
proof-carrying helper, `Poseidon.Sponge.Blocks.loop`. The composition check
pins those counts so adding or removing a builder requires an explicit review
and count update.

## Direct composition edges

The parent-to-child edges are:

- Boolean: `Alloc`, `And`, and `ConditionalEnforceEqual` use `Core.mul`;
  `ConditionalSelect` uses `Element.Mul`; `Consistent` and `Decompose` use
  `Boolean.Alloc`.
- Element: allocation, multiplication, division, inversion, and zero tests use
  `Core.mul` at the leaf. Composite contracts use `EnforceNonzero` plus
  `Divide`, `Invertible`, `InvertWith`, `IsZero`, or repeated `Mul` calls as
  appropriate.
- Endoscalar: `Alloc` repeats `Boolean.Alloc`; `Extract` uses
  `Boolean.Decompose`; `Lift` repeats `Boolean.And`; `GroupScale.Step` composes
  conditional point operations with unchecked double-and-add; and
  `GroupScale` composes initial point addition/doubling with 64 `Step` calls.
- Horner and nonzero bank: `Horner.Ky` uses `Element.Fold`; the bank scope folds
  with `Element.Mul` and discharges with `Element.EnforceNonzero`.
- Point: the formulas compose `Element.Divide`, `Square`, `Mul`, and, in the
  checked variants, `EnforceNonzero`; conditional operations use
  `Boolean.ConditionalSelect`; `Consistent` uses `Point.Alloc`.
- Poseidon: `Sbox` uses three `Element.Mul` calls; rounds use `Sbox`;
  `AnyRound` dispatches to a round contract; `Permutation` recursively chains
  `AnyRound`; `Blocks.loop` chains `Permutation`; and the sponge entry points
  compose `Blocks` and/or `Permutation`.

No parent circuit builder or soundness proof calls a child's qualified `main`.
`Endoscalar.Lift.soundness` names `Boolean.And.output`, the child's stable
output/layout accessor, while deriving its meaning from `Boolean.And.Spec`.

## Assumption discharge

Most child verifier assumptions are `True`. The nontrivial paths are:

| Child obligation | How callers discharge it |
| --- | --- |
| Boolean inputs are `IsBool` | Passed from the parent contract (`ConditionalSelect`, conditional point operations, `Lift`, and group-scale steps). |
| `Element.Divide`: `y != 0` or `x != 0` | `DivNonzero` obtains `y != 0` from `EnforceNonzero`; checked point gadgets obtain it from the bank discharge; unchecked point gadgets require the relevant non-degeneracy in their own assumptions. |
| Point inputs lie on the curve | Passed from the parent assumption or established by a prior point child spec. |
| Point doubling has no order-two input | Derived from `curveParams.noOrderTwoPoints`, giving the nonzero denominator. |
| An unchecked double-and-add chain succeeds | `GroupScale.Step` derives the two successful additions from `stepNative != none`. |
| Every group-scale step succeeds | `GroupScale` threads `groupScaleNative != none` through the 64-step invariant. |

Two caller-visible residual assumptions remain deliberate:

- `Point.Consistent` receives `curveParams.nonzeroCoordinates` externally.
- `Endoscalar.GroupScale` receives `groupScaleNative != none`, representing the
  no-collision/non-degeneracy argument in
  (Bowe–Grigg–Hopwood, <a href="https://eprint.iacr.org/2019/1021">Recursive
  Proof Composition without a Trusted Setup</a>, Appendix C). The deployed
  recursion model must establish that premise from its own context; this gadget
  proof does not manufacture it.

Verifier and prover contracts remain distinct. For example,
`Element.Alloc.Spec` is intentionally `True` because an arbitrary fresh
allocation has no verifier-visible relationship to its private hint;
`ProverSpec` records the honest-witness relationship. Similar hint obligations
belong only to completeness.

## Robustness and enforcement

Three checks enforce this boundary:

1. `Ragu.Meta.Tests.ContractComposition` checks that a child postcondition
   cannot be consumed before its assumptions are supplied.
2. `scripts/check_fv_contract_composition.sh` strips Lean comments and rejects
   qualified `.main` references anywhere in the circuit modules. CI runs this
   before the Lean build.
3. `Ragu.Meta.ContractCompositionCheck` scans the elaborated environment for
   every definition whose final result is `Circuit`, pins all 50 builders, and
   rejects direct semantic references to a different circuit's `main` or to
   the raw `FormalCircuitBase.main` projection.

The lint is an accidental-drift guard, not a parser-level security boundary.
Lean type checking and Clean's subcircuit definitions are the semantic check.

## What this does not prove

Composable contracts prove the meaning of the Lean circuit hierarchy. They do
not by themselves show that a Rust implementation has the same trace, or that
an isolated gadget has the deployed composed circuit's system gates, allocator
context, routine placement, final layout, wiring, or verifier acceptance
behavior. Those are separate Rust-to-Lean binding and deployment-layer checks,
tracked in [#865](https://github.com/tachyon-zcash/ragu/issues/865).

Layout proofs such as `localLength_eq`, `output_eq`, and
`subcircuitsConsistent` are also expected to depend on child layout metadata.
That is circuit composition, not a leak of the child's semantic proof. The
modularity claim is specifically that a parent derives child meaning from the
child contract rather than re-proving the child's raw constraints.
