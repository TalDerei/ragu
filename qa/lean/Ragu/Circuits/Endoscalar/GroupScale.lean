import Clean.Circuit
import Clean.Circuit.Loops
import Clean.Gadgets.Boolean
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Point.AddIncomplete
import Ragu.Circuits.Point.ConditionalEndo
import Ragu.Circuits.Point.ConditionalNegate
import Ragu.Circuits.Point.Double
import Ragu.Circuits.Point.DoubleAndAddIncomplete
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Endoscalar.GroupScale
variable {p : ℕ} [Fact p.Prime] [NeZero (2 : F p)]

/-- `Endoscalar::group_scale(p)` scales a curve point `p` by the 128-bit
endoscalar's bits. Implements Algorithm 1 from BGH19 (the Halo paper). Mirrors
`crates/ragu_primitives/src/endoscalar.rs::Endoscalar::group_scale`.

Init: `acc₀ = (p.endo() + p).double()` — i.e., `acc₀ = [2]·(ζ·p + p)`.
Loop (64 iters): each step takes a 2-bit pair `(n, e)`, builds
`s = (e=1 ? ζ·p.x : p.x, n=1 ? -p.y : p.y)`, then updates
`acc' = [2]·acc + s` via `double_and_add_incomplete`.

Non-degeneracy (post-PR-741 NonzeroBank architecture): each
`add_incomplete` / `double_and_add_incomplete` call runs inside its own
`NonzeroBank::scope`, folding every denominator into a running product and
discharging `product ≠ 0` via a trailing `enforce_nonzero` — so the
constraints themselves force the distinct-x conditions; no conditional spec
or threaded nonzero wire. The sub-gadget `Inputs` carry an
`UnconstrainedDep field` inverse hint for the prover-side discharge; this
reimpl passes a default closure (`fun _ => 0`) since hints don't affect the
verifier-side constraint trace. The extraction mirrors this by wrapping each
call in `NonzeroBank::scope`. -/
structure Input (F : Type) where
  bits : Vector F 128
  pt : Point.Spec.Point F
deriving ProvableStruct

/-- One native step: given current acc and (n, e), compute `acc' = 2·acc + s`
where `s = (e=1 ? ζ·p.x : p.x, n=1 ? -p.y : p.y)`. Returns `none` if either
intermediate `add_incomplete` fails. -/
def stepNative (curveParams : Point.Spec.CurveParams p)
    (pt acc : Point.Spec.Point (F p)) (n e : F p) : Option (Point.Spec.Point (F p)) :=
  let s : Point.Spec.Point (F p) :=
    ⟨if e = 1 then curveParams.ζ * pt.x else pt.x,
     if n = 1 then -pt.y else pt.y⟩
  match acc.add_incomplete s with
  | none => none
  | some r => r.add_incomplete acc

/-- Initial accumulator: `(p.endo + p).double`. -/
def initAcc (curveParams : Point.Spec.CurveParams p) (pt : Point.Spec.Point (F p))
    : Option (Point.Spec.Point (F p)) :=
  match (pt.endo curveParams).add_incomplete pt with
  | none => none
  | some pre => pre.double

/-- Accumulator after `m` iterations of the loop, starting from `initAcc`. -/
def accAfter (curveParams : Point.Spec.CurveParams p)
    (pt : Point.Spec.Point (F p)) (bits : Vector (F p) 128) : ℕ → Option (Point.Spec.Point (F p))
  | 0 => initAcc curveParams pt
  | m + 1 =>
    match accAfter curveParams pt bits m with
    | none => none
    | some acc =>
      if h : 2 * m + 1 < 128 then
        stepNative curveParams pt acc
          (bits[2 * m]'(by omega)) (bits[2 * m + 1]'h)
      else
        none

/-- Native group-scaling result: `acc₆₄`. -/
def groupScaleNative (curveParams : Point.Spec.CurveParams p)
    (pt : Point.Spec.Point (F p)) (bits : Vector (F p) 128) : Option (Point.Spec.Point (F p)) :=
  accAfter curveParams pt bits 64

/-- The body of the in-circuit loop. Each iteration freshens both output
coordinates via `Element.Mul.circuit ⟨_, 1⟩` to break the exponential growth
of the symbolic accumulator's Expression tree across iterations. Post-PR-741:
DAA now takes an `inverse` prover hint (the bank's running product inverse). -/
def loopBody (curveParams : Point.Spec.CurveParams p) (input : Var Input (F p))
    (acc : Var Point.Spec.Point (F p)) (i : Fin 64)
    : Circuit (F p) (Var Point.Spec.Point (F p)) := do
  let n := input.bits[2 * i.val]'(by have := i.isLt; omega)
  let e := input.bits[2 * i.val + 1]'(by have := i.isLt; omega)
  let s_neg ← Point.ConditionalNegate.circuit ⟨n, input.pt.x, input.pt.y⟩
  let s ← Point.ConditionalEndo.circuit curveParams ⟨e, s_neg.x, s_neg.y⟩
  -- DAA's new shape: { P1, P2, inverse } where inverse is UnconstrainedDep
  -- field F (prover-only hint for the bank discharge). Under extraction
  -- (MaybeKind = Empty) we provide a default closure.
  let acc_sym ← Point.DoubleAndAddIncomplete.circuit curveParams
    ⟨acc, s, fun _ => 0⟩
  let fresh_x ← Element.Mul.circuit ⟨acc_sym.x, 1⟩
  let fresh_y ← Element.Mul.circuit ⟨acc_sym.y, 1⟩
  return ⟨fresh_x, fresh_y⟩

@[irreducible]
def main (curveParams : Point.Spec.CurveParams p) (input : Var Input (F p))
    : Circuit (F p) (Var Point.Spec.Point (F p)) := do
  -- p_endo = (ζ·p.x, p.y) — pure scale, no constraints.
  let p_endo : Var Point.Spec.Point (F p) := ⟨curveParams.ζ * input.pt.x, input.pt.y⟩
  -- acc_pre = p_endo + p (new AddIncomplete shape: { P1, P2, inverse }, output
  -- is just Spec.Point now, no .P3 field). Inverse hint defaulted.
  let acc_pre ← Point.AddIncomplete.circuit curveParams
    ⟨p_endo, input.pt, fun _ => 0⟩
  -- acc₀ = acc_pre.double()
  let acc_0 ← Point.Double.circuit curveParams acc_pre
  -- 64 iterations. We bypass `Circuit.foldl/foldlRange` (whose
  -- `ConstantOutput`/`ConstantLength` default tactics blow up on this
  -- 5-subcircuit body) by using `Vector.foldlM` directly.
  (Vector.finRange 64).foldlM (fun acc i => loopBody curveParams input acc i) acc_0

def Assumptions (curveParams : Point.Spec.CurveParams p) (input : Input (F p)) :=
  input.pt.isOnCurve curveParams ∧
  curveParams.noOrderTwoPoints ∧
  (∀ i : Fin 128, IsBool input.bits[i]) ∧
  input.pt.x ≠ 0 ∧
  curveParams.ζ ≠ 1 ∧
  groupScaleNative curveParams input.pt input.bits ≠ none

def Spec (curveParams : Point.Spec.CurveParams p) (input : Input (F p))
    (output : Point.Spec.Point (F p)) :=
  groupScaleNative curveParams input.pt input.bits = some output ∧
  output.isOnCurve curveParams

set_option maxHeartbeats 1000000000 in
instance elaborated (curveParams : Point.Spec.CurveParams p)
    : ElaboratedCircuit (F p) Input Point.Spec.Point where
  main := main curveParams
  -- 15 (AddIncomplete, new shape) + 12 (Double) + 64 × (3 + 3 + 24 + 3 + 3)
  --   = 27 + 64·36 = 2331
  localLength _ := 15 + 12 + 64 * 36
  -- `main` is `@[irreducible]` so the auto-`rfl` for `output_eq` works.
  -- `localLength_eq` and `subcircuitsConsistent` need explicit induction
  -- through the `Vector.foldlM` of `loopBody`.
  localLength_eq input offset := by
    show (main curveParams input).localLength offset = 15 + 12 + 64 * 36
    unfold main
    simp only [Circuit.bind_localLength_eq]
    have h_add : ∀ x n, (Point.AddIncomplete.circuit curveParams x).localLength n = 15 := by
      intro x n; rfl
    have h_dbl : ∀ x n, (Point.Double.circuit curveParams x).localLength n = 12 := by
      intro x n; rfl
    rw [h_add, h_dbl]
    letI constant : Circuit.ConstantLength
        (fun (t : Var Point.Spec.Point (F p) × Fin 64) =>
          loopBody curveParams input t.1 t.2) := {
      localLength := 36,
      localLength_eq := by
        intro ⟨acc, i⟩ k
        show (loopBody curveParams input acc i).localLength k = 36
        unfold loopBody
        simp only [circuit_norm,
          Point.ConditionalNegate.circuit, Point.ConditionalEndo.circuit,
          Point.DoubleAndAddIncomplete.circuit, Element.Mul.circuit]
    }
    rw [Circuit.FoldlM.localLength_eq]
    rfl
  -- The direct proof attempt (unfold main; bind_forAll split; per-iteration
  -- FoldlM.forAll_iff) runs away under the large heartbeat budget — the
  -- `simp only [..., Circuit.bind_forAll]` over the unfolded 64-iteration
  -- foldlM grinds for 30+ minutes without converging. Sorry'd so the build
  -- fails fast; revisit after the Step-bundle refactor shrinks the body to a
  -- single subcircuit call.
  subcircuitsConsistent _ _ := by sorry

/-! ## Native helpers for the prover-side (completeness) non-degeneracy chain.

Post-PR-741 the sub-gadget specs are unconditional, so *soundness* no longer
needs these: the constraints force the distinct-x conditions and
`groupScaleNative = some output` falls out of the per-step specs.
*Completeness* still extracts each iteration's non-degeneracy from the single
`groupScaleNative ≠ none` premise via these lemmas. -/

/-- `accAfter` is `none` from m onward, once it's `none` at some step ≤ m. -/
private lemma accAfter_none_persists (curveParams : Point.Spec.CurveParams p)
    (pt : Point.Spec.Point (F p)) (bits : Vector (F p) 128) :
    ∀ k m, k ≤ m → accAfter curveParams pt bits k = none →
      accAfter curveParams pt bits m = none := by
  intro k m hkm h_none
  induction m with
  | zero =>
    interval_cases k; exact h_none
  | succ m ih =>
    by_cases hkm' : k ≤ m
    · simp only [accAfter, ih hkm']
    · have : k = m + 1 := by omega
      rw [this] at h_none; exact h_none

/-- If `accAfter ... (m+1) ≠ none`, then `accAfter ... m ≠ none`. -/
private lemma accAfter_ne_succ_imp (curveParams : Point.Spec.CurveParams p)
    (pt : Point.Spec.Point (F p)) (bits : Vector (F p) 128) (m : ℕ)
    (h : accAfter curveParams pt bits (m + 1) ≠ none) :
    accAfter curveParams pt bits m ≠ none := by
  intro hm
  apply h
  simp only [accAfter, hm]

/-- If `groupScaleNative ≠ none`, every `accAfter m` for `m ≤ 64` is `≠ none`. -/
private lemma all_accAfter_ne (curveParams : Point.Spec.CurveParams p)
    (pt : Point.Spec.Point (F p)) (bits : Vector (F p) 128)
    (h : groupScaleNative curveParams pt bits ≠ none) :
    ∀ m ≤ 64, accAfter curveParams pt bits m ≠ none := by
  intro m hm hm_none
  apply h
  exact accAfter_none_persists curveParams pt bits m 64 hm hm_none

/-! ## Soundness and completeness. -/

set_option maxHeartbeats 8000000 in
theorem soundness (curveParams : Point.Spec.CurveParams p)
    : Soundness (F p) (elaborated curveParams)
        (Assumptions curveParams) (Spec curveParams) := by
  -- Strategy (post-PR-741, unconditional sub-gadget specs):
  --   1. `circuit_proof_start [...]` populates all subcircuit specs.
  --   2. The init AddIncomplete spec directly gives
  --      `p_endo.add_incomplete pt = some acc_pre ∧ acc_pre.isOnCurve`
  --      (unconditional — the bank discharge inside the sub-gadget forces
  --      `p_endo.x ≠ pt.x` at the constraint level); Double's spec gives
  --      `acc_pre.double = some acc_0 ∧ ...`.
  --   3. Generalized inductive invariant `∀ m ≤ 64`: the symbolic
  --      accumulator at iteration m evaluates to the (unique) point with
  --      `accAfter m = some it`. Each step composes DAA's unconditional
  --      `∃ r, acc.add s = some r ∧ r.add acc = some out ∧ out.isOnCurve`
  --      plus the two trivial `Element.Mul ⟨_, 1⟩` freshenings.
  --   4. Specialize at m = 64. Note: `groupScaleNative = some output` falls
  --      out of the constraints themselves — no `≠ none` premise needed.
  sorry

set_option maxHeartbeats 8000000 in
theorem completeness (curveParams : Point.Spec.CurveParams p)
    : Completeness (F p) (elaborated curveParams) (Assumptions curveParams) := by
  -- Prover side: each sub-gadget (AddIncomplete, DAA) is
  -- `GeneralFormalCircuit.WithHint` whose ProverAssumptions require curve
  -- membership plus genuine non-degeneracy (distinct x-coordinates) and a
  -- correct inverse hint for the bank discharge. These come from the native
  -- model: `groupScaleNative ≠ none` (Assumptions) unfolds per-step via the
  -- `accAfter` helpers below into each iteration's distinct-x facts; the
  -- init case needs `(ζ-1)·p.x ≠ 0` (from `h_zeta_ne_one` + `h_px_ne`).
  -- The current `fun _ => 0` placeholder hints in `main` likely make the
  -- discharge unsatisfiable prover-side — completeness may require threading
  -- real inverse hints (or restating via GeneralFormalCircuit). Resolve when
  -- this proof is attempted.
  sorry

def circuit (curveParams : Point.Spec.CurveParams p) : FormalCircuit (F p) Input Point.Spec.Point :=
  { elaborated curveParams with
    Assumptions := Assumptions curveParams
    Spec := Spec curveParams
    soundness := soundness curveParams
    completeness := completeness curveParams }

end Ragu.Circuits.Endoscalar.GroupScale
