import Clean.Circuit
import Clean.Utils.Primes
import Ragu.Circuits.Element.AllocSquare
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Element.Square
import Ragu.Circuits.Element.DivNonzero
import Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.AddIncomplete
variable {p : ℕ} [Fact p.Prime]

structure Inputs (F : Type) where
  P1 : Spec.Point F
  P2 : Spec.Point F
  nonzero : F
deriving ProvableStruct

structure Outputs (F : Type) where
  P3 : Spec.Point F
  nonzero : F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨⟨x1, y1⟩, ⟨x2, y2⟩, nonzero⟩ := input

  -- delta = (y2 - y1) / (x2 - x1)
  let tmp := x2 - x1
  let nonzero_out ← subcircuit Element.Mul.circuit ⟨nonzero, tmp⟩

  let delta ← subcircuit Element.DivNonzero.circuit ⟨y2 - y1, tmp⟩

  -- x3 = delta^2 - x1 - x2
  let ⟨delta2⟩ ← subcircuit Element.Square.circuit ⟨delta⟩
  let x3 := delta2 - x1 - x2

  -- y3 = delta * (x1 - x3) - y1
  let delta_mul_x_diff ← subcircuit Element.Mul.circuit ⟨delta, x1 - x3⟩
  let y3 := delta_mul_x_diff - y1

  return {
    P3 := ⟨x3, y3⟩,
    nonzero := nonzero_out
  }

def Assumptions (curveParams : Spec.CurveParams p) (input : Inputs (F p)) (_data : ProverData (F p)) :=
  input.P1.isOnCurve curveParams ∧ input.P2.isOnCurve curveParams ∧
  (input.P2.x - input.P1.x ≠ 0)

-- Spec is conditional on curve membership
def Spec (curveParams : Spec.CurveParams p) (input : Inputs (F p)) (output : Outputs (F p)) (_data : ProverData (F p)) :=
  let ⟨P1, P2, nonzero⟩ := input
  input.P1.isOnCurve curveParams → input.P2.isOnCurve curveParams →
  (
    -- If the x coordinates of P1 and P2 are different, then we can conclude that the
    -- addition output is affine and is the correct result of the addition
    P1.x ≠ P2.x -> (
      (
        match P1.add_incomplete P2  with
        | none => False -- this case never happens
        | some res => output.P3 = res
      )
      ∧ output.P3.isOnCurve curveParams
    )
  ) ∧
  (
    -- if the x coordinates of P1 and P2 are equal, then output nonzero is 0
    -- regardless of the input nonzero
    (P1.x = P2.x -> output.nonzero = 0) ∧

    -- if the x coordinates of P1 and P2 are not equal, then output nonzero preserves
    -- non-zero-ness from input nonzero
    (P1.x ≠ P2.x ->
      (nonzero = 0 -> output.nonzero = 0) ∧
      (nonzero ≠ 0 -> output.nonzero ≠ 0)
    )
  )

instance elaborated : ElaboratedCircuit (F p) Inputs Outputs where
  main
  localLength _ := 12

theorem soundness (curveParams : Spec.CurveParams p) : GeneralFormalCircuit.Soundness (F p) elaborated (Spec curveParams) := by
  circuit_proof_start
  simp [circuit_norm,
    Element.Square.circuit, Element.Square.Assumptions, Element.Square.Spec,
    Element.DivNonzero.circuit, Element.DivNonzero.Assumptions, Element.DivNonzero.Spec,
    Element.Mul.circuit, Element.Mul.Assumptions, Element.Mul.Spec
  ] at h_holds ⊢

  obtain ⟨c1, c2, c3, c4⟩ := h_holds

  intro h_P1_mem h_P2_mem
  rw [add_neg_eq_zero] at c2

  constructor
  · intro h
    have h_neq : ¬input_P2_x = input_P1_x := Ne.symm h
    specialize c2 h_neq
    rw [c2, c3, c2] at c4
    rw [c2] at c3
    rw [c4, c3]
    clear c1 c2 c3 c4
    simp [Spec.Point.add_incomplete, h]

    let h_lemma := Lemmas.add_incomplete_preserves_membership ⟨input_P1_x, input_P1_y⟩ ⟨input_P2_x, input_P2_y⟩ curveParams
    simp [Spec.Point.add_incomplete, h] at h_lemma
    specialize h_lemma h_P1_mem h_P2_mem
    ring_nf at ⊢ h_lemma
    simp_all only [id_eq, inv_pow, and_self]

  · simp_all only [id_eq, add_neg_cancel, mul_zero, implies_true, zero_mul, mul_eq_zero, false_or,
    true_and]
    rw [add_neg_eq_zero]
    intro h1 _
    apply Ne.symm
    exact h1

theorem completeness (curveParams : Spec.CurveParams p) : GeneralFormalCircuit.Completeness (F p) elaborated (Assumptions curveParams) := by
  circuit_proof_start [
    Element.Square.circuit, Element.Square.Assumptions,
    Element.DivNonzero.circuit, Element.DivNonzero.Assumptions,
    Element.Mul.circuit, Element.Mul.Assumptions
  ]
  obtain ⟨_, _, h_diff⟩ := h_assumptions
  -- Only non-trivial subcircuit goal: DivNonzero needs x2-x1 ≠ 0
  rw [Ne, add_neg_eq_zero]
  exact sub_ne_zero.mp h_diff

def circuit (curveParams : Spec.CurveParams p) : GeneralFormalCircuit (F p) Inputs Outputs :=
  {
    elaborated with
    Assumptions := Assumptions curveParams,
    Spec := Spec curveParams,
    soundness := soundness curveParams,
    completeness := completeness curveParams
  }

end Ragu.Circuits.Point.AddIncomplete
