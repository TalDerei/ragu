import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.AllocSquare
variable {p : ℕ} [Fact p.Prime]

structure Square (F : Type) where
  a : F
  a_sq : F
deriving ProvableStruct

def main (hint : ProverEnvironment (F p) → F p) :
    Circuit (F p) (Var Square (F p)) := do
  let ⟨x, y, z⟩ ← Core.AllocMul.circuit
    (fun env =>
      let a := hint env
      ⟨a, a, a * a⟩)
  assertZero (x - y)
  return ⟨x, z⟩

def Assumptions (_input : Unit) (_data : ProverData (F p)) := True

def ProverAssumptions (_input : F p) (_data : ProverData (F p)) (_hint : ProverHint (F p)) := True

def Spec (_input : Unit) (out : Square (F p)) (_data : ProverData (F p)) :=
  out.a_sq = out.a^2

def ProverSpec (input : F p) (out : Square (F p)) (_hint : ProverHint (F p)) :=
  out.a = input ∧ out.a_sq = input^2

instance elaborated :
    ElaboratedCircuit (F p) (Unconstrained (F p)) Square where
  main
  localLength _ := 3

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [Core.AllocMul.circuit, Core.AllocMul.Spec]
  obtain ⟨h_mul, h_eq⟩ := h_holds
  -- h_mul : x * y = z, h_eq : x - y = 0
  rw [add_neg_eq_zero] at h_eq
  -- Goal: z = x^2
  rw [← h_mul, h_eq]; ring

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness (F p) elaborated
      ProverAssumptions ProverSpec := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.ProverSpec
  ]
  obtain ⟨_, hx, hy, hz⟩ := h_env
  constructor
  · -- hx : x = a, hy : y = a → x - y = 0
    rw [hx, hy]; ring
  · -- hx : x = a, hz : z = a * a
    refine ⟨hx, ?_⟩
    rw [hz]; ring

def circuit : GeneralFormalCircuit.WithHint (F p) (Unconstrained (F p)) Square :=
  { elaborated with
    Assumptions := Assumptions,
    Spec,
    ProverAssumptions := ProverAssumptions,
    ProverSpec := ProverSpec,
    soundness := soundness,
    completeness := completeness }

end Ragu.Circuits.Element.AllocSquare
