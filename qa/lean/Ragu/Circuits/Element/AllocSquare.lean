import Clean.Circuit
import Ragu.Circuits.Core.AllocMul

namespace Ragu.Circuits.Element.AllocSquare
variable {p : ℕ} [Fact p.Prime]

structure Square (F : Type) where
  a : F
  a_sq : F
deriving ProvableStruct

def main (hintReader : ProverHint (F p) → F p) (_input : Unit) :
    Circuit (F p) (Var Square (F p)) := do
  let ⟨x, y, z⟩ ← Core.AllocMul.circuit
    (fun hint =>
      let a := hintReader hint
      ⟨a, a, a * a⟩) ()
  assertZero (x - y)
  return ⟨x, z⟩

def Assumptions (_input : Unit) (_data : ProverData (F p)) (_hint : ProverHint (F p)) := True

def Spec (_input : Unit) (out : Square (F p)) (_data : ProverData (F p)) :=
  out.a_sq = out.a^2

def CompletenessSpec (hintReader : ProverHint (F p) → F p)
    (_input : Unit) (out : Square (F p)) (hint : ProverHint (F p)) :=
  let a := hintReader hint
  out.a = a ∧ out.a_sq = a^2

instance elaborated (hintReader : ProverHint (F p) → F p) :
    ElaboratedCircuit (F p) unit Square where
  main := main hintReader
  localLength _ := 3

theorem soundness (hintReader : ProverHint (F p) → F p) :
    GeneralFormalCircuit.Soundness (F p) (elaborated hintReader) Spec := by
  circuit_proof_start [Core.AllocMul.circuit, Core.AllocMul.Spec]
  obtain ⟨h_mul, h_eq⟩ := h_holds
  -- h_mul : x * y = z, h_eq : x - y = 0
  rw [add_neg_eq_zero] at h_eq
  -- Goal: z = x^2
  rw [← h_mul, h_eq]; ring

theorem completeness (hintReader : ProverHint (F p) → F p) :
    GeneralFormalCircuit.Completeness (F p) (elaborated hintReader)
      Assumptions := by
  circuit_proof_start [
    Core.AllocMul.circuit, Core.AllocMul.Assumptions,
    Core.AllocMul.CompletenessSpec
  ]
  obtain ⟨_, hx, hy, _⟩ := h_env
  -- hx : x = a, hy : y = a → x - y = 0
  rw [hx, hy]; ring

theorem completenessSpec (hintReader : ProverHint (F p) → F p) :
    GeneralFormalCircuit.CompletenessSpecProof (F p) (elaborated hintReader)
      Assumptions (CompletenessSpec hintReader) := by
  circuit_proof_start [CompletenessSpec,
    Core.AllocMul.circuit, Core.AllocMul.Assumptions,
    Core.AllocMul.CompletenessSpec
  ]
  obtain ⟨_, hx, _, hz⟩ := h_env
  -- hx : x = a, hz : z = a * a
  refine ⟨hx, ?_⟩
  rw [hz]; ring

def circuit (hintReader : ProverHint (F p) → F p) :
    GeneralFormalCircuit (F p) unit Square :=
  { elaborated hintReader with
    Assumptions := Assumptions,
    Spec,
    CompletenessSpec := CompletenessSpec hintReader,
    soundness := soundness hintReader,
    completeness := completeness hintReader,
    completenessSpec := completenessSpec hintReader }

end Ragu.Circuits.Element.AllocSquare
