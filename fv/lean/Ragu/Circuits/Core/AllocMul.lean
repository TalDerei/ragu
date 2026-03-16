import Clean.Circuit

namespace Ragu.Circuits.Core.AllocMul
variable {p : ℕ} [Fact p.Prime]

structure Row (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct

/-- Read the witness row from ProverData at the given index. -/
def readRow (data : ProverData (F p)) (idx : ℕ) : Row (F p) :=
  let v := (data "alloc_mul_w" 3).getD idx default
  ⟨v[0], v[1], v[2]⟩

def main (idx : ℕ) (_input : Unit) : Circuit (F p) (Var Row (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun env => readRow env.data idx : Circuit (F p) (Var Row (F p)))
  assertZero (x*y - z)
  return ⟨x, y, z⟩

def Assumptions (idx : ℕ) (_inputs : Unit) (data : ProverData (F p)) :=
  let w := readRow data idx
  w.x * w.y = w.z

def Spec (_inputs : Unit) (out_point : Row (F p)) (_data : ProverData (F p)) :=
  out_point.x * out_point.y = out_point.z

instance elaborated (idx : ℕ) : ElaboratedCircuit (F p) unit Row where
  main := main idx
  localLength _ := 3

theorem soundness (idx : ℕ) : GeneralFormalCircuit.Soundness (F p) (elaborated idx) Spec := by
  circuit_proof_start
  ring_nf at *
  grind

theorem completeness (idx : ℕ) : GeneralFormalCircuit.Completeness (F p) (elaborated idx) (Assumptions idx) := by
  sorry

def circuit (idx : ℕ) : GeneralFormalCircuit (F p) unit Row :=
  {
    elaborated idx with
    Assumptions := Assumptions idx,
    Spec,
    soundness := soundness idx,
    completeness := completeness idx
  }

end Ragu.Circuits.Core.AllocMul
