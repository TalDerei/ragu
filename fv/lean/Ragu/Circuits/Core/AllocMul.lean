import Clean.Circuit

namespace Ragu.Circuits.Core.AllocMul
variable {p : ℕ} [Fact p.Prime]

structure Row (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct


def main (_input : Unit) : Circuit (F p) (Var Row (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun _env => default : Circuit (F p) (Var Row (F p)))
  assertZero (x*y - z)
  return ⟨x, y, z⟩

def Assumptions (_inputs : Unit) := True

def Spec (_inputsinputs : Unit) (out_point : Row (F p)) :=
  out_point.x * out_point.y = out_point.z

instance elaborated : ElaboratedCircuit (F p) unit Row where
  main
  localLength _ := 3

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  ring_nf at *
  simp_all only [sub_eq_iff_eq_add, zero_add]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  sorry

def circuit : FormalCircuit (F p) unit Row :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Ragu.Circuits.Core.AllocMul
