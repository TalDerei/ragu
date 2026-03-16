import Clean.Circuit

namespace Ragu.Circuits.Core.AllocMul
variable {p : ℕ} [Fact p.Prime]

structure Row (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct


def main (w : Row (F p)) (_input : Unit) : Circuit (F p) (Var Row (F p)) := do
  let ⟨x, y, z⟩ ← (witness fun _env => w : Circuit (F p) (Var Row (F p)))
  assertZero (x*y - z)
  return ⟨x, y, z⟩

def Assumptions (w : Row (F p)) (_inputs : Unit) := w.x * w.y = w.z

def Spec (_inputsinputs : Unit) (out_point : Row (F p)) :=
  out_point.x * out_point.y = out_point.z

instance elaborated (w : Row (F p)) : ElaboratedCircuit (F p) unit Row where
  main := main w
  localLength _ := 3

theorem soundness (w : Row (F p)) : Soundness (F p) (elaborated w) (Assumptions w) Spec := by
  circuit_proof_start
  ring_nf at *
  grind

theorem completeness (w : Row (F p)) : Completeness (F p) (elaborated w) (Assumptions w) := by
  circuit_proof_start
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.reduceAdd] at h_env
  have h0 := h_env 0
  have h1 := h_env 1
  have h2 := h_env 2
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, toElements, components,
    instProvableTypeField.eq_1, id_eq, ProvableStruct.combinedSize', List.map_cons, size,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.reduceAdd,
    ProvableStruct.combinedSize, toComponents, ProvableStruct.componentsToElements.eq_2,
    ProvableStruct.componentsToElements, Vector.append_empty, Vector.append_singleton,
    Vector.push_mk, List.push_toArray, List.cons_append, List.nil_append, Vector.cast_rfl] at h0
  rw [Vector.getElem_append] at h0
  simp only [zero_lt_one, ↓reduceDIte, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero] at h0
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, toElements, components, instProvableTypeField.eq_1,
    id_eq, ProvableStruct.combinedSize', List.map_cons, size, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, Nat.reduceAdd, ProvableStruct.combinedSize, toComponents,
    ProvableStruct.componentsToElements.eq_2, ProvableStruct.componentsToElements,
    Vector.append_empty, Vector.append_singleton, Vector.push_mk, List.push_toArray,
    List.cons_append, List.nil_append, Vector.cast_rfl] at h1
  rw [Vector.getElem_append] at h1
  simp only [Nat.one_mod, lt_self_iff_false, ↓reduceDIte, tsub_self, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero] at h1
  simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, toElements, components, instProvableTypeField.eq_1,
    id_eq, ProvableStruct.combinedSize', List.map_cons, size, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, Nat.reduceAdd, ProvableStruct.combinedSize, toComponents,
    ProvableStruct.componentsToElements.eq_2, ProvableStruct.componentsToElements,
    Vector.append_empty, Vector.append_singleton, Vector.push_mk, List.push_toArray,
    List.cons_append, List.nil_append, Vector.cast_rfl] at h2
  rw [Vector.getElem_append] at h2
  simp only [Nat.mod_succ, Nat.not_ofNat_lt_one, ↓reduceDIte, Nat.add_one_sub_one,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero] at h2
  grind

def circuit (w : Row (F p)) : GeneralFormalCircuit (F p) unit Row :=
  {
    elaborated w with
    Assumptions := Assumptions w,
    Spec,
    soundness := soundness w,
    completeness := completeness w
  }

end Ragu.Circuits.Core.AllocMul
