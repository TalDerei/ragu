import Ragu.Circuits.Endoscalar.Alloc
import Ragu.Circuits.Boolean.Alloc
import Ragu.Circuits.Core.Mul
import Ragu.Instances.Autogen.Endoscalar.Alloc
import Ragu.Core
import Mathlib.Tactic.IntervalCases

namespace Ragu.Instances.Endoscalar.Alloc
open Ragu.Instances.Autogen.Endoscalar.Alloc

def deserializeInput (_input : Vector (Expression (F p)) inputLen)
    : Var (Unconstrained (BitVec 128)) (F p) :=
  fun _ => 0#128

def serializeOutput (output : Var (fields 128) (F p))
    : Vector (Expression (F p)) 128 :=
  output

/-- The 4 flat operations a single `Boolean.Alloc.circuit` emits at the given
witness `offset`, after `Operations.toFlat` and `eraseCompute` normalization.
Uses the subtraction form `a - b` to match the reimpl directly; this is
definitionally `a + Expression.const (-1) * b`, which is the autogen form. -/
private def boolean_alloc_step (offset : ℕ) : List (FlatOperation (F p)) :=
  [FlatOperation.witness 3 (fun _ => default),
   FlatOperation.assert (var ⟨offset⟩ * var ⟨offset + 1⟩ - var ⟨offset + 2⟩),
   FlatOperation.assert (var ⟨offset + 2⟩),
   FlatOperation.assert (1 - var ⟨offset⟩ - var ⟨offset + 1⟩)]

/-- A single `Boolean.Alloc.circuit` call at a generic offset produces exactly
`boolean_alloc_step offset` once we toFlat + eraseCompute. -/
private lemma boolean_alloc_at (hint : ProverEnvironment (F p) → Bool) (offset : ℕ) :
    ((Circuits.Boolean.Alloc.circuit hint).operations offset).toFlat.map
        Core.Statements.FlatOperation.eraseCompute =
    boolean_alloc_step offset := by
  simp [Circuits.Boolean.Alloc.circuit, Circuits.Boolean.Alloc.main,
        Circuits.Core.Mul.main,
        Operations.toFlat, Core.Statements.FlatOperation.eraseCompute,
        GeneralFormalCircuit.WithHint.toSubcircuit,
        boolean_alloc_step, circuit_norm]

/-- `Operations.toFlat` distributes over `++`. -/
private lemma operations_toFlat_append (xs ys : Operations (F p)) :
    (xs ++ ys).toFlat = xs.toFlat ++ ys.toFlat := by
  induction xs with
  | nil => simp [Operations.toFlat]
  | cons x xs ih =>
    cases x <;> simp [Operations.toFlat, ih, List.append_assoc]

/-- `Boolean.Alloc.circuit hint` always has local length 3. -/
private lemma boolean_alloc_localLength
    (hint : ProverEnvironment (F p) → Bool) (offset : ℕ) :
    (Circuits.Boolean.Alloc.circuit hint).localLength offset = 3 := by
  rfl

/-- Inductive form: the operations of a `mapM` over any `Vector (Fin 128) n`
calling `Boolean.Alloc.circuit` agree element-for-element with our concrete
step function. The body is index-dependent through its witness closure, but
that closure is wiped by `eraseCompute`. -/
private lemma mapM_boolean_alloc_ops
    {value : ProverEnvironment (F p) → BitVec 128}
    {n : ℕ} (xs : Vector (Fin 128) n) (offset : ℕ) :
    (((xs.mapM (fun (i : Fin 128) =>
            Circuits.Boolean.Alloc.circuit
              (fun env => (value env)[i.val]))).operations offset).toFlat.map
          Core.Statements.FlatOperation.eraseCompute) =
      (List.range n).flatMap (fun i => boolean_alloc_step (offset + i * 3)) := by
  induction xs using Vector.induct generalizing offset with
  | nil =>
    -- Empty vector: mapM returns pure #v[], operations = [].
    simp [Vector.mapM_mk_empty, Circuit.pure_operations_eq, Operations.toFlat]
  | @cons n a as ih =>
    rw [Circuit.MapM.mapM_cons]
    -- The `do` block desugars to `>>= ... >>= ... pure`.
    -- Decompose via bind_operations_eq, knowing pure's ops are [].
    rw [show
          (do
            let y ← Circuits.Boolean.Alloc.circuit (fun env => (value env)[a.val])
            let ys ← as.mapM (fun i => Circuits.Boolean.Alloc.circuit
                                          (fun env => (value env)[i.val]))
            pure (Vector.listCons y ys))
          = (Circuits.Boolean.Alloc.circuit (fun env => (value env)[a.val])) >>=
              fun y => as.mapM (fun i => Circuits.Boolean.Alloc.circuit
                                            (fun env => (value env)[i.val])) >>=
                        fun ys => pure (Vector.listCons y ys) from rfl]
    rw [Circuit.bind_operations_eq, Circuit.bind_operations_eq,
        Circuit.pure_operations_eq, List.append_nil]
    rw [operations_toFlat_append, List.map_append]
    rw [boolean_alloc_at, boolean_alloc_localLength]
    rw [ih (offset := offset + 3)]
    -- Peel the head of the RHS `range_succ`-style.
    have rhs_eq :
      (List.range (n + 1)).flatMap (fun i => boolean_alloc_step (offset + i * 3)) =
      boolean_alloc_step offset ++
        (List.range n).flatMap (fun i => boolean_alloc_step (offset + 3 + i * 3)) := by
      rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp only [Nat.zero_mul, Nat.add_zero]
      congr 1
      apply List.flatMap_congr
      intro i _
      congr 1
      omega
    rw [rhs_eq]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput

  deserializeInput
  serializeOutput

  reimplementation := Circuits.Endoscalar.Alloc.circuit

  same_constraints := by
    intro input
    -- Unfold the framework wrapping (CoeFun → subcircuitWithHintAssertion → toSubcircuit)
    -- so the goal exposes the underlying `Vector.mapM` from our `main`.
    simp only [GeneralFormalCircuit.WithHint.toSubcircuit,
               subcircuitWithHintAssertion,
               Circuit.operations, Operations.toFlat, List.append_nil,
               Operations.toNested_toFlat,
               Circuits.Endoscalar.Alloc.circuit,
               Circuits.Endoscalar.Alloc.elaborated,
               Circuits.Endoscalar.Alloc.main,
               Circuit.mapFinRange, Vector.mapFinRangeM,
               deserializeInput]
    rw [mapM_boolean_alloc_ops (value := fun _ => 0#128) (Vector.finRange 128)]
    rfl

  same_output := by
    intro input
    -- Reduce the reimpl's output through subcircuit/mapFinRange machinery; both
    -- sides land as `Vector.mapFinRange 128 (fun i => var ⟨i*3⟩)` definitionally.
    apply Vector.ext
    intro i hi
    simp only [Circuits.Endoscalar.Alloc.circuit, deserializeInput, serializeOutput,
               Circuits.Endoscalar.Alloc.elaborated,
               Circuits.Endoscalar.Alloc.main,
               GeneralFormalCircuit.WithHint.toSubcircuit,
               subcircuitWithHintAssertion,
               Circuits.Boolean.Alloc.circuit,
               Circuits.Boolean.Alloc.main,
               Circuits.Core.Mul.main,
               circuit_norm, Vector.getElem_mapFinRange]
    -- LHS: `var ⟨0 + i * 3⟩`. RHS: i-th element of the autogen literal vector.
    -- The autogen unfolds to `var ⟨3 * i⟩` for each i ∈ [0, 128); split.
    interval_cases i <;> rfl

end Ragu.Instances.Endoscalar.Alloc
