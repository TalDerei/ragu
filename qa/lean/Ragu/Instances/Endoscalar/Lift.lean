import Ragu.Circuits.Endoscalar.Lift
import Ragu.Circuits.Boolean.And
import Ragu.Circuits.Core.Mul
import Ragu.Circuits.Point.Spec
import Ragu.Instances.Autogen.Endoscalar.Lift
import Ragu.Core
import Mathlib.Tactic.IntervalCases

namespace Ragu.Instances.Endoscalar.Lift
open Ragu.Instances.Autogen.Endoscalar.Lift

set_option maxHeartbeats 1000000000
set_option maxRecDepth 100000

def deserializeInput (input : Vector (Expression (F p)) inputLen)
    : Var Circuits.Endoscalar.Lift.Input (F p) :=
  { bits := input }

def serializeOutput (output : Var field (F p)) : Vector (Expression (F p)) outputLen :=
  #v[output]

/-- The 4 flat operations a single `Boolean.And.circuit ⟨n_in, e_in⟩` emits at
the given witness `offset`, after `Operations.toFlat` + `eraseCompute`. -/
private def boolean_and_step (offset : ℕ) (n_in e_in : Expression (F p))
    : List (FlatOperation (F p)) :=
  [FlatOperation.witness 3 (fun _ => default),
   FlatOperation.assert (var ⟨offset⟩ * var ⟨offset + 1⟩ - var ⟨offset + 2⟩),
   FlatOperation.assert (var ⟨offset⟩ - n_in),
   FlatOperation.assert (var ⟨offset + 1⟩ - e_in)]

private lemma boolean_and_at (n_in e_in : Expression (F p)) (offset : ℕ) :
    ((Circuits.Boolean.And.circuit ⟨n_in, e_in⟩).operations offset).toFlat.map
        Core.Statements.FlatOperation.eraseCompute =
    boolean_and_step offset n_in e_in := by
  simp [Circuits.Boolean.And.circuit, Circuits.Boolean.And.main,
        Circuits.Core.Mul.main,
        Operations.toFlat, Operations.toNested_toFlat,
        Core.Statements.FlatOperation.eraseCompute,
        FormalCircuit.toSubcircuit,
        GeneralFormalCircuit.WithHint.toSubcircuit,
        boolean_and_step, circuit_norm]

private lemma operations_toFlat_append (xs ys : Operations (F p)) :
    (xs ++ ys).toFlat = xs.toFlat ++ ys.toFlat := by
  induction xs with
  | nil => simp [Operations.toFlat]
  | cons x xs ih =>
    cases x <;> simp [Operations.toFlat, ih, List.append_assoc]

private lemma boolean_and_localLength (n_in e_in : Expression (F p)) (offset : ℕ) :
    (Circuits.Boolean.And.circuit ⟨n_in, e_in⟩).localLength offset = 3 := by
  rfl

/-! ## Output-side machinery for `same_output`

The reimpl returns `Fin.foldl 64 stepCircuit (Vector.mapM body finRange).1[i] init
+ Const (ctFinal ζ 64)`. The autogen has the same shape fully unfolded with
hex coefficients. We build a recursive helper `lift_acc_aux` matching the
foldl's Nat-recursive structure, prove the Lean reimpl reduces to it
(`fin_foldl_eq_lift_acc_aux`), then close `same_output` by `rfl` against the
kernel-reduced helper. -/

/-- Recursive output accumulator at iteration `k`, matching `Fin.foldl k
stepCircuit` over `bits`. The `if h : k < 64` guard keeps the function total
without requiring a bound parameter (we only call it with `k ≤ 64`). -/
private def lift_acc_aux (bits : Vector (Expression (F p)) 128)
    : ℕ → Expression (F p)
  | 0 => Expression.const 0
  | k + 1 =>
    if h : 2 * k + 1 < 128 then
      Expression.const 2 * lift_acc_aux bits k +
        ((Expression.const (-2 : F p) * bits[2 * k]'(by omega) +
          Expression.const (Circuits.Point.Spec.EpAffineParams.ζ - 1) *
            bits[2 * k + 1]'h) +
         Expression.const (2 * (1 - Circuits.Point.Spec.EpAffineParams.ζ)) *
            var ⟨k * 3 + 2⟩)
    else
      lift_acc_aux bits k

-- Sanity check: the autogen output literal IS our helper plus the ct_final.
/-- The autogen output literal IS `lift_acc_aux input 64 + Const (ctFinal ζ 64)`
under kernel reduction (Nat-recursive `lift_acc_aux` unfolds to the same
64-deep tree the autogen has, with coefficients kernel-equal). -/
private lemma exportedOutput_eq_aux (input : Vector (Expression (F p)) 128) :
    exportedOutput input = #v[lift_acc_aux input 64 +
      Expression.const (Circuits.Endoscalar.Lift.ctFinal
        Circuits.Point.Spec.EpAffineParams.ζ 64)] := by
  rfl

/-- `Fin.foldl_succ_last` doesn't directly match — it produces inner foldl
bodies wrapped in `castSucc`. This variant lets us bridge to a plain
`Fin n`-indexed inner body when they agree pointwise. (Mirrors the helper
in `Circuits/Endoscalar/Lift.lean`.) -/
private lemma fin_foldl_congr_aux {α : Type*} (n : ℕ)
    (f g : α → Fin n → α) (init : α)
    (h : ∀ acc i, f acc i = g acc i) :
    Fin.foldl n f init = Fin.foldl n g init := by
  induction n generalizing init with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
    have h' : ∀ acc i, (fun acc (i : Fin n) => f acc i.castSucc) acc i =
        (fun acc (i : Fin n) => g acc i.castSucc) acc i := fun acc i =>
      h acc i.castSucc
    rw [ih (fun acc i => f acc i.castSucc) (fun acc i => g acc i.castSucc) init h']
    rw [h _ (Fin.last n)]

private lemma fin_foldl_succ_last_eq_aux {α : Type*} (n : ℕ) (f : α → Fin (n + 1) → α)
    (g : α → Fin n → α) (init : α)
    (hfg : ∀ acc (i : Fin n), f acc i.castSucc = g acc i) :
    Fin.foldl (n + 1) f init = f (Fin.foldl n g init) (Fin.last n) := by
  rw [Fin.foldl_succ_last]
  congr 1
  exact fin_foldl_congr_aux n (fun acc i => f acc i.castSucc) g init hfg

/-- The reimpl's foldl-output (with ne_wires substituted by `var ⟨i*3+2⟩`)
equals `lift_acc_aux input n` by induction on `n`. -/
private lemma fin_foldl_eq_lift_acc_aux
    (input : Vector (Expression (F p)) 128) (n : ℕ) (h_n : n ≤ 64) :
    Fin.foldl n (fun (acc : Expression (F p)) (i : Fin n) =>
        Circuits.Endoscalar.Lift.stepCircuit Circuits.Point.Spec.EpAffineParams.ζ
          (input[2 * i.val]'(by have := i.isLt; omega))
          (input[2 * i.val + 1]'(by have := i.isLt; omega))
          (var ⟨i.val * 3 + 2⟩)
          acc)
      (Expression.const 0)
    = lift_acc_aux input n := by
  induction n with
  | zero =>
    -- Both sides: Expression.const 0.
    simp [Fin.foldl_zero, lift_acc_aux]
  | succ n ih =>
    have hn : n ≤ 64 := by omega
    have hn_lt : 2 * n + 1 < 128 := by omega
    rw [fin_foldl_succ_last_eq_aux n _ (fun acc (i : Fin n) =>
        Circuits.Endoscalar.Lift.stepCircuit Circuits.Point.Spec.EpAffineParams.ζ
          (input[2 * i.val]'(by have := i.isLt; omega))
          (input[2 * i.val + 1]'(by have := i.isLt; omega))
          (var ⟨i.val * 3 + 2⟩)
          acc) _ (fun _ _ => by simp [Fin.val_castSucc])]
    rw [ih hn]
    -- LHS: stepCircuit ζ input[2n] input[2n+1] (var ⟨n*3+2⟩) (lift_acc_aux input n)
    -- RHS: lift_acc_aux input (n+1), which unfolds (under `2*n+1<128`) to
    --      the same stepCircuit form by definition of `lift_acc_aux`.
    simp only [lift_acc_aux, Fin.val_last, hn_lt, dif_pos,
               Circuits.Endoscalar.Lift.stepCircuit]

/-! ## Coefficient bridges for `same_output`

The autogen renders Pasta-Fp arbitrary coefficients as raw hex. The Lean reimpl
uses symbolic field-arithmetic expressions in terms of `EpAffineParams.ζ`. These
four lemmas bridge each unique coefficient occurring in the reimpl's output. -/

private lemma const_neg_two_eq :
    (Expression.const (-2 : F Core.Primes.p) : Expression (F Core.Primes.p)) =
    Expression.const
      (0x40000000000000000000000000000000224698fc094cf91b992d30ecffffffff
       : F Core.Primes.p) := by
  rfl

private lemma const_zeta_minus_one_eq :
    (Expression.const (Circuits.Point.Spec.EpAffineParams.ζ - 1
        : F Core.Primes.p) : Expression (F Core.Primes.p)) =
    Expression.const
      (0x12ccca834acdba712caad5dc57aab1b01d1f8bd237ad31491dad5ebdfdfe4ab8
       : F Core.Primes.p) := by
  rfl

private lemma const_two_one_minus_zeta_eq :
    (Expression.const (2 * (1 - Circuits.Point.Spec.EpAffineParams.ζ)
        : F Core.Primes.p) : Expression (F Core.Primes.p)) =
    Expression.const
      (0x1a666af96a648b1da6aa544750aa9c9fe807815799f296895dd2737104036a91
       : F Core.Primes.p) := by
  rfl

private lemma const_ct_final_eq :
    (Expression.const (Circuits.Endoscalar.Lift.ctFinal
        Circuits.Point.Spec.EpAffineParams.ζ 64
        : F Core.Primes.p) : Expression (F Core.Primes.p)) =
    Expression.const
      (0x1955abb8af556360261c069d1c8aeb8444bd73be7b3163afbe2e2610a9922c76
       : F Core.Primes.p) := by
  rfl

/-- Inductive form. For an arbitrary `xs : Vector (Fin 64) n`, the operations
of the `mapM` of `Boolean.And.circuit` over `xs` decompose into one
`boolean_and_step` per element, with offsets advancing by 3 (the body's
constant `localLength`) and inputs read from `bits` at positions `2*i.val`,
`2*i.val + 1` (where `i : Fin 64` ensures `2*i.val + 1 < 128`). -/
private lemma mapM_boolean_and_ops
    (bits : Vector (Expression (F p)) 128)
    {n : ℕ} (xs : Vector (Fin 64) n) (offset : ℕ) :
    (((xs.mapM (fun (i : Fin 64) =>
            Circuits.Boolean.And.circuit
              ⟨bits[2 * i.val]'(by have := i.isLt; omega),
               bits[2 * i.val + 1]'(by have := i.isLt; omega)⟩
          )).operations offset).toFlat.map
          Core.Statements.FlatOperation.eraseCompute) =
      (List.finRange n).flatMap (fun (k : Fin n) =>
        boolean_and_step (offset + k.val * 3)
          (bits[2 * (xs[k.val]'k.isLt).val]'(by have := (xs[k.val]'k.isLt).isLt; omega))
          (bits[2 * (xs[k.val]'k.isLt).val + 1]'(by have := (xs[k.val]'k.isLt).isLt; omega))) := by
  induction xs using Vector.induct generalizing offset with
  | nil =>
    simp [Vector.mapM_mk_empty, Circuit.pure_operations_eq, Operations.toFlat]
  | @cons n a as ih =>
    rw [Circuit.MapM.mapM_cons]
    rw [show
          (do
            let y ← Circuits.Boolean.And.circuit
                      ⟨bits[2 * a.val]'(by have := a.isLt; omega),
                       bits[2 * a.val + 1]'(by have := a.isLt; omega)⟩
            let ys ← as.mapM (fun i => Circuits.Boolean.And.circuit
                              ⟨bits[2 * i.val]'(by have := i.isLt; omega),
                               bits[2 * i.val + 1]'(by have := i.isLt; omega)⟩)
            pure (Vector.listCons y ys))
          = (Circuits.Boolean.And.circuit
              ⟨bits[2 * a.val]'(by have := a.isLt; omega),
               bits[2 * a.val + 1]'(by have := a.isLt; omega)⟩) >>=
              fun y => as.mapM (fun i => Circuits.Boolean.And.circuit
                              ⟨bits[2 * i.val]'(by have := i.isLt; omega),
                               bits[2 * i.val + 1]'(by have := i.isLt; omega)⟩) >>=
                        fun ys => pure (Vector.listCons y ys) from rfl]
    rw [Circuit.bind_operations_eq, Circuit.bind_operations_eq,
        Circuit.pure_operations_eq, List.append_nil]
    rw [operations_toFlat_append, List.map_append]
    rw [boolean_and_at, boolean_and_localLength]
    rw [ih (offset := offset + 3)]
    -- Peel the head of the RHS finRange-style.
    have rhs_eq :
      (List.finRange (n + 1)).flatMap (fun (k : Fin (n + 1)) =>
        boolean_and_step (offset + k.val * 3)
          (bits[2 * ((Vector.listCons a as)[k.val]'k.isLt).val]'
            (by have := ((Vector.listCons a as)[k.val]'k.isLt).isLt; omega))
          (bits[2 * ((Vector.listCons a as)[k.val]'k.isLt).val + 1]'
            (by have := ((Vector.listCons a as)[k.val]'k.isLt).isLt; omega))) =
      boolean_and_step offset
        (bits[2 * a.val]'(by have := a.isLt; omega))
        (bits[2 * a.val + 1]'(by have := a.isLt; omega)) ++
      (List.finRange n).flatMap (fun (k : Fin n) =>
        boolean_and_step (offset + 3 + k.val * 3)
          (bits[2 * (as[k.val]'k.isLt).val]'(by have := (as[k.val]'k.isLt).isLt; omega))
          (bits[2 * (as[k.val]'k.isLt).val + 1]'(by have := (as[k.val]'k.isLt).isLt; omega))) := by
      rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
      simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero]
      congr 1
      apply List.flatMap_congr
      intro k _
      -- (Vector.listCons a as)[(Fin.succ k).val] = (listCons a as)[k.val + 1] = as[k.val]
      -- offset + (k.val + 1) * 3 = offset + 3 + k.val * 3
      simp only [Fin.val_succ]
      congr 1
      omega
    rw [rhs_eq]

noncomputable def formal_instance : Core.Statements.FormalInstance where
  p
  exportedOperations
  exportedOutput
  deserializeInput
  serializeOutput
  reimplementation :=
    (Circuits.Endoscalar.Lift.circuit Circuits.Point.Spec.EpAffineParams).isGeneralFormalCircuit.toWithHint

  same_constraints := by
    intro input
    -- Unfold the wrapping layers: WithHint.toSubcircuit → GeneralFormalCircuit
    -- via FormalCircuit.isGeneralFormalCircuit.toWithHint → main's `mapM >>=
    -- pure`. The final `pure (Fin.foldl ...)` emits no constraints, so all
    -- operations come from the mapM.
    simp only [GeneralFormalCircuit.WithHint.toSubcircuit,
               subcircuitWithHintAssertion,
               FormalCircuit.isGeneralFormalCircuit,
               GeneralFormalCircuit.toWithHint,
               Circuit.operations, Operations.toFlat, List.append_nil,
               Operations.toNested_toFlat,
               Circuits.Endoscalar.Lift.circuit,
               Circuits.Endoscalar.Lift.elaborated,
               Circuits.Endoscalar.Lift.main,
               Circuit.mapFinRange, Vector.mapFinRangeM,
               deserializeInput,
               Circuit.bind_operations_eq, Circuit.pure_operations_eq]
    rw [mapM_boolean_and_ops input (Vector.finRange 64) 0]
    rfl

  same_output := by
    intro input
    rw [exportedOutput_eq_aux]
    apply Vector.ext
    intro idx hidx
    interval_cases idx
    -- Use `circuit_norm` to leverage tagged lemmas (mapFinRange.output_eq,
    -- bind_output_eq, ...) for substituting the mapM's output. After this,
    -- the foldl body should contain `var ⟨i.val * 3 + 2⟩` directly.
    simp only [GeneralFormalCircuit.WithHint.toSubcircuit,
               subcircuitWithHintAssertion,
               FormalCircuit.isGeneralFormalCircuit,
               GeneralFormalCircuit.toWithHint,
               Circuits.Endoscalar.Lift.circuit,
               Circuits.Endoscalar.Lift.elaborated,
               Circuits.Endoscalar.Lift.main,
               deserializeInput, serializeOutput,
               Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
               Circuits.Boolean.And.circuit,
               Circuits.Boolean.And.main,
               Circuits.Boolean.And.elaborated,
               Circuits.Core.Mul.main,
               Nat.zero_add, Nat.add_assoc,
               show (1 + 1 : ℕ) = 2 from rfl,
               circuit_norm]
    congr 1
    exact fin_foldl_eq_lift_acc_aux input 64 (le_refl 64)

end Ragu.Instances.Endoscalar.Lift
