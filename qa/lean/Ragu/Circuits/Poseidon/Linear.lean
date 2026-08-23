import Clean.Circuit

/-!
# Flattening linear expressions

The Rust Poseidon permutation keeps the state words of the 56 partial rounds
as *virtual* wires: only `state[0]` passes through an S-box gate each round,
the other four words stay linear combinations that the MDS layer multiplies
4× in size every round. The extraction driver tolerates this because its
expressions form a shared DAG and `fingerprint.rs::normalize` memoizes by
pointer; in Lean, Clean's `Expression` is a plain tree, the fingerprint
normalizer is a plain tree walk, and soundness proofs would unfold the trees.

`normalizeLinear` collapses a linear expression into `const + Σ cᵢ · varᵢ`
with one term per variable, and returns any non-linear expression unchanged.
`eval_normalizeLinear` holds for *every* expression, so circuits may apply it
freely (the Poseidon round does so to its output words) without any
linearity hypothesis leaking into their soundness statements. The fingerprint
is unaffected: it hashes polynomial normal forms, not tree shapes.
-/

namespace Ragu.Circuits.Poseidon.Linear
variable {F : Type} [Field F]

/-- `const + Σ (i, c) ∈ terms, c · var i`. `terms` is kept sorted by variable
index with at most one entry per index by `mergeTerms`; the evaluation lemmas
do not depend on that invariant, it only bounds the size. -/
structure LinearForm (F : Type) where
  const : F
  terms : List (ℕ × F)

namespace LinearForm

/-- Value of a term list under `env`. -/
def evalTerms (env : Environment F) (terms : List (ℕ × F)) : F :=
  (terms.map fun t => t.2 * env.get t.1).sum

def eval (env : Environment F) (l : LinearForm F) : F :=
  l.const + evalTerms env l.terms

/-- Merge two index-sorted term lists, adding coefficients at equal indices. -/
def mergeTerms : List (ℕ × F) → List (ℕ × F) → List (ℕ × F)
  | [], ys => ys
  | xs, [] => xs
  | (i, a) :: xs, (j, b) :: ys =>
    if i < j then (i, a) :: mergeTerms xs ((j, b) :: ys)
    else if j < i then (j, b) :: mergeTerms ((i, a) :: xs) ys
    else (i, a + b) :: mergeTerms xs ys

def add (l m : LinearForm F) : LinearForm F :=
  ⟨l.const + m.const, mergeTerms l.terms m.terms⟩

def scale (c : F) (l : LinearForm F) : LinearForm F :=
  ⟨c * l.const, l.terms.map fun t => (t.1, c * t.2)⟩

/-- Rebuild an expression: `((const + c₁·v₁) + c₂·v₂) + ⋯`, one node pair per
term, so the tree has size linear in the number of variables. -/
def toExpr (l : LinearForm F) : Expression F :=
  l.terms.foldl (fun acc t => acc + Expression.const t.2 * var ⟨t.1⟩)
    (Expression.const l.const)

@[simp]
theorem evalTerms_nil (env : Environment F) :
    evalTerms env ([] : List (ℕ × F)) = 0 := by
  simp [evalTerms]

@[simp]
theorem evalTerms_cons (env : Environment F) (t : ℕ × F) (ts : List (ℕ × F)) :
    evalTerms env (t :: ts) = t.2 * env.get t.1 + evalTerms env ts := by
  simp [evalTerms]

theorem evalTerms_mergeTerms (env : Environment F) (xs ys : List (ℕ × F)) :
    evalTerms env (mergeTerms xs ys) = evalTerms env xs + evalTerms env ys := by
  induction xs, ys using mergeTerms.induct with
  | case1 ys => simp [mergeTerms]
  | case2 xs _ => simp [mergeTerms]
  | case3 i a xs j b ys hij ih =>
    rw [mergeTerms, if_pos hij]
    simp only [evalTerms_cons, ih]
    ring
  | case4 i a xs j b ys hij hji ih =>
    rw [mergeTerms, if_neg hij, if_pos hji]
    simp only [evalTerms_cons, ih]
    ring
  | case5 i a xs j b ys hij hji ih =>
    rw [mergeTerms, if_neg hij, if_neg hji]
    have : j = i := by omega
    subst this
    simp only [evalTerms_cons, ih]
    ring

theorem eval_add (env : Environment F) (l m : LinearForm F) :
    (l.add m).eval env = l.eval env + m.eval env := by
  simp only [eval, add, evalTerms_mergeTerms]
  ring

theorem evalTerms_scale (env : Environment F) (c : F) (ts : List (ℕ × F)) :
    evalTerms env (ts.map fun t => (t.1, c * t.2)) = c * evalTerms env ts := by
  induction ts with
  | nil => simp [evalTerms_nil]
  | cons t ts ih =>
    simp only [List.map_cons, evalTerms_cons, ih]
    ring

theorem eval_scale (env : Environment F) (c : F) (l : LinearForm F) :
    (l.scale c).eval env = c * l.eval env := by
  simp only [eval, scale, evalTerms_scale]
  ring

theorem eval_toExpr_aux (env : Environment F) (ts : List (ℕ × F)) (init : Expression F) :
    Expression.eval env
        (ts.foldl (fun acc t => acc + Expression.const t.2 * var ⟨t.1⟩) init) =
      Expression.eval env init + evalTerms env ts := by
  induction ts generalizing init with
  | nil => simp [evalTerms_nil]
  | cons t ts ih =>
    simp only [List.foldl_cons, ih, evalTerms_cons, Expression.eval]
    ring

theorem eval_toExpr (env : Environment F) (l : LinearForm F) :
    Expression.eval env l.toExpr = l.eval env := by
  simp only [toExpr, eval_toExpr_aux, Expression.eval, eval]

end LinearForm

open LinearForm in
/-- The linear form of `e`, or `none` when `e` multiplies two non-constant
subexpressions. -/
def ofExpr : Expression F → Option (LinearForm F)
  | var v => some ⟨0, [(v.index, 1)]⟩
  | .const c => some ⟨c, []⟩
  | .add a b => do
    let la ← ofExpr a
    let lb ← ofExpr b
    pure (la.add lb)
  | .mul a b => do
    let la ← ofExpr a
    let lb ← ofExpr b
    if la.terms.isEmpty then pure (lb.scale la.const)
    else if lb.terms.isEmpty then pure (la.scale lb.const)
    else none

theorem eval_ofExpr (env : Environment F) :
    ∀ (e : Expression F) (l : LinearForm F), ofExpr e = some l →
      l.eval env = Expression.eval env e := by
  intro e
  induction e with
  | var v =>
    intro l h
    simp only [ofExpr, Option.some.injEq] at h
    subst h
    simp [LinearForm.eval, LinearForm.evalTerms, Expression.eval]
  | const c =>
    intro l h
    simp only [ofExpr, Option.some.injEq] at h
    subst h
    simp [LinearForm.eval, LinearForm.evalTerms, Expression.eval]
  | add a b iha ihb =>
    intro l h
    simp only [ofExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨la, ha, lb, hb, rfl⟩ := h
    rw [LinearForm.eval_add, iha la ha, ihb lb hb]
    rfl
  | mul a b iha ihb =>
    intro l h
    simp only [ofExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨la, ha, lb, hb, h⟩ := h
    have ea := iha la ha
    have eb := ihb lb hb
    split_ifs at h with hla hlb
    · simp only [Option.some.injEq] at h
      subst h
      have hconst : la.eval env = la.const := by
        simp [LinearForm.eval, List.isEmpty_iff.mp hla]
      rw [LinearForm.eval_scale, eb, ← hconst, ea]
      rfl
    · simp only [Option.some.injEq] at h
      subst h
      have hconst : lb.eval env = lb.const := by
        simp [LinearForm.eval, List.isEmpty_iff.mp hlb]
      rw [LinearForm.eval_scale, ea, ← hconst, eb]
      simp only [Expression.eval]
      ring

/-- Flatten a linear expression into `const + Σ cᵢ · varᵢ` with one term per
variable; non-linear expressions are returned unchanged. -/
def normalizeLinear (e : Expression F) : Expression F :=
  match ofExpr e with
  | some l => l.toExpr
  | none => e

@[simp]
theorem eval_normalizeLinear (env : Environment F) (e : Expression F) :
    Expression.eval env (normalizeLinear e) = Expression.eval env e := by
  unfold normalizeLinear
  split
  · rename_i l h
    rw [LinearForm.eval_toExpr, eval_ofExpr env e l h]
  · rfl

end Ragu.Circuits.Poseidon.Linear
