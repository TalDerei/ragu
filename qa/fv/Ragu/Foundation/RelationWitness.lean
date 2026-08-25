import Mathlib.Data.Nat.Notation

/-!
# Sequencing computed outcome branches

Ported and adapted from `Zcash/Common/RelationWitness.lean` at `zcash/ironwood` commit
`3c056cbebf2880b54f801c348cb67ce7dc9f2a05`.

Reductions following the breaks-as-computed-data discipline conclude `A ⊕' R`: either the
intended result or an explicit relation/break witness. Unlike `A ∨ R`, this shape cannot be
case-split classically: a `PSum` value must be computed. The combinators here sequence one such
outcome and traverse finite or list-indexed families while preserving the first explicit break.

The inherited `OrRelationWitness` names are retained so later Ironwood-derived reductions can port
without adapter layers. These definitions only compose already-computed outcomes; they do not by
themselves establish a reduction, probability bound, or verifier connection.
-/

namespace Ragu.Foundation

universe u v w

/-- Preserve an explicit break branch while sequencing a successful result. -/
def bindOrRelationWitness {A : Sort u} {B : Sort v} {R : Sort w}
    (outcome : A ⊕' R) (next : A → B) : B ⊕' R :=
  match outcome with
  | PSum.inl value => PSum.inl (next value)
  | PSum.inr relation => PSum.inr relation

/-- Traverse a `Fin`-indexed family of computed outcomes left to right: every left-hand value, or
the first right-hand value as data, without existential search. -/
def finForallOrRelationWitness {n : Nat} {A : Fin n → Sort v} {R : Sort w}
    (outcome : ∀ i, A i ⊕' R) : (∀ i, A i) ⊕' R := by
  induction n with
  | zero => exact PSum.inl fun i => Fin.elim0 i
  | succ n ih =>
      cases hhead : outcome 0 with
      | inr relation => exact PSum.inr relation
      | inl head =>
          cases htail : ih (fun i => outcome i.succ) with
          | inr relation => exact PSum.inr relation
          | inl tail => exact PSum.inl (Fin.cases head tail)

/-- Traverse a finite family of optional certificates. The returned function contains the exact
certificates produced by the individual checks; failure at any index returns `none`.

To carry proposition proofs as certificates, use `PLift (P i)`: `Option` carries a `Type`, not a
`Prop`. -/
def finForallOption {n : ℕ} {A : Fin n → Type v}
    (outcome : ∀ i, Option (A i)) : Option (∀ i, A i) := by
  induction n with
  | zero => exact some fun i => Fin.elim0 i
  | succ n ih =>
      match outcome 0 with
      | none => exact none
      | some head =>
          match ih (fun i => outcome i.succ) with
          | none => exact none
          | some tail => exact some (Fin.cases head tail)

/-- If every individual optional certificate is present, their finite traversal is present. -/
theorem finForallOption_isSome_of {n : ℕ} {A : Fin n → Type v}
    (outcome : ∀ i, Option (A i)) (h : ∀ i, (outcome i).isSome) :
    (finForallOption outcome).isSome := by
  induction n with
  | zero => rfl
  | succ n ih =>
      obtain ⟨head, hhead⟩ := Option.isSome_iff_exists.mp (h 0)
      have htail : ∀ i : Fin n, (outcome i.succ).isSome := fun i => h i.succ
      obtain ⟨tail, htailEq⟩ := Option.isSome_iff_exists.mp
        (ih (fun i => outcome i.succ) htail)
      have hstep : finForallOption outcome =
          match outcome 0 with
          | none => none
          | some head =>
              match finForallOption (fun i : Fin n => outcome i.succ) with
              | none => none
              | some tail => some (Fin.cases head tail) := rfl
      rw [hstep, hhead, htailEq]
      rfl

/-- The bounded-`ℕ` analogue of `finForallOrRelationWitness`. -/
def boundedForallOrRelationWitness {n : Nat} {A : Nat → Sort v} {R : Sort w}
    (outcome : ∀ i, i < n → A i ⊕' R) : (∀ i, i < n → A i) ⊕' R :=
  bindOrRelationWitness
    (finForallOrRelationWitness (A := fun i : Fin n => A i.val)
      fun i => outcome i.val i.isLt)
    fun h i hi => h ⟨i, hi⟩

/-- The `List`-membership analogue of `finForallOrRelationWitness`: the outcomes for every member
of `l`, or the first break as data.

The clean side is a `Prop` because `x ∈ a :: t` is the `Prop`-valued `x = a ∨ x ∈ t`, and
recovering `A x` from the head and tail results eliminates that proposition. A `Sort`-valued family
over list membership should instead reindex through `Fin l.length`. -/
def listForallOrRelationWitness {α : Type u} {A : α → Prop} {R : Sort w} :
    ∀ l : List α, (∀ x ∈ l, A x ⊕' R) → (∀ x ∈ l, A x) ⊕' R
  | [], _ => PSum.inl fun _ hx => absurd hx (by simp)
  | a :: t, outcome =>
      match outcome a (by simp) with
      | PSum.inr relation => PSum.inr relation
      | PSum.inl head =>
          match listForallOrRelationWitness t
              (fun x hx => outcome x (by simp [hx])) with
          | PSum.inr relation => PSum.inr relation
          | PSum.inl tail =>
              PSum.inl fun x hx =>
                (List.mem_cons.mp hx).elim (fun h => by subst h; exact head) (tail x)

end Ragu.Foundation
