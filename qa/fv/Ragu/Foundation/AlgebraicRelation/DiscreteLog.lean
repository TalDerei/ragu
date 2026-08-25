import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Abel

/-!
Ported from `Zcash/Common/DiscreteLogRelation.lean` at `zcash/ironwood` commit
`3c056cbebf2880b54f801c348cb67ce7dc9f2a05`. Ragu adapts only the namespace.
-/

/-!
# Nontrivial linear (discrete-log) relations, as computed data

Shared primitive for the reduction-style security arguments (breaks as computed data — see
`Zcash.Security.RandomOracle`): a nontrivial `F`-linear relation among a family of generators
`g : Fin n → G` together with two distinguished generators `U`, `W`, carried as *data* (the
coefficients) so a reduction can compute it rather than merely assert its existence. In a
prime-order group such a relation always *exists* propositionally, so an ∃-closed `Prop` would be
vacuous; the content is that a reduction produces one, discharged against discrete-log-relation
hardness at the computational layer.

Both crypto layers instantiate this: the binding-signature reduction
(`Zcash.Security.BindingSignature`) and the deployed-verifier soundness peel (`Zcash.Snark`).
Each use site documents its own reading of the generators.
-/

namespace Ragu.Foundation.AlgebraicRelation

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A nontrivial `F`-linear (discrete-log) relation among the generators `(g, U, W)`, as data:
coefficients `(a, α, β)` not all zero that the generators send to `0`. -/
structure NontrivialRelation {n : ℕ} (g : Fin n → G) (U W : G) where
  a : Fin n → F
  α : F
  β : F
  nontrivial : a ≠ 0 ∨ α ≠ 0 ∨ β ≠ 0
  relation : (∑ i, a i • g i) + α • U + β • W = 0

/-- The one-distinguished-generator variant: a nontrivial `F`-linear relation among the
family `g` and a single distinguished generator `U`.  This is the shape of a Sinsemilla
discrete-log break (protocol spec Theorem 5.4.4): a relation among the per-chunk generator
table and the domain point `Q`, produced as data by the escape reduction
(`Zcash.Security.Ledger.Bridge.relationOfBreakData`). -/
structure NontrivialRelationOne {n : ℕ} (g : Fin n → G) (U : G) where
  a : Fin n → F
  α : F
  nontrivial : a ≠ 0 ∨ α ≠ 0
  relation : (∑ i, a i • g i) + α • U = 0

/-- The commitment over arbitrary generators `g`: `⟨a, g⟩ = Σᵢ aᵢ • gᵢ`. -/
def commitGen {n : ℕ} (g : Fin n → G) (a : Fin n → F) : G := ∑ i, a i • g i

/-- Additivity in the witness. -/
theorem commitGen_add_left {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a + a') = commitGen g a + commitGen g a' := by
  simp only [commitGen, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Homogeneity in the witness. -/
theorem commitGen_smul_left {n : ℕ} (g : Fin n → G) (c : F) (a : Fin n → F) :
    commitGen g (c • a) = c • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Additivity in the generators. -/
theorem commitGen_add_gen {n : ℕ} (g g' : Fin n → G) (a : Fin n → F) :
    commitGen (g + g') a = commitGen g a + commitGen g' a := by
  simp only [commitGen, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Homogeneity in the generators. -/
theorem commitGen_smul_gen {n : ℕ} (c : F) (g : Fin n → G) (a : Fin n → F) :
    commitGen (c • g) a = c • commitGen g a := by
  simp only [commitGen, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm (a i) c (g i)

/-- Subtractivity in the witness. -/
theorem commitGen_sub {n : ℕ} (g : Fin n → G) (a a' : Fin n → F) :
    commitGen g (a - a') = commitGen g a - commitGen g a' := by
  simp only [commitGen, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- Negation in the witness. -/
theorem commitGen_neg {n : ℕ} (g : Fin n → G) (a : Fin n → F) :
    commitGen g (-a) = -commitGen g a := by
  simpa using commitGen_smul_left g (-1) a

/-- **The combination-collision assembler.** Two `(g, U, W)`-combinations equal as group
elements, with coordinates that do not all agree, compute a nontrivial discrete-log
relation: the coordinate differences `(a − a', α − α', β − β')`. -/
def NontrivialRelation.ofCombinationCollision [DecidableEq F] {n : ℕ} {g : Fin n → G} {U W : G}
    {a a' : Fin n → F} {α α' β β' : F}
    (e : commitGen g a + α • U + β • W = commitGen g a' + α' • U + β' • W)
    (hne : ¬(a = a' ∧ α = α' ∧ β = β')) : NontrivialRelation (F := F) g U W where
  a := a - a'
  α := α - α'
  β := β - β'
  nontrivial := by
    by_cases ha : a = a'
    · by_cases hα : α = α'
      · exact Or.inr (Or.inr (sub_ne_zero.mpr (fun hβ => hne ⟨ha, hα, hβ⟩)))
      · exact Or.inr (Or.inl (sub_ne_zero.mpr hα))
    · exact Or.inl (sub_ne_zero.mpr ha)
  relation := by
    show commitGen g (a - a') + (α - α') • U + (β - β') • W = 0
    have hrw : commitGen g (a - a') + (α - α') • U + (β - β') • W
        = (commitGen g a + α • U + β • W) - (commitGen g a' + α' • U + β' • W) := by
      rw [commitGen_sub, sub_smul, sub_smul]; abel
    rw [hrw, e, sub_self]

/-- Over a zero third generator, a relation with a nonzero table-coefficient vector
or a nonzero distinguished coefficient converts to the one-generator form. The third
coefficient contributes nothing — it scales the zero point — so it cannot carry the
nontriviality. -/
def NontrivialRelation.toOne {n : ℕ} {g : Fin n → G} {U : G}
    (rel : NontrivialRelation (F := F) g U (0 : G))
    (h : rel.a ≠ 0 ∨ rel.α ≠ 0) : NontrivialRelationOne (F := F) g U where
  a := rel.a
  α := rel.α
  nontrivial := h
  relation := by
    have hr := rel.relation
    simpa [smul_zero] using hr

end Ragu.Foundation.AlgebraicRelation
