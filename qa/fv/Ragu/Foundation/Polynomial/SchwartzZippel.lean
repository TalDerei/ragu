import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# Generic Schwartz-Zippel bounds

Adapted from `Zcash/Snark/Fingerprint/SchwartzZippel.lean` at `zcash/ironwood` commit
`3c056cbebf2880b54f801c348cb67ce7dc9f2a05`. Unlike the source specialization to `Fp`, these
statements quantify over an arbitrary finite field and use `Fintype.card F` directly.
-/

namespace Ragu.Foundation.Polynomial

open MvPolynomial Finset Fintype

/-- A nonzero polynomial over a finite field vanishes on at most a
`totalDegree / |F|` fraction of `F^n`. -/
theorem schwartz_zippel_fin {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {n : ℕ} {p : MvPolynomial (Fin n) F} (hp : p ≠ 0) :
    (#{f ∈ piFinset fun _ => (univ : Finset F) | eval f p = 0} : ℚ≥0)
        / (Fintype.card F : ℚ≥0) ^ n ≤ (p.totalDegree : ℚ≥0) / Fintype.card F := by
  have h := schwartz_zippel_totalDegree hp (univ : Finset F)
  simpa only [Finset.card_univ] using h

/-- `schwartz_zippel_fin` transported to an arbitrary finite variable index. -/
theorem schwartz_zippel_index {F σ : Type*} [Fintype F] [Field F] [DecidableEq F]
    [Fintype σ] [DecidableEq σ] {p : MvPolynomial σ F} (hp : p ≠ 0) :
    (#{f ∈ piFinset fun _ : σ => (univ : Finset F) | eval f p = 0} : ℚ≥0)
        / (Fintype.card F : ℚ≥0) ^ Fintype.card σ
      ≤ (p.totalDegree : ℚ≥0) / Fintype.card F := by
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  have hq0 : rename (⇑e) p ≠ 0 := fun h =>
    hp (rename_injective (⇑e) e.injective (by simpa using h))
  have hdeg : (rename (⇑e) p).totalDegree = p.totalDegree := totalDegree_renameEquiv e p
  have hcard : #{f ∈ piFinset fun _ : σ => (univ : Finset F) | eval f p = 0}
      = #{g ∈ piFinset fun _ : Fin (Fintype.card σ) => (univ : Finset F) |
          eval g (rename (⇑e) p) = 0} := by
    refine Finset.card_equiv (e.arrowCongr (Equiv.refl F)) fun f => ?_
    have hcomp : eval (⇑(e.arrowCongr (Equiv.refl F)) f) (rename (⇑e) p) = eval f p := by
      have hfe : (⇑(e.arrowCongr (Equiv.refl F)) f) ∘ ⇑e = f := by
        funext v
        simp [Equiv.arrowCongr]
      rw [eval_rename, hfe]
    simp only [Finset.mem_filter, mem_piFinset, Finset.mem_univ, implies_true, true_and, hcomp]
  rw [hcard, ← hdeg]
  exact schwartz_zippel_fin hq0

end Ragu.Foundation.Polynomial
