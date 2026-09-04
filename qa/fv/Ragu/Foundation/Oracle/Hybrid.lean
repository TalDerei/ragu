import Ragu.Foundation.Probability.Bias
import Ragu.Foundation.Oracle.OracleComp

/-!
Ported from `Zcash/Common/Oracle/Hybrid.lean` at `zcash/ironwood` commit
`3c056cbebf2880b54f801c348cb67ce7dc9f2a05`. Ragu adapts only the namespace and internal imports.
-/

/-!
# Adaptive challenge-law hybrids

`OracleComp.runFreshPMF` gives an adaptive query tree fresh independent answers from a supplied
one-squeeze law.  `runFreshPMF_eventBiasLE` is the joint hybrid: a `Q`-query tree turns a weighted
one-squeeze bias `ε` into event bias at most `Q * ε`, even when later query points and continuations
depend on earlier answers.

Repeated random-oracle queries must first be deduplicated with `OracleComp.dedup`; the Action
deployment wrapper does that before applying this theorem, so repeated transcript points retain
one answer rather than receiving fresh samples.
-/

namespace Ragu.Foundation.Oracle

open scoped ENNReal
open Ragu.Foundation.Probability

namespace OracleComp

variable {T F α : Type*}

/-- Probabilistic semantics that gives every query node a fresh independent answer from `law`. -/
noncomputable def runFreshPMF (law : PMF F) : OracleComp T F α → PMF α
  | .pure a => PMF.pure a
  | .query _ k => law.bind fun u => runFreshPMF law (k u)

/-- **Adaptive joint hybrid.** A weighted one-squeeze bias accumulates at most once per visited
query node.  The proof follows the query-bound derivation, using continuation probabilities as
the `[0,1]` test passed to `PMFWeightedBiasLE`. -/
theorem runFreshPMF_eventBiasLE [Fintype F]
    {actual ideal : PMF F} {ε : ℝ≥0∞}
    (hstep : PMFWeightedBiasLE actual ideal ε)
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q) :
    PMFEventBiasLE (A.runFreshPMF actual) (A.runFreshPMF ideal) (Q * ε) := by
  induction hQ with
  | pure a Q =>
      intro S
      exact le_add_right le_rfl
  | @query t k Q hk ih =>
      intro S
      simp only [runFreshPMF, PMF.toOuterMeasure_bind_apply, tsum_fintype]
      have hcontinuation :
          ∑ u, actual u * (runFreshPMF actual (k u)).toOuterMeasure S ≤
            ∑ u, actual u * ((runFreshPMF ideal (k u)).toOuterMeasure S +
              (Q : ℝ≥0∞) * ε) := by
        exact Finset.sum_le_sum fun u _ ↦ mul_le_mul_right (ih u S) _
      refine hcontinuation.trans ?_
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul]
      have hmass : (∑ u : F, actual u) = 1 := by
        have h := actual.tsum_coe
        rw [tsum_fintype] at h
        exact h
      rw [hmass, one_mul]
      have hweight := hstep
        (fun u ↦ (runFreshPMF ideal (k u)).toOuterMeasure S)
        (fun u ↦ (PMF.toOuterMeasure_mono _ (Set.subset_univ _)).trans_eq (by
          rw [PMF.toOuterMeasure_apply, Set.indicator_univ]
          exact (runFreshPMF ideal (k u)).tsum_coe))
      calc
        ∑ u, actual u * (runFreshPMF ideal (k u)).toOuterMeasure S + (Q : ℝ≥0∞) * ε ≤
            (∑ u, ideal u * (runFreshPMF ideal (k u)).toOuterMeasure S + ε) +
              (Q : ℝ≥0∞) * ε :=
          add_le_add_left hweight _
        _ = ∑ u, ideal u * (runFreshPMF ideal (k u)).toOuterMeasure S +
              ((Q + 1 : ℕ) : ℝ≥0∞) * ε := by
          push_cast
          ring

end OracleComp

end Ragu.Foundation.Oracle
