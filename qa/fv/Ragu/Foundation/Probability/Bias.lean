import Mathlib.Probability.Distributions.Uniform

/-!
Ported and namespace-adapted from Zcash/Common/Oracle/Model.lean at zcash/ironwood commit
3c056cbebf2880b54f801c348cb67ce7dc9f2a05. The probability statements and proofs are otherwise retained.
-/

/-!
# One-sided bias interfaces for oracle experiments

`PMFEventBiasLE` and `PMFWeightedBiasLE` are the one-sided statistical-distance interfaces the
adaptive hybrid (`Oracle/Hybrid.lean`) and the security capstones consume: `actual` overshoots
`ideal` by at most `ρ`, on every event (`PMFEventBiasLE`) or against every `[0,1]`-valued test
(`PMFWeightedBiasLE`, the stronger continuation-weighted form).

Generic in the sample space, with no dependency on any transcript type or field. The `Fp`-specific
uniform-challenge idealization (`uniformChallenge`) and the deployed `Challenge255 → Fp` conversion
bias live on the Snark side (`Zcash/Snark/Soundness/Oracle/ChallengeUniform.lean` and
`Challenge255.lean`), since they name concrete deployed objects.
-/
namespace Ragu.Foundation.Probability

open scoped ENNReal

/-- `actual` overshoots `ideal` by at most `ρ` on every event.  This one-sided statistical-distance
interface is the exact premise needed to transport a soundness upper bound; it may represent one
squeeze or an entire adaptive transcript experiment. -/
def PMFEventBiasLE {Ω : Type*} (actual ideal : PMF Ω) (ρ : ℝ≥0∞) : Prop :=
  ∀ S : Set Ω, actual.toOuterMeasure S ≤ ideal.toOuterMeasure S + ρ

/-- `actual` overshoots `ideal` by at most `ρ` against every test taking values in `[0,1]`.

This finite weighted form is stronger than `PMFEventBiasLE`: indicator tests recover events, while
continuation probabilities are the weights needed to compose a one-squeeze bound through an
adaptive query tree. -/
def PMFWeightedBiasLE {Ω : Type*} [Fintype Ω]
    (actual ideal : PMF Ω) (ρ : ℝ≥0∞) : Prop :=
  ∀ weight : Ω → ℝ≥0∞, (∀ x, weight x ≤ 1) →
    ∑ x, actual x * weight x ≤ ∑ x, ideal x * weight x + ρ

/-- A weighted bias bound specializes to the event-bias interface used by the capstones. -/
theorem PMFWeightedBiasLE.eventBiasLE {Ω : Type*} [Fintype Ω]
    {actual ideal : PMF Ω} {ρ : ℝ≥0∞}
    (hbias : PMFWeightedBiasLE actual ideal ρ) :
    PMFEventBiasLE actual ideal ρ := by
  classical
  intro S
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, tsum_fintype, tsum_fintype]
  simpa only [Set.indicator_apply, mul_ite, mul_one, mul_zero] using
    hbias (fun x ↦ if x ∈ S then 1 else 0) (fun x ↦ by
      by_cases hx : x ∈ S <;> simp [hx])

/-- On a finite space an event bound is already a weighted bound, at the same `ρ`: against a
`[0,1]`-valued test, `actual` can overshoot `ideal` by no more than it does on the event where
it exceeds `ideal` pointwise. -/
theorem PMFEventBiasLE.weightedBiasLE {Ω : Type*} [Fintype Ω]
    {actual ideal : PMF Ω} {ρ : ℝ≥0∞}
    (hbias : PMFEventBiasLE actual ideal ρ) :
    PMFWeightedBiasLE actual ideal ρ := by
  classical
  intro w hw
  have hpt : ∀ x, actual x * w x
      ≤ ideal x * w x + if ideal x < actual x then actual x - ideal x else 0 := by
    intro x
    by_cases hx : ideal x < actual x
    · rw [if_pos hx]
      calc actual x * w x
          = (ideal x + (actual x - ideal x)) * w x := by
            rw [add_tsub_cancel_of_le hx.le]
        _ = ideal x * w x + (actual x - ideal x) * w x := add_mul _ _ _
        _ ≤ ideal x * w x + (actual x - ideal x) := by
            gcongr
            exact mul_le_of_le_one_right' (hw x)
    · rw [if_neg hx, add_zero]
      gcongr
      exact not_lt.mp hx
  calc ∑ x, actual x * w x
      ≤ ∑ x, (ideal x * w x
          + if ideal x < actual x then actual x - ideal x else 0) :=
        Finset.sum_le_sum fun x _ ↦ hpt x
    _ = ∑ x, ideal x * w x
        + ∑ x ∈ Finset.univ.filter fun x ↦ ideal x < actual x,
            (actual x - ideal x) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
    _ ≤ ∑ x, ideal x * w x + ρ := by
        gcongr
        have hBne : (∑ x ∈ Finset.univ.filter fun x ↦ ideal x < actual x,
              ideal x) ≠ ∞ :=
          ne_top_of_le_ne_top ENNReal.one_ne_top
            ((ENNReal.sum_le_tsum _).trans_eq ideal.tsum_coe)
        rw [← ENNReal.add_le_add_iff_right hBne,
          show (∑ x ∈ Finset.univ.filter fun x ↦ ideal x < actual x,
                (actual x - ideal x))
              + ∑ x ∈ Finset.univ.filter fun x ↦ ideal x < actual x, ideal x
            = ∑ x ∈ Finset.univ.filter fun x ↦ ideal x < actual x, actual x
            from by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun x hx ↦
            tsub_add_cancel_of_le (Finset.mem_filter.mp hx).2.le]
        calc (∑ x ∈ Finset.univ.filter fun x ↦ ideal x < actual x, actual x)
            = actual.toOuterMeasure
                ↑(Finset.univ.filter fun x ↦ ideal x < actual x) :=
              (actual.toOuterMeasure_apply_finset _).symm
          _ ≤ ideal.toOuterMeasure
                ↑(Finset.univ.filter fun x ↦ ideal x < actual x) + ρ :=
              hbias _
          _ = (∑ x ∈ Finset.univ.filter fun x ↦ ideal x < actual x, ideal x)
              + ρ := by
              rw [ideal.toOuterMeasure_apply_finset]
          _ = ρ + ∑ x ∈ Finset.univ.filter fun x ↦ ideal x < actual x,
              ideal x := add_comm _ _

/-- Bias bounds chain, adding their budgets. -/
theorem PMFEventBiasLE.trans {Ω : Type*} {p₁ p₂ p₃ : PMF Ω} {ρ₁ ρ₂ : ℝ≥0∞}
    (h₁ : PMFEventBiasLE p₁ p₂ ρ₁) (h₂ : PMFEventBiasLE p₂ p₃ ρ₂) :
    PMFEventBiasLE p₁ p₃ (ρ₂ + ρ₁) := fun S ↦
  (h₁ S).trans (by rw [← add_assoc]; gcongr ?_ + ρ₁; exact h₂ S)

/-- Mixing pointwise-biased experiments with the same outer distribution preserves their bias.
This transports a per-parameter event bound to the corresponding joint experiment. -/
theorem PMFEventBiasLE.bind_same {α β : Type*} [Fintype β] {μ : PMF β}
    {actual ideal : β → PMF α} {ρ : ℝ≥0∞}
    (hbias : ∀ b, PMFEventBiasLE (actual b) (ideal b) ρ) :
    PMFEventBiasLE (μ.bind actual) (μ.bind ideal) ρ := by
  intro S
  simp only [PMF.toOuterMeasure_bind_apply, tsum_fintype]
  calc
    ∑ b, μ b * (actual b).toOuterMeasure S ≤
        ∑ b, μ b * ((ideal b).toOuterMeasure S + ρ) :=
      Finset.sum_le_sum fun b _ ↦ mul_le_mul_right (hbias b S) _
    _ = ∑ b, μ b * (ideal b).toOuterMeasure S + ρ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      have hmass : (∑ b, μ b) = 1 := by
        have h := μ.tsum_coe
        rwa [tsum_fintype] at h
      rw [hmass, one_mul]

/-- Mixing experiments whose event bounds vary with the parameter averages their biases: the
joint experiment's budget is the mixture's mean `∑ b, μ b * ρ b`. `PMFEventBiasLE.bind_same`
is the constant-`ρ` case. -/
theorem PMFEventBiasLE.bind_average {α β : Type*} [Fintype β] {μ : PMF β}
    {actual ideal : β → PMF α} {ρ : β → ℝ≥0∞}
    (hbias : ∀ b, PMFEventBiasLE (actual b) (ideal b) (ρ b)) :
    PMFEventBiasLE (μ.bind actual) (μ.bind ideal) (∑ b, μ b * ρ b) := by
  intro S
  simp only [PMF.toOuterMeasure_bind_apply, tsum_fintype]
  calc
    ∑ b, μ b * (actual b).toOuterMeasure S ≤
        ∑ b, μ b * ((ideal b).toOuterMeasure S + ρ b) :=
      Finset.sum_le_sum fun b _ ↦ mul_le_mul_right (hbias b S) _
    _ = ∑ b, μ b * (ideal b).toOuterMeasure S + ∑ b, μ b * ρ b := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]

/-- Transport an ideal-experiment event bound to an explicitly related actual distribution. -/
theorem event_measure_le_of_bias {Ω : Type*} {actual ideal : PMF Ω} {ρ bound : ℝ≥0∞}
    (hbias : PMFEventBiasLE actual ideal ρ) (event : Set Ω)
    (hideal : ideal.toOuterMeasure event ≤ bound) :
    actual.toOuterMeasure event ≤ bound + ρ := by
  exact (hbias event).trans (add_le_add hideal le_rfl)

/-- A distribution's measure of any event is at most the total mass `1`. -/
theorem _root_.PMF.toOuterMeasure_apply_le_one {Ω : Type*} (p : PMF Ω) (S : Set Ω) :
    p.toOuterMeasure S ≤ 1 :=
  le_of_le_of_eq (PMF.toOuterMeasure_mono _ (Set.subset_univ _))
    ((PMF.toOuterMeasure_apply_eq_one_iff p Set.univ).mpr (Set.subset_univ _))

/-- Two-sided event bias with vanishing `ρ` forces convergence: when a family of
distributions and a fixed ideal overshoot each other by at most `ρ i` on every event, in
both `PMFEventBiasLE` directions, and `ρ` tends to `0` along the family's filter, the
family's measure of every event tends to the ideal's. -/
theorem tendsto_toOuterMeasure_of_eventBiasLE {Ω ι : Type*} {l : Filter ι}
    {actual : ι → PMF Ω} {ideal : PMF Ω} {ρ : ι → ℝ≥0∞}
    (hup : ∀ i, PMFEventBiasLE (actual i) ideal (ρ i))
    (hdown : ∀ i, PMFEventBiasLE ideal (actual i) (ρ i))
    (hρ : Filter.Tendsto ρ l (nhds 0)) (S : Set Ω) :
    Filter.Tendsto (fun i ↦ (actual i).toOuterMeasure S) l
      (nhds (ideal.toOuterMeasure S)) := by
  have hI : ideal.toOuterMeasure S ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (ideal.toOuterMeasure_apply_le_one S)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun i ↦ ideal.toOuterMeasure S - ρ i)
    (h := fun i ↦ ideal.toOuterMeasure S + ρ i) ?_ ?_ ?_ ?_
  · simpa using ENNReal.Tendsto.sub tendsto_const_nhds hρ (Or.inl hI)
  · simpa using Filter.Tendsto.add tendsto_const_nhds hρ
  · exact fun i ↦ tsub_le_iff_right.mpr (hdown i S)
  · exact fun i ↦ hup i S

end Ragu.Foundation.Probability
