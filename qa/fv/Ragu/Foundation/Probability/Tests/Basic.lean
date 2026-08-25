import Ragu.Foundation.Probability

namespace Ragu.Foundation.Probability.Tests.Basic

open scoped ENNReal
open Ragu.Foundation.Probability

example {Ω : Type*} (p : PMF Ω) : PMFEventBiasLE p p 0 := by
  intro event
  simp

example {Ω : Type*} [Fintype Ω] (p : PMF Ω) : PMFWeightedBiasLE p p 0 := by
  intro weight _
  simp

example {Ω : Type*} {p₁ p₂ p₃ : PMF Ω} {ρ₁ ρ₂ : ℝ≥0∞}
    (h₁ : PMFEventBiasLE p₁ p₂ ρ₁) (h₂ : PMFEventBiasLE p₂ p₃ ρ₂) :
    PMFEventBiasLE p₁ p₃ (ρ₂ + ρ₁) :=
  h₁.trans h₂

example :
    (PMF.uniformOfFintype Bool).toOuterMeasure (Set.univ : Set Bool) = 1 :=
  uniformOfFintype_toOuterMeasure_univ

end Ragu.Foundation.Probability.Tests.Basic
