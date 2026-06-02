import Ragu.Contrib.ExtractSoundnessSpike

/-!
DEMO — intentionally fails to build.

This attempts to prove *unconditional* soundness of the unfixed `extract`
(no `elem + c ≠ 0` hypothesis). It wedges in the `bit = 0` branch: the goal
becomes `False`, but at `elem + c = 0` there is no contradiction, so no honest
tactic closes it. That open `⊢ False` is the soundness gap.
-/

namespace Ragu.Contrib.ExtractSoundnessSpike

variable {F : Type*} [Field F]

theorem extract_sound_unconditional
    {g c elem bit sqrt : F}
    (hg : ¬ IsSquare g)
    (hc : UnfixedBitConstraints g c elem bit sqrt) :
    BitSpec c elem bit := by
  obtain ⟨hbool, hbranch⟩ := hc
  have hbit : bit = 0 ∨ bit = 1 := by
    rcases mul_eq_zero.mp hbool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  unfold BitSpec
  constructor
  · intro hb1
    subst hb1
    exact ⟨sqrt, by linear_combination -hbranch⟩
  · intro hsq
    rcases hbit with hb0 | hb1
    · exfalso
      subst hb0
      obtain ⟨t, ht⟩ := hsq
      -- STUCK: goal is `⊢ False`. We have
      --   hbranch : sqrt ^ 2 = 0 * (elem + c) + (1 - 0) * ((elem + c) * g)
      --   ht      : elem + c = t * t
      --   hg      : ¬ IsSquare g
      -- but NOTHING gives `elem + c ≠ 0`. At elem + c = 0 (t = 0) the
      -- assignment bit = 0 genuinely satisfies every constraint, so there is
      -- no contradiction to derive. No tactic closes this goal.
    · exact hb1

end Ragu.Contrib.ExtractSoundnessSpike
