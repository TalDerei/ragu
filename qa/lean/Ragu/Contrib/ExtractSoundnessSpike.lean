import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Throwaway spike: rediscovering the endoscalar `extract` zero-case flaw in Lean

This models the per-bit constraint emitted by `Endoscalar::extract`
(`crates/ragu_primitives/src/endoscalar.rs`) on the **unfixed** circuit, i.e.
*before* the zero-case disambiguation constraint is added.

For a bit position with shift `c = i`, the circuit allocates a boolean `bit`, a
square-root advice `sqrt`, and — folding `alloc_square` (`square = sqrt^2`) into
the branch constraint — enforces

```
bit * (bit - 1) = 0                                            -- booleanity
sqrt ^ 2 = bit * (elem + c) + (1 - bit) * ((elem + c) * g)     -- QR branch
```

where `g = MULTIPLICATIVE_GENERATOR` is a non-residue. The *intended* spec is
that the bit is the quadratic-residue indicator of `elem + c`:

```
bit = 1  ↔  IsSquare (elem + c)
```

* `extract_unsound` proves the unfixed constraints do **not** imply this spec:
  at `elem + c = 0` both branches collapse to `0`, so `bit = 0` satisfies every
  constraint even though `IsSquare 0` holds. This is the soundness bug,
  machine-checked as a real counterexample (the same forged witness as the Rust
  test `test_extract_rejects_false_zero_bits`).

* `extract_sound_of_shifted_ne_zero` proves the spec **is** implied once the
  hypothesis `elem + c ≠ 0` is added — the precondition the unfixed circuit
  silently relies on (sound in Ragu only because `elem` is a Fiat-Shamir hash).
  Surfacing that hypothesis is the whole point: Lean refuses the unconditional
  theorem and only lets us prove the conditional one.
-/

namespace Ragu.Contrib.ExtractSoundnessSpike

variable {F : Type*} [Field F]

/-- The per-bit constraints emitted by the **unfixed** `extract`, for shift `c`,
input `elem`, allocated boolean `bit`, and square-root advice `sqrt`. `g` is the
multiplicative generator (a non-residue). -/
def UnfixedBitConstraints (g c elem bit sqrt : F) : Prop :=
  bit * (bit - 1) = 0 ∧
  sqrt ^ 2 = bit * (elem + c) + (1 - bit) * ((elem + c) * g)

/-- The intended specification: the bit equals the quadratic-residue indicator
of `elem + c`. Note `IsSquare 0` holds, so the indicator at `elem + c = 0` is
`1`. -/
def BitSpec (c elem bit : F) : Prop :=
  bit = 1 ↔ IsSquare (elem + c)

/-- **The flaw.** The unfixed constraints do not pin the bit: for every shift
`c` there is a satisfying assignment that violates the spec. The forged witness
is `elem = -c` (so `elem + c = 0`), `bit = 0`, `sqrt = 0`: it satisfies
booleanity and the branch constraint (`0 = 0`), yet `IsSquare 0` is true, so the
spec demands `bit = 1`. -/
theorem extract_unsound (g c : F) :
    ¬ (∀ elem bit sqrt : F,
        UnfixedBitConstraints g c elem bit sqrt → BitSpec c elem bit) := by
  intro h
  have hconstraints : UnfixedBitConstraints g c (-c) 0 0 := by
    unfold UnfixedBitConstraints
    refine ⟨by ring, by ring⟩
  have hspec : BitSpec c (-c) 0 := h (-c) 0 0 hconstraints
  unfold BitSpec at hspec
  -- hspec : (0 : F) = 1 ↔ IsSquare ((-c) + c)
  have hsq0 : IsSquare ((-c) + c : F) := ⟨0, by ring⟩
  exact zero_ne_one (hspec.mpr hsq0)

/-- **Surfacing the precondition.** Add `elem + c ≠ 0` (together with the
non-residue hypothesis `¬ IsSquare g` that makes the QR test meaningful) and the
spec is implied. This is exactly the assumption the unfixed circuit leans on
without stating it. -/
theorem extract_sound_of_shifted_ne_zero
    {g c elem bit sqrt : F}
    (hg : ¬ IsSquare g) (hne : elem + c ≠ 0)
    (hc : UnfixedBitConstraints g c elem bit sqrt) :
    BitSpec c elem bit := by
  obtain ⟨hbool, hbranch⟩ := hc
  have hbit : bit = 0 ∨ bit = 1 := by
    rcases mul_eq_zero.mp hbool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  unfold BitSpec
  constructor
  · -- bit = 1 ⟹ elem + c is a square (it equals sqrt^2).
    intro hb1
    subst hb1
    exact ⟨sqrt, by linear_combination -hbranch⟩
  · -- elem + c a square ⟹ bit = 1, else bit = 0 forces g to be a square.
    intro hsq
    rcases hbit with hb0 | hb1
    · exfalso
      subst hb0
      obtain ⟨t, ht⟩ := hsq
      have htne : t ≠ 0 := by
        rintro rfl
        exact hne (by rw [ht]; ring)
      have htt : t * t ≠ 0 := mul_ne_zero htne htne
      -- From the branch constraint with bit = 0: sqrt^2 = (elem + c) * g = (t*t)*g.
      have key : sqrt * sqrt = t * t * g := by
        rw [ht] at hbranch
        linear_combination hbranch
      -- Hence g = (sqrt / t)^2, contradicting ¬ IsSquare g.
      apply hg
      refine ⟨sqrt / t, ?_⟩
      have hg' : g = sqrt * sqrt / (t * t) := by
        field_simp
        linear_combination -key
      rw [hg']; ring
    · exact hb1

end Ragu.Contrib.ExtractSoundnessSpike

-- Honesty check: confirm the proofs depend on no `sorry` (no `sorryAx`).
#print axioms Ragu.Contrib.ExtractSoundnessSpike.extract_unsound
#print axioms Ragu.Contrib.ExtractSoundnessSpike.extract_sound_of_shifted_ne_zero
