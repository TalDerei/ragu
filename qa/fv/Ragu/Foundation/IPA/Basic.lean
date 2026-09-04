import Mathlib.Algebra.Group.Nat.Defs

/-!
# Uniform reference strings

The generic `URS` record is lifted from `Zcash/Arithmetic/Group.lean` at `zcash/ironwood` commit
`3c056cbebf2880b54f801c348cb67ce7dc9f2a05`. No concrete Halo2 layout, transcript schedule, proof
encoding, or verifier-key machinery is included here.
-/

namespace Ragu.Foundation.IPA

/-- A generic IPA reference string: `2^k` monomial-basis generators, a blinding generator, and an
inner-product generator. -/
structure URS (G : Type*) where
  k : ℕ
  g : Fin (2 ^ k) → G
  w : G
  u : G

end Ragu.Foundation.IPA
