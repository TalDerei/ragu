import Ragu.Foundation.IPA.Halves
import Ragu.Foundation.IPA.CommitFold

/-!
Ported from `Zcash/Snark/Soundness/Ipa/Consistency.lean` at `zcash/ironwood` commit
`3c056cbebf2880b54f801c348cb67ce7dc9f2a05`. Ragu adapts the namespace and internal imports.
-/

/-!
# Folded IPA generators

`foldGens` is one IPA round's generator fold in the extractor's convention (`gLo + u⁻¹ • gHi`), used by
the IPA soundness layer (`Zcash.Snark.Soundness.Ipa.IpaSoundness`).
-/

namespace Ragu.Foundation.IPA

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The folded generators for one IPA round: `gLo + u⁻¹ • gHi`. The extractor's convention — the
witness folds by `u` (`foldVec`), so the generators fold by `u⁻¹`, the pairing under which an
accepting response is the true fold (`accepting_fold_eq_foldVec`). -/
def foldGens {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (u : F) : Fin (2 ^ k) → G :=
  loHalf g + u⁻¹ • hiHalf g

end Ragu.Foundation.IPA
