import Ragu.Foundation.IPA

namespace Ragu.Foundation.IPA.Tests.Basic

open Ragu.Foundation.IPA

def urs0 : URS ℚ where
  k := 0
  g := fun _ => 2
  w := 3
  u := 4

example : commit urs0 (fun _ => (5 : ℚ)) = (10 : ℚ) := by
  simp [commit, urs0]
  norm_num

example {α : Type*} {k : ℕ} (a : Fin (2 ^ (k + 1)) → α) :
    append (loHalf a) (hiHalf a) = a :=
  append_loHalf_hiHalf a

example {F : Type*} [Field F] {m : ℕ} (lo hi : Fin m → F) (u : F) :
    foldVec lo hi u = lo + u • hi :=
  rfl

example {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (a : Fin (2 ^ urs.k) → F) :
    commit urs a = Ragu.Foundation.AlgebraicRelation.commitGen urs.g a :=
  commit_eq_commitGen urs a

end Ragu.Foundation.IPA.Tests.Basic
