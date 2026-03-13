import Clean.Circuit
import Ragu.Core

namespace Ragu.Circuits.Point.Spec
open Core.Primes
variable {p : ℕ} [Fact p.Prime]

structure Point (F : Type) where
  x : F
  y : F
deriving ProvableStruct

/--
  Short Weierstrass curves with a = 0.

  `h_small_order` is a proof that the element ζ has order 3 in the base field
-/
structure CurveParams (base_p : ℕ) where
  b : F base_p
  ζ : F base_p
  h_small_order : ζ^3 = 1

def Point.isOnCurve (point : Point (F p)) (curveParams : CurveParams p) : Prop :=
  point.y^2 = point.x^3 + curveParams.b

def CurveParams.noOrderTwoPoints (curveParams : CurveParams p) : Prop :=
  (∀ point : Spec.Point (F p), (point.isOnCurve curveParams) → point.y ≠ 0)


def Point.negate (point : Point (F p)) : Point (F p) :=
  {
    x := point.x,
    y := -point.y
  }

def Point.double (point : Point (F p)) : Option (Point (F p)) :=
  -- a / 0 is defined to be 0 for fields, therefore to make the spec precise
  -- we return None if point.y is zero
  if point.y = 0 then none else
  let lambda := (3 * point.x^2) / (2 * point.y)
  let x2 := lambda^2 - 2*point.x
  some {
    x := x2,
    y := lambda * (point.x - x2) - point.y
  }

-- concrete pasta curves parameters
def EpAffineParams: Circuits.Point.Spec.CurveParams Core.Primes.p :=
{
  b := 5,
  ζ := 0x12ccca834acdba712caad5dc57aab1b01d1f8bd237ad31491dad5ebdfdfe4ab9,
  h_small_order := by native_decide
}

end Ragu.Circuits.Point.Spec

namespace Ragu.Circuits.Point.Lemmas
variable {p : ℕ} [Fact p.Prime] [NeZero (2 : F p)]
open Spec

lemma double_preserves_membership (point : Point (F p)) (curveParams: CurveParams p)
    (h_membership: point.isOnCurve curveParams) (h_order : curveParams.noOrderTwoPoints) :
    match point.double with
    | none =>
      -- this is impossible: since we assume that the curve does not have points of order two,
      -- every affine point has an affine double
      False
    | some double => double.isOnCurve curveParams := by
  simp only [CurveParams.noOrderTwoPoints] at h_order
  specialize h_order point h_membership
  simp only [Point.double, if_neg h_order, Point.isOnCurve]
  simp only [Point.isOnCurve] at h_membership
  have h2 : (2 : F p) ≠ 0 := NeZero.ne 2
  have h2y : (2 : F p) * point.y ≠ 0 := mul_ne_zero h2 h_order
  field_simp [h_order, h2y, h2]
  have hb : curveParams.b = point.y ^ 2 - point.x ^ 3 := by rw [h_membership]; ring
  rw [hb]
  ring


end Ragu.Circuits.Point.Lemmas
