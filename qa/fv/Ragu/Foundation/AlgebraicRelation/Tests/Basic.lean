import Ragu.Foundation.AlgebraicRelation

namespace Ragu.Foundation.AlgebraicRelation.Tests.Basic

open Ragu.Foundation.AlgebraicRelation

example {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    {n : Nat} (basis : Fin n → G) (coeffs : Fin n → F) :
    representationEval basis coeffs = commitGen basis coeffs :=
  representationEval_fin basis coeffs

example {F G ι : Type*} [Field F] [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} (r : AlgebraicRelationWitness (F := F) basis) :
    r.toGroupRepresentation.hEq = r.relation :=
  rfl

example {F : Type*} [Field F] (z : F) (x y : Fin 2 → F) (i : Fin 2) :
    programmedLogs z x y i = x i + z * y i :=
  rfl

example :
    independentProductPMF (PMF.uniformOfFintype Bool) (PMF.uniformOfFintype Bool) =
      PMF.uniformOfFintype (Bool × Bool) :=
  independentProductPMF_uniform

end Ragu.Foundation.AlgebraicRelation.Tests.Basic
