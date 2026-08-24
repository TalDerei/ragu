import Ragu.Meta.EndpointCensus
import Ragu.Core
import Ragu.Fingerprint.Instances
import Ragu.Fingerprint.Main
import Ragu.Circuits.Boolean.Alloc
import Ragu.Circuits.Boolean.And
import Ragu.Circuits.Boolean.ConditionalEnforceEqual
import Ragu.Circuits.Boolean.ConditionalSelect
import Ragu.Circuits.Boolean.Consistent
import Ragu.Circuits.Boolean.Decompose
import Ragu.Circuits.Core.Mul
import Ragu.Circuits.Element.Alloc
import Ragu.Circuits.Element.AllocSquare
import Ragu.Circuits.Element.Divide
import Ragu.Circuits.Element.DivNonzero
import Ragu.Circuits.Element.EnforceInvertible
import Ragu.Circuits.Element.EnforceNonzero
import Ragu.Circuits.Element.EnforceRootOfUnity
import Ragu.Circuits.Element.EnforceZero
import Ragu.Circuits.Element.Fold
import Ragu.Circuits.Element.Invert
import Ragu.Circuits.Element.Invertible
import Ragu.Circuits.Element.InvertibleConsistent
import Ragu.Circuits.Element.InvertWith
import Ragu.Circuits.Element.IsEqual
import Ragu.Circuits.Element.IsZero
import Ragu.Circuits.Element.Mul
import Ragu.Circuits.Element.Square
import Ragu.Circuits.Endoscalar.Alloc
import Ragu.Circuits.Endoscalar.Extract
import Ragu.Circuits.Endoscalar.GroupScale
import Ragu.Circuits.Endoscalar.Lift
import Ragu.Circuits.Horner.Ky
import Ragu.Circuits.NonzeroBank.Scope
import Ragu.Circuits.Point.AddIncomplete
import Ragu.Circuits.Point.AddIncompleteUnchecked
import Ragu.Circuits.Point.Alloc
import Ragu.Circuits.Point.ConditionalEndo
import Ragu.Circuits.Point.ConditionalNegate
import Ragu.Circuits.Point.Consistent
import Ragu.Circuits.Point.Double
import Ragu.Circuits.Point.DoubleAndAddIncomplete
import Ragu.Circuits.Point.DoubleAndAddIncompleteUnchecked
import Ragu.Circuits.Point.Spec
import Ragu.Circuits.Poseidon.Linear
import Ragu.Circuits.Poseidon.ParamsFp
import Ragu.Circuits.Poseidon.ParamsFq
import Ragu.Circuits.Poseidon.Permutation
import Ragu.Circuits.Poseidon.Round
import Ragu.Circuits.Poseidon.Sbox
import Ragu.Circuits.Poseidon.Sponge

/-!
# Ragu formal-verification trust boundary

Every deliverable `soundness` and `completeness` theorem is pinned directly with
`census_axioms`, which bounds its transitive kernel axioms to Lean's standard theorem tier and
rejects undisclosed compiler trust. The census also reserves protocol-level markers such as
`_error_bound`, `_finite_security`, `_prob_le`, and `_capstone` for the verifier and soundness
layers that will be added later. The two Pasta primality theorems are pinned at the same tier.

The fingerprint function and generated instance registry are executable boundary artifacts, so
they use `census_computable`: each must remain a safe, computable definition with the tighter
computable axiom budget. These checks do not prove that the trusted fingerprint encoders or
serialization assign the intended semantics, and they do not connect this gadget layer to an
unfinished Ragu verifier. Those remain separate manual and future refinement obligations.

The entries below are intentionally fully qualified and direct. Transitive coverage disappears
when a consumer is refactored and therefore does not satisfy the endpoint census.
-/

/-! ## Boolean circuits -/

census_axioms Ragu.Circuits.Boolean.Alloc.soundness
census_axioms Ragu.Circuits.Boolean.Alloc.completeness
census_axioms Ragu.Circuits.Boolean.And.soundness
census_axioms Ragu.Circuits.Boolean.And.completeness
census_axioms Ragu.Circuits.Boolean.ConditionalEnforceEqual.soundness
census_axioms Ragu.Circuits.Boolean.ConditionalEnforceEqual.completeness
census_axioms Ragu.Circuits.Boolean.ConditionalSelect.soundness
census_axioms Ragu.Circuits.Boolean.ConditionalSelect.completeness
census_axioms Ragu.Circuits.Boolean.Consistent.soundness
census_axioms Ragu.Circuits.Boolean.Consistent.completeness
census_axioms Ragu.Circuits.Boolean.Decompose.soundness
census_axioms Ragu.Circuits.Boolean.Decompose.completeness

/-! ## Core and element circuits -/

census_axioms Ragu.Circuits.Core.Mul.soundness
census_axioms Ragu.Circuits.Core.Mul.completeness
census_axioms Ragu.Circuits.Element.Alloc.soundness
census_axioms Ragu.Circuits.Element.Alloc.completeness
census_axioms Ragu.Circuits.Element.AllocSquare.soundness
census_axioms Ragu.Circuits.Element.AllocSquare.completeness
census_axioms Ragu.Circuits.Element.DivNonzero.soundness
census_axioms Ragu.Circuits.Element.DivNonzero.completeness
census_axioms Ragu.Circuits.Element.Divide.soundness
census_axioms Ragu.Circuits.Element.Divide.completeness
census_axioms Ragu.Circuits.Element.EnforceInvertible.soundness
census_axioms Ragu.Circuits.Element.EnforceInvertible.completeness
census_axioms Ragu.Circuits.Element.EnforceNonzero.soundness
census_axioms Ragu.Circuits.Element.EnforceNonzero.completeness
census_axioms Ragu.Circuits.Element.EnforceRootOfUnity.soundness
census_axioms Ragu.Circuits.Element.EnforceRootOfUnity.completeness
census_axioms Ragu.Circuits.Element.EnforceZero.soundness
census_axioms Ragu.Circuits.Element.EnforceZero.completeness
census_axioms Ragu.Circuits.Element.Fold.soundness
census_axioms Ragu.Circuits.Element.Fold.completeness
census_axioms Ragu.Circuits.Element.Invert.soundness
census_axioms Ragu.Circuits.Element.Invert.completeness
census_axioms Ragu.Circuits.Element.InvertWith.soundness
census_axioms Ragu.Circuits.Element.InvertWith.completeness
census_axioms Ragu.Circuits.Element.Invertible.soundness
census_axioms Ragu.Circuits.Element.Invertible.completeness
census_axioms Ragu.Circuits.Element.InvertibleConsistent.soundness
census_axioms Ragu.Circuits.Element.InvertibleConsistent.completeness
census_axioms Ragu.Circuits.Element.IsEqual.soundness
census_axioms Ragu.Circuits.Element.IsEqual.completeness
census_axioms Ragu.Circuits.Element.IsZero.soundness
census_axioms Ragu.Circuits.Element.IsZero.completeness
census_axioms Ragu.Circuits.Element.Mul.soundness
census_axioms Ragu.Circuits.Element.Mul.completeness
census_axioms Ragu.Circuits.Element.Square.soundness
census_axioms Ragu.Circuits.Element.Square.completeness

/-! ## Endoscalar, Horner, and nonzero-bank circuits -/

census_axioms Ragu.Circuits.Endoscalar.Alloc.soundness
census_axioms Ragu.Circuits.Endoscalar.Alloc.completeness
census_axioms Ragu.Circuits.Endoscalar.Extract.soundness
census_axioms Ragu.Circuits.Endoscalar.Extract.completeness
census_axioms Ragu.Circuits.Endoscalar.GroupScale.Step.soundness
census_axioms Ragu.Circuits.Endoscalar.GroupScale.Step.completeness
census_axioms Ragu.Circuits.Endoscalar.GroupScale.soundness
census_axioms Ragu.Circuits.Endoscalar.GroupScale.completeness
census_axioms Ragu.Circuits.Endoscalar.Lift.soundness
census_axioms Ragu.Circuits.Endoscalar.Lift.completeness
census_axioms Ragu.Circuits.Horner.Ky.soundness
census_axioms Ragu.Circuits.Horner.Ky.completeness
census_axioms Ragu.Circuits.NonzeroBank.Scope.soundness
census_axioms Ragu.Circuits.NonzeroBank.Scope.completeness

/-! ## Point circuits -/

census_axioms Ragu.Circuits.Point.AddIncomplete.soundness
census_axioms Ragu.Circuits.Point.AddIncomplete.completeness
census_axioms Ragu.Circuits.Point.AddIncompleteUnchecked.soundness
census_axioms Ragu.Circuits.Point.AddIncompleteUnchecked.completeness
census_axioms Ragu.Circuits.Point.Alloc.soundness
census_axioms Ragu.Circuits.Point.Alloc.completeness
census_axioms Ragu.Circuits.Point.ConditionalEndo.soundness
census_axioms Ragu.Circuits.Point.ConditionalEndo.completeness
census_axioms Ragu.Circuits.Point.ConditionalNegate.soundness
census_axioms Ragu.Circuits.Point.ConditionalNegate.completeness
census_axioms Ragu.Circuits.Point.Consistent.soundness
census_axioms Ragu.Circuits.Point.Consistent.completeness
census_axioms Ragu.Circuits.Point.Double.soundness
census_axioms Ragu.Circuits.Point.Double.completeness
census_axioms Ragu.Circuits.Point.DoubleAndAddIncomplete.soundness
census_axioms Ragu.Circuits.Point.DoubleAndAddIncomplete.completeness
census_axioms Ragu.Circuits.Point.DoubleAndAddIncompleteUnchecked.soundness
census_axioms Ragu.Circuits.Point.DoubleAndAddIncompleteUnchecked.completeness

/-! ## Poseidon circuits -/

census_axioms Ragu.Circuits.Poseidon.Permutation.AnyRound.soundness
census_axioms Ragu.Circuits.Poseidon.Permutation.AnyRound.completeness
census_axioms Ragu.Circuits.Poseidon.Permutation.soundness
census_axioms Ragu.Circuits.Poseidon.Permutation.completeness
census_axioms Ragu.Circuits.Poseidon.Round.Full.soundness
census_axioms Ragu.Circuits.Poseidon.Round.Full.completeness
census_axioms Ragu.Circuits.Poseidon.Round.Partial.soundness
census_axioms Ragu.Circuits.Poseidon.Round.Partial.completeness
census_axioms Ragu.Circuits.Poseidon.Sbox.soundness
census_axioms Ragu.Circuits.Poseidon.Sbox.completeness
census_axioms Ragu.Circuits.Poseidon.Sponge.Hash1.soundness
census_axioms Ragu.Circuits.Poseidon.Sponge.Hash1.completeness
census_axioms Ragu.Circuits.Poseidon.Sponge.Blocks.loop_soundness
census_axioms Ragu.Circuits.Poseidon.Sponge.Blocks.loop_completeness
census_axioms Ragu.Circuits.Poseidon.Sponge.Blocks.soundness
census_axioms Ragu.Circuits.Poseidon.Sponge.Blocks.completeness
census_axioms Ragu.Circuits.Poseidon.Sponge.Squeeze.soundness
census_axioms Ragu.Circuits.Poseidon.Sponge.Squeeze.completeness
census_axioms Ragu.Circuits.Poseidon.Sponge.Ragged.soundness
census_axioms Ragu.Circuits.Poseidon.Sponge.Ragged.completeness

/-! ## Prime-field and executable fingerprint boundary -/

census_axioms Ragu.Core.Primes.p_prime
census_axioms Ragu.Core.Primes.q_prime
census_computable Ragu.Core.Statements.FormalInstance.fingerprint +choice
census_computable Ragu.Fingerprint.instances +choice
census_computable _root_.main +choice
