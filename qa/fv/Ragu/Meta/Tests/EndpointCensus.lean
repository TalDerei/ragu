import Ragu.Meta.EndpointCensus

/-!
# Endpoint-census regression tests

Ported and adapted from `Zcash/Meta/Tests/EndpointCensus.lean` at `zcash/ironwood` commit
`3c056cbebf2880b54f801c348cb67ce7dc9f2a05`. The qualified-marker, exact-root endpoint, and
`census_* +native(...)` cases are Ragu-specific extensions.
-/

namespace Ragu.Meta.Tests.EndpointCensus

/-- Forged qualified soundness endpoint used to exercise the unpinned census path. -/
theorem soundness_of_unpinned : True := by trivial

/-- Forged qualified completeness endpoint used to exercise definition discovery. -/
def circuit_completeness_at_unpinned : Bool := true

/-- Forged axiom endpoint used to exercise axiom declaration discovery. -/
axiom axiom_soundness : True

/-- Forged opaque endpoint used to exercise non-theorem declaration discovery. -/
opaque opaque_soundness : Bool := true

/-- Forged inductive endpoint used to exercise declaration-kind completeness. -/
inductive forged_completeness where
  | witness

/-- Forged structure endpoint; structures elaborate as inductive declarations. -/
structure structure_completeness : Prop where
  proof : True

/-- Carrier whose endpoint-shaped constructor exercises constructor discovery. -/
inductive ConstructorCarrier : Prop where
  | constructor_soundness

/-- A similarly spelled non-endpoint: `soundness` is not a whole name component. -/
theorem unsoundness : True := by trivial

/-- A similarly spelled non-endpoint: the marker is followed by an alphanumeric character. -/
def soundnessHelper : Bool := true

/-- A test endpoint whose computability pin must remove it from the unpinned set. -/
def pinned_soundness : Bool := true

census_computable Ragu.Meta.Tests.EndpointCensus.pinned_soundness

/-- A test endpoint whose theorem pin must remove it from the unpinned set. -/
theorem pinned_completeness_of_case : True := by trivial

census_axioms Ragu.Meta.Tests.EndpointCensus.pinned_completeness_of_case

/-- A native theorem pin exercises forwarding of Ironwood's exact owner allowance. -/
theorem pinned_native_soundness : (123456 : Nat) < 123457 := by native_decide

census_axioms Ragu.Meta.Tests.EndpointCensus.pinned_native_soundness +native(
  Ragu.Meta.Tests.EndpointCensus.pinned_native_soundness)

/-- A computed test value with an owned native certificate and no choice allowance. -/
structure NativeCertificate where
  value : Nat
  small : value < 123457

def pinned_native_only_completeness : NativeCertificate where
  value := 123456
  small := pinned_native_soundness

census_computable Ragu.Meta.Tests.EndpointCensus.pinned_native_only_completeness +native(
  Ragu.Meta.Tests.EndpointCensus.pinned_native_soundness)

/-- A computed test value with both erased choice and an owned native certificate. -/
structure NativeChoiceCertificate where
  value : Nat
  small : value < 123457
  erased : True

def pinned_native_completeness : NativeChoiceCertificate where
  value := 123456
  small := pinned_native_soundness
  erased := Classical.choice (show Nonempty True from ⟨True.intro⟩)

census_computable Ragu.Meta.Tests.EndpointCensus.pinned_native_completeness +choice +native(
  Ragu.Meta.Tests.EndpointCensus.pinned_native_soundness)

#guard Ragu.Meta.isEndpointBaseName "soundness"
#guard Ragu.Meta.isEndpointBaseName "soundness_of_qualified_result"
#guard Ragu.Meta.isEndpointBaseName "circuit_completeness_at_instance"
#guard Ragu.Meta.isEndpointBaseName "circuit_soundness'"
#guard Ragu.Meta.isEndpointBaseName "binding_prob_le_of_assumption"
#guard Ragu.Meta.isEndpointBaseName "deployment_finite_security_at_consensus_max"
#guard Ragu.Meta.isEndpointBaseName "recursive_verifier_capstone"
#guard !Ragu.Meta.isEndpointBaseName "unsoundness"
#guard !Ragu.Meta.isEndpointBaseName "soundnessHelper"
#guard !Ragu.Meta.isEndpointBaseName "binding_prob_lemma"
#guard Ragu.Meta.isEndpointName `main
#guard !Ragu.Meta.isEndpointName `Ragu.Meta.Tests.EndpointCensus.main
#guard Ragu.Meta.isEndpointName `Ragu.Foundation.bindOrRelationWitness
#guard Ragu.Meta.isEndpointName `Ragu.Foundation.Pasta.pallas_group_order
#guard Ragu.Meta.isEndpointName `Ragu.Foundation.Probability.PMFEventBiasLE.bind_average
#guard Ragu.Meta.isEndpointName `Ragu.Foundation.Oracle.MultiOracleComp.runFreshPMF_eventBiasLE
#guard Ragu.Meta.isEndpointName `Ragu.Foundation.AlgebraicRelation.programmedExtractOrMiss

run_cmd do
  let env ← Lean.getEnv
  let production := Ragu.Meta.unpinnedEndpoints env
  unless production.isEmpty do
    throwError "test declarations escaped the production exclusion: {production.toList}"

  let unpinned := Ragu.Meta.unpinnedEndpoints env (excludeTests := false)
  let expected := #[
    `Ragu.Meta.Tests.EndpointCensus.soundness_of_unpinned,
    `Ragu.Meta.Tests.EndpointCensus.circuit_completeness_at_unpinned,
    `Ragu.Meta.Tests.EndpointCensus.axiom_soundness,
    `Ragu.Meta.Tests.EndpointCensus.opaque_soundness,
    `Ragu.Meta.Tests.EndpointCensus.forged_completeness,
    `Ragu.Meta.Tests.EndpointCensus.structure_completeness,
    `Ragu.Meta.Tests.EndpointCensus.ConstructorCarrier.constructor_soundness
  ].qsort Lean.Name.lt
  unless unpinned == expected do
    throwError "expected exactly the forged endpoints unpinned, got {unpinned.toList}; expected \
      {expected.toList}"

assert_endpoint_census

end Ragu.Meta.Tests.EndpointCensus
