import Ragu.Meta.AxiomCheck

/-!
# Environment-level trust-boundary census

Ported and adapted from `Zcash/Meta/EndpointCensus.lean` at `zcash/ironwood` commit
`3c056cbebf2880b54f801c348cb67ce7dc9f2a05`. Ragu uses project-specific endpoint names and wraps
the direct, commit-pinned CompElliptic checker; its marker-anywhere rule also closes the qualified
`_prob_le_of_...`-style escape present in that source snapshot.

The source-tree check in `scripts/check_fv_endpoint_census.sh` finds endpoint declarations that
have not been added to the trust boundary. This module enforces the complementary rule against
Lean's elaborated environment: every project-owned endpoint declaration in the import closure must
have a direct, successfully elaborated trust assertion.

`census_axioms` and `census_computable` delegate the actual trust checks to the pinned
`CompElliptic.Meta.AxiomCheck` implementation. They record the target only after that assertion
succeeds, so an unexpected axiom, `native_decide`, compiled-body override, unsafe/partial target,
or noncomputable target cannot be laundered into the endpoint census.

This is an accidental-drift guard, not a defence against a deliberately deceptive metaprogram that
mutates the persistent extension directly. Declaration-emitting metaprograms remain review-sensitive.
-/

namespace Ragu.Meta

open Lean Elab Command
open CompElliptic.Meta (nativeFlag)

/-- Names whose direct trust assertions have elaborated successfully. -/
initialize censusPinExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun names name => names.insert name
    addImportedFn := fun imported =>
      imported.foldl (init := {}) fun names moduleNames =>
        moduleNames.foldl (fun names name => names.insert name) names
  }

/-- Record a successfully checked direct trust-boundary entry. -/
def recordCensusPin (name : Name) : CommandElabM Unit :=
  modifyEnv fun env => censusPinExt.addEntry env name

/-- Resolve a census target and enforce CompElliptic's fully-qualified-name rule. -/
def resolveCensusTarget (target : Ident) : CommandElabM Name := do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  CompElliptic.Meta.checkFullyQualified target name
  return name

/-- Apply CompElliptic's theorem trust check, then record the successful direct pin. -/
elab "census_axioms " target:ident native:(nativeFlag)? : command => do
  match native with
  | some native => elabCommand (← `(command| assert_axioms $target $native))
  | none => elabCommand (← `(command| assert_axioms $target))
  recordCensusPin (← resolveCensusTarget target)

/-- Apply CompElliptic's computability check, then record the successful direct pin. -/
elab "census_computable " target:ident choice:("+choice")? native:(nativeFlag)? : command => do
  match choice, native with
  | some _, some native =>
    elabCommand (← `(command| assert_computable $target +choice $native))
  | some _, none => elabCommand (← `(command| assert_computable $target +choice))
  | none, some native => elabCommand (← `(command| assert_computable $target $native))
  | none, none => elabCommand (← `(command| assert_computable $target))
  recordCensusPin (← resolveCensusTarget target)

/-- Whether `pat` occurs anywhere in `s`. -/
def containsSubstring (s pat : String) : Bool :=
  (s.splitOn pat).length > 1

/-- Whether `marker` occurs as a whole underscore-delimited name component, optionally followed by
an apostrophe. The marker may occur anywhere: qualifying a result as `soundness_of_...` or
`circuit_completeness_at_...` must not retire its census obligation. -/
def hasEndpointMarker (s marker : String) : Bool :=
  s == marker ||
    s.startsWith (marker ++ "_") || s.startsWith (marker ++ "'") ||
    s.endsWith ("_" ++ marker) ||
    containsSubstring s ("_" ++ marker ++ "_") ||
    containsSubstring s ("_" ++ marker ++ "'")

/-- Semantic endpoint markers used by Ragu's formal circuit API and future protocol capstones. The
probability markers retain Ironwood's older spellings so a port cannot escape the census merely by
preserving its existing name. -/
def endpointMarkers : List String :=
  ["soundness", "completeness", "error_bound", "finite_security", "measure_le",
    "probability_bound", "prob_le", "capstone"]

/-- Other directly trusted endpoints that do not use a circuit-theorem marker. -/
def namedTrustEndpoints : List String :=
  ["p_prime", "q_prime", "fingerprint", "instances"]

/-- Fully qualified boundary names that are too generic to recognize by base name. -/
def exactTrustEndpoints : List Name :=
  [`main,
    `Ragu.Foundation.bindOrRelationWitness,
    `Ragu.Foundation.finForallOrRelationWitness,
    `Ragu.Foundation.finForallOption,
    `Ragu.Foundation.finForallOption_isSome_of,
    `Ragu.Foundation.boundedForallOrRelationWitness,
    `Ragu.Foundation.listForallOrRelationWitness,
    `Ragu.Foundation.Pasta.p_eq_pallasBaseCard,
    `Ragu.Foundation.Pasta.q_eq_pallasScalarCard,
    `Ragu.Foundation.Pasta.pallas_base_prime,
    `Ragu.Foundation.Pasta.pallas_scalar_prime,
    `Ragu.Foundation.Pasta.pallas_group_order,
    `Ragu.Foundation.Pasta.vesta_group_order,
    `Ragu.Foundation.Pasta.pallas_no_two_torsion,
    `Ragu.Foundation.Pasta.vesta_no_two_torsion]

/-- The base-name half of the endpoint predicate shared with
`scripts/check_fv_endpoint_census.sh`. -/
def isEndpointBaseName (name : String) : Bool :=
  namedTrustEndpoints.contains name || endpointMarkers.any (hasEndpointMarker name)

/-- Whether a fully qualified declaration name belongs to Ragu's endpoint policy. -/
def isEndpointName (name : Name) : Bool :=
  exactTrustEndpoints.contains name ||
    match name with
    | .str _ base => isEndpointBaseName base
    | _ => false

/-- Every elaborated constant kind can carry an endpoint-shaped declaration. Keeping this match
exhaustive makes a new Lean declaration kind fail closed until it is classified. -/
def isCensusKind : ConstantInfo → Bool
  | .thmInfo _ => true
  | .defnInfo _ => true
  | .axiomInfo _ => true
  | .opaqueInfo _ => true
  | .quotInfo _ => true
  | .inductInfo _ => true
  | .ctorInfo _ => true
  | .recInfo _ => true

/-- The module that declared `name`, or the module currently elaborating for a local declaration. -/
def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- Project-owned endpoint declarations with no successfully elaborated direct trust pin. -/
def unpinnedEndpoints (env : Environment) (excludeTests : Bool := true) : Array Name := Id.run do
  let pins := censusPinExt.getState env
  let mut unpinned : Array Name := #[]
  for (name, info) in env.constants.toList do
    unless isCensusKind info do continue
    if name.isInternal then continue
    unless isEndpointName name do continue
    let moduleName := moduleOf env name
    unless moduleName.getRoot == `Ragu do continue
    if excludeTests && (`Ragu.Meta.Tests).isPrefixOf moduleName then continue
    unless pins.contains name do unpinned := unpinned.push name
  return unpinned.qsort Name.lt

/-- Fail unless every endpoint in the elaborated import closure has a direct trust assertion. -/
elab "assert_endpoint_census" : command => do
  let unpinned := unpinnedEndpoints (← getEnv)
  unless unpinned.isEmpty do
    throwError "endpoint declaration(s) with no direct census_axioms/census_computable entry in \
      the elaborated import closure: {unpinned.toList}"

end Ragu.Meta
