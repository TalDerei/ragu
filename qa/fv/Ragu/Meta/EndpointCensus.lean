import Ragu.Meta.AxiomCheck

/-!
# Environment-level trust-boundary census

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
elab "census_axioms " target:ident : command => do
  elabCommand (← `(command| assert_axioms $target))
  recordCensusPin (← resolveCensusTarget target)

/-- Apply CompElliptic's computability check, then record the successful direct pin. -/
elab "census_computable " target:ident choice:("+choice")? : command => do
  if choice.isSome then
    elabCommand (← `(command| assert_computable $target +choice))
  else
    elabCommand (← `(command| assert_computable $target))
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

/-- The endpoint predicate shared with `scripts/check_fv_endpoint_census.sh`. -/
def isEndpointBaseName (name : String) : Bool :=
  namedTrustEndpoints.contains name || endpointMarkers.any (hasEndpointMarker name)

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
    let some base := (match name with | .str _ base => some base | _ => none) | continue
    unless isEndpointBaseName base do continue
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
