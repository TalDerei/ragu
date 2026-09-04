import Ragu.PolynomialFingerprint

/-!
# Randomized polynomial fingerprint regression tests

These executable guards pin the versioned challenge transport and the
fail-closed degree accounting independently of the cross-language diff.
-/

namespace Ragu.PolynomialFingerprint.Tests

open Ragu.PolynomialFingerprint

def seedHex : String :=
  "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"

def seed : ByteArray :=
  match parseSeed seedHex with
  | .ok bytes => bytes
  | .error _ => ByteArray.empty

#guard seed.size == 32

def parseFails (value : String) : Bool :=
  match parseSeed value with
  | .error _ => true
  | .ok _ => false

#guard parseFails ""
#guard parseFails
  "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1g"

def fpInputUnitVector : String :=
  let ctx : ChallengeContext Ragu.Core.Primes.p := ⟨seed, "unit-vector", 7⟩
  fieldHex (challengeBase ctx "input")

def fqInputUnitVector : String :=
  let ctx : ChallengeContext Ragu.Core.Primes.q := ⟨seed, "unit-vector", 7⟩
  fieldHex (challengeBase ctx "input")

#guard fpInputUnitVector ==
  "84ca68b8355db4099ed6dbec9a5269a27b382bff7463849781790f31a5c8cf20"
#guard fqInputUnitVector ==
  "76158de890f06f483d739d6475decc6b97033fabf65a8f46eb450f08a5fe2636"

abbrev TestField := F Ragu.Core.Primes.p

def testVar (index : ℕ) : Expression TestField := .var ⟨index⟩

def gateAssertion : Expression TestField :=
  .add (.mul (testVar 0) (testVar 1)) (.mul (.const (-1)) (testVar 2))

def nonlinearConstraint : Expression TestField :=
  .mul (.mul (testVar 0) (testVar 0)) (testVar 0)

def nonlinearParsed : ParsedOperations Ragu.Core.Primes.p := {
  gateAssertions := [gateAssertion]
  constraints := [nonlinearConstraint] }

#guard degreeBound 0 0 1 1 0 == 3
#guard match encodedDegree 0 nonlinearParsed [] with
  | .error _ => true
  | .ok _ => false

def mutatedGateParsed : ParsedOperations Ragu.Core.Primes.p := {
  gateAssertions := [.add gateAssertion (testVar 0)]
  constraints := [] }

#guard match encodedDegree 0 mutatedGateParsed [] with
  | .error _ => true
  | .ok _ => false

end Ragu.PolynomialFingerprint.Tests
