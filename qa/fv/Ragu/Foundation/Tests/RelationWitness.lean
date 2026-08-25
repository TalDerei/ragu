import Ragu.Foundation.RelationWitness

/-!
# Regression tests for computed outcome traversal

These checks pin left-value mapping, right-value preservation, left-to-right first-break order, and
the exact certificates returned by finite `Option` traversal.
-/

namespace Ragu.Foundation.Tests.RelationWitness

open Ragu.Foundation

#guard
  match bindOrRelationWitness (PSum.inl 4 : Nat ⊕' String) (fun n => n + 1) with
  | .inl value => value == 5
  | .inr _ => false

#guard
  match bindOrRelationWitness (PSum.inr "gap" : Nat ⊕' String) (fun n => n + 1) with
  | .inl _ => false
  | .inr gap => gap == "gap"

def finOutcomes (i : Fin 4) : Nat ⊕' String :=
  if i.val = 1 then PSum.inr "first"
  else if i.val = 2 then PSum.inr "second"
  else PSum.inl i.val

#guard
  match finForallOrRelationWitness finOutcomes with
  | .inl _ => false
  | .inr gap => gap == "first"

#guard
  match finForallOption (fun i : Fin 3 => some (i.val + 10)) with
  | none => false
  | some values => values 0 == 10 && values 1 == 11 && values 2 == 12

#guard
  match finForallOption (fun i : Fin 3 => if i.val = 1 then none else some i.val) with
  | none => true
  | some _ => false

example : (finForallOption (fun i : Fin 3 => some (i.val + 10))).isSome :=
  finForallOption_isSome_of _ (fun _ => rfl)

def boundedOutcomes (i : Nat) (_hi : i < 4) : Nat ⊕' String :=
  if i = 2 then PSum.inr "bounded"
  else PSum.inl i

#guard
  match boundedForallOrRelationWitness boundedOutcomes with
  | .inl _ => false
  | .inr gap => gap == "bounded"

def listOutcomes (x : Nat) (_hx : x ∈ [0, 1, 2]) : True ⊕' String :=
  if x = 1 then PSum.inr "first"
  else if x = 2 then PSum.inr "second"
  else PSum.inl True.intro

#guard
  match listForallOrRelationWitness [0, 1, 2] listOutcomes with
  | .inl _ => false
  | .inr gap => gap == "first"

end Ragu.Foundation.Tests.RelationWitness
