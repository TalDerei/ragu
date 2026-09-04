import Ragu.Foundation.Oracle

namespace Ragu.Foundation.Oracle.Tests.Basic

open Ragu.Foundation.Oracle

def oneQuery : OracleComp Bool Nat Nat :=
  .query true .pure

example : oneQuery.run (fun b => if b then 7 else 0) = 7 := by
  simp [oneQuery, OracleComp.run]

example : oneQuery.queries (fun _ => 7) = [true] := by
  simp [oneQuery, OracleComp.queries]

example : oneQuery.QueryBound 1 := by
  exact .query fun _ => .pure _ _

def labeledQuery : LabeledOracleComp Bool Nat (fun _ => Unit) Nat :=
  .query true () .pure

example : labeledQuery.run (fun b => if b then 9 else 0) = 9 := by
  simp [labeledQuery, LabeledOracleComp.run, LabeledOracleComp.erase, OracleComp.run]

def twoSpec : OracleSpec Bool where
  domain := fun _ => Bool
  range := fun _ => Nat

def multiQuery : MultiOracleComp twoSpec Nat :=
  .query true false .pure

def multiTable (i : Bool) (_ : twoSpec.domain i) : twoSpec.range i := by
  change Nat
  exact if i then 11 else 5

example : multiQuery.runTables multiTable = 11 := by
  simp [multiQuery, multiTable, MultiOracleComp.runTables]

example : (OracleComp.readFin (F := Nat) (fun i : Fin 2 => i == 0)).run
    (fun b => if b then 3 else 4) = fun i => if i == 0 then 3 else 4 := by
  simp

end Ragu.Foundation.Oracle.Tests.Basic
