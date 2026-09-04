import Ragu.Foundation.Oracle.OracleComp

/-!
Ported from `Zcash/Common/Oracle/WithReads.lean` at `zcash/ironwood` commit
`3c056cbebf2880b54f801c348cb67ce7dc9f2a05`. Ragu adapts only the namespace and internal import.
-/

/-!
# Returning a run's own reads with its output

`withReads` runs a machine, re-queries a designated family of points of its output, and returns
the output with those answers.  The wrapped output then determines everything the deployed accept
events read, and the query bound grows only by the family's size.
-/

namespace Ragu.Foundation.Oracle.OracleComp

variable {T F α : Type*}

/-- Query a `Fin`-indexed family of points and return their answers. -/
def readFin : ∀ {n : ℕ}, (Fin n → T) → OracleComp T F (Fin n → F)
  | 0, _ => .pure Fin.elim0
  | _ + 1, ts => .query (ts 0) fun v =>
      (readFin fun i => ts i.succ).bind fun vs => .pure (Fin.cons v vs)

@[simp] theorem run_readFin : ∀ {n : ℕ} (ts : Fin n → T) (O : T → F),
    (readFin (F := F) ts).run O = fun i => O (ts i)
  | 0, ts, O => funext fun i => i.elim0
  | n + 1, ts, O => by
      simp only [readFin, run_query, run_bind, run_pure,
        run_readFin (fun i => ts i.succ) O]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]
      · rw [Fin.cons_succ]

/-- The finite reader's query log is exactly the supplied point vector. -/
@[simp] theorem queries_readFin : ∀ {n : ℕ} (ts : Fin n → T) (O : T → F),
    (readFin (F := F) ts).queries O = List.ofFn ts
  | 0, ts, O => by
      simp [readFin, OracleComp.queries]
  | n + 1, ts, O => by
      simp only [readFin, OracleComp.queries, OracleComp.queries_bind, queries_readFin,
        List.append_nil]
      rw [List.ofFn_succ]

/-- The reader queries one point per index. -/
theorem queryBound_readFin : ∀ {n : ℕ} (ts : Fin n → T),
    (readFin (F := F) ts).QueryBound n
  | 0, _ => .pure _ _
  | n + 1, ts => by
      have hk : ∀ v : F, ((readFin fun i => ts i.succ).bind fun vs =>
          (.pure (Fin.cons v vs) : OracleComp T F (Fin (n + 1) → F))).QueryBound n :=
        fun v => (queryBound_bind (queryBound_readFin fun i => ts i.succ)
          (fun vs => QueryBound.pure _ 0)).mono (by omega)
      exact QueryBound.query hk

/-- Run the machine, re-query `pts` of its output, and return the output with those answers. -/
def withReads {n : ℕ} (pts : α → Fin n → T) (A : OracleComp T F α) :
    OracleComp T F (α × (Fin n → F)) :=
  A.bind fun p => (readFin (pts p)).bind fun vs => .pure (p, vs)

/-- The wrapped run is the original output paired with its designated reads. -/
@[simp] theorem run_withReads {n : ℕ} (pts : α → Fin n → T) (A : OracleComp T F α)
    (O : T → F) :
    (A.withReads pts).run O = (A.run O, fun i => O (pts (A.run O) i)) := by
  rw [withReads, run_bind, run_bind, run_readFin, run_pure]

/-- The wrapped machine adds one query per designated point. -/
theorem queryBound_withReads {n : ℕ} (pts : α → Fin n → T) {A : OracleComp T F α} {Q : ℕ}
    (hA : A.QueryBound Q) : (A.withReads pts).QueryBound (Q + n) := by
  have hf : ∀ p, ((readFin (pts p)).bind fun vs =>
      (.pure (p, vs) : OracleComp T F (α × (Fin n → F)))).QueryBound n :=
    fun p => (queryBound_bind (queryBound_readFin (pts p))
      (fun vs => QueryBound.pure _ 0)).mono (by omega)
  exact queryBound_bind hA hf

end Ragu.Foundation.Oracle.OracleComp
