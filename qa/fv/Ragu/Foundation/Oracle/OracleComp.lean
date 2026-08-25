import Ragu.Foundation.Probability.Uniform

/-!
Ported from `Zcash/Common/Oracle/OracleComp.lean` at `zcash/ironwood` commit
`3c056cbebf2880b54f801c348cb67ce7dc9f2a05`. Ragu adapts the namespace and uniform-measure import,
drops the source's unused Fiat-Shamir Execution import, and renames one proof-local variable for
the repository spellcheck.
-/

/-!
# The oracle-querying Fiat–Shamir adversary

Model a `Q`-query adversary as an adaptive query tree with eager whole-table semantics. Query
logs support resource accounting; blind escape sets give the adaptive query loss.
-/

namespace Ragu.Foundation.Oracle

open scoped ENNReal
open Ragu.Foundation.Probability

/-- An adaptive computation with one oracle `T → F`: either a result or a query whose continuation
receives the answer. -/
inductive OracleComp (T F α : Type*) where
  | pure (a : α)
  | query (t : T) (k : F → OracleComp T F α)

namespace OracleComp

variable {T F α : Type*}

/-- Run the machine against an oracle table `O`, answering each query by lookup (the eager/whole-table
semantics: drawing `O` uniformly makes every fresh answer uniform). -/
def run : OracleComp T F α → (T → F) → α
  | .pure a, _ => a
  | .query t k, O => (k (O t)).run O

@[simp] theorem run_pure (a : α) (O : T → F) : (pure a : OracleComp T F α).run O = a := rfl

@[simp] theorem run_query (t : T) (k : F → OracleComp T F α) (O : T → F) :
    (query t k).run O = (k (O t)).run O := rfl

/-- The query log of a run: the points the machine asks, in order, on the path the table induces. -/
def queries : OracleComp T F α → (T → F) → List T
  | .pure _, _ => []
  | .query t k, O => t :: (k (O t)).queries O

/-- Reprogramming a point that a computation did not query leaves its result unchanged. -/
theorem run_update_of_not_mem_queries [DecidableEq T]
    (A : OracleComp T F α) (O : T → F) (t : T) (v : F)
    (hfresh : t ∉ A.queries O) :
    A.run (Function.update O t v) = A.run O := by
  induction A with
  | pure a => rfl
  | query q k ih =>
      simp only [queries, List.mem_cons, not_or] at hfresh
      have hqt : q ≠ t := Ne.symm hfresh.1
      rw [run_query, run_query, Function.update_apply, if_neg hqt]
      exact ih (O q) hfresh.2

/-- Two tables agreeing on every point a computation queries produce the same run and the same
query log. -/
theorem run_congr_of_agree {T F α : Type*} (A : OracleComp T F α)
    (O O' : T → F) (h : ∀ t ∈ A.queries O, O t = O' t) :
    A.run O = A.run O' ∧ A.queries O = A.queries O' := by
  induction A with
  | pure a => exact ⟨rfl, rfl⟩
  | query t k ih =>
      have ht : O t = O' t := h t (by simp [OracleComp.queries])
      obtain ⟨hr, hq⟩ := ih (O t) (fun u hu => h u (by simp [OracleComp.queries, hu]))
      constructor
      · rw [OracleComp.run_query, OracleComp.run_query, ← ht, hr]
      · rw [OracleComp.queries, OracleComp.queries, ← ht, hq]

/-- The machine makes at most `Q` queries on every path (VCVio's structural `IsQueryBound`). The
Fiat–Shamir reductions charge their query loss against this `Q`. -/
inductive QueryBound : OracleComp T F α → ℕ → Prop
  | pure (a : α) (Q : ℕ) : QueryBound (.pure a) Q
  | query {t : T} {k : F → OracleComp T F α} {Q : ℕ}
      (h : ∀ u, QueryBound (k u) Q) : QueryBound (.query t k) (Q + 1)

/-- A query bound is monotone: a machine within budget `Q` is within any larger budget. -/
theorem QueryBound.mono {A : OracleComp T F α} {Q Q' : ℕ} (h : QueryBound A Q) (hle : Q ≤ Q') :
    QueryBound A Q' := by
  induction h generalizing Q' with
  | pure a _ => exact .pure a Q'
  | query _ ih =>
      obtain ⟨Q'', rfl⟩ : ∃ Q'', Q' = Q'' + 1 := ⟨Q' - 1, by omega⟩
      exact .query fun u => ih u (by omega)

/-- A `Q`-bounded machine's query log has length at most `Q`, on every table. -/
theorem queries_length_le {A : OracleComp T F α} {Q : ℕ} (h : QueryBound A Q) (O : T → F) :
    (A.queries O).length ≤ Q := by
  induction h with
  | pure => exact Nat.zero_le _
  | query h ih => simpa [queries] using Nat.succ_le_succ (ih _)


/-- Some query answer lies in a table-dependent escape set that is blind at that query point. -/
def escapesDuringC (esc : T → (T → F) → Set F) : OracleComp T F α → (T → F) → Prop
  | .pure _, _ => False
  | .query t k, O => O t ∈ esc t O ∨ (k (O t)).escapesDuringC esc O

/-- The machine avoids cached points and makes no repeated query on a path. -/
inductive AvoidsCache [DecidableEq T] : List (T × F) → OracleComp T F α → Prop
  | pure (c : List (T × F)) (a : α) : AvoidsCache c (.pure a)
  | query {c : List (T × F)} {t : T} {k : F → OracleComp T F α}
      (ht : t ∉ c.map Prod.fst) (h : ∀ u, AvoidsCache ((t, u) :: c) (k u)) :
      AvoidsCache c (.query t k)

/-- Answer cached queries locally and issue each fresh query once. -/
def dedup [DecidableEq T] (c : List (T × F)) : OracleComp T F α → OracleComp T F α
  | .pure a => .pure a
  | .query t k =>
      match (c.find? (fun p => p.1 = t)) with
      | some p => dedup c (k p.2)
      | none => .query t (fun u => dedup ((t, u) :: c) (k u))

/-- Deduplication preserves lookup-table execution when the initial cache agrees with the table.
In particular, `dedup []` changes only the query schedule, never the result. -/
theorem run_dedup [DecidableEq T] (A : OracleComp T F α) (O : T → F)
    (c : List (T × F)) (hcon : ∀ p ∈ c, O p.1 = p.2) :
    (dedup c A).run O = A.run O := by
  induction A generalizing c with
  | pure a => rfl
  | query t k ih =>
      rw [dedup]
      cases hfind : c.find? (fun p => p.1 = t) with
      | some p =>
          have hp := List.find?_some hfind
          have hpmem := List.mem_of_find?_eq_some hfind
          have hpt : p.1 = t := by simpa using hp
          have hval : O t = p.2 := by
            rw [← hpt]
            exact hcon p hpmem
          rw [run_query, ih p.2 c hcon, hval]
      | none =>
          rw [run_query, run_query]
          exact ih (O t) ((t, O t) :: c) fun p hp ↦ by
            rcases List.mem_cons.mp hp with rfl | hp
            · rfl
            · exact hcon p hp

theorem dedup_avoidsCache [DecidableEq T] (c : List (T × F)) (A : OracleComp T F α) :
    AvoidsCache c (dedup c A) := by
  induction A generalizing c with
  | pure a => exact .pure c a
  | query t k ih =>
      rw [dedup]
      cases hfind : c.find? (fun p => p.1 = t) with
      | some p => exact ih p.2 c
      | none =>
          refine .query ?_ (fun u => ih u ((t, u) :: c))
          intro hmem
          obtain ⟨p, hp, hpt⟩ := List.mem_map.mp hmem
          have := List.find?_eq_none.mp hfind p hp
          simp [hpt] at this

theorem dedup_queryBound [DecidableEq T] {A : OracleComp T F α} {Q : ℕ}
    (h : A.QueryBound Q) (c : List (T × F)) : (dedup c A).QueryBound Q := by
  induction h generalizing c with
  | pure a Q => exact .pure a Q
  | @query t k Q hk ih =>
      rw [dedup]
      cases hfind : c.find? (fun p => p.1 = t) with
      | some p => exact (ih p.2 c).mono (Nat.le_succ Q)
      | none => exact .query (fun u => ih u ((t, u) :: c))

/-- Deduplication preserves escapes when the cache is table-consistent and contains no escaping
answer. -/
theorem escapesDuringC_dedup [DecidableEq T] (esc : T → (T → F) → Set F) {A : OracleComp T F α}
    {O : T → F} {c : List (T × F)}
    (hcon : ∀ p ∈ c, O p.1 = p.2) (hesc : ∀ p ∈ c, O p.1 ∉ esc p.1 O)
    (h : A.escapesDuringC esc O) : (dedup c A).escapesDuringC esc O := by
  induction A generalizing c with
  | pure a => exact h
  | query t k ih =>
      rw [dedup]
      cases hfind : c.find? (fun p => p.1 = t) with
      | some p =>
          have hp := List.find?_some hfind
          have hpmem := List.mem_of_find?_eq_some hfind
          have hpt : p.1 = t := by simpa using hp
          subst hpt
          have hval : O p.1 = p.2 := hcon p hpmem
          rcases h with h | h
          · exact absurd h (hesc p hpmem)
          · show (dedup c (k p.2)).escapesDuringC esc O
            rw [← hval]
            exact ih (O p.1) hcon hesc h
      | none =>
          by_cases hO : O t ∈ esc t O
          · exact Or.inl hO
          · rcases h with h | h
            · exact absurd h hO
            · refine Or.inr (ih (O t) ?_ ?_ h)
              · intro p hp
                rcases List.mem_cons.mp hp with hp | hp
                · subst hp; rfl
                · exact hcon p hp
              · intro p hp
                rcases List.mem_cons.mp hp with hp | hp
                · subst hp; exact hO
                · exact hesc p hp


variable {β : Type*}

/-- Sequence two machines: run the first, feed its result to the second. -/
def bind : OracleComp T F α → (α → OracleComp T F β) → OracleComp T F β
  | .pure a, f => f a
  | .query t k, f => .query t (fun u => (k u).bind f)

@[simp] theorem run_bind (A : OracleComp T F α) (f : α → OracleComp T F β) (O : T → F) :
    (A.bind f).run O = ((f (A.run O)).run O) := by
  induction A with
  | pure a => rfl
  | query t k ih => exact ih (O t)

/-- Query a list of points in order, ignoring the answers, and return `p`. -/
def queryList (p : α) : List T → OracleComp T F α
  | [] => .pure p
  | t :: ts => .query t (fun _ => queryList p ts)

@[simp] theorem run_queryList (p : α) (ts : List T) (O : T → F) :
    (queryList p ts).run O = p := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact ih

theorem queryBound_bind {A : OracleComp T F α} {f : α → OracleComp T F β} {Q Q' : ℕ}
    (hA : A.QueryBound Q) (hf : ∀ a, (f a).QueryBound Q') : (A.bind f).QueryBound (Q + Q') := by
  induction hA with
  | pure a Q => exact (hf a).mono (Nat.le_add_left _ _)
  | @query t k Q h ih =>
      have : (OracleComp.query t k).bind f = .query t (fun u => (k u).bind f) := rfl
      rw [this, Nat.succ_add]
      exact .query fun u => ih u

theorem queryBound_queryList (p : α) (ts : List T) :
    (queryList (F := F) p ts).QueryBound ts.length := by
  induction ts with
  | nil => exact .pure p 0
  | cons t ts ih => exact .query fun _ => ih

/-- An escape inside the second machine is an escape of the sequence. -/
theorem escapesDuringC_bind_right (esc : T → (T → F) → Set F) {A : OracleComp T F α}
    {f : α → OracleComp T F β} {O : T → F}
    (h : (f (A.run O)).escapesDuringC esc O) : (A.bind f).escapesDuringC esc O := by
  induction A with
  | pure a => exact h
  | query t k ih => exact Or.inr (ih (O t) h)

/-- An escaping answer at some listed point is an escape of the listing run. -/
theorem escapesDuringC_queryList (esc : T → (T → F) → Set F) (p : α) {ts : List T} {O : T → F}
    {t : T} (ht : t ∈ ts) (h : O t ∈ esc t O) : (queryList p ts).escapesDuringC esc O := by
  induction ts with
  | nil => exact absurd ht (List.not_mem_nil)
  | cons t' ts ih =>
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact Or.inl h
      · exact Or.inr (ih hmem)

/-- Run a machine, query every round prefix of its output, and return that output unchanged. -/
def completing {P : Type*} {k : ℕ} (prefixes : P → Fin k → T) (A : OracleComp T F P) :
    OracleComp T F P :=
  A.bind fun p => queryList p (List.ofFn (prefixes p))

@[simp] theorem run_completing {P : Type*} {k : ℕ} (prefixes : P → Fin k → T)
    (A : OracleComp T F P) (O : T → F) : (A.completing prefixes).run O = A.run O := by
  rw [completing, run_bind, run_queryList]

theorem queryBound_completing {P : Type*} {k : ℕ} (prefixes : P → Fin k → T)
    {A : OracleComp T F P} {Q : ℕ} (hA : A.QueryBound Q) :
    (A.completing prefixes).QueryBound (Q + k) := by
  refine queryBound_bind hA fun p => ?_
  have h := queryBound_queryList (F := F) p (List.ofFn (prefixes p))
  rwa [List.length_ofFn] at h

/-- An escaping answer at one of the output's own prefixes is an escape of the completed run. -/
theorem escapesDuringC_completing (esc : T → (T → F) → Set F) {P : Type*} {k : ℕ}
    (prefixes : P → Fin k → T) {A : OracleComp T F P} {O : T → F} {j : Fin k}
    (h : O (prefixes (A.run O) j) ∈ esc (prefixes (A.run O) j) O) :
    (A.completing prefixes).escapesDuringC esc O :=
  escapesDuringC_bind_right esc
    (escapesDuringC_queryList esc _ (by exact List.mem_ofFn.mpr ⟨j, rfl⟩) h)

/-- Sequencing concatenates the query logs. -/
theorem queries_bind (A : OracleComp T F α) (f : α → OracleComp T F β) (O : T → F) :
    (A.bind f).queries O = A.queries O ++ (f (A.run O)).queries O := by
  induction A with
  | pure a => rfl
  | query t k ih =>
      show t :: ((k (O t)).bind f).queries O
          = (t :: (k (O t)).queries O) ++ (f ((OracleComp.query t k).run O)).queries O
      rw [run_query, List.cons_append, ih (O t)]

/-- A list-query pass queries exactly its list. -/
theorem queries_queryList (p : α) (ts : List T) (O : T → F) :
    (queryList (F := F) p ts).queries O = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      show t :: _ = _
      rw [ih]

/-- The completed run queries every one of the output's own round prefixes. -/
theorem mem_queries_completing {P : Type*} {k : ℕ} (prefixes : P → Fin k → T)
    (A : OracleComp T F P) (O : T → F) (j : Fin k) :
    prefixes (A.run O) j ∈ (A.completing prefixes).queries O := by
  rw [completing, queries_bind, List.mem_append]
  right
  rw [queries_queryList]
  exact List.mem_ofFn.mpr ⟨j, rfl⟩


/-- Fix the junk table and retain only queries to the game domain. -/
def restrictSum {J : Type*} (j : J → F) : OracleComp (T ⊕ J) F α → OracleComp T F α
  | .pure a => .pure a
  | .query (Sum.inl t) k => .query t (fun u => restrictSum j (k u))
  | .query (Sum.inr x) k => restrictSum j (k (j x))

/-- The restriction's run against `O` is the original run against `O` with the junk table glued
on. -/
theorem run_restrictSum {J : Type*} (j : J → F) :
    (A : OracleComp (T ⊕ J) F α) → (O : T → F) →
    (restrictSum j A).run O = A.run (Sum.elim O j)
  | .pure _, _ => rfl
  | .query (Sum.inl t) k, O => run_restrictSum j (k (O t)) O
  | .query (Sum.inr x) k, O => run_restrictSum j (k (j x)) O

/-- Restriction never adds queries: the junk answers are read from the fixed table for free. -/
theorem queryBound_restrictSum {J : Type*} {A : OracleComp (T ⊕ J) F α} {Q : ℕ}
    (h : A.QueryBound Q) (j : J → F) : (restrictSum j A).QueryBound Q := by
  induction h with
  | pure a Q => exact .pure a Q
  | @query t k Q hk ih =>
      cases t with
      | inl t => exact .query fun u => ih u
      | inr x => exact (ih (j x)).mono (Nat.le_succ Q)


/-! ## Domain reindexing, reachable support, and restriction -/

variable {T' : Type*}

/-- Reindex a machine's query points. -/
def mapDomain (f : T → T') : OracleComp T F α → OracleComp T' F α
  | .pure a => .pure a
  | .query t k => .query (f t) fun u => (k u).mapDomain f

@[simp] theorem run_mapDomain (f : T → T') :
    (A : OracleComp T F α) → (O : T' → F) → (A.mapDomain f).run O = A.run (O ∘ f)
  | .pure _, _ => rfl
  | .query t k, O => run_mapDomain f (k (O (f t))) O

theorem queryBound_mapDomain (f : T → T') {A : OracleComp T F α} {Q : ℕ}
    (h : A.QueryBound Q) : (A.mapDomain f).QueryBound Q := by
  induction h with
  | pure a Q => exact .pure a Q
  | query hk ih => exact .query fun u => ih u

variable [DecidableEq T] [Fintype F]

/-- The finite set of points a machine can ever query, over all tables. -/
def reachSet : OracleComp T F α → Finset T
  | .pure _ => ∅
  | .query t k => insert t (Finset.univ.biUnion fun u : F => (k u).reachSet)

theorem mem_reachSet_query_self (t : T) (k : F → OracleComp T F α) :
    t ∈ (query t k).reachSet :=
  Finset.mem_insert_self t _

theorem reachSet_query_subset (t : T) (k : F → OracleComp T F α) (u : F) :
    (k u).reachSet ⊆ (query t k).reachSet := fun _ hx =>
  Finset.subset_insert t _
    (Finset.subset_biUnion_of_mem (fun v : F => (k v).reachSet) (Finset.mem_univ u) hx)

/-- A run depends only on reachable table points. -/
theorem run_congr_reachSet : (A : OracleComp T F α) → {O O' : T → F} →
    (∀ t ∈ A.reachSet, O t = O' t) → A.run O = A.run O'
  | .pure _, _, _, _ => rfl
  | .query t k, O, O', h => by
      have ht : O t = O' t := h t (mem_reachSet_query_self t k)
      simp only [run_query, ht]
      exact run_congr_reachSet (k (O' t))
        (fun x hx => h x (reachSet_query_subset t k (O' t) hx))

/-- Restrict a machine to a finite subdomain containing its reachable points. -/
def restrictTo (S : Finset T) : (A : OracleComp T F α) → A.reachSet ⊆ S →
    OracleComp {t // t ∈ S} F α
  | .pure a, _ => .pure a
  | .query t k, h =>
      .query ⟨t, h (mem_reachSet_query_self t k)⟩ fun u =>
        (k u).restrictTo S (fun _ hx => h (reachSet_query_subset t k u hx))

/-- The restriction reproduces the run against any table agreeing on the subdomain. -/
theorem run_restrictTo (S : Finset T) :
    (A : OracleComp T F α) → (h : A.reachSet ⊆ S) → (O : {t // t ∈ S} → F) → (Ō : T → F) →
    (∀ (t : T) (ht : t ∈ S), Ō t = O ⟨t, ht⟩) →
    (A.restrictTo S h).run O = A.run Ō
  | .pure _, _, _, _, _ => rfl
  | .query t k, h, O, Ō, hagree => by
      simp only [restrictTo, run_query]
      rw [show O ⟨t, h (mem_reachSet_query_self t k)⟩ = Ō t from
        (hagree t (h (mem_reachSet_query_self t k))).symm]
      exact run_restrictTo S (k (Ō t)) _ O Ō hagree

/-- Restriction never adds queries. -/
theorem queryBound_restrictTo (S : Finset T) {A : OracleComp T F α} {Q : ℕ}
    (hQ : A.QueryBound Q) : ∀ h : A.reachSet ⊆ S, (A.restrictTo S h).QueryBound Q := by
  induction hQ with
  | pure a Q => intro h; exact .pure a Q
  | query hk ih => intro h; exact .query fun u => ih u _

/-- Split queries between a designated finite domain and the reachable junk points. Queries that
retract through `ρ` use the designated table; all others use the junk table. -/
def splitDomain {T_D : Type*} (ι : T_D → T) (ρ : T → Option T_D) (S : Finset T) :
    (A : OracleComp T F α) → A.reachSet ⊆ S → OracleComp (T_D ⊕ {t // t ∈ S}) F α
  | .pure a, _ => .pure a
  | .query t k, h =>
      .query (match ρ t with
        | some tD => Sum.inl tD
        | none => Sum.inr ⟨t, h (mem_reachSet_query_self t k)⟩)
        fun u => (k u).splitDomain ι ρ S (fun _ hx => h (reachSet_query_subset t k u hx))

/-- The split machine reproduces the run against any full table agreeing with the designated
table along `ι` and with the junk table elsewhere. -/
theorem run_splitDomain {T_D : Type*} (ι : T_D → T) (ρ : T → Option T_D) (S : Finset T)
    (hρ₂ : ∀ t tD, ρ t = some tD → t = ι tD) :
    (A : OracleComp T F α) → (h : A.reachSet ⊆ S) →
    (O' : (T_D ⊕ {t // t ∈ S}) → F) → (Ofull : T → F) →
    (∀ tD, Ofull (ι tD) = O' (Sum.inl tD)) →
    (∀ (t : T) (ht : t ∈ S), ρ t = none → Ofull t = O' (Sum.inr ⟨t, ht⟩)) →
    (A.splitDomain ι ρ S h).run O' = A.run Ofull
  | .pure _, _, _, _, _, _ => rfl
  | .query t k, h, O', Ofull, hD, hJ => by
      simp only [splitDomain, run_query]
      have hans : O' (match ρ t with
          | some tD => Sum.inl tD
          | none => Sum.inr ⟨t, h (mem_reachSet_query_self t k)⟩) = Ofull t := by
        cases hρ : ρ t with
        | some tD =>
            simp
            rw [hρ₂ t tD hρ]
            exact (hD tD).symm
        | none =>
            simp
            exact (hJ t (h (mem_reachSet_query_self t k)) hρ).symm
      rw [hans]
      exact run_splitDomain ι ρ S hρ₂ (k (Ofull t)) _ O' Ofull hD hJ

/-- Splitting never adds queries. -/
theorem queryBound_splitDomain {T_D : Type*} (ι : T_D → T) (ρ : T → Option T_D)
    (S : Finset T) {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q) :
    ∀ h : A.reachSet ⊆ S, (A.splitDomain ι ρ S h).QueryBound Q := by
  induction hQ with
  | pure a Q => intro h; exact .pure a Q
  | query hk ih => intro h; exact .query fun u => ih u _


end OracleComp

/-! ## Overridden tables

Conditioned answers are represented as point-value overrides on an otherwise uniform table. -/

variable {T F : Type*} [DecidableEq T]

/-- Apply a list of point-value overrides to a table, later entries winning. -/
def applyUpdates (σ : List (T × F)) (O : T → F) : T → F :=
  σ.foldl (fun g p => Function.update g p.1 p.2) O

@[simp] theorem applyUpdates_nil (O : T → F) : applyUpdates ([] : List (T × F)) O = O := rfl

theorem applyUpdates_cons (p : T × F) (σ : List (T × F)) (O : T → F) :
    applyUpdates (p :: σ) O = applyUpdates σ (Function.update O p.1 p.2) := rfl

/-- Off the override domain, the table shows through. -/
theorem applyUpdates_apply_not_mem {σ : List (T × F)} {t : T}
    (h : t ∉ σ.map Prod.fst) (O : T → F) : applyUpdates σ O t = O t := by
  induction σ generalizing O with
  | nil => rfl
  | cons p σ ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [applyUpdates_cons, ih h.2, Function.update_apply, if_neg h.1]

/-- On the override domain, the value does not depend on the underlying table. -/
theorem applyUpdates_apply_of_mem {σ : List (T × F)} {t : T}
    (h : t ∈ σ.map Prod.fst) (O O' : T → F) : applyUpdates σ O t = applyUpdates σ O' t := by
  induction σ generalizing O O' with
  | nil => simp at h
  | cons p σ ih =>
      by_cases hmem : t ∈ σ.map Prod.fst
      · exact ih hmem _ _
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · subst h
          rw [applyUpdates_cons, applyUpdates_cons, applyUpdates_apply_not_mem hmem,
            applyUpdates_apply_not_mem hmem, Function.update_self, Function.update_self]
        · exact absurd h hmem

/-- Off the override domain, overriding the underlying table commutes with the record. -/
theorem applyUpdates_update_not_mem {σ : List (T × F)} {t : T}
    (h : t ∉ σ.map Prod.fst) (O : T → F) (v : F) :
    applyUpdates σ (Function.update O t v) = Function.update (applyUpdates σ O) t v := by
  funext j
  by_cases hj : j = t
  · subst hj
    rw [applyUpdates_apply_not_mem h, Function.update_self, Function.update_self]
  · by_cases hdom : j ∈ σ.map Prod.fst
    · rw [Function.update_apply, if_neg hj, applyUpdates_apply_of_mem hdom]
    · simp [applyUpdates_apply_not_mem hdom, hj]

/-- Overriding the table at an already-overridden point changes nothing. -/
theorem applyUpdates_update_of_mem {σ : List (T × F)} {t : T}
    (h : t ∈ σ.map Prod.fst) (O : T → F) (v : F) :
    applyUpdates σ (Function.update O t v) = applyUpdates σ O := by
  induction σ generalizing O with
  | nil => simp at h
  | cons p σ ih =>
      rw [applyUpdates_cons, applyUpdates_cons]
      by_cases hp : t = p.1
      · subst hp
        rw [Function.update_idem]
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h hp
        · rw [Function.update_comm hp]
          exact ih h _

/-- A `Q`-query cache-avoiding machine enters table-dependent blind escape sets of measure `ε` with
probability at most `Q · ε`. -/
theorem escapesDuringC_measure_le {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] {α : Type*} (esc : T → (T → F) → Set F)
    (hblind : ∀ (t : T) (O : T → F) (v : F), esc t (Function.update O t v) = esc t O)
    {ε : ℝ≥0∞} (hesc : ∀ t O, (PMF.uniformOfFintype F).toOuterMeasure (esc t O) ≤ ε)
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    {σ : List (T × F)} (hσ : OracleComp.AvoidsCache σ A) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | A.escapesDuringC esc (applyUpdates σ O)} ≤ Q * ε := by
  induction hQ generalizing σ with
  | pure a Q' =>
      have hempty : {O : T → F | (OracleComp.pure a : OracleComp T F α).escapesDuringC esc
          (applyUpdates σ O)} = ∅ := by
        ext O; simp [OracleComp.escapesDuringC]
      rw [hempty]
      simp
  | @query t k Q h ih =>
      cases hσ with
      | query ht hk =>
      have happ : ∀ O : T → F, applyUpdates σ O t = O t :=
        fun O => applyUpdates_apply_not_mem ht O
      have hsub : {O : T → F | (OracleComp.query t k).escapesDuringC esc (applyUpdates σ O)}
          ⊆ {O : T → F | O t ∈ esc t (applyUpdates σ O)} ∪ ⋃ u : F, {O : T → F | O t = u ∧
              O ∈ {O' : T → F | (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')}} := by
        intro O hO
        simp only [OracleComp.escapesDuringC, Set.mem_setOf_eq, happ O] at hO
        rcases hO with h1 | h2
        · exact Or.inl h1
        · refine Or.inr (Set.mem_iUnion.mpr ⟨O t, rfl, ?_⟩)
          have hcons : applyUpdates ((t, O t) :: σ) O = applyUpdates σ O := by
            rw [applyUpdates_cons, Function.update_eq_self]
          simp only [Set.mem_setOf_eq, hcons]
          exact h2
      refine le_trans (MeasureTheory.measure_mono hsub) ?_
      refine le_trans (MeasureTheory.measure_union_le _ _) ?_
      have hfirst : (PMF.uniformOfFintype (T → F)).toOuterMeasure
          {O : T → F | O t ∈ esc t (applyUpdates σ O)} ≤ ε := by
        refine uniformOfFintype_point_mem_blind_le t (fun O => esc t (applyUpdates σ O))
          (fun O v => ?_) (fun O => hesc t _)
        beta_reduce
        rw [applyUpdates_update_not_mem ht, hblind]
      have hsecond : (PMF.uniformOfFintype (T → F)).toOuterMeasure
          (⋃ u : F, {O : T → F | O t = u ∧
            O ∈ {O' : T → F | (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')}})
          ≤ Q * ε := by
        refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
        rw [tsum_fintype]
        have hper : ∀ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure
            {O : T → F | O t = u ∧
              O ∈ {O' : T → F | (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')}}
            ≤ (Q * ε) / Fintype.card F := by
          intro u
          have hblindE : ∀ (O : T → F) (v : F),
              Function.update O t v ∈ {O' : T → F |
                (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')}
              ↔ O ∈ {O' : T → F |
                (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')} := by
            intro O v
            have hcons : applyUpdates ((t, u) :: σ) (Function.update O t v)
                = applyUpdates ((t, u) :: σ) O := by
              rw [applyUpdates_cons, applyUpdates_cons, Function.update_idem]
            simp only [Set.mem_setOf_eq, hcons]
          rw [uniformOfFintype_cond_point t u _ hblindE]
          exact ENNReal.div_le_div_right (ih u (hk u)) _
        refine le_trans (Finset.sum_le_sum fun u _ => hper u) ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm,
          ENNReal.div_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _)]
      calc (PMF.uniformOfFintype (T → F)).toOuterMeasure
            {O : T → F | O t ∈ esc t (applyUpdates σ O)}
            + (PMF.uniformOfFintype (T → F)).toOuterMeasure (⋃ u : F, _)
          ≤ ε + Q * ε := add_le_add hfirst hsecond
        _ = (Q + 1) * ε := by ring
        _ = ((Q + 1 : ℕ) : ℝ≥0∞) * ε := by push_cast; ring

/-- The conditional escape bound for an arbitrary machine: deduplicate
(`OracleComp.escapesDuringC_dedup`), then apply the fresh-query bound. -/
theorem escapesDuringC_measure_le' {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] {α : Type*} (esc : T → (T → F) → Set F)
    (hblind : ∀ (t : T) (O : T → F) (v : F), esc t (Function.update O t v) = esc t O)
    {ε : ℝ≥0∞} (hesc : ∀ t O, (PMF.uniformOfFintype F).toOuterMeasure (esc t O) ≤ ε)
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | A.escapesDuringC esc O} ≤ Q * ε := by
  have hsub : {O : T → F | A.escapesDuringC esc O}
      ⊆ {O : T → F | (OracleComp.dedup [] A).escapesDuringC esc
          (applyUpdates ([] : List (T × F)) O)} := by
    intro O hO
    simp only [Set.mem_setOf_eq, applyUpdates_nil]
    exact OracleComp.escapesDuringC_dedup esc (by simp) (by simp) hO
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  exact escapesDuringC_measure_le esc hblind hesc (OracleComp.dedup_queryBound hQ [])
    (OracleComp.dedup_avoidsCache [] A)

/-! ## Weighted query charges

Bound natural-number query charges by the query budget. -/

/-- Accumulate a per-query charge along the run: each query `t` contributes `v t O (O t)`. -/
def queryCharge {T F α : Type*} (v : T → (T → F) → F → ℕ) :
    OracleComp T F α → (T → F) → ℕ
  | .pure _, _ => 0
  | .query t k, O => v t O (O t) + queryCharge v (k (O t)) O

/-- Fibering a table sum over one coordinate's value. -/
theorem sum_table_fiberwise {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [DecidableEq F] (t : T) (g : (T → F) → ℕ) :
    ∑ O : T → F, g O
      = ∑ u : F, ∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u), g O := by
  calc ∑ O : T → F, g O = ∑ O : T → F, ∑ u : F, if O t = u then g O else 0 := by
        refine Finset.sum_congr rfl fun O _ => ?_
        simp
    _ = ∑ u : F, ∑ O : T → F, if O t = u then g O else 0 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun u _ => (Finset.sum_filter _ _).symm

/-- A coordinate-blind summand makes every fiber of that coordinate the same size. -/
theorem sum_table_fiber_blind {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [DecidableEq F] (t : T) (g : (T → F) → ℕ)
    (hblind : ∀ (O : T → F) (v : F), g (Function.update O t v) = g O) (u u' : F) :
    ∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u), g O
      = ∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u'), g O := by
  refine Finset.sum_nbij' (fun O => Function.update O t u') (fun O => Function.update O t u)
    (fun O hO => ?_) (fun O hO => ?_) (fun O hO => ?_) (fun O hO => ?_) (fun O hO => ?_)
  · simp
  · simp
  · dsimp only
    rw [Function.update_idem, ← (Finset.mem_filter.mp hO).2, Function.update_eq_self]
  · dsimp only
    rw [Function.update_idem, ← (Finset.mem_filter.mp hO).2, Function.update_eq_self]
  · exact (hblind O u').symm

/-- Summing a coordinate-blind summand over one fiber recovers the full sum after scaling by the
field size. -/
theorem sum_table_fiber_mul_card {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [DecidableEq F] (t : T) (g : (T → F) → ℕ)
    (hblind : ∀ (O : T → F) (v : F), g (Function.update O t v) = g O) (u : F) :
    (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u), g O) * Fintype.card F
      = ∑ O : T → F, g O := by
  rw [sum_table_fiberwise t g,
    Finset.sum_congr rfl fun u' _ => sum_table_fiber_blind t g hblind u' u,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- A `Q`-query machine's total blind charge is at most `Q` times its average per-point budget,
stated after clearing the factor `|F|`.  The budget must hold uniformly over every override
context `σ'`, not just the ambient one; `queryCharge_sum_mul_le_table_budget` trades this for a
pointwise table-indexed budget. -/
theorem queryCharge_sum_mul_le {T F α : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [DecidableEq F] [Nonempty F] (v : T → (T → F) → F → ℕ)
    (hblind : ∀ (t : T) (O : T → F) (x y : F), v t (Function.update O t y) x = v t O x)
    {M : ℕ} (hbudget : ∀ (t : T) (σ' : List (T × F)),
      ∑ O : T → F, ∑ x : F, v t (applyUpdates σ' O) x ≤ M * Fintype.card (T → F))
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    {σ : List (T × F)} (hσ : OracleComp.AvoidsCache σ A) :
    (∑ O : T → F, queryCharge v A (applyUpdates σ O)) * Fintype.card F
      ≤ Q * M * Fintype.card (T → F) := by
  induction hQ generalizing σ with
  | pure a Q' => simp [queryCharge]
  | @query t k Q h ih =>
      cases hσ with
      | query ht hk =>
      have happ : ∀ O : T → F, applyUpdates σ O t = O t :=
        fun O => applyUpdates_apply_not_mem ht O
      have hsplit : ∀ O : T → F,
          queryCharge v (OracleComp.query t k) (applyUpdates σ O)
            = v t (applyUpdates σ O) (O t)
              + queryCharge v (k (O t)) (applyUpdates ((t, O t) :: σ) O) := by
        intro O
        have hcons : applyUpdates ((t, O t) :: σ) O = applyUpdates σ O := by
          rw [applyUpdates_cons, Function.update_eq_self]
        rw [queryCharge, happ O, hcons]
      rw [Finset.sum_congr rfl fun O _ => hsplit O, Finset.sum_add_distrib, Nat.add_mul,
        show (Q + 1) * M * Fintype.card (T → F)
          = M * Fintype.card (T → F) + Q * M * Fintype.card (T → F) by ring]
      refine Nat.add_le_add ?_ ?_
      · -- one query pays its answer-averaged budget
        have hb : ∀ (x : F) (O : T → F) (y : F),
            v t (applyUpdates σ (Function.update O t y)) x = v t (applyUpdates σ O) x := by
          intro x O y
          rw [applyUpdates_update_not_mem ht, hblind]
        calc (∑ O : T → F, v t (applyUpdates σ O) (O t)) * Fintype.card F
            = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                v t (applyUpdates σ O) (O t)) * Fintype.card F := by
              rw [sum_table_fiberwise t, Finset.sum_mul]
          _ = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                v t (applyUpdates σ O) u) * Fintype.card F := by
              refine Finset.sum_congr rfl fun u _ => ?_
              congr 1
              exact Finset.sum_congr rfl fun O hO => by rw [(Finset.mem_filter.mp hO).2]
          _ = ∑ u : F, ∑ O : T → F, v t (applyUpdates σ O) u :=
              Finset.sum_congr rfl fun u _ => sum_table_fiber_mul_card t _ (hb u) u
          _ = ∑ O : T → F, ∑ u : F, v t (applyUpdates σ O) u := Finset.sum_comm
          _ ≤ M * Fintype.card (T → F) := hbudget t σ
      · -- the continuation recurses conditionally on the answer
        have hbk : ∀ (u : F) (O : T → F) (y : F),
            queryCharge v (k u) (applyUpdates ((t, u) :: σ) (Function.update O t y))
              = queryCharge v (k u) (applyUpdates ((t, u) :: σ) O) := by
          intro u O y
          rw [applyUpdates_cons, applyUpdates_cons, Function.update_idem]
        have hfiber : (∑ O : T → F,
            queryCharge v (k (O t)) (applyUpdates ((t, O t) :: σ) O)) * Fintype.card F
            = ∑ u : F, ∑ O : T → F, queryCharge v (k u) (applyUpdates ((t, u) :: σ) O) := by
          rw [sum_table_fiberwise t, Finset.sum_mul]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [show (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                queryCharge v (k (O t)) (applyUpdates ((t, O t) :: σ) O))
              = ∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                queryCharge v (k u) (applyUpdates ((t, u) :: σ) O) from
            Finset.sum_congr rfl fun O hO => by rw [(Finset.mem_filter.mp hO).2]]
          exact sum_table_fiber_mul_card t _ (hbk u) u
        rw [hfiber]
        refine Nat.le_of_mul_le_mul_right ?_ (Fintype.card_pos (α := F))
        calc (∑ u : F, ∑ O : T → F, queryCharge v (k u) (applyUpdates ((t, u) :: σ) O))
              * Fintype.card F
            = ∑ u : F, (∑ O : T → F,
                queryCharge v (k u) (applyUpdates ((t, u) :: σ) O)) * Fintype.card F :=
              Finset.sum_mul _ _ _
          _ ≤ ∑ _u : F, Q * M * Fintype.card (T → F) :=
              Finset.sum_le_sum fun u _ => ih u (hk u)
          _ = Q * M * Fintype.card (T → F) * Fintype.card F := by
              rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- Table-indexed query-charge bound, charging the budget sum at the original override context. -/
theorem queryCharge_sum_mul_le_table_budget {T F α : Type*} [Fintype T] [DecidableEq T]
    [Fintype F] [DecidableEq F] [Nonempty F] (v : T → (T → F) → F → ℕ)
    (hblind : ∀ (t : T) (O : T → F) (x y : F), v t (Function.update O t y) x = v t O x)
    (B : (T → F) → ℕ) (hB : ∀ (t : T) (O : T → F), ∑ x : F, v t O x ≤ B O)
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    {σ : List (T × F)} (hσ : OracleComp.AvoidsCache σ A) :
    (∑ O : T → F, queryCharge v A (applyUpdates σ O)) * Fintype.card F
      ≤ Q * ∑ O : T → F, B (applyUpdates σ O) := by
  induction hQ generalizing σ with
  | pure a Q' => simp [queryCharge]
  | @query t k Q h ih =>
      cases hσ with
      | query ht hk =>
      have happ : ∀ O : T → F, applyUpdates σ O t = O t :=
        fun O => applyUpdates_apply_not_mem ht O
      have hsplit : ∀ O : T → F,
          queryCharge v (OracleComp.query t k) (applyUpdates σ O)
            = v t (applyUpdates σ O) (O t)
              + queryCharge v (k (O t)) (applyUpdates ((t, O t) :: σ) O) := by
        intro O
        have hcons : applyUpdates ((t, O t) :: σ) O = applyUpdates σ O := by
          rw [applyUpdates_cons, Function.update_eq_self]
        rw [queryCharge, happ O, hcons]
      rw [Finset.sum_congr rfl fun O _ => hsplit O, Finset.sum_add_distrib, Nat.add_mul,
        show (Q + 1) * ∑ O : T → F, B (applyUpdates σ O)
          = (∑ O : T → F, B (applyUpdates σ O)) + Q * ∑ O : T → F, B (applyUpdates σ O)
          by ring]
      refine Nat.add_le_add ?_ ?_
      · -- one query pays the budget at the current context
        have hb : ∀ (x : F) (O : T → F) (y : F),
            v t (applyUpdates σ (Function.update O t y)) x = v t (applyUpdates σ O) x := by
          intro x O y
          rw [applyUpdates_update_not_mem ht, hblind]
        calc (∑ O : T → F, v t (applyUpdates σ O) (O t)) * Fintype.card F
            = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                v t (applyUpdates σ O) (O t)) * Fintype.card F := by
              rw [sum_table_fiberwise t, Finset.sum_mul]
          _ = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                v t (applyUpdates σ O) u) * Fintype.card F := by
              refine Finset.sum_congr rfl fun u _ => ?_
              congr 1
              exact Finset.sum_congr rfl fun O hO => by rw [(Finset.mem_filter.mp hO).2]
          _ = ∑ u : F, ∑ O : T → F, v t (applyUpdates σ O) u :=
              Finset.sum_congr rfl fun u _ => sum_table_fiber_mul_card t _ (hb u) u
          _ = ∑ O : T → F, ∑ u : F, v t (applyUpdates σ O) u := Finset.sum_comm
          _ ≤ ∑ O : T → F, B (applyUpdates σ O) :=
              Finset.sum_le_sum fun O _ => hB t _
      · -- the continuation recurses conditionally; the budget fibers recombine exactly
        have hbk : ∀ (u : F) (O : T → F) (y : F),
            queryCharge v (k u) (applyUpdates ((t, u) :: σ) (Function.update O t y))
              = queryCharge v (k u) (applyUpdates ((t, u) :: σ) O) := by
          intro u O y
          rw [applyUpdates_cons, applyUpdates_cons, Function.update_idem]
        have hBk : ∀ (u : F) (O : T → F) (y : F),
            B (applyUpdates ((t, u) :: σ) (Function.update O t y))
              = B (applyUpdates ((t, u) :: σ) O) := by
          intro u O y
          rw [applyUpdates_cons, applyUpdates_cons, Function.update_idem]
        have hfiber : (∑ O : T → F,
            queryCharge v (k (O t)) (applyUpdates ((t, O t) :: σ) O)) * Fintype.card F
            = ∑ u : F, ∑ O : T → F, queryCharge v (k u) (applyUpdates ((t, u) :: σ) O) := by
          rw [sum_table_fiberwise t, Finset.sum_mul]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [show (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                queryCharge v (k (O t)) (applyUpdates ((t, O t) :: σ) O))
              = ∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                queryCharge v (k u) (applyUpdates ((t, u) :: σ) O) from
            Finset.sum_congr rfl fun O hO => by rw [(Finset.mem_filter.mp hO).2]]
          exact sum_table_fiber_mul_card t _ (hbk u) u
        have hBfiber : ∑ u : F, ∑ O : T → F, B (applyUpdates ((t, u) :: σ) O)
            = (∑ O : T → F, B (applyUpdates σ O)) * Fintype.card F := by
          calc ∑ u : F, ∑ O : T → F, B (applyUpdates ((t, u) :: σ) O)
              = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                  B (applyUpdates ((t, u) :: σ) O)) * Fintype.card F :=
                Finset.sum_congr rfl fun u _ => (sum_table_fiber_mul_card t _ (hBk u) u).symm
            _ = ∑ u : F, (∑ O ∈ Finset.univ.filter (fun O : T → F => O t = u),
                  B (applyUpdates ((t, O t) :: σ) O)) * Fintype.card F := by
                refine Finset.sum_congr rfl fun u _ => ?_
                congr 1
                exact Finset.sum_congr rfl fun O hO => by
                  rw [(Finset.mem_filter.mp hO).2]
            _ = (∑ O : T → F, B (applyUpdates ((t, O t) :: σ) O)) * Fintype.card F := by
                rw [sum_table_fiberwise t, Finset.sum_mul]
            _ = (∑ O : T → F, B (applyUpdates σ O)) * Fintype.card F := by
                congr 1
                refine Finset.sum_congr rfl fun O _ => ?_
                congr 1
                rw [applyUpdates_cons, Function.update_eq_self]
        rw [hfiber]
        refine Nat.le_of_mul_le_mul_right ?_ (Fintype.card_pos (α := F))
        calc (∑ u : F, ∑ O : T → F, queryCharge v (k u) (applyUpdates ((t, u) :: σ) O))
              * Fintype.card F
            = ∑ u : F, (∑ O : T → F,
                queryCharge v (k u) (applyUpdates ((t, u) :: σ) O)) * Fintype.card F :=
              Finset.sum_mul _ _ _
          _ ≤ ∑ u : F, Q * ∑ O : T → F, B (applyUpdates ((t, u) :: σ) O) :=
              Finset.sum_le_sum fun u _ => ih u (hk u)
          _ = Q * ∑ u : F, ∑ O : T → F, B (applyUpdates ((t, u) :: σ) O) := by
              rw [Finset.mul_sum]
          _ = Q * ((∑ O : T → F, B (applyUpdates σ O)) * Fintype.card F) := by
              rw [hBfiber]
          _ = Q * (∑ O : T → F, B (applyUpdates σ O)) * Fintype.card F := by ring

/-- A single query's charge is dominated by the accumulated charge of any run that makes it. -/
theorem le_queryCharge_of_mem_queries {T F α : Type*} (v : T → (T → F) → F → ℕ)
    {B : OracleComp T F α} {O : T → F} {t : T} (h : t ∈ B.queries O) :
    v t O (O t) ≤ queryCharge v B O := by
  induction B with
  | pure a => simp [OracleComp.queries] at h
  | query t' k ih =>
      simp only [OracleComp.queries, List.mem_cons] at h
      rw [queryCharge]
      rcases h with rfl | h
      · exact Nat.le_add_right _ _
      · exact le_trans (ih (O t') h) (Nat.le_add_left _ _)

/-- Deduplication preserves occurrence of a queried point not already cached. -/
theorem mem_queries_dedup {T F α : Type*} [DecidableEq T] {B : OracleComp T F α}
    {O : T → F} {t : T} {c : List (T × F)} (hc : ∀ p ∈ c, O p.1 = p.2)
    (ht : t ∉ c.map Prod.fst) (h : t ∈ B.queries O) :
    t ∈ (OracleComp.dedup c B).queries O := by
  induction B generalizing c with
  | pure a => simp [OracleComp.queries] at h
  | query t' k ih =>
      simp only [OracleComp.queries, List.mem_cons] at h
      rw [OracleComp.dedup]
      cases hfind : c.find? (fun p => p.1 = t') with
      | some p =>
          have hpc := List.mem_of_find?_eq_some hfind
          have hpt : p.1 = t' := by simpa using List.find?_some hfind
          have hval : O t' = p.2 := by rw [← hpt]; exact hc p hpc
          rcases h with rfl | h
          · exact absurd (hpt ▸ List.mem_map_of_mem hpc) ht
          · show t ∈ (OracleComp.dedup c (k p.2)).queries O
            rw [← hval]
            exact ih (O t') hc ht h
      | none =>
          simp only [OracleComp.queries, List.mem_cons]
          rcases h with rfl | h
          · exact Or.inl rfl
          · by_cases htt' : t = t'
            · exact Or.inl htt'
            · refine Or.inr (ih (O t') ?_ ?_ h)
              · intro p hp
                rcases List.mem_cons.mp hp with rfl | hp
                · rfl
                · exact hc p hp
              · simp only [List.map_cons, List.mem_cons, not_or]
                exact ⟨htt', ht⟩

/-- With pairwise-distinct override keys, the reprogrammed table shows each recorded override. -/
theorem applyUpdates_apply_mem_nodup {T F : Type*} [DecidableEq T] {σ : List (T × F)}
    (hnodup : (σ.map Prod.fst).Nodup) {p : T × F} (hp : p ∈ σ) (O : T → F) :
    applyUpdates σ O p.1 = p.2 := by
  induction σ generalizing O with
  | nil => simp at hp
  | cons q σ ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hp with rfl | hp
      · rw [applyUpdates_cons, applyUpdates_apply_not_mem hnodup.1, Function.update_self]
      · rw [applyUpdates_cons]
        exact ih hnodup.2 hp _

/-- Bound the charge at an adaptively selected queried point under a reprogrammed table by the
query budget times the average per-point budget. -/
theorem steeredCharge_context_sum_mul_le {T F α : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [DecidableEq F] [Nonempty F] (v : T → (T → F) → F → ℕ)
    (hblind : ∀ (t : T) (O : T → F) (x y : F), v t (Function.update O t y) x = v t O x)
    {M : ℕ} (hbudget : ∀ (t : T) (σ' : List (T × F)),
      ∑ O : T → F, ∑ x : F, v t (applyUpdates σ' O) x ≤ M * Fintype.card (T → F))
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    {σ : List (T × F)} (hnodup : (σ.map Prod.fst).Nodup)
    (fp : (T → F) → T)
    (hfp : ∀ O : T → F, fp O ∈ A.queries (applyUpdates σ O))
    (hfresh : ∀ O : T → F, fp O ∉ σ.map Prod.fst) :
    (∑ O : T → F, v (fp O) (applyUpdates σ O) (applyUpdates σ O (fp O))) * Fintype.card F
      ≤ Q * M * Fintype.card (T → F) := by
  have hle : ∀ O : T → F,
      v (fp O) (applyUpdates σ O) (applyUpdates σ O (fp O))
        ≤ queryCharge v (OracleComp.dedup σ A) (applyUpdates σ O) := fun O =>
    le_queryCharge_of_mem_queries v
      (mem_queries_dedup (fun p hp => applyUpdates_apply_mem_nodup hnodup hp O)
        (hfresh O) (hfp O))
  calc (∑ O : T → F, v (fp O) (applyUpdates σ O) (applyUpdates σ O (fp O))) * Fintype.card F
      ≤ (∑ O : T → F, queryCharge v (OracleComp.dedup σ A) (applyUpdates σ O))
        * Fintype.card F :=
        Nat.mul_le_mul_right _ (Finset.sum_le_sum fun O _ => hle O)
    _ ≤ Q * M * Fintype.card (T → F) :=
        queryCharge_sum_mul_le v hblind hbudget (OracleComp.dedup_queryBound hQ σ)
          (OracleComp.dedup_avoidsCache σ A)

/-- Table-indexed form of `steeredCharge_context_sum_mul_le`. -/
theorem steeredCharge_context_sum_mul_le_table_budget {T F α : Type*} [Fintype T]
    [DecidableEq T] [Fintype F] [DecidableEq F] [Nonempty F] (v : T → (T → F) → F → ℕ)
    (hblind : ∀ (t : T) (O : T → F) (x y : F), v t (Function.update O t y) x = v t O x)
    (B : (T → F) → ℕ) (hB : ∀ (t : T) (O : T → F), ∑ x : F, v t O x ≤ B O)
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    {σ : List (T × F)} (hnodup : (σ.map Prod.fst).Nodup)
    (fp : (T → F) → T)
    (hfp : ∀ O : T → F, fp O ∈ A.queries (applyUpdates σ O))
    (hfresh : ∀ O : T → F, fp O ∉ σ.map Prod.fst) :
    (∑ O : T → F, v (fp O) (applyUpdates σ O) (applyUpdates σ O (fp O))) * Fintype.card F
      ≤ Q * ∑ O : T → F, B (applyUpdates σ O) := by
  have hle : ∀ O : T → F,
      v (fp O) (applyUpdates σ O) (applyUpdates σ O (fp O))
        ≤ queryCharge v (OracleComp.dedup σ A) (applyUpdates σ O) := fun O =>
    le_queryCharge_of_mem_queries v
      (mem_queries_dedup (fun p hp => applyUpdates_apply_mem_nodup hnodup hp O)
        (hfresh O) (hfp O))
  calc (∑ O : T → F, v (fp O) (applyUpdates σ O) (applyUpdates σ O (fp O))) * Fintype.card F
      ≤ (∑ O : T → F, queryCharge v (OracleComp.dedup σ A) (applyUpdates σ O))
        * Fintype.card F :=
        Nat.mul_le_mul_right _ (Finset.sum_le_sum fun O _ => hle O)
    _ ≤ Q * ∑ O : T → F, B (applyUpdates σ O) :=
        queryCharge_sum_mul_le_table_budget v hblind B hB (OracleComp.dedup_queryBound hQ σ)
          (OracleComp.dedup_avoidsCache σ A)

/-- Context-free form of `steeredCharge_context_sum_mul_le`. -/
theorem steeredCharge_sum_mul_le {T F α : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [DecidableEq F] [Nonempty F] (v : T → (T → F) → F → ℕ)
    (hblind : ∀ (t : T) (O : T → F) (x y : F), v t (Function.update O t y) x = v t O x)
    {M : ℕ} (hbudget : ∀ (t : T) (σ' : List (T × F)),
      ∑ O : T → F, ∑ x : F, v t (applyUpdates σ' O) x ≤ M * Fintype.card (T → F))
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    (fp : (T → F) → T) (hfp : ∀ O : T → F, fp O ∈ A.queries O) :
    (∑ O : T → F, v (fp O) O (O (fp O))) * Fintype.card F
      ≤ Q * M * Fintype.card (T → F) := by
  have h := steeredCharge_context_sum_mul_le v hblind hbudget hQ
    (σ := []) (by simp) fp (fun O => by simpa using hfp O) (fun O => by simp)
  simpa using h


end Ragu.Foundation.Oracle
