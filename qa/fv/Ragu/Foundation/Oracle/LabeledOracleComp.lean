import Ragu.Foundation.Oracle.OracleComp

/-!
Ported from `Zcash/Common/Oracle/LabeledOracleComp.lean` at `zcash/ironwood` commit
`3c056cbebf2880b54f801c348cb67ce7dc9f2a05`. Ragu adapts only the namespace and internal import.
-/

/-!
# Labeled adaptive oracle computations

`LabeledOracleComp` is an adaptive oracle computation whose query nodes carry
data that is not passed to the oracle: the oracle still receives only the
query point, so different labels at the same point share one oracle answer.
Labels record per-query context an argument needs later — the AGM layer uses
them for pre-answer algebraic representations — and `erase` recovers the exact
unlabeled query tree the oracle sees.

The measure bounds at the end price an adaptively selected query's answer
landing in a label-dependent bad set, or in a fallback set when the point was
never queried, with no phase-ordering or prefix-determinism premise.
-/

namespace Ragu.Foundation.Oracle

open Ragu.Foundation.Probability

/-- An adaptive oracle computation whose query nodes carry data not passed to the oracle.  The
oracle still receives only `t : T`, so different labels at the same `t` share one oracle answer. -/
inductive LabeledOracleComp (T F : Type*) (Label : T → Type*) (α : Type*) where
  | pure (a : α)
  | query (t : T) (label : Label t) (k : F → LabeledOracleComp T F Label α)

namespace LabeledOracleComp

variable {T F α β : Type*} {Label : T → Type*}

/-- Forget query annotations, preserving the exact adaptive query tree seen by the random oracle. -/
def erase : LabeledOracleComp T F Label α → OracleComp T F α
  | .pure a => .pure a
  | .query t _ k => .query t (fun u => (k u).erase)

/-- Run a labeled computation against an ordinary oracle table. -/
def run (A : LabeledOracleComp T F Label α) (O : T → F) : α := A.erase.run O

/-- The ordinary query log of a labeled computation. -/
def queries (A : LabeledOracleComp T F Label α) (O : T → F) : List T := A.erase.queries O

/-- The annotation attached to each query on one concrete run.  Answers are deliberately omitted:
they remain available from the oracle table, while this log records exactly the data fixed before
each answer was read. -/
structure QueryAnnotation (T : Type*) (Label : T → Type*) where
  point : T
  label : Label point

/-- Query annotations along the adaptive path selected by `O`. -/
def annotations (A : LabeledOracleComp T F Label α) (O : T → F) :
    List (QueryAnnotation T Label) :=
  match A with
  | .pure _ => []
  | .query t label k => ⟨t, label⟩ :: (k (O t)).annotations O

/-- Evaluate an adaptive computation and retain its query annotations in the same traversal.
Unlike calling `run` and then repeatedly calling `findLabel`, this consults the oracle exactly
once at each visited query node. -/
def runWithAnnotations (A : LabeledOracleComp T F Label α) (O : T → F) :
    α × List (QueryAnnotation T Label) :=
  match A with
  | .pure a => (a, [])
  | .query t label k =>
      let rest := (k (O t)).runWithAnnotations O
      (rest.1, ⟨t, label⟩ :: rest.2)

@[simp] theorem runWithAnnotations_snd
    (A : LabeledOracleComp T F Label α) (O : T → F) :
    (A.runWithAnnotations O).2 = A.annotations O := by
  induction A with
  | pure => rfl
  | query t label k ih =>
      simp only [runWithAnnotations, annotations]
      rw [ih (O t)]

/-- Look up the first annotation at a point in an already retained log.  This traverses ordinary
data and does not re-run the adversary or consult the oracle. -/
def findLabelInAnnotations [DecidableEq T] :
    List (QueryAnnotation T Label) → (t : T) → Option (Label t)
  | [], _ => none
  | entry :: rest, t =>
      if h : entry.point = t then some (h ▸ entry.label)
      else findLabelInAnnotations rest t

/-- Retrieve the first annotation at `t`, if the computation queried `t`. -/
def findLabel [DecidableEq T] (A : LabeledOracleComp T F Label α) (O : T → F)
    (t : T) : Option (Label t) :=
  match A with
  | .pure _ => none
  | .query q label k =>
      if h : q = t then some (h ▸ label) else (k (O q)).findLabel O t

/-- A labeled computation is query-bounded exactly when its erased computation is. -/
abbrev QueryBound (A : LabeledOracleComp T F Label α) (Q : ℕ) : Prop := A.erase.QueryBound Q

/-- Sequence two labeled computations. -/
def bind : LabeledOracleComp T F Label α →
    (α → LabeledOracleComp T F Label β) → LabeledOracleComp T F Label β
  | .pure a, f => f a
  | .query t label k, f => .query t label (fun u => (k u).bind f)

@[simp] theorem erase_pure (a : α) :
    (pure a : LabeledOracleComp T F Label α).erase = .pure a := rfl

@[simp] theorem erase_query (t : T) (label : Label t)
    (k : F → LabeledOracleComp T F Label α) :
    (query t label k).erase = .query t (fun u => (k u).erase) := rfl

@[simp] theorem erase_bind (A : LabeledOracleComp T F Label α)
    (f : α → LabeledOracleComp T F Label β) :
    (A.bind f).erase = A.erase.bind (fun a => (f a).erase) := by
  induction A with
  | pure a => rfl
  | query t label k ih =>
      simp only [bind, erase, OracleComp.bind]
      congr
      funext u
      exact ih u

@[simp] theorem run_pure (a : α) (O : T → F) :
    (pure a : LabeledOracleComp T F Label α).run O = a := rfl

@[simp] theorem run_query (t : T) (label : Label t)
    (k : F → LabeledOracleComp T F Label α) (O : T → F) :
    (query t label k).run O = (k (O t)).run O := rfl

@[simp] theorem run_bind (A : LabeledOracleComp T F Label α)
    (f : α → LabeledOracleComp T F Label β) (O : T → F) :
    (A.bind f).run O = (f (A.run O)).run O := by
  simp only [run, erase_bind, OracleComp.run_bind]

@[simp] theorem annotations_pure (a : α) (O : T → F) :
    (pure a : LabeledOracleComp T F Label α).annotations O = [] := rfl

@[simp] theorem annotations_query (t : T) (label : Label t)
    (k : F → LabeledOracleComp T F Label α) (O : T → F) :
    (query t label k).annotations O =
      ⟨t, label⟩ :: (k (O t)).annotations O := rfl

/-- Erasing annotations gives the ordinary query log. -/
theorem queries_eq_map_annotations (A : LabeledOracleComp T F Label α) (O : T → F) :
    A.queries O = (A.annotations O).map QueryAnnotation.point := by
  induction A with
  | pure a => rfl
  | query t label k ih =>
      simp only [queries, erase, OracleComp.queries, annotations, List.map_cons]
      exact congrArg (List.cons t) (ih (O t))

@[simp] theorem runWithAnnotations_fst
    (A : LabeledOracleComp T F Label α) (O : T → F) :
    (A.runWithAnnotations O).1 = A.run O := by
  induction A with
  | pure => rfl
  | query t label k ih =>
      simpa only [runWithAnnotations, run_query] using ih (O t)

/-- Cached annotation lookup agrees with a fresh `findLabel` traversal. -/
theorem findLabelInAnnotations_annotations [DecidableEq T]
    (A : LabeledOracleComp T F Label α) (O : T → F) (t : T) :
    findLabelInAnnotations (A.annotations O) t = A.findLabel O t := by
  induction A with
  | pure => rfl
  | query q label k ih =>
      simp only [annotations, findLabelInAnnotations, findLabel]
      split
      · rfl
      · exact ih (O q)

/-- A labeled computation's result, query log, and annotations depend only on the table's
values at its own queries.  This is the locality fact behind every oracle-access certificate:
agreement on the query log reproduces the entire run. -/
theorem run_queries_annotations_eq_of_agree {A : LabeledOracleComp T F Label α} :
    ∀ {O O' : T → F}, (∀ t ∈ A.queries O, O' t = O t) →
      A.run O' = A.run O ∧ A.queries O' = A.queries O ∧
        A.annotations O' = A.annotations O := by
  induction A with
  | pure a => exact fun _ => ⟨rfl, rfl, rfl⟩
  | query t label k ih =>
      intro O O' h
      have hmemHead : t ∈ (LabeledOracleComp.query t label k).queries O := by
        simp [queries, erase, OracleComp.queries]
      have ht : O' t = O t := h t hmemHead
      have htail := ih (O t) (O := O) (O' := O') (fun s hs => h s (by
        simp only [queries, erase, OracleComp.queries, List.mem_cons]
        exact Or.inr (by simpa [queries, erase] using hs)))
      refine ⟨?_, ?_, ?_⟩
      · show ((k (O' t)).erase).run O' = ((k (O t)).erase).run O
        rw [ht]
        exact htail.1
      · show t :: ((k (O' t)).erase).queries O' = t :: ((k (O t)).erase).queries O
        rw [ht]
        exact congrArg _ htail.2.1
      · show ⟨t, label⟩ :: (k (O' t)).annotations O' = ⟨t, label⟩ :: (k (O t)).annotations O
        rw [ht]
        exact congrArg _ htail.2.2

/-- Locality of the single-traversal execution: agreement on the query log reproduces the
retained output and annotation log together. -/
theorem runWithAnnotations_eq_of_agree {A : LabeledOracleComp T F Label α} {O O' : T → F}
    (h : ∀ t ∈ A.queries O, O' t = O t) :
    A.runWithAnnotations O' = A.runWithAnnotations O := by
  have hall := run_queries_annotations_eq_of_agree (A := A) h
  ext1 <;> simp [runWithAnnotations_fst, runWithAnnotations_snd, hall.1, hall.2.2]

/-- The retained log contains exactly the ordinary query path. -/
theorem annotations_length_eq_queries
    (A : LabeledOracleComp T F Label α) (O : T → F) :
    (A.annotations O).length = (A.queries O).length := by
  rw [queries_eq_map_annotations, List.length_map]

/-- A query-bounded adaptive computation's one-pass output/annotation log has the same bound. -/
theorem runWithAnnotations_log_length_le
    (A : LabeledOracleComp T F Label α) {Q : ℕ} (hQ : A.QueryBound Q) (O : T → F) :
    (A.runWithAnnotations O).2.length ≤ Q := by
  rw [runWithAnnotations_snd, annotations_length_eq_queries]
  exact A.erase.queries_length_le hQ O

@[simp] theorem findLabel_isSome_iff [DecidableEq T]
    (A : LabeledOracleComp T F Label α) (O : T → F) (t : T) :
    (A.findLabel O t).isSome ↔ t ∈ A.queries O := by
  induction A with
  | pure a => simp [findLabel, queries, erase, OracleComp.queries]
  | query q label k ih =>
      by_cases h : q = t
      · subst t
        simp [findLabel, queries, erase, OracleComp.queries]
      · simpa [findLabel, h, queries, erase, OracleComp.queries, Ne.symm h] using ih (O q)

/-- Post-processing the output with a pure continuation leaves the first labels alone. -/
@[simp] theorem findLabel_bind_pure {β : Type*} [DecidableEq T]
    (A : LabeledOracleComp T F Label α) (f : α → β) (O : T → F) (t : T) :
    (A.bind fun a => pure (f a)).findLabel O t = A.findLabel O t := by
  induction A with
  | pure a => rfl
  | query q label k ih =>
      by_cases h : q = t
      · simp [bind, findLabel, h]
      · simp [bind, findLabel, h, ih (O q)]

/-- If no query-time annotation exists at `t`, reprogramming `t` cannot change the result. -/
theorem run_update_of_findLabel_eq_none [DecidableEq T]
    (A : LabeledOracleComp T F Label α) (O : T → F) (t : T) (v : F)
    (hfresh : A.findLabel O t = none) :
    A.run (Function.update O t v) = A.run O := by
  apply OracleComp.run_update_of_not_mem_queries
  intro hmem
  have : (A.findLabel O t).isSome := (findLabel_isSome_iff A O t).2 hmem
  simp [hfresh] at this

/-- The first annotation at a point is fixed before that point's answer is read. -/
theorem findLabel_update_self [DecidableEq T]
    (A : LabeledOracleComp T F Label α) (O : T → F) (t : T) (v : F) :
    A.findLabel (Function.update O t v) t = A.findLabel O t := by
  induction A with
  | pure a => rfl
  | query q label k ih =>
      by_cases h : q = t
      · subst t
        simp [findLabel]
      · simp [findLabel, h, ih (O q)]

/-- The bad set selected at `t`: use the first query-time annotation when it exists, otherwise
use a set computed from the final output.  The fallback is safe because `findLabel = none` means
reprogramming `t` cannot change that output. -/
def firstLabelOrFallbackBad [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (t : T) (O : T → F) : Set F :=
  match A.findLabel O t with
  | some label => bad t label O
  | none => fallback (A.run O) t O

/-- `firstLabelOrFallbackBad` is blind to the answer at the point it prices. -/
theorem firstLabelOrFallbackBad_update_self [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (hbadBlind : ∀ t label O v,
      bad t label (Function.update O t v) = bad t label O)
    (hfallbackBlind : ∀ a t O v,
      fallback a t (Function.update O t v) = fallback a t O)
    (t : T) (O : T → F) (v : F) :
    firstLabelOrFallbackBad A bad fallback t (Function.update O t v) =
      firstLabelOrFallbackBad A bad fallback t O := by
  rw [firstLabelOrFallbackBad, firstLabelOrFallbackBad, A.findLabel_update_self O t v]
  cases hfound : A.findLabel O t with
  | some label => exact hbadBlind t label O v
  | none =>
    rw [A.run_update_of_findLabel_eq_none O t v hfound]
    exact hfallbackBlind (A.run O) t O v

/-- **Arbitrary adaptive labeled squeeze.**  Complete the adversary with the verifier's selected
query.  Its answer lands in the first pre-answer annotation's bad set, or in the fresh fallback
set, with probability at most `(Q+1)·ε`.  No phase ordering or prefix-determinism premise is
required. -/
theorem firstLabelOrFallbackBad_measure_le
    [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    (A : LabeledOracleComp T F Label α) (xpt : α → T)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (hbadBlind : ∀ t label O v,
      bad t label (Function.update O t v) = bad t label O)
    (hfallbackBlind : ∀ a t O v,
      fallback a t (Function.update O t v) = fallback a t O)
    {epsilon : ENNReal}
    (hbad : ∀ t label O,
      (PMF.uniformOfFintype F).toOuterMeasure (bad t label O) ≤ epsilon)
    (hfallback : ∀ a t O,
      (PMF.uniformOfFintype F).toOuterMeasure (fallback a t O) ≤ epsilon)
    {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | O (xpt (A.run O)) ∈
        firstLabelOrFallbackBad A bad fallback (xpt (A.run O)) O} ≤
      (Q + 1 : ℕ) * epsilon := by
  let esc : T → (T → F) → Set F := firstLabelOrFallbackBad A bad fallback
  have hsub : {O : T → F | O (xpt (A.run O)) ∈ esc (xpt (A.run O)) O} ⊆
      {O : T → F | (A.erase.completing (fun a (_ : Fin 1) => xpt a)).escapesDuringC esc O} := by
    intro O hO
    exact OracleComp.escapesDuringC_completing esc
      (fun a (_ : Fin 1) => xpt a) (j := 0) hO
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  apply escapesDuringC_measure_le' esc
  · exact firstLabelOrFallbackBad_update_self A bad fallback hbadBlind hfallbackBlind
  · intro t O
    unfold esc firstLabelOrFallbackBad
    cases A.findLabel O t with
    | some label => exact hbad t label O
    | none => exact hfallback (A.run O) t O
  · exact OracleComp.queryBound_completing (fun a (_ : Fin 1) => xpt a) hQ

/-- Reduction shell for an output-defined failure event.  Once a computed relation finder covers
every discrepancy between final data and the first query annotation, the no-relation branch is
contained in the arbitrary adaptive labeled squeeze and inherits its `(Q+1) * epsilon` bound. -/
theorem finalBadWithoutRelation_measure_le
    [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    (A : LabeledOracleComp T F Label α) (xpt : α → T)
    (finalBad : α → T → (T → F) → Set F)
    (finder : (T → F) → Option β)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (hcover : ∀ O,
      O (xpt (A.run O)) ∈ finalBad (A.run O) (xpt (A.run O)) O →
      finder O = none →
      O (xpt (A.run O)) ∈ firstLabelOrFallbackBad A bad fallback
        (xpt (A.run O)) O)
    (hbadBlind : ∀ t label O v,
      bad t label (Function.update O t v) = bad t label O)
    (hfallbackBlind : ∀ a t O v,
      fallback a t (Function.update O t v) = fallback a t O)
    {epsilon : ENNReal}
    (hbad : ∀ t label O,
      (PMF.uniformOfFintype F).toOuterMeasure (bad t label O) ≤ epsilon)
    (hfallback : ∀ a t O,
      (PMF.uniformOfFintype F).toOuterMeasure (fallback a t O) ≤ epsilon)
    {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | O (xpt (A.run O)) ∈
          finalBad (A.run O) (xpt (A.run O)) O ∧ finder O = none} ≤
      (Q + 1 : ℕ) * epsilon := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (firstLabelOrFallbackBad_measure_le A xpt bad fallback hbadBlind hfallbackBlind
      hbad hfallback hQ)
  intro O hO
  exact hcover O hO.1 hO.2

theorem firstLabelOrFallbackBad_eq_fallback_of_findLabel_eq_none
    {T F α : Type*} {Label : T → Type*} [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (t : T) (O : T → F) (hfind : A.findLabel O t = none) :
    LabeledOracleComp.firstLabelOrFallbackBad A bad fallback t O =
      fallback (A.run O) t O := by
  unfold LabeledOracleComp.firstLabelOrFallbackBad
  rw [hfind]

theorem firstLabelOrFallbackBad_eq_bad_of_findLabel_eq_some
    {T F α : Type*} {Label : T → Type*} [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (t : T) (O : T → F) (label : Label t)
    (hfind : A.findLabel O t = some label) :
    LabeledOracleComp.firstLabelOrFallbackBad A bad fallback t O = bad t label O := by
  unfold LabeledOracleComp.firstLabelOrFallbackBad
  rw [hfind]

theorem mem_firstLabelOrFallbackBad_of_findLabel_eq_none
    {T F α : Type*} {Label : T → Type*} [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (t : T) (O : T → F) (x : F) (hfind : A.findLabel O t = none)
    (hx : x ∈ fallback (A.run O) t O) :
    x ∈ LabeledOracleComp.firstLabelOrFallbackBad A bad fallback t O := by
  rw [firstLabelOrFallbackBad_eq_fallback_of_findLabel_eq_none
    A bad fallback t O hfind]
  exact hx

theorem mem_firstLabelOrFallbackBad_of_findLabel_eq_some
    {T F α : Type*} {Label : T → Type*} [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (t : T) (O : T → F) (x : F) (label : Label t)
    (hfind : A.findLabel O t = some label) (hx : x ∈ bad t label O) :
    x ∈ LabeledOracleComp.firstLabelOrFallbackBad A bad fallback t O := by
  rw [firstLabelOrFallbackBad_eq_bad_of_findLabel_eq_some
    A bad fallback t O label hfind]
  exact hx

end LabeledOracleComp

end Ragu.Foundation.Oracle
