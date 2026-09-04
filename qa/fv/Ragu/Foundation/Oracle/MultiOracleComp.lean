import Ragu.Foundation.Probability.Bias

/-!
Ported from `Zcash/Common/Oracle/MultiOracleComp.lean` at `zcash/ironwood` commit
`3c056cbebf2880b54f801c348cb67ce7dc9f2a05`. Ragu adapts only the namespace and probability-model import.
-/

/-!
# Adaptive computations with an indexed family of oracles

`MultiOracleComp spec α` generalizes the single-oracle `OracleComp`: a query
names an oracle index `i`, a point in that oracle's domain `spec.domain i`,
and receives an answer in its range `spec.range i`. The security games that
need several oracles — the group-hash indifferentiability game (a pair oracle
and a hash oracle), and the ledger games to come — state their distinguishers
and adversaries over this type; specified parties (simulators, honest oracle
implementations) stay distributions over table families, never computations.

The design follows VCVio's, so the notions correspond by name where they
coincide: `OracleSpec` bundles the indexed domain and range families exactly
as there, and `QueryBound` is the per-index budget of VCVio's structural
`IsQueryBound`. We keep the explicit-constructor presentation of the existing
single-oracle layer rather than VCVio's free-monad one, and `mapQuery` is the
special case of VCVio's `simulate` where each source query is implemented by
exactly one target query plus post-processing — the only case the collapse
arguments need so far.

The machinery mirrors the single-oracle layer index-wise:

- `runTables` answers each query by lookup in a family of tables;
- `QueryBound` carries one budget per oracle;
- `mapQuery` translates oracles, with `runTables_mapQuery` showing the
  translation exact under the induced tables and `queryBound_mapQuery`
  transporting budgets;
- `runFreshPMF` gives every query node a fresh answer from a per-index law,
  and `runFreshPMF_eventBiasLE` is the joint adaptive hybrid: per-index
  one-squeeze biases `ρ i` under budgets `q i` compose to an event bias of at
  most `∑ i, q i * ρ i`, even when later queries depend on earlier answers.

## Why not generalize `OracleComp`?

`OracleComp` stays a separate single-oracle type rather than becoming a
`MultiOracleComp` over a one-element index. The single-oracle case is pervasive
and carries a large mature API —`dedup`, domain restriction, query charging,
labelled trees— that would all have to be re-generalized index-wise. Every
single-oracle site would also pay for a dead index: a `Unit` threaded through
each query, budgets as `Unit → ℕ` instead of `ℕ`, and answers as a projection
instead of a plain type. VCVio unifies the two because its free-monad
`do`-notation hides the indexing; the explicit-constructor presentation here
does not, so the index-free type stays the ergonomic default. A small bridge
connects them where a multi-oracle game collapses to a single-oracle one.
-/

namespace Ragu.Foundation.Oracle

open scoped ENNReal
open Ragu.Foundation.Probability

/-- An indexed family of oracle interfaces: oracle `i` takes query points in
`domain i` and answers in `range i`. The same bundling as VCVio's
`OracleSpec`. -/
structure OracleSpec (ι : Type*) where
  domain : ι → Type*
  range : ι → Type*

/-- An adaptive computation with an indexed family of oracles: a query names
an oracle `i`, a point in its domain, and continues from an answer in its
range. -/
inductive MultiOracleComp {ι : Type*} (spec : OracleSpec ι) (α : Type*) where
  | pure (a : α)
  | query (i : ι) (t : spec.domain i) (k : spec.range i → MultiOracleComp spec α)

namespace MultiOracleComp

variable {ι : Type*} {spec : OracleSpec ι} {α : Type*}

/-- Run the computation against a family of oracle tables, answering each
query by lookup. -/
def runTables : MultiOracleComp spec α → (∀ i, spec.domain i → spec.range i) → α
  | .pure a, _ => a
  | .query i t k, O => (k (O i t)).runTables O

@[simp] theorem runTables_pure (a : α) (O : ∀ i, spec.domain i → spec.range i) :
    (pure a : MultiOracleComp spec α).runTables O = a := rfl

@[simp] theorem runTables_query (i : ι) (t : spec.domain i)
    (k : spec.range i → MultiOracleComp spec α) (O : ∀ i, spec.domain i → spec.range i) :
    (query i t k).runTables O = (k (O i t)).runTables O := rfl

/-- The computation makes at most `q i` queries to oracle `i` on every path
(the per-index budget of VCVio's `IsQueryBound`). -/
inductive QueryBound [DecidableEq ι] : MultiOracleComp spec α → (ι → ℕ) → Prop
  | pure (a : α) (q : ι → ℕ) : QueryBound (.pure a) q
  | query {i : ι} {t : spec.domain i} {k : spec.range i → MultiOracleComp spec α}
      {q : ι → ℕ} (h : ∀ r, QueryBound (k r) q) :
      QueryBound (.query i t k) (Function.update q i (q i + 1))

/-- Implement every oracle of the source family by a single query to a target
family: oracle `i`'s queries go to oracle `π i`, with points translated by `σ`
and answers derived back by `τ`. This is the shape of a computable collapse,
in which a source oracle whose answers are computable from one target-oracle
answer is eliminated. It is the one-query special case of VCVio's
`simulate`. -/
def mapQuery {ι' : Type*} {spec' : OracleSpec ι'} (π : ι → ι')
    (σ : ∀ i, spec.domain i → spec'.domain (π i))
    (τ : ∀ i, spec'.range (π i) → spec.range i) :
    MultiOracleComp spec α → MultiOracleComp spec' α
  | .pure a => .pure a
  | .query i t k => .query (π i) (σ i t) fun r => (k (τ i r)).mapQuery π σ τ

/-- Running the mapped computation against target tables is running the
original against the induced source tables — the deterministic exactness of
the collapse. -/
theorem runTables_mapQuery {ι' : Type*} {spec' : OracleSpec ι'} (π : ι → ι')
    (σ : ∀ i, spec.domain i → spec'.domain (π i))
    (τ : ∀ i, spec'.range (π i) → spec.range i)
    (A : MultiOracleComp spec α) (O' : ∀ i', spec'.domain i' → spec'.range i') :
    (A.mapQuery π σ τ).runTables O'
      = A.runTables (fun i t => τ i (O' (π i) (σ i t))) := by
  induction A with
  | pure a => rfl
  | query i t k ih => exact ih (τ i (O' (π i) (σ i t)))

/-- Budgets transport along `mapQuery`: the target oracle `j` absorbs the
budgets of every source oracle mapped onto it. -/
theorem queryBound_mapQuery [Fintype ι] [DecidableEq ι] {ι' : Type*}
    [DecidableEq ι'] {spec' : OracleSpec ι'} (π : ι → ι')
    (σ : ∀ i, spec.domain i → spec'.domain (π i))
    (τ : ∀ i, spec'.range (π i) → spec.range i)
    {A : MultiOracleComp spec α} {q : ι → ℕ} (hq : A.QueryBound q) :
    (A.mapQuery π σ τ).QueryBound
      (fun j => ∑ i ∈ Finset.univ.filter (fun i => π i = j), q i) := by
  induction hq with
  | pure a q => exact .pure _ _
  | @query i t k q hk ih =>
      have hmem : i ∈ Finset.univ.filter (fun i' => π i' = π i) := by simp
      have hupd : (fun j => ∑ i' ∈ Finset.univ.filter (fun i' => π i' = j),
          Function.update q i (q i + 1) i')
          = Function.update
              (fun j => ∑ i' ∈ Finset.univ.filter (fun i' => π i' = j), q i')
              (π i)
              ((∑ i' ∈ Finset.univ.filter (fun i' => π i' = π i), q i') + 1) := by
        funext j
        rcases eq_or_ne j (π i) with rfl | hj
        · rw [Function.update_self, Finset.sum_update_of_mem hmem]
          have hsum := Finset.add_sum_erase _ q hmem
          rw [Finset.erase_eq] at hsum
          omega
        · rw [Function.update_apply, if_neg hj]
          refine Finset.sum_congr rfl fun i' hi' => ?_
          have hne : i' ≠ i := fun h => hj (h ▸ (Finset.mem_filter.mp hi').2).symm
          rw [Function.update_apply, if_neg hne]
      rw [hupd]
      exact .query fun r => ih (τ i r)

/-- Probabilistic semantics that gives every query node a fresh independent
answer from the queried oracle's law. -/
noncomputable def runFreshPMF (law : ∀ i, PMF (spec.range i)) :
    MultiOracleComp spec α → PMF α
  | .pure a => PMF.pure a
  | .query i _ k => (law i).bind fun r => (k r).runFreshPMF law

/-- **Adaptive joint hybrid over an oracle family.** Per-index weighted
one-squeeze biases accumulate at most once per visited query node, so budgets
`q i` compose them to an event bias of at most `∑ i, q i * ρ i` — even when
later query points, oracle choices, and continuations depend on earlier
answers. The proof follows the single-oracle `runFreshPMF_eventBiasLE`, with
the per-node charge landing on the queried index. -/
theorem runFreshPMF_eventBiasLE [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (spec.range i)]
    {actual ideal : ∀ i, PMF (spec.range i)} {ρ : ι → ℝ≥0∞}
    (hstep : ∀ i, PMFWeightedBiasLE (actual i) (ideal i) (ρ i))
    {A : MultiOracleComp spec α} {q : ι → ℕ} (hq : A.QueryBound q) :
    PMFEventBiasLE (A.runFreshPMF actual) (A.runFreshPMF ideal)
      (∑ i, (q i : ℝ≥0∞) * ρ i) := by
  induction hq with
  | pure a q =>
      intro S
      exact le_add_right le_rfl
  | @query i t k q hk ih =>
      intro S
      simp only [runFreshPMF, PMF.toOuterMeasure_bind_apply, tsum_fintype]
      have hcontinuation :
          ∑ r, actual i r * (runFreshPMF actual (k r)).toOuterMeasure S ≤
            ∑ r, actual i r * ((runFreshPMF ideal (k r)).toOuterMeasure S +
              ∑ j, (q j : ℝ≥0∞) * ρ j) :=
        Finset.sum_le_sum fun r _ => mul_le_mul_right (ih r S) _
      refine hcontinuation.trans ?_
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      have hmass : (∑ r : spec.range i, actual i r) = 1 := by
        have h := (actual i).tsum_coe
        rwa [tsum_fintype] at h
      rw [hmass, one_mul]
      have hweight := hstep i
        (fun r => (runFreshPMF ideal (k r)).toOuterMeasure S)
        (fun r => (PMF.toOuterMeasure_mono _ (Set.subset_univ _)).trans_eq (by
          rw [PMF.toOuterMeasure_apply, Set.indicator_univ]
          exact (runFreshPMF ideal (k r)).tsum_coe))
      have hupd : ∑ j, (Function.update q i (q i + 1) j : ℝ≥0∞) * ρ j
          = (∑ j, (q j : ℝ≥0∞) * ρ j) + ρ i := by
        have hmem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
        rw [show (fun j => (Function.update q i (q i + 1) j : ℝ≥0∞) * ρ j)
            = Function.update (fun j => (q j : ℝ≥0∞) * ρ j) i
                (((q i : ℝ≥0∞) + 1) * ρ i) by
          funext j
          rcases eq_or_ne j i with rfl | hj
          · rw [Function.update_self, Function.update_self]
            push_cast
            ring
          · rw [Function.update_apply, if_neg hj, Function.update_apply, if_neg hj]]
        rw [Finset.sum_update_of_mem hmem, add_mul, one_mul,
          ← Finset.add_sum_erase _ (fun j => (q j : ℝ≥0∞) * ρ j) hmem, Finset.erase_eq]
        ring
      rw [hupd]
      calc
        ∑ r, actual i r * (runFreshPMF ideal (k r)).toOuterMeasure S
            + ∑ j, (q j : ℝ≥0∞) * ρ j
          ≤ (∑ r, ideal i r * (runFreshPMF ideal (k r)).toOuterMeasure S + ρ i)
              + ∑ j, (q j : ℝ≥0∞) * ρ j :=
            add_le_add hweight le_rfl
        _ = ∑ r, ideal i r * (runFreshPMF ideal (k r)).toOuterMeasure S
              + ((∑ j, (q j : ℝ≥0∞) * ρ j) + ρ i) := by ring

end MultiOracleComp

end Ragu.Foundation.Oracle
