import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Polynomial.Vieta
import CompPoly.Univariate.ToPoly
import CompPoly.Univariate.Linear
import CompPoly.Univariate.Roots.Enumeration
import CompPoly.Univariate.DivisionCorrectness
import CompPoly.Univariate.Lagrange

/-!
The generic core is ported from `Zcash/Common/CPolynomial.lean` at `zcash/ironwood` commit
`3c056cbebf2880b54f801c348cb67ce7dc9f2a05`. It deliberately retains the source's `CompPoly.CPolynomial` extension namespace
and omits only Ironwood's concrete `Fp` wrapper.
-/

/-!
# General theory for the computable polynomial representation

`CompPoly.CPolynomial R` is `{ p : Array R // no trailing zeros }`: a canonical representation, so
`DecidableEq` is available and every ring operation is executable.  `CPolynomial.toPoly` is one
half of a proven ring isomorphism onto Mathlib's `Polynomial R`, which is what lets the two views
be identified freely.

This file collects the theory the Zcash development needs on top of what CompPoly already proves.
Everything in the `CompPoly.CPolynomial` namespace below is stated generically and is intended to
be upstreamed; it is kept here only so the migration does not block on an external repository.
The Zcash-specific part is the `Fp` instantiation at the end.

## Why this exists at all

Mathlib's `Polynomial` instances live in a `noncomputable section`.  A definition that touches
one becomes `noncomputable`, and that marker propagates through every downstream definition
without being visible at any of their definition sites.  Nothing here is `noncomputable`.
-/

namespace CompPoly.CPolynomial

variable {R : Type*}

/-! ## Evaluation algebra

CompPoly proves `eval_C`, `eval_mul`, `eval_one` and `eval_sub`; the additive and `X`/`pow` cases
are proved here.  Together they form a simp set that discharges the evaluation inductions in the
verifier layer without any manual transport to the Mathlib image. -/

@[simp]
theorem eval_zero [Semiring R] [BEq R] [LawfulBEq R] (x : R) :
    (0 : CPolynomial R).eval x = 0 := by
  rw [eval_toPoly, toPoly_zero, Polynomial.eval_zero]

@[simp]
theorem eval_add [Semiring R] [BEq R] [LawfulBEq R] (x : R) (p q : CPolynomial R) :
    (p + q).eval x = p.eval x + q.eval x := by
  rw [eval_toPoly, toPoly_add, Polynomial.eval_add, ← eval_toPoly, ← eval_toPoly]

@[simp]
theorem eval_neg [Ring R] [BEq R] [LawfulBEq R] (x : R) (p : CPolynomial R) :
    (-p).eval x = -p.eval x := by
  rw [eval_toPoly, toPoly_neg, Polynomial.eval_neg, ← eval_toPoly]

@[simp]
theorem eval_X [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (x : R) :
    (X : CPolynomial R).eval x = x := by
  rw [eval_toPoly, X_toPoly, Polynomial.eval_X]

@[simp]
theorem eval_pow [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (x : R) (p : CPolynomial R) (n : ℕ) :
    (p ^ n).eval x = p.eval x ^ n := by
  induction n with
  | zero => simp [eval_one]
  | succ n ih => rw [pow_succ, pow_succ, eval_mul, ih]

theorem eval_finsetSum {ι : Type*} [DecidableEq ι] [CommSemiring R] [BEq R] [LawfulBEq R]
    [Nontrivial R] (s : Finset ι) (f : ι → CPolynomial R) (x : R) :
    (∑ i ∈ s, f i).eval x = ∑ i ∈ s, (f i).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, eval_add, ih]

theorem eval_prod {ι : Type*} [DecidableEq ι] [CommSemiring R] [BEq R] [LawfulBEq R]
    [Nontrivial R] (s : Finset ι) (f : ι → CPolynomial R) (x : R) :
    (∏ i ∈ s, f i).eval x = ∏ i ∈ s, (f i).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eval_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, eval_mul, ih]

attribute [simp] eval_C eval_mul eval_one eval_sub

/-! ## Transport to the Mathlib image

These are the `simp` lemmas that push `toPoly` inwards, so a goal about the computable
representation becomes a goal about `Polynomial R` in one `simp` call. -/

attribute [simp] toPoly_add toPoly_mul toPoly_sub toPoly_neg toPoly_one toPoly_zero
  C_toPoly X_toPoly

/-- `toPoly` of a list product.  CompPoly has the `Finset` versions (`toPoly_prod`, `toPoly_sum`);
the row-polynomial constructions build their products over `List.ofFn`, where a `Finset` reindexing
would only be noise. -/
theorem toPoly_list_prod [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (l : List (CPolynomial R)) : l.prod.toPoly = (l.map toPoly).prod :=
  map_list_prod (ringEquiv : CPolynomial R ≃+* Polynomial R) l

/-- `toPoly` of a list sum. -/
theorem toPoly_list_sum [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (l : List (CPolynomial R)) : l.sum.toPoly = (l.map toPoly).sum :=
  map_list_sum (ringEquiv : CPolynomial R ≃+* Polynomial R) l

/-- `toPoly` of a multiset product. -/
theorem toPoly_multiset_prod [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (m : Multiset (CPolynomial R)) : m.prod.toPoly = (m.map toPoly).prod :=
  map_multiset_prod (ringEquiv : CPolynomial R ≃+* Polynomial R) m

/-- `toPoly` is injective.  CompPoly states this as `toPolyLinearEquiv.injective`, whose hypothesis
is phrased through the bundled coercion; this restates it directly on `toPoly` so callers do not
need a `change` at every use. -/
theorem toPoly_injective [Semiring R] [BEq R] [LawfulBEq R] {p q : CPolynomial R}
    (h : p.toPoly = q.toPoly) : p = q :=
  toPolyLinearEquiv.injective h

/-- Coefficient extensionality, the computable counterpart of `Polynomial.ext`. -/
theorem ext_coeff [Semiring R] [BEq R] [LawfulBEq R] {p q : CPolynomial R}
    (h : ∀ n, p.coeff n = q.coeff n) : p = q :=
  toPoly_injective (Polynomial.ext fun n => by rw [← coeff_toPoly, ← coeff_toPoly, h])

/-! ## Functoriality in the coefficient ring

CompPoly has no `map`: nothing pushes a ring hom through the coefficients, which is why every
change of coefficient ring so far had to detour through `Polynomial.map`.  `map` below is that
operation, computable — apply `f` entrywise and re-canonicalise, since a non-injective `f` can
create trailing zeros. -/

section Map

variable {S : Type*}

/-- Apply a ring hom to every coefficient. -/
def map [Semiring R] [BEq R] [LawfulBEq R] [Semiring S] [BEq S] [LawfulBEq S]
    (f : R →+* S) (p : CPolynomial R) : CPolynomial S :=
  ofArray (p.val.map f)

@[simp] theorem coeff_map [Semiring R] [BEq R] [LawfulBEq R] [Semiring S] [BEq S] [LawfulBEq S]
    (f : R →+* S) (p : CPolynomial R) (n : ℕ) : (map f p).coeff n = f (p.coeff n) := by
  rw [map, coeff_ofArray]
  show (p.val.map f).getD n 0 = f (p.val.getD n 0)
  by_cases h : n < p.val.size
  · rw [Array.getD, Array.getD, dif_pos (by simpa using h), dif_pos h]
    simp
  · rw [Array.getD, Array.getD, dif_neg (by simpa using h), dif_neg h, map_zero]

/-- `map` is Mathlib's `Polynomial.map` read across `toPoly`. -/
theorem toPoly_map [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [CommSemiring S] [BEq S] [LawfulBEq S] [Nontrivial S] (f : R →+* S) (p : CPolynomial R) :
    (map f p).toPoly = p.toPoly.map f := by
  refine Polynomial.ext fun n => ?_
  rw [← coeff_toPoly, Polynomial.coeff_map, ← coeff_toPoly, coeff_map]

@[simp] theorem map_zero [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [CommSemiring S] [BEq S] [LawfulBEq S] [Nontrivial S] (f : R →+* S) :
    map f (0 : CPolynomial R) = 0 :=
  ext_coeff fun n => by rw [coeff_map, coeff_zero, coeff_zero, _root_.map_zero]

@[simp] theorem map_C [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [CommSemiring S] [BEq S] [LawfulBEq S] [Nontrivial S] (f : R →+* S) (r : R) :
    map f (C r) = C (f r) :=
  ext_coeff fun n => by
    rw [coeff_map, coeff_C, coeff_C]
    split <;> simp

@[simp] theorem map_X [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [CommSemiring S] [BEq S] [LawfulBEq S] [Nontrivial S] (f : R →+* S) :
    map f (X : CPolynomial R) = X :=
  toPoly_injective (by rw [toPoly_map, X_toPoly, Polynomial.map_X, X_toPoly])

theorem map_add [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [CommSemiring S] [BEq S] [LawfulBEq S] [Nontrivial S] (f : R →+* S) (p q : CPolynomial R) :
    map f (p + q) = map f p + map f q :=
  ext_coeff fun n => by
    rw [coeff_map, coeff_add, coeff_add, coeff_map, coeff_map, _root_.map_add]

theorem map_mul [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [CommSemiring S] [BEq S] [LawfulBEq S] [Nontrivial S] (f : R →+* S) (p q : CPolynomial R) :
    map f (p * q) = map f p * map f q :=
  toPoly_injective (by rw [toPoly_map, toPoly_mul, Polynomial.map_mul, ← toPoly_map, ← toPoly_map,
    ← toPoly_mul])

/-- `map` bundled as a ring hom. -/
def mapRingHom [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [CommSemiring S] [BEq S] [LawfulBEq S] [Nontrivial S] (f : R →+* S) :
    CPolynomial R →+* CPolynomial S where
  toFun := map f
  map_one' := toPoly_injective (by rw [toPoly_map, toPoly_one, Polynomial.map_one, toPoly_one])
  map_mul' := map_mul f
  map_zero' := map_zero f
  map_add' := map_add f

@[simp] theorem coe_mapRingHom [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [CommSemiring S] [BEq S] [LawfulBEq S] [Nontrivial S] (f : R →+* S) :
    (mapRingHom f : CPolynomial R → CPolynomial S) = map f := rfl

theorem map_multiset_prod [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [CommSemiring S] [BEq S] [LawfulBEq S] [Nontrivial S] (f : R →+* S)
    (m : Multiset (CPolynomial R)) : map f m.prod = (m.map (map f)).prod := by
  simpa using _root_.map_multiset_prod (mapRingHom f) m

theorem map_sub [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [CommRing S] [BEq S] [LawfulBEq S] [Nontrivial S] (f : R →+* S) (p q : CPolynomial R) :
    map f (p - q) = map f p - map f q := by
  simpa using _root_.map_sub (mapRingHom f) p q

end Map

/-! ## Coefficients -/

theorem coeff_finsetSum {ι : Type*} [DecidableEq ι] [CommSemiring R] [BEq R] [LawfulBEq R]
    [Nontrivial R] (s : Finset ι) (f : ι → CPolynomial R) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, coeff_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add, ih]

theorem coeff_eq_zero_of_natDegree_lt [Semiring R] [BEq R] [LawfulBEq R] {p : CPolynomial R}
    {n : ℕ} (h : p.natDegree < n) : p.coeff n = 0 := by
  rw [coeff_toPoly]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [← natDegree_toPoly])

theorem coeff_X_pow [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (k n : ℕ) :
    ((X : CPolynomial R) ^ k).coeff n = if n = k then 1 else 0 := by
  rw [coeff_toPoly, toPoly_pow, X_toPoly, Polynomial.coeff_X_pow]

/-- **Identity from samples.** A polynomial of degree below the number of pairwise-distinct sample
points at which it vanishes is zero.  Mathlib's `eq_zero_of_natDegree_lt_card_of_eval_eq_zero` on
the computable representation. -/
theorem eq_zero_of_natDegree_lt_card_of_eval_eq_zero [CommRing R] [IsDomain R] [BEq R]
    [LawfulBEq R] [Nontrivial R] (p : CPolynomial R) {ι : Type*} [Fintype ι] {f : ι → R}
    (hf : Function.Injective f) (heval : ∀ i, p.eval (f i) = 0)
    (hcard : p.natDegree < Fintype.card ι) : p = 0 := by
  refine toPoly_injective ?_
  rw [toPoly_zero]
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hf (fun i => ?_) ?_
  · rw [← eval_toPoly]; exact heval i
  · rwa [← natDegree_toPoly]

/-! ## Degree of multiset sums, products and elementary symmetric functions -/

section MultisetDegree

variable [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]

theorem natDegree_multiset_prod_le (m : Multiset (CPolynomial R)) :
    m.prod.natDegree ≤ (m.map natDegree).sum := by
  rw [natDegree_toPoly, toPoly_multiset_prod]
  refine le_trans (Polynomial.natDegree_multiset_prod_le _) (le_of_eq ?_)
  rw [Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => (natDegree_toPoly p).symm)

theorem natDegree_multiset_prod_le_of_forall_le {m : Multiset (CPolynomial R)} {d : ℕ}
    (h : ∀ p ∈ m, p.natDegree ≤ d) : m.prod.natDegree ≤ Multiset.card m * d := by
  refine le_trans (natDegree_multiset_prod_le m) ?_
  calc (m.map natDegree).sum
      ≤ (m.map fun _ => d).sum :=
        Multiset.sum_map_le_sum_map _ _ (fun p hp => h p hp)
    _ = Multiset.card m * d := by simp [Multiset.sum_replicate, Multiset.map_const']

omit [Nontrivial R] in
theorem natDegree_multiset_sum_le_of_forall_le [DecidableEq R] {m : Multiset (CPolynomial R)}
    {d : ℕ} (h : ∀ p ∈ m, p.natDegree ≤ d) : m.sum.natDegree ≤ d := by
  induction m using Multiset.induction with
  | empty =>
      rw [Multiset.sum_zero, natDegree_toPoly, toPoly_zero, Polynomial.natDegree_zero]
      exact Nat.zero_le d
  | cons p m ih =>
      rw [Multiset.sum_cons]
      refine le_trans (natDegree_add_le _ _) (max_le (h p (Multiset.mem_cons_self _ _)) ?_)
      exact ih fun q hq => h q (Multiset.mem_cons_of_mem hq)

/-- The `k`-th elementary symmetric function of polynomials of degree at most `d` has degree at
most `k * d`: it is a sum of products of `k` of them. -/
theorem natDegree_esymm_le {m : Multiset (CPolynomial R)} {d : ℕ}
    (h : ∀ p ∈ m, p.natDegree ≤ d) (k : ℕ) : (m.esymm k).natDegree ≤ k * d := by
  classical
  refine natDegree_multiset_sum_le_of_forall_le fun q hq => ?_
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hq
  have hcard : Multiset.card t = k := (Multiset.mem_powersetCard.mp ht).2
  have hle : t.prod.natDegree ≤ Multiset.card t * d :=
    natDegree_multiset_prod_le_of_forall_le fun p hp =>
      h p (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hp)
  rwa [hcard] at hle

end MultisetDegree

/-! ## Products of monic linear factors

Vieta and the degree of `∏ (X + uᵢ)`, on the computable representation.  Both are Mathlib's
statements read across `toPoly`; CompPoly has neither. -/

section MonicLinearProduct

variable [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]

private theorem toPoly_prod_X_add_C (m : Multiset R) :
    ((m.map (fun u => X + C u)).prod).toPoly
      = (m.map (fun u => Polynomial.X + Polynomial.C u)).prod := by
  rw [toPoly_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun u _ => by simp)

/-- A product of `card m` monic linear factors has degree `card m`. -/
theorem natDegree_prod_X_add_C (m : Multiset R) :
    ((m.map (fun u => X + C u)).prod).natDegree = Multiset.card m := by
  rw [natDegree_toPoly, toPoly_prod_X_add_C]
  rw [Polynomial.natDegree_multiset_prod_of_monic (h := fun f hf => by
    obtain ⟨u, _, rfl⟩ := Multiset.mem_map.mp hf
    exact Polynomial.monic_X_add_C u)]
  simp [Multiset.map_map]

/-- Such a product has no coefficients above its degree. -/
theorem coeff_prod_X_add_C_eq_zero (m : Multiset R) {j : ℕ} (hj : Multiset.card m < j) :
    ((m.map (fun u => X + C u)).prod).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [natDegree_prod_X_add_C]; exact hj)

/-- **Vieta.** Below the degree, the `j`-th coefficient is an elementary symmetric polynomial in
the roots' negatives — here the shifts `uᵢ` themselves, since the factors are `X + uᵢ`. -/
theorem coeff_prod_X_add_C (m : Multiset R) {j : ℕ} (hj : j ≤ Multiset.card m) :
    ((m.map (fun u => X + C u)).prod).coeff j = m.esymm (Multiset.card m - j) := by
  rw [coeff_toPoly, toPoly_prod_X_add_C]
  exact Multiset.prod_X_add_C_coeff m hj

/-- The leading coefficient of a product of monic linear factors is `1`. -/
theorem leadingCoeff_prod_X_add_C (m : Multiset R) :
    ((m.map (fun u => X + C u)).prod).leadingCoeff = 1 := by
  rw [leadingCoeff_eq_coeff_natDegree, natDegree_prod_X_add_C]
  rw [coeff_prod_X_add_C _ (le_refl _), Nat.sub_self]
  simp [Multiset.esymm]

/-- Such a product is nonzero: it is monic. -/
theorem prod_X_add_C_ne_zero (m : Multiset R) :
    (m.map (fun u => X + C u)).prod ≠ 0 := fun h => by
  have h1 := leadingCoeff_prod_X_add_C m
  rw [h, leadingCoeff_eq_coeff_natDegree, coeff_zero] at h1
  exact zero_ne_one h1

end MonicLinearProduct

theorem natDegree_sum_le_of_forall_le {ι : Type*} [DecidableEq ι] [CommSemiring R] [BEq R]
    [LawfulBEq R] [Nontrivial R] (s : Finset ι) (f : ι → CPolynomial R) {n : ℕ}
    (h : ∀ i ∈ s, (f i).natDegree ≤ n) : (∑ i ∈ s, f i).natDegree ≤ n := by
  rw [natDegree_toPoly, toPoly_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  rw [← natDegree_toPoly]
  exact h i hi

/-- A `WithBot ℕ` degree bound on the Mathlib image gives the `natDegree` bound, the zero
polynomial included.  Interpolation bounds arrive in this shape from
`Lagrange.degree_interpolate_lt` and are wanted in the other. -/
theorem natDegree_lt_of_degree_toPoly_lt [Semiring R] [BEq R] [LawfulBEq R] {p : CPolynomial R}
    {n : ℕ} (hn : 0 < n) (h : p.toPoly.degree < (n : WithBot ℕ)) : p.natDegree < n := by
  rw [natDegree_toPoly]
  by_cases hzero : p.toPoly = 0
  · rw [hzero, Polynomial.natDegree_zero]
    exact hn
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr h

theorem natDegree_le_iff_coeff_eq_zero [Semiring R] [BEq R] [LawfulBEq R]
    {p : CPolynomial R} {n : ℕ} :
    p.natDegree ≤ n ↔ ∀ m : ℕ, n < m → p.coeff m = 0 := by
  rw [natDegree_toPoly, Polynomial.natDegree_le_iff_coeff_eq_zero]
  exact forall_congr' fun m => forall_congr' fun _ => by rw [coeff_toPoly]

/-! ## Degree arithmetic -/

/-- Mapping the coefficients cannot raise the degree. -/
theorem natDegree_map_le {S : Type*} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    [CommSemiring S] [BEq S] [LawfulBEq S] [Nontrivial S] (f : R →+* S) (p : CPolynomial R) :
    (map f p).natDegree ≤ p.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun n hn => by
    rw [coeff_map, coeff_eq_zero_of_natDegree_lt hn, _root_.map_zero]

theorem natDegree_sub_le [Ring R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) :
    (p - q).natDegree ≤ max p.natDegree q.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly, natDegree_toPoly, toPoly_sub]
  exact Polynomial.natDegree_sub_le _ _

theorem natDegree_mul_le [Semiring R] [BEq R] [LawfulBEq R] {p q : CPolynomial R} :
    (p * q).natDegree ≤ p.natDegree + q.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly, natDegree_toPoly, toPoly_mul]
  exact Polynomial.natDegree_mul_le

theorem natDegree_X_pow_le [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (n : ℕ) :
    ((X : CPolynomial R) ^ n).natDegree ≤ n := by
  rw [natDegree_toPoly, toPoly_pow, X_toPoly]
  simp

@[simp]
theorem natDegree_zero [Semiring R] [BEq R] [LawfulBEq R] :
    (0 : CPolynomial R).natDegree = 0 := by
  rw [natDegree_toPoly, toPoly_zero, Polynomial.natDegree_zero]

@[simp]
theorem natDegree_one [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    (1 : CPolynomial R).natDegree = 0 := by
  rw [natDegree_toPoly, toPoly_one, Polynomial.natDegree_one]

@[simp]
theorem natDegree_X [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    (X : CPolynomial R).natDegree = 1 := by
  rw [natDegree_toPoly, X_toPoly, Polynomial.natDegree_X]

theorem natDegree_X_le [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    (X : CPolynomial R).natDegree ≤ 1 := natDegree_X.le

@[simp]
theorem natDegree_neg [Ring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    (-p).natDegree = p.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly, toPoly_neg, Polynomial.natDegree_neg]

theorem natDegree_pow_le [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    {p : CPolynomial R} {n : ℕ} : (p ^ n).natDegree ≤ n * p.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly, toPoly_pow]
  exact Polynomial.natDegree_pow_le

theorem natDegree_C_mul_le [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (a : R) (p : CPolynomial R) : (C a * p).natDegree ≤ p.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly, toPoly_mul, C_toPoly]
  exact Polynomial.natDegree_C_mul_le a p.toPoly

theorem natDegree_prod_le {ι : Type*} [DecidableEq ι] [CommSemiring R] [BEq R] [LawfulBEq R]
    [Nontrivial R] (s : Finset ι) (f : ι → CPolynomial R) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, (f i).natDegree := by
  rw [natDegree_toPoly, toPoly_prod]
  simpa [natDegree_toPoly] using Polynomial.natDegree_prod_le s (fun i => (f i).toPoly)

theorem natDegree_sum_le {ι : Type*} [DecidableEq ι] [Semiring R] [BEq R] [LawfulBEq R]
    (s : Finset ι) (f : ι → CPolynomial R) :
    (∑ i ∈ s, f i).natDegree ≤ s.fold max 0 fun i => (f i).natDegree := by
  rw [natDegree_toPoly, toPoly_sum]
  simpa [Function.comp_def, natDegree_toPoly] using
    Polynomial.natDegree_sum_le s (fun i => (f i).toPoly)

/-! ## Divisibility and division by a monic polynomial

`toPoly` is a ring isomorphism, so divisibility transports.  `modByMonic` is CompPoly's own
executable remainder; the algebra it satisfies is Mathlib's, read across the isomorphism. -/

theorem dvd_iff_toPoly_dvd [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    {p q : CPolynomial R} : p ∣ q ↔ p.toPoly ∣ q.toPoly :=
  (map_dvd_iff (ringEquiv : CPolynomial R ≃+* Polynomial R)).symm

theorem zero_modByMonic [Field R] [BEq R] [LawfulBEq R] {r : CPolynomial R} (hr : r.monic) :
    modByMonic 0 r = 0 := by
  apply toPoly_injective
  simp [modByMonic_toPoly_eq_modByMonic _ _ hr, Polynomial.zero_modByMonic]

theorem add_modByMonic [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial R)
    {r : CPolynomial R} (hr : r.monic) :
    modByMonic (p + q) r = modByMonic p r + modByMonic q r := by
  apply toPoly_injective
  simp only [toPoly_add, modByMonic_toPoly_eq_modByMonic _ _ hr, Polynomial.add_modByMonic]

theorem C_mul_modByMonic [Field R] [BEq R] [LawfulBEq R] (a : R) (p : CPolynomial R)
    {r : CPolynomial R} (hr : r.monic) :
    modByMonic (C a * p) r = C a * modByMonic p r := by
  apply toPoly_injective
  simp only [toPoly_mul, C_toPoly, modByMonic_toPoly_eq_modByMonic _ _ hr,
    ← Polynomial.smul_eq_C_mul, Polynomial.smul_modByMonic]

theorem modByMonic_eq_zero_iff_dvd [Field R] [BEq R] [LawfulBEq R] {p r : CPolynomial R}
    (hr : r.monic) : modByMonic p r = 0 ↔ r ∣ p := by
  rw [← toPoly_eq_zero_iff, modByMonic_toPoly_eq_modByMonic _ _ hr, dvd_iff_toPoly_dvd]
  exact Polynomial.modByMonic_eq_zero_iff_dvd ((monic_toPoly_iff r).mp hr)

/-! ## Bundled homomorphisms

Mathlib's `Polynomial.C` and `Polynomial.evalRingHom` are bundled; CompPoly's `C` and `eval` are
bare functions.  Every `eval₂`-shaped construction, and every ring-hom transport in the verifier
layer, needs the bundled forms. -/

/-- The constant embedding as a ring hom. -/
def CRingHom [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : R →+* CPolynomial R where
  toFun := C
  map_one' := by apply toPoly_injective; simp
  map_mul' := by intro a b; apply toPoly_injective; simp
  map_zero' := by apply toPoly_injective; simp
  map_add' := by intro a b; apply toPoly_injective; simp

/-- `C` is multiplicative and respects powers.  The bundled `CRingHom` says so; these are the
unbundled spellings.  Deliberately not `simp`: pushing `C` inwards turns `C (ω ^ m)` into
`C ω ^ m`, which no longer matches the rotation lemmas. -/
theorem C_mul [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (a b : R) :
    (C (a * b) : CPolynomial R) = C a * C b := by
  apply toPoly_injective; simp

@[simp]
theorem C_add [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (a b : R) :
    (C (a + b) : CPolynomial R) = C a + C b := by
  apply toPoly_injective; simp

theorem C_pow [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (a : R) (n : ℕ) :
    (C (a ^ n) : CPolynomial R) = C a ^ n := by
  apply toPoly_injective; simp [toPoly_pow]

attribute [simp] natDegree_C

/-- Evaluation at `x` as a ring hom. -/
def evalRingHom [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (x : R) :
    CPolynomial R →+* R where
  toFun := eval x
  map_one' := eval_one x
  map_mul' := fun p q => eval_mul p q x
  map_zero' := eval_zero x
  map_add' := eval_add x

@[simp]
theorem coe_evalRingHom [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (x : R) :
    ⇑(evalRingHom x) = eval x := rfl

theorem eval_multiset_prod [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (m : Multiset (CPolynomial R)) (x : R) : (m.prod).eval x = (m.map (eval x)).prod := by
  simpa using _root_.map_multiset_prod (evalRingHom x) m

/-! ## Composition

CompPoly has `eval₂` but no `comp`.  With the constant embedding bundled, composition is `eval₂`
at that hom, and the Mathlib characterisation follows from `eval₂_toPoly` together with
`Polynomial.hom_eval₂` transported along `ringEquiv`. -/

/-- Polynomial composition: `comp p q` is `p ∘ q`. -/
def comp [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (p q : CPolynomial R) :
    CPolynomial R :=
  eval₂ CRingHom q p

theorem toPoly_comp [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p q : CPolynomial R) : (comp p q).toPoly = p.toPoly.comp q.toPoly := by
  have hring :
      ((ringEquiv : CPolynomial R ≃+* Polynomial R) : CPolynomial R →+* Polynomial R).comp
          CRingHom = Polynomial.C := by
    refine RingHom.ext fun c => ?_
    show (C c : CPolynomial R).toPoly = Polynomial.C c
    exact C_toPoly c
  rw [comp, eval₂_toPoly]
  have h := Polynomial.hom_eval₂ p.toPoly CRingHom
    ((ringEquiv : CPolynomial R ≃+* Polynomial R) : CPolynomial R →+* Polynomial R) q
  rw [hring] at h
  exact h.trans rfl

theorem eval_comp [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p q : CPolynomial R) (x : R) :
    (comp p q).eval x = p.eval (eval x q) := by
  rw [eval_toPoly, toPoly_comp, Polynomial.eval_comp, ← eval_toPoly, ← eval_toPoly]

theorem natDegree_comp [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [NoZeroDivisors R]
    (p q : CPolynomial R) :
    (comp p q).natDegree = p.natDegree * q.natDegree := by
  rw [natDegree_toPoly, toPoly_comp, Polynomial.natDegree_comp, ← natDegree_toPoly,
    ← natDegree_toPoly]

/-! ## Rotation

Composition with `C w * X` is the column rotation the halo2 verifier performs; it is worth naming
because both of its properties are used at every rotated-column site. -/

/-- Evaluating a rotated column rescales the point. -/
theorem eval_comp_C_mul_X [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) (w x : R) :
    (comp p (C w * X)).eval x = p.eval (w * x) := by
  rw [eval_comp, eval_mul, eval_C, eval_X]

/-- Rotation by a nonzero factor preserves degree. -/
theorem natDegree_comp_C_mul_X [Field R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) {w : R} (hw : w ≠ 0) :
    (comp p (C w * X)).natDegree = p.natDegree := by
  have hq : ((C w * X : CPolynomial R)).natDegree = 1 := by
    rw [natDegree_toPoly, toPoly_mul, C_toPoly, X_toPoly, Polynomial.natDegree_C_mul hw,
      Polynomial.natDegree_X]
  rw [natDegree_comp, hq, Nat.mul_one]

/-- `CPolynomial R` is a domain whenever `R` is: it is ring-isomorphic to `Polynomial R`, which
Mathlib knows is one.  Without this the roots theory below cannot be instantiated at a coefficient
ring that is itself a polynomial ring, which is exactly what the bivariate arguments need. -/
instance instIsDomain [CommRing R] [IsDomain R] [BEq R] [LawfulBEq R] :
    IsDomain (CPolynomial R) :=
  (ringEquiv (R := R)).toMulEquiv.isDomain (Polynomial R)

/-- Over a domain the leading coefficient is multiplicative. -/
theorem leadingCoeff_mul [CommRing R] [IsDomain R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) :
    (p * q).leadingCoeff = p.leadingCoeff * q.leadingCoeff := by
  rw [leadingCoeff_toPoly, leadingCoeff_toPoly, leadingCoeff_toPoly, toPoly_mul,
    Polynomial.leadingCoeff_mul]

/-- The leading coefficient of a constant is itself. -/
theorem leadingCoeff_C [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] (r : R) :
    (C r : CPolynomial R).leadingCoeff = r := by
  rw [leadingCoeff_toPoly, C_toPoly, Polynomial.leadingCoeff_C]

theorem C_injective [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    Function.Injective (C : R → CPolynomial R) := fun a b hab => by
  have := congrArg toPoly hab
  rw [C_toPoly, C_toPoly] at this
  exact Polynomial.C_injective this

theorem C_eq_zero_iff [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] {r : R} :
    (C r : CPolynomial R) = 0 ↔ r = 0 := by
  rw [← toPoly_eq_zero_iff, C_toPoly, Polynomial.C_eq_zero]

/-! ## Roots with multiplicity

Mathlib's `Polynomial.roots` — the multiset of roots counted with multiplicity, obtained by
repeated factorisation over a domain.  It is `noncomputable` there and stays so here; multiplicity
over an abstract domain is not something one runs.  These are thin wrappers, so the factorisation
theory applies to the computable representation without a detour through `toPoly` at every use. -/

section Roots

variable [CommRing R] [IsDomain R] [BEq R] [LawfulBEq R]

/-- The roots of a computable polynomial, with multiplicity. -/
noncomputable def roots (p : CPolynomial R) : Multiset R := p.toPoly.roots

omit [BEq R] [LawfulBEq R] in
@[simp] theorem roots_zero : roots (0 : CPolynomial R) = 0 := by
  rw [roots, toPoly_zero, Polynomial.roots_zero]

theorem mem_roots {p : CPolynomial R} (hp : p ≠ 0) {x : R} :
    x ∈ p.roots ↔ p.eval x = 0 := by
  rw [roots, Polynomial.mem_roots (by rwa [Ne, toPoly_eq_zero_iff]), Polynomial.IsRoot,
    ← eval_toPoly]

/-- At most `natDegree` roots, with multiplicity. -/
theorem card_roots_le (p : CPolynomial R) : Multiset.card p.roots ≤ p.natDegree := by
  rw [roots, natDegree_toPoly]
  exact Polynomial.card_roots' _

/-- The roots of `∏ (X - aᵢ)` are the `aᵢ`. -/
theorem roots_multiset_prod_X_sub_C (m : Multiset R) :
    ((m.map (fun a => X - C a)).prod).roots = m := by
  rw [roots, toPoly_multiset_prod, Multiset.map_map]
  have hfac : m.map ((fun p => toPoly p) ∘ fun a => X - C a)
      = m.map (fun a => Polynomial.X - Polynomial.C a) :=
    Multiset.map_congr rfl fun a _ => by simp
  rw [hfac, Polynomial.roots_multiset_prod_X_sub_C]

/-- The roots of `∏ (X + uᵢ)` are the negated shifts. -/
theorem roots_prod_X_add_C (m : Multiset R) :
    ((m.map (fun u => X + C u)).prod).roots = m.map (fun u => -u) := by
  have hrw : m.map (fun u => X + C u)
      = (m.map (fun u => -u)).map (fun a => X - C a) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun u _ => ?_
    rw [Function.comp_apply]
    refine toPoly_injective ?_
    rw [toPoly_sub, toPoly_add, C_toPoly, C_toPoly, Polynomial.C_neg, sub_neg_eq_add]
  rw [hrw, roots_multiset_prod_X_sub_C]

end Roots

/-! ## Distinct roots over an enumerated field

`Polynomial.roots` is a `Multiset` obtained by repeated factorisation and is `noncomputable`.  Over
an enumerable field the set of *distinct* roots is a filter over the enumeration, so it can be a
plain `def`.  Keeping it computable costs nothing and means it can never poison a downstream
definition — the failure mode that motivated this migration.

To be clear about what "computable" buys: nobody *runs* this.  The enumeration has
`scalarFieldOrder` elements, so evaluating it would exhaust memory.  It only ever appears inside
`Prop`s, where the bad-set predicate is decided by a single evaluation instead
(`Zcash.Snark.decidableMemSzBadSet`).  The point is that a `def` mentioning it stays a `def`.

The guard at zero preserves Mathlib's convention that the zero polynomial has no roots, which is
what makes `roots_eq_toFinset` an unconditional equality. -/

open Roots.FiniteField in
/-- The distinct roots of a computable polynomial over an enumerated field. -/
def rootsBy [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] (e : FieldEnumeration R)
    (p : CPolynomial R) : Finset R :=
  if p = 0 then ∅ else (rootsInFieldByEnumeration e p).toList.toFinset

open Roots.FiniteField in
@[simp]
theorem rootsBy_zero [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] (e : FieldEnumeration R) :
    rootsBy e (0 : CPolynomial R) = ∅ := by
  simp [rootsBy]

open Roots.FiniteField in
theorem mem_rootsBy [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] {e : FieldEnumeration R}
    {p : CPolynomial R} {x : R} (hp : p ≠ 0) :
    x ∈ rootsBy e p ↔ p.eval x = 0 := by
  rw [rootsBy, if_neg hp, List.mem_toFinset]
  exact ⟨fun h => rootsInFieldByEnumeration_sound h,
    fun h => rootsInFieldByEnumeration_complete _ h⟩

open Roots.FiniteField in
/-- The bridge to the Mathlib image: the two agree, so every Mathlib root theorem transfers. -/
theorem rootsBy_eq_toFinset [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] (e : FieldEnumeration R)
    (p : CPolynomial R) : rootsBy e p = p.toPoly.roots.toFinset := by
  by_cases hp : p = 0
  · simp [hp]
  · ext x
    rw [mem_rootsBy hp, Multiset.mem_toFinset,
      Polynomial.mem_roots (by rwa [Ne, toPoly_eq_zero_iff]),
      Polynomial.IsRoot.def, ← eval_toPoly]

open Roots.FiniteField in
/-- **Root counting.** A polynomial has at most `natDegree` distinct roots. -/
theorem card_rootsBy_le [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] (e : FieldEnumeration R)
    (p : CPolynomial R) : (rootsBy e p).card ≤ p.natDegree := by
  rw [rootsBy_eq_toFinset, natDegree_toPoly]
  exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)

end CompPoly.CPolynomial
