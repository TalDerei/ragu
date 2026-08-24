import Clean.Circuit
import Ragu.Circuits.Poseidon.Permutation

/-!
# The Poseidon sponge

`poseidon.rs::Sponge` starts from the all-zero state (`Element::zero` per
word), buffers absorbed elements, and on the first `squeeze` adds the buffered
elements into the first `RATE` words (`state[i] = state[i].add(values[i])`,
virtual wires), runs the permutation, and returns `state[0]` (`get_rate`
reverses the rate words and `squeeze` pops the last).

`Hash1` is the single-block shape: `k ≤ RATE` absorbed elements and one
squeezed element, i.e. exactly one permutation.
-/

namespace Ragu.Circuits.Poseidon.Sponge
variable {p : ℕ} [Fact p.Prime] {t : ℕ} [NeZero t]

/-- The permutation's parameters: the MDS matrix and the round schedule. -/
structure Params (F : Type) (t : ℕ) where
  mds : Vector (Vector F t) t
  rounds : List (Permutation.RoundSpec F t)

/-- The schedule `poseidon.rs` runs: `full / 2` full rounds, `part` partial
rounds, `full / 2` full rounds, consuming the round constants in order. -/
def schedule (full part : ℕ) (rcs : Vector (Vector (F p) t) (full + part)) :
    List (Permutation.RoundSpec (F p) t) :=
  (List.finRange (full + part)).map fun i =>
    if i.val < full / 2 ∨ full / 2 + part ≤ i.val then .full rcs[i] else .part rcs[i]

/-- `Sponge::new` followed by absorbing `xs` and entering `squeeze`: the zero
state with `xs[i]` added into word `i`.

This models the Rust sponge only for `k ≤ RATE`. Rust absorbs into the rate
words alone and permutes once the buffer is full, so at `k > RATE` this would
both contaminate the capacity word and skip a permutation. `Hash1.circuit`
carries the corresponding hypothesis. -/
def initialState {k : ℕ} (xs : Vector (Expression (F p)) k) : Vector (Expression (F p)) t :=
  Vector.ofFn fun i => if h : i.val < k then (0 : Expression (F p)) + xs[i.val] else 0

/-- Value-level `initialState`. -/
def initialStateVal {k : ℕ} (xs : Vector (F p) k) : Vector (F p) t :=
  Vector.ofFn fun i => if h : i.val < k then xs[i.val] else 0

-- Building the initial state commutes with evaluation. (A `--` comment, not a
-- docstring: `omit ... in` does not bind through `/-- ... -/`.)
omit [NeZero t] in
theorem eval_initialState (env : Environment (F p)) {k : ℕ} (xs : Vector (Expression (F p)) k) :
    (initialState (t := t) xs).map (Expression.eval env) =
      initialStateVal (xs.map (Expression.eval env)) := by
  ext i hi
  simp only [initialState, initialStateVal, Vector.getElem_map, Vector.getElem_ofFn]
  split <;> simp [Expression.eval]

namespace Hash1

/-- One permutation of the absorbed block, returning its first word. -/
def main (P : Params (F p) t) (k : ℕ) (xs : Var (fields k) (F p)) :
    Circuit (F p) (Expression (F p)) := do
  let state ← Permutation.circuit P.mds P.rounds (initialState xs)
  pure (state[0]'(Nat.pos_of_neZero t))

/-- No precondition on the absorbed values. -/
def Assumptions {k : ℕ} (_xs : Vector (F p) k) := True

/-- The squeezed element is word `0` of the permuted initial state. -/
def Spec (P : Params (F p) t) {k : ℕ} (xs : Vector (F p) k) (out : F p) :=
  out = (Permutation.permuteVal P.mds P.rounds (initialStateVal xs))[0]'(Nat.pos_of_neZero t)

/-- The indexed `main P k` argument determines the Poseidon parameters for
typeclass synthesis. -/
instance elaborated (P : Params (F p) t) (k : ℕ) :
    ElaboratedCircuit (F p) (fields k) field (main P k) where
  localLength _ := Permutation.localLength P.rounds
  output xs offset := (Permutation.output P.mds P.rounds (initialState xs) offset)[0]'(Nat.pos_of_neZero t)
  localLength_eq xs offset := by
    simp [main, circuit_norm, Permutation.circuit]
  output_eq xs offset := by
    simp [main, circuit_norm, Permutation.circuit]
  subcircuitsConsistent xs offset := by
    simp [main, circuit_norm]

/-- The permutation's `Spec` pins the whole output state; the squeezed
element is its first word. -/
theorem soundness (P : Params (F p) t) (k : ℕ) :
    Soundness (F p) (Input := (fields k)) (Output := field) (main P k) Assumptions (Spec P) := by
  circuit_proof_start [Permutation.circuit, Permutation.Assumptions, Permutation.Spec]
  rw [← h_input, ← eval_initialState, ← h_holds]
  simp [Vector.getElem_map]

/-- The permutation is total, so the honest witness exists. -/
theorem completeness (P : Params (F p) t) (k : ℕ) :
    Completeness (F p) (Input := (fields k)) (Output := field) (main P k) Assumptions := by
  circuit_proof_start [Permutation.circuit, Permutation.Assumptions]

/-- `Sponge::new`, `k` absorbs and one squeeze — a single-block hash.

The hypotheses pin the family to the shapes the Rust sponge actually runs,
and are not used by the circuit body:

- `_hk0`: the Rust sponge refuses to squeeze before anything was absorbed
  (`squeeze` returns an initialization error), so `k = 0` models no Rust
  circuit at all.
- `_hkt`: for this sponge family the capacity is the last state word and the
  rate is `t - 1`, so `k < t` is exactly `k ≤ RATE`. Beyond the rate the Rust
  sponge runs a second permutation and never touches the capacity word —
  and past `t`, `initialState` would silently drop inputs — so `k ≥ t`
  models no Rust circuit either.

Absorption is additive from the zero state, so a trailing zero element is
invisible: on `xs.push 0` this circuit computes the same value as on `xs` at
one block size smaller. That is the Rust sponge's documented behavior, not a
defect of the model; protocols must fix the element count. -/
def circuit (P : Params (F p) t) (k : ℕ) (_hk0 : 0 < k) (_hkt : k < t) :
    FormalCircuit (F p) (fields k) field :=
  { main := main P k
    elaborated := elaborated P k
    Assumptions
    Spec := Spec P
    soundness := soundness P k
    completeness := completeness P k }

end Hash1


/-- `Sponge::new`'s state: every word is `Element::zero`. -/
def zeroState : Vector (Expression (F p)) t := Vector.replicate t 0

/-- Absorb one buffered block into an arbitrary state: `state[i] += xs[i]` for
each buffered value, leaving the remaining words — the capacity word in
particular — untouched. This is `permute`'s absorb branch:

```rust
for (state, v) in state.values.iter_mut().zip(values.iter()) {
    *state = state.add(dr, v);
}
values.clear();
*state = dr.routine(Permutation::from(self.params), state.clone())?;
```

`initialState` is this at `zeroState`; the general form is what the second and
later blocks need, since by then the state is whatever the previous
permutation produced. The `zip` is what keeps the capacity word clean: a block
never has more than `RATE` values, so word `t - 1` is never written. -/
def absorbBlock {m : ℕ} (state : Vector (Expression (F p)) t)
    (xs : Vector (Expression (F p)) m) : Vector (Expression (F p)) t :=
  Vector.ofFn fun i => if h : i.val < m then state[i] + xs[i.val] else state[i]

/-- Value-level `absorbBlock`. -/
def absorbBlockVal {m : ℕ} (state : Vector (F p) t) (xs : Vector (F p) m) : Vector (F p) t :=
  Vector.ofFn fun i => if h : i.val < m then state[i] + xs[i.val] else state[i]

-- Absorbing a block commutes with evaluation.
omit [NeZero t] in
theorem eval_absorbBlock (env : Environment (F p)) {m : ℕ}
    (state : Vector (Expression (F p)) t) (xs : Vector (Expression (F p)) m) :
    (absorbBlock state xs).map (Expression.eval env) =
      absorbBlockVal (state.map (Expression.eval env)) (xs.map (Expression.eval env)) := by
  ext i hi
  simp only [absorbBlock, absorbBlockVal, Vector.getElem_map, Vector.getElem_ofFn]
  split <;> simp [Expression.eval]

/-!
## Many blocks

`Hash1` covers the shape where the whole input fits one block. Rust permutes
whenever a block boundary is crossed and once more at `squeeze`, so `k`
absorbed elements at rate `r` run `⌈k / r⌉` permutations over the *same*
state. `Blocks` is that loop, and it returns the full post-permutation state
rather than one word — which is what makes repeated `squeeze` and
`save_state` / `resume` expressible: `get_rate` reverses the rate words and
`squeeze` pops the last, so the `i`-th squeezed element is `state[i]`, and the
state `save_state` hands to `resume` is exactly this vector.
-/
namespace Blocks
variable {rate : ℕ}

/-- Value-level absorb-and-permute loop. -/
def loopVal (P : Params (F p) t) (n : ℕ)
    (blocks : Vector (Vector (F p) rate) n) (state : Vector (F p) t) :
    Vector (F p) t :=
  Fin.foldl n (fun acc i =>
    Permutation.permuteVal P.mds P.rounds (absorbBlockVal acc blocks[i])) state

/-- The absorb-and-permute loop: one boxed `Permutation` per block, threading
the state through. `foldlRange` is used because the symbolic output depends on
the accumulated state and therefore is not `ConstantOutput`. -/
def loop (P : Params (F p) t) (n : ℕ)
    (blocks : Vector (Vector (Expression (F p)) rate) n)
    (state : Var (fields t) (F p)) : Circuit (F p) (Var (fields t) (F p)) :=
  Circuit.foldlRange n state fun acc i =>
    Permutation.circuit P.mds P.rounds (absorbBlock acc blocks[i])

/-- The state wires after the whole loop, threaded block by block. -/
def loopOutput (P : Params (F p) t) (n : ℕ)
    (blocks : Vector (Vector (Expression (F p)) rate) n)
    (state : Var (fields t) (F p)) (offset : ℕ) : Var (fields t) (F p) :=
  Fin.foldl n (fun acc i =>
    Permutation.output P.mds P.rounds (absorbBlock acc blocks[i])
      (offset + i * Permutation.localLength P.rounds)) state

/-- `Sponge::new`, `n` blocks absorbed, then squeeze: the loop started at the
zero state.

The block width is written `w + 1` because Clean derives
`NonEmptyProvableType` — which `ProvableVector` needs — only for
`fields (_ + 1)`. That is no restriction here: a zero-width block would
absorb nothing and Rust never buffers one.

`Blocks` is a sub-gadget reached only through `Squeeze`, so the hypotheses
that pin this family to the shapes the Rust sponge actually runs are carried
by `Squeeze.circuit` rather than here. -/
def main (P : Params (F p) t) (n w : ℕ)
    (blocks : Var (ProvableVector (fields (w + 1)) n) (F p)) :
    Circuit (F p) (Var (fields t) (F p)) :=
  loop P n blocks zeroState

/-- No precondition on the absorbed values. -/
def Assumptions {n w : ℕ} (_blocks : Vector (Vector (F p) (w + 1)) n) := True

/-- The output is the whole sponge state after absorbing every block and
permuting once per block. -/
def Spec (P : Params (F p) t) {n w : ℕ}
    (blocks : Vector (Vector (F p) (w + 1)) n) (out : Vector (F p) t) :=
  out = loopVal P n blocks (Vector.replicate t 0)

/-- The loop allocates one permutation's worth of wires per block. -/
theorem loop_localLength (P : Params (F p) t) (n : ℕ)
    (blocks : Vector (Vector (Expression (F p)) rate) n)
    (state : Var (fields t) (F p)) (offset : ℕ) :
    (loop P n blocks state).localLength offset = n * Permutation.localLength P.rounds := by
  by_cases hn : n = 0
  · simp [loop, circuit_norm, Permutation.circuit, hn]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    simp [loop, circuit_norm, Permutation.circuit, hn_pos]

/-- The loop's output wires are `loopOutput`'s. -/
theorem loop_output (P : Params (F p) t) (n : ℕ)
    (blocks : Vector (Vector (Expression (F p)) rate) n)
    (state : Var (fields t) (F p)) (offset : ℕ) :
    (loop P n blocks state).output offset = loopOutput P n blocks state offset := by
  simp [loop, loopOutput, circuit_norm, Permutation.circuit]

/-- Every sub-permutation sits at the offset assigned by `foldlRange`. -/
theorem loop_consistent (P : Params (F p) t) (n : ℕ)
    (blocks : Vector (Vector (Expression (F p)) rate) n)
    (state : Var (fields t) (F p)) (offset : ℕ) :
    ((loop P n blocks state).operations offset).SubcircuitsConsistent offset := by
  simp [loop, circuit_norm, Permutation.circuit]

/-- One boxed `Permutation` per block, threading the state through. -/
instance elaborated (P : Params (F p) t) (n w : ℕ) :
    ElaboratedCircuit (F p) (ProvableVector (fields (w + 1)) n) (fields t) (main P n w) where
  localLength _ := n * Permutation.localLength P.rounds
  output blocks offset := loopOutput P n blocks zeroState offset
  localLength_eq blocks offset := loop_localLength P n blocks zeroState offset
  output_eq blocks offset := loop_output P n blocks zeroState offset
  subcircuitsConsistent blocks offset := loop_consistent P n blocks zeroState offset
  channelsLawful := by
    simp [main, loop, circuit_norm, Permutation.circuit]

/-- The value-level state after the first `k` of `n` blocks. -/
private def loopValPrefix (P : Params (F p) t) {n : ℕ}
    (blocks : Vector (Vector (F p) rate) n) (state : Vector (F p) t)
    (k : ℕ) (hk : k ≤ n) : Vector (F p) t :=
  Fin.foldl k (fun acc i =>
    Permutation.permuteVal P.mds P.rounds
      (absorbBlockVal acc (blocks[i.val]'(by omega)))) state

/-- The symbolic state after the first `k` of `n` blocks. -/
private def loopOutputPrefix (P : Params (F p) t) {n : ℕ}
    (blocks : Vector (Vector (Expression (F p)) rate) n)
    (state : Var (fields t) (F p)) (offset k : ℕ) (hk : k ≤ n) :
    Var (fields t) (F p) :=
  Fin.foldl k (fun acc i =>
    Permutation.output P.mds P.rounds (absorbBlock acc (blocks[i.val]'(by omega)))
      (offset + i * Permutation.localLength P.rounds)) state

/-- Clean's internal accumulator equals the explicit symbolic prefix. -/
private theorem foldlAcc_eq_loopOutputPrefix (P : Params (F p) t) {n : ℕ}
    (blocks : Vector (Vector (Expression (F p)) rate) n)
    (state : Var (fields t) (F p)) (offset : ℕ) (i : Fin n) :
    Circuit.FoldlM.foldlAcc offset (Vector.finRange n)
      (fun acc j =>
        subcircuit (Permutation.circuit P.mds P.rounds) (absorbBlock acc blocks[j])) state i =
      loopOutputPrefix P blocks state offset i (Nat.le_of_lt i.isLt) := by
  unfold Circuit.FoldlM.foldlAcc loopOutputPrefix
  congr 1
  funext acc j
  simp [circuit_norm, Permutation.circuit]

/-- Extending a symbolic prefix by one applies the next permutation. -/
private theorem loopOutputPrefix_succ (P : Params (F p) t) {n : ℕ}
    (blocks : Vector (Vector (Expression (F p)) rate) n)
    (state : Var (fields t) (F p)) (offset k : ℕ) (hk : k + 1 ≤ n) :
    loopOutputPrefix P blocks state offset (k + 1) hk =
      Permutation.output P.mds P.rounds
        (absorbBlock (loopOutputPrefix P blocks state offset k (by omega)) blocks[k])
        (offset + k * Permutation.localLength P.rounds) := by
  rw [loopOutputPrefix, Fin.foldl_succ_last]
  simp only [Fin.val_last]
  congr

/-- Extending a value-level prefix by one applies the next permutation. -/
private theorem loopValPrefix_succ (P : Params (F p) t) {n : ℕ}
    (blocks : Vector (Vector (F p) rate) n) (state : Vector (F p) t)
    (k : ℕ) (hk : k + 1 ≤ n) :
    loopValPrefix P blocks state (k + 1) hk =
      Permutation.permuteVal P.mds P.rounds
        (absorbBlockVal (loopValPrefix P blocks state k (by omega)) blocks[k]) := by
  rw [loopValPrefix, Fin.foldl_succ_last]
  congr

/-- Every symbolic prefix evaluates to the corresponding value-level prefix. -/
private theorem loop_prefix_soundness (P : Params (F p) t) (env : Environment (F p))
    {n : ℕ} (blocks : Vector (Vector (Expression (F p)) rate) n)
    (state : Var (fields t) (F p)) (offset : ℕ)
    (h_holds : ConstraintsHold.Soundness env
      ((loop P n blocks state).operations offset)) :
    ∀ (k : ℕ) (hk : k ≤ n),
      (loopOutputPrefix P blocks state offset k hk).map (Expression.eval env) =
        loopValPrefix P (blocks.map fun b => b.map (Expression.eval env))
          (state.map (Expression.eval env)) k hk := by
  simp only [loop, ConstraintsHold.Soundness, Circuit.foldlRange.forAllNoOffset] at h_holds
  intro k
  induction k with
  | zero =>
      intro hk
      simp [loopOutputPrefix, loopValPrefix]
  | succ k ih =>
      intro hk
      have hk0 : k ≤ n := by omega
      have hkn : k < n := by omega
      have h_perm := h_holds ⟨k, hkn⟩
      have h_acc := foldlAcc_eq_loopOutputPrefix P blocks state offset ⟨k, hkn⟩
      rw [h_acc] at h_perm
      simp only [circuit_norm, Permutation.circuit, Permutation.Assumptions,
        Permutation.Spec] at h_perm
      rw [loopOutputPrefix_succ P blocks state offset k hk,
        loopValPrefix_succ P _ _ k hk]
      calc
        _ = Permutation.permuteVal P.mds P.rounds
            ((absorbBlock (loopOutputPrefix P blocks state offset k (by omega))
              blocks[k]).map (Expression.eval env)) := h_perm
        _ = Permutation.permuteVal P.mds P.rounds
            (absorbBlockVal
              (loopValPrefix P (blocks.map fun b => b.map (Expression.eval env))
                (state.map (Expression.eval env)) k (by omega))
              (blocks.map fun b => b.map (Expression.eval env))[k]) := by
          rw [eval_absorbBlock, ih hk0]
          congr 2
          all_goals simp [Vector.getElem_map]

/-- Each block's `Permutation` spec composes along `foldlRange`. -/
theorem loop_soundness (P : Params (F p) t) (env : Environment (F p))
    (n : ℕ) (blocks : Vector (Vector (Expression (F p)) rate) n)
    (state : Var (fields t) (F p)) (offset : ℕ)
    (h_holds : ConstraintsHold.Soundness env
      ((loop P n blocks state).operations offset)) :
    (loopOutput P n blocks state offset).map (Expression.eval env) =
        loopVal P n (blocks.map fun b => b.map (Expression.eval env))
          (state.map (Expression.eval env)) ∧
      Operations.Requirements env ((loop P n blocks state).operations offset) := by
  constructor
  · simpa [loopOutput, loopOutputPrefix, loopVal, loopValPrefix] using
      loop_prefix_soundness P env blocks state offset h_holds n (le_refl n)
  · simp [loop, circuit_norm, Permutation.circuit]

/-- Every block permutation is total, so the folded circuit is complete. -/
theorem loop_completeness (P : Params (F p) t) (env : ProverEnvironment (F p))
    (n : ℕ) (blocks : Vector (Vector (Expression (F p)) rate) n)
    (state : Var (fields t) (F p)) (offset : ℕ)
    (_h_env : env.UsesLocalWitnessesCompleteness offset
      ((loop P n blocks state).operations offset)) :
    ConstraintsHold.Completeness env ((loop P n blocks state).operations offset) := by
  simp [loop, circuit_norm, Permutation.circuit, Permutation.Assumptions]

/-- Chaining each block's `Permutation` spec along the loop gives `loopVal`,
started at the zero state `Sponge::new` builds. -/
theorem soundness (P : Params (F p) t) (n w : ℕ) :
    Soundness (F p) (Input := (ProvableVector (fields (w + 1)) n))
      (Output := (fields t)) (main P n w) Assumptions (Spec P) := by
  circuit_proof_start
  obtain ⟨h_loop, h_requirements⟩ := loop_soundness P env n input_var zeroState i₀ h_holds
  constructor
  · rw [h_loop]
    congr 1
    · rw [← h_input]
      ext i hi j hj
      rw [← getElem_eval_vector]
      simp [CircuitType.eval_fields_dispatch, Vector.getElem_map]
    · ext i hi
      simp [zeroState, Expression.eval]
  · exact h_requirements

/-- Every block's permutation is total, so the honest witness exists at each
step and the loop adds no constraints of its own. -/
theorem completeness (P : Params (F p) t) (n w : ℕ) :
    Completeness (F p) (Input := (ProvableVector (fields (w + 1)) n))
      (Output := (fields t)) (main P n w) Assumptions := by
  intro offset env blocks_var h_env blocks _ _
  exact loop_completeness P env n blocks_var zeroState offset h_env

/-- The Poseidon sponge over `n` absorbed blocks, returning the full state. -/
def circuit (P : Params (F p) t) (n w : ℕ) :
    FormalCircuit (F p) (ProvableVector (fields (w + 1)) n) (fields t) :=
  { main := main P n w
    elaborated := elaborated P n w
    requirementsChannelsLawful := by
      simp [main, loop, circuit_norm, Permutation.circuit]
    Assumptions
    Spec := Spec P
    soundness := soundness P n w
    completeness := completeness P n w }

end Blocks


/-!
## Squeezing

`Blocks` returns the whole state. Rust's `squeeze` hands back one element at a
time: `get_rate` takes the rate words, reverses them, and `squeeze` pops the
last, so the `i`-th squeezed element is state word `i`, and taking at most
`RATE` of them triggers no further permutation. `Squeeze` is that projection,
and it is also the shape `save_state` / `resume` operate on — `resume` enters
squeeze mode on exactly this state.
-/
namespace Squeeze
variable {rate : ℕ}

/-- `s` squeezed elements: the first `s` words of the post-permutation state.
`hs` is what makes the projection well-typed; its meaning as the rate bound
is explained on `circuit`. -/
def main (P : Params (F p) t) (n w s : ℕ) (hs : s < t)
    (blocks : Var (ProvableVector (fields (w + 1)) n) (F p)) :
    Circuit (F p) (Var (fields s) (F p)) := do
  let state ← Blocks.circuit P n w blocks
  pure (Vector.ofFn fun i => state[i.val]'(by omega))

/-- No precondition on the absorbed values. -/
def Assumptions {n w : ℕ} (_blocks : Vector (Vector (F p) (w + 1)) n) := True

/-- The squeezed elements are the leading words of the sponge state after
absorbing every block. -/
def Spec (P : Params (F p) t) {n w s : ℕ} (hs : s < t)
    (blocks : Vector (Vector (F p) (w + 1)) n) (out : Vector (F p) s) :=
  out = Vector.ofFn fun i =>
    (Blocks.loopVal P n blocks (Vector.replicate t 0))[i.val]'(by omega)

/-- The projection allocates nothing beyond the block loop. -/
@[reducible] instance elaborated (P : Params (F p) t) (n w s : ℕ) (hs : s < t) :
    ElaboratedCircuit (F p) (ProvableVector (fields (w + 1)) n) (fields s)
      (main P n w s hs) where
  localLength _ := n * Permutation.localLength P.rounds
  output blocks offset :=
    Vector.ofFn fun i => (Blocks.loopOutput P n blocks zeroState offset)[i.val]'(by omega)
  localLength_eq blocks offset := by
    simp [main, circuit_norm, Blocks.circuit]
  output_eq blocks offset := by
    simp [main, circuit_norm, Blocks.circuit]
  subcircuitsConsistent blocks offset := by
    simp [main, circuit_norm]
  channelsLawful := by
    simp [main, circuit_norm, Blocks.circuit]

/-- Immediate from `Blocks`' spec, read at the leading words. -/
theorem soundness (P : Params (F p) t) (n w s : ℕ) (hs : s < t) :
    Soundness (F p) (Input := (ProvableVector (fields (w + 1)) n))
      (Output := (fields s)) (main P n w s hs) Assumptions (Spec P hs) := by
  circuit_proof_start [Blocks.circuit, Blocks.Assumptions, Blocks.Spec]
  ext i hi
  have h := congrArg (fun v : Vector (F p) t => v[i]'(by omega)) h_holds
  simpa [Vector.getElem_map] using h

/-- `Blocks` is total, so the honest witness exists. -/
theorem completeness (P : Params (F p) t) (n w s : ℕ) (hs : s < t) :
    Completeness (F p) (Input := (ProvableVector (fields (w + 1)) n))
      (Output := (fields s)) (main P n w s hs) Assumptions := by
  circuit_proof_start [Blocks.circuit, Blocks.Assumptions]

/-- `Sponge::new`, `n` blocks of `w + 1` elements, `s` squeezes.

The unused hypotheses pin the family to the shapes the Rust sponge actually
runs; `hs` is additionally what bounds the projection.

- `_hn`: the Rust sponge refuses to squeeze before anything was absorbed
  (`squeeze` returns an initialization error), so `n = 0` models no Rust
  circuit.
- `_hw`: a block never holds more than `RATE` values, and for this family
  `RATE = t - 1`, so `w + 1 < t` is `w + 1 ≤ RATE`. A wider block would write
  the capacity word, or drop inputs in `absorbBlock`.
- `_hs0`: the final permutation is run by the first `squeeze`. With no
  squeeze the last block stays buffered and unpermuted, so `s = 0` would
  model one permutation fewer than this loop runs.
- `hs`: `s < t` is `s ≤ RATE`; the `t`-th squeeze would exhaust the rate
  words and permute again, which this projection does not model.

Which Rust program a given width models depends on the width. At
`w + 1 = RATE` it is a run of plain `absorb`s: Rust packs the buffer to
`RATE` and permutes when the next element arrives, so `n` full blocks are
`n · RATE` consecutive absorbs. At `w + 1 < RATE` it is the interleaved
program `absorb^(w+1); squeeze; absorb^(w+1); squeeze; …` — a squeeze
permutes whatever was absorbed since the last one, and a later `absorb`
continues from that permuted state (`absorb` in squeeze mode re-enters
absorb mode on the same state). Any number of squeezes between two batches,
up to `RATE`, leaves the state alone. Only the final batch's squeezes are
output here; each intermediate squeeze is word `0` of the state a shorter
instance of this same circuit produces.

Not modeled: a ragged last block under plain absorption — `k` consecutive
absorbs with `k` not a multiple of `RATE`. That shape is `Ragged`. -/
def circuit (P : Params (F p) t) (n w s : ℕ) (_hn : 0 < n) (_hw : w + 1 < t)
    (_hs0 : 0 < s) (hs : s < t) :
    FormalCircuit (F p) (ProvableVector (fields (w + 1)) n) (fields s) :=
  { main := main P n w s hs
    elaborated := elaborated P n w s hs
    requirementsChannelsLawful := by
      simp [main, circuit_norm, Blocks.circuit]
    Assumptions
    Spec := Spec P hs
    soundness := soundness P n w s hs
    completeness := completeness P n w s hs }

end Squeeze


/-!
## A ragged last block

`k` consecutive absorbs with `k` not a multiple of `RATE` leave Rust with
`⌊k / RATE⌋` full blocks and a shorter final one. `Ragged` is that shape:
the `Blocks` loop over the full blocks, then one more absorb-and-permute of
the short tail, then the squeeze projection. Its input is a pair rather than
a named structure because the `ProvableStruct` deriver does not accept a
`Vector (fields (w + 1) F) n` field at a parameter `w`.
-/
namespace Ragged

/-- The full blocks, then the tail. -/
abbrev Input (n w k : ℕ) : TypeMap :=
  ProvablePair (ProvableVector (fields (w + 1)) n) (fields (k + 1))

/-- `Blocks` over the full blocks, one more permutation over the tail, then
the leading words. -/
def main (P : Params (F p) t) (n w k s : ℕ) (hs : s < t)
    (input : Var (Input n w k) (F p)) : Circuit (F p) (Var (fields s) (F p)) := do
  let state ← Blocks.circuit P n w input.1
  let state ← Permutation.circuit P.mds P.rounds (absorbBlock state input.2)
  pure (Vector.ofFn fun i => state[i.val]'(by omega))

/-- No precondition on the absorbed values. -/
def Assumptions {n w k : ℕ} (_input : Input n w k (F p)) := True

/-- Value-level: the tail absorbed into the state the full blocks produce,
permuted once more. -/
def stateVal (P : Params (F p) t) {n w k : ℕ} (input : Input n w k (F p)) : Vector (F p) t :=
  Permutation.permuteVal P.mds P.rounds
    (absorbBlockVal (Blocks.loopVal P n input.1 (Vector.replicate t 0)) input.2)

/-- The squeezed elements are the leading words of the final state. -/
def Spec (P : Params (F p) t) {n w k s : ℕ} (hs : s < t)
    (input : Input n w k (F p)) (out : Vector (F p) s) :=
  out = Vector.ofFn fun i => (stateVal P input)[i.val]'(by omega)

/-- The full-block loop plus one permutation. -/
@[reducible] instance elaborated (P : Params (F p) t) (n w k s : ℕ) (hs : s < t) :
    ElaboratedCircuit (F p) (Input n w k) (fields s) (main P n w k s hs) where
  localLength _ := n * Permutation.localLength P.rounds + Permutation.localLength P.rounds
  output input offset :=
    Vector.ofFn fun i =>
      (Permutation.output P.mds P.rounds
        (absorbBlock (Blocks.loopOutput P n input.1 zeroState offset) input.2)
        (offset + n * Permutation.localLength P.rounds))[i.val]'(by omega)
  localLength_eq input offset := by
    simp [main, circuit_norm, Blocks.circuit, Permutation.circuit]
  output_eq input offset := by
    simp [main, circuit_norm, Blocks.circuit, Permutation.circuit]
  subcircuitsConsistent input offset := by
    simp [main, circuit_norm]
    omega
  channelsLawful := by
    simp [main, circuit_norm, Blocks.circuit, Permutation.circuit]

/-- `Blocks`' spec pins the state after the full blocks, the permutation's
spec pins it after the tail, and the projection reads the leading words. -/
theorem soundness (P : Params (F p) t) (n w k s : ℕ) (hs : s < t) :
    Soundness (F p) (Input := (Input n w k)) (Output := (fields s))
      (main P n w k s hs) Assumptions (Spec P hs) := by
  circuit_proof_start [Blocks.circuit, Blocks.Assumptions, Blocks.Spec,
    Permutation.circuit, Permutation.Assumptions, Permutation.Spec]
  obtain ⟨h_blocks, h_perm⟩ := h_holds
  rw [← h_input]
  ext i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn]
  have h := congrArg (fun v : Vector (F p) t => v[i]'(by omega)) h_perm
  simp only [Vector.getElem_map] at h
  rw [h, stateVal, eval_absorbBlock, h_blocks]

/-- Both sub-gadgets are total, so the honest witness exists. -/
theorem completeness (P : Params (F p) t) (n w k s : ℕ) (hs : s < t) :
    Completeness (F p) (Input := (Input n w k)) (Output := (fields s))
      (main P n w k s hs) Assumptions := by
  circuit_proof_start [Blocks.circuit, Blocks.Assumptions,
    Permutation.circuit, Permutation.Assumptions]

/-- `Sponge::new`, `n · (w + 1) + (k + 1)` consecutive absorbs, `s` squeezes.

The unused hypotheses pin the family to the shapes the Rust sponge actually
runs; `hs` is additionally what bounds the projection.

- `_hw`: under consecutive absorption a block boundary is crossed only when
  the buffer holds exactly `RATE = t - 1` values, so every full block is
  `RATE` wide: `w + 2 = t`.
- `_hk`: the tail holds at most `RATE` values: `k + 1 < t`. (A tail of
  exactly `RATE` is not ragged — that shape is `Squeeze`.)
- `_hs0`, `hs`: as for `Squeeze.circuit` — the first squeeze runs the final
  permutation, and the `t`-th would run another. -/
def circuit (P : Params (F p) t) (n w k s : ℕ) (_hw : w + 2 = t) (_hk : k + 1 < t)
    (_hs0 : 0 < s) (hs : s < t) :
    FormalCircuit (F p) (Input n w k) (fields s) :=
  { main := main P n w k s hs
    elaborated := elaborated P n w k s hs
    requirementsChannelsLawful := by
      simp [main, circuit_norm, Blocks.circuit, Permutation.circuit]
    Assumptions
    Spec := Spec P hs
    soundness := soundness P n w k s hs
    completeness := completeness P n w k s hs }

end Ragged

end Ragu.Circuits.Poseidon.Sponge
