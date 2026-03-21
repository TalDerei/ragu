//! Sparse polynomial representation with block-compressed coefficient storage.
//!
//! Circuits produced by the alloc optimization have wire assignments where the
//! `b` and `c` wires are zero for most alloc gates and the `d` wire is zero
//! for most multiplication gates. A dense coefficient vector would store those
//! zeros explicitly, wasting memory and commitment bandwidth. This module
//! stores only the non-zero runs, keeping the zero gaps implicit.
//!
//! [`Polynomial<T, R>`] stores a degree $4n - 1$ polynomial (where $4n$ =
//! `R::num_coeffs()`) as sorted, non-overlapping blocks of contiguous
//! coefficients. Gaps between blocks are implicitly zero.
//!
//! # Construction
//!
//! There are three ways to create a polynomial:
//!
//! - [`Polynomial::new`]: empty (zero) polynomial.
//! - [`Polynomial::from_coeffs`]: compress a dense coefficient vector.
//! - [`view::View`]: a builder with four dense wire buffers (a, b, c, d) that
//!   maps gate-indexed values to degree positions and produces a polynomial via
//!   [`View::build`](view::View::build).
//!
//! Once constructed, the polynomial supports algebraic operations ([`scale`],
//! [`add_assign`], [`eval`], [`revdot`], [`dilate`], [`commit`], etc.) but
//! cannot be converted back to a view. Construction and mutation are separate
//! phases.
//!
//! [`scale`]: Polynomial::scale
//! [`add_assign`]: Polynomial::add_assign
//! [`eval`]: Polynomial::eval
//! [`revdot`]: Polynomial::revdot
//! [`dilate`]: Polynomial::dilate
//! [`commit`]: Polynomial::commit

pub mod view;

#[cfg(test)]
mod tests;

use alloc::vec::Vec;
use core::borrow::Borrow;
use core::marker::PhantomData;

use ff::Field;
use ragu_arithmetic::CurveAffine;
use rand::CryptoRng;

use super::Rank;

/// A sparse polynomial with coefficients stored as non-overlapping blocks.
///
/// See the [module documentation](self) for details.
#[derive(Clone, Debug)]
pub struct Polynomial<T, R: Rank> {
    /// Sorted, non-overlapping, non-empty blocks of `(start_index, values)`.
    blocks: Vec<(usize, Vec<T>)>,
    _marker: PhantomData<R>,
}

// ---------------------------------------------------------------------------
// Invariant checking
// ---------------------------------------------------------------------------

impl<T, R: Rank> Polynomial<T, R> {
    fn check_invariants(&self) {
        let mut prev_end: usize = 0;
        for (i, (start, data)) in self.blocks.iter().enumerate() {
            assert!(!data.is_empty(), "block {i} is empty");
            assert!(
                *start + data.len() <= R::num_coeffs(),
                "block {i} exceeds capacity"
            );
            if i > 0 {
                assert!(
                    *start > prev_end,
                    "block {i} overlaps or is adjacent to previous (start={start}, prev_end={prev_end})"
                );
            }
            prev_end = *start + data.len();
        }
    }

    /// Creates a polynomial from pre-built blocks. The caller must ensure
    /// blocks are sorted, non-overlapping, non-adjacent, non-empty, and within
    /// capacity.
    pub(super) fn from_blocks(blocks: Vec<(usize, Vec<T>)>) -> Self {
        let poly = Self {
            blocks,
            _marker: PhantomData,
        };
        poly.check_invariants();
        poly
    }
}

// ---------------------------------------------------------------------------
// Construction
// ---------------------------------------------------------------------------

impl<T, R: Rank> Default for Polynomial<T, R> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, R: Rank> Polynomial<T, R> {
    /// Creates a new empty (zero) polynomial.
    pub fn new() -> Self {
        Self {
            blocks: Vec::new(),
            _marker: PhantomData,
        }
    }

    /// Compresses a dense coefficient vector into sparse block form.
    ///
    /// The `is_zero` predicate identifies zero elements that can be omitted.
    /// Panics if `coeffs.len()` exceeds `R::num_coeffs()`.
    pub fn from_coeffs(coeffs: Vec<T>, is_zero: impl Fn(&T) -> bool) -> Self {
        assert!(
            coeffs.len() <= R::num_coeffs(),
            "coefficient vector length {} exceeds capacity {}",
            coeffs.len(),
            R::num_coeffs()
        );

        let mut blocks = Vec::new();
        let mut block_start = None;
        let mut current_block = Vec::new();

        for (i, coeff) in coeffs.into_iter().enumerate() {
            if is_zero(&coeff) {
                if !current_block.is_empty() {
                    blocks.push((block_start.unwrap(), current_block));
                    current_block = Vec::new();
                    block_start = None;
                }
            } else {
                if block_start.is_none() {
                    block_start = Some(i);
                }
                current_block.push(coeff);
            }
        }

        if !current_block.is_empty() {
            blocks.push((block_start.unwrap(), current_block));
        }

        let poly = Self {
            blocks,
            _marker: PhantomData,
        };
        poly.check_invariants();
        poly
    }
}

impl<F: Field, R: Rank> Polynomial<F, R> {
    /// Creates a polynomial with random coefficients filling all `4n` slots.
    pub fn random<RNG: CryptoRng>(rng: &mut RNG) -> Self {
        let coeffs: Vec<F> = (0..R::num_coeffs()).map(|_| F::random(&mut *rng)).collect();
        Self {
            blocks: alloc::vec![(0, coeffs)],
            _marker: PhantomData,
        }
    }
}

// ---------------------------------------------------------------------------
// Block storage operations (generic, no field bounds)
// ---------------------------------------------------------------------------

impl<T, R: Rank> Polynomial<T, R> {
    /// Returns `true` if no coefficients are stored.
    ///
    /// For polynomials over a field, this is equivalent to the polynomial
    /// being zero, provided arithmetic operations prune zero results.
    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    /// Returns a reference to the block list.
    pub fn blocks(&self) -> &[(usize, Vec<T>)] {
        &self.blocks
    }

    /// Total number of stored (non-zero) coefficients.
    pub fn num_nonzero(&self) -> usize {
        self.blocks.iter().map(|(_, data)| data.len()).sum()
    }

    /// Looks up the coefficient at `index`, returning `None` if it falls in a
    /// gap (implicitly zero).
    pub fn get(&self, index: usize) -> Option<&T> {
        let pos = self
            .blocks
            .binary_search_by(|(start, data)| {
                if index < *start {
                    core::cmp::Ordering::Greater
                } else if index >= *start + data.len() {
                    core::cmp::Ordering::Less
                } else {
                    core::cmp::Ordering::Equal
                }
            })
            .ok()?;
        let (start, data) = &self.blocks[pos];
        Some(&data[index - start])
    }

    /// Iterates over all stored `(degree_index, &value)` pairs.
    pub fn iter_nonzero(&self) -> impl Iterator<Item = (usize, &T)> {
        self.blocks
            .iter()
            .flat_map(|(start, data)| data.iter().enumerate().map(move |(i, v)| (start + i, v)))
    }

    /// Iterates mutably over all stored `(degree_index, &mut value)` pairs.
    pub fn iter_nonzero_mut(&mut self) -> impl Iterator<Item = (usize, &mut T)> {
        self.blocks.iter_mut().flat_map(|(start, data)| {
            let s = *start;
            data.iter_mut().enumerate().map(move |(i, v)| (s + i, v))
        })
    }

    /// Applies a closure to every stored element.
    pub fn apply_all(&mut self, mut op: impl FnMut(&mut T)) {
        for (_, data) in &mut self.blocks {
            for elem in data.iter_mut() {
                op(elem);
            }
        }
    }
}

impl<T: Clone, R: Rank> Polynomial<T, R> {
    /// Gets or creates a slot at `index`, returning a mutable reference.
    ///
    /// If the index falls in a gap, extends an adjacent block or creates a new
    /// single-element block initialized with the provided `zero` value.
    pub fn ensure_index(&mut self, index: usize, zero: T) -> &mut T {
        assert!(
            index < R::num_coeffs(),
            "index {index} out of bounds for capacity {}",
            R::num_coeffs()
        );

        // Find the insertion point: first block whose start > index.
        let pos = self.blocks.partition_point(|(start, _)| *start <= index);

        // Determine the action without holding borrows across mutation.
        enum Action {
            InsideBlock { block: usize, offset: usize },
            ExtendPrev { block: usize, merge_next: bool },
            StartOfNext { block: usize },
            PrependNext { block: usize },
            NewBlock { pos: usize },
        }

        let action = if pos > 0 {
            let (start, data_len) = (self.blocks[pos - 1].0, self.blocks[pos - 1].1.len());
            let end = start + data_len;
            if index < end {
                Action::InsideBlock {
                    block: pos - 1,
                    offset: index - start,
                }
            } else if index == end {
                let merge_next = pos < self.blocks.len() && self.blocks[pos].0 == index + 1;
                Action::ExtendPrev {
                    block: pos - 1,
                    merge_next,
                }
            } else if pos < self.blocks.len() && self.blocks[pos].0 == index {
                Action::StartOfNext { block: pos }
            } else if pos < self.blocks.len() && self.blocks[pos].0 == index + 1 {
                Action::PrependNext { block: pos }
            } else {
                Action::NewBlock { pos }
            }
        } else if pos < self.blocks.len() && self.blocks[pos].0 == index {
            Action::StartOfNext { block: pos }
        } else if pos < self.blocks.len() && self.blocks[pos].0 == index + 1 {
            Action::PrependNext { block: pos }
        } else {
            Action::NewBlock { pos }
        };

        let (blk, off) = match action {
            Action::InsideBlock { block, offset } => (block, offset),
            Action::ExtendPrev { block, merge_next } => {
                self.blocks[block].1.push(zero);
                let new_offset = self.blocks[block].1.len() - 1;
                if merge_next {
                    let (_, next_data) = self.blocks.remove(block + 1);
                    self.blocks[block].1.extend(next_data);
                }
                (block, new_offset)
            }
            Action::StartOfNext { block } => (block, 0),
            Action::PrependNext { block } => {
                self.blocks[block].0 = index;
                self.blocks[block].1.insert(0, zero);
                (block, 0)
            }
            Action::NewBlock { pos } => {
                self.blocks.insert(pos, (index, alloc::vec![zero]));
                (pos, 0)
            }
        };

        self.check_invariants();
        &mut self.blocks[blk].1[off]
    }

    /// Merges another polynomial into this one using the given binary operation.
    ///
    /// For positions present in both: applies `op(&mut self_elem, &other_elem)`.
    /// For positions only in `other`: clones `default`, applies `op`, and stores
    /// the result.
    /// For positions only in `self`: kept as-is.
    ///
    /// The `is_zero` predicate filters out zero-valued results during the
    /// rebuild, preserving the sparsity invariant.
    pub fn combine_assign(
        &mut self,
        other: &Self,
        default: T,
        mut op: impl FnMut(&mut T, &T),
        is_zero: impl Fn(&T) -> bool,
    ) {
        // Dense scratch approach: allocate a slot for every coefficient
        // position, fill from self and other, then compress back to blocks.
        // O(capacity) time and space, O(nnz) non-trivial work.

        let capacity = R::num_coeffs();

        let mut dense = alloc::vec![Option::<T>::None; capacity];

        // Fill from self.
        for (start, data) in &self.blocks {
            for (i, val) in data.iter().enumerate() {
                dense[start + i] = Some(val.clone());
            }
        }

        // Merge from other.
        for (start, data) in &other.blocks {
            for (i, val) in data.iter().enumerate() {
                let idx = start + i;
                match &mut dense[idx] {
                    Some(existing) => op(existing, val),
                    slot @ None => {
                        let mut z = default.clone();
                        op(&mut z, val);
                        *slot = Some(z);
                    }
                }
            }
        }

        // Rebuild blocks from the dense array, skipping zeros.
        let mut blocks: Vec<(usize, Vec<T>)> = Vec::new();
        let mut current_block: Option<(usize, Vec<T>)> = None;

        for (i, slot) in dense.into_iter().enumerate() {
            let keep = match &slot {
                Some(val) => !is_zero(val),
                None => false,
            };
            if keep {
                let val = slot.unwrap();
                if let Some((_, ref mut data)) = current_block {
                    data.push(val);
                } else {
                    current_block = Some((i, alloc::vec![val]));
                }
            } else if let Some(block) = current_block.take() {
                blocks.push(block);
            }
        }
        if let Some(block) = current_block {
            blocks.push(block);
        }

        self.blocks = blocks;
        self.check_invariants();
    }
}

impl<T: Clone + Default, R: Rank> Polynomial<T, R> {
    /// Iterates over all `R::num_coeffs()` coefficients in degree order,
    /// yielding `T::default()` for positions not in any block.
    pub fn iter_coeffs(&self) -> impl DoubleEndedIterator<Item = T> + ExactSizeIterator {
        let mut dense = alloc::vec![T::default(); R::num_coeffs()];
        for (start, data) in &self.blocks {
            dense[*start..*start + data.len()].clone_from_slice(data);
        }
        dense.into_iter()
    }

    /// Expands to a dense coefficient vector of length `R::num_coeffs()`.
    pub fn to_dense(&self) -> Vec<T> {
        self.iter_coeffs().collect()
    }
}

// ---------------------------------------------------------------------------
// Polynomial operations (require F: Field)
// ---------------------------------------------------------------------------

impl<F: Field, R: Rank> Polynomial<F, R> {
    /// Multiplies all coefficients by `by`.
    pub fn scale(&mut self, by: F) {
        self.apply_all(|x| *x *= by);
    }

    /// Adds the coefficients of `other` to `self`.
    pub fn add_assign(&mut self, other: &Self) {
        self.combine_assign(other, F::ZERO, |a, b| *a += *b, |x| bool::from(x.is_zero()));
    }

    /// Subtracts the coefficients of `other` from `self`.
    pub fn sub_assign(&mut self, other: &Self) {
        self.combine_assign(other, F::ZERO, |a, b| *a -= *b, |x| bool::from(x.is_zero()));
    }

    /// Negates all coefficients.
    pub fn negate(&mut self) {
        self.apply_all(|x| *x = -*x);
    }

    /// Horner-style weighted sum of polynomials by powers of `scale_factor`.
    pub fn fold<E: Borrow<Self>>(polys: impl IntoIterator<Item = E>, scale_factor: F) -> Self {
        polys.into_iter().fold(Self::default(), |mut acc, poly| {
            acc.scale(scale_factor);
            acc.add_assign(poly.borrow());
            acc
        })
    }

    /// Sets the degree-0 coefficient to `value`.
    pub fn set_constant_term(&mut self, value: F) {
        *self.ensure_index(0, F::ZERO) = value;
    }

    /// Evaluates this polynomial at `z`.
    pub fn eval(&self, z: F) -> F {
        let mut result = F::ZERO;
        for (start, data) in &self.blocks {
            let mut power = z.pow_vartime([u64::try_from(*start).unwrap()]);
            for coeff in data {
                result += *coeff * power;
                power *= z;
            }
        }
        result
    }

    /// Transforms `p(X)` into `p(zX)` by multiplying each coefficient at
    /// degree `k` by `z^k`.
    pub fn dilate(&mut self, z: F) {
        for (start, data) in &mut self.blocks {
            let mut power = z.pow_vartime([u64::try_from(*start).unwrap()]);
            for coeff in data.iter_mut() {
                *coeff *= power;
                power *= z;
            }
        }
    }

    /// Inner product of `self` with the coefficient-reversed `other`.
    ///
    /// Computes $\sum_k \text{self}\[k\] \cdot \text{other}\[4n - 1 - k\]$.
    ///
    /// Accumulates per-block partial sums for instruction-level parallelism.
    pub fn revdot(&self, other: &Self) -> F {
        let max_deg = R::num_coeffs() - 1;
        self.blocks
            .iter()
            .map(|(start, data)| {
                data.iter().enumerate().fold(F::ZERO, |acc, (i, coeff)| {
                    match other.get(max_deg - (start + i)) {
                        Some(other_coeff) => acc + *coeff * *other_coeff,
                        None => acc,
                    }
                })
            })
            .fold(F::ZERO, |a, b| a + b)
    }

    /// Computes a commitment in projective form.
    pub fn commit<C: CurveAffine<ScalarExt = F>>(
        &self,
        generators: &impl ragu_arithmetic::FixedGenerators<C>,
        blind: F,
    ) -> C::Curve {
        assert!(generators.g().len() >= R::num_coeffs());

        let g = generators.g();
        let entries: Vec<_> = self.iter_nonzero().collect();

        ragu_arithmetic::mul(
            entries
                .iter()
                .map(|(_, c)| *c)
                .chain(core::iter::once(&blind)),
            entries
                .iter()
                .map(|(i, _)| &g[*i])
                .chain(core::iter::once(generators.h())),
        )
    }

    /// Computes a commitment normalized to affine.
    pub fn commit_to_affine<C: CurveAffine<ScalarExt = F>>(
        &self,
        generators: &impl ragu_arithmetic::FixedGenerators<C>,
        blind: F,
    ) -> C {
        self.commit(generators, blind).into()
    }
}

// ---------------------------------------------------------------------------
// Trait impls
// ---------------------------------------------------------------------------

impl<F: Field, R: Rank> PartialEq for Polynomial<F, R> {
    fn eq(&self, other: &Self) -> bool {
        self.to_dense() == other.to_dense()
    }
}

impl<F: Field, R: Rank> Eq for Polynomial<F, R> {}

impl<F: Field, R: Rank> ragu_arithmetic::Ring for Polynomial<F, R> {
    type R = Self;
    type F = F;

    fn scale_assign(r: &mut Self, by: F) {
        r.scale(by);
    }
    fn add_assign(r: &mut Self, other: &Self) {
        Polynomial::add_assign(r, other);
    }
    fn sub_assign(r: &mut Self, other: &Self) {
        Polynomial::sub_assign(r, other);
    }
}
