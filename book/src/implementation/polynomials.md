# Polynomial Management

Ragu's prover works primarily with polynomials: constructing them from
circuit descriptions, multiplying them via FFTs, and decomposing their
products into forms the verifier can check. This chapter covers the
wiring polynomial that encodes an arithmetic circuit, the synthesis
process that builds it incrementally, and the low-level polynomial
utilities in [`ragu_arithmetic`] that support these operations.

## Wiring Polynomials

Individual arithmetic circuits are defined by the
[structured vector](../protocol/prelim/structured_vectors.md)
$\v{s} \in \F^{4n}$ that describes the
[constraints](../protocol/core/arithmetization.md#constraints)
enforced over the witness, given a concrete choice of random challenge $y$.
This vector is the coefficient vector of a special polynomial

$$
s(X, Y) = \sum\limits_{j=0}^{4n - 1} Y^j \Big(
      \sum_{i = 0}^{n - 1} (\v{u})_{j,i} X^{2n - 1 - i}
    + \sum_{i = 0}^{n - 1} (\v{v})_{j,i} X^{2n + i}
    + \sum_{i = 0}^{n - 1} (\v{w})_{j,i} X^{4n - 1 - i}
    + \sum_{i = 0}^{n - 1} (\v{d})_{j,i} X^{i}
\Big)
$$

at the restriction $Y = y$. This is known as the "wiring polynomial."

## Synthesis {#synthesis}

Ragu will directly synthesize circuit code into (partial) evaluations of
the reduced wiring polynomial. There are two operations that influence this
polynomial:

* `enforce_zero` creates a
  [constraint](../protocol/core/arithmetization.md#constraints)
  that enforces that a linear combination of wires must equal zero. This
  produces a new term in $Y^j$ for some unused $j$.
* `mul` creates new wires $(a, b, c)$ that must satisfy a
  [gate]
  $ab = c$. This allocates (or assigns) the corresponding powers
  $(X^{2n + i}, X^{2n - 1 - i}, X^{4n - 1 - i})$ for some unused $i$.

**Importantly, this synthesis process is procedural.** Any contiguous
sequence of `enforce_zero` and `mul` operations is defined by the
polynomials $g, h \in \F[X, Y]$ and transforms $s(X, Y)$ into $s'(X, Y)$
where for some $i, j$

$$
s'(X, Y) = s(X, Y) + Y^j (X^i g(X, Y) + h(X, Y)).
$$

Here, only $h(X, Y)$ varies depending on wires not allocated within that
sequence of operations. In many cases, $h$ is either extremely sparse (and
so trivial to compute as necessary) or is used in multiple repeated
sequences. Any repeated sequence produces the same $g$ polynomial by
definition, and so its evaluation can be fully memoized for future
invocations of an identical sequence of operations by simply scaling by
$X^i Y^j$.

[gate]: ../protocol/core/arithmetization.md#gates

## Polynomial Arithmetic

The synthesis machinery above relies on standard polynomial operations
provided by the [`ragu_arithmetic`] crate. These operate on coefficient
vectors in ascending
degree order: the slice $[c_0, c_1, \ldots, c_n]$ represents the
polynomial
$c_0 + c_1 X + \cdots + c_n X^n$.

### Evaluation and Inner Products

[`eval`] evaluates a polynomial at a point using Horner's method.
[`dot`] computes the inner product $\langle \v{a}, \v{b} \rangle$ of
two equal-length coefficient vectors. These helpers provide the scalar
operations underlying polynomial evaluation and inner-product checks.

### Polynomial Multiplication

[`poly_mul`] computes the coefficient convolution of two polynomials,
implemented using FFTs. Given polynomials $a(X)$ of degree $d_a$ and
$b(X)$ of degree $d_b$, it produces $c(X) = a(X) \cdot b(X)$ of degree
$d_a + d_b$. Internally, both inputs are zero-padded to a power-of-two
length, transformed into evaluation form via [`Domain::fft`], multiplied
pointwise, and transformed back via [`Domain::ifft`].

The output is written into a caller-supplied `&mut Vec<F>` so that
repeated multiplications can reuse a single allocation.

### Decomposition

The [NARK protocol](../protocol/core/nark.md#the-decomposition-trick)
reduces a revdot claim $\revdot{\v{a}}{\v{b}} = c$ to polynomial
evaluation queries by decomposing the product $a(X) \cdot b(X)$. The
[structured vectors chapter](../protocol/prelim/structured_vectors.md#reduction-to-polynomial-queries)
gives the general construction: for equal-length vectors
$\v{a}, \v{b} \in \F^n$, the product polynomial
$c(X) = a(X) \cdot b(X)$ of degree $2n - 2$ can be written as

$$
c(X) = X^{n-1}\, p(X^{-1}) + X^n\, q(X)
$$

where $p$ is formed by reversing the lower $n$ coefficients of $c$ and
$q$ collects the upper $n - 1$ coefficients. The key property is that
$p(0) = c_{n-1} = \revdot{\v{a}}{\v{b}}$, turning a coefficient
extraction into a constant-term query.

[`decomp_product_poly`] implements this step. It calls [`poly_mul`] to
obtain $c$, splits off the upper half as $q$, and reverses the lower
half in place to form $p$. The returned pair $(p, q)$ has lengths $n$
and $n - 1$ respectively (for $n \geq 1$; empty inputs return two
empty vectors).

### Root Polynomials

[`poly_with_roots`] constructs the monic polynomial
$\prod_{i} (X - r_i)$ from a list of roots, using a pairwise tree of
FFT-based multiplications. This is useful for constructing vanishing
polynomials over explicit root sets.

Together, these primitives support the prover's polynomial workflow:
the wiring polynomial is synthesized incrementally from circuit
operations, and products are multiplied and decomposed to reduce
revdot claims to polynomial queries.

[`ragu_arithmetic`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/
[`eval`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/fn.eval.html
[`dot`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/fn.dot.html
[`poly_mul`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/fn.poly_mul.html
[`decomp_product_poly`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/fn.decomp_product_poly.html
[`poly_with_roots`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/fn.poly_with_roots.html
[`Domain::fft`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/struct.Domain.html#method.fft
[`Domain::ifft`]: https://docs.rs/ragu_arithmetic/latest/ragu_arithmetic/struct.Domain.html#method.ifft
