# Overview

Ragu's arithmetic circuits over $\F$ consist of $n$ **gates** on four wires
$\v{a}_i, \v{b}_i, \v{c}_i, \v{d}_i \in \F$, with each gate enforcing both
$\v{a}_i \v{b}_i = \v{c}_i$ and $\v{c}_i \v{d}_i = 0$.[^whydwires]
In addition, there are $4n$ **constraints**, each requiring a fixed linear form
on all the wires to equal an **instance** value (either zero, or a **public
input**).[^why4n] A valid **witness** determines an assignment of field values
to every wire that satisfies all constraints; this assignment is also called the
**trace** of execution.

The protocol allows a prover to convince a verifier that the prover knows a
satisfying trace given a some instance.[^soundness-scope] The trace $\v{a},
\v{b}, \v{c}, \v{d} \in \F^n$ is encoded as a **trace polynomial** $r(X)$,
represented in the $4n$-dimensional space of **structured polynomials**.

```admonish info title="Structured polynomials"
A structured polynomial $p(X)$, of degree $< 4n$, is specified by four vectors
$\v{a}, \v{b}, \v{c}, \v{d} \in \F^n$:

$$
p(X) = \sum_{i=0}^{n-1} \left(
  \v{c}_i\, X^{i} +
  \v{b}_i\, X^{2n-1-i} +
  \v{a}_i\, X^{2n+i} +
  \v{d}_i\, X^{4n-1-i}
\right)
$$

Reading the $4n$ coefficients from lowest to highest degree, the coefficient
vector is the concatenation $\v{c} \| \rv{b} \| \v{a} \| \rv{d}$, where
$\rv{x}$ denotes the reversal of $\v{x} \in \F^n$. Reversing the full
coefficient vector yields another structured polynomial with
$\v{a} \leftrightarrow \v{b}$ and $\v{c} \leftrightarrow \v{d}$ swapped —
structured polynomials are closed under reversal of their coefficients.

The **revdot product** $\revdot{\v{p}}{\v{q}} = \dot{\v{p}}{\rv{q}}$ is the
dot product of one structured polynomial with the reversal of another:

$$
\revdot{\v{p}}{\v{q}} = \dot{\v{a}_p}{\v{b}_q} + \dot{\v{b}_p}{\v{a}_q}
  + \dot{\v{c}_p}{\v{d}_q} + \dot{\v{d}_p}{\v{c}_q}
$$

The reversal closure swaps $\v{a} \leftrightarrow \v{b}$ and
$\v{c} \leftrightarrow \v{d}$, so revdot naturally cross-multiplies these
pairs.
```

The trace polynomial $r(X)$ is a structured polynomial whose coefficient vector
is of this precise form, i.e. $\v{r} = \v{c} \| \rv{b} \| \v{a} \| \rv{d}$. When
we revdot between the trace $r(X)$ and its dilation $r(zX)$
for a verifier challenge $z \in \F$, it expands into two weighted sums:

$$
\revdot{\v{r}}{\v{r} \circ \v{z^{4n}}}
= \sum_{i=0}^{n-1} \v{a}_i \v{b}_i \left( z^{2n-1-i} + z^{2n+i} \right)
+ \sum_{i=0}^{n-1} \v{c}_i \v{d}_i \left( z^{i} + z^{4n-1-i} \right)
$$

The equation

$$
\revdot{\v{r}}{\v{r} \circ \v{z^{4n}} + \v{t}} = 0
$$

is equivalent to the gate equations, where the correction vector $\v{t}$
is determined by $z$ such that
$\revdot{\v{r}}{\v{t}} = -\sum_i \v{c}_i(z^{2n-1-i} + z^{2n+i})$
for all $\v{r}$.[^t-def] Expanding gives

$$
\sum_{i=0}^{n-1} (\v{a}_i \v{b}_i - \v{c}_i)(z^{2n-1-i} + z^{2n+i})
+ \sum_{i=0}^{n-1} \v{c}_i \v{d}_i (z^{i} + z^{4n-1-i}) = 0
$$

Viewed as a polynomial in $z$, the left-hand side has two sums over disjoint
monomial ranges. Vanishing of this polynomial forces each monomial coefficient
to zero: the first sum requires $\v{a} \circ \v{b} = \v{c}$, the second
requires $\v{c} \circ \v{d} = \v{0^n}$. By Schwartz–Zippel, vanishing at a
single random $z$ implies the polynomial vanishes identically (and hence the
gate equations hold) with overwhelming probability.[^sz-gate]

The constraints can be similarly collapsed into a single revdot check. Given an
instance vector $\v{k} \in \F^{4n}$, the $j$-th constraint can be written
$\revdot{\v{r}}{\v{u_j}} = \v{k}_j$, where $\v{u_j} \in \F^{4n}$ encodes the
$j$-th constraint's wire weights at the revdot complements of the trace
monomials. Given a verifier challenge $y \in \F$, we can stack all $4n$
constraints into a structured vector $\v{s} = \sum_{j=0}^{4n-1} y^j \v{u_j}$.
For a valid trace, linearity of revdot gives:

$$
\revdot{\v{r}}{\v{s}}
= \sum_{j=0}^{4n-1} y^j \revdot{\v{r}}{\v{u_j}}
= \sum_{j=0}^{4n-1} y^j \v{k}_j
= \dot{\v{k}}{\v{y^{4n}}}
$$

If any constraint is violated, the two sides differ as polynomials in $y$ of
degree at most $4n-1$, so by Schwartz–Zippel a random $y$ detects the
violation with overwhelming probability.[^sz-constraint]

Ragu combines these checks into a single equation that establishes both with
high probability for random $y, z \in \F$:

$$
\boxed{\revdot{\v{r}}{\v{r} \circ \v{z^{4n}} + \v{t} + \v{s}} = \dot{\v{k}}{\v{y^{4n}}}}
$$

Viewed as a polynomial in $z$, the gate check spans every power of $z$ while the
constraint check is $z$-independent (since $\v{s}$ depends only on the verifier
challenge $y$). Treated as a polynomial identity in $z$, the $z^{4n-1}$
coefficient gives $\v{c}_0 \v{d}_0 = 0$ and the $z^0$ coefficient gives $\v{c}_0
\v{d}_0 + \revdot{\v{r}}{\v{s}} = \dot{\v{k}}{\v{y^{4n}}}$, which together
recover the constraint check $\revdot{\v{r}}{\v{s}} = \dot{\v{k}}{\v{y^{4n}}}$.
By Schwartz–Zippel, a single random $(y, z)$ suffices.[^sz-combined]

[^soundness-scope]: This document argues only (standard) soundness: that an
    accepting verifier implies the gate and constraint equations hold. The
    concrete protocol also satisfies knowledge soundness, with an extractor that
    recovers a valid trace from any successful prover; extraction failure is
    bounded by analogous Schwartz–Zippel reasoning. Completeness is immediate,
    since an honest prover's trace satisfies the combined equation identically
    in $y$ and $z$ by construction.

[^sz-gate]: The left-hand side is a polynomial in $z$ whose monomials span
    $z^0, \ldots, z^{4n-1}$, hence it has degree at most $4n-1$. By the
    Schwartz–Zippel lemma, if the polynomial is nonzero then for $z$ drawn
    uniformly from $\F$ the probability that it vanishes at $z$ is at most
    $(4n-1)/|\F|$.

[^sz-constraint]: The difference has degree at most $4n-1$ in $y$, so by
    Schwartz–Zippel the soundness error for $y$ drawn uniformly from $\F$ is
    at most $(4n-1)/|\F|$.

[^sz-combined]: By linearity of revdot, the combined error decomposes additively
    as $E(y, z) = G(z) + C(y)$, where $G(z) := \revdot{\v{r}}{\v{r} \circ
    \v{z^{4n}} + \v{t}}$ is the gate error and $C(y) := \revdot{\v{r}}{\v{s}} -
    \dot{\v{k}}{\v{y^{4n}}}$ is the constraint error, each of degree $\leq 4n-1$
    in its sole variable. If gates fail, $G \not\equiv 0$ and Schwartz–Zippel on
    $z$ gives soundness error $\leq (4n-1)/|\F|$ for every $y$; if only
    constraints fail, symmetric in $y$; if both fail, for each $y$ the bad $z$'s
    are roots of $G(Z) + C(y)$, still a nonzero polynomial of degree $\leq 4n-1$
    in $z$. Either way, soundness error is at most $(4n-1)/|\F|$, and this bound
    is sharp.

[^whydwires]: The $\v{d}$ wires arise from the revdot product's pairing of
    $\v{a} \leftrightarrow \v{b}$ and $\v{c} \leftrightarrow \v{d}$. The gate
    equation $\v{c}_i \v{d}_i = 0$ forces $\v{d}_i = 0$ whenever $\v{c}_i \ne
    0$, which is typical; at gates where $\v{c}_i = 0$ it is a free wire that
    can carry additional witness data. The $\v{d}$ wires must appear in the
    soundness argument regardless of their use; they are unneeded to arithmetize
    any circuit.

[^why4n]: The constraint vectors $\v{u_j}$ are restrictions at $Y = y$ of a
    bivariate **wiring polynomial** $s(X, Y)$ (see [Wiring
    Polynomials](wiring.md)) that must itself fit within the structured
    polynomial space when restricted at $X$, capping the number of constraints
    at $4n$. Reducing a general R1CS instance to a Ragu circuit takes just over
    $3n$ constraints in the worst case (closer to $2n$ in favorable cases),
    leaving headroom for public inputs.

[^t-def]: This definition uniquely determines $\v{t}$ as a function of $z$
    alone, independent of $\v{r}$. The structured polynomial $t(X, Z)$ it
    encodes is a sum of two geometric series, in ratios $XZ$ and (formally)
    $X/Z$, so $t$ is a polynomial with $t(X, 0) = 0$:
    $$-t(X, Z) = X^{3n} Z^n \sum_{k=0}^{n-1} (XZ)^k + X^{3n} Z^{3n-1} \sum_{k=0}^{n-1} (X/Z)^k.$$
