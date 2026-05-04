# Wiring and Instance Polynomials

The combined [verifier check](arithmetization.md#combinedcheck) aggregates the
circuit's $4n$ constraints into a single structured vector $\v{s}$, using powers
of $y \in \F$ as weights. The vector $\v{s}$ encodes the $Y = y$ restriction of
a bivariate **wiring polynomial** $s(X, Y)$. It is _this_ polynomial which is
fixed by the circuit definition (as it encodes the weights and their
corresponding wire associations), and the $\v{s}$ vector is one way it is
materialized in the protocol after a verifier challenge $y$ is sampled.

In practice, $s(X, Y)$ is never represented in its full bivariate form, only
partially or fully evaluated at concrete points. Circuits synthesize into wiring
polynomials through a procedural API—create a gate, add a constraint, etc.—and
[drivers](../../guide/drivers/index.md) interpret these calls for different
purposes. Because the protocol only ever requires (partial) evaluations of
wiring polynomials, the construction is organized around per-driver
specialization, with $s(X, Y)$ shaped to make each driver's evaluation path
efficient.

```admonish info
Due to technical reasons discussed
[later](../core/accumulation/wiring.md), the real protocol also
requires the univariate restriction $s(x, Y)$ to be evaluated and manipulated.
In order to provide for a homogeneous degree bound, the degree of
$s(X, Y)$ is less than $4n$ in each variable separately. As a consequence,
there are only $4n$ possible constraints in a circuit arithmetization.
```

For example, the driver that computes $s(x, y)$ uses [Horner's
rule](https://en.wikipedia.org/wiki/Horner%27s_method) as its evaluation loop.
Each newly emitted constraint folds into the accumulating wiring polynomial via
the update $s(X, Y) \leftarrow Y \cdot s(X, Y) + u(X)$, where $u(X)$ is the
constraint's linear form over wires. This lands the first-emitted constraint at
the highest $Y$ power and the last-emitted at $Y^0$.

## Public Inputs

The instance vector $\v{k}$ encodes the expected values that linear combinations
over the wires are required to take due to the circuit's
[constraints](arithmetization.md). Public input constraints are designated
constraints where $\v{k}_j$ takes a nonzero value set during verification.

Public inputs tend to take the value of final computation outputs within a
circuit, and so their constraints are emitted last so they may naturally relate
to every previously emitted wire. As a result, Ragu tends to refer to these as
"public outputs" from the perspective of circuits.

This gives the layout

$$
\v{k} = \bigl(\,
  \underbrace{1}_{\v{k}_0}\,,\;
  \underbrace{\v{k}_1, \ldots, \v{k}_\ell}_{\text{public outputs (reversed)}}\,,\;
  \underbrace{0, \ldots, 0}_{\text{constraints}}\,
\bigr).
$$

due to the Horner ordering described above (last emitted at the lowest
$Y$-powers). The first value $\v{k}_0 = 1$ seeds the circuit with a stable
constant value; it is like a public input that is always set to
$1$.[^instance-literature] The remaining values of $\v{k}$ are implicitly set to
zero because circuit implementations themselves only emit constraints using
[`enforce_zero`](ragu_core::drivers::Driver::enforce_zero).

$\v{k}$ thus represents the coefficients of a low degree polynomial
$k(Y)$, which is ideal for the verifier.

[^instance-literature]: In the literature, the public instance is often
presented as the pair $(1, \v{x})$, combining the constant $1$ with the public
inputs $\v{x}$ into a single vector. Ragu's $\v{k}$ matches this convention.

## The `SYSTEM` Gate

There is a special gate in all wiring polynomials called the `SYSTEM` gate,
which is the first gate over wires $\v{a}_0, \v{b}_0, \v{c}_0, \v{d}_0$:

* The wire $\color{blue}{\v{d}_0}$ is a special wire called [`ONE`] which is the
  constant wire; in wiring polynomials that verify circuits, it is enforced to
  equal $1$ through the final constraint, via $k(0) = s(X, 0) = \v{k}_0 X^0 =
  1$. In a sense, the `ONE` wire stashes the $1$ value provided at $\v{k}_0$ by
  the verifier so that it is available in all future constraints.
* The $\color{#7e22ce}{\v{c}_0 = 0}$ wire assignment ensures $r(0) = 0$ for
  every trace, and this is forced by the gate equations when $\color{blue}{\v{d}_0
  = 1}$.
* The $\color{#dc2626}{\v{a}_0}$ slot carries an arbitrary value
  $\color{#dc2626}{\alpha}$ for every trace, with $\v{b}_0 = 0$ chosen so the
  gate equations remain satisfied.[^conventionally] This value is not a
  zero-knowledge blind, and is meant to keep adversarially-determined linear
  combinations of polynomial commitments away from the point at infinity.

There is also a special constraint $\color{#7e22ce}{\kappa} \v{c}_0 = 0$
injected in all wiring polynomials at the $Y^{4n - 1}$ position; circuits are
restricted in the number of constraints they emit to avoid overlapping this
term. This so-called [registry constraint](../extensions/registry.md) is
trivially satisfied for all values of $\color{#7e22ce}{\kappa}$, since $\v{c}_0
= 0$ anyway. In practice, $\color{#7e22ce}{\kappa}$ is a fixed value computed as
a digest of $s(X, Y)$ prior to its substitution, forcing every non-trivial
evaluation of $s$ to be unpredictable even to someone who chooses $s$.

[^conventionally]: There is nothing preventing the roles of $\v{a}_0$ and
    $\v{b}_0$ from being swapped, since neither wire is actually constrained in
    practice. However, because $\v{a}_0$ and $\v{d}_0$ are used as "free" wires
    during allocation for symmetry, this is maintained in the `SYSTEM` gate as a
    convention.

## Bonding Polynomials

Wiring polynomials typically verify constraints for circuit traces, but there do
exist wiring polynomials that only enforce constraints on incomplete traces.
These exist internally to Ragu and are called **bonding polynomials**.

Unlike circuit wiring polynomials, which are checked with
$
\revdot{\v{r}}{\v{r} \circ \v{z^{4n}} + \v{t} + \v{s}} = \dot{\v{k}}{\v{y^{4n}}}
$,
bonding polynomials instead appear in claims of the form
$\revdot{\v{r}}{\v{s}} = 0$, which do not enforce the gate equations on the
trace and permit batching.[^batching]

[^batching]: As an example, if two separate $\v{r_0}$ and $\v{r_1}$ must satisfy
a bonding revdot claim then $\revdot{\v{r_0} + z \v{r_1}}{\v{s}} = 0$ suffices
to check both at once.

In order to distinguish these polynomials from ordinary circuit wiring
polynomials, the $0$th constraint is not emitted in bonding polynomials, forcing
$k(0) = s(X, 0) = 0$. The verifier enforces the kind of wiring polynomial by
choosing $\v{k}_0$, since the revdot claim alone does not distinguish the two.

### Masking Polynomials

Masking polynomials are bonding polynomials used to constrain partial trace
polynomials (stages) so that nonzero wire assignments appear only at designated
gate positions.

The simplest theoretical mask $s_{\max}(X, Y) = \sum_{i=0}^{4n-1}(XY)^i$ would
zero every wire of every gate. Since `SYSTEM` gate wires are either unused or
constrained elsewhere, we instead use the _global mask polynomial_

$$s_{\text{global}}(X, Y) = s_{\max}(X, Y) - \bigl(1 + (XY)^{2n}\bigr)\bigl(1 + (XY)^{2n-1}\bigr),$$

which zeros every wire belonging to a non-`SYSTEM` gate (gates $1, 2, \ldots, n-1$).

A stage is parameterized by two integers $(g, m)$ with $g \geq 1$, $m \geq 0$,
and $g + m \leq n$; it owns the $m$ consecutive gates $g, g+1, \ldots, g+m-1$
and their $4m$ wire positions. Its mask polynomial is $s_{\text{global}}$ with
those positions removed:

$$s_{\text{mask}}(X, Y) = s_{\text{global}}(X, Y) - \bigl(1 + (XY)^{2n}\bigr)\bigl((XY)^g + (XY)^{2n-g-m}\bigr)\sum_{i=0}^{m-1}(XY)^i.$$

## Layout for Wiring Polynomials

| trace $\uparrow$ | monomials | wiring $\downarrow$ | $Y^0$ | $\cdots$ | $Y^{4n-1}$ |
|:--:|:--:|:--:|:--:|:--:|:--:|
| $\left.\begin{array}{ll} \v{d}_0 & = \color{blue}{0 \, \text{or} \, 1} \\ \v{d}_1 \\ \vdots \\ \v{d}_{n-1} \end{array}\right\}\v{d}$ | $\begin{array}{c} X^{4n-1} \\ X^{4n-2} \\ \vdots \\ X^{3n} \end{array}$ | $\v{c}\left\{\begin{array}{c} \color{#7e22ce}{\v{c}_0} \\ \v{c}_1 \\ \vdots \\ \v{c}_{n-1} \end{array}\right.$ | $\begin{array}{c} \color{#7e22ce}{0} \\ \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \end{array}$ | $\begin{array}{c} \color{#7e22ce}{0} \\ \phantom{\vdots} \\ \phantom{0} \\ \phantom{0} \end{array}$ | $\begin{array}{c} \color{#7e22ce}{\kappa} \\ \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \end{array}$ |
| $\left.\begin{array}{ll} \v{b}_{n-1} & \phantom{= 0 \, \text{or} \, 1} \\ \vdots \\ \v{b}_1 \\ \v{b}_0 & = 0 \end{array}\right\}\v{b}$ | $\begin{array}{c} X^{3n-1} \\ \vdots \\ X^{2n+1} \\ X^{2n} \end{array}$ | $\v{a}\left\{\begin{array}{c} \v{a}_{n-1} \\ \vdots \\ \v{a}_1 \\ \color{#dc2626}{\v{a}_0} \end{array}\right.$ | $\begin{array}{c} \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \\ \color{#dc2626}{0} \end{array}$ | $\begin{array}{c} \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \\ \color{#dc2626}{0} \end{array}$ | $\begin{array}{c} \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \\ \color{#dc2626}{0} \end{array}$ |
| $\left.\begin{array}{ll} \color{#dc2626}{\v{a}_0} & = \color{#dc2626}{\alpha} \\ \v{a}_1 & \phantom{= 0 \, \text{or} \, 1} \\ \vdots \\ \v{a}_{n-1} \end{array}\right\}\v{a}$ | $\begin{array}{c} X^{2n-1} \\ X^{2n-2} \\ \vdots \\ X^n \end{array}$ | $\v{b}\left\{\begin{array}{c} \v{b}_0 \\ \v{b}_1 \\ \vdots \\ \v{b}_{n-1} \end{array}\right.$ | $\begin{array}{c} 0 \\ \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \end{array}$ | $\begin{array}{c} 0 \\ \phantom{\vdots} \\ \phantom{0} \\ \phantom{0} \end{array}$ | $\begin{array}{c} 0 \\ \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \end{array}$ |
| $\left.\begin{array}{ll} \v{c}_{n-1} & \phantom{= 0 \, \text{or} \, 1} \\ \vdots \\ \v{c}_1 \\ \color{#7e22ce}{\v{c}_0} & \color{#7e22ce}{= 0} \end{array}\right\}\v{c}$ | $\begin{array}{c} X^{n-1} \\ \vdots \\ X^1 \\ X^0 \end{array}$ | $\v{d}\left\{\begin{array}{c} \v{d}_{n-1} \\ \vdots \\ \v{d}_1 \\ \color{blue}{\v{d}_0} \end{array}\right.$ | $\begin{array}{c} \phantom{0 \, \text{or} \, 1} \\ \phantom{\vdots} \\ \phantom{0 \, \text{or} \, 1} \\ \color{blue}{0 \, \text{or} \, 1} \end{array}$ | $\begin{array}{c} \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \\ \phantom{0} \end{array}$ | $\begin{array}{c} \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \\ \phantom{0} \end{array}$ |

[`ONE`]: ragu_core::drivers::Driver::ONE
