# Wiring and Instance Polynomials

The combined [verifier check](arithmetization.md#combinedcheck) aggregates the
circuit's $4n$ constraints into a single structured vector $\v{s}$, using powers
of $y \in \F$ as weights. The vector $\v{s}$ encodes the $Y = y$ restriction of
a bivariate **wiring polynomial** $s(X, Y)$. It is _this_ polynomial which is
fixed by the circuit reduction (as it encodes the weights and their
corresponding wire associations), and the $\v{s}$ slice is one way it is
materialized in the real protocol when a verifier challenge $y$ is sampled.

In practice, $s(X, Y)$ is never materialized in its full bivariate form, only
partially or fully evaluated at concrete points. Circuits synthesize into wiring
polynomials through a procedural API—create a gate, add a constraint, etc.—and
[drivers](../../guide/drivers/index.md) interpret these calls for different
purposes. Because the protocol only ever requires (partial) evaluations of
wiring polynomials, the construction is organized around per-driver
specialization, with $s(X, Y)$ shaped to make each driver's evaluation path
efficient.

```admonish info
Due to technical reasons discussed later, the real protocol also requires the
univariate restriction $s(x, Y)$ to be evaluated and manipulated. In order to
provide for a homogeneous degree bound, the degree of $s(X, Y)$ is less than $4n$
in each variable separately. As a consequence, there are only $4n$ possible
constraints in a circuit arithmetization.
```

For example, constraints fold into $s(X, Y)$ via the
[Horner update](https://en.wikipedia.org/wiki/Horner%27s_method)
$s \leftarrow Y \cdot s + u$, landing the first-emitted constraint at the
highest $Y$-power and the last-emitted at $Y^0$. The $s(x, y)$ driver exploits
this most sharply: the assembly rule is its evaluation loop.

## Public Inputs

The instance vector $\v{k}$ is sparse because most constraints have $\v{k}_j =
0$, as only public input constraints contribute nonzero entries. In order to
encourage $\v{k}$ to represent a low-degree polynomial $k(Y)$, we prefer that
public inputs are located only in the first elements of $\v{k}$.

Public input constraints are linear forms over the circuit's wires (typically,
the final outputs of the computations encoded within the circuit) and the
synthesis API admits constraints over wires already allocated. Public inputs are
therefore emitted last, which naturally aligns both with the desire to keep
$k(Y)$ low degree and to use Horner's rule to assign constraints to descending
powers of $Y$.

## The `SYSTEM` Gate

There is a special gate in all wiring polynomials called the `SYSTEM` gate,
which is the first gate over wires $\v{a}_0, \v{b}_0, \v{c}_0, \v{d}_0$. The
wire $\color{blue}{\v{d}_0}$ is a special wire called [`ONE`] which is the
constant wire; in wiring polynomials that verify circuits, it is enforced to
equal $1$ through the final constraint, via $k(0) = s(X, 0) = X^0 = 1$.

The $\color{#7e22ce}{\v{c}_0 = 0}$ wire assignment ensures $r(0) = 0$ for every
trace, and this is forced by the gate equations when $\color{blue}{\v{d}_0 =
1}$. Conventionally, we allow $\color{#dc2626}{\v{a}_0}$ to carry an arbitrary
(blinding) value $\color{#dc2626}{\alpha}$ for all traces, and thus $\v{b}_0 =
0$ is assigned so that the gate equations are always satisfied.

The constraint for $Y^{4n - 1}$ is reserved for the
[registry](../extensions/registry.md), which injects a fixed "key" value
$\color{#7e22ce}{\kappa}$ into a meaningless constraint over the
$\color{#7e22ce}{\v{c}_0}$ wire, which is assigned to $0$ in all traces
anyway. The purpose of this key is to make non-trivial evaluations of
$s(X, Y)$ unpredictable even to someone who chooses $s$, since the key can be
computed as a hash digest of $s$ prior to the substitution of
$\color{#7e22ce}{\kappa}$.

```admonish info
Due to these special gates and constraints, circuit wiring polynomials have
at most $4n - 2$ usable constraints and only $n - 1$ usable gates.
```

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

## Layout

| trace $\uparrow$ | monomials | wiring $\downarrow$ | $Y^0$ | $\cdots$ | $Y^{4n-1}$ |
|:--:|:--:|:--:|:--:|:--:|:--:|
| $\left.\begin{array}{ll} \v{d}_0 & = \color{blue}{0 \, \text{or} \, 1} \\ \v{d}_1 \\ \vdots \\ \v{d}_{n-1} \end{array}\right\}\v{d}$ | $\begin{array}{c} X^{4n-1} \\ X^{4n-2} \\ \vdots \\ X^{3n} \end{array}$ | $\v{c}\left\{\begin{array}{c} \color{#7e22ce}{\v{c}_0} \\ \v{c}_1 \\ \vdots \\ \v{c}_{n-1} \end{array}\right.$ | $\begin{array}{c} \color{#7e22ce}{0} \\ \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \end{array}$ | $\begin{array}{c} \color{#7e22ce}{0} \\ \phantom{\vdots} \\ \phantom{0} \\ \phantom{0} \end{array}$ | $\begin{array}{c} \color{#7e22ce}{\kappa} \\ \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \end{array}$ |
| $\left.\begin{array}{ll} \v{b}_{n-1} & \phantom{= 0 \, \text{or} \, 1} \\ \vdots \\ \v{b}_1 \\ \v{b}_0 & = 0 \end{array}\right\}\v{b}$ | $\begin{array}{c} X^{3n-1} \\ \vdots \\ X^{2n+1} \\ X^{2n} \end{array}$ | $\v{a}\left\{\begin{array}{c} \v{a}_{n-1} \\ \vdots \\ \v{a}_1 \\ \color{#dc2626}{\v{a}_0} \end{array}\right.$ | $\begin{array}{c} \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \\ \color{#dc2626}{0} \end{array}$ | $\begin{array}{c} \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \\ \color{#dc2626}{0} \end{array}$ | $\begin{array}{c} \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \\ \color{#dc2626}{0} \end{array}$ |
| $\left.\begin{array}{ll} \color{#dc2626}{\v{a}_0} & = \color{#dc2626}{\alpha} \\ \v{a}_1 & \phantom{= 0 \, \text{or} \, 1} \\ \vdots \\ \v{a}_{n-1} \end{array}\right\}\v{a}$ | $\begin{array}{c} X^{2n-1} \\ X^{2n-2} \\ \vdots \\ X^n \end{array}$ | $\v{b}\left\{\begin{array}{c} \v{b}_0 \\ \v{b}_1 \\ \vdots \\ \v{b}_{n-1} \end{array}\right.$ | $\begin{array}{c} 0 \\ \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \end{array}$ | $\begin{array}{c} 0 \\ \phantom{\vdots} \\ \phantom{0} \\ \phantom{0} \end{array}$ | $\begin{array}{c} 0 \\ \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \end{array}$ |
| $\left.\begin{array}{ll} \v{c}_{n-1} & \phantom{= 0 \, \text{or} \, 1} \\ \vdots \\ \v{c}_1 \\ \color{#7e22ce}{\v{c}_0} & \color{#7e22ce}{= 0} \end{array}\right\}\v{c}$ | $\begin{array}{c} X^{n-1} \\ \vdots \\ X^1 \\ X^0 \end{array}$ | $\v{d}\left\{\begin{array}{c} \v{d}_{n-1} \\ \vdots \\ \v{d}_1 \\ \color{blue}{\v{d}_0} \end{array}\right.$ | $\begin{array}{c} \phantom{0 \, \text{or} \, 1} \\ \phantom{0 \, \text{or} \, 1} \\ \phantom{0 \, \text{or} \, 1} \\ \color{blue}{0 \, \text{or} \, 1} \end{array}$ | $\begin{array}{c} \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \\ \phantom{0} \end{array}$ | $\begin{array}{c} \phantom{0} \\ \phantom{\vdots} \\ \phantom{0} \\ \phantom{0} \end{array}$ |

[`ONE`]: ragu_core::drivers::Driver::ONE
