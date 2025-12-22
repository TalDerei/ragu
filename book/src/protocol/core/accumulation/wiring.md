# Split-accumulation for Wiring Consistency

In our [Polynomial IOP](../nark.md#polynomial-iop), the wiring polynomial
$s(X,Y)$ that encodes the wiring among wires of `mul` gate is fixed and publicly
accessible before any online proving. During the
[verification](../nark.md#the-verification-checks), the verifier must conduct
$O(n)$ amount of work to locally compute $s(x,y)$. Theoretically, the IOP prover
can send a polynomial oracle for $s(X,Y)$ to the verifier for opening at any
$(x,y)$ evaluation point cheaply. However, this would necessitate a bivariate PCS
-- a complexity Ragu tries to avoid. Ragu only relies on simple univariate PCS.

Instead, in [step 3 of our NARK](../nark.md#nark), the NARK prover sends over the
commitment $S\in\G$ of the univariate $s(X,y)$ fixated at the challenge $y\in\F$.
Then, in step 4, the prover starts a _wiring consistency_ protocol to convince
the verifier that $S$ is indeed a valid commitment to $s(X,y)$ rather than some
arbitrary circuits $s'(X,y)$.

[Halo paper](https://eprint.iacr.org/2019/1021) proposed one construction for
a [single fixed circuit](#single-circuit-consistency). Ragu extends it to support
proving $s_i(X,Y)$ belongs to a [fixed set of circuits](#mesh-concistency)
$\set{s_j(X,Y)}$. Such extension allows consistency checks on different step
circuits (and even more granular sub-step circuits) as long as they are from a
[_mesh_](../../extensions/mesh.md) of pre-registered circuits.

## Intuition

A fundamental property of multivariate polynomials is that two degree-bounded polynomials are equal if and only if they agree at all points in their domain. Our protocol exploits this to verify polynomial equality probabilistically through random challenge points. 

Given two representations of a polynomial $p(W, X, Y)$, we verify consistency by evaluating at random challenge points. By the Schwartz-Zippel lemma, if two distinct polynomials of degree $d$ are evaluated at a random point, they agree with probability at most $d/|\mathbb{F}|$.

The protocol uses *partial evaluations* to reduce the dimensionality of the polynomial equality checks. We fix variables at specific challenge points and create lower-dimensional restrictions, where in each evaluation at most one variable remains free:

| Evaluation | Type | Description |
|------------|------|-------------|
| $p(W, x, y)$ | $\mathbb{F}[W]$ | Univariate in $W$ for fixed $x$ and $y$ |
| $p(w, X, y)$ | $\mathbb{F}[X]$ | Univariate in $X$ for fixed $w$ and $y$ |
| $p(w, x, Y)$ | $\mathbb{F}[Y]$ | Univariate in $Y$ for fixed $w$ and $x$ |
| $p(w, x, y)$ | $\mathbb{F}$ | Point evaluation |

This mirrors the technique used in the [sumcheck](https://people.cs.georgetown.edu/jthaler/sumcheck.pdf) protocol: within a protocol, we alternate between (univariate) restrictions of a polynomial using random challenges to prove equality, probabilistically reducing a claim about many different evaluations of a polynomial to a single polynomial evaluation.

If independent parties claim to hold evaluations of the same mesh polynomial $m(W, X, Y)$ at different points $(w_i, x_i, y_i)$ and $(w_z, x_z, y_z)$, we can verify they share the same underlying polynomial by:

1. Sampling random challenges $w^*, x^*, y^*$,
2. Evaluating the claimed polynomials at restrictions like $m(w^*, X, Y)$, $m(W, x^*, Y)$, etc,
3. Checking that the restricted polynomials agree at further challenge points

This ensures that claimed evaluations at different points are derived from the same underlying mesh $m(W, X, Y)$.

## Single-circuit consistency

Instantiating the intuition above for a single fixed $s(X,Y)$. Let the accumulator 
$\acc.\inst=(S_{old}\in\G, y_{old}\in\F)$ be the folded previous claims.
Accordingly, the witness is $\acc.\wit=s_{old}(X,y_{old})\in\F[X]$.

Given a new claim $(S, y)$ (i.e. "$S=\com(s(X,y))$ with the challenge $y$"),
the prover further folds it into the accumulator as follows:

1. Prover sends the new commitment $S$
2. Verifier samples $x_{new}\sample\F$
3. Prover sends the commitment to the restriction $S'\leftarrow \com(s(x_{new},Y))$
4. Verifier samples $y_{new}\sample\F$
5. Prover sends the updated accumulator $\acc'.S=S_{new}:= \com(s(X, y_{new}))$
6. Prover and Verifier engage in a [batched PCS evaluation](./pcs.md) protocol
   for claims: $(S_{old}, x, v_1), (S', y_{old}, v_1), (S_{new}, x, v_2),
   (S',y_{new}, v_2)$

The partial evaluation $s'(x,Y)$ restricted at $x$ bridges the bivariate claims.
The completeness property holds because:
$$
\begin{cases}
s_{old}(x_{new})=S(x_{new}, y_{old})=s'(y_{old})\\
s_{new}(x_{new})=S(x_{new}, y_{new})=s'(y_{new})
\end{cases}
$$

## Mesh Consistency

Given the definition of [mesh polynomials](../../extensions/mesh.md), we now
