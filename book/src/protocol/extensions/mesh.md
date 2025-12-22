# Mesh Polynomial

As [previously discussed](../core/arithmetization.md), individual circuits can be represented entirely by a polynomial $s(X, Y)$ that represents all of its linear constraints. In order to make many different circuits available within the protocol simultaneously, it will be useful to define a mesh polynomial $m(W, X, Y)$ in that third formal indeterminate $W$ that interpolates such that

$$
m(\omega^i, X, Y) = s_i(X, Y)
$$

for some root of unity $\omega \in \mathbb{F}$ of sufficiently large $2^k$ order to index all circuits. Evaluating the mesh at any domain point $W = \omega^i$ recovers exactly the $i$-th circuit's bivariate polynomial.

## Construction 

The mesh is a collection of circuits over a particular field, and the mesh has a *domain*, where each circuit is mapped to a successive power of $\omega$ in the domain. 

For instance, the mesh $m(W, x, y)$ is the polynomial free in $W$ that interpolates all circuit points. At each point $\omega$ in the domain, the mesh polynomial equals the $i$-th circuit's evaluation: 

$$
m(\omega^i, x, y) = s_i(x, y)
$$

These consistency checks may require evaluating the mesh polynomial free in $X$:

$$
m(\omega^i, X, y) \;\equiv\; s_i(X, y)
$$

More generally, the protocol needs to evaluate the mesh at *arbitrary* challenge points $w \in \mathbb{F}$ (not necessarily a root of unity $\omega$). We use Lagrange coefficients for polynomial interpolation. Suppose the mesh is defined on the points ${\omega^0, \omega^1, ..., \omega^{n-1}}$ with 

$$
f_i(X,y) \;=\; m(\omega^i, X, y) \;=\; s_i(X,y)
$$

Then for any $w \in \mathbb{F}$

$$
m(w, X, y) \;=\; \sum_{i=0}^{n-1} \ell_i(w)\, f_i(X,y)
$$

where the Lagrange basis coefficients are

$$
\ell_i(w) \;=\; \prod_{\substack{0\le j< n\\ j\ne i}} \frac{w-\omega^j}{\omega^i-\omega^j}.
$$

This gives you a polynomial that *(i)* passes through all circuit evaluations at their respective $\omega^i$ points, and *(ii)* evaluates to the correct interpolated value at the random challenge point $W = w$.

## Flexible Mesh Sizes via Domain Extension

The mesh requires a domain size $2^k$ for some non-negative integer k and assigns circuits to successive powers $\omega^j$, where $\omega$ is a $2^k$ primitive root of unity in the field. The domain size determines the degree of the interpolation polynomial. 

A naive approach to mesh construction would assign the $j$-th circuit directly to $\omega^j$ where $\omega$ is chosen based on the domain size $2^k$ needed to fit all circuits. However, this creates a fundamental problem: **the domain size must be known in advance**. If we allocate a $2^k$ domain and later register a $(2^k+1)$-th circuit into the mesh, we would outgrow the mesh and most previously-assigned values in the domain would be incorrect.

This limitation is cleverly resolved through *rolling domain extensions*: the domain is "rolling" in the sense that the mesh accepts circuits incrementally without knowing the final domain size $k$. When $k$ is fixed at mesh finalization, we use a bit-reversal technique that maps each circuit to its correct position in the finalized domain.


### Bit-Reversal

The way this construction works is $\omega$ values are *precomputed* in the maximal field domain $2^S$; the actual working domain $2^k$ is determined later and depends on the number of circuits that end up being registered in the mesh. The precomputation remains valid regardless of $k$.

To assign a domain point to the $j$-th circuit, we don't use $\omega^j$ directly. Instead, we fix a maximal upper bound $k = S$ and set

$$
i := \text{bitreverse}(j, S)
$$

where we reverse the bits of $j$ to compute the power $i$, and assign circuit $j$ to domain point $\omega_S^i$. This bit-reversal ensures we effectively exhaust the smaller domains first. 

During mesh finalization when $k = \lceil \log_2 C \rceil$ is determined, the value $\omega_S^i$ (where $i = \text{bitreverse}(j, S)$) assigned to circuit $j$ is re-expressed in the smaller $2^k$ domain as $\omega_k^{i \gg (S-k)}$ (by right-shifting the exponent).

Notice that these represent the same field element in different domains, since $\omega_k = \omega_S^{2^{S-k}}$. We've effectively compressed the $2^S$-slot domain to the $2^k$-slot domain.
 
Consequently, circuit synthesis can compute $\omega_S^i$ at compile-time without knowing how many other circuits will be registered in the mesh. This has the property that the domain element assigned to circuit $j$ depends only on the circuit index $j$ and the fixed maximal bound $S$, not on the total number of
circuits $C$. This enables incremental circuit registration during compilation, where each circuit independently computes its domain point, and the mesh is finalized only after all circuits are known.
