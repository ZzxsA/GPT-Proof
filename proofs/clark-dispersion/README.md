# Clark's extremal graph-dispersion conjecture

**ZzxsA and ChatGPT (OpenAI)**

For a connected simple graph, let $D$ be the degree and $X$ the entry of a positive adjacency Perron eigenvector at a uniformly chosen vertex. Write $c(Y)=\operatorname{Var}(Y)/(\mathbb E Y)^2$ and $\gamma=\max X/\min X$. Gregory J. Clark's Conjecture 4.4 concerns the quantity $\Gamma=(c(D)-c(X))/\gamma^2$. The journal article gives this sign convention. Clark's Theorem 4.3 already establishes the limit $1/4$ along stars. [Published paper, §§4.3–4.4](https://ora.ox.ac.uk/objects/uuid%3Ace57e3be-9b68-4934-93c4-f1a9ab477517/files/r08612p623)

## Results

* At each order $n\ge2$, the star $K_{1,n-1}$ maximizes $\Gamma$. Equality characterizes the star up to isomorphism.
* Over all orders the infimum of $\Gamma$ is $-1/27$ and the supremum is $1/4$. Both inequalities are strict for every finite graph.
* If $c(D)$ tends to infinity, then $\liminf c(X)\ge1$. This rules out the family with $c(X)\to0$ asked about immediately after the conjecture.

The central estimate comes from the symmetric adjacency matrix. The identities and inequalities $\mathbb E(DX)=\rho\,\mathbb EX$, $\mathbb ED^2\le\rho^2$ and covariance Cauchy–Schwarz imply
$$
c(X)\;\ge\;\frac{c(D)}{(1+\sqrt{1+c(D)})^2}.
$$
Bounding the degree variance by its range gives the fixed-order estimate with equality at the star. A separate family on $4m$ vertices has $\Gamma=-1/27+1/(3(m-1)^2)$ for each positive multiple of three $m$. [Full mathematical proof and prior work](PROOF.md)

## Lean and reproduction

| File | Result checked in Lean |
|---|---|
| [GraphQuarter.lean](GraphQuarter.lean) | The universal upper bound for a nonnegative adjacency matrix supplied with a normalized positive eigenpair. |
| [Scalar.lean](Scalar.lean) | The explicit increasing upper envelope and the lower bound in terms of scalar dispersions and ratios. |
| [Moments.lean](Moments.lean) | The degree second-moment inequality, the covariance estimate and the sharp upper envelope directly from symmetric adjacency. |
| [SimpleGraphBound.lean](SimpleGraphBound.lean) | The upper envelope in terms of the number of vertices of a mathlib simple graph supplied with its normalized eigenpair. |
| [Star.lean](Star.lean) | The star's adjacency, positive eigenpair, extremal entries and exact value of the envelope. |
| [LowerFamily.lean](LowerFamily.lean) | A universal lower estimate, the adjacency and exact value of the connected example family, and approximation to $-1/27$ to arbitrary positive accuracy. |

The paper proof includes the equality-case uniqueness argument, strictness at the lower endpoint, and the limiting argument for $c(X)$. The Lean graph statements take the positive eigenpair as input. For a connected graph of order at least two it exists by Perron–Frobenius. The Lean version is 4.19.0 and the pinned mathlib revision and build commands are in the [verification workflow](../../.github/workflows/verify.yml). The optional [numerical enumeration](check_small.py) uses NumPy and checks the fixed-order theorem on every connected labelled simple graph of orders 2 through 6.

A search of the journal version, citing works, and public proof repositories on 27 November 2026 found no earlier explicit resolution of Conjecture 4.4. The published result on the “Four's a Crowd” conjecture concerns a different statistic from the same paper. [Csikvári and Harangi](https://doi.org/10.1016/j.jctb.2026.03.003)
