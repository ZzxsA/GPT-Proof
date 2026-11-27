# The odd-field self-orthogonal MDS conjecture

**ZzxsA and ChatGPT (OpenAI)**

Shu Liu's Conjecture 2 asks whether a Euclidean self-orthogonal linear MDS code of length $q+1$ and dimension $k=(q-1)/2$ can exist over any odd field $\mathbb F_q$. Proposition 4.9 of the same preprint settles $q=3,5$. Here we prove nonexistence for **every odd prime $q$ and also $q=9$**. For arbitrary odd prime powers we prove nonexistence for all column scalings of a normal rational curve, equivalently for the full-length extended generalized Reed–Solomon class. A code outside that class at the other odd composite field sizes remains a possible exception. [Liu, Conjecture 2 and Proposition 4.9](https://arxiv.org/html/2611.30048v1)

## The finite-field obstruction

In the extended Reed–Solomon class the columns, up to a common invertible change of row basis and permutation, are
$$
s(t)(1,t,\ldots,t^{k-1})^{\mathsf T}\quad(t\in\mathbb F_q),\qquad
e(0,\ldots,0,1)^{\mathsf T},
$$
where every $s(t)$ and $e$ is nonzero. Changing row basis or permuting coordinates preserves zero Gram matrix. Let $w(t)=s(t)^2$ and $M_j=\sum_t w(t)t^j$. For $k\ge2$, products of row entries cover every monomial degree $0$ through $2k-2=q-3$; the infinity column contributes only to the final diagonal entry. For $k=1$ there is only that diagonal entry. Hence
$$
M_j=0\quad(0\le j<q-3),\qquad M_{q-3}=-e^2.
$$

For any fixed $x$ the indicator of $t=x$ equals $1-\sum_{j=0}^{q-1}t^jx^{q-1-j}$. When $t\ne x$, the sum is $(t^q-x^q)/(t-x)=1$. At $t=x$ all $q$ summands equal $x^{q-1}$ and sum to zero in the field. Multiply by $w(t)$ and sum in $t$. The vanishing moments leave
$$
w(x)=\sum_t w(t)-M_{q-3}x^2-M_{q-2}x-M_{q-1}
    =e^2x^2+Bx+C .
$$
Thus a monic quadratic $x^2+bx+c$ must take a nonzero square value at every element of $\mathbb F_q$, as seen by dividing by $e^2$.

Completing the square and translating $x$ reduces this to $x^2+d$. The case $d=0$ gives a zero value. If $d\ne0$, choose a square root $y(x)$ at each $x$ and set $u(x)=y(x)-x$. The identity $u(x)(y(x)+x)=d$ makes $u(x)$ nonzero. The value of $u$ determines $y+x=d/u$, hence also $2x=d/u-u$ and $x$. This would inject $\mathbb F_q$ into its $q-1$ nonzero elements. Odd characteristic is used when recovering $x$ from $2x$.

## Consequences for general MDS codes

The columns of a generator of any $[q+1,k]$ MDS code with $k\ge2$ represent $q+1$ projective points, any $k$ of which span the space. Such a set is called an arc. Theorem 36 of Ball and Lavrauw says that an arc of size $q+1$ in $\mathrm{PG}(k-1,q)$ is a normal rational curve when $k\le p=\operatorname{char}\mathbb F_q$ and $k\ne(q+1)/2$. For an odd prime $q\ge5$ both hypotheses hold for $k=(q-1)/2$. At $q=9$, $k=4$, and Segre's theorem on arcs of size $q+1$ in projective 3-space makes the arc a twisted cubic, again a normal rational curve. For $q=3$, the dimension is one and every length-four MDS generator has four nonzero entries, already covered above. These deductions use the published geometric classification. [Ball and Lavrauw, *Arcs in finite projective spaces*, Theorems 36 and 62](https://web.mat.upc.edu/simeon.michael.ball/expositoryarcs.pdf)

The literature search on 27 November 2026 covered Liu's preprint, extended generalized Reed–Solomon Euclidean self-orthogonality, and classifications of maximal arcs. The arc theorems and finite-field power identities are classical. We found no earlier explicit all-odd-prime conclusion for Liu's parameters. The full conjecture for nonclassical arcs over other odd composite field sizes remains open in this work.

## An independent check at seven

Given any eight columns spanning an $[8,3,6]_7$ code, put two projective points at $(0,1,0)$ and $(0,0,1)$ by a row basis change. The other six are affine representatives $(1,x,y)$ with six distinct $x$ and six distinct $y$ coordinates, because no three columns are dependent. Translating both coordinates sends the missing $x$ and missing $y$ to zero; scale the $y$ coordinate to arrange $f(1)=1$. All these changes come from invertible row operations, and the individual nonzero column multipliers are retained as unknowns. In this form the remaining five values of $f$ permute $2,3,4,5,6$.

The finite certificate finds exactly one such arc, with $f(x)=x^{-1}$. Let $w_x$ denote the squared multipliers, each in $\{1,2,4\}$. If the three Gram entries in the first row vanish, the affine contribution to either the second or the third diagonal entry is zero. The corresponding infinity coordinate then contributes a nonzero square to that diagonal, ruling out a zero Gram matrix.

## Verification

* `OddGRS.lean` proves `LiuOdd.no_extended_grs_self_orthogonal` directly for the Gram entries of the full-length extended GRS generator over every odd finite field. Its intermediate theorem `LiuOdd.no_grs_weights` proves the finite-field moment obstruction. The application of the published arc classification to general codes in the prime and order-nine cases is given above.
* `LiuSeven.lean` checks the normalized case independently in Lean's standard library, including every allowed permutation and every possible choice of square multipliers. The finite normalization is justified above.
* `verify_seven.py` independently enumerates all 120 normalized permutations, all admissible diagonal scalings, and checks the corresponding complete Gram matrices.

Use the repository's pinned Lean 4.19.0 and mathlib v4.19.0. From this directory, run `lean LiuSeven.lean` and `python3 verify_seven.py`. To run the general file, set `PROOF` to its absolute path, switch to a built mathlib checkout, and run `lake env lean "$PROOF"`.
