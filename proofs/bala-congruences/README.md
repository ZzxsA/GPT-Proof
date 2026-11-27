# Bala's shift congruence for an exponential family

**ZzxsA and ChatGPT (OpenAI)**

On 12 March 2023 Peter Bala conjectured that for $F,G\in\mathbb Z[[x]]$ with $G(0)=1$, the numbers
$$
 b(n)=n![x^n]F(x)\exp\bigl(xG(x)^n\bigr)
$$
satisfy $b(n+k)\equiv b(n)\pmod{k}$ for every $n\ge0$ and $k\ge1$. Here $[x^n]$ extracts the coefficient of $x^n$. The proof below also establishes integrality. Substituting $F=1$, $G=1+x$ gives A361281, while $G=1/(1-x)$ gives the separate A293013 conjecture. [Original general conjecture](https://oeis.org/A361281) · [A293013](https://oeis.org/A293013)

## Proof

Write $H=G-1$ and $c_{ji}=[x^j]F H^i$. Since $H$ has zero constant term, $c_{ji}=0$ for $i>j$. Expanding the exponential by its exponent $s$, then setting $j=n-s$, gives
$$
 b(n)=\sum_{j=0}^n n^{\underline j}
      \sum_{i=0}^{j} c_{ji}\binom{n(n-j)}{i},
 \qquad n^{\underline j}=n(n-1)\cdots(n-j+1).
$$
Indeed the coefficient left over after extracting $x^s$ is $[x^j]F G^{ns}$, to which we apply the binomial theorem with $G=1+H$.

Compare the sums for $m=n+k$ and $n$. The polynomial $x^{\underline j}=\prod_{t=0}^{j-1}(x-t)$ has integer coefficients, so $m^{\underline j}\equiv n^{\underline j}\pmod{k}$. For $j>n$, $n^{\underline j}=0$, and the extra summands for $m$ vanish modulo $k$. For $j\le n$ the arguments $u=m(m-j)$ and $v=n(n-j)$ are congruent modulo $k$. Applying the same polynomial observation at degree $i$ gives
$$
 i!\binom ui = u^{\underline i}\equiv v^{\underline i}=i!\binom vi\pmod k .
$$
Since $i\le j$, $i!$ divides $j!$, and $j!$ divides $n^{\underline j}=j!\binom nj$. The second binomial factor can therefore be replaced modulo $k$ after the falling-factorial replacement above. This proves the congruence for every $i,j$ and all integer arrays $c_{ji}$. The modulus is optimal for the whole family, since $F=x$, $G=1$ gives $b(n)=n$.

Pure periodicity follows at every positive modulus, with the least period dividing $k$. For A361281 the first four values are $1,1,5,37$, so every value is 1 modulo 4. Its second-index value is 5, so $a(5n+2)$ is divisible by 5. This also settles the two observations preceding the general conjecture in the OEIS entry.

## Verification

`Bala.diagonal_shift` proves the congruence termwise for arbitrary integer arrays. `Bala.universal_shift` connects the array to actual integral formal power series and proves the congruence for the integral finite coefficient expression. `Bala.exp_shift` identifies that expression with the corresponding factorial-scaled rational exponential coefficient. The exponential is defined by its finite coefficient sum in each degree. The independent Python computation obtains coefficients by the differential identity $E'=(xG^n)'E$ and checks them against the binomial expansion.

Use Lean 4.19.0 and mathlib v4.19.0. From the mathlib checkout with the needed caches installed, let `src` be the absolute path to this folder and run

```sh
export src
export mods=$(mktemp -d)
lake env bash -ec '
  export LEAN_PATH="$mods:$LEAN_PATH"
  lean --root="$src" -o "$mods/Bala.olean" "$src/Bala.lean"
  lean --root="$src" -o "$mods/BalaSeries.olean" "$src/BalaSeries.lean"
  lean --root="$src" "$src/BalaExp.lean"
'
python3 "$src/verify_bala.py"
```

## Prior work

Bala's earlier Theorem 1 proves shift congruences for the fixed generating function $F(x)\exp(xG(x))$. A different March 2023 conjecture on A278070 concerns $\exp(xG(x))F(x)^n$. AlphaProof Nexus verified the A278070 sequence and Ahaan Kallat proved that latter family by Lagrange inversion. The exponent $n$ in the present conjecture occurs on $G$ **inside** the exponential. A search on 27 November 2026 by both OEIS identifiers, their general formula, and Bala's name did not identify an earlier resolution of this formulation. [Bala's fixed-series theorem](https://oeis.org/A047974/a047974_1.pdf) · [A278070 and its references](https://oeis.org/A278070) · [Kallat's paper](https://arxiv.org/abs/2610.15849) · [Kallat's formal statement](https://github.com/ahaankallat/congruence-phenomena-higher-order-lean/blob/master/CongruenceTheoryHigherOrder/LagrangeFamily.lean)
