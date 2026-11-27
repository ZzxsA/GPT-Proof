# Strict growth of the shifted reciprocal floor series

**ZzxsA and ChatGPT (OpenAI)**

Clark Kimberling conjectured on 10 July 2017 that the coefficients of the following series at $r=(3+\sqrt5)/2$ increase strictly. Define
$$
A_r(x)=\frac{1}{\sum_{n\ge0}(-1)^n\left(\lfloor(n+1)r\rfloor-1\right)x^n}
       =\sum_{n\ge0}a_n x^n .
$$
We prove that $a_n>0$ and $a_{n+1}\ge2a_n$ for every $n\ge0$ and every $5/2\le r<8/3$. The specified quadratic irrational belongs to this interval. Subtracting one inside the floor gives the same integer because the shift is integral. This differs from the earlier A078140 problem, whose denominator uses unshifted floors. The OEIS entry states the conjecture and lists 30 coefficients. Searches by sequence number, initial terms and shifted floor-series formula found no earlier proof of this conjecture. [OEIS A289245](https://oeis.org/A289245)

## Proof

Write $G=1/A_r$ and $D=(1+x)G=\sum d_j x^j$, so $D A_r=1+x$. The floors at $r,2r,3r$ are $2,5,7$ throughout the interval. Hence $d_0=1$, $d_1=-3$ and $d_2=2$. For $j\ge1$, $d_j=(-1)^j(\lfloor(j+1)r\rfloor-\lfloor jr\rfloor)$ and the unsigned increment belongs to $\{2,3\}$.

We have $a_0=1$, $a_1=4$ and $a_2=10$. Suppose the doubling inequality holds through $a_{n-1}$, with $n\ge3$. The degree-$n$ coefficient equation gives
$$
a_n=3a_{n-1}-2a_{n-2}-\sum_{j=3}^n d_j a_{n-j}.
$$
In the sum, pair each odd index $j$ with the following even index. Each complete pair is at most $-2a_{n-j}+3a_{n-j-1}\le0$ by induction. An unpaired odd term is negative. Thus $a_n\ge3a_{n-1}-2a_{n-2}\ge2a_{n-1}$ and positivity follows.

## Verification

`ShiftedFloor.lean` constructs the coefficients recursively, proves their formal Cauchy product with the given floor series is one, verifies the doubling bound on the interval, and specializes it to the exact quadratic irrational. Its public theorems are `KimberlingShift.coefficients_are_reciprocal`, `KimberlingShift.doubled` and `KimberlingShift.a289245_strict`. It uses the existing Cauchy product from `proofs/kimberling-a289261/Kimberling.lean` and mathlib4 v4.19.0. The repository workflow builds that module before checking this proof. [Lean proof](ShiftedFloor.lean) · [Verification workflow](../../.github/workflows/verify.yml)

From this directory, run `python3 verify_shifted.py` for an independent exact check against the 30 listed terms and through the first 1,000 doubling inequalities.
