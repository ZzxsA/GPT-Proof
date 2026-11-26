# The largest prime factor of the Harkness period

**Mo Li (ZzxsA) and ChatGPT (OpenAI)**

Let $n\ge5$ be prime. For $m\ge1$ put $D_n(m)=(m+1)^n-m^n$, and set $b_n(m)=1$ if $D_n(m)$ and $D_n(m+1)$ are coprime, or $0$ otherwise. Since $\gcd(A,B)=\gcd(A,B-A)$, this agrees with the original definition using first and second differences. Let $a(n)$ be the least positive period of $b_n$. The argument below also establishes its existence. [Harkness, OEIS A353890](https://oeis.org/A353890)

**Theorem.** Put $J_n=(2^n+1)/3$. Every prime divisor of $J_n$ divides $a(n)$, and every prime divisor of $a(n)$ is at most $J_n$. Consequently, the largest prime factor of $a(n)$ equals $J_n$ if and only if $J_n$ is prime.

## Which primes divide the period?

For a prime $p$, let $R_p$ be the set of residues $m$ for which

$$m^n=(m+1)^n=(m+2)^n\pmod p.$$

The binary sequence vanishes precisely when $m\bmod p$ belongs to some $R_p$. Each $R_p$ omits zero. At a collision all three powers are nonzero, and $p\ne2$. Dividing the three bases by $m+1$ gives $x,1,2-x$. Here $x$ and $2-x$ are distinct, nonidentity $n$th roots of unity. As $n$ is prime, $x$ has order $n$. Hence $n\mid p-1$ and $2-x=x^t$ for some $2\le t\le n-1$. Conversely, such an $x$ gives $m=x/(1-x)$.

Write $\Phi_n(X)=1+X+\cdots+X^{n-1}$, and put

$$N_t=\operatorname{Res}(\Phi_n(X),2-X-X^t),\qquad 2\le t\le n-1.$$

Each $N_t$ is a nonzero integer. A common complex root would satisfy $x+x^t=2$ with both summands on the unit circle, forcing $x=1$ and contradicting $\Phi_n(1)=n$. If $n\mid p-1$, then $\Phi_n$ splits into distinct linear factors modulo $p$. Vanishing of the resultant modulo $p$ is therefore equivalent to a common root in the prime field. Thus

$$S=\{p:R_p\ne\varnothing\}=\{p\text{ prime}:n\mid p-1,\ p\mid N_t\text{ for some }t\}$$

is finite. Let $P$ be the product of its distinct members. Membership in every $R_p$ depends only on $m\bmod P$, so $P$ is a period. If $h$ is any positive period and $p\in S$ does not divide $h$, then $L=h(P/p)$ is also a period and $L\not\equiv0\pmod p$. By the Chinese remainder theorem, choose $m\ge1$ with any desired residue mod $p$ and zero residue at every other prime in $S$. Translating by $L$ preserves the zero residues. Periodicity would force $R_p$ to be invariant under a nonzero translation mod $p$. Such a translation generates the whole additive group, but $R_p$ is nonempty and omits zero. This contradiction proves $a(n)=P$.

## Lower and upper bounds

For the divisibility assertion, $3\nmid J_n$. Indeed, expanding $2^n=(-1+3)^n$ modulo 9 gives $J_n\equiv n\pmod3$. If $p\mid J_n$, then $2^n\equiv-1\pmod p$. The three consecutive residues $-2/3,1/3,4/3$ have equal $n$th powers modulo $p$, since $(-2)^n=4^n=1\pmod p$. It follows that $p\in S$.

For the upper bound, use the directed graph on $\mathbb Z/n\mathbb Z$ with an edge from each $i$ to $i+1$ and to $i+t$. It is strongly connected, with out-degree two. Let $\tau_t$ count its directed spanning trees oriented toward a fixed root. All root counts coincide by translation. The out-degree Laplacian has eigenvalues $2-\zeta^j-\zeta^{tj}$ for $0\le j<n$, where $\zeta$ is a primitive complex $n$th root of unity. The term at $j=0$ is the only zero eigenvalue. The coefficient of $z$ in $\det(zI+L)$ is the product of the nonzero eigenvalues, namely $N_t$. Expanding the same coefficient in principal minors and applying the directed matrix-tree theorem gives $N_t=n\tau_t$.

Lonc, Parol and Wojciechowski proved that the maximum number of rooted directed spanning trees for a directed circulant graph on $n$ vertices of out-degree two is $\lfloor(2^n+1)/3\rfloor$. Thus $\tau_t\le J_n$. For $p\in S$, we have $p\mid N_t$ for some $t$ and $n\mid p-1$, so $p\ne n$ and $p\mid\tau_t$. In particular $p\le J_n$. Together with the divisibility assertion this proves the theorem. [Lonc, Parol and Wojciechowski, *Networks* 37 (2001), 129–133](https://doi.org/10.1002/net.2)

## The first counterexample

The predicted values for $n=5,7,11,13,17,19,23$ are respectively $11,43,683,2731,43691,174763,2796203$. All are prime. For $n=29$ the prediction is $178956971=59\cdot3033169$. Hence 29 is the least counterexample. The other expression in the original conjecture, $\varphi(2^{29}+1)/2+1$, is also composite: it equals $175923745=5\cdot35184749$. The factorization of $J_{29}$ predates the conjecture. [OEIS A250291](https://oeis.org/A250291)

At $n=29$ the product formula gives exactly these prime factors of the least period:

```text
59, 233, 349, 929, 4003, 8353, 16067, 19489, 21577, 23201,
215587, 3033169, 23641903, 61584227, 89854181, 107367629, 108050869
```

Their product is

```text
23185169775494678703965601811862664516267203026525520380383050531459422153206071324389
```

The largest factor occurs at $t=4$, where $N_4=29\cdot108050869$. At $m=71665491$, all three consecutive powers give the residue $95285273$ modulo $108050869$. The same prime also occurs in a published LDPC graph calculation. [Xu et al., *Entropy* 28 (2026), Appendix A.2](https://doi.org/10.3390/e28101123)

The [integer-matrix computation](verify_harkness.py) produces a witness for each prime. The [polynomial-remainder computation](harkness_independent.py) recomputes the complete set by a second algorithm. The [Lean source](HarknessPeriod.lean) states the original conjecture using the least positive period and proves its negation by the factorization at 29.
