# Cicuttin's Farey alignment conjecture

**ZzxsA and ChatGPT (OpenAI)**

Order the reduced fractions in $[0,1]$ with denominators at most $n$. Write the resulting Farey sequence as $f_0,\dots,f_M$, where $M=\sum_{d=1}^n\varphi(d)$. On 27 May 2023, Andres Cicuttin conjectured that the proportion of indices $j$ with $f_j=j/M$ tends to zero. We prove the conjecture. At $n=5$ there are eleven grid points, seven fractions shared by the two sets, and five matches in the same position. The same-position count is OEIS A363321. [A363321](https://oeis.org/A363321) · [A363300, the common-point count](https://oeis.org/A363300)

## Proof

Let $A$ be the number of matches and let $B$ count the fractions that occur anywhere on both grids. Every reduced $a/d=j/M$ satisfies $d\mid M$. Conversely, if $d\mid M$, every reduced fraction with denominator $d$ appears somewhere on the uniform grid. Counting the endpoint $1$ separately gives
$$
 A\le B=1+\sum_{d\mid M,\ d\le n}\varphi(d)\le 1+n\tau(M),
$$
where $\tau$ counts positive divisors. The classical estimates $M\sim 3n^2/\pi^2$ and $\tau(m)=O_\delta(m^\delta)$ for each $\delta>0$ now give $A/(M+1)=O_\varepsilon(n^{-1+\varepsilon})$. The bound also applies to $B$. These estimates are classical inputs to this short proof. [Hardy and Wright, *An Introduction to the Theory of Numbers*, Theorems 315 and 330 and the ensuing Farey corollary](https://blngcc.wordpress.com/wp-content/uploads/2008/11/hardy-wright-theory_of_numbers.pdf)

## Elementary proof used by Lean

One fixed power saving suffices for the conjectured limit. Put $C=4096^{16}$. We have $\tau(m)^4\le Cm$. Indeed, for $p\ge16$ one has $(a+1)^4\le16^a\le p^a$. For $2\le p<16$ one has $(a+1)^4\le4096\,2^a$ by checking $0\le a\le6$ and increasing the exponent in steps of four. Multiplication over the distinct prime factors involves at most 16 exceptional factors.

Let $T=\max_{0\le d\le n}\tau(d)$, taking $\tau(0)=0$. The divisor sum identity for the totient gives $d=\sum_{i\mid d}\varphi(i)\le\tau(d)\varphi(d)$, since $i\mid d$ implies $\varphi(i)\mid\varphi(d)$. Thus $n^2\le2MT$, and $T^4\le Cn$ gives $n^7\le16CM^4$. The elementary upper bound $M\le 2n^2$ gives $\tau(M)^4\le2Cn^2$. Since $A\le 2n\tau(M)$ for $n\ge1$, these inequalities give
$$
 n A^4 \le 512 C^2 M^4 .
$$
In particular, $n\ge512 C^2 k^4+1$ suffices for $k A\le M+1$. Taking any integer $k>1/\varepsilon$ proves the required limit.

`FareyAlignment.count` enumerates reduced proper fractions and compares their exact ranks with the grid, including the right endpoint separately. `FareyAlignment.density_zero` states the reciprocal-integer epsilon form of the limit for this count. The finite proof uses Lean 4.19.0 and mathlib v4.19.0. With that mathlib checkout built, run

```sh
lake env lean /absolute/path/to/FareyAlignment.lean
python3 /absolute/path/to/verify_farey.py
```

The Python script independently generates and sorts exact rationals and checks the first 80 published counts. Searches for Cicuttin's name, both sequence numbers, and exact coincidences between Farey fractions and equal grids did not locate an earlier proof specific to this conjecture. Results on the rank discrepancy and the divisor bounds used here predate the question. [Farey rank discrepancy literature](https://cs.uwaterloo.ca/journals/JIS/VOL25/Tomas/tomas5.pdf)
