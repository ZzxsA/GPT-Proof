# Distinct sums of two powers of the same base

**ZzxsA and ChatGPT (OpenAI)**

In May 2023 Zhi-Wei Sun asked about representations of a positive even integer $2n$ as a sum of **distinct numerical values** of the form $b^i+b^j$, with nonnegative exponents. This folder treats both clauses of Conjecture 1(i). [Original statement, OEIS A362861](https://oeis.org/A362861)

* For $b=5$, precisely the following indices $n$ lack a representation of $2n$: **2, 7, 10, 11, 12, 27, 35, 50, 51, 52, 55, 60, 135, 255**. Thus 510 is the largest even integer without a representation.
* For $b=3$, every positive even integer has a representation.

For example, the first even integer above the largest exception is $512=6+126+130+250$. The four summands are $1+5$, $1+125$, $5+125$ and $125+125$.

## Powers of five

Write $h(a,j)=(5^a+5^j)/2$. Dividing all summands by two preserves distinctness. For $0\le j\le a<5$ the fifteen values are

    1, 3, 5, 13, 15, 25, 63, 65, 75, 125, 313, 315, 325, 375, 625.

Their subset sums cover every integer from 256 through 2087. Below 256 the missing indices are exactly the fourteen above. Every other allowed value is at least $(5^5+1)/2=1563$, so none can fill one of those holes. The independent Python calculation and the Lean seed certificate check this finite step.

To extend the interval, use five fresh values per exponent $s\ge5$, namely $h(s,j)$ for $0\le j<5$. An interval containing $W$ consecutive representable integers and its translate by a fresh summand $c\le W$ form one interval of length $W+c$. Start a stage with $W\ge u=(5^s+1)/2$. Its first summand is $u$ and every other summand in that stage is less than $2u$. The five extensions are therefore possible, and the final width is at least $6u\ge(5^{s+1}+1)/2$. The new summands exceed all summands used at earlier stages and are distinct within the stage. Iteration covers every integer from 256 onwards.

## Powers of three

Expand $n$ in base three. A digit 1 in position $i$ contributes $3^i+3^i$ to $2n$. A digit 2 contributes $3^i+3^{i+1}$. In both cases the highest power of three dividing the contribution is exactly $3^i$, so terms from different positions are distinct.

## Reproduce

From this folder, using the Lean version pinned in the repository root, run

```sh
python3 verify_seed.py
export LEAN_PATH="$(mktemp -d)"
lean Ternary.lean
lean -o "$LEAN_PATH/SeedFive.olean" SeedFive.lean
lean -o "$LEAN_PATH/FiveCoverage.olean" FiveCoverage.lean
lean FiveCharacterization.lean
```

[Finite certificate](SeedFive.lean) · [Interval induction](FiveCoverage.lean) · [Exact base-five statement](FiveCharacterization.lean) · [Ternary construction](Ternary.lean) · [Independent enumeration](verify_seed.py)

## Prior work

Sun listed all fourteen candidate exceptions in the original entry. Martin Ehrenstein subsequently recorded that a fifteenth term, if it existed, would have to be at least one million. Searches by sequence number, exception values and equivalent descriptions did not locate an earlier published proof of the full classification. The [OEIS Open results catalog](https://github.com/epoch-research/LeanOpenProblems-results/tree/cbb7cb657f24157d9ebb7640ec50bd35bad78ad8/metadata/oeis) has no entry for A362861 in either conjecture or sequence metadata. The ternary construction follows directly from positional notation. [OEIS A362861 and its dated comments](https://oeis.org/A362861)
