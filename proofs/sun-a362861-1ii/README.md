# Which pairs of odd bases represent every positive even integer?

**ZzxsA and ChatGPT (OpenAI)**

Zhi-Wei Sun asked in 2023 whether every positive even integer is a sum of distinct values of the form $3^a+7^b$ for nonnegative exponents. This is the first assertion of Conjecture 1(ii). [Original statement in OEIS A362861](https://oeis.org/A362861)

**Theorem.** For odd integers $3\le k\le m$, every positive even integer is a sum of pairwise distinct numerical values $k^a+m^b$ if and only if $(k,m)$ is one of $(3,3),(3,5),(3,7)$. For each of the three pairs it suffices to use $b=0$ and $b=1$. The even target 8 shows that allowing only $b=0$ would fail.

## Why the list is exhaustive

If both bases are at least 5, then 2 is the only available summand at most 4. Distinctness prevents using it twice. If $k=3$ and $m\ge9$, the only summands at most 8 are 2 and 4. Their sum is 6. These two obstructions leave exactly the three pairs listed above.

## Why the three pairs work

Write $m\in\{3,5,7\}$, $c_a=(3^a+1)/2$ and $d=(m-1)/2$. After division by 2, the exponents $b=0,1$ give the values $c_a$ and $c_a+d$. For $a=0,1,2$ the distinct values already fill the initial intervals below by taking subset sums.

| Second base | Distinct initial values | Interval of subset sums |
|---|---|---|
| 3 | 1, 2, 3, 5, 6 | 0 through 17 |
| 5 | 1, 2, 3, 4, 5, 7 | 0 through 22 |
| 7 | 1, 2, 4, 5, 8 | 0 through 20 |

If distinct summands cover $[0,S]$, adding a new summand $x\le S+1$ covers $[0,S+x]$, since the two intervals $[0,S]$ and $[x,S+x]$ leave no gap. This is the interval argument in Brown's criterion for complete sequences. [J. L. Brown, Jr., *Note on Complete Sequences of Integers* (1961)](https://doi.org/10.2307/2311150)

Start at $a=3$, where $c_3=14$ and each initial upper endpoint is at least 13. Suppose $S\ge c_a-1$. Append $c_a$, then $c_a+d$. Both satisfy the interval condition, since $S+1\ge c_a\ge d$. The new upper endpoint is at least $3c_a+d-1\ge c_{a+1}-1$, because $c_{a+1}=3c_a-1$. The new values remain distinct at every stage as $c_{a+1}-c_a=3^a>d$. The endpoints grow without bound. Multiplying the chosen terms by 2 yields the required representation.

For example, $100=88+8+4=(3^4+7)+(1+7)+(3+1)$. At target 8, setting $b=0$ allows only 2 and 4, regardless of the second base.

## Scope and prior work

Sun's second assertion of 1(ii) requires pairwise nondivisibility for summands of the form $3^a+5^b$. This folder proves distinctness. Conjecture 2 in the same entry asks about all sufficiently large even integers. Its quantifier allows the finite failures at 4 or 8. [OEIS A362861](https://oeis.org/A362861)

T. D. Noe tabulated the allowed summands in 2013. Brown's 1961 criterion supplies the positive-case argument. Searches using Sun's entry number, equivalent expressions for the summands, and the three-pair classification did not locate an earlier explicit proof of the specific claim. [OEIS A226816](https://oeis.org/A226816) · [Normalized summands](https://oeis.org/A226791) · [Brown's paper](https://doi.org/10.2307/2311150)

## Reproduce

From this folder, use the Lean toolchain pinned at the repository root.

```sh
python3 verify_pairs.py
export LEAN_PATH="$(mktemp -d)"
lean -o "$LEAN_PATH/ThreeSeven.olean" ThreeSeven.lean
lean -o "$LEAN_PATH/Obstructions.olean" Obstructions.lean
lean Classification.lean
```

[Positive cases](ThreeSeven.lean) · [Obstructions at 4 and 8](Obstructions.lean) · [Full classification](Classification.lean) · [Independent enumeration](verify_pairs.py)
