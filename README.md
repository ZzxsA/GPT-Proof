# GPT-Proof

**ZzxsA and ChatGPT (OpenAI)**

## Proof index

The table collects counterexamples. The sections below it also index proved conjectures and constructive answers. For the Harkness sequence, $a(n)$ is the least positive period. For graphs, θ is the fewest cliques needed to cover all vertices and b is the fewest rounds needed to burn the graph.

| Conjecture | Claim | Counterexample | Lean |
|---|---|---|---|
| [Shu Liu · Conjecture 1](proofs/liu-self-orthogonal-mds/) | For even prime powers $q\ge4$, there is no Euclidean self-orthogonal $[q+2,3]$ MDS code. | An explicit $[18,3,16]$ code over $\mathbb F_{16}$ has zero Gram matrix and 816 nonzero three-column minors. | [Lean matrix certificate](proofs/liu-self-orthogonal-mds/Liu16.lean) |
| [Larson and Van Cleemput · Table 15, row 2](proofs/larson-van-cleemput-periphery/) | On independence-irreducible graphs, $\alpha\ge \lvert\mathrm{Per}\rvert-\Delta-\mathrm{res}$. | Two matched five-cliques give $2<10-5-2=3$. The graph and invariant values appear in the authors' 2017 data. | [Lean proof](proofs/larson-van-cleemput-periphery/Prism.lean) |
| [Sun · OEIS A362743, Conjecture 3](proofs/sun-a362743/) | With even product of the bases, every sufficiently large integer is an admissible sum. | Bases 4 and 16 fail at every $4^L-1$, $L\ge 1$. | [Lean proof](proofs/sun-a362743/A362743.lean) |
| [Sun · OEIS A362861, Conjecture 3](proofs/sun-a362861/) | With two odd bases, every sufficiently large even integer is an admissible sum. | Bases 5 and 25 fail at every $5^L-1$, $L\ge 1$. | [Lean proof](proofs/sun-a362861/A362861.lean) |
| [Harkness period conjecture · OEIS A353890](proofs/harkness-period/) | The largest prime factor of $a(n)$ equals $(2^n+1)/3$ for prime $n\ge5$. | At $n=29$, the prediction is composite: $178956971=59\cdot3033169$. | [Lean proof](proofs/harkness-period/HarknessPeriod.lean) |
| [AutoGraphForge #1656 · Claw-free regular graphs](proofs/agf-1656/) | θ ≤ 3b − 4 | The 23-vertex cycle makes the left side at least 12 and the proposed upper bound at most 11. | [Lean certificate](proofs/agf-1656/Witness_c5b13d43.lean) |
| [AutoGraphForge #2256 · Graphs of maximum degree three or less](proofs/agf-2256/) | θ ≤ 3b − 2 | The 33-vertex cycle makes the left side at least 17 and the proposed upper bound at most 16. | [Lean certificate](proofs/agf-2256/Witness_31b3af5f.lean) |
| [AutoGraphForge #2618 · Eulerian graphs](proofs/agf-2618/) | θ ≤ 2b + 6 | The 41-vertex cycle makes the left side at least 21 and the proposed upper bound at most 20. | [Lean certificate](proofs/agf-2618/Witness_a1136330.lean) |

The Harkness folder also contains the proof of the general period theorem and two independent computations of the exact period. [Mathematical proof](proofs/harkness-period/PROOF.md)

For the two Conjecture 3 entries, an admissible sum uses terms of the form $k^a+m^b$ with nonnegative exponents and no summand dividing another. [Common obstruction](proofs/shared/sun-antichain/PROOF.md)

## Proved conjectures

| Conjecture | Result | Formal proof |
|---|---|---|
| [Gregory J. Clark · graph dispersion, Conjecture 4.4](proofs/clark-dispersion/) | The star maximizes the normalized dispersion difference at each fixed order. The infimum over all connected simple graphs is $-1/27$ and the supremum is $1/4$. | [Graph upper bound](proofs/clark-dispersion/SimpleGraphBound.lean) · [Star](proofs/clark-dispersion/Star.lean) · [Sharp lower bound](proofs/clark-dispersion/LowerFamily.lean) |
| [Andres Cicuttin · Farey alignment, A363321](proofs/cicuttin-farey/) | Among the reduced fractions of order $n$, the fraction that agree with the equally spaced grid at the same position tends to zero. | [Lean theorem](proofs/cicuttin-farey/FareyAlignment.lean) |
| [Peter Bala · power-series congruences, A361281 and A293013](proofs/bala-congruences/) | For all integral series $F,G$ with $G(0)=1$, the integers $b_n=n![x^n]F(x)\exp(xG(x)^n)$ satisfy $b_{n+k}\equiv b_n\pmod{k}$. | [Coefficient theorem](proofs/bala-congruences/BalaExp.lean) |
| [Clark Kimberling · shifted golden-ratio series, A289245](proofs/kimberling-a289245/) | After the change in the floor sequence, each coefficient is at least twice the preceding one throughout $5/2\le r<8/3$. | [Lean theorem](proofs/kimberling-a289245/ShiftedFloor.lean) |

[Clark Kimberling · strict increase of reciprocal floor-series coefficients](proofs/kimberling-a078140/). Among $1\le r<2$, the coefficients of the reciprocal of $\sum_{n\ge0}(-1)^n\lfloor(n+1)r\rfloor x^n$ are strictly increasing exactly for $3/2\le r<5/3$. This includes the golden ratio and the separate OEIS A289261 conjecture at $r=13/8$. [Real-parameter theorem](proofs/kimberling-a078140/KimberlingReal.lean) · [Independent proof for 13/8](proofs/kimberling-a289261/)

[Sun · OEIS A362861, Conjecture 1(i)](proofs/sun-a362861-1i/) asks which positive even integers are sums of distinct values of the form $b^i+b^j$. For $b=5$, exactly the 14 listed indices fail. For $b=3$, every positive even integer has a representation. [Base five](proofs/sun-a362861-1i/FiveCharacterization.lean) · [Base three](proofs/sun-a362861-1i/Ternary.lean)

[Sun · OEIS A362861, Conjecture 1(ii), first assertion](proofs/sun-a362861-1ii/) asks about distinct summands of the form $3^a+7^b$. Every positive even integer has a representation, already with $b\le 1$. More generally, the unordered pairs of odd bases greater than one that cover every positive even integer are exactly $(3,3),(3,5),(3,7)$. [Lean classification](proofs/sun-a362861-1ii/Classification.lean)

## Partial results on open conjectures

[Shu Liu · Conjecture 2, odd-field self-orthogonal MDS codes](proofs/liu-odd-self-orthogonal-mds/). The proposed nonexistence holds over every odd prime field and over $\mathbb F_9$. Lean rules out extended generalized Reed–Solomon generators at the stated dimension over all odd finite fields. The field-specific conclusion also uses published arc-classification theorems. [Lean obstruction](proofs/liu-odd-self-orthogonal-mds/OddGRS.lean) · [Independent calculation over seven elements](proofs/liu-odd-self-orthogonal-mds/LiuSeven.lean)

## Corrections to published statements

[Huang, Fang and Fu · intersection dimensions of MDS codes](proofs/huang-fang-fu-mds/). Theorem 4 in the 2021 preprint allows a ternary $[4,2,3]$ code contained in a $[4,3,2]$ code. No such pair exists. The classical odd-order hyperoval obstruction also supplies an infinite family of excluded parameters. [Lean proof of the ternary case](proofs/huang-fang-fu-mds/HuangFangFu.lean)

## Open problems with a constructive answer

[Knor, Sedlar, Škrekovski and Zhang · Problem 14](proofs/knor-geodesics-14/) asks for a graph family exceeding their benchmark for the number of shortest paths. On nine vertices the count rises from 90 to 105. As the graph order increases, the ratio tends to $121/81$. This resolves the construction part of the question. [Finite Lean certificates](proofs/knor-geodesics-14/Geodesics.lean) · [General lower bound](proofs/knor-geodesics-14/LayerFamily.lean)

## Ongoing search

The daily graph search tests 19 additional candidate inequalities. Run artifacts contain generated witnesses, search reports and verification logs and are retained for 30 days. [Candidate catalog](counterexamples/degree_catalog.json) · [Search code and reproduction guide](counterexamples/) · [GitHub Actions runs](https://github.com/ZzxsA/GPT-Proof/actions/workflows/counterexamples.yml)
