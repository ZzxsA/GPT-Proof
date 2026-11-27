# GPT-Proof

**ZzxsA and ChatGPT (OpenAI)**

## Proof index

The table collects counterexamples. The sections below it also index proved conjectures and constructive answers. For the Harkness sequence, $a(n)$ is the least positive period. For graphs, θ is the fewest cliques needed to cover all vertices and b is the fewest rounds needed to burn the graph.

| Conjecture | Claim | Counterexample | Lean |
|---|---|---|---|
| [Sun · OEIS A362743, Conjecture 3](proofs/sun-a362743/) | With even product of the bases, every sufficiently large integer is an admissible sum. | Bases 4 and 16 fail at every $4^L-1$, $L\ge 1$. | [Lean proof](proofs/sun-a362743/A362743.lean) |
| [Sun · OEIS A362861, Conjecture 3](proofs/sun-a362861/) | With two odd bases, every sufficiently large even integer is an admissible sum. | Bases 5 and 25 fail at every $5^L-1$, $L\ge 1$. | [Lean proof](proofs/sun-a362861/A362861.lean) |
| [Harkness period conjecture · OEIS A353890](proofs/harkness-period/) | The largest prime factor of $a(n)$ equals $(2^n+1)/3$ for prime $n\ge5$. | At $n=29$, the prediction is composite: $178956971=59\cdot3033169$. | [Lean proof](proofs/harkness-period/HarknessPeriod.lean) |
| [AutoGraphForge #1656 · Claw-free regular graphs](proofs/agf-1656/) | θ ≤ 3b − 4 | The 23-vertex cycle makes the left side at least 12 and the proposed upper bound at most 11. | [Lean certificate](proofs/agf-1656/Witness_c5b13d43.lean) |
| [AutoGraphForge #2256 · Graphs of maximum degree three or less](proofs/agf-2256/) | θ ≤ 3b − 2 | The 33-vertex cycle makes the left side at least 17 and the proposed upper bound at most 16. | [Lean certificate](proofs/agf-2256/Witness_31b3af5f.lean) |
| [AutoGraphForge #2618 · Eulerian graphs](proofs/agf-2618/) | θ ≤ 2b + 6 | The 41-vertex cycle makes the left side at least 21 and the proposed upper bound at most 20. | [Lean certificate](proofs/agf-2618/Witness_a1136330.lean) |

The Harkness folder also contains the proof of the general period theorem and two independent computations of the exact period. [Mathematical proof](proofs/harkness-period/PROOF.md)

For the two Conjecture 3 entries, an admissible sum uses terms of the form $k^a+m^b$ with nonnegative exponents and no summand dividing another. [Common obstruction](proofs/shared/sun-antichain/PROOF.md)

## Proved conjectures

[Sun · OEIS A362861, Conjecture 1(i)](proofs/sun-a362861-1i/) asks which positive even integers are sums of distinct values of the form $b^i+b^j$. For $b=5$, exactly the 14 listed indices fail. For $b=3$, every positive even integer has a representation. [Base five](proofs/sun-a362861-1i/FiveCharacterization.lean) · [Base three](proofs/sun-a362861-1i/Ternary.lean)

## Open problems with a constructive answer

[Knor, Sedlar, Škrekovski and Zhang · Problem 14](proofs/knor-geodesics-14/) asks for a graph family exceeding their benchmark for the number of shortest paths. On nine vertices the count rises from 90 to 105. As the graph order increases, the ratio tends to $121/81$. This resolves the construction part of the question. [Finite Lean certificates](proofs/knor-geodesics-14/Geodesics.lean) · [General lower bound](proofs/knor-geodesics-14/LayerFamily.lean)

## Ongoing search

The daily graph search tests 19 additional candidate inequalities. Run artifacts contain generated witnesses, search reports and verification logs and are retained for 30 days. [Candidate catalog](counterexamples/degree_catalog.json) · [Search code and reproduction guide](counterexamples/) · [GitHub Actions runs](https://github.com/ZzxsA/GPT-Proof/actions/workflows/counterexamples.yml)
