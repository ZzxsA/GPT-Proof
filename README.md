# GPT-Proof

**ZzxsA and ChatGPT (OpenAI)**

## Proof index

Each entry links to the original conjecture, an explicit counterexample and instructions for checking the proof. For the Harkness sequence, $a(n)$ is the least positive period. For graphs, θ is the fewest cliques needed to cover all vertices and b is the fewest rounds needed to burn the graph.

| Conjecture | Claim | Counterexample | Lean |
|---|---|---|---|
| [Harkness period conjecture · OEIS A353890](proofs/harkness-period/) | The largest prime factor of $a(n)$ equals $(2^n+1)/3$ for prime $n\ge5$. | At $n=29$, the prediction is composite: $178956971=59\cdot3033169$. | [Lean proof](proofs/harkness-period/HarknessPeriod.lean) |
| [AutoGraphForge #1656 · Claw-free regular graphs](proofs/agf-1656/) | θ ≤ 3b − 4 | The 23-vertex cycle makes the left side at least 12 and the proposed upper bound at most 11. | [Lean certificate](proofs/agf-1656/Witness_c5b13d43.lean) |
| [AutoGraphForge #2256 · Graphs of maximum degree three or less](proofs/agf-2256/) | θ ≤ 3b − 2 | The 33-vertex cycle makes the left side at least 17 and the proposed upper bound at most 16. | [Lean certificate](proofs/agf-2256/Witness_31b3af5f.lean) |
| [AutoGraphForge #2618 · Eulerian graphs](proofs/agf-2618/) | θ ≤ 2b + 6 | The 41-vertex cycle makes the left side at least 21 and the proposed upper bound at most 20. | [Lean certificate](proofs/agf-2618/Witness_a1136330.lean) |

The Harkness folder also contains the proof of the general period theorem and two independent computations of the exact period. [Mathematical proof](proofs/harkness-period/PROOF.md)

## Ongoing search

The daily graph search tests 19 additional candidate inequalities. Run artifacts contain generated witnesses, search reports and verification logs and are retained for 30 days. [Candidate catalog](counterexamples/degree_catalog.json) · [Search code and reproduction guide](counterexamples/) · [GitHub Actions runs](https://github.com/ZzxsA/GPT-Proof/actions/workflows/counterexamples.yml)
