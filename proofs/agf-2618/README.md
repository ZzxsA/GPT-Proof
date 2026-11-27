# AutoGraphForge #2618 · Eulerian graphs

**Conjecture.** Every nontrivial Eulerian graph satisfies **θ ≤ 2b + 6**. Here θ is the fewest cliques needed to cover all vertices, and b is the fewest rounds needed to burn the graph. A graph is nontrivial if it has at least two vertices. AutoGraphForge records this proposal under ID `a1136330`. [Original statement](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2553)

## Counterexample

Take the cycle on **41 vertices**, numbered from 0 to 40. Walking once around this cycle traverses each edge exactly once and returns to the starting vertex. This gives an Euler tour.

Every clique in the cycle contains at most two vertices, so any clique cover needs at least **21 cliques**. Ignite the vertices **6, 18, 27, 33, 37, 39, 40** in that order, choosing one new source per round while fire spreads from the previously burning vertices. The entire cycle burns in **7 rounds**. Thus the proposed right side is at most 20, while the left side is at least 21.

## Lean verification

The theorem `violates_a1136330` checks the graph hypotheses and proves that the optimal burning and clique-cover numbers violate the stated inequality. The certificate uses the shared cycle definitions. [Lean certificate](Witness_a1136330.lean) · [Shared definitions](../../counterexamples/CycleCertificate.lean)

Run from the repository root with the pinned Lean toolchain in a POSIX shell.

```sh
proof_cache=$(mktemp -d)
(cd counterexamples && lean -o "$proof_cache/CycleCertificate.olean" CycleCertificate.lean)
LEAN_PATH="$proof_cache" lean proofs/agf-2618/Witness_a1136330.lean
```

[Proof index](../../README.md#proof-index) · [Search method and infinite family](../../counterexamples/README.md#an-infinite-family)
