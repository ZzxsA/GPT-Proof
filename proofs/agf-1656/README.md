# AutoGraphForge #1656 · Claw-free regular graphs

**Conjecture.** Every nontrivial claw-free regular graph satisfies **θ ≤ 3b − 4**. Here θ is the fewest cliques needed to cover all vertices, and b is the fewest rounds needed to burn the graph. A graph is nontrivial if it has at least two vertices. AutoGraphForge records this proposal under ID `c5b13d43`. [Original statement](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1606)

## Counterexample

Take the cycle on **23 vertices**, numbered from 0 to 22. Every vertex on this cycle has degree two. All degrees are equal, and an induced claw would require a vertex with at least three neighbors.

Every clique in the cycle contains at most two vertices, so any clique cover needs at least **12 cliques**. Ignite the vertices **4, 12, 18, 21, 22** in that order, choosing one new source per round while fire spreads from the previously burning vertices. The entire cycle burns in **5 rounds**. Thus the proposed right side is at most 11, while the left side is at least 12.

## Lean verification

The theorem `violates_c5b13d43` checks the graph hypotheses and proves that the optimal burning and clique-cover numbers violate the stated inequality. The certificate uses the shared cycle definitions. [Lean certificate](Witness_c5b13d43.lean) · [Shared definitions](../../counterexamples/CycleCertificate.lean)

Run from the repository root with the pinned Lean toolchain in a POSIX shell.

```sh
proof_cache=$(mktemp -d)
(cd counterexamples && lean -o "$proof_cache/CycleCertificate.olean" CycleCertificate.lean)
LEAN_PATH="$proof_cache" lean proofs/agf-1656/Witness_c5b13d43.lean
```

[Proof index](../../README.md#proof-index) · [Search method and infinite family](../../counterexamples/README.md#an-infinite-family)
