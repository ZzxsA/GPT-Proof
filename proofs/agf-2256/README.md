# AutoGraphForge #2256 · Graphs of maximum degree three or less

**Conjecture.** Every nontrivial graph of maximum degree at most three satisfies **θ ≤ 3b − 2**. Here θ is the fewest cliques needed to cover all vertices, and b is the fewest rounds needed to burn the graph. A graph is nontrivial if it has at least two vertices. AutoGraphForge records this proposal under ID `31b3af5f`. [Original statement](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2194)

## Counterexample

Take the cycle on **33 vertices**, numbered from 0 to 32. Every vertex on this cycle has degree two, so the maximum degree is at most three.

Every clique in the cycle contains at most two vertices, so any clique cover needs at least **17 cliques**. Ignite the vertices **5, 15, 23, 28, 31, 32** in that order, choosing one new source per round while fire spreads from the previously burning vertices. The entire cycle burns in **6 rounds**. Thus the proposed right side is at most 16, while the left side is at least 17.

## Lean verification

The theorem `violates_31b3af5f` checks the graph hypotheses and proves that the optimal burning and clique-cover numbers violate the stated inequality. The certificate uses the shared cycle definitions. [Lean certificate](Witness_31b3af5f.lean) · [Shared definitions](../../counterexamples/CycleCertificate.lean)

Run from the repository root with the pinned Lean toolchain in a POSIX shell.

```sh
proof_cache=$(mktemp -d)
(cd counterexamples && lean -o "$proof_cache/CycleCertificate.olean" CycleCertificate.lean)
LEAN_PATH="$proof_cache" lean proofs/agf-2256/Witness_31b3af5f.lean
```

[Proof index](../../README.md#proof-index) · [Search method and infinite family](../../counterexamples/README.md#an-infinite-family)
