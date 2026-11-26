# Counterexample search

**ZzxsA and ChatGPT (OpenAI)**

The first campaign tests graph conjectures proposed by Ján Pastorek's AutoGraphForge. Each catalog entry links to the statement at a fixed upstream commit. Python finds a graph and produces a witness. Lean checks the mathematical certificate. Historical priority requires a separate literature search. [Upstream project](https://github.com/JanPastorek/AutoGraphForge) · [Daily runs and downloadable artifacts](https://github.com/ZzxsA/GPT-Proof/actions/workflows/counterexamples.yml)

## The first three witnesses

Here θ is the minimum number of cliques covering all vertices. A clique is a set of pairwise adjacent vertices. The burning number b is the minimum number of rounds needed to burn the graph. In each round, choose one vertex that was unburned at the end of the preceding round. Ignite it while fire spreads from all previously burning vertices to their neighbors.

| Original proposal | Domain (all graphs here are nontrivial) | Claimed bound | Witness | Certified bounds |
|---|---|---|---|---|
| [1656 · c5b13d43](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1606) | Claw-free regular | θ ≤ 3b − 4 | C₂₃ | θ ≥ 12, b ≤ 5 |
| [2256 · 31b3af5f](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2194) | Maximum degree at most three | θ ≤ 3b − 2 | C₃₃ | θ ≥ 17, b ≤ 6 |
| [2618 · a1136330](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2553) | Eulerian | θ ≤ 2b + 6 | C₄₁ | θ ≥ 21, b ≤ 7 |

For the first witness, label the cycle from 0 to 22 and ignite vertices 4, 12, 18, 21 and 22 in that order. At the end of round five their fires cover vertices 0–8, 9–15, 16–20, 20–22 and 22, respectively. Every clique contains at most two vertices, so covering 23 vertices requires at least 12 cliques. The conjecture gives at most 11. The proof only needs these one-sided bounds. The other rows give the contradictions 17 > 16 and 21 > 20. The table gives the first violating cycle for each proposal, with no claim about the smallest graph among all graph classes.

The three complete generated Lean files are committed with the project. Each `violates_` theorem asserts existence of the two optimal values and gives a strict inequality in the direction opposite the proposal. [23-vertex witness](examples/Witness_c5b13d43.lean) · [33-vertex witness](examples/Witness_31b3af5f.lean) · [41-vertex witness](examples/Witness_a1136330.lean)

## An infinite family

Every cycle on k² vertices, for integer k ≥ 7, refutes all three proposals simultaneously. The published formula for cycles gives b = k. Every clique contains at most two vertices, so θ ≥ k²/2. For k ≥ 7, we have k²/2 ≥ 7k/2, and 7k/2 exceeds both 3k − 2 and 2k + 6. The first bound, 3k − 4, is smaller still. This general argument uses the literature result. The three individual Lean certificates above check concrete schedules directly. [Bonato, Janssen and Roshanbin, *How to Burn a Graph*, Corollary 10(1)](https://math.ryerson.ca/~abonato/papers/Burning-IM-revised4.pdf#page=7)

## Reproduce a run

Use Python 3.10+ and the Lean version in the repository's `lean-toolchain`. Run these commands from the repository root. Choose fresh output directories.

```sh
python -m unittest discover -s counterexamples -p 'test_*.py'
python counterexamples/search.py --start 4 --count 46 --output results/cycles
python counterexamples/degree_search.py --seed 20261126 --graphs 200 --output results/degree
```

To verify both modules and the generated witnesses with Lean, use the following commands in a POSIX shell from the same directory.

```sh
mkdir -p results/olean
export LEAN_PATH="$PWD/results/olean"
(cd counterexamples && lean -o "$LEAN_PATH/CycleCertificate.olean" CycleCertificate.lean)
(cd counterexamples && lean -o "$LEAN_PATH/DegreeCertificate.olean" DegreeCertificate.lean)
(cd results/cycles && for f in Witness_*.lean; do lean "$f" || exit $?; done)
(cd results/degree && lean DegreeWitnesses.lean)
```

## What runs each day

The workflow is scheduled for 04:23 UTC. It samples 200 connected graphs on 4–12 vertices, also checks fixed graph families, and tests 19 sourced affine inequalities in graph invariants, including degree, clique number and vertex cover number. The run records the seed and exact source revision so the search can be replayed. A run with no counterexamples records that outcome. The run always rechecks the first cycle witness and a separately labelled synthetic inequality on the complete graph K₄. The synthetic inequality is excluded from all discovery counts.

The cycle search separately covers orders 4–49 in the initial run. Beginning November 27, 2026 it checks one further order per UTC day through 96. Later runs continue sampling general graphs. The same conjecture may fail on many graphs. Larger witnesses for an already refuted proposal do not count as new refutations. Missed cycle orders can be rerun with the manual workflow inputs.

Each run has an artifact with its plan, catalog, generated certificates and logs, retained for 30 days. A successful verification step means Lean accepted all the certificates generated during that run. Failure logs are also available in artifacts labelled `failure`.

## Refresh the catalog

`catalog.json` records the three burning proposals. `degree_catalog.json` is generated from the complete normalized candidate list at the linked commit. The importer accepts only graph predicates and graph invariants supported by the verifier. For the initial snapshot, the following command reproduces the committed degree catalog from the original UTF-8 source bytes.

```sh
python counterexamples/import_catalog.py --snapshot survivors_by_touch_normalised.txt \
  --revision 4d1a8afc99447cacd2328cca20e47b6493e8dbc5 \
  --expect-blob 11d0dd0f999791efeab05b043d805fcf3bd33e99 \
  --output results/degree_catalog.json
```

When adding a candidate, preserve its exact source statement, translate all premises, and check the generated theorem against the original inequality. Before reporting a discovery, look for earlier counterexamples on *any* graph in the stated domain. [Pinned candidate list](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt)
