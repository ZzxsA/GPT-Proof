# A ten-vertex counterexample to the periphery bound

**ZzxsA and ChatGPT (OpenAI)**

In Table 15, row 2, Larson and Van Cleemput conjectured that an independence-irreducible graph satisfies $\alpha\ge |\mathrm{Per}|-\Delta-\operatorname{res}$. Here $\alpha$ is the independence number, $\mathrm{Per}$ is the set of vertices of maximum eccentricity, $\Delta$ is the maximum degree and $\operatorname{res}$ is the number of zeros left by the Havel–Hakimi reduction of the degree sequence. Independence-irreducibility means $|N(I)|>|I|$ for every nonempty independent set $I$. The authors report testing through ten vertices. The same row is numbered Table 16 in their preprint. [Published article](https://doi.org/10.1016/j.artint.2015.10.002) · [Authors' preprint, §8](https://math1um.github.io/Research/r21.pdf)

## Graph and proof

Take two complete graphs on five vertices and match corresponding vertices in different copies. At most one vertex in each copy belongs to an independent set, and two unmatched vertices in different copies form one. A singleton has five neighbors; an independent pair has eight. The graph is hence independence-irreducible and $\alpha=2$. Every vertex has degree 5 and has vertices at distance 2. Each unmatched pair across the two copies is connected by a two-edge walk, so every vertex has eccentricity 2. All ten vertices are peripheral. Havel–Hakimi yields residue 2. The conjecture would require $2\ge 10-5-2=3$.

For two matched cliques of equal order $m\ge5$, the same argument gives independence number 2, degree $m$, periphery $2m$, and neighborhoods of sizes $m$ and $2m-2$ for the two kinds of nonempty independent set. The theorem $\operatorname{res}\le\alpha$ gives a gap of at least $m-4$ above the true independence number in the conjectured lower bound. The gap is unbounded. This family calculation uses the classical residue theorem. [Favaron, Mahéo and Saclé (1991)](https://doi.org/10.1002/jgt.3190150107)

## Earlier data

The authors' project stored this graph in 2017 under the graph6 string `IJ]KlNF}?`. The same snapshot records the irreducibility flag and the four invariant values. In prism order the archive labels are `0,5,6,7,8,9,4,3,2,1`. The reproduction script verifies the relabeling against every pair of vertices. The archive therefore contains a counterexample in its data. We found no earlier explicit correction during this search. [Periphery row](https://github.com/math1um/objects-invariants-properties/blob/54a1dba21e377e20adb9239187a78c63eafe668f/db/invariants/card_periphery.sql#L134) · [Independence number](https://github.com/math1um/objects-invariants-properties/blob/54a1dba21e377e20adb9239187a78c63eafe668f/db/invariants/independence_number.sql#L134) · [Maximum degree](https://github.com/math1um/objects-invariants-properties/blob/54a1dba21e377e20adb9239187a78c63eafe668f/db/invariants/max_degree.sql#L134) · [Residue](https://github.com/math1um/objects-invariants-properties/blob/54a1dba21e377e20adb9239187a78c63eafe668f/db/invariants/residue.sql#L134) · [Irreducibility](https://github.com/math1um/objects-invariants-properties/blob/54a1dba21e377e20adb9239187a78c63eafe668f/db/properties/is_independence_irreducible.sql#L134)

## Verification and minimum order

Lean verifies the ten-vertex counterexample from the adjacency relation. A separate exhaustive Python check calls nauty's `geng -cq` and tests one representative of every connected simple graph of orders 1 through 9. The counts by order are 1, 1, 2, 6, 21, 112, 853, 11,117 and 261,080. None of these 273,193 graphs violates the conjecture. Thus ten is the smallest order among connected simple counterexamples. This minimality result depends on the nauty enumeration and Python checker. The general family argument appears above in prose.

From this directory, with the pinned Lean toolchain and nauty installed, run

```sh
export LEAN_PATH="$(mktemp -d)"
lean -o "$LEAN_PATH/RookTenIndependent.olean" RookTenIndependent.lean
lean Prism.lean
python3 verify_graph.py
python3 verify_graph.py --census nauty-geng
```
