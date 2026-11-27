# More geodesics than the uniform three-vertex layers

Knor, Sedlar, Škrekovski and Zhang ask in Problem 14 for a graph family with more geodesics than their construction on equally many vertices. On every order $3m+6$, $m\ge1$, the construction below has exactly $10\cdot3^m-15$ more geodesics. Its asymptotic ratio to their construction is $121/81$. This answers the construction part of Problem 14. The maximum over all graphs remains open. [Published problem, §4](https://doi.org/10.1007/s00009-026-03159-3) · [April 2026 preprint](https://arxiv.org/abs/2604.04907)

## Construction and a short proof of asymptotic improvement

For a list of positive integers, form independent vertex sets of those sizes in the listed order. Join every vertex in each set to every vertex in the next set. These are all the edges. The resulting graph is simple and connected. Write $U_m$ for the graph with $m+2$ layers of size three and $H_m$ for the graph with layers

$$
1,\;2,\;\underbrace{3,\ldots,3}_{m},\;2,\;1.
$$

The authors write $U_m=G_{3,m+2}$ and count one geodesic of length zero per vertex. Paths traversed in opposite directions are counted once. Their Proposition 3 gives $\operatorname{gpn}(U_m)\sim(9/4)3^{m+2}$. [Definitions and Proposition 3](https://link.springer.com/article/10.1007/s00009-026-03159-3#Sec2)

Choose one vertex from each central layer. At each end of this central path, choose independently among five extensions. One can stop, append either vertex of the neighboring two-vertex layer, or append either such vertex followed by the terminal singleton. Each resulting path meets successive layers in order, hence has the least possible length between its endpoints. Its vertices recover the central choice and both extensions. For $m=1$, stopping on both sides contributes the singleton path at the chosen central vertex. We obtain

$$
\operatorname{gpn}(H_m)\ge25\cdot3^m
=\frac{25}{9}\,3^{m+2}.
$$

Since $25/9>9/4$, these paths alone improve the benchmark's leading coefficient. The nine-vertex instance $H_1$ has 105 geodesics and $U_1$ has 90.

## Exact count

Consider a graph with $s\ge2$ layers of sizes $a_1,\ldots,a_s$. A path with endpoints in layers $i<j$ is shortest exactly when it uses one vertex in each layer from $i$ through $j$, in order. Thus those two endpoint layers contribute $\prod_{k=i}^j a_k$ paths altogether. Two distinct vertices in layer $i$ have distance two and have $a_{i-1}+a_{i+1}$ common neighbors, with $a_0=a_{s+1}=0$. Adding the singleton paths gives

$$
\operatorname{gpn}
=\sum_i a_i
+\sum_{i<j}\prod_{k=i}^j a_k
+\sum_i {a_i\choose 2}(a_{i-1}+a_{i+1}).
$$

For $H_m$, a cap consists of one terminal singleton and its adjacent two-vertex layer. The following contributions partition the geodesics.

| Endpoints | Number |
| --- | ---: |
| Same vertex | $3m+6$ |
| Distinct vertices in the same layer | $18m+2$ |
| Distinct central layers | $\sum_{d=1}^{m-1}(m-d)3^{d+1}=(9\cdot3^m-18m-9)/4$ |
| One in a cap and one central | $8\sum_{j=1}^m3^j=4(3^{m+1}-3)$ |
| Both in one cap, in different layers | $4$ |
| One in each cap | $16\cdot3^m$ |

For the second row, the two size-two layers contribute eight. In the central layers each layer contributes three vertex pairs. Their adjacent layer sizes sum to $6m-2$ across all central layers, including when $m=1$. For the fourth row the two cap layers contribute $2+1\cdot2=4$ choices on each side of the graph. The last row uses both such factors.

Summing the rows, then substituting $k=3,t=m+2$ into the authors' Proposition 3, gives

$$
\begin{aligned}
4\operatorname{gpn}(H_m)&=121\cdot3^m+66m-9,\\
4\operatorname{gpn}(U_m)&=81\cdot3^m+66m+51.
\end{aligned}
$$

Consequently $\operatorname{gpn}(H_m)-\operatorname{gpn}(U_m)=10\cdot3^m-15>0$ for every $m\ge1$. In terms of the common order $n=3m+6$, the leading coefficient of $3^{n/3}$ increases from $9/4$ to $121/36$.

## Prior work and independent verification

The original authors already use nonuniform layers in their proof of Theorem 2. Claim D optimizes the number of geodesics *starting at one specified vertex* and explicitly compares terminal size patterns including $(3,2,1)$. Here the comparison concerns the total over all endpoints and places the $(2,1)$ layers at both ends. The publication formulates this comparison as an open problem. Earlier work by Varghese, Lakshmanan and Arumugam studies counts of positive-length geodesics under the name *geodesic path number*. Stephen, Wilfred and Abraham also investigate this count for complete bipartite graphs. For example $K_{4,5}$ already gives a finite improvement at order nine, with 99 geodesics in the convention above. The asymptotic comparison is the contribution of this construction. A search by the DOI, arXiv identifier and both names for the invariant found no prior publication giving this improvement. Priority is unconfirmed. [Original Theorem 2 and Problem 14](https://doi.org/10.1007/s00009-026-03159-3) · [Varghese et al., 2022](https://doi.org/10.1080/09728600.2022.2084354) · [Stephen et al., 2026](https://jidmis.org/index.php/jidmis/article/view/3232)

Yu and Zhu determine the largest number of shortest paths between a single pair with a prescribed distance and a bound on maximum degree. Their result addresses a distinct optimization problem. [Yu and Zhu, 2026](https://arxiv.org/abs/2609.02334)

Run `python verify_geodesics.py` from this directory. The verifier builds both graphs from their edges and counts shortest paths with breadth-first search from each vertex. It checks the exact formulas and the short lower bound for $1\le m\le20$.

The finite Lean proof counts shortest paths directly from the edges. The family module constructs distinct shortest paths for every positive m and proves the lower bound of 25·3ᵐ. The exact formula is derived above. [Finite graph certificates](Geodesics.lean) · [General construction](LayerFamily.lean)

Run from the repository root with the pinned Lean version.

```sh
lean proofs/knor-geodesics-14/Geodesics.lean
lean proofs/knor-geodesics-14/LayerFamily.lean
python proofs/knor-geodesics-14/verify_geodesics.py
```
