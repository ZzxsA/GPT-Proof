# A missing case in a statement on MDS code intersections

Huang, Fang and Fu's Theorem 4 in the July 2021 preprint asserts existence of a pair of length-`q+1` linear MDS codes of dimensions `k1,k2` with intersection dimension `l`, under the displayed dimension bounds and the condition that at least one of `l,k1-l,k2-l` equals one. The two triples explicitly excluded are `(1,2,1)` and `(2,1,1)`. The journal article appeared in 2022. The general existence statement with those same two exceptions was repeated in the 2026 paper by Zheng, Huang and Zhu. The theorem number here refers to the preprint. [Preprint, Theorem 4, p. 8](https://arxiv.org/pdf/2107.04166) · [2022 journal article](https://doi.org/10.1007/s12095-022-00582-7) · [2026 restatement](https://doi.org/10.1016/j.ffa.2025.102758)

At `q=3` and `(k1,k2,l)=(2,3,2)`, all stated hypotheses hold. An intersection of dimension two equals the smaller code. Such a containment would dualize to a full-support ternary `[4,1,4]` subcode of a `[4,2,3]` MDS code. The four columns of any generator of the latter give four distinct points of the projective line over `F₃`. They exhaust that line, so every nonzero row combination vanishes in exactly one coordinate. This proves the required nonexistence. The original paper itself gives the corresponding obstruction for its expressly excluded primal triple.

## A family beyond the dual exceptions

For every odd prime power `q≥5`, the same triple `(2,3,2)` also gives a counterexample. Suppose a `[q+1,2,q]` MDS code lies in a `[q+1,3,q-1]` MDS code. Choose rows generating the larger code with the first two a basis for the smaller. Append the column `(0,0,1)ᵀ`. Every triple of old columns is linearly independent by the larger MDS condition. Every triple containing the new column is independent because its minor is a two-column minor for the smaller MDS code. The resulting `q+2` columns give distinct points of `PG(2,q)` with no three collinear.

Each of the `q+1` lines through a point in this set contains a different one of its `q+1` other points. Thus every line meeting the set meets it twice. The lines through any point outside the set partition its `q+2` elements into pairs, impossible for odd `q`. This is the classical obstruction to hyperovals in odd order. The same argument applies at `q=3`, where duality also suffices. [Alderson, *Extending MDS Codes*](https://www.unb.ca/faculty-staff/directory/_resources/pdf/sase/alderson/mds-codes.pdf)

The lengthening argument applies to any pair of nested, consecutive-dimensional MDS codes. Conversely, shortening and puncturing an MDS code in the same coordinate produces such a pair. Consequently the proposed existence for adjacent nested dimensions at length `q+1` would force MDS length `q+2` in those dimensions. The geometric obstruction and this extension principle are classical. Searches by author, DOI, parameters and the extension principle did not identify an earlier explicit correction of this theorem. Priority has not been established.

## Lean and independent finite computation

`HuangFangFu.lean` formalizes the ternary instance using arbitrary linear codes as membership predicates on `F₃⁴` closed under linear combinations. The theorem `HuangFangFu.no_nested_mds` excludes containment of any qualifying pair. For the minimum-distance condition, the zero word is allowed and each nonzero codeword must have the claimed minimum Hamming weight or higher. For the dimension condition, projection onto the first `k` coordinates must be surjective. Any `[n,k,n-k+1]` linear code satisfies both conditions because a word zero in its first `k` positions has weight at most `n-k` and hence must vanish. This makes the projection injective, and both spaces have `q^k` elements. Conversely those two formal conditions give precisely dimension `k` and exact distance `n-k+1` by the Singleton bound.

The proof selects two systematic words from the smaller code and a third pivot word from the larger one. The remaining five entries take values in `F₃`. Lean's `decide` checks that the corresponding minimum-distance requirements conflict. The universal odd-order argument above is a mathematical proof on paper.

```
lean HuangFangFu.lean
python verify_hff.py
```

The Python program constructs every systematic ternary generator and finds eight `[4,2,3]` and eight `[4,3,2]` codes with zero nested pairs. It also checks all 15,625 normalized candidates for an ordered 7-arc in `PG(2,5)` and finds none. Normalization takes the first three independent points to the coordinate axes and the fourth to `(1,1,1)`. Each of the remaining points then has nonzero last coordinate and can be represented by `(x,y,1)`.
