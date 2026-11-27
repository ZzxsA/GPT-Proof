# A counterexample to Shu Liu's Conjecture 1

**ZzxsA and ChatGPT (OpenAI)**

Conjecture 1 of Shu Liu's *On Self-orthogonal MDS Codes* (arXiv v1, 23 November 2026) rules out a Euclidean self-orthogonal linear code of length $q+2$ and dimension 3 attaining the Singleton bound over every even prime-power field of order $q\ge4$. The following matrix generates a counterexample at $q=16$. [Conjecture 1 in the preprint](https://arxiv.org/html/2611.30048v1#S1.SS2)

## The generator matrix

Work over $\mathbf F_{16}=\mathbf F_2[t]/(t^4+t+1)$. An integer $b_0+2b_1+4b_2+8b_3$ denotes $b_0+b_1t+b_2t^2+b_3t^3$. Addition is bitwise XOR. Each line below is a row of $G$.

```text
15 13  5  9  2  1  1  1 12  1  1  1  1  1  1  1  0  0
 0 13 10  8  8  5  6  7 10  9 10 11 12 13 14 15  1  0
 0 13  2  2 12  7  2  3 13 10 12 13  9  8 15 14  0  1
```

* All six independent entries of the symmetric matrix $GG^{\mathsf T}$ vanish. For messages $u,v$, the Euclidean inner product of the words $uG,vG$ therefore equals $uGG^{\mathsf T}v^{\mathsf T}=0$.
* Every one of the $\binom{18}{3}=816$ three-column determinants is nonzero. Thus $G$ has rank 3, and a nonzero message cannot annihilate three columns. Every nonzero word has weight at least 16. The first row has weight exactly 16. Since $18-3+1=16$, the code is MDS.

The two conditions are sensitive to different aspects of the construction. The projective points are those of the classical Lunelli–Sce hyperoval. Multiplying columns by nonzero field elements preserves the nonzero-minor condition and can change the Gram matrix. The scalars used for the 16 affine columns (ordered by their second affine coordinate before scaling), followed by the two points at infinity, are

```text
15 13 5 9 2 1 1 1 12 1 1 1 1 1 1 1 1 1
```

One way to find the scalars is to give each unscaled column $p_i$ an unknown weight $w_i$ and solve the six linear equations $\sum_i w_i p_i p_i^{\mathsf T}=0$ with every $w_i$ nonzero. The required column scalars are the unique square roots of the weights in $\mathbf F_{16}$. Brown gives the underlying hyperoval polynomial in §2.3.2. [Brown, *(Hyper)ovals and ovoids in projective spaces*, p. 11](https://cage.ugent.be/~fdc/intensivecourse2/brown_2.pdf)

## Verification

Using the repository's pinned Lean 4.19.0 toolchain, run the following from this directory.

```sh
lean Liu16.lean
python3 verify_liu16.py
```

Lean checks that its finite-field multiplication table agrees with polynomial multiplication and reduction, that the matrix has 18 columns, that its Gram entries vanish, and that all its three-column minors are nonzero. It uses kernel reduction. The argument from these finite matrix facts to the parameters and Euclidean self-orthogonality is given above. The independent Python computation uses polynomial long division and also enumerates all $16^3=4096$ messages.

| Word weight | Number of messages |
|---:|---:|
| 0 | 1 |
| 16 | 2295 |
| 18 | 1800 |

## Related proof

The research note proves the general even-field classification, using classical results on hyperovals. Its all-field argument is a written mathematical proof. The finite certificate above covers the order-16 witness. [Classification by field size](https://github.com/ZzxsA/GPT-Proof/blob/cccb8382153a000584eba0db344a33d0fb0b21ce/proofs/liu-self-orthogonal-mds/CLASSIFICATION.md)

## Prior work

The underlying hyperoval dates to Lunelli and Sce (1958). Its ordinary $[18,3,16]$ MDS code also appears explicitly in the classification literature. The additional condition needed to refute Liu's conjecture is Euclidean self-orthogonality after choosing column scalars. A search on 27 November 2026 for the conjecture, parameters, Euclidean hulls, and hyperoval-code rescalings identified no earlier explicit Euclidean counterexample. Earlier work on the dual of a Schur square also gives the general method of testing diagonal scalings. Quantum CSS constructions using two mutually orthogonal codes and Hermitian self-orthogonality use different hypotheses. [Zhu and Liao](https://arxiv.org/abs/2201.02758) · [Ezerman, Jitman, Kiah and Ling, Theorem 5](https://doi.org/10.1142/S0219749913500275) · [Ball and Vilar](https://doi.org/10.1007/s00022-021-00619-x)

The result is an independently checkable refutation of v1. Historical priority remains open. [Brown](https://cage.ugent.be/~fdc/intensivecourse2/brown_2.pdf) · [Ball, Gamboa and Lavrauw](https://web.mat.upc.edu/simeon.michael.ball/smalladditiveAiM.pdf) · [Liu](https://arxiv.org/abs/2611.30048)
