# Two conjectures on sums with no summand dividing another

**ZzxsA and ChatGPT (OpenAI)**

Zhi-Wei Sun posed both questions in May 2023. Fix integers k,m greater than one. An admissible representation is a finite sum of numbers of the form kᵃ + mᵇ, where a and b are nonnegative integers and no summand divides any other summand. In particular a summand cannot be used twice.

| Original statement | Bases | Arbitrarily large exceptions |
|---|---|---|
| If km is even, every sufficiently large integer has an admissible representation. | k = 4, m = 16 | 4ᴸ − 1, for every L ≥ 1 |
| If both bases are odd, every sufficiently large even integer has an admissible representation. | k = 5, m = 25 | 5ᴸ − 1, for every L ≥ 1 |

Both statements are numbered **Conjecture 3** in the comments of their respective OEIS entries. The counterexamples concern this general assertion. Conjectures 1 and 2 in those entries impose different conditions. [A362743](https://oeis.org/A362743) · [A362861](https://oeis.org/A362861)

## Proof

Fix integers q ≥ 4 and L ≥ 1. Take bases q and q². Each allowed term is a sum of two powers of q, say qⁱ + qʲ. After ordering the exponents, write it as qʰ(1 + qᵈ), with h the smaller exponent and d their difference.

Suppose that some admissible sum equals qᴸ − 1. Both exponents in every term must be less than L, since a power of exponent at least L already exceeds the target. Therefore the only possible differences are 0 through L − 1. Any two terms with the same difference are comparable by divisibility: the one with smaller h divides the other. Hence at most L summands occur.

Those summands provide at most 2L powers of q in total. Adding one power contributes at most one to the sum of the base-q digits. Every carry replaces q units at one position by one unit at the next, reducing the digit sum by q − 1. The resulting digit sum is therefore at most 2L. But qᴸ − 1 has L digits all equal to q − 1, giving digit sum (q − 1)L > 2L. This contradiction proves the obstruction for every L.

At q = 4 the product of the bases is even. At q = 5, both bases are odd and 5ᴸ − 1 is always even. The exceptions in each row exceed any fixed threshold by taking L sufficiently large.

For a numerical check, take q = 4 and L = 3. The target is 63, written 333 in base four. Its digit sum is 9, whereas at most three admissible summands could contribute at most six powers of four.

## Verification and provenance

The Lean development derives the digit bound from division into powers of the base, proves the general obstruction, and instantiates the threshold quantifiers and parity conditions in both OEIS conjectures. An independent Python program tests small targets directly. The mathematical proof establishes the infinite families.

A362743 revision 16, dated May 2, 2023, allowed every pair of bases greater than one. Revision 22, dated May 6, added the even-product condition. The bases 4 and 16 satisfy this condition. [May 2 wording, revision 16](https://github.com/oeis/oeisdata/blob/7e45c6ddfc7eb4b7cfc665a2ae0c0d3d975af266/seq/A362/A362743.seq) · [May 6 wording, revision 22](https://github.com/oeis/oeisdata/blob/f98dbe962d868d86e0710e56a738dcfca0f2b849/seq/A362/A362743.seq)

A search of the current OEIS entries, their available revisions, and public material indexed by identifier and statement found no earlier explicit counterexample to either current conjecture as of November 27, 2026. The paper cited by Sun considers products of powers as summands. [Erdős and Lewin](https://doi.org/10.1090/S0025-5718-96-00707-7)
