# Zhi-Wei Sun · A362743, Conjecture 3

**Claim.** Fix integers k and m greater than one. When the product of the bases is even, every sufficiently large target in the stated domain can be written as a sum of terms kᵃ + mᵇ with nonnegative exponents and with no summand dividing another. [Original statement](https://oeis.org/A362743)

**Counterexamples.** Fix the bases at (4,16). For every integer L ≥ 1, the number 4ᴸ − 1 has no admissible representation. The proof groups terms by the difference of their exponents in a common base and counts the powers needed to fill the target's digits. This gives exceptions beyond every threshold.

[Proof of the infinite family](../shared/sun-antichain/PROOF.md) · [Lean theorem](A362743.lean) · [Shared Lean proof](../shared/sun-antichain/SunAntichain.lean) · [Independent finite check](../shared/sun-antichain/verify_sun.py)

To check this result with the repository's pinned Lean version, run the following from the repository root in a POSIX shell.

```sh
proof_cache=$(mktemp -d)
export LEAN_PATH="$proof_cache"
(cd proofs/shared/sun-antichain && lean -o "$proof_cache/DigitCost.olean" DigitCost.lean && lean -o "$proof_cache/SunAntichain.olean" SunAntichain.lean)
lean proofs/sun-a362743/A362743.lean
```
