# Harkness period conjecture · OEIS A353890

For prime $n\ge5$, let $D_n(m)=(m+1)^n-m^n$. Record a 1 at position $m$ if $D_n(m)$ and $D_n(m+1)$ are coprime, and a 0 otherwise. Write $a(n)$ for the least positive period of this binary sequence. Samuel Harkness conjectured that the largest prime factor of $a(n)$ equals $J_n=(2^n+1)/3$. [Original conjecture](https://oeis.org/A353890)

## Counterexample

At **$n=29$**, the prediction is $J_{29}=178956971=59\cdot3033169$. A composite number cannot equal a prime factor. The Lean theorem `Harkness.conjecture_false` formalizes this contradiction. The factorization itself predates the conjecture. [Lean proof](HarknessPeriod.lean) · [Earlier factorization, OEIS A250291](https://oeis.org/A250291)

The mathematical proof shows that the largest prime factor of $a(n)$ equals $J_n$ exactly when $J_n$ is prime. It follows that 29 is the first counterexample. Two independent exact computations give **108050869** as the actual largest prime factor of $a(29)$. One uses integer determinants and the other uses polynomial remainders over the rationals. [Full proof and exact period](PROOF.md) · [Integer computation](verify_harkness.py) · [Polynomial computation](harkness_independent.py)

## Reproduce

From the repository root, use the pinned Lean toolchain and Python 3.8 or later.

```sh
lean proofs/harkness-period/HarknessPeriod.lean
python proofs/harkness-period/verify_harkness.py
python proofs/harkness-period/harkness_independent.py
```

[Proof index](../../README.md#proof-index)
