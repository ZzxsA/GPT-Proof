# GPT-Proof

**ZzxsA and ChatGPT (OpenAI)**

## Counterexample search

The daily graph search checks published conjecture statements against explicit finite graphs and emits Lean certificates for hits. The first three witnesses are cycles on 23, 33 and 41 vertices. Each refutes a different numbered proposal from AutoGraphForge. The repository records the original hypotheses and the evidence for each failure. [Statements, witnesses and reproduction commands](counterexamples/README.md) · [Search runs](https://github.com/ZzxsA/GPT-Proof/actions/workflows/counterexamples.yml)

## The Harkness period conjecture

For a prime exponent $n\ge 5$, consider the binary sequence that records whether consecutive differences of $n$th powers are coprime. Write $a(n)$ for its least positive period. Samuel Harkness conjectured that the largest prime factor of $a(n)$ equals $J_n=(2^n+1)/3$. [Original conjecture, OEIS A353890](https://oeis.org/A353890)

The first counterexample is **$n=29$**. The prediction is $178956971=59\cdot3033169$, whereas the largest prime factor of the actual period is **108050869**. More generally, every prime factor of $a(n)$ is at most $J_n$, with equality attained if and only if $J_n$ is prime. The factorization of $J_{29}$ was recorded before the conjecture. [Proof and exact period](PROOF.md) · [Earlier factorization, OEIS A250291](https://oeis.org/A250291)

## Reproduce the calculation

Run either of the following with Python 3.8 or later. Both use only the standard library.

```sh
python verify_harkness.py
python harkness_independent.py
```

The first program computes integer determinants, factors them by trial division, and produces a modular witness for each prime. The second computes the same resultants by polynomial division over the rationals. Both programs check all seven smaller prime exponents in the conjecture's domain and report the same 17 prime factors of $a(29)$.

## Check the Lean proof

From the repository root, using the version pinned in `lean-toolchain`, run

```sh
lean HarknessPeriod.lean
```

The theorem `Harkness.conjecture_false` refutes the universal conjecture. The file also gives an explicit congruence for three consecutive 29th powers. The general characterization and the proof connecting the computed primes to the least period are given in [PROOF.md](PROOF.md).
