# Kimberling's interval for strict increase

Let \(1\le r<2\), and define \(a_n\) by
\[
G_r(x)=\sum_{j\ge0}(-1)^j\lfloor(j+1)r\rfloor x^j,
\qquad A_r(x)=1/G_r(x)=\sum_{n\ge0}a_nx^n.
\]
Then \(a_{n+1}>a_n\) at every index **if and only if** \(3/2\le r<5/3\). In this interval \(a_0=1\), so every coefficient is positive. Taking \(r=(1+\sqrt5)/2\) proves sign alternation for the reciprocal in Kimberling's original question, which uses \(G_r(-x)\).

Kimberling asked the golden-ratio sign question in December 2016. Gro-Tsen proposed the interval in a January 2017 comment based on numerical evidence. Kimberling recorded the stronger strict-increase and ratio-limit questions in OEIS in July 2017. The January 2017 discussion of the ratio identifies candidate roots and rational examples. The entries and discussions linked here give the prior observations for this proof. [Original sign question](https://mathoverflow.net/questions/258155/a-question-about-the-golden-ratio-and-other-numbers) · [Ratio question](https://mathoverflow.net/questions/259821/another-question-about-the-golden-ratio-and-other-numbers) · [OEIS A078140](https://oeis.org/A078140)

## Proof

Set \(D=(1+x)G_r\). Over the proposed interval its first four coefficients are \(1,-2,1,-2\). Each later coefficient is a signed difference of consecutive floors, whose unsigned increments are \(1\) or \(2\). Define \(D^*\) to agree through degree 3 and thereafter have even coefficients \(2\) and odd coefficients \(-1\). Thus \(E=D^*-D\) has nonnegative coefficients and zero constant term. Direct multiplication gives
\[
(1-x^2)D^*=(1-x-x^2)(1-x-x^3).
\]
Consequently
\[
\frac{1-x}{D^*}
=\left(1+\frac{x}{1-x-x^2}\right)
 \left(1+\frac{x^3}{1-x-x^3}\right)
\]
has strictly positive coefficients at every degree. Division by \(1-x\) shows that \(1/D^*\) also has positive coefficients. Since
\[
 (1-x)A_r=(1+x)\frac{1-x}{D^*}
             \sum_{j\ge0}\left(\frac{E}{D^*}\right)^j ,
\]
its coefficients are strictly positive. For degree \(n+1\) this coefficient is \(a_{n+1}-a_n\).

For \(1\le r<3/2\), one has \(a_1=2\) and \(a_2=4-\lfloor3r\rfloor\le1\). For \(5/3\le r<2\), one has \(a_1=3\), \(a_2=4\), and \(a_3=\lfloor4r\rfloor-3\le4\). These verify both endpoints of the classification.

## Lean verification

`KimberlingReal.coefficients_are_reciprocal` checks the defining convolution. The theorems `KimberlingReal.coefficients_strict` and `KimberlingReal.strictlyIncreasing_iff` state the positive-coefficient conclusion and the full classification. `KimberlingFamily.strictlyIncreasing` supplies the integer coefficient argument for the comparison series. These Lean theorems cover monotonicity. The analytic ratio-limit proof is given separately.

From the repository root, in a shell with Lean 4.19.0 and a built mathlib4 v4.19.0 checkout, set `MATHLIB` to its absolute path and run

~~~sh
export mods=$(mktemp -d)
cp proofs/kimberling-a289261/Kimberling.lean "$mods/"
cp proofs/kimberling-a078140/{KimberlingFamily,KimberlingReal}.lean "$mods/"
(
  cd "$MATHLIB"
  lake env bash -ec '
    export LEAN_PATH="$mods:$LEAN_PATH"
    lean --root="$mods" -o "$mods/Kimberling.olean" "$mods/Kimberling.lean"
    lean --root="$mods" -o "$mods/KimberlingFamily.olean" "$mods/KimberlingFamily.lean"
    lean --root="$mods" "$mods/KimberlingReal.lean"
  '
)
~~~
