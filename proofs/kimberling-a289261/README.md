# Strict increase of OEIS A289261

**ZzxsA and ChatGPT (OpenAI)**

For every $n\ge0$, the coefficients satisfy $a_{n+1}>a_n$, where
$$
  \sum_{n\ge0} a_n x^n =
  \left(\sum_{j\ge0}(-1)^j\left\lfloor13(j+1)/8\right\rfloor x^j\right)^{-1}.
$$
Clark Kimberling posed the strict-increase conjecture on July 14, 2017. Colin Barker supplied a rational generating function on the same date and a table through index 1000. The proof uses his generating function and verifies its connection to the defining floor sequence. [OEIS A289261](https://oeis.org/A289261)

## Proof

Write $d_n=a_{n+1}-a_n$. Barker's rational expression has numerator $(1+x)(1-x^8)$ and denominator
$$
  1-2x+x^2-2x^3+2x^4-x^5+2x^6-2x^7.
$$
The floor identity $\lfloor13(n+8)/8\rfloor=\lfloor13n/8\rfloor+13$ verifies this expression coefficient by coefficient. Combining successive instances of the resulting recurrence gives, for $n\ge3$,
$$
  d_{n+7}=2a_n+d_{n+2}+2d_{n+3}+2d_{n+4}+d_{n+5}.
$$
The first eleven coefficients are $1,3,5,9,17,30,52,91,160,281,494$. Induction now proves $a_n>0$ and $d_n>0$ together.

## Reproduce

From the repository root, using the version in the repository's Lean toolchain file, run

~~~sh
cd proofs/kimberling-a289261
lean Kimberling.lean
python3 verify_kimberling.py
~~~

The theorem `Kimberling.is_reciprocal` identifies the sequence defined in Lean by multiplying the two series. The theorem `Kimberling.a289261_strict` establishes strict increase at every index. The Python calculation independently inverts the original floor series through index 1000 and checks the difference identity wherever applicable.
