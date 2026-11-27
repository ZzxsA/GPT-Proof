import BalaSeries
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Bala
open PowerSeries Finset

/-- Coefficient definition of F*exp(B) over the rationals for integral F,B
and B(0)=0. The s-th term has order at least s. -/
noncomputable def weightedExp (F B : PowerSeries ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ∑ s ∈ range (n+1), (coeff ℤ n (F * B^s) : ℚ) / (s.factorial : ℚ)

theorem factorial_coeff_exp (F G : PowerSeries ℤ) (n : ℕ) :
    (n.factorial : ℚ) * coeff ℚ n (weightedExp F (X * G^n)) =
      (scaledCoefficient F G n : ℚ) := by
  rw [weightedExp, coeff_mk]
  rw [← Finset.sum_range_reflect
    (fun s : ℕ => (coeff ℤ n (F * (X * G^n)^s) : ℚ) / (s.factorial : ℚ)) (n+1)]
  rw [Finset.mul_sum]
  unfold scaledCoefficient
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  have h : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  simp only [Nat.add_sub_cancel]
  have eqp : F * (X * G^n)^(n-j) = (F * G^(n*(n-j))) * X^(n-j) := by
    rw [mul_pow, pow_mul]
    ac_rfl
  rw [eqp, coeff_mul_X_pow', if_pos (by omega : n-j ≤ n), show n-(n-j)=j by omega]
  have he : ((n-j).factorial : ℚ) * (n.descFactorial j : ℚ) = (n.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial h
  have hz : ((n-j).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [← he]
  field_simp
  <;> ring

/-- The coefficient of the rational exponential is integral, and its integer
representative obeys Bala's congruence. -/
theorem exp_shift (F G : PowerSeries ℤ) (hG : constantCoeff ℤ G = 1) (n k : ℕ) :
    ∃ a b : ℤ,
      (a : ℚ) = ((n+k).factorial : ℚ) * coeff ℚ (n+k) (weightedExp F (X * G^(n+k))) ∧
      (b : ℚ) = (n.factorial : ℚ) * coeff ℚ n (weightedExp F (X * G^n)) ∧
      a ≡ b [ZMOD k] := by
  exact ⟨_, _, (factorial_coeff_exp F G (n+k)).symm, (factorial_coeff_exp F G n).symm,
    universal_shift F G hG n k⟩

#print axioms exp_shift
end Bala
