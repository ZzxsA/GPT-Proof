import Bala
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Sum

/-! Bala's coefficient theorem for arbitrary integral formal power series. -/
namespace Bala
open PowerSeries Finset

def coeffArray (F G : PowerSeries ℤ) (j i : ℕ) : ℤ :=
  coeff ℤ j (F * (G - 1)^i)

private theorem array_zero (F G : PowerSeries ℤ) (hG : constantCoeff ℤ G = 1)
    {i j : ℕ} (h : j < i) : coeffArray F G j i = 0 := by
  have hd : (X : PowerSeries ℤ) ∣ G - 1 := X_dvd_iff.mpr (by simp [hG])
  exact X_pow_dvd_iff.mp (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hd i) F) j h

private theorem series_binomial (F G : PowerSeries ℤ) (u j : ℕ) :
    coeff ℤ j (F * G^u) = ∑ i ∈ range (u+1), coeffArray F G j i * (u.choose i : ℤ) := by
  conv_lhs => rw [show G^u = ((G-1)+1)^u by simp, add_pow]
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [one_pow, mul_one, coeffArray, ← mul_assoc]
  rw [show (u.choose i : PowerSeries ℤ) = C ℤ (u.choose i : ℤ) by simp]
  exact coeff_mul_C j _ _

private theorem series_binomial_cut (F G : PowerSeries ℤ) (hG : constantCoeff ℤ G = 1)
    (u j : ℕ) :
    coeff ℤ j (F * G^u) = ∑ i ∈ range (j+1), coeffArray F G j i * (u.choose i : ℤ) := by
  rw [series_binomial]
  by_cases hu : u ≤ j
  · apply Finset.sum_subset (Finset.range_mono (by omega : u+1 ≤ j+1))
    intro i _ hi
    have hut : u < i := by
      simp only [Finset.mem_range, not_lt] at hi
      omega
    simp [Nat.choose_eq_zero_of_lt hut]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega : j+1 ≤ u+1))
    intro i _ hi
    have hji : j < i := by
      simp only [Finset.mem_range, not_lt] at hi
      omega
    simp [array_zero F G hG hji]

/-- Integral form of n! [x^n] F(x) exp(x G(x)^n), obtained by expanding
the exponential and reindexing its summand with j = n-s. -/
def scaledCoefficient (F G : PowerSeries ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ range (n+1), (n.descFactorial j : ℤ) * coeff ℤ j (F * G^(n*(n-j)))

theorem scaled_eq_diagonal (F G : PowerSeries ℤ) (hG : constantCoeff ℤ G = 1) (n : ℕ) :
    scaledCoefficient F G n = diagonal (coeffArray F G) n := by
  unfold scaledCoefficient diagonal
  apply Finset.sum_congr rfl
  intro j _
  rw [series_binomial_cut F G hG, Finset.mul_sum]
  unfold inner
  apply Finset.sum_congr rfl
  intro i _
  simp [kernel, mul_left_comm, mul_assoc, mul_comm]

theorem universal_shift (F G : PowerSeries ℤ) (hG : constantCoeff ℤ G = 1) (n k : ℕ) :
    scaledCoefficient F G (n+k) ≡ scaledCoefficient F G n [ZMOD k] := by
  simpa only [scaled_eq_diagonal F G hG] using diagonal_shift (coeffArray F G) n k

#print axioms universal_shift
end Bala
