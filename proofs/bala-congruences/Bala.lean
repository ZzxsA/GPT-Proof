import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Congruences for the binomial-coefficient expansion of Bala's
power-series family (OEIS A361281 and A293013). -/
namespace Bala
open Finset

private theorem subtract_same {a b k : ℕ} (h : a ≡ b [MOD k]) {j : ℕ}
    (ha : j ≤ a) (hb : j ≤ b) : a - j ≡ b - j [MOD k] := by
  apply Nat.ModEq.add_right_cancel' j
  simpa only [Nat.sub_add_cancel ha, Nat.sub_add_cancel hb] using h

private theorem falling_congr {a b k : ℕ} (h : a ≡ b [MOD k]) (j : ℕ) :
    a.descFactorial j ≡ b.descFactorial j [MOD k] := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
    by_cases ha : j ≤ a
    · by_cases hb : j ≤ b
      · exact (subtract_same h ha hb).mul ih
      · have z := Nat.descFactorial_of_lt (by omega : b < j)
        rw [z] at ih ⊢
        simpa using ih.mul_left (a - j)
    · have z := Nat.descFactorial_of_lt (by omega : a < j)
      rw [z] at ih ⊢
      simpa using ih.mul_left (b - j)

/-- The indexed summand before multiplication by an integer coefficient. -/
def kernel (n j i : ℕ) : ℕ :=
  n.descFactorial j * (n * (n-j)).choose i

theorem kernel_shift (n k j i : ℕ) (hi : i ≤ j) :
    kernel (n+k) j i ≡ kernel n j i [MOD k] := by
  have h : n+k ≡ n [MOD k] := Nat.add_modEq_right
  have hd := falling_congr h j
  unfold kernel
  refine (hd.mul_right _).trans ?_
  by_cases hj : j ≤ n
  · have hv := h.mul (subtract_same h (by omega : j ≤ n+k) hj)
    have hc := falling_congr hv i
    rw [Nat.descFactorial_eq_factorial_mul_choose,
        Nat.descFactorial_eq_factorial_mul_choose] at hc
    obtain ⟨t, ht⟩ := (Nat.factorial_dvd_factorial hi).trans (Nat.factorial_dvd_descFactorial n j)
    simpa only [ht, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hc.mul_left t
  · rw [Nat.descFactorial_of_lt (by omega : n < j)]
    simp only [Nat.zero_mul]
    rfl

/-- The integer array c(j,i) represents [x^j] F(x)(G(x)-1)^i. -/
def inner (c : ℕ → ℕ → ℤ) (n j : ℕ) : ℤ :=
  ∑ i ∈ range (j+1), c j i * (kernel n j i : ℤ)

private theorem sum_congr_mod {k : ℕ} (u v : ℕ → ℤ) (s : Finset ℕ)
    (h : ∀ i ∈ s, u i ≡ v i [ZMOD k]) :
    ∑ i ∈ s, u i ≡ ∑ i ∈ s, v i [ZMOD k] := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

private theorem inner_shift (c : ℕ → ℕ → ℤ) (n k j : ℕ) :
    inner c (n+k) j ≡ inner c n j [ZMOD k] := by
  apply sum_congr_mod
  intro i hi
  have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  exact (Int.natCast_modEq_iff.mpr (kernel_shift n k j i hij)).mul_left (c j i)

private theorem inner_zero (c : ℕ → ℕ → ℤ) {n j : ℕ} (h : n < j) : inner c n j = 0 := by
  simp [inner, kernel, Nat.descFactorial_of_lt h]

def diagonal (c : ℕ → ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ range (n+1), inner c n j

private theorem pad (c : ℕ → ℕ → ℤ) (n t : ℕ) :
    ∑ j ∈ range (n+1+t), inner c n j = diagonal c n := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Nat.add_succ, Finset.sum_range_succ, ih, inner_zero c (by omega : n < n+1+t), add_zero]

/-- Bala's universal finite coefficient identity, for all integer arrays. -/
theorem diagonal_shift (c : ℕ → ℕ → ℤ) (n k : ℕ) :
    diagonal c (n+k) ≡ diagonal c n [ZMOD k] := by
  rw [← pad c n k]
  unfold diagonal
  rw [show n+k+1=n+1+k by omega]
  apply sum_congr_mod
  intro j _
  exact inner_shift c n k j

#print axioms diagonal_shift
end Bala
