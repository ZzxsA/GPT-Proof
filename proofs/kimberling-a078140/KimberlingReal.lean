import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import KimberlingFamily

/-! Clark Kimberling's A078140 interval conjecture.
`kernel r` has coefficient (-1)^n floor((n+1)r). The ordinary Cauchy
product in `IsReciprocal` specifies its formal reciprocal. -/
namespace KimberlingReal
open Kimberling

noncomputable section

def floorAt (r : ℝ) (n : ℕ) : ℤ := ⌊(n : ℝ) * r⌋

def kernel (r : ℝ) (n : ℕ) : ℤ :=
  if n % 2 = 0 then floorAt r (n + 1) else -floorAt r (n + 1)

def IsReciprocal (r : ℝ) (a : Series) : Prop :=
  ∀ n, product (kernel r) a n = unitSeries n

private def delay (f : Series) : Series
  | 0 => 0
  | n + 1 => f n

private def denominator (r : ℝ) (n : ℕ) : ℤ := kernel r n + delay (kernel r) n

private theorem increments (r : ℝ) (lo : 3 / 2 ≤ r) (hi : r < 5 / 3) (n : ℕ) :
    floorAt r n + 1 ≤ floorAt r (n + 1) ∧
    floorAt r (n + 1) ≤ floorAt r n + 2 := by
  have hmul : ((n + 1 : ℕ) : ℝ) * r = (n : ℝ) * r + r := by
    push_cast
    ring
  have hl : (n : ℝ) * r + 1 ≤ (n : ℝ) * r + r := by linarith
  have hu : (n : ℝ) * r + r ≤ (n : ℝ) * r + ((2 : ℤ) : ℝ) := by
    norm_num
    linarith
  have h₁ := Int.floor_le_floor hl
  have h₂ := Int.floor_le_floor hu
  rw [Int.floor_add_one] at h₁
  rw [Int.floor_add_intCast] at h₂
  simpa only [floorAt, hmul] using And.intro h₁ h₂

private theorem initial (r : ℝ) (lo : 3 / 2 ≤ r) (hi : r < 5 / 3) :
    denominator r 0 = 1 ∧ denominator r 1 = -2 ∧
    denominator r 2 = 1 ∧ denominator r 3 = -2 := by
  have q₁ : floorAt r 1 = 1 := by
    unfold floorAt
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have q₂ : floorAt r 2 = 3 := by
    unfold floorAt
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have q₃ : floorAt r 3 = 4 := by
    unfold floorAt
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have q₄ : floorAt r 4 = 6 := by
    unfold floorAt
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  norm_num [denominator, kernel, delay, q₁, q₂, q₃, q₄]

private theorem bound (r : ℝ) (lo : 3 / 2 ≤ r) (hi : r < 5 / 3) (n : ℕ)
    (hn : 4 ≤ n) : denominator r n ≤ if n % 2 = 0 then (2 : ℤ) else -1 := by
  cases n with
  | zero => omega
  | succ k =>
    obtain ⟨hl, hu⟩ := increments r lo hi (k + 1)
    by_cases he : (k + 1) % 2 = 0
    · have ho : k % 2 ≠ 0 := by omega
      simp only [denominator, kernel, delay, Nat.succ_eq_add_one, he, ho, if_true, if_false]
      omega
    · have ho : k % 2 = 0 := by omega
      simp only [denominator, kernel, delay, Nat.succ_eq_add_one, he, ho, if_true, if_false]
      omega

private theorem add_left (f g a : Series) (n : ℕ) :
    product (fun j => f j + g j) a n = product f a n + product g a n := by
  induction n generalizing f g with
  | zero => simp [product, add_mul]
  | succ n ih =>
    change (f 0 + g 0) * a (n+1) +
        product (fun j => f (j+1) + g (j+1)) a n =
      (f 0 * a (n+1) + product (fun j => f (j+1)) a n) +
      (g 0 * a (n+1) + product (fun j => g (j+1)) a n)
    rw [add_mul, ih]
    omega

private theorem transformed (r : ℝ) (a : Series) (h : IsReciprocal r a) (n : ℕ) :
    product (denominator r) a n = KimberlingFamily.numerator n := by
  change product (fun j => kernel r j + delay (kernel r) j) a n = _
  rw [add_left, h]
  cases n with
  | zero => simp [product, delay, unitSeries, KimberlingFamily.numerator]
  | succ k =>
    change unitSeries (k+1) + (0 * a (k+1) + product (kernel r) a k) = _
    rw [h k]
    simp only [zero_mul, zero_add]
    cases k <;> rfl

/-- Every coefficient of the reciprocal of the signed floor series is positive
and strictly smaller than the next one, throughout [3/2,5/3). -/
theorem strictlyIncreasing (r : ℝ) (lo : 3 / 2 ≤ r) (hi : r < 5 / 3)
    (a : Series) (ha : IsReciprocal r a) (n : ℕ) : 0 < a n ∧ a n < a (n + 1) := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := initial r lo hi
  exact KimberlingFamily.strictlyIncreasing (denominator r) a h₀ h₁ h₂ h₃
    (bound r lo hi) (transformed r a ha) n

private theorem congr_right (f a b : Series) (n : ℕ)
    (h : ∀ i, i ≤ n → a i = b i) : product f a n = product f b n := by
  induction n generalizing f with
  | zero => simp [product, h 0 (by omega)]
  | succ n ih =>
    change f 0 * a (n+1) + product (fun i => f (i+1)) a n =
      f 0 * b (n+1) + product (fun i => f (i+1)) b n
    rw [h (n+1) (by omega), ih (fun i => f (i+1)) (fun i hi => h i (by omega))]

/-- Coefficients obtained by formal division, with constant term one. -/
def coefficients (r : ℝ) (n : ℕ) : ℤ :=
  match n with
  | 0 => 1
  | m+1 => -product (fun i => kernel r (i+1))
      (fun i => if h : i < m+1 then coefficients r i else 0) m
termination_by n
decreasing_by omega

private theorem reciprocal_of_unit (r : ℝ) (h₀ : kernel r 0 = 1) :
    IsReciprocal r (coefficients r) := by
  intro n
  cases n with
  | zero =>
    change kernel r 0 * coefficients r 0 = 1
    rw [h₀]
    simp [coefficients]
  | succ m =>
    have eqn : coefficients r (m+1) = -product (fun i => kernel r (i+1))
        (fun i => if i < m+1 then coefficients r i else 0) m := by
      rw [coefficients]
      simp only [dite_eq_ite]
    have cut := congr_right (fun i => kernel r (i+1))
      (fun i => if i < m+1 then coefficients r i else 0) (coefficients r) m
      (fun i hi' => if_pos (by omega))
    change kernel r 0 * coefficients r (m+1) +
      product (fun i => kernel r (i+1)) (coefficients r) m = 0
    rw [h₀, one_mul, eqn, cut]
    omega

theorem coefficients_are_reciprocal (r : ℝ) (lo : 3 / 2 ≤ r) (hi : r < 5 / 3) :
    IsReciprocal r (coefficients r) := by
  apply reciprocal_of_unit
  have h := (initial r lo hi).1
  simpa only [denominator, delay, add_zero] using h

theorem coefficients_strict (r : ℝ) (lo : 3 / 2 ≤ r) (hi : r < 5 / 3)
    (n : ℕ) : 0 < coefficients r n ∧ coefficients r n < coefficients r (n+1) :=
  strictlyIncreasing r lo hi _ (coefficients_are_reciprocal r lo hi) n

#print axioms coefficients_strict

private theorem first_three (r : ℝ) (lo : 1 ≤ r) (hi : r < 2) :
    coefficients r 1 = floorAt r 2 ∧
    coefficients r 2 = floorAt r 2 * coefficients r 1 - floorAt r 3 ∧
    coefficients r 3 = floorAt r 2 * coefficients r 2 -
      floorAt r 3 * coefficients r 1 + floorAt r 4 := by
  let a := coefficients r
  have h₀ : kernel r 0 = 1 := by
    change ⌊(1 : ℝ) * r⌋ = (1 : ℤ)
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have h := reciprocal_of_unit r h₀
  have e₀ := h 0
  have e₁ := h 1
  have e₂ := h 2
  have e₃ := h 3
  change kernel r 0 * a 0 = 1 at e₀
  change kernel r 0 * a 1 + kernel r 1 * a 0 = 0 at e₁
  change kernel r 0 * a 2 + (kernel r 1 * a 1 + kernel r 2 * a 0) = 0 at e₂
  change kernel r 0 * a 3 +
    (kernel r 1 * a 2 + (kernel r 2 * a 1 + kernel r 3 * a 0)) = 0 at e₃
  have h₁ : kernel r 1 = -floorAt r 2 := rfl
  have h₂ : kernel r 2 = floorAt r 3 := rfl
  have h₃ : kernel r 3 = -floorAt r 4 := rfl
  simp only [h₀, h₁, h₂, h₃, one_mul] at e₀ e₁ e₂ e₃
  rw [e₀] at e₁ e₂ e₃
  simp only [mul_one, neg_mul] at e₁ e₂ e₃
  change a 1 = floorAt r 2 ∧ a 2 = floorAt r 2 * a 1 - floorAt r 3 ∧
    a 3 = floorAt r 2 * a 2 - floorAt r 3 * a 1 + floorAt r 4
  omega

/-- Exact parameter range for strict increase when the initial floor is one. -/
theorem strictlyIncreasing_iff (r : ℝ) (lo : 1 ≤ r) (hi : r < 2) :
    (∀ n, coefficients r n < coefficients r (n+1)) ↔ 3 / 2 ≤ r ∧ r < 5 / 3 := by
  constructor
  · intro h
    obtain ⟨e₁, e₂, e₃⟩ := first_three r lo hi
    constructor
    · by_contra! hl
      have q₂ : floorAt r 2 = 2 := by
        unfold floorAt
        apply Int.floor_eq_iff.mpr
        constructor <;> norm_num <;> linarith
      have q₃ : 3 ≤ floorAt r 3 := by
        unfold floorAt
        apply Int.le_floor.mpr
        norm_num <;> linarith
      have t : coefficients r 1 < coefficients r 2 := h 1
      rw [q₂] at e₁ e₂
      omega
    · by_contra! hu
      have q₂ : floorAt r 2 = 3 := by
        unfold floorAt
        apply Int.floor_eq_iff.mpr
        constructor <;> norm_num <;> linarith
      have q₃ : floorAt r 3 = 5 := by
        unfold floorAt
        apply Int.floor_eq_iff.mpr
        constructor <;> norm_num <;> linarith
      have q₄ : floorAt r 4 < 8 := by
        unfold floorAt
        apply Int.floor_lt.mpr
        norm_num <;> linarith
      have t : coefficients r 2 < coefficients r 3 := h 2
      rw [q₂] at e₁ e₂ e₃
      rw [q₃] at e₂ e₃
      omega
  · rintro ⟨hl, hu⟩ n
    exact (coefficients_strict r hl hu n).2

#print axioms strictlyIncreasing_iff

end
end KimberlingReal
