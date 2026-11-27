import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Kimberling

/-! Strict growth of the reciprocal shifted floor series in OEIS A289245. -/
namespace KimberlingShift
open Kimberling

noncomputable section

def floorAt (r : ℝ) (n : ℕ) : ℤ := ⌊(n : ℝ) * r⌋

/-- Subtracting one after the floor equals the OEIS floor of the shifted argument. -/
def kernel (r : ℝ) (n : ℕ) : ℤ :=
  if n % 2 = 0 then floorAt r (n+1) - 1 else -(floorAt r (n+1) - 1)

def IsReciprocal (r : ℝ) (a : Series) : Prop :=
  ∀ n, product (kernel r) a n = unitSeries n

private def delay (f : Series) : Series
  | 0 => 0
  | n+1 => f n

private def denominator (r : ℝ) (n : ℕ) : ℤ := kernel r n + delay (kernel r) n

private def numerator : Series
  | 0 | 1 => 1
  | _+2 => 0

private theorem increments (r : ℝ) (lo : 5/2 ≤ r) (hi : r < 8/3) (n : ℕ) :
    floorAt r n + 2 ≤ floorAt r (n+1) ∧
    floorAt r (n+1) ≤ floorAt r n + 3 := by
  have hmul : ((n+1 : ℕ) : ℝ) * r = (n : ℝ) * r + r := by
    push_cast
    ring
  have hl : (n : ℝ)*r + ((2 : ℤ) : ℝ) ≤ (n : ℝ)*r + r := by norm_num; linarith
  have hu : (n : ℝ)*r + r ≤ (n : ℝ)*r + ((3 : ℤ) : ℝ) := by norm_num; linarith
  have h₁ := Int.floor_le_floor hl
  have h₂ := Int.floor_le_floor hu
  rw [Int.floor_add_intCast] at h₁ h₂
  simpa only [floorAt, hmul] using And.intro h₁ h₂

private theorem initial (r : ℝ) (lo : 5/2 ≤ r) (hi : r < 8/3) :
    denominator r 0 = 1 ∧ denominator r 1 = -3 ∧ denominator r 2 = 2 := by
  have q₁ : floorAt r 1 = 2 := by
    unfold floorAt
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have q₂ : floorAt r 2 = 5 := by
    unfold floorAt
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  have q₃ : floorAt r 3 = 7 := by
    unfold floorAt
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith
  norm_num [denominator, kernel, delay, q₁, q₂, q₃]

private theorem bound (r : ℝ) (lo : 5/2 ≤ r) (hi : r < 8/3) (k : ℕ) :
    denominator r (k+1) ≤ (if (k+1)%2=0 then (3 : ℤ) else -2) := by
  obtain ⟨hl, hu⟩ := increments r lo hi (k+1)
  by_cases he : (k+1)%2 = 0
  · have ho : k%2 ≠ 0 := by omega
    simp only [denominator, kernel, delay, Nat.succ_eq_add_one, he, ho, if_true, if_false]
    omega
  · have ho : k%2 = 0 := by omega
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
    product (denominator r) a n = numerator n := by
  change product (fun j => kernel r j + delay (kernel r) j) a n = _
  rw [add_left, h]
  cases n with
  | zero => simp [product, delay, unitSeries, numerator]
  | succ k =>
    change unitSeries (k+1) + (0 * a (k+1) + product (kernel r) a k) = _
    rw [h k]
    simp only [zero_mul, zero_add]
    cases k <;> rfl

/-- Pair consecutive terms of the tail: negative, positive, negative, positive, … -/
private theorem paired (a : Series) (n : ℕ) (f : Series)
    (hf : ∀ i, f i ≤ if i%2=0 then -2 else 3)
    (hp : ∀ i, i ≤ n → 0 ≤ a i) (hg : ∀ i, i < n → 2*a i ≤ a (i+1)) :
    product f a n ≤ 0 := by
  induction n using Nat.strongRecOn generalizing f with
  | ind n ih =>
    have h₀ : f 0 ≤ -2 := by simpa using hf 0
    have h₁ : f 1 ≤ 3 := by simpa using hf 1
    match n with
    | 0 =>
      change f 0 * a 0 ≤ 0
      exact mul_nonpos_of_nonpos_of_nonneg (by omega) (hp 0 (by omega))
    | 1 =>
      change f 0*a 1 + f 1*a 0 ≤ 0
      have x := mul_le_mul_of_nonneg_right h₀ (hp 1 (by omega))
      have y := mul_le_mul_of_nonneg_right h₁ (hp 0 (by omega))
      have z := hg 0 (by omega)
      have u := hp 0 (by omega)
      omega
    | k+2 =>
      let g : Series := fun j => f (j+2)
      have bg (j : ℕ) : g j ≤ if j%2=0 then -2 else 3 := by
        have e := hf (j+2)
        have hmod : (j+2)%2 = j%2 := by omega
        simpa only [g, hmod] using e
      have t := ih k (by omega) g bg (fun i hi => hp i (by omega))
        (fun i hi => hg i (by omega))
      change f 0*a (k+2) + (f 1*a (k+1) + product g a k) ≤ 0
      have x := mul_le_mul_of_nonneg_right h₀ (hp (k+2) (by omega))
      have y := mul_le_mul_of_nonneg_right h₁ (hp (k+1) (by omega))
      have z := hg (k+1) (by omega)
      have u := hp (k+1) (by omega)
      omega

private theorem growth_of_reciprocal (r : ℝ) (lo : 5/2 ≤ r) (hi : r < 8/3)
    (a : Series) (ha : IsReciprocal r a) (n : ℕ) :
    0 < a n ∧ 2*a n ≤ a (n+1) := by
  let d := denominator r
  have ⟨h₀,h₁,h₂⟩ := initial r lo hi
  change d 0 = 1 at h₀
  change d 1 = -3 at h₁
  change d 2 = 2 at h₂
  have tr (i : ℕ) : product d a i = numerator i := transformed r a ha i
  have e₀ := tr 0
  have e₁ := tr 1
  change d 0*a 0=1 at e₀
  change d 0*a 1+d 1*a 0=1 at e₁
  rw [h₀] at e₀ e₁
  rw [h₁] at e₁
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => omega
    | 1 =>
      have e := tr 2
      change d 0*a 2 + (d 1*a 1 + d 2*a 0) = 0 at e
      rw [h₀,h₁,h₂] at e
      omega
    | k+2 =>
      let f : Series := fun j => d (j+3)
      have hb (j : ℕ) : f j ≤ if j%2=0 then -2 else 3 := by
        have e := bound r lo hi (j+2)
        change d (j+3) ≤ (if (j+3)%2=0 then 3 else -2) at e
        change d (j+3) ≤ _
        split <;> split at e <;> omega
      have t := paired a k f hb
        (fun i h => le_of_lt (ih i (by omega)).1)
        (fun i h => (ih i (by omega)).2)
      have e := tr (k+3)
      change d 0*a (k+3)+(d 1*a (k+2)+(d 2*a (k+1)+product f a k))=0 at e
      rw [h₀,h₁,h₂] at e
      obtain ⟨p,q⟩ := ih (k+1) (by omega)
      omega

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

theorem coefficients_are_reciprocal (r : ℝ) (lo : 5/2 ≤ r) (hi : r < 8/3) :
    IsReciprocal r (coefficients r) := by
  apply reciprocal_of_unit
  have h := (initial r lo hi).1
  simpa only [denominator, delay, add_zero] using h

theorem doubled (r : ℝ) (lo : 5/2 ≤ r) (hi : r < 8/3) (n : ℕ) :
    0 < coefficients r n ∧ 2*coefficients r n ≤ coefficients r (n+1) :=
  growth_of_reciprocal r lo hi _ (coefficients_are_reciprocal r lo hi) n

theorem a289245_strict (n : ℕ) :
    coefficients ((3+Real.sqrt 5)/2) n < coefficients ((3+Real.sqrt 5)/2) (n+1) := by
  have lower : (2:ℝ) ≤ Real.sqrt 5 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have upper : Real.sqrt 5 < (7:ℝ)/3 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have low : (5:ℝ)/2 ≤ (3+Real.sqrt 5)/2 := by linarith
  have high : (3+Real.sqrt 5)/2 < (8:ℝ)/3 := by linarith
  obtain ⟨p, q⟩ := doubled _ low high n
  omega

#print axioms coefficients_are_reciprocal
#print axioms doubled
#print axioms a289245_strict

end
end KimberlingShift
