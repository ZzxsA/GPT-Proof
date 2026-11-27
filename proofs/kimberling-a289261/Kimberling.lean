import Std

/-! Clark Kimberling's A289261. A series is a sequence of integer coefficients.
The product below is the ordinary Cauchy product, with the first factor
expanded one coefficient at a time. -/
namespace Kimberling

abbrev Series := Nat → Int

def floorKernel (n : Nat) : Int :=
  let q : Int := Int.ofNat (13 * (n + 1) / 8)
  if n % 2 = 0 then q else -q

private def tail (f : Series) : Series := fun n => f (n + 1)

def product (f g : Series) : Nat → Int
  | 0 => f 0 * g 0
  | n+1 => f 0 * g (n+1) + product (tail f) g n

def unitSeries : Series
  | 0 => 1
  | _+1 => 0

def IsFloorReciprocal (a : Series) : Prop := ∀ n, product floorKernel a n = unitSeries n

private def add (f g : Series) : Series := fun n => f n + g n
private def sub (f g : Series) : Series := fun n => f n - g n
private def shift (f : Series) : Series
  | 0 => 0
  | n+1 => f n
private def lag : Nat → Series → Series
  | 0, f => f
  | d+1, f => shift (lag d f)

private theorem product_add (f g a : Series) (n : Nat) :
    product (add f g) a n = product f a n + product g a n := by
  induction n generalizing f g with
  | zero => simp [product, add, Int.add_mul]
  | succ n ih =>
    change (f 0 + g 0) * a (n+1) + product (add (tail f) (tail g)) a n =
      (f 0 * a (n+1) + product (tail f) a n) + (g 0 * a (n+1) + product (tail g) a n)
    rw [Int.add_mul, ih]
    omega

private theorem product_sub (f g a : Series) (n : Nat) :
    product (sub f g) a n = product f a n - product g a n := by
  induction n generalizing f g with
  | zero => simp [product, sub, Int.sub_mul]
  | succ n ih =>
    change (f 0 - g 0) * a (n+1) + product (sub (tail f) (tail g)) a n =
      (f 0 * a (n+1) + product (tail f) a n) - (g 0 * a (n+1) + product (tail g) a n)
    rw [Int.sub_mul, ih]
    omega

private theorem product_lag (d : Nat) (f a : Series) (n : Nat) :
    product (lag d f) a n = lag d (product f a) n := by
  induction d generalizing n with
  | zero => rfl
  | succ d ih =>
    cases n with
    | zero => simp [lag, shift, product]
    | succ n =>
      change 0 * a (n+1) + product (lag d f) a n = lag d (product f a) n
      simp [ih]

private def coeffs : List Int := [1, -2, 1, -2, 2, -1, 2, -2]

private def fromList : List Int → Series
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: cs, n+1 => fromList cs n

private def applyPoly : List Int → Series → Nat → Int
  | [], _, _ => 0
  | c :: _, a, 0 => c * a 0
  | c :: cs, a, n+1 => c * a (n+1) + applyPoly cs a n

private theorem product_zero (a : Series) (n : Nat) :
    product (fun _ => 0) a n = 0 := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    change 0 * a (n+1) + product (fun _ => 0) a n = 0
    simp [ih]

private theorem product_poly (cs : List Int) (a : Series) (n : Nat) :
    product (fromList cs) a n = applyPoly cs a n := by
  induction cs generalizing n with
  | nil => exact product_zero a n
  | cons c cs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change c * a (n+1) + product (fromList cs) a n = c * a (n+1) + applyPoly cs a n
      rw [ih]

/-- Multiply the given floor series by (1+x)(1-x^8). -/
private theorem kernel_identity :
    fromList coeffs = sub (add floorKernel (lag 1 floorKernel))
                          (add (lag 8 floorKernel) (lag 9 floorKernel)) := by
  funext n
  by_cases hn : n < 9
  · have H : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases H with h|h|h|h|h|h|h|h|h <;> subst n <;> decide
  · obtain ⟨k, rfl⟩ : ∃ k, n = k+9 := ⟨n-9, by omega⟩
    change (0 : Int) = (floorKernel (k+9) + floorKernel (k+8)) -
      (floorKernel (k+1) + floorKernel k)
    have div_shift (j : Nat) :
        13 * (j + 8 + 1) / 8 = 13 * (j + 1) / 8 + 13 := by
      rw [show 13 * (j + 8 + 1) = 13 * (j + 1) + 8 * 13 by omega]
      exact Nat.add_mul_div_left _ _ (by decide)
    have hA : 13 * (k+9+1) / 8 = 13 * (k+1+1) / 8 + 13 := div_shift (k+1)
    have hB := div_shift k
    simp only [floorKernel, hA, hB, Int.ofNat_add]
    split <;> split <;> split <;> split <;> omega

private theorem transformed {a : Series} (h : IsFloorReciprocal a) (n : Nat) :
    applyPoly coeffs a n = (unitSeries n + lag 1 unitSeries n) -
                           (lag 8 unitSeries n + lag 9 unitSeries n) := by
  have hu : product floorKernel a = unitSeries := funext h
  rw [← product_poly, kernel_identity, product_sub, product_add, product_add]
  simp only [product_lag, hu]

private theorem initial {a : Series} (h : IsFloorReciprocal a) :
    a 0 = 1 ∧ a 1 = 3 ∧ a 2 = 5 ∧ a 3 = 9 ∧ a 4 = 17 ∧ a 5 = 30 ∧
    a 6 = 52 ∧ a 7 = 91 ∧ a 8 = 160 ∧ a 9 = 281 ∧ a 10 = 494 := by
  have e0 := transformed h 0
  have e1 := transformed h 1
  have e2 := transformed h 2
  have e3 := transformed h 3
  have e4 := transformed h 4
  have e5 := transformed h 5
  have e6 := transformed h 6
  have e7 := transformed h 7
  have e8 := transformed h 8
  have e9 := transformed h 9
  have e10 := transformed h 10
  simp [coeffs, applyPoly, unitSeries, lag, shift] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  omega

/-- Two successive instances of the order-seven recurrence eliminate the
negative coefficients in the next difference. -/
private theorem step {a : Series} (h : IsFloorReciprocal a) (k : Nat) :
    a (k+11) - a (k+10) = 2 * a (k+3) + (a (k+6) - a (k+5)) +
      2 * (a (k+7) - a (k+6)) + 2 * (a (k+8) - a (k+7)) +
      (a (k+9) - a (k+8)) := by
  have e := transformed h (k+10)
  have f := transformed h (k+11)
  change 1*a (k+10) + ((-2)*a (k+9) + (1*a (k+8) + ((-2)*a (k+7) +
    (2*a (k+6) + ((-1)*a (k+5) + (2*a (k+4) + ((-2)*a (k+3) + 0))))))) = 0 at e
  change 1*a (k+11) + ((-2)*a (k+10) + (1*a (k+9) + ((-2)*a (k+8) +
    (2*a (k+7) + ((-1)*a (k+6) + (2*a (k+5) + ((-2)*a (k+4) + 0))))))) = 0 at f
  omega

theorem strictly_increasing_of_reciprocal {a : Series} (h : IsFloorReciprocal a) (n : Nat) :
    0 < a n ∧ a n < a (n+1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < 10
    · have vals := initial h
      have H : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
      rcases H with h'|h'|h'|h'|h'|h'|h'|h'|h'|h' <;> subst n <;> simp only [Nat.reduceAdd] <;> omega
    · obtain ⟨k, rfl⟩ : ∃ k, n = k+10 := ⟨n-10, by omega⟩
      have p := ih (k+3) (by omega)
      have d5 := ih (k+5) (by omega)
      have d6 := ih (k+6) (by omega)
      have d7 := ih (k+7) (by omega)
      have d8 := ih (k+8) (by omega)
      have d9 := ih (k+9) (by omega)
      have eqn := step h k
      simp only [Nat.add_assoc, Nat.reduceAdd] at p d5 d6 d7 d8 d9 ⊢
      omega

private theorem product_congr_right (f g g' : Series) (n : Nat)
    (h : ∀ j, j ≤ n → g j = g' j) : product f g n = product f g' n := by
  induction n generalizing f with
  | zero => simp [product, h 0 (by omega)]
  | succ n ih =>
    simp only [product]
    rw [h (n+1) (by omega), ih (tail f) (fun j hj => h j (by omega))]

/-- The unique usual reciprocal can be generated coefficient by coefficient,
since floorKernel 0 = 1. The truncated recursive call uses only earlier indices. -/
def a289261 (n : Nat) : Int :=
  match n with
  | 0 => 1
  | m+1 =>
    -product (tail floorKernel) (fun i => if hi : i < m+1 then a289261 i else 0) m
termination_by n
decreasing_by omega

theorem is_reciprocal : IsFloorReciprocal a289261 := by
  intro n
  cases n with
  | zero => change 1 * a289261 0 = 1; simp [a289261]
  | succ m =>
    have eqn : a289261 (m+1) =
        -product (tail floorKernel) (fun i => if i < m+1 then a289261 i else 0) m := by
      rw [a289261]
      simp only [dite_eq_ite]
    have cut := product_congr_right (tail floorKernel)
      (fun i => if i < m+1 then a289261 i else 0) a289261 m
      (fun i hi => if_pos (by omega))
    change 1 * a289261 (m+1) + product (tail floorKernel) a289261 m = 0
    rw [Int.one_mul, eqn, cut]
    omega

/-- Clark Kimberling's strict monotonicity conjecture in OEIS A289261. -/
theorem a289261_strict (n : Nat) : a289261 n < a289261 (n+1) :=
  (strictly_increasing_of_reciprocal is_reciprocal n).2

#print axioms a289261_strict

end Kimberling
