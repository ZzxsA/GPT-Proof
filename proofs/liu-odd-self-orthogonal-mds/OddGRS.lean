import Mathlib.Algebra.GeomSum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The finite-field moment obstruction for extended generalized Reed--Solomon
codes of length q+1 and dimension (q-1)/2. The external classification of
arcs needed to deduce the result for every code over a prime field is cited
in the mathematical note. -/
namespace LiuOdd
open Finset

variable {K : Type*} [Field K] [Fintype K]

private theorem no_square_shift (two : (2 : K) ≠ 0) (d : K) :
    ¬ ∀ x : K, ∃ y : K, y ≠ 0 ∧ y^2 = x^2 + d := by
  classical
  intro hex
  let y (x : K) := Classical.choose (hex x)
  have ynz (x : K) : y x ≠ 0 := (Classical.choose_spec (hex x)).1
  have ysq (x : K) : (y x)^2 = x^2 + d := (Classical.choose_spec (hex x)).2
  have hd : d ≠ 0 := by
    intro hz
    have h0 := ysq 0
    rw [hz] at h0
    exact ynz 0 (by simpa using h0)
  let a (x : K) := y x - x
  have hab (x : K) : a x * (y x + x) = d := by
    dsimp [a]
    linear_combination ysq x
  have hnz (x : K) : a x ≠ 0 := by
    intro hx
    exact hd (by simpa [hx] using (hab x).symm)
  have hinj : Function.Injective a := by
    intro x z hx
    have hp : a x * (y x + x) = a x * (y z + z) := by
      calc
        _ = d := hab x
        _ = a z * (y z + z) := (hab z).symm
        _ = _ := by rw [hx]
    have hv := mul_left_cancel₀ (hnz x) hp
    change y x - x = y z - z at hx
    have hdiff : (2 : K) * (x - z) = 0 := by linear_combination hv - hx
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left two)
  obtain ⟨x,hx⟩ := (Finite.injective_iff_surjective.mp hinj) 0
  exact hnz x hx

theorem no_monic_square_values (two : (2 : K) ≠ 0) (b c : K) :
    ¬ ∀ x : K, ∃ y : K, y ≠ 0 ∧ y^2 = x^2 + b*x + c := by
  intro h
  let hlf := b / 2
  have hhlf : (2 : K) * hlf = b := by dsimp [hlf]; field_simp [two]
  apply no_square_shift two (c - hlf^2)
  intro x
  obtain ⟨y,hy,hval⟩ := h (x - hlf)
  refine ⟨y,hy,?_⟩
  rw [hval, ← hhlf]
  ring

private theorem delta [DecidableEq K] (t x : K) :
    1 - (∑ i ∈ range (Fintype.card K), t^i*x^(Fintype.card K-1-i)) =
      if t = x then (1 : K) else 0 := by
  split_ifs with h
  · subst t
    have term (i : ℕ) (hi : i ∈ range (Fintype.card K)) :
        x^i*x^(Fintype.card K-1-i) = x^(Fintype.card K-1) := by
      rw [← pow_add]
      congr 1
      have := mem_range.mp hi
      omega
    rw [sum_congr rfl term]
    simp [nsmul_eq_mul, FiniteField.cast_card_eq_zero]
  · have hh := geom_sum₂_mul t x (Fintype.card K)
    rw [FiniteField.pow_card, FiniteField.pow_card] at hh
    have hs : (∑ i ∈ range (Fintype.card K), t^i*x^(Fintype.card K-1-i)) = 1 :=
      mul_right_cancel₀ (sub_ne_zero.mpr h) (by simpa using hh)
    rw [hs, sub_self]

def moment (w : K → K) (i : ℕ) : K := ∑ t : K, w t * t^i

private theorem recover (w : K → K) (x : K) :
    w x = (∑ t : K, w t) - ∑ i ∈ range (Fintype.card K),
      moment w i * x^(Fintype.card K-1-i) := by
  classical
  calc
    w x = ∑ t : K, w t * (if t = x then 1 else 0) := by simp [mul_ite]
    _ = _ := by
      simp_rw [← delta]
      simp only [mul_sub, mul_one, mul_sum, sum_sub_distrib]
      congr 1
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      rw [moment, sum_mul]
      apply sum_congr rfl
      intro t ht
      ring

/-- The affine column multipliers s(x) and infinity multiplier e cannot
satisfy the Euclidean Gram equations. Here n = q-3 = 2(k-1). -/
theorem no_grs_weights (n : ℕ) (hq : Fintype.card K = n+3) (two : (2 : K) ≠ 0)
    (s : K → K) (e : K) (hs : ∀ x, s x ≠ 0) (he : e ≠ 0)
    (lower : ∀ i < n, moment (fun t => (s t)^2) i = 0)
    (top : moment (fun t => (s t)^2) n + e^2 = 0) : False := by
  classical
  let w (t : K) := (s t)^2
  let b := -moment w (n+1)
  let c := (∑ t : K, w t) - moment w (n+2)
  have splitLast (f : ℕ → K) : (∑ i ∈ range (n+3), f i) =
      (∑ i ∈ range n, f i) + f n + f (n+1) + f (n+2) := by
    rw [sum_range_succ, sum_range_succ, sum_range_succ]
  have eqn (x : K) : (s x)^2 = e^2*x^2 + b*x + c := by
    have h := recover w x
    rw [hq,splitLast] at h
    have hz : (∑ i ∈ range n, moment w i * x^(n+3-1-i)) = 0 := by
      apply sum_eq_zero
      intro i hi
      rw [show moment w i = 0 from lower i (mem_range.mp hi), zero_mul]
    rw [hz, show n+3-1-n = 2 by omega, show n+3-1-(n+1) = 1 by omega,
      show n+3-1-(n+2) = 0 by omega, pow_one, pow_zero, mul_one] at h
    have ht : moment w n = -e^2 := by
      change moment w n + e^2 = 0 at top
      exact eq_neg_of_add_eq_zero_left top
    rw [ht] at h
    change w x = _
    dsimp only [b,c]
    linear_combination h
  apply no_monic_square_values two (b/e^2) (c/e^2)
  intro x
  refine ⟨s x / e, div_ne_zero (hs x) he, ?_⟩
  rw [div_pow,eqn x]
  field_simp [he]
  ring

/-- Euclidean inner product of rows i,j for the extended GRS generator.
There is one column for each affine evaluation parameter and one at infinity. -/
def gramEntry (s : K → K) (e : K) (r i j : ℕ) : K :=
  (∑ t : K, (s t * t^i) * (s t * t^j)) +
    if i = r ∧ j = r then e^2 else 0

private theorem gramEntry_eq (s : K → K) (e : K) (r i j : ℕ) :
    gramEntry s e r i j = moment (fun t => (s t)^2) (i+j) +
      (if i = r ∧ j = r then e^2 else 0) := by
  unfold gramEntry moment
  apply congrArg (fun z : K => z + _)
  apply sum_congr rfl
  intro t ht
  rw [pow_add]
  ring

/-- There is no choice of nonzero column scaling which makes the standard
extended GRS generator Euclidean self-orthogonal. It has r+1 rows and
q+1 columns, where q = 2*r+3. -/
theorem no_extended_grs_self_orthogonal (r : ℕ) (hq : Fintype.card K = 2*r+3)
    (two : (2 : K) ≠ 0) (s : K → K) (e : K) (hs : ∀ x, s x ≠ 0) (he : e ≠ 0) :
    ¬ ∀ i ≤ r, ∀ j ≤ r, gramEntry s e r i j = 0 := by
  intro h
  apply no_grs_weights (2*r) hq two s e hs he
  · intro d hd
    let i := min r d
    let j := d-i
    have hi : i ≤ r := Nat.min_le_left _ _
    have hj : j ≤ r := by dsimp [j,i]; omega
    have hij : i+j = d := by dsimp [j,i]; omega
    have hn : ¬ (i = r ∧ j = r) := by omega
    have gg := h i hi j hj
    simpa [gramEntry_eq,hn,hij] using gg
  · have gg := h r (le_refl _) r (le_refl _)
    simpa [gramEntry_eq,two_mul] using gg

#print axioms no_extended_grs_self_orthogonal

#print axioms no_grs_weights
end LiuOdd
