import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A graph-level proof of the strict universal bound in Gregory Clark's
Conjecture 4.4. The adjacency matrix can even be any nonnegative real matrix.
An eigenvector is normalized by dividing by its least entry. -/

namespace Clark

open scoped BigOperators

variable {V : Type*} [Fintype V] [Nonempty V]

noncomputable def mean (y : V → ℝ) : ℝ := (∑ i, y i) / Fintype.card V

theorem mean_mono {y z : V → ℝ} (h : ∀ i, y i ≤ z i) : mean y ≤ mean z :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => h i)) (by positivity)

theorem mean_const (k : ℝ) : mean (fun _ : V => k) = k := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [mean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem mean_add (y z : V → ℝ) :
    mean (fun i => y i + z i) = mean y + mean z := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_sub (y z : V → ℝ) :
    mean (fun i => y i - z i) = mean y - mean z := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

theorem mean_scale (k : ℝ) (y : V → ℝ) :
    mean (fun i => k * y i) = k * mean y := by
  simp only [mean, ← Finset.mul_sum, mul_div_assoc]

/-- Squared coefficient of variation, with uniform population weights. -/
noncomputable def dispersion (y : V → ℝ) : ℝ :=
  mean (fun i => (y i - mean y)^2) / (mean y)^2

theorem dispersion_nonneg (y : V → ℝ) : 0 ≤ dispersion y := by
  have h := mean_mono (y := fun _ : V => (0 : ℝ))
    (z := fun i => (y i - mean y)^2) (fun i => sq_nonneg _)
  rw [mean_const] at h
  exact div_nonneg h (sq_nonneg _)

theorem variance_eq (y : V → ℝ) :
    mean (fun i => (y i - mean y)^2) = mean (fun i => y i^2) - (mean y)^2 := by
  calc
    _ = mean (fun i => (y i^2 - (2*mean y)*y i) + (mean y)^2) := by
      congr 1
      funext i
      ring
    _ = _ := by
      rw [mean_add, mean_sub, mean_scale, mean_const]
      ring

/-- A finite-population form of the Kantorovich range bound. -/
theorem dispersion_le_range (y : V → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ i, a ≤ y i ∧ y i ≤ b) : dispersion y ≤ (b-a)^2/(4*a*b) := by
  have hμ : a ≤ mean y := by
    simpa only [mean_const] using (mean_mono (y := fun _ : V => a) (z := y) (fun i => (h i).1))
  have hm : mean (fun i => y i^2) ≤ (a+b)*mean y-a*b := by
    calc
      _ ≤ mean (fun i => (a+b)*y i-a*b) := mean_mono (fun i => by
        nlinarith [mul_nonneg (sub_nonneg.mpr (h i).1) (sub_nonneg.mpr (h i).2)])
      _ = _ := by rw [mean_sub, mean_scale, mean_const]
  have hμpos : 0 < mean y := ha.trans_le hμ
  unfold dispersion
  rw [variance_eq]
  apply (div_le_div_iff₀ (by positivity : 0 < (mean y)^2) (by positivity : 0 < 4*a*b)).2
  nlinarith [mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ 4*a*b),
    sq_nonneg ((a+b)*mean y - 2*a*b)]

noncomputable def degree (A : V → V → ℝ) (i : V) : ℝ := ∑ j, A i j

theorem degree_interval (A : V → V → ℝ) (x : V → ℝ) {ρ g : ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hρ : 0 < ρ) (hg : 1 ≤ g)
    (hx : ∀ i, 1 ≤ x i ∧ x i ≤ g)
    (eigen : ∀ i, ∑ j, A i j * x j = ρ*x i) :
    ∀ i, ρ/g ≤ degree A i ∧ degree A i ≤ ρ*g := by
  have hg0 : 0 < g := by linarith
  intro i
  constructor
  · apply (div_le_iff₀ hg0).2
    calc
      ρ = ρ*1 := (mul_one ρ).symm
      _ ≤ ρ*x i := mul_le_mul_of_nonneg_left (hx i).1 hρ.le
      _ = ∑ j, A i j * x j := (eigen i).symm
      _ ≤ ∑ j, A i j * g := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (hx j).2 (hA i j))
      _ = degree A i * g := by rw [degree, Finset.sum_mul]
  · calc
      degree A i = ∑ j, A i j * 1 := by simp [degree]
      _ ≤ ∑ j, A i j * x j := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (hx j).1 (hA i j))
      _ = ρ*x i := eigen i
      _ ≤ ρ*g := mul_le_mul_of_nonneg_left (hx i).2 hρ.le

/-- Clark's published sign convention uses degree dispersion minus eigenvector
dispersion. With the least entry of the positive eigenvector normalized to one,
its largest entry is the principal ratio g. The proof also allows g to be any
upper bound on the normalized entries. -/
theorem graph_quarter (A : V → V → ℝ) (x : V → ℝ) {ρ g : ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hρ : 0 < ρ) (hg : 1 ≤ g)
    (hx : ∀ i, 1 ≤ x i ∧ x i ≤ g)
    (eigen : ∀ i, ∑ j, A i j * x j = ρ*x i) :
    (dispersion (degree A) - dispersion x) / g^2 < 1/4 := by
  have hg0 : 0 < g := by linarith
  have dr := degree_interval A x hA hρ hg hx eigen
  have bound := dispersion_le_range (degree A) (div_pos hρ hg0) (mul_pos hρ hg0) dr
  have simplify_bound : (ρ*g - ρ/g)^2/(4*(ρ/g)*(ρ*g)) = (g-1/g)^2/4 := by
    field_simp [ne_of_gt hρ, ne_of_gt hg0]
    <;> ring
  rw [simplify_bound] at bound
  have inv_le : 1/g ≤ 1 := (div_le_iff₀ hg0).2 (by linarith)
  have strict : (g-1/g)^2 < g^2 := by
    nlinarith [mul_pos (one_div_pos.mpr hg0) (show 0 < 2*g-1/g by linarith)]
  apply (div_lt_iff₀ (by positivity : 0 < g^2)).2
  linarith [dispersion_nonneg x]

#print axioms graph_quarter

end Clark
