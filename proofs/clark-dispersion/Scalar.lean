import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# The real-variable inequalities for Clark's Conjecture 4.4

The graph-to-scalar reductions are in PROOF.md. This module leaves those reductions
as named hypotheses. In particular, its quantified objects are real numbers.
-/

namespace Clark

noncomputable def rangeBound (r : ℝ) : ℝ := (r - 1)^2 / (4*r)

noncomputable def loss (c : ℝ) : ℝ := 1 / (1 + Real.sqrt (1+c))^2

noncomputable def upper (t : ℝ) : ℝ :=
  (1 - 1/t^2)^2 * (1 - (2*t/(t+1)^2)^2) / 4

/-- The population range bound, given the result of averaging (y-a)(b-y)≥0.
Here q is the second moment, and u is the first moment. -/
theorem bounded_dispersion {a b u q : ℝ} (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (h : q ≤ (a+b)*u-a*b) :
    (q-u^2)/u^2 ≤ (b-a)^2/(4*a*b) := by
  apply (div_le_div_iff₀ (by positivity : 0 < u^2) (by positivity : 0 < 4*a*b)).2
  nlinarith [mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 4*a*b),
    sq_nonneg ((a+b)*u-2*a*b)]

/-- Coupling from the squared covariance and the root-mean-square degree bound. -/
theorem coupling {c e : ℝ} (hc : 0 ≤ c) (he : 0 ≤ e)
    (h : (Real.sqrt (1+c)-1)^2 ≤ c*e) : c * loss c ≤ e := by
  by_cases hz : c = 0
  · simpa [hz] using he
  have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm hz)
  set s := Real.sqrt (1+c) with hs
  have hsq : s^2 = 1+c := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hpos : 0 < (1+s)^2 := by positivity
  have hid : (s-1)*(1+s) = c := by nlinarith
  have hid2 : (s-1)^2*(1+s)^2 = c*c := by
    rw [← hid]
    ring
  have hm := mul_le_mul_of_nonneg_right h hpos.le
  change (s-1)^2 * (1+s)^2 ≤ c*e * (1+s)^2 at hm
  rw [hid2, mul_assoc] at hm
  have hh : c ≤ e*(1+s)^2 := by
    by_contra! bad
    exact (not_lt_of_ge hm) (mul_lt_mul_of_pos_left bad hc')
  change c * (1 / (1+s)^2) ≤ e
  simpa [div_eq_mul_inv] using (div_le_iff₀ hpos).2 hh

private theorem loss_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    loss b ≤ loss a := by
  have hs : Real.sqrt (1+a) ≤ Real.sqrt (1+b) := Real.sqrt_le_sqrt (by linarith)
  have hp : 0 < (1+Real.sqrt (1+a))^2 := by positivity
  apply one_div_le_one_div_of_le hp
  gcongr <;> linarith

private theorem loss_le_one {a : ℝ} (ha : 0 ≤ a) : loss a ≤ 1 := by
  have hs := Real.sqrt_nonneg (1+a)
  unfold loss
  apply (div_le_iff₀ (by positivity)).2
  nlinarith [sq_nonneg (Real.sqrt (1+a))]

private theorem range_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ rangeBound (t^2) := by
  unfold rangeBound
  positivity

private theorem exact_formula {t : ℝ} (ht : 0 < t) :
    rangeBound (t^2) * (1-loss (rangeBound (t^2))) / t^2 = upper t := by
  have hden : (t+1)^2 ≠ 0 := by positivity
  have hnum : t^2+1 ≠ 0 := by positivity
  have hsq : 1 + rangeBound (t^2) = ((t^2+1)/(2*t))^2 := by
    unfold rangeBound
    field_simp [ne_of_gt ht]
    <;> ring
  have hu : 0 ≤ (t^2+1)/(2*t) := by positivity
  have heq : 1 + (t^2+1)/(2*t) = (t+1)^2/(2*t) := by
    field_simp [ne_of_gt ht]
    <;> ring
  unfold loss
  rw [hsq, Real.sqrt_sq hu, heq]
  unfold rangeBound upper
  field_simp [ne_of_gt ht, hden, ne_of_gt (show 0 < t+1 by linarith)]
  <;> ring

/-- t is the square root of the degree ratio; g is the principal ratio. -/
theorem clark_envelope {c e g t : ℝ} (hc : 0 ≤ c) (he : 0 ≤ e) (ht : 1 ≤ t)
    (hg : t^2 ≤ g^2) (hr : c ≤ rangeBound (t^2))
    (hcov : (Real.sqrt (1+c)-1)^2 ≤ c*e) :
    (c-e)/g^2 ≤ upper t := by
  have ht0 : 0 < t := by linarith
  have ht2 : 0 < t^2 := by positivity
  have hg2 : 0 < g^2 := ht2.trans_le hg
  have hf := coupling hc he hcov
  have hl := loss_antitone hc hr
  have hl0 : 0 ≤ 1-loss (rangeBound (t^2)) :=
    sub_nonneg.mpr (loss_le_one (range_nonneg ht0))
  have hnum : c-e ≤ rangeBound (t^2)*(1-loss (rangeBound (t^2))) := by
    nlinarith [mul_le_mul_of_nonneg_left hl hc,
      mul_le_mul_of_nonneg_right hr hl0]
  calc
    (c-e)/g^2 ≤ (rangeBound (t^2)*(1-loss (rangeBound (t^2))))/g^2 :=
      div_le_div_of_nonneg_right hnum hg2.le
    _ ≤ (rangeBound (t^2)*(1-loss (rangeBound (t^2))))/t^2 :=
      div_le_div_of_nonneg_left (mul_nonneg (range_nonneg ht0) hl0) ht2 hg
    _ = upper t := exact_formula ht0

private theorem inverse_range {t : ℝ} (ht : 1 ≤ t) :
    0 < 1/t^2 ∧ 1/t^2 ≤ 1 := by
  have h : 0 < t := by linarith
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < t^2)).2
    nlinarith [sq_nonneg (t-1)]

private theorem star_ratio_range {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ 2*t/(t+1)^2 ∧ 2*t/(t+1)^2 ≤ 1 := by
  have h : 0 < t := by linarith
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < (t+1)^2)).2
    nlinarith [sq_nonneg t]

theorem upper_monotone {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    upper s ≤ upper t := by
  have ht : 1 ≤ t := hs.trans hst
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hst2 : s^2 ≤ t^2 := by gcongr
  have h_inv := one_div_le_one_div_of_le (by positivity : 0 < s^2) hst2
  have h₁ : (1-1/s^2)^2 ≤ (1-1/t^2)^2 := by
    gcongr
    all_goals first | exact sub_nonneg.mpr (inverse_range hs).2 | linarith
  have hp : 0 ≤ s*t-1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr ht)]
  have hr : 2*t/(t+1)^2 ≤ 2*s/(s+1)^2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hst) hp]
  have hrsq : (2*t/(t+1)^2)^2 ≤ (2*s/(s+1)^2)^2 := by
    exact pow_le_pow_left₀ (star_ratio_range ht).1 hr 2
  have hb : (2*s/(s+1)^2)^2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (star_ratio_range hs).1 (star_ratio_range hs).2 2
  unfold upper
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul h₁ (by linarith) (sub_nonneg.mpr hb) (sq_nonneg _)

theorem upper_lt_quarter {t : ℝ} (ht : 1 ≤ t) : upper t < 1/4 := by
  obtain ⟨hp, hb⟩ := inverse_range ht
  have ha : (1-1/t^2)^2 < 1 := by
    nlinarith [mul_pos hp (show 0 < 2-1/t^2 by linarith)]
  have hle : (1-1/t^2)^2 * (1-(2*t/(t+1)^2)^2) ≤ (1-1/t^2)^2 := by
    nlinarith [mul_nonneg (sq_nonneg (1-1/t^2)) (sq_nonneg (2*t/(t+1)^2))]
  unfold upper
  linarith

/-- s is the square root of n-1 for the fixed-order bound in the paper proof. -/
theorem fixed_upper {c e g t s : ℝ} (hc : 0 ≤ c) (he : 0 ≤ e) (ht : 1 ≤ t)
    (hn : t ≤ s) (hg : t^2 ≤ g^2) (hr : c ≤ rangeBound (t^2))
    (hcov : (Real.sqrt (1+c)-1)^2 ≤ c*e) :
    (c-e)/g^2 ≤ upper s ∧ upper s < 1/4 :=
  ⟨(clark_envelope hc he ht hg hr hcov).trans (upper_monotone ht hn),
    upper_lt_quarter (ht.trans hn)⟩

/-- The lower constant is absolute and need not be sharp. -/
theorem lower_bound {g c e : ℝ} (hg : 1 ≤ g) (hc : 0 ≤ c)
    (he : e ≤ (g-1)^2/(4*g)) :
    -(1:ℝ)/27 ≤ (c-e)/g^2 := by
  have hg0 : 0 < g := by linarith
  have h := (le_div_iff₀ (by positivity : 0 < 4*g)).1 he
  apply (le_div_iff₀ (by positivity : 0 < g^2)).2
  by_contra! hh
  have hx := mul_lt_mul_of_pos_right hh hg0
  nlinarith [mul_nonneg (sq_nonneg (g-3)) (show 0 ≤ 4*g-3 by linarith),
    mul_nonneg hc hg0.le]

end Clark
