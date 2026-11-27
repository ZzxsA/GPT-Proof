import GraphQuarter
import Scalar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Sharp fixed-order bounds from the entries of a symmetric adjacency matrix.
The positive eigenpair is supplied explicitly, so the same calculation applies
to weighted undirected graphs. -/
namespace Clark

open scoped BigOperators

variable {V : Type*} [Fintype V] [Nonempty V]

private theorem mean_pair_sq (y z : V → ℝ) :
    mean (fun i => y i * z i) ^ 2 ≤
      mean (fun i => y i ^ 2) * mean (fun i => z i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y z
  unfold mean
  rw [div_pow, div_mul_div_comm, ← pow_two]
  exact div_le_div_of_nonneg_right h (sq_nonneg _)

private theorem covariance_eq (y z : V → ℝ) :
    mean (fun i => (y i - mean y) * (z i - mean z)) =
      mean (fun i => y i * z i) - mean y * mean z := by
  calc
    _ = mean (fun i => (y i*z i - mean y*z i) - mean z*y i + mean y*mean z) := by
      congr 1
      funext i
      ring
    _ = _ := by rw [mean_add, mean_sub, mean_sub, mean_scale, mean_scale, mean_const]; ring

private theorem degree_product (A : V → V → ℝ) (x : V → ℝ) {ρ : ℝ}
    (symm : ∀ i j, A i j = A j i)
    (eigen : ∀ i, ∑ j, A i j * x j = ρ * x i) :
    mean (fun i => degree A i * x i) = ρ * mean x := by
  rw [← mean_scale]
  unfold mean
  congr 1
  simp only [degree, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ i, A j i * x i := Finset.sum_congr rfl (fun i _ => by rw [symm i j])
    _ = _ := eigen j

theorem hofmeister (A : V → V → ℝ) (x : V → ℝ) {ρ : ℝ}
    (symm : ∀ i j, A i j = A j i) (hA : ∀ i j, 0 ≤ A i j)
    (hx : ∀ i, 0 < x i)
    (eigen : ∀ i, ∑ j, A i j * x j = ρ * x i) :
    mean (fun i => (degree A i)^2) ≤ ρ^2 := by
  have row (i : V) : (degree A i)^2 ≤ ρ*x i * ∑ j, A i j / x j := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (r := A i) (f := fun j => A i j * x j) (g := fun j => A i j / x j)
      (fun j _ => mul_nonneg (hA i j) (hx j).le)
      (fun j _ => div_nonneg (hA i j) (hx j).le)
      (fun j _ => by field_simp [(hx j).ne']; ring)
    rw [eigen i] at h
    exact h
  have total : (∑ i, ρ*x i * ∑ j, A i j / x j) = ∑ _ : V, ρ^2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = ∑ i, (ρ / x j) * (A j i * x i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [symm i j]
        ring
      _ = _ := by rw [← Finset.mul_sum, eigen j]; field_simp [(hx j).ne']; ring
  calc
    _ ≤ mean (fun i => ρ*x i * ∑ j, A i j / x j) := mean_mono row
    _ = mean (fun _ : V => ρ^2) := by unfold mean; rw [total]
    _ = _ := mean_const _

theorem spectral_coupling (A : V → V → ℝ) (x : V → ℝ) {ρ : ℝ}
    (symm : ∀ i j, A i j = A j i) (hA : ∀ i j, 0 ≤ A i j)
    (hρ : 0 < ρ) (hx : ∀ i, 0 < x i)
    (hd : 0 < mean (degree A)) (hm : 0 < mean x)
    (eigen : ∀ i, ∑ j, A i j * x j = ρ * x i) :
    (Real.sqrt (1 + dispersion (degree A)) - 1)^2 ≤
      dispersion (degree A) * dispersion x := by
  let d := degree A
  change 0 < mean d at hd
  change (Real.sqrt (1 + dispersion d) - 1)^2 ≤ dispersion d * dispersion x
  have moment (y : V → ℝ) (hy : 0 < mean y) :
      dispersion y * (mean y)^2 = mean (fun i => (y i - mean y)^2) := by
    unfold dispersion
    field_simp [hy.ne']
  have hdvar := moment d hd
  have hxvar := moment x hm
  have hh := hofmeister A x symm hA hx eigen
  change mean (fun i => (d i)^2) ≤ ρ^2 at hh
  have hsecond := hdvar
  rw [variance_eq] at hsecond
  have hrms : 1 + dispersion d ≤ (ρ / mean d)^2 := by
    rw [div_pow]
    apply (le_div_iff₀ (by positivity : 0 < (mean d)^2)).2
    linarith [show (1+dispersion d)*(mean d)^2 = (mean d)^2 + dispersion d*(mean d)^2 by ring]
  have hs : Real.sqrt (1+dispersion d) ≤ ρ / mean d := by
    exact (Real.sqrt_le_iff).2 ⟨(div_pos hρ hd).le, hrms⟩
  have hs1 : 1 ≤ Real.sqrt (1+dispersion d) := by
    have h := Real.sqrt_le_sqrt (a := 1) (b := 1+dispersion d) (by linarith [dispersion_nonneg d])
    simpa using h
  have hcov := mean_pair_sq (fun i => d i - mean d) (fun i => x i - mean x)
  rw [covariance_eq, ← hdvar, ← hxvar] at hcov
  have hp : mean (fun i => d i*x i) = ρ*mean x := degree_product A x symm eigen
  rw [hp] at hcov
  have hprod : 0 < (mean d * mean x)^2 := by positivity
  have ratio : ρ / mean d - 1 = (ρ*mean x - mean d*mean x)/(mean d*mean x) := by
    field_simp [hd.ne', hm.ne']
  calc
    _ ≤ (ρ / mean d - 1)^2 := by
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    _ ≤ _ := by
      rw [ratio, div_pow]
      apply (div_le_iff₀ hprod).2
      calc
        _ ≤ _ := hcov
        _ = _ := by ring

/-- A fixed-order envelope. Here a and b are the attained least and greatest
degrees, and s is any upper bound on the square root of their ratio.
For an n-vertex connected simple graph one can take s = sqrt(n-1). -/
theorem graph_fixed_bound (A : V → V → ℝ) (x : V → ℝ) {ρ g a b s : ℝ}
    (symm : ∀ i j, A i j = A j i) (hA : ∀ i j, 0 ≤ A i j)
    (hρ : 0 < ρ) (hg : 1 ≤ g) (hx : ∀ i, 1 ≤ x i ∧ x i ≤ g)
    (eigen : ∀ i, ∑ j, A i j * x j = ρ*x i)
    (ha : 0 < a) (hab : a ≤ b) (bounds : ∀ i, a ≤ degree A i ∧ degree A i ≤ b)
    (lo : ∃ i, degree A i = a) (hi : ∃ i, degree A i = b)
    (hs : Real.sqrt (b/a) ≤ s) :
    (dispersion (degree A) - dispersion x) / g^2 ≤ upper s ∧ upper s < 1/4 := by
  have hb : 0 < b := ha.trans_le hab
  have hg0 : 0 < g := by linarith
  have hd : 0 < mean (degree A) := ha.trans_le (by
    simpa only [mean_const] using (mean_mono (y := fun _ : V => a)
      (z := degree A) (fun i => (bounds i).1)))
  have hm : 0 < mean x := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (by
    simpa only [mean_const] using (mean_mono (y := fun _ : V => (1:ℝ))
      (z := x) (fun i => (hx i).1)))
  have cov := spectral_coupling A x symm hA hρ (fun i => lt_of_lt_of_le zero_lt_one (hx i).1) hd hm eigen
  have br := dispersion_le_range (degree A) ha hb bounds
  have rr : 1 ≤ b/a := (le_div_iff₀ ha).2 (by linarith)
  have rt := Real.sq_sqrt (div_pos hb ha).le
  have ht : 1 ≤ Real.sqrt (b/a) := by simpa using (Real.sqrt_le_sqrt rr)
  have de := degree_interval A x hA hρ hg hx eigen
  obtain ⟨i, ei⟩ := lo
  obtain ⟨j, ej⟩ := hi
  have elo := (de i).1
  have ehi := (de j).2
  rw [ei] at elo
  rw [ej] at ehi
  have eg := (div_le_iff₀ hg0).1 elo
  have hgp : b/a ≤ g^2 := (div_le_iff₀ ha).2 (by
    nlinarith [mul_le_mul_of_nonneg_right eg hg0.le])
  apply fixed_upper (dispersion_nonneg _) (dispersion_nonneg _) ht hs
  · rwa [rt]
  · rw [rt]
    have eqv : rangeBound (b/a) = (b-a)^2/(4*a*b) := by
      unfold rangeBound
      field_simp [ha.ne', hb.ne']; ring
    rwa [eqv]
  · exact cov

#print axioms graph_fixed_bound

end Clark
