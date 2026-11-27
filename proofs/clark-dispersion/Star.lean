import GraphQuarter
import Scalar
import Mathlib.Data.Fintype.BigOperators

/-! Clark's dispersion envelope is attained by the star on a hub and m leaves. -/
namespace Clark
open scoped BigOperators

def starAdjacency (m : ℕ) : Option (Fin m) → Option (Fin m) → ℝ
  | none, some _ | some _, none => 1
  | _, _ => 0

private def levels (m : ℕ) (hub leaf : ℝ) : Option (Fin m) → ℝ
  | none => hub
  | some _ => leaf

noncomputable def starVector (m : ℕ) := levels m (Real.sqrt m) 1

theorem star_degree (m : ℕ) :
    degree (starAdjacency m) = levels m (m : ℝ) 1 := by
  funext i
  cases i <;> simp [degree, Fintype.sum_option, starAdjacency, levels]

theorem star_eigen (m : ℕ) (i : Option (Fin m)) :
    ∑ j, starAdjacency m i j * starVector m j = Real.sqrt m * starVector m i := by
  have sq := Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  cases i <;> simp [Fintype.sum_option, starAdjacency, starVector, levels] <;> nlinarith

/-- The positive eigenvector attains both 1 and sqrt m, so its principal ratio is sqrt m. -/
theorem star_extrema (m : ℕ) (hm : 1 ≤ m) :
    (∀ i, 1 ≤ starVector m i ∧ starVector m i ≤ Real.sqrt m) ∧
    (∃ i, starVector m i = 1) ∧ (∃ i, starVector m i = Real.sqrt m) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ht : (1 : ℝ) ≤ Real.sqrt m := Real.le_sqrt_of_sq_le (by simpa using hm')
  refine ⟨?_, ⟨some ⟨0, by omega⟩, rfl⟩, ⟨none, rfl⟩⟩
  intro i
  cases i <;> simp [starVector, levels, ht]

private theorem mean_levels (m : ℕ) (u v : ℝ) :
    mean (levels m u v) = (u + (m : ℝ)*v)/(m+1) := by
  simp [mean, Fintype.sum_option, levels, nsmul_eq_mul]

private theorem dispersion_levels (m : ℕ) (u : ℝ) (hu : 0 < u) :
    dispersion (levels m u 1) = (m:ℝ)*(u-1)^2/(u+m)^2 := by
  have sq : (fun i => levels m u 1 i ^ 2) = levels m (u^2) 1 := by
    funext i
    cases i <;> simp [levels]
  unfold dispersion
  rw [variance_eq, sq, mean_levels, mean_levels]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h₁ : (m:ℝ)+1 ≠ 0 := by positivity
  have h₂ : u+(m:ℝ) ≠ 0 := by positivity
  simp only [mul_one]
  field_simp [h₁, h₂] <;> ring

/-- For the actual adjacency and positive eigenvector of K(1,m),
the normalized difference is exactly the universal envelope. -/
theorem star_attains (m : ℕ) (hm : 1 ≤ m) :
    (dispersion (degree (starAdjacency m)) - dispersion (starVector m)) /
      (Real.sqrt m)^2 = upper (Real.sqrt m) := by
  have hp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have ht : 0 < Real.sqrt (m:ℝ) := Real.sqrt_pos.2 hp
  rw [star_degree, starVector, dispersion_levels m m hp, dispersion_levels m _ ht]
  generalize hs : Real.sqrt (m : ℝ) = t at ht ⊢
  have hsq : (m:ℝ) = t^2 := by rw [← hs, Real.sq_sqrt hp.le]
  rw [hsq]
  unfold upper
  have h₁ : t^2+t^2 ≠ 0 := by positivity
  have h₂ : t+t^2 ≠ 0 := by positivity
  have h₃ : t+1 ≠ 0 := by positivity
  field_simp [ht.ne', h₁, h₂, h₃] <;> ring

#print axioms star_eigen
#print axioms star_extrema
#print axioms star_attains

end Clark
