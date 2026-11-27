import GraphQuarter
import Scalar
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-! Connected simple graphs asymptotically attaining the uniform lower bound
in Clark's problem. There are four equally large layers and a slot label
(block,position) in each. The first layer is a clique. Each of the three
other layers is complete multipartite with parts of size three. Each vertex
outside the first layer is matched to the first-layer vertex in its slot. -/
namespace Clark

/-- Uniform lower bound, for actual vectors on a finite vertex set. -/
theorem graph_lower {V : Type*} [Fintype V] [Nonempty V] (A : V → V → ℝ) (x : V → ℝ)
    {g : ℝ} (hg : 1 ≤ g) (hx : ∀ i, 1 ≤ x i ∧ x i ≤ g) :
    -(1:ℝ)/27 ≤ (dispersion (degree A) - dispersion x)/g^2 := by
  apply lower_bound hg (dispersion_nonneg _)
  simpa using dispersion_le_range x (by norm_num : (0:ℝ) < 1) (by linarith : 0 < g) hx

end Clark

namespace Clark.LowerFamily

open scoped BigOperators

abbrev Slot (k : ℕ) := Fin (k+1) × Fin 3
abbrev Vertex (k : ℕ) := Fin 4 × Slot k

def indicator {T : Type*} [DecidableEq T] (i j : T) : ℝ := if j=i then 1 else 0

noncomputable def size (k : ℕ) : ℝ := 3*((k:ℝ)+1)

noncomputable def adjacency {k : ℕ} (u v : Vertex k) : ℝ :=
  if u.1=v.1 then
    if u.1=0 then 1-indicator u.2 v.2
    else 1-indicator u.2.1 v.2.1
  else if u.1=0 ∨ v.1=0 then indicator u.2 v.2
  else 0

noncomputable def profile {k : ℕ} (a b : ℝ) (u : Vertex k) : ℝ :=
  if u.1=0 then a else b

private theorem sum_ind {T : Type*} [Fintype T] [DecidableEq T] (i : T) :
    ∑ j, indicator i j = 1 := by classical simp [indicator]

private theorem sum_slot_const (k : ℕ) (a : ℝ) :
    (∑ _ : Slot k, a) = size k*a := by
  simp [size, Fintype.card_prod, nsmul_eq_mul]
  <;> ring

private theorem sum_block_ind {k : ℕ} (i : Slot k) :
    ∑ j : Slot k, indicator i.1 j.1 = 3 := by
  rw [Fintype.sum_prod_type]
  have H (g : Fin (k+1)) : (∑ _ : Fin 3, indicator i.1 g) =
      if g=i.1 then 3 else 0 := by
    by_cases e : g=i.1 <;> simp [indicator,e]
  simp only [H]
  simp

private theorem row_block {k : ℕ} (a b : Fin 4) (i : Slot k) :
    ∑ j : Slot k, adjacency (a,i) (b,j) =
      if a=b then (if a=0 then size k-1 else size k-3)
      else if a=0 ∨ b=0 then 1 else 0 := by
  by_cases h : a=b <;> by_cases h0 : a=0 <;> by_cases h1 : b=0 <;>
    simp [adjacency, h, h0, h1, Finset.sum_sub_distrib, sum_slot_const,
      sum_ind, sum_block_ind]

/-- Matrix multiplication on a profile constant in each type of layer. -/
theorem row_profile {k : ℕ} (a b : ℝ) (u : Vertex k) :
    ∑ v, adjacency u v * profile a b v =
    profile ((size k-1)*a+3*b) (a+(size k-3)*b) u := by
  obtain ⟨s,i⟩ := u
  rw [Fintype.sum_prod_type]
  have expand (r : Fin 4) : (∑ j : Slot k, adjacency (s,i) (r,j) * profile a b (r,j)) =
      (if s=r then (if s=0 then size k-1 else size k-3)
       else if s=0 ∨ r=0 then 1 else 0) * (if r=0 then a else b) := by
    simp only [profile, ← Finset.sum_mul, row_block]
  simp only [expand, Fin.sum_univ_four]
  fin_cases s <;> norm_num [profile] <;> ring

theorem degree_formula {k : ℕ} (u : Vertex k) :
    Clark.degree adjacency u = profile (size k+2) (size k-2) u := by
  have hh := row_profile 1 1 u
  simp only [profile, ite_self, mul_one] at hh
  unfold Clark.degree profile
  split <;> rename_i H <;> simp [H] at hh <;> linarith

theorem eigen_formula {k : ℕ} (u : Vertex k) :
    ∑ v, adjacency u v * profile 3 1 v = size k * profile 3 1 u := by
  rw [row_profile]
  unfold profile
  split <;> ring

private theorem profile_mean {k : ℕ} (a b : ℝ) :
    Clark.mean (profile (k:=k) a b) = (a+3*b)/4 := by
  unfold Clark.mean
  rw [Fintype.sum_prod_type, Fin.sum_univ_four]
  simp [profile, size, Fintype.card_prod, nsmul_eq_mul]
  <;> field_simp
  <;> ring

private theorem profile_disp {k : ℕ} (a b : ℝ) :
    Clark.dispersion (profile (k:=k) a b) =
    3*(a-b)^2/(a+3*b)^2 := by
  unfold Clark.dispersion
  rw [profile_mean]
  have E : (fun i : Vertex k => (profile a b i - (a+3*b)/4)^2) =
      profile (k:=k) ((a-(a+3*b)/4)^2) ((b-(a+3*b)/4)^2) := by
    funext i
    by_cases h : i.1=0 <;> simp [profile,h]
  rw [E, profile_mean]
  by_cases h : a+3*b=0
  · simp [h]
  · field_simp
    <;> ring

/-- The increasingly dense family has a fixed principal ratio of 3 and
attains values arbitrarily close to the bound -1/27. -/
theorem gamma_formula (k : ℕ) :
    (Clark.dispersion (Clark.degree (adjacency (k:=k))) -
      Clark.dispersion (profile (k:=k) 3 1))/3^2 =
        -(1:ℝ)/27 + 1/(3*(size k-1)^2) := by
  have d : Clark.degree (adjacency (k:=k)) =
      profile (k:=k) (size k+2) (size k-2) := funext degree_formula
  rw [d, profile_disp, profile_disp]
  have s : 3 ≤ size k := by
    have hk : (0:ℝ) ≤ k := by positivity
    unfold size
    linarith
  have h : size k+2+3*(size k-2) ≠ 0 := by linarith
  have h' : size k-1 ≠ 0 := by linarith
  field_simp [h,h']
  <;> ring

#print axioms eigen_formula
#print axioms gamma_formula

end Clark.LowerFamily
