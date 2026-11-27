import Mathlib.Data.Real.Archimedean
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
  have dim : ((k:ℝ)+1)*3 = size k := by unfold size; ring
  by_cases h : a=b <;> by_cases h0 : a=0 <;> by_cases h1 : b=0 <;>
    simp [adjacency, h, h0, h1, Finset.sum_sub_distrib, dim,
      sum_ind, sum_block_ind, mul_comm]

/-- Matrix multiplication on a profile constant in each type of layer. -/
theorem row_profile {k : ℕ} (a b : ℝ) (u : Vertex k) :
    ∑ v, adjacency u v * profile a b v =
    profile ((size k-1)*a+3*b) (a+(size k-3)*b) u := by
  obtain ⟨s,i⟩ := u
  rw [Fintype.sum_prod_type]
  have expand (r : Fin 4) : (∑ j : Slot k, adjacency (s,i) (r,j) * profile a b (r,j)) =
      (if s=r then (if s=0 then size k-1 else size k-3)
       else if s=0 ∨ r=0 then 1 else 0) * (if r=0 then a else b) := by
    change (∑ j : Slot k, adjacency (s,i) (r,j) * (if r=0 then a else b)) = _
    rw [← Finset.sum_mul, row_block]
  simp only [expand, Fin.sum_univ_four]
  fin_cases s <;> simp (config := { decide := true }) [profile] <;> ring

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

/-- Every entry is 0 or 1, the diagonal is zero, and the adjacency matrix is
symmetric. -/
theorem simple_undirected {k : ℕ} (u v : Vertex k) :
    (adjacency u v = 0 ∨ adjacency u v = 1) ∧
    adjacency u u = 0 ∧ adjacency u v = adjacency v u := by
  obtain ⟨s,i⟩ := u
  obtain ⟨r,j⟩ := v
  have diag : adjacency (s,i) (s,i) = 0 := by by_cases h : s=0 <;> simp [adjacency,indicator,h]
  refine ⟨?_,diag,?_⟩
  · unfold adjacency indicator
    split_ifs <;> norm_num
  · by_cases hs : s=r
    · subst r
      by_cases h : s=0 <;> simp [adjacency, indicator, h, eq_comm]
    · simp [adjacency, indicator, hs, Ne.symm hs, or_comm, eq_comm]

/-- Walk through the high-layer vertices in the two prescribed slots.
Repeated successive vertices can be omitted. -/
theorem connected_walk {k : ℕ} (u v : Vertex k) :
    ∃ a b : Vertex k, (u=a ∨ adjacency u a=1) ∧
      (a=b ∨ adjacency a b=1) ∧ (b=v ∨ adjacency b v=1) := by
  obtain ⟨s,i⟩ := u
  obtain ⟨r,j⟩ := v
  refine ⟨(0,i),(0,j),?_,?_,?_⟩
  · by_cases e : s=0
    · subst s; exact Or.inl rfl
    · right; simp [adjacency,indicator,e]
  · by_cases e : i=j
    · subst j; exact Or.inl rfl
    · right; simp [adjacency,indicator,e,Ne.symm e]
  · by_cases e : r=0
    · subst r; exact Or.inl rfl
    · right; simp [adjacency,indicator,e,Ne.symm e]

/-- The normed Perron vector has both extreme entries. -/
theorem profile_range (k : ℕ) :
    (∀ i : Vertex k, 1 ≤ profile 3 1 i ∧ profile 3 1 i ≤ 3) ∧
    (∃ i : Vertex k, profile 3 1 i = 1) ∧ (∃ i : Vertex k, profile 3 1 i = 3) := by
  refine ⟨?_, ⟨(1,0,0),by norm_num [profile]⟩, ⟨(0,0,0),by norm_num [profile]⟩⟩
  intro i
  by_cases h : i.1=0 <;> norm_num [profile,h]

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

/-- Every proposed larger uniform lower bound fails for a member of the
explicit connected family. -/
theorem lower_sharp {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, (Clark.dispersion (Clark.degree (adjacency (k:=k))) -
      Clark.dispersion (profile (k:=k) 3 1))/3^2 < -(1:ℝ)/27+ε := by
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ε)
  refine ⟨k,?_⟩
  rw [gamma_formula]
  have h1 : 1 < (k:ℝ)*ε := (div_lt_iff₀ hε).1 hk
  have k0 : (0:ℝ) ≤ k := by positivity
  have h2 : (k:ℝ) ≤ 3*(size k-1)^2 := by
    unfold size
    nlinarith [sq_nonneg (k:ℝ)]
  have h3 := mul_le_mul_of_nonneg_right h2 hε.le
  have hpos : 0 < 3*(size k-1)^2 := by
    have ht : 0 < size k-1 := by unfold size; linarith
    positivity
  have hi : 1/(3*(size k-1)^2) < ε := (div_lt_iff₀ hpos).2 (by nlinarith)
  linarith

#print axioms lower_sharp

#print axioms connected_walk
#print axioms simple_undirected
#print axioms profile_range
#print axioms eigen_formula
#print axioms gamma_formula

end Clark.LowerFamily
