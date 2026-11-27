import Moments
import Star
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

namespace Clark
open scoped BigOperators
variable {V : Type*} [Fintype V] [Nonempty V]

/-- Every simple graph admitting a normalized positive adjacency eigenvector
of positive eigenvalue satisfies Clark's sharp fixed-order upper bound. In
particular, this applies to the Perron vector of every connected simple graph
of order at least two. -/
theorem simpleGraph_fixed_order (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) {ρ g : ℝ} (hρ : 0 < ρ) (hg : 1 ≤ g)
    (hx : ∀ i, 1 ≤ x i ∧ x i ≤ g)
    (eigen : ∀ i, ∑ j, G.adjMatrix ℝ i j * x j = ρ*x i) :
    (dispersion (fun i => (G.degree i : ℝ)) - dispersion x) / g^2 ≤
      upper (Real.sqrt (Fintype.card V - 1 : ℝ)) := by
  let A := G.adjMatrix ℝ
  have symm (i j : V) : A i j = A j i := by
    change (if G.Adj i j then (1:ℝ) else 0) = (if G.Adj j i then 1 else 0)
    by_cases h : G.Adj i j
    · simp [h, G.symm h]
    · have h' : ¬ G.Adj j i := fun e => h (G.symm e)
      simp [h, h']
  have hA (i j : V) : 0 ≤ A i j := by
    change 0 ≤ if G.Adj i j then (1:ℝ) else 0
    split <;> norm_num
  have deg (i : V) : degree A i = (G.degree i : ℝ) := by
    simpa [degree, A, Matrix.mulVec, dotProduct, Function.const] using
      (SimpleGraph.adjMatrix_mulVec_const_apply (G := G) (a := (1:ℝ)) (v := i))
  obtain ⟨i, hi⟩ := G.exists_minimal_degree_vertex
  obtain ⟨j, hj⟩ := G.exists_maximal_degree_vertex
  have dr := degree_interval A x hA hρ hg hx eigen
  have lo : degree A i = (G.minDegree:ℝ) := by rw [deg, hi]
  have high : degree A j = (G.maxDegree:ℝ) := by rw [deg, hj]
  have ha : 0 < (G.minDegree:ℝ) := by
    rw [← lo]
    exact (div_pos hρ (lt_of_lt_of_le zero_lt_one hg)).trans_le (dr i).1
  have hdegpos : 0 < G.minDegree := by exact_mod_cast ha
  have ha1 : (1:ℝ) ≤ G.minDegree := by exact_mod_cast hdegpos
  have hab : G.minDegree ≤ G.maxDegree := hi.trans_le (G.degree_le_maxDegree i)
  have hn : (G.maxDegree:ℝ) + 1 ≤ (Fintype.card V:ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt G.maxDegree_lt_card_verts
  have hh : (G.maxDegree:ℝ) / (G.minDegree:ℝ) ≤ (Fintype.card V:ℝ) - 1 := by
    calc
      _ ≤ (G.maxDegree:ℝ) / 1 := div_le_div_of_nonneg_left (by positivity) (by norm_num) ha1
      _ ≤ _ := by rw [div_one]; linarith
  have hbounds := graph_fixed_bound A x symm hA hρ hg hx eigen ha (by exact_mod_cast hab)
    (fun v => by rw [deg]; constructor
                 · exact_mod_cast G.minDegree_le_degree v
                 · exact_mod_cast G.degree_le_maxDegree v)
    ⟨i,lo⟩ ⟨j,high⟩ (Real.sqrt_le_sqrt hh)
  simpa only [show (fun i => (G.degree i : ℝ)) = degree A from funext (fun i => (deg i).symm)]
    using hbounds.1

/-- Comparison with the actual star on the same number of vertices. -/
theorem star_maximizes (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ)
    {ρ g : ℝ} (hρ : 0 < ρ) (hg : 1 ≤ g) (hx : ∀ i, 1 ≤ x i ∧ x i ≤ g)
    (eigen : ∀ i, ∑ j, G.adjMatrix ℝ i j * x j = ρ*x i) (m : ℕ)
    (hm : 1 ≤ m) (order : Fintype.card V = m+1) :
    (dispersion (fun i => (G.degree i : ℝ)) - dispersion x) / g^2 ≤
      (dispersion (degree (starAdjacency m)) - dispersion (starVector m)) /
      (Real.sqrt m)^2 := by
  have h := simpleGraph_fixed_order G x hρ hg hx eigen
  rw [star_attains m hm]
  simpa [order] using h

#print axioms star_maximizes
#print axioms simpleGraph_fixed_order
end Clark
