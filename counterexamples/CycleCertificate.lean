import Std

/-! Cycles, vertex clique covers, and the round-by-round graph burning process.
Vertex labels are the natural numbers strictly below the cycle order. -/
namespace CycleCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def Adj (n u v : Nat) : Prop :=
  u < n ∧ v < n ∧ (u + 1 = v ∨ v + 1 = u ∨
    (u = 0 ∧ v + 1 = n) ∨ (v = 0 ∧ u + 1 = n))

instance (n u v : Nat) : Decidable (Adj n u v) := by unfold Adj; infer_instance

theorem symmetric {n u v : Nat} (h : Adj n u v) : Adj n v u := by
  unfold Adj at *
  omega

theorem loopless {n : Nat} (hn : 4 ≤ n) (u : Nat) : ¬ Adj n u u := by
  unfold Adj
  omega

theorem nontrivial {n : Nat} (hn : 4 ≤ n) : 0 < n ∧ 1 < n ∧ (0 : Nat) ≠ 1 := by omega

inductive Reaches (n : Nat) : Nat → Nat → Prop
  | refl {u} : u < n → Reaches n u u
  | edge {u v} : Adj n u v → Reaches n u v
  | trans {u v w} : Reaches n u v → Reaches n v w → Reaches n u w

theorem reaches_symm {n u v : Nat} (h : Reaches n u v) : Reaches n v u := by
  induction h with
  | refl hu => exact .refl hu
  | edge ha => exact .edge (symmetric ha)
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁

private theorem from_zero (n v : Nat) (hv : v < n) : Reaches n 0 v := by
  induction v with
  | zero => exact .refl hv
  | succ j ih =>
    exact .trans (ih (by omega)) (.edge (by unfold Adj; omega))

theorem connected {n u v : Nat} (hu : u < n) (hv : v < n) : Reaches n u v :=
  .trans (reaches_symm (from_zero n u hu)) (from_zero n v hv)

/-- Each vertex has exactly two distinct neighbors, both in the graph. -/
theorem two_regular {n u : Nat} (hn : 4 ≤ n) (hu : u < n) :
    ∃ a b : Nat, a < n ∧ b < n ∧ a ≠ b ∧ ∀ v : Nat, Adj n u v ↔ v = a ∨ v = b := by
  by_cases hz : u = 0
  · refine ⟨1, n-1, by omega, by omega, by omega, ?_⟩
    intro v; unfold Adj; omega
  · by_cases hl : u + 1 = n
    · refine ⟨u-1, 0, by omega, by omega, by omega, ?_⟩
      intro v; unfold Adj; omega
    · refine ⟨u-1, u+1, by omega, by omega, by omega, ?_⟩
      intro v; unfold Adj; omega

/-- Every three neighbors include two equal vertices. In particular, no
vertex can be the center of an induced claw, and each degree is at most 3. -/
theorem no_three_neighbors {n u a b c : Nat} (hn : 4 ≤ n)
    (ha : Adj n u a) (hb : Adj n u b) (hc : Adj n u c) : a = b ∨ a = c ∨ b = c := by
  obtain ⟨x, y, _, _, _, h⟩ := two_regular hn ha.1
  have ha' := (h a).1 ha
  have hb' := (h b).1 hb
  have hc' := (h c).1 hc
  omega

/-- No four distinct neighbors, which is the maximum-degree-at-most-three condition. -/
theorem subcubic {n u a b c d : Nat} (hn : 4 ≤ n)
    (ha : Adj n u a) (hb : Adj n u b) (hc : Adj n u c) (_hd : Adj n u d) :
    a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by
  have := no_three_neighbors hn ha hb hc
  omega

/-- There cannot be an induced claw: three distinct leaves with this center
already contradict degree two, independently of the edges among the leaves. -/
theorem claw_free {n u a b c : Nat} (hn : 4 ≤ n)
    (ha : Adj n u a) (hb : Adj n u b) (hc : Adj n u c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  have := no_three_neighbors hn ha hb hc
  omega

def nextVertex (n i : Nat) : Nat := if i + 1 < n then i + 1 else 0

/-- The edge traversed at time i on the tour 0,1,...,n-1,0, without orientation. -/
def TourEdge (n i u v : Nat) : Prop :=
  i < n ∧ ((u = i ∧ v = nextVertex n i) ∨ (v = i ∧ u = nextVertex n i))

theorem tour_edge {n i : Nat} (hn : 4 ≤ n) (hi : i < n) : Adj n i (nextVertex n i) := by
  unfold Adj nextVertex
  split <;> omega

theorem tour_consecutive {n i : Nat} (hi : i+1 < n) : nextVertex n i = i+1 := by
  simp [nextVertex, hi]

theorem tour_closes {n : Nat} (hn : 4 ≤ n) : nextVertex n (n-1) = 0 := by
  unfold nextVertex
  split <;> omega

private theorem tour_covers {n u v : Nat} (h : Adj n u v) : ∃ i, TourEdge n i u v := by
  obtain ⟨hu, hv, h | h | h | h⟩ := h
  · exact ⟨u, hu, Or.inl ⟨rfl, by rw [nextVertex, if_pos (show u+1<n by omega), h]⟩⟩
  · exact ⟨v, hv, Or.inr ⟨rfl, by rw [nextVertex, if_pos (show v+1<n by omega), h]⟩⟩
  · exact ⟨v, hv, Or.inr ⟨rfl, by simp [nextVertex, show ¬v+1<n by omega, h.1]⟩⟩
  · exact ⟨u, hu, Or.inl ⟨rfl, by simp [nextVertex, show ¬u+1<n by omega, h.1]⟩⟩

private theorem tour_unique {n i j u v : Nat} (hn : 4 ≤ n)
    (hi : TourEdge n i u v) (hj : TourEdge n j u v) : j = i := by
  by_cases ci : i+1 < n <;> by_cases cj : j+1 < n <;>
    simp only [TourEdge, nextVertex, ci, cj, if_true, if_false] at hi hj <;> omega

/-- Every edge is traversed exactly once on the explicit closed tour above. -/
theorem eulerian {n : Nat} (hn : 4 ≤ n) {u v : Nat} (ha : Adj n u v) :
    ∃ i, TourEdge n i u v ∧ ∀ j, TourEdge n j u v → j = i := by
  obtain ⟨i, hi⟩ := tour_covers ha
  exact ⟨i, hi, fun _ hj => tour_unique hn hi hj⟩

theorem triangle_free {n x y z : Nat} (hn : 4 ≤ n)
    (a : Adj n x y) (b : Adj n x z) (c : Adj n y z) : False := by
  unfold Adj at *
  omega

/-- Pairwise adjacency excludes repetitions. Vertex bounds are included for
singleton cliques, for which the pairwise condition is vacuous. -/
def Clique (n : Nat) (xs : List Nat) : Prop :=
  (∀ x ∈ xs, x < n) ∧ xs.Pairwise (Adj n)

theorem clique_small {n : Nat} (hn : 4 ≤ n) {xs : List Nat} (h : Clique n xs) : xs.length ≤ 2 := by
  cases xs with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y xs =>
      cases xs with
      | nil => simp
      | cons z rest =>
        have a : Adj n x y := List.rel_of_pairwise_cons h.2 (by simp)
        have b : Adj n x z := List.rel_of_pairwise_cons h.2 (by simp)
        have c : Adj n y z := List.rel_of_pairwise_cons h.2.of_cons (by simp)
        exact False.elim (triangle_free hn a b c)

private theorem count_distinct (xs ys : List Nat) (hd : xs.Nodup)
    (hs : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hd
    have hxy := hs x (by simp)
    have he : ∀ y ∈ xs, y ∈ ys.erase x := by
      intro y hy
      have hne : y ≠ x := fun h => hx (h ▸ hy)
      exact (List.mem_erase_of_ne hne).2 (hs y (List.mem_cons_of_mem _ hy))
    have shorter := ih (ys.erase x) hxs he
    have herase := List.length_erase_of_mem hxy
    have positive : 0 < ys.length := by cases ys <;> simp_all
    simp only [List.length_cons]
    omega

def CliqueCover (n : Nat) (cs : List (List Nat)) : Prop :=
  (∀ c ∈ cs, Clique n c) ∧ ∀ x, x < n → x ∈ cs.flatten

private theorem flatten_bound {n : Nat} (hn : 4 ≤ n) (cs : List (List Nat))
    (h : ∀ c ∈ cs, Clique n c) : cs.flatten.length ≤ 2 * cs.length := by
  induction cs with
  | nil => decide
  | cons c cs ih =>
    have hc := clique_small hn (h c (by simp))
    have ht := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem clique_cover_lower {n : Nat} (hn : 4 ≤ n) {cs : List (List Nat)} (h : CliqueCover n cs) :
    n ≤ 2 * cs.length := by
  have hle := count_distinct (List.range n) cs.flatten List.nodup_range
    (fun x hx => h.2 x (List.mem_range.mp hx))
  rw [List.length_range] at hle
  exact Nat.le_trans hle (flatten_bound hn _ h.1)

theorem ceil_half_le {n : Nat} (hn : 4 ≤ n) {cs : List (List Nat)} (h : CliqueCover n cs) :
    (n+1)/2 ≤ cs.length := by
  have := clique_cover_lower hn h
  omega

/-- Every burning vertex stays burning, and every neighbor of an already
burning vertex catches fire during this round. -/
def spread (n : Nat) (seen : List Nat) : List Nat :=
  (List.range n).filter (fun v => decide (v ∈ seen) || seen.any (fun w => decide (Adj n w v)))

theorem mem_spread (n v : Nat) (seen : List Nat) :
    v ∈ spread n seen ↔ v < n ∧ (v ∈ seen ∨ ∃ w ∈ seen, Adj n w v) := by
  simp [spread, List.any_eq_true, Bool.or_eq_true_iff]

/-- Check that the new ignition was not burned at the end of the previous
round. Both the new ignition and the spread occur in the present round. -/
def run (n : Nat) : List Nat → List Nat → Option (List Nat)
  | [], seen => some seen
  | u :: rest, seen =>
    if u < n ∧ u ∉ seen then run n rest (u :: spread n seen) else none

def successful (n : Nat) (sources : List Nat) : Bool :=
  match run n sources [] with
  | none => false
  | some burned => (List.range n).all (fun v => decide (v ∈ burned))

/-- Existence of a legal complete schedule with this number of rounds. -/
def BurnableIn (n k : Nat) : Prop := ∃ s : List Nat, s.length = k ∧ successful n s = true

theorem burnable_by {n : Nat} {s : List Nat} (h : successful n s = true) : BurnableIn n s.length :=
  ⟨s, rfl, h⟩

/-- For a nondecreasing f, θ(G) ≤ f(b(G)) implies this statement by taking
a minimum cover and using b(G) ≤ the length of every successful schedule. -/
def BoundAt (n : Nat) (f : Nat → Nat) : Prop :=
  ∀ s : List Nat, successful n s = true → ∃ cs, CliqueCover n cs ∧ cs.length ≤ f s.length

theorem refute (n : Nat) (sources : List Nat) (f : Nat → Nat) (hn : 4 ≤ n)
    (hb : successful n sources = true) (hgap : 2 * f sources.length < n) : ¬ BoundAt n f := by
  intro claimed
  obtain ⟨cs, hcs, hlen⟩ := claimed sources hb
  have := clique_cover_lower hn hcs
  omega

def IsBurningNumber (n b : Nat) : Prop :=
  BurnableIn n b ∧ ∀ k, BurnableIn n k → b ≤ k

def IsCliqueCoverNumber (n t : Nat) : Prop :=
  (∃ cs, CliqueCover n cs ∧ cs.length = t) ∧ ∀ cs, CliqueCover n cs → t ≤ cs.length

theorem optimum_fails {n b t : Nat} {f : Nat → Nat}
    (mono : ∀ x y, x ≤ y → f x ≤ f y) (hc : IsCliqueCoverNumber n t)
    (hb : IsBurningNumber n b) (bad : ¬ BoundAt n f) : ¬ t ≤ f b := by
  intro h
  apply bad
  intro s hs
  obtain ⟨cs, hcs, ht⟩ := hc.1
  refine ⟨cs, hcs, ?_⟩
  rw [ht]
  exact Nat.le_trans h (mono _ _ (hb.2 _ (burnable_by hs)))

/-- A realized natural-number objective has a least realized value.
Induct on a known bound for one realization. -/
private theorem least_realized (P : Nat → Prop) (m : Nat) :
    (∃ j, j ≤ m ∧ P j) → ∃ k, P k ∧ ∀ j, P j → k ≤ j := by
  classical
  induction m with
  | zero =>
    intro h
    obtain ⟨j, hj, hp⟩ := h
    exact ⟨j, hp, fun _ _ => by omega⟩
  | succ m ih =>
    intro h
    by_cases earlier : ∃ j, j ≤ m ∧ P j
    · exact ih earlier
    · obtain ⟨j, hj, hp⟩ := h
      refine ⟨j, hp, ?_⟩
      intro t ht
      by_cases hle : j ≤ t
      · exact hle
      · exact False.elim (earlier ⟨t, by omega, ht⟩)

private theorem singleton_cover (n : Nat) :
    CliqueCover n ((List.range n).map (fun x => [x])) := by
  constructor
  · intro c hc
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hc
    subst c
    constructor
    · intro x hx
      have heq : x = y := by simpa using hx
      rw [heq]
      exact List.mem_range.mp hy
    · simp
  · intro x hx
    exact List.mem_flatten.mpr ⟨[x], List.mem_map.mpr ⟨x, List.mem_range.mpr hx, rfl⟩, by simp⟩

/-- Existence of both true optima, from an actual burning schedule and the
cover consisting of all singleton vertices. -/
theorem exists_optima_of_success {n : Nat} {sources : List Nat}
    (hb : successful n sources = true) :
    ∃ t b, IsCliqueCoverNumber n t ∧ IsBurningNumber n b := by
  obtain ⟨b, hb₁, hb₂⟩ := least_realized (BurnableIn n) sources.length
    ⟨sources.length, Nat.le_refl _, burnable_by hb⟩
  let base := (List.range n).map (fun x => [x])
  have hbase : CliqueCover n base := singleton_cover n
  obtain ⟨t, ht₁, ht₂⟩ := least_realized
    (fun k => ∃ cs : List (List Nat), CliqueCover n cs ∧ cs.length = k)
    base.length ⟨base.length, Nat.le_refl _, base, hbase, rfl⟩
  exact ⟨t, b, ⟨ht₁, fun cs hcs => ht₂ cs.length ⟨cs, hcs, rfl⟩⟩, ⟨hb₁, hb₂⟩⟩

theorem exists_optima_violation (n : Nat) (sources : List Nat) (f : Nat → Nat) (hn : 4 ≤ n)
    (hb : successful n sources = true) (hgap : 2 * f sources.length < n)
    (mono : ∀ x y : Nat, x ≤ y → f x ≤ f y) :
    ∃ b t, IsBurningNumber n b ∧ IsCliqueCoverNumber n t ∧ f b < t := by
  obtain ⟨t, b, hc, hburn⟩ := exists_optima_of_success hb
  have bad := optimum_fails mono hc hburn (refute n sources f hn hb hgap)
  exact ⟨b, t, hburn, hc, by omega⟩

/-- The graph hypotheses used by the three catalogue rows. Eulerianity is
witnessed by the specific closed tour 0,1,...,n-1,0. -/
structure CycleGraphHypotheses (n : Nat) : Prop where
  undirected : ∀ u v, Adj n u v → Adj n v u
  noLoops : ∀ u, ¬ Adj n u u
  atLeastTwo : 0 < n ∧ 1 < n ∧ (0 : Nat) ≠ 1
  connectedGraph : ∀ u v, u < n → v < n → Reaches n u v
  regularGraph : ∀ u, u < n → ∃ a b : Nat, a < n ∧ b < n ∧ a ≠ b ∧
    ∀ v, Adj n u v ↔ v = a ∨ v = b
  subcubicGraph : ∀ u a b c d, Adj n u a → Adj n u b → Adj n u c → Adj n u d →
    a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d
  clawFreeGraph : ∀ u a b c, Adj n u a → Adj n u b → Adj n u c →
    a ≠ b → a ≠ c → b ≠ c → False
  tourAdjacent : ∀ i, i < n → Adj n i (nextVertex n i)
  tourNext : ∀ i, i+1 < n → nextVertex n i = i+1
  tourClosed : nextVertex n (n-1) = 0
  eulerianGraph : ∀ u v, Adj n u v → ∃ i, TourEdge n i u v ∧
    ∀ j, TourEdge n j u v → j = i

theorem cycle_graph_hypotheses {n : Nat} (hn : 4 ≤ n) : CycleGraphHypotheses n where
  undirected := fun _ _ h => symmetric h
  noLoops := loopless hn
  atLeastTwo := nontrivial hn
  connectedGraph := fun _ _ hu hv => connected hu hv
  regularGraph := fun _ hu => two_regular hn hu
  subcubicGraph := fun _ _ _ _ _ ha hb hc hd => subcubic hn ha hb hc hd
  clawFreeGraph := fun _ _ _ _ ha hb hc hab hac hbc => claw_free hn ha hb hc hab hac hbc
  tourAdjacent := fun _ hi => tour_edge hn hi
  tourNext := fun _ hi => tour_consecutive hi
  tourClosed := tour_closes hn
  eulerianGraph := fun _ _ h => eulerian hn h

end CycleCertificate
