import Std

/-!
The Cartesian product of K₅ and K₂. Vertices 0–4 and 5–9 form two cliques,
and equal columns give the matching between them. Independent vertex sets
are arbitrary lists without repetitions; their order plays no role.
-/
namespace RookTen

abbrev V := Fin 10

def adj (u v : V) : Bool :=
  u != v && ((u.val / 5 == v.val / 5) || (u.val % 5 == v.val % 5))

def vertices : List V := [0,1,2,3,4,5,6,7,8,9]

theorem mem_vertices : ∀ v : V, v ∈ vertices := by decide

theorem vertices_nodup : vertices.Nodup := by decide

theorem adj_symm : ∀ u v : V, adj u v = adj v u := by decide

theorem adj_irrefl : ∀ u : V, adj u u = false := by decide

def Independent (xs : List V) : Prop :=
  xs.Nodup ∧ xs.Pairwise (fun u v => adj u v = false)

def neighborhood (xs : List V) : List V :=
  vertices.filter (fun v => xs.any (fun u => adj v u))

theorem mem_neighborhood {xs : List V} {v : V} :
    v ∈ neighborhood xs ↔ ∃ u ∈ xs, adj v u = true := by
  simp [neighborhood, mem_vertices, List.any_eq_true]

theorem neighbors_of_vertex : ∀ u : V, (vertices.filter (fun v => adj v u)).length = 5 := by
  decide

-- In a three-vertex set two vertices are in the same clique.
private theorem noIndependentTriple : ∀ u v w : V,
    ¬ (([u,v,w] : List V).Nodup ∧
        ([u,v,w] : List V).Pairwise (fun a b => adj a b = false)) := by
  decide

theorem independent_size : ∀ {xs : List V}, Independent xs → xs.length ≤ 2
  | [], _ => by decide
  | [_], _ => by decide
  | [_,_], _ => by decide
  | u :: v :: w :: tail, h => by
    have sub : ([u,v,w] : List V).Sublist (u :: v :: w :: tail) :=
      (((List.nil_sublist tail).cons₂ w).cons₂ v).cons₂ u
    exact False.elim (noIndependentTriple u v w
      ⟨List.Nodup.sublist sub h.1, List.Pairwise.sublist sub h.2⟩)

theorem independence_number_two :
    (∀ xs : List V, Independent xs → xs.length ≤ 2) ∧
      ∃ xs : List V, Independent xs ∧ xs.length = 2 := by
  refine ⟨fun _ h => independent_size h, [0,6], ?_, rfl⟩
  unfold Independent
  decide

private theorem filter_length_mono (l : List V) (p q : V → Bool)
    (h : ∀ v, p v = true → q v = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => decide
  | cons v vs ih =>
    cases hp : p v with
    | false =>
      cases hq : q v <;> simp [List.filter_cons, hp, hq] <;> omega
    | true =>
      have hq := h v hp
      simp [List.filter_cons, hp, hq] <;> omega

-- The open neighborhood of a nonempty set contains all five neighbors
-- of any chosen member. This bound also holds when the set is not independent.
theorem five_le_neighborhood {xs : List V} (ne : xs ≠ []) :
    5 ≤ (neighborhood xs).length := by
  cases xs with
  | nil => exact False.elim (ne rfl)
  | cons u tail =>
    have dom := filter_length_mono vertices (fun v => adj v u)
      (fun v => (u :: tail).any (fun w => adj v w))
      (fun v hv => by simp [hv])
    rw [neighbors_of_vertex u] at dom
    exact dom

theorem independence_irreducible {xs : List V} (h : Independent xs) (ne : xs ≠ []) :
    xs.length < (neighborhood xs).length := by
  have hi := independent_size h
  have hn := five_le_neighborhood ne
  omega

#print axioms independence_number_two
#print axioms independence_irreducible

end RookTen
