import RookTenIndependent

namespace RookTen

/-- Edge count along a walk in the graph specified by adj. -/
inductive Walk : V → V → Nat → Prop where
  | nil (u : V) : Walk u u 0
  | cons {u v w : V} {n : Nat} : adj u v = true → Walk v w n → Walk u w (n+1)

private theorem walk_zero {u v : V} (h : Walk u v 0) : u = v := by
  cases h
  rfl

private theorem walk_one {u v : V} (h : Walk u v 1) : adj u v = true := by
  cases h with
  | cons ha ht => cases ht; exact ha

private def corner (u v : V) : V :=
  ⟨5 * (u.val / 5) + v.val % 5, by have := u.isLt; omega⟩

private theorem common : ∀ u v : V, u ≠ v → adj u v = false →
    adj u (corner u v) = true ∧ adj (corner u v) v = true := by decide

def distance (u v : V) : Nat := if u = v then 0 else if adj u v then 1 else 2

theorem distance_is_shortest (u v : V) :
    Walk u v (distance u v) ∧ ∀ j, j < distance u v → ¬ Walk u v j := by
  by_cases eq : u = v
  · subst v
    rw [show distance u u = 0 by simp [distance]]
    exact ⟨Walk.nil u, by omega⟩
  cases ha : adj u v with
  | false =>
    have dd : distance u v = 2 := by simp [distance, eq, ha]
    rw [dd]
    obtain ⟨h1, h2⟩ := common u v eq ha
    refine ⟨Walk.cons h1 (Walk.cons h2 (Walk.nil v)), ?_⟩
    intro j hj hw
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact eq (walk_zero hw)
    · have hh := walk_one hw
      simp [ha] at hh
  | true =>
    have dd : distance u v = 1 := by simp [distance, eq, ha]
    rw [dd]
    refine ⟨Walk.cons ha (Walk.nil v), ?_⟩
    intro j hj hw
    have : j = 0 := by omega
    subst j
    exact eq (walk_zero hw)

def degree (u : V) := (vertices.filter (fun v => adj u v)).length
def maximumDegree := (vertices.map degree).foldr Nat.max 0
def eccentricity (u : V) := (vertices.map (distance u)).foldr Nat.max 0
def diameter := (vertices.map eccentricity).foldr Nat.max 0
def periphery := vertices.filter (fun u => eccentricity u == diameter)

private def insertDescending (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if y ≤ x then x :: y :: ys else y :: insertDescending x ys

private def descending : List Nat → List Nat
  | [] => []
  | x :: xs => insertDescending x (descending xs)

/-- The Havel–Hakimi residue. Every nonterminal iteration removes one entry. -/
def hh : Nat → List Nat → Nat
  | 0, ds => ds.length
  | fuel+1, ds =>
    match descending ds with
    | [] => 0
    | x :: tail =>
      if x = 0 then tail.length + 1
      else hh fuel ((tail.take x).map (fun d => d-1) ++ tail.drop x)

def residue := hh vertices.length (vertices.map degree)

theorem computed_invariants :
    (∀ u : V, eccentricity u = 2) ∧ periphery.length = 10 ∧ maximumDegree = 5 ∧ residue = 2 := by
  decide

/-- Specialize the published lower bound to this graph using its independent sets. -/
def proposedBound : Prop := ∃ xs : List V, Independent xs ∧
  periphery.length ≤ xs.length + maximumDegree + residue

theorem table_bound_fails :
    (∀ xs : List V, Independent xs → xs ≠ [] → xs.length < (neighborhood xs).length) ∧
    ¬ proposedBound := by
  refine ⟨fun _ h ne => independence_irreducible h ne, ?_⟩
  rintro ⟨xs, hi, hc⟩
  have small := independent_size hi
  obtain ⟨_, hp, hd, hr⟩ := computed_invariants
  omega

#print axioms distance_is_shortest
#print axioms table_bound_fails

end RookTen
