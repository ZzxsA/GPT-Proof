import Std

/-!
# Finite witnesses for Problem 14 of Knor, Sedlar, Škrekovski and Zhang

`search` enumerates actual vertex sequences in the supplied graph. It counts
no longer path after it has found one of minimum length. The total counts
one orientation for distinct endpoints and one singleton for each vertex.
No layer-product formula is assumed by the verifier.
-/

namespace Geodesics

set_option maxHeartbeats 0
set_option maxRecDepth 100000

structure Graph where
  order : Nat
  edge : Nat → Nat → Bool

def vertices (g : Graph) := List.range g.order

private def labelsFrom : Nat → List Nat → List Nat
  | _, [] => []
  | i, n :: ns => List.replicate n i ++ labelsFrom (i+1) ns

/-- The sequential join of independent layers. Each label is a vertex's
layer index; two vertices are adjacent precisely when their indices differ
by one. Out-of-range vertices have no incident edges. -/
def layered (widths : List Nat) : Graph :=
  let labels := labelsFrom 0 widths
  { order := labels.length
    edge := fun u v =>
      match labels[u]?, labels[v]? with
      | some i, some j => (i+1 == j) || (j+1 == i)
      | _, _ => false }

def simple (g : Graph) : Bool :=
  (vertices g).all fun u => !g.edge u u &&
    (vertices g).all (fun v => g.edge u v == g.edge v u)

/-- A frontier contains all simple paths of one fixed length from the
chosen source, stored endpoint-first. A path extends along one edge to any
vertex not already in the path. A new path has only one parent, its tail. -/
def extend (g : Graph) (front : List (List Nat)) : List (List Nat) :=
  front.flatMap fun p =>
    match p with
    | [] => []
    | u :: _ => ((vertices g).filter (fun w => g.edge u w && !(p.contains w))).map (fun w => w :: p)

private def atTarget (v : Nat) (front : List (List Nat)) : Nat :=
  (front.filter (fun p => p.head? == some v)).length

/-- Return (distance, number of shortest paths). Start from the unique
zero-length path. A simple path in an n-vertex graph has at most n-1 edges.
If the frontier dies out or the budget is exhausted, the pair is disconnected. -/
private def search (g : Graph) (v : Nat) : Nat → List (List Nat) → Option (Nat × Nat)
  | 0, front =>
    let count := atTarget v front
    if count = 0 then none else some (0, count)
  | fuel + 1, front =>
    let count := atTarget v front
    if count != 0 then some (0, count)
    else if front.isEmpty then none
    else (search g v fuel (extend g front)).map (fun t => (t.1+1, t.2))

def shortest (g : Graph) (u v : Nat) : Option (Nat × Nat) :=
  search g v (g.order-1) [[u]]

/-- Exactly one source-target ordering per distinct pair of labels. -/
def betweenPairs (g : Graph) : List (Option (Nat × Nat)) :=
  (vertices g).flatMap fun u =>
    ((vertices g).filter (fun v => decide (u < v))).map (fun v => shortest g u v)

structure Report where
  order : Nat
  isSimple : Bool
  isConnected : Bool
  diameter : Nat
  count : Nat
  deriving DecidableEq, Repr

def report (g : Graph) : Report :=
  let pairs := betweenPairs g
  let found := pairs.filterMap id
  { order := g.order
    isSimple := simple g
    isConnected := (g.order != 0) && (pairs.length == found.length)
    diameter := found.foldl (fun d t => max d t.1) 0
    count := g.order + (found.map Prod.snd).sum }

def baseline9 := layered [3,3,3]
def witness9 := layered [1,2,3,2,1]
def baseline12 := layered [3,3,3,3]
def witness12 := layered [1,2,3,3,2,1]

theorem baseline9_report : report baseline9 = ⟨9,true,true,2,90⟩ := by decide
theorem witness9_report : report witness9 = ⟨9,true,true,4,105⟩ := by decide
theorem baseline12_report : report baseline12 = ⟨12,true,true,3,228⟩ := by decide
theorem witness12_report : report witness12 = ⟨12,true,true,5,303⟩ := by decide

theorem improvement_nine : (report baseline9).count < (report witness9).count := by
  rw [baseline9_report, witness9_report]
  decide

theorem improvement_twelve : (report baseline12).count < (report witness12).count ∧
    9 * 3^4 < 4 * (report witness12).count := by
  rw [baseline12_report, witness12_report]
  decide

/-- There exists a simple connected graph whose geodesic count is greater
than the count in the paper's equal-width-three graph on the same order. -/
theorem problem14_finite : ∃ g : Graph, (report g).isSimple = true ∧
    (report g).isConnected = true ∧ (report g).order = (report baseline12).order ∧
    (report baseline12).count < (report g).count ∧ 9 * 3^4 < 4 * (report g).count := by
  refine ⟨witness12, ?_⟩
  rw [baseline12_report, witness12_report]
  decide

#print axioms problem14_finite

end Geodesics
