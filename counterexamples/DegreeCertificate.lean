import Std

/-! Exhaustive finite certificates for signed inequalities on simple graphs.
Vertices are 0,...,order-1. Each edge is listed once, smaller endpoint first.
All graph classes and invariant values are recomputed from that edge list. -/
namespace DegreeCertificate

structure Graph where
  order : Nat
  edges : List (Nat × Nat)
  deriving Repr

inductive ClassName
  | nontrivial | clawFree | subcubic | eulerian | triangleFree | regular | connected | cubic
  deriving DecidableEq, Repr

inductive Invariant
  | cliqueNumber | constant | vertexCoverNumber | maximumDegree | minimumDegree | size | order
  deriving DecidableEq, Repr

def Graph.vertices (g : Graph) : List Nat := List.range g.order

def Graph.valid (g : Graph) : Bool :=
  g.edges.all (fun e => decide (e.1 < e.2 ∧ e.2 < g.order)) &&
    (g.edges.eraseDups.length == g.edges.length)

def Graph.adj (g : Graph) (u v : Nat) : Bool :=
  g.edges.contains (min u v, max u v)

def Graph.neighbors (g : Graph) (u : Nat) : List Nat :=
  g.vertices.filter (g.adj u)

def Graph.degree (g : Graph) (u : Nat) : Nat := (g.neighbors u).length

private def grow (g : Graph) : Nat → List Nat → List Nat
  | 0, seen => seen
  | fuel + 1, seen =>
    if seen.length == g.order then seen
    else
      let more := g.vertices.filter (fun v => seen.contains v || seen.any (fun w => g.adj w v))
      if seen.length == more.length then seen else grow g fuel more

/-- A reached set starts at vertex 0 and grows across every edge. After at
most order iterations, it includes that vertex's whole connected component. -/
def Graph.connected (g : Graph) : Bool :=
  (g.order != 0) && ((grow g g.order [0]).length == g.order)

/-- An induced claw has a center and three distinct, pairwise nonadjacent
neighbors. Ordering the three labels avoids checking permutations. -/
def Graph.clawFree (g : Graph) : Bool :=
  g.vertices.all fun u =>
    let ns := g.neighbors u
    !(ns.any fun a => ns.any fun b =>
      decide (a < b) && !(g.adj a b) && ns.any (fun c =>
        decide (b < c) && !(g.adj a c) && !(g.adj b c)))

def Graph.triangleFree (g : Graph) : Bool :=
  g.edges.all fun e => !(g.vertices.any fun w => g.adj e.1 w && g.adj e.2 w)

def Graph.hasClass (g : Graph) : ClassName → Bool
  | .nontrivial => decide (2 ≤ g.order)
  | .clawFree => g.clawFree
  | .subcubic => g.vertices.all (fun u => decide (g.degree u ≤ 3))
  | .eulerian => g.connected && g.vertices.all (fun u => g.degree u % 2 == 0)
  | .triangleFree => g.triangleFree
  | .regular => g.vertices.all (fun u => g.degree u == g.degree 0)
  | .connected => g.connected
  | .cubic => g.vertices.all (fun u => g.degree u == 3)

/-- At each element, choose whether to include it. Starting from the
distinct vertex list, this enumerates every vertex subset exactly once. -/
private def subsets : List Nat → List (List Nat)
  | [] => [[]]
  | u :: rest =>
    let tailSets := subsets rest
    tailSets ++ tailSets.map (fun s => u :: s)

private def cliqueTest (g : Graph) : List Nat → Bool
  | [] => true
  | x :: xs => xs.all (g.adj x) && cliqueTest g xs

private def coversEdges (g : Graph) (s : List Nat) : Bool :=
  g.edges.all (fun e => s.contains e.1 || s.contains e.2)

def Graph.cliqueNumber (g : Graph) : Nat :=
  (subsets g.vertices).foldl
    (fun best s => if decide (best < s.length) && cliqueTest g s then s.length else best) 0

def Graph.vertexCoverNumber (g : Graph) : Nat :=
  (subsets g.vertices).foldl
    (fun best s => if decide (s.length < best) && coversEdges g s then s.length else best) g.order

def Graph.value (g : Graph) : Invariant → Nat
  | .cliqueNumber => g.cliqueNumber
  | .constant => 1
  | .vertexCoverNumber => g.vertexCoverNumber
  | .maximumDegree => (g.vertices.map g.degree).foldl max 0
  | .minimumDegree => (g.vertices.map g.degree).foldl min g.order
  | .size => g.edges.length
  | .order => g.order

/-- Catalogue rows use the signed difference between the alleged upper bound
and the bounded expression. Integer arithmetic preserves negative values. -/
def difference (g : Graph) (linear : List (Invariant × Int)) : Int :=
  (linear.map (fun term => term.2 * Int.ofNat (g.value term.1))).sum

def Witness (g : Graph) (classes : List ClassName) (linear : List (Invariant × Int)) : Prop :=
  g.valid = true ∧ classes.all g.hasClass = true ∧ difference g linear < 0

instance (g : Graph) (classes : List ClassName) (linear : List (Invariant × Int)) :
    Decidable (Witness g classes linear) := by
  unfold Witness
  infer_instance

theorem disproof {g : Graph} {classes : List ClassName} {linear : List (Invariant × Int)}
    (h : Witness g classes linear) :
    ¬ (∀ graph : Graph, graph.valid = true → classes.all graph.hasClass = true →
      0 ≤ difference graph linear) := by
  intro claimed
  have bad := claimed g h.1 h.2.1
  have strict := h.2.2
  omega

end DegreeCertificate
