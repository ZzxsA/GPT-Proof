import Std

/-! The odd-field conjecture at q = 7. After two projective points are sent
to the coordinate points at infinity, the six affine points form a graph
(1,x,f(x)) for x in F₇*. The accompanying proof justifies the normalization.
All arithmetic below uses natural representatives reduced modulo 7. -/
namespace LiuSeven

set_option maxRecDepth 16384
set_option maxHeartbeats 0

abbrev Point := Nat × Nat

def heights (a b c d e : Fin 5) : List Nat :=
  [1, a.val+2, b.val+2, c.val+2, d.val+2, e.val+2]

def points (ys : List Nat) : List Point := [1,2,3,4,5,6].zip ys

/-- Nonvanishing of the determinant of three columns (1,x,y). -/
def independent (a b c : Point) : Bool :=
  (a.1*b.2 + b.1*c.2 + c.1*a.2) % 7 != (b.1*a.2 + c.1*b.2 + a.1*c.2) % 7

def checkPairs (a : Point) : List Point → Bool
  | [] => true
  | b :: tail => tail.all (independent a b) && checkPairs a tail

def checkTriples : List Point → Bool
  | [] => true
  | a :: tail => checkPairs a tail && checkTriples tail

def arc (ys : List Nat) : Bool := decide ys.Nodup && checkTriples (points ys)

def inverseHeights : List Nat := [1,4,5,2,3,6]

theorem normalized_arc_unique : ∀ a b c d e : Fin 5,
    arc (heights a b c d e) = true → heights a b c d e = inverseHeights := by decide

/-- Every nonzero square in F₇ is 1, 2 or 4. -/
def sq (i : Fin 3) : Nat := 2 ^ i.val

private def squareIndex (x : Fin 7) : Fin 3 :=
  match x.val with
  | 1 | 6 => 0
  | 2 | 5 => 2
  | _ => 1

theorem square_options : ∀ x : Fin 7, x ≠ 0 → ∃ i : Fin 3, x.val^2 % 7 = sq i := by
  intro x hx
  exact ⟨squareIndex x, (by decide : ∀ z : Fin 7, z ≠ 0 → z.val^2 % 7 = sq (squareIndex z)) x hx⟩

def sixWeights (a b c d e f : Fin 3) : List Nat := [sq a, sq b, sq c, sq d, sq e, sq f]

def moment (ws ys : List Nat) (g : Point → Nat) : Nat :=
  ((ws.zip (points ys)).map fun pair => pair.1 * g pair.2).sum % 7

/-- The first row is orthogonal to all three rows only if the affine
contribution to one of the other two diagonal entries is zero. -/
theorem diagonal_obstruction : ∀ a b c d e f : Fin 3,
    let w := sixWeights a b c d e f
    let m := moment w inverseHeights
    m (fun _ => 1) = 0 → m Prod.fst = 0 → m Prod.snd = 0 →
    m (fun p => p.1^2) = 0 ∨ m (fun p => p.2^2) = 0 := by decide

theorem nonzero_square_mod (i : Fin 3) : sq i % 7 ≠ 0 := (by decide : ∀ j : Fin 3, sq j % 7 ≠ 0) i

/-- The infinity columns contribute nonzero squares to the last two
diagonal entries, so the Gram matrix cannot vanish. -/
theorem no_normalized_code (a b c d e : Fin 5) (u v w x y z h j : Fin 3)
    (ha : arc (heights a b c d e) = true) :
    let m := moment (sixWeights u v w x y z) (heights a b c d e)
    ¬ (m (fun _ => 1) = 0 ∧ m Prod.fst = 0 ∧ m Prod.snd = 0 ∧
       (m (fun p => p.1^2) + sq h) % 7 = 0 ∧ (m (fun p => p.2^2) + sq j) % 7 = 0) := by
  rw [normalized_arc_unique a b c d e ha]
  dsimp only
  intro ⟨h₀, h₁, h₂, h₃, h₄⟩
  rcases diagonal_obstruction u v w x y z h₀ h₁ h₂ with left | right
  · rw [left, Nat.zero_add] at h₃
    exact nonzero_square_mod h h₃
  · rw [right, Nat.zero_add] at h₄
    exact nonzero_square_mod j h₄

#print axioms normalized_arc_unique
#print axioms square_options
#print axioms no_normalized_code
end LiuSeven
