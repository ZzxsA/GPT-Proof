import Std

/-! A Euclidean self-orthogonal [18,3,16] code over F₁₆.
The low four bits are coefficients in (1, α, α², α³), where α⁴ = α+1.
Compilation target: Lean 4.19.0 with its bundled standard library. -/
namespace Liu16

set_option maxRecDepth 16384
set_option maxHeartbeats 0

abbrev F := Fin 16

def elem (n : Nat) : F := ⟨n % 16, Nat.mod_lt _ (by decide)⟩

def add (a b : F) : F := elem (a.val ^^^ b.val)

/-- Four polynomial multiply-and-reduce steps modulo X⁴+X+1. -/
def polyMul : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n+1, a, b =>
    let doubled := if a < 8 then 2*a else (2*a) ^^^ 19
    (if b % 2 = 1 then a else 0) ^^^ polyMul n doubled (b/2)

/-- Logarithms and antilogarithms in the polynomial basis above. -/
private def log : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 4
  | 4 => 2
  | 5 => 8
  | 6 => 5
  | 7 => 10
  | 8 => 3
  | 9 => 14
  | 10 => 9
  | 11 => 7
  | 12 => 6
  | 13 => 13
  | 14 => 11
  | _ => 12

private def antilog : Nat → F
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 3
  | 5 => 6
  | 6 => 12
  | 7 => 11
  | 8 => 5
  | 9 => 10
  | 10 => 7
  | 11 => 14
  | 12 => 15
  | 13 => 13
  | _ => 9

def mul (a b : F) : F :=
  if a = 0 ∨ b = 0 then 0 else antilog ((log a.val + log b.val) % 15)

theorem mul_is_polynomial_multiplication :
    ∀ a b : F, mul a b = elem (polyMul 4 a.val b.val) := by decide

structure Col where
  x : F
  y : F
  z : F

def columns : List Col :=
  [⟨15, 0, 0⟩,
   ⟨13, 13, 13⟩,
   ⟨5, 10, 2⟩,
   ⟨9, 8, 2⟩,
   ⟨2, 8, 12⟩,
   ⟨1, 5, 7⟩,
   ⟨1, 6, 2⟩,
   ⟨1, 7, 3⟩,
   ⟨12, 10, 13⟩,
   ⟨1, 9, 10⟩,
   ⟨1, 10, 12⟩,
   ⟨1, 11, 13⟩,
   ⟨1, 12, 9⟩,
   ⟨1, 13, 8⟩,
   ⟨1, 14, 15⟩,
   ⟨1, 15, 14⟩,
   ⟨0, 1, 0⟩,
   ⟨0, 0, 1⟩]

def inner (f g : Col → F) : F :=
  columns.foldl (fun s p => add s (mul (f p) (g p))) 0

/-- det[a,b,c], using subtraction = addition in characteristic two. -/
def det (a b c : Col) : F :=
  add (mul a.x (add (mul b.y c.z) (mul b.z c.y)))
    (add (mul a.y (add (mul b.x c.z) (mul b.z c.x)))
         (mul a.z (add (mul b.x c.y) (mul b.y c.x))))

/-- For fixed a, test all unordered pairs from the remaining list. -/
def checkPairs (a : Col) : List Col → Bool
  | [] => true
  | b :: bs => bs.all (fun c => det a b c != 0) && checkPairs a bs

/-- Test every choice of three distinct column positions exactly once. -/
def checkTriples : List Col → Bool
  | [] => true
  | a :: rest => checkPairs a rest && checkTriples rest

theorem length_eq : columns.length = 18 := by decide

/-- The six upper-triangular entries of the symmetric matrix G Gᵀ. -/
theorem euclidean_gram_zero :
    inner Col.x Col.x = 0 ∧ inner Col.x Col.y = 0 ∧
    inner Col.x Col.z = 0 ∧ inner Col.y Col.y = 0 ∧
    inner Col.y Col.z = 0 ∧ inner Col.z Col.z = 0 := by decide

theorem all_three_column_minors_nonzero : checkTriples columns = true := by decide

/-- Select a generator column by its position, from zero to seventeen. -/
def column (i : Fin 18) : Col := columns.get ⟨i.val, by
  change i.val < 18
  exact i.isLt⟩

/-- Pointwise version of the same minor check, quantified over all positions. -/
theorem every_ordered_minor :
    ∀ i j k : Fin 18, i < j → j < k →
      det (column i) (column j) (column k) ≠ 0 := by decide

/- The minors imply rank three, and a nonzero row vector kills at most two
columns: any three such columns would be contained in its two-dimensional
kernel. The resulting code therefore has distance at least 16. Two columns
always have a nonzero common annihilator, so the distance is exactly 16.
Bilinearity extends the six row inner-product checks to the entire code. -/

#print axioms mul_is_polynomial_multiplication
#print axioms euclidean_gram_zero
#print axioms all_three_column_minors_nonzero
#print axioms every_ordered_minor

end Liu16
