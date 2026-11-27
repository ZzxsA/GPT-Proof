import Std

/-!
The q = 3, n = 4, (k₁, k₂, ℓ) = (2, 3, 2) case of Huang–Fang–Fu's
Theorem 4 is impossible. An MDS code is specified by its minimum distance
and the surjectivity of projection onto the first k coordinates. Minimum
distance n-k+1 makes that projection injective, so this characterization
is equivalent to the usual linear [n,k,n-k+1] definition.
-/

namespace HuangFangFu

abbrev F := Fin 3

structure Word where
  x : F
  y : F
  z : F
  t : F
  deriving DecidableEq, BEq

def zeroWord : Word := ⟨0, 0, 0, 0⟩

def combine (a : F) (u : Word) (b : F) (v : Word) : Word :=
  ⟨a*u.x + b*v.x, a*u.y + b*v.y, a*u.z + b*v.z, a*u.t + b*v.t⟩

def weight (u : Word) : Nat :=
  [u.x, u.y, u.z, u.t].countP (fun x => x != 0)

def distanceOK (d : Nat) (u : Word) : Bool :=
  u == zeroWord || decide (d ≤ weight u)

structure Code where
  mem : Word → Prop
  zero_mem : mem zeroWord
  closed : ∀ {u v : Word}, mem u → mem v → ∀ a b : F, mem (combine a u b v)

def hasDistance (C : Code) (d : Nat) : Prop :=
  ∀ u, C.mem u → distanceOK d u = true

def mds423 (C : Code) : Prop :=
  (∀ a b : F, ∃ u : Word, C.mem u ∧ u.x = a ∧ u.y = b) ∧ hasDistance C 3

def mds432 (C : Code) : Prop :=
  (∀ a b c : F, ∃ u : Word, C.mem u ∧ u.x = a ∧ u.y = b ∧ u.z = c) ∧ hasDistance C 2

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
private theorem incompatible_rows : ∀ a b c d e : F,
    (∀ i j : F, distanceOK 3 (combine i ⟨1,0,a,b⟩ j ⟨0,1,c,d⟩) = true) →
    (∀ i j k : F, distanceOK 2
      (combine 1 (combine i ⟨1,0,a,b⟩ j ⟨0,1,c,d⟩) k ⟨0,0,1,e⟩) = true) →
    False := by decide

/-- No ternary [4,2,3] code can be contained in a ternary [4,3,2] code. -/
theorem no_nested_mds (C D : Code) (hc : mds423 C) (hd : mds432 D) :
    ¬ (∀ u, C.mem u → D.mem u) := by
  intro inside
  obtain ⟨⟨x₁,y₁,a,b⟩, h₁, hx₁, hy₁⟩ := hc.1 1 0
  change x₁ = 1 at hx₁
  change y₁ = 0 at hy₁
  subst x₁
  subst y₁
  obtain ⟨⟨x₂,y₂,c,d⟩, h₂, hx₂, hy₂⟩ := hc.1 0 1
  change x₂ = 0 at hx₂
  change y₂ = 1 at hy₂
  subst x₂
  subst y₂
  obtain ⟨⟨x₃,y₃,z₃,e⟩, h₃, hx₃, hy₃, hz₃⟩ := hd.1 0 0 1
  change x₃ = 0 at hx₃
  change y₃ = 0 at hy₃
  change z₃ = 1 at hz₃
  subst x₃
  subst y₃
  subst z₃
  apply incompatible_rows a b c d e
  · intro i j
    exact hc.2 _ (C.closed h₁ h₂ i j)
  · intro i j k
    exact hd.2 _ (D.closed (inside _ (C.closed h₁ h₂ i j)) h₃ 1 k)

#print axioms no_nested_mds

end HuangFangFu
