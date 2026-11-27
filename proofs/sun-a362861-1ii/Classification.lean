import ThreeSeven
import Obstructions

namespace OddPair

private theorem positiveCases {q : Nat} (hq : q = 3 ∨ q = 5 ∨ q = 7) : Universal 3 q := by
  intro n hn he
  obtain ⟨xs, hd, hw, hs⟩ := SunThreeSeven.restrictedEvenAll hq n (by omega)
  refine ⟨xs, hs, hd, ?_⟩
  intro x hx
  obtain ⟨a, b, _, heq⟩ := hw x hx
  exact ⟨a, b, heq⟩

/-- Classification for every positive even target and all odd bases at least three. -/
theorem universal_iff {k m : Nat} (hk : 3 ≤ k) (hm : 3 ≤ m)
    (ok : k % 2 = 1) (om : m % 2 = 1) :
    Universal k m ↔
      (k = 3 ∧ (m = 3 ∨ m = 5 ∨ m = 7)) ∨
      (m = 3 ∧ (k = 3 ∨ k = 5 ∨ k = 7)) := by
  constructor
  · exact necessary hk hm ok om
  · rintro (⟨rfl, hm'⟩ | ⟨rfl, hk'⟩)
    · exact positiveCases hm'
    · exact swap (positiveCases hk')

/-- Every positive even integer has a representation with second exponent at most B. -/
def WithBound (q B : Nat) : Prop :=
  ∀ n : Nat, 0 < n → 2 ∣ n → ∃ xs : List Nat, xs.sum = n ∧ xs.Nodup ∧
    ∀ x ∈ xs, ∃ a b : Nat, b ≤ B ∧ x = 3^a + q^b

/-- The uniform second-exponent bound 1 is optimal for all three positive cases. -/
theorem exponent_bound_iff {q B : Nat} (hq : q = 3 ∨ q = 5 ∨ q = 7) :
    WithBound q B ↔ 1 ≤ B := by
  constructor
  · intro h
    by_cases hB : 1 ≤ B
    · exact hB
    exfalso
    have zero : B = 0 := by omega
    obtain ⟨xs, hs, hd, hm⟩ := h 8 (by decide) (by decide)
    apply eight_obstruction (m := 9) (by decide) xs hs hd
    intro x hx
    obtain ⟨a, b, hb, eq⟩ := hm x hx
    have eq0 : b = 0 := by omega
    exact ⟨a, 0, by simpa only [eq0, Nat.pow_zero] using eq⟩
  · intro hB n _ he
    obtain ⟨xs, hd, hw, hs⟩ := SunThreeSeven.restrictedEvenAll hq n (by omega)
    refine ⟨xs, hs, hd, ?_⟩
    intro x hx
    obtain ⟨a, b, hb, heq⟩ := hw x hx
    exact ⟨a, b, Nat.le_trans hb hB, heq⟩

#print axioms universal_iff
#print axioms exponent_bound_iff

end OddPair
