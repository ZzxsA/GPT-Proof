import Std

/-! Finite basis for Conjecture 1(i) of OEIS A362861. All computed bitsets
are natural numbers. Bit n denotes an actual sublist whose sum is n. -/
namespace SunFive

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def halfTerm (a j : Nat) : Nat := (5^a + 5^j) / 2

def seedCoins : List Nat :=
  (List.range 5).flatMap (fun a => (List.range (a+1)).map (halfTerm a))

def holes : List Nat := [2, 7, 10, 11, 12, 27, 35, 50, 51, 52, 55, 60, 135, 255]

theorem seed_terms : ∀ v ∈ seedCoins, ∃ a j : Nat, j ≤ a ∧ a < 5 ∧ v = halfTerm a j := by
  intro v hv
  obtain ⟨a, ha, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hv
  have := List.mem_range.mp hj
  exact ⟨a, j, by omega, List.mem_range.mp ha, he.symm⟩

theorem seed_small_atom {a j : Nat} (ha : a < 5) (hj : j ≤ a) :
    halfTerm a j ∈ seedCoins :=
  List.mem_flatMap.mpr ⟨a, List.mem_range.mpr ha,
    List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩⟩

theorem seed_nodup : seedCoins.Nodup := by decide

private def represent (coins : List Nat) (n : Nat) : Prop :=
  ∃ ys : List Nat, ys.Sublist coins ∧ ys.sum = n

private theorem represent_cons (x n : Nat) (xs : List Nat) :
    represent (x :: xs) n ↔ represent xs n ∨ (x ≤ n ∧ represent xs (n-x)) := by
  constructor
  · rintro ⟨ys, hsub, hsum⟩
    rcases List.sublist_cons_iff.mp hsub with skipped | ⟨zs, rfl, used⟩
    · exact Or.inl ⟨ys, skipped, hsum⟩
    · simp only [List.sum_cons] at hsum
      exact Or.inr ⟨by omega, zs, used, by omega⟩
  · rintro (⟨ys, hsub, hsum⟩ | ⟨hle, ys, hsub, hsum⟩)
    · exact ⟨ys, hsub.cons x, hsum⟩
    · exact ⟨x :: ys, hsub.cons₂ x, by simp only [List.sum_cons]; omega⟩

private def reachableBits : List Nat → Nat
  | [] => 1
  | x :: xs => let tail := reachableBits xs; tail ||| (tail <<< x)

private theorem reachable_iff (xs : List Nat) (n : Nat) :
    (reachableBits xs).testBit n = true ↔ represent xs n := by
  induction xs generalizing n with
  | nil =>
    rw [show reachableBits [] = 1 from rfl, Nat.testBit_one_eq_true_iff_self_eq_zero]
    constructor
    · rintro rfl
      exact ⟨[], .slnil, rfl⟩
    · rintro ⟨ys, hsub, hsum⟩
      have hy : ys = [] := List.eq_nil_of_sublist_nil hsub
      subst ys
      exact hsum.symm
  | cons x xs ih =>
    simp only [reachableBits, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true_iff,
      Bool.and_eq_true_iff, decide_eq_true_eq, ih, represent_cons]

private def marked : List Nat → Nat
  | [] => 0
  | x :: xs => 2^x ||| marked xs

private theorem marked_iff (xs : List Nat) (n : Nat) :
    (marked xs).testBit n = true ↔ n ∈ xs := by
  induction xs with
  | nil => simp [marked]
  | cons x xs ih =>
    simp [marked, Nat.testBit_or, Nat.testBit_two_pow, ih, eq_comm]

/-- Check one 2088-bit equality. The low bits absent from the reachable
set are exactly the entries of the source's exception list. -/
private theorem certificate :
    (reachableBits seedCoins &&& (2^2088-1)) = ((2^2088-1) ^^^ marked holes) := by
  decide

theorem seed_exact (n : Nat) (hn : n ≤ 2087) :
    (∃ ys : List Nat, ys.Sublist seedCoins ∧ ys.sum = n) ↔ n ∉ holes := by
  change represent seedCoins n ↔ ¬ n ∈ holes
  rw [← reachable_iff, ← marked_iff]
  have key := congrArg (fun v : Nat => v.testBit n) certificate
  have hlt : n < 2088 := by omega
  cases haveCoin : (reachableBits seedCoins).testBit n <;>
    cases isHole : (marked holes).testBit n <;>
    simp [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
      hlt, haveCoin, isHole] at key ⊢

end SunFive
