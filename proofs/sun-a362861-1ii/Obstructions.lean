import Std

namespace OddPair

/-- Every positive even integer is a sum of distinct numerical summands. -/
def Universal (k m : Nat) : Prop :=
  ∀ n : Nat, 0 < n → 2 ∣ n →
    ∃ xs : List Nat, xs.sum = n ∧ xs.Nodup ∧
      ∀ x ∈ xs, ∃ a b : Nat, x = k^a + m^b

theorem swap {k m : Nat} (h : Universal k m) : Universal m k := by
  intro n hn he
  obtain ⟨xs, hs, hd, hw⟩ := h n hn he
  refine ⟨xs, hs, hd, ?_⟩
  intro x hx
  obtain ⟨a, b, hval⟩ := hw x hx
  exact ⟨b, a, hval.trans (Nat.add_comm _ _)⟩

private theorem member_le_sum {x : Nat} {xs : List Nat} (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hx with h | h
    · omega
    · have := ih h
      omega

private theorem sum_one {xs : List Nat} {p : Nat} (hd : xs.Nodup)
    (only : ∀ x ∈ xs, x = p) : xs.sum ≤ p := by
  cases xs with
  | nil => simp
  | cons x xs =>
    have hx := only x (by simp)
    cases xs with
    | nil => simp [hx]
    | cons y ys =>
      have hy := only y (by simp)
      have hxy : x = y := hx.trans hy.symm
      exact False.elim ((List.nodup_cons.mp hd).1 (by simp [hxy]))

private theorem sum_two {xs : List Nat} {p q : Nat} (hd : xs.Nodup)
    (only : ∀ x ∈ xs, x = p ∨ x = q) : xs.sum ≤ p + q := by
  cases xs with
  | nil => simp
  | cons x xs =>
    obtain ⟨hx, ht⟩ := List.nodup_cons.mp hd
    have tail (y : Nat) (hy : y ∈ xs) : y = p ∨ y = q :=
      only y (List.mem_cons_of_mem x hy)
    rcases only x (by simp) with hp | hq
    · have bound : xs.sum ≤ q := sum_one ht (by
        intro y hy
        rcases tail y hy with eq | eq
        · exact False.elim (hx (by simpa [hp, eq] using hy))
        · exact eq)
      simp only [List.sum_cons]
      omega
    · have bound : xs.sum ≤ p := sum_one ht (by
        intro y hy
        rcases tail y hy with eq | eq
        · exact eq
        · exact False.elim (hx (by simpa [hq, eq] using hy)))
      simp only [List.sum_cons]
      omega

private theorem pow_ge_one {k : Nat} (hk : 1 ≤ k) (a : Nat) : 1 ≤ k^a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.pow_succ]
    simpa using Nat.mul_le_mul ih hk

private theorem base_le_succ {k : Nat} (hk : 1 ≤ k) (a : Nat) : k ≤ k^(a+1) := by
  rw [Nat.pow_succ]
  simpa using Nat.mul_le_mul_right k (pow_ge_one hk a)

private theorem power_cases {k : Nat} (hk : 1 ≤ k) (a : Nat) : k^a = 1 ∨ k ≤ k^a := by
  cases a with
  | zero => exact Or.inl rfl
  | succ a => exact Or.inr (base_le_succ hk a)

private theorem three_power_cases (a : Nat) : 3^a = 1 ∨ 3^a = 3 ∨ 9 ≤ 3^a := by
  cases a with
  | zero => decide
  | succ a =>
    cases a with
    | zero => decide
    | succ a =>
      right; right
      rw [Nat.pow_succ]
      exact Nat.mul_le_mul_right 3 (base_le_succ (k := 3) (by decide) a)

/-- If both bases exceed three, 2 is the only summand at most 4. -/
private theorem one_is_three {k m : Nat} (hk : 3 ≤ k) (hm : 3 ≤ m)
    (h : Universal k m) : k = 3 ∨ m = 3 := by
  by_cases ek : k = 3
  · exact Or.inl ek
  by_cases em : m = 3
  · exact Or.inr em
  obtain ⟨xs, hs, hd, hw⟩ := h 4 (by decide) (by decide)
  have only (x : Nat) (hx : x ∈ xs) : x = 2 := by
    have hsmall := member_le_sum hx
    obtain ⟨a, b, hval⟩ := hw x hx
    have hka := pow_ge_one (k := k) (by omega) a
    have hmb := pow_ge_one (k := m) (by omega) b
    rcases power_cases (k := k) (by omega) a with ha | ha <;>
      rcases power_cases (k := m) (by omega) b with hb | hb <;> omega
  have bound := sum_one hd only
  omega

/-- For bases 3 and m ≥ 9, only 2 and 4 can occur at target 8. -/
theorem eight_obstruction {m : Nat} (hm : 9 ≤ m) (xs : List Nat) (hs : xs.sum = 8)
    (hd : xs.Nodup) (hw : ∀ x ∈ xs, ∃ a b : Nat, x = 3^a + m^b) : False := by
  have only (x : Nat) (hx : x ∈ xs) : x = 2 ∨ x = 4 := by
    have hsmall := member_le_sum hx
    obtain ⟨a, b, hval⟩ := hw x hx
    have ha := pow_ge_one (k := 3) (by decide) a
    have hb := pow_ge_one (k := m) (by omega) b
    rcases three_power_cases a with e | e | e <;>
      rcases power_cases (k := m) (by omega) b with f | f <;> omega
  have bound := sum_two hd only
  omega

private theorem no_large_right {m : Nat} (hm : 9 ≤ m) (h : Universal 3 m) : False := by
  obtain ⟨xs, hs, hd, hw⟩ := h 8 (by decide) (by decide)
  exact eight_obstruction hm xs hs hd hw

theorem necessary {k m : Nat} (hk : 3 ≤ k) (hm : 3 ≤ m)
    (ok : k % 2 = 1) (om : m % 2 = 1) (h : Universal k m) :
    (k = 3 ∧ (m = 3 ∨ m = 5 ∨ m = 7)) ∨ (m = 3 ∧ (k = 3 ∨ k = 5 ∨ k = 7)) := by
  have classify (x : Nat) (hx : 3 ≤ x) (ox : x % 2 = 1) (hu : Universal 3 x) :
      x = 3 ∨ x = 5 ∨ x = 7 := by
    by_cases big : 9 ≤ x
    · exact False.elim (no_large_right big hu)
    · omega
  rcases one_is_three hk hm h with he | he
  · subst k
    exact Or.inl ⟨rfl, classify m hm om h⟩
  · subst m
    exact Or.inr ⟨rfl, classify k hk ok (swap h)⟩

end OddPair
