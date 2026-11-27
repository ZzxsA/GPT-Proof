import Std

/-!
# The ternary assertion in Zhi-Wei Sun's Conjecture 1(i), OEIS A362861

For each base-three digit of `u`, construct terms summing to `2*u`.
Digit 1 at position i contributes `2*3^i = 3^i + 3^i`.
Digit 2 at position i contributes `4*3^i = 3^i + 3^(i+1)`.
The least significant term is either 2 or 4; every term from a higher
position is divisible by 3. The output is a list of actual natural numbers.
-/

namespace SunTernary

def Summand (x : Nat) : Prop := ∃ a b : Nat, x = 3^a + 3^b

def Represents (n : Nat) (xs : List Nat) : Prop :=
  xs.sum = n ∧ xs.Nodup ∧ ∀ x ∈ xs, Summand x

private def triples (xs : List Nat) := xs.map (fun x => 3*x)

private theorem sum_triples (xs : List Nat) : (triples xs).sum = 3 * xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change 3*x + (triples xs).sum = 3 * (x + xs.sum)
    rw [ih, Nat.mul_add]

private theorem nodup_triples {xs : List Nat} (h : xs.Nodup) : (triples xs).Nodup := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp h
    apply List.nodup_cons.mpr
    refine ⟨?_, ih hxs⟩
    intro hm
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
    have eq : y = x := by omega
    exact hx (eq ▸ hy)

private theorem triple_summand {x : Nat} (h : Summand x) : Summand (3*x) := by
  obtain ⟨a,b,ha⟩ := h
  refine ⟨a+1,b+1,?_⟩
  rw [ha, Nat.mul_add, Nat.pow_succ, Nat.pow_succ]
  omega

private theorem scaled {n : Nat} {xs : List Nat} (h : Represents n xs) :
    Represents (3*n) (triples xs) := by
  refine ⟨(sum_triples xs).trans (congrArg (fun y => 3*y) h.1), nodup_triples h.2.1, ?_⟩
  intro x hx
  obtain ⟨y, hy, he⟩ := List.mem_map.mp hx
  rw [← he]
  exact triple_summand (h.2.2 y hy)

private def appendDigit (d : Nat) (higher : List Nat) : List Nat :=
  if d = 0 then higher else 2*d :: higher

private theorem digit_step (u : Nat) {xs : List Nat} (h : Represents (2*(u/3)) xs) :
    Represents (2*u) (appendDigit (u%3) (triples xs)) := by
  obtain ⟨hs, hn, ha⟩ := scaled h
  by_cases hz : u%3 = 0
  · rw [appendDigit, if_pos hz]
    exact ⟨by omega, hn, ha⟩
  · rw [appendDigit, if_neg hz]
    have hd : 2*(u%3) = 2 ∨ 2*(u%3) = 4 := by omega
    have base : Summand (2*(u%3)) := by
      rcases hd with h2 | h4
      · exact ⟨0,0,h2⟩
      · exact ⟨0,1,h4⟩
    have fresh : 2*(u%3) ∉ triples xs := by
      intro hm
      obtain ⟨y, _, he⟩ := List.mem_map.mp hm
      omega
    refine ⟨?_, List.nodup_cons.mpr ⟨fresh,hn⟩, ?_⟩
    · rw [List.sum_cons]
      omega
    · intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · rw [hx]; exact base
      · exact ha x hx

/-- The constructive list is computed from the ternary digits of half the target. -/
def terms (u : Nat) : List Nat :=
  if h : u = 0 then [] else appendDigit (u%3) (triples (terms (u/3)))
termination_by u
decreasing_by omega

theorem terms_correct (u : Nat) : Represents (2*u) (terms u) := by
  refine Nat.strongRecOn (motive := fun n => Represents (2*n) (terms n)) u ?_
  intro n ih
  rw [terms]
  split
  · rename_i h
    subst n
    simp [Represents]
  · rename_i h
    exact digit_step n (ih (n/3) (by omega))

/-- The ternary assertion of Conjecture 1(i), including distinctness of the
numerical summands (not only of the exponent pairs). -/
theorem conjecture_one_i_ternary (n : Nat) (hn : 0 < n) (he : 2 ∣ n) :
    ∃ xs : List Nat, xs ≠ [] ∧ xs.sum = n ∧ xs.Nodup ∧
      ∀ x ∈ xs, ∃ a b : Nat, x = 3^a + 3^b := by
  obtain ⟨u, hu⟩ := he
  have spec := terms_correct u
  have hs : (terms u).sum = n := spec.1.trans hu.symm
  refine ⟨terms u, ?_, hs, spec.2.1, spec.2.2⟩
  intro hnil
  rw [hnil] at hs
  change 0 = n at hs
  omega

#print axioms conjecture_one_i_ternary
end SunTernary
