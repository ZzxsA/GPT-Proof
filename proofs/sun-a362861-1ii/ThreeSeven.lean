import Std

/-!
The first assertion of Zhi-Wei Sun's Conjecture 1(ii) in OEIS A362861.
Every positive even integer is a sum of distinct terms of the form
3^a + 7^b. The construction works for each second base q in {3, 5, 7}
and only needs the exponents b = 0 and b = 1.

All lists below contain the actual summand values. The auxiliary interval
is indexed by half the target, so a coin of value 2*d extends it by d.
-/
namespace SunThreeSeven

def RestrictedTerm (q x : Nat) : Prop :=
  ∃ a b : Nat, b ≤ 1 ∧ x = 3^a + q^b

def RestrictedSum (q n : Nat) : Prop :=
  ∃ xs : List Nat, xs.Nodup ∧ (∀ x ∈ xs, RestrictedTerm q x) ∧ xs.sum = n

def OriginalSum (q n : Nat) : Prop :=
  ∃ xs : List Nat, xs.Nodup ∧ (∀ x ∈ xs, ∃ a b : Nat, x = 3^a + q^b) ∧ xs.sum = n

/-- Every doubled target in the interval from zero to width can use coins below cap. -/
private def Covered (q cap width : Nat) : Prop :=
  ∀ n : Nat, n ≤ width → ∃ xs : List Nat, xs.Nodup ∧
    (∀ x ∈ xs, RestrictedTerm q x ∧ x < cap) ∧ xs.sum = 2*n

private theorem relax {q cap width cap' width' : Nat}
    (old : Covered q cap width) (hcap : cap ≤ cap') (widthBound : width' ≤ width) :
    Covered q cap' width' := by
  intro n hn
  obtain ⟨xs, nd, mem, total⟩ := old n (Nat.le_trans hn widthBound)
  refine ⟨xs, nd, ?_, total⟩
  intro x hx
  exact ⟨(mem x hx).1, Nat.lt_of_lt_of_le (mem x hx).2 hcap⟩

/-- If d is at most one past the interval, its translate adjoins without a gap. -/
private theorem addCoin {q cap width d : Nat} (old : Covered q cap width)
    (fresh : cap ≤ 2*d) (fit : d ≤ width+1) (coin : RestrictedTerm q (2*d)) :
    Covered q (2*d+1) (width+d) := by
  intro n hn
  by_cases lower : n ≤ width
  · exact relax old (by omega : cap ≤ 2*d+1) (Nat.le_refl width) n lower
  · obtain ⟨xs, nd, mem, total⟩ := old (n-d) (by omega)
    have absent : 2*d ∉ xs := fun hx => by
      have := (mem (2*d) hx).2
      omega
    refine ⟨2*d :: xs, List.nodup_cons.2 ⟨absent, nd⟩, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with eq | tail
      · subst x
        exact ⟨coin, by omega⟩
      · exact ⟨(mem x tail).1, by have := (mem x tail).2; omega⟩
    · simp only [List.sum_cons]
      omega

private theorem emptyCovered (q : Nat) : Covered q 0 0 := by
  intro n hn
  have eq : n = 0 := by omega
  subst n
  exact ⟨[], by simp, by simp, rfl⟩

/-- Five different small values suffice to start the common induction. -/
private theorem seed57 {q : Nat} (hq : q = 5 ∨ q = 7) : Covered q 28 14 := by
  have p2 : RestrictedTerm q 2 := ⟨0,0,by decide,by simp only [Nat.pow_zero]⟩
  have p4 : RestrictedTerm q 4 := ⟨1,0,by decide,by simp only [Nat.pow_one,Nat.pow_zero]⟩
  have p8 : RestrictedTerm q 8 := by
    rcases hq with h | h
    · subst q
      exact ⟨1,1,by decide,by decide⟩
    · subst q
      exact ⟨0,1,by decide,by decide⟩
  have p10 : RestrictedTerm q 10 := ⟨2,0,by decide,by rw [Nat.pow_zero]⟩
  have h1 : Covered q 3 1 := addCoin (d := 1) (emptyCovered q) (by decide) (by decide) p2
  have h2 : Covered q 5 3 := addCoin (d := 2) h1 (by decide) (by decide) p4
  have h3 : Covered q 9 7 := addCoin (d := 4) h2 (by decide) (by decide) p8
  have h4 : Covered q 11 12 := addCoin (d := 5) h3 (by decide) (by decide) p10
  rcases hq with h | h
  · subst q
    have h5 : Covered 5 15 19 := addCoin (d := 7) h4 (by decide) (by decide)
      ⟨2,1,by decide,by decide⟩
    exact relax h5 (by decide) (by decide)
  · subst q
    have h7 : Covered 7 17 20 := addCoin (d := 8) h4 (by decide) (by decide)
      ⟨2,1,by decide,by decide⟩
    exact relax h7 (by decide) (by decide)

private theorem seed {q : Nat} (hq : q = 3 ∨ q = 5 ∨ q = 7) : Covered q 28 14 := by
  rcases hq with h | h
  · subst q
    have s1 : Covered 3 3 1 := addCoin (d := 1) (emptyCovered 3) (by decide) (by decide)
      ⟨0,0,by decide,by decide⟩
    have s2 : Covered 3 5 3 := addCoin (d := 2) s1 (by decide) (by decide)
      ⟨1,0,by decide,by decide⟩
    have s3 : Covered 3 7 6 := addCoin (d := 3) s2 (by decide) (by decide)
      ⟨1,1,by decide,by decide⟩
    have s4 : Covered 3 11 11 := addCoin (d := 5) s3 (by decide) (by decide)
      ⟨2,0,by decide,by decide⟩
    have s5 : Covered 3 13 17 := addCoin (d := 6) s4 (by decide) (by decide)
      ⟨2,1,by decide,by decide⟩
    exact relax s5 (by decide) (by decide)
  · exact seed57 h

/-- The first coin added at stage t is 2 * firstHalf t = 3^(3+t) + 1. -/
private def firstHalf : Nat → Nat
  | 0 => 14
  | t+1 => 3 * firstHalf t - 1

private theorem stageSize (t : Nat) :
    2 * firstHalf t = 3^(3+t)+1 ∧ 14+t ≤ firstHalf t := by
  induction t with
  | zero => decide
  | succ t ih =>
    obtain ⟨eq, lower⟩ := ih
    change 2*(3*firstHalf t-1) = 3^((3+t)+1)+1 ∧ 14+(t+1) ≤ 3*firstHalf t-1
    rw [Nat.pow_succ]
    omega

private theorem stages {q : Nat} (hq : q = 3 ∨ q = 5 ∨ q = 7) (t : Nat) :
    Covered q (2*firstHalf t) (firstHalf t) := by
  induction t with
  | zero => exact seed hq
  | succ t ih =>
    let u := firstHalf t
    let d := (q-1)/2
    have gap : 1 ≤ d ∧ d ≤ 3 ∧ q = 2*d+1 := by
      rcases hq with h | h | h <;> subst q <;> decide
    obtain ⟨dlo, dhi, dq⟩ := gap
    have size : 2*u = 3^(3+t)+1 ∧ 14+t ≤ u := stageSize t
    obtain ⟨eq, lower⟩ := size
    have c0 : RestrictedTerm q (2*u) := ⟨3+t,0,by decide,by simpa only [Nat.pow_zero] using eq⟩
    have c1 : RestrictedTerm q (2*(u+d)) := by
      refine ⟨3+t,1,by decide,?_⟩
      simp only [Nat.pow_one]
      omega
    have s0 : Covered q (2*u+1) (u+u) := addCoin (d := u) ih (by omega) (by omega) c0
    have s1 : Covered q (2*(u+d)+1) (u+u+(u+d)) :=
      addCoin (d := u+d) s0 (by omega) (by omega) c1
    change Covered q (2*(3*u-1)) (3*u-1)
    exact relax s1 (by omega) (by omega)

/-- The empty sum gives the same conclusion at zero. -/
theorem allDoubles {q : Nat} (hq : q = 3 ∨ q = 5 ∨ q = 7) (n : Nat) : RestrictedSum q (2*n) := by
  obtain ⟨_, large⟩ := stageSize n
  obtain ⟨xs, nd, mem, total⟩ := stages hq n n (by omega)
  exact ⟨xs, nd, fun x hx => (mem x hx).1, total⟩

theorem restrictedEvenAll {q : Nat} (hq : q = 3 ∨ q = 5 ∨ q = 7) (n : Nat) (even : n%2 = 0) :
    RestrictedSum q n := by
  have eq : 2*(n/2) = n := by omega
  rw [← eq]
  exact allDoubles hq (n/2)

theorem restrictedEven {q : Nat} (hq : q = 5 ∨ q = 7) (n : Nat) (even : n%2 = 0) :
    RestrictedSum q n := restrictedEvenAll (Or.inr hq) n even

theorem originalEven {q : Nat} (hq : q = 5 ∨ q = 7) (n : Nat) (even : n%2 = 0) :
    OriginalSum q n := by
  obtain ⟨xs, nd, mem, total⟩ := restrictedEven hq n even
  refine ⟨xs, nd, ?_, total⟩
  intro x hx
  obtain ⟨a,b,_,eq⟩ := mem x hx
  exact ⟨a,b,eq⟩

/-- Sun's stated first clause for the bases (3,7). -/
theorem conjecture1iiFirst (n : Nat) (_positive : 0 < n) (even : n%2 = 0) : OriginalSum 7 n :=
  originalEven (Or.inr rfl) n even

#print axioms restrictedEvenAll
#print axioms restrictedEven
#print axioms originalEven
#print axioms conjecture1iiFirst

end SunThreeSeven
