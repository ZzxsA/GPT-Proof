import SeedFive

/-!
The base-five clause of Zhi-Wei Sun's Conjecture 1(i), OEIS A362861.
Here the target and the available summands are divided by two.
-/
namespace SunFive

def HalfAtom (x : Nat) : Prop :=
  ∃ a j : Nat, j ≤ a ∧ x = halfTerm a j

def HalfRep (n : Nat) : Prop :=
  ∃ xs : List Nat, xs.Nodup ∧ (∀ x ∈ xs, HalfAtom x) ∧ xs.sum = n

/-- Every integer in [256,256+width) can use distinct half-terms below cap. -/
private def Covered (cap width : Nat) : Prop :=
  ∀ n : Nat, 256 ≤ n → n < 256+width →
    ∃ xs : List Nat, xs.Nodup ∧ (∀ x ∈ xs, HalfAtom x ∧ x < cap) ∧ xs.sum = n

private theorem hole_small {n : Nat} (h : n ∈ holes) : n ≤ 255 := by
  simp [holes] at h
  omega

private theorem seed_atom_bound {x : Nat} (h : x ∈ seedCoins) : HalfAtom x ∧ x < 1563 := by
  obtain ⟨a,j,hj,ha,hx⟩ := seed_terms x h
  refine ⟨⟨a,j,hj,hx⟩, ?_⟩
  have leA : 5^a ≤ 5^4 := Nat.pow_le_pow_of_le (by decide) (by omega)
  have leJ : 5^j ≤ 5^4 := Nat.pow_le_pow_of_le (by decide) (by omega)
  change 5^a ≤ 625 at leA
  change 5^j ≤ 625 at leJ
  rw [hx]
  unfold halfTerm
  omega

private theorem initial : Covered (halfTerm 5 0) (halfTerm 5 0) := by
  intro n lo hi
  change n < 256+1563 at hi
  obtain ⟨xs, sub, total⟩ := (seed_exact n (by omega)).2 (fun h => by
    have := hole_small h
    omega)
  refine ⟨xs, List.Nodup.sublist sub seed_nodup, ?_, total⟩
  intro x hx
  exact seed_atom_bound (sub.subset hx)

private theorem relax {c w c' w' : Nat} (old : Covered c w)
    (cap : c ≤ c') (width : w' ≤ w) : Covered c' w' := by
  intro n lo hi
  obtain ⟨xs, nd, mem, total⟩ := old n lo (by omega)
  exact ⟨xs, nd, fun x hx => ⟨(mem x hx).1, Nat.lt_of_lt_of_le (mem x hx).2 cap⟩, total⟩

private theorem add_coin {c w x : Nat} (old : Covered c w)
    (fresh : c ≤ x) (fits : x ≤ w) (atom : HalfAtom x) : Covered (x+1) (w+x) := by
  intro n lo hi
  by_cases lower : n < 256+w
  · exact relax old (by omega : c ≤ x+1) (Nat.le_refl w) n lo lower
  · obtain ⟨xs, nd, mem, total⟩ := old (n-x) (by omega) (by omega)
    have absent : x ∉ xs := fun hx => by
      have := (mem x hx).2
      omega
    refine ⟨x :: xs, List.nodup_cons.2 ⟨absent, nd⟩, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with eq | tail
      · subst y
        exact ⟨atom, by omega⟩
      · obtain ⟨ay, bound⟩ := mem y tail
        exact ⟨ay, by omega⟩
    · simp only [List.sum_cons]
      omega

private theorem block {s : Nat} (hs : 5 ≤ s)
    (old : Covered (halfTerm s 0) (halfTerm s 0)) :
    Covered (halfTerm (s+1) 0) (halfTerm (s+1) 0) := by
  let a := halfTerm s 0
  let b := halfTerm s 1
  let c := halfTerm s 2
  let d := halfTerm s 3
  let e := halfTerm s 4
  let nextCoin := halfTerm (s+1) 0
  have hp : 3125 ≤ 5^s := Nat.pow_le_pow_of_le (a := 5) (n := 5) (by decide) hs
  have sizes : a < b ∧ b < c ∧ c < d ∧ d < e ∧ e+1 ≤ nextCoin ∧
      e ≤ a+a ∧ nextCoin ≤ a+a+b+c+d+e := by
    change ((5^s+1)/2 < (5^s+5)/2) ∧ ((5^s+5)/2 < (5^s+25)/2) ∧
      ((5^s+25)/2 < (5^s+125)/2) ∧ ((5^s+125)/2 < (5^s+625)/2) ∧
      (5^s+625)/2+1 ≤ (5^(s+1)+1)/2 ∧ (5^s+625)/2 ≤ (5^s+1)/2+(5^s+1)/2 ∧
      (5^(s+1)+1)/2 ≤ (5^s+1)/2+(5^s+1)/2+(5^s+5)/2+
        (5^s+25)/2+(5^s+125)/2+(5^s+625)/2
    rw [Nat.pow_succ]
    omega
  obtain ⟨ab,bc,cd,de,en,fit,total⟩ := sizes
  have one : Covered (a+1) (a+a) :=
    add_coin old (Nat.le_refl a) (Nat.le_refl a) ⟨s,0,by omega,rfl⟩
  have two : Covered (b+1) (a+a+b) := add_coin one (by omega) (by omega) ⟨s,1,by omega,rfl⟩
  have three : Covered (c+1) (a+a+b+c) := add_coin two (by omega) (by omega) ⟨s,2,by omega,rfl⟩
  have four : Covered (d+1) (a+a+b+c+d) := add_coin three (by omega) (by omega) ⟨s,3,by omega,rfl⟩
  have five : Covered (e+1) (a+a+b+c+d+e) := add_coin four (by omega) (by omega) ⟨s,4,by omega,rfl⟩
  exact relax five en total

private theorem all_blocks (d : Nat) : Covered (halfTerm (5+d) 0) (halfTerm (5+d) 0) := by
  induction d with
  | zero => exact initial
  | succ d ih => exact block (by omega : 5 ≤ 5+d) ih

theorem tail_five {n : Nat} (lo : 256 ≤ n) : HalfRep n := by
  have pow : 5+2*n < 5^(5+2*n) := Nat.lt_pow_self (by decide)
  have large : n < 256+halfTerm (5+2*n) 0 := by
    change n < 256+(5^(5+2*n)+1)/2
    omega
  obtain ⟨xs,nd,mem,tot⟩ := all_blocks (2*n) n lo large
  exact ⟨xs,nd,fun x hx => (mem x hx).1,tot⟩

private theorem member_le_total (ys : List Nat) (x : Nat) (hx : x ∈ ys) : x ≤ ys.sum := by
  induction ys with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hx with eq | mem
    · omega
    · have := ih mem
      omega

private theorem perm_sum {xs ys : List Nat} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [List.sum_cons, ih]
  | swap a b as => simp only [List.sum_cons]; omega
  | trans h k ih ik => exact ih.trans ik

/-- Reorder a distinct finite selection into its order in the containing list. -/
private theorem sublist_sum (pool xs : List Nat) (nd : xs.Nodup) (sub : xs ⊆ pool) :
    ∃ ys : List Nat, ys.Sublist pool ∧ ys.sum = xs.sum := by
  induction pool generalizing xs with
  | nil =>
    have emp := List.eq_nil_of_subset_nil sub
    subst xs
    exact ⟨[], .slnil, rfl⟩
  | cons a rest ih =>
    by_cases hit : a ∈ xs
    · have small : xs.erase a ⊆ rest := by
        intro x hx
        obtain ⟨ne, orig⟩ := nd.mem_erase_iff.mp hx
        rcases List.mem_cons.mp (sub orig) with eq | tail
        · exact (ne eq).elim
        · exact tail
      obtain ⟨ys, inc, eq⟩ := ih (xs.erase a) (nd.erase a) small
      refine ⟨a::ys, inc.cons₂ a, ?_⟩
      have p := perm_sum (List.perm_cons_erase hit)
      simp only [List.sum_cons] at p ⊢
      omega
    · have small : xs ⊆ rest := by
        intro x hx
        rcases List.mem_cons.mp (sub hx) with eq | tail
        · subst x
          exact (hit hx).elim
        · exact tail
      obtain ⟨ys,inc,eq⟩ := ih xs nd small
      exact ⟨ys,inc.cons a,eq⟩

theorem normalized_five_exact (n : Nat) : HalfRep n ↔ n ∉ holes := by
  constructor
  · rintro ⟨xs, nd, atoms, total⟩ hole
    have lim := hole_small hole
    have small : xs ⊆ seedCoins := by
      intro x hx
      have bound := member_le_total xs x hx
      obtain ⟨a,j,hj,val⟩ := atoms x hx
      have ha : a < 5 := by
        by_cases large : 5 ≤ a
        · have hp : 3125 ≤ 5^a := Nat.pow_le_pow_of_le (a := 5) (n := 5) (by decide) large
          unfold halfTerm at val
          omega
        · omega
      rw [val]
      exact seed_small_atom ha hj
    obtain ⟨ys,inc,eq⟩ := sublist_sum seedCoins xs nd small
    exact (seed_exact n (by omega)).1 ⟨ys,inc,eq.trans total⟩ hole
  · intro good
    by_cases lo : 256 ≤ n
    · exact tail_five lo
    · obtain ⟨xs,inc,total⟩ := (seed_exact n (by omega)).2 good
      exact ⟨xs,List.Nodup.sublist inc seed_nodup,fun x hx => (seed_atom_bound (inc.subset hx)).1,total⟩

end SunFive
