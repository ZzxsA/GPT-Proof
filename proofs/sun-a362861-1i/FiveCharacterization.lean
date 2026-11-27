import FiveCoverage

namespace SunFive

/-- The ordinary, unscaled summands from Sun's base-five conjecture. -/
def RepresentedTwice (n : Nat) : Prop :=
  ∃ xs : List Nat, xs.Nodup ∧ (∀ x ∈ xs, ∃ a b : Nat, x = 5^a+5^b) ∧ xs.sum = 2*n

private def twice (x : Nat) : Nat := 2*x

private theorem odd_power (a : Nat) : ∃ t : Nat, 5^a = 2*t+1 := by
  induction a with
  | zero => exact ⟨0,by decide⟩
  | succ a ih =>
    obtain ⟨t,ht⟩ := ih
    refine ⟨5*t+2, ?_⟩
    rw [Nat.pow_succ,ht]
    omega

private theorem twice_half (a j : Nat) : twice (halfTerm a j) = 5^a+5^j := by
  obtain ⟨s,hs⟩ := odd_power a
  obtain ⟨t,ht⟩ := odd_power j
  unfold twice halfTerm
  omega

private theorem half_atom (a j : Nat) : HalfAtom (halfTerm a j) := by
  rcases Nat.le_total j a with h | h
  · exact ⟨a,j,h,rfl⟩
  · exact ⟨j,a,h,by simp only [halfTerm,Nat.add_comm]⟩

private theorem twice_sum (xs : List Nat) : (xs.map twice).sum = 2*xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih,twice,Nat.mul_add]

private theorem twice_nodup (xs : List Nat) : (xs.map twice).Nodup ↔ xs.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have member : twice x ∈ xs.map twice ↔ x ∈ xs := by
      constructor
      · intro mem
        obtain ⟨y,hy,he⟩ := List.mem_map.mp mem
        unfold twice at he
        have eq : y = x := by omega
        simpa only [eq] using hy
      · intro mem
        exact List.mem_map_of_mem mem
    simp only [List.map_cons,List.nodup_cons,member,ih]

private theorem halve (xs : List Nat)
    (h : ∀ x ∈ xs, ∃ a j : Nat, x = 5^a+5^j) :
    ∃ ys : List Nat, ys.map twice = xs ∧ ∀ y ∈ ys, HalfAtom y := by
  induction xs with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨a,j,hx⟩ := h x (by simp)
    obtain ⟨ys, he, mem⟩ := ih (fun v hv => h v (List.mem_cons_of_mem x hv))
    refine ⟨halfTerm a j :: ys, ?_, ?_⟩
    · simp only [List.map_cons,twice_half,he,hx]
    · intro v hv
      rcases List.mem_cons.mp hv with eq | tail
      · rw [eq]
        exact half_atom a j
      · exact mem v tail

theorem represented_iff_half (n : Nat) : RepresentedTwice n ↔ HalfRep n := by
  constructor
  · rintro ⟨xs,nd,atoms,total⟩
    obtain ⟨ys,he,ha⟩ := halve xs atoms
    rw [←he] at nd total
    rw [twice_sum] at total
    exact ⟨ys,(twice_nodup ys).1 nd,ha,by omega⟩
  · rintro ⟨ys,nd,atoms,total⟩
    refine ⟨ys.map twice,(twice_nodup ys).2 nd,?_,by rw [twice_sum,total]⟩
    intro x hx
    obtain ⟨y,hy,he⟩ := List.mem_map.mp hx
    obtain ⟨a,j,_,hj⟩ := atoms y hy
    refine ⟨a,j,?_⟩
    rw [←he,hj,twice_half]

/-- The positive-index OEIS statement also holds at zero with the empty sum. -/
theorem basefive_characterization (n : Nat) : RepresentedTwice n ↔ n ∉ holes :=
  (represented_iff_half n).trans (normalized_five_exact n)

#print axioms basefive_characterization

end SunFive
