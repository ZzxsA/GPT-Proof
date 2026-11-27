import DigitCost

/-!
Zhi-Wei Sun, Conjecture 3 in each of OEIS A362743 and A362861 (May 2023).
For fixed bases (4,16), respectively (5,25), the integers b^L - 1
for L > 0 have no representation by mutually nondividing summands.
-/
namespace SunAntichain

/-- A pair stores the exponents in the summand k^a + m^c. -/
abbrev Exponents := Nat × Nat

def term (k m : Nat) (p : Exponents) : Nat := k ^ p.1 + m ^ p.2

def incomparable (x y : Nat) : Prop := ¬ x ∣ y ∧ ¬ y ∣ x

def Representable (k m n : Nat) : Prop :=
  ∃ ps : List Exponents,
    (ps.map (term k m)).sum = n ∧
    ps.Pairwise (fun p q => incomparable (term k m p) (term k m q))

/-- A common-base summand b^lo + b^(lo+gap), encoded by (lo,gap). -/
def value (b : Nat) (p : Exponents) : Nat := b ^ p.1 * (1 + b ^ p.2)

private theorem expand (b : Nat) (p : Exponents) :
    value b p = b ^ p.1 + b ^ (p.1 + p.2) := by
  simp only [value, Nat.mul_add, Nat.mul_one, Nat.pow_add]

private def normalize (i j : Nat) : Exponents :=
  if i ≤ j then (i, j - i) else (j, i - j)

private theorem normalize_value (b i j : Nat) :
    value b (normalize i j) = b ^ i + b ^ j := by
  rw [expand]
  by_cases h : i ≤ j
  · have hh : i + (j-i) = j := by omega
    simp [normalize, h, hh]
  · have hh : j + (i-j) = i := by omega
    simp [normalize, h, hh, Nat.add_comm]

private theorem divides_same_gap {b : Nat} {p q : Exponents}
    (gap : p.2 = q.2) (lo : p.1 ≤ q.1) : value b p ∣ value b q := by
  refine ⟨b ^ (q.1 - p.1), ?_⟩
  have he : p.1 + (q.1 - p.1) = q.1 := by omega
  calc
    value b q = b ^ (p.1 + (q.1 - p.1)) * (1 + b ^ p.2) := by
      simp only [value, he, gap]
    _ = value b p * b ^ (q.1 - p.1) := by
      simp only [value, Nat.pow_add]
      ac_rfl

private theorem different_gap {b : Nat} {p q : Exponents}
    (h : incomparable (value b p) (value b q)) : p.2 ≠ q.2 := by
  intro gap
  rcases Nat.le_total p.1 q.1 with le | ge
  · exact h.1 (divides_same_gap gap le)
  · exact h.2 (divides_same_gap gap.symm ge)

private theorem count_gaps {b : Nat} (ps : List Exponents) (slots : List Nat)
    (hanti : ps.Pairwise (fun p q => incomparable (value b p) (value b q)))
    (hslots : ∀ p ∈ ps, p.2 ∈ slots) : ps.length ≤ slots.length := by
  induction ps generalizing slots with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hanti
    have hp : p.2 ∈ slots := hslots p (by simp)
    have remain : ∀ q ∈ ps, q.2 ∈ slots.erase p.2 := by
      intro q hq
      have ne : q.2 ≠ p.2 := Ne.symm (different_gap (hhead q hq))
      exact (List.mem_erase_of_ne ne).2 (hslots q (by simp [hq]))
    have bound := ih (slots.erase p.2) htail remain
    rw [List.length_erase_of_mem hp] at bound
    have := List.length_pos_of_mem hp
    simp only [List.length_cons]
    omega

private theorem member_le_sum (n : Nat) (xs : List Nat) (hm : n ∈ xs) :
    n ≤ xs.sum := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hm with eq | mem
    · omega
    · have := ih mem
      omega

private def tokens : List Exponents → List Nat
  | [] => []
  | p :: ps => p.1 :: (p.1 + p.2) :: tokens ps

private theorem token_length (ps : List Exponents) : (tokens ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [tokens, List.length_cons, ih]
    omega

private theorem token_sum (b : Nat) (ps : List Exponents) :
    ((tokens ps).map (fun e => b^e)).sum = (ps.map (value b)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [tokens, List.map_cons, List.sum_cons, ih, expand, Nat.add_assoc]

private theorem common_base_impossible {b L : Nat} (hb : 4 ≤ b) (hL : 0 < L)
    (ps : List Exponents)
    (ant : ps.Pairwise (fun p q => incomparable (value b p) (value b q)))
    (sum : (ps.map (value b)).sum + 1 = b^L) : False := by
  have gaps : ∀ p ∈ ps, p.2 ∈ List.range L := by
    intro p hp
    have hm : value b p ∈ ps.map (value b) := List.mem_map_of_mem hp
    have le := member_le_sum (value b p) (ps.map (value b)) hm
    rw [expand] at le
    have hi : b ^ (p.1 + p.2) < b ^ L := by omega
    have hi' := (Nat.pow_lt_pow_iff_right (by omega : 1 < b)).1 hi
    apply List.mem_range.2
    omega
  have size := count_gaps ps (List.range L) ant gaps
  rw [List.length_range] at size
  have tok : ((tokens ps).map (fun e => b^e)).sum + 1 = b^L := by
    rw [token_sum, sum]
  have cost := SunDigits.digitCost b L (tokens ps) (by omega) tok
  rw [token_length] at cost
  have lower := Nat.mul_le_mul_right L (show 3 ≤ b-1 by omega)
  omega

/-- The two bases are distinct for every b in the claimed range. -/
theorem obstruction {b L : Nat} (hb : 4 ≤ b) (hL : 0 < L) :
    ¬ Representable b (b^2) (b^L-1) := by
  rintro ⟨ps, sum, ant⟩
  let convertPair : Exponents → Exponents := fun p => normalize p.1 (2*p.2)
  have hv (p : Exponents) : value b (convertPair p) = term b (b^2) p := by
    simp only [convertPair, normalize_value, term, Nat.pow_mul]
  have ant' : (ps.map convertPair).Pairwise
      (fun p q => incomparable (value b p) (value b q)) := by
    rw [List.pairwise_map]
    simpa only [hv] using ant
  have sum' : ((ps.map convertPair).map (value b)).sum + 1 = b^L := by
    simp only [List.map_map, Function.comp_def, hv]
    change (ps.map (term b (b^2))).sum + 1 = b^L
    have pos : 0 < b^L := Nat.pow_pos (by omega)
    omega
  exact common_base_impossible hb hL _ ant' sum'

def EvenProductConjecture : Prop :=
  ∀ k m : Nat, 1 < k → 1 < m → (k*m)%2 = 0 →
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n → Representable k m n

def OddBasesConjecture : Prop :=
  ∀ k m : Nat, 1 < k → 1 < m → k%2 = 1 → m%2 = 1 →
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n → n%2 = 0 → Representable k m n

theorem refuteA362743 : ¬ EvenProductConjecture := by
  intro claim
  obtain ⟨t, ht⟩ := claim 4 16 (by decide) (by decide) (by decide)
  have growth : t+1 < 4^(t+1) := Nat.lt_pow_self (by decide)
  exact obstruction (b := 4) (L := t+1) (by decide) (by omega)
    (ht (4^(t+1)-1) (by omega))

private theorem five_pow_odd (L : Nat) : ∃ j : Nat, 5^L = 2*j+1 := by
  induction L with
  | zero => exact ⟨0, by decide⟩
  | succ L ih =>
    obtain ⟨j, hj⟩ := ih
    refine ⟨5*j+2, ?_⟩
    rw [Nat.pow_succ, hj]
    omega

theorem refuteA362861 : ¬ OddBasesConjecture := by
  intro claim
  obtain ⟨t, ht⟩ := claim 5 25 (by decide) (by decide) (by decide) (by decide)
  have growth : t+1 < 5^(t+1) := Nat.lt_pow_self (by decide)
  obtain ⟨j, hj⟩ := five_pow_odd (t+1)
  exact obstruction (b := 5) (L := t+1) (by decide) (by omega)
    (ht (5^(t+1)-1) (by omega) (by omega))

#print axioms refuteA362743
#print axioms refuteA362861

end SunAntichain
