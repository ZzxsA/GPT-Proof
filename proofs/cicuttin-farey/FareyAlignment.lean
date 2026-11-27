import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace FareyAlignment
open Finset

/-- Number of intervals in the Farey sequence, including 0 and 1 as endpoints. -/
def steps (n : ℕ) : ℕ := ∑ d ∈ range (n+1), d.totient

/-- The zero-based rank of the reduced fraction a/d in the Farey list. -/
def rank (n a d : ℕ) : ℕ :=
  ∑ e ∈ range (n+1), ((range e).filter (fun b => e.Coprime b ∧ b*d < a*e)).card

/-- Count all proper aligned fractions, with 1 added for the common right endpoint. -/
def count (n : ℕ) : ℕ :=
  1 + ∑ d ∈ range (n+1),
    ((range d).filter (fun a => d.Coprime a ∧ a * steps n = rank n a d * d)).card

private theorem order_le_steps (n : ℕ) : n ≤ steps n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hp := Nat.totient_pos.mpr (Nat.succ_pos n)
    unfold steps at *
    rw [sum_range_succ]
    omega

private theorem count_le (n : ℕ) (hn : 0 < n) :
    count n ≤ 1 + n * (steps n).divisors.card := by
  let M := steps n
  have hm : 0 < M := lt_of_lt_of_le hn (order_le_steps n)
  let S := (range (n+1)).filter (fun d => d ∣ M)
  have hsub : S ⊆ M.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, hm.ne'⟩
  have hrow (d : ℕ) (hd : d ∈ range (n+1)) :
      ((range d).filter (fun a => d.Coprime a ∧ a * steps n = rank n a d * d)).card ≤
        if d ∣ M then n else 0 := by
    split_ifs with h
    · exact (card_filter_le _ _).trans (by simpa using (Nat.le_of_lt_succ (mem_range.mp hd)))
    · have he : ((range d).filter (fun a => d.Coprime a ∧ a * steps n = rank n a d * d)) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro a ha
        obtain ⟨_, hc, heq⟩ := mem_filter.mp ha
        apply h
        apply hc.dvd_of_dvd_mul_left
        exact ⟨rank n a d, by simpa [M, Nat.mul_comm] using heq⟩
      simp [he]
  unfold count
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ d ∈ range (n+1), if d ∣ M then n else 0 := sum_le_sum hrow
    _ = S.card * n := by rw [← sum_filter]; simp [S]
    _ ≤ n * M.divisors.card := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (card_le_card hsub)

/-- A uniform explicit constant for the elementary divisor estimate. -/
private def C : ℕ := 4096 ^ 16

private theorem small_exp (a : ℕ) : (a+1)^4 ≤ 4096 * 2^a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases ha : a ≤ 6
    · interval_cases a <;> decide
    · let b := a-4
      have hab : a = b+4 := by dsimp [b]; omega
      have hb : b < a := by dsimp [b]; omega
      have hpow := Nat.pow_le_pow_left (show a+1 ≤ 2*(b+1) by dsimp [b]; omega) 4
      calc
        (a+1)^4 ≤ (2*(b+1))^4 := hpow
        _ = 16*(b+1)^4 := by ring
        _ ≤ 16*(4096*2^b) := Nat.mul_le_mul_left _ (ih b hb)
        _ = 4096 * 2^a := by rw [hab, pow_add]; ring

private theorem divisor_fourth (m : ℕ) : m.divisors.card^4 ≤ C*m := by
  by_cases hm : m=0
  · simp [hm]
  let P := m.primeFactors
  let factor := fun p : ℕ => if p < 16 then 4096 else 1
  have hpp (p : ℕ) (hp : p ∈ P) : (m.factorization p+1)^4 ≤ factor p * p^(m.factorization p) := by
    let a := m.factorization p
    have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    change (a+1)^4 ≤ factor p * p^a
    by_cases h : p<16
    · simp only [factor, if_pos h]
      exact (small_exp a).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 a))
    · simp only [factor, if_neg h, one_mul]
      calc
        (a+1)^4 ≤ (2^a)^4 := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := a)) _
        _ = 16^a := by rw [← pow_mul, Nat.mul_comm a 4, pow_mul]; rfl
        _ ≤ p^a := Nat.pow_le_pow_left (by omega) _
  have hcard : (P.filter (fun p => p<16)).card ≤ 16 := by
    simpa using card_le_card (show P.filter (fun p => p<16) ⊆ range 16 from
      fun p hp => mem_range.mpr (mem_filter.mp hp).2)
  have hconst : P.prod factor ≤ C := by
    change (∏ p ∈ P, if p<16 then 4096 else 1) ≤ _
    rw [← prod_filter, prod_const]
    exact Nat.pow_le_pow_right (by decide) hcard
  have hfac : (∏ p ∈ P, p ^ m.factorization p) = m := Nat.factorization_prod_pow_eq_self hm
  calc
    m.divisors.card^4 = ∏ p ∈ P, (m.factorization p+1)^4 := by
      rw [Nat.card_divisors hm, prod_pow]; rfl
    _ ≤ ∏ p ∈ P, factor p * p^(m.factorization p) := prod_le_prod' hpp
    _ = (P.prod factor) * m := by rw [prod_mul_distrib, hfac]
    _ ≤ C*m := Nat.mul_le_mul_right _ hconst

private theorem triangular (n : ℕ) : 2*(∑ x ∈ range (n+1), x) = n*(n+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, mul_add, ih]; ring

private theorem shape (n : ℕ) (hn : 0 < n) :
    n^7 ≤ 16*C*(steps n)^4 ∧ steps n ≤ 2*n^2 := by
  let R := range (n+1)
  let S := R.image (fun x => x.divisors.card)
  have hs : S.Nonempty := ⟨(0:ℕ).divisors.card, mem_image.mpr ⟨0, mem_range.mpr (by omega), rfl⟩⟩
  let t := S.max' hs
  obtain ⟨x, hx, ht⟩ := mem_image.mp (S.max'_mem hs)
  have ht4 : t^4 ≤ C*n := by
    change (S.max' hs)^4 ≤ _
    rw [← ht]
    exact (divisor_fourth x).trans (Nat.mul_le_mul_left _ (Nat.le_of_lt_succ (mem_range.mp hx)))
  have hsum : (∑ x ∈ R, x) ≤ steps n * t := by
    unfold steps
    rw [sum_mul]
    apply sum_le_sum
    intro d hd
    have hdt : d.divisors.card ≤ t := S.le_max' _ (mem_image.mpr ⟨d, hd, rfl⟩)
    by_cases zd : d=0
    · simp [zd]
    have hphi : 0 < d.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero zd)
    calc
      d = ∑ i ∈ d.divisors, i.totient := (Nat.sum_totient d).symm
      _ ≤ ∑ _i ∈ d.divisors, d.totient := sum_le_sum (fun i hi =>
        Nat.le_of_dvd hphi (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hi)))
      _ ≤ d.totient*t := by simpa [mul_comm] using Nat.mul_le_mul_right d.totient hdt
  have h2 : n^2 ≤ 2*steps n*t := by
    have htri := triangular n
    change (∑ x ∈ range (n+1), x) ≤ _ at hsum
    nlinarith
  constructor
  · apply Nat.le_of_mul_le_mul_left (c:=n)
    · calc
        n*n^7 = (n^2)^4 := by ring
        _ ≤ (2*steps n*t)^4 := Nat.pow_le_pow_left h2 _
        _ = (2*steps n)^4*t^4 := by ring
        _ ≤ (2*steps n)^4*(C*n) := Nat.mul_le_mul_left _ ht4
        _ = n*(16*C*(steps n)^4) := by ring
    · exact hn
  · calc
      steps n ≤ ∑ _d ∈ R, n := sum_le_sum (fun d hd =>
        (Nat.totient_le d).trans (Nat.le_of_lt_succ (mem_range.mp hd)))
      _ = (n+1)*n := by simp [R]
      _ ≤ 2*n^2 := by nlinarith

/-- Reciprocal-integer epsilon form of count(n)/|F_n| → 0. -/
theorem density_zero (k : ℕ) : ∃ N, ∀ n ≥ N, k * count n ≤ steps n+1 := by
  refine ⟨512*C^2*k^4 + 1, ?_⟩
  intro n hn
  have hpos : 0 < n := by omega
  let M := steps n
  have hm : 0 < M := lt_of_lt_of_le hpos (order_le_steps n)
  obtain ⟨hg, hu⟩ := shape n hpos
  have hc : 1 ≤ M.divisors.card :=
    card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, hm.ne'⟩⟩
  have hx : 1 ≤ n * M.divisors.card := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hpos.ne' (by omega))
  have ha : count n ≤ 2*(n*M.divisors.card) := by
    have h := count_le n hpos
    change count n ≤ 1 + n * M.divisors.card at h
    omega
  have hs : M.divisors.card^4 ≤ C*(2*n^2) := (divisor_fourth M).trans (Nat.mul_le_mul_left _ hu)
  have hpow : 16*C*(k*count n)^4 ≤ 16*C*M^4 := calc
    16*C*(k*count n)^4 ≤ 16*C*(k*(2*(n*M.divisors.card)))^4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ ha) _)
    _ = (256*C*k^4*n^4)*M.divisors.card^4 := by ring
    _ ≤ (256*C*k^4*n^4)*(C*(2*n^2)) := Nat.mul_le_mul_left _ hs
    _ = (512*C^2*k^4)*n^6 := by ring
    _ ≤ n*n^6 := Nat.mul_le_mul_right _ (by omega)
    _ = n^7 := by ring
    _ ≤ 16*C*M^4 := hg
  have h4 : (k*count n)^4 ≤ M^4 := Nat.le_of_mul_le_mul_left hpow (by decide : 0 < 16*C)
  have hle : k*count n ≤ M := by
    by_contra! h
    exact (not_lt_of_ge h4) (Nat.pow_lt_pow_left h (by decide))
  exact hle.trans (Nat.le_succ _)

#print axioms density_zero
end FareyAlignment
