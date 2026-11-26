import Std

/-!
Counterexample to the greatest-prime-factor statement in Samuel Harkness,
OEIS A353890, posted May 9, 2022.

The period of a binary word at exponent 29 need not be computed: the
proposed greatest prime factor is composite for every possible period.
`three_consecutive_powers` is a separate modular witness for the
prime 108050869; the proof relating a prime collision to the least
period uses a resultant and CRT in the mathematical argument.
-/

namespace Harkness

/-- A natural number at least two is prime if it has no proper divisor
strictly above one. Division here is ordinary natural-number division. -/
def Prime (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ d : Fin n, 1 < d.val → n % d.val ≠ 0

def GreatestPrimeFactor (n p : Nat) : Prop :=
  Prime p ∧ p ∣ n ∧ ∀ q, Prime q → q ∣ n → q ≤ p

def jacobsthalPair : Nat → Nat × Nat
  | 0 => (0,1)
  | n+1 =>
    let t := jacobsthalPair n
    (t.2,t.2 + 2*t.1)

def jacobsthal (n : Nat) := (jacobsthalPair n).1

theorem prime29 : Prime 29 := by unfold Prime; decide

theorem jacobsthal29 : jacobsthal 29 = 59 * 3033169 := by decide

theorem notPrimeJacobsthal29 : ¬ Prime (jacobsthal 29) := by
  rw [jacobsthal29]
  intro h
  exact h.2 ⟨59, by decide⟩ (by decide) (by decide)

/-- No period function, in particular not the actual least-period function,
can satisfy the asserted greatest-prime-factor identity at every prime. -/
theorem counterexample (period : Nat → Nat) :
    ¬ (∀ n, 5 ≤ n → Prime n → GreatestPrimeFactor (period n) (jacobsthal n)) := by
  intro claimed
  exact notPrimeJacobsthal29 (claimed 29 (by decide) prime29).1

def firstDiff (n m : Nat) : Nat := (m + 1) ^ n - m ^ n

/-- gcd(a,b) = gcd(a,b-a) for these consecutive increasing differences. -/
def coprimeEntry (n m : Nat) : Bool :=
  Nat.gcd (firstDiff n m) (firstDiff n (m + 1)) == 1

def IsPeriod (n a : Nat) : Prop :=
  0 < a ∧ ∀ m : Nat, 1 ≤ m → coprimeEntry n (m + a) = coprimeEntry n m

def IsLeastPeriod (n a : Nat) : Prop :=
  IsPeriod n a ∧ ∀ h : Nat, IsPeriod n h → a ≤ h

theorem conjecture_false :
    ¬ (∀ n : Nat, 5 ≤ n → Prime n →
      ∃ a : Nat, IsLeastPeriod n a ∧ GreatestPrimeFactor a (jacobsthal n)) := by
  intro claimed
  obtain ⟨_, _, hg⟩ := claimed 29 (by decide) prime29
  exact notPrimeJacobsthal29 hg.1

def p : Nat := 108050869
def m : Nat := 71665491

theorem three_consecutive_powers :
    m ^ 29 % p = 95285273 ∧
    (m+1) ^ 29 % p = 95285273 ∧
    (m+2) ^ 29 % p = 95285273 := by decide

/-- The claimed Jacobsthal value and the stated alternative numerical
expression computed from the three primes 3, 59, 3033169. -/
theorem arithmetic :
    2 ^ 29 + 1 = 3 * 59 * 3033169 ∧
    (2 ^ 29 + 1) / 3 = 59 * 3033169 ∧
    ((3-1)*(59-1)*(3033169-1))/2+1 = 5 * 35184749 := by decide

#print axioms counterexample
#print axioms conjecture_false
#print axioms three_consecutive_powers

end Harkness
