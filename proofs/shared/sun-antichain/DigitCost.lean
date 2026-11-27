import Std

namespace SunDigits

/-- Count the units and divide each nonunit coin by the base. -/
private def units : List Nat → Nat
  | [] => 0
  | 0 :: es => units es + 1
  | (_ + 1) :: es => units es

private def down : List Nat → List Nat
  | [] => []
  | 0 :: es => down es
  | (e + 1) :: es => e :: down es

private theorem splitLength (es : List Nat) : es.length = units es + (down es).length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases e <;> simp only [List.length_cons, units, down] <;> omega

private theorem splitSum (b : Nat) (es : List Nat) :
    (es.map (fun e => b ^ e)).sum = units es + b * ((down es).map (fun e => b ^ e)).sum := by
  induction es with
  | nil => simp [units, down]
  | cons e es ih =>
    cases e with
    | zero =>
      simp only [List.map_cons, List.sum_cons, Nat.pow_zero, units, down]
      omega
    | succ e =>
      simp only [List.map_cons, List.sum_cons, Nat.pow_succ, units, down, Nat.mul_add]
      rw [Nat.mul_comm (b ^ e) b]
      omega

private theorem prependUnitsSum (b t : Nat) (es : List Nat) :
    ((List.replicate t 0 ++ es).map (fun e : Nat => b ^ e)).sum =
      t + (es.map (fun e => b ^ e)).sum := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [List.replicate_succ, List.cons_append, List.map_cons, List.sum_cons, Nat.pow_zero, ih]
    omega

/-- The number b^L - 1 requires at least (b - 1) * L powers of b, with repetition allowed. -/
theorem digitCost (b L : Nat) (es : List Nat) (hb : 2 ≤ b)
    (h : (es.map (fun e => b ^ e)).sum + 1 = b ^ L) :
    (b - 1) * L ≤ es.length := by
  induction L generalizing es with
  | zero => simp
  | succ L ih =>
    let s := ((down es).map (fun e => b ^ e)).sum
    let z := units es
    have hbase := h
    rw [splitSum b es, Nat.pow_succ, Nat.mul_comm (b ^ L) b] at hbase
    change z + b * s + 1 = b * (b ^ L) at hbase
    have hs : s < b ^ L := by
      by_cases hle : b ^ L ≤ s
      · have hm := Nat.mul_le_mul_left b hle
        omega
      · omega
    obtain ⟨t, ht⟩ : ∃ t : Nat, b ^ L = s + t + 1 :=
      ⟨b ^ L - s - 1, by omega⟩
    have hexpand : b * (b ^ L) = b * s + b * t + b := by
      calc
        b * (b ^ L) = b * (s + t + 1) := congrArg (fun x => b * x) ht
        _ = b * s + b * t + b := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    -- Retain t units for the next digit and pay b - 1 units for this digit.
    have hnext : (((List.replicate t 0 ++ down es).map (fun e => b ^ e)).sum + 1) = b ^ L := by
      rw [prependUnitsSum]
      change t + s + 1 = b ^ L
      omega
    have smaller := ih (List.replicate t 0 ++ down es) hnext
    rw [List.length_append, List.length_replicate] at smaller
    have hlen := splitLength es
    change es.length = z + (down es).length at hlen
    have ht_le : t ≤ b * t := by
      simpa using Nat.mul_le_mul_right t (show 1 ≤ b by omega)
    rw [Nat.mul_succ]
    omega

end SunDigits
