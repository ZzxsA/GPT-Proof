import Kimberling

/-!
A coefficient comparison for ordinary integer series. Write D₀ for the
denominator that uses the largest allowed coefficient in each degree.
The cancellation (1-x²)D₀ = (1-x-x²)(1-x-x³) realizes the comparison
by two recurrences with nonnegative feedback.
-/
namespace KimberlingFamily

open Kimberling

def numerator : Series
  | 0 => 1
  | 1 => 1
  | _+2 => 0

private def L (f : Series) : Series
  | 0 => 0
  | n+1 => f n

private def P (f : Series) : Series := fun n => f n - L f n - L (L f) n
private def Q (f : Series) : Series := fun n => f n - L f n - L (L (L f)) n
private def slope (f : Series) : Series := fun n => f n - L f n
private def gap (f : Series) : Series := fun n => f n - L (L f) n

private def base : Series
  | 0 => 1
  | 1 => -2
  | 2 => 1
  | 3 => -2
  | k+4 => if k%2 = 0 then 2 else -1

private def short : Series
  | 0 => 1
  | 1 => -2
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 1
  | _+6 => 0

private theorem base_gap : gap base = short := by
  funext n
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 => decide
  | k+6 =>
    change (if (k+2)%2=0 then (2:Int) else -1) -
      (if k%2=0 then (2:Int) else -1) = 0
    split <;> split <;> omega

private theorem prod_sub_l (f g a : Series) (n : Nat) :
    product (fun i => f i - g i) a n = product f a n - product g a n := by
  induction n generalizing f g with
  | zero => simp [product, Int.sub_mul]
  | succ n ih =>
    change (f 0-g 0)*a (n+1) + product (fun i => f (i+1) - g (i+1)) a n =
      (f 0*a (n+1) + product (fun i => f (i+1)) a n) -
      (g 0*a (n+1) + product (fun i => g (i+1)) a n)
    rw [Int.sub_mul, ih]
    omega

private theorem prod_sub_r (f g a : Series) (n : Nat) :
    product f (fun i => g i - a i) n = product f g n - product f a n := by
  induction n generalizing f with
  | zero => simp [product, Int.mul_sub]
  | succ n ih =>
    change f 0*(g (n+1)-a (n+1)) + product (fun i => f (i+1)) (fun i => g i-a i) n =
      (f 0*g (n+1)+product (fun i => f (i+1)) g n) -
      (f 0*a (n+1)+product (fun i => f (i+1)) a n)
    rw [Int.mul_sub, ih]
    omega

private theorem prod_L_l (f a : Series) (n : Nat) :
    product (L f) a n = L (product f a) n := by
  cases n with
  | zero => simp [product, L]
  | succ n =>
    change 0*a (n+1) + product f a n = _
    simp [L]

private theorem prod_L_r (f a : Series) (n : Nat) :
    product f (L a) n = L (product f a) n := by
  induction n generalizing f with
  | zero => simp [L, product]
  | succ n ih =>
    change f 0 * a n + product (fun i => f (i+1)) (L a) n = product f a n
    rw [ih]
    cases n <;> simp [product,L]

private theorem prod_zero (a : Series) (n : Nat) : product (fun _ => 0) a n = 0 := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    change 0*a (n+1) + product (fun _ => 0) a n = 0
    simp [ih]

private theorem short_product (a : Series) : product short a = Q (P a) := by
  funext n
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 => simp [product, short, Q, P, L] <;> omega
  | k+6 =>
    change 1*a (k+6) + ((-2)*a (k+5)+(0*a (k+4)+(0*a (k+3)+
      (1*a (k+2)+(1*a (k+1)+product (fun _ => 0) a k))))) =
      ((a (k+6)-a (k+5)-a (k+4))-(a (k+5)-a (k+4)-a (k+3)))-
      (a (k+3)-a (k+2)-a (k+1))
    rw [prod_zero]
    omega

private theorem transfer (a : Series) : gap (product base a) = Q (P a) := by
  have h := short_product a
  rw [← base_gap] at h
  funext n
  have e := congrFun h n
  change product (fun i => base i - L (L base) i) a n = _ at e
  rw [prod_sub_l] at e
  have s : product (L (L base)) a = L (L (product base a)) := by
    have a1 := funext (prod_L_l base a)
    have a2 := funext (prod_L_l (L base) a)
    rw [a2,a1]
  simpa [s,gap] using e

private theorem prod_nonneg (f g : Series) (n : Nat)
    (hf : ∀ i, i ≤ n → 0 ≤ f i) (hg : ∀ i, i ≤ n → 0 ≤ g i) :
    0 ≤ product f g n := by
  induction n generalizing f with
  | zero => exact Int.mul_nonneg (hf 0 (by omega)) (hg 0 (by omega))
  | succ n ih =>
    change 0 ≤ f 0*g (n+1) + product (fun i => f (i+1)) g n
    exact Int.add_nonneg (Int.mul_nonneg (hf 0 (by omega)) (hg (n+1) (by omega)))
      (ih (fun i => f (i+1)) (fun i hi => hf (i+1) (by omega)) (fun i hi => hg i (by omega)))

-- The sequence solveQ w satisfies Q (solveQ w)=w in every degree.
private def solveQ (w : Series) : Series
  | 0 => w 0
  | 1 => w 1 + solveQ w 0
  | 2 => w 2 + solveQ w 1
  | k+3 => w (k+3) + solveQ w (k+2) + solveQ w k

private theorem solved (w : Series) : Q (solveQ w) = w := by
  funext n
  match n with
  | 0 | 1 | 2 => simp [Q,L,solveQ] <;> omega
  | k+3 =>
    change solveQ w (k+3) - solveQ w (k+2) - solveQ w k = w (k+3)
    rw [solveQ]
    omega

private theorem Q_injective {f g : Series} (h : Q f = Q g) : f = g := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have e := congrFun h n
    match n with
    | 0 => simpa [Q,L] using e
    | 1 =>
      have t := ih 0 (by omega)
      simp [Q,L] at e
      omega
    | 2 =>
      have t := ih 1 (by omega)
      simp [Q,L] at e
      omega
    | k+3 =>
      have t := ih (k+2) (by omega)
      have u := ih k (by omega)
      change f (k+3)-f (k+2)-f k = g (k+3)-g (k+2)-g k at e
      omega

private theorem Q_gap (u : Series) : Q (gap u) = gap (Q u) := by
  funext n
  match n with
  | 0 | 1 | 2 | 3 | 4 => simp [Q, gap, L] <;> omega
  | k+5 => simp [Q, gap, L] <;> omega

private theorem Q_sub (u v : Series) :
    Q (fun i => u i-v i) = fun i => Q u i-Q v i := by
  funext n
  match n with
  | 0 | 1 | 2 => simp [Q,L] <;> omega
  | k+3 => simp [Q,L] <;> omega

private theorem P_sub (u v : Series) :
    P (fun i => u i-v i) = fun i => P u i-P v i := by
  funext n
  match n with
  | 0 | 1 => simp [P,L] <;> omega
  | k+2 => simp [P,L] <;> omega

private theorem initial_force (n : Nat) :
    slope numerator n - Q numerator n = L (L (L numerator)) n := by
  unfold slope Q
  omega

private theorem prior (f : Series) (n : Nat) (h : ∀ i, i<n → 0 ≤ f i) :
    0 ≤ L f n ∧ 0 ≤ L (L f) n ∧ 0 ≤ L (L (L f)) n := by
  match n with
  | 0 => decide
  | 1 => exact ⟨h 0 (by omega), by decide, by decide⟩
  | 2 => exact ⟨h 1 (by omega), h 0 (by omega), by decide⟩
  | k+3 => exact ⟨h (k+2) (by omega), h (k+1) (by omega), h k (by omega)⟩

private theorem dominated (d : Series)
    (h0 : d 0=1) (h1 : d 1= -2) (h2 : d 2=1) (h3 : d 3= -2)
    (hb : ∀ i, 4 ≤ i → d i ≤ (if i%2=0 then (2:Int) else -1)) (i : Nat) :
    d i ≤ base i := by
  match i with
  | 0 => simp [h0,base]
  | 1 => simp [h1,base]
  | 2 => simp [h2,base]
  | 3 => simp [h3,base]
  | k+4 =>
    have h := hb (k+4) (by omega)
    change d (k+4) ≤ (if k%2=0 then (2:Int) else -1)
    split <;> split at h <;> omega

theorem strictlyIncreasing (d a : Series)
    (h0 : d 0=1) (h1 : d 1= -2) (h2 : d 2=1) (h3 : d 3= -2)
    (hbound : ∀ i, 4 ≤ i → d i ≤ (if i%2=0 then (2:Int) else -1))
    (ha : ∀ n, product d a n = numerator n) (n : Nat) :
    0 < a n ∧ a n < a (n+1) := by
  let c := slope a
  let e := product (fun i => base i - d i) c
  let w := product base c
  let u := solveQ w
  let g : Series := fun i => u i - numerator i
  let v : Series := fun i => c i - u i
  have da : product d a = numerator := funext ha
  have dc : product d c = slope numerator := by
    funext i
    change product d (fun j => a j - L a j) i = _
    rw [prod_sub_r, prod_L_r, da]
    rfl
  have we (i : Nat) : w i = slope numerator i + e i := by
    have b := prod_sub_l base d c i
    rw [dc] at b
    change product base c i = slope numerator i + product (fun j => base j-d j) c i
    omega
  have en (i : Nat) (hi : ∀ j, j<i → 0 ≤ c j) : 0 ≤ e i := by
    cases i with
    | zero =>
      change 0 ≤ (1-d 0)*c 0
      simp [h0]
    | succ k =>
      change 0 ≤ (1-d 0)*c (k+1) + product (fun j => base (j+1)-d (j+1)) c k
      have le := prod_nonneg (fun j => base (j+1)-d (j+1)) c k
        (fun j _ => by have := dominated d h0 h1 h2 h3 hbound (j+1); omega)
        (fun j hj => hi j (by omega))
      simpa [h0] using le
  have qu : Q u = w := solved w
  have pc : P c = gap u := by
    apply Q_injective
    rw [Q_gap, qu]
    exact (transfer c).symm
  have gStep (i : Nat) : Q g i = L (L (L numerator)) i + e i := by
    have b := congrFun (Q_sub u numerator) i
    rw [qu] at b
    have t := we i
    have z := initial_force i
    change Q (fun j => u j-numerator j) i = _
    omega
  have vStep (i : Nat) : P v i = L u i := by
    have b := congrFun (P_sub c u) i
    change P (fun j => c j-u j) i = _
    rw [pc] at b
    change P (fun j => c j-u j) i =
      (u i-L (L u) i) - (u i-L u i-L (L u) i) at b
    omega
  have numNonneg (i : Nat) : 0 ≤ numerator i := by
    match i with
    | 0 | 1 | _+2 => decide
  have main (i : Nat) : 0 ≤ g i ∧ 0 ≤ u i ∧ 0 ≤ v i ∧ (0<i → 0<v i) ∧ 0<c i := by
    induction i using Nat.strongRecOn with
    | ind i ih =>
      have epos := en i (fun j hj => Int.le_of_lt (ih j hj).2.2.2.2)
      have gprev := prior g i (fun j hj => (ih j hj).1)
      have vprev := prior v i (fun j hj => (ih j hj).2.2.1)
      have uprev := prior u i (fun j hj => (ih j hj).2.1)
      have nprev := prior numerator i (fun j _ => numNonneg j)
      have gEq := gStep i
      have vEq := vStep i
      change g i-L g i-L (L (L g)) i = _ at gEq
      change v i-L v i-L (L v) i = _ at vEq
      have gn : 0 ≤ g i := by omega
      have un : 0 ≤ u i := by
        have ni := numNonneg i
        change 0 ≤ u i - numerator i at gn
        omega
      have vn : 0 ≤ v i := by omega
      have vp : 0<i → 0<v i := by
        intro ip
        match i with
        | 0 => omega
        | 1 =>
          have g0 := (ih 0 (by omega)).1
          change 0 ≤ u 0 - 1 at g0
          change v 1 - v 0 - 0 = u 0 at vEq
          have v0 := (ih 0 (by omega)).2.2.1
          omega
        | k+2 =>
          have vp := (ih (k+1) (by omega)).2.2.2.1 (by omega)
          change v (k+2) - v (k+1) - v k = u (k+1) at vEq
          have vk := (ih k (by omega)).2.2.1
          have uk := (ih (k+1) (by omega)).2.1
          omega
      refine ⟨gn, un, vn, vp, ?_⟩
      by_cases iz : i=0
      · subst i
        change 0 ≤ u 0 - 1 at gn
        change 0 ≤ c 0-u 0 at vn
        omega
      · have vz := vp (by omega)
        change 0 < c i-u i at vz
        omega
  have increasing (i : Nat) : a i < a (i+1) := by
    have hi := (main (i+1)).2.2.2.2
    change 0 < a (i+1)-a i at hi
    omega
  refine ⟨?_,increasing n⟩
  induction n with
  | zero =>
    have hi := (main 0).2.2.2.2
    change 0 < a 0-0 at hi
    omega
  | succ k ih =>
    have step := increasing k
    omega

#print axioms strictlyIncreasing

end KimberlingFamily
