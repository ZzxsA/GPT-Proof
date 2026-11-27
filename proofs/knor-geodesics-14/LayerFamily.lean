import Std

/-! An explicit injection of `Fin (25 * 3^m)` into canonically oriented
geodesics of the graph with layer widths 1,2,3,...,3,2,1 (m middle layers).
The vertex sequence itself is the witness. All shortestness statements
quantify over arbitrary competing walks with the same endpoints. -/
namespace LayerFamily

set_option maxHeartbeats 0
set_option maxRecDepth 100000

inductive Vertex where
  | leftEnd | leftInner (b : Bool) | middle (i : Nat) (digit : Fin 3)
  | rightInner (b : Bool) | rightEnd
  deriving DecidableEq, Repr

def valid (m : Nat) : Vertex → Prop
  | .middle i _ => i < m
  | _ => True

def level (m : Nat) : Vertex → Nat
  | .leftEnd => 0 | .leftInner _ => 1 | .middle i _ => i+2
  | .rightInner _ => m+2 | .rightEnd => m+3

def Edge (m : Nat) (u v : Vertex) : Prop := valid m u ∧ valid m v ∧
  (level m u + 1 = level m v ∨ level m v + 1 = level m u)

/-- A complete, duplicate-free vertex list. Its order is irrelevant. -/
def allVertices : Nat → List Vertex
  | 0 => [.leftEnd, .leftInner false, .leftInner true, .rightInner false, .rightInner true, .rightEnd]
  | m+1 => .middle m 0 :: .middle m 1 :: .middle m 2 :: allVertices m

private theorem three_digits : ∀ d : Fin 3, d=0 ∨ d=1 ∨ d=2 := by decide

theorem vertex_mem (m : Nat) (v : Vertex) : v ∈ allVertices m ↔ valid m v := by
  induction m generalizing v with
  | zero =>
    cases v with
    | leftEnd => simp [allVertices, valid]
    | rightEnd => simp [allVertices, valid]
    | leftInner b => cases b <;> simp [allVertices, valid]
    | rightInner b => cases b <;> simp [allVertices, valid]
    | middle i d => simp [allVertices, valid]
  | succ m ih =>
    cases v with
    | leftEnd => simp [allVertices, ih, valid]
    | rightEnd => simp [allVertices, ih, valid]
    | leftInner b => simp [allVertices, ih, valid]
    | rightInner b => simp [allVertices, ih, valid]
    | middle i d =>
      rcases three_digits d with rfl|rfl|rfl <;>
        simp [allVertices, ih, valid] <;> omega

theorem vertex_nodup (m : Nat) : (allVertices m).Nodup := by
  induction m with
  | zero => decide
  | succ m ih =>
    have d01 : (0 : Fin 3) ≠ 1 := by decide
    have d02 : (0 : Fin 3) ≠ 2 := by decide
    have d12 : (1 : Fin 3) ≠ 2 := by decide
    simp [allVertices, List.nodup_cons, vertex_mem, valid, ih, d01, d02, d12]

theorem vertex_order (m : Nat) : (allVertices m).length = 3*m+6 := by
  induction m with
  | zero => decide
  | succ m ih => simp only [allVertices, List.length_cons, ih]; omega

theorem symmetric {m : Nat} {u v : Vertex} (e : Edge m u v) : Edge m v u :=
  ⟨e.2.1, e.1, e.2.2.elim Or.inr Or.inl⟩

theorem loopless (m : Nat) (u : Vertex) : ¬ Edge m u u := by
  intro h
  have step := h.2.2
  omega

inductive Joins (m : Nat) : Vertex → Vertex → Prop
  | refl {u} : valid m u → Joins m u u
  | edge {u v} : Edge m u v → Joins m u v
  | trans {u v w} : Joins m u v → Joins m v w → Joins m u w

private theorem joins_symm {m : Nat} {u v : Vertex} (h : Joins m u v) : Joins m v u := by
  induction h with
  | refl hu => exact .refl hu
  | edge he => exact .edge (symmetric he)
  | trans _ _ h₁ h₂ => exact .trans h₂ h₁

private theorem to_middle {m : Nat} (i : Nat) (d : Fin 3) (hi : i < m) :
    Joins m .leftEnd (.middle i d) := by
  induction i generalizing d with
  | zero =>
    have he : Edge m .leftEnd (.leftInner false) := by simp [Edge,valid,level]
    have he' : Edge m (.leftInner false) (.middle 0 d) := by simp [Edge,valid,level,hi]
    exact .trans (.edge he) (.edge he')
  | succ i ih =>
    have hprev : i < m := by omega
    have he : Edge m (.middle i 0) (.middle (i+1) d) := by
      simp [Edge,valid,level,hprev,hi,Nat.add_assoc]
    exact .trans (ih 0 hprev) (.edge he)

private theorem to_right {m : Nat} (hm : 0 < m) (b : Bool) : Joins m .leftEnd (.rightInner b) := by
  have hi : m-1 < m := by omega
  have he : Edge m (.middle (m-1) 0) (.rightInner b) := by
    simp only [Edge,valid,level]
    exact ⟨hi,trivial,Or.inl (by omega)⟩
  exact .trans (to_middle _ 0 hi) (.edge he)

private theorem from_left {m : Nat} (hm : 0 < m) (v : Vertex) (hv : valid m v) :
    Joins m .leftEnd v := by
  cases v with
  | leftEnd => exact .refl trivial
  | leftInner b => exact .edge (by simp [Edge,valid,level])
  | middle i d => exact to_middle i d hv
  | rightInner b => exact to_right hm b
  | rightEnd => exact .trans (to_right hm false) (.edge (by simp [Edge,valid,level,Nat.add_assoc]))

theorem connected {m : Nat} (hm : 0 < m) {u v : Vertex} (hu : valid m u) (hv : valid m v) :
    Joins m u v := .trans (joins_symm (from_left hm u hu)) (from_left hm v hv)

def lastFrom : Vertex → List Vertex → Vertex
  | u, [] => u
  | _, v :: rest => lastFrom v rest

def Walk (m : Nat) : Vertex → List Vertex → Prop
  | u, [] => valid m u
  | u, v :: rest => Edge m u v ∧ Walk m v rest

/-- Fix the orientation by ordering the endpoint layers. A positive-length
sequence admitted here and its reversal cannot both have this orientation. -/
def CanonicalGeodesic (m : Nat) : List Vertex → Prop
  | [] => False
  | u :: rest => Walk m u rest ∧
    (rest = [] ∨ level m u < level m (lastFrom u rest)) ∧
    ∀ other, Walk m u other → lastFrom u other = lastFrom u rest → rest.length ≤ other.length

private theorem walk_bound (m : Nat) (u : Vertex) (rest : List Vertex) (hw : Walk m u rest) :
    level m (lastFrom u rest) ≤ level m u + rest.length := by
  induction rest generalizing u with
  | nil => simp [lastFrom]
  | cons v rest ih =>
    have ht := ih v hw.2
    have step := hw.1.2.2
    change level m (lastFrom v rest) ≤ level m u + (v :: rest).length
    simp only [List.length_cons]
    omega

private def Rows (m : Nat) : Nat → List Vertex → Prop
  | _, [] => True
  | i, u :: rest => valid m u ∧ level m u = i ∧ Rows m (i+1) rest

private theorem rows_path (m k : Nat) (u : Vertex) (rest : List Vertex)
    (h : Rows m k (u :: rest)) :
    Walk m u rest ∧ level m (lastFrom u rest) = k + rest.length := by
  induction rest generalizing k u with
  | nil => exact ⟨h.1, h.2.1⟩
  | cons v rest ih =>
    obtain ⟨hp, hv⟩ := ih (k+1) v h.2.2
    have hu := h.2.1
    have hl := h.2.2.2.1
    refine ⟨⟨⟨h.1, h.2.2.1, Or.inl (by omega)⟩, hp⟩, ?_⟩
    change level m (lastFrom v rest) = k + (v :: rest).length
    simp only [List.length_cons]
    omega

private theorem rows_geodesic (m k : Nat) (xs : List Vertex)
    (h : Rows m k xs) (hne : xs ≠ []) : CanonicalGeodesic m xs := by
  cases xs with
  | nil => exact False.elim (hne rfl)
  | cons u rest =>
    obtain ⟨hp, hend⟩ := rows_path m k u rest h
    have hstart := h.2.1
    refine ⟨hp, ?_, ?_⟩
    · cases rest with
      | nil => exact Or.inl rfl
      | cons v vs =>
        right
        simp only [List.length_cons] at hend
        omega
    · intro other hw he
      have hi := walk_bound m u other hw
      rw [he] at hi
      omega

private theorem append_rows (m i : Nat) (a b : List Vertex) (ha : Rows m i a)
    (hb : Rows m (i + a.length) b) : Rows m i (a ++ b) := by
  induction a generalizing i with
  | nil => simpa using hb
  | cons u a ih =>
    refine ⟨ha.1, ha.2.1, ih (i+1) ha.2.2 ?_⟩
    have hidx : i+1+a.length = i+(u::a).length := by simp only [List.length_cons]; omega
    rw [hidx]
    exact hb

private def leftPart (c : Fin 5) : List Vertex := match c.val with
  | 0 => [] | 1 => [.leftInner false] | 2 => [.leftInner true]
  | 3 => [.leftEnd, .leftInner false] | _ => [.leftEnd, .leftInner true]

private def rightPart (c : Fin 5) : List Vertex := match c.val with
  | 0 => [] | 1 => [.rightInner false] | 2 => [.rightInner true]
  | 3 => [.rightInner false, .rightEnd] | _ => [.rightInner true, .rightEnd]

private theorem left_rows (m : Nat) (c : Fin 5) : Rows m (2-(leftPart c).length) (leftPart c) := by
  have h := c.isLt
  have e : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ c.val = 3 ∨ c.val = 4 := by omega
  rcases e with h|h|h|h|h <;> simp [leftPart,h,Rows,valid,level]

private theorem right_rows (m : Nat) (c : Fin 5) : Rows m (m+2) (rightPart c) := by
  have h := c.isLt
  have e : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ c.val = 3 ∨ c.val = 4 := by omega
  rcases e with h|h|h|h|h <;> simp [rightPart,h,Rows,valid,level,Nat.add_assoc]

private def body : Nat → List (Fin 3) → List Vertex
  | _, [] => []
  | i, d :: ds => .middle i d :: body (i+1) ds

private theorem body_length (i : Nat) (ds : List (Fin 3)) : (body i ds).length = ds.length := by
  induction ds generalizing i with
  | nil => rfl
  | cons d ds ih => simp only [body, List.length_cons, ih (i+1)]

private theorem body_rows (m i : Nat) (ds : List (Fin 3)) (hi : i+ds.length ≤ m) :
    Rows m (i+2) (body i ds) := by
  induction ds generalizing i with
  | nil => trivial
  | cons d ds ih =>
    simp only [List.length_cons] at hi
    exact ⟨by change i < m; omega, rfl, ih (i+1) (by omega)⟩

private def sequence (l : Fin 5) (w : List (Fin 3)) (r : Fin 5) : List Vertex :=
  leftPart l ++ (body 0 w ++ rightPart r)

private theorem valid_sequence {m : Nat} (hm : 0 < m) (l r : Fin 5) (w : List (Fin 3))
    (hw : w.length = m) : CanonicalGeodesic m (sequence l w r) := by
  have hc : Rows m 2 (body 0 w) := body_rows m 0 w (by omega)
  have hc2 : Rows m (2+(body 0 w).length) (rightPart r) := by
    rw [body_length, hw, Nat.add_comm 2 m]
    exact right_rows m r
  have hcr := append_rows m 2 _ _ hc hc2
  have size_bound : ∀ a : Fin 5, (leftPart a).length ≤ 2 := by decide
  have hs : 2-(leftPart l).length+(leftPart l).length = 2 := by have := size_bound l; omega
  apply rows_geodesic m (2-(leftPart l).length)
  · exact append_rows m _ _ _ (left_rows m l) (by rw [hs]; exact hcr)
  · intro he
    have hl := congrArg List.length he
    simp only [sequence, List.length_append, body_length, List.length_nil, hw] at hl
    omega

private def keepLeft : Vertex → Option Vertex
  | .leftEnd => some .leftEnd | .leftInner b => some (.leftInner b) | _ => none

private def keepRight : Vertex → Option Vertex
  | .rightEnd => some .rightEnd | .rightInner b => some (.rightInner b) | _ => none

private def keepDigit : Vertex → Option (Fin 3)
  | .middle _ d => some d | _ => none

private theorem read_body (i : Nat) (w : List (Fin 3)) :
    (body i w).filterMap keepLeft = [] ∧ (body i w).filterMap keepRight = [] ∧
    (body i w).filterMap keepDigit = w := by
  induction w generalizing i with
  | nil => simp [body]
  | cons d w ih =>
    obtain ⟨hl,hr,hw⟩ := ih (i+1)
    simp [body,keepLeft,keepRight,keepDigit,hl,hr,hw]

private theorem read_sequence (l r : Fin 5) (w : List (Fin 3)) :
    (sequence l w r).filterMap keepLeft = leftPart l ∧
    (sequence l w r).filterMap keepRight = rightPart r ∧
    (sequence l w r).filterMap keepDigit = w := by
  have caps : ∀ c : Fin 5,
      (leftPart c).filterMap keepLeft = leftPart c ∧ (leftPart c).filterMap keepRight = [] ∧
      (leftPart c).filterMap keepDigit = [] ∧ (rightPart c).filterMap keepLeft = [] ∧
      (rightPart c).filterMap keepRight = rightPart c ∧ (rightPart c).filterMap keepDigit = [] := by decide
  obtain ⟨ll,lr,ld,_,_,_⟩ := caps l
  obtain ⟨_,_,_,rl,rr,rd⟩ := caps r
  obtain ⟨bl,br,bd⟩ := read_body 0 w
  simp [sequence,List.filterMap_append,ll,lr,ld,rl,rr,rd,bl,br,bd]

private theorem sequence_inj {l r l' r' : Fin 5} {w w' : List (Fin 3)}
    (h : sequence l w r = sequence l' w' r') : l = l' ∧ r = r' ∧ w = w' := by
  have cap_inj : ∀ a b : Fin 5, (leftPart a = leftPart b → a=b) ∧
      (rightPart a = rightPart b → a=b) := by decide
  obtain ⟨ll,rr,dd⟩ := read_sequence l r w
  obtain ⟨ll',rr',dd'⟩ := read_sequence l' r' w'
  rw [h] at ll rr dd
  exact ⟨(cap_inj _ _).1 (ll.symm.trans ll'), (cap_inj _ _).2 (rr.symm.trans rr'), dd.symm.trans dd'⟩

/-- Fixed-length base-three representation, with the least significant digit first. -/
private def digits : Nat → Nat → List (Fin 3)
  | 0, _ => []
  | m+1, z => ⟨z%3, Nat.mod_lt _ (by decide)⟩ :: digits m (z/3)

private def value : List (Fin 3) → Nat
  | [] => 0
  | d :: ds => d.val + 3 * value ds

private theorem digits_length (m z : Nat) : (digits m z).length = m := by
  induction m generalizing z with
  | zero => rfl
  | succ m ih => simp only [digits, List.length_cons, ih (z/3)]

private theorem value_digits (m z : Nat) (hz : z < 3^m) : value (digits m z) = z := by
  induction m generalizing z with
  | zero => simp only [Nat.pow_zero] at hz; change 0 = z; omega
  | succ m ih =>
    rw [Nat.pow_succ] at hz
    change z%3 + 3 * value (digits m (z/3)) = z
    rw [ih (z/3) (by omega)]
    omega

private def cap (z : Nat) : Fin 5 := ⟨z%5, Nat.mod_lt _ (by decide)⟩

def encoded (m z : Nat) : List Vertex :=
  sequence (cap z) (digits m (z/5/5)) (cap (z/5))

theorem encoded_geodesic (m z : Nat) (hm : 0 < m) : CanonicalGeodesic m (encoded m z) :=
  valid_sequence hm _ _ _ (digits_length _ _)

theorem encoded_injective (m : Nat) (a b : Fin (25 * 3^m))
    (h : encoded m a.val = encoded m b.val) : a = b := by
  obtain ⟨hl,hr,hw⟩ := sequence_inj h
  have l : a.val % 5 = b.val % 5 := congrArg Fin.val hl
  have r : (a.val/5)%5 = (b.val/5)%5 := congrArg Fin.val hr
  have ha := a.isLt
  have hb := b.isLt
  have eqv := congrArg value hw
  rw [value_digits m (a.val/5/5) (by omega), value_digits m (b.val/5/5) (by omega)] at eqv
  apply Fin.ext
  omega

/-- A lower bound on the number of distinct unoriented geodesics: use
the unique increasing-layer orientation, also admitting singleton paths. -/
def AtLeast (m k : Nat) : Prop := ∃ f : Fin k → List Vertex,
  (∀ a b, f a = f b → a = b) ∧ ∀ a, CanonicalGeodesic m (f a)

theorem geodesics_lower (m : Nat) (hm : 0 < m) : AtLeast m (25 * 3^m) :=
  ⟨fun i => encoded m i.val, encoded_injective m, fun i => encoded_geodesic m i.val hm⟩

/-- The order is 3m+6. Four times the certified lower bound exceeds
nine times 3^(m+2), which avoids division in the benchmark comparison. -/
theorem beats_asymptotic_benchmark (m : Nat) (hm : 0 < m) :
    AtLeast m (25 * 3^m) ∧ 9 * 3^(m+2) < 4 * (25 * 3^m) := by
  refine ⟨geodesics_lower m hm, ?_⟩
  have hp : 0 < 3^m := Nat.pow_pos (by decide)
  rw [Nat.pow_succ, Nat.pow_succ]
  omega

theorem problem14_family (m : Nat) (hm : 0 < m) :
    (allVertices m).length = 3*m+6 ∧ (allVertices m).Nodup ∧
    (∀ v, v ∈ allVertices m ↔ valid m v) ∧
    (∀ u, ¬ Edge m u u) ∧ (∀ u v, Edge m u v → Edge m v u) ∧
    (∀ u v, valid m u → valid m v → Joins m u v) ∧
    AtLeast m (25 * 3^m) ∧ 9 * 3^(m+2) < 4 * (25 * 3^m) :=
  ⟨vertex_order m, vertex_nodup m, vertex_mem m, loopless m,
    fun _ _ he => symmetric he, fun _ _ hu hv => connected hm hu hv,
    beats_asymptotic_benchmark m hm⟩

#print axioms problem14_family
end LayerFamily
