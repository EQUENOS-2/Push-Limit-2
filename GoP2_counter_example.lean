/-!
# GoP2 : an over-approximation of push-limit-one pistons and observers

Lean 4 (core only, no Mathlib) formalisation of GoP2 (Tim, draft of 10 October 2026):

  §0  vectors of Z³
  §1  the game : directions, cells, structures, activity (Def. 1), moves (Def. 2), engines (Def. 3)
  §2  simple lemmas
  §3  the decider : executable sparse structures, exact move sequences (E1/E2/R1/R2),
      `checkCert` (Bool) and its soundness theorem `checkCert_sound : checkCert .. = true → IsEngine ..`
  §4  the counter-example ("sheet engine", 30 blocks, 1388 moves) and its proof
  §5  the goal theorem of the paper (`NoEngine`) and its refutation
-/

namespace GoP2

/-! ## 0. Vectors of Z³ -/

@[ext] structure V3 where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr

namespace V3
instance : Add V3 := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩⟩
instance : Sub V3 := ⟨fun a b => ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩⟩
instance : Neg V3 := ⟨fun a => ⟨-a.x, -a.y, -a.z⟩⟩
instance : OfNat V3 0 := ⟨⟨0, 0, 0⟩⟩

@[simp] theorem add_x (a b : V3) : (a + b).x = a.x + b.x := rfl
@[simp] theorem add_y (a b : V3) : (a + b).y = a.y + b.y := rfl
@[simp] theorem add_z (a b : V3) : (a + b).z = a.z + b.z := rfl
@[simp] theorem sub_x (a b : V3) : (a - b).x = a.x - b.x := rfl
@[simp] theorem sub_y (a b : V3) : (a - b).y = a.y - b.y := rfl
@[simp] theorem sub_z (a b : V3) : (a - b).z = a.z - b.z := rfl
@[simp] theorem neg_x (a : V3) : (-a).x = -a.x := rfl
@[simp] theorem neg_y (a : V3) : (-a).y = -a.y := rfl
@[simp] theorem neg_z (a : V3) : (-a).z = -a.z := rfl
@[simp] theorem zero_x : (0 : V3).x = 0 := rfl
@[simp] theorem zero_y : (0 : V3).y = 0 := rfl
@[simp] theorem zero_z : (0 : V3).z = 0 := rfl

theorem sub_zero (a : V3) : a - 0 = a := by ext <;> simp
theorem add_sub_cancel (a b : V3) : a + b - b = a := by ext <;> simp
theorem sub_add_cancel (a b : V3) : a - b + b = a := by ext <;> simp
theorem sub_sub (a b c : V3) : a - b - c = a - (b + c) := by ext <;> simp <;> omega
theorem add_comm (a b : V3) : a + b = b + a := by ext <;> simp <;> omega
theorem eq_sub_iff_add_eq {a b c : V3} : a = b - c ↔ a + c = b := by
  constructor
  · rintro rfl; exact sub_add_cancel _ _
  · rintro rfl; exact (add_sub_cancel _ _).symm
end V3

/-! ## 1. The game -/

/-- `D = {±ex, ±ey, ±ez}`. -/
inductive Dir
  | xp | xn | yp | yn | zp | zn
  deriving DecidableEq, Repr

namespace Dir
def all : List Dir := [xp, xn, yp, yn, zp, zn]
theorem mem_all (d : Dir) : d ∈ all := by cases d <;> simp [all]

def vec : Dir → V3
  | xp => ⟨1, 0, 0⟩ | xn => ⟨-1, 0, 0⟩
  | yp => ⟨0, 1, 0⟩ | yn => ⟨0, -1, 0⟩
  | zp => ⟨0, 0, 1⟩ | zn => ⟨0, 0, -1⟩

theorem vec_ne_zero (d : Dir) : d.vec ≠ 0 := by
  intro h
  have h1 := congrArg V3.x h
  have h2 := congrArg V3.y h
  have h3 := congrArg V3.z h
  cases d <;> simp [vec] at h1 h2 h3
end Dir

/-- `Σ = {P⁰_d, P¹_d} ∪ {O_f} ∪ {∅, H}`.  `piston ε d` is `P^ε_d` (extended iff `ε = true`);
`obs f` is `O_f` (watches `q + f`, outputs into `q - f`); `solid` is `H`. -/
inductive Cell
  | piston (ext : Bool) (d : Dir)
  | obs (f : Dir)
  | empty
  | solid
  deriving DecidableEq, Repr

/-- `Mov = {H} ∪ {O_f} ∪ {P⁰_d}` : extended pistons are not movable. -/
def Cell.mov : Cell → Bool
  | .solid => true
  | .obs _ => true
  | .piston false _ => true
  | _ => false

def Mov (c : Cell) : Prop := c.mov = true

theorem Mov_iff (c : Cell) :
    Mov c ↔ c = .solid ∨ (∃ f, c = .obs f) ∨ (∃ d, c = .piston false d) := by
  cases c with
  | piston e d => cases e <;> simp [Mov, Cell.mov]
  | obs f => simp [Mov, Cell.mov]
  | empty => simp [Mov, Cell.mov]
  | solid => simp [Mov, Cell.mov]

theorem not_Mov_extended (d : Dir) : ¬ Mov (.piston true d) := by simp [Mov, Cell.mov]
theorem not_Mov_empty : ¬ Mov .empty := by simp [Mov, Cell.mov]

/-- A structure `S : Z³ → Σ`; finite support is the separate predicate `FiniteSupport`. -/
abbrev Struct := V3 → Cell

def FiniteSupport (S : Struct) : Prop := ∃ l : List V3, ∀ p, S p ≠ Cell.empty → p ∈ l
def Struct.NonEmpty (S : Struct) : Prop := ∃ p, S p ≠ Cell.empty

/-- `S[p ↦ a]`. -/
def upd (S : Struct) (p : V3) (a : Cell) : Struct := fun q => if q = p then a else S q

/-- `S + v` : `S` translated by `v` (the cell at `q` goes to `q + v`). -/
def shift (S : Struct) (v : V3) : Struct := fun q => S (q - v)

/-- `e_y`. -/
def eY : V3 := Dir.yp.vec

/-- `A = D ∪ (D + e_y) \ {0}` (`0 ∉ D`, so both readings of the precedence agree). -/
def InA (a : V3) : Prop := a ≠ 0 ∧ ∃ f : Dir, a = f.vec ∨ a = f.vec + eY

/-- Definition 1 (Activity), literally.  Piston at `p` facing `d`. -/
def Active (S : Struct) (p : V3) (d : Dir) : Prop :=
  (∃ f : Dir, f ≠ d ∧ S (p + f.vec) = Cell.obs f) ∨
  (∃ f : Dir, f ≠ Dir.yn ∧ S (p + eY + f.vec) = Cell.obs f) ∨
  (∃ a : V3, InA a ∧ a ≠ d.vec ∧ S (p + a) = Cell.solid ∧
      ∃ f : Dir, S (p + a + f.vec) = Cell.obs f)

/-- Definition 2 (Moves).  `Step S S'` is `S ⇝ S'`. -/
inductive Step : Struct → Struct → Prop
  /-- (E1) extend into air. -/
  | e1 {S : Struct} {p : V3} {d : Dir} :
      S p = Cell.piston false d → Active S p d → S (p + d.vec) = Cell.empty →
      Step S (upd S p (Cell.piston true d))
  /-- (E2) extend and push a movable block into air (push limit 1). -/
  | e2 {S : Struct} {p : V3} {d : Dir} {b : Cell} :
      S p = Cell.piston false d → Active S p d →
      S (p + d.vec) = b → Mov b → S (p + d.vec + d.vec) = Cell.empty →
      Step S (upd (upd (upd S p (Cell.piston true d)) (p + d.vec) Cell.empty)
                  (p + d.vec + d.vec) b)
  /-- (R1) retract (needs no activity). -/
  | r1 {S : Struct} {p : V3} {d : Dir} :
      S p = Cell.piston true d →
      Step S (upd S p (Cell.piston false d))
  /-- (R2) retract and pull the movable block two cells ahead (front cell empty). -/
  | r2 {S : Struct} {p : V3} {d : Dir} {b : Cell} :
      S p = Cell.piston true d → S (p + d.vec) = Cell.empty →
      S (p + d.vec + d.vec) = b → Mov b →
      Step S (upd (upd (upd S p (Cell.piston false d)) (p + d.vec) b)
                  (p + d.vec + d.vec) Cell.empty)

/-- Exactly `n` successive moves. -/
def Path : Nat → Struct → Struct → Prop
  | 0, S, T => S = T
  | n + 1, S, T => ∃ U, Step S U ∧ Path n U T

/-- Definition 3 : a nonempty structure (of finite support) is a GoP2 engine if
`S ⇝ S₁ ⇝ ⋯ ⇝ Sₙ = S + v` for some `n ≥ 1`, `v ≠ 0`. -/
def IsEngine (S : Struct) : Prop :=
  FiniteSupport S ∧ S.NonEmpty ∧ ∃ n : Nat, 1 ≤ n ∧ ∃ v : V3, v ≠ 0 ∧ Path n S (shift S v)

/-- The statement the paper hopes for ("GoP2 has no engine"). -/
def NoEngine : Prop := ∀ S : Struct, ¬ IsEngine S

/-! ## 2. Simple lemmas -/

theorem upd_same (S : Struct) (p : V3) (a : Cell) : upd S p a p = a := by simp [upd]
theorem upd_ne (S : Struct) {p q : V3} (a : Cell) (h : q ≠ p) : upd S p a q = S q := by
  simp [upd, h]

theorem shift_zero (S : Struct) : shift S 0 = S := by
  funext q; simp [shift, V3.sub_zero]

theorem shift_shift (S : Struct) (v w : V3) : shift (shift S v) w = shift S (v + w) := by
  funext q; simp [shift, V3.sub_sub, V3.add_comm]

theorem Path_trans {m n : Nat} {S T U : Struct} (h1 : Path m S T) (h2 : Path n T U) :
    Path (m + n) S U := by
  induction m generalizing S with
  | zero => cases h1; simpa [Nat.zero_add] using h2
  | succ m ih =>
    obtain ⟨V, hs, hp⟩ := h1
    have : m + 1 + n = (m + n) + 1 := by omega
    rw [this]
    exact ⟨V, hs, ih hp⟩

theorem finiteSupport_upd {S : Struct} (h : FiniteSupport S) (p : V3) (a : Cell) :
    FiniteSupport (upd S p a) := by
  obtain ⟨l, hl⟩ := h
  refine ⟨p :: l, fun q hq => ?_⟩
  by_cases hqp : q = p
  · simp [hqp]
  · exact List.mem_cons_of_mem _ (hl q (by simpa [upd, hqp] using hq))

/-- Moves preserve finite support. -/
theorem Step.finiteSupport {S T : Struct} (h : Step S T) (hS : FiniteSupport S) :
    FiniteSupport T := by
  cases h <;> repeat (first | exact hS | apply finiteSupport_upd)

/-- Retraction never needs activity : every extended piston can retract. -/
theorem retract_always {S : Struct} {p : V3} {d : Dir} (h : S p = Cell.piston true d) :
    ∃ T, Step S T := ⟨_, Step.r1 h⟩

/-- Extended pistons are never pushed or pulled (they are not `Mov`). -/
theorem extended_not_pushed (d : Dir) : ¬ Mov (Cell.piston true d) := not_Mov_extended d

/-! ## 3. The decider -/

/-- Boolean version of `InA`'s witnesses : the 12 offsets of `A`. -/
def Alist : List V3 :=
  (Dir.all.map Dir.vec ++ Dir.all.map (fun f => f.vec + eY)).filter (fun a => decide (a ≠ 0))

theorem mem_Alist (a : V3) : a ∈ Alist ↔ InA a := by
  simp only [Alist, InA, List.mem_filter, List.mem_append, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨(⟨f, _, rfl⟩ | ⟨f, _, rfl⟩), hne⟩
    · exact ⟨hne, f, Or.inl rfl⟩
    · exact ⟨hne, f, Or.inr rfl⟩
  · rintro ⟨hne, f, rfl | rfl⟩
    · exact ⟨Or.inl ⟨f, Dir.mem_all f, rfl⟩, hne⟩
    · exact ⟨Or.inr ⟨f, Dir.mem_all f, rfl⟩, hne⟩

/-- Boolean activity test. -/
def activeB (S : Struct) (p : V3) (d : Dir) : Bool :=
  Dir.all.any (fun f => decide (f ≠ d) && decide (S (p + f.vec) = Cell.obs f)) ||
  Dir.all.any (fun f => decide (f ≠ Dir.yn) && decide (S (p + eY + f.vec) = Cell.obs f)) ||
  Alist.any (fun a => decide (a ≠ d.vec) && decide (S (p + a) = Cell.solid) &&
      Dir.all.any (fun f => decide (S (p + a + f.vec) = Cell.obs f)))

theorem activeB_iff (S : Struct) (p : V3) (d : Dir) : activeB S p d = true ↔ Active S p d := by
  simp only [activeB, Active, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, mem_Alist]
  constructor
  · rintro ((⟨f, _, h1, h2⟩ | ⟨f, _, h1, h2⟩) | ⟨a, ha, ⟨h1, h2⟩, f, _, h3⟩)
    · exact Or.inl ⟨f, h1, h2⟩
    · exact Or.inr (Or.inl ⟨f, h1, h2⟩)
    · exact Or.inr (Or.inr ⟨a, ha, h1, h2, f, h3⟩)
  · rintro (⟨f, h1, h2⟩ | ⟨f, h1, h2⟩ | ⟨a, ha, h1, h2, f, h3⟩)
    · exact Or.inl (Or.inl ⟨f, Dir.mem_all f, h1, h2⟩)
    · exact Or.inl (Or.inr ⟨f, Dir.mem_all f, h1, h2⟩)
    · exact Or.inr ⟨a, ha, ⟨h1, h2⟩, f, Dir.mem_all f, h3⟩

/-- Sparse structures : association lists, the first entry for a key wins; absent = `∅`. -/
abbrev Sparse := List (V3 × Cell)

def Sparse.get : Sparse → V3 → Cell
  | [], _ => Cell.empty
  | (r, c) :: t, q => if r = q then c else Sparse.get t q

def Sparse.erase : Sparse → V3 → Sparse
  | [], _ => []
  | (r, c) :: t, p => if r = p then Sparse.erase t p else (r, c) :: Sparse.erase t p

def Sparse.set (s : Sparse) (p : V3) (c : Cell) : Sparse := (p, c) :: s.erase p

theorem get_erase {s : Sparse} {p q : V3} (h : q ≠ p) : (s.erase p).get q = s.get q := by
  induction s with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨r, c⟩ := e
    by_cases hr : r = p
    · have hrq : r ≠ q := fun h' => h (h'.symm.trans hr)
      simp only [Sparse.erase, Sparse.get, if_pos hr, if_neg hrq]
      exact ih
    · by_cases hq : r = q
      · simp only [Sparse.erase, Sparse.get, if_neg hr, if_pos hq]
      · simp only [Sparse.erase, Sparse.get, if_neg hr, if_neg hq]
        exact ih

theorem get_set (s : Sparse) (p : V3) (c : Cell) : (s.set p c).get = upd s.get p c := by
  funext q
  by_cases h : q = p
  · subst h; simp [Sparse.set, Sparse.get, upd]
  · have hp : p ≠ q := fun h' => h h'.symm
    simp only [Sparse.set, Sparse.get, upd, if_neg hp, if_neg h]
    exact get_erase h

theorem get_not_mem {s : Sparse} {q : V3} (h : q ∉ s.map Prod.fst) : s.get q = Cell.empty := by
  induction s with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨r, c⟩ := e
    simp only [List.map, List.mem_cons, not_or] at h
    simp [Sparse.get, Ne.symm h.1, ih h.2]

theorem finiteSupport_get (s : Sparse) : FiniteSupport s.get :=
  ⟨s.map Prod.fst, fun q hq =>
    Classical.byContradiction fun h => hq (get_not_mem h)⟩

/-- Exact moves, one constructor per rule of Definition 2. -/
inductive Move
  | e1 (p : V3) | e2 (p : V3) | r1 (p : V3) | r2 (p : V3)
  deriving Repr

/-- Executable single move, with the exact preconditions of the corresponding rule. -/
def applyMove (s : Sparse) : Move → Option Sparse
  | .e1 p =>
    match s.get p with
    | .piston false d =>
      if activeB s.get p d && decide (s.get (p + d.vec) = Cell.empty)
      then some (s.set p (.piston true d)) else none
    | _ => none
  | .e2 p =>
    match s.get p with
    | .piston false d =>
      if activeB s.get p d && (s.get (p + d.vec)).mov
          && decide (s.get (p + d.vec + d.vec) = Cell.empty)
      then some (((s.set p (.piston true d)).set (p + d.vec) Cell.empty).set
                  (p + d.vec + d.vec) (s.get (p + d.vec)))
      else none
    | _ => none
  | .r1 p =>
    match s.get p with
    | .piston true d => some (s.set p (.piston false d))
    | _ => none
  | .r2 p =>
    match s.get p with
    | .piston true d =>
      if decide (s.get (p + d.vec) = Cell.empty) && (s.get (p + d.vec + d.vec)).mov
      then some (((s.set p (.piston false d)).set (p + d.vec) (s.get (p + d.vec + d.vec))).set
                  (p + d.vec + d.vec) Cell.empty)
      else none
    | _ => none

theorem applyMove_sound {s t : Sparse} {m : Move} (h : applyMove s m = some t) :
    Step s.get t.get := by
  cases m with
  | e1 p =>
    simp only [applyMove] at h
    split at h
    · rename_i d hd
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        cases h
        rw [get_set]
        exact Step.e1 hd ((activeB_iff _ _ _).1 hc.1) hc.2
      · cases h
    · cases h
  | e2 p =>
    simp only [applyMove] at h
    split at h
    · rename_i d hd
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        cases h
        rw [get_set, get_set, get_set]
        exact Step.e2 hd ((activeB_iff _ _ _).1 hc.1.1) rfl hc.1.2 hc.2
      · cases h
    · cases h
  | r1 p =>
    simp only [applyMove] at h
    split at h
    · rename_i d hd
      cases h
      rw [get_set]
      exact Step.r1 hd
    · cases h
  | r2 p =>
    simp only [applyMove] at h
    split at h
    · rename_i d hd
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        cases h
        rw [get_set, get_set, get_set]
        exact Step.r2 hd hc.1 rfl hc.2
      · cases h
    · cases h

/-- Run a list of moves. -/
def run (s : Sparse) : List Move → Option Sparse
  | [] => some s
  | m :: ms =>
    match applyMove s m with
    | some t => run t ms
    | none => none

theorem run_sound {ms : List Move} {s t : Sparse} (h : run s ms = some t) :
    Path ms.length s.get t.get := by
  induction ms generalizing s with
  | nil => simp [run] at h; subst h; rfl
  | cons m ms ih =>
    simp only [run] at h
    split at h
    · rename_i u hu
      exact ⟨u.get, applyMove_sound hu, ih h⟩
    · cases h

/-- Translate a sparse structure. -/
def Sparse.shiftBy (s : Sparse) (v : V3) : Sparse := s.map fun e => (e.1 + v, e.2)

theorem get_shiftBy (s : Sparse) (v q : V3) : (s.shiftBy v).get q = s.get (q - v) := by
  induction s with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨r, c⟩ := e
    by_cases h : r + v = q
    · have h' : r = q - v := V3.eq_sub_iff_add_eq.2 h
      simp only [Sparse.shiftBy, List.map, Sparse.get, if_pos h, if_pos h']
    · have h' : r ≠ q - v := fun h'' => h (V3.eq_sub_iff_add_eq.1 h'')
      simp only [Sparse.shiftBy, List.map, Sparse.get, if_neg h, if_neg h']
      exact ih

/-- Semantic equality of two sparse structures. -/
def Sparse.same (a b : Sparse) : Bool :=
  (a.map Prod.fst ++ b.map Prod.fst).all fun q => decide (a.get q = b.get q)

theorem same_sound {a b : Sparse} (h : a.same b = true) : a.get = b.get := by
  funext q
  by_cases hq : q ∈ a.map Prod.fst ++ b.map Prod.fst
  · simp only [Sparse.same, List.all_eq_true, decide_eq_true_eq] at h
    exact h q hq
  · simp only [List.mem_append, not_or] at hq
    rw [get_not_mem hq.1, get_not_mem hq.2]

def Sparse.nonEmpty (s : Sparse) : Bool := s.any fun e => decide (s.get e.1 ≠ Cell.empty)

theorem nonEmpty_sound {s : Sparse} (h : s.nonEmpty = true) : Struct.NonEmpty s.get := by
  simp only [Sparse.nonEmpty, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨e, _, he⟩ := h
  exact ⟨e.1, he⟩

/-- **The decider.**  `checkCert s ms v = true` iff executing the exact moves `ms` from `s`
succeeds and yields `s + v` (with `v ≠ 0`, `ms ≠ []`, `s ≠ ∅`). -/
def checkCert (s : Sparse) (ms : List Move) (v : V3) : Bool :=
  decide (v ≠ 0) && !ms.isEmpty && s.nonEmpty &&
    match run s ms with
    | some t => t.same (s.shiftBy v)
    | none => false

theorem checkCert_path {s : Sparse} {ms : List Move} {v : V3}
    (h : checkCert s ms v = true) : Path ms.length s.get (shift s.get v) := by
  simp only [checkCert, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, hrun⟩ := h
  split at hrun
  · rename_i t ht
    have hp := run_sound ht
    have hs := same_sound hrun
    have : t.get = shift s.get v := by
      rw [hs]; funext q; exact get_shiftBy s v q
    rwa [this] at hp
  · cases hrun

theorem checkCert_sound {s : Sparse} {ms : List Move} {v : V3}
    (h : checkCert s ms v = true) : IsEngine s.get := by
  have hp := checkCert_path h
  simp only [checkCert, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hv, hms⟩, hne⟩, _⟩ := h
  have hlen : 1 ≤ ms.length := by
    cases ms with
    | nil => simp at hms
    | cons _ _ => simp
  exact ⟨finiteSupport_get s, nonEmpty_sound hne, ms.length, hlen, v, hv, hp⟩

/-- A certificate refutes `NoEngine`. -/
theorem checkCert_refutes {s : Sparse} {ms : List Move} {v : V3}
    (h : checkCert s ms v = true) : ¬ NoEngine :=
  fun hno => hno _ (checkCert_sound h)

/-! ## 4. The counter-example : the "sheet engine"

30 blocks (1 solid block, 18 observers `O_{+y}` forming a fixed sheet, 11 pistons), a period of
1388 moves (264 E1, 430 E2, 266 R1, 428 R2), translation `v = (1,0,0)`.
Source of the data : artifact "GoP2 Sheet Engine" (claude.ai/artifact/4N5vnEvoadpFVJUuDdv2vp).
We do not trust its JavaScript checker : the proof below is Lean's kernel running `run`.
The 1388 moves are cut into blocks of 50 with explicit intermediate states (computed by an
independent Python simulator of the same rules), so that the kernel never holds the whole
computation in memory. -/

theorem run_append_some {s t : Sparse} {a b : List Move} {r : Option Sparse}
    (h1 : run s a = some t) (h2 : run t b = r) : run s (a ++ b) = r := by
  induction a generalizing s with
  | nil => simp [run] at h1; subst h1; simpa using h2
  | cons m a ih =>
    simp only [run] at h1
    split at h1
    · rename_i u hu
      simp only [List.cons_append, run, hu]
      exact ih h1
    · cases h1

namespace Sheet

/-- A move is coded by one natural number : `k + 4·((x+8) + 32·((y+8) + 32·(z+8)))`,
with `k = 0,1,2,3` for E1, E2, R1, R2 and `(x,y,z)` the position of the piston. -/
def decode (c : Nat) : Move :=
  let k := c % 4
  let r := c / 4
  let p : V3 := ⟨Int.ofNat (r % 32) - 8, Int.ofNat ((r / 32) % 32) - 8,
                  Int.ofNat ((r / 1024) % 32) - 8⟩
  if k = 0 then Move.e1 p else if k = 1 then Move.e2 p else if k = 2 then Move.r1 p else Move.r2 p

def v : V3 := ⟨1, 0, 0⟩

/-- The initial structure (all pistons retracted). -/
def S0 : Sparse := [
  (⟨0,-1,0⟩, Cell.piston false Dir.yp),
  (⟨0,1,0⟩, Cell.obs Dir.yp),
  (⟨0,1,1⟩, Cell.obs Dir.yp),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,-1,0⟩, Cell.piston false Dir.zp),
  (⟨1,0,0⟩, Cell.piston false Dir.zp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,-1,0⟩, Cell.piston false Dir.xp),
  (⟨2,-1,1⟩, Cell.piston false Dir.xp),
  (⟨2,0,0⟩, Cell.piston false Dir.xp),
  (⟨2,0,1⟩, Cell.piston false Dir.xp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,-1,0⟩, Cell.piston false Dir.xn),
  (⟨3,-1,2⟩, Cell.piston false Dir.zn),
  (⟨3,0,0⟩, Cell.piston false Dir.xn),
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,0,0⟩, Cell.solid),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def c0 : List Move := ([
  33696, 33699, 42028, 42031, 37933, 33829, 33830, 42020, 42023, 37934, 42024, 42027,
  42021, 42029, 33836, 33839, 42031, 37929, 37930, 42022, 33833, 42025, 42033, 33840,
  42034, 42027, 33835, 42028, 33843, 42031, 42020, 42023, 42025, 33832, 33835, 33837,
  33838, 33828, 33831, 42027, 33828, 42021, 42022, 42029, 42030, 33836, 33839, 33831,
  33833, 42021] : List Nat).map decode

def c1 : List Move := ([
  42022, 42028, 42031, 42025, 42026, 33835, 33829, 33837, 33838, 42033, 33830, 42025,
  33833, 33840, 42034, 33843, 33835, 42027, 37928, 37931, 33837, 42029, 42030, 33839,
  33828, 33831, 37933, 37934, 37924, 37927, 33833, 42025, 42016, 42019, 42027, 33835,
  33829, 33830, 37925, 33837, 42028, 42031, 33839, 37927, 42025, 33833, 33834, 42027,
  37925, 33837] : List Nat).map decode

def c2 : List Move := ([
  42029, 42030, 33839, 37927, 42021, 33828, 33831, 42022, 37928, 37931, 33833, 42025,
  42016, 42019, 33834, 37921, 37922, 42027, 42020, 42023, 37925, 37926, 37921, 37929,
  37930, 37923, 42021, 33832, 33835, 42022, 37928, 37931, 37925, 37926, 37932, 37935,
  33833, 33834, 33829, 33830, 42020, 42023, 37932, 37935, 33837, 42025, 42026, 42032,
  42035, 33839] : List Nat).map decode

def c3 : List Move := ([
  37933, 37934, 37929, 37937, 37938, 37931, 33837, 42033, 42034, 42024, 42027, 33839,
  37933, 42021, 33828, 33831, 37934, 33832, 33835, 33829, 33830, 42023, 33837, 42028,
  42031, 33839, 37929, 37930, 42025, 33833, 33841, 33842, 33835, 42027, 42032, 42035,
  42028, 42031, 37929, 37930, 37925, 42029, 33836, 33839, 42031, 37927, 37928, 37931,
  42029, 42030] : List Nat).map decode

def c4 : List Move := ([
  33836, 33839, 37929, 37930, 37925, 33837, 42029, 42030, 33839, 37927, 37928, 37931,
  33837, 33838, 37925, 42036, 42039, 42032, 42035, 37933, 41900, 41903, 37805, 33701,
  33702, 41892, 41895, 37806, 41896, 41899, 41893, 41901, 33708, 33711, 41903, 37801,
  37802, 41894, 33705, 41897, 41905, 33712, 41906, 41899, 33707, 41900, 33715, 41903,
  41892, 41895] : List Nat).map decode

def c5 : List Move := ([
  41897, 33704, 33707, 33709, 33710, 33700, 33703, 41899, 33700, 41893, 41894, 41901,
  41902, 33708, 33711, 33703, 33705, 41893, 41894, 41900, 41903, 41897, 41898, 33707,
  33701, 33709, 33710, 41905, 33702, 41897, 33705, 33712, 41906, 33715, 33707, 41899,
  37800, 37803, 33709, 41901, 41902, 33711, 33700, 33703, 37805, 37806, 37796, 37799,
  33705, 41897] : List Nat).map decode

def c6 : List Move := ([
  41888, 41891, 41899, 33707, 33701, 33702, 37797, 33709, 41900, 41903, 33711, 37799,
  41897, 33705, 33706, 41899, 37797, 33709, 41901, 41902, 33711, 37799, 41893, 33700,
  33703, 41894, 37800, 37803, 33705, 41897, 41888, 41891, 33706, 37793, 37794, 41899,
  41892, 41895, 37797, 37798, 37793, 37801, 37802, 37795, 41893, 33704, 33707, 41894,
  37800, 37803] : List Nat).map decode

def c7 : List Move := ([
  37797, 37798, 37804, 37807, 33705, 33706, 33701, 33702, 41892, 41895, 37804, 37807,
  33709, 41897, 41898, 41904, 41907, 33711, 37805, 37806, 37801, 37809, 37817, 37818,
  37811, 37803, 37804, 37807, 33709, 41905, 41906, 41896, 41899, 33711, 37805, 41893,
  33700, 33703, 37806, 33704, 33707, 41894, 37805, 37806, 37796, 37799, 37801, 37802,
  41892, 41895] : List Nat).map decode

def c8 : List Move := ([
  33705, 33706, 37793, 37800, 37803, 37795, 37796, 37799, 41893, 41894, 37792, 37795,
  41897, 41889, 41890, 41899, 33704, 33707, 33701, 33702, 37801, 37802, 41892, 41895,
  37797, 33709, 41900, 41903, 33711, 37799, 41897, 33704, 33707, 37934, 37927, 42037,
  33836, 33839, 37929, 37930, 37925, 33837, 42038, 42028, 42031, 33839, 37927, 37928,
  37931, 33837] : List Nat).map decode

def c9 : List Move := ([
  33838, 42033, 42025, 33833, 33840, 42034, 33843, 33835, 42027, 37928, 37931, 33837,
  42029, 42021, 33828, 42022, 42031, 33839, 37929, 37930, 33830, 42025, 33833, 33841,
  33842, 33835, 42027, 33836, 42032, 42035, 33839, 33828, 33831, 33833, 42024, 42027,
  42029, 42030, 42020, 42023, 33835, 33829, 33830, 42020, 33837, 33838, 42028, 42031,
  42023, 42025] : List Nat).map decode

def c10 : List Move := ([
  33829, 33830, 33836, 33839, 33833, 33834, 42027, 42021, 42029, 42030, 33841, 42022,
  33833, 42025, 33842, 42032, 42035, 42027, 33835, 37928, 37931, 42029, 33837, 33828,
  33838, 42031, 42020, 42023, 42025, 42026, 42021, 42022, 33831, 37932, 37935, 42029,
  33833, 33834, 33840, 33843, 42031, 37929, 37937, 37938, 37931, 42029, 42030, 33841,
  33842, 33832] : List Nat).map decode

def c11 : List Move := ([
  33835, 37792, 37795, 42028, 42031, 37933, 33829, 33830, 42020, 42023, 37934, 42024,
  42027, 42021, 42029, 33836, 33839, 42031, 37929, 37930, 42022, 33833, 42025, 42033,
  33840, 42034, 42027, 33835, 42028, 33843, 42031, 42020, 42023, 42025, 33832, 33835,
  33837, 33838, 33828, 33831, 42027, 37928, 37931, 42025, 33829, 33830, 33836, 33839,
  33833, 33834] : List Nat).map decode

def c12 : List Move := ([
  42027, 42021, 42022, 42029, 42030, 33841, 33833, 42025, 33842, 42032, 42035, 42027,
  33835, 37928, 37931, 33833, 33834, 37932, 37935, 42029, 33837, 33828, 33831, 42030,
  37925, 37926, 33839, 33832, 33835, 37929, 37930, 33833, 42028, 42031, 42025, 33834,
  37932, 37935, 42033, 42034, 37929, 37930, 37936, 37939, 37933, 37934, 42027, 42029,
  33837, 33838] : List Nat).map decode

def c13 : List Move := ([
  42031, 42025, 37940, 37943, 42033, 33841, 41899, 33700, 37797, 37798, 37804, 37807,
  37801, 37802, 33702, 41897, 33705, 33713, 33714, 33707, 41899, 33708, 41904, 41907,
  33711, 33700, 33703, 33705, 41896, 41899, 41901, 41902, 41892, 41895, 33707, 33701,
  33702, 41892, 37800, 37803, 33709, 33710, 41900, 41903, 41895, 41897, 33701, 33702,
  33708, 33711] : List Nat).map decode

def c14 : List Move := ([
  33705, 33706, 41899, 41893, 41894, 41901, 41902, 33713, 33705, 41897, 33714, 41904,
  41907, 41899, 33707, 37800, 37803, 33705, 33706, 37804, 37807, 41901, 33709, 33700,
  33703, 41902, 37797, 37798, 33711, 33704, 33707, 37801, 37802, 33705, 41900, 41903,
  41897, 33706, 37804, 37807, 41905, 41906, 37801, 37802, 37808, 37811, 37805, 37806,
  41899, 41901] : List Nat).map decode

def c15 : List Move := ([
  33709, 33710, 41903, 41897, 37812, 37815, 41905, 33713, 33721, 33722, 33715, 41907,
  41899, 37813, 37814, 37804, 37807, 41901, 33708, 33711, 41903, 41897, 37809, 37810,
  37800, 37803, 37805, 37806, 37796, 41904, 41907, 41899, 37798, 33704, 33707, 41901,
  41902, 37800, 37803, 33705, 33706, 37796, 37799, 33709, 33701, 33702, 33711, 41900,
  41903, 41897] : List Nat).map decode

def c16 : List Move := ([
  41898, 37805, 37806, 33704, 33707, 37801, 41905, 33712, 33715, 41907, 37803, 33709,
  41900, 41903, 33711, 37801, 41896, 41905, 33713, 33714, 41907, 37803, 41899, 41901,
  33709, 33701, 33702, 33711, 41903, 37801, 37802, 37808, 37811, 33704, 33707, 41901,
  41902, 37800, 37803, 37805, 37806, 37796, 37799, 33705, 41897, 33842, 42035, 42027,
  37941, 37942] : List Nat).map decode

def c17 : List Move := ([
  37932, 37935, 37937, 37938, 37928, 37931, 37933, 37934, 33832, 33835, 42029, 33837,
  33829, 42020, 33838, 42031, 42023, 42025, 42026, 42021, 42022, 33831, 37932, 37935,
  42029, 42030, 41888, 41891, 42028, 42031, 37933, 33829, 42020, 42023, 37934, 42024,
  42027, 42021, 42022, 33831, 42029, 33836, 33839, 33833, 42031, 33834, 37932, 37935,
  37929, 37930] : List Nat).map decode

def c18 : List Move := ([
  37936, 37939, 33832, 33835, 42029, 42030, 37928, 37931, 37933, 37934, 37924, 37927,
  33833, 42024, 42027, 33835, 37925, 37926, 37932, 37935, 37929, 37930, 33833, 33834,
  42028, 42031, 37937, 37938, 37928, 37931, 42029, 33837, 33828, 33831, 33839, 42031,
  37929, 37930, 42025, 37936, 37939, 42033, 33840, 33843, 42035, 37933, 37934, 42026,
  33837, 42029] : List Nat).map decode

def c19 : List Move := ([
  42037, 33844, 42038, 42031, 33839, 42032, 33847, 42035, 42024, 42027, 42029, 33836,
  33839, 33841, 33842, 33832, 33835, 42031, 33832, 42025, 42026, 37932, 37935, 42033,
  42034, 33840, 33843, 33835, 33837, 42025, 42026, 42032, 42035, 42029, 42030, 33839,
  33833, 33834, 33841, 33842, 42037, 42029, 33837, 33844, 42038, 33847, 33839, 42031,
  37932, 37935] : List Nat).map decode

def c20 : List Move := ([
  42029, 42030, 37936, 37939, 33841, 42033, 42024, 42027, 33842, 37929, 37930, 42035,
  42028, 42031, 37933, 37934, 42029, 33840, 33843, 33837, 33845, 33846, 33839, 42031,
  37933, 37934, 37929, 33841, 42033, 41899, 33707, 37797, 37798, 37804, 37807, 37801,
  37802, 33705, 33706, 41900, 41903, 37809, 37810, 37800, 37803, 41901, 33709, 33700,
  33703, 33711] : List Nat).map decode

def c21 : List Move := ([
  41903, 37801, 37802, 41897, 37808, 37811, 41905, 33712, 33715, 41907, 37805, 37806,
  41898, 33709, 41901, 41909, 33716, 41910, 41903, 33711, 41904, 33719, 41907, 41896,
  41899, 41901, 33708, 33711, 33713, 33714, 33704, 33707, 41903, 33704, 41897, 41898,
  37804, 37807, 41905, 41906, 33712, 33715, 33707, 33709, 41897, 41898, 41904, 41907,
  41901, 41902] : List Nat).map decode

def c22 : List Move := ([
  33711, 33705, 33706, 33713, 33714, 41909, 41901, 33709, 33716, 41910, 33719, 33711,
  41903, 37804, 37807, 41901, 41902, 37808, 37811, 33713, 41905, 41896, 41899, 33714,
  37801, 37802, 41907, 41900, 41903, 37805, 37806, 41901, 33712, 33715, 33709, 33717,
  33718, 33711, 41903, 37805, 37806, 37801, 33713, 41905, 41913, 41914, 41907, 33715,
  37803, 37804] : List Nat).map decode

def c23 : List Move := ([
  37807, 33713, 41905, 41897, 33704, 41906, 33715, 33707, 33709, 41900, 41903, 33711,
  33705, 41898, 37809, 37810, 37800, 37803, 37805, 37806, 37796, 33712, 33715, 33707,
  37798, 41896, 41899, 33709, 33710, 37800, 37803, 41897, 41898, 37796, 37799, 41901,
  41893, 41894, 41903, 33708, 33711, 33705, 33706, 37805, 37806, 41896, 41899, 37801,
  33713, 41904] : List Nat).map decode

def c24 : List Move := ([
  41907, 33715, 37803, 41901, 33708, 33711, 41903, 33704, 37801, 33713, 41905, 41906,
  33715, 33707, 37803, 33709, 41901, 41893, 41894, 41903, 33711, 33705, 37801, 37802,
  33713, 41904, 41907, 33715, 37808, 37811, 37805, 37806, 33706, 41901, 33709, 33717,
  33718, 33711, 41903, 33712, 41908, 41911, 33715, 33704, 33707, 33709, 41900, 41903,
  41905, 41906] : List Nat).map decode

def c25 : List Move := ([
  41896, 41899, 33711, 33705, 33706, 41896, 33713, 33714, 41904, 41907, 41899, 41901,
  33705, 33706, 33712, 33715, 33709, 33710, 41903, 41897, 41905, 41906, 33717, 41898,
  33709, 41901, 33718, 41908, 41911, 41903, 33711, 37804, 37807, 41905, 33713, 33704,
  33714, 41907, 41896, 41899, 41901, 41902, 41897, 41898, 33707, 37808, 37811, 41905,
  41906, 42034] : List Nat).map decode

def c26 : List Move := ([
  33843, 37931, 37932, 37935, 33841, 42033, 42025, 33832, 42026, 42035, 33843, 37933,
  37934, 33834, 42029, 33837, 33845, 33846, 33839, 42031, 33840, 42036, 42039, 33843,
  33832, 33835, 33837, 42028, 42031, 42033, 42034, 42024, 42027, 33839, 33833, 33834,
  42024, 33841, 33842, 42032, 42035, 42027, 42029, 33833, 33834, 33840, 33843, 33837,
  33838, 42031] : List Nat).map decode

def c27 : List Move := ([
  42025, 42026, 42033, 42034, 33845, 33837, 42029, 42030, 42025, 42033, 33846, 42041,
  42042, 42035, 42027, 42028, 42036, 42039, 42031, 33839, 42024, 37932, 37935, 42033,
  33841, 33832, 33842, 42035, 42027, 42029, 42030, 42025, 42026, 33835, 37936, 37939,
  42033, 42034] : List Nat).map decode

def S1 : Sparse := [
  (⟨3,0,2⟩, Cell.piston false Dir.xn),
  (⟨2,0,2⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.piston true Dir.xp),
  (⟨2,0,1⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.piston true Dir.zp),
  (⟨3,0,0⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.piston false Dir.xp),
  (⟨3,0,1⟩, Cell.piston false Dir.zn),
  (⟨4,0,0⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.empty),
  (⟨4,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.obs Dir.yp),
  (⟨0,-1,0⟩, Cell.piston false Dir.yp),
  (⟨0,1,1⟩, Cell.obs Dir.yp),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,-1,0⟩, Cell.piston false Dir.zp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,-1,0⟩, Cell.piston false Dir.xp),
  (⟨2,-1,1⟩, Cell.piston false Dir.xp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,-1,0⟩, Cell.piston false Dir.xn),
  (⟨3,-1,2⟩, Cell.piston false Dir.zn),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,0,0⟩, Cell.solid),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S2 : Sparse := [
  (⟨3,0,2⟩, Cell.piston false Dir.xn),
  (⟨3,0,1⟩, Cell.empty),
  (⟨3,0,0⟩, Cell.piston true Dir.zp),
  (⟨2,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.piston true Dir.xp),
  (⟨2,0,0⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.piston false Dir.zn),
  (⟨0,0,0⟩, Cell.piston false Dir.xp),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.obs Dir.yp),
  (⟨4,0,1⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.piston false Dir.yp),
  (⟨0,1,1⟩, Cell.obs Dir.yp),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,-1,0⟩, Cell.piston false Dir.zp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,-1,0⟩, Cell.piston false Dir.xp),
  (⟨2,-1,1⟩, Cell.piston false Dir.xp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,-1,0⟩, Cell.piston false Dir.xn),
  (⟨3,-1,2⟩, Cell.piston false Dir.zn),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,0,0⟩, Cell.solid),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S3 : Sparse := [
  (⟨3,0,2⟩, Cell.empty),
  (⟨3,0,1⟩, Cell.piston false Dir.xp),
  (⟨3,0,0⟩, Cell.piston false Dir.zp),
  (⟨2,0,2⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston false Dir.xn),
  (⟨1,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.piston false Dir.xp),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.piston false Dir.zn),
  (⟨2,0,0⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨4,0,1⟩, Cell.obs Dir.yp),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.piston false Dir.yp),
  (⟨0,1,1⟩, Cell.obs Dir.yp),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,-1,0⟩, Cell.piston false Dir.zp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,-1,0⟩, Cell.piston false Dir.xp),
  (⟨2,-1,1⟩, Cell.piston false Dir.xp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,-1,0⟩, Cell.piston false Dir.xn),
  (⟨3,-1,2⟩, Cell.piston false Dir.zn),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,0,0⟩, Cell.solid),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S4 : Sparse := [
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨3,0,0⟩, Cell.piston false Dir.zp),
  (⟨3,0,1⟩, Cell.empty),
  (⟨4,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.piston false Dir.xp),
  (⟨1,0,1⟩, Cell.piston false Dir.xp),
  (⟨5,0,0⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.solid),
  (⟨2,0,2⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston false Dir.xn),
  (⟨2,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.obs Dir.yp),
  (⟨5,0,1⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.piston false Dir.yp),
  (⟨0,1,1⟩, Cell.obs Dir.yp),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,-1,0⟩, Cell.piston false Dir.zp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,-1,0⟩, Cell.piston false Dir.xp),
  (⟨2,-1,1⟩, Cell.piston false Dir.xp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,-1,0⟩, Cell.piston false Dir.xn),
  (⟨3,-1,2⟩, Cell.piston false Dir.zn),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S5 : Sparse := [
  (⟨3,-1,2⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston false Dir.zn),
  (⟨1,-1,2⟩, Cell.piston false Dir.xp),
  (⟨3,-1,0⟩, Cell.empty),
  (⟨3,-1,1⟩, Cell.piston false Dir.zp),
  (⟨2,-1,0⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.piston false Dir.xn),
  (⟨2,-1,1⟩, Cell.piston false Dir.xp),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.empty),
  (⟨5,0,1⟩, Cell.solid),
  (⟨4,0,1⟩, Cell.empty),
  (⟨3,0,1⟩, Cell.piston true Dir.xp),
  (⟨4,0,0⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston false Dir.zn),
  (⟨3,0,2⟩, Cell.empty),
  (⟨5,0,2⟩, Cell.piston false Dir.xn),
  (⟨2,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.piston true Dir.xp),
  (⟨3,0,0⟩, Cell.piston false Dir.zp),
  (⟨5,0,0⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.obs Dir.yp),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.piston false Dir.yp),
  (⟨0,1,1⟩, Cell.obs Dir.yp),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S6 : Sparse := [
  (⟨0,-1,2⟩, Cell.piston false Dir.zn),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston true Dir.xn),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston true Dir.zp),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.xp),
  (⟨3,-1,0⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.piston false Dir.xp),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨5,0,1⟩, Cell.solid),
  (⟨4,0,1⟩, Cell.empty),
  (⟨3,0,1⟩, Cell.piston true Dir.xp),
  (⟨4,0,0⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston false Dir.zn),
  (⟨3,0,2⟩, Cell.empty),
  (⟨5,0,2⟩, Cell.piston false Dir.xn),
  (⟨2,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.piston true Dir.xp),
  (⟨3,0,0⟩, Cell.piston false Dir.zp),
  (⟨5,0,0⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.obs Dir.yp),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.piston false Dir.yp),
  (⟨0,1,1⟩, Cell.obs Dir.yp),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S7 : Sparse := [
  (⟨0,-1,1⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.xp),
  (⟨2,-1,1⟩, Cell.piston false Dir.xn),
  (⟨1,-1,2⟩, Cell.piston false Dir.zn),
  (⟨2,-1,2⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston false Dir.zp),
  (⟨1,-1,0⟩, Cell.piston false Dir.xp),
  (⟨4,-1,1⟩, Cell.piston false Dir.yp),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨3,-1,0⟩, Cell.empty),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨5,0,1⟩, Cell.solid),
  (⟨4,0,1⟩, Cell.empty),
  (⟨3,0,1⟩, Cell.piston true Dir.xp),
  (⟨4,0,0⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston false Dir.zn),
  (⟨3,0,2⟩, Cell.empty),
  (⟨5,0,2⟩, Cell.piston false Dir.xn),
  (⟨2,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.piston true Dir.xp),
  (⟨3,0,0⟩, Cell.piston false Dir.zp),
  (⟨5,0,0⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.obs Dir.yp),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.obs Dir.yp),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S8 : Sparse := [
  (⟨1,-1,0⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.xp),
  (⟨1,-1,2⟩, Cell.piston false Dir.zn),
  (⟨2,-1,1⟩, Cell.piston false Dir.xn),
  (⟨0,-1,1⟩, Cell.piston false Dir.xp),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston false Dir.zp),
  (⟨3,-1,0⟩, Cell.empty),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨4,-1,1⟩, Cell.piston false Dir.yp),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨6,0,1⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨5,0,1⟩, Cell.solid),
  (⟨4,0,1⟩, Cell.empty),
  (⟨3,0,1⟩, Cell.piston true Dir.xp),
  (⟨4,0,0⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston false Dir.zn),
  (⟨3,0,2⟩, Cell.empty),
  (⟨5,0,2⟩, Cell.piston false Dir.xn),
  (⟨2,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.piston true Dir.xp),
  (⟨3,0,0⟩, Cell.piston false Dir.zp),
  (⟨5,0,0⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.obs Dir.yp),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S9 : Sparse := [
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨3,0,1⟩, Cell.empty),
  (⟨3,0,0⟩, Cell.piston true Dir.zp),
  (⟨4,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.piston false Dir.xp),
  (⟨1,0,1⟩, Cell.piston false Dir.xp),
  (⟨5,0,2⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston false Dir.xn),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.piston false Dir.xp),
  (⟨2,-1,0⟩, Cell.piston false Dir.xn),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston true Dir.zn),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.xp),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨3,-1,0⟩, Cell.piston false Dir.zp),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.piston false Dir.yp),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨6,0,1⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨5,0,1⟩, Cell.solid),
  (⟨4,0,0⟩, Cell.empty),
  (⟨5,0,0⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.obs Dir.yp),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S10 : Sparse := [
  (⟨2,0,0⟩, Cell.piston false Dir.xn),
  (⟨2,0,1⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.piston true Dir.zn),
  (⟨3,0,2⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.piston false Dir.xp),
  (⟨3,0,0⟩, Cell.empty),
  (⟨3,0,1⟩, Cell.piston false Dir.zp),
  (⟨1,0,0⟩, Cell.piston false Dir.xp),
  (⟨4,0,2⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.empty),
  (⟨4,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨5,0,2⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.piston false Dir.xp),
  (⟨2,-1,0⟩, Cell.piston false Dir.xn),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston true Dir.zn),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.xp),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨3,-1,0⟩, Cell.piston false Dir.zp),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.piston false Dir.yp),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨6,0,1⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨5,0,1⟩, Cell.solid),
  (⟨5,0,0⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.obs Dir.yp),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S11 : Sparse := [
  (⟨2,0,0⟩, Cell.piston true Dir.xp),
  (⟨4,0,0⟩, Cell.piston false Dir.xn),
  (⟨3,0,0⟩, Cell.empty),
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨3,0,1⟩, Cell.empty),
  (⟨4,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.piston false Dir.xp),
  (⟨6,0,1⟩, Cell.solid),
  (⟨5,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.piston false Dir.zp),
  (⟨2,0,2⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.empty),
  (⟨5,0,2⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.piston false Dir.xp),
  (⟨2,-1,0⟩, Cell.piston false Dir.xn),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston true Dir.zn),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.xp),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨3,-1,0⟩, Cell.piston false Dir.zp),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.piston false Dir.yp),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨5,0,0⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.obs Dir.yp),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S12 : Sparse := [
  (⟨2,0,0⟩, Cell.piston false Dir.xp),
  (⟨4,0,0⟩, Cell.piston false Dir.xn),
  (⟨3,0,0⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.piston true Dir.zn),
  (⟨0,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.obs Dir.yp),
  (⟨3,0,2⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.piston false Dir.xp),
  (⟨3,0,1⟩, Cell.piston false Dir.zp),
  (⟨4,0,2⟩, Cell.empty),
  (⟨4,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.piston false Dir.yp),
  (⟨6,0,1⟩, Cell.solid),
  (⟨5,0,1⟩, Cell.empty),
  (⟨5,0,2⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.piston false Dir.xp),
  (⟨2,-1,0⟩, Cell.piston false Dir.xn),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston true Dir.zn),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.xp),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨3,-1,0⟩, Cell.piston false Dir.zp),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨5,0,0⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S13 : Sparse := [
  (⟨3,0,0⟩, Cell.piston false Dir.xp),
  (⟨5,0,0⟩, Cell.obs Dir.yp),
  (⟨4,0,0⟩, Cell.empty),
  (⟨3,0,1⟩, Cell.empty),
  (⟨3,0,2⟩, Cell.piston true Dir.zn),
  (⟨4,0,2⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.piston false Dir.xp),
  (⟨5,0,1⟩, Cell.piston false Dir.xn),
  (⟨4,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.piston false Dir.zp),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.piston false Dir.yp),
  (⟨6,0,1⟩, Cell.solid),
  (⟨5,0,2⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.piston false Dir.xp),
  (⟨2,-1,0⟩, Cell.piston false Dir.xn),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston true Dir.zn),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.xp),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨3,-1,0⟩, Cell.piston false Dir.zp),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S14 : Sparse := [
  (⟨1,-1,0⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston false Dir.xp),
  (⟨3,-1,0⟩, Cell.piston false Dir.xn),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston true Dir.zn),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨1,-1,2⟩, Cell.piston false Dir.xp),
  (⟨3,-1,1⟩, Cell.piston false Dir.zp),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.yp),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨6,0,0⟩, Cell.obs Dir.yp),
  (⟨5,0,0⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.piston true Dir.xp),
  (⟨4,0,1⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston true Dir.zn),
  (⟨3,0,1⟩, Cell.empty),
  (⟨5,0,1⟩, Cell.piston false Dir.xn),
  (⟨3,0,2⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.piston true Dir.xp),
  (⟨3,0,0⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.piston false Dir.zp),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨5,0,2⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S15 : Sparse := [
  (⟨3,-1,0⟩, Cell.piston false Dir.xp),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨3,-1,2⟩, Cell.piston true Dir.zn),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston false Dir.xp),
  (⟨5,-1,1⟩, Cell.piston false Dir.xn),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.piston false Dir.yp),
  (⟨1,-1,1⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston false Dir.zp),
  (⟨1,-1,0⟩, Cell.empty),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨6,0,0⟩, Cell.obs Dir.yp),
  (⟨5,0,0⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.piston true Dir.xp),
  (⟨4,0,1⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston true Dir.zn),
  (⟨3,0,1⟩, Cell.empty),
  (⟨5,0,1⟩, Cell.piston false Dir.xn),
  (⟨3,0,2⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.piston true Dir.xp),
  (⟨3,0,0⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.piston false Dir.zp),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨5,0,2⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S16 : Sparse := [
  (⟨4,-1,2⟩, Cell.piston false Dir.zn),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston true Dir.xp),
  (⟨3,-1,0⟩, Cell.empty),
  (⟨3,-1,1⟩, Cell.piston false Dir.xn),
  (⟨1,-1,0⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston false Dir.zp),
  (⟨1,-1,2⟩, Cell.piston false Dir.xp),
  (⟨1,-1,1⟩, Cell.empty),
  (⟨2,-1,1⟩, Cell.piston false Dir.yp),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨5,-1,0⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨6,-1,0⟩, Cell.empty),
  (⟨6,1,0⟩, Cell.obs Dir.yp),
  (⟨6,0,0⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨5,0,0⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.piston true Dir.xp),
  (⟨4,0,1⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston true Dir.zn),
  (⟨3,0,1⟩, Cell.empty),
  (⟨5,0,1⟩, Cell.piston false Dir.xn),
  (⟨3,0,2⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.piston true Dir.xp),
  (⟨3,0,0⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.piston false Dir.zp),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨5,0,2⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S17 : Sparse := [
  (⟨5,0,1⟩, Cell.piston false Dir.xn),
  (⟨3,0,1⟩, Cell.piston false Dir.xp),
  (⟨4,0,1⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.empty),
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨2,0,2⟩, Cell.piston false Dir.xp),
  (⟨4,0,0⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.piston false Dir.yp),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston true Dir.xn),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston true Dir.zp),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.xp),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨3,-1,2⟩, Cell.piston false Dir.zn),
  (⟨3,-1,0⟩, Cell.piston false Dir.xp),
  (⟨1,-1,0⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨5,-1,0⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨6,-1,0⟩, Cell.empty),
  (⟨6,1,0⟩, Cell.obs Dir.yp),
  (⟨6,0,0⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨5,0,0⟩, Cell.empty),
  (⟨3,0,0⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.piston false Dir.zp),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨5,0,2⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.obs Dir.yp),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S18 : Sparse := [
  (⟨2,0,1⟩, Cell.piston false Dir.xp),
  (⟨4,0,1⟩, Cell.piston false Dir.xn),
  (⟨3,0,1⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.piston false Dir.zp),
  (⟨3,0,0⟩, Cell.empty),
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨2,0,2⟩, Cell.piston false Dir.xp),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.obs Dir.yp),
  (⟨0,-1,2⟩, Cell.piston false Dir.yp),
  (⟨5,0,1⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.empty),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston true Dir.xn),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston true Dir.zp),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.xp),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨3,-1,2⟩, Cell.piston false Dir.zn),
  (⟨3,-1,0⟩, Cell.piston false Dir.xp),
  (⟨1,-1,0⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨5,-1,0⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨6,-1,0⟩, Cell.empty),
  (⟨6,1,0⟩, Cell.obs Dir.yp),
  (⟨6,0,0⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨5,0,0⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨5,0,2⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S19 : Sparse := [
  (⟨5,0,2⟩, Cell.piston false Dir.zn),
  (⟨4,0,2⟩, Cell.empty),
  (⟨3,0,2⟩, Cell.piston true Dir.xp),
  (⟨3,0,1⟩, Cell.empty),
  (⟨3,0,0⟩, Cell.piston true Dir.zp),
  (⟨2,0,2⟩, Cell.piston false Dir.xp),
  (⟨5,0,1⟩, Cell.piston false Dir.xn),
  (⟨4,0,1⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.obs Dir.yp),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.piston false Dir.yp),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston true Dir.xn),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston true Dir.zp),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.xp),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨3,-1,2⟩, Cell.piston false Dir.zn),
  (⟨3,-1,0⟩, Cell.piston false Dir.xp),
  (⟨1,-1,0⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨5,-1,0⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨6,-1,0⟩, Cell.empty),
  (⟨6,1,0⟩, Cell.obs Dir.yp),
  (⟨6,0,0⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨5,0,0⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S20 : Sparse := [
  (⟨5,0,1⟩, Cell.empty),
  (⟨4,0,1⟩, Cell.piston false Dir.xn),
  (⟨3,0,1⟩, Cell.piston false Dir.xp),
  (⟨3,0,0⟩, Cell.empty),
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨5,0,0⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.piston false Dir.zp),
  (⟨5,0,2⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.piston false Dir.xp),
  (⟨2,0,2⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.obs Dir.yp),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.piston false Dir.yp),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston true Dir.xn),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston true Dir.zp),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.xp),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨3,-1,2⟩, Cell.piston false Dir.zn),
  (⟨3,-1,0⟩, Cell.piston false Dir.xp),
  (⟨1,-1,0⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨5,-1,0⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨6,-1,0⟩, Cell.empty),
  (⟨6,1,0⟩, Cell.obs Dir.yp),
  (⟨6,0,0⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S21 : Sparse := [
  (⟨1,-1,0⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston false Dir.zp),
  (⟨3,-1,0⟩, Cell.piston false Dir.xn),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.piston false Dir.yp),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨3,-1,2⟩, Cell.piston true Dir.zn),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨2,-1,1⟩, Cell.piston false Dir.xp),
  (⟨2,-1,2⟩, Cell.piston false Dir.xp),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨6,0,2⟩, Cell.obs Dir.yp),
  (⟨5,0,2⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston true Dir.xp),
  (⟨4,0,1⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.piston true Dir.zp),
  (⟨3,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.piston true Dir.xp),
  (⟨5,0,1⟩, Cell.piston false Dir.xn),
  (⟨3,0,0⟩, Cell.empty),
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨5,0,0⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨5,-1,0⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨6,-1,0⟩, Cell.empty),
  (⟨6,1,0⟩, Cell.obs Dir.yp),
  (⟨6,0,0⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S22 : Sparse := [
  (⟨3,-1,2⟩, Cell.piston false Dir.xp),
  (⟨5,-1,2⟩, Cell.piston false Dir.xn),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.empty),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨3,-1,0⟩, Cell.piston true Dir.zp),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston false Dir.xp),
  (⟨4,-1,1⟩, Cell.piston false Dir.zn),
  (⟨1,-1,1⟩, Cell.empty),
  (⟨2,-1,1⟩, Cell.piston false Dir.yp),
  (⟨5,-1,0⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.empty),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨6,0,2⟩, Cell.obs Dir.yp),
  (⟨5,0,2⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston true Dir.xp),
  (⟨4,0,1⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.piston true Dir.zp),
  (⟨3,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.piston true Dir.xp),
  (⟨5,0,1⟩, Cell.piston false Dir.xn),
  (⟨3,0,0⟩, Cell.empty),
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨5,0,0⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.empty),
  (⟨6,-1,0⟩, Cell.empty),
  (⟨6,1,0⟩, Cell.obs Dir.yp),
  (⟨6,0,0⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S23 : Sparse := [
  (⟨3,-1,1⟩, Cell.piston true Dir.xp),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨2,-1,1⟩, Cell.piston false Dir.xp),
  (⟨4,-1,2⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.piston false Dir.zp),
  (⟨6,-1,2⟩, Cell.empty),
  (⟨5,-1,2⟩, Cell.piston false Dir.yp),
  (⟨6,1,2⟩, Cell.obs Dir.yp),
  (⟨6,0,2⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.piston false Dir.xn),
  (⟨3,-1,0⟩, Cell.empty),
  (⟨3,-1,2⟩, Cell.piston false Dir.zn),
  (⟨5,-1,0⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.empty),
  (⟨1,-1,1⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.empty),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨5,0,2⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston true Dir.xp),
  (⟨4,0,1⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.piston true Dir.zp),
  (⟨3,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.piston true Dir.xp),
  (⟨5,0,1⟩, Cell.piston false Dir.xn),
  (⟨3,0,0⟩, Cell.empty),
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨5,0,0⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.empty),
  (⟨6,-1,0⟩, Cell.empty),
  (⟨6,1,0⟩, Cell.obs Dir.yp),
  (⟨6,0,0⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S24 : Sparse := [
  (⟨4,-1,2⟩, Cell.piston true Dir.xn),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨4,-1,0⟩, Cell.piston true Dir.zp),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨2,-1,1⟩, Cell.piston true Dir.xp),
  (⟨2,-1,0⟩, Cell.empty),
  (⟨2,-1,2⟩, Cell.piston false Dir.zn),
  (⟨1,-1,1⟩, Cell.piston false Dir.yp),
  (⟨3,-1,0⟩, Cell.empty),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.piston false Dir.xp),
  (⟨5,-1,2⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨6,-1,2⟩, Cell.empty),
  (⟨6,1,2⟩, Cell.obs Dir.yp),
  (⟨6,0,2⟩, Cell.empty),
  (⟨5,-1,0⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨5,0,2⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston true Dir.xp),
  (⟨4,0,1⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.piston true Dir.zp),
  (⟨3,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.piston true Dir.xp),
  (⟨5,0,1⟩, Cell.piston false Dir.xn),
  (⟨3,0,0⟩, Cell.empty),
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨5,0,0⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.empty),
  (⟨6,-1,0⟩, Cell.empty),
  (⟨6,1,0⟩, Cell.obs Dir.yp),
  (⟨6,0,0⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S25 : Sparse := [
  (⟨4,-1,2⟩, Cell.piston false Dir.xn),
  (⟨2,-1,2⟩, Cell.piston false Dir.xp),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨5,-1,2⟩, Cell.empty),
  (⟨3,-1,1⟩, Cell.empty),
  (⟨3,-1,0⟩, Cell.piston true Dir.zp),
  (⟨4,-1,0⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston false Dir.xp),
  (⟨4,-1,1⟩, Cell.piston false Dir.zn),
  (⟨5,-1,0⟩, Cell.empty),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.piston false Dir.yp),
  (⟨1,-1,1⟩, Cell.empty),
  (⟨6,-1,2⟩, Cell.empty),
  (⟨6,1,2⟩, Cell.obs Dir.yp),
  (⟨6,0,2⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨5,0,2⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.piston true Dir.xp),
  (⟨4,0,1⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.piston true Dir.zp),
  (⟨3,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.piston true Dir.xp),
  (⟨5,0,1⟩, Cell.piston false Dir.xn),
  (⟨3,0,0⟩, Cell.empty),
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨5,0,0⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.empty),
  (⟨6,-1,0⟩, Cell.empty),
  (⟨6,1,0⟩, Cell.obs Dir.yp),
  (⟨6,0,0⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S26 : Sparse := [
  (⟨4,0,2⟩, Cell.piston false Dir.xp),
  (⟨4,-1,2⟩, Cell.piston false Dir.zn),
  (⟨4,-1,0⟩, Cell.piston false Dir.xn),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨3,-1,1⟩, Cell.piston false Dir.xp),
  (⟨2,-1,2⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston false Dir.zp),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨3,-1,0⟩, Cell.piston false Dir.xp),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨5,-1,2⟩, Cell.empty),
  (⟨5,-1,0⟩, Cell.empty),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.piston false Dir.yp),
  (⟨1,-1,1⟩, Cell.empty),
  (⟨6,-1,2⟩, Cell.empty),
  (⟨6,1,2⟩, Cell.obs Dir.yp),
  (⟨6,0,2⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨5,0,2⟩, Cell.empty),
  (⟨4,0,1⟩, Cell.empty),
  (⟨4,0,0⟩, Cell.piston true Dir.zp),
  (⟨3,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.piston true Dir.xp),
  (⟨5,0,1⟩, Cell.piston false Dir.xn),
  (⟨3,0,0⟩, Cell.empty),
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨5,0,0⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.empty),
  (⟨6,-1,0⟩, Cell.empty),
  (⟨6,1,0⟩, Cell.obs Dir.yp),
  (⟨6,0,0⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S27 : Sparse := [
  (⟨3,0,0⟩, Cell.empty),
  (⟨3,0,1⟩, Cell.piston false Dir.xp),
  (⟨3,0,2⟩, Cell.piston false Dir.zn),
  (⟨5,0,0⟩, Cell.piston false Dir.xn),
  (⟨4,0,0⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.empty),
  (⟨4,0,2⟩, Cell.empty),
  (⟨2,0,2⟩, Cell.piston false Dir.xp),
  (⟨4,0,1⟩, Cell.piston false Dir.zp),
  (⟨5,0,2⟩, Cell.empty),
  (⟨5,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.piston false Dir.zn),
  (⟨4,-1,0⟩, Cell.piston false Dir.xn),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨3,-1,1⟩, Cell.piston false Dir.xp),
  (⟨2,-1,2⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston false Dir.zp),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨3,-1,0⟩, Cell.piston false Dir.xp),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨5,-1,2⟩, Cell.empty),
  (⟨5,-1,0⟩, Cell.empty),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.piston false Dir.yp),
  (⟨1,-1,1⟩, Cell.empty),
  (⟨6,-1,2⟩, Cell.empty),
  (⟨6,1,2⟩, Cell.obs Dir.yp),
  (⟨6,0,2⟩, Cell.empty),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.empty),
  (⟨6,-1,0⟩, Cell.empty),
  (⟨6,1,0⟩, Cell.obs Dir.yp),
  (⟨6,0,0⟩, Cell.empty),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨6,0,1⟩, Cell.solid),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

def S28 : Sparse := [
  (⟨4,0,2⟩, Cell.piston false Dir.zn),
  (⟨4,0,0⟩, Cell.piston false Dir.xn),
  (⟨4,0,1⟩, Cell.empty),
  (⟨2,0,1⟩, Cell.empty),
  (⟨3,0,1⟩, Cell.piston false Dir.xp),
  (⟨2,0,2⟩, Cell.empty),
  (⟨2,0,0⟩, Cell.piston false Dir.zp),
  (⟨3,0,2⟩, Cell.empty),
  (⟨3,0,0⟩, Cell.piston false Dir.xp),
  (⟨5,0,1⟩, Cell.empty),
  (⟨5,0,2⟩, Cell.empty),
  (⟨5,0,0⟩, Cell.empty),
  (⟨6,0,2⟩, Cell.empty),
  (⟨6,0,0⟩, Cell.solid),
  (⟨6,0,1⟩, Cell.empty),
  (⟨4,-1,2⟩, Cell.piston false Dir.zn),
  (⟨4,-1,0⟩, Cell.piston false Dir.xn),
  (⟨4,-1,1⟩, Cell.empty),
  (⟨2,-1,1⟩, Cell.empty),
  (⟨3,-1,1⟩, Cell.piston false Dir.xp),
  (⟨2,-1,2⟩, Cell.empty),
  (⟨2,-1,0⟩, Cell.piston false Dir.zp),
  (⟨3,-1,2⟩, Cell.empty),
  (⟨3,-1,0⟩, Cell.piston false Dir.xp),
  (⟨5,-1,1⟩, Cell.empty),
  (⟨5,-1,2⟩, Cell.empty),
  (⟨5,-1,0⟩, Cell.empty),
  (⟨1,-1,2⟩, Cell.empty),
  (⟨1,-1,0⟩, Cell.piston false Dir.yp),
  (⟨1,-1,1⟩, Cell.empty),
  (⟨6,-1,2⟩, Cell.empty),
  (⟨6,1,2⟩, Cell.obs Dir.yp),
  (⟨0,-1,2⟩, Cell.empty),
  (⟨1,0,1⟩, Cell.empty),
  (⟨1,0,0⟩, Cell.empty),
  (⟨1,0,2⟩, Cell.empty),
  (⟨0,0,2⟩, Cell.empty),
  (⟨0,1,2⟩, Cell.empty),
  (⟨6,-1,0⟩, Cell.empty),
  (⟨6,1,0⟩, Cell.obs Dir.yp),
  (⟨0,-1,1⟩, Cell.empty),
  (⟨0,0,1⟩, Cell.empty),
  (⟨0,1,1⟩, Cell.empty),
  (⟨0,-1,0⟩, Cell.empty),
  (⟨6,-1,1⟩, Cell.empty),
  (⟨6,1,1⟩, Cell.obs Dir.yp),
  (⟨0,0,0⟩, Cell.empty),
  (⟨0,1,0⟩, Cell.empty),
  (⟨1,1,0⟩, Cell.obs Dir.yp),
  (⟨1,1,1⟩, Cell.obs Dir.yp),
  (⟨1,1,2⟩, Cell.obs Dir.yp),
  (⟨2,1,0⟩, Cell.obs Dir.yp),
  (⟨2,1,1⟩, Cell.obs Dir.yp),
  (⟨2,1,2⟩, Cell.obs Dir.yp),
  (⟨3,1,0⟩, Cell.obs Dir.yp),
  (⟨3,1,1⟩, Cell.obs Dir.yp),
  (⟨3,1,2⟩, Cell.obs Dir.yp),
  (⟨4,1,0⟩, Cell.obs Dir.yp),
  (⟨4,1,1⟩, Cell.obs Dir.yp),
  (⟨4,1,2⟩, Cell.obs Dir.yp),
  (⟨5,1,0⟩, Cell.obs Dir.yp),
  (⟨5,1,1⟩, Cell.obs Dir.yp),
  (⟨5,1,2⟩, Cell.obs Dir.yp)]

theorem r0 : run S0 c0 = some S1 := by decide +kernel

theorem r1 : run S1 c1 = some S2 := by decide +kernel

theorem r2 : run S2 c2 = some S3 := by decide +kernel

theorem r3 : run S3 c3 = some S4 := by decide +kernel

theorem r4 : run S4 c4 = some S5 := by decide +kernel

theorem r5 : run S5 c5 = some S6 := by decide +kernel

theorem r6 : run S6 c6 = some S7 := by decide +kernel

theorem r7 : run S7 c7 = some S8 := by decide +kernel

theorem r8 : run S8 c8 = some S9 := by decide +kernel

theorem r9 : run S9 c9 = some S10 := by decide +kernel

theorem r10 : run S10 c10 = some S11 := by decide +kernel

theorem r11 : run S11 c11 = some S12 := by decide +kernel

theorem r12 : run S12 c12 = some S13 := by decide +kernel

theorem r13 : run S13 c13 = some S14 := by decide +kernel

theorem r14 : run S14 c14 = some S15 := by decide +kernel

theorem r15 : run S15 c15 = some S16 := by decide +kernel

theorem r16 : run S16 c16 = some S17 := by decide +kernel

theorem r17 : run S17 c17 = some S18 := by decide +kernel

theorem r18 : run S18 c18 = some S19 := by decide +kernel

theorem r19 : run S19 c19 = some S20 := by decide +kernel

theorem r20 : run S20 c20 = some S21 := by decide +kernel

theorem r21 : run S21 c21 = some S22 := by decide +kernel

theorem r22 : run S22 c22 = some S23 := by decide +kernel

theorem r23 : run S23 c23 = some S24 := by decide +kernel

theorem r24 : run S24 c24 = some S25 := by decide +kernel

theorem r25 : run S25 c25 = some S26 := by decide +kernel

theorem r26 : run S26 c26 = some S27 := by decide +kernel

theorem r27 : run S27 c27 = some S28 := by decide +kernel

/-- One period : the exact sequence of E1/E2/R1/R2 moves. -/

def moves : List Move :=
  c0 ++
  c1 ++
  c2 ++
  c3 ++
  c4 ++
  c5 ++
  c6 ++
  c7 ++
  c8 ++
  c9 ++
  c10 ++
  c11 ++
  c12 ++
  c13 ++
  c14 ++
  c15 ++
  c16 ++
  c17 ++
  c18 ++
  c19 ++
  c20 ++
  c21 ++
  c22 ++
  c23 ++
  c24 ++
  c25 ++
  c26 ++
  c27

def start : Sparse := S0

def final : Sparse := S28

theorem size_start : start.length = 30 := by decide +kernel

theorem size_moves : moves.length = 1388 := by decide +kernel

theorem run_all : run start moves = some final := by
  unfold moves start final
  simp only [List.append_assoc]
  exact run_append_some r0 (run_append_some r1 (run_append_some r2 (run_append_some r3 (run_append_some r4 (run_append_some r5 (run_append_some r6 (run_append_some r7 (run_append_some r8 (run_append_some r9 (run_append_some r10 (run_append_some r11 (run_append_some r12 (run_append_some r13 (run_append_some r14 (run_append_some r15 (run_append_some r16 (run_append_some r17 (run_append_some r18 (run_append_some r19 (run_append_some r20 (run_append_some r21 (run_append_some r22 (run_append_some r23 (run_append_some r24 (run_append_some r25 (run_append_some r26 (r27)))))))))))))))))))))))))))


/-- The decider accepts the certificate. -/
theorem check : checkCert start moves v = true := by
  unfold checkCert
  rw [run_all]
  decide +kernel

end Sheet

/-- **The sheet is a GoP2 engine** : `start ⇝¹³⁸⁸ start + (1,0,0)`. -/
theorem sheet_isEngine : IsEngine Sheet.start.get := checkCert_sound Sheet.check

set_option maxRecDepth 100000 in
/-- Explicit form : 1388 successive moves lead from the start to the start shifted by `(1,0,0)`. -/
theorem sheet_path : Path 1388 Sheet.start.get (shift Sheet.start.get ⟨1, 0, 0⟩) := by
  have h : Path Sheet.moves.length Sheet.start.get (shift Sheet.start.get Sheet.v) :=
    checkCert_path (s := Sheet.start) (ms := Sheet.moves) (v := Sheet.v) Sheet.check
  rw [Sheet.size_moves] at h
  exact h

/-! ## 5. The goal of the paper is false -/

/-- GoP2 *has* an engine, so `NoEngine` ("if GoP2 has no engine, then …") is refuted and
Theorem 9 of the draft cannot be used in its current form. -/
theorem gop2_has_engine : ∃ S : Struct, IsEngine S := ⟨_, sheet_isEngine⟩
theorem not_noEngine : ¬ NoEngine := fun h => h _ sheet_isEngine

/-! ## 6. Sanity checks (the decider is not vacuous) -/

namespace Sheet
/-- a move on a retracted, inactive piston is rejected -/
theorem check_neg1 : checkCert start [Move.e1 ⟨0, -1, 0⟩, Move.e1 ⟨0, -1, 0⟩] v = false := by
  decide +kernel
/-- the zero translation is rejected -/
theorem check_neg2 : checkCert start moves 0 = false := by decide +kernel
/-- the empty move list is rejected -/
theorem check_neg3 : checkCert start [] v = false := by decide +kernel
end Sheet

end GoP2

#print axioms GoP2.sheet_isEngine
#print axioms GoP2.sheet_path
#print axioms GoP2.not_noEngine
