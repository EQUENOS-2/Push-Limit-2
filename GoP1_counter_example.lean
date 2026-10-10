/-
  PistonFlyingMachine.lean
  =========================
  Lean 4 (tested with v4.15.0), core only: no Mathlib, no `native_decide`, no `sorry`.

  CONTENTS
   1. The game: `V3`, `Dir`, `Cell`, `Config`, `Aset`, `Active`, `Step`, `Reach`,
      `shift`, `FlyingMachine`, and the (false) statement `NoFlyingMachines`.
   2. A verified checker for explicit finite boards (`Board.step_sound`, `Board.run_sound`,
      `Board.shiftOk_sound`): if the Boolean checker accepts a move list, the moves are
      legal in the *relational* semantics `Step`/`Reach` of section 1.
   3. The counterexample: 12 blocks (4 red, 8 pistons) and a 278-move schedule.
   4. Translation invariance of the rules; `Reach.iterate_shift`.
   6. Basic facts: no pistons / no red blocks => no move; self-power fact;
      invariance under `x ↦ -x` and `z ↦ -z` (`step_invariant_x`, `step_invariant_z`).
   7. The level `g = x+y+z`: `red_front_lemma` (the Lemma), `front_lemma`, `rear_lemma`.
   8. Consequences: `red_front_rises`, `front_rises`, `rear_rises`;
      `one_R_vertical` ("only a vertical engine can require only one R block"),
      `one_R_flyer_goes_down`, `needs_two_R`.
   5. Main results (at the end of the file's data part):
        `machine_lap`            : Reach startConfig (shift startConfig e_x)
        `machine_flies n`        : Reach startConfig (shift startConfig (n, 0, 0))
        `startConfig_flyingMachine`, `flying_machines_exist : ¬ NoFlyingMachines`.

  Convention: the empty configuration trivially "flies" with zero moves, so
  `FlyingMachine` requires a non-empty configuration (and `v ≠ 0`).
-/
/-
  PistonFlyingMachine.lean  --  Lean 4 (core only, no Mathlib).

  Part 1.  The game: alphabet, configurations, legal moves, shifts.
-/
namespace PistonGame

/-! ## 1. Basic definitions -/

/-- Points of `ℤ³`. -/
@[ext] structure V3 where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr

namespace V3
instance : Add V3 := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩⟩
instance : Sub V3 := ⟨fun a b => ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩⟩

@[simp] theorem add_x (a b : V3) : (a + b).x = a.x + b.x := rfl
@[simp] theorem add_y (a b : V3) : (a + b).y = a.y + b.y := rfl
@[simp] theorem add_z (a b : V3) : (a + b).z = a.z + b.z := rfl
@[simp] theorem sub_x (a b : V3) : (a - b).x = a.x - b.x := rfl
@[simp] theorem sub_y (a b : V3) : (a - b).y = a.y - b.y := rfl
@[simp] theorem sub_z (a b : V3) : (a - b).z = a.z - b.z := rfl

/-- The grading `g(p) = x + y + z` used in the "front/rear" arguments. -/
def g (p : V3) : Int := p.x + p.y + p.z

@[simp] theorem g_add (a b : V3) : g (a + b) = g a + g b := by
  simp only [g, add_x, add_y, add_z]; omega
end V3

open V3

/-- Basis vectors `e_x, e_y, e_z`. -/
def ex : V3 := ⟨1, 0, 0⟩
def ey : V3 := ⟨0, 1, 0⟩
def ez : V3 := ⟨0, 0, 1⟩

/-- The six directions `±x, ±y, ±z`. -/
inductive Dir
  | px | nx | py | ny | pz | nz
  deriving DecidableEq, Repr

/-- The vector `d ∈ D = {±e_x, ±e_y, ±e_z}` attached to a direction. -/
def Dir.vec : Dir → V3
  | .px => ⟨1, 0, 0⟩
  | .nx => ⟨-1, 0, 0⟩
  | .py => ⟨0, 1, 0⟩
  | .ny => ⟨0, -1, 0⟩
  | .pz => ⟨0, 0, 1⟩
  | .nz => ⟨0, 0, -1⟩

/-- `D = {±e_x, ±e_y, ±e_z}`. -/
def Dset : List V3 := [Dir.px.vec, Dir.nx.vec, Dir.py.vec, Dir.ny.vec, Dir.pz.vec, Dir.nz.vec]

/-- `A = D ∪ {±e_x + e_y, ±e_z + e_y, 2 e_y}`: the activation neighbourhood. -/
def Aset : List V3 :=
  Dset ++ [⟨1, 1, 0⟩, ⟨-1, 1, 0⟩, ⟨0, 1, 1⟩, ⟨0, 1, -1⟩, ⟨0, 2, 0⟩]

/-- The alphabet `Σ = {∅, R, P_{±x}, P_{±y}, P_{±z}}`. -/
inductive Cell
  | empty
  | R
  | P (d : Dir)
  deriving DecidableEq, Repr

/-- A configuration is a function `ℤ³ → Σ`. -/
abbrev Config := V3 → Cell

/-- A piston `P_d` at `p` is *active* iff some `q ∈ p + (A \ {d})` holds an `R`. -/
def Active (C : Config) (p : V3) (d : Dir) : Prop :=
  ∃ a ∈ Aset, a ≠ d.vec ∧ C (p + a) = Cell.R

/-- Result of pushing the block at `p+d` to `p+2d` (the piston is at `p`). -/
def pushResult (C : Config) (p : V3) (d : Dir) : Config := fun q =>
  if q = p + d.vec + d.vec then C (p + d.vec)
  else if q = p + d.vec then Cell.empty
  else C q

/-- Result of pulling the block at `p+2d` to `p+d`. -/
def pullResult (C : Config) (p : V3) (d : Dir) : Config := fun q =>
  if q = p + d.vec then C (p + d.vec + d.vec)
  else if q = p + d.vec + d.vec then Cell.empty
  else C q

/-- One legal move. -/
inductive Step : Config → Config → Prop
  | push {C : Config} {p : V3} {d : Dir} :
      C p = Cell.P d → Active C p d →
      C (p + d.vec) ≠ Cell.empty → C (p + d.vec + d.vec) = Cell.empty →
      Step C (pushResult C p d)
  | pull {C : Config} {p : V3} {d : Dir} :
      C p = Cell.P d → Active C p d →
      C (p + d.vec) = Cell.empty → C (p + d.vec + d.vec) ≠ Cell.empty →
      Step C (pullResult C p d)

/-- A finite sequence of legal moves (possibly empty). -/
inductive Reach : Config → Config → Prop
  | refl (C : Config) : Reach C C
  | tail {A B C : Config} : Reach A B → Step B C → Reach A C

theorem Reach.single {A B : Config} (h : Step A B) : Reach A B := .tail (.refl A) h

theorem Reach.trans {A B C : Config} (h₁ : Reach A B) (h₂ : Reach B C) : Reach A C := by
  induction h₂ with
  | refl => exact h₁
  | tail _ s ih => exact .tail ih s

/-- Translating a configuration by `v`: `(shift C v)(q) = C (q - v)`. -/
def shift (C : Config) (v : V3) : Config := fun q => C (q - v)

/-- Finite support: only finitely many non-`∅` cells. -/
def FiniteSupport (C : Config) : Prop := ∃ l : List V3, ∀ q, C q ≠ Cell.empty → q ∈ l

/-- A (non-trivial) flying machine: finite, non-empty, and a finite sequence of
moves translates it by a non-zero vector.  (The empty configuration is excluded:
it is trivially invariant under every shift, with zero moves.) -/
def FlyingMachine (C : Config) (v : V3) : Prop :=
  FiniteSupport C ∧ (∃ q, C q ≠ Cell.empty) ∧ v ≠ ⟨0, 0, 0⟩ ∧ Reach C (shift C v)

/-- The statement the problem asks to prove (and which the counterexample refutes). -/
def NoFlyingMachines : Prop := ∀ C v, ¬ FlyingMachine C v

end PistonGame
namespace PistonGame
open V3

/-! ## 2. Executable boards (a verified checker for explicit finite configurations) -/

/-- A finite association list of cells; absent cells are `∅`. -/
abbrev Board := List (V3 × Cell)

def Board.get : Board → V3 → Cell
  | [], _ => Cell.empty
  | (p, c) :: t, q => if p = q then c else Board.get t q

def Board.set : Board → V3 → Cell → Board
  | [], q, c => [(q, c)]
  | (p, c') :: t, q, c => if p = q then (p, c) :: t else (p, c') :: Board.set t q c

def Board.keys (b : Board) : List V3 := b.map Prod.fst

theorem Board.get_set (b : Board) (q : V3) (c : Cell) (r : V3) :
    (b.set q c).get r = if q = r then c else b.get r := by
  induction b with
  | nil => simp [Board.set, Board.get]
  | cons e t ih =>
    obtain ⟨p, c'⟩ := e
    by_cases h : p = q
    · subst h
      by_cases h2 : p = r <;> simp [Board.set, Board.get, h2]
    · by_cases h2 : q = r
      · subst h2
        simp [Board.set, Board.get, h, ih]
      · by_cases h3 : p = r
        · subst h3; simp [Board.set, Board.get, h, Ne.symm h]
        · simp [Board.set, Board.get, h, h2, h3, ih]

theorem Board.get_eq_empty_of_not_mem (b : Board) (q : V3) (h : q ∉ b.keys) :
    b.get q = Cell.empty := by
  induction b with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨p, c⟩ := e
    simp only [Board.keys, List.map, List.mem_cons, not_or] at h
    have h1 : p ≠ q := fun e => h.1 e.symm
    simp only [Board.get, h1, if_false]
    exact ih (by simpa [Board.keys] using h.2)

theorem Board.mem_keys_of_ne_empty (b : Board) (q : V3) (h : b.get q ≠ Cell.empty) :
    q ∈ b.keys := by
  by_cases hq : q ∈ b.keys
  · exact hq
  · exact absurd (Board.get_eq_empty_of_not_mem b q hq) h

theorem ne_dbl (p : V3) (d : Dir) : p + d.vec ≠ p + d.vec + d.vec := by
  intro h
  have hx := congrArg V3.x h
  have hy := congrArg V3.y h
  have hz := congrArg V3.z h
  cases d <;> simp [Dir.vec] at hx hy hz <;> omega

theorem get_push (b : Board) (p : V3) (d : Dir) :
    ((b.set (p + d.vec + d.vec) (b.get (p + d.vec))).set (p + d.vec) Cell.empty).get
      = pushResult b.get p d := by
  funext q
  simp only [Board.get_set, pushResult]
  have hne := ne_dbl p d
  by_cases h1 : q = p + d.vec + d.vec
  · subst h1; simp [hne]
  · by_cases h2 : q = p + d.vec
    · subst h2; simp [hne, Ne.symm hne]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem get_pull (b : Board) (p : V3) (d : Dir) :
    ((b.set (p + d.vec) (b.get (p + d.vec + d.vec))).set (p + d.vec + d.vec) Cell.empty).get
      = pullResult b.get p d := by
  funext q
  simp only [Board.get_set, pullResult]
  have hne := ne_dbl p d
  by_cases h1 : q = p + d.vec
  · subst h1; simp [hne, Ne.symm hne]
  · by_cases h2 : q = p + d.vec + d.vec
    · subst h2; simp [hne, Ne.symm hne]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

def Board.isActive (b : Board) (p : V3) (d : Dir) : Bool :=
  Aset.any fun a => decide (a ≠ d.vec) && decide (b.get (p + a) = Cell.R)

theorem Board.isActive_sound {b : Board} {p : V3} {d : Dir}
    (h : b.isActive p d = true) : Active b.get p d := by
  simp only [Board.isActive, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨a, ha, h1, h2⟩ := h
  exact ⟨a, ha, h1, h2⟩

/-- A move is "push" or "pull" with the piston at a given cell. -/
inductive Kind
  | push | pull
  deriving DecidableEq, Repr

structure Move where
  pos : V3
  kind : Kind
  deriving Repr

/-- Execute one move on a board, returning `none` if it is illegal. -/
def Board.step (b : Board) (p : V3) (k : Kind) : Option Board :=
  match b.get p with
  | Cell.P d =>
    if b.isActive p d = true then
      match k with
      | .push =>
        if b.get (p + d.vec) ≠ Cell.empty ∧ b.get (p + d.vec + d.vec) = Cell.empty then
          some ((b.set (p + d.vec + d.vec) (b.get (p + d.vec))).set (p + d.vec) Cell.empty)
        else none
      | .pull =>
        if b.get (p + d.vec) = Cell.empty ∧ b.get (p + d.vec + d.vec) ≠ Cell.empty then
          some ((b.set (p + d.vec) (b.get (p + d.vec + d.vec))).set (p + d.vec + d.vec) Cell.empty)
        else none
    else none
  | _ => none

theorem Board.step_sound {b b' : Board} {p : V3} {k : Kind}
    (h : b.step p k = some b') : Step b.get b'.get := by
  unfold Board.step at h
  cases hp : b.get p with
  | empty => simp [hp] at h
  | R => simp [hp] at h
  | P d =>
    simp only [hp] at h
    by_cases hact : b.isActive p d = true
    · simp only [hact, if_true] at h
      cases k with
      | push =>
        simp only at h
        by_cases hc : b.get (p + d.vec) ≠ Cell.empty ∧ b.get (p + d.vec + d.vec) = Cell.empty
        · rw [if_pos hc] at h
          cases h
          rw [get_push]
          exact Step.push hp (Board.isActive_sound hact) hc.1 hc.2
        · rw [if_neg hc] at h
          cases h
      | pull =>
        simp only at h
        by_cases hc : b.get (p + d.vec) = Cell.empty ∧ b.get (p + d.vec + d.vec) ≠ Cell.empty
        · rw [if_pos hc] at h
          cases h
          rw [get_pull]
          exact Step.pull hp (Board.isActive_sound hact) hc.1 hc.2
        · rw [if_neg hc] at h
          cases h
    · simp [hact] at h

/-- Run a list of moves. -/
def Board.run : Board → List Move → Option Board
  | b, [] => some b
  | b, m :: ms =>
    match b.step m.pos m.kind with
    | none => none
    | some b' => b'.run ms

theorem Board.run_sound : ∀ (ms : List Move) (b b' : Board),
    b.run ms = some b' → Reach b.get b'.get
  | [], b, b', h => by
    simp only [Board.run, Option.some.injEq] at h
    subst h; exact .refl _
  | m :: ms, b, b', h => by
    simp only [Board.run] at h
    split at h
    · simp at h
    · rename_i b1 hb1
      exact (Reach.single (Board.step_sound hb1)).trans (Board.run_sound ms b1 b' h)

/-- Check `b1 = shift b0 v` on finitely many keys. -/
def Board.shiftOk (b0 b1 : Board) (v : V3) : Bool :=
  b1.keys.all (fun k => decide (b1.get k = b0.get (k - v))) &&
  b0.keys.all (fun k => decide (b1.get (k + v) = b0.get k))

theorem Board.sub_add_cancel' (q v : V3) : q - v + v = q := by
  ext <;> simp

theorem Board.shiftOk_sound {b0 b1 : Board} {v : V3}
    (h : Board.shiftOk b0 b1 v = true) : b1.get = shift b0.get v := by
  simp only [Board.shiftOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  funext q
  simp only [shift]
  by_cases hq : q ∈ b1.keys
  · exact h1 q hq
  · have e1 : b1.get q = Cell.empty := Board.get_eq_empty_of_not_mem b1 q hq
    rw [e1]
    by_cases hq0 : q - v ∈ b0.keys
    · have := h2 (q - v) hq0
      rw [Board.sub_add_cancel', e1] at this
      exact this
    · exact (Board.get_eq_empty_of_not_mem b0 _ hq0).symm

theorem Board.finiteSupport (b : Board) : FiniteSupport b.get :=
  ⟨b.keys, fun q h => Board.mem_keys_of_ne_empty b q h⟩

end PistonGame
namespace PistonGame
open V3

/-! ## 3. The counterexample: a 12-block flying machine -/

/-- The machine's initial configuration: 4 red blocks and 8 pistons.
    Coordinates are `(x, y, z)`, `y` is the vertical axis. -/
def startBoard : Board := [
  (⟨0, 0, 0⟩, Cell.R),
  (⟨0, 0, 2⟩, Cell.P .px),
  (⟨0, 1, 1⟩, Cell.R),
  (⟨0, 1, 2⟩, Cell.P .px),
  (⟨0, 2, 2⟩, Cell.R),
  (⟨1, 0, 0⟩, Cell.P .pz),
  (⟨1, 0, 1⟩, Cell.P .py),
  (⟨1, 1, 1⟩, Cell.P .nz),
  (⟨1, 2, 0⟩, Cell.P .ny),
  (⟨2, 0, 1⟩, Cell.P .py),
  (⟨2, 1, 1⟩, Cell.P .nx),
  (⟨2, 2, 0⟩, Cell.R)]

/-- Shorthands for writing the schedule. -/
def pushAt (x y z : Int) : Move := ⟨⟨x, y, z⟩, .push⟩
def pullAt (x y z : Int) : Move := ⟨⟨x, y, z⟩, .pull⟩

/-- The 278-move schedule (`pushAt`/`pullAt` names the cell of the *piston* that acts). -/
def schedule : List Move := [
  pushAt 1 0 0, pushAt 0 0 2, pullAt 1 2 0, pushAt 1 1 0, pushAt 0 1 2, pullAt 2 1 1,
  pushAt 1 1 0, pushAt 2 0 2, pushAt 0 1 2, pullAt 2 2 2, pullAt 0 1 2, pullAt 2 0 2,
  pullAt 0 0 2, pushAt 2 1 2, pullAt 2 0 1, pushAt 2 1 0, pullAt 0 1 0, pullAt 0 1 1,
  pushAt 1 0 2, pushAt 0 1 1, pushAt 0 1 0, pullAt 0 1 2, pullAt 2 1 0, pullAt 1 1 2,
  pushAt 0 1 2, pullAt 1 0 2, pushAt 0 0 2, pushAt 2 0 2, pushAt 0 1 2, pushAt 2 0 1,
  pullAt 0 1 2, pullAt 2 0 2, pullAt 0 0 2, pushAt 1 1 1, pullAt 2 1 2, pullAt 0 1 2,
  pushAt 1 0 2, pullAt 1 1 1, pushAt 0 1 2, pullAt 1 2 2, pullAt 1 0 2, pushAt 0 0 2,
  pushAt 1 1 1, pullAt 0 1 2, pushAt 2 1 1, pushAt 0 1 1, pushAt 0 1 3, pullAt 2 1 1,
  pushAt 1 1 1, pullAt 2 1 3, pullAt 1 1 1, pushAt 2 0 2, pullAt 2 2 2, pullAt 2 0 2,
  pullAt 0 0 2, pushAt 1 1 1, pullAt 1 0 2, pushAt 1 2 1, pushAt 1 0 1, pushAt 1 0 3,
  pullAt 1 2 1, pushAt 2 1 3, pullAt 0 1 3, pushAt 2 1 1, pushAt 1 1 3, pullAt 0 1 1,
  pullAt 1 1 3, pullAt 2 1 1, pushAt 1 2 1, pushAt 1 1 3, pushAt 2 1 1, pullAt 1 2 1,
  pullAt 1 1 1, pushAt 0 1 2, pullAt 1 0 3, pullAt 1 1 1, pushAt 1 2 1, pullAt 1 0 1,
  pullAt 2 1 1, pushAt 1 0 2, pullAt 0 1 2, pushAt 2 1 1, pushAt 0 0 2, pullAt 1 2 1,
  pushAt 1 1 2, pushAt 0 1 2, pullAt 2 1 1, pushAt 1 2 1, pushAt 2 1 2, pushAt 2 1 0,
  pullAt 0 1 0, pullAt 2 1 0, pullAt 2 1 2, pullAt 2 1 1, pushAt 1 1 1, pullAt 2 0 1,
  pushAt 2 0 2, pushAt 2 0 1, pushAt 2 2 2, pushAt 1 1 0, pullAt 1 2 1, pullAt 2 2 2,
  pullAt 3 1 1, pushAt 2 2 2, pullAt 1 1 0, pushAt 1 2 1, pushAt 1 0 1, pushAt 3 0 1,
  pullAt 1 0 1, pullAt 1 2 1, pushAt 1 1 1, pullAt 3 2 1, pullAt 2 2 1, pushAt 3 2 1,
  pullAt 2 2 2, pushAt 2 1 1, pullAt 3 2 1, pushAt 2 2 1, pullAt 1 1 1, pushAt 3 2 1,
  pushAt 1 2 1, pushAt 1 0 1, pullAt 1 2 1, pullAt 3 2 1, pushAt 2 2 1, pushAt 2 2 2,
  pullAt 2 0 2, pullAt 3 0 1, pullAt 1 1 1, pushAt 2 1 2, pushAt 2 2 0, pullAt 2 0 0,
  pullAt 2 2 0, pullAt 2 1 2, pushAt 1 1 1, pushAt 2 0 2, pullAt 2 2 2, pullAt 2 2 1,
  pushAt 3 0 1, pushAt 1 1 1, pushAt 3 2 1, pushAt 1 2 1, pullAt 1 0 1, pullAt 1 2 1,
  pullAt 3 2 1, pullAt 2 2 1, pushAt 3 2 1, pullAt 2 1 1, pushAt 2 2 2, pullAt 3 2 1,
  pushAt 2 2 1, pushAt 3 2 1, pullAt 1 1 1, pushAt 1 2 1, pushAt 1 0 1, pullAt 2 0 2,
  pullAt 3 0 1, pullAt 1 0 1, pullAt 1 2 1, pushAt 2 1 2, pullAt 1 1 1, pushAt 2 0 1,
  pullAt 2 1 2, pushAt 1 1 1, pullAt 2 0 1, pushAt 2 1 2, pullAt 1 1 1, pushAt 2 0 2,
  pushAt 1 1 1, pushAt 1 2 1, pullAt 2 2 2, pullAt 2 0 1, pushAt 1 0 1, pullAt 2 0 2,
  pushAt 3 0 1, pullAt 1 0 1, pullAt 1 2 1, pushAt 1 1 1, pullAt 2 1 2, pushAt 2 0 1,
  pullAt 1 1 1, pushAt 2 1 2, pullAt 2 0 1, pushAt 1 1 1, pushAt 1 1 0, pullAt 2 1 2,
  pushAt 1 1 2, pullAt 1 1 0, pushAt 1 2 1, pushAt 1 0 1, pushAt 3 1 2, pullAt 3 0 1,
  pullAt 1 0 1, pullAt 1 2 1, pushAt 2 0 1, pullAt 3 1 0, pullAt 1 1 1, pushAt 1 2 1,
  pushAt 2 1 0, pullAt 2 0 1, pushAt 1 0 1, pullAt 1 2 1, pushAt 2 0 2, pullAt 3 1 2,
  pushAt 3 0 1, pushAt 1 1 1, pushAt 1 2 1, pullAt 1 0 1, pullAt 3 2 1, pullAt 2 0 1,
  pushAt 3 1 2, pushAt 2 1 0, pushAt 2 1 2, pullAt 2 1 0, pullAt 3 1 2, pushAt 2 0 1,
  pushAt 1 0 1, pushAt 3 2 1, pullAt 1 2 1, pullAt 3 2 1, pushAt 3 1 2, pullAt 3 0 1,
  pullAt 1 1 1, pushAt 2 1 0, pullAt 3 1 2, pullAt 1 1 1, pushAt 2 2 1, pullAt 2 (-1) 2,
  pullAt 2 0 2, pushAt 2 (-1) 2, pullAt 2 2 1, pushAt 1 1 1, pushAt 3 1 2, pullAt 2 1 0,
  pushAt 1 1 1, pushAt 3 0 1, pullAt 3 1 2, pushAt 3 2 1, pushAt 1 2 1, pullAt 1 0 1,
  pullAt 3 2 1, pullAt 2 0 1, pushAt 3 1 2, pushAt 2 1 0, pullAt 2 1 2, pullAt 2 1 0,
  pullAt 2 0 2, pushAt 1 0 2, pushAt 2 0 1, pushAt 1 0 1, pullAt 3 1 2, pushAt 3 2 1,
  pullAt 1 2 1, pullAt 3 2 1, pullAt 1 1 1, pullAt 3 0 1, pushAt 3 1 2, pushAt 1 1 1,
  pushAt 3 0 2, pushAt 3 1 0, pushAt 1 1 0, pushAt 1 1 2, pushAt 3 0 1, pullAt 3 1 0,
  pushAt 3 2 2, pullAt 1 1 2, pullAt 3 0 2, pullAt 1 0 2, pullAt 3 1 2, pullAt 2 1 0,
  pullAt 1 1 2, pushAt 2 0 2, pushAt 2 2 2, pullAt 2 0 2, pushAt 3 1 1, pullAt 2 1 0,
  pushAt 2 2 0, pullAt 2 0 0]


/-- Boolean checker: every move of the schedule is legal and the final board is the
    initial board translated by `e_x`. -/
def verifyLap : Bool :=
  match startBoard.run schedule with
  | none => false
  | some b => startBoard.shiftOk b ex

end PistonGame
namespace PistonGame
open V3

/-! ## 4. Translation invariance of the rules -/

theorem V3.add_sub_cancel_right' (p v : V3) : p + v - v = p := by ext <;> simp
theorem V3.sub_eq_iff (q v r : V3) : q - v = r ↔ q = r + v := by
  constructor
  · intro h
    have hx := congrArg V3.x h
    have hy := congrArg V3.y h
    have hz := congrArg V3.z h
    simp at hx hy hz
    ext <;> simp <;> omega
  · intro h; subst h; ext <;> simp

theorem V3.sub_zero' (q : V3) : q - ⟨0, 0, 0⟩ = q := by ext <;> simp

theorem shift_zero (C : Config) : shift C ⟨0, 0, 0⟩ = C := by
  funext q; simp [shift, V3.sub_zero']

theorem shift_shift (C : Config) (v w : V3) : shift (shift C v) w = shift C (w + v) := by
  funext q
  simp only [shift]
  congr 1
  ext <;> simp <;> omega

theorem shift_pushResult (C : Config) (p v : V3) (d : Dir) :
    shift (pushResult C p d) v = pushResult (shift C v) (p + v) d := by
  funext q
  have e1 : (q - v = p + d.vec + d.vec) ↔ (q = p + v + d.vec + d.vec) := by
    have : p + d.vec + d.vec + v = p + v + d.vec + d.vec := by ext <;> simp <;> omega
    rw [V3.sub_eq_iff, this]
  have e2 : (q - v = p + d.vec) ↔ (q = p + v + d.vec) := by
    have : p + d.vec + v = p + v + d.vec := by ext <;> simp <;> omega
    rw [V3.sub_eq_iff, this]
  have e3 : p + v + d.vec - v = p + d.vec := by ext <;> simp <;> omega
  simp only [shift, pushResult, e1, e2, e3]

theorem shift_pullResult (C : Config) (p v : V3) (d : Dir) :
    shift (pullResult C p d) v = pullResult (shift C v) (p + v) d := by
  funext q
  have e1 : (q - v = p + d.vec + d.vec) ↔ (q = p + v + d.vec + d.vec) := by
    have : p + d.vec + d.vec + v = p + v + d.vec + d.vec := by ext <;> simp <;> omega
    rw [V3.sub_eq_iff, this]
  have e2 : (q - v = p + d.vec) ↔ (q = p + v + d.vec) := by
    have : p + d.vec + v = p + v + d.vec := by ext <;> simp <;> omega
    rw [V3.sub_eq_iff, this]
  have e3 : p + v + d.vec + d.vec - v = p + d.vec + d.vec := by ext <;> simp <;> omega
  simp only [shift, pullResult, e1, e2, e3]

theorem shift_active {C : Config} {p : V3} {d : Dir} (v : V3) (h : Active C p d) :
    Active (shift C v) (p + v) d := by
  obtain ⟨a, ha, hne, hC⟩ := h
  refine ⟨a, ha, hne, ?_⟩
  have : p + v + a - v = p + a := by ext <;> simp <;> omega
  simp only [shift, this, hC]

/-- The rules are translation invariant. -/
theorem Step.shift {C C' : Config} (v : V3) (h : Step C C') :
    Step (PistonGame.shift C v) (PistonGame.shift C' v) := by
  cases h with
  | push hp hact hn hf =>
    rename_i p d
    have e1 : p + v + d.vec - v = p + d.vec := by ext <;> simp <;> omega
    have e2 : p + v + d.vec + d.vec - v = p + d.vec + d.vec := by ext <;> simp <;> omega
    rw [shift_pushResult]
    refine Step.push ?_ (shift_active v hact) ?_ ?_
    · simp only [PistonGame.shift, V3.add_sub_cancel_right', hp]
    · simp only [PistonGame.shift, e1, hn, ne_eq, not_false_eq_true]
    · simp only [PistonGame.shift, e2, hf]
  | pull hp hact hn hf =>
    rename_i p d
    have e1 : p + v + d.vec - v = p + d.vec := by ext <;> simp <;> omega
    have e2 : p + v + d.vec + d.vec - v = p + d.vec + d.vec := by ext <;> simp <;> omega
    rw [shift_pullResult]
    refine Step.pull ?_ (shift_active v hact) ?_ ?_
    · simp only [PistonGame.shift, V3.add_sub_cancel_right', hp]
    · simp only [PistonGame.shift, e1, hn]
    · simp only [PistonGame.shift, e2, hf, ne_eq, not_false_eq_true]

theorem Reach.shift {A B : Config} (v : V3) (h : Reach A B) :
    Reach (PistonGame.shift A v) (PistonGame.shift B v) := by
  induction h with
  | refl => exact .refl _
  | tail _ s ih => exact .tail ih (s.shift v)

/-- `n • v` for a natural number `n`. -/
def V3.nsmul (n : Nat) (v : V3) : V3 := ⟨(n : Int) * v.x, (n : Int) * v.y, (n : Int) * v.z⟩

/-- If a configuration is translated by `v` after finitely many moves, it can be
translated by `n • v` for every `n`: it flies forever. -/
theorem Reach.iterate_shift {C : Config} {v : V3} (h : Reach C (PistonGame.shift C v))
    (n : Nat) : Reach C (PistonGame.shift C (V3.nsmul n v)) := by
  induction n with
  | zero =>
    have e : V3.nsmul 0 v = ⟨0, 0, 0⟩ := by ext <;> simp [V3.nsmul]
    rw [e, shift_zero]; exact .refl C
  | succ n ih =>
    have h2 := Reach.shift (V3.nsmul n v) h
    rw [shift_shift] at h2
    have e : V3.nsmul (n + 1) v = V3.nsmul n v + v := by
      ext <;> simp [V3.nsmul, Int.add_mul]
    rw [e]
    exact ih.trans h2

end PistonGame
namespace PistonGame
open V3

/-! ## 6. Basic facts about the rules -/

theorem V3.add_left_cancel' {p a b : V3} (h : p + a = p + b) : a = b := by
  have hx := congrArg V3.x h
  have hy := congrArg V3.y h
  have hz := congrArg V3.z h
  simp at hx hy hz
  ext <;> omega

theorem Dir.vec_ne_zero (d : Dir) : d.vec ≠ ⟨0, 0, 0⟩ := by
  cases d <;> decide

theorem p_ne_n (p : V3) (d : Dir) : p ≠ p + d.vec := by
  intro h
  have h' : p + (⟨0, 0, 0⟩ : V3) = p + d.vec := by
    rw [← h]; ext <;> simp
  exact Dir.vec_ne_zero d (V3.add_left_cancel' h').symm

theorem p_ne_f (p : V3) (d : Dir) : p ≠ p + d.vec + d.vec := by
  intro h
  have hx := congrArg V3.x h
  have hy := congrArg V3.y h
  have hz := congrArg V3.z h
  cases d <;> simp [Dir.vec] at hx hy hz <;> omega

/-- Without pistons there is no legal move. -/
theorem Step.exists_piston {C C' : Config} (h : Step C C') : ∃ p d, C p = Cell.P d := by
  cases h with
  | @push p d hp _ _ _ => exact ⟨p, d, hp⟩
  | @pull p d hp _ _ _ => exact ⟨p, d, hp⟩

/-- Without red blocks there is no legal move (a piston needs an active `R`). -/
theorem Step.exists_red {C C' : Config} (h : Step C C') : ∃ q, C q = Cell.R := by
  cases h with
  | @push p d _ hact _ _ =>
    obtain ⟨a, _, _, hC⟩ := hact
    exact ⟨p + a, hC⟩
  | @pull p d _ hact _ _ =>
    obtain ⟨a, _, _, hC⟩ := hact
    exact ⟨p + a, hC⟩

theorem Reach.no_red {C C' : Config} (h : Reach C C') (hC : ∀ q, C q ≠ Cell.R) : C' = C := by
  induction h with
  | refl => rfl
  | tail _ s ih =>
    subst ih
    obtain ⟨q, hq⟩ := s.exists_red
    exact absurd hq (hC q)

/-- **Self-power fact (push).**  A push never moves the block that powers the piston. -/
theorem self_power_push {p a : V3} {d : Dir} (hne : a ≠ d.vec) : p + a ≠ p + d.vec :=
  fun h => hne (V3.add_left_cancel' h)

/-- **Self-power fact (pull).**  A pull moves the block at `p + 2d`; that block can
power the piston only if `2d ∈ A \ {d}`, which forces `d = +y` (the block *falls*). -/
theorem self_power_pull {p a : V3} {d : Dir} (ha : a ∈ Aset) (hne : a ≠ d.vec)
    (h : p + a = p + d.vec + d.vec) : d = Dir.py := by
  have h' : a = d.vec + d.vec := by
    have : p + a = p + (d.vec + d.vec) := by
      rw [h]; ext <;> simp <;> omega
    exact V3.add_left_cancel' this
  subst h'
  cases d <;> first | rfl | (exfalso; revert ha; decide)

/-- Each `a ∈ A` has `g(a) ∈ {-1,0,1,2}`. -/
theorem g_Aset_bounds : ∀ a ∈ Aset, -1 ≤ g a ∧ g a ≤ 2 := by decide

theorem g_dir (d : Dir) : g d.vec = 1 ∨ g d.vec = -1 := by
  cases d <;> simp [g, Dir.vec]

theorem g_dir_pos {d : Dir} (h : 1 ≤ g d.vec) : d = Dir.px ∨ d = Dir.py ∨ d = Dir.pz := by
  cases d <;> simp [g, Dir.vec] at h ⊢

theorem g_dir_neg {d : Dir} (h : g d.vec ≤ -1) : d = Dir.nx ∨ d = Dir.ny ∨ d = Dir.nz := by
  cases d <;> simp [g, Dir.vec] at h ⊢

/-! ### Symmetries: the rules are invariant under `x ↦ -x` and `z ↦ -z`. -/

def Cell.map (σ : Dir → Dir) : Cell → Cell
  | .empty => .empty
  | .R => .R
  | .P d => .P (σ d)

/-- Data of a symmetry: an additive involution `ρ` of `ℤ³` preserving `A`, together
with the induced involution `σ` on directions. -/
structure Sym where
  ρ : V3 → V3
  σ : Dir → Dir
  ρ_add : ∀ u v, ρ (u + v) = ρ u + ρ v
  ρ_inv : ∀ v, ρ (ρ v) = v
  ρ_A : ∀ a ∈ Aset, ρ a ∈ Aset
  σ_vec : ∀ d, (σ d).vec = ρ d.vec

def Sym.cfg (S : Sym) (C : Config) : Config := fun q => (C (S.ρ q)).map S.σ

theorem Sym.ρ_eq_iff (S : Sym) (q x : V3) : S.ρ q = x ↔ q = S.ρ x := by
  constructor
  · intro h; rw [← h, S.ρ_inv]
  · intro h; rw [h, S.ρ_inv]

theorem Sym.cfg_pos (S : Sym) (C : Config) (p : V3) :
    S.cfg C (S.ρ p) = (C p).map S.σ := by
  simp [Sym.cfg, S.ρ_inv]

theorem Sym.cfg_n (S : Sym) (C : Config) (p : V3) (d : Dir) :
    S.cfg C (S.ρ p + (S.σ d).vec) = (C (p + d.vec)).map S.σ := by
  simp only [Sym.cfg, S.σ_vec, ← S.ρ_add, S.ρ_inv]

theorem Sym.cfg_f (S : Sym) (C : Config) (p : V3) (d : Dir) :
    S.cfg C (S.ρ p + (S.σ d).vec + (S.σ d).vec) = (C (p + d.vec + d.vec)).map S.σ := by
  simp only [Sym.cfg, S.σ_vec, ← S.ρ_add, S.ρ_inv]

theorem Cell.map_eq_empty (σ : Dir → Dir) (c : Cell) : c.map σ = Cell.empty ↔ c = Cell.empty := by
  cases c <;> simp [Cell.map]

theorem Sym.cfg_push (S : Sym) (C : Config) (p : V3) (d : Dir) :
    S.cfg (pushResult C p d) = pushResult (S.cfg C) (S.ρ p) (S.σ d) := by
  funext q
  have e1 : S.ρ p + (S.σ d).vec + (S.σ d).vec = S.ρ (p + d.vec + d.vec) := by
    rw [S.σ_vec, S.ρ_add, S.ρ_add]
  have e2 : S.ρ p + (S.σ d).vec = S.ρ (p + d.vec) := by rw [S.σ_vec, S.ρ_add]
  have hn := S.cfg_n C p d
  show (pushResult C p d (S.ρ q)).map S.σ = pushResult (S.cfg C) (S.ρ p) (S.σ d) q
  unfold pushResult
  rw [hn, e1, e2]
  by_cases h1 : q = S.ρ (p + d.vec + d.vec)
  · have h1' : S.ρ q = p + d.vec + d.vec := (S.ρ_eq_iff _ _).2 h1
    rw [if_pos h1', if_pos h1]
  · have h1' : ¬ S.ρ q = p + d.vec + d.vec := fun h => h1 ((S.ρ_eq_iff _ _).1 h)
    rw [if_neg h1', if_neg h1]
    by_cases h2 : q = S.ρ (p + d.vec)
    · have h2' : S.ρ q = p + d.vec := (S.ρ_eq_iff _ _).2 h2
      rw [if_pos h2', if_pos h2]; rfl
    · have h2' : ¬ S.ρ q = p + d.vec := fun h => h2 ((S.ρ_eq_iff _ _).1 h)
      rw [if_neg h2', if_neg h2]; rfl

theorem Sym.cfg_pull (S : Sym) (C : Config) (p : V3) (d : Dir) :
    S.cfg (pullResult C p d) = pullResult (S.cfg C) (S.ρ p) (S.σ d) := by
  funext q
  have e1 : S.ρ p + (S.σ d).vec + (S.σ d).vec = S.ρ (p + d.vec + d.vec) := by
    rw [S.σ_vec, S.ρ_add, S.ρ_add]
  have e2 : S.ρ p + (S.σ d).vec = S.ρ (p + d.vec) := by rw [S.σ_vec, S.ρ_add]
  have hf := S.cfg_f C p d
  show (pullResult C p d (S.ρ q)).map S.σ = pullResult (S.cfg C) (S.ρ p) (S.σ d) q
  unfold pullResult
  rw [hf, e1, e2]
  by_cases h1 : q = S.ρ (p + d.vec)
  · have h1' : S.ρ q = p + d.vec := (S.ρ_eq_iff _ _).2 h1
    rw [if_pos h1', if_pos h1]
  · have h1' : ¬ S.ρ q = p + d.vec := fun h => h1 ((S.ρ_eq_iff _ _).1 h)
    rw [if_neg h1', if_neg h1]
    by_cases h2 : q = S.ρ (p + d.vec + d.vec)
    · have h2' : S.ρ q = p + d.vec + d.vec := (S.ρ_eq_iff _ _).2 h2
      rw [if_pos h2', if_pos h2]; rfl
    · have h2' : ¬ S.ρ q = p + d.vec + d.vec := fun h => h2 ((S.ρ_eq_iff _ _).1 h)
      rw [if_neg h2', if_neg h2]; rfl

theorem Sym.active (S : Sym) {C : Config} {p : V3} {d : Dir} (h : Active C p d) :
    Active (S.cfg C) (S.ρ p) (S.σ d) := by
  obtain ⟨a, ha, hne, hC⟩ := h
  refine ⟨S.ρ a, S.ρ_A a ha, ?_, ?_⟩
  · rw [S.σ_vec]
    intro h
    apply hne
    rw [← S.ρ_inv a, h, S.ρ_inv]
  · have : S.ρ p + S.ρ a = S.ρ (p + a) := (S.ρ_add p a).symm
    rw [this]
    simp [Sym.cfg, S.ρ_inv, hC, Cell.map]

/-- A symmetry maps legal moves to legal moves. -/
theorem Sym.step (S : Sym) {C C' : Config} (h : Step C C') : Step (S.cfg C) (S.cfg C') := by
  cases h with
  | push hp hact hn hf =>
    rename_i p d
    rw [S.cfg_push]
    refine Step.push ?_ (S.active hact) ?_ ?_
    · rw [S.cfg_pos, hp]; rfl
    · rw [S.cfg_n]; exact fun h => hn ((Cell.map_eq_empty _ _).1 h)
    · rw [S.cfg_f, hf]; rfl
  | pull hp hact hn hf =>
    rename_i p d
    rw [S.cfg_pull]
    refine Step.pull ?_ (S.active hact) ?_ ?_
    · rw [S.cfg_pos, hp]; rfl
    · rw [S.cfg_n, hn]; rfl
    · rw [S.cfg_f]; exact fun h => hf ((Cell.map_eq_empty _ _).1 h)

theorem Sym.reach (S : Sym) {A B : Config} (h : Reach A B) : Reach (S.cfg A) (S.cfg B) := by
  induction h with
  | refl => exact .refl _
  | tail _ s ih => exact .tail ih (S.step s)

/-- Reflection `x ↦ -x` (exchanging `P_{+x}` and `P_{-x}`). -/
def Dir.flipX : Dir → Dir
  | .px => .nx | .nx => .px | d => d

/-- Reflection `z ↦ -z` (exchanging `P_{+z}` and `P_{-z}`). -/
def Dir.flipZ : Dir → Dir
  | .pz => .nz | .nz => .pz | d => d

def symX : Sym where
  ρ := fun v => ⟨-v.x, v.y, v.z⟩
  σ := Dir.flipX
  ρ_add := by intro u v; ext <;> simp <;> omega
  ρ_inv := by intro v; ext <;> simp
  ρ_A := by decide
  σ_vec := by intro d; cases d <;> rfl

def symZ : Sym where
  ρ := fun v => ⟨v.x, v.y, -v.z⟩
  σ := Dir.flipZ
  ρ_add := by intro u v; ext <;> simp <;> omega
  ρ_inv := by intro v; ext <;> simp
  ρ_A := by decide
  σ_vec := by intro d; cases d <;> rfl

/-- The rules are invariant under `x ↦ -x`. -/
theorem step_invariant_x {C C' : Config} (h : Step C C') : Step (symX.cfg C) (symX.cfg C') :=
  symX.step h

/-- The rules are invariant under `z ↦ -z`. -/
theorem step_invariant_z {C C' : Config} (h : Step C C') : Step (symZ.cfg C) (symZ.cfg C') :=
  symZ.step h

end PistonGame
namespace PistonGame
open V3

/-! ## 7. The level function `g = x + y + z`: fronts and rears -/

/-- All red blocks lie at level `≤ Λ`. -/
def BoundR (C : Config) (Λ : Int) : Prop := ∀ q, C q = Cell.R → g q ≤ Λ

/-- All non-empty cells lie at level `≤ Λ`. -/
def BoundAll (C : Config) (Λ : Int) : Prop := ∀ q, C q ≠ Cell.empty → g q ≤ Λ

/-- All non-empty cells lie at level `≥ Λ`. -/
def BelowAll (C : Config) (Λ : Int) : Prop := ∀ q, C q ≠ Cell.empty → Λ ≤ g q

theorem exists_violation_R {C : Config} {Λ : Int} (h : ¬ BoundR C Λ) :
    ∃ q, C q = Cell.R ∧ Λ < g q := by
  by_cases hex : ∃ q, C q = Cell.R ∧ Λ < g q
  · exact hex
  · exfalso; apply h; intro q hq
    by_cases hle : g q ≤ Λ
    · exact hle
    · exact absurd ⟨q, hq, by omega⟩ hex

theorem exists_violation_All {C : Config} {Λ : Int} (h : ¬ BoundAll C Λ) :
    ∃ q, C q ≠ Cell.empty ∧ Λ < g q := by
  by_cases hex : ∃ q, C q ≠ Cell.empty ∧ Λ < g q
  · exact hex
  · exfalso; apply h; intro q hq
    by_cases hle : g q ≤ Λ
    · exact hle
    · exact absurd ⟨q, hq, by omega⟩ hex

theorem exists_violation_Below {C : Config} {Λ : Int} (h : ¬ BelowAll C Λ) :
    ∃ q, C q ≠ Cell.empty ∧ g q < Λ := by
  by_cases hex : ∃ q, C q ≠ Cell.empty ∧ g q < Λ
  · exact hex
  · exfalso; apply h; intro q hq
    by_cases hle : Λ ≤ g q
    · exact hle
    · exact absurd ⟨q, hq, by omega⟩ hex

/-- **Lemma (red front).**  If a move makes the maximal level of the red blocks exceed
`Λ` (where `Λ` bounded the red blocks before), then it is a *push* of a red block located
at level exactly `Λ`; the pusher sits directly behind it, faces `+x`, `+y` or `+z`, and is
powered by a different red block at level `≤ Λ`. -/
theorem red_front_lemma {C C' : Config} {Λ : Int} (h : Step C C')
    (hb : BoundR C Λ) (hnb : ¬ BoundR C' Λ) :
    ∃ p d, C p = Cell.P d ∧ (d = Dir.px ∨ d = Dir.py ∨ d = Dir.pz) ∧
      C (p + d.vec) = Cell.R ∧ g (p + d.vec) = Λ ∧ C (p + d.vec + d.vec) = Cell.empty ∧
      C' = pushResult C p d ∧
      ∃ a ∈ Aset, a ≠ d.vec ∧ C (p + a) = Cell.R ∧ g (p + a) ≤ Λ := by
  obtain ⟨q, hq, hgt⟩ := exists_violation_R hnb
  cases h with
  | @push p d hp hact hn hf =>
    by_cases h1 : q = p + d.vec + d.vec
    · subst h1
      have hq' : C (p + d.vec) = Cell.R := by simpa [pushResult] using hq
      have hn_le := hb _ hq'
      have hg : g (p + d.vec + d.vec) = g (p + d.vec) + g d.vec := by simp
      have hd := g_dir d
      have hdpos : 1 ≤ g d.vec := by omega
      refine ⟨p, d, hp, g_dir_pos hdpos, hq', by omega, hf, rfl, ?_⟩
      obtain ⟨a, ha, hne, hC⟩ := hact
      exact ⟨a, ha, hne, hC, hb _ hC⟩
    · by_cases h2 : q = p + d.vec
      · subst h2; simp [pushResult, ne_dbl p d] at hq
      · have : C q = Cell.R := by simpa [pushResult, h1, h2] using hq
        have := hb q this
        omega
  | @pull p d hp hact hn hf =>
    exfalso
    by_cases h1 : q = p + d.vec
    · subst h1
      have hq' : C (p + d.vec + d.vec) = Cell.R := by simpa [pullResult] using hq
      have hf_le := hb _ hq'
      have hgf : g (p + d.vec + d.vec) = g (p + d.vec) + g d.vec := by simp
      have hgn : g (p + d.vec) = g p + g d.vec := by simp
      have hd := g_dir d
      obtain ⟨a, ha, hne, hC⟩ := hact
      have hpa := hb _ hC
      have hga : g (p + a) = g p + g a := by simp
      have hab := g_Aset_bounds a ha
      omega
    · by_cases h2 : q = p + d.vec + d.vec
      · subst h2; simp [pullResult, Ne.symm (ne_dbl p d)] at hq
      · have : C q = Cell.R := by simpa [pullResult, h1, h2] using hq
        have := hb q this
        omega

/-- **Overall front** (the same argument without using `A`): the maximal level of *all*
blocks can only increase through a push, of a block at level `Λ`, by a piston facing
`+x`, `+y` or `+z`. -/
theorem front_lemma {C C' : Config} {Λ : Int} (h : Step C C')
    (hb : BoundAll C Λ) (hnb : ¬ BoundAll C' Λ) :
    ∃ p d, C p = Cell.P d ∧ (d = Dir.px ∨ d = Dir.py ∨ d = Dir.pz) ∧
      C (p + d.vec) ≠ Cell.empty ∧ g (p + d.vec) = Λ ∧ C' = pushResult C p d := by
  obtain ⟨q, hq, hgt⟩ := exists_violation_All hnb
  cases h with
  | @push p d hp hact hn hf =>
    by_cases h1 : q = p + d.vec + d.vec
    · subst h1
      have hn_le := hb _ hn
      have hg : g (p + d.vec + d.vec) = g (p + d.vec) + g d.vec := by simp
      have hd := g_dir d
      have hdpos : 1 ≤ g d.vec := by omega
      exact ⟨p, d, hp, g_dir_pos hdpos, hn, by omega, rfl⟩
    · by_cases h2 : q = p + d.vec
      · subst h2; simp [pushResult, ne_dbl p d] at hq
      · have : C q ≠ Cell.empty := by simpa [pushResult, h1, h2] using hq
        have := hb q this
        omega
  | @pull p d hp hact hn hf =>
    exfalso
    by_cases h1 : q = p + d.vec
    · subst h1
      have hf_le := hb _ hf
      have hgf : g (p + d.vec + d.vec) = g (p + d.vec) + g d.vec := by simp
      have hgn : g (p + d.vec) = g p + g d.vec := by simp
      have hd := g_dir d
      have hp_le := hb p (by rw [hp]; intro h; cases h)
      omega
    · by_cases h2 : q = p + d.vec + d.vec
      · subst h2; simp [pullResult, Ne.symm (ne_dbl p d)] at hq
      · have : C q ≠ Cell.empty := by simpa [pullResult, h1, h2] using hq
        have := hb q this
        omega

/-- **Rear** (the mirror statement): if after a move *all* blocks lie at level `≥ Λ+1`
while before the move some block lay at level `≤ Λ`, then the move is a *pull* by a
piston facing `-x`, `-y` or `-z`, of the block located two cells ahead of the piston
(at level exactly `Λ`). -/
theorem rear_lemma {C C' : Config} {Λ : Int} (h : Step C C')
    (hex : ∃ q0, C q0 ≠ Cell.empty ∧ g q0 ≤ Λ)
    (hb : BelowAll C' (Λ + 1)) :
    ∃ p d, C p = Cell.P d ∧ (d = Dir.nx ∨ d = Dir.ny ∨ d = Dir.nz) ∧
      C (p + d.vec) = Cell.empty ∧ C (p + d.vec + d.vec) ≠ Cell.empty ∧
      g (p + d.vec + d.vec) = Λ ∧ C' = pullResult C p d := by
  obtain ⟨q0, hq0, hg0⟩ := hex
  cases h with
  | @push p d hp hact hn hf =>
    exfalso
    -- q0 must be the cell that is vacated, i.e. p + d
    have hq : q0 = p + d.vec := by
      by_cases h1 : q0 = p + d.vec + d.vec
      · rw [h1] at hq0; exact absurd hf hq0
      · by_cases h2 : q0 = p + d.vec
        · exact h2
        · have h3 : pushResult C p d q0 ≠ Cell.empty := by simpa [pushResult, h1, h2] using hq0
          have := hb q0 h3
          omega
    rw [hq] at hg0
    have hf' : pushResult C p d (p + d.vec + d.vec) ≠ Cell.empty := by
      simpa [pushResult] using hn
    have hgf := hb _ hf'
    have hgf2 : g (p + d.vec + d.vec) = g (p + d.vec) + g d.vec := by simp
    have hgn : g (p + d.vec) = g p + g d.vec := by simp
    have hp' : pushResult C p d p ≠ Cell.empty := by
      simp [pushResult, p_ne_f p d, p_ne_n p d, hp]
    have hgp := hb p hp'
    have hd := g_dir d
    omega
  | @pull p d hp hact hn hf =>
    have hq : q0 = p + d.vec + d.vec := by
      by_cases h1 : q0 = p + d.vec
      · rw [h1] at hq0; exact absurd hn hq0
      · by_cases h2 : q0 = p + d.vec + d.vec
        · exact h2
        · have h3 : pullResult C p d q0 ≠ Cell.empty := by simpa [pullResult, h1, h2] using hq0
          have := hb q0 h3
          omega
    rw [hq] at hg0
    have hn' : pullResult C p d (p + d.vec) ≠ Cell.empty := by
      simpa [pullResult] using hf
    have hgn := hb _ hn'
    have hgf : g (p + d.vec + d.vec) = g (p + d.vec) + g d.vec := by simp
    have hd := g_dir d
    have hdneg : g d.vec ≤ -1 := by omega
    exact ⟨p, d, hp, g_dir_neg hdneg, hn, hf, by omega, rfl⟩

end PistonGame
namespace PistonGame
open V3

/-! ## 8. Consequences for flying machines -/

theorem V3.g_sub (q v : V3) : g (q - v) = g q - g v := by
  simp only [g, sub_x, sub_y, sub_z]; omega

/-- Along a path from a configuration satisfying `B` to one that does not, there is a
single move leaving `B`. -/
theorem Reach.exit {B : Config → Prop} {A C : Config} (h : Reach A C) :
    B A → ¬ B C → ∃ C1 C2, Reach A C1 ∧ Step C1 C2 ∧ B C1 ∧ ¬ B C2 := by
  induction h with
  | refl => intro h1 h2; exact absurd h1 h2
  | @tail X Y hr s ih =>
    intro hA hC
    by_cases hX : B X
    · exact ⟨X, Y, hr, s, hX, hC⟩
    · exact ih hA hX

/-- **Consequence (R-front).**  If a configuration with red blocks reaches a translate
by `v` with `x+y+z > 0` for `v`, then at some moment the red front rises, and it does so
by a push from directly behind (the pusher faces `+x,+y` or `+z`), powered by another red
block.  (After applying the symmetries `x ↦ -x`, `z ↦ -z` this covers every direction
except steeply downward ones.) -/
theorem red_front_rises {C : Config} {v : V3} {Λ : Int}
    (hfly : Reach C (shift C v)) (hbound : BoundR C Λ)
    (hatt : ∃ q, C q = Cell.R ∧ g q = Λ) (hv : 0 < g v) :
    ∃ C1 p d, Reach C C1 ∧ BoundR C1 Λ ∧ C1 p = Cell.P d ∧
      (d = Dir.px ∨ d = Dir.py ∨ d = Dir.pz) ∧
      C1 (p + d.vec) = Cell.R ∧ g (p + d.vec) = Λ ∧ C1 (p + d.vec + d.vec) = Cell.empty ∧
      ∃ a ∈ Aset, a ≠ d.vec ∧ C1 (p + a) = Cell.R ∧ g (p + a) ≤ Λ := by
  have hnb : ¬ BoundR (shift C v) Λ := by
    intro hB
    obtain ⟨q, hq, hgq⟩ := hatt
    have h1 : shift C v (q + v) = Cell.R := by
      simp only [shift, V3.add_sub_cancel_right']; exact hq
    have := hB (q + v) h1
    simp at this
    omega
  obtain ⟨C1, C2, hr, hs, hb1, hnb2⟩ := Reach.exit (B := fun X => BoundR X Λ) hfly hbound hnb
  obtain ⟨p, d, h1, h2, h3, h4, h5, -, h6⟩ := red_front_lemma hs hb1 hnb2
  exact ⟨C1, p, d, hr, hb1, h1, h2, h3, h4, h5, h6⟩

/-- **Consequence (overall front).**  The same argument without `A`: the overall front
rises only by pushes. -/
theorem front_rises {C : Config} {v : V3} {Λ : Int}
    (hfly : Reach C (shift C v)) (hbound : BoundAll C Λ)
    (hatt : ∃ q, C q ≠ Cell.empty ∧ g q = Λ) (hv : 0 < g v) :
    ∃ C1 p d, Reach C C1 ∧ C1 p = Cell.P d ∧ (d = Dir.px ∨ d = Dir.py ∨ d = Dir.pz) ∧
      C1 (p + d.vec) ≠ Cell.empty ∧ g (p + d.vec) = Λ := by
  have hnb : ¬ BoundAll (shift C v) Λ := by
    intro hB
    obtain ⟨q, hq, hgq⟩ := hatt
    have h1 : shift C v (q + v) ≠ Cell.empty := by
      simp only [shift, V3.add_sub_cancel_right']; exact hq
    have := hB (q + v) h1
    simp at this
    omega
  obtain ⟨C1, C2, hr, hs, hb1, hnb2⟩ := Reach.exit (B := fun X => BoundAll X Λ) hfly hbound hnb
  obtain ⟨p, d, h1, h2, h3, h4, -⟩ := front_lemma hs hb1 hnb2
  exact ⟨C1, p, d, hr, h1, h2, h3, h4⟩

/-- **Consequence (rear).**  Dually, the rear rises only by pulls of a block located two
cells ahead of the pulling piston. -/
theorem rear_rises {C : Config} {v : V3} {Λ : Int}
    (hfly : Reach C (shift C v)) (hmin : BelowAll C Λ)
    (hatt : ∃ q, C q ≠ Cell.empty ∧ g q = Λ) (hv : 0 < g v) :
    ∃ C1 p d, Reach C C1 ∧ C1 p = Cell.P d ∧ (d = Dir.nx ∨ d = Dir.ny ∨ d = Dir.nz) ∧
      C1 (p + d.vec) = Cell.empty ∧ C1 (p + d.vec + d.vec) ≠ Cell.empty ∧
      g (p + d.vec + d.vec) = Λ := by
  have hB0 : ¬ BelowAll C (Λ + 1) := by
    intro hB
    obtain ⟨q, hq, hgq⟩ := hatt
    have := hB q hq
    omega
  have hB1 : ¬ ¬ BelowAll (shift C v) (Λ + 1) := by
    intro hcon
    apply hcon
    intro q hq
    have h1 : C (q - v) ≠ Cell.empty := hq
    have := hmin _ h1
    rw [V3.g_sub] at this
    omega
  obtain ⟨C1, C2, hr, hs, hb1, hnb2⟩ :=
    Reach.exit (B := fun X => ¬ BelowAll X (Λ + 1)) hfly hB0 hB1
  have hbel2 : BelowAll C2 (Λ + 1) := Classical.not_not.mp hnb2
  obtain ⟨q0, hq0, hg0⟩ := exists_violation_Below hb1
  obtain ⟨p, d, h1, h2, h3, h4, h5, -⟩ := rear_lemma hs ⟨q0, hq0, by omega⟩ hbel2
  exact ⟨C1, p, d, hr, h1, h2, h3, h4, h5⟩

/-! ### Exactly one red block: only a vertical engine -/

/-- `r` is the one and only red block of `C`. -/
def OnlyR (C : Config) (r : V3) : Prop := C r = Cell.R ∧ ∀ q, C q = Cell.R → q = r

/-- The cell one step below `r`. -/
def fall (r : V3) : V3 := ⟨r.x, r.y - 1, r.z⟩

/-- With a single red block, the red block can never be moved except by falling:
after any move it is either where it was, or exactly one cell lower
(self-powered pull by a `P_{+y}` piston). -/
theorem OnlyR.step {C C' : Config} {r : V3} (h : Step C C') (hr : OnlyR C r) :
    OnlyR C' r ∨ OnlyR C' (fall r) := by
  obtain ⟨hr1, hr2⟩ := hr
  cases h with
  | @push p d hp hact hn hf =>
    left
    obtain ⟨a, ha, hne, hC⟩ := hact
    have hpa : p + a = r := hr2 _ hC
    have hnR : C (p + d.vec) ≠ Cell.R := by
      intro hR
      have := hr2 _ hR
      exact self_power_push hne (hpa.trans this.symm)
    have hrf : r ≠ p + d.vec + d.vec := by
      intro e; rw [e, hf] at hr1; cases hr1
    have hrn : r ≠ p + d.vec := by
      intro e; rw [e] at hr1; exact hnR hr1
    refine ⟨?_, ?_⟩
    · simp [pushResult, hrf, hrn, hr1]
    · intro q hq
      by_cases h1 : q = p + d.vec + d.vec
      · subst h1
        have : C (p + d.vec) = Cell.R := by simpa [pushResult] using hq
        exact absurd this hnR
      · by_cases h2 : q = p + d.vec
        · subst h2; simp [pushResult, ne_dbl p d] at hq
        · apply hr2; simpa [pushResult, h1, h2] using hq
  | @pull p d hp hact hn hf =>
    obtain ⟨a, ha, hne, hC⟩ := hact
    have hpa : p + a = r := hr2 _ hC
    by_cases hBR : C (p + d.vec + d.vec) = Cell.R
    · right
      have hfr : p + d.vec + d.vec = r := hr2 _ hBR
      have hdpy : d = Dir.py := self_power_pull ha hne (hpa.trans hfr.symm)
      subst hdpy
      have hfall : fall r = p + Dir.py.vec := by
        rw [← hfr]; ext <;> simp [fall, Dir.vec] <;> omega
      rw [hfall]
      refine ⟨?_, ?_⟩
      · simp [pullResult, hBR]
      · intro q hq
        by_cases h1 : q = p + Dir.py.vec
        · exact h1
        · by_cases h2 : q = p + Dir.py.vec + Dir.py.vec
          · subst h2; simp [pullResult, Ne.symm (ne_dbl p Dir.py)] at hq
          · have hqR : C q = Cell.R := by simpa [pullResult, h1, h2] using hq
            exact absurd ((hr2 q hqR).trans hfr.symm) h2
    · left
      have hrn : r ≠ p + d.vec := by
        intro e; rw [e, hn] at hr1; cases hr1
      have hrf : r ≠ p + d.vec + d.vec := by
        intro e; rw [e] at hr1; exact hBR hr1
      refine ⟨?_, ?_⟩
      · simp [pullResult, hrn, hrf, hr1]
      · intro q hq
        by_cases h1 : q = p + d.vec
        · subst h1
          have : C (p + d.vec + d.vec) = Cell.R := by simpa [pullResult] using hq
          exact absurd this hBR
        · by_cases h2 : q = p + d.vec + d.vec
          · subst h2; simp [pullResult, Ne.symm (ne_dbl p d)] at hq
          · apply hr2; simpa [pullResult, h1, h2] using hq

/-- After any number of moves, the unique red block has only moved downwards, by
single steps. -/
theorem Reach.onlyR {C C' : Config} (h : Reach C C') :
    ∀ r, OnlyR C r → ∃ k : Nat, OnlyR C' ⟨r.x, r.y - (k : Int), r.z⟩ := by
  induction h with
  | refl =>
    intro r hr
    refine ⟨0, ?_⟩
    have : (⟨r.x, r.y - ((0 : Nat) : Int), r.z⟩ : V3) = r := by ext <;> simp
    rw [this]; exact hr
  | tail _ s ih =>
    intro r hr
    obtain ⟨k, hk⟩ := ih r hr
    rcases OnlyR.step s hk with h1 | h1
    · exact ⟨k, h1⟩
    · refine ⟨k + 1, ?_⟩
      have : fall ⟨r.x, r.y - (k : Int), r.z⟩ = ⟨r.x, r.y - ((k + 1 : Nat) : Int), r.z⟩ := by
        ext <;> simp [fall] <;> omega
      rw [← this]; exact h1

/-- **Only a vertical engine can require only one `R` block.**  If a configuration with
exactly one red block reaches a translate of itself by `v`, then `v = (0, -k, 0)` with
`k ≥ 0`: the machine can only fall straight down. -/
theorem one_R_vertical {C : Config} {v r : V3} (hr : OnlyR C r)
    (hfly : Reach C (shift C v)) : v.x = 0 ∧ v.z = 0 ∧ v.y ≤ 0 := by
  obtain ⟨k, hk⟩ := hfly.onlyR r hr
  have h2 : C (⟨r.x, r.y - (k : Int), r.z⟩ - v) = Cell.R := hk.1
  have h3 := hr.2 _ h2
  have hx := congrArg V3.x h3
  have hy := congrArg V3.y h3
  have hz := congrArg V3.z h3
  simp at hx hy hz
  refine ⟨by omega, by omega, by omega⟩

/-- A genuine flying machine with a single `R` block must move strictly downwards. -/
theorem one_R_flyer_goes_down {C : Config} {v r : V3} (hr : OnlyR C r)
    (hfm : FlyingMachine C v) : v.x = 0 ∧ v.z = 0 ∧ v.y < 0 := by
  obtain ⟨hx, hz, hy⟩ := one_R_vertical hr hfm.2.2.2
  refine ⟨hx, hz, ?_⟩
  by_cases h : v.y = 0
  · exfalso; apply hfm.2.2.1; ext <;> simp [hx, hz, h]
  · omega

/-- Equivalently: any flying machine that does not move straight down needs at least two
red blocks (it cannot have exactly one). -/
theorem needs_two_R {C : Config} {v : V3} (hfm : FlyingMachine C v)
    (hnv : v.x ≠ 0 ∨ v.z ≠ 0 ∨ 0 ≤ v.y) : ∀ r, ¬ OnlyR C r := by
  intro r hr
  obtain ⟨hx, hz, hy⟩ := one_R_flyer_goes_down hr hfm
  rcases hnv with h | h | h <;> omega

end PistonGame
namespace PistonGame
open V3

/-! ## 5. The counterexample is a valid flying machine -/

theorem verifyLap_true : verifyLap = true := by decide +kernel

/-- The initial configuration of the machine, as a function `ℤ³ → Σ`. -/
def startConfig : Config := startBoard.get

/-- Sanity checks on the data: 12 blocks, 4 red blocks, 8 pistons, 278 moves. -/
theorem start_size : startBoard.length = 12 := by decide
theorem start_red_count : (startBoard.filter (fun e => e.2 = Cell.R)).length = 4 := by decide
theorem start_piston_count : (startBoard.filter (fun e => e.2 ≠ Cell.R)).length = 8 := by decide
theorem schedule_length : schedule.length = 278 := by decide +kernel

/-- **Every one of the 278 moves is legal, and afterwards the whole machine has moved
by `e_x`.**  (This is the statement `Reach startConfig (shift startConfig e_x)` in the
formal semantics of the game, obtained from the verified checker.) -/
theorem machine_lap : Reach startConfig (shift startConfig ex) := by
  have h := verifyLap_true
  unfold verifyLap at h
  cases hr : startBoard.run schedule with
  | none => rw [hr] at h; simp at h
  | some b =>
    rw [hr] at h
    have h1 := Board.run_sound _ _ _ hr
    have h2 := Board.shiftOk_sound h
    rw [h2] at h1
    exact h1

/-- The machine keeps flying: after `n` laps it is translated by `n e_x`. -/
theorem machine_flies (n : Nat) :
    Reach startConfig (shift startConfig ⟨(n : Int), 0, 0⟩) := by
  have h := Reach.iterate_shift machine_lap n
  have e : V3.nsmul n ex = ⟨(n : Int), 0, 0⟩ := by ext <;> simp [V3.nsmul, ex]
  rwa [e] at h

theorem startConfig_finiteSupport : FiniteSupport startConfig := Board.finiteSupport startBoard

theorem startConfig_nonempty : ∃ q, startConfig q ≠ Cell.empty :=
  ⟨⟨0, 0, 0⟩, by decide⟩

theorem ex_ne_zero : ex ≠ ⟨0, 0, 0⟩ := by decide

/-- The machine is a flying machine in the sense of the problem. -/
theorem startConfig_flyingMachine : FlyingMachine startConfig ex :=
  ⟨startConfig_finiteSupport, startConfig_nonempty, ex_ne_zero, machine_lap⟩

/-- **The conjecture "there are no flying machines" is false.** -/
theorem flying_machines_exist : ¬ NoFlyingMachines :=
  fun h => h startConfig ex startConfig_flyingMachine

end PistonGame

/-! ## 9. Axiom audit (should list only `propext`, `Classical.choice`, `Quot.sound`;
    in particular no `sorry`, and no `Lean.ofReduceBool` / `native_decide`). -/
#print axioms PistonGame.flying_machines_exist
#print axioms PistonGame.machine_flies
#print axioms PistonGame.one_R_vertical
#print axioms PistonGame.red_front_lemma
#print axioms PistonGame.rear_lemma
#print axioms PistonGame.step_invariant_x
#print axioms PistonGame.step_invariant_z
