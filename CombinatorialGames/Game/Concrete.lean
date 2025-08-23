/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Junyan Xu
-/
import CombinatorialGames.Game.Loopy.IGame
import CombinatorialGames.Game.Impartial.Basic

/-!
# Combinatorial games from a type of states

In the literature, mathematicians often describe games as graphs, consisting of a set of states, as
well as move relations for the left and right players. We define a structure `ConcreteGame` which
facilitates this construction, bundling the left and right set functions along with the type, as
well as functions `ConcreteGame.toLGame` and `ConcreteGame.toIGame` which turn them into the
appropriate type of game.

Mathematically, `ConcreteGame.toLGame` is nothing but the corecursor on loopy games, while
`ConcreteGame.toIGame` is defined inductively.

## Design notes

When working with any "specific" game (nim, domineering, etc.) you can use  `ConcreteGame` to set up
the basic theorems and definitions, but the intent is that you're not working with `ConcreteGame`
directly most of the time.
-/

universe u v

noncomputable section

open IGame Set

variable {α : Type v}

/-- A "concrete" game is a type of states endowed with move sets for the left and right players.

You can use `ConcreteGame.toLGame` and `ConcreteGame.toIGame` to turn this structure into the
appropriate game type. -/
structure ConcreteGame (α : Type v) : Type v where
  /-- The sets of options for the players. -/
  protected moves : Player → α → Set α

namespace ConcreteGame
variable {c : ConcreteGame.{v} α} {p : Player}

/-- `IsOption a b` means that `a` is either a left or a right move for `b`. -/
def IsOption (c : ConcreteGame α) (a b : α) : Prop :=
  a ∈ ⋃ p, c.moves p b

@[aesop simp]
theorem isOption_iff_mem_union {a b : α} :
    c.IsOption a b ↔ a ∈ c.moves left b ∪ c.moves right b := by
  simp [IsOption]

theorem IsOption.of_mem_moves {p} {a b : α} (h : a ∈ c.moves p b) : c.IsOption a b :=
  ⟨_, ⟨p, rfl⟩, h⟩

theorem isWellFounded_isOption_of_eq (r : α → α → Prop) [Hr : IsWellFounded α r]
    (hr : ∀ p x, c.moves p x = {y | r y x}) : IsWellFounded _ c.IsOption := by
  convert Hr
  ext
  simp [isOption_iff_mem_union, hr]

variable [Hl : ∀ a, Small.{u} (c.moves left a)] [Hr : ∀ a, Small.{u} (c.moves right a)]

instance (b : α) : Small.{u} {a // c.IsOption a b} := by
  simp_rw [isOption_iff_mem_union]
  infer_instance

/-! ### Loopy games -/

variable (c) in
/-- Turns a state of a `ConcreteLGame` into an `LGame`. -/
def toLGame (a : α) : LGame.{u} :=
  .corec c.moves a

variable (c p) in
@[simp]
theorem moves_toLGame (a : α) : moves p (c.toLGame a) = c.toLGame '' c.moves p a :=
  LGame.moves_corec ..

theorem toLGame_def' (a : α) : c.toLGame a =
    !{fun p ↦ c.toLGame '' c.moves p a} := by
  ext p; simp

theorem toLGame_def (a : α) : c.toLGame a =
    !{c.toLGame '' c.moves left a | c.toLGame '' c.moves right a} := by
  ext p; cases p <;> simp

theorem mem_moves_toLGame_of_mem {a b : α} (hab : b ∈ c.moves p a) :
    c.toLGame b ∈ moves p (c.toLGame a) := by
  rw [moves_toLGame]
  exact ⟨b, hab, rfl⟩

theorem neg_toLGame (h : c.moves left = c.moves right) (a : α) : -c.toLGame a = c.toLGame a := by
  simp_rw [toLGame, LGame.neg_corec_apply]; congr; ext p; cases p <;> simp [h]

/-! ### Well-founded games -/

variable [H : IsWellFounded α c.IsOption]

variable (c) in
/-- **Conway recursion**: build data for a game by recursively building it on its
left and right sets. -/
@[elab_as_elim]
def moveRecOn {motive : α → Sort*} (x)
    (mk : Π x : α, (∀ p, Π y ∈ c.moves p x, motive y) → motive x) :
    motive x :=
  H.fix _ (fun x IH ↦ mk x fun _ _ h ↦ IH _ (.of_mem_moves h)) x

omit Hl Hr in
theorem moveRecOn_eq {motive : α → Sort*} (x)
    (mk : Π x : α, (∀ p, Π y ∈ c.moves p x, motive y) → motive x) :
    c.moveRecOn x mk = mk x fun _ y _ ↦ c.moveRecOn y mk := by
  rw [moveRecOn, H.fix_eq]
  rfl

variable (c) in
/-- Turns a state of a `ConcreteIGame` into an `IGame`. -/
def toIGame (a : α) : IGame.{u} :=
  c.moveRecOn a fun x IH ↦ !{fun p ↦ .range fun b : c.moves p x ↦ IH p b b.2}

theorem toIGame_def' (a : α) : c.toIGame a =
    !{fun p ↦ c.toIGame '' c.moves p a} := by
  rw [toIGame, moveRecOn_eq]; simp only [toIGame, image_eq_range]

theorem toIGame_def (a : α) : c.toIGame a =
    !{c.toIGame '' c.moves left a | c.toIGame '' c.moves right a} := by
  rw [toIGame_def', ofSets_eq_ofSets_cases]

variable (c p) in
@[simp]
theorem moves_toIGame (a : α) : moves p (c.toIGame a) = c.toIGame '' c.moves p a := by
  rw [toIGame_def']; simp

theorem mem_moves_toIGame_of_mem {a b : α} (hab : b ∈ c.moves p a) :
    c.toIGame b ∈ moves p (c.toIGame a) := by
  rw [moves_toIGame]
  exact ⟨b, hab, rfl⟩

variable (c) in
@[simp]
theorem toLGame_toIGame (a : α) : (c.toIGame a).toLGame = c.toLGame a := by
  refine c.moveRecOn a fun b IH ↦ ?_
  ext x
  rw [moves_toLGame, IGame.moves_toLGame, moves_toIGame]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (IH _ _ hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, mem_image_of_mem _ hx, IH _ _ hx⟩

theorem neg_toIGame (h : c.moves left = c.moves right) (a : α) : -c.toIGame a = c.toIGame a := by
  rw [← IGame.toLGame.injective.eq_iff]
  simpa using neg_toLGame h a

theorem impartial_toIGame (h : c.moves left = c.moves right) (a : α) : Impartial (c.toIGame a) := by
  refine c.moveRecOn a fun b IH ↦ ?_
  rw [impartial_def', neg_toIGame h]
  simp_all

end ConcreteGame
