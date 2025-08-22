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
  moves : Player → α → Set α

namespace ConcreteGame
variable {c : ConcreteGame.{v} α} {p : Player}

/-- `IsOption a b` means that `a` is either a left or a right move for `b`. -/
@[aesop simp]
def IsOption (c : ConcreteGame α) (a b : α) : Prop :=
  a ∈ c.moves left b ∪ c.moves right b

theorem IsOption.of_mem_moves {p} {a b : α} : a ∈ c.moves p b → c.IsOption a b :=
  p.rec .inl .inr

variable [∀ a, Small.{u} (c.moves left a)] [∀ a, Small.{u} (c.moves right a)]

instance (a : α) : Small.{u} {b // c.IsOption b a} :=
  inferInstanceAs (Small (c.moves left a ∪ c.moves right a :))

/-! ### Loopy games -/

variable (c) in
/-- Turns a state of a `ConcreteLGame` into an `LGame`. -/
def toLGame (a : α) : LGame.{u} :=
  .corec c.moves a

variable (c p) in
@[simp]
theorem moves_toLGame (a : α) : (c.toLGame a).moves p = c.toLGame '' c.moves p a :=
  LGame.moves_corec ..

theorem toLGame_def' (a : α) : c.toLGame a =
    !{fun p ↦ c.toLGame '' c.moves p a} := by
  ext p; simp

theorem toLGame_def (a : α) : c.toLGame a =
    !{c.toLGame '' c.moves left a | c.toLGame '' c.moves right a} := by
  ext p; cases p <;> simp

theorem mem_moves_toLGame_of_mem {a b : α} (hab : b ∈ c.moves p a) :
    c.toLGame b ∈ (c.toLGame a).moves p := by
  rw [moves_toLGame]
  exact ⟨b, hab, rfl⟩

theorem neg_toLGame (h : c.moves left = c.moves right) (a : α) : -c.toLGame a = c.toLGame a := by
  simp_rw [toLGame, LGame.neg_corec_apply]; congr; ext p; cases p <;> simp [h]

/-! ### Well-founded games -/

variable [H : IsWellFounded α c.IsOption]

variable (c) in
/-- **Conway recursion**: build data for a game by recursively building it on its
left and right sets. -/
def moveRecOn {motive : α → Sort*} (x)
    (mk : Π x : α, (∀ p, Π y ∈ c.moves p x, motive y) → motive x) :
    motive x :=
  H.wf.recursion x fun x IH ↦ mk x (fun _ _ h ↦ IH _ (.of_mem_moves h))

variable (c) in
/-- Turns a state of a `ConcreteIGame` into an `IGame`. -/
def toIGame (a : α) : IGame.{u} :=
  have := H
  !{fun p ↦ .range fun b : c.moves p a ↦ toIGame b}
termination_by H.wf.wrap a
decreasing_by all_goals aesop

variable (c p) in
@[simp]
theorem moves_toIGame (a : α) : (c.toIGame a).moves p = c.toIGame '' c.moves p a := by
  rw [toIGame, moves_ofSets, image_eq_range]

theorem toIGame_def' (a : α) : c.toIGame a =
    !{fun p ↦ c.toIGame '' c.moves p a} := by
  ext p; simp

theorem toIGame_def (a : α) : c.toIGame a =
    !{c.toIGame '' c.moves left a | c.toIGame '' c.moves right a} := by
  ext p; cases p <;> simp

theorem mem_moves_toIGame_of_mem {a b : α} (hab : b ∈ c.moves p a) :
    c.toIGame b ∈ (c.toIGame a).moves p := by
  rw [moves_toIGame]
  exact ⟨b, hab, rfl⟩

variable (c) in
@[simp]
theorem toLGame_toIGame (a : α) : (c.toIGame a).toLGame = c.toLGame a := by
  apply c.moveRecOn a fun b IH ↦ ?_
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
  apply c.moveRecOn a fun b IH ↦ ?_
  rw [impartial_def', neg_toIGame h]
  simp_all

/-! ### Convenience constructors -/

section ofImpartial
variable (p : Player) (moves : α → Set α)

/-- Create a `ConcreteGame` from a single function used for the left and right moves. -/
def ofImpartial : ConcreteGame α where
  moves := fun _ ↦ moves

@[simp] theorem ofImpartial_moves : (ofImpartial moves).moves p = moves := rfl

variable {moves} in
theorem isOption_ofImpartial_iff {a b : α} : (ofImpartial moves).IsOption a b ↔ a ∈ moves b :=
  or_self_iff

@[simp]
theorem isOption_ofImpartial : (ofImpartial moves).IsOption = fun a b ↦ a ∈ moves b := by
  ext; exact or_self_iff

variable [Hm : ∀ a, Small.{u} (moves a)]

instance : ∀ a, Small.{u} ((ofImpartial moves).moves p a) := Hm

@[simp]
theorem neg_toLGame_ofImpartial (a : α) :
    -(ofImpartial moves).toLGame a = (ofImpartial moves).toLGame a :=
  neg_toLGame rfl a

variable [IsWellFounded α (ofImpartial moves).IsOption]

instance impartial_toIGame_ofImpartial (a : α) : Impartial ((ofImpartial moves).toIGame a) :=
  impartial_toIGame rfl a

@[simp]
theorem neg_toIGame_ofImpartial (a : α) :
    -(ofImpartial moves).toIGame a = (ofImpartial moves).toIGame a :=
  neg_toIGame rfl a

end ofImpartial
end ConcreteGame
