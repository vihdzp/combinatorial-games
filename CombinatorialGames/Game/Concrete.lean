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
  /-- The set of options for the left player. -/
  leftMoves : α → Set α
  /-- The set of options for the right player. -/
  rightMoves : α → Set α

namespace ConcreteGame
variable {c : ConcreteGame.{v} α}

/-- `IsOption a b` means that `a` is either a left or a right move for `b`. -/
@[aesop simp]
def IsOption (c : ConcreteGame α) (a b : α) : Prop :=
  a ∈ c.leftMoves b ∪ c.rightMoves b

theorem IsOption.of_mem_leftMoves {a b : α} : a ∈ c.leftMoves b → c.IsOption a b := .inl
theorem IsOption.of_mem_rightMoves {a b : α} : a ∈ c.rightMoves b → c.IsOption a b := .inr

variable [∀ a, Small.{u} (c.leftMoves a)] [∀ a, Small.{u} (c.rightMoves a)]

instance (a : α) : Small.{u} {b // c.IsOption b a} :=
  inferInstanceAs (Small (c.leftMoves a ∪ c.rightMoves a :))

/-! ### Loopy games -/

variable (c) in
/-- Turns a state of a `ConcreteLGame` into an `LGame`. -/
def toLGame (a : α) : LGame.{u} :=
  .corec c.leftMoves c.rightMoves a

variable (c) in
@[simp]
theorem leftMoves_toLGame (a : α) : (c.toLGame a).leftMoves = c.toLGame '' c.leftMoves a :=
  LGame.leftMoves_corec ..

variable (c) in
@[simp]
theorem rightMoves_toLGame (a : α) : (c.toLGame a).rightMoves = c.toLGame '' c.rightMoves a :=
  LGame.rightMoves_corec ..

theorem toLGame_def (a : α) : c.toLGame a =
    {c.toLGame '' c.leftMoves a | c.toLGame '' c.rightMoves a}ᴸ := by
  ext <;> simp

theorem mem_leftMoves_toLGame_of_mem {a b : α} (hab : b ∈ c.leftMoves a) :
    c.toLGame b ∈ (c.toLGame a).leftMoves := by
  rw [leftMoves_toLGame]
  exact ⟨b, hab, rfl⟩

theorem mem_rightMoves_toLGame_of_mem {a b : α} (hab : b ∈ c.rightMoves a) :
    c.toLGame b ∈ (c.toLGame a).rightMoves := by
  rw [rightMoves_toLGame]
  exact ⟨b, hab, rfl⟩

theorem neg_toLGame (h : c.leftMoves = c.rightMoves) (a : α) : -c.toLGame a = c.toLGame a := by
  simp_rw [toLGame, LGame.neg_corec_apply, h]

/-! ### Well-founded games -/

variable [H : IsWellFounded α c.IsOption]

variable (c) in
/-- **Conway recursion**: build data for a game by recursively building it on its
left and right sets. -/
def moveRecOn {motive : α → Sort*} (x)
    (mk : Π x : α, (Π y ∈ c.leftMoves x, motive y) → (Π y ∈ c.rightMoves x, motive y) → motive x) :
    motive x :=
  H.wf.recursion x fun x IH ↦
    mk x (fun _ h ↦ IH _ (.of_mem_leftMoves h)) (fun _ h ↦ IH _ (.of_mem_rightMoves h))

variable (c) in
/-- Turns a state of a `ConcreteIGame` into an `IGame`. -/
def toIGame (a : α) : IGame.{u} :=
  have := H
  {.range fun b : c.leftMoves a ↦ toIGame b | .range fun b : c.rightMoves a ↦ toIGame b}ᴵ
termination_by H.wf.wrap a
decreasing_by all_goals aesop

variable (c) in
@[simp]
theorem leftMoves_toIGame (a : α) : (c.toIGame a).leftMoves = c.toIGame '' c.leftMoves a := by
  rw [toIGame, leftMoves_ofSets, image_eq_range]

variable (c) in
@[simp]
theorem rightMoves_toIGame (a : α) : (c.toIGame a).rightMoves = c.toIGame '' c.rightMoves a := by
  rw [toIGame, rightMoves_ofSets, image_eq_range]

theorem toIGame_def (a : α) : c.toIGame a =
    {c.toIGame '' c.leftMoves a | c.toIGame '' c.rightMoves a}ᴵ := by
  ext <;> simp

theorem mem_leftMoves_toIGame_of_mem {a b : α} (hab : b ∈ c.leftMoves a) :
    c.toIGame b ∈ (c.toIGame a).leftMoves := by
  rw [leftMoves_toIGame]
  exact ⟨b, hab, rfl⟩

theorem mem_rightMoves_toIGame_of_mem {a b : α} (hab : b ∈ c.rightMoves a) :
    c.toIGame b ∈ (c.toIGame a).rightMoves := by
  rw [rightMoves_toIGame]
  exact ⟨b, hab, rfl⟩

variable (c) in
@[simp]
theorem toLGame_toIGame (a : α) : (c.toIGame a).toLGame = c.toLGame a := by
  apply c.moveRecOn a fun b IHl IHr ↦ ?_
  ext x
  on_goal 1 => set IH := IHl; rw [leftMoves_toLGame, IGame.leftMoves_toLGame, leftMoves_toIGame]
  on_goal 2 => set IH := IHr; rw [rightMoves_toLGame, IGame.rightMoves_toLGame, rightMoves_toIGame]
  all_goals
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (IH _ hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, mem_image_of_mem _ hx, IH _ hx⟩

theorem neg_toIGame (h : c.leftMoves = c.rightMoves) (a : α) : -c.toIGame a = c.toIGame a := by
  rw [← IGame.toLGame.injective.eq_iff]
  simpa using neg_toLGame h a

theorem impartial_toIGame (h : c.leftMoves = c.rightMoves) (a : α) : Impartial (c.toIGame a) := by
  apply c.moveRecOn a fun b IHl IHr ↦ ?_
  rw [impartial_def', neg_toIGame h]
  simp_all

/-! ### Convenience constructors -/

section ofImpartial
variable (moves : α → Set α)

/-- Create a `ConcreteGame` from a single function used for the left and right moves. -/
def ofImpartial : ConcreteGame α where
  leftMoves := moves
  rightMoves := moves

@[simp] theorem ofImpartial_leftMoves : (ofImpartial moves).leftMoves = moves := rfl
@[simp] theorem ofImpartial_rightMoves : (ofImpartial moves).rightMoves = moves := rfl

variable {moves} in
theorem isOption_ofImpartial_iff {a b : α} : (ofImpartial moves).IsOption a b ↔ a ∈ moves b :=
  or_self_iff

@[simp]
theorem isOption_ofImpartial : (ofImpartial moves).IsOption = fun a b ↦ a ∈ moves b := by
  ext; exact or_self_iff

variable [Hm : ∀ a, Small.{u} (moves a)]

instance : ∀ a, Small.{u} ((ofImpartial moves).leftMoves a) := Hm
instance : ∀ a, Small.{u} ((ofImpartial moves).rightMoves a) := Hm

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
