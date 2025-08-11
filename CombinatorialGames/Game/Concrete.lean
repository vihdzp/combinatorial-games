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

When working with any "specific" game (nim, domineering, etc.) you can use this structure to set up
the basic theorems and definitions, but the intent is that you're not working with `ConcreteGame`
directly most of the time.

Mathematically, `ConcreteGame.toLGame` is nothing but the corecursor on loopy games, while
`ConcreteGame.toIGame` is defined inductively.
-/

universe u v

noncomputable section

open IGame Set

variable {α : Type*}

/-- A "concrete" game is a type of states endowed with move sets for the left and right players.

You can use `ConcreteGame.toLGame` and `ConcreteGame.toIGame` to turn this structure into the
appropriate game type. -/
structure ConcreteGame (α : Type v) where
  /-- The set of options for the left player. -/
  leftMoves : α → Set α
  /-- The set of options for the right player. -/
  rightMoves : α → Set α
  /-- To make a game in universe `u`, the set of left moves must be u-small. -/
  small_leftMoves (a : α) : Small.{u} (leftMoves a) := by infer_instance
  /-- To make a game in universe `u`, the set of left moves must be u-small. -/
  small_rightMoves (a : α) : Small.{u} (rightMoves a) := by infer_instance

namespace ConcreteGame
variable {c : ConcreteGame.{u} α}

instance (a : α) : Small.{u} (c.leftMoves a) := c.small_leftMoves a
instance (a : α) : Small.{u} (c.rightMoves a) := c.small_rightMoves a

/-- `IsOption x y` means that `x` is either a left or a right move for `y`. -/
@[aesop simp]
def IsOption (c : ConcreteGame α) (a b : α) : Prop :=
  a ∈ c.leftMoves b ∪ c.rightMoves b

theorem IsOption.of_mem_leftMoves {x y : α} : x ∈ c.leftMoves y → c.IsOption x y := .inl
theorem IsOption.of_mem_rightMoves {x y : α} : x ∈ c.rightMoves y → c.IsOption x y := .inr

instance (a : α) : Small.{u} {b // c.IsOption b a} :=
  inferInstanceAs (Small (c.leftMoves a ∪ c.rightMoves a :))

/-! ### Loopy games -/

/-- Turns a state of a `ConcreteLGame` into an `LGame`. -/
def toLGame (c : ConcreteGame α) (a : α) : LGame :=
  .corec c.leftMoves c.rightMoves a

@[simp]
theorem leftMoves_toLGame (c : ConcreteGame α) (a : α) :
    (c.toLGame a).leftMoves = c.toLGame '' c.leftMoves a :=
  LGame.leftMoves_corec ..

@[simp]
theorem rightMoves_toLGame (c : ConcreteGame α) (a : α) :
    (c.toLGame a).rightMoves = c.toLGame '' c.rightMoves a :=
  LGame.rightMoves_corec ..

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

/-- Turns a state of a `ConcreteIGame` into an `IGame`. -/
def toIGame (c : ConcreteGame α) [H : IsWellFounded α c.IsOption] (a : α) : IGame :=
  {.range fun b : c.leftMoves a ↦ c.toIGame b | .range fun b : c.rightMoves a ↦ c.toIGame b}ᴵ
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
  rw [impartial_def, neg_toIGame h]
  simp_all

/-! ### Convenience constructors -/

section ofImpartial
variable (moves : α → Set α) [∀ x, Small.{u} (moves x)]

/-- Create a `ConcreteGame` from a single function used for the left and right moves. -/
def ofImpartial : ConcreteGame α where
  leftMoves := moves
  rightMoves := moves

@[simp] theorem ofImpartial_leftMoves : (ofImpartial moves).leftMoves = moves := rfl
@[simp] theorem ofImpartial_rightMoves : (ofImpartial moves).rightMoves = moves := rfl

variable {moves} in
theorem isOption_ofImpartial_iff {x y : α} : (ofImpartial moves).IsOption x y ↔ x ∈ moves y :=
  or_self_iff

@[simp]
theorem isOption_ofImpartial : (ofImpartial moves).IsOption = fun x y ↦ x ∈ moves y := by
  ext; exact or_self_iff

@[simp]
theorem neg_toLGame_ofImpartial (x : α) :
    -(ofImpartial moves).toLGame x = (ofImpartial moves).toLGame x :=
  neg_toLGame rfl x

variable [IsWellFounded α (ofImpartial moves).IsOption]

instance impartial_toIGame_ofImpartial (x : α) : Impartial ((ofImpartial moves).toIGame x) :=
  impartial_toIGame rfl x

@[simp]
theorem neg_toIGame_ofImpartial (x : α) :
    -(ofImpartial moves).toIGame x = (ofImpartial moves).toIGame x :=
  neg_toIGame rfl x

end ofImpartial
end ConcreteGame
