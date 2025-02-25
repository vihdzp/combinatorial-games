/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.PGame

/-!
# Combinatorial games from a type of states

A "concrete" game is a type of states endowed with well-founded subsequence relations for the
left and right players. This is often a more convenient representation for a game, which can then be
used to define a `PGame` or any of the other combinatorial game types.
-/

variable {α : Type*}

/-- A "concrete" game is a type of states endowed with well-founded subsequence relations for the
left and right players. -/
class ConcreteGame (α : Type*) where
  /-- The subsequence relation for the left player. -/
  subsequentL : α → α → Prop
  /-- The subsequence relation for the right player. -/
  subsequentR : α → α → Prop
  /-- The subsequence relation is well-founded. -/
  isWellFounded_subsequent : IsWellFounded α fun a b ↦ subsequentL a b ∨ subsequentR a b

namespace ConcreteGame
variable [ConcreteGame α]

scoped infix:50 " ≺ₗ " => subsequentL
scoped infix:50 " ≺ᵣ " => subsequentR
attribute [instance] isWellFounded_subsequent

theorem subrelation_subsequentL :
    Subrelation subsequentL fun a b : α ↦ subsequentL a b ∨ subsequentR a b :=
  Or.inl
theorem subrelation_subsequentR :
    Subrelation subsequentR fun a b : α ↦ subsequentL a b ∨ subsequentR a b :=
  Or.inr

instance [ConcreteGame α] : IsWellFounded α subsequentL :=
  subrelation_subsequentL.isWellFounded
instance [ConcreteGame α] : IsWellFounded α subsequentR :=
  subrelation_subsequentR.isWellFounded

/-- Defines a concrete game from a single relation, to be used for both players. -/
def ofImpartial (r : α → α → Prop) [h : IsWellFounded α r] : ConcreteGame α where
  subsequentL := r
  subsequentR := r
  isWellFounded_subsequent := by convert h; rw [or_self]

/-- Turns a state of a `ConcreteGame` into a `PGame`. -/
def toPGame (a : α) : PGame :=
  PGame.mk {b // b ≺ₗ a} {b // b ≺ᵣ a}
    (fun b ↦ have := subrelation_subsequentL b.2; toPGame b)
    (fun b ↦ have := subrelation_subsequentR b.2; toPGame b)
termination_by isWellFounded_subsequent.wf.wrap a

/-- Use `toLeftMovesPGame` to cast between these two types. -/
theorem leftMoves_toPGame (a : α) : (toPGame a).LeftMoves = {b // b ≺ₗ a} := by
  rw [toPGame]; rfl
/-- Use `toRightMovesPGame` to cast between these two types. -/
theorem rightMoves_toPGame (a : α) : (toPGame a).RightMoves = {b // b ≺ᵣ a} := by
  rw [toPGame]; rfl

theorem moveLeft_toPGame_hEq (a : α) :
    HEq (toPGame a).moveLeft fun i : {b // b ≺ₗ a} => toPGame i.1 := by
  rw [toPGame]; rfl
theorem moveRight_toPGame_hEq (a : α) :
    HEq (toPGame a).moveRight fun i : {b // b ≺ᵣ a} => toPGame i.1 := by
  rw [toPGame]; rfl

/-- Turns a left-subsequent position for `a` into a left move for `toPGame a` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesPGame {a : α} : {b // b ≺ₗ a} ≃ (toPGame a).LeftMoves :=
  Equiv.cast (leftMoves_toPGame a).symm
/-- Turns a right-subsequent position for `a` into a right move for `toPGame a` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesPGame {a : α} : {b // b ≺ᵣ a} ≃ (toPGame a).RightMoves :=
  Equiv.cast (rightMoves_toPGame a).symm

@[simp]
theorem moveLeft_toPGame {a : α} (i) :
    (toPGame a).moveLeft i = toPGame (toLeftMovesPGame.symm i).1 :=
  (congr_heq (moveLeft_toPGame_hEq a).symm (cast_heq _ i)).symm
@[simp]
theorem moveRight_toPGame {a : α} (i) :
    (toPGame a).moveRight i = toPGame (toRightMovesPGame.symm i).1 :=
  (congr_heq (moveRight_toPGame_hEq a).symm (cast_heq _ i)).symm

theorem moveLeft_toPGame_toLeftMovesPGame {a : α} (i) :
    (toPGame a).moveLeft (toLeftMovesPGame i) = toPGame i.1 :=
  by simp
theorem moveRight_toPGame_toRightMovesPGame {a : α} (i) :
    (toPGame a).moveRight (toRightMovesPGame i) = toPGame i.1 :=
  by simp

end ConcreteGame
