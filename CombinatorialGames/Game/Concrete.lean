/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Impartial

/-!
# Combinatorial games from a type of states

A "concrete" game is a type of states endowed with well-founded subsequence relations for the
left and right players. This is often a more convenient representation for a game, which can then be
used to define a `PGame` or any of the other combinatorial game types.
-/

open PGame

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

@[simp]
theorem toLeftMovesPGame_symm_prop {a : α} (i : (toPGame a).LeftMoves) :
    (toLeftMovesPGame.symm i).1 ≺ₗ a :=
  (toLeftMovesPGame.symm i).prop
@[simp]
theorem toRightMovesPGame_symm_prop {a : α} (i : (toPGame a).RightMoves) :
    (toRightMovesPGame.symm i).1 ≺ᵣ a :=
  (toRightMovesPGame.symm i).prop

-- TODO: PR to Mathlib
theorem heq_subtype {α : Type*} {p q : α → Prop} {a : Subtype p} {b : Subtype q} (h : p = q)
    (he : HEq a b) : a.1 = b.1 := by
  subst h
  simpa [Subtype.eq_iff] using he

theorem neg_toPGame (h : subsequentL (α := α) = subsequentR) (a : α) : -toPGame a = toPGame a := by
  rw [toPGame, neg_def]
  congr
  all_goals try (ext; rw [h])
  all_goals
    apply Function.hfunext (by rw [h])
    simp_rw [heq_eq_eq, Subtype.forall, h]
    intro a ha b hb he
    have : a = b := heq_subtype (by rw [h]) he
    subst this
    have := subrelation_subsequentR hb
    apply neg_toPGame h
termination_by isWellFounded_subsequent.wf.wrap a

theorem impartial_toPGame (h : subsequentL (α := α) = subsequentR) (a : α) :
    Impartial (toPGame a) := by
  rw [impartial_def, neg_toPGame h]
  refine ⟨equiv_rfl, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [moveLeft_toPGame]
    have := subrelation_subsequentL <| toLeftMovesPGame_symm_prop i
    exact impartial_toPGame h _
  · rw [moveRight_toPGame]
    have := subrelation_subsequentR <| toRightMovesPGame_symm_prop i
    exact impartial_toPGame h _
termination_by isWellFounded_subsequent.wf.wrap a

end ConcreteGame
