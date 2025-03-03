/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.IGame.IGame

/-!
# Combinatorial games from a type of states

A "concrete" game is a type of states endowed with well-founded subsequence relations for the
left and right players. This is often a more convenient representation for a game, which can then be
used to define a `IGame`.
-/

noncomputable section

open IGame

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

local infix:50 " ≺ₗ " => subsequentL
local infix:50 " ≺ᵣ " => subsequentR
attribute [instance] isWellFounded_subsequent

theorem subrelation_subsequentL :
    Subrelation subsequentL fun a b : α ↦ subsequentL a b ∨ subsequentR a b :=
  Or.inl

theorem subrelation_subsequentR :
    Subrelation subsequentR fun a b : α ↦ subsequentL a b ∨ subsequentR a b :=
  Or.inr

instance [ConcreteGame α] : IsWellFounded α subsequentL := subrelation_subsequentL.isWellFounded
instance [ConcreteGame α] : IsWellFounded α subsequentR := subrelation_subsequentR.isWellFounded

/-- Defines a concrete game from a single relation, to be used for both players. -/
def ofImpartial (r : α → α → Prop) [h : IsWellFounded α r] : ConcreteGame α where
  subsequentL := r
  subsequentR := r
  isWellFounded_subsequent := by convert h; rw [or_self]

/-- Turns a state of a `ConcreteGame` into an `IGame`. -/
def toIGame (a : α) : IGame :=
  {.range fun b : {b // b ≺ₗ a} ↦ toIGame b |
    .range fun b : {b // b ≺ᵣ a} ↦ toIGame b}ᴵ
termination_by isWellFounded_subsequent.wf.wrap a
decreasing_by all_goals aesop

theorem toIGame_def (a : α) : toIGame a = {toIGame '' {b | b ≺ₗ a} | toIGame '' {b | b ≺ᵣ a}}ᴵ := by
  rw [toIGame]; simp [Set.image_eq_range]

@[simp]
theorem leftMoves_toIGame (a : α) : (toIGame a).leftMoves = toIGame '' {b | b ≺ₗ a} := by
  rw [toIGame_def, leftMoves_ofSets]

@[simp]
theorem rightMoves_toIGame (a : α) : (toIGame a).rightMoves = toIGame '' {b | b ≺ᵣ a} := by
  rw [toIGame_def, rightMoves_ofSets]

theorem neg_toIGame (h : subsequentL (α := α) = subsequentR) (a : α) : -toIGame a = toIGame a := by
  ext
  all_goals
    simp only [leftMoves_neg, rightMoves_neg, rightMoves_toIGame, Set.mem_neg, Set.mem_image,
      Set.mem_setOf_eq, leftMoves_toIGame, h]
    congr! 2
    rw [and_congr_right_iff]
    intros
    rw [← neg_eq_iff_eq_neg, neg_toIGame h]
termination_by isWellFounded_subsequent.wf.wrap a
decreasing_by all_goals aesop

-- TODO: port once we have impartial games

/-
theorem impartial_toPGame (h : subsequentL (α := α) = subsequentR) (a : α) :
    Impartial (toPGame a) := by
  rw [impartial_def, neg_toPGame h]
  refine ⟨.rfl, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [moveLeft_toPGame]
    have := subrelation_subsequentL <| toLeftMovesToPGame_symm_prop i
    exact impartial_toPGame h _
  · rw [moveRight_toPGame]
    have := subrelation_subsequentR <| toRightMovesToPGame_symm_prop i
    exact impartial_toPGame h _
termination_by isWellFounded_subsequent.wf.wrap a
-/

end ConcreteGame
end
