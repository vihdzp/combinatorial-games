/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.IGame
import CombinatorialGames.Game.Impartial

/-!
# Combinatorial games from a type of states

A "concrete" game is a type of states endowed with well-founded move relations for the
left and right players. This is often a more convenient representation for a game, which can then be
used to define a `IGame`.
-/

noncomputable section

open IGame

variable {α : Type*}

/-- A "concrete" game is a type of states endowed with well-founded move relations for the
left and right players. -/
class ConcreteGame (α : Type*) where
  /-- The move relation for the left player. -/
  relLeft : α → α → Prop
  /-- The move relation for the right player. -/
  relRight : α → α → Prop
  /-- The move relation is well-founded. -/
  isWellFounded_rel : IsWellFounded α fun a b ↦ relLeft a b ∨ relRight a b

namespace ConcreteGame
variable [ConcreteGame α]

local infix:50 " ≺ₗ " => relLeft
local infix:50 " ≺ᵣ " => relRight
attribute [instance] isWellFounded_rel

theorem subrelation_relLeft :
    Subrelation relLeft fun a b : α ↦ relLeft a b ∨ relRight a b :=
  Or.inl

theorem subrelation_relRight :
    Subrelation relRight fun a b : α ↦ relLeft a b ∨ relRight a b :=
  Or.inr

instance [ConcreteGame α] : IsWellFounded α relLeft := subrelation_relLeft.isWellFounded
instance [ConcreteGame α] : IsWellFounded α relRight := subrelation_relRight.isWellFounded

/-- Defines a concrete game from a single relation, to be used for both players. -/
def ofImpartial (r : α → α → Prop) [h : IsWellFounded α r] : ConcreteGame α where
  relLeft := r
  relRight := r
  isWellFounded_rel := by convert h; rw [or_self]

/-- Turns a state of a `ConcreteGame` into an `IGame`. -/
def toIGame (a : α) : IGame :=
  {.range fun b : {b // b ≺ₗ a} ↦ toIGame b |
    .range fun b : {b // b ≺ᵣ a} ↦ toIGame b}ᴵ
termination_by isWellFounded_rel.wf.wrap a
decreasing_by all_goals aesop

theorem toIGame_def (a : α) : toIGame a = {toIGame '' {b | b ≺ₗ a} | toIGame '' {b | b ≺ᵣ a}}ᴵ := by
  rw [toIGame]; simp [Set.image_eq_range]

@[simp]
theorem leftMoves_toIGame (a : α) : (toIGame a).leftMoves = toIGame '' {b | b ≺ₗ a} := by
  rw [toIGame_def, leftMoves_ofSets]

@[simp]
theorem rightMoves_toIGame (a : α) : (toIGame a).rightMoves = toIGame '' {b | b ≺ᵣ a} := by
  rw [toIGame_def, rightMoves_ofSets]

theorem mem_leftMoves_toIGame_of_relLeft {a b : α} (hab : b ≺ₗ a) :
    toIGame b ∈ (toIGame a).leftMoves := by
  rw [leftMoves_toIGame]
  exact ⟨b, hab, rfl⟩

theorem mem_rightMoves_toIGame_of_relRight {a b : α} (hab : b ≺ᵣ a) :
    toIGame b ∈ (toIGame a).rightMoves := by
  rw [rightMoves_toIGame]
  exact ⟨b, hab, rfl⟩

theorem neg_toIGame (h : relLeft (α := α) = relRight) (a : α) : -toIGame a = toIGame a := by
  ext
  all_goals
    simp only [leftMoves_neg, rightMoves_neg, rightMoves_toIGame, Set.mem_neg, Set.mem_image,
      Set.mem_setOf_eq, leftMoves_toIGame, h]
    congr! 2
    rw [and_congr_right_iff]
    intros
    rw [← neg_eq_iff_eq_neg, neg_toIGame h]
termination_by isWellFounded_rel.wf.wrap a
decreasing_by all_goals aesop

theorem impartial_toIGame (h : relLeft (α := α) = relRight) (a : α) :
    (toIGame a).Impartial := by
  rw [impartial_def, neg_toIGame h, leftMoves_toIGame, rightMoves_toIGame]
  refine ⟨.rfl, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  all_goals rw [← hi.choose_spec.2]
  · have := subrelation_relLeft <| hi.choose_spec.1
    exact impartial_toIGame h _
  · have := subrelation_relRight <| hi.choose_spec.1
    exact impartial_toIGame h _
termination_by isWellFounded_rel.wf.wrap a

end ConcreteGame
end
