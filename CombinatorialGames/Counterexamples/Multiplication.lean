/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Basic
import CombinatorialGames.Game.Special
import Mathlib.Tactic.FinCases

/-!
# Multiplication of pre-games can't be lifted to the quotient

We show that there exist equivalent pregames `x₁ ≈ x₂` and `y` such that `x₁ * y ≉ x₂ * y`. In
particular, we cannot define the multiplication of games in general.

The specific counterexample we use is `x₁ = y = {0 | 0}` and `x₂ = {-1, 0 | 0, 1}`. The first game
is colloquially known as `star`, so we use the name `star'` for the second. We prove that
`star ≈ star'` and `star * star ≈ star`, but `star' * star ≉ star`.
-/

noncomputable section
open IGame

namespace IGame

/-- The game `⋆' = {-1, 0 | 0, 1}`, which is equivalent but not identical to `⋆`. -/
def star' : IGame := {{0, -1} | {0, 1}}ᴵ
local notation " ⋆' " => star'

@[simp] theorem leftMoves_star' : leftMoves ⋆' = {0, -1} := leftMoves_ofSets ..
@[simp] theorem rightMoves_star' : rightMoves ⋆' = {0, 1} := rightMoves_ofSets ..

/-- `⋆'` is its own negative. -/
theorem neg_star' : -⋆' = ⋆' := by simp [star']

/-- `⋆'` is equivalent to `⋆`. -/
theorem star'_equiv_star : ⋆' ≈ ⋆ := by game_cmp

/-- `⋆' * ⋆ ⧏ ⋆` implies `⋆' * ⋆ ≉  ⋆`.-/
theorem star'_mul_star_lf : ⋆' * ⋆ ⧏ ⋆ := by
  rw [lf_iff_exists_le, rightMoves_mul]
  simp_rw [Set.mem_image, Prod.exists, mulOption]
  exact Or.inr ⟨⋆, ⟨1, 0, by simp⟩, by game_cmp⟩

/-- Pre-game multiplication cannot be lifted to games. -/
theorem mul_not_lift : ∃ x₁ x₂ y : IGame, x₁ ≈ x₂ ∧ ¬ x₁ * y ≈ x₂ * y :=
  ⟨_, _, _, star'_equiv_star, fun h ↦ absurd (star_mul_star ▸ h).ge star'_mul_star_lf⟩

end IGame
