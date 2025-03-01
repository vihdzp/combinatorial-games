/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Tristan Figueroa Reid
-/
import CombinatorialGames.IGame.IGame

/-!
# Special games

This file defines some simple yet notable combinatorial games:

* `⋆ = {0 | 0}`
* `↑ = {0 | ⋆}`
* `↓ = {⋆ | 0}`.
-/

universe u

noncomputable section

namespace Temp

namespace IGame

/-! ### Star -/

/-- The game `⋆ = {{0} | {0}}ᴵ`, which is fuzzy with zero. -/
def star : IGame :=
  {{0} | {0}}ᴵ

@[inherit_doc] notation "⋆" => star

@[simp] theorem leftMoves_star : leftMoves ⋆ = {0} := leftMoves_ofSets ..
@[simp] theorem rightMoves_star : rightMoves ⋆ = {0} := rightMoves_ofSets ..

theorem zero_lf_star : 0 ⧏ ⋆ := by rw [zero_lf]; simp
theorem star_lf_zero : ⋆ ⧏ 0 := by rw [lf_zero]; simp

-- TODO: `star_fuzzy_zero` once we define `CompRel`.

@[simp] theorem neg_star : -star = star := by simp [star]

/-! ### Up and down -/

/-- The game `↑ = {{0} | {⋆}}ᴵ`. -/
def up : IGame :=
  {{0} | {⋆}}ᴵ

@[inherit_doc] notation "↑" => up

@[simp] theorem leftMoves_up : leftMoves ↑ = {0} := leftMoves_ofSets ..
@[simp] theorem rightMoves_up : rightMoves ↑ = {⋆} := rightMoves_ofSets ..

@[simp]
theorem up_pos : 0 < ↑ := by
  rw [lt_iff_le_not_le, zero_lf, zero_le]
  simpa using zero_lf_star

-- TODO: `star_fuzzy_up` once we define `CompRel`.

/-- The pre-game `down` -/
def down : PGame.{u} :=
  ⟨PUnit, PUnit, fun _ ↦ star, fun _ ↦ 0⟩

@[simp]
theorem down_leftMoves : down.LeftMoves = PUnit :=
  rfl

@[simp]
theorem down_rightMoves : down.RightMoves = PUnit :=
  rfl

@[simp]
theorem down_moveLeft (x) : down.moveLeft x = star :=
  rfl

@[simp]
theorem down_moveRight (x) : down.moveRight x = 0 :=
  rfl

@[simp]
theorem down_neg : down < 0 := by
  rw [lt_iff_le_and_lf, lf_zero]
  simp [le_zero_lf, star_lf_zero]

@[simp]
theorem neg_down : -down = up := by simp [up, down]

@[simp]
theorem neg_up : -up = down := by simp [up, down]

theorem star_fuzzy_down : star ‖ down := by
  rw [← neg_fuzzy_neg_iff, neg_down, neg_star]
  exact star_fuzzy_up

end PGame
