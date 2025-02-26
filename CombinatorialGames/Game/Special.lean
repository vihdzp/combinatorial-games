/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Tristan Figueroa Reid
-/
import CombinatorialGames.Game.PGame

/-!
# Special games

This file defines some simple yet notable combinatorial games:

* `star = {0 | 0}`
* `up = {0 | star}`
* `down = {star | 0}`.
-/

universe u

namespace PGame

/-! ## Star -/

/-- The pre-game `star`, which is fuzzy with zero. -/
def star : PGame.{u} :=
  ⟨PUnit, PUnit, fun _ ↦ 0, fun _ ↦ 0⟩

@[simp]
theorem star_leftMoves : star.LeftMoves = PUnit :=
  rfl

@[simp]
theorem star_rightMoves : star.RightMoves = PUnit :=
  rfl

@[simp]
theorem star_moveLeft (x) : star.moveLeft x = 0 :=
  rfl

@[simp]
theorem star_moveRight (x) : star.moveRight x = 0 :=
  rfl

instance uniqueStarLeftMoves : Unique star.LeftMoves :=
  PUnit.instUnique

instance uniqueStarRightMoves : Unique star.RightMoves :=
  PUnit.instUnique

theorem zero_lf_star : 0 ⧏ star := by
  rw [zero_lf]
  use default
  rintro ⟨⟩

theorem star_lf_zero : star ⧏ 0 := by
  rw [lf_zero]
  use default
  rintro ⟨⟩

theorem star_fuzzy_zero : star ‖ 0 :=
  ⟨star_lf_zero, zero_lf_star⟩

@[simp]
theorem neg_star : -star = star := by simp [star]

/-! ## Up and down -/

/-- The pre-game `up` -/
def up : PGame.{u} :=
  ⟨PUnit, PUnit, fun _ ↦ 0, fun _ ↦ star⟩

@[simp]
theorem up_leftMoves : up.LeftMoves = PUnit :=
  rfl

@[simp]
theorem up_rightMoves : up.RightMoves = PUnit :=
  rfl

@[simp]
theorem up_moveLeft (x) : up.moveLeft x = 0 :=
  rfl

@[simp]
theorem up_moveRight (x) : up.moveRight x = star :=
  rfl

@[simp]
theorem up_neg : 0 < up := by
  rw [lt_iff_le_and_lf, zero_lf]
  simp [zero_le_lf, zero_lf_star]

theorem star_fuzzy_up : star ‖ up := by
  unfold Fuzzy
  simp only [← PGame.not_le]
  simp [le_iff_forall_lf]

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

section TinyMiny

variable (x : PGame)

/-! ## Tiny and Miny -/

/-- A tiny game ⧾ is defined as {0 | {0 | -G}}, and is amongst the smallest of the infinitesimals. -/
def tiny : PGame :=
  ⟨PUnit, PUnit, fun _ ↦ 0, fun _ ↦ ⟨PUnit, PUnit, fun _ ↦ 0, fun _ ↦ -x⟩⟩

/-- A miny game ⧿ is defined as {{G | 0} | 0}. -/
def miny : PGame :=
  ⟨PUnit, PUnit, fun _ ↦ ⟨PUnit, PUnit, fun _ ↦ x, fun _ ↦ 0⟩, fun _ ↦ 0⟩

theorem tiny_neg_miny : miny x = -tiny x := by
  rw [miny, tiny]
  simp

/-- **Tiny is tiny**. The tiny games are among the smallest of the infinitesimals. -/
proof_wanted gt_tiny (x : PGame) (hx : 0 < x) : ∃ n : ℕ, tiny n < x

end TinyMiny

end PGame
