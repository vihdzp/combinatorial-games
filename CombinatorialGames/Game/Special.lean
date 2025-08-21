/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Tristan Figueroa Reid
-/
import CombinatorialGames.Game.Short
import CombinatorialGames.Tactic.GameCmp

/-!
# Special games

This file defines some simple yet notable combinatorial games:

* `⋆ = {0 | 0}`
* `↑ = {0 | ⋆}`
* `↓ = {⋆ | 0}`.
-/

universe u

noncomputable section

namespace IGame

/-! ### Star -/

/-- The game `⋆ = {0 | 0}`, which is fuzzy with zero. -/
def star : IGame :=
  {{0} | {0}}ᴵ

@[inherit_doc] notation "⋆" => star
recommended_spelling "star" for "⋆" in [«term⋆»]

@[simp, game_cmp] theorem leftMoves_star : leftMoves ⋆ = {0} := leftMoves_ofSets ..
@[simp, game_cmp] theorem rightMoves_star : rightMoves ⋆ = {0} := rightMoves_ofSets ..

@[simp] theorem zero_lf_star : 0 ⧏ ⋆ := by rw [zero_lf]; simp
@[simp] theorem star_lf_zero : ⋆ ⧏ 0 := by rw [lf_zero]; simp

theorem star_fuzzy_zero : ⋆ ‖ 0 := ⟨zero_lf_star, star_lf_zero⟩
theorem zero_fuzzy_star : 0 ‖ ⋆ := ⟨star_lf_zero, zero_lf_star⟩

@[simp, game_cmp] theorem neg_star : -⋆ = ⋆ := by simp [star]

@[simp] theorem star_mul_star : ⋆ * ⋆ = ⋆ := by ext p; cases p <;> simp [mulOption]

@[simp] instance : Short ⋆ := by rw [short_def]; simp

/-! ### Half -/

/-- The game `½ = {0 | 1}`, which we prove satisfies `½ + ½ = 1`. -/
def half : IGame :=
  {{0} | {1}}ᴵ

@[inherit_doc] notation "½" => half
recommended_spelling "half" for "½" in [«term½»]

@[simp, game_cmp] theorem leftMoves_half : leftMoves ½ = {0} := leftMoves_ofSets ..
@[simp, game_cmp] theorem rightMoves_half : rightMoves ½ = {1} := rightMoves_ofSets ..

theorem zero_lt_half : 0 < ½ := by game_cmp
theorem half_lt_one : ½ < 1 := by game_cmp
theorem half_add_half_equiv_one : ½ + ½ ≈ 1 := by game_cmp

instance : Short ½ := by rw [short_def]; simp

/-! ### Up and down -/

/-- The game `↑ = {0 | ⋆}`. -/
def up : IGame :=
  {{0} | {⋆}}ᴵ

@[inherit_doc] notation "↑" => up
recommended_spelling "up" for "↑" in [«term↑»]

@[simp, game_cmp] theorem leftMoves_up : leftMoves ↑ = {0} := leftMoves_ofSets ..
@[simp, game_cmp] theorem rightMoves_up : rightMoves ↑ = {⋆} := rightMoves_ofSets ..

@[simp] theorem up_pos : 0 < ↑ := by game_cmp
theorem up_fuzzy_star : ↑ ‖ ⋆ := by game_cmp
theorem star_fuzzy_up : ⋆ ‖ ↑ := up_fuzzy_star.symm

instance : Short ↑ := by rw [short_def]; simp

/-- The game `↓ = {⋆ | 0}`. -/
def down : IGame :=
  {{⋆} | {0}}ᴵ

@[inherit_doc] notation "↓" => down
recommended_spelling "down" for "↓" in [«term↓»]

@[simp, game_cmp] theorem leftMoves_down : leftMoves ↓ = {⋆} := leftMoves_ofSets ..
@[simp, game_cmp] theorem rightMoves_down : rightMoves ↓ = {0} := rightMoves_ofSets ..

@[simp, game_cmp] theorem neg_down : -↓ = ↑ := by simp [up, down]
@[simp, game_cmp] theorem neg_up : -↑ = ↓ := by simp [up, down]

@[simp] theorem down_neg : ↓ < 0 := by game_cmp
theorem down_fuzzy_star : ↓ ‖ ⋆ := by game_cmp
theorem star_fuzzy_down : ⋆ ‖ ↓ := down_fuzzy_star.symm

instance : Short ↓ := by rw [short_def]; simp

/-! ### Tiny and miny -/

/-- A tiny game `⧾x` is defined as `{0 | {0 | -x}}`, and is amongst the smallest of the
infinitesimals. -/
def tiny (x : IGame) : IGame :=
  {{0} | {{{0} | {-x}}ᴵ}}ᴵ

@[inherit_doc] prefix:75 "⧾" => tiny
recommended_spelling "tiny" for "⧾" in [«term⧾_»]

@[simp, game_cmp]
theorem leftMoves_tiny (x : IGame) : leftMoves (⧾x) = {0} :=
  leftMoves_ofSets ..

@[simp, game_cmp]
theorem rightMoves_tiny (x : IGame) : rightMoves (⧾x) = {{{0} | {-x}}ᴵ} :=
  rightMoves_ofSets ..

instance (x : IGame) [Short x] : Short (⧾x) := by
  have : {{0} | {-x}}ᴵ.Short := by rw [short_def]; simpa
  rw [short_def]
  simpa

/-- A miny game `⧿x` is defined as `{{x | 0} | 0}`. -/
def miny (x : IGame) : IGame :=
  {{{{x} | {0}}ᴵ} | {0}}ᴵ

@[inherit_doc] prefix:75 "⧿" => miny
recommended_spelling "miny" for "⧿" in [«term⧿_»]

@[simp, game_cmp]
theorem leftMoves_miny (x : IGame) : leftMoves (⧿x) = {{{x} | {0}}ᴵ} :=
  leftMoves_ofSets ..

@[simp, game_cmp]
theorem rightMoves_miny (x : IGame) : rightMoves (⧿x) = {0} :=
  rightMoves_ofSets ..

@[simp, game_cmp]
theorem neg_tiny (x : IGame) : -(⧾x) = ⧿x := by
  simp [miny, tiny]

@[simp, game_cmp]
theorem neg_miny (x : IGame) : -(⧿x) = ⧾x := by
  simp [miny, tiny]

instance (x : IGame) [Short x] : Short (⧿x) := by
  rw [← neg_tiny]; infer_instance

@[simp, game_cmp] theorem tiny_pos (x : IGame) : 0 < ⧾x := by game_cmp
@[simp, game_cmp] theorem miny_neg (x : IGame) : ⧿x < 0 := by game_cmp

/-! ### Switches -/

/-- A **switch** `±x` is defined as `{x | -x}`: switches are their own confusion interval! -/
def switch (x : IGame) : IGame :=
  {{x} | {-x}}ᴵ

@[inherit_doc] prefix:75 "±" => switch
recommended_spelling "switch" for "±" in [«term±_»]

@[simp, game_cmp]
theorem leftMoves_switch (x : IGame) : leftMoves (±x) = {x} :=
  leftMoves_ofSets ..

@[simp, game_cmp]
theorem rightMoves_switch (x : IGame) : rightMoves (±x) = {-x} :=
  rightMoves_ofSets ..

@[simp]
theorem neg_switch (x : IGame) : -±x = ±x := by
  rw [switch, neg_ofSets]
  simp [Set.neg_singleton]

@[simp]
theorem switch_zero : ±0 = ⋆ := by
  simp_rw [switch, star, neg_zero]

end IGame
end
