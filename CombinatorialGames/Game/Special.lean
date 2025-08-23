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
  !{{0} | {0}}

@[inherit_doc] notation "⋆" => star
recommended_spelling "star" for "⋆" in [«term⋆»]

@[simp, game_cmp] theorem moves_left_star : moves_left ⋆ = {0} := moves_left_ofSets ..
@[simp, game_cmp] theorem moves_right_star : moves_right ⋆ = {0} := moves_right_ofSets ..

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
  !{{0} | {1}}

@[inherit_doc] notation "½" => half
recommended_spelling "half" for "½" in [«term½»]

@[simp, game_cmp] theorem moves_left_half : moves_left ½ = {0} := moves_left_ofSets ..
@[simp, game_cmp] theorem moves_right_half : moves_right ½ = {1} := moves_right_ofSets ..

theorem zero_lt_half : 0 < ½ := by game_cmp
theorem half_lt_one : ½ < 1 := by game_cmp
theorem half_add_half_equiv_one : ½ + ½ ≈ 1 := by game_cmp

instance : Short ½ := by rw [short_def]; simp

/-! ### Up and down -/

/-- The game `↑ = {0 | ⋆}`. -/
def up : IGame :=
  !{{0} | {⋆}}

@[inherit_doc] notation "↑" => up
recommended_spelling "up" for "↑" in [«term↑»]

@[simp, game_cmp] theorem moves_left_up : moves_left ↑ = {0} := moves_left_ofSets ..
@[simp, game_cmp] theorem moves_right_up : moves_right ↑ = {⋆} := moves_right_ofSets ..

@[simp] theorem up_pos : 0 < ↑ := by game_cmp
theorem up_fuzzy_star : ↑ ‖ ⋆ := by game_cmp
theorem star_fuzzy_up : ⋆ ‖ ↑ := up_fuzzy_star.symm

instance : Short ↑ := by rw [short_def]; simp

/-- The game `↓ = {⋆ | 0}`. -/
def down : IGame :=
  !{{⋆} | {0}}

@[inherit_doc] notation "↓" => down
recommended_spelling "down" for "↓" in [«term↓»]

@[simp, game_cmp] theorem moves_left_down : moves_left ↓ = {⋆} := moves_left_ofSets ..
@[simp, game_cmp] theorem moves_right_down : moves_right ↓ = {0} := moves_right_ofSets ..

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
  !{{0} | {!{{0} | {-x}}}}

@[inherit_doc] prefix:75 "⧾" => tiny
recommended_spelling "tiny" for "⧾" in [«term⧾_»]

@[simp, game_cmp]
theorem moves_left_tiny (x : IGame) : moves_left (⧾x) = {0} :=
  moves_left_ofSets ..

@[simp, game_cmp]
theorem moves_right_tiny (x : IGame) : moves_right (⧾x) = {!{{0} | {-x}}} :=
  moves_right_ofSets ..

instance (x : IGame) [Short x] : Short (⧾x) := by
  have : !{{0} | {-x}}.Short := by rw [short_def]; simpa
  rw [short_def]
  simpa

/-- A miny game `⧿x` is defined as `{{x | 0} | 0}`. -/
def miny (x : IGame) : IGame :=
  !{{!{{x} | {0}}} | {0}}

@[inherit_doc] prefix:75 "⧿" => miny
recommended_spelling "miny" for "⧿" in [«term⧿_»]

@[simp, game_cmp]
theorem moves_left_miny (x : IGame) : moves_left (⧿x) = {!{{x} | {0}}} :=
  moves_left_ofSets ..

@[simp, game_cmp]
theorem moves_right_miny (x : IGame) : moves_right (⧿x) = {0} :=
  moves_right_ofSets ..

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
  !{{x} | {-x}}

@[inherit_doc] prefix:75 "±" => switch
recommended_spelling "switch" for "±" in [«term±_»]

@[simp, game_cmp]
theorem moves_left_switch (x : IGame) : moves_left (±x) = {x} :=
  moves_left_ofSets ..

@[simp, game_cmp]
theorem moves_right_switch (x : IGame) : moves_right (±x) = {-x} :=
  moves_right_ofSets ..

@[simp]
theorem neg_switch (x : IGame) : -±x = ±x := by
  rw [switch, neg_ofSets]
  simp [Set.neg_singleton]

@[simp]
theorem switch_zero : ±0 = ⋆ := by
  simp_rw [switch, star, neg_zero]

end IGame
end
