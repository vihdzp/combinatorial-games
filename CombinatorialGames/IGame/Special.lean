/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Tristan Figueroa Reid
-/
import CombinatorialGames.IGame.IGame
import CombinatorialGames.IGame.Short

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

/-- The game `⋆ = {{0} | {0}}ᴵ`, which is fuzzy with zero. -/
def star : IGame :=
  {{0} | {0}}ᴵ

@[inherit_doc] notation "⋆" => star

@[simp] theorem leftMoves_star : leftMoves ⋆ = {0} := leftMoves_ofSets ..
@[simp] theorem rightMoves_star : rightMoves ⋆ = {0} := rightMoves_ofSets ..

@[simp] theorem zero_lf_star : 0 ⧏ ⋆ := by rw [zero_lf]; simp
@[simp] theorem star_lf_zero : ⋆ ⧏ 0 := by rw [lf_zero]; simp

theorem star_fuzzy_zero : ⋆ ‖ 0 := not_compRel_iff.2 ⟨zero_lf_star, star_lf_zero⟩
theorem zero_fuzzy_star : 0 ‖ ⋆ := not_compRel_iff.2 ⟨star_lf_zero, zero_lf_star⟩

@[simp] theorem neg_star : -star = star := by simp [star]

/-! ### Up and down -/

/-- The game `↑ = {0 | ⋆}`. -/
def up : IGame :=
  {{0} | {⋆}}ᴵ

@[inherit_doc] notation "↑" => up

@[simp] theorem leftMoves_up : leftMoves ↑ = {0} := leftMoves_ofSets ..
@[simp] theorem rightMoves_up : rightMoves ↑ = {⋆} := rightMoves_ofSets ..

@[simp]
theorem up_pos : 0 < ↑ := by
  rw [lt_iff_le_not_le, zero_lf, zero_le]
  simp

theorem up_fuzzy_star : ↑ ‖ ⋆ := by
  simp [CompRel]
  rw [le_iff_forall_lf, le_iff_forall_lf]
  simpa using up_pos.le

theorem star_fuzzy_up : ⋆ ‖ ↑ := by
  rw [compRel_comm]
  exact up_fuzzy_star

/-- The game `↓ = {⋆ | 0}`. -/
def down : IGame :=
  {{⋆} | {0}}ᴵ

@[inherit_doc] notation "↓" => down

@[simp] theorem leftMoves_down : leftMoves ↓ = {⋆} := leftMoves_ofSets ..
@[simp] theorem rightMoves_down : rightMoves ↓ = {0} := rightMoves_ofSets ..

@[simp] theorem neg_down : -↓ = ↑ := by simp [up, down]
@[simp] theorem neg_up : -↑ = ↓ := by simp [up, down]

@[simp]
theorem down_neg : ↓ < 0 := by
  rw [← zero_lt_neg, neg_down]
  exact up_pos

theorem down_fuzzy_star : ↓ ‖ ⋆ := by
  rw [← neg_fuzzy_neg_iff, neg_down, neg_star]
  exact up_fuzzy_star

theorem star_fuzzy_down : ⋆ ‖ ↓ := by
  rw [compRel_comm]
  exact down_fuzzy_star

/-! ### Tiny and miny -/

/-- A tiny game `⧾x` is defined as `{0 | {0 | -x}}`, and is amongst the smallest of the
infinitesimals. -/
def tiny (x : IGame) : IGame :=
  {{0} | {{{0} | {-x}}ᴵ}}ᴵ

@[inherit_doc] prefix:75 "⧾" => tiny

@[simp]
theorem leftMoves_tiny (x : IGame) : leftMoves (⧾x) = {0} :=
  leftMoves_ofSets ..

@[simp]
theorem rightMoves_tiny (x : IGame) : rightMoves (⧾x) = {{{0} | {-x}}ᴵ} :=
  rightMoves_ofSets ..

/-- A miny game `⧿x` is defined as `{{x | 0} | 0}`. -/
def miny (x : IGame) : IGame :=
  {{{{x} | {0}}ᴵ} | {0}}ᴵ

@[inherit_doc] prefix:75 "⧿" => miny

@[simp]
theorem leftMoves_miny (x : IGame) : leftMoves (⧿x) = {{{x} | {0}}ᴵ} :=
  leftMoves_ofSets ..

@[simp]
theorem rightMoves_miny (x : IGame) : rightMoves (⧿x) = {0} :=
  rightMoves_ofSets ..

@[simp]
theorem neg_tiny (x : IGame) : -(⧾x) = ⧿x := by
  simp [miny, tiny]

@[simp]
theorem neg_miny (x : IGame) : -(⧿x) = ⧾x := by
  simp [miny, tiny]

/-- **Tiny is tiny**. The tiny games are among the smallest of the infinitesimals. -/
proof_wanted exists_tiny_lt_of_pos {x : IGame} [Short x] (hx : 0 < x) : ∃ n : ℕ, ⧾n < x

end IGame
end
