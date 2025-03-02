/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Violeta Hernández Palacios
-/
import CombinatorialGames.IGame.Basic
import CombinatorialGames.IGame.Special
import CombinatorialGames.Mathlib.AntisymmRel

/-!
# Basic definitions about impartial games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivalent to its negative,
no matter what moves are played. This allows for games such as poker-nim to be classified as
impartial.
-/

universe u

-- TODO: remove Temp namespace
namespace Temp

namespace IGame

private def ImpartialAux (x : IGame) : Prop :=
  x ≈ -x ∧ (∀ i ∈ x.leftMoves, ImpartialAux i) ∧ (∀ j ∈ x.rightMoves, ImpartialAux j)
termination_by x
decreasing_by igame_wf

/-- An impartial game is one that's equivalent to its negative, such that each left and right move
is also impartial.

Note that this is a slightly more general definition than the one that's usually in the literature,
as we don't require `x = -x`. Despite this, the Sprague-Grundy theorem still holds: see
`IGame.equiv_nim_grundyValue`.

In such a game, both players have the same payoffs at any subposition. -/
@[mk_iff impartial_iff_aux]
class Impartial (x : IGame) : Prop where
  out : ImpartialAux x

theorem impartial_def {x : IGame} :
    x.Impartial ↔ -x ≈ x ∧ (∀ i ∈ x.leftMoves, Impartial i) ∧ ∀ j ∈ x.rightMoves, Impartial j := by
  simp_rw [impartial_iff_aux]
  rw [ImpartialAux]

namespace Impartial
variable (x y : IGame) [hx : Impartial x] [hy : Impartial y]

theorem mk' {x : IGame} (h₁ : -x ≈ x)
    (h₂ : ∀ i ∈ x.leftMoves, Impartial i) (h₃ : ∀ j ∈ x.rightMoves, Impartial j) : Impartial x :=
  impartial_def.2 ⟨h₁, h₂, h₃⟩

@[simp] theorem neg_equiv : -x ≈ x := (impartial_def.1 hx).1
@[simp] theorem equiv_neg : x ≈ -x := (neg_equiv _).symm

@[simp]
theorem neg_mk : -Game.mk x = Game.mk x :=
  Game.mk_eq (equiv_neg x).symm

@[simp]
theorem mk_add_self : Game.mk x + Game.mk x = 0 := by
  rw [add_eq_zero_iff_neg_eq, neg_mk]

theorem add_self_equiv (x : IGame) [Impartial x] : x + x ≈ 0 :=
  Game.mk_eq_mk.1 (mk_add_self x)

@[aesop unsafe 50% apply]
protected theorem leftMove {x y : IGame} [h : Impartial x] : y ∈ x.leftMoves → Impartial y :=
  (impartial_def.1 h).2.1 y

@[aesop unsafe 50% apply]
protected theorem rightMove {x y : IGame} [h : Impartial x] : y ∈ x.rightMoves → Impartial y :=
  (impartial_def.1 h).2.2 y

-- TODO: upstream
attribute [simp] AntisymmRel.refl

protected instance zero : Impartial 0 := by
  rw [impartial_def]
  simp

protected instance star : Impartial ⋆ := by
  rw [impartial_def]
  simp [Impartial.zero]

protected instance neg (x : IGame) [Impartial x] : Impartial (-x) := by
  apply mk'
  · simp
  on_goal 1 => rw [leftMoves_neg]
  on_goal 2 => rw [rightMoves_neg]
  all_goals
  · intro y hy
    try have := Impartial.leftMove hy
    try have := Impartial.rightMove hy
    rw [← neg_neg y]
    exact .neg _
termination_by x
decreasing_by igame_wf

protected instance add (x y : IGame) [Impartial x] [Impartial y] : Impartial (x + y) := by
  apply mk'
  · rw [neg_add]
    exact add_congr (neg_equiv x) (neg_equiv y)
  on_goal 1 => rw [leftMoves_add]
  on_goal 2 => rw [rightMoves_add]
  all_goals
  · rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) <;>
    · try have := Impartial.leftMove hz
      try have := Impartial.rightMove hz
      exact .add ..
termination_by (x, y)
decreasing_by igame_wf

theorem nonpos : ¬0 < x := by
  apply (lt_asymm · ?_)
  rwa [← IGame.neg_lt_neg_iff, neg_zero, (neg_equiv x).lt_congr_right]

theorem nonneg : ¬x < 0 := by
  simpa using nonpos (-x)

/-- In an impartial game, either the first player always wins, or the second player always wins. -/
theorem equiv_or_fuzzy_zero : x ≈ 0 ∨ x ‖ 0 := by
  obtain (h | h | h | h) := lt_or_antisymmRel_or_gt_or_not_compRel x 0
  · cases nonneg x h
  · exact .inl h
  · cases nonpos x h
  · exact .inr h

/-- This lemma doesn't require `x` to be impartial. -/
theorem equiv_iff_add_equiv_zero (x : IGame) : x ≈ y ↔ x + y ≈ 0 := by
  rw [← Game.mk_eq_mk, ← Game.mk_eq_mk, Game.mk_add, Game.mk_zero, add_eq_zero_iff_eq_neg, neg_mk]

/-- This lemma doesn't require `y` to be impartial. -/
theorem equiv_iff_add_equiv_zero' (y : IGame) : x ≈ y ↔ x + y ≈ 0 := by
  rw [antisymmRel_comm, add_comm, equiv_iff_add_equiv_zero]

variable {x y}

-- TODO: We should be using `IncompRel` instead of `CompRel`.
-- TODO: These theorems should not be specific to `0`.

@[simp]
theorem compRel_zero_iff : CompRel (· ≤ ·) x 0 ↔ x ≈ 0 :=
  ⟨not_imp_not.1 (equiv_or_fuzzy_zero x).resolve_left, AntisymmRel.compRel⟩

@[simp]
theorem zero_compRel_iff : CompRel (· ≤ ·) 0 x ↔ 0 ≈ x := by
  rw [compRel_comm, antisymmRel_comm, compRel_zero_iff]

theorem not_equiv_zero_iff : ¬ x ≈ 0 ↔ x ‖ 0 := by simp
theorem not_fuzzy_zero_iff : ¬ x ‖ 0 ↔ x ≈ 0 := by simp

theorem le_zero_comm : x ≤ 0 ↔ 0 ≤ x := by
  rw [← zero_le_neg, (neg_equiv x).le_congr_right]

@[simp]
theorem le_zero_iff_equiv : x ≤ 0 ↔ x ≈ 0 :=
  ⟨fun h ↦ ⟨h, le_zero_comm.1 h⟩, And.left⟩

@[simp]
theorem zero_le_iff_equiv : 0 ≤ x ↔ x ≈ 0 :=
  ⟨fun h ↦ ⟨le_zero_comm.2 h, h⟩, And.right⟩

theorem lf_zero_iff_fuzzy : x ⧏ 0 ↔ x ‖ 0 := by simp
theorem zero_lf_iff_fuzzy : 0 ⧏ x ↔ x ‖ 0 := by simp

#exit

theorem equiv_zero_iff_forall_leftMoves_fuzzy : x ≈ 0 ↔ ∀ i ∈ x.leftMoves, i ‖ 0 := by
  simpa using le_zero (x := x)

theorem equiv_zero_iff_forall_rightMoves_fuzzy : G ≈ 0 ↔ ∀ j ∈ G.rightMoves, j ‖ 0 := by
  simpa using zero_le (x := x)

theorem fuzzy_zero_iff_exists_leftMoves_equiv : G ‖ 0 ↔ ∃ i ∈ G.leftMoves, i ≈ 0 := by
  simpa using zero_lf (x := G)

theorem fuzzy_zero_iff_exists_rightMoves_equiv : G ‖ 0 ↔ ∃ j ∈ G.rightMoves, j ≈ 0 := by
  simpa using lf_zero (x := G)

/-- A **strategy stealing** argument. If there's a move in `G`, such that any subsequent move could
have also been reached in the first turn, then `G` is won by the first player.

This version of the theorem is stated exclusively in terms of left moves; see
`fuzzy_zero_of_forall_exists_moveRight` for a version stated with right moves. -/
theorem fuzzy_zero_of_forall_exists_moveLeft (i : G.leftMoves)
    (H : ∀ j ∈ (i : IGame).leftMoves, ∃ k ∈ G.leftMoves, j ≈ k) : G ‖ 0 := by
  apply (equiv_or_fuzzy_zero _).resolve_left fun hG ↦ ?_
  rw [equiv_zero_iff_forall_leftMoves_fuzzy] at hG
  obtain ⟨j, hj⟩ := fuzzy_zero_iff_exists_leftMoves_equiv.1 (hG i.1 i.2)
  obtain ⟨k, hk⟩ := H j hj.1
  exact (hG k hk.1).not_equiv (hk.symm.trans hj)

/-- A **strategy stealing** argument. If there's a move in `G`, such that any subsequent move could
have also been reached in the first turn, then `G` is won by the first player.

This version of the theorem is stated exclusively in terms of right moves; see
`fuzzy_zero_of_forall_exists_moveLeft` for a version stated with left moves. -/
theorem fuzzy_zero_of_forall_exists_moveRight (i : G.rightMoves)
    (H : ∀ j ∈ (i : IGame).rightMoves, ∃ k ∈ G.rightMoves, j ≈ k) : G ‖ 0 := by
  rw [← neg_fuzzy_zero_iff]
  apply fuzzy_zero_of_forall_exists_moveLeft (toLeftMovesNeg i)
  rw [moveLeft_neg_toLeftMovesNeg]
  simpa

end Impartial
end IGame
