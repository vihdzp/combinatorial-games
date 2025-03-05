/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Violeta Hernández Palacios
-/
import CombinatorialGames.IGame.Basic
import CombinatorialGames.IGame.Special
import CombinatorialGames.Mathlib.Comparable

/-!
# Basic definitions about impartial games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivalent to its negative,
no matter what moves are played. This allows for games such as poker-nim to be classified as
impartial.
-/

universe u

namespace IGame

private def ImpartialAux (x : IGame) : Prop :=
  -x ≈ x ∧ (∀ i ∈ x.leftMoves, ImpartialAux i) ∧ (∀ j ∈ x.rightMoves, ImpartialAux j)
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
protected theorem of_mem_leftMoves {x y : IGame} [h : Impartial x] :
    y ∈ x.leftMoves → Impartial y :=
  (impartial_def.1 h).2.1 y

@[aesop unsafe 50% apply]
protected theorem of_mem_rightMoves {x y : IGame} [h : Impartial x] :
    y ∈ x.rightMoves → Impartial y :=
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
    try have := Impartial.of_mem_leftMoves hy
    try have := Impartial.of_mem_rightMoves hy
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
    · try have := Impartial.of_mem_leftMoves hz
      try have := Impartial.of_mem_rightMoves hz
      exact .add ..
termination_by (x, y)
decreasing_by igame_wf

theorem le_comm {x y} [Impartial x] [Impartial y] : x ≤ y ↔ y ≤ x := by
  rw [← IGame.neg_le_neg_iff, (neg_equiv y).le_congr (neg_equiv x)]

@[simp]
theorem not_lt : ¬x < y := by
  apply (lt_asymm · ?_)
  rwa [← IGame.neg_lt_neg_iff, (neg_equiv x).lt_congr (neg_equiv y)]

/-- By setting `y = 0`, we find that in an impartial game, either the first player always wins, or
the second player always wins. -/
theorem equiv_or_fuzzy : x ≈ y ∨ x ‖ y := by
  obtain (h | h | h | h) := lt_or_antisymmRel_or_gt_or_incompRel x y
  · cases not_lt x y h
  · exact .inl h
  · cases not_lt y x h
  · exact .inr h

/-- This lemma doesn't require `x` to be impartial. -/
theorem equiv_iff_add_equiv_zero (x : IGame) : x ≈ y ↔ x + y ≈ 0 := by
  rw [← Game.mk_eq_mk, ← Game.mk_eq_mk, Game.mk_add, Game.mk_zero, add_eq_zero_iff_eq_neg, neg_mk]

/-- This lemma doesn't require `y` to be impartial. -/
theorem equiv_iff_add_equiv_zero' (y : IGame) : x ≈ y ↔ x + y ≈ 0 := by
  rw [antisymmRel_comm, add_comm, equiv_iff_add_equiv_zero]

variable {x y}

@[simp]
theorem not_equiv_iff : ¬ x ≈ y ↔ x ‖ y :=
   ⟨(equiv_or_fuzzy x y).resolve_left, IncompRel.not_antisymmRel⟩

@[simp]
theorem not_fuzzy_iff : ¬ x ‖ y ↔ x ≈ y :=
  not_iff_comm.1 not_equiv_iff

@[simp]
theorem le_iff_equiv : x ≤ y ↔ x ≈ y :=
  ⟨fun h ↦ ⟨h, le_comm.1 h⟩, And.left⟩

theorem ge_iff_equiv : y ≤ x ↔ x ≈ y :=
  ⟨fun h ↦ ⟨le_comm.2 h, h⟩, And.right⟩

theorem lf_iff_fuzzy : x ⧏ y ↔ x ‖ y := by simp [comm]
theorem gf_iff_fuzzy : y ⧏ x ↔ x ‖ y := by simp

theorem equiv_zero_iff_forall_leftMoves_fuzzy : x ≈ 0 ↔ ∀ y ∈ x.leftMoves, y ‖ 0 := by
  rw [← le_iff_equiv, le_zero]
  congr! 2 with a ha
  have := Impartial.of_mem_leftMoves ha
  rw [ge_iff_equiv, not_equiv_iff]

theorem equiv_zero_iff_forall_rightMoves_fuzzy : x ≈ 0 ↔ ∀ y ∈ x.rightMoves, y ‖ 0 := by
  rw [← neg_equiv_zero, equiv_zero_iff_forall_leftMoves_fuzzy, exists_rightMoves_neg]
  simp

theorem fuzzy_zero_iff_exists_leftMoves_equiv : x ‖ 0 ↔ ∃ y ∈ x.leftMoves, y ≈ 0 := by
  rw [← gf_iff_fuzzy, zero_lf]
  congr! 2
  rw [and_congr_right_iff]
  intro ha
  have := Impartial.of_mem_leftMoves ha
  exact ge_iff_equiv

theorem fuzzy_zero_iff_exists_rightMoves_equiv : x ‖ 0 ↔ ∃ y ∈ x.rightMoves, y ≈ 0 := by
  rw [← neg_fuzzy_zero, fuzzy_zero_iff_exists_leftMoves_equiv, exists_leftMoves_neg]
  simp

#exit
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
