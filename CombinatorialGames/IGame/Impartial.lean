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

private def ImpartialAux (G : IGame) : Prop :=
  G ≈ -G ∧ (∀ i ∈ G.leftMoves, ImpartialAux i) ∧ (∀ j ∈ G.rightMoves, ImpartialAux j)
termination_by G
decreasing_by igame_wf

/-- An impartial game is one that's equivalent to its negative, such that each left and right move
is also impartial.

Note that this is a slightly more general definition than the one that's usually in the literature,
as we don't require `G ≡ -G`. Despite this, the Sprague-Grundy theorem still holds: see
`IGame.equiv_nim_grundyValue`.

In such a game, both players have the same payoffs at any subposition. -/
class Impartial (G : IGame) : Prop where
  out : ImpartialAux G

private theorem impartial_iff_aux {G : IGame} : G.Impartial ↔ G.ImpartialAux :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

theorem impartial_def {G : IGame} :
    G.Impartial ↔ G ≈ -G ∧ (∀ i ∈ G.leftMoves, Impartial i) ∧ ∀ j ∈ G.rightMoves, Impartial j := by
  simp_rw [impartial_iff_aux]
  rw [ImpartialAux]

namespace Impartial

variable (G : IGame) [h : Impartial G]

instance impartial_zero : Impartial 0 := by
  rw [impartial_def]
  simp
  rfl

instance impartial_star : Impartial star := by
  rw [impartial_def]
  simp [Impartial.impartial_zero]
  rfl

theorem neg_equiv_self : G ≈ -G :=
  (impartial_def.1 h).1

@[simp]
theorem mk'_neg_equiv_self : -(Game.mk G) = (Game.mk G) :=
  Game.mk_eq (neg_equiv_self G).symm

instance moveLeft_impartial {G : IGame} [h : G.Impartial] (i : G.leftMoves) :
    Impartial i :=
  (impartial_def.1 h).2.1 i i.coe_prop

instance moveRight_impartial {G : IGame} [h : G.Impartial] (j : G.rightMoves) :
    Impartial j :=
  (impartial_def.1 h).2.2 j j.coe_prop

theorem impartial_congr {G H : IGame} (e : G = H) [G.Impartial] : H.Impartial :=
  impartial_def.2
    ⟨e.symm.equiv.trans ((neg_equiv_self G).trans (neg_equiv_neg_iff.2 e.equiv)),
      fun i ↦ (e.moveLeft_symm i).elim fun _ ↦ (impartial_congr ·),
      fun j ↦ (e.moveRight_symm j).elim fun _ ↦ (impartial_congr ·)⟩
termination_by (G, H)

instance impartial_add (G H : IGame) [G.Impartial] [H.Impartial] : (G + H).Impartial := by
  rw [impartial_def]
  refine ⟨(add_congr (neg_equiv_self G) (neg_equiv_self _)).trans
      (of_eq (G.neg_add H).symm), fun k ↦ ?_, fun k ↦ ?_⟩
  · apply leftMoves_add_cases k
    all_goals
      intro i; simp only [add_moveLeft_inl, add_moveLeft_inr]
      apply impartial_add
  · apply rightMoves_add_cases k
    all_goals
      intro i; simp only [add_moveRight_inl, add_moveRight_inr]
      apply impartial_add
termination_by (G, H)

instance impartial_neg (G : IGame) [G.Impartial] : (-G).Impartial := by
  rw [impartial_def]
  refine ⟨?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [neg_neg]
    exact (neg_equiv_self G).symm
  · rw [leftMoves_neg]
    exact impartial_neg _
  · rw [rightMoves_neg]
    exact impartial_neg _
termination_by G

theorem nonpos : ¬0 < G := by
  apply (lt_asymm · ?_)
  rwa [← IGame.neg_lt_neg_iff, neg_zero, ← (neg_equiv_self G).lt_congr_right]

theorem nonneg : ¬G < 0 := by
  simpa using nonpos (-G)

/-- In an impartial game, either the first player always wins, or the second player always wins. -/
theorem equiv_or_fuzzy_zero : G ≈ 0 ∨ G ‖ 0 := by
  rcases lt_or_equiv_or_gt_or_fuzzy G 0 with (h | h | h | h)
  · exact (nonneg G h).elim
  · exact Or.inl h
  · exact (nonpos G h).elim
  · exact Or.inr h

theorem add_self : G + G ≈ 0 :=
  (add_congr_left (neg_equiv_self G)).trans (neg_add_equiv G)

@[simp]
theorem mk'_add_self : (Game.mk G) + (.mk G) = 0 :=
  Game.mk_eq (add_self G)

/-- This lemma doesn't require `H` to be impartial. -/
theorem equiv_iff_add_equiv_zero (H : IGame) : H ≈ G ↔ H + G ≈ 0 := by
  -- rw [← Game.mk_eq_mk, ← Game.mk_eq_mk, ← add_right_cancel_iff (a := .mk G), mk'_add_self, ← quot_add,
  --   equiv_iff_game_eq, quot_zero]
  rw [← Game.mk_eq_mk, ← Game.mk_eq_mk, ← add_right_cancel_iff (a := .mk G),
    mk'_add_self, Game.mk_add]
  rfl

/-- This lemma doesn't require `H` to be impartial. -/
theorem equiv_iff_add_equiv_zero' (H : IGame) : G ≈ H ↔ G + H ≈ 0 := by
  rw [← Game.mk_eq_mk, ← Game.mk_eq_mk, ← add_left_cancel_iff, mk'_add_self,
    Game.mk_add, Game.mk_zero]
  aesop -- TODO: a + b = 0 ↔ 0 = a + b

variable {G}

@[simp]
theorem not_equiv_zero_iff : ¬ G ≈ 0 ↔ G ‖ 0 :=
  ⟨(equiv_or_fuzzy_zero G).resolve_left, Fuzzy.not_equiv⟩

@[simp]
theorem not_fuzzy_zero_iff : ¬ G ‖ 0 ↔ G ≈ 0 :=
  ⟨(equiv_or_fuzzy_zero G).resolve_right, Equiv.not_fuzzy⟩

theorem le_zero_iff : G ≤ 0 ↔ 0 ≤ G := by
  rw [← zero_le_neg, (neg_equiv_self G).le_congr_right]

theorem lf_zero_iff : G ⧏ 0 ↔ 0 ⧏ G := by
  rw [← zero_lf_neg_iff, lf_congr_right (neg_equiv_self G)]

@[simp]
theorem le_zero_iff_equiv : G ≤ 0 ↔ G ≈ 0 :=
  ⟨fun h ↦ ⟨h, le_zero_iff.1 h⟩, And.left⟩

@[simp]
theorem zero_le_iff_equiv : 0 ≤ G ↔ G ≈ 0 :=
  ⟨fun h ↦ ⟨le_zero_iff.2 h, h⟩, And.right⟩

@[simp]
theorem lf_zero_iff_fuzzy : G ⧏ 0 ↔ G ‖ 0 :=
  ⟨fun h ↦ ⟨h, lf_zero_iff.1 h⟩, And.left⟩

@[simp]
theorem zero_lf_iff_fuzzy : 0 ⧏ G ↔ G ‖ 0 :=
  ⟨fun h ↦ ⟨lf_zero_iff.2 h, h⟩, And.right⟩

theorem equiv_zero_iff_forall_leftMoves_fuzzy : G ≈ 0 ↔ ∀ i ∈ G.leftMoves, i ‖ 0 := by
  simpa using le_zero (x := G)

theorem equiv_zero_iff_forall_rightMoves_fuzzy : G ≈ 0 ↔ ∀ j ∈ G.rightMoves, j ‖ 0 := by
  simpa using zero_le (x := G)

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
