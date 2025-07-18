/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel, Violeta Hernández Palacios
-/
import CombinatorialGames.Specific.Nim

/-!
# Grundy value

We define the Grundy value for an impartial game `x` and prove the Sprague-Grundy theorem, which
states that `x` is equivalent to `nim (grundy x)`. We prove that the grundy value of a sum `x + y`
corresponds to the nimber sum of the individual grundy values.
-/

namespace Impartial

/-- The Grundy value of an impartial game is recursively defined as the minimum excluded value
(the infimum of the complement) of the Grundy values of either its left or right options.

This is the nimber which corresponds to the game of nim that the game is equivalent to. -/
noncomputable def grundy (x : IGame.{u}) : Nimber.{u} :=
  sInf (Set.range fun y : x.leftMoves ↦ grundy y.1)ᶜ
termination_by x
decreasing_by igame_wf

/-- This version is stated in terms of left moves of `x`. -/
theorem grundy_def (x : IGame) : grundy x = sInf (grundy '' x.leftMoves)ᶜ := by
  rw [grundy, image_eq_range]

/-- This version is stated in terms of left moves of `x`. -/
theorem le_grundy_iff {x : IGame} {o : Nimber} : o ≤ grundy x ↔ Iio o ⊆ grundy '' x.leftMoves := by
  rw [grundy_def, le_csInf_iff'']
  · rw [← compl_subset_compl (t := Iio o), subset_def]
    simp
  · exact nonempty_of_not_bddAbove (Nimber.not_bddAbove_compl_of_small _)

/-- This version is stated in terms of left moves of `x`. -/
theorem lt_grundy_iff {x : IGame} {o : Nimber} : o < grundy x ↔ Iic o ⊆ grundy '' x.leftMoves := by
  simpa using le_grundy_iff (o := Order.succ o)

/-- This version is stated in terms of left moves of `x`. -/
theorem mem_grundy_image_of_lt {x : IGame} {o : Nimber} (h : o < grundy x) :
    o ∈ grundy '' x.leftMoves :=
  le_grundy_iff.1 le_rfl h

/-- This version is stated in terms of left moves of `x`. -/
theorem grundy_ne {x y : IGame} (hy : y ∈ x.leftMoves) : grundy y ≠ grundy x := by
  conv_rhs => rw [grundy_def]
  have := csInf_mem (nonempty_of_not_bddAbove <|
    Nimber.not_bddAbove_compl_of_small (grundy '' x.leftMoves))
  simp_rw [mem_compl_iff, mem_image, not_exists, not_and] at this
  exact this y hy

/-- The **Sprague-Grundy theorem** states that every impartial game is equivalent to a game of nim,
namely the game of nim for the game's Grundy value. -/
theorem equiv_nim_grundy (x : IGame) [Impartial x] : x ≈ nim (grundy x) := by
  rw [equiv_iff_forall_fuzzy]
  constructor <;> intro y hy
  · have := Impartial.of_mem_leftMoves hy
    rw [(equiv_nim_grundy _).incompRel_congr_left, nim_fuzzy_iff]
    exact grundy_ne hy
  · rw [rightMoves_nim] at hy
    obtain ⟨o, ho, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := mem_grundy_image_of_lt ho
    have := Impartial.of_mem_leftMoves hz
    rw [← (equiv_nim_grundy _).incompRel_congr_right]
    exact fuzzy_leftMove hz
termination_by x
decreasing_by igame_wf

theorem grundy_eq_iff_equiv_nim {x : IGame} [Impartial x] {o : Nimber} :
    grundy x = o ↔ x ≈ nim o := by
  rw [(Impartial.equiv_nim_grundy x).antisymmRel_congr_left, nim_equiv_iff]

theorem grundy_eq_zero_iff {x : IGame} [Impartial x] : grundy x = 0 ↔ x ≈ 0 := by
  simpa using grundy_eq_iff_equiv_nim (o := 0)

@[simp]
theorem grundy_eq_iff_equiv {x y : IGame} [Impartial x] [Impartial y] :
    grundy x = grundy y ↔ x ≈ y := by
  rw [grundy_eq_iff_equiv_nim, ← (equiv_nim_grundy _).antisymmRel_congr_right]

@[simp] theorem grundy_nim (o : Nimber) : grundy (nim o) = o := grundy_eq_iff_equiv_nim.2 .rfl
@[simp] theorem grundy_zero : grundy 0 = 0 := by simpa using grundy_nim 0
@[simp] theorem grundy_star : grundy ⋆ = 1 := by simpa using grundy_nim 1

@[simp]
theorem grundy_neg (x : IGame) [Impartial x] : grundy (-x) = grundy x := by
  rw [grundy_eq_iff_equiv_nim, ← neg_nim, IGame.neg_equiv_neg_iff, ← grundy_eq_iff_equiv_nim]

@[simp]
theorem grundy_add (x y : IGame) [Impartial x] [Impartial y] :
    grundy (x + y) = grundy x + grundy y := by
  rw [grundy_eq_iff_equiv_nim, ← (nim_add_equiv _ _).antisymmRel_congr_right]
  exact add_congr (equiv_nim_grundy x) (equiv_nim_grundy y)

private theorem grundy_image_neg_rightMoves (x : IGame) [Impartial x] :
    grundy '' (-x.rightMoves) = grundy '' x.rightMoves := by
  rw [← Set.image_neg_eq_neg, image_image]
  congr! 1 with y hy
  have := Impartial.of_mem_rightMoves hy
  rw [grundy_neg]

/-- This version is stated in terms of right moves of `x`. -/
theorem grundy_def' (x : IGame) [Impartial x] : grundy x = sInf (grundy '' x.rightMoves)ᶜ := by
  rw [← grundy_image_neg_rightMoves]
  simpa using grundy_def (-x)

/-- This version is stated in terms of right moves of `x`. -/
theorem le_grundy_iff' {x : IGame} [Impartial x] {o : Nimber} :
    o ≤ grundy x ↔ Iio o ⊆ grundy '' x.rightMoves := by
  rw [← grundy_image_neg_rightMoves]
  simpa using le_grundy_iff (x := -x)

/-- This version is stated in terms of right moves of `x`. -/
theorem lt_grundy_iff' {x : IGame} [Impartial x] {o : Nimber} :
    o < grundy x ↔ Iic o ⊆ grundy '' x.rightMoves := by
  simpa using le_grundy_iff' (o := Order.succ o)

/-- This version is stated in terms of right moves of `x`. -/
theorem mem_grundy_image_of_lt' {x : IGame} [Impartial x] {o : Nimber} (h : o < grundy x) :
    o ∈ grundy '' x.rightMoves :=
  le_grundy_iff'.1 le_rfl h

/-- This version is stated in terms of right moves of `x`. -/
theorem grundy_ne' {x y : IGame} [Impartial x] (hy : y ∈ x.rightMoves) : grundy y ≠ grundy x := by
  have hy' : -y ∈ (-x).leftMoves := by simpa
  have := Impartial.of_mem_rightMoves hy
  simpa using grundy_ne hy'

end Impartial
