/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Birthday
import CombinatorialGames.Game.Impartial
import CombinatorialGames.Nimber.Basic

/-!
# Nim and the Sprague-Grundy theorem

In the game of `nim o`, for `o` an ordinal number, both players may move to `nim a` for any `a < o`.

We also define a Grundy value for an impartial game `x` and prove the Sprague-Grundy theorem, that
`x` is equivalent to `nim (grundy x)`. Finally, we prove that the grundy value of a sum `x + y`
corresponds to the nimber sum of the individual grundy values.
-/

universe u

open Nimber Set

noncomputable section

theorem Nimber.Iio_toNimber (n : ℕ) : Iio (∗n) = Ordinal.toNimber '' Iio n := by aesop

namespace IGame

/-! ### Nim game -/

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
take a positive number of stones from it on their turn. -/
noncomputable def nim (o : Nimber.{u}) : IGame.{u} :=
  {.range fun (⟨x, _⟩ : Iio o) ↦ nim x | .range fun (⟨x, _⟩ : Iio o) ↦ nim x}ᴵ
termination_by o

theorem nim_def (o : Nimber) : nim o = {nim '' Iio o | nim '' Iio o}ᴵ := by
  rw [nim]; simp [image_eq_range]

@[simp]
theorem leftMoves_nim (o : Nimber) : (nim o).leftMoves = nim '' Iio o := by
  rw [nim_def]; exact leftMoves_ofSets ..

@[simp]
theorem rightMoves_nim (o : Nimber) : (nim o).rightMoves = nim '' Iio o := by
  rw [nim_def]; exact rightMoves_ofSets ..

theorem forall_leftMoves_nim {P : IGame → Prop} {o : Nimber} :
    (∀ x ∈ (nim o).leftMoves, P x) ↔ (∀ a < o, P (nim a)) := by
  simp

theorem forall_rightMoves_nim {P : IGame → Prop} {o : Nimber} :
    (∀ x ∈ (nim o).rightMoves, P x) ↔ (∀ a < o, P (nim a)) := by
  simp

theorem exists_leftMoves_nim {P : IGame → Prop} {o : Nimber} :
    (∃ x ∈ (nim o).leftMoves, P x) ↔ (∃ a < o, P (nim a)) := by
  simp

theorem exists_rightMoves_nim {P : IGame → Prop} {o : Nimber} :
    (∃ x ∈ (nim o).rightMoves, P x) ↔ (∃ a < o, P (nim a)) := by
  simp

@[game_cmp]
theorem forall_leftMoves_nim_natCast {P : IGame → Prop} {n : ℕ} :
    (∀ x ∈ leftMoves (nim (∗n)), P x) ↔ ∀ m < n, P (nim (∗m)) := by
  rw [leftMoves_nim, Nimber.Iio_toNimber, Ordinal.Iio_natCast]
  simp

@[game_cmp]
theorem forall_rightMoves_nim_natCast {P : IGame → Prop} {n : ℕ} :
    (∀ x ∈ rightMoves (nim (∗n)), P x) ↔ ∀ m < n, P (nim (∗m)) := by
  rw [rightMoves_nim, Nimber.Iio_toNimber, Ordinal.Iio_natCast]
  simp

@[game_cmp]
theorem exists_leftMoves_nim_natCast {P : IGame → Prop} {n : ℕ} :
    (∃ x ∈ leftMoves (nim (∗n)), P x) ↔ (∃ m < n, P (nim (∗m))) := by
  rw [leftMoves_nim, Nimber.Iio_toNimber, Ordinal.Iio_natCast]
  simp

@[game_cmp]
theorem exists_rightMoves_nim_natCast {P : IGame → Prop} {n : ℕ} :
    (∃ x ∈ rightMoves (nim (∗n)), P x) ↔ (∃ m < n, P (nim (∗m))) := by
  rw [rightMoves_nim, Nimber.Iio_toNimber, Ordinal.Iio_natCast]
  simp

@[game_cmp]
theorem forall_leftMoves_nim_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∀ x ∈ leftMoves (nim (∗ofNat(n))), P x) ↔ ∀ m < n, P (nim (∗m)) :=
  forall_leftMoves_nim_natCast

@[game_cmp]
theorem forall_rightMoves_nim_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∀ x ∈ rightMoves (nim (∗ofNat(n))), P x) ↔ ∀ m < n, P (nim (∗m)) :=
  forall_rightMoves_nim_natCast

@[game_cmp]
theorem exists_leftMoves_nim_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∃ x ∈ leftMoves (nim (∗ofNat(n))), P x) ↔ ∃ m < n, P (nim (∗m)) :=
  exists_leftMoves_nim_natCast

@[game_cmp]
theorem exists_rightMoves_nim_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∃ x ∈ rightMoves (nim (∗ofNat(n))), P x) ↔ ∃ m < n, P (nim (∗m)) :=
  exists_rightMoves_nim_natCast

theorem mem_leftMoves_nim_of_lt {a b : Nimber} (h : a < b) : (nim a) ∈ (nim b).leftMoves := by
  simpa using ⟨_, h, rfl⟩

theorem mem_rightMoves_nim_of_lt {a b : Nimber} (h : a < b) : (nim a) ∈ (nim b).rightMoves := by
  simpa using ⟨_, h, rfl⟩

theorem nim_injective : Function.Injective nim := by
  intro a b h'
  obtain h | rfl | h := lt_trichotomy a b
  on_goal 2 => rfl
  all_goals cases self_not_mem_leftMoves _ <| h' ▸ mem_leftMoves_nim_of_lt h

@[simp] theorem nim_inj {a b : Nimber} : nim a = nim b ↔ a = b := nim_injective.eq_iff

@[simp, game_cmp] theorem nim_zero : nim 0 = 0 := by ext <;> simp
@[simp, game_cmp] theorem nim_one : nim 1 = ⋆ := by ext <;> simp [eq_comm]

@[simp]
theorem birthday_nim (o : Nimber) : (nim o).birthday = o := by
  rw [nim_def, birthday_ofSets, max_self, image_image]
  conv_rhs => rw [← iSup_succ o, iSup]
  simp_rw [Function.comp_apply, ← image_eq_range]
  congr!
  rw [birthday_nim]
termination_by o

@[simp, game_cmp]
theorem neg_nim (o : Nimber) : -nim o = nim o := by
  rw [nim_def, neg_ofSets]
  congr!
  all_goals
    rw [← image_neg_eq_neg, image_image]
    congr!
    rw [neg_nim]
termination_by o

instance impartial_nim (o : Nimber) : Impartial (nim o) := by
  apply Impartial.mk' (by simp)
  all_goals
    intro x hx
    simp only [leftMoves_nim, rightMoves_nim] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact impartial_nim a
termination_by o

private theorem nim_fuzzy_of_lt {a b : Nimber} (h : a < b) : nim a ‖ nim b :=
  Impartial.leftMove_fuzzy (mem_leftMoves_nim_of_lt h)

@[simp]
theorem nim_equiv_iff {a b : Nimber} : nim a ≈ nim b ↔ a = b := by
  obtain h | rfl | h := lt_trichotomy a b
  · simp_rw [h.ne, (nim_fuzzy_of_lt h).not_antisymmRel]
  · simp
  · simp_rw [h.ne', (nim_fuzzy_of_lt h).symm.not_antisymmRel]

@[simp]
theorem nim_fuzzy_iff {a b : Nimber} : nim a ‖ nim b ↔ a ≠ b := by
  rw [← Impartial.not_equiv_iff, ne_eq, not_iff_not, nim_equiv_iff]

theorem nim_add_equiv (a b : Nimber) : nim a + nim b ≈ nim (a + b) := by
  rw [Impartial.equiv_iff_forall_fuzzy, forall_leftMoves_add,
    forall_leftMoves_nim, forall_leftMoves_nim, forall_rightMoves_nim]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> intro c hc
  · rw [(nim_add_equiv c b).incompRel_congr_left, nim_fuzzy_iff, ne_eq, add_left_inj]
    exact hc.ne
  · rw [(nim_add_equiv a c).incompRel_congr_left, nim_fuzzy_iff, ne_eq, add_right_inj]
    exact hc.ne
  · obtain h | h := Nimber.lt_add_cases hc
    · have := nim_add_equiv (c + b) b
      rw [add_cancel_right] at this
      rw [← this.incompRel_congr_right, add_fuzzy_add_iff_right, nim_fuzzy_iff]
      exact h.ne'
    · rw [add_comm] at h
      have := nim_add_equiv a (c + a)
      rw [add_comm c, add_cancel_left] at this
      rw [← this.incompRel_congr_right, add_fuzzy_add_iff_left, nim_fuzzy_iff]
      exact h.ne'
termination_by (a, b)

/-! ### Grundy value -/

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
end IGame
