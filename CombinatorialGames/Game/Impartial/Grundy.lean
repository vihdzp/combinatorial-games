/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Specific.Nim

/-!
# Grundy value

The Grundy value of an impartial game is recursively defined as the least nimber not among the
Grundy values of either its left or right options. This map respects (by definition!) addition and
multiplication.

We provide two definitions for the Grundy value. `grundyAux` is computed using either the left or
right options of the game, and is defined for all games. To make the API symmetric, we also provide
`Impartial.grundy`, which enforces that the game is impartial, and is thus equal to either of
`grundyAux left` or `grundyAux right`.

The **Sprague-Grundy** theorem `Impartial.nim_grundy_equiv` shows that any impartial game is
equivalent to a game of Nim, namely that corresponding to its Grundy value.
-/

universe u

open Nimber Set

noncomputable section

namespace IGame

/-! ### Grundy value -/

/-- The left or right Grundy value of a game is recursively defined as the minimum excluded value
(the infimum of the complement) of the left or right Grundy values of its left or right options.

This is an auxiliary definition for reasoning about games not yet known to be impartial. Use
`Impartial.grundy` for an impartial game. -/
def grundyAux (p : Player) (x : IGame.{u}) : Nimber.{u} :=
  sInf (Set.range fun y : x.moves p ↦ grundyAux p y.1)ᶜ
termination_by x
decreasing_by igame_wf

theorem grundyAux_def (p) (x : IGame) : grundyAux p x = sInf (grundyAux p '' x.moves p)ᶜ := by
  rw [grundyAux, image_eq_range]

theorem le_grundyAux_iff {p : Player} {x : IGame} {o : Nimber} :
    o ≤ grundyAux p x ↔ Iio o ⊆ grundyAux p '' x.moves p := by
  rw [grundyAux_def, le_csInf_iff'']
  · rw [← compl_subset_compl (t := Iio o), subset_def]
    simp
  · exact nonempty_of_not_bddAbove (Nimber.not_bddAbove_compl_of_small _)

theorem lt_grundyAux_iff {p : Player} {x : IGame} {o : Nimber} :
    o < grundyAux p x ↔ Iic o ⊆ grundyAux p '' x.moves p := by
  simpa using le_grundyAux_iff (o := Order.succ o)

theorem mem_grundyAux_image_of_lt {p : Player} {x : IGame} {o : Nimber} (h : o < grundyAux p x) :
    o ∈ grundyAux p '' x.moves p :=
  le_grundyAux_iff.1 le_rfl h

theorem grundyAux_le_of_notMem {p : Player} {x : IGame} {o : Nimber}
    (h : o ∉ grundyAux p '' x.moves p) :
    grundyAux p x ≤ o :=
  le_of_not_gt <| mt mem_grundyAux_image_of_lt h

theorem grundyAux_ne {p : Player} {x y : IGame} (hy : y ∈ x.moves p) :
    grundyAux p y ≠ grundyAux p x := by
  conv_rhs => rw [grundyAux_def]
  have := csInf_mem (nonempty_of_not_bddAbove <|
    Nimber.not_bddAbove_compl_of_small (grundyAux p '' x.moves p))
  simp_all

@[simp]
theorem grundyAux_neg (p : Player) (x : IGame) : grundyAux p (-x) = grundyAux (-p) x := by
  rw [grundyAux_def, grundyAux_def, moves_neg]
  congr 2
  exact image_neg_of_apply_neg_eq fun _ _ ↦ grundyAux_neg p _
termination_by x
decreasing_by igame_wf

@[simp]
theorem grundyAux_image_neg (p : Player) (s : Set IGame) :
    grundyAux p '' (-s) = grundyAux (-p) '' s :=
  image_neg_of_apply_neg_eq fun _ _ ↦ grundyAux_neg _ _

namespace Impartial

/-- The Grundy value of an impartial game is recursively defined as the minimum excluded value
(the infimum of the complement) of the Grundy values of its options.

This definition enforces that `x` is impartial. If you want to talk about the left or right Grundy
values of a game (e.g. if you don't yet know it to be impartial), use `grundyAux`.
The lemma `grundyAux_eq_grundy` shows that both definitions match in
the case of an impartial game. -/
def grundy (x : IGame) [Impartial x] : Nimber :=
  x.grundyAux right

/-- The **Sprague-Grundy theorem** states that every impartial game is equivalent to a game of nim,
namely the game of nim for the game's Grundy value. -/
theorem nim_grundy_equiv (x : IGame) [Impartial x] : nim (grundy x) ≈ x := by
  rw [equiv_iff_forall_fuzzy default]
  constructor <;> intro y hy
  · rw [moves_nim] at hy
    obtain ⟨o, ho, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := mem_grundyAux_image_of_lt ho
    have := Impartial.of_mem_moves hz
    rw [← grundy, (nim_grundy_equiv _).incompRel_congr_left]
    exact fuzzy_of_mem_moves hz
  · have := Impartial.of_mem_moves hy
    rw [← (nim_grundy_equiv _).incompRel_congr_right, nim_fuzzy_iff]
    exact (grundyAux_ne hy).symm
termination_by x
decreasing_by igame_wf

theorem grundy_eq_iff_equiv_nim {x : IGame} [Impartial x] {o : Nimber} :
    grundy x = o ↔ x ≈ nim o := by
  rw [← (nim_grundy_equiv x).antisymmRel_congr_left, nim_equiv_iff]

alias ⟨_, grundy_eq⟩ := grundy_eq_iff_equiv_nim

theorem grundy_eq_zero_iff {x : IGame} [Impartial x] : grundy x = 0 ↔ x ≈ 0 := by
  simpa using grundy_eq_iff_equiv_nim (o := 0)

@[simp]
theorem grundy_eq_iff_equiv {x y : IGame} [Impartial x] [Impartial y] :
    grundy x = grundy y ↔ x ≈ y := by
  rw [grundy_eq_iff_equiv_nim, (nim_grundy_equiv _).antisymmRel_congr_right]

alias ⟨_, grundy_congr⟩ := grundy_eq_iff_equiv

@[simp] theorem grundy_nim (o : Nimber) : grundy (nim o) = o := grundy_eq .rfl
@[simp] theorem grundy_zero : grundy 0 = 0 := by simpa using grundy_nim 0
@[simp] theorem grundy_star : grundy ⋆ = 1 := by simpa using grundy_nim 1

@[simp]
theorem grundy_neg (x : IGame) [Impartial x] : grundy (-x) = grundy x := by
  rw [grundy_eq_iff_equiv_nim, ← neg_nim, IGame.neg_equiv_neg_iff, ← grundy_eq_iff_equiv_nim]

@[simp]
theorem grundyAux_eq_grundy (p) (x : IGame) [Impartial x] : grundyAux p x = grundy x := by
  cases p with
  | left => rw [← grundy_neg, grundy, grundyAux_neg, Player.neg_right]
  | right => rfl

theorem grundy_moves_ne {p : Player} {x y : IGame} [Impartial x] (hy : y ∈ x.moves p) :
    have := Impartial.of_mem_moves hy; grundy y ≠ grundy x := by
  cases p with
  | left =>
    simp_rw [← grundyAux_eq_grundy left]
    exact grundyAux_ne hy
  | right =>
    exact grundyAux_ne hy

/-- One half of the **lawnmower theorem** for impartial games. -/
protected theorem lt_of_numeric_of_pos (x) [Impartial x] {y} [Numeric y] (hy : 0 < y) : x < y := by
  rw [← (nim_grundy_equiv x).lt_congr_left]
  exact Dicotic.lt_of_numeric_of_pos _ hy

/-- One half of the **lawnmower theorem** for impartial games. -/
protected theorem lt_of_numeric_of_neg (x) [Impartial x] {y} [Numeric y] (hy : y < 0) : y < x := by
  rw [← (nim_grundy_equiv x).lt_congr_right]
  exact Dicotic.lt_of_numeric_of_neg _ hy

private theorem of_grundyAux_left_eq_grundyAux_right' {x : IGame}
    (h : ∀ p, ∀ y ∈ x.moves p, Impartial y)
    (H : grundyAux left x = grundyAux right x) : nim (grundyAux right x) ≈ x := by
  constructor <;> refine le_iff_forall_lf.2 ⟨?_, ?_⟩
  · rw [forall_moves_nim]
    intro a ha
    rw [← H] at ha
    obtain ⟨y, hy, rfl⟩ := mem_grundyAux_image_of_lt ha
    have := h left y hy
    rw [grundyAux_eq_grundy]
    exact lf_of_le_leftMove (nim_grundy_equiv y).le hy
  · intro y hy
    have := h right y hy
    rw [← (nim_grundy_equiv y).le_congr_left, lf_iff_fuzzy, nim_fuzzy_iff,
      ← grundyAux_eq_grundy right]
    exact (grundyAux_ne hy).symm
  · intro y hy
    have := h left y hy
    rw [← (nim_grundy_equiv y).le_congr_right, lf_iff_fuzzy, nim_fuzzy_iff,
      ← grundyAux_eq_grundy left]
    exact H ▸ grundyAux_ne hy
  · rw [forall_moves_nim]
    intro a ha
    obtain ⟨y, hy, rfl⟩ := mem_grundyAux_image_of_lt ha
    have := h right y hy
    exact lf_of_rightMove_le (nim_grundy_equiv y).ge hy

/-- If a game `x` has only impartial options, and its left Grundy value equals its right Grundy
value, then it's impartial. -/
theorem of_grundyAux_left_eq_grundyAux_right {x : IGame}
    (h : ∀ p, ∀ y ∈ x.moves p, Impartial y)
    (H : grundyAux left x = grundyAux right x) : Impartial x :=
  have H := of_grundyAux_left_eq_grundyAux_right' h H
  .mk ((neg_congr H).symm.trans ((neg_nim _).symm ▸ H)) h

end Impartial
end IGame
end
