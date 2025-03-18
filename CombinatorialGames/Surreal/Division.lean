/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Theodore Hwa
-/
import CombinatorialGames.Surreal.Multiplication
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring.RingNF

/-!
# Surreal division

In this file, we prove that if `x` is a positive numeric game, then `x⁻¹` (defined in
`Mathlib.SetTheory.Game.IGame`) is a number and is a multiplicative inverse for `x`. We use that
to define the field structure on `Surreal`.

This is Theorem 1.10 in ONAG, and we follow the broad strokes of the proof. We prove
by simultaneous induction that if `x` is positive and numeric, then (ii) `x⁻¹` is numeric, and (iv)
`x * x⁻¹ ≈ 1`. We do this by showing the inductive hypothesis implies that (i) `x * y < 1` for
`y ∈ x⁻¹.leftMoves` and `1 < x * y` for `y ∈ x⁻¹.rightMoves`, and that (iv) `y < 1` for
`y ∈ (x * x⁻¹).leftMoves` and `1 < y` for `y ∈ (x * x⁻¹.rightMoves)`.

An important difference is that Conway assumes that `x` has no negative left options, while we don't
make use of this assumption. This is because our definition of the inverse is tweaked to ensure that
only positive left options of `x` generate the options for `x⁻¹`. To make sure the induction checks
out, we require two small extra arithmetic lemmas `mulOption_le` and `le_mulOption`.

Once we have defined the inverse for positive `x`, it is extended in the obvious way to negative
numbers.
-/

open IGame

namespace Surreal.Division

/-! ### Arithmetic lemmas -/

lemma one_neg_mul_invOption (x : IGame) {y : IGame} (hy : y * y⁻¹ ≈ 1) (a : IGame)
    [Numeric x] [Numeric y] [Numeric y⁻¹] [Numeric a] :
    1 - x * invOption x y a ≈ (1 - x * a) * (y - x) / y := by
  rw [← Surreal.mk_eq_mk] at *
  dsimp [invOption, mk_div'] at *
  simp only [one_mul, sub_eq_add_neg, add_mul, hy]
  ring

lemma mulOption_self_inv (x : IGame) {y : IGame} (hy : y * y⁻¹ ≈ 1) (a : IGame)
    [Numeric x] [Numeric x⁻¹] [Numeric y] [Numeric y⁻¹] [Numeric a] :
    mulOption x x⁻¹ y a ≈ 1 + (x⁻¹ - invOption x y a) * y := by
  rw [mul_comm] at hy
  rw [← Surreal.mk_eq_mk] at *
  dsimp [mulOption, invOption, mk_div'] at *
  simp only [sub_eq_add_neg, add_mul, neg_mul, mul_assoc, hy]
  ring

lemma mulOption_le (x y : IGame) {a b : IGame} [Numeric x] [Numeric y] [Numeric a] [Numeric b]
    (ha : a ≤ 0) (hb : b ≤ y) : mulOption x y a b ≤ x * b := by
  rw [mulOption, ← Game.mk_le_mk]
  dsimp
  have : Game.mk (a * y) - Game.mk (a * b) ≤ 0 := by
    rw [← Game.mk_mul_sub]
    apply Numeric.mul_nonpos_of_nonpos_of_nonneg ha
    rwa [IGame.sub_nonneg]
  rw [← add_le_add_iff_left (Game.mk (x * b))] at this
  convert this using 1 <;> abel

theorem le_mulOption (x y : IGame) {a b : IGame} [Numeric x] [Numeric y] [Numeric a] [Numeric b]
    (ha : a ≤ 0) (hb : y ≤ b) : x * b ≤ mulOption x y a b := by
  rw [mulOption, ← Game.mk_le_mk]
  dsimp
  have : 0 ≤ Game.mk (a * y) - Game.mk (a * b) := by
    rw [← Game.mk_mul_sub]
    apply Numeric.mul_nonneg_of_nonpos_of_nonpos ha
    rwa [IGame.sub_nonpos]
  rw [← add_le_add_iff_left (Game.mk (x * b))] at this
  convert this using 1 <;> abel

/-! ### Inductive proof -/

lemma numeric_option_inv {x : IGame} [Numeric x]
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹) :
    (∀ y ∈ x⁻¹.leftMoves, Numeric y) ∧ (∀ y ∈ x⁻¹.rightMoves, Numeric y) := by
  apply invRec x Numeric.zero
  all_goals
    intro y hy hy'
    intros
    first |
      have := Numeric.of_mem_leftMoves hy; have := hl _ hy hy' |
      have := Numeric.of_mem_rightMoves hy; have := hr _ hy
    infer_instance

lemma mul_inv_option_mem {x : IGame} [Numeric x]
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹)
    (hl' : ∀ y ∈ x.leftMoves, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ x.rightMoves, y * y⁻¹ ≈ 1) :
    (∀ y ∈ x⁻¹.leftMoves, x * y < 1) ∧ (∀ y ∈ x⁻¹.rightMoves, 1 < x * y) := by
  apply invRec x
  · simp
  · intro y hy a ha h
    have := Numeric.of_mem_rightMoves hy
    have := hr y hy
    have := (numeric_option_inv hl hr).1 a ha
    rw [← IGame.sub_pos, (one_neg_mul_invOption x (hr' y hy) a).lt_congr_right]
    apply Numeric.mul_pos (Numeric.mul_pos _ _) (Numeric.inv_pos y)
    · rwa [IGame.sub_pos]
    · rw [IGame.sub_pos]
      exact Numeric.lt_rightMove hy
  · intro y hy hy' a ha h
    have := Numeric.of_mem_leftMoves hy
    have := hl y hy hy'
    have := (numeric_option_inv hl hr).2 a ha
    rw [← IGame.sub_pos, (one_neg_mul_invOption x (hl' y hy hy') a).lt_congr_right]
    apply Numeric.mul_pos (Numeric.mul_pos_of_neg_of_neg _ _) (Numeric.inv_pos y)
    · rwa [IGame.sub_neg]
    · rw [IGame.sub_neg]
      exact Numeric.leftMove_lt hy
  · intro y hy hy' a ha h
    have := Numeric.of_mem_leftMoves hy
    have := hl y hy hy'
    have := (numeric_option_inv hl hr).1 a ha
    rw [← IGame.sub_neg, (one_neg_mul_invOption x (hl' y hy hy') a).lt_congr_left]
    apply Numeric.mul_neg_of_neg_of_pos (Numeric.mul_neg_of_pos_of_neg _ _) (Numeric.inv_pos y)
    · rwa [IGame.sub_pos]
    · rw [IGame.sub_neg]
      exact Numeric.leftMove_lt hy
  · intro y hy a ha h
    have := Numeric.of_mem_rightMoves hy
    have := hr y hy
    have := (numeric_option_inv hl hr).2 a ha
    rw [← IGame.sub_neg, (one_neg_mul_invOption x (hr' y hy) a).lt_congr_left]
    apply Numeric.mul_neg_of_neg_of_pos (Numeric.mul_neg_of_neg_of_pos _ _) (Numeric.inv_pos y)
    · rwa [IGame.sub_neg]
    · rw [IGame.sub_pos]
      exact Numeric.lt_rightMove hy

lemma numeric_inv {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹)
    (hl' : ∀ y ∈ x.leftMoves, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ x.rightMoves, y * y⁻¹ ≈ 1) :
    Numeric x⁻¹ := by
  obtain ⟨Hl, Hr⟩ := mul_inv_option_mem hl hr hl' hr'
  obtain ⟨Hl', Hr'⟩ := numeric_option_inv hl hr
  refine Numeric.mk' (fun y hy z hz ↦ ?_) Hl' Hr'
  have := Hl' y hy
  have := Hr' z hz
  exact (Numeric.mul_lt_mul_left hx).1 <| (Hl y hy).trans (Hr z hz)

lemma option_mul_inv_lt {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹)
    (hl' : ∀ y ∈ x.leftMoves, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ x.rightMoves, y * y⁻¹ ≈ 1) :
    (∀ y ∈ (x * x⁻¹).leftMoves, y < 1) ∧ (∀ y ∈ (x * x⁻¹).rightMoves, 1 < y) := by
  have := numeric_inv hx hl hr hl' hr'
  obtain ⟨Hl, Hr⟩ := numeric_option_inv hl hr
  rw [forall_leftMoves_mul, forall_rightMoves_mul]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals
    intro y hy a ha
    first | have := Numeric.of_mem_leftMoves hy | have := Numeric.of_mem_rightMoves hy
    first | have := Hl a ha | have := Hr a ha
    try (have := hr y hy; have hy' := hx.trans (Numeric.lt_rightMove hy))
  · obtain hy' | hy' := Numeric.lt_or_le 0 y
    · have := hl y hy hy'
      rw [(mulOption_self_inv x (hl' y hy hy') a).lt_congr_left, add_comm,
        ← IGame.lt_sub_iff_add_lt, (IGame.sub_self_equiv _).lt_congr_right]
      apply Numeric.mul_neg_of_neg_of_pos _ hy'
      rw [IGame.sub_neg]
      exact Numeric.lt_rightMove (invOption_left_left_mem_rightMoves_inv hy hy' ha)
    · apply (mulOption_le _ _ hy' (Numeric.leftMove_lt ha).le).trans_lt
      exact (mul_inv_option_mem hl hr hl' hr').1 a ha
  · rw [(mulOption_self_inv x (hr' y hy) a).lt_congr_left, add_comm,
      ← IGame.lt_sub_iff_add_lt, (IGame.sub_self_equiv _).lt_congr_right]
    apply Numeric.mul_neg_of_neg_of_pos _ hy'
    rw [IGame.sub_neg]
    exact Numeric.lt_rightMove (invOption_right_right_mem_rightMoves_inv hy ha)
  · obtain hy' | hy' := Numeric.lt_or_le 0 y
    · have := hl y hy hy'
      rw [(mulOption_self_inv x (hl' y hy hy') a).lt_congr_right, add_comm,
        ← IGame.sub_lt_iff_lt_add, (IGame.sub_self_equiv _).lt_congr_left]
      apply Numeric.mul_pos _ hy'
      rw [IGame.sub_pos]
      apply Numeric.leftMove_lt (invOption_left_right_mem_leftMoves_inv hy hy' ha)
    · apply ((mul_inv_option_mem hl hr hl' hr').2 a ha).trans_le
      exact le_mulOption _ _ hy' (Numeric.lt_rightMove ha).le
  · rw [(mulOption_self_inv x (hr' y hy) a).lt_congr_right, add_comm,
      ← IGame.sub_lt_iff_lt_add, (IGame.sub_self_equiv _).lt_congr_left]
    apply Numeric.mul_pos _ hy'
    rw [IGame.sub_pos]
    exact Numeric.leftMove_lt (invOption_right_left_mem_leftMoves_inv hy ha)

lemma mul_inv_self {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹)
    (hl' : ∀ y ∈ x.leftMoves, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ x.rightMoves, y * y⁻¹ ≈ 1) :
    x * x⁻¹ ≈ 1 := by
  obtain ⟨Hl, Hr⟩ := option_mul_inv_lt hx hl hr hl' hr'
  have := numeric_inv hx hl hr hl' hr'
  apply equiv_one_of_fits ⟨fun z hz ↦ (Hl z hz).not_le, fun z hz ↦ (Hr z hz).not_le⟩
  rw [Numeric.mul_equiv_zero, not_or]
  exact ⟨hx.not_antisymmRel_symm, (Numeric.inv_pos x).not_antisymmRel_symm⟩

theorem main {x : IGame} [Numeric x] (hx : 0 < x) : Numeric x⁻¹ ∧ x * x⁻¹ ≈ 1 := by
  have IHl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹ ∧ y * y⁻¹ ≈ 1 :=
    fun y hy hy' ↦ have := Numeric.of_mem_leftMoves hy; main hy'
  have IHr : ∀ y ∈ x.rightMoves, Numeric y⁻¹ ∧ y * y⁻¹ ≈ 1 :=
    fun y hy ↦ have := Numeric.of_mem_rightMoves hy; main (hx.trans (Numeric.lt_rightMove hy))
  have hl := fun y hy hy' ↦ (IHl y hy hy').1
  have hr := fun y hy ↦ (IHr y hy).1
  have hl' := fun y hy hy' ↦ (IHl y hy hy').2
  have hr' := fun y hy ↦ (IHr y hy).2
  exact ⟨numeric_inv hx hl hr hl' hr', mul_inv_self hx hl hr hl' hr'⟩
termination_by x
decreasing_by igame_wf

end Surreal.Division

/-! ### Instances and corollaries -/

namespace IGame
open Surreal.Division

namespace Numeric

protected theorem inv {x : IGame} [Numeric x] (hx : 0 < x) : Numeric x⁻¹ := (main hx).1
protected theorem mul_inv_cancel {x : IGame} [Numeric x] (hx : 0 < x) : x * x⁻¹ ≈ 1 := (main hx).2

theorem inv_congr {x y : IGame} [Numeric x] [Numeric y] (hx : 0 < x) (hy : x ≈ y) : x⁻¹ ≈ y⁻¹ := by
  have hy' := hx.trans_antisymmRel hy
  have := Numeric.inv hx
  have := Numeric.inv hy'
  have := (Numeric.mul_inv_cancel hx).trans (Numeric.mul_inv_cancel hy').symm
  rw [← (Numeric.mul_congr_left hy).antisymmRel_congr_right] at this
  exact Numeric.mul_left_cancel hx.not_antisymmRel_symm this

protected instance ratCast (q : ℚ) : Numeric q := by
  have : Numeric (q.den : IGame)⁻¹ := .inv (mod_cast q.den_pos)
  change Numeric (_ * _)
  infer_instance

end Numeric

/-- An auxiliary definition for the surreal inverse. -/
private noncomputable def inv' (x : IGame) : IGame := by
  classical exact if 0 < x then x⁻¹ else if x < 0 then -(-x)⁻¹ else 0

private theorem inv'_zero : inv' 0 = 0 := by
  simp [inv']

private instance {x : IGame} [Numeric x] : Numeric (inv' x) := by
  unfold inv'
  obtain h | h | h := Numeric.lt_or_equiv_or_gt x 0
  · simpa [h, h.asymm] using Numeric.inv (IGame.zero_lt_neg.2 h)
  · simp [h.not_lt, h.not_gt]
  · simpa [h] using Numeric.inv h

private theorem Numeric.mul_inv'_cancel {x : IGame} [Numeric x] (hx : ¬ x ≈ 0) :
    x * (inv' x) ≈ 1 := by
  unfold inv'
  obtain h | h | h := Numeric.lt_or_equiv_or_gt x 0
  · simpa [h, h.asymm] using Numeric.mul_inv_cancel (IGame.zero_lt_neg.2 h)
  · contradiction
  · simpa [h] using Numeric.mul_inv_cancel h

private theorem Numeric.inv'_congr {x y : IGame} [Numeric x] [Numeric y] (hy : x ≈ y) :
    inv' x ≈ inv' y := by
  unfold inv'
  obtain h | h | h := Numeric.lt_or_equiv_or_gt y 0
  · have h' := hy.trans_lt h
    rw [if_neg h.asymm, if_neg h'.asymm, if_pos h, if_pos h', neg_equiv_neg_iff]
    rw [← IGame.zero_lt_neg] at h'
    apply Numeric.inv_congr h'
    rwa [neg_equiv_neg_iff]
  · have h' := hy.trans h
    rw [if_neg h.not_lt, if_neg h'.not_lt, if_neg h.not_gt, if_neg h'.not_gt]
  · have h' := h.trans_antisymmRel hy.symm
    rw [if_pos h, if_pos h']
    exact Numeric.inv_congr h' hy

end IGame

namespace Surreal

noncomputable instance : LinearOrderedField Surreal where
  inv := Quotient.map (fun x ↦ ⟨inv' x, by infer_instance⟩) fun _ _ ↦ Numeric.inv'_congr
  mul_inv_cancel := by rintro ⟨a⟩ h; exact mk_eq (Numeric.mul_inv'_cancel (mk_eq_mk.not.1 h))
  inv_zero := by change mk (inv' 0) = _; simp [inv'_zero]
  qsmul := _
  nnqsmul := _

theorem mk_inv_of_pos {x : IGame} (h : 0 < x) [Numeric x] : @mk x⁻¹ (.inv h) = (mk x)⁻¹ := by
  change _ = mk (inv' _)
  unfold inv'
  simp_rw [if_pos h]

theorem mk_div_of_pos (x : IGame) {y : IGame} (h : 0 < y) [Numeric x] [Numeric y] :
    @mk (x / y) (@Numeric.div x y _ (.inv h)) = mk x / mk y := by
  have := Numeric.inv h
  simp_rw [IGame.div_eq_mul_inv, mk_mul, mk_inv_of_pos h]
  rfl

@[simp]
theorem mk_ratCast (q : ℚ) : mk q = q := by
  simp_rw [ratCast_def]
  rw [mk_div_of_pos]
  · conv_rhs => rw [← q.num_div_den]
    simp
  · exact_mod_cast q.den_pos

end Surreal

namespace IGame

@[simp, norm_cast]
theorem ratCast_le {m n : ℚ} : (m : IGame) ≤ n ↔ m ≤ n := by
  simp [← Surreal.mk_le_mk]

@[simp, norm_cast]
theorem ratCast_lt {m n : ℚ} : (m : IGame) < n ↔ m < n := by
  simp [← Surreal.mk_lt_mk]

theorem ratCast_strictMono : StrictMono ((↑) : ℚ → IGame) :=
  fun _ _ h ↦ ratCast_lt.2 h

@[simp, norm_cast]
theorem ratCast_inj {m n : ℚ} : (m : IGame) = n ↔ m = n :=
  ratCast_strictMono.injective.eq_iff

end IGame
