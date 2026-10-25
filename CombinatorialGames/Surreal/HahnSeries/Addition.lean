/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Surreal.HahnSeries.Transfer
public import CombinatorialGames.Surreal.Omnific.Basic

import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Group isomorphism between surreals and Hahn series

We prove here that `Surreal` and `SurrealHahnSeries` are isomorphic as ordered groups.

Conway omits this proof entirely. This file is loosely based on pages 429-430 of Siegel.
-/

public noncomputable section

@[simp]
lemma LinearOrderedAddCommGroupWithTop.sub_nonneg {α} [LinearOrderedAddCommGroupWithTop α]
    {a b : α} : 0 ≤ a - b ↔ b ≤ a ∨ b = ⊤ := by
  obtain rfl | hb := eq_or_ne b ⊤
  · simp
  · simp [← sub_self_eq_zero_of_ne_top hb, hb]

lemma LinearOrderedAddCommGroupWithTop.sub_nonneg_of_le {α} [LinearOrderedAddCommGroupWithTop α]
    {a b : α} (h : b ≤ a) : 0 ≤ a - b := by
  rw [sub_nonneg]
  exact .inl h

namespace Surreal
open ArchimedeanClass Order Set SurrealHahnSeries

variable {x y : Surreal} (h : x.support ⊆ Ioi y.wlog)
include h

open PartialSum

namespace PartialSum

variable (x y) in
/-- `x` as a partial sum of `x + y`, whenever `y.support < x.support` pairwise. -/
def ofAdd : PartialSum (x + y) where
  carrier := x.toHahnSeries
  term_eq_leadingTerm_sub {j} hj := by
    rw [← leadingTerm_sub_truncIdx, toSurreal_toHahnSeries]
    obtain rfl | hy' := eq_or_ne y 0; · simp
    rw [add_sub_right_comm, leadingTerm_add_eq_left]
    nth_rw 1 [← toSurreal_toHahnSeries x]
    rw [vlt_def, ← mk_leadingTerm, leadingTerm_sub_truncIdx, mk_term hj, ← vlt_def,
      ← wlog_lt_wlog_iff hy' (wpow_ne_zero _), wlog_wpow]
    apply h
    simp

@[simp] theorem carrier_ofAdd : (ofAdd x y h).carrier = x.toHahnSeries := (rfl)
@[simp] theorem length_ofAdd : (ofAdd x y h).length = x.length := (rfl)

theorem truncIdx_top_add_length : (⊤ : PartialSum (x + y)).truncIdx x.length = ofAdd x y h :=
  truncIdx_length_of_le (y := ofAdd x y h) le_top

end PartialSum

private theorem truncIdx_add_length_of_subset : (x + y).toHahnSeries.truncIdx x.length = x := by
  apply toSurreal_eq
  simpa using congrArg carrier (truncIdx_top_add_length h).symm

theorem le_length_add_of_subset : x.length ≤ (x + y).length := by
  conv_lhs => rw [← truncIdx_add_length_of_subset h]
  simp

theorem lt_length_add_of_subset (hy : y ≠ 0) : x.length < (x + y).length := by
  apply (le_length_add_of_subset h).lt_of_ne
  rw [← length_ofAdd h, Surreal.length, ← carrier_top, ne_eq, length_inj]
  apply_fun carrier
  simpa

private theorem term_add_length_of_subset : (x + y).toHahnSeries.term x.length = y.leadingTerm := by
  obtain rfl | hy := eq_or_ne y 0; · simp
  rw [← carrier_top]
  apply ((⊤ : PartialSum (x + y)).term_eq_leadingTerm_sub _).trans
  · rw [carrier_top, truncIdx_add_length_of_subset h, add_sub_cancel_left]
  · rw [carrier_top]
    exact lt_length_add_of_subset h hy

private theorem exp_add_length_of_subset (hy : y ≠ 0) :
    (x + y).toHahnSeries.exp ⟨x.length,
      by simpa using lt_length_add_of_subset h hy⟩ = y.wlog := by
  rw [← wlog_term (lt_length_add_of_subset h hy), term_add_length_of_subset h, wlog_leadingTerm]

private theorem coeffIdx_add_length_of_subset :
    (x + y).toHahnSeries.coeffIdx x.length = y.leadingCoeff := by
  rw [← leadingCoeff_term, term_add_length_of_subset h, leadingCoeff_leadingTerm]

private theorem coeff_add_wlog_of_subset (hy : y ≠ 0) :
    (x + y).coeff y.wlog = y.leadingCoeff := by
  rw [coeff, ← exp_add_length_of_subset h hy, coeff_exp, coeffIdx_add_length_of_subset h]

omit h

private theorem trunc_add_of_subset {i : Surreal} (hx : x.support ⊆ Ioi i) (hy : y ≤ᵥ ω^ i) :
    (x + y).trunc i = x := by
  obtain rfl | hy₀ := eq_or_ne y 0
  · rw [add_zero]
    exact trunc_eq_self hx
  rw [← wlog_le_iff hy₀] at hy
  have hx' := hx.trans (Ioi_subset_Ioi hy)
  have hl := truncIdx_of_lt <| lt_length_add_of_subset hx' hy₀
  rw [exp_add_length_of_subset hx' hy₀] at hl
  conv_rhs => rw [← truncIdx_add_length_of_subset hx']
  rw [hl, toSurreal_trunc, toSurreal_toHahnSeries]
  refine (trunc_eq_trunc hy fun k hek hki ↦ ?_).symm
  contrapose! hki
  apply hx
  rw [← truncIdx_add_length_of_subset hx', hl, toSurreal_trunc, toSurreal_toHahnSeries,
    support_trunc]
  exact ⟨hki, hek⟩

private theorem coeff_add_of_subset {i : Surreal} (hx : x.support ⊆ Ioi i) (hy : y ≤ᵥ ω^ i) :
    (x + y).coeff i = stdPart (y / ω^ i) := by
  obtain rfl | hy₀ := eq_or_ne y 0
  · rw [add_zero, zero_div, stdPart_zero]
    contrapose! hx
    exact not_subset.2 ⟨_, hx, self_notMem_Ioi⟩
  rw [← wlog_le_iff hy₀] at hy
  obtain rfl | hy := hy.eq_or_lt
  · exact coeff_add_wlog_of_subset hx hy₀
  · have hx' := hx.trans (Ioi_subset_Ioi hy.le)
    trans 0
    · contrapose! hx
      refine not_subset.2 ⟨i, ?_, self_notMem_Ioi⟩
      rw [← trunc_add_of_subset hx' (wpow_wlog_veq hy₀).ge, support_trunc]
      exact ⟨hx, hy⟩
    · rw [eq_comm, stdPart_eq_zero]
      apply ne_of_gt
      rw [ArchimedeanClass.mk_div, LinearOrderedAddCommGroupWithTop.sub_pos, ← vlt_def,
        ← wlog_lt_iff hy₀]
      exact .inl hy

@[simp]
theorem sub_trunc_vle_wpow (x i : Surreal) : x - x.trunc i ≤ᵥ ω^ i := by
  obtain ⟨j, hj⟩ := trunc_mem_range_truncIdx x.toHahnSeries i
  obtain hsub | hsub := eq_or_ne (x - x.trunc i) 0; · simp [hsub]
  have hl : (x - x.trunc i).leadingTerm = x.toHahnSeries.term j := by
    rw [trunc, ← hj, ← leadingTerm_sub_truncIdx, toSurreal_toHahnSeries]
  obtain hxj | hxj := le_or_gt x.toHahnSeries.length j
  · rw [term_of_ge hxj, leadingTerm_eq_zero] at hl
    contradiction
  · rw [← wlog_le_iff hsub, ← wlog_leadingTerm, hl, wlog_term hxj]
    by_contra! hlt
    apply exp_notMem_support_truncIdx _ ⟨j, hxj⟩
    rw [hj]
    simpa

@[simp]
theorem trunc_sub_vle_wpow (x i : Surreal) : x.trunc i - x ≤ᵥ ω^ i := by
  rw [← neg_vle, neg_sub]
  exact sub_trunc_vle_wpow x i

private theorem mk_sub_trunc_div_wpow_nonneg {i : Surreal} :
    0 ≤ ArchimedeanClass.mk ((x - x.trunc i) / ω^ i) := by
  simp [← vle_def]

theorem coeff_eq_stdPart {i : Surreal} : x.coeff i = stdPart ((x - x.trunc i) / ω^ i) := by
  conv_lhs => rw [← add_sub_cancel (x.trunc i) x]
  apply coeff_add_of_subset _ (sub_trunc_vle_wpow x i)
  simp

theorem support_subset_of_round_eq (hx : x.round y = x) (hy : 0 < y) : support x ⊆ Ici y.wlog := by
  intro z hzy
  rw [mem_Ici]
  contrapose! hzy
  intro hz
  obtain ⟨i, rfl⟩ := eq_exp_of_mem_support hz
  have H : ArchimedeanClass.mk y < .mk (x - x.toHahnSeries.truncIdx i) := by
    nth_rw 1 [← toSurreal_toHahnSeries x]
    conv_rhs => rw [← mk_leadingTerm, leadingTerm_sub_truncIdx, mk_term i.2]
    rwa [← vlt_def, ← lt_wlog_iff hy.ne']
  refine (@birthday_round_le x (x.toHahnSeries.truncIdx i) y ⟨?_, ?_⟩).not_gt ?_
  · rw [sub_lt_comm]
    exact lt_of_mk_lt_mk_of_nonneg H hy.le
  · rw [← sub_lt_iff_lt_add']
    apply lt_of_mk_lt_mk_of_nonneg _ hy.le
    rwa [mk_sub_comm]
  · grw [birthday_truncIdx_lt i.2, hx, toSurreal_toHahnSeries]

theorem support_subset_of_round_wpow_eq (h : x.round (ω^ y) = x) : support x ⊆ Ici y := by
  simpa using support_subset_of_round_eq h

include h in
theorem round_eq_of_support_subset (hy : 0 < y) : x.round y = x := by
  refine round_eq_of_forall_birthday_le (by simpa) fun w hw ↦ ?_
  rw [← toSurreal_toHahnSeries w]
  convert ← birthday_trunc_le _ y.wlog
  rw [SurrealHahnSeries.toSurreal_trunc, toSurreal_toHahnSeries, ← add_sub_cancel x w]
  apply trunc_add_of_subset h <| ValuativeRel.vle_trans _ (wpow_wlog_veq hy.ne').ge
  apply ArchimedeanClass.mk_le_mk_of_abs
  grind

theorem round_eq_wpow_of_support_subset (hx : x.support ⊆ Ioi y) : x.round (ω^ y) = x :=
  round_eq_of_support_subset (by simpa) (by simp)

/-- This is a special case of `support_add_subset`. -/
private theorem support_add_subset_Ioi {z : Surreal}
    (hx : x.support ⊆ Ioi z) (hy : y.support ⊆ Ioi z) : (x + y).support ⊆ Ioi z := by
  apply (support_subset_of_round_wpow_eq (y := !{{z} | x.support ∪ y.support}) _).trans
  · aesop
  · apply round_add_of_eq
    all_goals
      refine round_eq_wpow_of_support_subset fun w hw ↦ ?_
      aesop

@[simp, norm_cast]
theorem toHahnSeries_add (x y : Surreal) :
    (x + y).toHahnSeries = x.toHahnSeries + y.toHahnSeries := by
  ext i
  rw [coeff_toHahnSeries, coeff_add_apply]
  trans (x.trunc i + y.trunc i + ((x - x.trunc i) + (y - y.trunc i))).coeff i
  · abel_nf
  · rw [coeff_add_of_subset, add_div,
      stdPart_add mk_sub_trunc_div_wpow_nonneg mk_sub_trunc_div_wpow_nonneg,
      coeff_toHahnSeries, coeff_toHahnSeries, coeff_eq_stdPart, coeff_eq_stdPart]
    · apply support_add_subset_Ioi <;> simp
    · apply ValuativeRel.vle_add <;> exact sub_trunc_vle_wpow _ i

/-- `Surreal.toHahnSeries` as an `OrderAddMonoidIso`. -/
@[expose, simps!]
def toHahnSeriesMonoidIso : Surreal ≃+o SurrealHahnSeries where
  map_add' := toHahnSeries_add
  map_le_map_iff' := toHahnSeries_le_toHahnSeries_iff
  __ := toHahnSeriesOrderIso

@[simp, norm_cast]
theorem toHahnSeries_neg (x : Surreal) : (-x).toHahnSeries = -x.toHahnSeries :=
  map_neg toHahnSeriesMonoidIso x

@[simp, norm_cast]
theorem toHahnSeries_sub (x y : Surreal) : (x - y).toHahnSeries = x.toHahnSeries - y.toHahnSeries :=
  map_sub toHahnSeriesMonoidIso x y

@[simp, norm_cast]
theorem _root_.SurrealHahnSeries.toSurreal_neg (x : SurrealHahnSeries) :
    (-x).toSurreal = -x.toSurreal :=
  map_neg toHahnSeriesMonoidIso.symm x

@[simp, norm_cast]
theorem _root_.SurrealHahnSeries.toSurreal_add (x y : SurrealHahnSeries) :
    (x + y).toSurreal = x.toSurreal + y.toSurreal :=
  map_add toHahnSeriesMonoidIso.symm x y

@[simp, norm_cast]
theorem _root_.SurrealHahnSeries.toSurreal_sub (x y : SurrealHahnSeries) :
    (x - y).toSurreal = x.toSurreal - y.toSurreal :=
  map_sub toHahnSeriesMonoidIso.symm x y

@[simp]
theorem support_neg {x : Surreal} : support (-x) = support x := by
  rw [support, toHahnSeries_neg, SurrealHahnSeries.support_neg, support]

theorem support_add_subset {x y : Surreal} : support (x + y) ⊆ support x ∪ support y := by
  conv_lhs => rw [← toSurreal_toHahnSeries x, ← toSurreal_toHahnSeries y, ← toSurreal_add]
  rw [support_toSurreal]
  exact SurrealHahnSeries.support_add_subset

theorem support_sub_subset {x y : Surreal} : support (x - y) ⊆ support x ∪ support y := by
  simpa [sub_eq_add_neg] using support_add_subset (y := -y)

@[simp]
theorem coeff_neg (x i : Surreal) : (-x).coeff i = -x.coeff i := by
  rw [coeff]; simp

@[simp]
theorem coeff_add (x y i : Surreal) : (x + y).coeff i = x.coeff i + y.coeff i := by
  rw [coeff]; simp

@[simp]
theorem coeff_sub (x y i : Surreal) : (x - y).coeff i = x.coeff i - y.coeff i := by
  rw [coeff]; simp

@[simp]
theorem trunc_neg (x i : Surreal) : (-x).trunc i = -x.trunc i := by
  rw [trunc]; simp

@[simp]
theorem trunc_add (x y i : Surreal) : (x + y).trunc i = x.trunc i + y.trunc i := by
  rw [trunc]; simp

@[simp]
theorem trunc_sub (x y i : Surreal) : (x - y).trunc i = x.trunc i - y.trunc i := by
  rw [trunc]; simp

@[simp]
theorem infPart_neg (x : Surreal) : infPart (-x) = -infPart x := by
  simp [infPart]; abel

@[simp]
theorem infPart_add (x y : Surreal) : infPart (x + y) = infPart x + infPart y := by
  simp [infPart]; abel

@[simp]
theorem infPart_sub (x y : Surreal) : infPart (x - y) = infPart x - infPart y := by
  simp [sub_eq_add_neg]

theorem infPart_vlt_one (x : Surreal) : infPart x <ᵥ 1 := by
  rw [infPart, coeff_eq_stdPart, wpow_zero, div_one]
  apply sub_stdPart_vlt_one
  rw [← wpow_zero]
  exact sub_trunc_vle_wpow x 0

theorem archimedeanClassMk_infPart_pos (x : Surreal) : 0 < ArchimedeanClass.mk (infPart x) :=
  vlt_def.1 (infPart_vlt_one x)

@[simp]
theorem leadingTerm_sub_trunc_of_mem_support {x i : Surreal} (hi : i ∈ x.support) :
    (x - x.trunc i).leadingTerm = x.coeff i * ω^ i := by
  rw [← toSurreal_toHahnSeries (_ - _), SurrealHahnSeries.leadingTerm_toSurreal,
    toHahnSeries_sub, term_zero_of_isGreatest i]
  · simp
  · refine ⟨?_, fun _ ↦ ?_⟩
    · simpa
    · aesop

@[simp]
theorem leadingCoeff_sub_trunc_of_mem_support {x i : Surreal} (hi : i ∈ x.support) :
    (x - x.trunc i).leadingCoeff = x.coeff i := by
  rw [← leadingCoeff_leadingTerm, leadingTerm_sub_trunc_of_mem_support hi]
  simp

end Surreal

namespace SurrealHahnSeries
open Surreal

private theorem toSurreal_single_mul (i : Surreal) (r : ℝ) (x : SurrealHahnSeries) :
    (single i r * x).toSurreal = r * ω^ i * x.toSurreal := by
  induction x using SurrealHahnSeries.lengthRecOn with
  | succ x j s hj hs IH => simp [mul_add, IH]; ring
  | limit x hx IH =>
    obtain rfl | hr := eq_or_ne r 0; · simp
    cases i with | mk i
    rw [toSurreal_def', ← mk_wpow, ← mk_real_toIGame, ← mk_mul, ← mk_toIGame, ← mk_mul,
      eq_comm, mk_eq_mk]
    have He := IGame.Numeric.realCast_mul_wpow_equiv r i
    apply IGame.Fits.equiv_of_forall_moves_of_equiv _ (IGame.Numeric.mul_congr_left He (y := x))
    · constructor
      all_goals
      · simp_rw [IGame.moves_ofSets, Player.cases, Set.forall_mem_image]
        first | rw [forall_mem_truncLT] | rw [forall_mem_truncGT]
        simp_rw [support_single_mul hr, coeff_single_mul, trunc_single_mul, IGame.Numeric.not_le]
        intro j hj s hs
        rw [← mk_lt_mk, mk_toIGame, toSurreal_add, IH _ (length_trunc_lt hj)]
        simp_rw [toSurreal_trunc, toSurreal_single, mk_mul, mk_real_toIGame, mk_wpow, mk_toIGame]
        first | rw [← lt_sub_iff_add_lt'] | rw [← sub_lt_iff_lt_add']
        rw [mul_assoc, mul_assoc, ← mul_sub, ← mul_sub, mul_comm _ (_ - _)]
        apply leadingTerm_mono.reflect_lt
        simp_all [mul_assoc]
        simpa [← mul_assoc, ← Real.toSurreal_mul]
    · simp_rw [IGame.forall_moves_mul, Player.mul_left, IGame.leftMoves_ofSets,
        Set.exists_mem_image, exists_mem_truncLT, coeff_single_mul, support_single_mul hr]
      intro p a ha b hb
      rw [IGame.moves_ofSets, ← Player.apply_cases, Set.mem_image] at ha
      obtain ⟨s, hs, rfl⟩ := ha
      rw [toIGame_limit hx, IGame.moves_ofSets, ← Player.apply_cases, Set.mem_image] at hb
      obtain ⟨j, hj, t, H, rfl⟩ : ∃ j ∈ x.support, ∃ t : ℝ,
          s * x.coeff j - s * t + r * t < r * x.coeff j ∧
          (x.trunc j + single j t).toIGame = b := by
        cases p
        all_goals
        · dsimp [Player.cases] at hb hs
          first | rw [exists_mem_truncLT] at hb | rw [exists_mem_truncGT] at hb
          first | rw [Set.mem_Iio] at hs | rw [Set.mem_Ioi] at hs
          obtain ⟨j, hj, t, ht, rfl⟩ := hb
          refine ⟨j, hj, t, ?_, rfl⟩
          rw [← sub_pos] at hs ht ⊢
          convert mul_pos hs ht
          ring
      obtain ⟨k, hk, hk'⟩ := exists_between H
      refine ⟨j + .mk i, (by simpa), k, (by simpa), le_of_lt ?_⟩
      rw [← Surreal.mk_lt_mk, mk_mulOption, ← mk_eq He]
      suffices s * (x - x.trunc j).toSurreal < ω^ j * (s * t - r * t + k :) by
        simp [IH _ (length_trunc_lt hj)] at this ⊢
        linarith only [mul_lt_mul_of_pos_left this (wpow_pos (.mk i))]
      apply leadingTerm_mono.reflect_lt
      rw [toSurreal_sub, toSurreal_trunc, leadingTerm_mul, leadingTerm_mul,
        leadingTerm_realCast, leadingTerm_sub_trunc_of_mem_support (by simpa),
        coeff_toSurreal, leadingTerm_wpow, leadingTerm_realCast, ← mul_rotate',
        mul_lt_mul_iff_of_pos_left (wpow_pos j), ← Real.toSurreal_mul, Real.toSurreal_lt_iff]
      linarith
    · simp_rw [IGame.forall_moves_mul, Player.mul_right, IGame.rightMoves_ofSets,
        Set.exists_mem_image, exists_mem_truncGT, coeff_single_mul, support_single_mul hr]
      intro p a ha b hb
      rw [IGame.moves_ofSets, ← Player.apply_cases, Set.mem_image] at ha
      obtain ⟨s, hs, rfl⟩ := ha
      rw [toIGame_limit hx, IGame.moves_ofSets, ← Player.apply_cases, Set.mem_image] at hb
      obtain ⟨j, hj, t, H, rfl⟩ : ∃ j ∈ x.support, ∃ t : ℝ,
          r * x.coeff j < s * x.coeff j - s * t + r * t ∧
          (x.trunc j + single j t).toIGame = b := by
        cases p
        all_goals
        · dsimp [Player.cases] at hb hs
          first | rw [exists_mem_truncLT] at hb | rw [exists_mem_truncGT] at hb
          first | rw [Set.mem_Iio] at hs | rw [Set.mem_Ioi] at hs
          obtain ⟨j, hj, t, ht, rfl⟩ := hb
          refine ⟨j, hj, t, ?_, rfl⟩
          rw [← sub_pos] at hs ht ⊢
          convert mul_pos hs ht
          ring
      obtain ⟨k, hk, hk'⟩ := exists_between H
      refine ⟨j + .mk i, (by simpa), k, (by simpa), le_of_lt ?_⟩
      rw [← Surreal.mk_lt_mk, mk_mulOption, ← mk_eq He]
      suffices ω^ j * (s * t - r * t + k :) < s * (x - x.trunc j).toSurreal by
        simp [IH _ (length_trunc_lt hj)] at this ⊢
        linarith only [mul_lt_mul_of_pos_left this (wpow_pos (.mk i))]
      apply leadingTerm_mono.reflect_lt
      rw [toSurreal_sub, toSurreal_trunc, leadingTerm_mul, leadingTerm_mul,
        leadingTerm_realCast, leadingTerm_sub_trunc_of_mem_support (by simpa),
        coeff_toSurreal, leadingTerm_wpow, leadingTerm_realCast, ← mul_rotate',
        mul_lt_mul_iff_of_pos_left (wpow_pos j), ← Real.toSurreal_mul, Real.toSurreal_lt_iff]
      linarith

private theorem toSurreal_single_mul' (i : Surreal) (r : ℝ) (x : SurrealHahnSeries) :
    (single i r * x).toSurreal = r * (ω^ i * x.toSurreal) := by
  rw [toSurreal_single_mul, mul_assoc]

private theorem toSurreal_single_one_mul (i : Surreal) (x : SurrealHahnSeries) :
    (single i 1 * x).toSurreal = ω^ i * x.toSurreal := by
  rw [toSurreal_single_mul, Real.toSurreal_one, one_mul]

private theorem toSurreal_single_one_mul' (i : Surreal) (x : SurrealHahnSeries) :
    (single i 1 * x).toSurreal = x.toSurreal * ω^ i := by
  rw [toSurreal_single_one_mul, mul_comm]

private theorem exists_sub_mul_sub_lt (a b : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ p < a, ∃ q < b, (a - p) * (b - q) < r := by
  obtain ⟨q, hbq, hqb⟩ := exists_between ((sub_lt_self_iff b).2 hr)
  refine ⟨_, sub_one_lt a, q, hqb, ?_⟩
  simpa [sub_lt_comm]

private theorem exists_sub_mul_sub'_gt (a b : ℝ) {r : ℝ} (hr : r < 0) :
    ∃ p < a, ∃ q > b, r < (a - p) * (b - q) := by
  obtain ⟨q, hbq, hqb⟩ := exists_between (lt_add_of_pos_right b (neg_pos.2 hr))
  refine ⟨_, sub_one_lt a, q, hbq, ?_⟩
  simpa [lt_sub_iff_add_lt'] using hqb

private theorem exists_sub'_mul_sub_gt (a b : ℝ) {r : ℝ} (hr : r < 0) :
    ∃ p > a, ∃ q < b, r < (a - p) * (b - q) := by
  obtain ⟨q, hq, p, hp, h⟩ := exists_sub_mul_sub'_gt b a hr
  refine ⟨p, hp, q, hq, ?_⟩
  rwa [mul_comm]

@[simp]
theorem toSurreal_mul (x y : SurrealHahnSeries) :
    (x * y).toSurreal = x.toSurreal * y.toSurreal := by
  induction x using SurrealHahnSeries.lengthRecOn with
  | succ x i r _ _ IH => simpa [add_mul, toSurreal_single_mul]
  | limit x IH =>
    rw [← mk_toIGame, toSurreal_def', toSurreal_def', ← mk_mul, mk_eq_mk]
    apply IGame.Fits.equiv_of_forall_moves_of_equiv _ (toIGame_equiv _)
    · constructor
      · intro y hy
        sorry
      · sorry
    · sorry
      /-simp_rw [IGame.leftMoves_ofSets, Set.forall_mem_image, IGame.exists_moves_mul,
        Player.mul_left, forall_mem_truncLT, mem_support_iff]
      intro i hab r hr
      obtain ⟨a, ha, b, hb, rfl⟩ := support_mul_subset hab
      obtain ⟨p, hp, q, hq, hpq⟩ := exists_sub_mul_sub_lt (x.coeff a) (y.coeff b) (sub_pos.2 hr)
      refine ⟨.left, (x.trunc a + single a p :), ?_, (y.trunc b + single b q :), ?_, ?_⟩
      · rw [IGame.leftMoves_ofSets, Set.mem_image, exists_mem_truncLT]
        exact ⟨a, ha, _, hp, rfl⟩
      · rw [IGame.leftMoves_ofSets, Set.mem_image, exists_mem_truncLT]
        exact ⟨b, hb, _, hq, rfl⟩
      · simp_rw [← Surreal.mk_le_mk, mk_toIGame, Surreal.mk_mulOption, ← toSurreal_def',
          mk_toIGame, toSurreal_add, add_mul, mul_add, toSurreal_single]
        repeat rw [← toSurreal_mul]
        rw [← toSurreal_single_mul, ← toSurreal_single_mul, mul_rotate' x.toSurreal,
          ← toSurreal_single_mul', mul_rotate', ← toSurreal_single_mul', mul_mul_mul_comm,
          ← Real.toSurreal_mul, ← wpow_add]
        simp only [← toSurreal_single, ← toSurreal_add, ← toSurreal_sub]
        rw [toSurreal_le_toSurreal_iff]
        suffices (x - x.trunc a) * (y - y.trunc b) -
            (x - x.trunc a) * single b q - single a p * (y - y.trunc b) +
            (single (a + b) (p * q) + single (a + b) r) ≤ x * y - (x * y).trunc (a + b) by
          linarith only [this]
        rw [← single_add]
        apply (lt_of_support_subset_of_lt (a + b) _ support_sub_trunc _).le
        · apply_rules [support_add_subset_of_subset, support_sub_subset_of_subset]
          · grw [support_mul_subset, support_sub_trunc, support_sub_trunc, Set.Iic_add_Iic_subset]
          · grw [support_mul_single_subset, support_sub_trunc]
            simp
          · grw [support_single_mul_subset, support_sub_trunc]
            simp [add_comm]
          · exact support_single_subset.trans (by simp)
        · simp [coeff_mul_add_of_support_subset, support_sub_trunc]
          linarith only [hpq]-/
    · sorry
      /-simp_rw [IGame.rightMoves_ofSets, Set.forall_mem_image, IGame.exists_moves_mul,
        Player.mul_right, forall_mem_truncGT, mem_support_iff]
      intro i hab r hr
      obtain ⟨a, ha, b, hb, rfl⟩ := support_mul_subset hab
      obtain ⟨p, hp, q, hq, hpq⟩ := exists_sub'_mul_sub_gt (x.coeff a) (y.coeff b) (sub_neg.2 hr)
      refine ⟨.right, (x.trunc a + single a p :), ?_, (y.trunc b + single b q :), ?_, ?_⟩
      · rw [IGame.rightMoves_ofSets, Set.mem_image, exists_mem_truncGT]
        exact ⟨a, ha, _, hp, rfl⟩
      · rw [Player.neg_right, IGame.leftMoves_ofSets, Set.mem_image, exists_mem_truncLT]
        exact ⟨b, hb, _, hq, rfl⟩
      · simp_rw [← Surreal.mk_le_mk, mk_toIGame, Surreal.mk_mulOption, ← toSurreal_def',
          mk_toIGame, toSurreal_add, add_mul, mul_add, toSurreal_single]
        repeat rw [← toSurreal_mul]
        rw [← toSurreal_single_mul, ← toSurreal_single_mul, mul_rotate' x.toSurreal,
          ← toSurreal_single_mul', mul_rotate', ← toSurreal_single_mul', mul_mul_mul_comm,
          ← Real.toSurreal_mul, ← wpow_add]
        simp only [← toSurreal_single, ← toSurreal_add, ← toSurreal_sub]
        rw [toSurreal_le_toSurreal_iff]
        suffices x * y - (x * y).trunc (a + b) ≤ (x - x.trunc a) * (y - y.trunc b) -
            (x - x.trunc a) * single b q - single a p * (y - y.trunc b) +
            (single (a + b) (p * q) + single (a + b) r) by
          linarith only [this]
        rw [← single_add]
        apply (lt_of_support_subset_of_lt (a + b) support_sub_trunc _ _).le
        -- This is the same as above.
        · apply_rules [support_add_subset_of_subset, support_sub_subset_of_subset]
          · grw [support_mul_subset, support_sub_trunc, support_sub_trunc, Set.Iic_add_Iic_subset]
          · grw [support_mul_single_subset, support_sub_trunc]
            simp
          · grw [support_single_mul_subset, support_sub_trunc]
            simp [add_comm]
          · exact support_single_subset.trans (by simp)
        · simp [coeff_mul_add_of_support_subset, support_sub_trunc]
          linarith only [hpq]-/
termination_by (x, y)
decreasing_by all_goals sorry

end SurrealHahnSeries
