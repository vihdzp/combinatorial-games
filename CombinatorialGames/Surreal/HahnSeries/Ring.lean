/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.HahnSeries.Transfer
import CombinatorialGames.Surreal.Omnific.Basic

/-!
# Ring isomorphism between surreals and Hahn series

We prove here that `Surreal` and `SurrealHahnSeries` are isomorphic as ordered rings.

Conway omits this proof entirely. This file is based on pages 429-431 of Siegel.
-/

universe u

noncomputable section

namespace Surreal
open ArchimedeanClass Order Set SurrealHahnSeries

/-! ### Addition -/

namespace PartialSum

variable {x y : Surreal} (h : x.support ⊆ Ioi y.wlog)

variable (x y) in
/-- `x` as a partial sum of `x + y`. -/
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

@[simp] theorem carrier_ofAdd : (ofAdd x y h).carrier = x.toHahnSeries := rfl
@[simp] theorem length_ofAdd : (ofAdd x y h).length = x.length := rfl

theorem truncIdx_top_add_length {x y : Surreal}
    (h : x.support ⊆ Ioi y.wlog) : (⊤ : PartialSum (x + y)).truncIdx x.length = ofAdd x y h :=
  PartialSum.truncIdx_length_of_le (y := ofAdd x y h) le_top

@[simp]
theorem term_succ_ofAdd_length {x y : Surreal} (h : x.support ⊆ Ioi y.wlog) :
    (succ (ofAdd x y h)).carrier.term x.length = y.leadingTerm := by
  rw [← length_ofAdd h, term_succ_length, carrier_ofAdd,
    toSurreal_toHahnSeries, add_sub_cancel_left]

end PartialSum

private theorem truncIdx_add_length_of_subset {x y : Surreal}
    (hx : x.support ⊆ Ioi y.wlog) : (x + y).toHahnSeries.truncIdx x.length = x := by
  have := congrArg PartialSum.carrier (PartialSum.truncIdx_top_add_length hx)
  aesop

private theorem le_length_add_of_subset {x y : Surreal}
    (hx : x.support ⊆ Ioi y.wlog) : x.length ≤ (x + y).length := by
  conv_lhs => rw [← truncIdx_add_length_of_subset hx]
  simp

open PartialSum in
private theorem lt_length_add_of_subset {x y : Surreal}
    (hx : x.support ⊆ Ioi y.wlog) (hy' : y ≠ 0) : x.length < (x + y).length := by
  apply (le_length_add_of_subset hx).lt_of_ne
  change (ofAdd x y hx).length ≠ PartialSum.length ⊤
  rw [ne_eq, length_inj]
  apply_fun carrier
  simpa

open PartialSum in
private theorem trunc_add_of_subset {x y i : Surreal}
    (hx : x.support ⊆ Ioi i) (hy : y ≤ᵥ ω^ i) : (x + y).trunc i = x := by
  obtain rfl | hy' := eq_or_ne y 0
  · rw [add_zero, trunc_eq_self]
    simpa
  have hy'' : y.wlog ≤ i := by simpa using wlog_le_wlog_of_vle hy' hy
  have hx' : x.support ⊆ Ioi y.wlog := hx.trans (by simpa)
  · have hl := lt_length_add_of_subset hx' hy'
    conv_rhs => rw [← truncIdx_add_length_of_subset hx']
    rw [truncIdx_of_lt hl]
    · apply (trunc_eq_trunc (hy''.trans_eq' _) _).symm
      · convert PartialSum.exp_congr (y := succ (.ofAdd x y hx')) _ _
        · rw [← wlog_term, term_succ_ofAdd_length, wlog_leadingTerm]
        · rw [← PartialSum.length_ofAdd hx'] at hl ⊢
          exact lt_succ_of_not_isMax (hl.not_isMax (α := PartialSum _))
      · sorry

private theorem coeff_add_of_subset {x y i : Surreal}
    (hx : x.support ⊆ Ioi i) (hy : y ≤ᵥ ω^ i) :
    (x + y).coeff i = stdPart (y / ω^ i) := by
  sorry

theorem coeff_eq_stdPart {x i : Surreal} : x.coeff i = stdPart ((x - x.trunc i) / ω^ i) := by
  conv_lhs => rw [← add_sub_cancel (x.trunc i) x]
  apply coeff_add_of_subset
  · simp
  · sorry

theorem support_subset_of_round_eq {x y : Surreal} (hx : x.round y = x) (hy : 0 < y) :
    support x ⊆ Ici y.wlog := by
  intro z hzy
  rw [mem_Ici]
  contrapose! hzy
  intro hz
  obtain ⟨i, rfl⟩ := eq_exp_of_mem_support hz
  have H : ArchimedeanClass.mk y < .mk (x - x.toHahnSeries.truncIdx i) := by
    nth_rw 1 [← toSurreal_toHahnSeries x]
    conv_rhs => rw [← mk_leadingTerm, leadingTerm_sub_truncIdx, mk_term i.2]
    rw [← vlt_def, ← wlog_lt_wlog_iff (by simp) hy.ne']
    simpa
  refine (@birthday_round_le x (x.toHahnSeries.truncIdx i) y ⟨?_, ?_⟩).not_gt ?_
  · rw [sub_lt_comm]
    exact lt_of_mk_lt_mk_of_nonneg H hy.le
  · rw [← sub_lt_iff_lt_add']
    apply lt_of_mk_lt_mk_of_nonneg _ hy.le
    rwa [mk_sub_comm]
  · apply (birthday_truncIdx_lt i.2).trans_eq
    simp [hx]

theorem support_subset_of_round_wpow_eq {x y : Surreal} (h : x.round (ω^ y) = x) :
    support x ⊆ Ici y := by
  simpa using support_subset_of_round_eq h

theorem IsOmnific.support_subset {x : Surreal} (h : IsOmnific x) : support x ⊆ Ici 0 := by
  simpa using support_subset_of_round_eq h

theorem eq_round_of_support_subset {x y : Surreal}
    (hx : x.support ⊆ Ioi y.wlog) (hz : 0 < y) : x.round y = x := by
  apply round_eq_of_forall_birthday_le
  · simpa
  · intro w hw
    convert birthday_trunc_le w.toHahnSeries y
    · sorry
    · exact (toSurreal_toHahnSeries w).symm

theorem eq_round_wpow_of_support_subset {x y : Surreal} (hx : x.support ⊆ Ioi y) :
    x.round (ω^ y) = x :=
  eq_round_of_support_subset (by simpa) (by simp)

/-- This is a special case of `support_add_subset`. -/
private theorem support_add_subset_Ioi {x y z : Surreal}
    (hx : x.support ⊆ Ioi z) (hy : y.support ⊆ Ioi z) : (x + y).support ⊆ Ioi z := by
  apply (support_subset_of_round_wpow_eq (y := !{{z} | x.support ∪ y.support}) _).trans
  · aesop
  · apply round_add_of_eq
    all_goals
      refine eq_round_wpow_of_support_subset fun w hw ↦ ?_
      aesop

@[simp, norm_cast]
theorem toHahnSeries_add (x y : Surreal) :
    (x + y).toHahnSeries = x.toHahnSeries + y.toHahnSeries := by
  ext i
  rw [coeff_toHahnSeries, coeff_add_apply]
  trans ((x.trunc i + y.trunc i) + ((x - x.trunc i) + (y - y.trunc i))).coeff i
  · abel_nf
  · rw [coeff_add_of_subset, add_div, stdPart_add]
    · simp [coeff_eq_stdPart]
    · sorry
    · sorry
    · apply support_add_subset_Ioi <;> simp
    · apply ValuativeRel.vle_add <;> sorry

@[simps!]
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

end Surreal
