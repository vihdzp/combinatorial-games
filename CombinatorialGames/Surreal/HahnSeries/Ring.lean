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

Conway omits this proof entirely. This file is loosely based on pages 429-431 of Siegel.

## Addition

For this proof, we reuse the `PartialSeq` API that we created in order to show the equivalence
between surreals and Hahn sequences. We notice that if `y.support < x.support` pairwise, then `x` is
a partial sum for `x + y`. This lets us relate the Hahn series of both.



TODO: finish writing
-/

universe u

noncomputable section

lemma LinearOrderedAddCommGroupWithTop.sub_nonneg {α} [LinearOrderedAddCommGroupWithTop α]
    {a b : α} : 0 ≤ a - b ↔ b ≤ a ∨ b = ⊤ := by
  obtain rfl | hb := eq_or_ne b ⊤
  · simp
  · simp [← sub_self_eq_zero_of_ne_top hb, hb]

namespace Surreal
open ArchimedeanClass Order Set SurrealHahnSeries

/-! ### Addition -/

section Addition
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

@[simp] theorem carrier_ofAdd : (ofAdd x y h).carrier = x.toHahnSeries := rfl
@[simp] theorem length_ofAdd : (ofAdd x y h).length = x.length := rfl

theorem truncIdx_top_add_length : (⊤ : PartialSum (x + y)).truncIdx x.length = ofAdd x y h :=
  truncIdx_length_of_le (y := ofAdd x y h) le_top

@[simp]
theorem term_succ_ofAdd_length : (succ (ofAdd x y h)).carrier.term x.length = y.leadingTerm := by
  rw [← length_ofAdd h, term_succ_length, carrier_ofAdd, toSurreal_toHahnSeries,
    add_sub_cancel_left]

end PartialSum

private theorem truncIdx_add_length_of_subset : (x + y).toHahnSeries.truncIdx x.length = x := by
  apply toSurreal_eq
  simpa using congrArg carrier (truncIdx_top_add_length h).symm

theorem le_length_add_of_subset : x.length ≤ (x + y).length := by
  conv_lhs => rw [← truncIdx_add_length_of_subset h]
  simp

theorem lt_length_add_of_subset (hy : y ≠ 0) : x.length < (x + y).length := by
  apply (le_length_add_of_subset h).lt_of_ne
  change (ofAdd x y h).length ≠ PartialSum.length ⊤
  rw [ne_eq, length_inj]
  apply_fun carrier
  simpa

private theorem term_add_length_of_subset : (x + y).toHahnSeries.term x.length = y.leadingTerm := by
  obtain rfl | hy := eq_or_ne y 0; · simp
  apply ((⊤ : PartialSum (x + y)).term_eq_leadingTerm_sub (lt_length_add_of_subset h hy)).trans
  rw [carrier_top, truncIdx_add_length_of_subset h, add_sub_cancel_left]

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
  rw [hl, SurrealHahnSeries.toSurreal_trunc, toSurreal_toHahnSeries]
  refine (trunc_eq_trunc hy fun k hek hki ↦ ?_).symm
  contrapose! hki
  apply hx
  rw [← truncIdx_add_length_of_subset hx', hl, SurrealHahnSeries.toSurreal_trunc,
    toSurreal_toHahnSeries, support_trunc]
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

private theorem mk_sub_trunc_div_wpow_nonneg {x i : Surreal} :
    0 ≤ ArchimedeanClass.mk ((x - x.trunc i) / ω^ i) := by
  rw [ArchimedeanClass.mk_div, LinearOrderedAddCommGroupWithTop.sub_nonneg, ← vle_def]
  exact .inl (sub_trunc_vle_wpow x i)

theorem coeff_eq_stdPart {x i : Surreal} : x.coeff i = stdPart ((x - x.trunc i) / ω^ i) := by
  conv_lhs => rw [← add_sub_cancel (x.trunc i) x]
  apply coeff_add_of_subset _ (sub_trunc_vle_wpow x i)
  simp

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

/-- Omnific integers have no infinitesimal part. -/
theorem IsOmnific.support_subset {x : Surreal} (h : IsOmnific x) : support x ⊆ Ici 0 := by
  simpa using support_subset_of_round_eq h

-- AI
include h in
theorem eq_round_of_support_subset (hy : 0 < y) : x.round y = x := by
  apply round_eq_of_forall_birthday_le
  · simpa
  · intro w hw
    convert SurrealHahnSeries.birthday_trunc_le w.toHahnSeries y.wlog
    · symm
      rw [SurrealHahnSeries.toSurreal_trunc, toSurreal_toHahnSeries]
      calc
        w.trunc y.wlog = (x + (w - x)).trunc y.wlog := by
          congr 2
          abel
        _ = x := trunc_add_of_subset h <| by
          have habs : |w - x| < y := by
            rw [abs_lt]
            constructor <;> linarith [hw.1, hw.2]
          apply ValuativeRel.vle_trans _ (wpow_wlog_veq hy.ne').symm.1
          rw [vle_def]
          exact ArchimedeanClass.mk_le_mk_of_abs (by simpa [abs_of_pos hy] using habs.le)
    · exact (toSurreal_toHahnSeries w).symm

theorem eq_round_wpow_of_support_subset {x y : Surreal} (hx : x.support ⊆ Ioi y) :
    x.round (ω^ y) = x :=
  eq_round_of_support_subset (by simpa) (by simp)

/-- This is a special case of `support_add_subset`. -/
private theorem support_add_subset_Ioi {z : Surreal}
    (hx : x.support ⊆ Ioi z) (hy : y.support ⊆ Ioi z) : (x + y).support ⊆ Ioi z := by
  apply (support_subset_of_round_wpow_eq (y := !{{z} | x.support ∪ y.support}) _).trans
  · aesop
  · apply round_add_of_eq
    all_goals
      refine eq_round_wpow_of_support_subset fun w hw ↦ ?_
      aesop

-- AI
@[simp, norm_cast]
theorem toHahnSeries_add (x y : Surreal) :
    (x + y).toHahnSeries = x.toHahnSeries + y.toHahnSeries := by
  ext i
  rw [coeff_toHahnSeries, SurrealHahnSeries.coeff_add_apply]
  trans ((x.trunc i + y.trunc i) + ((x - x.trunc i) + (y - y.trunc i))).coeff i
  · abel_nf
  · rw [coeff_add_of_subset, add_div,
      stdPart_add mk_sub_trunc_div_wpow_nonneg mk_sub_trunc_div_wpow_nonneg]
    · rw [coeff_toHahnSeries x, coeff_toHahnSeries y, coeff_eq_stdPart, coeff_eq_stdPart]
    · apply support_add_subset_Ioi <;> simp
    · apply ValuativeRel.vle_add <;> exact sub_trunc_vle_wpow _ _

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

end Addition
end Surreal
