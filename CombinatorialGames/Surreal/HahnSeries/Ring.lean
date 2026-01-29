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
open Set SurrealHahnSeries

/-! ### Addition -/

def PartialSum.ofAdd {x : SurrealHahnSeries} {y i : Surreal}
    (hx : x.support ⊆ Ioi i) (hy : y.wlog ≤ i) : PartialSum (x + y) where
  carrier := x
  term_eq_leadingTerm_sub {i} hi := by
    rw [← leadingTerm_sub_truncIdx, add_sub_right_comm, leadingTerm_add_eq_left]
    rw [vlt_def]


    sorry

#exit
theorem sus {x y : SurrealHahnSeries} {i j : Surreal}
    (hx : x.trunc j = y) (hx' : y.support ⊆ Iio i) : x.trunc i = y :=
  sorry

/-- This is a special case of `trunc_add`. -/
private theorem trunc_add_of_lt {x : SurrealHahnSeries} {y i : Surreal}
    (hx : x.support ⊆ Iio i) (hy : y.wlog ≤ i) : (x + y).trunc i = x := by
  let z : PartialSum (x + y) := ⟨x, sorry⟩
  obtain ⟨j, hj : _ = x.toSurreal⟩ := z.mem_range_trunc
  rw [trunc, toSurreal_inj] at hj ⊢
  apply sus hj hx

theorem support_subset_of_round_eq {x y : Surreal} (hx : x.round y = x) (hy : 0 < y) :
    support x ⊆ Ici y.wlog := by
  intro z hzy
  rw [mem_Ici]
  contrapose! hzy
  intro hz
  obtain ⟨i, rfl⟩ := eq_exp_of_mem_support hz
  have H : ArchimedeanClass.mk y < .mk (x - x.toHahnSeries.truncIdx i) := by
    nth_rw 1 [← toSurreal_toHahnSeries x]
    conv_rhs => rw [← mk_leadingTerm, leadingTerm_sub_truncIdx, mk_term _ i.2]
    rw [← vlt_def, ← wlog_lt_wlog_iff (by simp) hy.ne']
    simpa
  refine (@birthday_round_le x (x.toHahnSeries.truncIdx i) y ⟨?_, ?_⟩).not_gt ?_
  · rw [sub_lt_comm]
    exact ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg H hy.le
  · rw [← sub_lt_iff_lt_add']
    apply ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg _ hy.le
    rwa [ArchimedeanClass.mk_sub_comm]
  · apply (birthday_truncIdx_lt i.2).trans_eq
    simp [hx]

theorem support_subset_of_round_wpow_eq {x y : Surreal} (h : x.round (ω^ y) = x) :
    support x ⊆ Ici y := by
  simpa using support_subset_of_round_eq h

theorem IsOmnific.support_subset {x : Surreal} (h : IsOmnific x) : support x ⊆ Ici 0 := by
  simpa using support_subset_of_round_eq h

theorem eq_round_of_support_subset {x y z : Surreal}
    (hx : x.support ⊆ Ioi y) (hy : z.wlog ≤ y) (hz : 0 < z) : x.round z = x := by
  apply round_eq_of_forall_birthday_le
  · simpa
  · intro w hw
    convert birthday_trunc_le w.toHahnSeries y
    · sorry
    · exact (toSurreal_toHahnSeries w).symm

theorem eq_round_wpow_of_support_subset {x y : Surreal} (hx : x.support ⊆ Ioi y) :
    x.round (ω^ y) = x := by
  apply eq_round_of_support_subset hx <;> simp

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
  sorry

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
