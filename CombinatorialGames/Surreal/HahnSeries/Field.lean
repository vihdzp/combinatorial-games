/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.HahnSeries.Surreal
import CombinatorialGames.Surreal.Omnific.Basic

/-!

Conway omits this proof entirely. This file is based on pages 429-431 of Siegel.
-/

universe u

namespace Surreal
open Set SurrealHahnSeries

/-- The support of a surreal's Conway normal form. -/
def support (x : Surreal) : Set Surreal :=
  x.toHahnSeries.support

@[simp]
theorem support_toSurrealHahnSeries (x : Surreal) : x.toHahnSeries.support = x.support :=
  rfl

@[simp]
theorem SurrealHahnSeries.support_toSurreal (x : SurrealHahnSeries) :
    x.toSurreal.support = x.support := by
  simp [support]

@[simp] theorem support_zero : support 0 = ∅ := by simp [support]
@[simp] theorem support_one : support 1 = {0} := by simp [support]
@[simp] theorem support_wpow (x : Surreal) : support (ω^ x) = {x} := by aesop (add simp [support])

@[simp]
theorem support_eq_empty {x : Surreal} : x.support = ∅ ↔ x = 0 := by
  rw [support, SurrealHahnSeries.support_eq_empty, toHahnSeries_eq_zero]

instance (x : Surreal.{u}) : Small.{u} x.support :=
  inferInstanceAs (Small (SurrealHahnSeries.support _))

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

/-
theorem support_subset_Ioi_iff {x y : Surreal} :
    x.support ⊆ Ioi y ↔ ∃ z, y < z ∧ x.round (ω^ z) = x where
  mp h := by
    have H : ∀ a ∈ ({y} : Set _), ∀ b ∈ x.support, a < b := by aesop
    let z := !{{y} | x.support}
    refine ⟨z, ?_, ?_⟩
    · exact lt_ofSets_of_mem_left (mem_singleton _)
    · rw [eq_round_of_support_subset (y := z) _ (by simp) (by simp)]
      exact fun w ↦ ofSets_lt_of_mem_right (H := H)
  mpr := by
    rintro ⟨z, hz, hx⟩
    apply (support_subset_of_round_eq hx (wpow_pos _)).trans
    simpa
-/

theorem support_add_subset_Ioi {x y z : Surreal} (hx : x.support ⊆ Ioi z) (hy : y.support ⊆ Ioi z) :
    (x + y).support ⊆ Ioi z := by
  apply (support_subset_of_round_wpow_eq (y := !{{z} | x.support ∪ y.support}) _).trans
  · aesop
  · apply round_add_of_eq
    all_goals
      refine eq_round_wpow_of_support_subset fun w hw ↦ ?_
      aesop

end Surreal
