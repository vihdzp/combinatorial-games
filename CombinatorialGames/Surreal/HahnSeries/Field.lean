/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.HahnSeries.Surreal

/-!

Conway omits this proof entirely. This file is based on pages 429-431 of Siegel.
-/

namespace Surreal
open SurrealHahnSeries

/-- We say that a surreal is `y`-truncated when every element in the support of its Hahn series is
larger than `y`.

This is an auxiliary definition towards showing the ring isomorphism between surreals and their Hahn
series. -/
def IsTruncated (x : Surreal) (y : Surreal) : Prop :=
  ∀ z ∈ x.toHahnSeries.support, y < z

attribute [local simp] sub_eq_add_neg in
theorem isTruncated_ofSets (x : Surreal) {y z : Surreal} (h : y < z) :
    IsTruncated !{{x - ω^ z} | {x + ω^ z}} y := by
  sorry

#exit
attribute [local simp] sub_eq_add_neg in
theorem isTruncated_iff {x y : Surreal} :
    IsTruncated x y ↔ ∃ z, y < z ∧ x = !{{x - ω^ z} | {x + ω^ z}} where
  mp h := by
    let y' := !{{y} | x.toHahnSeries.support}'(by grind [IsTruncated])
    have hy : y < y' := by aesop
    refine ⟨_, hy, ?_⟩
    conv_lhs => rw [← Surreal.out_eq x]
    rw [ofSets_eq_mk]
    refine (@mk_eq_mk _ _ _ ?_).2 ?_
    apply IGame.Fits.equiv_of_forall_moves_of_equiv
      !{toIGame '' x.toHahnSeries.truncLT | toIGame '' x.toHahnSeries.truncGT}
    · rw [← mk_eq_mk, out_eq, ← toSurreal_eq', toSurreal_toHahnSeries]
    · simp [IGame.Fits]
    · simp only [game_cmp, forall_mem_truncLT]
      intro z hz r hr
      have hz' := h z hz
      have hy' : y' < z := by aesop
      rw [← mk_le_mk, out_eq, mk_toIGame]
      have hx := @toSurreal_succ x.toHahnSeries y' (-1) (by aesop)
      rw [toSurreal_toHahnSeries, Real.toSurreal_neg, Real.toSurreal_one, neg_one_mul] at hx
      rw [← hx, toSurreal_le_toSurreal_iff, le_def]
      refine le_of_lt ⟨z, fun i hi ↦ ?_, ?_⟩ <;> dsimp
      · rw [coeff_trunc_of_lt hi, coeff_single_of_ne hi.ne, coeff_single_of_ne]
        rintro rfl
        exact hy'.not_gt hi
      · rw [coeff_trunc_of_le le_rfl, coeff_single_self, coeff_single_of_ne hy'.ne]
        simpa
    -- TODO: unify?
    · simp only [game_cmp, forall_mem_truncGT]
      intro z hz r hr
      have hz' := h z hz
      have hy' : y' < z := by aesop
      rw [← mk_le_mk, out_eq, mk_toIGame]
      have hx := @toSurreal_succ x.toHahnSeries y' 1 (by aesop)
      rw [toSurreal_toHahnSeries, Real.toSurreal_one, one_mul] at hx
      rw [← hx, toSurreal_le_toSurreal_iff, le_def]
      refine le_of_lt ⟨z, fun i hi ↦ ?_, ?_⟩ <;> dsimp
      · rw [coeff_trunc_of_lt hi, coeff_single_of_ne hi.ne, coeff_single_of_ne]
        rintro rfl
        exact hy'.not_gt hi
      · rw [coeff_trunc_of_le le_rfl, coeff_single_self, coeff_single_of_ne hy'.ne]
        simpa
  mpr := fun ⟨z, hz, hx⟩ ↦ hx ▸ isTruncated_ofSets x hz

end Surreal
