/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Surreal.HahnSeries.Ring

/-!
# Characterization of omnific integers by Hahn series

We show that omnific integers are exactly those whose support is contained in the nonnegative
surreals, and whose zero coefficient is an integer.
-/

public noncomputable section

open Set

namespace Surreal
variable {x y : Surreal}

theorem IsOmnific.support_subset (h : IsOmnific x) : support x ⊆ Ici 0 := by
  simpa using support_subset_of_round_eq h

theorem IsOmnific.coeff_eq_zero_of_lt (h : IsOmnific x) (hy : y < 0) : x.coeff y = 0 := by
  rw [← notMem_support_iff]
  exact fun hyx ↦ (h.support_subset hyx).not_gt hy

theorem IsOmnific.of_support_subset_Ioi (hx : x.support ⊆ Ioi 0) : IsOmnific x := by
  apply round_eq_of_support_subset _ zero_lt_one
  simpa

@[simp]
theorem IsOmnific.trunc_zero (x : Surreal) : IsOmnific (x.trunc 0) := by
  apply IsOmnific.of_support_subset_Ioi
  simp

theorem IsOmnific.trunc_add_coeff_eq (h : IsOmnific x) : x.trunc 0 + x.coeff 0 = x := by
  ext i
  rw [coeff_add, coeff_realCast]
  obtain hi | rfl | hi := lt_trichotomy i 0
  · rw [coeff_trunc_of_le hi.le, Pi.single_eq_of_ne hi.ne, zero_add, h.coeff_eq_zero_of_lt hi]
  · rw [coeff_trunc_of_le le_rfl, Pi.single_eq_same, zero_add]
  · rw [coeff_trunc_of_lt hi, Pi.single_eq_of_ne hi.ne', add_zero]

theorem IsOmnific.coeff_zero_mem_range_intCast (h : IsOmnific x) :
    x.coeff 0 ∈ range ((↑) : ℤ → _) := by
  rwa [← isOmnific_realCast_iff, ← isOmnific_add_iff_right (.trunc_zero x), h.trunc_add_coeff_eq]

theorem isOmnific_iff_subset_and_mem_range :
    IsOmnific x ↔ support x ⊆ Ici 0 ∧ x.coeff 0 ∈ range ((↑) : ℤ → _) where
  mp hx := ⟨hx.support_subset, hx.coeff_zero_mem_range_intCast⟩
  mpr := by
    intro ⟨hx, ⟨n, hn⟩⟩
    rw [← isOmnific_sub_iff_left (.intCast n), ← Real.toSurreal_intCast, hn]
    apply IsOmnific.of_support_subset_Ioi
    rw [← Ici_sdiff_left]
    apply subset_sdiff_singleton
    · apply support_sub_subset.trans (union_subset hx <| support_realCast_subset.trans _)
      simp
    · simp

@[simp]
theorem isOmnific_wpow_iff : IsOmnific (ω^ x) ↔ 0 ≤ x := by
  rw [isOmnific_iff_subset_and_mem_range]
  aesop

end Surreal
end
