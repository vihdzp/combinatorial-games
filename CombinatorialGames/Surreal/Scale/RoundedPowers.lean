/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Scale.Rounding

import Mathlib.Tactic.Positivity.Finset

/-!
# Rounding products with translated powers

Removing a sufficiently early rounding from the base of a power leaves a factor whose
multiplication commutes with rounding at the specified positive precision.
-/

universe u

open scoped Pointwise

public noncomputable section

namespace Surreal

variable (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex]

local notation "A" => unitExponentSubgroup C
local notation "B" => infinitesimals C
local notation "U" => residueRepresentatives C
local notation "D[" t "]" => (ω^ (t : Surreal) • infinitesimals C)

/-- Dividing a simplest precision exponent by a nonzero natural number preserves fixedness. -/
theorem cosetRep_unitExponentSubgroup_div_natCast_eq {x : Surreal.{u}} (hx : cosetRep A x = x)
    {n : ℕ} (hn : n ≠ 0) : cosetRep A (x / n) = x / n := by
  have hn' : (n : Surreal.{u}) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hdiv : n • (x / n : Surreal.{u}) = x := by
    rw [nsmul_eq_mul, mul_comm, div_mul_cancel₀ _ hn']
  have h := (cosetRepAddHom A).map_nsmul n (x / n)
  rw [cosetRepAddHom_apply, cosetRepAddHom_apply, hdiv, hx, nsmul_eq_mul] at h
  exact (eq_div_iff hn').mpr ((mul_comm _ _).trans h.symm)

private theorem precisionLevel_pow {x : Surreal.{u}} (hx : x ≠ 0) (n : ℕ) :
    precisionLevel C (x ^ n) = (n : Surreal.{u}) * precisionLevel C x := by
  induction n with
  | zero => rw [pow_zero, ← wpow_zero, precisionLevel_wpow, cosetRep_zero, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [pow_succ, precisionLevel_mul C (pow_ne_zero _ hx) hx, ih, Nat.cast_succ, add_mul, one_mul]

private theorem roundAt_mul_eq_of_sub_mul_mem {t c w : Surreal.{u}} (hw : w ∈ U)
    (h : (c - cosetRep D[t] c) * w ∈ D[t]) :
    roundAt C t (c * w) = roundAt C t c * w := by
  have hcong : roundAt C t (c * w) = roundAt C t (cosetRep D[t] c * w) := by
    simp only [roundAt_eq]
    apply cosetRep_eq_of_sub_mem
    rw [← sub_div, ← sub_mul]
    exact (mem_smul_addSubgroup_iff_div_mem (wpow_ne_zero _)).mp h
  rw [hcong, cosetRep_wpow_smul, ← roundAt_eq, roundAt_eq C t (_ * w), mul_assoc,
    mul_div_cancel_left₀ _ (wpow_ne_zero _), (mem_residueRepresentatives_iff C).mp
      ((U).mul_mem (roundAt_mem_residueRepresentatives C t c) hw)]

/-- At positive precision `t`, some smaller positive precision gives a rounded part `a`
of `x` for which rounding `c * (x - a) ^ n` amounts to rounding the coefficient `c`. -/
theorem exists_roundAt_mul_sub_pow {t : Surreal.{u}} (ht : 0 < t) (htfix : cosetRep A t = t)
    (c : Surreal.{u}) {x : Surreal.{u}} (hx : x ∈ U) {n : ℕ} (hn : 0 < n) :
    ∃ s : Surreal.{u}, 0 < s ∧ s < t ∧ cosetRep A s = s ∧
      roundAt C t (c * (x - cosetRep D[s] x) ^ n) =
        roundAt C t c * (x - cosetRep D[s] x) ^ n := by
  let e := c - cosetRep D[t] c
  have he : e ∈ D[t] := sub_cosetRep_mem _ _
  by_cases he₀ : e = 0
  · let s := t / 2
    refine ⟨s, half_pos ht, half_lt_self ht, ?_, ?_⟩
    · exact cosetRep_unitExponentSubgroup_div_natCast_eq C htfix (n := 2) (by decide)
    · apply roundAt_mul_eq_of_sub_mul_mem C
      · exact (U).pow_mem ((U).sub_mem hx
          (cosetRep_wpow_smul_mem_residueRepresentatives C (half_pos ht).le x)) _
      · simpa only [show c - cosetRep D[t] c = 0 from he₀, zero_mul] using (D[t]).zero_mem
  have heLevel : precisionLevel C e < t :=
    (mem_wpow_smul_infinitesimals_iff C he₀ htfix).mp he
  let δ := min t (t - precisionLevel C e)
  have hδ : 0 < δ := lt_min ht (sub_pos.mpr heLevel)
  have hδfix : cosetRep A δ = δ := by
    dsimp only [δ]
    rw [(monotone_cosetRep A).map_min, cosetRep_sub, htfix, cosetRep_precisionLevel]
  let s := δ / (↑(n + 2) : Surreal.{u})
  have hden : 0 < (↑(n + 2) : Surreal.{u}) := by positivity
  have hs : 0 < s := div_pos hδ hden
  have hsmall : s < δ := by
    apply (div_lt_iff₀ hden).mpr
    have hn' : (1 : Surreal.{u}) < (↑(n + 2) : Surreal.{u}) := by
      exact_mod_cast (show 1 < n + 2 by omega)
    simpa only [mul_one] using mul_lt_mul_of_pos_left hn' hδ
  have hrs : s < t := hsmall.trans_le (show δ ≤ t from min_le_left ..)
  have hns : (n : Surreal.{u}) * s < δ := by
    dsimp only [s]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).mpr
    have hn' : (n : Surreal.{u}) < (↑(n + 2) : Surreal.{u}) := by
      exact_mod_cast (show n < n + 2 by omega)
    simpa only [mul_comm δ] using mul_lt_mul_of_pos_right hn' hδ
  have hsfix : cosetRep A s = s := cosetRep_unitExponentSubgroup_div_natCast_eq C hδfix (by omega)
  refine ⟨s, hs, hrs, hsfix, ?_⟩
  let w := x - cosetRep D[s] x
  have hw : w ∈ U :=
    (U).sub_mem hx (cosetRep_wpow_smul_mem_residueRepresentatives C hs.le x)
  apply roundAt_mul_eq_of_sub_mul_mem C ((U).pow_mem hw n)
  change e * w ^ n ∈ D[t]
  by_cases hw₀ : w = 0
  · rw [hw₀, zero_pow hn.ne', mul_zero]
    exact (D[t]).zero_mem
  have hwLevel : precisionLevel C w < s :=
    (mem_wpow_smul_infinitesimals_iff C hw₀ hsfix).mp (sub_cosetRep_mem _ _)
  apply (mem_wpow_smul_infinitesimals_iff C (mul_ne_zero he₀ (pow_ne_zero _ hw₀))
    htfix).mpr
  rw [precisionLevel_mul C he₀ (pow_ne_zero _ hw₀), precisionLevel_pow C hw₀]
  have hBound := mul_le_mul_of_nonneg_left hwLevel.le (Nat.cast_nonneg (α := Surreal.{u}) n)
  have hδle : δ ≤ t - precisionLevel C e := min_le_right _ _
  linarith only [hBound, hns, hδle]

end Surreal
