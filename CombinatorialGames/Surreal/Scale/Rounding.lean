/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Scale.Basic

/-!
# Rounding by Conway monomials

Divide a surreal by a Conway monomial, then choose the simplest representative modulo the
infinitesimals of a convex subring.
-/

universe u

open scoped Pointwise

public noncomputable section

namespace Surreal

variable (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex]

/-- The simplest residue representative of a surreal divided by the monomial at precision `t`. -/
def roundAt (t x : Surreal.{u}) : Surreal.{u} :=
  cosetRep (infinitesimals C) (x / ω^ t)

/-- Evaluation of rescaled rounding. -/
theorem roundAt_eq (t x : Surreal.{u}) :
    roundAt C t x = cosetRep (infinitesimals C) (x / ω^ t) := (rfl)

/-- The rescaled rounding belongs to the subring of residue representatives. -/
theorem roundAt_mem_residueRepresentatives (t x : Surreal.{u}) :
    roundAt C t x ∈ residueRepresentatives C :=
  cosetRep_mem_residueRepresentatives C _

/-- The unscaled rounding chooses the simplest representative modulo the infinitesimals. -/
@[simp] theorem roundAt_zero_precision (x : Surreal.{u}) :
    roundAt C 0 x = cosetRep (infinitesimals C) x := by
  rw [roundAt_eq, wpow_zero, div_one]

/-- Rescaled rounding is additive. -/
@[simp] theorem roundAt_add (t x y : Surreal.{u}) :
    roundAt C t (x + y) = roundAt C t x + roundAt C t y := by
  simp only [roundAt_eq, add_div, cosetRep_add]

/-- Rescaled rounding commutes with subtraction. -/
@[simp] theorem roundAt_sub (t x y : Surreal.{u}) :
    roundAt C t (x - y) = roundAt C t x - roundAt C t y := by
  simp only [roundAt_eq, sub_div, cosetRep_sub]

/-- The simplest representative modulo the scaled infinitesimals belongs to the subring of
residue representatives when the precision is nonnegative. -/
theorem cosetRep_wpow_smul_mem_residueRepresentatives {t : Surreal.{u}} (ht : 0 ≤ t)
    (x : Surreal.{u}) :
    cosetRep (ω^ t • infinitesimals C) x ∈ residueRepresentatives C := by
  have hle := smul_addSubgroup_mono (infinitesimals C) (wpow_pos 0) (wpow_le_wpow.mpr ht)
  rw [wpow_zero, one_smul] at hle
  exact (mem_residueRepresentatives_iff C).mpr (cosetRep_cosetRep_of_ge hle x)

/-- Rounding at a greater precision depends only on the simplest representative at the
smaller precision. -/
theorem roundAt_scaleCosetRep_of_le {s r : Surreal.{u}} (hsr : s ≤ r) (x : Surreal.{u}) :
    roundAt C r (cosetRep (ω^ s • infinitesimals C) x) =
      roundAt C r x := by
  simp only [roundAt_eq]
  symm
  apply cosetRep_eq_of_sub_mem
  rw [← sub_div]
  apply (mem_smul_addSubgroup_iff_div_mem (wpow_ne_zero r)).mp
  exact smul_addSubgroup_mono (infinitesimals C) (wpow_pos s) (wpow_le_wpow.mpr hsr)
    (sub_cosetRep_mem _ _)

/-- Reading a simplest representative at a smaller precision multiplies its original
rescaled reading by the monomial of the difference of precisions. -/
theorem roundAt_scaleCosetRep_of_ge {s r : Surreal.{u}} (hrs : r ≤ s) (x : Surreal.{u}) :
    roundAt C r (cosetRep (ω^ s • infinitesimals C) x) =
      ω^ (s - r) * roundAt C s x := by
  have hfix := (mem_residueRepresentatives_iff C).mp
    (wpow_mul_mem_residueRepresentatives C (sub_nonneg.mpr hrs)
      (roundAt_mem_residueRepresentatives C s x))
  have heq : cosetRep (ω^ s • infinitesimals C) x / ω^ r =
      ω^ (s - r) * roundAt C s x := by
    rw [cosetRep_wpow_smul, roundAt_eq, mul_comm (ω^ s), mul_div_assoc,
      mul_comm _ (ω^ s / ω^ r), ← wpow_sub]
  rw [roundAt_eq, heq, hfix]

/-- A second rounding at a nonnegative precision adds that precision to the first. -/
theorem roundAt_roundAt (s : Surreal.{u}) {t : Surreal.{u}} (ht : 0 ≤ t) (x : Surreal.{u}) :
    roundAt C t (roundAt C s x) = roundAt C (s + t) x := by
  have htinv : (ω^ t)⁻¹ ∈ C := by
    rw [← wpow_neg]
    exact C.toAddSubgroup.mem_of_nonneg_of_le (wpow_nonneg _)
      (by simpa only [wpow_zero] using wpow_le_wpow.mpr (neg_nonpos.mpr ht)) C.one_mem
  rw [roundAt_eq C t, roundAt_eq C (s + t), roundAt_eq C s, wpow_add, ← div_div]
  symm
  apply cosetRep_eq_of_sub_mem
  rw [← sub_div, div_eq_mul_inv, mul_comm]
  exact mul_mem_infinitesimals_of_mem C htinv (sub_cosetRep_mem _ _)

/-- The leading reading of a nonzero representative is a nonzero residue scalar. -/
theorem roundAt_precisionLevel_mem_residueSubfield_and_ne_zero (x : residueRepresentatives C)
    (hx : (x : Surreal) ≠ 0) :
    roundAt C (precisionLevel C (x : Surreal)) x ∈ residueSubfield C ∧
      roundAt C (precisionLevel C (x : Surreal)) x ≠ 0 := by
  let t := precisionLevel C (x : Surreal)
  have ht := cosetRep_precisionLevel C (x : Surreal)
  have hunit := (div_wpow_mem_subring_and_inv_iff C hx ht).mpr rfl
  have hsub := infinitesimals_le C (sub_cosetRep_mem (infinitesimals C) ((x : Surreal) / ω^ t))
  have hxC : (x : Surreal) / ω^ t ∈ C := hunit.1
  have hmem : cosetRep (infinitesimals C) ((x : Surreal) / ω^ t) ∈ C := by
    simpa only [sub_sub_cancel] using C.sub_mem hxC hsub
  have hnot := (notMem_infinitesimals_iff C).mpr ⟨div_ne_zero hx (wpow_ne_zero t), hunit.2⟩
  exact ⟨(mem_residueSubfield_iff C).mpr
      ⟨roundAt_mem_residueRepresentatives C t x, (roundAt_eq C t x).symm ▸ hmem⟩,
    fun h ↦ hnot (cosetRep_eq_zero_iff.mp ((roundAt_eq C t x).symm.trans h))⟩

end Surreal
