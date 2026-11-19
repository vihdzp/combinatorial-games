/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Coset.Basic
public import CombinatorialGames.Surreal.Omnific.Basic
public import Mathlib.Algebra.Ring.Subring.Basic

import CombinatorialGames.Surreal.Omnific.Coset
import Mathlib.Tactic.Ring.RingNF

/-!
# Residues of omnific integers modulo simplest representatives

For a convex subring `C` of the surreal numbers, subtracting the simplest representative
modulo `C` gives a ring retraction from the omnific integers onto their intersection with `C`.
-/

universe u

public noncomputable section

namespace Surreal

variable (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex]

private theorem isOmnific_sub_cosetRep (x : omnific.{u}) :
    IsOmnific ((x : Surreal.{u}) - cosetRep C.toAddSubgroup x) :=
  (mem_omnific_iff.mp x.property).sub
    (isOmnific_of_cosetRep_eq (cosetRep_cosetRep C.toAddSubgroup x))

private theorem sub_cosetRep_mul (x y : omnific.{u}) :
    (x : Surreal.{u}) * y - cosetRep C.toAddSubgroup (x * y) =
      ((x : Surreal.{u}) - cosetRep C.toAddSubgroup x) *
        ((y : Surreal.{u}) - cosetRep C.toAddSubgroup y) := by
  let p := cosetRep C.toAddSubgroup x
  let q := cosetRep C.toAddSubgroup y
  let d := (x : Surreal.{u}) - p
  let e := (y : Surreal.{u}) - q
  have hdiff : (x : Surreal.{u}) * y - (p * y + q * d) = d * e := by
    dsimp [d, e]
    ring
  have hmem : (x : Surreal.{u}) * y - (p * y + q * d) ∈ C.toAddSubgroup := by
    rw [hdiff]
    exact C.mul_mem (sub_cosetRep_mem C.toAddSubgroup x) (sub_cosetRep_mem C.toAddSubgroup y)
  have hfix₁ : cosetRep C.toAddSubgroup (p * y) = p * y :=
    cosetRep_mul_eq_of_isOmnific (cosetRep_cosetRep C.toAddSubgroup x)
      (mem_omnific_iff.mp y.property)
  have hfix₂ : cosetRep C.toAddSubgroup (q * d) = q * d :=
    cosetRep_mul_eq_of_isOmnific (cosetRep_cosetRep C.toAddSubgroup y)
      (isOmnific_sub_cosetRep C x)
  rw [cosetRep_eq_of_sub_mem hmem, cosetRep_add, hfix₁, hfix₂]
  exact hdiff

/-- Subtract the simplest representative modulo `C` from an omnific integer. This defines
a ring retraction onto the omnific integers that belong to `C`. -/
def omnificResidue :
    omnific.{u} →+* (omnific ⊓ C : Subring Surreal.{u}) where
  toFun x := ⟨(x : Surreal.{u}) - cosetRep C.toAddSubgroup x, Subring.mem_inf.mpr
    ⟨mem_omnific_iff.mpr (isOmnific_sub_cosetRep C x),
      sub_cosetRep_mem C.toAddSubgroup x⟩⟩
  map_one' := Subtype.ext (show (1 : Surreal.{u}) - cosetRep C.toAddSubgroup 1 = 1 by
    rw [cosetRep_eq_zero_iff.mpr C.one_mem, sub_zero])
  map_zero' := Subtype.ext (show (0 : Surreal.{u}) - cosetRep C.toAddSubgroup 0 = 0 by simp)
  map_add' x y := Subtype.ext (show
    (x : Surreal.{u}) + y - cosetRep C.toAddSubgroup (x + y) =
      ((x : Surreal.{u}) - cosetRep C.toAddSubgroup x) +
        ((y : Surreal.{u}) - cosetRep C.toAddSubgroup y) by
    rw [cosetRep_add, add_sub_add_comm])
  map_mul' x y := Subtype.ext (sub_cosetRep_mul C x y)

/-- The value of the residue is the difference from the simplest representative. -/
@[simp] theorem coe_omnificResidue (x : omnific.{u}) :
    (omnificResidue C x : Surreal.{u}) = (x : Surreal.{u}) - cosetRep C.toAddSubgroup x :=
  (rfl)

/-- Taking residues fixes the omnific integers in the convex subring. -/
@[simp]
theorem omnificResidue_inclusion (x : (omnific ⊓ C : Subring Surreal.{u})) :
    omnificResidue C (Subring.inclusion inf_le_left x) = x := by
  apply Subtype.ext
  rw [coe_omnificResidue, Subring.coe_inclusion,
    cosetRep_eq_zero_iff.mpr (Subring.mem_inf.mp x.property).2, sub_zero]

/-- An omnific integer has zero residue exactly when it is its own simplest representative. -/
@[simp] theorem omnificResidue_eq_zero_iff (x : omnific.{u}) :
    omnificResidue C x = 0 ↔ cosetRep C.toAddSubgroup (x : Surreal.{u}) = x := by
  rw [← Subtype.coe_inj, coe_omnificResidue, Subring.coe_zero, sub_eq_zero, eq_comm]

end Surreal
