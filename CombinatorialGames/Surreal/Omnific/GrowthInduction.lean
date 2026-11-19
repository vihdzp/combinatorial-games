/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Omnific.Residue
public import CombinatorialGames.Surreal.Scale.Growth

import CombinatorialGames.Surreal.Omnific.Coset

/-!
# Induction on the growth classes of an omnific integer

Division by a nonzero residue at an occurring class keeps exactly the strictly larger classes.
Their reverse order has smaller ordinal type. The quotient has residue one at every lower scale.
-/

universe u

public noncomputable section

namespace Surreal

/-- At each occurring growth class the upper residue is a nonzero factor. Its complementary
omnific factor has residue one at every lower scale and keeps exactly the larger occurrences. -/
theorem exists_normalizedFactor_of_growthOccurs (x : omnific.{u}) {i : Surreal.{u}}
    (hi : GrowthOccurs i x) :
    let D := upperGrowthSubring i
    let w := omnificResidue D x
    w ≠ 0 ∧ ∃ v : omnific.{u}, x = Subring.inclusion inf_le_left w * v ∧
      (∀ j, GrowthOccurs j v ↔ i < j ∧ GrowthOccurs j x) ∧
      ∀ (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex], C ≤ D → omnificResidue C v = 1 := by
  let D := upperGrowthSubring i
  let w := omnificResidue D x
  let p := cosetRep D.toAddSubgroup (x : Surreal)
  have hwp : (x : Surreal) - w = p := by rw [coe_omnificResidue]; exact sub_sub_cancel ..
  have hw : w ≠ 0 := by
    intro h
    have he := (omnificResidue_eq_zero_iff D x).mp h
    have hproj := cosetRep_cosetRep_of_ge
      (show (lowerGrowthSubring i).toAddSubgroup ≤ D.toAddSubgroup from
        lowerGrowthSubring_le_upperGrowthSubring i) (x : Surreal)
    rw [he] at hproj
    exact (growthOccurs_iff i x).mp hi (hproj.trans he.symm)
  have hw₀ : (w : Surreal) ≠ 0 := fun he ↦ hw (Subtype.ext he)
  have hwW := mem_omnific_iff.mp (Subring.mem_inf.mp w.property).1
  have hwD := (Subring.mem_inf.mp w.property).2
  have hfix := cosetRep_div_eq_of_isOmnific (cosetRep_cosetRep D.toAddSubgroup
    (x : Surreal)) hwW hwD hw₀
  let v : omnific.{u} := ⟨p / w + 1,
    mem_omnific_iff.mpr ((isOmnific_of_cosetRep_eq hfix).add IsOmnific.one)⟩
  have hv : (v : Surreal) = (x : Surreal) / w := by
    change p / w + 1 = _
    rw [← hwp, sub_div, div_self hw₀, sub_add_cancel]
  refine ⟨hw, v, Subtype.ext ?_, ?_, ?_⟩
  · change (x : Surreal) = w * (v : Surreal)
    rw [hv, mul_comm, div_mul_cancel₀ _ hw₀]
  · intro j
    rw [hv]
    exact growthOccurs_div_iff hwW hw₀ hwD hwp j
  · intro C _ hCD
    apply Subtype.ext
    rw [coe_omnificResidue]
    have h := cosetRep_cosetRep_of_ge (show C.toAddSubgroup ≤ D.toAddSubgroup from hCD) (p / w)
    rw [show cosetRep D.toAddSubgroup (p / w) = p / w from hfix] at h
    change p / w + 1 - cosetRep C.toAddSubgroup (p / w + 1) = 1
    rw [cosetRep_add, h, cosetRep_eq_zero_iff.mpr C.one_mem, add_zero, add_sub_cancel_left]

private abbrev Occurrences (x : Surreal.{u}) :=
  {i : Surreal.{u}ᵒᵈ // GrowthOccurs (OrderDual.ofDual i) x}

private instance (x : Surreal.{u}) : WellFoundedLT (Occurrences x) :=
  growthOccurs_wellFounded x

private def occurrenceLength (x : Surreal.{u}) : Ordinal.{u+1} :=
  Ordinal.type (α := Occurrences x) (· < ·)

private theorem occurrenceLength_lt_of_prefix {x v i : Surreal.{u}} (hi : GrowthOccurs i x)
    (hv : ∀ j, GrowthOccurs j v ↔ i < j ∧ GrowthOccurs j x) :
    occurrenceLength v < occurrenceLength x := by
  let j : Occurrences x := ⟨OrderDual.toDual i, hi⟩
  let e : Occurrences v ≃o Set.Iio j :=
    { toFun k := ⟨⟨k.1, ((hv _).mp k.2).2⟩, ((hv _).mp k.2).1⟩
      invFun k := ⟨k.1.1, (hv _).mpr ⟨k.2, k.1.2⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_rel_iff' := Iff.rfl }
  exact e.ordinalType_congr.trans_lt (Ordinal.typein_lt_type (· < ·) j)

/-- Induction on omnific integers by retaining the growth classes strictly above a chosen
occurring class. -/
theorem omnific_growthInduction (P : omnific.{u} → Prop)
    (step : ∀ x : omnific.{u}, (∀ i, GrowthOccurs i x → ∀ v : omnific.{u},
      (∀ j, GrowthOccurs j v ↔ i < j ∧ GrowthOccurs j x) → P v) → P x)
    (x : omnific.{u}) : P x := by
  apply step
  intro i hi v hv
  exact omnific_growthInduction P step v
termination_by occurrenceLength (x : Surreal)
decreasing_by exact occurrenceLength_lt_of_prefix hi hv

end Surreal
