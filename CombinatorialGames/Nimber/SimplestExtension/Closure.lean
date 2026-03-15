/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/
module

public import CombinatorialGames.Nimber.SimplestExtension.Basic

import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.SetTheory.Cardinal.Subfield
import Mathlib.Algebra.CharP.Algebra

/-!
# Closures

We define `groupClosure`, `ringClosure`, and `fieldClosure`, which represent the smallest nimber
equal or greater to another, which satisfies `IsGroup`, `IsRing`, or `IsField`.
-/

universe u

public section

/-! ### For Mathlib -/

section
variable {R : Type*}

@[simp]
theorem Subring.coe_eq_univ [Ring R] {H : Subring R} : (H : Set R) = .univ ↔ H = ⊤ :=
  (SetLike.ext'_iff.trans (by rfl)).symm

@[simp]
theorem Subfield.coe_eq_univ [Field R] {H : Subfield R} : (H : Set R) = .univ ↔ H = ⊤ :=
  (SetLike.ext'_iff.trans (by rfl)).symm

@[simp]
theorem Subfield.toSubring_eq_top [Field R] {H : Subfield R} : H.toSubring = ⊤ ↔ H = ⊤ := by
  rw [← SetLike.coe_set_eq, Subfield.coe_toSubring]; simp

@[simp]
theorem Subfield.coe_bot [DivisionRing R] :
    (⊥ : Subfield R) = Set.range ((↑) : ℚ → R) := by
  obtain _ | ⟨p, _, _⟩ := CharP.exists' R
  · change _ = (RingHom.fieldRange (Rat.castHom R) : Set R)
    refine congrArg SetLike.coe (le_antisymm bot_le ?_)
    rw [← Subfield.fieldRange_subtype (⊥ : Subfield R),
      Subsingleton.elim (Rat.castHom R) ((⊥ : Subfield R).subtype.comp
      (Rat.castHom (⊥ : Subfield R))),
      RingHom.fieldRange_eq_map, RingHom.fieldRange_eq_map, ← Subfield.map_map]
    exact (Subfield.gc_map_comap _).monotone_l le_top
  · trans (RingHom.fieldRange (ZMod.castHom (dvd_refl p) R) : Set R)
    · have := Subfield.charP (⊥ : Subfield R) p
      refine congrArg SetLike.coe (le_antisymm bot_le ?_)
      rw [← Subfield.fieldRange_subtype (⊥ : Subfield R),
        Subsingleton.elim (ZMod.castHom (dvd_refl p) R)
          ((⊥ : Subfield R).subtype.comp (ZMod.castHom (dvd_refl p) (⊥ : Subfield R))),
        RingHom.fieldRange_eq_map, RingHom.fieldRange_eq_map, ← Subfield.map_map]
      exact (Subfield.gc_map_comap _).monotone_l le_top
    · apply subset_antisymm
      · rw [RingHom.coe_fieldRange, Set.range_subset_iff]
        intro x
        refine ⟨x.val, ?_⟩
        trans Int.cast (ZMod.cast x)
        · rw [← Rat.cast_intCast]
          exact congrArg Rat.cast (by simp)
        · simp
      · rw [Set.range_subset_iff]
        intro x
        rw [Rat.cast_def, SetLike.mem_coe]
        apply div_mem
        · apply intCast_mem
        · apply natCast_mem

attribute [simp] Cardinal.aleph0_lt_univ

instance Subfield.small_closure (s : Set R) [DivisionRing R] [Small.{u} s] :
    Small.{u} (Subfield.closure s) := by
  rw [Cardinal.small_iff_lift_mk_lt_univ] at *
  apply (Cardinal.lift_le.2 (Subfield.cardinalMk_closure_le_max s)).trans_lt
  simpa

instance Subfield.small_closure' (s : Set R) [DivisionRing R] [Small.{u} s] :
    Small.{u} (Subfield.closure s : Set R) :=
  Subfield.small_closure s

theorem Order.IsNormal.exists_btwn {α : Type*} {f : α → α} {x : α}
    [LinearOrder α] [WellFoundedLT α] [SuccOrder α] [NoMaxOrder α] [OrderBot α]
    (hf : Order.IsNormal f) (hx : f ⊥ ≤ x) : ∃ a, f a ≤ x ∧ x < f (Order.succ a) := by
  let := WellFoundedLT.conditionallyCompleteLinearOrderBot α
  refine ⟨sSup (f ⁻¹' Set.Iic x), ?_, ?_⟩
  · rw [hf.le_iff_le_sSup' ⟨⊥, hx⟩]
  · rw [← not_le, hf.le_iff_le_sSup' ⟨⊥, hx⟩, not_le, Order.lt_succ_iff]

-- A version of `IsNormal.exists_btwn` which hides some def-eq abuse.
private theorem Order.IsNormal.exists_btwn' {f : Ordinal.{u} → Nimber.{u}} {x : Nimber}
    (hf : Order.IsNormal f) (hx : f 0 ≤ x) : ∃ a, f a ≤ x ∧ x < f (Order.succ a) :=
  hf.exists_btwn hx

end

noncomputable section

namespace Nimber
open Set

/-! ### Groups -/

section AddSubgroup
open AddSubgroup

theorem isGroup_sInf_compl (s : AddSubgroup Nimber) (hs : s ≠ ⊤) : IsGroup (sInf sᶜ) := by
  obtain rfl | hsb := eq_or_ne s ⊥
  · simp [← Iio_one]
  · have hsn : (s : Set Nimber)ᶜ.Nonempty := by contrapose! hs; simpa using hs
    have hI := csInf_mem hsn
    by_contra hs
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_add_of_not_isGroup hs fun _ ↦ by simp_all
    apply (hyz ▸ hI) (add_mem ..)
    · simpa using notMem_of_lt_csInf' hy
    · simpa using notMem_of_lt_csInf' hz

theorem isLowerSet_addSubgroupClosure {s : Set Nimber} (hs : IsLowerSet s) :
    IsLowerSet (closure s : Set Nimber) := by
  intro a b h ha
  by_contra hb
  have hx := isGroup_sInf_compl (closure s) (by contrapose hb; simp [hb])
  apply notMem_of_lt_csInf' (h.trans_lt (hx.toAddSubgroup.closure_le.2 _ ha)) hb
  intro y hy
  rw [SetLike.mem_coe, mem_toAddSubgroup_iff]
  by_contra! hy'
  exact csInf_mem (s := _ᶜ) ⟨b, hb⟩ (mem_closure_of_mem (hs hy' hy))

instance small_addSubgroupClosure (s : Set Nimber) [Small.{u} s] : Small.{u} (closure s) := by
  apply small_subset (s := (Subfield.closure s : Set Nimber))
  change closure s ≤ (Subfield.closure s).toAddSubgroup
  simp

theorem addSubgroupClosure_Iio_eq_Iio (x : Nimber) :
    ∃ y, (closure (Iio x) : Set Nimber) = Iio y := by
  refine (isLowerSet_addSubgroupClosure (isLowerSet_Iio x)).eq_univ_or_Iio.resolve_left fun hx ↦ ?_
  have H : Small (_ : Set _) := small_addSubgroupClosure (Iio x)
  rw [hx, small_univ_iff] at H
  cases not_small_nimber H

/-- Returns the smallest `IsGroup` that's at least `x`. -/
def groupClosure (x : Nimber) : Nimber := Classical.choose (addSubgroupClosure_Iio_eq_Iio x)

@[simp]
theorem coe_addSubgroupClosure_Iio (x : Nimber) :
    (closure (Iio x) : Set Nimber) = Iio (groupClosure x) :=
  Classical.choose_spec (addSubgroupClosure_Iio_eq_Iio x)

@[simp]
theorem mem_addSubgroupClosure_Iio {x y : Nimber} : y ∈ closure (Iio x) ↔ y < groupClosure x := by
  rw [← SetLike.mem_coe, coe_addSubgroupClosure_Iio, mem_Iio]

@[simp]
theorem le_groupClosure (x : Nimber) : x ≤ groupClosure x := by
  by_contra! hx
  exact (mem_addSubgroupClosure_Iio.1 (mem_closure_of_mem hx)).false

@[simp]
protected theorem IsGroup.groupClosure (x : Nimber) : IsGroup (groupClosure x) where
  ne_zero := (mem_addSubgroupClosure_Iio.1 (AddSubgroup.zero_mem _)).ne'
  add_lt y z := by
    simp_rw [← mem_addSubgroupClosure_Iio]
    exact AddSubgroup.add_mem _

theorem IsGroup.groupClosure_le_iff {x y : Nimber} (h : IsGroup x) :
    y.groupClosure ≤ x ↔ y ≤ x where
  mp := le_trans (le_groupClosure y)
  mpr hyx := by
    rw [← not_lt, ← mem_addSubgroupClosure_Iio]
    intro hx
    have := h.closure_Iio ▸ closure_mono (Iio_subset_Iio hyx) hx
    simpa

theorem IsGroup.lt_groupClosure_iff {x y : Nimber} (h : IsGroup x) :
    x < y.groupClosure ↔ x < y :=
  le_iff_le_iff_lt_iff_lt.1 h.groupClosure_le_iff

theorem IsGroup.groupClosure_eq {x : Nimber} (h : IsGroup x) : groupClosure x = x := by
  apply (le_groupClosure x).antisymm'
  rw [h.groupClosure_le_iff]

theorem groupClosure_mono : Monotone groupClosure := by
  intro x y
  rw [(IsGroup.groupClosure y).groupClosure_le_iff]
  exact (le_groupClosure y).trans'

@[simp]
theorem groupClosure_zero : groupClosure 0 = 1 := by
  rw [← Iio_inj, ← coe_addSubgroupClosure_Iio]
  simp

@[simp]
theorem groupClosure_one : groupClosure 1 = 1 :=
  IsGroup.one.groupClosure_eq

@[simp]
theorem groupClosure_two : groupClosure (∗2) = ∗2 :=
  IsGroup.two.groupClosure_eq

theorem IsGroup.one_le {x : Nimber} (h : IsGroup x) : 1 ≤ x := by
  rw [← groupClosure_zero, h.groupClosure_le_iff]
  exact zero_le _

@[simp]
theorem groupClosure.two_opow (x : Ordinal) : groupClosure (∗(2 ^ x)) = ∗(2 ^ x) :=
  (IsGroup.two_opow x).groupClosure_eq

theorem groupClosure_of_not_isGroup {x : Nimber} (h : ¬ IsGroup x) (hx₀ : x ≠ 0) :
    groupClosure x = ∗(2 ^ (Ordinal.log 2 x.val + 1)) := by
  rw [← val_ne_zero] at hx₀
  apply le_antisymm
  · rw [(IsGroup.two_opow _).groupClosure_le_iff, ← val_le_iff]
    simpa using (Ordinal.lt_opow_succ_log_self one_lt_two x.val).le
  · obtain ⟨y, hy⟩ := isGroup_iff_mem_range_two_opow.1 <| IsGroup.groupClosure x
    rw [← hy]
    apply Ordinal.opow_le_opow_right two_pos
    rw [Order.add_one_le_iff, ← Ordinal.lt_opow_iff_log_lt one_lt_two hx₀]
    rw [of_eq_iff] at hy
    rw [hy, val.lt_iff_lt]
    apply (le_groupClosure x).lt_of_ne
    contrapose! h
    exact h ▸ IsGroup.groupClosure x

theorem not_bddAbove_setOf_isGroup : ¬ BddAbove (setOf IsGroup) :=
  fun ⟨a, ha⟩ ↦ (ha (.groupClosure _)).not_gt <| (Order.lt_succ a).trans_le (le_groupClosure _)

/-- The normal enumerator function for groups. (This is equal to `∗(2 ^ x)`.) -/
def enumGroup (x : Ordinal) : Nimber :=
  ∗(Ordinal.enumOrd {y | IsGroup (∗y)} x)

@[simp]
theorem range_enumGroup : Set.range enumGroup = setOf IsGroup :=
  Ordinal.range_enumOrd not_bddAbove_setOf_isGroup

theorem mem_range_enumGroup_iff {x : Nimber} : x ∈ Set.range enumGroup ↔ IsGroup x :=
  Set.ext_iff.1 range_enumGroup _

theorem IsGroup.enumGroup (x : Ordinal) : IsGroup (enumGroup x) :=
  mem_range_enumGroup_iff.1 ⟨x, rfl⟩

theorem isNormal_enumGroup : Order.IsNormal enumGroup :=
  Ordinal.isNormal_enumOrd (fun _ ↦ IsGroup.sSup) not_bddAbove_setOf_isGroup

@[simp]
theorem enumGroup_le_enumGroup_iff {x y} : enumGroup x ≤ enumGroup y ↔ x ≤ y :=
  isNormal_enumGroup.strictMono.le_iff_le

@[simp]
theorem enumGroup_lt_enumGroup_iff {x y} : enumGroup x < enumGroup y ↔ x < y :=
  isNormal_enumGroup.strictMono.lt_iff_lt

@[simp]
theorem enumGroup_inj {x y} : enumGroup x = enumGroup y ↔ x = y :=
  isNormal_enumGroup.strictMono.injective.eq_iff

theorem enumGroup_eq_two_opow (x : Ordinal) : enumGroup x = ∗(2 ^ x) := by
  simp_rw [enumGroup, of.eq_iff_eq, isGroup_iff_mem_range_two_opow]
  apply congrFun (Ordinal.enumOrd_range (f := fun y ↦ 2 ^ y) fun a b h ↦ ?_)
  rwa [Ordinal.opow_lt_opow_iff_right one_lt_two]

@[simp]
theorem enumGroup_zero : enumGroup 0 = 1 := by
  simp [enumGroup_eq_two_opow]

theorem exists_isGroup_btwn {x : Nimber} (ne : x ≠ 0) : ∃ l u,
    IsGroup l ∧ IsGroup u ∧ l ≤ x ∧ x < u ∧ ∀ z, IsGroup z → l < z → u ≤ z := by
  have ⟨a, hl, hu⟩ := isNormal_enumGroup.exists_btwn' (x := x) (by simpa)
  refine ⟨_, _, .enumGroup _, .enumGroup _, hl, hu, fun b hb hab ↦ ?_⟩
  obtain ⟨b, rfl⟩ := mem_range_enumGroup_iff.2 hb
  simpa using hab

end AddSubgroup

/-! ### Rings -/

section Subring
open Subring

theorem isRing_sInf_compl (s : Subring Nimber) (hs : s ≠ ⊤) : IsRing (sInf sᶜ) := by
  obtain rfl | hsb := eq_or_ne s ⊥
  · simp [coe_bot, ← Iio_two]
  · have hsn : (s : Set Nimber)ᶜ.Nonempty := by contrapose! hs; simpa using hs
    have hI := csInf_mem hsn
    by_contra hs'
    have ⟨y, hy, z, hz, hyz⟩ :=
      (isGroup_sInf_compl s.toAddSubgroup (by simpa)).exists_mul_of_not_isRing hs'
      fun _ ↦ by simp_all
    apply (hyz ▸ hI) (mul_mem ..)
    · simpa using notMem_of_lt_csInf' hy
    · simpa using notMem_of_lt_csInf' hz

theorem isLowerSet_subringClosure {s : Set Nimber} (hs : IsLowerSet s) :
    IsLowerSet (closure s : Set Nimber) := by
  intro a b h ha
  by_contra hb
  have hx := isRing_sInf_compl (closure s) (by contrapose hb; simp [hb])
  apply notMem_of_lt_csInf' (h.trans_lt (hx.toSubring.closure_le.2 _ ha)) hb
  intro y hy
  rw [SetLike.mem_coe, mem_toSubring_iff]
  by_contra! hy'
  exact csInf_mem (s := _ᶜ) ⟨b, hb⟩ (mem_closure_of_mem (hs hy' hy))

instance small_subringClosure (s : Set Nimber) [Small.{u} s] : Small.{u} (closure s) := by
  apply small_subset (s := (Subfield.closure s : Set Nimber))
  change closure s ≤ (Subfield.closure s).toSubring
  simp

theorem subringClosure_Iio_eq_Iio (x : Nimber) : ∃ y, (closure (Iio x) : Set Nimber) = Iio y := by
  refine (isLowerSet_subringClosure (isLowerSet_Iio x)).eq_univ_or_Iio.resolve_left fun hx ↦ ?_
  have H : Small (_ : Set _) := small_subringClosure (Iio x)
  rw [hx, small_univ_iff] at H
  cases not_small_nimber H

/-- Returns the smallest `IsRing` that's at least `x`. -/
def ringClosure (x : Nimber) : Nimber := Classical.choose (subringClosure_Iio_eq_Iio x)

@[simp]
theorem coe_subringClosure_Iio (x : Nimber) :
    (closure (Iio x) : Set Nimber) = Iio (ringClosure x) :=
  Classical.choose_spec (subringClosure_Iio_eq_Iio x)

@[simp]
theorem mem_subringClosure_Iio {x y : Nimber} : y ∈ closure (Iio x) ↔ y < ringClosure x := by
  rw [← SetLike.mem_coe, coe_subringClosure_Iio, mem_Iio]

@[simp]
theorem le_ringClosure (x : Nimber) : x ≤ ringClosure x := by
  by_contra! hx
  exact (mem_subringClosure_Iio.1 (mem_closure_of_mem hx)).false

@[simp]
protected theorem IsRing.ringClosure (x : Nimber) : IsRing (ringClosure x) where
  ne_zero := (mem_subringClosure_Iio.1 (Subring.zero_mem _)).ne'
  ne_one := (mem_subringClosure_Iio.1 (Subring.one_mem _)).ne'
  add_lt y z := by
    simp_rw [← mem_subringClosure_Iio]
    exact Subring.add_mem _
  mul_lt y z := by
    simp_rw [← mem_subringClosure_Iio]
    exact Subring.mul_mem _

theorem IsRing.ringClosure_le_iff {x y : Nimber} (h : IsRing x) :
    y.ringClosure ≤ x ↔ y ≤ x where
  mp := le_trans (le_ringClosure y)
  mpr hyx := by
    rw [← not_lt, ← mem_subringClosure_Iio]
    intro hx
    have := h.closure_Iio ▸ closure_mono (Iio_subset_Iio hyx) hx
    simpa

theorem IsRing.lt_ringClosure_iff {x y : Nimber} (h : IsRing x) :
    x < y.ringClosure ↔ x < y :=
  le_iff_le_iff_lt_iff_lt.1 h.ringClosure_le_iff

theorem IsRing.ringClosure_eq {x : Nimber} (h : IsRing x) : ringClosure x = x := by
  apply (le_ringClosure x).antisymm'
  rw [h.ringClosure_le_iff]

theorem ringClosure_mono : Monotone ringClosure := by
  intro x y
  rw [(IsRing.ringClosure y).ringClosure_le_iff]
  exact (le_ringClosure y).trans'

@[simp]
theorem ringClosure_zero : ringClosure 0 = ∗2 := by
  rw [← Iio_inj, ← coe_subringClosure_Iio]
  simp [Subring.coe_bot]

@[simp]
theorem ringClosure_one : ringClosure 1 = ∗2 := by
  apply le_antisymm
  · rw [IsRing.two.ringClosure_le_iff]
    simp
  · rw [← ringClosure_zero]
    exact ringClosure_mono zero_le_one

@[simp]
theorem ringClosure_two : ringClosure (∗2) = ∗2 :=
  IsRing.two.ringClosure_eq

theorem IsRing.two_le {x : Nimber} (h : IsRing x) : ∗2 ≤ x := by
  rw [← ringClosure_zero, h.ringClosure_le_iff]
  exact zero_le _

theorem groupClosure_le_ringClosure (x : Nimber) : groupClosure x ≤ ringClosure x := by
  rw [(IsRing.ringClosure x).groupClosure_le_iff]
  exact le_ringClosure x

theorem not_bddAbove_setOf_isRing : ¬ BddAbove (setOf IsRing) :=
  fun ⟨a, ha⟩ ↦ (ha (.ringClosure _)).not_gt <| (Order.lt_succ a).trans_le (le_ringClosure _)

/-- The normal enumerator function for rings. -/
def enumRing (x : Ordinal) : Nimber :=
  ∗(Ordinal.enumOrd {y | IsRing (∗y)} x)

@[simp]
theorem range_enumRing : Set.range enumRing = setOf IsRing :=
  Ordinal.range_enumOrd not_bddAbove_setOf_isRing

theorem mem_range_enumRing_iff {x : Nimber} : x ∈ Set.range enumRing ↔ IsRing x :=
  Set.ext_iff.1 range_enumRing _

theorem IsRing.enumRing (x : Ordinal) : IsRing (enumRing x) :=
  mem_range_enumRing_iff.1 ⟨x, rfl⟩

theorem isNormal_enumRing : Order.IsNormal enumRing :=
  Ordinal.isNormal_enumOrd (fun _ ↦ IsRing.sSup) not_bddAbove_setOf_isRing

@[simp]
theorem enumRing_le_enumRing_iff {x y} : enumRing x ≤ enumRing y ↔ x ≤ y :=
  isNormal_enumRing.strictMono.le_iff_le

@[simp]
theorem enumRing_lt_enumRing_iff {x y} : enumRing x < enumRing y ↔ x < y :=
  isNormal_enumRing.strictMono.lt_iff_lt

@[simp]
theorem enumRing_inj {x y} : enumRing x = enumRing y ↔ x = y :=
  isNormal_enumRing.strictMono.injective.eq_iff

@[simp]
theorem enumRing_zero : enumRing 0 = ∗2 := by
  rw [enumRing, of.eq_iff_eq, Ordinal.enumOrd_zero]
  apply le_antisymm
  · exact csInf_le' IsRing.two
  · rw [le_csInf_iff'']
    · exact fun _ ↦ IsRing.two_le
    · exact ⟨_, IsRing.two⟩

theorem exists_isRing_btwn {x : Nimber} (ne : 1 < x) : ∃ l u,
    IsRing l ∧ IsRing u ∧ l ≤ x ∧ x < u ∧ ∀ z, IsRing z → l < z → u ≤ z := by
  have ⟨a, hl, hu⟩ := isNormal_enumRing.exists_btwn' (x := x) (by simpa [← succ_one])
  refine ⟨_, _, .enumRing _, .enumRing _, hl, hu, fun b hb hab ↦ ?_⟩
  obtain ⟨b, rfl⟩ := mem_range_enumRing_iff.2 hb
  simpa using hab

end Subring

/-! ### Fields -/

section Subfield
open Subfield

theorem isField_sInf_compl (s : Subfield Nimber) (hs : s ≠ ⊤) : IsField (sInf sᶜ) := by
  obtain rfl | hsb := eq_or_ne s ⊥
  · simp [coe_bot, ← Iio_two]
  · have hsn : (s : Set Nimber)ᶜ.Nonempty := by contrapose! hs; simpa using hs
    have hI := csInf_mem hsn
    contrapose hI
    have := notMem_of_lt_csInf' <|
      (isRing_sInf_compl s.toSubring (by simpa)).inv_lt_self_of_not_isField hI
    simpa

theorem isLowerSet_subfieldClosure {s : Set Nimber} (hs : IsLowerSet s) :
    IsLowerSet (closure s : Set Nimber) := by
  intro a b h ha
  by_contra hb
  have hx := isField_sInf_compl (closure s) (by contrapose hb; simp [hb])
  apply notMem_of_lt_csInf' (h.trans_lt (hx.toSubfield.closure_le.2 _ ha)) hb
  intro y hy
  rw [SetLike.mem_coe, mem_toSubfield_iff]
  by_contra! hy'
  exact csInf_mem (s := _ᶜ) ⟨b, hb⟩ (mem_closure_of_mem (hs hy' hy))

instance small_subfieldClosure (s : Set Nimber) [Small.{u} s] : Small.{u} (closure s) :=
  inferInstance

theorem subfieldClosure_Iio_eq_Iio (x : Nimber) : ∃ y, (closure (Iio x) : Set Nimber) = Iio y := by
  refine (isLowerSet_subfieldClosure (isLowerSet_Iio x)).eq_univ_or_Iio.resolve_left fun hx ↦ ?_
  have H : Small (_ : Set _) := small_subfieldClosure (Iio x)
  rw [hx, small_univ_iff] at H
  cases not_small_nimber H

/-- Returns the smallest `IsField` that's at least `x`. -/
def fieldClosure (x : Nimber) : Nimber := Classical.choose (subfieldClosure_Iio_eq_Iio x)

@[simp]
theorem coe_subfieldClosure_Iio (x : Nimber) :
    (closure (Iio x) : Set Nimber) = Iio (fieldClosure x) :=
  Classical.choose_spec (subfieldClosure_Iio_eq_Iio x)

@[simp]
theorem mem_subfieldClosure_Iio {x y : Nimber} : y ∈ closure (Iio x) ↔ y < fieldClosure x := by
  rw [← SetLike.mem_coe, coe_subfieldClosure_Iio, mem_Iio]

@[simp]
theorem le_fieldClosure (x : Nimber) : x ≤ fieldClosure x := by
  by_contra! hx
  exact (mem_subfieldClosure_Iio.1 (mem_closure_of_mem hx)).false

@[simp]
protected theorem IsField.fieldClosure (x : Nimber) : IsField (fieldClosure x) where
  ne_zero := (mem_subfieldClosure_Iio.1 (Subfield.zero_mem _)).ne'
  ne_one := (mem_subfieldClosure_Iio.1 (Subfield.one_mem _)).ne'
  add_lt y z := by
    simp_rw [← mem_subfieldClosure_Iio]
    exact Subfield.add_mem _
  mul_lt y z := by
    simp_rw [← mem_subfieldClosure_Iio]
    exact Subfield.mul_mem _
  inv_lt' y _ := by
    simp_rw [← mem_subfieldClosure_Iio]
    exact Subfield.inv_mem _

theorem IsField.fieldClosure_le_iff {x y : Nimber} (h : IsField x) :
    y.fieldClosure ≤ x ↔ y ≤ x where
  mp := le_trans (le_fieldClosure y)
  mpr hyx := by
    rw [← not_lt, ← mem_subfieldClosure_Iio]
    intro hx
    have := h.closure_Iio ▸ closure_mono (Iio_subset_Iio hyx) hx
    simpa

theorem IsField.lt_fieldClosure_iff {x y : Nimber} (h : IsField x) :
    x < y.fieldClosure ↔ x < y :=
  le_iff_le_iff_lt_iff_lt.1 h.fieldClosure_le_iff

theorem IsField.fieldClosure_eq {x : Nimber} (h : IsField x) : fieldClosure x = x := by
  apply (le_fieldClosure x).antisymm'
  rw [h.fieldClosure_le_iff]

theorem fieldClosure_mono : Monotone fieldClosure := by
  intro x y
  rw [(IsField.fieldClosure y).fieldClosure_le_iff]
  exact (le_fieldClosure y).trans'

@[simp]
theorem fieldClosure_zero : fieldClosure 0 = ∗2 := by
  rw [← Iio_inj, ← coe_subfieldClosure_Iio]
  simp

@[simp]
theorem fieldClosure_one : fieldClosure 1 = ∗2 := by
  apply le_antisymm
  · rw [IsField.two.fieldClosure_le_iff]
    simp
  · rw [← fieldClosure_zero]
    exact fieldClosure_mono zero_le_one

@[simp]
theorem fieldClosure_two : fieldClosure (∗2) = ∗2 :=
  IsField.two.fieldClosure_eq

theorem IsField.two_le {x : Nimber} (h : IsField x) : ∗2 ≤ x := by
  rw [← fieldClosure_zero, h.fieldClosure_le_iff]
  exact zero_le _

theorem ringClosure_le_fieldClosure (x : Nimber) : ringClosure x ≤ fieldClosure x := by
  rw [(IsField.fieldClosure x).ringClosure_le_iff]
  exact le_fieldClosure x

theorem groupClosure_le_fieldClosure (x : Nimber) : groupClosure x ≤ fieldClosure x :=
  (groupClosure_le_ringClosure x).trans (ringClosure_le_fieldClosure x)

theorem not_bddAbove_setOf_isField : ¬ BddAbove (setOf IsField) :=
  fun ⟨a, ha⟩ ↦ (ha (.fieldClosure _)).not_gt <| (Order.lt_succ a).trans_le (le_fieldClosure _)

/-- The normal enumerator function for fields. -/
def enumField (x : Ordinal) : Nimber :=
  ∗(Ordinal.enumOrd {y | IsField (∗y)} x)

@[simp]
theorem range_enumField : Set.range enumField = setOf IsField :=
  Ordinal.range_enumOrd not_bddAbove_setOf_isField

theorem mem_range_enumField_iff {x : Nimber} : x ∈ Set.range enumField ↔ IsField x :=
  Set.ext_iff.1 range_enumField _

theorem IsField.enumField (x : Ordinal) : IsField (enumField x) :=
  mem_range_enumField_iff.1 ⟨x, rfl⟩

theorem isNormal_enumField : Order.IsNormal enumField :=
  Ordinal.isNormal_enumOrd (fun _ ↦ IsField.sSup) not_bddAbove_setOf_isField

@[simp]
theorem enumField_le_enumField_iff {x y} : enumField x ≤ enumField y ↔ x ≤ y :=
  isNormal_enumField.strictMono.le_iff_le

@[simp]
theorem enumField_lt_enumField_iff {x y} : enumField x < enumField y ↔ x < y :=
  isNormal_enumField.strictMono.lt_iff_lt

@[simp]
theorem enumField_inj {x y} : enumField x = enumField y ↔ x = y :=
  isNormal_enumField.strictMono.injective.eq_iff

@[simp]
theorem enumField_zero : enumField 0 = ∗2 := by
  rw [enumField, of.eq_iff_eq, Ordinal.enumOrd_zero]
  apply le_antisymm
  · exact csInf_le' IsField.two
  · rw [le_csInf_iff'']
    · exact fun _ ↦ IsField.two_le
    · exact ⟨_, IsField.two⟩

theorem exists_isField_btwn {x : Nimber} (ne : 1 < x) : ∃ l u,
    IsField l ∧ IsField u ∧ l ≤ x ∧ x < u ∧ ∀ z, IsField z → l < z → u ≤ z := by
  obtain ⟨a, hl, hu⟩ := isNormal_enumField.exists_btwn' (x := x) (by simpa [← succ_one])
  refine ⟨_, _, .enumField _, .enumField _, hl, hu, fun b hb hab ↦ ?_⟩
  obtain ⟨b, rfl⟩ := mem_range_enumField_iff.2 hb
  simpa using hab

end Subfield
end Nimber
end
