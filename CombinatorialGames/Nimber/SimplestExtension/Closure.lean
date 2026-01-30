/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/
import CombinatorialGames.Nimber.SimplestExtension.Basic
import Mathlib.SetTheory.Cardinal.Subfield

/-!
# Closures

We define `groupClosure`, `ringClosure`, and `fieldClosure`, which represent the smallest nimber
equal or greater to another, which satisfies `IsGroup`, `IsRing`, or `IsField`.
-/

universe u

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
    · -- todo: generalize `Subfield.charP` to division rings
      -- have := Subfield.charP (⊥ : Subfield R) p
      have := (⊥ : Subfield R).subtype.charP (⊥ : Subfield R).subtype_injective p
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

theorem le_groupClosure (x : Nimber) : x ≤ groupClosure x := by
  by_contra! hx
  exact (mem_addSubgroupClosure_Iio.1 (mem_closure_of_mem hx)).false

protected theorem IsGroup.groupClosure (x : Nimber) : IsGroup (groupClosure x) where
  ne_zero := (mem_addSubgroupClosure_Iio.1 (AddSubgroup.zero_mem _)).ne'
  add_lt y z := by
    simp_rw [← mem_addSubgroupClosure_Iio]
    exact AddSubgroup.add_mem _

theorem IsGroup.groupClosure_le_iff {x y : Nimber} (h : IsGroup x) :
    groupClosure y ≤ x ↔ y ≤ x where
  mp := le_trans (le_groupClosure y)
  mpr hyx := by
    rw [← not_lt, ← mem_addSubgroupClosure_Iio]
    intro hx
    have := h.closure_Iio ▸ closure_mono (Iio_subset_Iio hyx) hx
    simpa

theorem IsGroup.lt_groupClosure_iff {x y : Nimber} (h : IsGroup x) :
    x < groupClosure y ↔ x < y :=
  le_iff_le_iff_lt_iff_lt.1 h.groupClosure_le_iff

theorem groupClosure_mono : Monotone groupClosure := by
  intro x y h
  rw [(IsGroup.groupClosure y).groupClosure_le_iff]
  exact h.trans (le_groupClosure y)

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

theorem le_ringClosure (x : Nimber) : x ≤ ringClosure x := by
  by_contra! hx
  exact (mem_subringClosure_Iio.1 (mem_closure_of_mem hx)).false

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
    ringClosure y ≤ x ↔ y ≤ x where
  mp := le_trans (le_ringClosure y)
  mpr hyx := by
    rw [← not_lt, ← mem_subringClosure_Iio]
    intro hx
    have := h.closure_Iio ▸ closure_mono (Iio_subset_Iio hyx) hx
    simpa

theorem IsRing.lt_ringClosure_iff {x y : Nimber} (h : IsRing x) :
    x < ringClosure y ↔ x < y :=
  le_iff_le_iff_lt_iff_lt.1 h.ringClosure_le_iff

theorem ringClosure_mono : Monotone ringClosure := by
  intro x y h
  rw [(IsRing.ringClosure y).ringClosure_le_iff]
  exact h.trans (le_ringClosure y)

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

theorem le_fieldClosure (x : Nimber) : x ≤ fieldClosure x := by
  by_contra! hx
  exact (mem_subfieldClosure_Iio.1 (mem_closure_of_mem hx)).false

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
    fieldClosure y ≤ x ↔ y ≤ x where
  mp := le_trans (le_fieldClosure y)
  mpr hyx := by
    rw [← not_lt, ← mem_subfieldClosure_Iio]
    intro hx
    have := h.closure_Iio ▸ closure_mono (Iio_subset_Iio hyx) hx
    simpa

theorem IsField.lt_fieldClosure_iff {x y : Nimber} (h : IsField x) :
    x < fieldClosure y ↔ x < y :=
  le_iff_le_iff_lt_iff_lt.1 h.fieldClosure_le_iff

theorem fieldClosure_mono : Monotone fieldClosure := by
  intro x y h
  rw [(IsField.fieldClosure y).fieldClosure_le_iff]
  exact h.trans (le_fieldClosure y)

end Subfield
end Nimber
end
