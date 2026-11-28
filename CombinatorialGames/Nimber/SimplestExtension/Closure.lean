/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/
module

public import CombinatorialGames.Nimber.SimplestExtension.Basic
public import Mathlib.Order.OrdContinuous
public import Mathlib.SetTheory.Cardinal.Cofinality.Club

import Mathlib.Algebra.Field.ZMod
import Mathlib.SetTheory.Cardinal.Subfield
import Mathlib.Algebra.CharP.Algebra

/-!
# Closures

We define `groupClosure`, `ringClosure`, and `fieldClosure`, which represent the smallest nimber
equal or greater to another, which satisfies `IsGroup`, `IsRing`, or `IsField`.

The analogous `algClosure` is defined in `Nimber.SimplestExtension.Algebraic`.
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

instance Subfield.small_closure (s : Set R) [DivisionRing R] [Small.{u} s] :
    Small.{u} (Subfield.closure s) := by
  rw [Cardinal.small_iff_lift_mk_lt_univ] at *
  apply (Cardinal.lift_le.2 (Subfield.cardinalMk_closure_le_max s)).trans_lt
  simpa

instance Subfield.small_closure' (s : Set R) [DivisionRing R] [Small.{u} s] :
    Small.{u} (Subfield.closure s : Set R) :=
  Subfield.small_closure s

/-- The intended use of this theorem is for `c` some kind of closure operator, e.g. the smallest
element in the set that's `≥` than the input. -/
theorem IsClub.exists_between_closure {α : Type*}
    [LinearOrder α] [WellFoundedLT α] [NoMaxOrder α] [SuccOrder α]
    {s : Set α} (hs : IsClub s) {x : α} (hx : ∃ y ∈ s, y ≤ x)
    {c : α → α} (hc : ∀ x, x ≤ c x) (hc' : ∀ x, c x ∈ s) :
    ∃ l ∈ s, l ≤ x ∧ x < c (Order.succ l) := by
  obtain ⟨l, hl, r, hr, hlx, hxu, H⟩ := hs.exists_between hx
  exact ⟨l, hl, hlx, hxu.trans_le (H _ (hc' (Order.succ l)) (Order.succ_le_iff.1 (hc _)))⟩

end

noncomputable section

namespace Nimber
open Set

instance : IsRegularCardinalOrder Nimber :=
  inferInstanceAs (IsRegularCardinalOrder Ordinal)

/-! ### Groups -/

section AddSubgroup
open AddSubgroup

theorem isGroup_sInf_compl (s : AddSubgroup Nimber) (hs : s ≠ ⊤) : IsGroup (sInf sᶜ) := by
  have hsn : (s : Set Nimber)ᶜ.Nonempty := by contrapose! hs; simpa using hs
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
  refine (isLowerSet_addSubgroupClosure (.Iio x)).eq_univ_or_Iio.resolve_left fun hx ↦ ?_
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

@[simp]
theorem IsGroup.groupClosure_eq {x : Nimber} (h : IsGroup x) : groupClosure x = x := by
  apply (le_groupClosure x).antisymm'
  rw [h.groupClosure_le_iff]

@[gcongr]
theorem groupClosure_monotone : Monotone groupClosure := by
  intro x y
  rw [(IsGroup.groupClosure y).groupClosure_le_iff]
  exact (le_groupClosure y).trans'

theorem leftOrdContinuous_groupClosure : LeftOrdContinuous groupClosure := by
  intro s x hs₀ hs
  have hbdd := groupClosure_monotone.map_bddAbove hs.bddAbove
  have Hs := IsGroup.sSup (by simp) (by simpa) hbdd
  refine ⟨groupClosure_monotone.mem_upperBounds_image hs.1, fun y hy ↦ (csSup_le' hy).trans' ?_⟩
  rw [Hs.groupClosure_le_iff, ← hs.csSup_eq hs₀]
  exact csSup_le' fun z hz ↦ (le_groupClosure _).trans <| le_csSup hbdd (mem_image_of_mem _ hz)

@[simp]
theorem groupClosure_zero : groupClosure 0 = 1 := by
  rw [← Iio_inj, ← coe_addSubgroupClosure_Iio]
  simp

theorem groupClosure_one : groupClosure 1 = 1 :=
  IsGroup.one.groupClosure_eq

theorem groupClosure_two : groupClosure (∗2) = ∗2 :=
  IsGroup.two.groupClosure_eq

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
    contrapose h
    exact h ▸ IsGroup.groupClosure x

theorem isClub_ofPred_isGroup : IsClub (ofPred IsGroup) where
  isCofinal a := ⟨_, .groupClosure _, le_groupClosure a⟩
  dirSupClosed s hs hs₀ _ a ha := by
    rw [← ha.csSup_eq hs₀]
    exact IsGroup.sSup hs hs₀ ha.bddAbove

private theorem exists_isGroup_le {x : Nimber} (hx : x ≠ 0) : ∃ y, IsGroup y ∧ y ≤ x :=
  ⟨1, by simpa⟩

theorem exists_isGroup_between {x : Nimber} (hx : x ≠ 0) :
    ∃ l, IsGroup l ∧ ∃ u, IsGroup u ∧ l ≤ x ∧ x < u ∧ ∀ z, IsGroup z → l < z → u ≤ z :=
  isClub_ofPred_isGroup.exists_between (exists_isGroup_le hx)

theorem exists_isGroup_between' {x : Nimber} (hx : x ≠ 0) :
    ∃ l, IsGroup l ∧ l ≤ x ∧ x < groupClosure (Order.succ l) :=
  isClub_ofPred_isGroup.exists_between_closure (exists_isGroup_le hx)
    le_groupClosure IsGroup.groupClosure

/-- The normal enumerator function for groups. (This is equal to `∗(2 ^ x)`.) -/
def enumGroup : Ordinal ↪o Nimber :=
  .ofStrictMono (fun x ↦ Order.enum _ isClub_ofPred_isGroup.isCofinal (of x)) fun _ ↦ by simp

theorem enumGroup_def (x : Ordinal) :
    enumGroup x = Order.enum _ isClub_ofPred_isGroup.isCofinal (of x) :=
  (rfl)

theorem enumGroup_def' (x : Ordinal) :
    enumGroup x = of (Order.enum {x | IsGroup (∗x)}
      (by exact isClub_ofPred_isGroup.isCofinal) x) :=
  (rfl)

@[simp]
theorem range_enumGroup : range enumGroup = ofPred IsGroup := by
  erw [enumGroup, OrderEmbedding.coe_ofStrictMono, EquivLike.range_comp]
  exact Subtype.range_val

theorem mem_range_enumGroup_iff {x : Nimber} : x ∈ range enumGroup ↔ IsGroup x :=
  Set.ext_iff.1 range_enumGroup _

alias ⟨_, IsGroup.mem_range_enumGroup⟩ := mem_range_enumGroup_iff

theorem IsGroup.enumGroup (x : Ordinal) : IsGroup (enumGroup x) :=
  mem_range_enumGroup_iff.1 ⟨x, rfl⟩

theorem isNormal_enumGroup : Order.IsNormal enumGroup :=
  isClub_ofPred_isGroup.isNormal_enum

theorem of_le_enumGroup (x : Ordinal) : ∗x ≤ enumGroup x :=
  isNormal_enumGroup.strictMono.le_apply

theorem enumGroup_add_one (x : Ordinal) :
    enumGroup (x + 1) = groupClosure (Order.succ (enumGroup x)) := by
  apply le_antisymm
  · rw [enumGroup_def, ← succ_of]
    apply Order.enum_succ_le_of_lt (IsGroup.groupClosure _)
    rw [← enumGroup_def, (IsGroup.enumGroup _).lt_groupClosure_iff, Order.lt_succ_iff]
  · rw [(IsGroup.enumGroup _).groupClosure_le_iff, Order.succ_le_iff]
    exact isNormal_enumGroup.strictMono (lt_add_one x)

theorem enumGroup_eq_two_opow (x : Ordinal) : enumGroup x = ∗(2 ^ x) := by
  rw [enumGroup_def', of.eq_iff_eq]
  have : {x | (of x).IsGroup} = range fun y : Ordinal ↦ 2 ^ y := by
    ext; simp [isGroup_iff_mem_range_two_opow]
  rw! [this, Order.enum_range]
  · rfl
  · intro a b h
    rwa [Ordinal.opow_lt_opow_iff_right one_lt_two]

@[simp]
theorem enumGroup_zero : enumGroup 0 = 1 := by
  simp [enumGroup_eq_two_opow]

@[simp]
theorem enumGroup_one : enumGroup 1 = ∗2 := by
  simp [enumGroup_eq_two_opow]

theorem enumGroup_natCast (n : ℕ) : enumGroup n = ∗(2 ^ n) := by
  simp [enumGroup_eq_two_opow]

end AddSubgroup

/-! ### Rings -/

section Subring
open Subring

theorem isRing_sInf_compl (s : Subring Nimber) (hs : s ≠ ⊤) : IsRing (sInf sᶜ) := by
  have hsn : (s : Set Nimber)ᶜ.Nonempty := by contrapose! hs; simpa using hs
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
  refine (isLowerSet_subringClosure (.Iio x)).eq_univ_or_Iio.resolve_left fun hx ↦ ?_
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

@[simp]
theorem IsRing.ringClosure_eq {x : Nimber} (h : IsRing x) : ringClosure x = x := by
  apply (le_ringClosure x).antisymm'
  rw [h.ringClosure_le_iff]

@[gcongr]
theorem ringClosure_monotone : Monotone ringClosure := by
  intro x y
  rw [(IsRing.ringClosure y).ringClosure_le_iff]
  exact (le_ringClosure y).trans'

theorem leftOrdContinuous_ringClosure : LeftOrdContinuous ringClosure := by
  intro s x hs₀ hs
  have hbdd := ringClosure_monotone.map_bddAbove hs.bddAbove
  have Hs := IsRing.sSup (by simp) (by simpa) hbdd
  refine ⟨ringClosure_monotone.mem_upperBounds_image hs.1, fun y hy ↦ (csSup_le' hy).trans' ?_⟩
  rw [Hs.ringClosure_le_iff, ← hs.csSup_eq hs₀]
  exact csSup_le' fun z hz ↦ (le_ringClosure _).trans <| le_csSup hbdd (mem_image_of_mem _ hz)

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
    exact ringClosure_monotone zero_le_one

theorem ringClosure_two : ringClosure (∗2) = ∗2 :=
  IsRing.two.ringClosure_eq

@[simp]
theorem groupClosure_le_ringClosure (x : Nimber) : groupClosure x ≤ ringClosure x := by
  rw [(IsRing.ringClosure x).groupClosure_le_iff]
  exact le_ringClosure x

@[simp]
theorem ringClosure_groupClosure (x : Nimber) : ringClosure (groupClosure x) = ringClosure x := by
  apply le_antisymm
  · rw [(IsRing.ringClosure x).ringClosure_le_iff]
    exact groupClosure_le_ringClosure x
  · exact ringClosure_monotone (le_groupClosure x)

theorem isClub_ofPred_isRing : IsClub (ofPred IsRing) where
  isCofinal a := ⟨_, .ringClosure _, le_ringClosure a⟩
  dirSupClosed s hs hs₀ _ a ha := by
    rw [← ha.csSup_eq hs₀]
    exact IsRing.sSup hs hs₀ ha.bddAbove

private theorem exists_isRing_le {x : Nimber} (hx : 1 < x) : ∃ y, IsRing y ∧ y ≤ x :=
  ⟨∗2, IsRing.two, by rwa [← succ_one, Order.succ_le_iff]⟩

theorem exists_isRing_between {x : Nimber} (hx : 1 < x) :
    ∃ l, IsRing l ∧ ∃ u, IsRing u ∧ l ≤ x ∧ x < u ∧ ∀ z, IsRing z → l < z → u ≤ z :=
  isClub_ofPred_isRing.exists_between (exists_isRing_le hx)

theorem exists_isRing_between' {x : Nimber} (hx : 1 < x) :
    ∃ l, IsRing l ∧ l ≤ x ∧ x < ringClosure (Order.succ l) :=
  isClub_ofPred_isRing.exists_between_closure (exists_isRing_le hx)
    le_ringClosure IsRing.ringClosure

/-- The normal enumerator function for rings. -/
def enumRing : Ordinal ↪o Nimber :=
  .ofStrictMono (fun x ↦ Order.enum _ isClub_ofPred_isRing.isCofinal (of x)) fun _ ↦ by simp

theorem enumRing_def (x : Ordinal) :
    enumRing x = Order.enum _ isClub_ofPred_isRing.isCofinal (of x) :=
  (rfl)

theorem enumRing_def' (x : Ordinal) :
    enumRing x = of (Order.enum {x | IsRing (∗x)}
      (by exact isClub_ofPred_isRing.isCofinal) x) :=
  (rfl)

@[simp]
theorem range_enumRing : range enumRing = ofPred IsRing := by
  erw [enumRing, OrderEmbedding.coe_ofStrictMono, EquivLike.range_comp]
  exact Subtype.range_val

theorem mem_range_enumRing_iff {x : Nimber} : x ∈ range enumRing ↔ IsRing x :=
  Set.ext_iff.1 range_enumRing _

alias ⟨_, IsRing.mem_range_enumRing⟩ := mem_range_enumRing_iff

theorem IsRing.enumRing (x : Ordinal) : IsRing (enumRing x) :=
  mem_range_enumRing_iff.1 ⟨x, rfl⟩

theorem isNormal_enumRing : Order.IsNormal enumRing :=
  isClub_ofPred_isRing.isNormal_enum

theorem of_le_enumRing (x : Ordinal) : ∗x ≤ enumRing x :=
  isNormal_enumRing.strictMono.le_apply

theorem enumGroup_le_enumRing (x : Ordinal) : enumGroup x ≤ enumRing x :=
  Order.enum_anti fun _ ↦ IsRing.toIsGroup

theorem enumRing_add_one (x : Ordinal) :
    enumRing (x + 1) = ringClosure (Order.succ (enumRing x)) := by
  apply le_antisymm
  · rw [enumRing_def, ← succ_of]
    apply Order.enum_succ_le_of_lt (IsRing.ringClosure _)
    rw [← enumRing_def, (IsRing.enumRing _).lt_ringClosure_iff, Order.lt_succ_iff]
  · rw [(IsRing.enumRing _).ringClosure_le_iff, Order.succ_le_iff]
    exact isNormal_enumRing.strictMono (lt_add_one x)

@[simp]
theorem enumRing_zero : enumRing 0 = ∗2 := by
  rw [enumRing_def, of_zero, ← bot_eq_zero, Order.enum_bot]
  apply le_antisymm
  · exact csInf_le' IsRing.two
  · rw [le_csInf_iff']
    · exact fun _ ↦ IsRing.two_le
    · exact ⟨_, IsRing.two⟩

end Subring

/-! ### Fields -/

section Subfield
open Subfield

theorem isField_sInf_compl (s : Subfield Nimber) (hs : s ≠ ⊤) : IsField (sInf sᶜ) := by
  have hsn : (s : Set Nimber)ᶜ.Nonempty := by contrapose! hs; simpa using hs
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

theorem subfieldClosure_Iio_eq_Iio (x : Nimber) : ∃ y, (closure (Iio x) : Set Nimber) = Iio y := by
  refine (isLowerSet_subfieldClosure (.Iio x)).eq_univ_or_Iio.resolve_left fun hx ↦ ?_
  have H := Subfield.small_closure' (Iio x)
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

@[simp]
theorem IsField.fieldClosure_eq {x : Nimber} (h : IsField x) : fieldClosure x = x := by
  apply (le_fieldClosure x).antisymm'
  rw [h.fieldClosure_le_iff]

@[gcongr]
theorem fieldClosure_monotone : Monotone fieldClosure := by
  intro x y
  rw [(IsField.fieldClosure y).fieldClosure_le_iff]
  exact (le_fieldClosure y).trans'

theorem leftOrdContinuous_fieldClosure : LeftOrdContinuous fieldClosure := by
  intro s x hs₀ hs
  have hbdd := fieldClosure_monotone.map_bddAbove hs.bddAbove
  have Hs := IsField.sSup (by simp) (by simpa) hbdd
  refine ⟨fieldClosure_monotone.mem_upperBounds_image hs.1, fun y hy ↦ (csSup_le' hy).trans' ?_⟩
  rw [Hs.fieldClosure_le_iff, ← hs.csSup_eq hs₀]
  exact csSup_le' fun z hz ↦ (le_fieldClosure _).trans <| le_csSup hbdd (mem_image_of_mem _ hz)

@[simp]
theorem fieldClosure_zero : fieldClosure 0 = ∗2 := by
  apply le_antisymm
  · rw [IsField.two.fieldClosure_le_iff]
    apply zero_le
  · rw [← ringClosure_zero, (IsField.fieldClosure 0).ringClosure_le_iff]
    apply zero_le

@[simp]
theorem fieldClosure_one : fieldClosure 1 = ∗2 := by
  apply le_antisymm
  · rw [IsField.two.fieldClosure_le_iff]
    simp
  · rw [← fieldClosure_zero]
    exact fieldClosure_monotone zero_le_one

theorem fieldClosure_two : fieldClosure (∗2) = ∗2 :=
  IsField.two.fieldClosure_eq

@[simp]
theorem ringClosure_le_fieldClosure (x : Nimber) : ringClosure x ≤ fieldClosure x := by
  rw [(IsField.fieldClosure x).ringClosure_le_iff]
  exact le_fieldClosure x

@[simp]
theorem groupClosure_le_fieldClosure (x : Nimber) : groupClosure x ≤ fieldClosure x :=
  (groupClosure_le_ringClosure x).trans (ringClosure_le_fieldClosure x)

@[simp]
theorem fieldClosure_ringClosure (x : Nimber) : fieldClosure (ringClosure x) = fieldClosure x := by
  apply le_antisymm
  · rw [(IsField.fieldClosure x).fieldClosure_le_iff]
    exact ringClosure_le_fieldClosure x
  · exact fieldClosure_monotone (le_ringClosure x)

@[simp]
theorem fieldClosure_groupClosure (x : Nimber) :
    fieldClosure (groupClosure x) = fieldClosure x := by
  rw [← fieldClosure_ringClosure, ringClosure_groupClosure, fieldClosure_ringClosure]

theorem isClub_ofPred_isField : IsClub (ofPred IsField) where
  isCofinal a := ⟨_, .fieldClosure _, le_fieldClosure a⟩
  dirSupClosed s hs hs₀ _ a ha := by
    rw [← ha.csSup_eq hs₀]
    exact IsField.sSup hs hs₀ ha.bddAbove

private theorem exists_isField_le {x : Nimber} (hx : 1 < x) : ∃ y, IsField y ∧ y ≤ x :=
  ⟨∗2, IsField.two, by rwa [← succ_one, Order.succ_le_iff]⟩

theorem exists_isField_between {x : Nimber} (hx : 1 < x) :
    ∃ l, IsField l ∧ ∃ u, IsField u ∧ l ≤ x ∧ x < u ∧ ∀ z, IsField z → l < z → u ≤ z :=
  isClub_ofPred_isField.exists_between (exists_isField_le hx)

theorem exists_isField_between' {x : Nimber} (hx : 1 < x) :
    ∃ l, IsField l ∧ l ≤ x ∧ x < fieldClosure (Order.succ l) :=
  isClub_ofPred_isField.exists_between_closure (exists_isField_le hx)
    le_fieldClosure IsField.fieldClosure

/-- The normal enumerator function for fields. -/
def enumField : Ordinal ↪o Nimber :=
  .ofStrictMono (fun x ↦ Order.enum _ isClub_ofPred_isField.isCofinal (of x)) fun _ ↦ by simp

theorem enumField_def (x : Ordinal) :
    enumField x = Order.enum _ isClub_ofPred_isField.isCofinal (of x) :=
  (rfl)

theorem enumField_def' (x : Ordinal) :
    enumField x = of (Order.enum {x | IsField (∗x)}
      (by exact isClub_ofPred_isField.isCofinal) x) :=
  (rfl)

@[simp]
theorem range_enumField : range enumField = ofPred IsField := by
  erw [enumField, OrderEmbedding.coe_ofStrictMono, EquivLike.range_comp]
  exact Subtype.range_val

theorem mem_range_enumField_iff {x : Nimber} : x ∈ range enumField ↔ IsField x :=
  Set.ext_iff.1 range_enumField _

alias ⟨_, IsField.mem_range_enumField⟩ := mem_range_enumField_iff

theorem IsField.enumField (x : Ordinal) : IsField (enumField x) :=
  mem_range_enumField_iff.1 ⟨x, rfl⟩

theorem isNormal_enumField : Order.IsNormal enumField :=
  isClub_ofPred_isField.isNormal_enum

theorem of_le_enumField (x : Ordinal) : ∗x ≤ enumField x :=
  isNormal_enumField.strictMono.le_apply

theorem enumRing_le_enumField (x : Ordinal) : enumRing x ≤ enumField x :=
  Order.enum_anti fun _ ↦ IsField.toIsRing

theorem enumGroup_le_enumField (x : Ordinal) : enumGroup x ≤ enumField x :=
  (enumGroup_le_enumRing x).trans (enumRing_le_enumField x)

theorem enumField_add_one (x : Ordinal) :
    enumField (x + 1) = fieldClosure (Order.succ (enumField x)) := by
  apply le_antisymm
  · rw [enumField_def, ← succ_of]
    apply Order.enum_succ_le_of_lt (IsField.fieldClosure _)
    rw [← enumField_def, (IsField.enumField _).lt_fieldClosure_iff, Order.lt_succ_iff]
  · rw [(IsField.enumField _).fieldClosure_le_iff, Order.succ_le_iff]
    exact isNormal_enumField.strictMono (lt_add_one x)

@[simp]
theorem enumField_zero : enumField 0 = ∗2 := by
  rw [enumField_def, of_zero, ← bot_eq_zero, Order.enum_bot]
  apply le_antisymm
  · exact csInf_le' IsField.two
  · rw [le_csInf_iff']
    · exact fun _ h ↦ h.two_le
    · exact ⟨_, IsField.two⟩

end Subfield
end Nimber
end
