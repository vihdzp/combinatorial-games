/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.SignExpansion.Basic

/-!
# Small sign expansions

A sign expansion is *small* if it is eventually constant. All terminating sign expansions are small.
-/

universe u
noncomputable section
namespace SignExpansion
open Order Set

def birthday (e : SignExpansion.{u}) : WithTop NatOrdinal.{u} :=
  ⨅ (i : NatOrdinal.{u}) (_ : (e '' Ici i).Subsingleton), WithTop.some i

def birthday' (e : SignExpansion.{u}) : NatOrdinal.{u} :=
  e.birthday.untopD 0

theorem isGLB_birthday (e : SignExpansion.{u}) :
    IsGLB (WithTop.some '' {i | (e '' Ici i).Subsingleton}) e.birthday :=
  isGLB_biInf

theorem eq_of_birthday_le {e : SignExpansion.{u}} {o o' : NatOrdinal.{u}}
    (ho : e.birthday ≤ o) (ho' : e.birthday ≤ o') : e o = e o' := by
  have hbb := isGLB_birthday e
  have h : ¬IsPredPrelimit e.birthday := by
    cases hb : e.birthday with
    | top => simp [hb] at ho
    | coe u =>
      intro hu
      have lele := hu.isGLB_Ioi.right fun x hux => succ_le_of_lt hux
      simp at lele
  obtain ⟨k, hk, hkb⟩ := hbb.mem_of_not_isPredPrelimit h
  rw [← hkb, WithTop.coe_le_coe] at ho ho'
  exact hk (Set.mem_image_of_mem e ho) (Set.mem_image_of_mem e ho')

theorem coe_lt_birthday_iff {e : SignExpansion.{u}} {o : NatOrdinal.{u}} :
    o < e.birthday ↔ ∃ o' > o, e o ≠ e o' := by
  constructor
  · intro h
    contrapose! h
    apply iInf₂_le
    apply Set.subsingleton_of_subset_singleton
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_singleton_iff]
    rw [mem_Ici] at hx
    apply eq_or_lt_of_le at hx
    obtain hx | hx := hx
    · exact congrArg e hx.symm
    · exact (h x hx).symm
  · intro ⟨o', ho', heo⟩
    apply lt_of_not_ge
    intro h
    exact heo (eq_of_birthday_le h (h.trans (WithTop.coe_le_coe.mpr ho'.le)))

theorem birthday_le_coe_iff {e : SignExpansion.{u}} {o : NatOrdinal.{u}} :
    e.birthday ≤ o ↔ ∀ o' > o, e o = e o' := by
  simpa using coe_lt_birthday_iff.not

def IsSmall (e : SignExpansion.{u}) : Prop :=
  birthday e < ⊤

theorem isSmall_iff_birthday_lt_top {e : SignExpansion.{u}} : e.IsSmall ↔ e.birthday < ⊤ := .rfl

theorem isSmall_iff_exists_image_subsingleton {e : SignExpansion.{u}} :
    e.IsSmall ↔ ∃ o, (e '' Ici o).Subsingleton := by
  rw [isSmall_iff_birthday_lt_top]
  constructor
  · rw [WithTop.lt_top_iff_ne_top, WithTop.ne_top_iff_exists]
    intro ⟨o, ho⟩
    refine ⟨o, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [mem_Ici, ← WithTop.coe_le_coe, ho] at ha hb
    exact eq_of_birthday_le ha hb
  · intro ⟨o, ho⟩
    apply (WithTop.coe_lt_top o).trans_le'
    rw [birthday_le_coe_iff]
    intro o' hoo'
    exact ho (mem_image_of_mem e (mem_Ici.2 le_rfl)) (mem_image_of_mem e hoo'.le)

theorem birthday_eq_top {e : SignExpansion.{u}} : e.birthday = ⊤ ↔ ¬e.IsSmall := by
  rw [isSmall_iff_birthday_lt_top, not_lt, top_le_iff]

theorem birthday_of_not_isSmall {e : SignExpansion.{u}} (he : ¬e.IsSmall) :
    e.birthday = ⊤ := birthday_eq_top.2 he

theorem birthday'_of_not_isSmall {e : SignExpansion.{u}} (he : ¬e.IsSmall) :
    e.birthday' = 0 := by
  simp [birthday', birthday_of_not_isSmall he]

theorem coe_birthday' {e : SignExpansion.{u}} (he : e.IsSmall) :
    e.birthday' = e.birthday := by
  rw [birthday']
  cases h : e.birthday with
  | top => rw [birthday_eq_top] at h; contradiction
  | coe _ => rw [WithTop.untopD_coe]

theorem birthday_le_size (e : SignExpansion.{u}) : e.birthday ≤ e.size := by
  cases h : e.size with
  | top => simp
  | coe x =>
    rw [birthday_le_coe_iff]
    intro o ho
    apply WithTop.coe_lt_coe.2 at ho
    rw [← h] at ho
    rw [apply_of_size_le h.le, apply_of_size_le ho.le]
