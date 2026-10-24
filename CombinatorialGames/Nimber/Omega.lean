/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Nimber.SimplestExtension.Algebraic

import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Omega numbers are algebraically closed

We prove that for `x ≠ 0`, the nimbers `∗ω_ x` are algebraically closed, and that there are `ω_ x`
algebraically closed nimbers below `∗ω_ x`.
-/

public section

universe u v

open Cardinal Order Ordinal Set

/-! ### For Mathlib -/

attribute [local implicit_reducible] Function.Injective in
/-- Restrict an order isomorphism to an initial segment. -/
def OrderIso.restrictIio {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β) (x : α) :
    Iio x ≤i β where
  toFun x := e x
  inj' _ := by simp [Subtype.coe_inj]
  map_rel_iff' := by simp
  mem_range_of_rel' y z h := by
    refine ⟨⟨e.symm z, y.2.trans' ?_⟩, ?_⟩
    · simpa [e.symm_apply_lt]
    · simp

theorem InitialSeg.le_of_strictMono {α β : Type*} [LinearOrder α] [LinearOrder β] [WellFoundedLT α]
    (f : α ≤i β) {g : α → β} (hg : StrictMono g) (x : α) : f x ≤ g x := by
  induction x using WellFoundedLT.induction with | ind x IH
  by_contra! hx
  obtain ⟨y, hy⟩ := f.mem_range_of_le hx.le
  rw [← hy, f.lt_iff_lt] at hx
  apply (IH y hx).not_gt
  rwa [hy, hg.lt_iff_lt]

theorem Order.enum_le_of_strictMono {α : Type*} [LinearOrder α] [WellFoundedLT α]
    [IsRegularCardinalOrder α] {s : Set α} (hs : IsCofinal s) {x y : α}
    {f : Iio x → s} (hf : StrictMono f) (hy : y < x) : Order.enum s hs y ≤ f ⟨y, mem_Iio.2 hy⟩ :=
  InitialSeg.le_of_strictMono ((Order.enum s hs).restrictIio x) hf ⟨y, hy⟩

open Notation in
theorem Ordinal.enum_lt_of_lt_ord_cof {s : Set Ordinal} (hs : IsCofinal s) {x y : Ordinal}
    (hx : ∀ a < x, ∃ b ∈ s, b ∈ Ico a x) (hy : y < x.cof.ord) : Order.enum s hs y < x := by
  let f : Iio x.cof.ord ≤i Iio x ↓∩ s := by
    apply (Ordinal.type_le_iff.1 _).some
    rw [type_lt_Iio, lift_ord, lift_cof, ord_le, card_type, ← cof_Iio]
    refine cof_le fun ⟨a, ha⟩ ↦ ?_
    obtain ⟨b, hb, ⟨hab, hbx⟩⟩ := hx a ha
    exact ⟨⟨b, hbx⟩, hb, hab⟩
  let g (a : Iio x.cof.ord) : s := ⟨f a, (f a).2⟩
  have hg : StrictMono g := fun _ ↦ by simp [g]
  exact (Subtype.coe_le_coe.2 <| enum_le_of_strictMono hs hg hy).trans_lt (f _).1.2

theorem Ordinal.enum_ord_cof_le {s : Set Ordinal} (hs : IsClub s) {x : Ordinal}
    (hx : ∀ a < x, ∃ b ∈ s, b ∈ Ico a x) (hx' : IsSuccLimit x) :
    Order.enum s hs.isCofinal x.cof.ord ≤ x := by
  apply (hs.isNormal_enum.le_iff_forall_le _).2
  · exact fun y hy ↦ (Ordinal.enum_lt_of_lt_ord_cof _ hx hy).le
  · apply isSuccLimit_ord
    rwa [aleph0_le_cof_iff, one_lt_cof_iff]

@[simp]
theorem Ordinal.one_le_lift {x : Ordinal.{u}} : 1 ≤ Ordinal.lift.{v} x ↔ 1 ≤ x := by
  simpa using Ordinal.lift_le (a := 1)

theorem Ordinal.card_le_aleph_iff {x y : Ordinal} : x.card ≤ ℵ_ y ↔ x < ω_ (y + 1) := by
  rw [card_le_iff, succ_aleph, ord_aleph]

@[simp]
theorem Ordinal.ofNat_opow_omega0 {n : ℕ} [n.AtLeastTwo] : ofNat(n) ^ ω = ω :=
  natCast_opow_omega0 Nat.AtLeastTwo.one_lt

namespace Nimber

/-! ### ω is a field -/

theorem IsAlgClosed.omega0_le {x : Nimber} (hx : IsAlgClosed x) : ∗ω ≤ x := by
  contrapose! hx
  simp_rw [← val_lt_iff, lt_omega0, val_eq_iff] at hx
  obtain ⟨n, rfl⟩ := hx
  intro hn
  have hi : Infinite (Iio _) := hn.isAlgClosed.instInfinite
  rw [← Cardinal.aleph0_le_mk_iff, cardinalMk_Iio, lift_card, aleph0_le_card, omega0_le_lift] at hi
  simpa using hi.not_gt

-- TODO: prove this as a corollary of the classification of quadratic extensions.
private theorem enumField_natCast_lt_omega0 (n : ℕ) : enumField n < ∗ω := by
  induction n with
  | zero => simp
  | succ n IH =>
    have ht : (enumField n).leastNoRoots ≠ ⊤ := by
      intro ht
      rw [← isAlgClosed_iff_leastNoRoots_eq_top (IsField.enumField _).toIsRing] at ht
      exact ht.omega0_le.not_gt IH
    rw [Nat.cast_add_one, enumField_add_one,
      (IsField.enumField _).fieldClosure_succ_eq_pow_natDegree_leastNoRoots ht, of.lt_iff_lt]
    rw [← val_lt_iff] at IH
    obtain ⟨m, hm⟩ := lt_omega0.1 IH
    rw [hm, ← natCast_pow]
    exact natCast_lt_omega0 _

@[simp]
theorem enumField_omega0 : enumField ω = ∗ω := by
  apply (of_le_enumField _).antisymm'
  simp_rw [isNormal_enumField.le_iff_forall_le isSuccLimit_omega0, lt_omega0]
  rintro _ ⟨n, rfl⟩
  exact (enumField_natCast_lt_omega0 n).le

@[simp]
theorem enumRing_omega0 : enumRing ω = ∗ω := by
  apply (of_le_enumRing _).antisymm'
  grw [← enumField_omega0, enumRing_le_enumField]

@[simp]
theorem enumGroup_omega0 : enumGroup ω = ∗ω := by
  apply (of_le_enumGroup _).antisymm'
  grw [← enumRing_omega0, enumGroup_le_enumRing]

@[simp]
theorem IsField.omega0 : IsField (∗ω) := by
  rw [← enumField_omega0]
  exact IsField.enumField _

@[simp]
theorem IsRing.omega0 : IsRing (∗ω) :=
  IsField.omega0.toIsRing

/-! ### Cardinality of closures -/

theorem card_fieldClosure {x : Nimber} (hx : ∗ω ≤ x) : (fieldClosure x).val.card = x.val.card := by
  have h1x : 1 < x := (of.lt_iff_lt.2 one_lt_omega0).trans_le hx
  apply (card_monotone (by simp)).antisymm'
  obtain ⟨l, hl, hlx, hxl⟩ := exists_isField_between' h1x
  obtain rfl | hlx := hlx.eq_or_lt
  · rw [hl.fieldClosure_eq]
  have hxl' : x.fieldClosure = (succ l).fieldClosure := by
    rw [← succ_le_iff] at hlx
    apply (fieldClosure_monotone hlx).antisymm'
    simpa using fieldClosure_monotone hxl.le
  rw [hxl', ← Cardinal.lift_le, ← cardinalMk_Iio, ← coe_toSubfield (IsField.fieldClosure _),
    ← IsField.fieldAdjoin_simple_self hl]
  apply (IntermediateField.cardinalMk_adjoin_le ..).trans
  apply max_le (max_le ((cardinalMk_Iio _).trans_le _) _) _
  · rw [Cardinal.lift_le]
    apply card_monotone
    simpa
  · simpa using h1x.le
  · simpa

theorem card_algClosure {x : Nimber} (hx : ∗ω ≤ x) : (algClosure x).val.card = x.val.card := by
  apply (card_monotone (by simp)).antisymm'
  rw [← Cardinal.lift_le, ← cardinalMk_Iio, ← Iio_def]
  simp_rw [lt_algClosure_iff_isAlgebraic]
  apply (Algebraic.cardinalMk_le_max ..).trans (max_le ..)
  · apply (cardinalMk_Iio _).trans_le
    rw [card_fieldClosure hx]
  · simpa

theorem card_ringClosure {x : Nimber} (hx : ∗ω ≤ x) : (ringClosure x).val.card = x.val.card := by
  apply (card_monotone (by simp)).antisymm'
  rw [← card_fieldClosure hx]
  exact card_monotone (by simp)

theorem card_groupClosure {x : Nimber} (hx : ∗ω ≤ x) : (groupClosure x).val.card = x.val.card := by
  apply (card_monotone (by simp)).antisymm'
  rw [← card_fieldClosure hx]
  exact card_monotone (by simp)

theorem card_algClosure_le (x : Nimber) : (algClosure x).val.card ≤ max ℵ₀ x.val.card := by
  obtain hx | hx := le_or_gt (∗ω) x
  · rw [card_algClosure hx]
    exact le_max_right ..
  · grw [hx, card_algClosure]
    · simp
    · rfl

theorem card_fieldClosure_le (x : Nimber) : (fieldClosure x).val.card ≤ max ℵ₀ x.val.card := by
  grw [fieldClosure_le_algClosure, card_algClosure_le]

theorem card_ringClosure_le (x : Nimber) : (ringClosure x).val.card ≤ max ℵ₀ x.val.card := by
  grw [ringClosure_le_fieldClosure, card_fieldClosure_le]

theorem card_groupClosure_le (x : Nimber) : (groupClosure x).val.card ≤ max ℵ₀ x.val.card := by
  grw [groupClosure_le_ringClosure, card_ringClosure_le]

theorem enumAlgClosed_omega {x : Ordinal} (hx₀ : x ≠ 0) : enumAlgClosed (ω_ x) = ∗ω_ x := by
  induction x using Ordinal.limitRecOn with
  | zero => contradiction
  | add_one x =>
    apply (of_le_enumAlgClosed _).antisymm'
    conv_lhs => rw [← ord_aleph, ← cof_omega_add_one, enumAlgClosed_def]
    refine Ordinal.enum_ord_cof_le isClub_ofPred_isAlgClosed (fun z hz ↦ ?_) (isSuccLimit_omega _)
    rw [← card_le_aleph_iff] at hz
    refine ⟨(algClosure (∗z)).val, IsAlgClosed.algClosure _, ⟨le_algClosure _, ?_⟩⟩
    grw [← card_le_aleph_iff, card_algClosure_le]
    simpa
  | limit x hx IH =>
    have := hx.nonempty_Iio.to_subtype
    apply (of_le_enumAlgClosed _).antisymm'
    conv_lhs => rw [isNormal_omega.apply_of_isSuccLimit hx]
    rw [isNormal_enumAlgClosed.map_iSup Ordinal.bddAbove_of_small]
    refine ciSup_le' fun ⟨y, hy⟩ ↦ ?_
    obtain rfl | hy₀ := eq_or_ne y 0
    · grw [Subtype.coe_mk, zero_le_one]
      simpa [IH 1 (one_lt_of_isSuccLimit hx), Order.one_le_iff_ne_zero]
    · rw [IH y hy hy₀]
      simpa using hy.le

@[simp]
theorem enumField_omega (x : Ordinal) : enumField (ω_ x) = ∗ω_ x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · apply (of_le_enumField _).antisymm'
    grw [← enumAlgClosed_omega hx, enumField_le_enumAlgClosed]

@[simp]
theorem enumRing_omega (x : Ordinal) : enumRing (ω_ x) = ∗ω_ x := by
  apply (of_le_enumRing _).antisymm'
  grw [← enumField_omega, enumRing_le_enumField]

@[simp]
theorem enumGroup_omega (x : Ordinal) : enumGroup (ω_ x) = ∗ω_ x := by
  apply (of_le_enumGroup _).antisymm'
  grw [← enumRing_omega, enumGroup_le_enumRing]

theorem IsAlgClosed.omega {x : Ordinal} (hx : x ≠ 0) : IsAlgClosed (∗ω_ x) := by
  rw [← enumAlgClosed_omega hx]
  exact IsAlgClosed.enumAlgClosed _

theorem IsField.omega (x : Ordinal) : IsField (∗ω_ x) := by
  rw [← enumField_omega x]
  exact IsField.enumField _

theorem IsRing.omega (x : Ordinal) : IsRing (∗ω_ x) :=
  (IsField.omega x).toIsRing

theorem IsGroup.omega (x : Ordinal) : IsGroup (∗ω_ x) :=
  (IsRing.omega x).toIsGroup

end Nimber
end
