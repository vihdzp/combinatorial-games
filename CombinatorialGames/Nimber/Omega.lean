module

public import CombinatorialGames.Nimber.SimplestExtension.Algebraic

/-!
-/

public section

universe u v

open Order Ordinal Set Notation

/-! ### For Mathlib -/

set_option backward.isDefEq.respectTransparency.types false in
def OrderIso.restrictIio {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β) (x : α) :
    Iio x ≤i β where
  toFun x := e x
  inj' _ := by simp [Subtype.coe_inj]
  map_rel_iff' := by simp
  mem_range_of_rel' y z h := by
    refine ⟨⟨e.symm z, ?_⟩, ?_⟩
    · apply y.2.trans'
      simpa [e.symm_apply_lt]
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

theorem Ordinal.enum_lt_of_lt_cof_ord {s : Set Ordinal} (hs : IsCofinal s) {x y : Ordinal}
    (hx : ∀ a < x, ∃ b ∈ s, b ∈ Ico a x) (hy : y < x.cof.ord) : Order.enum s hs y < x := by
  let f : Iio x.cof.ord ≤i Iio x ↓∩ s := by
    apply (Ordinal.type_le_iff.1 _).some
    rw [type_lt_Iio, Cardinal.lift_ord, lift_cof, Cardinal.ord_le, card_type, ← cof_Iio]
    refine cof_le fun ⟨a, ha⟩ ↦ ?_
    obtain ⟨b, hb, ⟨hab, hbx⟩⟩ := hx a ha
    exact ⟨⟨b, hbx⟩, hb, hab⟩
  let g (a : Iio x.cof.ord) : s := ⟨f a, (f a).2⟩
  have hg : StrictMono g := fun _ ↦ by simp [g]
  exact (Subtype.coe_le_coe.2 <| enum_le_of_strictMono hs hg hy).trans_lt (f _).1.2

@[simp]
theorem Ordinal.one_le_lift {x : Ordinal.{u}} : 1 ≤ Ordinal.lift.{v} x ↔ 1 ≤ x := by
  simpa using Ordinal.lift_le (a := 1)

@[simp]
theorem Ordinal.omega0_le_lift {x : Ordinal.{u}} : ω ≤ Ordinal.lift.{v} x ↔ ω ≤ x := by
  simpa using Ordinal.lift_le (a := ω)

namespace Nimber

/-! ### Uncountable initial ordinals are algebraically closed -/

theorem card_fieldClosure {x : Nimber.{u}} (hx : ∗ω ≤ x) :
    (fieldClosure x).val.card = x.val.card := by
  have h1x : 1 < x := (of.lt_iff_lt.2 one_lt_omega0).trans_le hx
  apply (card_monotone (by simp)).antisymm'
  obtain ⟨l, hl, hlx, hxl⟩ := exists_isField_between' h1x
  obtain rfl | hlx := hlx.eq_or_lt
  · rw [hl.fieldClosure_eq]
  have hxl' : x.fieldClosure = (succ l).fieldClosure := by
    rw [← succ_le_iff] at hlx
    apply (fieldClosure_mono hlx).antisymm'
    simpa using fieldClosure_mono hxl.le
  rw [hxl', ← Cardinal.lift_le.{u + 1}, ← cardinalMk_Iio, ← coe_toSubfield (IsField.fieldClosure _),
    ← IsField.fieldAdjoin_simple_self hl]
  apply (IntermediateField.cardinalMk_adjoin_le ..).trans
  rw [max_le_iff, max_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply (cardinalMk_Iio _).trans_le
    rw [Cardinal.lift_le]
    apply card_monotone
    simpa
  · simpa using h1x.le
  · simpa

theorem card_algClosure {x : Nimber} (hx : ∗ω ≤ x) : (algClosure x).val.card = x.val.card := by
  sorry

theorem card_ringClosure {x : Nimber} (hx : ∗ω ≤ x) : (ringClosure x).val.card = x.val.card := by
  apply (card_monotone (by simp)).antisymm'
  rw [← card_fieldClosure hx]
  exact card_monotone (by simp)

theorem card_groupClosure {x : Nimber} (hx : ∗ω ≤ x) : (groupClosure x).val.card = x.val.card := by
  apply (card_monotone (by simp)).antisymm'
  rw [← card_fieldClosure hx]
  exact card_monotone (by simp)

theorem enumAlgClosed_omega {x : Ordinal} (hx₀ : x ≠ 0) : enumAlgClosed (ω_ x) = ∗ω_ x := by
  induction x using SuccOrder.limitRecOn with
  | isMin => simp_all
  | succ x =>
    apply (of_le_enumAlgClosed _).antisymm'
    rw [isNormal_enumAlgClosed.le_iff_forall_le (Cardinal.isSuccLimit_omega _)]
    intro y hy
    rw [enumAlgClosed_def', of.le_iff_le]
    apply (Ordinal.enum_lt_of_lt_cof_ord ..).le
    · sorry
    · simpa
  | isSuccLimit x hx IH =>
    have := hx.nonempty_Iio.to_subtype
    apply (of_le_enumAlgClosed _).antisymm'
    conv_lhs => rw [isNormal_omega.apply_of_isSuccLimit hx]
    rw [isNormal_enumAlgClosed.map_iSup Ordinal.bddAbove_of_small]
    apply ciSup_le'
    intro ⟨y, hy⟩
    obtain rfl | hy₀ := eq_or_ne y 0
    · trans enumAlgClosed (ω_ 1)
      · exact (omega.comp enumAlgClosed).monotone zero_le_one
      · rw [IH 1 (one_lt_of_isSuccLimit hx) one_ne_zero]
        simpa [Order.one_le_iff_ne_zero]
    · rw [IH y hy hy₀]
      simpa using hy.le


#exit

end Nimber
end
