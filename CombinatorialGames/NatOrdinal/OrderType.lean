/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.NatOrdinal.Pow
import Mathlib.Order.GameAdd

/-!
# Maximal order types of embeddings

This file is devoted to two theorems, which also serve as characterizations of the natural sum and
product. Let `α`, `β`, `γ` be well-orders.

- Given the existence of a monotone, surjective map `f : α ⊕ β → γ`, the order type of `γ` is at
  most the natural sum of the order types of `α` and `β`, and the inequality is strict.
- Given the existence of a monotone, surjective map `f : α × β → γ`, the order type of `γ` is at
  most the natural product of the order types of `α` and `β`, and the inequality is strict.

## Main statements

- `type_sum_embedding_le`: inequality for the sum case
- `exists_sum_embedding`: equality for the sum case

TODO: prove product case
-/

open Ordinal Order Set

universe u

public section

/-! ### For Mathlib -/

section Preorder

variable {α β : Type*}

theorem Sum.swap_surjective : Function.Surjective (α := α ⊕ β) Sum.swap :=
  Sum.swap_leftInverse.surjective

variable [Preorder α] [Preorder β]

theorem Monotone.rangeFactorization {f : α → β} (hf : Monotone f) :
    Monotone (rangeFactorization f) :=
  fun _ _ h ↦ hf h

-- #43598
theorem Sum.swap_monotone : Monotone (α := α ⊕ β) Sum.swap :=
  fun _ _ ↦ swap_le_swap_iff.2

theorem Equiv.emptySum_monotone [IsEmpty α] : Monotone (Equiv.emptySum α β) := by
  simp [Monotone]

theorem Equiv.sumEmpty_monotone [IsEmpty β] : Monotone (Equiv.sumEmpty α β) := by
  simp [Monotone]

end Preorder

section LinearOrder

variable {α β γ : Type*}
  [LinearOrder α] [LinearOrder β] [LinearOrder γ]
  [WellFoundedLT α] [WellFoundedLT β] [WellFoundedLT γ]

-- #43588
instance : WellFoundedLT (α ⊕ₗ β) :=
  have H : IsWellOrder _ (Sum.Lex (· < · : α → _) (· < · : β → _)) := inferInstance
  ⟨H.wf⟩

/-- An order isomorphism between `insert a s` and `s ⊕ₗ PUnit`. -/
def orderIsoInsert {s : Set α} [DecidablePred (· ∈ s)] {a : α} (ha : ∀ b ∈ s, b < a) :
    (insert a s :) ≃o s ⊕ₗ PUnit :=
  ⟨(Equiv.Set.insert fun h ↦ (ha a h).false).trans toLex, by
    simp only [Equiv.trans_apply, Subtype.forall, mem_insert_iff]
    rintro b (rfl | hb) c (rfl | hc)
    · simp
    · rw [Equiv.Set.insert_apply_right _ ⟨c, hc⟩]
      simpa using (ha c hc)
    · rw [Equiv.Set.insert_apply_right _ ⟨b, hb⟩]
      simpa using (ha b hb).le
    · rw [Equiv.Set.insert_apply_right _ ⟨b, hb⟩, Equiv.Set.insert_apply_right _ ⟨c, hc⟩]
      simp
  ⟩

namespace Ordinal

-- #43588
@[simp]
theorem type_lt_sum_lex {α β : Type u} [LinearOrder α] [LinearOrder β]
    [WellFoundedLT α] [WellFoundedLT β] : typeLT (α ⊕ₗ β) = typeLT α + typeLT β :=
  rfl

@[simp]
theorem type_univ {α : Type*} [LinearOrder α] [WellFoundedLT α] :
    typeLT (univ (α := α)) = typeLT α :=
  OrderIso.Set.univ.ordinalType_congr

theorem type_insert {s : Set α} {a : α} (ha : ∀ b ∈ s, b < a) :
    typeLT (insert a s :) = typeLT s + 1 := by
  classical exact (orderIsoInsert ha).ordinalType_congr

theorem type_set_lt {s : Set α} (hs : ∃ a, ∀ b ∈ s, b < a) : typeLT s < typeLT α := by
  obtain ⟨a, ha⟩ := hs
  rw [← add_one_le_iff, ← type_insert ha]
  exact type_set_le ..

theorem type_le_iff_forall {x : Ordinal} :
    typeLT α ≤ x ↔ ∀ a : α, typein (α := α) (· < ·) a < x where
  mp h a := (typein_lt_type ..).trans_le h
  mpr h := by
    by_contra! hx
    simpa using h (enum (· < ·) ⟨x, hx⟩)

/-- Well-orders of the same order type are isomorphic. -/
noncomputable def OrderIso.of_ordinalType_eq {α β : Type u} [LinearOrder α] [LinearOrder β]
    [WellFoundedLT α] [WellFoundedLT β] (H : typeLT α = typeLT β) : α ≃o β :=
  .ofRelIsoLT (type_eq.1 H).some

theorem exists_orderIso_sum {α : Type u} [LinearOrder α] [WellFoundedLT α]
    {x : Ordinal} (hx : x ≤ typeLT α) :
    ∃ (β : Type u) (_ : LinearOrder β) (_ : WellFoundedLT β)
      (γ : Type u) (_ : LinearOrder γ) (_ : WellFoundedLT γ)
      (_ : β ⊕ₗ γ ≃o α), typeLT β = x := by
  refine ⟨x.ToType, inferInstance, inferInstance,
    (typeLT α - x).ToType, inferInstance, inferInstance, .of_ordinalType_eq ?_, by simp⟩
  simpa using Ordinal.add_sub_cancel_of_le hx

end Ordinal
end LinearOrder

/-! ### Sum embeddings -/

namespace NatOrdinal

variable {α β γ : Type u}
  [LinearOrder α] [LinearOrder β] [LinearOrder γ]
  [WellFoundedLT α] [WellFoundedLT β] [WellFoundedLT γ]

theorem type_sum_embedding_le {f : α ⊕ β → γ} (hf : Monotone f) (hfs : f.Surjective) :
    NatOrdinal.of (typeLT γ) ≤ .of (typeLT α) + .of (typeLT β) := by
  induction hγ : typeLT γ using WellFoundedLT.induction generalizing α β γ with | ind c IH
  subst hγ
  rw [of_le_iff, type_le_iff_forall]
  intro c
  rw [← of_lt_iff]
  let g (x : (f ∘ Sum.inl) ⁻¹' Iio c ⊕ (f ∘ Sum.inr) ⁻¹' Iio c) : Iio c :=
    x.rec (fun y ↦ ⟨f (.inl y.1), y.2⟩) (fun y ↦ ⟨f (.inr y.1), y.2⟩)
  apply (IH (f := g) ..).trans_lt
  · obtain ⟨a | b, rfl⟩ := hfs c
    · apply add_lt_add_of_lt_of_le
      · rw [of.lt_iff_lt]
        refine type_set_lt ⟨a, fun b hb ↦ ?_⟩
        contrapose! hb
        simpa using hf (Sum.inl_mono hb)
      · rw [of.le_iff_le]
        exact type_set_le ..
    · apply add_lt_add_of_le_of_lt
      · rw [of.le_iff_le]
        exact type_set_le ..
      · rw [of.lt_iff_lt]
        refine type_set_lt ⟨b, fun a ha ↦ ?_⟩
        contrapose! ha
        simpa using hf (Sum.inr_mono ha)
  · exact typein_lt_type ..
  · rintro (a | a) (b | b) (hab | hab)
    · exact hf (Sum.inl_mono hab)
    · exact hf (Sum.inr_mono hab)
  · intro ⟨x, hx⟩
    obtain ⟨(a | b), rfl⟩ := hfs x
    · exact ⟨.inl ⟨a, hx⟩, rfl⟩
    · exact ⟨.inr ⟨b, hx⟩, rfl⟩
  · rfl

theorem type_sum_embedding_range_le {f : α ⊕ β → γ} (hf : Monotone f) :
    NatOrdinal.of (typeLT (range f)) ≤ .of (typeLT α) + .of (typeLT β) :=
  type_sum_embedding_le hf.rangeFactorization rangeFactorization_surjective

theorem type_union_le (s t : Set α) :
    NatOrdinal.of (typeLT (s ∪ t :)) ≤ .of (typeLT s) + .of (typeLT t) := by
  let f (x : s ⊕ t) : (s ∪ t :) :=
    x.rec (fun y ↦ ⟨y, subset_union_left y.2⟩) (fun y ↦ ⟨y, subset_union_right y.2⟩)
  apply type_sum_embedding_le (f := f) <;> intro <;> aesop

theorem le_type_add_of_codisjoint {s t : Set α} (h : Codisjoint s t) :
    NatOrdinal.of (typeLT α) ≤ .of (typeLT s) + .of (typeLT t) := by
  rw [← type_univ, ← top_eq_univ, ← codisjoint_iff.1 h]
  exact type_union_le s t

theorem exists_sum_embedding (α β : Type u) [LinearOrder α] [LinearOrder β]
    [WellFoundedLT α] [WellFoundedLT β] :
    ∃ (γ : Type u) (_ : LinearOrder γ) (_ : WellFoundedLT γ),
      .of (typeLT α) + .of (typeLT β) = NatOrdinal.of (typeLT γ) ∧
      ∃ f : α ⊕ β →o γ, Function.Surjective f := by
  induction H : NatOrdinal.of (typeLT α) + .of (typeLT β) using WellFoundedLT.induction
    generalizing α β with | ind s IH
  subst H
  -- `wlog` doesn't play well with `induction`, unfortunately.
  have H {α' β' : Type u} [LinearOrder α'] [LinearOrder β']
      [WellFoundedLT α'] [WellFoundedLT β']
      (H : NatOrdinal.of (typeLT α') + .of (typeLT β') = .of (typeLT α) + .of (typeLT β))
      (hle : typeLT β' ≤ typeLT α') :
      ∃ (γ : Type u) (_ : LinearOrder γ) (_ : WellFoundedLT γ),
        .of (typeLT α') + .of (typeLT β') = NatOrdinal.of (typeLT γ) ∧
        ∃ f : α' ⊕ β' →o γ, Function.Surjective f := by
    obtain hβ₀ | hβ₀ := eq_or_ne (typeLT β') 0
    · rw [type_eq_zero_iff_isEmpty] at hβ₀
      exact ⟨α', ‹_›, ‹_›, by simpa, ⟨_, Equiv.sumEmpty_monotone⟩, Equiv.surjective _⟩
    have hα₀ := (hβ₀.pos.trans_le hle).ne_zero
    obtain ⟨γ, _, _, δ, _, _, e, hγ⟩ := exists_orderIso_sum (opow_log_le_self ω hα₀)
    have hδ : typeLT δ < typeLT α' := by
      have := e.ordinalType_congr
      rw [type_lt_sum_lex, hγ] at this
      rw [← sub_eq_of_add_eq this]
      exact sub_omega0_opow_log_lt hα₀
    obtain ⟨ε, _, _, hε, ⟨f, hf⟩, hf'⟩ := IH _ (by simpa [← H]) δ β' rfl
    let g : α' ⊕ β' → γ ⊕ₗ ε := toLex ∘ Sum.map id (f ∘ ofLex) ∘ ofLex ∘
      OrderIso.sumLexAssoc γ δ β' ∘ toLex ∘ Sum.map e.symm id
    refine ⟨_, inferInstance, inferInstance, ?_, ⟨g, ?_⟩, ?_⟩
    · have hα' : of (typeLT α') < ω^ (of (log ω (typeLT α')) + 1) := by
        rw [of_lt_iff, val_wpow, val_add_one, val_of]
        exact lt_opow_succ_log_self one_lt_omega0 _
      have hδ' : of (typeLT δ) < ω^ (of (log ω (typeLT α')) + 1) := (of.strictMono hδ).trans hα'
      rwa [type_lt_sum_lex, hγ, ← val_of (log _ _), ← val_of (typeLT ε), ← wpow_add_of_lt,
        ← hε, ← add_assoc, add_left_inj, wpow_add_of_lt, val_of, val_of, ← hγ,
        ← e.ordinalType_congr, type_lt_sum_lex]
      · rw [← hε]
        exact add_lt_wpow hδ' ((of.monotone hle).trans_lt hα')
    · rintro (x | x) (y | y) (hxy | hxy)
      · unfold g
        revert x y
        simp_rw [e.symm.forall_congr_left]
        simpa using fun x y hxy ↦ hf (Sum.inl_mono hxy)
      · simpa [g] using hf (Sum.inr_mono hxy)
    · apply toLex.surjective.comp <| Function.Surjective.comp _
        (ofLex.surjective.comp <| (Equiv.surjective _).comp <| toLex.surjective.comp _) <;>
        rw [Sum.map_surjective]
      · exact ⟨Function.surjective_id, hf'⟩
      · exact ⟨e.symm.surjective, Function.surjective_id⟩
  obtain hle | hle := le_total (typeLT α) (typeLT β)
  · obtain ⟨γ, _, _, hγ, ⟨f, hf⟩, hf'⟩ := H (add_comm ..) hle
    rw [add_comm] at hγ
    exact ⟨γ, ‹_›, ‹_›, hγ, ⟨_, hf.comp Sum.swap_monotone⟩, hf'.comp Sum.swap_surjective⟩
  · exact H rfl hle

/-! ### Product embeddings -/

theorem type_prod_embedding_le {α β γ : Type u} [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    [WellFoundedLT α] [WellFoundedLT β] [WellFoundedLT γ]
    {f : α × β → γ} (hf : Monotone f) (hfs : f.Surjective) :
    NatOrdinal.of (typeLT γ) ≤ .of (typeLT α) * .of (typeLT β) := by
  obtain hα₀ | hα₀ := eq_or_ne (typeLT α) 0
  · rw [type_eq_zero_iff_isEmpty] at hα₀
    have := hfs.isEmpty
    simp [type_eq_zero_of_empty]
  obtain hβ₀ | hβ₀ := eq_or_ne (typeLT β) 0
  · rw [type_eq_zero_iff_isEmpty] at hβ₀
    have := hfs.isEmpty
    simp [type_eq_zero_of_empty]
  have hα := opow_log_le_self ω hα₀
  have hβ := opow_log_le_self ω hβ₀
  obtain ⟨β₁, _, _, β₂, _, _, eβ, hβ₁⟩ := exists_orderIso_sum hβ
  obtain ⟨α₁, _, _, α₂, _, _, eα, hα₁⟩ := exists_orderIso_sum hα
  have heα : typeLT α = typeLT α₁ + typeLT α₂ := eα.ordinalType_congr.symm
  have heβ : typeLT β = typeLT β₁ + typeLT β₂ := eβ.ordinalType_congr.symm
  obtain hα | hα := (hα₁ ▸ hα).lt_or_eq
  · have : typeLT α₂ < typeLT α := by
      rw [hα₁] at heα
      rw [← Ordinal.sub_eq_of_add_eq heα.symm]
      exact sub_omega0_opow_log_lt hα₀
    rw [heα, hα₁, ← val_of (log _ _), ← val_of (typeLT α₂), ← wpow_add_of_lt, add_mul,
      ← of_omega0_opow, ← hα₁]
    · let e : α₁ × β ⊕ α₂ × β ≃ α × β :=
        (Equiv.sumProdDistrib α₁ α₂ β).symm.trans (Equiv.prodCongr (toLex.trans eα) (.refl _))
      have he : Monotone e := by rintro (x | x) (y | y) (hxy | hxy) <;> simpa [e]
      apply (le_type_add_of_codisjoint
        (s := (f ∘ e) '' range Sum.inl) (t := (f ∘ e) '' range Sum.inr) _).trans
      · apply add_le_add
        all_goals
          rw [← range_comp, Function.comp_assoc]
          apply type_prod_embedding_le _ rangeFactorization_surjective
          apply (hf.comp (he.comp _)).rangeFactorization
        · exact Sum.inl_mono
        · exact Sum.inr_mono
      · rw [codisjoint_iff]
        dsimp
        rw [← image_union, range_inl_union_range_inr, image_univ]
        simpa using hfs.range_eq
    · rw [of_lt_iff, val_wpow, val_add_one, val_of]
      apply (lt_opow_succ_log_self one_lt_omega0 _).trans_le'
      rw [heα]
      exact self_le_add_left ..
  obtain hβ | hβ := (hβ₁ ▸ hβ).lt_or_eq
  · have : typeLT β₂ < typeLT β := by
      rw [hβ₁] at heβ
      rw [← Ordinal.sub_eq_of_add_eq heβ.symm]
      exact sub_omega0_opow_log_lt hβ₀
    rw [heβ, hβ₁, ← val_of (log _ _), ← val_of (typeLT β₂), ← wpow_add_of_lt, mul_add,
      ← of_omega0_opow, ← hβ₁]
    · let e : α × β₁ ⊕ α × β₂ ≃ α × β :=
        (Equiv.prodSumDistrib α β₁ β₂).symm.trans (Equiv.prodCongr (.refl _) (toLex.trans eβ))
      have he : Monotone e := by rintro (x | x) (y | y) (hxy | hxy) <;> simpa [e]
      apply (le_type_add_of_codisjoint
        (s := (f ∘ e) '' range Sum.inl) (t := (f ∘ e) '' range Sum.inr) _).trans
      · apply add_le_add
        all_goals
          rw [← range_comp, Function.comp_assoc]
          apply type_prod_embedding_le _ rangeFactorization_surjective
          apply (hf.comp (he.comp _)).rangeFactorization
        · exact Sum.inl_mono
        · exact Sum.inr_mono
      · rw [codisjoint_iff]
        dsimp
        rw [← image_union, range_inl_union_range_inr, image_univ]
        simpa using hfs.range_eq
    · rw [of_lt_iff, val_wpow, val_add_one, val_of]
      apply (lt_opow_succ_log_self one_lt_omega0 _).trans_le'
      rw [heβ]
      exact self_le_add_left ..
  rw [of_le_iff, type_le_iff_forall]
  intro c
  obtain ⟨⟨a, b⟩, rfl⟩ := hfs c
  rw [← type_Iio_lt]
  let gα : Iio a × β → γ := f ∘ Prod.map Subtype.val id
  let gβ : α × Iio b → γ := f ∘ Prod.map id Subtype.val
  apply (type_mono (t := range gα ∪ range gβ) _).trans_lt
  · rw [← of_lt_iff]
    apply (type_union_le _ _).trans_lt
    rw [← hα, ← hβ, hα₁, hβ₁, of_omega0_opow, of_omega0_opow, ← wpow_add]
    apply add_lt_wpow
    · have : typeLT (Iio a) < typeLT α := typein_lt_type (· < ·) a
      rw [wpow_add]
      apply (type_prod_embedding_le (f := rangeFactorization gα) ..).trans_lt
      · apply mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
        · rwa [of_lt_iff, val_wpow, val_of, ← hα₁, hα]
        · rw [of_le_iff, val_wpow, val_of, ← hβ₁, hβ]
        · exact zero_le
        · exact wpow_pos _
      · exact (hf.comp (Monotone.prodMap (Subtype.mono_coe _) monotone_id)).rangeFactorization
      · exact rangeFactorization_surjective
    · have : typeLT (Iio b) < typeLT β := typein_lt_type (· < ·) b
      rw [wpow_add]
      apply (type_prod_embedding_le (f := rangeFactorization gβ) ..).trans_lt
      · apply mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
        · rw [of_le_iff, val_wpow, val_of, ← hα₁, hα]
        · rwa [of_lt_iff, val_wpow, val_of, ← hβ₁, hβ]
        · exact zero_le
        · exact wpow_pos _
      · exact (hf.comp (Monotone.prodMap monotone_id (Subtype.mono_coe _))).rangeFactorization
      · exact rangeFactorization_surjective
  · intro x hx
    obtain ⟨⟨c, d⟩, rfl⟩ := hfs x
    obtain hca | hac := lt_or_ge c a
    · exact .inl ⟨⟨⟨c, hca⟩, d⟩, rfl⟩
    obtain hda | had := lt_or_ge d b
    · exact .inr ⟨⟨c, ⟨d, hda⟩⟩, rfl⟩
    · cases hx.not_ge (hf ⟨hac, had⟩)
termination_by (typeLT α, typeLT β)

end NatOrdinal
end
