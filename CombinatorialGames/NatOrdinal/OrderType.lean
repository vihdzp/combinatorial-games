/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.NatOrdinal.Basic

/-!
# Maximal order types of embeddings
-/

open Ordinal Order Set

universe u

public section

variable {α β γ : Type u}
  [LinearOrder α] [LinearOrder β] [LinearOrder γ]
  [WellFoundedLT α] [WellFoundedLT β] [WellFoundedLT γ]

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

end Ordinal

namespace NatOrdinal

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

end NatOrdinal
end
