import CombinatorialGames.NatOrdinal

universe u
open Set NatOrdinal WithTop

instance {α : Type*} [PartialOrder α] [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α]
    [∀ a : α, Decidable (Order.succ a = a)] : SuccAddOrder (WithTop α) where
  succ_eq_add_one := by
    rintro (x | x)
    · rfl
    · apply succ_coe.trans
      rw [Order.succ_eq_add_one]
      rfl

theorem WithTop.coe_add_one {α} [Add α] [One α] (x : α) : WithTop.some (x + 1) = x + 1 := by
  simp

theorem small_of_image {α β} {f : α → β} {s : Set α} (hf : InjOn f s)
    [Small.{u} (f '' s)] : Small.{u} s :=
  small_of_injective hf.imageFactorization_injective

theorem small_image_iff {α β} {f : α → β} {s : Set α} (hf : InjOn f s) :
    Small.{u} (f '' s) ↔ Small.{u} s :=
  ⟨fun _ ↦ small_of_image hf, fun _ ↦ small_image ..⟩

-- TODO: PR these into Mathlib as lemmas on `Ordinal`.

namespace NatOrdinal

theorem withTop_iSup_coe_lt {ι} [Small.{u} ι] (f : ι → NatOrdinal.{u}) :
    ⨆ i, WithTop.some (f i) < ⊤ := by
  simp_rw [← coe_iSup _ (bddAbove_of_small _), coe_lt_top]

theorem withTop_sSup_coe_lt (s : Set NatOrdinal.{u}) [Small.{u} s] :
    sSup (WithTop.some '' s) < ⊤ := by
  simp_rw [← coe_sSup' (bddAbove_of_small _), coe_lt_top]

theorem withTop_iSup_lt_top_iff_of_forall_lt {ι} {f : ι → WithTop NatOrdinal.{u}}
    (h : ∀ i, f i < ⊤) : ⨆ i, f i < ⊤ ↔ Small.{u} (range f) := by
  simp_rw [lt_top_iff_ne_top, ne_top_iff_exists] at h
  choose g hg using h
  obtain rfl := funext hg
  refine ⟨fun h ↦ ?_, fun hg' ↦ ?_⟩
  · rw [lt_top_iff_ne_top, ne_top_iff_exists] at h
    obtain ⟨a, ha⟩ := h
    rw [range_comp']
    refine @small_image _ _ _ _ (bddAbove_iff_small.1 ⟨a, ?_⟩)
    rintro _ ⟨i, rfl⟩
    rw [← coe_le_coe, ha]
    apply _root_.le_iSup _ i
  · rw [range_comp'] at hg'
    rw [iSup, range_comp']
    have : Small.{u} (range g) := small_of_image coe_injective.injOn
    exact withTop_sSup_coe_lt _

theorem withTop_sSup_lt_top_iff_of_forall_lt {s : Set (WithTop NatOrdinal.{u})}
    (h : ∀ x ∈ s, x < ⊤) : sSup s < ⊤ ↔ Small.{u} s := by
  rw [sSup_eq_iSup', withTop_iSup_lt_top_iff_of_forall_lt] <;> simp_all

@[simp]
theorem withTop_iSup_lt_top {ι} [Small.{u} ι] {f : ι → WithTop NatOrdinal.{u}} :
    ⨆ i, f i < ⊤ ↔ ∀ i, f i < ⊤ := by
  use fun hf i ↦ (_root_.le_iSup f i).trans_lt hf
  refine fun h ↦ (withTop_iSup_lt_top_iff_of_forall_lt h).2 ?_
  infer_instance

@[simp]
theorem withTop_sSup_lt_top {s : Set (WithTop NatOrdinal.{u})} [Small.{u} s] :
    sSup s < ⊤ ↔ ∀ x ∈ s, x < ⊤ := by
  rw [sSup_eq_iSup', withTop_iSup_lt_top, Subtype.forall]

end NatOrdinal
