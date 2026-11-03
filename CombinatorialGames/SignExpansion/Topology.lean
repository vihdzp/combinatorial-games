/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.NatOrdinal.Topology
public import CombinatorialGames.SignExpansion.Simplicity
public import Mathlib.Order.Comparable
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Topology.Separation.CompletelyRegular

import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Separation.Connected

/-!
# Topology on sign expansions

We endow sign expansions with the Scott-Hausdorff topology, i.e. the topology where closed sets are
closed under directed suprema. This is the topology defined in Surreal Substructures by Vincent
Bagayoko and Joris van der Hoeven.
-/

public section

namespace Simplicity
open Order Set SignExpansion Topology

instance : TopologicalSpace Simplicity :=
  Topology.scottHausdorff _ .univ

instance : Topology.IsScottHausdorff Simplicity .univ :=
  ⟨rfl⟩

theorem isOpen_iff_dirSupInacc {s : Set Simplicity} : IsOpen s ↔ DirSupInacc s :=
  Topology.IsScottHausdorff.isOpen_iff_dirSupInacc

theorem isClosed_iff_dirSupClosed {s : Set Simplicity} : IsClosed s ↔ DirSupClosed s :=
  Topology.IsScottHausdorff.isClosed_iff_dirSupClosed

theorem isClosed_iff_sSup {s : Set Simplicity} :
    IsClosed s ↔ ∀ t ⊆ s, t.Nonempty → BddAbove t → sSup t ∈ s := by
  rw [isClosed_iff_dirSupClosed]
  refine ⟨fun hs t ht ht₀ ht₁ ↦ ?_, fun hs t ht ht₀ ht₁ x hx ↦ ?_⟩
  · exact hs ht ht₀ (directedOn_iff_bddAbove.2 ht₁) (isLUB_sSup_of_bddAbove ht₁)
  · rw [hx.unique (isLUB_sSup_of_bddAbove hx.bddAbove)]
    exact hs t ht ht₀ hx.bddAbove

-- #45605
theorem dirSupClosed_closure (s : Set Simplicity) : DirSupClosed (closure s) := by
  rw [← isClosed_iff_dirSupClosed]
  exact isClosed_closure

theorem closure_eq_setOfPred_isLUB (s : Set Simplicity) :
    closure s = {x | ∃ d ⊆ s, d.Nonempty ∧ IsLUB d x} := by
  apply subset_antisymm
  · rw [IsClosed.closure_subset_iff]
    · exact fun x hx ↦ ⟨{x}, singleton_subset_iff.2 hx, singleton_nonempty x, isLUB_singleton⟩
    · rw [isClosed_iff_dirSupClosed]
      intro d hd hd₀ hd₁ x hx
      choose f hfs hf₀ hf using hd
      refine ⟨⋃ y : d, f y.2, ?_, ?_, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
      · simpa
      · aesop
      · obtain ⟨⟨i, hi⟩, hz⟩ := mem_iUnion.1 hy
        exact ((hf hi).1 hz).trans (hx.1 hi)
      · exact hx.2 fun z hz ↦ (hf hz).2 (upperBounds_mono_set (subset_iUnion _ ⟨z, hz⟩) hy)
  · rintro x ⟨d, hd, hd₀, hx⟩
    -- mem_closure_of_isLUB
    exact dirSupClosed_closure _ (hd.trans subset_closure) hd₀
      (directedOn_iff_bddAbove.2 hx.bddAbove) hx

theorem mem_closure_iff_isLUB {s : Set Simplicity} {x : Simplicity} :
    x ∈ closure s ↔ ∃ d ⊆ s, d.Nonempty ∧ IsLUB d x :=
  Set.ext_iff.1 (closure_eq_setOfPred_isLUB s) x

-- #45605
theorem mem_closure_of_isLUB {d s : Set Simplicity} (hd : d ⊆ s) (hd₀ : d.Nonempty)
    {x : Simplicity} (hx : IsLUB d x) : x ∈ closure s :=
  mem_closure_iff_isLUB.2 ⟨d, hd, hd₀, hx⟩

theorem closure_eq_setOfPred_sSup (s : Set Simplicity) :
    closure s = {x | ∃ d ⊆ s, d.Nonempty ∧ BddAbove d ∧ sSup d = x} := by
  rw [closure_eq_setOfPred_isLUB]
  ext x
  constructor
  · rintro ⟨d, hd, hd₀, hx⟩
    exact ⟨d, hd, hd₀, hx.bddAbove, hx.sSup_eq⟩
  · rintro ⟨d, hd, hd₀, hd₁, rfl⟩
    exact ⟨d, hd, hd₀, isLUB_sSup_of_bddAbove hd₁⟩

theorem mem_closure_iff_sSup {s : Set Simplicity} {x : Simplicity} :
    x ∈ closure s ↔ ∃ d ⊆ s, d.Nonempty ∧ BddAbove d ∧ sSup d = x :=
  Set.ext_iff.1 (closure_eq_setOfPred_sSup s) x

theorem sSup_mem_closure {d s : Set Simplicity} (hd : d ⊆ s) (hd₀ : d.Nonempty) (hd₁ : BddAbove d) :
    sSup d ∈ closure s :=
  mem_closure_iff_sSup.2 ⟨d, hd, hd₀, hd₁, rfl⟩

-- #43536
theorem isClopen_Iic (x : Simplicity) : IsClopen (Iic x) := by
  constructor
  · rw [isClosed_iff_sSup]
    intro t ht ht₀ ht₁
    simpa using sSup_mono ht bddAbove_Iic
  · rw [← isClosed_compl_iff, isClosed_iff_sSup]
    intro t ht ht₀ ht₁ hx
    obtain ⟨y, hy⟩ := ht₀
    exact ht hy <| (Simplicity.le_sSup hy ht₁).trans hx

-- #43536
theorem isClopen_Ioc (x y : Simplicity) : IsClopen (Ioc x y) := by
  by_cases h : x < y
  · rw [← Iic_sdiff_Iic h.le]
    exact (isClopen_Iic y).diff (isClopen_Iic x)
  · rw [Ioc_eq_empty h]
    exact isClopen_empty

-- #43536
theorem isClopen_Ioi (x : Simplicity) : IsClopen (Ioi x) := by
  constructor
  · rw [isClosed_iff_sSup]
    intro t ht ht₀ ht₁
    obtain ⟨y, hy⟩ := ht₀
    exact (ht hy).trans_le (Simplicity.le_sSup hy ht₁)
  · have : Ioi x = ⋃ y : Ioi x, Ioc x y := by aesop
    rw [this]
    exact isOpen_iUnion fun i ↦ (isClopen_Ioc ..).isOpen

theorem isClosed_of_pairwise_incompRel {s : Set Simplicity} (hs : s.Pairwise (IncompRel (· ≤ ·))) :
    IsClosed s := by
  rw [isClosed_iff_sSup]
  intro t ht ⟨x, hx⟩ ht₁
  rw [← isChain_iff_bddAbove] at ht₁
  have ht' : t.Subsingleton := by
    intro x hx y hy
    by_contra h
    exact not_symmGen_iff.2 (hs (ht hx) (ht hy) h) (ht₁.total hx hy)
  obtain rfl := ht'.eq_singleton_of_mem hx
  simpa using ht

-- generalize to Scott-Hausdorff
theorem isClopen_singleton_of_not_isSuccLimit {x : Simplicity} (hx : ¬ IsSuccLimit x) :
    IsClopen {x} := by
  rw [not_isSuccLimit_iff, not_isSuccPrelimit_iff] at hx
  obtain hx | ⟨y, hx⟩ := hx
  · rw [← hx.Iic_eq]
    exact isClopen_Iic x
  · rw [← hx.Ioc_eq]
    exact isClopen_Ioc y x

-- generalize to Scott-Hausdorff
@[simp]
theorem isClopen_singleton_bot : IsClopen {(⊥ : Simplicity)} :=
  isClopen_singleton_of_not_isSuccLimit not_isSuccLimit_bot

theorem nhds_eq_pure_of_not_isSuccLimit {x : Simplicity} (hx : ¬ IsSuccLimit x) : 𝓝 x = pure x := by
  rw [← isOpen_singleton_iff_nhds_eq_pure]
  exact (isClopen_singleton_of_not_isSuccLimit hx).isOpen

@[simp]
theorem nhds_bot : 𝓝 (⊥ : Simplicity) = pure ⊥ :=
  nhds_eq_pure_of_not_isSuccLimit not_isSuccLimit_bot

theorem hasBasis_nhds_Ioc {x : Simplicity} (hx₀ : x ≠ ⊥) : (𝓝 x).HasBasis (· < x) (Ioc · x) where
  mem_iff' s := by
    simp_rw [mem_nhds_iff]
    constructor
    · rintro ⟨t, hts, ht, hx⟩
      by_cases hx' : IsSuccLimit x
      · suffices ∃ i < x, Ico i x ⊆ t by
          obtain ⟨i, hi, hi'⟩ := this
          refine ⟨i, hi, hts.trans' ?_⟩
          rw [← Ioo_insert_right hi]
          exact insert_subset hx (Ioo_subset_Ico_self.trans hi')
        rw [Topology.IsScottHausdorff.isOpen_iff (D := univ)] at ht
        specialize ht (mem_univ (Iio x))
        simp_rw [Ici_inter_Iio] at ht
        apply ht
        · simpa
        · rw [directedOn_iff_bddAbove]
          exact bddAbove_Iio
        · exact (isLUB_sSup_of_bddAbove bddAbove_Iio)
        · rwa [sSup_Iio_of_isSuccLimit hx']
      · simp_rw [not_isSuccLimit_iff, isMin_iff_eq_bot, hx₀, false_or,
          not_isSuccPrelimit_iff] at hx'
        obtain ⟨y, hy⟩ := hx'
        use y, hy.lt
        rw [hy.Ioc_eq, singleton_subset_iff]
        exact hts hx
    · rintro ⟨y, hy, hs⟩
      exact ⟨_, hs, (isClopen_Ioc y x).isOpen, ⟨hy, le_rfl⟩⟩

instance : ZeroDimensionalSpace Simplicity := by
  rw [zeroDimensionalSpace_iff_isTopologicalBasis_isClopen]
  refine .of_hasBasis_nhds fun x ↦ ?_
  obtain rfl | hx := eq_or_ne x ⊥
  · rw [nhds_bot]
    apply (Filter.hasBasis_pure _).to_hasBasis'
    · refine fun _ _ ↦ ⟨{⊥}, ?_⟩
      simp
    · simp
  · apply (hasBasis_nhds_Ioc hx).to_hasBasis'
    · refine fun y hy ↦ ⟨_, ⟨isClopen_Ioc y x, ?_⟩, subset_rfl⟩
      simpa
    · exact fun s hs ↦ hs.1.isOpen.mem_nhds hs.2

-- This follows from #43536 + #45602.
instance : TotallySeparatedSpace Simplicity := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y _
  by_cases x ≤ y
  · refine ⟨_, (isClopen_Iic x), ?_⟩
    grind
  · refine ⟨_, (isClopen_Iic y).compl, ?_⟩
    simpa

-- #43536
theorem isOpen_Iio (x : Simplicity) : IsOpen (Iio x) := by
  rw [← Iic_sdiff_right]
  exact (isClopen_Iic x).isOpen.inter isOpen_compl_singleton

-- #43536
theorem isClosed_Icc (x y : Simplicity) : IsClosed (Icc x y) := by
  by_cases h : x ≤ y
  · rw [← Ioc_insert_left h]
    simpa using (isClopen_Ioc x y).isClosed.union (isClosed_singleton (x := x))
  · rw [Icc_eq_empty h]
    exact isClosed_empty

-- #43536
theorem isClosed_Ici (x : Simplicity) : IsClosed (Ici x) := by
  rw [← Ioi_insert]
  simpa using (isClopen_Ioi x).isClosed.union (isClosed_singleton (x := x))

instance : T35Space Simplicity where

section LinearOrder
variable {α} [LinearOrder α] [TopologicalSpace α]

-- #45612
instance [WellFoundedLT α] [OrderTopology α] : IsScottHausdorff α univ :=
  sorry

-- #45605
theorem Topology.IsScottHausdorff.mem_closure_iff_isLUB [IsScottHausdorff α univ]
    {s : Set α} {x : α} : x ∈ closure s ↔ ∃ d ⊆ s, d.Nonempty ∧ IsLUB d x :=
  sorry

end LinearOrder

theorem continuous_of_leftOrdContinuous {f : Simplicity → Simplicity} (hf : LeftOrdContinuous f) :
    Continuous f := by
  rw [continuous_iff_image_closure_subset_closure_image]
  rintro s _ ⟨y, hy, rfl⟩
  obtain ⟨d, hd, hd₀, hx⟩ := mem_closure_iff_isLUB.1 hy
  exact mem_closure_of_isLUB (image_mono hd) (hd₀.image _) (hf hd₀ hx)

theorem continuous_of_leftOrdContinuous' {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [IsScottHausdorff α univ] {f : α → Simplicity} (hf : LeftOrdContinuous f) :
    Continuous f := by
  rw [continuous_iff_image_closure_subset_closure_image]
  rintro s _ ⟨y, hy, rfl⟩
  obtain ⟨d, hd, hd₀, hx⟩ := Topology.IsScottHausdorff.mem_closure_iff_isLUB.1 hy
  exact mem_closure_of_isLUB (image_mono hd) (hd₀.image _) (hf hd₀ hx)

theorem continuous_restrict (x : SignExpansion) : Continuous (of ∘ restrict x) :=
  continuous_of_leftOrdContinuous' (leftOrdContinuous_restrict x)

end Simplicity
end
