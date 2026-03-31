/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.SignExpansion.Simplicity
public import Mathlib.Order.Comparable
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Topology.Separation.CompletelyRegular

import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Separation.Connected

/-!
# Topology on sign expansions

We give sign expansions the Scott-Hausdorff topology.
-/

private theorem CompletelyRegularSpace.of_isTopologicalBasis_clopens {X} [TopologicalSpace X]
    (h : TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s}) :
    CompletelyRegularSpace X where
  completely_regular x K hK hx := by
    obtain ⟨s, hs, hx, hsK⟩ := h.exists_subset_of_mem_open hx hK.isOpen_compl
    refine ⟨(sᶜ).indicator 1, ?_, ?_, fun x hx ↦ Set.indicator_of_mem ?_ _⟩
    · exact hs.compl.continuous_indicator continuous_const
    · simpa
    · exact fun hs ↦ hsK hs hx

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
  refine ⟨fun hs t ht ht₀ ht₁ ↦ ?_, fun hs t ht₀ ht₁ x hx ht ↦ ?_⟩
  · exact hs ht₀ (directedOn_iff_bddAbove.2 ht₁) (isLUB_sSup_of_bddAbove ht₁) ht
  · rw [hx.unique (isLUB_sSup_of_bddAbove hx.bddAbove)]
    exact hs t ht ht₀ hx.bddAbove

theorem isClopen_Iic (x : Simplicity) : IsClopen (Iic x) := by
  constructor
  · rw [isClosed_iff_sSup]
    intro t ht ht₀ ht₁
    simpa using sSup_mono ht bddAbove_Iic
  · rw [← isClosed_compl_iff, isClosed_iff_sSup]
    intro t ht ht₀ ht₁ hx
    obtain ⟨y, hy⟩ := ht₀
    exact ht hy <| (Simplicity.le_sSup hy ht₁).trans hx

theorem isClopen_Ioc (x y : Simplicity) : IsClopen (Ioc x y) := by
  by_cases h : x < y
  · rw [← Iic_diff_Iic h.le]
    exact (isClopen_Iic y).diff (isClopen_Iic x)
  · rw [Ioc_eq_empty h]
    exact isClopen_empty

theorem isClopen_Ioi (x : Simplicity) : IsClopen (Ioi x) := by
  constructor
  · rw [isClosed_iff_sSup]
    intro t ht ht₀ ht₁
    obtain ⟨y, hy⟩ := ht₀
    exact (ht hy).trans_le (Simplicity.le_sSup hy ht₁)
  · have : Ioi x = ⋃ y : Ioi x, Ioc x y := by aesop
    rw [this]
    exact isOpen_iUnion fun i ↦ (isClopen_Ioc ..).isOpen

instance : TotallySeparatedSpace Simplicity := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y _
  by_cases x ≤ y
  · refine ⟨_, (isClopen_Iic x), ?_⟩
    grind
  · refine ⟨_, (isClopen_Iic y).compl, ?_⟩
    simpa

theorem isOpen_Iio (x : Simplicity) : IsOpen (Iio x) := by
  rw [← Iic_diff_right]
  exact (isClopen_Iic x).isOpen.inter isOpen_compl_singleton

theorem isClosed_Icc (x y : Simplicity) : IsClosed (Icc x y) := by
  by_cases h : x ≤ y
  · rw [← Ioc_insert_left h]
    simpa using (isClopen_Ioc x y).isClosed.union (isClosed_singleton (x := x))
  · rw [Icc_eq_empty h]
    exact isClosed_empty

theorem isClosed_Ici (x : Simplicity) : IsClosed (Ici x) := by
  rw [← Ioi_insert]
  simpa using (isClopen_Ioi x).isClosed.union (isClosed_singleton (x := x))

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

theorem isClopen_singleton_of_not_isSuccLimit {x : Simplicity} (hx : ¬ IsSuccLimit x) :
    IsClopen {x} := by
  rw [not_isSuccLimit_iff, not_isSuccPrelimit_iff_exists_covBy] at hx
  obtain hx | ⟨y, hx⟩ := hx
  · rw [← hx.Iic_eq]
    exact isClopen_Iic x
  · rw [← hx.Ioc_eq]
    exact isClopen_Ioc y x

@[simp]
theorem isClopen_singleton_bot : IsClopen {(⊥ : Simplicity)} :=
  isClopen_singleton_of_not_isSuccLimit not_isSuccLimit_bot

theorem nhds_eq_pure_of_not_isSuccLimit {x : Simplicity} (hx : ¬ IsSuccLimit x) :
    𝓝 x = pure x := by
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
          not_isSuccPrelimit_iff_exists_covBy] at hx'
        obtain ⟨y, hy⟩ := hx'
        use y, hy.lt
        rw [hy.Ioc_eq, singleton_subset_iff]
        exact hts hx
    · rintro ⟨y, hy, hs⟩
      exact ⟨_, hs, (isClopen_Ioc y x).isOpen, ⟨hy, le_rfl⟩⟩

theorem isTopologicalBasis_setOf_isClopen :
    TopologicalSpace.IsTopologicalBasis {s : Set Simplicity | IsClopen s} := by
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

instance : CompletelyRegularSpace Simplicity :=
  .of_isTopologicalBasis_clopens isTopologicalBasis_setOf_isClopen

instance : T35Space Simplicity where

end Simplicity
end
