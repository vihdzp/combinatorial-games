/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.SignExpansion.Simplicity
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Order.ScottTopology

/-!
# Topology on sign expansions

We give sign expansions the Scott-Hausdorff topology.
-/

namespace Simplicity
open Set SignExpansion

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
    exact ht hy <| (le_sSup hy ht₁).trans hx

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
    exact (ht hy).trans_le (le_sSup hy ht₁)
  · have : Ioi x = ⋃ y : Ioi x, Ioc x y := by aesop
    rw [this]
    exact isOpen_iUnion fun i ↦ (isClopen_Ioc ..).isOpen

end Simplicity
