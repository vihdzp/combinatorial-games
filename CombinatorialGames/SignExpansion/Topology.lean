/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.SignExpansion.Simplicity
public import Mathlib.Topology.Order.ScottTopology

/-!
# Topology on sign expansions

We give sign expansions the Scott-Hausdorff topology.
-/

theorem Topology.IsScottHausdorff.isOpen_iff_dirSupInacc {α : Type*} [TopologicalSpace α]
    [PartialOrder α] [Topology.IsScottHausdorff α .univ] {s : Set α} :
    IsOpen s ↔ DirSupInacc s where
  mp h := dirSupInaccOn_univ.1 <| Topology.IsScottHausdorff.dirSupInaccOn_of_isOpen h
  mpr h := by
    rw [Topology.IsScottHausdorff.isOpen_iff (D := .univ)]
    intro t _ ht₀ ht₁ a ha has
    have := h ht₀ ht₁ ha has
    by_cases ht : a ∈ t
    · refine ⟨a, ht, fun b ⟨hba, hbt⟩ ↦ ?_⟩
      obtain rfl := (ha.1 hbt).antisymm hba
      exact has
    · by_contra! H
      have H : ∀ b : t, ∃ c, b.1 ≤ c ∧ c ∈ t ∧ c ∉ s := by simpa [Set.not_subset, and_assoc] using H
      choose f hf using H
      have := ht₀.to_subtype
      have hft : Set.range f ⊆ t := by grind
      apply (h (Set.range_nonempty f) _ _ has).ne_empty
      · aesop
      · intro a ha b hb
        obtain ⟨c, hc, _, _⟩ := ht₁ _ (hft ha) _ (hft hb)
        have := hf ⟨c, hc⟩
        grind
      · exact ⟨upperBounds_mono_set hft ha.1,
          fun b hb ↦ ha.2 fun c hc ↦ (hf ⟨c, hc⟩).1.trans (hb <| by simp)⟩

theorem Topology.IsScottHausdorff.isClosed_iff_dirSupClosed {α : Type*} [TopologicalSpace α]
    [PartialOrder α] [Topology.IsScottHausdorff α .univ] {s : Set α} :
    IsClosed s ↔ DirSupClosed s := by
  rw [← isOpen_compl_iff, Topology.IsScottHausdorff.isOpen_iff_dirSupInacc, dirSupInacc_compl]

namespace Simplicity

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

/-- For any `x` and `o < x.length`, the set of restrictions `x ↾ a` with `a < o` form a neighborhood
basis for `x`. -/
def restrictSet (x : Simplicity) (o : NatOrdinal) : Set Simplicity

end Simplicity
