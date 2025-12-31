/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Game.IGame
import Mathlib.Algebra.Group.Pointwise.Set.Lattice

/-!
# Game reductions

We prove that dominated moves can be deleted and reversible moves can be bypassed.
-/

universe u v

namespace IGame
open Set

theorem equiv_of_dominated_left {u v w r : Set IGame.{u}}
    [Small.{u} v] [Small.{u} w] [Small.{u} r]
    (hu : ∀ g ∈ u, ∃ g' ∈ v, g ≤ g') (hw : w ∈ Icc v (u ∪ v)) : !{w | r} ≈ !{v | r} := by
  apply equiv_of_exists_le <;> simp only [moves_ofSets, Player.cases]
  · exact fun z hz => (hw.2 hz).elim (fun hz => hu z hz) (fun hz => ⟨z, hz, le_rfl⟩)
  · exact fun z hz => ⟨z, hz, le_rfl⟩
  · exact fun z hz => ⟨z, hw.1 hz, le_rfl⟩
  · exact fun z hz => ⟨z, hz, le_rfl⟩

theorem equiv_of_dominated_right {l u v w : Set IGame.{u}}
    [Small.{u} l] [Small.{u} u] [Small.{u} v] [Small.{u} w]
    (hu : ∀ g ∈ u, ∃ g' ∈ v, g' ≤ g) (hw : w ∈ Icc v (u ∪ v)) : !{l | w} ≈ !{l | v} := by
  apply equiv_of_exists_le <;> simp only [moves_ofSets, Player.cases]
  · exact fun z hz => ⟨z, hz, le_rfl⟩
  · exact fun z hz => (hw.2 hz).elim (fun hz => hu z hz) (fun hz => ⟨z, hz, le_rfl⟩)
  · exact fun z hz => ⟨z, hz, le_rfl⟩
  · exact fun z hz => ⟨z, hw.1 hz, le_rfl⟩

theorem equiv_of_bypass_left {ι : Type v} {l r u v : Set IGame.{u}}
    [Small.{u} l] [Small.{u} r] [Small.{u} u] [Small.{u} v]
    {c cr : ι → IGame.{u}} (hbb : ∀ i, cr i ≤ !{u | r})
    (hcr : ∀ i, cr i ∈ (c i).moves right)
    (hu : u ∈ Icc l (range c ∪ l)) (hv : v = (⋃ i ∈ c ⁻¹' u, (cr i).moves left) ∪ l) :
    !{u | r} ≈ !{v | r} := by
  cases hv
  apply equiv_of_forall_lf <;> simp only [moves_ofSets, Player.cases]
  · intro z hzu
    obtain ⟨i, rfl⟩ | hz := hu.2 hzu
    · refine lf_of_right_le (le_iff_forall_lf.2 ⟨?_, ?_⟩) (hcr i)
      · intro z hz
        apply left_lf
        rw [leftMoves_ofSets]
        exact .inl (mem_biUnion hzu hz)
      · intro z hz
        refine fun h => lf_right ?_ (h.trans (hbb i))
        simpa using hz
    · apply left_lf
      rw [leftMoves_ofSets]
      exact .inr hz
  · intro z hz
    apply lf_right
    simpa using hz
  · intro z hz
    obtain hz | hz := hz
    · simp only [mem_preimage, mem_iUnion, exists_prop] at hz
      obtain ⟨i, hi, hz⟩ := hz
      exact fun h => left_lf hz ((hbb i).trans h)
    · apply left_lf
      rw [leftMoves_ofSets]
      exact hu.1 hz
  · intro z hz
    apply lf_right
    simpa using hz

theorem equiv_of_bypass_right {ι : Type v} {l r u v : Set IGame.{u}}
    [Small.{u} l] [Small.{u} r] [Small.{u} u] [Small.{u} v]
    {d dl : ι → IGame.{u}} (hbb : ∀ i, !{l | u} ≤ dl i)
    (hdl : ∀ i, dl i ∈ (d i).moves left)
    (hu : u ∈ Icc r (range d ∪ r)) (hv : v = (⋃ i ∈ d ⁻¹' u, (dl i).moves right) ∪ r) :
    !{l | u} ≈ !{l | v} := by
  rw [← neg_equiv_neg_iff, neg_ofSets, neg_ofSets]
  refine @equiv_of_bypass_left ι (-r) (-l) (-u) (-v) _ _ _ _ (-d) (-dl) ?_ ?_ ?_ ?_
  · simpa [← neg_ofSets] using hbb
  · simpa using hdl
  · simpa [neg_subset, neg_range] using hu
  · simpa [neg_eq_iff_eq_neg] using hv

theorem equiv_of_gift_left {gs l r u : Set IGame.{u}} [Small.{u} l] [Small.{u} r] [Small.{u} u]
    (hg : ∀ g ∈ gs, ¬!{l | r} ≤ g) (hu : u ∈ Icc l (gs ∪ l)) : !{l | r} ≈ !{u | r} := by
  apply equiv_of_forall_lf <;> simp only [moves_ofSets, Player.cases]
  · intro z hz
    apply left_lf
    rw [leftMoves_ofSets]
    exact hu.1 hz
  · intro z hz
    apply lf_right
    simpa using hz
  · intro z hz
    obtain hz | hz := hu.2 hz
    · exact hg z hz
    · apply left_lf
      simpa using hz
  · intro z hz
    apply lf_right
    simpa using hz

theorem equiv_of_gift_right {gs l r u : Set IGame.{u}} [Small.{u} l] [Small.{u} r] [Small.{u} u]
    (hg : ∀ g ∈ gs, ¬g ≤ !{l | r}) (hu : u ∈ Icc r (gs ∪ r)) : !{l | r} ≈ !{l | u} := by
  rw [← neg_equiv_neg_iff, neg_ofSets, neg_ofSets]
  refine @equiv_of_gift_left (-gs) (-r) (-l) (-u) _ _ _ ?_ ?_
  · simpa [← neg_ofSets] using hg
  · simpa [neg_subset] using hu

end IGame
