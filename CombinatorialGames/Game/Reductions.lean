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

universe u

namespace IGame

theorem equiv_of_dominated_left {u v r : Set IGame.{u}} [Small.{u} u] [Small.{u} v] [Small.{u} r]
    (hu : ∀ g ∈ u, ∃ g' ∈ v, g ≤ g') : {u ∪ v | r}ᴵ ≈ {v | r}ᴵ := by
  apply equiv_of_exists_le <;> aesop

theorem equiv_of_dominated_right {l u v : Set IGame.{u}} [Small.{u} l] [Small.{u} u] [Small.{u} v]
    (hu : ∀ g ∈ u, ∃ g' ∈ v, g' ≤ g) : {l | u ∪ v}ᴵ ≈ {l | v}ᴵ := by
  apply equiv_of_exists_le <;> aesop

theorem equiv_of_bypass_left {ι : Type u} {l r : Set IGame.{u}} [Small.{u} l] [Small.{u} r]
    {c cr : ι → IGame.{u}} (hbb : ∀ i, cr i ≤ {Set.range c ∪ l | r}ᴵ)
    (hcr : ∀ i, cr i ∈ (c i).rightMoves) :
    {Set.range c ∪ l | r}ᴵ ≈ {(⋃ i, (cr i).leftMoves) ∪ l | r}ᴵ := by
  apply equiv_of_forall_lf <;> simp only [leftMoves_ofSets, rightMoves_ofSets]
  · rintro z (⟨i, rfl⟩ | hz)
    · refine lf_of_rightMove_le (le_iff_forall_lf.2 ⟨?_, ?_⟩) (hcr i)
      · intro z hz
        apply leftMove_lf
        rw [leftMoves_ofSets]
        exact .inl (Set.mem_iUnion_of_mem i hz)
      · intro z hz
        apply not_le_of_le_of_not_le (hbb i)
        apply lf_rightMove
        rwa [rightMoves_ofSets] at hz ⊢
    · apply leftMove_lf
      rw [leftMoves_ofSets]
      exact .inr hz
  · intro z hz
    apply lf_rightMove
    rwa [rightMoves_ofSets]
  · intro z hz
    obtain ⟨_, ⟨i, rfl⟩, hz⟩ | hz := hz
    · exact not_le_of_not_le_of_le (leftMove_lf hz) (hbb i)
    · apply leftMove_lf
      rw [leftMoves_ofSets]
      exact .inr hz
  · intro z hz
    apply lf_rightMove
    rwa [rightMoves_ofSets]

theorem equiv_of_bypass_right {ι : Type u} {l r : Set IGame.{u}} [Small.{u} l] [Small.{u} r]
    {d dl : ι → IGame.{u}} (hbb : ∀ i, {l | Set.range d ∪ r}ᴵ ≤ dl i)
    (hdl : ∀ i, dl i ∈ (d i).leftMoves) :
    {l | Set.range d ∪ r}ᴵ ≈ {l | (⋃ i, (dl i).rightMoves) ∪ r}ᴵ := by
  rw [← neg_equiv_neg_iff]
  conv at hbb =>
    intro i
    rw [← IGame.neg_le_neg_iff, neg_ofSets]
    simp only [Set.union_neg, Set.neg_range]
  conv at hdl =>
    intro i
    rw [← Set.neg_mem_neg, leftMoves, ← Player.neg_right, ← moves_neg]
  simpa [Set.neg_range] using equiv_of_bypass_left hbb hdl

theorem equiv_of_gift_left {gs l r : Set IGame.{u}} [Small.{u} gs] [Small.{u} l] [Small.{u} r]
    (hg : ∀ g ∈ gs, ¬{l | r}ᴵ ≤ g) : {l | r}ᴵ ≈ {gs ∪ l | r}ᴵ := by
  apply equiv_of_forall_lf
  · intro z hz
    apply leftMove_lf
    rw [leftMoves_ofSets] at hz ⊢
    exact .inr hz
  · intro z hz
    apply lf_rightMove
    rwa [rightMoves_ofSets] at hz ⊢
  · intro z hz
    rw [leftMoves_ofSets] at hz
    obtain hz | hz := hz
    · exact hg z hz
    · apply leftMove_lf
      rwa [leftMoves_ofSets]
  · intro z hz
    apply lf_rightMove
    rwa [rightMoves_ofSets] at hz ⊢

theorem equiv_of_gift_right {gs l r : Set IGame.{u}} [Small.{u} gs] [Small.{u} l] [Small.{u} r]
    (hg : ∀ g ∈ gs, ¬g ≤ {l | r}ᴵ) : {l | r}ᴵ ≈ {l | gs ∪ r}ᴵ := by
  rw [← neg_equiv_neg_iff]
  conv at hg =>
    rw [← neg_involutive.toPerm.forall_congr_right]
    intro g
    rw [Function.Involutive.coe_toPerm, ← IGame.neg_le_neg_iff, neg_neg, neg_ofSets, ← Set.mem_neg]
  simpa using equiv_of_gift_left hg

end IGame
