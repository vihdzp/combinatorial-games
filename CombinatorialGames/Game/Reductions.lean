/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import CombinatorialGames.Game.IGame
public import Mathlib.Algebra.Group.Pointwise.Set.Lattice

/-!
# Game reductions

We prove that dominated moves can be deleted, reversible moves can be bypassed,
and gift horses can be given, without changing the value of the game.
-/

public section

universe u v

namespace IGame
open Set

variable {u v : IGame.{u}} {w : Player → Set IGame.{u}}

/-- If every move in `w` is dominated by a move in `v`, then the game `u` is equivalent
to the game `v` obtained by removing the dominated options in `w` from `u`. -/
theorem equiv_of_dominated
    (hu : ∀ p, ∀ g ∈ w p, ∃ g' ∈ v.moves p, p.cases (g ≤ g') (g' ≤ g))
    (hw : ∀ p, u.moves p ∈ Icc (v.moves p) (v.moves p ∪ w p)) : u ≈ v := by
  apply equiv_of_exists_le <;> intro z hz
  · exact ((hw left).2 hz).elim (fun hz => ⟨z, hz, le_rfl⟩) (fun hz => hu left z hz)
  · exact ((hw right).2 hz).elim (fun hz => ⟨z, hz, le_rfl⟩) (fun hz => hu right z hz)
  · exact ⟨z, (hw left).1 hz, le_rfl⟩
  · exact ⟨z, (hw right).1 hz, le_rfl⟩

private theorem equiv_of_bypass_left {ι : Type v} {l r u v : Set IGame.{u}}
    [Small.{u} r] [Small.{u} u] [Small.{u} v]
    {c cr : ι → IGame.{u}} (hbb : ∀ i, cr i ≤ !{u | r})
    (hcr : ∀ i, cr i ∈ (c i).moves right)
    (hu : u ∈ Icc l (range c ∪ l)) (hv : v = (⋃ i ∈ c ⁻¹' u, (cr i).moves left) ∪ l) :
    !{u | r} ≈ !{v | r} := by
  apply equiv_of_forall_lf <;> simp only [moves_ofSets, Player.cases] <;> intro z hz
  · obtain ⟨i, rfl⟩ | hzu := hu.2 hz
    · refine lf_of_right_le (le_iff_forall_lf.2 ⟨?_, ?_⟩) (hcr i) <;> intro z hz'
      · apply left_lf
        rw [leftMoves_ofSets, hv]
        exact .inl (mem_biUnion hz hz')
      · refine fun h => lf_right ?_ (h.trans (hbb i))
        simpa using hz'
    · apply left_lf
      rw [leftMoves_ofSets, hv]
      exact .inr hzu
  · apply lf_right
    simpa using hz
  · rw [hv, mem_union, mem_iUnion₂] at hz
    obtain ⟨i, hi, hz⟩ | hz := hz
    · exact fun h => left_lf hz ((hbb i).trans h)
    · apply left_lf
      rw [leftMoves_ofSets]
      exact hu.1 hz
  · apply lf_right
    simpa using hz

private theorem equiv_of_bypass_right {ι : Type v} {l r u v : Set IGame.{u}}
    [Small.{u} l] [Small.{u} u] [Small.{u} v]
    {d dl : ι → IGame.{u}} (hbb : ∀ i, !{l | u} ≤ dl i)
    (hdl : ∀ i, dl i ∈ (d i).moves left)
    (hu : u ∈ Icc r (range d ∪ r)) (hv : v = (⋃ i ∈ d ⁻¹' u, (dl i).moves right) ∪ r) :
    !{l | u} ≈ !{l | v} := by
  rw [← neg_equiv_neg_iff, neg_ofSets, neg_ofSets]
  refine @equiv_of_bypass_left ι (-r) (-l) (-u) (-v) _ _ _ (-d) (-dl) ?_ ?_ ?_ ?_
  · simpa [← neg_ofSets] using hbb
  · simpa using hdl
  · simpa [neg_subset, neg_range] using hu
  · simpa [neg_eq_iff_eq_neg] using hv

/-- If each of the moves `c p i ∈ u.moves p` in `u` is reversed by `cr p i ∈ (c p i).moves (-p)`,
then `u` is equivalent to the game `v` which bypasses each `c p i` by
replacing it with `(cr p i).moves p`. -/
theorem equiv_of_bypass {ι : Type v} {c cr : Player → ι → IGame.{u}}
    (hbb : ∀ (p : Player) i, p.cases (cr p i ≤ u) (u ≤ cr p i))
    (hcr : ∀ p i, cr p i ∈ (c p i).moves (-p))
    (hu : ∀ p, u.moves p ∈ Icc (w p) (range (c p) ∪ w p))
    (hv : ∀ p, v.moves p = (⋃ i ∈ c p ⁻¹' u.moves p, (cr p i).moves p) ∪ w p) :
    u ≈ v := by
  rw [← ofSets_moves u, ofSets_eq_ofSets_cases u.moves] at hbb ⊢
  have hl := equiv_of_bypass_left (hbb left) (hcr left) (hu left) (hv left)
  have hr := equiv_of_bypass_right
    (fun i => hl.ge.trans (hbb right i)) (hcr right) (hu right) (hv right)
  grw [hl, hr]
  simp

/-- The game `u` is equivalent to the game `v` obtained from `u`
by adding the gift horses in `w`. -/
theorem equiv_of_gift
    (hg : ∀ p, ∀ g ∈ w p, ¬p.cases (u ≤ g) (g ≤ u))
    (hu : ∀ p, v.moves p ∈ Icc (u.moves p) (u.moves p ∪ w p)) : u ≈ v := by
  apply equiv_of_forall_lf <;> intro z hz
  · apply left_lf
    exact (hu left).1 hz
  · apply lf_right
    exact (hu right).1 hz
  · obtain hz | hz := (hu left).2 hz
    · apply left_lf
      simpa using hz
    · exact hg left z hz
  · obtain hz | hz := (hu right).2 hz
    · apply lf_right
      simpa using hz
    · exact hg right z hz

end IGame
