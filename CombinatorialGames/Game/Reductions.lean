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

variable {u v w g : Player → Set IGame.{u}}
    [Small.{u} (u left)] [Small.{u} (u right)]
    [Small.{u} (v left)] [Small.{u} (v right)]
    [Small.{u} (w left)] [Small.{u} (w right)]

omit [Small.{u} (u left)] [Small.{u} (u right)] in
/-- If every move in `u` is dominated by a move in `v`, then the game `!{w}` is equivalent
to the game `!{v}` obtained by removing the dominated options in `u` from `!{w}`. -/
theorem equiv_of_dominated
    (hu : ∀ p, ∀ g ∈ u p, ∃ g' ∈ v p, p.cases (g ≤ g') (g' ≤ g))
    (hw : ∀ p, w p ∈ Icc (v p) (u p ∪ v p)) : !{w} ≈ !{v} := by
  apply equiv_of_exists_le <;> simp only [moves_ofSets] <;> intro z hz
  · exact ((hw left).2 hz).elim (fun hz => hu left z hz) (fun hz => ⟨z, hz, le_rfl⟩)
  · exact ((hw right).2 hz).elim (fun hz => hu right z hz) (fun hz => ⟨z, hz, le_rfl⟩)
  · exact ⟨z, (hw left).1 hz, le_rfl⟩
  · exact ⟨z, (hw right).1 hz, le_rfl⟩

private theorem equiv_of_bypass_left {ι : Type v} {l r u v : Set IGame.{u}}
    [Small.{u} r] [Small.{u} u] [Small.{u} v]
    {c cr : ι → IGame.{u}} (hbb : ∀ i, cr i ≤ !{u | r})
    (hcr : ∀ i, cr i ∈ (c i).moves right)
    (hu : u ∈ Icc l (range c ∪ l)) (hv : v = (⋃ i ∈ c ⁻¹' u, (cr i).moves left) ∪ l) :
    !{u | r} ≈ !{v | r} := by
  subst hv
  apply equiv_of_forall_lf <;> simp only [moves_ofSets, Player.cases] <;> intro z hz
  · obtain ⟨i, rfl⟩ | hzu := hu.2 hz
    · refine lf_of_right_le (le_iff_forall_lf.2 ⟨?_, ?_⟩) (hcr i) <;> intro z hz'
      · apply left_lf
        rw [leftMoves_ofSets]
        exact .inl (mem_biUnion hz hz')
      · refine fun h => lf_right ?_ (h.trans (hbb i))
        simpa using hz'
    · apply left_lf
      rw [leftMoves_ofSets]
      exact .inr hzu
  · apply lf_right
    simpa using hz
  · rw [mem_union, mem_iUnion₂] at hz
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

/-- If each of the moves `c p i ∈ u p` in `!{u}` is reversed by `cr p i ∈ (c p i).moves (-p)`,
then `!{u}` is equivalent to the game `!{v}` which bypasses each `c p i` by
replacing it with `(cr p i).moves p`. -/
theorem equiv_of_bypass {ι : Type v} {c cr : Player → ι → IGame.{u}}
    (hbb : ∀ (p : Player) i, p.cases (cr p i ≤ !{u}) (!{u} ≤ cr p i))
    (hcr : ∀ p i, cr p i ∈ (c p i).moves (-p))
    (hu : ∀ p, u p ∈ Icc (g p) (range (c p) ∪ g p))
    (hv : ∀ p, v p = (⋃ i ∈ c p ⁻¹' u p, (cr p i).moves p) ∪ g p) :
    !{u} ≈ !{v} := by
  rw [ofSets_eq_ofSets_cases u] at hbb ⊢
  have hl := equiv_of_bypass_left (hbb left) (hcr left) (hu left) (hv left)
  have hr := equiv_of_bypass_right
    (fun i => hl.ge.trans (hbb right i)) (hcr right) (hu right) (hv right)
  grw [hl, hr]
  rw [ofSets_eq_ofSets_cases v]

/-- The game `!{u}` is equivalent to the game `!{v}` obtained from `!{u}`
by adding the gift horses in `g`. -/
theorem equiv_of_gift
    (hg : ∀ p, ∀ z ∈ g p, ¬p.cases (!{u} ≤ z) (z ≤ !{u}))
    (hu : ∀ p, v p ∈ Icc (u p) (g p ∪ u p)) : !{u} ≈ !{v} := by
  apply equiv_of_forall_lf <;> simp only [moves_ofSets] <;> intro z hz
  · apply left_lf
    rw [moves_ofSets]
    exact (hu left).1 hz
  · apply lf_right
    rw [moves_ofSets]
    exact (hu right).1 hz
  · obtain hz | hz := (hu left).2 hz
    · exact hg left z hz
    · apply left_lf
      simpa using hz
  · obtain hz | hz := (hu right).2 hz
    · exact hg right z hz
    · apply lf_right
      simpa using hz

end IGame
