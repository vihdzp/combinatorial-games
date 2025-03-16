/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
import CombinatorialGames.Surreal.Basic

/-!
# Small games all around

We define dicotic games, games `x` where both players can move from
every nonempty subposition of `x`. We prove that these games are small, and relate them
to infinitesimals.

## TODO

- Define infinitesimal games as games x such that ∀ y : ℝ, 0 < y → -y < x ∧ x < y
  - (Does this hold for small infinitesimal games?)
- Prove that any short game is an infinitesimal (but not vice versa, consider `ω⁻¹`)
-/

namespace IGame

/-! # Dicotic Games -/

private def DicoticAux (x : IGame) : Prop :=
  (x.leftMoves = ∅ ↔ x.rightMoves = ∅) ∧
    (∀ l ∈ x.leftMoves, DicoticAux l) ∧ (∀ r ∈ x.rightMoves, DicoticAux r)
termination_by x
decreasing_by igame_wf

/-- A game `G` is dicotic if both players can move from every nonempty subposition of `G` -/
@[mk_iff dicotic_iff_aux]
class Dicotic (x : IGame) : Prop where
  out : DicoticAux x

theorem dicotic_def {x : IGame} : Dicotic x ↔
    (x.leftMoves = ∅ ↔ x.rightMoves = ∅) ∧
      (∀ l ∈ x.leftMoves, Dicotic l) ∧ (∀ r ∈ x.rightMoves, Dicotic r) := by
  simp_rw [dicotic_iff_aux]; rw [DicoticAux]

namespace Dicotic
variable {x y z : IGame}

theorem neq_zero_iff [hx : Dicotic x] : x ≠ 0 ↔ x.leftMoves ≠ ∅ ∧ x.rightMoves ≠ ∅ := by
  rw [dicotic_def] at hx
  rw [Ne.eq_def, zero_def, IGame.ext_iff, leftMoves_ofSets, rightMoves_ofSets]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp_all⟩
  by_cases x.leftMoves = ∅ <;> simp_all

@[simp]
protected instance zero : Dicotic 0 := by
  rw [dicotic_def]
  simp

protected instance neg (x) [hx : Dicotic x] : Dicotic (-x) := by
  rw [dicotic_def, leftMoves_neg, rightMoves_neg] at *
  refine ⟨by simp_all, fun l hl ↦ ?_, fun r hr ↦ ?_⟩
  · have h := @Dicotic.neg (-l) (hx.2.2 (-l) <| Set.mem_neg.mp hl)
    rw [neg_neg] at h
    exact h
  · have h := @Dicotic.neg (-r) (hx.2.1 (-r) <| Set.mem_neg.mp hr)
    rw [neg_neg] at h
    exact h
termination_by x
decreasing_by all_goals simp_all; igame_wf

theorem of_mem_leftMoves [h : Dicotic x] (hy : y ∈ x.leftMoves) : Dicotic y := by
  cases (dicotic_def.1 h); simp_all

theorem of_mem_rightMoves [h : Dicotic x] (hy : y ∈ x.rightMoves) : Dicotic y := by
  cases (dicotic_def.1 h); simp_all

theorem lt_surreal (x) [hx : Dicotic x] (y) [hny : Numeric y] (hy : 0 < y) : x < y := by
  rw [lt_iff_le_not_le, lf_iff_exists_le, le_iff_forall_lf]
  refine ⟨⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩, ?_⟩
  · have : Dicotic z := of_mem_leftMoves hz
    exact not_le_of_lt <| lt_surreal z y hy
  · suffices x < z by exact (lt_iff_le_not_le.mp this).2
    have : Numeric z := Numeric.of_mem_rightMoves hz
    rcases Numeric.lt_or_equiv_or_gt z 0 with (h | h | h)
    · exact absurd hy (not_lt_of_gt <| (Numeric.lt_rightMove hz).trans h)
    · exact absurd hy (not_lt_of_gt <| (Numeric.lt_rightMove hz).trans_le h.1)
    · exact lt_surreal x z h
  · by_cases h : x = 0
    · subst h
      exact Numeric.lt_iff_exists_le.mp hy
    · have h := (neq_zero_iff.mp h).2
      push_neg at h
      have : h.choose.Dicotic := of_mem_rightMoves h.choose_spec
      exact .inr ⟨h.choose, h.choose_spec, le_of_lt <| lt_surreal h.choose y hy⟩
termination_by (x, y)
decreasing_by igame_wf

theorem surreal_lt (x) [hx : Dicotic x] (y) (hy : Numeric y) (hy : y < 0) : y < x :=
  IGame.neg_lt_neg_iff.mp <| lt_surreal (-x) (-y) (zero_lt_neg.mpr hy)

end Dicotic

end IGame
