/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
import CombinatorialGames.Surreal.Basic

/-!
# Small games all around

We define dicotic games, games `G` where both players can move from
every nonempty subposition of `G`. We prove that these games are small, and relate them
to infinitesimals.

## TODO

- Define infinitesimal games as games x such that ∀ y : ℝ, 0 < y → -y < x ∧ x < y
  - (Does this hold for small infinitesimal games?)
- Prove that dicotic = ∀ y : IGame, Numeric y → 0 < y → -y < x ∧ x < y
- Prove that any short game is an infinitesimal (but not vice versa! see 1/ω)
-/

namespace IGame

/-! # Dicotic Games -/

private def DicoticAux (x : IGame) : Prop :=
  (x.leftMoves = ∅ ∧ x.rightMoves = ∅) ∨
  (x.leftMoves ≠ ∅ ∧ x.rightMoves ≠ ∅ ∧
    (∀ l ∈ x.leftMoves, DicoticAux l) ∧
    ∀ r ∈ x.rightMoves, DicoticAux r)
termination_by x
decreasing_by igame_wf

/-- A game `G` is dicotic if both players can move from every nonempty subposition of `G` -/
@[mk_iff dicotic_iff_aux]
class Dicotic (x : IGame) : Prop where
  out : DicoticAux x

theorem dicotic_def {x : IGame} : Dicotic x ↔
    (x.leftMoves = ∅ ∧ x.rightMoves = ∅) ∨
    (x.leftMoves ≠ ∅ ∧ x.rightMoves ≠ ∅ ∧
      (∀ l ∈ x.leftMoves, Dicotic l) ∧
      ∀ r ∈ x.rightMoves, Dicotic r) := by
  simp_rw [dicotic_iff_aux]; rw [DicoticAux]

namespace Dicotic
variable {x y z : IGame}

theorem dicotic_zero_iff [hx : Dicotic x] : x ≠ 0 ↔ x.leftMoves ≠ ∅ ∧ x.rightMoves ≠ ∅ := by
  rw [dicotic_def] at hx
  rw [Ne.eq_def, zero_def, IGame.ext_iff, leftMoves_ofSets, rightMoves_ofSets]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp_all⟩
  by_cases x.leftMoves = ∅ <;> simp_all

@[simp]
protected instance zero : Dicotic 0 := by
  rw [dicotic_def]
  simp

protected instance neg (x) [hx : Dicotic x] : Dicotic (-x) := by
  rw [dicotic_def, ne_eq] at *
  cases hx with
  | inl hx => simp_all
  | inr hx =>
    refine .inr ⟨by simp_all, by simp_all, fun l hl ↦ ?_, fun r hr ↦ ?_⟩
    · rw [leftMoves_neg] at hl
      have h := @Dicotic.neg (-l) (hx.2.2.2 (-l) <| Set.mem_neg.mp hl)
      rw [neg_neg] at h
      exact h
    · rw [rightMoves_neg] at hr
      have h := @Dicotic.neg (-r) (hx.2.2.1 (-r) <| Set.mem_neg.mp hr)
      rw [neg_neg] at h
      exact h
termination_by x
decreasing_by all_goals simp_all; igame_wf

theorem of_mem_leftMoves [h : Dicotic x] (hy : y ∈ x.leftMoves) : Dicotic y := by
  cases (dicotic_def.1 h) <;> simp_all

theorem of_mem_rightMoves [h : Dicotic x] (hy : y ∈ x.rightMoves) : Dicotic y := by
  cases (dicotic_def.1 h) <;> simp_all

theorem lt_surreal (x) [hx : Dicotic x] (y) [hny : Numeric y] (hy : 0 < y) : x < y := by
  rw [lt_iff_le_not_le, lf_iff_exists_le, le_iff_forall_lf]
  refine ⟨⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩, ?_⟩
  · suffices z < y by rw [lt_iff_le_not_le] at this; exact this.2
    have : Dicotic z := of_mem_leftMoves hz
    exact lt_surreal z y hy
  · suffices x < z by rw [lt_iff_le_not_le] at this; exact this.2
    have : Numeric z := Numeric.of_mem_rightMoves hz
    by_cases h : 0 < z
    · exact lt_surreal x z h
    · rw [Numeric.not_lt] at h
      rw [numeric_def] at hny
      have := hny.1
      sorry
  · by_cases h : x = 0
    · left
      subst h
      sorry
    · have h := (dicotic_zero_iff.mp h).2
      push_neg at h
      have : h.choose.Dicotic := of_mem_rightMoves h.choose_spec
      exact .inr ⟨h.choose, h.choose_spec, le_of_lt <| lt_surreal h.choose y hy⟩
termination_by (x, y)
decreasing_by igame_wf

end Dicotic

end IGame
