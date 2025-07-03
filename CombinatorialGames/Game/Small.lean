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

- Define infinitesimal games as games `x` such that `∀ r : ℝ, 0 < r → -r < x ∧ x < r`
  - (Does this hold for small infinitesimal games?)
- Prove that any short dicotic game is an infinitesimal (but not vice versa, consider `ω⁻¹`)
-/

namespace IGame

/-! ### Dicotic games -/

private def DicoticAux (x : IGame) : Prop :=
  (x.leftMoves = ∅ ↔ x.rightMoves = ∅) ∧
    (∀ l ∈ x.leftMoves, DicoticAux l) ∧ (∀ r ∈ x.rightMoves, DicoticAux r)
termination_by x
decreasing_by igame_wf

/-- A game `x` is dicotic if both players can move from every nonempty subposition of `x`. -/
@[mk_iff dicotic_iff_aux]
class Dicotic (x : IGame) : Prop where
  out : DicoticAux x

theorem dicotic_def {x : IGame} : Dicotic x ↔
    (x.leftMoves = ∅ ↔ x.rightMoves = ∅) ∧
      (∀ l ∈ x.leftMoves, Dicotic l) ∧ (∀ r ∈ x.rightMoves, Dicotic r) := by
  simp_rw [dicotic_iff_aux]; rw [DicoticAux]

namespace Dicotic
variable {x y z : IGame}

theorem eq_zero_iff [hx : Dicotic x] : x = 0 ↔ x.leftMoves = ∅ ∨ x.rightMoves = ∅ := by
  rw [dicotic_def] at hx
  simp_all [IGame.ext_iff]

theorem ne_zero_iff [Dicotic x] : x ≠ 0 ↔ x.leftMoves ≠ ∅ ∧ x.rightMoves ≠ ∅ := by
  simpa using eq_zero_iff.not

theorem mk' (h : x.leftMoves = ∅ ↔ x.rightMoves = ∅)
    (hl : ∀ y ∈ x.leftMoves, Dicotic y) (hr : ∀ y ∈ x.rightMoves, Dicotic y) : Dicotic x :=
  dicotic_def.2 ⟨h, hl, hr⟩

theorem leftMoves_eq_empty_iff [hx : Dicotic x] : x.leftMoves = ∅ ↔ x.rightMoves = ∅ :=
  (dicotic_def.1 hx).1

theorem rightMoves_eq_empty_iff [hx : Dicotic x] : x.rightMoves = ∅ ↔ x.leftMoves = ∅ :=
  leftMoves_eq_empty_iff.symm

protected theorem of_mem_leftMoves [hx : Dicotic x] (h : y ∈ x.leftMoves) : Dicotic y :=
  (dicotic_def.1 hx).2.1 y h

protected theorem of_mem_rightMoves [hx : Dicotic x] (h : y ∈ x.rightMoves) : Dicotic y :=
  (dicotic_def.1 hx).2.2 y h

@[simp]
protected instance zero : Dicotic 0 := by
  rw [dicotic_def]
  simp

protected instance neg (x) [Dicotic x] : Dicotic (-x) := by
  rw [dicotic_def, forall_leftMoves_neg, forall_rightMoves_neg]
  refine ⟨by simp [leftMoves_eq_empty_iff], fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · have := Dicotic.of_mem_rightMoves hy
    exact .neg y
  · have := Dicotic.of_mem_leftMoves hy
    exact .neg y
termination_by x
decreasing_by igame_wf

/--
One half of the **lawnmower theorem**:
any dicotic game is smaller than any positive numeric game.
-/
theorem lt_of_numeric_of_pos (x) [Dicotic x] {y} [Numeric y] (hy : 0 < y) : x < y := by
  rw [lt_iff_le_not_ge, le_iff_forall_lf]
  refine ⟨⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩, ?_⟩
  · have := Dicotic.of_mem_leftMoves hz
    exact (lt_of_numeric_of_pos z hy).not_ge
  · have := Numeric.of_mem_rightMoves hz
    obtain (h | h) := Numeric.le_or_lt z 0
    · cases ((Numeric.lt_rightMove hz).trans_le h).not_gt hy
    · exact (lt_of_numeric_of_pos x h).not_ge
  · obtain rfl | h := eq_or_ne x 0
    · exact hy.not_ge
    · simp_rw [ne_zero_iff, ← Set.nonempty_iff_ne_empty] at h
      obtain ⟨z, hz⟩ := h.2
      have := Dicotic.of_mem_rightMoves hz
      exact lf_of_rightMove_le (lt_of_numeric_of_pos z hy).le hz
termination_by (x, y)
decreasing_by igame_wf

/--
One half of the **lawnmower theorem**:
any dicotic game is greater than any negative numeric game.
-/
theorem lt_of_numeric_of_neg (x) [Dicotic x] {y} [Numeric y] (hy : y < 0) : y < x := by
  have := lt_of_numeric_of_pos (-x) (y := -y); simp_all

end Dicotic

end IGame
