/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
module

public import CombinatorialGames.Game.Impartial.Grundy

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

public section

namespace IGame
namespace Dicotic

/--
One half of the **lawnmower theorem**: any dicotic game is smaller than any positive numeric game.
-/
theorem lt_of_numeric_of_pos (x) [Dicotic x] {y} [Numeric y] (hy : 0 < y) : x < y := by
  rw [lt_iff_le_not_ge, le_iff_forall_lf]
  refine ⟨⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩, ?_⟩
  · dicotic
    exact (lt_of_numeric_of_pos z hy).not_ge
  · numeric
    obtain (h | h) := Numeric.le_or_gt z 0
    · cases ((Numeric.lt_right hz).trans_le h).not_gt hy
    · exact (lt_of_numeric_of_pos x h).not_ge
  · obtain rfl | h := eq_or_ne x 0
    · exact hy.not_ge
    · simp_rw [ne_zero_iff, ← Set.nonempty_iff_ne_empty] at h
      obtain ⟨z, hz⟩ := h right
      dicotic
      exact lf_of_right_le (lt_of_numeric_of_pos z hy).le hz
termination_by (x, y)
decreasing_by igame_wf

/--
One half of the **lawnmower theorem**: any dicotic game is greater than any negative numeric game.
-/
theorem lt_of_numeric_of_neg (x) [Dicotic x] {y} [Numeric y] (hy : y < 0) : y < x := by
  have := lt_of_numeric_of_pos (-x) (y := -y); simp_all

end Dicotic

namespace Impartial

/-- One half of the **lawnmower theorem** for impartial games. -/
protected theorem lt_of_numeric_of_pos (x) [Impartial x] {y} [Numeric y] (hy : 0 < y) : x < y := by
  grw [← nim_grundy_equiv x]
  exact Dicotic.lt_of_numeric_of_pos _ hy

/-- One half of the **lawnmower theorem** for impartial games. -/
protected theorem lt_of_numeric_of_neg (x) [Impartial x] {y} [Numeric y] (hy : y < 0) : y < x := by
  grw [← nim_grundy_equiv x]
  exact Dicotic.lt_of_numeric_of_neg _ hy

end Impartial
end IGame
end
