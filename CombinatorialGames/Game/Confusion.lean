/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Cut

/-!
# Confusion intervals of games

For a game `x`, its confusion interval is the set of surreals that are fuzzy (or confused) with it.
We prove that this set is always order connected, and calculate some confusion intervals.
-/

/-! ### Some explicit calculations with cuts -/

namespace Surreal.Cut

@[simp, grind =] theorem supLeft_star : supLeft ⋆ = rightSurreal 0 := by simp [supLeft]
@[simp, grind =] theorem infRight_star : infRight ⋆ = leftSurreal 0 := by simp [infRight]

@[simp, grind =]
theorem leftGame_star : leftGame (.mk ⋆) = rightSurreal 0 := by
  rw [leftGame_eq_supLeft_of_le (by simp), supLeft_star]

@[simp, grind =]
theorem rightGame_star : rightGame (.mk ⋆) = leftSurreal 0 := by
  rw [rightGame_eq_infRight_of_le (by simp), infRight_star]

@[simp, grind =]
theorem supLeft_switch (x : IGame) : supLeft (±x) = rightGame (.mk x) := by
  simp [supLeft]

@[simp, grind =]
theorem infRight_switch (x : IGame) : infRight (±x) = -rightGame (.mk x) := by
  rw [← IGame.neg_switch, infRight_neg, supLeft_switch]

theorem infRight_switch_le_supLeft_switch {x : IGame} (h : 0 ≤ x) :
    infRight (±x) ≤ supLeft (±x) := by
  trans leftSurreal 0
  · simpa
  · apply le_of_lt
    simpa

theorem leftGame_switch {x : IGame} (h : 0 ≤ x) [x.Numeric] :
    leftGame (.mk (±x)) = rightSurreal (.mk x) := by
  rw [leftGame_eq_supLeft_of_le (infRight_switch_le_supLeft_switch h)]
  simp

theorem rightGame_switch {x : IGame} (h : 0 ≤ x) [x.Numeric] :
    rightGame (.mk (±x)) = -rightSurreal (.mk x) := by
  rw [rightGame_eq_infRight_of_le (infRight_switch_le_supLeft_switch h)]
  simp

end Surreal.Cut

/-! ### Confusion intervals -/

namespace Game
open Surreal Cut

/-- The confusion interval of `x` is the set of surreals `y` with `x ‖ y`. -/
def confusionInterval (x : Game) : Set Surreal :=
  (rightGame x).right ∩ (leftGame x).left

@[simp]
theorem mem_confusionInterval {x : Game} {y : Surreal} :
    y ∈ confusionInterval x ↔ y.toGame ‖ x := by
  simp [confusionInterval, IncompRel]

@[simp]
theorem confusionInterval_toGame (x : Surreal) : confusionInterval x.toGame = ∅ := by
  grind [confusionInterval]

@[simp]
theorem confusionInterval_neg (x : Game) : confusionInterval (-x) = -confusionInterval x := by
  simp [confusionInterval, Set.inter_comm]

@[simp]
theorem confusionInterval_ordinal (o : NatOrdinal) : confusionInterval o = ∅ := by
  simpa using confusionInterval_toGame o

@[simp]
theorem confusionInterval_zero : confusionInterval 0 = ∅ := by
  simpa using confusionInterval_ordinal 0

@[simp]
theorem confusionInterval_one : confusionInterval 1 = ∅ := by
  simpa using confusionInterval_ordinal 1

instance ordConnected_confusionInterval (x : Game) : x.confusionInterval.OrdConnected := by
  refine ⟨fun y hy z hz w ⟨hw, hw'⟩ ↦ ⟨?_, ?_⟩⟩
  · apply isUpperSet_right _ hw
    grind [confusionInterval]
  · apply isLowerSet_left _ hw'
    grind [confusionInterval]

@[simp]
theorem confusionInterval_star : confusionInterval (.mk ⋆) = {0} := by
  grind [confusionInterval]

@[simp]
theorem confusionInterval_switch {x : IGame} (h : 0 ≤ x) [x.Numeric] :
    confusionInterval (.mk (±x)) = Set.Icc (-Surreal.mk x) (.mk x) := by
  rw [confusionInterval, leftGame_switch h, rightGame_switch h]
  ext
  simp

-- This should be easy after #306.
proof_wanted bddAbove_confusionInterval (x : Game) : BddAbove (confusionInterval x)
proof_wanted bddBelow_confusionInterval (x : Game) : BddBelow (confusionInterval x)

proof_wanted confusionInterval_subset_zero (x : IGame) [x.Dicotic] : confusionInterval

end Game
