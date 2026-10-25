/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Surreal.Cut

/-!
# Confusion intervals of games

For a game `x`, its confusion interval is the set of surreals that are fuzzy (or confused) with it.
We prove that this set is always order connected, and calculate some explicit confusion intervals.
-/

public section

namespace Game
open Surreal Cut

/-- The confusion interval of `x` is the set of surreals `y` with `x ‖ y`. -/
def confusionInterval (x : Game) : Set Surreal :=
  (rightGame x).right ∩ (leftGame x).left

theorem confusionInterval_def (x : Game) :
    confusionInterval x = (rightGame x).right ∩ (leftGame x).left :=
  (rfl)

@[simp]
theorem mem_confusionInterval {x : Game} {y : Surreal} :
    y ∈ confusionInterval x ↔ y.toGame ‖ x := by
  simp [confusionInterval, IncompRel]

theorem ordConnected_confusionInterval (x : Game) : x.confusionInterval.OrdConnected :=
  (isUpperSet_right _).ordConnected.inter (isLowerSet_left _).ordConnected

theorem bddAbove_confusionInterval (x : Game) : BddAbove (confusionInterval x) := by
  refine ⟨x.birthday, fun y hy ↦ ?_⟩
  contrapose! hy
  rw [mem_confusionInterval, incompRel_comm]
  exact (x.le_toGame_birthday.trans_lt <| toGame.strictMono hy).not_incompRel

theorem bddBelow_confusionInterval (x : Game) : BddBelow (confusionInterval x) := by
  refine ⟨-x.birthday, fun y hy ↦ ?_⟩
  contrapose! hy
  rw [mem_confusionInterval]
  exact ((toGame.strictMono hy).trans_le x.neg_toGame_birthday_le).not_incompRel

@[simp]
theorem confusionInterval_toGame (x : Surreal) : confusionInterval x.toGame = ∅ := by
  grind [confusionInterval]

@[simp]
theorem confusionInterval_mk_of_numeric (x : IGame) [x.Numeric] : confusionInterval (.mk x) = ∅ :=
  confusionInterval_toGame (.mk x)

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

@[simp]
theorem confusionInterval_star : confusionInterval (.mk ⋆) = {0} := by
  grind [confusionInterval]

@[simp]
theorem confusionInterval_up : confusionInterval (.mk ↑) = ∅ := by
  grind [confusionInterval]

@[simp]
theorem confusionInterval_down : confusionInterval (.mk ↓) = ∅ := by
  grind [confusionInterval]

@[simp]
theorem confusionInterval_switch_of_numeric {x : IGame} (h : 0 ≤ x) [x.Numeric] :
    confusionInterval (.mk (±x)) = Set.Icc (-Surreal.mk x) (.mk x) := by
  rw [confusionInterval, leftGame_switch_of_numeric h, rightGame_switch_of_numeric h]
  ext
  simp

end Game
end
