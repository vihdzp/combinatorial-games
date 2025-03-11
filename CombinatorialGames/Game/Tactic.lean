/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.IGame

/-!
# Tactic for game inequalities

This file defines the `game_cmp` tactic, capable of proving inequalities between games. See its
docstring for more info.

Tests for the tactic are found in the `CombinatorialGames.Test` file.
-/

/-- Proves simple inequalities on concrete games.

This tactic works by repeatedly unfolding the definition of `≤` and applying `simp` lemmas tagged
with `game_cmp` until the goal is solved. It is effective on any game whose moves can be
"enumerated" by `simp`, in the sense that a quantifier over its moves can be written in a
quantifier-less way. For instance, `∀ y ∈ leftMoves {{0, 1} | {2, 3}}ᴵ, P y` can be simplified into
`P 0 ∧ P 1`.

## Which lemmas to tag

Lemmas which are safe to tag with `game_cmp` are the following:

* Lemmas of the form `(∀ y ∈ leftMoves (f x), P y) ↔ _` and analogous, as long as any quantifiers
  in the simplified form are over left or right moves of simpler games.
* Lemmas of the form `leftMoves (f x) = _` and analogous, as long as the simplified set is of the
  form `{x₁, x₂, …}`, listing out all elements explicitly.
* Lemmas which replace games by other simpler games.

Tagging any other lemmas might lead to `simp` getting stuck in a goal that it can't solve.
-/
macro "game_cmp" : tactic =>
  `(tactic| {
    try simp only [lt_iff_le_not_le, AntisymmRel, CompRel, IncompRel]
    repeat
      rw [IGame.le_iff_forall_lf]
      simp only [game_cmp]})

section Extra
variable {α : Type*} {P : α → Prop}

attribute [game_cmp] Set.forall_mem_empty
@[game_cmp] theorem Set.exists_mem_empty : (∃ x ∈ (∅ : Set α), P x) ↔ False := by simp

@[game_cmp] theorem Set.forall_singleton {x : α} : (∀ y ∈ ({x} : Set α), P y) ↔ P x := by simp
@[game_cmp] theorem Set.exists_singleton {x : α} : (∃ y ∈ ({x} : Set α), P y) ↔ P x := by simp

@[game_cmp]
theorem Set.forall_insert {x : α} {y : Set α} :
    (∀ z ∈ insert x y, P z) ↔ P x ∧ (∀ z ∈ y, P z) := by
  simp

@[game_cmp]
theorem Set.exists_insert {x : α} {y : Set α} :
    (∃ z ∈ insert x y, P z) ↔ P x ∨ (∃ z ∈ y, P z) := by
  simp

attribute [game_cmp] le_rfl
  zero_add add_zero zero_mul mul_zero one_mul mul_one sub_eq_add_neg
  Nat.cast_zero Nat.cast_one
  not_not not_true not_false_eq_true not_forall true_and and_true false_and and_false

end Extra
