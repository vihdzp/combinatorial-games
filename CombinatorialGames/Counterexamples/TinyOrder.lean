/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import CombinatorialGames.Game.Special
public import CombinatorialGames.Game.Specific.Nim
public import CombinatorialGames.Tactic.GameCmp

/-!
# Order properties of tiny

We show that `tiny` does not have certain order properties.
-/

public section

namespace IGame

theorem exists_pos_fuzzy_tiny_lt : ∃ x y : IGame, 0 < x ∧ 0 < y ∧ x ‖ y ∧ ⧾x < ⧾y :=
  ⟨⧾⋆, ⧾0, by game_cmp, by game_cmp, by game_cmp, by game_cmp⟩

theorem exists_pos_fuzzy_tiny_equiv : ∃ x y : IGame, 0 < x ∧ 0 < y ∧ x ‖ y ∧ ⧾x ≈ ⧾y :=
  ⟨!{{0} | {nim (.of 2)}}, !{{0} | {nim (.of 3)}},
    by game_cmp, by game_cmp, by game_cmp, by game_cmp⟩

theorem exists_pos_fuzzy_tiny_fuzzy : ∃ x y : IGame, 0 < x ∧ 0 < y ∧ x ‖ y ∧ ⧾x ‖ ⧾y :=
  ⟨⧾↓, ⧾↓ + ⋆, by game_cmp, by game_cmp, by game_cmp, by game_cmp⟩

theorem exists_pos_lt_tiny_gt : ∃ x y : IGame, 0 < x ∧ 0 < y ∧ x < y ∧ ⧾y < ⧾x :=
  ⟨↑, ↑ + ↑, by game_cmp, by game_cmp, by game_cmp, by game_cmp⟩

theorem exists_pos_lt_tiny_equiv : ∃ x y : IGame, 0 < x ∧ 0 < y ∧ x < y ∧ ⧾x ≈ ⧾y :=
  ⟨!{{0} | {⋆}}, !{{↑} | {⋆}}, by game_cmp, by game_cmp, by game_cmp, by game_cmp⟩

end IGame
