/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import CombinatorialGames.Game.Special
public import CombinatorialGames.Tactic.GameCmp

/-!
# Order properties of tiny

We show that `tiny` does not have certain order properties.
-/

public section

namespace IGame

theorem tiny_not_reflect_le_pos : ∃ x y : IGame, 0 < x ∧ 0 < y ∧ ⧾x ≤ ⧾y ∧ ¬y ≤ x :=
  ⟨⧾⋆, ⧾0, by game_cmp, by game_cmp, by game_cmp, by game_cmp⟩

theorem tiny_not_preserve_lt_pos : ∃ x y : IGame, 0 < x ∧ 0 < y ∧ x < y ∧ ¬⧾y < ⧾x :=
  ⟨!{{0} | {⋆}}, !{{↑} | {⋆}}, by game_cmp, by game_cmp, by game_cmp, by game_cmp⟩

theorem tiny_not_reflect_lt_pos : ∃ x y : IGame, 0 < x ∧ 0 < y ∧ ⧾x < ⧾y ∧ ¬y < x :=
  ⟨⧾⋆, ⧾0, by game_cmp, by game_cmp, by game_cmp, by game_cmp⟩

theorem tiny_not_reflect_equiv_pos : ∃ x y : IGame, 0 < x ∧ 0 < y ∧ ⧾x ≈ ⧾y ∧ ¬x ≈ y :=
  ⟨!{{0} | {⋆}}, !{{↑} | {⋆}}, by game_cmp, by game_cmp, by game_cmp, by game_cmp⟩

end IGame
