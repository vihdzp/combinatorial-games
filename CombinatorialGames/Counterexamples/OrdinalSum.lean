/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Game.OrdinalSum

import CombinatorialGames.Tactic.GameCmp

/-!
# Ordinal sum does not respect equivalence on the left

The theorem `IGame.ordinalSum_right_congr` tells us that if `b₁ ≈ b₂`, then `a ∶ b₁ ≈ a ∶ b₂` for
any game `a`. We show that this does not hold for the left argument by providing an explicit
counterexample. If `a₁ = {-1 | 1}`, `a₂ = 0`, and `b = 1`, then `a₁ ≈ a₂` but `a₁ ∶ b ≉ a₂ ∶ b`. (In
fact, the LHS is equivalent to `½`, while the RHS is equivalent to `1`).
-/

public section
namespace IGame

theorem not_ordinalSum_congr_left : ∃ a₁ a₂ b : IGame, a₁ ≈ a₂ ∧ ¬ a₁ ∶ b ≈ a₂ ∶ b :=
  ⟨!{{-1} | {1}}, 0, 1, by game_cmp, by game_cmp⟩

end IGame
end
