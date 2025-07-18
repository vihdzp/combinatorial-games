/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Ordinal
import CombinatorialGames.Game.Specific.Nim
import CombinatorialGames.Game.Tactic

/-!
Tests for the `game_cmp` tactic.
-/

open IGame Nimber

-- Basic order relations
example : (0 : IGame) < 1 := by game_cmp
example : (-3 : ℤ) ≤ (3 : IGame) := by game_cmp
example : 1 ≥ ½ := by game_cmp
example : ↑ > 0 := by game_cmp
example : ⋆ ⧏ ⧾⋆ := by game_cmp
example : {{1} | {2}}ᴵ ≈ {{0, 1} | {2, 3}}ᴵ := by game_cmp
example : ⋆ ‖ 0 := by game_cmp

-- Arithmetic
example : (2 : IGame) + 2 ≈ 4 := by game_cmp
example : (3 : IGame) - 2 ≈ 1 := by game_cmp
example : (2 : IGame) * 2 ≈ 4 := by game_cmp

-- Ordinals and nimbers
example : NatOrdinal.toIGame 3 ≈ 3 := by game_cmp
example : nim 1 + nim (∗2) ≈ nim (∗3) := by game_cmp
example : nim 2 ≈ nim 0 := by game_cmp -- Be careful, `↑2` is not the same as `∗2`.
