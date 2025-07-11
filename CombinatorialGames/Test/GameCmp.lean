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

open Nimber

example : (0 : IGame) < 1 := by game_cmp
example : (2 : IGame) + 2 ≈ 4 := by game_cmp
example : (3 : IGame) - 2 ≈ 1 := by game_cmp
example : {{1} | {2}}ᴵ ≈ {{0, 1} | {2, 3}}ᴵ := by game_cmp
example : (2 : IGame) * 2 ≈ 4 := by game_cmp
example : NatOrdinal.toIGame 3 ≈ 3 := by game_cmp
example : IGame.nim 1 + IGame.nim (∗2) ≈ IGame.nim (∗3) := by game_cmp
