import CombinatorialGames.Game.Ordinal
import CombinatorialGames.Tactic



section Test

example : (0 : IGame) < 1 := by game_cmp
example : (2 : IGame) + 2 ≈ 4 := by game_cmp
example : (3 : IGame) - 2 ≈ 1 := by game_cmp
example : {{1} | {2}}ᴵ ≈ {{0, 1} | {2, 3}}ᴵ := by game_cmp
example : (2 : IGame) * 2 ≈ 4 := by game_cmp

end Test
