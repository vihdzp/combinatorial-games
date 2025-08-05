import CombinatorialGames.Game.IGame
import CombinatorialGames.Game.Loopy.Basic

/-!
# Well-founded games to loopy games

We define the embedding `IGame ↪ LGame`, and prove that it behaves in the expected ways with
arithmetic.
-/

namespace IGame

private def toLGame' (x : IGame) : LGame :=
  {range fun y : x.leftMoves ↦ toLGame' y | range fun y : x.rightMoves ↦ toLGame' y}ᴸ
termination_by x
decreasing_by igame_wf



end IGame
