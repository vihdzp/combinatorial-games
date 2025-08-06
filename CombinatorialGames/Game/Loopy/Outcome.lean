import CombinatorialGames.Game.Loopy.Basic
import CombinatorialGames.Game.IGame

namespace LGame

/-- A surviving strategy for Left, going second.

This is a set of states containing `x`, such that for every move Right makes, Left can bring it back
to the set. -/
def LeftStrategy (x : LGame) (s : Set LGame) : Prop :=
  x ∈ s ∧ ∀ y ∈ s, ∀ z ∈ y.rightMoves, ∃ r ∈ z.leftMoves, r ∈ s

/-- A surviving strategy for Right, going second.

This is a set of states containing `x`, such that for every move Left makes, Right can bring it back
to the set. -/
def RightStrategy (x : LGame) (s : Set LGame) : Prop :=
  x ∈ s ∧ ∀ y ∈ s, ∀ z ∈ y.leftMoves, ∃ r ∈ z.rightMoves, r ∈ s

private theorem left_or_right_survive_left (x : LGame) :
    (∃ y ∈ x.leftMoves, ∃ s, LeftStrategy y s) ∨ ∃ s, RightStrategy x s := by
  sorry

end LGame
