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

@[simp]
theorem leftStrategy_neg {x : LGame} {s : Set LGame} :
    LeftStrategy (-x) (-s) ↔ RightStrategy x s := by
  simp [LeftStrategy, RightStrategy]

@[simp]
theorem rightStrategy_neg {x : LGame} {s : Set LGame} :
    RightStrategy (-x) (-s) ↔ LeftStrategy x s := by
  simp_rw [← leftStrategy_neg, neg_neg]

theorem exists_leftStrategy_iff_forall {x : LGame} :
    (∃ s, LeftStrategy x s) ↔ ∀ y ∈ x.rightMoves, ∃ z ∈ y.leftMoves, ∃ s, LeftStrategy z s := by
  sorry

theorem exists_rightStrategy_iff_forall {x : LGame} :
    (∃ s, RightStrategy x s) ↔ ∀ y ∈ x.leftMoves, ∃ z ∈ y.rightMoves, ∃ s, RightStrategy z s := by
  have H {x} : (∃ s, LeftStrategy x (-s)) ↔ ∃ s, LeftStrategy x s := by
    rw [← (Equiv.neg _).exists_congr_right]; simp
  simp_rw [← leftStrategy_neg]
  rw [H, exists_leftStrategy_iff_forall]
  simp [← H]

private theorem left_or_right_survive_left (x : LGame) :
    (∃ y ∈ x.leftMoves, ∃ s, LeftStrategy y s) ∨ ∃ s, RightStrategy x s := by
  sorry

end LGame
