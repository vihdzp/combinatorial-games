import CombinatorialGames.Surreal.Multiplication
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp

noncomputable section

namespace IGame

private theorem mul_move_inv {x y z : IGame} [Numeric x] (h : 0 < x) :
    (∀ y ∈ (x⁻¹).leftMoves, x * y < 1) ∧ (∀ y ∈ (x⁻¹).rightMoves, 1 < x * z) :=
  refine invRec ?_

theorem mul_leftMove_inv_lt {x y : IGame} [Numeric x] (h : 0 < x) (hy : y ∈ (x⁻¹).leftMoves) :
    x * y < 1 :=
  (mul_move_inv h).1 y hy

theorem lt_mul_rightMove_inv {x y : IGame} [Numeric x] (h : 0 < x) (hy : y ∈ (x⁻¹).rightMoves) :
    1 < x * y :=
  (mul_move_inv h).2 y hy

end
