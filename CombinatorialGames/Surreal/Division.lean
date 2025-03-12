import CombinatorialGames.Surreal.Multiplication
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp

open IGame

noncomputable section

instance (x y : IGame) [Numeric x] [Numeric y⁻¹] : Numeric (x / y) :=
  inferInstanceAs (Numeric (_ * _))

theorem IGame.inv_pos (x : IGame) [Numeric x⁻¹] : 0 < x⁻¹ :=
  Numeric.lt_of_not_le (inv_nonneg x)

@[simp]
theorem Surreal.mk_mul (x y : IGame) [Numeric x] [Numeric y] :
    Surreal.mk (x * y) = Surreal.mk x * Surreal.mk y :=
  rfl

@[simp]
theorem Surreal.mk_div (x y : IGame) [Numeric x] [Numeric y⁻¹] :
    Surreal.mk (x / y) = Surreal.mk x * Surreal.mk y⁻¹ :=
  rfl

protected theorem IGame.sub_pos {x y : IGame} : 0 < x - y ↔ y < x :=
  sub_pos (a := Game.mk x) (b := Game.mk y)

protected theorem IGame.sub_neg {x y : IGame} : x - y < 0 ↔ x < y :=
  sub_neg (a := Game.mk x) (b := Game.mk y)

instance (x y a : IGame) [Numeric x] [Numeric y] [Numeric y⁻¹] [Numeric a] :
    Numeric (invOption x y a) :=
  inferInstanceAs (Numeric (_ / _))

protected theorem IGame.Numeric.mul_neg_of_pos_of_neg {x y : IGame} [Numeric x] [Numeric y]
    (hx : 0 < x) (hy : y < 0) : x * y < 0 := by
  exact mul_neg_of_pos_of_neg (a := Surreal.mk x) (b := Surreal.mk y) hx hy

protected theorem IGame.Numeric.mul_neg_of_neg_of_pos {x y : IGame} [Numeric x] [Numeric y]
    (hx : x < 0) (hy : 0 < y) : x * y < 0 := by
  exact mul_neg_of_neg_of_pos (a := Surreal.mk x) (b := Surreal.mk y) hx hy

protected theorem IGame.Numeric.mul_pos_of_neg_of_neg {x y : IGame} [Numeric x] [Numeric y]
    (hx : x < 0) (hy : y < 0) : 0 < x * y := by
  exact mul_pos_of_neg_of_neg (a := Surreal.mk x) (b := Surreal.mk y) hx hy

namespace Surreal.Division

theorem numeric_option_inv {x : IGame} [Numeric x]
    (hl : ∀ y ∈ x.leftMoves, Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹) :
    (∀ y ∈ x⁻¹.leftMoves, Numeric y) ∧ (∀ y ∈ x⁻¹.rightMoves, Numeric y) := by
  apply invRec x Numeric.zero
  all_goals
    intro y hy
    intros
    first |
      have := Numeric.of_mem_leftMoves hy; have := hl _ hy |
      have := Numeric.of_mem_rightMoves hy; have := hr _ hy
    infer_instance

theorem one_neg_mul_invOption (x : IGame) {y : IGame} (hy : y * y⁻¹ ≈ 1) (a : IGame)
    [Numeric x] [Numeric y] [Numeric y⁻¹] [Numeric a] :
    1 - x * invOption x y a ≈ (1 - x * a) * (y - x) / y := by
  rw [← Surreal.mk_eq_mk] at *
  dsimp [invOption] at *
  simp only [one_mul, sub_eq_add_neg, add_mul, hy]
  ring

theorem mul_inv_option_mem (x : IGame) [Numeric x]
    (hl : ∀ y ∈ x.leftMoves, Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹)
    (hl' : ∀ y ∈ x.leftMoves, y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ x.rightMoves, y * y⁻¹ ≈ 1) :
    (∀ y ∈ x⁻¹.leftMoves, x * y < 1) ∧ (∀ y ∈ x⁻¹.rightMoves, 1 < x * y) := by
  apply invRec x
  · simp
  · intro y hy a ha h
    have := Numeric.of_mem_rightMoves hy
    have := hr y hy
    have := (numeric_option_inv hl hr).1 a ha
    rw [← IGame.sub_pos, (one_neg_mul_invOption x (hr' y hy) a).lt_congr_right]
    apply Numeric.mul_pos (Numeric.mul_pos _ _) (IGame.inv_pos y)
    · rwa [IGame.sub_pos]
    · rw [IGame.sub_pos]
      exact Numeric.lt_rightMove hy
  · intro y hy hy' a ha h
    have := Numeric.of_mem_leftMoves hy
    have := hl y hy
    have := (numeric_option_inv hl hr).1 a ha
    rw [← IGame.sub_pos, (one_neg_mul_invOption x (hl' y hy) a).lt_congr_right]
    apply Numeric.mul_pos (Numeric.mul_pos_of_neg_of_neg _ _) (IGame.inv_pos y)
    · rwa [IGame.sub_neg]
    · rw [IGame.sub_neg]
      exact Numeric.leftMove_lt hy
  · intro y hy hy' a ha h
    have := Numeric.of_mem_leftMoves hy
    have := hl y hy
    have := (numeric_option_inv hl hr).1 a ha
    rw [← IGame.sub_neg, (one_neg_mul_invOption x (hl' y hy) a).lt_congr_left]
    apply Numeric.mul_neg_of_neg_of_pos (Numeric.mul_neg_of_pos_of_neg _ _) (IGame.inv_pos y)
    · rwa [IGame.sub_pos]
    · rw [IGame.sub_neg]
      exact Numeric.leftMove_lt hy
  · intro y hy a ha h
    have := Numeric.of_mem_rightMoves hy
    have := hr y hy
    have := (numeric_option_inv hl hr).1 a ha
    rw [← IGame.sub_neg, (one_neg_mul_invOption x (hr' y hy) a).lt_congr_left]
    apply Numeric.mul_neg_of_neg_of_pos (Numeric.mul_neg_of_neg_of_pos _ _) (IGame.inv_pos y)
    · rwa [IGame.sub_neg]
    · rw [IGame.sub_pos]
      exact Numeric.lt_rightMove hy

#exit
/-
theorem one_neg_mul_invOption (x : IGame) {y : IGame} (hy : Game.mk (y * y⁻¹) = 1) (a : IGame) :
    Game.mk (1 - x * invOption x y a) = Game.mk ((1 - x * a) * (y - x) / y) := by
  rw [IGame.div_eq_mul_inv, Game.mk_mul_assoc, Game.mk_sub_mul, one_mul, Game.mk_sub_mul,
    mul_comm (y - x), ← Game.mk_mul_assoc, Game.mk_mul_sub]
  rw [invOption, Game.mk_sub, Game.mk_one, IGame.div_eq_mul_inv, mul_comm, Game.mk_mul_assoc,
    Game.mk_add_mul, Game.mk_mul_assoc, Game.mk_sub_mul, one_mul]
  simp only [← Game.mk_mul_assoc, ← sub_add, ← sub_sub, hy, mul_comm]
  congr 2
  rw [Game.mk_mul_assoc, Game.mk_mul_assoc, mul_comm, Game.mk_mul_assoc]

  -- [mul_comm, Game.mk_mul_assoc]
  · rw [mul_comm]
  · sorry

  abel_nf
  congr 2
  /-simp [invOption, IGame.div_eq_mul_inv, sub_eq_add_neg,
  Game.mk_mul_assoc, Game.mk_add_mul, Game.mk_mul_add]-/
-/
#exit

private theorem numeric_inv' (x : IGame) [Numeric x] :
    (∀ y ∈ (x⁻¹).leftMoves, Numeric y) ∧ (∀ y ∈ (x⁻¹).rightMoves, Numeric y) := by
  refine invRec x ?_ ?_ ?_ ?_ ?_
  · infer_instance
  · intro y hy a ha _
    rw [invOption, IGame.div_eq_mul_inv]
    have := Numeric.of_mem_rightMoves hy
    have := numeric_inv' y
    infer_instance
  · sorry
  · sorry
  · sorry
termination_by x
decreasing_by igame_wf

#exit
private theorem mul_move_inv {x : IGame} [Numeric x] (h : 0 < x) :
    (∀ y ∈ (x⁻¹).leftMoves, x * y < 1) ∧ (∀ y ∈ (x⁻¹).rightMoves, 1 < x * y) := by
  refine invRec x ?_ ?_ ?_ ?_ ?_
  · simp
  · intro y hy a ha hxa
    rw [invOption, IGame.div_eq_mul_inv]
    sorry
  · sorry
  · sorry
  · sorry

#exit
theorem mul_leftMove_inv_lt {x y : IGame} [Numeric x] (h : 0 < x) (hy : y ∈ (x⁻¹).leftMoves) :
    x * y < 1 :=
  (mul_move_inv h).1 y hy

theorem lt_mul_rightMove_inv {x y : IGame} [Numeric x] (h : 0 < x) (hy : y ∈ (x⁻¹).rightMoves) :
    1 < x * y :=
  (mul_move_inv h).2 y hy

end IGame
end
