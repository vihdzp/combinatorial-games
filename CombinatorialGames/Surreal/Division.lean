import CombinatorialGames.Surreal.Multiplication
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp

open IGame

namespace Surreal.Division

lemma one_neg_mul_invOption (x : IGame) {y : IGame} (hy : y * y⁻¹ ≈ 1) (a : IGame)
    [Numeric x] [Numeric y] [Numeric y⁻¹] [Numeric a] :
    1 - x * invOption x y a ≈ (1 - x * a) * (y - x) / y := by
  rw [← Surreal.mk_eq_mk] at *
  dsimp [invOption, mk_div'] at *
  simp only [one_mul, sub_eq_add_neg, add_mul, hy]
  ring

lemma mulOption_self_inv (x : IGame) {y : IGame} (hy : y * y⁻¹ ≈ 1) (a : IGame)
    [Numeric x] [Numeric x⁻¹] [Numeric y] [Numeric y⁻¹] [Numeric a] :
    mulOption x x⁻¹ y a ≈ 1 + (x⁻¹ - invOption x y a) * y := by
  rw [mul_comm] at hy
  rw [← Surreal.mk_eq_mk] at *
  dsimp [mulOption, invOption, mk_div'] at *
  simp only [sub_eq_add_neg, add_mul, neg_mul, mul_assoc, hy]
  ring

lemma numeric_option_inv {x : IGame} [Numeric x]
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹) :
    (∀ y ∈ x⁻¹.leftMoves, Numeric y) ∧ (∀ y ∈ x⁻¹.rightMoves, Numeric y) := by
  apply invRec x Numeric.zero
  all_goals
    intro y hy hy'
    intros
    first |
      have := Numeric.of_mem_leftMoves hy; have := hl _ hy hy' |
      have := Numeric.of_mem_rightMoves hy; have := hr _ hy
    infer_instance

lemma mul_inv_option_mem {x : IGame} [Numeric x]
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹)
    (hl' : ∀ y ∈ x.leftMoves, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ x.rightMoves, y * y⁻¹ ≈ 1) :
    (∀ y ∈ x⁻¹.leftMoves, x * y < 1) ∧ (∀ y ∈ x⁻¹.rightMoves, 1 < x * y) := by
  apply invRec x
  · simp
  · intro y hy a ha h
    have := Numeric.of_mem_rightMoves hy
    have := hr y hy
    have := (numeric_option_inv hl hr).1 a ha
    rw [← IGame.sub_pos, (one_neg_mul_invOption x (hr' y hy) a).lt_congr_right]
    apply Numeric.mul_pos (Numeric.mul_pos _ _) (Numeric.inv_pos y)
    · rwa [IGame.sub_pos]
    · rw [IGame.sub_pos]
      exact Numeric.lt_rightMove hy
  · intro y hy hy' a ha h
    have := Numeric.of_mem_leftMoves hy
    have := hl y hy hy'
    have := (numeric_option_inv hl hr).2 a ha
    rw [← IGame.sub_pos, (one_neg_mul_invOption x (hl' y hy hy') a).lt_congr_right]
    apply Numeric.mul_pos (Numeric.mul_pos_of_neg_of_neg _ _) (Numeric.inv_pos y)
    · rwa [IGame.sub_neg]
    · rw [IGame.sub_neg]
      exact Numeric.leftMove_lt hy
  · intro y hy hy' a ha h
    have := Numeric.of_mem_leftMoves hy
    have := hl y hy hy'
    have := (numeric_option_inv hl hr).1 a ha
    rw [← IGame.sub_neg, (one_neg_mul_invOption x (hl' y hy hy') a).lt_congr_left]
    apply Numeric.mul_neg_of_neg_of_pos (Numeric.mul_neg_of_pos_of_neg _ _) (Numeric.inv_pos y)
    · rwa [IGame.sub_pos]
    · rw [IGame.sub_neg]
      exact Numeric.leftMove_lt hy
  · intro y hy a ha h
    have := Numeric.of_mem_rightMoves hy
    have := hr y hy
    have := (numeric_option_inv hl hr).2 a ha
    rw [← IGame.sub_neg, (one_neg_mul_invOption x (hr' y hy) a).lt_congr_left]
    apply Numeric.mul_neg_of_neg_of_pos (Numeric.mul_neg_of_neg_of_pos _ _) (Numeric.inv_pos y)
    · rwa [IGame.sub_neg]
    · rw [IGame.sub_pos]
      exact Numeric.lt_rightMove hy

lemma numeric_inv {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹)
    (hl' : ∀ y ∈ x.leftMoves, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ x.rightMoves, y * y⁻¹ ≈ 1) :
    Numeric x⁻¹ := by
  obtain ⟨Hl, Hr⟩ := mul_inv_option_mem hl hr hl' hr'
  obtain ⟨Hl', Hr'⟩ := numeric_option_inv hl hr
  refine Numeric.mk' (fun y hy z hz ↦ ?_) Hl' Hr'
  have := Hl' y hy
  have := Hr' z hz
  have := (Hl y hy).trans (Hr z hz)
  rwa [Numeric.mul_lt_mul_left hx] at this

#exit
theorem main {x : IGame} [Numeric x] (hx : 0 < x) : Numeric x⁻¹ ∧ x * x⁻¹ ≈ 1 := by
  have IHl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹ ∧ y * y⁻¹ ≈ 1 :=
    fun y hy hy' ↦ have := Numeric.of_mem_leftMoves hy; main hy'
  have IHr : ∀ y ∈ x.rightMoves, Numeric y⁻¹ ∧ y * y⁻¹ ≈ 1 :=
    fun y hy ↦ have := Numeric.of_mem_rightMoves hy; main (hx.trans (Numeric.lt_rightMove hy))
  sorry
termination_by x
decreasing_by igame_wf

end Surreal.Division

namespace IGame
open Surreal.Division

theorem Numeric.inv {x : IGame} [Numeric x] (hx : 0 < x) : Numeric x⁻¹ :=
  (main hx).1

theorem Numeric.mul_inv_cancel {x : IGame} [Numeric x] (hx : 0 < x) : x * x⁻¹ ≈ 1 :=
  (main hx).2

end IGame

namespace Surreal


end Surreal
