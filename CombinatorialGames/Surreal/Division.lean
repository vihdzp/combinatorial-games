import CombinatorialGames.Surreal.Multiplication
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp

open IGame

-- TODO: upstream
theorem not_antisymmRel_of_lt {α} [Preorder α] {x y : α} (h : x < y) : ¬ AntisymmRel (· ≤ ·) x y :=
  fun h' ↦ h.not_le h'.ge

theorem not_antisymmRel_of_gt {α} [Preorder α] {x y : α} (h : y < x) : ¬ AntisymmRel (· ≤ ·) x y :=
  fun h' ↦ h.not_le h'.le

alias LT.lt.not_antisymmRel := not_antisymmRel_of_lt
alias LT.lt.not_antisymmRel_symm := not_antisymmRel_of_gt

theorem IGame.Numeric.le_or_lt (x y : IGame) [Numeric x] [Numeric y] : x ≤ y ∨ y < x := by
  rw [← Numeric.not_le]
  exact em _

theorem IGame.Numeric.lt_or_le (x y : IGame) [Numeric x] [Numeric y] : x < y ∨ y ≤ x := by
  rw [← Numeric.not_lt]
  exact em _

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

lemma mulOption_le (x y : IGame) {a b : IGame} [Numeric x] [Numeric y] [Numeric a] [Numeric b]
    (ha : a ≤ 0) (hb : b ≤ y) : mulOption x y a b ≤ x * b := by
  rw [mulOption, ← Game.mk_le_mk]
  dsimp
  have : Game.mk (a * y) - Game.mk (a * b) ≤ 0 := by
    rw [← Game.mk_mul_sub]
    apply Numeric.mul_nonpos_of_nonpos_of_nonneg ha
    rwa [IGame.sub_nonneg]
  rw [← add_le_add_iff_left (Game.mk (x * b))] at this
  convert this using 1 <;> abel

theorem le_mulOption (x y : IGame) {a b : IGame} [Numeric x] [Numeric y] [Numeric a] [Numeric b]
    (ha : a ≤ 0) (hb : y ≤ b) : x * b ≤ mulOption x y a b := by
  rw [mulOption, ← Game.mk_le_mk]
  dsimp
  have : 0 ≤ Game.mk (a * y) - Game.mk (a * b) := by
    rw [← Game.mk_mul_sub]
    apply Numeric.mul_nonneg_of_nonpos_of_nonpos ha
    rwa [IGame.sub_nonpos]
  rw [← add_le_add_iff_left (Game.mk (x * b))] at this
  convert this using 1 <;> abel

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
  exact (Numeric.mul_lt_mul_left hx).1 <| (Hl y hy).trans (Hr z hz)

lemma option_mul_inv_lt {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹)
    (hl' : ∀ y ∈ x.leftMoves, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ x.rightMoves, y * y⁻¹ ≈ 1) :
    (∀ y ∈ (x * x⁻¹).leftMoves, y < 1) ∧ (∀ y ∈ (x * x⁻¹).rightMoves, 1 < y) := by
  have := numeric_inv hx hl hr hl' hr'
  obtain ⟨Hl, Hr⟩ := numeric_option_inv hl hr
  rw [forall_leftMoves_mul, forall_rightMoves_mul]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals
    intro y hy a ha
    first | have := Numeric.of_mem_leftMoves hy | have := Numeric.of_mem_rightMoves hy
    first | have := Hl a ha | have := Hr a ha
    try (have := hr y hy; have hy' := hx.trans (Numeric.lt_rightMove hy))
  · obtain hy' | hy' := Numeric.lt_or_le 0 y
    · have := hl y hy hy'
      rw [(mulOption_self_inv x (hl' y hy hy') a).lt_congr_left, add_comm,
        ← IGame.lt_sub_iff_add_lt, (IGame.sub_self_equiv _).lt_congr_right]
      apply Numeric.mul_neg_of_neg_of_pos _ hy'
      rw [IGame.sub_neg]
      exact Numeric.lt_rightMove (invOption_left_left_mem_rightMoves_inv hy hy' ha)
    · apply (mulOption_le _ _ hy' (Numeric.leftMove_lt ha).le).trans_lt
      exact (mul_inv_option_mem hl hr hl' hr').1 a ha
  · rw [(mulOption_self_inv x (hr' y hy) a).lt_congr_left, add_comm,
      ← IGame.lt_sub_iff_add_lt, (IGame.sub_self_equiv _).lt_congr_right]
    apply Numeric.mul_neg_of_neg_of_pos _ hy'
    rw [IGame.sub_neg]
    exact Numeric.lt_rightMove (invOption_right_right_mem_rightMoves_inv hy ha)
  · obtain hy' | hy' := Numeric.lt_or_le 0 y
    · have := hl y hy hy'
      rw [(mulOption_self_inv x (hl' y hy hy') a).lt_congr_right, add_comm,
        ← IGame.sub_lt_iff_lt_add, (IGame.sub_self_equiv _).lt_congr_left]
      apply Numeric.mul_pos _ hy'
      rw [IGame.sub_pos]
      apply Numeric.leftMove_lt (invOption_left_right_mem_leftMoves_inv hy hy' ha)
    · apply ((mul_inv_option_mem hl hr hl' hr').2 a ha).trans_le
      exact le_mulOption _ _ hy' (Numeric.lt_rightMove ha).le
  · rw [(mulOption_self_inv x (hr' y hy) a).lt_congr_right, add_comm,
      ← IGame.sub_lt_iff_lt_add, (IGame.sub_self_equiv _).lt_congr_left]
    apply Numeric.mul_pos _ hy'
    rw [IGame.sub_pos]
    exact Numeric.leftMove_lt (invOption_right_left_mem_leftMoves_inv hy ha)

lemma mul_inv_self {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹)
    (hl' : ∀ y ∈ x.leftMoves, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ x.rightMoves, y * y⁻¹ ≈ 1) :
    x * x⁻¹ ≈ 1 := by
  obtain ⟨Hl, Hr⟩ := option_mul_inv_lt hx hl hr hl' hr'
  have := numeric_inv hx hl hr hl' hr'
  apply equiv_one_of_fits ⟨fun z hz ↦ (Hl z hz).not_le, fun z hz ↦ (Hr z hz).not_le⟩
  rw [Numeric.mul_equiv_zero, not_or]
  exact ⟨hx.not_antisymmRel_symm, (Numeric.inv_pos x).not_antisymmRel_symm⟩

theorem main {x : IGame} [Numeric x] (hx : 0 < x) : Numeric x⁻¹ ∧ x * x⁻¹ ≈ 1 := by
  have IHl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹ ∧ y * y⁻¹ ≈ 1 :=
    fun y hy hy' ↦ have := Numeric.of_mem_leftMoves hy; main hy'
  have IHr : ∀ y ∈ x.rightMoves, Numeric y⁻¹ ∧ y * y⁻¹ ≈ 1 :=
    fun y hy ↦ have := Numeric.of_mem_rightMoves hy; main (hx.trans (Numeric.lt_rightMove hy))
  have hl := fun y hy hy' ↦ (IHl y hy hy').1
  have hr := fun y hy ↦ (IHr y hy).1
  have hl' := fun y hy hy' ↦ (IHl y hy hy').2
  have hr' := fun y hy ↦ (IHr y hy).2
  exact ⟨numeric_inv hx hl hr hl' hr', mul_inv_self hx hl hr hl' hr'⟩
termination_by x
decreasing_by igame_wf

end Surreal.Division

namespace IGame
open Surreal.Division

theorem Numeric.inv {x : IGame} [Numeric x] (hx : 0 < x) : Numeric x⁻¹ := (main hx).1
theorem Numeric.mul_inv_cancel {x : IGame} [Numeric x] (hx : 0 < x) : x * x⁻¹ ≈ 1 := (main hx).2

end IGame

namespace Surreal


end Surreal
