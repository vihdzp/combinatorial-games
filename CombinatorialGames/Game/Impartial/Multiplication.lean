/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Game.Impartial.Grundy
public import CombinatorialGames.Nimber.Field

/-!
# Multiplication of impartial games

We prove here that the product of impartial games is impartial, and that its Grundy value equals the
product of the Grundy values of its factors. This implies that game multiplication is algebraically
well-behaved on impartial games, i.e. it respects equivalence, and there are no zero divisors.
-/

open Nimber

public section

namespace IGame.Impartial

private theorem mul' (x y : IGame) [Impartial x] [Impartial y] :
    Impartial (x * y) ∧ grundyAux right (x * y) = grundyAux right x * grundyAux right y := by
  have h (p) : grundyAux p (x * y) = grundyAux p x * grundyAux p y := by
    apply le_antisymm
    · apply grundyAux_le_of_notMem
      intro ⟨z, hz, hz'⟩
      rw [moves_mul] at hz
      obtain ⟨⟨a, b⟩, ⟨ha, hb⟩ | ⟨ha, hb⟩, rfl⟩ := hz
      all_goals
        impartial
        have := (mul' a y).1; have := (mul' x b).1; have := (mul' a b).1
        simp_rw [mulOption, grundyAux_sub, grundyAux_add, grundyAux_eq_grundy,
          ← grundyAux_eq_grundy right] at hz'
        repeat rw [(mul' ..).2] at hz'
        simp_rw [grundyAux_eq_grundy right] at hz'
        apply mul_ne_of_ne _ _ hz' <;> solve_by_elim [grundy_moves_ne]
    · rw [le_grundyAux_iff]
      intro a h
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_of_lt_mul h
      rw [grundyAux_eq_grundy, ← grundyAux_eq_grundy left] at ha
      obtain ⟨a, ha', rfl⟩ := mem_grundyAux_image_of_lt ha
      obtain ⟨b, hb', rfl⟩ := mem_grundyAux_image_of_lt hb
      refine ⟨_, mulOption_mem_moves_mul ha' hb', ?_⟩
      impartial
      have := (mul' a y).1; have := (mul' x b).1; have := (mul' a b).1
      simp_rw [mulOption, grundyAux_sub, grundyAux_add, grundyAux_eq_grundy,
        ← grundyAux_eq_grundy right]
      repeat rw [(mul' ..).2]
  simp_rw [grundyAux_eq_grundy] at h
  refine ⟨of_grundyAux_left_eq_grundyAux_right ?_ ((h left).trans (h right).symm), ?_⟩
  · intro p
    simp only [forall_moves_mul, mulOption]
    intro p' a ha b hb
    impartial
    have := (mul' a y).1; have := (mul' x b).1; have := (mul' a b).1
    infer_instance
  · simpa [grundyAux_eq_grundy] using h right
termination_by (x, y)
decreasing_by igame_wf

protected instance mul (x y : IGame) [Impartial x] [Impartial y] : Impartial (x * y) :=
  (mul' x y).1

variable {x y x₁ x₂ y₁ y₂ : IGame} [Impartial x] [Impartial y]
  [Impartial x₁] [Impartial x₂] [Impartial y₁] [Impartial y₂]

@[simp]
theorem grundy_mul (x y : IGame) [Impartial x] [Impartial y] :
    grundy (x * y) = grundy x * grundy y := by
  simp_rw [← grundyAux_eq_grundy right]
  exact (Impartial.mul' x y).2

theorem _root_.IGame.nim_mul_equiv (a b : Nimber) : nim a * nim b ≈ nim (a * b) := by
  conv_rhs => rw [← grundy_nim a, ← grundy_nim b, ← grundy_mul]
  exact (nim_grundy_equiv _).symm

theorem mul_equiv_zero : x * y ≈ 0 ↔ x ≈ 0 ∨ y ≈ 0 := by
  rw [← grundy_eq_zero_iff, grundy_mul, mul_eq_zero, grundy_eq_zero_iff, grundy_eq_zero_iff]

protected instance mulOption (x y a b : IGame)
    [Impartial x] [Impartial y] [Impartial a] [Impartial b] :
    Impartial (mulOption x y a b) :=
  .sub ..

theorem mul_congr_left (he : x₁ ≈ x₂) : x₁ * y ≈ x₂ * y := by
  rw [← Game.mk_eq_mk, ← sub_eq_zero] at he ⊢
  rw [← Game.mk_sub_mul]
  exact Game.mk_eq (mul_equiv_zero.2 <| .inl (Game.mk_eq_mk.1 he))

theorem mul_congr_right (he : y₁ ≈ y₂) : x * y₁ ≈ x * y₂ := by
  rw [mul_comm, mul_comm x]; exact mul_congr_left he

theorem mul_congr (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ * y₁ ≈ x₂ * y₂ :=
  (mul_congr_left hx).trans (mul_congr_right hy)

end IGame.Impartial
end
