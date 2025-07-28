/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Specific.Nim
import CombinatorialGames.Mathlib.Neg
import CombinatorialGames.Nimber.Field

/-!
# Grundy value

The Grundy value of an impartial game is recursively defined as the least nimber not among the
Grundy values of either its left or right options. This map respects addition and multiplication.

We provide three definitions for the Grundy value. `leftGrundy` and `rightGrundy` are computed using
the left/right options of the game respectively, and are defined for all games. To make the API
symmetric, we also provide `Impartial.grundy`, which enforces that the game is impartial, and is
thus equal to either of `leftGrundy` or `rightGrundy`.

The **Sprague-Grundy** theorem `nim_grundy_equiv` shows that any impartial game is equivalent to a
game of Nim, namely that corresponding to its Grundy value.
-/

universe u

open Nimber Set

noncomputable section

namespace IGame

/-! ### Grundy value -/

/-- The left Grundy value of a game is recursively defined as the minimum excluded value
(the infimum of the complement) of the left Grundy values of its left options.

This is an auxiliary definition for reasoning about games not yet known to be impartial. Use
`Impartial.grundy` for an impartial game. -/
def leftGrundy (x : IGame.{u}) : Nimber.{u} :=
  sInf (Set.range fun y : x.leftMoves ↦ leftGrundy y.1)ᶜ
termination_by x
decreasing_by igame_wf

theorem leftGrundy_def (x : IGame) : leftGrundy x = sInf (leftGrundy '' x.leftMoves)ᶜ := by
  rw [leftGrundy, image_eq_range]

theorem le_leftGrundy_iff {x : IGame} {o : Nimber} :
    o ≤ leftGrundy x ↔ Iio o ⊆ leftGrundy '' x.leftMoves := by
  rw [leftGrundy_def, le_csInf_iff'']
  · rw [← compl_subset_compl (t := Iio o), subset_def]
    simp
  · exact nonempty_of_not_bddAbove (Nimber.not_bddAbove_compl_of_small _)

theorem lt_leftGrundy_iff {x : IGame} {o : Nimber} :
    o < leftGrundy x ↔ Iic o ⊆ leftGrundy '' x.leftMoves := by
  simpa using le_leftGrundy_iff (o := Order.succ o)

theorem mem_leftGrundy_image_of_lt {x : IGame} {o : Nimber} (h : o < leftGrundy x) :
    o ∈ leftGrundy '' x.leftMoves :=
  le_leftGrundy_iff.1 le_rfl h

theorem leftGrundy_le_of_notMem {x : IGame} {o : Nimber} (h : o ∉ leftGrundy '' x.leftMoves) :
    leftGrundy x ≤ o :=
  le_of_not_gt <| mt mem_leftGrundy_image_of_lt h

theorem leftGrundy_ne {x y : IGame} (hy : y ∈ x.leftMoves) : leftGrundy y ≠ leftGrundy x := by
  conv_rhs => rw [leftGrundy_def]
  have := csInf_mem (nonempty_of_not_bddAbove <|
    Nimber.not_bddAbove_compl_of_small (leftGrundy '' x.leftMoves))
  simp_all

@[simp]
theorem leftGrundy_add (x y : IGame) : (x + y).leftGrundy = x.leftGrundy + y.leftGrundy := by
  apply le_antisymm
  · apply leftGrundy_le_of_notMem
    rw [leftMoves_add]
    rintro ⟨_, (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩), ha'⟩
    · rw [leftGrundy_add, add_left_inj] at ha'
      exact leftGrundy_ne ha ha'
    · rw [leftGrundy_add, add_right_inj] at ha'
      exact leftGrundy_ne ha ha'
  · rw [le_leftGrundy_iff]
    intro a ha
    obtain ha | ha := Nimber.lt_add_cases ha
    · obtain ⟨z, hz, hz'⟩  := mem_leftGrundy_image_of_lt ha
      refine ⟨_, add_right_mem_leftMoves_add hz y, ?_⟩
      rw [leftGrundy_add, hz', add_cancel_right]
    · obtain ⟨z, hz, hz'⟩  := mem_leftGrundy_image_of_lt ha
      refine ⟨_, add_left_mem_leftMoves_add hz x, ?_⟩
      rw [leftGrundy_add, hz', add_comm, add_cancel_right]
termination_by (x, y)
decreasing_by igame_wf

/-- The right Grundy value of a game is recursively defined as the minimum excluded value
(the infimum of the complement) of the right Grundy values of its right options.

This is an auxiliary definition for reasoning about games not yet known to be impartial. Use
`Impartial.grundy` for an impartial game. -/
def rightGrundy (x : IGame.{u}) : Nimber.{u} :=
  sInf (Set.range fun y : x.rightMoves ↦ rightGrundy y.1)ᶜ
termination_by x
decreasing_by igame_wf

theorem rightGrundy_def (x : IGame) : rightGrundy x = sInf (rightGrundy '' x.rightMoves)ᶜ := by
  rw [rightGrundy, image_eq_range]

@[simp]
theorem leftGrundy_neg (x : IGame) : leftGrundy (-x) = rightGrundy x := by
  rw [leftGrundy_def, rightGrundy_def, leftMoves_neg]
  congr
  exact image_neg_of_apply_neg_eq fun _ _ ↦ leftGrundy_neg _
termination_by x
decreasing_by igame_wf

@[simp]
theorem rightGrundy_neg (x : IGame) : rightGrundy (-x) = leftGrundy x := by
  rw [← leftGrundy_neg, neg_neg]

@[simp]
theorem leftGrundy_image_neg (s : Set IGame) : leftGrundy '' (-s) = rightGrundy '' s :=
  image_neg_of_apply_neg_eq fun _ _ ↦ leftGrundy_neg _

@[simp]
theorem rightGrundy_image_neg (s : Set IGame) : rightGrundy '' (-s) = leftGrundy '' s :=
  image_neg_of_apply_neg_eq fun _ _ ↦ rightGrundy_neg _

theorem le_rightGrundy_iff {x : IGame} {o : Nimber} :
    o ≤ rightGrundy x ↔ Iio o ⊆ rightGrundy '' x.rightMoves := by
  simpa using @le_leftGrundy_iff (-x) o

theorem lt_rightGrundy_iff {x : IGame} {o : Nimber} :
    o < rightGrundy x ↔ Iic o ⊆ rightGrundy '' x.rightMoves := by
  simpa using le_rightGrundy_iff (o := Order.succ o)

theorem mem_rightGrundy_image_of_lt {x : IGame} {o : Nimber} (h : o < rightGrundy x) :
    o ∈ rightGrundy '' x.rightMoves :=
  le_rightGrundy_iff.1 le_rfl h

theorem rightGrundy_le_of_notMem {x : IGame} {o : Nimber} (h : o ∉ rightGrundy '' x.rightMoves) :
    rightGrundy x ≤ o :=
  le_of_not_gt <| mt mem_rightGrundy_image_of_lt h

theorem rightGrundy_ne {x y : IGame} : y ∈ x.rightMoves → rightGrundy y ≠ rightGrundy x := by
  simpa using @leftGrundy_ne (-x) (-y)

@[simp]
theorem rightGrundy_add (x y : IGame) : (x + y).rightGrundy = x.rightGrundy + y.rightGrundy := by
  rw [← leftGrundy_neg, neg_add, leftGrundy_add, leftGrundy_neg, leftGrundy_neg]

@[simp]
theorem leftGrundy_sub (x y : IGame) : (x - y).leftGrundy = x.leftGrundy + y.rightGrundy := by
  rw [sub_eq_add_neg, leftGrundy_add, leftGrundy_neg]

@[simp]
theorem rightGrundy_sub (x y : IGame) : (x - y).rightGrundy = x.rightGrundy + y.leftGrundy := by
  rw [sub_eq_add_neg, rightGrundy_add, rightGrundy_neg]

namespace Impartial

/-- The Grundy value of an impartial game is recursively defined as the minimum excluded value
(the infimum of the complement) of the Grundy values of its options.

This definition enforces that `x` is impartial. If you want to talk about the left or right Grundy
values of a game (e.g. if you don't yet know it to be impartial), use `leftGrundy` or `rightGrundy`.
The lemmas `leftGrundy_eq_grundy` and `rightGrundy_eq_grundy` show that both definitions match in
the case of an impartial game. -/
def grundy (x : IGame) [Impartial x] : Nimber :=
  x.rightGrundy

/-- The **Sprague-Grundy theorem** states that every impartial game is equivalent to a game of nim,
namely the game of nim for the game's Grundy value. -/
theorem nim_grundy_equiv (x : IGame) [Impartial x] : nim (grundy x) ≈ x := by
  rw [equiv_iff_forall_fuzzy]
  constructor <;> intro y hy
  · rw [leftMoves_nim] at hy
    obtain ⟨o, ho, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := mem_rightGrundy_image_of_lt ho
    have := Impartial.of_mem_rightMoves hz
    rw [← grundy, (nim_grundy_equiv _).incompRel_congr_left]
    exact rightMove_fuzzy hz
  · have := Impartial.of_mem_rightMoves hy
    rw [← (nim_grundy_equiv _).incompRel_congr_right, nim_fuzzy_iff]
    exact (rightGrundy_ne hy).symm
termination_by x
decreasing_by igame_wf

theorem grundy_eq_iff_equiv_nim {x : IGame} [Impartial x] {o : Nimber} :
    grundy x = o ↔ x ≈ nim o := by
  rw [← (nim_grundy_equiv x).antisymmRel_congr_left, nim_equiv_iff]

alias ⟨_, grundy_eq⟩ := grundy_eq_iff_equiv_nim

theorem grundy_eq_zero_iff {x : IGame} [Impartial x] : grundy x = 0 ↔ x ≈ 0 := by
  simpa using grundy_eq_iff_equiv_nim (o := 0)

@[simp]
theorem grundy_eq_iff_equiv {x y : IGame} [Impartial x] [Impartial y] :
    grundy x = grundy y ↔ x ≈ y := by
  rw [grundy_eq_iff_equiv_nim, (nim_grundy_equiv _).antisymmRel_congr_right]

@[simp] theorem grundy_nim (o : Nimber) : grundy (nim o) = o := grundy_eq .rfl
@[simp] theorem grundy_zero : grundy 0 = 0 := by simpa using grundy_nim 0
@[simp] theorem grundy_star : grundy ⋆ = 1 := by simpa using grundy_nim 1

@[simp]
theorem grundy_neg (x : IGame) [Impartial x] : grundy (-x) = grundy x := by
  rw [grundy_eq_iff_equiv_nim, ← neg_nim, IGame.neg_equiv_neg_iff, ← grundy_eq_iff_equiv_nim]

@[simp]
theorem leftGrundy_eq_grundy (x : IGame) [Impartial x] : leftGrundy x = grundy x := by
  rw [← grundy_neg, grundy, rightGrundy_neg]

@[simp]
theorem rightGrundy_eq_grundy (x : IGame) [Impartial x] : rightGrundy x = grundy x :=
  rfl

@[simp]
theorem grundy_add (x y : IGame) [Impartial x] [Impartial y] :
    grundy (x + y) = grundy x + grundy y :=
  rightGrundy_add x y

theorem _root_.IGame.nim_add_equiv (a b : Nimber) : nim a + nim b ≈ nim (a + b) := by
  conv_rhs => rw [← grundy_nim a, ← grundy_nim b, ← grundy_add]
  exact (nim_grundy_equiv _).symm

theorem grundy_leftMove_ne {x y : IGame} [Impartial x] (hy : y ∈ x.leftMoves) :
    have := Impartial.of_mem_leftMoves hy; grundy y ≠ grundy x := by
  simp_rw [← leftGrundy_eq_grundy]
  exact leftGrundy_ne hy

theorem grundy_rightMove_ne {x y : IGame} [Impartial x] (hy : y ∈ x.rightMoves) :
    have := Impartial.of_mem_rightMoves hy; grundy y ≠ grundy x :=
  rightGrundy_ne hy

/-- One half of the **lawnmower theorem** for impartial games. -/
protected theorem lt_of_numeric_of_pos (x) [Impartial x] {y} [Numeric y] (hy : 0 < y) : x < y := by
  rw [← (nim_grundy_equiv x).lt_congr_left]
  exact Dicotic.lt_of_numeric_of_pos _ hy

/-- One half of the **lawnmower theorem** for impartial games. -/
protected theorem lt_of_numeric_of_neg (x) [Impartial x] {y} [Numeric y] (hy : y < 0) : y < x := by
  rw [← (nim_grundy_equiv x).lt_congr_right]
  exact Dicotic.lt_of_numeric_of_neg _ hy

private theorem of_leftGrundy_eq_rightGrundy' {x : IGame}
    (hl : ∀ y ∈ x.leftMoves, Impartial y) (hr : ∀ y ∈ x.rightMoves, Impartial y)
    (H : leftGrundy x = rightGrundy x) : nim (rightGrundy x) ≈ x := by
  constructor <;> refine le_iff_forall_lf.2 ⟨?_, ?_⟩
  · rw [forall_leftMoves_nim]
    intro a ha
    rw [← H] at ha
    obtain ⟨y, hy, rfl⟩ := mem_leftGrundy_image_of_lt ha
    have := hl y hy
    rw [leftGrundy_eq_grundy]
    exact lf_of_le_leftMove (nim_grundy_equiv y).le hy
  · intro y hy
    have := hr y hy
    rw [← (nim_grundy_equiv y).le_congr_left, lf_iff_fuzzy, nim_fuzzy_iff, ← rightGrundy_eq_grundy]
    exact (rightGrundy_ne hy).symm
  · intro y hy
    have := hl y hy
    rw [← (nim_grundy_equiv y).le_congr_right, lf_iff_fuzzy, nim_fuzzy_iff, ← leftGrundy_eq_grundy]
    exact H ▸ leftGrundy_ne hy
  · rw [forall_rightMoves_nim]
    intro a ha
    obtain ⟨y, hy, rfl⟩ := mem_rightGrundy_image_of_lt ha
    have := hr y hy
    exact lf_of_rightMove_le (nim_grundy_equiv y).ge hy

/-- If a game `x` has only impartial options, and its left Grundy value equals its right Grundy
value, then it's impartial. -/
theorem of_leftGrundy_eq_rightGrundy {x : IGame}
    (hl : ∀ y ∈ x.leftMoves, Impartial y) (hr : ∀ y ∈ x.rightMoves, Impartial y)
    (H : leftGrundy x = rightGrundy x) : Impartial x :=
  have H := of_leftGrundy_eq_rightGrundy' hl hr H
  .mk' ((neg_congr H).symm.trans ((neg_nim _).symm ▸ H)) hl hr

/-! ### Multiplication -/

set_option maxHeartbeats 500000 in
private theorem mul' (x y : IGame) [Impartial x] [Impartial y] :
    Impartial (x * y) ∧ rightGrundy (x * y) = rightGrundy x * rightGrundy y := by
  have h₁ : leftGrundy (x * y) = leftGrundy x * leftGrundy y := by
    apply le_antisymm
    · apply leftGrundy_le_of_notMem
      intro ⟨z, hz, hz'⟩
      rw [leftMoves_mul] at hz
      obtain ⟨⟨a, b⟩, ⟨ha, hb⟩ | ⟨ha, hb⟩, rfl⟩ := hz
      all_goals
        first | have := Impartial.of_mem_leftMoves ha | have := Impartial.of_mem_rightMoves ha
        first | have := Impartial.of_mem_leftMoves hb | have := Impartial.of_mem_rightMoves hb
        have := (mul' a y).1
        have := (mul' x b).1
        simp_rw [mulOption, leftGrundy_sub, leftGrundy_add,
          leftGrundy_eq_grundy, ← rightGrundy_eq_grundy] at hz'
        repeat rw [(mul' ..).2] at hz'
        apply mul_ne_of_ne _ _ hz' <;> solve_by_elim [grundy_leftMove_ne, grundy_rightMove_ne]
    · rw [le_leftGrundy_iff]
      intro a h
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_of_lt_mul h
      obtain ⟨a, ha', rfl⟩ := mem_leftGrundy_image_of_lt ha
      obtain ⟨b, hb', rfl⟩ := mem_leftGrundy_image_of_lt hb
      refine ⟨_, mulOption_left_left_mem_leftMoves_mul ha' hb', ?_⟩
      have := Impartial.of_mem_leftMoves ha'
      have := Impartial.of_mem_leftMoves hb'
      have := (mul' a y).1
      have := (mul' x b).1
      simp_rw [mulOption, leftGrundy_sub, leftGrundy_add,
        leftGrundy_eq_grundy, ← rightGrundy_eq_grundy]
      repeat rw [(mul' ..).2]
  have h₂ : rightGrundy (x * y) = rightGrundy x * rightGrundy y := by
    apply le_antisymm
    · apply rightGrundy_le_of_notMem
      intro ⟨z, hz, hz'⟩
      rw [rightMoves_mul] at hz
      obtain ⟨⟨a, b⟩, ⟨ha, hb⟩ | ⟨ha, hb⟩, rfl⟩ := hz
      all_goals
        first | have := Impartial.of_mem_leftMoves ha | have := Impartial.of_mem_rightMoves ha
        first | have := Impartial.of_mem_leftMoves hb | have := Impartial.of_mem_rightMoves hb
        have := (mul' a b).1
        simp_rw [mulOption, rightGrundy_sub, rightGrundy_add,
          leftGrundy_eq_grundy, ← rightGrundy_eq_grundy] at hz'
        repeat rw [(mul' ..).2] at hz'
        apply mul_ne_of_ne _ _ hz' <;> solve_by_elim [grundy_leftMove_ne, grundy_rightMove_ne]
    · rw [le_rightGrundy_iff]
      intro a h
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_of_lt_mul h
      rw [rightGrundy_eq_grundy, ← leftGrundy_eq_grundy] at ha
      obtain ⟨a, ha', rfl⟩ := mem_leftGrundy_image_of_lt ha
      obtain ⟨b, hb', rfl⟩ := mem_rightGrundy_image_of_lt hb
      refine ⟨_, mulOption_left_right_mem_rightMoves_mul ha' hb', ?_⟩
      have := Impartial.of_mem_leftMoves ha'
      have := Impartial.of_mem_rightMoves hb'
      have := (mul' a b).1
      simp_rw [mulOption, rightGrundy_sub, rightGrundy_add,
        leftGrundy_eq_grundy, ← rightGrundy_eq_grundy]
      repeat rw [(mul' ..).2]
  simp_rw [leftGrundy_eq_grundy, rightGrundy_eq_grundy] at h₁ h₂
  refine ⟨of_leftGrundy_eq_rightGrundy ?_ ?_ (h₁.trans h₂.symm), h₂⟩
  all_goals
    simp only [forall_leftMoves_mul, forall_rightMoves_mul, mulOption]
    constructor
    all_goals
      intro a ha b hb
      first | have := Impartial.of_mem_leftMoves ha | have := Impartial.of_mem_rightMoves ha
      first | have := Impartial.of_mem_leftMoves hb | have := Impartial.of_mem_rightMoves hb
      have := (mul' a y).1
      have := (mul' x b).1
      have := (mul' a b).1
      infer_instance
termination_by (x, y)
decreasing_by igame_wf

protected instance mul (x y : IGame) [Impartial x] [Impartial y] : Impartial (x * y) :=
  (mul' x y).1

@[simp]
theorem grundy_mul (x y : IGame) [Impartial x] [Impartial y] :
    grundy (x * y) = grundy x * grundy y :=
  (mul' x y).2

theorem _root_.IGame.nim_mul_equiv (a b : Nimber) : nim a * nim b ≈ nim (a * b) := by
  conv_rhs => rw [← grundy_nim a, ← grundy_nim b, ← grundy_mul]
  exact (nim_grundy_equiv _).symm

theorem mul_equiv_zero {x y : IGame} [Impartial x] [Impartial y] : x * y ≈ 0 ↔ x ≈ 0 ∨ y ≈ 0 := by
  rw [← grundy_eq_zero_iff, grundy_mul, mul_eq_zero, grundy_eq_zero_iff, grundy_eq_zero_iff]

protected instance mulOption (x y a b : IGame)
    [Impartial x] [Impartial y] [Impartial a] [Impartial b] :
    Impartial (mulOption x y a b) :=
  .sub ..

theorem mul_congr_left {x₁ x₂ y : IGame} [Impartial x₁] [Impartial x₂] [Impartial y]
    (he : x₁ ≈ x₂) : x₁ * y ≈ x₂ * y := by
  rw [← Game.mk_eq_mk, ← sub_eq_zero] at he ⊢
  rw [← Game.mk_sub_mul]
  exact Game.mk_eq (mul_equiv_zero.2 <| .inl (Game.mk_eq_mk.1 he))

theorem mul_congr_right {x y₁ y₂ : IGame} [Impartial x] [Impartial y₁] [Impartial y₂]
    (he : y₁ ≈ y₂) : x * y₁ ≈ x * y₂ := by
  rw [mul_comm, mul_comm x]; exact mul_congr_left he

theorem mul_congr {x₁ x₂ y₁ y₂ : IGame} [Impartial x₁] [Impartial x₂] [Impartial y₁] [Impartial y₂]
    (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ * y₁ ≈ x₂ * y₂ :=
  (mul_congr_left hx).trans (mul_congr_right hy)

end Impartial
end IGame
end
