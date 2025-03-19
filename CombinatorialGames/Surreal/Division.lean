/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Theodore Hwa
-/
import CombinatorialGames.Surreal.Multiplication
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring.RingNF

/-!
# Surreal division

In this file, we prove that if `x` is a positive numeric game, then `x⁻¹` (defined in
`Mathlib.SetTheory.Game.IGame`) is a number and is a multiplicative inverse for `x`. We use that
to define the field structure on `Surreal`.

This is Theorem 1.10 in ONAG, and we follow the broad strokes of the proof. We prove
by simultaneous induction that if `x` is positive and numeric, then (ii) `x⁻¹` is numeric, and (iv)
`x * x⁻¹ ≈ 1`. We do this by showing the inductive hypothesis implies that (i) `x * y < 1` for
`y ∈ x⁻¹.leftMoves` and `1 < x * y` for `y ∈ x⁻¹.rightMoves`, and that (iv) `y < 1` for
`y ∈ (x * x⁻¹).leftMoves` and `1 < y` for `y ∈ (x * x⁻¹.rightMoves)`.

An important difference is that Conway assumes that `x` has no negative left options, while we don't
make use of this assumption. This is because our definition of the inverse is tweaked to ensure that
only positive left options of `x` generate the options for `x⁻¹`. To make sure the induction checks
out, we require two small extra arithmetic lemmas `mulOption_le` and `le_mulOption`.

Once we have defined the inverse for positive `x`, it is extended in the obvious way to negative
numbers.
-/

universe u

open IGame

private instance {x y : IGame} [Numeric x] [Numeric y⁻¹] : Numeric (x / y) := .mul ..

private instance {x y a : IGame} [Numeric x] [Numeric y] [Numeric y⁻¹] [Numeric a] :
    Numeric (invOption x y a) :=
  .mul ..

private theorem inv_pos' {x : IGame} [Numeric x⁻¹] (hx : 0 < x) : 0 < x⁻¹ :=
  Numeric.leftMove_lt (zero_mem_leftMoves_inv hx)

private theorem mk_div' (x y : IGame) [Numeric x] [Numeric y⁻¹] :
    Surreal.mk (x / y) = Surreal.mk x * Surreal.mk y⁻¹ :=
  Surreal.mk_mul ..

namespace Surreal.Division

/-! ### Arithmetic lemmas -/

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

/-! ### Inductive proof -/

lemma numeric_option_inv {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹) :
    (∀ y ∈ x⁻¹.leftMoves, Numeric y) ∧ (∀ y ∈ x⁻¹.rightMoves, Numeric y) := by
  apply invRec hx Numeric.zero
  all_goals
    intro y hy hyx
    intros
    first |
      have := Numeric.of_mem_leftMoves hyx; have := hl _ hyx hy |
      have := Numeric.of_mem_rightMoves hyx; have := hr _ hyx
    infer_instance

lemma mul_inv_option_mem {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹)
    (hl' : ∀ y ∈ x.leftMoves, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ x.rightMoves, y * y⁻¹ ≈ 1) :
    (∀ y ∈ x⁻¹.leftMoves, x * y < 1) ∧ (∀ y ∈ x⁻¹.rightMoves, 1 < x * y) := by
  apply invRec hx
  · simp
  all_goals intro y hy hyx a ha h
  · have := Numeric.of_mem_rightMoves hyx
    have := hr y hyx
    have := (numeric_option_inv hx hl hr).1 a ha
    rw [← IGame.sub_pos, (one_neg_mul_invOption x (hr' y hyx) a).lt_congr_right]
    apply Numeric.mul_pos (Numeric.mul_pos _ _) (inv_pos' hy)
    · rwa [IGame.sub_pos]
    · rw [IGame.sub_pos]
      exact Numeric.lt_rightMove hyx
  · have := Numeric.of_mem_leftMoves hyx
    have := hl y hyx hy
    have := (numeric_option_inv hx hl hr).2 a ha
    rw [← IGame.sub_pos, (one_neg_mul_invOption x (hl' y hyx hy) a).lt_congr_right]
    apply Numeric.mul_pos (Numeric.mul_pos_of_neg_of_neg _ _) (inv_pos' hy)
    · rwa [IGame.sub_neg]
    · rw [IGame.sub_neg]
      exact Numeric.leftMove_lt hyx
  · have := Numeric.of_mem_leftMoves hyx
    have := hl y hyx hy
    have := (numeric_option_inv hx hl hr).1 a ha
    rw [← IGame.sub_neg, (one_neg_mul_invOption x (hl' y hyx hy) a).lt_congr_left]
    apply Numeric.mul_neg_of_neg_of_pos (Numeric.mul_neg_of_pos_of_neg _ _) (inv_pos' hy)
    · rwa [IGame.sub_pos]
    · rw [IGame.sub_neg]
      exact Numeric.leftMove_lt hyx
  · have := Numeric.of_mem_rightMoves hyx
    have := hr y hyx
    have := (numeric_option_inv hx hl hr).2 a ha
    rw [← IGame.sub_neg, (one_neg_mul_invOption x (hr' y hyx) a).lt_congr_left]
    apply Numeric.mul_neg_of_neg_of_pos (Numeric.mul_neg_of_neg_of_pos _ _) (inv_pos' hy)
    · rwa [IGame.sub_neg]
    · rw [IGame.sub_pos]
      exact Numeric.lt_rightMove hyx

lemma numeric_inv {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹)
    (hl' : ∀ y ∈ x.leftMoves, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ x.rightMoves, y * y⁻¹ ≈ 1) :
    Numeric x⁻¹ := by
  obtain ⟨Hl, Hr⟩ := mul_inv_option_mem hx hl hr hl' hr'
  obtain ⟨Hl', Hr'⟩ := numeric_option_inv hx hl hr
  refine Numeric.mk' (fun y hy z hz ↦ ?_) Hl' Hr'
  have := Hl' y hy
  have := Hr' z hz
  exact (Numeric.mul_lt_mul_left hx).1 <| (Hl y hy).trans (Hr z hz)

lemma option_mul_inv_lt {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹)
    (hl' : ∀ y ∈ x.leftMoves, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ x.rightMoves, y * y⁻¹ ≈ 1) :
    (∀ y ∈ (x * x⁻¹).leftMoves, y < 1) ∧ (∀ y ∈ (x * x⁻¹).rightMoves, 1 < y) := by
  have := numeric_inv hx hl hr hl' hr'
  obtain ⟨Hl, Hr⟩ := numeric_option_inv hx hl hr
  rw [forall_leftMoves_mul, forall_rightMoves_mul]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  all_goals
    intro y hyx a ha
    first | have := Numeric.of_mem_leftMoves hyx | have := Numeric.of_mem_rightMoves hyx
    first | have := Hl a ha | have := Hr a ha
    try (have := hr y hyx; have hy := hx.trans (Numeric.lt_rightMove hyx))
  · obtain hy | hy := Numeric.lt_or_le 0 y
    · have := hl y hyx hy
      rw [(mulOption_self_inv x (hl' y hyx hy) a).lt_congr_left, add_comm,
        ← IGame.lt_sub_iff_add_lt, (IGame.sub_self_equiv _).lt_congr_right]
      apply Numeric.mul_neg_of_neg_of_pos _ hy
      rw [IGame.sub_neg]
      exact Numeric.lt_rightMove (invOption_left_left_mem_rightMoves_inv hx hy hyx ha)
    · apply (mulOption_le _ _ hy (Numeric.leftMove_lt ha).le).trans_lt
      exact (mul_inv_option_mem hx hl hr hl' hr').1 a ha
  · rw [(mulOption_self_inv x (hr' y hyx) a).lt_congr_left, add_comm,
      ← IGame.lt_sub_iff_add_lt, (IGame.sub_self_equiv _).lt_congr_right]
    apply Numeric.mul_neg_of_neg_of_pos _ hy
    rw [IGame.sub_neg]
    exact Numeric.lt_rightMove (invOption_right_right_mem_rightMoves_inv hx hy hyx ha)
  · obtain hy | hy := Numeric.lt_or_le 0 y
    · have := hl y hyx hy
      rw [(mulOption_self_inv x (hl' y hyx hy) a).lt_congr_right, add_comm,
        ← IGame.sub_lt_iff_lt_add, (IGame.sub_self_equiv _).lt_congr_left]
      apply Numeric.mul_pos _ hy
      rw [IGame.sub_pos]
      apply Numeric.leftMove_lt (invOption_left_right_mem_leftMoves_inv hx hy hyx ha)
    · apply ((mul_inv_option_mem hx hl hr hl' hr').2 a ha).trans_le
      exact le_mulOption _ _ hy (Numeric.lt_rightMove ha).le
  · rw [(mulOption_self_inv x (hr' y hyx) a).lt_congr_right, add_comm,
      ← IGame.sub_lt_iff_lt_add, (IGame.sub_self_equiv _).lt_congr_left]
    apply Numeric.mul_pos _ hy
    rw [IGame.sub_pos]
    exact Numeric.leftMove_lt (invOption_right_left_mem_leftMoves_inv hx hy hyx ha)

lemma mul_inv_self {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ x.leftMoves, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ x.rightMoves, Numeric y⁻¹)
    (hl' : ∀ y ∈ x.leftMoves, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ x.rightMoves, y * y⁻¹ ≈ 1) :
    x * x⁻¹ ≈ 1 := by
  obtain ⟨Hl, Hr⟩ := option_mul_inv_lt hx hl hr hl' hr'
  have := numeric_inv hx hl hr hl' hr'
  apply equiv_one_of_fits ⟨fun z hz ↦ (Hl z hz).not_le, fun z hz ↦ (Hr z hz).not_le⟩
  rw [Numeric.mul_equiv_zero, not_or]
  exact ⟨hx.not_antisymmRel_symm, (inv_pos' hx).not_antisymmRel_symm⟩

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

/-! ### Instances and corollaries -/

namespace IGame.Numeric
open Surreal.Division

protected instance inv (x : IGame) [Numeric x] : Numeric x⁻¹ := by
  obtain h | h | h := Numeric.lt_or_equiv_or_gt x 0
  · rw [← IGame.zero_lt_neg] at h
    simpa using (main h).1
  · simp [inv_of_equiv_zero h]
  · exact (main h).1

protected instance div (x y : IGame) [Numeric x] [Numeric y] : Numeric (x / y) := .mul ..
protected instance ratCast (q : ℚ) : Numeric q := .div ..

protected instance invOption (x y a : IGame) [Numeric x] [Numeric y] [Numeric a] :
    Numeric (invOption x y a) :=
  .div ..

protected theorem mul_inv_cancel {x : IGame} [Numeric x] (hx : ¬ x ≈ 0) : x * x⁻¹ ≈ 1 := by
  obtain h | h | h := Numeric.lt_or_equiv_or_gt x 0
  · rw [← IGame.zero_lt_neg] at h
    simpa using (main h).2
  · contradiction
  · exact (main h).2

protected theorem inv_mul_cancel {x : IGame} [Numeric x] (hx : ¬ x ≈ 0) : x⁻¹ * x ≈ 1 := by
  rw [mul_comm]
  exact Numeric.mul_inv_cancel hx

theorem inv_congr {x y : IGame} [Numeric x] [Numeric y] (he : x ≈ y) : x⁻¹ ≈ y⁻¹ := by
  by_cases hy : y ≈ 0
  · rw [inv_of_equiv_zero hy, inv_of_equiv_zero (he.trans hy)]
  · have hx := (hy <| he.symm.trans ·)
    have := (Numeric.mul_inv_cancel hx).trans (Numeric.mul_inv_cancel hy).symm
    rw [← (Numeric.mul_congr_left he).antisymmRel_congr_right] at this
    exact Numeric.mul_left_cancel hx this

theorem div_congr_left {x₁ x₂ y : IGame} [Numeric x₁] [Numeric x₂] [Numeric y] (he : x₁ ≈ x₂) :
    x₁ / y ≈ x₂ / y :=
  mul_congr_left he

theorem div_congr_right {x y₁ y₂ : IGame} [Numeric x] [Numeric y₁] [Numeric y₂] (he : y₁ ≈ y₂) :
    x / y₁ ≈ x / y₂ :=
  mul_congr_right (inv_congr he)

theorem div_congr {x₁ x₂ y₁ y₂ : IGame} [Numeric x₁] [Numeric x₂] [Numeric y₁] [Numeric y₂]
    (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ / y₁ ≈ x₂ / y₂ :=
  (div_congr_left hx).trans (div_congr_right hy)

end IGame.Numeric

namespace Surreal

noncomputable instance : LinearOrderedField Surreal where
  inv := Quotient.map (fun x ↦ ⟨x⁻¹, by infer_instance⟩) fun _ _ ↦ Numeric.inv_congr
  mul_inv_cancel := by rintro ⟨a⟩ h; exact mk_eq (Numeric.mul_inv_cancel (mk_eq_mk.not.1 h))
  inv_zero := by change mk 0⁻¹ = _; simp [inv_zero]
  qsmul := _
  nnqsmul := _

@[simp] theorem mk_inv (x : IGame) [Numeric x] : mk x⁻¹ = (mk x)⁻¹ := rfl
@[simp] theorem mk_div (x y : IGame) [Numeric x] [Numeric y] : mk (x / y) = mk x / mk y := rfl

@[simp]
theorem mk_ratCast (q : ℚ) : mk q = q := by
  conv_rhs => rw [← q.num_div_den]
  simp [ratCast_def]

@[simp]
theorem toGame_ratCast (q : ℚ) : toGame q = q := by
  rw [← mk_ratCast, toGame_mk, Game.mk_ratCast]

end Surreal

namespace IGame

theorem Numeric.inv_equiv_of_mul_eq_one {x y : IGame} [Numeric x] [Numeric y]
    (he : x * y ≈ 1) : x⁻¹ ≈ y := by
  rw [← Surreal.mk_eq_mk] at *
  exact inv_eq_of_mul_eq_one_right (a := Surreal.mk x) he

theorem Numeric.equiv_inv_of_mul_eq_one {x y : IGame} [Numeric x] [Numeric y]
    (he : x * y ≈ 1) : x ≈ y⁻¹ :=
  (Numeric.inv_equiv_of_mul_eq_one (mul_comm x y ▸ he)).symm

@[simp]
theorem Numeric.inv_pos {x : IGame} [Numeric x] : 0 < x⁻¹ ↔ 0 < x := by
  simp [← Surreal.mk_lt_mk]

@[simp]
theorem Numeric.inv_neg {x : IGame} [Numeric x] : x⁻¹ < 0 ↔ x < 0 := by
  simp [← Surreal.mk_lt_mk]

@[simp]
theorem Numeric.inv_nonneg {x : IGame} [Numeric x] : 0 ≤ x⁻¹ ↔ 0 ≤ x := by
  simp [← Surreal.mk_le_mk]

@[simp]
theorem Numeric.inv_nonpos {x : IGame} [Numeric x] : x⁻¹ ≤ 0 ↔ x ≤ 0 := by
  simp [← Surreal.mk_le_mk]

@[simp, norm_cast]
theorem ratCast_le {m n : ℚ} : (m : IGame) ≤ n ↔ m ≤ n := by
  simp [← Surreal.mk_le_mk]

@[simp, norm_cast]
theorem ratCast_lt {m n : ℚ} : (m : IGame) < n ↔ m < n := by
  simp [← Surreal.mk_lt_mk]

theorem ratCast_strictMono : StrictMono ((↑) : ℚ → IGame) :=
  fun _ _ h ↦ ratCast_lt.2 h

@[simp, norm_cast]
theorem ratCast_inj {m n : ℚ} : (m : IGame) = n ↔ m = n :=
  ratCast_strictMono.injective.eq_iff

-- TODO: upstream
attribute [simp] AntisymmRel.refl

private theorem equiv_ratCast_of_mem_move_inv_natCast {n : ℕ} :
    (∀ x ∈ leftMoves.{u} n⁻¹, ∃ q : ℚ, x ≈ q) ∧ (∀ x ∈ rightMoves.{u} n⁻¹, ∃ q : ℚ, x ≈ q) := by
  cases n with
  | zero => simp
  | succ n =>
    refine invRec (mod_cast n.succ_pos) ⟨0, ?_⟩ ?_ ?_ ?_ ?_
    any_goals simp
    all_goals
      rintro _ hn rfl x hx q hq
      use (1 + -q) / n
      first | have := Numeric.of_mem_leftMoves hx | have := Numeric.of_mem_rightMoves hx
      simp_all [invOption, ← Surreal.mk_eq_mk]

private theorem equiv_ratCast_of_mem_move_ratCast {q : ℚ} :
    (∀ x ∈ leftMoves.{u} q, ∃ r : ℚ, x ≈ r) ∧ (∀ x ∈ rightMoves.{u} q, ∃ r : ℚ, x ≈ r) := by
  constructor
  all_goals
    rw [ratCast_def]
    simp only [IGame.div_eq_mul_inv, forall_leftMoves_mul, forall_rightMoves_mul]
    obtain ⟨m, n, hn, _⟩ := q
    constructor
    all_goals
    · intro x hx y hy
      first |
        obtain ⟨k, _, rfl⟩ := eq_intCast_of_mem_leftMoves_intCast hx |
        obtain ⟨k, _, rfl⟩ := eq_intCast_of_mem_rightMoves_intCast hx
      first |
        obtain ⟨q, hq⟩ := equiv_ratCast_of_mem_move_inv_natCast.1 _ hy |
        obtain ⟨q, hq⟩ := equiv_ratCast_of_mem_move_inv_natCast.2 _ hy
      use k * (n : ℚ)⁻¹ + m * q - k * q
      first | have := Numeric.of_mem_leftMoves hy | have := Numeric.of_mem_rightMoves hy
      simp_all [mulOption, ← Surreal.mk_eq_mk]

/-- Every left option of a rational number is equivalent to a smaller rational number. -/
theorem equiv_ratCast_of_mem_leftMoves_ratCast {q : ℚ} {x : IGame} (hx : x ∈ leftMoves q) :
    ∃ r : ℚ, r < q ∧ x ≈ r := by
  obtain ⟨r, hr⟩ := equiv_ratCast_of_mem_move_ratCast.1 x hx
  refine ⟨r, ?_, hr⟩
  rw [← ratCast_lt, ← hr.lt_congr_left]
  simpa using Numeric.leftMove_lt hx

/-- Every right option of a rational number is equivalent to a larger rational number. -/
theorem equiv_ratCast_of_mem_rightMoves_ratCast {q : ℚ} {x : IGame} (hx : x ∈ rightMoves q) :
    ∃ r : ℚ, q < r ∧ x ≈ r := by
  obtain ⟨r, hr⟩ := equiv_ratCast_of_mem_move_ratCast.2 x hx
  refine ⟨r, ?_, hr⟩
  rw [← ratCast_lt, ← hr.lt_congr_right]
  simpa using Numeric.lt_rightMove hx

end IGame

namespace Game

@[simp, norm_cast]
theorem ratCast_le {m n : ℚ} : (m : Game) ≤ n ↔ m ≤ n :=
  IGame.ratCast_le

@[simp, norm_cast]
theorem ratCast_lt {m n : ℚ} : (m : Game) < n ↔ m < n :=
  IGame.ratCast_lt

theorem ratCast_strictMono : StrictMono ((↑) : ℚ → Game) :=
  fun _ _ h ↦ ratCast_lt.2 h

@[simp, norm_cast]
theorem ratCast_inj {m n : ℚ} : (m : Game) = n ↔ m = n :=
  ratCast_strictMono.injective.eq_iff

end Game
