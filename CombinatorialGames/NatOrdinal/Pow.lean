/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.NatOrdinal.Basic
import Mathlib.Order.IsNormal

/-!
# Natural exponentiation

There is no notion of "natural exponentiation of ordinals", at least not in the usual sense. While
surreal exponentiation can be defined via the Gonshor exponential and logarithm, this operation is
not closed on the ordinals. Attempting to axiomatize such an operation will not be successful
either; it's proven in [Altman2015] that the following five conditions are incompatible:

1. `x ^ 1 = x`
2. `Monotone (· ^ y)`
3. `Monotone (x ^ ·)` for `x ≠ 0`
4. `x ^ (y + z) = x ^ y * x ^ z`
5. `x ^ (y * z) = (x ^ y) ^ z`

This is not to imply that there is no useful notion of exponentiation on `NatOrdinal`. What we
define here is called **Super-Jacobsthal exponentiation** by the same article, and is the unique
normal function such that `x ^ 0 = 1` and `x ^ (y + 1) = x ^ y * x` for all `x` and `y`. This
satisfies properties 1 through 4.

Quite conveniently, super-Jacobsthal exponentiation with base `ω` matches ordinal exponentiation
with the same base. This allows us to conveniently state a full characterization of natural
arithmetic.
-/

open Order Set

namespace NatOrdinal

variable {x y z : NatOrdinal}

/-- **Super-Jacobsthal exponentiation** is defined by transfinite induction as the unique normal
function such that `x ^ 0 = 1` and `x ^ (y + 1) = x ^ y * x`. -/
noncomputable instance : HomogeneousPow NatOrdinal where
  pow x y := if x = 0 then (if y = 0 then 1 else 0) else
    SuccOrder.limitRecOn y (fun _ _ ↦ 1) (fun _ _ IH ↦ IH * x) (fun y _ IH ↦ ⨆ z : Iio y, IH z z.2)

@[aesop simp]
theorem zero_npow_eq (x : NatOrdinal) : 0 ^ x = if x = 0 then 1 else 0 := dif_pos rfl

@[simp]
theorem zero_npow (hx : x ≠ 0) : 0 ^ x = 0 := by
  simp [zero_npow_eq, hx]

@[simp]
theorem npow_zero (x : NatOrdinal) : x ^ (0 : NatOrdinal) = 1 := by
  obtain rfl | hx := eq_or_ne x 0
  · simp [zero_npow_eq]
  · apply (dif_neg hx).trans
    simp

@[simp]
theorem npow_add_one (x y : NatOrdinal) : x ^ (y + 1) = x ^ y * x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · apply (dif_neg hx).trans
    rw [← succ_eq_add_one, SuccOrder.limitRecOn_succ, eq_comm]
    congr
    exact dif_neg hx

@[simp]
theorem npow_one_add (x y : NatOrdinal) : x ^ (1 + y) = x * x ^ y := by
  rw [add_comm, npow_add_one, mul_comm]

@[simp]
theorem npow_natCast (x : NatOrdinal) (n : ℕ) : x ^ (n : NatOrdinal) = x ^ n := by
  induction n with
  | zero => exact npow_zero x
  | succ n IH => rw [Nat.cast_add_one, npow_add_one, pow_succ, IH]

@[simp]
theorem npow_one (x : NatOrdinal) : x ^ (1 : NatOrdinal) = x := by
  simpa using npow_natCast x 1

theorem npow_of_isSuccLimit (hx : x ≠ 0) (hy : IsSuccLimit y) : x ^ y = ⨆ z : Iio y, x ^ z.1 := by
  apply (dif_neg hx).trans
  rw [SuccOrder.limitRecOn_of_isSuccLimit _ _ _ hy, eq_comm]
  congr!
  exact dif_neg hx

theorem lt_npow_iff (hx : x ≠ 0) (h : IsSuccLimit y) : z < x ^ y ↔ ∃ y' < y, z < x ^ y' := by
  rw [npow_of_isSuccLimit hx h, lt_ciSup_iff' (bddAbove_of_small _)]
  simp

/-- TOOO: update Mathlib -/
private theorem _root_.Order.IsSuccLimit.nonempty_Iio (H : IsSuccLimit x) : Nonempty (Iio x) :=
  ⟨⟨⊥, H.bot_lt⟩⟩

@[simp]
theorem one_npow (x : NatOrdinal) : 1 ^ x = 1 := by
  induction x using SuccOrder.limitRecOn with
  | isMin _ _ | succ _ _ _ => simp_all
  | isSuccLimit x hx IH =>
    have := hx.nonempty_Iio
    rw [npow_of_isSuccLimit one_ne_zero hx, iSup_congr fun z ↦ IH _ z.2, ciSup_const]

theorem npow_le_npow_left (h : x ≤ y) (z : NatOrdinal) : x ^ z ≤ y ^ z := by
  obtain rfl | hx := eq_or_ne x 0
  · aesop
  induction z using SuccOrder.limitRecOn with
  | isMin z IH => simp_all
  | succ z _ IH => simpa using mul_le_mul' IH h
  | isSuccLimit z hz IH =>
    rw [npow_of_isSuccLimit hx hz, npow_of_isSuccLimit _ hz]
    · have := hz.nonempty_Iio
      apply ciSup_mono (bddAbove_of_small _)
      simpa
    · aesop

@[simp]
theorem npow_pos (h : x ≠ 0) (y : NatOrdinal) : 0 < x ^ y := by
  rw [← pos_iff_ne_zero, ← one_le_iff_pos] at *
  rw [← one_npow y]
  exact npow_le_npow_left h y

@[simp]
theorem npow_ne_zero (h : x ≠ 0) (y : NatOrdinal) : x ^ y ≠ 0 :=
  (npow_pos h y).ne'

theorem isNormal_npow (hx : 1 < x) : Order.IsNormal (x ^ · : NatOrdinal → NatOrdinal) := by
  refine .of_succ_lt (fun y ↦ ?_) (@fun y hy ↦ ?_)
  · rw [succ_eq_add_one, npow_add_one]
    exact lt_mul_right (npow_pos hx.ne_bot y) hx
  · rw [npow_of_isSuccLimit hx.ne_bot hy]
    exact isLUB_ciSup_set (bddAbove_of_small _) ⟨0, hy.bot_lt⟩

theorem npow_lt_npow_iff_right (hx : 1 < x) : x ^ y < x ^ z ↔ y < z :=
  (isNormal_npow hx).strictMono.lt_iff_lt

theorem npow_lt_npow_right (hx : 1 < x) (h : y < z) : x ^ y < x ^ z :=
  (npow_lt_npow_iff_right hx).2 h

theorem npow_le_npow_iff_right (hx : 1 < x) : x ^ y ≤ x ^ z ↔ y ≤ z :=
  (isNormal_npow hx).strictMono.le_iff_le

theorem npow_le_npow_right (hx : x ≠ 0) (h : y ≤ z) : x ^ y ≤ x ^ z := by
  obtain hx' | hx' := le_or_gt x 1
  · simp_all [le_one_iff]
  · exact (npow_le_npow_iff_right hx').2 h

theorem npow_add (x y z : NatOrdinal) : x ^ (y + z) = x ^ y * x ^ z := by
  obtain hx | hx := le_or_gt x 1
  · aesop (add simp [le_one_iff])
  · have hx₀ : x ≠ 0 := hx.ne_bot
    obtain rfl | ⟨y, rfl⟩ | hy := zero_or_add_one_or_isSuccLimit y
    · simp
    · have := lt_add_one y
      simp_rw [add_right_comm, npow_add_one, npow_add x y z, mul_right_comm]
    obtain rfl | ⟨z, rfl⟩ | hz := zero_or_add_one_or_isSuccLimit z
    · simp
    · have := lt_add_one z
      simp_rw [← add_assoc, npow_add_one, npow_add x y z, mul_assoc]
    have H := isSuccLimit_add hy hz
    have := H.nonempty_Iio
    rw [npow_of_isSuccLimit hx₀ H]
    apply le_antisymm
    · apply ciSup_le
      rintro ⟨a, ha⟩
      rw [mem_Iio, lt_add_iff] at ha
      obtain ⟨b, hb, ha⟩ | ⟨b, hb, ha⟩ := ha
      all_goals
        apply (npow_le_npow_right hx₀ ha).trans
        rw [npow_add]
        have := npow_le_npow_right hx₀ hb.le
        aesop (add simp [pos_iff_ne_zero])
    · simp_rw [mul_le_iff, lt_npow_iff hx₀ hy, lt_npow_iff hx₀ hz]
      rintro a ⟨b, hb, hab⟩ c ⟨d, hd, hcd⟩
      calc
        _ < x ^ max (b + z) (y + d) + x ^ max (b + z) (y + d) := by
          apply add_lt_add_of_lt_of_le
          · apply (mul_lt_mul_of_pos_right hab (npow_pos hx₀ _)).trans_le
            simp_rw [← npow_add x b z]
            exact npow_le_npow_right hx₀ (le_max_left ..)
          · apply (mul_left_mono hcd.le).trans
            simp_rw [← npow_add x y d]
            exact npow_le_npow_right hx₀ (le_max_right ..)
        _ ≤ x ^ (max (b + z) (y + d) + 1) := by
          rw [← mul_two, npow_add_one]
          apply mul_left_mono
          rwa [← one_add_one_eq_two, add_one_le_iff]
        _ ≤ _ := by
          apply le_add_right.trans'
          refine le_ciSup (f := fun a : Iio (y + z) ↦ x ^ a.1) (bddAbove_of_small _) ⟨_, ?_⟩
          apply H.add_one_lt
          simp_all
termination_by (y, z)

end NatOrdinal
