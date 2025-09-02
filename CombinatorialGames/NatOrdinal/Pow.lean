/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.NatOrdinal.Basic

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

variable {x y : NatOrdinal}

/-- **Super-Jacobsthal exponentiation** is defined by transfinite induction as the unique normal
function such that `x ^ 0 = 1` and `x ^ (y + 1) = x ^ y * x`. -/
noncomputable instance : HomogeneousPow NatOrdinal where
  pow x y := if x = 0 then (if y = 0 then 1 else 0) else
    SuccOrder.limitRecOn y (fun _ _ ↦ 1) (fun _ _ IH ↦ IH * x) (fun y _ IH ↦ ⨆ z : Iio y, IH z z.2)

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

theorem npow_add_one (x y : NatOrdinal) : x ^ (y + 1) = x ^ y * x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · apply (dif_neg hx).trans
    rw [← succ_eq_add_one, SuccOrder.limitRecOn_succ, eq_comm]
    congr
    exact dif_neg hx

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

theorem npow_add (x y z : NatOrdinal) : x ^ (y + z) = x ^ y * x ^ z := sorry

end NatOrdinal
