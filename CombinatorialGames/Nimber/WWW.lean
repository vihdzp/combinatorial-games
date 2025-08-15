/-
Copyright (c) 2025 Django Peeters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Django Peeters
-/
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Nth
import CombinatorialGames.Nimber.Simplicity
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.SetTheory.Ordinal.CantorNormalForm

/-!
# w^(w^w) is algebraically closed

This file aims to prove that `w ^ (w ^ w)` is an algebraically closed field.

The proof follows [On Numbers And Games][conway2001] (pp. 59-61)
and [On The Algebraic Closure Of Two][lenstra1977] (pp. 1-8).

## Todo

Formalize pp. 59-61.

Formalize pp. 1-8.
-/

open Ordinal
open Nat (nth)

/-! ### Mathlib lemmas -/

theorem one_lt_nth_prime (k : ℕ) : 1 < nth Nat.Prime k := by
  apply lt_of_lt_of_le (b := 2) (by norm_num)
  exact le_trans (b := k + 2) (Nat.le_add_left 2 k) (Nat.add_two_le_nth_prime k)

theorem nth_prime_ne_zero (k : ℕ) : nth Nat.Prime k ≠ 0 := by
  rw [Nat.ne_zero_iff_zero_lt]
  exact lt_trans zero_lt_one (one_lt_nth_prime k)

/-! ### Main lemmas -/

noncomputable section

namespace Nimber

protected def field_two : Subfield Nimber := Subfield.closure ∅

private def tau : Nimber := of (omega0 ^ (omega0 ^ omega0))

protected def degree (x : Nimber) : ℕ :=
  (minpoly Nimber.field_two x).natDegree

/- `kappa q` where `q = (nth Nat.Prime k) ^ (n + 1)` -/
protected def kappa_q (k n : ℕ) : Nimber :=
  of <| 2 ^ (omega0 ^ k * (nth Nat.Prime k) ^ n)

protected def kappa (h : ℕ) : Nimber :=
  sInf {x | x < tau ∧ h ∣ Nimber.degree x}

protected def alpha (h : ℕ) : Nimber :=
  sInf {x | x < Nimber.kappa h ∧ ∀ y < Nimber.kappa h, y.val ^ h ≠ x.val}

theorem kappa_q_lt_iff_pair_lt (k n k' n' : ℕ) :
  Nimber.kappa_q k n < Nimber.kappa_q k' n' ↔ k < k' ∨ k = k' ∧ n < n' := by
  simp only [Nimber.kappa_q, OrderIso.lt_iff_lt]
  rw [opow_lt_opow_iff_right (by simp)]
  constructor
  · contrapose!
    intro ⟨h, h'⟩
    rw [le_iff_lt_or_eq] at h
    rcases h with h | rfl
    · apply le_trans (b := omega0 ^ k)
      · repeat rw [← opow_natCast]
        rw [← natCast_opow]
        apply le_of_lt
        apply omega0_opow_mul_nat_lt
        rwa [Nat.cast_lt]
      · apply Ordinal.le_mul_left
        rw [← opow_natCast]
        apply opow_pos
        rw [← Nat.cast_zero, Nat.cast_lt, Nat.pos_iff_ne_zero]
        exact nth_prime_ne_zero k
    · simp only [forall_const] at h'
      rw [Ordinal.mul_le_mul_iff_left (by rw [← opow_natCast]; exact opow_pos _ omega0_pos)]
      repeat rw [← opow_natCast, ← natCast_opow]
      rwa [Nat.cast_le, Nat.pow_le_pow_iff_right (one_lt_nth_prime k')]
  · intro h
    rcases h with h | ⟨rfl, h⟩
    · apply lt_of_lt_of_le (b := omega0 ^ k')
      · repeat rw [← opow_natCast]
        rw [← natCast_opow]
        apply omega0_opow_mul_nat_lt
        rwa [Nat.cast_lt]
      · apply Ordinal.le_mul_left
        rw [← opow_natCast]
        apply opow_pos
        rw [← Nat.cast_zero, Nat.cast_lt, Nat.pos_iff_ne_zero]
        exact nth_prime_ne_zero k'
    · rw [Ordinal.mul_lt_mul_iff_left (by rw [← opow_natCast]; exact opow_pos _ omega0_pos)]
      repeat rw [← opow_natCast, ← natCast_opow]
      rwa [Nat.cast_lt, Nat.pow_lt_pow_iff_right (one_lt_nth_prime k)]



theorem kappa_nth_prime_pow (k n : ℕ) {h : n ≠ 0} :
  Nimber.kappa ((nth Nat.Prime k) ^ n) = Nimber.kappa_q k n := by
  sorry

theorem kappa_pow_eq_alpha (k : ℕ) :
  (Nimber.kappa (nth Nat.Prime k)) ^ (nth Nat.Prime k) = Nimber.alpha (nth Nat.Prime k) := by
  sorry

theorem kappa_pow_decrease (k n : ℕ) {h : n ≠ 0} :
  (Nimber.kappa ((nth Nat.Prime k) ^ (n + 1))) ^ (nth Nat.Prime k)
  = (Nimber.kappa ((nth Nat.Prime k) ^ n)) := by
  sorry

/-
TODO: lexicographic ordering of kappa's ?
-/

theorem wpow_wpow_w_isAlgClosed : IsAlgClosed tau := by
  sorry

end Nimber

end
