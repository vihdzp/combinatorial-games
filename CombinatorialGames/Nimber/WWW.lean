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
A possible follow-up is to prove that arithmetic in `w ^ (w ^ w)` is effectively computable.

The proof follows [On Numbers And Games][conway2001] (pp. 59-61),
[On The Algebraic Closure Of Two][lenstra1977] (pp. 1-8) and
[Combinatorial Games][siegel2013] (pp. 444-450).

## Todo

Formalize pp. 59-61.
Formalize pp. 1-8.
Formalize pp.444-450.
-/

universe u

open Ordinal
open Nat (nth)

/-! ### Prime lemmas -/

theorem one_lt_nth_prime (k : ℕ) : 1 < nth Nat.Prime k := by
  apply lt_of_lt_of_le (b := 2) (by norm_num)
  exact le_trans (b := k + 2) (Nat.le_add_left 2 k) (Nat.add_two_le_nth_prime k)

theorem nth_prime_ne_zero (k : ℕ) : nth Nat.Prime k ≠ 0 := by
  rw [Nat.ne_zero_iff_zero_lt]
  exact lt_trans zero_lt_one (one_lt_nth_prime k)

/-! ### Main lemmas -/

noncomputable section

namespace Nimber

/- First we prove the algebraic closure. -/

/-- `kappa_q` where `q = (nth Nat.Prime k) ^ (n + 1)` -/
protected def kappa_q (k n : ℕ) : Nimber.{u} :=
  of <| 2 ^ (ω ^ k * (nth Nat.Prime k) ^ n)

protected theorem kappa_q_lt_iff_pair_lt (k n k' n' : ℕ) :
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

/-- `alpha_p` where `p = nth Nat.Prime (k + 1)` -/
protected def alpha_p (k : ℕ) : Nimber.{u} :=
  sInf {x | x < Nimber.kappa_q (k + 1) 0 ∧
    ∀ y < Nimber.kappa_q (k + 1) 0, y ^ (nth Nat.Prime (k + 1)) ≠ x}

@[simp]
protected theorem alpha_p_zero : Nimber.alpha_p 0 = ∗2 := by
  sorry

theorem omega0_cubed_eq_three : (∗ω) ^ 3 = ∗2 := by
  sorry

/-- Theorem 4.5 on p. 446. -/
protected theorem kappa_q_pow_reduce :
  ∀ (k : ℕ), (Nimber.kappa_q.{u} (k + 1) 0) ^ (nth Nat.Prime (k + 1)) = Nimber.alpha_p.{u} k ∧
  (∀ (n : ℕ), (Nimber.kappa_q.{u} (k + 1) (n + 1)) ^ (nth Nat.Prime (k + 1)) =
  (Nimber.kappa_q.{u} (k + 1) n) ∧ IsField (Nimber.kappa_q.{u} (k + 1) n)) ∧
  IsNthDegreeClosed (nth Nat.Prime (k + 1)) (Nimber.kappa_q.{u} (k + 2) 0) := by
  intro k
  induction k with
  | zero =>
    simp [Nimber.kappa_q]
    rw [opow_omega0 (by simp) (by exact nat_lt_omega0 2)]
    refine ⟨omega0_cubed_eq_three, ?_, ?_⟩
    · sorry
    · sorry
  | succ k ih =>
    sorry

protected theorem kappa_q_pow_eq_alpha (k : ℕ) :
  (Nimber.kappa_q.{u} (k + 1) 0) ^ (nth Nat.Prime (k + 1)) =
  Nimber.alpha_p.{u} k := by
  exact Nimber.kappa_q_pow_reduce k |>.1

protected theorem kappa_q_pow_decrease (k n : ℕ) :
  (Nimber.kappa_q.{u} (k + 1) (n + 1)) ^ (nth Nat.Prime (k + 1)) =
  (Nimber.kappa_q.{u} (k + 1) n) := by
  exact Nimber.kappa_q_pow_reduce k |>.2.1 n |>.1

/-- Add two ordinals as nimbers. -/
scoped notation:65 x:65 "+ₙᵢₘ" y:66 => val (∗x + ∗y)

protected theorem base_two_expansion (x : Nimber.{u}) :
  (CNF 2 x.val).foldr (fun p r ↦ 2 ^ p.1 * p.2 +ₙᵢₘ r) 0 = x.val := by
  sorry

private def tau : Nimber.{u} := ∗(ω ^ (ω ^ ω))

private def tau' : Nimber.{u} :=
  sInf {x | IsAlgClosed x}

private theorem tau'_eq_tau : tau' = tau := by
  sorry

/-- public name is more explicit -/
theorem wpow_wpow_w_first_isAlgClosed :
  sInf {x | IsAlgClosed x} = ∗(ω ^ (ω ^ ω)) := by exact tau'_eq_tau

/- Then we prove effective arithmetic. -/

protected def field_two : Subfield Nimber := Subfield.closure ∅

protected def degree (x : Nimber.{u}) : ℕ :=
  (minpoly Nimber.field_two x).natDegree

protected def kappa (h : ℕ) : Nimber.{u} :=
  sInf {x | x < tau ∧ h ∣ Nimber.degree x}

protected theorem kappa_q_of_kappa (k n : ℕ) :
  Nimber.kappa ((nth Nat.Prime k) ^ (n + 1)) = Nimber.kappa_q k n := by
  sorry

end Nimber

end
