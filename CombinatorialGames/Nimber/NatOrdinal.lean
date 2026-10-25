/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.NatOrdinal.Basic
public import CombinatorialGames.Nimber.SimplestExtension.Basic

import CombinatorialGames.NatOrdinal.Pow
import CombinatorialGames.Nimber.Omega
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Bounds for nimber arithmetic

We prove that the sum of two nimbers is bounded by their natural sum, and likewise for the product.
As a corollary of these bounds, `∗(ω ^ ω ^ x)` is always a ring.
-/

public section

open Ordinal

universe u

private theorem Ordinal.isPrincipal_mul_opow_omega0 {x : Ordinal} (hx : 1 < x) :
    IsPrincipal (· * ·) (x ^ ω) := by
  intro a b ha hb
  simp_rw [(isNormal_opow hx).lt_iff_exists_lt isSuccLimit_omega0, lt_omega0] at ha hb
  obtain ⟨_, ⟨m, rfl⟩, hm⟩ := ha
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hb
  apply (mul_le_mul' hm.le hn.le).trans_lt
  rw [← opow_add, opow_lt_opow_iff_right hx, ← Nat.cast_add]
  exact natCast_lt_omega0 _

namespace Nimber

/-! ### Addition -/

/-- A version of `add_le_nadd` stated in terms of `Ordinal`. -/
theorem add_le_nadd' (a b : Ordinal) : (∗a + ∗b).val ≤ (NatOrdinal.of a + NatOrdinal.of b).val := by
  rw [val_le_iff]
  apply add_le_of_forall_ne
  all_goals
    intro c hc
    cases c with | of c
    rw [← val_eq_iff.ne]
    apply ((add_le_nadd' ..).trans_lt _).ne
    simpa
termination_by (a, b)

theorem add_le_nadd (a b : Nimber) : a + b ≤ ∗(NatOrdinal.of a.val + NatOrdinal.of b.val).val :=
  add_le_nadd' ..

/-! ### Multiplication -/

private theorem exists_of_natCast_mul_eq (m n : ℕ) : ∃ k : ℕ, ∗m * ∗n = ∗k := by
  simp_rw [← val_eq_iff, ← lt_omega0]
  apply IsField.omega0.mul_lt <;> simp

private theorem two_opow_log_lt {a : Ordinal} (ha : a % 2 ^ log 2 a ≠ 0) :
    2 ^ log 2 a < a := by
  have ha₀ : a ≠ 0 := by rintro rfl; simp at ha
  conv_rhs => rw [← Ordinal.two_opow_log_add ha₀]
  rwa [lt_add_iff_pos_right, pos_iff_ne_zero]

private theorem natCast_mul_natCast_le_nmul (m n : ℕ) :
    Nimber.val.{u} (∗m * ∗n) ≤ m * n := by
  rw [mul_def', val_sInf, Set.preimage_compl, ← natCast_mul, ← card_le_nat,
    ← Cardinal.lift_le.{u + 1}, Cardinal.lift_natCast]
  grw [Ordinal.lift_card_sInf_compl_le, of_preimage, Cardinal.mk_image_le, Cardinal.mk_image_le]
  simp

private theorem mul_natCast_le_nmul (x : Ordinal) (n : ℕ) :
    (∗x * ∗n).val ≤ (NatOrdinal.of x * n).val := by
  obtain rfl | hx₀ := eq_or_ne x 0; · simp
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hx' := mod_lt x (opow_ne_zero (log ω x) omega0_ne_zero)
  rw [← div_add_mod x (ω ^ log ω x), hm,
    of_omega0_opow_mul_natCast_add hx', NatOrdinal.of_omega0_opow_mul_natCast_add' hx',
    add_mul, add_mul, val_le_iff]
  apply (add_le_nadd ..).trans
  rw [of.le_iff_le, NatOrdinal.val.le_iff_le, ← NatOrdinal.of_omega0_opow]
  apply add_le_add <;> rw [NatOrdinal.of_le_iff]
  · obtain ⟨k, hk⟩ := exists_of_natCast_mul_eq m n
    rw [mul_assoc, mul_assoc, ← Nat.cast_mul, NatOrdinal.of_omega0_opow, hk,
      ← of_omega0_opow_mul_natCast, ← NatOrdinal.of_omega0_opow_mul_natCast, val_of,
      NatOrdinal.val_of]
    apply mul_le_mul_right
    rw [← of.le_iff_le, ← hk, ← val_le_iff, Ordinal.natCast_mul]
    exact natCast_mul_natCast_le_nmul m n
  · have := mod_opow_log_lt_self ω hx₀
    apply mul_natCast_le_nmul
termination_by x

/-- A version of `mul_le_nmul` stated in terms of `Ordinal`. -/
theorem mul_le_nmul' (a b : Ordinal) : (∗a * ∗b).val ≤ (NatOrdinal.of a * NatOrdinal.of b).val := by
  -- `a = 0` or `b = 0` are trivial.
  obtain rfl | ha₀ := eq_or_ne a 0; · simp
  obtain rfl | hb₀ := eq_or_ne b 0; · simp
  -- By the inductive hypothesis, we can assume `a`, `b` are powers of `2`.
  by_cases! ha : a % 2 ^ log 2 a ≠ 0
  · rw [← two_opow_log_add ha₀, ← NatOrdinal.two_opow_log_add ha₀]
    simp_rw [add_mul, val_le_iff]
    apply (add_le_nadd ..).trans
    rw [of.le_iff_le, NatOrdinal.val.le_iff_le]
    have := two_opow_log_lt ha
    have := mod_opow_log_lt_self 2 ha₀
    apply add_le_add <;> exact mul_le_nmul' ..
  by_cases! hb : b % 2 ^ log 2 b ≠ 0
  · rw [← two_opow_log_add hb₀, ← NatOrdinal.two_opow_log_add hb₀]
    simp_rw [mul_add, val_le_iff]
    apply (add_le_nadd ..).trans
    rw [of.le_iff_le, NatOrdinal.val.le_iff_le]
    have := two_opow_log_lt hb
    have := mod_opow_log_lt_self 2 hb₀
    apply add_le_add <;> exact mul_le_nmul' ..
  rw [← two_opow_log_add ha₀, ← NatOrdinal.two_opow_log_add ha₀,
    ← two_opow_log_add hb₀, ← NatOrdinal.two_opow_log_add hb₀]
  simp_rw [ha, hb, of_zero, NatOrdinal.of_zero, add_zero]
  -- Using `mul_le_nmul_natCast`, we can in fact assume `a`, `b` are powers of `ω`.
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.1 (mod_lt (log 2 a) omega0_ne_zero)
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.1 (mod_lt (log 2 b) omega0_ne_zero)
  have IHa : 2 ^ log 2 a ≤ a := opow_log_le_self _ ha₀
  have IHb : 2 ^ log 2 b ≤ b := opow_log_le_self _ hb₀
  rw [← div_add_mod (log 2 a) ω, hm] at IHa ⊢
  rw [← div_add_mod (log 2 b) ω, hn] at IHb ⊢
  simp_rw [opow_add, opow_mul, ofNat_opow_omega0, opow_natCast] at IHa IHb ⊢
  replace IHa := (Ordinal.le_mul_left _ (pow_pos two_pos m)).trans IHa
  replace IHb := (Ordinal.le_mul_left _ (pow_pos two_pos n)).trans IHb
  rw [← Nat.cast_ofNat]
  simp_rw [← natCast_pow, of_omega0_opow_mul_natCast, NatOrdinal.of_omega0_opow_mul_natCast]
  obtain ⟨k, hk⟩ := exists_of_natCast_mul_eq (2 ^ m) (2 ^ n)
  rw [mul_mul_mul_comm, mul_mul_mul_comm (G := NatOrdinal), ← of_val (of _ * _), hk]
  apply (mul_natCast_le_nmul ..).trans
  rw [NatOrdinal.val.le_iff_le]
  apply mul_le_mul'
  · rw [NatOrdinal.of_le_iff, val_le_iff]
    -- The result now follows from the inductive hypothesis, as well as the fact `ω ^ ω ^ x` is
    -- closed under natural multiplication.
    apply mul_le_of_forall_ne
    intro c hc d hd
    cases c with | of c
    cases d with | of d
    rw [of.lt_iff_lt] at hc hd
    have H₁ := hc.trans_le IHa
    have H₂ := hd.trans_le IHb
    have : toLex (ω ^ (log 2 a / ω), d) < toLex (a, b) := by
      rw [Prod.Lex.toLex_lt_toLex']
      exact ⟨IHa, fun _ ↦ H₂⟩
    apply ne_of_lt
    apply (add_le_nadd ..).trans_lt
    rw [← NatOrdinal.wpow_add]
    apply NatOrdinal.add_lt_wpow
    · rw [NatOrdinal.of_lt_iff, val_lt_iff]
      apply (add_le_nadd ..).trans_lt
      rw [NatOrdinal.val_wpow, of.lt_iff_lt, NatOrdinal.val_lt_iff]
      apply NatOrdinal.add_lt_wpow
      all_goals
      · rw [NatOrdinal.of_lt_iff]
        apply (mul_le_nmul' ..).trans_lt
        rw [NatOrdinal.val.lt_iff_lt, NatOrdinal.wpow_add, NatOrdinal.of_omega0_opow]
        first | rw [mul_lt_mul_iff_left₀] | rw [mul_lt_mul_iff_right₀]
        · rwa [← NatOrdinal.of_omega0_opow, NatOrdinal.of.lt_iff_lt]
        · exact NatOrdinal.wpow_pos _
    · rw [NatOrdinal.of_lt_iff]
      apply (mul_le_nmul' ..).trans_lt
      rw [NatOrdinal.val.lt_iff_lt, NatOrdinal.wpow_add]
      exact mul_lt_mul'' hc hd zero_le zero_le
  · rw [← val_eq_iff, ← NatOrdinal.of.eq_iff_eq, NatOrdinal.of_natCast] at hk
    rw [← hk, NatOrdinal.of_le_iff]
    exact mul_natCast_le_nmul ..
termination_by (a, b)
decreasing_by
  on_goal 6 => assumption
  all_goals decreasing_tactic

theorem mul_le_nmul (a b : Nimber) : a * b ≤ ∗(NatOrdinal.of a.val * NatOrdinal.of b.val).val :=
  mul_le_nmul' ..

theorem IsRing.omega0_omega0_opow (x : Ordinal) : IsRing (∗(ω ^ ω ^ x)) where
  ne_one := by
    rw [of_ne_one, ← opow_zero ω, ne_eq, opow_right_inj one_lt_omega0]
    exact opow_ne_zero _ omega0_ne_zero
  mul_lt x y hx hy := (mul_le_nmul ..).trans_lt (NatOrdinal.mul_lt_wpow_wpow hx hy)
  __ := IsGroup.omega0_opow _

theorem IsRing.opow_omega0 {x : Ordinal} (hx : 1 < x) : IsRing (∗(x ^ ω)) := by
  obtain (hx' | ⟨y, hy⟩) := isPrincipal_mul_iff_le_two_or_omega0_opow_opow.1 <|
    isPrincipal_mul_opow_omega0 hx
  · absurd hx'.not_gt
    apply (natCast_lt_omega0 2).trans_le
    conv_lhs => rw [← natCast_opow_omega0 one_lt_two]
    apply opow_le_opow_left
    rwa [Nat.cast_ofNat, ← one_add_one_eq_two, Order.add_one_le_iff]
  · rw [← hy]
    exact IsRing.omega0_omega0_opow _

end Nimber
end
