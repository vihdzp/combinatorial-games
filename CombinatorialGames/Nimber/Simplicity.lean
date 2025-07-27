/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/
import CombinatorialGames.Nimber.Field
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Simplest extension theorems

We say that a nimber `x` is a group when the lower set `Iio x` is closed under addition. Likewise,
we say that `x` is a ring when `Iio x` is closed under addition and multiplication, and we say that
`x` is a field when it's closed under addition, multiplication, and division.

This file aims to prove the four parts of the simplest extension theorem:

- If `x` is not a group, then `x` can be written as `y + z` for some `y, z < x`.
- If `x` is a group but not a ring, then `x` can be written as `y * z` for some `y, z < x`.
- If `x` is a ring but not a field, then `x` can be written as `y⁻¹` for some `y < x`.
- If `x` is a field that isn't algebraically complete, then `x` is the root of some polynomial with
  coefficients `< x`.
-/

open Polynomial Set

namespace Nimber

/-- A nimber `x` is a group when `Iio x` is closed under addition. Note that `0` is a group under
this definition. -/
@[mk_iff]
structure IsGroup (x : Nimber) where
  add_lt {y z} (hy : y < x) (hz : z < x) : y + z < x

theorem IsGroup.zero : IsGroup 0 where
  add_lt := by simp

/-- A nimber `x` is a ring when `Iio x` is closed under addition and multiplication. Note that `0`
is a ring under this definition. -/
@[mk_iff]
structure IsRing (x : Nimber) extends IsGroup x where
  mul_lt {y z} (hy : y < x) (hz : z < x) : y * z < x

theorem IsRing.zero : IsRing 0 where
  mul_lt := by simp
  __ := IsGroup.zero

/-- A nimber `x` is a field when `Iio x` is closed under addition, multiplication, and division.
Note that `0` is a field under this definition. -/
@[mk_iff]
structure IsField (x : Nimber) extends IsRing x where
  inv_lt {y} (hy : y < x) : y⁻¹ < x

theorem IsField.zero : IsField 0 where
  inv_lt := by simp
  __ := IsRing.zero

theorem IsField.div_lt {x y z : Nimber} (h : IsField x) (hy : y < x) (hz : z < x) : y / z < x :=
  h.toIsRing.mul_lt hy (h.inv_lt hz)

/-- A nimber `x` is algebraically closed when `IsField x`, and every polynomial in the nimbers with
coefficients less than `x` has a root that's less than `x`. Note that `0` is algebraically closed
under this definition. -/
@[mk_iff]
structure IsAlgClosed (x : Nimber) extends IsRing x where
  has_root {p : Nimber[X]} (hp : ∀ n, p.coeff n < x) : ∃ r < x, p.IsRoot r

theorem IsAlgClosed.zero : IsAlgClosed 0 where
  has_root := by simp
  __ := IsField.zero

/-- The first **simplest extension theorem**: if `x` is not a group, then `x` can be written as
`y + z` for some `y, z < x`. -/
theorem exists_add_of_not_isGroup {x : Nimber} (h : ¬ IsGroup x) : ∃ y < x, ∃ z < x, y + z = x := by
  simp_rw [isGroup_iff, not_forall, not_lt] at h
  obtain ⟨y, z, hy, hz, hx⟩ := h
  obtain ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, H⟩ := exists_minimal_of_wellFoundedLT
    (fun p : Iio x × Iio x ↦ x ≤ p.1 + p.2) ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, hx⟩
  refine ⟨y, hy, z, hz, H.1.antisymm' (add_le_of_forall_ne ?_ ?_)⟩ <;> intro a ha hax
  · exact H.not_lt (y := ⟨⟨a, ha.trans hy⟩, _⟩) hax.ge (Prod.lt_of_lt_of_le ha le_rfl)
  · exact H.not_lt (y := ⟨_, ⟨a, ha.trans hz⟩⟩) hax.ge (Prod.lt_of_le_of_lt le_rfl ha)


#exit
end Nimber


open Ordinal in
private theorem two_opow_aux {a : Ordinal} :
    (∀ b < ∗(2 ^ a), ∀ c < ∗(2 ^ a), b + c < ∗(2 ^ a)) ∧
      ∀ b < 2 ^ a, ∗(2 ^ a + b) = ∗(2 ^ a) + ∗b := by
  refine ⟨fun b hb c hc ↦ ?_, fun b ↦ ?_⟩
  · induction b with | h b =>
    induction c with | h c =>
    obtain rfl | hb₀ := eq_or_ne b 0; simpa
    obtain rfl | hc₀ := eq_or_ne c 0; simpa
    have hb' : log 2 b < a := (lt_opow_iff_log_lt one_lt_two hb₀).1 hb
    have hc' : log 2 c < a := (lt_opow_iff_log_lt one_lt_two hc₀).1 hc
    have hm {x y : Ordinal} : x % 2 ^ y < 2 ^ y :=
      Ordinal.mod_lt _ (Ordinal.opow_ne_zero _ two_ne_zero)
    rw [← two_opow_log_add hb₀, ← two_opow_log_add hc₀, two_opow_aux.2 _ hm, two_opow_aux.2 _ hm]
    -- TODO: it'd be nicer to use `wlog`, but it breaks the termination checker.
    have H {x y} (hxy : log 2 x < log 2 y) (IH : log 2 y < a) :
        ∗(2 ^ log 2 y) + ∗(y % 2 ^ log 2 y) + (∗(2 ^ log 2 x) + ∗(x % 2 ^ log 2 x)) < ∗(2 ^ a) := by
      have H' : ∗(y % 2 ^ log 2 y) + (∗(2 ^ log 2 x) + ∗(x % 2 ^ log 2 x)) < ∗(2 ^ log 2 y) := by
        apply two_opow_aux.1 _ hm _ (two_opow_aux.1 ..)
        · rwa [toNimber.lt_iff_lt, opow_lt_opow_iff_right one_lt_two]
        · exact hm.trans ((opow_lt_opow_iff_right one_lt_two).2 hxy)
      rw [add_assoc, ← toOrdinal_toNimber (∗(y % _) + _)]
      apply (two_opow_aux.2 _ H').symm.trans_lt
      rw [← toOrdinal.lt_iff_lt] at H' ⊢
      apply (add_left_strictMono H').trans_le
      dsimp
      rwa [← Ordinal.mul_two, ← opow_succ, opow_le_opow_iff_right one_lt_two, succ_le_iff]
    obtain hbc | hbc | hbc := lt_trichotomy (log 2 b) (log 2 c)
    · rw [add_comm]
      exact H hbc hc'
    · rw [hbc, ← add_assoc, add_comm (∗(2 ^ _)), add_cancel_right]
      apply (two_opow_aux.1 _ hm _ hm).trans
      rwa [toNimber.lt_iff_lt, opow_lt_opow_iff_right one_lt_two]
    · exact H hbc hb'
  · induction b using Ordinal.induction with | h b IH =>
    intro hb
    apply le_antisymm
    · sorry
    · apply add_le_of_forall_ne <;> intro c hc
      ·
termination_by a

theorem lt_two_opow {a : Ordinal} {b c : Nimber} (hb : b < ∗(2 ^ a)) (hc : c < ∗(2 ^ a)) :
    b + c < ∗(2 ^ a) :=
  two_opow_aux.1 b hb c hc

/-- A version of `lt_two_opow` stated using only ordinals. -/
theorem lt_two_opow' {a b c : Ordinal} (hb : b < 2 ^ a) (hc : c < 2 ^ a) : ∗b + ∗c < ∗(2 ^ a) :=
  lt_two_opow hb hc

/-- As a consequence of this as `add_self`, nimber addition is the same as XORing the base 2
Cantor Normal Forms of two ordinals. -/
theorem two_opow_add {a b : Ordinal} (h : b < 2 ^ a) : ∗(2 ^ a + b) = ∗(2 ^ a) + ∗b :=
  two_opow_aux.2 b h
