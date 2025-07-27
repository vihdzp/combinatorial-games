/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/
import CombinatorialGames.Nimber.Field
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.SetTheory.Ordinal.Exponential

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

## Todo

We are currently at 1/4.
-/

open Ordinal Polynomial Set

/-! ### Mathlib lemmas -/

namespace Ordinal

theorem div_two_opow_log {o : Ordinal} (ho : o ≠ 0) : o / 2 ^ log 2 o = 1 := by
  apply le_antisymm
  · simpa [← succ_one] using div_opow_log_lt o one_lt_two
  · simpa [← succ_zero] using div_opow_log_pos 2 ho

theorem two_opow_log_add {o : Ordinal} (ho : o ≠ 0) : 2 ^ log 2 o + o % 2 ^ log 2 o = o := by
  convert div_add_mod .. using 2
  rw [div_two_opow_log ho, mul_one]

protected theorem mul_two (o : Ordinal) : o * 2 = o + o := by
  rw [← one_add_one_eq_two, mul_add, mul_one]

end Ordinal

namespace Nimber

/-! ### Groups -/

/-- Add two nimbers as ordinal numbers. -/
scoped notation:65 x:arg "+ₒ" y:arg => ∗(toOrdinal x + toOrdinal y)

/-- A nimber `x` is a group when `Iio x` is closed under addition. Note that `0` is a group under
this definition. -/
@[mk_iff]
structure IsGroup (x : Nimber) where
  add_lt {y z} (hy : y < x) (hz : z < x) : y + z < x

theorem IsGroup.zero : IsGroup 0 where
  add_lt := by simp

theorem IsGroup.le_add_self {x y : Nimber} (h : IsGroup x) (hy : y < x) : x ≤ x + y := by
  by_contra!
  simpa using h.add_lt this hy

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

/-- A version of `IsGroup.mul_add_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsGroup.mul_add_eq_of_lt' {x y : Ordinal} (h : IsGroup (∗x)) (hy : y < x) (z : Ordinal) :
    ∗(x * z + y) = ∗(x * z) + ∗y := by
  obtain rfl | hx₀ := eq_or_ne x 0; simp
  apply le_antisymm
  · sorry
  · apply add_le_of_forall_ne
    all_goals
      intro a ha
      induction' a with a
      rw [toNimber.lt_iff_lt] at ha
    · have hx : a % x < x := mod_lt _ hx₀
      have hx' : toOrdinal (∗(a % x) + ∗y) < x := h.add_lt hx hy
      have IH : a / toOrdinal x < z := (Ordinal.div_lt hx₀).2 ha
      rw [← div_add_mod a, h.mul_add_eq_of_lt' hx, add_assoc, ← toNimber_toOrdinal (_ + ∗y),
        ← h.mul_add_eq_of_lt' hx', ne_eq, toNimber.eq_iff_eq]
      apply ((add_left_strictMono hx').trans_le ((le_add_right .. ).trans' _)).ne
      simp_rw [← mul_succ]
      apply mul_le_mul_left'
      simpa
    · rw [← h.mul_add_eq_of_lt' (ha.trans hy)]
      simpa using ha.ne
termination_by (z, y)

theorem IsGroup.mul_add_eq_of_lt {x y : Nimber} (h : IsGroup x) (hy : y < x) (z : Ordinal) :
    ∗(toOrdinal x * z + toOrdinal y) = ∗(toOrdinal x * z) + ∗y :=
  h.mul_add_eq_of_lt' hy z

theorem IsGroup.add_eq_of_lt {x y : Nimber} (h : IsGroup x) (hy : y < x) : x +ₒ y = x + y := by
  simpa using h.mul_add_eq_of_lt hy 1

/-- A version of `IsGroup.add_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsGroup.add_eq_of_lt' {x y : Ordinal} (h : IsGroup (∗x)) (hy : y < x) :
    x + y = toOrdinal (∗x + ∗y) :=
  h.add_eq_of_lt hy

theorem IsGroup.two_opow (x : Ordinal) : IsGroup (∗(2 ^ x)) := by
  refine ⟨@fun y z hy hz ↦ ?_⟩
  induction y with | h y =>
  induction z with | h z =>
  obtain rfl | hy₀ := eq_or_ne y 0; simpa
  obtain rfl | hz₀ := eq_or_ne z 0; simpa
  have hy' : log 2 y < x := by rwa [← lt_opow_iff_log_lt one_lt_two hy₀]
  have hz' : log 2 z < x := by rwa [← lt_opow_iff_log_lt one_lt_two hz₀]
  have hm {x y : Ordinal} : x % 2 ^ y < 2 ^ y := mod_lt _ (opow_ne_zero _ two_ne_zero)
  rw [← two_opow_log_add hy₀, ← two_opow_log_add hz₀,
    (two_opow _).add_eq_of_lt' hm, (two_opow _).add_eq_of_lt' hm]
  -- TODO: it'd be nicer to use `wlog` here, but it breaks the termination checker.
  have H {a b} (hab : log 2 a < log 2 b) (IH : log 2 b < x) :
      ∗(2 ^ log 2 b) + ∗(b % 2 ^ log 2 b) + (∗(2 ^ log 2 a) + ∗(a % 2 ^ log 2 a)) < ∗(2 ^ x) := by
    have H' : ∗(b % 2 ^ log 2 b) + (∗(2 ^ log 2 a) + ∗(a % 2 ^ log 2 a)) < ∗(2 ^ log 2 b) := by
      apply (two_opow _).add_lt hm ((two_opow _).add_lt ..)
      · rwa [toNimber.lt_iff_lt, opow_lt_opow_iff_right one_lt_two]
      · exact hm.trans ((opow_lt_opow_iff_right one_lt_two).2 hab)
    rw [add_assoc]
    apply ((two_opow _).add_eq_of_lt H').symm.trans_lt
    rw [← toOrdinal.lt_iff_lt] at H' ⊢
    apply (add_left_strictMono H').trans_le
    dsimp
    rwa [← Ordinal.mul_two, ← opow_succ, opow_le_opow_iff_right one_lt_two, Order.succ_le_iff]
  obtain hyz | hyz | hyz := lt_trichotomy (log 2 y) (log 2 z)
  · rw [add_comm]
    exact H hyz hz'
  · dsimp
    rw [hyz, ← add_assoc, add_comm (∗(2 ^ _)), add_cancel_right]
    apply ((two_opow _).add_lt hm hm).trans
    rwa [toNimber.lt_iff_lt, opow_lt_opow_iff_right one_lt_two]
  · exact H hyz hy'
termination_by x

theorem two_opow_log_add {o : Ordinal} (ho : o ≠ 0) : ∗(2 ^ log 2 o) + ∗(o % 2 ^ log 2 o) = ∗o :=
  ((IsGroup.two_opow _).add_eq_of_lt (mod_lt _ (opow_ne_zero _ two_ne_zero))).symm.trans
    (o.two_opow_log_add ho)

/-- The nimbers that are groups are exactly `0` and the powers of `2`. -/
theorem isGroup_iff_zero_or_mem_range_two_opow {x : Ordinal} :
    IsGroup x ↔ x = 0 ∨ x ∈ range fun y : Ordinal ↦ ∗(2 ^ y) := by
  constructor
  · by_contra! H
    obtain ⟨h, hx, hx'⟩ := H
    apply ((h.add_lt (x := ∗x) ..).trans_eq (two_opow_log_add hx).symm).false
    · rw [toNimber.lt_iff_lt]
      apply (opow_log_le_self _ hx).lt_of_ne
      contrapose! hx'
      exact hx' ▸ mem_range_self _
    · exact mod_opow_log_lt_self _ hx
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · exact .zero
    · exact .two_opow x

/-! ### Rings -/

/-- A nimber `x` is a ring when `Iio x` is closed under addition and multiplication. Note that `0`
is a ring under this definition. -/
@[mk_iff]
structure IsRing (x : Nimber) extends IsGroup x where
  mul_lt {y z} (hy : y < x) (hz : z < x) : y * z < x

theorem IsRing.zero : IsRing 0 where
  mul_lt := by simp
  __ := IsGroup.zero

/-! ### Fields -/

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

/-! ### Algebraically closed fields -/

/-- A nimber `x` is algebraically closed when `IsField x`, and every polynomial in the nimbers with
coefficients less than `x` has a root that's less than `x`. Note that `0` is algebraically closed
under this definition. -/
@[mk_iff]
structure IsAlgClosed (x : Nimber) extends IsRing x where
  has_root {p : Nimber[X]} (hp : ∀ n, p.coeff n < x) : ∃ r < x, p.IsRoot r

theorem IsAlgClosed.zero : IsAlgClosed 0 where
  has_root := by simp
  __ := IsField.zero

end Nimber
