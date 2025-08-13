/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/
import CombinatorialGames.Nimber.Field
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic.ComputeDegree

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

The proof follows Aaron Siegel's Combinatorial Games, pp. 440-444.

## Todo

We are currently at 3/4.
-/

open Ordinal Polynomial Set

/-! ### Mathlib lemmas -/

/-! ### Order lemmas -/

-- #27703
theorem le_of_forall_ne {α : Type*} [LinearOrder α] {x y : α} (h : ∀ z < x, z ≠ y) : x ≤ y := by
  contrapose! h
  use y

-- #27701
theorem lt_add_iff_lt_or_exists_lt {α : Type*} [Add α] [LinearOrder α] [CanonicallyOrderedAdd α]
    [AddLeftReflectLT α] [IsLeftCancelAdd α] {a b c : α} :
    a < b + c ↔ a < b ∨ ∃ d < c, a = b + d := by
  obtain h | h := lt_or_ge a b
  · have : a < b + c := h.trans_le (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp

theorem forall_lt_add {α : Type*} [Add α] [LinearOrder α] [CanonicallyOrderedAdd α]
    [AddLeftReflectLT α] [IsLeftCancelAdd α] {b c : α} {P : α → Prop} :
    (∀ a < b + c, P a) ↔ (∀ a < b, P a) ∧ (∀ a < c, P (b + a)) := by
  simp_rw [lt_add_iff_lt_or_exists_lt]
  aesop

theorem exists_lt_add {α : Type*} [Add α] [LinearOrder α] [CanonicallyOrderedAdd α]
    [AddLeftReflectLT α] [IsLeftCancelAdd α] {b c : α} {P : α → Prop} :
    (∃ a < b + c, P a) ↔ (∃ a < b, P a) ∨ (∃ a < c, P (b + a)) := by
  simp_rw [lt_add_iff_lt_or_exists_lt]
  aesop

theorem le_add_iff_lt_or_exists_le {α : Type*} [Add α] [LinearOrder α] [CanonicallyOrderedAdd α]
    [AddLeftMono α] [IsLeftCancelAdd α] {a b c : α} :
    a ≤ b + c ↔ a < b ∨ ∃ d ≤ c, a = b + d := by
  obtain h | h := lt_or_ge a b
  · have : a ≤ b + c := h.le.trans (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp

theorem forall_le_add {α : Type*} [Add α] [LinearOrder α] [CanonicallyOrderedAdd α]
    [AddLeftMono α] [IsLeftCancelAdd α] {b c : α} {P : α → Prop} :
    (∀ a ≤ b + c, P a) ↔ (∀ a < b, P a) ∧ (∀ a ≤ c, P (b + a)) := by
  simp_rw [le_add_iff_lt_or_exists_le]
  aesop

theorem exists_le_add {α : Type*} [Add α] [LinearOrder α] [CanonicallyOrderedAdd α]
    [AddLeftMono α] [IsLeftCancelAdd α] {b c : α} {P : α → Prop} :
    (∃ a ≤ b + c, P a) ↔ (∃ a < b, P a) ∨ (∃ a ≤ c, P (b + a)) := by
  simp_rw [le_add_iff_lt_or_exists_le]
  aesop

theorem Maximal.isGreatest {α : Type*} [LinearOrder α] {P : α → Prop} {x : α} (h : Maximal P x) :
    IsGreatest {y | P y} x := by
  refine ⟨h.1, fun y hy ↦ ?_⟩
  by_contra! hx
  exact (h.le_of_ge hy hx.le).not_gt hx

/-! #### Ordinal lemmas-/

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

theorem lt_mul_iff {a b c : Ordinal} : a < b * c ↔ ∃ q < c, ∃ r < b, a = b * q + r := by
  obtain rfl | hb₀ := eq_or_ne b 0; simp
  refine ⟨fun h ↦ ⟨_, (Ordinal.div_lt hb₀).2 h, _, mod_lt a hb₀, (div_add_mod ..).symm⟩, ?_⟩
  rintro ⟨q, hq, r, hr, rfl⟩
  apply (add_left_strictMono hr).trans_le
  simp_rw [← mul_succ]
  exact mul_le_mul_left' (Order.succ_le_iff.mpr hq) _

theorem forall_lt_mul {b c : Ordinal} {P : Ordinal → Prop} :
    (∀ a < b * c, P a) ↔ ∀ q < c, ∀ r < b, P (b * q + r) := by
  simp_rw [lt_mul_iff]
  aesop

theorem exists_lt_mul {b c : Ordinal} {P : Ordinal → Prop} :
    (∃ a < b * c, P a) ↔ ∃ q < c, ∃ r < b, P (b * q + r) := by
  simp_rw [lt_mul_iff]
  aesop

theorem mul_add_lt {a b c d : Ordinal} (h₁ : c < a) (h₂ : b < d) : a * b + c < a * d := by
  apply lt_of_lt_of_le (b := a * (Order.succ b))
  · rwa [mul_succ, add_lt_add_iff_left]
  · apply mul_le_mul_left'
    rwa [Order.succ_le_iff]

-- TODO: come up with a better name, probably rename `log_eq_zero` while we're at it.
theorem log_eq_zero' {b x : Ordinal} (hb : b ≤ 1) : log b x = 0 := by
  obtain rfl | rfl := Ordinal.le_one_iff.1 hb <;> simp

theorem log_eq_zero_iff {b x : Ordinal} : log b x = 0 ↔ b ≤ 1 ∨ x < b := by
  constructor
  · by_contra!
    apply (le_log_of_opow_le (c := 1) this.2.1 (by simpa using this.2.2)).not_gt
    simpa using this.1
  · rintro (hb | hb)
    · exact log_eq_zero' hb
    · exact log_eq_zero hb

instance : CanonicallyOrderedAdd Ordinal where
  le_self_add := le_add_right

attribute [simp] principal_zero Ordinal.not_lt_zero

protected theorem Principal.sSup {op : Ordinal → Ordinal → Ordinal} {s : Set Ordinal}
    (H : ∀ x ∈ s, Principal op x) : Principal op (sSup s) := by
  have : Principal op (sSup ∅) := by simp
  by_cases hs : BddAbove s; swap; rwa [csSup_of_not_bddAbove hs]
  obtain rfl | hs' := s.eq_empty_or_nonempty; assumption
  refine fun x y hx hy ↦ ?_
  rw [lt_csSup_iff hs hs'] at *
  obtain ⟨a, has, ha⟩ := hx
  obtain ⟨b, hbs, hb⟩ := hy
  refine ⟨_, max_rec' _ has hbs, max_rec ?_ ?_⟩ <;> intro hab
  · exact H a has ha (hb.trans_le hab)
  · exact H b hbs (ha.trans_le hab) hb

protected theorem Principal.iSup {op : Ordinal → Ordinal → Ordinal} {ι} {f : ι → Ordinal}
    (H : ∀ i, Principal op (f i)) : Principal op (⨆ i, f i) := by
  apply Principal.sSup
  simpa

end Ordinal

/-! #### Polynomial lemmas -/

namespace Polynomial

variable {R : Type*} [Semiring R] {p : R[X]}

@[simp]
theorem coeffs_nonempty_iff : p.coeffs.Nonempty ↔ p ≠ 0 := by
  simp [Finset.nonempty_iff_ne_empty]

theorem natDegree_eq_zero_iff : p.natDegree = 0 ↔ p = 0 ∨ p.degree = 0 := by
  rw [p.natDegree_eq_zero_iff_degree_le_zero, le_iff_lt_or_eq, ← WithBot.coe_zero, ← bot_eq_zero',
    WithBot.lt_coe_bot, p.degree_eq_bot]

alias ⟨_, IsRoot.mul_div_eq⟩ := mul_div_eq_iff_isRoot

end Polynomial

theorem inv_eq_self_iff {α : Type*} [DivisionRing α] {a : α} :
    a⁻¹ = a ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  obtain rfl | ha := eq_or_ne a 0; simp
  rw [← mul_eq_one_iff_inv_eq₀ ha, ← pow_two, sq_eq_one_iff]
  tauto

theorem self_eq_inv_iff {α : Type*} [DivisionRing α] {a : α} :
    a = a⁻¹ ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  rw [eq_comm, inv_eq_self_iff]

namespace Nimber

/-! ### Groups -/

/-- Add two nimbers as ordinal numbers. -/
scoped notation:65 x:65 "+ₒ" y:66 => ∗(val x + val y)

/-- A nimber `x` is a group when `Iio x` is closed under addition. Note that `0` is a group under
this definition. -/
@[mk_iff]
structure IsGroup (x : Nimber) where
  add_lt ⦃y z⦄ (hy : y < x) (hz : z < x) : y + z < x

theorem IsGroup.sum_lt {x : Nimber} (h : IsGroup x) (hx₀ : x ≠ 0) {ι} {s : Finset ι}
    {f : ι → Nimber} (hs : ∀ y ∈ s, f y < x) : s.sum f < x := by
  classical
  induction s using Finset.induction with
  | empty => simp_all [Nimber.pos_iff_ne_zero]
  | insert a s ha IH =>
    rw [Finset.sum_insert ha]
    apply h.add_lt <;> aesop

/-- `Iio x` as a subgroup of `Nimber`. -/
def IsGroup.toAddSubgroup {x : Nimber} (h : IsGroup x) (hx₀ : x ≠ 0) : AddSubgroup Nimber where
  carrier := Iio x
  zero_mem' := Nimber.pos_iff_ne_zero.2 hx₀
  add_mem' := @h.add_lt
  neg_mem' := id

@[simp]
theorem val_toAddSubgroup_lt {x : Nimber} (h : IsGroup x) (hx₀ : x ≠ 0) (y : h.toAddSubgroup hx₀) :
    y < x := y.2

@[simp]
theorem IsGroup.zero : IsGroup 0 where
  add_lt := by simp

@[simp]
theorem IsGroup.one : IsGroup 1 where
  add_lt := by simp

theorem IsGroup.of_le_one {x : Nimber} (h : x ≤ 1) : IsGroup x := by
  obtain rfl | rfl := Nimber.le_one_iff.1 h <;> simp

protected theorem IsGroup.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsGroup x) :
    IsGroup (sSup s) :=
  ⟨Principal.sSup (fun x hx ↦ (H x hx).add_lt)⟩

protected theorem IsGroup.iSup {ι} {f : ι → Nimber} (H : ∀ i, IsGroup (f i)) :
    IsGroup (⨆ i, f i) := by
  apply IsGroup.sSup
  simpa

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
  apply le_antisymm
  · apply le_of_forall_ne
    simp_rw [← of.toEquiv.forall_congr_right, RelIso.coe_fn_toEquiv, OrderIso.lt_iff_lt]
    rw [forall_lt_add, forall_lt_mul]
    refine ⟨fun a ha b hb ↦ ?_, fun a ha ↦ ?_⟩
    · have hx : val (∗b + ∗y) < x := h.add_lt hb hy
      rw [ne_eq, h.mul_add_eq_of_lt' hb, ← CharTwo.add_eq_iff_eq_add, add_assoc,
        ← of_val (∗b + _), ← h.mul_add_eq_of_lt' hx]
      exact (mul_add_lt hx ha).ne
    · rw [h.mul_add_eq_of_lt' (ha.trans hy)]
      simpa using ha.ne
  · apply add_le_of_forall_ne <;>
      simp_rw [← of.toEquiv.forall_congr_right, RelIso.coe_fn_toEquiv, OrderIso.lt_iff_lt]
    · rw [forall_lt_mul]
      intro a ha b hb
      have hx : val (∗b + ∗y) < x := h.add_lt hb hy
      rw [ne_eq, h.mul_add_eq_of_lt' hb, add_assoc, ← of_val (∗b + _), ← h.mul_add_eq_of_lt' hx]
      exact ((mul_add_lt hx ha).trans_le (Ordinal.le_add_right ..)).ne
    · intro b hb
      rw [ne_eq, ← h.mul_add_eq_of_lt' (hb.trans hy)]
      simpa using hb.ne
termination_by (z, y)

theorem IsGroup.mul_add_eq_of_lt {x y : Nimber} (h : IsGroup x) (hy : y < x) (z : Ordinal) :
    ∗(val x * z + val y) = ∗(val x * z) + y :=
  h.mul_add_eq_of_lt' hy z

theorem IsGroup.add_eq_of_lt {x y : Nimber} (h : IsGroup x) (hy : y < x) : x +ₒ y = x + y := by
  simpa using h.mul_add_eq_of_lt hy 1

/-- A version of `IsGroup.add_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsGroup.add_eq_of_lt' {x y : Ordinal} (h : IsGroup (∗x)) (hy : y < x) :
    x + y = val (∗x + ∗y) :=
  h.add_eq_of_lt hy

theorem IsGroup.two_opow (x : Ordinal) : IsGroup (∗(2 ^ x)) := by
  refine ⟨fun y z hy hz ↦ ?_⟩
  induction y with | mk y
  induction z with | mk z
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
      apply (two_opow _).add_lt hm ((two_opow _).add_lt _ _)
      · rwa [of.lt_iff_lt, opow_lt_opow_iff_right one_lt_two]
      · exact hm.trans ((opow_lt_opow_iff_right one_lt_two).2 hab)
    rw [add_assoc]
    apply ((two_opow _).add_eq_of_lt H').symm.trans_lt
    rw [← val.lt_iff_lt] at H' ⊢
    apply (add_left_strictMono H').trans_le
    dsimp
    rwa [← Ordinal.mul_two, ← opow_succ, opow_le_opow_iff_right one_lt_two, Order.succ_le_iff]
  obtain hyz | hyz | hyz := lt_trichotomy (log 2 y) (log 2 z)
  · rw [add_comm]
    exact H hyz hz'
  · dsimp
    rw [hyz, ← add_assoc, add_comm (∗(2 ^ _)), add_cancel_right]
    apply ((two_opow _).add_lt hm hm).trans
    rwa [of.lt_iff_lt, opow_lt_opow_iff_right one_lt_two]
  · exact H hyz hy'
termination_by x

theorem two_opow_log_add {o : Ordinal} (ho : o ≠ 0) : ∗(2 ^ log 2 o) + ∗(o % 2 ^ log 2 o) = ∗o :=
  ((IsGroup.two_opow _).add_eq_of_lt (mod_lt _ (opow_ne_zero _ two_ne_zero))).symm.trans
    (o.two_opow_log_add ho)

theorem add_lt_of_log_eq {a b : Ordinal} (ha₀ : a ≠ 0) (hb₀ : b ≠ 0) (h : log 2 a = log 2 b) :
    ∗a + ∗b < ∗(2 ^ log 2 a) := by
  rw [← two_opow_log_add ha₀, ← two_opow_log_add hb₀, h]
  abel_nf
  rw [CharTwo.two_zsmul, zero_add]
  apply (IsGroup.two_opow _).add_lt <;> exact mod_lt _ (opow_ne_zero _ two_ne_zero)

theorem exists_isGroup_add_lt {x : Nimber} (hx : x ≠ 0) : ∃ y ≤ x, IsGroup y ∧ x + y < y := by
  induction x with | mk x
  refine ⟨_, opow_log_le_self _ hx, .two_opow _, ?_⟩
  exact add_lt_of_log_eq hx (opow_ne_zero _ two_ne_zero) (log_opow one_lt_two _).symm

/-- The nimbers that are groups are exactly `0` and the powers of `2`. -/
theorem isGroup_iff_zero_or_mem_range_two_opow {x : Nimber} :
    IsGroup x ↔ x = 0 ∨ x ∈ range fun y : Ordinal ↦ ∗(2 ^ y) := by
  constructor
  · by_contra! H
    obtain ⟨h, hx, hx'⟩ := H
    apply ((h.add_lt (x := ∗x) _ _).trans_eq (two_opow_log_add hx).symm).false
    · rw [of.lt_iff_lt]
      apply (opow_log_le_self _ hx).lt_of_ne
      contrapose! hx'
      exact hx' ▸ mem_range_self _
    · exact mod_opow_log_lt_self _ hx
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · exact .zero
    · exact .two_opow x

/-- A version of `isGroup_iff_zero_or_mem_range_two_opow` stated in terms of `Ordinal`. -/
theorem isGroup_iff_zero_or_mem_range_two_opow' {x : Ordinal} :
    IsGroup (∗x) ↔ x = 0 ∨ x ∈ range (2 ^ · : Ordinal → _) :=
  isGroup_iff_zero_or_mem_range_two_opow

/-! ### Rings -/

/-- Multiply two nimbers as ordinal numbers. -/
scoped notation:70 x:70 "*ₒ" y:71 => ∗(val x * val y)

/-- A nimber `x` is a ring when `Iio x` is closed under addition and multiplication. Note that `0`
is a ring under this definition. -/
@[mk_iff]
structure IsRing (x : Nimber) extends IsGroup x where
  mul_lt ⦃y z⦄ (hy : y < x) (hz : z < x) : y * z < x

theorem IsRing.pow_lt' {x y : Nimber} (h : IsRing x) {n : ℕ} (hn : n ≠ 0) (hy : y < x) :
    y ^ n < x := by
  induction n using Nat.twoStepInduction with
  | zero => contradiction
  | one => simpa
  | more n _ IH => rw [pow_succ]; exact h.mul_lt (IH n.succ_ne_zero) hy

theorem IsRing.pow_lt {x y : Nimber} (h : IsRing x) {n : ℕ} (hx : 1 < x) (hy : y < x) :
    y ^ n < x := by
  obtain rfl | hn := eq_or_ne n 0
  · simpa
  · exact h.pow_lt' hn hy

private theorem p_eq_zero_of_le_one {x : Nimber} {p : Nimber[X]}
    (hx₁ : x ≤ 1) (h : ∀ k, p.coeff k < x) : p = 0 := by
  ext k; simpa using (h k).trans_le hx₁

theorem IsRing.eval_lt {x y : Nimber} (h : IsRing x) {p : Nimber[X]} (hp : ∀ k, p.coeff k < x)
    (hy : y < x) : p.eval y < x := by
  obtain hx₁ | hx₁ := le_or_gt x 1
  · have := p_eq_zero_of_le_one hx₁ hp
    simp_all
  · rw [eval_eq_sum]
    exact h.sum_lt hx₁.ne_bot fun n hn ↦ h.mul_lt (hp _) (h.pow_lt hx₁ hy)

/-- `Iio x` as a subring of `Nimber`. -/
def IsRing.toSubring {x : Nimber} (h : IsRing x) (hx₁ : 1 < x) : Subring Nimber where
  one_mem' := hx₁
  mul_mem' := @h.mul_lt
  __ := h.toAddSubgroup (by aesop)

@[simp]
theorem val_toSubring_lt {x : Nimber} (h : IsRing x) (hx₁ : 1 < x) (y : h.toSubring hx₁) :
    y < x := y.2

@[simp]
theorem IsRing.zero : IsRing 0 where
  mul_lt := by simp
  __ := IsGroup.zero

@[simp]
theorem IsRing.one : IsRing 1 where
  mul_lt := by simp
  __ := IsGroup.one

theorem IsRing.of_le_one {x : Nimber} (h : x ≤ 1) : IsRing x := by
  obtain rfl | rfl := Nimber.le_one_iff.1 h <;> simp

protected theorem IsRing.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsRing x) :
    IsRing (sSup s) :=
  ⟨IsGroup.sSup fun x hx ↦ (H x hx).toIsGroup, Principal.sSup fun x hx ↦ (H x hx).mul_lt⟩

protected theorem IsRing.iSup {ι} {f : ι → Nimber} (H : ∀ i, IsRing (f i)) :
    IsRing (⨆ i, f i) := by
  apply IsRing.sSup
  simpa

/-- The second **simplest extension theorem**: if `x` is a group but not a ring, then `x` can be
written as `y * z` for some `y, z < x`. -/
theorem exists_mul_of_not_isRing {x : Nimber} (h' : IsGroup x) (h : ¬ IsRing x) :
    ∃ y < x, ∃ z < x, y * z = x := by
  simp_rw [isRing_iff, h', true_and, not_forall, not_lt] at h
  obtain ⟨y, z, hy, hz, hx⟩ := h
  obtain ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, H⟩ := exists_minimal_of_wellFoundedLT
    (fun p : Iio x × Iio x ↦ x ≤ p.1 * p.2) ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, hx⟩
  refine ⟨y, hy, z, hz, H.1.antisymm' (mul_le_of_forall_ne ?_)⟩
  refine fun a ha b hb hx ↦ hx.not_lt (h'.add_lt (h'.add_lt ?_ ?_) ?_) <;> by_contra! hx
  · exact H.not_lt (y := (⟨a, ha.trans hy⟩, ⟨z, hz⟩)) hx (Prod.lt_of_lt_of_le ha le_rfl)
  · exact H.not_lt (y := (⟨y, hy⟩, ⟨b, hb.trans hz⟩)) hx (Prod.lt_of_le_of_lt le_rfl hb)
  · exact H.not_lt (y := (⟨a, ha.trans hy⟩, ⟨b, hb.trans hz⟩)) hx (Prod.lt_of_lt_of_le ha hb.le)

/-- A version of `IsRing.mul_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsRing.mul_eq_of_lt' {x y z : Ordinal} (hx : IsRing (∗x)) (hy : IsGroup (∗y))
    (hyx : y ≤ x) (hzy : z < y) (H : ∀ z < y, (∗z)⁻¹ < ∗x) : x * z = val (∗x * ∗z) := by
  apply le_antisymm
  · apply le_of_forall_ne
    rw [forall_lt_mul]
    intro a ha b hb
    rw [ne_eq, ← of_eq_iff, hx.mul_add_eq_of_lt' hb,
      hx.mul_eq_of_lt' hy hyx (ha.trans hzy) H, add_comm, CharTwo.add_eq_iff_eq_add,
      of_val, ← mul_add]
    obtain hza | hza := eq_or_ne (∗z + ∗a) 0
    · cases ha.ne' (add_eq_zero.1 hza)
    · rw [← div_eq_iff hza]
      exact (hx.mul_lt hb (H _ (hy.add_lt hzy (ha.trans hzy)))).ne
  · rw [val_le_iff]
    refine mul_le_of_forall_ne fun a ha b hb ↦ ?_
    rw [add_comm, ← add_assoc, ← mul_add, add_comm]
    induction b with | mk b
    rw [of.lt_iff_lt] at hb
    have hx' : val (a * (∗b + ∗z)) < x :=
      hx.mul_lt ha (hx.add_lt (hb.trans (hzy.trans_le hyx)) (hzy.trans_le hyx))
    rw [← of_val (_ * _), ← hx.mul_eq_of_lt' hy hyx (hb.trans hzy) H,
      ← of_val (a * _), ← hx.mul_add_eq_of_lt' hx']
    exact (mul_add_lt hx' hb).ne
termination_by z

theorem IsRing.mul_eq_of_lt {x y z : Nimber} (hx : IsRing x) (hy : IsGroup y)
    (hyx : y ≤ x) (hzy : z < y) (H : ∀ z < y, z⁻¹ < x) : x *ₒ z = x * z :=
  hx.mul_eq_of_lt' hy hyx hzy H

/-! ### Fields -/

/-- A nimber `x` is a field when `Iio x` is closed under addition, multiplication, and division.
Note that `0` and `1` are fields under this definition.

For simplicity, the constructor takes a redundant `y ≠ 0` assumption. The lemma `IsField.inv_lt`
proves that this theorem applies when `y = 0` as well. -/
@[mk_iff]
structure IsField (x : Nimber) extends IsRing x where
  inv_lt' ⦃y⦄ (hy₀ : y ≠ 0) (hy : y < x) : y⁻¹ < x

theorem IsField.inv_lt {x y : Nimber} (h : IsField x) (hy : y < x) : y⁻¹ < x := by
  obtain rfl | hy₀ := eq_or_ne y 0
  · simpa
  · exact h.inv_lt' hy₀ hy

theorem IsField.div_lt {x y z : Nimber} (h : IsField x) (hy : y < x) (hz : z < x) : y / z < x :=
  h.toIsRing.mul_lt hy (h.inv_lt hz)

/-- `Iio x` as a subring of `Nimber`. -/
def IsField.toSubfield {x : Nimber} (h : IsField x) (hx₁ : 1 < x) : Subfield Nimber where
  inv_mem' := @h.inv_lt
  __ := h.toSubring hx₁

@[simp]
theorem val_toSubfield_lt {x : Nimber} (h : IsField x) (hx₁ : 1 < x) (y : h.toSubfield hx₁) :
    y < x := y.2

noncomputable instance {x : Nimber} (h : IsField x) (hx₁ : 1 < x) : Field (h.toSubring hx₁) :=
  inferInstanceAs (Field (h.toSubfield hx₁))

@[simp]
theorem IsField.zero : IsField 0 where
  inv_lt' := by simp
  __ := IsRing.zero

@[simp]
theorem IsField.one : IsField 1 where
  inv_lt' := by simp
  __ := IsRing.one

theorem IsField.of_le_one {x : Nimber} (h : x ≤ 1) : IsField x := by
  obtain rfl | rfl := Nimber.le_one_iff.1 h <;> simp

theorem IsField.mul_eq_of_lt {x y : Nimber} (h : IsField x) (hyx : y < x) : x *ₒ y = x * y :=
  h.toIsRing.mul_eq_of_lt h.toIsGroup le_rfl hyx @h.inv_lt

/-- A version of `IsField.mul_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsField.mul_eq_of_lt' {x y : Ordinal} (hx : IsField (∗x)) (hyx : y < x) :
    x * y = val (∗x * ∗y) :=
  hx.mul_eq_of_lt hyx

-- One day we'll get rid of this wretched simp lemma.
attribute [-simp] add_one_eq_succ in
private theorem inv_lt_of_not_isField_aux {x : Nimber} (h' : IsRing x) (h : ¬ IsField x) :
    x⁻¹ < x ∧ ∀ y < x⁻¹, y⁻¹ < x := by
  have hx₁ : 1 < x := lt_of_not_ge <| mt IsField.of_le_one h
  have hx₀ : x ≠ 0 := hx₁.ne_bot
  let s := {z | x ≤ z⁻¹}
  simp_rw [isField_iff, h', true_and, not_forall, not_lt] at h
  obtain ⟨a, _, ha, hxa⟩ := h
  have hsx : sInf s < x := (csInf_le' (s := s) hxa).trans_lt ha
  have hxs : x ≤ (sInf s)⁻¹ := csInf_mem (s := s) ⟨a, hxa⟩
  obtain ⟨y, hys, hy, hsy⟩ := exists_isGroup_add_lt (x := sInf s) fun _ ↦ by simp_all
  have Hs (y) (hy : y < sInf s) : y⁻¹ < x := lt_of_not_ge (notMem_of_lt_csInf' (s := s) hy)
  have Hs' (z) (hy : z < y) : z⁻¹ < x := Hs _ (hy.trans_le hys)
  suffices x * y = x * (sInf s + y) + 1 by
    rw [add_comm, CharTwo.eq_add_iff_add_eq, ← mul_add, add_comm, add_cancel_right] at this
    rw [inv_eq_of_mul_eq_one_right this]
    exact ⟨hsx, Hs⟩
  have hyx := hys.trans_lt hsx
  rw [← h'.mul_eq_of_lt hy hyx.le hsy Hs', ← h'.mul_add_eq_of_lt hx₁]
  · apply le_antisymm
    · refine mul_le_of_forall_ne fun a ha b hb ↦ ?_
      rw [add_comm, ← add_assoc, ← mul_add, add_comm]
      have hax := h'.mul_lt ha (h'.add_lt (hb.trans hyx) hyx)
      rw [← h'.mul_eq_of_lt hy hyx.le hb Hs', ← h'.mul_add_eq_of_lt hax]
      · rw [ne_eq, of.eq_iff_eq, val_one]
        intro H
        have H' : _ / _ = _ / _ := congrArg (· / val x) H
        have hx₀ : val x ≠ 0 := hx₀
        have hx₁ : 1 < val x := hx₁
        rw [mul_add_div _ hx₀, mul_add_div _ hx₀, div_eq_zero_of_lt (val.lt_iff_lt.2 hax),
          div_eq_zero_of_lt hx₁, add_zero, add_zero, val.eq_iff_eq] at H'
        apply ha.not_ge (hxs.trans_eq (inv_eq_of_mul_eq_one_left _))
        simpa [H'] using H
    · rw [← val.le_iff_le]
      apply le_of_forall_ne
      simp_rw [val_one, add_one_eq_succ, val_of, Order.lt_succ_iff,
        le_iff_eq_or_lt, forall_eq_or_imp, forall_lt_mul, ne_eq, ← of_eq_iff]
      refine ⟨?_, fun a ha b hb ↦ ?_⟩
      · rw [h'.mul_eq_of_lt hy hyx.le hsy Hs', mul_right_inj' hx₀]
        exact hsy.ne
      · have hay : ∗a < y := ha.trans hsy
        rw [← of_lt_iff] at hb
        refine ne_of_eq_of_ne ?_ (mul_ne_of_ne (a' := ∗b / (∗a + y)) ?_ hay.ne)
        · rw [add_comm, ← add_assoc, ← mul_add, div_mul_cancel₀ _ (add_ne_zero_iff.2 hay.ne),
            ← val_of b, h'.mul_add_eq_of_lt hb, ← h'.mul_eq_of_lt hy hyx.le hay Hs']
          exact add_comm ..
        · apply (h'.mul_lt hb (Hs ..)).ne
          rw [← add_comm, ← hy.add_eq_of_lt hay, of_lt_iff]
          apply (add_lt_add_left ha _).trans_eq
          rw [← of_eq_iff, hy.add_eq_of_lt hsy, add_comm, add_cancel_right]

theorem inv_lt_of_not_isField {x y : Nimber} (h' : IsRing x) (h : ¬ IsField x) (hy : y < x⁻¹) :
    y⁻¹ < x :=
  (inv_lt_of_not_isField_aux h' h).2 y hy

theorem inv_le_of_not_isField {x y : Nimber} (h' : IsRing x) (h : ¬ IsField x) (hy : y ≤ x⁻¹) :
    y⁻¹ ≤ x := by
  obtain rfl | hy := hy.eq_or_lt; simp
  exact (inv_lt_of_not_isField h' h hy).le

/-- The third **simplest extension theorem**: if `x` is a ring but not a field, then `x` can be
written as `y⁻¹` for some `y < x`. In simpler wording, `x⁻¹ < x`. -/
theorem inv_lt_self_of_not_isField {x : Nimber} (h' : IsRing x) (h : ¬ IsField x) : x⁻¹ < x :=
  (inv_lt_of_not_isField_aux h' h).1

-- TODO: characterize nim arithmetic on the naturals.
proof_wanted IsRing.two_two_pow (n : ℕ) : IsRing (∗(2 ^ 2 ^ n))

-- TODO: this follows directly from `IsRing.two_two_pow` and the surjectivity of `a * ·` for `a ≠ 0`.
proof_wanted IsField.two_two_pow (n : ℕ) : IsField (∗(2 ^ 2 ^ n))

/-! ### Polynomials -/

/-- Reinterpret a polynomial in the nimbers as a polynomial in the subfield `x`.

We could define this under the weaker assumption `IsRing`, but due to proof erasure, this leads to
issues where `Field (h.toSubring ⋯)` can't be inferred, even if `h : IsField x`. -/
def IsField.embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) (p : Nimber[X])
    (hp : ∀ k, p.coeff k < x) : (h.toSubfield hx₁)[X] :=
  .ofFinsupp <| .mk p.support (fun k ↦ ⟨p.coeff k, hp k⟩) (by simp [← Subtype.val_inj])

@[simp]
theorem IsField.coeff_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) (k : ℕ) : (h.embed hx₁ p hp).coeff k = ⟨p.coeff k, hp k⟩ :=
  rfl

@[simp]
theorem IsField.map_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) : (h.embed hx₁ p hp).map (Subring.subtype _) = p := by
  ext; simp

theorem forall_coeff_C_lt {x y : Nimber} (hy : y < x) (k) : (C y).coeff k < x := by
  rw [coeff_C]
  split_ifs
  · assumption
  · exact hy.bot_lt

@[simp]
theorem IsField.embed_C {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {y} {hy} :
    h.embed hx₁ (C y) hy = C ⟨y, by simpa using hy 0⟩ := by
  ext
  simp_rw [h.coeff_embed, coeff_C]
  split_ifs <;> rfl

theorem IsField.val_eval_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) (y) : (h.embed hx₁ p hp).eval y = p.eval y.1 := by
  simp [embed, sum, eval_eq_sum]

@[simp]
theorem IsField.eval_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) (y) : (h.embed hx₁ p hp).eval y = ⟨_, h.eval_lt hp y.2⟩ := by
  rw [← Subtype.val_inj, h.val_eval_embed]

@[simp]
theorem IsField.degree_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) : (h.embed hx₁ p hp).degree = p.degree := by
  conv_rhs => rw [← h.map_embed hx₁ hp]
  exact (degree_map_eq_of_injective (Subring.subtype_injective _) _).symm

/-! ### n-th degree closed fields -/

/-- A nimber `x` is `n`-th degree closed when `IsRing x`, and every non-constant polynomial in the
nimbers with degree less or equal to `n` and coefficients less than `x` has a root that's less than
`x`. Note that `0` and `1` are `n`-th degree closed under this definition.

We don't extend `IsField x`, as for `1 ≤ n`, this predicate implies it.

For simplicity, the constructor takes a `0 < p.degree` assumption. The theorem
`IsNthDegreeClosed.has_root` proves that this theorem applies (vacuously) when `p = 0` as well. -/
@[mk_iff]
structure IsNthDegreeClosed (n : ℕ) (x : Nimber) extends IsRing x where
  has_root' ⦃p : Nimber[X]⦄ (hp₀ : 0 < p.degree) (hpn : p.degree ≤ n) (hp : ∀ k, p.coeff k < x) :
    ∃ r < x, p.IsRoot r

theorem IsNthDegreeClosed.has_root {n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x) {p : Nimber[X]}
    (hp₀ : p.degree ≠ 0) (hpn : p.degree ≤ n) (hp : ∀ k, p.coeff k < x) : ∃ r < x, p.IsRoot r := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · aesop
  · apply h.has_root' _ hpn hp
    cases _ : p.degree <;> simp_all [Nat.pos_iff_ne_zero]

theorem IsNthDegreeClosed.le {m n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x) (hmn : m ≤ n) :
    IsNthDegreeClosed m x where
  has_root' _p hp₀ hpm := h.has_root' hp₀ (hpm.trans (mod_cast hmn))
  __ := h.toIsRing

theorem IsNthDegreeClosed.of_le_one (n : ℕ) {x : Nimber} (h : x ≤ 1) : IsNthDegreeClosed n x where
  has_root' p hp₀ _ hp := by
    have := p_eq_zero_of_le_one h hp
    simp_all
  __ := IsRing.of_le_one h

@[simp]
theorem IsNthDegreeClosed.zero (n : ℕ) : IsNthDegreeClosed n 0 :=
  .of_le_one n zero_le_one

@[simp]
theorem IsNthDegreeClosed.one (n : ℕ) : IsNthDegreeClosed n 1 :=
  .of_le_one n le_rfl

protected theorem IsNthDegreeClosed.sSup {n : ℕ} {s : Set Nimber}
    (H : ∀ x ∈ s, IsNthDegreeClosed n x) : IsNthDegreeClosed n (sSup s) := by
  have : IsNthDegreeClosed n (sSup ∅) := by simp
  by_cases hs : BddAbove s; swap; rwa [csSup_of_not_bddAbove hs]
  obtain rfl | hs' := s.eq_empty_or_nonempty; assumption
  refine ⟨IsRing.sSup fun x hx ↦ (H x hx).toIsRing, fun p hp₀ hpn hp ↦ ?_⟩
  simp_rw [lt_csSup_iff hs hs'] at *
  choose f hf using hp
  obtain ⟨c, hc⟩ := ((Finset.range (p.natDegree + 1)).image f).exists_maximal (by simp)
  have hc' := hc.1
  simp_rw [Finset.mem_image, Finset.mem_range, Nat.lt_succ] at hc'
  obtain ⟨n, hn, rfl⟩ := hc'
  have := (H _ (hf n).1).has_root' hp₀ hpn fun m ↦ ?_
  · obtain ⟨r, hr, hr'⟩ := this
    exact ⟨r, ⟨_, (hf n).1, hr⟩, hr'⟩
  · obtain hm | hm := le_or_gt m p.natDegree
    · apply (hf m).2.trans_le (hc.isGreatest.2 _)
      aesop (add simp [Nat.lt_succ])
    · rw [coeff_eq_zero_of_natDegree_lt hm]
      exact bot_le.trans_lt (hf n).2

protected theorem IsNthDegreeClosed.iSup {n : ℕ} {ι} {f : ι → Nimber}
    (H : ∀ i, IsNthDegreeClosed n (f i)) : IsNthDegreeClosed n (⨆ i, f i) := by
  apply IsNthDegreeClosed.sSup
  simpa

/-- If `x` is a field, to prove it `n`-th degree closed, it suffices to check *monic* polynomials of
degree less or equal to `n`. -/
theorem IsNthDegreeClosed.ofMonic {n : ℕ} {x : Nimber} (h : IsField x)
    (hp : ∀ p : Nimber[X], p.Monic → 0 < p.degree → p.degree ≤ n → (∀ k, p.coeff k < x) →
      ∃ r < x, p.IsRoot r) : IsNthDegreeClosed n x where
  has_root' p hp₀ hpn hp' := by
    have hp₀' : p ≠ 0 := by rintro rfl; simp at hp₀
    have hm : (C p.leadingCoeff⁻¹ * p).Monic := by simp [Monic, hp₀']
    have hd : (C p.leadingCoeff⁻¹ * p).degree = p.degree := by compute_degree!
    have := hp _ hm (hd ▸ hp₀) (hd ▸ hpn) fun k ↦ ?_
    · aesop
    · rw [coeff_C_mul, inv_mul_eq_div]
      exact h.div_lt (hp' k) (hp' _)
  __ := h

@[simp]
theorem isNthDegreeClosed_zero_iff_isRing {x : Nimber} : IsNthDegreeClosed 0 x ↔ IsRing x := by
  refine ⟨IsNthDegreeClosed.toIsRing, fun h ↦ ⟨h, fun p ↦ ?_⟩⟩
  cases _ : p.degree <;> aesop

theorem IsNthDegreeClosed.toIsField {n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x) (hn : 0 < n) :
    IsField x := by
  obtain hx₁ | hx₁ := le_or_gt x 1
  · exact IsField.of_le_one hx₁
  · refine ⟨h.toIsRing, fun y hy₀ hy ↦ ?_⟩
    have hp : degree (C y * (X : Nimber[X]) + 1) = 1 := by compute_degree!
    have ⟨r, hr, hr₀⟩ := h.has_root (hp ▸ one_ne_zero) (by simpa [hp]) fun k ↦ ?_
    · convert hr
      apply inv_eq_of_mul_eq_one_right
      rw [← Nimber.add_eq_zero]
      simpa using hr₀
    · obtain hk | hk := le_or_gt k 1
      · obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.1 hk <;> simpa [coeff_one]
      · rw [coeff_eq_zero_of_degree_lt]
        · exact zero_lt_one.trans hx₁
        · simp_all

@[simp]
theorem isNthDegreeClosed_one_iff_isField {x : Nimber} : IsNthDegreeClosed 1 x ↔ IsField x := by
  refine ⟨(IsNthDegreeClosed.toIsField · one_pos), (.ofMonic · fun p hm hp₀ hp₁ hp ↦ ?_)⟩
  rw [Polynomial.eq_X_add_C_of_degree_le_one hp₁] at hp ⊢
  have : p.natDegree = 1 := by
    apply natDegree_eq_of_degree_eq_some
    rw [← Order.succ_le_iff] at hp₀
    exact hp₁.antisymm hp₀
  rw [Monic, leadingCoeff] at hm
  have := hp 0
  aesop

-- We could have proved this earlier, but going through `IsNthDegreeClosed`
-- gives a much shorter proof.
protected theorem IsField.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsField x) :
    IsField (sSup s) := by
  simp_rw [← isNthDegreeClosed_one_iff_isField] at *
  exact IsNthDegreeClosed.sSup H

protected theorem IsField.iSup {ι} {f : ι → Nimber} (H : ∀ i, IsField (f i)) :
    IsField (⨆ i, f i) := by
  apply IsField.sSup
  simpa

theorem IsNthDegreeClosed.has_root_subring {n : ℕ} {x : Nimber} (hx₁ : 1 < x)
    (h : IsNthDegreeClosed n x) {p : (h.toSubring hx₁)[X]}
    (hp₀ : p.degree ≠ 0) (hpn : p.degree ≤ n) : ∃ r, p.IsRoot r := by
  have hd : (p.map (Subring.subtype _)).degree = p.degree := by simpa using (em _).symm
  obtain ⟨r, hr, hr'⟩ := h.has_root (hd ▸ hp₀) (hd ▸ hpn) (by simp)
  exact ⟨⟨r, hr⟩, (isRoot_map_iff (Subring.subtype_injective _)).1 hr'⟩


theorem IsNthDegreeClosed.splits_subring {n : ℕ} {x : Nimber} (hx₁ : 1 < x)
    (h : IsNthDegreeClosed n x) (h' : IsField x) {p : (h.toSubring hx₁)[X]} (hpn : p.degree ≤ n) :
    p.Splits (h'.subringMap hx₁) := by
  let F := h'.toSubfield hx₁
  obtain hp₀ | hp₀ := le_or_gt p.degree 0
  · exact splits_of_degree_le_one _ (hp₀.trans zero_le_one)
  induction n with
  | zero => cases hp₀.not_ge hpn
  | succ n IH =>
    obtain ⟨r, hr⟩ := h.has_root_subring hx₁ hp₀.ne' hpn
    rw [← hr.mul_div_eq (R := F)]
    apply splits_mul _ (splits_X_sub_C _)
    -- TODO: how do we avoid the def-eq abuse here?
    let q : F[X] := @HDiv.hDiv F[X] F[X] _ _ p (X - C r)
    obtain hp₀' | hp₀' := le_or_gt q.degree 1
    · exact splits_of_degree_le_one _ hp₀'
    · apply IH (h.le n.le_succ)
      · rw [← Order.lt_succ_iff]
        apply (degree_div_lt (R := F) _ _).trans_le hpn <;> aesop
      · exact zero_lt_one.trans hp₀'

set_option maxHeartbeats 500000 in
theorem IsNthDegreeClosed.eq_prod_roots_of_degree_le {n : ℕ} {x : Nimber}
    (h : IsNthDegreeClosed n x) {p : Nimber[X]} (hpn : p.degree ≤ n) (hp : ∀ k, p.coeff k < x) :
    p = C p.leadingCoeff * (p.roots.map fun a ↦ X - C a).prod := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  obtain hx₁ | hx₁ := le_or_gt x 1
  · cases hp₀ (p_eq_zero_of_le_one hx₁ hp)
  obtain rfl | hn₀ := n.eq_zero_or_pos
  · cases hp' : p.degree
    · simp_all
    · have hp₀ : p.degree = 0 := by simp_all
      rw [p.eq_C_of_degree_eq_zero hp₀]
      simp
  · have h' := h.toIsField hn₀
    let F := h'.toSubfield hx₁
    have := eq_prod_roots_of_splits (K := F) (i := .id _)
      (h.splits_subring hx₁ h' (p := h.embed hx₁ p hp) (by simpa))
    apply_fun Polynomial.map (Subfield.subtype F) at this
    convert ← this
    · rw [map_map]
      exact h.map_embed hx₁ hp
    · simp
      congr
      have := map_multiset_prod (Subring.subtype _) ((h.embed hx₁ p hp).roots.map (fun a ↦ X - C a))
      rw [← map_multiset_prod]

#exit
theorem pow_add_prod_ne_pow {x : Nimber} {n : ℕ} {f : Fin n → Nimber} (hf : ∀ i, f i < x) :
    x ^ n ≠ x∏ i : Fin n, (x + f i) := by
  sorry

theorem IsNthDegreeClosed.foldr_mul_add_eq_of_lt {n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x)
    (l : List Nimber) (hl : ∀ y ∈ l, y < x) (hln : l.length ≤ n + 1) :
    l.zipIdx.foldr (fun a b ↦ a.1 * x ^ a.2 + b) 0 =
    of (l.zipIdx.foldr (fun a b ↦ a.1.val * x.val ^ a.2 + b) 0) := by
  sorry


#exit

proof_wanted IsNthDegreeClosed.omega0 : IsNthDegreeClosed 2 (∗ω)

/-! ### Algebraically closed fields -/

/-- A nimber `x` is algebraically closed when `IsRing x`, and every non-constant polynomial in the
nimbers with coefficients less than `x` has a root that's less than `x`. Note that `0` and `1` are
algebraically closed under this definition.

For simplicity, the constructor takes a `0 < p.degree` assumption. The theorem
`IsAlgClosed.has_root` proves that this theorem applies (vacuously) when `p = 0` as well. -/
@[mk_iff]
structure IsAlgClosed (x : Nimber) extends IsRing x where
  has_root' ⦃p : Nimber[X]⦄ (hp₀ : 0 < p.degree) (hp : ∀ k, p.coeff k < x) : ∃ r < x, p.IsRoot r

theorem IsAlgClosed.toIsNthDegreeClosed {x : Nimber} (h : IsAlgClosed x) (n : ℕ) :
    IsNthDegreeClosed n x where
  has_root' _p hp₀ _ := h.has_root' hp₀
  __ := h

@[coe]
theorem IsAlgClosed.toIsField {x : Nimber} (h : IsAlgClosed x) : IsField x :=
  (h.toIsNthDegreeClosed 1).toIsField one_pos

theorem isAlgClosed_iff_forall {x : Nimber} : IsAlgClosed x ↔ ∀ n, IsNthDegreeClosed n x where
  mp := IsAlgClosed.toIsNthDegreeClosed
  mpr H := ⟨(H 0).toIsRing, fun _p hp₀ ↦ (H _).has_root' hp₀ degree_le_natDegree⟩

theorem IsAlgClosed.has_root {x : Nimber} (h : IsAlgClosed x) {p : Nimber[X]}
    (hp₀ : p.degree ≠ 0) (hp : ∀ n, p.coeff n < x) : ∃ r < x, p.IsRoot r :=
  (h.toIsNthDegreeClosed _).has_root hp₀ degree_le_natDegree hp

@[simp]
theorem IsAlgClosed.zero : IsAlgClosed 0 := by
  simp [isAlgClosed_iff_forall]

@[simp]
theorem IsAlgClosed.one : IsAlgClosed 1 := by
  simp [isAlgClosed_iff_forall]

protected theorem IsAlgClosed.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsAlgClosed x) :
    IsAlgClosed (sSup s) := by
  rw [isAlgClosed_iff_forall]
  exact fun n ↦ IsNthDegreeClosed.sSup fun x hx ↦ (H x hx).toIsNthDegreeClosed n

protected theorem IsAlgClosed.iSup {ι} {f : ι → Nimber} (H : ∀ i, IsAlgClosed (f i)) :
    IsAlgClosed (⨆ i, f i) := by
  apply IsAlgClosed.sSup
  simpa

/-- If `x` is a field, to prove it algebraically closed, it suffices to check
*monic* polynomials. -/
theorem IsAlgClosed.ofMonic {x : Nimber} (h : IsField x)
    (hp : ∀ p : Nimber[X], p.Monic → 0 < p.degree → (∀ k, p.coeff k < x) → ∃ r < x, p.IsRoot r) :
    IsAlgClosed x := by
  rw [isAlgClosed_iff_forall]
  exact fun n ↦ IsNthDegreeClosed.ofMonic h fun p hm hp₀ _ ↦ hp p hm hp₀

end Nimber
