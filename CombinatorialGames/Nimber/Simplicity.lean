/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/
import CombinatorialGames.Nimber.Field
import CombinatorialGames.Mathlib.WithTop
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.Multiset.Fintype
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
- If `x` is a field that isn't algebraically closed, then `x` is the root of some polynomial with
  coefficients `< x`.

The proof follows Aaron Siegel's Combinatorial Games, pp. 440-444.

## Todo

We are currently at 3/4.
-/

universe u

open Order Ordinal Polynomial Set

/-! ### Mathlib lemmas -/

-- TODO: should some of these be global?
attribute [local aesop simp] Function.update coeff_one coeff_C coeff_X

-- TODO: this is a pending Mathlib refactor.
attribute [-simp] add_one_eq_succ
attribute [simp] lt_add_one_iff

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

theorem MinimalFor.not_lt {α ι : Type*} {P : α → Prop} {f : α → ι} {x y : α} [Preorder ι]
    (h : MinimalFor P f x) (hy : P y) : ¬ f y < f x :=
  fun hx ↦ (h.le_of_le hy hx.le).not_gt hx

theorem WithBot.le_zero_iff {α} [AddZeroClass α] [PartialOrder α] [CanonicallyOrderedAdd α]
    {x : WithBot α} : x ≤ 0 ↔ x = ⊥ ∨ x = 0 := by
  cases x <;> simp

@[simp]
theorem WithBot.add_one_ne_zero (x : WithBot ℕ) : x + 1 ≠ 0 := by
  cases x <;> exact not_eq_of_beq_eq_false rfl

theorem WithBot.coe_add_one (n : ℕ) : WithBot.some (n + 1) = WithBot.some n + 1 :=
  rfl

@[simp]
theorem WithBot.natCast_eq_coe (n : ℕ) : (n : WithBot ℕ) = WithBot.some n :=
  rfl

@[simp]
theorem WithBot.lt_add_one {x : WithBot ℕ} (n : ℕ) : x < WithBot.some n + 1 ↔ x ≤ n := by
  cases x
  · simp [bot_lt_iff_ne_bot]
  · rw [← WithBot.coe_add_one, WithBot.coe_lt_coe]
    simp

@[simp]
theorem WithTop.forall_lt_coe {α : Type*} {P : WithTop α → Prop} [Preorder α] {x : α} :
    (∀ y < WithTop.some x, P y) ↔ ∀ y < x, P (.some y) := by
  refine ⟨?_, fun h y ↦ ?_⟩
  · aesop
  · rw [WithTop.lt_iff_exists_coe]
    aesop

/-! #### Ordinal lemmas-/

namespace Ordinal

theorem div_two_opow_log {o : Ordinal} (ho : o ≠ 0) : o / 2 ^ log 2 o = 1 := by
  apply le_antisymm
  · simpa [← one_add_one_eq_two] using div_opow_log_lt o one_lt_two
  · simpa [one_le_iff_ne_zero, pos_iff_ne_zero] using div_opow_log_pos 2 ho

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
  exact mul_le_mul_left' (succ_le_iff.mpr hq) _

theorem forall_lt_mul {b c : Ordinal} {P : Ordinal → Prop} :
    (∀ a < b * c, P a) ↔ ∀ q < c, ∀ r < b, P (b * q + r) := by
  simp_rw [lt_mul_iff]
  aesop

theorem exists_lt_mul {b c : Ordinal} {P : Ordinal → Prop} :
    (∃ a < b * c, P a) ↔ ∃ q < c, ∃ r < b, P (b * q + r) := by
  simp_rw [lt_mul_iff]
  aesop

theorem mul_add_lt {a b c d : Ordinal} (h₁ : c < a) (h₂ : b < d) : a * b + c < a * d := by
  apply lt_of_lt_of_le (b := a * (succ b))
  · rwa [mul_succ, add_lt_add_iff_left]
  · apply mul_le_mul_left'
    rwa [succ_le_iff]

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

theorem eq_C_mul_X_pow_add_of_degree_le {R} [Ring R] {p : R[X]} {n : ℕ} (h : p.degree ≤ n) :
    ∃ (a : R) (q : R[X]), p = C a * X ^ n + q ∧ q.degree < n := by
  obtain hp | hp := h.lt_or_eq
  · use 0, p
    simpa
  · refine ⟨p.coeff n, p - C (p.coeff n) * X ^ n, ?_, ?_⟩
    · rw [_root_.add_sub_cancel]
    · apply (degree_sub_lt _ (by aesop) _).trans_le h
      · rw [hp, degree_C_mul_X_pow _ (p.coeff_ne_zero_of_eq_degree hp)]
      · rw [leadingCoeff, p.natDegree_eq_of_degree_eq_some hp]
        simp

theorem degree_pos_of_mem_roots {R} [CommRing R] [IsDomain R] {p : R[X]} {r} (h : r ∈ p.roots) :
    0 < p.degree := by
  by_contra!
  rw [p.eq_C_of_degree_le_zero this, roots_C] at h
  cases h

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

@[simp]
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
    rwa [← Ordinal.mul_two, ← opow_succ, opow_le_opow_iff_right one_lt_two, succ_le_iff]
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

theorem IsGroup.opow {x : Nimber} (h : IsGroup x) (a : Ordinal) : IsGroup (∗x.val ^ a) := by
  rw [isGroup_iff_zero_or_mem_range_two_opow] at h
  obtain rfl | ⟨b, hb, rfl⟩ := h
  · exact .of_le_one (zero_opow_le _)
  · simp [← opow_mul]

theorem IsGroup.pow {x : Nimber} (h : IsGroup x) (n : ℕ) : IsGroup (∗x.val ^ n) :=
  mod_cast h.opow n

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
theorem IsGroup.exists_mul_of_not_isRing {x : Nimber} (h' : IsGroup x) (h : ¬ IsRing x) :
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

/-- A version of `IsGroup.mul_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsGroup.mul_eq_of_lt' {x y z w : Ordinal}
    (hx : IsGroup (∗x)) (hy : IsGroup (∗y)) (hw : IsGroup (∗w))
    (hyx : y ≤ x) (hzy : z < y) (hyw : y ≤ w)
    (H : ∀ z < y, (∗z)⁻¹ < ∗w) (H' : ∀ ⦃a b⦄, a < x → b < w → ∗a * ∗b < x) :
    x * z = val (∗x * ∗z) := by
  apply le_antisymm
  · apply le_of_forall_ne
    rw [forall_lt_mul]
    intro a ha b hb
    rw [ne_eq, ← of_eq_iff, hx.mul_add_eq_of_lt' hb,
      hx.mul_eq_of_lt' hy hw hyx (ha.trans hzy) hyw H H', add_comm, CharTwo.add_eq_iff_eq_add,
      of_val, ← mul_add]
    obtain hza | hza := eq_or_ne (∗z + ∗a) 0
    · cases ha.ne' (add_eq_zero.1 hza)
    · rw [← div_eq_iff hza]
      exact (H' hb (H _ (hy.add_lt hzy (ha.trans hzy)))).ne
  · rw [val_le_iff]
    refine mul_le_of_forall_ne fun a ha b hb ↦ ?_
    rw [add_comm, ← add_assoc, ← mul_add, add_comm]
    induction b with | mk b
    rw [of.lt_iff_lt] at hb
    have hzw := hzy.trans_le hyw
    have hx' : val (a * (∗b + ∗z)) < x := H' ha (hw.add_lt (hb.trans hzw) hzw)
    rw [← of_val (_ * _), ← hx.mul_eq_of_lt' hy hw hyx (hb.trans hzy) hyw H H',
      ← of_val (a * _), ← hx.mul_add_eq_of_lt' hx']
    exact (mul_add_lt hx' hb).ne
termination_by z

theorem IsGroup.mul_eq_of_lt {x y z w : Nimber} (hx : IsGroup x) (hy : IsGroup y) (hw : IsGroup w)
    (hyx : y ≤ x) (hzy : z < y) (hyw : y ≤ w)
    (H : ∀ z < y, z⁻¹ < w) (H' : ∀ ⦃a b⦄, a < x → b < w → a * b < x) : x *ₒ z = x * z :=
  hx.mul_eq_of_lt' hy hw hyx hzy hyw H H'

/-- A version of `IsRing.mul_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsRing.mul_eq_of_lt' {x y z : Ordinal} (hx : IsRing (∗x)) (hy : IsGroup (∗y))
    (hyx : y ≤ x) (hzy : z < y) (H : ∀ z < y, (∗z)⁻¹ < ∗x) : x * z = val (∗x * ∗z) :=
  hx.toIsGroup.mul_eq_of_lt' hy hx.toIsGroup hyx hzy hyx H hx.mul_lt

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
  · simp_all
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
      simp_rw [val_one, add_one_eq_succ, val_of, lt_succ_iff,
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

theorem IsRing.inv_lt_of_not_isField {x y : Nimber} (h' : IsRing x) (h : ¬ IsField x)
    (hy : y < x⁻¹) : y⁻¹ < x :=
  (inv_lt_of_not_isField_aux h' h).2 y hy

theorem IsRing.inv_le_of_not_isField {x y : Nimber} (h' : IsRing x) (h : ¬ IsField x)
    (hy : y ≤ x⁻¹) : y⁻¹ ≤ x := by
  obtain rfl | hy := hy.eq_or_lt; simp
  exact (h'.inv_lt_of_not_isField h hy).le

/-- The third **simplest extension theorem**: if `x` is a ring but not a field, then `x` can be
written as `y⁻¹` for some `y < x`. In simpler wording, `x⁻¹ < x`. -/
theorem IsRing.inv_lt_self_of_not_isField {x : Nimber} (h' : IsRing x) (h : ¬ IsField x) : x⁻¹ < x :=
  (inv_lt_of_not_isField_aux h' h).1

-- TODO: characterize nim arithmetic on the naturals.
proof_wanted IsRing.two_two_pow (n : ℕ) : IsRing (∗(2 ^ 2 ^ n))

-- TODO: this follows directly from `IsRing.two_two_pow` and the surjectivity of `a * ·` for `a ≠ 0`.
proof_wanted IsField.two_two_pow (n : ℕ) : IsField (∗(2 ^ 2 ^ n))

/-! ### Polynomials -/

theorem IsGroup.coeff_add_lt {x : Nimber} {p q : Nimber[X]} (h : IsGroup x)
    (hp : ∀ k, p.coeff k < x) (hq : ∀ k, q.coeff k < x) : ∀ k, (p + q).coeff k < x := by
  intro k
  rw [coeff_add]
  exact h.add_lt (hp k) (hq k)

theorem IsGroup.coeff_sum_lt {x : Nimber} {ι} {f : ι → Nimber[X]} {s : Finset ι} (h : IsGroup x)
    (hx₀ : x ≠ 0) (hs : ∀ y ∈ s, ∀ k, (f y).coeff k < x) : ∀ k, (s.sum f).coeff k < x := by
  intro k
  rw [finset_sum_coeff]
  exact h.sum_lt hx₀ fun y hy ↦ (hs y hy k)

theorem IsRing.coeff_mul_lt {x : Nimber} {p q : Nimber[X]} (h : IsRing x)
    (hp : ∀ k, p.coeff k < x) (hq : ∀ k, q.coeff k < x) : ∀ k, (p * q).coeff k < x := by
  intro k
  rw [coeff_mul]
  exact h.sum_lt (hp 0).ne_bot fun y hy ↦ h.mul_lt (hp _) (hq _)

theorem IsRing.coeff_prod_lt {x : Nimber} {ι} {f : ι → Nimber[X]} {s : Finset ι} (h : IsRing x)
    (hx₁ : 1 < x) (hs : ∀ y ∈ s, ∀ k, (f y).coeff k < x) : ∀ k, (s.prod f).coeff k < x := by
  classical
  induction s using Finset.induction with
  | empty =>
    have := zero_lt_one.trans hx₁
    aesop (add simp [coeff_one])
  | insert y s hy IH =>
    rw [Finset.prod_insert hy]
    apply h.coeff_mul_lt <;> aesop

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
theorem IsField.degree_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) : (h.embed hx₁ p hp).degree = p.degree :=
  rfl

@[simp]
theorem IsField.leadingCoeff_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) : (h.embed hx₁ p hp).leadingCoeff = ⟨p.leadingCoeff, hp _⟩ :=
  rfl

@[simp]
theorem IsField.map_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) : (h.embed hx₁ p hp).map (Subfield.subtype _) = p := by
  ext; simp

@[simp]
theorem IsField.embed_C {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {y hy} :
    h.embed hx₁ (C y) hy = C ⟨y, by simpa using hy 0⟩ := by
  ext
  simp_rw [h.coeff_embed, coeff_C]
  split_ifs <;> rfl

@[simp]
theorem IsField.eval_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) (y) : (h.embed hx₁ p hp).eval y = ⟨_, h.eval_lt hp y.2⟩ := by
  simp [← Subtype.val_inj, embed, sum, eval_eq_sum]

/-- Evaluate a nimber polynomial using ordinal arithmetic. -/
def oeval (x : Nimber) (p : Nimber[X]) : Nimber :=
  ∗((List.range (p.natDegree + 1)).reverse.map fun k ↦ x.val ^ k * (p.coeff k).val).sum

@[simp]
theorem oeval_zero (x : Nimber) : oeval x 0 = 0 := by
  simp [oeval]

theorem oeval_eq_of_natDegree_le {p : Nimber[X]} {n : ℕ} (h : p.natDegree + 1 ≤ n) (x : Nimber) :
    oeval x p = ∗((List.range n).reverse.map fun k ↦ x.val ^ k * (p.coeff k).val).sum := by
  induction n with
  | zero => simp_all
  | succ n IH =>
    obtain h | h := h.eq_or_lt
    · rw [oeval, h]
    · rw [add_lt_add_iff_right] at h
      rw [List.range_succ]
      simpa [p.coeff_eq_zero_of_natDegree_lt h] using IH h

theorem oeval_C_mul_X_pow_add {n : ℕ} {p : Nimber[X]} (hp : p.degree < n) (x a : Nimber) :
    oeval x (C a * X ^ n + p) = ∗(x.val ^ n * a.val + val (oeval x p)) := by
  obtain rfl | ha := eq_or_ne a 0; simp [oeval]
  · have hp' : p.natDegree ≤ n := p.natDegree_le_of_degree_le hp.le
    have hp'' : (C a * X ^ n + p).natDegree ≤ n := by compute_degree!
    rw [oeval_eq_of_natDegree_le (add_right_mono hp'),
      oeval_eq_of_natDegree_le (add_right_mono hp'')]
    cases n with
    | zero => simp_all
    | succ n =>
      suffices (List.range n).map
        (fun k ↦ val x ^ k * val ((if k = n + 1 then a else 0) + p.coeff k)) =
      (List.range n).map (fun k ↦ val x ^ k * val (p.coeff k)) by
        simp [List.range_succ, p.coeff_eq_zero_of_degree_lt hp, this]
      apply List.map_congr_left
      aesop

@[simp]
theorem oeval_C_mul_X_pow (x a : Nimber) (n : ℕ) :
    oeval x (C a * X ^ n) = ∗(x.val ^ n * a.val) := by
  simpa using oeval_C_mul_X_pow_add (p := 0) (WithBot.bot_lt_coe n) x a

@[simp]
theorem oeval_X_pow (x : Nimber) (n : ℕ) : oeval x (X ^ n) = ∗(x.val ^ n) := by
  simpa using oeval_C_mul_X_pow x 1 n

@[simp]
theorem oeval_C (x a : Nimber) : oeval x (C a) = a := by
  simpa using oeval_C_mul_X_pow x a 0

@[simp]
theorem oeval_X (x : Nimber) : oeval x X = x := by
  simpa using oeval_X_pow x 1

/-- A version of `eq_oeval_of_lt_opow` stated in terms of `Ordinal`. -/
theorem eq_oeval_of_lt_opow' {x y : Ordinal} {n : ℕ} (hx₀ : x ≠ 0) (h : y < x ^ n) :
    ∃ p : Nimber[X], p.degree < n ∧ (∀ k, val (p.coeff k) < x) ∧ val (oeval (∗x) p) = y := by
  induction n generalizing y with
  | zero => use 0; simp_all [Ordinal.pos_iff_ne_zero]
  | succ n IH =>
    obtain ⟨p, hpn, hpk, hp⟩ := IH (mod_lt y (pow_ne_zero n hx₀))
    refine ⟨C (∗(y / x ^ n)) * X ^ n + p, ?_, fun k ↦ ?_, ?_⟩
    · compute_degree!
      exact hpn.le
    · rw [coeff_add, coeff_C_mul, coeff_X_pow]
      split_ifs with h
      · subst h
        rw [p.coeff_eq_zero_of_degree_lt hpn, add_zero, mul_one, val_of]
        rwa [div_lt (pow_ne_zero k hx₀), ← pow_succ]
      · simpa using hpk k
    · rw [oeval_C_mul_X_pow_add hpn, hp]
      exact div_add_mod ..

theorem eq_oeval_of_lt_opow {x y : Nimber} {n : ℕ} (hx₀ : x ≠ 0) (h : y < of (x.val ^ n)) :
    ∃ p : Nimber[X], p.degree < n ∧ (∀ k, p.coeff k < x) ∧ oeval x p = y :=
  eq_oeval_of_lt_opow' hx₀ h

theorem oeval_lt_opow {x : Ordinal} {p : Nimber[X]} {n : ℕ}
    (hp : ∀ k, p.coeff k < x) (hn : p.degree < n) : val (oeval x p) < x ^ n := by
  obtain rfl | hx₀ := x.eq_zero_or_pos; simp at hp
  induction n generalizing p with
  | zero => simp_all
  | succ n IH =>
    have hn' : p.degree ≤ n := le_of_lt_succ hn
    obtain ⟨a, q, rfl, hq⟩ := eq_C_mul_X_pow_add_of_degree_le hn'
    rw [oeval_C_mul_X_pow_add hq, val_of, pow_succ]
    refine mul_add_lt (IH (fun k ↦ ?_) hq) ?_
    · obtain h | h := lt_or_ge k n
      · convert hp k using 1
        aesop
      · rwa [q.coeff_eq_zero_of_degree_lt (hq.trans_le (mod_cast h))]
    · simpa [q.coeff_eq_zero_of_degree_lt hq] using hp n

namespace Lex

/-- The lexicographic ordering on nimber polynomials. -/
noncomputable instance : LinearOrder (Nimber[X]) where
  lt p q := ∃ n, (∀ k, n < k → p.coeff k = q.coeff k) ∧ p.coeff n < q.coeff n
  __ := LinearOrder.lift'
    (fun p : Nimber[X] ↦ toLex <| p.toFinsupp.equivMapDomain OrderDual.toDual) <| by
      intro p q h
      rw [toLex_inj, Finsupp.ext_iff] at h
      rwa [← toFinsupp_inj, Finsupp.ext_iff]

theorem lt_def {p q : Nimber[X]} : p < q ↔ ∃ n,
    (∀ k, n < k → p.coeff k = q.coeff k) ∧ p.coeff n < q.coeff n :=
  .rfl

instance : WellFoundedLT (Lex (ℕᵒᵈ →₀ Nimber)) where
  wf := Finsupp.Lex.wellFounded' Nimber.not_lt_zero lt_wf (wellFounded_lt (α := ℕ))

instance : WellFoundedLT (Nimber[X]) where
  wf := InvImage.wf
    (fun p : Nimber[X] ↦ toLex <| p.toFinsupp.equivMapDomain OrderDual.toDual) wellFounded_lt

noncomputable instance : OrderBot (Nimber[X]) where
  bot := 0
  bot_le p := by rw [← not_lt, lt_def]; simp

@[simp] theorem bot_eq_zero : (⊥ : Nimber[X]) = 0 := rfl
@[simp] theorem le_zero_iff {p : Nimber[X]} : p ≤ 0 ↔ p = 0 := le_bot_iff

noncomputable instance : ConditionallyCompleteLinearOrderBot (Nimber[X]) :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

theorem forall_lt_quadratic {P : Nimber[X] → Prop} {x y z : Nimber} :
    (∀ p < C x * X ^ 2 + C y * X + C z, P p) ↔
      (∀ c < z, P (C x * X ^ 2 + C y * X + C c)) ∧
      (∀ b < y, ∀ c, P (C x * X ^ 2 + C b * X + C c)) ∧
      (∀ a < x, ∀ b c, P (C a * X ^ 2 + C b * X + C c)) := by
  refine ⟨fun H ↦
    ⟨fun c hc ↦ H _ ⟨0, by aesop⟩, fun b hb c ↦ H _ ⟨1, by aesop⟩, fun a ha b c ↦ H _ ⟨2, by aesop⟩⟩,
    fun ⟨H₁, H₂, H₃⟩ p hp ↦ ?_⟩
  obtain ⟨n, hn, hp⟩ := hp
  match n with
  | 0 =>
    have : p.coeff 0 < z := by simpa using hp
    convert H₁ _ this
    ext k
    match k with | 0 | 1 | 2 | k + 3 => aesop
  | 1 =>
    have : p.coeff 1 < y := by simpa using hp
    convert H₂ _ this (p.coeff 0)
    ext k
    match k with | 0 | 1 | 2 | k + 3 => aesop
  | 2 =>
    have : p.coeff 2 < x := by simpa using hp
    convert H₃ _ this (p.coeff 1) (p.coeff 0)
    ext k
    match k with | 0 | 1 | 2 | k + 3 => aesop
  | n + 3 => simp at hp

theorem forall_le_quadratic {P : Nimber[X] → Prop} {x y z : Nimber} :
    (∀ p ≤ C x * X ^ 2 + C y * X + C z, P p) ↔
      (∀ c ≤ z, P (C x * X ^ 2 + C y * X + C c)) ∧
      (∀ b < y, ∀ c, P (C x * X ^ 2 + C b * X + C c)) ∧
      (∀ a < x, ∀ b c, P (C a * X ^ 2 + C b * X + C c)) := by
  simp_rw [le_iff_eq_or_lt, forall_eq_or_imp, forall_lt_quadratic]
  tauto

theorem exists_lt_quadratic {P : Nimber[X] → Prop} {x y z : Nimber} :
    (∃ p < C x * X ^ 2 + C y * X + C z, P p) ↔
      (∃ c < z, P (C x * X ^ 2 + C y * X + C c)) ∨
      (∃ b < y, ∃ c, P (C x * X ^ 2 + C b * X + C c)) ∨
      (∃ a < x, ∃ b c, P (C a * X ^ 2 + C b * X + C c)) := by
  rw [← not_iff_not]; simpa using forall_lt_quadratic

theorem exists_le_quadratic {P : Nimber[X] → Prop} {x y z : Nimber} :
    (∃ p ≤ C x * X ^ 2 + C y * X + C z, P p) ↔
      (∃ c ≤ z, P (C x * X ^ 2 + C y * X + C c)) ∨
      (∃ b < y, ∃ c, P (C x * X ^ 2 + C b * X + C c)) ∨
      (∃ a < x, ∃ b c, P (C a * X ^ 2 + C b * X + C c)) := by
  rw [← not_iff_not]; simpa using forall_le_quadratic

theorem forall_lt_linear {P : Nimber[X] → Prop} {x y : Nimber} :
    (∀ p < C x * X + C y, P p) ↔
      (∀ b < y, P (C x * X + C b)) ∧ (∀ a < x, ∀ b, P (C a * X + C b)) := by
  convert @forall_lt_quadratic P 0 x y using 2 <;> simp

theorem forall_le_linear {P : Nimber[X] → Prop} {x y : Nimber} :
    (∀ p ≤ C x * X + C y, P p) ↔
      (∀ b ≤ y, P (C x * X + C b)) ∧ (∀ a < x, ∀ b, P (C a * X + C b)) := by
  convert @forall_le_quadratic P 0 x y using 2 <;> simp

theorem exists_lt_linear {P : Nimber[X] → Prop} {x y : Nimber} :
    (∃ p < C x * X + C y, P p) ↔
      (∃ b < y, P (C x * X + C b)) ∨ (∃ a < x, ∃ b, P (C a * X + C b)) := by
  convert @exists_lt_quadratic P 0 x y using 2 <;> simp

theorem exists_le_linear {P : Nimber[X] → Prop} {x y : Nimber} :
    (∃ p ≤ C x * X + C y, P p) ↔
      (∃ b ≤ y, P (C x * X + C b)) ∨ (∃ a < x, ∃ b, P (C a * X + C b)) := by
  convert @exists_le_quadratic P 0 x y using 2 <;> simp

@[simp]
theorem forall_lt_C {P : Nimber[X] → Prop} {x : Nimber} :
    (∀ p < C x, P p) ↔ ∀ a < x, P (C a) := by
  convert @forall_lt_linear P 0 x using 2 <;> simp

@[simp]
theorem forall_le_C {P : Nimber[X] → Prop} {x : Nimber} :
    (∀ y ≤ C x, P y) ↔ ∀ y ≤ x, P (C y) := by
  convert @forall_le_linear P 0 x using 2 <;> simp

@[simp]
theorem exists_lt_C {P : Nimber[X] → Prop} {x : Nimber} :
    (∃ y < C x, P y) ↔ ∃ y < x, P (C y) := by
  convert @exists_lt_linear P 0 x using 2 <;> simp

@[simp]
theorem exists_le_C {P : Nimber[X] → Prop} {x : Nimber} :
    (∃ y ≤ C x, P y) ↔ ∃ y ≤ x, P (C y) := by
  convert @exists_le_linear P 0 x using 2 <;> simp

theorem degree_mono : Monotone (α := Nimber[X]) degree := by
  intro p q h
  obtain rfl | hq₀ := eq_or_ne q 0; aesop
  contrapose! h
  have h' := natDegree_lt_natDegree hq₀ h
  refine ⟨p.natDegree, fun k hk ↦ ?_, ?_⟩
  · rw [p.coeff_eq_zero_of_natDegree_lt hk, q.coeff_eq_zero_of_natDegree_lt (h'.trans hk)]
  · rw [q.coeff_eq_zero_of_natDegree_lt h']
    aesop (add simp [Nimber.pos_iff_ne_zero])

theorem natDegree_mono : Monotone (α := Nimber[X]) natDegree := by
  apply Monotone.comp (fun a b ↦ ?_) degree_mono
  cases a <;> cases b <;> aesop

theorem lt_of_degree_lt {p q : Nimber[X]} (h : p.degree < q.degree) : p < q := by
  contrapose! h; exact degree_mono h

theorem lt_of_natDegree_lt {p q : Nimber[X]} (h : p.natDegree < q.natDegree) : p < q := by
  contrapose! h; exact natDegree_mono h

@[simp]
theorem lt_X_pow_iff {p : Nimber[X]} {n : ℕ} : p < X ^ n ↔ p.degree < n := by
  simp_rw [lt_def, degree_lt_iff_coeff_zero, le_iff_lt_or_eq]
  refine ⟨?_, fun _ ↦ ⟨n, ?_⟩⟩ <;> aesop

@[simp]
theorem coe_lt_X_pow_iff {p : Nimber[X]} {n : ℕ} : WithTop.some p < .some X ^ n ↔ p.degree < n := by
  rw [← WithTop.coe_pow, WithTop.coe_lt_coe, lt_X_pow_iff]

instance : NoMaxOrder (Nimber[X]) where
  exists_gt p := by
    use X ^ (p.natDegree + 1)
    simpa using degree_le_natDegree

noncomputable instance : SuccOrder (Nimber.{u}[X]) := by
  have (a b) (h : a < b) : b ≠ 0 := h.ne_bot -- Used by `aesop`
  refine .ofCore (fun p ↦ .ofFinsupp (p.toFinsupp.update 0 (succ (p.coeff 0)))) ?_ (by simp)
  refine @fun p _ q ↦ ⟨fun hpq ↦ ?_, ?_⟩
  · obtain ⟨n, hn, hpq⟩ := hpq
    cases n with
    | zero =>
      obtain hpq' | hpq' := (succ_le_of_lt hpq).lt_or_eq
      · refine le_of_lt ⟨0, ?_⟩
        aesop
      · apply le_of_eq
        ext k
        cases k <;> aesop
    | succ n => refine le_of_lt ⟨n + 1, ?_⟩; aesop
  · rw [le_iff_lt_or_eq]
    rintro (hpq | rfl)
    · obtain ⟨n, hn, hpq⟩ := hpq
      refine ⟨n, fun k hk ↦ ?_, ?_⟩
      · specialize hn k hk
        aesop
      · have (a b : Nimber.{u}) (h : succ a < b) : a < b := (le_succ a).trans_lt h
        aesop
    · use 0
      aesop

@[aesop simp]
theorem coeff_succ (p : Nimber[X]) :
    (succ p).coeff = Function.update p.coeff 0 (succ (p.coeff 0)) := by
  change coeff (Polynomial.ofFinsupp _) = _
  simp
  rfl

@[simp]
theorem coeff_succ_zero (p : Nimber[X]) :
    (succ p).coeff 0 = succ (p.coeff 0) := by
  rw [coeff_succ, Function.update_self]

@[simp]
theorem coeff_succ_of_ne_zero (p : Nimber[X]) {k : ℕ} (h : k ≠ 0) :
    (succ p).coeff k = p.coeff k := by
  rw [coeff_succ, Function.update_of_ne h]

theorem succ_eq_add_one_of_coeff_zero {p : Nimber[X]} (h : p.coeff 0 = 0) : succ p = p + 1 := by
  aesop

end Lex

/-- Returns the lexicographically earliest polynomial, all of whose coefficients are less than `x`,
without any roots less than `x`. If none exists, returns `⊤`.

This function takes values on `WithTop (Nimber[X])`, which is a well-ordered complete lattice (the
order on `Nimber[X]` is the lexicographic order). -/
noncomputable def simplestIrreducible (x : Nimber) : WithTop (Nimber[X]) :=
  sInf (WithTop.some '' {p | 0 < p.degree ∧ (∀ k, p.coeff k < x) ∧ ∀ r < x, p.eval r ≠ 0})

private theorem simplestIrreducible_mem {x : Nimber} (ht) :
    (simplestIrreducible x).untop ht ∈
      {p | 0 < p.degree ∧ (∀ k, p.coeff k < x) ∧ ∀ r < x, p.eval r ≠ 0} := by
  obtain hs | hs := ({p : Nimber[X] |
    0 < p.degree ∧ (∀ k, p.coeff k < x) ∧ ∀ r < x, p.eval r ≠ 0}).eq_empty_or_nonempty
  · simp [simplestIrreducible, hs] at ht
  · convert csInf_mem hs
    rw [← WithTop.coe_inj, WithTop.coe_untop, simplestIrreducible, WithTop.coe_sInf' hs]
    exact OrderBot.bddBelow _

theorem degree_simplestIrreducible_pos {x : Nimber} (ht) :
    0 < ((simplestIrreducible x).untop ht).degree :=
  (simplestIrreducible_mem ht).1

theorem coeff_simplestIrreducible_lt {x : Nimber} (ht) :
    ∀ k, ((simplestIrreducible x).untop ht).coeff k < x :=
  (simplestIrreducible_mem ht).2.1

theorem simplestIrreducible_not_root_of_lt {x r : Nimber} (ht) (hr : r < x) :
    ((simplestIrreducible x).untop ht).eval r ≠ 0 :=
  (simplestIrreducible_mem ht).2.2 r hr

@[simp]
theorem simplestIrreducible_zero : simplestIrreducible 0 = ⊤ := by
  simp [simplestIrreducible]

theorem coeff_simplestIrreducible_zero_ne {x : Nimber} (ht) :
    ((simplestIrreducible x).untop ht).coeff 0 ≠ 0 := by
  obtain rfl | hx := eq_bot_or_bot_lt x
  · simp at ht
  · rw [coeff_zero_eq_eval_zero]
    exact simplestIrreducible_not_root_of_lt _ hx

@[simp]
theorem simplestIrreducible_ne_zero (x : Nimber) : simplestIrreducible x ≠ 0 := by
  intro h
  have ht := h ▸ WithTop.zero_ne_top
  simpa [h] using coeff_simplestIrreducible_zero_ne ht


@[simp]
theorem simplestIrreducible_ne_zero' (x : Nimber) (ht) : (simplestIrreducible x).untop ht ≠ 0 := by
  rw [← WithTop.coe_inj.ne]
  simp

-- TODO: upstream attr.
attribute [simp] mem_lowerBounds

theorem simplestIrreducible_le_of_not_isRoot {x : Nimber} {p : Nimber[X]}
    (hp₀ : 0 < p.degree) (hpk : ∀ k, p.coeff k < x) (hr : ∀ r < x, ¬ p.IsRoot r) :
    simplestIrreducible x ≤ p := by
  rw [simplestIrreducible, sInf_le_iff]
  aesop

theorem has_root_of_lt_simplestIrreducible {x : Nimber} {p : Nimber[X]}
    (hp₀ : p.degree ≠ 0) (hpk : ∀ k, p.coeff k < x) (hpn : p < simplestIrreducible x) :
    ∃ r < x, p.IsRoot r := by
  obtain hp | hp₀ := le_or_gt p.degree 0
  · have := WithBot.le_zero_iff.1 hp; aesop
  contrapose! hpn
  exact simplestIrreducible_le_of_not_isRoot hp₀ hpk hpn

theorem IsField.has_root_subfield {x : Nimber} (h : IsField x)
    (hx₁ : 1 < x) {p : (h.toSubfield hx₁)[X]} (hp₀ : p.degree ≠ 0)
    (hpn : map (Subfield.subtype _) p < simplestIrreducible x) : ∃ r, p.IsRoot r := by
  have hd : (p.map (Subring.subtype _)).degree = p.degree := by simpa using (em _).symm
  obtain ⟨r, hr, hr'⟩ := has_root_of_lt_simplestIrreducible (hd ▸ hp₀) (by simp) hpn
  exact ⟨⟨r, hr⟩, (isRoot_map_iff (Subring.subtype_injective _)).1 hr'⟩

theorem IsField.splits_subfield {x : Nimber} (h : IsField x) (hx₁ : 1 < x)
    {p : (h.toSubfield hx₁)[X]} (hpn : map (Subfield.subtype _) p < simplestIrreducible x) :
    p.Splits (.id _) := by
  obtain hp₀ | hp₀ := le_or_gt p.degree 0
  · exact splits_of_degree_le_one _ (hp₀.trans zero_le_one)
  induction hp : p.degree using WellFoundedLT.induction generalizing p with | ind n IH
  subst hp
  obtain ⟨r, hr⟩ := h.has_root_subfield hx₁ hp₀.ne' hpn
  rw [← hr.mul_div_eq]
  apply splits_mul _ (splits_X_sub_C _)
  obtain hp₀' | hp₀' := le_or_gt (p / (X - C r)).degree 1
  · exact splits_of_degree_le_one _ hp₀'
  · have hp : (p / (X - C r)).degree < p.degree := by apply degree_div_lt <;> aesop
    apply IH _ hp _ (zero_lt_one.trans hp₀') rfl
    apply (WithTop.coe_strictMono (Lex.lt_of_degree_lt _)).trans hpn
    simpa

theorem IsField.roots_eq_map {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hpn : p < simplestIrreducible x) (hpk : ∀ k, p.coeff k < x) :
    p.roots = (h.embed hx₁ p hpk).roots.map (Subfield.subtype _) := by
  simpa using roots_map (Subfield.subtype _)
    (h.splits_subfield hx₁ (p := h.embed hx₁ p hpk) (by simpa))

theorem IsField.root_lt {x r : Nimber} (h : IsField x) {p : Nimber[X]}
    (hpn : p < simplestIrreducible x) (hpk : ∀ k, p.coeff k < x) (hr : r ∈ p.roots) : r < x := by
  obtain hx₁ | hx₁ := le_or_gt x 1; simp [p_eq_zero_of_le_one hx₁ hpk] at hr
  have := h.roots_eq_map hx₁ hpn hpk ▸ hr; aesop

attribute [-simp] WithTop.coe_add WithTop.coe_mul WithTop.coe_pow

theorem IsRing.simplestIrreducible_eq_of_not_isField {x : Nimber} (h : IsRing x) (h' : ¬ IsField x) :
    simplestIrreducible x = .some (C x⁻¹ * X + 1) := by
  have hx₁ : 1 < x := by by_contra! hx; cases h' <| IsField.of_le_one hx
  have hx₀ : x ≠ 0 := hx₁.ne_bot
  apply le_antisymm
  · refine simplestIrreducible_le_of_not_isRoot ?_ ?_ fun r hr H ↦ ?_
    · convert zero_lt_one' (WithBot ℕ)
      dsimp
      compute_degree!
    · have := h.inv_lt_self_of_not_isField h'
      apply h.coeff_add_lt (h.coeff_mul_lt _ _) <;> aesop (add simp [Nimber.pos_iff_ne_zero])
    · replace H : x⁻¹ * r + 1 = 0 := by simpa using H
      rw [Nimber.add_eq_zero] at H
      obtain rfl := eq_of_inv_mul_eq_one H
      exact hr.false
  · apply le_of_forall_ne
    rw [WithTop.forall_lt_coe, ← C_1, Lex.forall_lt_linear]
    refine ⟨?_, fun y hy z ht ↦ ?_⟩
    · simp_rw [lt_one_iff_zero, forall_eq, map_zero, add_zero]
      intro ht
      have ht' := ht ▸ WithTop.coe_ne_top
      simpa [← ht] using coeff_simplestIrreducible_zero_ne ht'
    · have ht' := ht ▸ WithTop.coe_ne_top
      apply simplestIrreducible_not_root_of_lt ht' (r := z / y)
      · apply h.mul_lt _ (h.inv_lt_of_not_isField h' hy)
        simpa [← ht] using coeff_simplestIrreducible_lt ht' 0
      · have hy₀ : y ≠ 0 := by
          rintro rfl
          apply (degree_C_le (R := Nimber)).not_gt
          simpa [← ht] using degree_simplestIrreducible_pos ht'
        simp [← ht, mul_div_cancel₀, hy₀]

theorem IsField.monic_simplestIrreducible {x : Nimber} (h : IsField x) (h') :
    Monic ((simplestIrreducible x).untop h') := by
  by_contra! hm
  let c := ((simplestIrreducible x).untop h').leadingCoeff
  have hm' : 1 < c := by
    rw [← not_le, le_one_iff]
    simp_all [c, Monic]
  apply (simplestIrreducible_le_of_not_isRoot (x := x)
    (p := C c⁻¹ * ((simplestIrreducible x).untop h')) _ _ _).not_gt
  · sorry
  · sorry
  · sorry
  · sorry

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
  have : p.natDegree = 1 := natDegree_eq_of_degree_eq_some <| by
    rw [← succ_le_iff] at hp₀
    exact hp₁.antisymm hp₀
  rw [Monic, leadingCoeff] at hm
  have := hp 0
  aesop

-- We could have proved this much earlier, but going through `IsNthDegreeClosed`
-- gives a much shorter proof.
protected theorem IsField.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsField x) :
    IsField (sSup s) := by
  simp_rw [← isNthDegreeClosed_one_iff_isField] at *
  exact IsNthDegreeClosed.sSup H

protected theorem IsField.iSup {ι} {f : ι → Nimber} (H : ∀ i, IsField (f i)) :
    IsField (⨆ i, f i) := by
  apply IsField.sSup
  simpa

theorem IsNthDegreeClosed.X_pow_lt_simplestIrreducible {n : ℕ} {x : Nimber}
    (h : IsNthDegreeClosed n x) : .some (X ^ (n + 1)) < simplestIrreducible x := by
  apply lt_of_le_of_ne
  · refine le_of_forall_ne fun p hp hp' ↦ ?_
    obtain ⟨p, rfl, hp⟩ := WithTop.lt_iff_exists_coe.1 hp
    have h' := hp' ▸ WithTop.coe_ne_top
    have ⟨r, hr, hr'⟩ := h.has_root' (degree_simplestIrreducible_pos h') ?_
      (coeff_simplestIrreducible_lt h')
    · exact simplestIrreducible_not_root_of_lt h' hr hr'
    · simp_rw [← hp']
      simpa using hp
  · intro hp
    have ht := hp ▸ WithTop.coe_ne_top
    simpa [← hp] using coeff_simplestIrreducible_zero_ne ht

theorem IsField.X_sq_lt_simplestIrreducible {x : Nimber} (h : IsField x) :
    .some (X ^ 2) < simplestIrreducible x := by
  rw [← isNthDegreeClosed_one_iff_isField] at h
  exact h.X_pow_lt_simplestIrreducible

theorem IsNthDegreeClosed.root_lt {n : ℕ} {x r : Nimber} (h : IsNthDegreeClosed n x) {p : Nimber[X]}
    (hpn : p.degree ≤ n) (hpk : ∀ k, p.coeff k < x) (hr : r ∈ p.roots) : r < x := by
  cases n with
  | zero => cases hpn.not_gt <| degree_pos_of_mem_roots hr
  | succ n =>
    apply (h.toIsField n.succ_pos).root_lt _ hpk hr
    apply (WithTop.coe_lt_coe.2 (Lex.lt_of_degree_lt _)).trans h.X_pow_lt_simplestIrreducible
    rw [degree_X_pow]
    exact lt_succ_of_le hpn

/-
-- TODO: do I even need this?
-- TODO: upstream attr.
attribute [simp] Polynomial.map_multiset_prod
theorem IsNthDegreeClosed.eq_prod_roots_of_degree_le {n : ℕ} {x : Nimber}
    (h : IsNthDegreeClosed n x) {p : Nimber[X]} (hpn : p.degree ≤ n) (hp : ∀ k, p.coeff k < x) :
    p = C p.leadingCoeff * (p.roots.map fun a ↦ X - C a).prod := by
  obtain rfl | hp₀ := eq_or_ne p 0; simp
  have hx₁ := lt_of_not_ge fun h ↦ hp₀ (p_eq_zero_of_le_one h hp)
  cases n with
  | zero =>
    obtain hp' | hp' := WithBot.le_zero_iff.1 hpn
    · simp_all
    · rw [p.eq_C_of_degree_eq_zero hp']
      simp
  | succ n =>
    have h' := h.toIsField n.succ_pos
    have hs := h.splits_subfield h' hx₁ (p := h'.embed hx₁ p hp) hpn
    have hr := roots_map (Subfield.subtype _) hs
    rw [h'.map_embed] at hr
    conv_lhs => rw [← h'.map_embed hx₁ hp, eq_prod_roots_of_splits_id hs]
    simp [hr]
-/

theorem IsNthDegreeClosed.eval_eq_of_lt {n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x)
    {p : Nimber[X]} (hpn : p.degree ≤ n) (hpk : ∀ k, p.coeff k < x) :
    p.eval x = oeval x p := by
  obtain hx₁ | hx₁ := le_or_gt x 1; simp [p_eq_zero_of_le_one hx₁ hpk]
  have hx₀ := zero_lt_one.trans hx₁
  induction n generalizing p with
  | zero => rw [p.eq_C_of_degree_le_zero hpn]; simp
  | succ n IH =>
    have h' := h.le n.le_succ
    have hx : ∗(x.val ^ (n + 1)) = x ^ (n + 1) := by
      refine le_antisymm (le_of_forall_ne fun y hy ↦ ?_) (pow_le_of_forall_ne fun f ↦ ?_)
      · obtain ⟨p, hpn, hpk, rfl⟩ := eq_oeval_of_lt_opow hx₀.ne' hy
        have : p.coeff (n + 1) = 0 := p.coeff_eq_zero_of_degree_lt hpn
        rw [WithBot.natCast_eq_coe, WithBot.coe_add_one, WithBot.lt_add_one] at hpn
        rw [← IH h' hpn hpk, ← Nimber.add_eq_zero.ne]
        suffices eval x (p + X ^ (n + 1)) ≠ 0 by simpa
        have hpq : p.degree < (X ^ (n + 1) : Nimber[X]).degree := by simpa
        have hqn : (p + X ^ (n + 1)).degree = (n + 1 : WithBot ℕ) :=
          (degree_add_eq_right_of_degree_lt hpq).trans (degree_X_pow _)
        have hq₀ : p + X ^ (n + 1) ≠ 0 := fun h ↦ by
          have := h ▸ hqn
          rw [WithBot.natCast_eq_coe, ← WithBot.coe_add_one] at this
          exact WithBot.bot_ne_coe this
        refine fun hq ↦ (h.root_lt hqn.le ?_ ((mem_roots hq₀).2 hq)).false
        aesop
      · have hm : (∏ i, (X + C (f i).1)).Monic := by simp [Monic, leadingCoeff_prod]
        have hq : (∏ i, (X + C (f i).1)).degree = (n + 1 : WithBot ℕ) := by
          rw [degree_prod_of_monic] <;> simp [Monic]
        have hq' : (X ^ (n + 1) + ∏ i, (X + C (f i).1)).degree ≤ n := by
          rw [← lt_succ_iff, ← CharTwo.sub_eq_add]
          convert degree_sub_lt .. <;> simp_all
        have H : ∀ k, (X ^ (n + 1) + ∏ i, (X + C (f i).1)).coeff k < x := by
          apply h.coeff_add_lt
          · aesop
          · refine h.coeff_prod_lt hx₁ fun y hy ↦ ?_
            have : (f y).1 < x := (f y).2
            apply h.coeff_add_lt <;> aesop (add simp [coeff_X, coeff_C])
        have IH := IH h' hq' H
        simp only [eval_add, eval_pow, eval_X, eval_prod, eval_C] at IH
        exact IH ▸ (oeval_lt_opow H (lt_succ_of_le hq')).ne
    obtain ⟨a, q, rfl, hqn⟩ := eq_C_mul_X_pow_add_of_degree_le hpn
    have hqn' := hqn
    rw [WithBot.natCast_eq_coe, WithBot.coe_add_one, WithBot.lt_add_one] at hqn'
    have hqk (k) : q.coeff k < x := by
      obtain hk | hk := le_or_gt k n
      · convert hpk k using 1
        aesop
      · rwa [q.coeff_eq_zero_of_degree_lt (hqn'.trans_lt (mod_cast hk))]
    rw [eval_add, eval_mul, eval_C, eval_pow, eval_X, oeval_C_mul_X_pow_add hqn, IH h' hqn' hqk,
      (h.pow (n + 1)).mul_add_eq_of_lt', mul_comm, eq_comm, ← hx]
    · have hxn : val x ≤ val x ^ (n + 1) := by
        rw [← opow_natCast]
        exact left_le_opow _ (mod_cast n.succ_pos)
      congr
      refine (h.pow (n + 1)).mul_eq_of_lt h.toIsGroup h.toIsGroup hxn ?_ le_rfl
        @(h.toIsField n.succ_pos).inv_lt fun a b ha hb ↦ ?_
      · convert hpk (n + 1)
        simpa using q.coeff_eq_zero_of_degree_lt hqn
      · obtain ⟨p, hpn, hpk, rfl⟩ := eq_oeval_of_lt_opow hx₀.ne' ha
        rw [WithBot.natCast_eq_coe, WithBot.coe_add_one, WithBot.lt_add_one] at hpn
        have hpn' : (p * C b).degree ≤ n := by compute_degree!
        have H : ∀ k, (p * C b).coeff k < x := by
          simp_rw [coeff_mul_C]
          exact fun k ↦ h.mul_lt (hpk k) hb
        rw [← IH h' hpn hpk, ← eval_C (a := b), ← eval_mul, IH h' hpn' H]
        apply oeval_lt_opow H
        simpa using hpn'
    · exact oeval_lt_opow hqk hqn

theorem IsNthDegreeClosed.pow_mul_eq {n : ℕ} {x y : Nimber}
    (h : IsNthDegreeClosed n x) (hy : y < x) : x ^ n * y = ∗(x.val ^ n * y.val) := by
  obtain hx₁ | hx₁ := le_or_gt x 1
  · have := le_one_iff.1 hx₁; aesop
  · conv_lhs => rw [← eval_X (x := x), ← eval_pow, ← eval_C (a := y), ← eval_mul]
    rw [h.eval_eq_of_lt, mul_comm, oeval_C_mul_X_pow]
    · compute_degree!
    · have := zero_lt_one.trans hx₁
      aesop

theorem IsNthDegreeClosed.pow_eq {n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x) :
    x ^ n = ∗(x.val ^ n) := by
  obtain hx₁ | hx₁ := le_or_gt x 1
  · have := le_one_iff.1 hx₁; cases n <;> aesop
  · simpa using h.pow_mul_eq hx₁

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

theorem IsAlgClosed.simplestIrreducible_eq_top {x : Nimber} (h : IsAlgClosed x) :
    simplestIrreducible x = ⊤ := by
  rw [WithTop.eq_top_iff_forall_ge]
  refine fun p ↦ le_of_lt ?_
  apply (h.toIsNthDegreeClosed _).X_pow_lt_simplestIrreducible.trans'
  rw [WithTop.coe_lt_coe]
  simpa using degree_le_natDegree

-- TODO: is the `IsRing` assumption necessary?
theorem isAlgClosed_iff_simplestIrreducible_eq_top {x : Nimber} (h : IsRing x) :
    IsAlgClosed x ↔ simplestIrreducible x = ⊤ where
  mp := IsAlgClosed.simplestIrreducible_eq_top
  mpr hx := ⟨h, fun _p hp₀ hpk ↦
    has_root_of_lt_simplestIrreducible hp₀.ne' hpk (hx ▸ WithTop.coe_lt_top _)⟩

@[simp]
theorem simplestIrreducible_one : simplestIrreducible 1 = ⊤ :=
  IsAlgClosed.one.simplestIrreducible_eq_top

/-- The fourth **simplest extension theorem**: if `x` is a field that isn't algebraically closed,
then `x` is the root of some polynomial with coefficients `< x`. -/
theorem IsField.isRoot_simplestIrreducible {x : Nimber} (h : IsField x) (h' : ¬ IsAlgClosed x) :
    ((simplestIrreducible x).untop
      ((isAlgClosed_iff_simplestIrreducible_eq_top h.toIsRing).not.1 h')).IsRoot x := by
  sorry

end Nimber
