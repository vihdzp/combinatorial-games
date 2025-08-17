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

The simplest extension theorem states:

- If `x` is not a group, then `x` can be written as `y + z` for some `y, z < x`.
- If `x` is a group but not a ring, then `x` can be written as `y * z` for some `y, z < x`.
- If `x` is a ring but not a field, then `x` can be written as `y⁻¹` for some `y < x`.
- If `x` is a field that isn't algebraically closed, then `x` is the root of some polynomial with
  coefficients `< x`.

This file proves the first 3/4 parts of the theorem. The last part is in
`CombinatorialGames.Nimber.SimplestExtension.Polynomial`.

The proof follows Aaron Siegel's Combinatorial Games, pp. 440-444.
-/

universe u

open Order Ordinal Set

/-! ### Mathlib lemmas -/

-- TODO: this is a pending Mathlib refactor.
attribute [-simp] add_one_eq_succ
attribute [simp] lt_add_one_iff

-- TODO: PR these
attribute [simp] principal_zero Ordinal.not_lt_zero

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

-- TODO: presumably we should PR this along with all the other versions.
theorem WithBot.add_pos_of_pos_of_nonneg {α : Type*} [AddZeroClass α] [Preorder α] [AddLeftMono α]
    {a b : WithBot α} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b := by
  obtain ⟨a, rfl, ha⟩ := WithBot.lt_iff_exists_coe.1 ha
  obtain ⟨b, rfl, hb⟩ := WithBot.coe_le_iff.1 hb
  rw [← WithBot.coe_add,← WithBot.coe_zero, WithBot.coe_lt_coe, WithBot.coe_le_coe] at *
  exact _root_.add_pos_of_pos_of_nonneg ha hb

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

theorem inv_eq_self_iff {α : Type*} [DivisionRing α] {a : α} :
    a⁻¹ = a ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  obtain rfl | ha := eq_or_ne a 0; simp
  rw [← mul_eq_one_iff_inv_eq₀ ha, ← pow_two, sq_eq_one_iff]
  tauto

theorem self_eq_inv_iff {α : Type*} [DivisionRing α] {a : α} :
    a = a⁻¹ ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  rw [eq_comm, inv_eq_self_iff]

protected theorem CharTwo.add_eq_zero {R : Type*} [Ring R] [CharP R 2] {x y : R} :
    x + y = 0 ↔ x = y := by
  rw [← CharTwo.sub_eq_add, sub_eq_iff_eq_add, zero_add]

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

-- TODO: upstream
def _root_.Subring.toSubfield_of_finite {R : Type*} [Field R]
    (s : Subring R) (hs : s.carrier.Finite) : Subfield R where
  inv_mem' x hx := by
    obtain rfl | hx₀ := eq_or_ne x 0; simp
    have := hs.to_subtype
    let f (y : s) : s := ⟨x * y, s.mul_mem hx y.2⟩
    have hf : Function.Injective f := fun _ ↦ by aesop
    obtain ⟨y, hy⟩ := Finite.surjective_of_injective hf ⟨1, s.one_mem⟩
    convert y.2
    apply inv_eq_of_mul_eq_one_right
    simpa [f] using hy
  __ := s

theorem IsRing.toIsField_of_finite {n : ℕ} (h : IsRing.{u} (∗n)) : IsField.{u} (∗n) where
  inv_lt' x hx₀ hx := by
    obtain hn₁ | hn₁ := le_or_gt n 1
    · interval_cases n <;> simp_all
    · exact ((h.toSubring ((Nat.one_lt_cast (α := Ordinal)).2 hn₁)).toSubfield_of_finite
        (finite_Iio_of_natCast n)).inv_mem hx
  __ := h

-- TODO: characterize nim arithmetic on the naturals.
proof_wanted IsRing.two_two_pow (n : ℕ) : IsRing (∗(2 ^ 2 ^ n))

-- TODO: this follows directly from `IsRing.two_two_pow` and the surjectivity of `a * ·` for `a ≠ 0`.
proof_wanted IsField.two_two_pow (n : ℕ) : IsField (∗(2 ^ 2 ^ n))

end Nimber
