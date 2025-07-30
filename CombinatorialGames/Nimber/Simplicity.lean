/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/
import CombinatorialGames.Nimber.Field
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.SetTheory.Ordinal.Principal

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

theorem le_of_forall_ne {α : Type*} [LinearOrder α] {x y : α} (h : ∀ z < x, z ≠ y) : x ≤ y := by
  contrapose! h
  use y

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

theorem coeff_eq_zero_of_degree_lt {n : ℕ} (h : p.degree < n) : p.coeff n = 0 := by
  -- FIXME: why does this take explicit args?
  apply (p.degree_lt_iff_coeff_zero n).1 h
  rfl

theorem coeff_eq_zero_of_natDegree_lt {n : ℕ} (h : p.natDegree < n) : p.coeff n = 0 := by
  apply coeff_eq_zero_of_degree_lt (p.degree_le_natDegree.trans_lt _)
  rwa [Nat.cast_lt]

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
scoped notation:65 x:65 "+ₒ" y:66 => ∗(toOrdinal x + toOrdinal y)

/-- A nimber `x` is a group when `Iio x` is closed under addition. Note that `0` is a group under
this definition. -/
@[mk_iff]
structure IsGroup (x : Nimber) where
  add_lt ⦃y z⦄ (hy : y < x) (hz : z < x) : y + z < x

@[simp]
theorem IsGroup.zero : IsGroup 0 where
  add_lt := by simp

@[simp]
theorem IsGroup.one : IsGroup 1 where
  add_lt := by simp

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
    simp_rw [← toNimber.toEquiv.forall_congr_right, RelIso.coe_fn_toEquiv, OrderIso.lt_iff_lt]
    rw [forall_lt_add, forall_lt_mul]
    refine ⟨fun a ha b hb ↦ ?_, fun a ha ↦ ?_⟩
    · have hx : toOrdinal (∗b + ∗y) < x := h.add_lt hb hy
      rw [ne_eq, h.mul_add_eq_of_lt' hb, ← CharTwo.add_eq_iff_eq_add, add_assoc,
        ← toNimber_toOrdinal (∗b + _), ← h.mul_add_eq_of_lt' hx]
      exact (mul_add_lt hx ha).ne
    · rw [h.mul_add_eq_of_lt' (ha.trans hy)]
      simpa using ha.ne
  · apply add_le_of_forall_ne <;>
      simp_rw [← toNimber.toEquiv.forall_congr_right, RelIso.coe_fn_toEquiv, OrderIso.lt_iff_lt]
    · rw [forall_lt_mul]
      intro a ha b hb
      have hx : toOrdinal (∗b + ∗y) < x := h.add_lt hb hy
      rw [ne_eq, h.mul_add_eq_of_lt' hb, add_assoc, ← toNimber_toOrdinal (∗b + _),
        ← h.mul_add_eq_of_lt' hx]
      exact ((mul_add_lt hx ha).trans_le (Ordinal.le_add_right ..)).ne
    · intro b hb
      rw [ne_eq, ← h.mul_add_eq_of_lt' (hb.trans hy)]
      simpa using hb.ne
termination_by (z, y)

theorem IsGroup.mul_add_eq_of_lt {x y : Nimber} (h : IsGroup x) (hy : y < x) (z : Ordinal) :
    ∗(toOrdinal x * z + toOrdinal y) = ∗(toOrdinal x * z) + y :=
  h.mul_add_eq_of_lt' hy z

theorem IsGroup.add_eq_of_lt {x y : Nimber} (h : IsGroup x) (hy : y < x) : x +ₒ y = x + y := by
  simpa using h.mul_add_eq_of_lt hy 1

/-- A version of `IsGroup.add_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsGroup.add_eq_of_lt' {x y : Ordinal} (h : IsGroup (∗x)) (hy : y < x) :
    x + y = toOrdinal (∗x + ∗y) :=
  h.add_eq_of_lt hy

theorem IsGroup.two_opow (x : Ordinal) : IsGroup (∗(2 ^ x)) := by
  refine ⟨fun y z hy hz ↦ ?_⟩
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
      apply (two_opow _).add_lt hm ((two_opow _).add_lt _ _)
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

theorem add_lt_of_log_eq {a b : Ordinal} (ha₀ : a ≠ 0) (hb₀ : b ≠ 0) (h : log 2 a = log 2 b) :
    ∗a + ∗b < ∗(2 ^ log 2 a) := by
  rw [← two_opow_log_add ha₀, ← two_opow_log_add hb₀, h]
  abel_nf
  rw [CharTwo.two_zsmul, zero_add]
  apply (IsGroup.two_opow _).add_lt <;> exact mod_lt _ (opow_ne_zero _ two_ne_zero)

theorem exists_isGroup_add_lt {x : Nimber} (hx : x ≠ 0) : ∃ y ≤ x, IsGroup y ∧ x + y < y := by
  induction x with | h x =>
  refine ⟨_, opow_log_le_self _ hx, .two_opow _, ?_⟩
  exact add_lt_of_log_eq hx (opow_ne_zero _ two_ne_zero) (log_opow one_lt_two _).symm

/-- The nimbers that are groups are exactly `0` and the powers of `2`. -/
theorem isGroup_iff_zero_or_mem_range_two_opow {x : Nimber} :
    IsGroup x ↔ x = 0 ∨ x ∈ range fun y : Ordinal ↦ ∗(2 ^ y) := by
  constructor
  · by_contra! H
    obtain ⟨h, hx, hx'⟩ := H
    apply ((h.add_lt (x := ∗x) _ _).trans_eq (two_opow_log_add hx).symm).false
    · rw [toNimber.lt_iff_lt]
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
scoped notation:70 x:70 "*ₒ" y:71 => ∗(toOrdinal x * toOrdinal y)

/-- A nimber `x` is a ring when `Iio x` is closed under addition and multiplication. Note that `0`
is a ring under this definition. -/
@[mk_iff]
structure IsRing (x : Nimber) extends IsGroup x where
  mul_lt ⦃y z⦄ (hy : y < x) (hz : z < x) : y * z < x

@[simp]
theorem IsRing.zero : IsRing 0 where
  mul_lt := by simp
  __ := IsGroup.zero

@[simp]
theorem IsRing.one : IsRing 1 where
  mul_lt := by simp
  __ := IsGroup.one

protected theorem IsRing.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsRing x) :
    IsRing (sSup s) :=
  ⟨IsGroup.sSup fun x hx ↦ (H x hx).toIsGroup, Principal.sSup (fun x hx ↦ (H x hx).mul_lt)⟩

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
    (hyx : y ≤ x) (hzy : z < y) (H : ∀ z < y, (∗z)⁻¹ < ∗x) : x * z = toOrdinal (∗x * ∗z) := by
  apply le_antisymm
  · apply le_of_forall_ne
    rw [forall_lt_mul]
    intro a ha b hb
    rw [ne_eq, ← toNimber_eq_iff, hx.mul_add_eq_of_lt' hb,
      hx.mul_eq_of_lt' hy hyx (ha.trans hzy) H, add_comm, CharTwo.add_eq_iff_eq_add,
      toNimber_toOrdinal, ← mul_add]
    obtain hza | hza := eq_or_ne (∗z + ∗a) 0
    · cases ha.ne' (add_eq_zero.1 hza)
    · rw [← div_eq_iff hza]
      exact (hx.mul_lt hb (H _ (hy.add_lt hzy (ha.trans hzy)))).ne
  · rw [toOrdinal_le_iff]
    refine mul_le_of_forall_ne fun a ha b hb ↦ ?_
    rw [add_comm, ← add_assoc, ← mul_add, add_comm]
    induction b with | h b =>
    rw [toNimber.lt_iff_lt] at hb
    have hx' : toOrdinal (a * (∗b + ∗z)) < x :=
      hx.mul_lt ha (hx.add_lt (hb.trans (hzy.trans_le hyx)) (hzy.trans_le hyx))
    rw [← toNimber_toOrdinal (_ * _), ← hx.mul_eq_of_lt' hy hyx (hb.trans hzy) H,
      ← toNimber_toOrdinal (a * _), ← hx.mul_add_eq_of_lt' hx']
    exact (mul_add_lt hx' hb).ne
termination_by z

theorem IsRing.mul_eq_of_lt {x y z : Nimber} (hx : IsRing x) (hy : IsGroup y)
    (hyx : y ≤ x) (hzy : z < y) (H : ∀ z < y, z⁻¹ < x) : x *ₒ z = x * z :=
  hx.mul_eq_of_lt' hy hyx hzy H

-- TODO: characterize nim arithmetic on the naturals.
proof_wanted IsRing.two_two_pow (n : ℕ) : IsRing (∗(2 ^ 2 ^ n))

/-! ### Fields -/

/-- A nimber `x` is a field when `Iio x` is closed under addition, multiplication, and division.
Note that `0` and `1` are fields under this definition. -/
@[mk_iff]
structure IsField (x : Nimber) extends IsRing x where
  inv_lt ⦃y⦄ (hy : y < x) : y⁻¹ < x

@[simp]
theorem IsField.zero : IsField 0 where
  inv_lt := by simp
  __ := IsRing.zero

@[simp]
theorem IsField.one : IsField 1 where
  inv_lt := by simp
  __ := IsRing.one

protected theorem IsField.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsField x) :
    IsField (sSup s) := by
  have : IsField (sSup ∅) := by simp
  by_cases hs : BddAbove s; swap; rwa [csSup_of_not_bddAbove hs]
  obtain rfl | hs' := s.eq_empty_or_nonempty; assumption
  refine ⟨IsRing.sSup fun x hx ↦ (H x hx).toIsRing, fun x hx ↦ ?_⟩
  rw [lt_csSup_iff hs hs'] at *
  obtain ⟨a, has, ha⟩ := hx
  exact ⟨a, has, (H a has).inv_lt ha⟩

protected theorem IsField.iSup {ι} {f : ι → Nimber} (H : ∀ i, IsField (f i)) :
    IsField (⨆ i, f i) := by
  apply IsField.sSup
  simpa

theorem IsField.div_lt {x y z : Nimber} (h : IsField x) (hy : y < x) (hz : z < x) : y / z < x :=
  h.toIsRing.mul_lt hy (h.inv_lt hz)

theorem IsField.mul_eq_of_lt {x y : Nimber} (h : IsField x) (hyx : y < x) : x *ₒ y = x * y :=
  h.toIsRing.mul_eq_of_lt h.toIsGroup le_rfl hyx @h.inv_lt

/-- A version of `IsField.mul_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsField.mul_eq_of_lt' {x y : Ordinal} (hx : IsField (∗x)) (hyx : y < x) :
    x * y = toOrdinal (∗x * ∗y) :=
  hx.mul_eq_of_lt hyx

-- One day we'll get rid of this wretched simp lemma.
attribute [-simp] add_one_eq_succ in
private theorem inv_lt_of_not_isField_aux {x : Nimber} (h' : IsRing x) (h : ¬ IsField x) :
    x⁻¹ < x ∧ ∀ y < x⁻¹, y⁻¹ < x := by
  have hx₁ : 1 < x := by rw [← not_le, le_one_iff]; aesop
  have hx₀ : x ≠ 0 := hx₁.ne_bot
  let s := {z | x ≤ z⁻¹}
  simp_rw [isField_iff, h', true_and, not_forall, not_lt] at h
  obtain ⟨a, ha, hxa⟩ := h
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
      · rw [ne_eq, toNimber.eq_iff_eq, toOrdinal_one]
        intro H
        have H' : _ / _ = _ / _ := congrArg (· / toOrdinal x) H
        have hx₀ : toOrdinal x ≠ 0 := hx₀
        have hx₁ : 1 < toOrdinal x := hx₁
        rw [mul_add_div _ hx₀, mul_add_div _ hx₀,
          div_eq_zero_of_lt (toOrdinal.lt_iff_lt.2 hax), div_eq_zero_of_lt hx₁, add_zero, add_zero, toOrdinal.eq_iff_eq] at H'
        apply ha.not_ge (hxs.trans_eq (inv_eq_of_mul_eq_one_left _))
        simpa [H'] using H
    · rw [← toOrdinal.le_iff_le]
      apply le_of_forall_ne
      simp_rw [toOrdinal_one, add_one_eq_succ, toOrdinal_toNimber, Order.lt_succ_iff,
        le_iff_eq_or_lt, forall_eq_or_imp, forall_lt_mul, ne_eq, ← toNimber_eq_iff]
      refine ⟨?_, fun a ha b hb ↦ ?_⟩
      · rw [h'.mul_eq_of_lt hy hyx.le hsy Hs', mul_right_inj' hx₀]
        exact hsy.ne
      · have hay : ∗a < y := ha.trans hsy
        rw [← toNimber_lt_iff] at hb
        refine ne_of_eq_of_ne ?_ (mul_ne_of_ne (a' := ∗b / (∗a + y)) (b' := ∗a) ?_ hay.ne)
        · rw [add_comm, ← add_assoc, ← mul_add, div_mul_cancel₀ _ (add_ne_zero_iff.2 hay.ne),
            ← toOrdinal_toNimber b, h'.mul_add_eq_of_lt hb, ← h'.mul_eq_of_lt hy hyx.le hay Hs']
          exact add_comm ..
        · apply (h'.mul_lt hb (Hs ..)).ne
          rw [← add_comm, ← hy.add_eq_of_lt hay, toNimber_lt_iff]
          apply (add_lt_add_left ha _).trans_eq
          rw [← toNimber_eq_iff, hy.add_eq_of_lt hsy, add_comm, add_cancel_right]

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

-- TODO: this follows directly from `IsRing.two_two_pow` and the surjectivity of `a * ·` for `a ≠ 0`.
proof_wanted IsField.two_two_pow (n : ℕ) : IsField (∗(2 ^ 2 ^ n))

/-! ### Algebraically closed fields -/

/-- A nimber `x` is algebraically closed when `IsField x`, and every non-constant polynomial in the
nimbers with coefficients less than `x` has a root that's less than `x`. Note that `0` and `1` are
algebraically closed under this definition.

For simplicity, the constructor takes a redundant `p ≠ 0` assumption. The lemma
`IsAlgClosed.has_root` proves that this theorem applies (vacuously) when `p = 0` as well. -/
@[mk_iff]
structure IsAlgClosed (x : Nimber) extends IsRing x where
  has_root' ⦃p : Nimber[X]⦄ (hp₀ : p ≠ 0) (hp : p.degree ≠ 0) (hp' : ∀ n, p.coeff n < x) :
    ∃ r < x, p.IsRoot r

theorem IsAlgClosed.has_root {x : Nimber} (h : IsAlgClosed x) {p : Nimber[X]}
    (hp : p.degree ≠ 0) (hp' : ∀ n, p.coeff n < x) : ∃ r < x, p.IsRoot r := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · aesop
  · exact h.has_root' hp₀ hp hp'

@[simp]
theorem IsAlgClosed.zero : IsAlgClosed 0 where
  has_root' := by simp
  __ := IsField.zero

@[simp]
theorem IsAlgClosed.one : IsAlgClosed 1 where
  has_root' p hp₀ hp hp' := by
    apply (hp₀ _).elim
    ext n
    simpa using hp' n
  __ := IsField.one

protected theorem IsAlgClosed.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsAlgClosed x) :
    IsAlgClosed (sSup s) := by
  have : IsAlgClosed (sSup ∅) := by simp
  by_cases hs : BddAbove s; swap; rwa [csSup_of_not_bddAbove hs]
  obtain rfl | hs' := s.eq_empty_or_nonempty; assumption
  refine ⟨IsRing.sSup fun x hx ↦ (H x hx).toIsRing, fun p hp₀ hp hp' ↦ ?_⟩
  simp_rw [lt_csSup_iff hs hs'] at *
  choose f hf using hp'
  obtain ⟨c, hc⟩ := ((Finset.range (p.natDegree + 1)).image f).exists_maximal (by simp)
  have hc' := hc.1
  simp_rw [Finset.mem_image, Finset.mem_range, Nat.lt_succ] at hc'
  obtain ⟨n, hn, rfl⟩ := hc'
  have := (H _ (hf n).1).has_root hp fun m ↦ ?_
  · obtain ⟨r, hr, hr'⟩ := this
    exact ⟨r, ⟨_, (hf n).1, hr⟩, hr'⟩
  · obtain hm | hm := le_or_gt m p.natDegree
    · apply (hf m).2.trans_le (hc.isGreatest.2 _)
      aesop (add simp [Nat.lt_succ])
    · rw [coeff_eq_zero_of_natDegree_lt hm]
      exact bot_le.trans_lt (hf n).2

protected theorem IsAlgClosed.iSup {ι} {f : ι → Nimber} (H : ∀ i, IsAlgClosed (f i)) :
    IsAlgClosed (⨆ i, f i) := by
  apply IsAlgClosed.sSup
  simpa

end Nimber
