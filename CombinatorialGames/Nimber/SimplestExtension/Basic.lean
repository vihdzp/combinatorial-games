/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/
module

public import CombinatorialGames.Nimber.Field
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.SetTheory.Ordinal.Exponential

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.Monoid.Canonical.Basic
import Mathlib.SetTheory.Ordinal.Principal

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

This file proves the first 3/4 parts of the theorem. The last part will be proven in
`CombinatorialGames.Nimber.SimplestExtension.Algebraic`.

The proof follows Aaron Siegel's Combinatorial Games, pp. 440-444.
-/

open Order Ordinal Set

@[expose] public section

/-! ### Order lemmas -/

theorem Maximal.isGreatest {α : Type*} [LinearOrder α] {P : α → Prop} {x : α} (h : Maximal P x) :
    IsGreatest {y | P y} x := by
  refine ⟨h.1, fun y hy ↦ ?_⟩
  by_contra! hx
  exact (h.le_of_ge hy hx.le).not_gt hx

/-! #### Ordinal lemmas -/

namespace Ordinal

theorem mul_add_lt {a b c d : Ordinal} (h₁ : c < a) (h₂ : b < d) : a * b + c < a * d := by
  apply lt_of_lt_of_le (b := a * (Order.succ b))
  · rwa [mul_succ, add_lt_add_iff_left]
  · apply mul_le_mul_right
    rwa [Order.succ_le_iff]

-- TODO: come up with a better name, probably rename `log_eq_zero` while we're at it.
theorem log_eq_zero' {b x : Ordinal} (hb : b ≤ 1) : log b x = 0 := by
  cases Ordinal.le_one_iff.1 hb <;> simp_all

theorem log_eq_zero_iff {b x : Ordinal} : log b x = 0 ↔ b ≤ 1 ∨ x < b := by
  constructor
  · by_contra!
    apply (le_log_of_opow_le (c := 1) this.2.1 (by simpa using this.2.2)).not_gt
    simpa using this.1
  · rintro (hb | hb)
    · exact log_eq_zero' hb
    · exact log_eq_zero hb

end Ordinal

namespace Nimber
variable {x y z w : Nimber}

/-! ### Groups -/

/-- A nonzero nimber `x` is a group when `Iio x` is closed under addition. -/
@[mk_iff]
structure IsGroup (x : Nimber) where
  add_lt ⦃y z : Nimber⦄ (hy : y < x) (hz : z < x) : y + z < x
  ne_zero : x ≠ 0

theorem IsGroup.neZero (h : IsGroup x) : NeZero x where
  out := h.ne_zero

@[aesop forward safe]
theorem IsGroup.zero_lt (h : IsGroup x) : 0 < x := bot_lt_iff_ne_bot.2 h.ne_zero
alias IsGroup.pos := IsGroup.zero_lt

theorem IsGroup.sum_lt (h : IsGroup x) {ι} {s : Finset ι}
    {f : ι → Nimber} (hs : ∀ y ∈ s, f y < x) : s.sum f < x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using h.zero_lt
  | insert a s ha IH =>
    rw [Finset.sum_insert ha]
    apply h.add_lt <;> simp_all

/-- `Iio x` as a subgroup of `Nimber`. -/
def IsGroup.toAddSubgroup (h : IsGroup x) : AddSubgroup Nimber where
  carrier := Iio x
  zero_mem' := h.zero_lt
  add_mem' := @h.add_lt
  neg_mem' := id

@[simp] theorem val_toAddSubgroup_lt (h : IsGroup x) (y : h.toAddSubgroup) : y < x := y.2
@[simp] theorem mem_toAddSubgroup_iff (h : IsGroup x) : y ∈ h.toAddSubgroup ↔ y < x := .rfl

theorem IsGroup.closure_Iio (h : IsGroup x) : AddSubgroup.closure (Iio x) = h.toAddSubgroup :=
  h.toAddSubgroup.closure_eq

@[simp]
theorem IsGroup.one : IsGroup 1 where
  add_lt := by simp
  ne_zero := one_ne_zero

protected theorem IsGroup.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsGroup x)
    (ne : s.Nonempty) (bdd : BddAbove s) : IsGroup (sSup s) where
  add_lt := Principal.sSup (fun x hx ↦ (H x hx).add_lt)
  ne_zero h := by
    have lub := isLUB_csSup ne bdd
    obtain ⟨x, hx⟩ := ne
    apply (H x hx).ne_zero
    rw [← Nimber.le_zero, ← h]
    exact lub.left hx

protected theorem IsGroup.iSup {ι} [Nonempty ι] {f : ι → Nimber} (H : ∀ i, IsGroup (f i))
    (bdd : BddAbove (range f) := by apply Nimber.bddAbove_of_small) : IsGroup (⨆ i, f i) :=
  .sSup (by simpa) (range_nonempty f) bdd

theorem IsGroup.le_add_self (h : IsGroup x) (hy : y < x) : x ≤ x + y := by
  by_contra!
  simpa using h.add_lt this hy

/-- The first **simplest extension theorem**: if `x ≠ 0` is not a group, then `x` can be written as
`y + z` for some `y, z < x`. -/
theorem exists_add_of_not_isGroup (h : ¬IsGroup x) (ne : x ≠ 0) : ∃ y < x, ∃ z < x, y + z = x := by
  simp_rw [isGroup_iff, and_iff_left ne, not_forall, not_lt] at h
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
  · apply le_of_forall_lt_imp_ne
    simp_rw [← of.toEquiv.forall_congr_right, RelIso.coe_fn_toEquiv, OrderIso.lt_iff_lt]
    rw [forall_lt_add_iff_lt_left, forall_lt_mul]
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
      exact ((mul_add_lt hx ha).trans_le (le_self_add ..)).ne
    · intro b hb
      rw [ne_eq, ← h.mul_add_eq_of_lt' (hb.trans hy)]
      simpa using hb.ne
termination_by (z, y)

theorem IsGroup.mul_add_eq_of_lt (h : IsGroup x) (hy : y < x) (z : Ordinal) :
    ∗(x.val * z + y.val) = ∗(x.val * z) + y :=
  h.mul_add_eq_of_lt' hy z

theorem IsGroup.add_eq_of_lt (h : IsGroup x) (hy : y < x) : ∗(x.val + y.val) = x + y := by
  simpa using h.mul_add_eq_of_lt hy 1

/-- A version of `IsGroup.add_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsGroup.add_eq_of_lt' {x y : Ordinal} (h : IsGroup (∗x)) (hy : y < x) :
    x + y = val (∗x + ∗y) :=
  h.add_eq_of_lt hy

@[simp]
theorem IsGroup.two_opow (x : Ordinal) : IsGroup (∗2 ^ x) := by
  refine ⟨fun y z hy hz ↦ ?_, by simp⟩
  induction y with | mk y
  induction z with | mk z
  obtain rfl | hy₀ := eq_or_ne y 0; · simpa
  obtain rfl | hz₀ := eq_or_ne z 0; · simpa
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
    apply (add_right_strictMono H').trans_le
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

@[simp]
theorem IsGroup.omega0_opow (x : Ordinal) : IsGroup (∗ω ^ x) := by
  rw [← natCast_opow_omega0 one_lt_two, ← opow_mul]
  exact .two_opow _

@[simp] theorem IsGroup.two : IsGroup (∗2) := by simpa using IsGroup.two_opow 1

theorem two_opow_log_add {o : Ordinal} (ho : o ≠ 0) : ∗(2 ^ log 2 o) + ∗(o % 2 ^ log 2 o) = ∗o :=
  ((IsGroup.two_opow _).add_eq_of_lt (mod_lt _ (opow_ne_zero _ two_ne_zero))).symm.trans
    (o.two_opow_log_add ho)

theorem add_lt_of_log_eq {a b : Ordinal} (ha₀ : a ≠ 0) (hb₀ : b ≠ 0) (h : log 2 a = log 2 b) :
    ∗a + ∗b < ∗2 ^ log 2 a := by
  rw [← two_opow_log_add ha₀, ← two_opow_log_add hb₀, h]
  abel_nf
  rw [CharTwo.two_zsmul, zero_add]
  apply (IsGroup.two_opow _).add_lt <;> exact mod_lt _ (opow_ne_zero _ two_ne_zero)

theorem exists_isGroup_add_lt (hx : x ≠ 0) : ∃ y ≤ x, IsGroup y ∧ x + y < y := by
  induction x with | mk x
  refine ⟨_, opow_log_le_self _ hx, .two_opow _, ?_⟩
  exact add_lt_of_log_eq hx (opow_ne_zero _ two_ne_zero) (log_opow one_lt_two _).symm

/-- The nimbers that are groups are exactly the powers of `2`. -/
theorem isGroup_iff_mem_range_two_opow : IsGroup x ↔ x ∈ range fun y : Ordinal ↦ ∗2 ^ y := by
  refine ⟨?_, Set.forall_mem_range.2 .two_opow x⟩
  by_contra! H
  obtain ⟨h, hx⟩ := H
  apply ((h.add_lt (x := ∗x) _ _).trans_eq (two_opow_log_add h.ne_zero).symm).false
  · rw [of.lt_iff_lt]
    apply (opow_log_le_self _ h.ne_zero).lt_of_ne
    contrapose! hx
    exact hx ▸ mem_range_self _
  · exact mod_opow_log_lt_self _ h.ne_zero

/-- A version of `isGroup_iff_zero_or_mem_range_two_opow` stated in terms of `Ordinal`. -/
theorem isGroup_iff_zero_or_mem_range_two_opow' {x : Ordinal} :
    IsGroup (∗x) ↔ x ∈ range (2 ^ · : Ordinal → _) :=
  isGroup_iff_mem_range_two_opow

theorem IsGroup.opow (h : IsGroup x) (a : Ordinal) : IsGroup (∗x.val ^ a) := by
  rw [isGroup_iff_mem_range_two_opow] at h
  obtain ⟨b, hb, rfl⟩ := h
  simp [← opow_mul]

/-- A version of `IsGroup.opow` stated in terms of `Ordinal`. -/
theorem IsGroup.opow' {x : Ordinal} (h : IsGroup (∗x)) (a : Ordinal) : IsGroup (∗x ^ a) :=
  h.opow a

theorem IsGroup.pow (h : IsGroup x) (n : ℕ) : IsGroup (∗x.val ^ n) :=
  mod_cast h.opow n

/-- A version of `IsGroup.pow` stated in terms of `Ordinal`. -/
theorem IsGroup.pow' {x : Ordinal} (h : IsGroup (∗x)) (n : ℕ) : IsGroup (∗x ^ n) :=
  h.pow n

/-! ### Rings -/

/-- A nimber `x` is a ring when `1 < x` and `Iio x` is closed under addition and multiplication. -/
@[mk_iff]
structure IsRing (x : Nimber) extends IsGroup x where
  mul_lt ⦃y z : Nimber⦄ (hy : y < x) (hz : z < x) : y * z < x
  ne_one : x ≠ 1

attribute [aesop forward safe] IsRing.toIsGroup

@[aesop forward safe]
theorem IsRing.one_lt (h : IsRing x) : 1 < x := by
  rw [← not_le, Nimber.le_one_iff, not_or]
  exact ⟨h.ne_zero, h.ne_one⟩

theorem IsRing.pow_lt (h : IsRing x) {n : ℕ} (hy : y < x) :
    y ^ n < x := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact h.one_lt
  | succ n ih =>
    rw [pow_succ]
    exact h.mul_lt ih hy

@[simp]
theorem IsRing.two : IsRing (∗2) where
  ne_one := by rw [← of_one, of.eq_iff_eq.ne]; simp
  mul_lt := by simp_rw [lt_two_iff]; aesop
  __ := IsGroup.two

/-- `Iio x` as a subring of `Nimber`. -/
def IsRing.toSubring (h : IsRing x) : Subring Nimber where
  toAddSubgroup := h.toAddSubgroup
  one_mem' := h.one_lt
  mul_mem' := @h.mul_lt

@[simp] theorem val_toSubring_lt (h : IsRing x) (y : h.toSubring) : y < x := y.2
@[simp] theorem mem_toSubring_iff (h : IsRing x) : y ∈ h.toSubring ↔ y < x := .rfl

theorem IsRing.closure_Iio (h : IsRing x) : Subring.closure (Iio x) = h.toSubring :=
  h.toSubring.closure_eq

protected theorem IsRing.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsRing x)
    (ne : s.Nonempty) (bdd : BddAbove s) : IsRing (sSup s) where
  toIsGroup := .sSup (fun x hx => (H x hx).toIsGroup) ne bdd
  mul_lt := Principal.sSup fun x hx ↦ (H x hx).mul_lt
  ne_one h := by
    have lub := isLUB_csSup ne bdd
    obtain ⟨x, hx⟩ := ne
    apply (H x hx).one_lt.not_ge
    rw [← h]
    exact lub.left hx

protected theorem IsRing.iSup {ι} [Nonempty ι] {f : ι → Nimber} (H : ∀ i, IsRing (f i))
    (bdd : BddAbove (range f) := by apply Nimber.bddAbove_of_small) : IsRing (⨆ i, f i) :=
  .sSup (by simpa) (range_nonempty f) bdd

theorem IsGroup.mul_le_of_forall_lt (h : IsGroup x) {y z : Nimber}
    (hyl : ∀ l < z, y * l < x) (hrz : ∀ r < y, r * z < x)
    (hrl : ∀ r < y, ∀ l < z, r * l < x) : y * z ≤ x :=
  mul_le_of_forall_ne fun a ha b hb hx ↦
    hx.not_lt (h.add_lt (h.add_lt (hrz a ha) (hyl b hb)) (hrl a ha b hb))

/-- The second **simplest extension theorem**: if `x ≠ 1` is a group but not a ring, then `x` can be
written as `y * z` for some `y, z < x`. -/
theorem IsGroup.exists_mul_of_not_isRing (h' : IsGroup x) (h : ¬IsRing x) (ne : x ≠ 1) :
    ∃ y < x, ∃ z < x, y * z = x := by
  contrapose! h
  refine { toIsGroup := h', ne_one := ne, mul_lt a b ha hb := ?_ }
  induction a using WellFoundedLT.induction generalizing b with | ind a iha
  induction b using WellFoundedLT.induction with | ind b ihb
  refine lt_of_le_of_ne (h'.mul_le_of_forall_lt ?_ ?_ ?_) (h a ha b hb)
  · exact fun l hl => ihb l hl (hl.trans hb)
  · exact fun r hr => iha r hr b (hr.trans ha) hb
  · exact fun r hr l hl => iha r hr l (hr.trans ha) (hl.trans hb)

/-- A version of `IsGroup.mul_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsGroup.mul_eq_of_lt' {x y z w : Ordinal}
    (hx : IsGroup (∗x)) (hy : IsGroup (∗y)) (hz : IsGroup (∗z))
    (hyx : y ≤ x) (hyz : y ≤ z) (hwy : w < y)
    (H : ∀ a < y, (∗a)⁻¹ < ∗z) (H' : ∀ ⦃a b⦄, a < x → b < z → ∗a * ∗b < ∗x) :
    x * w = val (∗x * ∗w) := by
  apply le_antisymm
  · apply le_of_forall_lt_imp_ne
    rw [forall_lt_mul]
    intro a ha b hb
    rw [ne_eq, ← of_eq_iff, hx.mul_add_eq_of_lt' hb,
      hx.mul_eq_of_lt' hy hz hyx hyz (ha.trans hwy) H H', add_comm, CharTwo.add_eq_iff_eq_add,
      of_val, ← mul_add]
    obtain hwa | hwa := eq_or_ne (∗w + ∗a) 0
    · cases ha.ne' (add_eq_zero.1 hwa)
    · rw [← div_eq_iff hwa]
      exact (H' hb (H _ (hy.add_lt hwy (ha.trans hwy)))).ne
  · rw [val_le_iff]
    refine mul_le_of_forall_ne fun a ha b hb ↦ ?_
    rw [add_comm, ← add_assoc, ← mul_add, add_comm]
    induction b with | mk b
    rw [of.lt_iff_lt] at hb
    have hwz := hwy.trans_le hyz
    have hx' : val (a * (∗b + ∗w)) < x := H' ha (hz.add_lt (hb.trans hwz) hwz)
    rw [← of_val (_ * _), ← hx.mul_eq_of_lt' hy hz hyx hyz (hb.trans hwy) H H',
      ← of_val (a * _), ← hx.mul_add_eq_of_lt' hx']
    exact (mul_add_lt hx' hb).ne
termination_by w

theorem IsGroup.mul_eq_of_lt (hx : IsGroup x) (hy : IsGroup y) (hz : IsGroup z)
    (hyx : y ≤ x) (hyz : y ≤ z) (hwy : w < y)
    (H : ∀ a < y, a⁻¹ < z) (H' : ∀ ⦃a b⦄, a < x → b < z → a * b < x) : ∗(x.val * w.val) = x * w :=
  hx.mul_eq_of_lt' hy hz hyx hyz hwy H H'

/-- A version of `IsRing.mul_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsRing.mul_eq_of_lt' {x y z : Ordinal} (hx : IsRing (∗x)) (hy : IsGroup (∗y))
    (hyx : y ≤ x) (hzy : z < y) (H : ∀ z < y, (∗z)⁻¹ < ∗x) : x * z = val (∗x * ∗z) :=
  hx.toIsGroup.mul_eq_of_lt' hy hx.toIsGroup hyx hyx hzy H hx.mul_lt

theorem IsRing.mul_eq_of_lt (hx : IsRing x) (hy : IsGroup y)
    (hyx : y ≤ x) (hzy : z < y) (H : ∀ z < y, z⁻¹ < x) : ∗(x.val * z.val) = x * z :=
  hx.mul_eq_of_lt' hy hyx hzy H

-- TODO: characterize nim arithmetic on the naturals.
proof_wanted IsRing.two_two_pow (n : ℕ) : IsRing (∗(2 ^ 2 ^ n))

/-! ### Fields -/

/-- A nimber `x` is a field when `1 < x` and `Iio x` is closed under
addition, multiplication, and division.

For simplicity, the constructor takes a redundant `y ≠ 0` assumption. The lemma `IsField.inv_lt`
proves that this theorem applies when `y = 0` as well. -/
@[mk_iff]
structure IsField (x : Nimber) extends IsRing x where
  inv_lt' ⦃y : Nimber⦄ (hy₀ : y ≠ 0) (hy : y < x) : y⁻¹ < x

attribute [aesop forward safe] IsField.toIsRing

theorem IsField.inv_lt (h : IsField x) (hy : y < x) : y⁻¹ < x := by
  obtain rfl | hy₀ := eq_or_ne y 0
  · simpa
  · exact h.inv_lt' hy₀ hy

theorem IsField.div_lt (h : IsField x) (hy : y < x) (hz : z < x) : y / z < x :=
  h.toIsRing.mul_lt hy (h.inv_lt hz)

@[simp]
theorem IsField.two : IsField (∗2) where
  inv_lt' := by simp [lt_two_iff]
  __ := IsRing.two

/-- `Iio x` as a subring of `Nimber`. -/
def IsField.toSubfield (h : IsField x) : Subfield Nimber where
  toSubring := h.toSubring
  inv_mem' := @h.inv_lt

@[simp] theorem val_toSubfield_lt (h : IsField x) (y : h.toSubfield) : y < x := y.2
@[simp] theorem mem_toSubfield_iff (h : IsField x) : y ∈ h.toSubfield ↔ y < x := .rfl

theorem IsField.closure_Iio (h : IsField x) : Subfield.closure (Iio x) = h.toSubfield :=
  h.toSubfield.closure_eq

protected theorem IsField.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsField x)
    (ne : s.Nonempty) (bdd : BddAbove s) : IsField (sSup s) where
  toIsRing := .sSup (fun x hx => (H x hx).toIsRing) ne bdd
  inv_lt' y _ hy := by
    rw [lt_csSup_iff bdd ne] at hy ⊢
    obtain ⟨x, hx, hx'⟩ := hy
    exact ⟨x, hx, (H x hx).inv_lt hx'⟩

protected theorem IsField.iSup {ι} [Nonempty ι] {f : ι → Nimber} (H : ∀ i, IsField (f i))
    (bdd : BddAbove (range f) := by apply Nimber.bddAbove_of_small) : IsField (⨆ i, f i) :=
  .sSup (by simpa) (range_nonempty f) bdd

theorem IsField.mul_eq_of_lt (hx : IsRing x) (hy : IsField y) (hyx : y ≤ x) (hzy : z < y) :
    ∗(x.val * z.val) = x * z :=
  hx.mul_eq_of_lt hy.toIsGroup hyx hzy fun _ hw ↦ (hy.inv_lt hw).trans_le hyx

/-- A version of `IsField.mul_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsField.mul_eq_of_lt' {x y z : Ordinal} (hx : IsRing (∗x)) (hy : IsField (∗y))
    (hyx : y ≤ x) (hzy : z < y) : x * z = val (∗x * ∗z) :=
  hy.mul_eq_of_lt hx hyx hzy

private theorem inv_lt_of_not_isField_aux (h' : IsRing x) (h : ¬IsField x) :
    x⁻¹ < x ∧ ∀ y < x⁻¹, y⁻¹ < x := by
  have hx₁ : 1 < x := h'.one_lt
  have hx₀ : x ≠ 0 := hx₁.ne_bot
  let s := {z | x ≤ z⁻¹}
  simp_rw [isField_iff, h', true_and, not_forall, not_lt] at h
  obtain ⟨a, -, ha, hxa⟩ := h
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
      apply le_of_forall_lt_imp_ne
      simp_rw [val_one, val_of, lt_add_one_iff, le_iff_eq_or_lt, forall_eq_or_imp, forall_lt_mul,
        ne_eq, ← of_eq_iff]
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
          apply (add_lt_add_right ha _).trans_eq
          rw [← of_eq_iff, hy.add_eq_of_lt hsy, add_comm, add_cancel_right]

theorem IsRing.inv_lt_of_not_isField (h' : IsRing x) (h : ¬ IsField x)
    (hy : y < x⁻¹) : y⁻¹ < x :=
  (inv_lt_of_not_isField_aux h' h).2 y hy

theorem IsRing.inv_le_of_not_isField (h' : IsRing x) (h : ¬ IsField x)
    (hy : y ≤ x⁻¹) : y⁻¹ ≤ x := by
  obtain rfl | hy := hy.eq_or_lt; · simp
  exact (h'.inv_lt_of_not_isField h hy).le

/-- The third **simplest extension theorem**: if `x` is a ring but not a field, then `x` can be
written as `y⁻¹` for some `y < x`. In simpler wording, `x⁻¹ < x`. -/
theorem IsRing.inv_lt_self_of_not_isField (h' : IsRing x) (h : ¬ IsField x) : x⁻¹ < x :=
  (inv_lt_of_not_isField_aux h' h).1

/-- A version of `IsField.opow_mul_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsField.opow_mul_eq_of_lt' {x z : Ordinal}
    (hx : IsField (∗x)) (y : Ordinal) (hz : z < x) : x ^ y * z = val (∗(x ^ y) * ∗z) := by
  have hx' := hx.opow' y
  obtain rfl | hy := eq_zero_or_pos y; · simp
  apply hx'.mul_eq_of_lt' hx.toIsGroup hx.toIsGroup (left_le_opow _ hy) le_rfl hz @hx.inv_lt
  intro a b ha hb
  induction a using WellFoundedLT.induction with | ind a IH
  obtain rfl | ha' := eq_or_ne a 0; · simpa
  rw [← div_add_mod a (x ^ log x a), (hx.opow' _).mul_add_eq_of_lt', add_mul]
  · apply hx'.add_lt
    · have hax' : a / x ^ log x a < x := div_opow_log_lt a hx.one_lt
      have hax : val (∗(a / _) * ∗b) < x := hx.mul_lt hax' hb
      have hay : log x a < y := by
        rwa [← lt_opow_iff_log_lt _ ha']
        exact hx.one_lt
      rw [IsField.opow_mul_eq_of_lt' hx _ hax', of_val, mul_assoc, ← val_lt_iff,
        ← of_val (∗_ * ∗_), ← IsField.opow_mul_eq_of_lt' hx _ hax]
      apply (opow_le_opow_right hx.pos hay.succ_le).trans_lt'
      rw [opow_succ]
      exact mul_lt_mul_of_pos_left hax (opow_pos _ hx.pos)
    · exact IH _ (mod_opow_log_lt_self _ ha') ((mod_le ..).trans_lt ha)
  · exact mod_lt _ (opow_ne_zero _ hz.ne_bot)
termination_by y

theorem IsField.opow_mul_eq_of_lt (hx : IsField x) (y : Ordinal) (hz : z < x) :
    ∗(val x ^ y * val z) = ∗(val x ^ y) * z :=
  hx.opow_mul_eq_of_lt' y hz

/-- A version of `IsField.pow_mul_eq_of_lt` stated in terms of `Ordinal`. -/
theorem IsField.pow_mul_eq_of_lt' {x z : Ordinal}
    (hx : IsField (∗x)) (n : ℕ) (hz : z < x) : x ^ n * z = val (∗(x ^ n) * ∗z) :=
  mod_cast hx.opow_mul_eq_of_lt' n hz

theorem IsField.pow_mul_eq_of_lt
    (hx : IsField x) (n : ℕ) (hz : z < x) : ∗(val x ^ n * val z) = ∗(val x ^ n) * z :=
  mod_cast hx.opow_mul_eq_of_lt n hz

/-- If `x` is a field and `y` is an `x`-subspace, then `y` is an ordinal power of `x`. -/
theorem IsField.opow_log_eq_of_isGroup (hx : IsField x) (hy : IsGroup y)
    (hxy : ∀ z w, z < x → w < y → z * w < y) : ∗(x.val ^ log x.val y.val) = y := by
  apply le_antisymm
  · exact opow_log_le_self _ hy.ne_zero
  · by_contra! hy'
    have H₁ : ∗(val y / val x ^ log x.val y.val) < x := div_opow_log_lt _ hx.one_lt
    have H₂ : ∗(val y % val x ^ log x.val y.val) < y := mod_opow_log_lt_self _ hy.ne_zero
    apply (hy.add_lt (hxy _ _ H₁ hy') H₂).ne
    rw [mul_comm, ← hx.opow_mul_eq_of_lt _ H₁, ← (hx.opow _).mul_add_eq_of_lt']
    · exact div_add_mod ..
    · exact mod_lt _ (opow_ne_zero _ hx.ne_zero)

/-- If `x` is a field and `y` is a ring with `x ≤ y`, then `y` is an ordinal power of `x`. -/
theorem IsField.opow_log_eq_of_isRing (hx : IsField x) (hy : IsRing y) (hxy : x ≤ y) :
    ∗(x.val ^ log x.val y.val) = y :=
  hx.opow_log_eq_of_isGroup hy.toIsGroup fun _z _w hz hw ↦ hy.mul_lt (hz.trans_le hxy) hw

theorem IsField.mul_lt_opow_of_left_lt {x y z : Nimber} {o : Ordinal}
    (h : IsField x) (hy : y < x) (hz : z < ∗(val x ^ o)) : y * z < ∗(val x ^ o) := by
  induction o using WellFoundedLT.induction generalizing z with | ind o IH
  obtain rfl | ho := eq_or_ne o 0
  · simp_all
  have H₁ : of (val z / val x ^ log (val x) (val z)) < x := div_opow_log_lt _ h.one_lt
  have H₂ := h.mul_lt H₁ hy
  have H₃ : log (val x) (val z) < o := (lt_opow_iff_log_lt' h.one_lt ho).1 hz
  have H₄ : val z % val x ^ log (val x) (val z) < _ := mod_lt _ (opow_ne_zero _ h.ne_zero)
  rw [← of_val z, ← div_add_mod z.val (x.val ^ log x.val z.val), (h.opow _).mul_add_eq_of_lt' H₄,
    mul_add, ← val_of (_ / _), h.opow_mul_eq_of_lt _ H₁]
  apply (h.opow _).add_lt
  · rw [mul_comm, mul_assoc, ← val_lt_iff, ← of_val (of _ * y), ← h.opow_mul_eq_of_lt]
    · exact opow_mul_lt_opow H₂ H₃
    · exact H₂
  · exact (IH _ H₃ H₄).trans_le (opow_le_opow_right h.pos H₃.le)

theorem IsField.mul_lt_opow_of_right_lt {x y z : Nimber} {o : Ordinal}
    (h : IsField x) (hy : y < ∗(val x ^ o)) (hz : z < x) : y * z < ∗(val x ^ o) :=
  mul_comm y z ▸ h.mul_lt_opow_of_left_lt hz hy

theorem IsField.mul_lt_pow_of_left_lt {x y z : Nimber} {n : ℕ}
    (h : IsField x) (hy : y < x) (hz : z < ∗(val x ^ n)) : y * z < ∗(val x ^ n) :=
  (opow_natCast x.val n ▸ h.mul_lt_opow_of_left_lt) hy hz

theorem IsField.mul_lt_pow_of_right_lt {x y z : Nimber} {n : ℕ}
    (h : IsField x) (hy : y < ∗(val x ^ n)) (hz : z < x) : y * z < ∗(val x ^ n) :=
  (opow_natCast x.val n ▸ h.mul_lt_opow_of_right_lt) hy hz

-- TODO: this follows from `IsRing.two_two_pow` and the surjectivity of `a * ·` for `a ≠ 0`.
proof_wanted IsField.two_two_pow (n : ℕ) : IsField (∗(2 ^ 2 ^ n))

theorem IsField.exists_linearCombination_of_lt {x : Nimber} (h : IsField x)
    {o : Ordinal} {y : Nimber} (hy : y < ∗(val x ^ o)) :
    ∃ f : Ordinal →₀ h.toSubfield, (SetLike.coe f.support ⊆ Iio o) ∧
    f.linearCombination h.toSubfield (fun o => ∗(val x ^ o)) = y := by
  sorry

theorem IsField.linearCombination_lt {x : Nimber} (h : IsField x)
    {o : Ordinal} {f : Ordinal →₀ h.toSubfield} (hf : SetLike.coe f.support ⊆ Iio o) :
    f.linearCombination h.toSubfield (fun o => ∗(val x ^ o)) < ∗(val x ^ o) := by
  sorry

end Nimber
end
