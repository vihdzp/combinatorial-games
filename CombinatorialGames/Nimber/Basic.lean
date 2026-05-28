/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public meta import CombinatorialGames.Tactic.Register
public import CombinatorialGames.NatOrdinal.Basic

import CombinatorialGames.Tactic.OrdinalAlias
import Mathlib.Data.Nat.Bitwise

/-!
# Nimbers

The goal of this file is to define the nimbers, constructed as ordinals endowed with new
arithmetical operations. The nim sum `a + b` is recursively defined as the least ordinal not equal
to any `a' + b` or `a + b'` for `a' < a` and `b' < b`. There is also a nim product, defined in the
`CombinatorialGames.Nimber.Field` file.

Nim arithmetic arises within the context of impartial games. By the Sprague-Grundy theorem, each
impartial game is equivalent to some game of nim. If `x ≈ nim o₁` and `y ≈ nim o₂`, then
`x + y ≈ nim (o₁ + o₂)` and `x * y ≈ nim (o₁ * o₂)`, where the ordinals are summed or multiplied
together as nimbers.

## Notation

Following [On Numbers And Games][conway2001] (p. 121), we define notation `∗o` for the cast from
`Ordinal` to `Nimber`. Note that for general `n : ℕ`, `∗n` is **not** the same as `↑n`. For
instance, `∗2 ≠ 0`, whereas `↑2 = ↑1 + ↑1 = 0`.

## Implementation notes

The nimbers inherit the order from the ordinals - this makes working with minimum excluded values
much more convenient. However, the fact that nimbers are of characteristic 2 prevents the order from
interacting with the arithmetic in any nice way.

To reduce API duplication, we opt not to implement operations on `Nimber` on `Ordinal`. The order
isomorphisms `Nimber.of` and `Nimber.val` allow us to cast between them whenever needed.
-/

universe u v

open Function Order

public noncomputable section

/-! ### Basic casts between `Ordinal` and `Nimber` -/

ordinal_alias!
  /-- A type synonym for ordinals with nimber addition and multiplication. -/ Nimber

namespace Nimber

attribute [game_cmp] of_zero of_one
attribute [simp] succ_zero succ_ne_zero Iio_one lt_one_iff

@[inherit_doc] scoped prefix:75 "∗" => of
recommended_spelling "of" for "∗" in [Nimber.«term∗_»]

@[simp] theorem Iio_two : Set.Iio (∗2) = {0, 1} := Order.Iio_two (α := Ordinal)
theorem lt_two_iff {x : Nimber} : x < ∗2 ↔ x = 0 ∨ x = 1 := Set.ext_iff.1 Iio_two x

@[simp] theorem succ_one : Order.succ 1 = ∗2 := one_add_one_eq_two (R := Ordinal)

theorem not_small_nimber : ¬ Small.{u} Nimber.{u} := not_small_ordinal

/-! ### Nimber addition -/

variable {a b c : Nimber.{u}}

-- We write the binders like this so that the termination checker works.
private def add (a b : Nimber.{u}) : Nimber.{u} :=
  sInf {x | (∃ a', ∃ (_ : a' < a), add a' b = x) ∨ ∃ b', ∃ (_ : b' < b), add a b' = x}ᶜ
termination_by (a, b)

#adaptation_note /-- noncomputable is now needed -/ in
/-- Nimber addition is recursively defined so that `a + b` is the smallest nimber not equal to
`a' + b` or `a + b'` for `a' < a` and `b' < b`. -/
@[no_expose]
noncomputable instance : Add Nimber :=
  ⟨Nimber.add⟩

theorem add_def (a b : Nimber) :
    a + b = sInf {x | (∃ a' < a, a' + b = x) ∨ ∃ b' < b, a + b' = x}ᶜ := by
  change add a b = _
  rw [add]
  simp_rw [exists_prop]
  rfl

/-- The set in the definition of `add` is nonempty. -/
private theorem add_nonempty (a b : Nimber.{u}) :
    {x | (∃ a' < a, a' + b = x) ∨ ∃ b' < b, a + b' = x}ᶜ.Nonempty :=
  nonempty_of_not_bddAbove <| not_bddAbove_compl_of_small
    ((· + b) '' Set.Iio a ∪ (a + ·) '' Set.Iio b)

theorem exists_of_lt_add (h : c < a + b) : (∃ a' < a, a' + b = c) ∨ ∃ b' < b, a + b' = c := by
  rw [add_def] at h
  have := notMem_of_lt_csInf' h
  rwa [Set.mem_compl_iff, not_not] at this

theorem add_le_of_forall_ne (h₁ : ∀ a' < a, a' + b ≠ c) (h₂ : ∀ b' < b, a + b' ≠ c) :
    a + b ≤ c := by
  by_contra! h
  have := exists_of_lt_add h
  tauto

private theorem add_ne_of_lt (a b : Nimber) :
    (∀ a' < a, a' + b ≠ a + b) ∧ ∀ b' < b, a + b' ≠ a + b := by
  have H := csInf_mem (add_nonempty a b)
  rw [← add_def] at H
  simpa using H

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

private theorem add_comm (a b : Nimber) : a + b = b + a := by
  rw [add_def, add_def]
  simp_rw [or_comm]
  congr! 7 <;>
    (rw [and_congr_right_iff]; intro; rw [add_comm])
termination_by (a, b)

instance : IsLeftCancelAdd Nimber where
  add_left_cancel a b c h := by
    apply le_antisymm <;>
    apply le_of_not_gt
    · exact fun hc ↦ (add_ne_of_lt a b).2 c hc h.symm
    · exact fun hb ↦ (add_ne_of_lt a c).2 b hb h

instance : IsRightCancelAdd Nimber where
  add_right_cancel a b c h := by
    simp_rw [add_comm] at h
    exact add_left_cancel h

theorem add_eq_zero {a b : Nimber} : a + b = 0 ↔ a = b := by
  constructor <;>
    intro hab
  · obtain h | rfl | h := lt_trichotomy a b
    · have ha : a + a = 0 := add_eq_zero.2 rfl
      rwa [← ha, add_right_inj, eq_comm] at hab
    · rfl
    · have hb : b + b = 0 := add_eq_zero.2 rfl
      rwa [← hb, add_left_inj] at hab
  · rw [← le_zero_iff]
    apply add_le_of_forall_ne <;>
    simp_rw [ne_eq] <;>
    intro x hx
    · rw [add_eq_zero, ← hab]
      exact hx.ne
    · rw [add_eq_zero, hab]
      exact hx.ne'
termination_by (a, b)

theorem add_ne_zero_iff : a + b ≠ 0 ↔ a ≠ b :=
  add_eq_zero.not

@[simp]
theorem add_self (a : Nimber) : a + a = 0 :=
  add_eq_zero.2 rfl

private theorem add_assoc (a b c : Nimber) : a + b + c = a + (b + c) := by
  apply le_antisymm <;>
    apply add_le_of_forall_ne <;>
    intro x hx <;>
    try obtain ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ := exists_of_lt_add hx
  on_goal 1 => rw [add_assoc y, add_ne_add_left]
  on_goal 2 => rw [add_assoc _ y, add_ne_add_right, add_ne_add_left]
  on_goal 3 => rw [add_assoc _ _ x, add_ne_add_right, add_ne_add_right]
  on_goal 4 => rw [← add_assoc x, add_ne_add_left, add_ne_add_left]
  on_goal 5 => rw [← add_assoc _ y, add_ne_add_left, add_ne_add_right]
  on_goal 6 => rw [← add_assoc _ _ y, add_ne_add_right]
  all_goals apply ne_of_lt; assumption
termination_by (a, b, c)

private theorem add_zero (a : Nimber) : a + 0 = a := by
  apply le_antisymm
  · apply add_le_of_forall_ne
    · intro a' ha
      rw [add_zero]
      exact ha.ne
    · intro _ h
      cases not_lt_zero h
  · by_contra! h
    replace h := h -- needed to remind `termination_by`
    have := add_zero (a + 0)
    rw [add_left_inj] at this
    exact this.not_lt h
termination_by a

instance : Neg Nimber :=
  ⟨id⟩

@[simp]
protected theorem neg_eq (a : Nimber) : -a = a :=
  rfl

instance : AddCommGroupWithOne Nimber where
  add_assoc := by exact add_assoc
  add_zero := by exact add_zero
  zero_add _ := by rw [add_comm, add_zero]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := add_self
  add_comm := by exact add_comm

@[simp]
theorem add_cancel_right (a b : Nimber) : a + b + b = a := by
  rw [add_assoc, add_self, add_zero]

@[simp]
theorem add_cancel_left (a b : Nimber) : a + (a + b) = b := by
  rw [← add_assoc, add_self, zero_add]

theorem add_trichotomy {a b c : Nimber} (h : a + b + c ≠ 0) :
    b + c < a ∨ c + a < b ∨ a + b < c := by
  rw [← pos_iff_ne_zero] at h
  obtain ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩ := exists_of_lt_add h <;>
  rw [add_eq_zero] at hx'
  · obtain ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩ := exists_of_lt_add (hx' ▸ hx)
    · rw [← hx', add_comm, add_cancel_right]
      exact Or.inl hx
    · rw [← hx', add_comm a, add_cancel_right]
      exact Or.inr <| Or.inl hx
  · rw [← hx'] at hx
    exact Or.inr <| Or.inr hx

theorem lt_add_cases {a b c : Nimber} (h : a < b + c) : a + c < b ∨ a + b < c := by
  obtain ha | hb | hc := add_trichotomy <| add_assoc a b c ▸ add_ne_zero_iff.2 h.ne
  exacts [(h.asymm ha).elim, Or.inl <| add_comm c a ▸ hb, Or.inr hc]

/-- Nimber addition of naturals corresponds to the bitwise XOR operation. -/
theorem add_nat (a b : ℕ) : ∗a + ∗b = ∗(a ^^^ b) := by
  apply le_antisymm
  · apply add_le_of_forall_ne
    all_goals
      intro c hc
      obtain ⟨c, rfl⟩ := eq_natCast_of_le_natCast hc.le
      rw [OrderIso.lt_iff_lt] at hc
      replace hc := Nat.cast_lt.1 hc
      rw [add_nat]
      simpa using hc.ne
  · apply le_of_not_gt
    intro hc
    obtain ⟨c, hc'⟩ := eq_natCast_of_le_natCast hc.le
    rw [hc', OrderIso.lt_iff_lt, Nat.cast_lt] at hc
    obtain h | h := Nat.lt_xor_cases hc
    · apply h.ne
      simpa [Nat.xor_comm, Nat.xor_xor_cancel_left, ← hc'] using add_nat (c ^^^ b) b
    · apply h.ne
      simpa [Nat.xor_comm, Nat.xor_xor_cancel_left, ← hc'] using add_nat a (c ^^^ a)

end Nimber
