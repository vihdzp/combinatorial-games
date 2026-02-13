/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Tactic.OrdinalAlias
import CombinatorialGames.Tactic.Register
import Mathlib.Data.Nat.Bitwise
import Mathlib.SetTheory.Ordinal.Family

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

noncomputable section

/-! ### Basic casts between `Ordinal` and `Nimber` -/

ordinal_alias!
  /-- A type synonym for ordinals with nimber addition and multiplication. -/ Nimber

namespace Nimber

attribute [game_cmp] of_zero of_one

@[inherit_doc] scoped prefix:75 "∗" => of
recommended_spelling "of" for "∗" in [Nimber.«term∗_»]

@[simp] theorem Iio_two : Set.Iio (∗2) = {0, 1} := Ordinal.Iio_two
theorem lt_two_iff {x : Nimber} : x < ∗2 ↔ x = 0 ∨ x = 1 := Set.ext_iff.1 Iio_two x

@[simp] theorem succ_one : Order.succ 1 = ∗2 := Ordinal.succ_one

theorem not_small_nimber : ¬ Small.{u} Nimber.{u} := not_small_ordinal

/-! ### Nimber addition -/

variable {a b c : Nimber.{u}}

-- We write the binders like this so that the termination checker works.
private def add (a b : Nimber.{u}) : Nimber.{u} :=
  sInf {x | (∃ a', ∃ (_ : a' < a), Nimber.add a' b = x) ∨
    ∃ b', ∃ (_ : b' < b), Nimber.add a b' = x}ᶜ
termination_by (a, b)

/-- Nimber addition is recursively defined so that `a + b` is the smallest nimber not equal to
`a' + b` or `a + b'` for `a' < a` and `b' < b`. -/
instance : Add Nimber :=
  ⟨Nimber.add⟩

theorem add_def (a b : Nimber) :
    a + b = sInf {x | (∃ a' < a, a' + b = x) ∨ ∃ b' < b, a + b' = x}ᶜ := by
  change Nimber.add a b = _
  rw [Nimber.add]
  simp_rw [exists_prop]
  rfl

/-- The set in the definition of `Nimber.add` is nonempty. -/
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

protected theorem add_comm (a b : Nimber) : a + b = b + a := by
  rw [add_def, add_def]
  simp_rw [or_comm]
  congr! 7 <;>
    (rw [and_congr_right_iff]; intro; rw [Nimber.add_comm])
termination_by (a, b)

instance : IsLeftCancelAdd Nimber where
  add_left_cancel a b c h := by
    apply le_antisymm <;>
    apply le_of_not_gt
    · exact fun hc ↦ (add_ne_of_lt a b).2 c hc h.symm
    · exact fun hb ↦ (add_ne_of_lt a c).2 b hb h

instance : IsRightCancelAdd Nimber where
  add_right_cancel a b c h := by
    simp_rw [Nimber.add_comm] at h
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
  · rw [← Nimber.le_zero]
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

protected theorem add_assoc (a b c : Nimber) : a + b + c = a + (b + c) := by
  apply le_antisymm <;>
    apply add_le_of_forall_ne <;>
    intro x hx <;>
    try obtain ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ := exists_of_lt_add hx
  on_goal 1 => rw [Nimber.add_assoc y, add_ne_add_left]
  on_goal 2 => rw [Nimber.add_assoc _ y, add_ne_add_right, add_ne_add_left]
  on_goal 3 => rw [Nimber.add_assoc _ _ x, add_ne_add_right, add_ne_add_right]
  on_goal 4 => rw [← Nimber.add_assoc x, add_ne_add_left, add_ne_add_left]
  on_goal 5 => rw [← Nimber.add_assoc _ y, add_ne_add_left, add_ne_add_right]
  on_goal 6 => rw [← Nimber.add_assoc _ _ y, add_ne_add_right]
  all_goals apply ne_of_lt; assumption
termination_by (a, b, c)

protected theorem add_zero (a : Nimber) : a + 0 = a := by
  apply le_antisymm
  · apply add_le_of_forall_ne
    · intro a' ha
      rw [Nimber.add_zero]
      exact ha.ne
    · intro _ h
      exact (Nimber.not_neg _ h).elim
  · by_contra! h
    replace h := h -- needed to remind `termination_by`
    have := Nimber.add_zero (a + 0)
    rw [add_left_inj] at this
    exact this.not_lt h
termination_by a

protected theorem zero_add (a : Nimber) : 0 + a = a := by
  rw [Nimber.add_comm, Nimber.add_zero]

instance : Neg Nimber :=
  ⟨id⟩

@[simp]
protected theorem neg_eq (a : Nimber) : -a = a :=
  rfl

instance : AddCommGroupWithOne Nimber where
  add_assoc := Nimber.add_assoc
  add_zero := Nimber.add_zero
  zero_add := Nimber.zero_add
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := add_self
  add_comm := Nimber.add_comm

-- #34622
section Mathlib

theorem _root_.Set.range_if {α β : Type*} {p : α → Prop} [DecidablePred p] {x y : β}
    (hp : ∃ a, p a) (hn : ∃ a, ¬ p a) :
    Set.range (fun a ↦ if p a then x else y) = {x, y} := by
  grind

theorem natCast_eq_if (n : ℕ) : (n : Nimber) = if Even n then 0 else 1 := by
  induction n <;> aesop

@[simp]
theorem range_natCast : Set.range ((↑) : ℕ → Nimber) = {0, 1} := by
  rw [funext natCast_eq_if, Set.range_if]
  · use 0; simp
  · use 1; simp

theorem natCast_eq_mod (n : ℕ) : (n : Nimber) = (n % 2 : ℕ) := by
  simp [natCast_eq_if, Nat.even_iff]

@[simp]
theorem ofNat_eq_mod (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : Nimber) = (n % 2 : ℕ) :=
  natCast_eq_mod n

theorem intCast_eq_if (n : ℤ) : (n : Nimber) = if Even n then 0 else 1 := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simpa using natCast_eq_if n

@[simp]
theorem range_intCast : Set.range ((↑) : ℤ → Nimber) = {0, 1} := by
  rw [funext intCast_eq_if, Set.range_if]
  · use 0; simp
  · use 1; simp

theorem intCast_eq_mod (n : ℤ) : (n : Nimber) = (n % 2 : ℤ) := by
  simp [intCast_eq_if, Int.even_iff]

end Mathlib

@[simp]
theorem add_cancel_right (a b : Nimber) : a + b + b = a := by
  rw [add_assoc, add_self, add_zero]

@[simp]
theorem add_cancel_left (a b : Nimber) : a + (a + b) = b := by
  rw [← add_assoc, add_self, zero_add]

theorem add_trichotomy {a b c : Nimber} (h : a + b + c ≠ 0) :
    b + c < a ∨ c + a < b ∨ a + b < c := by
  rw [← Nimber.pos_iff_ne_zero] at h
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
