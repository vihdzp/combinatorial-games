/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Impartial.Grundy
import Mathlib.Data.Nat.Bitwise
import Mathlib.SetTheory.Ordinal.Family

/-!
# Nimber addition

The goal of this file is to define nimber addition. Nimbers were "constructed" in
`CombinatorialGames.Nimber.Defs` as a type alias for `Ordinal`. Using this barebones definition, we
proved the Sprague-Grundy theorem, which allows us to simply define the nim sum `a + b` as the
Grundy value of `nim a + nim b`.

The nim sum `a + b` can alternatively be recursively defined as the least nimber not equal
to any `a' + b` or `a + b'` for `a' < a` and `b' < b`. However, this definition requires more setup,
as theorems like commutativity or associativity are nontrivial. The equivalence between both
definitions is a simple consequence of `Nimber.add_le_of_forall_ne` alongside cancellativity, so we
don't bother to state it verbatim.

The nim product and inverse are defined in the `CombinatorialGames.Nimber.Field` file.

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

open IGame

noncomputable section

/-! ### Grundy value of sum -/

/-- Nimber addition `a + b` is defined as the Grundy value of `nim a + nim b`. -/
instance : Add Nimber where
  add a b := Impartial.grundy (nim a + nim b)

namespace IGame.Impartial

theorem grundy_nim_add_nim (a b : Nimber) : grundy (nim a + nim b) = a + b :=
  rfl

@[simp]
theorem grundy_add (x y : IGame) [Impartial x] [Impartial y] :
    grundy (x + y) = grundy x + grundy y := by
  rw [← grundy_nim_add_nim]
  apply grundy_congr (add_congr ..) <;> exact (nim_grundy_equiv _).symm

@[simp]
theorem grundy_sub (x y : IGame) [Impartial x] [Impartial y] :
    grundy (x - y) = grundy x + grundy y :=
  (grundy_congr (sub_equiv x y)).trans (grundy_add x y)

end IGame.Impartial

theorem IGame.nim_add_equiv (a b : Nimber) : nim (a + b) ≈ nim a + nim b := by
  rw [← Impartial.grundy_eq_iff_equiv, Impartial.grundy_nim, Impartial.grundy_nim_add_nim]

@[simp]
theorem Game.mk_nim_add (a b : Nimber) : mk (nim (a + b)) = mk (nim a) + mk (nim b) :=
  Game.mk_eq (IGame.nim_add_equiv a b)

/-! ### Nimber addition -/

namespace Nimber

variable {a b c : Nimber.{u}}

theorem exists_of_lt_add (h : c < a + b) : (∃ a' < a, a' + b = c) ∨ ∃ b' < b, a + b' = c := by
  have := mem_grundyAux_image_of_lt h
  aesop

theorem add_le_of_forall_ne (h₁ : ∀ a' < a, a' + b ≠ c) (h₂ : ∀ b' < b, a + b' ≠ c) :
    a + b ≤ c := by
  by_contra! h
  have := exists_of_lt_add h
  tauto

protected theorem add_comm (a b : Nimber) : a + b = b + a := by
  simp_rw [← Impartial.grundy_nim_add_nim, add_comm]

theorem add_eq_zero {a b : Nimber} : a + b = 0 ↔ a = b := by
  rw [← Impartial.grundy_nim_add_nim, Impartial.grundy_eq_zero_iff,
    ← Impartial.equiv_iff_add_equiv_zero, nim_equiv_iff]

theorem add_ne_zero_iff : a + b ≠ 0 ↔ a ≠ b :=
  add_eq_zero.not

@[simp]
theorem add_self (a : Nimber) : a + a = 0 :=
  add_eq_zero.2 rfl

protected theorem add_assoc (a b c : Nimber) : a + b + c = a + (b + c) := by
  simp_rw [← Impartial.grundy_nim_add_nim, Impartial.grundy_eq_iff_equiv,
    Impartial.grundy_nim_add_nim, ← Game.mk_eq_mk]
  simp [add_assoc]

protected theorem add_zero (a : Nimber) : a + 0 = a := by
  simp [← Impartial.grundy_nim_add_nim]

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

theorem natCast_eq_if (n : ℕ) : (n : Nimber) = if Even n then 0 else 1 := by
  induction n <;> aesop

@[game_cmp]
theorem natCast_eq_mod (n : ℕ) : (n : Nimber) = (n % 2 : ℕ) := by
  simp [natCast_eq_if, Nat.even_iff]

@[simp, game_cmp]
theorem ofNat_eq_mod (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : Nimber) = (n % 2 : ℕ) :=
  natCast_eq_mod n

-- This lets `game_cmp` reduce any instances of `NatCast`.
attribute [game_cmp] Nat.reduceMod

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
      simpa [Nat.xor_comm, Nat.xor_cancel_left, ← hc'] using add_nat (c ^^^ b) b
    · apply h.ne
      simpa [Nat.xor_comm, Nat.xor_cancel_left, ← hc'] using add_nat a (c ^^^ a)

end Nimber

namespace IGame.Impartial

@[simp]
theorem grundyAux_add (p : Player) (x y : IGame) :
    (x + y).grundyAux p = x.grundyAux p + y.grundyAux p := by
  apply le_antisymm
  · apply grundyAux_le_of_notMem
    rw [moves_add]
    rintro ⟨_, (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩), ha'⟩
    · rw [grundyAux_add, add_left_inj] at ha'
      exact grundyAux_ne ha ha'
    · rw [grundyAux_add, add_right_inj] at ha'
      exact grundyAux_ne ha ha'
  · rw [le_grundyAux_iff]
    intro a ha
    obtain ha | ha := Nimber.lt_add_cases ha
    · obtain ⟨z, hz, hz'⟩  := mem_grundyAux_image_of_lt ha
      refine ⟨_, add_right_mem_moves_add hz y, ?_⟩
      rw [grundyAux_add, hz', Nimber.add_cancel_right]
    · obtain ⟨z, hz, hz'⟩  := mem_grundyAux_image_of_lt ha
      refine ⟨_, add_left_mem_moves_add hz x, ?_⟩
      rw [grundyAux_add, hz', add_comm, Nimber.add_cancel_right]
termination_by (x, y)
decreasing_by igame_wf

@[simp]
theorem grundyAux_sub (p : Player) (x y : IGame) :
    (x - y).grundyAux p = x.grundyAux p + y.grundyAux (-p) := by
  rw [sub_eq_add_neg, grundyAux_add, grundyAux_neg]

end IGame.Impartial
