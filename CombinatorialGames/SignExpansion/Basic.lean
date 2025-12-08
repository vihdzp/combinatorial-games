/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Violeta Hernández Palacios
-/
import CombinatorialGames.NatOrdinal.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Sign.Defs
import Mathlib.Order.PiLex

/-!
# Sign expansions

In this repository we define the type of `Surreal` numbers following Conway's theory of games. A
popular alternative is to instead define the surreals as potentially infinite "expansions of signs",
setting for instance `+ = 1`, `- = -1`, `+- = ½`, etc.

This file defines the type `SignExpansion` and constructs its basic instances. We do not yet link it
to the development of surreal numbers.
-/

universe u

noncomputable section

-- #32571
@[simp] theorem SignType.neg_le_neg_iff {x y : SignType} : -x ≤ -y ↔ y ≤ x := by decide +revert
@[simp] theorem SignType.neg_lt_neg_iff {x y : SignType} : -x < -y ↔ y < x := by decide +revert

/-- A sign expansion is a an ordinal indexed sequence of `1`s and `-1`s, followed by `0`s. -/
structure SignExpansion : Type (u + 1) where
  /-- The sequence defining the sign expansion. -/
  sign : NatOrdinal.{u} → SignType
  /-- Every sign after the first `0` is also `0`.

  Do not use directly, use `isUpperSet_preimage_singleton_zero` instead. -/
  isUpperSet_preimage_singleton_zero' : IsUpperSet (sign ⁻¹' {0})

namespace SignExpansion
open Order

instance : FunLike SignExpansion NatOrdinal SignType where
  coe := sign
  coe_injective' a b hab := by cases a; cases b; cases hab; rfl

/-- Every sign after the first `0` is also `0`. -/
theorem isUpperSet_preimage_singleton_zero (x : SignExpansion) : IsUpperSet (x ⁻¹' {0}) := x.2

@[simp] theorem coe_mk (f h) : SignExpansion.mk f h = f := rfl
@[simp] theorem sign_eq_coe (x : SignExpansion) : x.sign = ⇑x := rfl

@[ext]
protected theorem ext {x y : SignExpansion} (hxy : ∀ o, x o = y o) : x = y :=
  DFunLike.coe_injective (funext hxy)

theorem apply_eq_zero_of_le {x : SignExpansion} {o o' : Ordinal}
    (hoo' : o ≤ o') (ho : x o = 0) : x o' = 0 :=
  isUpperSet_preimage_singleton_zero x hoo' ho

/-- The length of a sign expansion is the smallest ordinal at which it equals zero,
or `⊤` is no such ordinal exists. -/
def length (x : SignExpansion) : WithTop NatOrdinal :=
  sInf ((↑) '' (x ⁻¹' {0}))

theorem apply_of_length_le {x : SignExpansion} {o : NatOrdinal} (h : x.length ≤ o) : x o = 0 := by
  obtain he | he := (WithTop.some '' (x ⁻¹' {0})).eq_empty_or_nonempty
  · simp_all [length]
  · obtain ⟨a, ha, ha'⟩ := csInf_mem he
    apply apply_eq_zero_of_le _ ha
    rwa [← WithTop.coe_le_coe, ha']

theorem apply_eq_zero {x : SignExpansion} {o : NatOrdinal} : x o = 0 ↔ x.length ≤ o := by
  refine ⟨fun h ↦ csInf_le' ?_, apply_of_length_le⟩
  simpa

theorem length_eq_top {x : SignExpansion} : x.length = ⊤ ↔ ∀ o, x o ≠ 0 := by
  simpa [apply_eq_zero] using WithTop.eq_top_iff_forall_gt

/-! ### Basic sign expansions -/

private def const (s : SignType) : SignExpansion where
  sign _ := s
  isUpperSet_preimage_singleton_zero' := by aesop

instance : Zero SignExpansion where
  zero := const 0

@[simp] theorem coe_zero : ⇑(0 : SignExpansion) = 0 := rfl
theorem zero_apply (o : NatOrdinal) : (0 : SignExpansion) o = 0 := rfl

@[simp]
theorem length_zero : length 0 = 0 := by
  apply csInf_eq_bot_of_bot_mem; simp

instance : Bot SignExpansion where
  bot := const (-1)

@[simp] theorem coe_bot : ⇑(⊥ : SignExpansion) = -1 := rfl
theorem bot_apply (o : NatOrdinal) : (⊥ : SignExpansion) o = -1 := rfl

@[simp]
theorem length_bot : length ⊥ = ⊤ := by
  simp [length]

instance : Top SignExpansion where
  top := const 1

@[simp] theorem coe_top : ⇑(⊤ : SignExpansion) = 1 := rfl
theorem top_apply (o : NatOrdinal) : (⊤ : SignExpansion) o = 1 := rfl

@[simp]
theorem length_top : length ⊤ = ⊤ := by
  simp [length]

instance : Neg SignExpansion where
  neg e :=
  { sign := -e
    isUpperSet_preimage_singleton_zero' a b hab ha := by
      simp only [Set.mem_preimage, Pi.neg_apply, Set.mem_singleton_iff,
        SignType.neg_eq_zero_iff, apply_eq_zero] at ha ⊢
      exact ha.trans (WithTop.coe_le_coe.2 hab) }

@[simp] theorem coe_neg (x : SignExpansion) : ⇑(-x : SignExpansion) = -⇑x := rfl
theorem neg_apply (x : SignExpansion) (o : NatOrdinal) : (-x) o = -x o := rfl

@[simp] theorem neg_zero : -(0 : SignExpansion) = 0 := rfl
@[simp] theorem neg_bot : -(⊥ : SignExpansion) = ⊤ := rfl
@[simp] theorem neg_top : -(⊤ : SignExpansion) = ⊥ := rfl

instance : InvolutiveNeg SignExpansion where
  neg_neg x := by ext; simp

/-- Cut off the part of a sign expansion after an ordinal `o`, by filling it in with zeros. -/
def restrict (x : SignExpansion) (o : WithTop NatOrdinal) : SignExpansion where
  sign i := if i < o then x i else 0
  isUpperSet_preimage_singleton_zero' a b hab ha := by
    rw [← WithTop.coe_le_coe] at hab
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ite_eq_right_iff, apply_eq_zero] at ha ⊢
    exact fun hb ↦ (ha (hab.trans_lt hb)).trans hab

@[inherit_doc] scoped notation x:70 " ↾ " o:70 => restrict x o
recommended_spelling "restrict" for "↾" in [«term_↾_»]

@[aesop simp]
theorem coe_restrict (x : SignExpansion) (o : WithTop NatOrdinal) :
    ⇑(x ↾ o) = fun i : NatOrdinal ↦ if i < o then x i else 0 :=
  rfl

theorem restrict_apply_of_coe_lt {x : SignExpansion} {o₁ : WithTop NatOrdinal}
    {o₂ : NatOrdinal} (h : o₂ < o₁) : (x ↾ o₁) o₂ = x o₂ := if_pos h

theorem restrict_apply_of_le_coe {x : SignExpansion} {o₁ : WithTop NatOrdinal}
    {o₂ : NatOrdinal} (h : o₁ ≤ o₂) : (x ↾ o₁) o₂ = 0 := if_neg h.not_gt

@[simp]
theorem length_restrict (x : SignExpansion) (o : WithTop NatOrdinal) :
    (x.restrict o).length = min x.length o := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  cases c <;> simp [← apply_eq_zero, restrict, imp_iff_or_not]

theorem restrict_of_length_le {x : SignExpansion} {o : WithTop NatOrdinal}
    (ho : x.length ≤ o) : x ↾ o = x := by
  ext o'
  obtain ho' | ho' := lt_or_ge (↑o') x.length
  · rw [restrict_apply_of_coe_lt (ho'.trans_le ho)]
  · rw [apply_of_length_le ho']
    apply apply_of_length_le
    simp [ho']

@[simp]
theorem restrict_zero_left (o : NatOrdinal) : 0 ↾ o = 0 := by
  ext; simp [apply_eq_zero]

@[simp]
theorem restrict_zero_right (x : SignExpansion) : x ↾ 0 = 0 := by
  ext; simp [apply_eq_zero]

@[simp]
theorem restrict_top_right {x : SignExpansion} : x ↾ ⊤ = x := by
  apply restrict_of_length_le; simp

/-! ### Order structure -/

instance : LinearOrder SignExpansion :=
  LinearOrder.lift' (toLex ⇑·) (by simp [Function.Injective])

theorem le_iff_toLex {x y : SignExpansion} : x ≤ y ↔ toLex ⇑x ≤ toLex ⇑y := .rfl
theorem lt_iff_toLex {x y : SignExpansion} : x < y ↔ toLex ⇑x < toLex ⇑y := .rfl

instance : BoundedOrder SignExpansion where
  le_top _ := le_iff_toLex.2 le_top
  bot_le _ := le_iff_toLex.2 bot_le

protected theorem neg_lt_neg {x y : SignExpansion} (h : x < y) : -y < -x := by
  obtain ⟨i, hi⟩ := h
  use i
  simp_all

@[simp]
protected theorem neg_lt_neg_iff {x y : SignExpansion} : -x < -y ↔ y < x where
  mp := by simpa using SignExpansion.neg_lt_neg (x := -x) (y := -y)
  mpr := SignExpansion.neg_lt_neg

@[simp]
protected theorem neg_le_neg_iff {x y : SignExpansion} : -x ≤ -y ↔ y ≤ x :=
  le_iff_le_iff_lt_iff_lt.2 SignExpansion.neg_lt_neg_iff

protected alias ⟨_, neg_le_neg⟩ := SignType.neg_le_neg_iff

end SignExpansion
