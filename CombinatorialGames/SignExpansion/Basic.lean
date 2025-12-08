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

/-- Cut off the part of a sign expansion after an ordinal `o`, by filling it in with zeros. -/
def restrict (x : SignExpansion) (o : WithTop NatOrdinal) : SignExpansion where
  sign i := if i < o then x i else 0
  isUpperSet_preimage_singleton_zero' a b hab ha := by
    rw [← WithTop.coe_le_coe] at hab
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ite_eq_right_iff, apply_eq_zero] at ha ⊢
    exact fun hb ↦ (ha (hab.trans_lt hb)).trans hab

@[aesop simp]
theorem coe_restrict (x : SignExpansion) (o : WithTop NatOrdinal) :
    ⇑(x.restrict o) = fun i : NatOrdinal ↦ if i < o then x i else 0 :=
  rfl

theorem restrict_apply_of_coe_lt {x : SignExpansion} {o₁ : WithTop NatOrdinal}
    {o₂ : NatOrdinal} (h : o₂ < o₁) : x.restrict o₁ o₂ = x o₂ := if_pos h

theorem restrict_apply_of_le_coe {x : SignExpansion} {o₁ : WithTop NatOrdinal}
    {o₂ : NatOrdinal} (h : o₁ ≤ o₂) : x.restrict o₁ o₂ = 0 := if_neg h.not_gt

@[simp]
theorem length_restrict (x : SignExpansion) (o : WithTop NatOrdinal) :
    (x.restrict o).length = min x.length o := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  cases c <;> simp [← apply_eq_zero, restrict, imp_iff_or_not]

@[simp]
theorem restrict_of_length_le {x : SignExpansion} {o : WithTop NatOrdinal}
    (ho : x.length ≤ o) : x.restrict o = x := by
  ext o'
  obtain ho' | ho' := lt_or_ge (↑o') x.length
  · rw [restrict_apply_of_coe_lt (ho'.trans_le ho)]
  · rw [apply_of_length_le ho']
    apply apply_of_length_le
    simp [ho']

@[simp, grind =]
theorem restrict_restrict_eq {x : SignExpansion} {o₁ o₂ : WithTop NatOrdinal} :
    (x.restrict o₁).restrict o₂ = x.restrict (min o₁ o₂) := by
  aesop

@[simp]
theorem restrict_zero_left (o : WithTop NatOrdinal) : restrict 0 o = 0 := by
  ext; simp [apply_eq_zero]

@[simp]
theorem restrict_zero_right (x : SignExpansion) : x.restrict 0 = 0 := by
  ext; simp [apply_eq_zero]

@[simp]
theorem restrict_top_right {x : SignExpansion} : x.restrict ⊤ = x :=
  rfl

/-! ### Subset relation -/

/-- We write `x ⊆ y` when `x = restrict y o` for some `o`. In the literature, this is written as
`x ≤ₛ y` or `x ⊑ y`. -/
instance : HasSubset SignExpansion where
  Subset x y := restrict y x.length = x

/-- We write `x ⊂ y` when `x ⊆ y` and `x ≠ y`. In the literature, this is written as
`x <ₛ y` or `x ⊏ y`. -/
instance : HasSSubset SignExpansion where
  SSubset x y := x ⊆ y ∧ ¬ y ⊆ x

theorem subset_def {x y : SignExpansion} : x ⊆ y ↔ restrict y x.length = x := .rfl
theorem ssubset_def {x y : SignExpansion} : x ⊂ y ↔ x ⊆ y ∧ ¬ y ⊆ x := .rfl

alias ⟨eq_of_subset, _⟩ := subset_def

@[simp]
theorem restrict_subset (x : SignExpansion) (o : WithTop NatOrdinal) : restrict x o ⊆ x := by
  rw [subset_def, length_restrict, ← restrict_restrict_eq, restrict_of_length_le le_rfl]

@[simp]
theorem zero_subset (x : SignExpansion) : 0 ⊆ x := by
  rw [← restrict_zero_right x]
  exact restrict_subset ..

theorem eq_or_length_lt_of_subset {x y : SignExpansion} (h : x ⊆ y) :
    x = y ∨ x.length < y.length := by
  rw [subset_def] at h
  have := lt_or_ge x.length y.length
  aesop

instance : IsRefl SignExpansion (· ⊆ ·) where
  refl x := restrict_subset x ⊤

instance : IsTrans SignExpansion (· ⊆ ·) where
  trans := by grind [subset_def]

instance : IsAntisymm SignExpansion (· ⊆ ·) where
  antisymm x y h₁ h₂ := by
    have := eq_or_length_lt_of_subset h₁
    have := eq_or_length_lt_of_subset h₂
    grind

instance : IsNonstrictStrictOrder SignExpansion (· ⊆ ·) (· ⊂ ·) where
  right_iff_left_not_left _ _ := .rfl

@[gcongr]
theorem length_le_of_subset {x y : SignExpansion} (h : x ⊆ y) : x.length ≤ y.length := by
  rw [← eq_of_subset h]
  simp

@[gcongr]
theorem length_lt_of_ssubset {x y : SignExpansion} (h : x ⊂ y) : x.length < y.length := by
  have := eq_or_length_lt_of_subset (subset_of_ssubset h)
  have := ssubset_irrefl x
  aesop

/-! ### Order structure -/

instance : LinearOrder SignExpansion :=
  LinearOrder.lift' (toLex ⇑·) (by simp [Function.Injective])

theorem le_iff_toLex {x y : SignExpansion} : x ≤ y ↔ toLex ⇑x ≤ toLex ⇑y := .rfl
theorem lt_iff_toLex {x y : SignExpansion} : x < y ↔ toLex ⇑x < toLex ⇑y := .rfl

instance : BoundedOrder SignExpansion where
  le_top _ := le_iff_toLex.2 le_top
  bot_le _ := le_iff_toLex.2 bot_le

end SignExpansion

/-! ### Cast from ordinals -/

namespace NatOrdinal
open SignExpansion

variable {o₁ o₂ : NatOrdinal}

/-- Returns the sign expansion with the corresponding number of `1`s. -/
def toSignExpansion : NatOrdinal ↪o SignExpansion :=
  .ofStrictMono (restrict ⊤ ·) fun x y h ↦ by
    use x
    aesop (add apply unsafe [lt_trans])

instance : Coe NatOrdinal SignExpansion where
  coe x := x.toSignExpansion

theorem toSignExpansion_def (o : NatOrdinal) : o = restrict ⊤ o := rfl

@[aesop simp]
theorem coe_toSignExpansion (o : NatOrdinal) :
    ⇑(o : SignExpansion) = fun i : NatOrdinal ↦ if i < o then 1 else 0 := by
  unfold toSignExpansion
  aesop

@[simp]
theorem length_toSignExpansion (o : NatOrdinal) : length o = o := by
  simp [toSignExpansion]

theorem toSignExpansion_apply_of_lt (h : o₂ < o₁) : toSignExpansion o₁ o₂ = 1 := by
  aesop

theorem toSignExpansion_apply_of_le (h : o₁ ≤ o₂) : toSignExpansion o₁ o₂ = 0 := by
  aesop

theorem toSignExpansion_subset_toSignExpansion_of_le (h : o₁ ≤ o₂) :
    (o₁ : SignExpansion) ⊆ o₂ := by
  rw [subset_def]
  aesop (add unsafe apply lt_of_lt_of_le)

theorem toSignExpansion_ssubset_toSignExpansion_of_lt (h : o₁ < o₂) :
    (o₁ : SignExpansion) ⊂ o₂ := by
  rw [ssubset_iff_subset_ne]
  use toSignExpansion_subset_toSignExpansion_of_le h.le
  aesop

@[simp]
theorem toSignExpansion_subset_toSignExpansion_iff : (o₁ : SignExpansion) ⊆ o₂ ↔ o₁ ≤ o₂ := by
  refine ⟨?_, toSignExpansion_subset_toSignExpansion_of_le⟩
  contrapose!
  exact fun h ↦ (toSignExpansion_ssubset_toSignExpansion_of_lt h).2

@[simp]
theorem toSignExpansion_ssubset_toSignExpansion_iff : (o₁ : SignExpansion) ⊂ o₂ ↔ o₁ < o₂ := by
  refine ⟨?_, toSignExpansion_ssubset_toSignExpansion_of_lt⟩
  contrapose!
  exact fun h ↦ not_ssubset_of_subset (toSignExpansion_subset_toSignExpansion_of_le h)

end NatOrdinal
