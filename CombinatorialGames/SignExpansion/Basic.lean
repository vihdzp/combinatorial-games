/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.NatOrdinal
import Mathlib.Data.Fintype.Order
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Data.Sign
import Mathlib.Order.PiLex

/-!
# Sign Expansions

We define the type of sign expansions and show some basic properties.
-/

namespace SignType
noncomputable instance : CompleteLinearOrder SignType := Fintype.toCompleteLinearOrder SignType
instance : SuccOrder SignType where
  succ
  | -1 => 0
  | 0 => 1
  | 1 => 1
  le_succ := by decide
  max_of_succ_le := by unfold IsMax; decide
  succ_le_of_lt := by decide
instance : PredOrder SignType where
  pred
  | -1 => -1
  | 0 => -1
  | 1 => 0
  pred_le := by decide
  min_of_le_pred := by unfold IsMin; decide
  le_pred_of_lt := by decide

@[simp] theorem succ_neg_one : Order.succ (-1 : SignType) = 0 := rfl
@[simp] theorem succ_zero : Order.succ (0 : SignType) = 1 := rfl
@[simp] theorem succ_one : Order.succ (1 : SignType) = 1 := rfl
@[simp] theorem pred_neg_one : Order.pred (-1 : SignType) = -1 := rfl
@[simp] theorem pred_zero : Order.pred (0 : SignType) = -1 := rfl
@[simp] theorem pred_one : Order.pred (1 : SignType) = 0 := rfl

@[simp] theorem neg_eq_zero : ∀ a : SignType, -a = 0 ↔ a = 0 := by decide
end SignType

theorem OrderIso.isSuccPreimit_apply {α β : Type*} [Preorder α] [Preorder β] {e : α ≃o β} {a : α} :
    Order.IsSuccPrelimit (e a) ↔ Order.IsSuccPrelimit a := by
  rw [Order.IsSuccPrelimit, ← e.forall_congr_right, Order.IsSuccPrelimit]
  simp

theorem OrderIso.isSuccLimit_apply {α β : Type*} [Preorder α] [Preorder β] {e : α ≃o β} {a : α} :
    Order.IsSuccLimit (e a) ↔ Order.IsSuccLimit a := by
  rw [Order.IsSuccLimit, e.isMin_apply, e.isSuccPreimit_apply, Order.IsSuccLimit]

universe u

noncomputable section

/--
A sign expansion is a an ordinal indexed sequence of `1`s and `-1`s, followed by `0`s.
-/
structure SignExpansion : Type (u + 1) where
  /--
  The sequence defining the sign expansion
  -/
  sign : NatOrdinal.{u} → SignType
  isUpperSet_sign_preimage_singleton_zero : IsUpperSet (sign ⁻¹' {0})

namespace SignExpansion
open Order Set

instance : FunLike SignExpansion.{u} NatOrdinal.{u} SignType where
  coe := sign
  coe_injective' a b hab := by
    cases a; cases b; cases hab; rfl

@[ext]
protected theorem ext {x y : SignExpansion.{u}} (hxy : ∀ o, x o = y o) : x = y :=
  DFunLike.coe_injective (funext hxy)

@[simp]
theorem coe_mk (sign : NatOrdinal.{u} → SignType)
    (isUpperSet_sign_preimage_singleton_zero : IsUpperSet (sign ⁻¹' {0})) :
    ⇑{sign, isUpperSet_sign_preimage_singleton_zero : SignExpansion.{u}} = sign := rfl

@[simp]
theorem sign_eq_coe (e : SignExpansion.{u}) : e.sign = ⇑e := rfl

theorem apply_eq_zero_of_le {e : SignExpansion} {o o' : Ordinal.{u}}
    (hoo' : o ≤ o') (ho : e o = 0) : e o' = 0 := e.isUpperSet_sign_preimage_singleton_zero hoo' ho

/-- The length of a sign expansion is the smallest ordinal at which it equals zero,
or `⊤` is no such ordinal exists. -/
noncomputable def length (e : SignExpansion.{u}) : WithTop NatOrdinal.{u} :=
  ⨅ (i : NatOrdinal.{u}) (_ : e i = 0), WithTop.some i

theorem apply_of_length_le {e : SignExpansion.{u}} {o : NatOrdinal.{u}} (h : e.length ≤ o) :
    e o = 0 := by
  cases he : e.length with
  | top => simp [he] at h
  | coe g =>
    rw [he, WithTop.coe_le_coe, ← lt_succ_iff,
      ← WithTop.coe_lt_coe, ← he, length] at h
    simp_rw [iInf_lt_iff, WithTop.coe_lt_coe, lt_succ_iff] at h
    obtain ⟨i, hi, hio⟩ := h
    exact e.apply_eq_zero_of_le hio hi

theorem apply_eq_zero {x : SignExpansion.{u}} {o : NatOrdinal.{u}} :
    x o = 0 ↔ x.length ≤ o :=
  ⟨fun h => iInf₂_le o h, apply_of_length_le⟩

theorem length_eq_top {x : SignExpansion.{u}} : x.length = ⊤ ↔ ∀ o, x o ≠ 0 := by
  simpa [apply_eq_zero] using WithTop.eq_top_iff_forall_gt

/--
Cut off the part of a sign expansion after an ordinal `o`, by filling it in with `0`.
-/
def restrict (x : SignExpansion.{u}) (o : WithTop NatOrdinal.{u}) : SignExpansion.{u} where
  sign i := if i < o then x.sign i else 0
  isUpperSet_sign_preimage_singleton_zero := by
    intro a b hab ha
    rw [← WithTop.coe_le_coe] at hab
    simp only [sign_eq_coe, Set.mem_preimage, Set.mem_singleton_iff, ite_eq_right_iff,
      apply_eq_zero] at ha ⊢
    exact fun hb => (ha (hab.trans_lt hb)).trans hab

@[simp]
theorem length_restrict (x : SignExpansion.{u}) (o : WithTop NatOrdinal.{u}) :
    (x.restrict o).length = min x.length o := by
  apply eq_of_forall_ge_iff
  intro c
  cases c with
  | top => simp
  | coe c =>
    rw [← apply_eq_zero, restrict]
    simp [imp_iff_or_not, apply_eq_zero]

theorem restrict_apply_of_coe_lt {x : SignExpansion.{u}} {o₁ : WithTop NatOrdinal.{u}}
    {o₂ : NatOrdinal.{u}} (h : o₂ < o₁) : x.restrict o₁ o₂ = x o₂ := by
  simp [restrict, h]

theorem restrict_apply_of_le_coe {x : SignExpansion.{u}} {o₁ : WithTop NatOrdinal.{u}}
    {o₂ : NatOrdinal.{u}} (h : o₁ ≤ o₂) : x.restrict o₁ o₂ = 0 := by
  simp [restrict, h]

@[simp]
theorem restrict_of_length_le {e : SignExpansion.{u}} {o : WithTop NatOrdinal.{u}}
    (ho : e.length ≤ o) : e.restrict o = e := by
  ext o'
  obtain ho' | ho' := lt_or_ge (.some o') e.length
  · rw [restrict_apply_of_coe_lt (ho'.trans_le ho)]
  · rw [apply_of_length_le ho']
    apply apply_of_length_le
    simp [ho']

theorem restrict_top_right {e : SignExpansion.{u}} : e.restrict ⊤ = e := by simp

instance : Zero SignExpansion.{u} where
  zero := {
    sign _ := 0
    isUpperSet_sign_preimage_singleton_zero := by simp [isUpperSet_univ]
  }

@[simp]
theorem zero_apply (o : NatOrdinal.{u}) : (0 : SignExpansion.{u}) o = 0 := rfl

theorem restrict_zero (e : SignExpansion.{u}) : e.restrict 0 = 0 := by
  ext; simp [apply_eq_zero]

@[simp]
theorem length_zero : length 0 = 0 := by
  rw [← restrict_zero 0, length_restrict, ← WithTop.coe_zero,
    ← NatOrdinal.bot_eq_zero, WithTop.coe_bot, min_bot_right]

instance linearOrder : LinearOrder SignExpansion.{u} :=
  LinearOrder.lift' (toLex ⇑·) (by simp [Function.Injective])

theorem le_iff_toLex {a b : SignExpansion.{u}} : a ≤ b ↔ toLex ⇑a ≤ toLex ⇑b := Iff.rfl
theorem lt_iff_toLex {a b : SignExpansion.{u}} : a < b ↔ toLex ⇑a < toLex ⇑b := Iff.rfl

instance : Bot SignExpansion.{u} where
  bot := {
    sign _ := -1
    isUpperSet_sign_preimage_singleton_zero := by simp [isUpperSet_empty]
  }

@[simp]
theorem bot_apply (o : NatOrdinal.{u}) : (⊥ : SignExpansion.{u}) o = -1 := rfl

instance : Top SignExpansion.{u} where
  top := {
    sign _ := 1
    isUpperSet_sign_preimage_singleton_zero := by simp [isUpperSet_empty]
  }

@[simp]
theorem top_apply (o : NatOrdinal.{u}) : (⊤ : SignExpansion.{u}) o = 1 := rfl

instance boundedOrder : BoundedOrder SignExpansion.{u} where
  le_top _ := le_iff_toLex.2 <| Pi.toLex_monotone (by simp [Pi.le_def])
  bot_le _ := le_iff_toLex.2 <| Pi.toLex_monotone (by simp [Pi.le_def])

instance biheytingAlgebra : BiheytingAlgebra SignExpansion.{u} :=
  linearOrder.toBiheytingAlgebra

instance : Neg SignExpansion.{u} where
  neg e := {
    sign := -e
    isUpperSet_sign_preimage_singleton_zero a b hab ha := by
      simp only [mem_preimage, Pi.neg_apply, mem_singleton_iff, SignType.neg_eq_zero,
        apply_eq_zero] at ha ⊢
      exact ha.trans (WithTop.coe_le_coe.2 hab)
  }

@[simp]
theorem neg_apply (e : SignExpansion) (o : Ordinal) : (-e) o = -e o := rfl

end SignExpansion
