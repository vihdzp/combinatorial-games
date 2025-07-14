/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.NatOrdinal
import Mathlib.Data.Sign
import Mathlib.Order.PiLex

/-!
# Sign Expansions

We define the type of sign expansions.
-/

universe u

noncomputable section

structure SignExpansion : Type (u + 1) where
  sign : NatOrdinal.{u} → SignType
  isUpperSet_sign_preimage_singleton_zero : IsUpperSet (sign ⁻¹' {0})

namespace SignExpansion
open Order

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

noncomputable def size (e : SignExpansion.{u}) : WithTop NatOrdinal.{u} :=
  ⨅ (i : NatOrdinal.{u}) (_ : e i = 0), WithTop.some i

theorem apply_of_size_le {e : SignExpansion.{u}} {o : NatOrdinal.{u}} (h : e.size ≤ o) :
    e o = 0 := by
  cases he : e.size with
  | top => simp [he] at h
  | coe g =>
    rw [he, WithTop.coe_le_coe, ← lt_succ_iff,
      ← WithTop.coe_lt_coe, ← he, size] at h
    simp_rw [iInf_lt_iff, WithTop.coe_lt_coe, lt_succ_iff] at h
    obtain ⟨i, hi, hio⟩ := h
    exact e.isUpperSet_sign_preimage_singleton_zero hio hi

@[simp]
theorem apply_eq_zero {x : SignExpansion.{u}} {o : NatOrdinal.{u}} :
    x o = 0 ↔ x.size ≤ o :=
  ⟨fun h => iInf₂_le o h, apply_of_size_le⟩

def restrict (x : SignExpansion.{u}) (o : WithTop NatOrdinal.{u}) : SignExpansion.{u} where
  sign i := if i < o then x.sign i else 0
  isUpperSet_sign_preimage_singleton_zero := by
    intro a b hab ha
    rw [← WithTop.coe_le_coe] at hab
    simp only [sign_eq_coe, Set.mem_preimage, Set.mem_singleton_iff, ite_eq_right_iff,
      apply_eq_zero] at ha ⊢
    exact fun hb => (ha (hab.trans_lt hb)).trans hab

@[simp]
theorem size_restrict (x : SignExpansion.{u}) (o : WithTop NatOrdinal.{u}) :
    (x.restrict o).size = min x.size o := by
  apply eq_of_forall_ge_iff
  intro c
  cases c with
  | top => simp
  | coe c =>
    rw [← apply_eq_zero, restrict]
    simp [imp_iff_or_not]

theorem restrict_apply_of_lt {x : SignExpansion.{u}} {o₁ o₂ : NatOrdinal.{u}}
    (h : o₂ < o₁) : x.restrict o₁ o₂ = x o₂ := by
  simp [restrict, h]

theorem restrict_apply_of_le {x : SignExpansion.{u}} {o₁ o₂ : NatOrdinal.{u}}
    (h : o₁ ≤ o₂) : x.restrict o₁ o₂ = 0 := by
  simp [restrict, h]

instance : LinearOrder SignExpansion.{u} :=
  LinearOrder.lift' (toLex ⇑·) (by simp [Function.Injective])

theorem le_iff_toLex_le {a b : SignExpansion.{u}} : a ≤ b ↔ toLex ⇑a ≤ toLex ⇑b := Iff.rfl
theorem lt_iff_toLex_lt {a b : SignExpansion.{u}} : a < b ↔ toLex ⇑a < toLex ⇑b := Iff.rfl

end SignExpansion
