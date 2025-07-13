/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.NatOrdinal
import Mathlib.Data.Sign

/-!
# Sign Expansions

We define the type of sign expansions.
-/

universe u

noncomputable section

structure SignExpansion : Type (u + 1) where
  size : NatOrdinal.{u}
  sign : Set.Iio size → ℤˣ

namespace SignExpansion

instance : FunLike SignExpansion.{u} NatOrdinal.{u} SignType where
  coe e o := if h : o < e.size then .sign (e.sign ⟨o, h⟩ : ℤ) else 0
  coe_injective' a b hab := by
    let p (i : SignExpansion.{u}) (o : NatOrdinal.{u}) : SignType :=
      (if h : o < i.size then .sign (i.sign ⟨o, h⟩ : ℤ) else 0)
    change p a = p b at hab
    have hi (i : SignExpansion.{u}) :
      ⨅ (o : Subtype (p i · = 0)), o.1 = i.size := by
      have hi : (p i · = 0) = (· ∈ Set.Ici i.size) := by simp [p]
      rw [hi]
      apply le_antisymm
      · exact ciInf_le ⟨⊥, bot_mem_lowerBounds _⟩ (Subtype.mk i.size le_rfl)
      · apply le_ciInf
        exact Subtype.prop
    have h : a.size = b.size := calc
      _ = _ := (hi a).symm
      _ = _ := by rw [hab]
      _ = _ := hi b
    cases a with | mk s ua
    cases b with | mk s ub
    cases h
    rw [SignExpansion.mk.injEq, eq_self, true_and, heq_iff_eq]
    ext ⟨i, ci⟩
    -- #check congr($hab i)
    have uu := congrFun hab i
    simp_rw [p, dif_pos (Set.mem_Iio.mp ci)] at uu
    have cx : ∀ {x y : ℤˣ} (h : SignType.sign (x : ℤ) = SignType.sign (y : ℤ)), x = y := by
      decide
    rw [cx uu]

@[ext]
protected theorem ext {x y : SignExpansion.{u}} (hxy : ∀ o, x o = y o) : x = y :=
  DFunLike.coe_injective (funext hxy)

theorem apply_def (e : SignExpansion.{u}) (o : NatOrdinal.{u}) :
    e o = if h : o < e.size then .sign (e.sign ⟨o, h⟩ : ℤ) else 0 := rfl

theorem apply_of_size_le {x : SignExpansion.{u}} {o : NatOrdinal.{u}} (h : x.size ≤ o) :
    x o = 0 :=
  dif_neg (not_lt_of_ge h)

@[simp]
theorem apply_eq_zero {x : SignExpansion.{u}} {o : NatOrdinal.{u}} :
    x o = 0 ↔ x.size ≤ o := by
  refine ⟨fun h => ?_, apply_of_size_le⟩
  rw [apply_def] at h
  split_ifs at h with ho
  · absurd h
    generalize x.sign ⟨o, ho⟩ = u
    decide +revert
  · exact le_of_not_gt ho

def restrict (x : SignExpansion.{u}) (o : NatOrdinal.{u}) : SignExpansion.{u} where
  size := min x.size o
  sign i := x.sign ⟨i, i.prop.trans_le (min_le_left x.size o)⟩

@[simp]
theorem size_restrict (x : SignExpansion.{u}) (o : NatOrdinal.{u}) :
    (x.restrict o).size = min x.size o := rfl

theorem restrict_apply_of_lt {x : SignExpansion.{u}} {o₁ o₂ : NatOrdinal.{u}}
    (h : o₂ < o₁) : x.restrict o₁ o₂ = x o₂ := by
  simp [apply_def, h, restrict]

theorem restrict_apply_of_le {x : SignExpansion.{u}} {o₁ o₂ : NatOrdinal.{u}}
    (h : o₁ ≤ o₂) : x.restrict o₁ o₂ = 0 := by
  apply apply_of_size_le
  simp [h]

instance : LinearOrder SignExpansion.{u} :=
  LinearOrder.lift' (toLex ⇑·) (by simp [Function.Injective])

theorem le_iff_toLex_le {a b : SignExpansion.{u}} : a ≤ b ↔ toLex ⇑a ≤ toLex ⇑b := Iff.rfl
theorem lt_iff_toLex_lt {a b : SignExpansion.{u}} : a < b ↔ toLex ⇑a < toLex ⇑b := Iff.rfl

end SignExpansion
