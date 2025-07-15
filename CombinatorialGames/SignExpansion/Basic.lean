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

We define the type of sign expansions.
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

structure SignExpansion : Type (u + 1) where
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
    exact e.apply_eq_zero_of_le hio hi

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
theorem coe_bot : ⇑(⊥ : SignExpansion.{u}) = ⊥ := rfl

theorem bot_apply (o : NatOrdinal.{u}) : (⊥ : SignExpansion.{u}) o = -1 := rfl

instance : Top SignExpansion.{u} where
  top := {
    sign _ := 1
    isUpperSet_sign_preimage_singleton_zero := by simp [isUpperSet_empty]
  }

@[simp]
theorem coe_top : ⇑(⊤ : SignExpansion.{u}) = ⊤ := rfl

theorem top_apply (o : NatOrdinal.{u}) : (⊤ : SignExpansion.{u}) o = 1 := rfl

instance : BoundedOrder SignExpansion.{u} where
  le_top _ := le_iff_toLex.2 <| Pi.toLex_monotone (by simp)
  bot_le _ := le_iff_toLex.2 <| Pi.toLex_monotone (by simp)

section CompleteLattice

private def sets (s : Set SignExpansion.{u}) (o : Ordinal.{u}) : Set SignExpansion.{u} :=
  Ordinal.limitRecOn o
    s -- zero
    (fun o ih => {x ∈ ih | x o.toNatOrdinal = ⨆ i ∈ ih, i o.toNatOrdinal}) -- succ
    (fun _ _ ih => ⋂ (i) (hi), ih i hi) -- limit

private theorem sets_zero (s : Set SignExpansion.{u}) : sets s 0 = s :=
  Ordinal.limitRecOn_zero ..

private theorem sets_succ (s : Set SignExpansion.{u}) (o : Ordinal.{u}) :
    sets s (succ o) = {x ∈ sets s o | x o.toNatOrdinal = ⨆ i ∈ sets s o, i o.toNatOrdinal} :=
  Ordinal.limitRecOn_succ ..

private theorem sets_limit (s : Set SignExpansion.{u}) {o : Ordinal.{u}}
    (ho : IsSuccLimit o) : sets s o = ⋂ (i : Ordinal.{u}) (_ : i < o), sets s i :=
  Ordinal.limitRecOn_limit _ _ _ _ ho

private theorem sets_anti_right (s : Set SignExpansion.{u}) {o o' : Ordinal.{u}}
    (hoo' : o ≤ o') : sets s o' ⊆ sets s o := by
  apply exists_add_of_le at hoo'
  obtain ⟨o', rfl⟩ := hoo'
  induction o' using Ordinal.limitRecOn with
  | zero => simp
  | succ o' ih =>
    apply ih.trans'
    rw [Ordinal.add_succ, sets_succ]
    simp
  | isLimit o' limit ih =>
    have limit' := limit
    apply Ordinal.isLimit_add o at limit'
    rw [sets_limit s limit']
    apply Set.iInter₂_subset
    simpa [← Ordinal.bot_eq_zero, bot_lt_iff_ne_bot] using limit.ne_bot

private theorem sets_singleton_inc (s : Set SignExpansion.{u}) (o o' : Ordinal.{u})
    (x : SignExpansion) (hoo' : o ≤ o') (h : sets s o = {x}) : sets s o' = {x} := by
  apply exists_add_of_le at hoo'
  obtain ⟨o', rfl⟩ := hoo'
  induction o' using Ordinal.limitRecOn with
  | zero => simpa using h
  | succ o' ih =>
    rw [Ordinal.add_succ]
    apply subset_antisymm
    · rw [← ih]
      apply sets_anti_right
      apply le_succ
    · rw [sets_succ, Set.singleton_subset_iff]
      simp [ih]
  | isLimit o' limit ih =>
    have limit' := limit
    apply Ordinal.isLimit_add o at limit'
    rw [sets_limit s limit']
    apply subset_antisymm
    · exact iInter₂_subset_of_subset (o + 0) (add_lt_add_left limit.pos o) (ih 0 limit.pos).subset
    · rw [Set.subset_iInter₂_iff]
      intro i hi
      obtain hoi | hio := le_total o i
      · apply exists_add_of_le at hoi
        obtain ⟨c, rfl⟩ := hoi
        rw [add_lt_add_iff_left] at hi
        exact (ih c hi).superset
      · apply (sets_anti_right s hio).trans'
        rw [← add_zero o]
        exact (ih 0 limit.pos).superset

private theorem sets_congr_of_lt (s : Set SignExpansion.{u}) (o o' : Ordinal.{u})
    (ho' : o' < o) (e : SignExpansion.{u}) (he : e ∈ sets s o) :
    e o'.toNatOrdinal = ⨆ i ∈ sets s o', i o'.toNatOrdinal := by
  induction o using Ordinal.limitRecOn generalizing o' e with
  | zero => simp [← not_le] at ho'
  | succ o ih =>
    rw [lt_succ_iff_eq_or_lt, or_comm] at ho'
    obtain h | rfl := ho'
    · exact ih o' h e (sets_anti_right s (le_succ o) he)
    rw [sets_succ] at he
    exact he.right
  | isLimit o limit ih =>
    rw [← Ordinal.succ_lt_of_isLimit limit] at ho'
    exact ih (succ o') ho' o' (lt_succ o') e (sets_anti_right s ho'.le he)

private theorem congr_sets_of_lt (s : Set SignExpansion.{u}) (o : Ordinal.{u})
    (e : SignExpansion.{u}) (he : e ∈ s)
    (ho' : ∀ o' < o, e o'.toNatOrdinal = ⨆ i ∈ sets s o', i o'.toNatOrdinal) : e ∈ sets s o := by
  induction o using Ordinal.limitRecOn generalizing e with
  | zero => rwa [sets_zero]
  | succ o ih =>
    rw [sets_succ]
    constructor
    · apply ih e he
      intro o' hoo'
      exact ho' o' (hoo'.trans_le (le_succ o))
    · exact ho' o (lt_succ o)
  | isLimit o limit ih =>
    rw [sets_limit s limit, Set.mem_iInter₂]
    intro o' hoo'
    apply ih o' hoo' e he
    intro o'' hoo''
    exact ho' o'' (hoo''.trans hoo')

private theorem sets_singleton_succ_of_zero (s : Set SignExpansion.{u}) (o : Ordinal.{u})
    (h : ⨆ i ∈ sets s o, i o.toNatOrdinal = 0) : ∃ k, sets s (succ o) = {k} := by
  have lubo : IsLUB ((· o.toNatOrdinal) '' sets s o) (⨆ i ∈ sets s o, i o.toNatOrdinal) :=
    isLUB_biSup
  have np0 : ¬IsSuccPrelimit (succ (-1) : SignType) :=
    not_isSuccPrelimit_succ_of_not_isMax (by simp)
  rw [SignType.succ_neg_one] at np0
  rw [h] at lubo
  have hm0 := lubo.mem_of_not_isSuccPrelimit np0
  rw [Set.mem_image] at hm0
  obtain ⟨x, hx, hxo⟩ := hm0
  refine ⟨x, subset_antisymm ?_ ?_⟩
  · intro y hy
    rw [Set.mem_singleton_iff]
    rw [sets_succ] at hy
    ext c
    obtain hc | hc := lt_or_ge c.toOrdinal o
    · rw [← c.toOrdinal_toNatOrdinal, sets_congr_of_lt s o c.toOrdinal hc x hx,
        sets_congr_of_lt s o c.toOrdinal hc y hy.left]
    · rw [← Ordinal.toNatOrdinal.map_rel_iff, NatOrdinal.toOrdinal_toNatOrdinal] at hc
      rw [x.apply_eq_zero_of_le hc hxo, y.apply_eq_zero_of_le hc (hy.right.trans h)]
  · rw [singleton_subset_iff, sets_succ]
    refine ⟨hx, ?_⟩
    rwa [h]

private def sSup'' (s : Set SignExpansion.{u}) (o : Ordinal.{u}) : SignType :=
  ⨆ i ∈ sets s o, i o.toNatOrdinal

private theorem sSup''_valid (s : Set SignExpansion.{u}) : IsUpperSet (sSup'' s ⁻¹' {0}) := by
  intro a b hab ha
  rw [Set.mem_preimage, Set.mem_singleton_iff, sSup''] at ha ⊢
  rw [le_iff_eq_or_succ_le] at hab
  obtain rfl | hab := hab
  · exact ha
  · have hk := sets_singleton_succ_of_zero s a ha
    obtain ⟨k, hk⟩ := hk
    have hb := sets_singleton_inc s (succ a) b k hab hk
    have hh := hk.superset
    rw [hb]
    rw [singleton_subset_iff, sets_succ, ha] at hh
    simp only [mem_singleton_iff, iSup_iSup_eq_left]
    exact k.apply_eq_zero_of_le ((le_succ a).trans hab) hh.right

private def sSup' (s : Set SignExpansion.{u}) : SignExpansion.{u} where
  sign i := sSup'' s i.toOrdinal
  isUpperSet_sign_preimage_singleton_zero := by
    intro a b hab hb
    cases a with | toNatOrdinal a =>
    cases b with | toNatOrdinal b =>
    rw [mem_preimage, Ordinal.toNatOrdinal_toOrdinal, mem_singleton_iff] at hb ⊢
    exact sSup''_valid s (Ordinal.toNatOrdinal.map_rel_iff.mp hab) hb

instance completeSemilatticeSup : CompleteSemilatticeSup SignExpansion.{u} where
  sSup := sSup'
  le_sSup := by
    intro s a has
    rw [le_iff_toLex, ← not_lt]
    intro ⟨k, hkl, hk⟩
    simp_rw [Pi.toLex_apply, sSup', sSup'', NatOrdinal.toOrdinal_toNatOrdinal, coe_mk] at hk hkl
    revert hk
    rw [imp_false, not_lt]
    apply le_biSup fun i : SignExpansion => i k
    apply congr_sets_of_lt s k.toOrdinal a has
    intro o' ho'
    rw [← Ordinal.toNatOrdinal.lt_iff_lt, NatOrdinal.toOrdinal_toNatOrdinal] at ho'
    rw [← hkl o'.toNatOrdinal ho', o'.toNatOrdinal_toOrdinal]
  sSup_le := by
    intro s a
    simp_rw [le_iff_toLex, ← not_lt, ← not_exists]
    rw [not_exists, not_imp_not]
    intro ⟨d, hll, hd⟩
    simp_rw [Pi.toLex_apply, sSup', coe_mk, sSup''] at hd hll
    rw [lt_biSup_iff] at hd
    obtain ⟨k, hk, hik⟩ := hd
    refine ⟨k, ?_, d, ?_, ?_⟩
    · rw [← sets_zero s]
      exact sets_anti_right s d.toOrdinal.zero_le hk
    · intro j hj
      rw [Pi.toLex_apply, Pi.toLex_apply, hll j hj, ← j.toOrdinal_toNatOrdinal]
      rw [sets_congr_of_lt s d.toOrdinal j.toOrdinal (NatOrdinal.toOrdinal.lt_iff_lt.mpr hj) k hk]
      rw [j.toOrdinal_toNatOrdinal, j.toOrdinal_toNatOrdinal]
    · simpa using hik

instance completeLinearOrder : CompleteLinearOrder SignExpansion.{u} where
  __ := linearOrder
  __ := linearOrder.toBiheytingAlgebra
  __ := completeLatticeOfCompleteSemilatticeSup SignExpansion

end CompleteLattice

instance : Neg SignExpansion.{u} where
  neg e := {
    sign := -e
    isUpperSet_sign_preimage_singleton_zero a b hab ha := by
      simp only [mem_preimage, Pi.neg_apply, mem_singleton_iff, SignType.neg_eq_zero,
        apply_eq_zero] at ha ⊢
      exact ha.trans (WithTop.coe_le_coe.2 hab)
  }

@[simp] theorem coe_neg (e : SignExpansion) : ⇑(-e) = -⇑e := rfl

theorem neg_apply (e : SignExpansion) (o : Ordinal) : (-e) o = -e o := rfl

end SignExpansion
