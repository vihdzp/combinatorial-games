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
open Set

instance : FunLike SignExpansion NatOrdinal SignType where
  coe := sign
  coe_injective' a b hab := by cases a; cases b; cases hab; rfl

/-- Every sign after the first `0` is also `0`. -/
theorem isUpperSet_preimage_singleton_zero (e : SignExpansion) : IsUpperSet (e ⁻¹' {0}) := e.2

@[simp] theorem coe_mk (f h) : SignExpansion.mk f h = f := rfl
@[simp] theorem sign_eq_coe (e : SignExpansion) : e.sign = ⇑e := rfl

@[ext]
protected theorem ext {x y : SignExpansion} (hxy : ∀ o, x o = y o) : x = y :=
  DFunLike.coe_injective (funext hxy)

theorem apply_eq_zero_of_le {e : SignExpansion} {o o' : Ordinal}
    (hoo' : o ≤ o') (ho : e o = 0) : e o' = 0 :=
  isUpperSet_preimage_singleton_zero e hoo' ho

/-- The length of a sign expansion is the smallest ordinal at which it equals zero,
or `⊤` is no such ordinal exists. -/
def length (e : SignExpansion) : WithTop NatOrdinal :=
  sInf ((↑) '' (e ⁻¹' {0}))

theorem apply_of_length_le {e : SignExpansion} {o : NatOrdinal} (h : e.length ≤ o) : e o = 0 := by
  obtain he | he := (WithTop.some '' (e ⁻¹' {0})).eq_empty_or_nonempty
  · simp_all [length]
  · obtain ⟨a, ha, ha'⟩ := csInf_mem he
    apply apply_eq_zero_of_le _ ha
    rwa [← WithTop.coe_le_coe, ha']

theorem apply_eq_zero {e : SignExpansion} {o : NatOrdinal} : e o = 0 ↔ e.length ≤ o := by
  refine ⟨fun h ↦ csInf_le' ?_, apply_of_length_le⟩
  simpa

theorem length_eq_top {e : SignExpansion} : e.length = ⊤ ↔ ∀ o, e o ≠ 0 := by
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
      simp only [mem_preimage, Pi.neg_apply, mem_singleton_iff,
        SignType.neg_eq_zero_iff, apply_eq_zero] at ha ⊢
      exact ha.trans (WithTop.coe_le_coe.2 hab) }

@[simp] theorem coe_neg (e : SignExpansion) : ⇑(-e : SignExpansion) = -⇑e := rfl
theorem neg_apply (e : SignExpansion) (o : Ordinal) : (-e) o = -e o := rfl

/-- Cut off the part of a sign expansion after an ordinal `o`, by filling it in with zeros. -/
def restrict (x : SignExpansion) (o : WithTop NatOrdinal) : SignExpansion where
  sign i := if i < o then x.sign i else 0
  isUpperSet_preimage_singleton_zero' a b hab ha := by
    rw [← WithTop.coe_le_coe] at hab
    simp only [sign_eq_coe, mem_preimage, mem_singleton_iff,
      ite_eq_right_iff, apply_eq_zero] at ha ⊢
    exact fun hb ↦ (ha (hab.trans_lt hb)).trans hab

@[simp]
theorem length_restrict (x : SignExpansion) (o : WithTop NatOrdinal) :
    (x.restrict o).length = min x.length o := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  cases c <;> simp [← apply_eq_zero, restrict, imp_iff_or_not]

theorem restrict_apply_of_coe_lt {x : SignExpansion} {o₁ : WithTop NatOrdinal}
    {o₂ : NatOrdinal} (h : o₂ < o₁) : x.restrict o₁ o₂ = x o₂ := if_pos h

theorem restrict_apply_of_le_coe {x : SignExpansion} {o₁ : WithTop NatOrdinal}
    {o₂ : NatOrdinal} (h : o₁ ≤ o₂) : x.restrict o₁ o₂ = 0 := if_neg h.not_gt

theorem restrict_of_length_le {e : SignExpansion} {o : WithTop NatOrdinal}
    (ho : e.length ≤ o) : e.restrict o = e := by
  ext o'
  obtain ho' | ho' := lt_or_ge (↑o') e.length
  · rw [restrict_apply_of_coe_lt (ho'.trans_le ho)]
  · rw [apply_of_length_le ho']
    apply apply_of_length_le
    simp [ho']

@[simp]
theorem restrict_zero_left (o : NatOrdinal) : restrict 0 o = 0 := by
  ext; simp [apply_eq_zero]

@[simp]
theorem restrict_zero_right (e : SignExpansion) : e.restrict 0 = 0 := by
  ext; simp [apply_eq_zero]

@[simp]
theorem restrict_top_right {e : SignExpansion} : e.restrict ⊤ = e := by
  apply restrict_of_length_le; simp

/-! ### Order structure -/

-- #32444
instance : CompleteLinearOrder SignType := Fintype.toCompleteLinearOrder SignType

instance linearOrder : LinearOrder SignExpansion :=
  LinearOrder.lift' (toLex ⇑·) (by simp [Function.Injective])

theorem le_iff_toLex {a b : SignExpansion} : a ≤ b ↔ toLex ⇑a ≤ toLex ⇑b := Iff.rfl
theorem lt_iff_toLex {a b : SignExpansion} : a < b ↔ toLex ⇑a < toLex ⇑b := Iff.rfl

instance : BoundedOrder SignExpansion where
  le_top _ := le_iff_toLex.2 le_top
  bot_le _ := le_iff_toLex.2 bot_le

private def inf (s : Set SignExpansion) (o : NatOrdinal) : SignType :=
  ⨅ e : {e ∈ s | ∀ i < o, e i = inf s i}, e.1 o
termination_by o

private theorem exists_of_inf_ne_one {s : Set SignExpansion} {o : NatOrdinal} (h : inf s o ≠ 1) :
    ∃ e ∈ s, e o = inf s o ∧ ∀ i < o, e i = inf s i := by
  rw [inf] at h ⊢
  obtain hs | hs := isEmpty_or_nonempty {e ∈ s | ∀ i < o, e i = inf s i}
  · rw [iInf_of_empty] at h
    contradiction
  · obtain ⟨e, he⟩ := @ciInf_mem _ _ _ _ hs fun e ↦ e.1 o
    exact ⟨_, e.2.1, he, e.2.2⟩

instance : InfSet SignExpansion where
  sInf s :=
  { sign := inf s
    isUpperSet_preimage_singleton_zero' a b hab ha := by
      induction b using WellFoundedLT.induction with | ind b IH
      obtain rfl | hab := hab.eq_or_lt; assumption
      rw [mem_preimage, mem_singleton_iff] at ha ⊢
      rw [inf]
      convert iInf_const with e
      · exact e.1.isUpperSet_preimage_singleton_zero hab.le (ha ▸ e.2.2 _ hab)
      · rw [nonempty_coe_sort]
        obtain ⟨e, he, _, h⟩ := exists_of_inf_ne_one (ha.trans_ne <| by decide)
        refine ⟨e, he, fun i hi ↦ ?_⟩
        obtain hia | hai := lt_or_ge i a
        · exact h i hia
        · rw [IH i hi hai]
          apply e.isUpperSet_preimage_singleton_zero hai
          simp_all }

theorem sInf_apply (s : Set SignExpansion) (o : NatOrdinal) :
    sInf s o = ⨅ e : {e ∈ s | ∀ i < o, e i = sInf s i}, e.1 o := by
  dsimp [sInf]
  rw [inf]
  rfl

theorem sInf_apply_le {s : Set SignExpansion} {o : NatOrdinal} {e : SignExpansion}
    (he : e ∈ s) (h : ∀ i < o, e i = sInf s i) : sInf s o ≤ e o := by
  rw [sInf_apply]
  exact sInf_le ⟨⟨e, he, h⟩, rfl⟩

theorem le_sInf_apply {s : Set SignExpansion} {o : NatOrdinal} {e : SignExpansion}
    (h : ∀ f ∈ s, (∀ i < o, f i = sInf s i) → e o ≤ f o) : e o ≤ sInf s o := by
  rw [sInf_apply]
  apply le_sInf
  grind

theorem exists_of_sInf_ne_one {s : Set SignExpansion} {o : NatOrdinal} (h : sInf s o ≠ 1) :
    ∃ e ∈ s, e o = sInf s o ∧ ∀ i < o, e i = sInf s i :=
  exists_of_inf_ne_one h

instance : CompleteSemilatticeInf SignExpansion where
  sInf_le s e he := by
    by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (sInf_apply_le he ha.1)
  le_sInf s e h := by
    by_contra! hs
    obtain ⟨a, ha⟩ := hs
    apply ha.2.not_ge <| le_sInf_apply fun f hf hf' ↦ ?_
    -- TODO: make a lemma for this contrapose step
    have := h f hf
    contrapose! this
    use a
    simp_all

-- TODO: better def-eqs
instance : CompleteLinearOrder SignExpansion where
  __ := linearOrder
  __ := LinearOrder.toBiheytingAlgebra _
  __ := completeLatticeOfCompleteSemilatticeInf _

end SignExpansion
