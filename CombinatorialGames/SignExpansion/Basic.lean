/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Violeta Hernández Palacios
-/
import CombinatorialGames.NatOrdinal.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Sign.Defs
import Mathlib.Order.CompleteLattice.PiLex

/-!
# Sign expansions

In this repository we define the type of `Surreal` numbers following Conway's theory of games. A
popular alternative is to instead define the surreals as potentially infinite "expansions of signs",
setting for instance `+ = 1`, `- = -1`, `+- = ½`, etc.

This file defines the type `SignExpansion` and constructs its basic instances. We do not yet link it
to the development of surreal numbers.
-/

universe u

/-! ### For Mathlib -/

attribute [grind =] Pi.toLex_apply

instance : ZeroLEOneClass SignType where
  zero_le_one := by decide

@[local simp← ]
theorem Set.preimage_neg {α ι : Type*} [InvolutiveNeg α] (f : ι → α) {s : Set α} :
    f ⁻¹' (-s) = (-f) ⁻¹' s :=
  rfl

@[simp]
theorem Pi.Lex.neg_apply {α β : Type*} [Neg β] (x : Lex (α → β)) (i : α) : (-x) i = -x i :=
  rfl

-- TODO: we're missing an `AntitoneNeg` typeclass to express the following theorems generally.

theorem Pi.Lex.neg_lt_neg {α : Type*} [LinearOrder α] [WellFoundedLT α]
    {x y : Lex (α → SignType)} (h : x < y) : -y < -x := by
  obtain ⟨i, hi⟩ := h
  use i
  simp_all

@[simp]
theorem Pi.Lex.neg_lt_neg_iff {α : Type*} [LinearOrder α] [WellFoundedLT α]
    {x y : Lex (α → SignType)} : -x < -y ↔ y < x where
  mp := by simpa using @Pi.Lex.neg_lt_neg _ _ _ (-x) (-y)
  mpr := Pi.Lex.neg_lt_neg

@[simp]
theorem Pi.Lex.neg_le_neg_iff {α : Type*} [LinearOrder α] [WellFoundedLT α]
    {x y : Lex (α → SignType)} : -x ≤ -y ↔ y ≤ x := by
  simp [← not_lt]

theorem Pi.Lex.neg_lt_iff {α : Type*} [LinearOrder α] [WellFoundedLT α]
    {x y : Lex (α → SignType)} : -x < y ↔ -y < x := by
  simpa using Pi.Lex.neg_lt_neg_iff (y := -y)

theorem Pi.Lex.lt_neg_iff {α : Type*} [LinearOrder α] [WellFoundedLT α]
    {x y : Lex (α → SignType)} : x < -y ↔ y < -x := by
  simpa using Pi.Lex.neg_lt_neg_iff (x := -x)

theorem Pi.Lex.neg_le_iff {α : Type*} [LinearOrder α] [WellFoundedLT α]
    {x y : Lex (α → SignType)} : -x ≤ y ↔ -y ≤ x := by
  simpa using Pi.Lex.neg_le_neg_iff (y := -y)

theorem Pi.Lex.le_neg_iff {α : Type*} [LinearOrder α] [WellFoundedLT α]
    {x y : Lex (α → SignType)} : x ≤ -y ↔ y ≤ -x := by
  simpa using Pi.Lex.neg_le_neg_iff (x := -x)

/-! ### Sign expansions -/

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

/-- Adjust definitional equalities of a sign expansion. -/
def copy (x : SignExpansion) (sign : NatOrdinal → SignType)
    (h : sign = x) : SignExpansion where
  sign
  isUpperSet_preimage_singleton_zero' := h ▸ isUpperSet_preimage_singleton_zero x

@[simp]
theorem copy_eq (x : SignExpansion) (sign : NatOrdinal → SignType)
    (h : sign = x) : x.copy sign h = x :=
  DFunLike.coe_injective h

@[simp] theorem coe_mk (f h) : mk f h = f := rfl
@[simp] theorem sign_eq_coe (x : SignExpansion) : x.sign = ⇑x := rfl

@[ext]
protected theorem ext {x y : SignExpansion} (hxy : ∀ o, x o = y o) : x = y :=
  DFunLike.coe_injective (funext hxy)

@[simp]
theorem mk_eq_mk {f g h₁ h₂} : mk f h₁ = mk g h₂ ↔ f = g := by
  simp [DFunLike.ext'_iff]

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
  neg e := ⟨-e, by simpa using e.2⟩

@[simp] theorem coe_neg (x : SignExpansion) : ⇑(-x : SignExpansion) = -⇑x := rfl
theorem neg_apply (x : SignExpansion) (o : NatOrdinal) : (-x) o = -x o := rfl
@[simp] theorem neg_mk (f h) : -mk f h = mk (-f) (by simpa) := rfl

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
    (x ↾ o).length = min x.length o := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  cases c <;> simp [← apply_eq_zero, restrict, imp_iff_or_not]

@[simp]
theorem restrict_of_length_le {x : SignExpansion} {o : WithTop NatOrdinal}
    (ho : x.length ≤ o) : x ↾ o = x := by
  ext o'
  obtain ho' | ho' := lt_or_ge (↑o') x.length
  · rw [restrict_apply_of_coe_lt (ho'.trans_le ho)]
  · rw [apply_of_length_le ho']
    apply apply_of_length_le
    simp [ho']

@[simp, grind =]
theorem restrict_restrict_eq {x : SignExpansion} {o₁ o₂ : WithTop NatOrdinal} :
    (x ↾ o₁) ↾ o₂ = x ↾ min o₁ o₂ := by
  aesop

@[simp]
theorem restrict_zero_left (o : WithTop NatOrdinal) : 0 ↾ o = 0 := by
  ext; simp [apply_eq_zero]

@[simp]
theorem restrict_zero_right (x : SignExpansion) : x ↾ 0 = 0 := by
  ext; simp [apply_eq_zero]

@[simp]
theorem restrict_top_right {x : SignExpansion} : x ↾ ⊤ = x :=
  rfl

/-! ### Subset relation -/

/-- We write `x ⊆ y` when `x = y ↾ o` for some `o`. In the literature, this is written as
`x ≤ₛ y` or `x ⊑ y`. -/
instance : HasSubset SignExpansion where
  Subset x y := y ↾ x.length = x

/-- We write `x ⊂ y` when `x ⊆ y` and `x ≠ y`. In the literature, this is written as
`x <ₛ y` or `x ⊏ y`. -/
instance : HasSSubset SignExpansion where
  SSubset x y := x ⊆ y ∧ ¬ y ⊆ x

theorem subset_def {x y : SignExpansion} : x ⊆ y ↔ y ↾ x.length = x := .rfl
theorem ssubset_def {x y : SignExpansion} : x ⊂ y ↔ x ⊆ y ∧ ¬ y ⊆ x := .rfl

alias ⟨eq_of_subset, _⟩ := subset_def

@[simp]
theorem restrict_subset (x : SignExpansion) (o : WithTop NatOrdinal) : x ↾ o ⊆ x := by
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

-- This has deliberately not been upstreamed to Mathlib.
instance : CompleteLinearOrder SignType := Fintype.toCompleteLinearOrder _

instance : LinearOrder SignExpansion :=
  LinearOrder.lift' (toLex ⇑·) (by simp [Function.Injective])

theorem le_iff_toLex {x y : SignExpansion} : x ≤ y ↔ toLex ⇑x ≤ toLex ⇑y := .rfl
theorem lt_iff_toLex {x y : SignExpansion} : x < y ↔ toLex ⇑x < toLex ⇑y := .rfl

instance : BoundedOrder SignExpansion where
  le_top _ := le_iff_toLex.2 le_top
  bot_le _ := le_iff_toLex.2 bot_le

protected theorem neg_lt_neg {x y : SignExpansion} (h : x < y) : -y < -x :=
  Pi.Lex.neg_lt_neg h

@[simp]
protected theorem neg_lt_neg_iff {x y : SignExpansion} : -x < -y ↔ y < x :=
  Pi.Lex.neg_lt_neg_iff

@[simp]
protected theorem neg_le_neg_iff {x y : SignExpansion} : -x ≤ -y ↔ y ≤ x :=
  Pi.Lex.neg_le_neg_iff

protected theorem neg_le {x y : SignExpansion} : -x ≤ y ↔ -y ≤ x :=
  by simpa using SignExpansion.neg_le_neg_iff (y := -y)

protected theorem le_neg {x y : SignExpansion} : x ≤ -y ↔ y ≤ -x :=
  by simpa using SignExpansion.neg_le_neg_iff (x := -x)

protected theorem neg_lt {x y : SignExpansion} : -x < y ↔ -y < x :=
  by simpa using SignExpansion.neg_lt_neg_iff (y := -y)

protected theorem lt_neg {x y : SignExpansion} : x < -y ↔ y < -x :=
  by simpa using SignExpansion.neg_lt_neg_iff (x := -x)

/-! #### Floor function -/

open Classical in
/-- The floor function on a function `NatOrdinal → SignType` "rounds" it downwards to the nearest
valid `SignExpansion`. -/
def floor (f : NatOrdinal → SignType) : SignExpansion :=
  if hf : IsUpperSet (f ⁻¹' {0}) then ⟨f, hf⟩ else
    let a := sInf (f ⁻¹' {0})
    haveI ha b : b < a → f b ≠ 0 := notMem_of_lt_csInf'
    { sign c := if c < a then f c else
        if f (sInf {b | a < b ∧ f b ≠ 0}) = -1 then
          if c = a then -1 else 1
        else 0
      isUpperSet_preimage_singleton_zero' := by
        by_cases h : f (sInf {b | a < b ∧ f b ≠ 0}) = -1
        · convert isUpperSet_empty
          aesop
        · convert isUpperSet_Ici a
          aesop }

private theorem floor_of_eq_neg_one {f : NatOrdinal → SignType} (hf : ¬ IsUpperSet (f ⁻¹' {0}))
    (hf' : f (sInf {b | sInf (f ⁻¹' {0}) < b ∧ f b ≠ 0}) = -1) (c : NatOrdinal) :
    floor f c = if c < sInf (f ⁻¹' {0}) then f c else if c = sInf (f ⁻¹' {0}) then -1 else 1 := by
  simp_all [floor]

private theorem floor_of_eq_one {f : NatOrdinal → SignType} (hf : ¬ IsUpperSet (f ⁻¹' {0}))
    (hf' : f (sInf {b | sInf (f ⁻¹' {0}) < b ∧ f b ≠ 0}) = 1) (c : NatOrdinal) :
    floor f c = if c < sInf (f ⁻¹' {0}) then f c else 0 := by
  simp_all [floor]

private theorem nonempty_of_not_isUpperSet {f : NatOrdinal → SignType}
    (hf : ¬ IsUpperSet (f ⁻¹' {0})) :
    (f ⁻¹' {0}).Nonempty ∧ {b | sInf (f ⁻¹' {0}) < b ∧ f b ≠ 0}.Nonempty := by
  constructor
  · contrapose! hf
    rw [hf]
    exact isUpperSet_empty
  · simp_rw [IsUpperSet, Set.mem_preimage, Set.mem_singleton_iff, not_forall] at hf
    obtain ⟨a, b, hab, ha, hb⟩ := hf
    obtain rfl | hab := hab.eq_or_lt
    · contradiction
    · exact ⟨b, hab.trans_le' <| csInf_le' ha, hb⟩

theorem floor_of_isUpperSet {f : NatOrdinal → SignType} (hf : IsUpperSet (f ⁻¹' {0})) :
    floor f = ⟨f, hf⟩ :=
  dif_pos hf

@[simp]
theorem floor_coe (x : SignExpansion) : floor x = x :=
  floor_of_isUpperSet x.2

theorem floor_apply_of_lt_sInf {f : NatOrdinal → SignType} {a : NatOrdinal}
    (hf : a < sInf (f ⁻¹' {0})) : floor f a = f a := by
  rw [floor]
  split_ifs
  · rfl
  · simp [hf.not_ge]

theorem floor_lt_of_not_isUpperSet {f : NatOrdinal → SignType} (hf : ¬ IsUpperSet (f ⁻¹' {0})) :
    toLex ⇑(floor f) < toLex f := by
  obtain ⟨hf₁, hf₂⟩ := nonempty_of_not_isUpperSet hf
  have hf' := csInf_mem hf₁
  rw [floor, dif_neg hf]
  dsimp
  split_ifs with h
  · use sInf (f ⁻¹' {0})
    simp_all
  · refine ⟨sInf {b | sInf (f ⁻¹' {0}) < b ∧ f b ≠ 0}, ?_, ?_⟩
    · simp_rw [Pi.toLex_apply, ite_eq_left_iff, not_lt]
      intro a ha ha'
      by_contra ha₀
      obtain rfl | ha' := ha'.eq_or_lt
      · simp_all
      · exact notMem_of_lt_csInf' ha ⟨ha', Ne.symm ha₀⟩
    · dsimp
      rw [if_neg]
      · obtain h | h | h := (f (sInf {b | sInf (f ⁻¹' {0}) < b ∧ f b ≠ 0})).trichotomy
        · contradiction
        · cases (csInf_mem hf₂).2 h
        · exact h ▸ zero_lt_one
      · exact (csInf_mem hf₂).1.not_gt

theorem floor_le (f : NatOrdinal → SignType) : toLex ⇑(floor f) ≤ toLex f := by
  by_cases hf : IsUpperSet (f ⁻¹' {0})
  · rw [floor_of_isUpperSet hf]; rfl
  · exact (floor_lt_of_not_isUpperSet hf).le

theorem floor_lt {f : NatOrdinal → SignType} {x : SignExpansion} :
    floor f < x ↔ toLex f < toLex ⇑x := by
  by_cases hf : IsUpperSet (f ⁻¹' {0})
  · rw [floor_of_isUpperSet hf]
    rfl
  obtain ⟨hf₁, hf₂⟩ := nonempty_of_not_isUpperSet hf
  have hf₁' := csInf_mem hf₁
  have hf₂' := csInf_mem hf₂
  refine ⟨fun ⟨a, ha⟩ ↦ ?_, (floor_le f).trans_lt⟩
  dsimp at ha
  obtain ha' | ha' := lt_or_ge a (sInf (f ⁻¹' {0}))
  · rw [floor_apply_of_lt_sInf ha'] at ha
    exact ⟨a, fun b hb ↦ (floor_apply_of_lt_sInf (hb.trans ha')).symm.trans (ha.1 _ hb), ha.2⟩
  · obtain h | h | h := (f (sInf {b | sInf (f ⁻¹' {0}) < b ∧ f b ≠ 0})).trichotomy
    · simp_rw [floor_of_eq_neg_one hf h, if_neg ha'.not_gt] at ha
      obtain rfl | ha' := ha'.eq_or_lt
      · rw [if_pos rfl] at ha
        simp +contextual only [↓reduceIte] at ha
        obtain hx | hx | hx := (x (sInf (f ⁻¹' {0}))).trichotomy
        · simp [hx] at ha
        · refine ⟨sInf {b | sInf (f ⁻¹' {0}) < b ∧ f b ≠ 0}, fun b hb ↦ ?_, ?_⟩
          · obtain hb' | hb' := lt_or_ge b (sInf (f ⁻¹' {0}))
            · exact ha.1 b hb'
            · apply Eq.trans _ (x.isUpperSet_preimage_singleton_zero hb' hx).symm
              by_contra
              refine notMem_of_lt_csInf' hb ⟨hb'.lt_of_ne ?_, this⟩
              grind
          · dsimp
            rw [h, SignType.neg_one_lt_iff]
            exact (x.isUpperSet_preimage_singleton_zero hf₂'.1.le hx).ge
        · use sInf (f ⁻¹' {0})
          simp_all
      · rw [if_neg ha'.ne'] at ha
        simpa using ha.2
    · cases hf₂'.2 h
    · simp_rw [floor_of_eq_one hf h, if_neg ha'.not_gt] at ha
      obtain rfl | ha' := ha'.eq_or_lt
      · use sInf (f ⁻¹' {0})
        simp_all
      · apply (mt (x.isUpperSet_preimage_singleton_zero ha'.le) ha.2.ne' _).elim
        simpa using (ha.1 _ ha').symm

theorem le_floor {f : NatOrdinal → SignType} {x : SignExpansion} :
    x ≤ floor f ↔ toLex ⇑x ≤ toLex f := by
  simpa using floor_lt.not

theorem gc_coe_floor : GaloisConnection (toLex ∘ (⇑·) : SignExpansion → _) (floor ∘ ofLex) :=
  fun _ _ ↦ le_floor.symm

/-- `floor` as a Galois coinsertion. -/
def gciFloor : GaloisCoinsertion (toLex ∘ (⇑·) : SignExpansion → _) (floor ∘ ofLex) where
  gc := gc_coe_floor
  u_l_le := by simp
  choice x h := (floor (ofLex x)).copy (ofLex x) (toLex_inj.1 (h.antisymm (gc_coe_floor.l_u_le x)))
  choice_eq x h := copy_eq ..

/-! #### Ceiling function -/

/-- The ceiling function on a function `NatOrdinal → SignType` "rounds" it upwards to the nearest
valid `SignExpansion`. -/
def ceil (f : NatOrdinal → SignType) : SignExpansion :=
  -floor (-f)

theorem ceil_of_isUpperSet {f : NatOrdinal → SignType} (hf : IsUpperSet (f ⁻¹' {0})) :
    ceil f = ⟨f, hf⟩ := by
  rw [ceil, floor_of_isUpperSet (by simpa)]
  simp

@[simp]
theorem ceil_coe (x : SignExpansion) : ceil x = x :=
  ceil_of_isUpperSet x.2

theorem ceil_apply_of_lt_sInf {f : NatOrdinal → SignType} {a : NatOrdinal}
    (hf : a < sInf (f ⁻¹' {0})) : ceil f a = f a := by
  rw [ceil, neg_apply, floor_apply_of_lt_sInf]
  · simp
  · simpa

theorem lt_ceil_of_not_isUpperSet {f : NatOrdinal → SignType} (h : ¬ IsUpperSet (f ⁻¹' {0})) :
    toLex f < toLex ⇑(ceil f) := by
  rw [ceil]
  simpa [Pi.Lex.lt_neg_iff] using floor_lt_of_not_isUpperSet (f := -f) (by simpa)

theorem le_ceil (f : NatOrdinal → SignType) : toLex f ≤ toLex ⇑(ceil f) := by
  rw [ceil]
  simpa [Pi.Lex.le_neg_iff] using floor_le (-f)

theorem lt_ceil {f : NatOrdinal → SignType} {x : SignExpansion} :
    x < ceil f ↔ toLex ⇑x < toLex f := by
  rw [ceil, SignExpansion.lt_neg, floor_lt]
  simp

theorem ceil_le {f : NatOrdinal → SignType} {x : SignExpansion} :
    ceil f ≤ x ↔ toLex f ≤ toLex ⇑x := by
  simpa using lt_ceil.not

theorem gc_ceil_coe : GaloisConnection (ceil ∘ ofLex) (toLex ∘ (⇑·) : SignExpansion → _) :=
  fun _ _ ↦ ceil_le

/-- `ceil` as a Galois insertion. -/
def giCeil : GaloisInsertion (ceil ∘ ofLex) (toLex ∘ (⇑·) : SignExpansion → _) where
  gc := gc_ceil_coe
  le_l_u := by simp
  choice x h := (ceil (ofLex x)).copy (ofLex x) (toLex_inj.1 ((gc_ceil_coe.le_u_l x).antisymm h))
  choice_eq x h := copy_eq ..

@[simp]
theorem floor_neg (f : NatOrdinal → SignType) : floor (-f) = -ceil f := by
  simp [ceil]

@[simp]
theorem ceil_neg (f : NatOrdinal → SignType) : ceil (-f) = -floor f := by
  simp [ceil]

theorem floor_le_ceil (f : NatOrdinal → SignType) : floor f ≤ ceil f :=
  (floor_le f).trans (le_ceil f)

theorem floor_lt_ceil_of_not_isUpperSet {f : NatOrdinal → SignType} (h : ¬ IsUpperSet (f ⁻¹' {0})) :
    floor f < ceil f :=
  (floor_lt_of_not_isUpperSet h).trans_le (le_ceil f)

/-! #### Complete linear order instance -/

instance : CompleteLattice SignExpansion :=
  fast_instance%
  { __ := instLinearOrder.toBiheytingAlgebra _
    __ := giCeil.liftCompleteLattice.toCompleteSemilatticeInf
    __ := gciFloor.liftCompleteLattice.toCompleteSemilatticeSup }

instance : CompleteLinearOrder SignExpansion where
  __ := LinearOrder.toBiheytingAlgebra _
  __ := instCompleteLattice
  __ := instLinearOrder

theorem coe_sInf (s : Set SignExpansion) :
    sInf s = ofLex (sInf ((fun x : SignExpansion ↦ toLex ⇑x) '' s)) := rfl

theorem coe_iInf {ι} (f : ι → SignExpansion) :
    ⨅ i, f i = ofLex (⨅ i : ι, toLex (⇑(f i))) := by
  rw [iInf, coe_sInf]
  congr
  aesop

theorem sInf_apply (s : Set SignExpansion) (i : NatOrdinal) :
    sInf s i = ⨅ x : {x : SignExpansion // x ∈ s ∧ ∀ j < i, x j = sInf s j}, x.1 i := by
  rw [coe_sInf, Pi.ofLex_apply, Pi.Lex.sInf_apply]
  apply congrArg sInf
  aesop

theorem coe_sSup (s : Set SignExpansion) :
    sSup s = ofLex (sSup ((fun x : SignExpansion ↦ toLex ⇑x) '' s)) := rfl

theorem coe_iSup {ι} (f : ι → SignExpansion) :
    ⨆ i, f i = ofLex (⨆ i : ι, toLex (⇑(f i))) := by
  rw [iSup, coe_sSup]
  congr
  aesop

theorem sSup_apply (s : Set SignExpansion) (i : NatOrdinal) :
    sSup s i = ⨆ x : {x : SignExpansion // x ∈ s ∧ ∀ j < i, x j = sSup s j}, x.1 i := by
  rw [coe_sSup, Pi.ofLex_apply, Pi.Lex.sSup_apply]
  apply congrArg sSup
  aesop

end SignExpansion

/-! ### Cast from ordinals -/

namespace NatOrdinal
open SignExpansion

variable {o₁ o₂ : NatOrdinal}

/-- Returns the sign expansion with the corresponding number of `1`s. -/
def toSignExpansion : NatOrdinal ↪o SignExpansion :=
  .ofStrictMono (⊤ ↾ ·) fun x y h ↦ by
    use x
    aesop (add apply unsafe [lt_trans])

instance : Coe NatOrdinal SignExpansion where
  coe x := x.toSignExpansion

theorem toSignExpansion_def (o : NatOrdinal) : o = ⊤ ↾ o := rfl

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
