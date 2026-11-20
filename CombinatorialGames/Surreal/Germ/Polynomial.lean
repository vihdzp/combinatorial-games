/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Germ.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs

import CombinatorialGames.Mathlib.Polynomial.TranslatedPowers
import CombinatorialGames.Surreal.Scale.RoundedPowers
import CombinatorialGames.Surreal.Scale.RoundedProduct
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Polynomial values at a positive precision

Representatives whose readings belong to a subring of germs form a subring. Replacing the
base of each power by its difference from an early projection reads a polynomial value as
a polynomial in the original germ.
-/

universe u

open scoped Pointwise

open Polynomial Set

public noncomputable section

namespace Surreal

variable (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex]

local notation "A" => unitExponentSubgroup C
local notation "U" => residueRepresentatives C
local notation "D[" t "]" => (ω^ (t : Surreal) • infinitesimals C)

private theorem wpow_notMem_of_precision_pos {t : Surreal.{u}} (ht : 0 < t)
    (htfix : cosetRep A t = t) : ω^ t ∉ C := by
  apply (notMem_subring_iff_precisionLevel_pos C (wpow_ne_zero t)).mpr
  rwa [precisionLevel_wpow, htfix]

private theorem wpow_mem_residueRepresentatives {t : Surreal.{u}} (ht : 0 ≤ t) :
    ω^ t ∈ U := by
  simpa only [mul_one] using wpow_mul_mem_residueRepresentatives C ht (U).one_mem

private theorem germMap_wpow_mem (S : Subring (Germ C)) {t : Surreal.{u}} (ht : 0 ≤ t)
    (htfix : cosetRep A t = t) :
    germMap C ⟨ω^ t, wpow_mem_residueRepresentatives C ht⟩ ∈ S := by
  rcases eq_or_lt_of_le ht with rfl | hp
  · have heq : (⟨ω^ (0 : Surreal.{u}), wpow_mem_residueRepresentatives C le_rfl⟩ : U) = 1 :=
      Subtype.ext wpow_zero
    rw [heq, map_one]
    exact S.one_mem
  · have heq : germMap C ⟨ω^ t, wpow_mem_residueRepresentatives C ht⟩ = 0 :=
      (germMap_eq_zero_iff C).mpr ((mem_germIdeal_iff C).mpr
        (Or.inr ⟨t, wpow_notMem_of_precision_pos C hp htfix, 1, (mul_one _).symm⟩))
    rw [heq]
    exact S.zero_mem

private theorem germReading_mul_mem (S : Subring (Germ C)) (x y : U)
    (hx : ∀ t : Surreal.{u}, 0 ≤ t → cosetRep A t = t → germReading C t x ∈ S)
    (hy : ∀ t : Surreal.{u}, 0 ≤ t → cosetRep A t = t → germReading C t y ∈ S)
    {t : Surreal.{u}} (ht : 0 ≤ t) (htfix : cosetRep A t = t) :
    germReading C t ((x : Surreal.{u}) * y) ∈ S := by
  let V : Subring U := S.comap (germMap C)
  let W : Subring Surreal.{u} := V.map (U).subtype
  have hgen : roundedProductGenerators C t x y ⊆ W := by
    intro z hz
    obtain ⟨r, hr, hrfix, rfl | rfl | rfl⟩ := (mem_roundedProductGenerators C).mp hz
    · exact Subring.mem_map.mpr
        ⟨⟨_, wpow_mem_residueRepresentatives C hr.1⟩, germMap_wpow_mem C S hr.1 hrfix, rfl⟩
    · refine Subring.mem_map.mpr ⟨⟨_, roundAt_mem_residueRepresentatives C r x⟩, ?_, rfl⟩
      change germMap C ⟨roundAt C r x, _⟩ ∈ S
      rw [← germReading_eq]
      exact hx r hr.1 hrfix
    · refine Subring.mem_map.mpr ⟨⟨_, roundAt_mem_residueRepresentatives C r y⟩, ?_, rfl⟩
      change germMap C ⟨roundAt C r y, _⟩ ∈ S
      rw [← germReading_eq]
      exact hy r hr.1 hrfix
  obtain ⟨z, hz, heq⟩ := Subring.mem_map.mp <| Subring.closure_le.mpr hgen <|
    roundAt_mul_mem_closure C ht htfix x y x.2 y.2
  have h : z = ⟨_, roundAt_mem_residueRepresentatives C t ((x : Surreal.{u}) * y)⟩ :=
    Subtype.ext heq
  rw [germReading_eq]
  exact h ▸ hz

/-- Representatives whose readings at all nonnegative precisions belong to the given
subring of germs. -/
def germReadingSubring (S : Subring (Germ C)) : Subring U where
  carrier := {x | ∀ t : Surreal.{u}, 0 ≤ t → cosetRep A t = t → germReading C t x ∈ S}
  zero_mem' := by
    intro t _ _
    rw [Subring.coe_zero, germReading_zero_input]
    exact S.zero_mem
  one_mem' := by
    intro t ht hfix
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, germReading_zero, map_one]
      exact S.one_mem
    · have hread := germReading_residueSubfield_eq_zero C h hfix (1 : residueSubfield C)
      rw [Subring.coe_one]
      rw [Subfield.coe_one] at hread
      rw [hread]
      exact S.zero_mem
  add_mem' := by
    intro x y hx hy t ht hfix
    rw [Subring.coe_add, germReading_add]
    exact S.add_mem (hx t ht hfix) (hy t ht hfix)
  neg_mem' := by
    intro x hx t ht hfix
    rw [Subring.coe_neg, ← zero_sub, germReading_sub, germReading_zero_input, zero_sub]
    exact S.neg_mem (hx t ht hfix)
  mul_mem' := by
    intro x y hx hy t ht hfix
    exact germReading_mul_mem C S x y hx hy ht hfix

/-- Membership in the subring defined by the readings at nonnegative precisions. -/
theorem mem_germReadingSubring {S : Subring (Germ C)} {x : U} :
    x ∈ germReadingSubring C S ↔
      ∀ t : Surreal.{u}, 0 ≤ t → cosetRep A t = t → germReading C t x ∈ S :=
  Iff.rfl

private theorem scaleCosetRep_mem_germReadingSubring (S : Subring (Germ C)) (x : U)
    (hx : ∀ t : Surreal.{u}, 0 < t → cosetRep A t = t → germReading C t x ∈ S)
    {s : Surreal.{u}} (hs : 0 < s) (hsfix : cosetRep A s = s) :
    (⟨cosetRep D[s] x, cosetRep_wpow_smul_mem_residueRepresentatives C hs.le x⟩ : U) ∈
      germReadingSubring C S := by
  apply (mem_germReadingSubring C).mpr
  intro r hr hrfix
  change germReading C r (cosetRep D[s] x) ∈ S
  rcases lt_or_ge r s with hrs | hrs
  · have hfix : cosetRep A (s - r) = s - r := by rw [cosetRep_sub, hsfix, hrfix]
    rw [germReading_scaleCosetRep_eq_zero_of_notMem C hrs.le
      (wpow_notMem_of_precision_pos C (sub_pos.mpr hrs) hfix)]
    exact S.zero_mem
  · rw [germReading_scaleCosetRep_of_le C hrs]
    exact hx r (hs.trans_le hrs) hrfix

private def germReadingHom (t : Surreal.{u}) : U →+ Germ C where
  toFun x := germReading C t x
  map_zero' := by simpa only [Subring.coe_zero] using germReading_zero_input C t
  map_add' x y := by simpa only [Subring.coe_add] using germReading_add C t x y

private theorem exists_eval₂_eq_germReading_pos (S : Subring (Germ C)) (x : U)
    (hx : ∀ t : Surreal.{u}, 0 < t → cosetRep A t = t → germReading C t x ∈ S)
    {t : Surreal.{u}} (ht : 0 < t) (htfix : cosetRep A t = t) (n : ℕ)
    (F : (germReadingSubring C S)[X]) (hF : F.natDegree ≤ n) :
    ∃ f : S[X], f.natDegree ≤ n ∧
      f.eval₂ S.subtype (germMap C x) =
        germReading C t ((F.eval₂ (germReadingSubring C S).subtype x : U) : Surreal.{u}) ∧
      (f.coeff n : Germ C) = germReading C t ((F.coeff n : U) : Surreal.{u}) ∧
      (0 < n → F.coeff n = 1 → (f.coeff (n - 1) : Germ C) =
        germReading C t ((F.coeff (n - 1) : U) : Surreal.{u}) + n • germReading C t x) := by
  let R := germReadingSubring C S
  change ∃ f : S[X], f.natDegree ≤ n ∧
    f.eval₂ S.subtype (germMap C x) = germReadingHom C t (F.eval₂ R.subtype x) ∧
    (f.coeff n : Germ C) = germReadingHom C t (F.coeff n) ∧
    (0 < n → F.coeff n = 1 → (f.coeff (n - 1) : Germ C) =
      germReadingHom C t (F.coeff (n - 1)) + n • germReadingHom C t x)
  refine Polynomial.exists_eval₂_eq_of_translated_powers R S (germReadingHom C t) x (germMap C x)
    (fun c ↦ (mem_germReadingSubring C).mp c.property t ht.le htfix) ?_ n F hF
  intro c k hk
  obtain ⟨s, hs, hst, hsfix, hpow⟩ :=
    exists_roundAt_mul_sub_pow C ht htfix ((c : U) : Surreal.{u}) x.property hk
  let a' : U := ⟨cosetRep D[s] x, cosetRep_wpow_smul_mem_residueRepresentatives C hs.le x⟩
  let a : R := ⟨a', scaleCosetRep_mem_germReadingSubring C S x hx hs hsfix⟩
  refine ⟨a, 0, ?_, Or.inl rfl, ?_⟩
  · exact germReading_scaleCosetRep_of_le C hst.le x
  · rw [Subring.coe_zero, sub_zero]
    let w : U := x - a'
    have ha₀ : germMap C a' = 0 :=
      (germMap_eq_zero_iff C).mpr (cosetRep_wpow_smul_mem_germIdeal C hs.le
        (wpow_notMem_of_precision_pos C hs hsfix) x)
    have hw : germMap C w = germMap C x := by
      rw [show w = x - a' from rfl, map_sub, ha₀, sub_zero]
    change germReading C t (((c : U) * w ^ k : U) : Surreal.{u}) =
      germReading C t ((c : U) : Surreal.{u}) * (germMap C x) ^ k
    let v : Surreal.{u} := ((c : U) * w ^ k : U)
    let r : U := ⟨roundAt C t (c : U), roundAt_mem_residueRepresentatives C t (c : U)⟩
    have hpow' : (⟨roundAt C t v, roundAt_mem_residueRepresentatives C t v⟩ : U) =
        r * w ^ k := Subtype.ext hpow
    rw [germReading_eq, hpow', map_mul, map_pow, hw, ← germReading_eq]

/-- At a nonnegative precision a polynomial value reads as a polynomial of bounded degree in
the original germ. At positive precision its monic penultimate coefficient also records the
reading of the base. -/
theorem exists_eval₂_eq_germReading (S : Subring (Germ C)) (x : U)
    (hx : ∀ t : Surreal.{u}, 0 < t → cosetRep A t = t → germReading C t x ∈ S)
    {t : Surreal.{u}} (ht : 0 ≤ t) (htfix : cosetRep A t = t) (n : ℕ)
    (F : (germReadingSubring C S)[X]) (hF : F.natDegree ≤ n) :
    ∃ f : S[X], f.natDegree ≤ n ∧
      f.eval₂ S.subtype (germMap C x) =
        germReading C t ((F.eval₂ (germReadingSubring C S).subtype x : U) : Surreal.{u}) ∧
      (f.coeff n : Germ C) = germReading C t ((F.coeff n : U) : Surreal.{u}) ∧
      (0 < t → 0 < n → F.coeff n = 1 → (f.coeff (n - 1) : Germ C) =
        germReading C t ((F.coeff (n - 1) : U) : Surreal.{u}) + n • germReading C t x) := by
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t
    let R := germReadingSubring C S
    let φ : R →+* S := ((germMap C).comp R.subtype).codRestrict S (fun c ↦ by
      change germMap C (c : U) ∈ S
      rw [← germReading_zero]
      exact (mem_germReadingSubring C).mp c.property 0 le_rfl (cosetRep_zero A))
    refine ⟨F.map φ, Polynomial.natDegree_map_le.trans hF, ?_, ?_,
      fun h ↦ (lt_irrefl 0 h).elim⟩
    · rw [Polynomial.eval₂_map, germReading_zero]
      exact (Polynomial.hom_eval₂ F R.subtype (germMap C) x).symm
    · rw [Polynomial.coeff_map, germReading_zero]
      rfl
  · obtain ⟨f, hfdeg, hfeval, hfcoeff, hfnext⟩ :=
      exists_eval₂_eq_germReading_pos C S x hx ht htfix n F hF
    exact ⟨f, hfdeg, hfeval, hfcoeff, fun _ ↦ hfnext⟩

end Surreal
