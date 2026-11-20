/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Germ.Polynomial
public import Mathlib.RingTheory.AlgebraicIndependent.Defs

import CombinatorialGames.Mathlib.Polynomial.OrderedReadings
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Polynomial relations between germ readings

For a proper convex subring, a germ outside a coefficient subalgebra is transcendental over it
when its positive-precision readings lie there and each coefficient admits a representative with
all readings in the subalgebra. Ordering the readings of the given entries selects coordinates
for them.
-/

universe u

public noncomputable section

namespace Surreal

open Polynomial

variable (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex]

local notation "K" => residueSubfield C
local notation "U" => residueRepresentatives C
local notation "G" => Germ C
local notation "H" => unitExponentSubgroup C

private def germReadingSubringToSubalgebra (S : Subalgebra K G) :
    germReadingSubring C S.toSubring →+* S :=
  ((germMap C).comp (germReadingSubring C S.toSubring).subtype).codRestrict S.toSubring (fun p ↦ by
    change germMap C (p : U) ∈ S.toSubring
    rw [← germReading_zero]
    exact (mem_germReadingSubring C).mp p.2 0 le_rfl (cosetRep_zero H))

private theorem germMap_eval₂_germReadingSubring (S : Subalgebra K G) (x : U)
    (F : (germReadingSubring C S.toSubring)[X]) :
    germMap C (F.eval₂ (germReadingSubring C S.toSubring).subtype x) =
      (F.map (germReadingSubringToSubalgebra C S)).eval₂ S.toSubring.subtype (germMap C x) := by
  rw [Polynomial.eval₂_map]
  exact Polynomial.hom_eval₂ F (germReadingSubring C S.toSubring).subtype (germMap C) x

private theorem germMap_germReadingSubring_mem (S : Subalgebra K G)
    (x : germReadingSubring C S.toSubring) : germMap C (x : U) ∈ S := by
  rw [← germReading_zero]
  exact (mem_germReadingSubring C).mp x.2 0 le_rfl (cosetRep_zero H)

private theorem exists_monic_germRelation (hC : C ≠ ⊤) (S : Subalgebra K G)
    (hlift : Function.Surjective (germReadingSubringToSubalgebra C S)) (x : U)
    (hpos : ∀ t : Surreal.{u}, 0 < t → cosetRep H t = t → germReading C t x ∈ S)
    (p : S[X]) (hp : p ≠ 0) (heval : p.eval₂ S.toSubring.subtype (germMap C x) = 0) :
    ∃ q : S[X], q.Monic ∧ q.natDegree = p.natDegree ∧
      q.eval₂ S.toSubring.subtype (germMap C x) = 0 := by
  let d := p.natDegree
  obtain ⟨F, hFmap, hFdegree⟩ := exists_natDegree_eq_of_mem_lifts (mem_lifts_of_surjective hlift p)
  have hF : germMap C (F.eval₂ (germReadingSubring C S.toSubring).subtype x) = 0 := by
    rw [germMap_eval₂_germReadingSubring, hFmap, heval]
  have hFcoeff : germMap C ((F.coeff d : germReadingSubring C S.toSubring) : U) ≠ 0 := by
    intro hzero
    have hmap := congrArg (fun f : S[X] ↦ f.coeff d) hFmap
    rw [Polynomial.coeff_map] at hmap
    have hpcoeff : p.coeff d = 0 := by
      rw [← hmap]
      exact Subtype.ext hzero
    exact (Polynomial.leadingCoeff_ne_zero.mpr hp) hpcoeff
  obtain ⟨η, hη, hηfix, hηzero⟩ := exists_germReading_eq_zero_of_germMap_eq_zero C hC _ hF
  obtain ⟨t, k, ht₀, htη, htfix, hk₀, hscalar⟩ :=
    exists_germReading_eq_residueSubfield_of_germMap_ne_zero C _ hη hηfix hFcoeff
  obtain ⟨f, hfdegree, hfeval, hfcoeff, _⟩ :=
    exists_eval₂_eq_germReading C S.toSubring x hpos ht₀ htfix d F hFdegree.le
  let ki : S := ⟨residueSubfieldGerm C k⁻¹, by rw [← algebraMap_germ]; exact S.algebraMap_mem _⟩
  let q := Polynomial.C ki * f
  have hqcoeff : q.coeff d = 1 := by
    apply Subtype.ext
    change (q.coeff d : G) = 1
    dsimp [q]
    rw [Polynomial.coeff_C_mul]
    change residueSubfieldGerm C k⁻¹ * (f.coeff d : G) = 1
    rw [hfcoeff, hscalar, ← map_mul, inv_mul_cancel₀ hk₀, map_one]
  have hqdeg : q.natDegree = d :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      ((Polynomial.natDegree_C_mul_le ki f).trans hfdegree) (hqcoeff ▸ one_ne_zero)
  have hqmonic : q.Monic := by rw [Polynomial.Monic, Polynomial.leadingCoeff, hqdeg, hqcoeff]
  have hqeval : q.eval₂ S.toSubring.subtype (germMap C x) = 0 := by
    rw [show q = Polynomial.C ki * f from rfl, Polynomial.eval₂_mul, hfeval, hηzero t htη htfix,
      mul_zero]
  exact ⟨q, hqmonic, hqdeg, hqeval⟩

/-- A germ outside a subalgebra is transcendental over it if all its positive readings
belong to the subalgebra and every coefficient admits a lift with all readings there. -/
theorem injective_eval₂_germMap_of_pos_readings (hC : C ≠ ⊤) (S : Subalgebra K G)
    (hlift : ∀ a : S, ∃ f : germReadingSubring C S.toSubring, germMap C (f : U) = (a : G))
    (x : U) (hx : germMap C x ∉ S)
    (hpos : ∀ t : Surreal.{u}, 0 < t → cosetRep H t = t → germReading C t x ∈ S) :
    Function.Injective (Polynomial.eval₂ S.toSubring.subtype (germMap C x)) := by
  intro a b hab
  by_contra hab'
  have hrel : ∃ p : S[X], p ≠ 0 ∧ p.eval₂ S.toSubring.subtype (germMap C x) = 0 :=
    ⟨a - b, sub_ne_zero.mpr hab', by rw [Polynomial.eval₂_sub, hab, sub_self]⟩
  obtain ⟨p, hp⟩ := exists_minimalFor_of_wellFoundedLT
    (fun f : S[X] ↦ f ≠ 0 ∧ f.eval₂ S.toSubring.subtype (germMap C x) = 0)
    Polynomial.natDegree hrel
  let d := p.natDegree
  have hd : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd₀
    have hCq := Polynomial.eq_C_of_natDegree_eq_zero hd₀
    have hp₀ := hp.prop.2
    rw [hCq, Polynomial.eval₂_C] at hp₀
    have hcoeff : p.coeff 0 = 0 := Subtype.ext hp₀
    exact hp.prop.1 (by rw [hCq, hcoeff, map_zero])
  let φ := germReadingSubringToSubalgebra C S
  have hφ : Function.Surjective φ := fun a ↦ (hlift a).imp fun f hf ↦ Subtype.ext hf
  obtain ⟨q, hqmonic, hqdeg, hqeval⟩ :=
    exists_monic_germRelation C hC S hφ x hpos p hp.prop.1 hp.prop.2
  obtain ⟨F, hFmap, hFdegree, hFmonic⟩ :=
    lifts_and_natDegree_eq_and_monic (mem_lifts_of_surjective hφ q) hqmonic
  have hFdeg : F.natDegree = d := hFdegree.trans hqdeg
  have hFtop : F.coeff d = 1 := by rw [← hFdeg]; exact hFmonic
  have hF : germMap C (F.eval₂ (germReadingSubring C S.toSubring).subtype x) = 0 := by
    rw [germMap_eval₂_germReadingSubring, hFmap, hqeval]
  obtain ⟨η, hη, hηfix, hηzero⟩ := exists_germReading_eq_zero_of_germMap_eq_zero C hC _ hF
  let y : U := (F.coeff (d - 1) : U) + d • x
  have hy (t : Surreal.{u}) (ht : 0 < t) (htη : t < η) (htfix : cosetRep H t = t) :
      germReading C t (y : Surreal) = 0 := by
    obtain ⟨f, hfdegree, hfeval, hfcoeff, hfnext⟩ :=
      exists_eval₂_eq_germReading C S.toSubring x hpos ht.le htfix d F hFdeg.le
    have hfcoeff₀ : f.coeff d = 0 := by
      apply Subtype.ext
      rw [hfcoeff, hFtop]
      exact germReading_residueSubfield_eq_zero C ht htfix (1 : K)
    have hf₀ : f = 0 := by
      by_contra hne
      have hdeg : f.natDegree = d :=
        le_antisymm hfdegree (hp.le ⟨hne, hfeval.trans (hηzero t htη htfix)⟩)
      apply Polynomial.leadingCoeff_ne_zero.mpr hne
      rw [Polynomial.leadingCoeff, hdeg, hfcoeff₀]
    have hnext := hfnext ht hd hFtop
    rw [hf₀, Polynomial.coeff_zero] at hnext
    let T : U →+ G :=
      { toFun := fun z ↦ germReading C t z
        map_zero' := germReading_zero_input C t
        map_add' := fun z w ↦ germReading_add C t z w }
    change T ((F.coeff (d - 1) : U) + d • x) = 0
    rw [map_add, map_nsmul]
    exact hnext.symm
  obtain ⟨k, hk⟩ := exists_germ_eq_residueSubfield_of_germReading_eq_zero C y hη hηfix hy
  have hkS : germMap C y ∈ S := by
    rw [hk, ← algebraMap_germ]
    exact S.algebraMap_mem _
  have hmul : (d : G) * germMap C x ∈ S := by
    simpa only [y, map_add, map_mul, map_natCast, add_sub_cancel_left, nsmul_eq_mul] using
      S.sub_mem hkS (germMap_germReadingSubring_mem C S (F.coeff (d - 1)))
  have hd₀ : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hdinv : residueSubfieldGerm C (d : K)⁻¹ ∈ S := by
    rw [← algebraMap_germ]
    exact S.algebraMap_mem _
  apply hx
  have hmem := S.mul_mem hdinv hmul
  rw [← map_natCast (residueSubfieldGerm C) d, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hd₀, map_one, one_mul] at hmem
  exact hmem

private abbrev GermPrecision := {t : Surreal.{u} // 0 ≤ t ∧ cosetRep H t = t}

private def addGermPrecision (s t : GermPrecision C) : GermPrecision C :=
  ⟨s + t, add_nonneg s.2.1 t.2.1, by rw [cosetRep_add, s.2.2, t.2.2]⟩

private theorem scalar_germReadingLift (E : Subalgebra K G) (k : K) :
    ∃ f : germReadingSubring C E.toSubring, germMap C (f : U) = algebraMap K G k := by
  let x : U := ⟨k, ((mem_residueSubfield_iff C).mp k.2).1⟩
  have he : germMap C x = algebraMap K G k := by
    rw [algebraMap_germ, residueSubfieldGerm_eq]
  refine ⟨⟨x, (mem_germReadingSubring C).mpr ?_⟩, he⟩
  intro t ht hfix
  rcases eq_or_lt_of_le ht with rfl | ht
  · rw [germReading_zero, he]
    exact E.algebraMap_mem k
  · change germReading C t (k : Surreal) ∈ E
    rw [germReading_residueSubfield_eq_zero C ht hfix k]
    exact E.zero_mem

/-- Read the given representatives in order. Their germs lie in the polynomial algebra
on those readings which the preceding readings cannot express. -/
theorem independent_germ_readings {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    (hC : C ≠ ⊤) (z : ι → U) :
    ∃ T : Set G, T ⊆ {a | ∃ j t, 0 ≤ t ∧ cosetRep H t = t ∧ germReading C t (z j) = a} ∧
      AlgebraicIndependent K ((↑) : T → G) ∧ ∀ j, germMap C (z j) ∈ Algebra.adjoin K T := by
  let v (j : ι) (t : GermPrecision C) := germReading C t (z j)
  have hrigid (j : ι) (t : GermPrecision C) :
      let E := Algebra.adjoin K (Algebra.earlierReadings v j t)
      v j t ∉ E → Transcendental E (v j t) := by
    intro E hnew
    let rep (k : ι) (s : GermPrecision C) : U :=
      ⟨roundAt C s (z k), roundAt_mem_residueRepresentatives C s (z k)⟩
    have read_rep (k : ι) (s : GermPrecision C) : v k s = germMap C (rep k s) :=
      germReading_eq C s (z k)
    have earlier {k : ι} {s : GermPrecision C} (hs : k < j ∨ k = j ∧ t < s) :
        v k s ∈ E := Algebra.subset_adjoin (Algebra.mem_earlierReadings.mpr ⟨k, s, hs, rfl⟩)
    let φ := (germMap C).comp (germReadingSubring C E.toSubring).subtype
    let B : Subalgebra K G :=
      { toSubsemiring := φ.range.toSubsemiring
        algebraMap_mem' := scalar_germReadingLift C E }
    have lifts : E ≤ B := by
      apply Algebra.adjoin_le
      intro a ha
      obtain ⟨k, s, hs, rfl⟩ := Algebra.mem_earlierReadings.mp ha
      refine ⟨⟨rep k s, (mem_germReadingSubring C).mpr ?_⟩, (read_rep k s).symm⟩
      intro r hr hfix
      change germReading C r (roundAt C s (z k)) ∈ E
      rw [germReading_roundAt C s hr]
      apply earlier (s := addGermPrecision C s ⟨r, hr, hfix⟩)
      exact hs.imp_right fun ⟨he, hlt⟩ ↦ ⟨he, hlt.trans_le (le_add_of_nonneg_right hr)⟩
    rw [read_rep] at hnew ⊢
    apply transcendental_iff_injective.mpr
    change Function.Injective (Polynomial.eval₂ E.toSubring.subtype (germMap C (rep j t)))
    apply injective_eval₂_germMap_of_pos_readings C hC E (fun a ↦ lifts a.2) (rep j t) hnew
    intro r hr hfix
    change germReading C r (roundAt C t (z j)) ∈ E
    rw [germReading_roundAt C t hr.le]
    exact earlier (s := addGermPrecision C t ⟨r, hr.le, hfix⟩)
      (Or.inr ⟨rfl, lt_add_of_pos_right _ hr⟩)
  have hfirst (E : Subalgebra K G) (j : ι) (h : ∃ t, v j t ∉ E) :
      ∃ t, v j t ∉ E ∧ ∀ s, t < s → v j s ∈ E := by
    obtain ⟨t, ht⟩ := h
    obtain ⟨s, ⟨hs, hfix, hbad⟩, hmax⟩ := exists_greatest_germReading_notMem C (z j)
      (0 ≤ ·) E E.zero_mem ⟨t, t.2.1, t.2.2, ht⟩
    exact ⟨⟨s, hs, hfix⟩, hbad, fun r hr ↦ by_contra fun h ↦
      hr.not_ge (hmax r r.2.1 r.2.2 h)⟩
  obtain ⟨hind, hall⟩ :=
    Algebra.independent_ordered_readings v (algebraMap K G).injective hrigid hfirst
  refine ⟨_, ?_, hind, fun j ↦ ?_⟩
  · intro a ha
    obtain ⟨j, t, _, rfl⟩ := Algebra.mem_selectedReadings.mp ha
    exact ⟨j, t, t.2.1, t.2.2, rfl⟩
  · simpa only [v, germReading_zero] using hall j ⟨0, le_rfl, cosetRep_zero H⟩

/-- The germs in a given finite tuple are polynomials in finitely many independent readings. -/
theorem finite_germ_coordinates (hC : C ≠ ⊤) {n : ℕ} (z : Fin n → G) :
    ∃ T : Finset G, AlgebraicIndependent K ((↑) : ↥T → G) ∧
      ∀ j, z j ∈ Algebra.adjoin K (T : Set G) := by
  choose x hx using fun j ↦ germMap_surjective C (z j)
  obtain ⟨T, _, hind, hall⟩ := independent_germ_readings C hC x
  obtain ⟨s, _, hs, hmem⟩ := Algebra.finite_independent_coordinates hind z
    (fun j ↦ hx j ▸ hall j)
  exact ⟨s, hs, hmem⟩

end Surreal
