/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Scale.Rounding
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Surreal germs at a convex subring

Quotient the ring of residue representatives by the ideal of those divisible by a monomial outside
the convex subring. The germ at an exponent is obtained by dividing by its monomial and taking the
simplest representative modulo the infinitesimals before passing to the quotient.
-/

universe u

open scoped Pointwise

public noncomputable section

namespace Surreal

variable (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex]

/-- Representatives divisible by a Conway monomial outside the convex subring, with zero
included also when there are no such monomials. -/
def germIdeal : Ideal (residueRepresentatives C) where
  carrier := {x | x = 0 ∨
    ∃ s : Surreal, ω^ s ∉ C ∧ ∃ y : residueRepresentatives C, (x : Surreal) = ω^ s * y}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro x z (rfl | ⟨s, hs, x', hx⟩) (rfl | ⟨t, ht, z', hz⟩)
    · exact Or.inl (zero_add _)
    · rw [zero_add]
      exact Or.inr ⟨t, ht, z', hz⟩
    · rw [add_zero]
      exact Or.inr ⟨s, hs, x', hx⟩
    · let r := min s t
      have hr : ω^ r ∉ C := by
        obtain h | h := le_total s t
        · simpa only [r, min_eq_left h] using hs
        · simpa only [r, min_eq_right h] using ht
      have hxU := wpow_mul_mem_residueRepresentatives C (sub_nonneg.mpr (min_le_left s t)) x'.2
      have hzU := wpow_mul_mem_residueRepresentatives C (sub_nonneg.mpr (min_le_right s t)) z'.2
      have hs' : ω^ r * ω^ (s - r) = ω^ s := by rw [← wpow_add, add_comm r, sub_add_cancel]
      have ht' : ω^ r * ω^ (t - r) = ω^ t := by rw [← wpow_add, add_comm r, sub_add_cancel]
      refine Or.inr ⟨r, hr, ⟨_, (residueRepresentatives C).add_mem hxU hzU⟩, ?_⟩
      change (x : Surreal) + z = ω^ r * (ω^ (s - r) * x' + ω^ (t - r) * z')
      simp only [hx, hz, mul_add, ← mul_assoc, hs', ht']
  smul_mem' := by
    rintro a x (rfl | ⟨s, hs, y, hxy⟩)
    · exact Or.inl (smul_zero _)
    · refine Or.inr ⟨s, hs, a * y, ?_⟩
      change (a : Surreal) * x = ω^ s * ((a : Surreal) * y)
      rw [hxy, mul_left_comm]

/-- A representative lies in the germ ideal exactly when it is zero or is divisible by a
Conway monomial outside the convex subring, with quotient in the representative ring. -/
theorem mem_germIdeal_iff {x : residueRepresentatives C} :
    x ∈ germIdeal C ↔ x = 0 ∨
      ∃ s : Surreal, ω^ s ∉ C ∧ ∃ y : residueRepresentatives C, (x : Surreal) = ω^ s * y :=
  Iff.rfl

/-- Every element of the germ ideal is fixed by the simplest projection modulo the
convex subring. -/
theorem germIdeal_le_simplestRepresentativesIdeal :
    germIdeal C ≤ simplestRepresentativesIdeal C C le_rfl := by
  intro x hx
  rcases (mem_germIdeal_iff C).mp hx with rfl | ⟨s, hs, y, hy⟩
  · exact Ideal.zero_mem _
  · apply (mem_simplestRepresentativesIdeal_iff C C le_rfl).mpr
    rw [hy]
    exact cosetRep_mul_eq_of_mem_residueRepresentatives C C le_rfl
      (cosetRep_wpow_eq_of_notMem (H := C.toAddSubgroup) hs) y.2

/-- Germs of the simplest representatives modulo the infinitesimals. -/
abbrev Germ := residueRepresentatives C ⧸ germIdeal C

/-- The projection from a representative to its germ. -/
def germMap : residueRepresentatives C →+* Germ C :=
  Ideal.Quotient.mk (germIdeal C)

/-- Every germ has a representative. -/
theorem germMap_surjective : Function.Surjective (germMap C) :=
  Ideal.Quotient.mk_surjective

/-- Exactly the elements of the germ ideal have zero germ. -/
theorem germMap_eq_zero_iff {x : residueRepresentatives C} :
    germMap C x = 0 ↔ x ∈ germIdeal C :=
  Ideal.Quotient.eq_zero_iff_mem

/-- Two representatives have the same germ exactly when their difference lies in the germ
ideal. -/
theorem germMap_eq_germMap_iff (x y : residueRepresentatives C) :
    germMap C x = germMap C y ↔ x - y ∈ germIdeal C :=
  Ideal.Quotient.mk_eq_mk_iff_sub_mem x y

private def residueSubfieldInclusion : residueSubfield C →+* residueRepresentatives C where
  toFun x := ⟨x, ((mem_residueSubfield_iff C).mp x.2).1⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- The map from the residue subfield to the ring of germs. -/
def residueSubfieldGerm : residueSubfield C →+* Germ C :=
  (germMap C).comp (residueSubfieldInclusion C)

/-- The germ of a residue scalar is its germ as an element of the representative ring. -/
theorem residueSubfieldGerm_eq (x : residueSubfield C) :
    residueSubfieldGerm C x =
      germMap C ⟨x, ((mem_residueSubfield_iff C).mp x.2).1⟩ :=
  (rfl)

/-- Taking germs embeds the residue subfield. -/
theorem residueSubfieldGerm_injective : Function.Injective (residueSubfieldGerm C) := by
  intro x y h
  rw [residueSubfieldGerm_eq, residueSubfieldGerm_eq, germMap_eq_germMap_iff] at h
  have hfix := (mem_simplestRepresentativesIdeal_iff C C le_rfl).mp
    (germIdeal_le_simplestRepresentativesIdeal C h)
  have hmem : (x : Surreal) - y ∈ C.toAddSubgroup :=
    C.sub_mem ((mem_residueSubfield_iff C).mp x.2).2 ((mem_residueSubfield_iff C).mp y.2).2
  exact Subtype.ext (sub_eq_zero.mp (hfix.symm.trans (cosetRep_eq_zero_iff.mpr hmem)))

instance germ_nontrivial : Nontrivial (Germ C) :=
  (residueSubfieldGerm_injective C).nontrivial

instance germAlgebra : Algebra (residueSubfield C) (Germ C) :=
  (residueSubfieldGerm C).toAlgebra

/-- The algebra map embeds the residue subfield by taking germs. -/
theorem algebraMap_germ :
    algebraMap (residueSubfield C) (Germ C) = residueSubfieldGerm C :=
  RingHom.algebraMap_toAlgebra _

/-- The germ of a surreal after division by a monomial and projection modulo the infinitesimals. -/
def germReading (t x : Surreal.{u}) : Germ C :=
  germMap C ⟨roundAt C t x, roundAt_mem_residueRepresentatives C t x⟩

/-- A germ at a scale is the germ of the rounded representative at that scale. -/
theorem germReading_eq (t x : Surreal.{u}) :
    germReading C t x = germMap C ⟨roundAt C t x, roundAt_mem_residueRepresentatives C t x⟩ :=
  (rfl)

/-- The germ at zero precision of a representative is its germ. -/
theorem germReading_zero (x : residueRepresentatives C) :
    germReading C 0 (x : Surreal) = germMap C x := by
  rw [germReading_eq]
  apply congrArg (germMap C)
  exact Subtype.ext ((roundAt_zero_precision C x).trans ((mem_residueRepresentatives_iff C).mp x.2))

/-- The germ at any precision of zero is zero. -/
theorem germReading_zero_input (t : Surreal.{u}) : germReading C t 0 = 0 := by
  rw [germReading_eq, ← (germMap C).map_zero]
  apply congrArg (germMap C)
  apply Subtype.ext
  change roundAt C t 0 = 0
  exact (roundAt_eq C t 0).trans (by rw [zero_div, cosetRep_zero])

/-- Taking germs at a fixed precision is additive. -/
theorem germReading_add (t x y : Surreal.{u}) :
    germReading C t (x + y) = germReading C t x + germReading C t y := by
  rw [germReading_eq, germReading_eq, germReading_eq, ← map_add]
  exact congrArg (germMap C) (Subtype.ext (roundAt_add C t x y))

/-- Taking germs at a fixed precision commutes with subtraction. -/
theorem germReading_sub (t x y : Surreal.{u}) :
    germReading C t (x - y) = germReading C t x - germReading C t y := by
  rw [germReading_eq, germReading_eq, germReading_eq, ← map_sub]
  exact congrArg (germMap C) (Subtype.ext (roundAt_sub C t x y))

/-- A germ reading of a rescaled representative adds the two precisions. -/
theorem germReading_roundAt (s : Surreal.{u}) {t : Surreal.{u}} (ht : 0 ≤ t) (x : Surreal.{u}) :
    germReading C t (roundAt C s x) = germReading C (s + t) x := by
  rw [germReading_eq, germReading_eq]
  exact congrArg (germMap C) (Subtype.ext (roundAt_roundAt C s ht x))

/-- The simplest representative at a scale whose monomial lies outside the convex subring
has zero germ. -/
theorem cosetRep_wpow_smul_mem_germIdeal {s : Surreal.{u}} (hs : 0 ≤ s)
    (hsC : ω^ s ∉ C) (x : Surreal.{u}) :
    (⟨cosetRep (ω^ s • infinitesimals C) x,
      cosetRep_wpow_smul_mem_residueRepresentatives C hs x⟩ : residueRepresentatives C) ∈
      germIdeal C := by
  apply (mem_germIdeal_iff C).mpr
  refine Or.inr ⟨s, hsC, ⟨_, roundAt_mem_residueRepresentatives C s x⟩, ?_⟩
  change cosetRep (ω^ s • infinitesimals C) x = ω^ s * roundAt C s x
  rw [roundAt_eq, cosetRep_wpow_smul]

/-- At a greater precision the germ is unchanged by projection modulo the smaller scaled
infinitesimals. -/
theorem germReading_scaleCosetRep_of_le {s r : Surreal.{u}} (hsr : s ≤ r) (x : Surreal.{u}) :
    germReading C r (cosetRep (ω^ s • infinitesimals C) x) =
      germReading C r x := by
  rw [germReading_eq, germReading_eq]
  exact congrArg (germMap C) (Subtype.ext (roundAt_scaleCosetRep_of_le C hsr x))

/-- A simplest representative at a larger precision has zero germ at a smaller precision when
the monomial of the difference of precisions lies outside the convex subring. -/
theorem germReading_scaleCosetRep_eq_zero_of_notMem {s r : Surreal.{u}} (hrs : r ≤ s)
    (hsr : ω^ (s - r) ∉ C) (x : Surreal.{u}) :
    germReading C r (cosetRep (ω^ s • infinitesimals C) x) = 0 := by
  rw [germReading_eq, germMap_eq_zero_iff, mem_germIdeal_iff]
  exact Or.inr ⟨s - r, hsr, ⟨_, roundAt_mem_residueRepresentatives C s x⟩,
    roundAt_scaleCosetRep_of_ge C hrs x⟩

/-- A residue scalar has zero germ at each positive precision represented by a simplest
exponent modulo the exponents of unit monomials. -/
theorem germReading_residueSubfield_eq_zero {t : Surreal.{u}} (ht : 0 < t)
    (htfix : cosetRep (unitExponentSubgroup C) t = t) (k : residueSubfield C) :
    germReading C t (k : Surreal) = 0 := by
  by_cases hk : (k : Surreal) = 0
  · rw [hk, germReading_zero_input]
  have hk₀ : precisionLevel C (k : Surreal) ≤ 0 := le_of_not_gt fun h ↦
    ((notMem_subring_iff_precisionLevel_pos C hk).mpr h) ((mem_residueSubfield_iff C).mp k.2).2
  have hdiv := (div_wpow_mem_infinitesimals_iff C hk htfix).mpr (hk₀.trans_lt ht)
  rw [germReading_eq, ← (germMap C).map_zero]
  apply congrArg (germMap C)
  apply Subtype.ext
  exact (roundAt_eq C t k).trans (cosetRep_eq_zero_iff.mpr hdiv)

/-- The leading reading of a nonzero representative has nonzero germ. -/
theorem germReading_precisionLevel_ne_zero (x : residueRepresentatives C)
    (hx : (x : Surreal) ≠ 0) : germReading C (precisionLevel C (x : Surreal)) x ≠ 0 := by
  let t := precisionLevel C (x : Surreal)
  obtain ⟨hzK, hz₀⟩ := roundAt_precisionLevel_mem_residueSubfield_and_ne_zero C x hx
  let k : residueSubfield C := ⟨roundAt C t x, hzK⟩
  have hk₀ : k ≠ 0 := fun h ↦ hz₀ (congrArg Subtype.val h)
  have hg := (residueSubfieldGerm_injective C).ne hk₀
  rw [map_zero, residueSubfieldGerm_eq] at hg
  rw [germReading_eq]
  exact hg

/-- Larger simplest exponents with visible readings select representatives of strictly
smaller birthday. -/
theorem birthday_scaleCosetRep_lt_of_lt_of_germReading_ne_zero (x : Surreal.{u})
    {s t : Surreal.{u}} (hst : s < t)
    (hs : cosetRep (unitExponentSubgroup C) s = s) (ht : cosetRep (unitExponentSubgroup C) t = t)
    (h : germReading C s x ≠ 0) :
    (cosetRep (ω^ t • infinitesimals C) x).birthday <
      (cosetRep (ω^ s • infinitesimals C) x).birthday := by
  have hdiff : ω^ (t - s) ∉ C := by
    apply (wpow_notMem_subring_iff C).mpr
    rw [cosetRep_sub, ht, hs]
    exact sub_pos.mpr hst
  have hne : cosetRep (ω^ t • infinitesimals C) x ≠
      cosetRep (ω^ s • infinitesimals C) x := by
    intro heq
    have hz := germReading_scaleCosetRep_eq_zero_of_notMem C hst.le hdiff x
    rw [heq, germReading_scaleCosetRep_of_le C le_rfl] at hz
    exact h hz
  have hle := smul_addSubgroup_mono (infinitesimals C)
    (wpow_pos s) (wpow_le_wpow.mpr hst.le)
  exact birthday_cosetRep_lt_of_ne (hle (sub_cosetRep_mem _ x)) hne

/-- Any nonempty family of simplest exponents with readings outside a set containing zero
has a greatest exponent. -/
theorem exists_greatest_germReading_notMem (x : Surreal.{u}) (P : Surreal.{u} → Prop)
    (S : Set (Germ C)) (hzero : 0 ∈ S)
    (h : ∃ t, P t ∧ cosetRep (unitExponentSubgroup C) t = t ∧ germReading C t x ∉ S) :
    ∃ t, (P t ∧ cosetRep (unitExponentSubgroup C) t = t ∧ germReading C t x ∉ S) ∧
      ∀ s, P s → cosetRep (unitExponentSubgroup C) s = s → germReading C s x ∉ S → s ≤ t := by
  obtain ⟨t, ht⟩ := exists_minimalFor_of_wellFoundedLT
    (fun t ↦ P t ∧ cosetRep (unitExponentSubgroup C) t = t ∧ germReading C t x ∉ S)
    (fun t ↦ (cosetRep (ω^ t • infinitesimals C) x).birthday) h
  refine ⟨t, ht.prop, fun s hs hsfix hsread ↦ le_of_not_gt fun hlt ↦ ?_⟩
  have htread : germReading C t x ≠ 0 := fun heq ↦ ht.prop.2.2 (heq.symm ▸ hzero)
  exact (birthday_scaleCosetRep_lt_of_lt_of_germReading_ne_zero C x hlt
    ht.prop.2.1 hsfix htread).not_ge (ht.le ⟨hs, hsfix, hsread⟩)

/-- If the readings vanish throughout a positive interval of simplest exponents, the germ
belongs to the embedded residue subfield. -/
theorem exists_germ_eq_residueSubfield_of_germReading_eq_zero (x : residueRepresentatives C)
    {η : Surreal.{u}} (hη : 0 < η) (hηfix : cosetRep (unitExponentSubgroup C) η = η)
    (hread : ∀ t, 0 < t → t < η → cosetRep (unitExponentSubgroup C) t = t →
      germReading C t (x : Surreal) = 0) :
    ∃ k : residueSubfield C, germMap C x = residueSubfieldGerm C k := by
  let p := cosetRep (ω^ η • infinitesimals C) (x : Surreal)
  let pU : residueRepresentatives C :=
    ⟨p, cosetRep_wpow_smul_mem_residueRepresentatives C hη.le x⟩
  let y := x - pU
  have hηC : ω^ η ∉ C := (wpow_notMem_subring_iff C).mpr (hηfix.symm ▸ hη)
  have hp0 : germMap C pU = 0 :=
    (germMap_eq_zero_iff C).mpr (cosetRep_wpow_smul_mem_germIdeal C hη.le hηC x)
  have hgy : germMap C y = germMap C x := by
    change germMap C (x - pU) = germMap C x
    rw [map_sub, hp0, sub_zero]
  by_cases hy : (y : Surreal) = 0
  · refine ⟨0, ?_⟩
    rw [← hgy, show y = 0 from Subtype.ext hy, map_zero, map_zero]
  let t := precisionLevel C (y : Surreal)
  have htfix := cosetRep_precisionLevel C (y : Surreal)
  have htη : t < η := (mem_wpow_smul_infinitesimals_iff C hy hηfix).mp
    (sub_cosetRep_mem _ (x : Surreal))
  have ht₀ : t = 0 := by
    have hnonneg := precisionLevel_nonneg_of_mem_residueRepresentatives C y.2 hy
    refine hnonneg.antisymm' (le_of_not_gt fun ht ↦ ?_)
    have hsub : ω^ (η - t) ∉ C := by
      apply (wpow_notMem_subring_iff C).mpr
      rw [cosetRep_sub, hηfix, htfix]
      exact sub_pos.mpr htη
    have hgy₀ := germReading_precisionLevel_ne_zero C y hy
    apply hgy₀
    change germReading C t ((x : Surreal) - p) = 0
    rw [germReading_sub, hread t ht htη htfix,
      germReading_scaleCosetRep_eq_zero_of_notMem C htη.le hsub, sub_zero]
  have hyC : (y : Surreal) ∈ C := by
    have hunit := (div_wpow_mem_subring_and_inv_iff C hy htfix).mpr rfl
    simpa only [show precisionLevel C (y : Surreal) = 0 from ht₀, wpow_zero, div_one] using hunit.1
  refine ⟨⟨y, (mem_residueSubfield_iff C).mpr ⟨y.2, hyC⟩⟩, ?_⟩
  rw [residueSubfieldGerm_eq]
  exact hgy.symm

/-- A nonzero germ has a nonzero scalar reading below every positive simplest exponent. -/
theorem exists_germReading_eq_residueSubfield_of_germMap_ne_zero (x : residueRepresentatives C)
    {η : Surreal.{u}} (hη : 0 < η) (hηfix : cosetRep (unitExponentSubgroup C) η = η)
    (hx : germMap C x ≠ 0) :
    ∃ (t : Surreal.{u}) (k : residueSubfield C), 0 ≤ t ∧ t < η ∧
      cosetRep (unitExponentSubgroup C) t = t ∧ k ≠ 0 ∧
      germReading C t (x : Surreal) = residueSubfieldGerm C k := by
  let p := cosetRep (ω^ η • infinitesimals C) (x : Surreal)
  let pU : residueRepresentatives C :=
    ⟨p, cosetRep_wpow_smul_mem_residueRepresentatives C hη.le x⟩
  let y := x - pU
  have hηC : ω^ η ∉ C := (wpow_notMem_subring_iff C).mpr (hηfix.symm ▸ hη)
  have hp0 : germMap C pU = 0 :=
    (germMap_eq_zero_iff C).mpr (cosetRep_wpow_smul_mem_germIdeal C hη.le hηC x)
  have hy : (y : Surreal) ≠ 0 := by
    intro hy0
    apply hx
    have heq : x = pU := sub_eq_zero.mp (Subtype.ext hy0 : y = 0)
    exact heq.symm ▸ hp0
  let t := precisionLevel C (y : Surreal)
  have htfix := cosetRep_precisionLevel C (y : Surreal)
  have htη : t < η := (mem_wpow_smul_infinitesimals_iff C hy hηfix).mp
    (sub_cosetRep_mem _ (x : Surreal))
  have hdiff : ω^ (η - t) ∉ C := by
    apply (wpow_notMem_subring_iff C).mpr
    rw [cosetRep_sub, hηfix, htfix]
    exact sub_pos.mpr htη
  obtain ⟨hk, hk₀⟩ := roundAt_precisionLevel_mem_residueSubfield_and_ne_zero C y hy
  refine ⟨t, ⟨roundAt C t y, hk⟩, precisionLevel_nonneg_of_mem_residueRepresentatives C y.2 hy,
    htη, htfix, fun h ↦ hk₀ (congrArg Subtype.val h), ?_⟩
  calc
    germReading C t (x : Surreal) = germReading C t (y : Surreal) := by
      change germReading C t (x : Surreal) = germReading C t ((x : Surreal) - p)
      rw [germReading_sub, germReading_scaleCosetRep_eq_zero_of_notMem C htη.le hdiff, sub_zero]
    _ = _ := by rw [germReading_eq, residueSubfieldGerm_eq]

/-- A proper convex subring has a positive simplest exponent modulo the unit exponents. -/
theorem exists_positive_precision (hC : C ≠ ⊤) :
    ∃ t : Surreal.{u}, 0 < t ∧ cosetRep (unitExponentSubgroup C) t = t := by
  have hnonempty : ∃ x : Surreal.{u}, x ∉ C := by
    by_contra! h
    exact hC (top_unique fun x _ ↦ h x)
  obtain ⟨x, hx⟩ := hnonempty
  have hx₀ : x ≠ 0 := fun h ↦ hx (h.symm ▸ C.zero_mem)
  exact ⟨precisionLevel C x, (notMem_subring_iff_precisionLevel_pos C hx₀).mp hx,
    cosetRep_precisionLevel C x⟩

/-- A representative with zero germ has zero readings below some positive simplest exponent,
including at zero precision. -/
theorem exists_germReading_eq_zero_of_germMap_eq_zero (hC : C ≠ ⊤)
    (x : residueRepresentatives C) (hx : germMap C x = 0) :
    ∃ η : Surreal.{u}, 0 < η ∧ cosetRep (unitExponentSubgroup C) η = η ∧
      ∀ t, t < η → cosetRep (unitExponentSubgroup C) t = t →
        germReading C t (x : Surreal) = 0 := by
  rcases (mem_germIdeal_iff C).mp ((germMap_eq_zero_iff C).mp hx) with
    rfl | ⟨s, hs, y, hy⟩
  · obtain ⟨η, hη, hηfix⟩ := exists_positive_precision C hC
    exact ⟨η, hη, hηfix, fun t _ _ ↦ germReading_zero_input C t⟩
  let H := unitExponentSubgroup C
  refine ⟨cosetRep H s, (wpow_notMem_subring_iff C).mp hs, cosetRep_cosetRep H s, ?_⟩
  intro t ht htfix
  have hdiff : ω^ (s - t) ∉ C := by
    apply (wpow_notMem_subring_iff C).mpr
    rw [cosetRep_sub, htfix]
    exact sub_pos.mpr ht
  have hfix := cosetRep_mul_eq_of_mem_residueRepresentatives C C le_rfl
    (cosetRep_wpow_eq_of_notMem (H := C.toAddSubgroup) hdiff) y.2
  have hU : ω^ (s - t) * (y : Surreal) ∈ residueRepresentatives C := by
    rw [← hfix]
    exact cosetRep_mem_residueRepresentatives_of_le C C le_rfl _
  have hdiv : (x : Surreal) / ω^ t = ω^ (s - t) * (y : Surreal) := by
    rw [hy, wpow_sub, div_mul_eq_mul_div]
  have hr : roundAt C t x = ω^ (s - t) * (y : Surreal) := by
    rw [roundAt_eq, hdiv, (mem_residueRepresentatives_iff C).mp hU]
  rw [germReading_eq, germMap_eq_zero_iff, mem_germIdeal_iff]
  exact Or.inr ⟨s - t, hdiff, y, hr⟩

end Surreal
