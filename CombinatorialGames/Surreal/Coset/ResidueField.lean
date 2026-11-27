/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Coset.Basic
public import CombinatorialGames.Surreal.Omnific.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.RingTheory.Ideal.Defs

import CombinatorialGames.Surreal.Coset.Arithmetic
import CombinatorialGames.Surreal.Omnific.Coset
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Residue representatives of convex subrings

The infinitesimals of a convex subring form a convex additive subgroup. Its simplest coset
representatives form a subring, and those lying in the convex subring form a residue subfield.
-/

universe u

public noncomputable section

namespace Surreal

variable (C : Subring Surreal.{u})

variable [C.toAddSubgroup.IsConvex]

private theorem mem_subring_of_abs_le {x y : Surreal.{u}} (hy : y ∈ C) (h : |x| ≤ |y|) : x ∈ C :=
  abs_mem_iff.mp <| C.toAddSubgroup.mem_of_nonneg_of_le (abs_nonneg x) h (abs_mem_iff.mpr hy)

private def convexValuationSubring : ValuationSubring Surreal.{u} :=
  ValuationSubring.ofSubring C fun x ↦ by
    by_cases hx : |x| ≤ 1
    · exact Or.inl (mem_subring_of_abs_le C C.one_mem (by simpa only [abs_one] using hx))
    · right
      have hpos := zero_lt_one.trans (lt_of_not_ge hx)
      apply mem_subring_of_abs_le C C.one_mem
      rw [abs_inv, abs_one]
      exact (inv_le_one₀ hpos).2 (le_of_not_ge hx)

/-- The additive subgroup of elements of the maximal ideal of a convex subring. -/
def infinitesimals : AddSubgroup Surreal.{u} :=
  (convexValuationSubring C).nonunits.toAddSubgroup

/-- An element is infinitesimal relative to the subring exactly when it is zero or its inverse
lies outside the subring. -/
theorem mem_infinitesimals_iff {x : Surreal.{u}} :
    x ∈ infinitesimals C ↔ x = 0 ∨ x⁻¹ ∉ C := by
  rw [infinitesimals, NonUnitalSubring.mem_toAddSubgroup, ValuationSubring.mem_nonunits_iff_or]
  rw [convexValuationSubring, ValuationSubring.mem_ofSubring]

/-- The complement of the infinitesimals consists of nonzero elements with inverse in the
subring. -/
theorem notMem_infinitesimals_iff {x : Surreal.{u}} :
    x ∉ infinitesimals C ↔ x ≠ 0 ∧ x⁻¹ ∈ C := by
  rw [mem_infinitesimals_iff, not_or, not_not]

/-- Infinitesimals have magnitude smaller than every inverse of a positive element of the
subring. -/
theorem mem_infinitesimals_iff_forall {x : Surreal.{u}} :
    x ∈ infinitesimals C ↔ ∀ c ∈ C, 0 < c → |x| < c⁻¹ := by
  rw [mem_infinitesimals_iff]
  constructor
  · rintro (rfl | hx) c hc hc₀
    · simpa only [abs_zero] using inv_pos.mpr hc₀
    · by_contra! h
      apply hx
      apply mem_subring_of_abs_le C hc
      rw [abs_inv, abs_of_pos hc₀]
      simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hc₀) h
  · intro h
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      intro hxC
      have hc := h |x⁻¹| (abs_mem_iff.mpr hxC)
        (abs_pos.mpr (inv_ne_zero hx))
      rw [abs_inv, inv_inv] at hc
      exact hc.false

/-- The subgroup of infinitesimals relative to a convex subring is convex. -/
instance infinitesimals_isConvex : (infinitesimals C).IsConvex where
  ordConnected := by
    constructor
    intro a ha b hb x hx
    change a ∈ infinitesimals C at ha
    change b ∈ infinitesimals C at hb
    change x ∈ infinitesimals C
    rw [mem_infinitesimals_iff_forall] at ha hb ⊢
    intro c hc hc₀
    exact (abs_le_max_abs_abs hx.1 hx.2).trans_lt (max_lt (ha c hc hc₀) (hb c hc hc₀))

/-- Every infinitesimal relative to a convex subring belongs to the subring. -/
theorem infinitesimals_le : infinitesimals C ≤ C.toAddSubgroup := by
  intro x hx
  have h := (convexValuationSubring C).nonunits_subset hx
  exact (ValuationSubring.mem_ofSubring ..).mp h

/-- Multiplication by any element of the convex subring preserves its infinitesimals. -/
theorem mul_mem_infinitesimals_of_mem {x y : Surreal.{u}} (hx : x ∈ C)
    (hy : y ∈ infinitesimals C) : x * y ∈ infinitesimals C := by
  let A := convexValuationSubring C
  have hvalx : A.valuation x ≤ 1 :=
    (A.valuation_le_one_iff x).mpr ((ValuationSubring.mem_ofSubring ..).mpr hx)
  have hvaly : A.valuation y < 1 := A.mem_nonunits_iff.mp hy
  apply A.mem_nonunits_iff.mpr
  rw [map_mul]
  exact (mul_le_of_le_one_left zero_le hvalx).trans_lt hvaly

private theorem cosetRep_infinitesimals_one :
    cosetRep (infinitesimals C) 1 = 1 := by
  rw [← mk_one]
  apply cosetRep_mk_eq_of_forall_moves
  intro p a ha
  cases p with
  | left =>
    simp only [IGame.moves_left_one, Set.mem_singleton_iff] at ha
    subst a
    simp [notMem_infinitesimals_iff, C.one_mem]
  | right => simp at ha

private theorem mul_notMem_infinitesimals {x y : Surreal.{u}} (hx : x ∉ infinitesimals C)
    (hy : y ∉ infinitesimals C) : x * y ∉ infinitesimals C := by
  rw [notMem_infinitesimals_iff] at hx hy ⊢
  refine ⟨mul_ne_zero hx.1 hy.1, ?_⟩
  simpa only [mul_inv_rev] using C.mul_mem hy.2 hx.2

/-- The simplest representatives modulo the infinitesimals of a convex subring, as a subring. -/
def residueRepresentatives : Subring Surreal.{u} where
  carrier := {x | cosetRep (infinitesimals C) x = x}
  zero_mem' := cosetRep_zero _
  one_mem' := cosetRep_infinitesimals_one C
  add_mem' := fun {x y} hx hy ↦ (cosetRep_add _ x y).trans (congrArg₂ (· + ·) hx hy)
  neg_mem' := fun {x} hx ↦ (cosetRep_neg _ x).trans (congrArg Neg.neg hx)
  mul_mem' := fun hx hy ↦ cosetRep_mul_eq_of_mul_notMem hx hy fun _ _ ha hb ↦
    mul_notMem_infinitesimals C ha hb

/-- The subring of residue representatives comprises the fixed points of the simplest
projection modulo the infinitesimals. -/
theorem mem_residueRepresentatives_iff {x : Surreal.{u}} :
    x ∈ residueRepresentatives C ↔ cosetRep (infinitesimals C) x = x :=
  Iff.rfl

/-- The simplest representative modulo the infinitesimals belongs to the subring of
residue representatives. -/
theorem cosetRep_mem_residueRepresentatives (x : Surreal.{u}) :
    cosetRep (infinitesimals C) x ∈ residueRepresentatives C :=
  (mem_residueRepresentatives_iff C).mpr (cosetRep_cosetRep _ x)

/-- An element that is both a residue representative and infinitesimal is zero. -/
theorem eq_zero_of_mem_residueRepresentatives_of_mem_infinitesimals {x : Surreal.{u}}
    (hx : x ∈ residueRepresentatives C) (hb : x ∈ infinitesimals C) : x = 0 :=
  ((mem_residueRepresentatives_iff C).mp hx).symm.trans (cosetRep_eq_zero_iff.mpr hb)

/-- Every omnific integer is its own simplest representative modulo the infinitesimals of a
convex subring. -/
theorem omnific_le_residueRepresentatives : omnific ≤ residueRepresentatives C := by
  intro x hx
  apply (mem_residueRepresentatives_iff C).mpr
  simpa only [one_mul] using
    cosetRep_mul_eq_of_isOmnific (cosetRep_infinitesimals_one C) (mem_omnific_iff.mp hx)

private theorem inv_mem_residueRepresentatives {x : Surreal.{u}}
    (hx : x ∈ residueRepresentatives C) (hxC : x ∈ C) : x⁻¹ ∈ residueRepresentatives C := by
  by_cases hx₀ : x = 0
  · simpa only [hx₀, inv_zero] using (residueRepresentatives C).zero_mem
  let y := cosetRep (infinitesimals C) x⁻¹
  have hy := cosetRep_mem_residueRepresentatives C x⁻¹
  have hb : x * (x⁻¹ - y) ∈ infinitesimals C :=
    mul_mem_infinitesimals_of_mem C hxC (sub_cosetRep_mem _ _)
  have hrep : x * (x⁻¹ - y) ∈ residueRepresentatives C := by
    rw [mul_sub, mul_inv_cancel₀ hx₀]
    exact (residueRepresentatives C).sub_mem (residueRepresentatives C).one_mem
      ((residueRepresentatives C).mul_mem hx hy)
  have he := eq_zero_of_mem_residueRepresentatives_of_mem_infinitesimals C hrep hb
  have hxy : x⁻¹ = y := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hx₀)
  exact hxy ▸ hy

private theorem inv_mem_subring_of_mem_residueRepresentatives {x : Surreal.{u}}
    (hx : x ∈ residueRepresentatives C) : x⁻¹ ∈ C := by
  by_cases hx₀ : x = 0
  · simpa only [hx₀, inv_zero] using C.zero_mem
  have hb : x ∉ infinitesimals C := fun hb ↦
    hx₀ (eq_zero_of_mem_residueRepresentatives_of_mem_infinitesimals C hx hb)
  exact ((notMem_infinitesimals_iff C).mp hb).2

/-- The residue field in a convex subring, represented by its simplest coset representatives. -/
def residueSubfield : Subfield Surreal.{u} where
  __ := residueRepresentatives C ⊓ C
  inv_mem' := by
    intro x hx
    obtain ⟨hxU, hxC⟩ := Subring.mem_inf.mp hx
    exact Subring.mem_inf.mpr
      ⟨inv_mem_residueRepresentatives C hxU hxC,
        inv_mem_subring_of_mem_residueRepresentatives C hxU⟩

/-- A surreal belongs to the residue subfield exactly when it is in the convex subring and is
its own simplest representative modulo the infinitesimals. -/
theorem mem_residueSubfield_iff {x : Surreal.{u}} :
    x ∈ residueSubfield C ↔ x ∈ residueRepresentatives C ∧ x ∈ C :=
  Subring.mem_inf

variable (D : Subring Surreal.{u}) [D.toAddSubgroup.IsConvex]

/-- The simplest representative modulo a larger convex subring is also a representative
modulo the infinitesimals of the smaller subring. -/
theorem cosetRep_mem_residueRepresentatives_of_le (h : C ≤ D) (x : Surreal.{u}) :
    cosetRep D.toAddSubgroup x ∈ residueRepresentatives C :=
  (mem_residueRepresentatives_iff C).mpr
    (cosetRep_cosetRep_of_ge (fun _ hx ↦ h (infinitesimals_le C hx)) x)

/-- Multiplying a simplest representative modulo a larger convex subring by a representative
modulo the smaller subring's infinitesimals preserves the larger subring's representatives. -/
theorem cosetRep_mul_eq_of_mem_residueRepresentatives (h : C ≤ D) {x y : Surreal.{u}}
    (hx : cosetRep D.toAddSubgroup x = x) (hy : y ∈ residueRepresentatives C) :
    cosetRep D.toAddSubgroup (x * y) = x * y := by
  apply cosetRep_mul_eq_of_mul_notMem hx ((mem_residueRepresentatives_iff C).mp hy)
  intro a b ha hb hab
  have hb₀ := ((notMem_infinitesimals_iff C).mp hb).1
  have hbD := h ((notMem_infinitesimals_iff C).mp hb).2
  exact ha (by
    simpa only [Subring.mem_toAddSubgroup, mul_assoc, mul_inv_cancel₀ hb₀, mul_one] using
      D.mul_mem hab hbD)

/-- Exact division of a simplest representative modulo a larger convex subring by a nonzero
representative in that subring preserves the simplest representative property. -/
theorem cosetRep_div_eq_of_mem_residueRepresentatives (h : C ≤ D) {p w : Surreal.{u}}
    (hp : cosetRep D.toAddSubgroup p = p) (hwU : w ∈ residueRepresentatives C)
    (hwD : w ∈ D) (hw₀ : w ≠ 0) : cosetRep D.toAddSubgroup (p / w) = p / w := by
  let r := cosetRep D.toAddSubgroup (p / w)
  have hdiff : (p / w - r) * w ∈ D := D.mul_mem (sub_cosetRep_mem D.toAddSubgroup _) hwD
  rw [sub_mul, div_mul_cancel₀ _ hw₀] at hdiff
  have hmul : r * w = p := calc
    r * w = cosetRep D.toAddSubgroup (r * w) :=
      (cosetRep_mul_eq_of_mem_residueRepresentatives C D h (cosetRep_cosetRep _ _) hwU).symm
    _ = cosetRep D.toAddSubgroup p := (cosetRep_eq_of_sub_mem hdiff).symm
    _ = p := hp
  exact (eq_div_iff hw₀).2 hmul

/-- The exact quotient in a larger convex subring remains in the ring of representatives
modulo the infinitesimals of the smaller subring. -/
theorem div_mem_residueRepresentatives_of_cosetRep_eq (h : C ≤ D) {p w : Surreal.{u}}
    (hp : cosetRep D.toAddSubgroup p = p) (hwU : w ∈ residueRepresentatives C)
    (hwD : w ∈ D) (hw₀ : w ≠ 0) : p / w ∈ residueRepresentatives C := by
  rw [← cosetRep_div_eq_of_mem_residueRepresentatives C D h hp hwU hwD hw₀]
  exact cosetRep_mem_residueRepresentatives_of_le C D h _

/-- The simplest representatives modulo a larger convex subring form an ideal in the
ring of representatives modulo the smaller subring's infinitesimals. -/
def simplestRepresentativesIdeal (h : C ≤ D) : Ideal (residueRepresentatives C) where
  carrier := {x | cosetRep D.toAddSubgroup (x : Surreal) = x}
  zero_mem' := cosetRep_zero _
  add_mem' := fun {x y} hx hy ↦ (cosetRep_add _ x y).trans (congrArg₂ (· + ·) hx hy)
  smul_mem' := fun a x hx ↦ by
    change cosetRep D.toAddSubgroup ((a : Surreal) * x) = a * (x : Surreal)
    rw [mul_comm]
    exact cosetRep_mul_eq_of_mem_residueRepresentatives C D h hx a.property

/-- Membership in the ideal of simplest representatives is fixedness under the projection
modulo the larger convex subring. -/
theorem mem_simplestRepresentativesIdeal_iff (h : C ≤ D) {x : residueRepresentatives C} :
    x ∈ simplestRepresentativesIdeal C D h ↔ cosetRep D.toAddSubgroup (x : Surreal) = x :=
  Iff.rfl

private theorem sub_cosetRep_mul_of_mem_residueRepresentatives (h : C ≤ D)
    (x y : residueRepresentatives C) :
    (x : Surreal) * y - cosetRep D.toAddSubgroup (x * y) =
      ((x : Surreal) - cosetRep D.toAddSubgroup x) *
        ((y : Surreal) - cosetRep D.toAddSubgroup y) := by
  let p := cosetRep D.toAddSubgroup x
  let q := cosetRep D.toAddSubgroup y
  let d := (x : Surreal) - p
  let e := (y : Surreal) - q
  have heq : (x : Surreal) * y - (p * y + q * d) = d * e := by
    dsimp [d, e]
    ring
  have hmem : (x : Surreal) * y - (p * y + q * d) ∈ D.toAddSubgroup := by
    rw [heq]
    exact D.mul_mem (sub_cosetRep_mem D.toAddSubgroup x) (sub_cosetRep_mem D.toAddSubgroup y)
  have hd : d ∈ residueRepresentatives C :=
    (residueRepresentatives C).sub_mem x.property
      (cosetRep_mem_residueRepresentatives_of_le C D h x)
  have hpy : cosetRep D.toAddSubgroup (p * y) = p * y :=
    cosetRep_mul_eq_of_mem_residueRepresentatives C D h (cosetRep_cosetRep _ x) y.property
  have hqd : cosetRep D.toAddSubgroup (q * d) = q * d :=
    cosetRep_mul_eq_of_mem_residueRepresentatives C D h (cosetRep_cosetRep _ y) hd
  rw [cosetRep_eq_of_sub_mem hmem, cosetRep_add, hpy, hqd]
  exact heq

/-- Subtracting the simplest representative modulo a larger convex subring gives a ring
retraction onto the representatives that belong to that subring. -/
def residueRetraction (h : C ≤ D) :
    residueRepresentatives C →+* (residueRepresentatives C ⊓ D : Subring Surreal) where
  toFun x := ⟨(x : Surreal) - cosetRep D.toAddSubgroup x, Subring.mem_inf.mpr
    ⟨(residueRepresentatives C).sub_mem x.property
        (cosetRep_mem_residueRepresentatives_of_le C D h x),
      sub_cosetRep_mem D.toAddSubgroup x⟩⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (show (1 : Surreal) - cosetRep D.toAddSubgroup 1 = 1 by
    rw [cosetRep_eq_zero_iff.mpr D.one_mem, sub_zero])
  map_add' x y := Subtype.ext (show
    (x : Surreal) + y - cosetRep D.toAddSubgroup (x + y) =
      ((x : Surreal) - cosetRep D.toAddSubgroup x) + ((y : Surreal) - cosetRep D.toAddSubgroup y) by
    rw [cosetRep_add, add_sub_add_comm])
  map_mul' x y := Subtype.ext (sub_cosetRep_mul_of_mem_residueRepresentatives C D h x y)

/-- The residue is the difference from the simplest representative modulo the larger
convex subring. -/
@[simp] theorem coe_residueRetraction (h : C ≤ D) (x : residueRepresentatives C) :
    (residueRetraction C D h x : Surreal) = (x : Surreal) - cosetRep D.toAddSubgroup x :=
  (rfl)

/-- Taking the residue fixes representatives already in the larger convex subring. -/
@[simp] theorem residueRetraction_inclusion (h : C ≤ D)
    (x : (residueRepresentatives C ⊓ D : Subring Surreal)) :
    residueRetraction C D h (Subring.inclusion inf_le_left x) = x := by
  apply Subtype.ext
  rw [coe_residueRetraction, Subring.coe_inclusion,
    cosetRep_eq_zero_iff.mpr (Subring.mem_inf.mp x.property).2, sub_zero]

/-- A representative is omnific exactly when its residue in a larger convex subring is
omnific. -/
theorem isOmnific_iff_isOmnific_residueRetraction (h : C ≤ D)
    (x : residueRepresentatives C) :
    IsOmnific (x : Surreal) ↔ IsOmnific (residueRetraction C D h x : Surreal) := by
  rw [coe_residueRetraction]
  have hp := isOmnific_of_cosetRep_eq (cosetRep_cosetRep D.toAddSubgroup x)
  refine ⟨fun hx ↦ hx.sub hp, fun hd ↦ ?_⟩
  simpa only [sub_add_cancel] using hd.add hp

end Surreal
