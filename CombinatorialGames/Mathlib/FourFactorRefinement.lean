/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Basic

import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Tactic.TypeStar

/-!
# Four-factor refinement

An equality of two products in a commutative decomposition monoid admits four refinement factors
when multiplication cancels away from zero.
-/

public section

/-- A primal factor suffices to refine an equality of two products. -/
theorem IsPrimal.exists_mul_eq_mul {R : Type*}
    [CommMonoidWithZero R] [IsCancelMulZero R]
    {a b c d : R} (haP : IsPrimal a) (hab : a * b = c * d) :
    ∃ e f g h : R, a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h := by
  by_cases ha : a = 0
  · subst a
    have hcd : c * d = 0 := by simpa using hab.symm
    rcases mul_eq_zero.mp hcd with rfl | rfl
    · exact ⟨0, d, b, 1, by simp⟩
    · exact ⟨c, 0, 1, b, by simp⟩
  · have hadvd : a ∣ c * d := ⟨b, hab.symm⟩
    obtain ⟨e, f, hec, hfd, haef⟩ := haP hadvd
    obtain ⟨g, hcg⟩ := hec
    obtain ⟨h, hdh⟩ := hfd
    refine ⟨e, f, g, h, haef, ?_, hcg, hdh⟩
    apply mul_left_cancel₀ ha
    calc
      a * b = c * d := hab
      _ = (e * g) * (f * h) := by rw [hcg, hdh]
      _ = (e * f) * (g * h) := by ac_rfl
      _ = a * (g * h) := by rw [← haef]

/-- In a commutative decomposition monoid with cancellation away from zero, two factorizations
into two factors admit a common refinement. -/
theorem DecompositionMonoid.exists_mul_eq_mul {R : Type*}
    [CommMonoidWithZero R] [IsCancelMulZero R] [DecompositionMonoid R]
    {a b c d : R} (hab : a * b = c * d) :
    ∃ e f g h : R, a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h :=
  (DecompositionMonoid.primal a).exists_mul_eq_mul hab

/-- Every line with a nonzero horizontal coordinate has a row generating all its points. -/
abbrev HasGeneratingRows (A : Type*) [CommRing A] : Prop :=
  ∀ a c : A, a ≠ 0 → ∃ f g : A, f ≠ 0 ∧
    ∀ x y : A, c * x = a * y → ∃ q : A, x = q * f ∧ y = q * g

/-- Dividing the two coordinates by their gcd gives a row generating the line. -/
theorem HasGeneratingRows.of_isGCDMonoid (R : Type*) [CommRing R] [IsDomain R] [h : IsGCDMonoid R] :
    HasGeneratingRows R := by
  obtain ⟨_⟩ := h
  intro a c ha
  obtain ⟨f, g, haf, hcg, hfg⟩ := extract_gcd a c
  have hd : gcd a c ≠ 0 := (gcd_eq_zero_iff a c).not.mpr fun hz ↦ ha hz.1
  have hf : f ≠ 0 := right_ne_zero_of_mul (haf ▸ ha)
  refine ⟨f, g, hf, fun x y hxy ↦ ?_⟩
  have eqn : g * x = f * y := mul_left_cancel₀ hd (by
    simpa only [← mul_assoc, ← haf, ← hcg] using hxy)
  obtain ⟨q, hq⟩ := (gcd_isUnit_iff_isRelPrime.mp hfg).dvd_of_dvd_mul_left
    (show f ∣ g * x from ⟨y, eqn⟩)
  refine ⟨q, hq.trans (mul_comm f q), mul_left_cancel₀ hf ?_⟩
  calc f * y = g * x := eqn.symm
       _ = f * (q * g) := by rw [hq]; ac_rfl

/-- Carry generating rows across a ring equivalence. -/
theorem HasGeneratingRows.of_equiv {A D : Type*} [CommRing A] [CommRing D] (e : A ≃+* D)
    (H : HasGeneratingRows D) : HasGeneratingRows A := by
  intro a c ha
  obtain ⟨f, g, hf, row⟩ := H (e a) (e c) ((map_ne_zero_iff _ e.injective).mpr ha)
  refine ⟨e.symm f, e.symm g, (map_ne_zero_iff _ e.symm.injective).mpr hf, fun x y h ↦ ?_⟩
  obtain ⟨q, hx, hy⟩ := row (e x) (e y) (by simpa only [map_mul] using congrArg e h)
  exact ⟨e.symm q, by simpa using congrArg e.symm hx, by simpa using congrArg e.symm hy⟩

/-- A row generating two points gives the four factors of their product equality. -/
theorem HasGeneratingRows.decompositionMonoid {R : Type*} [CommRing R] [IsDomain R]
    (rows : HasGeneratingRows R) : DecompositionMonoid R := by
  constructor
  rintro a c d ⟨b, he⟩
  by_cases ha : a = 0
  · subst a
    rcases mul_eq_zero.mp (he.trans (zero_mul _)) with rfl | rfl
    · exact ⟨0, 1, dvd_zero _, one_dvd _, (zero_mul _).symm⟩
    · exact ⟨1, 0, one_dvd _, dvd_zero _, (one_mul _).symm⟩
  obtain ⟨f, g, _, row⟩ := rows a c ha
  obtain ⟨e, hA, hC⟩ := row a c (mul_comm ..)
  obtain ⟨h, hD, _⟩ := row d b he
  exact ⟨e, f, ⟨g, hC⟩, ⟨h, hD.trans (mul_comm ..)⟩, hA⟩
