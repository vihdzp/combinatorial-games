/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Coset.ResidueField
public import CombinatorialGames.Surreal.Scale.Growth

import CombinatorialGames.Mathlib.FourFactorRefinement
import CombinatorialGames.Surreal.Omnific.Refinement.AtScale

/-!
# Primality at a least occurring growth class
-/

universe u

public section

namespace Surreal

/-- At a least occurring class, the upper residue is primal if the bounded ring of
representatives is pre-Schreier. The complementary factor retains only larger occurrences. -/
theorem isPrimal_of_least_growthOccurs {i : Surreal.{u}}
    (hBounded : ∀ z : (residueRepresentatives (lowerGrowthSubring i) ⊓ upperGrowthSubring i :
      Subring Surreal.{u}), IsPrimal z)
    (x : omnific.{u}) (hi : IsLeast {j : Surreal.{u} | GrowthOccurs j x} i)
    (ih : ∀ j, GrowthOccurs j x → ∀ v : omnific.{u},
      (∀ k, GrowthOccurs k v ↔ j < k ∧ GrowthOccurs k x) → IsPrimal v) :
    IsPrimal x := by
  let I : Set Surreal.{u} := {j | GrowthOccurs j x}
  let C := commonLowerGrowthSubring I
  let D := upperGrowthSubring i
  have hLD : lowerGrowthSubring i ≤ D := lowerGrowthSubring_le_upperGrowthSubring i
  have hIeq : C = lowerGrowthSubring i := by
    apply le_antisymm (commonLowerGrowthSubring_le_lowerGrowthSubring hi.1)
    intro z hz
    apply (mem_commonLowerGrowthSubring_iff I).mpr
    intro j hj
    rcases (hi.2 hj).lt_or_eq with hlt | rfl
    · exact upperGrowthSubring_le_lowerGrowthSubring hlt (hLD hz)
    · exact hz
  apply isPrimal_of_growth_refinements x ih
  intro b c d hab
  let π := growthProjection I ⟨i, hi.1⟩
  have hpr (C' : Subring Surreal.{u}) [C'.toAddSubgroup.IsConvex]
      (he : C' = lowerGrowthSubring i) :
      ∀ z : (residueRepresentatives C' ⊓ D : Subring Surreal), IsPrimal z := by
    subst C'
    exact hBounded
  refine ⟨⟨i, hi.1⟩, (hpr C hIeq (π x)).exists_mul_eq_mul ?_⟩
  simpa only [map_mul] using congrArg π hab

end Surreal
