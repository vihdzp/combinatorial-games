/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Scale.Growth

import CombinatorialGames.Surreal.Omnific.Coset

/-!
# Residues at the common lower growth scale
-/

universe u

public section

namespace Surreal

theorem commonLowerGrowthSubring_le_lowerGrowthSubring {I : Set Surreal.{u}} {i : Surreal.{u}}
    (hi : i ∈ I) : commonLowerGrowthSubring I ≤ lowerGrowthSubring i :=
  fun _ hx ↦ (mem_commonLowerGrowthSubring_iff I).mp hx i hi

theorem upperGrowthSubring_le_commonLowerGrowthSubring {I : Set Surreal.{u}} {j : Surreal.{u}}
    (hj : ∀ i ∈ I, j < i) : upperGrowthSubring j ≤ commonLowerGrowthSubring I :=
  fun _ hx ↦ (mem_commonLowerGrowthSubring_iff I).mpr
    fun i hi ↦ upperGrowthSubring_le_lowerGrowthSubring (hj i hi) hx

theorem growthOccurs_sub_cosetRep_iff_of_upper_le
    (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex] {x j : Surreal.{u}}
    (h : upperGrowthSubring j ≤ C) :
    GrowthOccurs j (x - cosetRep C.toAddSubgroup x) ↔ GrowthOccurs j x := by
  have hL : (lowerGrowthSubring j).toAddSubgroup ≤ C.toAddSubgroup :=
    (lowerGrowthSubring_le_upperGrowthSubring j).trans h
  have hU : (upperGrowthSubring j).toAddSubgroup ≤ C.toAddSubgroup := h
  simp only [growthOccurs_iff, cosetRep_sub, cosetRep_cosetRep_of_ge hL,
    cosetRep_cosetRep_of_ge hU]
  apply not_congr
  constructor
  · intro e
    simpa only [sub_add_cancel] using congrArg (· + cosetRep C.toAddSubgroup x) e
  · exact congrArg (· - cosetRep C.toAddSubgroup x)

/-- Projecting an omnific integer to the intersection of the lower subrings of all its
occurring growth classes leaves an ordinary integer. -/
theorem exists_intCast_eq_sub_cosetRep_commonLowerGrowth (I : Set Surreal.{u}) {x : Surreal.{u}}
    (hx : IsOmnific x) (hI : ∀ i, GrowthOccurs i x → i ∈ I) :
    ∃ k : ℤ, (k : Surreal) = x - cosetRep (commonLowerGrowthSubring I).toAddSubgroup x := by
  let C := commonLowerGrowthSubring I
  let y := x - cosetRep C.toAddSubgroup x
  have hy : y ∈ C := sub_cosetRep_mem C.toAddSubgroup x
  apply (hx.sub (isOmnific_of_cosetRep_eq (cosetRep_cosetRep C.toAddSubgroup x)))
    |>.exists_intCast_of_not_growthOccurs
  intro j hj
  have hbelow : ∀ i ∈ I, j < i := by
    intro i hi
    by_contra! hij
    have hyL : y ∈ lowerGrowthSubring j := by
      rcases hij.lt_or_eq with hlt | rfl
      · exact upperGrowthSubring_le_lowerGrowthSubring hlt
          (lowerGrowthSubring_le_upperGrowthSubring i
            (commonLowerGrowthSubring_le_lowerGrowthSubring hi hy))
      · exact commonLowerGrowthSubring_le_lowerGrowthSubring hi hy
    have hL : cosetRep (lowerGrowthSubring j).toAddSubgroup y = 0 :=
      cosetRep_eq_zero_iff.mpr hyL
    have hU : cosetRep (upperGrowthSubring j).toAddSubgroup y = 0 :=
      cosetRep_eq_zero_iff.mpr (lowerGrowthSubring_le_upperGrowthSubring j hyL)
    exact (growthOccurs_iff j y).mp hj (hL.trans hU.symm)
  have hj' := (growthOccurs_sub_cosetRep_iff_of_upper_le C
    (upperGrowthSubring_le_commonLowerGrowthSubring hbelow)).mp hj
  exact (lt_irrefl j) (hbelow j (hI j hj'))

end Surreal
