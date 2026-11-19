/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Germ.Basic
public import CombinatorialGames.Surreal.Scale.Growth

import CombinatorialGames.Surreal.Omnific.Coset

/-!
# Germs and residues at a limit of growth classes
-/

universe u

open scoped Pointwise

public section

namespace Surreal

theorem commonLowerGrowthSubring_le_lowerGrowthSubring {I : Set Surreal.{u}} {i : Surreal.{u}}
    (hi : i ∈ I) : commonLowerGrowthSubring I ≤ lowerGrowthSubring i :=
  fun _ hx ↦ (mem_commonLowerGrowthSubring_iff I).mp hx i hi

theorem upperGrowthSubring_le_commonLowerGrowthSubring {I : Set Surreal.{u}} {j : Surreal.{u}}
    (hj : ∀ i ∈ I, j < i) : upperGrowthSubring j ≤ commonLowerGrowthSubring I :=
  fun _ hx ↦ (mem_commonLowerGrowthSubring_iff I).mpr
    fun i hi ↦ upperGrowthSubring_le_lowerGrowthSubring (hj i hi) hx

/-- At a nonempty family of growth classes with no least class, having zero germ means being
the simplest representative modulo the upper subring of some class in the family. -/
theorem mem_germIdeal_commonLowerGrowth_iff {I : Set Surreal.{u}} (hI : I.Nonempty)
    (hno : ∀ j ∈ I, ∃ i ∈ I, i < j)
    {x : residueRepresentatives (commonLowerGrowthSubring I)} :
    x ∈ germIdeal (commonLowerGrowthSubring I) ↔
      ∃ i ∈ I, cosetRep (upperGrowthSubring i).toAddSubgroup (x : Surreal) = x := by
  let C := commonLowerGrowthSubring I
  constructor
  · intro hx
    rcases (mem_germIdeal_iff C).mp hx with rfl | ⟨t, ht, y, hy⟩
    · obtain ⟨i, hi⟩ := hI
      exact ⟨i, hi, cosetRep_zero _⟩
    · obtain ⟨j, hj, hnot⟩ : ∃ j ∈ I, ω^ t ∉ lowerGrowthSubring j := by
        by_contra! h
        exact ht ((mem_commonLowerGrowthSubring_iff I).mpr h)
      obtain ⟨i, hi, hij⟩ := hno j hj
      have hle : (upperGrowthSubring i).toAddSubgroup ≤
          (ω^ t • infinitesimals C) :=
        fun z hz ↦ by
          apply (mem_smul_addSubgroup_iff_div_mem (wpow_ne_zero t)).mpr
          rw [mem_infinitesimals_iff C]
          rcases eq_or_ne z 0 with rfl | hz₀
          · simp
          · right
            intro h
            have hquot : ω^ t / z ∈ lowerGrowthSubring j := by
              apply commonLowerGrowthSubring_le_lowerGrowthSubring hj
              simpa only [inv_div] using h
            have hzL := upperGrowthSubring_le_lowerGrowthSubring hij
              (Subring.mem_toAddSubgroup.mp hz)
            exact hnot (by simpa only [div_mul_cancel₀ _ hz₀] using
              (lowerGrowthSubring j).mul_mem hquot hzL)
      have hfixed : cosetRep (ω^ t • infinitesimals C) (x : Surreal) = x := by
        rw [hy]
        exact cosetRep_wpow_mul_eq ((mem_residueRepresentatives_iff C).mp y.2)
      refine ⟨i, hi, ?_⟩
      simpa only [hfixed] using cosetRep_cosetRep_of_ge hle (x : Surreal)
  · rintro ⟨i, hi, hfix⟩
    have hC := (commonLowerGrowthSubring_le_lowerGrowthSubring hi).trans
      (lowerGrowthSubring_le_upperGrowthSubring i)
    have hp : growthMonomial i ∈ upperGrowthSubring i := by
      refine (mem_upperGrowthSubring_iff i).mpr ⟨1, ?_⟩
      simp only [growthMonomial_eq, wpow_abs, pow_one, le_refl]
    have hle : (ω^ (ω^ i) • infinitesimals C) ≤
        (upperGrowthSubring i).toAddSubgroup := by
      intro z hz
      have hdiv := (mem_smul_addSubgroup_iff_div_mem (wpow_ne_zero _)).mp hz
      have hmul := (upperGrowthSubring i).mul_mem (hC (infinitesimals_le C hdiv)) hp
      rw [growthMonomial_eq, div_mul_cancel₀ _ (wpow_ne_zero _)] at hmul
      exact hmul
    have hm : ω^ (ω^ i) ∉ C := by
      intro h
      have hlt := (mem_lowerGrowthSubring_iff i).mp
        (commonLowerGrowthSubring_le_lowerGrowthSubring hi h) 1
      exact lt_irrefl _ (by simpa only [wpow_abs, pow_one, growthMonomial_eq] using hlt)
    apply (mem_germIdeal_iff C).mpr
    refine Or.inr ⟨ω^ i, hm, ⟨_,
      cosetRep_mem_residueRepresentatives C ((x : Surreal) / ω^ (ω^ i))⟩, ?_⟩
    have he := cosetRep_cosetRep_of_ge hle (x : Surreal)
    rw [hfix, cosetRep_wpow_smul] at he
    exact he.symm

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
