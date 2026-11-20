/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Scale.Growth

import CombinatorialGames.Mathlib.Polynomial.OrderedReadings
import CombinatorialGames.Surreal.Germ.Readings
import CombinatorialGames.Surreal.Omnific.Refinement.AtScale
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.FinCases

/-!
# Primality when the occurring growth classes have no least element

Refine the four germs using their finite set of readings. Each of the four resulting
equalities holds at some occurring class and at every lower one. The least of these four
classes therefore gives an exact refinement of the projection.
-/

universe u

public noncomputable section

namespace Surreal

private theorem exists_cutoff_of_zero_germ {I : Set Surreal.{u}} (hI : I.Nonempty)
    (hno : ∀ j ∈ I, ∃ i ∈ I, i < j) {z : residueRepresentatives (commonLowerGrowthSubring I)}
    (hz : germMap (commonLowerGrowthSubring I) z = 0) :
    ∃ i : I, ∀ k : I, k ≤ i → residueRetraction (commonLowerGrowthSubring I) (upperGrowthSubring k)
      ((commonLowerGrowthSubring_le_lowerGrowthSubring k.2).trans
        (lowerGrowthSubring_le_upperGrowthSubring k)) z = 0 := by
  obtain ⟨i, hi, hfix⟩ :=
    (mem_germIdeal_commonLowerGrowth_iff hI hno).mp ((germMap_eq_zero_iff _).mp hz)
  refine ⟨⟨i, hi⟩, fun k hk ↦ Subtype.ext ?_⟩
  have hle : (upperGrowthSubring k).toAddSubgroup ≤ (upperGrowthSubring i).toAddSubgroup := by
    rcases lt_or_eq_of_le (show k.1 ≤ i from hk) with hlt | heq
    · exact (upperGrowthSubring_le_lowerGrowthSubring hlt).trans
        (lowerGrowthSubring_le_upperGrowthSubring i)
    · rw [heq]
  have he := cosetRep_cosetRep_of_ge hle (z : Surreal)
  rw [hfix] at he
  rw [coe_residueRetraction, he, sub_self, Subring.coe_zero]

/-- Primality at a limit of occurring growth classes follows by applying the primality
criterion successively to the upper residues of the occurring classes. -/
theorem isPrimal_omnific_of_noLeast_growthOccurs (x : omnific.{u})
    (hI : ∃ i, GrowthOccurs i (x : Surreal))
    (hno : ∀ j, GrowthOccurs j (x : Surreal) → ∃ i, GrowthOccurs i (x : Surreal) ∧ i < j)
    (hprev : ∀ i, GrowthOccurs i (x : Surreal) → ∀ v : omnific.{u},
      (∀ j, GrowthOccurs j (v : Surreal) ↔ i < j ∧ GrowthOccurs j (x : Surreal)) → IsPrimal v) :
    IsPrimal x := by
  let I : Set Surreal.{u} := {i | GrowthOccurs i (x : Surreal)}
  let C := commonLowerGrowthSubring I
  let U := residueRepresentatives C
  let inc : omnific.{u} →+* U :=
    Subring.inclusion (omnific_le_residueRepresentatives C)
  have hC : C ≠ ⊤ := by
    obtain ⟨i, hi⟩ := hI
    intro htop
    have h : growthMonomial i ∈ C := by rw [htop]; trivial
    have hlt := (mem_lowerGrowthSubring_iff i).mp
      (commonLowerGrowthSubring_le_lowerGrowthSubring (show i ∈ I from hi) h) 1
    have hpos : 0 ≤ growthMonomial i := by rw [growthMonomial_eq]; exact wpow_nonneg _
    exact (lt_irrefl (growthMonomial i)) (by simpa only [abs_of_nonneg hpos, pow_one] using hlt)
  apply isPrimal_of_growth_refinements x hprev
  intro b c d hab
  let γ := (germMap C).comp inc
  have hg : γ x * γ b = γ c * γ d := by simpa only [map_mul] using congrArg γ hab
  obtain ⟨T, hind, hm⟩ := finite_germ_coordinates C hC ![γ x, γ b, γ c, γ d]
  obtain ⟨base, hbase⟩ := hI
  obtain ⟨E, F, G, H, ha, hb, hc, hd⟩ := Algebra.four_factors_in_adjoin hind inferInstance
    (hm 0) (hm 1) (hm 2) (hm 3) hg
  obtain ⟨e, he⟩ := germMap_surjective C (E : Germ C)
  obtain ⟨f, hf⟩ := germMap_surjective C (F : Germ C)
  obtain ⟨g, hhg⟩ := germMap_surjective C (G : Germ C)
  obtain ⟨h, hh⟩ := germMap_surjective C (H : Germ C)
  let err : Fin 4 → U := ![inc x - e * f, inc b - g * h, inc c - e * g, inc d - f * h]
  have hz (j : Fin 4) : germMap C (err j) = 0 := by
    have zero_of_eq (a : omnific) (p q : U) (he : γ a = germMap C p * germMap C q) :
        germMap C (inc a - p * q) = 0 := by
      rw [map_sub, map_mul, sub_eq_zero]
      exact he
    fin_cases j
    all_goals apply zero_of_eq
    all_goals simp only [he, hf, hhg, hh]
    exacts [ha, hb, hc, hd]
  choose cutoff hcut using fun j ↦ exists_cutoff_of_zero_germ (I := I) ⟨base, hbase⟩ hno (hz j)
  let i := Finset.univ.inf' Finset.univ_nonempty cutoff
  let ρ := residueRetraction C (upperGrowthSubring i)
    ((commonLowerGrowthSubring_le_lowerGrowthSubring i.2).trans
      (lowerGrowthSubring_le_upperGrowthSubring i))
  have exactAt (j : Fin 4) : ρ (err j) = 0 := hcut j i (Finset.inf'_le _ (Finset.mem_univ j))
  refine ⟨i, ρ e, ρ f, ρ g, ρ h, ?_, ?_, ?_, ?_⟩
  all_goals change ρ (inc _) = ρ _ * ρ _
  all_goals rw [← map_mul, ← sub_eq_zero, ← map_sub]
  exacts [exactAt 0, exactAt 1, exactAt 2, exactAt 3]

end Surreal
