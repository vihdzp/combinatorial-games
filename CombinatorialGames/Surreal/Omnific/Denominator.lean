/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Coset.ResidueField
public import CombinatorialGames.Surreal.Scale.Growth

import CombinatorialGames.Surreal.Omnific.Coset
import CombinatorialGames.Surreal.Scale.OptionGaps
import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Whole denominators in intersections of lower growth subrings
-/

universe u

public noncomputable section

namespace Surreal

open Set

private theorem wlog_lt_exponent_div_of_mem_lower {i q : Surreal.{u}} (hq : 0 < q)
    (h : q ∈ lowerGrowthSubring i) (n : ℕ) : q.wlog < ω^ i / ((n : Surreal) + 1) := by
  have hn : 0 < (n : Surreal.{u}) + 1 := by positivity
  apply (lt_div_iff₀ hn).mpr
  have hi := wpow_pos (ω^ i)
  have hpow := (mem_lowerGrowthSubring_iff i).mp h (2 * (n + 1))
  rw [abs_of_pos hq, growthMonomial_eq] at hpow
  have hle := wlog_monotoneOn (pow_pos hq _) hi hpow.le
  have hi' := wpow_pos i
  simp only [wlog_pow, wlog_wpow, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_one] at hle
  nlinarith

private theorem wpow_mem_lower_of_forall_lt_exponent_div {b i : Surreal.{u}}
    (h : ∀ n : ℕ, b < ω^ i / ((n : Surreal) + 1)) : ω^ b ∈ lowerGrowthSubring i := by
  apply (mem_lowerGrowthSubring_iff i).mpr
  intro n
  rw [wpow_abs, growthMonomial_eq, ← wpow_natCast_mul, wpow_lt_wpow]
  cases n with
  | zero => simp
  | succ n =>
      have hn : 0 < (n : Surreal.{u}) + 1 := by positivity
      have hlt := (lt_div_iff₀ hn).mp (h n)
      simpa only [Nat.cast_succ, mul_comm] using hlt

/-- A member of the residue subfield of a small intersection of lower growth subrings is a
quotient of two omnific integers in that intersection, with positive denominator. -/
theorem exists_whole_denominator_commonLowerGrowth (I : Set Surreal.{u}) [Small.{u} I]
    {k : Surreal.{u}} (hkU : k ∈ residueRepresentatives (commonLowerGrowthSubring I))
    (hkC : k ∈ commonLowerGrowthSubring I) :
    ∃ m : Surreal.{u}, 0 < m ∧ IsOmnific m ∧ m ∈ commonLowerGrowthSubring I ∧
      IsOmnific (m * k) ∧ m * k ∈ commonLowerGrowthSubring I := by
  let C := commonLowerGrowthSubring I
  let earlier := {y : Surreal.{u} | y.birthday < k.birthday}
  have gap (y : earlier) : 0 < |(k - y.1)⁻¹| ∧ |(k - y.1)⁻¹| ∈ C := by
    obtain ⟨hne, hC⟩ := (notMem_infinitesimals_iff C).mp
      (cosetRep_eq_iff.mp ((mem_residueRepresentatives_iff C).mp hkU) y.1 y.2)
    exact ⟨abs_pos.mpr (inv_ne_zero hne), abs_mem_iff.mpr hC⟩
  let L : Set Surreal.{u} := insert 0 (range fun y : earlier ↦ -(k - y.1).wlog)
  let R : Set Surreal.{u} := range fun v : I × ℕ ↦ ω^ v.1.1 / ((v.2 : Surreal) + 1)
  have hseparate : ∀ l ∈ L, ∀ r ∈ R, l < r := by
    intro l hl r hr
    obtain ⟨⟨i, n⟩, rfl⟩ := hr
    rcases hl with he | ⟨a, rfl⟩
    · rw [he]
      exact div_pos (wpow_pos _) (by positivity)
    · simpa only [wlog_abs, wlog_inv] using wlog_lt_exponent_div_of_mem_lower (gap a).1
        ((mem_commonLowerGrowthSubring_iff I).mp (gap a).2 i i.2) n
  let b : Surreal.{u} := !{L | R}' hseparate
  have hb : 0 < b := lt_ofSets_of_mem_left (mem_insert _ _)
  have hbC : ω^ b ∈ C := by
    apply (mem_commonLowerGrowthSubring_iff I).mpr
    intro i hi
    apply wpow_mem_lower_of_forall_lt_exponent_div
    intro n
    exact ofSets_lt_of_mem_right (s := L) (t := R) (H := hseparate)
      (mem_range_self ((⟨i, hi⟩ : I), n))
  have hwhole : IsOmnific (ω^ b) := by
    apply isOmnific_of_cosetRep_eq (C := finiteSubring)
    apply cosetRep_wpow_eq_of_notMem
    exact (notMem_finiteSubring_iff_wlog_pos (wpow_ne_zero b)).mpr (by simpa using hb)
  refine ⟨ω^ b, wpow_pos b, hwhole, hbC, ?_, C.mul_mem hbC hkC⟩
  apply isOmnific_of_cosetRep_eq (C := finiteSubring)
  apply (cosetRep_mul_wpow_finite_iff k b).mpr
  intro y hy
  exact lt_ofSets_of_mem_left (s := L) (t := R) (H := hseparate)
    (mem_insert_of_mem _ (mem_range_self (⟨y, hy⟩ : earlier)))

end Surreal
