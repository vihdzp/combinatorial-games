/-
Copyright (c) 2026 CombinatorialGames contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CombinatorialGames contributors
-/
module

public import CombinatorialGames.Surreal.Scale.Basic
public import CombinatorialGames.Surreal.Omnific.Order

import Mathlib.Algebra.Group.Subgroup.Order

/-!
# A Conway cut between the gaps of two families

One monomial rescales a column and its reciprocal rescales a row to simplest representatives
modulo the finite surreals precisely when each product of two birth gaps is infinite.
-/

universe u

public noncomputable section

namespace Surreal

open Set
open scoped Pointwise

/-- A nonzero surreal is infinite in magnitude exactly when its leading exponent is positive. -/
theorem notMem_finiteSubring_iff_wlog_pos {x : Surreal.{u}} (hx : x ≠ 0) :
    x ∉ finiteSubring ↔ 0 < x.wlog := by
  rw [← not_le, ← wlog_one, wlog_le_wlog_iff hx one_ne_zero, vle_def,
    ArchimedeanClass.mk_le_mk, mem_finiteSubring_iff]
  simp only [abs_one, nsmul_eq_mul, mul_one]

/-- Dividing by a monomial leaves zero finite remainder exactly when its level lies below
all the gaps to earlier numbers. -/
theorem cosetRep_div_wpow_finite_iff (x t : Surreal.{u}) :
    cosetRep finiteSubring.toAddSubgroup (x / ω^ t) = x / ω^ t ↔
      ∀ y : Surreal.{u}, y.birthday < x.birthday → t < (x - y).wlog := by
  have scale : cosetRep (ω^ t • finiteSubring.toAddSubgroup) x = x ↔
      cosetRep finiteSubring.toAddSubgroup (x / ω^ t) = x / ω^ t := by
    rw [cosetRep_wpow_smul, eq_div_iff (wpow_ne_zero t), mul_comm]
  rw [← scale, cosetRep_eq_iff]
  apply forall_congr' fun y ↦ forall_congr' fun hy ↦ ?_
  have hd : x - y ≠ 0 := sub_ne_zero.mpr fun he ↦ hy.ne (congrArg birthday he.symm)
  rw [mem_smul_addSubgroup_iff_div_mem (wpow_ne_zero t)]
  change (x - y) / ω^ t ∉ finiteSubring ↔ _
  rw [notMem_finiteSubring_iff_wlog_pos (div_ne_zero hd (wpow_ne_zero t)), div_eq_mul_inv,
    wlog_mul hd (inv_ne_zero (wpow_ne_zero t)), wlog_inv, wlog_wpow]
  simp only [← sub_eq_add_neg, sub_pos]

private abbrev Earlier (x : Surreal.{u}) := {y : Surreal.{u} | y.birthday < x.birthday}

/-- Multiplying by a monomial leaves zero finite remainder exactly when the exponent
exceeds the leading exponents of the reciprocal gaps. -/
theorem cosetRep_mul_wpow_finite_iff (x t : Surreal.{u}) :
    cosetRep finiteSubring.toAddSubgroup (ω^ t * x) = ω^ t * x ↔
      ∀ y : Surreal.{u}, y.birthday < x.birthday → -(x - y).wlog < t := by
  rw [mul_comm (ω^ t), ← div_inv_eq_mul, ← wpow_neg, cosetRep_div_wpow_finite_iff]
  exact ⟨fun h y hy ↦ neg_lt.mp (h y hy), fun h y hy ↦ neg_lt.mp (h y hy)⟩

/-- The exponent puts the reciprocal gaps of the first family on the left and the gaps of
the second on the right. Both scaled families then have zero finite remainder. -/
theorem exists_wpow_rescaling_iff_infinite_gap_products {ι κ : Type*} [Small.{u} ι] [Small.{u} κ]
    (p : ι → Surreal.{u}) (q : κ → Surreal.{u}) :
    (∃ t : Surreal.{u},
      (∀ i, cosetRep finiteSubring.toAddSubgroup (ω^ t * p i) = ω^ t * p i) ∧
      ∀ j, cosetRep finiteSubring.toAddSubgroup (q j / ω^ t) = q j / ω^ t) ↔
    ∀ i x, x.birthday < (p i).birthday → ∀ j y, y.birthday < (q j).birthday →
      (p i - x) * (q j - y) ∉ finiteSubring := by
  have gaps (i) (x : Earlier (p i)) (j) (y : Earlier (q j)) :
      (p i - x) * (q j - y) ∉ finiteSubring ↔ -(p i - x).wlog < (q j - y).wlog := by
    have h₁ : p i - x ≠ 0 := sub_ne_zero.mpr fun he ↦ x.2.ne (congrArg birthday he.symm)
    have h₂ : q j - y ≠ 0 := sub_ne_zero.mpr fun he ↦ y.2.ne (congrArg birthday he.symm)
    rw [notMem_finiteSubring_iff_wlog_pos (mul_ne_zero h₁ h₂), wlog_mul h₁ h₂,
      neg_lt_iff_pos_add, add_comm]
  constructor
  · rintro ⟨t, hp, hq⟩ i x hx j y hy
    exact (gaps i ⟨x, hx⟩ j ⟨y, hy⟩).2
      (((cosetRep_mul_wpow_finite_iff _ _).1 (hp i) x hx).trans
        ((cosetRep_div_wpow_finite_iff _ _).1 (hq j) y hy))
  · intro h
    let L := range fun v : Σ i, Earlier (p i) ↦ -(p v.1 - v.2).wlog
    let R := range fun v : Σ j, Earlier (q j) ↦ (q v.1 - v.2).wlog
    have : Small.{u} L := small_range _
    have : Small.{u} R := small_range _
    have sep : ∀ l ∈ L, ∀ r ∈ R, l < r := by
      rintro _ ⟨⟨i, x⟩, rfl⟩ _ ⟨⟨j, y⟩, rfl⟩
      exact (gaps i x j y).1 (h i x x.2 j y y.2)
    let t : Surreal.{u} := !{L | R}' sep
    refine ⟨t, fun i ↦ (cosetRep_mul_wpow_finite_iff _ t).2 fun x hx ↦ ?_,
      fun j ↦ (cosetRep_div_wpow_finite_iff _ t).2 fun y hy ↦ ?_⟩
    · exact lt_ofSets_of_mem_left (H := sep) (mem_range_self (⟨i, ⟨x, hx⟩⟩ : Σ i, Earlier (p i)))
    · exact ofSets_lt_of_mem_right (H := sep) (mem_range_self (⟨j, ⟨y, hy⟩⟩ : Σ j, Earlier (q j)))

/-- Representatives modulo the infinitesimals of C and representatives modulo C have
separated gaps. The same cut makes both rescaled families whole. -/
theorem exists_wpow_rescaling_of_cosetReps {ι κ : Type*} [Small.{u} ι] [Small.{u} κ]
    (C : Subring Surreal.{u})
    [C.toAddSubgroup.IsConvex] (p : ι → Surreal.{u}) (q : κ → Surreal.{u})
    (hp : ∀ i, p i ∈ residueRepresentatives C)
    (hq : ∀ j, cosetRep C.toAddSubgroup (q j) = q j) :
    ∃ t : Surreal.{u},
      (∀ i, cosetRep finiteSubring.toAddSubgroup (ω^ t * p i) = ω^ t * p i) ∧
      ∀ j, cosetRep finiteSubring.toAddSubgroup (q j / ω^ t) = q j / ω^ t := by
  have separated (i x) (hx : x.birthday < (p i).birthday) (j y) (hy : y.birthday < (q j).birthday) :
      (p i - x) * (q j - y) ∉ finiteSubring := by
    have hg := (notMem_infinitesimals_iff C).mp
      (cosetRep_eq_iff.mp ((mem_residueRepresentatives_iff C).mp (hp i)) x hx)
    have hh := cosetRep_eq_iff.mp (hq j) y hy
    change q j - y ∉ C at hh
    intro h
    obtain ⟨n, hn⟩ := mem_finiteSubring_iff.mp h
    have hC : (p i - x) * (q j - y) ∈ C := abs_mem_iff.mp
      (C.toAddSubgroup.mem_of_nonneg_of_le (abs_nonneg _) hn (natCast_mem C n))
    exact hh (by simpa only [inv_mul_cancel_left₀ hg.1] using C.mul_mem hg.2 hC)
  exact (exists_wpow_rescaling_iff_infinite_gap_products p q).2 separated

end Surreal
