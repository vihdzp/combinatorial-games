/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Mathlib.ConvexSubgroup
public import CombinatorialGames.Surreal.Omnific.Basic

import Mathlib.Algebra.Order.Ring.Archimedean
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Finite omnific integers

The unit cut leaves no positive omnific integer below one. Subtracting the greatest
ordinary integer below a finitely bounded omnific integer therefore recovers zero.
-/

universe u

public section

namespace Surreal

/-- The subring of surreals bounded in magnitude by a natural number. -/
noncomputable def finiteSubring : Subring Surreal.{u} :=
  (ArchimedeanClass.addValuation Surreal.{u}).toValuation.valuationSubring.toSubring

/-- A surreal number is finite if its magnitude is bounded by a natural number. -/
theorem mem_finiteSubring_iff {x : Surreal.{u}} :
    x ∈ finiteSubring ↔ ∃ n : ℕ, |x| ≤ (n : Surreal) := by
  change x ∈ (ArchimedeanClass.addValuation Surreal.{u}).toValuation.valuationSubring ↔ _
  rw [Valuation.mem_valuationSubring_iff]
  change ArchimedeanClass.mk (1 : Surreal.{u}) ≤ ArchimedeanClass.mk x ↔ _
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using hn⟩

instance : finiteSubring.{u}.toAddSubgroup.IsConvex where
  ordConnected := by
    constructor
    intro x hx y hy z hz
    have hx' : 0 ≤ ArchimedeanClass.mk x := hx
    have hy' : 0 ≤ ArchimedeanClass.mk y := hy
    exact (le_min hx' hy').trans (ArchimedeanClass.min_le_mk_of_le_of_le hz.1 hz.2)

/-- An omnific integer bounded in magnitude by a finite count is an ordinary integer. -/
theorem IsOmnific.exists_intCast_of_abs_le {x : Surreal.{u}} (hx : IsOmnific x)
    {n : ℕ} (hn : |x| ≤ n) : ∃ k : ℤ, (k : Surreal) = x := by
  obtain ⟨hl, hu⟩ := abs_le.mp hn
  obtain ⟨k, hk⟩ := exists_floor' x
    ⟨-(n : ℤ), by simpa only [Int.cast_neg, Int.cast_natCast] using hl⟩
    ⟨n, by simpa only [Int.cast_natCast] using hu⟩
  refine ⟨k, ((hk k).mp le_rfl).eq_of_not_lt ?_⟩
  intro h
  have h1 := (hx.sub (.intCast k)).one_le_iff_pos.mpr (sub_pos.mpr h)
  have hnext : ((k + 1 : ℤ) : Surreal) ≤ x := by
    rw [Int.cast_add, Int.cast_one, add_comm]
    exact le_sub_iff_add_le.mp h1
  exact (Int.lt_succ_self k).not_ge ((hk (k + 1)).mpr hnext)

end Surreal
