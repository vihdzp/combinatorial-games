/-
Copyright (c) 2026 CombinatorialGames contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CombinatorialGames contributors
-/
module

public import CombinatorialGames.Surreal.Omnific.Order
public import CombinatorialGames.Surreal.Real
public import CombinatorialGames.Surreal.Scale.Basic

import CombinatorialGames.Surreal.Omnific.Coset
import CombinatorialGames.Surreal.Scale.OptionGaps

/-!
# A common whole row with an infinitesimal exponent

For any real slope, the points with horizontal coordinates ω and the sum of ω^(1/n)
for n ≥ 1 share a whole direction with horizontal coordinate ω^(1/ω).
The cut defining the sum uses its finite partial sums. For slope √2 this gives whole factors
for the example of L’Innocente and Mantova, §9.1, after allowing surreal exponents.
-/

universe u

public noncomputable section

open Set
open scoped Pointwise

namespace Surreal

private theorem wpow_fixed_of_pos {b : Surreal.{u}} (hb : 0 < b) :
    cosetRep finiteSubring.toAddSubgroup (ω^ b) = ω^ b := by
  apply cosetRep_wpow_eq_of_notMem
  exact (notMem_finiteSubring_iff_wlog_pos (wpow_ne_zero b)).mpr (by simpa using hb)

private theorem real_mem_finite (r : ℝ) : (r : Surreal.{u}) ∈ finiteSubring := by
  obtain ⟨n, hn⟩ := exists_nat_ge |r|
  exact mem_finiteSubring_iff.mpr ⟨n, by
    simpa only [Real.toSurreal_abs, Real.toSurreal_natCast] using
      (Real.toSurreal_le_iff.mpr hn : (|r| : ℝ).toSurreal ≤ (n : ℝ).toSurreal)⟩

private theorem real_mem_finite_scalar (r : ℝ) :
    (r : Surreal.{u}) ∈ residueSubfield finiteSubring := by
  refine (mem_residueSubfield_iff _).mpr
    ⟨(mem_residueRepresentatives_iff _).mpr ?_, real_mem_finite r⟩
  apply cosetRep_mk_eq_of_forall_moves r.toIGame
  intro p a ha
  have gap (q : Dyadic) (hq : r ≠ q.toRat) :
      (r : Surreal.{u}) - (q.toRat : Surreal) ∉ infinitesimals finiteSubring := by
    have hne : r - (q.toRat : ℝ) ≠ 0 := sub_ne_zero.mpr hq
    have h := (notMem_infinitesimals_iff finiteSubring).mpr
      ⟨show ((r - (q.toRat : ℝ) : ℝ) : Surreal.{u}) ≠ 0 by exact_mod_cast hne,
        show ((r - (q.toRat : ℝ) : ℝ) : Surreal.{u})⁻¹ ∈ finiteSubring by
          simpa only [← Real.toSurreal_inv] using real_mem_finite (r - (q.toRat : ℝ))⁻¹⟩
    simpa only [Real.toSurreal_sub, Real.toSurreal_ratCast] using h
  cases p with
  | left =>
    obtain ⟨q, hq, rfl⟩ := Real.moves_left_toIGame r ▸ ha
    simpa only [mk_real_toIGame, Surreal.mk_dyadic] using gap q (ne_of_gt hq)
  | right =>
    obtain ⟨q, hq, rfl⟩ := Real.moves_right_toIGame r ▸ ha
    simpa only [mk_real_toIGame, Surreal.mk_dyadic] using gap q (ne_of_lt hq)

private def partialMonomials (t : ℕ → Surreal.{u}) : ℕ → Surreal.{u}
  | 0 => 0
  | n + 1 => partialMonomials t n + ω^ (t n)

private def upperMonomials (t : ℕ → Surreal.{u}) (n : ℕ) :=
  partialMonomials t n + 2 * ω^ (t n)

private theorem partialMonomials_increasing (t : ℕ → Surreal.{u}) :
    StrictMono (partialMonomials t) :=
  strictMono_nat_of_lt_succ fun n ↦ lt_add_of_pos_right _ (wpow_pos (t n))

private theorem upperMonomials_decreasing {t : ℕ → Surreal.{u}} (ht : StrictAnti t) :
    StrictAnti (upperMonomials t) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have h := natCast_mul_wpow_lt_wpow 2 (ht (Nat.lt_succ_self n))
  simp only [Nat.cast_ofNat] at h
  unfold upperMonomials
  rw [partialMonomials]
  linarith

private theorem partialMonomials_separated {t : ℕ → Surreal.{u}} (ht : StrictAnti t) :
    ∀ l ∈ range (partialMonomials t), ∀ r ∈ range (upperMonomials t), l < r := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  let n := max i j
  have gap : partialMonomials t n < upperMonomials t n :=
    lt_add_of_pos_right _ (mul_pos two_pos (wpow_pos _))
  exact ((partialMonomials_increasing t).monotone (le_max_left i j)).trans_lt
    (gap.trans_le ((upperMonomials_decreasing ht).antitone (le_max_right i j)))

/-- The sum of a decreasing sequence of unit monomials, cut between its finite prefixes
and those prefixes plus twice the next term. -/
def descendingMonomialSum (t : ℕ → Surreal.{u}) (ht : StrictAnti t) : Surreal.{u} :=
  !{range (partialMonomials t) | range (upperMonomials t)}' (partialMonomials_separated ht)

/-- Dividing a countable descending monomial sum by a monomial strictly below every term
leaves zero finite remainder. The simplest representative still lies between the same options. -/
theorem descendingMonomialSum_div_fixed {t : ℕ → Surreal.{u}} (ht : StrictAnti t)
    {ε : Surreal.{u}} (hε : ∀ n, ε < t n) :
    let s := descendingMonomialSum t ht
    cosetRep finiteSubring.toAddSubgroup (s / ω^ ε) = s / ω^ ε := by
  let H := ω^ ε • finiteSubring.toAddSubgroup
  let s := descendingMonomialSum t ht
  have term (n) : cosetRep H (ω^ (t n)) = ω^ (t n) := by
    rw [cosetRep_wpow_smul, ← wpow_sub, wpow_fixed_of_pos (sub_pos.mpr (hε n)),
      ← wpow_add, add_sub_cancel]
  have left (n) : cosetRep H (partialMonomials t n) = partialMonomials t n := by
    induction n with
    | zero => exact cosetRep_zero H
    | succ n ih => rw [partialMonomials, cosetRep_add, ih, term]
  have right (n) : cosetRep H (upperMonomials t n) = upperMonomials t n := by
    simp only [upperMonomials, two_mul, cosetRep_add, left, term]
  have fixed : cosetRep H s = s := by
    by_contra h
    apply (birthday_ofSets_lt_of_btwn (H := partialMonomials_separated ht)
      (z := cosetRep H s) ?_ ?_ (Ne.symm h)).not_ge (birthday_cosetRep_le (by simp : s - s ∈ H))
    · rintro _ ⟨n, rfl⟩
      have hnext : partialMonomials t (n + 1) < s := lt_ofSets_of_mem_left (mem_range_self _)
      exact ((partialMonomials_increasing t) (Nat.lt_succ_self n)).trans_le
        (left (n + 1) ▸ monotone_cosetRep H hnext.le)
    · rintro _ ⟨n, rfl⟩
      have hnext : s < upperMonomials t (n + 1) := ofSets_lt_of_mem_right (mem_range_self _)
      exact (right (n + 1) ▸ monotone_cosetRep H hnext.le).trans_lt
        ((upperMonomials_decreasing ht) (Nat.lt_succ_self n))
  exact (eq_div_iff (wpow_ne_zero ε)).2 (by
    simpa only [H, cosetRep_wpow_smul, mul_comm (ω^ ε)] using fixed)

/-- The four explicit factors on the line of real slope r through the horizontal
coordinates ω and the sum of ω^(1/n) for n ≥ 1. The exponent of their common row is 1/ω. -/
theorem refinement_omega_descendingMonomialSum (r : ℝ) :
    let w : Surreal.{u} := ω^ (1 : Surreal)
    let t (n : ℕ) : Surreal.{u} := ((n : Surreal) + 1)⁻¹
    ∃ ht : StrictAnti t, let s := descendingMonomialSum t ht
      let m := ω^ w⁻¹
      IsOmnific (w / m) ∧ IsOmnific (s / m) ∧ IsOmnific m ∧ IsOmnific (m * (r : Surreal)) ∧
      (w / m) * m = w ∧ (w / m) * (m * r) = w * r ∧
      (s / m) * m = s ∧ (s / m) * (m * r) = s * r := by
  let w : Surreal.{u} := ω^ (1 : Surreal)
  let t (n : ℕ) : Surreal.{u} := ((n : Surreal) + 1)⁻¹
  have ht : StrictAnti t := by
    intro a b hab
    exact inv_strictAnti₀ (by positivity : 0 < (a : Surreal.{u}) + 1)
      (by exact_mod_cast Nat.succ_lt_succ hab : (a : Surreal) + 1 < (b : Surreal) + 1)
  let s := descendingMonomialSum t ht
  have below (n) : w⁻¹ < t n := by
    apply inv_strictAnti₀ (by positivity : 0 < (n : Surreal.{u}) + 1)
    simpa only [Nat.cast_succ, wpow_zero, mul_one] using
      natCast_mul_wpow_lt_wpow (n + 1) (zero_lt_one : (0 : Surreal.{u}) < 1)
  have hm := wpow_fixed_of_pos (inv_pos.mpr (wpow_pos (1 : Surreal.{u})))
  let m := ω^ w⁻¹
  have hm₀ : m ≠ 0 := wpow_ne_zero _
  have divide (x : Surreal.{u}) : x / m * m = x := div_mul_cancel₀ _ hm₀
  have scale (x : Surreal.{u}) : x / m * (m * r) = x * r := by rw [← mul_assoc, divide]
  refine ⟨ht, ?_, isOmnific_of_cosetRep_eq (C := finiteSubring)
    (descendingMonomialSum_div_fixed ht below),
    isOmnific_of_cosetRep_eq (C := finiteSubring) hm, ?_, divide w, scale w, divide s, scale s⟩
  · have h₁ : w⁻¹ < 1 := by simpa only [t, Nat.cast_zero, zero_add, inv_one] using below 0
    exact isOmnific_of_cosetRep_eq (C := finiteSubring) (by
      rw [← wpow_sub]
      exact wpow_fixed_of_pos (sub_pos.mpr h₁))
  · apply isOmnific_of_cosetRep_eq (C := finiteSubring)
    exact cosetRep_mul_eq_of_mem_residueRepresentatives finiteSubring finiteSubring le_rfl hm
      ((mem_residueSubfield_iff _).mp (real_mem_finite_scalar r)).1

end Surreal
