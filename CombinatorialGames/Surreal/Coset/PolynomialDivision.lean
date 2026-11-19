/-
Copyright (c) 2026 CombinatorialGames contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CombinatorialGames contributors
-/
module

public import CombinatorialGames.Surreal.Coset.ResidueField
public import Mathlib.Algebra.Polynomial.FieldDivision

import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.FieldSimp

/-!
# Polynomial division by rounding

Let the coefficients lie in the residue field of a convex subring. Evaluate at a
representative whose inverse is infinitesimal. Rounding the ratio of the two values
then gives the value of their polynomial quotient.
-/

universe u

public noncomputable section

namespace Surreal

open Polynomial

variable (D : Subring Surreal.{u}) [D.toAddSubgroup.IsConvex] {k : Type*} [Field k]
variable (j : k →+* residueSubfield D)
local notation "B" => infinitesimals D
local notation "U" => residueRepresentatives D
local notation "φ" => RingHom.comp (Subfield.subtype (residueSubfield D)) j
local notation "E" => Polynomial.eval₂RingHom φ

private theorem scalar_eval_mem (S : Subring Surreal.{u}) {m : Surreal.{u}} (hm : m ∈ S)
    (hc : ∀ a : k, φ a ∈ S) (p : k[X]) : E m p ∈ S := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb => exact (map_add (E m) a b) ▸ S.add_mem ha hb
  | monomial n a =>
    change Polynomial.eval₂ φ m _ ∈ S
    rw [Polynomial.eval₂_monomial]
    exact S.mul_mem (hc a) (S.pow_mem hm _)

private theorem eval_small_sub_const {u : Surreal.{u}} (hu : u ∈ B) (p : k[X]) :
    E u p - φ (p.coeff 0) ∈ B := by
  have h := congrArg (E u) (Polynomial.divX_mul_X_add p)
  simp only [map_add, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  have eqn : E u p - φ (p.coeff 0) = E u p.divX * u := by
    change p.eval₂ φ u - _ = _
    rw [← h, add_sub_cancel_right]
    rfl
  rw [eqn]
  exact mul_mem_infinitesimals_of_mem D (scalar_eval_mem D j D (infinitesimals_le D hu)
    (fun a ↦ ((mem_residueSubfield_iff D).mp (j a).2).2) _) hu

private theorem eval_reverse_at_inverse {m : Surreal.{u}} (hm : m ≠ 0) (a : k[X]) :
    E m a = E m⁻¹ a.reverse * m ^ a.natDegree := by
  let := invertibleOfNonzero hm
  simpa only [Polynomial.coe_eval₂RingHom, invOf_eq_inv] using
    (Polynomial.eval₂_reverse_mul_pow φ m a).symm

private theorem eval_reverse_not_small {m : Surreal.{u}} (hu : m⁻¹ ∈ B) {q : k[X]} (hq : q ≠ 0) :
    E m⁻¹ q.reverse ∉ B := by
  have hqsmall := eval_small_sub_const D j hu q.reverse
  rw [coeff_zero_reverse] at hqsmall
  intro h
  have hc : φ q.leadingCoeff ∈ B := by
    simpa only [sub_sub_cancel] using (B).sub_mem h hqsmall
  have hz := eq_zero_of_mem_residueRepresentatives_of_mem_infinitesimals D
    ((mem_residueSubfield_iff D).mp (j q.leadingCoeff).2).1 hc
  exact (leadingCoeff_ne_zero.mpr hq) ((map_eq_zero_iff φ (φ).injective).mp hz)

private theorem scalar_eval_injective {m : Surreal.{u}} (hm : m ≠ 0) (hu : m⁻¹ ∈ B) :
    Function.Injective (E m) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro q h
  by_contra hq
  have hn := ((notMem_infinitesimals_iff D).mp (eval_reverse_not_small D j hu hq)).1
  rw [eval_reverse_at_inverse D j hm] at h
  exact mul_ne_zero hn (pow_ne_zero _ hm) h

private theorem lower_degree_ratio_small {m : Surreal.{u}} (hm : m ≠ 0) (hu : m⁻¹ ∈ B)
    {p q : k[X]} (hq : q ≠ 0) (hd : p.degree < q.degree) : E m p / E m q ∈ B := by
  by_cases hp : p = 0
  · simp [hp]
  obtain ⟨hqrev, hinv⟩ := (notMem_infinitesimals_iff D).mp (eval_reverse_not_small D j hu hq)
  have hlt : p.natDegree < q.natDegree := (natDegree_lt_natDegree_iff hp).mpr hd
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt hlt
  have smallpow : (m⁻¹) ^ (n + 1) ∈ B := by
    rw [pow_succ]
    exact mul_mem_infinitesimals_of_mem D (D.pow_mem (infinitesimals_le D hu) n) hu
  have hpc := scalar_eval_mem D j D (infinitesimals_le D hu)
    (fun a ↦ ((mem_residueSubfield_iff D).mp (j a).2).2) p.reverse
  convert mul_mem_infinitesimals_of_mem D (D.mul_mem hpc hinv) smallpow using 1
  rw [eval_reverse_at_inverse D j hm p, eval_reverse_at_inverse D j hm q, hn, Nat.add_assoc,
    pow_add, inv_pow]
  field_simp [hqrev, hm]

/-- Evaluating a polynomial quotient above the coefficient scale gives the simplest member
of the infinitesimal coset of the actual surreal quotient. -/
theorem scalar_division_by_rounding {m : Surreal.{u}}
    (hm : m ≠ 0) (hmU : m ∈ U) (hu : m⁻¹ ∈ B) (p q : k[X]) (hq : q ≠ 0) :
    cosetRep B (E m p / E m q) = E m (p / q) := by
  have rsmall := lower_degree_ratio_small D j hm hu hq (Polynomial.degree_mod_lt p hq)
  have hqn := (map_ne_zero_iff _ (scalar_eval_injective D j hm hu)).mpr hq
  have h := congrArg (E m) (EuclideanDomain.mod_add_div p q)
  simp only [map_add, map_mul] at h
  have diff : E m p / E m q - E m (p / q) = E m (p % q) / E m q := by
    rw [← h, add_div, mul_div_cancel_left₀ _ hqn, add_sub_cancel_right]
  exact (cosetRep_eq_of_sub_mem (diff ▸ rsmall)).trans ((mem_residueRepresentatives_iff D).mp
    (scalar_eval_mem D j U hmU (fun a ↦ ((mem_residueSubfield_iff D).mp (j a).2).1) _))

end Surreal
