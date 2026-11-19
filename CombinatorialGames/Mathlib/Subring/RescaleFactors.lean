/-
Copyright (c) 2026 CombinatorialGames contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CombinatorialGames contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Ring.Subring.Basic

import CombinatorialGames.Mathlib.FourFactorRefinement
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.TypeStar

/-!
# Rescaling the four factors of one equality

Two factorizations of a nonzero matrix as an outer product over a field differ by a
single scalar on the column and its inverse on the row.
-/

public section

/-- Primality is invariant under a ring equivalence. -/
theorem RingEquiv.isPrimal_iff {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (e : A ≃+* B) (a : A) : IsPrimal (e a) ↔ IsPrimal a := by
  simp only [IsPrimal, e.surjective.forall₂, e.surjective.exists₂, ← map_mul,
    map_dvd_iff e, e.injective.eq_iff]

namespace Subring

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] (S : Subring K)

private theorem scale_outer_product (p q : Fin 2 → K) (u v : Fin 2 → S)
    (hp : ∃ i, p i ≠ 0) (hq : ∃ j, q j ≠ 0)
    (heq : ∀ i j, p i * q j = (u i : K) * v j) :
    ∃ k : K, k ≠ 0 ∧ (∀ i, k * p i ∈ S) ∧ ∀ j, k⁻¹ * q j ∈ S := by
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hq
  have huv : (u i : K) * v j ≠ 0 := (heq i j) ▸ mul_ne_zero hi hj
  let k := (u i : K) / p i
  have hk : k ≠ 0 := div_ne_zero (left_ne_zero_of_mul huv) hi
  have hki : k * p i = u i := div_mul_cancel₀ _ hi
  have row (l) : q l = k * v l := by
    apply mul_left_cancel₀ hi
    rw [heq, mul_left_comm, ← mul_assoc, hki]
  refine ⟨k, hk, fun l ↦ ?_, fun l ↦ ?_⟩
  · have he : k * p l = u l := by
      apply mul_right_cancel₀ (right_ne_zero_of_mul huv)
      rw [mul_comm k (p l), mul_assoc, ← row, heq]
    exact he ▸ (u l).2
  · rw [row, inv_mul_cancel_left₀ hk]
    exact (v l).2

/-- Match a nonzero lower outer product to a refinement over the scalar residue subring. -/
theorem rescale_nonzero_four_factors (π : A →ₐ[K] K) (p q : Fin 2 → A)
    (hp : ∃ i, π (p i) ≠ 0) (hq : ∃ j, π (q j) ≠ 0)
    (whole : ∀ i j, π (p i * q j) ∈ S)
    (hpr : IsPrimal (⟨π (p 0 * q 0), whole 0 0⟩ : S)) :
    ∃ (u v : Fin 2 → A), (∀ i, π (u i) ∈ S) ∧ (∀ j, π (v j) ∈ S) ∧
      ∀ i j, u i * v j = p i * q j := by
  let m (i j : Fin 2) : S := ⟨π (p i * q j), whole i j⟩
  have hdet : m 0 0 * m 1 1 = m 0 1 * m 1 0 := by
    apply Subtype.ext
    change π _ * π _ = π _ * π _
    simp only [map_mul]
    ac_rfl
  obtain ⟨e, f, g, h, ha, hb, hc, hd⟩ := hpr.exists_mul_eq_mul hdet
  let u : Fin 2 → S := ![e, h]
  let v : Fin 2 → S := ![f, g]
  have he : ∀ i j, m i j = u i * v j := by
    intro i j
    fin_cases i <;> fin_cases j
    exacts [ha, hc, hd.trans (mul_comm _ _), hb.trans (mul_comm _ _)]
  obtain ⟨k, hk, hu, hv⟩ := scale_outer_product S (π ∘ p) (π ∘ q) u v
    hp hq fun i j ↦
      (π.map_mul _ _).symm.trans (congrArg Subtype.val (he i j))
  let c := algebraMap K A
  refine ⟨fun i ↦ c k * p i, fun j ↦ c k⁻¹ * q j, ?_, ?_, fun i j ↦ ?_⟩
  · intro i
    rw [map_mul, π.commutes]
    exact hu i
  · intro j
    rw [map_mul, π.commutes]
    exact hv j
  · change c k * p i * (c k⁻¹ * q j) = _
    calc
      _ = (c k * c k⁻¹) * (p i * q j) := by ac_rfl
      _ = _ := by rw [← map_mul, mul_inv_cancel₀ hk, map_one, one_mul]

end Subring
