/-
Copyright (c) 2026 CombinatorialGames contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CombinatorialGames contributors
-/
module

public import CombinatorialGames.Mathlib.FourFactorRefinement
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPolynomial.Basic

import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Generating rows after adjoining polynomial variables

Compare coefficients of the new variables in the line equation. Each coefficient pair is
a multiple of the original row, so the polynomial pair is a multiple of it as well.
-/

public section

namespace MvPolynomial

private theorem row_in_constants {R σ : Type*} [CommRing R] [IsDomain R] {a c f g : R}
    (ha : a ≠ 0) (row : ∀ x y : R, c * x = a * y → ∃ q, x = q * f ∧ y = q * g)
    {x y : MvPolynomial σ R} (h : C c * x = C a * y) :
    ∃ q, x = q * C f ∧ y = q * C g := by
  obtain ⟨k, hk, hk'⟩ := row a c (mul_comm ..)
  have eqn : c * f = a * g := by rw [hk, hk']; ac_rfl
  have dvd : C f ∣ x := (C_dvd_iff_dvd_coeff ..).mpr fun d ↦ by
    have he := congrArg (fun p : MvPolynomial σ R ↦ p.coeff d) h
    simp only [coeff_C_mul] at he
    obtain ⟨q, hq, _⟩ := row _ _ he
    exact ⟨q, hq.trans (mul_comm ..)⟩
  obtain ⟨q, hq⟩ := dvd
  refine ⟨q, hq.trans (mul_comm ..), mul_left_cancel₀ (C_ne_zero.mpr ha) ?_⟩
  calc
    C a * y = C c * x := h.symm
    _ = (C c * C f) * q := by rw [hq, mul_assoc]
    _ = C a * (q * C g) := by rw [← map_mul, eqn, map_mul]; ac_rfl

/-- On adjoining new variables, compare coefficients in those variables. -/
theorem row_under_rename {R σ τ : Type*} [CommRing R] [IsDomain R]
    (j : σ → τ) (hj : Function.Injective j) {a c f g : MvPolynomial σ R}
    (ha : a ≠ 0) (row : ∀ x y, c * x = a * y → ∃ q, x = q * f ∧ y = q * g)
    {x y : MvPolynomial τ R} (h : rename j c * x = rename j a * y) :
    ∃ q, x = q * rename j f ∧ y = q * rename j g := by
  classical
  let W := (Set.range j)ᶜ
  let e : W ⊕ σ ≃ τ := ((Equiv.refl W).sumCongr (Equiv.ofInjective j hj)).trans
    ((Equiv.sumComm W (Set.range j)).trans (Equiv.Set.sumCompl (Set.range j)))
  have old (s : σ) : e.symm (j s) = Sum.inr s := e.symm_apply_eq.mpr rfl
  let iso := (renameEquiv R e.symm).trans (sumAlgEquiv R W σ)
  have incl : iso.toAlgHom.comp (rename j) =
      IsScalarTower.toAlgHom R (MvPolynomial σ R) (MvPolynomial W (MvPolynomial σ R)) := by
    apply MvPolynomial.algHom_ext
    intro s
    simp only [AlgHom.comp_apply, rename_X]
    change (sumAlgEquiv R W σ) ((rename e.symm) (X (j s))) = C (X s)
    rw [rename_X, old, sumAlgEquiv_X_inr]
  have eqC (p : MvPolynomial σ R) : iso (rename j p) = C p := DFunLike.congr_fun incl p
  have he := congrArg iso h
  simp only [map_mul, eqC] at he
  obtain ⟨q, hx, hy⟩ := row_in_constants ha row he
  exact ⟨iso.symm q, iso.injective (by rw [map_mul, eqC, iso.apply_symm_apply, hx]),
    iso.injective (by rw [map_mul, eqC, iso.apply_symm_apply, hy])⟩

end MvPolynomial
