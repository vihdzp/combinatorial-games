/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Subring.Defs

import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.TypeStar

/-!
# Additive images of polynomial values

An additive map with prescribed images for translated powers sends the value of a polynomial
to the value of a polynomial of at most the same degree. When the input polynomial is monic,
translation also gives the penultimate coefficient.
-/

public section

namespace Polynomial

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Suppose an additive map takes coefficients in `D` into `S`. If each positive power
of `x` can be translated by a coefficient so that reading it gives a translated power of `z`,
polynomial values at `x` are read by polynomials over `S` at `z`.
For monic input the translation records the penultimate coefficient as well. -/
theorem exists_eval₂_eq_of_translated_powers
    (D : Subring A) (S : Subring B) (T : A →+ B) (x : A) (z : B)
    (hD : ∀ c : D, T c ∈ S)
    (hshift : ∀ (c : D) (n : ℕ), 0 < n → ∃ (a : D) (w : S), T a = T x ∧
      (w = 0 ∨ T 1 = 0) ∧ T ((c : A) * (x - a) ^ n) = T c * (z - w) ^ n)
    (n : ℕ) (F : D[X]) (hF : F.natDegree ≤ n) :
    ∃ f : S[X], f.natDegree ≤ n ∧ f.eval₂ S.subtype z = T (F.eval₂ D.subtype x) ∧
      (f.coeff n : B) = T (F.coeff n) ∧
      (0 < n → F.coeff n = 1 → (f.coeff (n - 1) : B) = T (F.coeff (n - 1)) + n • T x) := by
  classical
  induction n generalizing F with
  | zero =>
    have hv : F.eval₂ D.subtype x = (F.coeff 0 : A) :=
      (congrArg (eval₂ D.subtype x) (eq_C_of_natDegree_le_zero hF)).trans (eval₂_C ..)
    exact ⟨C ⟨_, hD (F.coeff 0)⟩, by simp, by simp [hv], by simp, by simp⟩
  | succ n ih =>
    let c := F.coeff (n + 1)
    obtain ⟨a, w, ha, hw, hpower⟩ := hshift c (n + 1) (Nat.succ_pos _)
    let L : D[X] := C c * (X + C (-a)) ^ (n + 1)
    let R := F - L
    have hL (j : ℕ) : L.coeff j = c * ((-a) ^ (n + 1 - j) * (n + 1).choose j) := by
      rw [show L = _ from rfl, coeff_C_mul, coeff_X_add_C_pow]
    have hR : R.natDegree ≤ n := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro j hj
      rw [show R = F - L from rfl, coeff_sub]
      rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hj) with rfl | hlt
      · simp [hL, c]
      · simp [hL, coeff_eq_zero_of_natDegree_lt (hF.trans_lt hlt), Nat.choose_eq_zero_of_lt hlt]
    obtain ⟨g, hgdeg, hgeval, hgcoeff, _⟩ := ih R hR
    let b : S := ⟨T c, hD c⟩
    let M : S[X] := C b * (X + C (-w)) ^ (n + 1)
    have hM (j : ℕ) : M.coeff j = b * ((-w) ^ (n + 1 - j) * (n + 1).choose j) := by
      rw [show M = _ from rfl, coeff_C_mul, coeff_X_add_C_pow]
    refine ⟨M + g, natDegree_add_le_of_degree_le ?_ (hgdeg.trans (Nat.le_succ _)), ?_, ?_, ?_⟩
    · exact natDegree_le_iff_coeff_eq_zero.mpr fun j hj ↦
        by simp [hM, Nat.choose_eq_zero_of_lt hj]
    · have hLeval : L.eval₂ D.subtype x = (c : A) * (x - a) ^ (n + 1) := by
        simp [L, eval₂_pow, sub_eq_add_neg]
      have hReval : R.eval₂ D.subtype x = F.eval₂ D.subtype x - L.eval₂ D.subtype x :=
        eval₂_sub _
      have hMeval : M.eval₂ S.subtype z = (b : B) * (z - w) ^ (n + 1) := by
        simp [M, eval₂_pow, sub_eq_add_neg]
      rw [eval₂_add, hMeval, hgeval, hReval, map_sub, hLeval, hpower]
      exact add_sub_cancel _ _
    · simp [hM, coeff_eq_zero_of_natDegree_lt (hgdeg.trans_lt (Nat.lt_succ_self _)), b, c]
    · intro _ hmonic
      have hMn : M.coeff n = 0 := by
        rcases hw with rfl | hzero
        · simp [hM]
        · have hb : b = 0 := Subtype.ext (by
            simpa only [b, c, hmonic, Subring.coe_one, Subring.coe_zero] using hzero)
          simp [hM, hb]
      have hnext : R.coeff n = F.coeff n + (n + 1) • a := by
        rw [show R = _ from rfl, coeff_sub, hL]
        simp [c, hmonic, Nat.choose_succ_self_right, nsmul_eq_mul, mul_comm]
      have hs : (((n + 1) • a : D) : A) = (n + 1) • (a : A) :=
        D.subtype.toAddMonoidHom.map_nsmul (n + 1) a
      simpa only [Nat.add_sub_cancel, coeff_add, hMn,
        zero_add, hnext, Subring.coe_add, hs, map_add, map_nsmul, ha] using hgcoeff

end Polynomial
