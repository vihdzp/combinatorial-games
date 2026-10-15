/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.SetTheory.Cardinal.Finsupp

import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Cardinal of algebraic closure

TODO: these results can be stated and proven in greater generality, and should be upstreamed.
-/

open Cardinal Polynomial

universe u

variable {E F : Type u} [Field E] [Field F] [Algebra E F]

@[simp]
theorem mk_polynomial : #E[X] = max ℵ₀ #E := by
  let e : E[X] ≃ (ℕ →₀ E) :=
    (Polynomial.toFinsuppIso E).toEquiv.trans AddMonoidAlgebra.coeffEquiv
  rw [e.cardinal_eq]
  simp

public theorem Cardinal.mk_setOfPred_isIntegral_le :
    #{y : F | IsAlgebraic E y} ≤ max ℵ₀ #E := by
  trans #(⋃₀ Set.range fun p : E[X] ↦ {x | x ∈ p.aroots F})
  · apply Cardinal.mk_le_mk_of_subset
    rintro x ⟨p, hp₀, hp⟩
    aesop
  trans #E[X] * ℵ₀
  · apply (mk_sUnion_le _).trans (mul_le_mul' mk_range_le <| ciSup_le _)
    rintro ⟨_, ⟨p, rfl⟩⟩
    apply le_of_lt
    rw [lt_aleph0_iff_finite]
    exact Multiset.finite_toSet _
  · simp
