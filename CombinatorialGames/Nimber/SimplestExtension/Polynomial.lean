/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.Polynomial.Degree.Definitions

/-!
# Nimber polynomials

This file will contain multiple auxiliary results and definitions for working with nimber
polynomials. (Though right now it's just a stub.)
-/

universe u

open Order Polynomial

/-! ### For Mathlib-/

namespace Polynomial

variable {R : Type*} [Semiring R] {p : R[X]}

@[simp]
theorem coeffs_nonempty_iff : p.coeffs.Nonempty ↔ p ≠ 0 := by
  simp [Finset.nonempty_iff_ne_empty]

theorem natDegree_eq_zero_iff : p.natDegree = 0 ↔ p = 0 ∨ p.degree = 0 := by
  rw [p.natDegree_eq_zero_iff_degree_le_zero, le_iff_lt_or_eq, ← WithBot.coe_zero, ← bot_eq_zero',
    WithBot.lt_coe_bot, p.degree_eq_bot]

end Polynomial
