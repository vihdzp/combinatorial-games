/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Nimber.SimplestExtension.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Nimber polynomials

This file contains multiple auxiliary results and definitions for working with nimber polynomials:

- `IsField.embed`: embeds a polynomial `p : Nimber[X]` into the subfield `Iio x`, for `IsField x`.
-/

universe u

open Order Polynomial

/-! ### For Mathlib-/

-- TODO: should some of these be global?
attribute [local aesop simp] Function.update coeff_one coeff_C coeff_X

namespace Polynomial

variable {R : Type*} [Semiring R] {p : R[X]}

@[simp]
theorem coeffs_nonempty_iff : p.coeffs.Nonempty ↔ p ≠ 0 := by
  simp [Finset.nonempty_iff_ne_empty]

theorem natDegree_eq_zero_iff : p.natDegree = 0 ↔ p = 0 ∨ p.degree = 0 := by
  rw [p.natDegree_eq_zero_iff_degree_le_zero, le_iff_lt_or_eq, ← WithBot.coe_zero, ← bot_eq_zero',
    WithBot.lt_coe_bot, p.degree_eq_bot]

end Polynomial

namespace Nimber

/-! ### Basic results -/

theorem polynomial_eq_zero_of_le_one {x : Nimber} {p : Nimber[X]}
    (hx₁ : x ≤ 1) (h : ∀ k, p.coeff k < x) : p = 0 := by
  ext k; simpa using (h k).trans_le hx₁

theorem IsRing.eval_lt {x y : Nimber} (h : IsRing x) {p : Nimber[X]} (hp : ∀ k, p.coeff k < x)
    (hy : y < x) : p.eval y < x := by
  obtain hx₁ | hx₁ := le_or_gt x 1
  · have := polynomial_eq_zero_of_le_one hx₁ hp
    simp_all
  · rw [eval_eq_sum]
    exact h.sum_lt hx₁.ne_bot fun n hn ↦ h.mul_lt (hp _) (h.pow_lt hx₁ hy)

theorem coeff_X_pow_lt {x : Nimber} (n : ℕ) (h : 1 < x) : ∀ k, (X ^ n).coeff k < x := by
  have : 0 < x := h.bot_lt
  aesop

theorem IsGroup.coeff_add_lt {x : Nimber} {p q : Nimber[X]} (h : IsGroup x)
    (hp : ∀ k, p.coeff k < x) (hq : ∀ k, q.coeff k < x) : ∀ k, (p + q).coeff k < x := by
  intro k
  rw [coeff_add]
  exact h.add_lt (hp k) (hq k)

theorem IsGroup.coeff_sum_lt {x : Nimber} {ι} {f : ι → Nimber[X]} {s : Finset ι} (h : IsGroup x)
    (hx₀ : x ≠ 0) (hs : ∀ y ∈ s, ∀ k, (f y).coeff k < x) : ∀ k, (s.sum f).coeff k < x := by
  intro k
  rw [finset_sum_coeff]
  exact h.sum_lt hx₀ fun y hy ↦ (hs y hy k)

theorem IsRing.coeff_mul_lt {x : Nimber} {p q : Nimber[X]} (h : IsRing x)
    (hp : ∀ k, p.coeff k < x) (hq : ∀ k, q.coeff k < x) : ∀ k, (p * q).coeff k < x := by
  intro k
  rw [coeff_mul]
  exact h.sum_lt (hp 0).ne_bot fun y hy ↦ h.mul_lt (hp _) (hq _)

theorem IsRing.coeff_prod_lt {x : Nimber} {ι} {f : ι → Nimber[X]} {s : Finset ι} (h : IsRing x)
    (hx₁ : 1 < x) (hs : ∀ y ∈ s, ∀ k, (f y).coeff k < x) : ∀ k, (s.prod f).coeff k < x := by
  classical
  induction s using Finset.induction with
  | empty =>
    have := zero_lt_one.trans hx₁
    aesop
  | insert y s hy IH =>
    rw [Finset.prod_insert hy]
    apply h.coeff_mul_lt <;> aesop

/-! ### Embedding in a subfield -/

/-- Reinterpret a polynomial in the nimbers as a polynomial in the subfield `x`.

We could define this under the weaker assumption `IsRing`, but due to proof erasure, this leads to
issues where `Field (h.toSubring ⋯)` can't be inferred, even if `h : IsField x`. -/
def IsField.embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) (p : Nimber[X])
    (hp : ∀ k, p.coeff k < x) : (h.toSubfield hx₁)[X] :=
  .ofFinsupp <| .mk p.support (fun k ↦ ⟨p.coeff k, hp k⟩) (by simp [← Subtype.val_inj])

@[simp]
theorem IsField.coeff_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) (k : ℕ) : (h.embed hx₁ p hp).coeff k = ⟨p.coeff k, hp k⟩ :=
  rfl

@[simp]
theorem IsField.degree_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) : (h.embed hx₁ p hp).degree = p.degree :=
  rfl

@[simp]
theorem IsField.leadingCoeff_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) : (h.embed hx₁ p hp).leadingCoeff = ⟨p.leadingCoeff, hp _⟩ :=
  rfl

@[simp]
theorem IsField.map_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) : (h.embed hx₁ p hp).map (Subfield.subtype _) = p := by
  ext; simp

@[simp]
theorem IsField.embed_C {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {y hy} :
    h.embed hx₁ (C y) hy = C ⟨y, by simpa using hy 0⟩ := by
  ext
  simp_rw [h.coeff_embed, coeff_C]
  split_ifs <;> rfl

@[simp]
theorem IsField.eval_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) (y) : (h.embed hx₁ p hp).eval y = ⟨_, h.eval_lt hp y.2⟩ := by
  simp [← Subtype.val_inj, embed, sum, eval_eq_sum]

end Nimber
