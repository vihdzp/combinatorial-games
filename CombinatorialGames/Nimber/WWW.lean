/-
Copyright (c) 2025 Django Peeters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Django Peeters
-/
import CombinatorialGames.Nimber.SimplestExtension.Algebraic
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Logic.Function.Defs
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.SetTheory.Ordinal.CantorNormalForm

/-!
# w^(w^w) is algebraically closed

This file aims to prove that `w ^ (w ^ w)` is an algebraically closed field.
A possible follow-up is to prove that arithmetic in `w ^ (w ^ w)` is effectively computable.

The proof follows [On Numbers And Games][conway2001] (pp. 59-61),
[On The Algebraic Closure Of Two][lenstra1977] (pp. 1-8) and
[Combinatorial Games][siegel2013] (pp. 444-450).

## Todo

Formalize pp. 59-61.
Formalize pp. 1-8.
Formalize pp.444-450.
-/

universe u

open Ordinal Polynomial Function
open Nat (nth)

/-! ### Prime lemmas -/

theorem one_lt_nth_prime (k : ℕ) : 1 < nth Nat.Prime k := by
  apply lt_of_lt_of_le (b := 2) (by norm_num)
  exact le_trans (b := k + 2) (Nat.le_add_left 2 k) (Nat.add_two_le_nth_prime k)

theorem nth_prime_ne_zero (k : ℕ) : nth Nat.Prime k ≠ 0 := by
  rw [Nat.ne_zero_iff_zero_lt]
  exact lt_trans zero_lt_one (one_lt_nth_prime k)

/-! ### Field lemmas -/

#check X_pow_sub_C_splits_of_isPrimitiveRoot

theorem splits_or_irreducible_of_primitive_pth_root
  (F : Type*) [Field F]
  {p : ℕ} [Fact (Nat.Prime p)]
  (h : ∃ ζ : F, IsPrimitiveRoot ζ p) (a : F) :
  (X ^ p - C a).Splits (RingHom.id F) ∨ Irreducible (X ^ p - C a) := by
  sorry

/-! ### Finite Field lemmas -/

/- testing
theorem cuberoot_extension_iff_three_dvd_of_cubic_extension
  (K : Type*) [Field K] [Fintype K]
  (L : Type*) [Field L] [Algebra K L] (h : Module.finrank K L = 3) :
  3 ∣ Fintype.card K - 1 ↔ ∃ a : K, Irreducible (X ^ 3 - C a) := by
  sorry
-/

--noncomputable section

theorem card_units_eq_card_minus_one
  (F : Type*) [Field F] [Finite F] : Nat.card Fˣ = Nat.card F - 1 := by
  exact Nat.card_units F

theorem p_dvd_card_minus_one_iff_primitive_root
  (F : Type*) [Field F] [Finite F] {p : ℕ} [Fact (Nat.Prime p)] :
  p ∣ Nat.card F - 1 ↔ ∃ ζ : F, IsPrimitiveRoot ζ p := by
  haveI fcyclic : IsCyclic (Fˣ) := inferInstance
  let ffintype := Fintype.ofFinite F
  constructor
  · intro ⟨a, ha⟩
    have ⟨g, hg⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := Fˣ)).1 fcyclic
    use (g ^ a)
    have : (g ^ a) ^ p = 1 := by
      rw [← pow_mul, mul_comm, ← ha, ← card_units_eq_card_minus_one F]
      simp only [pow_card_eq_one']
    apply IsPrimitiveRoot.mk_of_lt _ ?_ ?_ ?_
    · exact Nat.Prime.pos Fact.out
    · rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, this, Units.val_one]
    · intro l lpos lltp h
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Units.val_eq_one] at h
      have hga := pow_gcd_eq_one (g ^ a) this h
      have hpl : p.gcd l = 1 := by
        apply Nat.gcd_eq_one_of_lt_minFac
        · exact Nat.ne_zero_iff_zero_lt.2 lpos
        · rwa [Nat.Prime.minFac_eq Fact.out]
      rw [hpl, pow_one] at hga
      have hga' := orderOf_dvd_of_pow_eq_one hga
      rw [hg, card_units_eq_card_minus_one F, ha] at hga'
      have apos : 0 < a := by
        rw [← Nat.ne_zero_iff_zero_lt]
        rintro rfl
        rw [mul_zero] at ha
        have two_le_card := IsPrimePow.two_le <| FiniteField.isPrimePow_card F
        rw [← Nat.card_eq_fintype_card] at two_le_card
        have : 1 ≤ Nat.card F := by linarith
        rw [Nat.sub_eq_iff_eq_add this, zero_add] at ha
        rw [ha] at two_le_card
        linarith
      have ⟨b, hb⟩ := hga'
      rw [mul_assoc, ← mul_one a, mul_assoc a, one_mul, mul_comm p, mul_assoc, Eq.comm] at hb
      apply Nat.mul_left_cancel apos at hb
      apply Nat.eq_one_of_mul_eq_one_left at hb
      exact Nat.Prime.ne_one Fact.out hb
  · intro ⟨ζ, hζ⟩
    have ⟨ha, hb⟩ := hζ
    let fp : Fˣ →* Fˣ := ⟨⟨fun x ↦ x ^ p, one_pow p⟩, fun x y ↦ mul_pow x y p⟩
    rw [← card_units_eq_card_minus_one F, dvd_def]
    have fp1pre : Nat.card (fp ⁻¹' {1}) = p := by
      simp only [Set.preimage, MonoidHom.coe_mk, OneHom.coe_mk, Set.mem_singleton_iff,
        Set.coe_setOf, fp]
      sorry
      /-
      haveI : Fintype (fp ⁻¹' {1}) := Fintype.ofFinite (fp ⁻¹' {1})
      haveI : Fintype (Fˣ) := Fintype.ofFinite (Fˣ)
      rw [Nat.card_eq_fintype_card]
      apply eq_of_le_of_ge
      --apply Nat.eq_of_le_of_not_gt
      · apply Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.Prime.ne_zero Fact.out))
        apply orderOf_dvd_card_of_mem
        rw [Set.mem_preimage, Set.mem_singleton_iff, MonoidHom.mem_ker]
        simp only [Units.ext_iff]
        rw [← Units.val_pow_eq_pow_val, Units.val_eq_one]
        exact ha
      · intro hgt
        have one_lt_order := Nat.Prime.one_lt_order Fact.out ha
        linarith
      -/
    have fpcount : ∀ y : fp.range, Nat.card (fp ⁻¹' {y.val}) = p := by
      intro y
      sorry
      /-
      haveI : Fintype (fp ⁻¹' {y.val}) := Fintype.ofFinite (fp ⁻¹' {y.val})
      haveI : Fintype (Fˣ) := Fintype.ofFinite (Fˣ)
      haveI : Fintype (fp.range) := Fintype.ofFinite (fp.range)
      haveI : Finite (fp.range) := inferInstance
      haveI : Finite (Fˣ) := inferInstance
      rw [Nat.card_eq_fintype_card]
      apply Finset.card_preimage_eq_of_injective_on_fiber
      · intro x hx x' hx' h
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
        rw [hx, hx'] at h
        have : x / x' ∈ fp.ker := by
          rw [MonoidHom.mem_ker, Units.ext_iff] at h ⊢
          simp only [Units.val_mul, Units.val_inv, mul_pow, one_pow, mul_one, h]
        rw [Set.mem_setOf_eq] at this
        have ker_subgroup : Subgroup fp.ker := Subgroup.ker fp
        have ker_finite : Finite fp.ker := Subgroup.finite_of_fintype ker_subgroup
        have ker_card : Nat.card fp.ker = p := by
          haveI : Fintype fp.ker := Fintype.ofFinite fp.ker
          haveI : Finite fp.ker := inferInstance
          rw [Nat.card_eq_fintype_card]
          apply Nat.eq_of_le_of_not_gt
          · apply Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.Prime.ne_zero Fact.out))
            apply orderOf_dvd_card_of_mem
            exact Subgroup.mem_ker.mp this
          · intro hgt
            have one_lt_order := Nat.Prime.one_lt_order Fact.out (Subgroup.mem_ker.mp this)
            linarith
        rw [← Units.ext_iff]
        have : x / x' ∈ fp.ker := by
          rw [Set.mem_setOf_eq]
      -/
    #check Nat.card_prod
    sorry

--end

theorem primitive_root_iff_not_surjective
  (F : Type*) [Field F] [Finite F] {p : ℕ} [Fact (Nat.Prime p)] :
  (∃ ζ : F, IsPrimitiveRoot ζ p) ↔ ¬Surjective (fun x : F ↦ x ^ p) := by
  sorry

theorem not_surjective_iff_irreducible
  (F : Type*) [Field F] [Finite F] {p : ℕ} [Fact (Nat.Prime p)] :
  ¬Surjective (fun x : F ↦ x ^ p) ↔ ∃ a : F, Irreducible (X ^ p - C a) := by
  sorry

theorem p_dvd_card_minus_one_iff_irreducible
  (F : Type*) [Field F] [Finite F] {p : ℕ} [Fact (Nat.Prime p)] :
  p ∣ Nat.card F - 1 ↔ ∃ a : F, Irreducible (X ^ p - C a) := by
  rw [p_dvd_card_minus_one_iff_primitive_root, primitive_root_iff_not_surjective,
  not_surjective_iff_irreducible]

/-! ### Main lemmas -/

noncomputable section

namespace Nimber

/- First we prove the algebraic closure. -/

/-- `kappa_q` where `q = (nth Nat.Prime k) ^ (n + 1)` -/
protected def kappa_q (k n : ℕ) : Nimber.{u} :=
  of <| 2 ^ (ω ^ k * (nth Nat.Prime k) ^ n)

protected theorem kappa_q_lt_iff_pair_lt (k n k' n' : ℕ) :
  Nimber.kappa_q k n < Nimber.kappa_q k' n' ↔ k < k' ∨ k = k' ∧ n < n' := by
  simp only [Nimber.kappa_q, OrderIso.lt_iff_lt]
  rw [opow_lt_opow_iff_right (by simp)]
  constructor
  · contrapose!
    intro ⟨h, h'⟩
    rw [le_iff_lt_or_eq] at h
    rcases h with h | rfl
    · apply le_trans (b := omega0 ^ k)
      · repeat rw [← opow_natCast]
        rw [← natCast_opow]
        apply le_of_lt
        apply omega0_opow_mul_nat_lt
        rwa [Nat.cast_lt]
      · apply Ordinal.le_mul_left
        rw [← opow_natCast]
        apply opow_pos
        rw [← Nat.cast_zero, Nat.cast_lt, Nat.pos_iff_ne_zero]
        exact nth_prime_ne_zero k
    · simp only [forall_const] at h'
      rw [Ordinal.mul_le_mul_iff_left (by rw [← opow_natCast]; exact opow_pos _ omega0_pos)]
      repeat rw [← opow_natCast, ← natCast_opow]
      rwa [Nat.cast_le, Nat.pow_le_pow_iff_right (one_lt_nth_prime k')]
  · intro h
    rcases h with h | ⟨rfl, h⟩
    · apply lt_of_lt_of_le (b := omega0 ^ k')
      · repeat rw [← opow_natCast]
        rw [← natCast_opow]
        apply omega0_opow_mul_nat_lt
        rwa [Nat.cast_lt]
      · apply Ordinal.le_mul_left
        rw [← opow_natCast]
        apply opow_pos
        rw [← Nat.cast_zero, Nat.cast_lt, Nat.pos_iff_ne_zero]
        exact nth_prime_ne_zero k'
    · rw [Ordinal.mul_lt_mul_iff_left (by rw [← opow_natCast]; exact opow_pos _ omega0_pos)]
      repeat rw [← opow_natCast, ← natCast_opow]
      rwa [Nat.cast_lt, Nat.pow_lt_pow_iff_right (one_lt_nth_prime k)]

/-- `alpha_p` where `p = nth Nat.Prime (k + 1)` -/
protected def alpha_p (k : ℕ) : Nimber.{u} :=
  sInf {x | x < Nimber.kappa_q (k + 1) 0 ∧
    ∀ y < Nimber.kappa_q (k + 1) 0, y ^ (nth Nat.Prime (k + 1)) ≠ x}

@[simp]
protected theorem alpha_p_zero : Nimber.alpha_p 0 = ∗2 := by
  sorry

theorem omega0_cubed_eq_two : (∗ω) ^ 3 = ∗2 := by
  sorry

/-- Theorem 4.5 on p. 446. -/
protected theorem kappa_q_pow_reduce :
  ∀ (k : ℕ), (Nimber.kappa_q.{u} (k + 1) 0) ^ (nth Nat.Prime (k + 1)) = Nimber.alpha_p.{u} k ∧
  (∀ (n : ℕ), (Nimber.kappa_q.{u} (k + 1) (n + 1)) ^ (nth Nat.Prime (k + 1)) =
  (Nimber.kappa_q.{u} (k + 1) n) ∧ IsField (Nimber.kappa_q.{u} (k + 1) n)) ∧
  IsNthDegreeClosed (nth Nat.Prime (k + 1)) (Nimber.kappa_q.{u} (k + 2) 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>

    sorry
  /-
  | zero =>
    simp [Nimber.kappa_q]
    rw [opow_omega0 (by simp) (by exact nat_lt_omega0 2)]
    refine ⟨omega0_cubed_eq_two, ?_, ?_⟩
    · sorry
    · sorry
  | succ k ih =>
    sorry
  -/

protected theorem kappa_q_pow_eq_alpha (k : ℕ) :
  (Nimber.kappa_q.{u} (k + 1) 0) ^ (nth Nat.Prime (k + 1)) =
  Nimber.alpha_p.{u} k := by
  exact Nimber.kappa_q_pow_reduce k |>.1

protected theorem kappa_q_pow_decrease (k n : ℕ) :
  (Nimber.kappa_q.{u} (k + 1) (n + 1)) ^ (nth Nat.Prime (k + 1)) =
  (Nimber.kappa_q.{u} (k + 1) n) := by
  exact Nimber.kappa_q_pow_reduce k |>.2.1 n |>.1

/-- Add two ordinals as nimbers. -/
scoped notation:65 x:65 "+ₙᵢₘ" y:66 => val (∗x + ∗y)

protected theorem base_two_expansion (x : Nimber.{u}) :
  (CNF 2 x.val).foldr (fun p r ↦ 2 ^ p.1 * p.2 +ₙᵢₘ r) 0 = x.val := by
  sorry

private def tau : Nimber.{u} := ∗(ω ^ (ω ^ ω))

private def tau' : Nimber.{u} :=
  sInf {x | IsAlgClosed x ∧ 1 < x}

private theorem tau'_eq_tau : tau' = tau := by
  sorry

/-- public name is more explicit -/
theorem wpow_wpow_w_first_isAlgClosed :
  sInf {x | IsAlgClosed x ∧ 1 < x} = ∗(ω ^ (ω ^ ω)) := by exact tau'_eq_tau

/- Then we prove effective arithmetic. -/

protected def field_two : Subfield Nimber := Subfield.closure ∅

protected def degree (x : Nimber.{u}) : ℕ :=
  (minpoly Nimber.field_two x).natDegree

protected def kappa (h : ℕ) : Nimber.{u} :=
  sInf {x | x < tau ∧ h ∣ Nimber.degree x}

protected theorem kappa_q_of_kappa (k n : ℕ) :
  Nimber.kappa ((nth Nat.Prime k) ^ (n + 1)) = Nimber.kappa_q k n := by
  sorry

end Nimber

end
