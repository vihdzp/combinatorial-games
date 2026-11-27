/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Scale.Rounding
public import Mathlib.Algebra.MonoidAlgebra.Defs

import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Tactic.TypeStar

/-!
# Finite sums of distinct scale leaders

Over the residue field, evaluation of a finite sum of leaders at distinct fixed exponents is
faithful. Rounding at the largest exponent in a nonempty support recovers its coefficient.
-/

universe u

public noncomputable section

namespace Surreal

variable (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex]
variable {M : Type*} [AddCommMonoid M] (j : M →+ Surreal.{u})

/-- Evaluate each exponent at its Conway monomial, with coefficients in the residue field. -/
def leaderEvaluation (j : M →+ Surreal.{u}) :
    AddMonoidAlgebra (residueSubfield C) M →+* Surreal.{u} :=
  AddMonoidAlgebra.liftNCRingHom (residueSubfield C).subtype
    { toFun := fun t : Multiplicative M ↦ ω^ (j t.toAdd)
      map_one' := by change ω^ (j 0) = 1; rw [map_zero, wpow_zero]
      map_mul' := fun s t ↦ by
        change ω^ (j (s.toAdd + t.toAdd)) = ω^ (j s.toAdd) * ω^ (j t.toAdd)
        rw [map_add, wpow_add] }
    (fun _ _ ↦ Commute.all ..)

@[simp]
theorem leaderEvaluation_single (m : M) (k : residueSubfield C) :
    leaderEvaluation C j (AddMonoidAlgebra.single m k) = (k : Surreal) * ω^ (j m) := by
  rw [leaderEvaluation, AddMonoidAlgebra.liftNCRingHom_single]
  rfl

theorem leaderEvaluation_apply (p : AddMonoidAlgebra (residueSubfield C) M) :
    leaderEvaluation C j p = ∑ m ∈ p.coeff.support, (p.coeff m : Surreal) * ω^ (j m) := (rfl)

private theorem roundAt_mul_wpow_self (t : Surreal.{u}) (k : residueSubfield C) :
    roundAt C t ((k : Surreal) * ω^ t) = k := by
  rw [roundAt_eq, mul_div_cancel_right₀ _ (wpow_ne_zero _)]
  exact (mem_residueRepresentatives_iff C).mp ((mem_residueSubfield_iff C).mp k.2).1

/-- Above a monomial's fixed exponent its rescaled rounding is zero. -/
theorem roundAt_mul_wpow_eq_zero {s t : Surreal.{u}} (hst : s < t)
    (hs : cosetRep (unitExponentSubgroup C) s = s)
    (ht : cosetRep (unitExponentSubgroup C) t = t) (k : residueSubfield C) :
    roundAt C t ((k : Surreal) * ω^ s) = 0 := by
  rcases eq_or_ne (k : Surreal) 0 with hk | hk
  · simp [hk, roundAt_eq]
  have h₀ : precisionLevel C (k : Surreal) = 0 := by
    apply (div_wpow_mem_subring_and_inv_iff C hk (cosetRep_zero _)).mp
    simp only [wpow_zero, div_one]
    exact ⟨((mem_residueSubfield_iff C).mp k.2).2,
      ((mem_residueSubfield_iff C).mp (k⁻¹ : residueSubfield C).2).2⟩
  rw [roundAt_eq, cosetRep_eq_zero_iff]
  apply (div_wpow_mem_infinitesimals_iff C (mul_ne_zero hk (wpow_ne_zero s)) ht).mpr
  simpa only [precisionLevel_mul C hk (wpow_ne_zero s), precisionLevel_wpow, hs, h₀, zero_add]

/-- Below a monomial's exponent, rescaled rounding subtracts the precision from its exponent. -/
theorem roundAt_mul_wpow_of_le {s t : Surreal.{u}} (hts : t ≤ s) (k : residueSubfield C) :
    roundAt C t ((k : Surreal) * ω^ s) = (k : Surreal) * ω^ (s - t) := by
  rw [roundAt_eq, mul_div_assoc, ← wpow_sub]
  apply (mem_residueRepresentatives_iff C).mp
  rw [mul_comm]
  exact wpow_mul_mem_residueRepresentatives C (sub_nonneg.mpr hts)
    ((mem_residueSubfield_iff C).mp k.2).1

/-- Distinct simplicity representatives of exponent classes give linearly independent monomials
over the residue field. -/
theorem leaderEvaluation_injective [LinearOrder M] (hj : StrictMono j)
    (hfix : ∀ m, cosetRep (unitExponentSubgroup C) (j m) = j m) :
    Function.Injective (leaderEvaluation C j) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro p hp
  by_contra h
  have hS : p.coeff.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr (AddMonoidAlgebra.coeff_eq_zero.not.mpr h)
  let t := p.coeff.support.max' hS
  have ht : t ∈ p.coeff.support := Finset.max'_mem _ hS
  let T : Surreal.{u} →+ Surreal.{u} :=
    { toFun := roundAt C (j t)
      map_zero' := by simp [roundAt_eq]
      map_add' := roundAt_add C (j t) }
  have read : T (leaderEvaluation C j p) = (p.coeff t : Surreal) := by
    rw [leaderEvaluation_apply, map_sum]
    refine (Finset.sum_eq_single_of_mem t ht (fun b hb hbt ↦ ?_)).trans
      (roundAt_mul_wpow_self C (j t) (p.coeff t))
    exact roundAt_mul_wpow_eq_zero C (hj ((Finset.le_max' _ _ hb).lt_of_ne hbt))
      (hfix b) (hfix t) _
  have hc : (p.coeff t : Surreal) = 0 := by rw [← read, hp, map_zero]
  exact (Finsupp.mem_support_iff.mp ht) (Subtype.ext hc)

end Surreal
