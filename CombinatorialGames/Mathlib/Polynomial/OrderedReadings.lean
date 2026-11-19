/-
Copyright (c) 2026 CombinatorialGames contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CombinatorialGames contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

import CombinatorialGames.Mathlib.FourFactorRefinement
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.Tactic.TypeStar

/-!
# Finite coordinates in a polynomial algebra
-/

public noncomputable section

namespace Algebra

open Set

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Evaluating a polynomial only uses the values of the variables that occur in it. -/
theorem eval_mem_adjoin_of_vars {R A σ : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (v : σ → A) (F : MvPolynomial σ R) (S : Set A)
    (hs : ∀ j ∈ F.vars, v j ∈ S) : MvPolynomial.aeval v F ∈ Algebra.adjoin R S := by
  obtain ⟨Q, hQ⟩ := F.exists_rename_coe_vars_eq
  rw [← hQ, MvPolynomial.aeval_rename]
  let w : F.vars → A := v ∘ Subtype.val
  have hw : Set.range w ⊆ S := by
    rintro _ ⟨j, rfl⟩
    exact hs j j.2
  apply Algebra.adjoin_mono hw
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨Q, rfl⟩

private theorem finite_readings_of_mem {S : Set A} {a : A} (ha : a ∈ adjoin R S) :
    ∃ T : Finset A, (T : Set A) ⊆ S ∧ a ∈ adjoin R (T : Set A) := by
  classical
  obtain ⟨p, rfl⟩ := exists_mvPolynomial_aeval_eq_of_mem_adjoin
    (f := ((↑) : S → A)) Subtype.range_coe.superset ha
  refine ⟨p.vars.image ((↑) : S → A), ?_, eval_mem_adjoin_of_vars _ _ _ (fun j hj ↦
    Finset.mem_image.mpr ⟨j, hj, rfl⟩)⟩
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  exact j.2

/-- A finite tuple in an independent algebra uses only finitely many of its generators. -/
theorem finite_independent_coordinates {S : Set A} (hind : AlgebraicIndependent R ((↑) : S → A))
    {n : ℕ} (z : Fin n → A) (hz : ∀ k, z k ∈ adjoin R S) :
    ∃ T : Finset A, (T : Set A) ⊆ S ∧ AlgebraicIndependent R ((↑) : ↥T → A) ∧
      ∀ k, z k ∈ adjoin R (T : Set A) := by
  classical
  choose s hs hm using fun j ↦ finite_readings_of_mem (hz j)
  let T := Finset.univ.biUnion s
  have hT : (T : Set A) ⊆ S := by
    intro x hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    exact hs j hj
  exact ⟨T, hT, AlgebraicIndependent.mono hT hind, fun j ↦
    adjoin_mono (fun _ hx ↦ Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hx⟩) (hm j)⟩

/-- Refine the equality inside the polynomial algebra on these independent readings. -/
theorem four_factors_in_adjoin {R : Type*} [CommRing R] [IsDomain R] [Algebra R A]
    {T : Finset A} (hind : AlgebraicIndependent R ((↑) : ↥T → A))
    (split : DecompositionMonoid (MvPolynomial (↥T) R)) {a b c d : A}
    (ha : a ∈ adjoin R (T : Set A)) (hb : b ∈ adjoin R (T : Set A))
    (hc : c ∈ adjoin R (T : Set A)) (hd : d ∈ adjoin R (T : Set A)) (hab : a * b = c * d) :
    ∃ e f g h : adjoin R (T : Set A), a = (e : A) * f ∧ b = (g : A) * h ∧
      c = (e : A) * g ∧ d = (f : A) * h := by
  let E := adjoin R (T : Set A)
  let iso := hind.aevalEquiv.trans (Subalgebra.equivOfEq _ E
    (congrArg (adjoin R) Subtype.range_coe))
  let : DecompositionMonoid E := MulEquiv.decompositionMonoid iso.symm
  let : IsDomain E := iso.symm.toMulEquiv.isDomain _
  have heq : (⟨a, ha⟩ : E) * ⟨b, hb⟩ = ⟨c, hc⟩ * ⟨d, hd⟩ := Subtype.ext hab
  obtain ⟨e, f, g, h, he, hf, hg, hh⟩ := DecompositionMonoid.exists_mul_eq_mul heq
  exact ⟨e, f, g, h, congrArg Subtype.val he, congrArg Subtype.val hf,
    congrArg Subtype.val hg, congrArg Subtype.val hh⟩

end Algebra

/-- An algebraically independent generating set presents an algebra as a polynomial ring. -/
noncomputable def AlgebraicIndependent.mvPolynomialAlgEquivOfAdjoinEqTop {R B : Type*} [CommRing R]
    [CommRing B] [Algebra R B] {T : Set B} (hind : AlgebraicIndependent R ((↑) : T → B))
    (htop : Algebra.adjoin R T = ⊤) : MvPolynomial T R ≃ₐ[R] B :=
  have hr : Algebra.adjoin R (Set.range ((↑) : T → B)) = ⊤ := by
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq]; exact htop
  hind.aevalEquiv.trans ((Subalgebra.equivOfEq _ _ hr).trans Subalgebra.topEquiv)
