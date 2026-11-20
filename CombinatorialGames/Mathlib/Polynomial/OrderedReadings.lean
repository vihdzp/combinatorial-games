/-
Copyright (c) 2026 CombinatorialGames contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CombinatorialGames contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.Order.Prod.Lex.Basic

import CombinatorialGames.Mathlib.FourFactorRefinement
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.Data.Finset.Max
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.TypeStar

/-!
# Polynomial coordinates from ordered readings

Read the entries in order, and read each entry from higher precision to lower precision.
Keep exactly the values outside the algebra of all preceding values. A polynomial relation
uses finitely many readings and therefore has a last one. For spanning, a first reading
missing from the generated algebra would itself have been kept.
-/

public noncomputable section

namespace Algebra

open Set

variable {R A ι P : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [LinearOrder ι] [WellFoundedLT ι] [LinearOrder P]

/-- Entries already visited, including the higher precisions of the current entry. -/
def earlierReadings (v : ι → P → A) (i : ι) (t : P) : Set A :=
  {a | ∃ j s, (j < i ∨ j = i ∧ t < s) ∧ v j s = a}

omit [CommRing A] [WellFoundedLT ι] in
theorem mem_earlierReadings {v : ι → P → A} {i : ι} {t : P} {a : A} :
    a ∈ earlierReadings v i t ↔ ∃ j s, (j < i ∨ j = i ∧ t < s) ∧ v j s = a := Iff.rfl

/-- Readings whose predecessors cannot express them as a polynomial. -/
def selectedReadings (R : Type*) [CommRing R] [Algebra R A] (v : ι → P → A) : Set A :=
  {a | ∃ i t, v i t ∉ adjoin R (earlierReadings v i t) ∧ v i t = a}

omit [WellFoundedLT ι] in
theorem mem_selectedReadings {v : ι → P → A} {a : A} :
    a ∈ selectedReadings R v ↔ ∃ i t, v i t ∉ adjoin R (earlierReadings v i t) ∧ v i t = a :=
  Iff.rfl

omit [CommRing A] [WellFoundedLT ι] in
theorem earlierReadings_of_isBot (v : ι → P → A) {i : ι} (hi : IsBot i) (t : P) :
    earlierReadings v i t = v i '' Ioi t := by
  ext a
  constructor
  · rintro ⟨j, s, hj | ⟨rfl, hs⟩, rfl⟩
    · exact (hj.not_ge (hi j)).elim
    · exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨i, s, Or.inr ⟨rfl, hs⟩, rfl⟩

private theorem independent_of_earlier {J : Type*} [LinearOrder J] (v : J → A)
    (hinj : Function.Injective (algebraMap R A))
    (h : ∀ j, Transcendental (adjoin R (v '' Iio j)) (v j)) : AlgebraicIndependent R v := by
  classical
  apply algebraicIndependent_of_finite_type
  intro t hfin
  suffices aux : ∀ s : Finset J, AlgebraicIndepOn R v (s : Set J) by
    simpa using aux hfin.toFinset
  intro s
  induction s using Finset.induction_on_max with
  | empty =>
    rw [Finset.coe_empty]
    exact algebraicIndependent_empty_type_iff.mpr hinj
  | insert j s hsj ih =>
    rw [Finset.coe_insert]
    exact ih.insert ((h j).of_tower_top_of_subalgebra_le
      (adjoin_mono (image_mono fun k hk ↦ hsj k hk)))

/-- Determine the polynomial generators from the readings of the specified entries.
The first-missing hypothesis concerns one entry at a time. -/
theorem independent_ordered_readings [Nontrivial R] (v : ι → P → A)
    (hinj : Function.Injective (algebraMap R A))
    (hrigid : ∀ i t, let E := adjoin R (earlierReadings v i t)
      v i t ∉ E → Transcendental E (v i t))
    (hfirst : ∀ (E : Subalgebra R A) i, (∃ t, v i t ∉ E) →
      ∃ t, v i t ∉ E ∧ ∀ s, t < s → v i s ∈ E) :
    AlgebraicIndependent R ((↑) : selectedReadings R v → A) ∧
      ∀ i t, v i t ∈ adjoin R (selectedReadings R v) := by
  let J := ι ×ₗ Pᵒᵈ
  let read (j : J) := v (ofLex j).1 (OrderDual.ofDual (ofLex j).2)
  let fresh := {j : J | read j ∉ adjoin R (earlierReadings v (ofLex j).1 (ofLex j).2)}
  let w (j : fresh) := read j.1
  have hind : AlgebraicIndependent R w := by
    apply independent_of_earlier w hinj
    intro j
    apply (hrigid _ _ j.2).of_tower_top_of_subalgebra_le
    apply adjoin_mono
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨(ofLex k.1).1, (ofLex k.1).2, Prod.Lex.lt_iff.mp hk, rfl⟩
  have heq : range w = selectedReadings R v := by
    ext a
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, _, j.2, rfl⟩
    · rintro ⟨i, t, hnew, rfl⟩
      exact ⟨⟨toLex (i, OrderDual.toDual t), hnew⟩, rfl⟩
  rw [← heq]
  refine ⟨(algebraicIndependent_subtype_range hind.injective).mpr hind, ?_⟩
  let E := adjoin R (range w)
  intro i
  have wf : WellFounded ((· < ·) : ι → ι → Prop) := wellFounded_lt
  induction i using wf.induction with
  | h i ih =>
    by_contra! hmiss
    obtain ⟨t, ht, hprev⟩ := hfirst E i hmiss
    have hle : adjoin R (earlierReadings v i t) ≤ E := by
      apply adjoin_le
      rintro _ ⟨j, s, hji | ⟨rfl, hts⟩, rfl⟩
      · exact ih j hji s
      · exact hprev s hts
    have hj : toLex (i, OrderDual.toDual t) ∈ fresh := fun h ↦ ht (hle h)
    exact ht (subset_adjoin ⟨⟨_, hj⟩, rfl⟩)

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
