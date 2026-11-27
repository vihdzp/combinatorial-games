/-
Copyright (c) 2026 CombinatorialGames contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CombinatorialGames contributors
-/
module

public import CombinatorialGames.Surreal.Scale.Bounded.Readings

import CombinatorialGames.Mathlib.Polynomial.GeneratingRows
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation

/-!
# The least row on a bounded line

The readings of the product of the coordinates contain both coordinates and every divisor.
Find a generating row there. Every further point on the line is a multiple of it,
so its horizontal level is least. Normalize its leading reading to one. Rounding a
quotient by this row leaves no smaller nonzero point on the line.
-/

universe u

public noncomputable section

open Set

namespace Surreal

variable (i : Surreal.{u})
local notation "V" => boundedResidueRepresentatives i
local notation "L" => boundedLeaderSubring i
local notation "C₋" => lowerGrowthSubring i
local notation "Δ" => boundedPrecision i

private theorem vars_of_nonzero_product {σ R : Type*} [CommRing R] [IsDomain R]
    (Y Z : MvPolynomial σ R) (hY : Y ≠ 0) (hZ : Z ≠ 0) :
    ∀ j, j ∈ Y.vars ∨ j ∈ Z.vars → j ∈ (Y * Z).vars := by
  classical
  simp only [MvPolynomial.vars_def, MvPolynomial.degrees_mul_eq hY hZ,
    Multiset.mem_toFinset, Multiset.mem_add]
  exact fun _ h ↦ h

private theorem factors_mem_adjoin_vars {R A : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [Algebra R A] {T B : Set A} (hTB : T ⊆ B) (hB : AlgebraicIndependent R ((↑) : B → A))
    (P : MvPolynomial T R) {y z : A} (hy : y ∈ Algebra.adjoin R B)
    (hz : z ∈ Algebra.adjoin R B) (hyz : y * z = MvPolynomial.aeval ((↑) : T → A) P)
    (hn : y * z ≠ 0) (S : Set A) (hS : ∀ j ∈ P.vars, (j : A) ∈ S) :
    y ∈ Algebra.adjoin R S ∧ z ∈ Algebra.adjoin R S := by
  classical
  obtain ⟨Y, hY⟩ := Algebra.exists_mvPolynomial_aeval_eq_of_mem_adjoin
    (f := ((↑) : B → A)) Subtype.range_coe.superset hy
  obtain ⟨Z, hZ⟩ := Algebra.exists_mvPolynomial_aeval_eq_of_mem_adjoin
    (f := ((↑) : B → A)) Subtype.range_coe.superset hz
  let f : T → B := Set.inclusion hTB
  have hproduct : Y * Z = MvPolynomial.rename f P := by
    apply algebraicIndependent_iff_injective_aeval.mp hB
    rw [map_mul, hY, hZ, MvPolynomial.aeval_rename]
    exact hyz
  have hprod_ne : Y * Z ≠ 0 := by
    intro e
    apply hn
    rw [← hY, ← hZ, ← map_mul, e, map_zero]
  obtain ⟨hYn, hZn⟩ := mul_ne_zero_iff.mp hprod_ne
  have hs (j : B) (hj : j ∈ Y.vars ∨ j ∈ Z.vars) : (j : A) ∈ S := by
    have hmid := vars_of_nonzero_product Y Z hYn hZn j hj
    rw [hproduct] at hmid
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ((MvPolynomial.vars_rename f P) hmid)
    exact hS k hk
  rw [← hY, ← hZ]
  exact ⟨Algebra.eval_mem_adjoin_of_vars ((↑) : B → A) Y S (fun j hj ↦ hs j (.inl hj)),
    Algebra.eval_mem_adjoin_of_vars ((↑) : B → A) Z S (fun j hj ↦ hs j (.inr hj))⟩

private theorem extend_product_readings (p x y : V) :
    ∃ T : Set V,
      Algebra.selectedReadings L (boundedReadings i (fun _ : Fin 1 ↦ p)) ⊆ T ∧
      AlgebraicIndependent L ((↑) : T → V) ∧ x ∈ Algebra.adjoin L T ∧ y ∈ Algebra.adjoin L T := by
  let z : Fin 3 → V := ![p, x, y]
  let read := boundedReadings i z
  obtain ⟨hind, hall⟩ := independent_bounded_readings i z
  have entry (k : Fin 3) : z k ∈ Algebra.adjoin L (Algebra.selectedReadings L read) := by
    simpa only [boundedReadings, boundedRound_zero] using hall k ⟨0, zero_mem_boundedPrecision i⟩
  refine ⟨_, ?_, hind, entry 1, entry 2⟩
  intro v hv
  obtain ⟨j, t, hnew, he⟩ := Algebra.mem_selectedReadings.mp hv
  obtain rfl : j = 0 := Subsingleton.elim _ _
  refine Algebra.mem_selectedReadings.mpr ⟨(0 : Fin 3), t, ?_, he⟩
  rw [Algebra.earlierReadings_of_isBot read (fun k ↦ Fin.zero_le k) t]
  rw [Algebra.earlierReadings_of_isBot _ (fun k ↦ Fin.zero_le k) t] at hnew
  exact hnew

private theorem divisor_coordinates (p : V) (hp : p ≠ 0) :
    ∃ S : Finset V, (∀ x ∈ S, ∃ t : Δ, boundedRound i ((mem_boundedPrecision i).mp t.2).1 p = x) ∧
      (S : Set V) ⊆ Algebra.selectedReadings L (boundedReadings i (fun _ : Fin 1 ↦ p)) ∧
      AlgebraicIndependent L ((↑) : ↥S → V) ∧ ∀ y z : V, y * z = p →
        y ∈ Algebra.adjoin L (S : Set V) ∧ z ∈ Algebra.adjoin L (S : Set V) := by
  classical
  let start := boundedReadings i (fun _ : Fin 1 ↦ p)
  let T := Algebra.selectedReadings L start
  obtain ⟨hind, hspan⟩ := independent_bounded_readings i (fun _ : Fin 1 ↦ p)
  have hpT : p ∈ Algebra.adjoin L T := by
    simpa only [boundedReadings, boundedRound_zero] using hspan 0 ⟨0, zero_mem_boundedPrecision i⟩
  obtain ⟨P, hP⟩ := Algebra.exists_mvPolynomial_aeval_eq_of_mem_adjoin
    (f := ((↑) : T → V)) Subtype.range_coe.superset hpT
  let S := P.vars.image ((↑) : T → V)
  have hST : (S : Set V) ⊆ T := by
    rintro s hs
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
    exact j.2
  refine ⟨S, ?_, hST, AlgebraicIndependent.mono hST hind, ?_⟩
  · intro s hs
    obtain ⟨j, t, _, he⟩ := Algebra.mem_selectedReadings.mp (hST hs)
    exact ⟨t, he⟩
  · intro y z hyz
    obtain ⟨B, sub, hB, hy, hz⟩ := extend_product_readings i p y z
    exact factors_mem_adjoin_vars sub hB P hy hz (hyz.trans hP.symm)
      (hyz ▸ hp) S (fun j hj ↦ Finset.mem_image.mpr ⟨j, hj, rfl⟩)

/-- Finitely many independent readings of a nonzero bounded product contain every
bounded divisor in their polynomial algebra. The readings depend only on the product. -/
theorem finite_bounded_readings_capture_divisors (p : V) (hp : p ≠ 0) :
    ∃ S : Finset V, (∀ x ∈ S, ∃ t : Δ, boundedRound i ((mem_boundedPrecision i).mp t.2).1 p = x) ∧
      AlgebraicIndependent L ((↑) : ↥S → V) ∧ ∀ y z : V, y * z = p →
        y ∈ Algebra.adjoin L (S : Set V) ∧ z ∈ Algebra.adjoin L (S : Set V) := by
  obtain ⟨S, read, _, hind, hall⟩ := divisor_coordinates i p hp
  exact ⟨S, read, hind, hall⟩

private theorem adjoin_row {T : Set V} (hi : AlgebraicIndependent L ((↑) : T → V))
    {a c : V} (ha : a ≠ 0) (haT : a ∈ Algebra.adjoin L T) (hcT : c ∈ Algebra.adjoin L T)
    (extend : ∀ x y : V, ∃ B : Set V, T ⊆ B ∧ AlgebraicIndependent L ((↑) : B → V) ∧
      x ∈ Algebra.adjoin L B ∧ y ∈ Algebra.adjoin L B) :
    ∃ f g : V, f ≠ 0 ∧ ∀ x y : V, c * x = a * y → ∃ q, x = q * f ∧ y = q * g := by
  let φ := MvPolynomial.aeval (R := L) ((↑) : T → V)
  obtain ⟨A, hA⟩ := Algebra.exists_mvPolynomial_aeval_eq_of_mem_adjoin
    (f := ((↑) : T → V)) Subtype.range_coe.superset haT
  obtain ⟨C, hC⟩ := Algebra.exists_mvPolynomial_aeval_eq_of_mem_adjoin
    (f := ((↑) : T → V)) Subtype.range_coe.superset hcT
  have hn : A ≠ 0 := fun e ↦ ha (hA.symm.trans (by rw [e, map_zero]))
  obtain ⟨F, G, hf, row⟩ := generating_rows_boundedLeaders i T A C hn
  refine ⟨φ F, φ G, (map_ne_zero_iff _ (algebraicIndependent_iff_injective_aeval.mp hi)).mpr hf,
    fun x y he ↦ ?_⟩
  obtain ⟨B, sub, hB, hx, hy⟩ := extend x y
  let j := Set.inclusion sub
  let ψ := MvPolynomial.aeval (R := L) ((↑) : B → V)
  obtain ⟨X, hX⟩ := Algebra.exists_mvPolynomial_aeval_eq_of_mem_adjoin
    (f := ((↑) : B → V)) Subtype.range_coe.superset hx
  obtain ⟨Y, hY⟩ := Algebra.exists_mvPolynomial_aeval_eq_of_mem_adjoin
    (f := ((↑) : B → V)) Subtype.range_coe.superset hy
  have eqn (v : MvPolynomial T L) : ψ (MvPolynomial.rename j v) = φ v :=
    MvPolynomial.aeval_rename ..
  have h : MvPolynomial.rename j C * X = MvPolynomial.rename j A * Y :=
    algebraicIndependent_iff_injective_aeval.mp hB (show ψ _ = ψ _ by
      simp only [map_mul, eqn, φ, ψ, hA, hC, hX, hY, he])
  obtain ⟨Q, hx, hy⟩ := MvPolynomial.row_under_rename j (Set.inclusion_injective sub) hn row h
  exact ⟨ψ Q, hX.symm.trans ((congrArg ψ hx).trans (by rw [map_mul, eqn])),
    hY.symm.trans ((congrArg ψ hy).trans (by rw [map_mul, eqn]))⟩

/-- A row chosen using the readings of the first point serves every other bounded point. -/
theorem generating_row_from_first_point : HasGeneratingRows V := by
  intro a c ha
  by_cases hc : c = 0
  · subst c
    exact ⟨1, 0, one_ne_zero, fun x y h ↦ ⟨x, (mul_one _).symm, by
      rw [mul_zero]; exact (mul_eq_zero.mp ((zero_mul x).symm.trans h).symm).resolve_left ha⟩⟩
  obtain ⟨S, _, sub, hind, capture⟩ := divisor_coordinates i (a * c) (mul_ne_zero ha hc)
  obtain ⟨hA, hC⟩ := capture a c rfl
  apply adjoin_row i hind ha hA hC
  intro x y
  obtain ⟨B, hB, ind, hx, hy⟩ := extend_product_readings i (a * c) x y
  exact ⟨B, sub.trans hB, ind, hx, hy⟩

/-- On a bounded line a row has smallest leading level exactly when every point on the line
is its multiple. The multiplier is the simplest representative of the horizontal quotient. -/
theorem least_level_row_iff_rounded_multiples {a c f g : V} (ha : a ≠ 0) (hf : f ≠ 0)
    (hfg : c * f = a * g) :
    (∀ x y : V, x ≠ 0 → c * x = a * y → precisionLevel C₋ f ≤ precisionLevel C₋ x) ↔
    ∀ x y : V, c * x = a * y →
      ∃ q : V, (q : Surreal) = cosetRep (infinitesimals C₋) ((x : Surreal) / f) ∧
        x = q * f ∧ y = q * g := by
  have hf₀ : (f : Surreal) ≠ 0 := fun e ↦ hf (Subtype.ext e)
  constructor
  · intro least x y hxy
    let z := (x : Surreal) / f
    have hfinv : (f : Surreal)⁻¹ ∈ C₋ := ((notMem_infinitesimals_iff C₋).mp fun h ↦ hf₀
      (eq_zero_of_mem_residueRepresentatives_of_mem_infinitesimals C₋
        ((mem_boundedResidueRepresentatives i).mp f.2).1 h)).2
    have hz : z ∈ upperGrowthSubring i := by
      exact (upperGrowthSubring i).mul_mem ((mem_boundedResidueRepresentatives i).mp x.2).2
        (lowerGrowthSubring_le_upperGrowthSubring i hfinv)
    have gap := sub_cosetRep_mem (infinitesimals C₋) z
    let q : V := ⟨cosetRep (infinitesimals C₋) z, (mem_boundedResidueRepresentatives i).mpr
      ⟨cosetRep_mem_residueRepresentatives C₋ z, by
        simpa only [sub_sub_cancel] using (upperGrowthSubring i).sub_mem hz
          (lowerGrowthSubring_le_upperGrowthSubring i (infinitesimals_le C₋ gap))⟩⟩
    have line : c * (x - q * f) = a * (y - q * g) := by linear_combination hxy - q * hfg
    have zero : x - q * f = 0 := by
      by_contra hn
      have hr : ((x : Surreal) - (q : Surreal) * f) ≠ 0 := fun e ↦ hn (Subtype.ext e)
      have hdiv : ((x : Surreal) - (q : Surreal) * f) / f ∈ infinitesimals C₋ := by
        rw [sub_div, mul_div_cancel_right₀ _ hf₀]
        exact gap
      have hlt := (div_wpow_mem_infinitesimals_iff C₋ (div_ne_zero hr hf₀)
        (cosetRep_zero _)).mp (by simpa only [wpow_zero, div_one] using hdiv)
      rw [precisionLevel_div C₋ hr hf₀, sub_neg] at hlt
      have lower := least (x - q * f) (y - q * g) hn line
      exact hlt.not_ge lower
    rw [zero, mul_zero, eq_comm, mul_eq_zero] at line
    exact ⟨q, rfl, sub_eq_zero.mp zero, sub_eq_zero.mp (line.resolve_left ha)⟩
  · intro generates x y hx hxy
    obtain ⟨q, _, eqn, _⟩ := generates x y hxy
    have hq : (q : Surreal) ≠ 0 := by
      intro h
      exact hx (by rw [eqn, show q = 0 from Subtype.ext h, zero_mul])
    rw [eqn, Subring.coe_mul, precisionLevel_mul C₋ hq hf₀]
    exact le_add_of_nonneg_left (precisionLevel_nonneg_of_mem_residueRepresentatives C₋
      ((mem_boundedResidueRepresentatives i).mp q.2).1 hq)

private theorem exists_least_level_row {a c : V} (ha : a ≠ 0) :
    ∃ f g : V, f ≠ 0 ∧ c * f = a * g ∧ ∀ x y : V, x ≠ 0 → c * x = a * y →
      precisionLevel C₋ f ≤ precisionLevel C₋ x := by
  obtain ⟨f, g, hf, row⟩ := generating_row_from_first_point i a c ha
  obtain ⟨k, hk, hk'⟩ := row a c (mul_comm ..)
  have line : c * f = a * g := by rw [hk, hk']; ac_rfl
  have least : ∀ x y : V, x ≠ 0 → c * x = a * y → precisionLevel C₋ f ≤ precisionLevel C₋ x := by
    intro x y hx he
    obtain ⟨q, eqn, _⟩ := row x y he
    have hn : (q : Surreal) ≠ 0 := fun hz ↦ hx (by
      rw [eqn, show q = 0 from Subtype.ext hz, zero_mul])
    rw [eqn, Subring.coe_mul, precisionLevel_mul _ hn (fun e ↦ hf (Subtype.ext e))]
    exact le_add_of_nonneg_left (precisionLevel_nonneg_of_mem_residueRepresentatives _
      ((mem_boundedResidueRepresentatives i).mp q.2).1 hn)
  exact ⟨f, g, hf, line, least⟩

private theorem scalar_reading (k : residueSubfield C₋) (t x : Surreal.{u}) :
    roundAt C₋ t ((k : Surreal) * x) = k * roundAt C₋ t x := by
  rw [roundAt_eq, roundAt_eq, mul_div_assoc]
  have hk := (mem_residueSubfield_iff C₋).mp k.2
  have diff := mul_mem_infinitesimals_of_mem C₋ hk.2
    (sub_cosetRep_mem (infinitesimals C₋) (x / ω^ t))
  rw [mul_sub] at diff
  exact (cosetRep_eq_of_sub_mem diff).trans ((mem_residueRepresentatives_iff C₋).mp
    ((residueRepresentatives C₋).mul_mem hk.1 (cosetRep_mem_residueRepresentatives C₋ _)))

/-- The least horizontal level and a leading reading of one specify the bounded row uniquely. -/
theorem unique_normalized_bounded_row {a c : V} (ha : a ≠ 0) :
    ∃! p : V × V, p.1 ≠ 0 ∧ c * p.1 = a * p.2 ∧
      (∀ x y : V, x ≠ 0 → c * x = a * y → precisionLevel C₋ p.1 ≤ precisionLevel C₋ x) ∧
      roundAt C₋ (precisionLevel C₋ p.1) p.1 = 1 := by
  obtain ⟨f, g, hf, line, least⟩ := exists_least_level_row i (c := c) ha
  have hf₀ : (f : Surreal) ≠ 0 := fun h ↦ hf (Subtype.ext h)
  let t := precisionLevel C₋ f
  obtain ⟨hk, hn⟩ := roundAt_precisionLevel_mem_residueSubfield_and_ne_zero C₋
    ⟨f, ((mem_boundedResidueRepresentatives i).mp f.2).1⟩ hf₀
  let k : residueSubfield C₋ := ⟨roundAt C₋ t f, hk⟩
  have hk₀ : (k : Surreal) ≠ 0 := hn
  let s : V := algebraMap (residueSubfield C₋) V k⁻¹
  have val : (s : Surreal) = (k : Surreal)⁻¹ := coe_boundedResidue_algebraMap i _
  have unit : precisionLevel C₋ (s : Surreal) = 0 := by
    apply (div_wpow_mem_subring_and_inv_iff C₋ (val ▸ inv_ne_zero hk₀) (cosetRep_zero _)).mp
    simp only [wpow_zero, div_one, val, inv_inv]
    exact ⟨((mem_residueSubfield_iff C₋).mp (k⁻¹).2).2, ((mem_residueSubfield_iff C₋).mp k.2).2⟩
  have s₀ : (s : Surreal) ≠ 0 := val ▸ inv_ne_zero hk₀
  let p := (s * f, s * g)
  have hn' : p.1 ≠ 0 := mul_ne_zero (fun h ↦ s₀ (congrArg Subtype.val h)) hf
  have level : precisionLevel C₋ p.1 = t := by
    change precisionLevel C₋ ((s : Surreal) * f) = t
    rw [precisionLevel_mul C₋ s₀ hf₀, unit, zero_add]
  have line' : c * p.1 = a * p.2 := by
    change c * (s * f) = a * (s * g)
    rw [mul_left_comm c, line, mul_left_comm s]
  have lead : roundAt C₋ t p.1 = 1 := by
    change roundAt C₋ t ((s : Surreal) * f) = 1
    rw [val]
    exact (scalar_reading i k⁻¹ t f).trans (inv_mul_cancel₀ hk₀)
  refine ⟨p, ⟨hn', line', level ▸ least, level ▸ lead⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨hx, hxy, hleast, hlead⟩
  have ex : precisionLevel C₋ x = t := le_antisymm ((hleast _ _ hn' line').trans_eq level)
    (least x y hx hxy)
  change roundAt C₋ (precisionLevel C₋ x) x = 1 at hlead
  rw [ex] at hlead
  have onLine : c * (x - p.1) = a * (y - p.2) := by rw [mul_sub, mul_sub, hxy, line']
  have eqx : x = p.1 := by
    by_contra! he
    have diff : ((x : Surreal) - p.1) ≠ 0 := sub_ne_zero.mpr (fun h ↦ he (Subtype.ext h))
    have hy₀ := least (x - p.1) (y - p.2) (sub_ne_zero.mpr he) onLine
    have same : roundAt C₋ t x = roundAt C₋ t p.1 := hlead.trans lead.symm
    rw [roundAt_eq, roundAt_eq, cosetRep_eq_cosetRep_iff, ← sub_div] at same
    have lower := (div_wpow_mem_infinitesimals_iff C₋ diff (cosetRep_precisionLevel C₋ f)).mp same
    exact lower.not_ge hy₀
  refine Prod.ext eqx ?_
  apply mul_left_cancel₀ ha
  exact hxy.symm.trans (eqx ▸ line')

/-- A least horizontal level is attained on every bounded line. Dividing by that row and
taking the simplest representative gives the exact multiplier of each point. -/
theorem bounded_least_row {a c : V} (ha : a ≠ 0) :
    ∃ f g : V, f ≠ 0 ∧ c * f = a * g ∧
      (∀ x y : V, x ≠ 0 → c * x = a * y →
        precisionLevel (lowerGrowthSubring i) f ≤ precisionLevel (lowerGrowthSubring i) x) ∧
      roundAt C₋ (precisionLevel C₋ f) f = 1 ∧ ∀ x y : V, c * x = a * y →
        let q := cosetRep (infinitesimals (lowerGrowthSubring i)) ((x : Surreal) / f)
        ∃ hq : q ∈ V, x = (⟨q, hq⟩ : V) * f ∧ y = (⟨q, hq⟩ : V) * g := by
  obtain ⟨⟨f, g⟩, ⟨hf, line, least, head⟩, _⟩ := unique_normalized_bounded_row i (c := c) ha
  refine ⟨f, g, hf, line, least, head, fun x y h ↦ ?_⟩
  obtain ⟨q, hq, hx, hy⟩ := (least_level_row_iff_rounded_multiples i ha hf line).mp least x y h
  dsimp only
  rw [← hq]
  exact ⟨q.2, hx, hy⟩

private theorem rounded_generating_rows : HasGeneratingRows V := by
  intro a c ha
  obtain ⟨f, g, hf, _, _, _, read⟩ := bounded_least_row i (c := c) ha
  refine ⟨f, g, hf, fun x y he ↦ ?_⟩
  obtain ⟨hq, hx, hy⟩ := read x y he
  exact ⟨⟨_, hq⟩, hx, hy⟩

/-- The least-level row gives bounded primality. -/
instance : DecompositionMonoid V := (rounded_generating_rows i).decompositionMonoid

/-- A common refinement of two nonzero bounded products can be carried out in a finite
polynomial algebra generated by rescaled prefixes of the common product itself. -/
theorem bounded_refinement_from_product_cuts {a b c d : V} (hab : a * b = c * d) (hp : a * b ≠ 0) :
    ∃ S : Finset V, (∀ x ∈ S, ∃ t : Δ,
        boundedRound i ((mem_boundedPrecision i).mp t.2).1 (a * b) = x) ∧
      AlgebraicIndependent L ((↑) : ↥(S : Set V) → V) ∧
      ∃ e f g h : Algebra.adjoin L (S : Set V),
        a = (e : V) * f ∧ b = (g : V) * h ∧ c = (e : V) * g ∧ d = (f : V) * h := by
  obtain ⟨S, hS, hind, hall⟩ := finite_bounded_readings_capture_divisors i (a * b) hp
  refine ⟨S, hS, hind, ?_⟩
  obtain ⟨f, g, _, read⟩ := rounded_generating_rows i a c (left_ne_zero_of_mul hp)
  obtain ⟨e, ha, hc⟩ := read a c (mul_comm ..)
  obtain ⟨h, hd, hb⟩ := read d b hab.symm
  have inside {v : V} (hv : v ∣ a * b) : v ∈ Algebra.adjoin L (S : Set V) := by
    obtain ⟨u, hu⟩ := hv
    exact (hall v u hu.symm).1
  have hea : e ∣ a := ⟨f, ha⟩
  have hfa : f ∣ a := ⟨e, ha.trans (mul_comm ..)⟩
  have hgb : g ∣ b := ⟨h, hb.trans (mul_comm ..)⟩
  have hhb : h ∣ b := ⟨g, hb⟩
  exact ⟨⟨e, inside (hea.trans (dvd_mul_right ..))⟩, ⟨f, inside (hfa.trans (dvd_mul_right ..))⟩,
    ⟨g, inside (hgb.trans (dvd_mul_left ..))⟩, ⟨h, inside (hhb.trans (dvd_mul_left ..))⟩,
    ha, hb.trans (mul_comm ..), hc, hd.trans (mul_comm ..)⟩

/-- Swapping consecutive targets preserves the common product and all their positive
readings. A nonunit divisor of their product cannot have the same split for both orders. -/
theorem consecutive_targets_miss_split (a c : V) (ha : ¬ IsUnit a) :
    (∀ (t : Surreal.{u}) (ht : t ∈ Δ), 0 < t →
      boundedRound i ((mem_boundedPrecision i).mp ht).1 c =
        boundedRound i ((mem_boundedPrecision i).mp ht).1 (c + 1)) ∧
    ¬ ∃ e f : V, a = e * f ∧ e ∣ c ∧ f ∣ c + 1 ∧ e ∣ c + 1 ∧ f ∣ c := by
  constructor
  · intro t ht hp
    simp only [← boundedRoundHom_apply, map_add, boundedRoundHom_one_of_pos i ht hp, add_zero]
  · rintro ⟨e, f, he, hec, hfd, hed, hfc⟩
    have unit (x : V) (hc : x ∣ c) (hd : x ∣ c + 1) : IsUnit x :=
      isUnit_iff_dvd_one.mpr (by simpa only [add_sub_cancel_left] using dvd_sub hd hc)
    exact ha (he ▸ (unit e hec hed).mul (unit f hfc hfd))

end Surreal
