/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Scale.Bounded.Leaders
public import Mathlib.RingTheory.Algebraic.Defs

import CombinatorialGames.Mathlib.Polynomial.TranslatedPowers
import CombinatorialGames.Surreal.Scale.RoundedPowers
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Reading a polynomial relation at a bounded cut

At positive precision the top coefficient of a monic relation disappears. Its next
coefficient reads the original variable. A relation of minimum degree would therefore
recover that variable in the coefficient algebra.
-/

universe u

open Polynomial
open scoped Pointwise

public noncomputable section

namespace Surreal

variable (i : Surreal.{u})

local notation "C₋" => lowerGrowthSubring i
local notation "K" => residueSubfield (lowerGrowthSubring i)
local notation "V" => boundedResidueRepresentatives i
local notation "L" => boundedLeaderSubring i
local notation "Δ" => boundedPrecision i

abbrev ClosedUnderBoundedCuts (E : Subalgebra L V) : Prop :=
  ∀ {t : Surreal.{u}} (ht : t ∈ Δ) {x : V}, x ∈ E →
    boundedRound i ((mem_boundedPrecision i).mp ht).1 x ∈ E

private theorem read_polynomial (E : Subalgebra L V) (hE : ClosedUnderBoundedCuts i E)
    (x : V) (hx : ∀ {s : Surreal.{u}} (hs : s ∈ Δ), 0 < s →
      boundedRound i ((mem_boundedPrecision i).mp hs).1 x ∈ E)
    {t : Surreal.{u}} (ht : t ∈ Δ) (hp : 0 < t) (n : ℕ) (F : E[X]) (hF : F.natDegree ≤ n) :
    ∃ f : E[X], f.natDegree ≤ n ∧ aeval x f = boundedRoundHom i hp.le (aeval x F) ∧
      (f.coeff n : V) = boundedRoundHom i hp.le (F.coeff n) ∧
      (0 < n → F.coeff n = 1 → (f.coeff (n - 1) : V) =
        boundedRoundHom i hp.le (F.coeff (n - 1)) + n • boundedRoundHom i hp.le x) := by
  apply Polynomial.exists_eval₂_eq_of_translated_powers E.toSubring E.toSubring
    (boundedRoundHom i hp.le) x x (fun c ↦ by rw [boundedRoundHom_apply]; exact hE ht c.2) _ n F hF
  intro c k hk
  obtain ⟨s, hsp, hst, hsfix, hpow⟩ := exists_roundAt_mul_sub_pow C₋ hp
    ((mem_boundedPrecision i).mp ht).2.1 ((c : V) : Surreal)
    ((mem_boundedResidueRepresentatives i).mp x.2).1 hk
  have hs := mem_boundedPrecision_of_le i hsp.le hsfix hst.le ht
  let a := boundedMonomial i hs * boundedRound i hsp.le x
  have ha : a ∈ E := E.mul_mem
    (E.algebraMap_mem (⟨_, boundedMonomial_mem_boundedLeaderSubring i hs⟩ : L)) (hx hs hsp)
  have haeq : (a : Surreal) = cosetRep (ω^ s • infinitesimals C₋) (x : Surreal) := by
    rw [show a = _ from rfl, Subring.coe_mul, coe_boundedMonomial, coe_boundedRound,
      roundAt_eq, cosetRep_wpow_smul]
  refine ⟨⟨a, ha⟩, ⟨a, ha⟩, Subtype.ext ?_, Or.inr (boundedRoundHom_one_of_pos i ht hp),
    Subtype.ext ?_⟩
  · simp only [boundedRoundHom_apply, coe_boundedRound, haeq, roundAt_scaleCosetRep_of_le C₋ hst.le]
  · simp only [boundedRoundHom_apply, coe_boundedRound, Subring.coe_mul, Subring.coe_pow,
      show ((x - a : V) : Surreal) = (x : Surreal) - a from rfl, haeq]
    exact hpow

private theorem scalar_mem (E : Subalgebra L V) (k : K) : algebraMap K V k ∈ E :=
  E.algebraMap_mem (⟨_, algebraMap_mem_boundedLeaderSubring i k⟩ : L)

private theorem exists_scalar_read (y : V) (hy : y ≠ 0) :
    ∃ (t : Surreal.{u}) (ht : t ∈ Δ) (k : K), k ≠ 0 ∧
      boundedRound i ((mem_boundedPrecision i).mp ht).1 y = algebraMap K V k := by
  let t := precisionLevel C₋ (y : Surreal)
  have ht := precisionLevel_mem_boundedPrecision i y hy
  let u : residueRepresentatives C₋ := ⟨y, ((mem_boundedResidueRepresentatives i).mp y.2).1⟩
  obtain ⟨hk, hk₀⟩ := roundAt_precisionLevel_mem_residueSubfield_and_ne_zero C₋ u
    (fun he ↦ hy (Subtype.ext he))
  let k : K := ⟨roundAt C₋ t y, hk⟩
  refine ⟨t, ht, k, fun he ↦ hk₀ (congrArg Subtype.val he), Subtype.ext ?_⟩
  rw [coe_boundedRound, coe_boundedResidue_algebraMap]

/-- The positive readings of a bounded element all vanish only at lower-field scalars. -/
theorem exists_scalar_of_pos_reads_zero (y : V)
    (hy : ∀ {t : Surreal.{u}} (ht : t ∈ Δ), 0 < t →
      boundedRound i ((mem_boundedPrecision i).mp ht).1 y = 0) :
    ∃ k : K, y = algebraMap K V k := by
  by_cases h : y = 0
  · exact ⟨0, h.trans (map_zero _).symm⟩
  obtain ⟨t, ht, k, hk, he⟩ := exists_scalar_read i y h
  rcases eq_or_lt_of_le ((mem_boundedPrecision i).mp ht).1 with hzero | hpos
  · subst t
    rw [boundedRound_zero] at he
    exact ⟨k, he⟩
  · rw [hy ht hpos] at he
    exact (hk ((algebraMap K V).injective (he.symm.trans (map_zero _).symm))).elim

/-- If every positive cut of x is in a cut-closed algebra, an algebraic relation for x
already puts x in the algebra. The proof reads a minimum-degree relation on x itself. -/
theorem transcendental_boundedRound_of_pos_readings (E : Subalgebra L V)
    (hE : ClosedUnderBoundedCuts i E)
    (x : V) (hmissing : x ∉ E) (hx : ∀ {s : Surreal.{u}} (hs : s ∈ Δ), 0 < s →
      boundedRound i ((mem_boundedPrecision i).mp hs).1 x ∈ E) : Transcendental E x := by
  intro hrel
  obtain ⟨p, hp⟩ := exists_minimalFor_of_wellFoundedLT
    (fun f : E[X] ↦ f ≠ 0 ∧ aeval x f = 0) Polynomial.natDegree hrel
  let d := p.natDegree
  have hd : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro he
    have hpC := eq_C_of_natDegree_eq_zero he
    have hz := hp.prop.2
    rw [hpC, aeval_C] at hz
    exact hp.prop.1 (by rw [hpC, show p.coeff 0 = 0 from Subtype.ext hz, map_zero])
  have hpd : (p.coeff d : V) ≠ 0 := fun he ↦
    (leadingCoeff_ne_zero.mpr hp.prop.1) (Subtype.ext he)
  obtain ⟨t, ht, k, hk, htop⟩ := exists_scalar_read i _ hpd
  obtain ⟨g, hgdeg, hgzero, hgcoeff⟩ : ∃ g : E[X], g.natDegree ≤ d ∧ aeval x g = 0 ∧
      (g.coeff d : V) = algebraMap K V k := by
    rcases eq_or_lt_of_le ((mem_boundedPrecision i).mp ht).1 with he | htpos
    · subst t
      exact ⟨p, le_rfl, hp.prop.2, by simpa only [boundedRound_zero] using htop⟩
    · obtain ⟨g, hg, hval, hcoeff, _⟩ := read_polynomial i E hE x hx ht htpos d p le_rfl
      exact ⟨g, hg, by rw [hval, hp.prop.2, map_zero],
        hcoeff.trans ((boundedRoundHom_apply i _ _).trans htop)⟩
  let u : E := ⟨algebraMap K V k⁻¹, scalar_mem i E _⟩
  let q := C u * g
  have hqdeg : q.natDegree ≤ d := (natDegree_C_mul_le _ _).trans hgdeg
  have hqzero : aeval x q = 0 := by simp [q, map_mul, hgzero]
  have hqtop : q.coeff d = 1 := by
    apply Subtype.ext
    rw [show q = C u * g from rfl, coeff_C_mul]
    change algebraMap K V k⁻¹ * (g.coeff d : V) = 1
    rw [hgcoeff, ← map_mul, inv_mul_cancel₀ hk, map_one]
  let y : V := (q.coeff (d - 1) : V) + d • x
  have hy : y ∈ E := by
    suffices hs : ∃ k : K, y = algebraMap K V k by
      obtain ⟨k, hk⟩ := hs
      exact hk ▸ scalar_mem i E k
    apply exists_scalar_of_pos_reads_zero i
    intro r hr hrpos
    obtain ⟨f, hfdeg, hval, hcoeff, hnext⟩ := read_polynomial i E hE x hx hr hrpos d q hqdeg
    have hfzero : aeval x f = 0 := by rw [hval, hqzero, map_zero]
    have hf : f = 0 := by
      by_contra hne
      have he : f.natDegree = d := le_antisymm hfdeg (hp.le ⟨hne, hfzero⟩)
      apply (leadingCoeff_ne_zero.mpr hne)
      apply Subtype.ext
      rw [Polynomial.leadingCoeff, he, hcoeff, hqtop, Subalgebra.coe_one,
        boundedRoundHom_one_of_pos i hr hrpos]
      rfl
    have he := hnext hd hqtop
    rw [hf, coeff_zero, Subalgebra.coe_zero] at he
    rw [← boundedRoundHom_apply]
    change boundedRoundHom i hrpos.le ((q.coeff (d - 1) : V) + d • x) = 0
    rw [map_add, map_nsmul]
    exact he.symm
  have hdx : (d : V) * x ∈ E := by
    simpa only [y, add_sub_cancel_left, nsmul_eq_mul] using E.sub_mem hy (q.coeff (d - 1)).2
  have hm := E.mul_mem (scalar_mem i E (d : K)⁻¹) hdx
  rw [← map_natCast (algebraMap K V) d, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd.ne'), map_one, one_mul] at hm
  exact hmissing hm

end Surreal
