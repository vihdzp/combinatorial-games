/-
Copyright (c) 2026 CombinatorialGames contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CombinatorialGames contributors
-/
module

public import CombinatorialGames.Surreal.Scale.Bounded.LeastRow

import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Divisors from one positive prefix

If a bounded product has two nonunit factors, all its divisors can be expressed in
readings of one positive prefix. This includes the normalized least row of a bounded line
when the product is that of the two coordinates of a point.
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

/-- All rescaled prefixes of one bounded representative. -/
def boundedReadingSet (p : V) : Set V :=
  Set.range fun t : Δ ↦ boundedRound i ((mem_boundedPrecision i).mp t.2).1 p

/-- If the product splits into two nonunits, zero precision can be omitted. If its support
meets every interval starting at zero, the underlying unscaled prefixes are then all proper. -/
theorem positive_cuts_capture_divisors {p y z : V} (hp : p ≠ 0) (hyz : y * z = p)
    (hy : ¬ IsUnit y) (hz : ¬ IsUnit z) :
    ∃ S : Finset V, (∀ x ∈ S, ∃ (t : Surreal.{u}) (ht : t ∈ Δ), 0 < t ∧
        boundedRound i ((mem_boundedPrecision i).mp ht).1 p = x) ∧
      AlgebraicIndependent L ((↑) : ↥(S : Set V) → V) ∧
      ∀ a b : V, a * b = p → a ∈ Algebra.adjoin L (S : Set V) ∧
        b ∈ Algebra.adjoin L (S : Set V) := by
  obtain ⟨S, hcuts, hind, hall⟩ := finite_bounded_readings_capture_divisors i p hp
  have hpS : p ∉ S := by
    intro h
    let v := ((↑) : ↥(S : Set V) → V)
    let j : ↥(S : Set V) := ⟨p, h⟩
    obtain ⟨hyS, hzS⟩ := hall y z hyz
    obtain ⟨Y, hY⟩ := Algebra.exists_mvPolynomial_aeval_eq_of_mem_adjoin
      (f := v) Subtype.range_coe.superset hyS
    obtain ⟨Z, hZ⟩ := Algebra.exists_mvPolynomial_aeval_eq_of_mem_adjoin
      (f := v) Subtype.range_coe.superset hzS
    have he : (MvPolynomial.X j : MvPolynomial _ L) = Y * Z := by
      apply algebraicIndependent_iff_injective_aeval.mp hind
      change MvPolynomial.aeval v (MvPolynomial.X j) = MvPolynomial.aeval v (Y * Z)
      rw [MvPolynomial.aeval_X, map_mul, hY, hZ, hyz]
    have hirr := (MvPolynomial.prime_X (R := L) (i := j)).irreducible
    rcases hirr.isUnit_or_isUnit he with h | h
    · exact hy (hY ▸ h.map (MvPolynomial.aeval v))
    · exact hz (hZ ▸ h.map (MvPolynomial.aeval v))
  refine ⟨S, ?_, hind, hall⟩
  intro x hx
  obtain ⟨⟨t, ht⟩, he⟩ := hcuts x hx
  refine ⟨t, ht, ?_, he⟩
  rcases eq_or_lt_of_le ((mem_boundedPrecision i).mp ht).1 with hzero | hpos
  · subst t
    rw [boundedRound_zero] at he
    exact (hpS (he.symm ▸ hx)).elim
  · exact hpos

/-- The needed positive cuts are nested. One positive prefix of the product, together
with the readings of that prefix, contains all of its bounded divisors. -/
theorem one_prefix_captures_divisors {p y z : V} (hp : p ≠ 0) (hyz : y * z = p)
    (hy : ¬ IsUnit y) (hz : ¬ IsUnit z) :
    ∃ (s : Surreal.{u}) (hs : s ∈ Δ), 0 < s ∧
      ∃ S : Finset V, (S : Set V) ⊆
          boundedReadingSet i (boundedRound i ((mem_boundedPrecision i).mp hs).1 p) ∧
        AlgebraicIndependent L ((↑) : ↥(S : Set V) → V) ∧
        ∀ a b : V, a * b = p → a ∈ Algebra.adjoin L (S : Set V) ∧
          b ∈ Algebra.adjoin L (S : Set V) := by
  classical
  obtain ⟨S, hcuts, hind, hall⟩ := positive_cuts_capture_divisors i hp hyz hy hz
  let time (j : ↥S) := (hcuts j j.2).choose
  have spec (j : ↥S) : ∃ ht : time j ∈ Δ, 0 < time j ∧
      boundedRound i ((mem_boundedPrecision i).mp ht).1 p = (j : V) := (hcuts j j.2).choose_spec
  let times := insert (ω^ i) (Finset.univ.image time)
  have htimes : times.Nonempty := Finset.insert_nonempty _ _
  let s := times.min' htimes
  have hs : s ∈ Δ ∧ 0 < s := by
    rcases Finset.mem_insert.mp (times.min'_mem htimes) with h | h
    · change s = ω^ i at h
      rw [h]
      exact ⟨(mem_boundedPrecision i).mpr
        ⟨(wpow_pos i).le, cosetRep_growthExponent_eq i, 1, by simp⟩, wpow_pos i⟩
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
      change time j = s at hj
      obtain ⟨ht, hpos, _⟩ := spec j
      exact hj ▸ ⟨ht, hpos⟩
  refine ⟨s, hs.1, hs.2, S, ?_, hind, hall⟩
  intro x hx
  let j : ↥S := ⟨x, hx⟩
  obtain ⟨ht, _, he⟩ := spec j
  have hle : s ≤ time j := times.min'_le _ (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  refine ⟨⟨time j - s, sub_mem_boundedPrecision i hs.1 ht hle⟩, ?_⟩
  change boundedRound i _ (boundedRound i _ p) = x
  rw [boundedRound_boundedRound]
  simpa only [show s + (time j - s) = time j by abel] using he

/-- The normalized least row is expressible using the readings of one positive prefix of
the product of its two input coordinates. -/
theorem normalized_row_in_one_prefix {a c : V} (hp : a * c ≠ 0)
    (ha : ¬ IsUnit a) (hc : ¬ IsUnit c) :
    ∃ (s : Surreal.{u}) (hs : s ∈ Δ), 0 < s ∧
      let reading := boundedRound i ((mem_boundedPrecision i).mp hs).1 (a * c)
      let T := Algebra.adjoin L (boundedReadingSet i reading)
      ∃ f ∈ T, ∃ g ∈ T, f ≠ 0 ∧ c * f = a * g ∧
        (∀ x y : V, x ≠ 0 → c * x = a * y → precisionLevel C₋ f ≤ precisionLevel C₋ x) ∧
        roundAt C₋ (precisionLevel C₋ f) f = 1 := by
  obtain ⟨s, hs, pos, S, sub, _, capture⟩ := one_prefix_captures_divisors i hp rfl ha hc
  obtain ⟨f, g, hf, line, least, head, read⟩ :=
    bounded_least_row i (c := c) (left_ne_zero_of_mul hp)
  obtain ⟨hk, he, he'⟩ := read a c (mul_comm ..)
  let k : V := ⟨_, hk⟩
  have fa : f ∣ a := ⟨k, he.trans (mul_comm ..)⟩
  have gc : g ∣ c := ⟨k, he'.trans (mul_comm ..)⟩
  have inside {x : V} (hx : x ∣ a * c) :
      x ∈ Algebra.adjoin L
        (boundedReadingSet i (boundedRound i ((mem_boundedPrecision i).mp hs).1 (a * c))) := by
    obtain ⟨y, hy⟩ := hx
    exact (Algebra.adjoin_mono sub) (capture x y hy.symm).1
  exact ⟨s, hs, pos, f, inside (fa.trans (dvd_mul_right ..)), g,
    inside (gc.trans (dvd_mul_left ..)), hf, line, least, head⟩

end Surreal
