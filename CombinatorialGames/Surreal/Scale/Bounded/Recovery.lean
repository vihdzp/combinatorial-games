/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Scale.Bounded.Basic

import CombinatorialGames.Surreal.Scale.RoundedPowers

/-!
# The greatest missing bounded reading

Multiplying by a bounded monomial recovers a lower reading throughout the gap below a prefix.
-/

universe u

open scoped Pointwise

open Set

public noncomputable section

namespace Surreal

variable (i : Surreal.{u})

local notation "C" => lowerGrowthSubring i
local notation "A" => unitExponentSubgroup (lowerGrowthSubring i)
local notation "B" => infinitesimals (lowerGrowthSubring i)
local notation "V" => boundedResidueRepresentatives i
local notation "D[" t "]" => (ω^ (t : Surreal) • B)

private theorem exists_boundedPrecision_pos_lt {a : Surreal.{u}} (ha : 0 < a)
    (hafix : cosetRep A a = a) :
    ∃ s ∈ boundedPrecision i, 0 < s ∧ s < a := by
  let s := min (ω^ i) (a / 2)
  have hs : 0 < s := lt_min (wpow_pos i) (half_pos ha)
  have hsfix : cosetRep A s = s := by
    dsimp only [s]
    have hhalf : cosetRep A (a / 2) = a / 2 :=
      cosetRep_unitExponentSubgroup_div_natCast_eq C hafix (n := 2) (by decide)
    rw [(monotone_cosetRep A).map_min, cosetRep_growthExponent_eq, hhalf]
  refine ⟨s, (mem_boundedPrecision i).mpr ⟨hs.le, hsfix, 1, ?_⟩, hs, ?_⟩
  · simpa only [Nat.cast_one, one_mul] using min_le_left (ω^ i) (a / 2)
  · exact (min_le_right (ω^ i) (a / 2)).trans_lt (half_lt_self ha)

private theorem exists_smaller_boundedPrecision_of_mem_scaled {t e : Surreal.{u}}
    (ht : t ∈ boundedPrecision i) (ht₀ : 0 < t) (he : e ∈ D[t]) :
    ∃ r ∈ boundedPrecision i, r < t ∧ e ∈ D[r] := by
  have htfix := ((mem_boundedPrecision i).mp ht).2.1
  by_cases he₀ : e = 0
  · obtain ⟨r, hr, _, hrt⟩ := exists_boundedPrecision_pos_lt i ht₀ htfix
    exact ⟨r, hr, hrt, he₀ ▸ (D[r]).zero_mem⟩
  have hlevel := (mem_wpow_smul_infinitesimals_iff C he₀ htfix).mp he
  let a := max 0 (precisionLevel C e)
  have ha : a < t := max_lt ht₀ hlevel
  have hafix : cosetRep A a = a := by
    dsimp only [a]
    rw [(monotone_cosetRep A).map_max, cosetRep_zero, cosetRep_precisionLevel]
  let r := (a + t) / 2
  have har : a < r := by dsimp only [r]; linarith
  have hrt : r < t := by dsimp only [r]; linarith
  have hr₀ : 0 ≤ r := (le_max_left ..).trans har.le
  have hrfix : cosetRep A r = r :=
    cosetRep_unitExponentSubgroup_div_natCast_eq C (by rw [cosetRep_add, hafix, htfix])
      (n := 2) (by decide)
  refine ⟨r, mem_boundedPrecision_of_le i hr₀ hrfix hrt.le ht, hrt, ?_⟩
  exact (mem_wpow_smul_infinitesimals_iff C he₀ hrfix).mpr
    ((le_max_right ..).trans_lt har)

private theorem boundedRound_eq_monomial_mul_of_mem_scaled {s t : Surreal.{u}}
    (hs : s ∈ boundedPrecision i) (ht : t ∈ boundedPrecision i) (hst : s ≤ t) (x : V)
    (he : (x : Surreal.{u}) - cosetRep D[t] x ∈ D[s]) :
    boundedRound i ((mem_boundedPrecision i).mp hs).1 x =
      boundedMonomial i (sub_mem_boundedPrecision i hs ht hst) *
        boundedRound i ((mem_boundedPrecision i).mp ht).1 x := by
  apply Subtype.ext
  simp only [coe_boundedRound, coe_boundedMonomial, Subring.coe_mul]
  have heq : roundAt C s x = roundAt C s (cosetRep D[t] x) := by
    simp only [roundAt_eq]
    apply cosetRep_eq_of_sub_mem
    rw [← sub_div]
    exact (mem_smul_addSubgroup_iff_div_mem (wpow_ne_zero s)).mp he
  exact heq.trans (roundAt_scaleCosetRep_of_ge C hst _)

/-- The greatest precision where a bounded representative's rescaled prefix still lies
outside a subring containing the bounded monomials. -/
theorem exists_greatest_missing_boundedRound (E : Subring V)
    (hm : ∀ {t : Surreal.{u}} (ht : t ∈ boundedPrecision i), boundedMonomial i ht ∈ E)
    (x : V) (hmiss : ∃ (t : Surreal.{u}) (ht : t ∈ boundedPrecision i),
      boundedRound i ((mem_boundedPrecision i).mp ht).1 x ∉ E) :
    ∃ (t : Surreal.{u}) (ht : t ∈ boundedPrecision i),
      boundedRound i ((mem_boundedPrecision i).mp ht).1 x ∉ E ∧
      ∀ s (hs : s ∈ boundedPrecision i),
        boundedRound i ((mem_boundedPrecision i).mp hs).1 x ∉ E → s ≤ t := by
  let T : Set Surreal.{u} := {t | ∃ ht : t ∈ boundedPrecision i,
    boundedRound i ((mem_boundedPrecision i).mp ht).1 x ∉ E}
  have hT : T.Nonempty := hmiss
  have hx₀ : x ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht, hbad⟩ := hmiss
    apply hbad
    have hz : boundedRound i ((mem_boundedPrecision i).mp ht).1 (0 : V) = 0 :=
      Subtype.ext (by simp [coe_boundedRound, roundAt_eq])
    rw [hz]
    exact E.zero_mem
  have hsub : T ⊆ boundedPrecision i := fun _ h ↦ h.1
  have hbdd : ∃ b ∈ boundedPrecision i, ∀ t ∈ T, t ≤ b := by
    refine ⟨_, precisionLevel_mem_boundedPrecision i x hx₀, ?_⟩
    rintro t ⟨ht, htbad⟩
    obtain ⟨ht₀, htfix, _, _⟩ := (mem_boundedPrecision i).mp ht
    by_contra! h
    exact htbad ((boundedRound_eq_zero_of_level_lt i ht₀ htfix x h) ▸ E.zero_mem)
  obtain ⟨t, ht, hub, hleast⟩ := exists_least_boundedPrecision_upperBound i hT hsub hbdd
  have ht₀ := ((mem_boundedPrecision i).mp ht).1
  have htbad : boundedRound i ht₀ x ∉ E := by
    intro hgood
    by_cases htzero : t = 0
    · subst t
      obtain ⟨s, hs, hbad⟩ := hmiss
      obtain rfl : s = 0 := le_antisymm (hub s ⟨hs, hbad⟩) ((mem_boundedPrecision i).mp hs).1
      exact hbad hgood
    have htpos := ht₀.lt_of_ne (Ne.symm htzero)
    have herr := sub_cosetRep_mem D[t] (x : Surreal.{u})
    obtain ⟨r, hr, hrt, her⟩ := exists_smaller_boundedPrecision_of_mem_scaled i ht htpos herr
    apply hrt.not_ge (hleast r hr ?_)
    rintro s ⟨hs, hsbad⟩
    by_contra! hrs
    apply hsbad
    have hst : s ≤ t := hub s ⟨hs, hsbad⟩
    have he := smul_addSubgroup_mono B (wpow_pos r) (wpow_le_wpow.mpr hrs.le) her
    rw [boundedRound_eq_monomial_mul_of_mem_scaled i hs ht hst x he]
    exact E.mul_mem (hm _) hgood
  exact ⟨t, ht, htbad, fun s hs hsbad ↦ hub s ⟨hs, hsbad⟩⟩

/-- The greatest precision where a bounded representative's rescaled prefix still lies
outside a subring containing the bounded monomials. -/
theorem exists_greatest_boundedRound_notMem (E : Subring V)
    (hm : ∀ {t : Surreal.{u}} (ht : t ∈ boundedPrecision i), boundedMonomial i ht ∈ E)
    (x : V) (hx : x ∉ E) :
    ∃ (t : Surreal.{u}) (ht : t ∈ boundedPrecision i),
      boundedRound i ((mem_boundedPrecision i).mp ht).1 x ∉ E ∧
      ∀ s (hs : s ∈ boundedPrecision i),
        boundedRound i ((mem_boundedPrecision i).mp hs).1 x ∉ E → s ≤ t := by
  exact exists_greatest_missing_boundedRound i E hm x
    ⟨0, zero_mem_boundedPrecision i, by simpa only [boundedRound_zero] using hx⟩

end Surreal
