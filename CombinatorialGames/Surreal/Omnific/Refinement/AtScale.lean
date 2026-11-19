/-
Copyright (c) 2026 CombinatorialGames contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CombinatorialGames contributors
-/
module

public import CombinatorialGames.Surreal.Omnific.GrowthInduction
public import CombinatorialGames.Surreal.Scale.Limit
public import CombinatorialGames.Surreal.Omnific.Rescaling

import CombinatorialGames.Surreal.Omnific.Divisibility

/-!
# Finishing a refinement at one occurring growth class

The four factors of the projected equality can be made whole at that scale. The nonzero
factors of the projected divisor divide the original entries by exact whole division.
Its complementary factor has fewer occurring classes.
-/

universe u

public noncomputable section

namespace Surreal

/-- Upper residue at an occurring class, with coefficients at the common lower scale. -/
abbrev growthProjection (I : Set Surreal.{u}) (i : I) :=
  (residueRetraction (commonLowerGrowthSubring I) (upperGrowthSubring i)
    ((commonLowerGrowthSubring_le_lowerGrowthSubring i.2).trans
      (lowerGrowthSubring_le_upperGrowthSubring i))).comp
    (Subring.inclusion (omnific_le_residueRepresentatives (commonLowerGrowthSubring I)))

private theorem coe_growthProjection (I : Set Surreal.{u}) (i : I) (x : omnific.{u}) :
    (growthProjection I i x : Surreal) = omnificResidue (upperGrowthSubring i) x := by
  rw [growthProjection, RingHom.comp_apply, coe_residueRetraction, Subring.coe_inclusion,
    coe_omnificResidue]

/-- For this equality it suffices to refine its projection at any one occurring class.
The choice of class can depend on all four entries. -/
theorem isPrimal_of_growth_refinements (a : omnific.{u})
    (ih : ∀ i, GrowthOccurs i a → ∀ v : omnific.{u},
      (∀ j, GrowthOccurs j v ↔ i < j ∧ GrowthOccurs j a) → IsPrimal v)
    (localSplit : ∀ b c d : omnific.{u}, a * b = c * d →
      let I := {j : Surreal.{u} | GrowthOccurs j a}
      ∃ i : I, let π := growthProjection I i
        ∃ e f g h, π a = e * f ∧ π b = g * h ∧ π c = e * g ∧ π d = f * h) :
    IsPrimal a := by
  rintro c d ⟨b, hcd⟩
  let I : Set Surreal.{u} := {j | GrowthOccurs j a}
  let : Small.{u} I := small_growthOccurs (a : Surreal)
  obtain ⟨i, e, f, g, h, ha, hb, hc, hd⟩ := localSplit b c d hcd.symm
  let C := commonLowerGrowthSubring I
  let D := upperGrowthSubring i
  have hCD : C ≤ D := (commonLowerGrowthSubring_le_lowerGrowthSubring i.2).trans
    (lowerGrowthSubring_le_upperGrowthSubring i)
  let w := omnificResidue D a
  obtain ⟨n, hn⟩ := exists_intCast_eq_sub_cosetRep_commonLowerGrowth I
    (mem_omnific_iff.mp a.2) fun _ h ↦ h
  have hres : (n : Surreal) = (w : Surreal) - cosetRep C.toAddSubgroup w := by
    rw [coe_omnificResidue, cosetRep_sub, cosetRep_cosetRep_of_ge
      (show C.toAddSubgroup ≤ D.toAddSubgroup from hCD)]
    exact hn.trans (by abel)
  obtain ⟨e, f, g, h, hef, _, heg, hfh⟩ :=
    whole_refinement_at_scale C D hCD ⟨n, hres⟩
      (by simpa only [coe_growthProjection, Subring.coe_mul] using congrArg Subtype.val ha)
      (by simpa only [coe_growthProjection, Subring.coe_mul] using congrArg Subtype.val hb)
      (by simpa only [coe_growthProjection, Subring.coe_mul] using congrArg Subtype.val hc)
      (by simpa only [coe_growthProjection, Subring.coe_mul] using congrArg Subtype.val hd)
  obtain ⟨hw, v, hav, hv, _⟩ := exists_normalizedFactor_of_growthOccurs a i.2
  let inc := Subring.inclusion (show omnific ⊓ D ≤ omnific from inf_le_left)
  have hef₀ : e * f ≠ 0 := hef ▸ hw
  obtain ⟨c', hc'⟩ := (dvd_iff_dvd_omnificResidue D (left_ne_zero_of_mul hef₀) c).2 ⟨g, heg⟩
  obtain ⟨d', hd'⟩ := (dvd_iff_dvd_omnificResidue D (right_ne_zero_of_mul hef₀) d).2 ⟨h, hfh⟩
  have ha' : a = (inc e * inc f) * v := by rw [← map_mul, ← hef]; exact hav
  have hnonzero : inc e * inc f ≠ 0 := fun hz ↦ hef₀ (Subtype.ext
    (congrArg (fun w : omnific ↦ (w : Surreal)) hz))
  have hdiv : v ∣ c' * d' := by
    refine ⟨b, mul_left_cancel₀ hnonzero ?_⟩
    calc
      (inc e * inc f) * (c' * d') = (inc e * c') * (inc f * d') := by ac_rfl
      _ = c * d := by rw [← hc', ← hd']
      _ = (inc e * inc f) * (v * b) := by rw [hcd, ha', mul_assoc]
  obtain ⟨s, t, ⟨k, hk⟩, ⟨l, hl⟩, hst⟩ := ih i i.2 v hv hdiv
  exact ⟨inc e * s, inc f * t, ⟨k, by rw [hc', hk, mul_assoc]⟩,
    ⟨l, by rw [hd', hl, mul_assoc]⟩, by rw [ha', hst]; ac_rfl⟩

end Surreal
