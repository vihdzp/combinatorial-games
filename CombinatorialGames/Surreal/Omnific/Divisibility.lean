/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Omnific.Residue

import CombinatorialGames.Surreal.Omnific.Coset

/-!
# Divisibility in convex subrings of omnific integers

A nonzero omnific integer in a convex subring divides an element precisely when it divides
its residue. This transfers primality in both directions.
-/

universe u

public section

namespace Surreal

variable (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex]

/-- Divisibility by a nonzero omnific integer in a convex subring is detected by the residue. -/
theorem dvd_iff_dvd_omnificResidue {d : (omnific ⊓ C : Subring Surreal.{u})}
    (hd : d ≠ 0) (x : omnific.{u}) :
    Subring.inclusion inf_le_left d ∣ x ↔ d ∣ omnificResidue C x := by
  constructor
  · intro h
    simpa only [omnificResidue_inclusion] using map_dvd (omnificResidue C) h
  · rintro ⟨s, hs⟩
    let p := cosetRep C.toAddSubgroup (x : Surreal)
    have hd' : (d : Surreal) ≠ 0 := fun h ↦ hd (Subtype.ext h)
    have hp := isOmnific_div_of_cosetRep_eq (cosetRep_cosetRep C.toAddSubgroup x)
      (mem_omnific_iff.mp (Subring.mem_inf.mp d.property).1)
      (Subring.mem_inf.mp d.property).2 hd'
    refine ⟨⟨p / d + s, mem_omnific_iff.mpr
      (hp.add (mem_omnific_iff.mp (Subring.mem_inf.mp s.property).1))⟩, Subtype.ext ?_⟩
    have he : (x : Surreal) - p = (d : Surreal) * s := by
      simpa only [coe_omnificResidue, Subring.coe_mul] using
        congrArg (fun z : (omnific ⊓ C : Subring Surreal.{u}) ↦ (z : Surreal)) hs
    change (x : Surreal) = (d : Surreal) * (p / d + s)
    rw [mul_add, mul_comm (d : Surreal) (p / d), div_mul_cancel₀ _ hd']
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm ..)

/-- An omnific integer in a convex subring is primal in their intersection precisely when it is
primal in the ring of all omnific integers. -/
theorem isPrimal_inclusion_omnific_iff (a : (omnific ⊓ C : Subring Surreal.{u})) :
    IsPrimal (Subring.inclusion (show omnific ⊓ C ≤ omnific from inf_le_left) a) ↔
      IsPrimal a := by
  let i := Subring.inclusion (show omnific ⊓ C ≤ omnific from inf_le_left)
  let r := omnificResidue C
  have hi (x) : r (i x) = x := omnificResidue_inclusion C x
  change IsPrimal (i a) ↔ IsPrimal a
  constructor
  · intro h x y hxy
    have hm : i a ∣ i x * i y := by simpa only [map_mul] using map_dvd i hxy
    obtain ⟨p, q, hp, hq, he⟩ := h hm
    exact ⟨r p, r q, hi x ▸ map_dvd r hp, hi y ▸ map_dvd r hq,
      by simpa only [hi, map_mul] using congrArg r he⟩
  · intro h
    obtain rfl | ha := eq_or_ne a 0
    · simpa only [map_zero] using (isPrimal_zero : IsPrimal (0 : omnific.{u}))
    intro x y hxy
    have hm : a ∣ r x * r y := by simpa only [hi, map_mul] using map_dvd r hxy
    obtain ⟨p, q, hp, hq, he⟩ := h hm
    have hpq : p * q ≠ 0 := he ▸ ha
    exact ⟨i p, i q, (dvd_iff_dvd_omnificResidue C (left_ne_zero_of_mul hpq) x).2 hp,
      (dvd_iff_dvd_omnificResidue C (right_ne_zero_of_mul hpq) y).2 hq,
      by simpa only [map_mul] using congrArg i he⟩

end Surreal
