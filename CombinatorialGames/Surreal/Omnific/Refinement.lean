/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Omnific.Basic

import CombinatorialGames.Mathlib.FourFactorRefinement
import CombinatorialGames.Surreal.Omnific.GrowthInduction
import CombinatorialGames.Surreal.Omnific.Refinement.Integer
import CombinatorialGames.Surreal.Omnific.Refinement.LeastClass
import CombinatorialGames.Surreal.Omnific.Refinement.Limit
import CombinatorialGames.Surreal.Scale.Bounded.LeastRow

/-!
# Conway's refinement theorem for omnific integers

Every equality `a * b = c * d` in `Surreal.omnific` has four factors
`a = e * f`, `b = g * h`, `c = e * g` and `d = f * h`.

When the divisor has a least occurring growth class, the bounded points on the projected line
are multiples of one row of least horizontal level. Rounding the horizontal quotient gives each
multiplier. When there is no least class, a refinement of four germs holds at one common cutoff.
Rescaling makes the factors whole. The complementary divisor retains precisely the classes
strictly above the cutoff.

The accompanying `Refinement.md` gives the mathematical argument and links to its main lemmas.
-/

universe u

public noncomputable section

namespace Surreal

/-- Every omnific integer is primal. -/
instance : DecompositionMonoid omnific.{u} where
  primal a := by
    apply omnific_growthInduction (fun x ↦ IsPrimal x) _ a
    intro x ih
    by_cases hI : ∃ i, GrowthOccurs i (x : Surreal)
    · by_cases hmin : ∃ i, IsLeast {j : Surreal.{u} | GrowthOccurs j x} i
      · obtain ⟨i, hi⟩ := hmin
        apply isPrimal_of_least_growthOccurs _ x hi ih
        exact fun y ↦ DecompositionMonoid.primal (α := boundedResidueRepresentatives i) y
      · apply isPrimal_omnific_of_noLeast_growthOccurs x hI _ ih
        intro j hj
        by_contra! h
        exact hmin ⟨j, hj, fun k hk ↦ h k hk⟩
    · obtain ⟨n, hn⟩ := (mem_omnific_iff.mp x.2).exists_intCast_of_not_growthOccurs
        (fun i hi ↦ hI ⟨i, hi⟩)
      have hx : x = (n : omnific.{u}) :=
        Subtype.ext (hn.symm.trans (Subring.coe_intCast ..).symm)
      rw [hx]
      exact isPrimal_omnific_intCast n

/-- Conway's refinement theorem. Every pair of ways of writing an omnific integer as a product
has a common four-factor refinement. -/
theorem omnific_refinement {a b c d : omnific.{u}} (hab : a * b = c * d) :
    ∃ e f g h : omnific.{u}, a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h :=
  DecompositionMonoid.exists_mul_eq_mul hab

end Surreal
