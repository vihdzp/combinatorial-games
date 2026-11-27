/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Germ.Readings

import CombinatorialGames.Mathlib.Polynomial.OrderedReadings
import Mathlib.SetTheory.Cardinal.Order

/-!
# A polynomial presentation of the whole germ algebra
-/

universe u

public noncomputable section

namespace Surreal

variable (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex]
local notation "K" => residueSubfield C
local notation "G" => Germ C

/-- The germ algebra of a proper convex subring has an algebraically independent family
of generators over its residue subfield. -/
theorem exists_algebraicIndependent_germ_generators (hC : C ≠ ⊤) :
    ∃ T : Set G, AlgebraicIndependent K ((↑) : T → G) ∧ Algebra.adjoin K T = ⊤ := by
  obtain ⟨ord, wf⟩ := exists_wellFoundedLT G
  choose z hz using germMap_surjective C
  obtain ⟨T, _, hind, hall⟩ := independent_germ_readings C hC z
  exact ⟨T, hind, top_unique fun g _ ↦ hz g ▸ hall g⟩

/-- The germ algebra of a proper convex subring is a polynomial algebra over its residue
subfield. -/
theorem exists_mvPolynomial_algEquiv_germ (hC : C ≠ ⊤) :
    ∃ ι : Type (u + 1), Nonempty (MvPolynomial ι K ≃ₐ[K] G) := by
  obtain ⟨T, hT, hgen⟩ := exists_algebraicIndependent_germ_generators C hC
  exact ⟨T, ⟨hT.mvPolynomialAlgEquivOfAdjoinEqTop hgen⟩⟩

end Surreal
