/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Omnific.Basic

import CombinatorialGames.Surreal.Omnific.Divisibility
import CombinatorialGames.Surreal.Omnific.Order
import Mathlib.Algebra.GCDMonoid.Nat

/-!
# Finite divisors of products of omnific integers

The finite part of the omnific integers is a retract isomorphic to the ordinary integers.
Divisibility by its nonzero members lifts from the retract to the whole ring.
-/

universe u

public noncomputable section

namespace Surreal

private abbrev finiteOmnificSubring : Subring Surreal.{u} := omnific ⊓ finiteSubring

private def intEquivFiniteOmnific : ℤ ≃+* finiteOmnificSubring.{u} :=
  RingEquiv.ofBijective (Int.castRingHom _) ⟨Int.cast_injective, by
    intro x
    have hx := Subring.mem_inf.mp x.property
    obtain ⟨n, hn⟩ := mem_finiteSubring_iff.mp hx.2
    obtain ⟨k, hk⟩ := (mem_omnific_iff.mp hx.1).exists_intCast_of_abs_le hn
    exact ⟨k, Subtype.ext (by simpa using hk)⟩⟩

/-- Every ordinary integer is primal in the ring of omnific integers. -/
theorem isPrimal_omnific_intCast (n : ℤ) : IsPrimal (n : omnific.{u}) := by
  let : DecompositionMonoid finiteOmnificSubring.{u} :=
    MulEquiv.decompositionMonoid intEquivFiniteOmnific.{u}.symm
  have hf : IsPrimal (n : finiteOmnificSubring.{u}) := DecompositionMonoid.primal _
  simpa only [map_intCast] using
    (isPrimal_inclusion_omnific_iff finiteSubring (n : finiteOmnificSubring.{u})).2 hf

end Surreal
