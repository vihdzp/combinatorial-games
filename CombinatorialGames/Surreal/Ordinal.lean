/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.IGame.Ordinal
import CombinatorialGames.Surreal.Multiplication
import Mathlib.Algebra.Order.Hom.Ring

/-!
# Ordinals as surreals

We define the canonical map `NatOrdinal → Surreal` in terms of the map `NatOrdinal.toIGame`.
-/

open IGame Surreal

noncomputable section

/-- Ordinal games are numeric. -/
instance IGame.Numeric.toIGame (o : NatOrdinal) : Numeric o.toIGame := by
  rw [numeric_def]
  simpa using fun a ha ↦ IGame.Numeric.toIGame a
termination_by o

namespace NatOrdinal

/-- Converts an ordinal into the corresponding surreal. -/
def toSurreal : NatOrdinal ↪o Surreal where
  toFun o := .mk o.toIGame
  inj' _ _ h := toIGame_equiv_iff.1 (Quotient.exact h :)
  map_rel_iff' := @toIGame_le_iff

@[simp] theorem _root_.Surreal.mk_toIGame (o : NatOrdinal) : .mk o.toIGame = o.toSurreal := rfl

@[simp] theorem toSurreal_zero : toSurreal 0 = 0 := by simp [← Surreal.mk_toIGame]
@[simp] theorem toSurreal_one : toSurreal 1 = 1 := by simp [← Surreal.mk_toIGame]

@[simp]
theorem toSurreal_nonneg (a : NatOrdinal) : 0 ≤ a.toGame :=
  toIGame_nonneg a

theorem toSurreal_injective : Function.Injective toSurreal :=
  toSurreal.injective

theorem toSurreal_le_iff {a b : NatOrdinal} : a.toSurreal ≤ b.toSurreal ↔ a ≤ b := by simp
theorem toSurreal_lt_iff {a b : NatOrdinal} : a.toSurreal < b.toSurreal ↔ a < b := by simp
theorem toSurreal_inj {a b : NatOrdinal} : a.toSurreal = b.toSurreal ↔ a = b := by simp

@[simp]
theorem toSurreal_add (a b : NatOrdinal) : (a + b).toSurreal = a.toSurreal + b.toSurreal :=
  mk_eq (toIGame_add a b)

@[simp]
theorem toSurreal_mul (a b : NatOrdinal) : (a * b).toSurreal = a.toSurreal * b.toSurreal :=
  mk_eq (toIGame_mul a b)

/-- `NatOrdinal.toGame` as an `OrderRingHom`. -/
@[simps]
def toSurrealRingHom : NatOrdinal →+*o Surreal where
  toFun := toSurreal
  map_zero' := toSurreal_zero
  map_one' := toSurreal_one
  map_add' := toSurreal_add
  map_mul' := toSurreal_mul
  monotone' _ _ := toGame_le_iff.2

@[simp]
theorem toSurreal_natCast : ∀ n : ℕ, toSurreal n = n :=
  map_natCast' toSurrealRingHom toSurreal_one

end NatOrdinal
end
