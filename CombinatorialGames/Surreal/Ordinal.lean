/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Ordinal
import CombinatorialGames.Surreal.Multiplication

/-!
# Surreals as games

We define the canonical map `Ordinal → Surreal` in terms of the map `Ordinal.toPGame`.

# Main declarations

- `Ordinal.toSurreal`: The canonical map between ordinals and surreal numbers.
-/

open PGame Surreal
open scoped NaturalOps PGame

namespace Ordinal

/-- Ordinal games are numeric. -/
theorem numeric_toPGame (o : Ordinal) : o.toPGame.Numeric := by
  induction' o using Ordinal.induction with o IH
  apply numeric_of_isEmpty_rightMoves
  simpa using fun i ↦ IH _ (Ordinal.toLeftMovesToPGame_symm_lt i)

/-- Converts an ordinal into the corresponding surreal. -/
noncomputable def toSurreal : Ordinal ↪o Surreal where
  toFun o := .mk _ o.numeric_toPGame
  inj' _ _ h := toPGame_equiv_iff.1 (Quotient.exact h :)
  map_rel_iff' := @toPGame_le_iff

@[simp]
theorem _root_.Surreal.mk_toPGame (o : Ordinal) : .mk _ (numeric_toPGame o) = o.toSurreal :=
  rfl

@[simp]
theorem toSurreal_zero : toSurreal 0 = 0 :=
  Surreal.mk_eq toPGame_zero_equiv

@[simp]
theorem toSurreal_one : toSurreal 1 = 1 :=
  Surreal.mk_eq toPGame_one_equiv

theorem toSurreal_injective : Function.Injective toSurreal :=
  toSurreal.injective

theorem toSurreal_le_iff {a b : Ordinal} : a.toSurreal ≤ b.toSurreal ↔ a ≤ b := by simp
theorem toSurreal_lt_iff {a b : Ordinal} : a.toSurreal < b.toSurreal ↔ a < b := by simp
theorem toSurreal_inj {a b : Ordinal} : a.toSurreal = b.toSurreal ↔ a = b := by simp

theorem toSurreal_nadd (a b : Ordinal) : (a ♯ b).toSurreal = a.toSurreal + b.toSurreal :=
  mk_eq (toPGame_nadd a b)

theorem toSurreal_nmul (a b : Ordinal) : (a ⨳ b).toSurreal = a.toSurreal * b.toSurreal :=
  mk_eq (toPGame_nmul a b)

end Ordinal
