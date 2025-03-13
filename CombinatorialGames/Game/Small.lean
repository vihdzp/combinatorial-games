/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
import CombinatorialGames.Surreal.Basic

/-!
# Small games all around

We define small games, games that are smaller than every Surreal
and dicotic games, games `G` where both players can move from every nonempty subposition of `G`.

## TODO

- Define infinitesimal games as games x such that ∀ y : ℝ, 0 < y → -y < x ∧ x < y
  - (Does this hold for small infinitesimal games?)
- Prove that dicotic = small
- Prove that any short game is an infinitesimal (but not vice versa! see 1/ω)
-/

namespace IGame

/-! # Small Games -/

def Small (x : IGame) : Prop := ∀ y : IGame, Numeric y → 0 < y → -y < x ∧ x < y

/-! # Dicotic Games -/

private def DicoticAux (x : IGame) : Prop :=
  (x.leftMoves = ∅ ∧ x.rightMoves = ∅) ∨
  (x.leftMoves ≠ ∅ ∧ x.rightMoves ≠ ∅ ∧
    (∀ l ∈ x.leftMoves, DicoticAux l) ∧
    ∀ r ∈ x.rightMoves, DicoticAux r)
termination_by x
decreasing_by igame_wf

/-- A game `G` is dicotic if both players can move from every nonempty subposition of `G` -/
@[mk_iff dicotic_iff_aux]
class Dicotic (x : IGame) : Prop where
  out : DicoticAux x

theorem dicotic_def {x : IGame} : Dicotic x ↔
    (x.leftMoves = ∅ ∧ x.rightMoves = ∅) ∨
    (x.leftMoves ≠ ∅ ∧ x.rightMoves ≠ ∅ ∧
      (∀ l ∈ x.leftMoves, DicoticAux l) ∧
      ∀ r ∈ x.rightMoves, DicoticAux r) := by
  simp_rw [dicotic_iff_aux]; rw [DicoticAux]

namespace Dicotic

@[simp]
protected instance zero : Dicotic 0 := by
  rw [dicotic_def]
  simp

proof_wanted lt_numeric (x : IGame) [Dicotic x] (y : IGame) [Numeric y] : Game.mk x < Game.mk y

end Dicotic

end IGame
