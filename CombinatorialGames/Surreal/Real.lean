/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Division
import Mathlib.Data.Real.Archimedean

/-!
# Real numbers as games

We define the function `Real.toIGame`, casting a real number to its Dedekind cut, and prove that
it's an order embedding. We then define the `Game` and `Surreal` versions of this map, and prove
that they are ring and field homomorphisms respectively.

## TODO

Every real number has birthday at most `ω`. This can be proven by showing that a real number is
equivalent to its Dedekind cut where only dyadic rationals are considered. At a later point, after
we have the necessary API on dyadic numbers, we might want to prove this equivalence, or even
re-define real numbers as Dedekind cuts of dyadic numbers specifically.
-/

open IGame

noncomputable section

namespace Real

/-- We make this private until we can build the `OrderEmbedding`. -/
private def toIGame' (x : ℝ) : IGame :=
  {(↑) '' {q : ℚ | q < x} | (↑) '' {q : ℚ | x < q}}ᴵ

private theorem Numeric.toIGame' (x : ℝ) : Numeric (toIGame' x) := by
  rw [Real.toIGame']
  apply Numeric.mk' <;> simp only [leftMoves_ofSets, rightMoves_ofSets, Set.forall_mem_image]
  · intro x hx y hy
    dsimp at *
    exact_mod_cast hx.trans hy
  all_goals
    intros
    infer_instance

/-- The canonical map from `ℝ` to `IGame`, sending a real number to its Dedekind cut. -/
def toIGame : ℝ ↪o IGame := by
  refine .ofStrictMono toIGame' fun x y h ↦ ?_
  have := Numeric.toIGame' x
  have := Numeric.toIGame' y
  obtain ⟨q, hx, hy⟩ := exists_rat_btwn h
  trans (q : IGame)
  · apply Numeric.lt_rightMove
    simpa [toIGame']
  · apply Numeric.leftMove_lt
    simpa [toIGame']

instance (x : ℝ) : Numeric x.toIGame :=
  Numeric.toIGame' x

@[simp]
theorem leftMoves_toIGame (x : ℝ) : x.toIGame.leftMoves = (↑) '' {q : ℚ | q < x} :=
  leftMoves_ofSets ..

@[simp]
theorem rightMoves_toIGame (x : ℝ) : x.toIGame.rightMoves = (↑) '' {q : ℚ | x < q} :=
  rightMoves_ofSets ..

theorem forall_leftMoves_toIGame {P : IGame → Prop} {x : ℝ} :
    (∀ y ∈ leftMoves (toIGame x), P y) ↔ ∀ q : ℚ, q < x → P q := by
  simp

theorem exists_leftMoves_toIGame {P : IGame → Prop} {x : ℝ} :
    (∃ y ∈ leftMoves (toIGame x), P y) ↔ ∃ q : ℚ, q < x ∧ P q := by
  simp

theorem forall_rightMoves_toIGame {P : IGame → Prop} {x : ℝ} :
    (∀ y ∈ rightMoves (toIGame x), P y) ↔ ∀ q : ℚ, x < q → P q := by
  simp

theorem exists_rightMoves_toIGame {P : IGame → Prop} {x : ℝ} :
    (∃ y ∈ rightMoves (toIGame x), P y) ↔ ∃ q : ℚ, x < q ∧ P q := by
  simp

theorem mem_leftMoves_toIGame_of_lt {q : ℚ} {x : ℝ} (h : q < x) :
    (q : IGame) ∈ x.toIGame.leftMoves := by
  simpa

theorem mem_rightMoves_toIGame_of_lt {q : ℚ} {x : ℝ} (h : x < q) :
    (q : IGame) ∈ x.toIGame.rightMoves := by
  simpa

theorem toIGame_ratCast_equiv (q : ℚ) : toIGame q ≈ q := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp
  · intro x hx
    have := equiv_ratCast_of_mem_rightMoves_inv_natCast
  · simp
  · simp

theorem toIGame_add_ratCast_equiv (x : ℝ) (q : ℚ) : x.toIGame + q ≈ (x + q).toIGame := by
  apply Fits.equiv_of_forall_not_fits

end Real
end
