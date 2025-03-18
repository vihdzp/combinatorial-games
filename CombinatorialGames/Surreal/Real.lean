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

theorem IGame.ratCast_add_equiv (q r : ℚ) : (q + r : IGame) ≈ (q + r : ℚ) := by
  simp [← Surreal.mk_eq_mk]

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
  refine ⟨⟨?_, fun x hx ↦ ?_⟩, ⟨fun x hx ↦ ?_, ?_⟩⟩
  · simp
  · obtain ⟨r, hr⟩ := equiv_ratCast_of_mem_rightMoves_ratCast hx
    rw [hr.le_congr_left]
    apply lf_rightMove
    have : q < r := by
      rw [← IGame.ratCast_lt, ← hr.lt_congr_right]
      exact Numeric.lt_rightMove hx
    simpa
  · obtain ⟨r, hr⟩ := equiv_ratCast_of_mem_leftMoves_ratCast hx
    rw [hr.le_congr_right]
    apply leftMove_lf
    have : r < q := by
      rw [← IGame.ratCast_lt, ← hr.lt_congr_left]
      exact Numeric.leftMove_lt hx
    simpa
  · simp

@[simp]
theorem ratCast_lt_toIGame {q : ℚ} {x : ℝ} : q < x.toIGame ↔ q < x := by
  obtain h | rfl | h := lt_trichotomy (q : ℝ) x
  · exact iff_of_true (Numeric.leftMove_lt (mem_leftMoves_toIGame_of_lt h)) h
  · simpa using (toIGame_ratCast_equiv q).not_gt
  · exact iff_of_false (Numeric.lt_rightMove (mem_rightMoves_toIGame_of_lt h)).asymm h.asymm

@[simp]
theorem toIGame_lt_ratCast {q : ℚ} {x : ℝ} : x.toIGame < q ↔ x < q := by
  obtain h | rfl | h := lt_trichotomy (q : ℝ) x
  · exact iff_of_false (Numeric.leftMove_lt (mem_leftMoves_toIGame_of_lt h)).asymm h.asymm
  · simpa using (toIGame_ratCast_equiv q).not_lt
  · exact iff_of_true (Numeric.lt_rightMove (mem_rightMoves_toIGame_of_lt h)) h

@[simp]
theorem ratCast_le_toIGame {q : ℚ} {x : ℝ} : q ≤ x.toIGame ↔ q ≤ x := by
  simp [← not_lt, ← Numeric.not_lt]

@[simp]
theorem toIGame_le_ratCast {q : ℚ} {x : ℝ} : x.toIGame ≤ q ↔ x ≤ q := by
  simp [← not_lt, ← Numeric.not_lt]

@[simp]
theorem ratCast_equiv_toIGame {q : ℚ} {x : ℝ} : (q : IGame) ≈ x.toIGame ↔ q = x := by
  simp [AntisymmRel, le_antisymm_iff]

@[simp]
theorem toIGame_equiv_ratCast {q : ℚ} {x : ℝ} : x.toIGame ≈ q ↔ x = q := by
  simp [AntisymmRel, le_antisymm_iff]

theorem toIGame_add_ratCast_equiv (x : ℝ) (q : ℚ) : x.toIGame + q ≈ (x + q).toIGame := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf,
    forall_leftMoves_add, forall_rightMoves_add]
  simp_rw [forall_leftMoves_toIGame, forall_rightMoves_toIGame, Numeric.not_le]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · intro r hr
    rw [(IGame.ratCast_add_equiv ..).lt_congr_left]
    simpa
  · intro x hx
    obtain ⟨r, hr⟩ := equiv_ratCast_of_mem_leftMoves_ratCast hx
    rw [(add_congr_right hr).le_congr_right]
    apply leftMove_lf
    simp


    #exit

theorem toIGame_add_equiv (x y : ℝ) : x.toIGame + y.toIGame ≈ (x + y).toIGame := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf,
    forall_leftMoves_add, forall_rightMoves_add]
  simp_rw [forall_leftMoves_toIGame, forall_rightMoves_toIGame, Numeric.not_le]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · intro q hq

end Real
end
