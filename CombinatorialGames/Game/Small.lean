/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
import CombinatorialGames.Game.Impartial.Grundy
import CombinatorialGames.Surreal.Division

/-!
# Small games all around

A small game is one that's smaller than all positive surreals, but larger than all negative
surreals. The only small numeric game can be zero, but surprisingly there are other non-numeric
small games, such as the nimbers.

We prove that every dicotic game, and hence every impartial game is small. The former of these
results is known as the lawnmower theorem.
-/

namespace IGame

/-- Small games lie between all the positive and negative surreals. -/
class Small (x : IGame) : Prop where
  /-- A small game is smaller than any positive numeric game. -/
  lt_numeric_of_pos {y : IGame} [Numeric y] : 0 < y → x < y
  /-- A small game is larger than any negative numeric game. -/
  numeric_lt_of_neg {y : IGame} [Numeric y] : y < 0 → y < x

namespace Small

protected instance zero : Small 0 := ⟨id, id⟩

theorem lt_surreal_of_pos {x : IGame} [Small x] {y : Surreal} (h : 0 < y) : .mk x < y.toGame := by
  rw [← Surreal.gameMk_out]
  apply Small.lt_numeric_of_pos
  rw [← Surreal.mk_lt_mk]
  simpa

theorem surreal_lt_of_neg {x : IGame} [Small x] {y : Surreal} (h : y < 0) : y.toGame < .mk x := by
  rw [← Surreal.gameMk_out]
  apply Small.numeric_lt_of_neg
  rw [← Surreal.mk_lt_mk]
  simpa

theorem of_equiv {x y : IGame} (h : x ≈ y) [Small x] : Small y where
  lt_numeric_of_pos := by grw [← h]; exact Small.lt_numeric_of_pos
  numeric_lt_of_neg := by grw [← h]; exact Small.numeric_lt_of_neg

theorem congr {x y : IGame} (h : x ≈ y) : Small x ↔ Small y :=
  ⟨fun _ ↦ of_equiv h, fun _ ↦ of_equiv h.symm⟩

theorem _root_.IGame.Numeric.small_iff_equiv_zero {x : IGame} [Numeric x] : Small x ↔ x ≈ 0 := by
  refine ⟨fun _ ↦ ?_, fun h ↦ of_equiv h.symm⟩
  obtain hx | hx | hx := Numeric.lt_or_equiv_or_gt x 0
  · cases (numeric_lt_of_neg hx).false
  · exact hx
  · cases (lt_numeric_of_pos hx).false

protected instance neg (x : IGame) [Small x] : Small (-x) where
  lt_numeric_of_pos {y} _ hy := by
    rw [← IGame.neg_lt]
    apply Small.numeric_lt_of_neg
    rwa [IGame.neg_lt_zero]
  numeric_lt_of_neg {y} _ hy := by
    rw [← IGame.lt_neg]
    apply Small.lt_numeric_of_pos
    rwa [IGame.zero_lt_neg]

protected instance add (x y : IGame) [Small x] [Small y] : Small (x + y) where
  lt_numeric_of_pos {z} _ hz := by
    rw [← Game.mk_lt_mk]
    have H (x) [Small x] := lt_surreal_of_pos (x := x) (y := .mk z / 2) ?_
    · simpa [← Surreal.toGame_add] using add_lt_add (H x) (H y)
    · simpa
  numeric_lt_of_neg {z} _ hz := by
    rw [← Game.mk_lt_mk]
    have H (x) [Small x] := surreal_lt_of_neg (x := x) (y := .mk z / 2) ?_
    · simpa [← Surreal.toGame_add] using add_lt_add (H x) (H y)
    · rw [div_neg_iff]
      exact .inr ⟨hz, two_pos⟩

protected instance sub (x y : IGame) [Small x] [Small y] : Small (x - y) :=
  .add ..

end Small

namespace Dicotic

private theorem lt_numeric_of_pos {x} [Dicotic x] {y} [Numeric y] (hy : 0 < y) : x < y := by
  rw [lt_iff_le_not_ge, le_iff_forall_lf]
  refine ⟨⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩, ?_⟩
  · dicotic
    exact (lt_numeric_of_pos hy).not_ge
  · numeric
    obtain (h | h) := Numeric.le_or_gt z 0
    · cases ((Numeric.lt_right hz).trans_le h).not_gt hy
    · exact (lt_numeric_of_pos h).not_ge
  · obtain rfl | h := eq_or_ne x 0
    · exact hy.not_ge
    · simp_rw [Dicotic.ne_zero_iff, ← Set.nonempty_iff_ne_empty] at h
      obtain ⟨z, hz⟩ := h right
      dicotic
      exact lf_of_right_le (lt_numeric_of_pos hy).le hz
termination_by (x, y)
decreasing_by igame_wf

/-- The **lawnmower theorem**: every dicotic game is small. -/
instance toSmall (x) [Dicotic x] : Small x where
  lt_numeric_of_pos
  numeric_lt_of_neg {y} _ hy := by have := lt_numeric_of_pos (x := -x) (y := -y); simp_all

end Dicotic

-- TODO: a game is dicotic iff every non-strict subposition is small.
-- First, we need a predicate for non-strict subpositions!

instance Impartial.toSmall (x) [Impartial x] : Small x :=
  .of_equiv (nim_grundy_equiv x)

end IGame
