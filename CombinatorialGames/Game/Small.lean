/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
module

public import CombinatorialGames.Game.Confusion
public import CombinatorialGames.Game.Stops

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.CharZero
import CombinatorialGames.Game.Impartial.Grundy

/-!
# Small games all around

A small game is one that's smaller than all positive surreals, but larger than all negative
surreals. The only small numeric games are zero, but surprisingly there are other non-numeric
small games, such as the nimbers.

We prove that every dicotic game, and hence every impartial game is small. The former of these
results is known as the lawnmower theorem.

## TODO

Prove that every small game lies between two dicotic games.
-/

public section

namespace IGame

/-- Small games lie between all the positive and negative surreals. -/
class Small (x : IGame) : Prop where
  /-- A small game is smaller than any positive numeric game. -/
  le_numeric_of_pos (x) {y : IGame} [Numeric y] : 0 < y → x ≤ y
  /-- A small game is larger than any negative numeric game. -/
  numeric_le_of_neg (x) {y : IGame} [Numeric y] : y < 0 → y ≤ x

namespace Small
open Surreal.Cut

@[simp] protected instance zero : Small 0 := ⟨le_of_lt, le_of_lt⟩

theorem lt_numeric_of_pos (x : IGame) {y : IGame} [Small x] [Numeric y] (h : 0 < y) : x < y := by
  have h' : 0 < Surreal.mk y := by simpa
  obtain ⟨z, hz, hzy⟩ := exists_between h'
  cases z with | mk z
  rw [Surreal.mk_lt_mk] at hzy
  apply (le_numeric_of_pos x hz).trans_lt hzy

theorem numeric_lt_of_neg (x : IGame) {y : IGame} [Small x] [Numeric y] (h : y < 0) : y < x := by
  have h' : Surreal.mk y < 0 := by simpa
  obtain ⟨z, hzy, hz⟩ := exists_between h'
  cases z with | mk z
  rw [Surreal.mk_lt_mk] at hzy
  exact hzy.trans_le (numeric_le_of_neg x hz)

theorem lt_surreal_of_pos (x : IGame) [Small x] {y : Surreal} (h : 0 < y) : .mk x < y.toGame := by
  rw [← Surreal.gameMk_out]
  apply Small.lt_numeric_of_pos
  rw [← Surreal.mk_lt_mk]
  simpa

theorem surreal_lt_of_neg (x : IGame) [Small x] {y : Surreal} (h : y < 0) : y.toGame < .mk x := by
  rw [← Surreal.gameMk_out]
  apply Small.numeric_lt_of_neg
  rw [← Surreal.mk_lt_mk]
  simpa

theorem of_equiv {x y : IGame} (h : x ≈ y) [Small x] : Small y where
  le_numeric_of_pos := by grw [← h]; exact Small.le_numeric_of_pos x
  numeric_le_of_neg := by grw [← h]; exact Small.numeric_le_of_neg x

theorem congr {x y : IGame} (h : x ≈ y) : Small x ↔ Small y :=
  ⟨fun _ ↦ of_equiv h, fun _ ↦ of_equiv h.symm⟩

theorem _root_.IGame.Numeric.small_iff_equiv_zero {x : IGame} [Numeric x] : Small x ↔ x ≈ 0 := by
  refine ⟨fun _ ↦ ?_, fun h ↦ of_equiv h.symm⟩
  obtain hx | hx | hx := Numeric.lt_or_equiv_or_gt x 0
  · cases (numeric_lt_of_neg x hx).false
  · exact hx
  · cases (lt_numeric_of_pos x hx).false

protected instance neg (x : IGame) [Small x] : Small (-x) where
  le_numeric_of_pos {y} _ hy := by
    rw [← IGame.neg_le]
    apply Small.numeric_le_of_neg
    rwa [IGame.neg_lt_zero]
  numeric_le_of_neg {y} _ hy := by
    rw [← IGame.le_neg]
    apply Small.le_numeric_of_pos
    rwa [IGame.zero_lt_neg]

@[simp]
theorem neg_iff {x : IGame} : Small (-x) ↔ Small x :=
  ⟨fun _ ↦ by simpa using Small.neg (-x), fun _ ↦ .neg x⟩

protected instance add (x y : IGame) [Small x] [Small y] : Small (x + y) where
  le_numeric_of_pos {z} _ hz := by
    rw [← Game.mk_le_mk, ← Surreal.toGame_mk z, Game.mk_add]
    obtain ⟨z₁, hz₁0, hz₁z⟩ := exists_between (Surreal.mk_lt_mk.2 hz)
    grw [← add_sub_cancel z₁ (.mk z), Surreal.toGame_add,
      Small.lt_surreal_of_pos x hz₁0, add_le_add_iff_left]
    exact lt_surreal_of_pos y (sub_pos_of_lt hz₁z) |>.le
  numeric_le_of_neg {z} _ hz := by
    rw [← Game.mk_le_mk, ← Surreal.toGame_mk z, Game.mk_add]
    obtain ⟨z₁, hz₁0, hz₁z⟩ := exists_between' (Surreal.mk_lt_mk.2 hz)
    grw [← add_sub_cancel z₁ (.mk z), Surreal.toGame_add,
      Small.surreal_lt_of_neg x hz₁0, add_le_add_iff_left]
    exact surreal_lt_of_neg y (sub_neg_of_lt hz₁z) |>.le

protected instance sub (x y : IGame) [Small x] [Small y] : Small (x - y) :=
  .add ..

/-- A game between two small games is small. -/
theorem of_between (x y) {z} [Small x] [Small y] (h : z ∈ Set.Icc x y) : Small z where
  le_numeric_of_pos hw := h.2.trans (le_numeric_of_pos y hw)
  numeric_le_of_neg hw := (numeric_le_of_neg x hw).trans h.1

theorem leftGame_mk_cases (x : IGame) [Small x] :
    leftGame (.mk x) = leftSurreal 0 ∨ leftGame (.mk x) = rightSurreal 0 := by
  apply (em (x ≤ 0)).imp <;> intro hx <;> ext y
  · simp only [left_leftGame, Set.mem_ofPred_eq, left_leftSurreal, Set.mem_Iio]
    obtain hy | rfl | hy := lt_trichotomy y 0
    · simpa [hy] using (surreal_lt_of_neg x hy).not_ge
    · simpa
    · simpa [hy.asymm] using (lt_surreal_of_pos x hy).le
  · simp only [left_leftGame, Set.mem_ofPred_eq, left_rightSurreal, Set.mem_Iic]
    obtain hy | rfl | hy := lt_trichotomy y 0
    · simpa [hy.le] using (surreal_lt_of_neg x hy).not_ge
    · simpa
    · simpa [hy.not_ge] using (lt_surreal_of_pos x hy).le

theorem rightGame_mk_cases (x : IGame) [Small x] :
    rightGame (.mk x) = leftSurreal 0 ∨ rightGame (.mk x) = rightSurreal 0 := by
  simpa [or_comm, neg_eq_iff_eq_neg] using leftGame_mk_cases (-x)

instance (x : IGame) [Small x] : (leftGame (.mk x)).Numeric := by
  obtain h | h := leftGame_mk_cases x <;> simp [h]

instance (x : IGame) [Small x] : (rightGame (.mk x)).Numeric := by
  obtain h | h := rightGame_mk_cases x <;> simp [h]

@[simp]
theorem toSurreal_leftGame_mk (x : IGame) [Small x] : (leftGame (.mk x)).toSurreal = 0 := by
  obtain h | h := leftGame_mk_cases x <;> simp [h]

@[simp]
theorem toSurreal_rightGame_mk (x : IGame) [Small x] : (rightGame (.mk x)).toSurreal = 0 := by
  obtain h | h := rightGame_mk_cases x <;> simp [h]

@[simp]
theorem _root_.IGame.leftStop_of_small (x : IGame) [Small x] [Short x] : leftStop x = 0 := by
  have := toSurreal_leftGame_mk_of_short x
  rw [toSurreal_leftGame_mk] at this
  exact mod_cast this.symm

@[simp]
theorem _root_.IGame.rightStop_of_small (x : IGame) [Small x] [Short x] : rightStop x = 0 := by
  rw [← neg_eq_zero, ← leftStop_neg, leftStop_of_small]

theorem of_stops_eq_zero {x : IGame} [Short x] (hl : leftStop x = 0) (hr : rightStop x = 0) :
    Small x where
  le_numeric_of_pos {y} _ hy := by
    apply (lt_of_leftStop_lt _).le
    simp_all
  numeric_le_of_neg {y} _ hy := by
    apply (lt_of_lt_rightStop _).le
    simp_all

theorem _root_IGame.small_iff_stops_eq_zero {x : IGame} [Short x] :
    Small x ↔ leftStop x = 0 ∧ rightStop x = 0 :=
  ⟨fun _ ↦ ⟨leftStop_of_small x, rightStop_of_small x⟩,
    fun ⟨hl, hr⟩ ↦ of_stops_eq_zero hl hr⟩

/-- A short infinitesimal game is in fact small. -/
theorem of_infinitesimal {x : IGame} [Short x]
    (hl : ∀ y : Dyadic, y < 0 → y ≤ x) (hr : ∀ y : Dyadic, 0 < y → x ≤ y) : Small x where
  le_numeric_of_pos {y} _ hy := by
    apply (lt_of_leftStop_lt (hy.trans_le' _)).le
    rw [Dyadic.toIGame_le_zero]
    contrapose! hr
    obtain ⟨z, hz, hzx⟩ := exists_between hr
    exact ⟨z, hz, lf_of_lt_leftStop (mod_cast hzx)⟩
  numeric_le_of_neg {y} _ hy := by
    apply (lt_of_lt_rightStop (hy.trans_le _)).le
    rw [Dyadic.zero_le_toIGame]
    contrapose! hl
    obtain ⟨z, hxz, hz⟩ := exists_between hl
    exact ⟨z, hz, lf_of_rightStop_lt (mod_cast hxz)⟩

theorem confusionInterval_subset_zero (x : IGame) [Small x] :
    Game.confusionInterval (.mk x) ⊆ {0} := by
  rw [Game.confusionInterval_def]
  obtain hl | hl := leftGame_mk_cases x <;> obtain hr | hr := rightGame_mk_cases x <;> grind

theorem lt_numeric_of_pos_of_forall_of_nonempty {x y : IGame} (hy : 0 < y) [Numeric y]
    (h : ∀ p, ∀ y ∈ x.moves p, Small y) (hn : xᴿ.Nonempty) : x < y := by
  rw [lt_iff_le_not_ge, le_iff_forall_lf]
  refine ⟨⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩, ?_⟩
  · have := h _ _ hz
    exact (lt_numeric_of_pos z hy).not_ge
  · numeric
    exact (lt_numeric_of_pos_of_forall_of_nonempty (hy.trans (Numeric.lt_right hz)) h hn).not_ge
  · obtain ⟨z, hz⟩ := hn
    have := h _ _ hz
    exact lf_of_right_le (le_numeric_of_pos _ hy) hz
termination_by y
decreasing_by igame_wf

theorem numeric_lt_of_neg_of_forall_of_nonempty {x y : IGame} (hy : y < 0) [Numeric y]
    (h : ∀ p, ∀ y ∈ x.moves p, Small y) (hn : xᴸ.Nonempty) : y < x := by
  rw [← IGame.neg_lt_neg_iff]
  apply lt_numeric_of_pos_of_forall_of_nonempty
  · simpa
  · simpa [and_comm] using h
  · simpa

theorem of_forall_of_nonempty {x : IGame}
    (h : ∀ p, ∀ y ∈ x.moves p, Small y) (hn : ∀ p, (x.moves p).Nonempty) : Small x where
  le_numeric_of_pos hy := (lt_numeric_of_pos_of_forall_of_nonempty hy h (hn _)).le
  numeric_le_of_neg hy := (numeric_lt_of_neg_of_forall_of_nonempty hy h (hn _)).le

/-- The **lawnmower theorem**: every dicotic game is small. -/
instance _root_.IGame.Dicotic.toSmall (x) [Dicotic x] : Small x := by
  obtain rfl | hx := eq_or_ne x 0; · infer_instance
  refine Small.of_forall_of_nonempty (fun p y hy ↦ ?_) (Dicotic.ne_zero_iff'.1 hx)
  dicotic
  exact Dicotic.toSmall y
termination_by x
decreasing_by igame_wf

-- TODO: a game is dicotic iff every non-strict subposition is small.

instance _root_.IGame.Impartial.toSmall (x) [Impartial x] : Small x :=
  .of_equiv (Impartial.nim_grundy_equiv x)

@[simp]
protected instance ofSets_zero_left (x : IGame) [Small x] : !{{0} | {x}}.Small :=
  .of_forall_of_nonempty (by simpa) (by simp)

@[simp]
protected instance ofSets_zero_right (x : IGame) [Small x] : !{{x} | {0}}.Small :=
  .of_forall_of_nonempty (by simpa) (by simp)

@[simp]
protected instance tiny (x : IGame) [Small x] : Small (⧾x) :=
  .of_forall_of_nonempty (by simp) (by simp)

@[simp]
protected instance miny (x : IGame) [Small x] : Small (⧿x) :=
  .of_forall_of_nonempty (by simp) (by simp)

protected theorem tiny_of_nonneg {x : IGame} (hx : 0 ≤ x) : Small (⧾x) :=
  of_between 0 (⧾0) ⟨(tiny_pos _).le, tiny_antitone hx⟩

protected theorem miny_of_nonneg {x : IGame} (hx : 0 ≤ x) : Small (⧿x) :=
  of_between (⧿0) 0 ⟨miny_monotone hx, (miny_neg _).le⟩

example : Small ⋆ := by infer_instance
example : Small ↑ := by infer_instance
example : Small ↓ := by infer_instance

end Small
end IGame
end
