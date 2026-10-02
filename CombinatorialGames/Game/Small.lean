/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
module

public import CombinatorialGames.Game.Impartial.Grundy
public import CombinatorialGames.Surreal.Dyadic

import Init.Data.Dyadic.Instances
import Mathlib.Algebra.Order.Field.Basic

/-!
# Small games all around

A small game is one that's smaller than all positive surreals, but larger than all negative
surreals. The only small numeric games are zero, but surprisingly there are other non-numeric
small games, such as the nimbers.

We prove that every dicotic game, and hence every impartial game is small. The former of these
results is known as the lawnmower theorem.
-/

universe u

public section

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
  numeric_lt_of_neg hy := IGame.neg_lt_neg_iff.1 (lt_numeric_of_pos (IGame.zero_lt_neg.2 hy))

end Dicotic

-- TODO: a game is dicotic iff every non-strict subposition is small.

instance Impartial.toSmall (x) [Impartial x] : Small x :=
  .of_equiv (nim_grundy_equiv x)

@[mk_iff infinitesimal_iff]
class Infinitesimal (x : IGame) : Prop where
  out : ∀ y : Dyadic, 0 < y → -y < x ∧ x < y

namespace Infinitesimal

theorem dyadic_eq_zero (x : Dyadic) [inst : Infinitesimal x] : x = 0 := by
  by_contra hd
  rcases lt_or_gt_of_ne hd with h | h
  · have := (inst.out _ (neg_pos.mpr h)).left
    simp_all only [Dyadic.toIGame_neg, neg_neg, lt_self_iff_false]
  · have := (inst.out _ h).right
    simp_all only [lt_self_iff_false]

theorem coe_dyadic_eq_zero (x : Dyadic) [inst : Infinitesimal.{u} x] : (x : IGame.{u}) = 0 := by
  exact Dyadic.toIGame_eq_zero.mpr <| dyadic_eq_zero x

theorem of_equiv (x y : IGame) (h : x ≈ y) [inst : Infinitesimal x] : Infinitesimal y := by
  refine y.infinitesimal_iff.mpr (fun _ hz ↦ ?_)
  obtain ⟨hlt, hgt⟩ := inst.out _ hz
  exact ⟨hlt.trans_antisymmRel h, h.symm.trans_lt hgt⟩

instance zero : Infinitesimal 0 := by
  simp [infinitesimal_iff]

@[simp] theorem sub_self (x : IGame) : Infinitesimal (x - x) := of_equiv 0 _ (sub_self_equiv x).symm

protected lemma neg (x : IGame) [inst : Infinitesimal x] : Infinitesimal (-x) := by
  rw [infinitesimal_iff]
  intro y hy
  obtain ⟨h₁, h₂⟩ := inst.out _ hy
  exact ⟨IGame.neg_lt_neg_iff.mpr h₂, IGame.neg_lt.mp h₁⟩

instance (x : IGame) [h : Infinitesimal x] : Infinitesimal (-x) := h.neg

protected lemma add {x y : IGame} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := by
  rw [infinitesimal_iff]
  intro z hz
  have ⟨hx₁, hx₂⟩ := hx.out _ (Dyadic.shiftRight_pos_of_pos z 1 hz)
  have ⟨hy₁, hy₂⟩ := hy.out _ (Dyadic.shiftRight_pos_of_pos z 1 hz)
  constructor
  · have := add_lt_add hx₁ hy₁
    rw [← Dyadic.toIGame_neg] at this ⊢
    rw [← z.shiftRight_one_add_shiftRight_one]
    refine lt_of_antisymmRel_of_lt ?_ this
    rw [neg_add]
    exact Dyadic.toIGame_add_equiv ..
  · have := add_lt_add hx₂ hy₂
    rw [← z.shiftRight_one_add_shiftRight_one]
    exact lt_of_lt_of_antisymmRel this (Dyadic.toIGame_add_equiv ..).symm

instance (x y : IGame) [hx : Infinitesimal x] [hy : Infinitesimal y] : Infinitesimal (x + y) :=
  hx.add hy

instance (x y : IGame) [Infinitesimal x] [Infinitesimal y] : Infinitesimal (x - y) := by
  rw [sub_eq_add_neg]
  infer_instance

theorem eq_of_infinitesimal_sub (z : IGame) (x y : Dyadic) [hx : Infinitesimal (z - x)]
    [hy : Infinitesimal (z - y)] : x = y := by
  have : Infinitesimal (y - x) := by
    have := z.sub_self_equiv
    rw [sub_eq_add_neg] at this
    apply (hx.add hy.neg).of_equiv
    rw [sub_add_eq_add_sub, neg_sub', ← add_sub_assoc, sub_neg_eq_add]
    simp_all only [sub_congr_left, add_equiv_right_iff]
  have := of_equiv (h := (Dyadic.toIGame_sub_equiv y x).symm)
  exact (sub_eq_zero.mp <| Dyadic.toIGame_eq_zero.mp <| coe_dyadic_eq_zero _).symm

end Infinitesimal
end IGame
end
