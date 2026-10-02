/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
module

public import CombinatorialGames.Game.Impartial.Grundy
public import CombinatorialGames.Surreal.Dyadic

import Init.Data.Dyadic.Instances

/-!
# Small games all around

We define dicotic games, games `x` where both players can move from
every nonempty subposition of `x`. We prove that these games are small, and relate them
to infinitesimals.

## TODO

- Define infinitesimal games as games `x` such that `∀ r : ℝ, 0 < r → -r < x ∧ x < r`
  - (Does this hold for small infinitesimal games?)
- Prove that any short dicotic game is an infinitesimal (but not vice versa, consider `ω⁻¹`)
-/

universe u

public section

namespace IGame
namespace Dicotic

/--
One half of the **lawnmower theorem**: any dicotic game is smaller than any positive numeric game.
-/
theorem lt_of_numeric_of_pos (x) [Dicotic x] {y} [Numeric y] (hy : 0 < y) : x < y := by
  rw [lt_iff_le_not_ge, le_iff_forall_lf]
  refine ⟨⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩, ?_⟩
  · dicotic
    exact (lt_of_numeric_of_pos z hy).not_ge
  · numeric
    obtain (h | h) := Numeric.le_or_gt z 0
    · cases ((Numeric.lt_right hz).trans_le h).not_gt hy
    · exact (lt_of_numeric_of_pos x h).not_ge
  · obtain rfl | h := eq_or_ne x 0
    · exact hy.not_ge
    · simp_rw [ne_zero_iff, ← Set.nonempty_iff_ne_empty] at h
      obtain ⟨z, hz⟩ := h right
      dicotic
      exact lf_of_right_le (lt_of_numeric_of_pos z hy).le hz
termination_by (x, y)
decreasing_by igame_wf

/--
One half of the **lawnmower theorem**: any dicotic game is greater than any negative numeric game.
-/
theorem lt_of_numeric_of_neg (x) [Dicotic x] {y} [Numeric y] (hy : y < 0) : y < x := by
  have := lt_of_numeric_of_pos (-x) (y := -y); simp_all

end Dicotic

namespace Impartial

/-- One half of the **lawnmower theorem** for impartial games. -/
protected theorem lt_of_numeric_of_pos (x) [Impartial x] {y} [Numeric y] (hy : 0 < y) : x < y := by
  grw [← nim_grundy_equiv x]
  exact Dicotic.lt_of_numeric_of_pos _ hy

/-- One half of the **lawnmower theorem** for impartial games. -/
protected theorem lt_of_numeric_of_neg (x) [Impartial x] {y} [Numeric y] (hy : y < 0) : y < x := by
  grw [← nim_grundy_equiv x]
  exact Dicotic.lt_of_numeric_of_neg _ hy

end Impartial

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
