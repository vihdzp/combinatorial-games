/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Coset.Basic
public import CombinatorialGames.Surreal.Omnific.Basic

import CombinatorialGames.Surreal.Coset.Arithmetic

/-!
# Omnific integers and convex cosets

Multiplication by an omnific integer preserves simplest representatives of convex additive
cosets. For a convex subring those representatives are omnific integers, and exact division
by a nonzero omnific integer in the subring preserves the representatives.
-/

universe u

public section

namespace Surreal

open IGame

/-- Multiplication by an omnific integer preserves the simplest representatives modulo a convex
additive subgroup. -/
theorem cosetRep_mul_eq_of_isOmnific {H : AddSubgroup Surreal.{u}} [H.IsConvex]
    {x w : Surreal.{u}} (hx : cosetRep H x = x) (hw : IsOmnific w) :
    cosetRep H (x * w) = x * w := by
  obtain ⟨x, _, rfl, hbx⟩ := birthday_eq_iGameBirthday x
  have hgap := (cosetRep_mk_eq_iff_forall_moves hbx).mp hx
  let : IGame.Numeric !{{w.out - 1} | {w.out + 1}} :=
    .mk (by simpa [← Surreal.mk_lt_mk] using
      (sub_lt_self w zero_lt_one).trans (lt_add_of_pos_right w zero_lt_one))
      (by simp [Numeric.add, Numeric.sub])
  have hcut : mk !{{w.out - 1} | {w.out + 1}} = w := by
    simpa only [out_eq, mk_one, hw.eq] using
      (round_mk_of_pos (x := w.out) (r := 1) IGame.zero_lt_one).symm
  rw [← hcut]
  apply cosetRep_mk_mul_eq_of_forall_moves
  intro p a ha q b hb
  cases q with
  | left =>
    simp only [moves_left_ofSets, Set.mem_singleton_iff] at hb
    subst b
    simpa only [hcut, mk_sub, mk_one, out_eq, sub_sub_cancel, mul_one] using hgap p a ha
  | right =>
    simp only [moves_right_ofSets, Set.mem_singleton_iff] at hb
    subst b
    simpa only [hcut, mk_add, mk_one, out_eq, sub_add_eq_sub_sub, sub_self, zero_sub,
      mul_neg, mul_one, H.neg_mem_iff] using hgap p a ha

/-- The simplest representatives modulo a convex unital subring are omnific integers. -/
theorem isOmnific_of_cosetRep_eq {C : Subring Surreal.{u}} [C.toAddSubgroup.IsConvex]
    {x : Surreal.{u}} (hx : cosetRep C.toAddSubgroup x = x) : IsOmnific x := by
  suffices h : x.round 1 = x from h ▸ IsOmnific.round x
  apply round_eq_of_forall_birthday_le
  · exact ⟨sub_lt_self x zero_lt_one, lt_add_of_pos_right x zero_lt_one⟩
  · intro z hz
    have hmem : x - z ∈ C.toAddSubgroup := by
      have hc := (inferInstance : C.toAddSubgroup.IsConvex).ordConnected
      apply hc.out (C.neg_mem C.one_mem) C.one_mem
      exact ⟨le_sub_comm.mpr (by simpa only [sub_neg_eq_add] using hz.2.le),
        sub_le_comm.mp hz.1.le⟩
    simpa only [hx] using birthday_cosetRep_le hmem

/-- Dividing a simplest representative modulo a convex subring by a nonzero omnific integer
in that subring gives a simplest representative modulo the same subring. -/
theorem cosetRep_div_eq_of_isOmnific
    {C : Subring Surreal.{u}} [C.toAddSubgroup.IsConvex] {p w : Surreal.{u}}
    (hp : cosetRep C.toAddSubgroup p = p) (hw : IsOmnific w)
    (hwC : w ∈ C) (hw₀ : w ≠ 0) : cosetRep C.toAddSubgroup (p / w) = p / w := by
  let r := cosetRep C.toAddSubgroup (p / w)
  have hr : cosetRep C.toAddSubgroup r = r := cosetRep_cosetRep _ _
  have hdiff : (p / w - r) * w ∈ C :=
    C.mul_mem (sub_cosetRep_mem C.toAddSubgroup (p / w)) hwC
  rw [sub_mul, div_mul_cancel₀ _ hw₀] at hdiff
  have hmul : r * w = p := calc
    r * w = cosetRep C.toAddSubgroup (r * w) := (cosetRep_mul_eq_of_isOmnific hr hw).symm
    _ = cosetRep C.toAddSubgroup p := (cosetRep_eq_of_sub_mem hdiff).symm
    _ = p := hp
  exact (eq_div_iff hw₀).2 hmul

/-- An omnific integer in a convex subring divides every simplest representative modulo the
subring, with omnific quotient, provided the divisor is nonzero. -/
theorem isOmnific_div_of_cosetRep_eq
    {C : Subring Surreal.{u}} [C.toAddSubgroup.IsConvex] {p w : Surreal.{u}}
    (hp : cosetRep C.toAddSubgroup p = p) (hw : IsOmnific w)
    (hwC : w ∈ C) (hw₀ : w ≠ 0) : IsOmnific (p / w) :=
  isOmnific_of_cosetRep_eq (cosetRep_div_eq_of_isOmnific hp hw hwC hw₀)

end Surreal
