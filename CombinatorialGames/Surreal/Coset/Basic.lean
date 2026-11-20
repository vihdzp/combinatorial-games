/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Mathlib.ConvexSubgroup
public import CombinatorialGames.Surreal.Birthday.Basic

import CombinatorialGames.Surreal.Birthday.Simplicity
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel

/-!
# Simplest representatives of convex cosets

A coset of a convex additive subgroup of the surreal numbers contains a unique number of
least birthday. The sufficient condition on the options of a cut is the additive-coset case
of the cut implication in Bagayoko and van der Hoeven, *Surreal substructures*, Lemma 6.5.
Applying this criterion to Conway's addition cut shows that the projection is additive.
-/

universe u

open IGame Set

public noncomputable section

namespace Surreal

private theorem existsUnique_cosetRep (H : AddSubgroup Surreal.{u}) [H.IsConvex] (x : Surreal.{u}) :
    ∃! p, x - p ∈ H ∧ ∀ y, x - y ∈ H → p.birthday ≤ y.birthday := by
  apply existsUnique_min_birthday (s := {y | x - y ∈ H})
  · exact ⟨x, by simp⟩
  · refine ⟨?_⟩
    intro a ha b hb z hz
    exact AddSubgroup.IsConvex.ordConnected.out hb ha
      ⟨sub_le_sub_left hz.2 x, sub_le_sub_left hz.1 x⟩

/-- The unique surreal of least birthday in the coset of `x` modulo a convex subgroup `H`. -/
def cosetRep (H : AddSubgroup Surreal.{u}) [H.IsConvex] (x : Surreal.{u}) : Surreal.{u} :=
  (existsUnique_cosetRep H x).exists.choose

variable {H : AddSubgroup Surreal.{u}} [H.IsConvex] {x y : Surreal.{u}}

private theorem cosetRep_spec (H : AddSubgroup Surreal.{u}) [H.IsConvex] (x : Surreal.{u}) :
    x - cosetRep H x ∈ H ∧ ∀ y, x - y ∈ H → (cosetRep H x).birthday ≤ y.birthday :=
  (existsUnique_cosetRep H x).exists.choose_spec

/-- The simplest representative belongs to the original coset. -/
theorem sub_cosetRep_mem (H : AddSubgroup Surreal.{u}) [H.IsConvex] (x : Surreal.{u}) :
    x - cosetRep H x ∈ H :=
  (cosetRep_spec H x).1

/-- The simplest representative has birthday at most that of any member of its coset. -/
theorem birthday_cosetRep_le (h : x - y ∈ H) : (cosetRep H x).birthday ≤ y.birthday :=
  (cosetRep_spec H x).2 y h

private theorem cosetRep_eq_of_mem_of_forall_birthday_le (hy : x - y ∈ H)
    (hmin : ∀ z, x - z ∈ H → y.birthday ≤ z.birthday) : cosetRep H x = y :=
  (existsUnique_cosetRep H x).unique (cosetRep_spec H x) ⟨hy, hmin⟩

/-- A distinct member of a coset has strictly larger birthday than its simplest representative. -/
theorem birthday_cosetRep_lt_of_ne (h : x - y ∈ H) (hne : cosetRep H x ≠ y) :
    (cosetRep H x).birthday < y.birthday := by
  refine (birthday_cosetRep_le h).lt_of_not_ge fun hge ↦ hne ?_
  exact cosetRep_eq_of_mem_of_forall_birthday_le h fun z hz ↦
    hge.trans (birthday_cosetRep_le hz)

/-- Congruent inputs have the same simplest representative. -/
theorem cosetRep_eq_of_sub_mem (h : x - y ∈ H) : cosetRep H x = cosetRep H y := by
  refine cosetRep_eq_of_mem_of_forall_birthday_le ?_ ?_
  · simpa only [sub_add_sub_cancel] using H.add_mem h (sub_cosetRep_mem H y)
  · intro z hz
    exact birthday_cosetRep_le
      (by simpa only [sub_sub_sub_cancel_left] using H.sub_mem hz h)

/-- Two simplest representatives are equal exactly when their inputs belong to the same coset. -/
theorem cosetRep_eq_cosetRep_iff : cosetRep H x = cosetRep H y ↔ x - y ∈ H := by
  refine ⟨fun h ↦ ?_, cosetRep_eq_of_sub_mem⟩
  simpa only [← h, sub_sub_sub_cancel_right] using
    H.sub_mem (sub_cosetRep_mem H x) (sub_cosetRep_mem H y)

/-- A simplest representative is fixed by projection to the same coset. -/
@[simp] theorem cosetRep_cosetRep (H : AddSubgroup Surreal.{u}) [H.IsConvex] (x : Surreal.{u}) :
    cosetRep H (cosetRep H x) = cosetRep H x :=
  (cosetRep_eq_of_sub_mem (sub_cosetRep_mem H x)).symm

/-- Projection to simplest representatives is monotone. -/
theorem monotone_cosetRep (H : AddSubgroup Surreal.{u}) [H.IsConvex] :
    Monotone (cosetRep H) := by
  intro x y hxy
  by_contra! h
  have hbound : cosetRep H x - cosetRep H y ≤
      (y - cosetRep H y) - (x - cosetRep H x) := by
    rw [← sub_nonneg]
    convert sub_nonneg.mpr hxy using 1
    abel
  have hmem := H.mem_of_nonneg_of_le (sub_nonneg.mpr h.le) hbound
    (H.sub_mem (sub_cosetRep_mem H y) (sub_cosetRep_mem H x))
  exact h.ne (by simpa using (cosetRep_eq_of_sub_mem hmem).symm)

/-- A surreal is its own simplest representative exactly when every earlier surreal lies outside
its coset. -/
theorem cosetRep_eq_iff :
    cosetRep H x = x ↔ ∀ y : Surreal.{u}, y.birthday < x.birthday → x - y ∉ H := by
  refine ⟨fun h y hy hmem ↦ hy.not_ge ?_, fun h ↦ ?_⟩
  · simpa only [h] using birthday_cosetRep_le hmem
  · exact cosetRep_eq_of_mem_of_forall_birthday_le (by simp)
      (fun y hy ↦ le_of_not_gt fun hlt ↦ h y hlt hy)

private theorem lt_of_mem_of_nonneg_of_notMem {a b : Surreal.{u}}
    (ha : a ∈ H) (hb : 0 ≤ b) (hb' : b ∉ H) : a < b :=
  lt_of_not_ge fun hab ↦ hb' (H.mem_of_nonneg_of_le hb hab ha)

/-- A numeric game gives a simplest coset representative if the difference from its value to
each option lies outside the subgroup. -/
theorem cosetRep_mk_eq_of_forall_moves (g : IGame.{u}) [g.Numeric]
    (h : ∀ (p : Player) (a : IGame.{u}) (ha : a ∈ g.moves p),
      mk g - @mk a (.of_mem_moves ha) ∉ H) : cosetRep H (mk g) = mk g := by
  refine cosetRep_eq_of_mem_of_forall_birthday_le (by simp) (fun y hy ↦ ?_)
  rw [← out_eq y]
  apply IGame.Fits.surrealBirthday_le
  constructor
  · intro a ha
    let := IGame.Numeric.of_mem_moves ha
    rw [IGame.Numeric.not_le, ← mk_lt_mk, out_eq]
    exact (sub_lt_sub_iff_left _).mp <| lt_of_mem_of_nonneg_of_notMem hy
      (sub_nonneg.mpr (mk_lt_mk.mpr (IGame.Numeric.left_lt ha)).le) (h _ a ha)
  · intro a ha
    let := IGame.Numeric.of_mem_moves ha
    rw [IGame.Numeric.not_le, ← mk_lt_mk, out_eq]
    exact (sub_lt_sub_iff_right _).mp <| lt_of_mem_of_nonneg_of_notMem (H.sub_mem_comm_iff.mp hy)
      (sub_nonneg.mpr (mk_lt_mk.mpr (IGame.Numeric.lt_right ha)).le)
      (mt H.sub_mem_comm_iff.mp (h _ a ha))

/-- For a numeric game of least birthday representing its surreal value, excluding all option
gaps from the subgroup characterizes fixedness under projection. -/
theorem cosetRep_mk_eq_iff_forall_moves {g : IGame.{u}} [g.Numeric]
    (hg : g.birthday = (mk g).birthday) :
    cosetRep H (mk g) = mk g ↔ ∀ (p : Player) (a : IGame.{u}) (ha : a ∈ g.moves p),
      mk g - @mk a (.of_mem_moves ha) ∉ H := by
  refine ⟨fun h p a ha ↦ ?_, cosetRep_mk_eq_of_forall_moves g⟩
  let := IGame.Numeric.of_mem_moves ha
  exact cosetRep_eq_iff.mp h (mk a)
    ((birthday_mk_le a).trans_lt ((IGame.birthday_lt_of_mem_moves ha).trans_eq hg))

private theorem cosetRep_add_of_eq (hx : cosetRep H x = x) (hy : cosetRep H y = y) :
    cosetRep H (x + y) = x + y := by
  obtain ⟨g, hg, rfl, hgb⟩ := x.birthday_eq_iGameBirthday
  obtain ⟨k, hk, rfl, hkb⟩ := y.birthday_eq_iGameBirthday
  let := hg
  let := hk
  rw [← mk_add]
  apply cosetRep_mk_eq_of_forall_moves
  intro p a ha
  rw [IGame.moves_add] at ha
  rcases ha with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
  · let := IGame.Numeric.of_mem_moves hb
    simpa only [mk_add, add_sub_add_right_eq_sub] using
      (cosetRep_mk_eq_iff_forall_moves hgb).mp hx p b hb
  · let := IGame.Numeric.of_mem_moves hb
    simpa only [mk_add, add_sub_add_left_eq_sub] using
      (cosetRep_mk_eq_iff_forall_moves hkb).mp hy p b hb

/-- Projection to the simplest representatives of a convex subgroup commutes with addition. -/
@[simp]
theorem cosetRep_add (H : AddSubgroup Surreal.{u}) [H.IsConvex] (x y : Surreal.{u}) :
    cosetRep H (x + y) = cosetRep H x + cosetRep H y := by
  have h : x + y - (cosetRep H x + cosetRep H y) ∈ H := by
    rw [add_sub_add_comm]
    exact H.add_mem (sub_cosetRep_mem H x) (sub_cosetRep_mem H y)
  exact (cosetRep_eq_of_sub_mem h).trans
    (cosetRep_add_of_eq (cosetRep_cosetRep H x) (cosetRep_cosetRep H y))

/-- Zero is the simplest representative of the subgroup itself. -/
@[simp] theorem cosetRep_zero (H : AddSubgroup Surreal.{u}) [H.IsConvex] :
    cosetRep H 0 = 0 :=
  cosetRep_eq_iff.mpr (by simp)

/-- The simplest representative is zero exactly for members of the subgroup. -/
@[simp] theorem cosetRep_eq_zero_iff : cosetRep H x = 0 ↔ x ∈ H := by
  rw [← cosetRep_zero H, cosetRep_eq_cosetRep_iff, sub_zero]

/-- Projection to the simplest representatives of a convex subgroup as an additive homomorphism. -/
def cosetRepAddHom (H : AddSubgroup Surreal.{u}) [H.IsConvex] : Surreal.{u} →+ Surreal.{u} where
  toFun := cosetRep H
  map_zero' := cosetRep_zero H
  map_add' := cosetRep_add H

/-- Evaluation of the additive projection to simplest representatives. -/
@[simp] theorem cosetRepAddHom_apply (H : AddSubgroup Surreal.{u}) [H.IsConvex] (x : Surreal.{u}) :
    cosetRepAddHom H x = cosetRep H x := (rfl)

/-- Projection to simplest representatives commutes with negation. -/
@[simp] theorem cosetRep_neg (H : AddSubgroup Surreal.{u}) [H.IsConvex] (x : Surreal.{u}) :
    cosetRep H (-x) = -cosetRep H x := (cosetRepAddHom H).map_neg x

/-- Projection to simplest representatives commutes with subtraction. -/
@[simp] theorem cosetRep_sub (H : AddSubgroup Surreal.{u}) [H.IsConvex] (x y : Surreal.{u}) :
    cosetRep H (x - y) = cosetRep H x - cosetRep H y := (cosetRepAddHom H).map_sub x y

variable {J : AddSubgroup Surreal.{u}} [J.IsConvex]

/-- A simplest representative modulo a larger subgroup is fixed modulo a smaller subgroup. -/
theorem cosetRep_cosetRep_of_ge (h : H ≤ J) (x : Surreal.{u}) :
    cosetRep H (cosetRep J x) = cosetRep J x :=
  cosetRep_eq_iff.mpr fun y hy hmem ↦ (cosetRep_eq_iff.mp (cosetRep_cosetRep J x) y hy) (h hmem)

end Surreal
