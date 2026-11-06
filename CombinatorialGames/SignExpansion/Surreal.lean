/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import CombinatorialGames.SignExpansion.Basic
public import CombinatorialGames.Surreal.Birthday.Basic

import CombinatorialGames.Surreal.Cut
import Mathlib.Tactic.Order

/-!
# Sign expansions

In this file we define the correspondence between surreals and sign expansions. This map can be
uniquely characterized as the order-preserving map such that every surreal gets mapped to a sign
sequence whose length equals its birthday.
-/

universe u

public noncomputable section

theorem sign_sub_eq_of_notMem_Icc {α : Type*} [LinearOrder α]
    [AddGroup α] [AddRightMono α] {x y z : α} (hxy : x ≤ y) (hz : z ∉ Set.Icc x y) :
    SignType.sign (x - z) = SignType.sign (y - z) := by
  obtain hzx | hyz : z < x ∨ y < z := by grind
  · have := hzx.trans_le hxy
    rw [sign_eq_one_iff.2, sign_eq_one_iff.2] <;> simpa
  · have := hxy.trans_lt hyz
    rw [sign_eq_neg_one_iff.2, sign_eq_neg_one_iff.2] <;> simpa

theorem sign_sub_lt_of_mem_Icc {α : Type*} [LinearOrder α]
    [AddGroup α] [AddRightMono α] {x y z : α} (hxy : x < y) (hz : z ∈ Set.Icc x y) :
    SignType.sign (x - z) < SignType.sign (y - z) := by
  obtain rfl | hxz := hz.1.eq_or_lt
  · simpa [sign_eq_one_iff]
  obtain rfl | hzy := hz.2.eq_or_lt
  · simpa [sign_eq_neg_one_iff]
  rw [sign_eq_neg_one_iff.2, sign_eq_one_iff.2]
  · simp
  · simpa
  · simpa

/-- Recursor for `SignType` using the preferred forms `0`, `-1`, and `1`. -/
@[expose, elab_as_elim, cases_eliminator, induction_eliminator]
def SignType.recZeroNegOne {motive : SignType → Sort*}
    (zero : motive 0) (neg_one : motive (-1)) (one : motive 1) (t : SignType) : motive t :=
  match t with
  | 0 => zero
  | -1 => neg_one
  | 1 => one

@[simp]
theorem SignType.recZeroNegOne_zero {motive : SignType → Sort*}
    (zero : motive 0) (neg_one : motive (-1)) (one : motive 1) :
    recZeroNegOne zero neg_one one 0 = zero := rfl

@[simp]
theorem SignType.recZeroNegOne_neg_one {motive : SignType → Sort*}
    (zero : motive 0) (neg_one : motive (-1)) (one : motive 1) :
    recZeroNegOne zero neg_one one (-1) = neg_one := rfl

@[simp]
theorem SignType.recZeroNegOne_one {motive : SignType → Sort*}
    (zero : motive 0) (neg_one : motive (-1)) (one : motive 1) :
    recZeroNegOne zero neg_one one 1 = one := rfl

@[simp]
theorem SignType.recZeroNegOne_neg {motive : SignType → Sort*}
    (zero : motive 0) (neg_one : motive (-1)) (one : motive 1) (t : SignType) :
    @recZeroNegOne motive zero neg_one one (-t) =
      recZeroNegOne zero one neg_one t := by cases t <;> rfl

open Surreal IGame SignExpansion
namespace Surreal

/-- The truncation of a surreal to an ordinal `o` is the unique surreal `trunc o x`
with `birthday (trunc o x) ≤ o` which compares the same to every `y` with `birthday y < o`. -/
def trunc (o : NatOrdinal.{u}) : Surreal.{u} →o Surreal.{u} where
  toFun x := !{fun p => {y | y.birthday < o} ∩ {s | p.cases (s < x) (x < s)}}'
    (fun u hu v hv => hu.2.trans hv.2)
  monotone' := by
    apply id
    intro x y hxy
    rw [Surreal.ofSets_le_ofSets_iff']
    constructor
    · intro z hz
      apply Surreal.lt_ofSets_of_mem_left'
      exact ⟨hz.1, hz.2.trans_le hxy⟩
    · intro z hz
      apply Surreal.ofSets_lt_of_mem_right'
      exact ⟨hz.1, hxy.trans_lt hz.2⟩

theorem birthday_trunc_le (o : NatOrdinal.{u}) (x : Surreal.{u}) :
    (trunc o x).birthday ≤ o := by
  rw [trunc, OrderHom.coe_mk]
  apply birthday_ofSets_le'.trans
  apply csSup_le'
  rw [mem_upperBounds, Set.forall_mem_image, Set.forall_mem_iUnion]
  intro p y hy
  exact Order.add_one_le_of_lt hy.1

@[simp]
theorem trunc_eq_self_iff {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    x.trunc o = x ↔ x.birthday ≤ o := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine le_of_not_gt fun ho => ne_of_lt ?_ (congrArg birthday h)
    exact (x.birthday_trunc_le o).trans_lt ho
  · rw [trunc, OrderHom.coe_mk]
    apply Surreal.ofSets_eq_of_forall_birthday_le'
    · simp
    · simp
    · intro z hzl hzr
      by_contra! hbb
      obtain hzx | hxz := lt_or_gt_of_ne (ne_of_apply_ne birthday hbb.ne)
      · exact (hzl z ⟨hbb.trans_le h, hzx⟩).false
      · exact (hzr z ⟨hbb.trans_le h, hxz⟩).false

@[simp]
theorem trunc_birthday_self {x : Surreal.{u}} :
    x.trunc x.birthday = x := by simp

private theorem trunc_lt_of_lt {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) (hxy : x < y) : x.trunc o < y := by
  rw [trunc, OrderHom.coe_mk]
  apply ofSets_lt_of_mem_right'
  exact ⟨hy, hxy⟩

private theorem lt_trunc_of_lt {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) (hxy : y < x) : y < x.trunc o := by
  rw [trunc, OrderHom.coe_mk]
  apply lt_ofSets_of_mem_left'
  exact ⟨hy, hxy⟩

@[grind =]
theorem trunc_lt_iff_lt {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) : x.trunc o < y ↔ x < y := by
  obtain h | rfl | h := lt_trichotomy x y
  · exact iff_of_true (trunc_lt_of_lt hy h) h
  · exact iff_of_false (trunc_eq_self_iff.2 hy.le).not_lt (lt_irrefl _)
  · exact iff_of_false (lt_trunc_of_lt hy h).not_gt h.not_gt

@[grind =]
theorem lt_trunc_iff_lt {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) : y < x.trunc o ↔ y < x := by
  obtain h | rfl | h := lt_trichotomy x y
  · exact iff_of_false (trunc_lt_of_lt hy h).not_gt h.not_gt
  · exact iff_of_false (trunc_eq_self_iff.2 hy.le).not_gt (lt_irrefl _)
  · exact iff_of_true (lt_trunc_of_lt hy h) h

theorem trunc_le_iff_le {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) : x.trunc o ≤ y ↔ x ≤ y := by
  simpa using (lt_trunc_iff_lt hy).not

theorem le_trunc_iff_le {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) : y ≤ x.trunc o ↔ y ≤ x := by
  simpa using (trunc_lt_iff_lt hy).not

theorem trunc_eq_of_birthday_le_of_forall_lt_gt_iff
    {x y : Surreal.{u}} {o : NatOrdinal.{u}} (hy : y.birthday ≤ o)
    (hlt : ∀ z, z.birthday < o → (y < z ↔ x < z))
    (hgt : ∀ z, z.birthday < o → (z < y ↔ z < x)) :
    x.trunc o = y := by
  rw [trunc, OrderHom.coe_mk]
  apply ofSets_eq_of_forall_birthday_le'
  · intro z hz
    exact (hgt z hz.1).2 hz.2
  · intro z hz
    exact (hlt z hz.1).2 hz.2
  · intro z hzl hzr
    by_contra! hzb
    obtain hzy | hyz := lt_or_gt_of_ne (ne_of_apply_ne birthday hzb.ne)
    · exact (hzl z ⟨hzb.trans_le hy, (hgt z (hzb.trans_le hy)).1 hzy⟩).false
    · exact (hzr z ⟨hzb.trans_le hy, (hlt z (hzb.trans_le hy)).1 hyz⟩).false

theorem trunc_eq_of_birthday_le_of_forall_le_ge_iff
    {x y : Surreal.{u}} {o : NatOrdinal.{u}} (hy : y.birthday ≤ o)
    (hle : ∀ z, z.birthday < o → (y ≤ z ↔ x ≤ z))
    (hge : ∀ z, z.birthday < o → (z ≤ y ↔ z ≤ x)) :
    x.trunc o = y :=
  trunc_eq_of_birthday_le_of_forall_lt_gt_iff hy
    (fun z hz => by simpa using (hge z hz).not)
    (fun z hz => by simpa using (hle z hz).not)

@[simp]
theorem birthday_trunc {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    (x.trunc o).birthday = min x.birthday o := by
  obtain h | h := le_total x.birthday o
  · rw [trunc_eq_self_iff.2 h, min_eq_left h]
  rw [min_eq_right h]
  apply (birthday_trunc_le o x).antisymm
  contrapose! h
  refine lt_of_eq_of_lt (congrArg birthday ?_) h
  apply le_antisymm
  · rw [← trunc_le_iff_le h]
  · rw [← le_trunc_iff_le h]

theorem trunc_trunc {x : Surreal.{u}} {o₁ o₂ : NatOrdinal.{u}} :
    (x.trunc o₁).trunc o₂ = x.trunc (min o₁ o₂) := by
  refine (trunc_eq_of_birthday_le_of_forall_lt_gt_iff ?_ ?_ ?_).symm
  · rw [birthday_trunc, birthday_trunc]
    order
  · intro z hz
    rw [trunc_lt_iff_lt (hz.trans_le (min_le_right o₁ o₂)),
      trunc_lt_iff_lt (hz.trans_le (min_le_left o₁ o₂))]
  · intro z hz
    rw [lt_trunc_iff_lt (hz.trans_le (min_le_right o₁ o₂)),
      lt_trunc_iff_lt (hz.trans_le (min_le_left o₁ o₂))]

end Surreal

namespace SignExpansion

/-- To every surreal is associated a unique sign expansion, which can be seen as
a sequence of directions along an ordinal-depth complete binary tree.
The `o`'th term of this sign sequence is `+` if `trunc o x < x`,
`-` if `x < trunc o x`, and `0` if `trunc o x = x`. -/
def ofSurreal : Surreal.{u} ↪o SignExpansion :=
  .ofStrictMono (fun x =>
    { sign i := .sign (x - x.trunc i)
      isUpperSet_preimage_singleton_zero' := by
        apply id
        intro a b hab ha
        rw [Set.mem_preimage, Set.mem_singleton_iff,
          sign_eq_zero_iff, sub_eq_zero, eq_comm, trunc_eq_self_iff] at ha ⊢
        exact ha.trans hab }) fun x y hxy => by
    have cxy : Cut.leftSurreal x < Cut.rightSurreal y := by simpa using hxy.le
    let c := Cut.simplestBtwn cxy
    have hc : c ∈ Set.Icc x y := Cut.fits_simplestBtwn cxy
    have hdcc (d : Surreal) (hd : d.birthday < c.birthday) : d ∉ Set.Icc x y := by
      contrapose! hd
      apply Cut.birthday_simplestBtwn_le_of_fits
      exact hd
    have hcxy (j : NatOrdinal) (hj : j ≤ c.birthday)
        (z : Surreal) (hz : z ∈ Set.Icc x y) : z.trunc j = c.trunc j := by
      apply trunc_eq_of_birthday_le_of_forall_lt_gt_iff (birthday_trunc_le j c) <;> grind
    rw [lt_iff_toLex]
    refine ⟨c.birthday, fun j hj => ?_, ?_⟩ <;> dsimp
    · rw [hcxy j hj.le x (Set.left_mem_Icc.2 hxy.le), hcxy j hj.le y (Set.right_mem_Icc.2 hxy.le)]
      exact sign_sub_eq_of_notMem_Icc hxy.le (hdcc _ ((birthday_trunc_le j c).trans_lt hj))
    · rw [hcxy _ le_rfl x (Set.left_mem_Icc.2 hxy.le), hcxy _ le_rfl y (Set.right_mem_Icc.2 hxy.le)]
      apply sign_sub_lt_of_mem_Icc hxy
      simpa

theorem ofSurreal_apply (x : Surreal.{u}) (o : NatOrdinal.{u}) :
    ofSurreal x o = .sign (x - x.trunc o) := (rfl)

theorem ofSurreal_eq_neg_one_iff {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    ofSurreal x o = -1 ↔ x < x.trunc o := by
  rw [ofSurreal_apply, sign_eq_neg_one_iff, sub_lt_zero]

theorem ofSurreal_eq_zero_iff {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    ofSurreal x o = 0 ↔ x.trunc o = x := by
  rw [ofSurreal_apply, sign_eq_zero_iff, sub_eq_zero, eq_comm]

theorem ofSurreal_eq_one_iff {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    ofSurreal x o = 1 ↔ x.trunc o < x := by
  rw [ofSurreal_apply, sign_eq_one_iff, sub_pos]

@[simp]
theorem length_ofSurreal (x : Surreal.{u}) :
    (ofSurreal x).length = x.birthday := by
  apply eq_of_forall_ge_iff
  intro c
  cases c with
  | top => simp
  | coe c => rw [← apply_eq_zero, ofSurreal_eq_zero_iff, trunc_eq_self_iff, WithTop.coe_le_coe]

@[simp]
theorem ofSurreal_trunc {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    ofSurreal (x.trunc o) = (ofSurreal x).trunc o := by
  ext o'
  obtain h | h := lt_or_ge o' o
  · rw [ofSurreal_apply, trunc_trunc, min_eq_right_of_lt h,
      trunc_apply_of_coe_lt (WithTop.coe_lt_coe.2 h), ofSurreal_apply]
    simp_rw [sign_apply, sub_pos, sub_neg,
      lt_trunc_iff_lt ((birthday_trunc_le o' x).trans_lt h),
      trunc_lt_iff_lt ((birthday_trunc_le o' x).trans_lt h)]
  · rw [trunc_apply_of_le_coe (WithTop.coe_le_coe.2 h), apply_eq_zero,
      length_ofSurreal, WithTop.coe_le_coe]
    exact (birthday_trunc_le o x).trans h

@[simp]
theorem small_ofSurreal (x : Surreal) : (ofSurreal x).Small :=
  small_iff_length_lt_top.2 (by simp)

theorem range_ofSurreal : Set.range ofSurreal.{u} = .ofPred Small := by
  apply subset_antisymm
  · simp [Set.range_subset_iff]
  · intro f hf
    rw [Set.mem_ofPred, small_iff_length_ne_top, WithTop.ne_top_iff_exists] at hf
    obtain ⟨l, hl⟩ := hf
    rw [Set.mem_range]
    induction l using WellFoundedLT.induction generalizing f with | ind l ih
    replace ih (f : SignExpansion) (hl : f.length < l) :=
      ih (f.length.untop (ne_top_of_lt hl))
        ((WithTop.untop_lt_iff _).2 hl) (WithTop.coe_untop _ _)
    choose u hu using ih
    let g : IGame := !{fun p => {s : IGame.{u} | s.birthday < l} ∩
      {s | ∃ _ : s.Numeric, p.cases (ofSurreal (.mk s) < f) (f < ofSurreal (.mk s))}}
    have hgn : g.Numeric := by
      rw [numeric_def]
      refine ⟨fun y hy z hz => ?_, fun p y hy => ?_⟩
      · rw [moves_ofSets] at hy hz
        exact (@mk_lt_mk y z hy.2.1 hz.2.1).mp (ofSurreal.lt_iff_lt.1 (hy.2.2.trans hz.2.2))
      · rw [moves_ofSets] at hy
        exact hy.2.1
    have hgo : g.birthday ≤ l := by
      rw [birthday_le_iff]
      intro p m hm
      rw [moves_ofSets, Set.mem_inter_iff, Set.mem_ofPred] at hm
      exact hm.left
    refine ⟨Surreal.mk g, ?_⟩
    ext o
    induction o using WellFoundedLT.induction with | ind o ih
    obtain ⟨k, nk, hkg, hkb⟩ := birthday_eq_iGameBirthday ((Surreal.mk g).trunc o)
    cases hfo : f o with
    | zero =>
      rw [ofSurreal_eq_zero_iff, trunc_eq_self_iff]
      apply ((birthday_mk_le g).trans hgo).trans
      rw [← WithTop.coe_le_coe, hl, ← apply_eq_zero, hfo]
    | neg_one =>
      rw [ofSurreal_eq_neg_one_iff, ← hkg, mk_lt_mk]
      apply Numeric.lt_right
      rw [moves_ofSets, Set.mem_inter_iff, Set.mem_ofPred, Set.mem_ofPred]
      refine ⟨(hkb.trans_le (birthday_trunc_le o (Surreal.mk g))).trans_lt ?_, nk, ?_⟩
      · rw [← WithTop.coe_lt_coe, hl, ← not_le, ← apply_eq_zero, hfo]
        decide
      · rw [hkg]
        refine ⟨o, fun j hj => ?_, ?_⟩
        · simp [← ih j hj, trunc_apply_of_coe_lt (WithTop.coe_lt_coe.2 hj)]
        · simp [hfo, trunc_apply_of_le_coe le_rfl]
    | one =>
      rw [ofSurreal_eq_one_iff, ← hkg, mk_lt_mk]
      apply Numeric.left_lt
      rw [moves_ofSets, Set.mem_inter_iff, Set.mem_ofPred, Set.mem_ofPred]
      refine ⟨(hkb.trans_le (birthday_trunc_le o (Surreal.mk g))).trans_lt ?_, nk, ?_⟩
      · rw [← WithTop.coe_lt_coe, hl, ← not_le, ← apply_eq_zero, hfo]
        decide
      · rw [hkg]
        refine ⟨o, fun j hj => ?_, ?_⟩
        · simp [← ih j hj, trunc_apply_of_coe_lt (WithTop.coe_lt_coe.2 hj)]
        · simp [hfo, trunc_apply_of_le_coe le_rfl]

end SignExpansion
