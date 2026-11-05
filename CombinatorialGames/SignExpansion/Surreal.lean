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
# Sign Expansions

Every surreal number has a sign expansion, a function from its birthday to the set `{-1, 1}`.
This sign expansion uniquely identifies the number.
-/

public theorem ite_lt_iff {α : Type*} [LT α] {P : Prop} [Decidable P] {a b c : α} :
    (if P then a else b) < c ↔ P ∧ a < c ∨ ¬P ∧ b < c := by split <;> simp_all

public theorem lt_ite_iff {α : Type*} [LT α] {P : Prop} [Decidable P] {a b c : α} :
    a < (if P then b else c) ↔ P ∧ a < b ∨ ¬P ∧ a < c := by split <;> simp_all

public theorem ite_le_iff {α : Type*} [LE α] {P : Prop} [Decidable P] {a b c : α} :
    (if P then a else b) ≤ c ↔ P ∧ a ≤ c ∨ ¬P ∧ b ≤ c := by split <;> simp_all

public theorem le_ite_iff {α : Type*} [LE α] {P : Prop} [Decidable P] {a b c : α} :
    a ≤ (if P then b else c) ↔ P ∧ a ≤ b ∨ ¬P ∧ a ≤ c := by split <;> simp_all

theorem sign_sub_eq_of_not_mem_Icc {α : Type*} [LinearOrder α]
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

universe u

public noncomputable section

open Surreal IGame SignExpansion
namespace Surreal

/-- The truncation of a surreal to an ordinal `o` is the unique surreal `truncate o x`
with `birthday (truncate o x) ≤ o` which compares the same to every `y` with `birthday y < o`. -/
def truncate (o : NatOrdinal.{u}) : Surreal.{u} →o Surreal.{u} where
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

theorem birthday_truncate_le (o : NatOrdinal.{u}) (x : Surreal.{u}) :
    (truncate o x).birthday ≤ o := by
  rw [truncate, OrderHom.coe_mk]
  apply birthday_ofSets_le'.trans
  apply csSup_le'
  rw [mem_upperBounds, Set.forall_mem_image, Set.forall_mem_iUnion]
  intro p y hy
  exact Order.add_one_le_of_lt hy.1

theorem truncate_of_birthday_le {o : NatOrdinal.{u}} {x : Surreal.{u}}
    (h : x.birthday ≤ o) : x.truncate o = x := by
  rw [truncate, OrderHom.coe_mk]
  apply Surreal.ofSets_eq_of_forall_birthday_le'
  · simp
  · simp
  · intro z hzl hzr
    by_contra! hbb
    obtain hzx | hxz := lt_or_gt_of_ne (ne_of_apply_ne birthday hbb.ne)
    · exact (hzl z ⟨hbb.trans_le h, hzx⟩).false
    · exact (hzr z ⟨hbb.trans_le h, hxz⟩).false

@[simp]
theorem truncate_eq_self_iff {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    x.truncate o = x ↔ x.birthday ≤ o := by
  refine ⟨fun h => ?_, truncate_of_birthday_le⟩
  refine le_of_not_gt fun ho => ne_of_lt ?_ (congrArg birthday h)
  exact (x.birthday_truncate_le o).trans_lt ho

@[simp]
theorem truncate_birthday_self {x : Surreal.{u}} :
    x.truncate x.birthday = x := by simp

private theorem truncate_lt_of_lt {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) (hxy : x < y) : x.truncate o < y := by
  rw [truncate, OrderHom.coe_mk]
  apply ofSets_lt_of_mem_right'
  exact ⟨hy, hxy⟩

private theorem lt_truncate_of_lt {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) (hxy : y < x) : y < x.truncate o := by
  rw [truncate, OrderHom.coe_mk]
  apply lt_ofSets_of_mem_left'
  exact ⟨hy, hxy⟩

@[grind =]
theorem truncate_lt_iff_lt {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) : x.truncate o < y ↔ x < y := by
  obtain h | rfl | h := lt_trichotomy x y
  · exact iff_of_true (truncate_lt_of_lt hy h) h
  · exact iff_of_false (truncate_eq_self_iff.2 hy.le).not_lt (lt_irrefl _)
  · exact iff_of_false (lt_truncate_of_lt hy h).not_gt h.not_gt

@[grind =]
theorem lt_truncate_iff_lt {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) : y < x.truncate o ↔ y < x := by
  obtain h | rfl | h := lt_trichotomy x y
  · exact iff_of_false (truncate_lt_of_lt hy h).not_gt h.not_gt
  · exact iff_of_false (truncate_eq_self_iff.2 hy.le).not_gt (lt_irrefl _)
  · exact iff_of_true (lt_truncate_of_lt hy h) h

theorem truncate_le_iff_le {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) : x.truncate o ≤ y ↔ x ≤ y := by
  simpa using (lt_truncate_iff_lt hy).not

theorem le_truncate_iff_le {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) : y ≤ x.truncate o ↔ y ≤ x := by
  simpa using (truncate_lt_iff_lt hy).not

theorem truncate_eq_of_birthday_le_of_forall_lt_gt_iff
    {x y : Surreal.{u}} {o : NatOrdinal.{u}} (hy : y.birthday ≤ o)
    (hlt : ∀ z, z.birthday < o → (y < z ↔ x < z))
    (hgt : ∀ z, z.birthday < o → (z < y ↔ z < x)) :
    x.truncate o = y := by
  rw [truncate, OrderHom.coe_mk]
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

theorem truncate_eq_of_birthday_le_of_forall_le_ge_iff
    {x y : Surreal.{u}} {o : NatOrdinal.{u}} (hy : y.birthday ≤ o)
    (hle : ∀ z, z.birthday < o → (y ≤ z ↔ x ≤ z))
    (hge : ∀ z, z.birthday < o → (z ≤ y ↔ z ≤ x)) :
    x.truncate o = y :=
  truncate_eq_of_birthday_le_of_forall_lt_gt_iff hy
    (fun z hz => by simpa using (hge z hz).not)
    (fun z hz => by simpa using (hle z hz).not)

theorem birthday_truncate {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    (x.truncate o).birthday = min o x.birthday := by
  obtain h | h := le_total x.birthday o
  · rw [truncate_eq_self_iff.2 h, min_eq_right h]
  rw [min_eq_left h]
  apply le_antisymm
  · exact birthday_truncate_le o x
  contrapose! h
  refine lt_of_eq_of_lt (congrArg birthday ?_) h
  apply le_antisymm
  · rw [← truncate_le_iff_le h]
  · rw [← le_truncate_iff_le h]

theorem truncate_truncate {x : Surreal.{u}} {o₁ o₂ : NatOrdinal.{u}} :
    (x.truncate o₁).truncate o₂ = x.truncate (min o₁ o₂) := by
  refine (truncate_eq_of_birthday_le_of_forall_lt_gt_iff ?_ ?_ ?_).symm
  · rw [birthday_truncate, birthday_truncate]
    order
  · intro z hz
    rw [truncate_lt_iff_lt (hz.trans_le (min_le_right o₁ o₂)),
      truncate_lt_iff_lt (hz.trans_le (min_le_left o₁ o₂))]
  · intro z hz
    rw [lt_truncate_iff_lt (hz.trans_le (min_le_right o₁ o₂)),
      lt_truncate_iff_lt (hz.trans_le (min_le_left o₁ o₂))]

end Surreal

namespace SignExpansion

/-- To every surreal is associated a unique sign expansion, which can be seen as
a sequence of directions along an ordinal-depth complete binary tree.
The `o`'th term of this sign sequence is `+` if `truncate o x < x`,
`-` if `x < truncate o x`, and `0` if `truncate o x = x`. -/
def ofSurreal : Surreal.{u} ↪o SignExpansion :=
  .ofStrictMono (fun x =>
    { sign i := .sign (x - x.truncate i)
      isUpperSet_preimage_singleton_zero' := by
        apply id
        intro a b hab ha
        rw [Set.mem_preimage, Set.mem_singleton_iff,
          sign_eq_zero_iff, sub_eq_zero, eq_comm, truncate_eq_self_iff] at ha ⊢
        exact ha.trans hab }) fun x y hxy => by
    have cxy : Cut.leftSurreal x < Cut.rightSurreal y := by simpa using hxy.le
    let c := Cut.simplestBtwn cxy
    have hc : c ∈ Set.Icc x y := Cut.fits_simplestBtwn cxy
    rw [lt_iff_toLex]
    have hdcc (d : Surreal) (hd : d.birthday < c.birthday) : d ∉ Set.Icc x y := by
      contrapose! hd
      apply Cut.birthday_simplestBtwn_le_of_fits
      exact hd
    have hcxy (j : NatOrdinal) (hj : j ≤ c.birthday)
        (z : Surreal) (hz : z ∈ Set.Icc x y) : z.truncate j = c.truncate j := by
      apply truncate_eq_of_birthday_le_of_forall_lt_gt_iff (birthday_truncate_le j c) <;> grind
    refine ⟨c.birthday, fun j hj => ?_, ?_⟩ <;> dsimp
    · rw [hcxy j hj.le x (Set.left_mem_Icc.2 hxy.le), hcxy j hj.le y (Set.right_mem_Icc.2 hxy.le)]
      exact sign_sub_eq_of_not_mem_Icc hxy.le (hdcc _ ((birthday_truncate_le j c).trans_lt hj))
    · rw [hcxy _ le_rfl x (Set.left_mem_Icc.2 hxy.le), hcxy _ le_rfl y (Set.right_mem_Icc.2 hxy.le)]
      apply sign_sub_lt_of_mem_Icc hxy
      simpa

theorem ofSurreal_apply (x : Surreal.{u}) (o : NatOrdinal.{u}) :
    ofSurreal x o = .sign (x - x.truncate o) := (rfl)

@[simp]
theorem length_ofSurreal (x : Surreal.{u}) :
    (ofSurreal x).length = x.birthday := by
  apply eq_of_forall_ge_iff
  intro c
  cases c with
  | top => simp
  | coe c =>
    rw [← apply_eq_zero, WithTop.coe_le_coe, ofSurreal_apply,
      sign_eq_zero_iff, sub_eq_zero, eq_comm, truncate_eq_self_iff]

@[simp]
theorem ofSurreal_truncate {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    ofSurreal (x.truncate o) = (ofSurreal x).restrict o := by
  ext o'
  obtain h | h := lt_or_ge o' o
  · rw [ofSurreal_apply, truncate_truncate, min_eq_right_of_lt h,
      restrict_apply_of_coe_lt (WithTop.coe_lt_coe.2 h), ofSurreal_apply]
    simp_rw [sign_apply, sub_pos, sub_neg,
      lt_truncate_iff_lt ((birthday_truncate_le o' x).trans_lt h),
      truncate_lt_iff_lt ((birthday_truncate_le o' x).trans_lt h)]
  · rw [restrict_apply_of_le_coe (WithTop.coe_le_coe.2 h), apply_eq_zero,
      length_ofSurreal, WithTop.coe_le_coe]
    exact (birthday_truncate_le o x).trans h

theorem range_ofSurreal : Set.range ofSurreal.{u} = { f | f.length ≠ ⊤ } := by
  apply subset_antisymm
  · simp [Set.range_subset_iff]
  · intro f hf
    rw [Set.mem_ofPred, WithTop.ne_top_iff_exists] at hf
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
    rw [ofSurreal_apply]
    obtain ⟨k, nk, hkg, hkb⟩ := birthday_eq_iGameBirthday ((Surreal.mk g).truncate o)
    cases hfo : f o with
    | zero =>
      rw [SignType.zero_eq_zero, sign_eq_zero_iff, sub_eq_zero, eq_comm, truncate_eq_self_iff]
      apply ((birthday_mk_le g).trans hgo).trans
      rw [← WithTop.coe_le_coe, hl, ← apply_eq_zero, hfo, SignType.zero_eq_zero]
    | neg =>
      rw [SignType.neg_eq_neg_one, sign_eq_neg_one_iff, sub_neg, ← hkg, mk_lt_mk]
      apply Numeric.lt_right
      rw [moves_ofSets, Set.mem_inter_iff, Set.mem_ofPred, Set.mem_ofPred]
      refine ⟨(hkb.trans_le (birthday_truncate_le o (Surreal.mk g))).trans_lt ?_, nk, ?_⟩
      · rw [← WithTop.coe_lt_coe, hl, ← not_le, ← apply_eq_zero, hfo]
        decide
      · rw [hkg]
        refine ⟨o, fun j hj => ?_, ?_⟩
        · simp [← ih j hj, restrict_apply_of_coe_lt (WithTop.coe_lt_coe.2 hj)]
        · simp [hfo, restrict_apply_of_le_coe le_rfl]
    | pos =>
      rw [SignType.pos_eq_one, sign_eq_one_iff, sub_pos, ← hkg, mk_lt_mk]
      apply Numeric.left_lt
      rw [moves_ofSets, Set.mem_inter_iff, Set.mem_ofPred, Set.mem_ofPred]
      refine ⟨(hkb.trans_le (birthday_truncate_le o (Surreal.mk g))).trans_lt ?_, nk, ?_⟩
      · rw [← WithTop.coe_lt_coe, hl, ← not_le, ← apply_eq_zero, hfo]
        decide
      · rw [hkg]
        refine ⟨o, fun j hj => ?_, ?_⟩
        · simp [← ih j hj, restrict_apply_of_coe_lt (WithTop.coe_lt_coe.2 hj)]
        · simp [hfo, restrict_apply_of_le_coe le_rfl]

end SignExpansion
