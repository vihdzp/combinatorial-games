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

universe u

public noncomputable section

namespace Surreal
open IGame SignExpansion

/-- The truncation of a surreal to an ordinal `o` is the unique surreal `truncate o x`
with `birthday (truncate o x) ≤ o` which compares the same to every `y` with `birthday y < o`. -/
def truncate (o : NatOrdinal.{u}) : Surreal.{u} →o Surreal.{u} where
  toFun x := @mk !{fun p => {s : IGame.{u} | s.birthday < o} ∩
    {s | ∃ _ : s.Numeric, p.cases (.mk s < x) (x < .mk s)}} <| by
      rw [numeric_def]
      refine ⟨fun y hy z hz => ?_, fun p y hy => ?_⟩
      · rw [moves_ofSets] at hy hz
        exact (@mk_lt_mk y z hy.2.1 hz.2.1).mp (hy.2.2.trans hz.2.2)
      · rw [moves_ofSets] at hy
        exact hy.2.1
  monotone' := by
    intro x y hxy
    simp_rw [Surreal.mk_le_mk]
    rw [le_iff_forall_lf]
    refine ⟨fun z hz => left_lf ?_, fun z hz => lf_right ?_⟩ <;> rw [moves_ofSets] at hz ⊢
    · exact ⟨hz.1, hz.2.1, hz.2.2.trans_le hxy⟩
    · exact ⟨hz.1, hz.2.1, hxy.trans_lt hz.2.2⟩

private theorem truncate_apply (o : NatOrdinal.{u}) (x : Surreal.{u}) :
    ∃ h : Numeric _, truncate o x = @mk !{fun p => {s : IGame.{u} | s.birthday < o} ∩
      {s | ∃ _ : s.Numeric, p.cases (.mk s < x) (x < .mk s)}} h := ⟨_, rfl⟩

theorem birthday_truncate_le (o : NatOrdinal.{u}) (x : Surreal.{u}) :
    (truncate o x).birthday ≤ o := by
  obtain ⟨_, h⟩ := truncate_apply o x
  rw [h]
  apply (birthday_mk_le _).trans
  rw [birthday_le_iff]
  intro p y hy
  rw [moves_ofSets] at hy
  exact hy.1

theorem truncate_of_birthday_le {o : NatOrdinal.{u}} {x : Surreal.{u}}
    (h : x.birthday ≤ o) : x.truncate o = x := by
  obtain ⟨k, nk, rfl, hk⟩ := x.birthday_eq_iGameBirthday
  rw [← hk] at h
  obtain ⟨_, ht⟩ := truncate_apply o (mk k)
  rw [ht, Surreal.mk_eq_mk]
  symm
  apply Fits.equiv_of_forall_birthday_le
  · constructor <;> simp +contextual
  · intro z nz hz
    apply le_of_not_gt
    intro hbb
    have hne : mk z ≠ mk k := by
      intro eq
      rw [hk, ← eq] at hbb
      exact not_le_of_gt hbb (birthday_mk_le z)
    obtain hzk | hkz := lt_or_gt_of_ne hne
    · refine hz.left z ?_ le_rfl
      rw [moves_ofSets]
      exact ⟨hbb.trans_le h, nz, hzk⟩
    · refine hz.right z ?_ le_rfl
      rw [moves_ofSets]
      exact ⟨hbb.trans_le h, nz, hkz⟩

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
  obtain ⟨_, h⟩ := truncate_apply o x
  obtain ⟨k, nk, rfl, hk⟩ := y.birthday_eq_iGameBirthday
  rw [h, mk_lt_mk]
  apply Numeric.lt_right
  rw [moves_ofSets]
  exact ⟨hk.trans_lt hy, nk, hxy⟩

private theorem lt_truncate_of_lt {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) (hxy : y < x) : y < x.truncate o := by
  obtain ⟨_, h⟩ := truncate_apply o x
  obtain ⟨k, nk, rfl, hk⟩ := y.birthday_eq_iGameBirthday
  rw [h, mk_lt_mk]
  apply Numeric.left_lt
  rw [moves_ofSets]
  exact ⟨hk.trans_lt hy, nk, hxy⟩

theorem truncate_lt_iff_lt {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) : x.truncate o < y ↔ x < y := by
  obtain h | rfl | h := lt_trichotomy x y
  · exact iff_of_true (truncate_lt_of_lt hy h) h
  · exact iff_of_false (truncate_eq_self_iff.2 hy.le).not_lt (lt_irrefl _)
  · exact iff_of_false (lt_truncate_of_lt hy h).not_gt h.not_gt

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
  obtain ⟨_, h⟩ := truncate_apply o x
  obtain ⟨k, nk, rfl, hk⟩ := y.birthday_eq_iGameBirthday
  rw [h, eq_comm, mk_eq_mk]
  apply Fits.equiv_of_forall_birthday_le
  · constructor
    · rw [moves_ofSets]
      intro z hz
      obtain ⟨hzb, zn, hz⟩ := hz
      rw [← mk_le_mk, not_le, hgt (mk z) ((birthday_mk_le z).trans_lt hzb)]
      exact hz
    · rw [moves_ofSets]
      intro z hz
      obtain ⟨hzb, zn, hz⟩ := hz
      rw [← mk_le_mk, not_le, hlt (mk z) ((birthday_mk_le z).trans_lt hzb)]
      exact hz
  · intro z zn hz
    by_contra! hzb
    obtain hzk | hzk | hkz := lt_trichotomy (mk z) (mk k)
    · refine hz.1 z ?_ le_rfl
      rw [moves_ofSets, Set.mem_inter_iff, Set.mem_setOf, Set.mem_setOf]
      exact ⟨by order, zn, (hgt (mk z) (by order [birthday_mk_le z])).1 hzk⟩
    · absurd hzb
      rw [hk, ← hzk]
      exact (birthday_mk_le z).not_gt
    · refine hz.2 z ?_ le_rfl
      rw [moves_ofSets, Set.mem_inter_iff, Set.mem_setOf, Set.mem_setOf]
      exact ⟨by order, zn, (hlt (mk z) (by order [birthday_mk_le z])).1 hkz⟩

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

/-- To every surreal is associated a unique sign expansion, which can be seen as
a sequence of directions along an ordinal-depth complete binary tree.
The `o`'th term of this sign sequence is `+` if `truncate o x < x`,
`-` if `x < truncate o x`, and `0` if `truncate o x = x`. -/
def ofSurreal : Surreal.{u} ↪o SignExpansion :=
  .ofStrictMono (fun x =>
    { sign i := .sign (x - x.truncate i)
      isUpperSet_preimage_singleton_zero' := by
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
      apply truncate_eq_of_birthday_le_of_forall_lt_gt_iff (birthday_truncate_le j c)
      · intro k hk
        rw [truncate_lt_iff_lt hk]
        specialize hdcc k (hk.trans_le hj)
        by_contra h
        rw [Set.mem_Icc] at hc hz hdcc
        push +distrib Not at hdcc h
        cases h <;> cases hdcc <;> order
      · intro k hk
        rw [lt_truncate_iff_lt hk]
        specialize hdcc k (hk.trans_le hj)
        by_contra h
        rw [Set.mem_Icc] at hc hz hdcc
        push +distrib Not at hdcc h
        cases h <;> cases hdcc <;> order
    refine ⟨c.birthday, fun j hj => ?_, ?_⟩
    · have htj : c.truncate j ∉ Set.Icc x y := hdcc _ ((birthday_truncate_le j c).trans_lt hj)
      simp only [Set.mem_Icc, Classical.not_and_iff_not_or_not] at htj
      by_contra! h
      /-
      simp? [hcxy j hj.le x (Set.left_mem_Icc.2 hxy.le),
        hcxy j hj.le y (Set.right_mem_Icc.2 hxy.le),
        sign_apply, ite_eq_iff, eq_ite_iff, imp_iff_not_or, and_or_left, or_and_right] at h
      -/
      simp only [sign_apply, sub_pos, sub_neg, coe_mk, Pi.toLex_apply,
        hcxy j hj.le x (Set.left_mem_Icc.2 hxy.le), hcxy j hj.le y (Set.right_mem_Icc.2 hxy.le),
        ne_eq, eq_ite_iff, ite_eq_left_iff, not_lt, ite_eq_iff, SignType.neg_eq_self_iff,
        one_ne_zero, and_false, zero_ne_one, or_self, imp_false, not_le, SignType.self_eq_neg_iff,
        reduceCtorEq, false_or, SignType.neg_eq_zero_iff, and_or_left, not_or,
        not_and, imp_iff_not_or, or_and_right, and_self] at h
      -- this proof is very slow (unsurprisingly, since it splits into 80 cases)
      -- TODO: find a faster proof
      casesm* _ ∨ _ <;> order
    · simp only [Set.mem_Icc] at hc
      by_contra! h
      /-
      simp? [hcxy _ le_rfl x (Set.left_mem_Icc.2 hxy.le),
        hcxy _ le_rfl y (Set.right_mem_Icc.2 hxy.le),
        sign_apply, ite_le_iff, le_ite_iff, and_or_left] at h
      -/
      simp only [sign_apply, sub_pos, sub_neg, coe_mk, Pi.toLex_apply,
        hcxy _ le_rfl y (Set.right_mem_Icc.2 hxy.le), truncate_birthday_self,
        hcxy _ le_rfl x (Set.left_mem_Icc.2 hxy.le), le_ite_iff, ite_le_iff, Std.le_refl, and_true,
        not_lt, SignType.le_one, zero_le_one, and_or_left, SignType.le_neg_one_iff,
        SignType.self_eq_neg_iff, one_ne_zero, and_false, reduceCtorEq, or_false, false_or,
        SignType.one_le_iff, zero_ne_one, SignType.neg_one_le] at h
      -- this proof is not as slow as the other one, it only has 6 cases
      -- TODO: find a better proof
      casesm* _ ∨ _ <;> order

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

theorem ofSurreal_truncate_apply_of_lt {x : Surreal.{u}} {o₁ o₂ : NatOrdinal.{u}}
    (h : o₂ < o₁) : ofSurreal (x.truncate o₁) o₂ = ofSurreal x o₂ := by
  rw [ofSurreal_apply, truncate_truncate, min_eq_right_of_lt h, ofSurreal_apply]
  simp_rw [sign_apply, sub_pos, sub_neg,
    lt_truncate_iff_lt ((birthday_truncate_le o₂ x).trans_lt h),
    truncate_lt_iff_lt ((birthday_truncate_le o₂ x).trans_lt h)]

theorem ofSurreal_truncate_apply_of_ge {x : Surreal.{u}} {o₁ o₂ : NatOrdinal.{u}}
    (h : o₁ ≤ o₂) : ofSurreal (x.truncate o₁) o₂ = 0 :=
  apply_eq_zero.2 ((length_ofSurreal _).trans_le (WithTop.coe_le_coe.2
    ((birthday_truncate_le o₁ x).trans h)))

theorem range_ofSurreal : Set.range ofSurreal.{u} = { f | f.length ≠ ⊤ } := by
  apply subset_antisymm
  · rw [Set.range_subset_iff]
    exact fun _ => (length_ofSurreal _).trans_ne WithTop.coe_ne_top
  · intro f hf
    rw [Set.mem_setOf, WithTop.ne_top_iff_exists] at hf
    obtain ⟨l, hl⟩ := hf
    rw [Set.mem_range]
    induction l using WellFoundedLT.induction generalizing f with
    | ind l ih =>
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
        rw [moves_ofSets, Set.mem_inter_iff, Set.mem_setOf] at hm
        exact hm.left
      refine ⟨mk g, ?_⟩
      ext o
      induction o using WellFoundedLT.induction with
      | ind o ih =>
        rw [ofSurreal_apply]
        obtain ⟨k, nk, hkg, hkb⟩ := birthday_eq_iGameBirthday ((mk g).truncate o)
        cases hfo : f o with
        | zero =>
          rw [SignType.zero_eq_zero, sign_eq_zero_iff, sub_eq_zero, eq_comm, truncate_eq_self_iff]
          apply ((birthday_mk_le g).trans hgo).trans
          rw [← WithTop.coe_le_coe, hl, ← apply_eq_zero, hfo, SignType.zero_eq_zero]
        | neg =>
          rw [SignType.neg_eq_neg_one, sign_eq_neg_one_iff, sub_neg, ← hkg, mk_lt_mk]
          apply Numeric.lt_right
          rw [moves_ofSets, Set.mem_inter_iff, Set.mem_setOf, Set.mem_setOf]
          refine ⟨(hkb.trans_le (birthday_truncate_le o (mk g))).trans_lt ?_, nk, ?_⟩
          · rw [← WithTop.coe_lt_coe, hl, ← not_le, ← apply_eq_zero, hfo]
            decide
          · rw [hkg]
            refine ⟨o, fun j hj => ?_, ?_⟩
            · simp [← ih j hj, ofSurreal_truncate_apply_of_lt hj]
            · simp [hfo, ofSurreal_truncate_apply_of_ge le_rfl]
        | pos =>
          rw [SignType.pos_eq_one, sign_eq_one_iff, sub_pos, ← hkg, mk_lt_mk]
          apply Numeric.left_lt
          rw [moves_ofSets, Set.mem_inter_iff, Set.mem_setOf, Set.mem_setOf]
          refine ⟨(hkb.trans_le (birthday_truncate_le o (mk g))).trans_lt ?_, nk, ?_⟩
          · rw [← WithTop.coe_lt_coe, hl, ← not_le, ← apply_eq_zero, hfo]
            decide
          · rw [hkg]
            refine ⟨o, fun j hj => ?_, ?_⟩
            · simp [← ih j hj, ofSurreal_truncate_apply_of_lt hj]
            · simp [hfo, ofSurreal_truncate_apply_of_ge le_rfl]

end Surreal
