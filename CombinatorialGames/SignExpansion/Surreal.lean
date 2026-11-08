/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import CombinatorialGames.SignExpansion.Basic
public import CombinatorialGames.Surreal.Birthday.Basic

import CombinatorialGames.Surreal.Cut

/-!
# Sign expansions

In this file we define the correspondence between surreals and sign expansions. This map can be
uniquely characterized as the order-preserving map such that every surreal gets mapped to a sign
sequence whose length equals its birthday.
-/

universe u

open IGame Set SignExpansion Surreal

public noncomputable section

theorem cmp_eq_cmp_of_notMem_Icc {α : Type*} [LinearOrder α]
    {x y z : α} (hxy : x ≤ y) (hz : z ∉ Icc x y) : cmp x z = cmp y z := by
  obtain hzx | hyz : z < x ∨ y < z := by grind
  · rw [hzx.cmp_eq_gt, (hzx.trans_le hxy).cmp_eq_gt]
  · have := hxy.trans_lt hyz
    rw [hyz.cmp_eq_lt, (hxy.trans_lt hyz).cmp_eq_lt]

-- TODO: should we have a `LinearOrder Ordering` instance?
theorem cmp_lt_cmp_of_mem_Icc {α : Type*} [LinearOrder α]
    {x y z : α} (hxy : x < y) (hz : z ∈ Icc x y) :
    SignType.orderingEquiv.symm (cmp x z) < SignType.orderingEquiv.symm (cmp y z) := by
  obtain rfl | hxz := hz.1.eq_or_lt
  · simpa
  obtain rfl | hzy := hz.2.eq_or_lt
  · simpa
  rw [hxz.cmp_eq_lt, hzy.cmp_eq_gt]
  simp

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

theorem SignType.lt_cases {x y : SignType} :
    x < y ↔ x = -1 ∧ y = 0 ∨ x = -1 ∧ y = 1 ∨ x = 0 ∧ y = 1 := by
  decide +revert

/-! ### Surreals to sign sequences -/

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
  rw [mem_upperBounds, forall_mem_image, forall_mem_iUnion]
  intro p y hy
  exact Order.add_one_le_of_lt hy.1

@[simp]
theorem trunc_eq_self {x : Surreal.{u}} {o : NatOrdinal.{u}} :
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
  · exact iff_of_false (trunc_eq_self.2 hy.le).not_lt (lt_irrefl _)
  · exact iff_of_false (lt_trunc_of_lt hy h).not_gt h.not_gt

@[grind =]
theorem lt_trunc_iff_lt {x y : Surreal.{u}} {o : NatOrdinal.{u}}
    (hy : y.birthday < o) : y < x.trunc o ↔ y < x := by
  obtain h | rfl | h := lt_trichotomy x y
  · exact iff_of_false (trunc_lt_of_lt hy h).not_gt h.not_gt
  · exact iff_of_false (trunc_eq_self.2 hy.le).not_gt (lt_irrefl _)
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
  · rw [trunc_eq_self.2 h, min_eq_left h]
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
  · grw [birthday_trunc, birthday_trunc, min_le_right x.birthday o₁]
  · intro z hz
    rw [trunc_lt_iff_lt (hz.trans_le (min_le_right o₁ o₂)),
      trunc_lt_iff_lt (hz.trans_le (min_le_left o₁ o₂))]
  · intro z hz
    rw [lt_trunc_iff_lt (hz.trans_le (min_le_right o₁ o₂)),
      lt_trunc_iff_lt (hz.trans_le (min_le_left o₁ o₂))]

/-- To every surreal is associated a unique sign expansion, which can be seen as
a sequence of directions along an ordinal-depth complete binary tree.
The `o`'th term of this sign sequence is `+` if `trunc o x < x`,
`-` if `x < trunc o x`, and `0` if `trunc o x = x`. -/
def toSignExpansion : Surreal.{u} ↪o SignExpansion :=
  .ofStrictMono (fun x =>
    { sign i := SignType.orderingEquiv.symm (cmp x (x.trunc i))
      isUpperSet_preimage_singleton_zero' := by
        apply id
        intro a b hab ha
        rw [mem_preimage, mem_singleton_iff, SignType.orderingEquiv_symm_eq_zero_iff,
          cmp_eq_eq_iff, eq_comm, trunc_eq_self] at ha ⊢
        exact ha.trans hab }) fun x y hxy => by
    have cxy : Cut.leftSurreal x < Cut.rightSurreal y := by simpa using hxy.le
    let c := Cut.simplestBtwn cxy
    have hc : c ∈ Icc x y := Cut.fits_simplestBtwn cxy
    have hdcc (d : Surreal) (hd : d.birthday < c.birthday) : d ∉ Icc x y := by
      contrapose! hd
      apply Cut.birthday_simplestBtwn_le_of_fits
      exact hd
    have hcxy (j : NatOrdinal) (hj : j ≤ c.birthday)
        (z : Surreal) (hz : z ∈ Icc x y) : z.trunc j = c.trunc j := by
      apply trunc_eq_of_birthday_le_of_forall_lt_gt_iff (birthday_trunc_le j c) <;> grind
    rw [lt_iff_toLex]
    refine ⟨c.birthday, fun j hj => ?_, ?_⟩ <;> dsimp
    · rw [hcxy j hj.le x (left_mem_Icc.2 hxy.le), hcxy j hj.le y (right_mem_Icc.2 hxy.le)]
      congr 1
      exact cmp_eq_cmp_of_notMem_Icc hxy.le (hdcc _ ((birthday_trunc_le j c).trans_lt hj))
    · rw [hcxy _ le_rfl x (left_mem_Icc.2 hxy.le), hcxy _ le_rfl y (right_mem_Icc.2 hxy.le)]
      apply cmp_lt_cmp_of_mem_Icc hxy
      simpa

theorem toSignExpansion_apply (x : Surreal.{u}) (o : NatOrdinal.{u}) :
    toSignExpansion x o = SignType.orderingEquiv.symm (cmp x (x.trunc o)) := (rfl)

theorem toSignExpansion_eq_neg_one_iff {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    toSignExpansion x o = -1 ↔ x < x.trunc o := by
  rw [toSignExpansion_apply, SignType.orderingEquiv_symm_eq_neg_one_iff, cmp_eq_lt_iff]

theorem toSignExpansion_eq_zero_iff {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    toSignExpansion x o = 0 ↔ x.trunc o = x := by
  rw [toSignExpansion_apply, SignType.orderingEquiv_symm_eq_zero_iff, cmp_eq_eq_iff, eq_comm]

theorem toSignExpansion_eq_one_iff {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    toSignExpansion x o = 1 ↔ x.trunc o < x := by
  rw [toSignExpansion_apply, SignType.orderingEquiv_symm_eq_one_iff, cmp_eq_gt_iff]

@[simp]
theorem length_toSignExpansion (x : Surreal.{u}) :
    (toSignExpansion x).length = x.birthday := by
  apply eq_of_forall_ge_iff
  intro c
  cases c with
  | top => simp
  | coe c =>
    rw [← apply_eq_zero, toSignExpansion_eq_zero_iff, trunc_eq_self, WithTop.coe_le_coe]

@[simp]
instance small_toSignExpansion (x : Surreal) : (toSignExpansion x).Small :=
  small_iff_length_lt_top.2 (by simp)

@[simp]
theorem toSignExpansion_trunc {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    toSignExpansion (x.trunc o) = (toSignExpansion x).trunc o := by
  ext o'
  obtain h | h := lt_or_ge o' o
  · rw [toSignExpansion_apply, trunc_trunc, min_eq_right_of_lt h,
      trunc_apply_of_coe_lt (WithTop.coe_lt_coe.2 h), toSignExpansion_apply]
    simp_rw [SignType.orderingEquiv_symm_cmp, sign_apply, sub_pos, sub_neg,
      lt_trunc_iff_lt ((birthday_trunc_le o' x).trans_lt h),
      trunc_lt_iff_lt ((birthday_trunc_le o' x).trans_lt h)]
  · rw [trunc_apply_of_le_coe (WithTop.coe_le_coe.2 h), apply_eq_zero,
      length_toSignExpansion, WithTop.coe_le_coe]
    exact (birthday_trunc_le o x).trans h

/-
theorem range_toSignExpansion : range toSignExpansion.{u} = .ofPred SignExpansion.Small := by
  apply subset_antisymm
  · simp [range_subset_iff]
  · intro f hf
    rw [mem_ofPred, small_iff_length_ne_top, WithTop.ne_top_iff_exists] at hf
    obtain ⟨l, hl⟩ := hf
    rw [mem_range]
    induction l using WellFoundedLT.induction generalizing f with | ind l ih
    replace ih (f : SignExpansion) (hl : f.length < l) :=
      ih (f.length.untop (ne_top_of_lt hl))
        ((WithTop.untop_lt_iff _).2 hl) (WithTop.coe_untop _ _)
    choose u hu using ih
    let g : IGame := !{fun p => {s : IGame.{u} | s.birthday < l} ∩
      {s | ∃ _ : s.Numeric, p.cases (toSignExpansion (.mk s) < f) (f < toSignExpansion (.mk s))}}
    have hgn : g.Numeric := by
      rw [numeric_def]
      refine ⟨fun y hy z hz => ?_, fun p y hy => ?_⟩
      · rw [moves_ofSets] at hy hz
        exact (@mk_lt_mk y z hy.2.1 hz.2.1).mp (toSignExpansion.lt_iff_lt.1 (hy.2.2.trans hz.2.2))
      · rw [moves_ofSets] at hy
        exact hy.2.1
    have hgo : g.birthday ≤ l := by
      rw [birthday_le_iff]
      intro p m hm
      rw [moves_ofSets, mem_inter_iff, mem_ofPred] at hm
      exact hm.left
    refine ⟨Surreal.mk g, ?_⟩
    ext o
    induction o using WellFoundedLT.induction with | ind o ih
    obtain ⟨k, nk, hkg, hkb⟩ := birthday_eq_iGameBirthday ((Surreal.mk g).trunc o)
    cases hfo : f o with
    | zero =>
      rw [toSignExpansion_eq_zero_iff, trunc_eq_self]
      apply ((birthday_mk_le g).trans hgo).trans
      rw [← WithTop.coe_le_coe, hl, ← apply_eq_zero, hfo]
    | neg_one =>
      rw [toSignExpansion_eq_neg_one_iff, ← hkg, mk_lt_mk]
      apply Numeric.lt_right
      rw [moves_ofSets, mem_inter_iff, mem_ofPred, mem_ofPred]
      refine ⟨(hkb.trans_le (birthday_trunc_le o (Surreal.mk g))).trans_lt ?_, nk, ?_⟩
      · rw [← WithTop.coe_lt_coe, hl, ← not_le, ← apply_eq_zero, hfo]
        decide
      · rw [hkg]
        refine ⟨o, fun j hj => ?_, ?_⟩
        · simp [← ih j hj, trunc_apply_of_coe_lt (WithTop.coe_lt_coe.2 hj)]
        · simp [hfo, trunc_apply_of_le_coe le_rfl]
    | one =>
      rw [toSignExpansion_eq_one_iff, ← hkg, mk_lt_mk]
      apply Numeric.left_lt
      rw [moves_ofSets, mem_inter_iff, mem_ofPred, mem_ofPred]
      refine ⟨(hkb.trans_le (birthday_trunc_le o (Surreal.mk g))).trans_lt ?_, nk, ?_⟩
      · rw [← WithTop.coe_lt_coe, hl, ← not_le, ← apply_eq_zero, hfo]
        decide
      · rw [hkg]
        refine ⟨o, fun j hj => ?_, ?_⟩
        · simp [← ih j hj, trunc_apply_of_coe_lt (WithTop.coe_lt_coe.2 hj)]
        · simp [hfo, trunc_apply_of_le_coe le_rfl]

theorem mem_range_toSignExpansion (x : SignExpansion) [x.Small] :
    x ∈ range toSignExpansion := by
  rwa [range_toSignExpansion]

theorem toSignExpansion_eq_of_birthday_le_of_forall_lt_gt_iff
    {x : Surreal} {y : SignExpansion} (hy : y.length ≤ x.birthday)
    (hlt : ∀ z : Surreal, z.birthday < x.birthday → (toSignExpansion z < y ↔ z < x))
    (hgt : ∀ z : Surreal, z.birthday < x.birthday → (y < toSignExpansion z ↔ x < z)) :
    toSignExpansion x = y := by
  apply eq_of_length_le_of_forall_lt_gt_iff
  · simpa
  all_goals
  · intro z hz
    have := small_iff_length_lt_top.2 hz.lt_top
    obtain ⟨z, rfl⟩ := mem_range_toSignExpansion z
    rw [OrderEmbedding.lt_iff_lt]
    first | apply hlt | apply hgt
    simpa using hz

/-- The `toSignExpansion` function is determined uniquely by the birthday relation, and by being
correctly ordered with respect to simpler values. -/
theorem toSignExpansion_eq_of_birthday_eq_of_forall_lt_gt
    {x : Surreal} {y : SignExpansion} (hy : x.birthday = y.length)
    (hlt : ∀ z : Surreal, z.birthday < x.birthday → z < x → toSignExpansion z < y)
    (hgt : ∀ z : Surreal, z.birthday < x.birthday → x < z → y < toSignExpansion z) :
    toSignExpansion x = y := by
  apply eq_of_length_eq_of_forall_lt_gt
  · simpa
  all_goals
  · intro z hz
    have := small_iff_length_lt_top.2 hz.lt_top
    obtain ⟨z, rfl⟩ := mem_range_toSignExpansion z
    rw [OrderEmbedding.lt_iff_lt]
    first | apply hlt | apply hgt
    simpa using hz
-/

end Surreal

namespace SignExpansion

/-! ### Sign sequences to games -/

private theorem preimage_singleton_sign_subset {x : SignExpansion} [x.Small] {p : Player} :
    x ⁻¹' {p.sign} ⊆ Iio (Small.length x) := by
  intro y hy
  rw [mem_Iio, WithTop.lt_untop_iff, ← apply_ne_zero]
  exact hy.trans_ne p.sign_ne_zero

local instance (x : SignExpansion.{u}) [x.Small] (p : Player) : Small.{u} (x ⁻¹' {p.sign}) :=
  small_subset preimage_singleton_sign_subset

/-- The "canonical" game associated to a sign expansion, whose options are all the truncates on
positions with signs -1 or +1, depending on the player. -/
def toIGame (x : SignExpansion.{u}) [x.Small] : IGame.{u} :=
  !{fun p ↦ range fun a : x ⁻¹' {p.sign} ↦ toIGame (x ↾ a)}
termination_by wellFounded_lt.wrap x.length
decreasing_by all_goals simpa using preimage_singleton_sign_subset a.2

theorem toIGame_def (x : SignExpansion.{u}) [x.Small] :
    toIGame x = !{fun p ↦ range fun a : x ⁻¹' {p.sign} ↦ toIGame (x ↾ a)} := by
  rw [toIGame]

theorem moves_toIGame (x : SignExpansion) [x.Small] (p : Player) :
    x.toIGame.moves p = {z | ∃ o : NatOrdinal, toIGame (x ↾ o) = z ∧ x o = p.sign} := by
  rw [toIGame_def, moves_ofSets]
  aesop

theorem toIGame_trunc_mem_moves_toIGame {x : SignExpansion} [x.Small] {p : Player} {o : NatOrdinal}
    (hx : x o = p.sign) : toIGame (x ↾ o) ∈ x.toIGame.moves p := by
  rw [moves_toIGame]
  exact ⟨o, rfl, hx⟩

theorem eq_toIGame_trunc_of_mem_moves_toIGame {x : SignExpansion} [x.Small] {y : IGame} {p : Player}
    (hy : y ∈ x.toIGame.moves p) : ∃ o : NatOrdinal, o < x.length ∧ y = toIGame (x ↾ o) := by
  rw [moves_toIGame] at hy
  obtain ⟨o, rfl, ho⟩ := hy
  refine ⟨o, ?_, rfl⟩
  rw [← apply_ne_zero, ho]
  exact p.sign_ne_zero

@[simp]
theorem forall_moves_toIGame {x : SignExpansion} [x.Small] {p : Player} {P : IGame → Prop} :
    (∀ y ∈ x.toIGame.moves p, P y) ↔ ∀ o, x o = p.sign → P (x ↾ o).toIGame := by
  rw [moves_toIGame]
  grind

@[simp]
theorem exists_moves_toIGame {x : SignExpansion} [x.Small] {p : Player} {P : IGame → Prop} :
    (∃ y ∈ x.toIGame.moves p, P y) ↔ ∃ o, x o = p.sign ∧ P (x ↾ o).toIGame := by
  rw [moves_toIGame]
  grind

instance numeric_toIGame (x : SignExpansion) [x.Small] : Numeric x.toIGame := by
  refine Numeric.mk (fun y hy z hz ↦ ?_) (fun p y hy ↦ ?_)
  · rw [moves_toIGame] at hy hz
    obtain ⟨a, rfl, ha⟩ := hy
    obtain ⟨b, rfl, hb⟩ := hz
    obtain hab | rfl | hba := lt_trichotomy a b
    · have := apply_ne_zero.1 (hb.trans_ne <| by decide)
      have := numeric_toIGame (x ↾ b)
      have := hab.le
      apply Numeric.left_lt
      rw [moves_toIGame]
      use a
      aesop
    · rw [ha] at hb
      contradiction
    · have := apply_ne_zero.1 (ha.trans_ne <| by decide)
      have := numeric_toIGame (x ↾ a)
      have := hba.le
      apply Numeric.lt_right
      rw [moves_toIGame]
      use b
      aesop
  · obtain ⟨o, ho, rfl⟩ := eq_toIGame_trunc_of_mem_moves_toIGame hy
    exact numeric_toIGame (x ↾ o)
termination_by wellFounded_lt.wrap x.length

private theorem toIGame_strictMono :
    StrictMono fun x : Subtype SignExpansion.Small ↦ have := x.2; toIGame x := by
  intro ⟨x, _⟩ ⟨y, _⟩ h
  rw [Subtype.mk_lt_mk, lt_iff_toLex] at h
  obtain ⟨i, hi, hi'⟩ := h
  dsimp at *
  have hxy : x ↾ i = y ↾ i := by aesop
  obtain ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ := SignType.lt_cases.1 hi'
  · convert ← Numeric.lt_right (toIGame_trunc_mem_moves_toIGame hx)
    rwa [hxy, trunc_eq_self, ← apply_eq_zero]
  · trans toIGame (x ↾ i)
    · exact Numeric.lt_right (toIGame_trunc_mem_moves_toIGame hx)
    · rw! [hxy]
      exact Numeric.left_lt (toIGame_trunc_mem_moves_toIGame hy)
  · convert ← Numeric.left_lt (toIGame_trunc_mem_moves_toIGame hy)
    rwa [← hxy, trunc_eq_self, ← apply_eq_zero]

@[simp]
theorem toIGame_le_toIGame_iff {x y : SignExpansion} [x.Small] [y.Small] :
    toIGame x ≤ toIGame y ↔ x ≤ y :=
  toIGame_strictMono.le_iff_le (a := ⟨x, ‹_›⟩) (b := ⟨y, ‹_›⟩)

@[simp]
theorem toIGame_lt_toIGame_iff {x y : SignExpansion} [x.Small] [y.Small] :
    toIGame x < toIGame y ↔ x < y :=
  toIGame_strictMono.lt_iff_lt (a := ⟨x, ‹_›⟩) (b := ⟨y, ‹_›⟩)

@[simp]
theorem toIGame_equiv_toIGame_iff {x y : SignExpansion} [x.Small] [y.Small] :
    toIGame x ≈ toIGame y ↔ x ≈ y := by
  simp [AntisymmRel]

@[simp]
theorem toIGame_inj {x y : SignExpansion} [x.Small] [y.Small] :
    toIGame x = toIGame y ↔ x = y := by
  apply (toIGame_strictMono.injective.eq_iff (a := ⟨x, ‹_›⟩) (b := ⟨y, ‹_›⟩)).trans
  rw [Subtype.mk_eq_mk]

@[simp]
theorem _root_.NatOrdinal.toIGame_toSignExpansion (o : NatOrdinal) :
    o.toSignExpansion.toIGame = o := by
  ext p x
  cases p with
  | right => simp [moves_toIGame]
  | left =>
    simp_rw [NatOrdinal.moves_left_toIGame, mem_image, mem_Iio, moves_toIGame]
    constructor
    · rintro ⟨a, rfl, ha⟩
      have hao : a < o := by aesop
      refine ⟨a, hao, ?_⟩
      rw! [NatOrdinal.trunc_toSignExpansion, min_eq_right hao.le, toIGame_toSignExpansion]
      rfl
    · rintro ⟨a, hao, rfl⟩
      refine ⟨a, ?_, ?_⟩
      · rw! [NatOrdinal.trunc_toSignExpansion, min_eq_right hao.le, toIGame_toSignExpansion]
        rfl
      · aesop
termination_by o

/-! ### Sign sequences to surreals -/

/-- The "canonical" surreal associated to a sign expansion, defined in terms of
`SignExpansion.toIGame`. -/
def toSurreal (x : SignExpansion) [x.Small] : Surreal := .mk x.toIGame

@[simp]
theorem mk_toIGame (x : SignExpansion) [x.Small] : .mk x.toIGame = x.toSurreal :=
  (rfl)

@[simp]
theorem toSurreal_le_toSurreal_iff {x y : SignExpansion} [x.Small] [y.Small] :
    toSurreal x ≤ toSurreal y ↔ x ≤ y :=
  toIGame_le_toIGame_iff

@[simp]
theorem toSurreal_lt_toSurreal_iff {x y : SignExpansion} [x.Small] [y.Small] :
    toSurreal x < toSurreal y ↔ x < y :=
  toIGame_lt_toIGame_iff

@[simp]
theorem toSurreal_inj {x y : SignExpansion} [x.Small] [y.Small] :
    toSurreal x = toSurreal y ↔ x = y := by
  simp [le_antisymm_iff]

theorem toSurreal_def (x : SignExpansion.{u}) [x.Small] :
    toSurreal x = !{fun p ↦ range fun a : x ⁻¹' {p.sign} ↦ toSurreal (x ↾ a)}'(by
      simp_rw [forall_mem_range]
      intro ⟨a, ha⟩ ⟨b, hb⟩
      rw [toSurreal_lt_toSurreal_iff]
      trans x <;> simpa) := by
  rw! [toSurreal, toIGame_def, Surreal.mk_ofSets']
  congr!
  aesop

@[simp]
theorem toSurreal_trunc (x : SignExpansion) [x.Small] (o : NatOrdinal) :
    (x ↾ o).toSurreal = x.toSurreal.trunc o := by
  rw [eq_comm]
  apply trunc_eq_of_birthday_le_of_forall_le_ge_iff
  sorry

#exit
@[simp]
theorem toSignExpansion_toSurreal (x : SignExpansion) [x.Small] :
    x.toSurreal.toSignExpansion = x := by
  ext i
  rw [toSignExpansion_apply, ]
  sorry

end SignExpansion
end
