/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Surreal.Birthday.Basic
public import CombinatorialGames.Surreal.Real
public import Mathlib.Algebra.Ring.Subring.Defs

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Ring.Subring.Order
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Omnific integers

We define the omnific integers, as the subring of surreals such that `x = {x - 1 | x + 1}`.

## Todo

Prove the characterization of omnific integers, as surreals whose Hahn series `x` have the
following form:

- `x.support ⊆ Ici 0`
- `x.coeff 0` is an integer
-/

public noncomputable section

namespace Surreal
open IGame Set

attribute [local simp] add_assoc sub_lt_iff_lt_add

/-! ### Rounding operation -/

/-- We define `x.round r = {x - r | x + r}` whenever `0 < r`. For `r ≤ 0`, we set the junk value
`x.round r = x`.

If `r = 1`, this operation truncates the fractional part of `x`, rounding up or down to whichever
omnific integer is simplest. -/
def round (x r : Surreal) : Surreal :=
  if hr : 0 < r then !{{x - r} | {x + r}} else x

theorem round_of_pos {x r : Surreal} (hr : 0 < r) : x.round r = !{{x - r} | {x + r}} :=
  dite_eq_left hr

theorem round_of_nonpos {x r : Surreal} (hr : r ≤ 0) : x.round r = x :=
  dite_eq_right hr.not_gt

theorem round_mk_of_pos {x r : IGame} (hr : 0 < r) [x.Numeric] [r.Numeric] :
    (mk x).round (mk r) = @mk !{{x - r} | {x + r}}
      (.mk (by simpa [← Surreal.mk_lt_mk]) (by simp [Numeric.add, Numeric.sub])) := by
  rw [round_of_pos hr, mk_ofSets]
  congr <;> aesop

theorem round_mem_Ioo {x r : Surreal} (hr : 0 < r) : round x r ∈ Ioo (x - r) (x + r) := by
  rw [round_of_pos hr]
  exact ⟨lt_ofSets_of_mem_left (mem_singleton _), ofSets_lt_of_mem_right (mem_singleton _)⟩

theorem sub_lt_round {x r : Surreal} (hr : 0 < r) : x - r < round x r := (round_mem_Ioo hr).1
theorem round_lt_add {x r : Surreal} (hr : 0 < r) : round x r < x + r := (round_mem_Ioo hr).2

theorem birthday_round_le {x y r : Surreal} (h : y ∈ Ioo (x - r) (x + r)) :
    (x.round r).birthday ≤ y.birthday := by
  have hr : 0 < r := by simpa using nonempty_Ioo.1 ⟨y, h⟩
  cases h
  rw [round_of_pos hr]
  apply birthday_ofSets_le_of_btwn <;> simp_all

theorem birthday_round_lt {x y r : Surreal} (h : y ∈ Ioo (x - r) (x + r)) (hy : x.round r ≠ y) :
    (x.round r).birthday < y.birthday := by
  have hr : 0 < r := by simpa using nonempty_Ioo.1 ⟨y, h⟩
  cases h
  rw [round_of_pos hr] at hy ⊢
  apply birthday_ofSets_lt_of_btwn <;> simp_all

theorem round_eq_of_forall_birthday_le {x y r : Surreal}
    (h : y ∈ Ioo (x - r) (x + r)) (hz : ∀ z, z ∈ Ioo (x - r) (x + r) → y.birthday ≤ z.birthday) :
    x.round r = y := by
  have hr : 0 < r := by simpa using nonempty_Ioo.1 ⟨y, h⟩
  cases h
  rw [round_of_pos hr, ofSets_eq_of_forall_birthday_le]
  · simp_all
  · simpa
  · simpa using hz

theorem round_of_zero_mem {x r : Surreal} (h : 0 ∈ Ioo (x - r) (x + r)) : x.round r = 0 := by
  simpa using birthday_round_le h

@[simp]
theorem round_zero (r : Surreal) : round 0 r = 0 := by
  obtain h | h := le_or_gt r 0
  · rw [round_of_nonpos h]
  · apply round_of_zero_mem
    simpa

@[simp]
theorem round_neg {x r : Surreal} : (-x).round r = -x.round r := by
  obtain h | h := le_or_gt r 0
  · simp_rw [round_of_nonpos h]
  cases x with | mk x
  cases r with | mk r
  simp only [← mk_neg, round_mk_of_pos h, neg_ofSets, neg_singleton,
    sub_eq_add_neg, neg_add, neg_neg]

theorem round_add_of_eq {x y r : Surreal} (hx : x.round r = x) (hy : y.round r = y) :
    (x + y).round r = x + y := by
  obtain h | h := le_or_gt r 0
  · rw [round_of_nonpos h]
  cases x with | mk x
  cases y with | mk y
  cases r with | mk r
  conv_rhs => rw [← hx, ← hy]
  simp only [← mk_add, round_mk_of_pos h] at *
  generalize_proofs at hx hy
  simp only [ofSets_add_ofSets, mk_ofSets, image_singleton, union_singleton,
    range_singleton, range_insert]
  dsimp
  congr <;> rw [hx, hy] <;> grind

theorem round_sub_of_eq {x y r : Surreal} (hx : x.round r = x) (hy : y.round r = y) :
    (x - y).round r = x - y := by
  rw [sub_eq_add_neg, round_add_of_eq hx]
  rw [round_neg, hy]

theorem round_mul_of_eq {x y r : Surreal} (h : 0 < r) (hx : x.round r = x) (hy : y.round r = y) :
    (x * y).round (r * r) = x * y := by
  have h' : 0 < r * r := mul_self_pos.2 h.ne'
  cases x with | mk x
  cases y with | mk y
  cases r with | mk r
  conv_rhs => rw [← hx, ← hy]
  simp only [← mk_mul, round_mk_of_pos h, round_mk_of_pos h'] at *
  generalize_proofs at hx hy
  simp only [ofSets_mul_ofSets, mk_ofSets, mulOption, singleton_prod_singleton,
    union_singleton, image_insert_eq, image_singleton, range_singleton, range_insert]
  congr <;> dsimp <;> rw [hx, hy] <;> grind

/-! ### Omnific integers -/

/-- An omnific integer is one such that `x = {x - 1 | x + 1}`. These are an analog of the integers
to the surreals. -/
@[expose]
def IsOmnific (x : Surreal) : Prop :=
  x.round 1 = x

theorem IsOmnific.eq {x : Surreal} (h : IsOmnific x) : x.round 1 = x := h

@[simp] theorem IsOmnific.zero : IsOmnific 0 := by simp [IsOmnific]

@[simp]
theorem IsOmnific.one : IsOmnific 1 := by
  rw [IsOmnific, ← mk_one, round_mk_of_pos IGame.zero_lt_one, mk_eq_mk']
  apply equiv_one_of_fits
  on_goal 2 => rw [← fits_zero_iff_equiv]
  all_goals simp [Fits, ← Game.mk_lt_mk]

theorem IsOmnific.neg {x : Surreal} (hx : IsOmnific x) : IsOmnific (-x) := by
  simpa [IsOmnific]

@[simp]
theorem isOmnific_neg_iff {x : Surreal} : IsOmnific (-x) ↔ IsOmnific x :=
  ⟨fun h ↦ neg_neg x ▸ h.neg, .neg⟩

theorem IsOmnific.add {x y : Surreal}
    (hx : IsOmnific x) (hy : IsOmnific y) : IsOmnific (x + y) :=
  round_add_of_eq hx hy

theorem IsOmnific.sub {x y : Surreal}
    (hx : IsOmnific x) (hy : IsOmnific y) : IsOmnific (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem IsOmnific.mul {x y : Surreal}
    (hx : IsOmnific x) (hy : IsOmnific y) : IsOmnific (x * y) := by
  simpa [IsOmnific] using round_mul_of_eq zero_lt_one hx hy

theorem IsOmnific.one_le_iff_pos {x : Surreal} (h : IsOmnific x) : 1 ≤ x ↔ 0 < x where
  mp := zero_lt_one.trans_le
  mpr hx := by
    by_contra!
    rw [IsOmnific, round_of_zero_mem] at h
    · exact hx.ne h
    · grind

theorem IsOmnific.lt_one_iff_nonpos {x : Surreal} (h : IsOmnific x) : x < 1 ↔ x ≤ 0 := by
  rw [← not_iff_not]
  simpa using h.one_le_iff_pos

theorem IsOmnific.birthday_le_of_mem_Ioo {x y : Surreal} (h : IsOmnific x)
    (hy : y ∈ Ioo (x - 1) (x + 1)) : x.birthday ≤ y.birthday :=
  h ▸ birthday_round_le hy

theorem IsOmnific.natOrdinal (x : NatOrdinal) : IsOmnific x := by
  refine round_eq_of_forall_birthday_le (by simp) fun z ⟨hz, ?_⟩ ↦ ?_
  grw [sub_lt_iff_lt_add, le_toSurreal_birthday z] at hz
  rwa [← NatOrdinal.toSurreal_one, ← NatOrdinal.toSurreal_add, NatOrdinal.toSurreal.lt_iff_lt,
    Order.lt_add_one_iff, ← birthday_toSurreal x] at hz

/-- The subring of `IsOmnific` surreal numbers. -/
private def omnificSubring : Subring Surreal where
  carrier := {x | IsOmnific x}
  zero_mem' := .zero
  one_mem' := .one
  neg_mem' := .neg
  add_mem' := .add
  mul_mem' := .mul

/-- The ring of `IsOmnific` surreal numbers. -/
def Omnific : Type _ := omnificSubring
deriving CommRing, LinearOrder, IsStrictOrderedRing

@[coe] def Omnific.coe (x : Omnific) : Surreal := x.1
instance : Coe Omnific Surreal := ⟨Omnific.coe⟩

theorem Omnific.prop (x : Omnific) : IsOmnific x := x.2

/-- Construct an omnific integer from a surreal. -/
def Omnific.mk (x : Surreal) (hx : IsOmnific x) : Omnific := ⟨x, hx⟩

@[simp, norm_cast] theorem Omnific.coe_mk (x hx) : Omnific.mk x hx = x := (rfl)

@[simp, norm_cast] theorem Omnific.coe_zero : ((0 : Omnific) : Surreal) = 0 := (rfl)
@[simp, norm_cast] theorem Omnific.coe_one : ((1 : Omnific) : Surreal) = 1 := (rfl)
@[simp, norm_cast] theorem Omnific.coe_natCast (n : ℕ) : ((n : Omnific) : Surreal) = n := (rfl)
@[simp, norm_cast] theorem Omnific.coe_intCast (n : ℤ) : ((n : Omnific) : Surreal) = n := (rfl)
@[simp, norm_cast] theorem Omnific.coe_neg (x : Omnific) : ((-x : Omnific) : Surreal) = -x := (rfl)

@[simp, norm_cast] theorem Omnific.coe_add (x y : Omnific) :
    ((x + y : Omnific) : Surreal) = x + y := (rfl)
@[simp, norm_cast] theorem Omnific.coe_sub (x y : Omnific) :
    ((x - y : Omnific) : Surreal) = x - y := (rfl)
@[simp, norm_cast] theorem Omnific.coe_mul (x y : Omnific) :
    ((x * y : Omnific) : Surreal) = x * y := (rfl)

theorem Omnific.coe_add_one (x : Omnific) : ((x + 1 : Omnific) : Surreal) = x + 1 := (rfl)

@[simp, norm_cast, gcongr] theorem Omnific.coe_le_coe {x y : Omnific} :
    (x : Surreal) ≤ y ↔ x ≤ y := .rfl
@[simp, norm_cast, gcongr] theorem Omnific.coe_lt_coe {x y : Omnific} :
    (x : Surreal) < y ↔ x < y := .rfl
@[simp, norm_cast, gcongr] theorem Omnific.coe_inj {x y : Omnific} :
    (x : Surreal) = y ↔ x = y := Subtype.coe_inj

@[ext] theorem Omnific.ext {x y : Omnific} (h : x.coe = y.coe) : x = y := Subtype.ext h

/-- Cast an ordinal to an omnific integer. -/
@[expose, simps!]
def _root_.NatOrdinal.toOmnific : NatOrdinal →+*o Omnific where
  toFun x := Omnific.mk x (IsOmnific.natOrdinal x)
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp
  monotone' _ := by simp [← Omnific.coe_le_coe]

@[simp] theorem IsOmnific.natCast (n : ℕ) : IsOmnific n := (n : Omnific).prop
@[simp] theorem IsOmnific.intCast (n : ℤ) : IsOmnific n := (n : Omnific).prop

theorem isOmnific_add_iff_left {x y : Surreal} (hy : IsOmnific y) :
    IsOmnific (x + y) ↔ IsOmnific x where
  mp h := by simpa using h.sub hy
  mpr h := h.add hy

theorem isOmnific_add_iff_right {x y : Surreal} (hx : IsOmnific x) :
    IsOmnific (x + y) ↔ IsOmnific y := by
  rw [add_comm, isOmnific_add_iff_left hx]

theorem isOmnific_sub_iff_left {x y : Surreal} (hy : IsOmnific y) :
    IsOmnific (x - y) ↔ IsOmnific x := by
  rw [sub_eq_add_neg, isOmnific_add_iff_left hy.neg]

theorem isOmnific_sub_iff_right {x y : Surreal} (hx : IsOmnific x) :
    IsOmnific (x - y) ↔ IsOmnific y := by
  rw [sub_eq_add_neg, isOmnific_add_iff_right hx, isOmnific_neg_iff]

@[simp]
theorem isOmnific_realCast_iff {r : ℝ} : IsOmnific r ↔ r ∈ range ((↑) : ℤ → ℝ) where
  mpr := by rintro ⟨n, rfl⟩; simp
  mp h := by
    rw [← Int.fract_eq_zero_iff]
    apply (Int.fract_nonneg r).antisymm'
    rw [← Real.toSurreal_le_iff, Real.toSurreal_zero, ← IsOmnific.lt_one_iff_nonpos]
    · exact_mod_cast Int.fract_lt_one r
    · rw [Int.fract, Real.toSurreal_sub]
      apply h.sub
      simp

@[simp]
theorem isOmnific_ratCast_iff {q : ℚ} : IsOmnific q ↔ q ∈ range ((↑) : ℤ → ℚ) := by
  rw [← Real.toSurreal_ratCast, isOmnific_realCast_iff]
  refine exists_congr fun _ ↦ ?_
  norm_cast

@[no_expose]
instance : SuccOrder Omnific :=
  .ofCore (fun x ↦ x + 1) (by
    refine @fun x _ y ↦ ⟨fun h ↦ ?_, (lt_add_one x).trans_le⟩
    rwa [← le_sub_iff_add_le', ← Omnific.coe_le_coe, Omnific.coe_one,
      (Omnific.prop _).one_le_iff_pos, Omnific.coe_sub, lt_sub_iff_add_lt, zero_add]
  ) (by simp)

instance : SuccAddOrder Omnific where
  succ_eq_add_one x := by rfl

@[no_expose]
instance : PredOrder Omnific :=
  .ofCore (fun x ↦ x - 1) (by
    refine @fun x _ y ↦ ⟨fun h ↦ ?_, (sub_one_lt x).trans_le'⟩
    rwa [le_sub_comm, ← Omnific.coe_le_coe, Omnific.coe_one,
      (Omnific.prop _).one_le_iff_pos, Omnific.coe_sub, lt_sub_iff_add_lt, zero_add]
  ) (by simp)

instance : PredSubOrder Omnific where
  pred_eq_sub_one x := by rfl

end Surreal
end
