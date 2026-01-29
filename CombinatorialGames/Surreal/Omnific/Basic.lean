/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Birthday.Basic
import CombinatorialGames.Surreal.Real
import Mathlib.Algebra.Ring.Subring.Defs

/-!
# Omnific integers

We define the omnific integers, as the subring of surreals such that `x = {x - 1 | x + 1}`.

## Todo

Prove the characterization of omnific integers, as surreals whose Hahn series `x` have the
following form:

- `x.support ⊆ Ici 0`
- `x.coeff 0` is an integer
-/

noncomputable section

/-! ### For Mathlib -/

namespace Set
variable {α β : Type*}

@[simp]
theorem range_singleton (x : α) (f : ({x} : Set α) → β) : range f = {f ⟨x, mem_singleton x⟩} :=
  range_unique

@[simp]
theorem range_insert (x : α) (s : Set α) (f : ((insert x s) : Set α) → β) :
    range f = insert (f ⟨x, mem_insert x s⟩)
      (range fun y : s ↦ f ⟨y, mem_insert_of_mem _ y.2⟩) := by
  aesop

end Set

section CommGroup
variable {α : Type*} {x y : α} [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

@[to_additive (attr := simp)]
theorem div_lt_mul_self_iff : x / y < x * y ↔ 1 < y := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
theorem div_le_mul_self_iff : x / y ≤ x * y ↔ 1 ≤ y := by
  simp [div_eq_mul_inv]

end CommGroup

namespace Surreal
open IGame Set

/-! ### Rounding operation -/

/-- We define `x.round r = {x - r | x + r}` whenever `0 < r`. For `r ≤ 0`, we set the junk value
`x.round r = x`.

If `r = 1`, this operation truncates the fractional part of `x`, rounding up or down to whichever
omnific integer is simplest. -/
def round (x r : Surreal) : Surreal :=
  if hr : 0 < r then !{{x - r} | {x + r}} else x

theorem round_of_pos {x r : Surreal} (hr : 0 < r) : x.round r = !{{x - r} | {x + r}} :=
  dif_pos hr

theorem round_of_nonpos {x r : Surreal} (hr : r ≤ 0) : x.round r = x :=
  dif_neg hr.not_gt

theorem round_mk_of_pos {x r : IGame} (hr : 0 < r) [x.Numeric] [r.Numeric] :
    (mk x).round (mk r) = @mk !{{x - r} | {x + r}}
      (.mk (by simpa [← Surreal.mk_lt_mk]) (by aesop)) := by
  rw [round_of_pos hr, mk_ofSets]
  congr <;> aesop

theorem birthday_round_le {x y r : Surreal} (h : y ∈ Ioo (x - r) (x + r)) :
    (x.round r).birthday ≤ y.birthday := by
  have hr : 0 < r := by simpa using nonempty_Ioo.1 ⟨y, h⟩
  cases h
  rw [round_of_pos hr]
  apply birthday_ofSets_le_of_mem <;> simpa

theorem round_eq_of_forall_birthday_le {x y r : Surreal}
    (h : y ∈ Ioo (x - r) (x + r)) (hz : ∀ z, z ∈ Ioo (x - r) (x + r) → y.birthday ≤ z.birthday) :
    x.round r = y := by
  have hr : 0 < r := by simpa using nonempty_Ioo.1 ⟨y, h⟩
  cases h
  rw [round_of_pos hr, ofSets_eq_of_forall_birthday_le]
  · simpa
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
    (hx : IsOmnific x) (hy : IsOmnific y) : IsOmnific (x - y) :=
  hx.add hy.neg

theorem IsOmnific.mul {x y : Surreal}
    (hx : IsOmnific x) (hy : IsOmnific y) : IsOmnific (x * y) := by
  simpa using round_mul_of_eq zero_lt_one hx hy

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

/-- The subring of `IsOmnific` surreal numbers. -/
def Omnific : Subring Surreal where
  carrier := {x | IsOmnific x}
  zero_mem' := .zero
  one_mem' := .one
  neg_mem' := .neg
  add_mem' := .add
  mul_mem' := .mul

@[simp] theorem IsOmnific.natCast (n : ℕ) : IsOmnific n := (n : Omnific).2
@[simp] theorem IsOmnific.intCast (n : ℤ) : IsOmnific n := (n : Omnific).2

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

/-- This seemingly innocuous theorem seems to require the result that any surreal is at distance at
most 1 from an omnific integer, which itself seems to require the characterization in the module
docstring. -/
proof_wanted IsOmnific.round (x : Surreal) : (x.round 1).IsOmnific

end Surreal
end
