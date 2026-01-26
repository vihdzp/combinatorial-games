/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Multiplication
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
theorem range_singleton (x : α) (f : ({x} : Set α) → β) : range f = {f ⟨x, mem_singleton x⟩} := by
  aesop

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

/-! ### Expand operation -/

/-- We define `x.expand r = {x - r | x + r}` whenever `0 < r`. For `r ≤ 0`, we set the junk value
`x.expand r = x`. -/
def expand (x r : Surreal) : Surreal :=
  if h : 0 < r then !{{x - r} | {x + r}} else x

theorem expand_of_pos {x r : Surreal} (h : 0 < r) : x.expand r = !{{x - r} | {x + r}} :=
  dif_pos h

theorem expand_of_nonpos {x r : Surreal} (h : r ≤ 0) : x.expand r = x :=
  dif_neg h.not_gt

theorem expand_mk_of_pos {x r : IGame} (h : 0 < r) [x.Numeric] [r.Numeric] :
    (mk x).expand (mk r) = @mk !{{x - r} | {x + r}}
      (.mk (by simpa [← Surreal.mk_lt_mk]) (by aesop)) := by
  rw [expand_of_pos h, mk_ofSets]
  congr <;> aesop

@[simp]
theorem expand_zero (r : Surreal) : expand 0 r = 0 := by
  obtain h | h := le_or_gt r 0
  · rw [expand_of_nonpos h]
  cases r with | mk r
  rw [← mk_zero, expand_mk_of_pos h, mk_eq_mk', ← IGame.fits_zero_iff_equiv]
  simpa [IGame.Fits]

@[simp]
theorem expand_neg {x r : Surreal} : (-x).expand r = -x.expand r := by
  obtain h | h := le_or_gt r 0
  · simp_rw [expand_of_nonpos h]
  cases x with | mk x
  cases r with | mk r
  simp only [← mk_neg, expand_mk_of_pos h, IGame.neg_ofSets, Set.neg_singleton,
    sub_eq_add_neg, neg_add, neg_neg]

theorem expand_add_of_eq {x y r : Surreal} (hx : x.expand r = x) (hy : y.expand r = y) :
    (x + y).expand r = x + y := by
  obtain h | h := le_or_gt r 0
  · rw [expand_of_nonpos h]
  cases x with | mk x
  cases y with | mk y
  cases r with | mk r
  conv_rhs => rw [← hx, ← hy]
  simp only [← mk_add, expand_mk_of_pos h] at *
  generalize_proofs at hx hy
  simp only [IGame.ofSets_add_ofSets, mk_ofSets, Set.image_singleton, Set.union_singleton,
    Set.range_singleton, Set.range_insert]
  dsimp
  congr <;> rw [hx, hy] <;> grind

theorem expand_mul_of_eq {x y r : Surreal} (h : 0 < r) (hx : x.expand r = x) (hy : y.expand r = y) :
    (x * y).expand (r * r) = x * y := by
  have h' : 0 < r * r := mul_self_pos.2 h.ne'
  cases x with | mk x
  cases y with | mk y
  cases r with | mk r
  conv_rhs => rw [← hx, ← hy]
  simp only [← mk_mul, expand_mk_of_pos h, expand_mk_of_pos h'] at *
  generalize_proofs at hx hy
  simp only [IGame.ofSets_mul_ofSets, mk_ofSets, IGame.mulOption, Set.singleton_prod_singleton,
    Set.union_singleton, Set.image_insert_eq, Set.image_singleton,
    Set.range_singleton, Set.range_insert]
  congr <;> dsimp <;> rw [hx, hy] <;> grind

/-! ### Omnific integers -/

/-- An omnific integer is one such that `x = {x - 1 | x + 1}`. These are an analog of the integers
to the surreals. -/
def IsOmnific (x : Surreal) : Prop :=
  x.expand 1 = x

theorem IsOmnific.eq {x : Surreal} (h : IsOmnific x) : x.expand 1 = x := h

theorem IsOmnific.zero : IsOmnific 0 := by simp [IsOmnific]

theorem IsOmnific.one : IsOmnific 1 := by
  rw [IsOmnific, ← mk_one, expand_mk_of_pos IGame.zero_lt_one, mk_eq_mk']
  apply IGame.equiv_one_of_fits
  on_goal 2 => rw [← IGame.fits_zero_iff_equiv]
  all_goals simp [IGame.Fits, ← Game.mk_lt_mk]

theorem IsOmnific.add {x y : Surreal}
    (hx : IsOmnific x) (hy : IsOmnific y) : IsOmnific (x + y) :=
  expand_add_of_eq hx hy

theorem IsOmnific.neg {x : Surreal} (hx : IsOmnific x) : IsOmnific (-x) := by
  simpa [IsOmnific]

@[simp]
theorem isOmnific_neg_iff {x : Surreal} : IsOmnific (-x) ↔ IsOmnific x :=
  ⟨fun h ↦ neg_neg x ▸ h.neg, .neg⟩

theorem IsOmnific.mul {x y : Surreal}
    (hx : IsOmnific x) (hy : IsOmnific y) : IsOmnific (x * y) := by
  simpa using expand_mul_of_eq zero_lt_one hx hy

/-- The subring of `IsOmnific` surreal numbers. -/
def Omnific : Subring Surreal where
  carrier := {x | IsOmnific x}
  zero_mem' := .zero
  one_mem' := .one
  neg_mem' := .neg
  add_mem' := .add
  mul_mem' := .mul

theorem IsOmnific.natCast (n : ℕ) : IsOmnific n := (n : Omnific).2
theorem IsOmnific.intCast (n : ℤ) : IsOmnific n := (n : Omnific).2

end Surreal
end
