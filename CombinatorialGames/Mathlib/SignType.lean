/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Basic.Sign.Defs

/-!
#45724
-/

public section

namespace SignType

/-- The function `cmp x 0`, as an `Equiv`. -/
@[expose]
def orderingEquiv : SignType ≃ Ordering where
  toFun
  | zero => .eq
  | neg => .lt
  | pos => .gt
  invFun
  | .eq => zero
  | .lt => neg
  | .gt => pos
  left_inv := by decide
  right_inv := by decide

@[simp] theorem orderingEquiv_zero : orderingEquiv 0 = .eq := rfl
@[simp] theorem orderingEquiv_one : orderingEquiv 1 = .gt := rfl
@[simp] theorem orderingEquiv_neg_one : orderingEquiv (-1) = .lt := rfl

@[simp] theorem orderingEquiv_symm_eq : orderingEquiv.symm .eq = 0 := rfl
@[simp] theorem orderingEquiv_symm_gt : orderingEquiv.symm .gt = 1 := rfl
@[simp] theorem orderingEquiv_symm_lt : orderingEquiv.symm .lt = -1 := rfl

@[simp] theorem orderingEquiv_eq_eq_iff {x : SignType} : orderingEquiv x = .eq ↔ x = 0 := by
  rw [← orderingEquiv_zero, Equiv.apply_eq_iff_eq]
@[simp] theorem orderingEquiv_eq_gt_iff {x : SignType} : orderingEquiv x = .gt ↔ x = 1 := by
  rw [← orderingEquiv_one, Equiv.apply_eq_iff_eq]
@[simp] theorem orderingEquiv_eq_lt_iff {x : SignType} : orderingEquiv x = .lt ↔ x = -1 := by
  rw [← orderingEquiv_neg_one, Equiv.apply_eq_iff_eq]

@[simp]
theorem orderingEquiv_symm_eq_zero_iff {x : Ordering} : orderingEquiv.symm x = 0 ↔ x = .eq := by
  rw [← orderingEquiv_symm_eq, Equiv.apply_eq_iff_eq]
@[simp]
theorem orderingEquiv_symm_eq_one_iff {x : Ordering} : orderingEquiv.symm x = 1 ↔ x = .gt := by
  rw [← orderingEquiv_symm_gt, Equiv.apply_eq_iff_eq]
@[simp]
theorem orderingEquiv_symm_eq_neg_one_iff {x : Ordering} : orderingEquiv.symm x = -1 ↔ x = .lt := by
  rw [← orderingEquiv_symm_lt, Equiv.apply_eq_iff_eq]

@[simp]
theorem orderingEquiv_neg (x : SignType) : orderingEquiv (-x) = (orderingEquiv x).swap := by
  cases x <;> rfl

@[simp]
theorem orderingEquiv_symm_swap (x : Ordering) :
    orderingEquiv.symm x.swap = -orderingEquiv.symm x := by
  cases x <;> rfl

@[simp]
theorem cmp_zero (x : SignType) : cmp x 0 = x.orderingEquiv := by
  cases x <;> rfl

@[simp]
theorem zero_cmp (x : SignType) : cmp 0 x = x.orderingEquiv.swap := by
  cases x <;> rfl

section LinearOrder
variable {α : Type*} [AddGroup α] [LinearOrder α] [AddRightStrictMono α]

@[simp]
theorem orderingEquiv_sign_sub (x y : α) :
    orderingEquiv (sign (x - y)) = cmp x y := by
  obtain h | rfl | h := lt_trichotomy x y
  · rw [h.cmp_eq_lt, sign_eq_neg_one_iff.2, orderingEquiv_neg_one]
    rwa [sub_neg]
  · simp
  · rw [h.cmp_eq_gt, sign_eq_one_iff.2, orderingEquiv_one]
    rwa [sub_pos]

theorem orderingEquiv_symm_cmp (x y : α) :
    orderingEquiv.symm (cmp x y) = sign (x - y) := by
  rw [Equiv.symm_apply_eq, orderingEquiv_sign_sub]

end LinearOrder
end SignType
end
