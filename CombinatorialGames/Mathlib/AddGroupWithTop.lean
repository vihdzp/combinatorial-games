import Mathlib.Algebra.Order.AddGroupWithTop

-- #32804

namespace LinearOrderedAddCommGroupWithTop
variable {α : Type*} [LinearOrderedAddCommGroupWithTop α]

@[simp]
theorem sub_top (a : α) : a - ⊤ = ⊤ := by
  rw [sub_eq_add_neg, LinearOrderedAddCommGroupWithTop.neg_top, add_top]

@[simp]
theorem sub_self_eq_zero_iff_ne_top {a : α} : a - a = 0 ↔ a ≠ ⊤ where
  mp := by
    contrapose!
    simp +contextual
  mpr := by
    rw [sub_eq_add_neg]
    exact add_neg_cancel_of_ne_top

alias ⟨_, sub_self_eq_zero_of_ne_top⟩ := sub_self_eq_zero_iff_ne_top

end LinearOrderedAddCommGroupWithTop
