import Mathlib.Algebra.Group.Pointwise.Set.Basic

universe u

namespace Set

@[simp]
theorem neg_setOf {α : Type*} [InvolutiveNeg α] (p : α → Prop) :
    -{x | p x} = {x | p (-x)} :=
  rfl

theorem image_neg_of_apply_neg_eq {α β : Type*} [InvolutiveNeg α]
    {s : Set α} {f g : α → β} (H : ∀ x ∈ s, f (-x) = g x) : f '' (-s) = g '' s := by
  rw [← Set.image_neg_eq_neg, Set.image_image]; exact Set.image_congr H

theorem image_neg_of_apply_neg_eq_neg {α β : Type*} [InvolutiveNeg α] [InvolutiveNeg β]
    {s : Set α} {f g : α → β} (H : ∀ x ∈ s, f (-x) = -g x) : f '' (-s) = -g '' s := by
  conv_rhs => rw [← image_neg_eq_neg, image_image, ← image_neg_of_apply_neg_eq H]

@[simp]
theorem forall_mem_neg {α : Type*} [InvolutiveNeg α] {p : α → Prop} {s : Set α} :
    (∀ x, -x ∈ s → p x) ↔ ∀ x ∈ s, p (-x) := by
  rw [← (Equiv.neg _).forall_congr_right]
  simp

@[simp]
theorem exists_mem_neg {α : Type*} [InvolutiveNeg α] {p : α → Prop} {s : Set α} :
    (∃ x, -x ∈ s ∧ p x) ↔ ∃ x ∈ s, p (-x) := by
  rw [← (Equiv.neg _).exists_congr_right]
  simp

end Set
