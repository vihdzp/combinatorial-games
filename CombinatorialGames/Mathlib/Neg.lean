import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Logic.Small.Set

universe u

namespace Set

theorem image_neg_of_apply_neg_eq {α β : Type*} [InvolutiveNeg α]
    {s : Set α} {f g : α → β} (H : ∀ x ∈ s, f (-x) = g x) : f '' (-s) = g '' s := by
  rw [← Set.image_neg_eq_neg, Set.image_image]; exact Set.image_congr H

theorem image_neg_of_apply_neg_eq_neg {α β : Type*} [InvolutiveNeg α] [InvolutiveNeg β]
    {s : Set α} {f g : α → β} (H : ∀ x ∈ s, f (-x) = -g x) : f '' (-s) = -g '' s := by
  conv_rhs => rw [← image_neg_eq_neg, image_image, ← image_neg_of_apply_neg_eq H]

end Set
