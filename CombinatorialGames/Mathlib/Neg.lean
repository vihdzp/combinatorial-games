import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Logic.Small.Set

universe u

namespace Set

theorem neg_setOf {α : Type*} [InvolutiveNeg α] (p : α → Prop) :
    -{x | p x} = {x | p (-x)} :=
  rfl

theorem image_neg_of_apply_neg_eq {α β : Type*} [InvolutiveNeg α]
    {s : Set α} {f g : α → β} (H : ∀ x ∈ s, f (-x) = g x) : f '' (-s) = g '' s := by
  ext
  rw [mem_image, ← (Equiv.neg _).exists_congr_right]
  aesop

theorem image_neg_of_apply_neg_eq_neg {α β : Type*} [InvolutiveNeg α] [InvolutiveNeg β]
    {s : Set α} {f g : α → β} (H : ∀ x ∈ s, f (-x) = -g x) : f '' (-s) = -g '' s := by
  conv_rhs => rw [← image_neg_eq_neg, image_image, ← image_neg_of_apply_neg_eq H]

instance {α : Type*} [InvolutiveNeg α] (s : Set α) [Small.{u} s] : Small.{u} (-s :) := by
  rw [← Set.image_neg_eq_neg]
  infer_instance

end Set
