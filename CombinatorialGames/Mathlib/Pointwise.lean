import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Logic.Small.Set

universe u

variable {α β : Type*}

open Pointwise

instance [Zero α] : Small.{u} (0 : Set α) :=
  small_single _

instance [One α] : Small.{u} (1 : Set α) :=
  small_single _

instance [InvolutiveNeg α] (s : Set α) [Small.{u} s] : Small.{u} (-s :) := by
  rw [← Set.image_neg_eq_neg]
  infer_instance

instance (s t : Set α) [Add α] [Small.{u} s] [Small.{u} t] : Small.{u} (s + t :) := by
  rw [← Set.image2_add]
  infer_instance

instance (s t : Set α) [Sub α] [Small.{u} s] [Small.{u} t] : Small.{u} (s - t :) := by
  rw [← Set.image2_sub]
  infer_instance

instance (s t : Set α) [Mul α] [Small.{u} s] [Small.{u} t] : Small.{u} (s * t :) := by
  rw [← Set.image2_mul]
  infer_instance

instance (s t : Set α) [Div α] [Small.{u} s] [Small.{u} t] : Small.{u} (s / t :) := by
  rw [← Set.image2_div]
  infer_instance
