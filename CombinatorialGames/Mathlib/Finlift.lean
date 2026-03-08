/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
module

public import Mathlib.Data.Fintype.Quotient

-- https://github.com/leanprover-community/mathlib4/pull/27302/files

public section

namespace Quotient

variable {ι₁ : Type*} [Fintype ι₁] [DecidableEq ι₁] {ι₂ : Type*} [Fintype ι₂] [DecidableEq ι₂]
  {α : ι₁ → Sort*} {S₁ : ∀ i, Setoid (α i)} {β : ι₂ → Sort*} {S₂ : ∀ i, Setoid (β i)} {φ : Sort*}
  (q₁ : ∀ i, Quotient (S₁ i)) (q₂ : ∀ i, Quotient (S₂ i)) (f : (∀ i, α i) → (∀ i, β i) → φ)
  (c : ∀ (a₁ : ∀ i, α i) (b₁ : ∀ i, β i) (a₂ : ∀ i, α i) (b₂ : ∀ i, β i),
    (∀ i, a₁ i ≈ a₂ i) → (∀ i, b₁ i ≈ b₂ i) → f a₁ b₁ = f a₂ b₂)

/-- Lift a binary function from its finitely indexed types `∀ i : ι₁, α i`, `∀ i : ι₂, β i` to
a binary function on quotients. This is analogous to the combination of `Quotient.finLiftOn`
and `Quotient.liftOn₂`. -/
def finLiftOn₂ : φ := Quotient.liftOn₂ (finChoice q₁) (finChoice q₂) f c

@[simp]
lemma finLiftOn₂_mk (a : ∀ i, α i) (b : ∀ i, β i) : finLiftOn₂ (⟦a ·⟧) (⟦b ·⟧) f c = f a b := by
  simp_rw [finLiftOn₂, finChoice_eq, lift_mk]

end Quotient
end
