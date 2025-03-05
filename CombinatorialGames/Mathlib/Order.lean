import Mathlib.Order.Basic

theorem not_le_of_le_of_not_le {α : Type*} [Preorder α] {a b c : α} (h₁ : a ≤ b) (h₂ : ¬ c ≤ b) :
    ¬ c ≤ a :=
  fun h ↦ h₂ (h.trans h₁)

theorem not_le_of_not_le_of_le {α : Type*} [Preorder α] {a b c : α} (h₁ : ¬ b ≤ a) (h₂ : b ≤ c) :
    ¬ c ≤ a :=
  fun h ↦ h₁ (h₂.trans h)
