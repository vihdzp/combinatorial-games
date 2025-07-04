import Mathlib.Order.Antisymmetrization

theorem not_le_of_le_of_not_le {α : Type*} [Preorder α] {a b c : α} (h₁ : a ≤ b) (h₂ : ¬ c ≤ b) :
    ¬ c ≤ a :=
  fun h ↦ h₂ (h.trans h₁)

theorem not_le_of_not_le_of_le {α : Type*} [Preorder α] {a b c : α} (h₁ : ¬ b ≤ a) (h₂ : b ≤ c) :
    ¬ c ≤ a :=
  fun h ↦ h₁ (h₂.trans h)

theorem not_lt_of_antisymmRel {α} [Preorder α] {x y : α} (h : AntisymmRel (· ≤ ·) x y) : ¬ x < y :=
  h.ge.not_gt

theorem not_gt_of_antisymmRel {α} [Preorder α] {x y : α} (h : AntisymmRel (· ≤ ·) x y) : ¬ y < x :=
  h.le.not_gt

alias AntisymmRel.not_lt := not_lt_of_antisymmRel
alias AntisymmRel.not_gt := not_gt_of_antisymmRel

theorem not_antisymmRel_of_lt {α} [Preorder α] {x y : α} : x < y → ¬ AntisymmRel (· ≤ ·) x y :=
  imp_not_comm.1 not_lt_of_antisymmRel

theorem not_antisymmRel_of_gt {α} [Preorder α] {x y : α} : y < x → ¬ AntisymmRel (· ≤ ·) x y :=
  imp_not_comm.1 not_gt_of_antisymmRel

alias LT.lt.not_antisymmRel := not_antisymmRel_of_lt
alias LT.lt.not_antisymmRel_symm := not_antisymmRel_of_gt
