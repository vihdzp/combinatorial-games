import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Antisymmetrization

/-! ### Basic order theorems -/

theorem not_le_of_le_of_not_le {α : Type*} [Preorder α] {a b c : α} (h₁ : a ≤ b) (h₂ : ¬ c ≤ b) :
    ¬ c ≤ a :=
  mt h₁.trans' h₂

theorem not_le_of_not_le_of_le {α : Type*} [Preorder α] {a b c : α} (h₁ : ¬ b ≤ a) (h₂ : b ≤ c) :
    ¬ c ≤ a :=
  mt h₂.trans h₁

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

/-! ### `exists_between` for Finsets -/

-- Written by Kenny Lau: https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/.60exists_between.60.20for.20finite.20sets/near/526965677

theorem Finset.exists_between {α : Type*} [LinearOrder α] [DenselyOrdered α] {s t : Finset α}
    (hs : s.Nonempty) (ht : t.Nonempty) (H : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  convert _root_.exists_between (a₁ := s.max' hs) (a₂ := t.min' ht) (by simp_all) <;> simp

theorem Finset.exists_between' {α : Type*} [LinearOrder α] [DenselyOrdered α] (s t : Finset α)
    [NoMaxOrder α] [NoMinOrder α] [Nonempty α]
    (H : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  by_cases hs : s.Nonempty <;> by_cases ht : t.Nonempty
  · exact s.exists_between hs ht H
  · exact let ⟨p, hp⟩ := exists_gt (s.max' hs); ⟨p, by simp_all⟩
  · exact let ⟨p, hp⟩ := exists_lt (t.min' ht); ⟨p, by simp_all⟩
  · exact Nonempty.elim ‹_› fun p ↦ ⟨p, by simp_all⟩

theorem Set.Finite.exists_between {α : Type*} [LinearOrder α] [DenselyOrdered α] {s t : Set α}
    (hsf : s.Finite) (hs : s.Nonempty) (htf : t.Finite) (ht : t.Nonempty)
    (H : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  convert Finset.exists_between (s := hsf.toFinset) (t := htf.toFinset)
    (by simpa) (by simpa) (by simpa) using 1; simp

theorem Set.Finite.exists_between' {α : Type*} [LinearOrder α] [DenselyOrdered α]
    [NoMaxOrder α] [NoMinOrder α] [Nonempty α] {s t : Set α} (hs : s.Finite) (ht : t.Finite)
    (H : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  convert hs.toFinset.exists_between' ht.toFinset (by simpa) using 1; simp
