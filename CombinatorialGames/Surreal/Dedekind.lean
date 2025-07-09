/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Surreal.Basic

/-!
# Dedekind cuts of Surreals

TODO: write docstring
-/

namespace Surreal
open Set

structure Cut where
  left : Set Surreal
  right : Set Surreal
  left_lf_right' : ∀ l ∈ left, ∀ r ∈ right, l ⧏ r
  codisjoint' : Codisjoint left right

namespace Cut

noncomputable instance : DecidableEq Cut := Classical.decEq Cut

theorem ext {c d : Cut} (hl : c.left = d.left) (hr : c.right = d.right) : c = d := by
  cases c; cases d; cases hl; cases hr; rfl

theorem left_lf_right {c : Cut} {l r : Surreal} (hl : l ∈ c.left) (hr : r ∈ c.right) : l ⧏ r :=
  c.left_lf_right' l hl r hr

theorem codisjoint {c : Cut} : Codisjoint c.left c.right := c.codisjoint'

@[simp]
theorem left_union_right {c : Cut} : c.left ∪ c.right = univ := by
  simpa using codisjoint_iff.1 c.codisjoint

@[simp]
theorem right_union_left {c : Cut} : c.right ∪ c.left = univ := by
  simpa using codisjoint_iff.1 c.codisjoint.symm

theorem disjoint {c : Cut} : Disjoint c.left c.right := by
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
  intro x hx
  exact c.left_lf_right hx.left hx.right le_rfl

@[simp]
theorem left_inter_right {c : Cut} : c.left ∩ c.right = ∅ := by
  simpa using disjoint_iff.1 c.disjoint

@[simp]
theorem right_inter_left {c : Cut} : c.right ∩ c.left = ∅ := by
  simpa using disjoint_iff.1 c.disjoint.symm

theorem isCompl {c : Cut} : IsCompl c.left c.right :=
  ⟨c.disjoint, c.codisjoint⟩

@[simp]
theorem compl_left {c : Cut} : c.leftᶜ = c.right :=
  c.isCompl.compl_eq

@[simp]
theorem compl_right {c : Cut} : c.rightᶜ = c.left :=
  c.isCompl.symm.compl_eq

theorem ext_left {c d : Cut} (h : c.left = d.left) : c = d := by
  refine ext h ?_
  rwa [← compl_inj_iff, c.compl_right, d.compl_right]

theorem ext_right {c d : Cut} (h : c.right = d.right) : c = d := by
  refine ext ?_ h
  rwa [← compl_inj_iff, c.compl_left, d.compl_left]

theorem isLowerSet_left {c : Cut} : IsLowerSet c.left := by
  intro x y hyx hx
  by_contra hy
  rw [← mem_compl_iff, c.compl_left] at hy
  exact c.left_lf_right hx hy hyx

theorem isUpperSet_right {c : Cut} : IsUpperSet c.right := by
  simpa using isUpperSet_compl.2 c.isLowerSet_left

instance : LE Cut where
  le a b := a.left ⊆ b.left ∧ b.right ⊆ a.right

noncomputable instance : DecidableLE Cut := Classical.decRel LE.le

theorem le_iff_subset {a b : Cut} : a ≤ b ↔ a.left ⊆ b.left ∧ b.right ⊆ a.right := Iff.rfl

theorem le_iff_right {a b : Cut} : a ≤ b ↔ b.right ⊆ a.right := by
  rw [le_iff_subset, ← compl_subset_compl, compl_left, compl_left, and_self]

theorem le_iff_left {a b : Cut} : a ≤ b ↔ a.left ⊆ b.left := by
  rw [le_iff_right, ← compl_subset_compl, compl_right, compl_right]

instance : LT Cut where
  lt a b := (b.left ∩ a.right).Nonempty

noncomputable instance : DecidableLT Cut := Classical.decRel LT.lt

theorem lt_iff_nonempty {a b : Cut} : a < b ↔ (b.left ∩ a.right).Nonempty := Iff.rfl

protected theorem not_le {a b : Cut} : ¬a ≤ b ↔ b < a := by
  simp_rw [le_iff_left, not_subset, ← mem_compl_iff]
  rw [← inter_nonempty_iff_exists_left, compl_left, lt_iff_nonempty]

protected theorem le_of_lt {a b : Cut} (h : a < b) : a ≤ b := by
  rw [lt_iff_nonempty] at h
  rw [le_iff_left]
  obtain ⟨x, hx⟩ := h
  intro y hy
  refine b.isLowerSet_left ?_ hx.left
  exact le_of_not_ge (a.left_lf_right hy hx.right)

instance : Preorder Cut where
  le_refl _ := ⟨subset_rfl, subset_rfl⟩
  le_trans a b c hab hbc := ⟨hab.left.trans hbc.left, hbc.right.trans hab.right⟩
  lt_iff_le_not_ge a b := by
    rw [Cut.not_le, iff_and_self]
    exact Cut.le_of_lt

instance : PartialOrder Cut where
  le_antisymm _ _ hab hba :=
    ext (subset_antisymm hab.left hba.left) (subset_antisymm hba.right hab.right)

instance : BoundedOrder Cut where
  top := {
    left := univ
    right := ∅
    left_lf_right' := by simp
    codisjoint' _ h _ := by simpa using h
  }
  le_top c := ⟨subset_univ c.left, empty_subset c.right⟩
  bot := {
    left := ∅
    right := univ
    left_lf_right' := by simp
    codisjoint' _ _ h := by simpa using h
  }
  bot_le c := ⟨empty_subset c.left, subset_univ c.right⟩

@[simp] theorem left_top : left ⊤ = univ := rfl
@[simp] theorem right_top : right ⊤ = ∅ := rfl
@[simp] theorem left_bot : left ⊥ = ∅ := rfl
@[simp] theorem right_bot : right ⊥ = univ := rfl

instance : Lattice Cut where
  sup a b := {
    left := a.left ∪ b.left
    right := a.right ∩ b.right
    left_lf_right' l hl r hr :=
      hl.elim (fun h => a.left_lf_right h hr.left) (fun h => b.left_lf_right h hr.right)
    codisjoint' := by
      simp_rw [codisjoint_iff_le_sup, sup_eq_union]
      rw [union_inter_distrib_left, union_right_comm, left_union_right,
        union_assoc, left_union_right]
      simp
  }
  le_sup_left _ _ := le_iff_subset.2 (by simp)
  le_sup_right _ _ := le_iff_subset.2 (by simp)
  sup_le := by simp +contextual [le_iff_subset]
  inf a b := {
    left := a.left ∩ b.left
    right := a.right ∪ b.right
    left_lf_right' l hl r hr :=
      hr.elim (a.left_lf_right hl.left) (b.left_lf_right hl.right)
    codisjoint' := by
      simp_rw [codisjoint_iff_le_sup, sup_eq_union]
      rw [inter_union_distrib_right, ← union_assoc, left_union_right,
        union_left_comm, left_union_right]
      simp
  }
  inf_le_left _ _ := le_iff_subset.2 (by simp)
  inf_le_right _ _ := le_iff_subset.2 (by simp)
  le_inf := by simp +contextual [le_iff_subset]

noncomputable instance : LinearOrder Cut :=
  have : IsTotal Cut (· ≤ ·) := by
    constructor
    intro a b
    rw [or_iff_not_imp_left]
    intro h
    exact Cut.le_of_lt (Cut.not_le.1 h)
  Lattice.toLinearOrder Cut

noncomputable instance : CompleteLinearOrder Cut where
  __ := inferInstanceAs (LinearOrder Cut)
  __ := (inferInstanceAs (LinearOrder Cut)).toBiheytingAlgebra
  sSup s := {
    left := ⋃ i ∈ s, i.left
    right := ⋂ i ∈ s, i.right
    left_lf_right' l hl r hr := by
      rw [mem_iUnion₂] at hl
      rw [mem_iInter₂] at hr
      obtain ⟨i, hi, hl⟩ := hl
      specialize hr i hi
      exact left_lf_right hl hr
    codisjoint' := by
      simp_rw [codisjoint_iff_le_sup, top_eq_univ, sup_eq_union]
      rw [union_iInter₂]
      conv =>
        enter [2, 1, i, 1, hi]
        equals univ =>
          rw [← univ_subset_iff, ← i.left_union_right]
          apply union_subset_union_left
          exact subset_biUnion_of_mem hi
      simp
  }
  le_sSup s i hi := le_iff_left.2 (subset_biUnion_of_mem hi)
  sSup_le := by simp +contextual [le_iff_subset]
  sInf s := {
    left := ⋂ i ∈ s, i.left
    right := ⋃ i ∈ s, i.right
    left_lf_right' l hl r hr := by
      rw [mem_iInter₂] at hl
      rw [mem_iUnion₂] at hr
      obtain ⟨i, hi, hr⟩ := hr
      specialize hl i hi
      exact left_lf_right hl hr
    codisjoint' := by
      simp_rw [codisjoint_iff_le_sup, top_eq_univ, sup_eq_union]
      rw [iInter₂_union]
      conv =>
        enter [2, 1, i, 1, hi]
        equals univ =>
          rw [← univ_subset_iff, ← i.left_union_right]
          apply union_subset_union_right
          exact subset_biUnion_of_mem hi
      simp
  }
  sInf_le s i hi := le_iff_right.2 (subset_biUnion_of_mem hi)
  le_sInf := by simp +contextual [le_iff_subset]
