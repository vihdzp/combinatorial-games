/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.SignExpansion.Surreal
public import CombinatorialGames.Surreal.Cut


/-!
# Cuts as sign expansion

A cut can be thought of as a `Surreal` of birthday `univ`. In particular, they correspond to sign
sequences without any zeros. This file constructs this correspondence.
-/

public noncomputable section

open SignExpansion

namespace Surreal.Cut

theorem biSup_toSignExpansion_left_lt {x : Cut} {y : Surreal} (hy : y ∈ x.right) :
    ⨆ y ∈ x.left, toSignExpansion y < toSignExpansion y := by
  apply (iSup₂_le fun z hz ↦ ?_).trans_lt (pred_lt _)
  simpa using x.left_lt_right hz hy

theorem lt_biInf_toSignExpansion_right {x : Cut} {y : Surreal} (hy : y ∈ x.left) :
    toSignExpansion y < ⨅ y ∈ x.right, toSignExpansion y := by
  refine (lt_succ _).trans_le (le_iInf₂ fun z hz ↦ ?_)
  simpa using x.left_lt_right hy hz

open Classical in
/-- The sign expansion associated to a cut, thought of as a surreal of birthday `univ`. -/
def toSignExpansion : Cut ↪o SignExpansion :=
  .ofStrictMono (fun x ↦ ⨆ y ∈ x.left, y.toSignExpansion.succ) <| by
    intro x y h
    obtain ⟨z, hx, hy⟩ := lt_iff_nonempty_inter.1 h
    apply lt_of_le_of_lt (b := z.toSignExpansion)
    · refine iSup₂_le fun w hw ↦ ?_
      simpa using x.left_lt_right hw hx
    · rw [← succ_le_iff]
      apply le_biSup _ hy

attribute [gcongr] OrderEmbedding.strictMono

theorem left_lt_toSignExpansion {x : Cut} {y : Surreal} (hy : y ∈ x.left) :
    y.toSignExpansion < toSignExpansion x := by
  rw [← succ_le_iff]
  apply le_biSup _ hy

theorem toSignExpansion_lt_right {x : Cut} {y : Surreal} (hy : y ∈ x.right) :
    toSignExpansion x < y.toSignExpansion := by
  change ⨆ y ∈ x.left, y.toSignExpansion.succ < _
  obtain hl | hr := noMax_left_or_noMin_right x
  · rw [← le_pred_iff]
    refine iSup₂_le fun z hz ↦ ?_
    obtain ⟨w, hw, hzw⟩ := hl z hz
    grw [succ_le_iff, hzw, le_pred_iff, OrderEmbedding.lt_iff_lt]
    exact x.left_lt_right hw hy
  · obtain ⟨r, hr, hry⟩ := hr y hy
    grw [← hry]
    refine iSup₂_le fun z hz ↦ ?_
    rw [succ_le_iff, OrderEmbedding.lt_iff_lt]
    exact x.left_lt_right hz hr

@[simp]
theorem not_small_toSignExpansion (x : Cut) : ¬ x.toSignExpansion.Small := by
  intro
  obtain ⟨y, hyx⟩ := mem_range_toSignExpansion x.toSignExpansion
  obtain hy | hy := Set.mem_union_of_codisjoint x.isCompl_left_right.codisjoint y
  · exact (left_lt_toSignExpansion hy).ne hyx
  · exact (toSignExpansion_lt_right hy).ne' hyx

@[simp]
theorem length_toSignExpansion (x : Cut) : x.toSignExpansion.length = ⊤ := by
  rw [← not_ne_iff, ← small_iff_length_ne_top]
  exact not_small_toSignExpansion x

/-- The sign expansion corresponding to `x` is the unique sign expansion between those of all the
surreals in the left and right sets. -/
theorem toSignExpansion_eq {x : Cut} {y : SignExpansion}
    (hl : ∀ z ∈ x.left, z.toSignExpansion < y) (hr : ∀ z ∈ x.right, y < z.toSignExpansion) :
    toSignExpansion x = y := by
  by_contra! h
  obtain hlt | hlt := h.lt_or_gt
  · by_cases hcov : x.toSignExpansion ⋖ y
    · obtain ⟨h, _⟩ | ⟨_, hxy⟩ := covBy_iff.1 hcov
      · simp at h
      · obtain ⟨y, rfl⟩ := mem_range_toSignExpansion y
        obtain hy | hy := Set.mem_union_of_codisjoint x.isCompl_left_right.codisjoint y
        · exact (hl y hy).false
        · exact (hr y hy).false
    · rw [not_covBy_iff hlt] at hcov
      obtain ⟨z, _, hxz, hzy⟩ := exists_small_between hcov
      obtain ⟨z, rfl⟩ := mem_range_toSignExpansion z
      obtain hz | hz := Set.mem_union_of_codisjoint x.isCompl_left_right.codisjoint z
      · exact (left_lt_toSignExpansion hz).asymm hxz
      · exact (hr z hz).asymm hzy
  · by_cases hcov : y ⋖ x.toSignExpansion
    · obtain ⟨_, hyx⟩ | ⟨h, _⟩ := covBy_iff.1 hcov
      · obtain ⟨y, rfl⟩ := mem_range_toSignExpansion y
        obtain hy | hy := Set.mem_union_of_codisjoint x.isCompl_left_right.codisjoint y
        · exact (hl y hy).false
        · exact (hr y hy).false
      · simp at h
    · rw [not_covBy_iff hlt] at hcov
      obtain ⟨z, _, hyz, hzx⟩ := exists_small_between hcov
      obtain ⟨z, rfl⟩ := mem_range_toSignExpansion z
      obtain hz | hz := Set.mem_union_of_codisjoint x.isCompl_left_right.codisjoint z
      · exact (hl z hz).asymm hyz
      · exact (toSignExpansion_lt_right hz).asymm hzx

@[simp]
theorem toSignExpansion_neg (x : Cut) : toSignExpansion (-x) = -toSignExpansion x := by
  apply toSignExpansion_eq
  · simpa using fun _ ↦ toSignExpansion_lt_right
  · simpa using fun _ ↦ left_lt_toSignExpansion

theorem toSignExpansion_eq_biSup_left (x : Cut) :
    toSignExpansion x = ⨆ y ∈ x.left, y.toSignExpansion.succ :=
  (rfl)

theorem toSignExpansion_eq_biInf_right (x : Cut) :
    toSignExpansion x = ⨅ y ∈ x.right, y.toSignExpansion.pred := by
  apply toSignExpansion_eq <;> intro y hy
  · grw [left_lt_toSignExpansion hy]
    refine le_iInf₂ fun z hz ↦ ?_
    rw [le_pred_iff]
    exact toSignExpansion_lt_right hz
  · exact (iInf₂_le y hy).trans_lt (pred_lt _)

@[simp]
theorem toSignExpansion_leftSurreal (x : Surreal) :
    (leftSurreal x).toSignExpansion = x.toSignExpansion.pred := by
  rw [toSignExpansion_eq_biInf_right]
  apply (le_iInf₂ _).antisymm' (biInf_le _ _) <;> simp

@[simp]
theorem toSignExpansion_rightSurreal (x : Surreal) :
    (rightSurreal x).toSignExpansion = x.toSignExpansion.succ := by
  conv_lhs => rw [← neg_neg x, ← neg_leftSurreal, toSignExpansion_neg]
  simp


/-
@[simp]
theorem range_toSignExpansion : Set.range toSignExpansion = {x | x.length = ⊤} := by
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro hx
-/


end Surreal.Cut
end
