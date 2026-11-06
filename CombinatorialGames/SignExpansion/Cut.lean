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

theorem Set.mem_union_of_codisjoint {α : Type*} {x y : Set α} (h : Codisjoint x y) (z : α) :
    z ∈ x ∪ y := by
  simpa using Set.ext_iff.1 (codisjoint_iff.1 h) z

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
def toSignExpansion (x : Cut) : SignExpansion :=
  if ∃ a ∈ x.left, ∀ b ∈ x.left, b ≤ a
    then ⨅ y ∈ x.right, y.toSignExpansion
    else ⨆ y ∈ x.left, y.toSignExpansion

attribute [gcongr] OrderEmbedding.strictMono

theorem left_lt_toSignExpansion {x : Cut} {y : Surreal} (hy : y ∈ x.left) :
    y.toSignExpansion < toSignExpansion x := by
  rw [toSignExpansion]
  split_ifs with hl
  · exact lt_biInf_toSignExpansion_right hy
  · push Not at hl
    obtain ⟨z, hz, hyz⟩ := hl y hy
    grw [hyz]
    apply le_biSup
    simpa

theorem toSignExpansion_lt_right {x : Cut} {y : Surreal} (hy : y ∈ x.right) :
    toSignExpansion x < y.toSignExpansion := by
  rw [toSignExpansion]
  split_ifs with hl
  · obtain ⟨l, hl, hl'⟩ := hl
    have hr : ∀ a ∈ x.right, ∃ b ∈ x.right, b < a := by
      by_contra! hr
      obtain ⟨r, hr, hr'⟩ := hr
      obtain ⟨z, hzl, hzr⟩ := exists_between (x.left_lt_right hl hr)
      obtain hz | hz := Set.mem_union_of_codisjoint x.isCompl_left_right.codisjoint z
      · exact (hl' z hz).not_gt hzl
      · exact (hr' z hz).not_gt hzr
    obtain ⟨z, hz, hzy⟩ := hr y hy
    grw [← hzy]
    apply biInf_le
    simpa
  · exact biSup_toSignExpansion_left_lt hy

theorem toSignExpansion_strictMono : StrictMono toSignExpansion := by
  intro x y h
  rw [lt_iff_nonempty_inter] at h
  obtain ⟨z, hx, hy⟩ := h
  exact (toSignExpansion_lt_right hx).trans (left_lt_toSignExpansion hy)

@[simp]
theorem toSignExpansion_lt_toSignExpansion {x y : Cut} :
    x.toSignExpansion < y.toSignExpansion ↔ x < y :=
  toSignExpansion_strictMono.lt_iff_lt

@[simp]
theorem toSignExpansion_le_toSignExpansion {x y : Cut} :
    x.toSignExpansion ≤ y.toSignExpansion ↔ x ≤ y :=
  toSignExpansion_strictMono.le_iff_le

@[simp]
theorem toSignExpansion_inj {x y : Cut} :
    x.toSignExpansion = y.toSignExpansion ↔ x = y :=
  toSignExpansion_strictMono.injective.eq_iff

@[simp]
theorem length_toSignExpansion (x : Cut) : x.toSignExpansion.length = ⊤ := by
  by_contra! h
  rw [← small_iff_length_ne_top] at h
  obtain ⟨y, hyx⟩ := mem_range_toSignExpansion x.toSignExpansion
  obtain hy | hy := Set.mem_union_of_codisjoint x.isCompl_left_right.codisjoint y
  · exact (left_lt_toSignExpansion hy).ne hyx
  · exact (toSignExpansion_lt_right hy).ne' hyx

@[simp]
theorem not_small_toSignExpansion (x : Cut) : ¬ x.toSignExpansion.Small := by
  simp [small_iff_length_ne_top]

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

@[simp]
theorem toSignExpansion_leftSurreal (x : Surreal) :
    (leftSurreal x).toSignExpansion = .pred x.toSignExpansion := by
  apply toSignExpansion_eq
  · simp_rw [left_leftSurreal, Set.mem_Iio]
    intro y hy
    obtain ⟨z, hzy, hxz⟩ := exists_between hy
    grw [hzy]
    simpa
  · simp

@[simp]
theorem toSignExpansion_rightSurreal (x : Surreal) :
    (rightSurreal x).toSignExpansion = .succ x.toSignExpansion := by
  conv_lhs => rw [← neg_neg x, ← neg_leftSurreal, toSignExpansion_neg]
  simp

theorem toSignExpansion_eq_biSup_left (x : Cut) :
    toSignExpansion x = ⨆ y ∈ x.left, y.toSignExpansion.succ := by
  apply toSignExpansion_eq <;> intro y hy
  · apply (lt_succ _).trans_le
    apply le_iSup₂ y hy
  · grw [← toSignExpansion_lt_right hy]
    refine iSup₂_le fun z hz ↦ ?_
    rw [succ_le_iff]
    exact left_lt_toSignExpansion hz

theorem toSignExpansion_eq_biInf_right (x : Cut) :
    toSignExpansion x = ⨅ y ∈ x.right, y.toSignExpansion.pred := by
  apply toSignExpansion_eq <;> intro y hy
  · grw [left_lt_toSignExpansion hy]
    refine le_iInf₂ fun z hz ↦ ?_
    rw [le_pred_iff]
    exact toSignExpansion_lt_right hz
  · exact (iInf₂_le y hy).trans_lt (pred_lt _)

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
