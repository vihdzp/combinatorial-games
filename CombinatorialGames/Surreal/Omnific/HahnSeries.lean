/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Surreal.HahnSeries.Addition

/-!
# Characterization of omnific integers by Hahn series

We show that omnific integers are exactly those whose support is contained in the nonnegative
surreals, and whose zero coefficient is an integer.
-/

public noncomputable section

open Set

namespace Surreal
variable {x y : Surreal}

/-! ### Characterization -/

theorem IsOmnific.support_subset (h : IsOmnific x) : support x ⊆ Ici 0 := by
  simpa using support_subset_of_round_eq h

theorem IsOmnific.coeff_eq_zero_of_lt (h : IsOmnific x) (hy : y < 0) : x.coeff y = 0 := by
  rw [← notMem_support_iff]
  exact fun hyx ↦ (h.support_subset hyx).not_gt hy

theorem IsOmnific.of_support_subset_Ioi (hx : x.support ⊆ Ioi 0) : IsOmnific x := by
  apply round_eq_of_support_subset _ zero_lt_one
  simpa

@[simp]
theorem IsOmnific.trunc_zero (x : Surreal) : IsOmnific (x.trunc 0) := by
  apply IsOmnific.of_support_subset_Ioi
  simp

theorem IsOmnific.trunc_add_coeff_eq (h : IsOmnific x) : x.trunc 0 + x.coeff 0 = x := by
  ext i
  rw [coeff_add, coeff_realCast]
  obtain hi | rfl | hi := lt_trichotomy i 0
  · rw [coeff_trunc_of_ge hi.le, Pi.single_eq_of_ne hi.ne, zero_add, h.coeff_eq_zero_of_lt hi]
  · rw [coeff_trunc_of_ge le_rfl, Pi.single_eq_same, zero_add]
  · rw [coeff_trunc_of_lt hi, Pi.single_eq_of_ne hi.ne', add_zero]

theorem IsOmnific.infPart_eq_zero (h : IsOmnific x) : infPart x = 0 := by
  rw [infPart, sub_sub, h.trunc_add_coeff_eq, sub_self]

theorem IsOmnific.coeff_zero_mem_range_intCast (h : IsOmnific x) :
    x.coeff 0 ∈ range ((↑) : ℤ → _) := by
  rwa [← isOmnific_realCast_iff, ← isOmnific_add_iff_right (.trunc_zero x), h.trunc_add_coeff_eq]

theorem isOmnific_iff_subset_and_mem_range :
    IsOmnific x ↔ support x ⊆ Ici 0 ∧ x.coeff 0 ∈ range ((↑) : ℤ → _) where
  mp hx := ⟨hx.support_subset, hx.coeff_zero_mem_range_intCast⟩
  mpr := by
    intro ⟨hx, ⟨n, hn⟩⟩
    rw [← isOmnific_sub_iff_left (.intCast n), ← Real.toSurreal_intCast, hn]
    apply IsOmnific.of_support_subset_Ioi
    rw [← Ici_sdiff_left]
    apply subset_sdiff_singleton
    · apply support_sub_subset.trans (union_subset hx <| support_realCast_subset.trans _)
      simp
    · simp

@[simp]
theorem isOmnific_wpow_iff : IsOmnific (ω^ x) ↔ 0 ≤ x := by
  rw [isOmnific_iff_subset_and_mem_range]
  aesop

/-! ### Floor and ceiling -/

open scoped Classical in
/-- `⌊x⌋ₛ` is the greatest omnific integer `n` such that `n ≤ x`. -/
def floor (x : Surreal) : Omnific :=
  let n' := x.trunc 0 + ⌊x.coeff 0⌋
  let n := Omnific.mk n' <| (IsOmnific.trunc_zero x).add (.intCast _)
  if x < n' then n - 1 else n

@[inherit_doc] notation "⌊" x "⌋ₛ" => Surreal.floor x

@[simp]
theorem trunc_floor_zero (x : Surreal) : trunc ⌊x⌋ₛ 0 = x.trunc 0 := by
  rw [floor]
  split_ifs <;> simp

theorem coeff_floor_of_pos (x : Surreal) {i : Surreal} (hi : 0 < i) : coeff ⌊x⌋ₛ i = coeff x i := by
  rw [← coeff_trunc_of_lt hi, trunc_floor_zero, coeff_trunc_of_lt hi]

theorem coeff_floor_zero_le (x : Surreal) : coeff ⌊x⌋ₛ 0 ≤ x.coeff 0 := by
  rw [floor]
  split_ifs with h
  · simpa using (Int.floor_le _).trans (lt_add_one _).le
  · simpa using Int.floor_le _

@[simp]
theorem floor_le (x : Surreal) : ⌊x⌋ₛ ≤ x := by
  rw [floor]
  split_ifs with h
  · apply le_of_lt
    rw [Omnific.coe_sub, Omnific.coe_mk, Omnific.coe_one, lt_iff_coeff]
    refine ⟨0, fun i hi ↦ ?_, ?_⟩
    · aesop
    · simpa using (sub_one_lt _).trans_le (Int.floor_le _)
  · simpa using h

@[simp]
theorem lt_floor_add_one (x : Surreal) : x < ⌊x⌋ₛ + 1 := by
  rw [floor]
  split_ifs with h
  · simpa
  · rw [not_lt] at h
    rw [Omnific.coe_mk]
    obtain h | h := h.eq_or_lt
    · conv_lhs => rw [← h]
      simp
    · obtain ⟨i, hix, hix'⟩ := lt_iff_coeff.1 h
      obtain hi | rfl | hi := lt_trichotomy 0 i
      · simp [hi, hi.ne'] at hix'
      · simp at hix'
        rw [add_assoc, ← sub_lt_iff_lt_add', ← sub_lt_sub_iff_right, ← infPart,
          ← Real.toSurreal_one, ← Real.toSurreal_intCast, ← Real.toSurreal_add,
          ← Real.toSurreal_sub]
        have H : 0 < (↑⌊x.coeff 0⌋ + 1 - x.coeff 0 : ℝ) := by simp
        apply ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg
        · rw [ArchimedeanClass.mk_realCast H.ne']
          exact archimedeanClassMk_infPart_pos _
        · rw [Real.toSurreal_nonneg_iff]
          exact H.le
      · rw [lt_iff_coeff]
        refine ⟨0, fun j hji ↦ ?_, ?_⟩
        · aesop
        · simp

theorem gc_coe_floor : GaloisConnection Omnific.coe floor := by
  intro n x
  obtain h | h := le_or_gt n ⌊x⌋ₛ
  · apply iff_of_true _ h
    grw [h, floor_le]
  · apply iff_of_false _ h.not_ge
    rw [← Order.add_one_le_iff, ← Omnific.coe_le_coe, Omnific.coe_add_one] at h
    exact ((lt_floor_add_one _).trans_le h).not_ge

@[simp]
theorem le_floor {n : Omnific} {x : Surreal} : n ≤ ⌊x⌋ₛ ↔ n ≤ x :=
  gc_coe_floor.le_iff_le.symm

@[simp]
theorem floor_lt {n : Omnific} {x : Surreal} : ⌊x⌋ₛ < n ↔ x < n :=
  gc_coe_floor.lt_iff_lt.symm

@[simp]
theorem floor_coe (n : Omnific) : ⌊n⌋ₛ = n := by
  rw [← Omnific.coe_inj]
  apply (floor_le n).antisymm
  rw [Omnific.coe_le_coe, le_floor]

@[simp]
theorem floor_realCast (r : ℝ) : ⌊r⌋ₛ = ⌊r⌋ := by
  rw [floor]
  split_ifs with h
  · contrapose! h
    simpa using mod_cast Int.floor_le r
  · ext
    simp

@[simp] theorem floor_ratCast (q : ℚ) : ⌊q⌋ₛ = ⌊q⌋ := mod_cast floor_realCast q
@[simp] theorem floor_intCast (n : ℤ) : ⌊n⌋ₛ = n := by simpa using floor_coe n
@[simp] theorem floor_natCast (n : ℕ) : ⌊n⌋ₛ = n := by simpa using floor_coe n
@[simp] theorem floor_zero : ⌊0⌋ₛ = 0 := by simpa using floor_coe 0
@[simp] theorem floor_one : ⌊1⌋ₛ = 1 := by simpa using floor_coe 1

/-- `⌈x⌉ₛ` is the smallest omnific integer `n` such that `x ≤ n`. -/
def ceil (x : Surreal) : Omnific :=
  -⌊-x⌋ₛ

@[inherit_doc] notation "⌈" x "⌉ₛ" => Surreal.ceil x

@[simp] theorem ceil_neg (x : Surreal) : ⌈-x⌉ₛ = -⌊x⌋ₛ := by simp [ceil]
@[simp] theorem floor_neg (x : Surreal) : ⌊-x⌋ₛ = -⌈x⌉ₛ := by simp [ceil]

@[simp]
theorem trunc_ceil_zero (x : Surreal) : trunc ⌈x⌉ₛ 0 = x.trunc 0 := by
  rw [ceil, Omnific.coe_neg, trunc_neg, trunc_floor_zero, trunc_neg, neg_neg]

theorem coeff_ceil_of_pos (x : Surreal) {i : Surreal} (hi : 0 < i) : coeff ⌈x⌉ₛ i = coeff x i := by
  rw [ceil, Omnific.coe_neg, coeff_neg, coeff_floor_of_pos _ hi, coeff_neg, neg_neg]

theorem le_coeff_ceil_zero (x : Surreal) : x.coeff 0 ≤ coeff ⌈x⌉ₛ 0 := by
  rw [ceil, Omnific.coe_neg, coeff_neg, le_neg, ← coeff_neg]
  exact coeff_floor_zero_le _

@[simp]
theorem le_ceil (x : Surreal) : x ≤ ⌈x⌉ₛ := by
  rw [ceil, Omnific.coe_neg, le_neg]
  exact floor_le _

@[simp]
theorem ceil_sub_one_lt (x : Surreal) : ⌈x⌉ₛ - 1 < x := by
  rw [ceil, Omnific.coe_neg, ← neg_add', neg_lt]
  exact lt_floor_add_one _

theorem gc_ceil_coe : GaloisConnection ceil Omnific.coe := by
  intro n x
  rw [ceil, neg_le, le_floor, Omnific.coe_neg, neg_le_neg_iff]

@[simp]
theorem ceil_le {n : Omnific} {x : Surreal} : ⌈x⌉ₛ ≤ n ↔ x ≤ n :=
  gc_ceil_coe.le_iff_le

@[simp]
theorem lt_ceil {n : Omnific} {x : Surreal} : n < ⌈x⌉ₛ ↔ n < x :=
  gc_ceil_coe.lt_iff_lt

@[simp]
theorem ceil_coe (n : Omnific) : ⌈n⌉ₛ = n := by
  simpa using floor_coe (-n)

@[simp]
theorem ceil_realCast (r : ℝ) : ⌈r⌉ₛ = ⌈r⌉ := by
  simpa [Int.floor_neg] using floor_realCast (-r)

@[simp] theorem ceil_ratCast (q : ℚ) : ⌈q⌉ₛ = ⌈q⌉ := mod_cast ceil_realCast q
@[simp] theorem ceil_intCast (n : ℤ) : ⌈n⌉ₛ = n := by simpa using ceil_coe n
@[simp] theorem ceil_natCast (n : ℕ) : ⌈n⌉ₛ = n := by simpa using ceil_coe n
@[simp] theorem ceil_zero : ⌈0⌉ₛ = 0 := by simpa using ceil_coe 0
@[simp] theorem ceil_one : ⌈1⌉ₛ = 1 := by simpa using ceil_coe 1

theorem IsOmnific.round_one (x : Surreal) : IsOmnific (x.round 1) := by
  by_contra hx
  obtain h | h | h := lt_trichotomy x (x.round 1)
  · refine (x.birthday_round_lt ⟨(sub_one_lt x).trans_le (le_ceil x), ?_⟩ ?_).not_ge
      (⌈x⌉ₛ.prop.birthday_le_of_mem_Ioo ⟨(ceil_sub_one_lt x).trans h, ?_⟩)
    · rw [← sub_lt_iff_lt_add]
      exact ceil_sub_one_lt x
    · contrapose hx
      rw [hx]
      exact Omnific.prop _
    · apply (round_lt_add zero_lt_one).trans_le
      simp
  · apply hx
    rwa [← h, IsOmnific, eq_comm]
  · refine (x.birthday_round_lt ⟨?_, (floor_le x).trans_lt (lt_add_one x)⟩ ?_).not_ge
      (⌊x⌋ₛ.prop.birthday_le_of_mem_Ioo ⟨?_, h.trans (lt_floor_add_one x)⟩)
    · rw [sub_lt_iff_lt_add]
      exact lt_floor_add_one x
    · contrapose hx
      rw [hx]
      exact Omnific.prop _
    · apply (sub_lt_round zero_lt_one).trans_le'
      simp

end Surreal
end
