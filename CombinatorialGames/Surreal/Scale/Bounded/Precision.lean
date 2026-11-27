/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Scale.Basic
public import CombinatorialGames.Surreal.Scale.Growth

/-!
# Bounded precisions of a growth class

The nonnegative simplest exponents bounded by a natural multiple of one leader form a small set.
Integer comparisons distinguish the exponents and small cuts give bounded suprema.
-/

universe u

open Set

public noncomputable section

namespace Surreal

variable (i : Surreal.{u})

local notation "C" => lowerGrowthSubring i
local notation "A" => unitExponentSubgroup (lowerGrowthSubring i)
local notation "z" => ω^ i

/-- Nonnegative simplest precision exponents bounded by a natural multiple of the growth
exponent. -/
def boundedPrecision : Set Surreal.{u} :=
  {t | 0 ≤ t ∧ cosetRep A t = t ∧ ∃ n : ℕ, t ≤ (n : Surreal.{u}) * z}

/-- Membership in the bounded nonnegative precision exponents of a growth class. -/
theorem mem_boundedPrecision {t : Surreal.{u}} :
    t ∈ boundedPrecision i ↔ 0 ≤ t ∧ cosetRep A t = t ∧
      ∃ n : ℕ, t ≤ (n : Surreal.{u}) * z := Iff.rfl

/-- The additive group of simplest precision exponents bounded in magnitude by natural
multiples of a growth exponent. -/
def boundedPrecisionGroup : AddSubgroup Surreal.{u} where
  carrier := {t | cosetRep A t = t ∧ ∃ n : ℕ, |t| ≤ (n : Surreal.{u}) * z}
  zero_mem' := ⟨cosetRep_zero _, 0, by simp⟩
  add_mem' := by
    rintro s t ⟨hs, n, hsn⟩ ⟨ht, m, htm⟩
    refine ⟨by rw [cosetRep_add, hs, ht], n + m, ?_⟩
    rw [Nat.cast_add, add_mul]
    exact (abs_add_le s t).trans (add_le_add hsn htm)
  neg_mem' := by
    rintro t ⟨ht, n, htn⟩
    exact ⟨by rw [cosetRep_neg, ht], n, by simpa only [abs_neg] using htn⟩

/-- Membership in the additive group of bounded simplest exponents. -/
theorem mem_boundedPrecisionGroup {t : Surreal.{u}} :
    t ∈ boundedPrecisionGroup i ↔ cosetRep A t = t ∧
      ∃ n : ℕ, |t| ≤ (n : Surreal.{u}) * z := Iff.rfl

/-- The nonnegative cone of the bounded precision group is the set of bounded precisions. -/
theorem mem_boundedPrecision_iff_nonneg {t : Surreal.{u}} :
    t ∈ boundedPrecision i ↔ 0 ≤ t ∧ t ∈ boundedPrecisionGroup i := by
  rw [mem_boundedPrecision, mem_boundedPrecisionGroup]
  constructor
  · rintro ⟨h₀, hfix, n, hbound⟩
    exact ⟨h₀, hfix, n, by simpa only [abs_of_nonneg h₀] using hbound⟩
  · rintro ⟨h₀, hfix, n, hbound⟩
    exact ⟨h₀, hfix, n, by simpa only [abs_of_nonneg h₀] using hbound⟩

/-- Zero is a bounded nonnegative precision exponent. -/
theorem zero_mem_boundedPrecision : 0 ∈ boundedPrecision i :=
  (mem_boundedPrecision i).mpr ⟨le_rfl, cosetRep_zero _, 0, by simp⟩

/-- The exponent of a growth monomial is its own simplest precision representative. -/
theorem cosetRep_growthExponent_eq : cosetRep A z = z := by
  apply cosetRep_wpow_eq_of_notMem
  intro ha
  have hc := ((mem_unitExponentSubgroup_iff C).mp ha).1
  rw [← growthMonomial_eq] at hc
  have hlt := (mem_lowerGrowthSubring_iff i).mp hc 1
  rw [abs_of_pos (by rw [growthMonomial_eq]; exact wpow_pos _), pow_one] at hlt
  exact lt_irrefl _ hlt

/-- Addition preserves bounded nonnegative precision exponents. -/
theorem add_mem_boundedPrecision {s t : Surreal.{u}}
    (hs : s ∈ boundedPrecision i) (ht : t ∈ boundedPrecision i) :
    s + t ∈ boundedPrecision i := by
  obtain ⟨hs₀, hsfix, n, hsn⟩ := (mem_boundedPrecision i).mp hs
  obtain ⟨ht₀, htfix, m, htm⟩ := (mem_boundedPrecision i).mp ht
  refine (mem_boundedPrecision i).mpr ⟨add_nonneg hs₀ ht₀, ?_, n + m, ?_⟩
  · rw [cosetRep_add, hsfix, htfix]
  · rw [Nat.cast_add, add_mul]
    exact add_le_add hsn htm

/-- A nonnegative simplest precision below a bounded precision is bounded. -/
theorem mem_boundedPrecision_of_le {s t : Surreal.{u}} (hs : 0 ≤ s)
    (hsfix : cosetRep A s = s) (hst : s ≤ t) (ht : t ∈ boundedPrecision i) :
    s ∈ boundedPrecision i := by
  obtain ⟨n, hn⟩ := ((mem_boundedPrecision i).mp ht).2.2
  exact (mem_boundedPrecision i).mpr ⟨hs, hsfix, n, hst.trans hn⟩

/-- Subtracting a smaller bounded precision from a larger one gives a bounded precision. -/
theorem sub_mem_boundedPrecision {s t : Surreal.{u}}
    (hs : s ∈ boundedPrecision i) (ht : t ∈ boundedPrecision i) (hst : s ≤ t) :
    t - s ∈ boundedPrecision i := by
  obtain ⟨hs₀, hsfix, _, _⟩ := (mem_boundedPrecision i).mp hs
  have htfix := ((mem_boundedPrecision i).mp ht).2.1
  exact mem_boundedPrecision_of_le i (sub_nonneg.mpr hst)
    (by rw [cosetRep_sub, htfix, hsfix]) (sub_le_self t hs₀) ht

private theorem exists_nat_mul_ge_of_fixed_pos {t : Surreal.{u}} (ht : 0 < t)
    (htfix : cosetRep A t = t) : ∃ n : ℕ, z ≤ (n : Surreal.{u}) * t := by
  have hnot : ω^ t ∉ C :=
    (wpow_notMem_subring_iff C).mpr (by simpa only [htfix] using ht)
  rw [mem_lowerGrowthSubring_iff i] at hnot
  push Not at hnot
  obtain ⟨n, hn⟩ := hnot
  refine ⟨n, ?_⟩
  rwa [abs_of_pos (wpow_pos t), ← wpow_natCast_mul, growthMonomial_eq, wpow_le_wpow] at hn

private theorem exists_boundedPrecision_separator {x y : Surreal.{u}}
    (hx : x ∈ boundedPrecision i) (hy : y ∈ boundedPrecision i) (hxy : x < y) :
    ∃ n : ℕ, ∃ k : ℤ, (n : Surreal.{u}) * x < (k : Surreal.{u}) * z ∧
      (k : Surreal.{u}) * z ≤ (n : Surreal.{u}) * y := by
  obtain ⟨hx₀, hxfix, m, hxm⟩ := (mem_boundedPrecision i).mp hx
  obtain ⟨_, hyfix, _, _⟩ := (mem_boundedPrecision i).mp hy
  have hfix : cosetRep A (y - x) = y - x := by rw [cosetRep_sub, hxfix, hyfix]
  obtain ⟨n, hn⟩ := exists_nat_mul_ge_of_fixed_pos i (sub_pos.mpr hxy) hfix
  let a := (n : Surreal.{u}) * x / z
  have hpos : 0 ≤ a := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hx₀) (wpow_nonneg _)
  have hbound : a ≤ ((n * m : ℕ) : Surreal.{u}) := by
    apply (div_le_iff₀ (wpow_pos i)).mpr
    rw [Nat.cast_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hxm (Nat.cast_nonneg _)
  obtain ⟨k, hk⟩ := exists_floor' a ⟨0, by simpa only [Int.cast_zero] using hpos⟩
    ⟨((n * m : ℕ) : ℤ), by simpa only [Int.cast_natCast] using hbound⟩
  refine ⟨n, k + 1, ?_, ?_⟩
  · apply (div_lt_iff₀ (wpow_pos i)).mp
    apply lt_of_not_ge
    intro h
    exact (by omega : ¬ k + 1 ≤ k) ((hk _).mpr h)
  · have hkx := (le_div_iff₀ (wpow_pos i)).mp ((hk k).mp le_rfl)
    rw [Int.cast_add, Int.cast_one, add_mul, one_mul]
    rw [mul_sub] at hn
    linarith only [hkx, hn]

/-- The bounded precision exponents of a growth class form a small set. -/
instance small_boundedPrecision : Small.{u} (boundedPrecision i) := by
  let f (x : boundedPrecision i) : Set (ℕ × ℤ) :=
    {p | (p.2 : Surreal.{u}) * z ≤ (p.1 : Surreal.{u}) * (x : Surreal.{u})}
  suffices hf : Function.Injective f by
    let : Small.{0} (boundedPrecision i) := small_of_injective hf
    exact small_lift.{u + 1, u, 0} (boundedPrecision i)
  have separated (x y : boundedPrecision i) (hxy : (x : Surreal.{u}) < y) : f x ≠ f y := by
    obtain ⟨n, k, hx, hy⟩ := exists_boundedPrecision_separator i x.property y.property hxy
    intro heq
    have hy' : (n, k) ∈ f y := hy
    rw [← heq] at hy'
    exact hx.not_ge hy'
  intro x y hxy
  apply Subtype.ext
  rcases lt_trichotomy (x : Surreal.{u}) y with h | h | h
  · exact (separated x y h hxy).elim
  · exact h
  · exact (separated y x h hxy.symm).elim

/-- A nonempty collection of bounded precisions with a bounded upper bound has a least
bounded upper bound. -/
theorem exists_least_boundedPrecision_upperBound {T : Set Surreal.{u}} (hT : T.Nonempty)
    (hsub : T ⊆ boundedPrecision i)
    (hbdd : ∃ b ∈ boundedPrecision i, ∀ t ∈ T, t ≤ b) :
    ∃ b ∈ boundedPrecision i, (∀ t ∈ T, t ≤ b) ∧
      ∀ c ∈ boundedPrecision i, (∀ t ∈ T, t ≤ c) → b ≤ c := by
  by_cases hmax : ∃ b ∈ T, ∀ t ∈ T, t ≤ b
  · obtain ⟨b, hb, hub⟩ := hmax
    exact ⟨b, hsub hb, hub, fun c hc huc ↦ huc b hb⟩
  let R := {a ∈ boundedPrecision i | ∀ t ∈ T, t ≤ a}
  have hsmallT : Small.{u} T := small_subset hsub
  have hsmallR : Small.{u} R := small_subset (fun _ ha ↦ ha.1)
  have hsep : ∀ t ∈ T, ∀ a ∈ R, t < a := by
    intro t ht a ha
    exact (ha.2 t ht).lt_of_ne (fun e ↦ hmax ⟨a, e ▸ ht, ha.2⟩)
  let w : Surreal := !{T | R}' hsep
  let b := cosetRep A w
  have hub (t : Surreal.{u}) (ht : t ∈ T) : t ≤ b := by
    simpa only [((mem_boundedPrecision i).mp (hsub ht)).2.1] using
      monotone_cosetRep A (lt_ofSets_of_mem_left (H := hsep) ht).le
  have hle (a : Surreal.{u}) (ha : a ∈ boundedPrecision i) (hua : ∀ t ∈ T, t ≤ a) :
      b ≤ a := by
    simpa only [((mem_boundedPrecision i).mp ha).2.1] using
      monotone_cosetRep A (ofSets_lt_of_mem_right (H := hsep) ⟨ha, hua⟩).le
  obtain ⟨a, ha, hua⟩ := hbdd
  obtain ⟨t, ht⟩ := hT
  have hb₀ := (((mem_boundedPrecision i).mp (hsub ht)).1).trans (hub t ht)
  exact ⟨b, mem_boundedPrecision_of_le i hb₀ (cosetRep_cosetRep A w) (hle a ha hua) ha, hub, hle⟩

end Surreal
