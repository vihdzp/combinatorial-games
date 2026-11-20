/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Coset.Basic
public import CombinatorialGames.Surreal.Omnific.Basic
public import CombinatorialGames.Surreal.Pow

import CombinatorialGames.Surreal.Omnific.Coset
import CombinatorialGames.Surreal.Omnific.Order
import CombinatorialGames.Surreal.Scale.Basic
import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Convex subrings of bounded growth

The monomial \`ω^(ω^i)\` represents a growth class. Two convex subrings bound it, one consisting
of numbers all of whose finite powers are below it and the other consisting of numbers bounded
by some finite power of it. Comparing their simplest coset representatives detects whether
this growth class occurs in a number.
-/

universe u

public noncomputable section

namespace Surreal

open Set

/-- The representative of the growth class indexed by the exponent of its exponent leader. -/
def growthMonomial (i : Surreal.{u}) : Surreal.{u} :=
  ω^ (ω^ i)

theorem growthMonomial_eq (i : Surreal.{u}) : growthMonomial i = ω^ (ω^ i) := by
  unfold growthMonomial
  rfl

/-- The growth monomial exceeds every natural number. -/
theorem natCast_lt_growthMonomial (n : ℕ) (i : Surreal.{u}) :
    (n : Surreal.{u}) < growthMonomial i := by
  rw [growthMonomial_eq]
  simpa only [wpow_zero, mul_one] using Surreal.natCast_mul_wpow_lt_wpow n (wpow_pos i)

private theorem pow_max_lt {x y z : Surreal.{u}} {n : ℕ}
    (hx : x ^ n < z) (hy : y ^ n < z) : max x y ^ n < z := by
  rcases le_total x y with h | h
  · simpa only [max_eq_right h] using hy
  · simpa only [max_eq_left h] using hx

private theorem abs_add_le_square_max (x y : Surreal.{u}) :
    |x + y| ≤ max 2 (max |x| |y|) ^ 2 := by
  let m := max (2 : Surreal.{u}) (max |x| |y|)
  have hm : 2 ≤ m := le_max_left _ _
  have hm₀ : 0 ≤ m := (by norm_num : (0 : Surreal.{u}) ≤ 2).trans hm
  calc
    |x + y| ≤ |x| + |y| := abs_add_le _ _
    _ ≤ m + m := add_le_add
      ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
    _ = m * 2 := (mul_two _).symm
    _ ≤ m ^ 2 := by simpa only [pow_two] using mul_le_mul_of_nonneg_left hm hm₀

private theorem abs_mul_le_square_max (x y : Surreal.{u}) :
    |x * y| ≤ max 2 (max |x| |y|) ^ 2 := by
  rw [abs_mul, pow_two]
  exact mul_le_mul ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _)) (abs_nonneg _)
    ((abs_nonneg x).trans ((le_max_left _ _).trans (le_max_right _ _)))

private theorem abs_pow_lt_growthMonomial_of_bound {i x y z : Surreal.{u}}
    (h : |z| ≤ max 2 (max |x| |y|) ^ 2)
    (hx : ∀ n : ℕ, |x| ^ n < growthMonomial i)
    (hy : ∀ n : ℕ, |y| ^ n < growthMonomial i) (n : ℕ) :
    |z| ^ n < growthMonomial i := by
  refine (pow_le_pow_left₀ (abs_nonneg _) h _).trans_lt ?_
  rw [← pow_mul]
  apply pow_max_lt
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using natCast_lt_growthMonomial (2 ^ (2 * n)) i
  · exact pow_max_lt (hx _) (hy _)

/-- The convex subring of numbers whose finite powers of their magnitudes are strictly below
the representative of the given growth class. -/
def lowerGrowthSubring (i : Surreal.{u}) : Subring Surreal.{u} where
  carrier := {x | ∀ n : ℕ, |x| ^ n < growthMonomial i}
  zero_mem' := by
    change ∀ n : ℕ, |(0 : Surreal.{u})| ^ n < growthMonomial i
    intro n
    cases n with
    | zero => simpa using natCast_lt_growthMonomial 1 i
    | succ n => simpa using natCast_lt_growthMonomial 0 i
  one_mem' := by
    change ∀ n : ℕ, |(1 : Surreal.{u})| ^ n < growthMonomial i
    intro n
    simpa using natCast_lt_growthMonomial 1 i
  neg_mem' := by
    intro x hx
    simpa only [mem_ofPred_eq, abs_neg] using hx
  add_mem' := by
    intro x y hx hy
    exact abs_pow_lt_growthMonomial_of_bound (abs_add_le_square_max x y) hx hy
  mul_mem' := by
    intro x y hx hy
    exact abs_pow_lt_growthMonomial_of_bound (abs_mul_le_square_max x y) hx hy

theorem mem_lowerGrowthSubring_iff (i : Surreal.{u}) {x : Surreal.{u}} :
    x ∈ lowerGrowthSubring i ↔ ∀ n : ℕ, |x| ^ n < growthMonomial i :=
  Iff.rfl

instance lowerGrowthSubring_isConvex (i : Surreal.{u}) :
    (lowerGrowthSubring i).toAddSubgroup.IsConvex where
  ordConnected := by
    constructor
    intro x hx y hy z hz
    change x ∈ lowerGrowthSubring i at hx
    change y ∈ lowerGrowthSubring i at hy
    change z ∈ lowerGrowthSubring i
    rw [mem_lowerGrowthSubring_iff] at hx hy ⊢
    intro n
    exact (pow_le_pow_left₀ (abs_nonneg _) (abs_le_max_abs_abs hz.1 hz.2) n).trans_lt
      (pow_max_lt (hx n) (hy n))

/-- The convex subring of numbers bounded in magnitude by a finite power of the representative
of the given growth class. -/
def upperGrowthSubring (i : Surreal.{u}) : Subring Surreal.{u} where
  carrier := {x | ∃ n : ℕ, |x| ≤ growthMonomial i ^ n}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨0, by simp⟩
  neg_mem' := fun ⟨n, hn⟩ ↦ ⟨n, by simpa only [abs_neg] using hn⟩
  add_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    have hi : (2 : Surreal.{u}) ≤ growthMonomial i := by
      simpa using (natCast_lt_growthMonomial 2 i).le
    have h₁ := one_le_two.trans hi
    refine ⟨max m n + 1, (abs_add_le x y).trans ?_⟩
    rw [pow_succ]
    calc
      |x| + |y| ≤ growthMonomial i ^ max m n + growthMonomial i ^ max m n :=
        add_le_add (hm.trans (pow_le_pow_right₀ h₁ (le_max_left m n)))
          (hn.trans (pow_le_pow_right₀ h₁ (le_max_right m n)))
      _ = growthMonomial i ^ max m n * 2 := (mul_two _).symm
      _ ≤ growthMonomial i ^ max m n * growthMonomial i :=
        mul_le_mul_of_nonneg_left hi (pow_nonneg (zero_le_one.trans h₁) _)
  mul_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    rw [abs_mul, pow_add]
    exact mul_le_mul hm hn (abs_nonneg _) ((abs_nonneg x).trans hm)

theorem mem_upperGrowthSubring_iff (i : Surreal.{u}) {x : Surreal.{u}} :
    x ∈ upperGrowthSubring i ↔ ∃ n : ℕ, |x| ≤ growthMonomial i ^ n :=
  Iff.rfl

instance upperGrowthSubring_isConvex (i : Surreal.{u}) :
    (upperGrowthSubring i).toAddSubgroup.IsConvex where
  ordConnected := by
    constructor
    intro x hx y hy z hz
    change x ∈ upperGrowthSubring i at hx
    change y ∈ upperGrowthSubring i at hy
    change z ∈ upperGrowthSubring i
    obtain ⟨m, hm⟩ := (mem_upperGrowthSubring_iff i).mp hx
    obtain ⟨n, hn⟩ := (mem_upperGrowthSubring_iff i).mp hy
    have hi : (1 : Surreal.{u}) ≤ growthMonomial i := by
      simpa using (natCast_lt_growthMonomial 1 i).le
    exact (mem_upperGrowthSubring_iff i).mpr
      ⟨max m n, (abs_le_max_abs_abs hz.1 hz.2).trans (max_le
          (hm.trans (pow_le_pow_right₀ hi (le_max_left m n)))
          (hn.trans (pow_le_pow_right₀ hi (le_max_right m n))))⟩

theorem lowerGrowthSubring_le_upperGrowthSubring (i : Surreal.{u}) :
    lowerGrowthSubring i ≤ upperGrowthSubring i := by
  intro x hx
  refine (mem_upperGrowthSubring_iff i).mpr ⟨1, ?_⟩
  simpa only [pow_one] using ((mem_lowerGrowthSubring_iff i).mp hx 1).le

theorem wpow_natCast_mul (a : Surreal.{u}) (n : ℕ) :
    ω^ ((n : Surreal.{u}) * a) = (ω^ a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.cast_succ, add_mul, one_mul, wpow_add, ih, pow_succ]

theorem growthMonomial_pow_lt_growthMonomial {i j : Surreal.{u}} (hij : i < j) (n : ℕ) :
    growthMonomial i ^ n < growthMonomial j := by
  simp only [growthMonomial_eq, ← wpow_natCast_mul, wpow_lt_wpow]
  exact Surreal.natCast_mul_wpow_lt_wpow n hij

theorem upperGrowthSubring_le_lowerGrowthSubring {i j : Surreal.{u}} (hij : i < j) :
    upperGrowthSubring i ≤ lowerGrowthSubring j := by
  intro x hx
  obtain ⟨m, hm⟩ := (mem_upperGrowthSubring_iff i).mp hx
  apply (mem_lowerGrowthSubring_iff j).mpr
  intro n
  refine (pow_le_pow_left₀ (abs_nonneg _) hm _).trans_lt ?_
  rw [← pow_mul]
  exact growthMonomial_pow_lt_growthMonomial hij (m * n)

/-- A growth class occurs when its lower and upper convex subrings give distinct simplest
representatives. -/
def GrowthOccurs (i x : Surreal.{u}) : Prop :=
  cosetRep (lowerGrowthSubring i).toAddSubgroup x ≠ cosetRep (upperGrowthSubring i).toAddSubgroup x

theorem growthOccurs_iff (i x : Surreal.{u}) :
    GrowthOccurs i x ↔
      cosetRep (lowerGrowthSubring i).toAddSubgroup x ≠
        cosetRep (upperGrowthSubring i).toAddSubgroup x :=
  Iff.rfl

private theorem strictAnti_growthOccurrenceBirthday (x : Surreal.{u}) :
    StrictAnti (fun i : {i : Surreal.{u} // GrowthOccurs i x} ↦
      (cosetRep (lowerGrowthSubring i.1).toAddSubgroup x).birthday) := by
  intro j i hij
  refine (birthday_cosetRep_le (H := (lowerGrowthSubring i.1).toAddSubgroup) ?_).trans_lt
    (birthday_cosetRep_lt_of_ne (H := (upperGrowthSubring j.1).toAddSubgroup) ?_
      ((growthOccurs_iff j.1 x).mp j.2).symm)
  · exact upperGrowthSubring_le_lowerGrowthSubring hij
      (Subring.mem_toAddSubgroup.mp (sub_cosetRep_mem (upperGrowthSubring j.1).toAddSubgroup x))
  · exact lowerGrowthSubring_le_upperGrowthSubring j.1
      (Subring.mem_toAddSubgroup.mp (sub_cosetRep_mem (lowerGrowthSubring j.1).toAddSubgroup x))

/-- The occurring growth classes of a surreal are well ordered in decreasing order. -/
theorem growthOccurs_wellFounded (x : Surreal.{u}) :
    WellFounded (fun i j : {i : Surreal.{u} // GrowthOccurs i x} ↦ j.1 < i.1) := by
  let d (i : {i : Surreal.{u} // GrowthOccurs i x}) :=
    (cosetRep (lowerGrowthSubring i.1).toAddSubgroup x).birthday
  refine Subrelation.wf ?_ (InvImage.wf d wellFounded_lt)
  intro i j h
  exact strictAnti_growthOccurrenceBirthday x h

instance small_growthOccurs (x : Surreal.{u}) :
    Small.{u} {i : Surreal.{u} // GrowthOccurs i x} := by
  let f (i : {i : Surreal.{u} // GrowthOccurs i x}) : Set.Iic x.birthday :=
    ⟨(cosetRep (lowerGrowthSubring i.1).toAddSubgroup x).birthday, birthday_cosetRep_le (by simp)⟩
  exact small_of_injective (f := f) fun i j h ↦
    (strictAnti_growthOccurrenceBirthday x).injective (congrArg Subtype.val h)

theorem exists_growthOccurs_of_infinite {x : Surreal.{u}} (h : ∀ n : ℕ, (n : Surreal) < |x|) :
    ∃ i, GrowthOccurs i x := by
  have hx : x ≠ 0 := by
    intro he
    simpa only [he, Nat.cast_zero, abs_zero, lt_self_iff_false] using h 0
  have ha : 0 < x.wlog := by
    rw [← wlog_one, wlog_lt_wlog_iff one_ne_zero hx, vlt_def]
    apply lt_of_not_ge
    rintro ⟨n, hn⟩
    exact (h n).not_ge (by simpa using hn)
  let i := x.wlog.wlog
  have hi : 0 < growthMonomial i := growthMonomial_eq i ▸ wpow_pos _
  have he := veq_def.mp (wpow_wlog_veq ha.ne')
  obtain ⟨m, hm⟩ := he.ge
  obtain ⟨n, hn⟩ := he.le
  change |ω^ i| ≤ m • |x.wlog| at hm
  change |x.wlog| ≤ n • |ω^ i| at hn
  simp only [wpow_abs, abs_of_pos ha, nsmul_eq_mul] at hm hn
  have hU : x ∈ upperGrowthSubring i := by
    have hp : growthMonomial i ^ n ∈ upperGrowthSubring i :=
      (mem_upperGrowthSubring_iff i).mpr ⟨n, by rw [abs_of_nonneg (pow_nonneg hi.le _)]⟩
    apply mem_subring_of_vle (upperGrowthSubring i) hp
    apply (wlog_le_wlog_iff hx (pow_ne_zero n hi.ne')).mp
    simpa only [wlog_pow, growthMonomial_eq, wlog_wpow] using hn
  have hL : x ∉ lowerGrowthSubring i := by
    intro hL
    have hpow : 0 < |x| ^ (m + 1) := pow_pos (abs_pos.mpr hx) _
    have hle := wlog_monotoneOn hpow hi (((mem_lowerGrowthSubring_iff i).mp hL (m + 1)).le)
    rw [wlog_pow, wlog_abs, growthMonomial_eq, wlog_wpow, Nat.cast_add, Nat.cast_one, add_mul,
        one_mul] at hle
    exact (hm.trans_lt (lt_add_of_pos_right _ ha)).not_ge hle
  refine ⟨i, (growthOccurs_iff i x).mpr ?_⟩
  have hp : cosetRep (upperGrowthSubring i).toAddSubgroup x = 0 := cosetRep_eq_zero_iff.mpr hU
  rw [hp]
  exact fun h ↦ hL (cosetRep_eq_zero_iff.mp h)

theorem IsOmnific.exists_intCast_of_not_growthOccurs {x : Surreal.{u}}
    (hx : IsOmnific x) (h : ∀ i, ¬ GrowthOccurs i x) :
    ∃ k : ℤ, (k : Surreal) = x := by
  have hb : ∃ n : ℕ, |x| ≤ n := by
    by_contra! hb
    obtain ⟨i, hi⟩ := exists_growthOccurs_of_infinite hb
    exact h i hi
  obtain ⟨n, hn⟩ := hb
  exact hx.exists_intCast_of_abs_le hn

theorem cosetRep_div_eq_div_of_isOmnific
    (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex] {x w : Surreal.{u}}
    (hw : IsOmnific w) (hwC : w ∈ C) (hw₀ : w ≠ 0) :
    cosetRep C.toAddSubgroup (x / w) = cosetRep C.toAddSubgroup x / w := by
  have hwabs : IsOmnific |w| := abs_by_cases IsOmnific hw hw.neg
  have h₁ : 1 ≤ |w| := hwabs.one_le_iff_pos.mpr (abs_pos.mpr hw₀)
  refine (cosetRep_eq_of_sub_mem (H := C.toAddSubgroup) ?_).trans
    (cosetRep_div_eq_of_isOmnific (cosetRep_cosetRep _ x) hw hwC hw₀)
  rw [← sub_div]
  apply abs_mem_iff.mp
  refine C.toAddSubgroup.mem_of_nonneg_of_le (abs_nonneg _) ?_
    (abs_mem_iff.mpr (sub_cosetRep_mem C.toAddSubgroup x))
  rw [abs_div]
  exact div_le_self (abs_nonneg _) h₁

theorem growthOccurs_div_iff {i x w : Surreal.{u}} (hw : IsOmnific w) (hw₀ : w ≠ 0)
    (hwC : w ∈ upperGrowthSubring i)
    (hres : x - w = cosetRep (upperGrowthSubring i).toAddSubgroup x) (j : Surreal.{u}) :
    GrowthOccurs j (x / w) ↔ i < j ∧ GrowthOccurs j x := by
  by_cases hij : i < j
  · simp only [hij, true_and, growthOccurs_iff]
    have hwL := upperGrowthSubring_le_lowerGrowthSubring hij hwC
    rw [cosetRep_div_eq_div_of_isOmnific _ hw hwL hw₀,
      cosetRep_div_eq_div_of_isOmnific _ hw
        (lowerGrowthSubring_le_upperGrowthSubring j hwL) hw₀]
    exact not_congr (div_left_inj₀ hw₀)
  · simp only [hij, false_and, iff_false, growthOccurs_iff, not_ne_iff]
    have hfix : cosetRep (upperGrowthSubring i).toAddSubgroup (x / w - 1) = x / w - 1 := by
      rw [show x / w - 1 = (x - w) / w by rw [sub_div, div_self hw₀], hres]
      exact cosetRep_div_eq_of_isOmnific (cosetRep_cosetRep _ _) hw hwC hw₀
    have hj : upperGrowthSubring j ≤ upperGrowthSubring i := by
      rcases (le_of_not_gt hij).lt_or_eq with h | rfl
      · exact (upperGrowthSubring_le_lowerGrowthSubring h).trans
          (lowerGrowthSubring_le_upperGrowthSubring i)
      · exact le_rfl
    have project (D : Subring Surreal.{u}) [D.toAddSubgroup.IsConvex]
        (hD : D ≤ upperGrowthSubring i) : cosetRep D.toAddSubgroup (x / w) = x / w - 1 := by
      have h := cosetRep_cosetRep_of_ge
        (show D.toAddSubgroup ≤ (upperGrowthSubring i).toAddSubgroup from hD) (x / w - 1)
      have h₁ : cosetRep D.toAddSubgroup 1 = 0 := cosetRep_eq_zero_iff.mpr D.one_mem
      rw [hfix, cosetRep_sub, h₁, sub_zero] at h
      exact h
    rw [project _ ((lowerGrowthSubring_le_upperGrowthSubring j).trans hj), project _ hj]

/-- The intersection of the lower convex subrings of a family of growth classes. -/
def commonLowerGrowthSubring (I : Set Surreal.{u}) : Subring Surreal.{u} :=
  ⨅ i : I, lowerGrowthSubring i

theorem mem_commonLowerGrowthSubring_iff (I : Set Surreal.{u}) {x : Surreal.{u}} :
    x ∈ commonLowerGrowthSubring I ↔ ∀ i ∈ I, x ∈ lowerGrowthSubring i := by
  rw [commonLowerGrowthSubring, Subring.mem_iInf]
  exact ⟨fun h i hi ↦ h ⟨i, hi⟩, fun h i ↦ h i i.2⟩

instance commonLowerGrowthSubring_isConvex (I : Set Surreal.{u}) :
    (commonLowerGrowthSubring I).toAddSubgroup.IsConvex where
  ordConnected := by
    constructor
    intro x hx y hy z hz
    apply (mem_commonLowerGrowthSubring_iff I).mpr
    intro i hi
    exact (AddSubgroup.IsConvex.ordConnected (H := (lowerGrowthSubring i).toAddSubgroup)).out
      ((mem_commonLowerGrowthSubring_iff I).mp hx i hi)
      ((mem_commonLowerGrowthSubring_iff I).mp hy i hi) hz

end Surreal
