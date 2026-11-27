/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Dyadic.Basic
public import Mathlib.Data.Nat.Log

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Dyadic numbers

This file contains auxiliary theorems for dyadic numbers, which should get upstreamed to Mathlib.
-/

@[expose] public section

/-! ### For Mathlib -/

theorem Nat.pow_log_eq_self_iff {b n : ℕ} (hb : b ≠ 0) :
    b ^ Nat.log b n = n ↔ n ∈ Set.range (b ^ ·) := by
  constructor
  · aesop
  · rintro ⟨n, rfl⟩
    rw [← Nat.one_le_iff_ne_zero, le_iff_eq_or_lt] at hb
    obtain rfl | hb := hb
    · simp
    · rw [Nat.log_pow hb]

theorem pos_of_mem_powers {n : ℕ} (h : n ∈ Submonoid.powers 2) : 0 < n := by
  obtain ⟨n, rfl⟩ := h
  exact pow_pos (Nat.succ_pos 1) n

theorem ne_zero_of_mem_powers {n : ℕ} (h : n ∈ Submonoid.powers 2) : n ≠ 0 :=
  (pos_of_mem_powers h).ne'

theorem dvd_iff_le_of_mem_powers {m n : ℕ}
    (hm : m ∈ Submonoid.powers 2) (hn : n ∈ Submonoid.powers 2) : m ∣ n ↔ m ≤ n := by
  obtain ⟨m, rfl⟩ := hm
  obtain ⟨n, rfl⟩ := hn
  simp_all [pow_dvd_pow_iff, pow_le_pow_iff_right₀]

namespace Dyadic

/-- Numerator of a dyadic number. -/
abbrev num (x : Dyadic) : ℤ := x.toRat.num
/-- Denominator of a dyadic number. -/
abbrev den (x : Dyadic) : ℕ := x.toRat.den

theorem den_ne_zero (x : Dyadic) : x.den ≠ 0 := Rat.den_ne_zero x
theorem den_pos (x : Dyadic) : 0 < x.den := Rat.den_pos x
theorem one_le_den (x : Dyadic) : 1 ≤ x.den := x.den_pos
theorem den_mem_powers (x : Dyadic) : x.den ∈ Submonoid.powers 2 := by
  fun_cases toRat x with
  | case1 -- zero
  | case3 => exact one_mem _ -- integer
  | case2 => apply pow_mem; exact Submonoid.mem_powers 2 -- dyadic rational

theorem den_eq_two_pow_toNat_precision (x : Dyadic) :
    x.den = 2 ^ (x.precision.getD 0).toNat := by
  cases x with
  | zero => rfl
  | ofOdd n k hn =>
    cases k with
    | ofNat k => rfl
    | negSucc k => rfl

theorem precision_eq_none {x : Dyadic} : x.precision = none ↔ x = 0 := by
  cases x <;> simp

theorem isSome_precision_eq_true {x : Dyadic} : x.precision.isSome = true ↔ x ≠ 0 :=
  Option.isSome_iff_ne_none.trans Dyadic.precision_eq_none.not

theorem isSome_precision_eq_true_of_den_ne_one {x : Dyadic} (hx : x.den ≠ 1) :
    x.precision.isSome = true :=
  x.isSome_precision_eq_true.mpr (mt (by rintro rfl; rfl) hx)

@[simp]
theorem den_le_one_iff_eq_one {x : Dyadic} : x.den ≤ 1 ↔ x.den = 1 := by
  simp_rw [Nat.le_one_iff_eq_zero_or_eq_one, x.den_ne_zero, false_or]

@[simp]
theorem one_lt_den_iff_ne_one {x : Dyadic} : 1 < x.den ↔ x.den ≠ 1 := by
  simp [← den_le_one_iff_eq_one]

theorem den_ne_one_of_den_lt {x y : Dyadic} (h : x.den < y.den) : y.den ≠ 1 := by
  simpa using (one_le_den x).trans_lt h

@[ext] theorem ext {x y : Dyadic} (h : (x : ℚ) = y) : x = y := toRat_inj.1 h

@[simp, norm_cast] theorem num_natCast (n : ℕ) : (n : Dyadic).num = n :=
  congrArg Rat.num (toRat_natCast n)
@[simp, norm_cast] theorem den_natCast (n : ℕ) : (n : Dyadic).den = 1 :=
  congrArg Rat.den (toRat_natCast n)

@[simp] theorem num_ofNat (n : ℕ) : (ofNat(n) : Dyadic).num = n :=
  num_natCast n
@[simp] theorem den_ofNat (n : ℕ) : (ofNat(n) : Dyadic).den = 1 :=
  den_natCast n

@[simp] theorem natCast_lt_toRat {x : ℕ} {y : Dyadic} : x < y.toRat ↔ x < y := by norm_cast
@[simp] theorem natCast_le_toRat {x : ℕ} {y : Dyadic} : x ≤ y.toRat ↔ x ≤ y := by norm_cast
@[simp] theorem toRat_lt_natCast {x : Dyadic} {y : ℕ} : x.toRat < y ↔ x < y := by norm_cast
@[simp] theorem toRat_le_natCast {x : Dyadic} {y : ℕ} : x.toRat ≤ y ↔ x ≤ y := by norm_cast

@[simp, norm_cast] theorem toRat_eq_natCast {x : Dyadic} {y : ℕ} : x.toRat = y ↔ x = y := by
  rw [← toRat_natCast, toRat_inj]
@[simp, norm_cast] theorem natCast_eq_toRat {x : ℕ} {y : Dyadic} : x = y.toRat ↔ x = y := by
  rw [← toRat_natCast, toRat_inj]

@[norm_cast] alias coe_intCast := toRat_intCast
@[simp, norm_cast] theorem num_intCast (n : ℤ) : (n : Dyadic).num = n :=
  congrArg Rat.num (toRat_intCast n)
@[simp, norm_cast] theorem den_intCast (n : ℤ) : (n : Dyadic).den = 1 :=
  congrArg Rat.den (toRat_intCast n)

@[simp] theorem intCast_lt_toRat {x : ℤ} {y : Dyadic} : x < y.toRat ↔ x < y := by norm_cast
@[simp] theorem intCast_le_toRat {x : ℤ} {y : Dyadic} : x ≤ y.toRat ↔ x ≤ y := by norm_cast
@[simp] theorem toRat_lt_intCast {x : Dyadic} {y : ℤ} : x.toRat < y ↔ x < y := by norm_cast
@[simp] theorem toRat_le_intCast {x : Dyadic} {y : ℤ} : x.toRat ≤ y ↔ x ≤ y := by norm_cast
@[simp] theorem toRat_eq_intCast {x : Dyadic} {y : ℤ} : x.toRat = y ↔ x = y := by norm_cast
@[simp] theorem intCast_eq_toRat {x : ℤ} {y : Dyadic} : x = y.toRat ↔ x = y := by norm_cast

instance : Inhabited Dyadic := ⟨0⟩

@[simp] theorem num_zero : (0 : Dyadic).num = 0 := rfl
@[simp] theorem den_zero : (0 : Dyadic).den = 1 := rfl

@[simp] theorem zero_lt_toRat {x : Dyadic} : 0 < x.toRat ↔ 0 < x := by norm_cast
@[simp] theorem zero_le_toRat {x : Dyadic} : 0 ≤ x.toRat ↔ 0 ≤ x := by norm_cast
@[simp] theorem toRat_lt_zero {x : Dyadic} : x.toRat < 0 ↔ x < 0 := by norm_cast
@[simp] theorem toRat_le_zero {x : Dyadic} : x.toRat ≤ 0 ↔ x ≤ 0 := by norm_cast
alias toRat_eq_zero := toRat_eq_zero_iff
@[simp] theorem zero_eq_toRat {x : Dyadic} : 0 = x.toRat ↔ 0 = x := by norm_cast

@[simp] theorem num_one : (1 : Dyadic).num = 1 := rfl
@[simp] theorem den_one : (1 : Dyadic).den = 1 := rfl

attribute [norm_cast] toRat_one

@[simp] theorem one_lt_toRat {x : Dyadic} : 1 < x.toRat ↔ 1 < x := by norm_cast
@[simp] theorem one_le_toRat {x : Dyadic} : 1 ≤ x.toRat ↔ 1 ≤ x := by norm_cast
@[simp] theorem toRat_lt_one {x : Dyadic} : x.toRat < 1 ↔ x < 1 := by norm_cast
@[simp] theorem toRat_le_one {x : Dyadic} : x.toRat ≤ 1 ↔ x ≤ 1 := by norm_cast
@[simp] theorem toRat_eq_one {x : Dyadic} : x.toRat = 1 ↔ x = 1 := by norm_cast
@[simp] theorem one_eq_toRat {x : Dyadic} : 1 = x.toRat ↔ 1 = x := by norm_cast

@[simp] theorem num_neg (x : Dyadic) : (-x).num = -x.num := congrArg Rat.num (toRat_neg x)
@[simp] theorem den_neg (x : Dyadic) : (-x).den = x.den := (congrArg Rat.den (toRat_neg x) :)

instance : SMul Nat Dyadic where
  smul x y := x * y

@[norm_cast] theorem toRat_nsmul (x : ℕ) (y : Dyadic) : (x • y).toRat = x • y.toRat :=
  (toRat_mul x y).trans (by simp)

instance : SMul Int Dyadic where
  smul x y := x * y

@[norm_cast] theorem toRat_zsmul (x : ℤ) (y : Dyadic) : (x • y).toRat = x • y.toRat :=
  (toRat_mul x y).trans (by simp)

/-- The dyadic number ½. -/
def half : Dyadic := (1 : Dyadic) >>> 1

@[simp, norm_cast] theorem toRat_half : half.toRat = 2⁻¹ := (Rat.inv_def 2).symm
@[simp] theorem num_half : half.num = 1 := rfl
@[simp] theorem num_den : half.den = 2 := rfl

/-- Constructor for the fraction `m / n`. -/
protected def mkRat (m : ℤ) {n : ℕ} (h : n ∈ Submonoid.powers 2) : Dyadic :=
  ofIntWithPrec m (Submonoid.log ⟨n, h⟩)

@[simp, norm_cast]
theorem toRat_mkRat (m : ℤ) {n : ℕ} (h : n ∈ Submonoid.powers 2) :
    (Dyadic.mkRat m h).toRat = mkRat m n := by
  rw [Dyadic.mkRat, toRat_ofIntWithPrec_eq_mul_two_pow, zpow_neg,
    ← Nat.cast_two, zpow_natCast, ← Nat.cast_pow, ← Submonoid.pow_coe,
    Submonoid.pow_log_eq_self, Rat.mkRat_eq_div, div_eq_mul_inv]

@[simp] theorem mkRat_self (x : Dyadic) : Dyadic.mkRat x.num x.den_mem_powers = x := by ext; simp

@[simp]
theorem mkRat_one (m : ℤ) (h : 1 ∈ Submonoid.powers 2) : Dyadic.mkRat m h = m := by
  ext; simp [Rat.mkRat_one]

@[simp]
theorem mkRat_lt_mkRat {m n : ℤ} {k : ℕ} (h : k ∈ Submonoid.powers 2) :
    Dyadic.mkRat m h < Dyadic.mkRat n h ↔ m < n := by
  have hk : 0 < (k : ℚ) := by
    rw [Rat.natCast_pos, Nat.pos_iff_ne_zero]
    obtain ⟨n, rfl⟩ := h
    simp
  rw [← toRat_lt_toRat_iff]
  simp [Rat.mkRat_eq_div, div_lt_div_iff_of_pos_right hk]

@[simp]
theorem mkRat_le_mkRat {m n : ℤ} {k : ℕ} (h : k ∈ Submonoid.powers 2) :
    Dyadic.mkRat m h ≤ Dyadic.mkRat n h ↔ m ≤ n :=
  le_iff_le_iff_lt_iff_lt.2 (mkRat_lt_mkRat h)

theorem mkRat_add_mkRat_self {m n : ℤ} {k : ℕ} (h : k ∈ Submonoid.powers 2) :
    Dyadic.mkRat m h + Dyadic.mkRat n h = .mkRat (m + n) h := by
  ext; simp [Rat.mkRat_eq_div, add_div]

-- #46066
instance : DenselyOrdered Dyadic where
  dense x y h := by
    use half * (x + y)
    simp_rw [← toRat_lt_toRat_iff] at *
    constructor
    · simpa [inv_mul_eq_div] using left_lt_add_div_two.2 h
    · simpa [inv_mul_eq_div] using add_div_two_lt_right.2 h

-- #46066
instance : Archimedean Dyadic where
  arch x y h := by
    rw [← toRat_lt_toRat_iff, toRat_zero] at h
    obtain ⟨n, hn⟩ := exists_lt_nsmul h x.toRat
    refine ⟨n, ?_⟩
    rw [← toRat_le_toRat_iff, nsmul_eq_mul, toRat_mul, toRat_natCast, ← nsmul_eq_mul]
    exact hn.le

theorem even_den {x : Dyadic} (hx : x.den ≠ 1) : Even x.den := by
  obtain ⟨n, hn⟩ := x.den_mem_powers
  rw [← hn]
  cases n
  · simp_all
  · rw [even_iff_two_dvd]
    exact dvd_mul_left ..

theorem odd_num {x : Dyadic} (hx : x.den ≠ 1) : Odd x.num := by
  rw [← Int.not_even_iff_odd]
  have hd := even_den hx
  rw [even_iff_two_dvd] at *
  rw [← Int.natAbs_dvd_natAbs]
  exact (Nat.not_coprime_of_dvd_of_dvd one_lt_two · hd x.toRat.reduced)

theorem intCast_num_eq_self_of_den_eq_one {x : Dyadic} (hx : x.den = 1) : x.num = x := by
  ext
  rw [toRat_intCast]
  exact Rat.intCast_num_of_den_eq_one hx

theorem den_mkRat_le (x : ℤ) {n : ℕ} (hn : n ≠ 0) : (mkRat x n).den ≤ n := by
  rw [← Rat.normalize_eq_mkRat hn, Rat.normalize_eq hn]
  exact Nat.div_le_self n _

theorem den_mkRat_lt {x : Dyadic} {n : ℤ} (hn : 2 ∣ n) (hd : x.den ≠ 1) :
    (mkRat n x.den).den < x.den := by
  rw [← Rat.normalize_eq_mkRat x.den_ne_zero, Rat.normalize_eq]
  apply Nat.div_lt_self x.den_pos
  apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ x.den_pos) (Nat.dvd_gcd _ (even_den hd).two_dvd)
  rwa [← Int.natAbs_dvd_natAbs] at hn

theorem den_add_self_lt {x : Dyadic} (hx : x.den ≠ 1) : (x + x).den < x.den := by
  suffices x + x = Dyadic.mkRat (2 * x.num) x.den_mem_powers by
    rw [this, den, Dyadic.toRat_mkRat]
    exact den_mkRat_lt (Int.dvd_mul_right 2 x.num) hx
  ext
  simp [Rat.mkRat_eq_div, Rat.num_div_den, mul_div_assoc, ← two_mul]

theorem eq_mkRat_of_den_le {x : Dyadic} {n : ℕ} (h : x.den ≤ n) (hn : n ∈ Submonoid.powers 2) :
    ∃ m, x = .mkRat m hn := by
  use x.num * (n / x.den)
  ext
  rw [← x.mkRat_self, toRat_mkRat, toRat_mkRat,
    Rat.mkRat_eq_iff x.den_ne_zero (ne_zero_of_mem_powers hn), mkRat_self, Int.mul_assoc]
  congr
  exact (Nat.div_mul_cancel ((dvd_iff_le_of_mem_powers x.den_mem_powers hn).2 h)).symm

instance : CanLift Dyadic Int Int.cast (·.den = 1) where
  prf x hx := ⟨x.num, Dyadic.ext (toRat_intCast x.num ▸ x.toRat.den_eq_one_iff.mp hx)⟩

theorem den_add_le_den_right {x y : Dyadic} (h : x.den ≤ y.den) : (x + y).den ≤ y.den := by
  obtain ⟨n, hn⟩ := eq_mkRat_of_den_le h y.den_mem_powers
  conv_lhs => rw [← y.mkRat_self, hn, mkRat_add_mkRat_self]
  rw [den, Dyadic.toRat_mkRat]
  exact den_mkRat_le _ y.den_ne_zero

/-- Coercion as a `RingHom`. -/
@[simps]
def toRatRingHom : Dyadic →+* ℚ where
  toFun := Dyadic.toRat
  map_zero' := rfl
  map_one' := rfl
  map_add' := toRat_add
  map_mul' := toRat_mul

section shift

theorem toRat_shiftRight (x : Dyadic) (n : ℤ) : toRat (x >>> n) = toRat x * 2 ^ (-n) := by
  simp_rw [(· >>> ·), Dyadic.shiftRight]
  match x with
  | .zero => norm_num
  | .ofOdd m k hm =>
      rw [toRat_ofOdd_eq_mul_two_pow, toRat_ofOdd_eq_mul_two_pow, neg_add, zpow_add₀ two_ne_zero]
      ring

@[simp] theorem shiftRight_shiftRight (x : Dyadic) (m n : ℤ) : x >>> m >>> n = x >>> (m + n) := by
  simp_rw [(· >>> ·), Dyadic.shiftRight, Dyadic.ext_iff]
  cases x
  · gcongr
  · group

theorem add_shiftRight (x y : Dyadic) (n : ℤ) : (x + y) >>> n = x >>> n + y >>> n := by
  simp only [Dyadic.ext_iff, toRat_shiftRight, toRat_add, zpow_neg]
  ring

@[simp] theorem shiftRight_one_add_shiftRight_one (x : Dyadic) :
    x >>> (1 : ℤ) + x >>> (1 : ℤ) = x := by
  rw [Dyadic.ext_iff, toRat_add, toRat_shiftRight]
  ring

@[simp] theorem shiftRight_add_one_add_shiftRight_add_one (x : Dyadic) (n : ℤ) :
    x >>> (n + 1) + x >>> (n + 1) = x >>> n := by
  rw [← shiftRight_shiftRight, shiftRight_one_add_shiftRight_one (x >>> n)]

theorem shiftRight_pos_of_pos (x : Dyadic) (n : ℤ) (h : 0 < x) : 0 < x >>> n := by
  rw [← toRat_lt_toRat_iff, toRat_shiftRight]
  simp_all only [coe_ofNat, Nat.cast_zero, zero_lt_coe, mul_pos_iff_of_pos_left]
  exact Rat.zpow_pos rfl

end shift

end Dyadic
end
