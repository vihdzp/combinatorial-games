/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Int

/-!
# Dyadic numbers

A dyadic (rational) number is a rational number whose denominator is a power of two. We define them
as a subtype of `ℚ`, and build the `CommRing` structure, as well as proving some auxiliary theorems
on them.

This material belongs in Mathlib, though we do need to consider if the definition of `Dyadic` used
here is the best one.
-/

/-! ### For Mathlib

Most of these are no longer needed, but perhaps they'd make good contributions regardless? -/

theorem le_of_le_of_lt_of_lt {α β : Type*} [PartialOrder α] [Preorder β] {x y : α}
    {f : α → β} (h : x < y → f x < f y) (hxy : x ≤ y) : f x ≤ f y := by
  obtain rfl | h' := hxy.eq_or_lt
  · rfl
  · exact (h h').le

theorem Nat.pow_log_eq_self_iff {b n : ℕ} (hb : b ≠ 0) :
    b ^ Nat.log b n = n ↔ n ∈ Set.range (b ^ ·) := by
  constructor
  · aesop
  · rintro ⟨n, rfl⟩
    rw [← Nat.one_le_iff_ne_zero, le_iff_eq_or_lt] at hb
    obtain rfl | hb := hb
    · simp
    · rw [Nat.log_pow hb]

theorem Set.range_if {α β : Type*} {p : α → Prop} [DecidablePred p] {x y : β}
    (hp : ∃ a, p a) (hn : ∃ a, ¬ p a) :
    Set.range (fun a ↦ if p a then x else y) = {x, y} := by
  grind

theorem range_zero_pow {M : Type*} [MonoidWithZero M] : Set.range ((0 : M) ^ ·) = {1, 0} := by
  simp_rw [zero_pow_eq]
  exact Set.range_if ⟨0, rfl⟩ ⟨1, one_ne_zero⟩

instance (b n : ℕ) : Decidable (n ∈ Set.range (b ^ ·)) :=
  match b with
  | 0 => decidable_of_iff (n ∈ {1, 0}) (by rw [range_zero_pow])
  | b + 1 => decidable_of_iff _ (Nat.pow_log_eq_self_iff b.succ_ne_zero)

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

/-! ### Dyadic numbers -/

namespace Dyadic

attribute [coe] Dyadic.toRat
instance : Coe Dyadic ℚ := ⟨Dyadic.toRat⟩

instance : Inhabited Dyadic := ⟨0⟩
instance : Nontrivial Dyadic := ⟨0, 1, by decide⟩

@[simp, norm_cast] theorem coe_inj {x y : Dyadic} : (x : ℚ) = y ↔ x = y := toRat_inj
@[simp, norm_cast] theorem coe_lt_coe {x y : Dyadic} : (x : ℚ) < y ↔ x < y := lt_iff_toRat.symm
@[simp, norm_cast] theorem coe_le_coe {x y : Dyadic} : (x : ℚ) ≤ y ↔ x ≤ y := le_iff_toRat.symm

@[simp, norm_cast] theorem coe_zero : ((0 : Dyadic) : ℚ) = 0 := rfl
@[simp, norm_cast] theorem coe_one : ((1 : Dyadic) : ℚ) = 1 := rfl

@[simp, norm_cast] theorem coe_natCast (n : ℕ) : ((n : Dyadic) : ℚ) = n := toRat_natCast n
@[simp] theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] : ((ofNat(n) : Dyadic) : ℚ) = n := coe_natCast n

@[simp, norm_cast] theorem coe_intCast (n : ℤ) : ((n : Dyadic) : ℚ) = n := toRat_intCast n

@[simp] theorem natCast_lt_coe {x : ℕ} {y : Dyadic} : x < (y : ℚ) ↔ x < y := by norm_cast
@[simp] theorem natCast_le_coe {x : ℕ} {y : Dyadic} : x ≤ (y : ℚ) ↔ x ≤ y := by norm_cast
@[simp] theorem coe_lt_natCast {x : Dyadic} {y : ℕ} : (x : ℚ) < y ↔ x < y := by norm_cast
@[simp] theorem coe_le_natCast {x : Dyadic} {y : ℕ} : (x : ℚ) ≤ y ↔ x ≤ y := by norm_cast
@[simp] theorem coe_eq_natCast {x : Dyadic} {y : ℕ} : (x : ℚ) = y ↔ x = y := by norm_cast
@[simp] theorem natCast_eq_coe {x : ℕ} {y : Dyadic} : x = (y : ℚ) ↔ x = y := by norm_cast

@[simp] theorem intCast_lt_coe {x : ℤ} {y : Dyadic} : x < (y : ℚ) ↔ x < y := by norm_cast
@[simp] theorem intCast_le_coe {x : ℤ} {y : Dyadic} : x ≤ (y : ℚ) ↔ x ≤ y := by norm_cast
@[simp] theorem coe_lt_intCast {x : Dyadic} {y : ℤ} : (x : ℚ) < y ↔ x < y := by norm_cast
@[simp] theorem coe_le_intCast {x : Dyadic} {y : ℤ} : (x : ℚ) ≤ y ↔ x ≤ y := by norm_cast
@[simp] theorem coe_eq_intCast {x : Dyadic} {y : ℤ} : (x : ℚ) = y ↔ x = y := by norm_cast
@[simp] theorem intCast_eq_coe {x : ℤ} {y : Dyadic} : x = (y : ℚ) ↔ x = y := by norm_cast

@[simp] theorem zero_lt_coe {x : Dyadic} : 0 < (x : ℚ) ↔ 0 < x := natCast_lt_coe
@[simp] theorem zero_le_coe {x : Dyadic} : 0 ≤ (x : ℚ) ↔ 0 ≤ x := natCast_le_coe
@[simp] theorem coe_lt_zero {x : Dyadic} : (x : ℚ) < 0 ↔ x < 0 := coe_lt_natCast
@[simp] theorem coe_le_zero {x : Dyadic} : (x : ℚ) ≤ 0 ↔ x ≤ 0 := coe_le_natCast
@[simp] theorem coe_eq_zero {x : Dyadic} : (x : ℚ) = 0 ↔ x = 0 := coe_eq_intCast
@[simp] theorem zero_eq_coe {x : Dyadic} : 0 = (x : ℚ) ↔ 0 = x := intCast_eq_coe

@[simp] theorem one_lt_coe {x : Dyadic} : 1 < (x : ℚ) ↔ 1 < x := natCast_lt_coe
@[simp] theorem one_le_one {x : Dyadic} : 1 ≤ (x : ℚ) ↔ 1 ≤ x := natCast_le_coe
@[simp] theorem coe_lt_one {x : Dyadic} : (x : ℚ) < 1 ↔ x < 1 := coe_lt_natCast
@[simp] theorem coe_le_one {x : Dyadic} : (x : ℚ) ≤ 1 ↔ x ≤ 1 := coe_le_natCast
@[simp] theorem coe_eq_one {x : Dyadic} : (x : ℚ) = 1 ↔ x = 1 := coe_eq_intCast
@[simp] theorem one_eq_coe {x : Dyadic} : 1 = (x : ℚ) ↔ 1 = x := intCast_eq_coe

@[simp, norm_cast] theorem coe_neg (x : Dyadic) : ((-x : Dyadic) : ℚ) = -x := toRat_neg x
@[simp, norm_cast] theorem coe_add (x y : Dyadic) : ((x + y : Dyadic) : ℚ) = x + y := toRat_add x y
@[simp, norm_cast] theorem coe_sub (x y : Dyadic) : ((x - y : Dyadic) : ℚ) = x - y := toRat_sub x y
@[simp, norm_cast] theorem coe_mul (x y : Dyadic) : ((x * y : Dyadic) : ℚ) = x * y := toRat_mul x y
@[simp, norm_cast] theorem coe_pow (x : Dyadic) (n : ℕ) : ((x ^ n : Dyadic) : ℚ) = x ^ n :=
  toRat_pow x n

/-- The dyadic number ½. -/
def half : Dyadic := .ofOdd 1 1 rfl

@[simp]
theorem coe_half : (half : ℚ) = 2⁻¹ := by
  rw [Rat.inv_def]
  rfl

instance : LinearOrder Dyadic where
  le_refl := Dyadic.le_refl
  le_trans _ _ _ := Dyadic.le_trans
  le_antisymm _ _ := Dyadic.le_antisymm
  le_total := Dyadic.le_total
  lt_iff_le_not_ge x y := by simp_rw [← coe_lt_coe, ← coe_le_coe, lt_iff_le_not_ge]
  toDecidableLE := inferInstance

instance : CommRing Dyadic where
  zero_add := Dyadic.zero_add
  add_zero := Dyadic.add_zero
  add_comm := Dyadic.add_comm
  add_assoc := Dyadic.add_assoc
  zero_mul := Dyadic.zero_mul
  mul_zero := Dyadic.mul_zero
  one_mul := Dyadic.one_mul
  mul_one := Dyadic.mul_one
  mul_comm := Dyadic.mul_comm
  mul_assoc := Dyadic.mul_assoc
  left_distrib := Dyadic.mul_add
  right_distrib := Dyadic.add_mul
  neg_add_cancel := Dyadic.neg_add_cancel
  natCast_succ n := by rw [← coe_inj, coe_natCast]; simp
  intCast_negSucc n := by rw [← coe_inj, coe_intCast]; simp
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : IsStrictOrderedRing Dyadic where
  add_le_add_left x y := by simp_rw [← coe_le_coe, coe_add]; exact fun h _ ↦ add_le_add_left h _
  le_of_add_le_add_left x y z := by simp_rw [← coe_le_coe, coe_add]; exact le_of_add_le_add_left
  mul_lt_mul_of_pos_left x y z := by simp_rw [← coe_lt_coe, coe_mul]; exact mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right x y z := by simp_rw [← coe_lt_coe, coe_mul]; exact mul_lt_mul_of_pos_right
  zero_le_one := rfl

instance : DenselyOrdered Dyadic where
  dense x y h := by
    use half * (x + y)
    simp_rw [← coe_lt_coe] at *
    constructor
    · simpa [inv_mul_eq_div] using left_lt_add_div_two.2 h
    · simpa [inv_mul_eq_div] using add_div_two_lt_right.2 h

instance : Archimedean Dyadic where
  arch x y h := by
    obtain ⟨n, hn⟩ := exists_lt_nsmul (zero_lt_coe.2 h) x
    use n
    simpa [← coe_le_coe] using hn.le

/-- Numerator of a dyadic number. -/
def num (x : Dyadic) : ℤ := (x : ℚ).num
/-- The base 2 logarithm of the denominator of a dyadic number. -/
def den : Dyadic → ℕ
  | 0 | .ofOdd _ (-((k : ℕ) + 1)) _ => 0
  | .ofOdd _ (k : ℕ) _ => k

@[simp] theorem num_coe (x : Dyadic) : (x : ℚ).num = x.num := rfl
@[simp] theorem den_coe : ∀ x : Dyadic, (x : ℚ).den = 2 ^ x.den
  | 0 | .ofOdd _ (-((k : ℕ) + 1)) _ | .ofOdd _ (k : ℕ) _ => rfl

@[simp] theorem num_zero : (0 : Dyadic).num = 0 := rfl
@[simp] theorem den_zero : (0 : Dyadic).den = 0 := rfl

@[simp] theorem num_one : (1 : Dyadic).num = 1 := rfl
@[simp] theorem den_one : (1 : Dyadic).den = 0 := rfl

@[simp] theorem num_half : half.num = 1 := rfl
@[simp] theorem den_half : half.den = 1 := rfl

@[simp] theorem num_ofOdd (n : ℤ) (k : ℕ) (h : n % 2 = 1) : (Dyadic.ofOdd n k h).num = n := rfl
@[simp] theorem den_ofOdd (n : ℤ) (k : ℕ) (h : n % 2 = 1) : (Dyadic.ofOdd n k h).den = k := rfl

@[simp]
theorem num_ofOdd_neg (n : ℤ) (k : ℕ) (hn : n % 2 = 1) :
    (Dyadic.ofOdd n (-k) hn).num = n * 2 ^ k := by
  cases k
  · rw [pow_zero, _root_.mul_one]; rfl
  · rw [← Nat.cast_ofNat (n := 2), ← Nat.cast_pow]; rfl

@[simp]
theorem den_ofOdd_neg (n : ℤ) (k : ℕ) (hn : n % 2 = 1) :
    (Dyadic.ofOdd n (-k) hn).den = 0 := by
  cases k <;> rfl

@[simp, norm_cast] theorem num_intCast (n : ℤ) : (n : Dyadic).num = n := by
  rw [← num_coe, toRat_intCast, Rat.num_intCast]
@[simp, norm_cast] theorem den_intCast (n : ℤ) : (n : Dyadic).den = 0 := by
  rw [← Nat.pow_right_inj one_lt_two, ← den_coe, toRat_intCast, Rat.den_intCast, pow_zero]

@[simp, norm_cast] theorem num_natCast (n : ℕ) : (n : Dyadic).num = n := num_intCast n
@[simp, norm_cast] theorem den_natCast (n : ℕ) : (n : Dyadic).den = 0 := den_intCast n

@[simp] theorem num_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : Dyadic).num = n := num_natCast n
@[simp] theorem den_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : Dyadic).den = 0 := den_natCast n

@[simp] theorem num_neg (x : Dyadic) : (-x).num = -x.num := by
  rw [← num_coe, toRat_neg, Rat.num_neg_eq_neg_num, num_coe]
@[simp] theorem den_neg (x : Dyadic) : (-x).den = x.den := by
  rw [← Nat.pow_right_inj one_lt_two, ← den_coe, toRat_neg, Rat.den_neg_eq_den, den_coe]

/-
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
  exact (Nat.not_coprime_of_dvd_of_dvd one_lt_two · hd x.1.reduced)

theorem intCast_num_eq_self_of_den_eq_one {x : Dyadic} (hx : x.den = 1) : x.num = x := by
  ext
  exact Rat.coe_int_num_of_den_eq_one hx

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
  suffices x + x = Dyadic.mkRat (2 * x.num) x.den_mem_powers from
    this ▸ den_mkRat_lt (Int.dvd_mul_right 2 x.num) hx
  ext
  simp [Rat.mkRat_eq_div, Rat.num_div_den, mul_div_assoc, ← two_mul]

theorem eq_mkRat_of_den_le {x : Dyadic} {n : ℕ} (h : x.den ≤ n) (hn : n ∈ Submonoid.powers 2) :
    ∃ m, x = .mkRat m hn := by
  use x.num * (n / x.den)
  ext
  rw [← x.mkRat_self, val_mkRat, val_mkRat,
    Rat.mkRat_eq_iff x.den_ne_zero (ne_zero_of_mem_powers hn), mkRat_self, mul_assoc]
  congr
  exact (Nat.div_mul_cancel ((dvd_iff_le_of_mem_powers x.den_mem_powers hn).2 h)).symm

instance : CanLift Dyadic Int Int.cast (·.1.den = 1) where
  prf x hx := ⟨x.1.num, Dyadic.ext (x.1.den_eq_one_iff.mp hx)⟩

theorem den_add_le_den_right {x y : Dyadic} (h : x.den ≤ y.den) : (x + y).den ≤ y.den := by
  obtain ⟨n, hn⟩ := eq_mkRat_of_den_le h y.den_mem_powers
  conv_lhs => rw [← y.mkRat_self, hn, mkRat_add_mkRat_self]
  exact den_mkRat_le _ y.den_ne_zero
-/

end Dyadic
