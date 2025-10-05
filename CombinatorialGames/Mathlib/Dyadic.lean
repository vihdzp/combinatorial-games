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

## Todo

In the time since this file was created, `Dyadic` got added to Lean core. We've temporarily renamed
our implementation to `Dyadic'`. In the near future, these two implementations will be merged.
-/

/-! ### For Mathlib -/

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
  ext
  constructor
  · rintro ⟨a, rfl⟩
    dsimp
    split_ifs <;> simp
  · rintro (rfl | rfl)
    on_goal 1 => obtain ⟨a, ha⟩ := hp
    on_goal 2 => obtain ⟨a, ha⟩ := hn
    all_goals use a; simp_all

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

/-! ### Dyadic' numbers -/

/-- A dyadic rational number is one whose denominator is a power of two. -/
def IsDyadic (x : ℚ) : Prop := x.den ∈ Submonoid.powers 2

instance {m n : ℕ} : Decidable (m ∈ Submonoid.powers n) :=
  decidable_of_iff (m ∈ Set.range (n ^ ·)) (Submonoid.mem_powers_iff m n)

instance : DecidablePred IsDyadic :=
  fun x ↦ inferInstanceAs (Decidable (x.den ∈ _))

theorem IsDyadic.mkRat (x : ℤ) {y : ℕ} (hy : y ∈ Submonoid.powers 2) : IsDyadic (mkRat x y) := by
  obtain ⟨n, rfl⟩ := hy
  have := Rat.den_dvd x (2 ^ n)
  rw [dvd_prime_pow Int.prime_two] at this
  obtain ⟨m, -, hm⟩ := this
  obtain hm | hm := Int.associated_iff.1 hm
  · use m
    rw [Rat.mkRat_eq_divInt, Nat.cast_pow, Nat.cast_ofNat, ← Nat.cast_inj (R := ℤ), hm]
    simp
  · rw [← Nat.cast_ofNat, ← Nat.cast_pow 2 m, Nat.cast_eq_neg_cast] at hm
    simp_all

theorem IsDyadic.neg {x : ℚ} (hx : IsDyadic x) : IsDyadic (-x) := hx
@[simp] theorem IsDyadic.neg_iff {x : ℚ} : IsDyadic (-x) ↔ IsDyadic x := .rfl

theorem IsDyadic.natCast (n : ℕ) : IsDyadic n := ⟨0, rfl⟩
theorem IsDyadic.intCast (n : ℤ) : IsDyadic n := ⟨0, rfl⟩

theorem IsDyadic.add {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  rw [Rat.add_def']
  exact .mkRat _ (Submonoid.mul_mem _ hx hy)

theorem IsDyadic.sub {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem IsDyadic.mul {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x * y) := by
  rw [Rat.mul_def, Rat.normalize_eq_mkRat]
  exact .mkRat _ (Submonoid.mul_mem _ hx hy)

theorem IsDyadic.nsmul {x : ℚ} (n : ℕ) (hx : IsDyadic x) : IsDyadic (n • x) := by
  simpa using .mul (.natCast n) hx

theorem IsDyadic.zsmul {x : ℚ} (n : ℤ) (hx : IsDyadic x) : IsDyadic (n • x) := by
  simpa using .mul (.intCast n) hx

theorem IsDyadic.pow {x : ℚ} (hx : IsDyadic x) (n : ℕ) : IsDyadic (x ^ n) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hx

/-- The subtype of `IsDyadic` numbers.

We don't use `Localization.Away 2`, as this would not give us any computability, nor would it allow
us to talk about numerators and denominators.

TODO: replace this with `Dyadic` from Lean core. -/
abbrev Dyadic' := Subtype IsDyadic

namespace Dyadic'

theorem le_def {x y : Dyadic'} : x ≤ y ↔ x.1 ≤ y.1 := .rfl
theorem lt_def {x y : Dyadic'} : x < y ↔ x.1 < y.1 := .rfl

/-- Numerator of a dyadic number. -/
abbrev num (x : Dyadic') : ℤ := x.1.num
/-- Denominator of a dyadic number. -/
abbrev den (x : Dyadic') : ℕ := x.1.den

theorem den_ne_zero (x : Dyadic') : x.den ≠ 0 := x.1.den_ne_zero
theorem den_pos (x : Dyadic') : 0 < x.den := x.1.den_pos
theorem den_mem_powers (x : Dyadic') : x.den ∈ Submonoid.powers 2 := x.2
theorem one_le_den (x : Dyadic') : 1 ≤ x.den := x.den_pos

@[simp]
theorem den_le_one_iff_eq_one {x : Dyadic'} : x.den ≤ 1 ↔ x.den = 1 := by
  simp_rw [Nat.le_one_iff_eq_zero_or_eq_one, x.den_ne_zero, false_or]

@[simp]
theorem one_lt_den_iff_ne_one {x : Dyadic'} : 1 < x.den ↔ x.den ≠ 1 := by
  simp [← den_le_one_iff_eq_one]

theorem den_ne_one_of_den_lt {x y : Dyadic'} (h : x.den < y.den) : y.den ≠ 1 := by
  simpa using (one_le_den x).trans_lt h

@[ext] theorem ext {x y : Dyadic'} (h : x.val = y.val) : x = y := Subtype.ext h

instance : NatCast Dyadic' where
  natCast n := ⟨n, .natCast n⟩

@[simp, norm_cast] theorem val_natCast (n : ℕ) : (n : Dyadic').val = n := rfl
@[simp, norm_cast] theorem num_natCast (n : ℕ) : (n : Dyadic').num = n := rfl
@[simp, norm_cast] theorem den_natCast (n : ℕ) : (n : Dyadic').den = 1 := rfl

@[simp] theorem val_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : Dyadic').val = n := rfl
@[simp] theorem num_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : Dyadic').num = n := rfl
@[simp] theorem den_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : Dyadic').den = 1 := rfl

@[simp, norm_cast] theorem natCast_lt_val {x : ℕ} {y : Dyadic'} : x < y.1 ↔ x < y := .rfl
@[simp, norm_cast] theorem natCast_le_val {x : ℕ} {y : Dyadic'} : x ≤ y.1 ↔ x ≤ y := .rfl
@[simp, norm_cast] theorem val_lt_natCast {x : Dyadic'} {y : ℕ} : x.1 < y ↔ x < y := .rfl
@[simp, norm_cast] theorem val_le_natCast {x : Dyadic'} {y : ℕ} : x.1 ≤ y ↔ x ≤ y := .rfl

@[simp, norm_cast] theorem val_eq_natCast {x : Dyadic'} {y : ℕ} : x.1 = y ↔ x = y :=
  @Subtype.val_inj _ _ x y
@[simp, norm_cast] theorem natCast_eq_val {x : ℕ} {y : Dyadic'} : x = y.1 ↔ x = y := by
  simp [eq_comm]

instance : IntCast Dyadic' where
  intCast n := ⟨n, .intCast n⟩

@[simp] theorem val_intCast (n : ℤ) : (n : Dyadic').val = n := rfl
@[simp] theorem mk_intCast {n : ℤ} (h : IsDyadic n) : (⟨n, h⟩ : Dyadic') = n := rfl
@[simp] theorem num_intCast (n : ℤ) : (n : Dyadic').num = n := rfl
@[simp] theorem den_intCast (n : ℤ) : (n : Dyadic').den = 1 := rfl

@[simp, norm_cast] theorem intCast_lt_val {x : ℤ} {y : Dyadic'} : x < y.1 ↔ x < y := .rfl
@[simp, norm_cast] theorem intCast_le_val {x : ℤ} {y : Dyadic'} : x ≤ y.1 ↔ x ≤ y := .rfl
@[simp, norm_cast] theorem val_lt_intCast {x : Dyadic'} {y : ℤ} : x.1 < y ↔ x < y := .rfl
@[simp, norm_cast] theorem val_le_intCast {x : Dyadic'} {y : ℤ} : x.1 ≤ y ↔ x ≤ y := .rfl
@[simp, norm_cast] theorem val_eq_intCast {x : Dyadic'} {y : ℤ} : x.1 = y ↔ x = y :=
  @Subtype.val_inj _ _ x y
@[simp, norm_cast] theorem intCast_eq_val {x : ℤ} {y : Dyadic'} : x = y.1 ↔ x = y := by
  simp [eq_comm]

instance : Zero Dyadic' where
  zero := (0 : ℕ)

instance : Inhabited Dyadic' := ⟨0⟩

@[simp, norm_cast] theorem val_zero : (0 : Dyadic').val = 0 := rfl
@[simp] theorem mk_zero (h : IsDyadic 0) : (⟨0, h⟩ : Dyadic') = 0 := rfl
@[simp] theorem num_zero : (0 : Dyadic').num = 0 := rfl
@[simp] theorem den_zero : (0 : Dyadic').den = 1 := rfl

@[simp, norm_cast] theorem zero_lt_val {x : Dyadic'} : 0 < x.1 ↔ 0 < x := .rfl
@[simp, norm_cast] theorem zero_le_val {x : Dyadic'} : 0 ≤ x.1 ↔ 0 ≤ x := .rfl
@[simp, norm_cast] theorem val_lt_zero {x : Dyadic'} : x.1 < 0 ↔ x < 0 := .rfl
@[simp, norm_cast] theorem val_le_zero {x : Dyadic'} : x.1 ≤ 0 ↔ x ≤ 0 := .rfl
@[simp, norm_cast] theorem val_eq_zero {x : Dyadic'} : x.1 = 0 ↔ x = 0 := val_eq_intCast
@[simp, norm_cast] theorem zero_eq_val {x : Dyadic'} : 0 = x.1 ↔ 0 = x := intCast_eq_val

instance : One Dyadic' where
  one := (1 : ℕ)

@[simp, norm_cast] theorem val_one : (1 : Dyadic').val = 1 := rfl
@[simp] theorem mk_one (h : IsDyadic 1) : (⟨1, h⟩ : Dyadic') = 1 := rfl
@[simp] theorem num_one : (1 : Dyadic').num = 1 := rfl
@[simp] theorem den_one : (1 : Dyadic').den = 1 := rfl

@[simp, norm_cast] theorem one_lt_val {x : Dyadic'} : 1 < x.1 ↔ 1 < x := .rfl
@[simp, norm_cast] theorem one_le_val {x : Dyadic'} : 1 ≤ x.1 ↔ 1 ≤ x := .rfl
@[simp, norm_cast] theorem val_lt_one {x : Dyadic'} : x.1 < 1 ↔ x < 1 := .rfl
@[simp, norm_cast] theorem val_le_one {x : Dyadic'} : x.1 ≤ 1 ↔ x ≤ 1 := .rfl
@[simp, norm_cast] theorem val_eq_one {x : Dyadic'} : x.1 = 1 ↔ x = 1 := val_eq_intCast
@[simp, norm_cast] theorem one_eq_val {x : Dyadic'} : 1 = x.1 ↔ 1 = x := intCast_eq_val

instance : Nontrivial Dyadic' where
  exists_pair_ne := ⟨0, 1, by decide⟩

instance : Neg Dyadic' where
  neg x := ⟨_, x.2.neg⟩

@[simp] theorem val_neg (x : Dyadic') : (-x).val = -x.val := rfl
@[simp] theorem neg_mk {x : ℚ} (hx : IsDyadic x) : -(⟨x, hx⟩ : Dyadic') = ⟨-x, hx.neg⟩ := rfl
@[simp] theorem num_neg (x : Dyadic') : (-x).num = -x.num := rfl
@[simp] theorem den_neg (x : Dyadic') : (-x).den = x.den := rfl

instance : Add Dyadic' where
  add x y := ⟨_, x.2.add y.2⟩

@[simp] theorem val_add (x y : Dyadic') : (x + y).val = x.val + y.val := rfl

instance : Sub Dyadic' where
  sub x y := ⟨_, x.2.sub y.2⟩

@[simp] theorem val_sub (x y : Dyadic') : (x - y).val = x.val - y.val := rfl

instance : Mul Dyadic' where
  mul x y := ⟨_, x.2.mul y.2⟩

@[simp] theorem val_mul (x y : Dyadic') : (x * y).val = x.val * y.val := rfl

instance : SMul Nat Dyadic' where
  smul x y := ⟨_, y.2.nsmul x⟩

@[simp] theorem val_nsmul (x : ℕ) (y : Dyadic') : (x • y).val = x • y.val := rfl

instance : SMul Int Dyadic' where
  smul x y := ⟨_, y.2.zsmul x⟩

@[simp] theorem val_zsmul (x : ℤ) (y : Dyadic') : (x • y).val = x • y.val := rfl

instance : NatPow Dyadic' where
  pow x y := ⟨_, x.2.pow y⟩

@[simp] theorem val_pow (x : Dyadic') (y : ℕ) : (x ^ y).val = x.val ^ y := rfl

/-- The dyadic number ½. -/
def half : Dyadic' := ⟨2⁻¹, ⟨1, by simp⟩⟩

@[simp] theorem val_half : half.val = 2⁻¹ := rfl
@[simp] theorem num_half : half.num = 1 := show ((2 : ℚ)⁻¹).num = 1 by simp
@[simp] theorem num_den : half.den = 2 := show ((2 : ℚ)⁻¹).den = 2 by simp

/-- Constructor for the fraction `m / n`. -/
protected def mkRat (m : ℤ) {n : ℕ} (h : n ∈ Submonoid.powers 2) : Dyadic' :=
  ⟨mkRat m n, .mkRat m h⟩

@[simp]
theorem val_mkRat (m : ℤ) {n : ℕ} (h : n ∈ Submonoid.powers 2) :
    (Dyadic'.mkRat m h).val = mkRat m n :=
  rfl

@[simp] theorem mkRat_self (x : Dyadic') : Dyadic'.mkRat x.num x.2 = x := by ext; simp

@[simp]
theorem mkRat_one (m : ℤ) (h : 1 ∈ Submonoid.powers 2) : Dyadic'.mkRat m h = m := by
  ext; exact Rat.mkRat_one ..

@[simp]
theorem mkRat_lt_mkRat {m n : ℤ} {k : ℕ} (h₁ h₂ : k ∈ Submonoid.powers 2) :
    Dyadic'.mkRat m h₁ < Dyadic'.mkRat n h₂ ↔ m < n := by
  simp_rw [Dyadic'.mkRat, Rat.mkRat_eq_div]
  rw [Subtype.mk_lt_mk, div_lt_div_iff_of_pos_right (mod_cast pos_of_mem_powers h₁), Int.cast_lt]

@[simp]
theorem mkRat_le_mkRat {m n : ℤ} {k : ℕ} (h₁ h₂ : k ∈ Submonoid.powers 2) :
    Dyadic'.mkRat m h₁ ≤ Dyadic'.mkRat n h₂ ↔ m ≤ n :=
  le_iff_le_iff_lt_iff_lt.2 (mkRat_lt_mkRat h₁ h₂)

theorem mkRat_add_mkRat_self {m n : ℤ} {k : ℕ} (h₁ h₂ : k ∈ Submonoid.powers 2) :
    Dyadic'.mkRat m h₁ + Dyadic'.mkRat n h₂ = .mkRat (m + n) h₁ := by
  ext; simp [Rat.mkRat_eq_div, add_div]

instance : CommRing Dyadic' where
  add_assoc x y z := by ext; simp [add_assoc]
  zero_add x := by ext; simp
  add_zero x := by ext; simp
  add_comm x y := by ext; simp [add_comm]
  mul_comm x y := by ext; simp [mul_comm]
  left_distrib x y z := by ext; simp [mul_add]
  right_distrib x y z := by ext; simp [add_mul]
  zero_mul x := by ext; simp
  mul_zero x := by ext; simp
  mul_assoc x y z := by ext; simp [mul_assoc]
  one_mul x := by ext; simp
  mul_one x := by ext; simp
  neg_add_cancel x := by ext; simp
  sub_eq_add_neg x y := by ext; simp [sub_eq_add_neg]
  natCast_succ n := by ext; simp
  nsmul n x := n • x
  nsmul_zero x := by ext; simp
  nsmul_succ n x := by ext; simp [add_one_mul]
  zsmul n x := n • x
  zsmul_zero' x := by ext; simp
  zsmul_succ' n x := by ext; simp [add_one_mul]
  zsmul_neg' n x := by ext; simp [add_mul]
  npow n x := x ^ n
  npow_succ n x := by ext; simp [pow_succ]

instance : IsStrictOrderedRing Dyadic' where
  add_le_add_left x y h z := add_le_add_left (α := ℚ) h z
  le_of_add_le_add_left x y z := le_of_add_le_add_left (α := ℚ)
  mul_lt_mul_of_pos_left x y z := mul_lt_mul_of_pos_left (α := ℚ)
  mul_lt_mul_of_pos_right x y z := mul_lt_mul_of_pos_right (α := ℚ)
  zero_le_one := by decide

instance : DenselyOrdered Dyadic' where
  dense x y h := by
    use half * (x + y)
    simp_rw [lt_def] at *
    constructor
    · simpa [inv_mul_eq_div] using left_lt_add_div_two.2 h
    · simpa [inv_mul_eq_div] using add_div_two_lt_right.2 h

instance : Archimedean Dyadic' where
  arch x _ h :=
    have ⟨n, hn⟩ := exists_lt_nsmul (M := ℚ) h x
    ⟨n, hn.le⟩

theorem even_den {x : Dyadic} (hx : x.den ≠ 1) : Even x.den := by
  obtain ⟨n, hn⟩ := x.den_mem_powers
  rw [← hn]
  cases n
  · simp_all
  · rw [even_iff_two_dvd]
    exact dvd_mul_left ..

theorem odd_num {x : Dyadic'} (hx : x.den ≠ 1) : Odd x.num := by
  rw [← Int.not_even_iff_odd]
  have hd := even_den hx
  rw [even_iff_two_dvd] at *
  rw [← Int.natAbs_dvd_natAbs]
  exact (Nat.not_coprime_of_dvd_of_dvd one_lt_two · hd x.1.reduced)

theorem intCast_num_eq_self_of_den_eq_one {x : Dyadic'} (hx : x.den = 1) : x.num = x := by
  ext
  exact Rat.coe_int_num_of_den_eq_one hx

theorem den_mkRat_le (x : ℤ) {n : ℕ} (hn : n ≠ 0) : (mkRat x n).den ≤ n := by
  rw [← Rat.normalize_eq_mkRat hn, Rat.normalize_eq hn]
  exact Nat.div_le_self n _

theorem den_mkRat_lt {x : Dyadic'} {n : ℤ} (hn : 2 ∣ n) (hd : x.den ≠ 1) :
    (mkRat n x.den).den < x.den := by
  rw [← Rat.normalize_eq_mkRat x.den_ne_zero, Rat.normalize_eq]
  apply Nat.div_lt_self x.den_pos
  apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ x.den_pos) (Nat.dvd_gcd _ (even_den hd).two_dvd)
  rwa [← Int.natAbs_dvd_natAbs] at hn

theorem den_add_self_lt {x : Dyadic'} (hx : x.den ≠ 1) : (x + x).den < x.den := by
  suffices x + x = Dyadic'.mkRat (2 * x.num) x.den_mem_powers from
    this ▸ den_mkRat_lt (Int.dvd_mul_right 2 x.num) hx
  ext
  simp [Rat.mkRat_eq_div, Rat.num_div_den, mul_div_assoc, ← two_mul]

theorem eq_mkRat_of_den_le {x : Dyadic'} {n : ℕ} (h : x.den ≤ n) (hn : n ∈ Submonoid.powers 2) :
    ∃ m, x = .mkRat m hn := by
  use x.num * (n / x.den)
  ext
  rw [← x.mkRat_self, val_mkRat, val_mkRat,
    Rat.mkRat_eq_iff x.den_ne_zero (ne_zero_of_mem_powers hn), mkRat_self, mul_assoc]
  congr
  exact (Nat.div_mul_cancel ((dvd_iff_le_of_mem_powers x.den_mem_powers hn).2 h)).symm

instance : CanLift Dyadic' Int Int.cast (·.1.den = 1) where
  prf x hx := ⟨x.1.num, Dyadic'.ext (x.1.den_eq_one_iff.mp hx)⟩

theorem den_add_le_den_right {x y : Dyadic'} (h : x.den ≤ y.den) : (x + y).den ≤ y.den := by
  obtain ⟨n, hn⟩ := eq_mkRat_of_den_le h y.den_mem_powers
  conv_lhs => rw [← y.mkRat_self, hn, mkRat_add_mkRat_self]
  exact den_mkRat_le _ y.den_ne_zero

/-- Coercion as a `RingHom`. -/
@[simps]
def coeRingHom : Dyadic' →+* ℚ where
  toFun := (↑)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end Dyadic'
