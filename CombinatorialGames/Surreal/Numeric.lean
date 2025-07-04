/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Short
import CombinatorialGames.Surreal.Division
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Int

/-!
# Dyadic games

A combinatorial game that is both `Short` and `Numeric` is called dyadic. We show that the dyadic
games are in correspondence with the `Dyadic` rationals, in the sense that there exists a map
`Dyadic.toIGame` such that:

- `Dyadic.toIGame x` is always a dyadic game.
- For any dyadic game `y`, there exists `x` with `Dyadic.toIGame x ≈ y`.
- The game `Dyadic.toGame x` is equivalent to the `RatCast` of `x`.

## Todo

Prove the second bullet point.
-/

universe u
open IGame

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

/-! ### Dyadic numbers

This material belongs in Mathlib, though we do need to consider if the definition of `Dyadic` used
here is the best one. -/

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
us to talk about numerators and denominators. -/
abbrev Dyadic := Subtype IsDyadic

namespace Dyadic

/-- Numerator of a dyadic number. -/
abbrev num (x : Dyadic) : ℤ := x.1.num
/-- Denominator of a dyadic number. -/
abbrev den (x : Dyadic) : ℕ := x.1.den

theorem den_ne_zero (x : Dyadic) : x.den ≠ 0 := x.1.den_ne_zero
theorem den_pos (x : Dyadic) : 0 < x.den := x.1.den_pos
theorem den_mem_powers (x : Dyadic) : x.den ∈ Submonoid.powers 2 := x.2
theorem one_le_den (x : Dyadic) : 1 ≤ x.den := x.den_pos

@[simp]
theorem den_le_one_iff_eq_one {x : Dyadic} : x.den ≤ 1 ↔ x.den = 1 := by
  simp_rw [Nat.le_one_iff_eq_zero_or_eq_one, x.den_ne_zero, false_or]

@[simp]
theorem one_lt_den_iff_ne_one {x : Dyadic} : 1 < x.den ↔ x.den ≠ 1 := by
  simp [← den_le_one_iff_eq_one]

theorem den_ne_one_of_den_lt {x y : Dyadic} (h : x.den < y.den) : y.den ≠ 1 := by
  simpa using (one_le_den x).trans_lt h

@[ext] theorem ext {x y : Dyadic} (h : x.val = y.val) : x = y := Subtype.ext h

instance : NatCast Dyadic where
  natCast n := ⟨n, .natCast n⟩

@[simp] theorem val_natCast (n : ℕ) : (n : Dyadic).val = n := rfl
@[simp] theorem num_natCast (n : ℕ) : (n : Dyadic).num = n := rfl
@[simp] theorem den_natCast (n : ℕ) : (n : Dyadic).den = 1 := rfl

@[simp] theorem val_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : Dyadic).val = n := rfl
@[simp] theorem num_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : Dyadic).num = n := rfl
@[simp] theorem den_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : Dyadic).den = 1 := rfl

instance : IntCast Dyadic where
  intCast n := ⟨n, .intCast n⟩

@[simp] theorem val_intCast (n : ℤ) : (n : Dyadic).val = n := rfl
@[simp] theorem mk_intCast {n : ℤ} (h : IsDyadic n) : (⟨n, h⟩ : Dyadic) = n := rfl
@[simp] theorem num_intCast (n : ℤ) : (n : Dyadic).num = n := rfl
@[simp] theorem den_intCast (n : ℤ) : (n : Dyadic).den = 1 := rfl

instance : Zero Dyadic where
  zero := (0 : ℕ)

@[simp] theorem val_zero : (0 : Dyadic).val = 0 := rfl
@[simp] theorem mk_zero (h : IsDyadic 0) : (⟨0, h⟩ : Dyadic) = 0 := rfl
@[simp] theorem num_zero : (0 : Dyadic).num = 0 := rfl
@[simp] theorem den_zero : (0 : Dyadic).den = 1 := rfl

instance : One Dyadic where
  one := (1 : ℕ)

@[simp] theorem val_one : (1 : Dyadic).val = 1 := rfl
@[simp] theorem mk_one (h : IsDyadic 1) : (⟨1, h⟩ : Dyadic) = 1 := rfl
@[simp] theorem num_one : (1 : Dyadic).num = 1 := rfl
@[simp] theorem den_one : (1 : Dyadic).den = 1 := rfl

instance : Nontrivial Dyadic where
  exists_pair_ne := ⟨0, 1, by decide⟩

instance : Neg Dyadic where
  neg x := ⟨_, x.2.neg⟩

@[simp] theorem val_neg (x : Dyadic) : (-x).val = -x.val := rfl
@[simp] theorem neg_mk {x : ℚ} (hx : IsDyadic x) : -(⟨x, hx⟩ : Dyadic) = ⟨-x, hx.neg⟩ := rfl
@[simp] theorem num_neg (x : Dyadic) : (-x).num = -x.num := rfl
@[simp] theorem den_neg (x : Dyadic) : (-x).den = x.den := rfl

instance : Add Dyadic where
  add x y := ⟨_, x.2.add y.2⟩

@[simp] theorem val_add (x y : Dyadic) : (x + y).val = x.val + y.val := rfl

instance : Sub Dyadic where
  sub x y := ⟨_, x.2.sub y.2⟩

@[simp] theorem val_sub (x y : Dyadic) : (x - y).val = x.val - y.val := rfl

instance : Mul Dyadic where
  mul x y := ⟨_, x.2.mul y.2⟩

@[simp] theorem val_mul (x y : Dyadic) : (x * y).val = x.val * y.val := rfl

instance : SMul Nat Dyadic where
  smul x y := ⟨_, y.2.nsmul x⟩

@[simp] theorem val_nsmul (x : ℕ) (y : Dyadic) : (x • y).val = x • y.val := rfl

instance : SMul Int Dyadic where
  smul x y := ⟨_, y.2.zsmul x⟩

@[simp] theorem val_zsmul (x : ℤ) (y : Dyadic) : (x • y).val = x • y.val := rfl

instance : NatPow Dyadic where
  pow x y := ⟨_, x.2.pow y⟩

@[simp] theorem val_pow (x : Dyadic) (y : ℕ) : (x ^ y).val = x.val ^ y := rfl

/-- The dyadic number ½. -/
def half : Dyadic := ⟨2⁻¹, ⟨1, by simp⟩⟩

@[simp] theorem val_half : half.val = 2⁻¹ := rfl
@[simp] theorem num_half : half.num = 1 := show ((2 : ℚ)⁻¹).num = 1 by simp
@[simp] theorem num_den : half.den = 2 := show ((2 : ℚ)⁻¹).den = 2 by simp

/-- Constructor for the fraction `m / n`. -/
protected def mkRat (m : ℤ) {n : ℕ} (h : n ∈ Submonoid.powers 2) : Dyadic :=
  ⟨mkRat m n, .mkRat m h⟩

@[simp]
theorem val_mkRat (m : ℤ) {n : ℕ} (h : n ∈ Submonoid.powers 2) :
    (Dyadic.mkRat m h).val = mkRat m n :=
  rfl

@[simp] theorem mkRat_self (x : Dyadic) : Dyadic.mkRat x.num x.2 = x := by ext; simp

@[simp]
theorem mkRat_one (m : ℤ) (h : 1 ∈ Submonoid.powers 2) : Dyadic.mkRat m h = m := by
  ext; simp

@[simp]
theorem mkRat_lt_mkRat {m n : ℤ} {k : ℕ} (h₁ h₂ : k ∈ Submonoid.powers 2) :
    Dyadic.mkRat m h₁ < Dyadic.mkRat n h₂ ↔ m < n := by
  simp_rw [Dyadic.mkRat, Rat.mkRat_eq_div]
  rw [Subtype.mk_lt_mk, div_lt_div_iff_of_pos_right (mod_cast pos_of_mem_powers h₁), Int.cast_lt]

@[simp]
theorem mkRat_le_mkRat {m n : ℤ} {k : ℕ} (h₁ h₂ : k ∈ Submonoid.powers 2) :
    Dyadic.mkRat m h₁ ≤ Dyadic.mkRat n h₂ ↔ m ≤ n :=
  le_iff_le_iff_lt_iff_lt.2 (mkRat_lt_mkRat h₁ h₂)

theorem mkRat_add_mkRat_self {m n : ℤ} {k : ℕ} (h₁ h₂ : k ∈ Submonoid.powers 2) :
    Dyadic.mkRat m h₁ + Dyadic.mkRat n h₂ = .mkRat (m + n) h₁ := by
  ext; simp [Rat.mkRat_eq_div, div_add_div_same]

instance : CommRing Dyadic where
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
  zsmul n x := n • x
  npow n x := x ^ n
  npow_succ n x := by ext; simp [pow_succ]

instance : IsStrictOrderedRing Dyadic where
  add_le_add_left x y h z := add_le_add_left (α := ℚ) h z
  le_of_add_le_add_left x y z := le_of_add_le_add_left (α := ℚ)
  mul_lt_mul_of_pos_left x y z := mul_lt_mul_of_pos_left (α := ℚ)
  mul_lt_mul_of_pos_right x y z := mul_lt_mul_of_pos_right (α := ℚ)
  zero_le_one := by decide

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

private theorem den_mkRat_le (x : ℤ) {n : ℕ} (hn : n ≠ 0) : (mkRat x n).den ≤ n := by
  rw [← Rat.normalize_eq_mkRat hn, Rat.normalize_eq hn]
  exact Nat.div_le_self n _

private theorem den_mkRat_lt {x : Dyadic} {n : ℤ} (hn : 2 ∣ n) (hd : x.den ≠ 1) :
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

/-! ### Dyadic games -/

/-- For a dyadic number `m / n`, returns `(m - 1) / n`. -/
def lower (x : Dyadic) : Dyadic :=
  .mkRat (x.num - 1) x.2

/-- For a dyadic number `m / n`, returns `(m + 1) / n`. -/
def upper (x : Dyadic) : Dyadic :=
  .mkRat (x.num + 1) x.2

theorem den_lower_lt {x : Dyadic} (h : x.den ≠ 1) : (lower x).den < x.den :=
  den_mkRat_lt ((odd_num h).sub_odd odd_one).two_dvd h

theorem den_upper_lt {x : Dyadic} (h : x.den ≠ 1) : (upper x).den < x.den :=
  den_mkRat_lt ((odd_num h).add_odd odd_one).two_dvd h

/-- An auxiliary tactic for inducting on the denominator of a `Dyadic`. -/
macro "dyadic_wf" : tactic =>
  `(tactic| all_goals first | solve_by_elim
    [Prod.Lex.left, Prod.Lex.right, den_lower_lt, den_upper_lt] | decreasing_tactic)

@[simp]
theorem lower_neg (x : Dyadic) : lower (-x) = -upper x := by
  unfold lower upper
  ext
  simp [Rat.neg_mkRat, ← sub_eq_neg_add]

@[simp]
theorem upper_neg (x : Dyadic) : upper (-x) = -lower x := by
  unfold lower upper
  ext
  simp [Rat.neg_mkRat, ← sub_eq_neg_add]

theorem le_lower_of_lt {x y : Dyadic} (hd : x.den ≤ y.den) (h : x < y) : x ≤ y.lower := by
  obtain ⟨m, rfl⟩ := eq_mkRat_of_den_le hd y.den_mem_powers
  conv_rhs at h => rw [← y.mkRat_self]
  rw [mkRat_lt_mkRat] at h
  rwa [lower, mkRat_le_mkRat, Int.le_sub_one_iff]

theorem upper_le_of_lt {x y : Dyadic} (hd : y.den ≤ x.den) (h : x < y) : x.upper ≤ y := by
  have hd' : (-y).den ≤ (-x).den := hd
  simpa using le_lower_of_lt hd' (neg_lt_neg h)

theorem lower_eq_of_den_eq_one {x : Dyadic} (h : x.den = 1) : lower x = x.num - 1 := by
  simp [lower, h]

theorem upper_eq_of_den_eq_one {x : Dyadic} (h : x.den = 1) : upper x = x.num + 1 := by
  simp [upper, h]

theorem lower_lt (x : Dyadic) : lower x < x := by
  conv_rhs => rw [← x.mkRat_self]
  rw [lower, mkRat_lt_mkRat]
  exact sub_one_lt x.num

theorem lt_upper (x : Dyadic) : x < upper x := by
  simpa using lower_lt (-x)

theorem lower_lt_upper (x : Dyadic) : lower x < upper x :=
  (lower_lt x).trans (lt_upper x)

theorem val_lower (x : Dyadic) : (lower x).val = x - (x.den : ℚ)⁻¹ := by
  simp [lower, Rat.mkRat_eq_div, sub_div, Rat.num_div_den]

theorem val_upper (x : Dyadic) : (upper x).val = x + (x.den : ℚ)⁻¹ := by
  simp [upper, Rat.mkRat_eq_div, add_div, Rat.num_div_den]

theorem lower_add_le_of_den_le {x y : Dyadic} (h : x.den ≤ y.den) :
    lower (x + y) ≤ x + lower y := by
  rw [Subtype.mk_le_mk]
  suffices (y.den : ℚ)⁻¹ ≤ ((x + y).den : ℚ)⁻¹ by simpa [val_lower, add_assoc, sub_eq_add_neg]
  rw [inv_le_inv₀ (mod_cast y.den_pos) (mod_cast den_pos _)]
  exact_mod_cast den_add_le_den_right h

theorem lower_add_le_of_den_ge {x y : Dyadic} (h : y.den ≤ x.den) :
    lower (x + y) ≤ lower x + y := by
  simpa [add_comm] using lower_add_le_of_den_le h

theorem le_upper_add_of_den_le {x y : Dyadic} (h : x.den ≤ y.den) :
    x + upper y ≤ upper (x + y) := by
  simpa only [← neg_add, lower_neg, neg_le_neg_iff] using @lower_add_le_of_den_le (-x) (-y) h

theorem le_upper_add_of_den_ge {x y : Dyadic} (h : y.den ≤ x.den) :
    upper x + y ≤ upper (x + y) := by
  simpa [add_comm] using le_upper_add_of_den_le h

/-- Converts a dyadic rational into an `IGame`. This map is defined so that:

* If `x : ℤ`, then `toIGame x = ↑x`.
* Otherwise, if `x = m / n` with `n` even, then `toIGame x = {(m - 1) / n | (m + 1) / n}ᴵ`. Note
  that both options will have smaller denominators. -/
noncomputable def toIGame (x : Dyadic) : IGame :=
  if _ : x.den = 1 then x.num else {{toIGame (lower x)} | {toIGame (upper x)}}ᴵ
termination_by x.den
decreasing_by dyadic_wf

theorem toIGame_of_den_eq_one {x : Dyadic} (hx : x.den = 1) : toIGame x = x.num := by
  rw [toIGame, dif_pos hx]

@[simp] theorem toIGame_intCast (n : ℤ) : toIGame n = n := toIGame_of_den_eq_one rfl
@[simp] theorem toIGame_natCast (n : ℕ) : toIGame n = n := toIGame_intCast n

@[simp] theorem toIGame_zero : toIGame 0 = 0 := toIGame_natCast 0
@[simp] theorem toIGame_one : toIGame 1 = 1 := by simpa using toIGame_natCast 1

theorem toIGame_of_den_ne_one {x : Dyadic} (hx : x.den ≠ 1) :
    toIGame x = {{toIGame (lower x)} | {toIGame (upper x)}}ᴵ :=
  by rw [toIGame, dif_neg hx]

@[simp]
theorem toIGame_half : toIGame half = ½ := by
  have : mkRat 2 2 = 1 := rfl
  rw [toIGame_of_den_ne_one] <;> aesop (add simp [lower, upper, Dyadic.mkRat])

@[simp]
theorem toIGame_neg (x : Dyadic) : toIGame (-x) = -toIGame x := by
  unfold toIGame
  dsimp
  split_ifs with h
  · simp
  · simpa using ⟨toIGame_neg _, toIGame_neg _⟩
termination_by x.den
decreasing_by dyadic_wf

theorem eq_lower_of_mem_leftMoves_toIGame {x : Dyadic} {y : IGame}
    (h : y ∈ (toIGame x).leftMoves) : y = toIGame (lower x) := by
  by_cases hx : x.den = 1
  · rw [toIGame_of_den_eq_one hx] at h
    rw [lower_eq_of_den_eq_one hx, eq_sub_one_of_mem_leftMoves_intCast h,
      ← Int.cast_one (R := Dyadic), ← Int.cast_sub, toIGame_intCast]
  · simpa [toIGame_of_den_ne_one hx] using h

theorem eq_upper_of_mem_rightMoves_toIGame {x : Dyadic} {y : IGame}
    (h : y ∈ (toIGame x).rightMoves) : y = toIGame (upper x) := by
  have : -y ∈ (toIGame (-x)).leftMoves := by simpa
  simpa using eq_lower_of_mem_leftMoves_toIGame this

/-- A dyadic number `x` is always equivalent to `{lower x | upper x}ᴵ`, though this may not
necessarily be the canonical form. -/
theorem toIGame_equiv_lower_upper (x : Dyadic) :
    toIGame x ≈ {{toIGame (lower x)} | {toIGame (upper x)}}ᴵ := by
  rw [toIGame]
  split_ifs with h
  · unfold lower upper
    simp only [Dyadic.mkRat, Rat.mkRat_one, mk_intCast, toIGame_intCast, h]
    apply Fits.equiv_of_forall_not_fits
    · simp [Fits]
    · intro m hm
      obtain ⟨m, hm', rfl⟩ := eq_intCast_of_mem_leftMoves_intCast hm
      simp_all [Fits, Int.sub_one_lt_iff]
    · intro m hm
      obtain ⟨m, hm', rfl⟩ := eq_intCast_of_mem_rightMoves_intCast hm
      simp_all [Fits, Int.lt_add_one_iff]
  · rfl

instance _root_.IGame.Short.dyadic (x : Dyadic) : Short (toIGame x) := by
  rw [toIGame]
  split_ifs with h
  · exact .intCast _
  · rw [short_def]
    simpa using ⟨.dyadic _, .dyadic _⟩
termination_by x.den
decreasing_by dyadic_wf

private theorem numeric_lower (x : Dyadic) [hx : Numeric (toIGame.{u} x)] :
    Numeric (toIGame.{u} (lower x)) := by
  by_cases h : x.den = 1
  · rw [lower_eq_of_den_eq_one h, ← Int.cast_one, ← Int.cast_sub, toIGame_intCast]
    infer_instance
  · apply hx.of_mem_leftMoves
    simp [toIGame_of_den_ne_one h]

private theorem numeric_upper (x : Dyadic) [hx : Numeric (toIGame.{u} x)] :
    Numeric (toIGame.{u} (upper x)) := by
  have : Numeric (toIGame.{u} (-x)) := by simpa
  simpa using numeric_lower (-x)

private theorem lower_lt_aux (x : Dyadic) [hx : Numeric (toIGame.{u} x)] :
    toIGame.{u} (lower x) < toIGame x := by
  by_cases h : x.den = 1
  · rw [lower_eq_of_den_eq_one h, ← Int.cast_one, ← Int.cast_sub, toIGame_intCast,
      toIGame_of_den_eq_one h]
    simp
  · apply hx.leftMove_lt
    simp [toIGame_of_den_ne_one h]

private theorem lt_upper_aux (x : Dyadic) [hx : Numeric (toIGame.{u} x)] :
    toIGame.{u} (x) < toIGame (upper x) := by
  have : Numeric (toIGame.{u} (-x)) := by simpa
  simpa using lower_lt_aux (-x)

private theorem toIGame_lt_toIGame_aux {x y : Dyadic}
    [Numeric (toIGame.{u} x)] [Numeric (toIGame.{u} y)] (h : x < y) :
    toIGame.{u} x < toIGame y := by
  by_cases H : x.den = 1 ∧ y.den = 1
  · rwa [toIGame_of_den_eq_one H.1, toIGame_of_den_eq_one H.2, intCast_lt,
      ← Int.cast_lt (R := Dyadic), intCast_num_eq_self_of_den_eq_one H.1, intCast_num_eq_self_of_den_eq_one H.2]
  · obtain hd | hd := le_total x.den y.den
    · have := numeric_lower y
      have hy := lower_lt_aux y
      by_cases hy' : y.den = 1
      · rw [hy', den_le_one_iff_eq_one] at hd
        exact (H ⟨hd, hy'⟩).elim
      · exact (le_of_le_of_lt_of_lt toIGame_lt_toIGame_aux (le_lower_of_lt hd h)).trans_lt hy
    · have := numeric_upper x
      have hx := lt_upper_aux x
      by_cases hx' : x.den = 1
      · rw [hx', den_le_one_iff_eq_one] at hd
        exact (H ⟨hx', hd⟩).elim
      · exact hx.trans_le (le_of_le_of_lt_of_lt toIGame_lt_toIGame_aux (upper_le_of_lt hd h))
termination_by (x.den, y.den)
decreasing_by dyadic_wf

instance _root_.IGame.Numeric.dyadic (x : Dyadic) : Numeric (toIGame x) := by
  by_cases h : x.den = 1
  · rw [toIGame_of_den_eq_one h]
    infer_instance
  · rw [numeric_def, toIGame_of_den_ne_one h]
    have := IGame.Numeric.dyadic (lower x)
    have := IGame.Numeric.dyadic (upper x)
    have := toIGame_lt_toIGame_aux (lower_lt_upper x)
    simp_all
termination_by x.den
decreasing_by dyadic_wf

/-- `Dyadic.toIGame` as an `OrderEmbedding`. -/
@[simps!]
noncomputable def toIGameEmbedding : Dyadic ↪o IGame :=
  .ofStrictMono toIGame fun _ _ ↦ toIGame_lt_toIGame_aux

@[simp]
theorem toIGame_le_toIGame {x y : Dyadic} : toIGame x ≤ toIGame y ↔ x ≤ y :=
  toIGameEmbedding.le_iff_le

@[simp]
theorem toIGame_lt_toIGame {x y : Dyadic} : toIGame x < toIGame y ↔ x < y :=
  toIGameEmbedding.lt_iff_lt

@[simp]
theorem toIGame_equiv_toIGame {x y : Dyadic} : toIGame x ≈ toIGame y ↔ x = y := by
  simp [AntisymmRel, le_antisymm_iff]

@[simp]
theorem toIGame_inj {x y : Dyadic} : toIGame x = toIGame y ↔ x = y :=
  toIGameEmbedding.inj

theorem toIGame_add_equiv (x y : Dyadic) : toIGame.{u} (x + y) ≈ toIGame x + toIGame y := by
  by_cases H : x.den = 1 ∧ y.den = 1
  · rw [← intCast_num_eq_self_of_den_eq_one H.1, ← intCast_num_eq_self_of_den_eq_one H.2]
    simpa [← Int.cast_add] using intCast_add_equiv ..
  apply Fits.equiv_of_forall_not_fits
  · rw [Fits, forall_leftMoves_add, forall_rightMoves_add]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro z hz
    any_goals
      obtain rfl := eq_lower_of_mem_leftMoves_toIGame hz
      rw [← (toIGame_add_equiv _ _).le_congr_right]
      simpa using lower_lt _
    all_goals
      obtain rfl := eq_upper_of_mem_rightMoves_toIGame hz
      rw [← (toIGame_add_equiv _ _).le_congr_left]
      simpa using lt_upper _
  · intro z hz
    obtain rfl := eq_lower_of_mem_leftMoves_toIGame hz
    rw [not_fits_iff]
    left
    obtain h | h := le_or_gt x.den y.den
    · by_cases hy : y.den = 1; simp_all
      use toIGame x + toIGame (lower y)
      have hy := toIGame_of_den_ne_one hy
      have : toIGame (lower y) ∈ (toIGame y).leftMoves := by rw [hy]; simp
      rw [← (toIGame_add_equiv ..).le_congr_right, hy]
      simpa using lower_add_le_of_den_le h
    · use toIGame (lower x) + toIGame y
      have hx := toIGame_of_den_ne_one (den_ne_one_of_den_lt h)
      have : toIGame (lower x) ∈ (toIGame x).leftMoves := by rw [hx]; simp
      rw [← (toIGame_add_equiv ..).le_congr_right, hx]
      simpa using lower_add_le_of_den_ge h.le
  · intro z hz
    obtain rfl := eq_upper_of_mem_rightMoves_toIGame hz
    rw [not_fits_iff]
    right
    obtain h | h := le_or_gt x.den y.den
    · by_cases hy : y.den = 1; simp_all
      use toIGame x + toIGame (upper y)
      have hy := toIGame_of_den_ne_one hy
      have : toIGame (upper y) ∈ (toIGame y).rightMoves := by rw [hy]; simp
      rw [← (toIGame_add_equiv ..).le_congr_left, hy]
      simpa using le_upper_add_of_den_le h
    · use toIGame (upper x) + toIGame y
      have hx := toIGame_of_den_ne_one (den_ne_one_of_den_lt h)
      have : toIGame (upper x) ∈ (toIGame x).rightMoves := by rw [hx]; simp
      rw [← (toIGame_add_equiv ..).le_congr_left, hx]
      simpa using le_upper_add_of_den_ge h.le
termination_by (toIGame.{u} x, toIGame.{u} y)
decreasing_by igame_wf

theorem toIGame_sub_equiv (x y : Dyadic) : toIGame (x - y) ≈ toIGame x - toIGame y := by
  simpa [sub_eq_add_neg] using toIGame_add_equiv x (-y)

theorem toIGame_equiv_ratCast (x : Dyadic) : toIGame x ≈ x.val := by
  by_cases h : x.den = 1
  · rw [toIGame_of_den_eq_one h, ← (ratCast_intCast_equiv _).antisymmRel_congr_left,
      Rat.coe_int_num_of_den_eq_one h]
  · have := den_add_self_lt h
    have := (toIGame_add_equiv x x).symm.trans (toIGame_equiv_ratCast (x + x))
    simp_all [← Surreal.mk_eq_mk, ← two_mul]
termination_by x.den

end Dyadic

@[simp]
theorem Game.mk_dyadic (x : Dyadic) : mk x.toIGame = x.1 :=
  Game.mk_eq x.toIGame_equiv_ratCast

@[simp]
theorem Surreal.mk_dyadic (x : Dyadic) : mk x.toIGame = x.1 := by
  simpa using Surreal.mk_eq x.toIGame_equiv_ratCast

theorem Dyadic.toIGame_mul_equiv (x y : Dyadic) : toIGame (x * y) ≈ toIGame x * toIGame y := by
  simp [← Surreal.mk_eq_mk]
