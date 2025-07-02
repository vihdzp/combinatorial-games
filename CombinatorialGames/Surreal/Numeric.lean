/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Multiplication
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Int
import Mathlib.GroupTheory.MonoidLocalization.Away

/-!
# Dyadic games

A combinatorial game that is both `Short` and `Numeric` is called dyadic. We show that the dyadic
games are in correspondence with the `Dyadic` rationals, in the sense that there exists a map
`Dyadic.toIGame` such that:

- `Dyadic.toIGame x` is always a dyadic game.
- For any dyadic game `y`, there exists `x` with `Dyadic.toIGame x ≈ y`.
- The map `Dyadic.toGame` (defined in the obvious way) is a ring homomorphism.

## Todo

Show the latter two bullet points.
-/

universe u

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

theorem IsDyadic.add {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  rw [Rat.add_def']
  exact IsDyadic.mkRat _ (Submonoid.mul_mem _ hx hy)

theorem IsDyadic.nsmul {x : ℚ} (n : ℕ) (hx : IsDyadic x) : IsDyadic (n • x) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [succ_nsmul]
    exact ih.add hx

theorem IsDyadic.zsmul {x : ℚ} (n : ℤ) (hx : IsDyadic x) : IsDyadic (n • x) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, natCast_zsmul]
    exact hx.nsmul n
  | negSucc n =>
    rw [negSucc_zsmul]
    exact (hx.nsmul (n + 1)).neg

theorem IsDyadic.sub {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem IsDyadic.mul {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x * y) := by
  rw [Rat.mul_def, Rat.normalize_eq_mkRat]
  exact IsDyadic.mkRat _ (Submonoid.mul_mem _ hx hy)

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

@[ext] theorem ext {x y : Dyadic} (h : x.val = y.val) : x = y := Subtype.ext h

instance : NatCast Dyadic where
  natCast n := ⟨n, ⟨0, rfl⟩⟩

@[simp] theorem val_natCast (n : ℕ) : (n : Dyadic).val = n := rfl

instance : IntCast Dyadic where
  intCast n := ⟨n, ⟨0, rfl⟩⟩

@[simp] theorem val_intCast (n : ℤ) : (n : Dyadic).val = n := rfl

instance : Zero Dyadic where
  zero := (0 : ℕ)

@[simp] theorem val_zero : (0 : Dyadic).val = 0 := rfl
@[simp] theorem mk_zero (h : IsDyadic 0) : (⟨0, h⟩ : Dyadic) = 0 := rfl

instance : One Dyadic where
  one := (1 : ℕ)

@[simp] theorem val_one : (1 : Dyadic).val = 1 := rfl
@[simp] theorem mk_one (h : IsDyadic 1) : (⟨1, h⟩ : Dyadic) = 1 := rfl

instance : Neg Dyadic where
  neg x := ⟨_, x.2.neg⟩

@[simp] theorem val_neg (x : Dyadic) : (-x).val = -x.val := rfl
@[simp] theorem neg_mk {x : ℚ} (hx : IsDyadic x) : -(⟨x, hx⟩ : Dyadic) = ⟨-x, hx.neg⟩ := rfl

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

theorem even_den {x : Dyadic} (hx : x.1.den ≠ 1) : Even x.1.den := by
  obtain ⟨n, hn⟩ := x.2
  rw [← hn]
  cases n
  · simp_all
  · rw [even_iff_two_dvd]
    exact dvd_mul_left ..

theorem odd_num {x : Dyadic} (hx : x.1.den ≠ 1) : Odd x.1.num := by
  rw [← Int.not_even_iff_odd]
  have hd := even_den hx
  rw [even_iff_two_dvd] at *
  rw [← Int.natAbs_dvd_natAbs]
  exact (Nat.not_coprime_of_dvd_of_dvd one_lt_two · hd x.1.reduced)

instance : CanLift Dyadic Int Int.cast (·.1.den = 1) where
  prf x hx := ⟨x.1.num, Dyadic.ext (x.1.den_eq_one_iff.mp hx)⟩

/-! ### Dyadic games -/

/-- For a dyadic number `m / n`, returns `(m - 1) / n`. -/
def lower (x : Dyadic) : Dyadic :=
  ⟨mkRat (x.1.num - 1) x.1.den, IsDyadic.mkRat _ x.2⟩

/-- For a dyadic number `m / n`, returns `(m + 1) / n`. -/
def upper (x : Dyadic) : Dyadic :=
  ⟨mkRat (x.1.num + 1) x.1.den, IsDyadic.mkRat _ x.2⟩

private theorem den_mkRat_lt {x : Dyadic} {n : ℤ} (hn : 2 ∣ n) (hd : x.1.den ≠ 1) :
    (mkRat n x.1.den).den < x.1.den := by
  rw [← Rat.normalize_eq_mkRat x.1.den_nz, Rat.normalize_eq]
  apply Nat.div_lt_self x.1.den_pos
  apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ x.1.den_pos) (Nat.dvd_gcd _ (even_den hd).two_dvd)
  rwa [← Int.natAbs_dvd_natAbs] at hn

theorem den_lower_lt {x : Dyadic} (h : x.1.den ≠ 1) : (lower x).1.den < x.1.den :=
  den_mkRat_lt ((odd_num h).sub_odd odd_one).two_dvd h

theorem den_upper_lt {x : Dyadic} (h : x.1.den ≠ 1) : (upper x).1.den < x.1.den :=
  den_mkRat_lt ((odd_num h).add_odd odd_one).two_dvd h

@[simp]
theorem lower_neg (x : Dyadic) : lower (-x) = -upper x := by
  unfold lower upper
  simp [Rat.neg_mkRat, ← sub_eq_neg_add]

@[simp]
theorem upper_neg (x : Dyadic) : upper (-x) = -lower x := by
  unfold lower upper
  simp [Rat.neg_mkRat, ← sub_eq_neg_add]

theorem num_den_add_self_of_den_ne_one {x : Dyadic} (hx : x.1.den ≠ 1) :
    (x + x).1.num = x.1.num ∧ (x + x).1.den = x.1.den / 2 := by
  obtain ⟨r, hr⟩ := x
  cases r using Rat.numDenCasesOn'' with | _ n d nz red =>
  dsimp [IsDyadic] at hr hx ⊢
  rw [Submonoid.mem_powers_iff] at hr
  obtain ⟨⟨⟩ | c, rfl⟩ := hr
  · simp at hx
  · have hc₀ : 2 ^ (c + 1) / 2 ≠ 0 := by simp [Nat.pow_add_one]
    have hcc : n.natAbs.Coprime (2 ^ (c + 1) / 2) := by
      rw [Nat.coprime_pow_right_iff c.zero_lt_succ] at red
      rw [Nat.pow_add_one, Nat.mul_div_cancel (2 ^ c) zero_lt_two]
      exact red.pow_right c
    set d : Rat := ⟨n, 2 ^ (c + 1), nz, red⟩
    rw [← Rat.mk'.injEq _ _ (d + d).den_nz (d + d).reduced n _ hc₀ hcc]
    simp_rw [Rat.mk'_num_den, d, Rat.mk'_eq_divInt, ← Rat.add_divInt]
    rw [Nat.pow_add_one, Nat.mul_div_cancel (2 ^ c) zero_lt_two,
      Rat.divInt_eq_divInt (by simp) (by simp)]
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_two, mul_right_comm, mul_assoc]

theorem den_add_intCast {x : Dyadic} (n : ℤ) : (x + n).1.den = x.1.den := by
  obtain ⟨x, hx⟩ := x
  dsimp
  cases x using Rat.numDenCasesOn' with | _ t b nz =>
  rw [Rat.intCast_eq_divInt, Rat.divInt_add_divInt t n (Nat.cast_ne_zero.mpr nz) one_ne_zero,
    mul_one, mul_one, Rat.den_mk, Rat.den_mk]
  rw [if_neg (Nat.cast_ne_zero.mpr nz), if_neg (Nat.cast_ne_zero.mpr nz)]
  simp_rw [Int.gcd_eq_natAbs]
  apply congrArg (b / ·)
  apply Nat.dvd_antisymm
  · rw [Nat.dvd_gcd_iff]
    constructor
    · rw [← Int.gcd_eq_natAbs, ← Int.ofNat_dvd, Int.dvd_natAbs]
      conv_rhs => equals t + n * b - n * b => simp
      apply dvd_sub
      · exact Int.gcd_dvd_left
      · apply dvd_mul_of_dvd_right
        exact Int.gcd_dvd_right
    · apply Nat.gcd_dvd_right
  · rw [Nat.dvd_gcd_iff]
    constructor
    · rw [← Int.gcd_eq_natAbs, ← Int.ofNat_dvd, Int.dvd_natAbs]
      apply dvd_add
      · exact Int.gcd_dvd_left
      · apply dvd_mul_of_dvd_right
        exact Int.gcd_dvd_right
    · apply Nat.gcd_dvd_right

theorem den_zsmul_le {x : Dyadic} (n : ℤ) : (n • x).1.den ≤ x.1.den := by
  obtain ⟨x, hx⟩ := x
  dsimp
  cases x using Rat.numDenCasesOn' with | _ t b nz =>
  rw [zsmul_eq_mul, Rat.intCast_eq_divInt, Rat.divInt_mul_divInt', one_mul,
    Rat.den_mk, Rat.den_mk]
  rw [if_neg (Nat.cast_ne_zero.mpr nz), if_neg (Nat.cast_ne_zero.mpr nz)]
  apply Nat.div_le_div_left
  · apply Nat.le_of_dvd (by simp [Int.gcd_pos_iff, nz])
    exact Int.gcd_dvd_gcd_mul_left t b n
  · simp [Int.gcd_pos_iff, nz]

@[simp]
theorem lower_add_self {x : Dyadic} (hx : x.1.den ≠ 1) :
    lower (x + x) = lower x + lower x := by
  ext
  simp_rw [val_add, lower]
  rw [Rat.mkRat_add_mkRat _ _ x.1.den_ne_zero x.1.den_ne_zero,
    Rat.mkRat_eq_iff (x + x).1.den_ne_zero (mul_ne_zero x.1.den_ne_zero x.1.den_ne_zero)]
  obtain ⟨hn, hd⟩ := num_den_add_self_of_den_ne_one hx
  have h2 : (2 : Int) ∣ x.1.den := by
    rw [← even_iff_two_dvd]
    exact (even_den hx).natCast
  rw [hn, hd, ← mul_add, ← mul_two, mul_assoc, mul_assoc, Int.natCast_div, Nat.cast_ofNat,
    Int.mul_ediv_cancel' h2, Nat.cast_mul]

@[simp]
theorem upper_add_self {x : Dyadic} (hx : x.1.den ≠ 1) :
    upper (x + x) = upper x + upper x := by
  rw [← Rat.den_neg_eq_den, ← Dyadic.val_neg] at hx
  simpa [← neg_add_rev] using lower_add_self hx

theorem lower_intCast (x : Int) : lower x = x - 1 := by
  ext
  simp [lower, Rat.den_intCast]

theorem upper_intCast (x : Int) : upper x = x + 1 := by
  ext
  simp [upper, Rat.den_intCast]

@[simp]
theorem lower_add_upper (x : Dyadic) : lower x + upper x = x + x := by
  ext
  simp_rw [val_add, lower, upper, Rat.mkRat_eq_divInt, ← Rat.add_divInt,
    sub_add_add_cancel, Rat.add_divInt, Rat.divInt_self]

theorem lower_lt_upper (x : Dyadic) : lower x < upper x := by
  rw [← Subtype.coe_lt_coe]
  apply lt_of_sub_pos
  simp_rw [lower, upper, Rat.mkRat_eq_divInt, sub_eq_add_neg,
    Rat.neg_divInt, ← Rat.add_divInt, ← Rat.zero_divInt 1]
  apply lt_of_le_of_ne
  · rw [Rat.divInt_le_divInt zero_lt_one (by simp [Rat.den_pos])]
    omega
  · rw [ne_eq, Rat.divInt_eq_divInt one_ne_zero (by simp)]
    omega

theorem exists_den_le_min_zsmul_eq (x y : Dyadic) :
    ∃ z : Dyadic, z.1.den ≤ max x.1.den y.1.den ∧
    (∃ n : Int, n • z = x) ∧ (∃ n : Int, n • z = y) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  have hj : (((max x.den y.den : Nat) : Rat)⁻¹).den = max x.den y.den := by
    rw [ ← Int.cast_natCast, ← Int.ofNat_inj, ← one_div, ← Int.cast_one,
      Rat.den_div_eq_of_coprime (Nat.cast_pos.mpr (lt_max_of_lt_left x.den_pos)) (by simp)]
  have hd : IsDyadic ((max x.den y.den : Nat) : Rat)⁻¹ := by
    rw [IsDyadic] at hx hy ⊢
    rw [hj]
    obtain ⟨h, -⟩ | ⟨h, -⟩ := max_cases x.den y.den <;> rwa [h]
  use ⟨_, hd⟩
  simp_rw [hj, le_rfl, true_and, Subtype.ext_iff, val_zsmul]
  wlog hxy : x.den ≤ y.den generalizing x y with ih
  · rw [max_comm, and_comm]
    exact ih y hy x hx (by rwa [max_comm]) (by rwa [max_comm]) (le_of_not_le hxy)
  rw [max_eq_right hxy]
  constructor
  · rw [IsDyadic, Submonoid.mem_powers_iff] at hx hy
    obtain ⟨c, hc⟩ := hx
    obtain ⟨g, hg⟩ := hy
    rw [← hc, ← hg] at hxy
    rw [pow_le_pow_iff_right₀ one_lt_two] at hxy
    use x.num * 2 ^ (g - c)
    rw [← hg, zsmul_eq_mul, Int.cast_mul, mul_assoc, Nat.cast_pow, Int.cast_pow,
      Nat.cast_ofNat, Int.cast_ofNat, pow_sub₀ 2 two_ne_zero hxy, mul_right_comm,
      mul_inv_cancel₀ (by simp), one_mul, ← Nat.cast_ofNat, ← Nat.cast_pow, hc,
      ← div_eq_mul_inv, Rat.num_div_den]
  · use y.num
    simp [← div_eq_mul_inv, Rat.num_div_den]

/-- Converts a dyadic rational into an `IGame`. This map is defined so that:

* If `x : ℤ`, then `toIGame x = ↑x`.
* Otherwise, if `x = m / n` with `n` even, then `toIGame x = {(m - 1) / n | (m + 1) / n}ᴵ`. Note
  that both options will have smaller denominators. -/
noncomputable def toIGame (x : Dyadic) : IGame :=
  if h : x.1.den = 1 then x.1.num else
    have := den_lower_lt h; have := den_upper_lt h
    {{toIGame (lower x)} | {toIGame (upper x)}}ᴵ
termination_by x.1.den

@[simp] theorem toIGame_intCast (n : ℤ) : toIGame n = n := by rw [toIGame, dif_pos] <;> rfl
@[simp] theorem toIGame_natCast (n : ℕ) : toIGame n = n := toIGame_intCast n

@[simp] theorem toIGame_zero : toIGame 0 = 0 := toIGame_natCast 0
@[simp] theorem toIGame_one : toIGame 1 = 1 := by simpa using toIGame_natCast 1

theorem toIGame_of_den_ne_one {x : Dyadic} (hx : x.1.den ≠ 1) :
    toIGame x = {{toIGame (lower x)} | {toIGame (upper x)}}ᴵ :=
  by rw [toIGame, dif_neg hx]

@[simp]
theorem toIGame_half : toIGame half = ½ := by
  have : mkRat 2 2 = 1 := rfl
  rw [toIGame_of_den_ne_one] <;> aesop (add simp [lower, upper])

@[simp]
theorem toIGame_neg (x : Dyadic) : toIGame (-x) = -toIGame x := by
  unfold toIGame
  dsimp
  split_ifs with h
  · simp
  · have := den_upper_lt h
    have := den_lower_lt h
    simpa using ⟨toIGame_neg _, toIGame_neg _⟩
termination_by x.1.den

theorem _root_.IGame.Numeric.le_of_add_self_le {x y : IGame} [x.Numeric] [y.Numeric]
    (h : x + x ≤ y + y) : x ≤ y := by
  by_contra hyx
  rw [IGame.Numeric.not_le] at hyx
  exact (add_lt_add hyx hyx).not_le h

theorem _root_.IGame.Numeric.add_self_le {x y : IGame} [x.Numeric] [y.Numeric] :
    x + x ≤ y + y ↔ x ≤ y :=
  ⟨IGame.Numeric.le_of_add_self_le, fun h => add_le_add h h⟩

theorem _root_.IGame.Numeric.equiv_of_add_self_equiv {x y : IGame} [x.Numeric] [y.Numeric]
    (h : x + x ≈ y + y) : x ≈ y :=
  h.imp IGame.Numeric.le_of_add_self_le IGame.Numeric.le_of_add_self_le

theorem _root_.IGame.Numeric.add_self_equiv {x y : IGame} [x.Numeric] [y.Numeric] :
    x + x ≈ y + y ↔ x ≈ y :=
  ⟨IGame.Numeric.equiv_of_add_self_equiv, fun h => IGame.add_congr h h⟩

/-!
# Properties of toIGame

In this section we use induction to simultaneously prove three properties of `toIGame`:
- Its range is numeric.
- It preserves addition up to equivalence.
- It is an order embedding.
-/

section bundle

-- bundle together all our induction hypotheses
private def bundle (n : Nat) : Prop :=
  (∀ x, x.1.den < n → (toIGame.{u} x).Numeric) ∧
  (∀ x y, x.1.den < n → y.1.den < n → toIGame.{u} (x + y) ≈ toIGame x + toIGame y) ∧
  (∀ x y, x.1.den < n → y.1.den < n → (toIGame.{u} x ≤ toIGame y ↔ x ≤ y))

private theorem numericK {n : Nat} {x : Dyadic}
    (ih : bundle.{u} n) (hn : x.1.den ≤ n) : (toIGame.{u} x).Numeric := by
  obtain h | rfl := lt_or_eq_of_le hn
  · exact ih.1 x h
  by_cases hx : x.1.den = 1
  · rw [toIGame, dif_pos hx]
    infer_instance
  rw [toIGame_of_den_ne_one hx, IGame.numeric_def]
  simp_rw [IGame.leftMoves_ofSets, IGame.rightMoves_ofSets,
    Set.mem_singleton_iff, forall_eq, lt_iff_le_not_le]
  simp only [ih.2.2, den_lower_lt hx, den_upper_lt hx]
  exact ⟨lt_iff_le_not_le.mp (lower_lt_upper x),
    ih.1 x.lower (den_lower_lt hx), ih.1 x.upper (den_upper_lt hx)⟩

private theorem toIGame_add_self_leK {n : Nat} {x : Dyadic} (ih : bundle.{u} n) (hn : x.1.den ≤ n) :
    toIGame.{u} (x + x) ≤ toIGame x + toIGame x := by
  obtain h | rfl := lt_or_eq_of_le hn
  · exact (ih.2.1 x x h h).le
  by_cases hx : x.1.den = 1
  · lift x to ℤ using hx
    simp_rw [← Int.cast_add, toIGame_intCast]
    exact (IGame.intCast_add_equiv x x).le
  have ih₁ : toIGame.{u} (x.lower + x.lower) ≈ toIGame x.lower + toIGame x.lower :=
    ih.2.1 x.lower x.lower (den_lower_lt hx) (den_lower_lt hx)
  have ih₂ : toIGame.{u} (x.upper + x.upper) ≈ toIGame x.upper + toIGame x.upper :=
    ih.2.1 x.upper x.upper (den_upper_lt hx) (den_upper_lt hx)
  have ih₁₂ : toIGame.{u} (x.lower + x.upper) ≈ toIGame x.lower + toIGame x.upper :=
    ih.2.1 x.lower x.upper (den_lower_lt hx) (den_upper_lt hx)
  have : (toIGame.{u} x.lower).Numeric := ih.1 x.lower (den_lower_lt hx)
  have : (toIGame.{u} x.upper).Numeric := ih.1 x.upper (den_upper_lt hx)
  have nn : (toIGame x).Numeric := numericK ih le_rfl
  rw [toIGame_of_den_ne_one hx] at nn ⊢
  rw [IGame.le_iff_forall_lf]
  constructor
  · have hm : {{x.lower.toIGame} | {x.upper.toIGame}}ᴵ + x.lower.toIGame ∈
      ({{x.lower.toIGame} | {x.upper.toIGame}}ᴵ +
        {{x.lower.toIGame} | {x.upper.toIGame}}ᴵ).leftMoves := by simp
    by_cases hxx : (x + x).1.den = 1
    · intro z hz
      have h : (x + x).1.num = x + x := by
        ext
        simpa using (Rat.den_eq_one_iff (x + x).1).mp hxx
      rw [← h, toIGame_intCast] at hz
      cases hc : (x + x).1.num with
      | ofNat c => cases c with rw [hc, Int.ofNat_eq_natCast, IGame.intCast_nat] at hz
        | zero => simp at hz
        | succ c =>
          rw [IGame.leftMoves_natCast_succ', Set.mem_singleton_iff] at hz
          subst hz
          refine IGame.lf_of_le_leftMove ?_ hm
          suffices hl : c ≤ toIGame x.lower + toIGame x.lower by
            apply hl.trans
            apply add_right_mono
            apply IGame.Numeric.le_of_not_le
            apply IGame.leftMove_lf
            simp
          refine le_trans ?_ ih₁.le
          rw [← lower_add_self hx, ← h, hc, Int.ofNat_eq_natCast, lower_intCast,
            Int.cast_natCast, Nat.cast_succ, add_sub_cancel_right, toIGame_natCast]
      | negSucc c =>
        rw [hc, IGame.intCast_negSucc, IGame.leftMoves_neg,
          ← Nat.cast_succ, IGame.rightMoves_natCast] at hz
        simp at hz
    simp_rw [toIGame_of_den_ne_one hxx, IGame.leftMoves_ofSets,
      Set.mem_singleton_iff, forall_eq]
    refine IGame.lf_of_le_leftMove ?_ hm
    rw [lower_add_self hx]
    apply ih₁.le.trans
    apply add_right_mono
    apply IGame.Numeric.le_of_not_le
    apply IGame.leftMove_lf
    simp
  · have hm : x.lower.toIGame + x.upper.toIGame ∈
      ({{x.lower.toIGame} | {x.upper.toIGame}}ᴵ + x.upper.toIGame).leftMoves := by simp
    simp_rw [IGame.forall_rightMoves_add, IGame.rightMoves_ofSets,
      Set.mem_singleton_iff, forall_eq]
    rw [add_comm, and_self]
    refine IGame.lf_of_le_leftMove ?_ hm
    rw [← lower_add_upper]
    exact ih₁₂.le

private theorem toIGame_add_selfK {n : Nat} {x : Dyadic} (ih : bundle.{u} n) (hn : x.1.den ≤ n) :
    toIGame.{u} (x + x) ≈ toIGame x + toIGame x := by
  constructor
  · apply toIGame_add_self_leK ih hn
  · rw [← Rat.den_neg_eq_den, ← Dyadic.val_neg] at hn
    simpa [← neg_add_rev] using toIGame_add_self_leK ih hn

private theorem intCast_leK {n : Nat} {x : Dyadic} (ih : bundle.{u} n)
    (hx : x.1.den ≤ n) (g : Int) : g ≤ toIGame.{u} x ↔ g ≤ x := by
  by_cases h : x.1.den = 1
  · lift x to ℤ using h
    simp [← Subtype.coe_le_coe]
  · have : (toIGame x).Numeric := numericK ih hx
    rw [← IGame.Numeric.add_self_le,
      ← (IGame.intCast_add_equiv g g).le_congr (toIGame_add_selfK ih hx)]
    have hh : (g : Dyadic).val ≤ x ↔ (g : Dyadic).val + (g : Dyadic).val ≤ x + x := by
      constructor
      · intro hu
        exact add_le_add hu hu
      · intro hgg
        by_contra hc
        rw [not_le] at hc
        exact (add_lt_add hc hc).not_le hgg
    simp_rw [← Dyadic.val_add, Subtype.coe_le_coe, ← Int.cast_add] at hh
    rw [hh]
    have hd : (x + x).1.den < x.1.den := by
      rw [(num_den_add_self_of_den_ne_one h).right]
      exact Nat.div_lt_self x.1.den_pos one_lt_two
    exact intCast_leK ih (hd.le.trans hx) (g + g)
termination_by x.1.den

private theorem toIGame_leK {n : Nat} {x y : Dyadic} (ih : bundle.{u} n)
    (hx : x.1.den ≤ n) (hy : y.1.den ≤ n) : toIGame.{u} x ≤ toIGame y ↔ x ≤ y := by
  have := numericK ih hx
  have := numericK ih hy
  have ux := toIGame_add_selfK ih hx
  have uy := toIGame_add_selfK ih hy
  by_cases cx : x.1.den = 1 <;> by_cases cy : y.1.den = 1
  · lift x to ℤ using cx
    lift y to ℤ using cy
    simp [← Subtype.coe_le_coe]
  · lift x to ℤ using cx
    rw [toIGame_intCast]
    exact intCast_leK ih hy x
  · lift y to ℤ using cy
    rw [toIGame_intCast]
    rw [← Rat.neg_den, ← Dyadic.val_neg] at hx
    simpa [← Subtype.coe_le_coe] using intCast_leK ih hx (-y)
  rw [← IGame.Numeric.add_self_le, ux.symm.le_congr uy.symm]
  have u (i : Dyadic) (hi : i.1.den ≠ 1) (hin : i.1.den ≤ n) : (i + i).1.den < n := by
    rw [(num_den_add_self_of_den_ne_one hi).right]
    refine lt_of_lt_of_le ?_ hin
    exact Nat.div_lt_self i.1.den_pos one_lt_two
  rw [ih.2.2 (x + x) (y + y) (u x cx hx) (u y cy hy)]
  simp_rw [← Subtype.coe_le_coe, Dyadic.val_add]
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    exact (add_lt_add hc hc).not_le h
  · intro h
    exact add_le_add h h

private theorem intCast_add_equivK {n : Nat} {x : Dyadic} (ih : bundle.{u} n)
    (hx : x.1.den ≤ n) (g : Int) : toIGame.{u} (x + g) ≈ (toIGame x + toIGame g) := by
  by_cases h : x.1.den = 1
  · lift x to ℤ using h
    simp_rw [← Int.cast_add, toIGame_intCast]
    exact IGame.intCast_add_equiv x g
  · have : (toIGame x).Numeric := numericK ih hx
    have hgg : (x + g).1.den ≤ n := by
      rwa [den_add_intCast]
    have : (toIGame (x + g)).Numeric := numericK ih hgg
    rw [toIGame_intCast, ← IGame.Numeric.add_self_equiv, add_add_add_comm]
    apply (toIGame_add_selfK ih hgg).symm.trans
    refine AntisymmRel.trans ?_
      (IGame.add_congr (toIGame_add_selfK ih hx) (IGame.intCast_add_equiv g g))
    rw [add_add_add_comm, ← Int.cast_add, ← toIGame_intCast]
    have hd : (x + x).1.den < x.1.den := by
      rw [(num_den_add_self_of_den_ne_one h).right]
      exact Nat.div_lt_self x.1.den_pos one_lt_two
    exact intCast_add_equivK ih (hd.le.trans hx) (g + g)
termination_by x.1.den

private theorem toIGame_add_equivK {n : Nat} {x y : Dyadic} (ih : bundle.{u} n)
    (hx : x.1.den ≤ n) (hy : y.1.den ≤ n) : toIGame.{u} (x + y) ≈ toIGame x + toIGame y := by
  have := numericK ih hx
  have := numericK ih hy
  by_cases hk1 : x.1.den = 1
  · lift x to ℤ using hk1
    rw [← Rat.neg_den, ← Dyadic.val_neg] at hy
    simpa [← neg_add_rev] using intCast_add_equivK ih hy (-x)
  by_cases hl1 : y.1.den = 1
  · lift y to ℤ using hl1
    exact intCast_add_equivK ih hx y
  obtain ⟨d, hdxy, ⟨k, rfl⟩, ⟨l, rfl⟩⟩ := exists_den_le_min_zsmul_eq x y
  rw [← add_zsmul]
  have hd := hdxy.trans (sup_le hx hy)
  have hk := (den_zsmul_le k).trans hd
  have hl := (den_zsmul_le l).trans hd
  have hkl := (den_zsmul_le (k + l)).trans hd
  have := numericK ih hkl
  apply IGame.Numeric.equiv_of_add_self_equiv
  apply (toIGame_add_selfK ih hkl).symm.trans
  rw [add_add_add_comm, add_zsmul, add_add_add_comm]
  have uk : (k • d + k • d).1.den < n := by
    rw [(num_den_add_self_of_den_ne_one hk1).right]
    refine lt_of_lt_of_le ?_ hx
    exact Nat.div_lt_self (k • d).1.den_pos one_lt_two
  have ul : (l • d + l • d).1.den < n := by
    rw [(num_den_add_self_of_den_ne_one hl1).right]
    refine lt_of_lt_of_le ?_ hy
    exact Nat.div_lt_self (l • d).1.den_pos one_lt_two
  apply (ih.2.1 (k • d + k • d) (l • d + l • d) uk ul).trans
  exact IGame.add_congr (toIGame_add_selfK ih hk) (toIGame_add_selfK ih hl)

private theorem forall_bundle (n : Nat) : bundle.{u} n := by
  induction n with
  | zero => simp [bundle]
  | succ n ih =>
    constructor
    · intro x hx
      rw [Nat.lt_succ_iff] at hx
      exact numericK ih hx
    constructor
    · intro x y hx hy
      rw [Nat.lt_succ_iff] at hx hy
      exact toIGame_add_equivK ih hx hy
    · intro x y hx hy
      rw [Nat.lt_succ_iff] at hx hy
      exact toIGame_leK ih hx hy

end bundle

instance (x : Dyadic) : (toIGame x).Numeric := numericK (forall_bundle _) le_rfl

theorem toIGame_le_iff {x y : Dyadic} : toIGame x ≤ toIGame y ↔ x ≤ y :=
  toIGame_leK (forall_bundle _) (le_max_left ..) (le_max_right ..)

theorem toIGame_add_equiv {x y : Dyadic} : toIGame (x + y) ≈ toIGame x + toIGame y :=
  toIGame_add_equivK (forall_bundle _) (le_max_left ..) (le_max_right ..)

end Dyadic
