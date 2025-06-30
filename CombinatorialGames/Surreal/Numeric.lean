/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Short
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Int
import CombinatorialGames.Surreal.Basic

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
open IGame

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

theorem IsDyadic.add {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  rw [Rat.add_def']
  exact .mkRat _ (Submonoid.mul_mem _ hx hy)

theorem IsDyadic.sub {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem IsDyadic.mul {x y : ℚ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x * y) := by
  rw [Rat.mul_def, Rat.normalize_eq_mkRat]
  exact .mkRat _ (Submonoid.mul_mem _ hx hy)

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

@[simp]
theorem den_le_one_iff_eq_one {x : Dyadic} : x.den ≤ 1 ↔ x.den = 1 := by
  simp_rw [Nat.le_one_iff_eq_zero_or_eq_one, x.den_ne_zero, false_or]

@[ext] theorem ext {x y : Dyadic} (h : x.val = y.val) : x = y := Subtype.ext h

instance : NatCast Dyadic where
  natCast n := ⟨n, ⟨0, rfl⟩⟩

@[simp] theorem val_natCast (n : ℕ) : (n : Dyadic).val = n := rfl
@[simp] theorem num_natCast (n : ℕ) : (n : Dyadic).num = n := rfl
@[simp] theorem den_natCast (n : ℕ) : (n : Dyadic).den = 1 := rfl

instance : IntCast Dyadic where
  intCast n := ⟨n, ⟨0, rfl⟩⟩

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

instance : Ring Dyadic where
  add_assoc x y z := by ext; simp [add_assoc]
  zero_add x := by ext; simp
  add_zero x := by ext; simp
  add_comm x y := by ext; simp [add_comm]
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
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : LinearOrderedRing Dyadic where
  add_le_add_left x y h z := add_le_add_left (α := ℚ) h z
  zero_le_one := by decide
  mul_pos x y := mul_pos (α := ℚ)
  le_total x y := le_total (α := ℚ) x y
  decidableLE x y := inferInstanceAs (Decidable (x.1 ≤ y.1))
  min_def x y := by ext; rw [min_def]
  max_def x y := by ext; rw [max_def]
  compare_eq_compareOfLessAndEq x y := by
    change compare x.1 y.1 = _
    rw [LinearOrder.compare_eq_compareOfLessAndEq]
    simp [compareOfLessAndEq, Dyadic.ext_iff]

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

/-! ### Dyadic games -/

/-- For a dyadic number `m / n`, returns `(m - 1) / n`. -/
def lower (x : Dyadic) : Dyadic :=
  .mkRat (x.num - 1) x.2

/-- For a dyadic number `m / n`, returns `(m + 1) / n`. -/
def upper (x : Dyadic) : Dyadic :=
  .mkRat (x.num + 1) x.2

private theorem den_mkRat_lt {x : Dyadic} {n : ℤ} (hn : 2 ∣ n) (hd : x.den ≠ 1) :
    (mkRat n x.den).den < x.den := by
  rw [← Rat.normalize_eq_mkRat x.den_ne_zero, Rat.normalize_eq]
  apply Nat.div_lt_self x.den_pos
  apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ x.den_pos) (Nat.dvd_gcd _ (even_den hd).two_dvd)
  rwa [← Int.natAbs_dvd_natAbs] at hn

theorem den_lower_lt {x : Dyadic} (h : x.den ≠ 1) : (lower x).den < x.den :=
  den_mkRat_lt ((odd_num h).sub_odd odd_one).two_dvd h

theorem den_upper_lt {x : Dyadic} (h : x.den ≠ 1) : (upper x).den < x.den :=
  den_mkRat_lt ((odd_num h).add_odd odd_one).two_dvd h

/-- An auxiliary tactic for inducting on the denominator of a `Dyadic`. -/
macro "dyadic_wf" : tactic =>
  `(tactic| all_goals first | solve_by_elim [Prod.Lex.left, Prod.Lex.right, den_lower_lt, den_upper_lt] | decreasing_tactic)

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

theorem lower_eq_of_den_eq_one {x : Dyadic} (h : x.den = 1) : lower x = x.num - 1 := by
  simp [lower, h, Dyadic.ext_iff]

theorem upper_eq_of_den_eq_one {x : Dyadic} (h : x.den = 1) : upper x = x.num + 1 := by
  simp [upper, h, Dyadic.ext_iff]

theorem lower_lt_upper (x : Dyadic) : lower x < upper x := by
  unfold lower upper
  rw [Subtype.mk_lt_mk, val_mkRat, val_mkRat, Rat.mkRat_eq_div, Rat.mkRat_eq_div,
    div_lt_div_iff_of_pos_right (mod_cast x.den_pos)]
  simp [sub_eq_add_neg]

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

instance _root_.IGame.Short.dyadic (x : Dyadic) : Short (toIGame x) := by
  rw [toIGame]
  split_ifs with h
  · exact .intCast _
  · rw [short_def]
    simpa using ⟨.dyadic _, .dyadic _⟩
termination_by x.den
decreasing_by dyadic_wf

end Dyadic
