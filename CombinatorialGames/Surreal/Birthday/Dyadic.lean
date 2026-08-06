/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Surreal.Birthday.Basic
public import CombinatorialGames.Surreal.Dyadic

import CombinatorialGames.Surreal.Birthday.Cut

/-!
# Birthday of dyadic rationals

We prove that a surreal number has a finite birthday iff it's a dyadic number.
-/

public section

-- mathlib PR #42481
theorem Nat.add_div_le_div_add_div_add_one (a b c : ℕ) : (a + b) / c ≤ a / c + b / c + 1 :=
  if h : c = 0 then by simp [h] else
    (Nat.add_div (Nat.pos_of_ne_zero h)).trans_le
      (Nat.add_le_add_left (by split <;> decide) _)

theorem Nat.div_lt_div_iff_exists {a b c : ℕ} : a / c < b / c ↔ ∃ d, a < d ∧ d ≤ b ∧ c ∣ d := by
  constructor
  · intro h
    refine ⟨b - b % c, ?_, Nat.sub_le b _, Nat.dvd_sub_mod b⟩
    have hc0 : c ≠ 0 := by rintro rfl; simp at h
    -- lean4 PR #14699
    rw [← Nat.div_mul_cancel (Nat.dvd_sub_mod b),
      ← Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hc0), ← Nat.div_eq_sub_mod_div]
    exact h
  · intro ⟨d, ha, hb, hc⟩
    grw [← hb]
    exact Nat.div_lt_div_of_lt_of_dvd hc ha

local notation "ω" => NatOrdinal.of Ordinal.omega0

@[simp]
theorem Game.birthday_ratCast (x : ℚ) : Game.birthday x = Surreal.birthday x := by
  rw [← Surreal.toGame_ratCast, Surreal.birthday_toGame]

theorem Surreal.birthday_dyadic_lt_omega0 (x : Dyadic) : Surreal.birthday x < ω := by
  rw [← Surreal.mk_dyadic]
  exact (Surreal.birthday_mk_le _).trans_lt (IGame.Short.birthday_lt_omega0 _)

theorem Surreal.birthday_lt_omega0_iff {x : Surreal} :
    x.birthday < ω ↔ x ∈ Set.range ((↑) : Dyadic → _) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨x, _, rfl, hx⟩ := Surreal.birthday_eq_iGameBirthday x
    rw [← hx, ← IGame.short_iff_birthday_finite] at h
    exact ⟨_, ratCast_toDyadic _⟩
  · rintro ⟨q, rfl⟩
    exact Surreal.birthday_dyadic_lt_omega0 q

/-- The birthday of a dyadic number can be computed explicitly. -/
@[expose]
def Dyadic.birthday (x : Dyadic) : Nat :=
  if h : x.den = 1 then x.num.natAbs else (x.precision.get ?isSome).toNat + x.num.natAbs / x.den + 1
where finally
  cases x
  · exact h.elim rfl
  · rfl

@[simp]
theorem Dyadic.birthday_intCast (n : Int) : Dyadic.birthday n = n.natAbs := by
  unfold Dyadic.birthday
  rw [dif_pos (Dyadic.den_intCast n), Dyadic.num_intCast]

@[simp]
theorem Dyadic.birthday_natCast (n : Nat) : Dyadic.birthday n = n := by
  rw [← Int.cast_natCast, Dyadic.birthday_intCast, Int.natAbs_natCast]

theorem Dyadic.birthday_of_den_ne_one {x : Dyadic} (hx : x.den ≠ 1) :
  x.birthday = (x.precision.get (by
    cases x
    · exact hx.elim rfl
    · rfl)).toNat + x.num.natAbs / x.den + 1 := dif_neg hx

example : Dyadic.birthday ((13 : Dyadic) >>> 2) = 6 := rfl -- birthday 3.25 = 6
example : Dyadic.birthday ((1 : Dyadic) >>> 1) = 2 := rfl -- birthday 1/2 = 2
example : Dyadic.birthday 7 = 7 := rfl -- birthday 7 = 7
example : Dyadic.birthday ((-5 : Dyadic) >>> 1) = 4 := rfl -- birthday -2.5 = 4
example : Dyadic.birthday ((1 : Dyadic) <<< 4) = 16 := rfl -- birthday 16 = 16

theorem IGame.birthday_dyadic (x : Dyadic) : IGame.birthday x = x.birthday := by
  induction hd : x.den using Nat.strongRec generalizing x with | ind d ih
  cases hd
  obtain hd | hd := eq_or_ne x.den 1
  · unfold Dyadic.birthday
    rw [Dyadic.toIGame_of_den_eq_one hd, IGame.birthday_intCast, dif_pos hd]
  · rw [Dyadic.toIGame_of_den_ne_one hd, birthday_ofSets]
    simp_rw [Set.image_singleton, csSup_singleton, Function.comp_apply]
    rw [ih _ (x.den_lower_lt hd) _ rfl, ih _ (x.den_upper_lt hd) _ rfl,
      Order.succ_eq_add_one, Order.succ_eq_add_one,
      ← Nat.cast_add_one, ← Nat.cast_add_one, ← Nat.cast_max,
      Nat.cast_inj, Nat.add_max_add_right]
    unfold Dyadic.birthday
    rw [dif_neg hd, Nat.add_one_inj]
    have hnd := x.max_den_lower_upper hd
    have hnd0 : (x.precision.getD 0).toNat ≠ 0 := by
      rw [ne_eq, ← pow_right_inj₀ Nat.two_pos (by decide), pow_zero,
        ← Dyadic.den_eq_two_pow_toNat_precision]
      exact hd
    simp_rw [Dyadic.den_eq_two_pow_toNat_precision] at hnd
    rw [← (pow_right_monotone one_le_two).map_max,
      ← Nat.pow_sub_one (by decide) hnd0, pow_right_inj₀ Nat.two_pos (by decide),
      eq_comm, Nat.sub_eq_iff_eq_add (Nat.one_le_iff_ne_zero.2 hnd0)] at hnd
    rw [Option.get_eq_getD, hnd, add_right_comm]
    have hcd : x.num / x.den = x.toRat := x.toRat.num_div_den
    have hd0 : 0 < x.den := by positivity
    generalize hcn : x.num = c, hdd : x.den = d at hcd hd0
    conv =>
      enter [1]
      congr <;>
      · enter [3]
        unfold Dyadic.num Dyadic.den
    have hle : x.lower.toRat = Int.cast (c - 1) / d := by
      rw [x.coe_lower, hdd, ← hcd, ← one_div, ← sub_div, ← Rat.intCast_one, ← Int.cast_sub]
    have hue : x.upper.toRat = Int.cast (c + 1) / d := by
      rw [x.coe_upper, hdd, ← hcd, ← one_div, ← add_div, ← Rat.intCast_one, ← Int.cast_add]
    have hk (c : Int) (d : Nat) : (Rat.num (c / d)).natAbs / Rat.den (c / d) = c.natAbs / d := by
      obtain hd0 | hd0 := eq_zero_or_pos d
      · simp [hd0]
      · rw [← Rat.mkRat_eq_div, Rat.num_mkRat, Rat.den_mkRat,
          if_neg hd0.ne', if_neg hd0.ne',
          Int.natAbs_ediv_of_dvd (Int.natCast_dvd.2 (Nat.gcd_dvd_right _ _)),
          Int.natAbs_natCast, ← Nat.mul_div_mul_right _ _ (Nat.gcd_pos_of_pos_left c.natAbs hd0),
          Nat.div_mul_cancel (Nat.gcd_dvd_left _ _), Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]
    simp_rw [hle, hue, hk]
    have hlnd (hl : x.lower.den = 1) : x.lower.num.natAbs = (c - 1).natAbs / d := by
      have hlnd := congr((x.lower.num / $hl : Rat))
      rw [Nat.cast_one, div_one, ← Int.cast_natCast, ← Rat.intCast_div _ _ (by simp [hl]),
        Int.cast_inj] at hlnd
      rw [← hlnd, Int.natAbs_ediv_of_dvd (by simp [hl]), Int.natAbs_natCast,
        Dyadic.num, Dyadic.den, hle, hk]
    have hund (hr : x.upper.den = 1) : x.upper.num.natAbs = (c + 1).natAbs / d := by
      have hund := congr((x.upper.num / $hr : Rat))
      rw [Nat.cast_one, div_one, ← Int.cast_natCast, ← Rat.intCast_div _ _ (by simp [hr]),
        Int.cast_inj] at hund
      rw [← hund, Int.natAbs_ediv_of_dvd (by simp [hr]), Int.natAbs_natCast,
        Dyadic.num, Dyadic.den, hue, hk]
    have hccl (hl : x.lower.den ≠ 1) : (c - 1).natAbs / d = c.natAbs / d := by
      apply le_antisymm
      · rw [← not_lt, Nat.div_lt_div_iff_exists]
        simp_rw [not_exists, not_and]
        intro k hkl hkr
        cases le_antisymm (Nat.add_one_le_of_lt hkl) (hkr.trans (Int.natAbs_sub_le c 1))
        rw [le_antisymm hkr (Int.natAbs_sub_le c 1), ← Int.natCast_dvd]
        contrapose! hl
        obtain ⟨e, he⟩ := hl
        rw [he, Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ (by positivity)] at hle
        rw [Dyadic.den, hle, Rat.den_intCast]
      · rw [← not_lt, Nat.div_lt_div_iff_exists]
        simp_rw [not_exists, not_and]
        intro k hkl hkr
        rw [← Int.sub_add_cancel c 1] at hkr
        cases le_antisymm (Nat.add_one_le_of_lt hkl) (hkr.trans (Int.natAbs_add_le _ 1))
        rw [le_antisymm hkr (Int.natAbs_add_le _ 1), Int.sub_add_cancel, ← Int.natCast_dvd]
        contrapose! hd
        obtain ⟨e, he⟩ := hd
        rw [he, Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ (by positivity)] at hcd
        rw [Dyadic.den, ← hcd, Rat.den_intCast]
    have hccu (hr : x.upper.den ≠ 1) : (c + 1).natAbs / d = c.natAbs / d := by
      apply le_antisymm
      · rw [← not_lt, Nat.div_lt_div_iff_exists]
        simp_rw [not_exists, not_and]
        intro k hkl hkr
        cases le_antisymm (Nat.add_one_le_of_lt hkl) (hkr.trans (Int.natAbs_add_le c 1))
        rw [le_antisymm hkr (Int.natAbs_add_le c 1), ← Int.natCast_dvd]
        contrapose! hr
        obtain ⟨e, he⟩ := hr
        rw [he, Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ (by positivity)] at hue
        rw [Dyadic.den, hue, Rat.den_intCast]
      · rw [← not_lt, Nat.div_lt_div_iff_exists]
        simp_rw [not_exists, not_and]
        intro k hkl hkr
        rw [← Int.add_sub_cancel c 1] at hkr
        cases le_antisymm (Nat.add_one_le_of_lt hkl) (hkr.trans (Int.natAbs_sub_le _ 1))
        rw [le_antisymm hkr (Int.natAbs_sub_le _ 1), Int.add_sub_cancel, ← Int.natCast_dvd]
        contrapose! hd
        obtain ⟨e, he⟩ := hd
        rw [he, Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ (by positivity)] at hcd
        rw [Dyadic.den, ← hcd, Rat.den_intCast]
    by_cases hl : x.lower.den = 1 <;> by_cases hr : x.upper.den = 1
    · rw [dif_pos hl, dif_pos hr]
      rw [Dyadic.den_eq_two_pow_toNat_precision, Nat.pow_eq_one, or_iff_right (by decide)] at hl hr
      rw [hl, hr, max_self, zero_add, ← Nat.pow_right_inj Nat.one_lt_two, Nat.pow_one,
        ← Dyadic.den_eq_two_pow_toNat_precision] at hnd
      rw [hl, hr, max_self, zero_add, ← hdd, hnd]
      obtain ⟨c, rfl⟩ := hcn ▸ x.odd_num hd
      unfold Dyadic.num
      rw [hle, hue, ← hdd, hnd, Int.add_sub_cancel, add_assoc, ← two_mul, ← mul_add,
        Rat.intCast_mul, Rat.intCast_mul, Rat.intCast_ofNat, Rat.natCast_ofNat,
        mul_div_cancel_left₀ _ (by decide), mul_div_cancel_left₀ _ (by decide),
        Rat.num_intCast, Rat.num_intCast]
      lia
    · rw [dif_pos hl, dif_neg hr, hlnd hl]
      rw [Dyadic.den_eq_two_pow_toNat_precision, Nat.pow_eq_one, or_iff_right (by decide)] at hl
      rw [hl, zero_max] at hnd ⊢
      rw [hccu hr, Option.get_eq_getD, max_eq_right_iff, add_assoc]
      apply le_add_of_le_right
      grw [Int.natAbs_sub_le]
      rw [Int.natAbs_one, Nat.succ_div, Nat.add_le_add_iff_left]
      apply ite_le_sup
    · rw [dif_neg hl, dif_pos hr, hund hr]
      rw [Dyadic.den_eq_two_pow_toNat_precision, Nat.pow_eq_one, or_iff_right (by decide)] at hr
      rw [hr, max_zero] at hnd ⊢
      rw [hccl hl, Option.get_eq_getD, max_eq_left_iff, add_assoc]
      apply le_add_of_le_right
      grw [Int.natAbs_add_le]
      rw [Int.natAbs_one, Nat.succ_div, Nat.add_le_add_iff_left]
      apply ite_le_sup
    · rw [dif_neg hl, dif_neg hr, hccl hl, hccu hr, Nat.add_max_add_right, Nat.add_max_add_right,
        Option.get_eq_getD, Option.get_eq_getD]

-- `Dyadic.toIGame` is canonical, so it minimizes the birthday in its equivalence class.
proof_wanted Surreal.birthday_dyadic (x : Dyadic) :
    Surreal.birthday x = IGame.birthday x

end
