/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Mathlib.Neg
import CombinatorialGames.Surreal.Dyadic.Basic
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Data.Real.Archimedean

/-!
# Real numbers as games

We define the function `Real.toIGame`, casting a real number to its Dedekind cut, and prove that
it's an order embedding. We then define the `Game` and `Surreal` versions of this map, and prove
that they are ring and field homomorphisms respectively.

## TODO

Every real number has birthday at most `ω`. This can be proven by showing that a real number is
equivalent to its Dedekind cut where only dyadic rationals are considered. At a later point, after
we have the necessary API on dyadic numbers, we might want to prove this equivalence, or even
re-define real numbers as Dedekind cuts of dyadic numbers specifically.
-/

open IGame

noncomputable section

-- TODO: PR to Mathlib
theorem exists_div_btwn {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Archimedean K] {x y : K} {n : ℕ} (h : x < y) (nh : (y - x)⁻¹ < n) :
    ∃ z : ℤ, x < (z : K) / n ∧ (z : K) / n < y := by
  obtain ⟨z, zh⟩ := exists_floor (x * n)
  refine ⟨z + 1, ?_⟩
  have n0' := (inv_pos.2 (sub_pos.2 h)).trans nh
  rw [div_lt_iff₀ n0']
  refine ⟨(lt_div_iff₀ n0').2 <| (lt_iff_lt_of_le_iff_le (zh _)).1 (lt_add_one _), ?_⟩
  rw [Int.cast_add, Int.cast_one]
  refine lt_of_le_of_lt (add_le_add_right ((zh _).1 le_rfl) _) ?_
  rwa [← lt_sub_iff_add_lt', ← sub_mul, ← div_lt_iff₀' (sub_pos.2 h), one_div]

theorem exists_dyadic_btwn {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Archimedean K] {x y : K} (h : x < y) : ∃ q : Dyadic, x < q ∧ q < y := by
  obtain ⟨n, nh⟩ := exists_nat_gt (y - x)⁻¹
  have := nh.trans (Nat.cast_lt.2 Nat.lt_two_pow_self)
  obtain ⟨z, hz, hz'⟩ := exists_div_btwn h (nh.trans (Nat.cast_lt.2 Nat.lt_two_pow_self))
  use .mkRat z ⟨n, rfl⟩
  simp_all [Rat.mkRat_eq_div]

namespace Real

/-! ### `ℝ` to `IGame` -/

/-- The canonical map from `ℝ` to `IGame`, sending a real number to its Dedekind cut of dyadic
rationals. -/
@[coe, match_pattern] def toIGame (x : ℝ) : IGame :=
  {(↑) '' {q : Dyadic | q < x} | (↑) '' {q : Dyadic | x < q}}ᴵ

instance : Coe ℝ IGame := ⟨toIGame⟩

instance Numeric.toIGame (x : ℝ) : Numeric x := by
  rw [Real.toIGame]
  apply Numeric.mk' <;> simp only [leftMoves_ofSets, rightMoves_ofSets, Set.forall_mem_image]
  · intro x hx y hy
    dsimp at *
    simpa using hx.trans hy
  all_goals infer_instance

@[simp]
theorem leftMoves_toIGame (x : ℝ) : leftMoves x = (↑) '' {q : Dyadic | q < x} :=
  leftMoves_ofSets ..

@[simp]
theorem rightMoves_toIGame (x : ℝ) : rightMoves x = (↑) '' {q : Dyadic | x < q} :=
  rightMoves_ofSets ..

theorem forall_leftMoves_toIGame {P : IGame → Prop} {x : ℝ} :
    (∀ y ∈ leftMoves x, P y) ↔ ∀ q : Dyadic, q < x → P q := by
  aesop

theorem exists_leftMoves_toIGame {P : IGame → Prop} {x : ℝ} :
    (∃ y ∈ leftMoves x, P y) ↔ ∃ q : Dyadic, q < x ∧ P q := by
  aesop

theorem forall_rightMoves_toIGame {P : IGame → Prop} {x : ℝ} :
    (∀ y ∈ rightMoves x, P y) ↔ ∀ q : Dyadic, x < q → P q := by
  aesop

theorem exists_rightMoves_toIGame {P : IGame → Prop} {x : ℝ} :
    (∃ y ∈ rightMoves x, P y) ↔ ∃ q : Dyadic, x < q ∧ P q := by
  aesop

theorem mem_leftMoves_toIGame_of_lt {q : Dyadic} {x : ℝ} (h : q < x) :
    (q : IGame) ∈ leftMoves x := by
  simpa

theorem mem_rightMoves_toIGame_of_lt {q : Dyadic} {x : ℝ} (h : x < q) :
    (q : IGame) ∈ rightMoves x := by
  simpa

/-- `Real.toIGame` as an `OrderEmbedding`. -/
@[simps!]
def toIGameEmbedding : ℝ ↪o IGame := by
  refine .ofStrictMono toIGame fun x y h ↦ ?_
  obtain ⟨q, hx, hy⟩ := exists_dyadic_btwn h
  trans (q : IGame)
  · apply Numeric.lt_rightMove
    simpa [toIGame]
  · apply Numeric.leftMove_lt
    simpa [toIGame]

@[simp, norm_cast]
theorem toIGame_le_iff {x y : ℝ} : (x : IGame) ≤ y ↔ x ≤ y :=
  toIGameEmbedding.le_iff_le

@[simp, norm_cast]
theorem toIGame_lt_iff {x y : ℝ} : (x : IGame) < y ↔ x < y :=
  toIGameEmbedding.lt_iff_lt

@[simp, norm_cast]
theorem toIGame_equiv_iff {x y : ℝ} : (x : IGame) ≈ y ↔ x = y := by
  simp [AntisymmRel, le_antisymm_iff]

@[simp, norm_cast]
theorem toIGame_inj {x y : ℝ} : (x : IGame) = y ↔ x = y :=
  toIGameEmbedding.inj

@[simp, norm_cast]
theorem toIGame_neg (x : ℝ) : toIGame (-x) = -toIGame x := by
  simp_rw [toIGame, neg_ofSets, ofSets_inj,
    ← Set.image_neg_of_apply_neg_eq_neg (fun _ _ ↦ Dyadic.toIGame_neg _)]
  aesop (add simp [lt_neg, neg_lt])

theorem toIGame_ratCast_equiv (q : ℚ) : toIGame q ≈ q := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf]
  refine ⟨⟨?_, fun x hx ↦ ?_⟩, ⟨fun x hx ↦ ?_, ?_⟩⟩
  · aesop
  · obtain ⟨r, hr, hr'⟩ := equiv_ratCast_of_mem_rightMoves_ratCast hx
    obtain ⟨s, hs, hs'⟩ := exists_dyadic_btwn hr
    rw [← IGame.ratCast_lt, ← hr'.lt_congr_right] at hs'
    apply lf_of_rightMove_le (z := s)
    · rw [Rat.cast_eq_id, id, ← s.toIGame_equiv.lt_congr_left] at hs'
      exact hs'.le
    · simpa
  · obtain ⟨r, hr, hr'⟩ := equiv_ratCast_of_mem_leftMoves_ratCast hx
    obtain ⟨s, hs, hs'⟩ := exists_dyadic_btwn hr
    rw [← IGame.ratCast_lt, ← hr'.lt_congr_left] at hs
    apply lf_of_le_leftMove (z := s)
    · rw [Rat.cast_eq_id, id, ← s.toIGame_equiv.lt_congr_right] at hs
      exact hs.le
    · simpa
  · aesop

theorem toIGame_dyadic_equiv (q : Dyadic) : toIGame q ≈ q := by
  rw [q.toIGame_equiv.antisymmRel_congr_right]
  exact toIGame_ratCast_equiv _

theorem toIGame_natCast_equiv (n : ℕ) : toIGame n ≈ n := by
  rw [← Rat.cast_natCast]
  simpa using toIGame_dyadic_equiv n

theorem toIGame_intCast_equiv (n : ℤ) : toIGame n ≈ n := by
  rw [← Rat.cast_intCast]
  simpa using toIGame_dyadic_equiv n

theorem toIGame_zero_equiv : toIGame 0 ≈ 0 := by simpa using toIGame_natCast_equiv 0
theorem toIGame_one_equiv : toIGame 1 ≈ 1 := by simpa using toIGame_natCast_equiv 1

@[simp] theorem ratCast_lt_toIGame {q : ℚ} {x : ℝ} : q < (x : IGame) ↔ q < x := by
  rw [← (toIGame_ratCast_equiv q).lt_congr_left, toIGame_lt_iff]
@[simp] theorem toIGame_lt_ratCast {q : ℚ} {x : ℝ} : (x : IGame) < q ↔ x < q := by
  rw [← (toIGame_ratCast_equiv q).lt_congr_right, toIGame_lt_iff]

@[simp] theorem ratCast_le_toIGame {q : ℚ} {x : ℝ} : q ≤ (x : IGame) ↔ q ≤ x := by
  simp [← not_lt, ← Numeric.not_lt]
@[simp] theorem toIGame_le_ratCast {q : ℚ} {x : ℝ} : (x : IGame) ≤ q ↔ x ≤ q := by
  simp [← not_lt, ← Numeric.not_lt]

@[simp] theorem ratCast_equiv_toIGame {q : ℚ} {x : ℝ} : (q : IGame) ≈ (x : IGame) ↔ q = x := by
  simp [AntisymmRel, le_antisymm_iff]
@[simp] theorem toIGame_equiv_ratCast {q : ℚ} {x : ℝ} : (x : IGame) ≈ q ↔ x = q := by
  simp [AntisymmRel, le_antisymm_iff]

theorem toIGame_add_ratCast_equiv (x : ℝ) (q : ℚ) : toIGame (x + q) ≈ x + q := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf, forall_leftMoves_add, forall_rightMoves_add]
  simp_rw [forall_leftMoves_toIGame, forall_rightMoves_toIGame, Numeric.not_le]
  refine ⟨⟨fun r hr ↦ ?_, ⟨fun r hr ↦ ?_, ?_⟩⟩, ⟨⟨fun r hr ↦ ?_, ?_⟩, fun r hr ↦ ?_⟩⟩
  · rw [r.toIGame_equiv.lt_congr_left, ← IGame.sub_lt_iff_lt_add,
      ← (IGame.ratCast_sub_equiv ..).lt_congr_left]
    simpa [sub_lt_iff_lt_add]
  · rw [(add_congr_left r.toIGame_equiv).lt_congr_right,
      ← (IGame.ratCast_add_equiv ..).lt_congr_right]
    simpa
  · intro y hy
    obtain ⟨r, hr, hy⟩ := equiv_ratCast_of_mem_rightMoves_ratCast hy
    rw [(add_congr_right hy).le_congr_left]
    rw [← ratCast_lt, ← add_lt_add_iff_left x] at hr
    obtain ⟨s, hs, hs'⟩ := exists_rat_btwn hr
    apply (lt_trans (b := (s : IGame)) _ _).not_ge
    · simpa
    · rw [← IGame.sub_lt_iff_lt_add, ← (IGame.ratCast_sub_equiv ..).lt_congr_left]
      simpa [sub_lt_iff_lt_add]
  · rw [(add_congr_left r.toIGame_equiv).lt_congr_left,
      ← (IGame.ratCast_add_equiv ..).lt_congr_left]
    simpa
  · intro y hy
    obtain ⟨r, hr, hy⟩ := equiv_ratCast_of_mem_leftMoves_ratCast hy
    rw [(add_congr_right hy).le_congr_right]
    rw [← ratCast_lt, ← add_lt_add_iff_left x] at hr
    obtain ⟨s, hs, hs'⟩ := exists_rat_btwn hr
    apply (lt_trans (b := (s : IGame)) _ _).not_ge
    · rw [← IGame.lt_sub_iff_add_lt, ← (IGame.ratCast_sub_equiv ..).lt_congr_right]
      simpa [lt_sub_iff_add_lt]
    · simpa
  · rw [r.toIGame_equiv.lt_congr_right, ← IGame.lt_sub_iff_add_lt,
      ← (IGame.ratCast_sub_equiv ..).lt_congr_right]
    simpa [lt_sub_iff_add_lt]

theorem toIGame_ratCast_add_equiv (q : ℚ) (x : ℝ) : toIGame (q + x) ≈ q + x := by
  simpa [add_comm] using toIGame_add_ratCast_equiv x q

theorem toIGame_add_dyadic_equiv (x : ℝ) (q : Dyadic) : toIGame (x + q) ≈ x + q :=
  (toIGame_add_ratCast_equiv _ _).trans (add_congr_right q.toIGame_equiv.symm)

theorem toIGame_dyadic_add_equiv (q : Dyadic) (x : ℝ) : toIGame (q + x) ≈ q + x := by
  simpa [add_comm] using toIGame_add_dyadic_equiv x q

theorem toIGame_add_equiv (x y : ℝ) : toIGame (x + y) ≈ x + y := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf, forall_leftMoves_add, forall_rightMoves_add]
  simp_rw [forall_leftMoves_toIGame, forall_rightMoves_toIGame, Numeric.not_le]
  refine ⟨⟨?_, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩ <;> intro q hq
  · rw [← sub_lt_iff_lt_add] at hq
    obtain ⟨r, hr, hr'⟩ := exists_rat_btwn hq
    rw [sub_lt_comm] at hr
    obtain ⟨s, hs, hs'⟩ := exists_rat_btwn hr
    trans r + s
    · rw [add_comm, q.toIGame_equiv.lt_congr_left, ← IGame.sub_lt_iff_lt_add,
        ← (ratCast_sub_equiv ..).lt_congr_left]
      simp_all [← Rat.cast_sub]
    · apply add_lt_add <;> simpa
  · rw [← (toIGame_dyadic_add_equiv ..).lt_congr_right]
    simpa
  · rw [← (toIGame_add_dyadic_equiv ..).lt_congr_right]
    simpa
  · rw [← (toIGame_dyadic_add_equiv ..).lt_congr_left]
    simpa
  · rw [← (toIGame_add_dyadic_equiv ..).lt_congr_left]
    simpa
  · rw [← lt_sub_iff_add_lt] at hq
    obtain ⟨r, hr, hr'⟩ := exists_rat_btwn hq
    rw [lt_sub_comm] at hr'
    obtain ⟨s, hs, hs'⟩ := exists_rat_btwn hr'
    trans r + s
    · apply add_lt_add <;> simpa
    · rw [add_comm, q.toIGame_equiv.lt_congr_right, ← IGame.lt_sub_iff_add_lt,
        ← (ratCast_sub_equiv ..).lt_congr_right]
      simp_all [← Rat.cast_sub]

theorem toIGame_sub_ratCast_equiv (x : ℝ) (q : ℚ) : toIGame (x - q) ≈ x - q := by
  simpa using toIGame_add_ratCast_equiv x (-q)

theorem toIGame_ratCast_sub_equiv (q : ℚ) (x : ℝ) : toIGame (q - x) ≈ q - x := by
  simpa using toIGame_ratCast_add_equiv q (-x)

theorem toIGame_sub_dyadic_equiv (x : ℝ) (q : Dyadic) : toIGame (x - q) ≈ x - q := by
  simpa using toIGame_add_dyadic_equiv x (-q)

theorem toIGame_dyadic_sub_equiv (q : Dyadic) (x : ℝ) : toIGame (q - x) ≈ q - x := by
  simpa using toIGame_dyadic_add_equiv q (-x)

theorem toIGame_sub_equiv (x y : ℝ) : toIGame (x - y) ≈ x - y := by
  simpa using toIGame_add_equiv x (-y)

/-! ### `ℝ` to `Game` -/

/-- The canonical map from `ℝ` to `Game`, sending a real number to its Dedekind cut. -/
@[coe, match_pattern] def toGame (x : ℝ) : Game := .mk x

instance : Coe ℝ Game := ⟨toGame⟩

@[simp] theorem _root_.Game.mk_real_toIGame (x : ℝ) : .mk x.toIGame = x.toGame := rfl

theorem toGame_def (x : ℝ) :
    toGame x = {(↑) '' {q : Dyadic | q < x} | (↑) '' {q : Dyadic | x < q}}ᴳ := by
  rw [← Game.mk_real_toIGame, toIGame]
  simp [Set.image_image]

/-- `Real.toGame` as an `OrderEmbedding`. -/
@[simps!]
def toGameEmbedding : ℝ ↪o Game :=
  .ofStrictMono toGame fun _ _ h ↦ toIGameEmbedding.strictMono h

@[simp, norm_cast]
theorem toGame_le_iff {x y : ℝ} : (x : Game) ≤ y ↔ x ≤ y :=
  toGameEmbedding.le_iff_le

@[simp, norm_cast]
theorem toGame_lt_iff {x y : ℝ} : (x : Game) < y ↔ x < y :=
  toGameEmbedding.lt_iff_lt

@[simp, norm_cast]
theorem toGame_equiv_iff {x y : ℝ} : (x : Game) ≈ y ↔ x = y := by
  simp [AntisymmRel, le_antisymm_iff]

@[simp, norm_cast]
theorem toGame_inj {x y : ℝ} : (x : Game) = y ↔ x = y :=
  toGameEmbedding.inj

@[simp, norm_cast] theorem toGame_ratCast (q : ℚ) : toGame q = q := Game.mk_eq (toIGame_ratCast_equiv q)
@[simp, norm_cast] theorem toGame_natCast (n : ℕ) : toGame n = n := by simpa using toGame_ratCast n
@[simp, norm_cast] theorem toGame_intCast (n : ℤ) : toGame n = n := by simpa using toGame_ratCast n

@[simp] theorem toGame_zero : toGame 0 = 0 := by simpa using toGame_natCast 0
@[simp] theorem toGame_one : toGame 1 = 1 := by simpa using toGame_natCast 1

@[simp]
theorem toGame_add (x y : ℝ) : toGame (x + y) = toGame x + toGame y := by
  simpa using Game.mk_eq (toIGame_add_equiv x y)

@[simp]
theorem toGame_sub (x y : ℝ) : toGame (x - y) = toGame x - toGame y := by
  simpa using Game.mk_eq (toIGame_sub_equiv x y)

/-- `Real.toGame` as an `OrderAddMonoidHom`. -/
@[simps]
def toGameAddHom : ℝ →+o Game where
  toFun := toGame
  map_zero' := toGame_zero
  map_add' := toGame_add
  monotone' := toGameEmbedding.monotone

/-! ### `ℝ` to `Surreal` -/

/-- The canonical map from `ℝ` to `Surreal`, sending a real number to its Dedekind cut. -/
@[coe, match_pattern] def toSurreal (x : ℝ) : Surreal := .mk x

instance : Coe ℝ Surreal := ⟨toSurreal⟩

@[simp] theorem _root_.Surreal.mk_real_toIGame (x : ℝ) : .mk x.toIGame = x.toSurreal := rfl

private theorem toSurreal_def_aux {x : ℝ} :
    ∀ y ∈ ((↑) '' {q : Dyadic | q < x} : Set Surreal),
    ∀ z ∈ (↑) '' {q : Dyadic | x < q}, y < z := by
  rintro - ⟨q, hq, rfl⟩ - ⟨r, hr, rfl⟩
  dsimp at *
  exact_mod_cast hq.trans hr

@[simp] theorem toGame_toSurreal (x : ℝ) : x.toSurreal.toGame = x.toGame := rfl

theorem toSurreal_def (x : ℝ) : toSurreal x =
    .ofSets ((↑) '' {q : Dyadic | q < x}) ((↑) '' {q : Dyadic | x < q}) toSurreal_def_aux := by
  rw [← Surreal.toGame_inj, toGame_toSurreal, Surreal.toGame_ofSets, toGame_def]
  congr <;> aesop

/-- `Real.toSurreal` as an `OrderEmbedding`. -/
@[simps!]
def toSurrealEmbedding : ℝ ↪o Surreal :=
  .ofStrictMono toSurreal fun _ _ h ↦ toIGameEmbedding.strictMono h

@[simp, norm_cast]
theorem toSurreal_le_iff {x y : ℝ} : (x : Surreal) ≤ y ↔ x ≤ y :=
  toSurrealEmbedding.le_iff_le

@[simp, norm_cast]
theorem toSurreal_lt_iff {x y : ℝ} : (x : Surreal) < y ↔ x < y :=
  toSurrealEmbedding.lt_iff_lt

@[simp, norm_cast]
theorem toSurreal_equiv_iff {x y : ℝ} : (x : Surreal) ≈ y ↔ x = y := by
  simp [AntisymmRel, le_antisymm_iff]

@[simp, norm_cast]
theorem toSurreal_inj {x y : ℝ} : (x : Surreal) = y ↔ x = y :=
  toSurrealEmbedding.inj

@[simp, norm_cast]
theorem toSurreal_ratCast (q : ℚ) : toSurreal q = q := by
  simpa using Surreal.mk_eq (toIGame_ratCast_equiv q)

@[simp, norm_cast] theorem toSurreal_natCast (n : ℕ) : toSurreal n = n := by
  simpa using toSurreal_ratCast n
@[simp, norm_cast] theorem toSurreal_intCast (n : ℤ) : toSurreal n = n := by
  simpa using toSurreal_ratCast n

@[simp, norm_cast] theorem toSurreal_zero : toSurreal 0 = 0 := by simpa using toSurreal_natCast 0
@[simp, norm_cast] theorem toSurreal_one : toSurreal 1 = 1 := by simpa using toSurreal_natCast 1

@[simp]
theorem toSurreal_add (x y : ℝ) : toSurreal (x + y) = x + y := by
  simpa using Surreal.mk_eq (toIGame_add_equiv x y)

@[simp]
theorem toSurreal_sub (x y : ℝ) : toSurreal (x - y) = x - y := by
  simpa using Surreal.mk_eq (toIGame_sub_equiv x y)

/-! For convenience, we deal with multiplication after defining `Real.toSurreal`. -/

private theorem exists_rat_mul_btwn {a b x : ℝ} (h : a * x < b) :
    ∃ q : ℚ, a * x ≤ q * x ∧ q * x < b := by
  obtain hx | rfl | hx := lt_trichotomy x 0
  · rw [← div_lt_iff_of_neg hx] at h
    obtain ⟨q, hq, hq'⟩ := exists_rat_btwn h
    use q, mul_le_mul_of_nonpos_right hq'.le hx.le
    rwa [← div_lt_iff_of_neg hx]
  · use 0
    simp_all
  · rw [← lt_div_iff₀ hx] at h
    obtain ⟨q, hq, hq'⟩ := exists_rat_btwn h
    use q, mul_le_mul_of_nonneg_right hq.le hx.le
    rwa [← lt_div_iff₀ hx]

private theorem exists_rat_mul_btwn' {a b x : ℝ} (h : a < b * x) :
    ∃ q : ℚ, a < q * x ∧ q * x ≤ b * x := by
  have : -b * x < -a := by simpa
  obtain ⟨q, hq, hq'⟩ := exists_rat_mul_btwn this
  use -q
  simp_all [lt_neg, neg_le]

private theorem toIGame_mul_le_mul {x : ℝ} {q r : ℚ} (h : x * r ≤ q * r) :
    toIGame x * r ≤ q * r := by
  obtain hr | rfl | hr := lt_trichotomy r 0 <;> simp_all

private theorem toIGame_mul_le_mul' {x : ℝ} {q r : ℚ} (h : q * r ≤ x * r) :
    q * r ≤ toIGame x * r := by
  obtain hr | rfl | hr := lt_trichotomy r 0 <;> simp_all

private theorem mulOption_lt_toIGame {x : ℝ} {q r s : ℚ} (h : x * s < x * q - r * q + r * s) :
    mulOption (toIGame x) q r s < toIGame (x * q) := by
  obtain ⟨t, ht, ht'⟩ := exists_rat_mul_btwn h
  apply lt_of_le_of_lt (b := ((r * q + t * s - r * s :) : IGame))
  · have := toIGame_mul_le_mul ht
    simp_all [mulOption, ← Surreal.mk_le_mk]
  · rw [← sub_lt_iff_lt_add, lt_sub_iff_add_lt] at ht'
    convert ht'
    simp only [ratCast_lt_toIGame, Rat.cast_sub, Rat.cast_add, Rat.cast_mul]
    abel_nf

private theorem toIGame_lt_mulOption {x : ℝ} {q r s : ℚ} (h : x * q - r * q + r * s < x * s) :
    toIGame (x * q) < mulOption (toIGame x) q r s := by
  obtain ⟨t, ht, ht'⟩ := exists_rat_mul_btwn' h
  apply lt_of_lt_of_le (b := ((r * q + t * s - r * s :) : IGame))
  · rw [← lt_sub_iff_add_lt, sub_lt_iff_lt_add] at ht
    convert ht
    simp only [toIGame_lt_ratCast, Rat.cast_sub, Rat.cast_add, Rat.cast_mul]
    abel_nf
  · have := toIGame_mul_le_mul' ht'
    simp_all [mulOption, ← Surreal.mk_le_mk]

theorem toIGame_mul_ratCast_equiv (x : ℝ) (q : ℚ) : (x * q).toIGame ≈ x * q := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf, forall_leftMoves_mul, forall_rightMoves_mul]
  simp_rw [forall_leftMoves_toIGame, forall_rightMoves_toIGame, Numeric.not_le]
  refine ⟨⟨?_, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro r h
    rw [r.toIGame_equiv.lt_congr_left]
    obtain hq | rfl | hq := lt_trichotomy q 0
    · rw [← lt_div_iff_of_neg (mod_cast hq)] at h
      rw [← Numeric.lt_div_iff_of_neg (by simpa),
        ← (ratCast_div_equiv ..).lt_congr_right]
      simpa
    · simp_all
    · rw [← div_lt_iff₀ (mod_cast hq)] at h
      rw [← Numeric.div_lt_iff (by simpa), ← (ratCast_div_equiv ..).lt_congr_left]
      simpa
  · intro r hr y hy
    have := Numeric.of_mem_rightMoves hy
    obtain ⟨s, hs, hy⟩ := equiv_ratCast_of_mem_rightMoves_ratCast hy
    rw [(Numeric.mulOption_congr₃ r.toIGame_equiv).le_congr_left,
      (Numeric.mulOption_congr₄ hy).le_congr_left]
    apply (toIGame_lt_mulOption _).not_ge
    have : 0 < (x - r) * (s - q) := by apply mul_pos <;> simpa [sub_pos]
    simp_all [sub_mul, mul_sub, lt_sub_iff_add_lt]
  · intro r hr y hy
    have := Numeric.of_mem_leftMoves hy
    obtain ⟨s, hs, hy⟩ := equiv_ratCast_of_mem_leftMoves_ratCast hy
    rw [(Numeric.mulOption_congr₃ r.toIGame_equiv).le_congr_left,
      (Numeric.mulOption_congr₄ hy).le_congr_left]
    apply (toIGame_lt_mulOption _).not_ge
    have : 0 < (x - r) * (s - q) := by apply mul_pos_of_neg_of_neg <;> simpa [sub_pos]
    simp_all [sub_mul, mul_sub, lt_sub_iff_add_lt]
  · intro r hr y hy
    have := Numeric.of_mem_leftMoves hy
    obtain ⟨s, hs, hy⟩ := equiv_ratCast_of_mem_leftMoves_ratCast hy
    rw [(Numeric.mulOption_congr₃ r.toIGame_equiv).le_congr_right,
      (Numeric.mulOption_congr₄ hy).le_congr_right]
    apply (mulOption_lt_toIGame _).not_ge
    have : 0 < (x - r) * (q - s) := by apply mul_pos <;> simpa [sub_pos]
    simp_all [sub_mul, mul_sub, sub_lt_iff_lt_add]
  · intro r hr y hy
    have := Numeric.of_mem_rightMoves hy
    obtain ⟨s, hs, hy⟩ := equiv_ratCast_of_mem_rightMoves_ratCast hy
    rw [(Numeric.mulOption_congr₃ r.toIGame_equiv).le_congr_right,
      (Numeric.mulOption_congr₄ hy).le_congr_right]
    apply (mulOption_lt_toIGame _).not_ge
    have : 0 < (x - r) * (q - s) := by apply mul_pos_of_neg_of_neg <;> simpa [sub_pos]
    simp_all [sub_mul, mul_sub, sub_lt_iff_lt_add]
  · intro r h
    rw [r.toIGame_equiv.lt_congr_right]
    obtain hq | rfl | hq := lt_trichotomy q 0
    · rw [← div_lt_iff_of_neg (mod_cast hq)] at h
      rw [← Numeric.div_lt_iff_of_neg (by simpa), ← (ratCast_div_equiv ..).lt_congr_left]
      simpa
    · simp_all
    · rw [← lt_div_iff₀ (mod_cast hq)] at h
      rw [← Numeric.lt_div_iff (by simpa), ← (ratCast_div_equiv ..).lt_congr_right]
      simpa

theorem toIGame_ratCast_mul_equiv (q : ℚ) (x : ℝ) : (q * x).toIGame ≈ q * x := by
  simpa [mul_comm] using toIGame_mul_ratCast_equiv x q

private theorem dyadic_lt_mul_toIGame' {x y : ℝ} {q : Dyadic}
    (hx : 0 < x) (hy : 0 < y) (h : q < x * y) : (q : IGame) < x * y := by
  rw [← div_lt_iff₀ hy] at h
  obtain ⟨r, hr, hr'⟩ := exists_rat_btwn (max_lt h hx)
  obtain ⟨hr, hr₀⟩ := max_lt_iff.1 hr
  rw [div_lt_comm₀ hy hr₀] at hr
  obtain ⟨s, hs, hs'⟩ := exists_rat_btwn (max_lt hr hy)
  trans r * s
  · rw [mul_comm, q.toIGame_equiv.lt_congr_left, ← IGame.Numeric.div_lt_iff,
      ← (ratCast_div_equiv ..).lt_congr_left] <;>
      simp_all [← Rat.cast_div]
  · simp_rw [← Surreal.mk_lt_mk]
    dsimp
    apply mul_lt_mul _ (le_of_lt _) _ (le_of_lt _) <;>
      simp_all [← toSurreal_zero, ← toSurreal_ratCast]

private theorem mul_toIGame_lt_dyadic' {x y : ℝ} {q : Dyadic}
    (hx : 0 < x) (hy : 0 < y) (h : x * y < q) : x * y < (q : IGame) := by
  rw [← lt_div_iff₀ hy] at h
  obtain ⟨r, hr, hr'⟩ := exists_rat_btwn h
  have hr₀ := hx.trans hr
  rw [lt_div_comm₀ hr₀ hy] at hr'
  obtain ⟨s, hs, hs'⟩ := exists_rat_btwn hr'
  trans r * s
  · simp_rw [← Surreal.mk_lt_mk]
    dsimp
    apply mul_lt_mul _ (le_of_lt _) _ (le_of_lt _) <;>
      simp_all [← toSurreal_zero, ← toSurreal_ratCast]
  · rw [mul_comm,q.toIGame_equiv.lt_congr_right,  ← IGame.Numeric.lt_div_iff,
      ← (ratCast_div_equiv ..).lt_congr_right] <;>
      simp_all [← Rat.cast_div]

private theorem dyadic_lt_mul_toIGame {x y : ℝ} (q : Dyadic) (h : q < x * y) :
    (q : IGame) < x * y := by
  obtain hx | rfl | hx := lt_trichotomy x 0
  · obtain hy | rfl | hy := lt_trichotomy y 0
    · have := @dyadic_lt_mul_toIGame' (-x) (-y) q
      simp_all
    · rw [(Numeric.mul_congr_right toIGame_zero_equiv).lt_congr_right]
      simp_all
    · have := @mul_toIGame_lt_dyadic' (-x) y (-q)
      simp_all
  · rw [(Numeric.mul_congr_left toIGame_zero_equiv).lt_congr_right]
    simp_all
  · obtain hy | rfl | hy := lt_trichotomy y 0
    · have := @mul_toIGame_lt_dyadic' x (-y) (-q)
      simp_all
    · rw [(Numeric.mul_congr_right toIGame_zero_equiv).lt_congr_right]
      simp_all
    · exact dyadic_lt_mul_toIGame' hx hy h

private theorem mul_toIGame_lt_dyadic {x y : ℝ} (q : Dyadic) (h : x * y < q) :
    x * y < (q : IGame) := by
  have := @dyadic_lt_mul_toIGame (-x) y (-q)
  simp_all

private theorem toSurreal_mul_ratCast (x : ℝ) (q : ℚ) : toSurreal (x * q) = x * q := by
  simpa using Surreal.mk_eq (toIGame_mul_ratCast_equiv x q)

private theorem mulOption_toIGame_equiv {x y : ℝ} {q r : Dyadic} :
    mulOption (toIGame x) (toIGame y) q r ≈ toIGame (q * y + x * r - q * r) := by
  simp [← Surreal.mk_eq_mk, mulOption, mul_comm, toSurreal_mul_ratCast]

theorem toIGame_mul_equiv (x y : ℝ) : (x * y).toIGame ≈ x * y := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf, forall_leftMoves_mul, forall_rightMoves_mul]
  simp_rw [forall_leftMoves_toIGame, forall_rightMoves_toIGame, Numeric.not_le]
  refine ⟨⟨dyadic_lt_mul_toIGame, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, mul_toIGame_lt_dyadic⟩⟩ <;>
    intro q hq r hr
  · rw [mulOption_toIGame_equiv.lt_congr_right, toIGame_lt_iff]
    have : 0 < (x - q) * (r - y) := by apply mul_pos <;> simpa [sub_pos]
    simp_all [sub_mul, mul_sub, sub_lt_iff_lt_add', add_sub_assoc]
  · rw [mulOption_toIGame_equiv.lt_congr_right, toIGame_lt_iff]
    have : 0 < (x - q) * (r - y) := by apply mul_pos_of_neg_of_neg <;> simpa [sub_pos]
    simp_all [sub_mul, mul_sub, sub_lt_iff_lt_add', add_sub_assoc]
  · rw [mulOption_toIGame_equiv.lt_congr_left, toIGame_lt_iff]
    have : 0 < (x - q) * (y - r) := by apply mul_pos <;> simpa [sub_pos]
    simp_all [sub_mul, mul_sub, lt_sub_iff_add_lt', add_sub_assoc]
  · rw [mulOption_toIGame_equiv.lt_congr_left, toIGame_lt_iff]
    have : 0 < (x - q) * (y - r) := by apply mul_pos_of_neg_of_neg <;> simpa [sub_pos]
    simp_all [sub_mul, mul_sub, lt_sub_iff_add_lt', add_sub_assoc]

@[simp, norm_cast]
theorem toSurreal_mul (x y : ℝ) : (x * y).toSurreal = x * y :=
  Surreal.mk_eq (toIGame_mul_equiv x y)

/-- `Real.toSurreal` as an `OrderRingHom`. -/
@[simps]
def toSurrealRingHom : ℝ →+*o Surreal where
  toFun := toSurreal
  map_zero' := toSurreal_zero
  map_one' := toSurreal_one
  map_add' := toSurreal_add
  map_mul' := toSurreal_mul
  monotone' := toSurrealEmbedding.monotone

@[simp, norm_cast]
theorem toSurreal_inv (x : ℝ) : x⁻¹.toSurreal = x.toSurreal⁻¹ :=
  map_inv₀ toSurrealRingHom x

@[simp, norm_cast]
theorem toSurreal_div (x y : ℝ) : (x / y).toSurreal = x / y :=
  map_div₀ toSurrealRingHom x y

theorem toIGame_inv_equiv (x : ℝ) : x⁻¹.toIGame ≈ x.toIGame⁻¹ := by
  simp [← Surreal.mk_eq_mk]

theorem toIGame_div_equiv (x y : ℝ) : (x / y).toIGame ≈ x / y := by
  simp [← Surreal.mk_eq_mk]

/-! ### Simp lemmas -/

/-! #### Dyadic -/

@[simp, norm_cast] theorem dyadic_lt_toIGame {q : Dyadic} {x : ℝ} : q < (x : IGame) ↔ q < x := by
  rw [← (toIGame_dyadic_equiv q).lt_congr_left, toIGame_lt_iff]
@[simp, norm_cast] theorem toIGame_lt_dyadic {q : Dyadic} {x : ℝ} : (x : IGame) < q ↔ x < q := by
  rw [← (toIGame_dyadic_equiv q).lt_congr_right, toIGame_lt_iff]

@[simp, norm_cast] theorem dyadic_le_toIGame {q : Dyadic} {x : ℝ} : q ≤ (x : IGame) ↔ q ≤ x := by
  simp [← not_lt, ← Numeric.not_lt]
@[simp, norm_cast] theorem toIGame_le_dyadic {q : Dyadic} {x : ℝ} : (x : IGame) ≤ q ↔ x ≤ q := by
  simp [← not_lt, ← Numeric.not_lt]

@[simp, norm_cast] theorem dyadic_equiv_toIGame {q : Dyadic} {x : ℝ} : (q : IGame) ≈ x ↔ q = x := by
  simp [AntisymmRel, le_antisymm_iff]
@[simp, norm_cast] theorem toIGame_equiv_dyadic {q : Dyadic} {x : ℝ} : (x : IGame) ≈ q ↔ x = q := by
  simp [AntisymmRel, le_antisymm_iff]

/-! #### ℤ -/

@[simp, norm_cast] theorem toIGame_lt_intCast {x : ℝ} {y : ℤ} : (x : IGame) < y ↔ x < y := by
  simp [← (ratCast_intCast_equiv y).lt_congr_right]
@[simp, norm_cast] theorem toIGame_le_intCast {x : ℝ} {y : ℤ} : (x : IGame) ≤ y ↔ x ≤ y := by
  simp [← (ratCast_intCast_equiv y).le_congr_right]

@[simp, norm_cast] theorem intCast_lt_toIGame {x : ℤ} {y : ℝ} : (x : IGame) < y ↔ x < y := by
  simp [← (ratCast_intCast_equiv x).lt_congr_left]
@[simp, norm_cast] theorem intCast_le_toIGame {x : ℤ} {y : ℝ} : (x : IGame) ≤ y ↔ x ≤ y := by
  simp [← (ratCast_intCast_equiv x).le_congr_left]

@[simp, norm_cast] theorem toIGame_equiv_intCast {x : ℝ} {y : ℤ} : (x : IGame) ≈ y ↔ x = y := by
  simp [AntisymmRel, le_antisymm_iff]
@[simp, norm_cast] theorem intCast_equiv_toIGame {x : ℤ} {y : ℝ} : (x : IGame) ≈ y ↔ x = y := by
  simp [AntisymmRel, le_antisymm_iff]

/-! #### ℕ -/

@[simp, norm_cast] theorem toIGame_lt_natCast {x : ℝ} {y : ℕ} : (x : IGame) < y ↔ x < y :=
  toIGame_lt_intCast (y := y)
@[simp, norm_cast] theorem toIGame_le_natCast {x : ℝ} {y : ℕ} : (x : IGame) ≤ y ↔ x ≤ y :=
  toIGame_le_intCast (y := y)

@[simp, norm_cast] theorem natCast_lt_toIGame {x : ℕ} {y : ℝ} : (x : IGame) < y ↔ x < y :=
  intCast_lt_toIGame (x := x)
@[simp, norm_cast] theorem natCast_le_toIGame {x : ℕ} {y : ℝ} : (x : IGame) ≤ y ↔ x ≤ y :=
  intCast_le_toIGame (x := x)

@[simp, norm_cast] theorem toIGame_equiv_natCast {x : ℝ} {y : ℕ} : (x : IGame) ≈ y ↔ x = y :=
  toIGame_equiv_intCast (y := y)
@[simp, norm_cast] theorem natCast_equiv_toIGame {x : ℕ} {y : ℝ} : (x : IGame) ≈ y ↔ x = y :=
  intCast_equiv_toIGame (x := x)

/-! #### 0 -/

@[simp, norm_cast] theorem toIGame_lt_zero {x : ℝ} : (x : IGame) < 0 ↔ x < 0 := by
  simpa using toIGame_lt_natCast (y := 0)
@[simp, norm_cast] theorem toIGame_le_zero {x : ℝ} : (x : IGame) ≤ 0 ↔ x ≤ 0 := by
  simpa using toIGame_le_natCast (y := 0)

@[simp, norm_cast] theorem zero_lt_toIGame {x : ℝ} : 0 < (x : IGame) ↔ 0 < x := by
  simpa using natCast_lt_toIGame (x := 0)
@[simp, norm_cast] theorem zero_le_toIGame {x : ℝ} : 0 ≤ (x : IGame) ↔ 0 ≤ x := by
  simpa using natCast_le_toIGame (x := 0)

@[simp, norm_cast] theorem toIGame_equiv_zero {x : ℝ} : (x : IGame) ≈ 0 ↔ x = 0 := by
  simpa using toIGame_equiv_natCast (y := 0)
@[simp, norm_cast] theorem zero_equiv_toIGame {x : ℝ} : 0 ≈ (x : IGame) ↔ 0 = x := by
  simpa using natCast_equiv_toIGame (x := 0)

/-! #### 1 -/

@[simp, norm_cast] theorem toIGame_lt_one {x : ℝ} : (x : IGame) < 1 ↔ x < 1 := by
  simpa using toIGame_lt_natCast (y := 1)
@[simp, norm_cast] theorem toIGame_le_one {x : ℝ} : (x : IGame) ≤ 1 ↔ x ≤ 1 := by
  simpa using toIGame_le_natCast (y := 1)

@[simp, norm_cast] theorem one_lt_toIGame {x : ℝ} : 1 < (x : IGame) ↔ 1 < x := by
  simpa using natCast_lt_toIGame (x := 1)
@[simp, norm_cast] theorem one_le_toIGame {x : ℝ} : 1 ≤ (x : IGame) ↔ 1 ≤ x := by
  simpa using natCast_le_toIGame (x := 1)

@[simp, norm_cast] theorem toIGame_equiv_one {x : ℝ} : (x : IGame) ≈ 1 ↔ x = 1 := by
  simpa using toIGame_equiv_natCast (y := 1)
@[simp, norm_cast] theorem one_equiv_toIGame {x : ℝ} : 1 ≈ (x : IGame) ↔ 1 = x := by
  simpa using natCast_equiv_toIGame (x := 1)

end Real
end
