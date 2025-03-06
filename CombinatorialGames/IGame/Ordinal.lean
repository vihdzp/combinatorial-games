/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.IGame.Basic
import CombinatorialGames.IGame.Short
import Mathlib.SetTheory.Ordinal.NaturalOps

/-!
# Ordinals as games

We define the canonical map `NatOrdinal → IGame`, where every ordinal is mapped to the game whose
left set consists of all previous ordinals. We make use of the type alias `NatOrdinal` rather than
`Ordinal`, as this map also preserves addition, and in the case of surreals, multiplication. The map
to surreals is defined in `NatOrdinal.toSurreal`.

This file also contains some properties about `NatCast` on `IGame` and `Game`.

# Main declarations

- `NatOrdinal.toIGame`: The canonical map between `NatOrdinal` and `IGame`.
- `NatOrdinal.toGame`: The canonical map between `NatOrdinal` and `Game`.
-/

universe u

open Set IGame

noncomputable section

-- TODO: upstream
@[simp]
theorem OrderEmbedding.antisymmRel_iff_antisymmRel {α β : Type*} [Preorder α] [Preorder β]
    {a b : α} (f : α ↪o β) : f a ≈ f b ↔ a ≈ b := by
  simp [AntisymmRel]

theorem OrderEmbedding.antisymmRel_iff_eq {α β : Type*} [Preorder α] [PartialOrder β]
    {a b : α} (f : α ↪o β) : f a ≈ f b ↔ a = b := by
  simp

theorem not_le_of_le_of_not_le {α : Type*} [Preorder α] {a b c : α} (h₁ : a ≤ b) (h₂ : ¬ c ≤ b) :
    ¬ c ≤ a :=
  fun h ↦ h₂ (h.trans h₁)

theorem not_le_of_not_le_of_le {α : Type*} [Preorder α] {a b c : α} (h₁ : ¬ b ≤ a) (h₂ : b ≤ c) :
    ¬ c ≤ a :=
  fun h ↦ h₁ (h₂.trans h)

theorem range_fin {α} (f : ℕ → α) (n : ℕ) : range (f ∘ @Fin.val n) = f '' Iio n := by
  ext
  simp [Fin.exists_iff]

theorem Ordinal.Iio_natCast (n : ℕ) : Iio (n : Ordinal) = Nat.cast '' Iio n := by
  ext o
  constructor
  · intro ho
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 (ho.trans (nat_lt_omega0 _))
    simp_all
  · rintro ⟨o, ho, rfl⟩
    simp_all

theorem NatOrdinal.Iio_natCast (n : ℕ) : Iio (n : NatOrdinal) = Nat.cast '' Iio n := by
  rw [← Ordinal.toNatOrdinal_cast_nat]
  apply (Ordinal.Iio_natCast _).trans
  congr! 1
  exact Ordinal.toNatOrdinal_cast_nat _

namespace NatOrdinal

instance (o : NatOrdinal.{u}) : Small.{u} (Iio o) := inferInstanceAs (Small (Iio o.toOrdinal))

instance : CharZero NatOrdinal where
  cast_injective m n h := by
    apply_fun toOrdinal at h
    simpa using h

@[simp]
theorem zero_le (o : NatOrdinal) : 0 ≤ o :=
  Ordinal.zero_le o

theorem not_lt_zero (o : NatOrdinal) : ¬ o < 0 := by simp

@[simp]
theorem lt_one_iff_zero {o : NatOrdinal} : o < 1 ↔ o = 0 :=
  Ordinal.lt_one_iff_zero

theorem lt_add_iff {a b c : NatOrdinal} :
    a < b + c ↔ (∃ b' < b, a ≤ b' + c) ∨ ∃ c' < c, a ≤ b + c' :=
  Ordinal.lt_nadd_iff

theorem add_le_iff {a b c : NatOrdinal} :
     b + c ≤ a ↔ (∀ b' < b, b' + c < a) ∧ ∀ c' < c, b + c' < a :=
  Ordinal.nadd_le_iff

theorem lt_mul_iff {a b c : NatOrdinal} :
    c < a * b ↔ ∃ a' < a, ∃ b' < b, c + a' * b' ≤ a' * b + a * b' :=
  Ordinal.lt_nmul_iff

theorem mul_le_iff {a b c : NatOrdinal} :
    a * b ≤ c ↔ ∀ a' < a, ∀ b' < b, a' * b + a * b' < c + a' * b' :=
  Ordinal.nmul_le_iff

theorem mul_add_lt {a b a' b' : NatOrdinal} (ha : a' < a) (hb : b' < b) :
    a' * b + a * b' < a * b + a' * b' :=
  Ordinal.nmul_nadd_lt ha hb

theorem nmul_nadd_le {a b a' b' : NatOrdinal} (ha : a' ≤ a) (hb : b' ≤ b) :
    a' * b + a * b' ≤ a * b + a' * b' :=
  Ordinal.nmul_nadd_le ha hb

/-! ### `NatOrdinal` to `PGame` -/

/-- We make this private until we can build the `OrderEmbedding`. -/
private def toIGame' (o : NatOrdinal.{u}) : IGame.{u} :=
  {.range fun (⟨x, _⟩ : Iio o) ↦ toIGame' x | ∅}ᴵ
termination_by o

theorem toIGame'_def (o : NatOrdinal) : o.toIGame' = {toIGame' '' Iio o | ∅}ᴵ := by
  rw [toIGame']; simp [image_eq_range]

private theorem leftMoves_toIGame' (o : NatOrdinal) : o.toIGame'.leftMoves = toIGame' '' Iio o := by
  rw [toIGame'_def]; exact leftMoves_ofSets ..

private theorem rightMoves_toIGame' (o : NatOrdinal) : o.toIGame'.rightMoves = ∅ := by
  rw [toIGame'_def]; exact rightMoves_ofSets ..

private theorem toIGame'_strictMono : StrictMono toIGame' := by
  refine fun a b h ↦ lt_of_le_not_le ?_ (leftMove_lf ?_)
  · rw [le_iff_forall_lf]
    simpa [leftMoves_toIGame', rightMoves_toIGame'] using
      fun c hc ↦ (toIGame'_strictMono (hc.trans h)).not_le
  · rw [leftMoves_toIGame']
    exact ⟨a, h, rfl⟩
termination_by a => a

/-- The canonical map from `NatOrdinal` to `IGame`, sending `o` to `{Iio o | ∅}`. -/
def toIGame : NatOrdinal.{u} ↪o IGame.{u} :=
  .ofStrictMono NatOrdinal.toIGame' toIGame'_strictMono

theorem toIGame_def (o : NatOrdinal) : o.toIGame = {toIGame '' Iio o | ∅}ᴵ :=
  toIGame'_def o

@[simp]
theorem leftMoves_toIGame (o : NatOrdinal) : o.toIGame.leftMoves = toIGame '' Iio o :=
  leftMoves_toIGame' o

@[simp]
theorem rightMoves_toIGame (o : NatOrdinal) : o.toIGame.rightMoves = ∅ :=
  rightMoves_toIGame' o

theorem mem_leftMoves_toIGame_of_lt {a b : NatOrdinal} (h : a < b) :
    a.toIGame ∈ b.toIGame.leftMoves := by
  simpa

alias _root_.LT.lt.mem_leftMoves_toIGame := mem_leftMoves_toIGame_of_lt

@[simp] theorem toIGame_zero : toIGame 0 = 0 := by ext <;> simp
@[simp] theorem toIGame_one : toIGame 1 = 1 := by ext <;> simp [eq_comm]

theorem toIGame_le_iff {a b : NatOrdinal} : toIGame a ≤ toIGame b ↔ a ≤ b := by simp
theorem toIGame_lt_iff {a b : NatOrdinal} : toIGame a < toIGame b ↔ a < b := by simp
theorem toIGame_equiv_iff {a b : NatOrdinal} : toIGame a ≈ toIGame b ↔ a = b := by simp
theorem toIGame_inj {a b : NatOrdinal} : toIGame a = toIGame b ↔ a = b := by simp

@[simp]
theorem not_toIGame_fuzzy (a b : NatOrdinal) : ¬ toIGame a ‖ toIGame b := by
  simpa [IncompRel] using le_of_lt

@[simp]
theorem toIGame_nonneg (a : NatOrdinal) : 0 ≤ a.toIGame := by
  simpa using toIGame_le_iff.2 (NatOrdinal.zero_le a)

/-! ### `NatOrdinal` to `Game` -/

/-- Converts an ordinal into the corresponding game. -/
noncomputable def toGame : NatOrdinal.{u} ↪o Game.{u} where
  toFun o := .mk o.toIGame
  inj' a b := by simp [le_antisymm_iff]
  map_rel_iff' := toIGame_le_iff

@[simp] theorem mk_toPGame (o : NatOrdinal) : .mk o.toIGame = o.toGame := rfl

@[simp] theorem toGame_zero : toGame 0 = 0 := by simp [← mk_toPGame]
@[simp] theorem toGame_one : toGame 1 = 1 := by simp [← mk_toPGame]

theorem toGame_le_iff {a b : NatOrdinal} : toGame a ≤ toGame b ↔ a ≤ b := by simp
theorem toGame_lt_iff {a b : NatOrdinal} : toGame a < toGame b ↔ a < b := by simp
theorem toGame_inj {a b : NatOrdinal} : toGame a = toGame b ↔ a = b := by simp

@[simp]
theorem not_toGame_fuzzy (a b : NatOrdinal) : ¬ toGame a ‖ toGame b :=
  not_toIGame_fuzzy a b

@[simp]
theorem toGame_nonneg (a : NatOrdinal) : 0 ≤ a.toGame :=
  toIGame_nonneg a

/-- The natural addition of ordinals corresponds to their sum as games. -/
theorem toIGame_add (a b : NatOrdinal) : (a + b).toIGame ≈ a.toIGame + b.toIGame := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf]
  simp [NatOrdinal.lt_add_iff]
  constructor
  · rintro c (⟨d, _, hd⟩ | ⟨d, _, hd⟩)
    all_goals
    · rw [← toIGame_le_iff] at hd
      apply (hd.trans_lt _).not_le
      rw [(toIGame_add ..).lt_congr_left]
      simpa
  · rintro _ (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    all_goals
      rw [← (toIGame_add ..).le_congr_right]
      simpa
termination_by (a, b)

@[simp]
theorem toGame_add (a b : NatOrdinal) : (a + b).toGame = a.toGame + b.toGame :=
  Game.mk_eq (toIGame_add a b)

/-- The natural multiplication of ordinals corresponds to their product as games. -/
theorem toIGame_mul (a b : NatOrdinal) : (a * b).toIGame ≈ a.toIGame * b.toIGame := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf]
  simp [NatOrdinal.lt_mul_iff, mulOption]
  constructor
  · rintro _ e c hc d hd he rfl
    rw [← toIGame_le_iff, (toIGame_add ..).le_congr (toIGame_add ..)] at he
    rw [← add_le_add_iff_right (toIGame (c * d)), (add_congr_right (toIGame_mul ..)).le_congr_left]
    apply not_le_of_le_of_not_le he
    rw [(add_congr (toIGame_mul ..) (toIGame_mul ..)).le_congr_right, ← IGame.le_sub_iff_add_le]
    exact leftMove_lf <|
      mulOption_left_left_mem_leftMoves_mul hc.mem_leftMoves_toIGame hd.mem_leftMoves_toIGame
  · rintro _ _ _ c hc rfl d hd rfl rfl
    rw [IGame.le_sub_iff_add_le,
      ← (add_congr_right (toIGame_mul ..)).le_congr (add_congr (toIGame_mul ..) (toIGame_mul ..)),
      ← (toIGame_add ..).le_congr (toIGame_add ..), toIGame_le_iff, not_le]
    exact mul_add_lt hc hd
termination_by (a, b)

@[simp]
theorem toGame_mul (a b : NatOrdinal) : (a * b).toGame = .mk (a.toIGame * b.toIGame) :=
  Game.mk_eq (toIGame_mul a b)

/-! ### `NatCast` properties -/

@[simp]
theorem toGame_natCast : ∀ n : ℕ, toGame n = n
  | 0 => toGame_zero
  | n + 1 => by
    rw [Nat.cast_add, toGame_add, toGame_natCast, Nat.cast_one, toGame_one, Nat.cast_add_one]

/-- Note that the equality doesn't hold, as e.g. `↑2 = {1 | }`, while `toIGame 2 = {0, 1 | }`. -/
@[simp]
theorem toIGame_natCast_equiv (n : ℕ) : toIGame n ≈ n :=
  Game.mk_eq_mk.1 (by simp)

end NatOrdinal

open NatOrdinal

theorem IGame.natCast_strictMono : StrictMono ((↑) : ℕ → IGame) := by
  intro x y h
  rwa [← (toIGame_natCast_equiv x).lt_congr (toIGame_natCast_equiv y), toIGame_lt_iff, Nat.cast_lt]

theorem Game.natCast_strictMono : StrictMono ((↑) : ℕ → Game) := by
  intro x y h
  rwa [← toGame_natCast, ← toGame_natCast, toGame_lt_iff, Nat.cast_lt]

instance : CharZero IGame where
  cast_injective := natCast_strictMono.injective

@[simp]
theorem IGame.natCast_lt {m n : ℕ} : (m : IGame) < n ↔ m < n :=
  natCast_strictMono.lt_iff_lt

@[simp]
theorem IGame.natCast_le {m n : ℕ} : (m : IGame) ≤ n ↔ m ≤ n :=
  natCast_strictMono.le_iff_le

instance : CharZero Game where
  cast_injective := Game.natCast_strictMono.injective

/-- This represents the game `n = {Iio n | }`, unlike the `NatCast` instance which
represents `n + 1 = {n | }`. -/
def SGame.ordinalNat (n : ℕ) : SGame :=
  .mk n 0 (fun i ↦ ordinalNat i) nofun

@[simp]
theorem SGame.toIGame_ordinalNat (n : ℕ) : (ordinalNat n).toIGame = NatOrdinal.toIGame n := by
  rw [SGame.ordinalNat]
  apply IGame.ext
  · suffices Set.range ((toIGame ∘ ordinalNat) ∘ Fin.val) = NatOrdinal.toIGame '' Iio n by simpa
    rw [range_fin, NatOrdinal.Iio_natCast, image_image]
    congr!
    exact toIGame_ordinalNat _
  · simp

instance (n : ℕ) : Short (NatOrdinal.toIGame n) :=
  ⟨_, SGame.toIGame_ordinalNat n⟩

/-- Some natural number such that `x ≤ n`. -/
def SGame.upperBound (x : SGame) : ℕ :=
  (List.ofFn fun i ↦ upperBound (x.moveLeft i) + 1).max?.getD 0
termination_by x
decreasing_by sgame_wf

theorem SGame.le_upperBound (x : SGame) : x ≤ upperBound x := by
  apply toIGame_le_iff.2
  constructor <;> intro i
  · rw [upperBound, toIGame_natCast]
    apply not_le_of_lt
    refine lt_of_le_of_lt (le_upperBound (x.moveLeft i)) ?_
    rw [toIGame_natCast, IGame.natCast_lt]
    refine (Nat.succ_le_iff.1 <| List.le_max?_getD_of_mem ?_)
    simp
  · rw [rightMoves_natCast] at i
    exact i.elim0
termination_by x
decreasing_by sgame_wf

theorem IGame.Short.exists_lt_natCast (x : IGame) [Short x] : ∃ n : ℕ, x < n := by
  use (toSGame x).upperBound + 1
  conv_lhs => rw [← @toIGame_toSGame x]
  refine lt_of_le_of_lt (SGame.le_upperBound _) ?_
  simpa using zero_lt_one

theorem IGame.Short.exists_neg_natCast_lt (x : IGame) [Short x] : ∃ n : ℕ, -n < x := by
  obtain ⟨n, hn⟩ := exists_lt_natCast (-x)
  use n
  rwa [IGame.neg_lt]

notation "ω" => toIGame Ordinal.omega0.toNatOrdinal

theorem IGame.Short.lt_omega0 (x : IGame) [Short x] : x < ω := by
  obtain ⟨n, hn⟩ := exists_lt_natCast x
  apply hn.trans
  rw [← (toIGame_natCast_equiv n).lt_congr_left, toIGame_lt_iff, ← Ordinal.toNatOrdinal_cast_nat n]
  exact Ordinal.nat_lt_omega0 n

theorem IGame.Short.neg_omega0_lt (x : IGame) [Short x] : -ω < x := by
  rw [IGame.neg_lt]
  exact lt_omega0 _
