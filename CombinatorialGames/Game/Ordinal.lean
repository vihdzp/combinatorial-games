/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Basic
import CombinatorialGames.Game.Short
import CombinatorialGames.NatOrdinal.Basic
import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Ordinals as games

We define the canonical map `NatOrdinal → IGame`, where every ordinal is mapped to the game whose
left set consists of all previous ordinals. We make use of the type alias `NatOrdinal` rather than
`Ordinal`, as this map also preserves addition, and in the case of surreals, multiplication. The map
to surreals is defined in `NatOrdinal.toSurreal`.

We also prove some properties about `NatCast`, which is related to the previous construction by
`toIGame (↑n) ≈ ↑n`.

# Main declarations

- `NatOrdinal.toIGame`: The canonical map between `NatOrdinal` and `IGame`.
- `NatOrdinal.toGame`: The canonical map between `NatOrdinal` and `Game`.
-/

universe u

open Set IGame

noncomputable section

/-! ### Lemmas to upstream -/

@[simp]
theorem OrderEmbedding.antisymmRel_iff_antisymmRel {α β : Type*} [Preorder α] [Preorder β]
    {a b : α} (f : α ↪o β) : f a ≈ f b ↔ a ≈ b := by
  simp [AntisymmRel]

theorem OrderEmbedding.antisymmRel_iff_eq {α β : Type*} [Preorder α] [PartialOrder β]
    {a b : α} (f : α ↪o β) : f a ≈ f b ↔ a = b := by
  simp

namespace NatOrdinal

/-! ### `NatOrdinal` to `IGame` -/

/-- We make this private until we can build the `OrderEmbedding`. -/
private def toIGame' (o : NatOrdinal.{u}) : IGame.{u} :=
  !{.range fun (⟨x, _⟩ : Iio o) ↦ toIGame' x | ∅}
termination_by o

private theorem toIGame'_def (o : NatOrdinal) : o.toIGame' = !{toIGame' '' Iio o | ∅} := by
  rw [toIGame']; simp [image_eq_range]

private theorem leftMoves_toIGame' (o : NatOrdinal) : o.toIGame'ᴸ = toIGame' '' Iio o := by
  rw [toIGame'_def]; exact leftMoves_ofSets ..

private theorem rightMoves_toIGame' (o : NatOrdinal) : o.toIGame'ᴿ = ∅ := by
  rw [toIGame'_def]; exact rightMoves_ofSets ..

private theorem toIGame'_strictMono : StrictMono toIGame' := by
  refine fun a b h ↦ lt_of_le_not_ge ?_ (leftMove_lf ?_)
  · rw [le_iff_forall_lf]
    simpa [leftMoves_toIGame', rightMoves_toIGame'] using
      fun c hc ↦ (toIGame'_strictMono (hc.trans h)).not_ge
  · rw [leftMoves_toIGame']
    exact ⟨a, h, rfl⟩
termination_by a => a

/-- The canonical map from `NatOrdinal` to `IGame`, sending `o` to `{Iio o | ∅}`. -/
def toIGame : NatOrdinal.{u} ↪o IGame.{u} :=
  .ofStrictMono NatOrdinal.toIGame' toIGame'_strictMono

instance : Coe NatOrdinal IGame where
  coe x := toIGame x

theorem toIGame_def (o : NatOrdinal) : o.toIGame = !{toIGame '' Iio o | ∅} :=
  toIGame'_def o

@[simp]
theorem leftMoves_toIGame (o : NatOrdinal) : o.toIGameᴸ = toIGame '' Iio o :=
  leftMoves_toIGame' o

@[simp, game_cmp]
theorem rightMoves_toIGame (o : NatOrdinal) : o.toIGameᴿ = ∅ :=
  rightMoves_toIGame' o

@[game_cmp]
theorem forall_leftMoves_toIGame_natCast {P : IGame → Prop} {n : ℕ} :
    (∀ x ∈ (toIGame n)ᴸ, P x) ↔ ∀ m < n, P (toIGame m) := by
  simp

@[game_cmp]
theorem exists_leftMoves_toIGame_natCast {P : IGame → Prop} {n : ℕ} :
    (∃ x ∈ (toIGame n)ᴸ, P x) ↔ (∃ m < n, P (toIGame m)) := by
  simp

@[game_cmp]
theorem forall_leftMoves_toIGame_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∀ x ∈ (toIGame ofNat(n))ᴸ, P x) ↔ ∀ m < n, P (toIGame m) :=
  forall_leftMoves_toIGame_natCast

@[game_cmp]
theorem exists_leftMoves_toIGame_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∃ x ∈ (toIGame ofNat(n))ᴸ, P x) ↔ ∃ m < n, P (toIGame m) :=
  exists_leftMoves_toIGame_natCast

theorem mem_leftMoves_toIGame_of_lt {a b : NatOrdinal} (h : a < b) :
    a.toIGame ∈ b.toIGameᴸ := by
  simpa

@[simp, game_cmp] theorem toIGame_zero : toIGame 0 = 0 := by ext p; cases p <;> simp
@[simp, game_cmp] theorem toIGame_one : toIGame 1 = 1 := by ext p; cases p <;> simp [eq_comm]

@[simp]
theorem not_toIGame_fuzzy (a b : NatOrdinal) : ¬ toIGame a ‖ toIGame b := by
  simpa [IncompRel] using le_of_lt

@[simp]
theorem toIGame_nonneg (a : NatOrdinal) : 0 ≤ a.toIGame := by
  simpa using toIGame.monotone (NatOrdinal.zero_le a)

/-! ### `NatOrdinal` to `Game` -/

/-- Converts an ordinal into the corresponding game. -/
noncomputable def toGame : NatOrdinal.{u} ↪o Game.{u} :=
  .ofStrictMono (fun o ↦ .mk o.toIGame) fun _ _ h ↦ toIGame.strictMono h

instance : Coe NatOrdinal Game where
  coe x := toGame x

@[simp] theorem _root_.Game.mk_natOrdinal_toIGame (o : NatOrdinal) : .mk o.toIGame = o.toGame := rfl

theorem toGame_def (o : NatOrdinal) : o.toGame = !{toGame '' Iio o | ∅} := by
  rw [← Game.mk_natOrdinal_toIGame, toIGame_def]
  simp [image_image]

@[simp] theorem toGame_zero : toGame 0 = 0 := by simp [← Game.mk_natOrdinal_toIGame]
@[simp] theorem toGame_one : toGame 1 = 1 := by simp [← Game.mk_natOrdinal_toIGame]

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
    · rw [← toIGame.le_iff_le] at hd
      apply (hd.trans_lt _).not_ge
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
    rw [← toIGame.le_iff_le, (toIGame_add ..).le_congr (toIGame_add ..)] at he
    rw [← add_le_add_iff_right (toIGame (c * d)), (add_congr_right (toIGame_mul ..)).le_congr_left]
    apply not_le_of_le_of_not_le he
    rw [(add_congr (toIGame_mul ..) (toIGame_mul ..)).le_congr_right, ← IGame.le_sub_iff_add_le]
    exact leftMove_lf <| mulOption_mem_moves_mul
      (mem_leftMoves_toIGame_of_lt hc) (mem_leftMoves_toIGame_of_lt hd)
  · rintro _ _ _ c hc rfl d hd rfl rfl
    rw [IGame.le_sub_iff_add_le,
      ← (add_congr_right (toIGame_mul ..)).le_congr (add_congr (toIGame_mul ..) (toIGame_mul ..)),
      ← (toIGame_add ..).le_congr (toIGame_add ..), toIGame.le_iff_le, not_le]
    exact mul_add_lt hc hd
termination_by (a, b)

@[simp]
theorem toGame_mul (a b : NatOrdinal) : (a * b).toGame = .mk (a.toIGame * b.toIGame) :=
  Game.mk_eq (toIGame_mul a b)

/-- `NatOrdinal.toGame` as an `OrderAddMonoidHom`. -/
@[simps]
def toGameAddHom : NatOrdinal →+o Game where
  toFun := toGame
  map_zero' := toGame_zero
  map_add' := toGame_add
  monotone' := toGame.monotone

/-! ### `NatCast` properties -/

@[simp]
theorem toGame_natCast : ∀ n : ℕ, toGame n = n :=
  map_natCast' toGameAddHom toGame_one

/-- Note that the equality doesn't hold, as e.g. `↑2 = {1 | }`, while `toIGame 2 = {0, 1 | }`. -/
theorem toIGame_natCast_equiv (n : ℕ) : toIGame n ≈ n :=
  Game.mk_eq_mk.1 (by simp)

end NatOrdinal

namespace IGame
open NatOrdinal

theorem Short.exists_lt_natCast (x : IGame) [Short x] : ∃ n : ℕ, x < n := by
  have (y : xᴸ) : ∃ n : ℕ, y.1 < n := by
    have := Short.of_mem_moves y.2
    exact Short.exists_lt_natCast y
  choose f hf using this
  obtain ⟨n, hn⟩ := (finite_range f).bddAbove
  refine ⟨n + 1, lt_of_le_of_lt ?_ (IGame.natCast_lt.2 (Nat.lt_succ_self _))⟩
  rw [le_iff_forall_lf]
  simpa using fun y hy ↦ ((hf ⟨y, hy⟩).trans_le (mod_cast hn ⟨⟨y, hy⟩, rfl⟩)).not_ge
termination_by x
decreasing_by igame_wf

theorem Short.exists_neg_natCast_lt (x : IGame) [Short x] : ∃ n : ℕ, -n < x := by
  obtain ⟨n, hn⟩ := exists_lt_natCast (-x)
  use n
  rwa [IGame.neg_lt]

local notation "ω" => toIGame (NatOrdinal.of Ordinal.omega0)

theorem Short.lt_omega0 (x : IGame) [Short x] : x < ω := by
  obtain ⟨n, hn⟩ := exists_lt_natCast x
  apply hn.trans
  rw [← (toIGame_natCast_equiv n).lt_congr_left, toIGame.lt_iff_lt, ← NatOrdinal.of_natCast n]
  exact Ordinal.nat_lt_omega0 n

theorem Short.neg_omega0_lt (x : IGame) [Short x] : -ω < x := by
  rw [IGame.neg_lt]
  exact lt_omega0 _

end IGame
