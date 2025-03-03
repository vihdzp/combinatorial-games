/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.IGame.Basic
import CombinatorialGames.Mathlib.AntisymmRel
import Mathlib.SetTheory.Ordinal.NaturalOps

/-!
# Ordinals as games

We define the canonical map `NatOrdinal → IGame`, where every ordinal is mapped to the game whose
left set consists of all previous ordinals. We make use of the type alias `NatOrdinal` rather than
`Ordinal`, as this map also preserves addition, and in the case of surreals, multiplication.

The map to surreals is defined in `NatOrdinal.toSurreal`.

# Main declarations

- `NatOrdinal.toIGame`: The canonical map between `NatOrdinal` and `IGame`.
- `NatOrdinal.toGame`: The canonical map between `NatOrdinal` and `Game`.
-/

universe u

open Set IGame
open scoped NaturalOps IGame

noncomputable section

-- TODO: upstream
@[simp]
theorem OrderEmbedding.antisymmRel_iff_antisymmRel {α β : Type*} [Preorder α] [Preorder β]
    {a b : α} (f : α ↪o β) : f a ≈ f b ↔ a ≈ b := by
  simp [AntisymmRel]

theorem OrderEmbedding.antisymmRel_iff_eq {α β : Type*} [Preorder α] [PartialOrder β]
    {a b : α} (f : α ↪o β) : f a ≈ f b ↔ a = b := by
  simp

namespace NatOrdinal

instance (o : NatOrdinal.{u}) : Small.{u} (Iio o) := inferInstanceAs (Small (Iio o.toOrdinal))

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

@[simp] theorem toIGame_zero : toIGame 0 = 0 := by ext <;> simp
@[simp] theorem toIGame_one : toIGame 1 = 1 := by ext <;> simp [eq_comm]

theorem toIGame_le_iff {a b : NatOrdinal} : toIGame a ≤ toIGame b ↔ a ≤ b := by simp
theorem toIGame_lt_iff {a b : NatOrdinal} : toIGame a < toIGame b ↔ a < b := by simp
theorem toIGame_equiv_iff {a b : NatOrdinal} : toIGame a ≈ toIGame b ↔ a = b := by simp
theorem toIGame_inj {a b : NatOrdinal} : toIGame a = toIGame b ↔ a = b := by simp

@[simp]
theorem not_toIGame_fuzzy (a b : NatOrdinal) : ¬ toIGame a ‖ toIGame b := by
  simpa [CompRel] using le_of_lt

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
      rw [(toIGame_add _ _).lt_congr_left]
      simpa
  · rintro _ (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    all_goals
      rw [← (toIGame_add _ _).le_congr_right]
      simpa
termination_by (a, b)

@[simp]
theorem toGame_add (a b : NatOrdinal) : (a + b).toGame = a.toGame + b.toGame :=
  Game.mk_eq (toIGame_add a b)

-- TODO: fix this once game multiplication is ported

/-
/-- The natural multiplication of ordinals corresponds to their product as pre-games. -/
theorem toPGame_nmul (a b : NatOrdinal) : (a ⨳ b).toPGame ≈ a.toPGame * b.toPGame := by
  refine ⟨le_of_forall_lf (fun i ↦ ?_) isEmptyElim, le_of_forall_lf (fun i ↦ ?_) isEmptyElim⟩
  · rw [toPGame_moveLeft']
    rcases lt_nmul_iff.1 (toLeftMovesToPGame_symm_lt i) with ⟨c, hc, d, hd, h⟩
    rw [← toPGame_le_iff, le_iff_game_le, mk_toPGame, mk_toPGame, toGame_nadd _ _, toGame_nadd _ _,
      ← le_sub_iff_add_le] at h
    refine lf_of_le_of_lf h <| (lf_congr_left ?_).1 <| moveLeft_lf <| toLeftMovesMul <| Sum.inl
      ⟨toLeftMovesToPGame ⟨c, hc⟩, toLeftMovesToPGame ⟨d, hd⟩⟩
    simp only [mul_moveLeft_inl, toPGame_moveLeft', Equiv.symm_apply_apply, equiv_iff_game_eq,
      quot_sub, quot_add]
    repeat rw [← game_eq (toPGame_nmul _ _)]
    rfl
  · apply leftMoves_mul_cases i _ isEmptyElim
    intro i j
    rw [mul_moveLeft_inl, toPGame_moveLeft', toPGame_moveLeft', lf_iff_game_lf,
      quot_sub, quot_add, ← Game.not_le, le_sub_iff_add_le]
    repeat rw [← game_eq (toPGame_nmul _ _)]
    simp_rw [mk_toPGame, ← toGame_nadd]
    apply toPGame_lf (nmul_nadd_lt _ _) <;>
    exact toLeftMovesToPGame_symm_lt _
termination_by (a, b)

theorem toGame_nmul (a b : NatOrdinal) : (a ⨳ b).toGame = ⟦a.toPGame * b.toPGame⟧ :=
  game_eq (toPGame_nmul a b)
-/

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
