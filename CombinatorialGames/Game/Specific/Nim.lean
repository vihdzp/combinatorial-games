/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Birthday
import CombinatorialGames.Game.Concrete
import CombinatorialGames.Game.Small
import CombinatorialGames.Nimber.Basic

/-!
# Nim

In the game of `nim o`, for `o` an ordinal number, both players may move to `nim a` for any `a < o`.

This is an impartial game; in fact, in a strong sense, it's the simplest impartial game, as by the
Sprague-Grundy theorem, any other impartial game is equivalent to some game of nim. As such, many
results on Nim are proven in `Game.Impartial.Grundy`.

We define `nim` in terms of a `Nimber` rather than an `Ordinal`, as this makes the results
`nim (a + b) ≈ nim a + nim b` and `nim (a * b) ≈ nim a * nim b` much easier to state.
-/

universe u

open Nimber Set

namespace ConcreteGame

/-- The game of nim as a `ConcreteGame`. -/
abbrev nim : ConcreteGame Nimber where
  moves _ := Iio

instance : IsWellFounded _ nim.IsOption :=
  isWellFounded_isOption_of_eq (· < ·) fun _ _ ↦ rfl

end ConcreteGame

namespace IGame

/-! ### Nim game -/

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
take a positive number of stones from it on their turn. -/
noncomputable def nim : Nimber.{u} → IGame.{u} :=
  ConcreteGame.nim.toIGame

theorem nim_def (o : Nimber) : nim o = !{fun _ ↦ nim '' Iio o} :=
  ConcreteGame.toIGame_def' ..

@[simp]
theorem moves_nim (p : Player) (o : Nimber) : (nim o).moves p = nim '' Iio o :=
  ConcreteGame.moves_toIGame ..

theorem forall_moves_left_nim {P : IGame → Prop} {o : Nimber} :
    (∀ x ∈ (nim o).moves_left, P x) ↔ (∀ a < o, P (nim a)) := by
  simp

theorem forall_moves_right_nim {P : IGame → Prop} {o : Nimber} :
    (∀ x ∈ (nim o).moves_right, P x) ↔ (∀ a < o, P (nim a)) := by
  simp

theorem exists_moves_left_nim {P : IGame → Prop} {o : Nimber} :
    (∃ x ∈ (nim o).moves_left, P x) ↔ (∃ a < o, P (nim a)) := by
  simp

theorem exists_moves_right_nim {P : IGame → Prop} {o : Nimber} :
    (∃ x ∈ (nim o).moves_right, P x) ↔ (∃ a < o, P (nim a)) := by
  simp

@[game_cmp]
theorem forall_moves_left_nim_natCast {P : IGame → Prop} {n : ℕ} :
    (∀ x ∈ moves_left (nim (∗n)), P x) ↔ ∀ m < n, P (nim (∗m)) := by
  simp [← of_image_Iio, ← NatOrdinal.natCast_image_Iio']

@[game_cmp]
theorem forall_moves_right_nim_natCast {P : IGame → Prop} {n : ℕ} :
    (∀ x ∈ moves_right (nim (∗n)), P x) ↔ ∀ m < n, P (nim (∗m)) := by
  simp [← of_image_Iio, ← NatOrdinal.natCast_image_Iio']

@[game_cmp]
theorem exists_moves_left_nim_natCast {P : IGame → Prop} {n : ℕ} :
    (∃ x ∈ moves_left (nim (∗n)), P x) ↔ (∃ m < n, P (nim (∗m))) := by
  simp [← of_image_Iio, ← NatOrdinal.natCast_image_Iio']

@[game_cmp]
theorem exists_moves_right_nim_natCast {P : IGame → Prop} {n : ℕ} :
    (∃ x ∈ moves_right (nim (∗n)), P x) ↔ (∃ m < n, P (nim (∗m))) := by
  simp [← of_image_Iio, ← NatOrdinal.natCast_image_Iio']

@[game_cmp]
theorem forall_moves_left_nim_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∀ x ∈ moves_left (nim (∗ofNat(n))), P x) ↔ ∀ m < n, P (nim (∗m)) :=
  forall_moves_left_nim_natCast

@[game_cmp]
theorem forall_moves_right_nim_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∀ x ∈ moves_right (nim (∗ofNat(n))), P x) ↔ ∀ m < n, P (nim (∗m)) :=
  forall_moves_right_nim_natCast

@[game_cmp]
theorem exists_moves_left_nim_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∃ x ∈ moves_left (nim (∗ofNat(n))), P x) ↔ ∃ m < n, P (nim (∗m)) :=
  exists_moves_left_nim_natCast

@[game_cmp]
theorem exists_moves_right_nim_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∃ x ∈ moves_right (nim (∗ofNat(n))), P x) ↔ ∃ m < n, P (nim (∗m)) :=
  exists_moves_right_nim_natCast

theorem mem_moves_left_nim_of_lt {a b : Nimber} (h : a < b) : (nim a) ∈ (nim b).moves_left := by
  simpa using ⟨_, h, rfl⟩

theorem mem_moves_right_nim_of_lt {a b : Nimber} (h : a < b) : (nim a) ∈ (nim b).moves_right := by
  simpa using ⟨_, h, rfl⟩

theorem nim_injective : Function.Injective nim := by
  intro a b h'
  obtain h | rfl | h := lt_trichotomy a b
  on_goal 2 => rfl
  all_goals cases self_notMem_moves _ _ <| h' ▸ mem_moves_left_nim_of_lt h

@[simp] theorem nim_inj {a b : Nimber} : nim a = nim b ↔ a = b := nim_injective.eq_iff

@[simp, game_cmp] theorem nim_zero : nim 0 = 0 := by ext p; cases p <;> simp
@[simp, game_cmp] theorem nim_one : nim 1 = ⋆ := by ext p; cases p <;> simp [eq_comm]

@[simp]
theorem birthday_nim (o : Nimber) : (nim o).birthday = o := by
  rw [nim_def, ofSets_eq_ofSets_cases, birthday_ofSets, max_self, image_image]
  conv_rhs => rw [← iSup_succ o, iSup]
  simp_rw [Function.comp_apply, ← image_eq_range]
  congr!
  rw [birthday_nim]
termination_by o

@[simp, game_cmp]
theorem neg_nim (o : Nimber) : -nim o = nim o :=
  ConcreteGame.neg_toIGame rfl ..

protected instance Impartial.nim (o : Nimber) : Impartial (nim o) :=
  ConcreteGame.impartial_toIGame rfl ..

protected instance Dicotic.nim (o : Nimber) : Dicotic (nim o) := by
  rw [dicotic_def]
  simpa using fun a ha ↦ .nim a
termination_by o

private theorem nim_fuzzy_of_lt {a b : Nimber} (h : a < b) : nim a ‖ nim b :=
  Impartial.left_fuzzy (mem_moves_left_nim_of_lt h)

@[simp]
theorem nim_equiv_iff {a b : Nimber} : nim a ≈ nim b ↔ a = b := by
  obtain h | rfl | h := lt_trichotomy a b
  · simp_rw [h.ne, (nim_fuzzy_of_lt h).not_antisymmRel]
  · simp
  · simp_rw [h.ne', (nim_fuzzy_of_lt h).symm.not_antisymmRel]

@[simp]
theorem nim_fuzzy_iff {a b : Nimber} : nim a ‖ nim b ↔ a ≠ b := by
  rw [← Impartial.not_equiv_iff, ne_eq, not_iff_not, nim_equiv_iff]

end IGame
