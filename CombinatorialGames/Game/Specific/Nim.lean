/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel, Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Game.Birthday
public import CombinatorialGames.Game.Classes
public import CombinatorialGames.Game.Graph
public import CombinatorialGames.Nimber.Basic

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

@[expose] public section

open Nimber Set

namespace GameGraph

/-- The game of nim as a `GameGraph`. -/
abbrev nim : GameGraph Nimber where
  moves _ := Iio

instance : IsWellFounded _ nim.IsOption :=
  isWellFounded_isOption_of_eq (· < ·) fun _ _ ↦ rfl

end GameGraph

namespace IGame

/-! ### Nim game -/

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
take a positive number of stones from it on their turn. -/
noncomputable def nim : Nimber.{u} → IGame.{u} :=
  GameGraph.nim.toIGame

theorem nim_def (o : Nimber) : nim o = !{fun _ ↦ nim '' Iio o} :=
  GameGraph.toIGame_def' ..

@[simp]
theorem moves_nim (p : Player) (o : Nimber) : (nim o).moves p = nim '' Iio o :=
  GameGraph.moves_toIGame ..

theorem forall_moves_nim {p : Player} {P : IGame → Prop} {o : Nimber} :
    (∀ x ∈ (nim o).moves p, P x) ↔ (∀ a < o, P (nim a)) := by
  simp

theorem exists_moves_nim {p : Player} {P : IGame → Prop} {o : Nimber} :
    (∃ x ∈ (nim o).moves p, P x) ↔ (∃ a < o, P (nim a)) := by
  simp

@[game_cmp]
theorem forall_moves_nim_natCast {p : Player} {P : IGame → Prop} {n : ℕ} :
    (∀ x ∈ (nim (∗n)).moves p, P x) ↔ ∀ m < n, P (nim (∗m)) := by
  simp [← of_image_Iio, ← NatOrdinal.natCast_image_Iio']

@[game_cmp]
theorem exists_moves_nim_natCast {p : Player} {P : IGame → Prop} {n : ℕ} :
    (∃ x ∈ (nim (∗n)).moves p, P x) ↔ (∃ m < n, P (nim (∗m))) := by
  simp [← of_image_Iio, ← NatOrdinal.natCast_image_Iio']

@[game_cmp]
theorem forall_moves_nim_ofNat {p : Player} {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∀ x ∈ (nim (∗ofNat(n))).moves p, P x) ↔ ∀ m < n, P (nim (∗m)) :=
  forall_moves_nim_natCast

@[game_cmp]
theorem exists_moves_nim_ofNat {p : Player} {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∃ x ∈ (nim (∗ofNat(n))).moves p, P x) ↔ ∃ m < n, P (nim (∗m)) :=
  exists_moves_nim_natCast

theorem mem_moves_nim_of_lt {a b : Nimber} (p : Player) (h : a < b) :
    (nim a) ∈ (nim b).moves p := by
  simpa using ⟨_, h, rfl⟩

theorem nim_injective : Function.Injective nim := by
  intro a b h'
  obtain h | rfl | h := lt_trichotomy a b
  on_goal 2 => rfl
  all_goals cases self_notMem_moves _ _ <| h' ▸ mem_moves_nim_of_lt default h

@[simp] theorem nim_inj {a b : Nimber} : nim a = nim b ↔ a = b := nim_injective.eq_iff

@[simp, game_cmp] theorem nim_zero : nim 0 = 0 := by ext p; cases p <;> simp
@[simp, game_cmp] theorem nim_one : nim 1 = ⋆ := by ext p; cases p <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem birthday_nim (o : Nimber) : (nim o).birthday = .of o.val := by
  rw [nim_def, birthday_ofSets_const, image_image, sSup_image']
  convert iSup_succ o with _ x
  cases x
  exact congrArg _ (birthday_nim _)
termination_by o

@[simp, game_cmp]
theorem neg_nim (o : Nimber) : -nim o = nim o :=
  GameGraph.neg_toIGame rfl ..

protected instance Impartial.nim (o : Nimber) : Impartial (nim o) :=
  GameGraph.impartial_toIGame rfl ..

protected instance Dicotic.nim (o : Nimber) : Dicotic (nim o) := by
  rw [dicotic_def]
  simpa using fun a ha ↦ .nim a
termination_by o

private theorem nim_fuzzy_of_lt {a b : Nimber} (h : a < b) : nim a ‖ nim b :=
  Impartial.fuzzy_of_mem_moves (mem_moves_nim_of_lt default h)

@[simp]
theorem nim_equiv_iff {a b : Nimber} : nim a ≈ nim b ↔ a = b := by
  obtain h | rfl | h := lt_trichotomy a b
  · simp_rw [h.ne, (nim_fuzzy_of_lt h).not_antisymmRel]
  · simp
  · simp_rw [h.ne', (nim_fuzzy_of_lt h).symm.not_antisymmRel]

@[simp]
theorem nim_fuzzy_iff {a b : Nimber} : nim a ‖ nim b ↔ a ≠ b := by
  rw [← Impartial.not_equiv_iff, ne_eq, not_iff_not, nim_equiv_iff]

theorem _root_.Game.birthday_nim (o : Nimber) : Game.birthday (.mk (nim o)) = .of o.val := by
  apply ((Game.birthday_mk_le _).trans_eq (IGame.birthday_nim o)).antisymm
  simp_rw [Game.le_birthday_iff, Game.mk_eq_mk]
  refine fun x hxo ↦ le_of_not_gt fun hxb ↦ ?_
  induction o using Nimber.induction generalizing x with | _ o iho
  have hu {u : IGame} (hu : u ∈ (nim (.of x.birthday.val))ᴸ) : u ⧏ x := by
    rw [moves_nim] at hu
    obtain ⟨o', ho', rfl⟩ := hu
    grw [hxo]
    simpa using (ho'.trans hxb).ne'
  obtain ⟨y, hy, hxy⟩ | ⟨y, hy, hyx⟩ := (le_def.1 hxo.le).2 _ (mem_moves_nim_of_lt _ hxb)
  · exact hu hy hxy
  have hyo := lf_right_of_le hxo.ge hy
  replace hy := Subposition.of_mem_moves hy
  induction y using IsWellFounded.induction Subposition with | ind y ihy
  obtain ⟨w, hw, how⟩ | ⟨w, hw, hxy⟩ := lf_iff_exists_le.1 hyo
  · refine lf_of_le_left ?_ hw hyx
    rw [le_iff_forall_lf]
    constructor <;> intro k hk hk'
    · exact hu hk ((hxo.le.trans how).trans hk')
    · have hky := Subposition.trans (.of_mem_moves hk) (.of_mem_moves hw)
      exact ihy k hky hk' (lf_right_of_le how hk) (hky.trans hy)
  · rw [moves_nim] at hw
    obtain ⟨o', ho', rfl⟩ := hw
    obtain rfl := nim_equiv_iff.1 (Impartial.le_iff_equiv.1 (hxy.trans hyx))
    exact iho _ ho' y ⟨hyx, hxy⟩ (birthday_lt_of_subposition hy)

end IGame
end
