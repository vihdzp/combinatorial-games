/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Markus Himmel, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Birthday
import CombinatorialGames.Game.Impartial
import CombinatorialGames.Mathlib.Neg
import CombinatorialGames.Nimber.Basic

/-!
# Nim and the Sprague-Grundy theorem

In the game of `nim o`, for `o` an ordinal number, both players may move to `nim a` for any `a < o`.

We also define a Grundy value for an impartial game `x` and prove the Sprague-Grundy theorem, that
`x` is equivalent to `nim (grundy x)`. Finally, we prove that the grundy value of a sum `x + y`
corresponds to the nimber sum of the individual grundy values.
-/

universe u

open Nimber Set

noncomputable section

theorem Nimber.Iio_toNimber (n : ℕ) : Iio (∗n) = Ordinal.toNimber '' Iio n := by aesop

namespace IGame

/-! ### Nim game -/

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
take a positive number of stones from it on their turn. -/
def nim (o : Nimber.{u}) : IGame.{u} :=
  {.range fun (⟨x, _⟩ : Iio o) ↦ nim x | .range fun (⟨x, _⟩ : Iio o) ↦ nim x}ᴵ
termination_by o

theorem nim_def (o : Nimber) : nim o = {nim '' Iio o | nim '' Iio o}ᴵ := by
  rw [nim]; simp [image_eq_range]

@[simp]
theorem leftMoves_nim (o : Nimber) : (nim o).leftMoves = nim '' Iio o := by
  rw [nim_def]; exact leftMoves_ofSets ..

@[simp]
theorem rightMoves_nim (o : Nimber) : (nim o).rightMoves = nim '' Iio o := by
  rw [nim_def]; exact rightMoves_ofSets ..

theorem forall_leftMoves_nim {P : IGame → Prop} {o : Nimber} :
    (∀ x ∈ (nim o).leftMoves, P x) ↔ (∀ a < o, P (nim a)) := by
  simp

theorem forall_rightMoves_nim {P : IGame → Prop} {o : Nimber} :
    (∀ x ∈ (nim o).rightMoves, P x) ↔ (∀ a < o, P (nim a)) := by
  simp

theorem exists_leftMoves_nim {P : IGame → Prop} {o : Nimber} :
    (∃ x ∈ (nim o).leftMoves, P x) ↔ (∃ a < o, P (nim a)) := by
  simp

theorem exists_rightMoves_nim {P : IGame → Prop} {o : Nimber} :
    (∃ x ∈ (nim o).rightMoves, P x) ↔ (∃ a < o, P (nim a)) := by
  simp

@[game_cmp]
theorem forall_leftMoves_nim_natCast {P : IGame → Prop} {n : ℕ} :
    (∀ x ∈ leftMoves (nim (∗n)), P x) ↔ ∀ m < n, P (nim (∗m)) := by
  rw [leftMoves_nim, Nimber.Iio_toNimber, Ordinal.Iio_natCast]
  simp

@[game_cmp]
theorem forall_rightMoves_nim_natCast {P : IGame → Prop} {n : ℕ} :
    (∀ x ∈ rightMoves (nim (∗n)), P x) ↔ ∀ m < n, P (nim (∗m)) := by
  rw [rightMoves_nim, Nimber.Iio_toNimber, Ordinal.Iio_natCast]
  simp

@[game_cmp]
theorem exists_leftMoves_nim_natCast {P : IGame → Prop} {n : ℕ} :
    (∃ x ∈ leftMoves (nim (∗n)), P x) ↔ (∃ m < n, P (nim (∗m))) := by
  rw [leftMoves_nim, Nimber.Iio_toNimber, Ordinal.Iio_natCast]
  simp

@[game_cmp]
theorem exists_rightMoves_nim_natCast {P : IGame → Prop} {n : ℕ} :
    (∃ x ∈ rightMoves (nim (∗n)), P x) ↔ (∃ m < n, P (nim (∗m))) := by
  rw [rightMoves_nim, Nimber.Iio_toNimber, Ordinal.Iio_natCast]
  simp

@[game_cmp]
theorem forall_leftMoves_nim_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∀ x ∈ leftMoves (nim (∗ofNat(n))), P x) ↔ ∀ m < n, P (nim (∗m)) :=
  forall_leftMoves_nim_natCast

@[game_cmp]
theorem forall_rightMoves_nim_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∀ x ∈ rightMoves (nim (∗ofNat(n))), P x) ↔ ∀ m < n, P (nim (∗m)) :=
  forall_rightMoves_nim_natCast

@[game_cmp]
theorem exists_leftMoves_nim_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∃ x ∈ leftMoves (nim (∗ofNat(n))), P x) ↔ ∃ m < n, P (nim (∗m)) :=
  exists_leftMoves_nim_natCast

@[game_cmp]
theorem exists_rightMoves_nim_ofNat {P : IGame → Prop} {n : ℕ} [n.AtLeastTwo] :
    (∃ x ∈ rightMoves (nim (∗ofNat(n))), P x) ↔ ∃ m < n, P (nim (∗m)) :=
  exists_rightMoves_nim_natCast

theorem mem_leftMoves_nim_of_lt {a b : Nimber} (h : a < b) : (nim a) ∈ (nim b).leftMoves := by
  simpa using ⟨_, h, rfl⟩

theorem mem_rightMoves_nim_of_lt {a b : Nimber} (h : a < b) : (nim a) ∈ (nim b).rightMoves := by
  simpa using ⟨_, h, rfl⟩

theorem nim_injective : Function.Injective nim := by
  intro a b h'
  obtain h | rfl | h := lt_trichotomy a b
  on_goal 2 => rfl
  all_goals cases self_notMem_leftMoves _ <| h' ▸ mem_leftMoves_nim_of_lt h

@[simp] theorem nim_inj {a b : Nimber} : nim a = nim b ↔ a = b := nim_injective.eq_iff

@[simp, game_cmp] theorem nim_zero : nim 0 = 0 := by ext <;> simp
@[simp, game_cmp] theorem nim_one : nim 1 = ⋆ := by ext <;> simp [eq_comm]

@[simp]
theorem birthday_nim (o : Nimber) : (nim o).birthday = o := by
  rw [nim_def, birthday_ofSets, max_self, image_image]
  conv_rhs => rw [← iSup_succ o, iSup]
  simp_rw [Function.comp_apply, ← image_eq_range]
  congr!
  rw [birthday_nim]
termination_by o

@[simp, game_cmp]
theorem neg_nim (o : Nimber) : -nim o = nim o := by
  rw [nim_def, neg_ofSets]
  congr!
  all_goals
    rw [← image_neg_eq_neg, image_image]
    congr!
    rw [neg_nim]
termination_by o

protected instance Impartial.nim (o : Nimber) : Impartial (nim o) := by
  apply Impartial.mk' (by simp)
  all_goals
    intro x hx
    simp only [leftMoves_nim, rightMoves_nim] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact .nim a
termination_by o

private theorem nim_fuzzy_of_lt {a b : Nimber} (h : a < b) : nim a ‖ nim b :=
  Impartial.leftMove_fuzzy (mem_leftMoves_nim_of_lt h)

@[simp]
theorem nim_equiv_iff {a b : Nimber} : nim a ≈ nim b ↔ a = b := by
  obtain h | rfl | h := lt_trichotomy a b
  · simp_rw [h.ne, (nim_fuzzy_of_lt h).not_antisymmRel]
  · simp
  · simp_rw [h.ne', (nim_fuzzy_of_lt h).symm.not_antisymmRel]

@[simp]
theorem nim_fuzzy_iff {a b : Nimber} : nim a ‖ nim b ↔ a ≠ b := by
  rw [← Impartial.not_equiv_iff, ne_eq, not_iff_not, nim_equiv_iff]

/-! ### Grundy value -/

/-- The left Grundy value of a game is recursively defined as the minimum excluded value
(the infimum of the complement) of the left Grundy values of its left options.

This is an auxiliary definition for reasoning about games not yet known to be impartial. Use
`Impartial.grundy` for an impartial game. -/
def leftGrundy (x : IGame.{u}) : Nimber.{u} :=
  sInf (Set.range fun y : x.leftMoves ↦ leftGrundy y.1)ᶜ
termination_by x
decreasing_by igame_wf

theorem leftGrundy_def (x : IGame) : leftGrundy x = sInf (leftGrundy '' x.leftMoves)ᶜ := by
  rw [leftGrundy, image_eq_range]

theorem le_leftGrundy_iff {x : IGame} {o : Nimber} :
    o ≤ leftGrundy x ↔ Iio o ⊆ leftGrundy '' x.leftMoves := by
  rw [leftGrundy_def, le_csInf_iff'']
  · rw [← compl_subset_compl (t := Iio o), subset_def]
    simp
  · exact nonempty_of_not_bddAbove (Nimber.not_bddAbove_compl_of_small _)

theorem lt_leftGrundy_iff {x : IGame} {o : Nimber} :
    o < leftGrundy x ↔ Iic o ⊆ leftGrundy '' x.leftMoves := by
  simpa using le_leftGrundy_iff (o := Order.succ o)

theorem mem_leftGrundy_image_of_lt {x : IGame} {o : Nimber} (h : o < leftGrundy x) :
    o ∈ leftGrundy '' x.leftMoves :=
  le_leftGrundy_iff.1 le_rfl h

theorem leftGrundy_le_of_notMem {x : IGame} {o : Nimber} (h : o ∉ leftGrundy '' x.leftMoves) :
    leftGrundy x ≤ o :=
  le_of_not_gt <| mt mem_leftGrundy_image_of_lt h

theorem leftGrundy_ne {x y : IGame} (hy : y ∈ x.leftMoves) : leftGrundy y ≠ leftGrundy x := by
  conv_rhs => rw [leftGrundy_def]
  have := csInf_mem (nonempty_of_not_bddAbove <|
    Nimber.not_bddAbove_compl_of_small (leftGrundy '' x.leftMoves))
  simp_all

@[simp]
theorem leftGrundy_add (x y : IGame) : (x + y).leftGrundy = x.leftGrundy + y.leftGrundy := by
  apply le_antisymm
  · apply leftGrundy_le_of_notMem
    rw [leftMoves_add]
    rintro ⟨_, (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩), ha'⟩
    · rw [leftGrundy_add, add_left_inj] at ha'
      exact leftGrundy_ne ha ha'
    · rw [leftGrundy_add, add_right_inj] at ha'
      exact leftGrundy_ne ha ha'
  · rw [le_leftGrundy_iff]
    intro a ha
    obtain ha | ha := Nimber.lt_add_cases ha
    · obtain ⟨z, hz, hz'⟩  := mem_leftGrundy_image_of_lt ha
      refine ⟨_, add_right_mem_leftMoves_add hz y, ?_⟩
      rw [leftGrundy_add, hz', add_cancel_right]
    · obtain ⟨z, hz, hz'⟩  := mem_leftGrundy_image_of_lt ha
      refine ⟨_, add_left_mem_leftMoves_add hz x, ?_⟩
      rw [leftGrundy_add, hz', add_comm, add_cancel_right]
termination_by (x, y)
decreasing_by igame_wf

/-- The right Grundy value of a game is recursively defined as the minimum excluded value
(the infimum of the complement) of the right Grundy values of its right options.

This is an auxiliary definition for reasoning about games not yet known to be impartial. Use
`Impartial.grundy` for an impartial game. -/
def rightGrundy (x : IGame.{u}) : Nimber.{u} :=
  sInf (Set.range fun y : x.rightMoves ↦ rightGrundy y.1)ᶜ
termination_by x
decreasing_by igame_wf

theorem rightGrundy_def (x : IGame) : rightGrundy x = sInf (rightGrundy '' x.rightMoves)ᶜ := by
  rw [rightGrundy, image_eq_range]

@[simp]
theorem leftGrundy_neg (x : IGame) : leftGrundy (-x) = rightGrundy x := by
  rw [leftGrundy_def, rightGrundy_def, leftMoves_neg]
  congr
  exact image_neg_of_apply_neg_eq fun _ _ ↦ leftGrundy_neg _
termination_by x
decreasing_by igame_wf

@[simp]
theorem rightGrundy_neg (x : IGame) : rightGrundy (-x) = leftGrundy x := by
  rw [← leftGrundy_neg, neg_neg]

@[simp]
theorem leftGrundy_image_neg (s : Set IGame) : leftGrundy '' (-s) = rightGrundy '' s :=
  image_neg_of_apply_neg_eq fun _ _ ↦ leftGrundy_neg _

@[simp]
theorem rightGrundy_image_neg (s : Set IGame) : rightGrundy '' (-s) = leftGrundy '' s :=
  image_neg_of_apply_neg_eq fun _ _ ↦ rightGrundy_neg _

theorem le_rightGrundy_iff {x : IGame} {o : Nimber} :
    o ≤ rightGrundy x ↔ Iio o ⊆ rightGrundy '' x.rightMoves := by
  simpa using @le_leftGrundy_iff (-x) o

theorem lt_rightGrundy_iff {x : IGame} {o : Nimber} :
    o < rightGrundy x ↔ Iic o ⊆ rightGrundy '' x.rightMoves := by
  simpa using le_rightGrundy_iff (o := Order.succ o)

theorem mem_rightGrundy_image_of_lt {x : IGame} {o : Nimber} (h : o < rightGrundy x) :
    o ∈ rightGrundy '' x.rightMoves :=
  le_rightGrundy_iff.1 le_rfl h

theorem rightGrundy_le_of_notMem {x : IGame} {o : Nimber} (h : o ∉ rightGrundy '' x.rightMoves) :
    rightGrundy x ≤ o :=
  le_of_not_gt <| mt mem_rightGrundy_image_of_lt h

theorem rightGrundy_ne {x y : IGame} : y ∈ x.rightMoves → rightGrundy y ≠ rightGrundy x := by
  simpa using @leftGrundy_ne (-x) (-y)

@[simp]
theorem rightGrundy_add (x y : IGame) : (x + y).rightGrundy = x.rightGrundy + y.rightGrundy := by
  rw [← leftGrundy_neg, neg_add, leftGrundy_add, leftGrundy_neg, leftGrundy_neg]

@[simp]
theorem leftGrundy_sub (x y : IGame) : (x - y).leftGrundy = x.leftGrundy + y.rightGrundy := by
  rw [sub_eq_add_neg, leftGrundy_add, leftGrundy_neg]

@[simp]
theorem rightGrundy_sub (x y : IGame) : (x - y).rightGrundy = x.rightGrundy + y.leftGrundy := by
  rw [sub_eq_add_neg, rightGrundy_add, rightGrundy_neg]

namespace Impartial

/-- The Grundy value of an impartial game is recursively defined as the minimum excluded value
(the infimum of the complement) of the Grundy values of its options.

This definition enforces that `x` is impartial. If you want to talk about the left or right Grundy
values of a game (e.g. if you don't yet know it to be impartial), use `leftGrundy` or `rightGrundy`.
The lemmas `leftGrundy_eq_grundy` and `rightGrundy_eq_grundy` show that both definitions match in
the case of an impartial game. -/
def grundy (x : IGame) [Impartial x] : Nimber :=
  x.rightGrundy

/-- The **Sprague-Grundy theorem** states that every impartial game is equivalent to a game of nim,
namely the game of nim for the game's Grundy value. -/
theorem nim_grundy_equiv (x : IGame) [Impartial x] : nim (grundy x) ≈ x := by
  rw [equiv_iff_forall_fuzzy]
  constructor <;> intro y hy
  · rw [leftMoves_nim] at hy
    obtain ⟨o, ho, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := mem_rightGrundy_image_of_lt ho
    have := Impartial.of_mem_rightMoves hz
    rw [← grundy, (nim_grundy_equiv _).incompRel_congr_left]
    exact rightMove_fuzzy hz
  · have := Impartial.of_mem_rightMoves hy
    rw [← (nim_grundy_equiv _).incompRel_congr_right, nim_fuzzy_iff]
    exact (rightGrundy_ne hy).symm
termination_by x
decreasing_by igame_wf

theorem grundy_eq_iff_equiv_nim {x : IGame} [Impartial x] {o : Nimber} :
    grundy x = o ↔ x ≈ nim o := by
  rw [← (nim_grundy_equiv x).antisymmRel_congr_left, nim_equiv_iff]

alias ⟨_, grundy_eq⟩ := grundy_eq_iff_equiv_nim

theorem grundy_eq_zero_iff {x : IGame} [Impartial x] : grundy x = 0 ↔ x ≈ 0 := by
  simpa using grundy_eq_iff_equiv_nim (o := 0)

@[simp]
theorem grundy_eq_iff_equiv {x y : IGame} [Impartial x] [Impartial y] :
    grundy x = grundy y ↔ x ≈ y := by
  rw [grundy_eq_iff_equiv_nim, (nim_grundy_equiv _).antisymmRel_congr_right]

@[simp] theorem grundy_nim (o : Nimber) : grundy (nim o) = o := grundy_eq .rfl
@[simp] theorem grundy_zero : grundy 0 = 0 := by simpa using grundy_nim 0
@[simp] theorem grundy_star : grundy ⋆ = 1 := by simpa using grundy_nim 1

@[simp]
theorem grundy_neg (x : IGame) [Impartial x] : grundy (-x) = grundy x := by
  rw [grundy_eq_iff_equiv_nim, ← neg_nim, IGame.neg_equiv_neg_iff, ← grundy_eq_iff_equiv_nim]

@[simp]
theorem leftGrundy_eq_grundy (x : IGame) [Impartial x] : leftGrundy x = grundy x := by
  rw [← grundy_neg, grundy, rightGrundy_neg]

@[simp]
theorem rightGrundy_eq_grundy (x : IGame) [Impartial x] : rightGrundy x = grundy x :=
  rfl

@[simp]
theorem grundy_add (x y : IGame) [Impartial x] [Impartial y] :
    grundy (x + y) = grundy x + grundy y :=
  rightGrundy_add x y

theorem _root_.IGame.nim_add_equiv (a b : Nimber) : nim a + nim b ≈ nim (a + b) := by
  conv_rhs => rw [← grundy_nim a, ← grundy_nim b, ← grundy_add]
  exact (nim_grundy_equiv _).symm

theorem grundy_leftMove_ne {x y : IGame} [Impartial x] (hy : y ∈ x.leftMoves) :
    have := Impartial.of_mem_leftMoves hy; grundy y ≠ grundy x := by
  simp_rw [← leftGrundy_eq_grundy]
  exact leftGrundy_ne hy

theorem grundy_rightMove_ne {x y : IGame} [Impartial x] (hy : y ∈ x.rightMoves) :
    have := Impartial.of_mem_rightMoves hy; grundy y ≠ grundy x :=
  rightGrundy_ne hy

end Impartial
end IGame
end
