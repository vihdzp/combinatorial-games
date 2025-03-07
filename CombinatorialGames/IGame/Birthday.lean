/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.IGame.Ordinal
import CombinatorialGames.IGame.Special
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.SetTheory.Ordinal.NaturalOps

/-!
# Birthdays of games

There are two related but distinct notions of a birthday within combinatorial game theory. One is
the birthday of an `IGame`, which represents the "step" at which it is constructed. We define it
recursively as the least ordinal larger than the birthdays of its left and right options. On the
other hand, the birthday of a `Game` is the smallest birthday among all `IGame`s that quotient to
it.

The birthday of an `IGame` can be understood as representing the depth of its game tree. Meanwhile,
the birthday of a `Game` more closely matches Conway's original description. The lemma
`Game.birthday_eq_iGameBirthday` links both definitions together.
-/

universe u

open NatOrdinal Order Set
open scoped NaturalOps IGame

/-! ### Stuff for Mathlib -/

theorem IncompRel.ne {α : Type*} {r : α → α → Prop} [IsRefl α r] {a b : α}
    (h : IncompRel r a b) : a ≠ b := by
  rintro rfl
  exact h.1 <| refl_of r a

-- TODO: upstream
theorem ciSup_eq_bot {α : Type*} {ι : Sort*} [ConditionallyCompleteLinearOrderBot α] {f : ι → α}
    (hf : BddAbove (range f)) : ⨆ i, f i = ⊥ ↔ ∀ i, f i = ⊥ := by
  simpa using ciSup_le_iff' hf (a := ⊥)

-- fix this! embarassing
@[simp]
theorem NatOrdinal.bot_eq_zero' : (⊥ : NatOrdinal) = 0 :=
  rfl

-- TODO: upstream
@[simp]
theorem NatOrdinal.succ_ne_zero (x : NatOrdinal) : succ x ≠ 0 :=
  Ordinal.succ_ne_zero x

@[simp]
protected theorem NatOrdinal.le_zero {x : NatOrdinal} : x ≤ 0 ↔ x = 0 :=
  Ordinal.le_zero

@[simp]
protected theorem NatOrdinal.succ_zero : succ (0 : NatOrdinal) = 1 :=
  Ordinal.succ_zero

@[simp]
protected theorem NatOrdinal.succ_one : succ (1 : NatOrdinal) = 2 := by
  rw [succ_eq_add_one, one_add_one_eq_two]

-- TODO: upstream
protected theorem NatOrdinal.lt_iSup_iff {ι : Type*} [Small.{u} ι] (f : ι → NatOrdinal.{u}) {x} :
    x < ⨆ i, f i ↔ ∃ i, x < f i :=
  Ordinal.lt_iSup_iff

-- TODO: upstream
protected theorem NatOrdinal.iSup_eq_zero_iff {ι : Type*} [Small.{u} ι] {f : ι → NatOrdinal.{u}} :
    ⨆ i, f i = 0 ↔ ∀ i, f i = 0 :=
  Ordinal.iSup_eq_zero_iff

/-! ### `IGame` birthday -/

namespace IGame

-- move to `IGame` file
instance (x : IGame.{u}) : Small.{u} {y // IsOption y x} :=
  inferInstanceAs (Small (x.leftMoves ∪ x.rightMoves :))

/-- The birthday of an `IGame` is inductively defined as the least strict upper bound of the
birthdays of its options. It may be thought as the "step" in which a certain game is constructed. -/
noncomputable def birthday (x : IGame.{u}) : NatOrdinal.{u} :=
  ⨆ y : {y // IsOption y x}, succ (birthday y)
termination_by x
decreasing_by igame_wf

theorem lt_birthday_iff {x : IGame} {o : NatOrdinal} : o < x.birthday ↔
    (∃ y ∈ x.leftMoves, o ≤ y.birthday) ∨ (∃ y ∈ x.rightMoves, o ≤ y.birthday) := by
  rw [birthday, NatOrdinal.lt_iSup_iff]
  simp [IsOption, or_and_right, exists_or]

theorem birthday_eq_max (x : IGame) : birthday x =
    max (⨆ y : x.leftMoves, succ y.1.birthday) (⨆ y : x.rightMoves, succ y.1.birthday) := by
  apply eq_of_forall_lt_iff
  simp [lt_birthday_iff, NatOrdinal.lt_iSup_iff]

theorem birthday_lt_of_mem_leftMoves {x y : IGame} (hy : y ∈ x.leftMoves) :
    y.birthday < x.birthday :=
  lt_birthday_iff.2 (.inl ⟨y, hy, le_rfl⟩)

theorem birthday_lt_of_mem_rightMoves {x y : IGame} (hy : y ∈ x.rightMoves) :
    y.birthday < x.birthday :=
  lt_birthday_iff.2 (.inr ⟨y, hy, le_rfl⟩)

theorem birthday_ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] :
    birthday {s | t}ᴵ = max (sSup (succ ∘ birthday '' s)) (sSup (succ ∘ birthday '' t)) := by
  rw [birthday_eq_max, leftMoves_ofSets, rightMoves_ofSets]
  simp [iSup, image_eq_range]

@[simp]
theorem birthday_eq_zero {x : IGame} : birthday x = 0 ↔ x = 0 := by
  rw [birthday, NatOrdinal.iSup_eq_zero_iff, IGame.ext_iff]
  simp [IsOption, forall_and, eq_empty_iff_forall_not_mem]

@[simp] theorem birthday_zero : birthday 0 = 0 := by simp
@[simp] theorem birthday_one : birthday 1 = 1 := by rw [one_def, birthday_ofSets]; simp
@[simp] theorem birthday_star : birthday ⋆ = 1 := by rw [star, birthday_ofSets]; simp

@[simp]
theorem birthday_half : birthday ½ = 2 := by
  rw [half, birthday_ofSets]
  simpa using one_le_two

@[simp]
theorem birthday_up : birthday ↑ = 2 := by
  rw [up, birthday_ofSets]
  simpa using one_le_two

@[simp]
theorem birthday_down : birthday ↓ = 2 := by
  rw [down, birthday_ofSets]
  simpa using one_le_two

@[simp]
theorem birthday_neg (x : IGame) : (-x).birthday = x.birthday := by
  refine eq_of_forall_lt_iff fun y ↦ ?_
  rw [lt_birthday_iff, lt_birthday_iff, exists_leftMoves_neg, exists_rightMoves_neg, or_comm]
  congr! 3
  all_goals
    rw [← and_congr_right]
    intro h
    rw [birthday_neg]
termination_by x
decreasing_by igame_wf

@[simp]
theorem birthday_toIGame (o : NatOrdinal) : o.toIGame.birthday = o := by
  rw [toIGame_def, birthday_ofSets, image_empty, csSup_empty, max_bot_right, image_image]
  conv_rhs => rw [← iSup_succ o, iSup]
  simp_rw [Function.comp_apply, ← image_eq_range]
  congr!
  rw [birthday_toIGame]
termination_by o

theorem le_toIGame_birthday (x : IGame) : x ≤ x.birthday.toIGame := by
  rw [le_iff_forall_lf]
  refine ⟨fun y hy ↦ ((le_toIGame_birthday y).trans_lt ?_).not_le, ?_⟩
  · simpa using birthday_lt_of_mem_leftMoves hy
  · simp
termination_by x
decreasing_by igame_wf

theorem neg_toIGame_birthday_le (x : IGame) : -x.birthday.toIGame ≤ x := by
  simpa [IGame.neg_le] using le_toIGame_birthday (-x)

@[simp]
theorem birthday_add (x y : IGame) : (x + y).birthday = x.birthday + y.birthday := by
  refine eq_of_forall_lt_iff fun o ↦ ?_
  simp_rw [lt_add_iff, lt_birthday_iff, exists_leftMoves_add, exists_rightMoves_add, or_and_right,
    exists_or, or_or_or_comm]
  congr! 2
  all_goals
    constructor
    · rintro ⟨z, hz, hz'⟩
      refine ⟨_, ⟨z, hz, le_rfl⟩, ?_⟩
      rwa [← birthday_add]
    · rintro ⟨a, ⟨⟨z, hz, hz'⟩, ha⟩⟩
      use z, hz
      rw [birthday_add]
      apply ha.trans
      first | exact add_le_add_left hz' _ | exact add_le_add_right hz' _
termination_by (x, y)
decreasing_by igame_wf

@[simp]
theorem birthday_sub (x y : IGame) : (x - y).birthday = x.birthday + y.birthday := by
  simp [sub_eq_add_neg]

@[simp, norm_cast]
theorem birthday_natCast : ∀ n : ℕ, birthday n = n
  | 0 => birthday_zero
  | n + 1 => by simp_rw [Nat.cast_add_one, birthday_add, birthday_natCast, birthday_one]

@[simp]
theorem birthday_ofNat (n : ℕ) [n.AtLeastTwo] : birthday ofNat(n) = n :=
  birthday_natCast n

@[simp]
theorem birthday_tiny (x : IGame) : (⧾x).birthday = x.birthday + 2 := by
  rw [tiny]
  simp [Order.succ_eq_add_one, birthday_ofSets, ← one_add_one_eq_two, ← add_assoc]

@[simp]
theorem birthday_miny (x : IGame) : (⧿x).birthday = x.birthday + 2 := by
  rw [← neg_tiny, birthday_neg, birthday_tiny]

-- TODO: short game iff finite birthday

end IGame

/-! ### `Game` birthday -/

namespace Game

/-- The birthday of a game is defined as the least birthday among all pre-games that define it. -/
noncomputable def birthday (x : Game.{u}) : NatOrdinal.{u} :=
  sInf (IGame.birthday '' (mk ⁻¹' {x}))

theorem birthday_eq_iGameBirthday (x : Game) :
    ∃ y : IGame, Game.mk y = x ∧ y.birthday = birthday x := by
  refine csInf_mem (image_nonempty.2 ?_)
  exact ⟨_, x.out_eq⟩

theorem birthday_mk_le (x : IGame) : birthday (mk x) ≤ x.birthday :=
  csInf_le' ⟨x, rfl, rfl⟩

@[simp]
theorem birthday_zero : birthday 0 = 0 := by
  simpa using birthday_mk_le 0

@[simp]
theorem birthday_eq_zero {x : Game} : birthday x = 0 ↔ x = 0 := by
  obtain ⟨_, _, _⟩ := birthday_eq_iGameBirthday x
  refine ⟨fun _ ↦ ?_, ?_⟩ <;> simp_all

private theorem birthday_neg_le (x : Game) : (-x).birthday ≤ x.birthday := by
  obtain ⟨y, hy, hy'⟩ := birthday_eq_iGameBirthday x
  rw [← hy', ← hy]
  apply (birthday_mk_le _).trans
  rw [IGame.birthday_neg]

@[simp]
theorem birthday_neg (x : Game) : (-x).birthday = x.birthday := by
  apply (birthday_neg_le x).antisymm
  simpa using birthday_neg_le (-x)

theorem le_toGame_birthday (x : Game) : x ≤ x.birthday.toGame := by
  obtain ⟨y, hy, hy'⟩ := birthday_eq_iGameBirthday x
  rw [← hy', ← hy]
  exact y.le_toIGame_birthday

theorem neg_toGame_birthday_le (x : Game) : -x.birthday.toGame ≤ x := by
  simpa [neg_le] using le_toGame_birthday (-x)

@[simp]
theorem birthday_toGame (o : NatOrdinal) : birthday o.toGame = o := by
  apply le_antisymm
  · simpa using birthday_mk_le o.toIGame
  · simpa using o.toGame.le_toGame_birthday

@[simp, norm_cast]
theorem birthday_natCast (n : ℕ) : birthday n = n := by
  simpa using birthday_toGame n

@[simp]
theorem birthday_ofNat (n : ℕ) [n.AtLeastTwo] : birthday ofNat(n) = n :=
  birthday_natCast n

@[simp]
theorem birthday_one : birthday 1 = 1 := by
  simpa using birthday_natCast 1

@[simp]
theorem birthday_star : birthday (Game.mk ⋆) = 1 := by
  apply le_antisymm
  · simpa using birthday_mk_le ⋆
  · rw [Ordinal.one_le_iff_ne_zero, birthday_eq_zero.ne]
    exact IncompRel.ne (r := (· ≤ ·)) (IGame.star_fuzzy_zero)

theorem birthday_add_le (x y : Game) : (x + y).birthday ≤ x.birthday + y.birthday := by
  obtain ⟨a, ha, ha'⟩ := birthday_eq_iGameBirthday x
  obtain ⟨b, hb, hb'⟩ := birthday_eq_iGameBirthday y
  rw [← ha', ← hb', ← ha, ← hb, ← IGame.birthday_add]
  exact birthday_mk_le _

theorem birthday_sub_le (x y : Game) : (x - y).birthday ≤ x.birthday + y.birthday := by
  simpa using birthday_add_le x (-y)

/- The bound `(x * y).birthday ≤ x.birthday * y.birthday` on surreals is currently an open problem.
See https://mathoverflow.net/a/476829/147705. -/

/-- Games with bounded birthday are a small set. -/
theorem small_setOf_birthday_lt (o : NatOrdinal) : Small.{u} {x : Game.{u} // birthday x < o} := by
  induction o using Ordinal.induction with | h o IH =>
  let S := ⋃ a ∈ Iio o, {x : Game.{u} | birthday x < a}
  let H : Small.{u} S := @small_biUnion _ _ _ _ _ IH
  obtain rfl | ⟨a, rfl⟩ | ho := zero_or_succ_or_limit o
  · simp_rw [NatOrdinal.not_lt_zero]
    exact small_empty
  · simp_rw [lt_succ_iff, le_iff_lt_or_eq]
    convert small_union.{u} {x | birthday x < a} {x | birthday x = a}
    · exact IH _ (lt_succ a)
    · let f (g : Set S × Set S) : Game := Game.mk ({
        range (fun x ↦ ((equivShrink g.1).symm x).1.1.out) |
        range (fun x ↦ ((equivShrink g.2).symm x).1.1.out)
      }ᴵ)
      suffices {x | x.birthday = a} ⊆ range f from small_subset this
      rintro x rfl
      obtain ⟨y, rfl, hy'⟩ := birthday_eq_pGameBirthday x
      refine ⟨⟨{z | ∃ i ∈ y.leftMoves, .mk i = z.1}, {z | ∃ i ∈ y.rightMoves, .mk i = z.1}⟩, ?_⟩
      apply Game.mk_eq <| IGame.equiv_of_exists _ _ _ _ <;> intro i hi
      · obtain ⟨j, hj⟩ := ((equivShrink _).symm i).2
        exact ⟨j, by simp [IGame.equiv_iff_game_eq, hj]⟩
      · obtain ⟨j, hj⟩ := ((equivShrink _).symm i).2
        exact ⟨j, by simp [IGame.equiv_iff_game_eq, hj]⟩
      · refine ⟨equivShrink _ ⟨⟨.mk i, ?_⟩, i, rfl⟩, by simpa using Quotient.mk_out _⟩
        suffices ∃ b ≤ y.birthday, birthday ⟦y.moveLeft i⟧ < b by simpa [S, hy'] using this
        refine ⟨_, le_rfl, ?_⟩
        exact (birthday_quot_le_pGameBirthday _).trans_lt (IGame.birthday_moveLeft_lt i)
      · refine ⟨equivShrink _ ⟨⟨⟦y.moveRight i⟧, ?_⟩, i, rfl⟩, by simpa using Quotient.mk_out _⟩
        suffices ∃ b ≤ y.birthday, birthday ⟦y.moveRight i⟧ < b by simpa [S, hy'] using this
        refine ⟨_, le_rfl, ?_⟩
        exact (birthday_quot_le_pGameBirthday _).trans_lt (IGame.birthday_moveRight_lt i)
  · convert H
    change birthday _ < o ↔ ∃ a, _
    simpa using lt_limit ho

end Game
