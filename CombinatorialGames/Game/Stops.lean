/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Surreal.Cut
public import CombinatorialGames.Surreal.Dyadic

import CombinatorialGames.Surreal.Birthday.Cut
import CombinatorialGames.Surreal.Birthday.Dyadic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Left and right stops

The functions `Surreal.Cut.leftGame` and `Surreal.Cut.rightGame`, defined in `Surreal.Cut`, define
the left and right stops of a game as cuts. Whenever the game is short, these cuts are always
numeric, and their endpoints are dyadic rationals. This file defines the `Dyadic`-valued versions of
these functions.
-/

public section

namespace IGame
open Ordinal Surreal.Cut

private theorem stop_aux₁ {x : Surreal.Cut} [x.Numeric] (hx : x.birthday < NatOrdinal.of ω) :
    x.toSurreal ∈ Set.range ((↑) : Dyadic → _) := by
  rw [← Surreal.birthday_lt_omega0_iff]
  apply (lt_add_one _).trans
  rwa [← WithTop.coe_lt_coe, WithTop.coe_add, WithTop.coe_one, ← birthday_of_numeric]

private theorem stop_aux₂ (x : IGame) [Short x] :
    ((Game.mk x).birthday : WithTop NatOrdinal) + 1 < NatOrdinal.of ω := by
  have ⟨n, hn⟩ := (NatOrdinal.lt_omega0 (o := (Game.mk x).birthday)).1 ?_
  · rw [hn, WithTop.coe_natCast, ← Nat.cast_add_one, ← WithTop.coe_natCast, WithTop.coe_lt_coe]
    exact NatOrdinal.natCast_lt_omega0 _
  · grw [Game.birthday_mk_le, Short.birthday_lt_omega0]

/-- The left stop of a short game is the dyadic number which defines `leftGame (mk x)`.

Every surreal `y` with `leftStop x < y` satisfies `x < y` (`lt_of_lt_rightStop`), and every surreal
`y` with `y < leftStop x` satisfies `y ⧏ x` (`lf_of_lt_leftStop`). -/
noncomputable def leftStop (x : IGame) [Short x] : Dyadic :=
  Classical.choose (stop_aux₁ ((birthday_leftGame_le _).trans_lt (stop_aux₂ x)))

/-- The right stop of a short game is the dyadic number which defines `rightGame (mk x)`.

Every surreal `y` with `y < rightStop x` satisfies `y < x` (`lt_of_leftStop_lt`), and every surreal
`y` with `rightStop x < y` satisfies `x ⧏ y` (`lf_of_rightStop_lt`). -/
noncomputable def rightStop (x : IGame) [Short x] : Dyadic :=
  Classical.choose (stop_aux₁ ((birthday_rightGame_le _).trans_lt (stop_aux₂ x)))

@[simp]
theorem toSurreal_leftGame_mk_of_short (x : IGame) [Short x] :
    (leftGame (.mk x)).toSurreal = leftStop x := by
  unfold leftStop
  generalize_proofs _ H
  exact (Classical.choose_spec H).symm

@[simp]
theorem toSurreal_rightGame_mk_of_short (x : IGame) [Short x] :
    (rightGame (.mk x)).toSurreal = rightStop x := by
  unfold rightStop
  generalize_proofs _ H
  exact (Classical.choose_spec H).symm

@[simp]
theorem leftStop_of_numeric (x : IGame) [Short x] [Numeric x] : leftStop x = x.toDyadic := by
  simpa [← Surreal.ratCast_toDyadic] using (toSurreal_leftGame_mk_of_short x).symm

@[simp]
theorem rightStop_of_numeric (x : IGame) [Short x] [Numeric x] : rightStop x = x.toDyadic := by
  simpa [← Surreal.ratCast_toDyadic] using (toSurreal_rightGame_mk_of_short x).symm

theorem leftStop_toIGame (x : Dyadic) : leftStop x = x := by simp
theorem rightStop_toIGame (x : Dyadic) : rightStop x = x := by simp
theorem leftStop_zero : leftStop 0 = 0 := by simp
theorem rightStop_zero : rightStop 0 = 0 := by simp
theorem leftStop_one : leftStop 1 = 1 := by simp
theorem rightStop_one : rightStop 1 = 1 := by simp

theorem lt_of_leftStop_lt {x y : IGame} [Short x] [Numeric y] (h : leftStop x < y) : x < y := by
  obtain ⟨z, _, hxz, hzy⟩ := Numeric.exists_between h
  apply hzy.trans_le'
  rw [← Game.mk_le_mk, ← Surreal.toGame_mk z, ← mem_right_leftGame]
  apply mem_right_of_toSurreal_lt
  simpa [← Surreal.mk_lt_mk] using hxz

theorem lf_of_lt_leftStop {x y : IGame} [Short x] [Numeric y] (h : y < leftStop x) : y ⧏ x := by
  rw [← Game.mk_le_mk, ← Surreal.toGame_mk y, ← mem_left_leftGame]
  apply mem_left_of_lt_toSurreal
  simpa [← Surreal.mk_lt_mk] using h

theorem lt_of_lt_rightStop {x y : IGame} [Short x] [Numeric y] (h : y < rightStop x) : y < x := by
  obtain ⟨z, _, hyz, hzx⟩ := Numeric.exists_between h
  apply hyz.trans_le
  rw [← Game.mk_le_mk, ← Surreal.toGame_mk z, ← mem_left_rightGame]
  apply mem_left_of_lt_toSurreal
  simpa [← Surreal.mk_lt_mk] using hzx

theorem lf_of_rightStop_lt {x y : IGame} [Short x] [Numeric y] (h : rightStop x < y) : x ⧏ y := by
  rw [← Game.mk_le_mk, ← Surreal.toGame_mk y, ← mem_right_rightGame]
  apply mem_right_of_toSurreal_lt
  simpa [← Surreal.mk_lt_mk] using h

@[simp]
theorem leftStop_neg (x : IGame) [Short x] : leftStop (-x) = -rightStop x := by
  simpa [← Rat.cast_neg, ← Dyadic.toRat_neg] using (toSurreal_leftGame_mk_of_short (-x)).symm

@[simp]
theorem rightStop_neg (x : IGame) [Short x] : rightStop (-x) = -leftStop x := by
  simpa [neg_eq_iff_eq_neg] using (leftStop_neg (-x)).symm

theorem leftStop_congr {x y : IGame} [Short x] [Short y] (h : x ≈ y) :
    leftStop x = leftStop y := by
  rw! [← Dyadic.toRat_inj, ← Rat.cast_inj (α := Surreal),
    ← toSurreal_leftGame_mk_of_short, Game.mk_eq h, toSurreal_leftGame_mk_of_short]
  rfl

theorem rightStop_congr {x y : IGame} [Short x] [Short y] (h : x ≈ y) :
    rightStop x = rightStop y := by
  simpa using leftStop_congr (IGame.neg_congr h)

theorem rightStop_le_leftStop (x : IGame) [Short x] : rightStop x ≤ leftStop x := by
  by_contra! h
  obtain ⟨y, hl, hr⟩ := exists_between h
  cases ((lt_of_leftStop_lt (mod_cast hl)).trans (lt_of_lt_rightStop (y := y) (mod_cast hr))).false

end IGame
end
