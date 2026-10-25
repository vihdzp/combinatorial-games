/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import CombinatorialGames.Game.Specific.Nim

import Mathlib.Algebra.Order.Monoid.Canonical.Basic
import Mathlib.Order.GameAdd

/-!
# Ordinal sum of games

The ordinal sum of two games `x` and `y`, written `x : y`,
is defined as `{xᴸ, x : yᴸ | xᴿ, x : yᴿ}`. Moving in `y` is done as in the ordinary sum,
but a move in `x` destroys the other component `y` of the sum.
-/

public noncomputable section
open Set

namespace IGame

/--
The ordinal sum of `x` and `y` is played like the ordinay sum, but making a move in `x`
destroys the other component `y` of the sum.
-/
def ordinalSum (x y : IGame) : IGame :=
  !{fun p => x.moves p ∪ range fun z : y.moves p => ordinalSum x z}
termination_by y
decreasing_by igame_wf

infixl:70 " ∶ " => ordinalSum

theorem moves_ordinalSum (p : Player) (x y : IGame) :
    (x ∶ y).moves p = x.moves p ∪ ordinalSum x '' y.moves p := by
  rw [ordinalSum]
  ext; simp

theorem neg_ordinalSum (x y : IGame) : -(x ∶ y) = (-x) ∶ (-y) := by
  induction y using IGame.moveRecOn with | ind y ih
  refine IGame.ext fun p => ?_
  simp only [moves_neg, moves_ordinalSum, ← Set.image_neg_eq_neg]
  rw [Set.image_union, Set.image_image, Set.image_image, Set.image_congr (ih (-p))]

@[simp]
theorem ordinalSum_zero (x : IGame) : x ∶ 0 = x :=
  IGame.ext fun p => by simp [moves_ordinalSum]

@[simp]
theorem zero_ordinalSum (x : IGame) : 0 ∶ x = x := by
  induction x using IGame.moveRecOn with | ind x ih
  refine IGame.ext fun p => ?_
  rw [moves_ordinalSum, moves_zero, empty_union, Set.image_congr (ih p), Set.image_id']

theorem nim_ordinalSum_nim (o o' : Nimber) :
    nim o ∶ nim o' = nim (.of (o.val + o'.val)) := by
  induction o' using WellFoundedLT.induction with | ind o' ih
  refine IGame.ext fun p => ?_
  simp_rw [moves_ordinalSum, moves_nim, Set.image_image]
  conv =>
    enter [1, 2]
    apply_congr
    tactic =>
      apply ih
      assumption
  rw [← Set.image_image nim (fun z => .of (o.val + z.val)) (Iio o'), ← Set.image_union]
  refine congr(nim '' $(Set.ext fun x => ?_))
  simp_rw [Set.mem_union, Set.mem_image, Set.mem_Iio]
  rw [← Nimber.val_lt_iff, lt_add_iff_lt_left_or_exists_lt, ← Nimber.val.exists_congr_right]
  simp_rw [Nimber.of_eq_iff, OrderIso.coe_toEquiv, Nimber.val.lt_iff_lt, eq_comm]

theorem natOrdinal_ordinalSum_natOrdinal (o o' : NatOrdinal) :
    o.toIGame ∶ o'.toIGame = (NatOrdinal.of (o.val + o'.val)).toIGame := by
  induction o' using WellFoundedLT.induction with | ind o' ih
  refine IGame.ext fun p => p.casesOn ?_ (by simp [moves_ordinalSum])
  simp_rw [moves_ordinalSum, NatOrdinal.moves_left_toIGame, Set.image_image]
  conv =>
    enter [1, 2]
    apply_congr
    tactic =>
      apply ih
      assumption
  rw [← Set.image_image NatOrdinal.toIGame (fun z => .of (o.val + z.val)) (Iio o'),
    ← Set.image_union]
  refine congr(NatOrdinal.toIGame '' $(Set.ext fun x => ?_))
  simp_rw [Set.mem_union, Set.mem_image, Set.mem_Iio]
  rw [← NatOrdinal.val_lt_iff, lt_add_iff_lt_left_or_exists_lt, ← NatOrdinal.val.exists_congr_right]
  simp_rw [NatOrdinal.of_eq_iff, OrderIso.coe_toEquiv, NatOrdinal.val.lt_iff_lt, eq_comm]

theorem ordinalSum_le_ordinalSum_iff_left {x y z : IGame} : x ∶ y ≤ x ∶ z ↔ y ≤ z := by
  -- todo: fix recursor argument names
  induction y, z using Sym2.GameAdd.recursion wellFounded_subposition with | IH y z ih
  rw [Sym2.eq_swap] at ih
  rw [le_iff_forall_lf, le_iff_forall_lf]
  simp_rw [moves_ordinalSum, forall_mem_union, forall_mem_image]
  rw [and_and_and_comm,
    forall₂_congr fun c hc => (ih z c (.snd (.of_mem_moves hc))).not,
    forall₂_congr fun c hc => (ih c y (.fst (.of_mem_moves hc))).not]
  apply and_iff_right
  constructor
  · intro c hc
    apply left_lf
    simp [moves_ordinalSum, hc]
  · intro c hc
    apply lf_right
    simp [moves_ordinalSum, hc]

theorem ordinalSum_le_ordinalSum_right (x : IGame) {y z : IGame} (h : y ≤ z) : x ∶ y ≤ x ∶ z :=
  ordinalSum_le_ordinalSum_iff_left.2 h

theorem ordinalSum_lf_ordinalSum_right (x : IGame) {y z : IGame} (h : y ⧏ z) : x ∶ y ⧏ x ∶ z :=
  mt ordinalSum_le_ordinalSum_iff_left.1 h

theorem ordinalSum_right_congr (x : IGame) {y z : IGame} (h : y ≈ z) : x ∶ y ≈ x ∶ z :=
  ⟨ordinalSum_le_ordinalSum_right x h.le, ordinalSum_le_ordinalSum_right x h.ge⟩

mutual

theorem ordinalSum_le_iff_of_forall_wsubposition {x y z : IGame}
    (h : ∀ c, WSubposition c z → ¬x ≈ c) : x ∶ y ≤ z ↔ x ≤ z := by
  rw [le_iff_forall_lf, le_iff_forall_lf, moves_ordinalSum, forall_mem_union, forall_mem_image,
    forall₂_congr fun c hc => (le_ordinalSum_iff_of_forall_wsubposition h).not,
    forall₂_congr fun c hc => (le_ordinalSum_iff_of_forall_wsubposition
      fun u hu => h u (hu.trans (.of_mem_moves hc))).not,
    and_assoc, and_left_comm]
  apply and_iff_right_of_imp
  rw [← le_iff_forall_lf]
  intro hxz c hc hzx
  exact h z .rfl ⟨hxz, hzx⟩
termination_by (y, z)
decreasing_by igame_wf

theorem le_ordinalSum_iff_of_forall_wsubposition {x y z : IGame}
    (h : ∀ c, WSubposition c z → ¬x ≈ c) : z ≤ x ∶ y ↔ z ≤ x := by
  rw [le_iff_forall_lf, le_iff_forall_lf, moves_ordinalSum, forall_mem_union, forall_mem_image,
    forall₂_congr fun c hc => (ordinalSum_le_iff_of_forall_wsubposition h).not,
    forall₂_congr fun c hc => (ordinalSum_le_iff_of_forall_wsubposition
      fun u hu => h u (hu.trans (.of_mem_moves hc))).not,
    ← and_assoc]
  apply and_iff_left_of_imp
  rw [← le_iff_forall_lf]
  intro hzx c hc hxz
  exact h z .rfl ⟨hxz, hzx⟩
termination_by (y, z)
decreasing_by igame_wf

end

theorem ordinalSum_lf_iff_of_forall_wsubposition {x y z : IGame}
    (h : ∀ c, WSubposition c z → ¬x ≈ c) : x ∶ y ⧏ z ↔ x ⧏ z :=
  (le_ordinalSum_iff_of_forall_wsubposition h).not

theorem lf_ordinalSum_iff_of_forall_wsubposition {x y z : IGame}
    (h : ∀ c, WSubposition c z → ¬x ≈ c) : z ⧏ x ∶ y ↔ z ⧏ x :=
  (ordinalSum_le_iff_of_forall_wsubposition h).not

end IGame
