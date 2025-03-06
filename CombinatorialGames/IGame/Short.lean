/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Kim Morrison
-/
import CombinatorialGames.IGame.IGame
import Mathlib.Data.Finite.Prod

/-!
# Short games

A combinatorial game is `Short` if it has only finitely many subpositions. In particular, this means
there is a finite set of moves at every point.

We historically defined `Short x` as data, which we then used to enable some degree of computation
on combinatorial games. This functionality is now implemented through the `game_cmp` tactic instead.
-/

universe u

namespace IGame

def ShortAux (x : IGame) : Prop :=
  x.leftMoves.Finite ∧ x.rightMoves.Finite ∧
    (∀ y ∈ x.leftMoves, ShortAux y) ∧ (∀ y ∈ x.rightMoves, ShortAux y)
termination_by x
decreasing_by igame_wf

/-- A short game is one with finitely many subpositions. That is, the left and right sets are
finite, and all of the games in them are short as well. -/
@[mk_iff short_iff_aux]
class Short (x : IGame) : Prop where
  out : ShortAux x

theorem short_def {x : IGame} : Short x ↔
    x.leftMoves.Finite ∧ x.rightMoves.Finite ∧
      (∀ y ∈ x.leftMoves, Short y) ∧ (∀ y ∈ x.rightMoves, Short y) := by
  simp_rw [short_iff_aux]; rw [ShortAux]

namespace Short
variable {x y : IGame}

theorem mk' (h₁ : x.leftMoves.Finite) (h₂ : x.rightMoves.Finite)
    (h₃ : ∀ y ∈ x.leftMoves, Short y) (h₄ : ∀ y ∈ x.rightMoves, Short y) : Short x :=
  short_def.2 ⟨h₁, h₂, h₃, h₄⟩

theorem finite_leftMoves (x : IGame) [h : Short x] : x.leftMoves.Finite :=
  (short_def.1 h).1

theorem finite_rightMoves (x : IGame) [h : Short x] : x.rightMoves.Finite :=
  (short_def.1 h).2.1

theorem finite_setOf_isOption (x : IGame) [Short x] : {y | IsOption y x}.Finite :=
  (finite_leftMoves x).union (finite_rightMoves x)

protected theorem of_mem_leftMoves [h : Short x] (hy : y ∈ x.leftMoves) : Short y :=
  (short_def.1 h).2.2.1 y hy

protected theorem of_mem_rightMoves [h : Short x] (hy : y ∈ x.rightMoves) : Short y :=
  (short_def.1 h).2.2.2 y hy

protected theorem isOption [Short x] (h : IsOption y x) : Short y := by
  cases h with
  | inl h => exact .of_mem_leftMoves h
  | inr h => exact .of_mem_rightMoves h

alias _root_.IGame.IsOption.short := Short.isOption

theorem finite_setOf_subposition (x : IGame) [Short x] : {y | Subposition y x}.Finite := by
  have : {y | Subposition y x} = {y | IsOption y x} ∪
      ⋃ y ∈ {y | IsOption y x}, {z | Subposition z y} := by
    ext
    rw [Set.mem_setOf_eq, Subposition, Relation.transGen_iff]
    simp [and_comm]
  rw [this]
  refine (finite_setOf_isOption x).union <| (finite_setOf_isOption x).biUnion fun y hy ↦ ?_
  have := hy.short
  exact finite_setOf_subposition y
termination_by x
decreasing_by igame_wf

theorem _root_.IGame.short_iff_finite_setOf_subposition {x : IGame} :
    Short x ↔ {y | Subposition y x}.Finite := by
  refine ⟨@finite_setOf_subposition x, fun h ↦ mk' ?_ ?_ ?_ ?_⟩
  any_goals refine h.subset fun y hy ↦ ?_
  any_goals refine fun y hy ↦ short_iff_finite_setOf_subposition.2 <| h.subset fun z hz ↦ ?_
  all_goals igame_wf
termination_by x
decreasing_by igame_wf

@[simp]
protected instance zero : Short 0 := by
  rw [short_def]; simp

@[simp]
protected instance one : Short 1 := by
  rw [short_def]; simp

protected instance neg (x : IGame) [Short x] : Short (-x) := by
  apply mk'
  · simpa [← Set.image_neg_eq_neg] using (finite_rightMoves x).image _
  · simpa [← Set.image_neg_eq_neg] using (finite_leftMoves x).image _
  · intro y hy
    rw [leftMoves_neg] at hy
    simpa using (Short.of_mem_rightMoves hy).neg
  · rw [forall_rightMoves_neg]
    intro y hy
    simpa using (Short.of_mem_leftMoves hy).neg
termination_by x
decreasing_by all_goals simp_all; igame_wf

#exit
protected instance add (x y : IGame) [Short x] [Short y] : Short (x + y) := by
  apply mk'
  · simpa using ⟨(finite_leftMoves x).image _, (finite_leftMoves y).image _⟩
  · simpa using ⟨(finite_rightMoves x).image _, (finite_rightMoves y).image _⟩
  · rw [forall_leftMoves_add]
    constructor
    all_goals
      intro z hz
      have := Short.of_mem_rightMoves hz
      exact Short.add ..
  · rw [forall_rightMoves_add]
    constructor
    all_goals
      intro z hz
      have := Short.of_mem_rightMoves hz
      exact Short.add ..
termination_by (x, y)
decreasing_by igame_wf

protected instance sub (x y : IGame) [Short x] [Short y] : Short (x - y) :=
  inferInstanceAs (Short (x + -y))

protected instance natCast : ∀ n : ℕ, Short n
  | 0 => inferInstanceAs (Short 0)
  | n + 1 => have := Short.natCast n; inferInstanceAs (Short (n + 1))

protected instance ofNat (n : ℕ) [n.AtLeastTwo] : Short ofNat(n) :=
  inferInstanceAs (Short n)

protected instance mul (x y : IGame) [Short x] [Short y] : Short (x * y) := by
  apply mk'
  · simpa [Set.image_union] using
      ⟨((finite_leftMoves x).prod (finite_leftMoves y)).image _,
        ((finite_rightMoves x).prod (finite_rightMoves y)).image _⟩
  · simpa [Set.image_union] using
      ⟨((finite_leftMoves x).prod (finite_rightMoves y)).image _,
        ((finite_rightMoves x).prod (finite_leftMoves y)).image _⟩
  · intro z hz
    rw []

end Short

#exit
#exit
namespace Short
attribute [simp] toIGame_toSGame

@[simp]
theorem toSGame_le_iff {x y : IGame} [Short x] [Short y] : toSGame x ≤ toSGame y ↔ x ≤ y := by
  change (toSGame x).toIGame ≤ (toSGame y).toIGame ↔ x ≤ y
  simp

@[simp]
theorem toSGame_lt_iff {x y : IGame} [Short x] [Short y] : toSGame x < toSGame y ↔ x < y :=
  lt_iff_lt_of_le_iff_le' toSGame_le_iff toSGame_le_iff

instance (x y : IGame) [Short x] [Short y] : Decidable (x ≤ y) :=
  decidable_of_iff _ toSGame_le_iff

instance (x y : IGame) [Short x] [Short y] : Decidable (x < y) :=
  decidable_of_iff _ toSGame_lt_iff

instance (x y : IGame) [Short x] [Short y] : Decidable (x ≈ y) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (x y : IGame) [Short x] [Short y] : Decidable (x = y) :=
  decidable_of_iff ((toSGame x).toIGame = (toSGame y).toIGame) (by simp)

instance : Short 0 := ⟨0, SGame.toIGame_zero⟩
instance : Short 1 := ⟨1, SGame.toIGame_one⟩

-- These should be computable: https://github.com/leanprover/lean4/pull/7283
noncomputable instance (n : ℕ) : Short n := ⟨n, SGame.toIGame_natCast n⟩
noncomputable instance (n : ℕ) [n.AtLeastTwo] : Short ofNat(n) := inferInstanceAs (Short n)

instance (x : IGame) [Short x] : Short (-x) := ⟨-toSGame x, by simp⟩
instance (x y : IGame) [Short x] [Short y] : Short (x + y) := ⟨toSGame x + toSGame y, by simp⟩
instance (x y : IGame) [Short x] [Short y] : Short (x - y) := ⟨toSGame x - toSGame y, by simp⟩
instance (x y : IGame) [Short x] [Short y] : Short (x * y) := ⟨toSGame x * toSGame y, by simp⟩

end Short

-- TODO: add some actual theorems

proof_wanted exists_lt_natCast_of_short (x : IGame) [Short x] : ∃ n : ℕ, x < n
proof_wanted exists_neg_natCast_lt_of_short (x : IGame) [Short x] : ∃ n : ℕ, -n < x

proof_wanted short_iff_finite_subposition (x : IGame) :
    Nonempty (Short x) ↔ Set.Finite {y | Subposition y x}

end IGame

section Test

example : (0 : IGame) < 1 := by decide
example : (-1 : IGame) < 0 := by native_decide
example : (0 : IGame) < 1 + 1 := by native_decide
example : (-1 : IGame) + 1 ≠ 0 := by native_decide
--example : (2 : IGame) < (5 : IGame) := by native_decide

end Test
