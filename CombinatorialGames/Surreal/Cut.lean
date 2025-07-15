/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Violeta Hernández Palacios
-/
import Mathlib.Order.UpperLower.CompleteLattice
import CombinatorialGames.Mathlib.Concept
import CombinatorialGames.Surreal.Basic

/-!
# Surreal cuts

A surreal cut is defined as consisting of two sets of surreals with the following properties:

- They are complementary sets.
- Every surreal in the first set is less than every surreal in the second set.

This construction resembles the construction of the surreals themselves, but yields a "bigger"
structure, which can embed the surreals, but is also a complete linear order.

Note that surreal cuts are is **not** the same as the Dedekind completion of the surreals. Whereas
the Dedekind completion maps every element of the original order to a unique Dedekind cut, every
surreal number `x` actually corresponds to two cuts `(Iio x, Ici x)` and `(Iic x, Ioi x)`, which we
call the left and right cut, respectively.

The theory of concept lattices gives us a very simple definition of surreal cuts as
`Concept Surreal Surreal (⬝ < ⬝)`. However, we've attempted to provide a thin wrapper for all
concept terminology.
-/

universe u

namespace Surreal
open Set IGame

/-- A surreal cut consists of two complementary sets of surreals, where every surreal in the former
is less than every surreal in the latter. -/
abbrev Cut := Concept Surreal Surreal (· < ·)

namespace Cut

/-- The left set in a cut. This is an alias for `Concept.extent`. -/
def left (x : Cut) := x.extent
/-- The right set in a cut. This is an alias for `Concept.intent`. -/
def right (x : Cut) := x.intent

alias left_lt_right := Concept.rel_extent_intent
alias disjoint_left_right := Concept.disjoint_extent_intent
alias codisjoint_left_right := Concept.codisjoint_extent_intent
alias isCompl_left_right := Concept.isCompl_extent_intent

alias isLowerSet_left := Concept.isLowerSet_extent'
alias isUpperSet_left := Concept.isUpperSet_intent'

@[simp] theorem left_subset_left_iff {c d : Cut}: c.left ⊆ d.left ↔ c ≤ d := .rfl
@[simp] theorem left_ssubset_left_iff {c d : Cut} : c.left ⊂ d.left ↔ c < d := .rfl

@[simp] theorem right_subset_right_iff {c d : Cut}: c.right ⊆ d.right ↔ d ≤ c :=
  Concept.intent_subset_intent_iff
@[simp] theorem right_ssubset_right_iff {c d : Cut} : c.right ⊂ d.right ↔ d < c :=
  Concept.intent_ssubset_intent_iff

instance : IsTotal Cut (· ≤ ·) where
  total a b := le_total (α := LowerSet _) ⟨_, isLowerSet_left a⟩ ⟨_, isLowerSet_left b⟩

noncomputable instance : LinearOrder Cut :=
  by classical exact Lattice.toLinearOrder _

noncomputable instance : CompleteLinearOrder Cut where
  __ := instLinearOrder
  __ := Concept.instCompleteLattice
  __ := LinearOrder.toBiheytingAlgebra

@[simp] theorem compl_left (x : Cut) : x.leftᶜ = x.right := (isCompl_left_right x).compl_eq
@[simp] theorem compl_right (x : Cut) : x.rightᶜ = x.left := (isCompl_left_right x).eq_compl.symm

theorem lt_iff_nonempty_inter {x y : Cut} : x < y ↔ (x.right ∩ y.left).Nonempty := by
  rw [← not_le, ← left_subset_left_iff, ← diff_nonempty, diff_eq_compl_inter, compl_left]

/-- The left cut of a game `x` is such that its right set consists of surreals
equal or larger to it. -/
def leftGame : Game →o Cut where
  toFun x := {
    extent := {y | y.toGame ⧏ x}
    intent := {y | x ≤ y.toGame}
    upperPolar_extent := by
      refine ext fun y ↦ ⟨?_, fun hy z hz ↦ ?_⟩
      · simp_all [upperPolar, not_imp_comm]
      · simpa using not_le_of_not_le_of_le hz hy
    lowerPolar_intent := by
      refine ext fun y ↦ ⟨fun H hx ↦ (H hx).false, fun hy z hz ↦ ?_⟩
      simpa using not_le_of_not_le_of_le hy hz
  }
  monotone' x y hy z hz := not_le_of_not_le_of_le hz hy

/-- The right cut of a game `x` is such that its right set consists of surreals
equal or lesser to it. -/
def rightGame : Game →o Cut where
  toFun x := {
    extent := {y | y.toGame ≤ x}
    intent := {y | x ⧏ y.toGame}
    upperPolar_extent := by
      refine ext fun y ↦ ⟨fun H hx ↦ (H hx).false, fun hy z hz ↦ ?_⟩
      simpa using not_le_of_le_of_not_le hz hy
    lowerPolar_intent := by
      refine ext fun y ↦ ⟨?_, fun hy z hz ↦ ?_⟩
      · simp_all [lowerPolar, not_imp_comm]
      · simpa using not_le_of_le_of_not_le hy hz
  }
  monotone' x y hy z := le_trans' hy

/-- The cut just to the left of a surreal number. -/
def leftSurreal : Surreal ↪o Cut where
  toFun x := (leftGame x.toGame).copy
    (Iio x) (by rw [leftGame]; aesop) (Ici x) (by rw [leftGame]; aesop)
  inj' _ := by simp [Concept.copy, Ici_inj]
  map_rel_iff' := Iio_subset_Iio_iff

/-- The cut just to the right of a surreal number. -/
def rightSurreal : Surreal ↪o Cut where
  toFun x := (rightGame x.toGame).copy
    (Iic x) (by rw [rightGame]; aesop) (Ioi x) (by rw [rightGame]; aesop)
  inj' _ := by simp [Concept.copy, Ioi_inj]
  map_rel_iff' := Iic_subset_Iic

@[simp] theorem left_leftGame (x : Game) : (leftGame x).left = {y | y.toGame ⧏ x}:= rfl
@[simp] theorem right_leftGame (x : Game) : (leftGame x).right = {y | x ≤ y.toGame} := rfl
@[simp] theorem left_rightGame (x : Game) : left (rightGame x) = {y | y.toGame ≤ x} := rfl
@[simp] theorem right_rightGame (x : Game) : right (rightGame x) = {y | x ⧏ y.toGame} := rfl

@[simp] theorem left_leftSurreal (x : Surreal) : left (leftSurreal x) = Iio x := rfl
@[simp] theorem right_leftSurreal (x : Surreal) : right (leftSurreal x) = Ici x := rfl
@[simp] theorem left_rightSurreal (x : Surreal) : left (rightSurreal x) = Iic x := rfl
@[simp] theorem right_rightSurreal (x : Surreal) : right (rightSurreal x) = Ioi x := rfl

theorem mem_left_leftGame {x y} : y ∈ (leftGame x).left ↔ y.toGame ⧏ x := .rfl
theorem mem_right_leftGame {x y} : y ∈ (leftGame x).right ↔ x ≤ y.toGame := .rfl
theorem mem_left_rightGame {x y} : y ∈ (rightGame x).left ↔ y.toGame ≤ x := .rfl
theorem mem_right_rightGame {x y} : y ∈ (rightGame x).right ↔ x ⧏ y.toGame := .rfl

theorem mem_left_leftSurreal {x y} : y ∈ (leftSurreal x).left ↔ y < x := .rfl
theorem mem_right_leftSurreal {x y} : y ∈ (leftSurreal x).right ↔ x ≤ y := .rfl
theorem mem_left_rightSurreal {x y} : y ∈ (rightSurreal x).left ↔ y ≤ x := .rfl
theorem mem_right_rightSurreal {x y} : y ∈ (rightSurreal x).right ↔ x < y := .rfl

@[simp] theorem leftGame_toGame (x : Surreal) : leftGame x.toGame = leftSurreal x := by
  apply Concept.copy_eq <;> simp <;> rfl

@[simp] theorem rightGame_toGame (x : Surreal) : rightGame x.toGame = rightSurreal x := by
  apply Concept.copy_eq <;> simp <;> rfl

theorem leftSurreal_lt_rightSurreal (x : Surreal) : leftSurreal x < rightSurreal x :=
  lt_iff_nonempty_inter.2 ⟨x, by simp⟩

theorem leftGame_lt_rightGame_iff {x : Game} :
    leftGame x < rightGame x ↔ x ∈ range Surreal.toGame := by
  constructor
  · rw [lt_iff_nonempty_inter]
    rintro ⟨y, hyr, hyl⟩
    exact ⟨y, le_antisymm hyl hyr⟩
  · rintro ⟨x, rfl⟩
    simpa using leftSurreal_lt_rightSurreal x

end Cut
