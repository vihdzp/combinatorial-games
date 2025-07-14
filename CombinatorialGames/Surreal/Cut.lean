/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
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

noncomputable instance : DecidableEq Cut := Classical.decEq Cut

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

-- add le and lt iffs

instance : IsTotal Cut (· ≤ ·) where
  total a b := le_total (α := LowerSet _) ⟨_, isLowerSet_left a⟩ ⟨_, isLowerSet_left b⟩

noncomputable instance : LinearOrder Cut :=
  by classical exact Lattice.toLinearOrder _

noncomputable instance : CompleteLinearOrder Cut where
  __ := instLinearOrder
  __ := Concept.instCompleteLattice
  __ := LinearOrder.toBiheytingAlgebra

@[simp] theorem compl_left (x : Cut) : (left x)ᶜ = right x := (isCompl_left_right x).compl_eq
@[simp] theorem compl_right (x : Cut) : (right x)ᶜ = left x := (isCompl_left_right x).eq_compl.symm

theorem lt_iff_nonempty_inter {x y : Cut} : x < y ↔ (right x ∩ left y).Nonempty := by
  rw [← not_le, ← Concept.extent_subset_extent_iff, ← diff_nonempty, diff_eq, ← left, compl_left,
    inter_comm]

  #exit

/-- The cut just to the left of a surreal number. -/
def leftSurreal : Surreal ↪o Cut where
  toFun x := {
    extent := Iio x
    intent := Ici x
    upperPolar_extent := by ext; simpa [upperPolar] using forall_lt_iff_le
    lowerPolar_intent := by
      aesop (add apply unsafe [lt_trans]) (add simp [lowerPolar, le_iff_eq_or_lt])
  }
  inj' x y := by simp [Ici_inj]
  map_rel_iff' := Iio_subset_Iio_iff

/-- The cut just to the right of a surreal number. -/
def rightSurreal : Surreal ↪o Cut where
  toFun x := {
    extent := Iic x
    intent := Ioi x
    upperPolar_extent := by
      aesop (add apply unsafe [lt_trans]) (add simp [upperPolar, le_iff_eq_or_lt])
    lowerPolar_intent := by ext; simpa [lowerPolar] using forall_gt_iff_le
  }
  inj' x y := by simp [Ioi_inj]
  map_rel_iff' := Iic_subset_Iic

@[simp] theorem left_leftSurreal {x : Surreal} : left (leftSurreal x) = Iio x := rfl
@[simp] theorem right_leftSurreal {x : Surreal} : right (leftSurreal x) = Ici x := rfl
@[simp] theorem left_rightSurreal {x : Surreal} : left (rightSurreal x) = Iic x := rfl
@[simp] theorem right_rightSurreal {x : Surreal} : right (rightSurreal x) = Ioi x := rfl

theorem leftSurreal_lt_rightSurreal (x : Surreal) : leftSurreal x < rightSurreal x := by
  rw [← not_le, extent_in]

  #exit

theorem leftSurreal_le_rightSurreal (x : Surreal) : leftSurreal x ≤ rightSurreal x :=
  (leftSurreal_lt_rightSurreal x).le

/--
The cut to the left of a game.
-/
def leftGame : Game →o Cut where
  toFun x := {
    left := {y | y.toGame ⧏ x}
    right := {y | x ≤ y.toGame}
    left_lf_right' l hl r hr := mt toGame.le_iff_le.2 (not_le_of_not_le_of_le hl hr)
    codisjoint' := codisjoint_iff_le_sup.2 (by simp [union_def, (em (x ≤ toGame _)).symm])
  }
  monotone' x y hxy := le_iff_right.2 (by simp +contextual [hxy.trans])

/--
The cut to the right of a game.
-/
def rightGame : Game →o Cut where
  toFun x := {
    left := {y | y.toGame ≤ x}
    right := {y | x ⧏ y.toGame}
    left_lf_right' l hl r hr := mt toGame.le_iff_le.2 (not_le_of_le_of_not_le hl hr)
    codisjoint' := codisjoint_iff_le_sup.2 (by simp [union_def, em (toGame _ ≤ x)])
  }
  monotone' x y hxy := le_iff_left.2 (by simp +contextual [hxy.trans'])

@[simp]
theorem mem_left_leftGame {x : Game} {y : Surreal} :
    y ∈ (leftGame x).left ↔ y.toGame ⧏ x := Iff.rfl

@[simp]
theorem mem_right_leftGame {x : Game} {y : Surreal} :
    y ∈ (leftGame x).right ↔ x ≤ y.toGame := Iff.rfl

@[simp]
theorem mem_left_rightGame {x : Game} {y : Surreal} :
    y ∈ (rightGame x).left ↔ y.toGame ≤ x := Iff.rfl

@[simp]
theorem mem_right_rightGame {x : Game} {y : Surreal} :
    y ∈ (rightGame x).right ↔ x ⧏ y.toGame := Iff.rfl

@[simp]
theorem leftGame_toGame (x : Surreal) : leftGame x.toGame = leftSurreal x := by
  apply Cut.ext <;> apply Set.ext <;> simp

@[simp]
theorem rightGame_toGame (x : Surreal) : rightGame x.toGame = rightSurreal x := by
  apply Cut.ext <;> apply Set.ext <;> simp

theorem leftGame_lt_rightGame_iff {x : Game} :
    leftGame x < rightGame x ↔ x ∈ range Surreal.toGame := by
  constructor
  · rintro ⟨y, hyl, hyr⟩
    exact ⟨y, le_antisymm hyl hyr⟩
  · rintro ⟨x, rfl⟩
    simp [leftSurreal_lt_rightSurreal]

/--
Auxiliary definition for computing the `leftGame` of an explicitly given game.
-/
abbrev iGameLeft (x : IGame) : Cut :=
  ⨆ i ∈ x.leftMoves, rightGame (.mk i)
/--
Auxiliary definition for computing the `rightGame` of an explicitly given game.
-/
abbrev iGameRight (x : IGame) : Cut :=
  ⨅ i ∈ x.rightMoves, leftGame (.mk i)

theorem equiv_of_mem_iGameLeft_of_mem_iGameRight {x y : IGame} [y.Numeric]
    (hyl : .mk y ∈ (iGameLeft x).right) (hyr : .mk y ∈ (iGameRight x).left)
    (hol : ∀ z ∈ y.leftMoves, ∀ (_ : z.Numeric), .mk z ∈ (iGameLeft x).left)
    (hor : ∀ z ∈ y.rightMoves, ∀ (_ : z.Numeric), .mk z ∈ (iGameRight x).right) :
    x ≈ y := by
  refine ⟨le_iff_forall_lf.2 ⟨?_, ?_⟩, le_iff_forall_lf.2 ⟨?_, ?_⟩⟩
  · intro z hz
    simp_rw [right_iSup, mem_iInter] at hyl
    simpa using hyl z hz
  · intro z hz
    have nz := Numeric.of_mem_rightMoves hz
    specialize hor z hz nz
    simp_rw [iGameRight, right_iInf, mem_iUnion] at hor
    obtain ⟨i, hi, hor⟩ := hor
    refine lf_of_rightMove_le ?_ hi
    simpa using hor
  · intro z hz
    have nz := Numeric.of_mem_leftMoves hz
    specialize hol z hz nz
    simp_rw [iGameLeft, left_iSup, mem_iUnion] at hol
    obtain ⟨i, hi, hol⟩ := hol
    refine lf_of_le_leftMove ?_ hi
    simpa using hol
  · intro z hz
    simp_rw [left_iInf, mem_iInter] at hyr
    simpa using hyr z hz

theorem leftGame_eq_iGameLeft_of_le {x : IGame} (h : iGameRight x ≤ iGameLeft x) :
    leftGame (.mk x) = iGameLeft x := by
  refine ext_right (Set.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩)
  · rw [mem_right_leftGame] at hy
    simp_rw [right_iSup, mem_iInter, mem_right_rightGame]
    intro i hi
    refine not_le_of_not_le_of_le ?_ hy
    exact mt Game.mk_le_mk.1 (lf_of_le_leftMove le_rfl hi)
  · rw [mem_right_leftGame, ← y.out_eq, toGame_mk, Game.mk_le_mk, le_iff_forall_lf]
    constructor
    · intro i hi
      simp_rw [right_iSup, mem_iInter, mem_right_rightGame] at hy
      rw [← Game.mk_le_mk, ← toGame_mk, y.out_eq]
      exact hy i hi
    · intro z hz
      rw [le_iff_right] at h
      apply h at hy
      simp_rw [right_iInf, mem_iUnion, mem_right_leftGame] at hy
      obtain ⟨i, hi, hy⟩ := hy
      refine lf_of_rightMove_le ?_ hi
      rw [← y.out_eq, toGame_mk, Game.mk_le_mk] at hy
      exact hy.trans (Numeric.lt_rightMove hz).le

theorem rightGame_eq_iGameRight_of_le {x : IGame} (h : iGameRight x ≤ iGameLeft x) :
    rightGame (.mk x) = iGameRight x := by
  refine ext_left (Set.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩)
  · rw [mem_left_rightGame] at hy
    simp_rw [left_iInf, mem_iInter, mem_left_leftGame]
    intro i hi
    apply not_le_of_le_of_not_le hy
    exact mt Game.mk_le_mk.1 (lf_of_rightMove_le le_rfl hi)
  · rw [mem_left_rightGame, ← y.out_eq, toGame_mk, Game.mk_le_mk, le_iff_forall_lf]
    constructor
    · intro z hz
      rw [le_iff_left] at h
      apply h at hy
      simp_rw [left_iSup, mem_iUnion, mem_left_rightGame] at hy
      obtain ⟨i, hi, hy⟩ := hy
      refine lf_of_le_leftMove ?_ hi
      rw [← y.out_eq, toGame_mk, Game.mk_le_mk] at hy
      exact (Numeric.leftMove_lt hz).le.trans hy
    · intro i hi
      simp_rw [left_iInf, mem_iInter, mem_left_leftGame] at hy
      rw [← Game.mk_le_mk, ← toGame_mk y.out, y.out_eq]
      exact hy i hi
