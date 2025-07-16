/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Violeta Hernández Palacios
-/
import Mathlib.Order.UpperLower.CompleteLattice
import CombinatorialGames.Mathlib.Concept
import CombinatorialGames.Mathlib.Neg
import CombinatorialGames.Surreal.Birthday.Basic

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

/-! ### Basic definitions -/

/-- The left set in a cut. This is an alias for `Concept.extent`. -/
def left (x : Cut) := x.extent
/-- The right set in a cut. This is an alias for `Concept.intent`. -/
def right (x : Cut) := x.intent

alias left_lt_right := Concept.rel_extent_intent
alias disjoint_left_right := Concept.disjoint_extent_intent
alias codisjoint_left_right := Concept.codisjoint_extent_intent
alias isCompl_left_right := Concept.isCompl_extent_intent

theorem isLowerSet_left (c : Cut) : IsLowerSet c.left := c.isLowerSet_extent'
theorem isUpperSet_right (c : Cut) : IsUpperSet c.right := c.isUpperSet_intent'

@[ext] theorem ext {c d : Cut} (h : c.left = d.left) : c = d := Concept.ext h
theorem ext' {c d : Cut} (h : c.right = d.right) : c = d := Concept.ext' h

theorem left_injective : Function.Injective left := Concept.extent_injective
theorem right_injective : Function.Injective right := Concept.intent_injective

@[simp] theorem left_inj {c d : Cut} : c.left = d.left ↔ c = d := left_injective.eq_iff
@[simp] theorem right_inj {c d : Cut} : c.right = d.right ↔ c = d := right_injective.eq_iff

@[simp] theorem left_subset_left_iff {c d : Cut}: c.left ⊆ d.left ↔ c ≤ d := .rfl
@[simp] theorem left_ssubset_left_iff {c d : Cut} : c.left ⊂ d.left ↔ c < d := .rfl

@[simp] theorem right_subset_right_iff {c d : Cut}: c.right ⊆ d.right ↔ d ≤ c :=
  Concept.intent_subset_intent_iff
@[simp] theorem right_ssubset_right_iff {c d : Cut} : c.right ⊂ d.right ↔ d < c :=
  Concept.intent_ssubset_intent_iff

@[simp] theorem compl_left (x : Cut) : x.leftᶜ = x.right := (isCompl_left_right x).compl_eq
@[simp] theorem compl_right (x : Cut) : x.rightᶜ = x.left := (isCompl_left_right x).eq_compl.symm

@[simp] theorem right_bot : (⊥ : Cut).right = univ := rfl
@[simp] theorem left_bot : (⊥ : Cut).left = ∅ := by simpa using (compl_right ⊥).symm

@[simp] theorem left_top : (⊤ : Cut).left = univ := rfl
@[simp] theorem right_top : (⊤ : Cut).right = ∅ := by simpa using (compl_left ⊤).symm

instance : IsTotal Cut (· ≤ ·) where
  total a b := le_total (α := LowerSet _) ⟨_, isLowerSet_left a⟩ ⟨_, isLowerSet_left b⟩

noncomputable instance : LinearOrder Cut :=
  by classical exact Lattice.toLinearOrder _

noncomputable instance : CompleteLinearOrder Cut where
  __ := instLinearOrder
  __ := Concept.instCompleteLattice
  __ := LinearOrder.toBiheytingAlgebra

@[simp] theorem left_min (x y : Cut) : (min x y).left = x.left ∩ y.left := rfl
@[simp] theorem right_min (x y : Cut) : (min x y).right = x.right ∪ y.right := by
  simpa [compl_inter] using (compl_left (min x y)).symm

@[simp] theorem right_max (x y : Cut) : (max x y).right = x.right ∩ y.right := rfl
@[simp] theorem left_max (x y : Cut) : (max x y).left = x.left ∪ y.left := by
  simpa [compl_inter] using (compl_right (max x y)).symm

@[simp] theorem left_sInf (s : Set Cut) : (sInf s).left = ⋂ x ∈ s, x.left := rfl
@[simp] theorem right_sInf (s : Set Cut) : (sInf s).right = ⋃ x ∈ s, x.right := by
  simpa using (compl_left (sInf s)).symm

@[simp] theorem right_sSup (s : Set Cut) : (sSup s).right = ⋂ x ∈ s, x.right := rfl
@[simp] theorem left_sSup (s : Set Cut) : (sSup s).left = ⋃ x ∈ s, x.left := by
  simpa using (compl_right (sSup s)).symm

-- TODO: PR the iInf/iSup versions for concepts to Mathlib

@[simp] theorem left_iInf {ι} (f : ι → Cut) : (⨅ i, f i).left = ⋂ i, (f i).left := by simp [iInf]
@[simp] theorem right_iInf {ι} (f : ι → Cut) : (⨅ i, f i).right = ⋃ i, (f i).right := by simp [iInf]

@[simp] theorem right_iSup {ι} (f : ι → Cut) : (⨆ i, f i).right = ⋂ i, (f i).right := by simp [iSup]
@[simp] theorem left_iSup {ι} (f : ι → Cut) : (⨆ i, f i).left = ⋃ i, (f i).left := by simp [iSup]

theorem lt_iff_nonempty_inter {x y : Cut} : x < y ↔ (x.right ∩ y.left).Nonempty := by
  rw [← not_le, ← left_subset_left_iff, ← diff_nonempty, diff_eq_compl_inter, compl_left]

instance : Neg Cut where
  neg x := {
    extent := -x.intent
    intent := -x.extent
    upperPolar_extent := by
      ext
      simp_rw [← Concept.lowerPolar_intent, upperPolar, lowerPolar, mem_setOf]
      rw [← (Equiv.neg _).forall_congr_right]
      simp [neg_lt]
    lowerPolar_intent := by
      ext
      simp_rw [← Concept.upperPolar_extent, upperPolar, lowerPolar, mem_setOf]
      rw [← (Equiv.neg _).forall_congr_right]
      simp [lt_neg]
  }

@[simp] theorem left_neg (x : Cut) : (-x).left = -x.right := rfl
@[simp] theorem right_neg (x : Cut) : (-x).right = -x.left := rfl

instance : InvolutiveNeg Cut where
  neg_neg x := by ext; simp

@[simp] theorem neg_bot : -(⊥ : Cut) = ⊤ := by ext; simp
@[simp] theorem neg_top : -(⊤ : Cut) = ⊥ := by ext; simp

@[simp] theorem neg_min (x y : Cut) : -min x y = max (-x) (-y) := by ext; simp
@[simp] theorem neg_max (x y : Cut) : -max x y = min (-x) (-y) := by ext; simp

@[simp]
theorem neg_sInf (s : Set Cut) : -sInf s = sSup (-s) := by
  ext
  rw [left_neg, right_sInf, mem_neg, mem_iUnion, ← (Equiv.neg _).exists_congr_right]
  simp

@[simp]
theorem neg_sSup (s : Set Cut) : -sSup s = sInf (-s) := by
  rw [← neg_neg (sInf _), neg_sInf, neg_neg]

@[simp] theorem neg_iInf {ι} (f : ι → Cut) : - ⨅ i, f i = ⨆ i, - f i := by
  simp [iInf, iSup, neg_range]
@[simp] theorem neg_iSup {ι} (f : ι → Cut) : - ⨆ i, f i = ⨅ i, - f i := by
  simp [iInf, iSup, neg_range]

@[simp]
protected theorem neg_le_neg_iff {x y : Cut} : -x ≤ -y ↔ y ≤ x := by
  rw [← left_subset_left_iff, left_neg, left_neg, neg_subset_neg, right_subset_right_iff]

protected theorem neg_le {x y : Cut} : -x ≤ y ↔ -y ≤ x := by
  simpa using @Cut.neg_le_neg_iff x (-y)
protected theorem le_neg {x y : Cut} : x ≤ -y ↔ y ≤ -x := by
  simpa using @Cut.neg_le_neg_iff (-x) y

@[simp]
protected theorem neg_lt_neg_iff {x y : Cut} : -x < -y ↔ y < x := by
  simp [← not_le]

protected theorem neg_lt {x y : Cut} : -x < y ↔ -y < x := by
  simpa using @Cut.neg_lt_neg_iff x (-y)
protected theorem lt_neg {x y : Cut} : x < -y ↔ y < -x := by
  simpa using @Cut.neg_lt_neg_iff (-x) y

/-! ### Cuts from games -/

/-- The left cut of a game `x` is such that its right set consists of surreals
equal or larger to it. -/
def leftGame : Game →o Cut where
  toFun x := {
    extent := {y | y.toGame ⧏ x}
    intent := {y | x ≤ y.toGame}
    upperPolar_extent := by
      refine Set.ext fun y ↦ ⟨?_, fun hy z hz ↦ ?_⟩
      · simp_all [upperPolar, not_imp_comm]
      · simpa using not_le_of_not_le_of_le hz hy
    lowerPolar_intent := by
      refine Set.ext fun y ↦ ⟨fun H hx ↦ (H hx).false, fun hy z hz ↦ ?_⟩
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
      refine Set.ext fun y ↦ ⟨fun H hx ↦ (H hx).false, fun hy z hz ↦ ?_⟩
      simpa using not_le_of_le_of_not_le hz hy
    lowerPolar_intent := by
      refine Set.ext fun y ↦ ⟨?_, fun hy z hz ↦ ?_⟩
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
@[simp] theorem left_rightGame (x : Game) : (rightGame x).left = {y | y.toGame ≤ x} := rfl
@[simp] theorem right_rightGame (x : Game) : (rightGame x).right = {y | x ⧏ y.toGame} := rfl

@[simp] theorem left_leftSurreal (x : Surreal) : (leftSurreal x).left = Iio x := rfl
@[simp] theorem right_leftSurreal (x : Surreal) : (leftSurreal x).right = Ici x := rfl
@[simp] theorem left_rightSurreal (x : Surreal) : (rightSurreal x).left = Iic x := rfl
@[simp] theorem right_rightSurreal (x : Surreal) : (rightSurreal x).right = Ioi x := rfl

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

@[simp] theorem neg_leftGame (x : Game) : -leftGame x = rightGame (-x) := by
  ext; simp [le_neg]

@[simp] theorem neg_rightGame (x : Game) : -rightGame x = leftGame (-x) := by
  ext; simp [neg_le]

@[simp]
theorem neg_leftGame_image (s : Set Game) : -leftGame '' s = rightGame '' (-s) := by
  rw [← image_neg_of_apply_neg_eq_neg]
  simp

@[simp]
theorem neg_rightGame_image (s : Set Game) : -rightGame '' s = leftGame '' (-s) := by
  rw [← image_neg_of_apply_neg_eq_neg]
  simp

@[simp] theorem neg_leftSurreal (x : Surreal) : -leftSurreal x = rightSurreal (-x) := by
  ext; simp [le_neg]

@[simp] theorem neg_rightSurreal (x : Surreal) : -rightSurreal x = leftSurreal (-x) := by
  ext; simp [lt_neg]

@[simp]
theorem neg_leftSurreal_image (s : Set Surreal) : -leftSurreal '' s = rightSurreal '' (-s) := by
  rw [← image_neg_of_apply_neg_eq_neg]
  simp

@[simp]
theorem neg_rightSurreal_image (s : Set Surreal) : -rightSurreal '' s = leftSurreal '' (-s) := by
  rw [← image_neg_of_apply_neg_eq_neg]
  simp

@[simp]
theorem le_leftSurreal_iff {x : Cut} {y : Surreal} : x ≤ leftSurreal y ↔ y ∈ x.right := by
  rw [← left_subset_left_iff, left_leftSurreal, ← compl_left, mem_compl_iff]
  constructor
  · intro h hy
    simpa using h hy
  · intro hy z hz
    rw [mem_Iio]
    contrapose! hy
    exact isLowerSet_left x hy hz

@[simp]
theorem leftSurreal_lt_iff {x : Surreal} {y : Cut} : leftSurreal x < y ↔ x ∈ y.left := by
  rw [← compl_right, mem_compl_iff, ← le_leftSurreal_iff, ← not_le]

@[simp]
theorem rightSurreal_le_iff {x : Surreal} {y : Cut} : rightSurreal x ≤ y ↔ x ∈ y.left := by
  simpa [← neg_rightSurreal] using @le_leftSurreal_iff (-y) (-x)

@[simp]
theorem lt_rightSurreal_iff {x : Cut} {y : Surreal} : x < rightSurreal y ↔ y ∈ x.right := by
  simpa [← neg_rightSurreal] using @leftSurreal_lt_iff (-y) (-x)

theorem leftSurreal_lt_rightSurreal (x : Surreal) : leftSurreal x < rightSurreal x := by
  simp

theorem leftSurreal_lt_rightSurreal_iff {x y : Surreal} :
    leftSurreal x < rightSurreal y ↔ x ≤ y := by
  simp

@[simp]
theorem rightSurreal_lt_leftSurreal_iff {x y : Surreal} :
    rightSurreal x < leftSurreal y ↔ x < y := by
  rw [← left_ssubset_left_iff, left_rightSurreal, left_leftSurreal]
  constructor <;> intro h
  · exact h.1 (mem_Iic.2 le_rfl)
  · constructor <;> simpa

theorem leftGame_lt_rightGame_iff {x : Game} :
    leftGame x < rightGame x ↔ x ∈ range Surreal.toGame := by
  constructor
  · rw [lt_iff_nonempty_inter]
    exact fun ⟨y, hyr, hyl⟩ ↦ ⟨y, le_antisymm hyl hyr⟩
  · aesop

theorem sInf_leftSurreal_right (x : Cut) : sInf (leftSurreal '' x.right) = x := by
  ext y
  simp_rw [left_sInf, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right,
    left_leftSurreal, mem_iInter, mem_Iio]
  refine ⟨fun H ↦ ?_, fun hy z ↦ left_lt_right hy⟩
  rw [← compl_right]
  exact fun hy ↦ (H y hy).false

theorem sSup_rightSurreal_left (x : Cut) : sSup (rightSurreal '' x.left) = x := by
  rw [← neg_inj, neg_sSup, neg_rightSurreal_image, ← right_neg, sInf_leftSurreal_right]

/-! ### Calculating cuts -/

/-- The supremum of all right cuts of left options of `x`.

If `infRight x ≤ supLeft x` then `leftGame x = supLeft x` and `rightGame x = infRight x`; otherwise,
`x` is equivalent to the simplest surreal between `supLeft x` and `infRight x`. -/
def supLeft (x : IGame) : Cut :=
  ⨆ i ∈ x.leftMoves, rightGame (.mk i)

theorem left_supLeft (x : IGame) :
    (supLeft x).left = ⋃ i ∈ x.leftMoves, {y | y.toGame ≤ .mk i} := by
  simp [supLeft]

theorem right_supLeft (x : IGame) :
    (supLeft x).right = ⋂ i ∈ x.leftMoves, {y | .mk i ⧏ y.toGame} := by
  simp [supLeft]

/-- The infimum of all left cuts of right options of `x`.

If `infRight x ≤ supLeft x` then `leftGame x = supLeft x` and `rightGame x = infRight x`; otherwise,
`x` is equivalent to the simplest surreal between `supLeft x` and `infRight x`. -/
def infRight (x : IGame) : Cut :=
  ⨅ i ∈ x.rightMoves, leftGame (.mk i)

theorem left_infRight (x : IGame) :
    (infRight x).left = ⋂ i ∈ x.rightMoves, {y | y.toGame ⧏ .mk i} := by
  simp [infRight]

theorem right_infRight (x : IGame) :
    (infRight x).right = ⋃ i ∈ x.rightMoves, {y | .mk i ≤ y.toGame} := by
  simp [infRight]

@[simp]
theorem neg_supLeft (x : IGame) : -supLeft x = infRight (-x) := by
  refine eq_of_forall_le_iff fun y ↦ ?_
  rw [supLeft, infRight, le_iInf_iff, ← (Equiv.neg _).forall_congr_right]
  simp

@[simp]
theorem neg_infRight (x : IGame) : -infRight x = supLeft (-x) := by
  rw [← neg_neg (supLeft _), neg_supLeft, neg_neg]

theorem leftGame_eq_supLeft_of_le {x : IGame} (h : infRight x ≤ supLeft x) :
    leftGame (.mk x) = supLeft x := by
  refine ext' (Set.ext fun y ↦ ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩)
  · rw [right_supLeft, mem_iInter₂]
    exact fun i hi ↦ not_le_of_not_le_of_le (mt Game.mk_le_mk.1 (leftMove_lf hi)) hy
  · rw [mem_right_leftGame, ← y.out_eq, toGame_mk, Game.mk_le_mk, le_iff_forall_lf]
    constructor <;> intro z hz
    · rw [right_supLeft, mem_iInter₂] at hy
      rw [← Game.mk_le_mk, ← toGame_mk, y.out_eq]
      exact hy z hz
    · rw [← right_subset_right_iff] at h
      apply h at hy
      rw [right_infRight, mem_iUnion₂] at hy
      obtain ⟨i, hi, hy⟩ := hy
      rw [mem_setOf, ← y.out_eq, toGame_mk, Game.mk_le_mk] at hy
      exact lf_of_rightMove_le (hy.trans (Numeric.lt_rightMove hz).le) hi

theorem rightGame_eq_infRight_of_le {x : IGame} : infRight x ≤ supLeft x →
    rightGame (.mk x) = infRight x := by
  simpa [← neg_supLeft, ← neg_infRight, ← neg_leftGame, ← neg_rightGame] using
    @leftGame_eq_supLeft_of_le (-x)

/-- A surreal `x` fits between two cuts `y` and `z` when `x ∈ y.right ∩ z.left`. -/
def Fits (x : Surreal) (y z : Cut) : Prop :=
  x ∈ y.right ∩ z.left

theorem Fits.lt {x : Surreal} {y z : Cut} (h : Fits x y z) : y < z :=
  lt_iff_nonempty_inter.mpr ⟨x, h⟩

@[simp]
theorem fits_leftSurreal_rightSurreal {x y : Surreal} :
    Fits x (leftSurreal y) (rightSurreal y) ↔ x = y := by
  simp [Fits, le_antisymm_iff, and_comm]

theorem Fits.le_leftSurreal {x : Surreal} {y z : Cut} (h : Fits x y z) : y ≤ leftSurreal x :=
  le_leftSurreal_iff.mpr h.1

theorem Fits.rightSurreal_le {x : Surreal} {y z : Cut} (h : Fits x y z) : rightSurreal x ≤ z :=
  rightSurreal_le_iff.mpr h.2

theorem not_fits_iff {x : Surreal} {y z : Cut} : ¬ Fits x y z ↔ x ∈ y.left ∪ z.right := by
  rw [Fits, ← mem_compl_iff, compl_inter, compl_left, compl_right]

/-- The simplest surreal number (in terms of birthday) that fits between two cuts. -/
noncomputable def simplestBtwn {x y : Cut} (h : x < y) : Surreal :=
  Classical.choose <|
    exists_minimalFor_of_wellFoundedLT _ birthday (lt_iff_nonempty_inter.1 h)

private theorem simplestBtwn_spec {x y : Cut} (h : x < y) :
    MinimalFor (fun z ↦ z ∈ x.right ∩ y.left) birthday (simplestBtwn h) :=
  Classical.choose_spec _

theorem fits_simplestBtwn {x y : Cut} (h : x < y) : Fits (simplestBtwn h) x y :=
  (simplestBtwn_spec h).1

theorem birthday_simplestBtwn_le_of_fits {x y : Cut} {z : Surreal}
    (hz : Fits z x y) : (simplestBtwn hz.lt).birthday ≤ z.birthday := by
  by_contra! H
  exact H.not_ge <| (simplestBtwn_spec hz.lt).2 hz H.le

theorem fits_supLeft_infRight {x y : IGame} [x.Numeric] :
    Fits (.mk x) (supLeft y) (infRight y) ↔ x.Fits y := by
  simp [Fits, supLeft, infRight, IGame.Fits]

theorem simplestBtwn_leftGame_rightGame {x : Game} (h : leftGame x < rightGame x) :
    (simplestBtwn h).toGame = x := by
  rw [leftGame_lt_rightGame_iff] at h
  obtain ⟨x, rfl⟩ := h
  simpa [le_antisymm_iff] using fits_simplestBtwn h

@[simp]
theorem simplestBtwn_leftSurreal_rightSurreal (x : Surreal) :
    simplestBtwn (leftSurreal_lt_rightSurreal x) = x := by
  convert simplestBtwn_leftGame_rightGame (x := x.toGame) _ <;> simp

/-- If `x` is a game with `supLeft x < infRight x`, then the simplest number between those two cuts
is equal to `x`. -/
theorem simplestBtwn_supLeft_infRight {x : IGame} (h : supLeft x < infRight x) :
    (simplestBtwn h).toGame = .mk x := by
  obtain ⟨y, _, hy, hy'⟩ := birthday_eq_iGameBirthday (simplestBtwn h)
  have H := fits_simplestBtwn h
  rw [← hy, fits_supLeft_infRight] at H
  rw [← hy, toGame_mk, Game.mk_eq_mk]
  refine H.equiv_of_forall_birthday_le fun z hz hzx ↦ ?_
  rw [← fits_supLeft_infRight] at hzx
  exact (hy' ▸ birthday_simplestBtwn_le_of_fits hzx).trans (birthday_mk_le z)

theorem supLeft_lt_infRight_of_equiv_numeric {x y : IGame} [y.Numeric] (h : x ≈ y) :
    supLeft x < infRight x := by
  replace h := Game.mk_eq h
  by_contra! hx
  have hx' := hx
  simp_rw [← leftGame_eq_supLeft_of_le hx, ← rightGame_eq_infRight_of_le hx, h, ← toGame_mk,
    leftGame_toGame, rightGame_toGame] at hx'
  simp at hx'

theorem supLeft_lt_infRight_of_numeric (x : IGame) [x.Numeric] : supLeft x < infRight x :=
  supLeft_lt_infRight_of_equiv_numeric .rfl

end Cut
end Surreal
