/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Birthday.Basic
import Mathlib.Order.Concept
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.UpperLower.CompleteLattice

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

theorem left_lt_right {x : Cut} {y z : Surreal} (hy : y ∈ x.left) (hz : z ∈ x.right) : y < z :=
  x.rel_extent_intent hy hz

theorem disjoint_left_right (x : Cut) : Disjoint x.left x.right := x.disjoint_extent_intent
theorem codisjoint_left_right (x : Cut) : Codisjoint x.left x.right := x.codisjoint_extent_intent
theorem isCompl_left_right (x : Cut) : IsCompl x.left x.right := x.isCompl_extent_intent

theorem isLowerSet_left (c : Cut) : IsLowerSet c.left := by
  intro a b hb ha
  obtain rfl | hb := hb.eq_or_lt
  · assumption
  · exact c.mem_extent_of_rel_extent hb ha

theorem isUpperSet_right (c : Cut) : IsUpperSet c.right := by
  intro a b hb ha
  obtain rfl | hb := hb.eq_or_lt
  · assumption
  · exact c.mem_intent_of_intent_rel hb ha

@[ext] theorem ext {c d : Cut} (h : c.left = d.left) : c = d := Concept.ext h
theorem ext' {c d : Cut} (h : c.right = d.right) : c = d := Concept.ext' h

theorem left_injective : Function.Injective left := Concept.extent_injective
theorem right_injective : Function.Injective right := Concept.intent_injective

@[simp] theorem left_inj {c d : Cut} : c.left = d.left ↔ c = d := left_injective.eq_iff
@[simp] theorem right_inj {c d : Cut} : c.right = d.right ↔ c = d := right_injective.eq_iff

@[simp] theorem left_subset_left_iff {c d : Cut} : c.left ⊆ d.left ↔ c ≤ d := .rfl
@[simp] theorem left_ssubset_left_iff {c d : Cut} : c.left ⊂ d.left ↔ c < d := .rfl

@[simp] theorem right_subset_right_iff {c d : Cut} : c.right ⊆ d.right ↔ d ≤ c :=
  Concept.intent_subset_intent_iff
@[simp] theorem right_ssubset_right_iff {c d : Cut} : c.right ⊂ d.right ↔ d < c :=
  Concept.intent_ssubset_intent_iff

@[simp] theorem compl_left (x : Cut) : x.leftᶜ = x.right := (isCompl_left_right x).compl_eq
@[simp] theorem compl_right (x : Cut) : x.rightᶜ = x.left := (isCompl_left_right x).eq_compl.symm

@[simp] theorem notMem_left_iff {x : Cut} {y : Surreal} : y ∉ x.left ↔ y ∈ x.right := by
  simp [← mem_compl_iff]
@[simp] theorem notMem_right_iff {x : Cut} {y : Surreal} : y ∉ x.right ↔ y ∈ x.left := by
  simp [← mem_compl_iff]

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
  __ := LinearOrder.toBiheytingAlgebra _

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

instance : Nontrivial Cut :=
  ⟨⊥, ⊤, by apply_fun left; simpa using empty_ne_univ⟩

theorem lt_iff_nonempty_inter {x y : Cut} : x < y ↔ (x.right ∩ y.left).Nonempty := by
  rw [← not_le, ← left_subset_left_iff, ← diff_nonempty, diff_eq_compl_inter, compl_left]

instance : Neg Cut where
  neg x := {
    extent := -x.intent
    intent := -x.extent
    upperPolar_extent := by
      ext
      simp_rw [← Concept.lowerPolar_intent, upperPolar, lowerPolar]
      simp [neg_lt]
    lowerPolar_intent := by
      ext
      simp_rw [← Concept.upperPolar_extent, upperPolar, lowerPolar]
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

@[simp] theorem neg_sInf (s : Set Cut) : -sInf s = sSup (-s) := by ext; simp
@[simp] theorem neg_sSup (s : Set Cut) : -sSup s = sInf (-s) := by ext; simp

@[simp] theorem neg_iInf {ι} (f : ι → Cut) : - ⨅ i, f i = ⨆ i, - f i := by ext; simp
@[simp] theorem neg_iSup {ι} (f : ι → Cut) : - ⨆ i, f i = ⨅ i, - f i := by ext; simp

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
      · simpa using mt hy.trans hz
    lowerPolar_intent := by
      refine Set.ext fun y ↦ ⟨fun H hx ↦ (H hx).false, fun hy z hz ↦ ?_⟩
      simpa using mt hz.trans hy
  }
  monotone' x y hy z hz := mt hy.trans hz

/-- The right cut of a game `x` is such that its right set consists of surreals
equal or lesser to it. -/
def rightGame : Game →o Cut where
  toFun x := {
    extent := {y | y.toGame ≤ x}
    intent := {y | x ⧏ y.toGame}
    upperPolar_extent := by
      refine Set.ext fun y ↦ ⟨fun H hx ↦ (H hx).false, fun hy z hz ↦ ?_⟩
      simpa using mt hz.trans' hy
    lowerPolar_intent := by
      refine Set.ext fun y ↦ ⟨?_, fun hy z hz ↦ ?_⟩
      · simp_all [lowerPolar, not_imp_comm]
      · simpa using mt hy.trans' hz
  }
  monotone' x y hy z := le_trans' hy

/-- The cut just to the left of a surreal number. -/
def leftSurreal : Surreal ↪o Cut where
  toFun x := (leftGame x.toGame).copy
    (Iio x) (Ici x) (by rw [leftGame]; aesop) (by rw [leftGame]; aesop)
  inj' _ := by simp [Concept.copy, Ici_inj]
  map_rel_iff' := Iio_subset_Iio_iff

/-- The cut just to the right of a surreal number. -/
def rightSurreal : Surreal ↪o Cut where
  toFun x := (rightGame x.toGame).copy
    (Iic x) (Ioi x) (by rw [rightGame]; aesop) (by rw [rightGame]; aesop)
  inj' _ := by simp [Concept.copy, Ioi_inj]
  map_rel_iff' := Iic_subset_Iic

@[simp, grind =]
theorem left_leftGame (x : Game) : (leftGame x).left = {y | y.toGame ⧏ x}:= rfl
@[simp, grind =]
theorem right_leftGame (x : Game) : (leftGame x).right = {y | x ≤ y.toGame} := rfl
@[simp, grind =]
theorem left_rightGame (x : Game) : (rightGame x).left = {y | y.toGame ≤ x} := rfl
@[simp, grind =]
theorem right_rightGame (x : Game) : (rightGame x).right = {y | x ⧏ y.toGame} := rfl

@[simp, grind =] theorem left_leftSurreal (x : Surreal) : (leftSurreal x).left = Iio x := rfl
@[simp, grind =] theorem right_leftSurreal (x : Surreal) : (leftSurreal x).right = Ici x := rfl
@[simp, grind =] theorem left_rightSurreal (x : Surreal) : (rightSurreal x).left = Iic x := rfl
@[simp, grind =] theorem right_rightSurreal (x : Surreal) : (rightSurreal x).right = Ioi x := rfl

theorem mem_left_leftGame {x y} : y ∈ (leftGame x).left ↔ y.toGame ⧏ x := .rfl
theorem mem_right_leftGame {x y} : y ∈ (leftGame x).right ↔ x ≤ y.toGame := .rfl
theorem mem_left_rightGame {x y} : y ∈ (rightGame x).left ↔ y.toGame ≤ x := .rfl
theorem mem_right_rightGame {x y} : y ∈ (rightGame x).right ↔ x ⧏ y.toGame := .rfl

theorem mem_left_leftSurreal {x y} : y ∈ (leftSurreal x).left ↔ y < x := .rfl
theorem mem_right_leftSurreal {x y} : y ∈ (leftSurreal x).right ↔ x ≤ y := .rfl
theorem mem_left_rightSurreal {x y} : y ∈ (rightSurreal x).left ↔ y ≤ x := .rfl
theorem mem_right_rightSurreal {x y} : y ∈ (rightSurreal x).right ↔ x < y := .rfl

@[simp, grind =] theorem leftGame_toGame (x : Surreal) : leftGame x.toGame = leftSurreal x := by
  apply Concept.copy_eq <;> simp <;> rfl

@[simp, grind =] theorem rightGame_toGame (x : Surreal) : rightGame x.toGame = rightSurreal x := by
  apply Concept.copy_eq <;> simp <;> rfl

@[simp, grind =]
theorem leftGame_mk (x : IGame) [Numeric x] : leftGame (.mk x) = leftSurreal (.mk x) := by
  rw [← toGame_mk, leftGame_toGame]

@[simp, grind =]
theorem rightGame_mk (x : IGame) [Numeric x] : rightGame (.mk x) = rightSurreal (.mk x) := by
  rw [← toGame_mk, rightGame_toGame]

@[simp, grind =]
theorem leftGame_zero : leftGame 0 = leftSurreal 0 := by simpa using leftGame_toGame 0
@[simp, grind =]
theorem rightGame_zero : rightGame 0 = rightSurreal 0 := by simpa using rightGame_toGame 0

@[simp, grind =]
theorem leftGame_one : leftGame 1 = leftSurreal 1 := by simpa using leftGame_toGame 1
@[simp, grind =]
theorem rightGame_one : rightGame 1 = rightSurreal 1 := by simpa using rightGame_toGame 1

@[simp, grind =] theorem leftGame_neg (x : Game) : leftGame (-x) = -rightGame x := by
  ext; simp [neg_le]

@[simp, grind =] theorem rightGame_neg (x : Game) : rightGame (-x) = -leftGame x := by
  ext; simp [le_neg]

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
  rw [← left_subset_left_iff, left_leftSurreal, ← notMem_left_iff]
  constructor
  · intro h hy
    simpa using h hy
  · intro hy z hz
    rw [mem_Iio]
    contrapose! hy
    exact isLowerSet_left x hy hz

@[simp]
theorem leftSurreal_lt_iff {x : Surreal} {y : Cut} : leftSurreal x < y ↔ x ∈ y.left := by
  rw [← notMem_right_iff, ← le_leftSurreal_iff, ← not_le]

@[simp]
theorem rightSurreal_le_iff {x : Surreal} {y : Cut} : rightSurreal x ≤ y ↔ x ∈ y.left := by
  simpa [← neg_rightSurreal] using @le_leftSurreal_iff (-y) (-x)

@[simp]
theorem lt_rightSurreal_iff {x : Cut} {y : Surreal} : x < rightSurreal y ↔ y ∈ x.right := by
  simpa [← neg_rightSurreal] using @leftSurreal_lt_iff (-y) (-x)

@[simp]
theorem leftSurreal_lt_rightSurreal (x : Surreal) : leftSurreal x < rightSurreal x := by
  simp

@[simp]
theorem leftSurreal_le_rightSurreal (x : Surreal) : leftSurreal x ≤ rightSurreal x :=
  (leftSurreal_lt_rightSurreal x).le

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

theorem leftSurreal_strictMono : StrictMono leftSurreal :=
  fun x y ↦ by simp

theorem rightSurreal_strictMono : StrictMono rightSurreal :=
  fun x y ↦ by simp

theorem leftSurreal_lt_leftSurreal_iff {x y : Surreal} : leftSurreal x < leftSurreal y ↔ x < y :=
  leftSurreal_strictMono.lt_iff_lt

theorem rightSurreal_lt_rightSurreal_iff {x y : Surreal} : leftSurreal x < leftSurreal y ↔ x < y :=
  leftSurreal_strictMono.lt_iff_lt

@[simp]
theorem leftSurreal_inj {x y : Surreal} : leftSurreal x = leftSurreal y ↔ x = y :=
  leftSurreal_strictMono.injective.eq_iff

@[simp]
theorem rightSurreal_inj {x y : Surreal} : rightSurreal x = rightSurreal y ↔ x = y :=
  rightSurreal_strictMono.injective.eq_iff

theorem leftSurreal_covBy_rightSurreal (x : Surreal) : leftSurreal x ⋖ rightSurreal x := by
  refine ⟨leftSurreal_lt_rightSurreal x, fun y ↦ ?_⟩
  simp

@[simp]
theorem leftSurreal_ne_rightSurreal (x y : Surreal) : leftSurreal x ≠ rightSurreal y := by
  refine fun h ↦ h.not_gt ?_
  simpa using h.ge

@[simp]
theorem rightSurreal_ne_leftSurreal (x y : Surreal) : rightSurreal x ≠ leftSurreal y :=
  (leftSurreal_ne_rightSurreal y x).symm

theorem leftGame_lt_rightGame_iff {x : Game} :
    leftGame x < rightGame x ↔ x ∈ range Surreal.toGame := by
  constructor
  · rw [lt_iff_nonempty_inter]
    exact fun ⟨y, hyr, hyl⟩ ↦ ⟨y, le_antisymm hyl hyr⟩
  · aesop

@[simp]
theorem leftGame_ne_bot (x : Game) : leftGame x ≠ ⊥ := by
  apply_fun left
  rw [left_bot, ← Set.nonempty_iff_ne_empty, left_leftGame]
  refine ⟨-(x.birthday + 1), fun h ↦ ?_⟩
  simpa [zero_lt_one.not_ge] using (Game.neg_toGame_birthday_le x).trans h

@[simp]
theorem leftGame_ne_top (x : Game) : leftGame x ≠ ⊤ := by
  apply_fun right
  rw [right_top, ← Set.nonempty_iff_ne_empty, right_leftGame]
  exact ⟨x.birthday, Game.le_toGame_birthday x⟩

@[simp]
theorem rightGame_ne_bot (x : Game) : rightGame x ≠ ⊥ := by
  rw [ne_eq, ← neg_inj, ← leftGame_neg, neg_bot]
  exact leftGame_ne_top _

@[simp]
theorem rightGame_ne_top (x : Game) : rightGame x ≠ ⊤ := by
  rw [ne_eq, ← neg_inj, ← leftGame_neg, neg_top]
  exact leftGame_ne_bot _

@[simp]
theorem leftSurreal_ne_bot (x : Surreal) : leftSurreal x ≠ ⊥ := by
  simpa using leftGame_ne_bot x.toGame

@[simp]
theorem leftSurreal_ne_top (x : Surreal) : leftSurreal x ≠ ⊤ := by
  simpa using leftGame_ne_top x.toGame

@[simp]
theorem rightSurreal_ne_bot (x : Surreal) : rightSurreal x ≠ ⊥ := by
  simpa using rightGame_ne_bot x.toGame

@[simp]
theorem rightSurreal_ne_top (x : Surreal) : rightSurreal x ≠ ⊤ := by
  simpa using rightGame_ne_top x.toGame

theorem sInf_leftSurreal_right (x : Cut) : sInf (leftSurreal '' x.right) = x := by
  ext y
  suffices (∀ i ∈ x.right, y < i) ↔ y ∈ x.left by simpa
  refine ⟨fun H ↦ ?_, fun hy z ↦ left_lt_right hy⟩
  rw [← compl_right]
  exact fun hy ↦ (H y hy).false

theorem sSup_rightSurreal_left (x : Cut) : sSup (rightSurreal '' x.left) = x := by
  rw [← neg_inj, neg_sSup, neg_rightSurreal_image, ← right_neg, sInf_leftSurreal_right]

theorem leftSurreal_mem_of_sInf_eq {s : Set Cut} {x : Surreal}
    (hs : sInf s = leftSurreal x) : leftSurreal x ∈ s := by
  have hs' := hs ▸ leftSurreal_lt_rightSurreal x
  obtain ⟨y, hy, hy'⟩ := sInf_lt_iff.1 hs'
  convert hy
  exact (hs ▸ sInf_le hy).antisymm ((leftSurreal_covBy_rightSurreal x).le_of_lt hy')

theorem rightSurreal_mem_of_sInf_eq {s : Set Cut.{u}} {x : Surreal} [Small.{u} s]
    (hs : sInf s = rightSurreal x) : rightSurreal x ∈ s := by
  by_contra hx
  have (a : s) : ∃ y, leftSurreal y ∈ Ioo (sInf s) a := by
    have : sInf s < a := (sInf_le a.2).lt_of_ne <| by aesop
    obtain ⟨y, hy⟩ := lt_iff_nonempty_inter.1 this
    use y
    simp_all
  choose f hf using this
  suffices rightSurreal !{{x} | range f} ≤ sInf s by
    apply this.not_gt
    simp_all [lt_ofSets_of_mem_left]
  simp_rw [le_sInf_iff, rightSurreal_le_iff, ← leftSurreal_lt_iff]
  intro y hy
  apply (leftSurreal.lt_iff_lt.2 <| ofSets_lt_of_mem_right (mem_range_self ⟨y, hy⟩)).trans
  simp_all

theorem rightSurreal_mem_of_sSup_eq {s : Set Cut} {x : Surreal} :
    sSup s = rightSurreal x → rightSurreal x ∈ s := by
  simpa [← neg_sSup, ← neg_rightSurreal] using @leftSurreal_mem_of_sInf_eq (-s) (-x)

theorem leftSurreal_mem_of_sSup_eq {s : Set Cut.{u}} {x : Surreal} [Small.{u} s] :
    sSup s = leftSurreal x → leftSurreal x ∈ s := by
  simpa [← neg_sSup, ← neg_leftSurreal] using @rightSurreal_mem_of_sInf_eq (-s) (-x)

/-! ### Calculating cuts -/

/-- The supremum of all right cuts of left options of `x`.

If `infRight x ≤ supLeft x` then `leftGame x = supLeft x` and `rightGame x = infRight x`; otherwise,
`x` is equivalent to the simplest surreal between `supLeft x` and `infRight x`. -/
def supLeft (x : IGame) : Cut :=
  ⨆ i ∈ xᴸ, rightGame (.mk i)

theorem left_supLeft (x : IGame) :
    (supLeft x).left = ⋃ i ∈ xᴸ, {y | y.toGame ≤ .mk i} := by
  simp [supLeft]

theorem right_supLeft (x : IGame) :
    (supLeft x).right = ⋂ i ∈ xᴸ, {y | .mk i ⧏ y.toGame} := by
  simp [supLeft]

theorem supLeft_mem_of_short {x : IGame} [Short x] (hx : xᴸ.Nonempty) :
    ∃ y ∈ xᴸ, rightGame (.mk y) = supLeft x :=
  Set.Nonempty.ciSup_mem_image _ hx (Short.finite_moves _ x)

/-- The infimum of all left cuts of right options of `x`.

If `infRight x ≤ supLeft x` then `leftGame x = supLeft x` and `rightGame x = infRight x`; otherwise,
`x` is equivalent to the simplest surreal between `supLeft x` and `infRight x`. -/
def infRight (x : IGame) : Cut :=
  ⨅ i ∈ xᴿ, leftGame (.mk i)

theorem left_infRight (x : IGame) :
    (infRight x).left = ⋂ i ∈ xᴿ, {y | y.toGame ⧏ .mk i} := by
  simp [infRight]

theorem right_infRight (x : IGame) :
    (infRight x).right = ⋃ i ∈ xᴿ, {y | .mk i ≤ y.toGame} := by
  simp [infRight]

theorem infRight_mem_of_short {x : IGame} [Short x] (hx : xᴿ.Nonempty) :
    ∃ y ∈ xᴿ, leftGame (.mk y) = infRight x :=
  -- TODO: missing Mathlib lemma
  Set.Nonempty.ciSup_mem_image (α := Cutᵒᵈ) _ hx (Short.finite_moves _ x)

@[simp]
theorem infRight_neg (x : IGame) : infRight (-x) = -supLeft x := by
  refine eq_of_forall_le_iff fun y ↦ ?_
  simp [supLeft, infRight]

@[simp]
theorem supLeft_neg (x : IGame) : supLeft (-x) = -infRight x := by
  rw [← neg_neg (supLeft _), ← infRight_neg, neg_neg]

theorem leftGame_eq_supLeft_of_le {x : IGame} (h : infRight x ≤ supLeft x) :
    leftGame (.mk x) = supLeft x := by
  refine ext' (Set.ext fun y ↦ ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩)
  · rw [right_supLeft, mem_iInter₂]
    exact fun i hi ↦ mt hy.trans (mt Game.mk_le_mk.1 (left_lf hi))
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
      exact lf_of_right_le (hy.trans (Numeric.lt_right hz).le) hi

theorem rightGame_eq_infRight_of_le {x : IGame} : infRight x ≤ supLeft x →
    rightGame (.mk x) = infRight x := by
  simpa using @leftGame_eq_supLeft_of_le (-x)

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
  by_contra! hx
  simp [← leftGame_eq_supLeft_of_le hx, ← rightGame_eq_infRight_of_le hx,
    Game.mk_eq h, ← toGame_mk] at hx

theorem supLeft_lt_infRight_of_numeric (x : IGame) [x.Numeric] : supLeft x < infRight x :=
  supLeft_lt_infRight_of_equiv_numeric .rfl

/-! ### Numeric cuts -/

/-- We say that a cut is numeric when it's either a left or right cut from a surreal. -/
@[mk_iff numeric_def']
protected class inductive Numeric : Cut → Prop where
  | protected leftSurreal : ∀ y, Cut.Numeric (leftSurreal y)
  | protected rightSurreal : ∀ y, Cut.Numeric (rightSurreal y)

theorem numeric_def {x : Cut} : x.Numeric ↔ x ∈ Set.range leftSurreal ∪ Set.range rightSurreal := by
  rw [numeric_def']
  simp [eq_comm]

namespace Numeric

attribute [instance] Numeric.leftSurreal Numeric.rightSurreal

open Classical in
/-- A version of the recursor which eliminates into `Sort`. -/
@[elab_as_elim]
noncomputable def recOn' {motive : ∀ x : Cut, [x.Numeric] → Sort*} (x : Cut) [h : x.Numeric]
    (leftSurreal : ∀ y, motive (Cut.leftSurreal y))
    (rightSurreal : ∀ y, motive (Cut.rightSurreal y)) : motive x :=
  if hx : x ∈ Set.range Cut.leftSurreal
    then
      cast (by congr; exact Classical.choose_spec hx) (leftSurreal (choose hx))
    else
      haveI hx' : x ∈ Set.range Cut.rightSurreal := by simp_all [numeric_def]
      cast (by congr; exact Classical.choose_spec hx') (rightSurreal (choose hx'))

@[simp]
theorem recOn'_leftSurreal {motive : ∀ x : Cut, [x.Numeric] → Sort*} (y : Surreal)
    (leftSurreal : ∀ y, motive (Cut.leftSurreal y))
    (rightSurreal : ∀ y, motive (Cut.rightSurreal y)) :
    recOn' (motive := motive) (Cut.leftSurreal y) leftSurreal rightSurreal = leftSurreal y := by
  rw [recOn', dif_pos (by simp)]
  generalize_proofs _ H
  rw [cast_eq_iff_heq]
  congr
  exact leftSurreal_inj.1 <| Classical.choose_spec H

@[simp]
theorem recOn'_rightSurreal {motive : ∀ x : Cut, [x.Numeric] → Sort*} (y : Surreal)
    (leftSurreal : ∀ y, motive (Cut.leftSurreal y))
    (rightSurreal : ∀ y, motive (Cut.rightSurreal y)) :
    recOn' (motive := motive) (Cut.rightSurreal y) leftSurreal rightSurreal = rightSurreal y := by
  rw [recOn', dif_neg (by simp)]
  generalize_proofs _ H
  rw [cast_eq_iff_heq]
  congr
  exact rightSurreal_inj.1 <| Classical.choose_spec H

/-- Returns the surreal defining the cut. -/
noncomputable def toSurreal (x : Cut) [x.Numeric] : Surreal :=
  recOn' x (fun y ↦ y) (fun y ↦ y)

@[simp]
theorem toSurreal_leftSurreal (x : Surreal) : toSurreal (leftSurreal x) = x :=
  recOn'_leftSurreal ..

@[simp]
theorem toSurreal_rightSurreal (x : Surreal) : toSurreal (rightSurreal x) = x :=
  recOn'_rightSurreal ..

-- TODO: prove the stronger condition that `(leftGame x).toSurreal` and `(rightGame x).toSurreal`
-- are dyadic.
private theorem short_aux (x : IGame) [Short x] :
    (leftGame <| .mk x).Numeric ∧ (rightGame <| .mk x).Numeric := by
  obtain h | h := lt_or_ge (supLeft x) (infRight x)
  · rw [← simplestBtwn_supLeft_infRight h, leftGame_toGame, rightGame_toGame]
    exact ⟨Numeric.leftSurreal _, Numeric.rightSurreal _⟩
  · have h₁ := leftGame_ne_bot (.mk x)
    have h₂ := rightGame_ne_top (.mk x)
    rw [leftGame_eq_supLeft_of_le h, rightGame_eq_infRight_of_le h] at *
    constructor
    · obtain hx | hx := xᴸ.eq_empty_or_nonempty
      · rw [supLeft, hx] at h₁
        simp at h₁
      · obtain ⟨y, hy, hy'⟩ := supLeft_mem_of_short hx
        rw [← hy']
        short
        exact (short_aux y).2
    · obtain hx | hx := xᴿ.eq_empty_or_nonempty
      · rw [infRight, hx] at h₂
        simp at h₂
      · obtain ⟨y, hy, hy'⟩ := infRight_mem_of_short hx
        rw [← hy']
        short
        exact (short_aux y).1
termination_by x
decreasing_by igame_wf

protected instance leftGame (x : IGame) [Short x] : (leftGame <| .mk x).Numeric :=
  (short_aux x).1

protected instance rightGame (x : IGame) [Short x] : (rightGame <| .mk x).Numeric :=
  (short_aux x).2

protected theorem supLeft {x : IGame} [Short x] (hx : xᴸ.Nonempty) : (supLeft x).Numeric := by
  obtain ⟨y, hy, hy'⟩ := supLeft_mem_of_short hx
  rw [← hy']
  short
  infer_instance

protected theorem infRight {x : IGame} [Short x] (hx : xᴿ.Nonempty) : (infRight x).Numeric := by
  obtain ⟨y, hy, hy'⟩ := infRight_mem_of_short hx
  rw [← hy']
  short
  infer_instance

end Numeric
end Cut
end Surreal
