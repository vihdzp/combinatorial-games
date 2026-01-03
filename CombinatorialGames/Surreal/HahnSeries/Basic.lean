/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Pow
import Mathlib.RingTheory.HahnSeries.Cardinal
import Mathlib.RingTheory.HahnSeries.Lex

/-!
# Surreal Hahn series

Hahn series are a generalization of power series and Puiseux series. A Hahn series `R⟦Γ⟧` is defined
as a function `Γ → R` whose support is well-founded. This condition is sufficient to define addition
and multiplication as with polynomials, so that under suitable conditions, `R⟦Γ⟧` has the structure
of an ordered field.

The aphorism goes that surreals are real Hahn series over themselves. However, there are a few
technicalities. Hahn series are conventionally defined so that the support has well-founded `<`,
whereas for surreals it's more natural to assume well-founded `>`. Moreover, the Hahn series that
correspond to surreals must have a `Small` support. Because of this, we often prefer to identify
these surreal Hahn series with ordinal-indexed sequences of surreal exponents and their
coefficients.

This file provides the translation layer between Hahn series as they're implemented in Mathlib, and
the Hahn series relevant to surreal numbers, by defining the type `SurrealHahnSeries` for the
latter.
-/

universe u

noncomputable section

/-! ### For Mathlib -/

attribute [aesop simp] Pi.single_apply

theorem Set.IsWF.to_subtype {α : Type*} [LT α] {s : Set α} (h : IsWF s) : WellFoundedLT s := ⟨h⟩

open Order Set

/-! ### Basic defs and instances -/

/-- The type of `u`-small Hahn series over `Surrealᵒᵈ`, endowed with the lexicographic ordering. We
will show that this type is isomorphic as an ordered field to the surreals themselves. -/
def SurrealHahnSeries : Type (u + 1) :=
  have : Fact (_ < _) := ⟨Cardinal.aleph0_lt_univ.{u, u}⟩
  show Subfield (Lex _) from HahnSeries.cardSuppLTSubfield Surrealᵒᵈ ℝ .univ

namespace SurrealHahnSeries

instance : Field SurrealHahnSeries := by
  unfold SurrealHahnSeries; infer_instance

instance : LinearOrder SurrealHahnSeries := by
  unfold SurrealHahnSeries; infer_instance

instance : IsStrictOrderedRing SurrealHahnSeries := by
  unfold SurrealHahnSeries; infer_instance

open Cardinal in
/-- A constructor for `SurrealHahnSeries` which hides various implementation details. -/
def mk (f : Surreal.{u} → ℝ) (small : Small.{u} (Function.support f))
    (wf : (Function.support f).WellFoundedOn (· > ·)) : SurrealHahnSeries where
  val := toLex ⟨f ∘ OrderDual.ofDual, IsWF.isPWO wf⟩
  property := by rwa [small_iff_lift_mk_lt_univ, lift_id, univ_umax.{u, u}] at small

/-! #### `coeff` -/

/-- Returns the coefficient for `X ^ i`. -/
def coeff (x : SurrealHahnSeries) (i : Surreal) : ℝ :=
  x.1.coeff <| OrderDual.toDual i

@[simp, grind =] theorem coeff_mk (f small wf) : coeff (mk f small wf) = f := rfl
@[simp, grind =] theorem coeff_zero : coeff 0 = 0 := rfl

@[simp, grind =]
theorem coeff_neg (x : SurrealHahnSeries) : (-x).coeff = -x.coeff := rfl

@[simp, grind =]
theorem coeff_add (x y : SurrealHahnSeries) : (x + y).coeff = x.coeff + y.coeff := rfl

@[simp, grind =]
theorem coeff_sub (x y : SurrealHahnSeries) : (x - y).coeff = x.coeff - y.coeff := rfl

theorem coeff_add_apply (x y : SurrealHahnSeries) (i : Surreal) :
    (x + y).coeff i = x.coeff i + y.coeff i := rfl

theorem coeff_sub_apply (x y : SurrealHahnSeries) (i : Surreal) :
    (x - y).coeff i = x.coeff i - y.coeff i := rfl

@[ext]
theorem ext {x y : SurrealHahnSeries} (h : x.coeff = y.coeff) : x = y :=
  Subtype.ext <| HahnSeries.ext h

/-! #### `support` -/

/-- The support of the Hahn series. -/
def support (x : SurrealHahnSeries) : Set Surreal :=
  Function.support x.coeff

@[simp] theorem support_coeff (x : SurrealHahnSeries) : Function.support x.coeff = x.support := rfl
@[simp] theorem support_mk (f small wf) : support (mk f small wf) = Function.support f := rfl

@[simp, grind =]
theorem mem_support_iff {x : SurrealHahnSeries} {i : Surreal} : i ∈ x.support ↔ x.coeff i ≠ 0 :=
  .rfl

@[simp]
theorem support_eq_empty {x : SurrealHahnSeries} : support x = ∅ ↔ x = 0 := by
  aesop (add simp [Set.eq_empty_iff_forall_notMem])

@[simp]
theorem support_zero : support 0 = ∅ :=
  support_eq_empty.2 rfl

theorem support_add_subset {x y : SurrealHahnSeries} : (x + y).support ⊆ x.support ∪ y.support :=
  Function.support_add ..

theorem wellFoundedOn_support (x : SurrealHahnSeries) : x.support.WellFoundedOn (· > ·) :=
  x.1.isWF_support

instance (x : SurrealHahnSeries) : WellFoundedGT x.support :=
  x.1.isWF_support.to_subtype

instance small_support (x : SurrealHahnSeries.{u}) : Small.{u} x.support := by
  rw [Cardinal.small_iff_lift_mk_lt_univ, Cardinal.lift_id]
  exact lt_of_lt_of_eq x.2 Cardinal.univ_umax.symm

@[simp]
theorem mk_coeff (x : SurrealHahnSeries) : mk x.coeff x.small_support x.wellFoundedOn_support = x :=
  rfl

theorem lt_def {x y : SurrealHahnSeries} : x < y ↔ toColex x.coeff < toColex y.coeff := .rfl
theorem le_def {x y : SurrealHahnSeries} : x ≤ y ↔ toColex x.coeff ≤ toColex y.coeff := .rfl

/-! #### `single` -/

/-- The Hahn series with a single entry. -/
def single (x : Surreal) (r : ℝ) : SurrealHahnSeries :=
  mk (Pi.single x r) (small_subset Pi.support_single_subset)
    (WellFoundedOn.subset wellFoundedOn_singleton Pi.support_single_subset)

@[aesop simp]
theorem coeff_single (x : Surreal) (r : ℝ) : (single x r).coeff = Pi.single x r := rfl

@[simp, grind =]
theorem coeff_single_self (x : Surreal) (r : ℝ) : (single x r).coeff x = r := by
  aesop

@[grind =]
theorem coeff_single_of_ne {x y : Surreal} (h : x ≠ y) (r : ℝ) : (single x r).coeff y = 0 := by
  aesop

@[simp]
theorem single_zero (x : Surreal) : single x 0 = 0 := by
  aesop

theorem support_single_subset {x : Surreal} {r : ℝ} : support (single x r) ⊆ {x} := by
  aesop

/-! #### `trunc` -/

/-- Zeroes out any terms of the Hahn series less than or equal to `i`. -/
def trunc (x : SurrealHahnSeries) (i : Surreal) : SurrealHahnSeries :=
  let g j := if i < j then x.coeff j else 0
  have hg : Function.support g ⊆ x.support := by simp [g]
  mk _ (small_subset hg) (WellFoundedOn.subset x.wellFoundedOn_support hg)

@[aesop simp]
theorem coeff_trunc (x : SurrealHahnSeries) (i : Surreal) :
    (x.trunc i).coeff = fun j ↦ if i < j then x.coeff j else 0 :=
  rfl

@[simp, grind =]
theorem support_trunc (x : SurrealHahnSeries) (i : Surreal) :
    (x.trunc i).support = x.support ∩ Ioi i := by
  aesop

theorem support_trunc_subset (x : SurrealHahnSeries) (i : Surreal) :
    (x.trunc i).support ⊆ x.support := by
  simp

theorem support_trunc_anti {x : SurrealHahnSeries} : Antitone fun i ↦ (trunc x i).support :=
  fun _ _ _ _ ↦ by aesop (add safe tactic (by order))

@[simp]
theorem coeff_trunc_of_lt {x : SurrealHahnSeries} {i j : Surreal} (h : i < j) :
    (x.trunc i).coeff j = x.coeff j :=
  if_pos h

@[simp]
theorem coeff_trunc_of_le {x : SurrealHahnSeries} {i j : Surreal} (h : j ≤ i) :
    (x.trunc i).coeff j = 0 :=
  if_neg h.not_gt

theorem coeff_trunc_eq_zero {x : SurrealHahnSeries} {i j : Surreal} (h : x.coeff i = 0) :
    (x.trunc j).coeff i = 0 := by
  aesop

theorem coeff_trunc_of_mem {x : SurrealHahnSeries} {i j : Surreal} (h : j ∈ (x.trunc i).support) :
    (x.trunc i).coeff j = x.coeff j := by
  aesop

@[simp]
theorem trunc_add (x y : SurrealHahnSeries) (i : Surreal) :
    (x + y).trunc i = x.trunc i + y.trunc i := by
  aesop

@[simp]
theorem trunc_sub (x y : SurrealHahnSeries) (i : Surreal) :
    (x - y).trunc i = x.trunc i - y.trunc i := by
  aesop

@[simp]
theorem trunc_single_of_le {i j : Surreal} {r : ℝ} (h : i ≤ j) :
    (single i r).trunc j = 0 := by
  aesop (add safe tactic (by order))

@[simp]
theorem trunc_single_of_lt {i j : Surreal} {r : ℝ} (h : j < i) :
    (single i r).trunc j = single i r := by
  aesop (add safe tactic (by order))

@[simp]
theorem trunc_trunc (x : SurrealHahnSeries) (i j : Surreal) :
    (x.trunc i).trunc j = x.trunc (max i j) := by
  ext k
  obtain hi | hi := lt_or_ge i k
  · obtain hj | hj := lt_or_ge j k
    · rw [coeff_trunc_of_lt hj, coeff_trunc_of_lt hi, coeff_trunc_of_lt (max_lt hi hj)]
    · rw [coeff_trunc_of_le hj, coeff_trunc_of_le (le_max_of_le_right hj)]
  · rw [coeff_trunc_eq_zero (coeff_trunc_of_le hi), coeff_trunc_of_le (le_max_of_le_left hi)]

theorem trunc_eq_self_iff {x : SurrealHahnSeries} {i : Surreal} :
    x.trunc i = x ↔ ∀ j ∈ x.support, i < j := by
  refine ⟨fun hx j hj ↦ ?_, fun _ ↦ ?_⟩
  · by_contra! hi
    apply_fun (coeff · j) at hx
    rw [coeff_trunc_of_le hi] at hx
    exact hj hx.symm
  · ext j
    by_cases j ∈ x.support <;> aesop

alias ⟨_, trunc_eq_self⟩ := trunc_eq_self_iff

theorem trunc_eq_trunc {x : SurrealHahnSeries} {i j : Surreal} (h : i ≤ j)
    (H : ∀ k, i < k → k ≤ j → x.coeff k = 0) : x.trunc i = x.trunc j := by
  ext k
  obtain hi | hi := le_or_gt k i
  · rw [coeff_trunc_of_le hi, coeff_trunc_of_le (hi.trans h)]
  · rw [coeff_trunc_of_lt hi]
    obtain hj | hj := lt_or_ge j k
    · rw [coeff_trunc_of_lt hj]
    · rw [coeff_trunc_of_le hj]
      exact H _ hi hj

theorem trunc_add_single {x : SurrealHahnSeries} {i : Surreal} (hi : IsLeast x.support i) :
    x.trunc i + single i (x.coeff i) = x := by
  ext j
  have := @hi.2 j
  aesop (add simp [le_iff_lt_or_eq'])

end SurrealHahnSeries
