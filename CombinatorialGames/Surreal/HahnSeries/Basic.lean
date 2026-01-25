/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Pow
import Mathlib.Order.Shrink
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

@[simp]
theorem equivShrink_le_equivShrink_iff {α : Type*} [Preorder α] [Small.{u} α] {x y : α} :
    equivShrink α x ≤ equivShrink α y ↔ x ≤ y :=
  (orderIsoShrink α).map_rel_iff

@[simp]
theorem equivShrink_lt_equivShrink_iff {α : Type*} [Preorder α] [Small.{u} α] {x y : α} :
    equivShrink α x < equivShrink α y ↔ x < y :=
  (orderIsoShrink α).toRelIsoLT.map_rel_iff

open Ordinal in
@[simp]
theorem Ordinal.type_lt_Iio (o : Ordinal.{u}) : typeLT (Set.Iio o) = lift.{u + 1} o := by
  convert ToType.mk.toRelIsoLT.ordinal_lift_type_eq
  · rw [lift_id'.{u, u+1}]
  · rw [type_toType]

-- This is like `RelIso.cast` with better def-eqs.
def RelIso.subrel {α : Type*} (r : α → α → Prop) {p q : α → Prop} (H : ∀ x, p x ↔ q x) :
    Subrel r p ≃r Subrel r q where
  map_rel_iff' := .rfl
  __ := Equiv.subtypeEquiv (Equiv.refl _) H

instance {α β : Type*} {r : α → α → Prop} {s} [IsWellOrder β s] : Subsingleton (r ≃r s) where
  allEq f g := by
    ext x
    change f.toInitialSeg x = g.toInitialSeg x
    congr 1
    subsingleton

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

theorem notMem_support_iff {x : SurrealHahnSeries} {i : Surreal} : i ∉ x.support ↔ x.coeff i = 0 :=
  mem_support_iff.not_left

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

instance (x : SurrealHahnSeries) :
    IsWellOrder x.support (Subrel (· > ·) (· ∈ x.support)) :=
  inferInstanceAs (IsWellOrder x.support (· > ·))

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

theorem trunc_add_single {x : SurrealHahnSeries} {i : Surreal} (hi : i ∈ lowerBounds x.support) :
    x.trunc i + single i (x.coeff i) = x := by
  ext j
  have := @hi j
  aesop (add simp [le_iff_lt_or_eq'])

/-! ### Indexing the support by ordinals -/

open Ordinal

local instance (x : SurrealHahnSeries.{u}) : IsWellOrder (Shrink.{u} x.support) (· > ·) :=
  (orderIsoShrink x.support).dual.symm.toRelIsoLT.toRelEmbedding.isWellOrder

/-! #### `length` -/

/-- The length of a surreal Hahn series is the order type of its support. -/
def length (x : SurrealHahnSeries.{u}) : Ordinal.{u} :=
  type (α := Shrink.{u} x.support) (· > ·)

@[simp]
theorem type_support (x : SurrealHahnSeries.{u}) :
    type (α := x.support) (· > ·) = lift.{u + 1} x.length :=
  ((orderIsoShrink x.support).dual.toRelIsoLT.trans
    (RelIso.preimage Equiv.ulift _).symm).ordinal_type_eq

@[simp]
theorem length_eq_zero {x : SurrealHahnSeries} : length x = 0 ↔ x = 0 := by
  rw [← lift_inj, ← type_support, lift_zero, type_eq_zero_iff_isEmpty]
  aesop

@[simp]
theorem length_zero : length 0 = 0 :=
  length_eq_zero.2 rfl

@[gcongr]
theorem length_mono {x y : SurrealHahnSeries} (h : x.support ⊆ y.support) :
    x.length ≤ y.length := by
  rw [← lift_le, ← type_support, ← type_support]
  exact (Subrel.inclusionEmbedding (· > ·) h).ordinal_type_le

/-! #### `exp` -/

/-- Returns the `i`-th largest exponent with a non-zero coefficient.

This is registered as a `RelIso` between `Iio x.length` and `x.support`, so that `x.exp.symm` can be
used to return the index of an element in the support. -/
def exp (x : SurrealHahnSeries) : (· < · : Iio x.length → _ → _) ≃r (· > · : x.support → _ → _) :=
  (enum _).trans (orderIsoShrink x.support).dual.toRelIsoLT.symm

@[simp]
theorem symm_exp_lt {x : SurrealHahnSeries} (i) : x.exp.symm i < x.length :=
  (x.exp.symm i).2

theorem exp_strictAnti {x : SurrealHahnSeries} : StrictAnti x.exp :=
  fun _ _ ↦ x.exp.map_rel_iff'.2

theorem exp_anti {x : SurrealHahnSeries} : Antitone x.exp :=
  x.exp_strictAnti.antitone

@[simp]
theorem exp_lt_exp_iff {x : SurrealHahnSeries} {i j : Iio x.length} :
    x.exp i < x.exp j ↔ j < i :=
  x.exp_strictAnti.lt_iff_gt

@[simp]
theorem exp_le_exp_iff {x : SurrealHahnSeries} {i j : Iio x.length} :
    x.exp i ≤ x.exp j ↔ j ≤ i :=
  x.exp_strictAnti.le_iff_ge

@[simp]
theorem symm_exp_lt_symm_exp_iff {x : SurrealHahnSeries} {i j : x.support} :
    x.exp.symm i < x.exp.symm j ↔ j < i := by
  simp [← exp_lt_exp_iff]

@[simp]
theorem symm_exp_le_symm_exp_iff {x : SurrealHahnSeries} {i j : x.support} :
    x.exp.symm i ≤ x.exp.symm j ↔ j ≤ i := by
  simp [← exp_le_exp_iff]

theorem eq_exp_of_mem_support {x : SurrealHahnSeries} {i : Surreal} (h : i ∈ x.support) :
    ∃ j, x.exp j = i := by
  use x.exp.symm ⟨i, h⟩
  simp

/-- This lemma is useful for rewriting. -/
theorem exp_congr {x y : SurrealHahnSeries} (h : x = y) (i : Iio x.length) :
    (x.exp i).1 = (y.exp ⟨i.1, h ▸ i.2⟩).1 := by
  congr!

@[simp]
theorem typein_support {x : SurrealHahnSeries.{u}} (i : x.support) :
    typein (· > ·) i = lift.{u + 1} (x.exp.symm i) := by
  unfold exp length
  rw [typein, RelEmbedding.ofMonotone_coe, ← lift_id'.{u, u + 1} (type _)]
  apply RelIso.ordinal_lift_type_eq
  use Equiv.subtypeEquiv (equivShrink _) (fun a ↦ (orderIsoShrink _).toRelIsoLT.map_rel_iff.symm)
  simp

/-! #### `coeffIdx` -/

/-- Returns the coefficient which corresponds to the `i`-th largest exponent, or `0` if no such
coefficient exists. -/
def coeffIdx (x : SurrealHahnSeries) (i : Ordinal) : ℝ :=
  if h : i < x.length then x.coeff (x.exp ⟨i, h⟩) else 0

theorem coeffIdx_of_lt {x : SurrealHahnSeries} {i : Ordinal} (h : i < x.length) :
    x.coeffIdx i = x.coeff (x.exp ⟨i, h⟩) := by
  rw [coeffIdx, dif_pos]

theorem coeffIdx_of_le {x : SurrealHahnSeries} {i : Ordinal} (h : x.length ≤ i) :
    x.coeffIdx i = 0 := by
  rw [coeffIdx, dif_neg h.not_gt]

@[simp]
theorem coeffIdx_zero : coeffIdx 0 = 0 := by
  ext j; simp [coeffIdx]

@[simp]
theorem coeff_exp (x : SurrealHahnSeries) (i) : x.coeff (x.exp i) = x.coeffIdx i :=
  (coeffIdx_of_lt _).symm

@[simp]
theorem coeffIdx_symm_exp (x : SurrealHahnSeries) (i) : x.coeffIdx (x.exp.symm i) = x.coeff i := by
  rw [coeffIdx_of_lt] <;> simp

@[simp]
theorem coeffIdx_eq_zero_iff {x : SurrealHahnSeries} {i : Ordinal} :
    x.coeffIdx i = 0 ↔ x.length ≤ i where
  mp h := by
    contrapose! h
    rw [coeffIdx_of_lt h]
    exact (x.exp _).2
  mpr := coeffIdx_of_le

/-! #### `truncIdx` -/

/-- Truncates the series at the `i`-th largest exponent, or returns it unchanged if no such
coefficient exists. -/
def truncIdx (x : SurrealHahnSeries) (i : Ordinal.{u}) : SurrealHahnSeries :=
  if h : i < x.length then x.trunc (x.exp ⟨i, h⟩) else x

@[aesop simp]
theorem support_truncIdx (x : SurrealHahnSeries) (i : Ordinal) :
    (truncIdx x i).support =
      if hi : i < x.length then x.support ∩ Ioi (x.exp ⟨i, hi⟩) else x.support := by
  unfold truncIdx
  aesop

theorem truncIdx_of_lt {x : SurrealHahnSeries} {i : Ordinal} (h : i < x.length) :
    x.truncIdx i = x.trunc (x.exp ⟨i, h⟩) := by
  rw [truncIdx, dif_pos]

theorem truncIdx_of_le {x : SurrealHahnSeries} {i : Ordinal} (h : x.length ≤ i) :
    x.truncIdx i = x := by
  rw [truncIdx, dif_neg h.not_gt]

@[simp]
theorem truncIdx_zero : truncIdx 0 = 0 := by
  ext j; simp [truncIdx]

@[simp, grind =]
theorem trunc_exp (x : SurrealHahnSeries) (i) : x.trunc (x.exp i) = x.truncIdx i :=
  (truncIdx_of_lt _).symm

@[simp]
theorem truncIdx_symm_exp (x : SurrealHahnSeries) (i) : x.truncIdx (x.exp.symm i) = x.trunc i := by
  rw [truncIdx_of_lt] <;> simp

theorem support_truncIdx_ssubset {x : SurrealHahnSeries} {i : Ordinal} (h : i < x.length) :
    support (truncIdx x i) ⊂ support x := by
  rw [truncIdx_of_lt h]
  refine ⟨support_trunc_subset .., ?_⟩
  rw [not_subset]
  use x.exp ⟨i, h⟩
  aesop

theorem support_truncIdx_subset (x : SurrealHahnSeries) (i : Ordinal) :
    support (truncIdx x i) ⊆ support x := by
  obtain h | h := lt_or_ge i x.length
  · exact (support_truncIdx_ssubset h).le
  · rw [truncIdx_of_le h]

@[simp, grind =]
theorem length_truncIdx (x : SurrealHahnSeries) (i : Ordinal) :
    (x.truncIdx i).length = min i x.length := by
  obtain hi | hi := lt_or_ge i x.length
  · rw [← lift_inj, ← type_support]
    trans type (Subrel (· > · : x.support → _) (· > x.exp ⟨i, hi⟩))
    · apply ((RelIso.subrel (q := fun y ↦ ∃ h : y ∈ x.support, ⟨y, h⟩ ∈ Ioi (x.exp ⟨i, hi⟩))
        (· > ·) _).trans _).ordinal_type_eq
      · rw [truncIdx_of_lt hi, support_trunc]
        aesop
      · use (Equiv.subtypeSubtypeEquivSubtypeExists ..).symm
        aesop
    · simpa using hi.le
  · rw [truncIdx_of_le hi, min_eq_right hi]

theorem length_trunc_lt {x : SurrealHahnSeries} {i : Surreal} (h : i ∈ x.support) :
    (x.trunc i).length < x.length := by
  obtain ⟨⟨i, hi⟩, rfl⟩ := eq_exp_of_mem_support h
  rwa [trunc_exp, length_truncIdx, min_eq_left hi.le]

theorem truncIdx_ne {x : SurrealHahnSeries} {i : Ordinal} (h : i < x.length) :
    x.truncIdx i ≠ x := by
  apply_fun length
  simpa

theorem coeff_truncIdx_of_mem {x : SurrealHahnSeries} {i : Ordinal} {j k : Surreal}
    (hjk : j ≤ k) (h : j ∈ (x.truncIdx i).support) : (x.truncIdx i).coeff k = x.coeff k := by
  obtain hi | hi := lt_or_ge i x.length
  · by_cases hk : k ∈ (x.truncIdx i).support
    · rw [truncIdx_of_lt hi, coeff_trunc_of_mem]
      rwa [trunc_exp]
    · rw [notMem_support_iff] at hk
      rw [hk, eq_comm]
      rwa [truncIdx_of_lt hi, coeff_trunc_of_lt] at hk
      apply hjk.trans_lt'
      aesop
  · rw [truncIdx_of_le hi]

theorem trunc_truncIdx_of_mem {x : SurrealHahnSeries} {i : Ordinal} {a b : Surreal}
    (hab : a ≤ b) (ha : a ∈ (x.truncIdx i).support) : (x.truncIdx i).trunc b = x.trunc b := by
  ext k
  obtain h | h := lt_or_ge b k
  · rw [coeff_trunc_of_lt h, coeff_trunc_of_lt h, coeff_truncIdx_of_mem (hab.trans h.le) ha]
  · rw [coeff_trunc_of_le h, coeff_trunc_of_le h]

/-! #### `term` -/

/-- Returns the `i`-th largest term of the sum, or `0` if it doesn't exist. -/
def term (x : SurrealHahnSeries) (i : Ordinal) : Surreal :=
  if hi : i < x.length then x.coeffIdx i * ω^ (x.exp ⟨i, hi⟩).1 else 0

theorem term_of_lt {x : SurrealHahnSeries} {i : Ordinal} (hi : i < x.length) :
    x.term i = x.coeffIdx i * ω^ (x.exp ⟨i, hi⟩).1 :=
  dif_pos hi

@[simp]
theorem term_eq_zero {x : SurrealHahnSeries} {i : Ordinal} : x.term i = 0 ↔ x.length ≤ i := by
  simp [term, ← not_le]

alias ⟨_, term_of_le⟩ := term_eq_zero

/-! ### Assemble Hahn series from sequences -/

/-- An auxiliary structure for a decreasing sequence of exponents and their bundled coefficients.
Use the coercion `TermSeq.toSurrealHahnSeries` to cast this into a `SurrealHahnSeries`. -/
structure TermSeq : Type (u + 1) where
  /-- The length of the sequence. -/
  protected length : Ordinal.{u}
  /-- The exponents in the sequence. -/
  protected exp : Iio length → Surreal.{u}
  /-- The coefficients in the sequence. -/
  protected coeff : Iio length → ℝ
  /-- The sequence of exponents must be strictly antitone. -/
  exp_strictAnti : StrictAnti exp
  /-- All of the coefficients must be non-zero. -/
  coeff_ne_zero (i) : coeff i ≠ 0

namespace TermSeq

attribute [simp, grind .] coeff_ne_zero

@[ext]
theorem ext {s t : TermSeq} (hl : s.length = t.length)
    (he : ∀ i (hs : i < s.length) (ht : i < t.length), s.exp ⟨i, hs⟩ = t.exp ⟨i, ht⟩)
    (hc : ∀ i (hs : i < s.length) (ht : i < t.length), s.coeff ⟨i, hs⟩ = t.coeff ⟨i, ht⟩) :
    s = t := by
  cases s
  cases t
  cases hl
  simp_rw [mk.injEq, heq_eq_eq, true_and]
  constructor <;> ext
  · exact he ..
  · exact hc ..

@[simp, grind =]
theorem exp_lt_exp_iff {s : TermSeq} {i j} : s.exp i < s.exp j ↔ j < i :=
  s.exp_strictAnti.lt_iff_gt

@[simp, grind =]
theorem exp_le_exp_iff {s : TermSeq} {i j} : s.exp i ≤ s.exp j ↔ j ≤ i :=
  s.exp_strictAnti.le_iff_ge

@[simp, grind =]
theorem exp_inj {s : TermSeq} {i j} : s.exp i = s.exp j ↔ i = j :=
  s.exp_strictAnti.injective.eq_iff

@[simps]
instance : Zero TermSeq where
  zero := .mk 0 0 0 (fun _ ↦ by simp) (by simp)

@[simp, grind =]
theorem length_eq_zero {s : TermSeq} : s.length = 0 ↔ s = 0 where
  mp h := by
    ext x _ hx
    · rw [h, zero_length]
    · simp at hx
    · simp at hx
  mpr := by simp +contextual

open Classical in
private theorem toSurrealHahnSeries_aux (o : Ordinal.{u}) (f : Iio o → Surreal.{u} × ℝ) :
    Function.support (fun i ↦ if h : ∃ o, (f o).1 = i then (f <| Classical.choose h).2 else 0) ⊆
      range (Prod.fst ∘ f) := by
  aesop

/-- Cast a sequence of terms into a `SurrealHahnSeries`. -/
@[coe]
def toSurrealHahnSeries (s : TermSeq) : SurrealHahnSeries :=
  have H := toSurrealHahnSeries_aux s.length fun i ↦ (s.exp i, s.coeff i)
  .mk _ (small_subset H) (.subset (by
    rw [wellFoundedOn_range]
    convert wellFounded_lt (α := Iio s.length)
    ext
    exact s.exp_strictAnti.lt_iff_gt
  ) H)

instance : Coe TermSeq SurrealHahnSeries where
  coe := toSurrealHahnSeries

/-- Build a `TermSeq` from a `SurrealHahnSeries`. -/
@[simps]
def ofSurrealHahnSeries (x : SurrealHahnSeries) : TermSeq where
  length := x.length
  exp := (↑) ∘ x.exp
  coeff i := x.coeffIdx i
  exp_strictAnti _ := by simp
  coeff_ne_zero := by simp

@[simp, grind =]
theorem coeff_coe {s : TermSeq} (i : Iio s.length) : coeff s (s.exp i) = s.coeff i := by
  rw [toSurrealHahnSeries, coeff_mk, dif_pos ⟨i, rfl⟩]
  generalize_proofs H
  rw [s.exp_strictAnti.injective <| Classical.choose_spec H]

theorem coeff_coe_of_notMem {s : TermSeq} {x : Surreal} (h : x ∉ range s.exp) : coeff s x = 0 := by
  grind [toSurrealHahnSeries]

@[simp, grind =]
theorem support_coe (s : TermSeq) : support s = range s.exp := by
  ext i
  by_cases hi : i ∈ range s.exp
  · obtain ⟨i, rfl⟩ := hi
    simp
  · grind [coeff_coe_of_notMem hi]

/-- Order isomorphism between `Iio x.length` and the range of `x.exp`. -/
private def relIso' (s : TermSeq) : (· < · : Iio s.length → _) ≃r (· > · : range s.exp → _) := by
  refine .ofSurjective ⟨⟨fun i ↦ ⟨s.exp i, ⟨i, rfl⟩⟩, fun a b h ↦ s.exp_strictAnti.injective ?_⟩,
    s.exp_lt_exp_iff⟩ fun _ ↦ ?_ <;> aesop

/-- Order isomorphism between `Iio s.length` and the support of `x`. -/
private def relIso (s : TermSeq) : (· < · : Iio s.length → _) ≃r (· > · : support s → _) :=
  (relIso' s).trans (RelIso.subrel (· > ·) (by simp))

@[simp, grind =]
theorem length_coe (s : TermSeq) : length s = s.length := by
  rw [← lift_inj, ← type_support, ← type_lt_Iio]
  exact (relIso s).ordinal_type_eq.symm

@[simp, grind =]
theorem exp_coe (s : TermSeq) (i) : exp s i = s.exp ⟨i, by simpa using i.2⟩ := by
  change _ = (((RelIso.subrel (· < ·) (by simp)).trans <| relIso s) i).1
  congr
  subsingleton

theorem coeffIdx_coe_of_lt {s : TermSeq} {i} (h : i < s.length) :
    coeffIdx s i = s.coeff ⟨i, h⟩ := by
  rw [coeffIdx_of_lt (by simpa), exp_coe, coeff_coe]

theorem coeffIdx_coe_of_le {s : TermSeq} {i} (h : s.length ≤ i) : coeffIdx s i = 0 :=
  coeffIdx_of_le (by simpa)

@[aesop simp]
theorem coeffIdx_coe (s : TermSeq) (i) :
    coeffIdx s i = if h : i < s.length then s.coeff ⟨i, h⟩ else 0 := by
  split_ifs with h
  · exact coeffIdx_coe_of_lt h
  · exact coeffIdx_coe_of_le (le_of_not_gt h)

theorem term_coe_of_lt {s : TermSeq} {i} (h : i < s.length) :
    term s i = s.coeff ⟨i, h⟩ * ω^ s.exp ⟨i, h⟩ := by
  rw [term_of_lt (by simpa), coeffIdx_coe_of_lt, exp_coe]

theorem term_coe_of_le {s : TermSeq} {i} (h : s.length ≤ i) : term s i = 0 :=
  term_of_le (by simpa)

@[aesop simp]
theorem term_coe (s : TermSeq) (i) :
    term s i = if h : i < s.length then s.coeff ⟨i, h⟩ * ω^ s.exp ⟨i, h⟩ else 0 := by
  split_ifs with h
  · exact term_coe_of_lt h
  · exact term_coe_of_le (le_of_not_gt h)

/-- `TermSeq` and `SurrealHahnSeries` are alternate representations for the same structure. -/
@[simps!]
def surrealHahnSeriesEquiv : TermSeq ≃ SurrealHahnSeries where
  toFun := toSurrealHahnSeries
  invFun := ofSurrealHahnSeries
  left_inv s := by
    ext x
    · simp
    · simp
    · simp_all [coeffIdx_coe_of_lt]
  right_inv x := by
    ext i
    by_cases h : i ∈ x.support
    · obtain ⟨i, hi, rfl⟩ := eq_exp_of_mem_support h
      apply (coeff_coe (s := ofSurrealHahnSeries x) i).trans
      simp
    · have hx : x.coeff i = 0 := by rwa [← notMem_support_iff]
      rw [coeff_coe_of_notMem, hx]
      simpa [ofSurrealHahnSeries]

@[simp]
theorem coe_ofSurrealHahnSeries (x : SurrealHahnSeries) : ofSurrealHahnSeries x = x :=
  surrealHahnSeriesEquiv.apply_symm_apply x

@[simp]
theorem ofSurrealHahnSeries_coe (x : TermSeq) : ofSurrealHahnSeries x = x :=
  surrealHahnSeriesEquiv.symm_apply_apply x

@[simp]
theorem coe_inj {x y : TermSeq} : (x : SurrealHahnSeries) = y ↔ x = y :=
  surrealHahnSeriesEquiv.apply_eq_iff_eq

@[simp]
theorem ofSurrealHahnSeries_inj {x y : SurrealHahnSeries} :
    ofSurrealHahnSeries x = ofSurrealHahnSeries y ↔ x = y :=
  surrealHahnSeriesEquiv.symm.apply_eq_iff_eq

end TermSeq
end SurrealHahnSeries
