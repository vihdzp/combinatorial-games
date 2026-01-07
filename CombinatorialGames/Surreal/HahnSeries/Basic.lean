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
attribute [-simp] Ordinal.add_one_eq_succ
attribute [grind =] Subtype.mk_le_mk Subtype.mk_lt_mk Order.lt_add_one_iff

theorem Set.IsWF.to_subtype {α : Type*} [LT α] {s : Set α} (h : IsWF s) : WellFoundedLT s := ⟨h⟩

@[simp]
theorem equivShrink_le_equivShrink_iff {α : Type*} [LinearOrder α] [Small.{u} α] {x y : α} :
    equivShrink α x ≤ equivShrink α y ↔ x ≤ y :=
  (orderIsoShrink α).map_rel_iff

@[simp]
theorem equivShrink_lt_equivShrink_iff {α : Type*} [LinearOrder α] [Small.{u} α] {x y : α} :
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
    IsWellOrder { y // y ∈ x.support } (Subrel (· > ·) (· ∈ x.support)) :=
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

local instance (x : SurrealHahnSeries) : IsWellOrder (Shrink.{u} x.support) (· > ·) :=
  (orderIsoShrink x.support).dual.symm.toRelIsoLT.toRelEmbedding.isWellOrder

/-! #### `length` -/

/-- The length of a surreal Hahn series is the order type of its support. Note that this is an
`Ordinal`, rather than a `NatOrdinal`.

Reasoning about `Ordinal.type` directly is often quite tedious. To prove things about `length`, it's
often easier to use `HahnSeries.ofSeqRecOn` and the `HahnSeries.ofSeq` API. -/
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
def exp (x : SurrealHahnSeries) : (· < · : Iio x.length → _) ≃r (· > · : x.support → _) :=
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
    ∃ j, x.exp j = i :=
  ⟨x.exp.symm ⟨i, h⟩, by simp⟩

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
def coeffIdx (x : SurrealHahnSeries) (i : Ordinal.{u}) : ℝ :=
  if h : i < x.length then x.coeff (x.exp ⟨i, h⟩) else 0

theorem coeffIdx_of_lt {x : SurrealHahnSeries} {i : Ordinal} (h : i < x.length) :
    x.coeffIdx i = x.coeff (x.exp ⟨i, h⟩) := by
  rw [coeffIdx, dif_pos]

@[simp]
theorem coeffIdx_eq_zero {x : SurrealHahnSeries} {i : Ordinal} :
    x.coeffIdx i = 0 ↔ x.length ≤ i where
  mp h := by
    contrapose! h
    rw [coeffIdx_of_lt h]
    exact (x.exp _).2
  mpr h := by rw [coeffIdx, dif_neg h.not_gt]

alias ⟨_, coeffIdx_of_le⟩ := coeffIdx_eq_zero

@[simp]
theorem coeffIdx_zero : coeffIdx 0 = 0 := by
  ext j; simp [coeffIdx]

@[simp]
theorem coeff_exp (x : SurrealHahnSeries) (i) : x.coeff (x.exp i) = x.coeffIdx i :=
  (coeffIdx_of_lt _).symm

@[simp]
theorem coeffIdx_symm_exp (x : SurrealHahnSeries) (i) : x.coeffIdx (x.exp.symm i) = x.coeff i := by
  rw [coeffIdx_of_lt] <;> simp

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
    trans type (Subrel (· > · : x.support → _ → _) (· > x.exp ⟨i, hi⟩))
    · apply ((RelIso.subrel (q := fun y ↦ ∃ h : y ∈ x.support, ⟨y, h⟩ ∈ Ioi (x.exp ⟨i, hi⟩))
        (· > ·) _).trans _).ordinal_type_eq
      · rw [truncIdx_of_lt hi, support_trunc]
        aesop
      · use (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm
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

@[simp]
theorem truncIdx_eq_self {x : SurrealHahnSeries} {i : Ordinal} :
    x.truncIdx i = x ↔ x.length ≤ i where
  mp h := by
    contrapose! h
    exact truncIdx_ne h
  mpr := truncIdx_of_le

theorem coeff_truncIdx_of_mem {x : SurrealHahnSeries} {i : Ordinal} {j k : Surreal}
    (hjk : j ≤ k) (h : j ∈ (x.truncIdx i).support) : (x.truncIdx i).coeff k = x.coeff k := by
  obtain hi | hi := lt_or_ge i x.length
  · by_cases hk : k ∈ (x.truncIdx i).support
    · rw [truncIdx_of_lt hi, coeff_trunc_of_mem]
      rwa [trunc_exp]
    · rw [mem_support_iff, not_ne_iff] at hk
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

@[simp]
theorem leadingTerm_term (x : SurrealHahnSeries) (i : Ordinal) :
    (x.term i).leadingTerm = x.term i := by
  rw [term]
  aesop

@[simp]
theorem leadingCoeff_term (x : SurrealHahnSeries) (i : Ordinal) :
    (x.term i).leadingCoeff = x.coeffIdx i := by
  rw [term]
  aesop (add simp [eq_comm 0])

theorem wlog_term (x : SurrealHahnSeries) {i : Ordinal} (hi : i < x.length) :
    (x.term i).wlog = x.exp ⟨i, hi⟩ := by
  rw [term]
  aesop

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
@[simps!]
def ofSurrealHahnSeries (x : SurrealHahnSeries) : TermSeq where
  length := x.length
  exp := (↑) ∘ x.exp
  coeff i := x.coeffIdx i
  exp_strictAnti _ := by simp
  coeff_ne_zero := by simp

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
  · apply he
  · apply hc

@[simp, grind =]
theorem exp_lt_exp_iff {s : TermSeq} {i j} : s.exp i < s.exp j ↔ j < i :=
  s.exp_strictAnti.lt_iff_gt

@[simp, grind =]
theorem exp_le_exp_iff {s : TermSeq} {i j} : s.exp i ≤ s.exp j ↔ j ≤ i :=
  s.exp_strictAnti.le_iff_ge

@[simp, grind =]
theorem exp_inj {s : TermSeq} {i j} : s.exp i = s.exp j ↔ i = j :=
  s.exp_strictAnti.injective.eq_iff

@[simp, grind =]
theorem coeff_exp {s : TermSeq} (i : Iio s.length) : coeff s (s.exp i) = s.coeff i := by
  rw [toSurrealHahnSeries, coeff_mk, dif_pos ⟨i, rfl⟩]
  generalize_proofs H
  rw [s.exp_strictAnti.injective <| Classical.choose_spec H]

theorem coeff_coe_of_notMem {s : TermSeq} {x : Surreal} (h : x ∉ range s.exp) : coeff s x = 0 := by
  grind [toSurrealHahnSeries]

@[simp, grind =]
theorem length_eq_zero {s : TermSeq} : s.length = 0 ↔ s.toSurrealHahnSeries = 0 where
  mp h := by
    ext
    apply coeff_coe_of_notMem
    simp [h]
  mpr h := by
    by_contra! hi
    rw [← pos_iff_ne_zero] at hi
    apply_fun (coeff · (s.exp ⟨0, hi⟩)) at h
    simp at h

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
  rw [coeffIdx_of_lt (by simpa), exp_coe, coeff_exp]

theorem coeffIdx_coe_of_le {s : TermSeq} {i} (h : s.length ≤ i) : coeffIdx s i = 0 :=
  coeffIdx_of_le (by simpa)

@[aesop simp]
theorem coeffIdx_coe (s : TermSeq) (i) :
    coeffIdx s i = if h : i < s.length then s.coeff ⟨i, h⟩ else 0 := by
  split_ifs with h
  · exact coeffIdx_coe_of_lt h
  · exact coeffIdx_coe_of_le (le_of_not_gt h)

/-- `TermSeq` and `SurrealHahnSeries` are alternate representations for the same structure. -/
@[simps!]
def surrealHahnSeriesEquiv : TermSeq ≃ SurrealHahnSeries where
  toFun := toSurrealHahnSeries
  invFun := ofSurrealHahnSeries
  left_inv s := by
    ext
    · simp
    · simp
    · simp_all [coeffIdx_coe_of_lt]
  right_inv x := by
    ext i
    by_cases h : i ∈ x.support
    · obtain ⟨i, hi, rfl⟩ := eq_exp_of_mem_support h
      apply (coeff_exp (s := ofSurrealHahnSeries x) i).trans
      simp
    · have hx : x.coeff i = 0 := by rwa [← not_ne_iff, ← mem_support_iff]
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

/-- A `TermSeq` with a single term. -/
@[simps (attr := grind =)]
def single (r : ℝ) (e : Surreal) (hr : r ≠ 0) : TermSeq where
  length := 1
  exp _ := e
  coeff _ := r
  exp_strictAnti _ := by simp
  coeff_ne_zero _ := hr

/-- Appends a single term at the end of a `TermSeq`.

TODO: generalize to an `append` function? -/
@[simps (attr := grind =) -isSimp]
def appendSingle (s : TermSeq) (r : ℝ) (e : Surreal) (hr : r ≠ 0) (he : ∀ i, e < s.exp i) :
    TermSeq where
  length := s.length + 1
  exp i := if h : i = s.length then e else s.exp ⟨i, by grind⟩
  coeff i := if h : i = s.length then r else s.coeff ⟨i, by grind⟩
  exp_strictAnti := by grind [StrictAnti]
  coeff_ne_zero := by grind

attribute [simp] appendSingle_length

theorem exp_eq_exp_appendSingle (s : TermSeq) (i r e hr he) :
    s.exp i = (s.appendSingle r e hr he).exp ⟨i.1, by grind⟩ := by
  grind

theorem coeff_eq_coeff_appendSingle (s : TermSeq) (i r e hr he) :
    s.coeff i = (s.appendSingle r e hr he).coeff ⟨i.1, by grind⟩ := by
  grind

@[simp, grind =]
theorem exp_appendSingle_same (s : TermSeq) (r e hr he) :
    (s.appendSingle r e hr he).exp ⟨s.length, by grind⟩ = e := by
  grind

@[simp, grind =]
theorem coeff_appendSingle_same (s : TermSeq) (r e hr he) :
    (s.appendSingle r e hr he).coeff ⟨s.length, by grind⟩ = r := by
  grind

@[simp]
theorem coe_appendSingle {s : TermSeq} {r : ℝ} {e : Surreal} (hr : r ≠ 0) (he : ∀ i, e < s.exp i) :
    appendSingle s r e hr he = s + SurrealHahnSeries.single e r := by
  ext j
  by_cases hj : j ∈ range s.exp
  · obtain ⟨j, rfl⟩ := hj
    dsimp [coeff_trunc]
    rw [coeff_exp, exp_eq_exp_appendSingle s j r e hr he, eq_comm]
    grind
  · rw [coeff_add_apply, coeff_coe_of_notMem hj, zero_add]
    obtain rfl | he := eq_or_ne e j
    · conv_lhs => right; rw [← exp_appendSingle_same s r e hr he]
      rw [coeff_exp]
      simp
    · rw [coeff_single_of_ne he, coeff_coe_of_notMem]
      grind

/-- Truncate a `TermSeq` at the i-th term. -/
@[simps (attr := grind =)]
def trunc (s : TermSeq) (i : Ordinal) : TermSeq where
  length := min i s.length
  exp i := s.exp ⟨i, by grind⟩
  coeff i := s.coeff ⟨i, by grind⟩
  exp_strictAnti _ := by grind
  coeff_ne_zero := by grind

@[simp]
theorem trunc_of_le {s : TermSeq} {i : Ordinal} (h : s.length ≤ i) : s.trunc i = s := by
  ext
  · simpa
  · rfl
  · rfl

@[simp]
theorem trunc_trunc (s : TermSeq) (i j : Ordinal) : (s.trunc i).trunc j = s.trunc (min i j) := by
  ext
  · dsimp
    ac_rfl
  · simp
  · simp

@[simp]
theorem coe_trunc (s : TermSeq) (i : Ordinal) : s.trunc i = truncIdx s i := by
  obtain hi | hi := lt_or_ge i s.length
  · rw [truncIdx_of_lt (by simpa), exp_coe]
    ext j
    by_cases hj : j ∈ range s.exp
    · obtain ⟨⟨j, hj⟩, _, rfl⟩ := hj
      obtain hj' | hj' := lt_or_ge j i
      · rw [coeff_trunc_of_lt, coeff_exp]
        · apply (s.trunc i).coeff_exp ⟨j, _⟩
          simpa [hj']
        · simpa
      · rw [coeff_trunc_of_le, coeff_coe_of_notMem]
        · grind
        · simpa
    · rw [coeff_trunc_eq_zero, coeff_coe_of_notMem]
      · grind
      · rwa [← support_coe, mem_support_iff, not_ne_iff] at hj
  · rw [trunc_of_le hi, truncIdx_of_le (by simpa)]

end TermSeq

/-! ### Recursion principles -/

/-- Recursion principle for `SurrealHahnSeries`. -/
@[elab_as_elim, cases_eliminator]
def recOn {motive : SurrealHahnSeries → Sort*} (x : SurrealHahnSeries)
    (mk : ∀ f small wf, motive (mk f small wf)) : motive x :=
  mk x.coeff x.small_support x.wellFoundedOn_support

@[simp]
theorem recOn_mk {motive : SurrealHahnSeries → Sort*} {f small wf}
    (mk' : ∀ f small wf, motive (mk f small wf)) : recOn (mk f small wf) mk' = mk' f small wf :=
  rfl

/-- Build data for a `SurrealHahnSeries` by building it for a `TermSeq`. -/
def termSeqRecOn {motive : SurrealHahnSeries → Sort*} (x : SurrealHahnSeries)
    (mk : ∀ s : TermSeq, motive s) : motive x :=
  cast (congrArg _ (by simp)) (mk (.ofSurrealHahnSeries x))

@[simp]
theorem termSeqRecOn_coe {motive : SurrealHahnSeries → Sort*} {mk} (s : TermSeq) :
    termSeqRecOn (motive := motive) s mk = mk s := by
  rw [termSeqRecOn, cast_eq_iff_heq]
  congr
  simp

theorem length_add_single {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (h : ∀ j ∈ x.support, i < j) (hr : r ≠ 0) : (x + single i r).length = x.length + 1 := by
  induction x using termSeqRecOn with | mk s
  rw [← TermSeq.coe_appendSingle hr fun _ ↦ h _ (by simp)]
  rw [TermSeq.length_coe]
  simp

theorem length_add_single_le {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (h : ∀ j ∈ x.support, i < j) : (x + single i r).length ≤ x.length + 1 := by
  obtain rfl | hr := eq_or_ne r 0
  · simp
  · rw [length_add_single h hr]

private theorem isLeast_support_succ {x : SurrealHahnSeries} {o : Ordinal} (h : x.length = o + 1) :
    (x.exp ⟨o, by simp_all⟩).1 ∈ lowerBounds x.support := by
  refine fun j hj ↦ ?_
  change _ ≤ ↑(⟨j, hj⟩ : x.support)
  rw [← symm_exp_le_symm_exp_iff, x.exp.symm_apply_apply, ← Subtype.coe_le_coe, ← lt_add_one_iff]
  exact h ▸ symm_exp_lt _

/-- Auxiliary construction for `lengthRecOn`. -/
private def lengthRecOnAux {motive : SurrealHahnSeries → Sort*} (o : Ordinal)
    (succ : ∀ y i r, (∀ j ∈ y.support, i < j) → r ≠ 0 → motive y → motive (y + single i r))
    (limit : ∀ y, IsSuccPrelimit y.length → (∀ z, length z < length y → motive z) → motive y) :
    ∀ x, x.length = o → motive x :=
  SuccOrder.prelimitRecOn o
    (by
      refine fun a _ IH x hx ↦ cast (congrArg _ <| trunc_add_single (isLeast_support_succ hx))
        (succ (x.trunc <| x.exp ⟨a, ?_⟩) _ _ ?_ ?_ (IH _ ?_))
      all_goals aesop
    )
    (fun a ha IH x hx ↦ limit _ (hx ▸ ha) fun y hy ↦ IH _ (hx ▸ hy) _ rfl)

private theorem lengthRecOnAux_succ {motive : SurrealHahnSeries → Sort*}
    {o a : Ordinal} (ha : a = o + 1) {succ limit} :
    lengthRecOnAux (motive := motive) a succ limit = fun x _ ↦
      cast (congrArg _ <| trunc_add_single (isLeast_support_succ <| by simp_all))
        (succ (x.trunc <| x.exp ⟨o, _⟩) _ _ (by grind) (by simp_all)
          (lengthRecOnAux o succ limit _ (by grind))) := by
  subst ha; exact SuccOrder.prelimitRecOn_succ ..

private theorem lengthRecOnAux_limit {motive : SurrealHahnSeries → Sort*}
    {o : Ordinal} (ho : IsSuccPrelimit o) {succ limit} :
    lengthRecOnAux (motive := motive) o succ limit = fun y hy ↦
      limit y (by simp_all) fun z _ ↦ lengthRecOnAux _ succ limit z rfl :=
  SuccOrder.prelimitRecOn_of_isSuccPrelimit _ _ ho

/-- Recursion on the length of a Hahn series, separating out the case where it's a
succesor ordinal. -/
def lengthRecOn {motive : SurrealHahnSeries → Sort*} (x : SurrealHahnSeries)
    (succ : ∀ y i r, (∀ j ∈ y.support, i < j) → r ≠ 0 → motive y → motive (y + single i r))
    (limit : ∀ y, IsSuccPrelimit y.length → (∀ z, length z < length y → motive z) → motive y) :
    motive x :=
  lengthRecOnAux _ succ limit _ rfl

theorem lengthRecOn_succ {motive : SurrealHahnSeries → Sort*} {succ limit}
    {x : SurrealHahnSeries} {i : Surreal} {r : ℝ} (hi : ∀ j ∈ x.support, i < j) (hr : r ≠ 0) :
    lengthRecOn (motive := motive) (x + single i r) succ limit =
      succ _ _ _ hi hr (lengthRecOn x succ limit) := by
  rw [lengthRecOn, lengthRecOnAux_succ (o := x.length), cast_eq_iff_heq, lengthRecOn]
  · have H : ∀ {hx}, ↑((x + single i r).exp ⟨x.length, hx⟩) = i := by
      induction x using termSeqRecOn with | mk s
      rw [← TermSeq.coe_appendSingle hr fun _ ↦ hi _ (by simp)]
      simp
    congr!
    · rw [H, trunc_add, trunc_single_of_le le_rfl, add_zero, trunc_eq_self hi]
    · exact H
    · rw [H]
      simpa using mt (hi i) (lt_irrefl i)
  · exact length_add_single hi hr

theorem lengthRecOn_limit {motive : SurrealHahnSeries → Sort*}
    {x : SurrealHahnSeries} (hx : IsSuccPrelimit x.length) {succ limit} :
    lengthRecOn (motive := motive) x succ limit =
      limit x hx fun y _ ↦ lengthRecOn y succ limit := by
  rw [lengthRecOn, lengthRecOnAux_limit hx]
  rfl

/-! ### Extra lemmas -/

theorem length_truncIdx_add_single {x : SurrealHahnSeries} (i : Iio x.length) {r : ℝ} (hr : r ≠ 0) :
    (x.truncIdx i + single (x.exp i) r).length = i + 1 := by
  rw [length_add_single _ hr, length_truncIdx]
  · grind
  · rw [truncIdx_of_lt i.2, support_trunc]
    aesop

theorem length_truncIdx_add_single_le {x : SurrealHahnSeries} (i : Iio x.length) (r : ℝ) :
    (x.truncIdx i + single (x.exp i) r).length ≤ i + 1 := by
  obtain rfl | hr := eq_or_ne r 0
  · simp
  · rw [length_truncIdx_add_single _ hr]

@[simp]
theorem truncIdx_truncIdx (x : SurrealHahnSeries) (i j : Ordinal) :
    (x.truncIdx i).truncIdx j = x.truncIdx (min i j) := by
  induction x using termSeqRecOn with | mk s
  simp [← TermSeq.coe_trunc]

@[aesop simp]
theorem coeffIdx_truncIdx (x : SurrealHahnSeries) (i : Ordinal) :
    (x.truncIdx i).coeffIdx = fun j ↦ if j < i then x.coeffIdx j else 0 := by
  ext j
  induction x using termSeqRecOn with | mk s
  rw [← TermSeq.coe_trunc, TermSeq.coeffIdx_coe]
  aesop

theorem coeffIdx_truncIdx_of_lt {x : SurrealHahnSeries} {i j : Ordinal} (h : j < i) :
    (x.truncIdx i).coeffIdx j = x.coeffIdx j := by
  rw [coeffIdx_truncIdx]
  exact if_pos h

theorem coeffIdx_truncIdx_of_le {x : SurrealHahnSeries} {i j : Ordinal} (h : i ≤ j) :
    (x.truncIdx i).coeffIdx j = 0 := by
  rw [coeffIdx_truncIdx]
  exact if_neg h.not_gt

theorem support_truncIdx_strictMonoOn {x : SurrealHahnSeries} :
    StrictMonoOn (fun i ↦ (truncIdx x i).support) (Iio x.length) := by
  intro i hi j hj h
  dsimp
  rw [← min_eq_right h.le, ← truncIdx_truncIdx]
  apply support_truncIdx_ssubset
  simp_all

theorem support_truncIdx_mono {x : SurrealHahnSeries} :
    Monotone fun i ↦ (truncIdx x i).support := by
  intro i j h
  dsimp
  rw [← min_eq_right h, ← truncIdx_truncIdx]
  exact support_truncIdx_subset ..

@[simp]
theorem exp_truncIdx {x : SurrealHahnSeries} {i : Ordinal} (j : Iio (x.truncIdx i).length) :
    (x.truncIdx i).exp j = ⟨x.exp ⟨j, by aesop⟩, by aesop⟩ := by
  induction x using termSeqRecOn with | mk s
  apply Subtype.val_injective
  rw [exp_congr (TermSeq.coe_trunc s i).symm]
  simp

theorem term_truncIdx_of_lt {x : SurrealHahnSeries} {i j : Ordinal} (h : j < i) :
    (x.truncIdx i).term j = x.term j := by
  obtain h' | h' := le_or_gt x.length j
  · rw [truncIdx_of_le (h'.trans h.le)]
  · rw [term_of_lt, term_of_lt h', coeffIdx_truncIdx_of_lt h]
    · simp
    · simpa [h]

theorem term_truncIdx_of_le {x : SurrealHahnSeries} {i j : Ordinal} (h : i ≤ j) :
    (x.truncIdx i).term j = 0 := by
  rw [term_of_le]
  simp [h]

theorem term_injective : term.Injective := by
  intro x y h
  induction x using termSeqRecOn with | mk s
  induction y using termSeqRecOn with | mk t
  congr
  ext i
  · refine eq_of_forall_ge_iff fun _ ↦ ?_
    simp_rw [← TermSeq.length_coe, ← term_eq_zero, h]
  · have := congrFun h i
    convert congrArg Surreal.wlog this <;>
    · rw [wlog_term, TermSeq.exp_coe]
      simpa
  · have := congrFun h i
    convert congrArg Surreal.leadingCoeff this <;>
    · rw [leadingCoeff_term, TermSeq.coeffIdx_coe_of_lt]

@[simp]
theorem term_inj {x y : SurrealHahnSeries} : x.term = y.term ↔ x = y :=
  term_injective.eq_iff

end SurrealHahnSeries
end
