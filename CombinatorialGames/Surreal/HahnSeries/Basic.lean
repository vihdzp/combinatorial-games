import CombinatorialGames.Surreal.Pow
import Mathlib.Algebra.Order.Ring.StandardPart
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Lex

/-!
# Surreals Hahn series

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

attribute [aesop simp] Pi.single_apply mem_lowerBounds
attribute [-simp] Ordinal.add_one_eq_succ
attribute [grind =] Subtype.mk_le_mk Subtype.mk_lt_mk Order.lt_add_one_iff
attribute [aesop unsafe forward] le_of_lt lt_of_le_of_ne not_lt_of_ge

-- #32648
section Subfield
open Cardinal HahnSeries

variable {Γ R : Type*} [LinearOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R]
  (κ : Cardinal) [Fact (ℵ₀ < κ)]

variable (Γ R) in
/-- The `κ`-bounded subfield of Hahn series with cardinal less than `c`. -/
@[simps!]
def cardLTSubfield [Fact (ℵ₀ < κ)] : Subfield R⟦Γ⟧ where
  carrier := {x | #x.support < κ}
  zero_mem' := sorry
  one_mem' := sorry
  neg_mem' := sorry
  add_mem' := sorry
  inv_mem' := sorry
  mul_mem' := sorry

@[simp]
theorem mem_cardLTSubfield {x : HahnSeries Γ R} : x ∈ cardLTSubfield Γ R κ ↔ #x.support < κ :=
  .rfl

end Subfield

theorem Set.IsWF.to_subtype {α : Type*} [LT α] {s : Set α} (h : IsWF s) : WellFoundedLT s := ⟨h⟩

noncomputable instance {α : Type*} [LinearOrder α] [Small.{u} α] : LinearOrder (Shrink.{u} α) :=
  .lift' _ (equivShrink _).symm.injective

/-- `equivShrink` as an `OrderIso`. -/
def orderIsoShrink (α : Type*) [LinearOrder α] [Small.{u} α] : α ≃o Shrink.{u} α where
  map_rel_iff' {x y} := by
    change (equivShrink _).symm _ ≤ (equivShrink _).symm _ ↔ _
    simp
  __ := equivShrink α

@[simp]
theorem orderIsoShrink_apply {α : Type*} [LinearOrder α] [Small.{u} α] (x : α) :
    orderIsoShrink α x = equivShrink α x := rfl

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

namespace InitialSeg

theorem apply_relEmbedding_le_apply_initialSeg {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder β s] (f : r ↪r s) (g : r ≼i s) (x : α) : ¬ s (f x) (g x) := by
  induction x using f.isWellOrder.wf.induction with | h x IH
  intro hs
  obtain ⟨y, hy, hr⟩ := g.exists_eq_iff_rel.1 hs
  exact (f.map_rel_iff.not.1 <| hy ▸ IH y hr) hr

theorem not_surjective_of_exists_gt {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder β s] (f : r ↪r s) (g : r ≼i s) (H : ∃ a, ∀ b, s (f b) a) :
    ¬ Function.Surjective g := by
  intro h
  obtain ⟨a, ha⟩ := H
  obtain ⟨a, rfl⟩ := h a
  exact apply_relEmbedding_le_apply_initialSeg f g a (ha a)

end InitialSeg

open Order Set

/-! ### Basic defs and instances -/

/-- The type of `u`-small Hahn series over `Surrealᵒᵈ`, endowed with the lexicographic ordering. We
will show that this type is isomorphic as an ordered field to the surreals themselves. -/
def SurrealHahnSeries : Type (u + 1) :=
  have : Fact (_ < _) := ⟨Cardinal.aleph0_lt_univ.{u, u}⟩
  show Subfield (Lex _) from cardLTSubfield Surrealᵒᵈ ℝ .univ

namespace SurrealHahnSeries

instance : Field SurrealHahnSeries := by
  unfold SurrealHahnSeries; infer_instance

instance : LinearOrder SurrealHahnSeries := by
  unfold SurrealHahnSeries; infer_instance

-- TODO: prove this!
-- instance : IsStrictOrderedRing SurrealHahnSeries := by
--  sorry

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
  aesop

@[simp]
theorem trunc_single_of_lt {i j : Surreal} {r : ℝ} (h : j < i) :
    (single i r).trunc j = single i r := by
  aesop

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

/-! ### Indexing the support by ordinals -/

open Ordinal

local instance (x : SurrealHahnSeries) : IsWellOrder (Shrink.{u} x.support) (· > ·) :=
  (orderIsoShrink x.support).dual.symm.toRelIsoLT.toRelEmbedding.isWellOrder

/-! #### `length` -/

/-- The length of a surreal Hahn series is the order type of its support.

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

theorem coeffIdx_of_le {x : SurrealHahnSeries} {i : Ordinal} (h : x.length ≤ i) :
    x.coeffIdx i = 0 := by
  rw [coeffIdx, dif_neg h.not_gt]

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

@[simp, grind =]
theorem trunc_exp (x : SurrealHahnSeries) (i) : x.trunc (x.exp i) = x.truncIdx i :=
  (truncIdx_of_lt _).symm

@[simp]
theorem truncIdx_symm_exp (x : SurrealHahnSeries) (i) : x.truncIdx (x.exp.symm i) = x.trunc i := by
  rw [truncIdx_of_lt] <;> simp

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

/-! #### `ofSeq` -/

section ofSeq
variable (o : Ordinal.{u}) (f : Iio o → Surreal.{u} × ℝ) (hf : StrictAnti (Prod.fst ∘ f))

open Classical in
private theorem ofSeq_aux :
    Function.support (fun i ↦ if h : ∃ o, (f o).1 = i then (f <| Classical.choose h).2 else 0) ⊆
      range (Prod.fst ∘ f) := by
  aesop

open Classical in
/-- Constructs a surreal Hahn series from a decreasing sequence of exponents and their
associated coefficients. -/
def ofSeq : SurrealHahnSeries := by
  apply mk _ (small_subset (ofSeq_aux o f)) (.subset _ (ofSeq_aux o f))
  rw [wellFoundedOn_range]
  convert wellFounded_lt (α := Iio o)
  ext
  exact hf.lt_iff_gt

variable {o f hf}

theorem coeff_ofSeq (i : Iio o) : coeff (ofSeq o f hf) (f i).1 = (f i).2 := by
  rw [ofSeq, coeff_mk, dif_pos ⟨i, rfl⟩]
  congr
  generalize_proofs H
  apply hf.injective
  have := Classical.choose_spec H
  simp_all

-- A variant of `coeff_ofSeq` that's useful for rewriting.
theorem coeff_ofSeq' {x : Surreal} (i : Ordinal) (hi : i < o) (h : (f ⟨i, hi⟩).1 = x) :
    (ofSeq o f hf).coeff x = (f ⟨i, hi⟩).2 := by
  rw [← h, coeff_ofSeq]

theorem coeff_ofSeq_of_ne {x : Surreal} (h : x ∉ range (Prod.fst ∘ f)) :
    coeff (ofSeq o f hf) x = 0 := by
  grind [ofSeq]

theorem coeff_ofSeq_zero (ho : o = 0) : ofSeq o f hf = 0 := by
  subst ho
  ext
  rw [coeff_ofSeq_of_ne, coeff_zero, Pi.zero_apply]
  simp

theorem support_ofSeq_subset : (ofSeq o f hf).support ⊆ range (Prod.fst ∘ f) :=
  ofSeq_aux o f

theorem support_ofSeq (hf' : ∀ i, (f i).2 ≠ 0) : (ofSeq o f hf).support = range (Prod.fst ∘ f) := by
  refine (ofSeq_aux o f).antisymm fun _ ↦ ?_
  simp only [Function.mem_support, ne_eq, dite_eq_right_iff, forall_exists_index]
  grind

variable (hf) in
/-- Embeds `Iio o` into the range of the first entries of `f`. -/
private def ofSeq_relIso : (· < · : Iio o → _ → _) ≃r (· > · : range (Prod.fst ∘ f) → _ → _) := by
  refine .ofSurjective ⟨⟨fun x ↦ ⟨(f x).1, ⟨x, rfl⟩⟩, fun a b h ↦ hf.injective ?_⟩, hf.lt_iff_gt⟩
    fun _ ↦ ?_ <;> aesop

theorem length_ofSeq_le : (ofSeq o f hf).length ≤ o := by
  have := (ofSeq_relIso hf).symm.toRelEmbedding.isWellOrder
  rw [← lift_le, ← type_support, ← type_lt_Iio, (ofSeq_relIso hf).ordinal_type_eq]
  apply RelEmbedding.ordinal_type_le
  exact Subrel.inclusionEmbedding (· > ·) (support_ofSeq_subset ..)

variable (hf) in
/-- Embeds `Iio o` into the support of `ofSeq o f hf`. -/
private def ofSeq_relIso' (hf' : ∀ i, (f i).2 ≠ 0) :
    (· < · : Iio o → _ → _) ≃r (· > · : (ofSeq o f hf).support → _ → _) := by
  refine (ofSeq_relIso hf).trans (RelIso.subrel (· > ·) fun _ ↦ ?_)
  rw [support_ofSeq hf']

theorem length_ofSeq (hf' : ∀ i, (f i).2 ≠ 0) : (ofSeq o f hf).length = o := by
  rw [← lift_inj, ← type_support, ← type_lt_Iio]
  exact (ofSeq_relIso' hf hf').ordinal_type_eq.symm

theorem exp_ofSeq (i : Iio (ofSeq o f hf).length) (hf' : ∀ i, (f i).2 ≠ 0) :
    exp _ i = (f ⟨i, by convert ← i.2; exact length_ofSeq hf'⟩).1 := by
  change _ = (((RelIso.subrel (· < ·) fun _ ↦ by rw [length_ofSeq hf']).trans <|
    ofSeq_relIso' hf hf') i).1
  congr
  subsingleton

theorem coeffIdx_ofSeq {i : Ordinal} (hf' : ∀ i, (f i).2 ≠ 0) (hi : i < o) :
    coeffIdx (ofSeq o f hf) i = (f ⟨i, hi⟩).2 := by
  rw [coeffIdx_of_lt, exp_ofSeq _ hf', coeff_ofSeq']
  · rfl
  · rwa [length_ofSeq hf']

theorem ofSeq_coeffIdx (x : SurrealHahnSeries) :
    ofSeq x.length (fun i ↦ ⟨x.exp i, x.coeffIdx i⟩) (fun _ _ h ↦ exp_strictAnti h) = x := by
  ext y
  by_cases hy : y ∈ x.support
  · rw [coeff_ofSeq' (x.exp.symm ⟨y, hy⟩)] <;>
      simp [coeffIdx_symm_exp]
  · grind [coeff_ofSeq_of_ne]

theorem ofSeq_add_single {i : Surreal} (r : ℝ) (h : ∀ j, i < (f j).1) :
    ofSeq o f hf + single i r = ofSeq (o + 1)
      (fun j ↦ if _ : j = o then ⟨i, r⟩ else f ⟨j, by grind⟩)
      fun j k h ↦ by grind [StrictAnti] := by
  ext j
  by_cases hj : j ∈ range (Prod.fst ∘ f)
  · obtain ⟨j, rfl⟩ := hj
    dsimp [coeff_trunc]
    rw [coeff_ofSeq, coeff_ofSeq' j (lt_add_one_iff.2 j.2.le)] <;> grind
  · rw [coeff_add_apply, coeff_ofSeq_of_ne hj, zero_add]
    obtain rfl | hi := eq_or_ne i j
    · rw [coeff_ofSeq' o] <;> grind
    · rw [coeff_single_of_ne hi, coeff_ofSeq_of_ne]
      grind

end ofSeq

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

/-- Build data for a Hahn series by building it for `ofSeq`. -/
def ofSeqRecOn {motive : SurrealHahnSeries → Sort*} (x : SurrealHahnSeries)
    (ofSeq : ∀ o f hf, (∀ i, (f i).2 ≠ 0) → motive (ofSeq o f hf)) : motive x :=
  cast (congrArg _ (ofSeq_coeffIdx x)) (ofSeq _ _ _ (by simp))

theorem ofSeqRecOn_ofSeq {motive : SurrealHahnSeries → Sort*} {o f hf}
    (ofSeq' : ∀ o f hf, (∀ i, (f i).2 ≠ 0) → motive (ofSeq o f hf)) (hf' : ∀ i, (f i).2 ≠ 0) :
    ofSeqRecOn (ofSeq o f hf) ofSeq' = ofSeq' o f hf hf' := by
  rw [ofSeqRecOn, cast_eq_iff_heq]
  congr!
  · exact length_ofSeq hf'
  · rw [exp_ofSeq _ hf']
    congr!
  · rw [coeffIdx_ofSeq hf']
    · congr!
    · grind

theorem length_add_single {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (h : ∀ j ∈ x.support, i < j) (hr : r ≠ 0) : (x + single i r).length = x.length + 1 := by
  induction x using ofSeqRecOn with | ofSeq o f hf hf'
  rw [support_ofSeq hf'] at h
  rw [ofSeq_add_single, length_ofSeq, length_ofSeq]
  · grind
  · -- Why does `grind` fail here?
    intro i
    split_ifs
    · exact hr
    · exact hf' _
  · grind

theorem length_add_single_le {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (h : ∀ j ∈ x.support, i < j) : (x + single i r).length ≤ x.length + 1 := by
  obtain rfl | hr := eq_or_ne r 0
  · simp
  · rw [length_add_single h hr]

theorem length_trunc_add_single {x : SurrealHahnSeries} (i : Iio x.length) {r : ℝ} (hr : r ≠ 0) :
    (x.truncIdx i + single (x.exp i) r).length = i + 1 := by
  rw [length_add_single _ hr, length_truncIdx]
  · aesop
  · rw [truncIdx_of_lt i.2, support_trunc]
    aesop

theorem length_trunc_add_single_le {x : SurrealHahnSeries} (i : Iio x.length) (r : ℝ) :
    (x.truncIdx i + single (x.exp i) r).length ≤ i + 1 := by
  obtain rfl | hr := eq_or_ne r 0
  · simp
  · rw [length_trunc_add_single _ hr]

private theorem isLeast_support_succ {x : SurrealHahnSeries} {o : Ordinal} (h : x.length = o + 1) :
    IsLeast x.support (x.exp ⟨o, by simp_all⟩) := by
  refine ⟨Subtype.coe_prop _, fun j hj ↦ ?_⟩
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
      induction x using ofSeqRecOn with | ofSeq x f hf hf'
      rw [ofSeq_add_single]
      · simp_rw [length_ofSeq hf']
        intro hx
        rw [exp_ofSeq, dif_pos rfl] 
        -- Why does `grind` fail here?
        intro j
        split_ifs
        · exact hr
        · exact hf' _
      · rw [support_ofSeq hf'] at hi
        grind
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

end SurrealHahnSeries
end
