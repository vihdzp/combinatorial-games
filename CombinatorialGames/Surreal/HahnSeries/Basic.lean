import CombinatorialGames.Surreal.Pow
import CombinatorialGames.Mathlib.StandardPart
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Lex

/-!
# Surreals as Hahn series

We show that the surreal numbers are isomorphic as an ordered field to
`cardLTSubfield Surrealᵒᵈ ℝ univ`, which is to say, the subfield of real Hahn series over the order
dual of surreals, whose support is a small set.
-/

universe u

noncomputable section

/-! ### For Mathlib -/

attribute [aesop simp] Pi.single_apply mem_lowerBounds
attribute [-simp] Ordinal.add_one_eq_succ
attribute [grind =] Subtype.mk_le_mk Subtype.mk_lt_mk Order.lt_add_one_iff
attribute [aesop unsafe forward] le_of_lt lt_of_le_of_ne not_lt_of_ge

-- #32670
namespace HahnSeries

@[inherit_doc HahnSeries]
scoped syntax:max (priority := high) term noWs "⟦" term "⟧" : term

macro_rules | `($R⟦$M⟧) => `(HahnSeries $M $R)

/-- Unexpander for `HahnSeries`. -/
@[scoped app_unexpander HahnSeries]
meta def unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $M $R) => `($R[$M])
  | _ => throw ()

end HahnSeries

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

@[simp]
theorem support_trunc (x : SurrealHahnSeries) (i : Surreal) :
    (x.trunc i).support = x.support ∩ Ioi i := by
  aesop

@[simp]
theorem coeff_trunc_of_lt (x : SurrealHahnSeries) {i j : Surreal} (h : i < j) :
    (x.trunc i).coeff j = x.coeff j :=
  if_pos h

@[simp]
theorem coeff_trunc_of_le (x : SurrealHahnSeries) {i j : Surreal} (h : j ≤ i) :
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

theorem trunc_eq {x : SurrealHahnSeries} {i : Surreal} (h : ∀ j ∈ x.support, i < j) :
    x.trunc i = x := by
  ext j
  by_cases j ∈ x.support <;> aesop

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

@[simp]
theorem length_trunc_exp (x : SurrealHahnSeries) (i : Iio x.length) :
    (x.trunc (x.exp i)).length = i := by
  rw [← lift_inj, ← type_support]
  trans type (Subrel (· > · : x.support → _ → _) (· > x.exp i))
  · apply ((RelIso.subrel (q := fun y ↦ ∃ h : y ∈ x.support, ⟨y, h⟩ ∈ Ioi (x.exp i))
      (· > ·) (by aesop)).trans _).ordinal_type_eq
    use (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm
    aesop
  · simp

theorem length_trunc_lt {x : SurrealHahnSeries} {i : Surreal} (h : i ∈ x.support) :
    (x.trunc i).length < x.length := by
  obtain ⟨i, rfl⟩ := eq_exp_of_mem_support h
  rw [length_trunc_exp]
  exact i.2

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
    (x.trunc (x.exp i) + single (x.exp i) r).length = i + 1 := by
  rw [length_add_single, length_trunc_exp] <;> aesop

theorem length_trunc_add_single_le {x : SurrealHahnSeries} (i : Iio x.length) (r : ℝ) :
    (x.trunc (x.exp i) + single (x.exp i) r).length ≤ i + 1 := by
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
        (succ (x.trunc <| x.exp ⟨a, ?_⟩) _ _ ?_ ?_ (IH _ <| length_trunc_exp ..))
      all_goals aesop
    )
    (fun a ha IH x hx ↦ limit _ (hx ▸ ha) fun y hy ↦ IH _ (hx ▸ hy) _ rfl)

private theorem lengthRecOnAux_succ {motive : SurrealHahnSeries → Sort*}
    {o a : Ordinal} (ha : a = o + 1) {succ limit} :
    lengthRecOnAux (motive := motive) a succ limit = fun x _ ↦
      cast (congrArg _ <| trunc_add_single (isLeast_support_succ <| by simp_all))
        (succ (x.trunc <| x.exp ⟨o, by simp_all⟩) _ _ (by simp) (by simp_all)
          (lengthRecOnAux o succ limit _ (by simp))) := by
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
    · rw [H, trunc_add, trunc_single_of_le le_rfl, add_zero, trunc_eq hi]
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

/-! ### Hahn series as games -/

open IGame

/-- A common base for both `truncLT` and `truncGT`. -/
private def truncAux (x : SurrealHahnSeries) (R : ℝ → ℝ → Prop) : Set SurrealHahnSeries :=
  range fun i : (j : x.support) × {r // R r (x.coeff j)} ↦ x.trunc i.1 + single i.1 i.2

/-- We write `x ≺ y` whenever `x = y.trunc i + single i r` for some `i ∈ y.support` and
`r < y.coeff i`.

When `y.length` is a limit ordinal, the series with `x ≺ y` describe the left options of
`toIGame y`. -/
def truncLT (x : SurrealHahnSeries) : Set SurrealHahnSeries :=
  truncAux x (· < ·)

notation:50 x:50 " ≺ " y:50 => x ∈ truncLT y
recommended_spelling "truncLT" for "≺" in [«term_≺_»]

/-- We write `x ≻ y` whenever `x = y.trunc i + single i r` for some `i ∈ y.support` and
`r > y.coeff i`.

When `y.length` is a limit ordinal, the series with `x ≻ y` describe the right options of
`toIGame y`. -/
def truncGT (x : SurrealHahnSeries) : Set SurrealHahnSeries :=
  truncAux x (· > ·)

local notation:50 x:50 " ≻ " y:50 => x ∈ truncGT y
recommended_spelling "truncGT" for "≻" in [«term_≺_»]

private theorem truncAux_def {x y : SurrealHahnSeries} {R : ℝ → ℝ → Prop} :
    x ∈ truncAux y R ↔ ∃ i ∈ y.support, ∃ r : ℝ, R r (y.coeff i) ∧ y.trunc i + single i r = x := by
  simp [truncAux]

theorem truncLT_def {x y : SurrealHahnSeries} :
    x ≺ y ↔ ∃ i ∈ y.support, ∃ r : ℝ, r < y.coeff i ∧ y.trunc i + single i r = x :=
  truncAux_def

theorem truncGT_def {x y : SurrealHahnSeries} :
    x ≻ y ↔ ∃ i ∈ y.support, ∃ r : ℝ, y.coeff i < r ∧ y.trunc i + single i r = x :=
  truncAux_def

private theorem truncAux_zero (R : ℝ → ℝ → Prop) : truncAux 0 R = ∅ := by
  unfold truncAux; simp

@[simp] theorem truncLT_zero : truncLT 0 = ∅ := truncAux_zero _
@[simp] theorem truncGT_zero : truncGT 0 = ∅ := truncAux_zero _

private theorem trunc_add_single_truncAux {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    {R : ℝ → ℝ → Prop} (hi : i ∈ x.support) (hr : R r (x.coeff i)) :
    x.trunc i + single i r ∈ truncAux x R := by
  unfold truncAux
  aesop

theorem trunc_add_single_truncLT {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (hi : i ∈ x.support) (hr : r < x.coeff i) : x.trunc i + single i r ≺ x :=
  trunc_add_single_truncAux hi hr

theorem trunc_add_single_truncGT {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (hi : i ∈ x.support) (hr : x.coeff i < r) : x.trunc i + single i r ≻ x :=
  trunc_add_single_truncAux hi hr

instance small_truncAux (x : SurrealHahnSeries.{u}) (R : ℝ → ℝ → Prop) : Small.{u} (truncAux x R) :=
  by unfold truncAux; infer_instance

instance small_truncLT (x : SurrealHahnSeries.{u}) : Small.{u} (truncLT x) :=
  small_truncAux ..

instance small_truncGT (x : SurrealHahnSeries.{u}) : Small.{u} (truncGT x) :=
  small_truncAux ..

private theorem length_le_of_truncAux {x y : SurrealHahnSeries} {R : ℝ → ℝ → Prop}
    (h : x ∈ truncAux y R) : x.length ≤ y.length := by
  obtain ⟨⟨i, hi⟩, rfl⟩ := h
  apply (length_add_single_le ..).trans
  · rw [add_one_le_iff]
    exact length_trunc_lt i.2
  · simp

private theorem length_lt_of_truncAux {x y : SurrealHahnSeries} (hy : IsSuccPrelimit y.length)
    {R : ℝ → ℝ → Prop} (h : x ∈ truncAux y R) : x.length < y.length := by
  obtain ⟨⟨i, hi⟩, rfl⟩ := h
  apply (length_add_single_le ..).trans_lt
  · exact hy.add_one_lt <| length_trunc_lt i.2
  · simp

theorem length_le_of_truncLT {x y : SurrealHahnSeries} (h : x ≺ y) : x.length ≤ y.length :=
  length_le_of_truncAux h

theorem length_le_of_truncGT {x y : SurrealHahnSeries} (h : x ≻ y) : x.length ≤ y.length :=
  length_le_of_truncAux h

theorem length_lt_of_truncLT {x y : SurrealHahnSeries} (hy : IsSuccPrelimit y.length) (h : x ≺ y) :
    x.length < y.length :=
  length_lt_of_truncAux hy h

theorem length_lt_of_truncGT {x y : SurrealHahnSeries} (hy : IsSuccPrelimit y.length) (h : x ≻ y) :
    x.length < y.length :=
  length_lt_of_truncAux hy h

theorem lt_of_truncLT {x y : SurrealHahnSeries} (h : x ≺ y) : x < y := by
  obtain ⟨⟨⟨i, hi⟩, s, hs⟩, rfl⟩ := h
  rw [lt_def]
  use i
  aesop

theorem gt_of_truncGT {x y : SurrealHahnSeries} (h : x ≻ y) : y < x := by
  obtain ⟨⟨⟨i, hi⟩, s, hs⟩, rfl⟩ := h
  rw [lt_def]
  use i
  aesop

/-- The game that corresponds to a given surreal Hahn series.

This is an arbitrary representative for `SurrealHahnSeries.toSurreal`, which we use in its place
while we prove that this game is numeric. -/
@[coe]
def toIGame (x : SurrealHahnSeries.{u}) : IGame.{u} :=
  lengthRecOn x (fun _ i r _ _ IH ↦ IH + r * ω^ i.out) fun y hy IH ↦
    !{range fun i : truncLT y ↦ IH i <| length_lt_of_truncLT hy i.2 |
      range fun i : truncGT y ↦ IH i <| length_lt_of_truncGT hy i.2}

instance : Coe SurrealHahnSeries IGame where
  coe := toIGame

theorem toIGame_succ {x : SurrealHahnSeries}
    {i : Surreal} {r : ℝ} (hi : ∀ j ∈ x.support, i < j) (hr : r ≠ 0) :
    toIGame (x + single i r) = toIGame x + r * ω^ i.out :=
  lengthRecOn_succ hi hr

theorem toIGame_succ_equiv {x : SurrealHahnSeries}
    {i : Surreal} {r : ℝ} (hi : ∀ j ∈ x.support, i < j) :
    toIGame (x + single i r) ≈ toIGame x + r * ω^ i.out := by
  obtain rfl | hr := eq_or_ne r 0
  · rw [single_zero, add_zero, antisymmRel_comm, add_equiv_left_iff, ← Surreal.mk_eq_mk]
    simp
  · rw [toIGame_succ hi hr]

theorem toIGame_limit {x : SurrealHahnSeries.{u}} (hx : IsSuccPrelimit x.length) :
    toIGame x = !{toIGame '' truncLT x | toIGame '' truncGT x} := by
  simp_rw [image_eq_range]
  exact lengthRecOn_limit hx

@[simp]
theorem toIGame_zero : toIGame 0 = 0 := by
  rw [toIGame_limit] <;> aesop

theorem leftMoves_toIGame_limit {x : SurrealHahnSeries} (hx : IsSuccPrelimit x.length) :
    (toIGame x)ᴸ = toIGame '' truncLT x := by
  rw [toIGame_limit hx, leftMoves_ofSets]

theorem rightMoves_toIGame_limit {x : SurrealHahnSeries} (hx : IsSuccPrelimit x.length) :
    (toIGame x)ᴿ = toIGame '' truncGT x := by
  rw [toIGame_limit hx, rightMoves_ofSets]

private theorem toIGame_lt_toIGame_of_truncLT' {x y : SurrealHahnSeries} (h : x ≺ y)
    [hy' : Numeric y] (IH : ∀ z : SurrealHahnSeries, z.length < y.length → Numeric z) :
    toIGame x < toIGame y := by
  induction y using lengthRecOn generalizing hy' x with
  | succ y i r hi hr IH' =>
    obtain ⟨⟨⟨j, hj⟩, s, hs⟩, rfl⟩ := h
    rw [coeff_add_apply] at hs
    replace hj := union_subset_union_right y.support support_single_subset (support_add_subset hj)
    have hij : i ≤ j := by rw [le_iff_lt_or_eq]; aesop
    dsimp
    rw [trunc_add, trunc_single_of_le hij, add_zero, toIGame_succ hi hr]
    grw [toIGame_succ_equiv (by simp)]
    obtain hj | rfl := hj
    · replace hij := hi _ hj
      rw [coeff_single_of_ne hij.ne, add_zero] at hs
      obtain ⟨t, ht, ht'⟩ := exists_between hs
      have hst : s * ω^ j.out ≈ t * ω^ j.out + ↑(s - t) * ω^ j.out := by
        rw [← Surreal.mk_eq_mk]
        simp [← add_mul]
      grw [hst, ← add_assoc]
      apply add_lt_add _ (Numeric.mul_wpow_lt_mul_wpow_of_neg ..)
      · grw [← toIGame_succ_equiv (by simp)]
        simp_rw [length_add_single hi hr, lt_add_one_iff] at IH
        have := IH _ le_rfl
        apply IH'
        · rw [truncLT_def]
          exact ⟨j, hj, t, ht', rfl⟩
        · exact fun z hz ↦ IH z hz.le
      · rwa [sub_neg]
      · rw [← Surreal.mk_lt_mk]
        simpa
    · rw [trunc_eq hi]
      have : y.coeff j = 0 := by
        by_contra h
        exact (hi _ h).false
      simpa [this] using hs
  | limit y hy IH' =>
    apply Numeric.left_lt
    rw [leftMoves_toIGame_limit hy]
    exact mem_image_of_mem _ h


private theorem toIGame_lt_toIGame_of_truncGT' {x y : SurrealHahnSeries} (h : x ≻ y)
    [hy' : Numeric y] (IH : ∀ z : SurrealHahnSeries, z.length < y.length → Numeric z) :
    toIGame y < toIGame x :=
  sorry

private theorem toIGame_aux {o : Ordinal} {x y : SurrealHahnSeries}
    (hx : x.length < o) (hy : y.length < o) : Numeric x ∧ Numeric y ∧
      x < y → toIGame x < toIGame y := by
  sorry

  #exit
proof_wanted strictMono_toIGame : StrictMono SurrealHahnSeries.toIGame
proof_wanted numeric_toIGame : ∀ x, Numeric (SurrealHahnSeries.toIGame x)

#exit

private theorem toIGame_lt_toIGame_aux {x y : SurrealHahnSeries} :
    Numeric x ∧ Numeric y ∧ x < y → toIGame x < toIGame y := by
  induction x using lengthRecOn generalizing y with
  | succ x i r hi hr IH =>
    rw [toIGame_succ hi hr]
    induction y using lengthRecOn with
    | succ y j s hj hs IH' =>
      rw [toIGame_succ hj hs]
    | limit y hy IH' => sorry
  | limit x hx IH => sorry


#exit
#exit
theorem strictMono_toIGame : StrictMono toIGame := by
  intro x y h
  rw [lt_def] at h
  obtain ⟨a, ha⟩ := h
  simp at ha


#exit
end SurrealHahnSeries

-- Split file here for import purposes?

namespace LinearOrderedAddCommGroupWithTop
variable {α : Type*} [LinearOrderedAddCommGroupWithTop α]

@[simp]
theorem sub_top (a : α) : a - ⊤ = ⊤ := by
  rw [sub_eq_add_neg, LinearOrderedAddCommGroupWithTop.neg_top, add_top]

@[simp]
theorem sub_self_eq_zero_iff_ne_top {a : α} : a - a = 0 ↔ a ≠ ⊤ where
  mp := by
    contrapose!
    simp +contextual
  mpr := by
    rw [sub_eq_add_neg]
    exact add_neg_cancel_of_ne_top

alias ⟨_, sub_self_eq_zero_of_ne_top⟩ := sub_self_eq_zero_iff_ne_top

end LinearOrderedAddCommGroupWithTop

namespace Surreal

@[simp]
theorem mk_div_wlog (x : Surreal) :
    ArchimedeanClass.mk (x / ω^ x.wlog) = ArchimedeanClass.mk x - ArchimedeanClass.mk x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · rw [div_eq_mul_inv, ← wpow_neg, ArchimedeanClass.mk_mul, ← wlog_inv,
      mk_wpow_wlog (inv_ne_zero hx), ArchimedeanClass.mk_inv, ← sub_eq_add_neg]

-- This leading coeff stuff should go in Pow

/-- The leading coefficient of a surreal's Hahn series. -/
def leadingCoeff (x : Surreal) : ℝ :=
  ArchimedeanClass.standardPart (x / ω^ x.wlog)

@[simp]
theorem leadingCoeff_realCast (r : ℝ) : leadingCoeff r = r := by
  rw [leadingCoeff, wlog_realCast, wpow_zero, div_one]
  exact ArchimedeanClass.standardPart_real Real.toSurrealRingHom r

@[simp]
theorem leadingCoeff_ratCast (q : ℚ) : leadingCoeff q = q :=
  mod_cast leadingCoeff_realCast q

@[simp]
theorem leadingCoeff_intCast (n : ℤ) : leadingCoeff n = n :=
  mod_cast leadingCoeff_realCast n

@[simp]
theorem leadingCoeff_natCast (n : ℕ) : leadingCoeff n = n :=
  mod_cast leadingCoeff_realCast n

@[simp]
theorem leadingCoeff_zero : leadingCoeff 0 = 0 :=
  mod_cast leadingCoeff_natCast 0

@[simp]
theorem leadingCoeff_one : leadingCoeff 1 = 1 :=
  mod_cast leadingCoeff_natCast 1

@[simp]
theorem leadingCoeff_neg (x : Surreal) : leadingCoeff (-x) = -leadingCoeff x := by
  simp [leadingCoeff, neg_div]

@[simp]
theorem leadingCoeff_mul (x y : Surreal) :
    leadingCoeff (x * y) = leadingCoeff x * leadingCoeff y := by
  unfold leadingCoeff
  by_cases hx : x = 0; simp [hx]
  by_cases hy : y = 0; simp [hy]
  rw [wlog_mul hx hy, wpow_add, ← ArchimedeanClass.standardPart_mul, mul_div_mul_comm]
  all_goals
    rw [mk_div_wlog, LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top]
    simpa

@[simp]
theorem leadingCoeff_inv (x : Surreal) : leadingCoeff x⁻¹ = (leadingCoeff x)⁻¹ := by
  obtain rfl | hx := eq_or_ne x 0; simp
  apply eq_inv_of_mul_eq_one_left
  rw [← leadingCoeff_mul, inv_mul_cancel₀ hx, leadingCoeff_one]

@[simp]
theorem leadingCoeff_eq_zero_iff {x : Surreal} : leadingCoeff x = 0 ↔ x = 0 where
  mp h := by
    contrapose h
    apply ArchimedeanClass.standardPart_ne_zero
    simpa
  mpr := by simp +contextual

/-- The ordinal-indexed sequence of "Hahn series residues" associated to a given surreal. -/
private def toHahnSeriesAux (x : Surreal) (i : Ordinal) : Surreal :=
  SuccOrder.prelimitRecOn i
    (fun j _ IH ↦ IH - leadingCoeff IH * ω^ IH.wlog)
    (fun j hj IH ↦ sorry) -- IH minus the Hahn series determined from all prev values

end Surreal
