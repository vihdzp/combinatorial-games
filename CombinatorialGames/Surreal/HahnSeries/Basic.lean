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

open HahnSeries

-- #32648
section Subfield
open Cardinal

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

open Set

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
instance : IsStrictOrderedRing SurrealHahnSeries := by
  sorry

open Cardinal in
/-- A constructor for `SurrealHahnSeries` which hides various implementation details. -/
def mk (f : Surreal.{u} → ℝ) (small : Small.{u} (Function.support f))
    (wf : (Function.support f).WellFoundedOn (· > ·)) : SurrealHahnSeries where
  val := toLex ⟨f ∘ OrderDual.ofDual, IsWF.isPWO wf⟩
  property := by rwa [small_iff_lift_mk_lt_univ, lift_id, univ_umax.{u, u}] at small

/-- Returns the coefficient for `X ^ i`. -/
def coeff (x : SurrealHahnSeries) (i : Surreal) : ℝ :=
  x.1.coeff <| OrderDual.toDual i

@[simp, grind =] theorem coeff_mk (f small wf) : coeff (mk f small wf) = f := rfl
@[simp, grind =] theorem coeff_zero : coeff 0 = 0 := rfl

@[simp, grind =]
theorem coeff_neg (x : SurrealHahnSeries) : (-x).coeff = -x.coeff :=
  rfl

@[simp, grind =]
theorem coeff_add (x y : SurrealHahnSeries) : (x + y).coeff = x.coeff + y.coeff :=
  rfl

@[simp, grind =]
theorem coeff_sub (x y : SurrealHahnSeries) : (x - y).coeff = x.coeff - y.coeff :=
  rfl

@[ext]
theorem ext {x y : SurrealHahnSeries} (h : x.coeff = y.coeff) : x = y :=
  Subtype.ext <| HahnSeries.ext h

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

/-- The Hahn series with a single entry. -/
def single (x : Surreal) (r : ℝ) : SurrealHahnSeries :=
  mk (Pi.single x r) (small_subset Pi.support_single_subset)
    (WellFoundedOn.subset wellFoundedOn_singleton Pi.support_single_subset)

@[aesop simp]
theorem coeff_single (x : Surreal) (r : ℝ) : (single x r).coeff = Pi.single x r :=
  rfl

@[simp]
theorem single_zero (x : Surreal) : single x 0 = 0 := by
  aesop

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
theorem coeff_trunc_of_lt (x : SurrealHahnSeries) {i j : Surreal} (h : i < j) :
    (x.trunc i).coeff j = x.coeff j :=
  if_pos h

@[simp]
theorem coeff_trunc_of_le (x : SurrealHahnSeries) {i j : Surreal} (h : j ≤ i) :
    (x.trunc i).coeff j = 0 :=
  if_neg h.not_gt

@[simp]
theorem support_trunc (x : SurrealHahnSeries) (i : Surreal) :
    (x.trunc i).support = x.support ∩ Ioi i := by
  aesop

theorem trunc_add_single {x : SurrealHahnSeries} {i : Surreal} (hi : IsLeast x.support i) :
    x.trunc i + single i (x.coeff i) = x := by
  ext j
  have := @hi.2 j
  aesop (add simp [le_iff_lt_or_eq'])

theorem single_add_trunc {x : SurrealHahnSeries} {i : Surreal} (hi : IsLeast x.support i) :
    single i (x.coeff i) + x.trunc i = x := by
  rw [add_comm, trunc_add_single hi]

/-! ### Indexing the support by ordinals -/

open Ordinal

local instance (x : SurrealHahnSeries) : IsWellOrder (Shrink.{u} x.support) (· > ·) :=
  (orderIsoShrink x.support).dual.symm.toRelIsoLT.toRelEmbedding.isWellOrder

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

theorem length_lt_length_of_subset_of_exists {x y : SurrealHahnSeries} (h : x.support ⊆ y.support)
    (H : ∃ a ∈ y.support, ∀ b ∈ x.support, a < b) : x.length < y.length := by
  choose a ha using H
  rw [← lift_lt, ← type_support, ← type_support]
  let f := Subrel.inclusionEmbedding (· > ·) h
  apply (f.collapse.toPrincipalSeg ?_).ordinal_type_lt
  apply InitialSeg.not_surjective_of_exists_gt f
  aesop

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

theorem length_add_single {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (h : ∀ j ∈ x.support, i < j) (hr : r ≠ 0) : (x + single i r).length = x.length + 1 := by
  rw [← lift_inj, ← type_support, lift_add, lift_one, ← type_lt_Iio,
    ← type_eq_one_of_unique (α := PUnit) (· < ·), ← type_sum_lex]
  apply RelIso.ordinal_type_eq
  sorry

theorem length_single_add {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (h : ∀ j ∈ x.support, i < j) (hr : r ≠ 0) : (single i r + x).length = x.length + 1 := by
  rw [add_comm, length_add_single h hr]

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
theorem coeffIdx_exp (x : SurrealHahnSeries) (i) : x.coeff (x.exp i) = x.coeffIdx i :=
  (coeffIdx_of_lt _).symm

@[simp]
theorem coeffIdx_exp_symm (x : SurrealHahnSeries) (i) : x.coeffIdx (x.exp.symm i) = x.coeff i := by
  rw [coeffIdx_of_lt] <;> simp

@[simp]
theorem coeffIdx_eq_zero_iff {x : SurrealHahnSeries} {i : Ordinal} :
    x.coeffIdx i = 0 ↔ x.length ≤ i where
  mp h := by
    contrapose! h
    rw [coeffIdx_of_lt h]
    exact (x.exp _).2
  mpr := coeffIdx_of_le

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

variable {o f}

theorem coeff_ofSeq_of_eq {i : Iio o} {x : Surreal} (h : (f i).1 = x) :
    coeff (ofSeq o f hf) x = (f i).2 := by
  rw [ofSeq, coeff_mk, dif_pos ⟨i, h⟩]
  congr
  generalize_proofs H
  apply hf.injective
  have := Classical.choose_spec H
  simp_all

theorem coeff_ofSeq_of_ne {x : Surreal} (h : x ∉ range (Prod.fst ∘ f)) :
    coeff (ofSeq o f hf) x = 0 := by
  grind [ofSeq]

theorem support_ofSeq_subset : (ofSeq o f hf).support ⊆ range (Prod.fst ∘ f) :=
  ofSeq_aux o f

theorem support_ofSeq (hf' : ∀ i, (f i).2 ≠ 0) : (ofSeq o f hf).support = range (Prod.fst ∘ f) := by
  refine (ofSeq_aux o f).antisymm fun _ ↦ ?_
  simp only [Function.mem_support, ne_eq, dite_eq_right_iff, forall_exists_index]
  grind

private def ofSeq_relIso : (· < · : Iio o → _ → _) ≃r (· > · : range (Prod.fst ∘ f) → _ → _) := by
  refine .ofSurjective ⟨⟨fun x ↦ ⟨(f x).1, ⟨x, rfl⟩⟩, fun a b h ↦ hf.injective ?_⟩, hf.lt_iff_gt⟩
    fun _ ↦ ?_ <;> aesop

theorem length_ofSeq_le : (ofSeq o f hf).length ≤ o := by
  have := (ofSeq_relIso hf).symm.toRelEmbedding.isWellOrder
  rw [← lift_le, ← type_support, ← type_lt_Iio, (ofSeq_relIso hf).ordinal_type_eq]
  apply RelEmbedding.ordinal_type_le
  exact Subrel.inclusionEmbedding (· > ·) (support_ofSeq_subset ..)

private def ofSeq_relIso' (hf' : ∀ i, (f i).2 ≠ 0) :
    (· < · : Iio o → _ → _) ≃r (· > · : (ofSeq o f hf).support → _ → _) := by
  refine (ofSeq_relIso hf).trans (RelIso.subrel (· > ·) fun _ ↦ ?_)
  rw [support_ofSeq hf hf']

theorem length_ofSeq (hf' : ∀ i, (f i).2 ≠ 0) : (ofSeq o f hf).length = o := by
  rw [← lift_inj, ← type_support, ← type_lt_Iio]
  exact (ofSeq_relIso' hf hf').ordinal_type_eq.symm

theorem exp_ofSeq (i : Iio (ofSeq o f hf).length) (hf' : ∀ i, (f i).2 ≠ 0) :
    exp _ i = (f ⟨i, by convert ← i.2; exact length_ofSeq hf hf'⟩).1 := by
  change _ = (((RelIso.subrel (· < ·) fun _ ↦ by rw [length_ofSeq hf hf']).trans <|
    ofSeq_relIso' hf hf') i).1
  congr
  subsingleton

theorem coeffIdx_ofSeq {i : Ordinal} (hf' : ∀ i, (f i).2 ≠ 0) (hi : i < o) :
    coeffIdx (ofSeq o f hf) i = (f ⟨i, hi⟩).2 := by
  rw [coeffIdx_of_lt, exp_ofSeq hf _ hf', coeff_ofSeq_of_eq]
  · rfl
  · rwa [length_ofSeq hf hf']

theorem ofSeq_coeffIdx (x : SurrealHahnSeries) :
    ofSeq x.length (fun i ↦ ⟨x.exp i, x.coeffIdx i⟩) (fun _ _ h ↦ exp_strictAnti h) = x := by
  ext y
  by_cases hy : y ∈ x.support
  · rw [coeff_ofSeq_of_eq (i := x.exp.symm ⟨y, hy⟩)] <;> simp
  · grind [coeff_ofSeq_of_ne]

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
    (ofSeq : ∀ o f hf, motive (ofSeq o f hf)) : motive x :=
  cast (congrArg _ (ofSeq_coeffIdx x)) (ofSeq ..)

theorem ofSeqRecOn_ofSeq {motive : SurrealHahnSeries → Sort*} {o f hf}
    (ofSeq' : ∀ o f hf, motive (ofSeq o f hf)) (hf' : ∀ i, (f i).2 ≠ 0) :
    ofSeqRecOn (ofSeq o f hf) ofSeq' = ofSeq' o f hf := by
  rw [ofSeqRecOn, cast_eq_iff_heq]
  congr!
  · exact length_ofSeq _ hf'
  · rw [exp_ofSeq _ _ hf']
    congr!
  · rw [coeffIdx_ofSeq _ hf']
    · congr!
    · grind

/-- Auxiliary construction for `lengthRecOn`. -/
private def lengthRecOnAux {motive : SurrealHahnSeries → Sort*}
    (o : Ordinal) (zero : motive 0)
    (succ : ∀ y i r, (∀ j ∈ y.support, i < j) → r ≠ 0 → motive y → motive (y + single i r))
    (limit : ∀ y, Order.IsSuccLimit y.length → (∀ z, length z < length y → motive z) → motive y) :
    ∀ x, x.length = o → motive x :=
  limitRecOn o
    (fun x hx ↦ cast (by simp_all) zero)
    (by
      intro a IH x hx
      refine cast (congrArg _ <| trunc_add_single ⟨Subtype.coe_prop _, fun j hj ↦ ?_⟩)
        (succ (x.trunc <| x.exp ⟨a, ?_⟩) _ _ ?_ ?_ (IH _ <| length_trunc_exp ..))
      · change _ ≤ ↑(⟨j, hj⟩ : x.support)
        rw [← symm_exp_le_symm_exp_iff, x.exp.symm_apply_apply, ← Subtype.coe_le_coe,
          ← Order.lt_succ_iff, ← hx]
        exact symm_exp_lt _
      all_goals aesop
    )
    (fun a ha IH x hx ↦ limit _ (hx ▸ ha) fun y hy ↦ IH _ (hx ▸ hy) _ rfl)

private theorem lengthRecOnAux_zero {motive : SurrealHahnSeries → Sort*}
    {o : Ordinal} (ho : o = 0) {zero : motive 0} {succ limit} :
    lengthRecOnAux o zero succ limit = fun x _ ↦ cast (by simp_all) zero := by
  subst ho; exact limitRecOn_zero ..

private theorem lengthRecOnAux_succ {motive : SurrealHahnSeries → Sort*}
    {o a : Ordinal} (ha : a = o + 1) {zero : motive 0} {succ limit} :
    lengthRecOnAux a zero succ limit = fun x _ ↦
      let i := x.exp ⟨o, by simp_all⟩
      cast (sorry) (succ (x.trunc i) i (x.coeff i) sorry sorry
        (lengthRecOnAux o zero succ limit (x.trunc i) sorry)) := by
  subst ha; exact limitRecOn_succ ..

private theorem lengthRecOnAux_limit {motive : SurrealHahnSeries → Sort*}
    {o : Ordinal} (ho : Order.IsSuccLimit o) (zero : motive 0) {succ limit} :
    lengthRecOnAux o zero succ limit = fun y hy ↦
      limit y (by simp_all) (fun z _ ↦ lengthRecOnAux _ zero succ limit z rfl) :=
  limitRecOn_limit _ _ _ _ ho

/-- Limit recursion on the length of a Hahn series. -/
def lengthRecOn {motive : SurrealHahnSeries → Sort*} (x : SurrealHahnSeries)
    (zero : motive 0)
    (succ : ∀ y i r, (∀ j ∈ y.support, i < j) → r ≠ 0 → motive y → motive (y + single i r))
    (limit : ∀ y, Order.IsSuccLimit y.length → (∀ z, length z < length y → motive z) → motive y) :
    motive x :=
  lengthRecOnAux _ zero succ limit _ rfl

@[simp]
theorem lengthRecOn_zero {motive : SurrealHahnSeries → Sort*} {zero : motive 0} {succ limit} :
    lengthRecOn 0 zero succ limit = zero := by
  rw [lengthRecOn, lengthRecOnAux_zero length_zero]
  rfl

theorem lengthRecOn_succ {motive : SurrealHahnSeries → Sort*} {zero : motive 0} {succ limit}
    {x : SurrealHahnSeries} {i : Surreal} {r : ℝ} (hi : ∀ j ∈ x.support, i < j) (hr : r ≠ 0) :
    lengthRecOn (x + single i r) zero succ limit =
      succ _ _ _ hi hr (lengthRecOn x zero succ limit) := by
  rw [lengthRecOn, lengthRecOnAux_succ (o := x.length)]
  · dsimp
    rw [cast_eq_iff_heq]
    congr!
    · sorry
    · sorry
    · sorry
    · sorry
  ·


theorem lengthRecOn_limit {motive : SurrealHahnSeries → Sort*}
    {x : SurrealHahnSeries} (hx : Order.IsSuccLimit x.length) {zero : motive 0} {succ limit} :
    lengthRecOn x zero succ limit = limit x hx (fun y _ ↦ lengthRecOn y zero succ limit) := by
  rw [lengthRecOn, lengthRecOnAux_limit hx]
  rfl

#exit
/-! ### Hahn series as games -/

/-- The game that corresponds to a given surreal Hahn series. -/
def toIGame (x : SurrealHahnSeries.{u}) : IGame.{u} :=
  !{range fun i : (j : Iio x.length) × {r // r < x.coeffIdx j} ↦
      toIGame (x.trunc (x.exp i.1) + single (x.exp i.1) i.2) |
    range fun i : (j : Iio x.length) × {r // x.coeffIdx j < r} ↦
      toIGame (x.trunc (x.exp i.1) + single (x.exp i.1) i.2)}
termination_by x.length
decreasing_by all_goals sorry


end SurrealHahnSeries
