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

open Ordinal in
@[simp]
theorem Ordinal.type_lt_Iio (o : Ordinal.{u}) : typeLT (Set.Iio o) = lift.{u + 1} o := by
  convert (enumIsoToType o).toRelIsoLT.ordinal_lift_type_eq
  · rw [lift_id'.{u, u+1}]
  · rw [type_toType]

-- This is like `RelIso.cast` with better def-eqs.
def RelIso.subrel {α : Type*} (r : α → α → Prop) (p q : α → Prop) (H : ∀ {x}, p x ↔ q x) :
    Subrel r p ≃r Subrel r q where
  toFun x := ⟨x, H.1 x.2⟩
  invFun x := ⟨x, H.2 x.2⟩
  map_rel_iff' := .rfl

instance {α β : Type*} {r : α → α → Prop} {s} [IsWellOrder β s] : Subsingleton (r ≃r s) where
  allEq f g := by
    ext x
    change f.toInitialSeg x = g.toInitialSeg x
    congr 1
    subsingleton

open Cardinal Set

/-! ### Basic functions and instances -/

/-- The type of `u`-small Hahn series over `Surrealᵒᵈ`, endowed with the lexicographic ordering. We
will show that this type is isomorphic as an ordered field to the surreals themselves. -/
def SurrealHahnSeries : Type (u + 1) :=
  have : Fact (_ < _) := ⟨aleph0_lt_univ.{u, u}⟩
  show Subfield (Lex _) from cardLTSubfield Surrealᵒᵈ ℝ univ

namespace SurrealHahnSeries

instance : Field SurrealHahnSeries := by
  unfold SurrealHahnSeries; infer_instance

instance : LinearOrder SurrealHahnSeries := by
  unfold SurrealHahnSeries; infer_instance

-- TODO: prove this!
instance : IsStrictOrderedRing SurrealHahnSeries := by
  sorry

/-- A constructor for `SurrealHahnSeries` which hides various implementation details. -/
def mk (f : Surreal.{u} → ℝ) (small : Small.{u} (Function.support f))
    (wf : (Function.support f).WellFoundedOn (· > ·)) : SurrealHahnSeries where
  val := toLex ⟨f ∘ OrderDual.ofDual, IsWF.isPWO wf⟩
  property := by rwa [small_iff_lift_mk_lt_univ, lift_id, univ_umax.{u, u}] at small

/-- Returns the coefficient for `X ^ i`. -/
def coeff (x : SurrealHahnSeries) (i : Surreal) : ℝ :=
  x.1.coeff <| OrderDual.toDual i

@[simp]
theorem coeff_mk (f small wf) : coeff (mk f small wf) = f :=
  rfl

@[ext]
theorem ext {x y : SurrealHahnSeries} (h : x.coeff = y.coeff) : x = y :=
  Subtype.ext <| HahnSeries.ext h

/-- The support of the Hahn series. -/
def support (x : SurrealHahnSeries) : Set Surreal :=
  Function.support x.coeff

@[simp]
theorem support_coeff (x : SurrealHahnSeries) : Function.support x.coeff = x.support :=
  rfl

@[simp]
theorem support_mk (f small wf) : support (mk f small wf) = Function.support f :=
  rfl

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

/-- Recursion principle for `SurrealHahnSeries`. -/
@[elab_as_elim]
def recOn {motive : SurrealHahnSeries → Sort*} (x : SurrealHahnSeries)
    (mk : ∀ f small wf, motive (mk f small wf)) : motive x :=
  mk x.coeff x.small_support x.wellFoundedOn_support

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
theorem length_zero : length 0 = 0 := by
  rw [← Ordinal.lift_inj, ← type_support, Ordinal.lift_zero, type_eq_zero_iff_isEmpty]
  aesop

@[gcongr]
theorem length_mono {x y : SurrealHahnSeries.{u}} (h : x.support ⊆ y.support) :
    x.length ≤ y.length := by
  rw [← Ordinal.lift_le.{u + 1}, ← type_support, ← type_support]
  apply RelEmbedding.ordinal_type_le
  exact Subrel.inclusionEmbedding (· > ·) h

/-- Returns the `i`-th largest exponent with a non-zero coefficient. -/
def exp (x : SurrealHahnSeries) : (· < · : Iio x.length → _ → _) ≃r (· > · : x.support → _ → _) :=
  (enum _).trans (orderIsoShrink x.support).dual.toRelIsoLT.symm

theorem exp_strictAnti (x : SurrealHahnSeries) : StrictAnti x.exp :=
  fun _ _ ↦ x.exp.map_rel_iff'.2

/-- Returns the coefficient which corresponds to the `i`-th largest exponent, or `0` if no such
coefficient exists. -/
def coeffIdx (x : SurrealHahnSeries) (i : Ordinal.{u}) : ℝ :=
  if h : i < x.length then x.coeff (x.exp ⟨i, h⟩) else 0

theorem coeffIdx_of_lt (x : SurrealHahnSeries) {i : Ordinal} (h : i < x.length) :
    x.coeffIdx i = x.coeff (x.exp ⟨i, h⟩) := by
  rw [coeffIdx, dif_pos]

theorem coeffIdx_of_le (x : SurrealHahnSeries) {i : Ordinal} (h : x.length ≤ i) :
    x.coeffIdx i = 0 := by
  rw [coeffIdx, dif_neg h.not_gt]

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
  unfold ofSeq
  aesop

theorem support_ofSeq_subset : (ofSeq o f hf).support ⊆ range (Prod.fst ∘ f) :=
  ofSeq_aux o f

theorem support_ofSeq (hf' : ∀ i, (f i).2 ≠ 0) : (ofSeq o f hf).support = range (Prod.fst ∘ f) := by
  refine (ofSeq_aux o f).antisymm fun _ ↦ ?_
  simp only [Function.mem_support, ne_eq, dite_eq_right_iff, forall_exists_index]
  grind

private def ofSeq_relIso : (· < · : Iio o → _ → _) ≃r (· > · : range (Prod.fst ∘ f) → _ → _) := by
  refine .ofSurjective ⟨⟨fun x ↦ ⟨(f x).1, ⟨x, rfl⟩⟩, fun a b h ↦ hf.injective ?_⟩, hf.lt_iff_gt⟩
    fun _ ↦ ?_ <;> aesop

def length_ofSeq_le : (ofSeq o f hf).length ≤ o := by
  have := (ofSeq_relIso o f hf).symm.toRelEmbedding.isWellOrder
  rw [← Ordinal.lift_le, ← type_support, ← type_lt_Iio, (ofSeq_relIso o f hf).ordinal_type_eq]
  apply RelEmbedding.ordinal_type_le
  exact Subrel.inclusionEmbedding (· > ·) (support_ofSeq_subset ..)

private def ofSeq_relIso' (hf' : ∀ i, (f i).2 ≠ 0) :
    (· < · : Iio o → _ → _) ≃r (· > · : (ofSeq o f hf).support → _ → _) := by
  apply (ofSeq_relIso o f hf).trans (RelIso.subrel (· > ·) ..)
  rw [support_ofSeq o f hf hf']

def length_ofSeq (hf' : ∀ i, (f i).2 ≠ 0) : (ofSeq o f hf).length = o := by
  rw [← Ordinal.lift_inj, ← type_support, ← type_lt_Iio]
  exact (ofSeq_relIso' o f hf hf').ordinal_type_eq.symm

theorem exp_coeffIdx (i : Iio (ofSeq o f hf).length) (hf' : ∀ i, (f i).2 ≠ 0) :
    exp _ i = (f ⟨i, by convert ← i.2; exact length_ofSeq o f hf hf'⟩).1 := by
  change _ = (((RelIso.subrel (· < ·) _ _ <| by rw [length_ofSeq o f hf hf']).trans <|
    ofSeq_relIso' o f hf hf') i).1
  congr
  subsingleton

theorem coeffIdx_ofSeq {i : Ordinal} (hf' : ∀ i, (f i).2 ≠ 0) (hi : i < o) :
    coeffIdx (ofSeq o f hf) i = (f ⟨i, hi⟩).2 := by
  rw [coeffIdx_of_lt, exp_coeffIdx o f hf _ hf', coeff_ofSeq_of_eq]
  · rfl
  · rwa [length_ofSeq o f hf hf']

end ofSeq
end SurrealHahnSeries
