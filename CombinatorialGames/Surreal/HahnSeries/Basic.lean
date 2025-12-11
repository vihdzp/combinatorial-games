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

open Cardinal Set

/-! ### Surreal Hahn series -/

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

def mk (f : Surreal.{u} → ℝ) (hs₁ : Small.{u} (Function.support f))
    (hs₂ : (Function.support f).WellFoundedOn (· > ·)) : SurrealHahnSeries where
  val := toLex ⟨f ∘ OrderDual.ofDual, IsWF.isPWO hs₂⟩ 
  property := by rwa [small_iff_lift_mk_lt_univ, lift_id, univ_umax.{u, u}] at hs₁


#exit
open Classical in
/-- Constructs a surreal Hahn series from a decreasing sequence of exponents and their
associated coefficients. -/
def ofSeq (o : Ordinal.{u}) (f : Iio o → Surreal.{u} × ℝ) (h : StrictAnti (Prod.fst ∘ f)) :
    SurrealHahnSeries where
  val := {
    coeff i := if h : ∃ o, i = (f o).1 then (f <| Classical.choose h).2 else 0
    isPWO_support' := by
      rw [isPWO_iff_isWF]
      apply IsWF.mono (t := OrderDual.ofDual ⁻¹' range (Prod.fst ∘ f))
      · apply wellFoundedOn_range.2
        convert wellFounded_lt (α := Iio o)
        ext
        exact h.lt_iff_gt
      · sorry --aesop
  }
  property := by
    aesop
    sorry

#exit

/-- The support of the Hahn series. -/
def support (x : SurrealHahnSeries) : Set Surreal :=
  OrderDual.toDual ⁻¹' x.1.support

instance (x : SurrealHahnSeries) : WellFoundedGT x.support :=
  x.1.isWF_support.to_subtype

theorem small_support (x : SurrealHahnSeries.{u}) : Small.{u} x.support := by
  rw [Cardinal.small_iff_lift_mk_lt_univ, Cardinal.lift_id]
  exact lt_of_lt_of_eq x.2 Cardinal.univ_umax.symm

def coeff (x : SurrealHahnSeries) (i : Surreal) : ℝ :=
  x.1.coeff <| OrderDual.toDual i

end SurrealHahnSeries
