/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Nimber.SimplestExtension.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.LinearAlgebra.Basis.Basic

import Mathlib.SetTheory.Ordinal.CantorNormalForm

/-!
# Nimbers as an `AddMonoidAlgebra`

We prove that if `b` is a field, then the base-`b` Cantor normal form of a nimber respects addition,
when viewed as a formal sum of powers of `b`.
-/

universe u

/-! ### For Mathlib -/

namespace Ordinal.CNF

@[simp]
theorem CNF_one (b : Ordinal) : CNF b 1 = [(0, 1)] := by
  obtain hb | hb := le_or_gt b 1
  · exact CNF.of_le_one hb one_ne_zero
  · exact CNF.of_lt one_ne_zero hb

theorem coeff_lt {b : Ordinal} (hb : 1 < b) (o e : Ordinal) : coeff b o e < b := by
  by_cases he : e ∈ (CNF b o).map Prod.fst
  · rw [List.mem_map, Prod.exists] at he
    obtain ⟨c, _, hc, rfl⟩ := he
    rw [coeff_of_mem_CNF hc]
    exact snd_lt hb hc
  · rw [coeff_of_notMem_CNF he]
    exact hb.pos

@[simp]
theorem coeff_one (b : Ordinal) : coeff b 1 = Finsupp.single 0 1 := by
  ext e
  obtain rfl | he := eq_or_ne e 0
  · rw [Finsupp.single_eq_same]
    apply coeff_of_mem_CNF
    simp
  · rw [coeff_of_notMem_CNF]
    · simp [he]
    · simpa

end Ordinal.CNF

namespace Finsupp
variable {M N α : Type*} [AddZeroClass M] [AddZeroClass N]

theorem mapRange_single_add {f : M → N} {g : α →₀ M} {hf : f 0 = 0} {a : α} {b : M}
    (hg : a ∉ g.support) : mapRange f hf (single a b + g) = single a (f b) + mapRange f hf g := by
  ext e
  obtain rfl | he := eq_or_ne e a
  · rw [notMem_support_iff] at hg
    simp_all
  · simp [he]

end Finsupp

namespace AddMonoidAlgebra
variable {R S : Type*} [Semiring R]

@[simp] theorem coe_zero : ⇑(0 : R[S]) = 0 := rfl
theorem zero_apply (x : S) : (0 : R[S]) x = 0 := rfl

variable [Zero S]

@[simp] theorem coe_one : ⇑(1 : R[S]) = single 0 1 := rfl

theorem one_apply_zero : (1 : R[S]) 0 = 1 := by simp
theorem one_apply_of_ne_zero {x : S} (hx : x ≠ 0) : (1 : R[S]) x = 0 := by simp [hx]

end AddMonoidAlgebra

public noncomputable section

namespace Nimber
variable (b : Nimber) (hb : IsField b)

open AddMonoidAlgebra Ordinal

/-! ### Nimbers as an `AddMonoidAlgebra` -/

/-- Interpret a nimber `x` as a sum of powers of `b`, for `b` a field.

This can be seen as a nimber specialization of the Cantor Normal form. -/
def toAddMonoidAlgebra (x : Nimber) : hb.toSubfield[Ordinal] :=
  (CNF.coeff b.val x.val).mapRange
    (fun z ↦ if h : z < b.val then ⟨z, h⟩ else ⟨0, hb.pos⟩) (dif_pos hb.pos)

@[simp]
private theorem toAddMonoidAlgebra_apply (x : Nimber) (e : Ordinal) :
    toAddMonoidAlgebra b hb x e = ⟨∗(CNF.coeff b.val x.val e), CNF.coeff_lt hb.one_lt _ e⟩ :=
  dif_pos ..

@[simp]
theorem toAddMonoidAlgebra_zero : toAddMonoidAlgebra b hb 0 = 0 := by
  ext; simp

@[simp]
theorem toAddMonoidAlgebra_one : toAddMonoidAlgebra b hb 1 = 1 := by
  ext e
  by_cases he : e = 0 <;> simp [he]

/-! ### `AddMonoidAlgebra`s as nimbers -/

/-- Add together powers of `b` to create a nimber. -/
@[pp_nodot]
def ofAddMonoidAlgebra (x : hb.toSubfield[Ordinal]) : Nimber :=
  ∗(CNF.eval b.val (x.mapRange (fun e ↦ e.1.val) rfl))

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem ofAddMonoidAlgebra_zero : ofAddMonoidAlgebra b hb 0 = 0 := by
  simp [ofAddMonoidAlgebra]

@[simp]
theorem ofAddMonoidAlgebra_one : ofAddMonoidAlgebra b hb 1 = 1 := by
  simp [ofAddMonoidAlgebra, one_def]

/-! ### Conversions -/

@[simp]
theorem toAddMonoidAlgebra_ofAddMonoidAlgebra (x : hb.toSubfield[Ordinal]) :
    toAddMonoidAlgebra b hb (ofAddMonoidAlgebra b hb x) = x := by
  ext e
  simp only [ofAddMonoidAlgebra, toAddMonoidAlgebra_apply, val_of]
  rw [CNF.coeff_eval (b := b.val) hb.one_lt] <;> simp

@[simp]
theorem ofAddMonoidAlgebra_toAddMonoidAlgebra (x : Nimber) :
    ofAddMonoidAlgebra b hb (toAddMonoidAlgebra b hb x) = x := by
  rw [ofAddMonoidAlgebra, of_eq_iff]
  convert CNF.eval_coeff _ _
  ext
  simp

theorem toAddMonoidAlgebra_injective : Function.Injective (toAddMonoidAlgebra b hb) :=
  Function.LeftInverse.injective (ofAddMonoidAlgebra_toAddMonoidAlgebra b hb)

theorem ofAddMonoidAlgebra_injective : Function.Injective (ofAddMonoidAlgebra b hb) :=
  Function.LeftInverse.injective (toAddMonoidAlgebra_ofAddMonoidAlgebra b hb)

@[simp]
theorem toAddMonoidAlgebra_inj {x y} :
    toAddMonoidAlgebra b hb x = toAddMonoidAlgebra b hb y ↔ x = y :=
  (toAddMonoidAlgebra_injective b hb).eq_iff

@[simp]
theorem ofAddMonoidAlgebra_inj {x y} :
    ofAddMonoidAlgebra b hb x = ofAddMonoidAlgebra b hb y ↔ x = y :=
  (ofAddMonoidAlgebra_injective b hb).eq_iff

set_option backward.isDefEq.respectTransparency false in
theorem ofAddMonoidAlgebra_def (x : hb.toSubfield[Ordinal]) :
    ofAddMonoidAlgebra b hb x = x.sum fun o y ↦ y * ∗(b.val ^ o) := by
  induction x using Finsupp.induction_on_max with
  | zero => simp
  | single_add o x f hf hx IH =>
    rw [ofAddMonoidAlgebra, Finsupp.mapRange_single_add (by contrapose! hf; use o),
      CNF.eval_single_add', (hb.opow o).mul_add_eq_of_lt', hb.opow_mul_eq_of_lt]
    · rw [Finsupp.sum_add_index' (by simp) (by simp [add_mul]), ← IH,
        Finsupp.sum_single_index (by simp), mul_comm, ofAddMonoidAlgebra]
    · simp
    · apply CNF.eval_lt
      · simp
      · simpa using hf
    · simpa using hf

@[simp]
theorem ofAddMonoidAlgebra_add (x y : hb.toSubfield[Ordinal]) :
    ofAddMonoidAlgebra b hb (x + y) = ofAddMonoidAlgebra b hb x + ofAddMonoidAlgebra b hb y := by
  simp_rw [ofAddMonoidAlgebra_def]
  apply Finsupp.sum_add_index'
  · simp
  · simp [add_mul]

/-- `toAddMonoidAlgebra` as an `AddEquiv`. -/
@[expose, simps!]
def toAddMonoidAlgebraAddEquiv : Nimber ≃+ hb.toSubfield[Ordinal] :=
  .symm {
    toFun := ofAddMonoidAlgebra b hb
    invFun := toAddMonoidAlgebra b hb
    map_add' := ofAddMonoidAlgebra_add b hb
    left_inv := toAddMonoidAlgebra_ofAddMonoidAlgebra b hb
    right_inv := ofAddMonoidAlgebra_toAddMonoidAlgebra b hb
  }

@[simp]
theorem toAddMonoidAlgebra_add (x y : Nimber) :
    toAddMonoidAlgebra b hb (x + y) = toAddMonoidAlgebra b hb x + toAddMonoidAlgebra b hb y :=
  (toAddMonoidAlgebraAddEquiv b hb).map_add x y

/-! ### Basis -/

/-- `toAddMonoidAlgebra` as a `LinearEquiv`. -/
@[expose, simps!]
def toAddMonoidAlgebraLinearEquiv : Nimber ≃ₗ[hb.toSubfield] (Ordinal →₀ hb.toSubfield) :=
  .symm {
    map_smul' := by simp [ofAddMonoidAlgebra_def, Finsupp.sum_smul_index, Finsupp.smul_sum,
      Subfield.smul_def, mul_assoc]
    __ := (toAddMonoidAlgebraAddEquiv b hb).symm
  }

/-- Ordinal powers of `b` as a basis for `Nimber`. -/
def IsField.opow_basis : Module.Basis Ordinal.{u} hb.toSubfield Nimber where
  repr := toAddMonoidAlgebraLinearEquiv b hb

end Nimber
end
