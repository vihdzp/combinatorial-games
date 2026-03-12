/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Nimber.SimplestExtension.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

import Mathlib.SetTheory.Ordinal.CantorNormalForm

/-!
# Nimbers as finitely supported functions

We prove that if `b` is a field, then the base-`b` Cantor normal form of a nimber respects addition,
when viewed as a formal sum of powers of `b`.
-/

universe u

/-! ### For Mathlib -/

namespace Ordinal.CNF

theorem coeff_lt {b : Ordinal} (hb : 1 < b) (o e : Ordinal) : coeff b o e < b := by
  by_cases he : e ∈ (CNF b o).map Prod.fst
  · rw [List.mem_map, Prod.exists] at he
    obtain ⟨c, _, hc, rfl⟩ := he
    rw [coeff_of_mem_CNF hc]
    exact snd_lt hb hc
  · rw [coeff_of_notMem_CNF he]
    exact hb.pos

theorem support_coeff_subset {b o x : Ordinal} (hx : x < b ^ o) :
    SetLike.coe (coeff b x).support ⊆ Set.Iio o := by
  obtain rfl | hb := eq_zero_or_pos b
  · have := hx.trans_le (zero_opow_le _)
    simp_all
  intro e
  rw [SetLike.mem_coe, Finsupp.mem_support_iff, Set.mem_Iio]
  contrapose!
  exact fun he ↦ coeff_eq_zero_of_lt (hx.trans_le (opow_le_opow_right hb he))

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

public noncomputable section

namespace Nimber
variable (b : Nimber) (hb : IsField b)

open Finsupp Ordinal Set

/-- `toFinsupp b hb x e` returns the coefficient of `b ^ e` in `x`. This is a specialization of
`Ordinal.CNF.coeff`. -/
@[pp_nodot]
def toFinsupp (x : Nimber) : Ordinal →₀ hb.toSubfield :=
  (CNF.coeff b.val x.val).mapRange
    (fun z ↦ if h : z < b.val then ⟨z, h⟩ else 0) (dif_pos hb.pos)

@[simp]
private theorem toFinsupp_apply (x : Nimber) (e : Ordinal) :
    toFinsupp b hb x e = ⟨∗(CNF.coeff b.val x.val e), CNF.coeff_lt hb.one_lt _ e⟩ :=
  dif_pos ..

@[simp]
theorem toFinsupp_zero : toFinsupp b hb 0 = 0 := by
  ext; simp

theorem support_toFinsupp_subset {o : Ordinal} {x : Nimber} (hx : x < ∗(b.val ^ o)) :
    SetLike.coe (toFinsupp b hb x).support ⊆ Iio o :=
  (SetLike.coe_subset_coe.2 (support_mapRange ..)).trans (CNF.support_coeff_subset hx)

/-- Add a linear combination of ordinal powers of `b` to create a nimber. This is a specialization
of `Ordinal.CNF.eval`. -/
@[pp_nodot]
def ofFinsupp (x : Ordinal →₀ hb.toSubfield) : Nimber :=
  ∗(CNF.eval b.val (x.mapRange (fun e ↦ e.1.val) rfl))

@[simp]
theorem ofFinsupp_zero : ofFinsupp b hb 0 = 0 := by
  simp [ofFinsupp]

theorem ofFinsupp_lt {o : Ordinal} {x : Ordinal →₀ hb.toSubfield}
    (hf : SetLike.coe x.support ⊆ Iio o) : ofFinsupp b hb x < ∗(b.val ^ o) := by
  apply CNF.eval_lt
  · simp
  · aesop

@[simp]
theorem toFinsupp_ofFinsupp (x) : toFinsupp b hb (ofFinsupp b hb x) = x := by
  ext e
  simp only [ofFinsupp, toFinsupp_apply, val_of]
  rw [CNF.coeff_eval (b := b.val) hb.one_lt] <;> simp

@[simp]
theorem ofFinsupp_toFinsupp (x) : ofFinsupp b hb (toFinsupp b hb x) = x := by
  rw [ofFinsupp, of_eq_iff]
  convert CNF.eval_coeff ..
  ext
  simp

theorem toFinsupp_injective : Function.Injective (toFinsupp b hb) :=
  Function.LeftInverse.injective (ofFinsupp_toFinsupp b hb)

theorem ofFinsupp_injective : Function.Injective (ofFinsupp b hb) :=
  Function.LeftInverse.injective (toFinsupp_ofFinsupp b hb)

@[simp]
theorem toFinsupp_inj {x y} : toFinsupp b hb x = toFinsupp b hb y ↔ x = y :=
  (toFinsupp_injective b hb).eq_iff

@[simp]
theorem ofFinsupp_inj {x y} : ofFinsupp b hb x = ofFinsupp b hb y ↔ x = y :=
  (ofFinsupp_injective b hb).eq_iff

theorem ofFinsupp_def (x) :
    ofFinsupp b hb x = x.linearCombination hb.toSubfield fun o ↦ ∗(val b ^ o) := by
  induction x using induction_on_max with
  | zero => simp
  | single_add o x f hf hx IH =>
    rw [ofFinsupp, mapRange_single_add (by contrapose! hf; use o),
      CNF.eval_single_add', (hb.opow o).mul_add_eq_of_lt', hb.opow_mul_eq_of_lt]
    · dsimp [linearCombination, lsum, Subfield.smul_def] at IH ⊢
      rw [sum_add_index' (by simp) (by simp [add_mul]), ← IH, sum_single_index (by simp), mul_comm]
      rfl
    · simp
    · apply CNF.eval_lt
      · simp
      · simpa using hf
    · simpa using hf

@[simp]
theorem ofFinsupp_single (x y) : ofFinsupp b hb (single x y) = y * ∗(b.val ^ x) := by
  simp [ofFinsupp_def, Subfield.smul_def]

@[simp]
theorem toFinsupp_opow_mul (o : Ordinal) {x : Nimber} (hx : x < b) :
    toFinsupp b hb (x * ∗(b.val ^ o)) = single o ⟨x, hx⟩ := by
  simp [← ofFinsupp_inj]

@[simp]
theorem toFinsupp_opow (o : Ordinal) : toFinsupp b hb (∗(b.val ^ o)) = single o 1 := by
  simpa using toFinsupp_opow_mul b hb o hb.one_lt

@[simp]
theorem toFinsupp_one : toFinsupp b hb 1 = single 0 1 := by
  simpa using toFinsupp_opow b hb 0

/-- `toFinsupp` as a `LinearEquiv`. -/
@[expose, simps!]
def toFinsuppIso : Nimber ≃ₗ[hb.toSubfield] (Ordinal →₀ hb.toSubfield) :=
  .symm {
    toFun := ofFinsupp b hb
    invFun := toFinsupp b hb
    left_inv := toFinsupp_ofFinsupp b hb
    right_inv := ofFinsupp_toFinsupp b hb
    map_add' x y := by
      simp_rw [ofFinsupp_def]
      apply sum_add_index'
      · simp
      · simp [add_mul, Subfield.smul_def]
    map_smul' := by simp [ofFinsupp_def]
  }

@[simp]
theorem toFinsupp_add (x y) : toFinsupp b hb (x + y) = toFinsupp b hb x + toFinsupp b hb y :=
  (toFinsuppIso b hb).map_add x y

@[simp]
theorem ofFinsupp_add (x y) : ofFinsupp b hb (x + y) = ofFinsupp b hb x + ofFinsupp b hb y :=
  (toFinsuppIso b hb).symm.map_add x y

/-- Ordinal powers of `b` form a basis for `Nimber`. -/
@[expose, simps!]
def IsField.opow_basis : Module.Basis Ordinal.{u} hb.toSubfield Nimber where
  repr := toFinsuppIso b hb

end Nimber
end
