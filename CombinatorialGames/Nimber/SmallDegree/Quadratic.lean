/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import CombinatorialGames.Nimber.SimplestExtension.Algebraic
public import Mathlib.Order.OrdContinuous

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Valuation.Integral

/-!
# Separable quadratic nimber extensions

TODO: write module docstring
-/

universe u

noncomputable section

public theorem Order.IsNormal.leftOrdContinuous {α β : Type*} [LinearOrder α] [LinearOrder β]
    {f : α → β} (hf : Order.IsNormal f) : LeftOrdContinuous f := by
  intro s x hs hx
  exact hf.map_isLUB hx hs

namespace Nimber
open Order Polynomial Set

@[expose]
public def quadraticIrreducibles : Set Nimber :=
  {x | IsGroup x ∧ ∀ y < fieldClosure (succ x), x ≤ y ^ 2 - y - x}

public theorem IsAlgClosed.mem_quadraticIrreducibles {t : Nimber} (ht : IsAlgClosed t) :
    t ∈ quadraticIrreducibles := by
  classical
  refine ⟨ht.toIsGroup, fun y hyt => ?_⟩
  by_contra! hlt
  obtain ⟨c, hct, hcr⟩ := ht.exists_root (ne_of_eq_of_ne (by compute_degree!) two_ne_zero)
    (ht.coeff_sub_lt
      (ht.coeff_sub_lt (coeff_X_pow_lt 2 ht.one_lt) (coeff_X_lt ht.one_lt))
      (coeff_C_lt hlt))
  rw [IsRoot.def, eval_sub, eval_sub, eval_X_pow, eval_X, eval_C] at hcr
  let tt : (IsField.fieldClosure (succ t)).toSubfield := ⟨t, succ_le_iff.1 (le_fieldClosure _)⟩
  let rr : (IsField.fieldClosure (succ t)).toSubfield :=
    ⟨y + c, (IsField.fieldClosure _).add_lt hyt
      (hct.trans (succ_le_iff.1 (le_fieldClosure _)))⟩
  have hrr : IsRoot (X ^ 2 - X - C tt) rr := by
    rw [IsRoot.def, eval_sub, eval_sub, eval_X_pow, eval_X, eval_C]
    simp_rw [Subtype.ext_iff, Subfield.coe_sub, Subfield.coe_zero, SubmonoidClass.coe_pow, tt, rr]
    rw [CharTwo.add_sq, ← CharTwo.sub_eq_add, ← CharTwo.sub_eq_add, ← neg_zero, ← hcr]
    ring
  let e := (RatFunc.algEquivOfTranscendental t ht.transcendental).toRingEquiv.trans
    -- (.subfieldCongr ht.fieldAdjoin_simple_self)
    -- -- `IntermediateField.adjoin` shouldn't be exposed
    (@RingEquiv.subfieldCongr Nimber _ (IntermediateField.toSubfield _) _
      ht.fieldAdjoin_simple_self)
  have herr : e.symm tt = .X := by
    rw [RingEquiv.symm_apply_eq]
    unfold e tt
    apply Subtype.ext
    rw [RingEquiv.trans_apply]
    conv =>
      enter [2]
      -- no idea what's wrong here
      -- update: I figured it out! See Zulip thread "Subobject Hell"
      -- rw [@RingEquiv.coe_subfieldCongr_apply Nimber _
      --   (IntermediateField.toSubfield (.adjoin ht.toSubfield {t})) hf.toSubfield
      --   ((RatFunc.algEquivOfTranscendental t ht.transcendental).toRingEquiv .X)
      --   ht.fieldAdjoin_simple_self]
      apply RingEquiv.coe_subfieldCongr_apply
    simp
  have hrf : ((X ^ 2 - X - C tt).map e.symm).IsRoot (e.symm rr) := by
    apply IsRoot.map
    simpa [rr, Subtype.ext_iff] using hrr
  rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, IsRoot.def, eval_sub, eval_sub, eval_X_pow, eval_X, eval_C,
    RingEquiv.coe_toRingHom, herr] at hrf
  let pi : (RatFunc.inftyValuation ht.toSubfield).valuationSubring := ⟨.X⁻¹, by simp⟩
  have herr0 : e.symm rr ≠ 0 := by
    intro h
    simp [h, RatFunc.X_ne_zero] at hrf
  have hro : (X ^ 2 - C pi.1 * X - C pi.1).IsRoot (e.symm rr)⁻¹ := by
    rw [IsRoot.def, ← neg_zero, ← zero_mul (pi.1 / e.symm rr ^ 2),
      ← hrf, CharTwo.sub_eq_add (X ^ 2)]
    simp [pi]
    field [RatFunc.X_ne_zero]
  refine Irreducible.not_isRoot_of_natDegree_ne_one ?_
    (ne_of_eq_of_ne (by compute_degree!) (show 2 ≠ 1 by decide)) hro
  have hpi : X ^ 2 - C pi.1 * X - C pi.1 = (X ^ 2 - C pi * X - C pi).map (algebraMap _ _) := by
    simp
  have hdeg : (X ^ 2 - C pi * X - C pi).degree = 2 := by compute_degree!
  rw [hpi]
  refine (Monic.isPrimitive (by monicity!)).irreducible_iff_irreducible_map_fraction_map.mp ?_
  let P : Ideal (RatFunc.inftyValuation ht.toSubfield).valuationSubring :=
    IsLocalRing.maximalIdeal _
  have hP : P.IsPrime := inferInstance
  refine Polynomial.irreducible_of_eisenstein_criterion hP ?_ ?_
    (lt_of_lt_of_eq two_pos hdeg.symm) ?_ (Monic.isPrimitive (by monicity!))
  · rw [Monic.leadingCoeff (by monicity!)]
    exact hP.one_notMem
  · rw [hdeg]
    intro n hn
    rw [← Nat.cast_ofNat, Nat.cast_lt] at hn
    interval_cases n
    · unfold P
      rw [Valuation.mem_maximalIdeal_iff]
      simp [pi]
    · unfold P
      rw [Valuation.mem_maximalIdeal_iff]
      simp [pi]
  ·  -- todo: characterize powers of the maximal ideal in terms of the valuation
    rw [pow_two, coeff_sub, coeff_sub, coeff_X_pow, coeff_C_mul_X,
      ite_eq_right (by decide), ite_eq_right (by decide),
      sub_zero, zero_sub, coeff_C_zero, neg_mem_iff]
    intro pim
    have hpim : WithZero.exp (-2) < RatFunc.inftyValuation ht.toSubfield pi := by simp [pi]
    absurd hpim.not_ge
    generalize pi = c at pim ⊢
    -- todo: name the motive `motive`
    -- todo: deprecate `Submodule.mul_induction_on` in favor of `Submodule.mul_induction_on'`
    induction pim using Submodule.mul_induction_on' with
    | add x hx y hy ihx ihy => grw [Subring.coe_add, Valuation.map_add, ihx, ihy, max_self]
    | mem_mul_mem m hm n hn =>
      simp_rw [P, Valuation.mem_maximalIdeal_iff] at hm hn
      rw [← WithZero.exp_zero, ← neg_add_cancel 1, WithZero.exp_add,
        WithZero.lt_mul_exp_iff_le (by decide)] at hm hn
      grw [Subring.coe_mul, Valuation.map_mul, hm, hn]
      decide

public theorem isCofinal_quadraticIrreducibles : IsCofinal quadraticIrreducibles :=
  fun x => ⟨algClosure x, (IsAlgClosed.algClosure x).mem_quadraticIrreducibles, le_algClosure x⟩

def quadraticAux (s : Set Nimber.{u}) : Ordinal :=
  ⨆ (i : ↥(quadraticIrreducibles ∩ s)),
    val ((Order.enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm ⟨i.1, i.2.1⟩)

theorem quadraticAux_monotone (s t : Set Nimber.{u})
    [Small.{u} s] [Small.{u} t] (hst : s ⊆ t) : quadraticAux s ≤ quadraticAux t := by
  unfold quadraticAux
  rw [Ordinal.iSup_le_iff]
  intro i
  exact Ordinal.le_iSup
    (fun i : ↥(quadraticIrreducibles ∩ t) =>
      val ((Order.enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm ⟨i.1, i.2.1⟩))
    ⟨i.1, i.2.1, hst i.2.2⟩

theorem leftOrdContinuous_quadraticAux (s : Set (Set Nimber.{u}))
    (hs : Small.{u} s) (ht : ∀ t : s, Small.{u} t) :
    quadraticAux (sUnion s) = ⨆ t : s, quadraticAux t := by
  apply le_antisymm
  · rw [quadraticAux, Ordinal.iSup_le_iff]
    intro ⟨i, hiq, ⟨t, hts, hit⟩⟩
    refine le_trans ?_ (Ordinal.le_iSup (fun t : s => quadraticAux t) ⟨t, hts⟩)
    rw [quadraticAux]
    have : Small t := ‹∀ t : s, Small t› ⟨t, hts⟩
    exact Ordinal.le_iSup
      (fun i : ↥(quadraticIrreducibles ∩ t) =>
        val ((Order.enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm ⟨i.1, i.2.1⟩))
      ⟨i, hiq, hit⟩
  · rw [Ordinal.iSup_le_iff]
    intro t
    exact quadraticAux_monotone t (sUnion s) (subset_sUnion_of_mem t.2)

public section

def quadraticLower (x : Nimber) : Ordinal :=
  quadraticAux ((fun y => y ^ 2 - y) '' Iio (fieldClosure x))

def quadraticUpper (x : Nimber) : Ordinal :=
  quadraticAux (Iio (fieldClosure x))

theorem quadraticLower_eq_quadraticLower_fieldClosure (x : Nimber) :
    quadraticLower x = quadraticLower (fieldClosure x) := by
  unfold quadraticLower
  rw [(IsField.fieldClosure x).fieldClosure_eq]

theorem quadraticUpper_eq_quadraticUpper_fieldClosure (x : Nimber) :
    quadraticUpper x = quadraticUpper (fieldClosure x) := by
  unfold quadraticUpper
  rw [(IsField.fieldClosure x).fieldClosure_eq]

theorem quadraticLower_monotone : Monotone quadraticLower := by
  intro x y hxy
  unfold quadraticLower
  apply quadraticAux_monotone
  gcongr

theorem quadraticUpper_monotone : Monotone quadraticUpper := by
  intro x y hxy
  unfold quadraticUpper
  apply quadraticAux_monotone
  gcongr

theorem leftOrdContinuous_quadraticLower : LeftOrdContinuous quadraticLower.{u} := by
  intro s x hs hx
  have h : IsLUB (fieldClosure '' s) (fieldClosure x) := leftOrdContinuous_fieldClosure hs hx
  unfold quadraticLower
  rw [← h.biUnion_Iio_eq, Set.image_iUnion₂, ← sUnion_image, Set.image_image]
  have hss : Small.{u} s := Ordinal.bddAbove_iff_small.1 hx.bddAbove
  have hst : ∀ t : (fun x ↦ (fun y ↦ y ^ 2 - y) '' Iio x.fieldClosure) '' s, Small.{u} t := by
    simp_rw [Subtype.forall, forall_mem_image]
    infer_instance
  rw [leftOrdContinuous_quadraticAux _ inferInstance hst, ← sSup_image', Set.image_image]
  exact isLUB_csSup' Ordinal.bddAbove_of_small

theorem leftOrdContinuous_quadraticUpper : LeftOrdContinuous quadraticUpper.{u} := by
  intro s x hs hx
  have h : IsLUB (fieldClosure '' s) (fieldClosure x) := leftOrdContinuous_fieldClosure hs hx
  unfold quadraticUpper
  rw [← h.biUnion_Iio_eq, ← sUnion_image, Set.image_image]
  have hss : Small.{u} s := Ordinal.bddAbove_iff_small.1 hx.bddAbove
  have hst : ∀ t : (fun x ↦ Iio x.fieldClosure) '' s, Small.{u} t := by
    simp_rw [Subtype.forall, forall_mem_image]
    infer_instance
  rw [leftOrdContinuous_quadraticAux _ inferInstance hst, ← sSup_image', Set.image_image]
  exact isLUB_csSup' Ordinal.bddAbove_of_small

end

end Nimber
