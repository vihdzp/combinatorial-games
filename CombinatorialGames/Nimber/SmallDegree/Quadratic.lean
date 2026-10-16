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

public noncomputable section

theorem Order.IsNormal.leftOrdContinuous {α β : Type*} [LinearOrder α] [LinearOrder β]
    {f : α → β} (hf : Order.IsNormal f) : LeftOrdContinuous f := by
  intro s x hs hx
  exact hf.map_isLUB hx hs

namespace Nimber
open Order Polynomial Set

@[expose]
def quadraticIrreducibles : Set Nimber :=
  {x | IsGroup x ∧ ∀ y < fieldClosure (succ x), x ≤ y ^ 2 - y - x}

theorem IsAlgClosed.mem_quadraticIrreducibles {t : Nimber} (ht : IsAlgClosed t) :
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

theorem isCofinal_quadraticIrreducibles : IsCofinal quadraticIrreducibles :=
  fun x => ⟨algClosure x, (IsAlgClosed.algClosure x).mem_quadraticIrreducibles, le_algClosure x⟩

def quadraticLower (x : Nimber) : Ordinal :=
  ⨆ (i : ↥(quadraticIrreducibles ∩ (fun y => y ^ 2 - y) '' Iio (fieldClosure x))),
    val ((Order.enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm ⟨i.1, i.2.1⟩)

def quadraticUpper (x : Nimber) : Ordinal :=
  ⨆ (i : ↥(quadraticIrreducibles ∩ Iio (fieldClosure x))),
    val ((Order.enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm ⟨i.1, i.2.1⟩)

theorem quadraticLower_eq_quadraticLower_fieldClosure (x : Nimber) :
    quadraticLower x = quadraticLower (fieldClosure x) := by
  unfold quadraticLower
  rw! (castMode := .all) [(IsField.fieldClosure x).fieldClosure_eq]
  rfl

theorem quadraticUpper_eq_quadraticUpper_fieldClosure (x : Nimber) :
    quadraticUpper x = quadraticUpper (fieldClosure x) := by
  unfold quadraticUpper
  rw! (castMode := .all) [(IsField.fieldClosure x).fieldClosure_eq]
  rfl

theorem quadraticLower_monotone : Monotone quadraticLower := by
  intro x y hxy
  unfold quadraticLower
  rw [Ordinal.iSup_le_iff]
  intro i
  refine Ordinal.le_iSup
    (fun i : ↥(quadraticIrreducibles ∩ (fun y ↦ y ^ 2 - y) '' Iio y.fieldClosure) =>
      val ((Order.enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm ⟨i.1, i.2.1⟩))
      ⟨i.1, i.2.1, ?_⟩
  grw [← hxy]
  exact i.2.2

-- theorem leftOrdContinuous_quadraticLower : LeftOrdContinuous quadraticLower := by
--   intro s x hs hx
--   constructor
--   · exact quadraticLower_monotone.mem_upperBounds_image hx.1
--   · intro c hc
--     unfold quadraticLower
--     rw [Ordinal.iSup_le_iff]
--     intro ⟨i, hi, hix⟩
--     obtain ⟨r, hrx, rfl⟩ := (mem_image _ _ _).1 hix
--     stop
--     obtain ⟨y, hy⟩ := hx.exists_between hrx
--     sorry

end Nimber
