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
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import Mathlib.RingTheory.Valuation.Integral

/-!
# Separable quadratic nimber extensions

todo: write module docstring
todo: prove `quadraticLower` is surjective
-/

universe u

public noncomputable section

theorem Order.IsNormal.leftOrdContinuous {α β : Type*} [LinearOrder α] [LinearOrder β]
    {f : α → β} (hf : Order.IsNormal f) : LeftOrdContinuous f := by
  intro s x hs hx
  exact hf.map_isLUB hx hs

-- is this a good name?
-- should more of these arguments be explicit?
theorem Ordinal.mul_le_mul_add_iff_of_lt
    {e x c d : Ordinal} (hex : e < x) : x * c ≤ x * d + e ↔ c ≤ d where
  mpr hcd := (mul_right_mono hcd).trans <| self_le_add_right _ e
  mp h := by
    convert Ordinal.div_le_left h x
    · rw [Ordinal.mul_div_cancel c hex.ne_zero]
    · rw [Ordinal.mul_add_div d hex.ne_zero, Ordinal.div_eq_zero_of_lt hex, add_zero]

open Ordinal in
theorem Ordinal.type_lt_Ico (a b : Ordinal.{u}) : typeLT (Set.Ico a b) = lift.{u + 1} (b - a) := by
  by_cases! hab : b < a
  · rw [Set.Ico_eq_empty hab.not_gt, Ordinal.sub_eq_zero_iff_le.2 hab.le,
      /- why is `type_empty` something different -/ Ordinal.type_eq_zero_of_empty, lift_zero]
  rw [le_iff_exists_add] at hab
  obtain ⟨b, rfl⟩ := hab
  rw [Ordinal.add_sub_cancel, ← type_lt_Iio]
  refine ((Set.orderIsoOfEq _ _ ?_).trans
    ((add_right_strictMono.strictMonoOn _).orderIso (a + ·) (Set.Iio b)).symm).ordinalType_congr
  -- `Set.image_const_add_Ico` requires commutativity :(
  apply subset_antisymm
  · intro x hx
    obtain ⟨x, rfl⟩ := exists_add_of_le hx.1
    apply Set.mem_image_of_mem
    exact lt_of_add_lt_add_left hx.2
  · rw [Set.image_subset_iff]
    intro x hx
    exact ⟨le_self_add, add_lt_add_right hx a⟩

namespace Nimber
open Order Polynomial Set

/-- A nimber is called a quadratic irreducible if it cannot be expressed as a finite sum of
smaller quadratic irreducibles and elements of the form `y ^ 2 - y`
for `y` in the smallest nimber field containing `x`. -/
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
  -- todo: figure out how to reduce code duplication with
  -- the other lemma `IsAlgClosed.leastNoRoots_fieldClosure_succ` in `Inseparable.lean`
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

private def quadraticAux (s : Set Nimber.{u}) : Ordinal :=
  ⨆ (i : ↥(quadraticIrreducibles ∩ s)),
    val ((Order.enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm ⟨i.1, i.2.1⟩) + 1

private theorem quadraticAux_monotone (s t : Set Nimber.{u})
    [Small.{u} s] [Small.{u} t] (hst : s ⊆ t) : quadraticAux s ≤ quadraticAux t := by
  unfold quadraticAux
  rw [Ordinal.iSup_le_iff]
  intro i
  exact Ordinal.le_iSup
    (fun i : ↥(quadraticIrreducibles ∩ t) =>
      val ((Order.enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm
        ⟨i.1, i.2.1⟩) + 1)
    ⟨i.1, i.2.1, hst i.2.2⟩

private theorem leftOrdContinuous_quadraticAux (s : Set (Set Nimber.{u}))
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
        val ((Order.enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm
          ⟨i.1, i.2.1⟩) + 1)
      ⟨i, hiq, hit⟩
  · rw [Ordinal.iSup_le_iff]
    intro t
    exact quadraticAux_monotone t (sUnion s) (subset_sUnion_of_mem t.2)

/-- For `x` a field, `quadraticLower x` is the ordinal index into `quadraticIrreducibles` giving
the smallest element of `quadraticIrreducibles` which is still irreducible in `x`, meaning,
it cannot be expressed as a finite sum of smaller quadratic irreducibles and
elements of the form `y ^ 2 - y` for `y < x`.
For `x` not a field, `quadraticLower x = quadraticLower (fieldClosure x)`. -/
def quadraticLower (x : Nimber) : Ordinal :=
  quadraticAux ((fun y => y ^ 2 - y) '' Iio (fieldClosure x))

/-- For `x` a field, `quadraticUpper x` is the ordinal index into `quadraticIrreducibles` giving
the unique element `y` of `quadraticIrreducibles` satisfying
`y ≤ z ↔ x ≤ z` for `z ∈ quadraticIrreducibles`.
For `x` not a field, `quadraticUpper x = quadraticUpper (fieldClosure x)`. -/
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

@[gcongr]
theorem quadraticLower_monotone : Monotone quadraticLower := by
  intro x y hxy
  unfold quadraticLower
  apply quadraticAux_monotone
  gcongr

@[gcongr]
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

theorem quadraticLower_le_quadraticUpper (x : Nimber) : quadraticLower x ≤ quadraticUpper x := by
  unfold quadraticLower quadraticUpper
  apply quadraticAux_monotone
  rw [Set.image_subset_iff]
  intro c hc
  exact (IsField.fieldClosure x).sub_lt ((IsField.fieldClosure x).pow_lt hc) hc

theorem le_quadraticUpper (x : Nimber) :
    x ≤ enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticUpper x)) := by
  by_contra! h
  apply (Ordinal.le_iSup (fun i : ↥(quadraticIrreducibles ∩ Iio (fieldClosure x)) =>
    val ((enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm ⟨i, i.2.1⟩) + 1)
    ⟨_, (enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticUpper x))).2,
      lt_of_lt_of_le h (le_fieldClosure x)⟩).not_gt
  rw [← quadraticAux, ← quadraticUpper]
  simp

theorem IsField.lt_quadraticUpper_iff {x : Nimber} (hx : IsField x) {y : quadraticIrreducibles} :
    y < enum quadraticIrreducibles isCofinal_quadraticIrreducibles
      (of (quadraticUpper x)) ↔ y < x := by
  constructor
  · intro hy
    rw [← OrderIso.symm_apply_lt, ← val_lt_iff, quadraticUpper, hx.fieldClosure_eq, quadraticAux,
      lt_ciSup_iff' Ordinal.bddAbove_of_small] at hy
    obtain ⟨i, hi⟩ := hy
    rw [lt_add_one_iff, val.le_iff_le, OrderIso.le_iff_le, ← Subtype.coe_le_coe] at hi
    exact hi.trans_lt i.2.2
  · rw [← Subtype.coe_lt_coe]
    exact (le_quadraticUpper x).trans_lt'

theorem IsField.quadraticUpper_le_iff {x : Nimber} (hx : IsField x) {y : quadraticIrreducibles} :
    enum quadraticIrreducibles isCofinal_quadraticIrreducibles
      (of (quadraticUpper x)) ≤ y ↔ x ≤ y := by
  rw [← not_lt, hx.lt_quadraticUpper_iff, not_lt]

end Nimber
