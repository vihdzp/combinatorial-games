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
  -- todo: figure out how to reduce code duplication with
  -- the other lemma `IsAlgClosed.leastNoRoots_fieldClosure_succ` in `Quadratic.lean`
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
    val ((Order.enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm ⟨i.1, i.2.1⟩) + 1

theorem quadraticAux_monotone (s t : Set Nimber.{u})
    [Small.{u} s] [Small.{u} t] (hst : s ⊆ t) : quadraticAux s ≤ quadraticAux t := by
  unfold quadraticAux
  rw [Ordinal.iSup_le_iff]
  intro i
  exact Ordinal.le_iSup
    (fun i : ↥(quadraticIrreducibles ∩ t) =>
      val ((Order.enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm
        ⟨i.1, i.2.1⟩) + 1)
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
        val ((Order.enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm
          ⟨i.1, i.2.1⟩) + 1)
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

theorem IsField.lt_of_lt_quadraticUpper {x : Nimber} (hx : IsField x) {y : quadraticIrreducibles}
    (hy : y < enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticUpper x))) :
    y < x := by
  rw [← OrderIso.symm_apply_lt, ← val_lt_iff, quadraticUpper, hx.fieldClosure_eq, quadraticAux,
    lt_ciSup_iff' Ordinal.bddAbove_of_small] at hy
  obtain ⟨i, hi⟩ := hy
  rw [lt_add_one_iff, val.le_iff_le, OrderIso.le_iff_le, ← Subtype.coe_le_coe] at hi
  exact hi.trans_lt i.2.2

theorem le_quadraticUpper (x : Nimber) :
    x ≤ enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticUpper x)) := by
  by_contra! h
  apply (Ordinal.le_iSup (fun i : ↥(quadraticIrreducibles ∩ Iio (fieldClosure x)) =>
    val ((enum quadraticIrreducibles isCofinal_quadraticIrreducibles).symm ⟨i, i.2.1⟩) + 1)
    ⟨_, (enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticUpper x))).2,
      lt_of_lt_of_le h (le_fieldClosure x)⟩).not_gt
  rw [← quadraticAux, ← quadraticUpper]
  simp

theorem quadraticLower_two : quadraticLower (of 2) = 0 := by
  unfold quadraticLower
  rw [fieldClosure_two, Iio_two, Set.image_insert_eq, Set.image_singleton,
    zero_pow two_ne_zero, sub_zero, one_pow, sub_self, insert_eq_of_mem (by simp),
    ← Ordinal.bot_eq_zero, ← csSup_empty, quadraticAux]
  suffices _ : IsEmpty ↥(quadraticIrreducibles ∩ {0}) from iSup_of_empty' _
  rw [isEmpty_coe_sort, inter_singleton_eq_empty]
  intro h
  exact h.1.pos.false

theorem coe_enum_quadraticIrreducibles_zero :
    (enum quadraticIrreducibles isCofinal_quadraticIrreducibles 0).1 = 1 := by
  apply le_antisymm
  · let one : quadraticIrreducibles := ⟨1, by simp [quadraticIrreducibles, lt_two_iff]⟩
    change _ ≤ one.1
    rw [Subtype.coe_le_coe, ← OrderIso.le_symm_apply]
    apply zero_le
  · rw [one_le_iff_ne_zero]
    exact (enum quadraticIrreducibles isCofinal_quadraticIrreducibles 0).2.1.ne_zero

theorem notMem_image_of_quadraticLower_le (x : Nimber) {y : quadraticIrreducibles}
    (hy : enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x)) ≤ y) :
    y.1 ∉ (fun z => z ^ 2 - z) '' Iio x := by
  unfold quadraticLower quadraticAux at hy
  rw [← OrderIso.le_symm_apply, of_le_iff, ciSup_le_iff' Ordinal.bddAbove_of_small] at hy
  intro hyi
  refine (Order.lt_succ _).not_ge (hy ⟨y.1, y.2, mem_of_subset_of_mem ?_ hyi⟩)
  grw [← le_fieldClosure]

theorem IsField.leastNoRoots_lt_of_quadraticLower_lt
    {x : Nimber} (hx : IsField x)
    (hlt : enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x)) < x) :
    leastNoRoots x < .some (X ^ 3) := by
  by_contra! h2
  apply notMem_image_of_quadraticLower_le x le_rfl
  obtain ⟨r, hr, hrr⟩ := exists_root_of_lt_leastNoRoots
    (two_pos.trans_eq (.symm (by compute_degree!))).ne'
    (hx.coeff_sub_lt
      (hx.coeff_sub_lt (coeff_X_pow_lt 2 hx.one_lt) (coeff_X_lt hx.one_lt))
      (coeff_C_lt hlt))
    (lt_of_lt_of_le (WithTop.coe_lt_coe.2 (Lex.lt_X_pow_iff.2 (by compute_degree!))) h2)
  exact ⟨r, hr, by simpa [sub_eq_zero] using hrr⟩

theorem IsField.quadraticLower_fieldClosure_succ_of_not_perfectField {x : Nimber} (hx : IsField x)
    (perf : ¬PerfectField hx.toSubfield) :
    quadraticLower (fieldClosure (succ x)) = quadraticLower x := by
  have hl := hx.leastNoRoots_eq_of_not_perfectField perf
  have hnt : leastNoRoots x ≠ ⊤ := by simp [hl]
  have hld : ((leastNoRoots x).untop hnt).degree = 2 := by
    rw! [hl]
    rw [WithTop.untop_coe]
    compute_degree!
  have hfs : fieldClosure (succ x) = of (val x ^ 2) :=
    hx.fieldClosure_succ_eq_pow_degree_leastNoRoots hnt hld
  apply le_antisymm
  · rw [quadraticLower, quadraticAux]
    apply Ordinal.iSup_le
    intro ⟨c, hcq, hci⟩
    obtain ⟨r, hrx, rfl⟩ := hci
    rw [add_one_le_iff]
    set c : quadraticIrreducibles := ⟨r ^ 2 - r, hcq⟩
    rw [(IsField.fieldClosure _).fieldClosure_eq, mem_Iio, hfs] at hrx
    -- todo: figure out how to reduce code duplication with the other theorems in this file
    obtain ⟨p, hpd, hpc, hr⟩ := eq_oeval_of_lt_pow hx.ne_zero hrx
    rw [← hx.eval_eq_of_lt (X_pow_lt_leastNoRoots_of_le_degree hnt hld.ge).le hpd hpc] at hr
    rw [show Nat.cast 2 = Order.succ (1 : WithBot Nat) from rfl, lt_succ_iff] at hpd
    obtain ⟨a, b, rfl⟩ : ∃ a b, p = C a * X + C b :=
      ⟨_, _, Polynomial.eq_X_add_C_of_degree_le_one hpd⟩
    rw [eval_add, eval_C_mul, eval_X, eval_C] at hr
    have hrr : r ^ 2 - r = -a * x + (a ^ 2 * x ^ 2 + (b ^ 2 - b)) := by
      rw [← hr, CharTwo.add_sq]
      ring
    replace hrx : r ^ 2 - r < x := by
      by_contra! hxr
      apply (hx.pos.trans_le hxr).not_ge
      rw [← sub_self (r ^ 2 - r)]
      apply hcq.2
      exact (hrx.trans_eq hfs.symm).trans_le (fieldClosure_monotone (Order.succ_mono hxr))
    have hax : a < x := by simpa using hpc 1
    have hbx : b < x := by simpa using hpc 0
    have haax : -a * x < x := by
      rw [← sub_eq_iff_eq_add] at hrr
      rw [← hrr]
      apply hx.sub_lt hrx
      exact hx.add_lt (hx.mul_lt (hx.pow_lt hax) (hx.sq_lt_self_of_not_perfectField perf))
        (hx.sub_lt (hx.pow_lt hbx) hbx)
    rw [CharTwo.neg_eq, mul_comm, ← hx.mul_eq_of_lt hx.toIsRing le_rfl hax, of_lt_iff] at haax
    obtain rfl : a = 0 := by
      contrapose! haax
      apply Ordinal.le_mul_left
      exact val_pos.2 (pos_of_ne_zero haax)
    rw [val_lt_iff, OrderIso.symm_apply_lt]
    by_contra! hc
    apply notMem_image_of_quadraticLower_le x hc
    exact ⟨b, hbx, by simpa [c] using hrr.symm⟩
  · exact quadraticLower_monotone ((le_succ x).trans (le_fieldClosure (succ x)))

theorem IsField.quadraticLower_fieldClosure_succ_of_le_leastNoRoots {x : Nimber} (hx : IsField x)
    (h2 : .some (X ^ 3) ≤ leastNoRoots x) :
    quadraticLower (fieldClosure (succ x)) = quadraticLower x := by
  apply le_antisymm
  · rw [quadraticLower, quadraticAux, ciSup_le_iff' Ordinal.bddAbove_of_small]
    intro ⟨c, hcq, hcx⟩
    rw [Order.add_one_le_iff, val_lt_iff, OrderIso.symm_apply_lt]
    simp_rw [← Subtype.coe_lt_coe]
    refine lt_of_lt_of_le ?_ <| not_lt.1 <| mt hx.leastNoRoots_lt_of_quadraticLower_lt h2.not_gt
    by_contra! hxc
    obtain ⟨r, hr, rfl⟩ := hcx
    rw [(IsField.fieldClosure _).fieldClosure_eq, mem_Iio] at hr
    apply hcq.1.pos.not_ge
    rw [← sub_self (r ^ 2 - r)]
    apply hcq.2
    apply hr.trans_le
    rw [(IsField.fieldClosure _).fieldClosure_le_iff]
    exact (succ_mono hxc).trans (le_fieldClosure _)
  · exact quadraticLower_monotone ((le_succ x).trans (le_fieldClosure (succ x)))

mutual

theorem IsField.mem_image_of_lt_quadraticLower {x : Nimber} (hx : IsField x) {y : Nimber}
    (hyx : y < x)
    (hy : y < enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x))) :
    y ∈ (fun z => z ^ 2 - z) '' Iio x := by
  have ihx (z : Nimber) (hz : IsField z) (hzx : z < x) := @hz.mem_image_of_lt_quadraticLower
  have ihqs (z : Nimber) (hz : IsField z) (hzx : z < x) :=
    hz.quadraticLower_fieldClosure_succ_of_perfectField_of_leastNoRoots_lt
  have ihl (z : Nimber) (hz : IsField z) (hzx : z < x) :=
    @hz.leastNoRoots_eq_quadraticLower_of_perfectField_of_leastNoRoots_lt
  induction y using WellFoundedLT.induction with | ind y ihy
  replace ihy (z : Nimber) (hz : z < y) := ihy z hz (hz.trans hyx) (hz.trans hy)
  by_cases! hyq : y ∉ quadraticIrreducibles
  · by_cases! hyg : ¬IsGroup y
    · by_cases hy0 : y = 0
      · exact ⟨0, hx.pos, by simp [hy0]⟩
      · obtain ⟨z, hz, w, hw, hzw⟩ := exists_add_of_not_isGroup hyg hy0
        rw [← hzw]
        obtain ⟨u, hu, rfl⟩ := ihy z hz
        obtain ⟨v, hv, rfl⟩ := ihy w hw
        refine ⟨u + v, hx.add_lt hu hv, ?_⟩
        rw [sub_add_sub_comm, ← CharTwo.add_sq]
    · rw [quadraticIrreducibles, mem_ofPred, and_iff_right hyg] at hyq
      push Not at hyq
      obtain ⟨z, hzx, hz⟩ := hyq
      obtain ⟨w, hwx, hw⟩ := ihy _ hz
      refine ⟨z - w, hx.sub_lt ?_ hwx, ?_⟩
      · grw [hzx, hx.fieldClosure_le_iff, succ_le_iff, hyx]
      · rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at hw
        rw [hw, sub_sub_sub_comm]
        simp [CharTwo.sub_eq_add, CharTwo.add_sq]
  let yq : quadraticIrreducibles := ⟨y, hyq⟩
  obtain ⟨o, hox⟩ := mem_range_enumField_iff.2 hx
  by_cases ho0 : o = 0
  · rw [ho0, enumField_zero] at hox
    rw [← hox, quadraticLower_two, of_zero, coe_enum_quadraticIrreducibles_zero, lt_one_iff] at hy
    exact ⟨0, hx.pos, by simp [hy]⟩
  by_cases ho : IsSuccLimit o
  · have hne : (Iio o).Nonempty := ⟨0, pos_of_ne_zero ho0⟩
    rw [← hox, isNormal_enumField.lt_iff_exists_lt ho] at hyx
    change yq.1 < _ at hy
    rw [Subtype.coe_lt_coe, ← OrderIso.symm_apply_lt, ← val_lt_iff] at hy
    rw [← hox, ← ho.sSup_Iio, isNormal_enumField.map_sSup hne Ordinal.bddAbove_of_small,
      leftOrdContinuous_quadraticLower.map_csSup (hne.image _) (bddAbove_of_small _),
      Set.image_image, lt_csSup_iff' Ordinal.bddAbove_of_small, exists_mem_image] at hy
    obtain ⟨o', hoo', hyx⟩ := hyx
    obtain ⟨o'', hoo'', hy⟩ := hy
    rw [val_lt_iff, OrderIso.symm_apply_lt] at hy
    grw [← hox, ← max_lt hoo' hoo'']
    exact ihx (Nimber.enumField (max o' o'')) (IsField.enumField (max o' o''))
      ((isNormal_enumField.strictMono (max_lt hoo' hoo'')).trans_eq hox)
      (hyx.trans_le (isNormal_enumField.monotone (le_max_left o' o'')))
      (hy.trans_le (by grw [← le_max_right]))
  rw [← isSuccPrelimit_iff_isSuccLimit_of_not_isMin (not_isMin_of_lt (pos_of_ne_zero ho0)),
    not_isSuccPrelimit_iff_succ_eq] at ho
  obtain ⟨o, -, rfl⟩ := ho
  rw [succ_eq_add_one, enumField_add_one] at hox
  have hxe : Nimber.enumField o < x := ((lt_succ _).trans_le (le_fieldClosure _)).trans_eq hox
  by_cases! hcl : y < enum quadraticIrreducibles isCofinal_quadraticIrreducibles
      (of (quadraticLower (Nimber.enumField o)))
  · grw [← hox, ← le_fieldClosure, ← le_succ]
    refine ihx (Nimber.enumField o) (IsField.enumField o) hxe ?_ hcl
    change yq.1 < _
    apply (IsField.enumField o).lt_of_lt_quadraticUpper
    grw [← Subtype.coe_lt_coe, ← quadraticLower_le_quadraticUpper, ← hcl]
  have perf : PerfectField (IsField.enumField o).toSubfield := by
    contrapose! hcl
    rwa [← (IsField.enumField o).quadraticLower_fieldClosure_succ_of_not_perfectField hcl, hox]
  have h2 : leastNoRoots (Nimber.enumField o) < .some (X ^ 3) := by
    contrapose! hcl
    rwa [← (IsField.enumField o).quadraticLower_fieldClosure_succ_of_le_leastNoRoots hcl, hox]
  change yq.1 < _ at hy
  rw [← hox, ihqs (Nimber.enumField o) (IsField.enumField o) hxe perf h2,
    Subtype.coe_lt_coe, ← OrderIso.symm_apply_lt, ← val_lt_iff, lt_add_one_iff,
    val_le_iff, OrderIso.symm_apply_le, ← Subtype.coe_le_coe] at hy
  cases le_antisymm hcl hy
  refine ⟨Nimber.enumField o, hxe, eq_of_sub_eq_zero ?_⟩
  simpa using (IsField.enumField o).isRoot_leastNoRoots_of_eq
    (ihl (Nimber.enumField o) (IsField.enumField o) hxe perf h2)
termination_by (x, 0)

private
theorem IsField.le_of_quadraticLower_le {x : Nimber} (hx : IsField x) {y : quadraticIrreducibles}
    (hy : enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x)) ≤ y)
    {z : Nimber} (hz : z < x) :
    y ≤ z ^ 2 - z - y := by
  have ihx (w : Nimber) (hw : IsField w) (hwx : w < x) := @hw.le_of_quadraticLower_le
  have ihqs (w : Nimber) (hw : IsField w) (hwx : w < x) :=
    hw.quadraticLower_fieldClosure_succ_of_perfectField_of_leastNoRoots_lt
  have ihl (w : Nimber) (hw : IsField w) (hwx : w < x) :=
    @hw.leastNoRoots_eq_quadraticLower_of_perfectField_of_leastNoRoots_lt
  have ihm (w : Nimber) (hw : IsField w) (hwx : w < x) :=
    hw.quadraticLower_lt_of_perfectField_of_leastNoRoots_lt
  obtain ⟨o, hox⟩ := mem_range_enumField_iff.2 hx
  by_cases ho0 : o = 0
  · rw [ho0, enumField_zero] at hox
    rw [← hox, lt_two_iff] at hz
    obtain rfl | rfl := hz <;> simp
  by_cases ho : IsSuccLimit o
  · have hne : (Iio o).Nonempty := ⟨0, pos_of_ne_zero ho0⟩
    rw [← hox, isNormal_enumField.lt_iff_exists_lt ho] at hz
    obtain ⟨o', hoo', hyx⟩ := hz
    refine ihx (Nimber.enumField o') (IsField.enumField o')
      ((isNormal_enumField.strictMono hoo').trans_eq hox) (le_trans ?_ hy) hyx
    rw [← hox]
    gcongr
  rw [← isSuccPrelimit_iff_isSuccLimit_of_not_isMin (not_isMin_of_lt (pos_of_ne_zero ho0)),
    not_isSuccPrelimit_iff_succ_eq] at ho
  obtain ⟨o, -, rfl⟩ := ho
  rw [succ_eq_add_one, enumField_add_one] at hox
  have hxe : Nimber.enumField o < x := ((lt_succ _).trans_le (le_fieldClosure _)).trans_eq hox
  by_cases! hlt : Nimber.enumField o ≤ y
  · apply y.2.2
    grw [hz, ← hox, (IsField.fieldClosure _).fieldClosure_le_iff, hlt, ← le_fieldClosure]
  by_cases! perf : ¬PerfectField (IsField.enumField o).toSubfield
  · have hlr := (IsField.enumField o).leastNoRoots_eq_of_not_perfectField perf
    have hnt : leastNoRoots (Nimber.enumField o) ≠ ⊤ := by simp [hlr]
    have hld : ((leastNoRoots (Nimber.enumField o)).untop hnt).degree = 2 := by
      rw! [hlr]
      rw [WithTop.untop_coe]
      compute_degree!
    have hfs : fieldClosure (succ (Nimber.enumField o)) = of (val (Nimber.enumField o) ^ 2) :=
      (IsField.enumField o).fieldClosure_succ_eq_pow_degree_leastNoRoots hnt hld
    rw [← hox, hfs] at hz
    -- todo: figure out how to reduce code duplication with the other theorems in this file
    obtain ⟨p, hpd, hpc, hz⟩ := eq_oeval_of_lt_pow (IsField.enumField o).ne_zero hz
    rw [← (IsField.enumField o).eval_eq_of_lt
      (X_pow_lt_leastNoRoots_of_le_degree hnt hld.ge).le hpd hpc] at hz
    rw [show Nat.cast 2 = Order.succ (1 : WithBot Nat) from rfl, lt_succ_iff] at hpd
    obtain ⟨a, b, rfl⟩ : ∃ a b, p = C a * X + C b :=
      ⟨_, _, Polynomial.eq_X_add_C_of_degree_le_one hpd⟩
    rw [eval_add, eval_C_mul, eval_X, eval_C] at hz
    have hzr : z ^ 2 - z =
        -a * Nimber.enumField o + (a ^ 2 * Nimber.enumField o ^ 2 + (b ^ 2 - b)) := by
      rw [← hz, CharTwo.add_sq]
      ring
    have hax : a < Nimber.enumField o := by simpa using hpc 1
    have hbx : b < Nimber.enumField o := by simpa using hpc 0
    by_cases ha0 : a = 0
    · rw [hzr, ha0, neg_zero, zero_mul, zero_add, zero_pow two_ne_zero, zero_mul, zero_add]
      refine ihx (Nimber.enumField o) (IsField.enumField o) hxe ?_ hbx
      grw [← hy, ← hox, ← le_fieldClosure, ← le_succ]
    · grw [hlt]
      by_contra! hcx
      rw [← sub_add_cancel (z ^ 2 - z) y, ← sub_eq_sub_iff_add_eq_add, eq_sub_iff_add_eq] at hzr
      have haao : a * Nimber.enumField o < Nimber.enumField o := by
        rw [← CharTwo.neg_eq a, ← hzr]
        exact (IsField.enumField o).add_lt ((IsField.enumField o).sub_lt hcx
          ((IsField.enumField o).add_lt
            ((IsField.enumField o).mul_lt ((IsField.enumField o).pow_lt hax)
              ((IsField.enumField o).sq_lt_self_of_not_perfectField perf))
            ((IsField.enumField o).sub_lt ((IsField.enumField o).pow_lt hbx) hbx))) hlt
      apply haao.not_ge
      rw [mul_comm, ← (IsField.enumField o).mul_eq_of_lt (IsField.enumField o).toIsRing le_rfl hax,
        ← val_le_iff]
      apply Ordinal.le_mul_left
      simpa [pos_iff_ne_zero] using ha0
  · have h2 := (IsField.enumField o).leastNoRoots_lt_of_quadraticLower_lt (by grw [hxe, hy, hlt])
    have hlr := ihl (Nimber.enumField o) (IsField.enumField o) hxe perf h2
    have hnt : leastNoRoots (Nimber.enumField o) ≠ ⊤ := by simp [hlr]
    have hld : ((leastNoRoots (Nimber.enumField o)).untop hnt).degree = 2 := by
      rw! [hlr]
      rw [WithTop.untop_coe]
      compute_degree!
    have hfs : fieldClosure (succ (Nimber.enumField o)) = of (val (Nimber.enumField o) ^ 2) :=
      (IsField.enumField o).fieldClosure_succ_eq_pow_degree_leastNoRoots hnt hld
    have hrt := (IsField.enumField o).isRoot_leastNoRoots hnt
    rw! [hlr] at hrt
    rw [WithTop.untop_coe, IsRoot.def, eval_sub, eval_sub, eval_X_pow, eval_X, eval_C,
      sub_eq_zero] at hrt
    rw [← hox, hfs] at hz
    -- todo: figure out how to reduce code duplication with the other theorems in this file
    obtain ⟨p, hpd, hpc, hz⟩ := eq_oeval_of_lt_pow (IsField.enumField o).ne_zero hz
    rw [← (IsField.enumField o).eval_eq_of_lt
      (X_pow_lt_leastNoRoots_of_le_degree hnt hld.ge).le hpd hpc] at hz
    rw [show Nat.cast 2 = Order.succ (1 : WithBot Nat) from rfl, lt_succ_iff] at hpd
    obtain ⟨a, b, rfl⟩ : ∃ a b, p = C a * X + C b :=
      ⟨_, _, Polynomial.eq_X_add_C_of_degree_le_one hpd⟩
    rw [eval_add, eval_C_mul, eval_X, eval_C] at hz
    have hzr : z ^ 2 - z = (a ^ 2 - a) * Nimber.enumField o + (a ^ 2 *
        (enum quadraticIrreducibles isCofinal_quadraticIrreducibles
          (of (quadraticLower (Nimber.enumField o)))) +
        (b ^ 2 - b)) := by
      rw [← hz, CharTwo.add_sq, mul_pow]
      calc
        _ = _ := by ring
        _ = _ := congr(a ^ 2 * $hrt + (a ^ 2 - a) * Nimber.enumField o + b ^ 2 - b)
        _ = _ := by ring
    have hax : a < Nimber.enumField o := by simpa using hpc 1
    have hbx : b < Nimber.enumField o := by simpa using hpc 0
    by_cases ha0 : a * (a - 1) = 0
    · rw [mul_eq_zero] at ha0
      obtain ha0 | ha1 := ha0
      · rw [hzr, ha0, zero_pow two_ne_zero, sub_zero, zero_mul, zero_mul, zero_add, zero_add]
        refine ihx (Nimber.enumField o) (IsField.enumField o) hxe ?_ hbx
        grw [← hy, ← hox, ← le_fieldClosure, ← le_succ]
      · rw [sub_eq_zero] at ha1
        rw [hzr, ha1, one_pow, sub_self, zero_mul, one_mul, zero_add, add_sub_assoc]
        by_contra! hcx
        have hcy : y ≤ b ^ 2 - b - y :=
          ihx (Nimber.enumField o) (IsField.enumField o) hxe
            (by grw [← hy, ← hox, ← le_fieldClosure, ← le_succ]) hbx
        apply hcy.not_gt
        rw [← add_sub_cancel_left
          (enum quadraticIrreducibles isCofinal_quadraticIrreducibles
            (of (quadraticLower (Nimber.enumField o)))).1 (b ^ 2 - b - y)]
        apply y.2.1.sub_lt hcx
        rwa [Subtype.coe_lt_coe, ← OrderIso.lt_symm_apply, of_lt_iff, ← add_one_le_iff,
          ← of_le_iff, OrderIso.le_symm_apply,
          ← ihqs (Nimber.enumField o) (IsField.enumField o) hxe perf h2, hox]
    · grw [hlt]
      by_contra! hcx
      rw [← sub_add_cancel (z ^ 2 - z) y, ← sub_eq_sub_iff_add_eq_add, eq_sub_iff_add_eq] at hzr
      have haao : (a ^ 2 - a) * Nimber.enumField o < Nimber.enumField o := by
        rw [← hzr]
        exact (IsField.enumField o).add_lt ((IsField.enumField o).sub_lt hcx
          ((IsField.enumField o).add_lt
            ((IsField.enumField o).mul_lt ((IsField.enumField o).pow_lt hax)
              (ihm (Nimber.enumField o) (IsField.enumField o) hxe perf h2))
            ((IsField.enumField o).sub_lt ((IsField.enumField o).pow_lt hbx) hbx))) hlt
      apply haao.not_ge
      rw [mul_comm, ← (IsField.enumField o).mul_eq_of_lt (IsField.enumField o).toIsRing le_rfl
        ((IsField.enumField o).sub_lt ((IsField.enumField o).pow_lt hax) hax),
        ← val_le_iff]
      apply Ordinal.le_mul_left
      simpa [pos_iff_ne_zero, mul_sub, sq] using ha0
termination_by (x, 0)

-- actually, this is still true without the `perf` assumption,
-- by the classification of imperfect nimber fields
theorem IsField.quadraticLower_lt_of_perfectField_of_leastNoRoots_lt
    {x : Nimber} (hx : IsField x) (perf : PerfectField hx.toSubfield)
    (h2 : leastNoRoots x < .some (X ^ 3)) :
    enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x)) < x := by
  have ihc := @hx.mem_image_of_lt_quadraticLower
  contrapose! h2
  apply hx.le_leastNoRoots_of_exists_isRoot
  intro q hq hqd hc
  rw [Lex.lt_X_pow_iff, show Nat.cast 3 = Order.succ (2 : WithBot Nat) from rfl,
    lt_succ_iff] at hq
  rw [← succ_le_iff, WithBot.succ_one'] at hqd
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, q = C a * X ^ 2 + C b * X + C c :=
    -- todo: move this lemma from `Mathlib.RingTheory.Polynomial.SmallDegreeVieta`
    -- to `Mathlib.Algebra.Polynomial.Degree.SmallDegree`?
    ⟨_, _, _, Polynomial.eq_quadratic_of_degree_le_two hq⟩
  have hax : a < x := by simpa using hc 2
  have hbx : b < x := by simpa using hc 1
  have hcx : c < x := by simpa using hc 0
  have ha0 : 0 < a := by
    simpa [pos_iff_ne_zero] using coeff_ne_zero_of_eq_degree (le_antisymm hq hqd)
  obtain rfl | hb := eq_or_ne b 0
  · refine ⟨√(c / a), ?_, by simp [div_pow, mul_div_cancel₀ c ha0.ne']⟩
    exact hx.sqrt_lt' (hx.div_lt hcx hax) perf
  · have hyx := hx.div_lt (hx.mul_lt hax hcx) (hx.mul_lt hbx hbx)
    obtain ⟨r, hrx, hr⟩ := ihc hyx (hyx.trans_le h2)
    refine ⟨r * (b / a), hx.mul_lt hrx (hx.div_lt hbx hax), ?_⟩
    rw [IsRoot.def, eval_add, eval_add, eval_C, eval_C_mul, eval_C_mul, eval_X_pow, eval_X,
      ← CharTwo.sub_eq_add, ← CharTwo.sub_eq_add]
    calc
      _ = _ := by field
      _ = _ := congr(b * b / a * $hr - c)
      _ = _ := by field
termination_by (x, 1)

theorem IsField.leastNoRoots_eq_quadraticLower_of_perfectField_of_leastNoRoots_lt
    {x : Nimber} (hx : IsField x) (perf : PerfectField hx.toSubfield)
    (h2 : leastNoRoots x < .some (X ^ 3)) :
    leastNoRoots x = .some (X ^ 2 - X -
      C (enum quadraticIrreducibles isCofinal_quadraticIrreducibles
        (of (quadraticLower x))).1) := by
  have ihc := @hx.mem_image_of_lt_quadraticLower
  have ihl := hx.quadraticLower_lt_of_perfectField_of_leastNoRoots_lt perf h2
  apply le_antisymm
  · apply leastNoRoots_le_of_not_isRoot
    · refine zero_lt_two.trans_eq (Eq.symm ?_)
      compute_degree!
    · apply hx.coeff_sub_lt (hx.coeff_sub_lt (coeff_X_pow_lt 2 hx.one_lt) (coeff_X_lt hx.one_lt))
      exact coeff_C_lt ihl
    · intro r hr hrr
      rw [IsRoot.def, eval_sub, eval_sub, eval_X_pow, eval_X, eval_C, sub_eq_zero] at hrr
      apply notMem_image_of_quadraticLower_le x le_rfl
      rw [← hrr]
      exact Set.mem_image_of_mem (fun z => z ^ 2 - z) hr
  · apply hx.le_leastNoRoots_of_exists_isRoot
    rw [show X ^ 2 - X -
      C (enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x))).1 =
      C 1 * X ^ 2 + C 1 * X +
      C (enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x))).1 by
        simp [CharTwo.sub_eq_add], Lex.forall_lt_quadratic]
    refine ⟨fun c hc _ _ => ?_, fun b hb c hd hc => ?_, fun a ha _ _ hd => ?_⟩
    · obtain ⟨r, hr, rfl⟩ := ihc (hc.trans ihl) hc
      refine ⟨r, hr, ?_⟩
      rw [IsRoot.def, eval_add, eval_add, map_one, one_mul, one_mul, eval_X_pow, eval_X, eval_C,
        CharTwo.add_eq_zero, ← CharTwo.sub_eq_add]
    · obtain rfl := lt_one_iff.1 hb
      exact ⟨√c, hx.sqrt_lt' (by simpa using hc 0) perf, by simp⟩
    · absurd hd.not_ge
      rw [lt_one_iff.1 ha]
      simp [degree_linear_le]
termination_by (x, 2)

theorem IsField.quadraticLower_fieldClosure_succ_of_perfectField_of_leastNoRoots_lt
    {x : Nimber} (hx : IsField x) (perf : PerfectField hx.toSubfield)
    (h2 : leastNoRoots x < .some (X ^ 3)) :
    quadraticLower (fieldClosure (succ x)) = quadraticLower x + 1 := by
  have ih := hx.leastNoRoots_eq_quadraticLower_of_perfectField_of_leastNoRoots_lt perf h2
  have ihl := hx.quadraticLower_lt_of_perfectField_of_leastNoRoots_lt perf h2
  have ihs := @hx.le_of_quadraticLower_le
  have hnt : leastNoRoots x ≠ ⊤ := by simp [ih]
  have hld : ((leastNoRoots x).untop hnt).degree = 2 := by
    rw! [ih]
    rw [WithTop.untop_coe]
    compute_degree!
  have hfs : fieldClosure (succ x) = of (val x ^ 2) :=
    hx.fieldClosure_succ_eq_pow_degree_leastNoRoots hnt hld
  have hrt := hx.isRoot_leastNoRoots hnt
  rw! [ih] at hrt
  rw [WithTop.untop_coe, IsRoot.def, eval_sub, eval_sub, eval_X_pow, eval_X, eval_C,
    sub_eq_zero] at hrt
  apply le_antisymm
  · rw [quadraticLower, quadraticAux]
    apply Ordinal.iSup_le
    intro ⟨c, hcq, hci⟩
    obtain ⟨r, hrx, rfl⟩ := hci
    apply add_left_mono
    set c : quadraticIrreducibles := ⟨r ^ 2 - r, hcq⟩
    rw [(IsField.fieldClosure _).fieldClosure_eq, mem_Iio, hfs] at hrx
    -- todo: figure out how to reduce code duplication with the other theorems in this file
    obtain ⟨p, hpd, hpc, hr⟩ := eq_oeval_of_lt_pow hx.ne_zero hrx
    rw [← hx.eval_eq_of_lt (X_pow_lt_leastNoRoots_of_le_degree hnt hld.ge).le hpd hpc] at hr
    rw [show Nat.cast 2 = Order.succ (1 : WithBot Nat) from rfl, lt_succ_iff] at hpd
    obtain ⟨a, b, rfl⟩ : ∃ a b, p = C a * X + C b :=
      ⟨_, _, Polynomial.eq_X_add_C_of_degree_le_one hpd⟩
    rw [eval_add, eval_C_mul, eval_X, eval_C] at hr
    have hrr : r ^ 2 - r = (a ^ 2 - a) * x + (a ^ 2 *
        (enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x))) +
        (b ^ 2 - b)) := by
      rw [← hr, CharTwo.add_sq, mul_pow]
      calc
        _ = _ := by ring
        _ = _ := congr(a ^ 2 * $hrt + (a ^ 2 - a) * x + b ^ 2 - b)
        _ = _ := by ring
    replace hrx : r ^ 2 - r < x := by
      by_contra! hxr
      apply (hx.pos.trans_le hxr).not_ge
      rw [← sub_self (r ^ 2 - r)]
      apply hcq.2
      exact (hrx.trans_eq hfs.symm).trans_le (fieldClosure_monotone (Order.succ_mono hxr))
    have hax : a < x := by simpa using hpc 1
    have hbx : b < x := by simpa using hpc 0
    have haax : (a ^ 2 - a) * x < x := by
      rw [← sub_eq_iff_eq_add] at hrr
      rw [← hrr]
      apply hx.sub_lt hrx
      exact hx.add_lt (hx.mul_lt (hx.pow_lt hax) ihl) (hx.sub_lt (hx.pow_lt hbx) hbx)
    rw [mul_comm, ← hx.mul_eq_of_lt hx.toIsRing le_rfl (hx.sub_lt (hx.pow_lt hax) hax),
      of_lt_iff] at haax
    have haq : a * (a - 1) = 0 := by
      rw [mul_sub, mul_one, ← sq]
      contrapose! haax
      apply Ordinal.le_mul_left
      exact val_pos.2 (pos_of_ne_zero haax)
    rw [mul_eq_zero, sub_eq_zero] at haq
    rw [val_le_iff, OrderIso.symm_apply_le]
    obtain rfl | rfl := haq
    · by_contra! hlt
      apply notMem_image_of_quadraticLower_le x hlt.le
      refine ⟨b, hbx, ?_⟩
      simp [c, ← hr]
    · by_contra! hc
      apply hc.not_ge
      rw [one_pow, sub_self, one_mul, zero_mul, zero_add,
        ← CharTwo.add_eq_iff_eq_add, add_comm, ← CharTwo.sub_eq_add] at hrr
      rw [← Subtype.coe_le_coe, ← hrr]
      exact ihs hc.le hbx
  · rw [Order.add_one_le_iff]
    apply lt_of_le_of_ne
    · exact quadraticLower_monotone ((le_succ x).trans (le_fieldClosure (succ x)))
    intro heq
    apply notMem_image_of_quadraticLower_le (fieldClosure (succ x)) (OrderIso.monotone _ heq.ge)
    exact ⟨x, (lt_succ x).trans_le (le_fieldClosure (succ x)), hrt⟩
termination_by (x, 3)

end

theorem le_of_quadraticLower_le (x : Nimber) {y : quadraticIrreducibles}
    (hy : enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x)) ≤ y)
    {z : Nimber} (hz : z < x) :
    y ≤ z ^ 2 - z - y := by
  apply (IsField.fieldClosure x).le_of_quadraticLower_le
  · rwa [← quadraticLower_eq_quadraticLower_fieldClosure]
  · exact hz.trans_le (le_fieldClosure x)

-- in fact this still holds without the `perf` assumption,
-- by the classification of imperfect nimber fields
theorem IsField.quadraticLower_eq_quadraticUpper_iff_of_perfectField {x : Nimber} (hx : IsField x)
    (perf : PerfectField hx.toSubfield) :
    quadraticLower x = quadraticUpper x ↔ .some (X ^ 3) ≤ leastNoRoots x := by
  rw [le_antisymm_iff, and_iff_right (quadraticLower_le_quadraticUpper x), le_iff_le_iff_lt_iff_lt,
    ← of.lt_iff_lt, ← (enum quadraticIrreducibles isCofinal_quadraticIrreducibles).lt_iff_lt]
  constructor
  · intro hlt
    apply hx.leastNoRoots_lt_of_quadraticLower_lt
    exact hx.lt_of_lt_quadraticUpper hlt
  · intro h2
    grw [← Subtype.coe_lt_coe, ← le_quadraticUpper]
    exact hx.quadraticLower_lt_of_perfectField_of_leastNoRoots_lt perf h2

end

end Nimber
