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

theorem IsField.notMem_image_of_quadraticLower_le {x : Nimber} (hx : IsField x)
    {y : quadraticIrreducibles}
    (hy : enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x)) ≤ y) :
    y.1 ∉ (fun z => z ^ 2 - z) '' Iio x := by
  unfold quadraticLower quadraticAux at hy
  rw [← OrderIso.le_symm_apply, of_le_iff, ciSup_le_iff' Ordinal.bddAbove_of_small] at hy
  intro hyi
  exact (Order.lt_succ _).not_ge (hy ⟨y.1, y.2, hx.fieldClosure_eq.symm ▸ hyi⟩)

theorem IsField.leastNoRoots_lt_of_quadraticLower_lt
    {x : Nimber} (hx : IsField x)
    (hlt : enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x)) < x) :
    leastNoRoots x < .some (X ^ 3) := by
  by_contra! h2
  apply hx.notMem_image_of_quadraticLower_le le_rfl
  obtain ⟨r, hr, hrr⟩ := exists_root_of_lt_leastNoRoots
    (two_pos.trans_eq (.symm (by compute_degree!))).ne'
    (hx.coeff_sub_lt
      (hx.coeff_sub_lt (coeff_X_pow_lt 2 hx.one_lt) (coeff_X_lt hx.one_lt))
      (coeff_C_lt hlt))
    (lt_of_lt_of_le (WithTop.coe_lt_coe.2 (Lex.lt_X_pow_iff.2 (by compute_degree!))) h2)
  exact ⟨r, hr, by simpa [sub_eq_zero] using hrr⟩

mutual

theorem IsField.mem_image_of_lt_quadraticLower {x : Nimber} (hx : IsField x) {y : Nimber}
    (hy : y < enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x))) :
    y ∈ (fun z => z ^ 2 - z) '' Iio x := by
  sorry

theorem IsField.le_of_quadraticLower_le {x : Nimber} (hx : IsField x) {y : quadraticIrreducibles}
    (hy : enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x)) ≤ y)
    {z : Nimber} (hz : z < x) :
    y ≤ z ^ 2 - z - y := by
  sorry

theorem IsField.quadraticLower_fieldClosure_succ_of_not_perfectField {x : Nimber} (hx : IsField x)
    (perf : ¬PerfectField hx.toSubfield) :
    quadraticLower (fieldClosure (succ x)) = quadraticLower x := by
  rw [hx.perfectField_iff_leastNoRoots, not_le] at perf
  sorry

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
  · obtain ⟨r, hrx, hr⟩ :=
      ihc (lt_of_lt_of_le (hx.div_lt (hx.mul_lt hax hcx) (hx.mul_lt hbx hbx)) h2)
    refine ⟨r * (b / a), hx.mul_lt hrx (hx.div_lt hbx hax), ?_⟩
    rw [IsRoot.def, eval_add, eval_add, eval_C, eval_C_mul, eval_C_mul, eval_X_pow, eval_X,
      ← CharTwo.sub_eq_add, ← CharTwo.sub_eq_add]
    calc
      _ = _ := by field
      _ = _ := congr(b * b / a * $hr - c)
      _ = _ := by field

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
      apply hx.notMem_image_of_quadraticLower_le le_rfl
      rw [← hrr]
      exact Set.mem_image_of_mem (fun z => z ^ 2 - z) hr
  · apply hx.le_leastNoRoots_of_exists_isRoot
    rw [show X ^ 2 - X -
      C (enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x))).1 =
      C 1 * X ^ 2 + C 1 * X +
      C (enum quadraticIrreducibles isCofinal_quadraticIrreducibles (of (quadraticLower x))).1 by
        simp [CharTwo.sub_eq_add], Lex.forall_lt_quadratic]
    refine ⟨fun c hc _ _ => ?_, fun b hb c hd hc => ?_, fun a ha _ _ hd => ?_⟩
    · obtain ⟨r, hr, rfl⟩ := ihc hc
      refine ⟨r, hr, ?_⟩
      rw [IsRoot.def, eval_add, eval_add, map_one, one_mul, one_mul, eval_X_pow, eval_X, eval_C,
        CharTwo.add_eq_zero, ← CharTwo.sub_eq_add]
    · obtain rfl := lt_one_iff.1 hb
      exact ⟨√c, hx.sqrt_lt' (by simpa using hc 0) perf, by simp⟩
    · absurd hd.not_ge
      rw [lt_one_iff.1 ha]
      simp [degree_linear_le]

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
      apply hx.notMem_image_of_quadraticLower_le hlt.le
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
    apply (IsField.fieldClosure (succ x)).notMem_image_of_quadraticLower_le
      (OrderIso.monotone _ heq.ge)
    exact ⟨x, (lt_succ x).trans_le (le_fieldClosure (succ x)), hrt⟩

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

end

end

end Nimber
