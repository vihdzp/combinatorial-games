/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import CombinatorialGames.Nimber.SimplestExtension.Algebraic

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Inseparable Nimber extensions

Let `t` be an algebraically closed nimber, and let `t(t)` denote the smallest nimber field
larger than `t`. Then the next few fields after `t(t)` are `t(t) ^ 2 ^ n` as `n` ranges over `ℕ`,
and these are all purely inseparable extensions over `t(t)` obtained by adjoining
the `2 ^ n`-th root of `t`. After these then `t(t) ^ ω` is a perfect field and so
all further extensions are too until the next algebraically closed nimber.

TODO: prove these are all of the inseparable nimber extensions
-/

universe u

public section

@[simp]
theorem RingEquiv.coe_subfieldCongr_apply {K : Type u} [DivisionRing K]
    {s t : Subfield K} (x : s) (h : s = t) : (RingEquiv.subfieldCongr h x : K) = (x : K) := rfl

namespace Nimber.IsAlgClosed
open Order Polynomial

variable {t : Nimber} (ht : IsAlgClosed t)
include ht

theorem leastNoRoots_fieldClosure_succ :
    leastNoRoots (fieldClosure (succ t)) = .some (X ^ 2 + C t) := by
  apply le_antisymm
  · apply leastNoRoots_le_of_not_isRoot
    · refine zero_lt_two.trans_eq (Eq.symm ?_)
      compute_degree!
    · apply (IsField.fieldClosure _).coeff_add_lt
      · exact coeff_X_pow_lt 2 (IsField.fieldClosure _).one_lt
      · exact coeff_C_lt ((lt_succ t).trans_le (le_fieldClosure (succ t)))
    · intro r hr hrr
      have hf := IsField.fieldClosure (succ t)
      let p : hf.toSubfield[X] :=
        X ^ 2 + C ⟨t, (lt_succ t).trans_le (le_fieldClosure (succ t))⟩
      let rr : hf.toSubfield := ⟨r, hr⟩
      have hrf : p.IsRoot rr := by simpa [p, rr, Subtype.ext_iff] using hrr
      set_option backward.isDefEq.respectTransparency false in
      let e := (RatFunc.algEquivOfTranscendental t ht.transcendental).toRingEquiv.trans
        -- (.subfieldCongr ht.fieldAdjoin_simple_self)
        -- -- `IntermediateField.adjoin` shouldn't be exposed
        (@RingEquiv.subfieldCongr Nimber _ (IntermediateField.toSubfield _) _
          ht.fieldAdjoin_simple_self)
      have hrf' : (p.map e.symm).IsRoot (e.symm rr) :=
        hrf.map -- `IsRoot.map` should take the ringhom explicity
      have herr : e.symm ⟨t, (lt_succ t).trans_le (le_fieldClosure (succ t))⟩ = .X := by
        rw [RingEquiv.symm_apply_eq]
        unfold e
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
      unfold p at hrf'
      rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        IsRoot.def, eval_add, eval_X_pow, eval_C, CharTwo.add_eq_zero] at hrf'
      apply_fun (Polynomial.idealX ht.toSubfield).valuation (RatFunc ht.toSubfield) at hrf'
      apply_fun WithZero.log at hrf'
      apply_fun Even at hrf'
      simp [herr] at hrf'
  · apply le_leastNoRoots_of_exists_isRoot
    rw [show X ^ 2 + C t = C 1 * X ^ 2 + C 0 * X + C t by simp, Lex.forall_lt_quadratic]
    refine ⟨fun c hc _ _ => ?_, fun _ => not_lt_zero.elim, fun a ha b c hd hc => ?_⟩
    · obtain ⟨r, hrt, hrr⟩ := ht.exists_root (Eq.trans_ne (by compute_degree!) two_ne_zero)
        (ht.coeff_add_lt (coeff_X_pow_lt 2 ht.one_lt) (coeff_C_lt hc))
      exact ⟨r, hrt.trans ((lt_succ t).trans_le (le_fieldClosure _)), by simpa using hrr⟩
    · rw [lt_one_iff.1 ha] at hd ⊢
      obtain rfl | hb := eq_or_ne b 0
      · absurd hd
        simpa using degree_C_le
      exact ⟨b⁻¹ * c, (IsField.fieldClosure _).mul_lt
        ((IsField.fieldClosure _).inv_lt (by simpa using hc 1)) (by simpa using hc 0),
        by simp [hb]⟩

theorem fieldClosure_succ_pow_two : fieldClosure (succ t) ^ 2 = t := by
  have hrt := (IsField.fieldClosure (succ t)).isRoot_leastNoRoots
    (by rw [ht.leastNoRoots_fieldClosure_succ]; simp)
  rw! [ht.leastNoRoots_fieldClosure_succ, WithTop.untop_coe, ← CharTwo.sub_eq_add] at hrt
  calc
    _ = _ := by simp
    _ = _ := congr(_ + $(IsRoot.def.1 hrt))
    _ = _ := add_zero _

set_option linter.unusedSectionVars false in
mutual

theorem isField_fieldClosure_succ_pow_two_pow (n : Nat) :
    IsField (of (val (fieldClosure (succ t)) ^ 2 ^ n)) := by
  have ih1 (m : Nat) (hm : m + 1 = n) := leastNoRoots_fieldClosure_succ_pow_two_pow_ne_top m
  have ih2 (m : Nat) (hm : m + 1 = n) := degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux m
  have ih3 (m : Nat) (hm : m + 1 = n) := isField_fieldClosure_succ_pow_two_pow m
  cases n with
  | zero =>
    rw [pow_zero, pow_one, of_val]
    exact IsField.fieldClosure (succ t)
  | succ n =>
    rw [pow_succ, pow_mul]
    exact (ih3 n rfl).pow_degree_leastNoRoots (ih1 n rfl) (ih2 n rfl (ih1 n rfl))
termination_by (n, 0)

theorem leastNoRoots_fieldClosure_succ_pow_two_pow_ne_top (n : Nat) :
    leastNoRoots (of (val (fieldClosure (succ t)) ^ 2 ^ n)) ≠ ⊤ := by
  have ih (m : Nat) (hm : m + 1 = n) := leastNoRoots_fieldClosure_succ_pow_two_pow_succ m
  cases n with
  | zero =>
    rw [pow_zero, pow_one, of_val, ht.leastNoRoots_fieldClosure_succ]
    simp
  | succ n =>
    rw [ih n rfl]
    simp
termination_by (n, 3)
decreasing_by grind

private theorem degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux (n : Nat)
    (hc : leastNoRoots (of (val (fieldClosure (succ t)) ^ 2 ^ n)) ≠ ⊤) :
    ((leastNoRoots (of (val (fieldClosure (succ t)) ^ 2 ^ n))).untop hc).degree = 2 := by
  have ih (m : Nat) (hm : m + 1 = n) := leastNoRoots_fieldClosure_succ_pow_two_pow_succ m
  cases n with
  | zero =>
    rw! [pow_zero, pow_one, of_val, ht.leastNoRoots_fieldClosure_succ, WithTop.untop_coe]
    compute_degree!
  | succ n =>
    rw! [ih n rfl, WithTop.untop_coe]
    compute_degree!
termination_by (n, 4)
decreasing_by grind

theorem leastNoRoots_fieldClosure_succ_pow_two_pow_succ (n : Nat) :
    leastNoRoots (of (val (fieldClosure (succ t)) ^ 2 ^ (n + 1))) =
      .some (X ^ 2 + C (of (val (fieldClosure (succ t)) ^ 2 ^ n))) := by
  have hf := isField_fieldClosure_succ_pow_two_pow (n + 1)
  have him := sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux n
  apply le_antisymm
  · apply leastNoRoots_le_of_not_isRoot
    · refine zero_lt_two.trans_eq (Eq.symm ?_)
      compute_degree!
    · apply hf.coeff_add_lt
      · exact coeff_X_pow_lt 2 hf.one_lt
      · exact coeff_C_lt (of.strictMono (pow_lt_pow_right₀
          (one_lt_val.2 (IsField.fieldClosure _).one_lt)
          (Nat.pow_lt_pow_right (by decide) (Nat.lt_add_one n))))
    · intro r hr hrr
      rw [IsRoot.def, eval_add, eval_X_pow, eval_C, CharTwo.add_eq_zero] at hrr
      rw [← Set.mem_Iio, ← him, ← RingEquiv.coe_toEquiv, Set.mem_image_equiv,
        ← RingEquiv.coe_toEquiv_symm, RingEquiv.coe_toEquiv, Nimber.sqrt_symm_apply, hrr,
        Set.mem_Iio] at hr
      exact hr.false
  · apply le_leastNoRoots_of_exists_isRoot
    rw [show X ^ 2 + C (of (val (succ t).fieldClosure ^ 2 ^ n)) =
      C 1 * X ^ 2 + C 0 * X + C (of (val (succ t).fieldClosure ^ 2 ^ n)) by simp,
      Lex.forall_lt_quadratic]
    refine ⟨fun c hc _ _ => ?_, fun _ => not_lt_zero.elim, fun a ha b c hd hc => ?_⟩
    · refine ⟨c.sqrt, ?_, by simp⟩
      rw [← Set.mem_Iio, ← him]
      exact Set.mem_image_of_mem Nimber.sqrt hc
    · rw [lt_one_iff.1 ha] at hd ⊢
      obtain rfl | hb := eq_or_ne b 0
      · absurd hd
        simpa using degree_C_le
      exact ⟨b⁻¹ * c, hf.mul_lt (hf.inv_lt (by simpa using hc 1)) (by simpa using hc 0),
        by simp [hb]⟩
termination_by (n + 1, 2)

theorem fieldClosure_succ_pow_two_pow_succ_pow_two (n : Nat) :
    of (val (fieldClosure (succ t)) ^ 2 ^ (n + 1)) ^ 2 =
      of (val (fieldClosure (succ t)) ^ 2 ^ n) := by
  have hf := isField_fieldClosure_succ_pow_two_pow (n + 1)
  have hnt := leastNoRoots_fieldClosure_succ_pow_two_pow_ne_top (n + 1)
  have ih := leastNoRoots_fieldClosure_succ_pow_two_pow_succ n
  have hrt := hf.isRoot_leastNoRoots hnt
  rw! [ih, WithTop.untop_coe, ← CharTwo.sub_eq_add] at hrt
  calc
    _ = _ := by simp
    _ = _ := congr(_ + $(IsRoot.def.1 hrt))
    _ = _ := add_zero _
termination_by (n + 1, 4)

private theorem sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux (n : Nat) :
    Nimber.sqrt '' Set.Iio (of (val (fieldClosure (succ t)) ^ 2 ^ n)) =
      Set.Iio (of (val (fieldClosure (succ t)) ^ 2 ^ (n + 1))) := by
  have hf0 := isField_fieldClosure_succ_pow_two_pow n
  have hf1 := isField_fieldClosure_succ_pow_two_pow (n + 1)
  have hf0t := leastNoRoots_fieldClosure_succ_pow_two_pow_ne_top n
  have hf0d := degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux n hf0t
  have hp2 (m : Nat) (hm : m + 1 = n) := fieldClosure_succ_pow_two_pow_succ_pow_two m
  have hfm (m : Nat) (hm : m + 1 = n) := isField_fieldClosure_succ_pow_two_pow m
  have ih (m : Nat) (hm : m + 1 = n) := sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux m
  have hf1t (m : Nat) (hm : m + 1 = n) := leastNoRoots_fieldClosure_succ_pow_two_pow_ne_top m
  have hf1d (m : Nat) (hm : m + 1 = n) :=
    degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux m (hf1t m hm)
  rw [pow_succ, pow_mul] at hf1 ⊢
  rw [← coe_toSubfield hf0, ← coe_toSubfield hf1, ← RingEquiv.coe_toRingHom,
    ← Subfield.coe_map, SetLike.coe_injective.eq_iff]
  erw [hf0.pow_degree_leastNoRoots_eq_adjoin hf0t hf0d]
  apply le_antisymm
  · cases n with
    | zero =>
      revert hf0
      rw [pow_zero, pow_one, of_val]
      intro hf0
      rw [← ht.fieldAdjoin_simple_self, Subfield.map_le_iff_le_comap,
        IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield,
        Subfield.algebraMap_ofSubfield, Subfield.algebraMap_ofSubfield,
        ← RingHom.coe_fieldRange, Subfield.fieldRange_subtype,
        ← RingHom.coe_fieldRange, Subfield.fieldRange_subtype]
      grw [← Subfield.closure_preimage_le]
      rw [Set.preimage_union, RingEquiv.coe_toRingHom,
        ← RingEquiv.image_symm_eq_preimage, ← RingEquiv.image_symm_eq_preimage,
        Set.image_singleton, Nimber.sqrt_symm_apply, ← RingEquiv.coe_toRingHom,
        ← Subfield.coe_map, ht.fieldClosure_succ_pow_two]
      gcongr
      -- this was impossible to find
      -- todo: fix names
      rw [RingHom.map_field_closure]
      rw [Set.image_union, ← SetLike.coe_subset_coe]
      refine subset_trans ?_ (Set.subset_union_left.trans Subfield.subset_closure)
      rw [RingEquiv.coe_toRingHom, RingEquiv.image_symm_eq_preimage, coe_toSubfield]
      intro x hx
      apply ht.sqrt_lt hx
      rw [ht.leastNoRoots_eq_top]
      simp
    | succ n =>
      specialize hp2 n rfl
      revert hf0
      rw [pow_succ 2, pow_mul] at hp2 ⊢
      intro hf0
      erw [(hfm n rfl).pow_degree_leastNoRoots_eq_adjoin (hf1t n rfl) (hf1d n rfl)]
      rw [Subfield.map_le_iff_le_comap,
        IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield,
        Subfield.algebraMap_ofSubfield, Subfield.algebraMap_ofSubfield,
        ← RingHom.coe_fieldRange, Subfield.fieldRange_subtype,
        ← RingHom.coe_fieldRange, Subfield.fieldRange_subtype]
      grw [← Subfield.closure_preimage_le]
      rw [Set.preimage_union, RingEquiv.coe_toRingHom,
        ← RingEquiv.image_symm_eq_preimage, ← RingEquiv.image_symm_eq_preimage,
        Set.image_singleton, Nimber.sqrt_symm_apply, ← RingEquiv.coe_toRingHom,
        ← Subfield.coe_map, hp2]
      gcongr
      -- this was impossible to find
      -- todo: fix names
      rw [← SetLike.coe_subset_coe, Subfield.coe_map, RingEquiv.coe_toRingHom,
        RingEquiv.image_symm_eq_preimage, ← Set.image_subset_iff, coe_toSubfield,
        ih n rfl, pow_succ, pow_mul, ← coe_toSubfield hf0, ← coe_toSubfield (hfm n rfl),
        ← Subfield.fieldRange_subtype (hfm n rfl).toSubfield, RingHom.coe_fieldRange,
        ← Subfield.algebraMap_ofSubfield, ← IntermediateField.adjoin_toSubfield,
        ← (hfm n rfl).pow_degree_leastNoRoots_eq_adjoin (hf1t n rfl) (hf1d n rfl),
        coe_toSubfield, coe_toSubfield, val_of]
  · rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le, Set.union_subset_iff,
      Set.singleton_subset_iff, Subfield.algebraMap_ofSubfield, ← RingHom.coe_fieldRange,
      Subfield.coe_map, RingEquiv.coe_toRingHom, RingEquiv.image_eq_preimage_symm,
      ← RingEquiv.coe_toRingHom, Set.mem_preimage, RingEquiv.coe_toRingHom, Nimber.sqrt_symm_apply,
      Subfield.fieldRange_subtype]
    constructor
    · intro x hx
      rw [Set.mem_preimage, Nimber.sqrt_symm_apply]
      exact pow_mem hx 2
    · cases n with
      | zero =>
        revert hf0
        rw [pow_zero, pow_one, of_val, ht.fieldClosure_succ_pow_two]
        intro hf0
        rw [SetLike.mem_coe, mem_toSubfield_iff, ← Order.succ_le_iff]
        exact le_fieldClosure (succ t)
      | succ n =>
        rw [hp2 n rfl]
        rw [SetLike.mem_coe, mem_toSubfield_iff, of.lt_iff_lt, pow_succ, pow_mul]
        apply lt_self_pow₀
        · refine Ordinal.one_lt_pow.2 ⟨?_, (Nat.pow_pos Nat.two_pos).ne'⟩
          exact one_lt_val.2 (IsField.fieldClosure (succ t)).one_lt
        · simp
termination_by (n + 1, 1)

end

theorem degree_leastNoRoots_fieldClosure_succ_pow_two_pow (n : Nat) :
    ((leastNoRoots (of (val (fieldClosure (succ t)) ^ 2 ^ n))).untop
      (ht.leastNoRoots_fieldClosure_succ_pow_two_pow_ne_top n)).degree = 2 :=
  ht.degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux n
    (ht.leastNoRoots_fieldClosure_succ_pow_two_pow_ne_top n)

theorem sqrt_map_fieldClosure_succ_pow_two_pow_succ (n : Nat) :
    (ht.isField_fieldClosure_succ_pow_two_pow n).toSubfield.map Nimber.sqrt.toRingHom =
      (ht.isField_fieldClosure_succ_pow_two_pow (n + 1)).toSubfield :=
  SetLike.coe_injective (ht.sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux n)

end Nimber.IsAlgClosed
