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
# Inseparable nimber extensions

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
    · simp [degree_X_pow_add_C]
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
      apply_fun Even ∘ WithZero.log at hrf'
      simp [herr] at hrf'
  · exact (IsField.fieldClosure _).X_sq_add_C_le_leastNoRoots _ fun z hz ↦
      (ht.sqrt_lt hz).trans <| (lt_succ t).trans_le (le_fieldClosure (succ t))

theorem fieldClosure_succ_pow_two : fieldClosure (succ t) ^ 2 = t := by
  simpa [CharTwo.add_eq_zero] using
    (IsField.fieldClosure _).isRoot_leastNoRoots_of_eq ht.leastNoRoots_fieldClosure_succ

-- false positive due to the `mutual` block
-- see https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/unused.20variables.20linter.20false.20positive/near/631476579
set_option linter.unusedSectionVars false in
mutual

theorem isField_fieldClosure_succ_pow_two_pow (n : Nat) :
    IsField (of (val (fieldClosure (succ t)) ^ 2 ^ n)) := by
  have ih12 (m : Nat) (hm : m + 1 = n) := degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux m
  have ih3 (m : Nat) (hm : m + 1 = n) := isField_fieldClosure_succ_pow_two_pow m
  cases n with
  | zero =>
    rw [pow_zero, pow_one, of_val]
    exact IsField.fieldClosure (succ t)
  | succ n =>
    rw [pow_succ, pow_mul]
    exact (ih3 n rfl).pow_degree_leastNoRoots (ih12 n rfl).1 (ih12 n rfl).2
termination_by (n, 0)

private theorem degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux (n : Nat) :
    ∃ (hc : leastNoRoots (of (val (fieldClosure (succ t)) ^ 2 ^ n)) ≠ ⊤),
    ((leastNoRoots (of (val (fieldClosure (succ t)) ^ 2 ^ n))).untop hc).degree = 2 := by
  have ih (m : Nat) (hm : m + 1 = n) := leastNoRoots_fieldClosure_succ_pow_two_pow_succ m
  cases n with
  | zero =>
    rw! [pow_zero, pow_one, of_val, ht.leastNoRoots_fieldClosure_succ, WithTop.untop_coe]
    exact ⟨by simp, by compute_degree!⟩
  | succ n =>
    rw! [ih n rfl, WithTop.untop_coe]
    exact ⟨by simp, by compute_degree!⟩
termination_by (n, 3)
decreasing_by grind

theorem leastNoRoots_fieldClosure_succ_pow_two_pow_succ (n : Nat) :
    leastNoRoots (of (val (fieldClosure (succ t)) ^ 2 ^ (n + 1))) =
      .some (X ^ 2 + C (of (val (fieldClosure (succ t)) ^ 2 ^ n))) := by
  have hf := isField_fieldClosure_succ_pow_two_pow (n + 1)
  have him := sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux n
  apply le_antisymm
  · apply leastNoRoots_le_of_not_isRoot
    · simp [degree_X_pow_add_C]
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
  · refine hf.X_sq_add_C_le_leastNoRoots _ fun z hz ↦ ?_
    rw [← Set.mem_Iio, ← him]
    exact Set.mem_image_of_mem Nimber.sqrt hz
termination_by (n + 1, 2)

theorem fieldClosure_succ_pow_two_pow_succ_pow_two (n : Nat) :
    of (val (fieldClosure (succ t)) ^ 2 ^ (n + 1)) ^ 2 =
      of (val (fieldClosure (succ t)) ^ 2 ^ n) := by
  have hf := isField_fieldClosure_succ_pow_two_pow (n + 1)
  have ih := leastNoRoots_fieldClosure_succ_pow_two_pow_succ n
  simpa [CharTwo.add_eq_zero] using hf.isRoot_leastNoRoots_of_eq ih
termination_by (n + 1, 3)

private theorem sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux (n : Nat) :
    Nimber.sqrt '' Set.Iio (of (val (fieldClosure (succ t)) ^ 2 ^ n)) =
      Set.Iio (of (val (fieldClosure (succ t)) ^ 2 ^ (n + 1))) := by
  have hf0 := isField_fieldClosure_succ_pow_two_pow n
  have hf1 := isField_fieldClosure_succ_pow_two_pow (n + 1)
  -- have hf0t := leastNoRoots_fieldClosure_succ_pow_two_pow_ne_top n
  have hf0td := degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux n
  have hp2 (m : Nat) (hm : m + 1 = n) := fieldClosure_succ_pow_two_pow_succ_pow_two m
  have hfm (m : Nat) (hm : m + 1 = n) := isField_fieldClosure_succ_pow_two_pow m
  have ih (m : Nat) (hm : m + 1 = n) := sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux m
  -- have hf1t (m : Nat) (hm : m + 1 = n) := leastNoRoots_fieldClosure_succ_pow_two_pow_ne_top m
  have hf1td (m : Nat) (hm : m + 1 = n) := degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux m
  rw [pow_succ, pow_mul] at hf1 ⊢
  rw [← coe_toSubfield hf0, ← coe_toSubfield hf1, ← RingEquiv.coe_toRingHom,
    ← Subfield.coe_map, SetLike.coe_set_eq]
  erw [hf0.pow_degree_leastNoRoots_eq_adjoin hf0td.1 hf0td.2]
  rw [← SetLike.coe_set_eq, Subfield.coe_map, RingEquiv.coe_toRingHom,
    ← RingEquiv.coe_toEquiv, ← Equiv.eq_preimage_iff_image_eq, RingEquiv.coe_toEquiv,
    ← RingEquiv.image_symm_eq_preimage, ← RingEquiv.coe_toRingHom, ← Subfield.coe_map,
    IntermediateField.adjoin_toSubfield, Subfield.algebraMap_ofSubfield,
    ← RingHom.coe_fieldRange, Subfield.fieldRange_subtype, coe_toSubfield,
    /- this was impossible to find
      todo: fix names -/ RingHom.map_field_closure,
    Set.image_union, Set.image_singleton,
    RingEquiv.coe_toRingHom, Nimber.sqrt_symm_apply]
  cases n with
  | zero =>
    rw [pow_zero, pow_one, of_val] at hf0 ⊢
    rw [ht.fieldClosure_succ_pow_two, ← coe_toSubfield hf0, ← ht.fieldAdjoin_simple_self,
      IntermediateField.adjoin_toSubfield, SetLike.coe_set_eq, Subfield.algebraMap_ofSubfield,
      ← RingHom.coe_fieldRange, Subfield.fieldRange_subtype, ← RingEquiv.coe_toRingHom,
      ← Subfield.coe_map,
      /- this was impossible to find
        todo: fix names -/ RingHom.map_field_closure,
      Set.image_union, Set.image_singleton, RingEquiv.coe_toRingHom, Nimber.sqrt_symm_apply]
    apply le_antisymm
    · gcongr
      grw [← Set.subset_union_left]
      intro x hx
      exact Subfield.mem_closure_of_mem ⟨x.sqrt, ht.sqrt_lt hx, by simp⟩
    · rw [Subfield.closure_le, Set.union_subset_iff, SetLike.coe_subset_coe,
        Subfield.closure_le, Set.union_subset_iff, Set.singleton_subset_iff,
        Set.singleton_subset_iff, Set.image_subset_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro x hx
        grw [← Set.subset_union_left]
        rw [Set.mem_preimage, Nimber.sqrt_symm_apply, Subfield.closure_eq]
        exact pow_mem hx 2
      · refine pow_mem (Subfield.mem_closure_of_mem ?_) 2
        simp
      · apply Subfield.mem_closure_of_mem
        simp
  | succ n =>
    specialize ih n rfl
    specialize hfm n rfl
    rw [← RingEquiv.coe_toEquiv, ← Equiv.eq_preimage_iff_image_eq,
      RingEquiv.coe_toEquiv, ← RingEquiv.image_symm_eq_preimage] at ih
    rw [← ih, hp2 n rfl]
    rw [pow_succ, pow_mul] at hf0 ⊢
    rw [← coe_toSubfield hfm, ← hfm.toSubfield.fieldRange_subtype,
      RingHom.coe_fieldRange, ← Subfield.algebraMap_ofSubfield,
      ← IntermediateField.adjoin_toSubfield, ← coe_toSubfield hf0, SetLike.coe_set_eq]
    exact hfm.pow_degree_leastNoRoots_eq_adjoin (hf1td n rfl).1 (hf1td n rfl).2
termination_by (n + 1, 1)

end

theorem sqrt_map_fieldClosure_succ_pow_two_pow_succ (n : Nat) :
    (ht.isField_fieldClosure_succ_pow_two_pow n).toSubfield.map Nimber.sqrt.toRingHom =
      (ht.isField_fieldClosure_succ_pow_two_pow (n + 1)).toSubfield :=
  SetLike.coe_injective (ht.sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux n)

end Nimber.IsAlgClosed
