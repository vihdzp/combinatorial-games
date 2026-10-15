/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import CombinatorialGames.Nimber.SimplestExtension.Algebraic

import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.PrimeField
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.SetTheory.Ordinal.Principal

/-!
# Inseparable nimber extensions

Let `t` be an algebraically closed nimber, and let `t(t)` denote the smallest nimber field
larger than `t`. Then the next few fields after `t(t)` are `t(t) ^ 2 ^ n` as `n` ranges over `ℕ`,
and these are all purely inseparable extensions over `t(t)` obtained by adjoining
the `2 ^ n`-th root of `t`. After these then `t(t) ^ ω` is a perfect field and so
all further extensions are too until the next algebraically closed nimber.
-/

universe u

public section

@[simp]
theorem RingEquiv.coe_subfieldCongr_apply {K : Type u} [DivisionRing K]
    {s t : Subfield K} (x : s) (h : s = t) : (RingEquiv.subfieldCongr h x : K) = (x : K) := rfl

instance {K : Type u} [Field K] : PerfectField (⊥ : Subfield K) := by
  obtain charzero | ⟨p, hp, charp⟩ := CharP.exists' K
  · infer_instance
  · -- todo: remove `Algebra (ZMod p) K` assumption from `Subfield.botEquivZMod`
    have := ZMod.algebra K p
    exact .of_ringEquiv (Subfield.botEquivZMod K p).symm

namespace Nimber.IsAlgClosed
open Order Polynomial Ordinal

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
      let e := (RatFunc.algEquivOfTranscendental t ht.transcendental).toRingEquiv.trans
        -- (.subfieldCongr ht.fieldAdjoin_simple_self)
        -- -- `IntermediateField.adjoin` shouldn't be exposed
        (@RingEquiv.subfieldCongr Nimber _ (IntermediateField.toSubfield _) _
          ht.fieldAdjoin_simple_self)
      let tt : hf.toSubfield := ⟨t, (lt_succ t).trans_le (le_fieldClosure (succ t))⟩
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
      have hrf : ((X ^ 2 + C tt).map e.symm).IsRoot (e.symm rr) := by
        apply IsRoot.map
        simpa [rr, Subtype.ext_iff] using hrr
      rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        IsRoot.def, eval_add, eval_X_pow, eval_C, CharTwo.add_eq_zero] at hrf
      apply_fun (Polynomial.idealX ht.toSubfield).valuation (RatFunc ht.toSubfield) at hrf
      apply_fun Even ∘ WithZero.log at hrf
      simp [herr] at hrf
  · exact (IsField.fieldClosure _).X_sq_add_C_le_leastNoRoots _ fun z hz ↦
      (ht.sqrt_lt hz).trans <| (lt_succ t).trans_le (le_fieldClosure (succ t))

theorem fieldClosure_succ_pow_two : fieldClosure (succ t) ^ 2 = t := by
  simpa [CharTwo.add_eq_zero] using
    (IsField.fieldClosure _).isRoot_leastNoRoots_of_eq ht.leastNoRoots_fieldClosure_succ

theorem sqrt_eq : Nimber.sqrt t = fieldClosure (succ t) := by
  rw [← Nimber.sqrt.eq_symm_apply, Nimber.sqrt_symm_apply, ht.fieldClosure_succ_pow_two]

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
    ∃ hc, ((leastNoRoots (of (val (fieldClosure (succ t)) ^ 2 ^ n))).untop hc).degree = 2 := by
  have ih (m : Nat) (hm : m + 1 = n) := leastNoRoots_fieldClosure_succ_pow_two_pow_succ m
  cases n with
  | zero =>
    rw! [pow_zero, pow_one, of_val, ht.leastNoRoots_fieldClosure_succ, WithTop.untop_coe]
    exact ⟨WithTop.coe_ne_top, degree_X_pow_add_C two_pos _⟩
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
          (Nat.pow_lt_pow_right one_lt_two (Nat.lt_add_one n))))
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
  have hf0td := degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux n
  have hp2 (m : Nat) (hm : m + 1 = n) := fieldClosure_succ_pow_two_pow_succ_pow_two m
  have hfm (m : Nat) (hm : m + 1 = n) := isField_fieldClosure_succ_pow_two_pow m
  have ih (m : Nat) (hm : m + 1 = n) := sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux m
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
      refine ⟨⟨fun x hx => ?_, pow_mem ?_ 2⟩, ?_⟩
      · grw [← Set.subset_union_left]
        rw [Set.mem_preimage, Nimber.sqrt_symm_apply, Subfield.closure_eq]
        exact pow_mem hx 2
      · apply Subfield.mem_closure_of_mem
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

theorem sqrt_fieldClosure_succ_pow_two_pow (n : Nat) :
    sqrt (of (val (fieldClosure (succ t)) ^ 2 ^ n)) =
      of (val (fieldClosure (succ t)) ^ 2 ^ (n + 1)) := by
  rw [← ht.fieldClosure_succ_pow_two_pow_succ_pow_two, Nimber.sqrt_sq]

theorem isField_fieldClosure_succ_pow_omega0 :
    IsField (of (val (fieldClosure (succ t)) ^ ω)) := by
  refine (congrArg IsField ?_).mp <| IsField.iSup ht.isField_fieldClosure_succ_pow_two_pow
  rw [← of.map_ciSup Ordinal.bddAbove_of_small, ← Ordinal.natCast_opow_omega0 one_lt_two]
  simp_rw [← opow_natCast, natCast_pow, ← opow_natCast, Nat.cast_ofNat]
  apply congrArg of
  let f (i : Ordinal) : Ordinal := val (fieldClosure (succ t)) ^ (2 : Ordinal) ^ i
  change ⨆ i : ℕ, f i = f ω
  apply Ordinal.apply_omega0_of_isNormal
  exact (Ordinal.isNormal_opow (one_lt_val.2 (IsField.fieldClosure _).one_lt)).comp
    (Ordinal.isNormal_opow one_lt_two)

theorem perfectField_fieldClosure_succ_pow_omega0 :
    PerfectField ht.isField_fieldClosure_succ_pow_omega0.toSubfield := by
  suffices _ : PerfectRing ht.isField_fieldClosure_succ_pow_omega0.toSubfield 2 from
    PerfectRing.toPerfectField _ 2
  constructor
  constructor
  · apply frobenius_inj
  intro ⟨x, hx⟩
  refine ⟨⟨x.sqrt, ?_⟩, by simp [Subtype.ext_iff]⟩
  rw [mem_toSubfield_iff, ← Ordinal.natCast_opow_omega0 one_lt_two] at hx ⊢
  have hN : IsNormal fun o : Ordinal =>
      of (val (fieldClosure (succ t)) ^ (Nat.cast 2 : Ordinal) ^ o) :=
    of.isNormal.comp
      ((Ordinal.isNormal_opow (one_lt_val.2 (IsField.fieldClosure _).one_lt)).comp
        (Ordinal.isNormal_opow one_lt_two))
  obtain ⟨n, hno, hn⟩ := (hN.lt_iff_exists_lt isSuccLimit_omega0).mp hx
  obtain ⟨n, rfl⟩ := lt_omega0.1 hno
  refine lt_trans ?_ (hN.strictMono (natCast_lt_omega0 (n + 1)))
  rw [Ordinal.opow_natCast, ← Ordinal.natCast_pow, Ordinal.opow_natCast] at hn ⊢
  rw [← mem_toSubfield_iff (ht.isField_fieldClosure_succ_pow_two_pow (n + 1)),
    ← ht.sqrt_map_fieldClosure_succ_pow_two_pow_succ, Subfield.mem_map]
  exact ⟨x, hn, rfl⟩

theorem not_perfectField_fieldClosure_succ_pow_two_pow (n : Nat) :
    ¬PerfectField (ht.isField_fieldClosure_succ_pow_two_pow n).toSubfield := by
  intro
  absurd bijective_frobenius (ht.isField_fieldClosure_succ_pow_two_pow n).toSubfield 2
  intro hbij
  cases n with
  | zero =>
    obtain ⟨c, hc⟩ := hbij.surjective ⟨t, by simp [← Order.succ_le_iff]⟩
    rw [frobenius_def, Subtype.ext_iff, SubmonoidClass.coe_pow, ← Nimber.sqrt_symm_apply,
      RingEquiv.symm_apply_eq, ht.sqrt_eq] at hc
    absurd c.2
    simp [hc]
  | succ n =>
    obtain ⟨c, hc⟩ := hbij.surjective ⟨of (val (fieldClosure (succ t)) ^ 2 ^ n),
      of.strictMono (pow_lt_pow_right₀ (one_lt_val.2 (IsField.fieldClosure _).one_lt)
        (Nat.pow_lt_pow_right one_lt_two (Nat.lt_add_one n)))⟩
    rw [frobenius_def, Subtype.ext_iff, SubmonoidClass.coe_pow, ← Nimber.sqrt_symm_apply,
      RingEquiv.symm_apply_eq, ht.sqrt_fieldClosure_succ_pow_two_pow] at hc
    absurd c.2
    simp [hc]

omit t ht in
theorem _root_.Nimber.IsField.not_perfectField_iff {x : Nimber} (hx : IsField x) :
   ¬PerfectField hx.toSubfield ↔ ∃ t, IsAlgClosed t ∧
      ∃ n, of (val (fieldClosure (succ t)) ^ 2 ^ n) = x := by
  constructor
  · intro h
    obtain halg | htr := lt_or_ge x (Nimber.algClosure 0)
    · absurd h
      let alg : Algebra (⊥ : Subfield Nimber) hx.toSubfield :=
        (Subfield.inclusion bot_le).toAlgebra
      have tower : IsScalarTower (⊥ : Subfield Nimber) hx.toSubfield Nimber :=
        ⟨fun _ _ _ => mul_assoc _ _ _⟩
      suffices algebraic : Algebra.IsAlgebraic (⊥ : Subfield Nimber) hx.toSubfield from
        algebraic.perfectField
      revert alg tower
      rw! [subfieldBot_eq, ← fieldClosure_zero]
      intro alg tower
      constructor
      intro c
      rw [← isAlgebraic_algebraMap_iff (A := Nimber)
          ((Subfield.algebraMap_ofSubfield hx.toSubfield).symm ▸ Subfield.subtype_injective _)]
      rw [Subfield.algebraMap_ofSubfield, Subfield.subtype_apply, ← lt_algClosure_iff_isAlgebraic]
      exact c.2.trans halg
    obtain ⟨t, ht, u, hu, htx, hxu, hbtwn⟩ := exists_isAlgClosed_between htr
    obtain hperf | hlt := le_or_gt (of (val (fieldClosure (succ t)) ^ ω)) x
    · absurd h
      let alg : Algebra ht.isField_fieldClosure_succ_pow_omega0.toSubfield hx.toSubfield :=
        (Subfield.inclusion ((IsField.toSubfield_le_toSubfield _ _).2 hperf)).toAlgebra
      have tower : IsScalarTower ht.isField_fieldClosure_succ_pow_omega0.toSubfield
          hx.toSubfield Nimber :=
        ⟨fun _ _ _ => mul_assoc _ _ _⟩
      suffices algebraic :
          Algebra.IsAlgebraic ht.isField_fieldClosure_succ_pow_omega0.toSubfield hx.toSubfield from
        have := ht.perfectField_fieldClosure_succ_pow_omega0
        algebraic.perfectField
      constructor
      intro c
      rw [← isAlgebraic_algebraMap_iff (A := Nimber)
          ((Subfield.algebraMap_ofSubfield hx.toSubfield).symm ▸ Subfield.subtype_injective _)]
      rw [Subfield.algebraMap_ofSubfield, Subfield.subtype_apply,
        ← ht.isField_fieldClosure_succ_pow_omega0.lt_algClosure_iff_isAlgebraic]
      refine (c.2.trans hxu).trans_le ?_
      refine hbtwn _ (IsAlgClosed.algClosure _) (lt_of_lt_of_le ?_ (le_algClosure _))
      rw [← Order.succ_le_iff, ← val_le_iff]
      exact (val.le_iff_le.2 <| le_fieldClosure _).trans (Ordinal.left_le_opow _ omega0_pos)
    · refine ⟨t, ht, ?_⟩
      rw [← natCast_opow_omega0 one_lt_two] at hlt
      have hN : IsNormal fun o : Ordinal =>
          of (val (fieldClosure (succ t)) ^ (Nat.cast 2 : Ordinal) ^ o) :=
        of.isNormal.comp
          ((Ordinal.isNormal_opow (one_lt_val.2 (IsField.fieldClosure _).one_lt)).comp
            (Ordinal.isNormal_opow one_lt_two))
      obtain ⟨n, hno, hn⟩ := (hN.lt_iff_exists_lt isSuccLimit_omega0).mp hlt
      obtain ⟨n, rfl⟩ := lt_omega0.1 hno
      clear hno
      rw [opow_natCast, ← natCast_pow, opow_natCast] at hn
      induction n with
      | zero =>
        rw [pow_zero, pow_one, of_val, hx.lt_fieldClosure_iff, lt_succ_iff] at hn
        absurd h
        obtain rfl := le_antisymm htx hn
        have := ht.isAlgClosed
        infer_instance
      | succ n ih =>
        obtain hb | hs := lt_or_ge x (of (val (fieldClosure (succ t)) ^ 2 ^ n))
        · exact ih hb
        refine ⟨n, le_antisymm hs ?_⟩
        rw [← lt_succ_iff, ← hx.lt_fieldClosure_iff]
        refine hn.trans_eq (Eq.symm ?_)
        rw [pow_succ, pow_mul]
        exact
          (ht.isField_fieldClosure_succ_pow_two_pow n).fieldClosure_succ_eq_pow_degree_leastNoRoots
            (ht.degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux n).1
            (ht.degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux n).2
  · rintro ⟨t, ht, n, rfl⟩
    exact ht.not_perfectField_fieldClosure_succ_pow_two_pow n

end Nimber.IsAlgClosed
