/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import CombinatorialGames.Nimber.SimplestExtension.Algebraic

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
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

-- #44989
open Ordinal in
@[simp]
theorem Ordinal.ofNat_opow_omega0 (n : ℕ) [n.AtLeastTwo] : ofNat(n) ^ ω = ω :=
  natCast_opow_omega0 Nat.AtLeastTwo.one_lt

namespace Subfield
variable {K L : Type*} [DivisionRing K] [DivisionRing L] (s : Subfield K)

/-- A subfield is isomorphic to its image under an injective function -/
@[expose]
noncomputable def equivMap (f : K →+* L) : s ≃+* s.map f :=
  s.toSubring.equivMapOfInjective f f.injective

@[simp]
theorem coe_equivMap_apply (f : K →+* L) (x : s) : (equivMap s f x : L) = f x :=
  rfl

end Subfield

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

theorem sqrt_eq : √t = fieldClosure (succ t) := by
  rw [← Nimber.sqrt.eq_symm_apply, Nimber.sqrt_symm_apply, ht.fieldClosure_succ_pow_two]

-- false positive due to the `mutual` block
-- see https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/unused.20variables.20linter.20false.20positive/near/631476579
set_option linter.unusedSectionVars false in
mutual

theorem isField_fieldClosure_succ_pow_two_pow (n : Nat) :
    IsField (of (val (fieldClosure (succ t)) ^ 2 ^ n)) := by
  have ih (m : Nat) (hm : m + 1 = n) := isField_fieldClosure_succ_pow_two_pow m
  have hdeg (m : Nat) (hm : m + 1 = n) := degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux m
  cases n with
  | zero =>
    rw [pow_zero, pow_one, of_val]
    exact IsField.fieldClosure (succ t)
  | succ n =>
    rw [pow_succ, pow_mul]
    exact (ih n rfl).pow_degree_leastNoRoots (hdeg n rfl).1 (hdeg n rfl).2
termination_by (n, 0)

private theorem degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux (n : Nat) :
    ∃ hc, ((leastNoRoots (of (val (fieldClosure (succ t)) ^ 2 ^ n))).untop hc).degree = 2 := by
  have hl (m : Nat) (hm : m + 1 = n) := leastNoRoots_fieldClosure_succ_pow_two_pow_succ m
  cases n with
  | zero =>
    rw [pow_zero, pow_one, of_val, ht.leastNoRoots_fieldClosure_succ]
    refine ⟨WithTop.coe_ne_top, ?_⟩
    rw [WithTop.untop_coe]
    compute_degree!
  | succ n =>
    rw [hl n rfl]
    refine ⟨WithTop.coe_ne_top, ?_⟩
    rw [WithTop.untop_coe]
    compute_degree!
termination_by (n, 5)
decreasing_by grind

theorem fieldClosure_succ_pow_two_pow_succ_pow_two (n : Nat) :
    of (val (fieldClosure (succ t)) ^ 2 ^ (n + 1)) ^ 2 =
      of (val (fieldClosure (succ t)) ^ 2 ^ n) := by
  obtain ⟨hf, perf⟩ := not_perfectField_fieldClosure_succ_pow_two_pow_aux (n + 1)
  have ih := sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux n
  apply le_antisymm
  · by_contra! hlt
    apply hf.sqrt_lt_of_not_perfectField perf at hlt
    rw [← Set.mem_Iio, ← ih, Nimber.sqrt.injective.mem_set_image, Set.mem_Iio] at hlt
    exact hlt.false
  · by_contra! hlt
    rw [← Set.mem_Iio, ← Nimber.sqrt.injective.mem_set_image, ih, Set.mem_Iio, sqrt_sq] at hlt
    exact hlt.false
termination_by (n + 1, 3)

theorem leastNoRoots_fieldClosure_succ_pow_two_pow_succ (n : Nat) :
    leastNoRoots (of (val (fieldClosure (succ t)) ^ 2 ^ (n + 1))) =
      .some (X ^ 2 + C (of (val (fieldClosure (succ t)) ^ 2 ^ n))) := by
  obtain ⟨hf, perf⟩ := not_perfectField_fieldClosure_succ_pow_two_pow_aux (n + 1)
  have hsq := fieldClosure_succ_pow_two_pow_succ_pow_two n
  rw [hf.leastNoRoots_eq_of_not_perfectField perf, hsq]
termination_by (n + 1, 4)

private theorem sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux (n : Nat) :
    Nimber.sqrt '' Set.Iio (of (val (fieldClosure (succ t)) ^ 2 ^ n)) =
      Set.Iio (of (val (fieldClosure (succ t)) ^ 2 ^ (n + 1))) := by
  obtain ⟨hf, perf⟩ := not_perfectField_fieldClosure_succ_pow_two_pow_aux n
  have hfp (m : Nat) (hm : m + 1 = n) := isField_fieldClosure_succ_pow_two_pow m
  have hd := degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux n
  have hdp (m : Nat) (hm : m + 1 = n) := degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux m
  have hs := hf.fieldClosure_succ_eq_pow_degree_leastNoRoots 2 hd
  have hsp (m : Nat) (hm : m + 1 = n) :=
    (hfp m hm).fieldClosure_succ_eq_pow_degree_leastNoRoots 2 (hdp m hm)
  have hsq (m : Nat) (hm : m + 1 = n) := fieldClosure_succ_pow_two_pow_succ_pow_two m
  have ih (m : Nat) (hm : m + 1 = n) := sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux m
  simp_rw [val_of] at hs hsp
  rw [pow_succ, pow_mul, ← hs, ← coe_toSubfield (IsField.fieldClosure _),
    ← hf.fieldAdjoin_simple_self, ← coe_toSubfield hf]
  apply subset_antisymm
  · rw [Set.image_subset_iff, ← sqrt.image_symm_eq_preimage, ← sqrt.symm.coe_toRingHom,
      ← Subfield.coe_map, IntermediateField.adjoin_toSubfield,
      /- this was impossible to find, todo: rename -/ RingHom.map_field_closure,
      Set.image_union, Set.image_singleton, Subfield.algebraMap_ofSubfield,
      ← RingHom.coe_fieldRange, Subfield.fieldRange_subtype, RingEquiv.coe_toRingHom]
    cases n with
    | zero =>
      rw! [pow_zero, pow_one, of_val]
      rw [← ht.fieldAdjoin_simple_self, IntermediateField.adjoin_toSubfield,
        Subfield.algebraMap_ofSubfield, ← RingHom.coe_fieldRange, Subfield.fieldRange_subtype,
        SetLike.coe_subset_coe, Subfield.closure_le, Set.union_subset_iff, Set.singleton_subset_iff]
      constructor
      · rw [SetLike.coe_subset_coe]
        intro x hx
        apply Subfield.mem_closure_of_mem
        apply Set.mem_union_left
        rw [sqrt.image_symm_eq_preimage, Set.mem_preimage, SetLike.mem_coe]
        apply Subfield.mem_closure_of_mem
        apply Set.mem_union_left
        exact ht.sqrt_lt hx
      · rw [SetLike.mem_coe]
        apply Subfield.mem_closure_of_mem
        simp [ht.fieldClosure_succ_pow_two]
    | succ n =>
      conv =>
        enter [2, 1, 1, 1]
        rw [coe_toSubfield, ← ih n rfl, ← Set.image_comp, ← RingEquiv.coe_trans,
          RingEquiv.self_trans_symm, RingEquiv.coe_refl, Set.image_id,
          ← coe_toSubfield (hfp n rfl)]
      rw [sqrt_symm_apply, hsq n rfl]
      rw! [pow_succ, pow_mul, ← hsp n rfl]
      rw [← (hfp n rfl).fieldAdjoin_simple_self, IntermediateField.adjoin_toSubfield,
        Subfield.algebraMap_ofSubfield, ← RingHom.coe_fieldRange, Subfield.fieldRange_subtype]
  · rw [/- todo: rename -/ IntermediateField.adjoin_toSubfield,
      ← RingEquiv.coe_toRingHom, ← Subfield.coe_map,
      SetLike.coe_subset_coe, Subfield.closure_le, Set.union_subset_iff,
      Set.singleton_subset_iff, Subfield.algebraMap_ofSubfield, ← RingHom.coe_fieldRange,
      Subfield.fieldRange_subtype, Subfield.coe_map, RingEquiv.coe_toRingHom,
      sqrt.image_eq_preimage_symm]
    constructor
    · intro x hx
      rw [Set.mem_preimage, SetLike.mem_coe, sqrt_symm_apply]
      rw [SetLike.mem_coe] at hx
      exact pow_mem hx 2
    · rw [Set.mem_preimage, sqrt_symm_apply, SetLike.mem_coe, mem_toSubfield_iff]
      exact hf.sq_lt_self_of_not_perfectField perf
termination_by (n + 1, 1)

private theorem not_perfectField_fieldClosure_succ_pow_two_pow_aux (n : Nat) :
    ∃ hf : IsField (of (val (fieldClosure (succ t)) ^ 2 ^ n)), ¬PerfectField hf.toSubfield := by
  have hf := isField_fieldClosure_succ_pow_two_pow n
  have hf' (m : Nat) (hm : m + 1 = n) := isField_fieldClosure_succ_pow_two_pow m
  have heq (m : Nat) (hm : m + 1 = n) := sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux m
  have ih (m : Nat) (hm : m + 1 = n) := not_perfectField_fieldClosure_succ_pow_two_pow_aux m
  refine ⟨hf, ?_⟩
  cases n with
  | zero =>
    rw [IsField.perfectField_iff_leastNoRoots, not_le, pow_zero, pow_one, of_val,
      ht.leastNoRoots_fieldClosure_succ, WithTop.coe_lt_coe]
    use 1; aesop
  | succ n =>
    let e : (hf' n rfl).toSubfield ≃+* hf.toSubfield :=
      ((hf' n rfl).toSubfield.equivMap Nimber.sqrt.toRingHom).trans
        (RingEquiv.subfieldCongr (SetLike.coe_injective (by simpa using heq n rfl)))
    intro perf
    apply (ih n rfl).2
    exact .of_ringEquiv e.symm
termination_by (n, 2)
decreasing_by all_goals grind

end

theorem sqrt_map_fieldClosure_succ_pow_two_pow_succ (n : Nat) :
    (ht.isField_fieldClosure_succ_pow_two_pow n).toSubfield.map Nimber.sqrt.toRingHom =
      (ht.isField_fieldClosure_succ_pow_two_pow (n + 1)).toSubfield :=
  SetLike.coe_injective (ht.sqrt_image_fieldClosure_succ_pow_two_pow_succ_aux n)

theorem not_perfectField_fieldClosure_succ_pow_two_pow (n : Nat) :
    ¬PerfectField (ht.isField_fieldClosure_succ_pow_two_pow n).toSubfield :=
  (ht.not_perfectField_fieldClosure_succ_pow_two_pow_aux n).2

theorem sqrt_fieldClosure_succ_pow_two_pow (n : Nat) :
    sqrt (of (val (fieldClosure (succ t)) ^ 2 ^ n)) =
      of (val (fieldClosure (succ t)) ^ 2 ^ (n + 1)) := by
  rw [← ht.fieldClosure_succ_pow_two_pow_succ_pow_two, Nimber.sqrt_sq]

omit ht in
private theorem isNormal_of_val_fieldClosure_succ_pow_two_pow : IsNormal fun o : Ordinal =>
    of (val (fieldClosure (succ t)) ^ (2 : Ordinal) ^ o) :=
  of.isNormal.comp <| ((isNormal_opow (one_lt_val.2 (IsField.fieldClosure _).one_lt)).comp
    (isNormal_opow one_lt_two))

/-- The next `ω` fields after an algebraically closed nimber `t` are `t(t) ^ 2 ^ n`. -/
theorem enumField_add_natCast_add_one {x : Ordinal} (hx : enumField x = t) (n : ℕ) :
    enumField (x + n + 1) = of (val (fieldClosure (succ t)) ^ 2 ^ n) := by
  induction n with
  | zero => simp [enumField_add_one, hx]
  | succ n IH =>
    rw [enumField_add_one, Nat.cast_add_one, ← add_assoc, IH,
      (isField_fieldClosure_succ_pow_two_pow ht n).fieldClosure_succ_eq_pow_degree_leastNoRoots 2
        (degree_leastNoRoots_fieldClosure_succ_pow_two_pow_aux ht n), val_of, ← pow_mul,
      Nat.pow_add_one]

-- todo: generalize from `fieldClosure (succ t)` to
-- arbitrary fields which are not algebraically closed
theorem enumField_add_omega0 {x : Ordinal} (hx : enumField x = t) :
    enumField (x + ω) = of (val (fieldClosure (succ t)) ^ ω) := by
  have hf : IsNormal fun o : Ordinal ↦ enumField (x + (1 + o)) := by
    simp_rw [← add_assoc]
    exact isNormal_enumField.comp (isNormal_add_right _)
  rw [← one_add_omega0, ← apply_omega0_of_isNormal hf]
  simp_rw [← Nat.cast_one_add, add_comm, Nat.cast_add_one, ← add_assoc,
    enumField_add_natCast_add_one ht hx, ← opow_natCast, natCast_pow, Nat.cast_ofNat,
    ← opow_natCast]
  rw [apply_omega0_of_isNormal isNormal_of_val_fieldClosure_succ_pow_two_pow, ofNat_opow_omega0,
    one_add_omega0]

-- todo: generalize from `fieldClosure (succ t)` to
-- arbitrary fields which are not algebraically closed
theorem isField_fieldClosure_succ_pow_omega0 :
    IsField (of (val (fieldClosure (succ t)) ^ ω)) := by
  obtain ⟨x, rfl⟩ := ht.mem_range_enumField
  rw [← enumField_add_omega0 ht rfl]
  exact IsField.enumField _

theorem exists_fieldClosure_succ_pow_two_pow_eq_of_isField_of_btwn {x : Nimber} (hx : IsField x)
    (htx : fieldClosure (succ t) ≤ x) (hxt : x < of (val (fieldClosure (succ t)) ^ ω)) :
    ∃ n, of (val (fieldClosure (succ t)) ^ 2 ^ n) = x := by
  obtain ⟨y, rfl⟩ := hx.mem_range_enumField
  obtain ⟨x, rfl⟩ := ht.mem_range_enumField
  rw [← enumField_add_one, enumField.le_iff_le, add_one_le_iff] at htx
  rw [← enumField_add_omega0 ht rfl, enumField.lt_iff_lt] at hxt
  simp_rw [← enumField_add_natCast_add_one ht rfl]
  obtain ⟨(_ | n), hn⟩ := lt_omega0.1 <| Ordinal.sub_lt_of_lt_add hxt omega0_pos
  · rw [Nat.cast_zero, Ordinal.sub_eq_zero_iff_le, ← not_lt] at hn
    contradiction
  use n
  rw [add_assoc, ← Nat.cast_add_one, ← hn, Ordinal.add_sub_cancel_of_le htx.le]

-- todo: generalize from `fieldClosure (succ t)` to
-- arbitrary fields which are not algebraically closed
theorem perfectField_fieldClosure_succ_pow_omega0 :
    PerfectField ht.isField_fieldClosure_succ_pow_omega0.toSubfield := by
  suffices _ : PerfectRing ht.isField_fieldClosure_succ_pow_omega0.toSubfield 2 from
    PerfectRing.toPerfectField _ 2
  refine .ofSurjective _ 2 ?_
  intro ⟨x, hx⟩
  refine ⟨⟨x.sqrt, ?_⟩, by simp [Subtype.ext_iff, frobenius_def]⟩
  rw [mem_toSubfield_iff, ← ofNat_opow_omega0 2] at hx ⊢
  obtain ⟨n, hno, hn⟩ :=
    ((isNormal_of_val_fieldClosure_succ_pow_two_pow).lt_iff_exists_lt
      isSuccLimit_omega0).mp hx
  obtain ⟨n, rfl⟩ := lt_omega0.1 hno
  refine lt_trans ?_ ((
    isNormal_of_val_fieldClosure_succ_pow_two_pow).strictMono (natCast_lt_omega0 (n + 1)))
  rw [opow_natCast, ← Nat.cast_ofNat, ← natCast_pow, opow_natCast] at hn ⊢
  rw [← mem_toSubfield_iff (ht.isField_fieldClosure_succ_pow_two_pow (n + 1)),
    ← ht.sqrt_map_fieldClosure_succ_pow_two_pow_succ, Subfield.mem_map]
  exact ⟨x, hn, rfl⟩

omit ht in
theorem _root_.Nimber.IsField.not_perfectField_iff {x : Nimber} (hx : IsField x) :
   ¬PerfectField hx.toSubfield ↔ ∃ t, IsAlgClosed t ∧
      ∃ n, of (val (fieldClosure (succ t)) ^ 2 ^ n) = x := by
  constructor
  · intro h
    obtain halg | htr := le_total x (Nimber.algClosure 0)
    · absurd h
      exact hx.perfectField_of_le_algClosure_zero halg
    obtain ⟨t, ht, u, hu, htx, hxu, hbtwn⟩ := exists_isAlgClosed_between htr
    obtain hperf | hlt := le_or_gt (of (val (fieldClosure (succ t)) ^ ω)) x
    · absurd h
      refine IsField.perfectField_of_btwn ht.isField_fieldClosure_succ_pow_omega0 hx
        ht.perfectField_fieldClosure_succ_pow_omega0 hperf (hxu.le.trans ?_)
      refine hbtwn _ (IsAlgClosed.algClosure _) (lt_of_lt_of_le ?_ (le_algClosure _))
      rw [← Order.succ_le_iff, ← val_le_iff]
      exact (val.le_iff_le.2 <| le_fieldClosure _).trans (left_le_opow _ omega0_pos)
    obtain htn | htp := lt_or_ge x (fieldClosure (succ t))
    · absurd h
      rw [hx.lt_fieldClosure_iff, lt_succ_iff] at htn
      rw! [← le_antisymm htx htn]
      exact ht.isAlgClosed.perfectField
    exact ⟨t, ht, ht.exists_fieldClosure_succ_pow_two_pow_eq_of_isField_of_btwn hx htp hlt⟩
  · rintro ⟨t, ht, n, rfl⟩
    exact ht.not_perfectField_fieldClosure_succ_pow_two_pow n

end Nimber.IsAlgClosed
