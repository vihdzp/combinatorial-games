/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Algebra.Polynomial.PartialFractions
import CombinatorialGames.Nimber.SimplestExtension.Algebraic

universe u

theorem Ordinal.opow_eq_one_iff {a b : Ordinal} : a ^ b = 1 ↔ a = 1 ∨ b = 0 := by
  refine ⟨fun h => ?_, by simp +contextual [or_imp]⟩
  contrapose! h
  by_cases ha : a = 0
  · simp [ha, h.2]
  apply ne_of_gt
  have h1a : 1 < a := lt_of_not_ge (by simp [le_one_iff, ha, h.1])
  rw [← opow_zero a, opow_lt_opow_iff_right h1a]
  exact pos_of_ne_zero h.2

theorem Ordinal.exists_omega0_mul_add_natCast (o : Ordinal) :
    ∃ a b, omega0 * a + Nat.cast b = o := by
  obtain ⟨b, hb⟩ := lt_omega0.1 (mod_lt o omega0_ne_zero)
  refine ⟨o / omega0, b, ?_⟩
  rw [← hb, div_add_mod]

theorem Ordinal.one_le_of_lt {a b : Ordinal} (hab : a < b) : 1 ≤ b := by
  rw [← zero_add 1, ← Order.succ_eq_add_one, Order.succ_le_iff]
  exact (zero_le a).trans_lt hab

theorem Order.IsNormal.isBot_or_exists_le_succ_of_lt {α β : Type*} [LinearOrder α] [SuccOrder α]
    [LinearOrder β] {f : α → β} (hf : IsNormal f) {a : α} {b : β} (h : b < f a) :
    IsBot a ∨ ∃ c < a, b < f (succ c) := by
  cases a using Order.isSuccLimitRecOn with
  | isMin a ha => exact .inl ha.isBot
  | succ a ha => exact .inr ⟨a, lt_succ_of_not_isMax ha, h⟩
  | isSuccLimit a ha =>
    obtain ⟨c, hca, hc⟩ := (hf.lt_iff_exists_lt ha).1 h
    exact .inr ⟨c, hca, hc.trans_le (hf.monotone (le_succ c))⟩

noncomputable section

open Ordinal Polynomial
namespace Nimber.IsAlgClosed

variable {t : Nimber.{u}} (ht : IsAlgClosed t)
include ht

theorem isRing_pow_omega0 : IsRing (of (val t ^ ω)) := by
  refine ⟨ht.opow _, fun y z hy hz ↦ ?_, ne_of_gt (by simp [ht.one_lt])⟩
  obtain ⟨py, hyd, rfl⟩ := eq_oeval_of_lt_opow_omega0 hy
  obtain ⟨pz, hzd, rfl⟩ := eq_oeval_of_lt_opow_omega0 hz
  rw [← ht.eval_eq_of_lt hyd, ← ht.eval_eq_of_lt hzd, ← eval_mul, ht.eval_eq_of_lt]
  on_goal 1 => apply oeval_lt_opow_omega0
  all_goals exact forall_coeff_mul_lt ht.toIsRing hyd hzd

-- not an instance because `ht` is not inferrable
abbrev algebraPowOmega0 : Algebra ht.toIsField.toSubfield ht.isRing_pow_omega0.toSubring :=
  (Subring.inclusion (Set.Iio_subset_Iio (val_le_iff.1 (left_le_opow _ omega0_pos)))).toAlgebra

theorem algebraPowOmega0ScalarTower :
    letI := ht.algebraPowOmega0
    IsScalarTower ht.toIsField.toSubfield ht.isRing_pow_omega0.toSubring Nimber :=
  @IsScalarTower.mk _ _ _ (_) _ _ fun _ _ _ => mul_assoc _ _ _

def algEquivPolynomial :
    letI := ht.algebraPowOmega0
    ht.isRing_pow_omega0.toSubring ≃ₐ[ht.toIsField.toSubfield]
    ht.toIsField.toSubfield[X] :=
  letI := ht.algebraPowOmega0
  .symm <| .ofBijective (aeval
      ⟨t, val_lt_iff.1 (left_lt_opow ht.one_lt one_lt_omega0)⟩) <| by
    have algMap (x : ht.toIsField.toSubfield) :
        algebraMap ht.toIsField.toSubfield ht.isRing_pow_omega0.toSubring x = ⟨x, _⟩ := rfl
    refine ⟨fun p q hpq => ?_, ?_⟩
    · rw [aeval_def, aeval_def, eval₂_eq_eval_map, eval₂_eq_eval_map,
        ← ht.isRing_pow_omega0.toSubring.subtype_injective.eq_iff,
        ← eval_map_apply, ← eval_map_apply, Subring.subtype_apply,
        ht.eval_eq_of_lt (by simp [algMap]), ht.eval_eq_of_lt (by simp [algMap]),
        oeval_eq_oeval_iff (by simp [algMap]) (by simp [algMap]),
        (map_injective _ (Subring.subtype_injective _)).eq_iff] at hpq
      refine map_injective _ ?_ hpq
      exact fun _ _ h => by simpa [algMap] using h
    · intro y
      obtain ⟨y, hy⟩ := y
      obtain ⟨py, hyd, rfl⟩ := eq_oeval_of_lt_opow_omega0 hy
      refine ⟨ht.toIsField.embed py hyd, ?_⟩
      rw [aeval_def, eval₂_eq_eval_map, ← ht.isRing_pow_omega0.toSubring.subtype_injective.eq_iff,
        ← eval_map_apply, map_map]
      change eval t (map ht.toIsField.toSubfield.subtype (ht.toIsField.embed py hyd)) = oeval t py
      rw [ht.toIsField.map_embed, ht.eval_eq_of_lt hyd]

theorem coe_algEquivPolynomial_symm_apply (p : ht.toIsField.toSubfield[X]) :
    letI := ht.algebraPowOmega0
    (ht.algEquivPolynomial.symm p : Nimber) = p.eval₂ ht.toIsField.toSubfield.subtype t := by
  unfold algEquivPolynomial
  rw [← ht.isRing_pow_omega0.toSubring.subtype_apply,
    @AlgEquiv.symm_symm, @AlgEquiv.ofBijective_apply,
    @aeval_def, ← eval_map, ← eval_map_apply, map_map, eval_map]
  rfl

def ringEquivPolynomial : ht.isRing_pow_omega0.toSubring ≃+* ht.toIsField.toSubfield[X] :=
  letI := ht.algebraPowOmega0
  ht.algEquivPolynomial.toRingEquiv

theorem coe_ringEquivPolynomial_symm_apply (p : ht.toIsField.toSubfield[X]) :
    (ht.ringEquivPolynomial.symm p : Nimber) = p.eval₂ ht.toIsField.toSubfield.subtype t :=
  ht.coe_algEquivPolynomial_symm_apply p

private theorem subring_aux {x : Nimber} (hx : IsRing (∗(val t ^ (ω * (1 + val x))))) :
    ht.isRing_pow_omega0.toSubring ≤ hx.toSubring :=
  Set.Iio_subset_Iio (of.monotone (Ordinal.opow_le_opow_right
    (val_zero.symm.trans_lt (val.strictMono ht.zero_lt)) (by simp)))

private theorem next_field_aux {x : Nimber} (hx : x < t) (n : ℕ) :
    ∗(val t ^ (ω * (1 + val x) + n)) = ((t - x) ^ (n + 1))⁻¹ ∧
      ∃ rx : IsRing (∗(val t ^ (ω * (1 + val x)))),
        letI : Algebra ht.isRing_pow_omega0.toSubring rx.toSubring :=
          (Subring.inclusion (subring_aux ht rx)).toAlgebra
        IsLocalization (Submonoid.comap ht.ringEquivPolynomial.toMonoidHom
          (Submonoid.closure ((fun u => X - C u) '' Set.Iio ⟨x, hx⟩)))
          rx.toSubring := by
  have normal : Order.IsNormal fun x => ∗(val t ^ (ω * (1 + val x))) :=
    of.isNormal.comp ((isNormal_opow (one_lt_val.2 ht.one_lt)).comp
      ((isNormal_mul_right omega0_pos).comp (isNormal_add_right 1)))
  induction x using WellFoundedLT.induction generalizing n with | ind x ihx
  -- have to generalize to lex(c, o) < lex(x, n)
  have surj (c : Nimber) (hcx : c < x) (o : Nat) (y : Nimber)
      (hyc : y < ∗(val t ^ (ω * (1 + val c) + o))) :
      ∃ m : Multiset Nimber, (∀ i ∈ m, i < c) ∧
      ∃ p : Nimber, p < ∗(val t ^ ω) ∧ p / ((m.map fun c => t - c).prod * (t - c) ^ o) = y := by
    obtain ⟨f, hs, hf⟩ := ht.toIsField.exists_linearCombination_of_lt hyc
    obtain ⟨e, hes, he⟩ : ∃ s : Nat →₀ ht.toIsField.toSubfield, s.support ⊆ Finset.Iio o ∧
        (f.filter (¬· < ω * (1 + val c))).sum (fun i a => a • of (val t ^ i)) =
        s.sum (fun i a => a • of (val t ^ (ω * (1 + val c) + i))) := by
      have hl (i : Ordinal) : ∃ l : ℕ,
          i ∈ (f.filter (¬· < ω * (1 + val c))).support → ω * (1 + val c) + l = i := by
        by_cases hi : i ∈ f.support
        · obtain ⟨l, hl⟩ := Ordinal.lt_omega0.1 (Ordinal.sub_lt_of_lt_add ((hs hi).trans
            (add_lt_add_right (nat_lt_omega0 o) _)) (by simp))
          refine ⟨l, fun h => ?_⟩
          rw [Finsupp.support_filter, Finset.mem_filter] at h
          rw [← hl, Ordinal.add_sub_cancel_of_le (le_of_not_gt h.2)]
        · simp [hi]
      choose l hl using hl
      refine ⟨(f.filter (¬· < ω * (1 + val c))).mapDomain l, ?_⟩
      rw [Finsupp.sum_filter_index, Finsupp.sum_mapDomain_index (by simp) (by simp [← add_smul]),
        Finsupp.sum_filter_index]
      refine ⟨Finsupp.mapDomain_support.trans fun i hi => Finset.mem_Iio.2 ?_,
        Finset.sum_congr rfl fun i hi => by rw [hl i hi]⟩
      rw [Finset.mem_image] at hi
      obtain ⟨i, hi, rfl⟩ := hi
      rw [Finsupp.support_filter] at hl hi
      specialize hs (Finset.mem_of_mem_filter i hi)
      rwa [← hl i hi, Set.mem_Iio, add_lt_add_iff_left, Nat.cast_lt] at hs
    rw [Finsupp.linearCombination_apply,
      ← Finsupp.sum_filter_add_sum_filter_not (· < ω * (1 + val c)),
      ← Finsupp.linearCombination_apply, he] at hf
    obtain ⟨-, hrc, hll⟩ := ihx c hcx (hcx.trans hx) 0
    let alg : Algebra ht.isRing_pow_omega0.toSubring hrc.toSubring :=
      (Subring.inclusion (subring_aux ht hrc)).toAlgebra
    have algmap (x : ht.isRing_pow_omega0.toSubring) :
        algebraMap ht.isRing_pow_omega0.toSubring hrc.toSubring x = ⟨x, _⟩ := rfl
    have hss : SetLike.coe (f.filter (· < ω * (1 + val c))).support ⊆
        Set.Iio (ω * (1 + val c)) := by
      rw [Finsupp.support_filter, Finset.coe_filter]
      intro i hi
      exact hi.2
    obtain ⟨⟨u, ⟨d, hd⟩⟩, ndeq⟩ := hll.surj _ ⟨_, ht.toIsField.linearCombination_lt hss⟩
    obtain ⟨m, hm, hmd⟩ : ∃ m : Multiset ht.toIsField.toSubfield,
        (∀ i ∈ m, i < c) ∧ (m.map fun x => t - x.1).prod = d := by
      obtain ⟨m, hm, hmd⟩ := Submonoid.exists_multiset_of_mem_closure hd
      simp_rw [Set.mem_image, Set.mem_Iio, ← Subtype.coe_lt_coe] at hm
      choose p hpc hpy using hm
      refine ⟨m.pmap p fun _ h => h, fun i hi => ?_, ?_⟩
      · rw [Multiset.mem_pmap] at hi
        obtain ⟨i, hi, rfl⟩ := hi
        exact hpc i hi
      · -- TODO: remove `RingEquiv.toMonoidHom` and friends
        change m.prod = ht.ringEquivPolynomial d at hmd
        rw [← RingEquiv.symm_apply_eq, map_multiset_prod] at hmd
        rw [Multiset.map_pmap, ← ht.isRing_pow_omega0.toSubring.subtype_apply, ← hmd,
          map_multiset_prod, Multiset.map_map, ← Multiset.pmap_eq_map (· ∈ m) _ m fun _ h => h]
        refine congr((m.pmap (fun x h => $(?_)) fun _ h => h).prod)
        rw [Subring.coe_subtype, Function.comp_apply, coe_ringEquivPolynomial_symm_apply]
        rw (occs := [1]) [← eval₂_X ht.toIsField.toSubfield.subtype t]
        rw [← Subfield.coe_subtype, ← eval₂_C ht.toIsField.toSubfield.subtype t,
          ← eval₂_sub, hpy x h]
    have hd0 : (d : Nimber) ≠ 0 := by
      refine hmd.symm.trans_ne (Multiset.prod_ne_zero fun h => ?_)
      rw [Multiset.mem_map] at h
      obtain ⟨k, hkm, hk⟩ := h
      exact ne_of_gt ((hm k hkm).trans (hcx.trans hx)) (sub_eq_zero.1 hk)
    simp_rw [algmap, Subtype.ext_iff, Subring.coe_mul, ← eq_div_iff_mul_eq hd0] at ndeq
    let algf := ht.algebraPowOmega0
    have towerf := ht.algebraPowOmega0ScalarTower
    let tt : ht.isRing_pow_omega0.toSubring :=
      ⟨t, val_lt_iff.1 (left_lt_opow (one_lt_val.2 ht.one_lt) one_lt_omega0)⟩
    have htc : t - c ≠ 0 := sub_ne_zero.2 (ne_of_gt (hcx.trans hx))
    refine ⟨m.map ht.toIsField.toSubfield.subtype, fun i hi => ?_, _,
      (u * (tt - ⟨c, ((hcx.trans hx).trans tt.2)⟩) ^ o +
        (m.map (fun i => tt - ⟨i.1, Set.Iio_subset_Iio tt.2.le i.2⟩)).prod *
        (e.linearCombination ht.toIsField.toSubfield fun i =>
          (tt - ⟨c, (hcx.trans hx).trans tt.2⟩) ^ (o - 1 - i))).2, ?_⟩
    · rw [Multiset.mem_map] at hi
      obtain ⟨i, hi, rfl⟩ := hi
      exact hm i hi
    rw [← Algebra.algebraMap_ofSubsemiring_apply]
    simp_rw [map_add, map_mul, map_pow, map_multiset_prod, tt, Multiset.map_map,
      Function.comp_def, map_sub, Algebra.algebraMap_ofSubsemiring_apply,
      Subfield.subtype_apply]
    rw [hmd, ← div_add_div _ _ hd0 (pow_ne_zero _ htc),
      ← ndeq, ← Algebra.algebraMap_ofSubsemiring_apply,
      ← towerf.toAlgHom_apply ht.toIsField.toSubfield,
      ← AlgHom.toLinearMap_apply, Finsupp.apply_linearCombination,
      div_eq_mul_inv, ← LinearMap.mulRight_apply ht.toIsField.toSubfield _⁻¹]
    set_option backward.isDefEq.respectTransparency false in rw [Finsupp.apply_linearCombination]
    rw [← hf, add_right_inj, Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun i hi => congrArg (e i • ·) ?_
    have hoi : i < o := Finset.mem_Iio.1 (hes hi)
    rw [(ihx c hcx (hcx.trans hx) i).1]
    simp_rw [Function.comp_apply, AlgHom.toLinearMap_apply, IsScalarTower.toAlgHom_apply,
      map_pow, map_sub, Algebra.algebraMap_ofSubsemiring_apply, LinearMap.mulRight_apply]
    rw [mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ htc), eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ htc),
      ← pow_add, add_right_comm, Nat.add_sub_of_le (Nat.le_sub_one_of_lt hoi),
      Nat.sub_add_cancel (Nat.one_le_of_lt hoi)]
  have surj' (y : Nimber) (hy : y < ∗(val t ^ (ω * (1 + val x)))) :
      ∃ m : Multiset Nimber, (∀ i ∈ m, i < x) ∧
      ∃ p : Nimber, p < ∗(val t ^ ω) ∧ p / (m.map fun c => t - c).prod = y := by
    obtain hx | ⟨c, hcx, hyc⟩ := normal.isBot_or_exists_le_succ_of_lt hy
    · rw [isBot_iff_eq_bot] at hx
      exact ⟨0, by simp, y, by simpa [hx] using hy, by simp⟩
    · rw [val.map_succ, Order.succ_eq_add_one, ← add_assoc, mul_add_one] at hyc
      have normal2 : Order.IsNormal fun x => ∗(val t ^ (ω * (1 + val c) + x)) :=
        of.isNormal.comp ((isNormal_opow (one_lt_val.2 ht.one_lt)).comp (isNormal_add_right _))
      obtain ⟨n1, hn1, hyn⟩ := (normal2.isBot_or_exists_le_succ_of_lt hyc).resolve_left (by simp)
      obtain ⟨n1, rfl⟩ := lt_omega0.1 hn1
      rw [← natCast_succ] at hyn
      obtain ⟨m, hm, p, hp, he⟩ := surj c hcx n1.succ y hyn
      refine ⟨m + .replicate n1.succ c, fun i hi => ?_, p, hp, Eq.trans ?_ he⟩
      · rw [Multiset.mem_add, Multiset.mem_replicate] at hi
        obtain hi | ⟨-, hi⟩ := hi
        · exact (hm i hi).trans hcx
        · exact hi.trans_lt hcx
      · rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]
    -- refine
    --   { toIsGroup := ht.toIsField.toIsGroup.opow _, mul_lt u v hu hv := ?_
    --     ne_one := by simp [Ordinal.opow_eq_one_iff, ht.ne_one] }
  have hr (n1 n2 : Nat) (c : Nimber) (hc : c < x) (u v : Nimber)
      (hu : u < ∗(val t ^ (ω * (1 + val c) + n1)))
      (hv : v < ∗(val t ^ (ω * (1 + val c) + n2))) :
      u * v < ∗(val t ^ (ω * (1 + val x) + n1 + n2)) := by
    stop
    obtain ⟨mu, hmu, pu, hpu, heu⟩ := surj u hu
    obtain ⟨mv, hmv, pv, hpv, hev⟩ := surj v hv
    let := Algebra.compHom Nimber ht.ringEquivPolynomial.symm.toRingHom
    let f := ht.ringEquivPolynomial (⟨pu, hpu⟩ * ⟨pv, hpv⟩)
    let s := (mu + mv).toFinset
    let g c : ht.toIsField.toSubfield[X] := if h : c < t then X - C ⟨c, h⟩ else 1
    have hg c : (g c).Monic := by unfold g; split <;> monicity
    have hgg a b (hab : a ≠ b) : IsCoprime (g a) (g b) := by
      unfold g
      split
      · split
        · apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
          simp [sub_ne_zero, hab]
        · apply isCoprime_one_right
      · apply isCoprime_one_left
    let n c := (mu + mv).count c
    let gi c := of (val t ^ (ω * (1 + val c)))
    -- have hgi i (hi : i ∈ s) : gi i *
    #check mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    stop
    rw [← val_lt_iff] at hu hv
    obtain ⟨ua, ub, rfl⟩ := exists_omega0_mul_add_natCast u
    obtain ⟨va, vb, rfl⟩ := exists_omega0_mul_add_natCast v
    by_cases! ha : max ua va = 0
    · rw [(max_eq_zero.1 ha).1, (max_eq_zero.1 ha).2, mul_zero, zero_add, opow_natCast, zero_add,
        opow_natCast, ← ht.pow_eq, ← ht.pow_eq, ← pow_add, ht.pow_eq, ← val_lt_iff, val_of,
        ← opow_natCast, opow_lt_opow_iff_right (one_lt_val.2 ht.one_lt), mul_one_add]
      exact lt_add_of_lt_of_nonneg (nat_lt_omega0 (ub + vb)) (zero_le _)
    obtain ⟨m, hm⟩ : ∃ m, 1 + m = max ua va :=
      ⟨_, Ordinal.add_sub_cancel_of_le (Ordinal.one_le_iff_ne_zero.2 ha)⟩
    have hua : ua < 1 + val x := lt_of_mul_lt_mul_left' (lt_of_le_of_lt (by simp) hu)
    have hva : va < 1 + val x := lt_of_mul_lt_mul_left' (lt_of_le_of_lt (by simp) hv)
    have hmx : m < val x := lt_of_add_lt_add_left (hm.trans_lt (max_lt hua hva))
    have hux : of ua < x := sorry
    have hvx : of va < x := sorry
    obtain ⟨ru, lu⟩ := (ihx (of ua) hux (hux.trans hx) 0).2
    obtain ⟨rv, lv⟩ := (ihx (of va) hvx (hvx.trans hx) 0).2
    sorry
  have hy {y : Nimber} (hy : y < ∗(val t ^ (ω * (1 + val x)))) : (t - x) * y ≠ 1 := by
    -- `y` is a `t`-linear combination of [powers] of `t`
    -- which must be either powers of `t` or negative powers of `t - z` for `z < x`
    -- these all lie in the localization of `t[t]` at `t - z` for `z < x`
    -- which admits a ring homomorphism into `t` sending `t` to `x`
    -- this sends `t - x` to `0`, so it cannot have an inverse
    sorry
  induction n with
  | zero =>
    rw [← inv_eq_iff_eq_inv]
    sorry
  | succ n ihn =>
    sorry

end Nimber.IsAlgClosed
