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
          (Subring.inclusion (ht.subring_aux rx)).toAlgebra
        IsLocalization (Submonoid.comap ht.ringEquivPolynomial.toMonoidHom
          (Submonoid.closure ((fun u => X - C u) '' Set.Iio ⟨x, hx⟩)))
          rx.toSubring := by
  obtain ⟨k, rfl, rfl⟩ : ∃ k : Nimber ×ₗ Nat, (ofLex k).1 = x ∧ (ofLex k).2 = n :=
    ⟨toLex (x, n), rfl, rfl⟩
  induction k using WellFoundedLT.induction with | ind k ih
  obtain ⟨x, n, rfl⟩ : ∃ x n, toLex (x, n) = k := ⟨(ofLex k).1, (ofLex k).2, rfl⟩
  simp only [Lex.forall, ofLex_toLex, Prod.forall] at hx ih ⊢
  have surj (c : Nimber) (o : Nat) (hco : toLex (c, o) ≤ toLex (x, n)) (y : Nimber)
      (hyc : y < ∗(val t ^ (ω * (1 + val c) + o))) (hq : c = x → n ≠ 0) :
      ∃ m : Multiset Nimber, (∀ i ∈ m, i < c) ∧
      ∃ p : Nimber, p < ∗(val t ^ ω) ∧ p / ((m.map fun c => t - c).prod * (t - c) ^ o) = y := by
    have hcx : c ≤ x := (Prod.Lex.toLex_le_toLex'.1 hco).1
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
    obtain ⟨-, hrc, hll⟩ := ih c 0 (lt_of_le_of_ne
      (hco.trans' (Prod.Lex.toLex_le_toLex.2 (.inr ⟨rfl, Nat.zero_le o⟩)))
      (fun h => hq congr((ofLex $h).1) congr((ofLex $(h.symm)).2))) (hcx.trans_lt hx)
    let alg : Algebra ht.isRing_pow_omega0.toSubring hrc.toSubring :=
      (Subring.inclusion (ht.subring_aux hrc)).toAlgebra
    have algmap (x : ht.isRing_pow_omega0.toSubring) :
        algebraMap ht.isRing_pow_omega0.toSubring hrc.toSubring x = ⟨x, _⟩ := rfl
    have hss : SetLike.coe (f.filter (· < ω * (1 + val c))).support ⊆
        Set.Iio (ω * (1 + val c)) := by
      rw [Finsupp.support_filter, Finset.coe_filter]
      intro i hi
      exact hi.2
    set_option backward.isDefEq.respectTransparency false in
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
      exact ne_of_gt ((hm k hkm).trans (hcx.trans_lt hx)) (sub_eq_zero.1 hk)
    set_option backward.isDefEq.respectTransparency false in
      simp_rw [algmap, Subtype.ext_iff, Subring.coe_mul, ← eq_div_iff_mul_eq hd0] at ndeq
    let algf := ht.algebraPowOmega0
    have towerf := ht.algebraPowOmega0ScalarTower
    let tt : ht.isRing_pow_omega0.toSubring :=
      ⟨t, val_lt_iff.1 (left_lt_opow (one_lt_val.2 ht.one_lt) one_lt_omega0)⟩
    have htc : t - c ≠ 0 := sub_ne_zero.2 (ne_of_gt (hcx.trans_lt hx))
    refine ⟨m.map ht.toIsField.toSubfield.subtype, fun i hi => ?_, _,
      (u * (tt - ⟨c, ((hcx.trans_lt hx).trans tt.2)⟩) ^ o +
        (m.map (fun i => tt - ⟨i.1, Set.Iio_subset_Iio tt.2.le i.2⟩)).prod *
        (e.linearCombination ht.toIsField.toSubfield fun i =>
          (tt - ⟨c, (hcx.trans_lt hx).trans tt.2⟩) ^ (o - 1 - i))).2, ?_⟩
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
    obtain ⟨hinv, -⟩ :=
      ih c i (hco.trans_lt' (Prod.Lex.toLex_lt_toLex.2 (.inr ⟨rfl, hoi⟩))) (hcx.trans_lt hx)
    simp_rw [Function.comp_apply, AlgHom.toLinearMap_apply, IsScalarTower.toAlgHom_apply,
      map_pow, map_sub, Algebra.algebraMap_ofSubsemiring_apply, LinearMap.mulRight_apply]
    rw [hinv, mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ htc),
      eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ htc), ← pow_add, add_right_comm,
      Nat.add_sub_of_le (Nat.le_sub_one_of_lt hoi), Nat.sub_add_cancel (Nat.one_le_of_lt hoi)]
  -- have surj' (y : Nimber) (hy : y < ∗(val t ^ (ω * (1 + val x)))) :
  --     ∃ m : Multiset Nimber, (∀ i ∈ m, i < x) ∧
  --     ∃ p : Nimber, p < ∗(val t ^ ω) ∧ p / (m.map fun c => t - c).prod = y := by
  --   obtain hx | ⟨c, hcx, hyc⟩ := normal.isBot_or_exists_le_succ_of_lt hy
  --   · rw [isBot_iff_eq_bot] at hx
  --     exact ⟨0, by simp, y, by simpa [hx] using hy, by simp⟩
  --   · rw [val.map_succ, Order.succ_eq_add_one, ← add_assoc, mul_add_one] at hyc
  --     have normal2 : Order.IsNormal fun x => ∗(val t ^ (ω * (1 + val c) + x)) :=
  --       of.isNormal.comp ((isNormal_opow (one_lt_val.2 ht.one_lt)).comp (isNormal_add_right _))
  --     obtain ⟨n1, hn1, hyn⟩ := (normal2.isBot_or_exists_le_succ_of_lt hyc).resolve_left (by simp)
  --     obtain ⟨n1, rfl⟩ := lt_omega0.1 hn1
  --     rw [← natCast_succ] at hyn
  --     obtain ⟨m, hm, p, hp, he⟩ := surj c hcx n1.succ y hyn
  --     refine ⟨m + .replicate n1.succ c, fun i hi => ?_, p, hp, Eq.trans ?_ he⟩
  --     · rw [Multiset.mem_add, Multiset.mem_replicate] at hi
  --       obtain hi | ⟨-, hi⟩ := hi
  --       · exact (hm i hi).trans hcx
  --       · exact hi.trans_lt hcx
  --     · rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]
    -- refine
    --   { toIsGroup := ht.toIsField.toIsGroup.opow _, mul_lt u v hu hv := ?_
    --     ne_one := by simp [Ordinal.opow_eq_one_iff, ht.ne_one] }
  have hr (n1 n2 : Nat) (c : Nimber) (hcn : toLex (c, n1 + n2) ≤ toLex (x, n)) (u v : Nimber)
      (hu : u < ∗(val t ^ (ω * (1 + val c) + n1)))
      (hv : v < ∗(val t ^ (ω * (1 + val c) + n2))) (hq : c = x → n ≠ 0) :
      u * v < ∗(val t ^ (ω * (1 + val c) + (n1 + n2 : Nat))) := by
    have hcii i (hi : i ≤ n1 + n2) : toLex (c, i) ≤ toLex (x, n) :=
      hcn.trans' (Prod.Lex.toLex_mono ⟨le_rfl, hi⟩)
    have hcn1 : toLex (c, n1) ≤ toLex (x, n) := hcii n1 (Nat.le_add_right n1 n2)
    have hcn2 : toLex (c, n2) ≤ toLex (x, n) := hcii n2 (Nat.le_add_left n2 n1)
    have hi0 i (hi : i ≤ c) : toLex (i, 0) < toLex (x, n) :=
      (Prod.Lex.toLex_mono ⟨hi, le_refl 0⟩).trans_lt <|
        lt_of_le_of_ne (hcii 0 (Nat.zero_le (n1 + n2)))
          fun h => hq congr((ofLex $h).1) congr((ofLex $(h.symm)).2)
    have hcx : c ≤ x := (Prod.Lex.toLex_le_toLex'.1 hcn).1
    obtain ⟨mu, hmu, pu, hpu, heu⟩ := surj c n1 hcn1 u hu hq
    obtain ⟨mv, hmv, pv, hpv, hev⟩ := surj c n2 hcn2 v hv hq
    let alg := Algebra.compHom Nimber ht.ringEquivPolynomial.symm.toRingHom
    have algMap : algebraMap ht.toIsField.toSubfield[X] Nimber =
        eval₂RingHom ht.toIsField.toSubfield.subtype t := by
      refine DFunLike.ext _ _ fun i => ?_
      rw [coe_eval₂RingHom, ← ht.coe_ringEquivPolynomial_symm_apply]
      rfl
    have hmi i (hi : i ∈ (mu + mv).toFinset) : i < c := by
      simp_rw [Multiset.mem_toFinset, Multiset.mem_add] at hi
      exact hi.elim (hmu i) (hmv i)
    let f := ht.ringEquivPolynomial (⟨pu, hpu⟩ * ⟨pv, hpv⟩)
    let s := Finset.cons c (mu + mv).toFinset fun h => lt_irrefl c (hmi c h)
    have hsc i (hi : i ∈ s) : i ≤ c := by
      simp_rw [s, Finset.mem_cons] at hi
      exact hi.elim (fun h => h.le) (fun h => (hmi i h).le)
    have hst i (hi : i ∈ s) : i < t := (hsc i hi).trans_lt (hcx.trans_lt hx)
    let g i : ht.toIsField.toSubfield[X] := X - C (if h : i < t then ⟨i, h⟩ else 0)
    have hg i : (g i).Monic := by unfold g; split <;> monicity
    have hgg : (SetLike.coe s).Pairwise fun a b => IsCoprime (g a) (g b) := by
      unfold g
      intro a ha b hb hab
      rw [dif_pos (hst a ha), dif_pos (hst b hb)]
      apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      simp [sub_ne_zero, hab]
    let n i := if i = c then n1 + n2 else (mu + mv).count i
    let gi i := of (val t ^ (ω * (1 + val i)))
    have hgi i (hi : i ∈ s) : gi i * algebraMap _ _ (g i) = 1 := by
      unfold g gi
      have hic : i ≤ c := by
        simp_rw [s, Finset.mem_cons, Multiset.mem_toFinset, Multiset.mem_add] at hi
        obtain hi | hi | hi := hi
        · exact hi.le
        · exact (hmu i hi).le
        · exact (hmv i hi).le
      have hit := hic.trans_lt (hcx.trans_lt hx)
      rw [dif_pos hit, algMap, ← add_zero (ω * (1 + val i)),
        ← Nat.cast_zero, (ih i 0 (hi0 i hic) hit).1]
      simp [sub_ne_zero.2 (ne_of_gt hit)]
    obtain ⟨q, r, hr, hf⟩ := mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse f
      (fun i _ => hg i) hgg n hgi
    rw [← heu, ← hev, div_mul_div_comm, mul_mul_mul_comm, ← Multiset.prod_add,
      ← Multiset.map_add, ← pow_add, div_eq_mul_inv]
    -- forced to do nonsense to extract parts of the goal state as variables
    refine letI lhs := _; (?_ : (zeta% lhs) < _)
    have hll : (zeta% lhs) = (letI lhs' := _; haveI f' : (zeta% lhs') = _ := hf; lhs') := by
      clear lhs
      apply congrArg₂ (· * ·)
      · rw [algMap, coe_eval₂RingHom, ← ht.coe_ringEquivPolynomial_symm_apply,
          ht.ringEquivPolynomial.symm_apply_apply, Subring.coe_mul]
      unfold s
      rw [mul_inv_rev, Finset.prod_cons]
      apply congrArg₂ (· * ·)
      · unfold gi n
        rw [← inv_pow, ← add_zero (ω * (1 + val c)), ← Nat.cast_zero,
          (ih c 0 (hi0 c le_rfl) (hcx.trans_lt hx)).1, zero_add, pow_one, if_pos rfl]
      rw [Finset.prod_multiset_map_count, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      unfold gi n
      rw [← inv_pow, if_neg (ne_of_lt (hmi i hi)), ← add_zero (ω * (1 + val i)), ← Nat.cast_zero,
        (ih i 0 (hi0 i (hmi i hi).le) ((hmi i hi).trans (hcx.trans_lt hx))).1, zero_add, pow_one]
    clear lhs
    rw [hll, hf]
    apply (ht.toIsGroup.opow _).add_lt
    · rw [algMap, coe_eval₂RingHom, ← ht.coe_ringEquivPolynomial_symm_apply]
      refine (ht.ringEquivPolynomial.symm q).2.trans_le
        (of.monotone (opow_le_opow_right (by simpa using ht.zero_lt) ?_))
      simp [mul_add, add_assoc]
    · refine (ht.toIsGroup.opow _).sum_lt fun i hi => (ht.toIsGroup.opow _).sum_lt fun j _ => ?_
      have hgd : (g i).degree = 1 := by unfold g; compute_degree!
      have hrd : (r i j).natDegree = 0 := by
        rw [natDegree_eq_zero_iff_degree_le_zero, ← Nat.WithBot.lt_one_iff_le_zero, ← hgd]
        exact hr i hi j
      have hlx : toLex (i, j.1) < toLex (c, n1 + n2) :=
        Prod.Lex.toLex_lt_toLex'.2 ⟨hsc i hi, fun h => j.2.trans_eq (if_pos h)⟩
      obtain ⟨b, hb⟩ := natDegree_eq_zero.1 hrd
      rw [← hb, algMap, coe_eval₂RingHom, eval₂_C]
      unfold gi
      rw [← add_zero (ω * (1 + val i)), ← Nat.cast_zero,
        (ih i 0 (hi0 i (hsc i hi)) (hst i hi)).1, zero_add, pow_one, inv_pow,
        ← (ih i j (hlx.trans_le hcn) (hst i hi)).1]
      apply ht.toIsField.mul_lt_opow_of_left_lt
      · exact b.2
      refine of.strictMono ((opow_lt_opow_iff_right (one_lt_val.2 ht.one_lt)).2 ?_)
      rw [mul_one_add, mul_one_add, add_assoc, add_assoc, add_lt_add_iff_left]
      obtain hij | hij := Prod.Lex.toLex_lt_toLex.1 hlx
      · rw [← val.lt_iff_lt, ← Order.add_one_le_iff] at hij
        refine lt_add_of_lt_of_nonneg (lt_of_lt_of_le ?_ (mul_le_mul_right hij ω)) (by simp)
        rw [mul_add_one, add_lt_add_iff_left]
        exact nat_lt_omega0 j
      · exact add_lt_add_of_le_of_lt ((mul_le_mul_iff_right₀ omega0_pos).2
          (val.monotone hij.1.le)) (Nat.cast_lt.2 hij.2)
  have normal1 : Order.IsNormal fun x => ∗(val t ^ (ω * (1 + val x))) :=
    of.isNormal.comp ((isNormal_opow (one_lt_val.2 ht.one_lt)).comp
      ((isNormal_mul_right omega0_pos).comp (isNormal_add_right 1)))
  have hk c (hc : c ≤ x) : t - c < (of (val t ^ (ω * (1 + val x)))) := by
    refine lt_of_lt_of_le ?_ (of.monotone (opow_le_opow_right (by simpa using ht.pos)
      (le_mul_of_one_le_right (by simp) (by simp))))
    rw [CharTwo.sub_eq_add]
    apply (ht.toIsGroup.opow ω).add_lt
    · exact val_lt_iff.1 (left_lt_opow (one_lt_val.2 ht.one_lt) one_lt_omega0)
    · apply (hc.trans_lt hx).trans
      exact val_lt_iff.1 (left_lt_opow (one_lt_val.2 ht.one_lt) one_lt_omega0)
  cases n with
  | zero =>
    have hrr : IsRing (∗(val t ^ (ω * (1 + val x)))) := by
      refine
        { toIsGroup := ht.toIsGroup.opow _, mul_lt y z hy hz := ?_,
          ne_one := by simp [Ordinal.opow_eq_one_iff, ht.ne_one] }
      wlog hzy : z ≤ y generalizing y z with hyz
      · rw [mul_comm]
        exact hyz z y hz hy (le_of_not_ge hzy)
      obtain hx | ⟨c, hcx, hyc⟩ := normal1.isBot_or_exists_le_succ_of_lt hy
      · rw [isBot_iff_eq_bot, bot_eq_zero] at hx
        rw [hx, val_zero, add_zero, mul_one] at hy hz ⊢
        exact ht.isRing_pow_omega0.mul_lt hy hz
      have normal2 : Order.IsNormal fun x => ∗(val t ^ (ω * (1 + val c) + x)) :=
        of.isNormal.comp ((isNormal_opow (one_lt_val.2 ht.one_lt)).comp (isNormal_add_right _))
      rw [val.map_succ, Order.succ_eq_add_one, ← add_assoc, mul_add_one] at hyc
      obtain ⟨d, hd, hyd⟩ := (normal2.isBot_or_exists_le_succ_of_lt hyc).resolve_left (by simp)
      obtain ⟨d, rfl⟩ := lt_omega0.1 hd
      rw [← natCast_succ] at hyd
      have hrr := (ih c d.succ (Prod.Lex.toLex_lt_toLex.2 (.inl hcx)) (hcx.trans hx)).2.1
      refine lt_of_lt_of_le (hr d.succ d.succ c (Prod.Lex.toLex_le_toLex.2 (.inl hcx)) y z hyd
        (hzy.trans_lt hyd) (Not.elim hcx.ne))
        (of.monotone (opow_le_opow_right (by simpa using ht.zero_lt) ?_))
      rw [mul_one_add, mul_one_add, add_assoc, add_le_add_iff_left]
      rw [← val.lt_iff_lt, ← Order.add_one_le_iff] at hcx
      refine le_trans ?_ (mul_le_mul_right hcx ω)
      rw [mul_add_one, add_le_add_iff_left]
      exact (nat_lt_omega0 (d.succ + d.succ)).le
    let alg : Algebra ht.isRing_pow_omega0.toSubring hrr.toSubring :=
      (Subring.inclusion (ht.subring_aux hrr)).toAlgebra
    have algMap (x : ht.isRing_pow_omega0.toSubring) :
        algebraMap ht.isRing_pow_omega0.toSubring hrr.toSubring x = ⟨x, _⟩ := rfl
    have hll : IsLocalization ((Submonoid.closure ((fun u ↦ X - C u) '' Set.Iio ⟨x, hx⟩)).comap
        ht.ringEquivPolynomial.toMonoidHom) hrr.toSubring := by
      refine { map_units := ?_, surj y := ?_, exists_of_eq h := ⟨1, by simpa [algMap] using h⟩ }
      · rw [Subtype.forall]
        simp only [← IsUnit.mem_submonoid_iff, ← Submonoid.mem_comap]
        rw [← SetLike.le_def,
          show ht.ringEquivPolynomial.toMonoidHom = -- is there a better way
            ht.ringEquivPolynomial.toMulEquiv.toMonoidHom from rfl,
          -- problem with `Submonoid.comap`, should take a `MonoidHom` instead
          show Submonoid.comap ht.ringEquivPolynomial.toMulEquiv.toMonoidHom =
            Submonoid.comap ht.ringEquivPolynomial.toMulEquiv from rfl,
          Submonoid.comap_equiv_eq_map_symm, Submonoid.map_le_iff_le_comap,
          Submonoid.closure_le, Set.image_subset_iff]
        intro y hy
        have hui := (ih y 0 (Prod.Lex.toLex_lt_toLex.2 (.inl hy)) (hx.trans' hy)).1
        rw [zero_add, pow_one, Nat.cast_zero, add_zero] at hui
        have hz : ∗(val t ^ (ω * (1 + val y))) ≠ 0 := by
          rw [hui]
          exact inv_ne_zero (sub_ne_zero.2 (ne_of_gt (hx.trans' hy)))
        simp_rw [Submonoid.coe_comap, Set.mem_preimage, SetLike.mem_coe, IsUnit.mem_submonoid_iff,
          show ⇑ht.ringEquivPolynomial.toMulEquiv.symm = ⇑ht.ringEquivPolynomial.symm from rfl,
          algMap, ht.coe_ringEquivPolynomial_symm_apply, eval₂_sub, eval₂_X, eval₂_C,
          Subfield.coe_subtype, ← inv_eq_iff_eq_inv.2 hui]
        refine IsUnit.of_mul_eq_one ⟨∗(val t ^ (ω * (1 + val y))), Set.mem_Iio.2 ?_⟩
          (Subtype.ext (inv_mul_cancel₀ hz))
        apply normal1.strictMono
        exact hy
      · obtain ⟨y, hy⟩ := y
        obtain hx | ⟨c, hcx, hyc⟩ := normal1.isBot_or_exists_le_succ_of_lt hy
        · rw [isBot_iff_eq_bot, bot_eq_zero] at hx
          subst x
          exact ⟨(⟨y, by simpa using hy⟩, 1),
            set_option backward.isDefEq.respectTransparency false in by simp [algMap]⟩
        have normal2 : Order.IsNormal fun x => ∗(val t ^ (ω * (1 + val c) + x)) :=
          of.isNormal.comp ((isNormal_opow (one_lt_val.2 ht.one_lt)).comp (isNormal_add_right _))
        rw [val.map_succ, Order.succ_eq_add_one, ← add_assoc, mul_add_one] at hyc
        obtain ⟨d, hd, hyd⟩ := (normal2.isBot_or_exists_le_succ_of_lt hyc).resolve_left (by simp)
        obtain ⟨d, rfl⟩ := lt_omega0.1 hd
        rw [← natCast_succ] at hyd
        obtain ⟨m, hmc, p, hp, hpm⟩ := surj c d.succ
          (Prod.Lex.toLex_le_toLex.2 (.inl hcx)) y hyd (Not.elim hcx.ne)
        have hti i (hi : i ≤ c) : t - i ∈ ht.isRing_pow_omega0.toSubring := by
          apply sub_mem
          · rw [mem_toSubring_iff]
            exact val_lt_iff.1 (left_lt_opow (one_lt_val.2 ht.one_lt) one_lt_omega0)
          · rw [mem_toSubring_iff]
            refine (hi.trans_lt (hcx.trans hx)).trans ?_
            exact val_lt_iff.1 (left_lt_opow (one_lt_val.2 ht.one_lt) one_lt_omega0)
        refine ⟨(⟨p, hp⟩, ⟨⟨(m.map (fun c => t - c)).prod *
          (t - c) ^ d.succ, ?_⟩, ?_⟩), Subtype.ext ?_⟩
        · apply mul_mem
          · apply multiset_prod_mem
            intro i hi
            rw [Multiset.mem_map] at hi
            obtain ⟨i, hi, rfl⟩ := hi
            exact hti i (hmc i hi).le
          · apply pow_mem
            exact hti c le_rfl
        · rw [← Submonoid.mem_map_iff_mem ht.isRing_pow_omega0.toSubring.subtype_injective]
          simp only [Subring.subtype_apply]
          refine letI rhs := _; (?_ : _ ∈ zeta% rhs)
          suffices h : ∀ i ≤ c, t - i ∈ zeta% rhs by
            apply mul_mem
            · apply multiset_prod_mem
              intro i hi
              rw [Multiset.mem_map] at hi
              obtain ⟨i, hi, rfl⟩ := hi
              exact h i (hmc i hi).le
            · exact pow_mem (h c le_rfl) d.succ
          intro i hi
          change ht.isRing_pow_omega0.toSubring.subtype ⟨t - i, hti i hi⟩ ∈ _
          apply Submonoid.mem_map_of_mem
          rw [Submonoid.mem_comap]
          apply Submonoid.mem_closure_of_mem
          rw [Set.mem_image]
          refine ⟨⟨i, hi.trans_lt (hcx.trans hx)⟩, hi.trans_lt hcx, ?_⟩
          rw [show ⇑ht.ringEquivPolynomial.toMonoidHom = ⇑ht.ringEquivPolynomial from rfl,
            ← ht.ringEquivPolynomial.symm_apply_eq, Subtype.ext_iff,
            ht.coe_ringEquivPolynomial_symm_apply, eval₂_sub, eval₂_X, eval₂_C,
            Subfield.subtype_apply]
        · simp_rw [Subring.coe_mul, algMap]
          refine (eq_div_iff_mul_eq ?_).1 hpm.symm
          apply mul_ne_zero
          · apply Multiset.prod_ne_zero
            intro h
            rw [Multiset.mem_map] at h
            obtain ⟨i, hi, hit⟩ := h
            exact ne_of_gt ((hmc i hi).trans (hcx.trans hx)) (sub_eq_zero.1 hit)
          · apply pow_ne_zero
            exact sub_ne_zero.2 (ne_of_gt (hcx.trans hx))
    refine ⟨?_, hrr, hll⟩
    have hy {y : Nimber} (hy : y < ∗(val t ^ (ω * (1 + val x)))) : (t - x) * y ≠ 1 := by
      let m : ht.isRing_pow_omega0.toSubring →+* ht.toIsField.toSubfield :=
        RingHom.comp (evalRingHom ⟨x, hx⟩) ht.ringEquivPolynomial.toRingHom
      let ml := hll.lift (g := m) <| by
        rw [Subtype.forall]
        simp only [← IsUnit.mem_submonoid_iff, ← Submonoid.mem_comap]
        rw [← SetLike.le_def,
          show ht.ringEquivPolynomial.toMonoidHom = -- is there a better way
            ht.ringEquivPolynomial.toMulEquiv.toMonoidHom from rfl,
          -- problem with `Submonoid.comap`, should take a `MonoidHom` instead
          show Submonoid.comap ht.ringEquivPolynomial.toMulEquiv.toMonoidHom =
            Submonoid.comap ht.ringEquivPolynomial.toMulEquiv from rfl,
          Submonoid.comap_equiv_eq_map_symm, Submonoid.map_le_iff_le_comap,
          Submonoid.closure_le, Set.image_subset_iff]
        intro y hy
        simp_rw [Submonoid.coe_comap, Set.mem_preimage, SetLike.mem_coe, IsUnit.mem_submonoid_iff]
        apply IsUnit.mk0
        unfold m
        rw [RingHom.comp_apply,
          show ⇑ht.ringEquivPolynomial.toRingHom = ⇑ht.ringEquivPolynomial from rfl,
          show ⇑ht.ringEquivPolynomial.toMulEquiv.symm = ⇑ht.ringEquivPolynomial.symm from rfl,
          ht.ringEquivPolynomial.apply_symm_apply, coe_evalRingHom, eval_sub, eval_X, eval_C,
          sub_ne_zero]
        exact ne_of_gt hy
      let tt : ht.isRing_pow_omega0.toSubring :=
        ⟨t, val_lt_iff.1 (left_lt_opow (one_lt_val.2 ht.one_lt) one_lt_omega0)⟩
      change ((algebraMap _ _ (tt - ⟨x, hx.trans tt.2⟩) * ⟨y, hy⟩ : hrr.toSubring) : Nimber) ≠ 1
      rw [← Subring.coe_subtype, map_ne_one_iff _ hrr.toSubring.subtype_injective]
      apply ne_of_apply_ne ml
      suffices h : m tt - m ⟨x, hx.trans tt.2⟩ = 0 by simp [h, ml]
      unfold m
      rw [RingHom.comp_apply, RingHom.comp_apply, sub_eq_zero]
      conv =>
        congr <;> enter [2, 2]
        · equals ht.ringEquivPolynomial.symm X =>
            apply Subtype.ext
            rw [ht.coe_ringEquivPolynomial_symm_apply]
            simp [tt]
        · equals ht.ringEquivPolynomial.symm (C ⟨x, hx⟩) =>
            apply Subtype.ext
            rw [ht.coe_ringEquivPolynomial_symm_apply]
            simp
      simp
    have hyo : of (val t ^ (ω * (1 + val x))) ≤ (t - x)⁻¹ := by
      by_contra! h
      apply hy h
      apply mul_inv_cancel₀
      exact sub_ne_zero.2 (ne_of_gt hx)
    have hyf : ¬IsField (of (val t ^ (ω * (1 + val x)))) :=
      fun h => (h.inv_lt (hk x le_rfl)).not_ge hyo
    rw [Nat.cast_zero, add_zero, zero_add, pow_one]
    apply le_antisymm hyo
    apply hrr.inv_le_of_not_isField hyf
    refine le_of_not_gt fun h => ?_
    rw [CharTwo.sub_eq_add, ← ht.add_eq_of_lt hx, ← val_lt_iff] at h
    obtain hi | ⟨d, hd, hi⟩ := lt_add_iff_lt_left_or_exists_lt.1 h
    · rw [val.lt_iff_lt] at hi
      apply ht.toIsField.inv_lt at hi
      apply hi.not_ge
      rw [inv_inv, ← val_le_iff]
      exact left_le_opow (val t) (by simp [pos_iff_ne_zero])
    · rw [← of_lt_iff] at hd
      rw [← val_of (val t + d), ← val_of d, ht.add_eq_of_lt (hd.trans hx),
        val.injective.eq_iff, inv_eq_iff_eq_inv, ← CharTwo.sub_eq_add] at hi
      apply hi.not_gt
      rw [← pow_one (t - of d), ← zero_add 1,
        ← (ih (of d) 0 (Prod.Lex.toLex_lt_toLex.2 (.inl hd)) (hd.trans hx)).1,
        Nat.cast_zero, add_zero]
      exact normal1.strictMono hd
  | succ n =>
    have hli i (hi : i ≤ n) : toLex (x, i) < toLex (x, n + 1) :=
      Prod.Lex.toLex_lt_toLex.2 (.inr ⟨rfl, Nat.lt_add_one_of_le hi⟩)
    have hp0 := (ih x 0 (hli 0 (Nat.zero_le n)) hx).1
    rw [Nat.cast_zero, add_zero, zero_add, pow_one] at hp0
    obtain ⟨hpu, hrr, hll⟩ := ih x n (hli n le_rfl) hx
    refine ⟨?_, hrr, hll⟩
    rw [pow_succ, mul_inv_rev]
    apply le_antisymm
    · refine le_of_not_gt fun h => ?_
      obtain ⟨m, hm, p, hp, hy⟩ := surj x (n + 1) le_rfl _ h fun _ => Nat.add_one_ne_zero n
      rw [← div_div, div_eq_iff (pow_ne_zero _ (sub_ne_zero.2 (ne_of_gt hx))),
        mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 (ne_of_gt hx))), mul_one,
        ← hp0, div_eq_mul_inv] at hy
      refine ne_of_lt ?_ hy
      apply hrr.mul_lt
      · apply hp.trans_le
        exact of.monotone (opow_le_opow_right (by simpa using ht.pos)
          (le_mul_of_one_le_right (by simp) (by simp)))
      · rw [← mem_toSubring_iff hrr, ← Multiset.prod_map_inv]
        apply multiset_prod_mem
        intro i hi
        rw [Multiset.mem_map] at hi
        obtain ⟨i, hi, rfl⟩ := hi
        rw [← pow_one (t - i), ← zero_add (1 : ℕ), mem_toSubring_iff,
          ← (ih i 0 (Prod.Lex.toLex_lt_toLex.2 (.inl (hm i hi))) ((hm i hi).trans hx)).1,
          Nat.cast_zero, add_zero]
        exact normal1.strictMono (hm i hi)
    rw [← hpu, ← hp0]
    refine (ht.toIsGroup.opow _).mul_le_of_forall_lt
      (fun l hl => ?_) (fun u hu => ?_) (fun u hu l hl => ?_) <;> rw [mul_comm]
    · refine hr n 1 x le_rfl _ _ hl ?_ fun _ => Nat.add_one_ne_zero n
      refine of.strictMono ((opow_lt_opow_iff_right (one_lt_val.2 ht.one_lt)).2 ?_)
      simp
    · refine hr (n + 1) 0 x le_rfl _ _ ?_ (hu.trans_eq (by simp)) fun _ => Nat.add_one_ne_zero n
      refine of.strictMono ((opow_lt_opow_iff_right (one_lt_val.2 ht.one_lt)).2 ?_)
      simp
    · refine hr n 1 x le_rfl _ _ hl (hu.trans ?_) fun _ => Nat.add_one_ne_zero n
      refine of.strictMono ((opow_lt_opow_iff_right (one_lt_val.2 ht.one_lt)).2 ?_)
      simp

end Nimber.IsAlgClosed
