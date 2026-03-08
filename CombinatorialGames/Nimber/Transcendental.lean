/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
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

def algEquivPolynomial :
    letI := ht.algebraPowOmega0
    ht.isRing_pow_omega0.toSubring ≃ₐ[ht.toIsField.toSubfield]
    ht.toIsField.toSubfield[X] :=
  letI := ht.algebraPowOmega0
  .symm <| .ofBijective (Polynomial.aeval
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
          (Submonoid.closure ((fun u => Polynomial.X - Polynomial.C u) '' Set.Iio ⟨x, hx⟩)))
          rx.toSubring := by
  have normal : Order.IsNormal fun x => ∗(val t ^ (ω * (1 + val x))) :=
    of.isNormal.comp ((isNormal_opow (one_lt_val.2 ht.one_lt)).comp
      ((isNormal_mul_right omega0_pos).comp (isNormal_add_right 1)))
  induction x using WellFoundedLT.induction generalizing n with | ind x ihx
  have surj (y : Nimber) (hy : y < ∗(val t ^ (ω * (1 + val x)))) :
      ∃ m : Multiset Nimber, (∀ i ∈ m, i < x) ∧
      ∃ p : Nimber, p < ∗(val t ^ ω) ∧ p / (m.map fun c => t - c).prod = y := by
    obtain hx | ⟨c, hcx, hyc⟩ := normal.isBot_or_exists_le_succ_of_lt hy
    · rw [isBot_iff_eq_bot] at hx
      exact ⟨0, by simp, y, by simpa [hx] using hy, by simp⟩
    · rw [val.map_succ, Order.succ_eq_add_one, ← add_assoc, mul_add_one] at hyc
      obtain ⟨f, hs, hf⟩ := ht.toIsField.exists_linearCombination_of_lt hyc
      rw [Finsupp.linearCombination_apply] at hf
      sorry
  induction n with
  | zero =>
    rw [← inv_eq_iff_eq_inv]
    have hr : IsRing (∗(val t ^ (ω * (1 + val x)))) := by
      refine
        { toIsGroup := ht.toIsField.toIsGroup.opow _, mul_lt u v hu hv := ?_
          ne_one := by simp [Ordinal.opow_eq_one_iff, ht.ne_one],}
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
    sorry
  | succ n ihn =>
    sorry

end Nimber.IsAlgClosed
