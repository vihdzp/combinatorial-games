/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Nimber.SimplestExtension.Closure
public import CombinatorialGames.Nimber.SimplestExtension.Polynomial
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Nimbers are algebraically closed

This file proves the last part of the simplest extension theorem (see
`CombinatorialGames.Nimber.SimplestExtension.Basic`), and deduces as a corollary that the nimbers
are algebraically closed.
-/

universe u

open Order Ordinal Polynomial Set

public section

namespace Nimber

/-! ### Lemmas relating rings to `leastNoRoots` -/

-- TODO: We're missing `IsRing.root_lt` which would avoid the duplication.
private theorem IsField.eval_eq_of_lt {n : ℕ} {x : Nimber} (h : IsField x)
    (h' : .some (X ^ n) ≤ leastNoRoots x) {p : Nimber[X]}
    (hpn : p.degree < n) (hpk : ∀ k, p.coeff k < x) : p.eval x = oeval x p := by
  have hx₁ := h.one_lt
  have hx₀ := h.zero_lt
  induction n generalizing p with
  | zero => simp_all
  | succ n IH =>
    replace IH := @IH (h'.trans' (by simp))
    have hx : ∗(x.val ^ n) = x ^ n := by
      refine le_antisymm (le_of_forall_lt_imp_ne fun y hy ↦ ?_) (pow_le_of_forall_ne fun f ↦ ?_)
      · obtain ⟨p, hpn, hpk, rfl⟩ := eq_oeval_of_lt_pow hx₀.ne' hy
        have : p.coeff n = 0 := p.coeff_eq_zero_of_degree_lt hpn
        rw [WithBot.natCast_eq_coe] at hpn
        rw [← IH hpn hpk, ← Nimber.add_eq_zero.ne]
        suffices eval x (p + X ^ n) ≠ 0 by simpa
        have hpq : p.degree < (X ^ n : Nimber[X]).degree := by simpa
        have hqn : (p + X ^ n).degree = (n : WithBot ℕ) :=
          (degree_add_eq_right_of_degree_lt hpq).trans (degree_X_pow _)
        have hq₀ : p + X ^ n ≠ 0 := fun h ↦ by
          have := h ▸ hqn
          rw [WithBot.natCast_eq_coe] at this
          exact WithBot.bot_ne_coe this
        refine fun hq ↦ (h.root_lt ?_ ?_ ((mem_roots hq₀).2 hq)).false
        · apply h'.trans_lt'
          rw [WithTop.coe_lt_coe]
          apply Lex.lt_of_degree_lt
          simp [hqn]
        · aesop
      · have hm : (∏ i, (X + C (f i).1)).Monic := by simp [Monic, leadingCoeff_prod]
        have hq : (∏ i, (X + C (f i).1)).degree = (n : WithBot ℕ) := by
          rw [degree_prod_of_monic] <;> simp [Monic]
        have hq' : (X ^ n + ∏ i, (X + C (f i).1)).degree < n := by
          rw [← CharTwo.sub_eq_add]
          convert degree_sub_lt .. <;> simp_all
        have H : ∀ k, (X ^ n + ∏ i, (X + C (f i).1)).coeff k < x := by
          refine h.coeff_add_lt (coeff_X_pow_lt _ hx₁) <| h.coeff_prod_lt fun y hy ↦ ?_
          have : (f y).1 < x := (f y).2
          apply h.coeff_add_lt <;> aesop (add simp [coeff_X, coeff_C])
        replace IH := IH hq' H
        simp only [eval_add, eval_X, eval_pow, eval_prod, eval_C] at IH
        exact IH ▸ (oeval_lt_pow H hq').ne
    rw [Nat.cast_add_one, WithBot.natCast_eq_coe, WithBot.lt_add_one] at hpn
    obtain ⟨a, q, rfl, hqn⟩ := eq_add_C_mul_X_pow_of_degree_le hpn
    have hqn' := hqn
    have hqk (k) : q.coeff k < x := by
      obtain hk | hk := lt_or_ge k n
      · convert hpk k using 1
        aesop
      · rwa [q.coeff_eq_zero_of_degree_lt (hqn'.trans_le (mod_cast hk))]
    rw [eval_add, eval_mul, eval_C, eval_X_pow, add_comm q, oeval_C_mul_X_pow_add hqn,
      IH hqn' hqk, (h.pow n).mul_add_eq_of_lt', mul_comm, eq_comm, ← hx]
    · rw [add_comm]
      congr
      cases n with
      | zero => simp
      | succ n =>
        have hxn : val x ≤ val x ^ (n + 1) := by
          rw [← opow_natCast]
          exact left_le_opow _ (mod_cast n.succ_pos)
        refine (h.pow (n + 1)).mul_eq_of_lt h.toIsGroup h.toIsGroup hxn le_rfl ?_
          @h.inv_lt fun a b ha hb ↦ ?_
        · convert hpk (n + 1)
          simpa using q.coeff_eq_zero_of_degree_lt hqn
        · obtain ⟨p, hpn, hpk, rfl⟩ := eq_oeval_of_lt_pow hx₀.ne' ha
          rw [WithBot.natCast_eq_coe, WithBot.coe_add_one, WithBot.lt_add_one] at hpn
          have hpn' : (p * C b).degree ≤ n := by compute_degree!
          have H : ∀ k, (p * C b).coeff k < x := by
            simp_rw [coeff_mul_C]
            exact fun k ↦ h.mul_lt (hpk k) hb
          simp_rw [Nat.cast_add_one, WithBot.natCast_eq_coe, WithBot.lt_add_one] at IH
          rw [← IH hpn hpk, ← eval_C (a := b), ← eval_mul, IH hpn' H]
          apply oeval_lt_pow H
          simpa using hpn'
    · exact oeval_lt_pow hqk hqn

theorem IsRing.eval_eq_of_lt {n : ℕ} {x : Nimber} (h : IsRing x)
    (h' : .some (X ^ n) ≤ leastNoRoots x) {p : Nimber[X]}
    (hpn : p.degree < n) (hpk : ∀ k, p.coeff k < x) : p.eval x = oeval x p := by
  match n with
  | 0 => simp_all
  | 1 =>
    rw [Nat.cast_one, Nat.WithBot.lt_one_iff_le_zero] at hpn
    rw [eq_C_of_degree_le_zero hpn]
    simp
  | n + 2 =>
    apply (h.toIsField_of_X_sq_lt_leastNoRoots (h'.trans' _)).eval_eq_of_lt h' hpn hpk
    simp

theorem IsRing.pow_mul_eq {n : ℕ} {x y : Nimber} (h : IsRing x)
    (h' : .some (X ^ (n + 1)) ≤ leastNoRoots x) (hy : y < x) :
    x ^ n * y = ∗(x.val ^ n * y.val) := by
  have hx₁ := h.one_lt
  conv_lhs => rw [← eval_X_pow, ← eval_C (a := y), ← eval_mul]
  rw [h.eval_eq_of_lt h', mul_comm, oeval_C_mul_X_pow]
  · compute_degree!
  · have := zero_lt_one.trans hx₁
    aesop

theorem IsRing.pow_eq {n : ℕ} {x y : Nimber} (h : IsRing x)
    (h' : .some (X ^ (n + 1)) ≤ leastNoRoots x) (hy : y < x) :
    x ^ n = ∗(x.val ^ n) := by
  obtain hx₁ | hx₁ := le_or_gt x 1
  · have := le_one_iff.1 hx₁; aesop
  · simpa using h.pow_mul_eq h' hx₁

proof_wanted leastNoRoots_omega0 : leastNoRoots (∗ω) = .some (X ^ 3 + C (∗2))

/-! ### Algebraically closed fields -/

/-- A nimber `x` is algebraically closed when `IsRing x`, and every non-constant polynomial in the
nimbers with coefficients less than `x` has a root that's less than `x`. Note that `0` and `1` are
algebraically closed under this definition.

For simplicity, the constructor takes a `0 < p.degree` assumption. The theorem
`IsAlgClosed.exists_root` proves that this theorem applies (vacuously) when `p = 0` as well. -/
structure IsAlgClosed (x : Nimber) extends IsField x where
  exists_root' ⦃p : Nimber[X]⦄ (hp₀ : 0 < p.degree) (hp : ∀ k, p.coeff k < x) : ∃ r < x, p.IsRoot r
  inv_lt' := (by
    intro y hy0 hyx
    let p : toIsRing.toSubring[X] := C ⟨y, hyx⟩ * X - 1
    have hpd : 0 < (p.map toIsRing.toSubring.subtype).degree :=
      degree_pos_of_root (ne_of_apply_ne (·.coeff 0) (by simp [p]))
        (show IsRoot _ y⁻¹ by simp [hy0, p])
    have hpp (k : ℕ) : (p.map toIsRing.toSubring.subtype).coeff k < x :=
      (coeff_map toIsRing.toSubring.subtype k).trans_lt (p.coeff k).2
    obtain ⟨r, hrx, hr⟩ := exists_root' hpd hpp
    refine Eq.trans_lt ?_ hrx
    simpa [sub_eq_zero, mul_eq_one_iff_inv_eq₀ hy0, p] using hr)

theorem IsAlgClosed.exists_root {x : Nimber} (h : IsAlgClosed x) {p : Nimber[X]}
    (hp₀ : p.degree ≠ 0) (hp : ∀ n, p.coeff n < x) : ∃ r < x, p.IsRoot r := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · aesop
  · apply h.exists_root' _ hp
    cases _ : p.degree <;> simp_all [Nat.pos_iff_ne_zero]

theorem IsAlgClosed.leastNoRoots_eq_top {x : Nimber} (h : IsAlgClosed x) :
    leastNoRoots x = ⊤ := by
  rw [WithTop.eq_top_iff_forall_ne]
  intro p hp
  replace hp := WithTop.eq_untop hp
  generalize_proofs ht at hp
  obtain ⟨r, hr, hr'⟩ := h.exists_root (degree_leastNoRoots_pos ht).ne' (coeff_leastNoRoots_lt ht)
  exact not_isRoot_leastNoRoots_of_lt ht hr hr'

theorem isAlgClosed_iff_leastNoRoots_eq_top {x : Nimber} (h : IsRing x) :
    IsAlgClosed x ↔ leastNoRoots x = ⊤ where
  mp := IsAlgClosed.leastNoRoots_eq_top
  mpr hx := { toIsRing := h, exists_root' _p hp₀ hpk :=
    exists_root_of_lt_leastNoRoots hp₀.ne' hpk (hx ▸ WithTop.coe_lt_top _) }

protected theorem IsAlgClosed.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsAlgClosed x)
    (ne : s.Nonempty) (bdd : BddAbove s) : IsAlgClosed (sSup s) := by
  rw [isAlgClosed_iff_leastNoRoots_eq_top, ← top_le_iff]
  · exact le_leastNoRoots_sSup fun x hx ↦ (H x hx).leastNoRoots_eq_top.ge
  · exact .sSup (fun x hx ↦ (H x hx).toIsRing) ne bdd

protected theorem IsAlgClosed.iSup {ι} [Nonempty ι] {f : ι → Nimber} (H : ∀ i, IsAlgClosed (f i))
    (bdd : BddAbove (range f) := by apply Nimber.bddAbove_of_small) : IsAlgClosed (⨆ i, f i) :=
  IsAlgClosed.sSup (by simpa) (range_nonempty f) bdd

theorem IsAlgClosed.eval_eq_of_lt {x : Nimber} (h : IsAlgClosed x)
    {p : Nimber[X]} (hpk : ∀ k, p.coeff k < x) : p.eval x = oeval x p :=
  h.toIsRing.eval_eq_of_lt (n := p.natDegree + 1) (by simp [h.leastNoRoots_eq_top])
    (by simpa using degree_le_natDegree) hpk

theorem IsAlgClosed.pow_mul_eq {n : ℕ} {x y : Nimber} (h : IsAlgClosed x) (hy : y < x) :
    x ^ n * y = ∗(x.val ^ n * y.val) :=
  h.toIsRing.pow_mul_eq (le_top.trans_eq h.leastNoRoots_eq_top.symm) hy

theorem IsAlgClosed.pow_eq {n : ℕ} {x : Nimber} (h : IsAlgClosed x) :
    x ^ n = ∗(x.val ^ n) :=
  h.toIsRing.pow_eq (le_top.trans_eq h.leastNoRoots_eq_top.symm)

/-- If `x` is a field, to prove it algebraically closed, it suffices to check
*monic* polynomials. -/
theorem IsAlgClosed.ofMonic {x : Nimber} (h : IsField x)
    (hp : ∀ p : Nimber[X], p.Monic → 0 < p.degree → (∀ k, p.coeff k < x) → ∃ r < x, p.IsRoot r) :
    IsAlgClosed x where
  exists_root' p hp₀ hp' := by
    have hp₀' : p ≠ 0 := by rintro rfl; simp at hp₀
    have hm : (C p.leadingCoeff⁻¹ * p).Monic := by simp [Monic, hp₀']
    have hd : (C p.leadingCoeff⁻¹ * p).degree = p.degree := by compute_degree!
    have := hp _ hm (hd ▸ hp₀) fun k ↦ ?_
    · simp_all
    · rw [coeff_C_mul, inv_mul_eq_div]
      exact h.div_lt (hp' k) (hp' _)
  __ := h

attribute [simp] eval_prod eval_multiset_prod leadingCoeff_prod in
private theorem IsField.isRoot_leastNoRoots {x : Nimber} (h : IsField x) (ht) :
    (x.leastNoRoots.untop ht).IsRoot x := by
  have hx₁ : 1 < x := h.one_lt
  generalize_proofs ht
  let n := (x.leastNoRoots.untop ht).natDegree
  have hn : 1 ≤ n := one_le_natDegree_leastNoRoots _
  have hd := degree_eq_natDegree (leastNoRoots_ne_zero' ht)
  have hld := (X_pow_lt_leastNoRoots_of_le_degree _ hd.ge).le
  have hm := h.monic_leastNoRoots ht
  have hxp : ∀ k, (X ^ n + x.leastNoRoots.untop ht).coeff k < x :=
    h.coeff_add_lt (coeff_X_pow_lt _ hx₁) (coeff_leastNoRoots_lt _)
  rw [IsRoot, ← add_right_inj (x ^ n), add_zero]
  apply le_antisymm
  · have hp : (X ^ n + x.leastNoRoots.untop ht).degree < (n : WithBot ℕ) := by
      rw [← CharTwo.sub_eq_add]
      apply (degree_sub_lt ..).trans_eq <;> aesop
    conv_lhs => left; rw [← eval_X_pow]
    rw [← eval_add, h.eval_eq_of_lt hld hp hxp]
    apply le_of_forall_lt_imp_ne
    rw [forall_lt_oeval_iff hxp]
    intro q hq hqk
    have hq' : q.degree < n := (Lex.degree_mono hq.le).trans_lt hp
    rw [← h.eval_eq_of_lt hld hq' hqk, ne_eq, ← add_right_inj (x ^ n), add_self,
      ← eval_X_pow, ← eval_add]
    · intro hx
      have hr : x ∈ (X ^ n + q).roots := by
        rwa [mem_roots]
        rw [ne_eq, CharTwo.add_eq_zero]
        apply_fun degree
        apply (hq'.trans_le _).ne'
        simp
      apply (h.root_lt _ (h.coeff_add_lt (coeff_X_pow_lt _ hx₁) hqk) hr).false
      rw [← WithTop.coe_untop _ ht, WithTop.coe_lt_coe]
      apply Lex.X_pow_add_lt hm
      simpa
  · refine pow_le_of_forall_ne fun f hf ↦ ?_
    rw [add_right_inj] at hf
    have hf' : ∏ i, (x + (f i)) = eval x (∏ i, (X + C (f i).1)) := by simp
    rw [hf', ← Nimber.add_eq_zero, ← eval_add] at hf
    apply (h.root_lt _ _ ((mem_roots _).2 hf)).false
    · conv_rhs => rw [← WithTop.coe_untop _ ht]
      rw [WithTop.coe_lt_coe, add_comm, ← CharTwo.sub_eq_add]
      apply Lex.lt_of_degree_lt (degree_sub_lt _ (leastNoRoots_ne_zero' ht) _)
      · rw [degree_prod_of_monic] <;> aesop (add simp [Monic])
      · aesop
    · apply h.coeff_add_lt (h.coeff_prod_lt _) (coeff_leastNoRoots_lt _)
      aesop
    · rw [ne_eq, CharTwo.add_eq_zero]
      let i : Fin n := ⟨0, natDegree_leastNoRoots_pos ht⟩
      apply_fun eval (f i).1
      rw [eval_prod, Finset.prod_eq_zero (Finset.mem_univ i), ne_comm]
      · exact not_isRoot_leastNoRoots_of_lt _ (f i).2
      · simp

/-- The fourth **simplest extension theorem**: if `x` is a ring that isn't algebraically closed,
then `x` is the root of some polynomial with coefficients `< x`. -/
theorem IsRing.isRoot_leastNoRoots {x : Nimber} (h : IsRing x) (ht) :
    (x.leastNoRoots.untop ht).IsRoot x := by
  by_cases hf : IsField x
  · exact hf.isRoot_leastNoRoots ht
  · rw [(WithTop.untop_eq_iff ht).2 (h.leastNoRoots_eq_of_not_isField hf)]
    simp [h.ne_zero]

theorem IsRing.pow_degree_leastNoRoots {x : Nimber} (h : IsRing x) (ht) {n : ℕ}
    (hn : (x.leastNoRoots.untop ht).degree = n) : IsRing (of (val x ^ n)) := by
  obtain rfl | hn1 := eq_or_ne n 1
  · simpa using h
  cases n with
  | zero => simpa [hn] using degree_leastNoRoots_pos ht
  | succ n =>
    have hd := (X_pow_lt_leastNoRoots_of_le_degree ht hn.ge).le
    have hn' : 2 ≤ n + 1 := by lia
    have hf : IsField x := h.toIsField_of_X_sq_lt_leastNoRoots
      (X_pow_lt_leastNoRoots_of_le_degree ht (hn ▸ mod_cast hn')).le
    have hem : (hf.embed _ (coeff_leastNoRoots_lt ht)).Monic := by
      simpa using hf.monic_leastNoRoots _
    refine ⟨h.pow _, fun y z hy hz ↦ ?_, ne_of_gt (by simp [h.one_lt])⟩
    obtain ⟨py, hyd, hyc, rfl⟩ := eq_oeval_of_lt_pow h.ne_zero hy
    obtain ⟨pz, hzd, hzc, rfl⟩ := eq_oeval_of_lt_pow h.ne_zero hz
    rw [← h.eval_eq_of_lt hd hyd hyc, ← h.eval_eq_of_lt hd hzd hzc, ← hf.map_embed hyc,
      ← hf.map_embed hzc, ← eval_mul, ← Polynomial.map_mul, ← modByMonic_add_div (_ * _),
      Polynomial.map_add, eval_add, Polynomial.map_mul, eval_mul,
      hf.map_embed (coeff_leastNoRoots_lt ht), h.isRoot_leastNoRoots ht, zero_mul, add_zero,
      h.eval_eq_of_lt hd _ (by simp)]
    on_goal 1 => apply oeval_lt_pow (by simp)
    all_goals exact (degree_map ..).trans_lt <| (degree_modByMonic_lt _ hem).trans_le (by simp [hn])

theorem IsField.pow_degree_leastNoRoots {x : Nimber} (hf : IsField x) (ht) {n : ℕ}
    (hn : (x.leastNoRoots.untop ht).degree = n) : IsField (of (val x ^ n)) := by
  obtain rfl | hn1 := eq_or_ne n 1
  · simpa using hf
  cases n with
  | zero => simpa [hn] using degree_leastNoRoots_pos ht
  | succ n =>
    have hxr := hf.toIsRing.pow_degree_leastNoRoots _ hn
    refine ⟨hxr, fun y hy0 hy ↦ ?_⟩
    obtain ⟨hc, hm⟩ : ∃ hc, Irreducible (hf.embed _ hc) :=
      ⟨coeff_leastNoRoots_lt ht, irreducible_embed_leastNoRoots hf ht⟩
    have hxn : x < of (val x ^ (n + 1)) := by
      simpa using (pow_lt_pow_iff_right₀ (a := x.val) hf.one_lt).2 (show 1 < n + 1 by lia)
    have hcc := Set.Iio_subset_Iio hxn.le
    let r : hf.toSubfield[X] →+* hxr.toSubring := eval₂RingHom (Subring.inclusion hcc) ⟨x, hxn⟩
    have hoc : hxr.toSubring.subtype.comp (Subring.inclusion hcc) = hf.toSubfield.subtype := rfl
    have hr : (RingHom.ker r).IsMaximal := by
      have hm' := PrincipalIdealRing.isMaximal_of_irreducible hm
      refine hm'.eq_of_le (RingHom.ker_ne_top r) ?_ ▸ hm'
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
        ← Subtype.val_inj, ← Subring.subtype_apply, Subring.coe_zero,
        coe_eval₂RingHom, Polynomial.hom_eval₂, ← eval_map, hoc, map_embed]
      exact hf.isRoot_leastNoRoots ht
    obtain ⟨py, hyd, hyc, rfl⟩ := eq_oeval_of_lt_pow hf.ne_zero hy
    rw [← hf.eval_eq_of_lt (X_pow_lt_leastNoRoots_of_le_degree ht hn.ge).le hyd hyc,
      ← hf.map_embed hyc, ← hoc, eval_map,
      show eval₂ _ x _ = eval₂ _ (hxr.toSubring.subtype ⟨x, hxn⟩) _ from rfl,
      ← Polynomial.hom_eval₂, ← coe_eval₂RingHom] at hy0 ⊢
    rw [← map_zero hxr.toSubring.subtype, hxr.toSubring.subtype_injective.ne_iff,
      ne_eq, ← RingHom.mem_ker] at hy0
    obtain ⟨i, s, hs, hi⟩ := hr.exists_inv hy0
    rw [inv_eq_of_mul_eq_one_left]
    · exact (r i).2
    · replace hi := congrArg r hi
      rw [map_add, map_mul, hs] at hi
      simpa using congrArg hxr.toSubring.subtype hi

theorem IsAlgClosed.isRing_opow_omega0 {t : Nimber} (ht : IsAlgClosed t) :
    IsRing (of (val t ^ ω)) where
  toIsGroup := ht.toIsGroup.opow _
  ne_one := ne_of_gt (by simp [ht.one_lt])
  mul_lt y z hy hz := by
    obtain ⟨py, hyd, rfl⟩ := eq_oeval_of_lt_opow_omega0 hy
    obtain ⟨pz, hzd, rfl⟩ := eq_oeval_of_lt_opow_omega0 hz
    rw [← ht.eval_eq_of_lt hyd, ← ht.eval_eq_of_lt hzd,
      ← eval_mul, ht.eval_eq_of_lt (ht.coeff_mul_lt hyd hzd)]
    exact oeval_lt_opow_omega0 (ht.coeff_mul_lt hyd hzd)

/-! ### Nimbers are algebraically closed -/

open Pointwise

private instance (x : Nimber.{u}) : Small.{u} {p : Nimber[X] // ∀ k, p.coeff k < x} := by
  refine small_of_injective (β := ℕ → Iio x) (f := fun p k ↦ ⟨_, p.2 k⟩) fun p q h ↦ ?_
  ext k
  simpa using congrFun h k

/-- The set of roots of polynomials with coefficients less than `x`. -/
private def rootSet (x : Nimber) : Set Nimber :=
  ⋃ p : {p : Nimber[X] // ∀ k, p.coeff k < x}, p.1.roots.toFinset

private instance (x : Nimber.{u}) : Small.{u} x.rootSet :=
  small_iUnion _

/-- Returns the smallest `IsAlgClosed` that's at least `x`. -/
noncomputable def algClosure (x : Nimber) : Nimber :=
  sSup (succ '' rootSet x.fieldClosure)

set_option backward.isDefEq.respectTransparency false in
mutual

private theorem isAlgebraic_of_not_isField {x y : Nimber} (h : y ≤ algClosure x)
    (hyf : ¬IsField y) : IsAlgebraic (IsField.fieldClosure x).toSubfield y := by
  obtain rfl | hy0 := eq_or_ne y 0
  · exact isAlgebraic_zero
  obtain rfl | hy1 := eq_or_ne y 1
  · exact isAlgebraic_one
  by_cases! hyg : ¬y.IsGroup
  · obtain ⟨y1, hy1, y2, hy2, rfl⟩ := exists_add_of_not_isGroup hyg hy0
    exact (isAlgebraic_of_lt (hy1.trans_le h)).add (isAlgebraic_of_lt (hy2.trans_le h))
  by_cases! hyr : ¬y.IsRing
  · obtain ⟨y1, hy1, y2, hy2, rfl⟩ := hyg.exists_mul_of_not_isRing hyr hy1
    exact (isAlgebraic_of_lt (hy1.trans_le h)).mul (isAlgebraic_of_lt (hy2.trans_le h))
  have hy := hyr.inv_lt_self_of_not_isField hyf
  exact inv_inv y ▸ (isAlgebraic_of_lt (hy.trans_le h)).inv
termination_by (y, 0)

private theorem isAlgebraic_of_leastNoRoots {x y : Nimber} (h : y ≤ x.algClosure)
    (ht : leastNoRoots y ≠ ⊤) : IsAlgebraic (IsField.fieldClosure x).toSubfield y := by
  by_cases! hyf : ¬y.IsField
  · exact isAlgebraic_of_not_isField h hyf
  by_cases! hxy : y < x.fieldClosure
  · exact isAlgebraic_algebraMap (R := IsField.toSubfield _) ⟨y, hxy⟩
  have hcf : x.fieldClosure.IsField := IsField.fieldClosure x
  let alg : Algebra hcf.toSubfield hyf.toSubfield :=
    (Subfield.inclusion (Iio_subset_Iio hxy)).toAlgebra
  have tower : IsScalarTower hcf.toSubfield hyf.toSubfield Nimber := ⟨fun _ _ _ => mul_assoc ..⟩
  have int : Algebra.IsAlgebraic hcf.toSubfield hyf.toSubfield :=
    ⟨fun z => have := z.2; (isAlgebraic_of_lt (z.2.trans_le h)).of_ringHom_of_comp_eq
      (RingHom.id _) (algebraMap _ _) Function.surjective_id (RingHom.injective _) rfl⟩
  refine IsAlgebraic.restrictScalars _
    ⟨hyf.embed (y.leastNoRoots.untop ht) (coeff_leastNoRoots_lt ht), ?_, ?_⟩
  · exact ne_of_apply_ne (Polynomial.map (Subfield.subtype _)) (by simp)
  · rw [aeval_def, Subfield.algebraMap_ofSubfield, eval₂_eq_eval_map, hyf.map_embed]
    exact hyf.isRoot_leastNoRoots ht
termination_by (y, 1)

private theorem isAlgebraic_of_lt {x y : Nimber} (h : y < algClosure x) :
    IsAlgebraic (IsField.fieldClosure x).toSubfield y := by
  by_cases! hyf : ¬y.IsField
  · exact isAlgebraic_of_not_isField h.le hyf
  by_cases! hxy : y < x.fieldClosure
  · exact isAlgebraic_algebraMap (R := IsField.toSubfield _) ⟨y, hxy⟩
  obtain ⟨c, hc, hyc⟩ : ∃ c ∈ x.fieldClosure.rootSet, y < succ c :=
    ((lt_csSup_iff' (bddAbove_of_small _)).trans exists_mem_image).1 h
  rw [rootSet, mem_iUnion] at hc
  obtain ⟨⟨p, hp⟩, hc⟩ := hc
  rw [SetLike.mem_coe, Multiset.mem_toFinset, mem_roots', IsRoot.def] at hc
  have int : IsIntegral hyf.toSubfield c := IsAlgebraic.isIntegral
    ⟨hyf.embed p fun k => (hp k).trans_le hxy,
      ne_of_apply_ne (Polynomial.map (Subfield.subtype _)) (by simp [hc.1]),
      by simp [aeval_def, Subfield.algebraMap_ofSubfield, eval₂_eq_eval_map, hc.2]⟩
  have ht : leastNoRoots y ≤ (minpoly hyf.toSubfield c).map (Subfield.subtype _) :=
    leastNoRoots_le_of_not_isRoot (by simp [minpoly.degree_pos int]) (by simp) fun r hr => by
      change ¬Polynomial.IsRoot _ (hyf.toSubfield.subtype ⟨r, hr⟩)
      rw [isRoot_map_iff (RingHom.injective _)]
      apply (minpoly.irreducible int).not_isRoot_of_natDegree_ne_one
      simp [minpoly.natDegree_eq_one_iff, Subfield.algebraMap_ofSubfield,
        mt succ_le_of_lt hyc.not_ge]
  exact isAlgebraic_of_leastNoRoots h.le (ne_of_lt (ht.trans_lt (WithTop.coe_lt_top _)))
termination_by (y, 2)

end

theorem lt_algClosure_iff_isAlgebraic {x y : Nimber} :
    y < algClosure x ↔ IsAlgebraic (IsField.fieldClosure x).toSubfield y := by
  induction y using WellFoundedLT.induction with | ind y ih =>
  refine ⟨isAlgebraic_of_lt, fun h => ?_⟩
  obtain ⟨p, hp0, hpr⟩ := h
  refine lt_csSup_of_lt (bddAbove_of_small _) (mem_image_of_mem _ ?_) (lt_succ y)
  apply mem_iUnion_of_mem ⟨p.map (Subfield.subtype _), by simp⟩
  simp [hp0, ← Subfield.algebraMap_ofSubfield, hpr]

@[simp]
theorem le_algClosure (x : Nimber) : x ≤ algClosure x :=
  le_of_forall_lt fun c hc => lt_algClosure_iff_isAlgebraic.2 <|
    isAlgebraic_algebraMap (R := IsField.toSubfield _) ⟨c, hc.trans_le (le_fieldClosure x)⟩

theorem IsAlgClosed.algClosure (x : Nimber) : (algClosure x).IsAlgClosed where
  __ := Classical.byContradiction fun h => lt_irrefl x.algClosure
    (lt_algClosure_iff_isAlgebraic.2 (isAlgebraic_of_not_isField le_rfl h))
  exists_root' p hd hp := by
    by_contra! hpr
    have ht : leastNoRoots x.algClosure ≤ p := leastNoRoots_le_of_not_isRoot hd hp hpr
    exact lt_irrefl x.algClosure (lt_algClosure_iff_isAlgebraic.2
      (isAlgebraic_of_leastNoRoots le_rfl (ne_of_lt (ht.trans_lt (WithTop.coe_lt_top _)))))

theorem IsAlgClosed.algClosure_le_iff {x y : Nimber} (h : IsAlgClosed x) :
    y.algClosure ≤ x ↔ y ≤ x where
  mp := le_trans (le_algClosure y)
  mpr hyx := le_of_forall_lt fun c hc => by
    obtain ⟨p, hp0, hp⟩ := lt_algClosure_iff_isAlgebraic.1 hc
    rw [aeval_def, eval₂_eq_eval_map] at hp
    exact h.toIsField.root_lt ((WithTop.coe_lt_top _).trans_eq h.leastNoRoots_eq_top.symm)
      (fun k => lt_of_lt_of_le (by simp [Subfield.algebraMap_ofSubfield])
        (h.toIsField.fieldClosure_le_iff.2 hyx)) ((mem_roots (by simp [hp0])).2 hp)

theorem IsAlgClosed.lt_algClosure_iff {x y : Nimber} (h : IsAlgClosed x) :
    x < y.algClosure ↔ x < y :=
  le_iff_le_iff_lt_iff_lt.1 h.algClosure_le_iff

theorem algClosure_mono : Monotone algClosure := by
  intro x y
  rw [(IsAlgClosed.algClosure y).algClosure_le_iff]
  exact (le_algClosure y).trans'

/-- The nimbers are an algebraically closed field. -/
instance : _root_.IsAlgClosed Nimber := by
  refine .of_exists_root Nimber fun p _ hp ↦ ?_
  have hk (k : ℕ) : p.coeff k < algClosure (succ (p.support.sup p.coeff)) := Classical.byCases
    (fun hk => (lt_succ_iff.2 (Finset.le_sup hk)).trans_le (le_algClosure _))
    (fun hk => (notMem_support_iff.1 hk).trans_lt (IsAlgClosed.algClosure _).pos)
  obtain ⟨r, -, hr⟩ := (IsAlgClosed.algClosure _).exists_root hp.degree_pos.ne' hk
  exact ⟨r, hr⟩

/-- TODO: characterize the fields of nimbers below the first transcendental, get this as a
corollary. -/
proof_wanted algClosure_zero : algClosure 0 = ∗(ω ^ ω ^ ω)

/-! ### Square roots -/

/-- The square root of a nimber `x` is the unique value with `(√x)^2 = x`. -/
noncomputable def sqrt : Nimber ≃+* Nimber :=
  (frobeniusEquiv _ 2).symm

@[inherit_doc] scoped prefix:max "√" => sqrt
recommended_spelling "sqrt" for "√" in [sqrt, «term√_»]

theorem sqrt_zero : √0 = 0 := map_zero _
theorem sqrt_one : √1 = 1 := map_one _
theorem sqrt_add (x y : Nimber) : √(x + y) = √x + √y := map_add ..
theorem sqrt_mul (x y : Nimber) : √(x * y) = √x * √y := map_mul ..
theorem sqrt_inj {x y : Nimber} : √x = √y ↔ x = y := sqrt.apply_eq_iff_eq

@[simp] theorem sqrt_sq (x : Nimber) : √(x ^ 2) = x := by simp [sqrt]
@[simp] theorem sq_sqrt (x : Nimber) : √x ^ 2 = x := by simp [sqrt]
@[simp] theorem sqrt_self_mul_self (x : Nimber) : √(x * x) = x := by rw [← pow_two, sqrt_sq]
@[simp] theorem sqrt_mul_sqrt_self (x : Nimber) : √x * √x = x := by rw [← pow_two, sq_sqrt]

theorem sqrt_eq_iff {x y : Nimber} : √y = x ↔ x ^ 2 = y := by
  conv_rhs => rw [← sq_sqrt y, CharTwo.sq_inj, eq_comm]

alias ⟨_, sqrt_eq⟩ := sqrt_eq_iff

theorem IsField.sqrt_lt {x y : Nimber} (h : IsField x) (hy : y < x)
    (hx : .some (X ^ 2 + C y) < leastNoRoots x) : √y < x := by
  apply h.root_lt hx
  · aesop
  · rw [mem_roots]
    · simp
    · apply_fun (coeff · 2)
      simp

theorem IsField.sqrt_lt' {x y : Nimber} (h : IsField x) (hy : y < x)
    (hx : .some (X ^ 2 + X) ≤ leastNoRoots x) : √y < x := by
  apply h.sqrt_lt hy (hx.trans_lt' <| WithTop.coe_lt_coe.2 _)
  use 1
  aesop

end Nimber
end
