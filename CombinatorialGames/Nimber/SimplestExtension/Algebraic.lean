/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Nimber.SimplestExtension.Closure
import CombinatorialGames.Nimber.SimplestExtension.Polynomial
import Mathlib.Algebra.Group.Pointwise.Set.Small
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Nimbers are algebraically closed

This file proves the last part of the simplest extension theorem (see
`CombinatorialGames.Nimber.SimplestExtension.Basic`), and deduces as a corollary that the nimbers
are algebraically closed.
-/

universe u

open Order Ordinal Polynomial Set

/-! ### For Mathlib -/

@[simp]
theorem Ordinal.one_lt_opow {x y : Ordinal} (h : 1 < x) : 1 < x ^ y ↔ y ≠ 0 := by
  obtain ⟨rfl, hy⟩ := eq_zero_or_pos y
  · simp
  · rw [← Ordinal.opow_zero x, Ordinal.opow_lt_opow_iff_right h, pos_iff_ne_zero]

@[simp]
theorem Ordinal.one_lt_pow {x : Ordinal} {n : ℕ} (h : 1 < x) : 1 < x ^ n ↔ n ≠ 0 :=
  mod_cast one_lt_opow (y := n) h

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
      · obtain ⟨p, hpn, hpk, rfl⟩ := eq_oeval_of_lt_opow hx₀.ne' hy
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
        exact IH ▸ (oeval_lt_opow H hq').ne
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
        -- replace h : IsField x := h.toIsField_of_X_sq_lt_leastNoRoots (h'.trans' (by simp))
        refine (h.pow (n + 1)).mul_eq_of_lt h.toIsGroup h.toIsGroup hxn ?_ le_rfl
          @h.inv_lt fun a b ha hb ↦ ?_
        · convert hpk (n + 1)
          simpa using q.coeff_eq_zero_of_degree_lt hqn
        · obtain ⟨p, hpn, hpk, rfl⟩ := eq_oeval_of_lt_opow hx₀.ne' ha
          rw [WithBot.natCast_eq_coe, WithBot.coe_add_one, WithBot.lt_add_one] at hpn
          have hpn' : (p * C b).degree ≤ n := by compute_degree!
          have H : ∀ k, (p * C b).coeff k < x := by
            simp_rw [coeff_mul_C]
            exact fun k ↦ h.mul_lt (hpk k) hb
          simp_rw [Nat.cast_add_one, WithBot.natCast_eq_coe, WithBot.lt_add_one] at IH
          rw [← IH hpn hpk, ← eval_C (a := b), ← eval_mul, IH hpn' H]
          apply oeval_lt_opow H
          simpa using hpn'
    · exact oeval_lt_opow hqk hqn

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
@[mk_iff]
structure IsAlgClosed (x : Nimber) extends IsRing x where
  exists_root' ⦃p : Nimber[X]⦄ (hp₀ : 0 < p.degree) (hp : ∀ k, p.coeff k < x) : ∃ r < x, p.IsRoot r

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
  mpr hx := ⟨h, fun _p hp₀ hpk ↦
    exists_root_of_lt_leastNoRoots hp₀.ne' hpk (hx ▸ WithTop.coe_lt_top _)⟩

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
  have hx₀ : 0 < x := h.zero_lt
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
    obtain ⟨py, hyd, hyc, rfl⟩ := eq_oeval_of_lt_opow h.ne_zero hy
    obtain ⟨pz, hzd, hzc, rfl⟩ := eq_oeval_of_lt_opow h.ne_zero hz
    rw [← h.eval_eq_of_lt hd hyd hyc, ← h.eval_eq_of_lt hd hzd hzc, ← hf.map_embed hyc,
      ← hf.map_embed hzc, ← eval_mul, ← Polynomial.map_mul, ← modByMonic_add_div (_ * _) hem,
      Polynomial.map_add, eval_add, Polynomial.map_mul, eval_mul, hf.map_embed,
      h.isRoot_leastNoRoots ht, zero_mul, add_zero, h.eval_eq_of_lt hd _ (by simp)]
    on_goal 1 => apply oeval_lt_opow (by simp)
    all_goals exact (degree_map ..).trans_lt <|
      (degree_modByMonic_lt _ hem).trans_le (by simp [hn])

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
      simpa using (Ordinal.opow_lt_opow_iff_right hf.one_lt).2
        (Nat.cast_lt.2 (show 1 < n + 1 by lia))
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
    obtain ⟨py, hyd, hyc, rfl⟩ := eq_oeval_of_lt_opow hf.ne_zero hy
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
  ⨆ n : ℕ, (fun y ↦ fieldClosure (sSup <| (succ '' rootSet y)))^[n] x.fieldClosure

@[simp]
theorem le_algClosure (x : Nimber) : x ≤ algClosure x :=
  le_ciSup_of_le (bddAbove_of_small _) 0 (by simp)

private protected theorem IsField.algClosure (x : Nimber) : IsField (algClosure x) := by
  refine IsField.iSup fun n ↦ ?_
  cases n
  · simp
  · rw [Function.iterate_succ_apply']
    simp

private theorem algClosure.root_lt {x r : Nimber} {p : Nimber[X]} (hp₀ : p ≠ 0)
    (hpk : ∀ k, p.coeff k < algClosure x) (hr : p.IsRoot r) : r < algClosure x := by
  simp_rw [algClosure, lt_ciSup_iff (bddAbove_of_small _)] at hpk ⊢
  have hpk' : ∀ k, ∃ a ∈ (range fun n ↦
      (fun y ↦ fieldClosure (sSup <| succ '' rootSet y))^[n] x.fieldClosure), p.coeff k < a :=
    by simpa
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := exists_gt_of_forall_coeff_gt hpk'
  use n + 1
  rw [Function.iterate_succ_apply', ← mem_subfieldClosure_Iio]
  apply Subfield.mem_closure_of_mem
  rw [mem_Iio, ← succ_le_iff]
  apply le_csSup (bddAbove_of_small _) (mem_image_of_mem ..)
  rw [rootSet, mem_iUnion]
  refine ⟨⟨p, hn⟩, ?_⟩
  simp_all

private theorem leastNoRoots_algClosure' {x : Nimber} {p : Nimber[X]} (hp : 0 < p.degree)
    (hpk : ∀ k, p.coeff k < x) (IH : ∀ q < p, 0 < q.degree → ∃ r, q.IsRoot r)
    (hr : ∀ r, ¬ p.IsRoot r) : leastNoRoots (algClosure x) = p := by
  apply le_antisymm
  · exact leastNoRoots_le_of_not_isRoot hp
      (fun k ↦ (hpk k).trans_le (le_algClosure x)) fun r _ ↦ hr r
  · apply le_of_forall_lt_imp_ne
    rw [WithTop.forall_lt_coe]
    intro q hq hq'
    have ht := hq' ▸ WithTop.coe_ne_top
    have hq' : q = x.algClosure.leastNoRoots.untop ht := by simp_rw [← hq', WithTop.untop_coe]
    obtain ⟨r, hr⟩ := IH q hq (hq' ▸ degree_leastNoRoots_pos ht)
    exact not_isRoot_leastNoRoots_of_lt ht
      (algClosure.root_lt (by aesop) (hq' ▸ coeff_leastNoRoots_lt ht) hr) (hq' ▸ hr)

/-- The nimbers are an algebraically closed field. -/
instance : _root_.IsAlgClosed Nimber := by
  suffices H : ∀ p : Nimber[X], 0 < p.degree → ∃ r, p.IsRoot r from
    .of_exists_root _ fun p _ hp ↦ H _ hp.degree_pos
  intro p
  induction p using WellFoundedLT.induction with | ind p IH
  intro hp
  by_contra! hr
  obtain ⟨x, hpk⟩ : ∃ x, ∀ k, p.coeff k < x := by
    refine ⟨⨆ k, succ (p.coeff k), fun k ↦ ?_⟩
    rw [lt_ciSup_iff' (bddAbove_of_small _)]
    exact ⟨k, lt_succ _⟩
  have ht := leastNoRoots_algClosure' hp hpk IH hr
  have hp' := (IsField.algClosure x).isRoot_leastNoRoots (ht ▸ WithTop.coe_ne_top)
  simp_rw [ht, WithTop.untop_coe] at hp'
  exact hr _ hp'

/-- TODO: characterize the fields of nimbers below the first transcendental, get this as a
corollary. -/
proof_wanted algClosure_zero : algClosure 0 = ∗(ω ^ ω ^ ω)

end Nimber
