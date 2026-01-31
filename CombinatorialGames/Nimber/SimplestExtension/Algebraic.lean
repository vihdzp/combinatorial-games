/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
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

namespace Finsupp

variable {α β : Type*} [Zero β]

end Finsupp

-- TODO: can we golf this using `finite_range_coeff`?
private theorem Polynomial.exists_gt_of_forall_coeff_gt {s : Set Nimber} {p : Nimber[X]}
    (h : ∀ k, ∃ a ∈ s, p.coeff k < a) : ∃ a ∈ s, ∀ k, p.coeff k < a := by
  choose f hf using h
  obtain ⟨c, hc⟩ := ((Finset.range (p.natDegree + 1)).image f).exists_maximal (by simp)
  have hc' := hc.1
  simp_rw [Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff] at hc'
  obtain ⟨n, hn, rfl⟩ := hc'
  refine ⟨_, (hf n).1, fun k ↦ ?_⟩
  obtain hk | hk := le_or_gt k p.natDegree
  · apply (hf k).2.trans_le (hc.isGreatest.2 _)
    aesop
  · rw [p.coeff_eq_zero_of_natDegree_lt hk]
    exact (hf n).2.bot_lt

namespace Nimber

/-! ### n-th degree closed fields -/

/-- A nimber `x` is `n`-th degree closed when `IsRing x`, and every non-constant polynomial in the
nimbers with degree less or equal to `n` and coefficients less than `x` has a root that's less than
`x`.

We don't extend `IsField x`, as for `1 ≤ n`, this predicate implies it.

For simplicity, the constructor takes a `0 < p.degree` assumption. The theorem
`IsNthDegreeClosed.exists_root` proves that this theorem applies (vacuously) when `p = 0` as well.
-/
@[mk_iff]
structure IsNthDegreeClosed (n : ℕ) (x : Nimber) extends IsRing x where
  exists_root' ⦃p : Nimber[X]⦄ (hp₀ : 0 < p.degree) (hpn : p.degree ≤ n) (hp : ∀ k, p.coeff k < x) :
    ∃ r < x, p.IsRoot r

theorem IsNthDegreeClosed.exists_root {n : ℕ} {x : Nimber}
    (h : IsNthDegreeClosed n x) {p : Nimber[X]}
    (hp₀ : p.degree ≠ 0) (hpn : p.degree ≤ n) (hp : ∀ k, p.coeff k < x) : ∃ r < x, p.IsRoot r := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · aesop
  · apply h.exists_root' _ hpn hp
    cases _ : p.degree <;> simp_all [Nat.pos_iff_ne_zero]

theorem IsNthDegreeClosed.le {m n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x) (hmn : m ≤ n) :
    IsNthDegreeClosed m x where
  exists_root' _p hp₀ hpm := h.exists_root' hp₀ (hpm.trans (mod_cast hmn))
  __ := h.toIsRing

protected theorem IsNthDegreeClosed.sSup {n : ℕ} {s : Set Nimber}
    (H : ∀ x ∈ s, IsNthDegreeClosed n x) (ne : s.Nonempty) (bdd : BddAbove s) :
    IsNthDegreeClosed n (sSup s) := by
  refine ⟨IsRing.sSup (fun x hx ↦ (H x hx).toIsRing) ne bdd, fun p hp₀ hpn hp ↦ ?_⟩
  simp_rw [lt_csSup_iff bdd ne] at *
  obtain ⟨c, hc, hc'⟩ := exists_gt_of_forall_coeff_gt hp
  obtain ⟨r, hr, hr'⟩ := (H _ hc).exists_root' hp₀ hpn fun m ↦ hc' _
  exact ⟨r, ⟨_, hc, hr⟩, hr'⟩

protected theorem IsNthDegreeClosed.iSup {n : ℕ} {ι} [Nonempty ι] {f : ι → Nimber}
    (H : ∀ i, IsNthDegreeClosed n (f i))
    (bdd : BddAbove (range f) := by apply Nimber.bddAbove_of_small) :
    IsNthDegreeClosed n (⨆ i, f i) :=
  IsNthDegreeClosed.sSup (by simpa) (range_nonempty f) bdd

/-- If `x` is a field, to prove it `n`-th degree closed, it suffices to check *monic* polynomials of
degree less or equal to `n`. -/
theorem IsNthDegreeClosed.ofMonic {n : ℕ} {x : Nimber} (h : IsField x)
    (hp : ∀ p : Nimber[X], p.Monic → 0 < p.degree → p.degree ≤ n → (∀ k, p.coeff k < x) →
      ∃ r < x, p.IsRoot r) : IsNthDegreeClosed n x where
  exists_root' p hp₀ hpn hp' := by
    have hp₀' : p ≠ 0 := by rintro rfl; simp at hp₀
    have hm : (C p.leadingCoeff⁻¹ * p).Monic := by simp [Monic, hp₀']
    have hd : (C p.leadingCoeff⁻¹ * p).degree = p.degree := by compute_degree!
    have := hp _ hm (hd ▸ hp₀) (hd ▸ hpn) fun k ↦ ?_
    · simp_all
    · rw [coeff_C_mul, inv_mul_eq_div]
      exact h.div_lt (hp' k) (hp' _)
  __ := h

@[simp]
theorem isNthDegreeClosed_zero_iff_isRing {x : Nimber} : IsNthDegreeClosed 0 x ↔ IsRing x := by
  refine ⟨IsNthDegreeClosed.toIsRing, fun h ↦ ⟨h, fun p ↦ ?_⟩⟩
  cases p.degree <;> aesop

theorem IsNthDegreeClosed.toIsField {n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x) (hn : 1 ≤ n) :
    IsField x := by
  refine ⟨h.toIsRing, fun y hy₀ hy ↦ ?_⟩
  have hp : degree (C y * (X : Nimber[X]) + 1) = 1 := by compute_degree!
  have ⟨r, hr, hr₀⟩ := h.exists_root (hp ▸ one_ne_zero) (by simpa [hp]) fun k ↦ ?_
  · convert hr
    apply inv_eq_of_mul_eq_one_right
    rw [← Nimber.add_eq_zero]
    simpa using hr₀
  · obtain hk | hk := le_or_gt k 1
    · obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.1 hk <;> simp [coeff_one, h.one_lt, hy]
    · rw [coeff_eq_zero_of_degree_lt]
      · exact h.zero_lt
      · simp_all

@[simp]
theorem isNthDegreeClosed_one_iff_isField {x : Nimber} : IsNthDegreeClosed 1 x ↔ IsField x := by
  refine ⟨(IsNthDegreeClosed.toIsField · le_rfl), (.ofMonic · fun p hm hp₀ hp₁ hp ↦ ?_)⟩
  rw [Polynomial.eq_X_add_C_of_degree_le_one hp₁] at hp ⊢
  have hd : p.natDegree = 1 := by
    apply natDegree_eq_of_degree_eq_some
    rw [← succ_le_iff] at hp₀
    exact hp₁.antisymm hp₀
  rw [Monic, leadingCoeff] at hm
  have := hp 0
  aesop

-- We could have proved this earlier, but going through `IsNthDegreeClosed`
-- gives a much shorter proof.
protected theorem IsField.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsField x)
    (ne : s.Nonempty) (bdd : BddAbove s) :
    IsField (sSup s) := by
  simp_rw [← isNthDegreeClosed_one_iff_isField] at *
  exact IsNthDegreeClosed.sSup H ne bdd

protected theorem IsField.iSup {ι} [Nonempty ι] {f : ι → Nimber} (H : ∀ i, IsField (f i))
    (bdd : BddAbove (range f) := by apply Nimber.bddAbove_of_small) :
    IsField (⨆ i, f i) :=
  IsField.sSup (by simpa) (range_nonempty f) bdd

theorem IsNthDegreeClosed.X_pow_lt_leastNoRoots {n : ℕ} {x : Nimber}
    (h : IsNthDegreeClosed n x) : .some (X ^ (n + 1)) < leastNoRoots x := by
  refine (leastNoRoots_ne_X_pow x _).lt_of_le' (le_of_forall_lt_imp_ne fun p hp hp' ↦ ?_)
  obtain ⟨p, rfl, hp⟩ := WithTop.lt_iff_exists_coe.1 hp
  have h' := hp' ▸ WithTop.coe_ne_top
  have ⟨r, hr, hr'⟩ := h.exists_root' (degree_leastNoRoots_pos h') ?_ (coeff_leastNoRoots_lt h')
  · exact leastNoRoots_not_root_of_lt h' hr hr'
  · simp_rw [← hp']
    simpa using hp

theorem isNthDegreeClosed_iff_X_pow_lt_leastNoRoots {n : ℕ} {x : Nimber} (h : IsRing x) :
    IsNthDegreeClosed n x ↔ .some (X ^ (n + 1)) < leastNoRoots x where
  mp := IsNthDegreeClosed.X_pow_lt_leastNoRoots
  mpr hx := by
    refine ⟨h, fun p hp₀ hpn hpk ↦ exists_root_of_lt_leastNoRoots hp₀.ne' hpk <| hx.trans' ?_⟩
    rw [WithTop.coe_lt_coe]
    apply Lex.lt_of_degree_lt
    simpa

theorem isNthDegreeClosed_iff_X_pow_le_leastNoRoots {n : ℕ} {x : Nimber} (h : IsRing x) :
    IsNthDegreeClosed n x ↔ .some (X ^ (n + 1)) ≤ leastNoRoots x where
  mp hx := hx.X_pow_lt_leastNoRoots.le
  mpr hx := (isNthDegreeClosed_iff_X_pow_lt_leastNoRoots h).2
    (hx.lt_of_ne' (leastNoRoots_ne_X_pow x _))

theorem IsField.X_sq_lt_leastNoRoots {x : Nimber} (h : IsField x) :
    .some (X ^ 2) < leastNoRoots x := by
  rw [← isNthDegreeClosed_one_iff_isField] at h
  exact h.X_pow_lt_leastNoRoots

theorem IsNthDegreeClosed.root_lt {n : ℕ} {x r : Nimber} (h : IsNthDegreeClosed n x) {p : Nimber[X]}
    (hpn : p.degree ≤ n) (hpk : ∀ k, p.coeff k < x) (hr : r ∈ p.roots) : r < x := by
  cases n with
  | zero => cases hpn.not_gt <| degree_pos_of_mem_roots hr
  | succ n =>
    apply (h.toIsField n.succ_pos).root_lt _ hpk hr
    apply (WithTop.coe_lt_coe.2 (Lex.lt_of_degree_lt _)).trans h.X_pow_lt_leastNoRoots
    rw [degree_X_pow]
    exact lt_succ_of_le hpn

theorem IsNthDegreeClosed.eval_eq_of_lt {n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x)
    {p : Nimber[X]} (hpn : p.degree ≤ n) (hpk : ∀ k, p.coeff k < x) :
    p.eval x = oeval x p := by
  have hx₁ := h.one_lt
  have hx₀ := h.zero_lt
  induction n generalizing p with
  | zero => rw [p.eq_C_of_degree_le_zero hpn]; simp
  | succ n IH =>
    have h' := h.le n.le_succ
    have hx : ∗(x.val ^ (n + 1)) = x ^ (n + 1) := by
      refine le_antisymm (le_of_forall_lt_imp_ne fun y hy ↦ ?_) (pow_le_of_forall_ne fun f ↦ ?_)
      · obtain ⟨p, hpn, hpk, rfl⟩ := eq_oeval_of_lt_pow hx₀.ne' hy
        have : p.coeff (n + 1) = 0 := p.coeff_eq_zero_of_degree_lt hpn
        rw [WithBot.natCast_eq_coe, WithBot.coe_add_one, WithBot.lt_add_one] at hpn
        rw [← IH h' hpn hpk, ← Nimber.add_eq_zero.ne]
        suffices eval x (p + X ^ (n + 1)) ≠ 0 by simpa
        have hpq : p.degree < (X ^ (n + 1) : Nimber[X]).degree := by simpa
        have hqn : (p + X ^ (n + 1)).degree = (n + 1 : WithBot ℕ) :=
          (degree_add_eq_right_of_degree_lt hpq).trans (degree_X_pow _)
        have hq₀ : p + X ^ (n + 1) ≠ 0 := fun h ↦ by
          have := h ▸ hqn
          rw [WithBot.natCast_eq_coe, ← WithBot.coe_add_one] at this
          exact WithBot.bot_ne_coe this
        refine fun hq ↦ (h.root_lt hqn.le ?_ ((mem_roots hq₀).2 hq)).false
        aesop
      · have hm : (∏ i, (X + C (f i).1)).Monic := by simp [Monic, leadingCoeff_prod]
        have hq : (∏ i, (X + C (f i).1)).degree = (n + 1 : WithBot ℕ) := by
          rw [degree_prod_of_monic] <;> simp [Monic]
        have hq' : (X ^ (n + 1) + ∏ i, (X + C (f i).1)).degree ≤ n := by
          rw [← lt_succ_iff, ← CharTwo.sub_eq_add]
          convert degree_sub_lt .. <;> simp_all
        have H : ∀ k, (X ^ (n + 1) + ∏ i, (X + C (f i).1)).coeff k < x := by
          refine h.coeff_add_lt (coeff_X_pow_lt _ hx₁) <| h.coeff_prod_lt fun y hy ↦ ?_
          have : (f y).1 < x := (f y).2
          apply h.coeff_add_lt <;> aesop (add simp [coeff_X, coeff_C])
        have IH := IH h' hq' H
        simp only [eval_add, eval_X, eval_pow, eval_prod, eval_C] at IH
        exact IH ▸ (oeval_lt_opow H (lt_succ_of_le hq')).ne
    obtain ⟨a, q, rfl, hqn⟩ := eq_add_C_mul_X_pow_of_degree_le hpn
    have hqn' := hqn
    rw [WithBot.natCast_eq_coe, WithBot.coe_add_one, WithBot.lt_add_one] at hqn'
    have hqk (k) : q.coeff k < x := by
      obtain hk | hk := le_or_gt k n
      · convert hpk k using 1
        aesop
      · rwa [q.coeff_eq_zero_of_degree_lt (hqn'.trans_lt (mod_cast hk))]
    rw [eval_add, eval_mul, eval_C, eval_X_pow, add_comm q, oeval_C_mul_X_pow_add hqn,
      IH h' hqn' hqk, (h.pow (n + 1)).mul_add_eq_of_lt', mul_comm, eq_comm, ← hx]
    · have hxn : val x ≤ val x ^ (n + 1) := by
        rw [← opow_natCast]
        exact left_le_opow _ (mod_cast n.succ_pos)
      rw [add_comm]
      congr
      refine (h.pow (n + 1)).mul_eq_of_lt h.toIsGroup h.toIsGroup hxn ?_ le_rfl
        @(h.toIsField n.succ_pos).inv_lt fun a b ha hb ↦ ?_
      · convert hpk (n + 1)
        simpa using q.coeff_eq_zero_of_degree_lt hqn
      · obtain ⟨p, hpn, hpk, rfl⟩ := eq_oeval_of_lt_pow hx₀.ne' ha
        rw [WithBot.natCast_eq_coe, WithBot.coe_add_one, WithBot.lt_add_one] at hpn
        have hpn' : (p * C b).degree ≤ n := by compute_degree!
        have H : ∀ k, (p * C b).coeff k < x := by
          simp_rw [coeff_mul_C]
          exact fun k ↦ h.mul_lt (hpk k) hb
        rw [← IH h' hpn hpk, ← eval_C (a := b), ← eval_mul, IH h' hpn' H]
        apply oeval_lt_opow H
        simpa using hpn'
    · exact oeval_lt_opow hqk hqn

theorem IsNthDegreeClosed.pow_mul_eq {n : ℕ} {x y : Nimber}
    (h : IsNthDegreeClosed n x) (hy : y < x) : x ^ n * y = ∗(x.val ^ n * y.val) := by
  have hx₁ := h.one_lt
  conv_lhs => rw [← eval_X_pow, ← eval_C (a := y), ← eval_mul]
  rw [h.eval_eq_of_lt, mul_comm, oeval_C_mul_X_pow]
  · compute_degree!
  · have := zero_lt_one.trans hx₁
    aesop

theorem IsNthDegreeClosed.pow_eq {n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x) :
    x ^ n = ∗(x.val ^ n) := by
  obtain hx₁ | hx₁ := le_or_gt x 1
  · have := le_one_iff.1 hx₁; cases n <;> aesop
  · simpa using h.pow_mul_eq hx₁

proof_wanted IsNthDegreeClosed.omega0 : IsNthDegreeClosed 2 (∗ω)

/-! ### Algebraically closed fields -/

/-- A nimber `x` is algebraically closed when `IsRing x`, and every non-constant polynomial in the
nimbers with coefficients less than `x` has a root that's less than `x`. Note that `0` and `1` are
algebraically closed under this definition.

For simplicity, the constructor takes a `0 < p.degree` assumption. The theorem
`IsAlgClosed.exists_root` proves that this theorem applies (vacuously) when `p = 0` as well. -/
@[mk_iff]
structure IsAlgClosed (x : Nimber) extends IsRing x where
  exists_root' ⦃p : Nimber[X]⦄ (hp₀ : 0 < p.degree) (hp : ∀ k, p.coeff k < x) : ∃ r < x, p.IsRoot r

theorem IsAlgClosed.toIsNthDegreeClosed {x : Nimber} (h : IsAlgClosed x) (n : ℕ) :
    IsNthDegreeClosed n x where
  exists_root' _p hp₀ _ := h.exists_root' hp₀
  __ := h

theorem IsAlgClosed.toIsField {x : Nimber} (h : IsAlgClosed x) : IsField x :=
  (h.toIsNthDegreeClosed 1).toIsField le_rfl

theorem isAlgClosed_iff_forall {x : Nimber} : IsAlgClosed x ↔ ∀ n, IsNthDegreeClosed n x where
  mp := IsAlgClosed.toIsNthDegreeClosed
  mpr H := ⟨(H 0).toIsRing, fun _p hp₀ ↦ (H _).exists_root' hp₀ degree_le_natDegree⟩

theorem IsAlgClosed.exists_root {x : Nimber} (h : IsAlgClosed x) {p : Nimber[X]}
    (hp₀ : p.degree ≠ 0) (hp : ∀ n, p.coeff n < x) : ∃ r < x, p.IsRoot r :=
  (h.toIsNthDegreeClosed _).exists_root hp₀ degree_le_natDegree hp

protected theorem IsAlgClosed.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsAlgClosed x)
    (ne : s.Nonempty) (bdd : BddAbove s) :
    IsAlgClosed (sSup s) := by
  rw [isAlgClosed_iff_forall]
  exact fun n ↦ IsNthDegreeClosed.sSup (fun x hx ↦ (H x hx).toIsNthDegreeClosed n) ne bdd

protected theorem IsAlgClosed.iSup {ι} [Nonempty ι] {f : ι → Nimber} (H : ∀ i, IsAlgClosed (f i))
    (bdd : BddAbove (range f) := by apply Nimber.bddAbove_of_small) :
    IsAlgClosed (⨆ i, f i) :=
  IsAlgClosed.sSup (by simpa) (range_nonempty f) bdd

/-- If `x` is a field, to prove it algebraically closed, it suffices to check
*monic* polynomials. -/
theorem IsAlgClosed.ofMonic {x : Nimber} (h : IsField x)
    (hp : ∀ p : Nimber[X], p.Monic → 0 < p.degree → (∀ k, p.coeff k < x) → ∃ r < x, p.IsRoot r) :
    IsAlgClosed x := by
  rw [isAlgClosed_iff_forall]
  exact fun n ↦ IsNthDegreeClosed.ofMonic h fun p hm hp₀ _ ↦ hp p hm hp₀

theorem IsAlgClosed.leastNoRoots_eq_top {x : Nimber} (h : IsAlgClosed x) :
    leastNoRoots x = ⊤ := by
  rw [WithTop.eq_top_iff_forall_ge]
  refine fun p ↦ le_of_lt ?_
  apply (h.toIsNthDegreeClosed p.natDegree).X_pow_lt_leastNoRoots.trans'
  rw [WithTop.coe_lt_coe]
  simpa using degree_le_natDegree

theorem isAlgClosed_iff_leastNoRoots_eq_top {x : Nimber} (h : IsRing x) :
    IsAlgClosed x ↔ leastNoRoots x = ⊤ where
  mp := IsAlgClosed.leastNoRoots_eq_top
  mpr hx := ⟨h, fun _p hp₀ hpk ↦
    exists_root_of_lt_leastNoRoots hp₀.ne' hpk (hx ▸ WithTop.coe_lt_top _)⟩

@[simp]
theorem leastNoRoots_one : leastNoRoots 1 = ⊤ := by
  rw [leastNoRoots, sInf_eq_top, forall_mem_image]
  intro x hx
  obtain rfl : x = 0 := by ext k; simpa using hx.2.1 k
  simp at hx

theorem leastNoRoots_of_le_one {x : Nimber} (h : x ≤ 1) : leastNoRoots x = ⊤ := by
  obtain rfl | rfl := Nimber.le_one_iff.1 h <;> simp

theorem IsAlgClosed.eval_eq_of_lt {x : Nimber} (h : IsAlgClosed x)
    {p : Nimber[X]} (hpk : ∀ k, p.coeff k < x) : p.eval x = oeval x p :=
  (h.toIsNthDegreeClosed _).eval_eq_of_lt degree_le_natDegree hpk

attribute [simp] eval_prod eval_multiset_prod leadingCoeff_prod in
private theorem IsField.isRoot_leastNoRoots {x : Nimber} (h : IsField x) (ht) :
    (x.leastNoRoots.untop ht).IsRoot x := by
  have hx₁ : 1 < x := h.one_lt
  have hx₀ : 0 < x := h.zero_lt
  generalize_proofs ht
  let n := (x.leastNoRoots.untop ht).natDegree
  have hn : 1 ≤ n := natDegree_leastNoRoots_pos _
  have hd := degree_eq_natDegree (leastNoRoots_ne_zero' ht)
  have hm := h.monic_leastNoRoots ht
  have hxp : ∀ k, (X ^ n + x.leastNoRoots.untop ht).coeff k < x :=
    h.coeff_add_lt (coeff_X_pow_lt _ hx₁) (coeff_leastNoRoots_lt _)
  rw [IsRoot, ← add_right_inj (x ^ n), add_zero]
  apply le_antisymm
  · have h'' : IsNthDegreeClosed (n - 1) x := by
      rw [isNthDegreeClosed_iff_X_pow_le_leastNoRoots h.toIsRing, n.sub_add_cancel hn,
        WithTop.coe_pow, ← WithTop.coe_untop _ ht, Lex.X_pow_le_coe_iff,
        degree_eq_natDegree (leastNoRoots_ne_zero' _)]
    have hp : (X ^ n + x.leastNoRoots.untop ht).degree ≤ .some (n - 1) := by
      rw [← lt_succ_iff, WithBot.orderSucc_coe, succ_eq_add_one, n.sub_add_cancel hn,
        ← CharTwo.sub_eq_add]
      apply (degree_sub_lt ..).trans_eq <;> aesop
    conv_lhs => left; rw [← eval_X_pow]
    rw [← eval_add, h''.eval_eq_of_lt hp hxp]
    apply le_of_forall_lt_imp_ne
    rw [forall_lt_oeval_iff hxp]
    intro q hq hqk
    have hq' : q.degree ≤ .some (n - 1) := hp.trans' (Lex.degree_mono hq.le)
    rw [← h''.eval_eq_of_lt _ hqk, ne_eq, ← add_right_inj (x ^ n), add_self,
      ← eval_X_pow, ← eval_add]
    · intro hx
      have hr : x ∈ (X ^ n + q).roots := by
        rwa [mem_roots]
        rw [ne_eq, CharTwo.add_eq_zero]
        apply_fun degree
        apply (hq'.trans_lt _).ne'
        simpa using hn
      apply (h.root_lt _ (h.coeff_add_lt (coeff_X_pow_lt _ hx₁) hqk) hr).false
      rw [← WithTop.coe_untop _ ht, WithTop.coe_lt_coe]
      apply Lex.X_pow_add_lt hm
      simpa
    · exact hp.trans' (Lex.degree_mono hq.le)
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
      · exact leastNoRoots_not_root_of_lt _ (f i).2
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
    replace h : IsNthDegreeClosed n x := by
      rwa [isNthDegreeClosed_iff_X_pow_le_leastNoRoots, ← WithTop.coe_untop _ ht,
        WithTop.coe_le_coe, Nimber.Lex.X_pow_le_iff, hn]
    have hf : IsField x := h.toIsField (by lia)
    have hem : (hf.embed _ (coeff_leastNoRoots_lt ht)).Monic := by
      simpa using hf.monic_leastNoRoots _
    refine ⟨h.pow _, fun y z hy hz ↦ ?_, ne_of_gt (by simp [h.one_lt])⟩
    obtain ⟨py, hyd, hyc, rfl⟩ := eq_oeval_of_lt_pow h.ne_zero hy
    obtain ⟨pz, hzd, hzc, rfl⟩ := eq_oeval_of_lt_pow h.ne_zero hz
    rw [WithBot.natCast_eq_coe, WithBot.coe_add_one, WithBot.lt_add_one] at hyd hzd
    rw [← h.eval_eq_of_lt hyd hyc, ← h.eval_eq_of_lt hzd hzc, ← hf.map_embed hyc,
      ← hf.map_embed hzc, ← eval_mul, ← Polynomial.map_mul, ← modByMonic_add_div (_ * _) hem,
      Polynomial.map_add, eval_add, Polynomial.map_mul, eval_mul, hf.map_embed,
      h.isRoot_leastNoRoots ht, zero_mul, add_zero, h.eval_eq_of_lt _ (by simp)]
    on_goal 1 => apply oeval_lt_opow (by simp)
    on_goal 2 => rw [← WithBot.lt_add_one]
    all_goals exact (degree_map ..).trans_lt <|
      (degree_modByMonic_lt _ hem).trans_le (by simp [hn])

theorem IsField.pow_degree_leastNoRoots {x : Nimber} (hf : IsField x) (ht) {n : ℕ}
    (hn : (x.leastNoRoots.untop ht).degree = n) : IsField (of (val x ^ n)) := by
  obtain rfl | hn1 := eq_or_ne n 1
  · simpa using hf
  cases n with
  | zero => simpa [hn] using degree_leastNoRoots_pos ht
  | succ n =>
    replace h : IsNthDegreeClosed n x := by
      rw [isNthDegreeClosed_iff_X_pow_le_leastNoRoots hf.toIsRing,
        ← WithTop.coe_untop _ ht, WithTop.coe_le_coe, Nimber.Lex.X_pow_le_iff, hn]
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
    obtain ⟨py, hyd, hyc, rfl⟩ := eq_oeval_of_lt_pow hf.ne_zero hy
    rw [WithBot.natCast_eq_coe, WithBot.coe_add_one, WithBot.lt_add_one] at hyd
    rw [← h.eval_eq_of_lt hyd hyc, ← hf.map_embed hyc, ← hoc, eval_map,
      show eval₂ _ x _ = eval₂ _ (hxr.toSubring.subtype ⟨x, hxn⟩) _ from rfl,
      ← Polynomial.hom_eval₂, ← coe_eval₂RingHom] at hy0 ⊢
    rw [← map_zero hxr.toSubring.subtype, hxr.toSubring.subtype_injective.ne_iff,
      ne_eq, ← RingHom.mem_ker] at hy0
    obtain ⟨i, s, hs, hi⟩ := hr.exists_inv hy0
    rw [inv_eq_of_mul_eq_one_left]
    · exact (r i).2
    · replace hi := congrArg r hi
      rw [map_add, map_mul, hs] at hi
      simpa using  congrArg hxr.toSubring.subtype hi

theorem IsAlgClosed.isRing_pow_omega0 {x : Nimber} (h : IsAlgClosed x) :
    IsRing (of (val x ^ ω)) := by
  refine ⟨h.opow _, fun y hy z hz ↦ ?_, ne_of_gt (by simp [h.one_lt])⟩
  obtain ⟨py, hyd, hyc, rfl⟩ := eq_oeval_of_lt_opow_omega0 hy
  obtain ⟨pz, hzd, hzc, rfl⟩ := eq_oeval_of_lt_pow h.ne_zero hz



end Nimber
