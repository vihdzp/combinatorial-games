/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/
import CombinatorialGames.Mathlib.Pointwise
import CombinatorialGames.Nimber.SimplestExtension.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Nimbers are algebraically closed

This file aims to prove the last part of the simplest extension theorem (see
`CombinatorialGames.Nimber.SimplestExtension.Basic`), and to deduce, as a corollary, that the
nimbers are algebraically closed.
-/

universe u

open Order Ordinal Polynomial Set

-- Why isn't this tagged?
attribute [simp] eval_prod eval_multiset_prod leadingCoeff_prod

-- TODO: upstream to Mathlib
attribute [aesop simp] coeff_C coeff_X coeff_one

/-! ### For Mathlib -/

namespace Finsupp

variable {α β : Type*} [Zero β]

theorem mem_frange_of_mem {x} {f : α →₀ β} (h : x ∈ f.support) : f x ∈ f.frange := by
  rw [mem_frange]
  constructor
  · rwa [mem_support_iff] at h
  · use x

theorem range_subset_insert_frange (f : α →₀ β) : range f ⊆ insert 0 f.frange := by
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ f.support
  · exact mem_insert_of_mem _ (mem_frange_of_mem hx)
  · rw [mem_support_iff, not_not] at hx
    rw [hx]
    exact mem_insert ..

theorem finite_range (f : α →₀ β) : (range f).Finite := by
  apply Finite.subset _ (range_subset_insert_frange f)
  simp

end Finsupp

namespace Polynomial

variable {R : Type*}

-- TODO: upstream
theorem Irreducible.degree_pos [DivisionSemiring R] {f : R[X]} (h : Irreducible f) :
    0 < f.degree := by
  rw [← natDegree_pos_iff_degree_pos]
  exact h.natDegree_pos

theorem finite_range_coeff [Semiring R] (p : R[X]) : (range p.coeff).Finite :=
  Finsupp.finite_range _

end Polynomial

-- TODO: can we golf this using `finite_range_coeff`?
private theorem Polynomial.exists_gt_of_forall_coeff_gt {s : Set Nimber} {p : Nimber[X]}
    (h : ∀ k, ∃ a ∈ s, p.coeff k < a) : ∃ a ∈ s, ∀ k, p.coeff k < a := by
  choose f hf using h
  obtain ⟨c, hc⟩ := ((Finset.range (p.natDegree + 1)).image f).exists_maximal (by simp)
  have hc' := hc.1
  simp_rw [Finset.mem_image, Finset.mem_range, Nat.lt_succ] at hc'
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
`x`. Note that `0` and `1` are `n`-th degree closed under this definition.

We don't extend `IsField x`, as for `1 ≤ n`, this predicate implies it.

For simplicity, the constructor takes a `0 < p.degree` assumption. The theorem
`IsNthDegreeClosed.has_root` proves that this theorem applies (vacuously) when `p = 0` as well. -/
@[mk_iff]
structure IsNthDegreeClosed (n : ℕ) (x : Nimber) extends IsRing x where
  has_root' ⦃p : Nimber[X]⦄ (hp₀ : 0 < p.degree) (hpn : p.degree ≤ n) (hp : ∀ k, p.coeff k < x) :
    ∃ r < x, p.IsRoot r

theorem IsNthDegreeClosed.has_root {n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x) {p : Nimber[X]}
    (hp₀ : p.degree ≠ 0) (hpn : p.degree ≤ n) (hp : ∀ k, p.coeff k < x) : ∃ r < x, p.IsRoot r := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · aesop
  · apply h.has_root' _ hpn hp
    cases _ : p.degree <;> simp_all [Nat.pos_iff_ne_zero]

theorem IsNthDegreeClosed.le {m n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x) (hmn : m ≤ n) :
    IsNthDegreeClosed m x where
  has_root' _p hp₀ hpm := h.has_root' hp₀ (hpm.trans (mod_cast hmn))
  __ := h.toIsRing

theorem IsNthDegreeClosed.of_le_one (n : ℕ) {x : Nimber} (h : x ≤ 1) : IsNthDegreeClosed n x where
  has_root' p hp₀ _ hp := by
    have := polynomial_eq_zero_of_le_one h hp
    simp_all
  __ := IsRing.of_le_one h

@[simp]
theorem IsNthDegreeClosed.zero (n : ℕ) : IsNthDegreeClosed n 0 :=
  .of_le_one n zero_le_one

@[simp]
theorem IsNthDegreeClosed.one (n : ℕ) : IsNthDegreeClosed n 1 :=
  .of_le_one n le_rfl

protected theorem IsNthDegreeClosed.sSup {n : ℕ} {s : Set Nimber}
    (H : ∀ x ∈ s, IsNthDegreeClosed n x) : IsNthDegreeClosed n (sSup s) := by
  have : IsNthDegreeClosed n (sSup ∅) := by simp
  by_cases hs : BddAbove s; swap; rwa [csSup_of_not_bddAbove hs]
  obtain rfl | hs' := s.eq_empty_or_nonempty; assumption
  refine ⟨IsRing.sSup fun x hx ↦ (H x hx).toIsRing, fun p hp₀ hpn hp ↦ ?_⟩
  simp_rw [lt_csSup_iff hs hs'] at *
  obtain ⟨c, hc, hc'⟩ := exists_gt_of_forall_coeff_gt hp
  obtain ⟨r, hr, hr'⟩ := (H _ hc).has_root' hp₀ hpn fun m ↦ hc' _
  exact ⟨r, ⟨_, hc, hr⟩, hr'⟩

protected theorem IsNthDegreeClosed.iSup {n : ℕ} {ι} {f : ι → Nimber}
    (H : ∀ i, IsNthDegreeClosed n (f i)) : IsNthDegreeClosed n (⨆ i, f i) := by
  apply IsNthDegreeClosed.sSup
  simpa

/-- If `x` is a field, to prove it `n`-th degree closed, it suffices to check *monic* polynomials of
degree less or equal to `n`. -/
theorem IsNthDegreeClosed.ofMonic {n : ℕ} {x : Nimber} (h : IsField x)
    (hp : ∀ p : Nimber[X], p.Monic → 0 < p.degree → p.degree ≤ n → (∀ k, p.coeff k < x) →
      ∃ r < x, p.IsRoot r) : IsNthDegreeClosed n x where
  has_root' p hp₀ hpn hp' := by
    have hp₀' : p ≠ 0 := by rintro rfl; simp at hp₀
    have hm : (C p.leadingCoeff⁻¹ * p).Monic := by simp [Monic, hp₀']
    have hd : (C p.leadingCoeff⁻¹ * p).degree = p.degree := by compute_degree!
    have := hp _ hm (hd ▸ hp₀) (hd ▸ hpn) fun k ↦ ?_
    · aesop
    · rw [coeff_C_mul, inv_mul_eq_div]
      exact h.div_lt (hp' k) (hp' _)
  __ := h

@[simp]
theorem isNthDegreeClosed_zero_iff_isRing {x : Nimber} : IsNthDegreeClosed 0 x ↔ IsRing x := by
  refine ⟨IsNthDegreeClosed.toIsRing, fun h ↦ ⟨h, fun p ↦ ?_⟩⟩
  cases _ : p.degree <;> aesop

theorem IsNthDegreeClosed.toIsField {n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x) (hn : 0 < n) :
    IsField x := by
  obtain hx₁ | hx₁ := le_or_gt x 1
  · exact IsField.of_le_one hx₁
  · refine ⟨h.toIsRing, fun y hy₀ hy ↦ ?_⟩
    have hp : degree (C y * (X : Nimber[X]) + 1) = 1 := by compute_degree!
    have ⟨r, hr, hr₀⟩ := h.has_root (hp ▸ one_ne_zero) (by simpa [hp]) fun k ↦ ?_
    · convert hr
      apply inv_eq_of_mul_eq_one_right
      rw [← Nimber.add_eq_zero]
      simpa using hr₀
    · obtain hk | hk := le_or_gt k 1
      · obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.1 hk <;> simpa [coeff_one]
      · rw [coeff_eq_zero_of_degree_lt]
        · exact zero_lt_one.trans hx₁
        · simp_all

@[simp]
theorem isNthDegreeClosed_one_iff_isField {x : Nimber} : IsNthDegreeClosed 1 x ↔ IsField x := by
  refine ⟨(IsNthDegreeClosed.toIsField · one_pos), (.ofMonic · fun p hm hp₀ hp₁ hp ↦ ?_)⟩
  rw [Polynomial.eq_X_add_C_of_degree_le_one hp₁] at hp ⊢
  have : p.natDegree = 1 := natDegree_eq_of_degree_eq_some <| by
    rw [← succ_le_iff] at hp₀
    exact hp₁.antisymm hp₀
  rw [Monic, leadingCoeff] at hm
  have := hp 0
  aesop

-- We could have proved this much earlier, but going through `IsNthDegreeClosed`
-- gives a much shorter proof.
protected theorem IsField.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsField x) :
    IsField (sSup s) := by
  simp_rw [← isNthDegreeClosed_one_iff_isField] at *
  exact IsNthDegreeClosed.sSup H

protected theorem IsField.iSup {ι} {f : ι → Nimber} (H : ∀ i, IsField (f i)) :
    IsField (⨆ i, f i) := by
  apply IsField.sSup
  simpa

theorem IsNthDegreeClosed.X_pow_lt_leastNotSplit {n : ℕ} {x : Nimber}
    (h : IsNthDegreeClosed n x) : .some (X ^ (n + 1)) < leastNotSplit x := by
  refine (leastNotSplit_ne_X_pow x _).lt_of_le' (le_of_forall_ne fun p hp hp' ↦ ?_)
  obtain ⟨p, rfl, hp⟩ := WithTop.lt_iff_exists_coe.1 hp
  have h' := hp' ▸ WithTop.coe_ne_top
  have ⟨r, hr, hr'⟩ := h.has_root' (degree_leastNotSplit_pos h') ?_
    (coeff_leastNotSplit_lt h')
  · exact leastNotSplit_not_root_of_lt h' hr hr'
  · simp_rw [← hp']
    simpa using hp

theorem isNthDegreeClosed_iff_X_pow_lt_leastNotSplit {n : ℕ} {x : Nimber} (h : IsRing x) :
    IsNthDegreeClosed n x ↔ .some (X ^ (n + 1)) < leastNotSplit x where
  mp := IsNthDegreeClosed.X_pow_lt_leastNotSplit
  mpr hx := by
    refine ⟨h, fun p hp₀ hpn hpk ↦ has_root_of_lt_leastNotSplit hp₀.ne' hpk <| hx.trans' ?_⟩
    rw [WithTop.coe_lt_coe]
    apply Lex.lt_of_degree_lt
    simpa

theorem isNthDegreeClosed_iff_X_pow_le_leastNotSplit {n : ℕ} {x : Nimber} (h : IsRing x) :
    IsNthDegreeClosed n x ↔ .some (X ^ (n + 1)) ≤ leastNotSplit x where
  mp hx := hx.X_pow_lt_leastNotSplit.le
  mpr hx := (isNthDegreeClosed_iff_X_pow_lt_leastNotSplit h).2
    (hx.lt_of_ne' (leastNotSplit_ne_X_pow x _))

theorem IsField.X_sq_lt_leastNotSplit {x : Nimber} (h : IsField x) :
    .some (X ^ 2) < leastNotSplit x := by
  rw [← isNthDegreeClosed_one_iff_isField] at h
  exact h.X_pow_lt_leastNotSplit

theorem IsNthDegreeClosed.root_lt {n : ℕ} {x r : Nimber} (h : IsNthDegreeClosed n x) {p : Nimber[X]}
    (hpn : p.degree ≤ n) (hpk : ∀ k, p.coeff k < x) (hr : r ∈ p.roots) : r < x := by
  cases n with
  | zero => cases hpn.not_gt <| degree_pos_of_mem_roots hr
  | succ n =>
    apply (h.toIsField n.succ_pos).root_lt _ hpk hr
    apply (WithTop.coe_lt_coe.2 (Lex.lt_of_degree_lt _)).trans h.X_pow_lt_leastNotSplit
    rw [degree_X_pow]
    exact lt_succ_of_le hpn

theorem IsNthDegreeClosed.eval_eq_of_lt {n : ℕ} {x : Nimber} (h : IsNthDegreeClosed n x)
    {p : Nimber[X]} (hpn : p.degree ≤ n) (hpk : ∀ k, p.coeff k < x) :
    p.eval x = oeval x p := by
  obtain hx₁ | hx₁ := le_or_gt x 1; simp [polynomial_eq_zero_of_le_one hx₁ hpk]
  have hx₀ := zero_lt_one.trans hx₁
  induction n generalizing p with
  | zero => rw [p.eq_C_of_degree_le_zero hpn]; simp
  | succ n IH =>
    have h' := h.le n.le_succ
    have hx : ∗(x.val ^ (n + 1)) = x ^ (n + 1) := by
      refine le_antisymm (le_of_forall_ne fun y hy ↦ ?_) (pow_le_of_forall_ne fun f ↦ ?_)
      · obtain ⟨p, hpn, hpk, rfl⟩ := eq_oeval_of_lt_opow hx₀.ne' hy
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
          refine h.coeff_add_lt (coeff_X_pow_lt _ hx₁) <| h.coeff_prod_lt hx₁ fun y hy ↦ ?_
          have : (f y).1 < x := (f y).2
          apply h.coeff_add_lt <;> aesop (add simp [coeff_X, coeff_C])
        have IH := IH h' hq' H
        simp only [eval_add, eval_X, eval_pow, eval_prod, eval_C] at IH
        exact IH ▸ (oeval_lt_opow H (lt_succ_of_le hq')).ne
    obtain ⟨a, q, rfl, hqn⟩ := eq_C_mul_X_pow_add_of_degree_le hpn
    have hqn' := hqn
    rw [WithBot.natCast_eq_coe, WithBot.coe_add_one, WithBot.lt_add_one] at hqn'
    have hqk (k) : q.coeff k < x := by
      obtain hk | hk := le_or_gt k n
      · convert hpk k using 1
        aesop
      · rwa [q.coeff_eq_zero_of_degree_lt (hqn'.trans_lt (mod_cast hk))]
    rw [eval_add, eval_mul, eval_C, eval_X_pow, oeval_C_mul_X_pow_add hqn, IH h' hqn' hqk,
      (h.pow (n + 1)).mul_add_eq_of_lt', mul_comm, eq_comm, ← hx]
    · have hxn : val x ≤ val x ^ (n + 1) := by
        rw [← opow_natCast]
        exact left_le_opow _ (mod_cast n.succ_pos)
      congr
      refine (h.pow (n + 1)).mul_eq_of_lt h.toIsGroup h.toIsGroup hxn ?_ le_rfl
        @(h.toIsField n.succ_pos).inv_lt fun a b ha hb ↦ ?_
      · convert hpk (n + 1)
        simpa using q.coeff_eq_zero_of_degree_lt hqn
      · obtain ⟨p, hpn, hpk, rfl⟩ := eq_oeval_of_lt_opow hx₀.ne' ha
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
  obtain hx₁ | hx₁ := le_or_gt x 1
  · have := le_one_iff.1 hx₁; aesop
  · conv_lhs => rw [← eval_X_pow, ← eval_C (a := y), ← eval_mul]
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
`IsAlgClosed.has_root` proves that this theorem applies (vacuously) when `p = 0` as well. -/
@[mk_iff]
structure IsAlgClosed (x : Nimber) extends IsRing x where
  has_root' ⦃p : Nimber[X]⦄ (hp₀ : 0 < p.degree) (hp : ∀ k, p.coeff k < x) : ∃ r < x, p.IsRoot r

theorem IsAlgClosed.toIsNthDegreeClosed {x : Nimber} (h : IsAlgClosed x) (n : ℕ) :
    IsNthDegreeClosed n x where
  has_root' _p hp₀ _ := h.has_root' hp₀
  __ := h

@[coe]
theorem IsAlgClosed.toIsField {x : Nimber} (h : IsAlgClosed x) : IsField x :=
  (h.toIsNthDegreeClosed 1).toIsField one_pos

theorem isAlgClosed_iff_forall {x : Nimber} : IsAlgClosed x ↔ ∀ n, IsNthDegreeClosed n x where
  mp := IsAlgClosed.toIsNthDegreeClosed
  mpr H := ⟨(H 0).toIsRing, fun _p hp₀ ↦ (H _).has_root' hp₀ degree_le_natDegree⟩

theorem IsAlgClosed.has_root {x : Nimber} (h : IsAlgClosed x) {p : Nimber[X]}
    (hp₀ : p.degree ≠ 0) (hp : ∀ n, p.coeff n < x) : ∃ r < x, p.IsRoot r :=
  (h.toIsNthDegreeClosed _).has_root hp₀ degree_le_natDegree hp

@[simp]
theorem IsAlgClosed.zero : IsAlgClosed 0 := by
  simp [isAlgClosed_iff_forall]

@[simp]
theorem IsAlgClosed.one : IsAlgClosed 1 := by
  simp [isAlgClosed_iff_forall]

theorem IsAlgClosed.of_le_one {x : Nimber} (h : x ≤ 1) : IsAlgClosed x := by
  obtain rfl | rfl := Nimber.le_one_iff.1 h <;> simp

protected theorem IsAlgClosed.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsAlgClosed x) :
    IsAlgClosed (sSup s) := by
  rw [isAlgClosed_iff_forall]
  exact fun n ↦ IsNthDegreeClosed.sSup fun x hx ↦ (H x hx).toIsNthDegreeClosed n

protected theorem IsAlgClosed.iSup {ι} {f : ι → Nimber} (H : ∀ i, IsAlgClosed (f i)) :
    IsAlgClosed (⨆ i, f i) := by
  apply IsAlgClosed.sSup
  simpa

/-- If `x` is a field, to prove it algebraically closed, it suffices to check
*monic* polynomials. -/
theorem IsAlgClosed.ofMonic {x : Nimber} (h : IsField x)
    (hp : ∀ p : Nimber[X], p.Monic → 0 < p.degree → (∀ k, p.coeff k < x) → ∃ r < x, p.IsRoot r) :
    IsAlgClosed x := by
  rw [isAlgClosed_iff_forall]
  exact fun n ↦ IsNthDegreeClosed.ofMonic h fun p hm hp₀ _ ↦ hp p hm hp₀

theorem IsAlgClosed.leastNotSplit_eq_top {x : Nimber} (h : IsAlgClosed x) :
    leastNotSplit x = ⊤ := by
  rw [WithTop.eq_top_iff_forall_ge]
  refine fun p ↦ le_of_lt ?_
  apply (h.toIsNthDegreeClosed _).X_pow_lt_leastNotSplit.trans'
  rw [WithTop.coe_lt_coe]
  simpa using degree_le_natDegree

theorem isAlgClosed_iff_leastNotSplit_eq_top {x : Nimber} (h : IsRing x) :
    IsAlgClosed x ↔ leastNotSplit x = ⊤ where
  mp := IsAlgClosed.leastNotSplit_eq_top
  mpr hx := ⟨h, fun _p hp₀ hpk ↦
    has_root_of_lt_leastNotSplit hp₀.ne' hpk (hx ▸ WithTop.coe_lt_top _)⟩

@[simp]
theorem leastNotSplit_one : leastNotSplit 1 = ⊤ :=
  IsAlgClosed.one.leastNotSplit_eq_top

theorem leastNotSplit_of_le_one {x : Nimber} (h : x ≤ 1) : leastNotSplit x = ⊤ :=
  (IsAlgClosed.of_le_one h).leastNotSplit_eq_top

theorem IsAlgClosed.eval_eq_of_lt {x : Nimber} (h : IsAlgClosed x)
    {p : Nimber[X]} (hpk : ∀ k, p.coeff k < x) : p.eval x = oeval x p :=
  (h.toIsNthDegreeClosed _).eval_eq_of_lt degree_le_natDegree hpk

/-- The fourth **simplest extension theorem**: if `x` is a field that isn't algebraically closed,
then `x` is the root of some polynomial with coefficients `< x`. -/
theorem IsField.isRoot_leastNotSplit {x : Nimber} (h : IsField x) (ht) :
    (x.leastNotSplit.untop ht).IsRoot x := by
  have hx₁ : 1 < x := by by_contra! hx; cases ht (leastNotSplit_of_le_one hx)
  have hx₀ : 0 < x := hx₁.bot_lt
  generalize_proofs ht
  let n := (x.leastNotSplit.untop ht).natDegree
  have hn : 1 ≤ n := natDegree_leastNotSplit_pos _
  have hd := degree_eq_natDegree (leastNotSplit_ne_zero' ht)
  have hm := h.monic_leastNotSplit ht
  have hxp : ∀ k, (X ^ n + x.leastNotSplit.untop ht).coeff k < x :=
    h.coeff_add_lt (coeff_X_pow_lt _ hx₁) (coeff_leastNotSplit_lt _)
  rw [IsRoot, ← add_right_inj (x ^ n), add_zero]
  apply le_antisymm
  · have h'' : IsNthDegreeClosed (n - 1) x := by
      rw [isNthDegreeClosed_iff_X_pow_le_leastNotSplit h.toIsRing, n.sub_add_cancel hn,
        WithTop.coe_pow, ← WithTop.coe_untop _ ht, Lex.X_pow_le_coe_iff,
        degree_eq_natDegree (leastNotSplit_ne_zero' _)]
    have hp : (X ^ n + x.leastNotSplit.untop ht).degree ≤ .some (n - 1) := by
      rw [← lt_succ_iff, WithBot.orderSucc_coe, succ_eq_add_one, n.sub_add_cancel hn,
        ← CharTwo.sub_eq_add]
      apply (degree_sub_lt ..).trans_eq <;> aesop
    conv_lhs => left; rw [← eval_X_pow]
    rw [← eval_add, h''.eval_eq_of_lt hp hxp]
    apply le_of_forall_ne
    rw [forall_lt_oeval_iff hx₁ hxp]
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
      apply Lex.lt_of_degree_lt (degree_sub_lt _ (leastNotSplit_ne_zero' ht) _)
      · rw [degree_prod_of_monic] <;> aesop (add simp [Monic])
      · aesop
    · apply h.coeff_add_lt (h.coeff_prod_lt hx₁ _) (coeff_leastNotSplit_lt _)
      aesop
    · rw [ne_eq, CharTwo.add_eq_zero]
      let i : Fin n := ⟨0, natDegree_leastNotSplit_pos ht⟩
      apply_fun eval (f i).1
      rw [eval_prod, Finset.prod_eq_zero (Finset.mem_univ i), ne_comm]
      · exact leastNotSplit_not_root_of_lt _ (f i).2
      · simp

/-! ### Nimbers are algebraically closed -/

open Pointwise

instance (x : Nimber.{u}) : Small.{u} {p : Nimber[X] // ∀ k, p.coeff k < x} := by
  refine small_of_injective (β := ℕ → Iio x) (f := fun p k ↦ ⟨_, p.2 k⟩) fun p q h ↦ ?_
  ext k
  simpa using congrFun h k

/-- The set of roots of polynomials with coefficients less than `x`. -/
private def rootSet (x : Nimber) : Set Nimber :=
  ⋃ p : {p : Nimber[X] // ∀ k, p.coeff k < x}, p.1.roots.toFinset

private instance (x : Nimber.{u}) : Small.{u} x.rootSet :=
  small_iUnion _

private theorem rootSet_mono : Monotone rootSet :=
  fun _ _ h ↦ sUnion_mono fun _ ⟨p, hp⟩ ↦ ⟨⟨p, fun k ↦ (p.2 k).trans_le h⟩, hp⟩

/-- A single step in the algebraic closure construction. -/
private def algClosureSet (x : Nimber) : Set Nimber :=
  (Iio x + Iio x) ∪ (Iio x * Iio x) ∪ rootSet x

private instance (x : Nimber.{u}) : Small.{u} (algClosureSet x) :=
  small_union ..

private theorem algClosureSet.add_mem {x y z : Nimber} (hy : y < x) (hz : z < x) :
    y + z ∈ algClosureSet x := by
  apply mem_union_left _ (mem_union_left ..)
  use y, hy, z, hz

private theorem algClosureSet.mul_mem {x y z : Nimber} (hy : y < x) (hz : z < x) :
    y * z ∈ algClosureSet x := by
  apply mem_union_left _ (mem_union_right ..)
  use y, hy, z, hz

private theorem algClosureSet.root_mem {x r : Nimber} {p : Nimber[X]} (hp₀ : p ≠ 0)
    (hpk : ∀ k, p.coeff k < x) (hr : p.IsRoot r) :
    r ∈ algClosureSet x := by
  apply mem_union_right
  rw [rootSet]
  aesop

private theorem algClosure.mem_of_lt {x y : Nimber} (h : y < x) : y ∈ algClosureSet x := by
  simpa using algClosureSet.add_mem h h.bot_lt

private theorem algClosureSet_mono : Monotone algClosureSet := by
  intro x y h
  have h' : Iio x ⊆ Iio y := by rwa [Iio_subset_Iio_iff]
  exact union_subset_union (union_subset_union (add_subset_add h' h') (mul_subset_mul h' h'))
    (rootSet_mono h)

private theorem le_sSup_algClosureSet (x : Nimber) : x ≤ sSup (succ '' algClosureSet x) := by
  refine le_of_forall_lt fun y hy ↦ ?_
  rw [← succ_le_iff]
  apply le_csSup (bddAbove_of_small _)
  simpa using algClosure.mem_of_lt hy

private theorem iterate_algClosureSet_mono {x : Nimber} :
    Monotone (fun n ↦ (fun y ↦ sSup (succ '' algClosureSet y))^[n] x) := by
  refine Monotone.monotone_iterate_of_le_map (fun y z h ↦ ?_) (le_sSup_algClosureSet x)
  exact csSup_le_csSup' (bddAbove_of_small _) (image_mono (algClosureSet_mono h))

/-- The algebraic closure of a nimber is the smallest nimber which all sums, products, and all roots
of all polynomials with coefficients less than `x`.

A priori this might not be algebraically closed; we'll prove that it is as part of proving that the
nimbers are algebraically closed. -/
noncomputable def algClosure (x : Nimber) : Nimber :=
  ⨆ n : ℕ, (fun y ↦ sSup (succ '' algClosureSet y))^[n] x

private theorem bddAbove_range_algClosure {x : Nimber} :
    BddAbove (range fun n ↦ (fun y ↦ sSup (succ '' algClosureSet y))^[n] x) :=
  bddAbove_of_small _

private theorem lt_algClosure_iff {x y : Nimber} :
    y < algClosure x ↔ ∃ n, y < (fun y ↦ sSup (succ '' algClosureSet y))^[n] x :=
  lt_ciSup_iff bddAbove_range_algClosure

private theorem algClosure.op_lt {x y z : Nimber} {op : Nimber → Nimber → Nimber}
    (hy : y < algClosure x) (hz : z < algClosure x)
    (H : ∀ {x y z}, y < x → z < x → op y z ∈ algClosureSet x) :
    op y z < algClosure x := by
  rw [lt_algClosure_iff] at *
  obtain ⟨m, hm⟩ := hy
  obtain ⟨n, hn⟩ := hz
  use max m n + 1
  simp_rw [Function.iterate_succ_apply', lt_csSup_iff' (bddAbove_of_small _),
    mem_image, exists_exists_and_eq_and, lt_succ_iff]
  refine ⟨_, H (hm.trans_le ?_) (hn.trans_le ?_), le_rfl⟩
  all_goals apply iterate_algClosureSet_mono; simp

theorem algClosure.add_lt {x y z : Nimber} (hy : y < algClosure x) (hz : z < algClosure x) :
    y + z < algClosure x :=
  algClosure.op_lt hy hz algClosureSet.add_mem

theorem algClosure.mul_lt {x y z : Nimber} (hy : y < algClosure x) (hz : z < algClosure x) :
    y * z < algClosure x :=
  algClosure.op_lt hy hz algClosureSet.mul_mem

theorem algClosure.root_lt {x r : Nimber} {p : Nimber[X]} (hp₀ : p ≠ 0)
    (hpk : ∀ k, p.coeff k < algClosure x) (hr : p.IsRoot r) : r < algClosure x := by
  simp_rw [lt_algClosure_iff] at hpk ⊢
  have hpk' : ∀ k, ∃ a ∈ (range fun n ↦ (fun y ↦ sSup (succ '' algClosureSet y))^[n] x),
    p.coeff k < a := by simpa
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := exists_gt_of_forall_coeff_gt hpk'
  use n + 1
  simp_rw [Function.iterate_succ_apply', lt_csSup_iff' (bddAbove_of_small _),
    mem_image, exists_exists_and_eq_and, lt_succ_iff]
  exact ⟨_, algClosureSet.root_mem hp₀ hn hr, le_rfl⟩

protected theorem IsField.algClosure (x : Nimber) : IsField (algClosure x) := by
  obtain h | h := le_or_gt (algClosure x) 1; exact .of_le_one h
  refine ⟨⟨⟨@algClosure.add_lt x⟩, @algClosure.mul_lt x⟩, fun y hy₀ hy ↦ ?_⟩
  apply algClosure.root_lt (p := C y * X + 1)
  · apply_fun (coeff · 0)
    simp
  · have := h.bot_lt
    aesop
  · simp [hy₀]

theorem le_algClosure (x : Nimber) : x ≤ algClosure x := by
  apply le_ciSup_of_le (bddAbove_of_small _) 1
  simpa using le_sSup_algClosureSet x

private theorem leastNotSplit_algClosure' {x : Nimber} {p : Nimber[X]} (hp : 0 < p.degree)
    (hpk : ∀ k, p.coeff k < x) (IH : ∀ q < p, 0 < q.degree → ∃ r, q.IsRoot r)
    (hr : ∀ r, ¬ p.IsRoot r) : leastNotSplit (algClosure x) = p := by
  apply le_antisymm
  · exact leastNotSplit_le_of_not_isRoot hp
      (fun k ↦ (hpk k).trans_le (le_algClosure x)) fun r _ ↦ hr r
  · apply le_of_forall_ne
    rw [WithTop.forall_lt_coe]
    intro q hq hq'
    have ht := hq' ▸ WithTop.coe_ne_top
    have hq' : q = x.algClosure.leastNotSplit.untop ht := by simp_rw [← hq', WithTop.untop_coe]
    have hqd : 0 < q.degree := hq' ▸ degree_leastNotSplit_pos ht
    obtain ⟨r, hr⟩ := IH q hq hqd
    apply leastNotSplit_not_root_of_lt ht (r := r)
    apply algClosure.root_lt (p := q) (by aesop)
    · exact hq' ▸ coeff_leastNotSplit_lt ht
    · exact hr
    · exact hq' ▸ hr

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
  have ht := leastNotSplit_algClosure' hp hpk IH hr
  have hp' := (IsField.algClosure x).isRoot_leastNotSplit (ht ▸ WithTop.coe_ne_top)
  simp_rw [ht, WithTop.untop_coe] at hp'
  exact hr _ hp'

end Nimber
