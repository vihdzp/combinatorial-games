/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Nimber.SimplestExtension.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Nimbers are algebraically closed

This file aims to prove the last part of the simplest extension theorem (see
`CombinatorialGames.Nimber.SimplestExtension.Basic`), and to deduce, as a corollary, that the
nimbers are algebraically closed.
-/

open Polynomial

namespace Nimber

/-! ### n-th degree closed fields -/

/-- A nimber `x` is `n`-th degree closed when `IsRing x`, and every non-constant polynomial in the
nimbers with degree less or equal to `n` and coefficients less than `x` has a root that's less than
`x`. Note that `0` and `1` are `n`-th degree closed under this definition.

We don't extend `IsField x`, as for `1 ≤ n`, this predicate implies it.

For simplicity, the constructor takes a `0 < p.degree` assumption. The theorem
`IsNthDegreeClosed.exists_root` proves that this theorem applies (vacuously) when `p = 0`
as well. -/
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

@[simp]
theorem IsNthDegreeClosed.zero (n : ℕ) : IsNthDegreeClosed n 0 where
  exists_root' := by simp
  __ := IsRing.zero

@[simp]
theorem IsNthDegreeClosed.one (n : ℕ) : IsNthDegreeClosed n 1 where
  exists_root' p hp₀ _ hp := by
    suffices p = 0 by simp_all
    ext n
    simpa using hp n
  __ := IsRing.one

theorem IsNthDegreeClosed.of_le_one (n : ℕ) {x : Nimber} (h : x ≤ 1) : IsNthDegreeClosed n x := by
  obtain rfl | rfl := Nimber.le_one_iff.1 h <;> simp

protected theorem IsNthDegreeClosed.sSup {n : ℕ} {s : Set Nimber}
    (H : ∀ x ∈ s, IsNthDegreeClosed n x) : IsNthDegreeClosed n (sSup s) := by
  have : IsNthDegreeClosed n (sSup ∅) := by simp
  by_cases hs : BddAbove s; swap; rwa [csSup_of_not_bddAbove hs]
  obtain rfl | hs' := s.eq_empty_or_nonempty; assumption
  refine ⟨IsRing.sSup fun x hx ↦ (H x hx).toIsRing, fun p hp₀ hpn hp ↦ ?_⟩
  simp_rw [lt_csSup_iff hs hs'] at *
  choose f hf using hp
  obtain ⟨c, hc⟩ := ((Finset.range (p.natDegree + 1)).image f).exists_maximal (by simp)
  have hc' := hc.1
  simp_rw [Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff] at hc'
  obtain ⟨n, hn, rfl⟩ := hc'
  have := (H _ (hf n).1).exists_root' hp₀ hpn fun m ↦ ?_
  · obtain ⟨r, hr, hr'⟩ := this
    exact ⟨r, ⟨_, (hf n).1, hr⟩, hr'⟩
  · obtain hm | hm := le_or_gt m p.natDegree
    · apply (hf m).2.trans_le (hc.isGreatest.2 _)
      aesop
    · rw [coeff_eq_zero_of_natDegree_lt hm]
      exact bot_le.trans_lt (hf n).2

protected theorem IsNthDegreeClosed.iSup {n : ℕ} {ι} {f : ι → Nimber}
    (H : ∀ i, IsNthDegreeClosed n (f i)) : IsNthDegreeClosed n (⨆ i, f i) := by
  apply IsNthDegreeClosed.sSup
  simpa

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
  obtain hx₁ | hx₁ := le_or_gt x 1
  · exact IsField.of_le_one hx₁
  · refine ⟨h.toIsRing, fun y hy₀ hy ↦ ?_⟩
    have hp : degree (C y * (X : Nimber[X]) + 1) = 1 := by compute_degree!
    have ⟨r, hr, hr₀⟩ := h.exists_root (hp ▸ one_ne_zero) (by simpa [hp]) fun k ↦ ?_
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
  refine ⟨(IsNthDegreeClosed.toIsField · le_rfl), (.ofMonic · fun p hm hp₀ hp₁ hp ↦ ?_)⟩
  rw [Polynomial.eq_X_add_C_of_degree_le_one hp₁] at hp ⊢
  have hd : p.natDegree = 1 := by
    apply natDegree_eq_of_degree_eq_some
    rw [← Order.succ_le_iff] at hp₀
    exact hp₁.antisymm hp₀
  rw [Monic, leadingCoeff] at hm
  have := hp 0
  aesop

-- We could have proved this earlier, but going through `IsNthDegreeClosed`
-- gives a much shorter proof.
protected theorem IsField.sSup {s : Set Nimber} (H : ∀ x ∈ s, IsField x) :
    IsField (sSup s) := by
  simp_rw [← isNthDegreeClosed_one_iff_isField] at *
  exact IsNthDegreeClosed.sSup H

protected theorem IsField.iSup {ι} {f : ι → Nimber} (H : ∀ i, IsField (f i)) :
    IsField (⨆ i, f i) := by
  apply IsField.sSup
  simpa

proof_wanted IsNthDegreeClosed.omega0 : IsNthDegreeClosed 2 (∗Ordinal.omega0)

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

@[simp]
theorem IsAlgClosed.zero : IsAlgClosed 0 := by
  simp [isAlgClosed_iff_forall]

@[simp]
theorem IsAlgClosed.one : IsAlgClosed 1 := by
  simp [isAlgClosed_iff_forall]

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

end Nimber
