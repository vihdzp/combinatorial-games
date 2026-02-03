/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Django Peeters
-/
import CombinatorialGames.Nimber.SimplestExtension.Algebraic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.PrimeCounting

/-!
# Nimbers below $\omega^{\omega^\omega}$
-/

local notation "p_ " => Nat.nth Nat.Prime

noncomputable section

@[simp]
theorem Nat.one_lt_nth_prime (n : ℕ) : 1 < p_ n :=
  (Nat.prime_nth_prime n).one_lt

@[simp]
theorem Nat.nth_prime_pos (n : ℕ) : 0 < p_ n :=
  n.one_lt_nth_prime.pos

@[simp, norm_cast]
theorem Ordinal.natCast_ofNat_pow (m n : ℕ) [m.AtLeastTwo] :
    Nat.cast (R := Ordinal) (ofNat(m) ^ n) = ofNat(m) ^ n := by
  simp

attribute [simp] Ordinal.opow_pos

namespace Nimber
open Ordinal

local notation "τ" => ∗(ω ^ ω ^ ω)

/-! ### $\kappa$ and $\alpha$ functions -/

/-- The values $\kappa_{k, n} = \ast 2^{\omega^k p_k^n}$ enumerate the fields below $\tau =
\omega^{\omega^\omega}$ in lexicographic order of $(k, n)$. That is to say, these fields are given
by:

$$\kappa_{0,0} < \kappa_{0,1} < \kappa_{0,2} < \cdots < \kappa_{1,0} < \kappa_{1,1} < \kappa_{1,2} <
\cdots < \kappa_{2,0} < \kappa_{2,1} < \kappa_{2,2} < \cdots$$

In the literature, these values are denoted as $\kappa_{p_k^n}$, but for simplicity we unbundle
the values of $k$ and $n$ instead. -/
def kappa (k n : ℕ) : Nimber :=
  ∗2 ^ (ω ^ k * p_ k ^ n)

theorem kappa_succ_left (k n : ℕ) : kappa (k + 1) n = ∗(ω ^ (ω ^ k * p_ (k + 1) ^ n)) := by
  rw [kappa, pow_succ', opow_mul, opow_mul, opow_omega0 one_lt_two (nat_lt_omega0 2), ← opow_mul]

@[simp]
theorem kappa_zero_left (n : ℕ) : kappa 0 n = ∗(2 ^ 2 ^ n) := by
  simp [kappa, ← opow_natCast]

@[simp]
theorem kappa_one_left (n : ℕ) : kappa 1 n = ∗(ω ^ 3 ^ n) := by
  rw [kappa_succ_left]
  simp [← opow_natCast]

theorem kappa_strictMono : StrictMono fun x : ℕ ×ₗ ℕ ↦ kappa (ofLex x).1 (ofLex x).2 := by
  simp_rw [StrictMono, Lex.forall]
  rintro ⟨k₁, n₁⟩ ⟨k₂, n₂⟩ (⟨n₁, n₂, hk⟩ | ⟨n, hk⟩) <;> dsimp [kappa]
  · rw [of.lt_iff_lt, opow_lt_opow_iff_right one_lt_two]
    simp_rw [← opow_natCast, ← natCast_opow]
    apply (omega0_opow_mul_nat_lt (Nat.cast_lt.2 hk) _).trans_le (Ordinal.le_mul_left _ _)
    simp
  · rw [of.lt_iff_lt, opow_lt_opow_iff_right one_lt_two]
    apply mul_lt_mul_of_pos_left (pow_lt_pow_right₀ _ hk) <;> simp

theorem kappa_lt_kappa_iff {k₁ k₂ n₁ n₂ : ℕ} :
    kappa k₁ n₁ < kappa k₂ n₂ ↔ k₁ < k₂ ∨ k₁ = k₂ ∧ n₁ < n₂ :=
  (kappa_strictMono.lt_iff_lt (a := toLex (k₁, n₁)) (b := toLex (k₂, n₂))).trans Prod.Lex.lt_iff

theorem kappa_le_kappa_iff {k₁ k₂ n₁ n₂ : ℕ} :
    kappa k₁ n₁ ≤ kappa k₂ n₂ ↔ k₁ < k₂ ∨ k₁ = k₂ ∧ n₁ ≤ n₂ :=
  (kappa_strictMono.le_iff_le (a := toLex (k₁, n₁)) (b := toLex (k₂, n₂))).trans Prod.Lex.le_iff

theorem kappa_lt_tau (k n : ℕ) : kappa k n < τ := by
  cases k with
  | zero =>
    rw [kappa_zero_left, of.lt_iff_lt]
    apply lt_of_lt_of_le _ (left_le_opow _ _)
    · exact_mod_cast nat_lt_omega0 (2 ^ 2 ^ n)
    · simp
  | succ k =>
    rw [kappa_succ_left, of.lt_iff_lt, opow_lt_opow_iff_right one_lt_omega0]
    simp_rw [← opow_natCast, ← natCast_opow]
    exact omega0_opow_mul_nat_lt (nat_lt_omega0 _) _

theorem lt_tau_iff {x : Nimber} : x < τ ↔ ∃ k n, x < kappa k n := by
  constructor
  · rw [← val_lt_iff]
    simp only [ne_eq, omega0_ne_zero, not_false_eq_true, isSuccLimit_omega0, isSuccLimit_opow_left,
      lt_opow_of_isSuccLimit, lt_omega0, ↓existsAndEq, opow_natCast, true_and, forall_exists_index,
      and_imp]
    refine fun y k hy hx ↦ ⟨k + 1, 0, ?_⟩
    rw [kappa_succ_left, ← val_lt_iff]
    apply hx.trans
    simpa
  · rintro ⟨k, n, h⟩
    exact h.trans (kappa_lt_tau k n)

/-- The values $\alpha_k = (\ast 2^{ω^k})^{p_k}$ give the smallest value without $p_k$-th roots in
$\kappa_{k,0}$, for $k \ne 0$.

As field extensions, we have $\kappa_{k,1} = \kappa_{k,0}(\alpha_k)$ and $\kappa_{k,n+2} =
\kappa_{k,n+1}(\kappa_{k,n})$.

In the literature, these values are denoted as $\alpha_{p_k}$, but for simplicity we unbundle the
value of $k$ instead. -/
def alpha (k : ℕ) : Nimber :=
  (∗(2 ^ ω ^ k)) ^ p_ k

@[simp]
theorem alpha_zero : alpha 0 = ∗3 := by
  simp [alpha]
  sorry -- missing (∗2)^2 = ∗3

proof_wanted alpha_one : alpha 1 = ∗2
proof_wanted alpha_two : alpha 2 = ∗4
proof_wanted alpha_three : alpha 3 = ∗(ω + 1)
-- ...

/-! ### Main induction -/

theorem degree_leastNoRoots_kappa (k n : ℕ) :
    ∃ ht, ((leastNoRoots (kappa k n)).untop ht).degree = p_ k := by
  sorry

theorem kappa_zero_right_pow (k : ℕ) : kappa k 0 ^ p_ k = alpha k := by
  simp [kappa, alpha]

theorem kappa_succ_right_pow (k n : ℕ) : kappa k (n + 1) ^ p_ k = kappa k n := by
  sorry

theorem IsField.kappa (k n : ℕ) : IsField (kappa k n) :=
  sorry

end Nimber
end
