/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Django Peeters
-/
import CombinatorialGames.Nimber.SimplestExtension.Algebraic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.DepRewrite

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

theorem kappa_zero_right_pow (k : ℕ) : kappa k 0 ^ p_ k = alpha k := by
  simp [kappa, alpha]

/-! ### Main induction -/

open Polynomial

/-- We know this already. -/
theorem leastNoRoots_kappa_zero_left (n : ℕ) : leastNoRoots (kappa 0 n) =
    .some (X ^ 2 + X + C (∗(2 ^ (2 ^ n - 1)))) := by
  rw [kappa_zero_left]
  sorry

/-- Let `y` be the field after `x`. Since `x < algClosure 0` we know `y/x` is a cyclic extension. If
`leastNoRoots` has composite degree, then we can find a nontrivial subgroup of `Gal(y/x)`, which
corresponds to an extension of smaller degree, a contradiction. -/
theorem prime_natDegree_leastNoRoots {x : Nimber} (h : IsField x) (hx : x < algClosure 0) :
    ∃ ht, (x.leastNoRoots.untop ht).natDegree.Prime := by
  sorry

/-- Every extension below `τ` (excluding the quadratic extensions) is by an `n`-th root. This is
a consequence of Kummer theory I think? -/
theorem leastNoRoots_kummer {x : Nimber} (h : IsField x) (hx' : ∗ω ≤ x) (hx : x < algClosure 0) :
    ∃ n : ℕ, n.Prime ∧ ∃ a < x, leastNoRoots x = .some (X ^ n + C a) := by
  sorry

/-- If `x` is algebraic over its prime field without extensions of degree `≤ n`, and `y/x` is
algebraic, then `y` has no extensions of degree `≤ n` either. I'm pretty sure this was easy to prove
via the Galois group. -/
theorem monotoneOn_leastNoRoots : MonotoneOn leastNoRoots {x < algClosure 0 | IsField x} := by
  sorry

-- I think these are the things we prove simultaneously:
section Induction

/--
There are two parts to this:

- Prove that polynomials below `X ^ p_ k` are all already covered.
- Prove that not all polynomials `X ^ p_ k + C a` have roots. Then `a = alpha k` by the simplest
  extension theorem. I don't know how to prove this.
-/
theorem leastNoRoots_kappa_zero_right {k : ℕ} (hk : k ≠ 0) :
    leastNoRoots (kappa k 0) = .some (X ^ p_ k + C (alpha k)) := by
  sorry

/--
There are two parts to this:

- Prove that polynomials between `X ^ p_ k` and `X ^ p_ k + C (kappa k n)` are covered. This is
  probably just Kummer theory again, adjoining one n-th root gives you all of them at once.
- Prove that `X ^ p_ k + C (kappa k n)` doesn't have a root. I think I had an argument for this
  using primitive roots but there's gotta be something nicer.
-/
theorem leastNoRoots_kappa_succ_right {k : ℕ} (n : ℕ) (hk : k ≠ 0) :
    leastNoRoots (kappa k (n + 1)) = .some (X ^ p_ k + C (kappa k n)) := by
  sorry

/-- This should follow from everything else we're doing. -/
theorem IsField.kappa (k n : ℕ) : IsField (kappa k n) := by
  sorry

end Induction

theorem degree_leastNoRoots_kappa (k n : ℕ) :
    ∃ ht, ((kappa k n).leastNoRoots.untop ht).degree = p_ k := by
  cases k with
  | zero =>
    rw [leastNoRoots_kappa_zero_left]
    use WithTop.coe_ne_top
    rw [WithTop.untop_coe, Nat.nth_prime_zero_eq_two]
    compute_degree!
  | succ k =>
    cases n with
    | zero =>
      rw [leastNoRoots_kappa_zero_right k.succ_ne_zero]
      use WithTop.coe_ne_top
      rw [WithTop.untop_coe, degree_X_pow_add_C (Nat.nth_prime_pos _)]
    | succ n =>
      rw [leastNoRoots_kappa_succ_right n k.succ_ne_zero]
      use WithTop.coe_ne_top
      rw [WithTop.untop_coe, degree_X_pow_add_C (Nat.nth_prime_pos _)]

theorem leastNoRoots_kappa_ne_top (k n : ℕ) : (kappa k n).leastNoRoots ≠ ⊤ := by
  obtain ⟨ht, -⟩ := degree_leastNoRoots_kappa k n
  exact ht

theorem kappa_succ_right_pow {k : ℕ} (n : ℕ) (hk : k ≠ 0) : kappa k (n + 1) ^ p_ k = kappa k n := by
  have := (IsField.kappa k (n + 1)).isRoot_leastNoRoots (leastNoRoots_kappa_ne_top _ _)
  rw! [leastNoRoots_kappa_succ_right n hk, WithTop.untop_coe] at this
  simpa [CharTwo.add_eq_zero] using this

/-- This follows from `leastNoRoots (kappa k n)` being cofinal. -/
theorem IsAlgClosed.tau : IsAlgClosed τ := by
  sorry

/-- With some extra diligence, we can show `kappa k (n + 1)` is the next field after `kappa k n`, so
that these are the only fields before the first algebraic. None of the `kappa k n` are algebraically
closed, but `τ` is, so the equality follows. -/
@[simp]
theorem algClosure_zero : algClosure 0 = τ := by
  sorry

end Nimber
end
