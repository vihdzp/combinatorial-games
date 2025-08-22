/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Nimber.SimplestExtension.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Finsupp.WellFounded

/-!
# Nimber polynomials

This file contains multiple auxiliary results and definitions for working with nimber polynomials:

- `IsField.embed`: embeds a polynomial `p : Nimber[X]` into the subfield `Iio x`, for `IsField x`.
-/

universe u

open Order Polynomial

/-! ### For Mathlib -/

-- TODO: should some of these be global?
attribute [local aesop simp] Function.update coeff_one coeff_C coeff_X

namespace Polynomial

variable {R : Type*} [Semiring R] {p : R[X]}

@[simp]
theorem coeffs_nonempty_iff : p.coeffs.Nonempty ↔ p ≠ 0 := by
  simp [Finset.nonempty_iff_ne_empty]

theorem natDegree_eq_zero_iff : p.natDegree = 0 ↔ p = 0 ∨ p.degree = 0 := by
  rw [p.natDegree_eq_zero_iff_degree_le_zero, le_iff_lt_or_eq, ← WithBot.coe_zero, ← bot_eq_zero',
    WithBot.lt_coe_bot, p.degree_eq_bot]

end Polynomial

-- Generalize to a SuccAddOrder
@[simp]
theorem WithBot.lt_add_one {x : WithBot ℕ} (n : ℕ) : x < WithBot.some n + 1 ↔ x ≤ n := by
  cases x
  · simp [bot_lt_iff_ne_bot]
  · rw [← WithBot.coe_add_one, WithBot.coe_lt_coe]
    simp

namespace Nimber

/-! ### Basic results -/

theorem polynomial_eq_zero_of_le_one {x : Nimber} {p : Nimber[X]}
    (hx₁ : x ≤ 1) (h : ∀ k, p.coeff k < x) : p = 0 := by
  ext k; simpa using (h k).trans_le hx₁

theorem IsRing.eval_lt {x y : Nimber} (h : IsRing x) {p : Nimber[X]} (hp : ∀ k, p.coeff k < x)
    (hy : y < x) : p.eval y < x := by
  obtain hx₁ | hx₁ := le_or_gt x 1
  · have := polynomial_eq_zero_of_le_one hx₁ hp
    simp_all
  · rw [eval_eq_sum]
    exact h.sum_lt hx₁.ne_bot fun n hn ↦ h.mul_lt (hp _) (h.pow_lt hx₁ hy)

theorem coeff_X_pow_lt {x : Nimber} (n : ℕ) (h : 1 < x) : ∀ k, (X ^ n).coeff k < x := by
  have : 0 < x := h.bot_lt
  aesop

theorem IsGroup.coeff_add_lt {x : Nimber} {p q : Nimber[X]} (h : IsGroup x)
    (hp : ∀ k, p.coeff k < x) (hq : ∀ k, q.coeff k < x) : ∀ k, (p + q).coeff k < x := by
  intro k
  rw [coeff_add]
  exact h.add_lt (hp k) (hq k)

theorem IsGroup.coeff_sum_lt {x : Nimber} {ι} {f : ι → Nimber[X]} {s : Finset ι} (h : IsGroup x)
    (hx₀ : x ≠ 0) (hs : ∀ y ∈ s, ∀ k, (f y).coeff k < x) : ∀ k, (s.sum f).coeff k < x := by
  intro k
  rw [finset_sum_coeff]
  exact h.sum_lt hx₀ fun y hy ↦ (hs y hy k)

theorem IsRing.coeff_mul_lt {x : Nimber} {p q : Nimber[X]} (h : IsRing x)
    (hp : ∀ k, p.coeff k < x) (hq : ∀ k, q.coeff k < x) : ∀ k, (p * q).coeff k < x := by
  intro k
  rw [coeff_mul]
  exact h.sum_lt (hp 0).ne_bot fun y hy ↦ h.mul_lt (hp _) (hq _)

theorem IsRing.coeff_prod_lt {x : Nimber} {ι} {f : ι → Nimber[X]} {s : Finset ι} (h : IsRing x)
    (hx₁ : 1 < x) (hs : ∀ y ∈ s, ∀ k, (f y).coeff k < x) : ∀ k, (s.prod f).coeff k < x := by
  classical
  induction s using Finset.induction with
  | empty =>
    have := zero_lt_one.trans hx₁
    aesop
  | insert y s hy IH =>
    rw [Finset.prod_insert hy]
    apply h.coeff_mul_lt <;> simp_all

/-! ### Embedding in a subfield -/

/-- Reinterpret a polynomial in the nimbers as a polynomial in the subfield `x`.

We could define this under the weaker assumption `IsRing`, but due to proof erasure, this leads to
issues where `Field (h.toSubring ⋯)` can't be inferred, even if `h : IsField x`. -/
def IsField.embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) (p : Nimber[X])
    (hp : ∀ k, p.coeff k < x) : (h.toSubfield hx₁)[X] :=
  .ofFinsupp <| .mk p.support (fun k ↦ ⟨p.coeff k, hp k⟩) (by simp [← Subtype.val_inj])

@[simp]
theorem IsField.coeff_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) (k : ℕ) : (h.embed hx₁ p hp).coeff k = ⟨p.coeff k, hp k⟩ :=
  rfl

@[simp]
theorem IsField.degree_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) : (h.embed hx₁ p hp).degree = p.degree :=
  rfl

@[simp]
theorem IsField.leadingCoeff_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) : (h.embed hx₁ p hp).leadingCoeff = ⟨p.leadingCoeff, hp _⟩ :=
  rfl

@[simp]
theorem IsField.map_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) : (h.embed hx₁ p hp).map (Subfield.subtype _) = p := by
  ext; simp

@[simp]
theorem IsField.embed_C {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {y hy} :
    h.embed hx₁ (C y) hy = C ⟨y, by simpa using hy 0⟩ := by
  ext
  simp_rw [h.coeff_embed, coeff_C]
  split_ifs <;> rfl

@[simp]
theorem IsField.eval_embed {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hp : ∀ k, p.coeff k < x) (y) : (h.embed hx₁ p hp).eval y = ⟨_, h.eval_lt hp y.2⟩ := by
  simp [← Subtype.val_inj, embed, sum, eval_eq_sum]

/-! ### Lexicographic ordering on polynomials -/

namespace Lex

/-- The lexicographic ordering on nimber polynomials. -/
noncomputable instance : LinearOrder (Nimber[X]) where
  lt p q := ∃ n, (∀ k, n < k → p.coeff k = q.coeff k) ∧ p.coeff n < q.coeff n
  __ := LinearOrder.lift'
    (fun p : Nimber[X] ↦ toLex <| p.toFinsupp.equivMapDomain OrderDual.toDual) <| by
      intro p q h
      rw [toLex_inj, Finsupp.ext_iff] at h
      rwa [← toFinsupp_inj, Finsupp.ext_iff]

theorem lt_def {p q : Nimber[X]} : p < q ↔ ∃ n,
    (∀ k, n < k → p.coeff k = q.coeff k) ∧ p.coeff n < q.coeff n :=
  .rfl

instance : WellFoundedLT (Lex (ℕᵒᵈ →₀ Nimber)) where
  wf := Finsupp.Lex.wellFounded' Nimber.not_lt_zero lt_wf (wellFounded_lt (α := ℕ))

instance : WellFoundedLT (Nimber[X]) where
  wf := InvImage.wf
    (fun p : Nimber[X] ↦ toLex <| p.toFinsupp.equivMapDomain OrderDual.toDual) wellFounded_lt

noncomputable instance : OrderBot (Nimber[X]) where
  bot := 0
  bot_le p := by rw [← not_lt, lt_def]; simp

@[simp] theorem bot_eq_zero : (⊥ : Nimber[X]) = 0 := rfl
@[simp] theorem le_zero_iff {p : Nimber[X]} : p ≤ 0 ↔ p = 0 := le_bot_iff

noncomputable instance : ConditionallyCompleteLinearOrderBot (Nimber[X]) :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

theorem forall_lt_quadratic {P : Nimber[X] → Prop} {x y z : Nimber} :
    (∀ p < C x * X ^ 2 + C y * X + C z, P p) ↔
      (∀ c < z, P (C x * X ^ 2 + C y * X + C c)) ∧
      (∀ b < y, ∀ c, P (C x * X ^ 2 + C b * X + C c)) ∧
      (∀ a < x, ∀ b c, P (C a * X ^ 2 + C b * X + C c)) := by
  refine ⟨fun H ↦
    ⟨fun c hc ↦ H _ ⟨0, by aesop⟩, fun b hb c ↦ H _ ⟨1, by aesop⟩, fun a ha b c ↦ H _ ⟨2, by aesop⟩⟩,
    fun ⟨H₁, H₂, H₃⟩ p ⟨n, hn, hp⟩ ↦ ?_⟩
  match n with
  | 0 =>
    have : p.coeff 0 < z := by simpa using hp
    convert H₁ _ this
    ext k
    match k with | 0 | 1 | 2 | k + 3 => aesop
  | 1 =>
    have : p.coeff 1 < y := by simpa using hp
    convert H₂ _ this (p.coeff 0)
    ext k
    match k with | 0 | 1 | 2 | k + 3 => aesop
  | 2 =>
    have : p.coeff 2 < x := by simpa using hp
    convert H₃ _ this (p.coeff 1) (p.coeff 0)
    ext k
    match k with | 0 | 1 | 2 | k + 3 => aesop
  | n + 3 => simp at hp

theorem forall_le_quadratic {P : Nimber[X] → Prop} {x y z : Nimber} :
    (∀ p ≤ C x * X ^ 2 + C y * X + C z, P p) ↔
      (∀ c ≤ z, P (C x * X ^ 2 + C y * X + C c)) ∧
      (∀ b < y, ∀ c, P (C x * X ^ 2 + C b * X + C c)) ∧
      (∀ a < x, ∀ b c, P (C a * X ^ 2 + C b * X + C c)) := by
  simp_rw [le_iff_eq_or_lt, forall_eq_or_imp, forall_lt_quadratic]
  tauto

theorem exists_lt_quadratic {P : Nimber[X] → Prop} {x y z : Nimber} :
    (∃ p < C x * X ^ 2 + C y * X + C z, P p) ↔
      (∃ c < z, P (C x * X ^ 2 + C y * X + C c)) ∨
      (∃ b < y, ∃ c, P (C x * X ^ 2 + C b * X + C c)) ∨
      (∃ a < x, ∃ b c, P (C a * X ^ 2 + C b * X + C c)) := by
  rw [← not_iff_not]; simpa using forall_lt_quadratic

theorem exists_le_quadratic {P : Nimber[X] → Prop} {x y z : Nimber} :
    (∃ p ≤ C x * X ^ 2 + C y * X + C z, P p) ↔
      (∃ c ≤ z, P (C x * X ^ 2 + C y * X + C c)) ∨
      (∃ b < y, ∃ c, P (C x * X ^ 2 + C b * X + C c)) ∨
      (∃ a < x, ∃ b c, P (C a * X ^ 2 + C b * X + C c)) := by
  rw [← not_iff_not]; simpa using forall_le_quadratic

theorem forall_lt_linear {P : Nimber[X] → Prop} {x y : Nimber} :
    (∀ p < C x * X + C y, P p) ↔
      (∀ b < y, P (C x * X + C b)) ∧ (∀ a < x, ∀ b, P (C a * X + C b)) := by
  convert @forall_lt_quadratic P 0 x y using 2 <;> simp

theorem forall_le_linear {P : Nimber[X] → Prop} {x y : Nimber} :
    (∀ p ≤ C x * X + C y, P p) ↔
      (∀ b ≤ y, P (C x * X + C b)) ∧ (∀ a < x, ∀ b, P (C a * X + C b)) := by
  convert @forall_le_quadratic P 0 x y using 2 <;> simp

theorem exists_lt_linear {P : Nimber[X] → Prop} {x y : Nimber} :
    (∃ p < C x * X + C y, P p) ↔
      (∃ b < y, P (C x * X + C b)) ∨ (∃ a < x, ∃ b, P (C a * X + C b)) := by
  convert @exists_lt_quadratic P 0 x y using 2 <;> simp

theorem exists_le_linear {P : Nimber[X] → Prop} {x y : Nimber} :
    (∃ p ≤ C x * X + C y, P p) ↔
      (∃ b ≤ y, P (C x * X + C b)) ∨ (∃ a < x, ∃ b, P (C a * X + C b)) := by
  convert @exists_le_quadratic P 0 x y using 2 <;> simp

@[simp]
theorem forall_lt_C {P : Nimber[X] → Prop} {x : Nimber} :
    (∀ p < C x, P p) ↔ ∀ a < x, P (C a) := by
  convert @forall_lt_linear P 0 x using 2 <;> simp

@[simp]
theorem forall_le_C {P : Nimber[X] → Prop} {x : Nimber} :
    (∀ y ≤ C x, P y) ↔ ∀ y ≤ x, P (C y) := by
  convert @forall_le_linear P 0 x using 2 <;> simp

@[simp]
theorem exists_lt_C {P : Nimber[X] → Prop} {x : Nimber} :
    (∃ y < C x, P y) ↔ ∃ y < x, P (C y) := by
  convert @exists_lt_linear P 0 x using 2 <;> simp

@[simp]
theorem exists_le_C {P : Nimber[X] → Prop} {x : Nimber} :
    (∃ y ≤ C x, P y) ↔ ∃ y ≤ x, P (C y) := by
  convert @exists_le_linear P 0 x using 2 <;> simp

theorem degree_mono : Monotone (α := Nimber[X]) degree := by
  intro p q h
  obtain rfl | hq₀ := eq_or_ne q 0; aesop
  contrapose! h
  have h' := natDegree_lt_natDegree hq₀ h
  refine ⟨p.natDegree, fun k hk ↦ ?_, ?_⟩
  · rw [p.coeff_eq_zero_of_natDegree_lt hk, q.coeff_eq_zero_of_natDegree_lt (h'.trans hk)]
  · rw [q.coeff_eq_zero_of_natDegree_lt h']
    aesop (add simp [Nimber.pos_iff_ne_zero])

theorem natDegree_mono : Monotone (α := Nimber[X]) natDegree := by
  apply Monotone.comp (fun a b ↦ ?_) degree_mono
  cases a <;> cases b <;> aesop

theorem C_strictMono : StrictMono (α := Nimber) C := by
  intro x y h
  use 0
  aesop

@[simp]
theorem C_lt_C_iff {x y : Nimber} : C x < C y ↔ x < y :=
  C_strictMono.lt_iff_lt

theorem lt_of_degree_lt {p q : Nimber[X]} (h : p.degree < q.degree) : p < q := by
  contrapose! h; exact degree_mono h

theorem lt_of_natDegree_lt {p q : Nimber[X]} (h : p.natDegree < q.natDegree) : p < q := by
  contrapose! h; exact natDegree_mono h

@[simp]
theorem lt_X_pow_iff {p : Nimber[X]} {n : ℕ} : p < X ^ n ↔ p.degree < n := by
  simp_rw [lt_def, degree_lt_iff_coeff_zero, le_iff_lt_or_eq]
  refine ⟨?_, fun _ ↦ ⟨n, ?_⟩⟩ <;> aesop

@[simp]
theorem coe_lt_X_pow_iff {p : Nimber[X]} {n : ℕ} : WithTop.some p < .some X ^ n ↔ p.degree < n := by
  rw [← WithTop.coe_pow, WithTop.coe_lt_coe, lt_X_pow_iff]

@[simp]
theorem X_pow_le_iff {p : Nimber[X]} {n : ℕ} : X ^ n ≤ p ↔ n ≤ p.degree := by
  rw [← not_lt, lt_X_pow_iff, not_lt]

@[simp]
theorem X_pow_le_coe_iff {p : Nimber[X]} {n : ℕ} : .some X ^ n ≤ WithTop.some p ↔ n ≤ p.degree := by
  rw [← not_lt, coe_lt_X_pow_iff, not_lt]

theorem X_pow_add_lt {p q : Nimber[X]} (hm : p.Monic) (h : q < X ^ p.natDegree + p) :
    X ^ p.natDegree + q < p := by
  have hd := degree_mono h.le
  obtain ⟨n, hn, hn'⟩ := h
  have hnp : n < p.natDegree := by
    by_contra! hnp
    apply hn'.ne_bot
    obtain rfl | hnp := hnp.eq_or_lt
    · simp [hm]
    · rw [coeff_eq_zero_of_natDegree_lt, Nimber.bot_eq_zero]
      apply (natDegree_add_le ..).trans_lt
      simpa
  have hp₀ : p ≠ 0 := by aesop
  refine ⟨n, fun k hk ↦ ?_, ?_⟩
  · rw [coeff_add, coeff_X_pow]
    split_ifs with hk'
    · subst hk'
      rw [q.coeff_eq_zero_of_degree_lt, hm.coeff_natDegree, add_zero]
      apply hd.trans_lt
      rw [add_comm, ← CharTwo.sub_eq_add, self_sub_X_pow_of_monic hm, ← degree_eq_natDegree hp₀]
      exact degree_eraseLead_lt hp₀
    · rw [zero_add, hn k hk, coeff_add, coeff_X_pow, if_neg hk', zero_add]
  · rwa [coeff_add, coeff_X_pow, if_neg hnp.ne, zero_add] at hn' ⊢

theorem X_pow_add_le {p q : Nimber[X]} (hm : p.Monic) (h : q ≤ X ^ p.natDegree + p) :
    X ^ p.natDegree + q ≤ p := by
  obtain rfl | h := h.eq_or_lt
  · rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add] -- CharTwo.add_cancel_left
  · exact (X_pow_add_lt hm h).le

theorem mul_leadingCoeff_inv_lt {p : Nimber[X]} (h₀ : p ≠ 0) (h₁ : ¬p.Monic) :
    p * C p.leadingCoeff⁻¹ < p := by
  refine ⟨p.natDegree, fun k hk ↦ ?_, ?_⟩
  · rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt hk]
    rwa [natDegree_mul_leadingCoeff_inv _ h₀]
  · obtain hp₁ | hp₁ := le_or_gt p.leadingCoeff 1
    · obtain _ | _ := le_one_iff.1 hp₁ <;> simp_all [Monic]
    · aesop

theorem mul_leadingCoeff_inv_le (p : Nimber[X]) :
    p * C p.leadingCoeff⁻¹ ≤ p := by
  obtain rfl | h₀ := eq_or_ne p 0; simp
  by_cases h₁ : p.leadingCoeff = 1; simp [h₁]
  exact (mul_leadingCoeff_inv_lt h₀ h₁).le

instance : NoMaxOrder (Nimber[X]) where
  exists_gt p := by
    use X ^ (p.natDegree + 1)
    simpa using degree_le_natDegree

noncomputable instance : SuccOrder (Nimber.{u}[X]) := by
  have (a b) (h : a < b) : b ≠ 0 := h.ne_bot -- Used by `aesop`
  refine .ofCore (fun p ↦ .ofFinsupp (p.toFinsupp.update 0 (succ (p.coeff 0)))) ?_ (by simp)
  refine @fun p _ q ↦ ⟨fun hpq ↦ ?_, ?_⟩
  · obtain ⟨n, hn, hpq⟩ := hpq
    cases n with
    | zero =>
      obtain hpq' | hpq' := (succ_le_of_lt hpq).lt_or_eq
      · refine le_of_lt ⟨0, ?_⟩
        aesop
      · apply le_of_eq
        ext k
        cases k <;> aesop
    | succ n => refine le_of_lt ⟨n + 1, ?_⟩; aesop
  · rw [le_iff_lt_or_eq]
    rintro (hpq | rfl)
    · obtain ⟨n, hn, hpq⟩ := hpq
      refine ⟨n, fun k hk ↦ ?_, ?_⟩
      · specialize hn k hk
        aesop
      · have (a b : Nimber.{u}) (h : succ a < b) : a < b := (le_succ a).trans_lt h
        aesop
    · use 0
      aesop

@[aesop simp]
theorem coeff_succ (p : Nimber[X]) :
    (succ p).coeff = Function.update p.coeff 0 (succ (p.coeff 0)) := by
  change coeff (Polynomial.ofFinsupp _) = _
  simp
  rfl

@[simp]
theorem coeff_succ_zero (p : Nimber[X]) :
    (succ p).coeff 0 = succ (p.coeff 0) := by
  rw [coeff_succ, Function.update_self]

@[simp]
theorem coeff_succ_of_ne_zero (p : Nimber[X]) {k : ℕ} (h : k ≠ 0) :
    (succ p).coeff k = p.coeff k := by
  rw [coeff_succ, Function.update_of_ne h]

theorem succ_eq_add_one_of_coeff_zero {p : Nimber[X]} (h : p.coeff 0 = 0) : succ p = p + 1 := by
  aesop

end Lex

end Nimber
