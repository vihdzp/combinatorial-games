/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Nimber.Simplicity.Basic

/-!
# Nimber polynomials

This file contains multiple auxiliary results and definitions for working with nimber polynomials:

- `IsField.embed`: embeds a polynomial `p : Nimber[X]` into the subfield `Iio x`, for `IsField x`.
- `Lex.instLinearOrderPolynomial`: a linear order instance on nimber polynomials, defined as the
  lexicographic ordering.
- `oeval`: evaluate a nimber polynomial using ordinal arithmetic.
- `leastNotSplit x`: the smallest non-constant polynomial in `x` without roots less than `x`.
-/

universe u

open Order Polynomial

/-! ### For Mathlib-/

-- TODO: should some of these be global?
attribute [local aesop simp] Function.update coeff_one coeff_C coeff_X

-- I wish we had a typeclass for `⊥ = 0`.
theorem List.le_sum_of_mem' {M} [AddMonoid M] [PartialOrder M] [OrderBot M]
    [AddLeftMono M] [AddRightMono M]
    (hm : (⊥ : M) = 0) {xs : List M} {x : M} (h₁ : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at h₁
  | cons y ys ih =>
    simp only [List.mem_cons] at h₁
    rcases h₁ with (rfl | h₁)
    · rw [List.sum_cons]
      conv_lhs => rw [← add_zero x]
      apply add_left_mono
      rw [← hm]
      exact bot_le
    · specialize ih h₁
      simp only [List.sum_cons]
      apply ih.trans
      conv_lhs => rw [← zero_add ys.sum]
      apply add_right_mono
      rw [← hm]
      exact bot_le

namespace Polynomial

variable {R : Type*} [Semiring R] {p : R[X]}

@[simp]
theorem coeffs_nonempty_iff : p.coeffs.Nonempty ↔ p ≠ 0 := by
  simp [Finset.nonempty_iff_ne_empty]

theorem natDegree_eq_zero_iff : p.natDegree = 0 ↔ p = 0 ∨ p.degree = 0 := by
  rw [p.natDegree_eq_zero_iff_degree_le_zero, le_iff_lt_or_eq, ← WithBot.coe_zero, ← bot_eq_zero',
    WithBot.lt_coe_bot, p.degree_eq_bot]

-- TODO: can I use `eraseLead` here instead?
theorem eq_C_mul_X_pow_add_of_degree_le {R} [Ring R] {p : R[X]} {n : ℕ} (h : p.degree ≤ n) :
    ∃ (a : R) (q : R[X]), p = C a * X ^ n + q ∧ q.degree < n := by
  obtain hp | hp := h.lt_or_eq
  · use 0, p
    simpa
  · refine ⟨p.coeff n, p - C (p.coeff n) * X ^ n, ?_, ?_⟩
    · rw [_root_.add_sub_cancel]
    · apply (degree_sub_lt _ (by aesop) _).trans_le h
      · rw [hp, degree_C_mul_X_pow _ (p.coeff_ne_zero_of_eq_degree hp)]
      · rw [leadingCoeff, p.natDegree_eq_of_degree_eq_some hp]
        simp

theorem degree_pos_of_mem_roots {R} [CommRing R] [IsDomain R] {p : R[X]} {r} (h : r ∈ p.roots) :
    0 < p.degree := by
  by_contra!
  rw [p.eq_C_of_degree_le_zero this, roots_C] at h
  cases h

theorem monomial_induction {motive : R[X] → Prop} (zero : motive 0)
    (add : ∀ a n q, degree q < .some n → motive q → motive (C a * X ^ n + q)) (p : R[X]) :
    motive p := by
  induction hn : p.degree using WellFoundedLT.induction generalizing p with | ind n IH
  cases n with
  | bot => simp_all
  | coe n =>
    rw [← eraseLead_add_C_mul_X_pow p, add_comm]
    have hp₀ : p ≠ 0 := by aesop
    have hpn : p.eraseLead.degree < .some n := hn ▸ degree_eraseLead_lt hp₀
    apply add _ _ _ ((degree_eraseLead_lt hp₀).trans_eq _) (IH _ hpn _ rfl)
    rw [hn, natDegree_eq_of_degree_eq_some hn]

theorem eval_X_pow {R} [CommRing R] (x : R) (n : ℕ) : eval x (X ^ n : R[X]) = x ^ n := by simp

theorem self_sub_X_pow_of_monic {R} [Ring R] {p : R[X]} (h : p.Monic) :
    p - X ^ p.natDegree = p.eraseLead := by
  rw [← self_sub_C_mul_X_pow, h, C_1, one_mul]

alias ⟨_, IsRoot.mul_div_eq⟩ := mul_div_eq_iff_isRoot

end Polynomial

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
    apply h.coeff_mul_lt <;> aesop

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

/-- Evaluate a nimber polynomial using ordinal arithmetic. -/
def oeval (x : Nimber) (p : Nimber[X]) : Nimber :=
  ∗((List.range (p.natDegree + 1)).reverse.map fun k ↦ x.val ^ k * (p.coeff k).val).sum

@[simp]
theorem oeval_zero (x : Nimber) : oeval x 0 = 0 := by
  simp [oeval]

theorem oeval_eq_of_natDegree_le {p : Nimber[X]} {n : ℕ} (h : p.natDegree + 1 ≤ n) (x : Nimber) :
    oeval x p = ∗((List.range n).reverse.map fun k ↦ x.val ^ k * (p.coeff k).val).sum := by
  induction n with
  | zero => simp at h
  | succ n IH =>
    obtain h | h := h.eq_or_lt
    · rw [oeval, h]
    · rw [add_lt_add_iff_right] at h
      rw [List.range_succ]
      simpa [p.coeff_eq_zero_of_natDegree_lt h] using IH h

theorem oeval_C_mul_X_pow_add {n : ℕ} {p : Nimber[X]} (hp : p.degree < n) (x a : Nimber) :
    oeval x (C a * X ^ n + p) = ∗(x.val ^ n * a.val + val (oeval x p)) := by
  obtain rfl | ha := eq_or_ne a 0; simp [oeval]
  · have hp' : p.natDegree ≤ n := p.natDegree_le_of_degree_le hp.le
    have hp'' : (C a * X ^ n + p).natDegree ≤ n := by compute_degree!
    rw [oeval_eq_of_natDegree_le (add_right_mono hp'),
      oeval_eq_of_natDegree_le (add_right_mono hp'')]
    cases n with
    | zero => simp_all
    | succ n =>
      suffices (List.range n).map
        (fun k ↦ val x ^ k * val ((if k = n + 1 then a else 0) + p.coeff k)) =
      (List.range n).map (fun k ↦ val x ^ k * val (p.coeff k)) by
        simp [List.range_succ, p.coeff_eq_zero_of_degree_lt hp, this]
      apply List.map_congr_left
      aesop

theorem oeval_eq (x : Nimber) (p : Nimber[X]) :
    oeval x p = ∗(x.val ^ p.natDegree * p.leadingCoeff.val + val (oeval x p.eraseLead)) := by
  obtain rfl | hp₀ := eq_or_ne p 0; simp
  conv_lhs => rw [← eraseLead_add_C_mul_X_pow p, add_comm]
  exact oeval_C_mul_X_pow_add ((degree_eraseLead_lt hp₀).trans_eq (degree_eq_natDegree hp₀)) ..

@[simp]
theorem oeval_X_pow_mul (x : Nimber) (n : ℕ) (p : Nimber[X]) :
    oeval x (X ^ n * p) = ∗(x.val ^ n * (oeval x p).val) := by
  induction p using monomial_induction with
  | zero => simp
  | add a m p hp IH =>
    rw [mul_add, mul_comm, mul_assoc, ← pow_add, oeval_C_mul_X_pow_add, oeval_C_mul_X_pow_add hp, IH]
    · simp [mul_add, ← mul_assoc, ← pow_add, add_comm]
    · rwa [degree_mul, degree_X_pow, add_comm, WithBot.natCast_eq_coe, WithBot.natCast_eq_coe,
        WithBot.coe_add, WithBot.add_lt_add_iff_right WithBot.coe_ne_bot]

@[simp]
theorem oeval_mul_X_pow (x : Nimber) (n : ℕ) (p : Nimber[X]) :
    oeval x (p * X ^ n) = ∗(x.val ^ n * (oeval x p).val) := by
  rw [mul_comm, oeval_X_pow_mul]

theorem oeval_C_mul_X_pow (x a : Nimber) (n : ℕ) :
    oeval x (C a * X ^ n) = ∗(x.val ^ n * a.val) := by
  simpa using oeval_C_mul_X_pow_add (p := 0) (WithBot.bot_lt_coe n) x a

@[simp]
theorem oeval_X_pow (x : Nimber) (n : ℕ) : oeval x (X ^ n) = ∗(x.val ^ n) := by
  simpa using oeval_C_mul_X_pow x 1 n

@[simp]
theorem oeval_X (x : Nimber) : oeval x X = x := by
  simpa using oeval_X_pow x 1

@[simp]
theorem oeval_C (x a : Nimber) : oeval x (C a) = a := by
  simpa using oeval_C_mul_X_pow x a 0

@[simp]
theorem oeval_one (x : Nimber) : oeval x 1 = 1 := by
  simpa using oeval_C x 1

theorem mul_coeff_le_oeval (x : Nimber) (p : Nimber[X]) (k : ℕ) :
    ∗(x.val ^ k * (p.coeff k).val) ≤ oeval x p := by
  obtain rfl | hp₀ := eq_or_ne p 0; simp
  obtain hk | hk := le_or_gt k p.natDegree
  · rw [oeval, of.le_iff_le]
    apply List.le_sum_of_mem' rfl
    aesop
  · rw [p.coeff_eq_zero_of_natDegree_lt hk]
    simp

theorem opow_natDegree_le_oeval (x : Nimber) {p : Nimber[X]} (hp : p ≠ 0) :
    ∗(x.val ^ p.natDegree) ≤ oeval x p := by
  apply (Ordinal.le_mul_left ..).trans (mul_coeff_le_oeval x p p.natDegree)
  simpa [Ordinal.pos_iff_ne_zero]

theorem oeval_lt_opow {x : Nimber} {p : Nimber[X]} {n : ℕ}
    (hpk : ∀ k, p.coeff k < x) (hn : p.degree < n) : val (oeval x p) < ∗(x.val ^ n) := by
  obtain rfl | hx₀ := x.eq_zero_or_pos; simp at hpk
  induction n generalizing p with
  | zero => simp_all
  | succ n IH =>
    have hn' : p.degree ≤ n := le_of_lt_succ hn
    obtain ⟨a, q, rfl, hq⟩ := eq_C_mul_X_pow_add_of_degree_le hn'
    rw [oeval_C_mul_X_pow_add hq, val_of, pow_succ]
    refine Ordinal.mul_add_lt (IH (fun k ↦ ?_) hq) ?_
    · obtain h | h := lt_or_ge k n
      · convert hpk k using 1
        aesop
      · rwa [q.coeff_eq_zero_of_degree_lt (hq.trans_le (mod_cast h))]
    · simpa [q.coeff_eq_zero_of_degree_lt hq] using hpk n

theorem oeval_lt_opow_iff {x : Nimber} {p : Nimber[X]} {n : ℕ}
    (hpk : ∀ k, p.coeff k < x) : val (oeval x p) < ∗(x.val ^ n) ↔ p.degree < n where
  mp H := by
    obtain rfl | hp₀ := eq_or_ne p 0; simp
    obtain hx₁ | hx₁ := le_or_gt x 1; cases hp₀ <| polynomial_eq_zero_of_le_one hx₁ hpk
    have H' := (opow_natDegree_le_oeval x hp₀).trans_lt H
    rw [of.lt_iff_lt, ← Ordinal.opow_natCast, ← Ordinal.opow_natCast,
      Ordinal.opow_lt_opow_iff_right (a := x.val) hx₁] at H'
    rw [← natDegree_lt_iff_degree_lt hp₀]
    simpa using H'
  mpr := oeval_lt_opow hpk

theorem oeval_split {x : Nimber} {p q : Nimber[X]} {n : ℕ}
    (hp : ∀ k < n, p.coeff k = 0) (hq : ∀ k, n ≤ k → q.coeff k = 0) :
    oeval x (p + q) = oeval x p + oeval x q := by
  induction n generalizing p q with
  | zero =>
    obtain rfl : q = 0 := by ext; simp_all
    simp
  | succ n IH => sorry

theorem oeval_split' {x : Nimber} {p q : Nimber[X]} {n : ℕ}
    (hp : ∀ k ≤ n, p.coeff k = 0) (hq : ∀ k, n < k → q.coeff k = 0) :
    oeval x (p + q) = oeval x p + oeval x q :=
  oeval_split (n := n + 1) (by simpa) hq

theorem oeval_lt_of_lt {x : Nimber} {p q : Nimber[X]} (h : p < q)
    (hpk : ∀ k, p.coeff k < x) (hqk : ∀ k, q.coeff k < x) : oeval x p < oeval x q := by
  sorry

theorem eq_oeval_of_lt_oeval {x y : Nimber} {p : Nimber[X]} (hx₀ : x ≠ 0) (h : y < oeval x p) :
    ∃ q : Nimber[X], q < p ∧ (∀ k, val (q.coeff k) < x) ∧ oeval x q = y := by
  sorry

theorem eq_oeval_of_lt_opow {x y : Nimber} {n : ℕ} (hx₀ : x ≠ 0) (h : y < of (x.val ^ n)) :
    ∃ p : Nimber[X], p.degree < n ∧ (∀ k, p.coeff k < x) ∧ oeval x p = y := by
  rw [← oeval_X_pow] at h
  obtain ⟨q, hqn, hqk, rfl⟩ := eq_oeval_of_lt_oeval hx₀ h
  refine ⟨q, ?_, hqk, rfl⟩
  simpa using hqn

theorem forall_lt_oeval_iff {x : Nimber} (hx₁ : 1 < x) {P : Ordinal → Prop}
    {p : Nimber[X]} (hpk : ∀ k, p.coeff k < x) :
    (∀ y < oeval x p, P y) ↔ ∀ q < p, (∀ k, q.coeff k < x) → P (oeval x q) where
  mp H q hqp hqk := H _ <| oeval_lt_of_lt hqp hqk hpk
  mpr H y hy := by
    obtain ⟨q, hqn, hqk, rfl⟩ := eq_oeval_of_lt_oeval hx₁.ne_bot hy
    exact H q hqn hqk

/-! ### Least irreducible polynomial -/

/-- Returns the lexicographically earliest non-constant polynomial, all of whose coefficients are
less than `x`, without any roots less than `x`. If none exists, returns `⊤`.

This function takes values on `WithTop (Nimber[X])`, which is a well-ordered complete lattice (the
order on `Nimber[X]` is the lexicographic order). -/
noncomputable def leastNotSplit (x : Nimber) : WithTop (Nimber[X]) :=
  sInf (WithTop.some '' {p | 0 < p.degree ∧ (∀ k, p.coeff k < x) ∧ ∀ r < x, p.eval r ≠ 0})

private theorem leastNotSplit_mem {x : Nimber} (ht) :
    x.leastNotSplit.untop ht ∈
      {p | 0 < p.degree ∧ (∀ k, p.coeff k < x) ∧ ∀ r < x, p.eval r ≠ 0} := by
  obtain hs | hs := ({p : Nimber[X] |
    0 < p.degree ∧ (∀ k, p.coeff k < x) ∧ ∀ r < x, p.eval r ≠ 0}).eq_empty_or_nonempty
  · simp [leastNotSplit, hs] at ht
  · convert csInf_mem hs
    rw [← WithTop.coe_inj, WithTop.coe_untop, leastNotSplit, WithTop.coe_sInf' hs]
    exact OrderBot.bddBelow _

theorem degree_leastNotSplit_pos {x : Nimber} (ht) :
    0 < (x.leastNotSplit.untop ht).degree :=
  (leastNotSplit_mem ht).1

theorem natDegree_leastNotSplit_pos {x : Nimber} (ht) :
    0 < (x.leastNotSplit.untop ht).natDegree :=
  natDegree_pos_iff_degree_pos.2 (degree_leastNotSplit_pos ht)

theorem coeff_leastNotSplit_lt {x : Nimber} (ht) :
    ∀ k, (x.leastNotSplit.untop ht).coeff k < x :=
  (leastNotSplit_mem ht).2.1

theorem leastNotSplit_not_root_of_lt {x r : Nimber} (ht) (hr : r < x) :
    (x.leastNotSplit.untop ht).eval r ≠ 0 :=
  (leastNotSplit_mem ht).2.2 r hr

@[simp]
theorem leastNotSplit_zero : leastNotSplit 0 = ⊤ := by
  simp [leastNotSplit]

@[simp]
theorem coeff_leastNotSplit_zero_ne {x : Nimber} (ht) :
    (x.leastNotSplit.untop ht).coeff 0 ≠ 0 := by
  obtain rfl | hx := eq_bot_or_bot_lt x
  · simp at ht
  · rw [coeff_zero_eq_eval_zero]
    exact leastNotSplit_not_root_of_lt _ hx

@[simp]
theorem leastNotSplit_ne_zero (x : Nimber) : leastNotSplit x ≠ 0 := by
  intro h
  have ht := h ▸ WithTop.zero_ne_top
  simpa [h] using coeff_leastNotSplit_zero_ne ht

@[simp]
theorem leastNotSplit_ne_zero' {x : Nimber} (ht) : x.leastNotSplit.untop ht ≠ 0 := by
  rw [← WithTop.coe_inj.ne]
  simp

theorem leastNotSplit_ne_X_pow' (x : Nimber) (n : ℕ) (ht) :
    x.leastNotSplit.untop ht ≠ X ^ n := by
  cases n with
  | zero =>
    have := degree_leastNotSplit_pos ht
    aesop
  | succ n =>
    apply_fun (coeff · 0)
    simp

theorem leastNotSplit_ne_X_pow (x : Nimber) (n : ℕ) :
    leastNotSplit x ≠ .some (X ^ n) := by
  intro hp
  have ht := hp ▸ WithTop.coe_ne_top
  rw [← WithTop.coe_untop _ ht, WithTop.coe_inj] at hp
  exact (leastNotSplit_ne_X_pow' _ _ _) hp

-- TODO: upstream attr.
attribute [simp] mem_lowerBounds

theorem leastNotSplit_le_of_not_isRoot {x : Nimber} {p : Nimber[X]}
    (hp₀ : 0 < p.degree) (hpk : ∀ k, p.coeff k < x) (hr : ∀ r < x, ¬ p.IsRoot r) :
    leastNotSplit x ≤ p := by
  rw [leastNotSplit, sInf_le_iff]
  aesop

theorem has_root_of_lt_leastNotSplit {x : Nimber} {p : Nimber[X]}
    (hp₀ : p.degree ≠ 0) (hpk : ∀ k, p.coeff k < x) (hpn : p < leastNotSplit x) :
    ∃ r < x, p.IsRoot r := by
  obtain hp | hp₀ := le_or_gt p.degree 0
  · have := WithBot.le_zero_iff.1 hp; aesop
  contrapose! hpn
  exact leastNotSplit_le_of_not_isRoot hp₀ hpk hpn

theorem IsField.has_root_subfield {x : Nimber} (h : IsField x)
    (hx₁ : 1 < x) {p : (h.toSubfield hx₁)[X]} (hp₀ : p.degree ≠ 0)
    (hpn : map (Subfield.subtype _) p < leastNotSplit x) : ∃ r, p.IsRoot r := by
  have hd : (p.map (Subring.subtype _)).degree = p.degree := by simpa using (em _).symm
  obtain ⟨r, hr, hr'⟩ := has_root_of_lt_leastNotSplit (hd ▸ hp₀) (by simp) hpn
  exact ⟨⟨r, hr⟩, (isRoot_map_iff (Subring.subtype_injective _)).1 hr'⟩

theorem IsField.splits_subfield {x : Nimber} (h : IsField x) (hx₁ : 1 < x)
    {p : (h.toSubfield hx₁)[X]} (hpn : map (Subfield.subtype _) p < leastNotSplit x) :
    p.Splits (.id _) := by
  obtain hp₀ | hp₀ := le_or_gt p.degree 0
  · exact splits_of_degree_le_one _ (hp₀.trans zero_le_one)
  induction hp : p.degree using WellFoundedLT.induction generalizing p with | ind n IH
  subst hp
  obtain ⟨r, hr⟩ := h.has_root_subfield hx₁ hp₀.ne' hpn
  rw [← hr.mul_div_eq]
  apply splits_mul _ (splits_X_sub_C _)
  obtain hp₀' | hp₀' := le_or_gt (p / (X - C r)).degree 1
  · exact splits_of_degree_le_one _ hp₀'
  · have hp : (p / (X - C r)).degree < p.degree := by apply degree_div_lt <;> aesop
    apply IH _ hp _ (zero_lt_one.trans hp₀') rfl
    apply (WithTop.coe_strictMono (Lex.lt_of_degree_lt _)).trans hpn
    simpa

theorem IsField.roots_eq_map {x : Nimber} (h : IsField x) (hx₁ : 1 < x) {p : Nimber[X]}
    (hpn : p < leastNotSplit x) (hpk : ∀ k, p.coeff k < x) :
    p.roots = (h.embed hx₁ p hpk).roots.map (Subfield.subtype _) := by
  simpa using roots_map (Subfield.subtype _)
    (h.splits_subfield hx₁ (p := h.embed hx₁ p hpk) (by simpa))

theorem IsField.root_lt {x r : Nimber} (h : IsField x) {p : Nimber[X]}
    (hpn : p < leastNotSplit x) (hpk : ∀ k, p.coeff k < x) (hr : r ∈ p.roots) : r < x := by
  obtain hx₁ | hx₁ := le_or_gt x 1; simp [polynomial_eq_zero_of_le_one hx₁ hpk] at hr
  have := h.roots_eq_map hx₁ hpn hpk ▸ hr; aesop

attribute [simp] Polynomial.map_multiset_prod
theorem IsField.eq_prod_roots_of_lt_leastNotSplit {x : Nimber} (h : IsField x)
    {p : Nimber[X]} (hpn : p < leastNotSplit x) (hpk : ∀ k, p.coeff k < x) :
    p = C p.leadingCoeff * (p.roots.map fun a ↦ X - C a).prod := by
  obtain rfl | hp₀ := eq_or_ne p 0; simp
  have hx₁ := lt_of_not_ge fun h ↦ hp₀ (polynomial_eq_zero_of_le_one h hpk)
  have hs := h.splits_subfield hx₁ (p := h.embed hx₁ p hpk) (by simpa)
  conv_lhs => rw [← h.map_embed hx₁ hpk, eq_prod_roots_of_splits_id hs]
  simp [h.roots_eq_map hx₁ hpn hpk]

attribute [-simp] WithTop.coe_add WithTop.coe_mul WithTop.coe_pow

theorem IsRing.leastNotSplit_eq_of_not_isField {x : Nimber} (h : IsRing x) (h' : ¬ IsField x) :
    leastNotSplit x = .some (C x⁻¹ * X + 1) := by
  have hx₁ : 1 < x := by by_contra! hx; cases h' <| IsField.of_le_one hx
  have hx₀ : x ≠ 0 := hx₁.ne_bot
  apply le_antisymm
  · refine leastNotSplit_le_of_not_isRoot ?_ ?_ fun r hr H ↦ ?_
    · convert zero_lt_one' (WithBot ℕ)
      dsimp
      compute_degree!
    · have := h.inv_lt_self_of_not_isField h'
      apply h.coeff_add_lt (h.coeff_mul_lt _ _) <;> aesop (add simp [Nimber.pos_iff_ne_zero])
    · replace H : x⁻¹ * r + 1 = 0 := by simpa using H
      rw [Nimber.add_eq_zero] at H
      obtain rfl := eq_of_inv_mul_eq_one H
      exact hr.false
  · apply le_of_forall_ne
    rw [WithTop.forall_lt_coe, ← C_1, Lex.forall_lt_linear]
    refine ⟨?_, fun y hy z ht ↦ ?_⟩
    · simp_rw [lt_one_iff_zero, forall_eq, map_zero, add_zero]
      intro ht
      have ht' := ht ▸ WithTop.coe_ne_top
      simpa [← ht] using coeff_leastNotSplit_zero_ne ht'
    · have ht' := ht ▸ WithTop.coe_ne_top
      apply leastNotSplit_not_root_of_lt ht' (r := z / y)
      · apply h.mul_lt _ (h.inv_lt_of_not_isField h' hy)
        simpa [← ht] using coeff_leastNotSplit_lt ht' 0
      · have hy₀ : y ≠ 0 := by
          rintro rfl
          apply (degree_C_le (R := Nimber)).not_gt
          simpa [← ht] using degree_leastNotSplit_pos ht'
        simp [← ht, mul_div_cancel₀, hy₀]

theorem IsField.monic_leastNotSplit {x : Nimber} (h : IsField x) (ht) :
    Monic (x.leastNotSplit.untop ht) := by
  by_contra! hm
  let c := (x.leastNotSplit.untop ht).leadingCoeff
  have hm' : 1 < c := by
    rw [← not_le, le_one_iff]
    simp_all [c, Monic]
  apply (leastNotSplit_le_of_not_isRoot _ _ _).not_gt
  · conv_rhs => rw [← WithTop.coe_untop _ ht]
    rw [WithTop.coe_lt_coe]
    exact Lex.mul_leadingCoeff_inv_lt (leastNotSplit_ne_zero' ht) hm
  · rw [degree_mul]
    apply WithBot.add_pos_of_pos_of_nonneg
    · exact degree_leastNotSplit_pos _
    · aesop
  · have H := coeff_leastNotSplit_lt ht
    have : c⁻¹ < x := h.inv_lt (H _)
    apply h.coeff_mul_lt <;> aesop (add simp [Nimber.pos_iff_ne_zero])
  · have := @leastNotSplit_not_root_of_lt x
    aesop

end Nimber
