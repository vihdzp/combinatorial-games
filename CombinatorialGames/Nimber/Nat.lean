/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Nimber.SimplestExtension.Algebraic
import CombinatorialGames.Mathlib.Hilbert90
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Order.Interval.Set.Nat
import Mathlib.RingTheory.Trace.Defs

/-!
# Finite nimber arithmetic

This file defines the type alias `NatNimber` of the natural numbers, endowed with nimber arithmetic.
The goal is to define the field structure computably, and prove that it matches that on `Nimber`.
-/

theorem Subfield.coe_pow {F : Type*} [DivisionRing F] {K : Subfield F} (x : K) (n : ℕ) :
    ((x ^ n : K) : F) = (x : F) ^ n := rfl

alias! /-- The natural numbers, endowed with nim operations. -/ NatNimber Nat

namespace NatNimber

instance : LinearOrder NatNimber := Nat.instLinearOrder

instance : Lean.ToExpr NatNimber where
  toExpr x := .app (.const `NatNimber.of []) (Lean.toExpr x.val)
  toTypeExpr := .const `NatNimber []

instance : ToString NatNimber where
  toString x := "∗" ++ x.val.repr

@[simp] theorem lt_one_iff_zero {a : NatNimber} : a < 1 ↔ a = 0 := Nat.lt_one_iff
@[simp] theorem one_le_iff_ne_zero {a : NatNimber} : 1 ≤ a ↔ a ≠ 0 := Nat.one_le_iff_ne_zero
theorem le_one_iff {a : NatNimber} : a ≤ 1 ↔ a = 0 ∨ a = 1 := Nat.le_one_iff_eq_zero_or_eq_one

/-- The embedding `NatNimber ↪o Nimber`. -/
def toNimber : NatNimber ↪o Nimber where
  toFun x := .of x.val
  inj' x y := by simp
  map_rel_iff' := by simp

@[simp] theorem toNimber_zero : toNimber 0 = 0 := rfl
@[simp] theorem toNimber_one : toNimber 1 = 1 := by simp [toNimber]
@[simp] theorem toNimber_of (n : ℕ) : toNimber (of n) = Nimber.of n := rfl

instance : Neg NatNimber where
  neg n := n

instance : Add NatNimber where
  add m n := of (m.val ^^^ n.val)

instance : Sub NatNimber where
  sub m n := m + n

@[simp]
theorem toNimber_add (x y : NatNimber) : toNimber (x + y) = .of x.val + .of y.val :=
  (Nimber.add_nat ..).symm

@[simp] theorem sub_eq (x y : NatNimber) : x - y = x + y := rfl
@[simp] theorem neg_eq (x : NatNimber) : -x = x := rfl

/-- Multiplies `x` by `∗2 ^ (2 ^ t - 1)`, whenever `x < ∗2 ^ 2 ^ t`. This is a subroutine needed to
multiply two general nimbers. This makes use of the formula:

$$(a2^{2^t}+b)2^{2^{t+1}-1} = (a2^{2^t-1})2^{2^t-1}+((a+b)2^{2^t-1})2^{2^t}$$

for $a, b < \ast 2 ^ {2 ^ t}$. -/
private def mulHalf (t : ℕ) (x : NatNimber) : NatNimber :=
  match t with
  | 0 => x
  | t + 1 =>
    let a := of (x.val / 2 ^ 2 ^ t)
    let b := of (x.val % 2 ^ 2 ^ t)
    of ((mulHalf t (a + b)).val * 2 ^ 2 ^ t) + mulHalf t (mulHalf t a)

/-- Multiplies `x` by `y`, whenever `x, y < ∗2 ^ 2 ^ t`. This makes use of the formula:

$$(a2^{2^t}+b)(c2^{2^t}+d)=(ac)2^{2^t-1}+(ac+ad+bc)2^{2^t}+bd$$

for $a, b, c, d < \ast 2 ^ {2 ^ t}$. -/
private def mul (t : ℕ) (x y : NatNimber) : NatNimber :=
  match t with
  | 0 => if x = 0 then 0 else if y = 0 then 0 else 1
  | t + 1 =>
    let a := of (x.val / 2 ^ 2 ^ t)
    let b := of (x.val % 2 ^ 2 ^ t)
    let c := of (y.val / 2 ^ 2 ^ t)
    let d := of (y.val % 2 ^ 2 ^ t)
    let z := mul t a c
    mulHalf t z + of ((z + mul t a d + mul t b c).val * 2 ^ 2 ^ t) + mul t b d

-- TODO: prove correctness
instance : Mul NatNimber where
  mul x y := mul (max x.val.log2.log2 y.val.log2.log2 + 1) x y

end NatNimber

example : Nimber.of 3 + Nimber.of 5 = Nimber.of 6 := by
  have : NatNimber.of 3 + NatNimber.of 5 = NatNimber.of 6 := by decide
  apply_fun NatNimber.toNimber at this
  simpa

namespace Nimber

theorem one_lt_two_two_pow (n : ℕ) : 1 < ∗Nat.cast (2 ^ 2 ^ n) := by
  rw [← of_one, of.lt_iff_lt, ← Nat.cast_one, Nat.cast_lt]
  simp

theorem lt_two_iff {x : Nimber} : x < ∗2 ↔ x = 0 ∨ x = 1 := by
  induction x with | mk x
  simp [← Ordinal.succ_one, Ordinal.le_one_iff]

theorem IsField.two : IsField (∗2) where
  ne_zero := by simp
  ne_one := by simp
  add_lt := by
    simp_rw [lt_two_iff]
    aesop
  mul_lt := by
    simp_rw [lt_two_iff]
    aesop
  inv_lt' := by
    simp_rw [lt_two_iff]
    aesop

private theorem two_two_pow_le {n m : ℕ} (h : n ≤ m) :
    ∗Nat.cast (2 ^ 2 ^ n) ≤ ∗Nat.cast (2 ^ 2 ^ m) :=
  of.monotone (Nat.cast_le.2
    (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) h)))

private theorem two_two_pow_lt {n m : ℕ} (h : n < m) :
    ∗Nat.cast (2 ^ 2 ^ n) < ∗Nat.cast (2 ^ 2 ^ m) :=
  of.strictMono (Nat.cast_lt.2
    (Nat.pow_lt_pow_right (by decide) (Nat.pow_lt_pow_right (by decide) h)))

theorem ncard_Iio_natCast (n : ℕ) : Set.ncard (Set.Iio (∗Nat.cast n)) = n := by
  suffices h : IsLowerSet (Set.range (Nat.castOrderEmbedding.trans of.toOrderEmbedding)) by
    rw [← Nat.castOrderEmbedding_apply, ← OrderIso.coe_toOrderEmbedding,
      ← RelEmbedding.trans_apply, ← OrderEmbedding.image_Iio _ h,
      Set.ncard_image_of_injective _ (RelEmbedding.injective _), Set.ncard_Iio_nat]
  intro a b hba ha
  obtain ⟨a, rfl⟩ := ha
  induction b with | mk b -- this case should be called `of`
  obtain ⟨b, rfl⟩ := Ordinal.lt_omega0.1 ((of.le_iff_le.1 hba).trans_lt (Ordinal.nat_lt_omega0 _))
  exact Set.mem_range_self b

theorem finite_Iio_natCast (n : ℕ) : (Set.Iio (∗Nat.cast n)).Finite := by
  cases n with
  | zero => simp
  | succ => exact Set.finite_of_ncard_ne_zero ((ncard_Iio_natCast _).trans_ne (by simp))

open Polynomial

private theorem coeff_polynomial_lt (n k : ℕ) :
    (C 1 * X ^ 2 + C 1 * X + C (∗Nat.cast (2 ^ (2 ^ n - 1)))).coeff k < ∗Nat.cast (2 ^ 2 ^ n) := by
  rw [← val_lt_iff]
  simp only [map_one, one_mul, coeff_add, coeff_X_pow, coeff_X, coeff_C]
  by_cases hk : k < 3
  · interval_cases k <;> simp only [↓reduceIte, Nat.reduceEqDiff]
    · rw [zero_add, zero_add, val_of, Nat.cast_lt]
      exact Nat.pow_lt_pow_right (by decide) (by simp)
    · rw [zero_add, add_zero, val_one, ← Nat.cast_one, Nat.cast_lt]
      simp
    · rw [add_zero, add_zero, val_one, ← Nat.cast_one, Nat.cast_lt]
      simp
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      zero_add, zero_add, val_zero, ← Nat.cast_zero, Nat.cast_lt]
    simp

mutual

theorem IsField.two_two_pow (n : ℕ) : IsField (∗Nat.cast (2 ^ 2 ^ n)) := by
  cases n with
  | zero => simpa using IsField.two
  | succ n =>
    have hf := IsField.two_two_pow n
    have he : Nat.cast (2 ^ 2 ^ (n + 1)) = (val (∗Nat.cast (2 ^ 2 ^ n))) ^ 2 := by
      rw [val_of, ← Ordinal.opow_natCast, Nat.pow_succ, Nat.pow_mul]
      simp
    rw [he]
    apply hf.pow_degree_leastNoRoots (leastNoRoots_eq n)
    compute_degree!
termination_by (n, 0)

private theorem algebraTrace_eq {m n : ℕ} (h : m ≤ n) :
  ∃ (hm : IsField (∗Nat.cast (2 ^ 2 ^ m))) (hn : IsField (∗Nat.cast (2 ^ 2 ^ n))),
    let algebra : Algebra hm.toSubfield hn.toSubfield :=
      Subfield.inclusion (Set.Iio_subset_Iio (two_two_pow_le h)) |>.toAlgebra
    ∀ x hx, Algebra.trace hm.toSubfield hn.toSubfield ⟨∗Nat.cast x, hx⟩ =
      ∗Nat.cast (x / 2 ^ (2 ^ n - 2 ^ m)) := by
  have hf : IsField (∗Nat.cast (2 ^ 2 ^ n)) := .two_two_pow n
  have hfm (m : ℕ) (hm : m < n) : IsField (∗Nat.cast (2 ^ 2 ^ m)) := .two_two_pow m
  obtain _ | h := Nat.eq_or_lt_of_le h
  · subst m
    exact ⟨hf, hf, by simp⟩
  refine ⟨hfm m h, hf, ?_⟩
  intro algebra x hx
  cases n with | zero => simp at h | succ n
  let algl : Algebra (hfm m h).toSubfield (hfm n (by simp)).toSubfield :=
    Subfield.inclusion (Set.Iio_subset_Iio (two_two_pow_le (by omega))) |>.toAlgebra
  let algu : Algebra (hfm n (by simp)).toSubfield hf.toSubfield :=
    Subfield.inclusion (Set.Iio_subset_Iio (two_two_pow_le (by simp))) |>.toAlgebra
  have : IsScalarTower (hfm m h).toSubfield (hfm n (by simp)).toSubfield hf.toSubfield :=
    ⟨fun a b c => Subtype.ext (mul_assoc a.1 b.1 c.1)⟩
  have : Finite (hfm n (by simp)).toSubfield :=
    Set.Finite.to_subtype (finite_Iio_natCast (2 ^ 2 ^ n))
  have : Finite hf.toSubfield :=
    Set.Finite.to_subtype (finite_Iio_natCast (2 ^ 2 ^ (n + 1)))
  have : Module.Finite (hfm m h).toSubfield (hfm n (by simp)).toSubfield := .of_finite
  have : Module.Finite (hfm n (by simp)).toSubfield hf.toSubfield := .of_finite
  let ux : hf.toSubfield := ⟨∗Nat.cast x, hx⟩
  let ua := Algebra.trace (hfm n (by simp)).toSubfield hf.toSubfield ux
  suffices ht : ua = ∗Nat.cast (x / 2 ^ (2 ^ n)) by
    rw [← @Algebra.trace_trace (hfm m h).toSubfield (hfm n (by simp)).toSubfield hf.toSubfield]
    conv =>
      enter [1, 1, 2]
      equals ⟨∗Nat.cast (x / 2 ^ (2 ^ n)), ht ▸ ua.2⟩ => exact Subtype.ext ht
    rw [(algebraTrace_eq (Nat.le_of_lt_add_one h)).2.2, Nat.div_div_eq_div_mul, ← Nat.pow_add,
      ← Nat.add_sub_assoc (Nat.pow_le_pow_right (by simp) (by omega)),
      ← Nat.mul_two, ← Nat.pow_add_one]
  change (algebraMap (hfm n (by simp)).toSubfield hf.toSubfield ua).1 = ∗Nat.cast (x / 2 ^ (2 ^ n))
  set d := x / 2 ^ 2 ^ n
  set r := x % 2 ^ 2 ^ n
  have hdr : 2 ^ 2 ^ n * d + r = x := Nat.div_add_mod x (2 ^ 2 ^ n)
  have hd : d < 2 ^ 2 ^ n := Nat.div_lt_of_lt_mul
    ((Nat.cast_lt.1 (of.lt_iff_lt.1 hx)).trans_eq (by simp [Nat.pow_add_one, Nat.pow_mul]))
  have hr : r < 2 ^ 2 ^ n := Nat.mod_lt x (by simp)
  clear_value d r
  let u2 : hf.toSubfield := ⟨∗Nat.cast (2 ^ 2 ^ n), two_two_pow_lt (by simp)⟩
  let d2 : (hfm n (by simp)).toSubfield := ⟨∗Nat.cast d, of.strictMono (Nat.cast_lt.2 hd)⟩
  let r2 : (hfm n (by simp)).toSubfield := ⟨∗Nat.cast r, of.strictMono (Nat.cast_lt.2 hr)⟩
  subst hdr
  have hdr : ux = u2 * (algebraMap (hfm n (by simp)).toSubfield hf.toSubfield d2) +
      (algebraMap (hfm n (by simp)).toSubfield hf.toSubfield r2) := by
    ext
    change ∗Nat.cast _ = ∗Nat.cast _ * ∗Nat.cast _ + ∗Nat.cast _
    rw [Nat.cast_add, Ordinal.natCast_mul, IsGroup.mul_add_eq_of_lt' (by simp) (Nat.cast_lt.2 hr),
      (hfm n (by simp)).mul_eq_of_lt' (hfm n (by simp)).toIsRing le_rfl (Nat.cast_lt.2 hd), of_val]
  unfold ua
  have card2 : Module.finrank (hfm n (by simp)).toSubfield hf.toSubfield = 2 := by
    have hcn : Nat.card (hfm n (by simp)).toSubfield = 2 ^ 2 ^ n :=
      (Nat.card_coe_set_eq _).trans (ncard_Iio_natCast _)
    have hcf : Nat.card hf.toSubfield = 2 ^ 2 ^ (n + 1) :=
      (Nat.card_coe_set_eq _).trans (ncard_Iio_natCast _)
    rw [← Nat.pow_right_inj (lt_of_lt_of_eq (by simp) hcn.symm),
      ← Module.natCard_eq_pow_finrank, hcn, hcf, Nat.pow_add_one, Nat.pow_mul]
  rw [hdr, map_add, map_add, Algebra.trace_algebraMap, card2, CharTwo.two_nsmul,
    map_zero, add_zero, mul_comm u2, ← Algebra.smul_def, map_smul, smul_eq_mul, map_mul]
  refine mul_right_eq_self₀.mpr (.inl ?_)
  have h22 : ∗Nat.cast (2 ^ (2 ^ n - 1)) < ∗Nat.cast (2 ^ 2 ^ n) := by
    simpa using coeff_polynomial_lt n 0
  have poly : minpoly (hfm n (by simp)).toSubfield u2 =
      X ^ 2 + X + C ⟨∗Nat.cast (2 ^ (2 ^ n - 1)), h22⟩ := by
    have hl := leastNoRoots_eq n
    have ht : (∗Nat.cast (2 ^ 2 ^ n)).leastNoRoots ≠ ⊤ :=
      fun h => WithTop.coe_ne_top (hl.symm.trans h)
    have uk : (hfm n (by simp)).embed
        ((∗Nat.cast (2 ^ 2 ^ n)).leastNoRoots.untop ht) (coeff_leastNoRoots_lt ht) =
        X ^ 2 + X + C ⟨∗Nat.cast (2 ^ (2 ^ n - 1)), h22⟩ := by
      rw [← (map_injective _ (hfm n (by simp)).toSubfield.subtype_injective).eq_iff,
        IsField.map_embed, (WithTop.untop_eq_iff ht).2 hl]
      simp
    refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ (by monicity!)).symm
    · rw [← uk]
      exact (hfm n (by simp)).irreducible_embed_leastNoRoots ht
    · ext
      rw [← uk, Subfield.coe_zero, aeval_def, eval₂_eq_eval_map]
      change hf.toSubfield.subtype _ = 0
      rw [← eval_map_apply, map_map]
      change eval (∗Nat.cast (2 ^ 2 ^ n)) (map (hfm n (by simp)).toSubfield.subtype _) = 0
      rw [IsField.map_embed]
      exact (hfm n (by simp)).isRoot_leastNoRoots ht
  have degree : Module.finrank
      (IntermediateField.adjoin (hfm n (by simp)).toSubfield {u2}) hf.toSubfield = 1 := by
    have ho : @Module.finrank (hfm n (by simp)).toSubfield
        (IntermediateField.adjoin (hfm n (by simp)).toSubfield {u2})
        -- typeclass times out if I don't explicitly specify the module instance :(
        _ _ (IntermediateField.module' _) = 2 := by
      rw [IntermediateField.adjoin.finrank (minpoly.ne_zero_iff.1 (poly.trans_ne
        (ne_of_apply_ne (coeff · 1) (by simp)))), poly]
      compute_degree!
    refine (Nat.mul_right_inj (ho.trans_ne two_ne_zero)).mp ?_
    rw [Module.finrank_mul_finrank, card2, ho, mul_one]
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, poly, degree,
    nextCoeff_of_natDegree_pos (Nat.zero_lt_two.trans_eq (Eq.symm (by compute_degree!))),
    show natDegree _ = 2 by compute_degree!]
  simp
termination_by (n, 1)

theorem leastNoRoots_eq (n : ℕ) : leastNoRoots (∗Nat.cast (2 ^ 2 ^ n)) =
    WithTop.some (C 1 * X ^ 2 + C 1 * X + C (∗Nat.cast (2 ^ (2 ^ n - 1)))) := by
  have hf := IsField.two_two_pow n
  have : Finite hf.toSubfield := Set.Finite.to_subtype (finite_Iio_natCast (2 ^ 2 ^ n))
  let algebra : Algebra (IsField.two.toSubfield) hf.toSubfield :=
    Subfield.inclusion (Set.Iio_subset_Iio
      (by simpa using two_two_pow_le (Nat.zero_le n))) |>.toAlgebra
  let : Fintype IsField.two.toSubfield :=
    { elems := Finset.cons 0 {1} (by simp)
      complete x := by simpa using Nimber.lt_two_iff.1 x.2 }
  have card2 : Fintype.card IsField.two.toSubfield = 2 := rfl
  have tr (x : hf.toSubfield) :
      Algebra.trace IsField.two.toSubfield hf.toSubfield (x ^ 2 + x) = 0 := by
    conv =>
      enter [1, 2, 1, 2]
      rw [← card2]
    rw [map_add, ← FiniteField.frobeniusAlgEquiv_apply IsField.two.toSubfield hf.toSubfield 2,
      Algebra.trace_eq_of_algEquiv, CharTwo.add_self_eq_zero]
  apply le_antisymm
  · apply leastNoRoots_le_of_not_isRoot
    · refine zero_lt_two.trans_eq (Eq.symm ?_)
      compute_degree!
    · exact coeff_polynomial_lt n
    · intro r hr
      induction r with | mk r
      obtain ⟨r, rfl⟩ := Ordinal.lt_omega0.1 ((of.lt_iff_lt.1 hr).trans (Ordinal.nat_lt_omega0 _))
      simp only [map_one, one_mul, IsRoot.def, eval_add, eval_pow, eval_X, eval_C]
      rw [CharTwo.add_eq_zero]
      have h22 : ∗Nat.cast (2 ^ (2 ^ n - 1)) < ∗Nat.cast (2 ^ 2 ^ n) := by
        simpa using coeff_polynomial_lt n 0
      let or : hf.toSubfield := ⟨∗Nat.cast r, hr⟩
      let oc : hf.toSubfield := ⟨_, h22⟩
      change hf.toSubfield.subtype (or ^ 2 + or) ≠ hf.toSubfield.subtype oc
      rw [hf.toSubfield.subtype_injective.ne_iff]
      apply ne_of_apply_ne (Algebra.trace IsField.two.toSubfield hf.toSubfield)
      rw [tr, ne_eq, ← SetLike.coe_eq_coe, (algebraTrace_eq (Nat.zero_le n)).2.2,
        Subfield.coe_zero, ← val_eq_iff, val_zero, ← Nat.cast_zero, Nat.cast_inj]
      simp
  · apply le_of_forall_lt_imp_ne
    intro c hc heq
    cases c with | top => simp at hc | coe c
    rw [WithTop.coe_lt_coe] at hc
    have ht : (∗Nat.cast (2 ^ 2 ^ n)).leastNoRoots ≠ ⊤ := fun h => WithTop.coe_ne_top (heq.trans h)
    have coeff := coeff_leastNoRoots_lt ht
    have degree := natDegree_leastNoRoots_pos ht
    rw [← (WithTop.eq_untop_iff ht).2 heq] at coeff degree
    suffices h : ∃ r : hf.toSubfield, eval (hf.toSubfield.subtype r) c = 0 by
      obtain ⟨r, hr⟩ := h
      apply leastNoRoots_not_root_of_lt ht r.2
      rw [← (WithTop.eq_untop_iff ht).2 heq]
      exact hr
    clear heq
    revert c
    rw [Lex.forall_lt_quadratic, and_comm]
    refine ⟨⟨fun b hb c coeff _ => ?_, fun a ha b c coeff degree => ?_⟩,
      fun c hcs coeff _ => ?_⟩
    · rw [lt_one_iff_zero] at hb
      subst hb
      have hc : c < ∗Nat.cast (2 ^ 2 ^ n) := by simpa using coeff 0
      obtain ⟨r, hr⟩ := surjective_frobenius hf.toSubfield 2 ⟨c, hc⟩
      exact ⟨r, by simpa [← SetLike.coe_eq_coe, frobenius_def] using CharTwo.add_eq_zero.2 hr⟩
    · rw [lt_one_iff_zero] at ha
      subst ha
      have hb : b < ∗Nat.cast (2 ^ 2 ^ n) := by simpa using coeff 1
      have hc : c < ∗Nat.cast (2 ^ 2 ^ n) := by simpa using coeff 0
      have hb0 : b ≠ 0 := fun hb0 => by simp [hb0] at degree
      let ub : hf.toSubfield := ⟨b, hb⟩
      let uc : hf.toSubfield := ⟨c, hc⟩
      exact ⟨ub⁻¹ * uc, by simp [ub, uc, hb0]⟩
    · have hc : c < ∗Nat.cast (2 ^ 2 ^ n) := by simpa using coeff 0
      have hg (g : Gal(hf.toSubfield/IsField.two.toSubfield)) :
          g ∈ Subgroup.zpowers (FiniteField.frobeniusAlgEquivOfAlgebraic _ _) := by
        obtain ⟨k, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow _ _).surjective g
        apply pow_mem
        exact Subgroup.mem_zpowers _
      have tc : Algebra.trace IsField.two.toSubfield hf.toSubfield ⟨c, hc⟩ = 0 := by
        induction c with | mk c
        obtain ⟨c, rfl⟩ := Ordinal.lt_omega0.1 ((of.lt_iff_lt.1 hc).trans (Ordinal.nat_lt_omega0 _))
        rw [← SetLike.coe_eq_coe, Subfield.coe_zero, (algebraTrace_eq (Nat.zero_le n)).2.2,
          of_eq_iff, val_zero, Nat.cast_eq_zero]
        rw [of.lt_iff_lt, Nat.cast_lt] at hcs
        rw [Nat.pow_zero, Nat.div_eq_zero_iff_lt (by simp)]
        exact hcs
      obtain ⟨r, hr⟩ := groupCohomology.exists_sub_of_trace_eq_zero hg tc
      rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply, card2, ← SetLike.coe_eq_coe,
        Subfield.coe_sub, Subfield.coe_pow, CharTwo.sub_eq_add, add_comm] at hr
      exact ⟨r, by simp [hr]⟩
termination_by (n, 2)

end

end Nimber
