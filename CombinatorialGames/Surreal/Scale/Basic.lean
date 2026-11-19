/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Coset.ResidueField
public import CombinatorialGames.Surreal.Pow

import CombinatorialGames.Surreal.Coset.Arithmetic
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.Algebra.Ring.Subgroup

/-!
# Rescaling simplest surreal coset representatives

Conway's monomials have a presentation whose options are separated from the value by at least
half its magnitude. The multiplication rule then preserves simplest coset representatives
when a convex subgroup and its representatives are rescaled by the same monomial.
-/

universe u

open IGame Set
open scoped Pointwise

public noncomputable section

namespace Surreal

/-- Any finite natural multiple of a Conway monomial is less than a monomial with larger
exponent. -/
theorem natCast_mul_wpow_lt_wpow (n : ℕ) {x y : Surreal.{u}} (hxy : x < y) :
    (n : Surreal.{u}) * ω^ x < ω^ y := by
  simpa using mul_wpow_lt_wpow (n : ℝ) hxy

private theorem mk_leftMove_wpow_lt_half {a b : IGame.{u}} [a.Numeric]
    (hb : b ∈ (ω^ a)ᴸ) : @mk b (.of_mem_moves hb) < ω^ (mk a) / 2 := by
  let := Numeric.of_mem_moves hb
  rw [moves_left_wpow, mem_insert_iff, mem_image2] at hb
  rcases hb with rfl | ⟨r, _, z, hz, rfl⟩
  · rw [mk_zero]
    exact half_pos (wpow_pos _)
  · let := Numeric.of_mem_moves hz
    rw [mk_mul, mk_dyadic, mk_wpow, div_eq_inv_mul]
    simpa using mul_wpow_lt_mul_wpow_of_pos (r : ℝ) (s := 2⁻¹) (by norm_num)
      (mk_lt_mk.mpr (Numeric.left_lt hz))

private theorem two_mul_wpow_lt_mk_rightMove {a b : IGame.{u}} [a.Numeric]
    (hb : b ∈ (ω^ a)ᴿ) : 2 * ω^ (mk a) < @mk b (.of_mem_moves hb) := by
  let := Numeric.of_mem_moves hb
  rw [moves_right_wpow, mem_image2] at hb
  obtain ⟨r, hr, z, hz, rfl⟩ := hb
  let := Numeric.of_mem_moves hz
  rw [mk_mul, mk_dyadic, mk_wpow]
  simpa using mul_wpow_lt_mul_wpow_of_pos 2 (s := (r : ℝ))
    (by exact_mod_cast (show 0 < r from hr)) (mk_lt_mk.mpr (Numeric.lt_right hz))

/-- The gap to any option in Conway's monomial presentation is at least half the monomial. -/
theorem half_wpow_le_abs_sub_mk_of_mem_moves_wpow {a b : IGame.{u}} [a.Numeric] {p : Player}
    (hb : b ∈ (ω^ a).moves p) : ω^ (mk a) / 2 ≤ |ω^ (mk a) - @mk b (.of_mem_moves hb)| := by
  let := Numeric.of_mem_moves hb
  cases p
  · have h := mk_leftMove_wpow_lt_half hb
    rw [le_abs]
    exact Or.inl (by linarith)
  · have h := two_mul_wpow_lt_mk_rightMove hb
    have hp := wpow_pos (mk a)
    rw [le_abs]
    exact Or.inr (by linarith)

/-- Membership in a nonzero scalar multiple is tested by division by the scalar. -/
theorem mem_smul_addSubgroup_iff_div_mem {H : AddSubgroup Surreal.{u}} {m x : Surreal.{u}}
    (hm : m ≠ 0) : x ∈ m • H ↔ x / m ∈ H := by
  simpa only [smul_eq_mul, div_eq_inv_mul] using
    AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem₀ hm H x

instance isConvex_smul_addSubgroup (H : AddSubgroup Surreal.{u}) [H.IsConvex] (m : Surreal.{u}) :
    ((m • H)).IsConvex where
  ordConnected := by
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · have hdiv : Antitone fun z : Surreal.{u} ↦ z / m := by
        intro x y hxy
        simpa only [div_neg, neg_le_neg_iff] using
          div_le_div_of_nonneg_right hxy (neg_nonneg.mpr hm.le)
      exact ⟨fun x hx y hy z hz ↦ (mem_smul_addSubgroup_iff_div_mem hm.ne).2
        (AddSubgroup.IsConvex.ordConnected.out ((mem_smul_addSubgroup_iff_div_mem hm.ne).1 hy)
          ((mem_smul_addSubgroup_iff_div_mem hm.ne).1 hx)
          ⟨hdiv hz.2, hdiv hz.1⟩)⟩
    · rw [AddSubgroup.zero_smul]
      simpa only [AddSubgroup.coe_bot] using (Set.ordConnected_singleton (a := (0 : Surreal.{u})))
    · exact ⟨fun x hx y hy z hz ↦ (mem_smul_addSubgroup_iff_div_mem hm.ne').2
        (AddSubgroup.IsConvex.ordConnected.out ((mem_smul_addSubgroup_iff_div_mem hm.ne').1 hx)
          ((mem_smul_addSubgroup_iff_div_mem hm.ne').1 hy)
          ⟨div_le_div_of_nonneg_right hz.1 hm.le, div_le_div_of_nonneg_right hz.2 hm.le⟩)⟩

/-- Multiples of a convex additive subgroup are monotone in the positive scalar. -/
theorem smul_addSubgroup_mono (H : AddSubgroup Surreal.{u}) [H.IsConvex]
    {m n : Surreal.{u}} (hm : 0 < m) (hn : m ≤ n) :
    m • H ≤ n • H := by
  have hn' := hm.trans_le hn
  intro x hx
  apply (mem_smul_addSubgroup_iff_div_mem hn'.ne').mpr
  apply abs_mem_iff.mp
  refine H.mem_of_nonneg_of_le (abs_nonneg (x / n)) ?_
    (abs_mem_iff.mpr ((mem_smul_addSubgroup_iff_div_mem hm.ne').mp hx))
  simpa only [abs_div, abs_of_pos hm, abs_of_pos hn'] using
    div_le_div_of_nonneg_left (abs_nonneg x) hm hn

/-- A Conway monomial outside a convex subgroup is its own simplest representative. -/
theorem cosetRep_wpow_eq_of_notMem {H : AddSubgroup Surreal.{u}} [H.IsConvex] {a : Surreal.{u}}
    (ha : ω^ a ∉ H) : cosetRep H (ω^ a) = ω^ a := by
  rw [← a.out_eq, ← mk_wpow]
  apply cosetRep_mk_eq_of_forall_moves
  intro p b hb hgap
  have hhalf := H.mem_of_nonneg_of_le (div_nonneg (wpow_nonneg (mk a.out)) (by norm_num))
    (half_wpow_le_abs_sub_mk_of_mem_moves_wpow hb)
    (abs_mem_iff.mpr (by simpa only [mk_wpow] using hgap))
  apply ha
  simpa only [add_halves, out_eq] using H.add_mem hhalf hhalf

private theorem mul_notMem_smul_addSubgroup {H : AddSubgroup Surreal.{u}} [H.IsConvex]
    {m d e : Surreal.{u}} (hm : 0 < m) (hd : m / 2 ≤ |d|) (he : e ∉ H) :
    d * e ∉ (m • H) := by
  intro h
  have hde : d * e / m ∈ H := (mem_smul_addSubgroup_iff_div_mem hm.ne').1 h
  have habs : |d * e / m| ∈ H := abs_mem_iff.mpr hde
  have hbound : |e| / 2 ≤ |d * e / m| := by
    rw [abs_div, abs_mul, abs_of_pos hm]
    apply (le_div_iff₀ hm).2
    calc
      |e| / 2 * m = m / 2 * |e| := by ring
      _ ≤ |d| * |e| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
  have hhalf := H.mem_of_nonneg_of_le (div_nonneg (abs_nonneg e) (by norm_num)) hbound habs
  apply he
  apply abs_mem_iff.mp
  simpa only [add_halves] using H.add_mem hhalf hhalf

/-- Multiplying a simplest representative by a Conway monomial rescales its convex subgroup. -/
theorem cosetRep_wpow_mul_eq {H : AddSubgroup Surreal.{u}} [H.IsConvex] {a x : Surreal.{u}}
    (hx : cosetRep H x = x) :
    cosetRep (ω^ a • H) (ω^ a * x) = ω^ a * x := by
  obtain ⟨g, _, rfl, hgb⟩ := x.birthday_eq_iGameBirthday
  rw [← a.out_eq, ← mk_wpow]
  apply cosetRep_mk_mul_eq_of_forall_moves
  intro p b hb q c hc
  apply mul_notMem_smul_addSubgroup (wpow_pos (mk a.out))
  · simpa only [mk_wpow] using half_wpow_le_abs_sub_mk_of_mem_moves_wpow hb
  · exact (cosetRep_mk_eq_iff_forall_moves hgb).mp hx q c hc

/-- Rescaling a convex subgroup by a Conway monomial commutes with choosing its simplest
coset representative. -/
theorem cosetRep_wpow_smul (H : AddSubgroup Surreal.{u}) [H.IsConvex] (a x : Surreal.{u}) :
    cosetRep (ω^ a • H) x = ω^ a * cosetRep H (x / ω^ a) := by
  refine (cosetRep_eq_of_sub_mem (H := (ω^ a • H)) ?_).trans
    (cosetRep_wpow_mul_eq (cosetRep_cosetRep H (x / ω^ a)))
  apply (mem_smul_addSubgroup_iff_div_mem (wpow_ne_zero a)).2
  simpa only [sub_div, mul_comm (ω^ a), mul_div_cancel_right₀ _ (wpow_ne_zero a)] using
    sub_cosetRep_mem H (x / ω^ a)

/-- The exponents of Conway monomials that are units of the subring. -/
def unitExponentSubgroup (C : Subring Surreal.{u}) : AddSubgroup Surreal.{u} where
  carrier := {a | ω^ a ∈ C ∧ (ω^ a)⁻¹ ∈ C}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, hai⟩ ⟨hb, hbi⟩
    simp only [Set.mem_ofPred_eq, wpow_add, mul_inv_rev]
    exact ⟨C.mul_mem ha hb, C.mul_mem hbi hai⟩
  neg_mem' := by
    rintro a ⟨ha, hai⟩
    simpa only [Set.mem_ofPred_eq, wpow_neg, inv_inv] using And.intro hai ha

theorem mem_unitExponentSubgroup_iff (C : Subring Surreal.{u}) {a : Surreal.{u}} :
    a ∈ unitExponentSubgroup C ↔ ω^ a ∈ C ∧ (ω^ a)⁻¹ ∈ C :=
  Iff.rfl

instance unitExponentSubgroup_isConvex (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex] :
    (unitExponentSubgroup C).IsConvex where
  ordConnected := by
    constructor
    intro a ha b hb z hz
    obtain ⟨_, hai⟩ := (mem_unitExponentSubgroup_iff C).mp ha
    obtain ⟨hb, _⟩ := (mem_unitExponentSubgroup_iff C).mp hb
    apply (mem_unitExponentSubgroup_iff C).mpr
    refine ⟨C.toAddSubgroup.mem_of_nonneg_of_le (wpow_nonneg z) (wpow_le_wpow.mpr hz.2) hb, ?_⟩
    rw [← wpow_neg] at hai ⊢
    exact C.toAddSubgroup.mem_of_nonneg_of_le (wpow_nonneg _)
      (wpow_le_wpow.mpr (neg_le_neg hz.1)) hai

variable (C : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex]

/-- The simplest exponent in the coset of a number's monomial exponent modulo the unit
exponents of the convex subring. -/
def precisionLevel (x : Surreal.{u}) : Surreal.{u} :=
  cosetRep (unitExponentSubgroup C) x.wlog

theorem precisionLevel_eq (x : Surreal.{u}) :
    precisionLevel C x = cosetRep (unitExponentSubgroup C) x.wlog :=
  (rfl)

@[simp]
theorem precisionLevel_wpow (a : Surreal.{u}) :
    precisionLevel C (ω^ a) = cosetRep (unitExponentSubgroup C) a := by
  rw [precisionLevel, wlog_wpow]

@[simp]
theorem cosetRep_precisionLevel (x : Surreal.{u}) :
    cosetRep (unitExponentSubgroup C) (precisionLevel C x) = precisionLevel C x :=
  cosetRep_cosetRep _ _

theorem precisionLevel_mul {x y : Surreal.{u}} (hx : x ≠ 0) (hy : y ≠ 0) :
    precisionLevel C (x * y) = precisionLevel C x + precisionLevel C y := by
  simp only [precisionLevel, wlog_mul hx hy, cosetRep_add]

@[simp]
theorem precisionLevel_inv (x : Surreal.{u}) :
    precisionLevel C x⁻¹ = -precisionLevel C x := by
  simp only [precisionLevel, wlog_inv, cosetRep_neg]

theorem precisionLevel_div {x y : Surreal.{u}} (hx : x ≠ 0) (hy : y ≠ 0) :
    precisionLevel C (x / y) = precisionLevel C x - precisionLevel C y := by
  rw [div_eq_mul_inv, precisionLevel_mul C hx (inv_ne_zero hy), precisionLevel_inv, sub_eq_add_neg]

private theorem wpow_mem_of_nonpos {a : Surreal.{u}} (h : a ≤ 0) : ω^ a ∈ C :=
  C.toAddSubgroup.mem_of_nonneg_of_le (wpow_nonneg _)
    (by simpa only [wpow_zero] using wpow_le_wpow.mpr h) C.one_mem

theorem wpow_notMem_subring_iff {a : Surreal.{u}} :
    ω^ a ∉ C ↔ 0 < cosetRep (unitExponentSubgroup C) a := by
  let H := unitExponentSubgroup C
  have hmono := monotone_cosetRep H
  constructor
  · intro h
    have ha : 0 < a := lt_of_not_ge (fun hle ↦ h (wpow_mem_of_nonpos C hle))
    have hle : 0 ≤ cosetRep H a := by simpa only [cosetRep_zero] using hmono ha.le
    apply hle.lt_of_ne
    intro heq
    exact h ((mem_unitExponentSubgroup_iff C).1 (cosetRep_eq_zero_iff.mp heq.symm)).1
  · intro h hmem
    have ha : 0 < a := by
      refine lt_of_not_ge fun hle ↦ h.not_ge ?_
      simpa only [cosetRep_zero] using hmono hle
    refine (ne_of_gt h) (cosetRep_eq_zero_iff.mpr ((mem_unitExponentSubgroup_iff C).2 ⟨hmem, ?_⟩))
    rw [← wpow_neg]
    exact wpow_mem_of_nonpos C (neg_nonpos.mpr ha.le)

theorem mem_subring_of_vle {x y : Surreal.{u}} (hy : y ∈ C) (hxy : x ≤ᵥ y) : x ∈ C := by
  obtain ⟨n, hn⟩ := vle_def.mp hxy
  apply abs_mem_iff.mp
  exact C.toAddSubgroup.mem_of_nonneg_of_le (abs_nonneg x) hn
    (C.toAddSubgroup.nsmul_mem (abs_mem_iff.mpr hy) n)

theorem mem_subring_iff_of_veq {x y : Surreal.{u}} (hxy : x =ᵥ y) : x ∈ C ↔ y ∈ C := by
  rw [veq_def] at hxy
  exact ⟨fun h ↦ mem_subring_of_vle C h (vle_def.mpr hxy.le),
    fun h ↦ mem_subring_of_vle C h (vle_def.mpr hxy.ge)⟩

theorem notMem_subring_iff_precisionLevel_pos {x : Surreal.{u}} (hx : x ≠ 0) :
    x ∉ C ↔ 0 < precisionLevel C x := by
  rw [← mem_subring_iff_of_veq C (wpow_wlog_veq hx)]
  exact wpow_notMem_subring_iff C

theorem div_wpow_mem_infinitesimals_iff {x t : Surreal.{u}} (hx : x ≠ 0)
    (ht : cosetRep (unitExponentSubgroup C) t = t) :
    x / ω^ t ∈ infinitesimals C ↔ precisionLevel C x < t := by
  have hdiv : x / ω^ t ≠ 0 := div_ne_zero hx (wpow_ne_zero t)
  rw [mem_infinitesimals_iff C, or_iff_right hdiv,
    notMem_subring_iff_precisionLevel_pos C (inv_ne_zero hdiv), precisionLevel_inv,
    precisionLevel_div C hx (wpow_ne_zero t), precisionLevel_wpow, ht, neg_sub, sub_pos]

theorem mem_wpow_smul_infinitesimals_iff {x t : Surreal.{u}} (hx : x ≠ 0)
    (ht : cosetRep (unitExponentSubgroup C) t = t) :
    x ∈ ω^ t • infinitesimals C ↔ precisionLevel C x < t :=
  (mem_smul_addSubgroup_iff_div_mem (wpow_ne_zero t)).trans
    (div_wpow_mem_infinitesimals_iff C hx ht)

theorem div_wpow_mem_subring_and_inv_iff {x t : Surreal.{u}} (hx : x ≠ 0)
    (ht : cosetRep (unitExponentSubgroup C) t = t) :
    x / ω^ t ∈ C ∧ (x / ω^ t)⁻¹ ∈ C ↔ precisionLevel C x = t := by
  have hdiv : x / ω^ t ≠ 0 := div_ne_zero hx (wpow_ne_zero t)
  have hpos := notMem_subring_iff_precisionLevel_pos C hdiv
  have hinv := notMem_subring_iff_precisionLevel_pos C (inv_ne_zero hdiv)
  rw [precisionLevel_div C hx (wpow_ne_zero t), precisionLevel_wpow, ht, sub_pos] at hpos
  rw [precisionLevel_inv, precisionLevel_div C hx (wpow_ne_zero t), precisionLevel_wpow,
    ht, neg_sub, sub_pos] at hinv
  rw [← not_not (a := x / ω^ t ∈ C), ← not_not (a := (x / ω^ t)⁻¹ ∈ C),
    hpos, hinv, not_lt, not_lt, le_antisymm_iff]

theorem precisionLevel_nonneg_of_mem_residueRepresentatives {x : Surreal.{u}}
    (hU : x ∈ residueRepresentatives C) (hx : x ≠ 0) : 0 ≤ precisionLevel C x := by
  by_contra! h
  have hB : x ∈ infinitesimals C := by
    simpa only [wpow_zero, div_one] using
      (div_wpow_mem_infinitesimals_iff C hx (cosetRep_zero _)).mpr h
  exact hx (((mem_residueRepresentatives_iff C).mp hU).symm.trans
    ((cosetRep_eq_zero_iff (H := infinitesimals C)).mpr hB))

theorem wpow_mul_mem_residueRepresentatives {a x : Surreal.{u}} (ha : 0 ≤ a)
    (hx : x ∈ residueRepresentatives C) : ω^ a * x ∈ residueRepresentatives C := by
  have hle : infinitesimals C ≤ (ω^ a • infinitesimals C) := by
    simpa only [one_smul] using smul_addSubgroup_mono (infinitesimals C)
      zero_lt_one (show 1 ≤ ω^ a by simpa only [wpow_zero] using wpow_le_wpow.mpr ha)
  have hfixed := cosetRep_wpow_mul_eq ((mem_residueRepresentatives_iff C).mp hx) (a := a)
  apply (mem_residueRepresentatives_iff C).mpr
  simpa only [hfixed] using cosetRep_cosetRep_of_ge hle (ω^ a * x)

end Surreal
