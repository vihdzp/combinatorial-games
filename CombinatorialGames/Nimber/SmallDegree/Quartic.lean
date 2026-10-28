/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import CombinatorialGames.Nimber.SimplestExtension.Algebraic
public import Mathlib.FieldTheory.Galois.Basic

import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic.Simproc.Factors

/-!
# Quartic nimber extensions

We prove that the extension between two adjacent nimber fields cannot be of degree 4.
-/

public section

theorem IntermediateField.finrank_fixedField_eq_index
    {F E : Type*} [Field F] [Field E] [Algebra F E] (H : Subgroup Gal(E/F))
    [FiniteDimensional F E] [IsGalois F E] : Module.finrank F (fixedField H) = H.index := by
  -- todo: adjust explicitness?
  apply Nat.eq_of_mul_eq_mul_right (@Module.finrank_pos (fixedField H) E _ _ _ _ _ _ _ _)
  rw [Module.finrank_mul_finrank, IntermediateField.finrank_fixedField_eq_card, H.index_mul_card]
  exact (IsGalois.card_aut_eq_finrank F E).symm

@[to_additive]
theorem IsSimpleGroup.isMulCommutative_iff_isSolvable {G : Type*} [Group G] [IsSimpleGroup G] :
    IsMulCommutative G ↔ Group.IsSolvable G := by
  rw [← IsSimpleGroup.comm_iff_isSolvable]
  exact ⟨fun h => mul_comm', fun h => ⟨⟨h⟩⟩⟩

theorem Polynomial.exists_irreducible_quadratic_or_cubic_of_irreducible_quartic
    {k : Type*} [Field k] (p : Polynomial k) (hp : Irreducible p) (hpd : p.degree = 4) :
    ∃ q : Polynomial k, Irreducible q ∧ (q.degree = 2 ∨ q.degree = 3) := by
  rw [← Nat.cast_ofNat, Polynomial.degree_eq_iff_natDegree_eq_of_pos (by decide)] at hpd
  by_cases! hps : ¬p.Separable
  · have perf : ¬PerfectField k := fun perf =>
      hps (perf.separable_of_irreducible hp)
    obtain ⟨q, charq⟩ := CharP.exists k
    have hq0 : q ≠ 0 := by
      intro rfl
      rw [CharP.charP_zero_iff_charZero] at charq
      exact perf inferInstance
    obtain ⟨n, p, hsep, rfl⟩ := Polynomial.exists_separable_of_irreducible q hp hq0
    rw [natDegree_expand] at hpd
    have hn0 : n ≠ 0 := by
      intro rfl
      apply hps
      simpa using hsep
    have hq : q ∣ 4 := by
      refine ⟨p.natDegree * q ^ (n - 1), ?_⟩
      rw [← hpd, mul_rotate', ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn0)]
    have hqp : q.Prime := charq.char_prime_of_ne_zero k hq0
    rw [← two_add_two_eq_four, ← mul_two, ← pow_two] at hq
    obtain rfl := (Nat.prime_two.dvd_iff_eq hqp.ne_one).1 (hqp.dvd_of_dvd_pow hq)
    obtain ⟨b, hb⟩ : ∃ b : k, ∀ a, a ^ 2 ≠ b := by
      by_contra! surj
      have pr : PerfectRing k 2 := .ofSurjective k 2 surj
      exact perf pr.toPerfectField
    exact ⟨X ^ 2 - C b, X_pow_sub_C_irreducible_of_prime Nat.prime_two hb,
      .inl (by compute_degree!)⟩
  · have splits := IsSplittingField.splits p.SplittingField p
    have := Fact.mk splits
    have solv : Group.IsSolvable Gal(p.SplittingField/k) := by
      suffices _ : Group.IsSolvable (Equiv.Perm ↑(p.rootSet p.SplittingField)) from
        Group.isSolvable_of_isSolvable_injective
          -- is `Polynomial.Gal.galActionHom` even a good idea to have? it's noncanonical
          (Polynomial.Gal.galActionHom_injective p p.SplittingField)
      apply Equiv.Perm.isSolvable
      grw [Nat.card_coe_set_eq, ncard_rootSet_le, hpd]
    have dvd : Nat.card Gal(p.SplittingField/k) ∣ 24 := by
      suffices hc : Nat.card (Equiv.Perm ↑(p.rootSet p.SplittingField)) ∣ 24 from
        (Subgroup.card_dvd_of_injective _
          -- is `Polynomial.Gal.galActionHom` even a good idea to have? it's noncanonical
          (Polynomial.Gal.galActionHom_injective p p.SplittingField)).trans hc
      grw [Nat.card_perm, Nat.card_coe_set_eq, ncard_rootSet_le, hpd]
      rfl
    have gal : IsGalois k p.SplittingField := .of_separable_splitting_field hps
    have nt : Nontrivial Gal(p.SplittingField/k) := by
      rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
      refine lt_of_lt_of_le ?_ (Nat.le_of_dvd ?_
        (Polynomial.Irreducible.natDegree_dvd_finrank hp splits))
      · simp [hpd]
      · apply Module.finrank_pos
    obtain ⟨N, ⟨hN, hNt⟩, hM⟩ :=
      (Set.toFinite { N : Subgroup Gal(p.SplittingField/k) | N.Normal ∧ N ≠ ⊤ }).exists_maximal
        ⟨⊥, Subgroup.normal_bot, bot_ne_top⟩
    simp_rw [Set.mem_ofPred, and_imp] at hM
    have simpl : IsSimpleGroup (Gal(p.SplittingField/k) ⧸ N) := by
      rw [isSimpleGroup_iff]
      constructor
      · rwa [QuotientGroup.nontrivial_iff]
      · intro H hH
        rw [or_iff_not_imp_right, ← le_bot_iff]
        intro hHt
        rw [← Subgroup.comap_le_comap_of_surjective (QuotientGroup.mk'_surjective N),
          /- this was impossible to find, todo: rename -/ MonoidHom.comap_bot,
          QuotientGroup.ker_mk']
        apply hM inferInstance
        · rwa [← Subgroup.comap_top (QuotientGroup.mk' N),
            (Subgroup.comap_injective (QuotientGroup.mk'_surjective N)).ne_iff]
        · grw [← Subgroup.ker_le_comap, QuotientGroup.ker_mk']
    have comm : IsMulCommutative (Gal(p.SplittingField/k) ⧸ N) :=
      IsSimpleGroup.isMulCommutative_iff_isSolvable.2 inferInstance
    rw [/- todo: rename -/ Group.is_simple_iff_prime_card] at simpl
    have hdvd := N.card_quotient_dvd_card.trans dvd
    set e := Nat.card (Gal(p.SplittingField/k) ⧸ N) with ← he
    have heq : e = 2 ∨ e = 3 := by
      have factors := simpl.mem_primeFactors' hdvd
      simp_rw [/- todo: rename -/ ← Nat.toFinset_factors, Nat.primeFactorsList_ofNat] at factors
      simpa using factors
    obtain ⟨a, ha⟩ := Field.exists_primitive_element k (IntermediateField.fixedField N)
    have hr := congr(Module.finrank k $ha)
    rw [IntermediateField.finrank_top', IntermediateField.finrank_fixedField_eq_index,
      Subgroup.index_eq_card, he,
      IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _)] at hr
    refine ⟨minpoly k a, minpoly.irreducible (Algebra.IsIntegral.isIntegral _), ?_⟩
    rcases heq with he | he
    · left
      rw [← Nat.cast_ofNat, Polynomial.degree_eq_iff_natDegree_eq_of_pos (by decide), hr, he]
    · right
      rw [← Nat.cast_ofNat, Polynomial.degree_eq_iff_natDegree_eq_of_pos (by decide), hr, he]

namespace Nimber
open Polynomial

theorem IsField.degree_leastNoRoots_ne_four
    {x : Nimber} (hx : IsField x) (ht : leastNoRoots x ≠ ⊤) :
    ((leastNoRoots x).untop ht).degree ≠ 4 := by
  intro h
  obtain ⟨p, hp, hpd⟩ :=
    Polynomial.exists_irreducible_quadratic_or_cubic_of_irreducible_quartic
      _ (hx.irreducible_embed_leastNoRoots ht) (by simpa using h)
  have hpl : p.map hx.toSubfield.subtype < leastNoRoots x := by
    rw [← WithTop.lt_untop_iff ht]
    apply Lex.lt_of_degree_lt
    rw [Polynomial.degree_map, h]
    rcases hpd with hd | hd <;>
      · rw [hd]
        decide
  obtain ⟨r, hrx, hrr⟩ := exists_root_of_lt_leastNoRoots
    (by rcases hpd with hd | hd <;> simp [hd]) (by simp) hpl
  change Polynomial.IsRoot _ (hx.toSubfield.subtype ⟨r, hrx⟩) at hrr
  rw [Polynomial.isRoot_map_iff hx.toSubfield.subtype_injective] at hrr
  refine hp.not_isRoot_of_natDegree_ne_one ?_ hrr
  rw [ne_eq, ← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by decide)]
  rcases hpd with hd | hd <;> simp [hd]

theorem IsField.natDegree_leastNoRoots_ne_four
    {x : Nimber} (hx : IsField x) (ht : leastNoRoots x ≠ ⊤) :
    ((leastNoRoots x).untop ht).natDegree ≠ 4 := by
  rw [ne_eq, ← degree_eq_iff_natDegree_eq (leastNoRoots_ne_zero' ht)]
  exact hx.degree_leastNoRoots_ne_four ht

theorem IsField.X_pow_five_lt_leastNoRoots_of_X_pow_four_le_leastNoRoots
    {x : Nimber} (hx : IsField x) (hl : .some (X ^ 4) ≤ leastNoRoots x) :
    .some (X ^ 5) < leastNoRoots x := by
  apply lt_of_ne_of_le' (leastNoRoots_ne_X_pow x 5)
  by_cases ht : leastNoRoots x = ⊤
  · simp [ht]
  rw [← WithTop.coe_untop _ ht, WithTop.coe_le_coe, Lex.X_pow_le_iff] at hl ⊢
  rw [Nat.cast_ofNat, ← show Order.succ (4 : WithBot ℕ) = 5 from rfl, Order.succ_le_iff]
  exact hl.lt_of_ne' (hx.degree_leastNoRoots_ne_four ht)

theorem IsField.leastNoRoots_lt_X_pow_four_of_leastNoRoots_le_X_pow_five
    {x : Nimber} (hx : IsField x) (hl : leastNoRoots x ≤ .some (X ^ 5)) :
    leastNoRoots x < .some (X ^ 4) := by
  contrapose! hl
  exact hx.X_pow_five_lt_leastNoRoots_of_X_pow_four_le_leastNoRoots hl

theorem IsField.sq_of_pow_four {x : Nimber} (hx : IsField x) (hx4 : IsField (of (val x ^ 4))) :
    IsField (of (val x ^ 2)) := by
  obtain ⟨ht, hd₄⟩ := degree_leastNoRoots_le_of_isField_pow (by decide) hx hx4
  replace hd₄ := (natDegree_le_of_degree_le hd₄).lt_of_ne (hx.natDegree_leastNoRoots_ne_four ht)
  have hd₁ := hx.one_lt_natDegree_leastNoRoots ht
  have hf := hx.pow_natDegree_leastNoRoots ht
  interval_cases (x.leastNoRoots.untop ht).natDegree
  · exact hf
  absurd sq_le_fieldClosure_succ hf
  rw [not_le, val_of, ← pow_mul]
  apply lt_of_le_of_lt (b := of (val x ^ 4))
  · rw [hx4.fieldClosure_le_iff, Order.succ_le_iff]
    exact of.strictMono (pow_lt_pow_right₀ hx.one_lt_val hd₄)
  · exact of.strictMono (pow_lt_pow_right₀ hx.one_lt_val (by decide))

end Nimber
