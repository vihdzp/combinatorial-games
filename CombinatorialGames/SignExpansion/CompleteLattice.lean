/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.SignExpansion.Basic


/-!
# Sign Expansions

We prove that sign expansions form a complete lattice.
-/

universe u

namespace SignExpansion
open Order Set

private def sets (s : Set SignExpansion.{u}) (o : Ordinal.{u}) : Set SignExpansion.{u} :=
  Ordinal.limitRecOn o
    s -- zero
    (fun o ih => {x ∈ ih | x o.toNatOrdinal = ⨆ i ∈ ih, i o.toNatOrdinal}) -- succ
    (fun _ _ ih => ⋂ (i) (hi), ih i hi) -- limit

private theorem sets_zero (s : Set SignExpansion.{u}) : sets s 0 = s :=
  Ordinal.limitRecOn_zero ..

private theorem sets_succ (s : Set SignExpansion.{u}) (o : Ordinal.{u}) :
    sets s (succ o) = {x ∈ sets s o | x o.toNatOrdinal = ⨆ i ∈ sets s o, i o.toNatOrdinal} :=
  Ordinal.limitRecOn_succ ..

private theorem sets_limit (s : Set SignExpansion.{u}) {o : Ordinal.{u}}
    (ho : IsSuccLimit o) : sets s o = ⋂ (i : Ordinal.{u}) (_ : i < o), sets s i :=
  Ordinal.limitRecOn_limit _ _ _ _ ho

private theorem sets_anti_right (s : Set SignExpansion.{u}) {o o' : Ordinal.{u}}
    (hoo' : o ≤ o') : sets s o' ⊆ sets s o := by
  apply exists_add_of_le at hoo'
  obtain ⟨o', rfl⟩ := hoo'
  induction o' using Ordinal.limitRecOn with
  | zero => simp
  | succ o' ih =>
    apply ih.trans'
    rw [Ordinal.add_succ, sets_succ]
    simp
  | isLimit o' limit ih =>
    have limit' := limit
    apply Ordinal.isLimit_add o at limit'
    rw [sets_limit s limit']
    apply Set.iInter₂_subset
    simpa [← Ordinal.bot_eq_zero, bot_lt_iff_ne_bot] using limit.ne_bot

private theorem sets_singleton_inc (s : Set SignExpansion.{u}) (o o' : Ordinal.{u})
    (x : SignExpansion) (hoo' : o ≤ o') (h : sets s o = {x}) : sets s o' = {x} := by
  apply exists_add_of_le at hoo'
  obtain ⟨o', rfl⟩ := hoo'
  induction o' using Ordinal.limitRecOn with
  | zero => simpa using h
  | succ o' ih =>
    rw [Ordinal.add_succ]
    apply subset_antisymm
    · rw [← ih]
      apply sets_anti_right
      apply le_succ
    · rw [sets_succ, Set.singleton_subset_iff]
      simp [ih]
  | isLimit o' limit ih =>
    have limit' := limit
    apply Ordinal.isLimit_add o at limit'
    rw [sets_limit s limit']
    apply subset_antisymm
    · exact iInter₂_subset_of_subset (o + 0) (add_lt_add_left limit.pos o) (ih 0 limit.pos).subset
    · rw [Set.subset_iInter₂_iff]
      intro i hi
      obtain hoi | hio := le_total o i
      · apply exists_add_of_le at hoi
        obtain ⟨c, rfl⟩ := hoi
        rw [add_lt_add_iff_left] at hi
        exact (ih c hi).superset
      · apply (sets_anti_right s hio).trans'
        rw [← add_zero o]
        exact (ih 0 limit.pos).superset

private theorem sets_congr_of_lt (s : Set SignExpansion.{u}) (o o' : Ordinal.{u})
    (ho' : o' < o) (e : SignExpansion.{u}) (he : e ∈ sets s o) :
    e o'.toNatOrdinal = ⨆ i ∈ sets s o', i o'.toNatOrdinal := by
  induction o using Ordinal.limitRecOn generalizing o' e with
  | zero => simp [← not_le] at ho'
  | succ o ih =>
    rw [lt_succ_iff_eq_or_lt, or_comm] at ho'
    obtain h | rfl := ho'
    · exact ih o' h e (sets_anti_right s (le_succ o) he)
    rw [sets_succ] at he
    exact he.right
  | isLimit o limit ih =>
    rw [← Ordinal.succ_lt_of_isLimit limit] at ho'
    exact ih (succ o') ho' o' (lt_succ o') e (sets_anti_right s ho'.le he)

private theorem congr_sets_of_lt (s : Set SignExpansion.{u}) (o : Ordinal.{u})
    (e : SignExpansion.{u}) (he : e ∈ s)
    (ho' : ∀ o' < o, e o'.toNatOrdinal = ⨆ i ∈ sets s o', i o'.toNatOrdinal) : e ∈ sets s o := by
  induction o using Ordinal.limitRecOn generalizing e with
  | zero => rwa [sets_zero]
  | succ o ih =>
    rw [sets_succ]
    constructor
    · apply ih e he
      intro o' hoo'
      exact ho' o' (hoo'.trans_le (le_succ o))
    · exact ho' o (lt_succ o)
  | isLimit o limit ih =>
    rw [sets_limit s limit, Set.mem_iInter₂]
    intro o' hoo'
    apply ih o' hoo' e he
    intro o'' hoo''
    exact ho' o'' (hoo''.trans hoo')

private theorem sets_singleton_succ_of_zero (s : Set SignExpansion.{u}) (o : Ordinal.{u})
    (h : ⨆ i ∈ sets s o, i o.toNatOrdinal = 0) : ∃ k, sets s (succ o) = {k} := by
  have lubo : IsLUB ((· o.toNatOrdinal) '' sets s o) (⨆ i ∈ sets s o, i o.toNatOrdinal) :=
    isLUB_biSup
  have np0 : ¬IsSuccPrelimit (succ (-1) : SignType) :=
    not_isSuccPrelimit_succ_of_not_isMax (by simp)
  rw [SignType.succ_neg_one] at np0
  rw [h] at lubo
  have hm0 := lubo.mem_of_not_isSuccPrelimit np0
  rw [Set.mem_image] at hm0
  obtain ⟨x, hx, hxo⟩ := hm0
  refine ⟨x, subset_antisymm ?_ ?_⟩
  · intro y hy
    rw [Set.mem_singleton_iff]
    rw [sets_succ] at hy
    ext c
    obtain hc | hc := lt_or_ge c.toOrdinal o
    · rw [← c.toOrdinal_toNatOrdinal, sets_congr_of_lt s o c.toOrdinal hc x hx,
        sets_congr_of_lt s o c.toOrdinal hc y hy.left]
    · rw [← Ordinal.toNatOrdinal.map_rel_iff, NatOrdinal.toOrdinal_toNatOrdinal] at hc
      rw [x.apply_eq_zero_of_le hc hxo, y.apply_eq_zero_of_le hc (hy.right.trans h)]
  · rw [singleton_subset_iff, sets_succ]
    refine ⟨hx, ?_⟩
    rwa [h]

private noncomputable def sSup'' (s : Set SignExpansion.{u}) (o : Ordinal.{u}) : SignType :=
  ⨆ i ∈ sets s o, i o.toNatOrdinal

private theorem sSup''_valid (s : Set SignExpansion.{u}) : IsUpperSet (sSup'' s ⁻¹' {0}) := by
  intro a b hab ha
  rw [Set.mem_preimage, Set.mem_singleton_iff, sSup''] at ha ⊢
  rw [le_iff_eq_or_succ_le] at hab
  obtain rfl | hab := hab
  · exact ha
  · have hk := sets_singleton_succ_of_zero s a ha
    obtain ⟨k, hk⟩ := hk
    have hb := sets_singleton_inc s (succ a) b k hab hk
    have hh := hk.superset
    rw [hb]
    rw [singleton_subset_iff, sets_succ, ha] at hh
    simp only [mem_singleton_iff, iSup_iSup_eq_left]
    exact k.apply_eq_zero_of_le ((le_succ a).trans hab) hh.right

private noncomputable def sSup' (s : Set SignExpansion.{u}) : SignExpansion.{u} where
  sign i := sSup'' s i.toOrdinal
  isUpperSet_sign_preimage_singleton_zero := by
    intro a b hab hb
    cases a with | toNatOrdinal a =>
    cases b with | toNatOrdinal b =>
    rw [mem_preimage, Ordinal.toNatOrdinal_toOrdinal, mem_singleton_iff] at hb ⊢
    exact sSup''_valid s (Ordinal.toNatOrdinal.map_rel_iff.mp hab) hb

noncomputable instance completeSemilatticeSup : CompleteSemilatticeSup SignExpansion.{u} where
  sSup := sSup'
  le_sSup := by
    intro s a has
    rw [le_iff_toLex, ← not_lt]
    intro ⟨k, hkl, hk⟩
    simp_rw [Pi.toLex_apply, sSup', sSup'', NatOrdinal.toOrdinal_toNatOrdinal, coe_mk] at hk hkl
    revert hk
    rw [imp_false, not_lt]
    apply le_biSup fun i : SignExpansion => i k
    apply congr_sets_of_lt s k.toOrdinal a has
    intro o' ho'
    rw [← Ordinal.toNatOrdinal.lt_iff_lt, NatOrdinal.toOrdinal_toNatOrdinal] at ho'
    rw [← hkl o'.toNatOrdinal ho', o'.toNatOrdinal_toOrdinal]
  sSup_le := by
    intro s a
    simp_rw [le_iff_toLex, ← not_lt, ← not_exists]
    rw [not_exists, not_imp_not]
    intro ⟨d, hll, hd⟩
    simp_rw [Pi.toLex_apply, sSup', coe_mk, sSup''] at hd hll
    rw [lt_biSup_iff] at hd
    obtain ⟨k, hk, hik⟩ := hd
    refine ⟨k, ?_, d, ?_, ?_⟩
    · rw [← sets_zero s]
      exact sets_anti_right s d.toOrdinal.zero_le hk
    · intro j hj
      rw [Pi.toLex_apply, Pi.toLex_apply, hll j hj, ← j.toOrdinal_toNatOrdinal]
      rw [sets_congr_of_lt s d.toOrdinal j.toOrdinal (NatOrdinal.toOrdinal.lt_iff_lt.mpr hj) k hk]
      rw [j.toOrdinal_toNatOrdinal, j.toOrdinal_toNatOrdinal]
    · simpa using hik

noncomputable instance completeLinearOrder : CompleteLinearOrder SignExpansion.{u} where
  __ := linearOrder
  __ := biheytingAlgebra
  __ := completeLatticeOfCompleteSemilatticeSup SignExpansion

end SignExpansion
