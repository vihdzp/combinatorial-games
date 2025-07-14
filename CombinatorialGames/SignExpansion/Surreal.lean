/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.SignExpansion.Basic
import CombinatorialGames.Surreal.Birthday

/-!
# Sign Expansions

Every surreal number has a sign expansion, a function from its birthday to the set `{-1, 1}`.
This sign expansion uniquely identifies the number.
-/

universe u

noncomputable section

namespace Surreal
open IGame SignExpansion

private def signApproxIGame (o : NatOrdinal.{u}) (x : Surreal.{u}) : IGame.{u} :=
  {{s : IGame.{u} | s.birthday < o} ∩ {s | ∃ _ : s.Numeric, .mk s < x} |
    {s : IGame.{u} | s.birthday < o} ∩ {s | ∃ _ : s.Numeric, x < .mk s}}ᴵ

private instance signApproxIGameNumeric (o : NatOrdinal.{u}) (x : Surreal.{u}) :
    Numeric (x.signApproxIGame o) := by
  rw [numeric_def, signApproxIGame]
  refine ⟨?_, ?_, ?_⟩
  · intro y hy z hz
    rw [leftMoves_ofSets] at hy
    rw [rightMoves_ofSets] at hz
    have := hy.2.1
    have := hz.2.1
    exact mk_lt_mk.mp (hy.2.2.trans hz.2.2)
  · intro y hy
    rw [leftMoves_ofSets] at hy
    exact hy.2.1
  · intro y hy
    rw [rightMoves_ofSets] at hy
    exact hy.2.1

def signApprox (o : NatOrdinal.{u}) (x : Surreal.{u}) : Surreal.{u} :=
  mk (x.signApproxIGame o)

theorem birthday_signApprox_le (o : NatOrdinal.{u}) (x : Surreal.{u}) :
    (signApprox o x).birthday ≤ o := by
  rw [signApprox]
  apply (birthday_mk_le _).trans
  rw [signApproxIGame, birthday_le_iff, leftMoves_ofSets, rightMoves_ofSets]
  constructor
  · intro y hy
    exact hy.left
  · intro y hy
    exact hy.left

theorem signApprox_of_birthday_le {o : NatOrdinal.{u}} {x : Surreal.{u}}
    (h : x.birthday ≤ o) : x.signApprox o = x := by
  obtain ⟨k, nk, rfl, hk⟩ := x.birthday_eq_iGameBirthday
  rw [← hk] at h
  rw [signApprox, Surreal.mk_eq_mk]
  symm
  apply Fits.equiv_of_forall_birthday_le
  · constructor
    · intro z hz
      rw [signApproxIGame, leftMoves_ofSets] at hz
      obtain ⟨hz, nz, hzk⟩ := hz
      rwa [← not_le, mk_le_mk] at hzk
    · intro z hz
      rw [signApproxIGame, rightMoves_ofSets] at hz
      obtain ⟨hz, nz, hkz⟩ := hz
      rwa [← not_le, mk_le_mk] at hkz
  · intro z nz hz
    apply le_of_not_gt
    intro hbb
    have hne : mk z ≠ mk k := by
      intro eq
      rw [hk, ← eq] at hbb
      exact not_le_of_gt hbb (birthday_mk_le z)
    obtain hzk | hkz := lt_or_gt_of_ne hne
    · refine hz.left z ?_ le_rfl
      rw [signApproxIGame, leftMoves_ofSets]
      exact ⟨hbb.trans_le h, nz, hzk⟩
    · refine hz.right z ?_ le_rfl
      rw [signApproxIGame, rightMoves_ofSets]
      exact ⟨hbb.trans_le h, nz, hkz⟩

@[simp]
theorem signApprox_eq_iff {x : Surreal.{u}} {o : NatOrdinal.{u}} :
    x.signApprox o = x ↔ x.birthday ≤ o := by
  refine ⟨fun h => ?_, signApprox_of_birthday_le⟩
  refine le_of_not_gt fun ho => ?_
  refine ne_of_lt ?_ (congrArg birthday h)
  exact (x.birthday_signApprox_le o).trans_lt ho

theorem monotone_signApprox {o : NatOrdinal.{u}} : Monotone (signApprox o) := by
  intro x y hxy
  simp_rw [signApprox, Surreal.mk_le_mk, signApproxIGame]
  rw [le_iff_forall_lf]
  refine ⟨fun z hz => lf_of_le_leftMove le_rfl ?_, fun z hz => lf_of_rightMove_le le_rfl ?_⟩
  · rw [leftMoves_ofSets] at hz ⊢
    exact ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 hxy⟩
  · rw [rightMoves_ofSets] at hz ⊢
    exact ⟨hz.1, hz.2.1, lt_of_le_of_lt hxy hz.2.2⟩

def ofSurreal (x : Surreal.{u}) : SignExpansion where
  sign i := .sign (x - x.signApprox i)
  isUpperSet_sign_preimage_singleton_zero := by
    intro a b hab ha
    rw [Set.mem_preimage, Set.mem_singleton_iff,
      sign_eq_zero_iff, sub_eq_zero, eq_comm, signApprox_eq_iff] at ha ⊢
    exact ha.trans hab

@[simp]
theorem size_ofSurreal (x : Surreal.{u}) :
    (ofSurreal x).size = x.birthday := by
  apply eq_of_forall_ge_iff
  intro c
  cases c with
  | top => simp
  | coe c =>
    rw [← apply_eq_zero, WithTop.coe_le_coe, ofSurreal, coe_mk,
      sign_eq_zero_iff, sub_eq_zero, eq_comm, signApprox_eq_iff]

theorem ofSurreal_apply (x : Surreal.{u}) (o : NatOrdinal.{u}) :
    ofSurreal x o = .sign (x - x.signApprox o) := rfl

end Surreal
