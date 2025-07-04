/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Surreal.Basic
import Mathlib.Data.Sign
import Mathlib.Data.Fintype.Units

/-!
# Sign Expansions

Every surreal number has a sign expansion, a function from its birthday to the set `{-1, 1}`.
This sign expansion uniquely identifies the number.
-/

universe u

noncomputable section
open IGame

namespace Surreal

def signApprox (x : Surreal.{u}) (o : NatOrdinal.{u}) : Surreal :=
  @Surreal.mk {{s : IGame.{u} | s.birthday < o} ∩ {s | ∃ _ : s.Numeric, .mk s < x} |
    {s : IGame.{u} | s.birthday < o} ∩ {s | ∃ _ : s.Numeric, x < .mk s}}ᴵ <| by
      rw [numeric_def]
      refine ⟨?_, ?_, ?_⟩
      · intro y hy z hz
        rw [leftMoves_ofSets] at hy
        rw [rightMoves_ofSets] at hz
        have := hy.2.1
        have := hz.2.1
        exact Surreal.mk_lt_mk.mp (hy.2.2.trans hz.2.2)
      · intro y hy
        rw [leftMoves_ofSets] at hy
        exact hy.2.1
      · intro y hy
        rw [rightMoves_ofSets] at hy
        exact hy.2.1

theorem birthday_signApprox_le (x : Surreal.{u}) (o : NatOrdinal.{u}) :
    (signApprox x o).toGame.birthday ≤ o := by
  rw [signApprox, Surreal.toGame_mk]
  apply (Game.birthday_mk_le _).trans
  rw [birthday_le_iff, leftMoves_ofSets, rightMoves_ofSets]
  constructor
  · intro y hy
    exact hy.left
  · intro y hy
    exact hy.left

end Surreal

structure SignExpansion : Type (u + 1) where
  size : NatOrdinal.{u}
  sign : Set.Iio size → ℤˣ

namespace SignExpansion

instance : FunLike SignExpansion.{u} NatOrdinal.{u} SignType where
  coe e o := if h : o < e.size then .sign (e.sign ⟨o, h⟩ : ℤ) else 0
  coe_injective' a b hab := by
    let p (i : SignExpansion.{u}) (o : NatOrdinal.{u}) : SignType :=
      (if h : o < i.size then .sign (i.sign ⟨o, h⟩ : ℤ) else 0)
    change p a = p b at hab
    have hi (i : SignExpansion.{u}) :
      ⨅ (o : Subtype (p i · = 0)), o.1 = i.size := by
      have hi : (p i · = 0) = (· ∈ Set.Ici i.size) := by simp [p]
      rw [hi]
      apply le_antisymm
      · exact ciInf_le ⟨⊥, bot_mem_lowerBounds _⟩ (Subtype.mk i.size le_rfl)
      · apply le_ciInf
        exact Subtype.prop
    have h : a.size = b.size := calc
      _ = _ := (hi a).symm
      _ = _ := by rw [hab]
      _ = _ := hi b
    cases a with | mk s ua
    cases b with | mk s ub
    cases h
    rw [SignExpansion.mk.injEq, eq_self, true_and, heq_iff_eq]
    ext ⟨i, ci⟩
    -- #check congr($hab i)
    have uu := congrFun hab i
    simp_rw [p, dif_pos (Set.mem_Iio.mp ci)] at uu
    have cx : ∀ {x y : ℤˣ} (h : SignType.sign (x : ℤ) = SignType.sign (y : ℤ)), x = y := by
      decide
    rw [cx uu]

instance : LinearOrder SignExpansion.{u} :=
  LinearOrder.lift' (toLex ⇑·) (by simp [Function.Injective])

theorem coe_le_coe {a b : SignExpansion.{u}} : toLex ⇑a ≤ toLex ⇑b ↔ a ≤ b := Iff.rfl
theorem coe_lt_coe {a b : SignExpansion.{u}} : toLex ⇑a < toLex ⇑b ↔ a < b := Iff.rfl

def ofSurreal (x : Surreal.{u}) : SignExpansion where
  size := x.toGame.birthday
  sign i :=
    match h : compare (x.signApprox i) x with
    | .lt => 1
    | .eq => False.elim <| by
      rw [compare_eq_iff_eq] at h
      refine ne_of_lt ?_ congr(($h).toGame.birthday)
      exact (x.birthday_signApprox_le i).trans_lt i.prop
    | .gt => -1

end SignExpansion
