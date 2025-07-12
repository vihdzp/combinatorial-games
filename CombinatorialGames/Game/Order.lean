/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Game.Birthday
import CombinatorialGames.Game.Special

/-!
# Games are densely ordered

We provide instances of `DenselyOrdered` for `IGame` and `Game`.
-/

universe u

noncomputable section
namespace IGame

theorem tiny_toIGame_birthday_lt {x : IGame.{u}} (hx : 0 < x) :
    ⧾x.birthday.toIGame < x := by
  apply lt_of_le_not_ge
  · rw [le_iff_forall_lf]
    constructor
    · simp [hx.not_ge]
    · intro y hy
      rw [lf_iff_exists_le]
      right
      simp only [rightMoves_tiny, Set.mem_singleton_iff, exists_eq_left]
      rw [le_iff_forall_lf]
      simp only [leftMoves_ofSets, Set.mem_singleton_iff, forall_eq]
      have h := hx.le
      rw [le_iff_forall_lf] at h
      refine ⟨h.right y hy, fun z hz => ?_⟩
      rw [lf_iff_exists_le]
      right
      simp only [rightMoves_ofSets, Set.mem_singleton_iff, exists_eq_left]
      apply (neg_toIGame_birthday_le z).trans'
      simpa using (birthday_lt_of_mem_rightMoves hz).le.trans (birthday_lt_of_mem_rightMoves hy).le
  · rw [lf_iff_exists_le]
    right
    simp only [rightMoves_tiny, Set.mem_singleton_iff, exists_eq_left]
    rw [le_iff_forall_lf]
    simp only [leftMoves_ofSets, Set.mem_singleton_iff, forall_eq]
    refine ⟨hx.not_ge, fun z hz => ?_⟩
    rw [lf_iff_exists_le]
    right
    simp only [rightMoves_ofSets, Set.mem_singleton_iff, exists_eq_left]
    apply (neg_toIGame_birthday_le z).trans'
    simpa using (birthday_lt_of_mem_rightMoves hz).le

instance : DenselyOrdered IGame.{u} where
  dense a b hab := by
    refine ⟨a + ⧾(b - a).birthday.toIGame, ?_, ?_⟩
    · simp [tiny_pos]
    · rw [add_comm, ← IGame.lt_sub_iff_add_lt]
      exact tiny_toIGame_birthday_lt (IGame.sub_pos.2 hab)

instance : DenselyOrdered Game.{u} where
  dense a b hab := by
    induction a using Game.ind with | mk a =>
    induction b using Game.ind with | mk b =>
    rw [Game.mk_lt_mk] at hab
    obtain ⟨c, hac, hcb⟩ := exists_between hab
    exact ⟨.mk c, hac, hcb⟩
