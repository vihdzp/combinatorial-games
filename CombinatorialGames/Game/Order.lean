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

theorem tiny_lf_of_not_nonpos_of_forall_neg_le {x a : IGame} (hx : 0 ⧏ x)
    (ha : ∀ y ∈ xᴿ, -a ≤ y) : ⧾a ⧏ x := by
  refine lf_of_rightMove_le ?_ (moves_right_tiny _ ▸ Set.mem_singleton _)
  rw [le_iff_forall_lf]
  simpa using ⟨hx, fun z hz ↦ lf_of_rightMove_le (ha z hz) (by simp)⟩

theorem tiny_le_of_pos_of_forall_neg_le {x a : IGame} (hx : 0 < x)
    (ha : ∀ y ∈ xᴿ, ∀ z ∈ yᴿ, -a ≤ z) : ⧾a ≤ x := by
  rw [le_iff_forall_lf]
  constructor
  · simpa using hx.not_ge
  · exact fun y hy ↦ tiny_lf_of_not_nonpos_of_forall_neg_le (lf_rightMove_of_le hx.le hy) (ha y hy)

theorem tiny_toIGame_birthday_lt {x : IGame.{u}} (hx : 0 < x) : ⧾x.birthday.toIGame < x := by
  apply lt_of_le_not_ge
  · refine tiny_le_of_pos_of_forall_neg_le hx
      fun y hy z hz ↦ (neg_toIGame_birthday_le z).trans' ?_
    simpa using ((birthday_lt_of_mem_moves hz).trans (birthday_lt_of_mem_moves hy)).le
  · refine tiny_lf_of_not_nonpos_of_forall_neg_le hx.not_ge
      fun y hy ↦ (neg_toIGame_birthday_le y).trans' ?_
    simpa using (birthday_lt_of_mem_moves hy).le

theorem lf_miny_of_not_nonneg_of_forall_le {x a : IGame} (hx : x ⧏ 0)
    (ha : ∀ y ∈ xᴸ, y ≤ a) : x ⧏ ⧿a := by
  refine lf_of_le_leftMove ?_ (moves_left_miny _ ▸ Set.mem_singleton _)
  rw [le_iff_forall_lf]
  simpa using ⟨fun z hz ↦ lf_of_le_leftMove (ha z hz) (by simp), hx⟩

theorem le_miny_of_neg_of_forall_le_neg {x a : IGame} (hx : x < 0)
    (ha : ∀ y ∈ xᴸ, ∀ z ∈ yᴸ, z ≤ a) : x ≤ ⧿a := by
  rw [le_iff_forall_lf]
  constructor
  · exact fun y hy ↦ lf_miny_of_not_nonneg_of_forall_le (leftMove_lf_of_le hx.le hy) (ha y hy)
  · simpa using hx.not_ge

theorem lt_miny_toIGame_birthday {x : IGame.{u}} (hx : x < 0) : x < ⧿x.birthday.toIGame := by
  simpa using IGame.lt_neg.2 (tiny_toIGame_birthday_lt (IGame.zero_lt_neg.2 hx))

instance : DenselyOrdered IGame where
  dense a b hab := by
    refine ⟨⧾(b - a).birthday.toIGame + a, ?_, ?_⟩
    · simp [tiny_pos]
    · rw [← IGame.lt_sub_iff_add_lt]
      exact tiny_toIGame_birthday_lt (IGame.sub_pos.2 hab)

instance : DenselyOrdered Game where
  dense a b hab := by
    induction a using Game.ind with | mk a
    induction b using Game.ind with | mk b
    rw [Game.mk_lt_mk] at hab
    obtain ⟨c, hac, hcb⟩ := exists_between hab
    exact ⟨.mk c, hac, hcb⟩

end IGame
end
