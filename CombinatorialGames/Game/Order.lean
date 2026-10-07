/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import CombinatorialGames.Game.Birthday

/-!
# Games are densely ordered

We provide instances of `DenselyOrdered` for `IGame` and `Game`.
-/

universe u

namespace IGame

theorem tiny_lf_aux {x a : IGame} (hx : 0 ⧏ x) (ha : ∀ y ∈ xᴿ, -y ≤ a) : ⧾a ⧏ x := by
  refine lf_of_right_le ?_ (rightMoves_tiny _ ▸ Set.mem_singleton _)
  rw [le_iff_forall_lf]
  exact ⟨by simpa using hx, fun z hz => lf_of_right_le (IGame.neg_le.1 (ha z hz)) (by simp)⟩

theorem tiny_le_aux {x a : IGame} (hx : 0 < x)
    (ha : ∀ y ∈ xᴿ, ∀ z ∈ yᴿ, -z ≤ a) : ⧾a ≤ x := by
  rw [le_iff_forall_lf]
  constructor
  · simpa using hx.not_ge
  · exact fun y hy ↦ tiny_lf_aux (lf_right_of_le hx.le hy) (ha y hy)

public section

theorem tiny_toIGame_birthday_lt {x : IGame.{u}} (hx : 0 < x) : ⧾x.birthday.toIGame < x := by
  apply lt_of_le_not_ge
  · refine tiny_le_aux hx fun y hy z hz =>
      (le_toIGame_birthday _).trans (NatOrdinal.toIGame.monotone ?_)
    grw [birthday_neg, birthday_lt_of_mem_moves hz, birthday_lt_of_mem_moves hy]
  · refine tiny_lf_aux hx.not_ge fun y hy =>
      (le_toIGame_birthday _).trans (NatOrdinal.toIGame.monotone ?_)
    grw [birthday_neg, birthday_lt_of_mem_moves hy]

theorem tiny_lt_of_toIGame_birthday_le {x : IGame.{u}} (hx : 0 < x)
    {o : IGame.{u}} (ho : x.birthday ≤ o) : ⧾o < x :=
  lt_of_le_of_lt (tiny_antitone ho) (tiny_toIGame_birthday_lt hx)

theorem fuzzy_tiny_of_birthday_le {x : IGame.{u}} (hx : x ‖ 0)
    {o : IGame.{u}} (ho : x.birthday ≤ o) : x ‖ ⧾o := by
  constructor
  · refine tiny_lf_aux hx.not_le fun y hy =>
      (le_toIGame_birthday _).trans ?_
    grw [birthday_neg, birthday_lt_of_mem_moves hy, ho]
  · exact fun h => hx.not_ge ((tiny_pos _).le.trans h)

theorem fuzzy_tiny_toIGame_birthday {x : IGame.{u}} (hx : x ‖ 0) : x ‖ ⧾x.birthday.toIGame :=
  fuzzy_tiny_of_birthday_le hx le_rfl

theorem lt_miny_toIGame_birthday {x : IGame.{u}} (hx : x < 0) : x < ⧿x.birthday.toIGame := by
  simpa using IGame.lt_neg.2 (tiny_toIGame_birthday_lt (IGame.zero_lt_neg.2 hx))

theorem lt_miny_toIGame_of_birthday_le {x : IGame.{u}} (hx : x < 0)
    {o : NatOrdinal.{u}} (ho : x.birthday ≤ o) : x < ⧿o.toIGame :=
  lt_of_lt_of_le (lt_miny_toIGame_birthday hx) (miny_monotone (NatOrdinal.toIGame.monotone ho))

theorem fuzzy_miny_of_birthday_le {x : IGame.{u}} (hx : x ‖ 0)
    {o : IGame.{u}} (ho : x.birthday ≤ o) : x ‖ ⧿o := by
  rw [← neg_fuzzy_neg_iff]
  simpa using fuzzy_tiny_of_birthday_le (neg_fuzzy_zero.2 hx) (by simpa using ho)

theorem fuzzy_miny_toIGame_birthday {x : IGame.{u}} (hx : x ‖ 0) : x ‖ ⧿x.birthday.toIGame := by
  rw [← neg_fuzzy_neg_iff]
  simpa using fuzzy_tiny_toIGame_birthday (neg_fuzzy_zero.2 hx)

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

end
end IGame
