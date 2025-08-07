/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/

import CombinatorialGames.Game.IGame
import CombinatorialGames.Game.Loopy.Basic

/-!
# Well-founded games to loopy games

We define the embedding `IGame ↪ LGame`, and prove that it behaves in the expected ways with
arithmetic.
-/

open Set

noncomputable section

namespace IGame

private def toLGame' (x : IGame) : LGame :=
  {range fun y : x.leftMoves ↦ toLGame' y | range fun y : x.rightMoves ↦ toLGame' y}ᴸ
termination_by x
decreasing_by igame_wf

private theorem toLGame'_def (x : IGame) :
    x.toLGame' = {toLGame' '' x.leftMoves | toLGame' '' x.rightMoves}ᴸ := by
  rw [toLGame']
  simp_rw [image_eq_range]

private theorem toLGame'_inj {x y : IGame} (h : x.toLGame' = y.toLGame') : x = y := by
  rw [toLGame'_def, toLGame'_def] at h
  have hl := congrArg LGame.leftMoves h
  have hr := congrArg LGame.rightMoves h
  simp_rw [LGame.leftMoves_ofSets, LGame.rightMoves_ofSets] at hl hr
  ext z <;> constructor <;> intro hz
  · obtain ⟨w, hw, hw'⟩ := hl ▸ mem_image_of_mem _ hz
    obtain rfl := toLGame'_inj hw'.symm
    exact hw
  · obtain ⟨w, hw, hw'⟩ := hl ▸ mem_image_of_mem _ hz
    obtain rfl := toLGame'_inj hw'
    exact hw
  · obtain ⟨w, hw, hw'⟩ := hr ▸ mem_image_of_mem _ hz
    obtain rfl := toLGame'_inj hw'.symm
    exact hw
  · obtain ⟨w, hw, hw'⟩ := hr ▸ mem_image_of_mem _ hz
    obtain rfl := toLGame'_inj hw'
    exact hw
termination_by (x, y)
decreasing_by igame_wf

/-- The inclusion map from well-founded games into loopy games. -/
def toLGame : IGame ↪ LGame where
  toFun := toLGame'
  inj' _ _ := toLGame'_inj

theorem toLGame_def (x : IGame) :
    x.toLGame = {toLGame '' x.leftMoves | toLGame '' x.rightMoves}ᴸ :=
  toLGame'_def x

@[simp]
theorem leftMoves_toLGame (x : IGame) : x.toLGame.leftMoves = toLGame '' x.leftMoves := by
  rw [toLGame_def, LGame.leftMoves_ofSets]

@[simp]
theorem rightMoves_toLGame (x : IGame) : x.toLGame.rightMoves = toLGame '' x.rightMoves := by
  rw [toLGame_def, LGame.rightMoves_ofSets]

theorem mem_range_toLGame_iff_acc {x : LGame} : x ∈ range toLGame ↔ Acc LGame.IsOption x where
  mp := by
    rintro ⟨x, rfl⟩
    refine x.moveRecOn fun x hl hr ↦ .intro _ fun y ↦ ?_
    rintro (hy | hy) <;> simp only [leftMoves_toLGame, rightMoves_toLGame] at hy <;>
      obtain ⟨y, hy, rfl⟩ := hy
    exacts [hl y hy, hr y hy]
  mpr h := h.rec fun x _ ih ↦ by
    choose f hf using ih
    use {range fun y : x.leftMoves ↦ f y (.inl y.2) | range fun y : x.rightMoves ↦ f y (.inr y.2)}ᴵ
    ext1 <;> (simp only [leftMoves_toLGame, leftMoves_ofSets, rightMoves_toLGame, rightMoves_ofSets,
      ← range_comp]; convert Subtype.range_val; ext1; apply hf)

@[simp]
theorem toLGame_zero : toLGame 0 = 0 := by
  ext <;> simp

@[simp]
theorem toLGame_one : toLGame 1 = 1 := by
  ext <;> simp

@[simp]
theorem toLGame_neg (x : IGame) : toLGame (-x) = -toLGame x := by
  ext y
  on_goal 1 => rw [leftMoves_toLGame, leftMoves_neg, LGame.leftMoves_neg, rightMoves_toLGame]
  on_goal 2 => rw [rightMoves_toLGame, rightMoves_neg, LGame.rightMoves_neg, leftMoves_toLGame]
  all_goals
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨_, hy, ?_⟩
      rw [← neg_neg y, toLGame_neg (-y)]
      simp
    · rintro ⟨y, hy, hy'⟩
      obtain rfl := neg_eq_iff_eq_neg.2 hy'
      exact ⟨_, neg_mem_neg.2 hy, toLGame_neg y⟩
termination_by x
decreasing_by igame_wf

@[simp]
theorem toLGame_add (x y : IGame) : toLGame (x + y) = toLGame x + toLGame y := by
  ext z
  on_goal 1 => simp_rw [LGame.leftMoves_add, leftMoves_toLGame, leftMoves_add]
  on_goal 2 => simp_rw [LGame.rightMoves_add, rightMoves_toLGame, rightMoves_add]
  all_goals
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩, rfl⟩
      · exact .inl ⟨_, mem_image_of_mem _ hz, (toLGame_add ..).symm⟩
      · refine .inr ⟨_, mem_image_of_mem _ hz, (toLGame_add ..).symm⟩
    · rintro (⟨_, ⟨z, hz, rfl⟩, rfl⟩ | ⟨_, ⟨z, hz, rfl⟩, rfl⟩)
      · exact ⟨_, .inl ⟨z, hz, rfl⟩, toLGame_add ..⟩
      · exact ⟨_, .inr ⟨z, hz, rfl⟩, toLGame_add ..⟩
termination_by (x, y)
decreasing_by igame_wf

@[simp]
theorem toLGame_sub (x y : IGame) : toLGame (x - y) = toLGame x - toLGame y := by
  simp [sub_eq_add_neg]

set_option maxHeartbeats 500000 in
@[simp]
theorem toLGame_mul (x y : IGame) : toLGame (x * y) = toLGame x * toLGame y := by
  ext z
  on_goal 1 => simp_rw [LGame.leftMoves_mul, leftMoves_toLGame, leftMoves_mul, rightMoves_toLGame]
  on_goal 2 => simp_rw [LGame.rightMoves_mul, rightMoves_toLGame, rightMoves_mul, leftMoves_toLGame]
  all_goals
    constructor
    on_goal 1 =>
      rintro ⟨_, ⟨⟨a, b⟩, ⟨ha, hb⟩ | ⟨ha, hb⟩, rfl⟩, rfl⟩ <;>
      have H : (toLGame a, toLGame b) ∈ (toLGame '' _) ×ˢ (toLGame '' _) :=
        ⟨mem_image_of_mem _ ha, mem_image_of_mem _ hb⟩
      on_goal 1 => refine ⟨_, .inl H, ?_⟩
      on_goal 2 => refine ⟨_, .inr H, ?_⟩
    on_goal 3 =>
      rintro ⟨⟨_, _⟩, ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩ | ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, rfl⟩ <;>
      have H : (a, b) ∈ _ ×ˢ _ := ⟨ha, hb⟩
      on_goal 1 => refine ⟨_, ⟨_, .inl H, rfl⟩, ?_⟩
      on_goal 2 => refine ⟨_, ⟨_, .inr H, rfl⟩, ?_⟩
    all_goals
      dsimp
      rw [LGame.mulOption, mulOption, toLGame_sub, toLGame_add,
        toLGame_mul, toLGame_mul, toLGame_mul]
termination_by (x, y)
decreasing_by igame_wf

@[simp]
theorem toLGame_mulOption (x y a b : IGame) :
    toLGame (mulOption x y a b) = LGame.mulOption x.toLGame y.toLGame a.toLGame b.toLGame := by
  simp [mulOption, LGame.mulOption]

end IGame
end
