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
  !{range fun y : xᴸ ↦ toLGame' y | range fun y : xᴿ ↦ toLGame' y}
termination_by x
decreasing_by igame_wf

private theorem toLGame'_def (x : IGame) :
    x.toLGame' = !{toLGame' '' xᴸ | toLGame' '' xᴿ} := by
  rw [toLGame']
  simp_rw [image_eq_range]

private theorem toLGame'_def' (x : IGame) :
    x.toLGame' = !{fun p ↦ toLGame' '' moves p x} := by
  rw [toLGame'_def, ofSets_eq_ofSets_cases (fun _ ↦ _ '' _)]

private theorem toLGame'_inj {x y : IGame} (h : x.toLGame' = y.toLGame') : x = y := by
  rw [toLGame'_def', toLGame'_def'] at h
  have h (p) := congrArg (moves p) h
  simp_rw [LGame.moves_ofSets] at h
  ext p; constructor <;> (intro hz; obtain ⟨w, hw, hw'⟩ := h _ ▸ mem_image_of_mem _ hz)
  · obtain rfl := toLGame'_inj hw'.symm
    exact hw
  · obtain rfl := toLGame'_inj hw'
    exact hw
termination_by (x, y)
decreasing_by igame_wf

/-- The inclusion map from well-founded games into loopy games. -/
def toLGame : IGame ↪ LGame where
  toFun := toLGame'
  inj' _ _ := toLGame'_inj

instance : Coe IGame LGame := ⟨toLGame⟩

theorem toLGame_def (x : IGame) :
    x.toLGame = !{toLGame '' xᴸ | toLGame '' xᴿ} :=
  toLGame'_def x

@[simp]
theorem moves_toLGame (p : Player) (x : IGame) : moves p x.toLGame = toLGame '' moves p x := by
  rw [toLGame_def, LGame.moves_ofSets]; cases p <;> rfl

theorem _root_.IGame.acc_toLGame (x : IGame) : Acc LGame.IsOption x := by
  refine x.moveRecOn fun x h ↦ .intro _ fun y ↦ ?_
  rw [LGame.isOption_iff_mem_union]
  rintro (hy | hy) <;> simp only [moves_toLGame] at hy <;> obtain ⟨y, hy, rfl⟩ := hy
  exacts [h _ y hy, h _ y hy]

theorem mem_range_toLGame_iff_acc {x : LGame} : x ∈ range toLGame ↔ Acc LGame.IsOption x where
  mp := by rintro ⟨x, rfl⟩; exact x.acc_toLGame
  mpr h := h.rec fun x _ ih ↦ by
    choose f hf using ih
    use !{fun p ↦ range fun y : moves p x ↦ f y (by aesop)}
    ext1
    simp only [moves_toLGame, moves_ofSets, ← range_comp]
    convert Subtype.range_val
    ext1
    apply hf

@[simp]
theorem toLGame_zero : toLGame 0 = 0 := by
  ext p; cases p <;> simp

@[simp]
theorem toLGame_one : toLGame 1 = 1 := by
  ext p; cases p <;> simp

@[simp]
theorem toLGame_neg (x : IGame) : toLGame (-x) = -toLGame x := by
  ext y
  rw [moves_toLGame, moves_neg, LGame.moves_neg, moves_toLGame]
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
  simp_rw [LGame.moves_add, moves_toLGame, moves_add]
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

@[simp]
theorem toLGame_mul (x y : IGame) : toLGame (x * y) = toLGame x * toLGame y := by
  ext z
  simp_rw [LGame.moves_mul, moves_toLGame, moves_mul]
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
    toLGame (mulOption x y a b) = LGame.mulOption x y a b := by
  simp [mulOption, LGame.mulOption]

end IGame
end
