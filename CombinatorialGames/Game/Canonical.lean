/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
import CombinatorialGames.Game.Birthday

/-!
# Canonical games

For any game G, its canonical game G' is the unique IGame game with
smallest birthday such that G'.Fits G.
From the literature, this file provides an explicit (though noncomputable) construction of canonical
games through undominating and unreversing games.

## Todo

- Define (un)reversibility
-/

universe u


namespace IGame

/-- Undominating a game. This returns garbage values on non-short games -/
noncomputable def undominate (x : IGame) : IGame :=
  {{y ∈ Set.range fun z : x.leftMoves ↦ undominate z | ∀ z ∈ x.leftMoves, ¬y < z} |
    {y ∈ Set.range fun z : x.rightMoves ↦ undominate z | ∀ z ∈ x.rightMoves, ¬z < y}}ᴵ
termination_by x
decreasing_by igame_wf

theorem birthday_undominate_le (x : IGame) : x.undominate.birthday ≤ x.birthday := by
  rw [undominate, birthday_le_iff']
  have (w) (hw : IsOption w x) := (birthday_undominate_le w).trans_lt (birthday_lt_of_isOption hw)
  aesop
termination_by x
decreasing_by igame_wf

theorem undominate_def {x : IGame} : x.undominate =
    {{y ∈ undominate '' x.leftMoves | ∀ z ∈ x.leftMoves, ¬y < z} |
      {y ∈ undominate '' x.rightMoves | ∀ z ∈ x.rightMoves, ¬z < y}}ᴵ := by
  rw [undominate]
  simp

@[simp]
theorem leftMoves_undominate {x : IGame} :
    x.undominate.leftMoves = {y ∈ undominate '' x.leftMoves | ∀ z ∈ x.leftMoves, ¬y < z} := by
  rw [undominate_def]
  exact leftMoves_ofSets ..

@[simp]
theorem rightMoves_undominate {x : IGame} :
    x.undominate.rightMoves = {y ∈ undominate '' x.rightMoves | ∀ z ∈ x.rightMoves, ¬z < y} := by
  rw [undominate_def]
  exact rightMoves_ofSets ..

instance {x : IGame} [hx : Short x] : Short (undominate x) := by
  rw [short_iff_birthday_finite] at hx ⊢
  exact (birthday_undominate_le x).trans_lt hx

@[simp]
theorem undominate_neg (x : IGame) : (-x).undominate = -x.undominate := by
  have := leftMoves_neg x ▸ Set.image_neg_of_apply_neg_eq_neg fun y _ ↦ undominate_neg y
  have := rightMoves_neg x ▸ Set.image_neg_of_apply_neg_eq_neg fun y _ ↦ undominate_neg y
  rw [undominate_def, undominate_def]
  simp_all [IGame.lt_neg, IGame.neg_lt]
termination_by x
decreasing_by igame_wf

private theorem le_undominate (x : IGame) [Short x] : x ≤ undominate x := by
  rw [le_def, leftMoves_undominate, rightMoves_undominate]
  refine ⟨fun y hy ↦ ?_, ?_⟩
  · obtain ⟨z, ⟨hyz, ⟨hz, hz'⟩⟩⟩ := (Short.finite_leftMoves x).exists_le_maximal hy
    have := Short.of_mem_leftMoves hz
    have IH := le_undominate z
    refine .inl ⟨_, ⟨⟨Set.mem_image_of_mem _ hz, fun a ha h ↦ ?_⟩, hyz.trans IH⟩⟩
    replace h := IH.trans_lt h
    exact (hz' ha h.le).not_gt h
  · rintro y ⟨⟨z, ⟨hz, rfl⟩⟩, _⟩
    have := Short.of_mem_rightMoves hz
    exact .inr ⟨z, hz, le_undominate z⟩
termination_by x
decreasing_by igame_wf

theorem undominate_equiv (x : IGame) [Short x] : undominate x ≈ x :=
  ⟨by simpa using le_undominate (-x), le_undominate x⟩

end IGame
