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
  !{fun p ↦ {y ∈ Set.range fun z : x.moves p ↦ undominate z | ∀ z ∈ x.moves p, ¬p.lt y z}}
termination_by x
decreasing_by igame_wf

theorem undominate_def {x : IGame} : x.undominate =
    !{fun p ↦ {y ∈ undominate '' x.moves p | ∀ z ∈ x.moves p, ¬ p.lt y z}} := by
  rw [undominate]
  simp

theorem undominate_def' {x : IGame} : x.undominate =
    !{{y ∈ undominate '' xᴸ | ∀ z ∈ xᴸ, ¬ y < z} |
    {y ∈ undominate '' xᴿ | ∀ z ∈ xᴿ, ¬ z < y}} := by
  rw [undominate_def, ofSets_eq_ofSets_cases]; rfl

@[simp]
theorem moves_undominate {x : IGame} {p : Player} :
    x.undominate.moves p = {y ∈ undominate '' x.moves p | ∀ z ∈ x.moves p, ¬p.lt y z} := by
  rw [undominate_def, moves_ofSets]

theorem moves_left_undominate {x : IGame} :
    x.undominateᴸ = {y ∈ undominate '' xᴸ | ∀ z ∈ xᴸ, ¬y < z} :=
  moves_undominate

theorem moves_right_undominate {x : IGame} :
    x.undominateᴿ = {y ∈ undominate '' xᴿ | ∀ z ∈ xᴿ, ¬z < y} :=
  moves_undominate

theorem birthday_undominate_le (x : IGame) : x.undominate.birthday ≤ x.birthday := by
  rw [undominate, birthday_le_iff']
  have (w) (hw : IsOption w x) := (birthday_undominate_le w).trans_lt (birthday_lt_of_isOption hw)
  aesop
termination_by x
decreasing_by igame_wf

instance {x : IGame} [hx : Short x] : Short (undominate x) := by
  rw [short_iff_birthday_finite] at hx ⊢
  exact (birthday_undominate_le x).trans_lt hx

@[simp]
theorem undominate_neg (x : IGame) : (-x).undominate = -x.undominate := by
  have := fun p ↦ moves_neg p x ▸ Set.image_neg_of_apply_neg_eq_neg fun y _ ↦ undominate_neg y
  rw [undominate_def', undominate_def', neg_ofSets]
  simp_all [IGame.lt_neg, IGame.neg_lt]
termination_by x
decreasing_by igame_wf

private theorem le_undominate (x : IGame) [Short x] : x ≤ undominate x := by
  rw [le_def, moves_undominate, moves_undominate]
  refine ⟨fun y hy ↦ ?_, ?_⟩
  · obtain ⟨z, ⟨hyz, ⟨hz, hz'⟩⟩⟩ := (Short.finite_moves _ x).exists_le_maximal hy
    short
    have IH := le_undominate z
    refine .inl ⟨_, ⟨⟨Set.mem_image_of_mem _ hz, fun a ha h ↦ ?_⟩, hyz.trans IH⟩⟩
    replace h := IH.trans_lt h
    exact (hz' ha h.le).not_gt h
  · rintro y ⟨⟨z, ⟨hz, rfl⟩⟩, _⟩
    short
    exact .inr ⟨z, hz, le_undominate z⟩
termination_by x
decreasing_by igame_wf

theorem undominate_equiv (x : IGame) [Short x] : undominate x ≈ x :=
  ⟨by simpa using le_undominate (-x), le_undominate x⟩

end IGame
