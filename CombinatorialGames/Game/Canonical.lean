/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/

import CombinatorialGames.Game.Birthday

/-!
# Canonical games

For any game G, its canonical game is the game of unique lowest birthday
which fits inside G. From the literature, this file provides an explicit
(though noncomputable) construction of canonical games through undominating
and unreversing games.

## TODO
- Define (un)reversibility
-/

universe u

namespace IGame

/-- Undominating a game. This returns garbage values on non-short games -/
noncomputable def undominate (x : IGame) : IGame :=
  have : Small {y : IGame | y.birthday < x.birthday} :=
    show Small {y : IGame // y.birthday < x.birthday} by infer_instance
  {{y ∈ {y | y.birthday < x.birthday} ∩
      {y | ∃ z, ∃ (_ : z ∈ x.leftMoves), z.undominate = y} | ∀ z ∈ x.leftMoves, ¬y < z} |
    {y ∈ {y | y.birthday < x.birthday} ∩
        {y | ∃ z, ∃ (_ : z ∈ x.rightMoves), z.undominate = y} | ∀ z ∈ x.rightMoves, ¬z < y}}ᴵ
termination_by x
decreasing_by igame_wf

theorem undominate_birthday_le (x : IGame) : x.undominate.birthday ≤ x.birthday := by
  rw [undominate, birthday_le_iff']
  aesop

theorem undominate_def {x : IGame} :
    x.undominate = {{y ∈ undominate '' x.leftMoves | ∀ z ∈ x.leftMoves, ¬y < z} |
      {y ∈ undominate '' x.rightMoves | ∀ z ∈ x.rightMoves, ¬z < y}}ᴵ:= by
  rw [undominate]
  apply IGame.ext <;> ext y
  · suffices (∀ z ∈ x.leftMoves, ¬y < z) → ∀ z ∈ x.leftMoves, z.undominate = y →
      y.birthday < x.birthday by simpa
    intro hz z hz hzy
    have := (undominate_birthday_le z).trans_lt (birthday_lt_of_mem_leftMoves hz)
    rwa [hzy] at this
  · suffices (∀ z ∈ x.rightMoves, ¬z < y) → ∀ z ∈ x.rightMoves, z.undominate = y →
      y.birthday < x.birthday by simpa
    intro hz z hz hzy
    have := (undominate_birthday_le z).trans_lt (birthday_lt_of_mem_rightMoves hz)
    rwa [hzy] at this

@[simp]
theorem undominate_leftMoves {x : IGame} :
    x.undominate.leftMoves = {y ∈ undominate '' x.leftMoves | ∀ z ∈ x.leftMoves, ¬y < z} := by
  rw [undominate_def]
  exact leftMoves_ofSets ..

@[simp]
theorem undominate_rightMoves {x : IGame} :
    x.undominate.rightMoves = {y ∈ undominate '' x.rightMoves | ∀ z ∈ x.rightMoves, ¬z < y} := by
  rw [undominate_def]
  exact rightMoves_ofSets ..

instance {x : IGame} [hx : Short x] : Short (undominate x) := by
  rw [short_iff_birthday_finite] at hx ⊢
  exact (undominate_birthday_le x).trans_lt hx

@[simp]
theorem undominate_neg {x : IGame} [Short x] : (-x).undominate = -x.undominate := by
  ext y
  all_goals
    simp only [undominate_leftMoves, leftMoves_neg, rightMoves_neg, Set.mem_image, Set.mem_neg,
      Set.mem_setOf_eq, undominate_rightMoves]
    constructor <;> intro ⟨⟨z, ⟨hxz, hz⟩⟩, hzy⟩ <;> constructor
  · subst hz
    have : (-z).Short := Short.of_mem_rightMoves hxz
    refine ⟨-z, hxz, ?_⟩
    have := undominate_neg (x := - z)
    rw [neg_neg] at this
    rw [this, neg_neg]
  · intro a ha
    have := hzy (-a) (show - (-a) ∈ x.rightMoves by simpa)
    rwa [IGame.lt_neg] at this
  · have : z.Short := Short.of_mem_rightMoves hxz
    refine ⟨-z, by simpa, ?_⟩
    rw [undominate_neg]
    exact neg_eq_iff_eq_neg.mpr hz
  · intro a ha
    have := hzy (-a) ha
    rwa [IGame.neg_lt_neg_iff] at this
  · subst hz
    refine ⟨-z, hxz, ?_⟩
    have : (-z).Short := Short.of_mem_leftMoves hxz
    have := undominate_neg (x := -z)
    rw [neg_neg] at this
    rw [this, neg_neg]
  · intro a ha
    have := hzy (-a) (show - (-a) ∈ x.leftMoves by simpa)
    rwa [IGame.neg_lt] at this
  · have : z.Short := Short.of_mem_leftMoves hxz
    refine ⟨-z, by simpa, ?_⟩
    rw [undominate_neg]
    exact neg_eq_iff_eq_neg.mpr hz
  · intro a ha
    have := hzy (-a) ha
    rwa [IGame.neg_lt_neg_iff] at this
termination_by x
decreasing_by igame_wf

theorem exists_ge_in_undominate_of_leftMoves {x y : IGame} [Short x] (hy₁ : y ∈ x.leftMoves) :
    ∃ z ∈ (undominate x).leftMoves, y ≤ z := by
  have : Fintype x.leftMoves := Fintype.ofFinite _
  have : Fintype (undominate '' x.leftMoves) := Fintype.ofFinite _
  obtain ⟨z, ⟨hyz, hz⟩⟩ := Finset.exists_le_maximal _ (Set.mem_toFinset.mpr hy₁)
  simp_rw [undominate_leftMoves, Set.mem_setOf_eq]
  refine ⟨z, ⟨(Set.mem_toFinset.mp (by sorry)), fun a ha ↦ ?_⟩, hyz⟩
  exact Maximal.not_gt hz (Set.mem_toFinset.mpr ha)

theorem exists_gt_in_undominate_of_rightMoves {x y : IGame} [Short x] (hy₁ : y ∈ x.rightMoves) :
    ∃ z ∈ (undominate x).rightMoves, z ≤ y := by
  have : -y ∈ (-x).leftMoves := by simp_all
  obtain ⟨z, ⟨hz, hzy⟩⟩ := exists_ge_in_undominate_of_leftMoves this
  refine ⟨-z, ?_, IGame.neg_le.mp hzy⟩
  rwa [undominate_neg, leftMoves_neg] at hz

theorem undominate_equiv {x : IGame} [Short x] : x ≈ undominate x := by
  constructor <;> dsimp only <;> rw [le_def]
  · rw [undominate_rightMoves]
    refine ⟨fun a ha ↦ .inl (exists_ge_in_undominate_of_leftMoves ha),
      fun a ⟨⟨b, ⟨hb, hba⟩⟩, _⟩ ↦ .inr ⟨b, hb, ?_⟩⟩
    have : b.Short := Short.of_mem_rightMoves hb
    rw [← hba]
    exact AntisymmRel.ge undominate_equiv.symm
  · rw [undominate_leftMoves]
    refine ⟨fun a ⟨⟨b, ⟨hb, hba⟩⟩, _⟩ ↦ .inl ⟨b, hb, ?_⟩,
      fun a ha ↦ .inr (exists_gt_in_undominate_of_rightMoves ha)⟩
    have : b.Short := Short.of_mem_leftMoves hb
    rw [← hba]
    exact AntisymmRel.ge undominate_equiv
termination_by x
decreasing_by igame_wf

end IGame
