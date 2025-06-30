/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Game.IGame

/-!
# Game reductions

We prove that dominated moves can be deleted and reversible moves can be bypassed.
-/

universe u

namespace IGame

theorem equiv_of_dominated_left {u v r : Set IGame.{u}} [Small.{u} u] [Small.{u} v] [Small.{u} r]
    (hu : ∀ g ∈ u, ∃ g' ∈ v, g ≤ g') : {u ∪ v | r}ᴵ ≈ {v | r}ᴵ := by
  apply equiv_of_exists_le <;> aesop

theorem equiv_of_dominated_right {l u v : Set IGame.{u}} [Small.{u} l] [Small.{u} u] [Small.{u} v]
    (hu : ∀ g ∈ u, ∃ g' ∈ v, g' ≤ g) : {l | u ∪ v}ᴵ ≈ {l | v}ᴵ := by
  apply equiv_of_exists_le <;> aesop

theorem equiv_of_bypass_left {l r : Set IGame.{u}} [Small.{u} l] [Small.{u} r]
    {cs crs : Set IGame.{u}} [Small.{u} cs] [Small.{u} crs]
    (hcr : ∀ cr ∈ crs, ∃ c ∈ cs, cr ∈ c.rightMoves) :
    {cs ∪ l | r}ᴵ ≈ {(⋃ cr ∈ crs, cr.leftMoves) ∪ l | r}ᴵ := by
  sorry

theorem equiv_of_bypass_right {l r : Set IGame.{u}} [Small.{u} l] [Small.{u} r]
    {ds dls : Set IGame.{u}} [Small.{u} ds] [Small.{u} dls]
    (hdl : ∀ dl ∈ dls, ∃ d ∈ ds, dl ∈ d.leftMoves) :
    {l | ds ∪ r}ᴵ ≈ {l | (⋃ dl ∈ dls, dl.rightMoves) ∪ r}ᴵ := by
  sorry

end IGame
