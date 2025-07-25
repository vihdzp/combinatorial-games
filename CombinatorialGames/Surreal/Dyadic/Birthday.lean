/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Dyadic.Basic
import CombinatorialGames.Surreal.Birthday.Cut

/-!
# Birthday of dyadic rationals

We prove that a surreal number has a finite birthday iff it's a dyadic number.

## Todo

There's a lot to be said about birthdays of dyadic numbers. The `proof_wanted` blocks should provide
guidance!
-/

local notation "ω" => Ordinal.omega0.toNatOrdinal

@[simp]
theorem Game.birthday_ratCast (x : ℚ) : Game.birthday x = Surreal.birthday x := by
  rw [← Surreal.toGame_ratCast, Surreal.birthday_toGame]

theorem Surreal.birthday_dyadic_lt_omega0 (x : Dyadic) : Surreal.birthday x < ω := by
  rw [← Surreal.mk_dyadic]
  exact (Surreal.birthday_mk_le _).trans_lt (IGame.Short.birthday_lt_omega0 _)

theorem Surreal.birthday_lt_omega0_iff {x : Surreal} :
    x.birthday < ω ↔ x ∈ Set.range ((↑) : Dyadic → _) := by
  constructor
  · intro h
    obtain ⟨x, _, rfl, hx⟩ := Surreal.birthday_eq_iGameBirthday x
    rw [← hx, ← IGame.short_iff_birthday_finite] at h
    use IGame.toDyadic x
    simp
  · rintro ⟨q, rfl⟩
    exact Surreal.birthday_dyadic_lt_omega0 q
