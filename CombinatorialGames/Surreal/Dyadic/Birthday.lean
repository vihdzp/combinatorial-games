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
-/

local notation "ω" => NatOrdinal.of Ordinal.omega0

@[simp]
theorem Game.birthday_ratCast (x : ℚ) : Game.birthday x = Surreal.birthday x := by
  rw [← Surreal.toGame_ratCast, Surreal.birthday_toGame]

theorem Surreal.birthday_dyadic_lt_omega0 (x : Dyadic) : Surreal.birthday x.toRat < ω := by
  rw [← Surreal.mk_dyadic]
  exact (Surreal.birthday_mk_le _).trans_lt (IGame.Short.birthday_lt_omega0 _)

theorem Surreal.birthday_lt_omega0_iff {x : Surreal} :
    x.birthday < ω ↔ x ∈ Set.range (fun x : Dyadic => (x.toRat : Surreal)) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨x, _, rfl, hx⟩ := Surreal.birthday_eq_iGameBirthday x
    rw [← hx, ← IGame.short_iff_birthday_finite] at h
    exact ⟨_, ratCast_toDyadic _⟩
  · rintro ⟨q, rfl⟩
    exact Surreal.birthday_dyadic_lt_omega0 q

-- `Dyadic'.toIGame` is canonical, so it minimizes the birthday in its equivalence class.
proof_wanted Surreal.birthday_dyadic (x : Dyadic) :
    Surreal.birthday x.toRat = IGame.birthday x

-- It's actually possible to explicitly compute the birthday of a dyadic number.
proof_wanted IGame.birthday_dyadic (x : Dyadic) :
    IGame.birthday x = ⌈x.num.natAbs⌉₊ + Nat.log2 x.den
