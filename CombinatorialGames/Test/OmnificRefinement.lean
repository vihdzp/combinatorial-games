/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

import CombinatorialGames.Surreal.Omnific.Refinement
import Mathlib.Algebra.Prime.Defs
meta import Lean.Elab.AssertExists

/-!
# Omnific refinement from cuts

Restate the theorem for four surreals satisfying Conway's unit cut, then use the
decomposition monoid instance to deduce that every irreducible omnific integer is prime.
-/

assert_not_imported CombinatorialGames.Surreal.HahnSeries.Basic Mathlib.RingTheory.HahnSeries.Basic

assert_not_imported CombinatorialGames.Surreal.Germ.Transcendence
  CombinatorialGames.Surreal.Scale.Bounded.Polynomial CombinatorialGames.Surreal.Omnific.Denominator

open Surreal

example :
    let Whole (x : Surreal) := x = !{{x - 1} | {x + 1}}' (by
      simp only [Set.mem_singleton_iff]
      rintro _ rfl _ rfl
      simp [sub_eq_add_neg])
    ∀ a b c d : Surreal, Whole a → Whole b → Whole c → Whole d → a * b = c * d →
      ∃ e f g h : Surreal, Whole e ∧ Whole f ∧ Whole g ∧ Whole h ∧
        a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h := by
  intro Whole a b c d ha hb hc hd h
  have whole_iff (x : Surreal) : Whole x ↔ x.IsOmnific := by
    dsimp only [Whole]
    rw [← round_of_pos (x := x) (r := 1) zero_lt_one]
    exact ⟨fun h ↦ h.symm ▸ IsOmnific.round x, fun h ↦ h.eq.symm⟩
  let lift (x : Surreal) (hx : Whole x) : omnific :=
    ⟨x, mem_omnific_iff.mpr ((whole_iff x).mp hx)⟩
  obtain ⟨e, f, g, k, ha', hb', hc', hd'⟩ := omnific_refinement
    (show lift a ha * lift b hb = lift c hc * lift d hd from Subtype.ext h)
  have whole (x : omnific) : Whole (x : Surreal) := (whole_iff x).mpr (mem_omnific_iff.mp x.2)
  exact ⟨e, f, g, k, whole e, whole f, whole g, whole k, congrArg Subtype.val ha',
    congrArg Subtype.val hb', congrArg Subtype.val hc', congrArg Subtype.val hd'⟩

example {x : omnific} (hx : Irreducible x) : Prime x := hx.prime
