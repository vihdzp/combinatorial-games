/-
Copyright (c) 2026 Dan Abramov, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Surreal.Birthday.Basic

/-!
# Simplicity of surreal numbers

Every nonempty order-connected set has a unique member of least birthday.
-/

universe u

public section

namespace Surreal

open Set

/-- A nonempty order-connected set has a unique surreal of least birthday. -/
theorem existsUnique_min_birthday {s : Set Surreal.{u}} (hne : s.Nonempty) (hc : s.OrdConnected) :
    ∃! x : Surreal.{u}, x ∈ s ∧ ∀ y ∈ s, x.birthday ≤ y.birthday := by
  obtain ⟨x, hx⟩ := exists_minimalFor_of_wellFoundedLT (· ∈ s) birthday hne
  refine ⟨x, ⟨hx.prop, fun _ hy ↦ hx.le hy⟩, ?_⟩
  rintro y ⟨hy, hymin⟩
  have h := le_antisymm (hymin x hx.prop) (hx.le hy)
  have no_lt {a b : Surreal} (ha : a ∈ s) (hb : b ∈ s)
      (hab : a < b) (ha' : a.birthday = x.birthday) (hb' : b.birthday = x.birthday) : False := by
    have hs : ∀ p ∈ ({a} : Set Surreal), ∀ q ∈ ({b} : Set Surreal), p < q := by
      simpa using hab
    have hl := lt_ofSets_of_mem_left (t := {b}) (H := hs) (mem_singleton a)
    have hr := ofSets_lt_of_mem_right (s := {a}) (H := hs) (mem_singleton b)
    exact (birthday_ofSets_singleton_lt_of_birthday_eq ha' hb' hab).not_ge
      (hx.le (hc.out ha hb ⟨hl.le, hr.le⟩))
  rcases lt_trichotomy y x with hyx | hyx | hxy
  · exact (no_lt hy hx.prop hyx h rfl).elim
  · exact hyx
  · exact (no_lt hx.prop hy hxy rfl h).elim

end Surreal
