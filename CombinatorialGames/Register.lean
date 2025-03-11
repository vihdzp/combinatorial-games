/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
We register a `simp` attribute for the `game_cmp` tactic. This needs to be done in a separate file
to where the tactic is defined.
-/

/-- Simp attribute for lemmas used in `game_cmp`. -/
register_simp_attr game_cmp
