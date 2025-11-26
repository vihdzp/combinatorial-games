/-
Copyright (c) 2025 Frantisek Silvasi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frantisek Silvasi
-/
import Lean.Elab.Tactic.Meta

/-!
# Eagerly add instances

Many definitions in game theory are hereditary. For instance, all options of a `Numeric` game are
`Numeric`, all options of an `Impartial` game are `Impartial`, etc.

The definition `addInstances` provides a tactic which will eagerly apply all passed functions to all
of the hypotheses, creating new ones in the process. The intended usage of this is to, for instance,
apply `Numeric.of_mem_moves` to all hypotheses, and thus build all possible `Numeric` instances.
-/

open Lean Elab Tactic

private def instances (constants : Array Name) (goal : MVarId) : MetaM (Option MVarId) := goal.withContext do
  let mut goal := goal
  for h in ←getLCtx do
    if h.isImplementationDetail then continue
    for c in constants do
      let ([goal'], _) ← runTactic goal (←`(tactic | try have := $(mkIdent c) $(mkIdent h.userName)))
        | logError "Applying {h.userName} to {c} must yield a single goal."; return .none
      goal := goal'
  return goal

/-- A tactic that eagerly adds instances by applying the functions in `constants` to every
hypothesis. -/
def addInstances (constants : Array Name) : TacticM Unit :=
  Lean.Elab.Tactic.liftMetaTactic1 (instances constants)
