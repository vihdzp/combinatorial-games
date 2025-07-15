/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Order.Filter.AtTopBot.Defs
import CombinatorialGames.SignExpansion.Basic
import Mathlib.Order.Atoms

/-!
# Small sign expansions

A sign expansion is *small* if it is eventually constant. All terminating sign expansions are small.
-/

universe u
noncomputable section
namespace SignExpansion
open Order

def IsSmall (e : SignExpansion.{u}) : Prop :=
  IsAtom (Filter.map e Filter.atTop)
