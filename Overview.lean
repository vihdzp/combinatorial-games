/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Daniel Weber
-/
module

import CombinatorialGames
import Mathlib.Tactic.Recall
import Mathlib.FieldTheory.IsRealClosed.Basic

/-!
# Repository overview

This file serves as an exposition of the various types and results that are covered within the
repository, as well as results that are wanted or being worked on.
-/

universe u v

set_option linter.unusedVariables false

/-! ### Games -/

/-! #### Basic types -/

/-! ##### IGame -/

/- The type of well-founded games. -/
recall IGame : Type _

/- Build a game from its left and right sets. -/
recall IGame.instOfSets : OfSets IGame _

/- The order instance on `IGame`, defined inductively. -/
recall IGame.instPreorder : Preorder IGame

/- Disjoint sum of games. -/
recall IGame.instAdd : Add IGame

/- Product of games, in the sense used for defining surreal multiplication. -/
recall IGame.instMul : Mul IGame

/-! ##### LGame -/

/- The type of loopy or non-well-founded games. -/
recall LGame : Type _

/- Build a loopy game from its left and right sets. -/
recall LGame.instOfSets : OfSets LGame _

/- The corecursor on loopy games, i.e. build a game from its graph. -/
recall LGame.corec {α : Type v} (mov : Player → α → Set α)
    [∀ a, Small.{u} (mov .left a)] [∀ a, Small.{u} (mov .right a)] (init : α) : LGame.{u}

/- Disjoint sum of games. -/
recall LGame.instAdd : Add LGame

/- Product of games, in the sense used for defining surreal multiplication. -/
recall LGame.instMul : Mul LGame

/-! ##### Game -/

/- The quotient of `IGame` by antisymmetry. This is an abelian group, and what many references often
refer to as simply "a game". -/
recall Game : Type _

/- The quotient map `IGame → Game`. -/
recall Game.mk : IGame → Game

/- Addition on `IGame` can be lifted to the quotient. -/
recall Game.instAdd : Add Game

/- But multiplication cannot! -/
recall IGame.mul_not_lift : ∃ x₁ x₂ y : IGame, x₁ ≈ x₂ ∧ ¬x₁ * y ≈ x₂ * y

/- `Game` is an abelian group (with a one). -/
recall Game.instAddCommGroupWithOne : AddCommGroupWithOne Game

/-! #### Basic games -/

/- The game `0 = { | }`. -/
recall IGame.instZero : Zero IGame

/- The game `1 = {0 | }`. -/
recall IGame.instOne : One IGame

/- The game `⋆ = {0 | 0}`. -/
recall IGame.star : IGame

/- The game `↑ = {0 | ⋆}`. -/
recall IGame.up : IGame

/- The game `↓ = {⋆ | 0}`. -/
recall IGame.down : IGame

/- The game `⧾x = {0 | {0 | -x}}`. -/
recall IGame.tiny : IGame → IGame

/- The game `⧿x = {{x | 0} | 0}`. -/
recall IGame.miny : IGame → IGame

/-! #### Specific games -/

/-! ##### Nim -/

/- A single Nim heap. -/
recall IGame.nim : Nimber → IGame

/- Nim is an impartial game. -/
recall IGame.Impartial.nim (x : Nimber) : (IGame.nim x).Impartial

/- The **Sprague-Grundy theorem**, which states every impartial game is
equivalent to a game of Nim. -/
recall IGame.Impartial.nim_grundy_equiv (x : IGame) [x.Impartial] :
    IGame.nim (IGame.Impartial.grundy x) ≈ x

/-! ##### Domineering -/

/- We have a definition of Domineering. -/
recall IGame.Domineering

-- We don't currently have any substantial theory on Domineering, or on any other "playable"
-- combinatorial game. Help welcome!

/-! ### Surreals -/

/- The type of surreal numbers, defined as a subquotient of `IGame`. -/
recall Surreal : Type _

/-! #### Field structure -/

/- Addition on `IGame` can be lifted to `Surreal`, giving it the structure of an abelian group. -/
recall Surreal.instAddCommGroupWithOne

/- Multiplication on `IGame` can also be lifted to `Surreal`, giving it a ring structure. Proving
this requires a very convoluted inductive argument. -/
recall Surreal.instCommRing : CommRing Surreal

/- Finally, through another inductive argument, it's possible to give a "genetic" definition of the
multiplicative inverse, making the surreals into a field. -/
recall Surreal.instField : Field Surreal

/- The fact that surreals are real-closed is a corollary of two results:

- Surreals are isomorphic as a field to a (sub)type of Hahn series.
- For `R` real-closed and `Γ` a divisible group, `R⟦Γ⟧` is also real-closed.

As of this writing, both are missing in their respective repositories. -/
proof_wanted Surreal.instIsRealClosed : IsRealClosed Surreal

/-! #### Important surreal functions -/

recall Real.toSurreal

/-! #### Sign expansions -/

recall SignExpansion : Type _

/-! ### Nimbers -/

/-! #### The simplest extension theorems -/

recall Nimber.exists_add_of_not_isGroup

/- As a consequence of the fourth simplest extension theorem, the nimbers are algebraically closed. -/
recall Nimber.instIsAlgClosed
