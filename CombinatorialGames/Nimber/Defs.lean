/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Tactic.OrdinalAlias
import CombinatorialGames.Tactic.Register

/-!
# Nimbers

This file does nothing but define `Nimber` as a type alias of `Ordinal`. The file
`CombinatorialGames.Game.Impartial.Grundy` sets up Grundy values using this alias, but without
defining any of the arithmetic on nimbers. The files `CombinatorialGames.Nimber.Basic` and
`CombinatorialGames.Nimber.Field` then set up the group and field structure on nimbers respectively.
-/

ordinal_alias!
  /-- A type synonym for ordinals with nimber addition and multiplication. -/ Nimber

namespace Nimber

attribute [game_cmp] of_zero of_one

@[inherit_doc] scoped prefix:75 "∗" => of
recommended_spelling "of" for "∗" in [Nimber.«term∗_»]
