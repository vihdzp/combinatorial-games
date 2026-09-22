/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.NatOrdinal.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Topology on ordinals

We endow `NatOrdinal` and `WithTop NatOrdinal` with the order topology.
-/

public section

instance : TopologicalSpace NatOrdinal := Preorder.topology _
instance : OrderTopology NatOrdinal := ⟨rfl⟩
instance : TopologicalSpace (WithTop NatOrdinal) := Preorder.topology _
instance : OrderTopology (WithTop NatOrdinal) := ⟨rfl⟩

end
