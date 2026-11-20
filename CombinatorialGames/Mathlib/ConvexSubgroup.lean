/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Order.Interval.Set.Defs

import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.TypeStar

/-!
# Convex additive subgroups

An additive subgroup of an ordered group is convex if its carrier is order-connected.
-/

public section

namespace AddSubgroup

variable {G : Type*} [AddGroup G] [Preorder G]

/-- A subgroup of an ordered group is convex when it is order-connected. -/
class IsConvex (H : AddSubgroup G) : Prop where
  /-- The carrier of a convex subgroup is order-connected. -/
  ordConnected : (H : Set G).OrdConnected

/-- A nonnegative element below an element of a convex subgroup lies in the subgroup. -/
theorem mem_of_nonneg_of_le (H : AddSubgroup G) [H.IsConvex] {x y : G} (hx : 0 ≤ x)
    (hxy : x ≤ y) (hy : y ∈ H) : x ∈ H :=
  IsConvex.ordConnected.out H.zero_mem hy ⟨hx, hxy⟩

end AddSubgroup
