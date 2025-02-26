/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.Antisymmetrization

variable {α : Type*} {a b : α} {r : α → α → Prop}

theorem AntisymmRel.of_eq [IsRefl α r] (h : a = b) : AntisymmRel r a b :=
  h ▸ .rfl
