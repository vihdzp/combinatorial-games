/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Coset.Basic

import Mathlib.Tactic.Ring.RingNF

/-!
# Multiplication of simplest surreal coset representatives

The gap from a surreal product to a Conway option is the product of the two signed gaps
from the factors to their options. This identity can certify a simplest coset representative
using presentations of the factors chosen for their gaps.
-/

universe u

public section

namespace Surreal

open IGame

/-- If the product of every pair of signed option gaps from two numeric games lies outside `H`,
the value of their product game is the simplest member of its coset modulo `H`. -/
theorem cosetRep_mk_mul_eq_of_forall_moves {H : AddSubgroup Surreal.{u}} [H.IsConvex]
    {x y : IGame.{u}} [x.Numeric] [y.Numeric]
    (h : ∀ (p : Player) (a : IGame.{u}) (ha : a ∈ x.moves p)
      (q : Player) (b : IGame.{u}) (hb : b ∈ y.moves q),
      (mk x - @mk a (.of_mem_moves ha)) * (mk y - @mk b (.of_mem_moves hb)) ∉ H) :
    cosetRep H (mk x * mk y) = mk x * mk y := by
  rw [← mk_mul]
  apply cosetRep_mk_eq_of_forall_moves (x * y)
  intro p c hc
  obtain ⟨q, a, ha, b, hb, rfl⟩ := exists_moves_mul.mp
    (show ∃ d ∈ (x * y).moves p, d = c from ⟨c, hc, rfl⟩)
  let : a.Numeric := .of_mem_moves ha
  let : b.Numeric := .of_mem_moves hb
  have hgap : mk (x * y) - mk (IGame.mulOption x y a b) = (mk x - mk a) * (mk y - mk b) := by
    simp only [IGame.mulOption, mk_sub, mk_mul, mk_add]
    ring
  rw [hgap]
  exact h q a ha _ b hb

/-- If multiplying elements outside `H` and `K` gives elements outside `L`, then multiplying
simplest representatives modulo `H` and `K` gives a simplest representative modulo `L`. -/
theorem cosetRep_mul_eq_of_mul_notMem {H K L : AddSubgroup Surreal.{u}}
    [H.IsConvex] [K.IsConvex] [L.IsConvex] {x y : Surreal.{u}}
    (hx : cosetRep H x = x) (hy : cosetRep K y = y)
    (h : ∀ ⦃a b : Surreal.{u}⦄, a ∉ H → b ∉ K → a * b ∉ L) :
    cosetRep L (x * y) = x * y := by
  obtain ⟨x, _, rfl, hbx⟩ := birthday_eq_iGameBirthday x
  obtain ⟨y, _, rfl, hby⟩ := birthday_eq_iGameBirthday y
  apply cosetRep_mk_mul_eq_of_forall_moves
  intro p a ha q b hb
  exact h ((cosetRep_mk_eq_iff_forall_moves hbx).mp hx p a ha)
    ((cosetRep_mk_eq_iff_forall_moves hby).mp hy q b hb)

end Surreal
