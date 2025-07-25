/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/

import Mathlib.Order.Defs.PartialOrder
import Batteries.Tactic.Init

inductive PlayerOutcome where
  /-- Left wins going first -/
  | L
  /-- Right wins going first -/
  | R

def PlayerOutcome.Conjugate : PlayerOutcome → PlayerOutcome
  | .L => .R
  | .R => .L

@[simp]
theorem PlayerOutcome.eq_iff_conjugate_eq {a b : PlayerOutcome} :
    (a.Conjugate = b.Conjugate) ↔ (a = b) := by
  cases a <;> cases b <;> simp only [reduceCtorEq, PlayerOutcome.Conjugate]

@[simp]
theorem PlayerOutcome.conjugate_conjugate_eq_self {o : PlayerOutcome} :
    o.Conjugate.Conjugate = o := by
  cases o <;> exact rfl

inductive Outcome where
  /-- Left wins -/
  | L
  /-- Next player wins -/
  | N
  /-- Previous (second) player wins -/
  | P
  /-- Right wins -/
  | R

/--
Game outcomes are ordered in favour of Left player (see Hasse diagram)

```
  L
 / \
N   P
 \ /
  R
```
-/
instance : LT Outcome where
  lt lhs rhs :=
    (lhs ≠ Outcome.L ∧ rhs = Outcome.L) ∨
    (lhs = Outcome.R ∧ rhs = Outcome.N) ∨
    (lhs = Outcome.R ∧ rhs = Outcome.P)

instance : LE Outcome where
  le lhs rhs := (lhs = rhs) ∨ (lhs < rhs)

instance : Preorder Outcome where
  le_refl _ := Or.inl rfl
  le_trans a b c _ _ := by
    cases a <;> cases b <;> cases c <;> simp [LE.le, LT.lt] at *
  lt_iff_le_not_ge a b := by
    cases a <;> cases b <;> simp [LE.le, LT.lt] at *

instance : PartialOrder Outcome where
  le_antisymm a b _ _ := by
    cases a <;> cases b <;> simp [LE.le, LT.lt] at *

def PlayerOutcomesToGameOutcome : PlayerOutcome → PlayerOutcome → Outcome
  | PlayerOutcome.L, PlayerOutcome.L => Outcome.L
  | PlayerOutcome.R, PlayerOutcome.R => Outcome.R
  | PlayerOutcome.R, PlayerOutcome.L => Outcome.P
  | PlayerOutcome.L, PlayerOutcome.R => Outcome.N

@[simp]
theorem Outcome.ge_R (o : Outcome) : o ≥ Outcome.R := by
  simp only [ge_iff_le]
  unfold LE.le
  cases o <;> simp [instLEOutcome, LT.lt]

@[simp]
theorem Outcome.L_ge (o : Outcome) : Outcome.L ≥ o := by
  simp only [ge_iff_le]
  unfold LE.le
  cases o <;> simp [instLEOutcome, LT.lt]

@[simp]
theorem Outcome.ge_P_ge_N_eq_L {o : Outcome} (hp : o ≥ Outcome.P) (hn : o ≥ Outcome.N)
    : o = Outcome.L := by
  cases o <;> simp [LE.le, LT.lt, LE.le] at *

def Outcome.Conjugate : Outcome → Outcome
  | .L => .R
  | .R => .L
  | .P => .P
  | .N => .N

theorem Outcome.conjugate_conjugate_eq_self {o : Outcome} : o.Conjugate.Conjugate = o := by
  cases o <;> rfl

theorem Outcome.outcome_ge_conjugate_le {x y : Outcome} (h1 : x ≥ y) : x.Conjugate ≤ y.Conjugate := by
  cases h2 : x
    <;> cases h3 : y
    <;> unfold Outcome.Conjugate
    <;> simp only [LE.le, LT.lt, and_false, and_self, and_true, ne_eq, not_false_eq_true,
                   not_true_eq_false, or_self, reduceCtorEq, or_false, or_true]
    <;> simp only [h2, h3, ge_iff_le] at h1
    <;> absurd h1
    <;> simp only [LE.le, LT.lt, and_false, and_self, and_true, ne_eq, not_false_eq_true,
                   not_true_eq_false, or_self, reduceCtorEq]
