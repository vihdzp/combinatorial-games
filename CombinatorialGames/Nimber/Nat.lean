import CombinatorialGames.Nimber.Basic

alias! /-- The natural numbers, endowed with nim operations. -/ NatNimber Nat

namespace NatNimber

instance : LinearOrder NatNimber := Nat.instLinearOrder

instance : Lean.ToExpr NatNimber where
  toExpr x := .app (.const `NatNimber.of []) (Lean.toExpr x.val)
  toTypeExpr := .const `NatNimber []

instance : ToString NatNimber where
  toString x := "∗" ++ x.val.repr

@[simp] theorem lt_one_iff_zero {a : NatNimber} : a < 1 ↔ a = 0 := Nat.lt_one_iff
@[simp] theorem one_le_iff_ne_zero {a : NatNimber} : 1 ≤ a ↔ a ≠ 0 := Nat.one_le_iff_ne_zero
theorem le_one_iff {a : NatNimber} : a ≤ 1 ↔ a = 0 ∨ a = 1 := Nat.le_one_iff_eq_zero_or_eq_one

/-- The embedding `NatNimber ↪o Nimber`. -/
def toNimber : NatNimber ↪o Nimber where
  toFun x := .of x.val
  inj' x y := by simp
  map_rel_iff' := by simp

@[simp] theorem toNimber_zero : toNimber 0 = 0 := rfl
@[simp] theorem toNimber_one : toNimber 1 = 1 := by simp [toNimber]
@[simp] theorem toNimber_of (n : ℕ) : toNimber (of n) = Nimber.of n := rfl

instance : Add NatNimber where
  add m n := of (m.val ^^^ n.val)

@[simp]
theorem toNimber_add (x y : NatNimber) : toNimber (x + y) = .of x.val + .of y.val :=
  (Nimber.add_nat ..).symm

/-- Multiplies `x` by `∗2 ^ (2 ^ t - 1)`, whenever `x < ∗2 ^ 2 ^ t`. This is a subroutine needed to
multiply two general nimbers. This makes use of the formula:

$$(a2^{2^t}+b)2^{2^{t+1}-1} = (a2^{2^t-1})2^{2^t-1}+((a+b)2^{2^t-1})2^{2^t}$$

for $a, b < \ast 2 ^ {2 ^ t}$. -/
private def mulHalf (t : ℕ) (x : NatNimber) : NatNimber :=
  match t with
  | 0 => x
  | t + 1 =>
    let a := of (x.val / 2 ^ 2 ^ t)
    let b := of (x.val % 2 ^ 2 ^ t)
    of ((mulHalf t (a + b)).val * 2 ^ 2 ^ t) + mulHalf t (mulHalf t a)

/-- Multiplies `x` by `y`, whenever `x, y < ∗2 ^ 2 ^ t`. This makes use of the formula:

$$(a2^{2^t}+b)(c2^{2^t}+d)=(ac)2^{2^t-1}+(ac+ad+bc)2^{2^t}+bd$$

for $a, b, c, d < \ast 2 ^ {2 ^ t}$.-/
private def mul (t : ℕ) (x y : NatNimber) : NatNimber :=
  match t with
  | 0 => if x = 0 then 0 else if y = 0 then 0 else 1
  | t + 1 =>
    let a := of (x.val / 2 ^ 2 ^ t)
    let b := of (x.val % 2 ^ 2 ^ t)
    let c := of (y.val / 2 ^ 2 ^ t)
    let d := of (y.val % 2 ^ 2 ^ t)
    let z := mul t a c
    mulHalf t z + of ((z + mul t a d + mul t b c).val * 2 ^ 2 ^ t) + mul t b d

private def log2_with_fuel (n fuel : ℕ) : ℕ :=
  if n < 2 then 0 else match fuel with
  | 0 => unreachable!
  | fuel + 1 => log2_with_fuel (n / 2) fuel + 1

private theorem log2_with_fuel_of_lt_two {n fuel : ℕ} (h : n < 2) : log2_with_fuel n fuel = 0 := by
  rw [log2_with_fuel.eq_def, if_pos h]

private theorem log2_with_fuel_add_two {n fuel : ℕ} :
    log2_with_fuel (n + 2) (fuel + 1) = log2_with_fuel ((n + 2) / 2) fuel + 1 := by
  rw [log2_with_fuel.eq_def, if_neg]
  exact Nat.not_lt.2 (Nat.le_add_left 2 n)

private theorem log2_with_fuel_of_le {n fuel : ℕ} (h : n ≤ fuel) :
    log2_with_fuel n fuel = log2_with_fuel n n :=
  match n with
  | 0 | 1 => by rw [log2_with_fuel_of_lt_two (by decide), log2_with_fuel_of_lt_two (by decide)]
  | n + 2 => by
    match fuel with
    | 0 => contradiction
    | fuel + 1 =>
      rw [log2_with_fuel_add_two, log2_with_fuel_add_two,
        log2_with_fuel_of_le, log2_with_fuel_of_le (fuel := n + 1)]
      · sorry
      · sorry

/--
Base-two logarithm of natural numbers. Returns `⌊max 0 (log₂ n)⌋`.

This function is overridden at runtime with an efficient implementation. This definition is
the logical model.

Examples:
 * `Nat.log2 0 = 0`
 * `Nat.log2 1 = 0`
 * `Nat.log2 2 = 1`
 * `Nat.log2 4 = 2`
 * `Nat.log2 7 = 2`
 * `Nat.log2 8 = 3`
-/
@[extern "lean_nat_log2"]
def log2 (n : @& Nat) : Nat :=
  log2_with_fuel n n

theorem log2_def (n : Nat) : log2 n = if n < 2 then 0 else log2 (n / 2) + 1 :=
  match n with
  | 0 | 1 => rfl
  | n + 2 => by
    rw [log2, log2_with_fuel_add_two, if_neg, log2_with_fuel_of_le]
    · rfl
    · sorry
    · exact Nat.not_lt.2 (Nat.le_add_left 2 n)





private def log2 (n : ℕ) : ℕ :=
  log2_with_fuel n n

#exit
-- TODO: prove correctness
instance : Mul NatNimber where
  mul x y := mul (max (log2 (log2 x.val)) (log2 (log2 y.val)) + 1) x y

end NatNimber

example : Nimber.of 3 + Nimber.of 5 = Nimber.of 6 := by
  have : NatNimber.of 3 + NatNimber.of 5 = NatNimber.of 6 := by decide
  apply_fun NatNimber.toNimber at this
  simpa
