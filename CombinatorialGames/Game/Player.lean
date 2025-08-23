/-
Copyright (c) 2025 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Logic.Small.Defs

/-!
# Type of players

This file implements the two-element type of players (`Left`, `Right`), alongside other basic
notational machinery to be used within game theory.
-/

universe u

/-! ### Players -/

/-- Either the Left or Right player. -/
@[aesop safe cases]
inductive Player where
  /-- The Left player. -/
  | left  : Player
  /-- The Right player. -/
  | right : Player
deriving DecidableEq, Inhabited

namespace Player

/-- Specify a function `Player → α` from its two outputs. -/
@[simp]
abbrev cases {α : Sort*} (l r : α) : Player → α
  | left => l
  | right => r

lemma apply_cases {α β : Sort*} (f : α → β) (l r : α) (p : Player) :
    f (cases l r p) = cases (f l) (f r) p := by
  cases p <;> rfl

@[simp]
theorem cases_inj {α : Sort*} {l₁ r₁ l₂ r₂ : α} :
    cases l₁ r₁ = cases l₂ r₂ ↔ l₁ = l₂ ∧ r₁ = r₂ :=
  ⟨fun h ↦ ⟨congr($h left), congr($h right)⟩, fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ rfl⟩

instance : Fintype Player where
  elems := {left, right}
  complete := by aesop

@[simp]
protected lemma «forall» {p : Player → Prop} :
    (∀ x, p x) ↔ p left ∧ p right :=
  ⟨fun h ↦ ⟨h left, h right⟩, fun ⟨hl, hr⟩ ↦ fun | left => hl | right => hr⟩

@[simp]
protected lemma «exists» {p : Player → Prop} :
    (∃ x, p x) ↔ p left ∨ p right :=
  ⟨fun | ⟨left, h⟩ => .inl h | ⟨right, h⟩ => .inr h, fun | .inl h | .inr h => ⟨_, h⟩⟩

instance : Neg Player where
  neg := cases right left

@[simp] lemma neg_left : -left = right := rfl
@[simp] lemma neg_right : -right = left := rfl

instance : InvolutiveNeg Player where
  neg_neg := by decide

/--
The multiplication of `Player`s is used to state the lemmas about the multiplication of
combinatorial games, such as `IGame.mulOption_mem_moves_mul`.
-/
instance : Mul Player where mul
  | left, p => p
  | right, p => -p

@[simp] lemma left_mul (p : Player) : left * p = p := rfl
@[simp] lemma right_mul (p : Player) : right * p = -p := rfl
@[simp] lemma mul_left : ∀ p, p * left = p := by decide
@[simp] lemma mul_right : ∀ p, p * right = -p := by decide
@[simp] lemma mul_self : ∀ p, p * p = left := by decide

instance : HasDistribNeg Player where
  neg_mul := by decide
  mul_neg := by decide

instance : CommGroup Player where
  one := left
  inv := id
  mul_assoc := by decide
  mul_comm := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

@[simp] lemma one_eq_left : 1 = left := rfl
@[simp] lemma inv_eq_self (p : Player) : p⁻¹ = p := rfl

end Player

open Player

/-! ### OfSets -/

/-- Typeclass for the `ofSets` operation. Used to implement the `!{st}` and `!{s | t}` syntax. -/
class OfSets (α : Type (u + 1)) (Valid : outParam ((Player → Set α) → Prop)) where
  /-- Construct a combinatorial game from its left and right sets. -/
  ofSets (st : Player → Set α) (h : Valid st) [Small.{u} (st left)] [Small.{u} (st right)] : α
export OfSets (ofSets)

@[inherit_doc OfSets.ofSets]
macro "!{" st:term "}'" h:term:max : term => `(OfSets.ofSets $st $h)

@[inherit_doc OfSets.ofSets]
macro "!{" s:term " | " t:term "}'" h:term:max : term => `(!{Player.cases $s $t}'$h)

macro "of_sets_tactic" : tactic =>
  `(tactic| first
    | done
    | trivial
    | assumption
    | aesop
    | fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
where `h` is a proof that sets are valid"
   )

@[inherit_doc OfSets.ofSets]
macro:max "!{" st:term "}" : term => `(!{$st}'(by of_sets_tactic))

@[inherit_doc OfSets.ofSets]
macro:max "!{" s:term " | " t:term "}" : term => `(!{$s | $t}'(by of_sets_tactic))

recommended_spelling "ofSets" for "!{st}'h" in [ofSets, «term!{_}'_»]
recommended_spelling "ofSets" for "!{s | t}'h" in [ofSets, «term!{_|_}'_»]
recommended_spelling "ofSets" for "!{st}" in [ofSets, «term!{_}»]
recommended_spelling "ofSets" for "!{s | t}" in [ofSets, «term!{_|_}»]

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab OfSets.ofSets]
def delabOfSets : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity' ``OfSets.ofSets 7
  withNaryArg 3 do
    let e ← getExpr
    if e.isAppOfArity' ``Player.cases 3 then
      let s ← withNaryArg 1 delab
      let t ← withNaryArg 2 delab
      `(!{$s | $t})
    else
      let st ← delab
      `(!{$st})

theorem ofSets_eq_ofSets_cases {α} {Valid : (Player → Set α) → Prop} [OfSets α Valid]
    (st : Player → Set α) (h : Valid st) [Small (st left)] [Small (st right)] :
    !{st} = !{st left | st right}'(by convert h; aesop) := by
  congr; ext1 p; cases p <;> rfl

/-! ### Moves -/

/-- Typeclass for the `moves` operation. Used to implement the `xᴸ` and `xᴿ` syntax. -/
class Moves (α : Type*) where
  /-- Either the set of left or right moves of a game. -/
  moves : Player → α → Set α
export Moves (moves)

/-- The set of left moves of the game. -/
postfix:max "ᴸ" => Moves.moves left
recommended_spelling "moves_left" for "ᴸ" in [«term_ᴸ»]

/-- The set of right moves of the game. -/
postfix:max "ᴿ" => Moves.moves right
recommended_spelling "moves_right" for "ᴿ" in [«term_ᴿ»]

open Lean PrettyPrinter Delaborator SubExpr in
@[app_delab Moves.moves]
def delabMoves : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity' ``Moves.moves 4
  let x ← withNaryArg 3 delab
  withNaryArg 2 do
    let p ← getExpr
    if p.isAppOf ``Player.left then `($xᴸ)
    else if p.isAppOf ``Player.right then `($xᴿ)
    else failure -- fail over to the default delaborator
