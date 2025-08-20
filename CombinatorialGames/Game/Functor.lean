/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Violeta Hernández Palacios, Yuyang Zhao
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Logic.Small.Set

/-!
# Game functor

The type of games `IGame` is an inductive type, with a single constructor `ofSets` taking in two
small sets of games and outputting a new game. This suggests the definition:

```
inductive IGame : Type (u + 1)
  | ofSets (s t : Set IGame) [Small.{u} s] [Small.{u} t] : IGame
```

However, the kernel does not accept this, as `Set IGame = IGame → Prop` contains a non-positive
occurence of `IGame` (see [counterexamples.org](https://counterexamples.org/strict-positivity.html)
for an explanation of what this is and why it's disallowed). We can get around this technical
limitation using the machinery of `QPF`s (quotients of polynomial functors). We define a functor
`GameFunctor` by

```
def GameFunctor (α : Type (u + 1)) : Type (u + 1) :=
  {s : Set α × Set α // Small.{u} s.1 ∧ Small.{u} s.2}
```

We can prove that this is a `QPF`, which then allows us to build its initial algebra through
`QPF.Fix`, which is exactly the inductive type `IGame`. As a bonus, we're able to describe the
coinductive type of loopy games `LGame` as the final coalgebra `QPF.Cofix` of the exact same
functor.
-/

universe u

/-- Either the Left or Right player. -/
@[aesop safe cases]
inductive Player where
  /-- The Left player. -/
  | left  : Player
  /-- The Right player. -/
  | right : Player
deriving DecidableEq

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
instance : Mul Player where
  mul := fun
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

/-- The functor from a type into the subtype of small pairs of sets in that type.

This is the quotient of a polynomial functor. The type `IGame` of well-founded games is defined as
the initial algebra of that `QPF`, while the type `LGame` of loopy games is defined as its final
coalgebra.

In other words, `IGame` and `LGame` have the following descriptions (which don't work verbatim due
to various Lean limitations):

```
inductive IGame : Type (u + 1)
  | ofSets (s t : Set IGame) [Small.{u} s] [Small.{u} t] : IGame

coinductive LGame : Type (u + 1)
  | ofSets (s t : Set LGame) [Small.{u} s] [Small.{u} t] : LGame
```
-/
def GameFunctor (α : Type (u + 1)) : Type (u + 1) :=
  {s : Player → Set α // ∀ p, Small.{u} (s p)}

namespace GameFunctor

@[ext] theorem ext {α : Type (u + 1)} {x y : GameFunctor α} : x.1 = y.1 → x = y := Subtype.ext

instance {α : Type (u + 1)} (x : GameFunctor α) (p : Player) : Small.{u} (x.1 p) := x.2 p

instance : Functor GameFunctor where
  map f s := ⟨(f '' s.1 ·), fun _ => inferInstance⟩

theorem map_def {α β} (f : α → β) (s : GameFunctor α) :
    f <$> s = ⟨(f '' s.1 ·), fun _ => inferInstance⟩ :=
  rfl

noncomputable instance : QPF GameFunctor where
  P := ⟨Player → Type u, fun x ↦ Σ p, PLift (x p)⟩
  abs x := ⟨fun p ↦ Set.range (x.2 ∘ .mk p ∘ PLift.up), fun _ ↦ inferInstance⟩
  repr x := ⟨fun p ↦ Shrink (x.1 p), Sigma.rec (fun _ y ↦ ((equivShrink _).symm y.1).1)⟩
  abs_repr x := by ext; simp [← (equivShrink _).exists_congr_right]
  abs_map f := by intro ⟨x, f⟩; ext; simp [PFunctor.map, map_def]

end GameFunctor
