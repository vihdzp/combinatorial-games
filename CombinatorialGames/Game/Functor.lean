/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Violeta Hernández Palacios
-/
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
occurence of `IGame` (meaning that it appears to the left of an arrow). We can get around this
technical limitation using the machinery of `QPF`s (quotients of polynomial functors). We define a
functor `GameFunctor` by

```
def GameFunctor : Type (u + 1) → Type (u + 1) :=
  fun α => {s : Set α × Set α // Small.{u} s.1 ∧ Small.{u} s.2}
```

We can prove that this is a `QPF`, which then allows us to build its initial algebra through
`QPF.Fix`, which is exactly the inductive type `IGame`. As a bonus, we're able to describe the
coinductive type of loopy games `LGame` as the cofinal algebra `QPF.Cofix` of the exact same
functor.
-/

universe u

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
def GameFunctor : Type (u + 1) → Type (u + 1) :=
  fun α => {s : Set α × Set α // Small.{u} s.1 ∧ Small.{u} s.2}

namespace GameFunctor

@[ext] theorem ext {α : Type (u + 1)} {x y : GameFunctor α} : x.1 = y.1 → x = y := Subtype.ext

instance {α : Type (u + 1)} (x : GameFunctor α) : Small.{u} x.1.1 := x.2.1
instance {α : Type (u + 1)} (x : GameFunctor α) : Small.{u} x.1.2 := x.2.2

instance : Functor GameFunctor where
  map f s := ⟨⟨f '' s.1.1, f '' s.1.2⟩, ⟨inferInstance, inferInstance⟩⟩

theorem map_def {α β} (f : α → β) (s : GameFunctor α) :
    f <$> s = ⟨⟨f '' s.1.1, f '' s.1.2⟩, ⟨inferInstance, inferInstance⟩⟩ :=
  rfl

noncomputable instance : QPF GameFunctor where
  P := ⟨Type u × Type u, fun x ↦ PLift x.1 ⊕ PLift x.2⟩
  abs x := ⟨⟨Set.range (x.2 ∘ .inl ∘ PLift.up), Set.range (x.2 ∘ .inr ∘ PLift.up)⟩,
    ⟨inferInstance, inferInstance⟩⟩
  repr x := ⟨⟨Shrink x.1.1, Shrink x.1.2⟩,
    Sum.rec (fun y ↦ ((equivShrink _).symm y.1).1) (fun y ↦ ((equivShrink _).symm y.1).1)⟩
  abs_repr x := by ext <;> simp [← (equivShrink _).exists_congr_right]
  abs_map f := by intro ⟨x, f⟩; ext <;> simp [PFunctor.map, map_def]
end GameFunctor
