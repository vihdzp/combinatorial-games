/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Loopy.IGame
import CombinatorialGames.Game.Impartial.Basic

/-!
# Combinatorial games from a type of states

In the literature, mathematicians often describe games as graphs, consisting of a set of states, as
well as move relations for the left and right players. We define two typeclasses to facilitate this
conversion: `ConcreteLGame`, which takes a graph and turns it into a potentially loopy game, and
`ConcreteIGame`, which enforces well-foundedness. We then define functions turning these into our
standard types `IGame` and `LGame`.

For simplicity, we put results on both concrete `IGame`s and `LGame`s in the common namespace
`ConcreteGame`.

Mathematically, `ConcreteGame.toLGame` is nothing but the corecursor on loopy games, while
`ConcreteGame.toIGame` is defined inductively.
-/

universe u v

noncomputable section

open IGame Set

variable {α : Type*}

/-- A "concrete" game is a type of states endowed with well-founded move relations for the
left and right players.

This typeclass allows for loopy games, see `ConcreteIGame` for a typeclass enforcing
well-foundedness. -/
class ConcreteLGame (α : Type v) where
  /-- The set of options for the left player. -/
  leftMoves : α → Set α
  /-- The set of options for the right player. -/
  rightMoves : α → Set α
  /-- To make a game in universe `u`, the set of left moves must be u-small. -/
  small_leftMoves (a : α) : Small.{u} (leftMoves a) := by infer_instance
  /-- To make a game in universe `u`, the set of left moves must be u-small. -/
  small_rightMoves (a : α) : Small.{u} (rightMoves a) := by infer_instance

@[inherit_doc ConcreteLGame.leftMoves]
def ConcreteGame.leftMoves [ConcreteLGame α] (a : α) :=
  ConcreteLGame.leftMoves a

@[inherit_doc ConcreteLGame.rightMoves]
def ConcreteGame.rightMoves [ConcreteLGame α] (a : α) :=
  ConcreteLGame.rightMoves a

/-- `IsOption x y` means that `x` is either a left or a right move for `y`. -/
@[aesop simp]
def ConcreteGame.IsOption [ConcreteLGame α] (a b : α) : Prop :=
  a ∈ ConcreteGame.leftMoves b ∪ ConcreteGame.rightMoves b

/-- A "concrete" game is a type of states endowed with well-founded move relations for the
left and right players.

This typeclass allows only for well-founded games, see `ConcreteLGame` for a typeclass allowing
loopy games. -/
class ConcreteIGame (α : Type v) extends ConcreteLGame.{u} α where
  /-- The option relation in the game is well-founded. -/
  isWellFounded_isOption : IsWellFounded α ConcreteGame.IsOption

/-! ### Loopy games -/

/-- Create a `ConcreteLGame` from a single function used for the left and right moves. -/
def ConcreteLGame.ofImpartial (moves : α → Set α) [∀ x, Small.{u} (moves x)] : ConcreteLGame α where
  leftMoves := moves
  rightMoves := moves

/-- Create a `ConcreteIGame` from a single function used for the left and right moves. -/
def ConcreteIGame.ofImpartial (moves : α → Set α) [∀ x, Small.{u} (moves x)]
    [H : IsWellFounded α fun a b ↦ a ∈ moves b] : ConcreteIGame α where
  isWellFounded_isOption := by
    convert H using 1
    ext
    exact or_self_iff
  __ := ConcreteLGame.ofImpartial moves

namespace ConcreteGame
section ConcreteLGame
variable [ConcreteLGame.{u} α]

theorem IsOption.of_mem_leftMoves {x y : α} : x ∈ leftMoves y → IsOption x y := .inl
theorem IsOption.of_mem_rightMoves {x y : α} : x ∈ rightMoves y → IsOption x y := .inr

instance (a : α) : Small.{u} (leftMoves a) := ConcreteLGame.small_leftMoves a
instance (a : α) : Small.{u} (rightMoves a) := ConcreteLGame.small_rightMoves a
instance (a : α) : Small.{u} {b // IsOption b a} :=
  inferInstanceAs (Small (leftMoves a ∪ rightMoves a :))

/-- Turns a state of a `ConcreteLGame` into an `LGame`. -/
def toLGame (a : α) : LGame :=
  .corec leftMoves rightMoves a

@[simp]
theorem leftMoves_toLGame (a : α) : (toLGame a).leftMoves = toLGame '' leftMoves a :=
  LGame.leftMoves_corec ..

@[simp]
theorem rightMoves_toLGame (a : α) : (toLGame a).rightMoves = toLGame '' rightMoves a :=
  LGame.rightMoves_corec ..

theorem mem_leftMoves_toLGame_of_mem {a b : α} (hab : b ∈ leftMoves a) :
    toLGame b ∈ (toLGame a).leftMoves := by
  rw [leftMoves_toLGame]
  exact ⟨b, hab, rfl⟩

theorem mem_rightMoves_toLGame_of_mem {a b : α} (hab : b ∈ rightMoves a) :
    toLGame b ∈ (toLGame a).rightMoves := by
  rw [rightMoves_toLGame]
  exact ⟨b, hab, rfl⟩

theorem neg_toLGame (h : leftMoves (α := α) = rightMoves) (a : α) : -toLGame a = toLGame a := by
  simp_rw [toLGame, LGame.neg_corec_apply, h]

end ConcreteLGame

/-! ### Well-founded games -/

section ConcreteIGame
variable [ConcreteIGame.{u} α]

open ConcreteLGame

instance : IsWellFounded α IsOption :=
  ConcreteIGame.isWellFounded_isOption

theorem isOption_wf : @WellFounded α IsOption :=
  IsWellFounded.wf

/-- **Conway recursion**: build data for a game by recursively building it on its
left and right sets. -/
def moveRecOn {motive : α → Sort*} (x)
    (mk : Π x : α, (Π y ∈ leftMoves x, motive y) → (Π y ∈ rightMoves x, motive y) → motive x) :
    motive x :=
  isOption_wf.recursion x fun x IH ↦
    mk x (fun _ h ↦ IH _ (.of_mem_leftMoves h)) (fun _ h ↦ IH _ (.of_mem_rightMoves h))

/-- Turns a state of a `ConcreteIGame` into an `IGame`. -/
def toIGame (a : α) : IGame :=
  {.range fun b : leftMoves a ↦ toIGame b | .range fun b : rightMoves a ↦ toIGame b}ᴵ
termination_by isOption_wf.wrap a
decreasing_by all_goals aesop

@[simp]
theorem leftMoves_toIGame (a : α) : (toIGame a).leftMoves = toIGame '' leftMoves a := by
  rw [toIGame, leftMoves_ofSets, image_eq_range]

@[simp]
theorem rightMoves_toIGame (a : α) : (toIGame a).rightMoves = toIGame '' rightMoves a := by
  rw [toIGame, rightMoves_ofSets, image_eq_range]

theorem mem_leftMoves_toIGame_of_mem {a b : α} (hab : b ∈ leftMoves a) :
    toIGame b ∈ (toIGame a).leftMoves := by
  rw [leftMoves_toIGame]
  exact ⟨b, hab, rfl⟩

theorem mem_rightMoves_toIGame_of_mem {a b : α} (hab : b ∈ rightMoves a) :
    toIGame b ∈ (toIGame a).rightMoves := by
  rw [rightMoves_toIGame]
  exact ⟨b, hab, rfl⟩

@[simp]
theorem toLGame_toIGame (a : α) : (toIGame a).toLGame = toLGame a := by
  apply moveRecOn a fun b IHl IHr ↦ ?_
  ext x
  · simp_rw [leftMoves_toLGame, mem_image, IGame.leftMoves_toLGame, leftMoves_toIGame]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (IHl _ hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, mem_image_of_mem _ hx, IHl _ hx⟩
  · simp_rw [rightMoves_toLGame, mem_image, IGame.rightMoves_toLGame, rightMoves_toIGame]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (IHr _ hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, mem_image_of_mem _ hx, IHr _ hx⟩

theorem neg_toIGame (h : leftMoves (α := α) = rightMoves) (a : α) : -toIGame a = toIGame a := by
  rw [← IGame.toLGame.injective.eq_iff]
  simpa using neg_toLGame h a

theorem impartial_toIGame (h : leftMoves (α := α) = rightMoves) (a : α) :
    Impartial (toIGame a) := by
  apply moveRecOn a fun b IHl IHr ↦ ?_
  rw [impartial_def, neg_toIGame h]
  simp_all

end ConcreteIGame

/-! ### Type aliases -/

/-- A type alias to turn a concrete game impartial, by allowing both players to perform
each other's moves. -/
def ToImpartial (α : Type*) := α

def toImpartial : α ≃ ToImpartial α := Equiv.refl _
def ofImpartial : ToImpartial α ≃ α := Equiv.refl _
@[simp] theorem ofImpartial_toImpartial (x : α) : ofImpartial (toImpartial x) = x := rfl
@[simp] theorem toImpartial_ofImpartial (x : ToImpartial α) : toImpartial (ofImpartial x) = x := rfl

namespace ToImpartial
section ConcreteLGame
variable [ConcreteLGame α]

instance : ConcreteLGame (ToImpartial α) :=
  .ofImpartial (fun x ↦ {y | IsOption (ofImpartial y) (ofImpartial x)})

theorem leftMoves_eq_rightMoves (x : ToImpartial α) : leftMoves x = rightMoves x := rfl

theorem mem_leftMoves {x y : ToImpartial α} :
    y ∈ leftMoves x ↔ IsOption (ofImpartial y) (ofImpartial x) := .rfl

theorem mem_rightMoves {x y : ToImpartial α} :
    y ∈ rightMoves x ↔ IsOption (ofImpartial y) (ofImpartial x) := .rfl

theorem isOption_iff {x y : ToImpartial α} :
    IsOption x y ↔ IsOption (ofImpartial x) (ofImpartial y) := or_self_iff

end ConcreteLGame

section ConcreteIGame
variable [ConcreteIGame α]

instance : ConcreteIGame (ToImpartial α) :=
  @ConcreteIGame.ofImpartial _ _ _ <| ConcreteIGame.isWellFounded_isOption (α := α)

@[simp]
theorem neg_toIGame (x : ToImpartial α) : -toIGame x = toIGame x :=
  ConcreteGame.neg_toIGame rfl x

instance (x : ToImpartial α) : Impartial (toIGame x) :=
  impartial_toIGame rfl x

end ConcreteIGame
end ToImpartial
