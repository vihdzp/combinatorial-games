/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Kim Morrison
-/
import CombinatorialGames.IGame.IGame
import Mathlib.Data.Countable.Small

/-!
# Short games

A combinatorial game is `Short` [Conway, ch.9][conway2001] if it has only finitely many positions.
In particular, this means there is a finite set of moves at every point.

We define here `IGame.Short` as data, providing data for the left and right moves of a game in the
form of an auxiliary `SGame` type. This makes us capable of performing some basic computations on
`IGame`.
-/

universe u

-- Universe polymorphic so we can use this on every universe of `IGame`.
inductive SGame : Type u
  | mk (s t : ℕ) (f : Fin s → SGame) (g : Fin t → SGame) : SGame
compile_inductive% SGame

namespace SGame

def LeftMoves : SGame → ℕ
  | mk α _ _ _ => α

def RightMoves : SGame → ℕ
  | mk _ β _ _ => β

def moveLeft : (x : SGame) → Fin x.LeftMoves → SGame
  | mk _ _ f _ => f

def moveRight : (x : SGame) → Fin x.RightMoves → SGame
  | mk _ _ _ g => g

inductive IsOption : SGame → SGame → Prop
  | moveLeft {x : SGame} (n : Fin x.LeftMoves) : IsOption (x.moveLeft n) x
  | moveRight {x : SGame} (n : Fin x.RightMoves) : IsOption (x.moveRight n) x

theorem isOption_wf : WellFounded IsOption := by
  refine ⟨rec fun s t f g IHl IHr ↦ .intro _ ?_⟩
  rintro y (h | h)
  · apply IHl
  · apply IHr

noncomputable def toIGame (x : SGame.{u}) : IGame.{u} :=
  {Set.range fun n ↦ toIGame (x.moveLeft n) | Set.range fun n ↦ toIGame (x.moveRight n)}ᴵ
termination_by isOption_wf.wrap x
decreasing_by all_goals apply_rules [IsOption.moveLeft, IsOption.moveRight]

@[simp]
theorem leftMoves_toIGame (x : SGame) :
    x.toIGame.leftMoves = Set.range (toIGame ∘ x.moveLeft) := by
  rw [toIGame]
  simp [Function.comp_def]

@[simp]
theorem rightMoves_toIGame (x : SGame) :
    x.toIGame.rightMoves = Set.range (toIGame ∘ x.moveRight) := by
  rw [toIGame]
  simp [Function.comp_def]

instance : Preorder SGame.{u} :=
  Preorder.lift toIGame.{u}

theorem toIGame_le_iff {x y : SGame} : toIGame x ≤ toIGame y ↔
    (∀ n, ¬ toIGame y ≤ toIGame (x.moveLeft n)) ∧
    (∀ n, ¬ toIGame (y.moveRight n) ≤ toIGame x) := by
  rw [IGame.le_iff_forall_lf]
  simp

private def decidableLE' {x y : SGame} : Decidable (x.toIGame ≤ y.toIGame) :=
  let _ (n) : Decidable (toIGame y ≤ toIGame (x.moveLeft n)) := decidableLE'
  let _ (n) : Decidable (toIGame (y.moveRight n) ≤ toIGame x) := decidableLE'
  decidable_of_iff' _ toIGame_le_iff
termination_by isOption_wf.sym2_gameAdd.wrap s(x, y)
decreasing_by
  · exact Sym2.GameAdd.snd_fst (.moveLeft _)
  · exact Sym2.GameAdd.fst_snd (.moveRight _)

instance : DecidableLE SGame := @decidableLE'
instance : DecidableLT SGame := decidableLTOfDecidableLE

/-! ### Basic games -/

def ofLists (l m : List SGame) : SGame :=
  mk l.length m.length l.get m.get

@[simp] theorem leftMoves_ofLists (l m : List SGame) : (ofLists l m).LeftMoves = l.length := rfl
@[simp] theorem righttMoves_ofLists (l m : List SGame) : (ofLists l m).RightMoves = m.length := rfl

@[simp] theorem moveLeft_ofLists (l m : List SGame) (n : Fin l.length) :
    (ofLists l m).moveLeft n = l[n] :=
  rfl

@[simp] theorem moveRight_ofLists (l m : List SGame) (n : Fin m.length) :
    (ofLists l m).moveRight n = m[n] :=
  rfl

instance : Zero SGame := ⟨ofLists [] []⟩

theorem zero_def : 0 = ofLists [] [] := rfl
@[simp] theorem leftMoves_zero : LeftMoves 0 = 0 := rfl
@[simp] theorem rightMoves_zero : RightMoves 0 = 0 := rfl
@[simp] theorem toIGame_zero : toIGame 0 = 0 := by ext <;> simp

instance : One SGame := ⟨ofLists [0] []⟩

theorem one_def : 1 = ofLists [0] [] := rfl
@[simp] theorem leftMoves_one : LeftMoves 1 = 1 := rfl
@[simp] theorem rightMoves_one : RightMoves 1 = 0 := rfl
@[simp] theorem moveLeft_one (n : Fin 1) : moveLeft 1 n = 0 := by simp [one_def]
@[simp] theorem toIGame_one : toIGame 1 = 1 := by ext <;> simp [eq_comm]

end SGame

namespace IGame

class Short (x : IGame.{u}) : Type u where
  toSGame : SGame.{u}
  toIGame_toSGame : toSGame.toIGame = x

namespace Short
attribute [simp] toIGame_toSGame

@[simp]
theorem toSGame_le_iff {x y : IGame} [Short x] [Short y] : toSGame x ≤ toSGame y ↔ x ≤ y := by
  change (toSGame x).toIGame ≤ (toSGame y).toIGame ↔ x ≤ y
  simp

@[simp]
theorem toSGame_lt_iff {x y : IGame} [Short x] [Short y] : toSGame x < toSGame y ↔ x < y :=
  lt_iff_lt_of_le_iff_le' toSGame_le_iff toSGame_le_iff

instance (x y : IGame) [Short x] [Short y] : Decidable (x ≤ y) :=
  decidable_of_iff _ toSGame_le_iff

instance (x y : IGame) [Short x] [Short y] : Decidable (x < y) :=
  decidable_of_iff _ toSGame_lt_iff

instance (x y : IGame) [Short x] [Short y] : Decidable (x ≈ y) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance : Short 0 := ⟨0, SGame.toIGame_zero⟩
instance : Short 1 := ⟨1, SGame.toIGame_one⟩

example : 0 < 1 := by decide

end Short
end IGame
