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

/-- An auxiliary type for `IGame.Short`.

The purpose of this type is to provide auxiliary data for an `IGame` which can then be used to
perform computations. You should not build any substantial theory around this type.

This could perfectly well have been in `Type 0`, but we make it universe polymorphic for
convenience: operations on `SGame.{u}` correspond to operations on `IGame.{u}`. -/
inductive SGame : Type u
  | mk (m n : ℕ) (f : Fin m → SGame) (g : Fin n → SGame) : SGame
compile_inductive% SGame

/-! ### Game moves -/

namespace SGame

/-- The number of left moves on a `SGame`. -/
def leftMoves : SGame → ℕ
  | mk m _ _ _ => m

/-- The number of right moves on a `SGame`. -/
def rightMoves : SGame → ℕ
  | mk _ n _ _ => n

/-- Perform a left move. -/
def moveLeft : (x : SGame) → Fin x.leftMoves → SGame
  | mk _ _ f _ => f

/-- Perform a right move. -/
def moveRight : (x : SGame) → Fin x.rightMoves → SGame
  | mk _ _ _ g => g

@[simp] theorem leftMoves_mk (m n f g) : leftMoves (mk m n f g) = m := rfl
@[simp] theorem rightMoves_mk (m n f g) : rightMoves (mk m n f g) = n := rfl
@[simp] theorem moveLeft_mk (m n f g) : moveLeft (mk m n f g) = f := rfl
@[simp] theorem moveRight_mk (m n f g) : moveRight (mk m n f g) = g := rfl

/-- A well-founded relation on `SGame`, see `IGame.IsOption`. -/
inductive IsOption : SGame → SGame → Prop
  | moveLeft {x : SGame} (n : Fin x.leftMoves) : IsOption (x.moveLeft n) x
  | moveRight {x : SGame} (n : Fin x.rightMoves) : IsOption (x.moveRight n) x

theorem isOption_wf : WellFounded IsOption := by
  refine ⟨rec fun s t f g IHl IHr ↦ .intro _ ?_⟩
  rintro y (h | h)
  · apply IHl
  · apply IHr

instance : WellFoundedRelation SGame := ⟨_, isOption_wf⟩

/-- (Noncomputably) converts an `SGame` into an `IGame`. -/
noncomputable def toIGame (x : SGame.{u}) : IGame.{u} :=
  {.range fun m ↦ toIGame (x.moveLeft m) | .range fun n ↦ toIGame (x.moveRight n)}ᴵ
termination_by x
decreasing_by all_goals apply_rules [IsOption.moveLeft, IsOption.moveRight]

theorem toIGame_def (x : SGame) : x.toIGame =
    {.range (toIGame ∘ x.moveLeft) | .range (toIGame ∘ x.moveRight)}ᴵ :=
  by rw [toIGame]; rfl

@[simp]
theorem leftMoves_toIGame (x : SGame) : x.toIGame.leftMoves = .range (toIGame ∘ x.moveLeft) := by
  simp [toIGame_def]

@[simp]
theorem rightMoves_toIGame (x : SGame) : x.toIGame.rightMoves = .range (toIGame ∘ x.moveRight) := by
  simp [toIGame_def]

/-- We define a preorder instance by simply lifting to `IGame`. -/
instance : Preorder SGame.{u} :=
  Preorder.lift toIGame.{u}

theorem toIGame_le_iff {x y : SGame} : toIGame x ≤ toIGame y ↔
    (∀ m, ¬ toIGame y ≤ toIGame (x.moveLeft m)) ∧
    (∀ n, ¬ toIGame (y.moveRight n) ≤ toIGame x) := by
  rw [IGame.le_iff_forall_lf]
  simp

@[semireducible]
private def decidableLE' {x y : SGame} : Decidable (x.toIGame ≤ y.toIGame) :=
  let _ (m) : Decidable (toIGame y ≤ toIGame (x.moveLeft m)) := decidableLE'
  let _ (n) : Decidable (toIGame (y.moveRight n) ≤ toIGame x) := decidableLE'
  decidable_of_iff' _ toIGame_le_iff
termination_by isOption_wf.sym2_gameAdd.wrap s(x, y)
decreasing_by
  · exact Sym2.GameAdd.snd_fst (.moveLeft m)
  · exact Sym2.GameAdd.fst_snd (.moveRight n)

instance : DecidableLE SGame := @decidableLE'
instance : DecidableLT SGame := decidableLTOfDecidableLE

/-! ### Basic games -/
/--/
/-- Create an `SGame` from two lists of `SGame`s. -/
def ofLists (l m : List SGame) : SGame :=
  mk l.length m.length l.get m.get

@[simp] theorem leftMoves_ofLists (l m : List SGame) : (ofLists l m).leftMoves = l.length := rfl
@[simp] theorem rightMoves_ofLists (l m : List SGame) : (ofLists l m).rightMoves = m.length := rfl

@[simp] theorem moveLeft_ofLists (l m : List SGame) (n : Fin l.length) :
    (ofLists l m).moveLeft n = l[n] :=
  rfl

@[simp] theorem moveRight_ofLists (l m : List SGame) (n : Fin m.length) :
    (ofLists l m).moveRight n = m[n] :=
  rfl-/

instance : Zero SGame := ⟨mk 0 0 nofun nofun⟩

theorem zero_def : (0 : SGame) = mk 0 0 nofun nofun := rfl
@[simp] theorem leftMoves_zero : leftMoves 0 = 0 := rfl
@[simp] theorem rightMoves_zero : rightMoves 0 = 0 := rfl
@[simp] theorem toIGame_zero : toIGame 0 = 0 := by ext <;> simp

instance : One SGame := ⟨mk 1 0 (fun _ ↦ 0) nofun⟩

theorem one_def : (1 : SGame) = mk 1 0 (fun _ ↦ 0) nofun := rfl
@[simp] theorem leftMoves_one : leftMoves 1 = 1 := rfl
@[simp] theorem rightMoves_one : rightMoves 1 = 0 := rfl
@[simp] theorem moveLeft_one (n : Fin 1) : moveLeft 1 n = 0 := rfl
@[simp] theorem toIGame_one : toIGame 1 = 1 := by ext <;> simp [eq_comm]

private def neg' (x : SGame) : SGame :=
  mk _ _ (fun n ↦ neg' (x.moveRight n)) (fun m ↦ neg' (x.moveLeft m))
termination_by x
decreasing_by all_goals apply_rules [IsOption.moveLeft, IsOption.moveRight]

instance : Neg SGame := ⟨neg'⟩

theorem neg_def (x : SGame) : -x = mk _ _ (Neg.neg ∘ x.moveRight) (Neg.neg ∘ x.moveLeft) := by
  change neg' _ = _
  rw [neg']
  rfl

@[simp] theorem leftMoves_neg (x : SGame) : (-x).leftMoves = x.rightMoves := by rw [neg_def]; rfl
@[simp] theorem rightMoves_neg (x : SGame) : (-x).rightMoves = x.leftMoves := by rw [neg_def]; rfl

theorem moveLeft_neg_heq (x : SGame) : HEq (moveLeft (-x)) (Neg.neg ∘ x.moveRight) := by
  rw [neg_def]
  rfl

theorem moveRight_neg_heq (x : SGame) : HEq (moveRight (-x)) (Neg.neg ∘ x.moveLeft) := by
  rw [neg_def]
  rfl

@[simp]
theorem moveLeft_neg (x : SGame) (n) : (-x).moveLeft n = -x.moveRight (cast (by simp) n) := by
  apply congr_heq (moveLeft_neg_heq x); simp

@[simp]
theorem moveRight_neg (x : SGame) (n) : (-x).moveRight n = -x.moveLeft (cast (by simp) n) := by
  apply congr_heq (moveRight_neg_heq x); simp

@[simp] theorem toIGame_neg (s : SGame) : toIGame (-s) = -toIGame s := by
  ext
  on_goal 1 =>
    simp only [leftMoves_toIGame, IGame.leftMoves_neg, rightMoves_toIGame,
      Set.mem_range, Set.mem_neg]
    have H : Fin (-s).leftMoves = Fin s.rightMoves := by simp
  on_goal 2 =>
    simp only [rightMoves_toIGame, IGame.rightMoves_neg, leftMoves_toIGame,
      Set.mem_range, Set.mem_neg]
    have H : Fin (-s).rightMoves = Fin s.leftMoves := by simp
  all_goals
    rw [← (Equiv.cast H).exists_congr_right]
    simp only [Function.comp_apply, moveLeft_neg, moveRight_neg, Equiv.cast_apply]
    congr! 2
    rw [← neg_inj, toIGame_neg, neg_neg]
termination_by s
decreasing_by all_goals apply_rules [IsOption.moveLeft, IsOption.moveRight]

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

instance (x : IGame) [Short x] : Short (-x) := ⟨-toSGame x, by simp⟩

example : (0 : IGame.{0}) < 1 := by decide

-- Why doesn't this work?
example : (-0 : IGame.{0}) < 1 := by decide

end Short
end IGame
