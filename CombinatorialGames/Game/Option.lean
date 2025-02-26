/-
Copyright (c) 2024 Theodore Hwa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Theodore Hwa, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.PGame

/-!
# Insert or remove options

We provide API for adding or removing an option from a `PGame`.
-/

namespace PGame

/-! ### Inserting an option -/

/-! #### Left option -/

/-- The pregame constructed by inserting `y` as a new left option into `x`. -/
def insertLeft (x y : PGame) : PGame :=
  match x with
  | mk xl xr xL xR => mk (Option xl) xr (fun x => x.elim y xL) xR

/-- Use `toLeftMovesInsertLeft` to cast between these two types. -/
@[simp]
theorem leftMoves_insertLeft (x y : PGame) :
    (insertLeft x y).LeftMoves = Option (x.LeftMoves) := by
  cases x
  rfl

/-- Use `toRightMovesInsertLeft` to cast between these two types. -/
@[simp]
theorem rightMoves_insertLeft (x y : PGame) : (insertLeft x y).RightMoves = x.RightMoves := by
  cases x
  rfl

/-- Turns a left move for `x`, or a `none` value, into a left move for `insertLeft x y` and vice
versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesInsertLeft {x y : PGame} : Option x.LeftMoves ≃ (insertLeft x y).LeftMoves :=
  Equiv.cast (leftMoves_insertLeft x _).symm

/-- Turns a right move for `x` into a right move for `insertLeft x y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesInsertLeft {x y : PGame} : x.RightMoves ≃ (insertLeft x y).RightMoves :=
  Equiv.cast (rightMoves_insertLeft x _).symm

@[simp]
theorem moveLeft_insertLeft_some {x y : PGame} (i) :
    (insertLeft x y).moveLeft (toLeftMovesInsertLeft (some i)) = x.moveLeft i := by
  cases x
  rfl

@[simp]
theorem moveLeft_insertLeft_none {x y : PGame} :
    (insertLeft x y).moveLeft (toLeftMovesInsertLeft none) = y := by
  cases x
  rfl

@[simp]
theorem moveRight_insertLeft {x y : PGame} (i) :
    (insertLeft x y).moveRight i = x.moveRight (toRightMovesInsertLeft.symm i) := by
  cases x
  rfl

theorem moveRight_insertLeft_toRightMovesInsertLeft {x y : PGame} (i) :
    (insertLeft x y).moveRight (toRightMovesInsertLeft i) = x.moveRight i := by
  simp

/-- A recursor for `(insertLeft x y).LeftMoves`. -/
@[elab_as_elim]
def leftMovesInsertLeftRecOn {x y : PGame} (i) {P : (insertLeft x y).LeftMoves → Sort*}
    (none : P (toLeftMovesInsertLeft none)) (some : Π i, P (toLeftMovesInsertLeft (some i))) :
    P i :=
  cast (by simp) <| (toLeftMovesInsertLeft.symm i).casesOn
    (motive := fun x ↦ P (toLeftMovesInsertLeft x)) none some

/-- A recursor for `(insertLeft x y).RightMoves`. -/
@[elab_as_elim]
def rightMovesInsertLeftRecOn {x y : PGame} (i) {P : (insertLeft x y).RightMoves → Sort*}
    (H : Π i, P (toRightMovesInsertLeft i)) : P i :=
  cast (by simp) <| H (toRightMovesInsertLeft.symm i)

@[simp]
theorem leftMovesInsertLeftRecOn_toLeftMovesInsertLeft_none {x y : PGame}
    {P : (insertLeft x y).LeftMoves → Sort*}
    (none : P (toLeftMovesInsertLeft none)) (some : Π i, P (toLeftMovesInsertLeft (some i))) :
    leftMovesInsertLeftRecOn (toLeftMovesInsertLeft .none) none some = none := by
  cases x; cases y; rfl

@[simp]
theorem leftMovesInsertLeftRecOn_toLeftMovesInsertLeft_some {x y : PGame} (i)
    {P : (insertLeft x y).LeftMoves → Sort*}
    (none : P (toLeftMovesInsertLeft none)) (some : Π i, P (toLeftMovesInsertLeft (some i))) :
    leftMovesInsertLeftRecOn (toLeftMovesInsertLeft (.some i)) none some = some i := by
  cases x; cases y; rfl

@[simp]
theorem rightMovesInsertLeftRecOn_toLeftMovesInsertLeft {x y : PGame} (i)
    {P : (insertLeft x y).RightMoves → Sort*} (H : Π i, P (toRightMovesInsertLeft i)) :
    rightMovesInsertLeftRecOn (toRightMovesInsertLeft i) H = H i := by
  cases x; cases y; rfl

theorem lf_insertLeft (x y : PGame) : y ⧏ insertLeft x y := by
  simpa using moveLeft_lf (toLeftMovesInsertLeft none)

/-- A new left option cannot hurt Left. -/
theorem le_insertLeft (x y : PGame) : x ≤ insertLeft x y := by
  rw [le_iff_forall_lf]
  constructor <;>
  intro i
  · simpa using moveLeft_lf (toLeftMovesInsertLeft (some i))
  · simpa using lf_moveRight _

/-- Adding a gift horse left option does not change the value of `x`.

A gift horse left option is a game `y` with `y ⧏ x`. It is called "gift horse" because it seems
like Left has gotten the "gift" of a new option, but actually the value of the game did not change.
-/
theorem insertLeft_equiv_of_lf {x y : PGame} (h : y ⧏ x) : insertLeft x y ≈ x := by
  refine ⟨?_, le_insertLeft x y⟩
  dsimp
  rw [le_iff_forall_lf]
  constructor <;> intro i
  · induction i using leftMovesInsertLeftRecOn
    · simpa
    · simpa using moveLeft_lf _
  · simpa using lf_moveRight (toRightMovesInsertLeft i)

/-! #### Right option -/

/-- The pregame constructed by inserting `y` as a new right option into `x`. -/
def insertRight (x y : PGame) : PGame :=
  match x with
  | mk xl xr xL xR => mk xl (Option xr) xL (fun x => x.elim y xR)

/-- Use `toLeftMovesInsertLeft` to cast between these two types. -/
@[simp]
theorem leftMoves_insertRight (x y : PGame) :
    (insertRight x y).LeftMoves = x.LeftMoves := by
  cases x
  rfl

/-- Use `toRightMovesInsertLeft` to cast between these two types. -/
@[simp]
theorem rightMoves_insertRight (x y : PGame) :
    (insertRight x y).RightMoves = Option x.RightMoves := by
  cases x
  rfl

/-- Turns a right move for `x` into a right move for `insertRight x y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesInsertRight {x y : PGame} : x.LeftMoves ≃ (insertRight x y).LeftMoves :=
  Equiv.cast (leftMoves_insertRight x _).symm

/-- Turns a left move for `x`, or a `none` value, into a left move for `insertRight x y` and vice
versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesInsertRight {x y : PGame} : Option x.RightMoves ≃ (insertRight x y).RightMoves :=
  Equiv.cast (rightMoves_insertRight x _).symm

@[simp]
theorem moveLeft_insertRight {x y : PGame} (i) :
    (insertRight x y).moveLeft i = x.moveLeft (toLeftMovesInsertRight.symm i) := by
  cases x
  rfl

theorem moveLeft_insertRight_toLeftMovesInsertRight {x y : PGame} (i) :
    (insertRight x y).moveLeft (toLeftMovesInsertRight i) = x.moveLeft i := by
  simp

@[simp]
theorem moveRight_insertRight_none {x y : PGame} :
    (insertRight x y).moveRight (toRightMovesInsertRight none) = y := by
  cases x
  rfl

@[simp]
theorem moveRight_insertRight_some {x y : PGame} (i) :
    (insertRight x y).moveRight (toRightMovesInsertRight (some i)) = x.moveRight i := by
  cases x
  rfl

/-- A recursor for `(insertLeft x y).LeftMoves`. -/
@[elab_as_elim]
def leftMovesInsertRightRecOn {x y : PGame} (i) {P : (insertRight x y).LeftMoves → Sort*}
    (H : Π i, P (toLeftMovesInsertRight i)) : P i :=
  cast (by simp) <| H (toLeftMovesInsertRight.symm i)

/-- A recursor for `(insertRight x y).RightMoves`. -/
@[elab_as_elim]
def rightMovesInsertRightRecOn {x y : PGame} (i) {P : (insertRight x y).RightMoves → Sort*}
    (none : P (toRightMovesInsertRight none)) (some : Π i, P (toRightMovesInsertRight (some i))) :
    P i :=
  cast (by simp) <| (toRightMovesInsertRight.symm i).casesOn
    (motive := fun x ↦ P (toRightMovesInsertRight x)) none some

@[simp]
theorem leftMovesInsertRightRecOn_toLeftMovesInsertRight {x y : PGame} (i)
    {P : (insertRight x y).LeftMoves → Sort*} (H : Π i, P (toLeftMovesInsertRight i)) :
    leftMovesInsertRightRecOn (toLeftMovesInsertRight i) H = H i := by
  cases x; cases y; rfl

@[simp]
theorem rightMovesInsertRightRecOn_toRightMovesInsertRight_none {x y : PGame}
    {P : (insertRight x y).RightMoves → Sort*}
    (none : P (toRightMovesInsertRight none)) (some : Π i, P (toRightMovesInsertRight (some i))) :
    rightMovesInsertRightRecOn (toRightMovesInsertRight .none) none some = none := by
  cases x; cases y; rfl

@[simp]
theorem rightMovesInsertRightRecOn_toRightMovesInsertRight_some {x y : PGame} (i)
    {P : (insertRight x y).RightMoves → Sort*}
    (none : P (toRightMovesInsertRight none)) (some : Π i, P (toRightMovesInsertRight (some i))) :
    rightMovesInsertRightRecOn (toRightMovesInsertRight (.some i)) none some = some i := by
  cases x; cases y; rfl

@[simp]
theorem neg_insertRight_neg (x y : PGame) : (-x).insertRight (-y) = -x.insertLeft y := by
  cases x
  cases y
  dsimp [insertRight, insertLeft]
  congr! with (i | j)

@[simp]
theorem neg_insertLeft_neg (x y : PGame) : (-x).insertLeft (-y) = -x.insertRight y := by
  rw [← neg_eq_iff_eq_neg, ← neg_insertRight_neg, neg_neg, neg_neg]

theorem insertRight_lf (x y : PGame) : insertRight x y ⧏ y := by
  simpa using lf_moveRight (toRightMovesInsertRight none)

/-- A new right option cannot hurt Right. -/
theorem insertRight_le (x y : PGame) : insertRight x y ≤ x := by
  simpa using le_insertLeft (-x) (-y)

/-- Adding a gift horse right option does not change the value of `x`.

A gift horse right option is a game `y` with `x ⧏ y`. It is called "gift horse" because it seems
like Right has gotten the "gift" of a new option, but actually the value of the game did not change.
-/
theorem insertRight_equiv_of_lf {x y : PGame} (h : x ⧏ y) : insertRight x y ≈ x := by
  rw [← neg_equiv_neg_iff, ← neg_insertLeft_neg]
  exact insertLeft_equiv_of_lf (neg_lf_neg_iff.mpr h)

/-- Inserting on the left and right commutes. -/
theorem insertRight_insertLeft {x y z : PGame} :
    insertRight (insertLeft x y) z = insertLeft (insertRight x z) y := by
  cases x; cases y; cases z
  dsimp [insertLeft, insertRight]

-- TODO: deleting an option!

end PGame
