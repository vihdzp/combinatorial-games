/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Kim Morrison
-/
import CombinatorialGames.IGame.IGame
import Mathlib.Data.Countable.Small

/-!
# Short games

A combinatorial game is `Short` if it has only finitely many positions. In particular, this means
there is a finite set of moves at every point.

We define here `IGame.Short` as data, providing data for the left and right moves of a game in the
form of an auxiliary `SGame` type. This makes us capable of performing some basic computations on
`IGame`. Unfortunately, well-founded recursion and reducibility don't mix very well in Lean. As
such, we must often rely on `native_decide` to make use of this typeclass for computation.
-/

universe u

/-- An auxiliary type for `IGame.Short`.

The purpose of this type is to provide auxiliary data for an `IGame` which can then be used to
perform computations. **You should not build any substantial theory based on this type.**

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

@[simp] theorem leftMoves_mk (m n f g) : (mk m n f g).leftMoves = m := rfl
@[simp] theorem rightMoves_mk (m n f g) : (mk m n f g).rightMoves = n := rfl
@[simp] theorem moveLeft_mk (m n f g) : (mk m n f g).moveLeft = f := rfl
@[simp] theorem moveRight_mk (m n f g) : (mk m n f g).moveRight = g := rfl

/-- A well-founded relation on `SGame`, see `IGame.IsOption`. -/
inductive IsOption : SGame → SGame → Prop
  | moveLeft {x : SGame} (n : Fin x.leftMoves) : IsOption (x.moveLeft n) x
  | moveRight {x : SGame} (n : Fin x.rightMoves) : IsOption (x.moveRight n) x

theorem isOption_wf : WellFounded IsOption := by
  refine ⟨rec fun s t f g IHl IHr ↦ .intro _ ?_⟩
  rintro y (h | h)
  · exact IHl _
  · exact IHr _

instance : WellFoundedRelation SGame := ⟨_, isOption_wf⟩

/-- See `igame_wf`. -/
macro "sgame_wf" : tactic =>
  `(tactic| all_goals solve_by_elim
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    IsOption.moveLeft, IsOption.moveRight] )

def toStringAux {n : ℕ} (f : Fin n → String) : String :=
  ", ".intercalate (.ofFn f)

def toString' (x : SGame) : String :=
  "{" ++ toStringAux (fun i ↦ toString' (x.moveLeft i)) ++ " | " ++
    toStringAux (fun j ↦ toString' (x.moveRight j)) ++ "}"
termination_by x
decreasing_by sgame_wf

/-- The size of an `SGame` is its number of proper subpositions.

Note that this doesn't necessarily correspond to the number of subpositions of the `IGame`, though
it does serve as a way to estimate how "complex" the game is to build. -/
def size (x : SGame) : ℕ :=
  ∑ i, ((x.moveLeft i).size + 1) + ∑ j, ((x.moveRight j).size + 1)
termination_by x
decreasing_by sgame_wf

instance : ToString SGame := ⟨toString'⟩

/-! ### Decidability instances -/

/-- (Noncomputably) converts an `SGame` into an `IGame`. -/
noncomputable def toIGame (x : SGame.{u}) : IGame.{u} :=
  {.range fun m ↦ toIGame (x.moveLeft m) | .range fun n ↦ toIGame (x.moveRight n)}ᴵ
termination_by x
decreasing_by sgame_wf

theorem toIGame_def (x : SGame) : x.toIGame =
    {.range (toIGame ∘ x.moveLeft) | .range (toIGame ∘ x.moveRight)}ᴵ :=
  by rw [toIGame]; rfl

@[simp]
theorem leftMoves_toIGame (x : SGame) : x.toIGame.leftMoves = .range (toIGame ∘ x.moveLeft) := by
  simp [toIGame_def]

@[simp]
theorem rightMoves_toIGame (x : SGame) : x.toIGame.rightMoves = .range (toIGame ∘ x.moveRight) := by
  simp [toIGame_def]

/-- We define a preorder instance by lifting to `IGame`. -/
instance : Preorder SGame.{u} :=
  .lift toIGame.{u}

theorem toIGame_le_iff {x y : SGame} : toIGame x ≤ toIGame y ↔
    (∀ m, ¬ toIGame y ≤ toIGame (x.moveLeft m)) ∧
    (∀ n, ¬ toIGame (y.moveRight n) ≤ toIGame x) := by
  rw [IGame.le_iff_forall_lf]
  simp

theorem toIGame_eq_iff {x y : SGame} : toIGame x = toIGame y ↔
    (∀ m, ∃ n, toIGame (x.moveLeft m) = toIGame (y.moveLeft n)) ∧
    (∀ n, ∃ m, toIGame (x.moveLeft m) = toIGame (y.moveLeft n)) ∧
    (∀ m, ∃ n, toIGame (x.moveRight m) = toIGame (y.moveRight n)) ∧
    (∀ n, ∃ m, toIGame (x.moveRight m) = toIGame (y.moveRight n)) := by
  rw [IGame.ext_iff]
  simp [subset_antisymm_iff, Set.subset_def, and_assoc, eq_comm]

@[semireducible] -- This aids, but doesn't completely fix reducibility issues.
private def decidableLE' {x y : SGame} : Decidable (x.toIGame ≤ y.toIGame) :=
  letI (m) : Decidable (toIGame y ≤ toIGame (x.moveLeft m)) := decidableLE'
  letI (n) : Decidable (toIGame (y.moveRight n) ≤ toIGame x) := decidableLE'
  decidable_of_iff' _ toIGame_le_iff
termination_by isOption_wf.sym2_gameAdd.wrap s(x, y)
decreasing_by
  · exact Sym2.GameAdd.snd_fst (.moveLeft m)
  · exact Sym2.GameAdd.fst_snd (.moveRight n)

instance : DecidableLE SGame := @decidableLE'
instance : DecidableLT SGame := decidableLTOfDecidableLE

@[semireducible] -- This aids, but doesn't completely fix reducibility issues.
private def decidableEQ' {x y : SGame} : Decidable (x.toIGame = y.toIGame) :=
  letI (m n) : Decidable (toIGame (x.moveLeft m) = toIGame (y.moveLeft n)) := decidableEQ'
  letI (m n) : Decidable (toIGame (x.moveRight m) = toIGame (y.moveRight n)) := decidableEQ'
  decidable_of_iff' _ toIGame_eq_iff
termination_by (x, y)
decreasing_by sgame_wf

instance (x y : SGame) : Decidable (toIGame x = toIGame y) := decidableEQ'

/-! ### Basic games -/

/-! #### Game from lists -/

/-- Create an `SGame` from two lists of `SGame`s. -/
def ofLists (l m : List SGame) : SGame :=
  mk l.length m.length l.get m.get

@[simp] theorem leftMoves_ofLists (l m : List SGame) : (ofLists l m).leftMoves = l.length := rfl
@[simp] theorem rightMoves_ofLists (l m : List SGame) : (ofLists l m).rightMoves = m.length := rfl

@[simp]
theorem moveLeft_ofLists (l m : List SGame) (n : Fin l.length) :
    (ofLists l m).moveLeft n = l[n] :=
  rfl

@[simp]
theorem moveRight_ofLists (l m : List SGame) (n : Fin m.length) :
    (ofLists l m).moveRight n = m[n] :=
  rfl

instance {α : Type*} (l : List α) : Small {x | x ∈ l} := by
  have := @Fintype.ofFinite _ (List.finite_toSet l)
  infer_instance

@[simp]
theorem toIGame_ofLists (l m : List SGame) :
    (ofLists l m).toIGame = {toIGame '' {x | x ∈ l} | toIGame '' {x | x ∈ m}}ᴵ := by
  ext <;> simp [List.exists_mem_iff_getElem, Fin.exists_iff]

/-! #### Natural numbers -/

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

private def natCast' : ℕ → SGame
  | 0 => 0
  | n + 1 => mk 1 0 (fun _ ↦ natCast' n) nofun

instance : NatCast SGame := ⟨natCast'⟩

@[simp] theorem natCast_zero : ((0 : ℕ) : SGame) = 0 := rfl

@[simp]
theorem natCast_succ (n : ℕ) : ((n + 1 : ℕ) : SGame) = mk 1 0 (fun _ ↦ n) nofun :=
  rfl

@[simp] theorem leftMoves_natCast_succ (n : ℕ) : leftMoves ((n + 1) : ℕ) = 1 := rfl
@[simp] theorem rightMoves_natCast (n : ℕ) : rightMoves n = 0 := by cases n <;> rfl
@[simp] theorem moveLeft_natCast_succ (n : ℕ) (i : Fin 1) : moveLeft ((n + 1) : ℕ) i = n := rfl

@[simp]
theorem toIGame_natCast (n : ℕ) : toIGame n = n := by
  cases n
  · simp
  · ext <;> simp
    rw [eq_comm, toIGame_natCast]

@[simp]
theorem toIGame_ofNat (n : ℕ) [n.AtLeastTwo] : toIGame ofNat(n) = n :=
  toIGame_natCast n

/-! #### Negation -/

private def neg' (x : SGame) : SGame :=
  mk _ _ (fun n ↦ neg' (x.moveRight n)) (fun m ↦ neg' (x.moveLeft m))
termination_by x
decreasing_by sgame_wf

instance : Neg SGame := ⟨neg'⟩

theorem neg_def (x : SGame) : -x = mk _ _ (Neg.neg ∘ x.moveRight) (Neg.neg ∘ x.moveLeft) := by
  change neg' x = _
  rw [neg']
  rfl

@[simp] theorem leftMoves_neg (x : SGame) : (-x).leftMoves = x.rightMoves := by rw [neg_def]; rfl
@[simp] theorem rightMoves_neg (x : SGame) : (-x).rightMoves = x.leftMoves := by rw [neg_def]; rfl

theorem moveLeft_neg_heq (x : SGame) : HEq (moveLeft (-x)) (Neg.neg ∘ x.moveRight) := by
  rw [neg_def]; rfl

theorem moveRight_neg_heq (x : SGame) : HEq (moveRight (-x)) (Neg.neg ∘ x.moveLeft) := by
  rw [neg_def]; rfl

@[simp]
theorem moveLeft_neg (x : SGame) (n) : (-x).moveLeft n = -x.moveRight (cast (by simp) n) := by
  apply congr_heq (moveLeft_neg_heq x); rw [heq_cast_iff_heq]

@[simp]
theorem moveRight_neg (x : SGame) (n) : (-x).moveRight n = -x.moveLeft (cast (by simp) n) := by
  apply congr_heq (moveRight_neg_heq x); rw [heq_cast_iff_heq]

@[simp]
theorem toIGame_neg (x : SGame) : toIGame (-x) = -toIGame x := by
  ext
  on_goal 1 =>
    simp only [leftMoves_toIGame, IGame.leftMoves_neg, rightMoves_toIGame,
      Set.mem_range, Set.mem_neg]
    have H : Fin (-x).leftMoves = Fin x.rightMoves := by rw [leftMoves_neg]
  on_goal 2 =>
    simp only [rightMoves_toIGame, IGame.rightMoves_neg, leftMoves_toIGame,
      Set.mem_range, Set.mem_neg]
    have H : Fin (-x).rightMoves = Fin x.leftMoves := by rw [rightMoves_neg]
  all_goals
    rw [← (Equiv.cast H).exists_congr_right]
    simp only [Function.comp_apply, moveLeft_neg, moveRight_neg, Equiv.cast_apply]
    congr! 2
    rw [← neg_inj, toIGame_neg, neg_neg]
termination_by x
decreasing_by sgame_wf

/-! #### Addition -/

private def add' (x y : SGame.{u}) : SGame.{u} :=
  mk (x.leftMoves + y.leftMoves) (x.rightMoves + y.rightMoves)
    (fun m ↦ (finSumFinEquiv.symm m).rec
      (fun n ↦ add' (x.moveLeft n) y) (fun n ↦ add' x (y.moveLeft n)))
    (fun m ↦ (finSumFinEquiv.symm m).rec
      (fun n ↦ add' (x.moveRight n) y) (fun n ↦ add' x (y.moveRight n)))
termination_by (x, y)
decreasing_by sgame_wf

instance : Add SGame := ⟨add'⟩
instance : Sub SGame := ⟨fun x y ↦ x + -y⟩

theorem add_def (x y : SGame) : x + y =
    mk (x.leftMoves + y.leftMoves) (x.rightMoves + y.rightMoves)
      (fun m ↦ (finSumFinEquiv.symm m).rec
        (fun n ↦ x.moveLeft n + y) (fun n ↦ x + y.moveLeft n))
      (fun m ↦ (finSumFinEquiv.symm m).rec
        (fun n ↦ x.moveRight n + y) (fun n ↦ x + y.moveRight n)) := by
  change add' x y = _
  rw [add']
  rfl

@[simp]
theorem leftMoves_add (x y : SGame) : (x + y).leftMoves = x.leftMoves + y.leftMoves := by
  rw [add_def]; rfl

@[simp]
theorem rightMoves_add (x y : SGame) : (x + y).rightMoves = x.rightMoves + y.rightMoves := by
  rw [add_def]; rfl

theorem moveLeft_add_heq (x y : SGame) :
  HEq (moveLeft (x + y))
    (fun m ↦ (finSumFinEquiv.symm m).rec (motive := fun _ ↦ SGame)
      (fun n ↦ x.moveLeft n + y) (fun n ↦ x + y.moveLeft n)) := by
  rw [add_def]; rfl

theorem moveRight_add_heq (x y : SGame) :
  HEq (moveRight (x + y))
    (fun m ↦ (finSumFinEquiv.symm m).rec (motive := fun _ ↦ SGame)
      (fun n ↦ x.moveRight n + y) (fun n ↦ x + y.moveRight n)) := by
  rw [add_def]; rfl

@[simp]
theorem moveLeft_add (x y : SGame) (n) :
    (x + y).moveLeft n = (finSumFinEquiv.symm (cast (by simp) n)).rec
      (fun n ↦ x.moveLeft n + y) (fun n ↦ x + y.moveLeft n) := by
  apply congr_heq (moveLeft_add_heq x y); rw [heq_cast_iff_heq]

@[simp]
theorem moveRight_add (x y : SGame) (n) :
    (x + y).moveRight n = (finSumFinEquiv.symm (cast (by simp) n)).rec
      (fun n ↦ x.moveRight n + y) (fun n ↦ x + y.moveRight n) := by
  apply congr_heq (moveRight_add_heq x y); rw [heq_cast_iff_heq]

@[simp]
theorem toIGame_add (x y : SGame) : toIGame (x + y) = toIGame x + toIGame y := by
  ext
  on_goal 1 =>
    simp only [leftMoves_toIGame, Set.mem_range]
    let e : Fin (x + y).leftMoves ≃ Fin x.leftMoves ⊕ Fin y.leftMoves :=
      (Equiv.cast (by simp)).trans finSumFinEquiv.symm
  on_goal 2 =>
    simp only [rightMoves_toIGame, Set.mem_range]
    let e : Fin (x + y).rightMoves ≃ Fin x.rightMoves ⊕ Fin y.rightMoves :=
      (Equiv.cast (by simp)).trans finSumFinEquiv.symm
  all_goals
    rw [e.exists_congr_left]
    simp [e]
    congr! 4 <;> rw [toIGame_add]
termination_by (x, y)
decreasing_by sgame_wf

@[simp]
theorem toIGame_sub (x y : SGame) : toIGame (x - y) = toIGame x - toIGame y :=
  show toIGame (x + -y) = _ by simp; rfl

/-! #### Multiplication -/

private def mul' (x y : SGame.{u}) : SGame.{u} :=
  mk (x.leftMoves * y.leftMoves + x.rightMoves * y.rightMoves)
    (x.leftMoves * y.rightMoves + x.rightMoves * y.leftMoves)
    (fun m ↦ (finSumFinEquiv.symm m).rec
      (fun n ↦ let a := finProdFinEquiv.symm n;
        mul' (x.moveLeft a.1) y + mul' x (y.moveLeft a.2) -
          mul' (x.moveLeft a.1) (y.moveLeft a.2))
      (fun n ↦ let a := finProdFinEquiv.symm n;
        mul' (x.moveRight a.1) y + mul' x (y.moveRight a.2) -
          mul' (x.moveRight a.1) (y.moveRight a.2)))
    (fun m ↦ (finSumFinEquiv.symm m).rec
      (fun n ↦ let a := finProdFinEquiv.symm n;
        mul' (x.moveLeft a.1) y + mul' x (y.moveRight a.2) -
          mul' (x.moveLeft a.1) (y.moveRight a.2))
      (fun n ↦ let a := finProdFinEquiv.symm n;
        mul' (x.moveRight a.1) y + mul' x (y.moveLeft a.2) -
          mul' (x.moveRight a.1) (y.moveLeft a.2)))
termination_by (x, y)
decreasing_by sgame_wf

instance : Mul SGame := ⟨mul'⟩

theorem mul_def (x y : SGame) : x * y =
  mk (x.leftMoves * y.leftMoves + x.rightMoves * y.rightMoves)
    (x.leftMoves * y.rightMoves + x.rightMoves * y.leftMoves)
    (fun m ↦ (finSumFinEquiv.symm m).rec
      (fun n ↦ let a := finProdFinEquiv.symm n;
        x.moveLeft a.1 * y + x * y.moveLeft a.2 - x.moveLeft a.1 * y.moveLeft a.2)
      (fun n ↦ let a := finProdFinEquiv.symm n;
        x.moveRight a.1 * y + x * y.moveRight a.2 - x.moveRight a.1 * y.moveRight a.2))
    (fun m ↦ (finSumFinEquiv.symm m).rec
      (fun n ↦ let a := finProdFinEquiv.symm n;
        x.moveLeft a.1 * y + x * y.moveRight a.2 - x.moveLeft a.1 * y.moveRight a.2)
      (fun n ↦ let a := finProdFinEquiv.symm n;
        x.moveRight a.1 * y + x * y.moveLeft a.2 - x.moveRight a.1 * y.moveLeft a.2)) := by
  change mul' x y = _
  rw [mul']
  rfl

@[simp]
theorem leftMoves_mul (x y : SGame) : (x * y).leftMoves =
    x.leftMoves * y.leftMoves + x.rightMoves * y.rightMoves := by
  rw [mul_def]; rfl

@[simp]
theorem rightMoves_mul (x y : SGame) : (x * y).rightMoves =
    x.leftMoves * y.rightMoves + x.rightMoves * y.leftMoves := by
  rw [mul_def]; rfl

theorem moveLeft_mul_heq (x y : SGame) :
  HEq (moveLeft (x * y))
    (fun m ↦ (finSumFinEquiv.symm m).rec (motive := fun _ ↦ SGame)
      (fun n ↦ let a := finProdFinEquiv.symm n;
        x.moveLeft a.1 * y + x * y.moveLeft a.2 - x.moveLeft a.1 * y.moveLeft a.2)
      (fun n ↦ let a := finProdFinEquiv.symm n;
        x.moveRight a.1 * y + x * y.moveRight a.2 - x.moveRight a.1 * y.moveRight a.2)) := by
  rw [mul_def]; rfl

theorem moveRight_mul_heq (x y : SGame) :
  HEq (moveRight (x * y))
    (fun m ↦ (finSumFinEquiv.symm m).rec (motive := fun _ ↦ SGame)
      (fun n ↦ let a := finProdFinEquiv.symm n;
        x.moveLeft a.1 * y + x * y.moveRight a.2 - x.moveLeft a.1 * y.moveRight a.2)
      (fun n ↦ let a := finProdFinEquiv.symm n;
        x.moveRight a.1 * y + x * y.moveLeft a.2 - x.moveRight a.1 * y.moveLeft a.2)) := by
  rw [mul_def]; rfl

@[simp]
theorem moveLeft_mul (x y : SGame) (n) :
    (x * y).moveLeft n = (finSumFinEquiv.symm (cast (by simp) n)).rec
      (fun n ↦ let a := finProdFinEquiv.symm n;
        x.moveLeft a.1 * y + x * y.moveLeft a.2 - x.moveLeft a.1 * y.moveLeft a.2)
      (fun n ↦ let a := finProdFinEquiv.symm n;
        x.moveRight a.1 * y + x * y.moveRight a.2 - x.moveRight a.1 * y.moveRight a.2)  := by
  apply congr_heq (moveLeft_mul_heq x y); rw [heq_cast_iff_heq]

@[simp]
theorem moveRight_mul (x y : SGame) (n) :
    (x * y).moveRight n = (finSumFinEquiv.symm (cast (by simp) n)).rec
      (fun n ↦ let a := finProdFinEquiv.symm n;
        x.moveLeft a.1 * y + x * y.moveRight a.2 - x.moveLeft a.1 * y.moveRight a.2)
      (fun n ↦ let a := finProdFinEquiv.symm n;
        x.moveRight a.1 * y + x * y.moveLeft a.2 - x.moveRight a.1 * y.moveLeft a.2) := by
  apply congr_heq (moveRight_mul_heq x y); rw [heq_cast_iff_heq]

@[simp]
theorem toIGame_mul (x y : SGame) : toIGame (x * y) = toIGame x * toIGame y := by
  ext z
  on_goal 1 =>
    simp only [leftMoves_toIGame, Set.mem_range]
    let e : Fin (x * y).leftMoves ≃
      Fin x.leftMoves × Fin y.leftMoves ⊕ Fin x.rightMoves × Fin y.rightMoves :=
    (Equiv.cast (by simp)).trans <|
      finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm)
    rw [e.exists_congr_left]
    simp [e, -finProdFinEquiv_symm_apply]
    trans
      (∃ m n, .mulOption x.toIGame y.toIGame (x.moveLeft m).toIGame (y.moveLeft n).toIGame = z) ∨
      (∃ m n, .mulOption x.toIGame y.toIGame (x.moveRight m).toIGame (y.moveRight n).toIGame = z)
  on_goal 3 =>
    simp only [rightMoves_toIGame, Set.mem_range]
    let e : Fin (x * y).rightMoves ≃
      Fin x.leftMoves × Fin y.rightMoves ⊕ Fin x.rightMoves × Fin y.leftMoves :=
    (Equiv.cast (by simp)).trans <|
      finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm)
    rw [e.exists_congr_left]
    simp [e, -finProdFinEquiv_symm_apply]
    trans
      (∃ m n, .mulOption x.toIGame y.toIGame (x.moveLeft m).toIGame (y.moveRight n).toIGame = z) ∨
      (∃ m n, .mulOption x.toIGame y.toIGame (x.moveRight m).toIGame (y.moveLeft n).toIGame = z)
  any_goals
    congr! 6
    all_goals
      rw [toIGame_mul, toIGame_mul, toIGame_mul]
      simp [IGame.mulOption]
  all_goals aesop (add simp [IGame.mulOption])
termination_by (x, y)
decreasing_by sgame_wf

end SGame

/-! ### Short instances -/

namespace IGame

/-- A short game is one with finitely many subpositions.

Short games are those for which we can feasibly perform computations. To enable this, this typeclass
provides a term of an auxiliary type `SGame`, which mimics `PGame` but restricts the indexing types
to `Fin n`, alongside a proof that this term, casted in the obvious way to `IGame`, represents the
game in question. All computations can then go through `SGame`.

Unfortunately, well-founded recursion and reducibility don't mix very well in Lean. As such, we must
often rely on `native_decide` to make use of this typeclass for computation.

A prototypical instance looks something like this:

```
example : IGame.Short {{0, 2, 5} | {3, -1, 7}}ᴵ where
  toSGame := .ofLists [0, 2, 5] [3, -1, 7]
  toIGame_toSGame := by aesop
```
-/
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

instance (x y : IGame) [Short x] [Short y] : Decidable (x = y) :=
  decidable_of_iff ((toSGame x).toIGame = (toSGame y).toIGame) (by simp)

instance : Short 0 := ⟨0, SGame.toIGame_zero⟩
instance : Short 1 := ⟨1, SGame.toIGame_one⟩

-- These should be computable: https://github.com/leanprover/lean4/pull/7283
noncomputable instance (n : ℕ) : Short n := ⟨n, SGame.toIGame_natCast n⟩
noncomputable instance (n : ℕ) [n.AtLeastTwo] : Short ofNat(n) := inferInstanceAs (Short n)

instance (x : IGame) [Short x] : Short (-x) := ⟨-toSGame x, by simp⟩
instance (x y : IGame) [Short x] [Short y] : Short (x + y) := ⟨toSGame x + toSGame y, by simp⟩
instance (x y : IGame) [Short x] [Short y] : Short (x - y) := ⟨toSGame x - toSGame y, by simp⟩
instance (x y : IGame) [Short x] [Short y] : Short (x * y) := ⟨toSGame x * toSGame y, by simp⟩

end Short

-- TODO: add some actual theorems

proof_wanted exists_lt_natCast_of_short (x : IGame) [Short x] : ∃ n : ℕ, x < n
proof_wanted exists_neg_natCast_lt_of_short (x : IGame) [Short x] : ∃ n : ℕ, -n < x

proof_wanted short_iff_finite_subposition (x : IGame) :
    Nonempty (Short x) ↔ Set.Finite {y | Subposition y x}

end IGame

section Test

example : (0 : IGame) < 1 := by decide
example : (-1 : IGame) < 0 := by native_decide
example : (0 : IGame) < 1 + 1 := by native_decide
example : (-1 : IGame) + 1 ≠ 0 := by native_decide
--example : (2 : IGame) < (5 : IGame) := by native_decide

end Test
