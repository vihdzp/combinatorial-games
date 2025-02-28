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

def ofLists (l m : List SGame) : SGame :=
  mk l.length m.length l.get m.get

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

/-

theorem ext_iff {x y : SGame} : x = y ↔
    ∃ (hl : x.LeftMoves = y.LeftMoves) (hr : x.RightMoves = y.RightMoves),
      (∀ i, x.moveLeft i = y.moveLeft (i.cast hl)) ∧
      (∀ i, x.moveRight i = y.moveRight (i.cast hr)) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨hl₁, hr₁, hl₂, hr₂⟩
    cases x
    cases y
    simp_rw [LeftMoves, RightMoves] at hl₁ hr₁
    subst_vars
    congr
    exacts [funext hl₂, funext hr₂]

def decidableEq' : DecidableEq SGame := fun x y ↦
  let _ : Π i hl, Decidable (x.moveLeft i = y.moveLeft (Fin.cast hl i)) :=
    fun _ _ ↦ decidableEq' ..
  let _ : Π i hr, Decidable (x.moveRight i = y.moveRight (Fin.cast hr i)) :=
    fun _ _ ↦ decidableEq' ..
  decidable_of_iff' _ ext_iff
termination_by x y => (x, y)
decreasing_by all_goals sorry-/

#exit
def leftMoves (x : SGame) : Finset SGame := by
  cases x with | mk α β =>
    apply Fintype.range
    sorry


end SGame

#exit
namespace IGame

inductive Short : IGame.{u} → Type (u + 1) where
  /-- If `s` and `t` are finsets of short games, then `{s | t}ᴵ` is short.

  You should prefer the `Short.mk` constructor. -/
  | mk' (s : Finset IGame) (t : Finset IGame) (hs : Π y ∈ s, Short y) (ht : Π y ∈ t, Short y) :
    Short {s | t}ᴵ

attribute [class] Short

namespace Short

/-- If `s` and `t` are finsets of short games, then `{s | t}ᴵ` is short. -/
def mk (s : Finset IGame) (t : Finset IGame) (hs : Π y ∈ s, Short y) (ht : Π y ∈ t, Short y)
    {x : IGame} (h : {s | t}ᴵ = x) : Short x :=
  cast (by rw [h]) (Short.mk' s t hs ht)

/-- The left moves of a short game, as a `Finset`. -/
protected def leftMoves (x : IGame) [h : Short x] : Finset IGame :=
  h.casesOn fun s _ _ _ ↦ s

/-- The right moves of a short game, as a `Finset`. -/
protected def rightMoves (x : IGame) [h : Short x] : Finset IGame :=
  h.casesOn fun _ t _ _ ↦ t

@[simp]
theorem leftMoves_mk' (s : Finset IGame) (t : Finset IGame)
    (hs : Π y ∈ s, Short y) (ht : Π y ∈ t, Short y) : @Short.leftMoves _ (mk' s t hs ht) = s :=
  rfl

@[simp]
theorem rightMoves_mk' (s : Finset IGame) (t : Finset IGame)
    (hs : Π y ∈ s, Short y) (ht : Π y ∈ t, Short y) : @Short.rightMoves _ (mk' s t hs ht) = t :=
  rfl

@[simp]
theorem leftMoves_mk (s : Finset IGame) (t : Finset IGame)
    (hs : Π y ∈ s, Short y) (ht : Π y ∈ t, Short y) {x : IGame} (h : {s | t}ᴵ = x) :
    @Short.leftMoves _ (mk s t hs ht h) = s := by
  subst h
  rfl

@[simp]
theorem rightMoves_mk (s : Finset IGame) (t : Finset IGame)
    (hs : Π y ∈ s, Short y) (ht : Π y ∈ t, Short y) {x : IGame} (h : {s | t}ᴵ = x) :
    @Short.rightMoves _ (mk s t hs ht h) = t := by
  subst h
  rfl

@[simp]
theorem leftMoves_eq (x : IGame) [h : Short x] : Short.leftMoves x = x.leftMoves := by
  cases h; simp

@[simp]
theorem rightMoves_eq (x : IGame) [h : Short x] : Short.rightMoves x = x.rightMoves := by
  cases h; simp

@[simp]
theorem mem_leftMoves_iff {x y : IGame} [Short x] : y ∈ Short.leftMoves x ↔ y ∈ x.leftMoves := by
  rw [← Finset.mem_coe, leftMoves_eq]

@[simp]
theorem mem_rightMoves_iff {x y : IGame} [Short x] : y ∈ Short.rightMoves x ↔ y ∈ x.rightMoves := by
  rw [← Finset.mem_coe, rightMoves_eq]

/-- Any left move from a short game yields a short game. -/
def ofMemLeftMoves {x y : IGame} [hx : Short x] (h : y ∈ x.leftMoves) : Short y :=
  let f : y ∈ Short.leftMoves x → Short y := hx.casesOn fun _ _ hs _ ↦ hs y
  f (mem_leftMoves_iff.2 h)

/-- Any right move from a short game yields a short game. -/
def ofMemRightMoves {x y : IGame} [hx : Short x] (h : y ∈ x.rightMoves) : Short y :=
  let f : y ∈ Short.rightMoves x → Short y := hx.casesOn fun _ _ _ ht ↦ ht y
  f (mem_rightMoves_iff.2 h)

instance (x : IGame) [Short x] : Fintype x.leftMoves where
  elems := (Short.leftMoves x).attach.map
    ⟨fun x ↦ ⟨x.1, mem_leftMoves_iff.1 x.2⟩, fun a b ↦ by simpa using Subtype.eq⟩
  complete := by simp

instance (x : IGame) [Short x] : Fintype x.rightMoves where
  elems := (Short.rightMoves x).attach.map
    ⟨fun x ↦ ⟨x.1, mem_rightMoves_iff.1 x.2⟩, fun a b ↦ by simpa using Subtype.eq⟩
  complete := by simp

private theorem heq_mk' {x : IGame} (h : Short x) :
    HEq h (mk' (Short.leftMoves x) (Short.rightMoves x)
      (fun _ hy ↦ ofMemLeftMoves  (mem_leftMoves_iff.1 hy))
      (fun _ hy ↦ ofMemRightMoves (mem_rightMoves_iff.1 hy))) := by
  cases h; rfl

private theorem subsingleton' {x : IGame} (a : Short x) (b : Short x) : a = b := by
  apply eq_of_heq <| (heq_mk' a).trans (.trans _ (heq_mk' b).symm)
  congr! 1
  · rw [← Finset.coe_inj, leftMoves_eq, leftMoves_eq]
  · rw [← Finset.coe_inj, rightMoves_eq, rightMoves_eq]
  all_goals
  · apply Function.hfunext rfl fun y z h ↦ ?_
    cases h
    refine Function.hfunext ?_ fun hy _ ↦ ?_
    · simp
    · simp only [mem_leftMoves_iff, mem_rightMoves_iff] at hy
      simpa using subsingleton' ..
termination_by x
decreasing_by all_goals simp_all; subst_vars; igame_wf

instance (x : IGame) : Subsingleton (Short x) :=
  ⟨subsingleton'⟩

protected instance zero : Short 0 :=
  .mk ∅ ∅
    (fun _ h ↦ (Finset.not_mem_empty _ h).elim)
    (fun _ h ↦ (Finset.not_mem_empty _ h).elim)
    (by simp [zero_def])

@[simp] protected theorem leftMoves_zero : Short.leftMoves 0 = ∅ := leftMoves_mk ..
@[simp] protected theorem rightMoves_zero : Short.rightMoves 0 = ∅ := rightMoves_mk ..

-- This shouldn't be noncomputable... that's bad.
protected instance one : Short 1 :=
  .mk {0} ∅
    (fun _ h ↦ cast (by simp_all) Short.zero)
    (fun _ h ↦ (Finset.not_mem_empty _ h).elim)
    (by simp [one_def])

end Short

/-example (x : IGame) (h : Short x) : sorry := by
  cases h-/

#exit

end IGame
