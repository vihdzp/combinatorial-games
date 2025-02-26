/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.PGame
import Mathlib.Logic.Small.Set

universe u

open PGame

/-- Games up to identity.

TODO: write proper docstring. -/
def IGame : Type (u + 1) :=
  Quotient identicalSetoid

namespace IGame

-- TODO: docstring
def mk (x : PGame) : IGame := Quotient.mk _ x
theorem mk_eq_mk {x y : PGame} : mk x = mk y ↔ x ≡ y := Quotient.eq

@[cases_eliminator]
theorem ind {P : IGame → Prop} (H : ∀ y, P (mk y)) (x : IGame) : P x :=
  Quotient.ind H x

alias ⟨_, mk_eq⟩ := mk_eq_mk
alias _root_.PGame.Identical.mk_eq := mk_eq

-- TODO: docstring
def lift {α : Sort*} (f : PGame → α) (hf : ∀ x y, x ≡ y → f x = f y) : IGame → α :=
  Quotient.lift f hf

def leftMoves : IGame → Set IGame := by
  refine lift (fun x ↦ mk '' Set.range x.moveLeft) fun x y h ↦ ?_
  ext z
  simp_rw [Set.mem_image, Set.mem_range, exists_exists_eq_and]
  constructor <;> rintro ⟨i, rfl⟩
  · obtain ⟨j, hj⟩ := h.moveLeft i
    exact ⟨j, hj.mk_eq.symm⟩
  · obtain ⟨j, hj⟩ := h.moveLeft_symm i
    exact ⟨j, hj.mk_eq⟩

def rightMoves : IGame → Set IGame := by
  refine lift (fun x ↦ mk '' Set.range x.moveRight) fun x y h ↦ ?_
  ext z
  simp_rw [Set.mem_image, Set.mem_range, exists_exists_eq_and]
  constructor <;> rintro ⟨i, rfl⟩
  · obtain ⟨j, hj⟩ := h.moveRight i
    exact ⟨j, hj.mk_eq.symm⟩
  · obtain ⟨j, hj⟩ := h.moveRight_symm i
    exact ⟨j, hj.mk_eq⟩

@[simp] theorem leftMoves_mk (x : PGame) : leftMoves (mk x) = mk '' Set.range x.moveLeft := rfl
@[simp] theorem rightMoves_mk (x : PGame) : rightMoves (mk x) = mk '' Set.range x.moveRight := rfl

instance (x : IGame.{u}) : Small.{u} x.leftMoves := by
  cases x
  rw [leftMoves_mk]
  infer_instance

instance (x : IGame.{u}) : Small.{u} x.rightMoves := by
  cases x
  rw [rightMoves_mk]
  infer_instance

--noncomputable def ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] : IGame.{u} :=


end IGame
