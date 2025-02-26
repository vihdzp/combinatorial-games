/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.PGame
import Mathlib.Logic.Small.Set

universe u

open PGame Set

/-- Games up to identity.

TODO: write proper docstring. -/
def IGame : Type (u + 1) :=
  Quotient identicalSetoid

namespace IGame

-- TODO: docstring
def mk (x : PGame) : IGame := Quotient.mk _ x
theorem mk_eq_mk {x y : PGame} : mk x = mk y ↔ x ≡ y := Quotient.eq

alias ⟨_, mk_eq⟩ := mk_eq_mk
alias _root_.PGame.Identical.mk_eq := mk_eq

@[cases_eliminator]
theorem ind {P : IGame → Prop} (H : ∀ y, P (mk y)) (x : IGame) : P x :=
  Quotient.ind H x

-- TODO: docstring
noncomputable def out (x : IGame) : PGame :=
  Quotient.out x

@[simp]
theorem out_eq (x : IGame) : mk x.out = x :=
  Quotient.out_eq x

-- TODO: docstring
def lift {α : Sort*} (f : PGame → α) (hf : ∀ x y, x ≡ y → f x = f y) : IGame → α :=
  Quotient.lift f hf

/-- The set of left moves of the game. -/
def leftMoves : IGame → Set IGame := by
  refine lift (fun x ↦ mk '' range x.moveLeft) fun x y h ↦ ?_
  ext z
  simp_rw [mem_image, mem_range, exists_exists_eq_and]
  constructor <;> rintro ⟨i, rfl⟩
  · obtain ⟨j, hj⟩ := h.moveLeft i
    exact ⟨j, hj.mk_eq.symm⟩
  · obtain ⟨j, hj⟩ := h.moveLeft_symm i
    exact ⟨j, hj.mk_eq⟩

/-- The set of right moves of the game. -/
def rightMoves : IGame → Set IGame := by
  refine lift (fun x ↦ mk '' range x.moveRight) fun x y h ↦ ?_
  ext z
  simp_rw [mem_image, mem_range, exists_exists_eq_and]
  constructor <;> rintro ⟨i, rfl⟩
  · obtain ⟨j, hj⟩ := h.moveRight i
    exact ⟨j, hj.mk_eq.symm⟩
  · obtain ⟨j, hj⟩ := h.moveRight_symm i
    exact ⟨j, hj.mk_eq⟩

@[simp] theorem leftMoves_mk (x : PGame) : leftMoves (mk x) = mk '' range x.moveLeft := rfl
@[simp] theorem rightMoves_mk (x : PGame) : rightMoves (mk x) = mk '' range x.moveRight := rfl

instance (x : IGame.{u}) : Small.{u} x.leftMoves := by
  cases x
  rw [leftMoves_mk]
  infer_instance

instance (x : IGame.{u}) : Small.{u} x.rightMoves := by
  cases x
  rw [rightMoves_mk]
  infer_instance

@[ext]
theorem ext {x y : IGame} (hl : x.leftMoves = y.leftMoves) (hr : x.rightMoves = y.rightMoves) :
    x = y := by
  cases x with | H x =>
  cases y with | H y =>
  dsimp at hl hr
  refine (identical_iff.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩).mk_eq <;> intro i
  · obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hl ▸ mem_image_of_mem mk (mem_range_self (f := x.moveLeft) i)
    exact ⟨j, mk_eq_mk.1 hj.symm⟩
  · obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hl ▸ mem_image_of_mem mk (mem_range_self (f := y.moveLeft) i)
    exact ⟨j, mk_eq_mk.1 hj⟩
  · obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hr ▸ mem_image_of_mem mk (mem_range_self (f := x.moveRight) i)
    exact ⟨j, mk_eq_mk.1 hj.symm⟩
  · obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hr ▸ mem_image_of_mem mk (mem_range_self (f := y.moveRight) i)
    exact ⟨j, mk_eq_mk.1 hj⟩

/-- Construct an `IGame` from its left and right sets. -/
noncomputable def ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] : IGame.{u} :=
  mk <| .mk (Shrink s) (Shrink t)
    (out ∘ Subtype.val ∘ (equivShrink s).symm) (out ∘ Subtype.val ∘ (equivShrink t).symm)

@[simp]
theorem leftMoves_ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] :
    (ofSets s t).leftMoves = s := by
  ext y
  simp [ofSets, range_comp, Equiv.range_eq_univ]

@[simp]
theorem rightMoves_ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] :
    (ofSets s t).rightMoves = t := by
  ext y
  simp [ofSets, range_comp, Equiv.range_eq_univ]

end IGame
