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

-- TODO: docstring
def IsOption (x y : IGame) : Prop :=
  x ∈ y.leftMoves ∪ y.rightMoves

theorem IsOption.of_mem_leftMoves {x y : IGame} : x ∈ y.leftMoves → IsOption x y := Or.inl
theorem IsOption.of_mem_rightMoves {x y : IGame} : x ∈ y.rightMoves → IsOption x y := Or.inr

-- TODO: is there some more general theorem about well-founded relations on quotients
-- that we could use here?
theorem isOption_wf : WellFounded IsOption := by
  suffices ∀ x, Acc IsOption (mk x) from ⟨ind this⟩
  intro x
  induction x using PGame.moveRecOn with
  | IH x hl hr =>
    constructor
    rintro ⟨y⟩ (h | h) <;>
    obtain ⟨_, ⟨i, rfl⟩, (hi : _ = Quot.mk _ _)⟩ := h
    exacts [hi ▸ hl i, hi ▸ hr i]

instance : IsWellFounded _ IsOption := ⟨isOption_wf⟩

/-- **Conway recursion**: build data for a game by recursively building it on its
left and right sets.

See `ofSetsRecOn` for an alternate form. -/
@[elab_as_elim]
noncomputable def moveRecOn {P : IGame → Sort*} (x)
    (H : Π x, (Π y ∈ x.leftMoves, P y) → (Π y ∈ x.rightMoves, P y) → P x) : P x :=
  isOption_wf.recursion x fun x IH ↦
    H x (fun _ h ↦ IH _ (.of_mem_leftMoves h)) (fun _ h ↦ IH _ (.of_mem_rightMoves h))

@[simp]
theorem moveRecOn_eq {P : IGame → Sort*} (x)
    (H : Π x, (Π y ∈ x.leftMoves, P y) → (Π y ∈ x.rightMoves, P y) → P x) :
    moveRecOn x H = H x (fun y _ ↦ moveRecOn y H) (fun y _ ↦ moveRecOn y H) :=
  isOption_wf.fix_eq ..

-- TODO: docstring
def Subsequent : IGame → IGame → Prop :=
  Relation.TransGen IsOption

theorem Subsequent.of_mem_leftMoves {x y : IGame} (h : x ∈ y.leftMoves) : Subsequent x y :=
  Relation.TransGen.single (.of_mem_leftMoves h)

theorem Subsequent.of_mem_rightMoves {x y : IGame} (h : x ∈ y.rightMoves) : Subsequent x y :=
  Relation.TransGen.single (.of_mem_rightMoves h)

theorem Subsequent.trans {x y z : IGame} (h₁ : Subsequent x y) (h₂ : Subsequent y z) :
    Subsequent x z :=
  Relation.TransGen.trans h₁ h₂

instance : IsTrans _ Subsequent := inferInstanceAs (IsTrans _ (Relation.TransGen _))
instance : IsWellFounded _ Subsequent := inferInstanceAs (IsWellFounded _ (Relation.TransGen _))
instance : WellFoundedRelation IGame := ⟨Subsequent, instIsWellFoundedSubsequent.wf⟩

/-- Construct an `IGame` from its left and right sets. -/
noncomputable def ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] : IGame.{u} :=
  mk <| .mk (Shrink s) (Shrink t)
    (out ∘ Subtype.val ∘ (equivShrink s).symm) (out ∘ Subtype.val ∘ (equivShrink t).symm)

@[simp]
theorem leftMoves_ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] :
    (ofSets s t).leftMoves = s := by
  ext; simp [ofSets, range_comp, Equiv.range_eq_univ]

@[simp]
theorem rightMoves_ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] :
    (ofSets s t).rightMoves = t := by
  ext; simp [ofSets, range_comp, Equiv.range_eq_univ]

@[simp]
theorem ofSets_leftMoves_rightMoves (x : IGame) : ofSets x.leftMoves x.rightMoves = x := by
  ext <;> simp

/-- **Conway recursion**: build data for a game by recursively building it on its
left and right sets.

See `moveRecOn` for an alternate form. -/
@[elab_as_elim]
noncomputable def ofSetsRecOn {P : IGame.{u} → Sort*} (x)
    (H : Π (s t : Set _) [Small.{u} s] [Small.{u} t],
      (Π x ∈ s, P x) → (Π x ∈ t, P x) → P (ofSets s t)) : P x :=
  cast (by simp) <| moveRecOn (P := fun x ↦ P (ofSets x.leftMoves x.rightMoves)) x fun x IHl IHr ↦
    H _ _ (fun y hy ↦ cast (by simp) (IHl y hy)) (fun y hy ↦ cast (by simp) (IHr y hy))

@[simp]
theorem ofSetsRecOn_ofSets {P : IGame.{u} → Sort*} (s t : Set IGame) [Small.{u} s] [Small.{u} t]
    (H : Π (s t : Set _) [Small.{u} s] [Small.{u} t],
      (Π x ∈ s, P x) → (Π x ∈ t, P x) → P (ofSets s t)) :
    ofSetsRecOn (ofSets s t) H =
      H _ _ (fun y _ ↦ ofSetsRecOn y H) (fun y _ ↦ ofSetsRecOn y H) := by
  rw [ofSetsRecOn, cast_eq_iff_heq, moveRecOn_eq]
  congr
  any_goals simp
  all_goals
    refine Function.hfunext rfl fun x _ h ↦ ?_
    cases h
    refine Function.hfunext ?_ fun _ _ _ ↦ ?_
    · simp
    · rw [ofSetsRecOn, cast_heq_iff_heq, heq_cast_iff_heq]


end IGame
