/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.PGame
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Logic.Small.Set

universe u

-- All computation should be done through `IGame.Short`.
noncomputable section

open PGame Set Pointwise

/-- Games up to identity.

TODO: write proper docstring. -/
def IGame : Type (u + 1) :=
  Quotient identicalSetoid

namespace IGame

/-! ### Game moves -/

/-- The quotient map from `PGame` into `IGame`. -/
def mk (x : PGame) : IGame := Quotient.mk _ x
theorem mk_eq_mk {x y : PGame} : mk x = mk y ↔ x ≡ y := Quotient.eq

alias ⟨_, mk_eq⟩ := mk_eq_mk
alias _root_.PGame.Identical.mk_eq := mk_eq

@[cases_eliminator]
theorem ind {P : IGame → Prop} (H : ∀ y, P (mk y)) (x : IGame) : P x :=
  Quotient.ind H x

/-- Choose an element of the equivalence class using the axiom of choice. -/
def out (x : IGame) : PGame :=
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

/-- `IsOption x y` means that `x` is either a left or a right move for `y`. -/
def IsOption (x y : IGame) : Prop :=
  x ∈ y.leftMoves ∪ y.rightMoves

theorem IsOption.of_mem_leftMoves {x y : IGame} : x ∈ y.leftMoves → IsOption x y := .inl
theorem IsOption.of_mem_rightMoves {x y : IGame} : x ∈ y.rightMoves → IsOption x y := .inr

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
def moveRecOn {P : IGame → Sort*} (x)
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

/-- Construct an `IGame` from its left and right sets.

This is given notation `{s | t}ᴳ`, where the superscript G is to disambiguate
from set builder notation. -/
def ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] : IGame.{u} :=
  mk <| .mk (Shrink s) (Shrink t)
    (out ∘ Subtype.val ∘ (equivShrink s).symm) (out ∘ Subtype.val ∘ (equivShrink t).symm)

-- TODO: can a macro expert verify this makes sense?
@[inherit_doc ofSets] macro "{" s:term " | " t:term "}ᴳ" : term => `(ofSets $s $t)

@[simp]
theorem leftMoves_ofSets (s t : Set _) [Small.{u} s] [Small.{u} t] : {s | t}ᴳ.leftMoves = s := by
  ext; simp [ofSets, range_comp, Equiv.range_eq_univ]

@[simp]
theorem rightMoves_ofSets (s t : Set _) [Small.{u} s] [Small.{u} t] : {s | t}ᴳ.rightMoves = t := by
  ext; simp [ofSets, range_comp, Equiv.range_eq_univ]

@[simp]
theorem ofSets_leftMoves_rightMoves (x : IGame) : ofSets x.leftMoves x.rightMoves = x := by
  ext <;> simp

@[simp]
theorem ofSets_inj {s₁ s₂ t₁ t₂ : Set _} [Small s₁] [Small s₂] [Small t₁] [Small t₂] :
    ofSets s₁ t₁ = ofSets s₂ t₂ ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp [IGame.ext_iff]

/-- **Conway recursion**: build data for a game by recursively building it on its
left and right sets.

See `moveRecOn` for an alternate form. -/
@[elab_as_elim]
def ofSetsRecOn {P : IGame.{u} → Sort*} (x)
    (H : Π (s t : Set _) [Small s] [Small t], (Π x ∈ s, P x) → (Π x ∈ t, P x) → P {s | t}ᴳ) : P x :=
  cast (by simp) <| moveRecOn (P := fun x ↦ P {x.leftMoves | x.rightMoves}ᴳ) x fun x IHl IHr ↦
    H _ _ (fun y hy ↦ cast (by simp) (IHl y hy)) (fun y hy ↦ cast (by simp) (IHr y hy))

@[simp]
theorem ofSetsRecOn_ofSets {P : IGame.{u} → Sort*} (s t : Set IGame) [Small.{u} s] [Small.{u} t]
    (H : Π (s t : Set _) [Small s] [Small t], (Π x ∈ s, P x) → (Π x ∈ t, P x) → P {s | t}ᴳ) :
    ofSetsRecOn {s | t}ᴳ H = H _ _ (fun y _ ↦ ofSetsRecOn y H) (fun y _ ↦ ofSetsRecOn y H) := by
  rw [ofSetsRecOn, cast_eq_iff_heq, moveRecOn_eq]
  congr
  any_goals simp
  all_goals
    refine Function.hfunext rfl fun x _ h ↦ ?_
    cases h
    refine Function.hfunext ?_ fun _ _ _ ↦ ?_
    · simp
    · rw [ofSetsRecOn, cast_heq_iff_heq, heq_cast_iff_heq]

/-! ### Basic games -/

/-- The game `0 = {∅ | ∅}ᴳ`. -/
instance : Zero IGame := ⟨{∅ | ∅}ᴳ⟩

theorem zero_def : 0 = {∅ | ∅}ᴳ := rfl

@[simp] theorem leftMoves_zero : leftMoves 0 = ∅ := leftMoves_ofSets ..
@[simp] theorem rightMoves_zero : rightMoves 0 = ∅ := rightMoves_ofSets ..

instance : Inhabited IGame := ⟨0⟩

/-- The game `1 = {{0} | ∅}ᴳ`. -/
instance : One IGame := ⟨{{0} | ∅}ᴳ⟩

@[simp] theorem leftMoves_one : leftMoves 1 = {0} := leftMoves_ofSets ..
@[simp] theorem rightMoves_one : rightMoves 1 = ∅ := rightMoves_ofSets ..

/-! ### Order relations -/

/-- The less or equal relation on games.

If `0 ≤ x`, then Left can win `x` as the second player. `x ≤ y` means that `0 ≤ y - x`.
See `PGame.le_iff_sub_nonneg`. -/
instance : LE IGame where
  le := Sym2.GameAdd.fix isOption_wf fun x y le ↦
    (∀ z (h : z ∈ x.leftMoves),  ¬le y z (Sym2.GameAdd.snd_fst (IsOption.of_mem_leftMoves h))) ∧
    (∀ z (h : z ∈ y.rightMoves), ¬le z x (Sym2.GameAdd.fst_snd (IsOption.of_mem_rightMoves h)))

-- TODO: can a macro expert verify this makes sense?
/-- The less or fuzzy relation on pre-games. `x ⧏ y` is notation for `¬ y ≤ x`.

If `0 ⧏ x`, then Left can win `x` as the first player. `x ⧏ y` means that `0 ⧏ y - x`.
See `PGame.lf_iff_sub_zero_lf`. -/
macro_rules | `($x ⧏ $y) => `(¬$y ≤ $x)

/-- Definition of `x ≤ y` on pre-games, in terms of `⧏`. -/
theorem le_iff_forall_lf {x y : IGame} :
    x ≤ y ↔ (∀ z ∈ x.leftMoves, z ⧏ y) ∧ (∀ z ∈ y.rightMoves, x ⧏ z) :=
  propext_iff.1 <| Sym2.GameAdd.fix_eq ..

/-- Definition of `x ⧏ y` on pre-games, in terms of `≤`. -/
theorem lf_iff_exists_le {x y : IGame} :
    x ⧏ y ↔ (∃ z ∈ y.leftMoves, x ≤ z) ∨ (∃ z ∈ x.rightMoves, z ≤ y) := by
  simpa [not_and_or, -not_and] using le_iff_forall_lf.not

/-- The definition of `0 ≤ x` on pre-games, in terms of `0 ⧏`. -/
theorem zero_le {x : IGame} : 0 ≤ x ↔ ∀ y ∈ x.rightMoves, 0 ⧏ y := by
  rw [le_iff_forall_lf]; simp

/-- The definition of `x ≤ 0` on pre-games, in terms of `⧏ 0`. -/
theorem le_zero {x : IGame} : x ≤ 0 ↔ ∀ y ∈ x.leftMoves, y ⧏ 0 := by
  rw [le_iff_forall_lf]; simp

/-- The definition of `0 ⧏ x` on pre-games, in terms of `0 ≤`. -/
theorem zero_lf {x : IGame} : 0 ⧏ x ↔ ∃ y ∈ x.leftMoves, 0 ≤ y := by
  rw [lf_iff_exists_le]; simp

/-- The definition of `x ⧏ 0` on pre-games, in terms of `≤ 0`. -/
theorem lf_zero {x : IGame} : x ⧏ 0 ↔ ∃ y ∈ x.rightMoves, y ≤ 0 := by
  rw [lf_iff_exists_le]; simp

/-- The definition of `x ≤ y` on pre-games, in terms of `≤` two moves later.

Note that it's often more convenient to use `le_iff_forall_lf`, which only unfolds the definition by
one step. -/
theorem le_def {x y : IGame} : x ≤ y ↔
    (∀ a ∈ x.leftMoves,  (∃ b ∈ y.leftMoves, a ≤ b) ∨ (∃ b ∈ a.rightMoves, b ≤ y)) ∧
    (∀ a ∈ y.rightMoves, (∃ b ∈ a.leftMoves, x ≤ b) ∨ (∃ b ∈ x.rightMoves, b ≤ a)) := by
  rw [le_iff_forall_lf]
  congr! 2 <;> rw [lf_iff_exists_le]

/-- The definition of `x ⧏ y` on pre-games, in terms of `⧏` two moves later.

Note that it's often more convenient to use `lf_iff_exists_le`, which only unfolds the definition by
one step. -/
theorem lf_def {x y : IGame} : x ⧏ y ↔
    (∃ a ∈ y.leftMoves,  (∀ b ∈ x.leftMoves, b ⧏ a) ∧ (∀ b ∈ a.rightMoves, x ⧏ b)) ∨
    (∃ a ∈ x.rightMoves, (∀ b ∈ a.leftMoves, b ⧏ y) ∧ (∀ b ∈ y.rightMoves, a ⧏ b)) := by
  rw [lf_iff_exists_le]
  congr! <;> rw [le_iff_forall_lf]

-- TODO: preorder instance

-- We use `equiv` in theorem names for convenience.
@[inherit_doc AntisymmRel] infix:50 " ≈ " => AntisymmRel (· ≤ ·)

theorem equiv_of_exists {x y : IGame}
    (hl₁ : ∀ a ∈ x.leftMoves,  ∃ b ∈ y.leftMoves,  a ≈ b)
    (hr₁ : ∀ a ∈ x.rightMoves, ∃ b ∈ y.rightMoves, a ≈ b)
    (hl₂ : ∀ b ∈ y.leftMoves,  ∃ a ∈ x.leftMoves,  a ≈ b)
    (hr₂ : ∀ b ∈ y.rightMoves, ∃ a ∈ x.rightMoves, a ≈ b) : x ≈ y := by
  constructor <;> refine le_def.2 ⟨?_, ?_⟩ <;> intro i hi
  · obtain ⟨j, hj, hj'⟩ := hl₁ i hi
    exact Or.inl ⟨j, hj, hj'.le⟩
  · obtain ⟨j, hj, hj'⟩ := hr₂ i hi
    exact Or.inr ⟨j, hj, hj'.le⟩
  · obtain ⟨j, hj, hj'⟩ := hl₂ i hi
    exact Or.inl ⟨j, hj, hj'.ge⟩
  · obtain ⟨j, hj, hj'⟩ := hr₁ i hi
    exact Or.inr ⟨j, hj, hj'.ge⟩

-- TODO: define the comparability relation `CompRel r a b = r a b ∨ r b a`, port it to Mathlib,
-- use it to define notation `x ‖ y = ¬ CompRel (· ≤ ·) x y`.

/-! ### Negation -/

/-- The negative of a game `-{s | t}ᴳ = {-t | -s}ᴳ`. -/
instance : Neg IGame where
  neg x := ofSetsRecOn x fun s t _ _ IHl IHr ↦
    {range fun x : t ↦ IHr _ x.2 | range fun x : s ↦ IHl _ x.2}ᴳ

instance {α : Type*} [InvolutiveNeg α] (s : Set α) [Small.{u} s] : Small.{u} (-s :) := by
  rw [← Set.image_neg_eq_neg]
  infer_instance

-- We can't write this using `-s` and `-t` since we don't know these sets are small yet!
private theorem neg_ofSets' (s t : Set _) [Small s] [Small t] :
    -{s | t}ᴳ = {Neg.neg '' t | Neg.neg '' s}ᴳ := by
  simp_rw [image_eq_range]
  exact ofSetsRecOn_ofSets ..

instance : InvolutiveNeg IGame where
  neg_neg x := by
    refine ofSetsRecOn x ?_
    aesop (add simp [neg_ofSets'])

@[simp]
theorem neg_ofSets (s t : Set _) [Small s] [Small t] : -{s | t}ᴳ = {-t | -s}ᴳ := by
  simp_rw [neg_ofSets', Set.image_neg_eq_neg]

instance : NegZeroClass IGame where
  neg_zero := by simp [zero_def]

theorem neg_eq (x : IGame) : -x = {-x.rightMoves | -x.leftMoves}ᴳ := by
  rw [← neg_ofSets, ofSets_leftMoves_rightMoves]

@[simp]
theorem leftMoves_neg (x : IGame) : (-x).leftMoves = -x.rightMoves := by
  refine ofSetsRecOn x ?_
  simp

@[simp]
theorem rightMoves_neg (x : IGame) : (-x).rightMoves = -x.leftMoves := by
  refine ofSetsRecOn x ?_
  simp

theorem isOption_neg {x y : IGame} : IsOption x (-y) ↔ IsOption (-x) y := by
  simp [IsOption, union_comm]

@[simp]
theorem isOption_neg_neg {x y : IGame} : IsOption (-x) (-y) ↔ IsOption x y := by
  rw [isOption_neg, neg_neg]

@[simp]
theorem neg_le_iff {x y : IGame} : -x ≤ -y ↔ y ≤ x := by
  -- TODO: may have to add an `elab_as_elim` attr. in Mathlib
  refine Sym2.GameAdd.induction (C := fun x y ↦ -x ≤ -y ↔ y ≤ x) isOption_wf (fun x y IH ↦ ?_) x y
  dsimp at *
  rw [le_iff_forall_lf, le_iff_forall_lf, and_comm, ← (Equiv.neg IGame).forall_congr_right]
  nth_rewrite 2 [← (Equiv.neg IGame).forall_congr_right]
  simp only [rightMoves_neg, Equiv.neg_apply, mem_neg, neg_neg, leftMoves_neg]
  congr! 3 with z hz z hz
  · rw [IH _ _ (Sym2.GameAdd.fst_snd (.of_mem_leftMoves hz))]
  · rw [IH _ _ (Sym2.GameAdd.snd_fst (.of_mem_rightMoves hz))]

end IGame
end
