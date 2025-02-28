/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.PGame
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Logic.Hydra
import Mathlib.Logic.Small.Set

universe u

-- This is a false positive due to the provisional duplicated IGame/IGame file path.
set_option linter.dupNamespace false
-- All computation should be done through `IGame.Short`.
noncomputable section

open PGame Set Pointwise

/-- Games up to identity.

`IGame` uses the set-theoretic notion of equality on games, compared to `PGame`'s 'type-theoretic'
notion of equality.

This is not the same equivalence as used broadly in combinatorial game theory literature, as a game
like {0, 1 | 0} is not *identical* to {1 | 0}, despite being equivalent. However, many theorems can
be proven over the 'identical' equivalence relation, and the literature may occasionally
specifically use the 'identical' equivalence relation for this reason.

For the more common game equivalence from literature, see `Game.Basic`. -/
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
def out (x : IGame) : PGame := Quotient.out x
@[simp] theorem out_eq (x : IGame) : mk x.out = x := Quotient.out_eq x

/-- The set of left moves of the game. -/
def leftMoves : IGame → Set IGame := by
  refine Quotient.lift (fun x ↦ mk '' range x.moveLeft) fun x y h ↦ ?_
  ext z
  simp_rw [mem_image, mem_range, exists_exists_eq_and]
  constructor <;> rintro ⟨i, rfl⟩
  · obtain ⟨j, hj⟩ := h.moveLeft i
    exact ⟨j, hj.mk_eq.symm⟩
  · obtain ⟨j, hj⟩ := h.moveLeft_symm i
    exact ⟨j, hj.mk_eq⟩

/-- The set of right moves of the game. -/
def rightMoves : IGame → Set IGame := by
  refine Quotient.lift (fun x ↦ mk '' range x.moveRight) fun x y h ↦ ?_
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

/-- A (proper) subposition is any game in the transitive closure of `IsOption`. -/
def Subposition : IGame → IGame → Prop :=
  Relation.TransGen IsOption

theorem Subposition.of_mem_leftMoves {x y : IGame} (h : x ∈ y.leftMoves) : Subposition x y :=
  Relation.TransGen.single (.of_mem_leftMoves h)

theorem Subposition.of_mem_rightMoves {x y : IGame} (h : x ∈ y.rightMoves) : Subposition x y :=
  Relation.TransGen.single (.of_mem_rightMoves h)

theorem Subposition.trans {x y z : IGame} (h₁ : Subposition x y) (h₂ : Subposition y z) :
    Subposition x z :=
  Relation.TransGen.trans h₁ h₂

instance : IsTrans _ Subposition := inferInstanceAs (IsTrans _ (Relation.TransGen _))
instance : IsWellFounded _ Subposition := inferInstanceAs (IsWellFounded _ (Relation.TransGen _))
instance : WellFoundedRelation IGame := ⟨Subposition, instIsWellFoundedSubposition.wf⟩

/-- Discharges proof obligations of the form `⊢ Subposition ..` arising in termination proofs
of definitions using well-founded recursion on `IGame`. -/
macro "igame_wf" : tactic =>
  `(tactic| all_goals solve_by_elim
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    Subposition.of_mem_leftMoves, Subposition.of_mem_rightMoves, Subposition.trans, Subtype.prop] )

/-- Construct an `IGame` from its left and right sets.

This is given notation `{s | t}ᴵ`, where the superscript `I` is to disambiguate
from set builder notation, and from the analogous constructor on `Game`. -/
def ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] : IGame.{u} :=
  mk <| .mk (Shrink s) (Shrink t)
    (out ∘ Subtype.val ∘ (equivShrink s).symm) (out ∘ Subtype.val ∘ (equivShrink t).symm)

-- TODO: can a macro expert verify this makes sense?
@[inherit_doc ofSets] macro "{" s:term " | " t:term "}ᴵ" : term => `(ofSets $s $t)

@[simp]
theorem leftMoves_ofSets (s t : Set _) [Small.{u} s] [Small.{u} t] : {s | t}ᴵ.leftMoves = s := by
  ext; simp [ofSets, range_comp, Equiv.range_eq_univ]

@[simp]
theorem rightMoves_ofSets (s t : Set _) [Small.{u} s] [Small.{u} t] : {s | t}ᴵ.rightMoves = t := by
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
    (H : Π (s t : Set _) [Small s] [Small t], (Π x ∈ s, P x) → (Π x ∈ t, P x) → P {s | t}ᴵ) : P x :=
  cast (by simp) <| moveRecOn (P := fun x ↦ P {x.leftMoves | x.rightMoves}ᴵ) x fun x IHl IHr ↦
    H _ _ (fun y hy ↦ cast (by simp) (IHl y hy)) (fun y hy ↦ cast (by simp) (IHr y hy))

@[simp]
theorem ofSetsRecOn_ofSets {P : IGame.{u} → Sort*} (s t : Set IGame) [Small.{u} s] [Small.{u} t]
    (H : Π (s t : Set _) [Small s] [Small t], (Π x ∈ s, P x) → (Π x ∈ t, P x) → P {s | t}ᴵ) :
    ofSetsRecOn {s | t}ᴵ H = H _ _ (fun y _ ↦ ofSetsRecOn y H) (fun y _ ↦ ofSetsRecOn y H) := by
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

/-- The game `0 = {∅ | ∅}ᴵ`. -/
instance : Zero IGame := ⟨{∅ | ∅}ᴵ⟩

theorem zero_def : 0 = {∅ | ∅}ᴵ := rfl

@[simp] theorem leftMoves_zero : leftMoves 0 = ∅ := leftMoves_ofSets ..
@[simp] theorem rightMoves_zero : rightMoves 0 = ∅ := rightMoves_ofSets ..

instance : Inhabited IGame := ⟨0⟩

/-- The game `1 = {{0} | ∅}ᴵ`. -/
instance : One IGame := ⟨{{0} | ∅}ᴵ⟩

theorem one_def : 1 = {{0} | ∅}ᴵ := rfl

@[simp] theorem leftMoves_one : leftMoves 1 = {0} := leftMoves_ofSets ..
@[simp] theorem rightMoves_one : rightMoves 1 = ∅ := rightMoves_ofSets ..

/-! ### Order relations -/

/-- The less or equal relation on games.

If `0 ≤ x`, then Left can win `x` as the second player. `x ≤ y` means that `0 ≤ y - x`. -/
instance : LE IGame where
  le := Sym2.GameAdd.fix isOption_wf fun x y le ↦
    (∀ z (h : z ∈ x.leftMoves),  ¬le y z (Sym2.GameAdd.snd_fst (IsOption.of_mem_leftMoves h))) ∧
    (∀ z (h : z ∈ y.rightMoves), ¬le z x (Sym2.GameAdd.fst_snd (IsOption.of_mem_rightMoves h)))

-- TODO: can a macro expert verify this makes sense?
/-- The less or fuzzy relation on pre-games. `x ⧏ y` is notation for `¬ y ≤ x`.

If `0 ⧏ x`, then Left can win `x` as the first player. `x ⧏ y` means that `0 ⧏ y - x`. -/
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

theorem lf_of_le_of_mem_leftMoves {x y z : IGame} (h : x ≤ y) (h' : z ∈ x.leftMoves) : z ⧏ y :=
  (le_iff_forall_lf.1 h).1 z h'

theorem lf_of_le_of_mem_rightMoves {x y z : IGame} (h : x ≤ y) (h' : z ∈ y.rightMoves) : x ⧏ z :=
  (le_iff_forall_lf.1 h).2 z h'

alias _root_.LE.le.lf_of_mem_leftMoves := lf_of_le_of_mem_leftMoves
alias _root_.LE.le.lf_of_mem_rightMoves := lf_of_le_of_mem_rightMoves

theorem lf_of_mem_leftMoves_of_lf {x y z : IGame} (h : z ∈ y.leftMoves) (h' : x ≤ z) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inl ⟨z, h, h'⟩

theorem lf_of_mem_rightMoves_of_lf {x y z : IGame} (h : z ∈ x.rightMoves) (h' : z ≤ y) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inr ⟨z, h, h'⟩

private theorem le_rfl' {x : IGame} : x ≤ x := by
  rw [le_iff_forall_lf]
  constructor <;> intro y hy
  exacts [lf_of_mem_leftMoves_of_lf hy le_rfl', lf_of_mem_rightMoves_of_lf hy le_rfl']
termination_by x
decreasing_by igame_wf

-- TODO: add these convenience theorems to Mathlib
theorem _root_.Relation.cutExpand_add_single {α : Type*} {r : α → α → Prop} {a' a : α}
    (s : Multiset α) (h : r a' a) : Relation.CutExpand r (s + {a'}) (s + {a}) :=
  (Relation.cutExpand_add_left s).2 <| Relation.cutExpand_singleton_singleton h

theorem _root_.Relation.cutExpand_single_add {α : Type*} {r : α → α → Prop} {a' a : α}
    (h : r a' a) (s : Multiset α) : Relation.CutExpand r ({a'} +  s) ({a} + s) :=
  (Relation.cutExpand_add_right s).2 <| Relation.cutExpand_singleton_singleton h

private theorem le_trans' {x y z : IGame} (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := by
  rw [le_iff_forall_lf]
  constructor <;> intro a ha h₃
  exacts [h₁.lf_of_mem_leftMoves ha (le_trans' h₂ h₃), h₂.lf_of_mem_rightMoves ha (le_trans' h₃ h₁)]
termination_by isOption_wf.cutExpand.wrap {x, y, z}
decreasing_by
  on_goal 1 => convert (Relation.cutExpand_add_single {y, z} (IsOption.of_mem_leftMoves ha))
  on_goal 2 => convert (Relation.cutExpand_single_add (IsOption.of_mem_rightMoves ha) {x, y})
  all_goals simp [← Multiset.singleton_add, add_comm, add_assoc, WellFounded.wrap]

instance : Preorder IGame where
  le_refl _ := le_rfl'
  le_trans x y z := le_trans'

-- We use `equiv` in theorem names for convenience.
@[inherit_doc AntisymmRel] infix:50 " ≈ " => AntisymmRel (· ≤ ·)

-- TODO: this seems like the kind of goal that could be simplified through `aesop`.
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

instance : ZeroLEOneClass IGame where
  zero_le_one := by rw [zero_le]; simp

theorem zero_lt_one : (0 : IGame) < 1 :=
  lt_of_le_not_le zero_le_one (by rw [le_zero]; simp)

/-! ### Negation -/

instance {α : Type*} [InvolutiveNeg α] (s : Set α) [Small.{u} s] : Small.{u} (-s :) := by
  rw [← Set.image_neg_eq_neg]
  infer_instance

private def neg' (x : IGame) : IGame :=
  {range fun y : x.rightMoves ↦ neg' y.1 | range fun y : x.leftMoves ↦ neg' y.1}ᴵ
termination_by x
decreasing_by igame_wf

/-- The negative of a game is defined by `-{s | t}ᴵ = {-t | -s}ᴵ`. -/
instance : Neg IGame where
  neg := neg'

private theorem neg_ofSets' (s t : Set _) [Small s] [Small t] :
    -{s | t}ᴵ = {Neg.neg '' t | Neg.neg '' s}ᴵ := by
  change neg' _ = _
  rw [neg']
  simp [Neg.neg, Set.ext_iff]

instance : InvolutiveNeg IGame where
  neg_neg x := by
    refine ofSetsRecOn x ?_
    aesop (add simp [neg_ofSets'])

@[simp]
theorem neg_ofSets (s t : Set _) [Small s] [Small t] : -{s | t}ᴵ = {-t | -s}ᴵ := by
  simp_rw [neg_ofSets', Set.image_neg_eq_neg]

instance : NegZeroClass IGame where
  neg_zero := by simp [zero_def]

theorem neg_eq (x : IGame) : -x = {-x.rightMoves | -x.leftMoves}ᴵ := by
  rw [← neg_ofSets, ofSets_leftMoves_rightMoves]

@[simp]
theorem leftMoves_neg (x : IGame) : (-x).leftMoves = -x.rightMoves := by
  refine ofSetsRecOn x ?_; simp

@[simp]
theorem rightMoves_neg (x : IGame) : (-x).rightMoves = -x.leftMoves := by
  refine ofSetsRecOn x ?_; simp

theorem isOption_neg {x y : IGame} : IsOption x (-y) ↔ IsOption (-x) y := by
  simp [IsOption, union_comm]

@[simp]
theorem isOption_neg_neg {x y : IGame} : IsOption (-x) (-y) ↔ IsOption x y := by
  rw [isOption_neg, neg_neg]

@[simp]
protected theorem neg_le_neg_iff {x y : IGame} : -x ≤ -y ↔ y ≤ x := by
  -- TODO: may have to add an `elab_as_elim` attr. in Mathlib
  refine Sym2.GameAdd.induction (C := fun x y ↦ -x ≤ -y ↔ y ≤ x) isOption_wf (fun x y IH ↦ ?_) x y
  dsimp at *
  rw [le_iff_forall_lf, le_iff_forall_lf, and_comm, ← (Equiv.neg IGame).forall_congr_right]
  nth_rewrite 2 [← (Equiv.neg IGame).forall_congr_right]
  simp only [rightMoves_neg, Equiv.neg_apply, mem_neg, neg_neg, leftMoves_neg]
  congr! 3 with z hz z hz
  · rw [IH _ _ (Sym2.GameAdd.fst_snd (.of_mem_leftMoves hz))]
  · rw [IH _ _ (Sym2.GameAdd.snd_fst (.of_mem_rightMoves hz))]

protected theorem neg_le {x y : IGame} : -x ≤ y ↔ -y ≤ x := by
  simpa using @IGame.neg_le_neg_iff x (-y)
protected theorem le_neg {x y : IGame} : x ≤ -y ↔ y ≤ -x := by
  simpa using @IGame.neg_le_neg_iff (-x) y

@[simp]
protected theorem neg_lt_neg_iff {x y : IGame} : -x < -y ↔ y < x := by
  rw [lt_iff_le_not_le, IGame.neg_le_neg_iff, IGame.neg_le_neg_iff, lt_iff_le_not_le]

protected theorem neg_lt {x y : IGame} : -x < y ↔ -y < x := by
  simpa using @IGame.neg_lt_neg_iff x (-y)
protected theorem lt_neg {x y : IGame} : x < -y ↔ y < -x := by
  simpa using @IGame.neg_lt_neg_iff (-x) y

@[simp]
protected theorem neg_equiv_neg_iff {x y : IGame} : -x ≈ -y ↔ x ≈ y := by
  simp [AntisymmRel, and_comm]

@[simp] theorem neg_le_zero {x : IGame} : -x ≤ 0 ↔ 0 ≤ x := by simpa using @IGame.neg_le x 0
@[simp] theorem zero_le_neg {x : IGame} : 0 ≤ -x ↔ x ≤ 0 := by simpa using @IGame.le_neg 0 x
@[simp] theorem neg_lt_zero {x : IGame} : -x < 0 ↔ 0 < x := by simpa using @IGame.neg_lt x 0
@[simp] theorem zero_lt_neg {x : IGame} : 0 < -x ↔ x < 0 := by simpa using @IGame.lt_neg 0 x

@[simp] theorem neg_equiv_zero {x : IGame} : -x ≈ 0 ↔ x ≈ 0 := by
  simpa using @IGame.neg_equiv_neg_iff x 0
@[simp] theorem zero_equiv_neg {x : IGame} : 0 ≈ -x ↔ 0 ≈ x := by
  simpa using @IGame.neg_equiv_neg_iff 0 x

/-! ### Addition and subtraction -/

private def add' (x y : IGame) : IGame :=
  {(range fun z : x.leftMoves ↦ add' z y) ∪ (range fun z : y.leftMoves ↦ add' x z) |
    (range fun z : x.rightMoves ↦ add' z y) ∪ (range fun z : y.rightMoves ↦ add' x z)}ᴵ
termination_by (x, y)
decreasing_by igame_wf

/-- The sum of `x = {s₁ | t₁}ᴵ` and `y = {s₂ | t₂}ᴵ` is `{s₁ + y, x + s₂ | t₁ + y, x + t₂}ᴵ`. -/
instance : Add IGame where
  add := add'

theorem add_eq (x y : IGame) : x + y =
    {(· + y) '' x.leftMoves ∪ (x + ·) '' y.leftMoves |
      (· + y) '' x.rightMoves ∪ (x + ·) '' y.rightMoves}ᴵ := by
  change add' _ _ = _
  rw [add']
  simp [HAdd.hAdd, Add.add, Set.ext_iff]

theorem ofSets_add_ofSets (s₁ t₁ s₂ t₂ : Set IGame) [Small s₁] [Small t₁] [Small s₂] [Small t₂] :
    {s₁ | t₁}ᴵ + {s₂ | t₂}ᴵ =
      {(· + {s₂ | t₂}ᴵ) '' s₁ ∪ ({s₁ | t₁}ᴵ + ·) '' s₂ |
        (· + {s₂ | t₂}ᴵ) '' t₁ ∪ ({s₁ | t₁}ᴵ + ·) '' t₂}ᴵ := by
  rw [add_eq]
  simp

@[simp]
theorem leftMoves_add (x y : IGame) :
    (x + y).leftMoves = (· + y) '' x.leftMoves ∪ (x + ·) '' y.leftMoves := by
  rw [add_eq]; simp

@[simp]
theorem rightMoves_add (x y : IGame) :
    (x + y).rightMoves = (· + y) '' x.rightMoves ∪ (x + ·) '' y.rightMoves := by
  rw [add_eq]; simp

instance : AddZeroClass IGame := by
  constructor <;>
  · intro x
    induction x using ofSetsRecOn with | H s t IHl IHr =>
    rw [add_eq]
    aesop

private theorem add_comm' (x y : IGame) : x + y = y + x := by
  ext <;>
  · simp only [leftMoves_add, rightMoves_add, mem_union, mem_image, or_comm]
    congr! 3 <;>
    · refine and_congr_right_iff.2 fun h ↦ ?_
      rw [add_comm']
termination_by (x, y)
decreasing_by igame_wf

private theorem add_assoc' (x y z : IGame) : x + y + z = x + (y + z) := by
  apply ext <;>
  · simp only [leftMoves_add, rightMoves_add, image_union, image_image, union_assoc]
    refine congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_) <;>
    · ext
      congr! 2
      rw [add_assoc']
termination_by (x, y, z)
decreasing_by igame_wf

instance : AddCommMonoid IGame where
  add_comm := add_comm'
  add_assoc := add_assoc'
  nsmul := nsmulRec
  __ : AddZeroClass IGame := inferInstance

end IGame
end
