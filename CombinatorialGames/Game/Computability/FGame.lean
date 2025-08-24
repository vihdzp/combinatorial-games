/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Kim Morrison, Tristan Figueroa-Reid
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

import CombinatorialGames.Game.Short
import CombinatorialGames.Mathlib.Finlift
import CombinatorialGames.Tactic.GameCmp

/-!
# Computably short games

We already have a definition of short games at `IGame.Short`, but it is, regrettably, noncomputable.
Here, we provide a computable definition of short games from the ground up, following a similar
construction method presented in `IGame.lean`.

We define `FGame` and its auxiliary backing type `SGame` as data, providing data for the left and
right moves of a game in the form of an auxiliary `SGame` type. This makes us capable of performing
some basic computations on `IGame`. Since we would like to use the same standard interface for
theorem proving in combinatorial games, we restrict this file only for computability usage and
FGame generation. Since some of `IGame`'s basic definitions are computable, these theorems
suffice for most of the computability we need.

In general, **You should not build any substantial theory based off of this file.** The theorems
here are intended to check for definitional correctness over theory building.
-/

/-! ### For Mathlib -/

instance {α β : Type*} (r : α → β → Prop) [H : Decidable (∀ a, ∃ b, r a b)] :
    Decidable (Relator.LeftTotal r) := H
instance {α β : Type*} (r : α → β → Prop) [H : Decidable (∀ b, ∃ a, r a b)] :
    Decidable (Relator.RightTotal r) := H

instance {α β : Type*} (r : α → β → Prop)
    [H₁ : Decidable (∀ a, ∃ b, r a b)] [H : Decidable (∀ b, ∃ a, r a b)] :
    Decidable (Relator.BiTotal r) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp]
theorem Finset.image_attach_comp {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) :
    s.attach.image (f ∘ Subtype.val) = s.image f := by
  classical
  rw [← Finset.image_image, Finset.attach_image_val]

@[simp]
theorem Finset.image_attach {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) :
    s.attach.image (fun x ↦ f x.1) = s.image f :=
  s.image_attach_comp f

universe u

/-- The type of "short pre-games", before we have quotiented by equivalence (`identicalSetoid`).

This serves the exact purpose that `PGame` does for `IGame`. However, unlike `PGame`'s relatively
short construction, we must prove some extra definitions for computing on top of `SGame`.

This could perfectly well have been in `Type 0`, but we make it universe polymorphic for
convenience when building quotient types. However, conversions from computable games to their
noncomputable counterparts are squeezed to `Type 0`. -/
inductive SGame : Type u
  | mk (m n : ℕ) (f : Fin m → SGame) (g : Fin n → SGame) : SGame
compile_inductive% SGame

namespace SGame

/-- The number of left moves on a `SGame`. -/
def LeftMoves : SGame → ℕ
  | mk m _ _ _ => m

/-- The number of right moves on a `SGame`. -/
def RightMoves : SGame → ℕ
  | mk _ n _ _ => n

/-- Perform a left move. -/
def moveLeft : ∀ g : SGame, Fin g.LeftMoves → SGame
  | mk _ _ f _ => f

/-- Perform a right move. -/
def moveRight : ∀ g : SGame, Fin g.RightMoves → SGame
  | mk _ _ _ g => g

@[simp] theorem leftMoves_mk (m n f g) : (mk m n f g).LeftMoves = m := rfl
@[simp] theorem rightMoves_mk (m n f g) : (mk m n f g).RightMoves = n := rfl
@[simp] theorem moveLeft_mk (m n f g) : (mk m n f g).moveLeft = f := rfl
@[simp] theorem moveRight_mk (m n f g) : (mk m n f g).moveRight = g := rfl

/-- A well-founded relation on `SGame`. While this goes against minimizing
`SGame` code, this enables well-defined recursion in `SGame`. -/
inductive IsOption : SGame → SGame → Prop
  | moveLeft {x : SGame} (n : Fin x.LeftMoves) : IsOption (x.moveLeft n) x
  | moveRight {x : SGame} (n : Fin x.RightMoves) : IsOption (x.moveRight n) x

theorem isOption_wf : WellFounded IsOption := by
  refine ⟨rec fun s t f g IHl IHr ↦ .intro _ ?_⟩
  rintro y (h | h)
  · exact IHl _
  · exact IHr _

instance : WellFoundedRelation SGame := ⟨_, isOption_wf⟩

macro "sgame_wf" : tactic =>
  `(tactic| all_goals solve_by_elim
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    IsOption.moveLeft, IsOption.moveRight] )

instance : DecidableEq SGame
  | mk m n f g, mk m' n' f' g' => if h : m = m' ∧ n = n' then
    let : ∀ a b, Decidable (f a = f' b) := fun a b ↦ instDecidableEq ..
    let : ∀ a b, Decidable (g a = g' b) := fun a b ↦ instDecidableEq ..
    decidable_of_iff ((m = m' ∧ n = n' ∧ (∀ i, f i = f' ⟨i, _⟩) ∧ ∀ i, g i = g' ⟨i, _⟩)) <| by
      rw [mk.injEq, Fin.heq_fun_iff h.1, Fin.heq_fun_iff h.2]
  else .isFalse (by simp_all)

/-- The identical relation on short games. See `PGame.Identical`. -/
def Identical : SGame.{u} → SGame.{u} → Prop
  | mk _ _ xL xR, mk _ _ yL yR =>
      Relator.BiTotal (fun i j ↦ Identical (xL i) (yL j)) ∧
      Relator.BiTotal (fun i j ↦ Identical (xR i) (yR j))

@[inherit_doc] scoped infix:50 " ≡ " => SGame.Identical

theorem identical_iff : ∀ {x y : SGame}, x ≡ y ↔
    Relator.BiTotal (x.moveLeft · ≡ y.moveLeft ·) ∧ Relator.BiTotal (x.moveRight · ≡ y.moveRight ·)
  | mk .., mk .. => .rfl

@[refl]
protected theorem Identical.refl (x) : x ≡ x :=
  x.recOn fun _ _ _ _ IHL IHR ↦ ⟨Relator.BiTotal.refl IHL, Relator.BiTotal.refl IHR⟩

@[symm]
protected theorem Identical.symm : ∀ {x y}, x ≡ y → y ≡ x
  | mk .., mk .., ⟨hL, hR⟩ => ⟨hL.symm fun _ _ h ↦ h.symm, hR.symm fun _ _ h ↦ h.symm⟩

@[trans]
protected theorem Identical.trans : ∀ {x y z}, x ≡ y → y ≡ z → x ≡ z
  | mk .., mk .., mk .., ⟨hL₁, hR₁⟩, ⟨hL₂, hR₂⟩ =>
    ⟨hL₁.trans (fun _ _ _ h₁ ↦ h₁.trans) hL₂, hR₁.trans (fun _ _ _ h₁ ↦ h₁.trans) hR₂⟩

/-- `Identical` as a `Setoid`. -/
def identicalSetoid : Setoid SGame :=
  ⟨Identical, .refl, .symm, .trans⟩

/-- If `x ≡ y`, then a left move of `x` is identical to some left move of `y`. -/
theorem Identical.moveLeft : ∀ {x y}, x ≡ y → ∀ i, ∃ j, x.moveLeft i ≡ y.moveLeft j
  | mk .., mk .., ⟨hl, _⟩ => hl.1

/-- If `x ≡ y`, then a left move of `y` is identical to some left move of `x`. -/
theorem Identical.moveLeft_symm : ∀ {x y}, x ≡ y → ∀ i, ∃ j, x.moveLeft j ≡ y.moveLeft i
  | mk .., mk .., ⟨hl, _⟩ => hl.2

/-- If `x ≡ y`, then a right move of `x` is identical to some right move of `y`. -/
theorem Identical.moveRight : ∀ {x y}, x ≡ y → ∀ i, ∃ j, x.moveRight i ≡ y.moveRight j
  | mk .., mk .., ⟨_, hr⟩ => hr.1

/-- If `x ≡ y`, then a right move of `y` is identical to some right move of `x`. -/
theorem Identical.moveRight_symm : ∀ {x y}, x ≡ y → ∀ i, ∃ j, x.moveRight j ≡ y.moveRight i
  | mk .., mk .., ⟨_, hr⟩ => hr.2

@[semireducible]
instance Identical.instDecidable (a b) : Decidable (a ≡ b) :=
  let : DecidableRel (a.moveLeft · ≡ b.moveLeft ·) := fun c d ↦ Identical.instDecidable ..
  let : DecidableRel (a.moveLeft · ≡ b.moveRight ·) := fun c d ↦ Identical.instDecidable ..
  let : DecidableRel (a.moveRight · ≡ b.moveLeft ·) := fun c d ↦ Identical.instDecidable ..
  let : DecidableRel (a.moveRight · ≡ b.moveRight ·) := fun c d ↦ Identical.instDecidable ..
  decidable_of_iff' _ identical_iff
termination_by (a, b)
decreasing_by sgame_wf

end SGame

/-! ### Game moves -/

/-- Short games up to identity.

`FGame` uses the set-theoretic notion of equality on short games,
similarly to how `IGame` is defined on top of `PGame`.

Here, we have the distinct advantage of being able to use finsets as our
backing left and right sets over `IGame`'s small sets.
-/
def FGame : Type u :=
  Quotient SGame.identicalSetoid

namespace FGame
open scoped SGame

/-- The quotient map from `SGame` into `FGame`. -/
def mk (x : SGame) : FGame := Quotient.mk _ x
theorem mk_eq_mk {x y : SGame} : mk x = mk y ↔ x ≡ y := Quotient.eq

alias ⟨_, mk_eq⟩ := mk_eq_mk
alias _root_.SGame.Identical.mk_eq := mk_eq

@[cases_eliminator]
theorem ind {motive : FGame → Prop} (H : ∀ y, motive (mk y)) (x : FGame) : motive x :=
  Quotient.ind H x

instance : DecidableEq FGame := Quotient.decidableEq (d := SGame.Identical.instDecidable)

/-- Choose an element of the equivalence class using the axiom of choice. -/
noncomputable def out (x : FGame) : SGame := Quotient.out x
@[simp] theorem out_eq (x : FGame) : mk x.out = x := Quotient.out_eq x

/-- The finset of left moves of the game. -/
def leftMoves : FGame → Finset FGame :=
  Quotient.lift (fun x ↦ Finset.univ.image fun y ↦ mk (x.moveLeft y)) fun x y h ↦ by
    ext z
    simp_rw [Finset.mem_image, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨i, rfl⟩
    · obtain ⟨j, hj⟩ := h.moveLeft i
      exact ⟨j, hj.mk_eq.symm⟩
    · obtain ⟨j, hj⟩ := h.moveLeft_symm i
      exact ⟨j, hj.mk_eq⟩

/-- The finset of right moves of the game. -/
def rightMoves : FGame → Finset FGame :=
  Quotient.lift (fun x ↦ Finset.univ.image fun y ↦ mk (x.moveRight y)) fun x y h ↦ by
    ext z
    simp_rw [Finset.mem_image, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨i, rfl⟩
    · obtain ⟨j, hj⟩ := h.moveRight i
      exact ⟨j, hj.mk_eq.symm⟩
    · obtain ⟨j, hj⟩ := h.moveRight_symm i
      exact ⟨j, hj.mk_eq⟩

@[simp] theorem leftMoves_mk (x : SGame) :
    leftMoves (mk x) = Finset.univ.image (mk ∘ x.moveLeft) := rfl
@[simp] theorem rightMoves_mk (x : SGame) :
    rightMoves (mk x) = Finset.univ.image (mk ∘ x.moveRight) := rfl

@[ext]
theorem ext {x y : FGame} (hl : x.leftMoves = y.leftMoves) (hr : x.rightMoves = y.rightMoves) :
    x = y := by
  cases x with | H x =>
  cases y with | H y =>
  dsimp at hl hr
  refine (SGame.identical_iff.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩).mk_eq <;> intro i
  · have := Finset.mem_image_of_mem mk (show x.moveLeft i ∈ Finset.univ.image x.moveLeft by simp)
    rw [Finset.image_image, hl] at this
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp this
    exact ⟨b, mk_eq_mk.mp hb.symm⟩
  · have := Finset.mem_image_of_mem mk (show y.moveLeft i ∈ Finset.univ.image y.moveLeft by simp)
    rw [Finset.image_image, ← hl] at this
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp this
    exact ⟨b, mk_eq_mk.mp hb⟩
  · have := Finset.mem_image_of_mem mk (show x.moveRight i ∈ Finset.univ.image x.moveRight by simp)
    rw [Finset.image_image, hr] at this
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp this
    exact ⟨b, mk_eq_mk.mp hb.symm⟩
  · have := Finset.mem_image_of_mem mk (show y.moveRight i ∈ Finset.univ.image y.moveRight by simp)
    rw [Finset.image_image, ← hr] at this
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp this
    exact ⟨b, mk_eq_mk.mp hb⟩

/-- `IsOption x y` means that `x` is either a left or a right move for `y`. -/
@[aesop simp]
def IsOption (x y : FGame) : Prop :=
  x ∈ y.leftMoves ∨ x ∈ y.rightMoves

theorem IsOption.of_mem_leftMoves {x y : FGame} : x ∈ y.leftMoves → IsOption x y := .inl
theorem IsOption.of_mem_rightMoves {x y : FGame} : x ∈ y.rightMoves → IsOption x y := .inr

theorem isOption_wf : WellFounded IsOption := by
  refine ⟨ind fun x ↦ ?_⟩
  induction x with
  | mk x _ _ _ hl hr =>
    constructor
    rintro ⟨y⟩ (h | h)
    · rw [leftMoves_mk, Finset.mem_image] at h
      exact h.choose_spec.2 ▸ hl h.choose
    · rw [rightMoves_mk, Finset.mem_image] at h
      exact h.choose_spec.2 ▸ hr h.choose

instance : IsWellFounded _ IsOption := ⟨isOption_wf⟩

theorem IsOption.irrefl (x : FGame) : ¬ IsOption x x := _root_.irrefl x

theorem self_notMem_leftMoves (x : FGame) : x ∉ x.leftMoves :=
  fun hx ↦ IsOption.irrefl x (.of_mem_leftMoves hx)

theorem self_notMem_rightMoves (x : FGame) : x ∉ x.rightMoves :=
  fun hx ↦ IsOption.irrefl x (.of_mem_rightMoves hx)

/-- Construct a `FGame` from its left and right lists. This is an auxiliary definition
used to define the more general `FGame.ofFinsets`. -/
def ofLists (s t : List FGame.{u}) : FGame.{u} :=
  Quotient.finLiftOn₂ s.get t.get (fun i j ↦ .mk <| .mk _ _ i j) fun a₁ b₁ a₂ b₂ ha hb ↦ by
    have := fun i ↦ (ha i).symm
    have := fun i ↦ (hb i).symm
    ext x <;> aesop (add simp [mk_eq_mk])

private theorem ofLists_moves {s t : List FGame} :
    (ofLists s t).leftMoves = s.toFinset ∧ (ofLists s t).rightMoves = t.toFinset := by
  unfold ofLists leftMoves rightMoves FGame.mk
  generalize hs : s.get = sf
  generalize ht : t.get = tf
  induction sf using Quotient.induction_on_pi
  induction tf using Quotient.induction_on_pi
  rw [Quotient.finLiftOn₂_mk, Quotient.lift_mk]
  aesop (add simp [hs.symm, ht.symm])

@[simp]
theorem leftMoves_ofLists {s t : List FGame} : (ofLists s t).leftMoves = s.toFinset :=
  ofLists_moves.1

@[simp]
theorem rightMoves_ofLists {s t : List FGame} : (ofLists s t).rightMoves = t.toFinset :=
  ofLists_moves.2

/-- Construct a `FGame` from its left and right finsets.

This is given notation `{s | t}ꟳ`, where the superscript `F` is to disambiguate from set builder
notation, and from the analogous constructors on other game types. -/
def ofFinsets (s t : Finset FGame) : FGame :=
  Quotient.liftOn₂ s.1 t.1 ofLists fun a₁ b₁ a₂ b₂ ha hb ↦ by
    rw [← Quotient.eq_iff_equiv, Multiset.quot_mk_to_coe, Multiset.quot_mk_to_coe] at ha hb
    simp_rw [FGame.ext_iff, leftMoves_ofLists, rightMoves_ofLists, ← List.toFinset_coe]
    exact ⟨congrArg Multiset.toFinset ha, congrArg Multiset.toFinset hb⟩

@[inherit_doc] notation "{" s " | " t "}ꟳ" => ofFinsets s t
recommended_spelling "ofFinsets" for "{· | ·}ꟳ" in [«term{_|_}ꟳ»]

private def moves_ofFinsets {s t : Finset FGame} :
    {s | t}ꟳ.leftMoves = s ∧ {s | t}ꟳ.rightMoves = t := by
  unfold ofFinsets
  generalize hs : s.val = sf
  generalize ht : t.val = tf
  induction sf, tf using Quotient.inductionOn₂
  rw [Multiset.quot_mk_to_coe] at hs ht
  simp_rw [Multiset.quot_mk_to_coe, Multiset.lift_coe]
  simp [List.toFinset, ← hs, ← ht]

@[simp]
theorem leftMoves_ofFinsets {s t : Finset FGame} : {s | t}ꟳ.leftMoves = s := moves_ofFinsets.1

@[simp]
theorem rightMoves_ofFinsets {s t : Finset FGame} : {s | t}ꟳ.rightMoves = t := moves_ofFinsets.2

@[simp]
theorem ofFinsets_leftMoves_rightMoves (x : FGame) : {x.leftMoves | x.rightMoves}ꟳ = x := by
  ext <;> simp

@[simp]
theorem ofFinsets_inj {s₁ s₂ t₁ t₂ : Finset _}:
    {s₁ | t₁}ꟳ = {s₂ | t₂}ꟳ ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp [FGame.ext_iff]

/-- A (proper) subposition is any game in the transitive closure of `IsOption`. -/
def Subposition : FGame → FGame → Prop :=
  Relation.TransGen IsOption

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_leftMoves {x y : FGame} (h : x ∈ y.leftMoves) : Subposition x y :=
  Relation.TransGen.single (.of_mem_leftMoves h)

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_rightMoves {x y : FGame} (h : x ∈ y.rightMoves) : Subposition x y :=
  Relation.TransGen.single (.of_mem_rightMoves h)

theorem Subposition.trans {x y z : FGame} (h₁ : Subposition x y) (h₂ : Subposition y z) :
    Subposition x z :=
  Relation.TransGen.trans h₁ h₂

instance : IsTrans _ Subposition := inferInstanceAs (IsTrans _ (Relation.TransGen _))
instance : IsWellFounded _ Subposition := inferInstanceAs (IsWellFounded _ (Relation.TransGen _))
instance : WellFoundedRelation FGame := ⟨Subposition, instIsWellFoundedSubposition.wf⟩

/-- Discharges proof obligations of the form `⊢ Subposition ..` arising in termination proofs
of definitions using well-founded recursion on `FGame`. -/
macro "fgame_wf" : tactic =>
  `(tactic| all_goals solve_by_elim (maxDepth := 8)
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    Subposition.of_mem_leftMoves, Subposition.of_mem_rightMoves, Subposition.trans, Subtype.prop] )

/-! ### Basic games -/

/-- The game `0 = {∅ | ∅}ꟳ`. -/
instance : Zero FGame := ⟨{∅ | ∅}ꟳ⟩

theorem zero_def : 0 = {∅ | ∅}ꟳ := rfl

@[simp, game_cmp] theorem leftMoves_zero : leftMoves 0 = ∅ := leftMoves_ofFinsets ..
@[simp, game_cmp] theorem rightMoves_zero : rightMoves 0 = ∅ := rightMoves_ofFinsets ..

/-- The game `1 = {{0} | ∅}ꟳ`. -/
instance : One FGame := ⟨{{0} | ∅}ꟳ⟩

theorem one_def : 1 = {{0} | ∅}ꟳ := rfl

@[simp, game_cmp] theorem leftMoves_one : leftMoves 1 = {0} := leftMoves_ofFinsets ..
@[simp, game_cmp] theorem rightMoves_one : rightMoves 1 = ∅ := rightMoves_ofFinsets ..

/-! ### Order relations -/

/-- The less or equal relation on games.

If `0 ≤ x`, then Left can win `x` as the second player. `x ≤ y` means that `0 ≤ y - x`. -/
instance : LE FGame where
  le := Sym2.GameAdd.fix isOption_wf fun x y le ↦
    (∀ z (h : z ∈ x.leftMoves),  ¬le y z (Sym2.GameAdd.snd_fst (IsOption.of_mem_leftMoves h))) ∧
    (∀ z (h : z ∈ y.rightMoves), ¬le z x (Sym2.GameAdd.fst_snd (IsOption.of_mem_rightMoves h)))

/-- The less or fuzzy relation on pre-games. `x ⧏ y` is notation for `¬ y ≤ x`.

If `0 ⧏ x`, then Left can win `x` as the first player. `x ⧏ y` means that `0 ⧏ y - x`. -/
macro_rules | `($x ⧏ $y) => `(¬$y ≤ $x)

/-- Definition of `x ≤ y` on games, in terms of `⧏`. -/
theorem le_iff_forall_lf {x y : FGame} :
    x ≤ y ↔ (∀ z ∈ x.leftMoves, z ⧏ y) ∧ (∀ z ∈ y.rightMoves, x ⧏ z) :=
  propext_iff.1 <| Sym2.GameAdd.fix_eq ..

/-- Definition of `x ⧏ y` on games, in terms of `≤`. -/
theorem lf_iff_exists_le {x y : FGame} :
    x ⧏ y ↔ (∃ z ∈ y.leftMoves, x ≤ z) ∨ (∃ z ∈ x.rightMoves, z ≤ y) := by
  simpa [not_and_or, -not_and] using le_iff_forall_lf.not

/-- The definition of `x ≤ y` on games, in terms of `≤` two moves later.

Note that it's often more convenient to use `le_iff_forall_lf`, which only unfolds the definition by
one step. -/
theorem le_def {x y : FGame} : x ≤ y ↔
    (∀ a ∈ x.leftMoves, (∃ b ∈ y.leftMoves, a ≤ b) ∨ (∃ b ∈ a.rightMoves, b ≤ y)) ∧
    (∀ a ∈ y.rightMoves, (∃ b ∈ a.leftMoves, x ≤ b) ∨ (∃ b ∈ x.rightMoves, b ≤ a)) := by
  rw [le_iff_forall_lf]
  congr! 2 <;> rw [lf_iff_exists_le]

/-! ### Negation -/

/-- A "naive" auxiliary definition of negation, which uses the less efficient `Finset.image` instead
of `Finset.map`. -/
private def neg' (x : FGame.{u}) : FGame.{u} :=
  {x.rightMoves.attach.image (fun x ↦ neg' x.1) | x.leftMoves.attach.image (fun x ↦ neg' x.1)}ꟳ
termination_by x
decreasing_by fgame_wf

private theorem neg'_def (x : FGame) :
    neg' x = {x.rightMoves.image neg' | x.leftMoves.image neg'}ꟳ := by
  rw [neg', Finset.image_attach, Finset.image_attach]

private theorem neg'_neg' (x : FGame) : neg' (neg' x) = x := by
  simp_rw [neg'_def, leftMoves_ofFinsets, rightMoves_ofFinsets, Finset.image_image]
  rw [← ofFinsets_leftMoves_rightMoves x, ofFinsets_inj]
  have (a) (_ : IsOption a x) : neg' (neg' a) = a := neg'_neg' a
  aesop
termination_by x
decreasing_by fgame_wf

/-- A more efficient definition for negation, which makes use of injectivity. -/
private def negEmbedding {x : FGame} :
    {f : {y // Subposition y x} ↪ FGame // ⇑f = neg' ∘ Subtype.val} := by
  let f := fun y : {y // Subposition y x} ↦ have := y.2;
    {(y.1.rightMoves.attach.map
      (Subtype.impEmbedding _ _ fun _ ↦ .of_mem_rightMoves)).map negEmbedding.1 |
    (y.1.leftMoves.attach.map
      (Subtype.impEmbedding _ _ fun _ ↦ .of_mem_leftMoves)).map negEmbedding.1}ꟳ
  have hf : f = neg' ∘ Subtype.val := by
    refine funext fun ⟨y, _⟩ ↦ ?_
    rw [Function.comp_apply, neg'_def]
    simp_rw [f, Finset.map_eq_image, Finset.image_image]
    repeat rw [negEmbedding.2]
    simp [Subtype.impEmbedding, Function.comp_def]
  refine ⟨⟨f, fun y z h ↦ ?_⟩, hf⟩
  rw [← Subtype.coe_inj]
  simp_rw [hf] at h
  exact Function.Involutive.injective neg'_neg' h
termination_by x

instance : Neg FGame where
  neg x := (negEmbedding (x := {{x} | ∅}ꟳ)).1 ⟨x, by aesop⟩

private theorem neg_eq_neg' : (- ·) = neg' := by
  refine funext fun x ↦ ?_
  change negEmbedding.1 _ = _
  rw [negEmbedding.2]
  rfl

open Pointwise

theorem neg_def (x : FGame) : -x = {-x.rightMoves | -x.leftMoves}ꟳ := by
  simp_rw [Finset.neg_def]
  convert neg'_def x <;> exact neg_eq_neg'

instance : InvolutiveNeg FGame where
  neg_neg x := by convert neg'_neg' x <;> exact neg_eq_neg'

@[simp, game_cmp]
theorem leftMoves_neg (x : FGame) : (-x).leftMoves = -x.rightMoves := by
  rw [neg_def, leftMoves_ofFinsets]

@[simp, game_cmp]
theorem rightMoves_neg (x : FGame) : (-x).rightMoves = -x.leftMoves := by
  rw [neg_def, rightMoves_ofFinsets]

/-! ### Addition and subtraction -/

@[semireducible]
private def add' (x y : FGame.{u}) : FGame.{u} :=
  {x.leftMoves.attach.image (fun z ↦ add' z.1 y) ∪ y.leftMoves.attach.image (fun z ↦ add' x z.1) |
    x.rightMoves.attach.image (fun z ↦ add' z.1 y) ∪ y.rightMoves.attach.image (fun z ↦ add' x z.1)}ꟳ
termination_by (x, y)
decreasing_by fgame_wf

instance : Add FGame where
  add := add'

theorem add_def (x y : FGame) : x + y =
    {x.leftMoves.image (· + y) ∪ y.leftMoves.image (x + ·) |
      x.rightMoves.image (· + y) ∪ y.rightMoves.image (x + ·)}ꟳ := by
  change add' .. = _
  rw [add']
  aesop

instance : Sub FGame where
  sub x y := x + -y

/-! ### Repr -/

-- Allows us to recursively represent `FGame`s. This doesn't seem very idiomatic,
-- so we avoid putting it in pub space.
private instance _root_.Std.Format.instRepr : Repr Std.Format := ⟨fun x _ => x⟩

private unsafe def Multiset.repr_or_emptyset {α : Type*} [Repr α] : Repr (Multiset α) where
  reprPrec g n := if g.card = 0 then "∅" else Multiset.instRepr.reprPrec g n

-- TODO: can we hook into delab?
private unsafe def instRepr_aux : FGame → Std.Format :=
  fun g ↦ "{" ++
    Multiset.repr_or_emptyset.reprPrec (g.leftMoves.val.map instRepr_aux) 0 ++ " | " ++
    Multiset.repr_or_emptyset.reprPrec (g.rightMoves.val.map instRepr_aux) 0 ++ "}"

/-- The Repr of FGame. We prefer our notation of games {{a, b, c} | {d, e, f}} over the usual
flattened out {a, b, c|d, e, f} to match with the `IGame` builder syntax. -/
unsafe instance : Repr FGame := ⟨fun g _ ↦ instRepr_aux g⟩

/-! ### Results on `IGame`s -/

/-- Noncomputably turn `FGame`s into `IGame`s. -/
noncomputable def toIGame (x : FGame) : IGame :=
  !{Set.range fun y : x.leftMoves ↦ toIGame y | Set.range fun y : x.rightMoves ↦ toIGame y}
termination_by x
decreasing_by fgame_wf

theorem toIGame_def {x : FGame} :
    x.toIGame = !{toIGame '' x.leftMoves | toIGame '' x.rightMoves} := by
  rw [toIGame]
  aesop
