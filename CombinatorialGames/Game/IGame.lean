/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Reid Barton, Mario Carneiro, Isabel Longbottom, Kim Morrison, Yuyang Zhao
-/
import CombinatorialGames.Mathlib.Order
import CombinatorialGames.Register
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Logic.Hydra
import Mathlib.Logic.Small.Set
import Mathlib.Order.Comparable
import Mathlib.Order.GameAdd
import Mathlib.Lean.PrettyPrinter.Delaborator

/-!
# Combinatorial (pre-)games

The basic theory of combinatorial games, following Conway's book `On Numbers and Games`.

In ZFC, games are built inductively out of two other sets of games, representing the options for two
players Left and Right. In Lean, we instead define the type of games `IGame` as arising from two
`Small` sets of games, with notation `{s | t}ᴵ` (see `IGame.ofSets`). A `u`-small type `α : Type v`
is one that is equivalent to some `β : Type u`, and the distinction between small and large types in
a given universe closely mimics the ZFC distinction between sets and proper classes.

This definition requires some amount of setup, which we achieve through an auxiliary type `PGame`.
This type was historically the foundation for game theory in Lean, but it has now been superseded by
`IGame`, a quotient of it with the correct notion of equality. See the docstring on `PGame` for more
information.

We are also interested in further quotients of `IGame`. The quotient of games under equivalence
`x ≈ y ↔ x ≤ y ∧ y ≤ x`, which in the literature is often what is meant by a "combinatorial game",
is defined as `Game` in `CombinatorialGames.Game.Basic`. The surreal numbers `Surreal` are defined
as a quotient (of a subtype) of games in `CombinatorialGames.Surreal.Basic`.

## Conway induction

Most constructions within game theory, and as such, many proofs within it, are done by structural
induction. Structural induction on games is sometimes called "Conway induction".

The most straightforward way to employ Conway induction is by using the termination checker, with
the auxiliary `igame_wf` tactic. This uses `solve_by_elim` to search the context for proofs of the
form `y ∈ x.leftMoves` or `y ∈ x.rightMoves`, which prove termination. Alternatively, you can use
the explicit recursion principles `IGame.ofSetsRecOn` or `IGame.moveRecOn`.

## Order properties

Pregames have both a `≤` and a `<` relation, satisfying the properties of a `Preorder`. The relation
`0 < x` means that `x` can always be won by Left, while `0 ≤ x` means that `x` can be won by Left as
the second player. Likewise, `x < 0` means that `x` can always be won by Right, while `x ≤ 0` means
that `x` can be won by Right as the second player.

Note that we don't actually prove these characterizations. Indeed, in Conway's setup, combinatorial
game theory can be done entirely without the concept of a strategy. For instance, `IGame.zero_le`
implies that if `0 ≤ x`, then any move by Right satisfies `¬ x ≤ 0`, and `IGame.zero_lf` implies
that if `¬ x ≤ 0`, then some move by Left satisfies `0 ≤ x`. The strategy is thus already encoded
within these game relations.

For convenience, we define notation `x ⧏ y` (pronounced "less or fuzzy") for `¬ y ≤ x`, notation
`x ‖ y` for `¬ x ≤ y ∧ ¬ y ≤ x`, and notation `x ≈ y` for `x ≤ y ∧ y ≤ x`.

You can prove most (simple) inequalities on concrete games through the `game_cmp` tactic, which
repeatedly unfolds the definition of `≤` and applies `simp` until it solves the goal.

## Algebraic structures

Most of the usual arithmetic operations can be defined for games. Addition is defined for
`x = {s₁ | t₁}ᴵ` and `y = {s₂ | t₂}ᴵ` by `x + y = {s₁ + y, x + s₂ | t₁ + y, x + t₂}ᴵ`. Negation is
defined by `-{s | t}ᴵ = {-t | -s}ᴵ`.

The order structures interact in the expected way with arithmetic. In particular, `Game` is an
`OrderedAddCommGroup`. Meanwhile, `IGame` satisfies the slightly weaker axioms of a
`SubtractionCommMonoid`, since the equation `x - x = 0` is only true up to equivalence.
-/

universe u

-- TODO: This is a false positive due to the provisional duplicated IGame/IGame file path.
set_option linter.dupNamespace false
-- Computations can be performed through the `game_cmp` tactic.
noncomputable section

open Set Pointwise

/-! ### Pre-games -/

/-- The type of "pre-games", before we have quotiented by equivalence (`identicalSetoid`).

In ZFC, a combinatorial game is constructed from two sets of combinatorial games that have been
constructed at an earlier stage. To do this in type theory, we say that a pre-game is built
inductively from two families of pre-games indexed over any type in `Type u`. The resulting type
`PGame.{u}` lives in `Type (u + 1)`, reflecting that it is a proper class in ZFC.

This type was historically the foundation for game theory in Lean, but this led to many annoyances.
Most impactfully, this type has a notion of equality that is too strict: two games `0 = { | }` could
be distinct (and unprovably so!) if the indexed families of left and right sets were two distinct
empty types. To get the correct notion of equality, we define `IGame` as the quotient of this type
by the `Identical` relation, representing extensional equivalence.

This type has thus been relegated to an auxiliary construction for `IGame`. **You should not build
any substantial theory based on this type.** -/
inductive PGame : Type (u + 1)
  | mk : ∀ α β : Type u, (α → PGame) → (β → PGame) → PGame
compile_inductive% PGame

namespace PGame

/-- The indexing type for allowable moves by Left. -/
def LeftMoves : PGame → Type u
  | mk l _ _ _ => l

/-- The indexing type for allowable moves by Right. -/
def RightMoves : PGame → Type u
  | mk _ r _ _ => r

/-- The new game after Left makes an allowed move. -/
def moveLeft : ∀ g : PGame, LeftMoves g → PGame
  | mk _l _ L _ => L

/-- The new game after Right makes an allowed move. -/
def moveRight : ∀ g : PGame, RightMoves g → PGame
  | mk _ _r _ R => R

@[simp] theorem leftMoves_mk {xl xr xL xR} : (mk xl xr xL xR).LeftMoves = xl := rfl
@[simp] theorem moveLeft_mk {xl xr xL xR} : (mk xl xr xL xR).moveLeft = xL := rfl
@[simp] theorem rightMoves_mk {xl xr xL xR} : (mk xl xr xL xR).RightMoves = xr := rfl
@[simp] theorem moveRight_mk {xl xr xL xR} : (mk xl xr xL xR).moveRight = xR := rfl

/-- Two pre-games are identical if their left and right sets are identical. That is, `Identical x y`
if every left move of `x` is identical to some left move of `y`, every right move of `x` is
identical to some right move of `y`, and vice versa.

`IGame` is defined as a quotient of `PGame` under this relation. -/
def Identical : PGame.{u} → PGame.{u} → Prop
  | mk _ _ xL xR, mk _ _ yL yR =>
      Relator.BiTotal (fun i j ↦ Identical (xL i) (yL j)) ∧
      Relator.BiTotal (fun i j ↦ Identical (xR i) (yR j))

@[inherit_doc] scoped infix:50 " ≡ " => PGame.Identical

theorem identical_iff : ∀ {x y : PGame}, x ≡ y ↔
    Relator.BiTotal (x.moveLeft · ≡ y.moveLeft ·) ∧ Relator.BiTotal (x.moveRight · ≡ y.moveRight ·)
  | mk .., mk .. => Iff.rfl

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
def identicalSetoid : Setoid PGame :=
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

end PGame

/-! ### Game moves -/

/-- Games up to identity.

`IGame` uses the set-theoretic notion of equality on games, compared to `PGame`'s 'type-theoretic'
notion of equality.

This is not the same equivalence as used broadly in combinatorial game theory literature, as a game
like `{0, 1 | 0}` is not *identical* to `{1 | 0}`, despite being equivalent. However, many theorems
can be proven over the 'identical' equivalence relation, and the literature may occasionally
specifically use the 'identical' equivalence relation for this reason.

For the more common game equivalence from literature, see `Game.Basic`. -/
def IGame : Type (u + 1) :=
  Quotient PGame.identicalSetoid

namespace IGame
open scoped PGame

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
  refine (PGame.identical_iff.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩).mk_eq <;> intro i
  · obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hl ▸ mem_image_of_mem mk (mem_range_self (f := x.moveLeft) i)
    exact ⟨j, mk_eq_mk.1 hj.symm⟩
  · obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hl ▸ mem_image_of_mem mk (mem_range_self (f := y.moveLeft) i)
    exact ⟨j, mk_eq_mk.1 hj⟩
  · obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hr ▸ mem_image_of_mem mk (mem_range_self (f := x.moveRight) i)
    exact ⟨j, mk_eq_mk.1 hj.symm⟩
  · obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hr ▸ mem_image_of_mem mk (mem_range_self (f := y.moveRight) i)
    exact ⟨j, mk_eq_mk.1 hj⟩

/-- `IsOption x y` means that `x` is either a left or a right move for `y`. -/
@[aesop simp]
def IsOption (x y : IGame) : Prop :=
  x ∈ y.leftMoves ∪ y.rightMoves

theorem IsOption.of_mem_leftMoves {x y : IGame} : x ∈ y.leftMoves → IsOption x y := .inl
theorem IsOption.of_mem_rightMoves {x y : IGame} : x ∈ y.rightMoves → IsOption x y := .inr

instance (x : IGame.{u}) : Small.{u} {y // IsOption y x} :=
  inferInstanceAs (Small (x.leftMoves ∪ x.rightMoves :))

-- TODO: is there some more general theorem about well-founded relations on quotients
-- that we could use here?
theorem isOption_wf : WellFounded IsOption := by
  suffices ∀ x, Acc IsOption (mk x) from ⟨ind this⟩
  intro x
  induction x with
  | mk x _ _ _ hl hr =>
    constructor
    rintro ⟨y⟩ (h | h) <;>
    obtain ⟨_, ⟨i, rfl⟩, (hi : _ = Quot.mk _ _)⟩ := h
    exacts [hi ▸ hl i, hi ▸ hr i]

instance : IsWellFounded _ IsOption := ⟨isOption_wf⟩

theorem IsOption.irrefl (x : IGame) : ¬ IsOption x x := _root_.irrefl x

theorem self_not_mem_leftMoves (x : IGame) : x ∉ x.leftMoves :=
  fun hx ↦ IsOption.irrefl x (.of_mem_leftMoves hx)

theorem self_not_mem_rightMoves (x : IGame) : x ∉ x.rightMoves :=
  fun hx ↦ IsOption.irrefl x (.of_mem_rightMoves hx)

/-- **Conway recursion**: build data for a game by recursively building it on its
left and right sets.

See `ofSetsRecOn` for an alternate form. -/
@[elab_as_elim]
def moveRecOn {P : IGame → Sort*} (x)
    (H : Π x, (Π y ∈ x.leftMoves, P y) → (Π y ∈ x.rightMoves, P y) → P x) : P x :=
  isOption_wf.recursion x fun x IH ↦
    H x (fun _ h ↦ IH _ (.of_mem_leftMoves h)) (fun _ h ↦ IH _ (.of_mem_rightMoves h))

theorem moveRecOn_eq {P : IGame → Sort*} (x)
    (H : Π x, (Π y ∈ x.leftMoves, P y) → (Π y ∈ x.rightMoves, P y) → P x) :
    moveRecOn x H = H x (fun y _ ↦ moveRecOn y H) (fun y _ ↦ moveRecOn y H) :=
  isOption_wf.fix_eq ..

/-- A (proper) subposition is any game in the transitive closure of `IsOption`. -/
def Subposition : IGame → IGame → Prop :=
  Relation.TransGen IsOption

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_leftMoves {x y : IGame} (h : x ∈ y.leftMoves) : Subposition x y :=
  Relation.TransGen.single (.of_mem_leftMoves h)

@[aesop unsafe apply 50%]
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
  `(tactic| all_goals solve_by_elim (maxDepth := 8)
    [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
    Subposition.of_mem_leftMoves, Subposition.of_mem_rightMoves, Subposition.trans, Subtype.prop] )

/-- Construct an `IGame` from its left and right sets.

This is given notation `{s | t}ᴵ`, where the superscript `I` is to disambiguate from set builder
notation, and from the analogous constructors on `Game` and `Surreal`.

This function is regrettably noncomputable. Among other issues, sets simply do not carry data in
Lean. To perform computations on `IGame` we can instead make use of the `game_cmp` tactic. -/
def ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] : IGame.{u} :=
  mk <| .mk (Shrink s) (Shrink t)
    (out ∘ Subtype.val ∘ (equivShrink s).symm) (out ∘ Subtype.val ∘ (equivShrink t).symm)

@[inherit_doc] notation "{" s " | " t "}ᴵ" => ofSets s t

@[simp, game_cmp]
theorem leftMoves_ofSets (s t : Set _) [Small.{u} s] [Small.{u} t] : {s | t}ᴵ.leftMoves = s := by
  ext; simp [ofSets, range_comp]

@[simp, game_cmp]
theorem rightMoves_ofSets (s t : Set _) [Small.{u} s] [Small.{u} t] : {s | t}ᴵ.rightMoves = t := by
  ext; simp [ofSets, range_comp]

@[simp]
theorem ofSets_leftMoves_rightMoves (x : IGame) : {x.leftMoves | x.rightMoves}ᴵ = x := by
  ext <;> simp

@[simp]
theorem ofSets_inj {s₁ s₂ t₁ t₂ : Set _} [Small s₁] [Small s₂] [Small t₁] [Small t₂] :
    {s₁ | t₁}ᴵ = {s₂ | t₂}ᴵ ↔ s₁ = s₂ ∧ t₁ = t₂ := by
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

@[simp, game_cmp] theorem leftMoves_zero : leftMoves 0 = ∅ := leftMoves_ofSets ..
@[simp, game_cmp] theorem rightMoves_zero : rightMoves 0 = ∅ := rightMoves_ofSets ..

instance : Inhabited IGame := ⟨0⟩

/-- The game `1 = {{0} | ∅}ᴵ`. -/
instance : One IGame := ⟨{{0} | ∅}ᴵ⟩

theorem one_def : 1 = {{0} | ∅}ᴵ := rfl

@[simp, game_cmp] theorem leftMoves_one : leftMoves 1 = {0} := leftMoves_ofSets ..
@[simp, game_cmp] theorem rightMoves_one : rightMoves 1 = ∅ := rightMoves_ofSets ..

/-! ### Order relations -/

/-- The less or equal relation on games.

If `0 ≤ x`, then Left can win `x` as the second player. `x ≤ y` means that `0 ≤ y - x`. -/
instance : LE IGame where
  le := Sym2.GameAdd.fix isOption_wf fun x y le ↦
    (∀ z (h : z ∈ x.leftMoves),  ¬le y z (Sym2.GameAdd.snd_fst (IsOption.of_mem_leftMoves h))) ∧
    (∀ z (h : z ∈ y.rightMoves), ¬le z x (Sym2.GameAdd.fst_snd (IsOption.of_mem_rightMoves h)))

/-- The less or fuzzy relation on pre-games. `x ⧏ y` is notation for `¬ y ≤ x`.

If `0 ⧏ x`, then Left can win `x` as the first player. `x ⧏ y` means that `0 ⧏ y - x`. -/
notation:50 x:50 " ⧏ " y:50 => ¬ y ≤ x

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

theorem leftMove_lf_of_le {x y z : IGame} (h : x ≤ y) (h' : z ∈ x.leftMoves) : z ⧏ y :=
  (le_iff_forall_lf.1 h).1 z h'

theorem lf_rightMove_of_le {x y z : IGame} (h : x ≤ y) (h' : z ∈ y.rightMoves) : x ⧏ z :=
  (le_iff_forall_lf.1 h).2 z h'

theorem lf_of_le_leftMove {x y z : IGame} (h : x ≤ z) (h' : z ∈ y.leftMoves) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inl ⟨z, h', h⟩

theorem lf_of_rightMove_le {x y z : IGame} (h : z ≤ y) (h' : z ∈ x.rightMoves) : x ⧏ y :=
  lf_iff_exists_le.2 <| Or.inr ⟨z, h', h⟩

private theorem le_rfl' {x : IGame} : x ≤ x := by
  rw [le_iff_forall_lf]
  constructor <;> intro y hy
  exacts [lf_of_le_leftMove le_rfl' hy, lf_of_rightMove_le le_rfl' hy]
termination_by x
decreasing_by igame_wf

private theorem le_trans' {x y z : IGame} (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z := by
  rw [le_iff_forall_lf]
  constructor <;> intro a ha h₃
  exacts [leftMove_lf_of_le h₁ ha (le_trans' h₂ h₃), lf_rightMove_of_le h₂ ha (le_trans' h₃ h₁)]
termination_by isOption_wf.cutExpand.wrap {x, y, z}
decreasing_by
  on_goal 1 => convert (Relation.cutExpand_add_single {y, z} (IsOption.of_mem_leftMoves ha))
  on_goal 2 => convert (Relation.cutExpand_single_add (IsOption.of_mem_rightMoves ha) {x, y})
  all_goals simp [← Multiset.singleton_add, add_comm, add_assoc, WellFounded.wrap]

instance : Preorder IGame where
  le_refl _ := le_rfl'
  le_trans x y z := le_trans'

theorem leftMove_lf {x y : IGame} (h : y ∈ x.leftMoves) : y ⧏ x :=
  lf_of_le_leftMove le_rfl h

theorem lf_rightMove {x y : IGame} (h : y ∈ x.rightMoves) : x ⧏ y :=
  lf_of_rightMove_le le_rfl h

/-- The equivalence relation `x ≈ y` means that `x ≤ y` and `y ≤ x`. This is notation for
`AntisymmRel (⬝ ≤ ⬝) x y`. -/
infix:50 " ≈ " => AntisymmRel (· ≤ ·)

/-- The "fuzzy" relation `x ‖ y` means that `x ⧏ y` and `y ⧏ x`. This is notation for
`IncompRel (⬝ ≤ ⬝) x y`. -/
notation:50 x:50 " ‖ " y:50 => IncompRel (· ≤ ·) x y

/-
TODO: use `annotateGoToSyntaxDef` from
`Mathlib.Lean.PrettyPrinter.Delaborator` once mathlib is updated
-/
open Lean PrettyPrinter Delaborator SubExpr Qq in
@[delab app.AntisymmRel]
def delabEquiv : Delab := do
  let_expr f@AntisymmRel α r _ _ := ← getExpr | failure
  have u := f.constLevels![0]!
  have α : Q(Type u) := α
  have r : Q($α → $α → Prop) := r
  let le ← synthInstanceQ q(LE $α)
  _ ← assertDefEqQ q(($le).le) q($r)
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  `($x ≈ $y)

open Lean PrettyPrinter Delaborator SubExpr Qq in
@[delab app.IncompRel]
def delabFuzzy : Delab := do
  let_expr f@IncompRel α r _ _ := ← getExpr | failure
  have u := f.constLevels![0]!
  have α : Q(Type u) := α
  have r : Q($α → $α → Prop) := r
  let le ← synthInstanceQ q(LE $α)
  _ ← assertDefEqQ q(($le).le) q($r)
  let x ← withNaryArg 2 delab
  let y ← withNaryArg 3 delab
  `($x ‖ $y)

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

@[simp]
theorem zero_lt_one : (0 : IGame) < 1 := by
  rw [lt_iff_le_not_ge, le_iff_forall_lf, le_iff_forall_lf]
  simp

instance : ZeroLEOneClass IGame where
  zero_le_one := zero_lt_one.le

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

@[game_cmp]
theorem forall_leftMoves_neg {P : IGame → Prop} {x : IGame} :
    (∀ y ∈ (-x).leftMoves, P y) ↔ (∀ y ∈ x.rightMoves, P (-y)) := by
  rw [← (Equiv.neg _).forall_congr_right]; simp

@[game_cmp]
theorem forall_rightMoves_neg {P : IGame → Prop} {x : IGame} :
    (∀ y ∈ (-x).rightMoves, P y) ↔ (∀ y ∈ x.leftMoves, P (-y)) := by
  rw [← (Equiv.neg _).forall_congr_right]; simp

@[game_cmp]
theorem exists_leftMoves_neg {P : IGame → Prop} {x : IGame} :
    (∃ y ∈ (-x).leftMoves, P y) ↔ (∃ y ∈ x.rightMoves, P (-y)) := by
  rw [← (Equiv.neg _).exists_congr_right]; simp

@[game_cmp]
theorem exists_rightMoves_neg {P : IGame → Prop} {x : IGame} :
    (∃ y ∈ (-x).rightMoves, P y) ↔ (∃ y ∈ x.leftMoves, P (-y)) := by
  rw [← (Equiv.neg _).exists_congr_right]; simp

@[simp]
protected theorem neg_le_neg_iff {x y : IGame} : -x ≤ -y ↔ y ≤ x := by
  -- TODO: may have to add an `elab_as_elim` attr. in Mathlib
  refine Sym2.GameAdd.induction (C := fun x y ↦ -x ≤ -y ↔ y ≤ x) isOption_wf (fun x y IH ↦ ?_) x y
  dsimp at *
  rw [le_iff_forall_lf, le_iff_forall_lf, and_comm, forall_leftMoves_neg, forall_rightMoves_neg]
  congr! 3 with z hz z hz
  · rw [IH _ _ (Sym2.GameAdd.fst_snd (.of_mem_leftMoves hz))]
  · rw [IH _ _ (Sym2.GameAdd.snd_fst (.of_mem_rightMoves hz))]

protected theorem neg_le {x y : IGame} : -x ≤ y ↔ -y ≤ x := by
  simpa using @IGame.neg_le_neg_iff x (-y)
protected theorem le_neg {x y : IGame} : x ≤ -y ↔ y ≤ -x := by
  simpa using @IGame.neg_le_neg_iff (-x) y

@[simp]
protected theorem neg_lt_neg_iff {x y : IGame} : -x < -y ↔ y < x := by
  simp [lt_iff_le_not_ge]

protected theorem neg_lt {x y : IGame} : -x < y ↔ -y < x := by
  simpa using @IGame.neg_lt_neg_iff x (-y)
protected theorem lt_neg {x y : IGame} : x < -y ↔ y < -x := by
  simpa using @IGame.neg_lt_neg_iff (-x) y

@[simp]
theorem neg_equiv_neg_iff {x y : IGame} : -x ≈ -y ↔ x ≈ y := by
  simp [AntisymmRel, and_comm]

alias ⟨_, neg_congr⟩ := neg_equiv_neg_iff

@[simp]
theorem neg_fuzzy_neg_iff {x y : IGame} : -x ‖ -y ↔ x ‖ y := by
  simp [IncompRel, and_comm]

@[simp] theorem neg_le_zero {x : IGame} : -x ≤ 0 ↔ 0 ≤ x := by simpa using @IGame.neg_le x 0
@[simp] theorem zero_le_neg {x : IGame} : 0 ≤ -x ↔ x ≤ 0 := by simpa using @IGame.le_neg 0 x
@[simp] theorem neg_lt_zero {x : IGame} : -x < 0 ↔ 0 < x := by simpa using @IGame.neg_lt x 0
@[simp] theorem zero_lt_neg {x : IGame} : 0 < -x ↔ x < 0 := by simpa using @IGame.lt_neg 0 x

@[simp] theorem neg_equiv_zero {x : IGame} : -x ≈ 0 ↔ x ≈ 0 := by
  simpa using @IGame.neg_equiv_neg_iff x 0
@[simp] theorem zero_equiv_neg {x : IGame} : 0 ≈ -x ↔ 0 ≈ x := by
  simpa using @IGame.neg_equiv_neg_iff 0 x

@[simp] theorem neg_fuzzy_zero {x : IGame} : -x ‖ 0 ↔ x ‖ 0 := by
  simpa using @IGame.neg_fuzzy_neg_iff x 0
@[simp] theorem zero_fuzzy_neg {x : IGame} : 0 ‖ -x ↔ 0 ‖ x := by
  simpa using @IGame.neg_fuzzy_neg_iff 0 x

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
  rw [add_eq, leftMoves_ofSets]

@[simp]
theorem rightMoves_add (x y : IGame) :
    (x + y).rightMoves = (· + y) '' x.rightMoves ∪ (x + ·) '' y.rightMoves := by
  rw [add_eq, rightMoves_ofSets]

theorem add_left_mem_leftMoves_add {x y : IGame} (h : x ∈ y.leftMoves) (z : IGame) :
    z + x ∈ (z + y).leftMoves := by
  rw [leftMoves_add]; right; use x

theorem add_right_mem_leftMoves_add {x y : IGame} (h : x ∈ y.leftMoves) (z : IGame) :
    x + z ∈ (y + z).leftMoves := by
  rw [leftMoves_add]; left; use x

theorem add_left_mem_rightMoves_add {x y : IGame} (h : x ∈ y.rightMoves) (z : IGame) :
    z + x ∈ (z + y).rightMoves := by
  rw [rightMoves_add]; right; use x

theorem add_right_mem_rightMoves_add {x y : IGame} (h : x ∈ y.rightMoves) (z : IGame) :
    x + z ∈ (y + z).rightMoves := by
  rw [rightMoves_add]; left; use x

theorem IsOption.add_left {x y z : IGame} (h : IsOption x y) : IsOption (z + x) (z + y) := by
  aesop

theorem IsOption.add_right {x y z : IGame} (h : IsOption x y) : IsOption (x + z) (y + z) := by
  aesop

@[game_cmp]
theorem forall_leftMoves_add {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x + y).leftMoves, P a) ↔
      (∀ a ∈ x.leftMoves, P (a + y)) ∧ (∀ b ∈ y.leftMoves, P (x + b)) := by
  aesop

@[game_cmp]
theorem forall_rightMoves_add {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x + y).rightMoves, P a) ↔
      (∀ a ∈ x.rightMoves, P (a + y)) ∧ (∀ b ∈ y.rightMoves, P (x + b)) := by
  aesop

@[game_cmp]
theorem exists_leftMoves_add {P : IGame → Prop} {x y : IGame} :
    (∃ a ∈ (x + y).leftMoves, P a) ↔
      (∃ a ∈ x.leftMoves, P (a + y)) ∨ (∃ b ∈ y.leftMoves, P (x + b)) := by
  aesop

@[game_cmp]
theorem exists_rightMoves_add {P : IGame → Prop} {x y : IGame} :
    (∃ a ∈ (x + y).rightMoves, P a) ↔
      (∃ a ∈ x.rightMoves, P (a + y)) ∨ (∃ b ∈ y.rightMoves, P (x + b)) := by
  aesop

instance : AddZeroClass IGame := by
  constructor <;>
  · refine (moveRecOn · fun _ _ _ ↦ ?_)
    aesop

@[simp]
theorem add_eq_zero_iff {x y : IGame} : x + y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor <;> simp_all [IGame.ext_iff]

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

/-- The subtraction of `x` and `y` is defined as `x + (-y)`. -/
instance : SubNegMonoid IGame where
  zsmul := zsmulRec

@[simp]
theorem leftMoves_sub (x y : IGame) :
    (x - y).leftMoves = (· - y) '' x.leftMoves ∪ (x + ·) '' (-y.rightMoves) := by
  simp [sub_eq_add_neg]

@[simp]
theorem rightMoves_sub (x y : IGame) :
    (x - y).rightMoves = (· - y) '' x.rightMoves ∪ (x + ·) '' (-y.leftMoves) := by
  simp [sub_eq_add_neg]

theorem sub_left_mem_leftMoves_sub {x y : IGame} (h : x ∈ y.rightMoves) (z : IGame) :
    z - x ∈ (z - y).leftMoves := by
  apply add_left_mem_leftMoves_add; simpa

theorem sub_right_mem_leftMoves_sub {x y : IGame} (h : x ∈ y.leftMoves) (z : IGame) :
    x - z ∈ (y - z).leftMoves :=
  add_right_mem_leftMoves_add h _

theorem sub_left_mem_rightMoves_sub {x y : IGame} (h : x ∈ y.leftMoves) (z : IGame) :
    z - x ∈ (z - y).rightMoves := by
  apply add_left_mem_rightMoves_add; simpa

theorem sub_right_mem_rightMoves_sub {x y : IGame} (h : x ∈ y.rightMoves) (z : IGame) :
    x - z ∈ (y - z).rightMoves :=
  add_right_mem_rightMoves_add h _

private theorem neg_add' (x y : IGame) : -(x + y) = -x + -y := by
  ext <;>
  · simp
    rw [← (Equiv.neg IGame).exists_congr_right]
    nth_rewrite 2 [← (Equiv.neg IGame).exists_congr_right]
    congr! 3 <;>
    · refine and_congr_right_iff.2 fun _ ↦ ?_
      rw [Equiv.neg_apply, ← neg_inj, neg_add', neg_neg, neg_neg]
termination_by (x, y)
decreasing_by igame_wf

instance : SubtractionCommMonoid IGame where
  neg_neg := neg_neg
  neg_add_rev x y := by rw [neg_add', add_comm]
  neg_eq_of_add := by simp
  add_comm := add_comm

private theorem sub_self_le (x : IGame) : x - x ≤ 0 := by
  rw [le_zero, leftMoves_sub]
  rintro _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
  · exact lf_of_rightMove_le (sub_self_le y) (sub_left_mem_rightMoves_sub hy y)
  · apply lf_of_rightMove_le (sub_self_le (-y))
    rw [mem_neg] at hy
    rw [sub_neg_eq_add]
    exact add_right_mem_rightMoves_add hy _
termination_by x
decreasing_by igame_wf

/-- The sum of a game and its negative is equivalent, though not necessarily identical to zero. -/
theorem sub_self_equiv (x : IGame) : x - x ≈ 0 := by
  rw [AntisymmRel, ← neg_le_zero, neg_sub, and_self]
  exact sub_self_le x

/-- The sum of a game and its negative is equivalent, though not necessarily identical to zero. -/
theorem neg_add_equiv (x : IGame) : -x + x ≈ 0 := by
  simpa [add_comm] using sub_self_equiv x

private theorem add_le_add_left' {x y : IGame} (h : x ≤ y) (z : IGame) : z + x ≤ z + y := by
  rw [le_iff_forall_lf, leftMoves_add, rightMoves_add]
  refine ⟨?_, ?_⟩ <;> rintro a (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
  · exact lf_of_le_leftMove (add_le_add_left' h a) (add_right_mem_leftMoves_add ha y)
  · obtain (⟨b, hb, hb'⟩ | ⟨b, hb, hb'⟩) := lf_iff_exists_le.1 (leftMove_lf_of_le h ha)
    · exact lf_of_le_leftMove (add_le_add_left' hb' z) (add_left_mem_leftMoves_add hb z)
    · exact lf_of_rightMove_le (add_le_add_left' hb' z) (add_left_mem_rightMoves_add hb z)
  · exact lf_of_rightMove_le (add_le_add_left' h a) (add_right_mem_rightMoves_add ha x)
  · obtain (⟨b, hb, hb'⟩ | ⟨b, hb, hb'⟩) := lf_iff_exists_le.1 (lf_rightMove_of_le h ha)
    · exact lf_of_le_leftMove (add_le_add_left' hb' z) (add_left_mem_leftMoves_add hb z)
    · exact lf_of_rightMove_le (add_le_add_left' hb' z) (add_left_mem_rightMoves_add hb z)
termination_by (x, y, z)
decreasing_by igame_wf

private theorem add_le_add_right' {x y : IGame} (h : x ≤ y) (z : IGame) : x + z ≤ y + z := by
  simpa [add_comm] using add_le_add_left' h z

instance : AddLeftMono IGame := ⟨fun x _ _ h ↦ add_le_add_left' h x⟩
instance : AddRightMono IGame := ⟨fun x _ _ h ↦ add_le_add_right' h x⟩

instance : AddLeftReflectLE IGame where
  elim x y z h := by
    rw [← zero_add y, ← zero_add z]
    apply (add_le_add_right (neg_add_equiv x).ge y).trans
    rw [add_assoc]
    apply (add_le_add_left h (-x)).trans
    rw [← add_assoc]
    exact add_le_add_right (neg_add_equiv x).le z

instance : AddRightReflectLE IGame :=
  addRightReflectLE_of_addLeftReflectLE _

instance : AddLeftStrictMono IGame where
  elim x y z h := by
    apply lt_of_le_not_ge (add_le_add_left h.le x)
    contrapose! h
    exact (le_of_add_le_add_left h).not_gt

instance : AddRightStrictMono IGame :=
  addRightStrictMono_of_addLeftStrictMono _

-- TODO: [AddLeftMono α] [AddLeftReflectLE α] → AddLeftReflectLT α
instance : AddLeftReflectLT IGame where
  elim _ := by simp [lt_iff_le_not_ge]

instance : AddRightReflectLT IGame :=
  addRightReflectLT_of_addLeftReflectLT _

-- TODO: add the general versions of this to Mathlib

theorem add_congr {a b : IGame} (h₁ : a ≈ b) {c d : IGame} (h₂ : c ≈ d) : a + c ≈ b + d :=
  ⟨add_le_add h₁.1 h₂.1, add_le_add h₁.2 h₂.2⟩

theorem add_congr_left {a b c : IGame} (h : a ≈ b) : a + c ≈ b + c :=
  add_congr h .rfl

theorem add_congr_right {a b c : IGame} (h : a ≈ b) : c + a ≈ c + b :=
  add_congr .rfl h

@[simp]
theorem add_fuzzy_add_iff_left {a b c : IGame} : a + b ‖ a + c ↔ b ‖ c := by
  simp [IncompRel]

@[simp]
theorem add_fuzzy_add_iff_right {a b c : IGame} : b + a ‖ c + a ↔ b ‖ c := by
  simp [IncompRel]

theorem sub_congr {a b : IGame} (h₁ : a ≈ b) {c d : IGame} (h₂ : c ≈ d) : a - c ≈ b - d :=
  add_congr h₁ (neg_congr h₂)

theorem sub_congr_left {a b c : IGame} (h : a ≈ b) : a - c ≈ b - c :=
  sub_congr h .rfl

theorem sub_congr_right {a b c : IGame} (h : a ≈ b) : c - a ≈ c - b :=
  sub_congr .rfl h

/-- We define the `NatCast` instance as `↑0 = 0` and `↑(n + 1) = {{↑n} | ∅}ᴵ`.

Note that this is equivalent, but not identical, to the more common definition `↑n = {Iio n | ∅}ᴵ`.
For that, use `Ordinal.toIGame`. -/
instance : AddMonoidWithOne IGame where

/-- This version of the theorem is more convenient for the `game_cmp` tactic. -/
@[game_cmp]
theorem leftMoves_natCast_succ' : ∀ n : ℕ, leftMoves n.succ = {(n : IGame)}
  | 0 => by simp
  | n + 1 => by
    rw [Nat.cast_succ, leftMoves_add, leftMoves_natCast_succ']
    simp

@[simp 1100] -- This should trigger before `leftMoves_add`.
theorem leftMoves_natCast_succ (n : ℕ) : leftMoves (n + 1) = {(n : IGame)} :=
  leftMoves_natCast_succ' n

@[simp 1100, game_cmp] -- This should trigger before `rightMoves_add`.
theorem rightMoves_natCast : ∀ n : ℕ, rightMoves n = ∅
  | 0 => by simp
  | n + 1 => by
    rw [Nat.cast_succ, rightMoves_add, rightMoves_natCast]
    simp

@[simp 1100, game_cmp]
theorem leftMoves_ofNat (n : ℕ) [n.AtLeastTwo] : leftMoves ofNat(n) = {((n - 1 : ℕ) : IGame)} := by
  change leftMoves n = _
  rw [← Nat.succ_pred (NeZero.out (n := n)), leftMoves_natCast_succ']
  simp

@[simp 1100, game_cmp]
theorem rightMoves_ofNat (n : ℕ) [n.AtLeastTwo] : rightMoves ofNat(n) = ∅ :=
  rightMoves_natCast n

theorem natCast_succ_eq (n : ℕ) : (n + 1 : IGame) = {{(n : IGame)} | ∅}ᴵ := by
  ext <;> simp

/-- Every left option of a natural number is equal to a smaller natural number. -/
theorem eq_natCast_of_mem_leftMoves_natCast {n : ℕ} {x : IGame} (hx : x ∈ leftMoves n) :
    ∃ m : ℕ, m < n ∧ m = x := by
  cases n with
  | zero => simp at hx
  | succ n =>
    use n
    simp_all

instance : IntCast IGame where
  intCast
  | .ofNat n => n
  | .negSucc n => -(n + 1)

@[simp] theorem intCast_nat (n : ℕ) : ((n : ℤ) : IGame) = n := rfl
@[simp] theorem intCast_ofNat (n : ℕ) : ((ofNat(n) : ℤ) : IGame) = n := rfl
@[simp] theorem intCast_negSucc (n : ℕ) : (Int.negSucc n : IGame) = -(n + 1) := rfl

theorem intCast_zero : ((0 : ℤ) : IGame) = 0 := rfl
theorem intCast_one : ((1 : ℤ) : IGame) = 1 := by simp

@[simp]
theorem intCast_neg (n : ℤ) : ((-n : ℤ) : IGame) = -(n : IGame) := by
  cases n with
  | ofNat n =>
    cases n with
    | zero => simp
    | succ n => rfl
  | negSucc n => exact (neg_neg _).symm

theorem eq_sub_one_of_mem_leftMoves_intCast {n : ℤ} {x : IGame} (hx : x ∈ leftMoves n) :
    x = (n - 1 : ℤ) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · cases n
    · simp at hx
    · rw [intCast_nat] at hx
      simp_all
  · simp at hx

theorem eq_add_one_of_mem_rightMoves_intCast {n : ℤ} {x : IGame} (hx : x ∈ rightMoves n) :
    x = (n + 1 : ℤ) := by
  have : -x ∈ leftMoves (-n : ℤ) := by simpa
  rw [← neg_inj]
  simpa [← IGame.intCast_neg, add_comm] using eq_sub_one_of_mem_leftMoves_intCast this

/-- Every left option of an integer is equal to a smaller integer. -/
theorem eq_intCast_of_mem_leftMoves_intCast {n : ℤ} {x : IGame} (hx : x ∈ leftMoves n) :
    ∃ m : ℤ, m < n ∧ m = x := by
  use n - 1
  simp [eq_sub_one_of_mem_leftMoves_intCast hx]

/-- Every right option of an integer is equal to a larger integer. -/
theorem eq_intCast_of_mem_rightMoves_intCast {n : ℤ} {x : IGame} (hx : x ∈ rightMoves n) :
    ∃ m : ℤ, n < m ∧ m = x := by
  use n + 1
  simp [eq_add_one_of_mem_rightMoves_intCast hx]

/-! ### Multiplication -/

-- TODO: upstream
attribute [aesop apply unsafe 50%] Prod.Lex.left Prod.Lex.right

def mul' (x y : IGame) : IGame :=
  {(range fun a : (x.leftMoves ×ˢ y.leftMoves ∪ x.rightMoves ×ˢ y.rightMoves :) ↦
    mul' a.1.1 y + mul' x a.1.2 - mul' a.1.1 a.1.2) |
  (range fun a : (x.leftMoves ×ˢ y.rightMoves ∪ x.rightMoves ×ˢ y.leftMoves :) ↦
    mul' a.1.1 y + mul' x a.1.2 - mul' a.1.1 a.1.2)}ᴵ
termination_by (x, y)
decreasing_by all_goals aesop

/-- The product of `x = {s₁ | t₁}ᴵ` and `y = {s₂ | t₂}ᴵ` is
`{a₁ * y + x * b₁ - a₁ * b₁ | a₂ * y + x * b₂ - a₂ * b₂}ᴵ`, where `(a₁, b₁) ∈ s₁ ×ˢ s₂ ∪ t₁ ×ˢ t₂`
and `(a₂, b₂) ∈ s₁ ×ˢ t₂ ∪ t₁ ×ˢ s₂`.

Using `IGame.mulOption`, this can alternatively be written as
`x * y = {mulOption x y a₁ b₁ | mulOption x y a₂ b₂}ᴵ`. -/
instance : Mul IGame where
  mul := mul'

/-- The general option of `x * y` looks like `a * y + x * b - a * b`, for `a` and `b` options of
`x` and `y`, respectively. -/
@[pp_nodot, game_cmp]
def mulOption (x y a b : IGame) : IGame :=
  a * y + x * b - a * b

theorem mul_eq (x y : IGame) : x * y =
    {(fun a ↦ mulOption x y a.1 a.2) ''
      (x.leftMoves ×ˢ y.leftMoves ∪ x.rightMoves ×ˢ y.rightMoves) |
    (fun a ↦ mulOption x y a.1 a.2) ''
      (x.leftMoves ×ˢ y.rightMoves ∪ x.rightMoves ×ˢ y.leftMoves)}ᴵ := by
  change mul' _ _ = _
  rw [mul']
  simp [mulOption, HMul.hMul, Mul.mul, Set.ext_iff]

theorem ofSets_mul_ofSets (s₁ t₁ s₂ t₂ : Set IGame) [Small s₁] [Small t₁] [Small s₂] [Small t₂] :
    {s₁ | t₁}ᴵ * {s₂ | t₂}ᴵ =
      {(fun a ↦ mulOption {s₁ | t₁}ᴵ {s₂ | t₂}ᴵ a.1 a.2) '' (s₁ ×ˢ s₂ ∪ t₁ ×ˢ t₂) |
      (fun a ↦ mulOption {s₁ | t₁}ᴵ {s₂ | t₂}ᴵ a.1 a.2) '' (s₁ ×ˢ t₂ ∪ t₁ ×ˢ s₂)}ᴵ := by
  rw [mul_eq]
  simp

@[simp]
theorem leftMoves_mul (x y : IGame) :
    (x * y).leftMoves = (fun a ↦ mulOption x y a.1 a.2) ''
      (x.leftMoves ×ˢ y.leftMoves ∪ x.rightMoves ×ˢ y.rightMoves) := by
  rw [mul_eq, leftMoves_ofSets]

@[simp]
theorem rightMoves_mul (x y : IGame) :
    (x * y).rightMoves = (fun a ↦ mulOption x y a.1 a.2) ''
      (x.leftMoves ×ˢ y.rightMoves ∪ x.rightMoves ×ˢ y.leftMoves) := by
  rw [mul_eq, rightMoves_ofSets]

@[simp]
theorem leftMoves_mulOption (x y a b : IGame) :
    (mulOption x y a b).leftMoves = leftMoves (a * y + x * b - a * b) :=
  rfl

@[simp]
theorem rightMoves_mulOption (x y a b : IGame) :
    (mulOption x y a b).rightMoves = rightMoves (a * y + x * b - a * b) :=
  rfl

theorem mulOption_left_left_mem_leftMoves_mul {x y a b : IGame}
    (h₁ : a ∈ x.leftMoves) (h₂ : b ∈ y.leftMoves) : mulOption x y a b ∈ (x * y).leftMoves := by
  rw [leftMoves_mul]; use (a, b); simp_all

theorem mulOption_right_right_mem_leftMoves_mul {x y a b : IGame}
    (h₁ : a ∈ x.rightMoves) (h₂ : b ∈ y.rightMoves) : mulOption x y a b ∈ (x * y).leftMoves := by
  rw [leftMoves_mul]; use (a, b); simp_all

theorem mulOption_left_right_mem_rightMoves_mul {x y a b : IGame}
    (h₁ : a ∈ x.leftMoves) (h₂ : b ∈ y.rightMoves) : mulOption x y a b ∈ (x * y).rightMoves := by
  rw [rightMoves_mul]; use (a, b); simp_all

theorem mulOption_right_left_mem_rightMoves_mul {x y a b : IGame}
    (h₁ : a ∈ x.rightMoves) (h₂ : b ∈ y.leftMoves) : mulOption x y a b ∈ (x * y).rightMoves := by
  rw [rightMoves_mul]; use (a, b); simp_all

theorem IsOption.mul {x y a b : IGame} (h₁ : IsOption a x) (h₂ : IsOption b y) :
    IsOption (mulOption x y a b) (x * y) := by
  aesop

@[game_cmp]
theorem forall_leftMoves_mul {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x * y).leftMoves, P a) ↔
      (∀ a ∈ x.leftMoves, ∀ b ∈ y.leftMoves, P (mulOption x y a b)) ∧
      (∀ a ∈ x.rightMoves, ∀ b ∈ y.rightMoves, P (mulOption x y a b)) := by
  aesop

@[game_cmp]
theorem forall_rightMoves_mul {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x * y).rightMoves, P a) ↔
      (∀ a ∈ x.leftMoves, ∀ b ∈ y.rightMoves, P (mulOption x y a b)) ∧
      (∀ a ∈ x.rightMoves, ∀ b ∈ y.leftMoves, P (mulOption x y a b)) := by
  aesop

@[game_cmp]
theorem exists_leftMoves_mul {P : IGame → Prop} {x y : IGame} :
    (∃ a ∈ (x * y).leftMoves, P a) ↔
      (∃ a ∈ x.leftMoves, ∃ b ∈ y.leftMoves, P (mulOption x y a b)) ∨
      (∃ a ∈ x.rightMoves, ∃ b ∈ y.rightMoves, P (mulOption x y a b)) := by
  aesop

@[game_cmp]
theorem exists_rightMoves_mul {P : IGame → Prop} {x y : IGame} :
    (∃ a ∈ (x * y).rightMoves, P a) ↔
      (∃ a ∈ x.leftMoves, ∃ b ∈ y.rightMoves, P (mulOption x y a b)) ∨
      (∃ a ∈ x.rightMoves, ∃ b ∈ y.leftMoves, P (mulOption x y a b)) := by
  aesop

instance : MulZeroClass IGame := by
  constructor <;>
  · refine (moveRecOn · fun _ _ _ ↦ ?_)
    aesop

instance : MulOneClass IGame := by
  constructor <;>
  · refine (moveRecOn · fun _ _ _ ↦ ?_)
    aesop (add simp [mulOption, and_assoc])

private theorem mul_comm' (x y : IGame) : x * y = y * x := by
  ext
  all_goals
    simp only [leftMoves_mul, rightMoves_mul, mem_image, mem_prod, mem_union, Prod.exists,
      and_comm, or_comm]
    rw [exists_comm]
    congr! 4 with b a
    rw [and_congr_left_iff]
    rintro (⟨_, _⟩ | ⟨_, _⟩) <;>
      rw [mulOption, mulOption, mul_comm' x, mul_comm' _ y, add_comm, mul_comm' a b]
termination_by (x, y)
decreasing_by igame_wf

instance : CommMagma IGame where
  mul_comm := mul_comm'

theorem mulOption_comm (x y a b : IGame) : mulOption x y a b = mulOption y x b a := by
  simp [mulOption, add_comm, mul_comm]

private theorem neg_mul' (x y : IGame) : -x * y = -(x * y) := by
  ext
  all_goals
    simp only [leftMoves_mul, leftMoves_neg, rightMoves_mul, rightMoves_neg,
      mem_image, mem_union, mem_prod, mem_neg, Prod.exists]
    rw [← (Equiv.neg _).exists_congr_right]
    simp only [Equiv.neg_apply, neg_neg, and_comm, mulOption, or_comm]
    congr! 4
    rw [and_congr_right_iff]
    rintro (⟨_, _⟩ | ⟨_, _⟩)
    all_goals
      rw [← neg_inj, neg_mul', neg_mul', neg_mul']
      simp [sub_eq_add_neg, add_comm]
termination_by (x, y)
decreasing_by igame_wf

private theorem mul_neg' (x y : IGame) : x * -y = -(x * y) := by
  rw [mul_comm, neg_mul', mul_comm]

instance : HasDistribNeg IGame where
  neg_mul := neg_mul'
  mul_neg := mul_neg'

theorem mulOption_neg_left (x y a b : IGame) : mulOption (-x) y a b = -mulOption x y (-a) b := by
  simp [mulOption, sub_eq_neg_add, add_comm]

theorem mulOption_neg_right (x y a b : IGame) : mulOption x (-y) a b = -mulOption x y a (-b) := by
  simp [mulOption, sub_eq_neg_add, add_comm]

theorem mulOption_neg (x y a b : IGame) : mulOption (-x) (-y) a b = mulOption x y (-a) (-b) := by
  simp [mulOption, sub_eq_neg_add, add_comm]

/-! Distributivity and associativity only hold up to equivalence; we prove this in
`CombinatorialGames.Game.Basic`. -/

/-! ### Division -/

/-- An auxiliary inductive type to enumerate the options of `IGame.inv`. -/
private inductive InvTy (l r : Type u) : Bool → Type u
  | zero : InvTy l r false
  | left₁ : r → InvTy l r false → InvTy l r false
  | left₂ : l → InvTy l r true → InvTy l r false
  | right₁ : l → InvTy l r false → InvTy l r true
  | right₂ : r → InvTy l r true → InvTy l r true

private def InvTy.val' {x : IGame}
    (IHl : Shrink {y ∈ x.leftMoves | 0 < y} → IGame)
    (IHr : Shrink {y ∈ x.rightMoves | 0 < y} → IGame) (b : Bool) :
    InvTy (Shrink {y ∈ x.leftMoves | 0 < y}) (Shrink {y ∈ x.rightMoves | 0 < y}) b → IGame
  | InvTy.zero => 0
  | InvTy.left₁ i j => (1 + ((equivShrink _).symm i - x) * val' IHl IHr _ j) * IHr i
  | InvTy.left₂ i j => (1 + ((equivShrink _).symm i - x) * val' IHl IHr _ j) * IHl i
  | InvTy.right₁ i j => (1 + ((equivShrink _).symm i - x) * val' IHl IHr _ j) * IHl i
  | InvTy.right₂ i j => (1 + ((equivShrink _).symm i - x) * val' IHl IHr _ j) * IHr i

private def inv' (x : IGame.{u}) : IGame.{u} :=
  let IHl : Shrink {y ∈ x.leftMoves | 0 < y} → IGame :=
    fun x ↦ inv' (Subtype.val <| (equivShrink _).symm x)
  let IHr : Shrink {y ∈ x.rightMoves | 0 < y} → IGame :=
    fun x ↦ inv' (Subtype.val <| (equivShrink _).symm x)
  {.range (InvTy.val' IHl IHr false) | .range (InvTy.val' IHl IHr true)}ᴵ
termination_by x
decreasing_by
· exact .of_mem_leftMoves ((equivShrink _).symm x).2.1
· exact .of_mem_rightMoves ((equivShrink _).symm x).2.1

private abbrev InvTy.val (x : IGame) (b : Bool)
    (i : InvTy (Shrink {y ∈ x.leftMoves | 0 < y}) (Shrink {y ∈ x.rightMoves | 0 < y}) b) : IGame :=
  i.val' (inv' ∘ Subtype.val ∘ (equivShrink _).symm) (inv' ∘ Subtype.val ∘ (equivShrink _).symm) b

/-- The inverse of a positive game `x = {s | t}ᴵ` is `{s' | t'}ᴵ`, where `s'` and `t'` are the
smallest sets such that `0 ∈ s'`, and such that `(1 + (z - x) * a) / z, (1 + (y - x) * b) / y ∈ s'`
and `(1 + (y - x) * a) / y, (1 + (z - x) * b) / z ∈ t'` for `y ∈ s` positive, `z ∈ t`, `a ∈ s'`, and
`b ∈ t'`.

If `x` is negative, we define `x⁻¹ = -(-x)⁻¹`. For any other game, we set `x⁻¹ = 0`.

If `x` is a non-zero numeric game, then `x * x⁻¹ ≈ 1`. The value of this function on any non-numeric
game should be treated as a junk value. -/
instance : Inv IGame where
  inv x := by classical exact if 0 < x then inv' x else if x < 0 then -inv' (-x) else 0

instance : Div IGame where
  div x y := x * y⁻¹

open Classical in
private theorem inv_eq' {x : IGame} :
    x⁻¹ = if 0 < x then inv' x else if x < 0 then -inv' (-x) else 0 :=
  rfl

private theorem inv_eq {x : IGame.{u}} (hx : 0 < x) :
    x⁻¹ = {.range (InvTy.val x false) | .range (InvTy.val x true)}ᴵ := by
  rw [inv_eq', if_pos hx, inv']
  rfl

protected theorem div_eq_mul_inv (x y : IGame) : x / y = x * y⁻¹ := rfl

theorem inv_of_equiv_zero {x : IGame} (h : x ≈ 0) : x⁻¹ = 0 := by simp [inv_eq', h.not_lt, h.not_gt]

@[simp] protected theorem inv_zero : (0 : IGame)⁻¹ = 0 := inv_of_equiv_zero .rfl
@[simp] protected theorem zero_div (x : IGame) : 0 / x = 0 := zero_mul _
@[simp] protected theorem neg_div (x y : IGame) : -x / y = -(x / y) := neg_mul ..

@[simp]
protected theorem inv_neg (x : IGame) : (-x)⁻¹ = -x⁻¹ := by
  rw [inv_eq', inv_eq']
  obtain h | h | h | h := lt_or_antisymmRel_or_gt_or_incompRel x 0
  repeat
    simp [h, h.asymm]
    simp [h.not_lt, h.not_gt]

/-- The general option of `x⁻¹` looks like `(1 + (y - x) * a) / y`, for `y` an option of `x`, and
`a` some other "earlier" option of `x⁻¹`. -/
@[pp_nodot]
def invOption (x y a : IGame) : IGame :=
  (1 + (y - x) * a) / y

private theorem invOption_eq {x y a : IGame} (hy : 0 < y) :
    invOption x y a = (1 + (y - x) * a) * inv' y := by
  rw [invOption, IGame.div_eq_mul_inv, inv_eq', if_pos hy]

theorem zero_mem_leftMoves_inv {x : IGame} (hx : 0 < x) : 0 ∈ x⁻¹.leftMoves := by
  rw [inv_eq hx, leftMoves_ofSets]
  exact ⟨InvTy.zero, rfl⟩

theorem inv_nonneg {x : IGame} (hx : 0 < x) : 0 ⧏ x⁻¹ :=
  leftMove_lf (zero_mem_leftMoves_inv hx)

theorem invOption_right_left_mem_leftMoves_inv {x y a : IGame} (hx : 0 < x) (hy : 0 < y)
    (hyx : y ∈ x.rightMoves) (ha : a ∈ x⁻¹.leftMoves) :
    invOption x y a ∈ x⁻¹.leftMoves := by
  rw [inv_eq hx, leftMoves_ofSets] at *
  obtain ⟨i, rfl⟩ := ha
  use InvTy.left₁ (equivShrink _ ⟨_, hyx, hy⟩) i
  simp [InvTy.val, InvTy.val', invOption_eq hy]

theorem invOption_left_right_mem_leftMoves_inv {x y a : IGame} (hx : 0 < x) (hy : 0 < y)
    (hyx : y ∈ x.leftMoves) (ha : a ∈ x⁻¹.rightMoves) :
    invOption x y a ∈ x⁻¹.leftMoves := by
  rw [inv_eq hx, leftMoves_ofSets, rightMoves_ofSets] at *
  obtain ⟨i, rfl⟩ := ha
  use InvTy.left₂ (equivShrink _ ⟨_, hyx, hy⟩) i
  simp [InvTy.val, InvTy.val', invOption_eq hy]

theorem invOption_left_left_mem_rightMoves_inv {x y a : IGame} (hx : 0 < x) (hy : 0 < y)
    (hyx : y ∈ x.leftMoves) (ha : a ∈ x⁻¹.leftMoves) :
    invOption x y a ∈ x⁻¹.rightMoves := by
  rw [inv_eq hx, leftMoves_ofSets, rightMoves_ofSets] at *
  obtain ⟨i, rfl⟩ := ha
  use InvTy.right₁ (equivShrink _ ⟨_, hyx, hy⟩) i
  simp [InvTy.val, InvTy.val', invOption_eq hy]

theorem invOption_right_right_mem_rightMoves_inv {x y a : IGame} (hx : 0 < x) (hy : 0 < y)
    (hyx : y ∈ x.rightMoves) (ha : a ∈ x⁻¹.rightMoves) :
    invOption x y a ∈ x⁻¹.rightMoves := by
  rw [inv_eq hx, rightMoves_ofSets] at *
  obtain ⟨i, rfl⟩ := ha
  use InvTy.right₂ (equivShrink _ ⟨_, hyx, hy⟩) i
  simp [InvTy.val, InvTy.val', invOption_eq hy]

set_option linter.unnecessarySimpa false in
private theorem invRec' {x : IGame} (hx : 0 < x)
    {P : ∀ y ∈ x⁻¹.leftMoves, Prop} {Q : ∀ y ∈ x⁻¹.rightMoves, Prop}
    (zero : P 0 (zero_mem_leftMoves_inv hx))
    (left₁ : ∀ y (hy : 0 < y) (hyx : y ∈ x.rightMoves), ∀ a (ha : a ∈ x⁻¹.leftMoves), P a ha →
      P _ (invOption_eq hy ▸ invOption_right_left_mem_leftMoves_inv hx hy hyx ha))
    (left₂ : ∀ y (hy : 0 < y) (hyx : y ∈ x.leftMoves), ∀ a (ha : a ∈ x⁻¹.rightMoves), Q a ha →
      P _ (invOption_eq hy ▸ invOption_left_right_mem_leftMoves_inv hx hy hyx ha))
    (right₁ : ∀ y (hy : 0 < y) (hyx : y ∈ x.leftMoves), ∀ a (ha : a ∈ x⁻¹.leftMoves), P a ha →
      Q _ (invOption_eq hy ▸ invOption_left_left_mem_rightMoves_inv hx hy hyx ha))
    (right₂ : ∀ y (hy : 0 < y) (hyx : y ∈ x.rightMoves), ∀ a (ha : a ∈ x⁻¹.rightMoves), Q a ha →
      Q _ (invOption_eq hy ▸ invOption_right_right_mem_rightMoves_inv hx hy hyx ha)) :
    (∀ y (hy : y ∈ x⁻¹.leftMoves), P y hy) ∧ (∀ y (hy : y ∈ x⁻¹.rightMoves), Q y hy) := by
  suffices ∀ b : Bool, ∀ i, if hb : b then
      Q (InvTy.val x b i) (by subst hb; simp [inv_eq hx]) else
      P (InvTy.val x b i) (by rw [Bool.not_eq_true] at hb; subst hb; simp [inv_eq hx]) by
    constructor <;> intro y hy
    · rw [inv_eq hx, leftMoves_ofSets] at hy
      obtain ⟨i, rfl⟩ := hy
      have hi := this false i
      simp_all
    · rw [inv_eq hx, rightMoves_ofSets] at hy
      obtain ⟨i, rfl⟩ := hy
      have hi := this true i
      simp_all
  intro b i
  induction i
  · simpa
  all_goals simp only [Bool.false_eq_true]
  on_goal 1 => apply left₁
  on_goal 5 => apply left₂
  on_goal 9 => apply right₁
  on_goal 13 => apply right₂
  any_goals simpa [inv_eq hx, InvTy.val]
  all_goals first |
    exact ((equivShrink {y ∈ _ | 0 < y}).symm _).2.1 |
    exact ((equivShrink {y ∈ _ | 0 < y}).symm _).2.2

/-- An induction principle on left and right moves of `x⁻¹`. -/
theorem invRec {x : IGame} (hx : 0 < x)
    {P : ∀ y ∈ x⁻¹.leftMoves, Prop} {Q : ∀ y ∈ x⁻¹.rightMoves, Prop}
    (zero : P 0 (zero_mem_leftMoves_inv hx))
    (left₁ : ∀ y (hy : 0 < y) (hyx : y ∈ x.rightMoves), ∀ a (ha : a ∈ x⁻¹.leftMoves), P a ha →
      P _ (invOption_right_left_mem_leftMoves_inv hx hy hyx ha))
    (left₂ : ∀ y (hy : 0 < y) (hyx : y ∈ x.leftMoves), ∀ a (ha : a ∈ x⁻¹.rightMoves), Q a ha →
      P _ (invOption_left_right_mem_leftMoves_inv hx hy hyx ha))
    (right₁ : ∀ y (hy : 0 < y) (hyx : y ∈ x.leftMoves), ∀ a (ha : a ∈ x⁻¹.leftMoves), P a ha →
      Q _ (invOption_left_left_mem_rightMoves_inv hx hy hyx ha))
    (right₂ : ∀ y (hy : 0 < y) (hyx : y ∈ x.rightMoves), ∀ a (ha : a ∈ x⁻¹.rightMoves), Q a ha →
      Q _ (invOption_right_right_mem_rightMoves_inv hx hy hyx ha)) :
    (∀ y (hy : y ∈ x⁻¹.leftMoves), P y hy) ∧ (∀ y (hy : y ∈ x⁻¹.rightMoves), Q y hy) := by
  apply invRec' hx zero
  on_goal 1 => convert left₁ using 6 with _ ha
  on_goal 2 => convert left₂ using 6 with _ ha
  on_goal 3 => convert right₁ using 6 with _ ha
  on_goal 4 => convert right₂ using 6 with _ ha
  all_goals simp_rw [invOption_eq ha]

instance : RatCast IGame where
  ratCast q := q.num / q.den

theorem ratCast_def (q : ℚ) : (q : IGame) = q.num / q.den := rfl

@[simp] theorem ratCast_zero : ((0 : ℚ) : IGame) = 0 := by simp [ratCast_def]
@[simp] theorem ratCast_neg (q : ℚ) : ((-q : ℚ) : IGame) = -(q : IGame) := by simp [ratCast_def]

end IGame
end
