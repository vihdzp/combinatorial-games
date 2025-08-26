/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Functor
import CombinatorialGames.Mathlib.Neg
import CombinatorialGames.Mathlib.Small
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Countable.Small
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Small.Set

/-!
# Loopy games

The standard notion of a game studied in combinatorial game theory is that of a terminating game,
meaning that there exists no infinite sequence of moves. Loopy games relax this condition by
allowing "self-refential" games, with the basic examples being `on = {on | }`, `off = { | off}`, and
`dud = {dud | dud}`.

In the literature, loopy games are defined as rooted directed graphs up to isomorphism. However,
it's simpler to define `LGame` as the coinductive type for the single constructor:

```
  | ofSets (s t : Set LGame.{u}) [Small.{u} s] [Small.{u} t] : LGame.{u}
```

(The inductive type for this same constructor would be `IGame`.) This gives us a powerful
corecursion principle `LGame.corec`, which can be interpreted as saying "for any graph we can draw
on a type `α`, as long as the amount of branches per node is `u`-small, there's an `LGame`
isomorphic to it".

Although extensionality still holds, it's not always sufficient to prove two games equal. For
instance, if `x = !{x | x}` and `y = !{y | y}`, then `x = y`, but trying to use extensionality to
prove this just leads to a cyclic argument. Instead, we can use `LGame.eq_of_bisim`, which can
roughly be interpreted as saying "if two games have the same shape, they're equal". In this case,
the relation `r a b ↔ a = x ∧ b = y` is a bisimulation between both games, which proves their
equality.
-/

open Set

universe u v w

variable {α : Type v} {β : Type w}

/-! ### For Mathlib -/

-- This is problematic as an instance.
theorem small_succ' (α : Type u) [Small.{v} α] : Small.{v + 1} α :=
  small_lift.{u, v + 1, v} α

-- TODO: PR to Mathlib, together with the analogous `QPF.Fix.unique`.
theorem QPF.Cofix.unique {F : Type u → Type u} [QPF F] {α : Type u}
    (a : α → F α) (f g : α → QPF.Cofix F)
    (hf : QPF.Cofix.dest ∘ f = Functor.map f ∘ a)
    (hg : QPF.Cofix.dest ∘ g = Functor.map g ∘ a) : f = g := by
  ext x
  refine QPF.Cofix.bisim (fun a b ↦ ∃ x, f x = a ∧ g x = b) (fun a b hab ↦ ?_) _ _ ⟨x, rfl, rfl⟩
  obtain ⟨x, rfl, rfl⟩ := hab
  use (fun y ↦ ⟨⟨f y, g y⟩, y, rfl, rfl⟩) <$> a x
  simp_rw [funext_iff, Function.comp_apply] at hf hg
  rw [hf, hg, ← QPF.comp_map, ← QPF.comp_map]
  exact ⟨rfl, rfl⟩

noncomputable section

/-! ### Game moves -/

/-- The type of loopy games.

Most games studied within game theory are terminating, which means that the `IsOption` relation is
well-founded. A loopy game relaxes this constraint. Thus, `LGame` contains all normal `IGame`s, but
it also contains games such as `on = {on | }`, `off = { | off}`, and `dud = {dud | dud}`.

See the module docstring for guidance on how to make use of this type. -/
def LGame := QPF.Cofix GameFunctor

namespace LGame
export Player (left right)

instance : DecidableEq LGame := Classical.decEq _

/-- The set of moves of the game. -/
def moves (p : Player) (x : LGame.{u}) : Set LGame.{u} := x.dest.1 p

/-- The set of left moves of the game. -/
scoped notation:max x:max "ᴸ" => moves left x

/-- The set of right moves of the game. -/
scoped notation:max x:max "ᴿ" => moves right x

instance small_moves (p : Player) (x : LGame.{u}) : Small.{u} (x.moves p) := x.dest.2 p

/-- `IsOption x y` means that `x` is either a left or a right move for `y`. -/
def IsOption (x y : LGame) : Prop :=
  x ∈ ⋃ p, y.moves p

@[aesop simp]
lemma isOption_iff_mem_union {x y : LGame} : IsOption x y ↔ x ∈ yᴸ ∪ yᴿ := by
  simp [IsOption, Player.exists]

theorem IsOption.of_mem_moves {p} {x y : LGame} (h : x ∈ y.moves p) : IsOption x y :=
  ⟨_, ⟨p, rfl⟩, h⟩

instance (x : LGame.{u}) : Small.{u} {y // IsOption y x} :=
  inferInstanceAs (Small (⋃ p, x.moves p))

/-- A (proper) subposition is any game in the transitive closure of `IsOption`. -/
def Subposition : LGame → LGame → Prop :=
  Relation.TransGen IsOption

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_moves {p} {x y : LGame} (h : x ∈ y.moves p) : Subposition x y :=
  Relation.TransGen.single (.of_mem_moves h)

theorem Subposition.trans {x y z : LGame} (h₁ : Subposition x y) (h₂ : Subposition y z) :
    Subposition x z :=
  Relation.TransGen.trans h₁ h₂

instance (x : LGame.{u}) : Small.{u} {y // Subposition y x} :=
  small_transGen' _ x

/-- Two loopy games are equal when there exists a bisimulation between them.

A way to think about this is that `r` defines a pairing between nodes of the game trees, which then
shows that the trees are isomorphic. -/
theorem eq_of_bisim (r : LGame → LGame → Prop)
    (H : ∀ x y, r x y → ∀ p, (∃ s : Set (LGame × LGame),
      Prod.fst '' s = x.moves p ∧ Prod.snd '' s = y.moves p ∧ ∀ z ∈ s, r z.1 z.2))
    {x y : LGame.{u}} (hxy : r x y) : x = y := by
  refine QPF.Cofix.bisim r (fun x y hxy ↦ ?_) x y hxy
  choose s hs₁ hs₂ hs using H _ _ hxy
  simp_rw [Set.ext_iff, mem_image, Prod.exists, exists_and_right, exists_eq_right] at *
  refine ⟨⟨fun p ↦ range (inclusion (hs p)), ?_⟩, ?_, ?_⟩
  · have this (p) : Small.{u} (s p) := small_subset (s := moves p x ×ˢ moves p y) fun z hz ↦
      ⟨(hs₁ p z.1).1 ⟨_, hz⟩, (hs₂ p z.2).1 ⟨_, hz⟩⟩
    rintro (_ | _) <;> infer_instance
  all_goals
    ext p z
    revert z
    specialize hs₁ p
    specialize hs₂ p
    cases p <;> simpa [GameFunctor.map_def, ← range_comp]

/-- Two `LGame`s are equal when their move sets are.

This is not always sufficient to prove that two games are equal. For instance, if `x = !{x | x}` and
`y = !{y | y}`, then `x = y`, but trying to use extensionality to prove this just leads to a cyclic
argument. For these situations, you can use `eq_of_bisim` instead. -/
@[ext]
protected theorem ext {x y : LGame.{u}}
    (h : ∀ p, x.moves p = y.moves p) : x = y := by
  refine eq_of_bisim (fun i j ↦ ∀ p, i.moves p = j.moves p) (fun x y hxy ↦ ?_) h
  refine fun p ↦ ⟨(fun i ↦ (i, i)) '' x.moves p, ?_⟩
  simp_all [image_image, - Player.forall]

-- The default corecursion principle we get from `QPF` has inconvenient type universes, so we prove
-- a more general version.
section corec
variable {α : Type v}

/-- A node `α` is reachable from `init` when it can be formed by applying
`moves` finitely many times. -/
private def Reachable (mov : Player → α → Set α) (init : α) (a : α) : Prop :=
  Relation.ReflTransGen (fun x y ↦ x ∈ mov left y ∪ mov right y) a init

variable (p : Player) (mov : Player → α → Set α)
  [∀ a, Small.{u} (mov left a)] [∀ a, Small.{u} (mov right a)] (init : α)

attribute [local instance] small_succ' in
private instance : Small.{u + 1} (Subtype (Reachable mov init)) :=
  small_reflTransGen' ..

/-- Destructor for the subtype of reachable positions. -/
@[simp]
private def dest (x : Shrink (Subtype (Reachable mov init))) :
    GameFunctor (Shrink (Subtype (Reachable mov init))) :=
  have hx := ((equivShrink _).symm x).2
  ⟨fun
    | left => equivShrink _ '' range (inclusion fun _y hy ↦ .trans (.single (.inl hy)) hx)
    | right => equivShrink _ '' range (inclusion fun _y hy ↦ .trans (.single (.inr hy)) hx),
    fun | left | right => inferInstance⟩

private theorem unique (f g : Subtype (Reachable mov init) → LGame.{u})
    (hf : QPF.Cofix.dest ∘ f ∘ (equivShrink _).symm =
      Functor.map (f ∘ (equivShrink _).symm) ∘ dest mov init)
    (hg : QPF.Cofix.dest ∘ g ∘ (equivShrink _).symm =
      Functor.map (g ∘ (equivShrink _).symm) ∘ dest mov init) (x) : f x = g x :=
  congrFun ((equivShrink _).symm.surjective.right_cancellable.1 <|
    QPF.Cofix.unique (dest mov init) _ _ hf hg) x

/-- The corecursor on the subtype of reachable nodes. -/
private def corec' (x : Subtype (Reachable mov init)) :=
  QPF.Cofix.corec (dest _ _) (equivShrink _ x)

/-- The corecursor on `LGame`.

You can use this in order to define an arbitrary `LGame` by "drawing" its move graph on some other
type. As an example, `on = !{on | }` is defined as `corec (Player.cases ⊤ ⊥) ()`. -/
def corec : LGame.{u} :=
  corec' mov init ⟨_, .refl⟩

private theorem corec'_trans {x} (hx : Reachable mov init x)
  (y : Subtype (Reachable mov x)) :
    corec' _ x y = corec' _ init (inclusion (fun _z hz ↦ .trans hz hx) y) := by
  apply unique <;> ext _ p <;> cases p <;>
    simp [← range_comp, corec', QPF.Cofix.dest_corec, GameFunctor.map_def]

private theorem corec'_aux {a} (ha : a ∈ mov left init ∪ mov right init) {x : LGame} :
    (∃ ha : Reachable mov init a, corec' _ init ⟨a, ha⟩ = x) ↔
    corec mov a = x := by
  unfold corec
  constructor
  · rintro ⟨hx, rfl⟩
    simp [corec'_trans _ _ hx]
  · rintro rfl
    use .single ha
    simp [corec'_trans _ _ (.single ha)]

@[simp]
theorem moves_corec : (corec mov init).moves p = corec mov '' mov p init := by
  rw [moves, corec, corec', QPF.Cofix.dest_corec, GameFunctor.map_def]
  ext f
  cases p <;>
    simpa [← (equivShrink (Subtype (Reachable _ _))).exists_congr_right]
      using exists_congr fun a ↦ and_congr_right fun ha ↦ corec'_aux mov init (by aesop)

theorem moves_comp_corec :
    moves p ∘ corec mov = image (corec mov) ∘ mov p :=
  funext (moves_corec p mov)

theorem hom_unique_apply {mov : Player → α → Set α}
    [∀ a, Small.{u} (mov left a)] [∀ a, Small.{u} (mov right a)] (f g : α → LGame.{u})
    (hf : ∀ p, moves p ∘ f = image f ∘ mov p)
    (hg : ∀ p, moves p ∘ g = image g ∘ mov p) (x) : f x = g x := by
  change (f ∘ Subtype.val) (⟨x, .refl⟩ : Subtype (Reachable mov x)) =
    (g ∘ Subtype.val) (⟨x, .refl⟩ : Subtype (Reachable mov x))
  apply unique <;> ext z p
  · change _ ∈ (moves p ∘ f) _ ↔ _
    rw [hf]
    cases p <;>
      simpa [GameFunctor.map_def, image_image] using exists_congr fun a ↦ and_congr_right
        fun ha ↦ iff_and_self.2 fun _ ↦ .trans (.single (by aesop)) ((equivShrink _).symm z).2
  · change _ ∈ (moves p ∘ g) _ ↔ _
    rw [hg]
    cases p <;>
      simpa [GameFunctor.map_def, image_image] using exists_congr fun a ↦ and_congr_right
        fun ha ↦ iff_and_self.2 fun _ ↦ .trans (.single (by aesop)) ((equivShrink _).symm z).2

theorem hom_unique {mov : Player → α → Set α}
    [∀ a, Small.{u} (mov left a)] [∀ a, Small.{u} (mov right a)] (f g : α → LGame.{u})
    (hf : ∀ p, moves p ∘ f = image f ∘ mov p)
    (hg : ∀ p, moves p ∘ g = image g ∘ mov p) : f = g :=
  funext (hom_unique_apply _ _ hf hg)

-- We make no use of `LGame`'s definition from a `QPF` after this point.
attribute [irreducible] LGame

end corec

theorem corec_comp_hom
    {movα : Player → α → Set α} {movβ : Player → β → Set β}
    [∀ a, Small.{u} (movα left a)] [∀ a, Small.{u} (movα right a)]
    [∀ b, Small.{u} (movβ left b)] [∀ b, Small.{u} (movβ right b)] (f : α → β)
    (hf : ∀ p, movβ p ∘ f = Set.image f ∘ movα p) :
    corec movβ ∘ f = corec movα := by
  refine hom_unique _ _ ?_ (fun _ ↦ moves_comp_corec ..)
  intro p
  rw [Set.image_comp_eq, Function.comp_assoc, ← hf,
    ← Function.comp_assoc, moves_comp_corec, Function.comp_assoc]

theorem corec_comp_hom_apply
    {movα : Player → α → Set α} {movβ : Player → β → Set β}
    [∀ a, Small.{u} (movα left a)] [∀ a, Small.{u} (movα right a)]
    [∀ b, Small.{u} (movβ left b)] [∀ b, Small.{u} (movβ right b)] (f : α → β)
    (hf : ∀ p, movβ p ∘ f = Set.image f ∘ movα p) (x : α) :
    corec movβ (f x) = corec movα x :=
  congrFun (corec_comp_hom f hf) x

@[simp]
theorem corec_moves : corec moves = id :=
  hom_unique _ _ (moves_comp_corec · moves) (fun _ ↦ Set.image_id_eq ▸ rfl)

theorem corec_moves_apply (x : LGame) : corec moves x = x := by simp

/-- Construct an `LGame` from its left and right sets.

It's not possible to create a non-well-founded game through this constructor alone. For that,
see `LGame.corec`. -/
instance : OfSets LGame.{u} fun _ ↦ True where
  ofSets lr _ :=
    have this (p) : ∀ (a : Option LGame),
        Small.{u} ((a.elim (some '' lr p) (some '' moves p ·)) : Set _) := by
      cases p <;> simpa [Option.forall] using ⟨inferInstance, inferInstance⟩
    corec (fun p ↦ (·.elim (some '' lr p) (some '' moves p ·))) none

@[simp]
theorem moves_ofSets (p : Player) (lr : Player → Set LGame.{u})
    [Small.{u} (lr left)] [Small.{u} (lr right)] : !{lr}.moves p = lr p := by
  dsimp [ofSets]
  rw [moves_corec, Option.elim_none, Set.image_image]
  conv_rhs => rw [← Set.image_id (lr p), ← corec_moves]
  generalize_proofs
  exact congrFun (congrArg _ (corec_comp_hom some (fun _ ↦ rfl))) _

theorem leftMoves_ofSets (l r : Set LGame) [Small.{u} l] [Small.{u} r] :
    !{l | r}ᴸ = l :=
  moves_ofSets ..

theorem rightMoves_ofSets (l r : Set LGame) [Small.{u} l] [Small.{u} r] :
    !{l | r}ᴿ = r :=
  moves_ofSets ..

/-! ### Basic games -/

/-- The game `0 = !{∅ | ∅}`. -/
instance : Zero LGame := ⟨!{fun _ ↦ ∅}⟩

theorem zero_def : (0 : LGame) = !{fun _ ↦ ∅} := rfl

@[simp] theorem leftMoves_zero : 0ᴸ = ∅ := leftMoves_ofSets ..
@[simp] theorem rightMoves_zero : 0ᴿ = ∅ := rightMoves_ofSets ..

-- TODO: remove the former?
@[simp] theorem moves_zero (p : Player) : moves p 0 = ∅ := moves_ofSets ..

-- TODO: remove the former?
@[simp] theorem moves_zero (p : Player) : moves p 0 = ∅ := moves_ofSets ..

instance : Inhabited LGame := ⟨0⟩

/-- The game `1 = !{{0} | ∅}`. -/
instance : One LGame := ⟨!{{0} | ∅}⟩

theorem one_def : (1 : LGame) = !{{0} | ∅} := rfl

@[simp] theorem leftMoves_one : 1ᴸ = {0} := leftMoves_ofSets ..
@[simp] theorem rightMoves_one : 1ᴿ = ∅ := rightMoves_ofSets ..

/-- The game `on = !{{on} | ∅}`. -/
def on : LGame := corec (Player.cases ⊤ ⊥) ()

@[simp] theorem leftMoves_on : onᴸ = {on} := by simp [on]
@[simp] theorem rightMoves_on : onᴿ = ∅ := by simp [on]
theorem on_eq : on = !{{on} | ∅} := by ext p; cases p <;> simp

theorem eq_on {x : LGame} : x = on ↔ xᴸ = {x} ∧ xᴿ = ∅ := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · simp_all
  · refine eq_of_bisim (fun a b ↦ a = x ∧ b = on) ?_ ⟨rfl, rfl⟩
    rintro a b ⟨rfl, rfl⟩
    refine Player.rec ⟨{(a, on)}, ?_⟩ ⟨∅, ?_⟩ <;> simp_all

/-- The game `off = !{∅ | {off}}`. -/
def off : LGame := corec (Player.cases ⊥ ⊤) ()

@[simp] theorem leftMoves_off : offᴸ = ∅ := by simp [off]
@[simp] theorem rightMoves_off : offᴿ = {off} := by simp [off]
theorem off_eq : off = !{∅ | {off}} := by ext p; cases p <;> simp

theorem eq_off {x : LGame} : x = off ↔ xᴸ = ∅ ∧ xᴿ = {x} := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · simp_all
  · refine eq_of_bisim (fun a b ↦ a = x ∧ b = off) ?_ ⟨rfl, rfl⟩
    rintro a b ⟨rfl, rfl⟩
    refine Player.rec ⟨∅, ?_⟩ ⟨{(a, off)}, ?_⟩ <;> simp_all

/-- The game `dud = !{{dud} | {dud}}`. -/
def dud : LGame := corec (Player.cases ⊤ ⊤) ()

@[simp] theorem leftMoves_dud : dudᴸ = {dud} := by simp [dud]
@[simp] theorem rightMoves_dud : dudᴿ = {dud} := by simp [dud]
theorem dud_eq : dud = !{{dud} | {dud}} := by ext p; cases p <;> simp

theorem eq_dud {x : LGame} : x = dud ↔ xᴸ = {x} ∧ xᴿ = {x} := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · simp_all
  · refine eq_of_bisim (fun a b ↦ a = x ∧ b = dud) ?_ ⟨rfl, rfl⟩
    rintro a b ⟨rfl, rfl⟩
    refine fun p ↦ ⟨{(a, dud)}, ?_⟩; cases p <;> simp_all

/-- The game `tis = !{{tisn} | ∅}`, where `tisn = !{∅ | {tis}}`. -/
def tis : LGame := corec (Player.cases (Bool.rec ∅ {false}) (Bool.rec {true} ∅)) true
/-- The game `tisn = !{∅ | {tis}}`, where `tis = !{{tisn} | ∅}`. -/
def tisn : LGame := corec (Player.cases (Bool.rec ∅ {false}) (Bool.rec {true} ∅)) false

@[simp] theorem leftMoves_tis : tisᴸ = {tisn} := by simp [tis, tisn]
@[simp] theorem rightMoves_tis : tisᴿ = ∅ := by simp [tis]
theorem tis_eq : tis = !{{tisn} | ∅} := by ext p; cases p <;> simp

@[simp] theorem leftMoves_tisn : tisnᴸ = ∅ := by simp [tisn]
@[simp] theorem rightMoves_tisn : tisnᴿ = {tis} := by simp [tis, tisn]
theorem tisn_eq : tisn = !{∅ | {tis}} := by ext p; cases p <;> simp

/-! ### Negation -/

/-- The negative of a game is defined by `-!{s | t} = !{-t | -s}`. -/
instance : Neg LGame where
  neg := corec fun p ↦ moves (-p)

@[simp] theorem corec_moves_neg : corec (fun p ↦ moves (-p)) = (- ·) := rfl
theorem corec_moves_neg_apply (x : LGame) : corec (fun p ↦ moves (-p)) x = -x := rfl

theorem neg_corec (mov : Player → α → Set α)
    [∀ x, Small.{u} (mov left x)] [∀ x, Small.{u} (mov right x)] :
    -corec mov = corec fun p ↦ mov (-p) :=
  corec_comp_hom _ (fun _ ↦ moves_comp_corec ..)

theorem neg_corec_apply (mov : Player → α → Set α)
    [∀ x, Small.{u} (mov left x)] [∀ x, Small.{u} (mov right x)] (init : α) :
    -corec mov init = corec (fun p ↦ mov (-p)) init :=
  congrFun (neg_corec ..) _

instance : InvolutiveNeg LGame where
  neg_neg _ := (neg_corec_apply ..).trans (corec_moves_apply ..)

@[simp]
theorem moves_neg (p : Player) (x : LGame) : (-x).moves p = -x.moves (-p) := by
  rw [← Set.image_neg_eq_neg]
  exact moves_corec ..

@[simp]
theorem neg_ofSets (s t : Set LGame.{u}) [Small.{u} s] [Small.{u} t] : -!{s | t} = !{-t | -s} := by
  ext p; cases p <;> simp

theorem neg_ofSets' (st : Player → Set LGame) [Small (st left)] [Small (st right)] :
    -!{st} = !{fun p ↦ -st (-p)} := by
  rw [ofSets_eq_ofSets_cases, ofSets_eq_ofSets_cases fun _ ↦ -_, neg_ofSets]
  rfl

@[simp]
theorem neg_ofSets_const (s : Set LGame) [Small s] :
    -!{fun _ ↦ s} = !{fun _ ↦ -s} := by
  simp [neg_ofSets']

instance : NegZeroClass LGame where
  neg_zero := by simp [zero_def]

@[simp] theorem neg_on : -on = off := neg_corec_apply ..
@[simp] theorem neg_off : -off = on := neg_corec_apply ..
@[simp] theorem neg_dud : -dud = dud := neg_corec_apply ..

@[simp]
theorem neg_tis : -tis = tisn := by
  refine eq_of_bisim (fun a b ↦ a = -tis ∧ b = tisn ∨ a = -tisn ∧ b = tis) ?_ (.inl ⟨rfl, rfl⟩)
  rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (_ | _)
  on_goal 1 => use ∅
  on_goal 2 => use {(-tisn, tis)}
  on_goal 3 => use {(-tis, tisn)}
  on_goal 4 => use ∅
  all_goals simp

@[simp]
theorem neg_tisn : -tisn = tis := by
  rw [← neg_tis, neg_neg]

/-! ### Addition -/

/-- The sum of `x = !{s₁ | t₁}` and `y = !{s₂ | t₂}` is `!{s₁ + y, x + s₂ | t₁ + y, x + t₂}`. -/
instance : Add LGame where
  add x y := corec
    (fun p x ↦ (fun y ↦ (y, x.2)) '' moves p x.1 ∪ (fun y ↦ (x.1, y)) '' moves p x.2)
    (x, y)

theorem corec_add_corec
    {movα : Player → α → Set α} {movβ : Player → β → Set β}
    [∀ x, Small.{u} (movα left x)] [∀ x, Small.{u} (movα right x)]
    [∀ x, Small.{u} (movβ left x)] [∀ x, Small.{u} (movβ right x)] (initα : α) (initβ : β) :
    corec movα initα + corec movβ initβ =
    corec
      (fun p x ↦ (fun y ↦ (y, x.2)) '' movα p x.1 ∪ (fun y ↦ (x.1, y)) '' movβ p x.2)
      (initα, initβ) := by
  refine corec_comp_hom_apply (Prod.map (corec movα) (corec movβ)) ?_ (initα, initβ)
  refine fun p ↦ funext fun ⟨a, b⟩ ↦ ?_
  simp [Set.image_image, Set.image_union, moves_corec]

@[simp]
theorem moves_add (p : Player) (x y : LGame) :
    (x + y).moves p = (· + y) '' x.moves p ∪ (x + ·) '' y.moves p := by
  apply (moves_corec ..).trans
  aesop (erase Player)

@[simp]
theorem add_eq_zero_iff {x y : LGame} : x + y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor <;> simp_all [LGame.ext_iff]

private theorem add_zero' (x : LGame) : x + 0 = x := by
  refine eq_of_bisim (fun x y ↦ x = y + 0) ?_ rfl
  rintro a b rfl
  refine fun p ↦ ⟨(fun x ↦ (x + 0, x)) '' b.moves p, ?_⟩
  cases p <;> simp [image_image]

private theorem add_comm' (x y : LGame) : x + y = y + x := by
  apply eq_of_bisim (fun x y ↦ ∃ a b, x = a + b ∧ y = b + a) ?_ ⟨x, y, rfl, rfl⟩
  rintro _ _ ⟨a, b, rfl, rfl⟩
  refine fun p ↦
    ⟨(fun x ↦ (x + b, b + x)) '' a.moves p ∪ (fun x ↦ (a + x, x + a)) '' b.moves p, ?_, ?_⟩
  all_goals aesop (erase Player)

private theorem add_assoc' (x y z : LGame) : x + y + z = x + (y + z) := by
  apply eq_of_bisim (fun x y ↦ ∃ a b c, x = a + b + c ∧ y = a + (b + c)) ?_ ⟨x, y, z, rfl, rfl⟩
  rintro _ _ ⟨a, b, c, rfl, rfl⟩
  refine fun p ↦
    ⟨(fun x ↦ (x + b + c, x + (b + c))) '' a.moves p ∪
    (fun x ↦ (a + x + c, a + (x + c))) '' b.moves p ∪
    (fun x ↦ (a + b + x, a + (b + x))) '' c.moves p, ?_, ?_⟩
  all_goals aesop (add simp [image_union]) (erase Player)

instance : AddCommMonoid LGame where
  add_zero := add_zero'
  zero_add _ := add_comm' .. ▸ add_zero' _
  add_comm := add_comm'
  add_assoc := add_assoc'
  nsmul := nsmulRec

@[simp]
theorem on_add_off : on + off = dud := by
  rw [eq_dud]
  simp

@[simp]
theorem off_add_on : off + on = dud := by
  rw [add_comm, on_add_off]

@[simp]
theorem add_dud (x : LGame) : x + dud = dud := by
  refine eq_of_bisim (fun x y ↦ (∃ b, x = b + dud) ∧ y = dud) ?_ ⟨⟨x, rfl⟩, rfl⟩
  rintro _ _ ⟨⟨x, rfl⟩, rfl⟩
  refine fun p ↦
    ⟨insert (x + dud, dud) ((fun y ↦ (y + dud, dud)) '' x.moves p), ?_, ?_⟩
  all_goals aesop

@[simp]
theorem dud_add (x : LGame) : dud + x = dud := by
  rw [add_comm, add_dud]

theorem moves_sum (p : Player) (m : Multiset LGame) : m.sum.moves p =
    ⋃ y ∈ m, (· + (m.erase y).sum) '' y.moves p := by
  induction m using Multiset.induction with
  | empty => cases p <;> simp
  | cons a m IH =>
    simp_rw [Multiset.mem_cons, Multiset.sum_cons, iUnion_iUnion_eq_or_left,
      Multiset.erase_cons_head, moves_add, IH, image_iUnion, image_image]
    congr! 5 with _ h
    rw [Multiset.erase_cons_tail_of_mem h]
    simp [← add_assoc, add_comm]

/-- The subtraction of `x` and `y` is defined as `x + (-y)`. -/
instance : SubNegMonoid LGame where
  zsmul := zsmulRec

theorem corec_sub_corec
    {movα : Player → α → Set α} {movβ : Player → β → Set β}
    [∀ x, Small.{u} (movα left x)] [∀ x, Small.{u} (movα right x)]
    [∀ x, Small.{u} (movβ left x)] [∀ x, Small.{u} (movβ right x)] (initα : α) (initβ : β) :
    corec movα initα - corec movβ initβ =
    corec
      (fun p x ↦ (fun y ↦ (y, x.2)) '' movα p x.1 ∪ (fun y ↦ (x.1, y)) '' movβ (-p) x.2)
      (initα, initβ) := by
  rw [sub_eq_add_neg, neg_corec_apply, corec_add_corec]

@[simp]
theorem moves_sub (p : Player) (x y : LGame) :
    (x - y).moves p = (· - y) '' x.moves p ∪ (x + ·) '' (-y.moves (-p)) := by
  simp [sub_eq_add_neg]

private theorem neg_add' (x y : LGame) : -(x + y) = -x + -y := by
  refine eq_of_bisim (fun x y ↦ ∃ a b, x = -(a + b) ∧ y = -a + -b) ?_ ⟨x, y, rfl, rfl⟩
  rintro _ _ ⟨a, b, rfl, rfl⟩
  refine fun p ↦
    ⟨(fun x ↦ (-(x + b), -x + -b)) '' a.moves (-p) ∪
    (fun x ↦ (-(a + x), -a + -x)) '' b.moves (-p), ?_, ?_⟩
  all_goals aesop (add simp [image_union]) (erase Player)

instance : SubtractionCommMonoid LGame where
  neg_neg := neg_neg
  neg_add_rev x y := by rw [neg_add', add_comm]
  neg_eq_of_add := by simp
  add_comm := add_comm

@[simp]
theorem on_sub_on : on - on = dud := by
  simp [sub_eq_add_neg]

@[simp]
theorem off_sub_off : off - off = dud := by
  simp [sub_eq_add_neg]

@[simp]
theorem sub_dud (x : LGame) : x - dud = dud := by
  simp [sub_eq_add_neg]

/-! ### Multiplication -/

/-- Given two game graphs drawn on types `α` and `β`, the graph for the product can be drawn on the
type `Multiset (Player × α × β)`. Each term corresponds to a sum `Σ ±aᵢ * bᵢ`, where `aᵢ` and `bᵢ`
are terms of `α` and `β` respectively, and the attached player represents each term's sign. -/
abbrev MulTy (α β : Type*) :=
  Multiset (Player × α × β)

namespace MulTy

/-- Inverts the sign of all entries. -/
instance : InvolutiveNeg (MulTy α β) where
  neg x := x.map (fun y ↦ (-y.1, y.2))
  neg_neg x := by simp

theorem neg_def (x : MulTy α β) : -x = Multiset.map (fun y ↦ (-y.1, y.2)) x :=
  rfl

@[simp]
theorem mem_neg {x : Player × α × β} {y : MulTy α β} : x ∈ -y ↔ (-x.1, x.2) ∈ y := by
  convert Multiset.mem_map_of_injective (a := (-x.1, x.2)) _ <;>
    simp [Function.Injective]

@[simp]
theorem neg_zero : -(0 : MulTy α β) = 0 :=
  rfl

@[simp]
theorem neg_singleton (a : Player × α × β) : -({a} : MulTy α β) = {(-a.1, a.2)} :=
  rfl

@[simp]
theorem neg_cons (a : Player × α × β) (x : MulTy α β) : -(a ::ₘ x) = (-a.1, a.2) ::ₘ -x :=
  Multiset.map_cons ..

@[simp]
theorem neg_add (x y : MulTy α β) : -(x + y) = -x + -y :=
  Multiset.map_add ..

@[simp]
theorem neg_erase [DecidableEq α] [DecidableEq β] (x : MulTy α β) (a : Player × α × β) :
    -x.erase a = (-x).erase (-a.1, a.2) :=
  Multiset.map_erase _ (fun _ ↦ by simp) ..

/-- Swaps the entries in all pairs. -/
def swap (x : MulTy α β) : MulTy β α :=
  x.map (fun a ↦ (a.1, a.2.swap))

theorem swap_def (x : MulTy α β) : x.swap = x.map (fun a ↦ (a.1, a.2.swap)) :=
  rfl

@[simp]
theorem mem_swap {x : Player × β × α} {y : MulTy α β} : x ∈ y.swap ↔ (x.1, x.2.swap) ∈ y := by
  apply Multiset.mem_map_of_injective (a := (x.1, x.2.swap))
  simp [Function.Injective]

@[simp]
theorem swap_zero : swap (0 : MulTy α β) = 0 :=
  rfl

@[simp]
theorem swap_singleton (a : Player × α × β) : swap {a} = {(a.1, a.2.swap)} :=
  rfl

@[simp]
theorem swap_cons (a : Player × α × β) (x : MulTy α β) :
    swap (a ::ₘ x) = (a.1, a.2.swap) ::ₘ x.swap :=
  Multiset.map_cons ..

@[simp]
theorem swap_add (x y : MulTy α β) : swap (x + y) = x.swap + y.swap :=
  Multiset.map_add ..

@[simp]
theorem swap_erase [DecidableEq α] [DecidableEq β] (x : MulTy α β) (a : Player × α × β) :
    swap (x.erase a) = x.swap.erase (a.1, a.2.swap) :=
  Multiset.map_erase _ (fun _ ↦ by simp) ..

/-- The general form of an option of `x * y` is `a * y + x * b - a * b`.

If the player argument is left, all signs are flipped. -/
def mulOption (p : Player) (x : α × β) (y : α × β) : MulTy α β :=
  {(p, y.1, x.2), (p, x.1, y.2), (-p, y.1, y.2)}

@[simp]
theorem neg_mulOption (p : Player) (x : α × β) (y : α × β) :
    -mulOption p x y = mulOption (-p) x y := by
  simp [mulOption]

@[simp]
theorem swap_mulOption (p : Player) (x : α × β) (y : α × β) :
    swap (mulOption p x y) = mulOption p x.swap y.swap := by
  simpa [mulOption, ← Multiset.singleton_add] using add_left_comm ..

theorem mulOption_eq_add (p : Player) (x : α × β) (y : α × β) :
    mulOption p x y = {(p, y.1, x.2)} + {(p, x.1, y.2)} + {(-p, y.1, y.2)} :=
  rfl

variable (p : Player) (movα : Player → α → Set α) (movβ : Player → β → Set β)

/-- The set of pairs `α × β` used in `movesSingle`. -/
def movesSet (x : Player × α × β) : Set (α × β) :=
  (p * x.1).rec
    (movα left x.2.1 ×ˢ movβ right x.2.2 ∪ movα right x.2.1 ×ˢ movβ left x.2.2)
    (movα left x.2.1 ×ˢ movβ left x.2.2 ∪ movα right x.2.1 ×ˢ movβ right x.2.2)

theorem movesSet_neg (x : Player × α × β) :
    movesSet p movα movβ (-x.1, x.2) = movesSet (-p) movα movβ x := by
  cases p
  · rfl
  · obtain ⟨_ | _, _, _⟩ := x <;> rfl

theorem movesSet_neg' (x : Player × LGame × LGame) :
    movesSet p moves moves (x.1, -x.2.1, x.2.2) =
    (fun y ↦ (-y.1, y.2)) '' movesSet (-p) moves moves x := by
  obtain ⟨_ | _, _, _⟩ := x <;> aesop (add simp [movesSet])

theorem movesSet_swap (x : Player × α × β) :
    movesSet p movβ movα (x.1, x.2.swap) = Prod.swap '' movesSet p movα movβ x := by
  obtain ⟨_ | _, _, _⟩ := x <;> cases p <;> simp [movesSet, image_union, union_comm]

/-- The left or right moves of `±x * y` are left or right moves of `x * y` if the sign is positive,
or the negatives of right or left moves of `x * y` if the sign is negative. -/
def movesSingle (x : Player × α × β) : Set (MulTy α β) :=
  mulOption x.1 x.2 '' movesSet p movα movβ x

theorem movesSingle_neg (x : Player × α × β) :
    movesSingle p movα movβ (-x.1, x.2) = -movesSingle (-p) movα movβ x := by
  rw [movesSingle, movesSingle, movesSet_neg]
  simp [image_image, ← image_neg_eq_neg]

theorem movesSingle_neg' (x : Player × LGame × LGame) :
    movesSingle p moves moves (x.1, -x.2.1, x.2.2) =
    (Multiset.map fun y ↦ (y.1, -y.2.1, y.2.2)) '' movesSingle (-p) moves moves x := by
  rw [movesSingle, movesSingle, movesSet_neg']
  simp [image_image, mulOption]

theorem movesSingle_swap (x : Player × α × β) :
    movesSingle p movβ movα (x.1, x.2.swap) = swap '' movesSingle p movα movβ x := by
  simp [movesSingle, movesSet_swap, image_image]

variable [Hα : DecidableEq α] [Hβ : DecidableEq β]

/-- The set of left or right moves of `Σ ±xᵢ * yᵢ` are `zᵢ + Σ ±xⱼ * yⱼ` for all `i`, where `cᵢ` is
a left or right move of `±xᵢ * yᵢ`, and the summation is taken over indices `j ≠ i`. -/
protected def moves (x : MulTy α β) : Set (MulTy α β) :=
  ⋃ y ∈ x, (x.erase y + ·) '' movesSingle p movα movβ y

-- TODO: upstream?
theorem _root_.Multiset.iUnion_map {α β γ} (m : Multiset α) (f : α → β) (g : β → Set γ) :
    ⋃ x ∈ m.map f, g x = ⋃ x ∈ m, g (f x) := by
  simp

theorem moves_neg (x : MulTy α β) :
    (-x).moves p movα movβ = -x.moves (-p) movα movβ := by
  rw [MulTy.moves, MulTy.moves, neg_def, Multiset.iUnion_map]
  simp [← image_neg_eq_neg, image_iUnion, image_image, movesSingle_neg, ← neg_def]

theorem moves_neg' (x : MulTy LGame LGame) :
    MulTy.moves p moves moves (Multiset.map (fun y ↦ (y.1, -y.2.1, y.2.2)) x) =
    (Multiset.map fun y ↦ (y.1, -y.2.1, y.2.2)) '' x.moves (-p) moves moves := by
  rw [MulTy.moves, MulTy.moves, Multiset.iUnion_map]
  simp only [movesSingle_neg', image_image, image_iUnion, Multiset.map_add]
  congr! with y hy
  exact (x.map_erase_of_mem _ hy).symm

theorem moves_swap (x : MulTy α β) :
    x.swap.moves p movβ movα = swap '' x.moves p movα movβ := by
  rw [MulTy.moves, swap_def, Multiset.iUnion_map]
  simp [MulTy.moves, image_iUnion, image_image, movesSingle_swap]
  rfl

variable {α₁ β₁ α₂ β₂ : Type*}
  {movα₁ : Player → α₁ → Set α₁} {movβ₁ : Player → β₁ → Set β₁}
  {movα₂ : Player → α₂ → Set α₂} {movβ₂ : Player → β₂ → Set β₂}
  (f : α₁ → α₂) (g : β₁ → β₂)

/-- Map `MulTy α₁ β₁` to `MulTy α₂ β₂` using `f : α₁ → α₂` and `g : β₁ → β₂` in the natural way. -/
def map : MulTy α₁ β₁ → MulTy α₂ β₂ :=
  Multiset.map (Prod.map id (Prod.map f g))

@[simp]
theorem map_add (x y) : map f g (x + y) = map f g x + map f g y :=
  Multiset.map_add ..

theorem map_erase [DecidableEq α₁] [DecidableEq β₁] [DecidableEq α₂] [DecidableEq β₂]
    {x : MulTy α₁ β₁} {y} (hy : y ∈ x) :
    map f g (x.erase y) = (map f g x).erase (y.1, f y.2.1, g y.2.2) :=
  Multiset.map_erase_of_mem _ _ hy

@[simp]
theorem map_mulOption (b x y) :
    map f g (mulOption b x y) = mulOption b (Prod.map f g x) (Prod.map f g y) := by
  simp [mulOption, map, Prod.map]

variable {p f g}

set_option maxHeartbeats 400000 in
theorem movesSingle_comp_prodMap
    (hf : ∀ p, movα₂ p ∘ f = Set.image f ∘ movα₁ p)
    (hg : ∀ p, movβ₂ p ∘ g = Set.image g ∘ movβ₁ p) :
    movesSingle p movα₂ movβ₂ ∘ Prod.map id (Prod.map f g) =
    image (map f g) ∘ movesSingle p movα₁ movβ₁ := by
  simp_rw [funext_iff, Function.comp_apply, movesSingle, movesSet] at *
  rintro ⟨p', x⟩
  ext
  simp_rw [Prod.map_apply, id_eq, Prod.map_fst, Prod.map_snd, mem_image, Prod.exists, hf, hg]
  clear hf hg
  cases p <;> cases p' <;> aesop

variable [Hα₁ : DecidableEq α₁] [Hβ₁ : DecidableEq β₁] [Hα₂ : DecidableEq α₂] [Hβ₂ : DecidableEq β₂]

theorem moves_comp_map
    (hf : ∀ p, movα₂ p ∘ f = Set.image f ∘ movα₁ p)
    (hg : ∀ p, movβ₂ p ∘ g = Set.image g ∘ movβ₁ p) :
    MulTy.moves p movα₂ movβ₂ ∘ map f g = image (map f g) ∘ MulTy.moves p movα₁ movβ₁ := by
  ext1 x
  simp_rw [Function.comp_apply, MulTy.moves, map, Multiset.iUnion_map, image_iUnion]
  congr! with y hy
  simp_rw [← Multiset.map_erase_of_mem _ _ hy, ← Function.comp_apply (g := Prod.map id _),
    movesSingle_comp_prodMap hf hg]
  aesop

variable (p)
    [∀ x, Small.{u} (movα left x)] [∀ x, Small.{u} (movα right x)]
    [∀ x, Small.{u} (movβ left x)] [∀ x, Small.{u} (movβ right x)]

private instance (x : Player × α × β) :
    Small.{u} (movesSet p movα movβ x) := by
  obtain ⟨(_ | _), _⟩ := x <;> cases p <;> exact small_union ..

instance (x : Player × α × β) :
    Small.{u} (movesSingle p movα movβ x) :=
  small_image ..

instance (x : MulTy α β) :
    Small.{u} (x.moves p movα movβ) := by
  simp_rw [MulTy.moves, ← Multiset.mem_toFinset]
  exact small_biUnion.{u} (Multiset.toFinset x).toSet _

/-- The game `±xᵢ * yᵢ`. -/
abbrev toLGame (x : Player × α × β) : LGame :=
  corec (MulTy.moves · movα movβ) {x}

theorem moves_toLGame (x : Player × α × β) :
    (toLGame movα movβ x).moves p =
    corec (MulTy.moves · movα movβ) '' movesSingle p movα movβ x := by
  apply (moves_corec ..).trans
  simp [MulTy.moves]

@[simp]
theorem corec_zero : corec (MulTy.moves · movα movβ) 0 = 0 := by
  ext p; cases p <;> simp [MulTy.moves]

theorem corec_neg (init : MulTy α β) :
    corec (MulTy.moves · movα movβ) (-init) = -corec (MulTy.moves · movα movβ) init := by
  rw [neg_corec_apply]
  apply corec_comp_hom_apply
  intro p
  ext
  simp [moves_neg]

theorem corec_add (init₁ init₂ : MulTy α β) :
    corec (MulTy.moves · movα movβ) (init₁ + init₂) =
    corec (MulTy.moves · movα movβ) init₁ + corec (MulTy.moves · movα movβ) init₂ := by
  refine eq_of_bisim (fun a b ↦ ∃ x y,
    a = corec (MulTy.moves · movα movβ) (x + y) ∧
    b = corec (MulTy.moves · movα movβ) x + corec (MulTy.moves · movα movβ) y) ?_
    ⟨_, _, rfl, rfl⟩
  rintro _ _ ⟨x, y, rfl, rfl⟩
  let f (s : _ → _) := (⋃ z ∈ x, (fun w ↦
      (corec (MulTy.moves · movα movβ) (mulOption z.1 z.2 w + x.erase z + y),
      corec (MulTy.moves · movα movβ) (mulOption z.1 z.2 w + x.erase z) +
      corec (MulTy.moves · movα movβ) y)) '' s z) ∪
    (⋃ z ∈ y, (fun w ↦
      (corec (MulTy.moves · movα movβ) (mulOption z.1 z.2 w + x + y.erase z),
      corec (MulTy.moves · movα movβ) x +
      corec (MulTy.moves · movα movβ) (mulOption z.1 z.2 w + y.erase z))) '' s z)
  intro p
  use f (movesSet p movα movβ)
  simp only [f, image_union, image_iUnion, image_image,
    Multiset.mem_add, iUnion_or, iUnion_union_distrib,
    moves_corec, MulTy.moves, movesSingle]
  refine ⟨?_, ?_, ?_⟩
  · congr! 6 with a ha b hb a ha b hb
    · rw [Multiset.erase_add_left_pos _ ha]
      simp [add_comm, add_assoc]
    · rw [Multiset.erase_add_right_pos _ ha]
      simp [add_comm, ← add_assoc]
  · simp [image_iUnion, image_image, MulTy.moves, movesSingle, add_comm]
  · rintro z (⟨_, ⟨a, rfl⟩, ⟨c, ⟨ha, rfl⟩, ⟨b, hb, rfl⟩⟩⟩ | ⟨_, ⟨a, rfl⟩, ⟨c, ⟨ha, rfl⟩, ⟨b, hb, rfl⟩⟩⟩)
    · use mulOption a.1 a.2 b + x.erase a, y
    · use mulOption a.1 a.2 b + y.erase a, x
      simp [add_comm, ← add_assoc]

theorem corec_mulOption (p : Player) (x y : α × β) :
    corec (MulTy.moves · movα movβ) (mulOption p x y) =
    toLGame movα movβ (p, y.1, x.2) +
    toLGame movα movβ (p, x.1, y.2) -
    toLGame movα movβ (p, y.1, y.2) := by
  simp_rw [mulOption_eq_add, corec_add]
  congr
  rw [← corec_neg, neg_singleton]

theorem _root_.LGame.corec_mulTy (x : MulTy α β) :
    corec (MulTy.moves · movα movβ) x =
    (Multiset.map (toLGame movα movβ) x).sum := by
  induction x using Multiset.induction with
  | empty => simp
  | cons a x IH => simp [← Multiset.singleton_add, corec_add, IH]

theorem corec_swap (x : MulTy α β) :
    corec (MulTy.moves · movβ movα) x.swap = corec (MulTy.moves · movα movβ) x := by
  apply corec_comp_hom_apply
  intro p
  ext
  simp [moves_swap]

/-- The product of `x = !{s₁ | t₁}` and `y = !{s₂ | t₂}` is
`!{a₁ * y + x * b₁ - a₁ * b₁ | a₂ * y + x * b₂ - a₂ * b₂}`, where `(a₁, b₁) ∈ s₁ ×ˢ s₂ ∪ t₁ ×ˢ t₂`
and `(a₂, b₂) ∈ s₁ ×ˢ t₂ ∪ t₁ ×ˢ s₂`.

Using `LGame.mulOption`, this can alternatively be written as
`x * y = !{mulOption x y a₁ b₁ | mulOption x y a₂ b₂}`. -/
instance _root_.LGame.instMul : Mul LGame where
  mul x y := toLGame moves moves (right, x, y)

theorem _root_.LGame.corec_mul_corec (initα : α) (initβ : β) :
    corec movα initα * corec movβ initβ =
    toLGame movα movβ (right, initα, initβ) := by
  refine corec_comp_hom_apply (MulTy.map (corec movα) (corec movβ)) ?_ {(right, initα, initβ)}
  intro p
  apply MulTy.moves_comp_map
  all_goals exact fun _ ↦ moves_comp_corec ..

end MulTy

/-- The general option of `x * y` looks like `a * y + x * b - a * b`, for `a` and `b` options of
`x` and `y`, respectively. -/
@[pp_nodot]
def mulOption (x y a b : LGame) : LGame :=
  a * y + x * b - a * b

@[simp]
theorem moves_mul (p : Player) (x y : LGame) :
    (x * y).moves p = (fun a ↦ mulOption x y a.1 a.2) ''
      (xᴸ ×ˢ y.moves p ∪ xᴿ ×ˢ y.moves (-p)) := by
  apply (moves_corec ..).trans
  simp [MulTy.moves, MulTy.movesSingle, MulTy.corec_mulOption, image_image]
  cases p <;> rfl

@[simp]
theorem moves_mulOption (p : Player) (x y a b : LGame) :
    (mulOption x y a b).moves p = (a * y + x * b - a * b).moves p :=
  rfl

instance : CommMagma LGame where
  mul_comm _ _ := (MulTy.corec_swap ..).symm

instance : MulZeroClass LGame where
  zero_mul x := by ext p; cases p <;> simp
  mul_zero x := by ext p; cases p <;> simp

private theorem one_mul' (x : LGame) : 1 * x = x := by
  refine eq_of_bisim (fun x y ↦ x = 1 * y) ?_ rfl
  rintro _ x rfl p
  use (fun z ↦ (1 * z, z)) '' x.moves p
  aesop

instance : MulOneClass LGame where
  one_mul := one_mul'
  mul_one x := mul_comm x _ ▸ one_mul' x

private theorem neg_mul' (x y : LGame) : -x * y = -(x * y) := by
  change MulTy.toLGame .. = -MulTy.toLGame ..
  unfold MulTy.toLGame
  rw [neg_corec_apply]
  apply corec_comp_hom_apply
    (Multiset.map (fun y ↦ (y.1, -y.2.1, y.2.2))) _ {(right, x, y)}
  intro p
  ext
  simp [MulTy.moves_neg']

instance : HasDistribNeg LGame where
  neg_mul := neg_mul'
  mul_neg _ _ := by rw [mul_comm, neg_mul', mul_comm]

end LGame
