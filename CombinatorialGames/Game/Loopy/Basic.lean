/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Functor
import CombinatorialGames.Mathlib.Small
import Mathlib.Data.Setoid.Basic
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
instance, if `x = {x | x}ᴸ` and `y = {y | y}ᴸ`, then `x = y`, but trying to use extensionality to
prove this just leads to a cyclic argument. Instead, we can use `LGame.eq_of_bisim`, which can
roughly be interpreted as saying "if two games have the same shape, they're equal". In this case,
the relation `r a b ↔ a = x ∧ b = y` is a bisimulation between both games, which proves their
equality.
-/

open Set

universe u v w

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

/-- The set of left moves of the game. -/
def leftMoves (x : LGame.{u}) : Set LGame.{u} := x.dest.1.1

/-- The set of right moves of the game. -/
def rightMoves (x : LGame.{u}) : Set LGame.{u} := x.dest.1.2

instance small_leftMoves (x : LGame.{u}) : Small.{u} (leftMoves x) := x.dest.2.1
instance small_rightMoves (x : LGame.{u}) : Small.{u} (rightMoves x) := x.dest.2.2

/-- `IsOption x y` means that `x` is either a left or a right move for `y`. -/
@[aesop simp]
def IsOption (x y : LGame) : Prop :=
  x ∈ y.leftMoves ∪ y.rightMoves

theorem IsOption.of_mem_leftMoves {x y : LGame} : x ∈ y.leftMoves → IsOption x y := .inl
theorem IsOption.of_mem_rightMoves {x y : LGame} : x ∈ y.rightMoves → IsOption x y := .inr

instance (x : LGame.{u}) : Small.{u} {y // IsOption y x} :=
  inferInstanceAs (Small (x.leftMoves ∪ x.rightMoves :))

/-- A (proper) subposition is any game in the transitive closure of `IsOption`. -/
def Subposition : LGame → LGame → Prop :=
  Relation.TransGen IsOption

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_leftMoves {x y : LGame} (h : x ∈ y.leftMoves) : Subposition x y :=
  Relation.TransGen.single (.of_mem_leftMoves h)

@[aesop unsafe apply 50%]
theorem Subposition.of_mem_rightMoves {x y : LGame} (h : x ∈ y.rightMoves) : Subposition x y :=
  Relation.TransGen.single (.of_mem_rightMoves h)

theorem Subposition.trans {x y z : LGame} (h₁ : Subposition x y) (h₂ : Subposition y z) :
    Subposition x z :=
  Relation.TransGen.trans h₁ h₂

instance (x : LGame.{u}) : Small.{u} {y // Subposition y x} :=
  small_transGen' _ x

/-- Two loopy games are equal when there exists a bisimulation between them.

A way to think about this is that `r` defines a pairing between nodes of the game trees, which then
shows that the trees are isomorphic. -/
theorem eq_of_bisim (r : LGame → LGame → Prop)
    (H : ∀ x y, r x y → (∃ s : Set (LGame × LGame),
      Prod.fst '' s = x.leftMoves ∧ Prod.snd '' s = y.leftMoves ∧ ∀ z ∈ s, r z.1 z.2) ∧
        (∃ t : Set (LGame × LGame),
      Prod.fst '' t = x.rightMoves ∧ Prod.snd '' t = y.rightMoves ∧ ∀ z ∈ t, r z.1 z.2))
    (x y : LGame.{u}) (hxy : r x y) : x = y := by
  refine QPF.Cofix.bisim r (fun x y hxy ↦ ?_) x y hxy
  obtain ⟨⟨s, hs₁, hs₂, hs⟩, ⟨t, ht₁, ht₂, ht⟩⟩ := H _ _ hxy
  simp_rw [Set.ext_iff, mem_image, Prod.exists, exists_and_right, exists_eq_right] at *
  refine ⟨⟨⟨range (inclusion hs), range (inclusion ht)⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · have : Small.{u} s := small_subset (s := leftMoves x ×ˢ leftMoves y) fun z hz ↦
      ⟨(hs₁ z.1).1 ⟨_, hz⟩, (hs₂ z.2).1 ⟨_, hz⟩⟩
    infer_instance
  · have : Small.{u} t := small_subset (s := rightMoves x ×ˢ rightMoves y) fun z hz ↦
      ⟨(ht₁ z.1).1 ⟨_, hz⟩, (ht₂ z.2).1 ⟨_, hz⟩⟩
    infer_instance
  all_goals
    ext z
    all_goals
      revert z
      simpa [GameFunctor.map_def, ← range_comp]

/-- Two `LGame`s are equal when their move sets are.

This is not always sufficient to prove that two games are equal. For instance, if `x = {x | x}ᴸ` and
`y = {y | y}ᴸ`, then `x = y`, but trying to use extensionality to prove this just leads to a cyclic
argument. For these situations, you can use `eq_of_bisim` instead. -/
@[ext]
protected theorem ext {x y : LGame.{u}}
    (hl : x.leftMoves = y.leftMoves) (hr : x.rightMoves = y.rightMoves) : x = y := by
  refine eq_of_bisim (fun i j ↦ i.leftMoves = j.leftMoves ∧ i.rightMoves = j.rightMoves)
    (fun x y hxy ↦ ?_) x y ⟨hl, hr⟩
  refine ⟨⟨(fun i ↦ (i, i)) '' x.leftMoves, ?_⟩, ⟨(fun i ↦ (i, i)) '' x.rightMoves, ?_⟩⟩ <;>
    simp_all [image_image]

-- The default corecursion principle we get from `QPF` has inconvenient type universes, so we prove
-- a more general version.
section corec
variable {α : Type v}

/-- A node `α` is reachable from `init` when it can be formed by applying
`leftMoves` and `rightMoves` finitely many times. -/
private def Reachable (leftMoves : α → Set α) (rightMoves : α → Set α) (init : α) (a : α) : Prop :=
  Relation.ReflTransGen (fun x y ↦ x ∈ leftMoves y ∪ rightMoves y) a init

variable (leftMoves : α → Set α) (rightMoves : α → Set α)
  [∀ a, Small.{u} (leftMoves a)] [∀ a, Small.{u} (rightMoves a)] (init : α)

attribute [local instance] small_succ' in
private instance : Small.{u + 1} (Subtype (Reachable leftMoves rightMoves init)) :=
  small_reflTransGen' ..

/-- Destructor for the subtype of reachable positions. -/
@[simp]
private def dest (x : Shrink (Subtype (Reachable leftMoves rightMoves init))) :
    GameFunctor (Shrink (Subtype (Reachable leftMoves rightMoves init))) :=
  have hx := ((equivShrink _).symm x).2
  ⟨⟨equivShrink _ '' range (inclusion fun _y hy ↦ .trans (.single (.inl hy)) hx),
    equivShrink _ '' range (inclusion fun _y hy ↦ .trans (.single (.inr hy)) hx)⟩,
    inferInstance, inferInstance⟩

private theorem unique (f g : Subtype (Reachable leftMoves rightMoves init) → LGame.{u})
    (hf : QPF.Cofix.dest ∘ f ∘ (equivShrink _).symm =
      Functor.map (f ∘ (equivShrink _).symm) ∘ dest leftMoves rightMoves init)
    (hg : QPF.Cofix.dest ∘ g ∘ (equivShrink _).symm =
      Functor.map (g ∘ (equivShrink _).symm) ∘ dest leftMoves rightMoves init) (x) : f x = g x :=
  congrFun ((equivShrink _).symm.surjective.right_cancellable.1 <|
    QPF.Cofix.unique (dest leftMoves rightMoves init) _ _ hf hg) x

/-- The corecursor on the subtype of reachable nodes. -/
private def corec' (x : Subtype (Reachable leftMoves rightMoves init)) :=
  QPF.Cofix.corec (dest _ _ _) (equivShrink _ x)

/-- The corecursor on `LGame`.

You can use this in order to define an arbitrary `LGame` by "drawing" its move graph on some other
type. As an example, `on = {on | }ᴸ` is defined as `corec ⊤ ⊥ ()`. -/
def corec : LGame.{u} :=
  corec' leftMoves rightMoves init ⟨_, .refl⟩

private theorem corec'_trans {x} (hx : Reachable leftMoves rightMoves init x)
  (y : Subtype (Reachable leftMoves rightMoves x)) :
    corec' _ _ x y = corec' _ _ init (inclusion (fun _z hz ↦ .trans hz hx) y) := by
  apply unique <;> ext <;>
    simp [← range_comp, corec', QPF.Cofix.dest_corec, GameFunctor.map_def]

private theorem corec'_aux {a} (ha : a ∈ leftMoves init ∪ rightMoves init) {x : LGame} :
    (∃ ha : Reachable leftMoves rightMoves init a, corec' _ _ init ⟨a, ha⟩ = x) ↔
    corec leftMoves rightMoves a = x := by
  unfold corec
  constructor
  · rintro ⟨hx, rfl⟩
    simp [corec'_trans _ _ _ hx]
  · rintro rfl
    use .single ha
    simp [corec'_trans _ _ _ (.single ha)]

@[simp]
theorem leftMoves_corec : (corec leftMoves rightMoves init).leftMoves =
    corec leftMoves rightMoves '' leftMoves init := by
  rw [LGame.leftMoves, corec, corec', QPF.Cofix.dest_corec, GameFunctor.map_def]
  ext f
  simpa [← (equivShrink (Subtype (Reachable _ _ _))).exists_congr_right]
    using exists_congr fun a ↦ and_congr_right fun ha ↦ corec'_aux _ _ _ (.inl ha)

@[simp]
theorem rightMoves_corec : (corec leftMoves rightMoves init).rightMoves =
    corec leftMoves rightMoves '' rightMoves init := by
  rw [LGame.rightMoves, corec, corec', QPF.Cofix.dest_corec, GameFunctor.map_def]
  ext f
  simpa [← (equivShrink (Subtype (Reachable _ _ _))).exists_congr_right]
    using exists_congr fun a ↦ and_congr_right fun ha ↦ corec'_aux _ _ _ (.inr ha)

theorem leftMoves_comp_corec :
    LGame.leftMoves ∘ corec leftMoves rightMoves = image (corec leftMoves rightMoves) ∘ leftMoves :=
  funext (leftMoves_corec leftMoves rightMoves)

theorem rightMoves_comp_corec :
    LGame.rightMoves ∘ corec leftMoves rightMoves = image (corec leftMoves rightMoves) ∘ rightMoves :=
  funext (rightMoves_corec leftMoves rightMoves)

theorem hom_unique (leftMoves : α → Set α) (rightMoves : α → Set α)
    [∀ a, Small.{u} (leftMoves a)] [∀ a, Small.{u} (rightMoves a)] (f g : α → LGame.{u})
    (fLeftMoves : LGame.leftMoves ∘ f = image f ∘ leftMoves)
    (fRightMoves : LGame.rightMoves ∘ f = image f ∘ rightMoves)
    (gLeftMoves : LGame.leftMoves ∘ g = image g ∘ leftMoves)
    (gRightMoves : LGame.rightMoves ∘ g = image g ∘ rightMoves) : f = g := by
  funext x
  change (f ∘ Subtype.val) (⟨x, .refl⟩ : Subtype (Reachable leftMoves rightMoves x)) =
    (g ∘ Subtype.val) (⟨x, .refl⟩ : Subtype (Reachable leftMoves rightMoves x))
  apply unique <;> ext z
  · change _ ∈ (LGame.leftMoves ∘ f) _ ↔ _
    rw [fLeftMoves]
    simpa [GameFunctor.map_def, image_image] using exists_congr fun a ↦ and_congr_right
      fun ha ↦ iff_and_self.2 fun _ ↦ .trans (.single (.inl ha)) ((equivShrink _).symm z).2
  · change _ ∈ (LGame.rightMoves ∘ f) _ ↔ _
    rw [fRightMoves]
    simpa [GameFunctor.map_def, image_image] using exists_congr fun a ↦ and_congr_right
      fun ha ↦ iff_and_self.2 fun _ ↦ .trans (.single (.inr ha)) ((equivShrink _).symm z).2
  · change _ ∈ (LGame.leftMoves ∘ g) _ ↔ _
    rw [gLeftMoves]
    simpa [GameFunctor.map_def, image_image] using exists_congr fun a ↦ and_congr_right
      fun ha ↦ iff_and_self.2 fun _ ↦ .trans (.single (.inl ha)) ((equivShrink _).symm z).2
  · change _ ∈ (LGame.rightMoves ∘ g) _ ↔ _
    rw [gRightMoves]
    simpa [GameFunctor.map_def, image_image] using exists_congr fun a ↦ and_congr_right
      fun ha ↦ iff_and_self.2 fun _ ↦ .trans (.single (.inr ha)) ((equivShrink _).symm z).2

-- We make no use of `LGame`'s definition from a `QPF` after this point.
attribute [irreducible] LGame

end corec

theorem corec_comp_hom {α : Type v} {β : Type w}
    (leftMovesα : α → Set α) (rightMovesα : α → Set α)
    (leftMovesβ : β → Set β) (rightMovesβ : β → Set β)
    [∀ a, Small.{u} (leftMovesα a)] [∀ a, Small.{u} (rightMovesα a)]
    [∀ b, Small.{u} (leftMovesβ b)] [∀ b, Small.{u} (rightMovesβ b)] (f : α → β)
    (hlf : leftMovesβ ∘ f = Set.image f ∘ leftMovesα)
    (hrf : rightMovesβ ∘ f = Set.image f ∘ rightMovesα) :
    corec leftMovesβ rightMovesβ ∘ f = corec leftMovesα rightMovesα := by
  refine hom_unique leftMovesα rightMovesα _ _ ?_ ?_
    (leftMoves_comp_corec ..) (rightMoves_comp_corec ..)
  · rw [Set.image_comp_eq, Function.comp_assoc, ← hlf,
      ← Function.comp_assoc, leftMoves_comp_corec, Function.comp_assoc]
  · rw [Set.image_comp_eq, Function.comp_assoc, ← hrf,
      ← Function.comp_assoc, rightMoves_comp_corec, Function.comp_assoc]

@[simp]
theorem corec_leftMoves_rightMoves : corec leftMoves.{u} rightMoves.{u} = id :=
  hom_unique leftMoves rightMoves _ _
    (leftMoves_comp_corec leftMoves rightMoves)
    (rightMoves_comp_corec leftMoves rightMoves)
    (Set.image_id_eq ▸ rfl) (Set.image_id_eq ▸ rfl)

/-- Construct an `LGame` from its left and right sets.

This is given notation `{s | t}ᴸ`, where the superscript `L` is to disambiguate from set builder
notation, and from the analogous constructors on other game types.

It's not possible to create a non-well-founded game through this constructor alone. For that,
see `LGame.corec`. -/
noncomputable def ofSets (l : Set LGame.{u}) (r : Set LGame.{u})
    [Small.{u} l] [Small.{u} r] : LGame.{u} := by
  refine @corec (Option LGame.{u})
    (Option.elim · (some '' l) (some '' leftMoves ·))
    (Option.elim · (some '' r) (some '' rightMoves ·)) ?_ ?_ none <;>
  simpa [Option.forall] using ⟨inferInstance, inferInstance⟩

@[inherit_doc] notation "{" s " | " t "}ᴸ" => ofSets s t

@[simp]
theorem leftMoves_ofSets (l r : Set _) [Small.{u} l] [Small.{u} r] : {l | r}ᴸ.leftMoves = l := by
  rw [ofSets, leftMoves_corec, Option.elim_none, Set.image_image]
  conv_rhs => rw [← Set.image_id l, ← corec_leftMoves_rightMoves]
  generalize_proofs
  exact congrFun (congrArg _ (corec_comp_hom _ _ _ _ some rfl rfl)) _

@[simp]
theorem rightMoves_ofSets (l r : Set _) [Small.{u} l] [Small.{u} r] : {l | r}ᴸ.rightMoves = r := by
  rw [ofSets, rightMoves_corec, Option.elim_none, Set.image_image]
  conv_rhs => rw [← Set.image_id r, ← corec_leftMoves_rightMoves]
  generalize_proofs
  exact congrFun (congrArg _ (corec_comp_hom _ _ _ _ some rfl rfl)) _

/-! ### Basic games -/

/-- The game `on = {on | }`. -/
def on : LGame := corec ⊤ ⊥ ()

@[simp] theorem leftMoves_on : leftMoves on = {on} := by simp [on]
@[simp] theorem rightMoves_on : rightMoves on = ∅ := by simp [on]
theorem on_eq : on = {{on} | ∅}ᴸ := by ext <;> simp

theorem eq_on {x : LGame} : x = on ↔ leftMoves x = {x} ∧ rightMoves x = ∅ := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · simp_all
  · refine eq_of_bisim (fun a b ↦ a = x ∧ b = on) ?_ _ _ ⟨rfl, rfl⟩
    rintro a b ⟨rfl, rfl⟩
    refine ⟨⟨{(a, on)}, ?_⟩, ⟨∅, ?_⟩⟩ <;> simp_all

/-- The game `off = { | off}`. -/
def off : LGame := corec ⊥ ⊤ ()

@[simp] theorem leftMoves_off : leftMoves off = ∅ := by simp [off]
@[simp] theorem rightMoves_off : rightMoves off = {off} := by simp [off]
theorem off_eq : off = {∅ | {off}}ᴸ := by ext <;> simp

theorem eq_off {x : LGame} : x = off ↔ leftMoves x = ∅ ∧ rightMoves x = {x} := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · simp_all
  · refine eq_of_bisim (fun a b ↦ a = x ∧ b = off) ?_ _ _ ⟨rfl, rfl⟩
    rintro a b ⟨rfl, rfl⟩
    refine ⟨⟨∅, ?_⟩, ⟨{(a, off)}, ?_⟩⟩ <;> simp_all

/-- The game `dud = {dud | dud}`. -/
def dud : LGame := corec ⊤ ⊤ ()

@[simp] theorem leftMoves_dud : leftMoves dud = {dud} := by simp [dud]
@[simp] theorem rightMoves_dud : rightMoves dud = {dud} := by simp [dud]
theorem dud_eq : dud = {{dud} | {dud}}ᴸ := by ext <;> simp

instance : Unique dud.leftMoves := by refine ⟨⟨dud, ?_⟩, ?_⟩ <;> simp
instance : Unique dud.rightMoves := by refine ⟨⟨dud, ?_⟩, ?_⟩ <;> simp

theorem eq_dud {x : LGame} : x = dud ↔ leftMoves x = {x} ∧ rightMoves x = {x} := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · simp_all
  · refine eq_of_bisim (fun a b ↦ a = x ∧ b = dud) ?_ _ _ ⟨rfl, rfl⟩
    rintro a b ⟨rfl, rfl⟩
    refine ⟨⟨{(a, dud)}, ?_⟩, ⟨{(a, dud)}, ?_⟩⟩ <;> simp_all

end LGame
