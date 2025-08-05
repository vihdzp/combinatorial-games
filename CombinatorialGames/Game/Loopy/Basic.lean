/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.IGame
import CombinatorialGames.Mathlib.Small
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Countable.Small

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

instance : DecidableEq LGame := Classical.decEq _

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
    {x y : LGame.{u}} (hxy : r x y) : x = y := by
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
    (fun x y hxy ↦ ?_) ⟨hl, hr⟩
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

theorem hom_unique_apply {leftMoves : α → Set α} {rightMoves : α → Set α}
    [∀ a, Small.{u} (leftMoves a)] [∀ a, Small.{u} (rightMoves a)] (f g : α → LGame.{u})
    (hlf : LGame.leftMoves ∘ f = image f ∘ leftMoves)
    (hrf : LGame.rightMoves ∘ f = image f ∘ rightMoves)
    (hlg : LGame.leftMoves ∘ g = image g ∘ leftMoves)
    (hrg : LGame.rightMoves ∘ g = image g ∘ rightMoves) (x) : f x = g x := by
  change (f ∘ Subtype.val) (⟨x, .refl⟩ : Subtype (Reachable leftMoves rightMoves x)) =
    (g ∘ Subtype.val) (⟨x, .refl⟩ : Subtype (Reachable leftMoves rightMoves x))
  apply unique <;> ext z
  · change _ ∈ (LGame.leftMoves ∘ f) _ ↔ _
    rw [hlf]
    simpa [GameFunctor.map_def, image_image] using exists_congr fun a ↦ and_congr_right
      fun ha ↦ iff_and_self.2 fun _ ↦ .trans (.single (.inl ha)) ((equivShrink _).symm z).2
  · change _ ∈ (LGame.rightMoves ∘ f) _ ↔ _
    rw [hrf]
    simpa [GameFunctor.map_def, image_image] using exists_congr fun a ↦ and_congr_right
      fun ha ↦ iff_and_self.2 fun _ ↦ .trans (.single (.inr ha)) ((equivShrink _).symm z).2
  · change _ ∈ (LGame.leftMoves ∘ g) _ ↔ _
    rw [hlg]
    simpa [GameFunctor.map_def, image_image] using exists_congr fun a ↦ and_congr_right
      fun ha ↦ iff_and_self.2 fun _ ↦ .trans (.single (.inl ha)) ((equivShrink _).symm z).2
  · change _ ∈ (LGame.rightMoves ∘ g) _ ↔ _
    rw [hrg]
    simpa [GameFunctor.map_def, image_image] using exists_congr fun a ↦ and_congr_right
      fun ha ↦ iff_and_self.2 fun _ ↦ .trans (.single (.inr ha)) ((equivShrink _).symm z).2

theorem hom_unique {leftMoves : α → Set α} {rightMoves : α → Set α}
    [∀ a, Small.{u} (leftMoves a)] [∀ a, Small.{u} (rightMoves a)] (f g : α → LGame.{u})
    (hlf : LGame.leftMoves ∘ f = image f ∘ leftMoves)
    (hrf : LGame.rightMoves ∘ f = image f ∘ rightMoves)
    (hlg : LGame.leftMoves ∘ g = image g ∘ leftMoves)
    (hrg : LGame.rightMoves ∘ g = image g ∘ rightMoves) : f = g :=
  funext (hom_unique_apply _ _ hlf hrf hlg hrg)

-- We make no use of `LGame`'s definition from a `QPF` after this point.
attribute [irreducible] LGame

end corec

theorem corec_comp_hom
    {leftMovesα rightMovesα : α → Set α} {leftMovesβ rightMovesβ : β → Set β}
    [∀ a, Small.{u} (leftMovesα a)] [∀ a, Small.{u} (rightMovesα a)]
    [∀ b, Small.{u} (leftMovesβ b)] [∀ b, Small.{u} (rightMovesβ b)] (f : α → β)
    (hlf : leftMovesβ ∘ f = Set.image f ∘ leftMovesα)
    (hrf : rightMovesβ ∘ f = Set.image f ∘ rightMovesα) :
    corec leftMovesβ rightMovesβ ∘ f = corec leftMovesα rightMovesα := by
  refine hom_unique _ _ ?_ ?_
    (leftMoves_comp_corec ..) (rightMoves_comp_corec ..)
  · rw [Set.image_comp_eq, Function.comp_assoc, ← hlf,
      ← Function.comp_assoc, leftMoves_comp_corec, Function.comp_assoc]
  · rw [Set.image_comp_eq, Function.comp_assoc, ← hrf,
      ← Function.comp_assoc, rightMoves_comp_corec, Function.comp_assoc]

theorem corec_comp_hom_apply
    {leftMovesα rightMovesα : α → Set α} {leftMovesβ rightMovesβ : β → Set β}
    [∀ a, Small.{u} (leftMovesα a)] [∀ a, Small.{u} (rightMovesα a)]
    [∀ b, Small.{u} (leftMovesβ b)] [∀ b, Small.{u} (rightMovesβ b)] (f : α → β)
    (hlf : leftMovesβ ∘ f = Set.image f ∘ leftMovesα)
    (hrf : rightMovesβ ∘ f = Set.image f ∘ rightMovesα) (x : α) :
    corec leftMovesβ rightMovesβ (f x) = corec leftMovesα rightMovesα x :=
  congrFun (corec_comp_hom f hlf hrf) x

@[simp]
theorem corec_leftMoves_rightMoves : corec leftMoves rightMoves = id :=
  hom_unique _ _
    (leftMoves_comp_corec leftMoves rightMoves) (rightMoves_comp_corec leftMoves rightMoves)
    (Set.image_id_eq ▸ rfl) (Set.image_id_eq ▸ rfl)

theorem corec_leftMoves_rightMoves_apply (x : LGame) : corec leftMoves rightMoves x = x := by simp

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
  exact congrFun (congrArg _ (corec_comp_hom some rfl rfl)) _

@[simp]
theorem rightMoves_ofSets (l r : Set _) [Small.{u} l] [Small.{u} r] : {l | r}ᴸ.rightMoves = r := by
  rw [ofSets, rightMoves_corec, Option.elim_none, Set.image_image]
  conv_rhs => rw [← Set.image_id r, ← corec_leftMoves_rightMoves]
  generalize_proofs
  exact congrFun (congrArg _ (corec_comp_hom some rfl rfl)) _

/-! ### Basic games -/

/-- The game `0 = {∅ | ∅}ᴸ`. -/
instance : Zero LGame := ⟨{∅ | ∅}ᴸ⟩

theorem zero_def : 0 = {∅ | ∅}ᴸ := rfl

@[simp] theorem leftMoves_zero : leftMoves 0 = ∅ := leftMoves_ofSets ..
@[simp] theorem rightMoves_zero : rightMoves 0 = ∅ := rightMoves_ofSets ..

instance : Inhabited LGame := ⟨0⟩

/-- The game `1 = {{0} | ∅}ᴵ`. -/
instance : One LGame := ⟨{{0} | ∅}ᴸ⟩

theorem one_def : 1 = {{0} | ∅}ᴸ := rfl

@[simp] theorem leftMoves_one : leftMoves 1 = {0} := leftMoves_ofSets ..
@[simp] theorem rightMoves_one : rightMoves 1 = ∅ := rightMoves_ofSets ..

/-- The game `on = {{on} | ∅}ᴸ`. -/
def on : LGame := corec ⊤ ⊥ ()

@[simp] theorem leftMoves_on : leftMoves on = {on} := by simp [on]
@[simp] theorem rightMoves_on : rightMoves on = ∅ := by simp [on]
theorem on_eq : on = {{on} | ∅}ᴸ := by ext <;> simp

theorem eq_on {x : LGame} : x = on ↔ leftMoves x = {x} ∧ rightMoves x = ∅ := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · simp_all
  · refine eq_of_bisim (fun a b ↦ a = x ∧ b = on) ?_ ⟨rfl, rfl⟩
    rintro a b ⟨rfl, rfl⟩
    refine ⟨⟨{(a, on)}, ?_⟩, ⟨∅, ?_⟩⟩ <;> simp_all

/-- The game `off = {∅ | {off}}ᴸ`. -/
def off : LGame := corec ⊥ ⊤ ()

@[simp] theorem leftMoves_off : leftMoves off = ∅ := by simp [off]
@[simp] theorem rightMoves_off : rightMoves off = {off} := by simp [off]
theorem off_eq : off = {∅ | {off}}ᴸ := by ext <;> simp

theorem eq_off {x : LGame} : x = off ↔ leftMoves x = ∅ ∧ rightMoves x = {x} := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · simp_all
  · refine eq_of_bisim (fun a b ↦ a = x ∧ b = off) ?_ ⟨rfl, rfl⟩
    rintro a b ⟨rfl, rfl⟩
    refine ⟨⟨∅, ?_⟩, ⟨{(a, off)}, ?_⟩⟩ <;> simp_all

/-- The game `dud = {{dud} | {dud}}ᴸ`. -/
def dud : LGame := corec ⊤ ⊤ ()

@[simp] theorem leftMoves_dud : leftMoves dud = {dud} := by simp [dud]
@[simp] theorem rightMoves_dud : rightMoves dud = {dud} := by simp [dud]
theorem dud_eq : dud = {{dud} | {dud}}ᴸ := by ext <;> simp

theorem eq_dud {x : LGame} : x = dud ↔ leftMoves x = {x} ∧ rightMoves x = {x} := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · simp_all
  · refine eq_of_bisim (fun a b ↦ a = x ∧ b = dud) ?_ ⟨rfl, rfl⟩
    rintro a b ⟨rfl, rfl⟩
    refine ⟨⟨{(a, dud)}, ?_⟩, ⟨{(a, dud)}, ?_⟩⟩ <;> simp_all

/-! ### Negation -/

/-- The negative of a game is defined by `-{s | t}ᴸ = {-t | -s}ᴸ`. -/
instance : Neg LGame where
  neg := corec rightMoves leftMoves

@[simp] theorem corec_rightMoves_leftMoves : corec rightMoves leftMoves = (- ·) := rfl
theorem corec_rightMoves_leftMoves_apply (x : LGame) : corec rightMoves leftMoves x = -x := rfl

theorem neg_corec (leftMoves rightMoves : α → Set α)
    [∀ x, Small.{u} (leftMoves x)] [∀ x, Small.{u} (rightMoves x)] :
    -corec leftMoves rightMoves = corec rightMoves leftMoves :=
  corec_comp_hom _ (rightMoves_comp_corec ..)  (leftMoves_comp_corec ..)

theorem neg_corec_apply (leftMoves rightMoves : α → Set α)
    [∀ x, Small.{u} (leftMoves x)] [∀ x, Small.{u} (rightMoves x)] (init : α) :
    -corec leftMoves rightMoves init = corec rightMoves leftMoves init :=
  congrFun (neg_corec ..) _

instance : InvolutiveNeg LGame where
  neg_neg _ := (neg_corec_apply ..).trans (corec_leftMoves_rightMoves_apply ..)

@[simp]
theorem leftMoves_neg (x : LGame) : (-x).leftMoves = -x.rightMoves := by
  rw [← Set.image_neg_eq_neg]
  exact leftMoves_corec ..

@[simp]
private theorem rightMoves_neg (x : LGame) : (-x).rightMoves = -x.leftMoves := by
  rw [← Set.image_neg_eq_neg]
  exact rightMoves_corec ..

@[simp]
theorem neg_ofSets (s t : Set LGame.{u}) [Small.{u} s] [Small.{u} t] : -{s | t}ᴸ = {-t | -s}ᴸ := by
  ext <;> simp

instance : NegZeroClass LGame where
  neg_zero := by simp [zero_def]

@[simp] theorem neg_on : -on = off := neg_corec_apply ..
@[simp] theorem neg_off : -off = on := neg_corec_apply ..
@[simp] theorem neg_dud : -dud = dud := neg_corec_apply ..

/-! ### Addition -/

/-- The sum of `x = {s₁ | t₁}ᴸ` and `y = {s₂ | t₂}ᴸ` is `{s₁ + y, x + s₂ | t₁ + y, x + t₂}ᴸ`. -/
instance : Add LGame where
  add x y := corec
    (fun x ↦ (fun y ↦ (y, x.2)) '' leftMoves x.1 ∪ (fun y ↦ (x.1, y)) '' leftMoves x.2)
    (fun x ↦ (fun y ↦ (y, x.2)) '' rightMoves x.1 ∪ (fun y ↦ (x.1, y)) '' rightMoves x.2)
    (x, y)

theorem corec_add_corec
    {leftMovesα rightMovesα : α → Set α} {leftMovesβ rightMovesβ : β → Set β}
    [∀ x, Small.{u} (leftMovesα x)] [∀ x, Small.{u} (rightMovesα x)]
    [∀ x, Small.{u} (leftMovesβ x)] [∀ x, Small.{u} (rightMovesβ x)] (initα : α) (initβ : β) :
    corec leftMovesα rightMovesα initα + corec leftMovesβ rightMovesβ initβ =
    corec
      (fun x ↦ (fun y ↦ (y, x.2)) '' leftMovesα x.1 ∪ (fun y ↦ (x.1, y)) '' leftMovesβ x.2)
      (fun x ↦ (fun y ↦ (y, x.2)) '' rightMovesα x.1 ∪ (fun y ↦ (x.1, y)) '' rightMovesβ x.2)
      (initα, initβ) := by
  refine corec_comp_hom_apply
    (Prod.map (corec leftMovesα rightMovesα) (corec leftMovesβ rightMovesβ)) ?_ ?_ (initα, initβ)
  all_goals
    refine funext fun ⟨a, b⟩ ↦ ?_
    simp [Set.image_image, Set.image_union, leftMoves_corec, rightMoves_corec]

@[simp]
theorem leftMoves_add (x y : LGame) :
    (x + y).leftMoves = (· + y) '' x.leftMoves ∪ (x + ·) '' y.leftMoves := by
  apply (leftMoves_corec ..).trans
  aesop

@[simp]
theorem rightMoves_add (x y : LGame) :
    (x + y).rightMoves = (· + y) '' x.rightMoves ∪ (x + ·) '' y.rightMoves := by
  apply (rightMoves_corec ..).trans
  aesop

@[simp]
theorem add_eq_zero_iff {x y : LGame} : x + y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor <;> simp_all [LGame.ext_iff]

private theorem add_zero' (x : LGame) : x + 0 = x := by
  refine eq_of_bisim (fun x y ↦ x = y + 0) ?_ rfl
  rintro a b rfl
  refine
    ⟨⟨(fun x ↦ (x + 0, x)) '' b.leftMoves, ?_, ?_⟩, ⟨(fun x ↦ (x + 0, x)) '' b.rightMoves, ?_, ?_⟩⟩
  all_goals simp [image_image]

private theorem add_comm' (x y : LGame) : x + y = y + x := by
  apply eq_of_bisim (fun x y ↦ ∃ a b, x = a + b ∧ y = b + a) ?_ ⟨x, y, rfl, rfl⟩
  rintro _ _ ⟨a, b, rfl, rfl⟩
  refine
    ⟨⟨(fun x ↦ (x + b, b + x)) '' a.leftMoves ∪ (fun x ↦ (a + x, x + a)) '' b.leftMoves, ?_, ?_⟩,
    ⟨(fun x ↦ (x + b, b + x)) '' a.rightMoves ∪ (fun x ↦ (a + x, x + a)) '' b.rightMoves, ?_, ?_⟩⟩
  all_goals aesop

private theorem add_assoc' (x y z : LGame) : x + y + z = x + (y + z) := by
  apply eq_of_bisim (fun x y ↦ ∃ a b c, x = a + b + c ∧ y = a + (b + c)) ?_ ⟨x, y, z, rfl, rfl⟩
  rintro _ _ ⟨a, b, c, rfl, rfl⟩
  refine
    ⟨⟨(fun x ↦ (x + b + c, x + (b + c))) '' a.leftMoves ∪
    (fun x ↦ (a + x + c, a + (x + c))) '' b.leftMoves ∪
    (fun x ↦ (a + b + x, a + (b + x))) '' c.leftMoves, ?_, ?_⟩,
    ⟨(fun x ↦ (x + b + c, x + (b + c))) '' a.rightMoves ∪
    (fun x ↦ (a + x + c, a + (x + c))) '' b.rightMoves ∪
    (fun x ↦ (a + b + x, a + (b + x))) '' c.rightMoves, ?_, ?_⟩⟩
  all_goals aesop (add simp [image_union])

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
  refine
    ⟨⟨insert (x + dud, dud) ((fun y ↦ (y + dud, dud)) '' x.leftMoves), ?_, ?_⟩,
    ⟨insert (x + dud, dud) ((fun y ↦ (y + dud, dud)) '' x.rightMoves), ?_, ?_⟩⟩
  all_goals aesop

@[simp]
theorem dud_add (x : LGame) : dud + x = dud := by
  rw [add_comm, add_dud]

theorem leftMoves_sum (m : Multiset LGame) : m.sum.leftMoves =
    ⋃ y ∈ m, (· + (m.erase y).sum) '' y.leftMoves := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m IH =>
    simp only [leftMoves_add, IH, image_iUnion, image_image, Multiset.mem_cons, Multiset.sum_cons,
      iUnion_iUnion_eq_or_left, Multiset.erase_cons_head]
    congr! 5 with _ h
    rw [Multiset.erase_cons_tail_of_mem h]
    simp [← add_assoc, add_comm]

theorem rightMoves_sum (m : Multiset LGame) : m.sum.rightMoves =
    ⋃ y ∈ m, (· + (m.erase y).sum) '' y.rightMoves := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m IH =>
    simp only [rightMoves_add, IH, image_iUnion, image_image, Multiset.mem_cons, Multiset.sum_cons,
      iUnion_iUnion_eq_or_left, Multiset.erase_cons_head]
    congr! 5 with _ h
    rw [Multiset.erase_cons_tail_of_mem h]
    simp [← add_assoc, add_comm]

/-- The subtraction of `x` and `y` is defined as `x + (-y)`. -/
instance : SubNegMonoid LGame where
  zsmul := zsmulRec

theorem corec_sub_corec
    {leftMovesα rightMovesα : α → Set α} {leftMovesβ rightMovesβ : β → Set β}
    [∀ x, Small.{u} (leftMovesα x)] [∀ x, Small.{u} (rightMovesα x)]
    [∀ x, Small.{u} (leftMovesβ x)] [∀ x, Small.{u} (rightMovesβ x)] (initα : α) (initβ : β) :
    corec leftMovesα rightMovesα initα - corec leftMovesβ rightMovesβ initβ =
    corec
      (fun x ↦ (fun y ↦ (y, x.2)) '' leftMovesα x.1 ∪ (fun y ↦ (x.1, y)) '' rightMovesβ x.2)
      (fun x ↦ (fun y ↦ (y, x.2)) '' rightMovesα x.1 ∪ (fun y ↦ (x.1, y)) '' leftMovesβ x.2)
      (initα, initβ) := by
  rw [sub_eq_add_neg, neg_corec_apply, corec_add_corec]

@[simp]
theorem leftMoves_sub (x y : LGame) :
    (x - y).leftMoves = (· - y) '' x.leftMoves ∪ (x + ·) '' (-y.rightMoves) := by
  simp [sub_eq_add_neg]

@[simp]
theorem rightMoves_sub (x y : LGame) :
    (x - y).rightMoves = (· - y) '' x.rightMoves ∪ (x + ·) '' (-y.leftMoves) := by
  simp [sub_eq_add_neg]

private theorem neg_add' (x y : LGame) : -(x + y) = -x + -y := by
  refine eq_of_bisim (fun x y ↦ ∃ a b, x = -(a + b) ∧ y = -a + -b) ?_ ⟨x, y, rfl, rfl⟩
  rintro _ _ ⟨a, b, rfl, rfl⟩
  refine
    ⟨⟨(fun x ↦ (-(x + b), -x + -b)) '' a.rightMoves ∪
    (fun x ↦ (-(a + x), -a + -x)) '' b.rightMoves, ?_, ?_⟩,
    ⟨(fun x ↦ (-(x + b), -x + -b)) '' a.leftMoves ∪
    (fun x ↦ (-(a + x), -a + -x)) '' b.leftMoves, ?_, ?_⟩⟩
  all_goals aesop (add simp [image_union])

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
type `Multiset (Bool × α × β)`. Each term corresponds to a sum `Σ ±aᵢ * bᵢ`, where `aᵢ` and `bᵢ` are
terms of `α` and `β` respectively. -/
@[reducible]
def MulTy (α β : Type*) :=
  Multiset (Bool × α × β)

namespace MulTy

instance : InvolutiveNeg (MulTy α β) where
  neg x := Multiset.map (fun y ↦ (!y.1, y.2)) x
  neg_neg x := by simp

theorem neg_def (x : MulTy α β) : -x = Multiset.map (fun y ↦ (!y.1, y.2)) x :=
  rfl

@[simp]
theorem mem_neg {x : Bool × α × β} {y : MulTy α β} : x ∈ -y ↔ (!x.1, x.2) ∈ y := by
  convert Multiset.mem_map_of_injective (a := (!x.1, x.2)) _ <;>
    simp [Function.Injective]

@[simp]
theorem neg_zero : -(0 : MulTy α β) = 0 :=
  rfl

@[simp]
theorem neg_singleton (a : Bool × α × β) : -({a} : MulTy α β) = {(!a.1, a.2)} :=
  rfl

@[simp]
theorem neg_cons (a : Bool × α × β) (x : MulTy α β) : -(a ::ₘ x) = (!a.1, a.2) ::ₘ -x :=
  Multiset.map_cons ..

@[simp]
theorem neg_add (x y : MulTy α β) : -(x + y) = -x + -y :=
  Multiset.map_add ..

@[simp]
theorem neg_erase [DecidableEq α] [DecidableEq β] (x : MulTy α β) (a : Bool × α × β) :
    -x.erase a = (-x).erase (!a.1, a.2) :=
  Multiset.map_erase _ (fun _ ↦ by simp) ..

/-- The general form of an option of `x * y` is `a * y + x * b - a * b`.

If the boolean argument is false, all signs are flipped. -/
def mulOption (b : Bool) (x : α × β) (y : α × β) : MulTy α β :=
  {(b, y.1, x.2), (b, x.1, y.2), (!b, y.1, y.2)}

@[simp]
theorem neg_mulOption (b : Bool) (x : α × β) (y : α × β) :
    -mulOption b x y = mulOption (!b) x y := by
  simp [mulOption]

theorem mulOption_eq_add (b : Bool) (x : α × β) (y : α × β) :
    mulOption b x y = {(b, y.1, x.2)} + {(b, x.1, y.2)} + {(!b, y.1, y.2)} :=
  rfl

variable (leftMovesα rightMovesα : α → Set α) (leftMovesβ rightMovesβ : β → Set β)

/-- The set of pairs `α × β` used in `leftMovesSingle`. -/
def leftMovesSet (x : Bool × α × β) : Set (α × β) :=
  x.1.rec
    (leftMovesα x.2.1 ×ˢ rightMovesβ x.2.2 ∪ rightMovesα x.2.1 ×ˢ leftMovesβ x.2.2)
    (leftMovesα x.2.1 ×ˢ leftMovesβ x.2.2 ∪ rightMovesα x.2.1 ×ˢ rightMovesβ x.2.2)

/-- The set of pairs `α × β` used in `rightMovesSingle`. -/
def rightMovesSet (x : Bool × α × β) : Set (α × β) :=
  leftMovesSet leftMovesα rightMovesα leftMovesβ rightMovesβ (!x.1, x.2)

theorem leftMovesSet_neg (x : Bool × α × β) :
    leftMovesSet leftMovesα rightMovesα leftMovesβ rightMovesβ (!x.1, x.2) =
    rightMovesSet leftMovesα rightMovesα leftMovesβ rightMovesβ x :=
  rfl

theorem rightMovesSet_neg (x : Bool × α × β) :
    rightMovesSet leftMovesα rightMovesα leftMovesβ rightMovesβ (!x.1, x.2) =
    leftMovesSet leftMovesα rightMovesα leftMovesβ rightMovesβ x := by
  obtain ⟨_ | _, _, _⟩ := x <;> rfl

/-- The left moves of `±x * y` are left moves of `x * y` if the sign is positive, or the
negatives of right moves of `x * y` if the sign is negative. -/
def leftMovesSingle (x : Bool × α × β) : Set (MulTy α β) :=
  mulOption x.1 x.2 '' leftMovesSet leftMovesα rightMovesα leftMovesβ rightMovesβ x

/-- The right moves of `±x * y` are right moves of `x * y` if the sign is positive, or the
negatives of left moves of `x * y` if the sign is negative. -/
def rightMovesSingle (x : Bool × α × β) : Set (MulTy α β) :=
  mulOption x.1 x.2 '' rightMovesSet leftMovesα rightMovesα leftMovesβ rightMovesβ x

theorem leftMovesSingle_neg (x : Bool × α × β) :
    leftMovesSingle leftMovesα rightMovesα leftMovesβ rightMovesβ (!x.1, x.2) =
    -rightMovesSingle leftMovesα rightMovesα leftMovesβ rightMovesβ x := by
  rw [leftMovesSingle, rightMovesSingle, leftMovesSet_neg]
  simp [image_image, ← image_neg_eq_neg]

theorem rightMovesSingle_neg (x : Bool × α × β) :
    rightMovesSingle leftMovesα rightMovesα leftMovesβ rightMovesβ (!x.1, x.2) =
    -leftMovesSingle leftMovesα rightMovesα leftMovesβ rightMovesβ x := by
  rw [leftMovesSingle, rightMovesSingle, rightMovesSet_neg]
  simp [image_image, ← image_neg_eq_neg]

variable [Hα : DecidableEq α] [Hβ : DecidableEq β]

/-- The set of left moves of `Σ ±xᵢ * yᵢ` are `zᵢ + Σ ±xⱼ * yⱼ` for all `i`, where `cᵢ` is a left
move of `±xᵢ * yᵢ`, and the summation is taken over indices `j ≠ i`. -/
def leftMoves (x : MulTy α β) : Set (MulTy α β) :=
  ⋃ y ∈ x, (x.erase y + ·) '' leftMovesSingle leftMovesα rightMovesα leftMovesβ rightMovesβ y

/-- The set of right moves of `Σ ±xᵢ * yᵢ` are `zᵢ + Σ ±xⱼ * yⱼ` for all `i`, where `cᵢ` is a right
move of `±xᵢ * yᵢ`, and the summation is taken over indices `j ≠ i`. -/
def rightMoves (x : MulTy α β) : Set (MulTy α β) :=
  ⋃ y ∈ x, (x.erase y + ·) '' rightMovesSingle leftMovesα rightMovesα leftMovesβ rightMovesβ y

theorem _root_.Multiset.iUnion_map {α β γ} (m : Multiset α) (f : α → β) (g : β → Set γ) :
    ⋃ x ∈ m.map f, g x = ⋃ x ∈ m, g (f x) := by
  simp

theorem leftMoves_neg (x : MulTy α β) :
    leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ (-x) =
    -rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ x := by
  rw [leftMoves, rightMoves, neg_def, Multiset.iUnion_map]
  simp [← image_neg_eq_neg, image_iUnion, image_image, leftMovesSingle_neg, ← neg_def]

theorem rightMoves_neg (x : MulTy α β) :
    rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ (-x) =
    -leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ x := by
  rw [leftMoves, rightMoves, neg_def, Multiset.iUnion_map]
  simp [← image_neg_eq_neg, image_iUnion, image_image, rightMovesSingle_neg, ← neg_def]

variable {α₁ β₁ α₂ β₂ : Type*}
  {leftMovesα₁ rightMovesα₁ : α₁ → Set α₁} {leftMovesβ₁ rightMovesβ₁ : β₁ → Set β₁}
  {leftMovesα₂ rightMovesα₂ : α₂ → Set α₂} {leftMovesβ₂ rightMovesβ₂ : β₂ → Set β₂}
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

variable {f g}
  [Hα₁ : DecidableEq α₁] [Hβ₁ : DecidableEq β₁] [Hα₂ : DecidableEq α₂] [Hβ₂ : DecidableEq β₂]

set_option maxHeartbeats 1000000 in
omit Hα₁ Hα₂ Hβ₁ Hβ₂ in
theorem leftMovesSingle_comp_prodMap
    (hlf : leftMovesα₂ ∘ f = Set.image f ∘ leftMovesα₁)
    (hrf : rightMovesα₂ ∘ f = Set.image f ∘ rightMovesα₁)
    (hlg : leftMovesβ₂ ∘ g = Set.image g ∘ leftMovesβ₁)
    (hrg : rightMovesβ₂ ∘ g = Set.image g ∘ rightMovesβ₁) :
    leftMovesSingle leftMovesα₂ rightMovesα₂ leftMovesβ₂ rightMovesβ₂ ∘ Prod.map id (Prod.map f g) =
    image (map f g) ∘ leftMovesSingle leftMovesα₁ rightMovesα₁ leftMovesβ₁ rightMovesβ₁ := by
  simp_rw [funext_iff, Function.comp_apply, leftMovesSingle, leftMovesSet] at *
  rintro ⟨(_ | _), x⟩ <;> aesop

-- TODO: find a faster proof using the previous theorem?
set_option maxHeartbeats 1000000 in
omit Hα₁ Hα₂ Hβ₁ Hβ₂ in
theorem rightMovesSingle_comp_prodMap
    (hlf : leftMovesα₂ ∘ f = Set.image f ∘ leftMovesα₁)
    (hrf : rightMovesα₂ ∘ f = Set.image f ∘ rightMovesα₁)
    (hlg : leftMovesβ₂ ∘ g = Set.image g ∘ leftMovesβ₁)
    (hrg : rightMovesβ₂ ∘ g = Set.image g ∘ rightMovesβ₁) :
    rightMovesSingle leftMovesα₂ rightMovesα₂ leftMovesβ₂ rightMovesβ₂ ∘ Prod.map id (Prod.map f g) =
    image (map f g) ∘ rightMovesSingle leftMovesα₁ rightMovesα₁ leftMovesβ₁ rightMovesβ₁ := by
  simp_rw [funext_iff, Function.comp_apply, rightMovesSingle, rightMovesSet, leftMovesSet] at *
  rintro ⟨(_ | _), x⟩ <;> aesop

theorem leftMoves_comp_map
    (hlf : leftMovesα₂ ∘ f = Set.image f ∘ leftMovesα₁)
    (hrf : rightMovesα₂ ∘ f = Set.image f ∘ rightMovesα₁)
    (hlg : leftMovesβ₂ ∘ g = Set.image g ∘ leftMovesβ₁)
    (hrg : rightMovesβ₂ ∘ g = Set.image g ∘ rightMovesβ₁) :
    leftMoves leftMovesα₂ rightMovesα₂ leftMovesβ₂ rightMovesβ₂ ∘ map f g =
    image (map f g) ∘ leftMoves leftMovesα₁ rightMovesα₁ leftMovesβ₁ rightMovesβ₁ := by
  apply funext fun x ↦ ?_
  simp_rw [Function.comp_apply, leftMoves, map, Multiset.iUnion_map, image_iUnion]
  congr! with y hy
  simp_rw [← Multiset.map_erase_of_mem _ _ hy, ← Function.comp_apply (g := Prod.map id _),
    leftMovesSingle_comp_prodMap hlf hrf hlg hrg]
  aesop

theorem rightMoves_comp_map
    (hlf : leftMovesα₂ ∘ f = Set.image f ∘ leftMovesα₁)
    (hrf : rightMovesα₂ ∘ f = Set.image f ∘ rightMovesα₁)
    (hlg : leftMovesβ₂ ∘ g = Set.image g ∘ leftMovesβ₁)
    (hrg : rightMovesβ₂ ∘ g = Set.image g ∘ rightMovesβ₁) :
    rightMoves leftMovesα₂ rightMovesα₂ leftMovesβ₂ rightMovesβ₂ ∘ map f g =
    image (map f g) ∘ rightMoves leftMovesα₁ rightMovesα₁ leftMovesβ₁ rightMovesβ₁ := by
  apply funext fun x ↦ ?_
  simp_rw [Function.comp_apply, rightMoves, map, Multiset.mem_map, iUnion_exists, biUnion_and',
    iUnion_iUnion_eq_right, image_iUnion]
  congr! with y hy
  simp_rw [← Multiset.map_erase_of_mem _ _ hy, ← Function.comp_apply (g := Prod.map id _),
    rightMovesSingle_comp_prodMap hlf hrf hlg hrg]
  aesop

variable
    [∀ x, Small.{u} (leftMovesα x)] [∀ x, Small.{u} (rightMovesα x)]
    [∀ x, Small.{u} (leftMovesβ x)] [∀ x, Small.{u} (rightMovesβ x)]

private instance (x : Bool × α × β) :
    Small.{u} (leftMovesSet leftMovesα rightMovesα leftMovesβ rightMovesβ x) := by
  obtain ⟨(_ | _), _⟩ := x <;> exact small_union ..

private instance (x : Bool × α × β) :
    Small.{u} (rightMovesSet leftMovesα rightMovesα leftMovesβ rightMovesβ x) := by
  obtain ⟨(_ | _), _⟩ := x <;> exact small_union ..

instance (x : Bool × α × β) :
    Small.{u} (leftMovesSingle leftMovesα rightMovesα leftMovesβ rightMovesβ x) :=
  small_image ..

instance (x : Bool × α × β) :
    Small.{u} (rightMovesSingle leftMovesα rightMovesα leftMovesβ rightMovesβ x) :=
  small_image ..

instance (x : MulTy α β) :
    Small.{u} (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ x) := by
  simp_rw [leftMoves, ← Multiset.mem_toFinset]
  exact small_biUnion.{u} (Multiset.toFinset x).toSet _

instance (x : MulTy α β) :
    Small.{u} (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ x) := by
  simp_rw [rightMoves, ← Multiset.mem_toFinset]
  exact small_biUnion.{u} (Multiset.toFinset x).toSet _

/-- The game `±xᵢ * yᵢ`. -/
def toLGame (x : Bool × α × β) : LGame :=
  corec
    (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
    (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) {x}

theorem leftMoves_toLGame (x : Bool × α × β) :
    (toLGame leftMovesα rightMovesα leftMovesβ rightMovesβ x).leftMoves =
    corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) ''
    leftMovesSingle leftMovesα rightMovesα leftMovesβ rightMovesβ x := by
  apply (leftMoves_corec ..).trans
  simp [leftMoves]

theorem rightMoves_toLGame (x : Bool × α × β) :
    (toLGame leftMovesα rightMovesα leftMovesβ rightMovesβ x).rightMoves =
    corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) ''
    rightMovesSingle leftMovesα rightMovesα leftMovesβ rightMovesβ x := by
  apply (rightMoves_corec ..).trans
  simp [rightMoves]

@[simp]
theorem corec_zero :
    corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) 0 = 0 := by
  ext <;> simp [leftMoves, rightMoves]

theorem corec_neg (init : MulTy α β) :
    corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) (-init) =
    -corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) init := by
  rw [neg_corec_apply]
  apply corec_comp_hom_apply
  all_goals
  · ext
    simp [leftMoves_neg, rightMoves_neg]

theorem corec_add (init₁ init₂ : MulTy α β) :
    corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) (init₁ + init₂) =
    corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) init₁ +
    corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) init₂ := by
  refine eq_of_bisim (fun a b ↦ ∃ x y,
    a = corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) (x + y) ∧
    b = corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) x +
    corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) y) ?_
    ⟨_, _, rfl, rfl⟩
  rintro _ _ ⟨x, y, rfl, rfl⟩
  let f (s : _ → _) := (⋃ z ∈ x, (fun w ↦
      (corec
        (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
        (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
        (mulOption z.1 z.2 w + x.erase z + y),
      corec
        (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
        (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
        (mulOption z.1 z.2 w + x.erase z) +
      corec
        (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
        (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) y)) '' s z) ∪
    (⋃ z ∈ y, (fun w ↦
      (corec
        (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
        (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
        (mulOption z.1 z.2 w + x + y.erase z),
      corec
        (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
        (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) x +
      corec
        (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
        (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
        (mulOption z.1 z.2 w + y.erase z))) '' s z)
  constructor
  on_goal 1 => use f (leftMovesSet leftMovesα rightMovesα leftMovesβ rightMovesβ)
  on_goal 2 => use f (rightMovesSet leftMovesα rightMovesα leftMovesβ rightMovesβ)
  all_goals
    simp only [f, image_union, image_iUnion, image_image,
      Multiset.mem_add, iUnion_or, iUnion_union_distrib,
      leftMoves_corec, leftMoves, leftMovesSingle, rightMoves_corec, rightMoves, rightMovesSingle]
    refine ⟨?_, ?_, ?_⟩
    · congr! 6 with a ha b hb a ha b hb
      · rw [Multiset.erase_add_left_pos _ ha]
        simp [add_comm, add_assoc]
      · rw [Multiset.erase_add_right_pos _ ha]
        simp [add_comm, ← add_assoc]
    · simp [image_iUnion, image_image, leftMoves, leftMovesSingle, rightMoves, rightMovesSingle,
        add_comm]
    · rintro z (⟨_, ⟨a, rfl⟩, ⟨c, ⟨ha, rfl⟩, ⟨b, hb, rfl⟩⟩⟩ | ⟨_, ⟨a, rfl⟩, ⟨c, ⟨ha, rfl⟩, ⟨b, hb, rfl⟩⟩⟩)
      · use mulOption a.1 a.2 b + x.erase a, y
      · use mulOption a.1 a.2 b + y.erase a, x
        simp [add_comm, ← add_assoc]

theorem corec_mulOption (b : Bool) (x y : α × β) :
    corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) (mulOption b x y) =
    toLGame leftMovesα rightMovesα leftMovesβ rightMovesβ (b, y.1, x.2) +
    toLGame leftMovesα rightMovesα leftMovesβ rightMovesβ (b, x.1, y.2) -
    toLGame leftMovesα rightMovesα leftMovesβ rightMovesβ (b, y.1, y.2) := by
  simp_rw [mulOption_eq_add, corec_add, toLGame]
  congr
  rw [← corec_neg, neg_singleton]

theorem _root_.LGame.corec_mulTy (x : MulTy α β) :
  corec
    (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
    (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) x =
  (Multiset.map (toLGame leftMovesα rightMovesα leftMovesβ rightMovesβ) x).sum := by
  refine eq_of_bisim (fun a b ↦ ∃ z,
    a = corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ) z ∧
    b = (Multiset.map (toLGame leftMovesα rightMovesα leftMovesβ rightMovesβ) z).sum) ?_
    ⟨x, rfl, rfl⟩
  rintro _ _ ⟨x, rfl, rfl⟩
  let f (s : _ → _) := ⋃ y ∈ x, (fun z ↦
    (corec
      (leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (x.erase y + mulOption y.1 y.2 z),
    (Multiset.map (toLGame leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (x.erase y + mulOption y.1 y.2 z)).sum)) '' s y
  constructor
  on_goal 1 => use f (leftMovesSet leftMovesα rightMovesα leftMovesβ rightMovesβ)
  on_goal 2 => use f (rightMovesSet leftMovesα rightMovesα leftMovesβ rightMovesβ)
  all_goals
    simp only [f, toLGame, Multiset.map_add, image_iUnion, image_image, Multiset.iUnion_map,
      Multiset.mem_singleton, iUnion_iUnion_eq_left, Multiset.erase_singleton, Multiset.zero_add,
      leftMoves_sum, leftMoves_corec, leftMoves, leftMovesSingle,
      rightMoves_sum, rightMoves_corec, rightMoves, rightMovesSingle, true_and]
    constructor
    · congr! 4 with y hy
      rw [Multiset.map_erase_of_mem _ _ hy, corec_mulOption]
      simp [mulOption, toLGame, sub_eq_add_neg, add_comm, add_assoc, ← corec_neg]
    · rintro ⟨y, z⟩ ⟨a, ⟨⟨c, rfl⟩, ⟨d, ⟨e, rfl⟩, ⟨f, hf, h⟩⟩ ⟩⟩
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h
      exact ⟨_, rfl, by simp⟩

/-- The product of `x = {s₁ | t₁}ᴵ` and `y = {s₂ | t₂}ᴵ` is
`{a₁ * y + x * b₁ - a₁ * b₁ | a₂ * y + x * b₂ - a₂ * b₂}ᴵ`, where `(a₁, b₁) ∈ s₁ ×ˢ s₂ ∪ t₁ ×ˢ t₂`
and `(a₂, b₂) ∈ s₁ ×ˢ t₂ ∪ t₁ ×ˢ s₂`.

Using `LGame.mulOption`, this can alternatively be written as
`x * y = {mulOption x y a₁ b₁ | mulOption x y a₂ b₂}ᴵ`. -/
instance _root_.LGame.instMul : Mul LGame where
  mul x y := MulTy.toLGame LGame.leftMoves LGame.rightMoves LGame.leftMoves LGame.rightMoves
    (true, x, y)

theorem _root_.LGame.corec_mul_corec (initα : α) (initβ : β) :
    corec leftMovesα rightMovesα initα * corec leftMovesβ rightMovesβ initβ =
    corec
      (MulTy.leftMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      (MulTy.rightMoves leftMovesα rightMovesα leftMovesβ rightMovesβ)
      {(true, initα, initβ)} := by
  classical
  refine corec_comp_hom_apply
    (MulTy.map (corec leftMovesα rightMovesα) (corec leftMovesβ rightMovesβ)) ?_ ?_
    {(true, initα, initβ)}
  on_goal 1 => apply MulTy.leftMoves_comp_map
  on_goal 5 => apply MulTy.rightMoves_comp_map
  all_goals first | exact leftMoves_comp_corec .. | exact rightMoves_comp_corec ..

end MulTy

/-- The general option of `x * y` looks like `a * y + x * b - a * b`, for `a` and `b` options of
`x` and `y`, respectively. -/
@[pp_nodot]
def mulOption (x y a b : LGame) : LGame :=
  a * y + x * b - a * b

@[simp]
theorem leftMoves_mul (x y : LGame) :
    (x * y).leftMoves = (fun a ↦ mulOption x y a.1 a.2) ''
      (x.leftMoves ×ˢ y.leftMoves ∪ x.rightMoves ×ˢ y.rightMoves) := by
  apply (leftMoves_corec ..).trans
  simp [MulTy.leftMoves, MulTy.leftMovesSingle, MulTy.corec_mulOption, MulTy.toLGame, image_image]
  rfl

@[simp]
theorem rightMoves_mul (x y : LGame) :
    (x * y).rightMoves = (fun a ↦ mulOption x y a.1 a.2) ''
      (x.leftMoves ×ˢ y.rightMoves ∪ x.rightMoves ×ˢ y.leftMoves) := by
  apply (rightMoves_corec ..).trans
  simp [MulTy.rightMoves, MulTy.rightMovesSingle, MulTy.corec_mulOption, MulTy.toLGame, image_image]
  rfl

@[simp]
theorem leftMoves_mulOption (x y a b : LGame) :
    (mulOption x y a b).leftMoves = leftMoves (a * y + x * b - a * b) :=
  rfl

@[simp]
theorem rightMoves_mulOption (x y a b : LGame) :
    (mulOption x y a b).rightMoves = rightMoves (a * y + x * b - a * b) :=
  rfl

instance : MulZeroClass LGame where
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp

end LGame
