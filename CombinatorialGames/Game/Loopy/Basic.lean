/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.IGame
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

theorem corec_comp_hom
    {leftMovesα rightMovesα : α → Set α} {leftMovesβ rightMovesβ : β → Set β}
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
  hom_unique leftMoves rightMoves _ _
    (leftMoves_comp_corec leftMoves rightMoves)
    (rightMoves_comp_corec leftMoves rightMoves)
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

@[simp]
theorem neg_corec (leftMoves rightMoves : α → Set α)
    [∀ x, Small.{u} (leftMoves x)] [∀ x, Small.{u} (rightMoves x)] (init : α) :
    -corec leftMoves rightMoves init = corec rightMoves leftMoves init :=
  corec_comp_hom_apply _ (rightMoves_comp_corec ..)  (leftMoves_comp_corec ..) _

instance : InvolutiveNeg LGame where
  neg_neg x := (neg_corec ..).trans (congrFun (corec_leftMoves_rightMoves ..) x)

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

@[simp] theorem neg_on : -on = off := neg_corec ..
@[simp] theorem neg_off : -off = on := neg_corec ..
@[simp] theorem neg_dud : -dud = dud := neg_corec ..

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
    (f := Prod.map (corec leftMovesα rightMovesα) (corec leftMovesβ rightMovesβ)) ?_ ?_
    (initα, initβ)
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

/-- The subtraction of `x` and `y` is defined as `x + (-y)`. -/
instance : SubNegMonoid LGame where
  zsmul := zsmulRec

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

end LGame
