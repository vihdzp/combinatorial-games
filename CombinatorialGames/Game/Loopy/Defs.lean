/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Game.Functor
import CombinatorialGames.Mathlib.Small
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Small.Set

/-!
# Loopy Games

We define loopy games and prove some basic properties.
TODO: documentation
-/

open Set

universe u v w

noncomputable section

-- mathlib4 PR #27546
instance small_quot {α : Type u} [Small.{v} α] (r : α → α → Prop) : Small.{v} (Quot r) :=
  small_of_surjective Quot.mk_surjective
instance small_quotient {α : Type u} [Small.{v} α] (s : Setoid α) : Small.{v} (Quotient s) :=
  small_of_surjective Quotient.mk_surjective
instance (priority := 100) small_succ' (α : Type u) [Small.{v} α] : Small.{v + 1} α :=
  small_lift.{u, v + 1, v} α

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

/-! ### Game moves -/

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
  small_setOf_transGen' _ x

theorem eq_of_bisim (r : LGame → LGame → Prop)
    (hl : ∀ x y, r x y → ∃ e : leftMoves x ≃ leftMoves y, ∀ i, r i.1 (e i).1)
    (hr : ∀ x y, r x y → ∃ e : rightMoves x ≃ rightMoves y, ∀ i, r i.1 (e i).1)
    (x y : LGame.{u}) (hxy : r x y) : x = y := by
  refine QPF.Cofix.bisim r (fun x y hxy => ?_) x y hxy
  obtain ⟨el, hel⟩ := hl x y hxy
  obtain ⟨er, her⟩ := hr x y hxy
  refine ⟨⟨(range fun i ↦ ⟨(i.1, (el i).1), hel i⟩, range fun i ↦ ⟨(i.1, (er i).1), her i⟩),
    inferInstance, inferInstance⟩, ?_, ?_⟩
  all_goals simp_rw [GameFunctor.map_def, ← range_comp]
  · ext <;> simp <;> rfl
  · ext <;> simp [el.exists_congr_left, er.exists_congr_left] <;> rfl

@[ext]
protected theorem ext {x y : LGame.{u}}
    (hl : x.leftMoves = y.leftMoves) (hr : x.rightMoves = y.rightMoves) : x = y :=
  eq_of_bisim
    (fun i j => i.leftMoves = j.leftMoves ∧ i.rightMoves = j.rightMoves)
    (fun _ _ hij => hij.left ▸ ⟨.refl _, fun _ => ⟨rfl, rfl⟩⟩)
    (fun _ _ hij => hij.right ▸ ⟨.refl _, fun _ => ⟨rfl, rfl⟩⟩)
    x y ⟨hl, hr⟩

-- The default corecursion principle we get from `QPF` has type inconvenient universes, so we prove
-- a more general version.
section corec
variable {α : Type v}

private def IsReachable (leftMoves : α → Set α) (rightMoves : α → Set α) (init : α) (a : α) : Prop :=
  Relation.ReflTransGen (fun x y ↦ x ∈ leftMoves y ∪ rightMoves y) a init

variable (leftMoves : α → Set α) (rightMoves : α → Set α)
  [∀ a, Small.{u} (leftMoves a)] [∀ a, Small.{u} (rightMoves a)] (init : α)

private instance : Small.{u + 1} (Subtype (IsReachable leftMoves rightMoves init)) :=
  @small_lift.{_, u, u + 1} _ <| small_setOf_reflTransGen' ..

/-- Destructor for the subtype of reachable positions. -/
@[simp]
private def dest (x : Shrink (Subtype (IsReachable leftMoves rightMoves init))) :
    GameFunctor (Shrink (Subtype (IsReachable leftMoves rightMoves init))) :=
  have hx := ((equivShrink _).symm x).2
  ⟨⟨equivShrink _ '' range (inclusion fun _y hy ↦ .trans (.single (.inl hy)) hx),
    equivShrink _ '' range (inclusion fun _y hy ↦ .trans (.single (.inr hy)) hx)⟩,
    inferInstance, inferInstance⟩

private theorem unique (f g : Subtype (IsReachable leftMoves rightMoves init) → LGame.{u})
    (hf : QPF.Cofix.dest ∘ f ∘ (equivShrink _).symm =
      Functor.map (f ∘ (equivShrink _).symm) ∘ dest leftMoves rightMoves init)
    (hg : QPF.Cofix.dest ∘ g ∘ (equivShrink _).symm =
      Functor.map (g ∘ (equivShrink _).symm) ∘ dest leftMoves rightMoves init) (x) :
    f x = g x :=
  congrFun ((equivShrink _).symm.surjective.right_cancellable.1 <|
    QPF.Cofix.unique (dest leftMoves rightMoves init) _ _ hf hg) x

private noncomputable def corec' (x : Subtype (IsReachable leftMoves rightMoves init)) :=
  QPF.Cofix.corec (dest _ _ _) (equivShrink _ x)

noncomputable def corec : LGame.{u} :=
  corec' leftMoves rightMoves init ⟨_, .refl⟩

private theorem corec'_trans {x} (hx : IsReachable leftMoves rightMoves init x)
  (y : Subtype (IsReachable leftMoves rightMoves x)) :
    corec' _ _ x y = corec' _ _ init (inclusion (fun _z hz ↦ .trans hz hx) y) := by
  apply unique <;> ext <;>
    simp [← range_comp, corec', QPF.Cofix.dest_corec, GameFunctor.map_def]

private theorem corec'_aux {a} (ha : a ∈ leftMoves init ∪ rightMoves init) {x : LGame} :
    (∃ ha : IsReachable leftMoves rightMoves init a, corec' _ _ init ⟨a, ha⟩ = x) ↔
    corec leftMoves rightMoves a = x := by
  unfold corec
  constructor
  · rintro ⟨hx, rfl⟩
    simp [corec'_trans _ _ _ hx]
  · rintro rfl
    use .single ha
    simp [corec'_trans _ _ _ (.single ha)]

theorem leftMoves_corec : (corec leftMoves rightMoves init).leftMoves =
    corec leftMoves rightMoves '' leftMoves init := by
  rw [LGame.leftMoves, corec, corec', QPF.Cofix.dest_corec, GameFunctor.map_def]
  ext f
  simpa [← (equivShrink (Subtype (IsReachable _ _ _))).exists_congr_right]
    using exists_congr fun a ↦ and_congr_right fun ha ↦ corec'_aux _ _ _ (.inl ha)

theorem rightMoves_corec : (corec leftMoves rightMoves init).rightMoves =
    corec leftMoves rightMoves '' rightMoves init := by
  rw [LGame.rightMoves, corec, corec', QPF.Cofix.dest_corec, GameFunctor.map_def]
  ext f
  simpa [← (equivShrink (Subtype (IsReachable _ _ _))).exists_congr_right]
    using exists_congr fun a ↦ and_congr_right fun ha ↦ corec'_aux _ _ _ (.inr ha)

theorem leftMoves_comp_corec :
    LGame.leftMoves ∘ corec leftMoves rightMoves = image (corec leftMoves rightMoves) ∘ leftMoves :=
  funext (leftMoves_corec leftMoves rightMoves)

theorem rightMoves_comp_corec :
    LGame.rightMoves ∘ corec leftMoves rightMoves = image (corec leftMoves rightMoves) ∘ rightMoves :=
  funext (rightMoves_corec leftMoves rightMoves)

theorem hom_unique {α : Type v} (leftMoves : α → Set α) (rightMoves : α → Set α)
    [∀ a, Small.{u} (leftMoves a)] [∀ a, Small.{u} (rightMoves a)] (f g : α → LGame.{u})
    (fLeftMoves : LGame.leftMoves ∘ f = image f ∘ leftMoves)
    (fRightMoves : LGame.rightMoves ∘ f = image f ∘ rightMoves)
    (gLeftMoves : LGame.leftMoves ∘ g = image g ∘ leftMoves)
    (gRightMoves : LGame.rightMoves ∘ g = image g ∘ rightMoves) : f = g := by
  funext x
  change (f ∘ Subtype.val) (⟨x, .refl⟩ : Subtype (IsReachable leftMoves rightMoves x)) =
    (g ∘ Subtype.val) (⟨x, .refl⟩ : Subtype (IsReachable leftMoves rightMoves x))
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

end corec

theorem corec_comp_hom {α : Type v} {β : Type w}
    (leftMovesα : α → Set α) (rightMovesα : α → Set α)
    (leftMovesβ : β → Set β) (rightMovesβ : β → Set β)
    [∀ a, Small.{u} (leftMovesα a)] [∀ a, Small.{u} (rightMovesα a)]
    [∀ b, Small.{u} (leftMovesβ b)] [∀ b, Small.{u} (rightMovesβ b)]
    (f : α → β)
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

noncomputable def ofSets (l : Set LGame.{u}) (r : Set LGame.{u})
    [Small.{u} l] [Small.{u} r] : LGame.{u} :=
  @corec (Option LGame.{u})
    (Option.elim · (some '' l) (some '' leftMoves ·))
    (Option.elim · (some '' r) (some '' rightMoves ·))
    (by
      simp only [Option.forall, Option.elim_none, Option.elim_some]
      exact ⟨inferInstance, inferInstance⟩)
    (by
      simp only [Option.forall, Option.elim_none, Option.elim_some]
      exact ⟨inferInstance, inferInstance⟩)
    none

theorem leftMoves_ofSets (l : Set LGame.{u}) (r : Set LGame.{u})
    [Small.{u} l] [Small.{u} r] : (ofSets l r).leftMoves = l := by
  rw [ofSets]
  generalize_proofs hl hr
  rw [leftMoves_corec, Option.elim_none, Set.image_image]
  refine Eq.trans ?_ (Set.image_id l)
  apply congrFun
  apply congrArg Set.image
  rw [← corec_leftMoves_rightMoves]
  exact corec_comp_hom
    leftMoves rightMoves
    (Option.elim · (some '' l) (some '' leftMoves ·))
    (Option.elim · (some '' r) (some '' rightMoves ·))
    some rfl rfl

theorem rightMoves_ofSets (l : Set LGame.{u}) (r : Set LGame.{u})
    [Small.{u} l] [Small.{u} r] : (ofSets l r).rightMoves = r := by
  rw [ofSets]
  generalize_proofs hl hr
  rw [rightMoves_corec, Option.elim_none, Set.image_image]
  refine Eq.trans ?_ (Set.image_id r)
  apply congrFun
  apply congrArg Set.image
  rw [← corec_leftMoves_rightMoves]
  exact corec_comp_hom
    leftMoves rightMoves
    (Option.elim · (some '' l) (some '' leftMoves ·))
    (Option.elim · (some '' r) (some '' rightMoves ·))
    some rfl rfl

end LGame
