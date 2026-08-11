/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
module

public import CombinatorialGames.Game.Birthday

/-!
# Canonical games

For any game G, its canonical game G' is the unique IGame game with
smallest birthday such that G'.Fits G.
From the literature, this file provides an explicit (though noncomputable) construction of canonical
games through undominating and unreversing games.

## Todo

- Define (un)reversibility
-/

universe u

public noncomputable section

section ForMathlib
open Set

variable {α : Type*} {ι : Sort*} {κ : ι → Sort*}

-- mathlib PR #42549
theorem forall_mem_iUnion {p : α → Prop} {f : ι → Set α} :
    (∀ x ∈ ⋃ i, f i, p x) ↔ (∀ i, ∀ x ∈ f i, p x) := by
  simp_rw [mem_iUnion, forall_exists_index]
  apply forall_comm

-- mathlib PR #42549
theorem forall_mem_iUnion₂ {p : α → Prop} {f : (i : ι) → κ i → Set α} :
    (∀ x ∈ ⋃ (i) (j), f i j, p x) ↔ (∀ i j, ∀ x ∈ f i j, p x) := by
  simp_rw [forall_mem_iUnion]

-- mathlib PR #42549
theorem forall_mem_biUnion {p : α → Prop} {f : ι → Set α} {q : ι → Prop} :
    (∀ x ∈ ⋃ (i : ι) (_ : q i), f i, p x) ↔ (∀ i, q i → ∀ x ∈ f i, p x) :=
  forall_mem_iUnion₂

end ForMathlib

namespace IGame

def reverseSet (x : IGame) (p : Player) (z : IGame) : Set IGame :=
  {g | g ∈ z.moves (-p) ∧ p.cases (g ≤ x) (x ≤ g)}

instance (x : IGame.{u}) (p : Player) (z : IGame.{u}) : Small.{u} (reverseSet x p z) := by
  unfold reverseSet
  infer_instance

-- false positive on `hg` which is referenced in the termination proof
set_option linter.unusedVariables false in
def unreverse1 (x : IGame) (p : Player) (z : IGame) : Set IGame :=
  open scoped Classical in
  if reverseSet x p z = ∅ then {z} else
  ⋃ (g) (hg : g ∈ reverseSet x p z) (g') (hg' : g' ∈ g.moves p), unreverse1 x p g'
termination_by z
decreasing_by exact .trans (.of_mem_moves hg') (.of_mem_moves hg.1)

instance (x : IGame.{u}) (p : Player) (z : IGame.{u}) : Small.{u} (unreverse1 x p z) := by
  fun_induction unreverse1 x p z with
  | case1 => infer_instance
  | case2 z _ ih =>
    exact @small_biUnion _ _ (reverseSet x p z) _ _ fun g hg =>
      @small_biUnion _ _ (g.moves p) _ _ (ih g hg)

theorem lf_of_mem_reverseSet_of_mem_unreverse1
    (x : IGame) (p : Player) (z : IGame) {g g' c : IGame}
    (hg : g ∈ reverseSet x p z) (hg' : g' ∈ g.moves p) (hc : c ∈ unreverse1 x p g') :
    ¬p.cases (x ≤ c) (c ≤ x) := by
  induction z using subposition_wf.induction generalizing g g' with | _ z ih
  unfold unreverse1 at hc
  by_cases hx : reverseSet x p g' = ∅
  · rw [if_pos hx, Set.mem_singleton_iff] at hc
    rw [hc]
    cases p with
    | left => exact fun h => left_lf hg' (hg.2.trans h)
    | right => exact fun h => lf_right hg' (h.trans hg.2)
  · rw [if_neg hx] at hc
    simp_rw [Set.mem_iUnion] at hc
    obtain ⟨g'', hg'', g''', hg''', hc⟩ := hc
    exact ih g' (.trans (.of_mem_moves hg') (.of_mem_moves hg.1)) hg'' hg''' hc

theorem lf_of_mem_moves_of_mem_unreverse1
    (x : IGame) (p : Player) (z : IGame) {g : IGame}
    (hz : z ∈ x.moves p) (hg : g ∈ unreverse1 x p z) :
    ¬p.cases (x ≤ g) (g ≤ x) := by
  unfold unreverse1 at hg
  by_cases hx : reverseSet x p z = ∅
  · rw [if_pos hx, Set.mem_singleton_iff] at hg
    rw [hg]
    cases p with
    | left => exact left_lf hz
    | right => exact lf_right hz
  · rw [if_neg hx] at hg
    simp_rw [Set.mem_iUnion] at hg
    obtain ⟨g', hg', g'', hg'', hg⟩ := hg
    exact lf_of_mem_reverseSet_of_mem_unreverse1 x p z hg' hg'' hg

private theorem unreverse_equiv_aux_left (x : IGame) :
    x ≈ !{⋃ z : xᴸ, unreverse1 x left z | xᴿ} := by
  apply equiv_of_forall_lf
  · intro z hz
    replace hz : unreverse1 x left z ⊆ ⋃ z : xᴸ, unreverse1 x left z :=
      Set.subset_iUnion (fun z : xᴸ => unreverse1 x left z) ⟨z, hz⟩
    induction z using subposition_wf.induction with | _ z ih
    by_cases hx : reverseSet x left z = ∅
    · apply left_lf
      rw [leftMoves_ofSets]
      apply hz
      unfold unreverse1
      simp [hx]
    · obtain ⟨g, hg⟩ : (reverseSet x left z).Nonempty := Set.nonempty_iff_ne_empty.2 hx
      refine lf_of_right_le (le_iff_forall_lf.2 ⟨?_, ?_⟩) hg.1
      · intro g' hg'
        refine ih g' (.trans (.of_mem_moves hg') (.of_mem_moves hg.1)) (subset_trans ?_ hz)
        conv_rhs => unfold unreverse1
        rw [if_neg hx]
        exact Set.subset_iUnion₂_of_subset g hg (Set.subset_biUnion_of_mem hg')
      · rw [rightMoves_ofSets]
        intro g' hg'
        exact fun h => lf_right hg' (h.trans hg.2)
  · intro z hz
    apply lf_right
    rw [rightMoves_ofSets]
    exact hz
  · rw [leftMoves_ofSets, forall_mem_iUnion, Subtype.forall]
    intro z hz g hg
    exact lf_of_mem_moves_of_mem_unreverse1 x left z hz hg
  · rw [rightMoves_ofSets]
    intro z hz
    exact lf_right hz

private theorem unreverse_equiv_aux_right (x : IGame) :
    x ≈ !{xᴸ | ⋃ z : xᴿ, unreverse1 x right z} := by
  rw [← neg_equiv_neg_iff, neg_ofSets, neg_eq]
  stop
  -- refine @unreverse_equiv_aux_left !{-xᴿ | -xᴸ}
  · simpa [← neg_ofSets] using hbb
  · simpa using hdl
  · simpa [neg_subset, neg_range] using hu
  · simpa [neg_eq_iff_eq_neg] using hv

def unreverse (x : IGame) : IGame :=
  !{fun p => ⋃ z : x.moves p, unreverse1 x p (unreverse z)}
termination_by x
decreasing_by igame_wf

/-- Undominating a game. This returns garbage values on non-short games -/
def undominate (x : IGame) : IGame :=
  !{{y ∈ Set.range fun z : xᴸ ↦ undominate z | ∀ z ∈ xᴸ, ¬y < z} |
    {y ∈ Set.range fun z : xᴿ ↦ undominate z | ∀ z ∈ xᴿ, ¬z < y}}
termination_by x
decreasing_by igame_wf

theorem birthday_undominate_le (x : IGame) : x.undominate.birthday ≤ x.birthday := by
  rw [undominate, birthday_le_iff]
  have (p w) (hw : w ∈ x.moves p) :=
    (birthday_undominate_le w).trans_lt (birthday_lt_of_mem_moves hw)
  aesop
termination_by x
decreasing_by igame_wf

theorem undominate_def {x : IGame} : x.undominate =
    !{{y ∈ undominate '' xᴸ | ∀ z ∈ xᴸ, ¬y < z} |
      {y ∈ undominate '' xᴿ | ∀ z ∈ xᴿ, ¬z < y}} := by
  rw [undominate]
  simp

@[simp]
theorem leftMoves_undominate {x : IGame} :
    x.undominateᴸ = {y ∈ undominate '' xᴸ | ∀ z ∈ xᴸ, ¬y < z} := by
  rw [undominate_def]
  exact leftMoves_ofSets ..

@[simp]
theorem rightMoves_undominate {x : IGame} :
    x.undominateᴿ = {y ∈ undominate '' xᴿ | ∀ z ∈ xᴿ, ¬z < y} := by
  rw [undominate_def]
  exact rightMoves_ofSets ..

instance {x : IGame} [hx : Short x] : Short (undominate x) := by
  rw [short_iff_birthday_finite] at hx ⊢
  exact (birthday_undominate_le x).trans_lt hx

@[simp]
theorem undominate_neg (x : IGame) : (-x).undominate = -x.undominate := by
  have := fun p ↦ moves_neg p x ▸ Set.image_neg_of_apply_neg_eq_neg fun y _ ↦ undominate_neg y
  rw [undominate_def, undominate_def]
  simp_all [IGame.lt_neg, IGame.neg_lt]
termination_by x
decreasing_by igame_wf

private theorem le_undominate (x : IGame) [Short x] : x ≤ undominate x := by
  rw [le_def, leftMoves_undominate, rightMoves_undominate]
  refine ⟨fun y hy ↦ ?_, ?_⟩
  · obtain ⟨z, ⟨hyz, ⟨hz, hz'⟩⟩⟩ := (Short.finite_moves _ x).exists_le_maximal hy
    short
    have IH := le_undominate z
    refine .inl ⟨_, ⟨⟨Set.mem_image_of_mem _ hz, fun a ha h ↦ ?_⟩, hyz.trans IH⟩⟩
    replace h := IH.trans_lt h
    exact (hz' ha h.le).not_gt h
  · rintro y ⟨⟨z, ⟨hz, rfl⟩⟩, _⟩
    short
    exact .inr ⟨z, hz, le_undominate z⟩
termination_by x
decreasing_by igame_wf

theorem undominate_equiv (x : IGame) [Short x] : undominate x ≈ x :=
  ⟨by simpa using le_undominate (-x), le_undominate x⟩

end IGame
end
