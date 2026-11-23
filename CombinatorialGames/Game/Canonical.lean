/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid, Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Game.Birthday

/-!
# Canonical games

This file defines functions for hereditarily removing all dominated and reversible positions from a
game, and uses them to define the canonical (or simplest) form of a short game.

## Dominated moves

Let `x` be a game. We say that `y ∈ xᴸ` is dominated by `z ∈ xᴸ` if `y < z`. Intuitively, Left will
always prefer moving to `z` than to `y`, so we can completely ignore `y`. Dominated moves for Right
are defined analogously.

We define `undominate x` by hereditarily removing all dominated positions, and prove
`undominate x ≈ x` for any **short** game. See `undominate_equiv`.

Note that the short hypothesis is indispensible, since e.g. `undominate ω = 0`.

## Reversible moves

Let `x` be a game. We say that `y ∈ xᴸ` is reversible through `z ∈ yᴿ` if `z ≤ x`. Intuitively,
after Left moves to `y`, Right can revert all their progress by moving to `z`, so they might as
well do this. Reversible moves for Right are defined analogously.

## Todo

Define `unreverse` and prove `unreverse x ≈ x` for **any** game.
-/

public noncomputable section

namespace IGame

/-! ### Undominating games -/

/-- A hereditarily undominated game is one where no move is dominated, and such that every
subposition satisfies this same property. -/
def IsUndominated (x : IGame) : Prop :=
  ∀ p, ∀ y ∈ x.moves p, IsUndominated y ∧ ∀ z ∈ x.moves p, ¬p.cases (· < ·) (· > ·) y z
termination_by x
decreasing_by igame_wf

theorem isUndominated_def {x : IGame} : IsUndominated x ↔
    ∀ p, ∀ y ∈ x.moves p, IsUndominated y ∧ ∀ z ∈ x.moves p, ¬p.cases (· < ·) (· > ·) y z := by
  rw [IsUndominated]

namespace IsUndominated

theorem of_mem_moves {x y : IGame} {p : Player} (hy : y ∈ x.moves p) (h : IsUndominated x) :
    IsUndominated y := by
  rw [isUndominated_def] at h
  exact (h p y hy).1

theorem not_lt_of_mem_moves {x y z : IGame} {p : Player} (h : IsUndominated x)
    (hy : y ∈ x.moves p) (hz : z ∈ x.moves p) : ¬p.cases (· < ·) (· > ·) y z := by
  rw [isUndominated_def] at h
  exact (h p y hy).2 z hz

theorem not_lt_of_mem_moves_left {x y z : IGame} (h : IsUndominated x)
    (hy : y ∈ xᴸ) (hz : z ∈ xᴸ) : ¬y < z :=
  not_lt_of_mem_moves h hy hz

theorem not_lt_of_mem_moves_right {x y z : IGame} (h : IsUndominated x)
    (hy : y ∈ xᴿ) (hz : z ∈ xᴿ) : ¬z < y :=
  not_lt_of_mem_moves h hy hz

end IsUndominated

/-- Hereditarily undominating a game. This returns garbage values on non-short games. -/
def undominate (x : IGame) : IGame :=
  !{fun p ↦ {y ∈ Set.range fun z : x.moves p ↦ undominate z |
    ∀ z ∈ x.moves p, ¬p.cases (· < ·) (· > ·) y z}}
termination_by x
decreasing_by igame_wf

theorem undominate_def' (x : IGame) : x.undominate =
    !{fun p ↦ {y ∈ undominate '' x.moves p | ∀ z ∈ x.moves p, ¬p.cases (· < ·) (· > ·) y z}} := by
  rw [undominate]
  simp

theorem undominate_def (x : IGame) : x.undominate =
    !{{y ∈ undominate '' xᴸ | ∀ z ∈ xᴸ, ¬y < z} | {y ∈ undominate '' xᴿ | ∀ z ∈ xᴿ, ¬z < y}} := by
  rw [undominate_def', ofSets_eq_ofSets_cases]

@[simp]
theorem forall_mem_moves_undominate {x : IGame} {p : Player} {P : IGame → Prop} :
    (∀ y ∈ x.undominate.moves p, P y) ↔
      ∀ y ∈ x.moves p, (∀ z ∈ x.moves p, ¬p.cases (· < ·) (· > ·) y.undominate z) →
        P y.undominate := by
  rw [undominate_def']
  simp

@[simp]
theorem exists_mem_moves_undominate {x : IGame} {p : Player} {P : IGame → Prop} :
    (∃ y ∈ x.undominate.moves p, P y) ↔
      ∃ y ∈ x.moves p, (∀ z ∈ x.moves p, ¬p.cases (· < ·) (· > ·) y.undominate z) ∧
        P y.undominate := by
  rw [undominate_def']
  aesop

/-- Every move of `x.undominate` is itself undominated. -/
theorem moves_undominate_subset_range (x : IGame) (p : Player) :
    x.undominate.moves p ⊆ .range undominate := by
  rw [Set.subset_def, forall_mem_moves_undominate]
  simp

theorem undominate_mem_moves_undominate' {x y : IGame} {p : Player} (hy : y ∈ x.moves p)
    (H : ∀ z ∈ x.moves p, ¬p.cases (· < ·) (· > ·) y.undominate z) :
    y.undominate ∈ x.undominate.moves p := by
  rw [undominate_def', moves_ofSets]
  exact ⟨Set.mem_image_of_mem _ hy, H⟩

theorem not_lt_of_mem_moves_undominate {x y z : IGame} {p : Player}
    (hy : y ∈ x.undominate.moves p) (hz : z ∈ x.moves p) : ¬p.cases (· < ·) (· > ·) y z := by
  rw [undominate_def', moves_ofSets] at hy
  obtain ⟨⟨y, hy, rfl⟩, Hy⟩ := hy
  exact Hy _ hz

theorem not_lt_of_mem_moves_left_undominate {x y z : IGame}
    (hy : y ∈ x.undominateᴸ) (hz : z ∈ xᴸ) : ¬ y < z :=
  not_lt_of_mem_moves_undominate hy hz

theorem not_lt_of_mem_moves_right_undominate {x y z : IGame}
    (hy : y ∈ x.undominateᴿ) (hz : z ∈ xᴿ) : ¬ z < y :=
  not_lt_of_mem_moves_undominate hy hz

theorem birthday_undominate_le (x : IGame) : x.undominate.birthday ≤ x.birthday := by
  simp_rw [birthday_le_iff, forall_mem_moves_undominate]
  exact fun p y hy _ ↦ (birthday_undominate_le y).trans_lt <| birthday_lt_of_mem_moves hy
termination_by x
decreasing_by igame_wf

instance {x : IGame} [hx : Short x] : Short (undominate x) := by
  rw [short_iff_birthday_finite] at hx ⊢
  exact (birthday_undominate_le x).trans_lt hx

@[simp]
theorem undominate_neg (x : IGame) : (-x).undominate = -x.undominate := by
  have := fun p ↦ moves_neg p x ▸ Set.image_neg_of_apply_neg_eq_neg fun y _ ↦ undominate_neg y
  rw [undominate_def, undominate_def, neg_ofSets]
  simp_rw [this]
  simp_all [IGame.lt_neg, IGame.neg_lt]
termination_by x
decreasing_by igame_wf

private theorem le_undominate (x : IGame) [Short x] : x ≤ undominate x := by
  rw [le_iff_forall_lf]
  simp_rw [forall_mem_moves_undominate]
  dsimp
  refine ⟨fun y hy ↦ ?_, fun y hy _ hyx ↦ ?_⟩
  · obtain ⟨z, ⟨hyz, ⟨hz, hz'⟩⟩⟩ := (Short.finite_moves _ x).exists_le_maximal hy
    short
    have IH := le_undominate z
    refine fun hxy ↦ lf_of_le_left IH (undominate_mem_moves_undominate' hz fun w hw hzw ↦ ?_)
      (hxy.trans hyz)
    grw [Player.cases, ← IH] at hzw
    exact hzw.not_ge (hz' hw hzw.le)
  · short
    grw [← le_undominate y] at hyx
    exact lf_right hy hyx
termination_by x
decreasing_by igame_wf

theorem undominate_equiv (x : IGame) [Short x] : undominate x ≈ x :=
  ⟨by simpa using le_undominate (-x), le_undominate x⟩

theorem undominate_mem_moves_undominate {x y : IGame} {p : Player} [Short x] (hy : y ∈ x.moves p)
    (H : ∀ z ∈ x.moves p, ¬p.cases (· < ·) (· > ·) y z) :
    y.undominate ∈ x.undominate.moves p := by
  refine undominate_mem_moves_undominate' hy fun z hz ↦ ?_
  short
  cases p <;>
  · dsimp
    grw [undominate_equiv]
    exact H z hz

theorem IsUndominated.undominate (x : IGame) [Short x] : IsUndominated x.undominate := by
  rw [isUndominated_def]
  simp_rw [forall_mem_moves_undominate]
  intro p y hy Hy
  short
  refine ⟨.undominate y, fun z hz _ ↦ ?_⟩
  short
  cases p <;>
  · dsimp
    grw [undominate_equiv z]
    exact Hy _ hz
termination_by x
decreasing_by igame_wf

theorem IsUndominated.undominate_eq {x : IGame} (hx : IsUndominated x) : x.undominate = x := by
  ext p y
  rw [undominate_def', moves_ofSets]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, Hy⟩
    rwa [(hx.of_mem_moves hy).undominate_eq]
  · exact fun hy ↦ ⟨⟨y, hy, (hx.of_mem_moves hy).undominate_eq⟩, fun z ↦ hx.not_lt_of_mem_moves hy⟩
termination_by x
decreasing_by igame_wf

theorem isUndominated_iff_undominate_eq {x : IGame} [Short x] :
    IsUndominated x ↔ x.undominate = x := by
  refine ⟨IsUndominated.undominate_eq, fun hx ↦ ?_⟩
  rw [← hx]
  exact .undominate x

@[simp]
theorem undominate_undominate (x : IGame) [Short x] : x.undominate.undominate = x.undominate :=
  (IsUndominated.undominate x).undominate_eq

end IGame
end
