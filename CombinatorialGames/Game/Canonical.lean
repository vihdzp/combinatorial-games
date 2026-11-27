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
  ∀ p, ∀ y ∈ x.moves p, IsUndominated y ∧ ∀ z ∈ x.moves p, ¬p.LT y z
termination_by x
decreasing_by igame_wf

theorem isUndominated_def {x : IGame} : IsUndominated x ↔
    ∀ p, ∀ y ∈ x.moves p, IsUndominated y ∧ ∀ z ∈ x.moves p, ¬p.LT y z := by
  rw [IsUndominated]

namespace IsUndominated

theorem of_mem_moves {x y : IGame} {p : Player} (hy : y ∈ x.moves p) (h : IsUndominated x) :
    IsUndominated y := by
  rw [isUndominated_def] at h
  exact (h p y hy).1

theorem not_lt_of_mem_moves {x y z : IGame} {p : Player} (h : IsUndominated x)
    (hy : y ∈ x.moves p) (hz : z ∈ x.moves p) : ¬p.LT y z := by
  rw [isUndominated_def] at h
  exact (h p y hy).2 z hz

theorem not_lt_of_mem_moves_left {x y z : IGame} (h : IsUndominated x)
    (hy : y ∈ xᴸ) (hz : z ∈ xᴸ) : ¬y < z :=
  not_lt_of_mem_moves h hy hz

theorem not_lt_of_mem_moves_right {x y z : IGame} (h : IsUndominated x)
    (hy : y ∈ xᴿ) (hz : z ∈ xᴿ) : ¬z < y :=
  not_lt_of_mem_moves h hy hz

protected theorem neg {x : IGame} (hx : IsUndominated x) : IsUndominated (-x) := by
  rw [isUndominated_def]
  simp_rw [forall_mem_moves_neg]
  refine fun p y hy ↦ ⟨.neg (.of_mem_moves hy hx), fun z hz ↦ ?_⟩
  simpa using hx.not_lt_of_mem_moves hy hz
termination_by x
decreasing_by igame_wf

@[simp]
theorem neg_iff {x : IGame} : IsUndominated (-x) ↔ IsUndominated x :=
  ⟨by simpa using IsUndominated.neg (x := -x), .neg⟩

@[simp]
protected theorem natCast (n : ℕ) : IsUndominated n := by
  rw [isUndominated_def]
  intro p y hy
  obtain ⟨m, hm, rfl⟩ := eq_natCast_of_mem_moves_natCast hy
  refine ⟨.natCast m, fun z hz ↦ ?_⟩
  rw [subsingleton_moves_natCast hy hz]
  cases p <;> exact lt_irrefl z

@[simp]
protected theorem intCast (n : ℤ) : IsUndominated n := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp

protected theorem zero : IsUndominated 0 := by
  simpa using IsUndominated.natCast 0

@[simp]
protected theorem one : IsUndominated 1 := by
  simpa using IsUndominated.natCast 1

@[simp]
protected theorem half : IsUndominated half := by
  rw [isUndominated_def]
  simpa using IsUndominated.zero

@[simp]
protected theorem _root_.IGame.WeaklyImpartial.isUndominated (x : IGame) [WeaklyImpartial x] :
    IsUndominated x := by
  rw [isUndominated_def]
  intro p y hy
  weakly_impartial
  refine ⟨WeaklyImpartial.isUndominated y, fun z hz ↦ ?_⟩
  weakly_impartial
  cases p <;> simp
termination_by x
decreasing_by igame_wf

end IsUndominated

/-- Hereditarily undominating a game. This returns garbage values on non-short games. -/
def undominate (x : IGame) : IGame :=
  !{fun p ↦ {y ∈ Set.range fun z : x.moves p ↦ undominate z |
    ∀ z ∈ x.moves p, ¬p.LT y (undominate z)}}
termination_by x
decreasing_by igame_wf

theorem undominate_def' (x : IGame) : x.undominate =
    !{fun p ↦ {y ∈ undominate '' x.moves p | ∀ z ∈ x.moves p, ¬p.LT y (undominate z)}} := by
  rw [undominate]
  simp

theorem undominate_def (x : IGame) : x.undominate =
    !{{y ∈ undominate '' xᴸ | ∀ z ∈ xᴸ, ¬y < undominate z} |
      {y ∈ undominate '' xᴿ | ∀ z ∈ xᴿ, ¬undominate z < y}} := by
  rw [undominate_def', ofSets_eq_ofSets_cases]

theorem moves_undominate (x : IGame) (p : Player) : x.undominate.moves p =
    {y ∈ undominate '' x.moves p | ∀ z ∈ x.moves p, ¬p.LT y (undominate z)} := by
  rw [undominate_def', moves_ofSets]

theorem moves_left_undominate (x : IGame) : x.undominateᴸ =
    {y ∈ undominate '' xᴸ | ∀ z ∈ xᴸ, ¬y < undominate z} :=
  moves_undominate ..

theorem moves_right_undominate (x : IGame) : x.undominateᴿ =
    {y ∈ undominate '' xᴿ | ∀ z ∈ xᴿ, ¬undominate z < y} :=
  moves_undominate ..

@[simp]
theorem forall_mem_moves_undominate {x : IGame} {p : Player} {P : IGame → Prop} :
    (∀ y ∈ x.undominate.moves p, P y) ↔
      ∀ y ∈ x.moves p, (∀ z ∈ x.moves p, ¬p.LT y.undominate z.undominate) → P y.undominate := by
  rw [undominate_def']
  simp

@[simp]
theorem exists_mem_moves_undominate {x : IGame} {p : Player} {P : IGame → Prop} :
    (∃ y ∈ x.undominate.moves p, P y) ↔
      ∃ y ∈ x.moves p, (∀ z ∈ x.moves p, ¬p.LT y.undominate z.undominate) ∧ P y.undominate := by
  rw [undominate_def']
  aesop

/-- See `undominate_mem_moves_undominate` for a specialization to short games. -/
theorem undominate_mem_moves_undominate' {x y : IGame} {p : Player} (hy : y ∈ x.moves p)
    (H : ∀ z ∈ x.moves p, ¬p.LT y.undominate z.undominate) :
    y.undominate ∈ x.undominate.moves p := by
  rw [undominate_def', moves_ofSets]
  exact ⟨Set.mem_image_of_mem _ hy, H⟩

/-- See `not_lt_of_mem_moves_undominate` for a specialization to short games. -/
theorem not_lt_of_mem_moves_undominate' {x y z : IGame} {p : Player}
    (hy : y ∈ x.undominate.moves p) (hz : z ∈ x.moves p) : ¬p.LT y z.undominate := by
  rw [undominate_def', moves_ofSets] at hy
  obtain ⟨⟨y, hy, rfl⟩, Hy⟩ := hy
  exact Hy _ hz

/-- See `not_lt_of_mem_moves_left_undominate` for a specialization to short games. -/
theorem not_lt_of_mem_moves_left_undominate' {x y z : IGame}
    (hy : y ∈ x.undominateᴸ) (hz : z ∈ xᴸ) : ¬ y < z.undominate :=
  not_lt_of_mem_moves_undominate' hy hz

/-- See `not_lt_of_mem_moves_right_undominate` for a specialization to short games. -/
theorem not_lt_of_mem_moves_right_undominate' {x y z : IGame}
    (hy : y ∈ x.undominateᴿ) (hz : z ∈ xᴿ) : ¬ z.undominate < y :=
  not_lt_of_mem_moves_undominate' hy hz

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
  simp_rw [this, moves_neg, Set.mem_neg, Set.forall_neg_mem]
  dsimp
  congr! 7 with y z hz
  · rw [undominate_neg, IGame.lt_neg]
  · rw [undominate_neg, IGame.neg_lt]
termination_by x
decreasing_by igame_wf

theorem undominate_equiv (x : IGame) [Short x] : undominate x ≈ x := by
  refine equiv_of_forall_lf ?_ ?_ (fun y hy hxy ↦ ?_) (fun y hy hxy ↦ ?_)
  · simp_rw [forall_mem_moves_undominate]
    dsimp [Player.LT]
    refine fun y hy _ hyx ↦ ?_
    short
    grw [undominate_equiv] at hyx
    exact left_lf hy hyx
  · simp_rw [forall_mem_moves_undominate]
    dsimp [Player.LT]
    refine fun y hy _ hyx ↦ ?_
    short
    grw [undominate_equiv y] at hyx
    exact lf_right hy hyx
  · obtain ⟨z, ⟨hyz, ⟨hz, hz'⟩⟩⟩ := (Short.finite_moves _ x).exists_le_maximal hy
    short
    have IHz := undominate_equiv z
    refine lf_of_le_left IHz.ge (undominate_mem_moves_undominate' hz fun w hw hzw ↦ ?_)
      (hxy.trans hyz)
    short
    grw [Player.left_lt, IHz, undominate_equiv w] at hzw
    exact hzw.not_ge (hz' hw hzw.le)
  · obtain ⟨z, ⟨hyz, ⟨hz, hz'⟩⟩⟩ := (Short.finite_moves _ x).exists_le_minimal hy
    short
    have IHz := undominate_equiv z
    refine lf_of_right_le IHz.le (undominate_mem_moves_undominate' hz fun w hw hzw ↦ ?_)
      (hyz.trans hxy)
    short
    grw [Player.left_lt, IHz, undominate_equiv w] at hzw
    exact hzw.not_ge (hz' hw hzw.le)
termination_by x
decreasing_by igame_wf

theorem undominate_mem_moves_undominate {x y : IGame} {p : Player} [Short x] (hy : y ∈ x.moves p)
    (H : ∀ z ∈ x.moves p, ¬p.LT y z) : y.undominate ∈ x.undominate.moves p := by
  refine undominate_mem_moves_undominate' hy fun z hz ↦ ?_
  short
  rw [Player.lt_congr (undominate_equiv y) (undominate_equiv z)]
  exact H z hz

theorem not_lt_of_mem_moves_undominate {x y z : IGame} {p : Player} [Short x]
    (hy : y ∈ x.undominate.moves p) (hz : z ∈ x.moves p) : ¬p.LT y z := by
  short
  rw [← Player.lt_congr_right (undominate_equiv z)]
  exact not_lt_of_mem_moves_undominate' hy hz

theorem not_lt_of_mem_moves_left_undominate {x y z : IGame} [Short x]
    (hy : y ∈ x.undominateᴸ) (hz : z ∈ xᴸ) : ¬ y < z :=
  not_lt_of_mem_moves_undominate hy hz

theorem not_lt_of_mem_moves_right_undominate {x y z : IGame} [Short x]
    (hy : y ∈ x.undominateᴿ) (hz : z ∈ xᴿ) : ¬ z < y :=
  not_lt_of_mem_moves_undominate hy hz

@[simp]
theorem IsUndominated.undominate (x : IGame) : IsUndominated x.undominate := by
  rw [isUndominated_def]
  simp_rw [forall_mem_moves_undominate]
  exact fun p y _ hy => ⟨.undominate y, fun z hz _ ↦ hy z hz⟩
termination_by x
decreasing_by igame_wf

@[simp]
theorem IsUndominated.undominate_eq {x : IGame} (hx : IsUndominated x) : x.undominate = x := by
  ext p y
  rw [undominate_def', moves_ofSets]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, Hy⟩
    rwa [(hx.of_mem_moves hy).undominate_eq]
  · refine fun hy ↦ ⟨⟨y, hy, (hx.of_mem_moves hy).undominate_eq⟩, fun z hz ↦ ?_⟩
    rw [(hx.of_mem_moves hz).undominate_eq]
    exact hx.not_lt_of_mem_moves hy hz
termination_by x
decreasing_by igame_wf

theorem isUndominated_iff_undominate_eq {x : IGame} : IsUndominated x ↔ x.undominate = x := by
  refine ⟨IsUndominated.undominate_eq, fun hx ↦ ?_⟩
  rw [← hx]
  exact .undominate x

/-! ### Unreversing games -/

/-- A hereditarily unreversed game is one where no move is reversible, and such that every
subposition satisfies this same property. -/
def IsUnreversed (x : IGame) : Prop :=
  ∀ p, ∀ y ∈ x.moves p, IsUnreversed y ∧ ∀ z ∈ y.moves (-p), ¬p.LE z x
termination_by x
decreasing_by igame_wf

theorem isUnreversed_def {x : IGame} : IsUnreversed x ↔
    ∀ p, ∀ y ∈ x.moves p, IsUnreversed y ∧ ∀ z ∈ y.moves (-p), ¬p.LE z x := by
  rw [IsUnreversed]

namespace IsUnreversed

theorem of_mem_moves {x y : IGame} {p : Player} (hy : y ∈ x.moves p) (h : IsUnreversed x) :
    IsUnreversed y := by
  rw [isUnreversed_def] at h
  exact (h p y hy).1

theorem lf_of_mem_moves_of_mem_moves {x y z : IGame} {p : Player} (h : IsUnreversed x)
    (hy : y ∈ x.moves p) (hz : z ∈ y.moves (-p)) : ¬p.LE z x := by
  rw [isUnreversed_def] at h
  exact (h p y hy).2 z hz

theorem lf_of_mem_moves_left_of_mem_moves_right {x y z : IGame} (h : IsUnreversed x)
    (hy : y ∈ xᴸ) (hz : z ∈ yᴿ) : x ⧏ z :=
  lf_of_mem_moves_of_mem_moves h hy hz

theorem lf_of_mem_moves_right_of_mem_moves_left {x y z : IGame} (h : IsUnreversed x)
    (hy : y ∈ xᴿ) (hz : z ∈ yᴸ) : z ⧏ x :=
  lf_of_mem_moves_of_mem_moves h hy hz

protected theorem neg {x : IGame} (hx : IsUnreversed x) : IsUnreversed (-x) := by
  induction x using IGame.moveRecOn with | ind x ih
  rw [isUnreversed_def]
  intro p
  rw [forall_mem_moves_neg]
  refine fun y hy ↦ ⟨ih (-p) y hy (.of_mem_moves hy hx), ?_⟩
  rw [forall_mem_moves_neg]
  intro z hz
  rw [IGame.neg_playerLE_neg_iff, ← Player.neg_le_iff_swap]
  exact hx.lf_of_mem_moves_of_mem_moves hy hz

@[simp] protected theorem neg_iff {x : IGame} : IsUnreversed (-x) ↔ IsUnreversed x :=
  ⟨fun h => neg_neg x ▸ h.neg, .neg⟩

@[simp] protected theorem zero : IsUnreversed 0 := by
  rw [isUnreversed_def]
  simp

@[simp] protected theorem one : IsUnreversed 1 := by
  rw [isUnreversed_def]
  simp

@[simp] protected theorem half : IsUnreversed ½ := by
  rw [isUnreversed_def]
  simp [IGame.zero_lt_half]

@[simp] protected theorem natCast (n : ℕ) : IsUnreversed n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [isUnreversed_def, Player.forall, moves_left_natCast_succ']
    simp [ih]

@[simp] protected theorem intCast (n : ℤ) : IsUnreversed n := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp

@[simp] protected theorem star : IsUnreversed ⋆ := by
  rw [isUnreversed_def]
  simp

@[simp] protected theorem up : IsUnreversed ↑ := by
  rw [isUnreversed_def]
  simp [up_pos.not_ge]

@[simp] protected theorem down : IsUnreversed ↓ := by
  rw [isUnreversed_def]
  simp [down_neg.not_ge]

@[simp]
theorem _root_.NatOrdinal.isUnreversed_toIGame (o : NatOrdinal) : IsUnreversed o.toIGame := by
  induction o using WellFoundedLT.induction with | ind o ih
  rw [isUnreversed_def]
  simp +contextual [ih]

end IsUnreversed

end IGame
end
