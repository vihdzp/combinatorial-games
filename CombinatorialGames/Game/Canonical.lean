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

/-- The set of `-p`-moves of `z` which reverse `z` with respect to a `p`-move from `x`.
That is, if player `p` moves from `x` to `z`, then `reverseSet x p z` is the set of
moves `-p` could make as a response that reverse the move from `x` to `z`.
Note that `z` is not necessarily a `p`-option of `x`. -/
@[expose]
def reverseSet (x : IGame) (p : Player) (z : IGame) : Set IGame :=
  {g | g ∈ z.moves (-p) ∧ p.cases (g ≤ x) (x ≤ g)}

instance (x : IGame.{u}) (p : Player) (z : IGame.{u}) : Small.{u} (reverseSet x p z) := by
  unfold reverseSet
  infer_instance

theorem neg_reverseSet (x : IGame) (p : Player) (z : IGame) :
    -reverseSet x p z = reverseSet (-x) (-p) (-z) := by
  unfold reverseSet
  cases p <;> simp [Set.ext_iff, IGame.neg_le]

theorem reverseSet_congr_left {x y : IGame} (hxy : x ≈ y) (p : Player) (z : IGame) :
    reverseSet x p z = reverseSet y p z := by
  unfold reverseSet
  cases p <;> simp [hxy.le_congr_left, hxy.le_congr_right]

theorem lf_of_reverseSet_eq_empty_of_mem_moves {x : IGame} {p : Player} {z : IGame}
    (hx : reverseSet x p z = ∅) {g : IGame} (hg : g ∈ z.moves (-p)) :
    ¬p.cases (g ≤ x) (x ≤ g) :=
  fun h => Set.eq_empty_iff_forall_notMem.1 hx g ⟨hg, h⟩

-- false positive on `hg` which is referenced in the termination proof
set_option linter.unusedVariables false in
/-- Repeatedly unreverse the move `z` with respect to a `p`-move from `x`.
Treating `z` as a `p`-option of `x`, bypass it if it is reversible, and
then recursively unreverse all the resulting games. -/
private def unreverse1 (x : IGame) (p : Player) (z : IGame) : Set IGame :=
  open scoped Classical in
  if reverseSet x p z = ∅ then {z} else
  ⋃ (g) (hg : g ∈ reverseSet x p z) (g') (hg' : g' ∈ g.moves p), unreverse1 x p g'
termination_by z
decreasing_by exact .trans (.of_mem_moves hg') (.of_mem_moves hg.1)

private theorem unreverse1_of_reverseSet_eq_empty {x : IGame} {p : Player} {z : IGame}
    (hx : reverseSet x p z = ∅) : unreverse1 x p z = {z} := by
  rw [unreverse1, ite_eq_left hx]

private theorem unreverse1_of_reverseSet_ne_empty {x : IGame} {p : Player} {z : IGame}
    (hx : reverseSet x p z ≠ ∅) : unreverse1 x p z =
    ⋃ (g) (_ : g ∈ reverseSet x p z) (g') (_ : g' ∈ g.moves p), unreverse1 x p g' := by
  rw [unreverse1, ite_eq_right hx]

private instance (x : IGame.{u}) (p : Player) (z : IGame.{u}) : Small.{u} (unreverse1 x p z) := by
  fun_induction unreverse1 x p z with
  | case1 => infer_instance
  | case2 z _ ih =>
    exact @small_biUnion _ _ (reverseSet x p z) _ _ fun g hg =>
      @small_biUnion _ _ (g.moves p) _ _ (ih g hg)

private theorem neg_unreverse1 (x : IGame) (p : Player) (z : IGame) :
    -unreverse1 x p z = unreverse1 (-x) (-p) (-z) := by
  fun_induction unreverse1 x p z with
  | case1 z hx =>
    unfold unreverse1
    rw [← neg_reverseSet, hx]
    simp
  | case2 z hx ih =>
    rw [unreverse1, ← neg_reverseSet]
    simp_rw [Set.neg_eq_empty, ite_eq_right hx]
    simp only [← Set.image_neg_eq_neg, Set.image_iUnion,
      Set.biUnion_image, moves_neg, neg_neg]
    refine Set.iUnion₂_congr fun g hg => Set.iUnion₂_congr fun g' hg' => ?_
    rw [Set.image_neg_eq_neg, ih g hg g' hg']

private theorem unreverse1_congr_left {x y : IGame} (hxy : x ≈ y) (p : Player) (z : IGame) :
    unreverse1 x p z = unreverse1 y p z := by
  fun_induction unreverse1 x p z with
  | case1 z hx => rw [unreverse1, ← reverseSet_congr_left hxy, ite_eq_left hx]
  | case2 z hx ih =>
    rw [unreverse1, ← reverseSet_congr_left hxy, ite_eq_right hx]
    refine Set.iUnion₂_congr fun g hg => Set.iUnion₂_congr fun g' hg' => ?_
    exact ih g hg g' hg'

private theorem reverseSet_of_mem_unreverse1 {x : IGame} {p : Player} {z : IGame} {g : IGame}
    (hg : g ∈ unreverse1 x p z) : reverseSet x p g = ∅ := by
  fun_induction unreverse1 x p z with
  | case1 z hx =>
    rw [Set.mem_singleton_iff.1 hg]
    exact hx
  | case2 z hx ih =>
    simp_rw [Set.mem_iUnion₂] at hg
    obtain ⟨g', hg', g'', hg'', hg⟩ := hg
    exact ih g' hg' g'' hg'' hg

private theorem wsubposition_of_mem_unreverse1 {x : IGame} {p : Player} {z : IGame} {g : IGame}
    (hg : g ∈ unreverse1 x p z) : WSubposition g z := by
  fun_induction unreverse1 x p z with
  | case1 z hx => rw [Set.mem_singleton_iff.1 hg]
  | case2 z hx ih =>
    simp_rw [Set.mem_iUnion₂] at hg
    obtain ⟨g', hg', g'', hg'', hg⟩ := hg
    exact (ih g' hg' g'' hg'' hg).trans (.trans (.of_mem_moves hg'') (.of_mem_moves hg'.1))

private theorem lf_of_mem_reverseSet_of_mem_unreverse1
    {x : IGame} {p : Player} {z : IGame} {g g' c : IGame}
    (hg : g ∈ reverseSet x p z) (hg' : g' ∈ g.moves p) (hc : c ∈ unreverse1 x p g') :
    ¬p.cases (x ≤ c) (c ≤ x) := by
  induction z using wellFounded_subposition.induction generalizing g g' with | _ z ih
  by_cases hx : reverseSet x p g' = ∅
  · rw [unreverse1_of_reverseSet_eq_empty hx, Set.mem_singleton_iff] at hc
    rw [hc]
    cases p with
    | left => exact fun h => left_lf hg' (hg.2.trans h)
    | right => exact fun h => lf_right hg' (h.trans hg.2)
  · rw [unreverse1_of_reverseSet_ne_empty hx] at hc
    simp_rw [Set.mem_iUnion] at hc
    obtain ⟨g'', hg'', g''', hg''', hc⟩ := hc
    exact ih g' (.trans (.of_mem_moves hg') (.of_mem_moves hg.1)) hg'' hg''' hc

private theorem lf_of_mem_moves_of_mem_unreverse1
    {x : IGame} {p : Player} {z : IGame} {g : IGame}
    (hz : z ∈ x.moves p) (hg : g ∈ unreverse1 x p z) :
    ¬p.cases (x ≤ g) (g ≤ x) := by
  by_cases hx : reverseSet x p z = ∅
  · rw [unreverse1_of_reverseSet_eq_empty hx, Set.mem_singleton_iff] at hg
    rw [hg]
    cases p with
    | left => exact left_lf hz
    | right => exact lf_right hz
  · rw [unreverse1_of_reverseSet_ne_empty hx] at hg
    simp_rw [Set.mem_iUnion] at hg
    obtain ⟨g', hg', g'', hg'', hg⟩ := hg
    exact lf_of_mem_reverseSet_of_mem_unreverse1 hg' hg'' hg

private theorem unreverse_equiv_aux_left (x : IGame) :
    x ≈ !{⋃ z : xᴸ, unreverse1 x left z | xᴿ} := by
  apply equiv_of_forall_lf
  · intro z hz
    replace hz : unreverse1 x left z ⊆ ⋃ z : xᴸ, unreverse1 x left z :=
      Set.subset_iUnion (fun z : xᴸ => unreverse1 x left z) ⟨z, hz⟩
    induction z using wellFounded_subposition.induction with | _ z ih
    by_cases hx : reverseSet x left z = ∅
    · apply left_lf
      rw [leftMoves_ofSets]
      apply hz
      rw [unreverse1_of_reverseSet_eq_empty hx, Set.mem_singleton_iff]
    · obtain ⟨g, hg⟩ : (reverseSet x left z).Nonempty := Set.nonempty_iff_ne_empty.2 hx
      refine lf_of_right_le (le_iff_forall_lf.2 ⟨?_, ?_⟩) hg.1
      · intro g' hg'
        refine ih g' (.trans (.of_mem_moves hg') (.of_mem_moves hg.1)) (subset_trans ?_ hz)
        rw [unreverse1_of_reverseSet_ne_empty hx]
        exact Set.subset_iUnion₂_of_subset g hg (Set.subset_biUnion_of_mem hg')
      · rw [rightMoves_ofSets]
        intro g' hg'
        exact fun h => lf_right hg' (h.trans hg.2)
  · intro z hz
    apply lf_right
    rw [rightMoves_ofSets]
    exact hz
  · rw [leftMoves_ofSets, Set.forall_mem_iUnion, Subtype.forall]
    intro z hz g hg
    exact lf_of_mem_moves_of_mem_unreverse1 hz hg
  · rw [rightMoves_ofSets]
    intro z hz
    exact lf_right hz

private theorem unreverse_equiv_aux_right (x : IGame) :
    x ≈ !{xᴸ | ⋃ z : xᴿ, unreverse1 x right z} := by
  rw [← neg_equiv_neg_iff, neg_ofSets, neg_eq]
  simp_rw [← Set.image_neg_eq_neg, Set.image_iUnion,
    Set.image_neg_eq_neg, neg_unreverse1]
  refine (unreverse_equiv_aux_left _).trans (Eq.antisymmRel ?_)
  rw [ofSets_inj, rightMoves_ofSets, and_iff_left rfl,
    Player.neg_right]
  simp_rw [Set.iUnion_coe_set, ← Set.iSup_eq_iUnion]
  apply (Equiv.neg IGame).iSup_congr
  simp [neg_eq]

/-- Recursively repeatedly bypass all reversible options from a game `x`,
so that `unreverse x` hereditarily has no reversible options. -/
def unreverse (x : IGame) : IGame :=
  !{fun p => ⋃ z : x.moves p, unreverse1 x p (unreverse z)}
termination_by x
decreasing_by igame_wf

theorem unreverse_equiv (x : IGame) : unreverse x ≈ x := by
  induction x using moveRecOn with | ind x ih
  unfold unreverse
  let x' := !{fun p => unreverse '' x.moves p}
  have hx'l := unreverse_equiv_aux_left x'
  have hx'r := hx'l.trans <| unreverse_equiv_aux_right _
  simp_rw [leftMoves_ofSets, ← unreverse1_congr_left hx'l] at hx'r
  have hx' : x' ≈ x := by
    unfold x'
    apply equiv_of_exists <;> simpa using fun z hz ↦ ⟨z, hz, ih _ z hz⟩
  simp_rw [unreverse1_congr_left hx'] at hx'r
  refine ((ofSets_eq_ofSets_cases _ _).antisymmRel.trans ?_).trans (hx'r.symm.trans hx')
  unfold x'
  simp

theorem birthday_unreverse_le (x : IGame) : birthday (unreverse x) ≤ birthday x := by
  induction x using moveRecOn with | ind x ih
  unfold unreverse
  simp_rw [birthday_le_iff, moves_ofSets, Set.forall_mem_iUnion]
  intro p z g hg
  exact ((birthday_le_of_wsubposition (wsubposition_of_mem_unreverse1 hg)).trans
    (ih p z.1 z.2)).trans_lt (birthday_lt_of_mem_moves z.2)

theorem reverseSet_unreverse {x : IGame} {p : Player} {z : IGame} (hz : z ∈ (unreverse x).moves p) :
    reverseSet x p z = ∅ := by
  unfold unreverse at hz
  rw [moves_ofSets, Set.mem_iUnion] at hz
  obtain ⟨⟨g, hg⟩, hz⟩ := hz
  exact reverseSet_of_mem_unreverse1 hz

theorem reverseSet_eq_empty_of_mem_moves_of_unreverse_eq_self
    {x : IGame} {p : Player} {z : IGame} (hz : z ∈ x.moves p) (hx : unreverse x = x) :
    reverseSet x p z = ∅ :=
  reverseSet_unreverse (hx.symm ▸ hz)

theorem unreverse_eq_self_of_reverseSet {x : IGame}
    (hx : ∀ p, ∀ z ∈ x.moves p, reverseSet x p z = ∅)
    (ih : ∀ p, ∀ z ∈ x.moves p, unreverse z = z) : unreverse x = x := by
  unfold unreverse
  ext p z
  rw [moves_ofSets,
    Set.iUnion_congr fun g : x.moves p =>
      (congrArg (unreverse1 x p) (ih p g.1 g.2)).trans
        (unreverse1_of_reverseSet_eq_empty (hx p g.1 g.2))]
  simp

mutual

theorem unreverse_eq_self_of_mem_moves_of_unreverse_eq_self {x : IGame} {p : Player} {z : IGame}
    (hz : z ∈ x.moves p) (hx : unreverse x = x) : unreverse z = z :=
  have hz : z ∈ ⋃ g : x.moves p, unreverse1 x p (unreverse g) := by
    rwa [← hx, unreverse, moves_ofSets] at hz
  (Set.mem_iUnion.1 hz).elim fun g hz =>
    unreverse_eq_self_of_wsubposition_of_unreverse_eq_self
      (wsubposition_of_mem_unreverse1 hz) (unreverse_unreverse g)
termination_by (x.birthday, 0)
decreasing_by
  · refine .left _ _ ?_
    exact birthday_lt_of_mem_moves g.2
  · refine .left _ _ ?_
    exact (birthday_unreverse_le g).trans_lt (birthday_lt_of_mem_moves g.2)

theorem unreverse_unreverse (x : IGame) : unreverse (unreverse x) = unreverse x :=
  unreverse_eq_self_of_reverseSet
    (fun p z hz => (reverseSet_congr_left (unreverse_equiv x) p z).trans (reverseSet_unreverse hz))
    (fun p z hz =>
      have hz : z ∈ ⋃ g : x.moves p, unreverse1 x p (unreverse g) := by
        rwa [unreverse, moves_ofSets] at hz
      (Set.mem_iUnion.1 hz).elim fun g hz =>
        unreverse_eq_self_of_wsubposition_of_unreverse_eq_self
          (wsubposition_of_mem_unreverse1 hz) (unreverse_unreverse g))
termination_by (x.birthday, 0)
decreasing_by
  · refine .left _ _ ?_
    exact birthday_lt_of_mem_moves g.2
  · refine .left _ _ ?_
    exact (birthday_unreverse_le g).trans_lt (birthday_lt_of_mem_moves g.2)

theorem unreverse_eq_self_of_wsubposition_of_unreverse_eq_self {x z : IGame}
    (hz : WSubposition z x) (hx : unreverse x = x) : unreverse z = z :=
  (wsubposition_iff_eq_or_subposition.1 hz).elim (fun hz => hz.symm ▸ hx)
    (fun hz => (subposition_iff_exists.1 hz).elim fun p hp =>
      hp.elim fun g hg => hg.elim fun hg hz =>
        unreverse_eq_self_of_wsubposition_of_unreverse_eq_self hz
          (unreverse_eq_self_of_mem_moves_of_unreverse_eq_self hg hx))
termination_by (x.birthday, 1)
decreasing_by
  · refine .right _ ?_
    simp
  · refine .left _ _ ?_
    exact birthday_lt_of_mem_moves hg

end

end IGame
end
