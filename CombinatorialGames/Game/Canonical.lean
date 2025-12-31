/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Birthday

/-!
# Canonical games

If `y, z ∈ xᴸ` with `y < z` or if `y, z ∈ xᴿ` with `z < y`, we say that `y` is **dominated** by `z`.
Under this assumption, the respective player will always choose to play on `z` rather than on `y`,
so we can remove `y` from consideration.

If `y ∈ xᴸ` and there exists some `z ∈ xᴿ` with `z ≤ x`, or if `y ∈ xᴿ` and there exists some
`z ∈ xᴸ` with `x ≤ z`, we say that `x` is **reversible** through `y`. Under this assumption, if the
respective player plays on `y`, they can assume that the other player will then play on `z`, so they
must be ready to consider all left/right options of `z`, respectively. That is, if we remove `y` and
replace it by the left/right options of `z`, we'll get an equivalent game.

If `x` is short, we can define `undominate x` as an equivalent game where no subposition has
dominated moves. Likewise, for any `x`, we can define `unreverse x` as an equivalent game where no
subposition has reversible moves. Finally, for `x` short, we can define its **canonical form**
`canonical x = undominate (unreverse x)`, which will have no dominated and no reversible moves.

## Todo

- Prove that `x ≈ y → canonical x = canonical y`.
- Prove that `Game.birthday (.mk x) = IGame.birthday (canonical x)`.
-/

universe u

noncomputable section

namespace IGame
variable {x y z : IGame.{u}} {p q : Player}

/-! ### Undominated games -/

/-- Removes all dominated positions from a game. This returns garbage values on non-short games. -/
def undominate (x : IGame) : IGame :=
  !{{y ∈ Set.range fun z : xᴸ ↦ undominate z | ∀ z ∈ xᴸ, ¬y < z} |
    {y ∈ Set.range fun z : xᴿ ↦ undominate z | ∀ z ∈ xᴿ, ¬z < y}}
termination_by x
decreasing_by igame_wf

theorem undominate_def : x.undominate =
    !{{y ∈ undominate '' xᴸ | ∀ z ∈ xᴸ, ¬y < z} |
      {y ∈ undominate '' xᴿ | ∀ z ∈ xᴿ, ¬z < y}} := by
  rw [undominate]
  simp

@[aesop simp]
theorem moves_left_undominate : x.undominateᴸ = {y ∈ undominate '' xᴸ | ∀ z ∈ xᴸ, ¬y < z} := by
  rw [undominate_def]
  exact leftMoves_ofSets ..

@[aesop simp]
theorem moves_right_undominate : x.undominateᴿ = {y ∈ undominate '' xᴿ | ∀ z ∈ xᴿ, ¬z < y} := by
  rw [undominate_def]
  exact rightMoves_ofSets ..

theorem mem_image_of_mem_moves_undominate (h : y ∈ x.undominate.moves p) :
    y ∈ undominate '' x.moves p := by
  aesop

theorem not_lt_of_mem_moves_left_undominate' (hy : y ∈ x.undominateᴸ) (hz : z ∈ xᴸ) : ¬y < z := by
  aesop

theorem not_lt_of_mem_moves_right_undominate' (hy : y ∈ x.undominateᴿ) (hz : z ∈ xᴿ) : ¬z < y := by
  aesop

theorem birthday_undominate_le (x : IGame) : x.undominate.birthday ≤ x.birthday := by
  rw [undominate, birthday_le_iff']
  have (w) (hw : IsOption w x) := (birthday_undominate_le w).trans_lt (birthday_lt_of_isOption hw)
  aesop
termination_by x
decreasing_by igame_wf

instance [hx : Short x] : Short (undominate x) := by
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
  rw [le_def, moves_left_undominate, moves_right_undominate]
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

/-- `undominate x` has no dominated left moves. -/
theorem not_lt_of_mem_moves_left_undominate [Short x]
    (hy : y ∈ x.undominateᴸ) (hz : z ∈ x.undominateᴸ) : ¬y < z := by
  rw [moves_left_undominate] at hz
  obtain ⟨⟨z, hz, rfl⟩, hz'⟩ := hz
  short
  grw [undominate_equiv z]
  exact not_lt_of_mem_moves_left_undominate' hy hz

/-- `undominate x` has no dominated right moves. -/
theorem not_lt_of_mem_moves_right_undominate [Short x]
    (hy : y ∈ x.undominateᴿ) (hz : z ∈ x.undominateᴿ) : ¬z < y := by
  rw [moves_right_undominate] at hz
  obtain ⟨⟨z, hz, rfl⟩, hz'⟩ := hz
  short
  grw [undominate_equiv z]
  exact not_lt_of_mem_moves_right_undominate' hy hz

/-! ### Unreversible games -/

/-- A predicate for `y` to be a reversible move for `p` in `x`. -/
def Reversible (x y : IGame) (p : Player) : Prop :=
  p.cases (∃ z ∈ yᴿ, z ⧏ x) (∃ z ∈ yᴸ, x ⧏ z)

/-- Choose an arbitrary witness for the `Reversible` predicate. -/
def Reversible.choose (h : Reversible x y p) : IGame :=
  match p with | left | right => Classical.choose h

private theorem Reversible.choose_spec (h : Reversible x y p) :
    p.cases (h.choose ∈ yᴿ ∧ h.choose ⧏ x) (h.choose ∈ yᴸ ∧ x ⧏ h.choose) := by
  cases p <;> exact Classical.choose_spec h

theorem Reversible.choose_mem_moves (h : Reversible x y p) : h.choose ∈ y.moves (-p) := by
  cases p <;> exact h.choose_spec.1

theorem Reversible.choose_lf (h : Reversible x y left) : h.choose ⧏ x := h.choose_spec.2
theorem Reversible.lf_choose (h : Reversible x y right) : x ⧏ h.choose := h.choose_spec.2

open Classical in
/-- An auxiliary definition for `unreverse`. If `y` is a reversible move for `p` in `x`, then
`reverseSet x y p` is defined as `p`'s moves in `Reversible.choose`. Otherwise,
`reverseSet x y p = {y}`. -/
def reverseSet (x y : IGame) (p : Player) : Set IGame :=
  if hy : Reversible x y p then hy.choose.moves p else {y}

instance : Small.{u} (reverseSet x y p) := by
  rw [reverseSet]
  split_ifs <;> infer_instance

theorem subposition_of_mem_reverseSet (hy : y ∈ x.moves p) (h : z ∈ reverseSet x y q) :
    Subposition z x := by
  rw [reverseSet] at h
  split_ifs at h with h'
  · exact .trans (.trans (.of_mem_moves h) (.of_mem_moves h'.choose_mem_moves)) (.of_mem_moves hy)
  · subst h
    exact .of_mem_moves hy

/-- Bypasses all reversible positions from a game and all its subpositions. -/
def unreverse (x : IGame) : IGame :=
  !{fun p ↦ ⋃ y : x.moves p, Set.range fun z : reverseSet x y p ↦ unreverse z}
termination_by x
decreasing_by all_goals exact subposition_of_mem_reverseSet (‹_› : Subtype _).2 z.2

theorem unreverse_def : x.unreverse =
    !{fun p ↦ ⋃ y ∈ x.moves p, unreverse '' reverseSet x y p} := by
  rw [unreverse]
  aesop

theorem moves_unreverse (x : IGame) (p : Player) : x.unreverse.moves p =
    ⋃ y ∈ x.moves p, unreverse '' reverseSet x y p := by
  rw [unreverse_def, moves_ofSets]

/-! ### Canonical forms -/

def canonical (x : IGame) : IGame :=
  undominate (unreverse x)

end IGame
end
