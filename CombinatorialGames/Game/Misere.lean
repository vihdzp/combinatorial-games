import CombinatorialGames.Game.IGame

universe u

open Set

instance small_ite {α : Type*} {p : Prop} [Decidable p] (s t : Set α) [Small.{u} s] [Small.{u} t] :
    Small.{u} (if p then s else t) := by
  split_ifs <;> infer_instance

instance small_ite' {α : Type*} {p : Prop} [Decidable p] (s t : Set α) [Small.{u} s] [Small.{u} t] :
    Small.{u} (if p then s else t : Set _) := by
  split_ifs <;> infer_instance

noncomputable section
namespace IGame

instance : DecidableEq (Set IGame) := Classical.decEq _

/-- Play a game using a misère convention. That means, every subposition that previously had no
moves for a given player now has a single move to `0`, granting them the win. -/
def toMisere (x : IGame) : IGame :=
  {if x.leftMoves = ∅ then {0} else (range fun y : x.leftMoves ↦ toMisere y) |
    if x.rightMoves = ∅ then {0} else (range fun y : x.rightMoves ↦ toMisere y)}ᴵ
termination_by x
decreasing_by igame_wf

theorem leftMoves_toMisere {x : IGame} : leftMoves (toMisere x) =
    if x.leftMoves = ∅ then {0} else toMisere '' x.leftMoves := by
  rw [toMisere]
  simp [image_eq_range]

theorem rightMoves_toMisere {x : IGame} : rightMoves (toMisere x) =
    if x.rightMoves = ∅ then {0} else toMisere '' x.rightMoves := by
  rw [toMisere]
  simp [image_eq_range]

private theorem toMisere_le' {x : IGame} :
    (toMisere x ≤ 0 ↔ x.leftMoves ≠ ∅ ∧ ∀ y ∈ x.leftMoves, toMisere y ⧏ 0) ∧
    (0 ≤ toMisere x ↔ x.rightMoves ≠ ∅ ∧ ∀ y ∈ x.rightMoves, 0 ⧏ toMisere y) := by
  rw [le_zero, zero_le, leftMoves_toMisere, rightMoves_toMisere]
  split_ifs <;> simp_all

/-- Left wins as the first player iff they run out of moves, or if there's some move that right
can't win as the first player. -/
theorem zero_lf_toMisere {x : IGame} :
    0 ⧏ toMisere x ↔ x.leftMoves = ∅ ∨ ∃ y ∈ x.leftMoves, 0 ≤ toMisere y := by
  rw [toMisere_le'.1, not_and_or]
  simp

/-- Right wins as the first player iff they run out of moves, or if there's some move that left
can't win as the first player. -/
theorem toMisere_lf_zero {x : IGame} :
    toMisere x ⧏ 0 ↔ x.rightMoves = ∅ ∨ ∃ y ∈ x.rightMoves, toMisere y ≤ 0 := by
  rw [toMisere_le'.2, not_and_or]
  simp

end IGame
end
