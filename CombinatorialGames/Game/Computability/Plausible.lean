/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
import CombinatorialGames.Game.Computability.Countable

/-!
# Plausibility, Representability, Shrinkability

This file provides the necessary instances to get Plausibility working, and enables a safe `Repr`
instance on `FGame` using the sorting provided by `FGame#toNat`.
-/

/-- ### Utilities -/

/- The `List` `Repr` using `{}` instead of `[]` -/
protected def _root_.List.reprSetlike {α : Type*} [Repr α] (a : List α) (n : Nat) : Std.Format :=
  let _ : Std.ToFormat α := ⟨repr⟩
  match a, n with
  | [], _ => "{}"
  | as, _ => Std.Format.bracket "{" (Std.Format.joinSep as ("," ++ Std.Format.line)) "}"

universe u

namespace FGame

open Plausible

instance : Shrinkable FGame where
  shrink x :=
    let digits := Nat.digits 4 (toNat x)
    ((List.range digits.length).map
      (fun idx ↦ [digits.set idx 0] ++
          (if digits[idx]? = some 3 then [digits.set idx 1, digits.set idx 2] else []))).flatten.map
        (ofNat <| Nat.ofDigits 4 ·)

/-! ### Repr -/

private def List.repr_or_emptyset {α : Type*} [Repr α] : Repr (List α) where
  reprPrec g n := if g.length = 0 then "∅" else List.reprSetlike g n

-- TODO: can we hook into delab?
private def instRepr_aux (g : FGame) : Std.Format :=
  have : IsTrans FGame (·.toNat ≤ ·.toNat) := ⟨fun a b c ↦ (·.trans ·)⟩
  -- TODO: holds if injectivity
  have : IsAntisymm FGame (·.toNat ≤ ·.toNat) := ⟨fun a b h hh ↦ sorry⟩
  have : IsTotal FGame (·.toNat ≤ ·.toNat) := ⟨fun a b ↦ Nat.le_total ..⟩
  "{" ++
    List.repr_or_emptyset.reprPrec
      ((g.leftMoves.sort (·.toNat ≤ ·.toNat)).attach.map (fun ⟨x, _⟩ ↦ instRepr_aux x)) 0 ++ " | " ++
    List.repr_or_emptyset.reprPrec
      ((g.rightMoves.sort (·.toNat ≤ ·.toNat)).attach.map (fun ⟨x, _⟩ ↦ instRepr_aux x)) 0 ++ "}"
termination_by g
decreasing_by all_goals rw [Finset.mem_sort] at *; fgame_wf

/-- The Repr of FGame. We confine inputs to {0} to make universe determinism easy on `#eval`,
and we prefer our notation of games {{a, b, c}|{d, e, f}} over the usual flattened out one
{a, b, c|d, e, f} to match with the `IGame` builder syntax. -/
instance : Repr FGame.{0} := ⟨fun g _ ↦ instRepr_aux g⟩

instance : SampleableExt FGame :=
  SampleableExt.mkSelfContained do
    let n ← Gen.choose Nat 0 (← Gen.getSize) (Nat.zero_le _)
    return .ofNat n

end FGame
