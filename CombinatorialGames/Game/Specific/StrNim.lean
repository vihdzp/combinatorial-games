/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
import CombinatorialGames.Game.Concrete
import CombinatorialGames.Game.Specific.Nim

/-!
# Str(ing)Nim

We define StrNim from the paper https://doi.org/10.48550/arXiv.2503.16781.
This is an impartial game played on a string - a list of characters.

We use σ for the type of the alphabet.
-/

namespace IGame

universe u

def StrNim (σ : Type u) [DecidableEq σ] := List σ
variable {σ : Type u} [DecidableEq σ]

instance : DecidableEq (StrNim σ) := instDecidableEqList -- deriving DecidableEq doesn't work
@[match_pattern] def toStrNim : List σ ≃ StrNim σ := Equiv.refl _
@[match_pattern] def ofStrNim : StrNim σ ≃ List σ := Equiv.refl _

@[simp] theorem toStrNim_ofStrNim (s : StrNim σ) :
  toStrNim (ofStrNim s) = s := rfl
@[simp] theorem ofStrNim_toStrNim (l : List σ) :
  ofStrNim (toStrNim l) = l := rfl

namespace StrNim

def length (s : StrNim σ) : ℕ := (ofStrNim s).length

instance : EmptyCollection (StrNim σ) := ⟨toStrNim []⟩

variable {σ : Type u} [DecidableEq σ] (s t : StrNim σ)

instance : GetElem (StrNim σ) Nat σ fun s i => i < s.length where
  getElem s i hi := (ofStrNim s)[i]'hi

structure Move where
  idx : ℕ
  len : ℕ
  len_pos : 0 < len
  bounded : idx + len < s.length
  equiv : ∃ σ, List.take len (List.drop idx (ofStrNim s)) = List.replicate len σ

theorem Move.idx_bounded (m : Move s) : m.idx < s.length - m.len := by
  have := m.bounded
  have := m.len_pos
  omega

/-- Players can remove any repeating substring -/
def moves : List (Move s) :=
  let idxs := List.range (s.length - 1)
  let lens := List.attach <| List.range' 1 s.length
  let prod := idxs.product lens
  prod.filterMap fun ⟨i, ⟨l, hl⟩⟩ ↦
    if h : (i + l) < s.length ∧
      (List.take l (List.drop i (ofStrNim s))).toFinset.card = 1
    then some ⟨i, l, by rw [List.mem_range'] at hl; omega, by omega, by
      simp_rw [List.eq_replicate_iff]
      rw [Finset.card_eq_one] at h
      refine ⟨h.2.choose, ?_, fun b hb ↦ ?_⟩
      · rw [List.length_take, List.length_drop, min_eq_left_iff, ← length]
        omega
      · have := h.2.choose_spec
        rw [Finset.eq_singleton_iff_unique_mem, List.mem_toFinset] at this
        simp_all
    ⟩
    else none

theorem moves_total (m : Move s) : m ∈ moves s := by
  rw [moves, List.mem_filterMap]
  simp only [Option.dite_none_right_eq_some, Prod.exists, List.pair_mem_product,
    List.mem_range, List.mem_attach, and_true, exists_and_left, Subtype.exists, List.mem_range'_1]
  refine ⟨
    m.idx, (by have := m.idx_bounded; have := m.len_pos; omega), m.len,
    ⟨m.len_pos, by have := m.bounded; omega⟩, ⟨m.bounded, ?_⟩, rfl
  ⟩
  rw [m.equiv.choose_spec, List.toFinset_replicate_of_ne_zero (Nat.ne_zero_of_lt m.len_pos)]
  rfl

/-- Moving with a move removes that move from the string. -/
def move (m : Move s) : StrNim σ :=
  toStrNim ((ofStrNim s).take (m.idx) ++ (ofStrNim s).drop (m.idx + m.len))

open ConcreteGame

/-- A player can move from `b` to `a` when there exists some `m ∈ moves b` with `a = b.move m`. -/
def rel (a b : StrNim σ) : Prop :=
  ∃ m ∈ moves b, a = b.move m

@[inherit_doc] local infixl:50 " ≺ " => rel

instance : DecidableRel (@rel σ _) := fun _ _ ↦ inferInstanceAs (Decidable (∃ _, _))

theorem move_size {s : StrNim σ} (m : Move s) :
    (ofStrNim (move s m)).length + m.len = s.length := by
  rw [move, ofStrNim_toStrNim, List.length_append, List.length_take, List.length_drop]
  have := m.bounded
  rw [← length, Nat.min_eq_left (by omega)]
  omega

theorem subrelation_rel :
    Subrelation (@rel σ _) (InvImage (· < ·) (fun s ↦ s.length)) := by
  intro a b h
  rw [InvImage, h.choose_spec.2, ← move_size h.choose]
  exact Nat.lt_add_of_pos_right h.choose.len_pos

instance : IsWellFounded _ (@rel σ _) := subrelation_rel.isWellFounded
instance : ConcreteGame (StrNim σ) := .ofImpartial rel

@[simp]
protected theorem neg_toIGame (s : StrNim σ) : -toIGame s = toIGame s :=
  neg_toIGame rfl s

protected instance impartial_toIGame (s : StrNim σ) : (toIGame s).Impartial :=
  impartial_toIGame rfl s

end StrNim

end IGame
