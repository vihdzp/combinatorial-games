/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Sign sequences

One can define a sequence of approximations for any surreal number `x`, such that the `n`-th
approximant is the number `{s | t}` where `s` and `t` are the numbers with birthday less than `n`
which are lesser and greater to `x`, respectively. This yields an ordinal-indexed sequence of signs,
where the `n`-th entry represents whether the `n`-th approximant to `x` is lesser, equal, or greater
than `x`.

As it turns out, the correspondence between surreal numbers and sign sequences is both bijective and
order-preserving, where the order given to sign sequences is the lexicographic ordering.

## Todo

* Define the sign sequence for a surreal number
* Prove that the correspondence is an order isomorphism
* Define the operation `x : y` on games.
-/

universe u

noncomputable section

/-! ### Signs -/

/-- Represents a sign in a `SignSeq`, which is either plus, zero, or minus.

For convenience, and to avoid introducing more notation, we write `⊤` for plus, `0` for zero, and
`⊥` for minus. -/
inductive Sign : Type
  | plus : Sign
  | zero : Sign
  | minus : Sign
deriving Fintype

namespace Sign

instance : Top Sign := ⟨plus⟩
instance : Zero Sign := ⟨zero⟩
instance : Bot Sign := ⟨minus⟩

@[simp] theorem top_def : plus = ⊤ := rfl
@[simp] theorem zero_def : zero = 0 := rfl
@[simp] theorem bot_def : minus = ⊥ := rfl

instance : Neg Sign where neg
  | plus => minus
  | zero => zero
  | minus => plus

@[simp] theorem neg_top : -(⊤ : Sign) = ⊥ := rfl
@[simp] theorem neg_zero : -(0 : Sign) = 0 := rfl
@[simp] theorem neg_bot : -(⊥ : Sign) = ⊤ := rfl

instance : InvolutiveNeg Sign where
  neg_neg := by rintro (_ | _ | _) <;> simp

@[simp] theorem neg_eq_zero {x : Sign} : -x = 0 ↔ x = 0 := neg_inj (b := (0 : Sign))

/-- Turns a sign into an integer in the obvious way. -/
def toInt : Sign → ℤ
  | plus => 1
  | zero => 0
  | minus => -1

@[simp] theorem toInt_plus : toInt ⊤ = 1 := rfl
@[simp] theorem toInt_zero : toInt 0 = 0 := rfl
@[simp] theorem toInt_minus : toInt ⊥ = -1 := rfl

theorem toInt_injective : Function.Injective toInt := by
  rintro (_ | _ | _) (_ | _ | _) <;> simp

@[simp]
theorem toInt_inj {x y : Sign} : toInt x = toInt y ↔ x = y :=
  toInt_injective.eq_iff

instance : LinearOrder Sign :=
  .lift' _ toInt_injective

instance : OrderBot Sign where
  bot_le := by rintro (_ | _ | _) <;> change toInt _ ≤ toInt _ <;> simp

instance : OrderTop Sign where
  le_top := by rintro (_ | _ | _) <;> change toInt _ ≤ toInt _ <;> simp

end Sign

/-! ### Sign sequences -/

/-- A sign sequence is a sequence `Ordinal → Sign`, which is equal to `0` after some point, and only
takes `⊥` or `⊤` as values before that point.

Sign sequences are ordered lexicographically. We show that sign sequences are order-isomorphic to
the surreal numbers. -/
def SignSeq : Type (u + 1) :=
  Subtype fun s : Lex (Ordinal.{u} → Sign) ↦ ∃ l, ∀ a, s a = 0 ↔ l ≤ a

namespace SignSeq

instance : LinearOrder SignSeq :=
  inferInstanceAs (LinearOrder (Subtype _))

/-- Construct a sign sequence from a function. -/
def mk (s : Ordinal.{u} → Sign) (l : Ordinal) (h : ∀ o, s o = 0 ↔ l ≤ o) : SignSeq.{u} :=
  ⟨toLex s, ⟨l, h⟩⟩

instance : GetElem SignSeq Ordinal Sign (fun _ _ ↦ True) where
  getElem s o _ := ofLex s.1 o

@[simp]
theorem get_mk (s : Ordinal → Sign) (l : Ordinal) (h : ∀ o, s o = 0 ↔ l ≤ o) (o : Ordinal) :
    (mk s l h)[o] = s o :=
  rfl

@[ext]
theorem ext {s t : SignSeq} (h : ∀ o : Ordinal, s[o] = t[o]) : s = t :=
  Subtype.ext (funext h)

/-- The length of a sign sequence is the first ordinal `o` such that `s[o] = 0`. -/
def length (s : SignSeq) : Ordinal :=
  Classical.choose s.2

@[simp]
theorem get_eq_zero_iff {s : SignSeq} {o : Ordinal} : s[o] = 0 ↔ s.length ≤ o :=
  Classical.choose_spec s.2 o

theorem length_eq_iff {s : SignSeq} {a : Ordinal} : s.length = a ↔ ∀ o, s[o] = 0 ↔ a ≤ o := by
  simp_rw [get_eq_zero_iff]
  refine ⟨?_, eq_of_forall_ge_iff⟩
  rintro rfl _
  rfl

@[simp]
theorem length_mk (s : Ordinal.{u} → Sign) (l : Ordinal) (h : ∀ o, s o = 0 ↔ l ≤ o) :
    length (mk s l h) = l := by
  simpa [length_eq_iff]

/-- The constant `0` sequence. -/
instance : Zero SignSeq where
  zero := mk (fun _ ↦ 0) 0 (by simp)

@[simp] theorem get_zero (o : Ordinal) : (0 : SignSeq)[o] = 0 := rfl
@[simp] theorem length_zero : length 0 = 0 := length_mk ..

/-- The negative of a sign sequence is created by flipping all signs. -/
instance : Neg SignSeq where
  neg s := mk (fun a ↦ -s[a]) s.length (by simp)

@[simp] theorem get_neg (s : SignSeq) (o : Ordinal) : (-s)[o] = -s[o] := rfl
@[simp] theorem length_neg (s : SignSeq) : (-s).length = s.length := length_mk ..

/-- Append two sequences by putting one after the other ends. -/
instance : Append SignSeq where
  append s t := by
    refine mk (fun o ↦ if o < s.length then s[o] else t[o - s.length])
      (s.length + t.length) fun a ↦ ?_
    dsimp
    split <;> rename_i h
    · simp [h.not_le, (h.trans_le (Ordinal.le_add_right ..)).not_le]
    · rw [get_eq_zero_iff, ← add_le_add_iff_left s.length,
        Ordinal.add_sub_cancel_of_le (le_of_not_lt h)]

theorem get_append_of_lt (s t : SignSeq) {o : Ordinal} (h : o < s.length) : (s ++ t)[o] = s[o] :=
  if_pos h

theorem get_append_of_le (s t : SignSeq) {o : Ordinal} (h : s.length ≤ o) :
    (s ++ t)[o] = t[o - s.length] :=
  if_neg h.not_lt

@[simp]
theorem get_append_add (s t : SignSeq) (o : Ordinal) : (s ++ t)[s.length + o] = t[o] := by
  rw [get_append_of_le _ _ (Ordinal.le_add_right ..), Ordinal.add_sub_cancel]

@[simp]
theorem length_append (s t : SignSeq) : (s ++ t).length = s.length + t.length :=
  length_mk ..

end SignSeq
end
