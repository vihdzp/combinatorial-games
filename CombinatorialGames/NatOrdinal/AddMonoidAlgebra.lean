/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.NatOrdinal.Pow
public import Mathlib.Algebra.MonoidAlgebra.Defs

import Mathlib.SetTheory.Ordinal.CantorNormalForm

/-!
# Cantor normal form for `NatOrdinal`

We prove that `NatOrdinal` is isomorphic to `ℕ[NatOrdinal]` via Cantor normal forms. This formalizes
the standard definition of natural operations as "polynomial operations on the Cantor normal form".

## Main declarations

- `toAddMonoidAlgebraIso`: the isomorphism `NatOrdinal ≃+* ℕ[NatOrdinal]`.
- `ofAddMonoidAlgebra_def`: an explicit characterization of the map `ℕ[NatOrdinal] → NatOrdinal`.
-/

/-! ### For Mathlib -/

namespace Ordinal

/-- Converts an ordinal less than `ω` into a natural number, sending all infinite ordinals to zero.
-/
noncomputable def toNat (o : Ordinal) : ℕ :=
  if h : o < ω then Classical.choose (lt_omega0.1 h) else 0

@[simp]
theorem toNat_natCast (n : ℕ) : toNat n = n := by
  have h := natCast_lt_omega0 n
  rw [toNat, dite_eq_left h, ← @Nat.cast_inj Ordinal, ← Classical.choose_spec (lt_omega0.1 h)]

theorem natCast_toNat {o : Ordinal} (h : o < ω) : toNat o = o := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 h
  rw [toNat_natCast]

@[simp]
theorem toNat_zero : toNat 0 = 0 :=
  toNat_natCast 0

namespace CNF

theorem coeff_lt {b : Ordinal} (hb : 1 < b) (o e : Ordinal) : coeff b o e < b := by
  by_cases he : e ∈ (CNF b o).map Prod.fst
  · rw [List.mem_map, Prod.exists] at he
    obtain ⟨c, _, hc, rfl⟩ := he
    rw [coeff_of_mem_CNF hc]
    exact snd_lt hb hc
  · rw [coeff_of_notMem_CNF he]
    exact hb.pos

end CNF
end Ordinal

namespace Finsupp
variable {M N α : Type*} [AddZeroClass M]

theorem mapRange_single_add [AddZeroClass N] {f : M → N} {g : α →₀ M} {hf : f 0 = 0} {a : α} {b : M}
    (hg : a ∉ g.support) : mapRange f hf (single a b + g) = single a (f b) + mapRange f hf g := by
  ext e
  obtain rfl | he := eq_or_ne e a
  · rw [notMem_support_iff] at hg
    simp_all
  · simp [he]

@[simp]
theorem equivMapDomain_add {f : α ≃ N} {g₁ g₂ : α →₀ M} :
    equivMapDomain f (g₁ + g₂) = equivMapDomain f g₁ + equivMapDomain f g₂ := by
  ext; simp

end Finsupp

public noncomputable section

namespace NatOrdinal
open AddMonoidAlgebra Ordinal

/-- `(toAddMonoidAlgebra x).coeff e` returns the coefficient of `ω^ e` in `x`. This is a
specialization of `Ordinal.CNF.coeff`. -/
def toAddMonoidAlgebra (x : NatOrdinal) : ℕ[NatOrdinal] :=
  .ofCoeff <| ((CNF.coeff ω x.val).mapRange toNat toNat_zero).equivMapDomain of

@[simp]
private theorem coeff_toAddMonoidAlgebra (x e : NatOrdinal) :
    (toAddMonoidAlgebra x).coeff e = (CNF.coeff ω x.val e.val).toNat :=
  rfl

@[simp]
theorem toAddMonoidAlgebra_zero : toAddMonoidAlgebra 0 = 0 := by
  ext; simp

/-- Add a linear combination of powers of `ω` to create an ordinal. This is a specialization of
`Ordinal.CNF.eval`. -/
@[pp_nodot]
def ofAddMonoidAlgebra (x : ℕ[NatOrdinal]) : NatOrdinal :=
  of (CNF.eval ω ((x.coeff.mapRange (↑) Nat.cast_zero).equivMapDomain val))

@[simp]
theorem ofAddMonoidAlgebra_zero : ofAddMonoidAlgebra 0 = 0 := by
  simp [ofAddMonoidAlgebra]

@[simp]
theorem toAddMonoidAlgebra_ofAddMonoidAlgebra (x) :
    toAddMonoidAlgebra (ofAddMonoidAlgebra x) = x := by
  ext e
  simp only [ofAddMonoidAlgebra, coeff_toAddMonoidAlgebra, val_of]
  rw [CNF.coeff_eval one_lt_omega0] <;> simp

@[simp]
theorem ofAddMonoidAlgebra_toAddMonoidAlgebra (x) :
    ofAddMonoidAlgebra (toAddMonoidAlgebra x) = x := by
  rw [ofAddMonoidAlgebra, of_eq_iff]
  convert CNF.eval_coeff ..
  ext
  simp [natCast_toNat (CNF.coeff_lt one_lt_omega0 _ _)]

theorem toAddMonoidAlgebra_injective : Function.Injective toAddMonoidAlgebra :=
  Function.LeftInverse.injective (ofAddMonoidAlgebra_toAddMonoidAlgebra)

theorem ofAddMonoidAlgebra_injective : Function.Injective ofAddMonoidAlgebra :=
  Function.LeftInverse.injective (toAddMonoidAlgebra_ofAddMonoidAlgebra)

@[simp]
theorem toAddMonoidAlgebra_inj {x y} : toAddMonoidAlgebra x = toAddMonoidAlgebra y ↔ x = y :=
  toAddMonoidAlgebra_injective.eq_iff

@[simp]
theorem ofAddMonoidAlgebra_inj {x y} : ofAddMonoidAlgebra x = ofAddMonoidAlgebra y ↔ x = y :=
  ofAddMonoidAlgebra_injective.eq_iff

private theorem sum_add_index (x y : NatOrdinal →₀ ℕ) :
    (x + y).sum (fun o y ↦ y * ω^ o) = x.sum (fun o y ↦ y * ω^ o) + y.sum (fun o y ↦ y * ω^ o) :=
  Finsupp.sum_add_index' (by simp) (by simp [add_mul])

private theorem sum_sum_index (x : NatOrdinal →₀ ℕ) (f : NatOrdinal → ℕ → NatOrdinal →₀ ℕ) :
    (x.sum f).sum (fun o y ↦ y * ω^ o) = x.sum fun a b ↦ (f a b).sum (fun o y ↦ y * ω^ o) :=
  Finsupp.sum_sum_index (by simp) (by simp [add_mul])

open Finsupp in
theorem ofAddMonoidAlgebra_def (x) : ofAddMonoidAlgebra x = x.coeff.sum fun o y ↦ y * ω^ o := by
  cases x with | ofCoeff x
  induction x using induction_on_max with
  | zero => simp
  | single_add o n f hf hn IH =>
    rw [ofAddMonoidAlgebra, mapRange_single_add (by contrapose! hf; use o),
      equivMapDomain_add, equivMapDomain_single, CNF.eval_single_add', ← val_of (CNF.eval ..),
      of_omega0_opow_mul_natCast_add']
    · rw [coeff_ofCoeff, sum_add_index, ← IH, Finsupp.sum_single_index (by simp), mul_comm]
      simp [ofAddMonoidAlgebra]
    · apply CNF.eval_lt
      · simp
      · simpa using! hf
    · simpa using! hf

@[simp]
theorem ofAddMonoidAlgebra_single (x y) : ofAddMonoidAlgebra (single x y) = y * ω^ x := by
  simp [ofAddMonoidAlgebra_def]

@[simp]
theorem toAddMonoidAlgebra_wpow (x) : toAddMonoidAlgebra (ω^ x) = single x 1 := by
  simp [← ofAddMonoidAlgebra_inj]

/-- `toAddMonoidAlgebra` as a `RingEquiv`. -/
@[expose, simps!]
def toAddMonoidAlgebraIso : NatOrdinal ≃+* ℕ[NatOrdinal] :=
  .symm {
    toFun := ofAddMonoidAlgebra
    invFun := toAddMonoidAlgebra
    left_inv := toAddMonoidAlgebra_ofAddMonoidAlgebra
    right_inv := ofAddMonoidAlgebra_toAddMonoidAlgebra
    map_add' x y := by
      simp_rw [ofAddMonoidAlgebra_def]
      exact sum_add_index ..
    map_mul' x y := by
      simp_rw [ofAddMonoidAlgebra_def, Finsupp.sum_mul, AddMonoidAlgebra.mul_def, coeff_finsuppSum]
      rw [sum_sum_index]
      congr!
      rw [sum_sum_index]
      simp [Finsupp.mul_sum, wpow_add, ← mul_assoc, mul_comm]
  }

@[simp]
theorem toAddMonoidAlgebra_one : toAddMonoidAlgebra 1 = 1 :=
  toAddMonoidAlgebraIso.map_one

@[simp]
theorem ofAddMonoidAlgebra_one : ofAddMonoidAlgebra 1 = 1 :=
  toAddMonoidAlgebraIso.symm.map_one

@[simp]
theorem toAddMonoidAlgebra_add (x y) :
    toAddMonoidAlgebra (x + y) = toAddMonoidAlgebra x + toAddMonoidAlgebra y :=
  (toAddMonoidAlgebraIso).map_add x y

@[simp]
theorem ofAddMonoidAlgebra_add (x y) :
    ofAddMonoidAlgebra (x + y) = ofAddMonoidAlgebra x + ofAddMonoidAlgebra y :=
  (toAddMonoidAlgebraIso).symm.map_add x y

@[simp]
theorem toAddMonoidAlgebra_mul (x y) :
    toAddMonoidAlgebra (x * y) = toAddMonoidAlgebra x * toAddMonoidAlgebra y :=
  (toAddMonoidAlgebraIso).map_mul x y

@[simp]
theorem ofAddMonoidAlgebra_mul (x y) :
    ofAddMonoidAlgebra (x * y) = ofAddMonoidAlgebra x * ofAddMonoidAlgebra y :=
  (toAddMonoidAlgebraIso).symm.map_mul x y

end NatOrdinal
end
