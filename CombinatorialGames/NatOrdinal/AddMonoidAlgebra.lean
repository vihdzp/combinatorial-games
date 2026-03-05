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

We prove that `NatOrdinal` is isomorphic to `ℕ[NatOrdinal]` via Cantor normal forms.
-/

/-! ### For Mathlib -/

namespace Ordinal

/-- Converts an ordinal less than `ω` into a natural number, sending all infinite ordinals to zero.
-/
noncomputable def toNat (o : Ordinal) : ℕ :=
  if h : o < ω then Classical.choose (lt_omega0.1 h) else 0

@[simp]
theorem toNat_natCast (n : ℕ) : toNat n = n := by
  have h := nat_lt_omega0 n
  rw [toNat, dif_pos h, ← @Nat.cast_inj Ordinal, ← Classical.choose_spec (lt_omega0.1 h)]

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

namespace AddMonoidAlgebra
variable {R S T : Type*} [Semiring R]

@[simp] theorem coe_zero : ⇑(0 : R[S]) = 0 := rfl
theorem zero_apply (x : S) : (0 : R[S]) x = 0 := rfl

end AddMonoidAlgebra

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

@[simp]
theorem OrderIso.toEquiv_eq {α β : Type*} [Preorder α] [Preorder β] (f : α ≃o β) :
    EquivLike.toEquiv f = f.toEquiv :=
  rfl

public noncomputable section

namespace NatOrdinal
open AddMonoidAlgebra Ordinal

/-- `toAddMonoidAlgebra x e` returns the coefficient of `ω^ e` in `x`. This is a specialization of
`Ordinal.CNF.coeff`. -/
def toAddMonoidAlgebra (x : NatOrdinal) : ℕ[NatOrdinal] :=
  ((CNF.coeff ω x.val).mapRange toNat toNat_zero).equivMapDomain of

@[simp]
private theorem toAddMonoidAlgebra_apply (x e : NatOrdinal) :
    toAddMonoidAlgebra x e = (CNF.coeff ω x.val e.val).toNat :=
  rfl

@[simp]
theorem toAddMonoidAlgebra_zero : toAddMonoidAlgebra 0 = 0 := by
  ext; simp

/-- Add a linear combination of powers of `ω` to create an ordinal. This is a specialization of
`Ordinal.CNF.eval`. -/
@[pp_nodot]
def ofAddMonoidAlgebra (x : ℕ[NatOrdinal]) : NatOrdinal :=
  of (CNF.eval ω ((x.mapRange (↑) rfl).equivMapDomain val))

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem ofAddMonoidAlgebra_zero : ofAddMonoidAlgebra 0 = 0 := by
  simp [ofAddMonoidAlgebra]

@[simp]
theorem toAddMonoidAlgebra_ofAddMonoidAlgebra (x) :
    toAddMonoidAlgebra (ofAddMonoidAlgebra x) = x := by
  ext e
  simp only [ofAddMonoidAlgebra, OrderIso.toEquiv_eq, toAddMonoidAlgebra_apply, val_of]
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

open Finsupp in
set_option backward.isDefEq.respectTransparency false in
theorem ofAddMonoidAlgebra_def (x) : ofAddMonoidAlgebra x = x.sum fun o y ↦ y * ω^ o := by
  induction x using induction_on_max with
  | zero => simp
  | single_add o n f hf hn IH =>
    rw [ofAddMonoidAlgebra, mapRange_single_add (by contrapose! hf; use o),
      equivMapDomain_add, equivMapDomain_single, CNF.eval_single_add', ← val_of (CNF.eval ..),
      OrderIso.toEquiv_eq, RelIso.coe_fn_toEquiv, ← wpow_mul_natCast_add_of_lt']
    · rw [sum_add_index' (by simp) (by simp [add_mul]), ← IH,
        Finsupp.sum_single_index (by simp), mul_comm]
      rfl
    · apply CNF.eval_lt
      · simp
      · simpa using hf
    · simpa using hf

@[simp]
theorem ofAddMonoidAlgebra_single (x y) : ofAddMonoidAlgebra (single x y) = y * ω^ x := by
  simp [ofAddMonoidAlgebra_def]

@[simp]
theorem toAddMonoidAlgebra_wpow (x) : toAddMonoidAlgebra (ω^ x) = single x 1 := by
  simp [← ofAddMonoidAlgebra_inj]

set_option backward.isDefEq.respectTransparency false in
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
      apply Finsupp.sum_add_index'
      · simp
      · simp [add_mul]
    map_mul' x y := by
      simp_rw [ofAddMonoidAlgebra_def, Finsupp.sum_mul, AddMonoidAlgebra.mul_def]
      rw [Finsupp.sum_sum_index]
      · congr!
        rw [Finsupp.sum_sum_index]
        · simp [Finsupp.mul_sum, wpow_add, ← mul_assoc, mul_comm]
        · simp
        · simp [add_mul]
      · simp
      · simp [add_mul]
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
