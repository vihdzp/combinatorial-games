/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.SignExpansion.Topology

noncomputable section

open Ordinal

namespace NatOrdinal

/-- TODO: we're missing `Ordinal.toNat`. -/
def toNat (x : NatOrdinal) : ℕ :=
  if hx : x < of ω then Classical.choose (lt_omega0.1 hx) else 0

@[simp]
theorem toNat_natCast (n : ℕ) : toNat n = n := by
  rw [toNat, dif_pos]
  · generalize_proofs H
    rw [← Nat.cast_inj (R := NatOrdinal), ← Classical.choose_spec H]
  · exact natCast_lt_omega0 n

theorem toNat_lt_of_lt_natCast {x : NatOrdinal} {y : ℕ} (h : x < y) : x.toNat < y := by
  obtain ⟨n, rfl⟩ := eq_natCast_of_le_natCast h.le
  simpa using h

end NatOrdinal

namespace Simplicity

local instance : Coe Bool SignType where
  coe
  | true => 1
  | false => -1

@[simp]
theorem coe_ne_zero (b : Bool) : (b : SignType) ≠ 0 := by
  decide +revert

/-- Defines a sign sequence from a sequence `Fin n → Bool`. -/
def ofFin {n : ℕ} (f : Fin n → Bool) : Simplicity :=
  of {
    sign m := if h : m < n then f ⟨m.toNat, m.toNat_lt_of_lt_natCast h⟩ else 0
    isUpperSet_preimage_singleton_zero' := by
      convert isUpperSet_Ici (n : NatOrdinal)
      aesop
  }

/-- Defines a sign sequence from a sequence `ℕ → Bool`. -/
def ofNat (f : ℕ → Bool) : Simplicity :=
  of {
    sign m := if h : m < .of ω then f m.toNat else 0
    isUpperSet_preimage_singleton_zero' := by
      convert isUpperSet_Ici (NatOrdinal.of ω)
      aesop
  }

/-- The set of sign sequences with length ω with finitely many 1s. -/
def A : Set Simplicity := {x | x.val.length = NatOrdinal.of ω ∧ (x ⁻¹' {1}).Finite}

/-- The set of sign sequences with length ω with infinitely many 1s. -/
def B : Set Simplicity := {x | x.val.length = NatOrdinal.of ω ∧ (x ⁻¹' {1}).Infinite}

variable (U : Set Simplicity)

open Classical in
def chain (U : Set Simplicity) (n : ℕ) : Bool :=
  ofFin (fun x : Fin n ↦ chain U x) ∈ U

def chainFin (n : ℕ) : Simplicity :=
  ofFin fun x : Fin n ↦ chain U x

open Classical in
theorem chain_def (n : ℕ) : chain U n = decide (chainFin U n ∈ U) := by
  rw [chain]
  rfl

variable {U : Set Simplicity}

theorem infinite_setOf_chainFin_mem_U (hU : IsOpen U) (hUA : U ⊆ A) :
    {n | chainFin U n ∈ U}.Infinite :=
  sorry

theorem chain_mem_B (hU : IsOpen U) (hUA : U ⊆ A) : ofNat (chain U) ∈ B :=
  sorry

public theorem not_normalSpace_simplicity : ¬ NormalSpace Simplicity := by
  sorry

end Simplicity
end
