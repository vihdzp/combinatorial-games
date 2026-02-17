/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.SetTheory.Ordinal.Veblen

/-!
# Veblen multivariate function

This file defines the multivariate Veblen function `Ordinal.veblen₀`. This is a generalization of
the two-variable `Ordinal.veblen` function to "transfinitely many" arguments - more precisely,
instead of taking two ordinal-valued arguments, the function now takes a single `Ordinal →₀ Ordinal`
argument.

The definition of this function is somewhat convoluted. For a function `g : Ordinal →₀ Ordinal`, the
value `veblen₀ g` is computed as follows:

1. Save the value `a = g 0`, and erase the `0`-th entry from `g`.
2. Find the smallest element `e` in the support of `g`. If the support is empty, return `ω ^ a`.
3. Consider all of the functions `fun o ↦ veblen₀ (g.update e x + single y o)` for `x < g e` and
  `y < e`. This is a small set of normal functions, so we can enumerate their common fixed points.
4. `veblen₀ g` is the `a`-th fixed point of the set of functions found in step 3.

As some examples:

- `veblen₀ (single 0 x) = ω ^ x`
- `veblen₀ (single 1 a + single 0 b) = veblen a b`
- `veblen₀ (single 2 0 + single 0 x) = Γ_ x`
- `veblen₀ (single ω 0) = SVO`, the small Veblen ordinal.

The function `veblen₀ (single · 0)` is normal, and its first fixed point is called the LVO or the
large Veblen ordinal.

We also provide a version `Ordinal.veblenWith₀` which permits replacing the function `ω ^ a` by some
other normal function, matching `Ordinal.veblenWith`.
-/

universe u

attribute [aesop simp] Function.update_apply Finsupp.update_apply
  Finsupp.single_apply Finsupp.erase_apply mem_lowerBounds IsLeast
attribute [simp] Ordinal.add_eq_zero_iff

namespace Finsupp
variable {α β : Type*} [AddZeroClass β]

theorem update_add_single {f : α →₀ β} {x : α} (h : x ∉ support f) (y z : β) :
    update (f + single x y) x z = f + single x z := by
  classical aesop

end Finsupp

namespace Ordinal

open Finsupp Order Set

section VeblenWith
variable (f : Ordinal.{u} → Ordinal.{u})

/-- The multivariate Veblen function, using `f` as a starting point. -/
noncomputable def veblenWith₀ (f : Ordinal.{u} → Ordinal.{u}) (g : Ordinal.{u} →₀ Ordinal.{u}) :
    Ordinal.{u} :=
  let g' := g.erase 0
  if hg : g'.support.Nonempty then
    let e := g'.support.min' hg
    derivFamily
      (fun (x : Set.Iio (g e) × Set.Iio e) o ↦ veblenWith₀ f (g'.update e x.1 + single x.2.1 o))
      (g 0)
  else f (g 0)
termination_by wellFounded_lt.wrap (toColex g)
decreasing_by
· use e
  have H (j) (hj : e < j) : j ≠ x.2 := (hj.trans' x.2.2).ne'
  aesop

@[simp]
theorem veblenWith₀_single (x : Ordinal) : veblenWith₀ f (single 0 x) = f x := by
  simp [veblenWith₀]

@[simp]
theorem veblenWith₀_zero : veblenWith₀ f 0 = f 0 := by
  simpa using veblenWith₀_single f 0

theorem veblenWith₀_of_isLeast (f : Ordinal.{u} → Ordinal.{u}) {g : Ordinal.{u} →₀ Ordinal.{u}}
    (e : Ordinal) (he : IsLeast (g.support \ {0}) e) :
    veblenWith₀ f g = derivFamily
      (fun (x : Set.Iio (g e) × Set.Iio e) o ↦
        veblenWith₀ f ((g.erase 0).update e x.1 + single x.2.1 o))
      (g 0) := by
  have he' : (g.erase 0).support.Nonempty := ⟨e, by simpa [and_comm] using he.1⟩
  have : (g.erase 0).support.min' he' = e := by
    rw [Finset.min'_eq_iff]
    aesop
  rw [veblenWith₀, dif_pos he']
  dsimp
  congr!

theorem veblenWith₀_add_single_zero (f : Ordinal.{u} → Ordinal.{u}) {g : Ordinal.{u} →₀ Ordinal.{u}}
    {e a : Ordinal} (hg : 0 ∉ g.support) (he : IsLeast g.support e) :
    veblenWith₀ f (g + single 0 a) = derivFamily (fun (x : Set.Iio (g e) × Set.Iio e) o ↦
      veblenWith₀ f (g.update e x.1.1 + single x.2.1 o)) a := by
  rw [veblenWith₀_of_isLeast f e]
  · have : (g + single 0 a :) e = g e := by aesop
    congr! <;> aesop
  · aesop

theorem veblenWith₀_add_single (f : Ordinal.{u} → Ordinal.{u}) {g : Ordinal.{u} →₀ Ordinal.{u}}
    {e a : Ordinal} (he : e ≠ 0) (ha : a ≠ 0) (he' : ∀ i ∈ g.support, e < i) :
    veblenWith₀ f (g + single e a) = derivFamily (fun (x : Set.Iio a × Set.Iio e) o ↦
      veblenWith₀ f (g + single e x.1.1 + single x.2.1 o)) 0 := by
  have : g 0 = 0 := by
    contrapose! he'
    exact ⟨0, by simpa, bot_le⟩
  have : g e = 0 := by
    contrapose! he'
    exact ⟨e, by simpa, le_rfl⟩
  have : (g + single e a) 0 = 0 := by aesop
  have : (g + single e a) e = a := by aesop
  rw [veblenWith₀_of_isLeast f e]
  · congr!
    rw [erase_of_notMem_support, update_add_single]
    · congr!
    · grind
    · grind
  · refine ⟨?_, fun x hx ↦ ?_⟩
    · aesop
    · contrapose! he'
      refine ⟨x, ?_, he'.le⟩
      aesop

variable {f} (hf : IsNormal f) (hp : 0 < f 0)

mutual

theorem veblenWith₀_pos (g : Ordinal →₀ Ordinal) : 0 < veblenWith₀ f g := by
  sorry

theorem isNormal_veblenWith₀ (g : Ordinal →₀ Ordinal) (e : Ordinal)
    (he' : ∀ i ∈ g.support, e < i) :
    IsNormal (fun o : Ordinal ↦ veblenWith₀ f (g + single e o)) := by
  rw [isNormal_iff]
  constructor
  · intro a b hab
    dsimp
    sorry
  · sorry

theorem veblenWith₀_veblenWith₀ (g : Ordinal →₀ Ordinal) (e e' a : Ordinal)
    (he : IsLeast g.support e) (he' : e' < e) (ha : a < g e) :
    veblenWith₀ f (g.update e a + single e' (veblenWith₀ f g)) = veblenWith₀ f g := by
  sorry

end

end VeblenWith

end Ordinal
