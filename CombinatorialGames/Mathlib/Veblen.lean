/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.SetTheory.Ordinal.Veblen
import Mathlib.Tactic.Order

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

attribute [aesop simp] Function.update_apply
  Finsupp.single_apply Finsupp.erase_apply mem_lowerBounds IsLeast
attribute [simp] Ordinal.add_eq_zero_iff
attribute [grind =] Pi.add_apply

namespace Finsupp
variable {α β : Type*} [AddZeroClass β]

open Classical in
@[aesop simp, grind =]
theorem update_apply' (f : α →₀ β) (a b i) : (f.update a b) i = if i = a then b else f i := by
  classical exact update_apply ..

theorem update_add_of_notMem_left {f g : α →₀ β} {x : α} (h : x ∉ support f) (y : β) :
    update (f + g) x y = f + update g x y := by
  aesop

theorem update_add_of_notMem_right {f g : α →₀ β} {x : α} (h : x ∉ support g) (y : β) :
    update (f + g) x y = update f x y + g := by
  aesop

@[simp]
theorem update_single (x : α) (y z : β) : update (single x y) x z = single x z := by
  aesop

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

theorem veblenWith₀_of_isLeast (f : Ordinal → Ordinal) {g : Ordinal →₀ Ordinal}
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

theorem veblenWith₀_add_single_add_single (f : Ordinal → Ordinal) {g : Ordinal →₀ Ordinal}
    {e a b : Ordinal} (he : e ≠ 0) (ha : a ≠ 0) (hg : ∀ i ∈ g.support, e < i) :
    veblenWith₀ f (g + single e a + single 0 b) = derivFamily (fun (x : Set.Iio a × Set.Iio e) o ↦
      veblenWith₀ f (g + single e x.1.1 + single x.2.1 o)) b := by
  have : g 0 = 0 := by
    contrapose! hg
    exact ⟨0, by simpa, bot_le⟩
  have : g e = 0 := by
    contrapose! hg
    exact ⟨e, by simpa, le_rfl⟩
  have : (g + single e a + single 0 b :) 0 = b := by simp_all
  have : (g + single e a + single 0 b :) e = a := by simp_all
  rw [veblenWith₀_of_isLeast f e]
  · congr!
    rw [erase_eq_update_zero, update_add_of_notMem_left, update_single, single_zero, add_zero,
      update_add_of_notMem_left, update_single]
    · congr!
    · grind
    · simp_all
  · refine ⟨?_, fun x hx ↦ ?_⟩
    · simp_all
    · contrapose! hg
      refine ⟨x, ?_, hg.le⟩
      simp only [mem_diff, SetLike.mem_coe, mem_support_iff, coe_add] at hx
      grind

theorem veblenWith₀_add_single (f : Ordinal.{u} → Ordinal.{u}) {g : Ordinal.{u} →₀ Ordinal.{u}}
    {e a : Ordinal} (he : e ≠ 0) (ha : a ≠ 0) (hg : ∀ i ∈ g.support, e < i) :
    veblenWith₀ f (g + single e a) = derivFamily (fun (x : Set.Iio a × Set.Iio e) o ↦
      veblenWith₀ f (g + single e x.1.1 + single x.2.1 o)) 0 := by
  simpa using veblenWith₀_add_single_add_single (b := 0) f he ha hg

variable {f}

private theorem isNormal_veblenWith₀_zero' (hf : IsNormal f) (g : Ordinal →₀ Ordinal)
    (he' : ∀ i ∈ g.support, 0 < i) :
    IsNormal fun o : Ordinal ↦ veblenWith₀ f (g + single 0 o) := by
  cases g using Finsupp.induction_on_min₂ with
  | h0 => simpa
  | ha e a g he ha =>
    have he₀ : e ≠ 0 := by
      specialize he' e
      aesop
    simp_rw [veblenWith₀_add_single_add_single f he₀ ha he]
    exact isNormal_derivFamily ..

theorem isNormal_veblenWith₀_zero (hf : IsNormal f) (g : Ordinal →₀ Ordinal) :
    IsNormal fun o : Ordinal ↦ veblenWith₀ f (g + single 0 o) := by
  conv_rhs => rw [← erase_add_single 0 g]
  simp_rw [add_assoc, ← single_add]
  have H : ∀ i ∈ (erase 0 g).support, 0 < i := by simp +contextual [pos_iff_ne_zero]
  exact (isNormal_veblenWith₀_zero' hf _ H).comp (isNormal_add_right (g 0))

mutual

theorem veblenWith₀_pos (hf : IsNormal f) (hp : 0 < f 0) (g : Ordinal →₀ Ordinal) :
    0 < veblenWith₀ f g := by
  sorry

theorem isNormal_veblenWith₀ (hf : IsNormal f) (hp : 0 < f 0) (g : Ordinal →₀ Ordinal) (e : Ordinal)
    (he' : ∀ i ∈ g.support, e < i) :
    IsNormal (fun o : Ordinal ↦ veblenWith₀ f (g + single e o)) := by
  obtain rfl | he := eq_or_ne e 0
  · exact isNormal_veblenWith₀_zero' hf g he'
  rw [isNormal_iff]
  refine ⟨fun a b hab ↦ ?_, fun o ho a IH ↦ ?_⟩
  · dsimp
    have H (i) (hi : i ∈ (g + single e a).support) : 0 < i := by
      specialize he' 0
      by_contra! hi
      simp_all
    let i : Iio b × Iio e := (⟨a, hab⟩, ⟨0, he.bot_lt⟩)
    rw [veblenWith₀_add_single (a := b) f he hab.ne_bot he',
      ← derivFamily_fp (i := i) (isNormal_veblenWith₀_zero' hf _ H)]
    conv_lhs => rw [← add_zero (_ + _), ← single_zero 0]
    apply (isNormal_veblenWith₀_zero' hf _ H).strictMono
    rw [← derivFamily_fp (i := i) (isNormal_veblenWith₀_zero' hf _ H)]
    dsimp [i]
    exact veblenWith₀_pos hf hp _
  · rw [veblenWith₀_add_single f he ho.ne_bot he', derivFamily_zero]
    refine nfpFamily_le fun l ↦ ?_
    suffices ∃ b < o, List.foldr _ 0 l ≤ veblenWith₀ f (g + single e b) by
      obtain ⟨b, hb, hb'⟩ := this
      exact hb'.trans (IH b hb)
    induction l with
    | nil => exact ⟨0, ho.bot_lt, by simp⟩
    | cons i l IH =>
      obtain ⟨j, hj, hj'⟩ := IH
      rw [List.foldr_cons]
      refine ⟨_, ho.add_one_lt (max_lt i.1.2 hj), ?_⟩



      sorry
termination_by toColex (g.mapRange ((↑) : Ordinal → WithTop Ordinal) rfl + single e ⊤)


theorem veblenWith₀_veblenWith₀_of_lt (hf : IsNormal f) (hp : 0 < f 0) (g : Ordinal →₀ Ordinal)
    {e e' a b c : Ordinal} (he : e' < e) (ha : a < b) (he' : ∀ i ∈ g.support, e < i) :
    veblenWith₀ f (g + single e a + single e' (veblenWith₀ f (g + single e b + single 0 c))) =
      veblenWith₀ f (g + single e b + single 0 c) := by
  rw [veblenWith₀_add_single_add_single f he.ne_bot ha.ne_bot he']
  apply derivFamily_fp (ι := Iio b × Iio e) (i := (⟨a, ha⟩, ⟨e', he⟩))
    (f := fun x o ↦ veblenWith₀ f (g + single e x.1.1 + single x.2.1 o))
    (isNormal_veblenWith₀ hf hp ..) c
  simp only [mem_support_iff, coe_add] at he' ⊢
  grind

end


theorem veblenWith₀_veblenWith₀_of_lt' (hf : IsNormal f) (hp : 0 < f 0) (g : Ordinal →₀ Ordinal)
    {e e' a b : Ordinal} (he : e' < e) (ha : a < b) (he' : ∀ i ∈ g.support, e < i) :
    veblenWith₀ f (g + single e a + single e' (veblenWith₀ f (g + single e b))) =
      veblenWith₀ f (g + single e b) := by
  simpa using veblenWith₀_veblenWith₀_of_lt (c := 0) hf hp g he ha he'

theorem veblenWith₀_veblenWith₀_of_isLeast (hf : IsNormal f) (hp : 0 < f 0)
    (g : Ordinal →₀ Ordinal) (e e' a : Ordinal)
    (he : IsLeast g.support e) (he' : e' < e) (ha : a < g e) :
    veblenWith₀ f (g.update e a + single e' (veblenWith₀ f g)) = veblenWith₀ f g := by
  sorry

end VeblenWith

end Ordinal
