/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Surreal.Birthday.Basic
import CombinatorialGames.Surreal.Dedekind

/-!
# Surreal Birthday equals Game Birthday

TODO: write module docstring
-/

theorem RelHomClass.map_antisymmRel {α β F : Type*} {r : α → α → Prop} {s : β → β → Prop}
    [FunLike F α β] [RelHomClass F r s] {x y : α} {f : F} (h : AntisymmRel r x y) :
    AntisymmRel s (f x) (f y) := by
  exact ⟨RelHomClass.map_rel f h.left, RelHomClass.map_rel f h.right⟩

universe u

open Surreal Set Order

private inductive Reps : Type (u + 1) where
  | left (x : Surreal.{u}) : Reps
  | right (x : Surreal.{u}) : Reps
  | iInf (ι : Type u) (f : ι → Reps) : Reps
  | iSup (ι : Type u) (f : ι → Reps) : Reps

private noncomputable def repsBirthday (x : Reps) : WithTop (NatOrdinal.{u}) :=
  match x with
  | .left x => .some (x.birthday)
  | .right x => .some (x.birthday)
  | .iInf ι f => ⨆ i : ι, (repsBirthday (f i))
  | .iSup ι f => ⨆ i : ι, (repsBirthday (f i))

private noncomputable def repsBirthdays (x : Reps) : WithTop (NatOrdinal.{u}) :=
  match x with
  | .left x => .some (succ x.birthday)
  | .right x => .some (succ x.birthday)
  | .iInf ι f => ⨆ i : ι, (repsBirthdays (f i))
  | .iSup ι f => ⨆ i : ι, (repsBirthdays (f i))

private theorem repsBirthday_le_repsBirthdays (x : Reps) :
    repsBirthday x ≤ repsBirthdays x := by
  induction x with
  | left x
  | right x => simp [repsBirthday, repsBirthdays, le_succ]
  | iInf ι f ih
  | iSup ι f ih =>
    rw [repsBirthday, repsBirthdays]
    apply iSup_mono
    simp [ih]

private theorem repsBirthdays_le_succ_repsBirthday (x : Reps) :
    repsBirthdays x ≤ succ (repsBirthday x) := by
  induction x with
  | left x
  | right x => simp [repsBirthday, repsBirthdays]
  | iInf ι f ih
  | iSup ι f ih =>
    rw [repsBirthday, repsBirthdays, iSup_le_iff]
    intro i
    apply (ih i).trans
    apply succ_mono
    exact le_iSup (fun i => repsBirthday (f i)) i

private def repsCut (x : Reps) : Cut :=
  match x with
  | .left x => .leftSurreal x
  | .right x => .rightSurreal x
  | .iInf ι f => ⨅ i : ι, repsCut (f i)
  | .iSup ι f => ⨆ i : ι, repsCut (f i)

-- this could be a useful definition on its own
private noncomputable def simplestBtwn {l r : Cut.{u}} (hlr : l < r) : Surreal.{u} :=
  let push : Set NatOrdinal.{u} := Surreal.birthday '' (r.left ∩ l.right)
  let glb := sInf push
  have h : glb ∈ push := csInf_mem (Set.image_nonempty.2 hlr)
  h.choose

private theorem simplestBtwn_simplest {l r : Cut.{u}} (hlr : l < r) {c : Surreal.{u}}
    (hc : c ∈ r.left ∩ l.right) : (simplestBtwn hlr).birthday ≤ c.birthday := by
  unfold simplestBtwn
  generalize_proofs h
  rw [h.choose_spec.right]
  apply csInf_le'
  exact mem_image_of_mem Surreal.birthday hc

private theorem simplestBtwn_btwn {l r : Cut.{u}} (hlr : l < r) :
    simplestBtwn hlr ∈ r.left ∩ l.right := by
  unfold simplestBtwn
  generalize_proofs h
  exact h.choose_spec.left

private theorem toGame_simplestBtwn_of_lt {x : IGame} (h : Cut.iGameLeft x < Cut.iGameRight x) :
    toGame (simplestBtwn h) = Game.mk x := by
  obtain ⟨y, ny, hy, hbb⟩ := Surreal.birthday_eq_iGameBirthday (simplestBtwn h)
  rw [eq_comm, ← hy, toGame_mk, Game.mk_eq_mk]
  apply Cut.equiv_of_mem_iGameLeft_of_mem_iGameRight
  · rw [hy]
    exact (simplestBtwn_btwn h).right
  · rw [hy]
    exact (simplestBtwn_btwn h).left
  · intro z hz nz
    by_contra zz
    rw [← mem_compl_iff, Cut.compl_left] at zz
    have hzy : z < y := ny.leftMove_lt hz
    rw [← Surreal.mk_lt_mk] at hzy
    apply (IGame.birthday_lt_of_mem_leftMoves hz).not_ge
    rw [hbb]
    refine le_trans ?_ (birthday_mk_le z)
    refine simplestBtwn_simplest h ⟨?_, zz⟩
    apply Cut.isLowerSet_left hzy.le
    rw [hy]
    exact (simplestBtwn_btwn h).left
  · intro z hz nz
    by_contra zz
    rw [← mem_compl_iff, Cut.compl_right] at zz
    have hzy : y < z := ny.lt_rightMove hz
    rw [← Surreal.mk_lt_mk] at hzy
    apply (IGame.birthday_lt_of_mem_rightMoves hz).not_ge
    rw [hbb]
    refine le_trans ?_ (birthday_mk_le z)
    refine simplestBtwn_simplest h ⟨zz, ?_⟩
    apply Cut.isUpperSet_right hzy.le
    rw [hy]
    exact (simplestBtwn_btwn h).right

private inductive Rept : Type (u + 1) where
  | iInf (ι : Type u) (f : ι → Surreal.{u}) : Rept
  | iSup (ι : Type u) (f : ι → Surreal.{u}) : Rept

private def reptT (x : Rept.{u}) : Type u :=
  match x with
  | .iInf ι _
  | .iSup ι _ => ι

private def reptA (x : Rept.{u}) : reptT x → Surreal.{u} :=
  match x with
  | .iInf _ f
  | .iSup _ f => f

private def reptCut (x : Rept.{u}) : Cut.{u} :=
  match x with
  | .iInf ι f => ⨅ i : ι, .leftSurreal (f i)
  | .iSup ι f => ⨆ i : ι, .rightSurreal (f i)

private noncomputable def reptBirthdays (x : Rept.{u}) : WithTop NatOrdinal.{u} :=
  match x with
  | .iInf ι f => ⨆ i : ι, succ (f i).birthday
  | .iSup ι f => ⨆ i : ι, succ (f i).birthday

private lemma auxAuxAux (x : Reps.{u}) :
    ∃ (y : Rept.{u}), reptCut y = repsCut x ∧ reptBirthdays y ≤ repsBirthdays x := by
  induction x with
  | left l =>
    refine ⟨.iInf PUnit fun _ => l, ?_, ?_⟩
    · simp [repsCut, reptCut]
    · simp [repsBirthdays, reptBirthdays]
  | right r =>
    refine ⟨.iSup PUnit fun _ => r, ?_, ?_⟩
    · simp [repsCut, reptCut]
    · simp [repsBirthdays, reptBirthdays]
  | iInf ι f ih =>
    choose g hc hb using ih
    by_cases hmin : ∃ k, Minimal (· ∈ range (reptCut ∘ g)) k
    · obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hmin
      refine ⟨g k, ?_, ?_⟩
      · simp only [mem_range, Function.comp_apply, forall_exists_index,
          forall_apply_eq_imp_iff] at hk
        rw [repsCut]
        apply le_antisymm
        · apply le_iInf
          peel hk with i hi
          rw [← hc]
          by_contra! hik
          exact hik.not_ge (hi hik.le)
        · rw [hc]
          exact iInf_le (fun i => repsCut (f i)) k
      · rw [repsBirthdays]
        exact le_iSup_of_le k (hb k)
    · have hh (i : ι) : ∃ j : ι, ∃ c : reptT (g j),
          reptA (g j) c ∈ (reptCut (g i)).left ∧ ∃ w, reptA (g j) c ∈ (reptCut (g w)).right := by
        simp only [mem_range, Function.comp_apply, not_exists] at hmin
        simp_rw [Minimal] at hmin
        simp only [forall_exists_index, forall_apply_eq_imp_iff,
          not_and, not_forall, not_le, exists_prop, and_iff_right_of_imp le_of_lt] at hmin
        obtain ⟨k, hk⟩ := hmin i
        obtain ⟨l, hl⟩ := hmin k
        refine ⟨k, ?_⟩
        generalize huu : g k = uu at hk hl ⊢
        cases uu with
        | iInf κ n =>
          rw [reptCut, iInf_lt_iff] at hk
          peel hk with o ho
          obtain ⟨p, hpl, hpr⟩ := ho
          refine ⟨(reptCut (g i)).isLowerSet_left hpr hpl, k, ?_⟩
          rw [huu]
          simp only [reptCut, Cut.right_iInf, Cut.right_leftSurreal, reptA, mem_iUnion, mem_Ici]
          use o
        | iSup κ n =>
          rw [reptCut, lt_iSup_iff] at hl
          peel hl with o ho
          obtain ⟨p, hpl, hpr⟩ := ho
          obtain ⟨q, hql, hqr⟩ := hk
          rw [reptA]
          simp only [reptCut, Cut.right_iSup, Cut.right_rightSurreal, mem_iInter, mem_Ioi] at hqr
          refine ⟨(reptCut (g i)).isLowerSet_left (hqr o).le hql, l, ?_⟩
          exact (reptCut (g l)).isUpperSet_right (by simpa using hpl) hpr
      choose u m c w hw using hh
      refine ⟨.iInf ι fun i => reptA (g (u i)) (m i), ?_, ?_⟩
      · rw [repsCut, reptCut]
        simp_rw [← hc]
        apply le_antisymm
        · rw [le_iInf_iff]
          intro i
          apply iInf_le_of_le i
          rw [Cut.le_iff_left]
          intro j hj
          simp only [Cut.left_leftSurreal, mem_Iio] at hj
          exact (reptCut (g i)).isLowerSet_left hj.le (c i)
        · rw [le_iInf_iff]
          intro i
          apply iInf_le_of_le (w i)
          rw [Cut.le_iff_right]
          intro j hj
          simp only [Cut.right_leftSurreal, mem_Ici] at hj
          exact (reptCut (g (w i))).isUpperSet_right hj (hw i)
      · simp only [reptBirthdays, WithTop.succ_coe, repsBirthdays, iSup_le_iff]
        intro i
        apply le_iSup_of_le (u i)
        apply (hb (u i)).trans'
        generalize m i = j
        revert j
        generalize g (u i) = cc
        intro j
        cases cc with | _ =>
        rw [reptBirthdays]
        apply le_iSup_of_le j
        simp [reptA]
  | iSup ι f ih =>
    choose g hc hb using ih
    by_cases hmin : ∃ k, Maximal (· ∈ range (reptCut ∘ g)) k
    · obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hmin
      refine ⟨g k, ?_, ?_⟩
      · simp only [mem_range, Function.comp_apply, forall_exists_index,
          forall_apply_eq_imp_iff] at hk
        rw [repsCut]
        apply le_antisymm
        · rw [hc]
          exact le_iSup (fun i => repsCut (f i)) k
        · apply iSup_le
          peel hk with i hi
          rw [← hc]
          by_contra! hik
          exact hik.not_ge (hi hik.le)
      · rw [repsBirthdays]
        exact le_iSup_of_le k (hb k)
    · have hh (i : ι) : ∃ j : ι, ∃ c : reptT (g j),
          reptA (g j) c ∈ (reptCut (g i)).right ∧ ∃ w, reptA (g j) c ∈ (reptCut (g w)).left := by
        simp only [mem_range, Function.comp_apply, not_exists] at hmin
        simp_rw [Maximal] at hmin
        simp only [forall_exists_index, forall_apply_eq_imp_iff,
          not_and, not_forall, not_le, exists_prop, and_iff_right_of_imp le_of_lt] at hmin
        obtain ⟨k, hk⟩ := hmin i
        obtain ⟨l, hl⟩ := hmin k
        refine ⟨k, ?_⟩
        generalize huu : g k = uu at hk hl ⊢
        cases uu with
        | iInf κ n =>
          rw [reptCut, iInf_lt_iff] at hl
          peel hl with o ho
          obtain ⟨p, hpl, hpr⟩ := ho
          obtain ⟨q, hql, hqr⟩ := hk
          rw [reptA]
          simp only [reptCut, Cut.left_iInf, Cut.left_leftSurreal, mem_iInter, mem_Iio] at hql
          refine ⟨(reptCut (g i)).isUpperSet_right (hql o).le hqr, l, ?_⟩
          exact (reptCut (g l)).isLowerSet_left (by simpa using hpr) hpl
        | iSup κ n =>
          rw [reptCut, lt_iSup_iff] at hk
          peel hk with o ho
          obtain ⟨p, hpl, hpr⟩ := ho
          refine ⟨(reptCut (g i)).isUpperSet_right hpl hpr, k, ?_⟩
          rw [huu]
          simp only [reptCut, Cut.left_iSup, Cut.left_rightSurreal, reptA, mem_iUnion, mem_Iic]
          use o
      choose u m c w hw using hh
      refine ⟨.iSup ι fun i => reptA (g (u i)) (m i), ?_, ?_⟩
      · rw [repsCut, reptCut]
        simp_rw [← hc]
        apply le_antisymm
        · rw [iSup_le_iff]
          intro i
          apply le_iSup_of_le (w i)
          rw [Cut.le_iff_left]
          intro j hj
          simp only [Cut.left_rightSurreal, mem_Iic] at hj
          exact (reptCut (g (w i))).isLowerSet_left hj (hw i)
        · rw [iSup_le_iff]
          intro i
          apply le_iSup_of_le i
          rw [Cut.le_iff_right]
          intro j hj
          simp only [Cut.right_rightSurreal, mem_Ioi] at hj
          exact (reptCut (g i)).isUpperSet_right hj.le (c i)
      · simp only [reptBirthdays, WithTop.succ_coe, repsBirthdays, iSup_le_iff]
        intro i
        apply le_iSup_of_le (u i)
        apply (hb (u i)).trans'
        generalize m i = j
        revert j
        generalize g (u i) = cc
        intro j
        cases cc with | _ =>
        rw [reptBirthdays]
        apply le_iSup_of_le j
        simp [reptA]

private theorem simplestBtwnIndAux {l r : Reps.{u}} (h : repsCut l < repsCut r) :
    birthday (simplestBtwn h) ≤ max (repsBirthdays l) (repsBirthdays r) := by
  induction l generalizing r with
  | left l =>
    apply le_max_of_le_left
    rw [repsBirthdays, WithTop.coe_le_coe]
    refine (simplestBtwn_simplest h ⟨?_, by simp [repsCut]⟩).trans (le_succ l.birthday)
    obtain ⟨c, hcr, hcl⟩ := h
    simp only [repsCut, Cut.right_leftSurreal, mem_Ici] at hcl
    exact Cut.isLowerSet_left hcl hcr
  | right l =>
    induction r with
    | left r =>
      simp_rw [repsBirthdays, ← WithTop.coe_sup, WithTop.coe_le_coe]
      have h' := h
      simp_rw [repsCut] at h'
      obtain ⟨u, hur, hlu⟩ := h'
      simp at hlu hur
      have h' := hlu.trans hur
      let c := {{l} | {r}}ˢ
      have hl : l < c := left_lt_ofSets (mem_singleton l) _
      have hr : c < r := ofSets_lt_right (mem_singleton r) _
      rw [← Set.mem_Ioi, ← Cut.right_rightSurreal] at hl
      rw [← Set.mem_Iio, ← Cut.left_leftSurreal] at hr
      apply (simplestBtwn_simplest h ⟨hr, hl⟩).trans
      apply (birthday_ofSets_le _).trans
      rw [← Ordinal.NatOrdinal.iSup_subtype, ← Ordinal.NatOrdinal.iSup_subtype]
      simp
    | right r =>
      apply le_max_of_le_right
      rw [repsBirthdays, WithTop.coe_le_coe]
      refine (simplestBtwn_simplest h ⟨by simp [repsCut], ?_⟩).trans (le_succ r.birthday)
      obtain ⟨c, hcr, hcl⟩ := h
      simp only [repsCut, Cut.left_rightSurreal, mem_Iic] at hcr
      exact Cut.isUpperSet_right hcr hcl
    | iInf R r ihr =>

      sorry
    | iSup R r ihr => sorry
  | iInf L l ihl =>
    sorry
  | iSup L l ihl =>
    sorry

mutual

private noncomputable def iGameRepsLeft (x : IGame.{u}) :
    {r : Reps.{u} // repsCut r = .iGameLeft x ∧ repsBirthdays r ≤ x.birthday} := by
  refine ⟨.iSup (Shrink x.leftMoves) (Shrink.rec fun i => iGameRepRight i), ?_, ?_⟩
  · rw [repsCut, ← (equivShrink x.leftMoves).iSup_comp]
    conv =>
      enter [1, 1, i]
      rw [Shrink.rec_equivShrink, (iGameRepRight i).prop.left]
    rw [Cut.iGameLeft, iSup_subtype]
  · rw [repsBirthdays, iSup_le_iff, ← (equivShrink x.leftMoves).forall_congr_right]
    intro ⟨i, hi⟩
    rw [Shrink.rec_equivShrink]
    apply (repsBirthdays_le_succ_repsBirthday _).trans
    apply (succ_mono (iGameRepRight i).prop.right).trans
    rw [WithTop.succ_coe, WithTop.coe_le_coe, succ_le_iff]
    exact IGame.birthday_lt_of_mem_leftMoves hi
termination_by (x, 0)
decreasing_by igame_wf

private noncomputable def iGameRepsRight (x : IGame.{u}) :
    {r : Reps.{u} // repsCut r = .iGameRight x ∧ repsBirthdays r ≤ x.birthday} := by
  refine ⟨.iInf (Shrink x.rightMoves) (Shrink.rec fun i => iGameRepLeft i), ?_, ?_⟩
  · rw [repsCut, ← (equivShrink x.rightMoves).iInf_comp]
    conv =>
      enter [1, 1, i]
      rw [Shrink.rec_equivShrink, (iGameRepLeft i).prop.left]
    rw [Cut.iGameRight, iInf_subtype]
  · rw [repsBirthdays, iSup_le_iff, ← (equivShrink x.rightMoves).forall_congr_right]
    intro ⟨i, hi⟩
    rw [Shrink.rec_equivShrink]
    apply (repsBirthdays_le_succ_repsBirthday _).trans
    apply (succ_mono (iGameRepLeft i).prop.right).trans
    rw [WithTop.succ_coe, WithTop.coe_le_coe, succ_le_iff]
    exact IGame.birthday_lt_of_mem_rightMoves hi
termination_by (x, 0)
decreasing_by igame_wf

private noncomputable def iGameRepLeft (x : IGame.{u}) :
    {r : Reps.{u} // repsCut r = .leftGame (.mk x) ∧ repsBirthday r ≤ x.birthday} := by
  refine ⟨if h : repsCut (iGameRepsLeft x) < repsCut (iGameRepsRight x) then
    .left (simplestBtwn h) else iGameRepsLeft x, ?_, ?_⟩
  · simp_rw [apply_dite repsCut, (iGameRepsLeft x).prop.left, (iGameRepsRight x).prop.left]
    split_ifs with h
    · rw [repsCut, ← Cut.leftGame_toGame]
      apply congrArg Cut.leftGame
      exact toGame_simplestBtwn_of_lt h
    · rw [not_lt] at h
      exact (Cut.leftGame_eq_iGameLeft_of_le h).symm
  · split_ifs with h
    · rw [repsBirthday]
      apply (simplestBtwnIndAux h).trans
      rw [max_le_iff]
      exact ⟨(iGameRepsLeft x).prop.right, (iGameRepsRight x).prop.right⟩
    · apply (repsBirthday_le_repsBirthdays _).trans
      exact (iGameRepsLeft x).prop.right
termination_by (x, 1)

private noncomputable def iGameRepRight (x : IGame.{u}) :
    {r : Reps.{u} // repsCut r = .rightGame (.mk x) ∧ repsBirthday r ≤ x.birthday} := by
  refine ⟨if h : repsCut (iGameRepsLeft x) < repsCut (iGameRepsRight x) then
    .right (simplestBtwn h) else iGameRepsRight x, ?_, ?_⟩
  · simp_rw [apply_dite repsCut, (iGameRepsLeft x).prop, (iGameRepsRight x).prop]
    split_ifs with h
    · rw [repsCut, ← Cut.rightGame_toGame]
      apply congrArg Cut.rightGame
      exact toGame_simplestBtwn_of_lt h
    · rw [not_lt] at h
      exact (Cut.rightGame_eq_iGameRight_of_le h).symm
  · split_ifs with h
    · rw [repsBirthday]
      apply (simplestBtwnIndAux h).trans
      rw [max_le_iff]
      exact ⟨(iGameRepsLeft x).prop.right, (iGameRepsRight x).prop.right⟩
    · apply (repsBirthday_le_repsBirthdays _).trans
      exact (iGameRepsRight x).prop.right
termination_by (x, 1)

end

theorem Surreal.birthday_toGame_eq (x : Surreal) :
    x.toGame.birthday = x.birthday := by
  apply x.birthday_toGame_le.antisymm
  obtain ⟨i, hi, hbb⟩ := x.toGame.birthday_eq_iGameBirthday
  obtain ⟨j, nj, rfl, hj⟩ := x.birthday_eq_iGameBirthday
  rw [← hbb]
  have h₁ := (iGameRepLeft i).prop.right
  simp_rw [iGameRepLeft, (iGameRepsLeft i).prop.left, (iGameRepsRight i).prop.left] at h₁
  have h : Cut.iGameLeft i < Cut.iGameRight i := by
    by_contra! h
    have u₁ := Cut.leftGame_eq_iGameLeft_of_le h
    have u₂ := Cut.rightGame_eq_iGameRight_of_le h
    rw [← u₁, ← u₂, ← not_lt, Cut.leftGame_lt_rightGame_iff] at h
    apply h
    rw [mem_range]
    exact ⟨.mk j, hi.symm⟩
  rw [dif_pos h, repsBirthday, WithTop.coe_le_coe] at h₁
  apply h₁.trans_eq'
  obtain ⟨k, nk, hk, uu⟩ := (simplestBtwn h).birthday_eq_iGameBirthday
  apply congrArg birthday
  rw [toGame_mk, Game.mk_eq_mk] at hi
  rw [← hk, Surreal.mk_eq_mk]
  apply hi.symm.trans
  apply Cut.equiv_of_mem_iGameLeft_of_mem_iGameRight
  · rw [hk]
    exact (simplestBtwn_btwn h).right
  · rw [hk]
    exact (simplestBtwn_btwn h).left
  · intro z hz nz
    by_contra hu
    rw [← mem_compl_iff, Cut.compl_left] at hu
    have hv : mk z ∈ (Cut.iGameRight i).left := by
      apply (Cut.iGameRight i).isLowerSet_left (mk_le_mk.2 (IGame.Numeric.leftMove_lt hz).le)
      rw [hk]
      exact (simplestBtwn_btwn h).left
    have hc := simplestBtwn_simplest h ⟨hv, hu⟩
    rw [← uu] at hc
    exact (IGame.birthday_lt_of_mem_leftMoves hz).not_ge (hc.trans (birthday_mk_le z))
  · intro z hz nz
    by_contra hu
    rw [← mem_compl_iff, Cut.compl_right] at hu
    have hv : mk z ∈ (Cut.iGameLeft i).right := by
      apply (Cut.iGameLeft i).isUpperSet_right (mk_le_mk.2 (IGame.Numeric.lt_rightMove hz).le)
      rw [hk]
      exact (simplestBtwn_btwn h).right
    have hc := simplestBtwn_simplest h ⟨hu, hv⟩
    rw [← uu] at hc
    exact (IGame.birthday_lt_of_mem_rightMoves hz).not_ge (hc.trans (birthday_mk_le z))
