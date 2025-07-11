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

private theorem simplestBtwnIndAux {l r : Reps.{u}} (h : repsCut l < repsCut r) :
    birthday (simplestBtwn h) ≤ max (repsBirthdays l) (repsBirthdays r) := by
  induction l generalizing r with
  | left l =>
    induction r with
    | left r =>
      simp_rw [repsBirthdays, ← WithTop.coe_sup, WithTop.coe_le_coe]
      have h' := h
      simp_rw [repsCut, OrderEmbedding.lt_iff_lt] at h'
      let c := {{l} | {r}}ˢ
      have hl : l < c := left_lt_ofSets (mem_singleton l) _
      have hr : c < r := ofSets_lt_right (mem_singleton r) _
      apply le_of_lt at hl
      rw [← Set.mem_Ici, ← Cut.right_leftSurreal] at hl
      rw [← Set.mem_Iio, ← Cut.left_leftSurreal] at hr
      apply (simplestBtwn_simplest h ⟨hr, hl⟩).trans
      apply (birthday_ofSets_le _).trans
      rw [← Ordinal.NatOrdinal.iSup_subtype, ← Ordinal.NatOrdinal.iSup_subtype]
      simp
    | right r =>
      simp_rw [repsBirthdays, ← WithTop.coe_sup, WithTop.coe_le_coe]
      have h' := h
      simp_rw [repsCut] at h'
      obtain ⟨u, hur, hlu⟩ := h'
      simp at hlu hur
      obtain hlr | h' := eq_or_lt_of_le (hlu.trans hur)
      · have hhl : simplestBtwn h = l := by
          simpa [← le_antisymm_iff, repsCut, hlr] using simplestBtwn_btwn h
        rw [hhl, hlr]
        simp [le_succ]
      let c := {{l} | {r}}ˢ
      have hl : l < c := left_lt_ofSets (mem_singleton l) _
      have hr : c ≤ r := (ofSets_lt_right (mem_singleton r) _).le
      apply le_of_lt at hl
      rw [← Set.mem_Ici, ← Cut.right_leftSurreal] at hl
      rw [← Set.mem_Iic, ← Cut.left_rightSurreal] at hr
      apply (simplestBtwn_simplest h ⟨hr, hl⟩).trans
      apply (birthday_ofSets_le _).trans
      rw [← Ordinal.NatOrdinal.iSup_subtype, ← Ordinal.NatOrdinal.iSup_subtype]
      simp
    | iInf R r =>
      sorry
    | iSup R r =>
      sorry
  | right l =>
    induction r with
    | left r => sorry
    | right r => sorry
    | iInf R r => sorry
    | iSup R r => sorry
  | iInf L l =>
    sorry
  | iSup L l =>
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
