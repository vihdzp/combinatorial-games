import CombinatorialGames.Surreal.HahnSeries.Basic

universe u

open IGame Order Set

attribute [-simp] Ordinal.add_one_eq_succ

noncomputable section

/-! ### Hahn series as games -/

namespace SurrealHahnSeries

/-- A common base for both `truncLT` and `truncGT`. -/
private def truncAux (x : SurrealHahnSeries) (R : ℝ → ℝ → Prop) : Set SurrealHahnSeries :=
  range fun i : (j : x.support) × {r // R r (x.coeff j)} ↦ x.trunc i.1 + single i.1 i.2

/-- We write `x ≺ y` whenever `x = y.trunc i + single i r` for some `i ∈ y.support` and
`r < y.coeff i`.

When `y.length` is a limit ordinal, the series with `x ≺ y` describe the left options of
`toIGame y`. -/
def truncLT (x : SurrealHahnSeries) : Set SurrealHahnSeries :=
  truncAux x (· < ·)

notation:50 x:50 " ≺ " y:50 => x ∈ truncLT y
recommended_spelling "truncLT" for "≺" in [«term_≺_»]

/-- We write `x ≻ y` whenever `x = y.trunc i + single i r` for some `i ∈ y.support` and
`r > y.coeff i`.

When `y.length` is a limit ordinal, the series with `x ≻ y` describe the right options of
`toIGame y`. -/
def truncGT (x : SurrealHahnSeries) : Set SurrealHahnSeries :=
  truncAux x (· > ·)

local notation:50 x:50 " ≻ " y:50 => x ∈ truncGT y
recommended_spelling "truncGT" for "≻" in [«term_≺_»]

private theorem truncAux_def {x y : SurrealHahnSeries} {R : ℝ → ℝ → Prop} :
    x ∈ truncAux y R ↔ ∃ i ∈ y.support, ∃ r : ℝ, R r (y.coeff i) ∧ y.trunc i + single i r = x := by
  simp [truncAux]

theorem truncLT_def {x y : SurrealHahnSeries} :
    x ≺ y ↔ ∃ i ∈ y.support, ∃ r : ℝ, r < y.coeff i ∧ y.trunc i + single i r = x :=
  truncAux_def

theorem truncGT_def {x y : SurrealHahnSeries} :
    x ≻ y ↔ ∃ i ∈ y.support, ∃ r : ℝ, y.coeff i < r ∧ y.trunc i + single i r = x :=
  truncAux_def

theorem forall_mem_truncAux {y : SurrealHahnSeries}
    {P : SurrealHahnSeries → Prop} {R : ℝ → ℝ → Prop} :
    (∀ x ∈ truncAux y R, P x) ↔
      ∀ i ∈ y.support, ∀ r : ℝ, R r (y.coeff i) → P (y.trunc i + single i r) := by
  aesop (add simp [truncAux])

theorem forall_mem_truncLT {y : SurrealHahnSeries} {P : SurrealHahnSeries → Prop} :
    (∀ x ∈ truncLT y, P x) ↔
      ∀ i ∈ y.support, ∀ r : ℝ, r < y.coeff i → P (y.trunc i + single i r) :=
  forall_mem_truncAux

theorem forall_mem_truncGT {y : SurrealHahnSeries} {P : SurrealHahnSeries → Prop} :
    (∀ x ∈ truncGT y, P x) ↔
      ∀ i ∈ y.support, ∀ r : ℝ, y.coeff i < r → P (y.trunc i + single i r) :=
  forall_mem_truncAux

theorem exists_mem_truncAux {y : SurrealHahnSeries}
    {P : SurrealHahnSeries → Prop} {R : ℝ → ℝ → Prop} :
    (∃ x ∈ truncAux y R, P x) ↔
      ∃ i ∈ y.support, ∃ r : ℝ, R r (y.coeff i) ∧ P (y.trunc i + single i r) := by
  aesop (add simp [truncAux])

theorem exists_mem_truncLT {y : SurrealHahnSeries} {P : SurrealHahnSeries → Prop} :
    (∃ x ∈ truncLT y, P x) ↔
      ∃ i ∈ y.support, ∃ r : ℝ, r < y.coeff i ∧ P (y.trunc i + single i r) :=
  exists_mem_truncAux

theorem exists_mem_truncGT {y : SurrealHahnSeries} {P : SurrealHahnSeries → Prop} :
    (∃ x ∈ truncGT y, P x) ↔
      ∃ i ∈ y.support, ∃ r : ℝ, y.coeff i < r ∧ P (y.trunc i + single i r) :=
  exists_mem_truncAux

private theorem truncAux_zero (R : ℝ → ℝ → Prop) : truncAux 0 R = ∅ := by
  unfold truncAux; simp

@[simp] theorem truncLT_zero : truncLT 0 = ∅ := truncAux_zero _
@[simp] theorem truncGT_zero : truncGT 0 = ∅ := truncAux_zero _

private theorem trunc_add_single_truncAux {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    {R : ℝ → ℝ → Prop} (hi : i ∈ x.support) (hr : R r (x.coeff i)) :
    x.trunc i + single i r ∈ truncAux x R := by
  unfold truncAux
  aesop

theorem trunc_add_single_truncLT {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (hi : i ∈ x.support) (hr : r < x.coeff i) : x.trunc i + single i r ≺ x :=
  trunc_add_single_truncAux hi hr

theorem trunc_add_single_truncGT {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (hi : i ∈ x.support) (hr : x.coeff i < r) : x.trunc i + single i r ≻ x :=
  trunc_add_single_truncAux hi hr

instance small_truncAux (x : SurrealHahnSeries.{u}) (R : ℝ → ℝ → Prop) : Small.{u} (truncAux x R) :=
  by unfold truncAux; infer_instance

instance small_truncLT (x : SurrealHahnSeries.{u}) : Small.{u} (truncLT x) := small_truncAux ..
instance small_truncGT (x : SurrealHahnSeries.{u}) : Small.{u} (truncGT x) := small_truncAux ..

private theorem length_le_of_truncAux {x y : SurrealHahnSeries} {R : ℝ → ℝ → Prop}
    (h : x ∈ truncAux y R) : x.length ≤ y.length := by
  obtain ⟨⟨i, hi⟩, rfl⟩ := h
  apply (length_add_single_le ..).trans
  · rw [add_one_le_iff]
    exact length_trunc_lt i.2
  · simp

private theorem length_lt_of_truncAux {x y : SurrealHahnSeries} (hy : IsSuccPrelimit y.length)
    {R : ℝ → ℝ → Prop} (h : x ∈ truncAux y R) : x.length < y.length := by
  obtain ⟨⟨i, hi⟩, rfl⟩ := h
  apply (length_add_single_le ..).trans_lt
  · exact hy.add_one_lt <| length_trunc_lt i.2
  · simp

theorem length_le_of_truncLT {x y : SurrealHahnSeries} (h : x ≺ y) : x.length ≤ y.length :=
  length_le_of_truncAux h

theorem length_le_of_truncGT {x y : SurrealHahnSeries} (h : x ≻ y) : x.length ≤ y.length :=
  length_le_of_truncAux h

theorem length_lt_of_truncLT {x y : SurrealHahnSeries} (hy : IsSuccPrelimit y.length) (h : x ≺ y) :
    x.length < y.length :=
  length_lt_of_truncAux hy h

theorem length_lt_of_truncGT {x y : SurrealHahnSeries} (hy : IsSuccPrelimit y.length) (h : x ≻ y) :
    x.length < y.length :=
  length_lt_of_truncAux hy h

theorem lt_of_truncLT {x y : SurrealHahnSeries} (h : x ≺ y) : x < y := by
  obtain ⟨⟨⟨i, hi⟩, s, hs⟩, rfl⟩ := h
  rw [lt_def]
  use i
  aesop

theorem gt_of_truncGT {x y : SurrealHahnSeries} (h : x ≻ y) : y < x := by
  obtain ⟨⟨⟨i, hi⟩, s, hs⟩, rfl⟩ := h
  rw [lt_def]
  use i
  aesop

/-- The game that corresponds to a given surreal Hahn series.

This is an arbitrary representative for `SurrealHahnSeries.toSurreal`, which we use in its place
while we prove that this game is numeric. -/
@[coe]
def toIGame (x : SurrealHahnSeries.{u}) : IGame.{u} :=
  lengthRecOn x (fun _ i r _ _ IH ↦ IH + r * ω^ i.out) fun y hy IH ↦
    !{range fun i : truncLT y ↦ IH i <| length_lt_of_truncLT hy i.2 |
      range fun i : truncGT y ↦ IH i <| length_lt_of_truncGT hy i.2}

instance : Coe SurrealHahnSeries IGame where
  coe := toIGame

theorem toIGame_succ {x : SurrealHahnSeries}
    {i : Surreal} {r : ℝ} (hi : ∀ j ∈ x.support, i < j) (hr : r ≠ 0) :
    toIGame (x + single i r) = toIGame x + r * ω^ i.out :=
  lengthRecOn_succ hi hr

theorem toIGame_succ_equiv {x : SurrealHahnSeries}
    {i : Surreal} {r : ℝ} (hi : ∀ j ∈ x.support, i < j) :
    toIGame (x + single i r) ≈ toIGame x + r * ω^ i.out := by
  obtain rfl | hr := eq_or_ne r 0
  · rw [single_zero, add_zero, antisymmRel_comm, add_equiv_left_iff, ← Surreal.mk_eq_mk]
    simp
  · rw [toIGame_succ hi hr]

theorem toIGame_limit {x : SurrealHahnSeries.{u}} (hx : IsSuccPrelimit x.length) :
    toIGame x = !{toIGame '' truncLT x | toIGame '' truncGT x} := by
  simp_rw [image_eq_range]
  exact lengthRecOn_limit hx

@[simp]
theorem toIGame_zero : toIGame 0 = 0 := by
  rw [toIGame_limit] <;> aesop

theorem leftMoves_toIGame_limit {x : SurrealHahnSeries} (hx : IsSuccPrelimit x.length) :
    (toIGame x)ᴸ = toIGame '' truncLT x := by
  rw [toIGame_limit hx, leftMoves_ofSets]

theorem rightMoves_toIGame_limit {x : SurrealHahnSeries} (hx : IsSuccPrelimit x.length) :
    (toIGame x)ᴿ = toIGame '' truncGT x := by
  rw [toIGame_limit hx, rightMoves_ofSets]

private theorem toIGame_lt_toIGame_of_truncLT {x y : SurrealHahnSeries} (h : x ≺ y)
    [hy' : Numeric y] (IH : ∀ z, length z < y.length → Numeric z) :
    toIGame x < toIGame y := by
  induction y using lengthRecOn generalizing hy' x with
  | succ y i r hi hr IH' =>
    obtain ⟨⟨⟨j, hj⟩, s, hs⟩, rfl⟩ := h
    rw [coeff_add_apply] at hs
    replace hj := union_subset_union_right y.support support_single_subset (support_add_subset hj)
    have hij : i ≤ j := by rw [le_iff_lt_or_eq]; aesop
    dsimp
    rw [trunc_add, trunc_single_of_le hij, add_zero, toIGame_succ hi hr]
    grw [toIGame_succ_equiv (by simp)]
    obtain hj | rfl := hj
    · replace hij := hi _ hj
      rw [coeff_single_of_ne hij.ne, add_zero] at hs
      obtain ⟨t, ht, ht'⟩ := exists_between hs
      have hst : s * ω^ j.out ≈ t * ω^ j.out + ↑(s - t) * ω^ j.out := by
        rw [← Surreal.mk_eq_mk]
        simp [← add_mul]
      grw [hst, ← add_assoc]
      apply add_lt_add _ (Numeric.mul_wpow_lt_mul_wpow_of_neg ..)
      · grw [← toIGame_succ_equiv (by simp)]
        simp_rw [length_add_single hi hr, lt_add_one_iff] at IH
        have := IH _ le_rfl
        apply IH'
        · rw [truncLT_def]
          exact ⟨j, hj, t, ht', rfl⟩
        · exact fun z hz ↦ IH z hz.le
      · rwa [sub_neg]
      · rw [← Surreal.mk_lt_mk]
        simpa
    · rw [trunc_eq hi]
      have : y.coeff j = 0 := by
        by_contra h
        exact (hi _ h).false
      simpa [this] using hs
  | limit y hy IH' =>
    apply Numeric.left_lt
    rw [leftMoves_toIGame_limit hy]
    exact mem_image_of_mem _ h

-- TODO: can we more immediately prove this from the previous theorem?
private theorem toIGame_lt_toIGame_of_truncGT {x y : SurrealHahnSeries} (h : x ≻ y)
    [hy' : Numeric y] (IH : ∀ z, length z < y.length → Numeric z) :
    toIGame y < toIGame x := by
  induction y using lengthRecOn generalizing hy' x with
  | succ y i r hi hr IH' =>
    obtain ⟨⟨⟨j, hj⟩, s, hs⟩, rfl⟩ := h
    rw [coeff_add_apply] at hs
    replace hj := union_subset_union_right y.support support_single_subset (support_add_subset hj)
    have hij : i ≤ j := by rw [le_iff_lt_or_eq]; aesop
    dsimp
    rw [trunc_add, trunc_single_of_le hij, add_zero, toIGame_succ hi hr]
    grw [toIGame_succ_equiv (by simp)]
    obtain hj | rfl := hj
    · replace hij := hi _ hj
      rw [coeff_single_of_ne hij.ne, add_zero] at hs
      obtain ⟨t, ht', ht⟩ := exists_between hs
      have hst : s * ω^ j.out ≈ t * ω^ j.out + ↑(s - t) * ω^ j.out := by
        rw [← Surreal.mk_eq_mk]
        simp [← add_mul]
      grw [hst, ← add_assoc]
      apply add_lt_add _ (Numeric.mul_wpow_lt_mul_wpow_of_pos ..)
      · grw [← toIGame_succ_equiv (by simp)]
        simp_rw [length_add_single hi hr, lt_add_one_iff] at IH
        have := IH _ le_rfl
        apply IH'
        · rw [truncGT_def]
          exact ⟨j, hj, t, ht', rfl⟩
        · exact fun z hz ↦ IH z hz.le
      · rwa [sub_pos]
      · rw [← Surreal.mk_lt_mk]
        simpa
    · rw [trunc_eq hi]
      have : y.coeff j = 0 := by
        by_contra h
        exact (hi _ h).false
      simpa [this] using hs
  | limit y hy IH' =>
    apply Numeric.lt_right
    rw [rightMoves_toIGame_limit hy]
    exact mem_image_of_mem _ h

private theorem numeric_toIGame' (x : SurrealHahnSeries)
    (IH : ∀ {y z}, length y < x.length → length z < x.length →
      Numeric y ∧ Numeric z ∧ (y < z → toIGame y < toIGame z)) : Numeric x := by
  have IH' {y : SurrealHahnSeries} (hy : y.length < _) := (IH hy hy).1
  cases x using lengthRecOn with
  | succ x i r hi hr =>
    rw [toIGame_succ hi hr]
    have hx : x.length < (x + single i r).length := by
      rw [length_add_single hi hr, lt_add_one_iff]
    have := IH' hx
    infer_instance
  | limit _ hx =>
    rw [toIGame_limit hx, numeric_def]
    aesop (add apply forward safe [length_lt_of_truncLT, length_lt_of_truncGT,
      lt_of_truncLT, gt_of_truncGT, lt_trans])

private theorem toIGame_aux {o : Ordinal} {x y : SurrealHahnSeries}
    (_ : x.length < o) (_ : y.length < o) : Numeric x ∧ Numeric y ∧
      (x < y → toIGame x < toIGame y) := by
  have hx' := numeric_toIGame' x toIGame_aux
  have hy' := numeric_toIGame' y toIGame_aux
  have IHx (z) (hz : length z < x.length) : Numeric z := (toIGame_aux hz hz).1
  have IHy (z) (hz : length z < y.length) : Numeric z := (toIGame_aux hz hz).1
  refine ⟨hx', hy', fun h ↦ ?_⟩
  obtain ⟨i, hi, hi'⟩ := lt_def.1 h
  dsimp at *
  obtain hx | hx := eq_or_ne (x.coeff i) 0 <;> obtain hy | hy := eq_or_ne (y.coeff i) 0
  · simp_all
  · by_cases! H : ∀ j : x.support, i < j
    · apply toIGame_lt_toIGame_of_truncLT _ IHy
      rw [truncLT_def]
      use i, hy, x.coeff i, hi'
      ext j
      have (hj : j < i) : x.coeff j = 0 := by
        by_contra hj'
        exact (H ⟨_, hj'⟩).not_gt hj
      have := lt_trichotomy i j
      aesop
    · obtain ⟨⟨j, hj⟩, (hj' : j ≤ i), hij⟩ := wellFounded_gt.has_min {j : x.support | j ≤ i} H
      obtain rfl | hj' := hj'.eq_or_lt
      · cases hj hx
      · obtain ⟨r, hr⟩ := exists_gt (x.coeff j)
        trans ↑(x.trunc j + single j r)
        · apply toIGame_lt_toIGame_of_truncGT _ IHx
          rw [truncGT_def]
          use j, hj, r
        · rw [hx] at hi'
          obtain ⟨s, hs, hs'⟩ := exists_between hi'
          trans ↑(y.trunc i + single i s)
          · grw [toIGame_succ_equiv (by simp), toIGame_succ (by simp) hs.ne']
            apply add_lt_add_of_le_of_lt (le_of_eq _)
            · apply Numeric.mul_wpow_lt_mul_wpow_of_pos _ hs
              simpa [← Surreal.mk_lt_mk]
            · congr 1
              trans x.trunc i
              · refine trunc_eq_trunc hj'.le fun k hj hi ↦ ?_
                by_contra h
                exact hij ⟨_, h⟩ hi hj
              · aesop
          · apply toIGame_lt_toIGame_of_truncLT _ IHy
            rw [truncLT_def]
            use i, hy, s
  -- TODO: can we more immediately prove this case from the previous?
  · by_cases! H : ∀ j : y.support, i < j
    · apply toIGame_lt_toIGame_of_truncGT _ IHx
      rw [truncGT_def]
      use i, hx, y.coeff i, hi'
      ext j
      have (hj : j < i) : y.coeff j = 0 := by
        by_contra hj'
        exact (H ⟨_, hj'⟩).not_gt hj
      have := lt_trichotomy i j
      aesop
    · obtain ⟨⟨j, hj⟩, (hj' : j ≤ i), hij⟩ := wellFounded_gt.has_min {j : y.support | j ≤ i} H
      obtain rfl | hj' := hj'.eq_or_lt
      · cases hj hy
      · obtain ⟨r, hr⟩ := exists_lt (y.coeff j)
        trans ↑(y.trunc j + single j r)
        · rw [hy] at hi'
          obtain ⟨s, hs', hs⟩ := exists_between hi'
          trans ↑(x.trunc i + single i s)
          · apply toIGame_lt_toIGame_of_truncGT _ IHx
            rw [truncGT_def]
            use i, hx, s
          · grw [toIGame_succ (by simp) hs.ne, toIGame_succ_equiv (by simp)]
            apply add_lt_add_of_le_of_lt (le_of_eq _)
            · apply Numeric.mul_wpow_lt_mul_wpow_of_neg _ hs
              simpa [← Surreal.mk_lt_mk]
            · congr 1
              trans y.trunc i
              · aesop
              · symm
                refine trunc_eq_trunc hj'.le fun k hj hi ↦ ?_
                by_contra h
                exact hij ⟨_, h⟩ hi hj
        · apply toIGame_lt_toIGame_of_truncLT _ IHy
          rw [truncLT_def]
          use j, hj, r
  · obtain ⟨r, hr, hr'⟩ := exists_between hi'
    trans ↑(x.trunc i + single i r)
    · apply toIGame_lt_toIGame_of_truncGT _ IHx
      rw [truncGT_def]
      use i, hx, r
    · apply toIGame_lt_toIGame_of_truncLT _ IHy
      rw [truncLT_def]
      use i, hy, r, hr'
      aesop
termination_by o

instance numeric_toIGame (x : SurrealHahnSeries) : Numeric (toIGame x) :=
  (toIGame_aux (lt_add_one _) (lt_add_one _)).1

theorem toIGame_strictMono : StrictMono toIGame := by
  refine fun x y h ↦ (toIGame_aux (o := max (x.length + 1) (y.length + 1)) ?_ ?_).2.2 h <;> simp

@[simp, norm_cast]
theorem toIGame_lt_toIGame_iff {x y : SurrealHahnSeries} : toIGame x < toIGame y ↔ x < y :=
  toIGame_strictMono.lt_iff_lt

@[simp, norm_cast]
theorem toIGame_le_toIGame_iff {x y : SurrealHahnSeries} : toIGame x ≤ toIGame y ↔ x ≤ y :=
  toIGame_strictMono.le_iff_le

@[simp, norm_cast]
theorem toIGame_inj {x y : SurrealHahnSeries} : toIGame x = toIGame y ↔ x = y :=
  toIGame_strictMono.injective.eq_iff

theorem toIGame_equiv (x : SurrealHahnSeries) :
    toIGame x ≈ !{toIGame '' truncLT x | toIGame '' truncGT x} := by
  induction x using lengthRecOn with
  | succ x i r hi hr IH =>
    have hi' : i ∉ x.support := fun hi' ↦ (hi i hi').false
    apply Fits.equiv_of_forall_moves_of_equiv (
      !{toIGame '' truncLT x | toIGame '' truncGT x} +
      !{(fun s : ℝ ↦ s * ω^ i.out) '' Iio r | (fun s : ℝ ↦ s * ω^ i.out) '' Ioi r})
    · grw [toIGame_succ hi hr, Numeric.realCast_mul_wpow_equiv, IH]
    · constructor
      all_goals
        rw [moves_ofSets, forall_mem_image]
        intro y hy
      · simpa using lt_of_truncLT hy
      · simpa using gt_of_truncGT hy
    · simp_rw [forall_moves_add, moves_ofSets, Player.cases,
        forall_mem_image, exists_mem_image, forall_mem_truncLT, exists_mem_truncLT, trunc_add]
      constructor
      · intro j hj s hs
        obtain ⟨t, ht⟩ := exists_lt ((x + single i r).coeff i)
        refine ⟨i, ?_, t, ht, ?_⟩
        · simp_all
        · grw [← Numeric.realCast_mul_wpow_equiv, trunc_single_of_le le_rfl,
            ← toIGame_succ_equiv (by aesop), toIGame_le_toIGame_iff]
          refine (lt_def.2 ⟨j, fun k hk ↦ ?_, ?_⟩).le
          · dsimp
            rw [coeff_trunc_of_lt hk, coeff_trunc_of_lt ((hi _ hj).trans hk)]
            aesop
          · aesop
      · intro s hs
        obtain ⟨t, ht, ht'⟩ := exists_between (α := ℝ) hs
        refine ⟨i, ?_, t, ?_, ?_⟩
        · simp_all
        · simp_all
        · grw [trunc_single_of_le le_rfl, ← IH, toIGame_succ_equiv (by simp), trunc_eq hi]
          simpa using ht.le
    -- TODO: can we more immediately prove this case from the previous?
    · simp_rw [forall_moves_add, moves_ofSets, Player.cases,
        forall_mem_image, exists_mem_image, forall_mem_truncGT, exists_mem_truncGT, trunc_add]
      constructor
      · intro j hj s hs
        obtain ⟨t, ht⟩ := exists_gt ((x + single i r).coeff i)
        refine ⟨i, ?_, t, ht, ?_⟩
        · simp_all
        · grw [← Numeric.realCast_mul_wpow_equiv, trunc_single_of_le le_rfl,
            ← toIGame_succ_equiv (by aesop), toIGame_le_toIGame_iff]
          refine (lt_def.2 ⟨j, fun k hk ↦ ?_, ?_⟩).le
          · dsimp
            rw [coeff_trunc_of_lt hk, coeff_trunc_of_lt ((hi _ hj).trans hk)]
            aesop
          · aesop
      · intro s hs
        obtain ⟨t, ht, ht'⟩ := exists_between (α := ℝ) hs
        refine ⟨i, ?_, t, ?_, ?_⟩
        · simp_all
        · simp_all
        · grw [trunc_single_of_le le_rfl, ← IH, toIGame_succ_equiv (by simp), trunc_eq hi]
          simpa using ht'.le
  | limit x hx IH => rw [toIGame_limit hx]

instance numeric_ofSets_truncLT_truncGT (x : SurrealHahnSeries) :
    Numeric !{toIGame '' truncLT x | toIGame '' truncGT x} := by
  rw [numeric_def]
  constructor
  · simp_rw [moves_ofSets, Player.cases, forall_mem_image]
    intro i hi j hj
    exact_mod_cast (lt_of_truncLT hi).trans (gt_of_truncGT hj)
  · simp [numeric_toIGame]

/-- The surreal that corresponds to a given surreal Hahn series. -/
@[coe]
def toSurreal (x : SurrealHahnSeries) : Surreal :=
  .mk x

instance : Coe SurrealHahnSeries Surreal where
  coe := toSurreal

theorem toSurreal_strictMono : StrictMono toSurreal :=
  toIGame_strictMono

@[simp, norm_cast]
theorem toSurreal_lt_toSurreal_iff {x y : SurrealHahnSeries} : toSurreal x < toSurreal y ↔ x < y :=
  toIGame_lt_toIGame_iff

@[simp, norm_cast]
theorem toSurreal_le_toSurreal_iff {x y : SurrealHahnSeries} : toSurreal x ≤ toSurreal y ↔ x ≤ y :=
  toIGame_le_toIGame_iff

@[simp, norm_cast]
theorem toSurreal_inj {x y : SurrealHahnSeries} : toSurreal x = toSurreal y ↔ x = y :=
  toSurreal_strictMono.injective.eq_iff

@[simp]
theorem toSurreal_zero : toSurreal 0 = 0 := by simp [toSurreal]

theorem toSurreal_eq {x : SurrealHahnSeries.{u}} :
    toSurreal x = !{toSurreal '' truncLT x | toSurreal '' truncGT x}'(by
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      exact_mod_cast (lt_of_truncLT hi).trans (gt_of_truncGT hj)
    ) := by
  convert Surreal.mk_eq <| toIGame_equiv x
  rw [Surreal.mk_ofSets]
  congr <;> aesop

end SurrealHahnSeries

namespace Surreal

structure InitialSeg (x : Surreal) : Type _ where
  carrier : SurrealHahnSeries
  coeffIdx_eq_leadingCoeff_sub : ∀ i, carrier.coeffIdx i = (x - )

#exit

open Classical in
private def toSurrealHahnSeriesTrunc (x : Surreal) (i : Ordinal) : Iio i → Surreal × ℝ :=
  SuccOrder.prelimitRecOn (motive := fun i ↦ Iio i → Surreal × ℝ) i
    (fun i hi IH ↦ let y := x - IH.toSurreal; IH + .single y.wlog y.leadingCoeff)
    (fun i hi IH ↦ sorry)

/-- The **Conway normal form** of a surreal number. -/
def toSurrealHahnSeries (x : Surreal) : SurrealHahnSeries :=
  sorry

end Surreal
