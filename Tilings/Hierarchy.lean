import Tilings.Basic

/-!
# Hierarchies, compositions, powers (skeleton)

Statements of the blueprint nodes of `models.tex` and two nodes of
`crowns.tex`/`main.tex` that only need the basic model:

* `lem:localfinite`        — `PlaneTiling.locallyFinite`, `PlaneTiling.countable`
* `lem:finiteparents`      — `Substitution.iterate_support`, `Substitution.finite_parents`
* `lem:substitution-hierarchy` — `SubstitutionTiling.exists_composition`
* `lem:hierarchy-step`     — `hierarchical_power_iff`
* `lem:finite-idempotent`  — `FiniteMap.exists_idempotent_iterate` (proved)
* `lem:sts-flc`            — `Substitution.STS.finite_crowns`
* `lem:covered-tile-belongs` — `Patch.mem_of_carrier_subset_union`
* `lem:allowed-hierarchy`  — `allowed_crowns_hierarchy_is_substitutive`

All proofs except `FiniteMap.exists_idempotent_iterate` are `sorry`.
-/

open Set Pointwise Metric

noncomputable section

namespace Tilings

open Substitution

variable {P : Protoset}

/-! ## `lem:localfinite` -/

namespace PlaneTiling

/-- Step 1 of the blueprint proof of `locallyFinite`: Choose an open disk in the interior of
each form. The minimum of these finitely many positive radii is $r>0$. -/
private lemma locallyFinite_step1_radii :
    ∃ (c : P.Form → Pt) (r : ℝ), 0 < r ∧
      ∀ p : P.Form, ball (c p) r ⊆ interior (P.disk p).carrier := by
  have H : ∀ p : P.Form, ∃ x r, 0 < r ∧ ball x r ⊆ interior (P.disk p).carrier := by
    intro p
    have h_ne : (interior (P.disk p).carrier).Nonempty := (P.disk p).interior_nonempty
    obtain ⟨x, hx⟩ := h_ne
    have h_open : IsOpen (interior (P.disk p).carrier) := isOpen_interior
    rw [Metric.isOpen_iff] at h_open
    obtain ⟨r, hr, hsub⟩ := h_open x hx
    exact ⟨x, r, hr, hsub⟩
  choose c r hr hsub using H
  by_cases h_ne : Nonempty P.Form
  · have h_univ_ne : (Finset.univ : Finset P.Form).Nonempty := Finset.univ_nonempty
    obtain ⟨p0, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset P.Form) r h_univ_ne
    use c, r p0
    constructor
    · exact hr p0
    · intro p
      have h_le : r p0 ≤ r p := hmin p (Finset.mem_univ p)
      intro y hy
      have h_dist : dist y (c p) < r p := by
        calc dist y (c p) < r p0 := hy
          _ ≤ r p := h_le
      have h_ball : y ∈ ball (c p) (r p) := by exact h_dist
      exact hsub p h_ball
  · use (fun _ => (0:Pt)), 1
    constructor
    · exact zero_lt_one
    · intro p
      exfalso
      exact h_ne ⟨p⟩

/-- Step 2 of the blueprint proof of `locallyFinite`: the maximum of the form diameters
is $D<\infty$. -/
private lemma locallyFinite_step2_diameter :
    ∃ D : ℝ, ∀ p : P.Form, Bornology.IsBounded (P.disk p).carrier ∧
      ∀ x y, x ∈ (P.disk p).carrier → y ∈ (P.disk p).carrier → dist x y ≤ D := by
  have H1 : ∀ p : P.Form, Bornology.IsBounded (P.disk p).carrier := fun p =>
    (P.disk p).compact.isBounded
  have H2 : ∀ p : P.Form, ∃ D : ℝ, ∀ x, x ∈ (P.disk p).carrier → ∀ y, y ∈ (P.disk p).carrier → dist x y ≤ D := fun p =>
    Metric.isBounded_iff.mp (H1 p)
  choose d hd using H2
  by_cases h_emp : IsEmpty P.Form
  · exact ⟨0, fun p => (h_emp.false p).elim⟩
  · haveI : Nonempty P.Form := not_isEmpty_iff.mp h_emp
    have h_s : (Finset.univ : Finset P.Form).Nonempty := Finset.univ_nonempty
    let D_max := Finset.max' (Finset.image d Finset.univ) (Finset.Nonempty.image h_s d)
    use D_max
    intro p
    refine ⟨H1 p, fun x y hx hy => ?_⟩
    have hd_le : d p ≤ D_max := Finset.le_max' _ _ (Finset.mem_image_of_mem d (Finset.mem_univ p))
    exact le_trans (hd p x hx y hy) hd_le

/-- Step 3 of the blueprint proof of `locallyFinite`: If a tile meets a compact set $K$,
its chosen interior disk centre lies in the closed $D$-neighbourhood of $K$. -/
private lemma locallyFinite_step3_centres (T : PlaneTiling P) (K : Set Pt)
    (c : P.Form → Pt) (D : ℝ)
    (hc : ∀ p : P.Form, c p ∈ interior (P.disk p).carrier)
    (hD : ∀ p : P.Form, ∀ x y, x ∈ (P.disk p).carrier → y ∈ (P.disk p).carrier → dist x y ≤ D) :
    ∀ A ∈ T.tiles, (A.carrier ∩ K).Nonempty →
      ∃ x ∈ K, dist (A.anchor +ᵥ c A.form) x ≤ D := by
  intro A _ hK
  rcases hK with ⟨x, hx_car, hx_K⟩
  use x, hx_K
  rw [PlacedTile.carrier] at hx_car
  rcases hx_car with ⟨y, hy, hyx⟩
  rw [← hyx]
  rw [dist_vadd_cancel_left]
  apply hD A.form
  · have H := hc A.form
    exact interior_subset H
  · exact hy

private lemma locallyFinite_step4_separated_step1_dist (x y : Pt) (r : ℝ) (h : Disjoint (ball x r) (ball y r)) : 2 * r ≤ dist x y := by
  contrapose! h
  let m : Pt := (1/2 : ℝ) • (x + y)
  have hmx : dist m x = dist x y / 2 := by
    rw [dist_eq_norm, dist_eq_norm x y]
    have : (1/2 : ℝ) • (x + y) - x = (1/2 : ℝ) • (y - x) := by
      calc (1/2 : ℝ) • (x + y) - x = (1/2 : ℝ) • x + (1/2 : ℝ) • y - x := by rw [smul_add]
      _ = (1/2 : ℝ) • y + ((1/2 : ℝ) • x - x) := by abel
      _ = (1/2 : ℝ) • y + (-(1/2 : ℝ) • x) := by
        congr 1
        calc (1/2 : ℝ) • x - x = (1/2 : ℝ) • x - (1 : ℝ) • x := by rw [one_smul]
        _ = ((1/2 : ℝ) - 1) • x := by rw [sub_smul]
        _ = -(1/2 : ℝ) • x := by norm_num
      _ = (1/2 : ℝ) • y - (1/2 : ℝ) • x := by rw [neg_smul, sub_eq_add_neg]
      _ = (1/2 : ℝ) • (y - x) := by rw [smul_sub]
    rw [this, norm_smul, Real.norm_of_nonneg (by norm_num)]
    have : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
    rw [this]
    ring
  have hmy : dist m y = dist x y / 2 := by
    rw [dist_eq_norm, dist_eq_norm x y]
    have : (1/2 : ℝ) • (x + y) - y = (1/2 : ℝ) • (x - y) := by
      calc (1/2 : ℝ) • (x + y) - y = (1/2 : ℝ) • x + (1/2 : ℝ) • y - y := by rw [smul_add]
      _ = (1/2 : ℝ) • x + ((1/2 : ℝ) • y - y) := by abel
      _ = (1/2 : ℝ) • x + (-(1/2 : ℝ) • y) := by
        congr 1
        calc (1/2 : ℝ) • y - y = (1/2 : ℝ) • y - (1 : ℝ) • y := by rw [one_smul]
        _ = ((1/2 : ℝ) - 1) • y := by rw [sub_smul]
        _ = -(1/2 : ℝ) • y := by norm_num
      _ = (1/2 : ℝ) • x - (1/2 : ℝ) • y := by rw [neg_smul, sub_eq_add_neg]
      _ = (1/2 : ℝ) • (x - y) := by rw [smul_sub]
    rw [this, norm_smul, Real.norm_of_nonneg (by norm_num)]
    ring
  have hmx_lt : dist m x < r := by linarith [hmx, h]
  have hmy_lt : dist m y < r := by linarith [hmy, h]
  exact not_disjoint_iff.mpr ⟨m, mem_ball.mpr hmx_lt, mem_ball.mpr hmy_lt⟩

/-- Step 4 of the blueprint proof of `locallyFinite`: Centres belonging to distinct tiles
are at distance at least $2r$, since their open interior disks are disjoint. -/
private lemma locallyFinite_step4_separated (T : PlaneTiling P)
    (c : P.Form → Pt) (r : ℝ) (hr : 0 < r)
    (hball : ∀ p : P.Form, ball (c p) r ⊆ interior (P.disk p).carrier) :
    ∀ A B, A ∈ T.tiles → B ∈ T.tiles → A ≠ B →
      2 * r ≤ dist (A.anchor +ᵥ c A.form) (B.anchor +ᵥ c B.form) := by
  intro A B hA hB hne
  have _ := hr
  have h1 : ball (A.anchor +ᵥ c A.form) r ⊆ interior A.carrier := by
    have hc : A.carrier = A.anchor +ᵥ (P.disk A.form).carrier := rfl
    rw [hc, interior_vadd]
    intro x hx
    rcases mem_ball.mp hx with hx_dist
    rw [mem_vadd_set_iff_neg_vadd_mem]
    have h_in_ball : -A.anchor +ᵥ x ∈ ball (c A.form) r := by
      rw [mem_ball, dist_eq_norm] at *
      have : -A.anchor + x - c A.form = x - (A.anchor + c A.form) := by
        abel
      have h_vadd_1 : -A.anchor +ᵥ x = -A.anchor + x := by rfl
      have h_vadd_2 : A.anchor +ᵥ c A.form = A.anchor + c A.form := by rfl
      rw [h_vadd_1, h_vadd_2] at *
      rw [this]
      exact hx_dist
    exact hball A.form h_in_ball
  have h2 : ball (B.anchor +ᵥ c B.form) r ⊆ interior B.carrier := by
    have hc : B.carrier = B.anchor +ᵥ (P.disk B.form).carrier := rfl
    rw [hc, interior_vadd]
    intro x hx
    rcases mem_ball.mp hx with hx_dist
    rw [mem_vadd_set_iff_neg_vadd_mem]
    have h_in_ball : -B.anchor +ᵥ x ∈ ball (c B.form) r := by
      rw [mem_ball, dist_eq_norm] at *
      have : -B.anchor + x - c B.form = x - (B.anchor + c B.form) := by
        abel
      have h_vadd_1 : -B.anchor +ᵥ x = -B.anchor + x := by rfl
      have h_vadd_2 : B.anchor +ᵥ c B.form = B.anchor + c B.form := by rfl
      rw [h_vadd_1, h_vadd_2] at *
      rw [this]
      exact hx_dist
    exact hball B.form h_in_ball
  have h3 : Disjoint (interior A.carrier) (interior B.carrier) := by
    exact T.disjoint hA hB hne
  have h4 : Disjoint (ball (A.anchor +ᵥ c A.form) r) (ball (B.anchor +ᵥ c B.form) r) := by
    exact h3.mono h1 h2
  exact locallyFinite_step4_separated_step1_dist _ _ _ h4

/-- Step 5 of the blueprint proof of `locallyFinite`: A compact metric set has only
finitely many $2r$-separated points, by a finite cover with disks of radius $r/2$.
Here stated as: a set of $2r$-separated points in a closed $D$-neighbourhood of a
compact set is finite. -/
private lemma locallyFinite_step5_compact (K : Set Pt) (hK : IsCompact K)
    (D r : ℝ) (hr : 0 < r) (S : Set Pt) (hS_prox : ∀ A ∈ S, ∃ x ∈ K, dist A x ≤ D)
    (hS_sep : ∀ A B, A ∈ S → B ∈ S → A ≠ B → 2 * r ≤ dist A B) :
    S.Finite := by
  let cthick := Metric.cthickening (max D 0) K
  have h_bound : Bornology.IsBounded cthick := Bornology.IsBounded.cthickening hK.isBounded
  have h_closed : IsClosed cthick := Metric.isClosed_cthickening
  have h_comp : IsCompact cthick := isCompact_iff_isClosed_bounded.mpr ⟨h_closed, h_bound⟩
  have h_sub : S ⊆ cthick := by
    intro x hx
    obtain ⟨y, hyK, hyD⟩ := hS_prox x hx
    apply Metric.mem_cthickening_of_dist_le x y (max D 0) K hyK
    exact le_trans hyD (le_max_left D 0)
  have h_compS : TotallyBounded S := TotallyBounded.subset h_sub h_comp.totallyBounded
  obtain ⟨T, hT_fin, hT_cover⟩ := (Metric.totallyBounded_iff.mp h_compS) r hr
  have H : ∀ x : S, ∃ y ∈ T, dist (x : Pt) y < r := by
    intro x
    have hx' := hT_cover x.2
    rw [Set.mem_iUnion] at hx'
    rcases hx' with ⟨y, hy⟩
    rw [Set.mem_iUnion] at hy
    rcases hy with ⟨hyT, hy_ball⟩
    use y, hyT
    exact hy_ball
  let f : S → T := fun x => ⟨Classical.choose (H x), (Classical.choose_spec (H x)).1⟩
  have hf_inj : f.Injective := by
    intro x y hxy
    have h_neq : (x : Pt) = y := by
      by_contra h_neq
      have h1 := (Classical.choose_spec (H x)).2
      have h2 := (Classical.choose_spec (H y)).2
      have heq : Classical.choose (H x) = Classical.choose (H y) := by
        have hxy_f : f x = f y := hxy
        exact congrArg Subtype.val hxy_f
      rw [heq] at h1
      have H_dist_lt : dist (x : Pt) y < 2 * r := by
        calc
          dist (x : Pt) y ≤ dist (x : Pt) (Classical.choose (H y)) + dist (Classical.choose (H y)) (y : Pt) := dist_triangle _ _ _
          _ < r + r := add_lt_add h1 (by rw [dist_comm]; exact h2)
          _ = 2 * r := by ring
      have H_dist_ge : 2 * r ≤ dist (x : Pt) y := hS_sep x y x.2 y.2 h_neq
      linarith
    exact Subtype.ext h_neq
  haveI : Finite T := hT_fin.to_subtype
  haveI : Finite S := Finite.of_injective f hf_inj
  exact Set.toFinite S

/-- `lem:localfinite` (local finiteness): every compact set meets only
finitely many tiles of a plane tiling by a finite protoset. -/
theorem locallyFinite (T : PlaneTiling P) {K : Set Pt} (hK : IsCompact K) :
    {A ∈ T.tiles | (A.carrier ∩ K).Nonempty}.Finite := by
  obtain ⟨c, r, hr, hball⟩ := locallyFinite_step1_radii (P := P)
  obtain ⟨D, hD⟩ := locallyFinite_step2_diameter (P := P)
  have hc : ∀ p : P.Form, c p ∈ interior (P.disk p).carrier := fun p =>
    hball p (by rw [mem_ball, dist_self]; exact hr)
  let f := fun A : PlacedTile P => A.anchor +ᵥ c A.form
  let S := f '' {A ∈ T.tiles | (A.carrier ∩ K).Nonempty}
  have hS_prox : ∀ X ∈ S, ∃ x ∈ K, dist X x ≤ D := by
    intro X hX
    rcases hX with ⟨A, hA, rfl⟩
    exact locallyFinite_step3_centres T K c D hc (fun p => (hD p).2) A hA.1 hA.2
  have hS_sep : ∀ X Y, X ∈ S → Y ∈ S → X ≠ Y → 2 * r ≤ dist X Y := by
    intro X Y hX hY hne
    rcases hX with ⟨A, hA, rfl⟩
    rcases hY with ⟨B, hB, rfl⟩
    have hAB : A ≠ B := by
      rintro rfl
      exact hne rfl
    exact locallyFinite_step4_separated T c r hr hball A B hA.1 hB.1 hAB
  have S_fin : S.Finite := locallyFinite_step5_compact K hK D r hr S hS_prox hS_sep
  have h_inj : {A ∈ T.tiles | (A.carrier ∩ K).Nonempty}.InjOn f := by
    intro A hA B hB h_eq
    by_contra h_neq
    have h_dist : 2 * r ≤ dist (f A) (f B) :=
      locallyFinite_step4_separated T c r hr hball A B hA.1 hB.1 h_neq
    have h_dist2 : dist (f A) (f B) = 0 := by rw [h_eq, dist_self]
    linarith
  exact Finite.of_finite_image S_fin h_inj

/-- `lem:localfinite` (countability): a plane tiling has countably many tiles. -/
theorem countable (T : PlaneTiling P) : T.tiles.Countable := by
  have H_disj : T.tiles.PairwiseDisjoint (fun A => interior A.carrier) := T.disjoint
  have H_open : ∀ A ∈ T.tiles, IsOpen (interior A.carrier) := fun A _ => isOpen_interior
  have H_nonempty : ∀ A ∈ T.tiles, (interior A.carrier).Nonempty := by
    intro A _
    have hc : A.carrier = A.anchor +ᵥ (P.disk A.form).carrier := rfl
    rw [hc, interior_vadd]
    exact (P.disk A.form).interior_nonempty.image (A.anchor +ᵥ ·)
  exact H_disj.countable_of_isOpen H_open H_nonempty

end PlaneTiling

/-! ## `lem:finiteparents` -/

namespace Substitution

variable (τ : Substitution P)

/-- `lem:finiteparents` (supports): the support of the supertile `τ^n p`
(anchored at the origin) is `θ^n • B_p`. -/
private lemma iterate_support_translateSet (v : Pt) (S : Set (PlacedTile P)) :
    support (translateSet v S) = v +ᵥ support S := by
  ext x
  simp only [support, translateSet, PlacedTile.translate, PlacedTile.carrier, mem_iUnion,
    mem_image, mem_vadd_set_iff_neg_vadd_mem]
  constructor
  · rintro ⟨A, ⟨B, hB, rfl⟩, hx⟩
    exact ⟨B, hB, by simpa [←add_assoc] using hx⟩
  · rintro ⟨A, hA, hx⟩
    refine ⟨⟨A.form, v +ᵥ A.anchor⟩, ⟨A, hA, rfl⟩, ?_⟩
    simpa [←add_assoc] using hx

private lemma iterate_support_decomposeTile (A : PlacedTile P) :
    support (τ.decomposeTile A) = τ.θ • A.carrier := by
  dsimp [decomposeTile]
  rw [iterate_support_translateSet, τ.support_eq, PlacedTile.carrier]
  ext x
  simp only [mem_vadd_set_iff_neg_vadd_mem, mem_smul_set]
  constructor
  · rintro ⟨y, hy, hx⟩
    refine ⟨A.anchor + y, ?_, ?_⟩
    · simpa
    · rw [smul_add]
      calc τ.θ • A.anchor + τ.θ • y = τ.θ • A.anchor + (-(τ.θ • A.anchor) + x) := by congr 1
        _ = x := by abel
  · rintro ⟨y, hy, rfl⟩
    refine ⟨-A.anchor + y, ?_, ?_⟩
    · simpa
    · simp [smul_add]

private lemma iterate_support_decompose (S : Set (PlacedTile P)) :
    support (τ.decompose S) = τ.θ • support S := by
  dsimp [decompose, support]
  rw [smul_set_iUnion₂]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨A, ⟨B, hB, hA⟩, hx⟩
    refine ⟨B, hB, ?_⟩
    have h : x ∈ support (τ.decomposeTile B) := by
      simp only [support, mem_iUnion]
      exact ⟨A, hA, hx⟩
    rw [iterate_support_decomposeTile] at h
    exact h
  · rintro ⟨A, hA, hx⟩
    have h : x ∈ support (τ.decomposeTile A) := by
      rw [iterate_support_decomposeTile]
      exact hx
    simp only [support, mem_iUnion] at h
    rcases h with ⟨B, hB, hx'⟩
    exact ⟨B, ⟨A, hA, hB⟩, hx'⟩

theorem iterate_support (n : ℕ) (p : P.Form) :
    support (τ.supertile n p) = (τ.θ ^ n) • (P.disk p).carrier := by
  induction' n with n ih
  · dsimp [supertile, decomposeIter, support, PlacedTile.carrier]
    ext x
    simp
  · change support (τ.decompose (τ.supertile n p)) = τ.θ ^ (n + 1) • (P.disk p).carrier
    rw [iterate_support_decompose]
    rw [ih, smul_smul, pow_succ']

private lemma decomposeTile_inv_eq (B : PlacedTile P) :
    {A : PlacedTile P | B ∈ τ.decomposeTile A} =
    ⋃ (p : P.Form) (C ∈ (τ.rule p).tiles) (_h : C.form = B.form),
       { (⟨p, τ.θ⁻¹ • (B.anchor -ᵥ C.anchor)⟩ : PlacedTile P) } := by
  ext A
  simp only [decomposeTile, translateSet, PlacedTile.translate, mem_setOf_eq, mem_image, mem_iUnion,
    mem_singleton_iff]
  constructor
  · rintro ⟨C, hC, hB⟩
    use A.form, C, hC
    have h1 : C.form = B.form := by rw [← hB]
    use h1
    have h2 : τ.θ • A.anchor +ᵥ C.anchor = B.anchor := congrArg PlacedTile.anchor hB
    have h3 : τ.θ • A.anchor = B.anchor -ᵥ C.anchor := by rw [← h2, vadd_vsub]
    have h4 : τ.θ⁻¹ • τ.θ • A.anchor = τ.θ⁻¹ • (B.anchor -ᵥ C.anchor) := congrArg (τ.θ⁻¹ • ·) h3
    have h5 : τ.θ ≠ 0 := by linarith [τ.one_lt]
    have h6 : A.anchor = τ.θ⁻¹ • (B.anchor -ᵥ C.anchor) := by
      rw [← h4]
      exact (inv_smul_smul₀ h5 A.anchor).symm
    cases A
    dsimp at h6 ⊢
    subst h6
    rfl
  · rintro ⟨p, C, hC, h1, h2⟩
    have hp : p = A.form := congrArg PlacedTile.form h2.symm
    subst hp
    use C, hC
    have h3 : A.anchor = τ.θ⁻¹ • (B.anchor -ᵥ C.anchor) := congrArg PlacedTile.anchor h2
    cases B with
    | mk form anchor =>
      dsimp at h1
      subst h1
      have ht : { form := C.form, anchor := τ.θ • A.anchor +ᵥ C.anchor : PlacedTile P } =
          { form := C.form, anchor := anchor } := by
        congr 1
        dsimp at h3 ⊢
        rw [h3]
        have h5 : τ.θ ≠ 0 := by linarith [τ.one_lt]
        have h6 : (τ.θ • τ.θ⁻¹ • (anchor -ᵥ C.anchor : Pt) : Pt) = anchor -ᵥ C.anchor :=
          smul_inv_smul₀ h5 _
        exact Eq.trans (congrArg (· +ᵥ C.anchor) h6) (vsub_vadd anchor C.anchor)
      exact ht

/-- `lem:finiteparents` (finite parents): a fixed placed child has only
finitely many possible placed parents under `τ`. -/
theorem finite_parents (B : PlacedTile P) :
    {A : PlacedTile P | B ∈ τ.decomposeTile A}.Finite := by
  rw [decomposeTile_inv_eq]
  apply finite_iUnion
  intro p
  apply Finite.biUnion
  · exact (τ.rule p).finite
  · intro C _
    apply finite_iUnion
    intro _
    exact finite_singleton _

/-- Step 1 of the blueprint proof of `finite_crowns_step1_vertex`: if `w` is the vertex
around which the crown is taken, then a translated tile `A = B.translate (-w)` contains
`0` as a vertex if and only if `w` is a vertex of `B`. -/
private lemma finite_crowns_step1_vertex_step1_translate (B : PlacedTile P) (w : Pt) :
    (0 : Pt) ∈ (B.translate (-w)).vertexSet ↔ w ∈ B.vertexSet := by
  dsimp [PlacedTile.vertexSet]
  simp [PlacedTile.vertex, PlacedTile.translate, vadd_eq_add]
  constructor
  · rintro ⟨y, hy⟩
    use y
    calc B.anchor + (P.disk B.form).vertex y
      _ = w + (-w + B.anchor + (P.disk B.form).vertex y) := by abel
      _ = w + 0 := by rw [hy]
      _ = w := by abel
  · rintro ⟨y, hy⟩
    use y
    calc -w + B.anchor + (P.disk B.form).vertex y
      _ = -w + (B.anchor + (P.disk B.form).vertex y) := by abel
      _ = -w + w := by rw [hy]
      _ = 0 := by abel

/-- Step 1 of the blueprint proof of `finite_crowns_step1_vertex_step2_sts`: a vertex of a tile is in its carrier. -/
private lemma finite_crowns_step1_vertex_step2_sts_step1_vertex_mem_carrier {τ : Substitution P}
    (C : PlacedTile P) (v : Pt) (hv : v ∈ C.vertexSet) : v ∈ C.carrier := by
  have _ := τ
  rcases hv with ⟨i, rfl⟩
  apply vadd_mem_vadd_set
  apply (show segment ℝ ((P.disk C.form).vertex i)
      ((P.disk C.form).vertex (finRotate (P.disk C.form).n i)) ⊆
      frontier (P.disk C.form).carrier from by
    rw [(P.disk C.form).frontier_eq]
    exact subset_iUnion (fun j => segment ℝ ((P.disk C.form).vertex j)
      ((P.disk C.form).vertex (finRotate (P.disk C.form).n j))) i).trans
    (P.disk C.form).compact.isClosed.frontier_subset
  exact left_mem_segment ℝ _ _

/-- Step 2 of the blueprint proof of `finite_crowns_step1_vertex_step2_sts`: two distinct tiles in a supertile have disjoint interiors. -/
private lemma finite_crowns_step1_vertex_step2_sts_step2_disjoint {τ : Substitution P} (n : ℕ) (p : P.Form)
    (C B : PlacedTile P) (hC : C ∈ τ.supertile n p) (hB : B ∈ τ.supertile n p) (hne : C ≠ B) :
    Disjoint (interior C.carrier) (interior B.carrier) := by
  induction n generalizing C B with
  | zero =>
      change C ∈ ({⟨p, 0⟩} : Set (PlacedTile P)) at hC
      change B ∈ ({⟨p, 0⟩} : Set (PlacedTile P)) at hB
      rw [mem_singleton_iff] at hC hB
      subst C
      subst B
      exact (hne rfl).elim
  | succ n ih =>
      change C ∈ τ.decompose (τ.supertile n p) at hC
      change B ∈ τ.decompose (τ.supertile n p) at hB
      simp only [Substitution.decompose, mem_iUnion] at hC hB
      rcases hC with ⟨A, hA, hCA⟩
      rcases hB with ⟨D, hD, hBD⟩
      by_cases hAD : A = D
      · subst D
        have hne' : C ≠ B := hne
        rcases hCA with ⟨C₀, hC₀, rfl⟩
        rcases hBD with ⟨B₀, hB₀, rfl⟩
        have hne₀ : C₀ ≠ B₀ := by
          intro h
          apply hne'
          rw [h]
        have hd := (τ.rule A.form).disjoint hC₀ hB₀ hne₀
        have heqC : (C₀.translate (τ.θ • A.anchor)).carrier =
            (τ.θ • A.anchor) +ᵥ C₀.carrier := by
          ext x
          simp only [PlacedTile.carrier, PlacedTile.translate,
            mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_rev]
          rw [← add_assoc]
        have heqB : (B₀.translate (τ.θ • A.anchor)).carrier =
            (τ.θ • A.anchor) +ᵥ B₀.carrier := by
          ext x
          simp only [PlacedTile.carrier, PlacedTile.translate,
            mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_rev]
          rw [← add_assoc]
        rw [heqC, heqB, interior_vadd, interior_vadd]
        have hinj : Function.Injective (fun x : Pt => (τ.θ • A.anchor) + x) :=
          add_right_injective _
        have hd' := Set.disjoint_image_of_injective hinj hd
        simpa only [vadd_eq_add] using hd'
      · have hd := ih A D hA hD hAD
        have hθ : τ.θ ≠ 0 := by linarith [τ.one_lt]
        have hd' : Disjoint (interior (τ.θ • A.carrier))
            (interior (τ.θ • D.carrier)) := by
          rw [interior_smul₀ hθ, interior_smul₀ hθ]
          exact Set.disjoint_image_of_injective (smul_right_injective Pt hθ) hd
        have hCsub : interior C.carrier ⊆ interior (τ.θ • A.carrier) := by
          apply interior_mono
          intro x hx
          have hx' : x ∈ support (τ.decomposeTile A) := by
            simp only [support, mem_iUnion]
            exact ⟨C, hCA, hx⟩
          rw [iterate_support_decomposeTile] at hx'
          exact hx'
        have hBsub : interior B.carrier ⊆ interior (τ.θ • D.carrier) := by
          apply interior_mono
          intro x hx
          have hx' : x ∈ support (τ.decomposeTile D) := by
            simp only [support, mem_iUnion]
            exact ⟨B, hBD, hx⟩
          rw [iterate_support_decomposeTile] at hx'
          exact hx'
        exact hd'.mono hCsub hBsub

private lemma finite_crowns_step1_vertex_step2_sts_step3_not_interior_aux1 (A : PlacedTile P) :
    closure (interior A.carrier) = A.carrier := by
  unfold PlacedTile.carrier
  rw [interior_vadd, closure_vadd, (P.disk A.form).regular_closed]

/-- Step 3 of the blueprint proof of `finite_crowns_step1_vertex_step2_sts`: if a point is in
the carrier of one tile, it cannot be in the interior of a disjoint tile. -/
private lemma finite_crowns_step1_vertex_step2_sts_step3_not_interior {τ : Substitution P}
    (C B : PlacedTile P) (w : Pt) (hwC : w ∈ C.carrier) (hd : Disjoint (interior C.carrier) (interior B.carrier)) :
    w ∉ interior B.carrier := by
  have _ := τ
  have hclosed : Disjoint (closure (interior C.carrier)) (interior B.carrier) :=
    hd.closure_left isOpen_interior
  rw [← finite_crowns_step1_vertex_step2_sts_step3_not_interior_aux1 C] at hwC
  exact Set.disjoint_left.mp hclosed hwC

/-- Step 4 of the blueprint proof of `finite_crowns_step1_vertex_step2_sts`: if a point in a
tile's carrier is not a vertex, it is either in the interior or strictly inside a side. -/
private lemma finite_crowns_step1_vertex_step2_sts_step4_carrier_cases {τ : Substitution P}
    (B : PlacedTile P) (w : Pt) (hwB : w ∈ B.carrier) (hvB : w ∉ B.vertexSet) :
    w ∈ interior B.carrier ∨ ∃ j : Fin (P.disk B.form).n, w ∈ B.side j ∧ w ≠ B.vertex j ∧ w ≠ B.vertex (finRotate (P.disk B.form).n j) := by
  have _ := τ.one_lt
  by_cases hint : w ∈ interior B.carrier
  · exact Or.inl hint
  · right
    have hclosed : IsClosed B.carrier := by
      unfold PlacedTile.carrier
      exact (P.disk B.form).compact.isClosed.vadd _
    have hwfront : w ∈ frontier B.carrier := by
      rw [hclosed.frontier_eq]
      exact ⟨hwB, hint⟩
    have hfront : frontier B.carrier =
        ⋃ i : Fin (P.disk B.form).n, B.side i := by
      unfold PlacedTile.carrier PlacedTile.side
      rw [frontier, interior_vadd, closure_vadd, ← Set.vadd_set_sdiff,
        ← frontier, (P.disk B.form).frontier_eq, Set.vadd_set_iUnion]
      simp only [PolygonalDisk.side]
    rw [hfront, mem_iUnion] at hwfront
    obtain ⟨j, hwj⟩ := hwfront
    refine ⟨j, hwj, ?_, ?_⟩
    · intro h
      exact hvB ⟨j, h.symm⟩
    · intro h
      exact hvB ⟨finRotate (P.disk B.form).n j, h.symm⟩

/-- Step 5 of the blueprint proof of `finite_crowns_step1_vertex_step2_sts`: a vertex of one
tile cannot lie strictly inside a side of another tile in a side-to-side patch. -/
private lemma finite_crowns_step1_vertex_step2_sts_step5_vertex_not_strict_in_side {τ : Substitution P}
    (n : ℕ) (p : P.Form) (h : τ.STS) (C B : PlacedTile P) (hC : C ∈ τ.supertile n p) (hB : B ∈ τ.supertile n p)
    (w : Pt) (hwC : w ∈ C.vertexSet) (hd : Disjoint (interior C.carrier) (interior B.carrier))
    (j : Fin (P.disk B.form).n) (hwj : w ∈ B.side j) (h1 : w ≠ B.vertex j) (h2 : w ≠ B.vertex (finRotate (P.disk B.form).n j)) :
    False := sorry

/-- Step 2 of the blueprint proof of `finite_crowns_step1_vertex`: in a side-to-side
patch (like a supertile), if `w` is a vertex of some tile `C` in the patch and `w` lies
in the closed carrier of another tile `B` in the patch, then `w` must be a vertex of `B`. -/
private lemma finite_crowns_step1_vertex_step2_sts {τ : Substitution P} (h : τ.STS) (n : ℕ)
    (p : P.Form) (C : PlacedTile P) (hC : C ∈ τ.supertile n p) (w : Pt) (hwC : w ∈ C.vertexSet)
    (B : PlacedTile P) (hB : B ∈ τ.supertile n p) (hwB : w ∈ B.carrier) :
    w ∈ B.vertexSet := by
  by_cases hne : C = B
  · subst hne
    exact hwC
  · by_contra hvB
    have hwC_car := @finite_crowns_step1_vertex_step2_sts_step1_vertex_mem_carrier _ τ C w hwC
    have hd := finite_crowns_step1_vertex_step2_sts_step2_disjoint n p C B hC hB hne
    have hnot_int := @finite_crowns_step1_vertex_step2_sts_step3_not_interior _ τ C B w hwC_car hd
    have hcases := @finite_crowns_step1_vertex_step2_sts_step4_carrier_cases _ τ B w hwB hvB
    rcases hcases with hint | ⟨j, hwj, h1, h2⟩
    · exact hnot_int hint
    · exact finite_crowns_step1_vertex_step2_sts_step5_vertex_not_strict_in_side n p h C B hC hB w hwC hd j hwj h1 h2

/-- Step 1 of the blueprint proof of `finite_crowns`: in an allowed pointed crown
under STS, the origin is a listed vertex of every tile in the crown. This follows
from the fact that in a side-to-side patch, a vertex cannot lie strictly inside
a tile side with an incident open sector, nor in the interior. -/
private lemma finite_crowns_step1_vertex (h : τ.STS) (K : Set (PlacedTile P))
    (hK : τ.IsAllowedCrown K) (A : PlacedTile P) (hA : A ∈ K) :
    0 ∈ A.vertexSet := by
  rcases hK with ⟨n, p, w, h_vert, rfl⟩
  dsimp [translateSet] at hA
  rcases hA with ⟨B, hB_crown, rfl⟩
  dsimp [crown] at hB_crown
  rcases hB_crown with ⟨hB_supertile, hB_carrier⟩
  rw [finite_crowns_step1_vertex_step1_translate]
  rcases h_vert with ⟨C, hC_supertile, hC_vert⟩
  exact finite_crowns_step1_vertex_step2_sts h n p C hC_supertile w hC_vert B hB_supertile
    hB_carrier

/-- Step 2 of the blueprint proof of `finite_crowns`: there are only finitely many
placed tiles that have the origin as a listed vertex, because a tile is fixed by
its form and the listed vertex identified with the centre. -/
private lemma finite_crowns_step2_finite_tiles :
    {A : PlacedTile P | 0 ∈ A.vertexSet}.Finite := by
  let f : (Σ p : P.Form, Fin (P.disk p).n) → PlacedTile P :=
    fun ⟨p, i⟩ => ⟨p, - (P.disk p).vertex i⟩
  have H : {A : PlacedTile P | 0 ∈ A.vertexSet} ⊆ range f := by
    rintro ⟨p, a⟩ h
    simp only [mem_setOf_eq, PlacedTile.vertexSet, mem_range] at h
    rcases h with ⟨i, hi⟩
    use ⟨p, i⟩
    dsimp [f]
    congr
    dsimp [PlacedTile.vertex] at hi
    have hi2 : a + (P.disk p).vertex i = 0 := hi
    exact (eq_neg_iff_add_eq_zero.mpr hi2).symm
  apply Set.Finite.subset (Set.finite_range f) H

/-- `lem:sts-flc`: under STS the allowed pointed crowns form a finite set
(they are normalized to centre `0`, i.e. taken up to translation).
This is the manifest name of the fact stated in `Main.lean` as `STS.flc`. -/
theorem STS.finite_crowns (h : τ.STS) : τ.FLC := by
  have H_sub : ∀ K, τ.IsAllowedCrown K → K ⊆ {A : PlacedTile P | 0 ∈ A.vertexSet} :=
    fun K hK A hA => finite_crowns_step1_vertex τ h K hK A hA
  have H_fin : {K | τ.IsAllowedCrown K} ⊆ 𝒫 {A : PlacedTile P | 0 ∈ A.vertexSet} := H_sub
  exact (finite_crowns_step2_finite_tiles (P := P)).powerset.subset H_fin

end Substitution

/-! ## `lem:substitution-hierarchy` -/

namespace SubstitutionTiling

private lemma exists_composition_step1_parents_translate_child (τ : Substitution P)
    (A B : PlacedTile P) (v : Pt) :
    B.translate (τ.θ • v) ∈ τ.decomposeTile A ↔
      B ∈ τ.decomposeTile (A.translate (-v)) := by
  simp only [Substitution.decomposeTile, translateSet, mem_image]
  constructor
  · rintro ⟨C, hC, hCB⟩
    refine ⟨C, hC, ?_⟩
    apply PlacedTile.ext
    · simpa [PlacedTile.translate] using congrArg PlacedTile.form hCB
    · have ha := congrArg PlacedTile.anchor hCB
      dsimp [PlacedTile.translate] at ha ⊢
      rw [smul_add, smul_neg]
      calc
        -(τ.θ • v) + τ.θ • A.anchor + C.anchor =
            -(τ.θ • v) + (τ.θ • A.anchor + C.anchor) := by abel
        _ = -(τ.θ • v) + (τ.θ • v + B.anchor) := congrArg _ ha
        _ = B.anchor := by abel
  · rintro ⟨C, hC, hCB⟩
    refine ⟨C, hC, ?_⟩
    apply PlacedTile.ext
    · simpa [PlacedTile.translate] using congrArg PlacedTile.form hCB
    · have ha := congrArg PlacedTile.anchor hCB
      dsimp [PlacedTile.translate] at ha ⊢
      rw [smul_add, smul_neg] at ha
      calc
        τ.θ • A.anchor + C.anchor =
            τ.θ • v + (-(τ.θ • v) + τ.θ • A.anchor + C.anchor) := by abel
        _ = τ.θ • v + B.anchor := congrArg _ ha

private lemma exists_composition_step1_parents_two_tiles (T : PlaneTiling P) :
    T.tiles.Nontrivial := by
  have hne : T.tiles.Nonempty := by
    have hzero : (0 : Pt) ∈ support T.tiles := by rw [T.cover]; exact mem_univ _
    simp only [support, mem_iUnion] at hzero
    rcases hzero with ⟨A, hA, _⟩
    exact ⟨A, hA⟩
  by_contra htriv
  rw [Set.not_nontrivial_iff] at htriv
  obtain ⟨A, hA⟩ := hne
  have hsub : T.tiles ⊆ {A} := by
    intro B hB
    rw [mem_singleton_iff]
    exact htriv hB hA
  have hsupp : support T.tiles ⊆ A.carrier := by
    intro x hx
    simp only [support, mem_iUnion] at hx
    rcases hx with ⟨B, hB, hxB⟩
    simpa [htriv hB hA] using hxB
  have hcarrier : A.carrier = univ := by
    apply eq_univ_of_univ_subset
    rw [← T.cover]
    exact hsupp
  have hcompact : IsCompact A.carrier := by
    exact IsCompact.vadd A.anchor (P.disk A.form).compact
  exact hcompact.ne_univ hcarrier

private lemma exists_composition_step1_parents_finite_cover (τ : Substitution P)
    {T : PlaneTiling P} (hT : τ.IsSubstitutionTiling T)
    (F : Set (PlacedTile P)) (hF : F ⊆ T.tiles) (hFfin : F.Finite) :
    ∃ F' : Set (PlacedTile P), F'.Finite ∧
      (∃ (n : ℕ) (p : P.Form), OccursIn F' (τ.supertile n p)) ∧
      F ⊆ τ.decompose F' := by
  obtain ⟨B, hBT, C, hCT, hBC⟩ := exists_composition_step1_parents_two_tiles T
  let G : Set (PlacedTile P) := insert B (insert C F)
  have hG : G ⊆ T.tiles := by
    intro D hD
    rcases hD with (rfl | hD)
    · exact hBT
    rcases hD with (rfl | hD)
    · exact hCT
    · exact hF hD
  have hGfin : G.Finite := (hFfin.insert C).insert B
  obtain ⟨n, p, v, hv⟩ := hT G hG hGfin
  cases n with
  | zero =>
      have hBv := hv (mem_image_of_mem (fun A => A.translate v) (mem_insert B _))
      have hCv := hv (mem_image_of_mem (fun A => A.translate v)
        (mem_insert_of_mem B (mem_insert C F)))
      simp only [Substitution.supertile, Substitution.decomposeIter] at hBv hCv
      exfalso
      apply hBC
      have heq : B.translate v = C.translate v := hBv.trans hCv.symm
      cases B with
      | mk bf ba =>
        cases C with
        | mk cf ca =>
          injection heq with hf ha
          subst hf
          congr
          exact add_left_cancel ha
  | succ n =>
      have hparents : ∀ D ∈ F, ∃ A ∈ τ.supertile n p,
          D.translate v ∈ τ.decomposeTile A := by
        intro D hDF
        have hDv : D.translate v ∈ τ.supertile (n + 1) p :=
          hv (mem_image_of_mem (fun A => A.translate v)
            (mem_insert_of_mem B (mem_insert_of_mem C hDF)))
        change D.translate v ∈ τ.decompose (τ.supertile n p) at hDv
        simp only [Substitution.decompose, mem_iUnion] at hDv
        rcases hDv with ⟨A, hAS, hAD⟩
        exact ⟨A, hAS, hAD⟩
      choose A hAS hAD using hparents
      let w : Pt := τ.θ⁻¹ • v
      let F' : Set (PlacedTile P) :=
        range (fun D : F => (A D.1 D.2).translate (-w))
      refine ⟨F', ?_, ?_, ?_⟩
      · letI := hFfin.fintype
        exact Set.finite_range _
      · refine ⟨n, p, w, ?_⟩
        rintro X ⟨Y, hY, rfl⟩
        rcases hY with ⟨D, rfl⟩
        simpa [PlacedTile.translate, w] using hAS D.1 D.2
      · intro D hDF
        simp only [Substitution.decompose, mem_iUnion]
        refine ⟨(A D hDF).translate (-w), ⟨?_, ?_⟩⟩
        · exact ⟨⟨D, hDF⟩, rfl⟩
        · apply (exists_composition_step1_parents_translate_child τ (A D hDF) D w).mp
          have hθ : τ.θ ≠ 0 := by linarith [τ.one_lt]
          simpa [w, smul_smul, hθ] using hAD D hDF

/-- Step 1 of the blueprint proof of `exists_composition`: by thinning a sequence
of parent covers using the finite-parent lemma (or by Kőnig's lemma on a finite inverse
system), there exists a global parent assignment `T'` whose decomposition covers `T`
and whose finite patches occur in supertiles. -/
private lemma exists_composition_step1_parents (τ : Substitution P) {T : PlaneTiling P}
    (hT : τ.IsSubstitutionTiling T) :
    ∃ T' : Set (PlacedTile P),
      (∀ F' ⊆ T', F'.Finite → ∃ (n : ℕ) (p : P.Form), OccursIn F' (τ.supertile n p)) ∧
      T.tiles ⊆ τ.decompose T' := by
  classical
  let I := Finset T.tiles
  let childSet : I → Set (PlacedTile P) := fun i => Subtype.val '' (i : Set T.tiles)
  have hchildSet_sub (i : I) : childSet i ⊆ T.tiles := by
    rintro _ ⟨B, _, rfl⟩
    exact B.2
  have hchildSet_fin (i : I) : (childSet i).Finite := by
    exact i.finite_toSet.image Subtype.val
  have hcover (i : I) :
      ∃ Q : Set (PlacedTile P), Q.Finite ∧
        (∃ (n : ℕ) (p : P.Form), OccursIn Q (τ.supertile n p)) ∧
        childSet i ⊆ τ.decompose Q :=
    exists_composition_step1_parents_finite_cover τ hT (childSet i)
      (hchildSet_sub i) (hchildSet_fin i)
  choose Q hQfin hQocc hQcov using hcover
  have hparent_exists (B : T.tiles) (i : I) (hBi : B ∈ i) :
      ∃ A ∈ Q i, B.1 ∈ τ.decomposeTile A := by
    have hBdec : B.1 ∈ τ.decompose (Q i) := hQcov i ⟨B, hBi, rfl⟩
    simp only [Substitution.decompose, mem_iUnion] at hBdec
    rcases hBdec with ⟨A, hAQ, hBA⟩
    exact ⟨A, hAQ, hBA⟩
  let singletonIndex : T.tiles → I := fun B => {B}
  have hparent_default (B : T.tiles) :
      ∃ A ∈ Q (singletonIndex B), B.1 ∈ τ.decomposeTile A := by
    apply hparent_exists B (singletonIndex B)
    exact Finset.mem_singleton_self B
  let parent : (B : T.tiles) → I → {A : PlacedTile P // B.1 ∈ τ.decomposeTile A} :=
    fun B i => if hBi : B ∈ i then
      ⟨(hparent_exists B i hBi).choose, (hparent_exists B i hBi).choose_spec.2⟩
    else
      ⟨(hparent_default B).choose, (hparent_default B).choose_spec.2⟩
  have hparent_mem (B : T.tiles) (i : I) (hBi : B ∈ i) :
      (parent B i).1 ∈ Q i := by
    simp only [parent, dif_pos hBi]
    exact (hparent_exists B i hBi).choose_spec.1
  let U : Ultrafilter I := Ultrafilter.of Filter.atTop
  have hparent_const (B : T.tiles) :
      ∃ A : {A : PlacedTile P // B.1 ∈ τ.decomposeTile A},
        ∀ᶠ i in U, parent B i = A := by
    letI : Finite {A : PlacedTile P // B.1 ∈ τ.decomposeTile A} :=
      (τ.finite_parents B.1).to_subtype
    apply (Ultrafilter.eventually_exists_iff (f := U)).mp
    exact Filter.Eventually.of_forall fun i => ⟨parent B i, rfl⟩
  choose selected hselected using hparent_const
  let selectedTile : T.tiles → PlacedTile P := fun B => (selected B).1
  let T' : Set (PlacedTile P) := range selectedTile
  refine ⟨T', ?_, ?_⟩
  · intro F' hF'T' hF'fin
    letI := hF'fin.fintype
    have hpreimage (X : F') : ∃ B : T.tiles, selectedTile B = X.1 := hF'T' X.2
    choose source hsource using hpreimage
    let E : Set T.tiles := range source
    have hEfin : E.Finite := Set.finite_range source
    have h_eventually_mem (B : T.tiles) : ∀ᶠ i : I in (U : Filter I), B ∈ i := by
      have h_atTop : ∀ᶠ i : I in Filter.atTop, B ∈ i := by
        apply Filter.eventually_atTop.2
        exact ⟨{B}, fun i hi => hi (Finset.mem_singleton_self B)⟩
      exact h_atTop.filter_mono (Ultrafilter.of_le Filter.atTop)
    have h_eventually_Q : ∀ᶠ i in U, ∀ B ∈ E, selectedTile B ∈ Q i := by
      apply (hEfin.eventually_all).2
      intro B hBE
      filter_upwards [hselected B, h_eventually_mem B] with i hsel hBi
      change (selected B).1 ∈ Q i
      rw [← hsel]
      exact hparent_mem B i hBi
    obtain ⟨i, hi⟩ := h_eventually_Q.exists
    obtain ⟨n, p, v, hv⟩ := hQocc i
    refine ⟨n, p, v, ?_⟩
    intro X hX
    rcases hX with ⟨Y, hYF', rfl⟩
    have hsourceE : source ⟨Y, hYF'⟩ ∈ E := ⟨⟨Y, hYF'⟩, rfl⟩
    have hYQ : Y ∈ Q i := by
      have hs := hi (source ⟨Y, hYF'⟩) hsourceE
      rw [hsource ⟨Y, hYF'⟩] at hs
      exact hs
    exact hv (mem_image_of_mem (fun A => A.translate v) hYQ)
  · intro B hBT
    let b : T.tiles := ⟨B, hBT⟩
    simp only [Substitution.decompose, mem_iUnion]
    exact ⟨selectedTile b, ⟨⟨b, rfl⟩, (selected b).2⟩⟩

private lemma exists_composition_step2_disjoint_supertile_step1_decompose_translate {v : Pt}
    {S : Set (PlacedTile P)} (h : DisjointInteriors S) : DisjointInteriors (translateSet v S) := by
  intro A hA B hB hne
  dsimp [translateSet] at hA hB
  rcases hA with ⟨A', hA', rfl⟩
  rcases hB with ⟨B', hB', rfl⟩
  have hne' : A' ≠ B' := by
    intro hc
    apply hne
    rw [hc]
  have hd := h hA' hB' hne'
  have heq1 : (A'.translate v).carrier = v +ᵥ A'.carrier := by
    ext x
    simp only [PlacedTile.carrier, PlacedTile.translate, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_rev]
    rw [← add_assoc]
  have heq2 : (B'.translate v).carrier = v +ᵥ B'.carrier := by
    ext x
    simp only [PlacedTile.carrier, PlacedTile.translate, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_rev]
    rw [← add_assoc]
  dsimp [Function.onFun] at hd
  dsimp [Function.onFun]
  rw [heq1, heq2]
  rw [interior_vadd, interior_vadd]
  have hinj : Function.Injective (v +ᵥ ·) := add_right_injective v
  exact (disjoint_image_iff hinj).mpr hd

/-- Step 1 of the blueprint proof of `exists_composition_step2_disjoint_supertile`: decomposition
preserves disjoint interiors. -/
private lemma exists_composition_step2_disjoint_supertile_step1_decompose (τ : Substitution P)
    (S : Set (PlacedTile P)) (hS : DisjointInteriors S) : DisjointInteriors (τ.decompose S) := by
  have hθ : τ.θ ≠ 0 := (zero_lt_one.trans τ.one_lt).ne'
  have key : ∀ {X X' : PlacedTile P}, X ∈ τ.decomposeTile X' →
      interior X.carrier ⊆ τ.θ • interior X'.carrier := by
    intro X X' hX
    rw [← interior_smul₀ hθ]
    refine interior_mono ?_
    rw [← iterate_support_decomposeTile]
    exact Set.subset_biUnion_of_mem hX
  intro A hA B hB hne
  simp only [decompose, mem_iUnion, exists_prop] at hA hB
  obtain ⟨A', hA', hAmem⟩ := hA
  obtain ⟨B', hB', hBmem⟩ := hB
  dsimp [Function.onFun]
  by_cases hAB : A' = B'
  · subst hAB
    have h_rule_disj := (τ.rule A'.form).disjoint
    have h_trans_disj :=
      exists_composition_step2_disjoint_supertile_step1_decompose_translate
      h_rule_disj (v := τ.θ • A'.anchor)
    change DisjointInteriors (τ.decomposeTile A') at h_trans_disj
    exact h_trans_disj hAmem hBmem hne
  · have hd : Disjoint (interior A'.carrier) (interior B'.carrier) := hS hA' hB' hAB
    have hd' : Disjoint (τ.θ • interior A'.carrier) (τ.θ • interior B'.carrier) :=
      (disjoint_image_iff (smul_right_injective _ hθ)).mpr hd
    exact hd'.mono (key hAmem) (key hBmem)

/-- Step 1 of the blueprint proof of `exists_composition_step2_disjoint`: supertiles have
disjoint interiors. -/
private lemma exists_composition_step2_disjoint_supertile (τ : Substitution P) (n : ℕ)
    (p : P.Form) :
    DisjointInteriors (τ.supertile n p) := by
  induction n with
  | zero =>
    intro x hx y hy hne
    simp [Substitution.supertile, Substitution.decomposeIter] at hx hy
    rcases hx with rfl
    rcases hy with rfl
    contradiction
  | succ n ih =>
    have h : τ.supertile (n + 1) p = τ.decompose (τ.supertile n p) := rfl
    rw [h]
    exact exists_composition_step2_disjoint_supertile_step1_decompose τ (τ.supertile n p) ih

/-- Step 2 of the blueprint proof of `exists_composition_step2_disjoint`: translation
preserves disjoint interiors. -/
private lemma exists_composition_step2_disjoint_translate_inv {v : Pt} {S : Set (PlacedTile P)}
    (h : DisjointInteriors (translateSet v S)) : DisjointInteriors S := by
  intro A hA B hB hne
  have h_trans : A.translate v ∈ translateSet v S := mem_image_of_mem _ hA
  have h_trans' : B.translate v ∈ translateSet v S := mem_image_of_mem _ hB
  have hne' : A.translate v ≠ B.translate v := by
    intro hc
    apply hne
    cases A with | mk form anchor =>
    cases B with | mk form' anchor' =>
    injection hc with hform hanchor
    subst hform
    congr
    dsimp at hanchor
    exact add_left_cancel hanchor
  have hd := h h_trans h_trans' hne'
  have heq1 : (A.translate v).carrier = v +ᵥ A.carrier := by
    ext x
    simp only [PlacedTile.carrier, PlacedTile.translate, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_rev]
    rw [← add_assoc]
  have heq2 : (B.translate v).carrier = v +ᵥ B.carrier := by
    ext x
    simp only [PlacedTile.carrier, PlacedTile.translate, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_rev]
    rw [← add_assoc]
  dsimp [Function.onFun] at hd
  dsimp [Function.onFun]
  rw [heq1, heq2] at hd
  rw [interior_vadd, interior_vadd] at hd
  have hinj : Function.Injective (v +ᵥ ·) := add_right_injective v
  have H : Disjoint ((v +ᵥ ·) '' interior A.carrier) ((v +ᵥ ·) '' interior B.carrier) := hd
  exact (disjoint_image_iff hinj).mp H

/-- Step 3 of the blueprint proof of `exists_composition_step2_disjoint`: a patch that
occurs in a set with disjoint interiors has disjoint interiors. -/
private lemma exists_composition_step2_disjoint_of_occurs {F S : Set (PlacedTile P)}
    (h_occ : OccursIn F S) (hS : DisjointInteriors S) : DisjointInteriors F := by
  rcases h_occ with ⟨v, hv⟩
  exact exists_composition_step2_disjoint_translate_inv (hS.subset hv)

/-- Step 2 of the blueprint proof of `exists_composition`: a parent assignment whose finite
patches occur in supertiles must have disjoint interiors. -/
private lemma exists_composition_step2_disjoint (τ : Substitution P) (T' : Set (PlacedTile P))
    (h_subst : ∀ F' ⊆ T', F'.Finite → ∃ (n : ℕ) (p : P.Form), OccursIn F' (τ.supertile n p)) :
    DisjointInteriors T' := by
  intro A hA B hB hne
  have hF : {A, B} ⊆ T' := by
    intro X hX
    rcases hX with rfl | rfl
    · exact hA
    · exact hB
  have hFin : ({A, B} : Set (PlacedTile P)).Finite := finite_singleton B |>.insert A
  rcases h_subst {A, B} hF hFin with ⟨n, p, h_occ⟩
  have hDisj := exists_composition_step2_disjoint_of_occurs h_occ
    (exists_composition_step2_disjoint_supertile τ n p)
  exact hDisj (mem_insert A _) (mem_insert_of_mem _ (mem_singleton _)) hne

private lemma exists_composition_step3_interior_biUnion_empty {α : Type*}
    [TopologicalSpace α] {ι : Type*} {t : ι → Set α}
    (u : Finset ι) (hc : ∀ i ∈ u, IsClosed (t i)) (hi : ∀ i ∈ u, interior (t i) = ∅) :
    interior (⋃ i ∈ u, t i) = ∅ := by
  classical
  induction' u using Finset.induction_on with i u hin ih
  · simp
  · rw [Finset.set_biUnion_insert, union_comm]
    rw [interior_union_isClosed_of_interior_empty]
    · exact ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
        (fun j hj => hi j (Finset.mem_insert_of_mem hj))
    · exact Set.Finite.isClosed_biUnion u.finite_toSet
        (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    · exact hi i (Finset.mem_insert_self i u)

private lemma exists_composition_step3_not_subset_finite_union {α : Type*}
    [TopologicalSpace α] {s : Set α} {ι : Type*} {t : ι → Set α}
    (u : Finset ι) (h_nonempty : (interior s).Nonempty)
    (h_subset : s ⊆ ⋃ i ∈ u, t i)
    (h_disj : ∀ i ∈ u, Disjoint (interior s) (interior (t i)))
    (hc : ∀ i ∈ u, IsClosed (t i)) : False := by
  have h_int_s : interior s ⊆ ⋃ i ∈ u, frontier (t i) := by
    intro x hx
    have h_in : x ∈ ⋃ i ∈ u, t i := h_subset (interior_subset hx)
    simp only [mem_iUnion, exists_prop] at h_in ⊢
    rcases h_in with ⟨i, hi, hxi⟩
    refine ⟨i, hi, subset_closure hxi, ?_⟩
    intro h_int
    exact Set.disjoint_left.mp (h_disj i hi) hx h_int
  have h_empty_int : interior (⋃ i ∈ u, frontier (t i)) = ∅ := by
    apply exists_composition_step3_interior_biUnion_empty
    · exact fun _ _ => isClosed_frontier
    · exact fun i hi => interior_frontier (hc i hi)
  have h_int_s_int : interior (interior s) ⊆ interior (⋃ i ∈ u, frontier (t i)) :=
    interior_mono h_int_s
  rw [interior_interior, h_empty_int] at h_int_s_int
  have h_empty : interior s = ∅ := subset_empty_iff.mp h_int_s_int
  rw [h_empty] at h_nonempty
  exact Set.not_nonempty_empty h_nonempty

/-- Step 3 of the blueprint proof of `exists_composition`: no extra child can occur in
the decomposition because the plane is already covered by `T` with disjoint interiors,
so the decomposition is exactly `T`. -/
private lemma exists_composition_step3_decompose_eq (τ : Substitution P) {T : PlaneTiling P}
    (T' : Set (PlacedTile P))
    (h_disj : DisjointInteriors T') (h_cov : T.tiles ⊆ τ.decompose T') :
    τ.decompose T' = T.tiles := by
  apply le_antisymm
  · intro A hA
    by_contra hAT
    have h_decomp_disj : DisjointInteriors (τ.decompose T') :=
      exists_composition_step2_disjoint_supertile_step1_decompose τ T' h_disj
    let S : Set (PlacedTile P) := {B ∈ T.tiles | (B.carrier ∩ A.carrier).Nonempty}
    have hA_compact : IsCompact A.carrier := IsCompact.vadd A.anchor (P.disk A.form).compact
    have hS_fin : S.Finite := T.locallyFinite hA_compact
    have hA_sub : A.carrier ⊆ ⋃ B ∈ hS_fin.toFinset, B.carrier := by
      intro x hx
      have hx_support : x ∈ support T.tiles := by rw [T.cover]; exact mem_univ x
      simp only [support, mem_iUnion, exists_prop] at hx_support
      rcases hx_support with ⟨B, hBT, hxB⟩
      have hBS : B ∈ S := ⟨hBT, ⟨x, hxB, hx⟩⟩
      simp only [mem_iUnion, exists_prop]
      exact ⟨B, (Set.Finite.mem_toFinset hS_fin).mpr hBS, hxB⟩
    have hA_ne : (interior A.carrier).Nonempty := by
      rw [PlacedTile.carrier, interior_vadd]
      exact (P.disk A.form).interior_nonempty.image (A.anchor +ᵥ·)
    have h_closed : ∀ B ∈ hS_fin.toFinset, IsClosed B.carrier := by
      intro B _
      exact (IsCompact.vadd B.anchor (P.disk B.form).compact).isClosed
    have h_int_disj : ∀ B ∈ hS_fin.toFinset,
        Disjoint (interior A.carrier) (interior B.carrier) := by
      intro B hB
      have hBS : B ∈ S := (Set.Finite.mem_toFinset hS_fin).mp hB
      have hAB : A ≠ B := by
        rintro rfl
        exact hAT hBS.1
      exact h_decomp_disj hA (h_cov hBS.1) hAB
    exact exists_composition_step3_not_subset_finite_union hS_fin.toFinset hA_ne hA_sub
      h_int_disj h_closed
  · exact h_cov

/-- Step 4 of the blueprint proof of `exists_composition`: scaling gives coverage of the
parent plane, so `T'` covers the plane. -/
private lemma exists_composition_step4_cover (τ : Substitution P) (T' : Set (PlacedTile P))
    {T : PlaneTiling P} (h_decomp : τ.decompose T' = T.tiles) :
    support T' = univ := by
  have hscaled : univ = τ.θ • support T' := by
    rw [← T.cover, ← h_decomp]
    exact iterate_support_decompose τ T'
  have hθ : τ.θ ≠ 0 := by
    linarith [τ.one_lt]
  ext x
  simp only [mem_univ, iff_true]
  have hx : τ.θ • x ∈ univ := mem_univ _
  rw [hscaled] at hx
  simp only [mem_smul_set] at hx
  rcases hx with ⟨y, hy, hxy⟩
  have hyx : y = x := smul_right_injective Pt hθ hxy
  rwa [← hyx]

/-- `lem:substitution-hierarchy`: every substitution plane tiling has a
composition which is again a substitution plane tiling. -/
theorem exists_composition (τ : Substitution P) {T : PlaneTiling P}
    (hT : τ.IsSubstitutionTiling T) :
    ∃ T' : PlaneTiling P, τ.IsComposition T' T ∧ τ.IsSubstitutionTiling T' := by
  rcases exists_composition_step1_parents τ hT with ⟨T'_set, h_subst, h_subset⟩
  have h_disj := exists_composition_step2_disjoint τ T'_set h_subst
  have h_decomp := exists_composition_step3_decompose_eq τ T'_set h_disj h_subset
  have h_cov := exists_composition_step4_cover τ T'_set h_decomp
  let T' : PlaneTiling P := ⟨T'_set, h_cov, h_disj⟩
  use T'
  exact ⟨h_decomp, h_subst⟩

end SubstitutionTiling

/-! ## `lem:hierarchy-step` -/

private lemma hierarchical_power_decompose_translate (τ : Substitution P) (v : Pt)
    (S : Set (PlacedTile P)) :
    τ.decompose (translateSet v S) = translateSet (τ.θ • v) (τ.decompose S) := by
  ext A
  simp only [Substitution.decompose, Substitution.decomposeTile, translateSet,
    PlacedTile.translate, mem_iUnion, mem_image]
  constructor
  · rintro ⟨B, ⟨C, hC, rfl⟩, D, hD, rfl⟩
    refine ⟨D.translate (τ.θ • C.anchor), ⟨C, hC, D, hD, ?_⟩, ?_⟩
    · apply PlacedTile.ext
      · rfl
      · simp [PlacedTile.translate]
    · apply PlacedTile.ext
      · rfl
      · change τ.θ • v + (τ.θ • C.anchor + D.anchor) =
          τ.θ • (v + C.anchor) + D.anchor
        rw [smul_add]
        abel
  · rintro ⟨B, ⟨C, hC, D, hD, rfl⟩, rfl⟩
    refine ⟨C.translate v, ⟨C, hC, rfl⟩, D, hD, ?_⟩
    apply PlacedTile.ext
    · rfl
    · change τ.θ • (v + C.anchor) + D.anchor =
        τ.θ • v + (τ.θ • C.anchor + D.anchor)
      rw [smul_add]
      abel

private lemma hierarchical_power_decompose_iUnion (τ : Substitution P)
    {ι : Sort*} (S : ι → Set (PlacedTile P)) :
    τ.decompose (⋃ i, S i) = ⋃ i, τ.decompose (S i) := by
  ext A
  simp only [Substitution.decompose, mem_iUnion]
  constructor
  · rintro ⟨B, ⟨i, hB⟩, hA⟩
    exact ⟨i, B, hB, hA⟩
  · rintro ⟨i, B, hB, hA⟩
    exact ⟨B, ⟨i, hB⟩, hA⟩

private lemma hierarchical_power_iter_iUnion (τ : Substitution P) (n : ℕ)
    {ι : Sort*} (S : ι → Set (PlacedTile P)) :
    τ.decomposeIter n (⋃ i, S i) = ⋃ i, τ.decomposeIter n (S i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change τ.decompose (τ.decomposeIter n (⋃ i, S i)) = _
      rw [ih, hierarchical_power_decompose_iUnion]
      rfl

private lemma hierarchical_power_iter_translate (τ : Substitution P) (n : ℕ)
    (v : Pt) (S : Set (PlacedTile P)) :
    τ.decomposeIter n (translateSet v S) =
      translateSet ((τ.θ ^ n) • v) (τ.decomposeIter n S) := by
  induction n with
  | zero => simp [Substitution.decomposeIter]
  | succ n ih =>
      change τ.decompose (τ.decomposeIter n (translateSet v S)) = _
      rw [ih, hierarchical_power_decompose_translate]
      congr 1
      rw [pow_succ', mul_smul]

private lemma hierarchical_power_singleton_translate (A : PlacedTile P) :
    ({A} : Set (PlacedTile P)) = translateSet A.anchor {⟨A.form, 0⟩} := by
  ext B
  simp [translateSet, PlacedTile.translate, PlacedTile.ext_iff]

private lemma hierarchical_power_decompose_eq_iter (τ : Substitution P) (m : ℕ)
    (hm : 0 < m) (S : Set (PlacedTile P)) :
    (τ.pow m hm).decompose S = τ.decomposeIter m S := by
  rw [show S = ⋃ A ∈ S, ({A} : Set (PlacedTile P)) by ext; simp]
  rw [hierarchical_power_decompose_iUnion, hierarchical_power_iter_iUnion]
  apply iUnion_congr
  intro A
  rw [hierarchical_power_decompose_iUnion, hierarchical_power_iter_iUnion]
  apply iUnion_congr
  intro hA
  rw [hierarchical_power_singleton_translate]
  rw [hierarchical_power_decompose_translate]
  rw [hierarchical_power_iter_translate]
  congr 1
  ext B
  simp [Substitution.decompose, Substitution.decomposeTile, Substitution.pow,
    Substitution.supertile, translateSet, PlacedTile.translate]

private lemma hierarchical_power_decompose_disjoint (τ : Substitution P)
    (S : Set (PlacedTile P)) (hS : DisjointInteriors S) :
    DisjointInteriors (τ.decompose S) := by
  intro A hA B hB hAB
  simp only [Substitution.decompose, mem_iUnion] at hA hB
  rcases hA with ⟨X, hX, hAX⟩
  rcases hB with ⟨Y, hY, hBY⟩
  simp only [Substitution.decomposeTile, translateSet, mem_image] at hAX hBY
  rcases hAX with ⟨C, hC, rfl⟩
  rcases hBY with ⟨D, hD, rfl⟩
  by_cases hXY : X = Y
  · subst Y
    have hCD : C ≠ D := by
      intro h
      subst D
      exact hAB rfl
    have hdisj := (τ.rule X.form).disjoint hC hD hCD
    have hcarrier (E : PlacedTile P) (v : Pt) :
        (E.translate v).carrier = v +ᵥ E.carrier := by
      dsimp [PlacedTile.carrier, PlacedTile.translate]
      rw [← vadd_assoc, vadd_eq_add]
    dsimp [Function.onFun] at hdisj ⊢
    rw [hcarrier, hcarrier, interior_vadd, interior_vadd]
    rw [Set.disjoint_left] at hdisj ⊢
    intro z hzC hzD
    apply hdisj
    · rwa [mem_vadd_set_iff_neg_vadd_mem] at hzC
    · rwa [mem_vadd_set_iff_neg_vadd_mem] at hzD
  · have hθ : τ.θ ≠ 0 := by linarith [τ.one_lt]
    have hCX : interior (C.translate (τ.θ • X.anchor)).carrier ⊆
        interior (τ.θ • X.carrier) := by
      apply interior_maximal
      · intro z hz
        have hz' : z ∈ support (τ.decomposeTile X) := by
          simp only [support, mem_iUnion]
          refine ⟨C.translate (τ.θ • X.anchor), ?_, interior_subset hz⟩
          simp only [Substitution.decomposeTile, translateSet, mem_image]
          exact ⟨C, hC, rfl⟩
        rwa [iterate_support_decomposeTile] at hz'
      · exact isOpen_interior
    have hDY : interior (D.translate (τ.θ • Y.anchor)).carrier ⊆
        interior (τ.θ • Y.carrier) := by
      apply interior_maximal
      · intro z hz
        have hz' : z ∈ support (τ.decomposeTile Y) := by
          simp only [support, mem_iUnion]
          refine ⟨D.translate (τ.θ • Y.anchor), ?_, interior_subset hz⟩
          simp only [Substitution.decomposeTile, translateSet, mem_image]
          exact ⟨D, hD, rfl⟩
        rwa [iterate_support_decomposeTile] at hz'
      · exact isOpen_interior
    have hparents := hS hX hY hXY
    dsimp [Function.onFun] at hparents
    have hscaled : Disjoint (interior (τ.θ • X.carrier))
        (interior (τ.θ • Y.carrier)) := by
      rw [interior_smul₀ hθ, interior_smul₀ hθ]
      rw [Set.disjoint_left] at hparents ⊢
      intro z hzX hzY
      apply hparents
      · exact (Set.mem_smul_set_iff_inv_smul_mem₀ hθ _ _).mp hzX
      · exact (Set.mem_smul_set_iff_inv_smul_mem₀ hθ _ _).mp hzY
    exact hscaled.mono hCX hDY

private def hierarchical_power_decompose_tiling (τ : Substitution P)
    (T : PlaneTiling P) : PlaneTiling P where
  tiles := τ.decompose T.tiles
  cover := by
    rw [iterate_support_decompose, T.cover]
    exact Set.smul_set_univ₀ (by linarith [τ.one_lt])
  disjoint := hierarchical_power_decompose_disjoint τ T.tiles T.disjoint

private lemma hierarchical_power_decompose_tiling_tiles (τ : Substitution P)
    (T : PlaneTiling P) :
    (hierarchical_power_decompose_tiling τ T).tiles = τ.decompose T.tiles := rfl

private lemma hierarchical_power_iter_tiling_tiles (τ : Substitution P) (n : ℕ)
    (T : PlaneTiling P) :
    ((hierarchical_power_decompose_tiling τ)^[n] T).tiles = τ.decomposeIter n T.tiles := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change τ.decompose (((hierarchical_power_decompose_tiling τ)^[n] T).tiles) = _
      rw [ih]
      rfl

private lemma hierarchical_power_tiling_ext {T₁ T₂ : PlaneTiling P}
    (h : T₁.tiles = T₂.tiles) : T₁ = T₂ := by
  cases T₁
  cases T₂
  cases h
  rfl

private lemma hierarchical_power_chain (τ : Substitution P)
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.IsComposition (seq (n + 1)) (seq n)) (k n : ℕ) :
    τ.decomposeIter k (seq (n + k)).tiles = (seq n).tiles := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      change τ.decompose (τ.decomposeIter k (seq (n + (k + 1))).tiles) = _
      rw [show n + (k + 1) = (n + 1) + k by omega, ih]
      exact hseq n

/-- `lem:hierarchy-step`: for `m > 0`, a plane tiling is `τ`-hierarchical
iff it is `τ^m`-hierarchical.  (Side-to-side hierarchy is *not* claimed to
transfer; that needs the alignment tuples.) -/
theorem hierarchical_power_iff (τ : Substitution P) (m : ℕ) (hm : 0 < m)
    (T : PlaneTiling P) :
    τ.IsHierarchical T ↔ (τ.pow m hm).IsHierarchical T := by
  constructor
  · rintro ⟨seq, hzero, hseq⟩
    refine ⟨fun n => seq (n * m), ?_, ?_⟩
    · simpa using hzero
    · intro n
      change (τ.pow m hm).decompose (seq ((n + 1) * m)).tiles =
        (seq (n * m)).tiles
      rw [hierarchical_power_decompose_eq_iter]
      rw [show (n + 1) * m = n * m + m by simp [Nat.add_mul]]
      exact hierarchical_power_chain τ seq hseq m (n * m)
  · rintro ⟨seq, hzero, hseq⟩
    have hcoarse : ∀ q, τ.decomposeIter m (seq (q + 1)).tiles = (seq q).tiles := by
      intro q
      rw [← hierarchical_power_decompose_eq_iter τ m hm]
      exact hseq q
    let fine : ℕ → PlaneTiling P := fun n =>
      ((hierarchical_power_decompose_tiling τ)^[m - n % m] (seq (n / m + 1)))
    refine ⟨fine, ?_, ?_⟩
    · apply hierarchical_power_tiling_ext
      dsimp [fine]
      rw [hierarchical_power_iter_tiling_tiles]
      change τ.decomposeIter (m - 0 % m) (seq (0 / m + 1)).tiles = T.tiles
      simpa [hzero] using hcoarse 0
    · intro n
      change τ.decompose (fine (n + 1)).tiles = (fine n).tiles
      rw [show (fine (n + 1)).tiles =
          τ.decomposeIter (m - (n + 1) % m) (seq ((n + 1) / m + 1)).tiles by
        exact hierarchical_power_iter_tiling_tiles τ _ _]
      rw [show (fine n).tiles =
          τ.decomposeIter (m - n % m) (seq (n / m + 1)).tiles by
        exact hierarchical_power_iter_tiling_tiles τ _ _]
      by_cases hdvd : m ∣ n + 1
      · have hdiv : (n + 1) / m = n / m + 1 := Nat.succ_div_of_dvd hdvd
        have hmod : (n + 1) % m = 0 := Nat.mod_eq_zero_of_dvd hdvd
        have hn := Nat.mod_add_div n m
        have hn1 := Nat.mod_add_div (n + 1) m
        rw [hmod, hdiv] at hn1
        simp only [zero_add, mul_add, mul_one] at hn1
        have hr : n % m + 1 = m := by omega
        rw [hmod, hdiv]
        change τ.decompose (τ.decomposeIter m (seq (n / m + 1 + 1)).tiles) = _
        rw [hcoarse (n / m + 1)]
        have hexp : m - n % m = 1 := by omega
        rw [hexp]
        rfl
      · have hm_ne_one : m ≠ 1 := by
          intro h
          subst m
          exact hdvd (one_dvd _)
        have hm_one : 1 < m := by omega
        have hr_lt : n % m + 1 < m := by
          have hr := Nat.mod_lt n hm
          by_contra hlt
          have heq : n % m + 1 = m := by omega
          apply hdvd
          rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
          rw [Nat.mod_eq_of_lt hm_one, heq, Nat.mod_self]
        have hmod : (n + 1) % m = n % m + 1 := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt hm_one, Nat.mod_eq_of_lt hr_lt]
        have hdiv : (n + 1) / m = n / m := Nat.succ_div_of_not_dvd hdvd
        rw [hmod, hdiv]
        have hr := Nat.mod_lt n hm
        have hexp : m - (n % m + 1) + 1 = m - n % m := by omega
        change τ.decompose (τ.decomposeIter (m - (n % m + 1))
          (seq (n / m + 1)).tiles) = _
        change τ.decomposeIter (m - (n % m + 1) + 1)
          (seq (n / m + 1)).tiles = _
        rw [hexp]

/-! ## `lem:finite-idempotent` -/

namespace FiniteMap

/-- `lem:finite-idempotent`: an endofunction of a finite type has an
idempotent positive iterate: `c^[2ℓ] = c^[ℓ]` for some `ℓ > 0`. -/
theorem exists_idempotent_iterate {S : Type*} [Finite S] (c : S → S) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ c^[2 * ℓ] = c^[ℓ] := by
  have main : ∀ a p : ℕ, 0 < p → c^[a] = c^[a + p] →
      ∃ ℓ : ℕ, 0 < ℓ ∧ c^[2 * ℓ] = c^[ℓ] := by
    intro a p hp heq
    have key : ∀ k : ℕ, c^[a + k * p] = c^[a] := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show a + (k + 1) * p = k * p + (a + p) by ring,
          Function.iterate_add c (k * p) (a + p), ← heq,
          ← Function.iterate_add c (k * p) a, Nat.add_comm (k * p) a, ih]
    have key' : ∀ n : ℕ, a ≤ n → ∀ k : ℕ, c^[n + k * p] = c^[n] := by
      intro n hn k
      obtain ⟨m, rfl⟩ : ∃ m, n = a + m := ⟨n - a, by omega⟩
      rw [show a + m + k * p = m + (a + k * p) by ring,
        Function.iterate_add c m (a + k * p), key k,
        ← Function.iterate_add c m a, Nat.add_comm m a]
    refine ⟨(a + 1) * p, Nat.mul_pos (Nat.succ_pos a) hp, ?_⟩
    rw [two_mul]
    have hle : a ≤ (a + 1) * p :=
      calc a ≤ (a + 1) * 1 := by omega
        _ ≤ (a + 1) * p := Nat.mul_le_mul (le_refl _) hp
    exact key' _ hle (a + 1)
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => c^[n])
  have heq' : c^[a] = c^[b] := heq
  rcases lt_or_gt_of_ne hab with h | h
  · exact main a (b - a) (by omega) (by rw [Nat.add_sub_of_le h.le]; exact heq')
  · exact main b (a - b) (by omega) (by rw [Nat.add_sub_of_le h.le]; exact heq'.symm)

end FiniteMap

/-! ## `lem:covered-tile-belongs` -/

namespace Patch

private lemma mem_of_carrier_subset_union_interior_biUnion_empty {α : Type*}
    [TopologicalSpace α] {ι : Type*} {t : ι → Set α}
    (u : Finset ι) (hc : ∀ i ∈ u, IsClosed (t i)) (hi : ∀ i ∈ u, interior (t i) = ∅) :
    interior (⋃ i ∈ u, t i) = ∅ := by
  classical
  induction' u using Finset.induction_on with i u hin ih
  · simp
  · rw [Finset.set_biUnion_insert]
    rw [union_comm]
    rw [interior_union_isClosed_of_interior_empty]
    · apply ih
      · intro j hj; apply hc; apply Finset.mem_insert_of_mem hj
      · intro j hj; apply hi; apply Finset.mem_insert_of_mem hj
    · apply Set.Finite.isClosed_biUnion u.finite_toSet
      intro j hj; apply hc; apply Finset.mem_insert_of_mem hj
    · apply hi
      apply Finset.mem_insert_self

private lemma mem_of_carrier_subset_union_empty_interior_of_subset_union_frontier
    {α : Type*} [TopologicalSpace α] {s : Set α} {ι : Type*} {t : ι → Set α}
    (u : Finset ι) (h_nonempty : (interior s).Nonempty)
    (h_subset : s ⊆ ⋃ i ∈ u, t i)
    (h_disj : ∀ i ∈ u, Disjoint (interior s) (interior (t i)))
    (hc : ∀ i ∈ u, IsClosed (t i)) :
    False := by
  have h_int_s : interior s ⊆ ⋃ i ∈ u, frontier (t i) := by
    intro x hx
    have h_in : x ∈ ⋃ i ∈ u, t i := h_subset (interior_subset hx)
    simp only [mem_iUnion, exists_prop] at h_in ⊢
    rcases h_in with ⟨i, hi, hxi⟩
    use i, hi
    have h_not_int : x ∉ interior (t i) := by
      intro h_int
      have : x ∈ interior s ∩ interior (t i) := ⟨hx, h_int⟩
      have hd := h_disj i hi
      rw [disjoint_iff_inter_eq_empty] at hd
      rw [hd] at this
      exact this
    exact ⟨subset_closure hxi, h_not_int⟩
  have h_empty_int : interior (⋃ i ∈ u, frontier (t i)) = ∅ := by
    apply mem_of_carrier_subset_union_interior_biUnion_empty
    · intro i hi
      exact isClosed_frontier
    · intro i hi
      have h1 := interior_frontier (hc i hi)
      exact h1
  have h_int_s_int : interior (interior s) ⊆ interior (⋃ i ∈ u, frontier (t i)) := by
    apply interior_mono
    exact h_int_s
  rw [interior_interior] at h_int_s_int
  rw [h_empty_int] at h_int_s_int
  have : interior s = ∅ := subset_empty_iff.mp h_int_s_int
  rw [this] at h_nonempty
  exact Set.not_nonempty_empty h_nonempty

private lemma mem_of_carrier_subset_union_isClosed_carrier {P : Protoset}
    (A : PlacedTile P) : IsClosed A.carrier := by
  dsimp [PlacedTile.carrier]
  apply IsCompact.isClosed
  exact IsCompact.vadd A.anchor (P.disk A.form).compact

private lemma mem_of_carrier_subset_union_interior_nonempty_carrier {P : Protoset}
    (A : PlacedTile P) : (interior A.carrier).Nonempty := by
  have hn := (P.disk A.form).interior_nonempty
  dsimp [PlacedTile.carrier]
  rw [interior_vadd]
  exact Set.Nonempty.image (fun x => A.anchor +ᵥ x) hn

/-- `lem:covered-tile-belongs`: if a tile `X` has interior disjoint from the
interior of every tile of the finite patch `F` other than `X`, and the carrier
of `X` is covered by the support of `F`, then `X ∈ F`. -/
theorem mem_of_carrier_subset_union (F : Patch P) (X : PlacedTile P)
    (hdisj : ∀ A ∈ F.tiles, A ≠ X → Disjoint (interior X.carrier) (interior A.carrier))
    (hsub : X.carrier ⊆ support F.tiles) : X ∈ F.tiles := by
  by_contra h_not_in
  have h_disj' : ∀ A ∈ F.tiles, Disjoint (interior X.carrier) (interior A.carrier) := by
    intro A hA
    have : A ≠ X := by rintro rfl; contradiction
    exact hdisj A hA this
  have h_fin := F.finite
  have h_sub_fin : X.carrier ⊆ ⋃ i ∈ h_fin.toFinset, i.carrier := by
    intro x hx
    have h_in : x ∈ support F.tiles := hsub hx
    simp only [support, mem_iUnion, exists_prop] at h_in ⊢
    rcases h_in with ⟨A, hA, hAx⟩
    use A
    have hA_u : A ∈ h_fin.toFinset := (Set.Finite.mem_toFinset h_fin).mpr hA
    exact ⟨hA_u, hAx⟩
  have hc : ∀ i ∈ h_fin.toFinset, IsClosed i.carrier :=
    fun i hi => mem_of_carrier_subset_union_isClosed_carrier i
  have h_disj_fin : ∀ i ∈ h_fin.toFinset, Disjoint (interior X.carrier) (interior i.carrier) :=
    fun i hi => h_disj' i ((Set.Finite.mem_toFinset h_fin).mp hi)
  have hn := mem_of_carrier_subset_union_interior_nonempty_carrier X
  exact mem_of_carrier_subset_union_empty_interior_of_subset_union_frontier h_fin.toFinset hn
    h_sub_fin h_disj_fin hc

end Patch

/-! ## `lem:allowed-hierarchy` -/

end Tilings

end
