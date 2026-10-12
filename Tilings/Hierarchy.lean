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
  sorry

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
    (0 : Pt) ∈ (B.translate (-w)).vertexSet ↔ w ∈ B.vertexSet := sorry

/-- Step 2 of the blueprint proof of `finite_crowns_step1_vertex`: in a side-to-side
patch (like a supertile), if `w` is a vertex of some tile `C` in the patch and `w` lies
in the closed carrier of another tile `B` in the patch, then `w` must be a vertex of `B`. -/
private lemma finite_crowns_step1_vertex_step2_sts {τ : Substitution P} (h : τ.STS) (n : ℕ)
    (p : P.Form) (C : PlacedTile P) (hC : C ∈ τ.supertile n p) (w : Pt) (hwC : w ∈ C.vertexSet)
    (B : PlacedTile P) (hB : B ∈ τ.supertile n p) (hwB : w ∈ B.carrier) :
    w ∈ B.vertexSet := sorry

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

/-- Step 1 of the blueprint proof of `exists_composition`: by thinning a sequence
of parent covers using the finite-parent lemma (or by Kőnig's lemma on a finite inverse
system), there exists a global parent assignment `T'` whose decomposition covers `T`
and whose finite patches occur in supertiles. -/
private lemma exists_composition_step1_parents (τ : Substitution P) {T : PlaneTiling P}
    (hT : τ.IsSubstitutionTiling T) :
    ∃ T' : Set (PlacedTile P),
      (∀ F' ⊆ T', F'.Finite → ∃ (n : ℕ) (p : P.Form), OccursIn F' (τ.supertile n p)) ∧
      T.tiles ⊆ τ.decompose T' := by
  sorry

/-- Step 1 of the blueprint proof of `exists_composition_step2_disjoint`: supertiles have
disjoint interiors. -/
private lemma exists_composition_step2_disjoint_supertile (τ : Substitution P) (n : ℕ)
    (p : P.Form) :
    DisjointInteriors (τ.supertile n p) := by
  sorry

/-- Step 2 of the blueprint proof of `exists_composition_step2_disjoint`: translation
preserves disjoint interiors. -/
private lemma exists_composition_step2_disjoint_translate_inv {v : Pt} {S : Set (PlacedTile P)}
    (h : DisjointInteriors (translateSet v S)) : DisjointInteriors S := by
  sorry

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

/-- Step 3 of the blueprint proof of `exists_composition`: no extra child can occur in
the decomposition because the plane is already covered by `T` with disjoint interiors,
so the decomposition is exactly `T`. -/
private lemma exists_composition_step3_decompose_eq (τ : Substitution P) {T : PlaneTiling P}
    (T' : Set (PlacedTile P))
    (h_disj : DisjointInteriors T') (h_cov : T.tiles ⊆ τ.decompose T') :
    τ.decompose T' = T.tiles := by
  sorry

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

/-- `lem:hierarchy-step`: for `m > 0`, a plane tiling is `τ`-hierarchical
iff it is `τ^m`-hierarchical.  (Side-to-side hierarchy is *not* claimed to
transfer; that needs the alignment tuples.) -/
theorem hierarchical_power_iff (τ : Substitution P) (m : ℕ) (hm : 0 < m)
    (T : PlaneTiling P) :
    τ.IsHierarchical T ↔ (τ.pow m hm).IsHierarchical T := by
  sorry

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
