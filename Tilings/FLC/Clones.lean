import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Tilings.Crowns

/-!
# Genuine-corner collared clones (skeleton)

Statements of the FLC-reduction nodes of `main.tex`:

* `lem:finite-neighbourhoods` — `FLC.finite_neighbourhoods`
* `def:clones`                — `FLC.coarsen`, `FLC.GenuineCornerClone`,
                                 `FLC.cloneProtoset`, `FLC.refinedSubstitution`,
                                 `FLC.cloneDecoration`
* `lem:clone-sts`             — `FLC.refinedSubstitution_sts`,
                                 `FLC.refinedSubstitution_hereditary`
                                 (and `FLC.refinedSubstitution_commutes`)
* `lem:clone-substitution-lift` — `FLC.substitution_clone_lift_iff`
* `lem:clone-hierarchy-lift`  — `FLC.hierarchy_clone_lift_iff`
* `lem:segment-rules`         — `FLC.forget_vertices_preserves_sofic`

## Modelling choices

* Neighbourhoods, contexts and clone vertices only depend on carriers and
  on *genuine* corners, so clones are built directly over `P`: the clone
  vertex set of `(A, S_A)` is the set of genuine corners of tiles of `S_A`
  lying on `∂A` (the tile `A` itself is in `S_A`, so its own genuine corners
  are included and its collinear dummy vertices are not).  This is the same
  as first coarsening (`FLC.coarsen`) and then adding context corners.
* A clone disk with a prescribed finite vertex set on the boundary is
  obtained from a `sorry`'d existence lemma (`exists_cloneDisk`) by choice.
* Contexts are normalized: the selected tile sits at anchor `0`.
-/

open Set Pointwise

noncomputable section

namespace Tilings

open Substitution

variable {P : Protoset}

/-! ## Coarsening a polygonal disk: erase collinear listed vertices -/

namespace PolygonalDisk

variable (D : PolygonalDisk)

open Classical in
/-- Indices of the genuine listed vertices. -/
def genuineIdx : Finset (Fin D.n) := Finset.univ.filter fun i => D.IsGenuineVertex i

/-- Number of genuine listed vertices. -/
def genuineCount : ℕ := D.genuineIdx.card

/-- Increasing enumeration of the genuine listed vertices (this preserves the
cyclic order). -/
def genuineEnum : Fin D.genuineCount ≃o D.genuineIdx := D.genuineIdx.orderIsoOfFin rfl

/-- The `i`-th genuine vertex. -/
def coarseVertex (i : Fin D.genuineCount) : Pt := D.vertex (D.genuineEnum i).1

/-- Step 1 of the blueprint proof of `three_le_genuineCount_step1`:
If the vertices are not collinear, then the number of extreme points of their convex hull is at least 3. -/
private lemma three_le_genuineCount_step1_step1_extreme_points_lower_bound
    (h : ¬ Collinear ℝ D.vertexSet) :
    3 ≤ (extremePoints ℝ (convexHull ℝ D.vertexSet)).ncard := by
  by_contra hcard
  have hcard' : (extremePoints ℝ (convexHull ℝ D.vertexSet)).ncard < 3 := by
    omega
  have hVfin : D.vertexSet.Finite := Set.finite_range D.vertex
  have hcomp : IsCompact (convexHull ℝ D.vertexSet) := hVfin.isCompact_convexHull
  have hEfin : (extremePoints ℝ (convexHull ℝ D.vertexSet)).Finite :=
    hVfin.subset extremePoints_convexHull_subset
  let s := hEfin.toFinset
  have hs_card : s.card < 3 := by
    dsimp [s]
    rw [← Set.ncard_eq_toFinset_card _ hEfin]
    exact hcard'
  have hEcol : Collinear ℝ (extremePoints ℝ (convexHull ℝ D.vertexSet)) := by
    rw [← hEfin.coe_toFinset]
    change Collinear ℝ (↑s : Set Pt)
    have hs_card_le : s.card ≤ 2 := by omega
    have hs_cases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
    rcases hs_cases with hs0 | hs1 | hs2
    · have hs' : s = ∅ := Finset.card_eq_zero.mp hs0
      rw [hs']
      have hset : (↑(∅ : Finset Pt) : Set Pt) = ∅ := by
        ext x
        simp
      rw [hset]
      exact collinear_empty ℝ Pt
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hs1
      rw [ha]
      have hset : (↑({a} : Finset Pt) : Set Pt) = {a} := by
        ext x
        simp
      rw [hset]
      exact collinear_singleton ℝ a
    · obtain ⟨a, b, _, habs⟩ := Finset.card_eq_two.mp hs2
      rw [habs]
      have hset : (↑({a, b} : Finset Pt) : Set Pt) = {a, b} := by
        ext x
        simp
      rw [hset]
      exact collinear_pair ℝ a b
  have hclosed : IsClosed (convexHull ℝ
      (extremePoints ℝ (convexHull ℝ D.vertexSet))) := hEfin.isClosed_convexHull
  have hclosure := closure_convexHull_extremePoints hcomp
    (convex_convexHull ℝ D.vertexSet)
  have hCE : convexHull ℝ (extremePoints ℝ (convexHull ℝ D.vertexSet)) =
      convexHull ℝ D.vertexSet := by
    calc
      convexHull ℝ (extremePoints ℝ (convexHull ℝ D.vertexSet)) =
          closure (convexHull ℝ (extremePoints ℝ (convexHull ℝ D.vertexSet))) :=
        hclosed.closure_eq.symm
      _ = convexHull ℝ D.vertexSet := hclosure
  have hline : Collinear ℝ
      (affineSpan ℝ (extremePoints ℝ (convexHull ℝ D.vertexSet)) : Set Pt) := by
    rw [collinear_iff_rank_le_one, ← AffineSubspace.direction_eq_vectorSpan,
      direction_affineSpan]
    exact hEcol
  apply h
  apply Collinear.subset (s₂ := (affineSpan ℝ
      (extremePoints ℝ (convexHull ℝ D.vertexSet)) : Set Pt))
  · exact (subset_convexHull ℝ D.vertexSet).trans (by
      intro x hx
      have hx' : x ∈ convexHull ℝ (extremePoints ℝ (convexHull ℝ D.vertexSet)) := by
        rw [hCE]
        exact hx
      exact convexHull_subset_affineSpan _ hx')
  · exact hline

/-- `finRotate` has no fixed point on `Fin N` when `2 ≤ N`: a helper for
`three_le_genuineCount_step1_step2_extreme_points_subset_genuine`. -/
private lemma three_le_genuineCount_step1_step2_extreme_points_subset_genuine_aux1
    {N : ℕ} (hN : 2 ≤ N) (x : Fin N) : finRotate N x ≠ x := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have := congrArg (· - x) h
  simp at this

/-- `finRotate` composed with itself has no fixed point on `Fin N` when `3 ≤ N`: a
helper for `three_le_genuineCount_step1_step2_extreme_points_subset_genuine`. -/
private lemma three_le_genuineCount_step1_step2_extreme_points_subset_genuine_aux2
    {m : ℕ} (hm : 3 ≤ m) (k : Fin m) : finRotate m (finRotate m k) ≠ k := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [finRotate_succ_apply, finRotate_succ_apply]
  intro h
  have h2 : (k + 1 + 1).val = k.val := by rw [h]
  rw [Fin.val_add, Fin.val_add, Fin.val_one'] at h2
  have hk := k.isLt
  rcases Nat.lt_or_ge (k.val + 1) (m + 1) with h3 | h3
  · rw [Nat.mod_eq_of_lt (show 1 < m + 1 by omega), Nat.mod_eq_of_lt h3] at h2
    rcases Nat.lt_or_ge (k.val + 1 + 1) (m + 1) with h4 | h4
    · rw [Nat.mod_eq_of_lt h4] at h2; omega
    · rw [show k.val + 1 + 1 = m + 1 by omega, Nat.mod_self] at h2; omega
  · rw [Nat.mod_eq_of_lt (show 1 < m + 1 by omega), show k.val + 1 = m + 1 by omega,
      Nat.mod_self] at h2
    rw [Nat.mod_eq_of_lt (show 0 + 1 < m + 1 by omega)] at h2; omega

/-- Step 2 of the blueprint proof of `three_le_genuineCount_step1`:
Every extreme point of the convex hull of the vertices is a genuine vertex. -/
private lemma three_le_genuineCount_step1_step2_extreme_points_subset_genuine :
    extremePoints ℝ (convexHull ℝ D.vertexSet) ⊆ D.vertex '' D.genuineIdx := by
  intro x hx
  obtain ⟨i, rfl⟩ := extremePoints_convexHull_subset hx
  by_contra hcon
  have hcol : Collinear ℝ ({D.vertex ((finRotate D.n).symm i), D.vertex i,
      D.vertex (finRotate D.n i)} : Set Pt) := by
    have hnotgen : i ∉ D.genuineIdx := fun h => hcon ⟨i, h, rfl⟩
    simpa [PolygonalDisk.genuineIdx, Finset.mem_filter, PolygonalDisk.IsGenuineVertex,
      not_not] using hnotgen
  set j : Fin D.n := (finRotate D.n).symm i with hjdef
  have hjn : finRotate D.n j = i := by rw [hjdef]; exact Equiv.apply_symm_apply _ i
  have hn2 : 2 ≤ D.n := by have := D.three_le; omega
  have hn3 : 3 ≤ D.n := D.three_le
  have hji : j ≠ i := by
    intro h
    apply three_le_genuineCount_step1_step2_extreme_points_subset_genuine_aux1 hn2 i
    rw [h] at hjn
    exact hjn
  have hri : finRotate D.n i ≠ i :=
    three_le_genuineCount_step1_step2_extreme_points_subset_genuine_aux1 hn2 i
  have hjr : j ≠ finRotate D.n i := by
    intro h
    apply three_le_genuineCount_step1_step2_extreme_points_subset_genuine_aux2 hn3 i
    rw [h] at hjn
    exact hjn
  have hpq : D.vertex j ≠ D.vertex i := fun h => hji (D.vertex_injective h)
  have hqr : D.vertex i ≠ D.vertex (finRotate D.n i) :=
    fun h => hri (D.vertex_injective h).symm
  have hpr : D.vertex j ≠ D.vertex (finRotate D.n i) := fun h => hjr (D.vertex_injective h)
  have hpC : D.vertex j ∈ convexHull ℝ D.vertexSet := subset_convexHull ℝ D.vertexSet ⟨j, rfl⟩
  have hrC : D.vertex (finRotate D.n i) ∈ convexHull ℝ D.vertexSet :=
    subset_convexHull ℝ D.vertexSet ⟨finRotate D.n i, rfl⟩
  have hsimple := D.simple j i hji
  rw [hjn] at hsimple
  rcases hcol.wbtw_or_wbtw_or_wbtw with h1 | h2 | h3
  · have hqseg : D.vertex i ∈ segment ℝ (D.vertex j) (D.vertex (finRotate D.n i)) :=
      h1.mem_segment
    have hqopen := mem_openSegment_of_ne_left_right hpq hqr.symm hqseg
    exact hpq (hx.2 hpC hrC hqopen)
  · have hrseg : D.vertex (finRotate D.n i) ∈ segment ℝ (D.vertex i) (D.vertex j) :=
      h2.mem_segment
    have hrj : D.vertex (finRotate D.n i) ∈ segment ℝ (D.vertex j) (D.vertex i) := by
      rw [segment_symm]; exact hrseg
    have hri' : D.vertex (finRotate D.n i) ∈
        segment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) :=
      right_mem_segment ℝ (D.vertex i) (D.vertex (finRotate D.n i))
    have hmem := hsimple ⟨hrj, hri'⟩
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem.1 with hc | hc
    · exact hpr hc.symm
    · exact hqr hc.symm
  · have hpseg : D.vertex j ∈ segment ℝ (D.vertex (finRotate D.n i)) (D.vertex i) :=
      h3.mem_segment
    have hpi : D.vertex j ∈ segment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) := by
      rw [segment_symm]; exact hpseg
    have hpj : D.vertex j ∈ segment ℝ (D.vertex j) (D.vertex i) :=
      left_mem_segment ℝ (D.vertex j) (D.vertex i)
    have hmem := hsimple ⟨hpj, hpi⟩
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem.2 with hc | hc
    · exact hpq hc
    · exact hpr hc

/-- Step 1 of the blueprint proof of `three_le_genuineCount`: if there are at most 2
genuine corners, the vertices are collinear. -/
private lemma three_le_genuineCount_step1 (h : D.genuineCount < 3) :
    Collinear ℝ D.vertexSet := by
  by_contra h_not_collinear
  have h1 := three_le_genuineCount_step1_step1_extreme_points_lower_bound D h_not_collinear
  have h2 := three_le_genuineCount_step1_step2_extreme_points_subset_genuine D
  have h_fin_genuine : (D.genuineIdx : Set (Fin D.n)).Finite := D.genuineIdx.finite_toSet
  have h_fin_image : (D.vertex '' D.genuineIdx).Finite := h_fin_genuine.image D.vertex
  have h3 : (extremePoints ℝ (convexHull ℝ D.vertexSet)).ncard ≤
      (D.vertex '' D.genuineIdx).ncard :=
    ncard_le_ncard h2 h_fin_image
  have h4 : (D.vertex '' D.genuineIdx).ncard ≤ (D.genuineIdx : Set (Fin D.n)).ncard :=
    ncard_image_le h_fin_genuine
  have h5 : (D.genuineIdx : Set (Fin D.n)).ncard = D.genuineCount := ncard_coe_finset D.genuineIdx
  omega

/-- Step 2 of the blueprint proof of `three_le_genuineCount`: if the vertices are
collinear, the boundary of the carrier is contained in a line. -/
private lemma three_le_genuineCount_step2
    (h_eq : frontier D.carrier =
      ⋃ i : Fin D.n, segment ℝ (D.vertex i) (D.vertex (finRotate D.n i)))
    (h : Collinear ℝ D.vertexSet) :
    Collinear ℝ (frontier D.carrier) := by
  rw [h_eq]
  apply Collinear.subset (s₂ := convexHull ℝ D.vertexSet)
  · apply iUnion_subset
    intro i
    apply segment_subset_convexHull
    · exact mem_range_self i
    · exact mem_range_self (finRotate D.n i)
  · unfold Collinear at *
    rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
    exact h

/-- Step 1 of the blueprint proof of `three_le_genuineCount_step3`: an open subset of the Euclidean plane contained in a line must be empty. -/
private lemma three_le_genuineCount_step3_step1_open_collinear_empty
    {U : Set Pt} (hU : IsOpen U) (hc : Collinear ℝ U) : ¬ U.Nonempty := by
  intro h_nonempty
  have h_span := IsOpen.affineSpan_eq_top hU h_nonempty
  have h_dir : (affineSpan ℝ U).direction = ⊤ := by
    rw [h_span, AffineSubspace.direction_top]
  have h_vec : vectorSpan ℝ U = ⊤ := by
    rw [← direction_affineSpan, h_dir]
  have h_finrank_top : Module.finrank ℝ (⊤ : Submodule ℝ Pt) = 2 := by
    rw [finrank_top, finrank_euclideanSpace, Fintype.card_fin]
  have hc' : Module.finrank ℝ (vectorSpan ℝ U) ≤ 1 := by
    haveI : FiniteDimensional ℝ (vectorSpan ℝ U) := hc.finiteDimensional_vectorSpan
    exact collinear_iff_finrank_le_one.mp hc
  rw [h_vec] at hc'
  omega

/-- Step 1 of the blueprint proof of
three_le_genuineCount_step3_step2_bounded_open_subset_line: a point outside a
collinear set has a nonzero ray disjoint from that set. -/
private lemma three_le_genuineCount_step3_step2_bounded_open_subset_line_step1_disjoint_ray
    {L : Set Pt} (hL : Collinear ℝ L) {p : Pt} (hp : p ∉ L) :
    ∃ v : Pt, v ≠ 0 ∧ ∀ t : ℝ, 0 ≤ t → p + t • v ∉ L := by
  rcases Set.eq_empty_or_nonempty L with rfl | hLne
  · let e : Pt := EuclideanSpace.single 0 1
    refine ⟨e, ?_, fun t ht => by simp⟩
    intro he
    change EuclideanSpace.single 0 (1 : ℝ) = 0 at he
    exact one_ne_zero (EuclideanSpace.single_eq_zero_iff.mp he)
  · obtain ⟨q, hq⟩ := hLne
    obtain ⟨a, ha⟩ := (collinear_iff_of_mem hq).mp hL
    by_cases ha0 : a = 0
    · let v : Pt := p - q
      refine ⟨v, ?_, ?_⟩
      · intro hv
        apply hp
        rw [sub_eq_zero.mp hv]
        exact hq
      · intro t ht hx
        obtain ⟨r, hr⟩ := ha _ hx
        rw [ha0, smul_zero, zero_vadd] at hr
        have heq : p + t • (p - q) = q := by simpa [v] using hr
        have hzero : (1 + t) • (p - q) = 0 := by
          calc
            (1 + t) • (p - q) = p + t • (p - q) - q := by module
            _ = 0 := sub_eq_zero.mpr heq
        have hscalar : (1 + t : ℝ) ≠ 0 := by linarith
        have hpq : p - q = 0 := (smul_eq_zero.mp hzero).resolve_left hscalar
        exact hp (sub_eq_zero.mp hpq ▸ hq)
    · let w : Pt := EuclideanSpace.single 0 (a 1) -
        EuclideanSpace.single 1 (a 0)
      let det : Pt → ℝ := fun x => x 0 * a 1 - x 1 * a 0
      have hw0 : w 0 = a 1 := by simp [w, EuclideanSpace.single_apply]
      have hw1 : w 1 = -(a 0) := by simp [w, EuclideanSpace.single_apply]
      have ha_coords : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
        by_contra h
        push_neg at h
        apply ha0
        ext i
        fin_cases i
        · exact h.1
        · exact h.2
      have hdetw : 0 < a 1 * a 1 + a 0 * a 0 := by
        rcases ha_coords with h0 | h1
        · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (a 1)]
        · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (a 0)]
      have hwne : w ≠ 0 := by
        intro hw
        have hw0' : a 1 = 0 := by simpa [hw] using hw0.symm
        have hw1' : a 0 = 0 := by simpa [hw] using hw1.symm
        apply ha0
        ext i
        fin_cases i
        · exact hw1'
        · exact hw0'
      have hdet : 0 ≤ det (p - q) ∨ det (p - q) < 0 := by
        by_cases h : 0 ≤ det (p - q)
        · exact Or.inl h
        · exact Or.inr (lt_of_not_ge h)
      rcases hdet with hdet | hdet
      · refine ⟨w, ?_, ?_⟩
        · exact hwne
        · intro t ht hx
          obtain ⟨r, hr⟩ := ha _ hx
          rw [vadd_eq_add] at hr
          have hvec : p - q + t • w = r • a := by
            calc
              p - q + t • w = (p + t • w) - q := by module
              _ = (r • a + q) - q := by rw [← hr]
              _ = r • a := by module
          have hdet_eq := congrArg det hvec
          by_cases ht0 : t = 0
          · apply hp
            rw [ht0] at hx
            simpa using hx
          · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
            dsimp [det] at hdet_eq
            rw [hw0, hw1] at hdet_eq
            dsimp [det] at hdet
            ring_nf at hdet_eq
            nlinarith
      · let v : Pt := -w
        refine ⟨v, ?_, ?_⟩
        · exact neg_ne_zero.mpr hwne
        · intro t ht hx
          obtain ⟨r, hr⟩ := ha _ hx
          rw [vadd_eq_add] at hr
          have hvec : p - q + t • (-w) = r • a := by
            calc
              p - q + t • (-w) = (p + t • v) - q := by simp [v]; module
              _ = (r • a + q) - q := by rw [← hr]
              _ = r • a := by module
          have hdet_eq := congrArg det hvec
          dsimp [det] at hdet_eq
          rw [hw0, hw1] at hdet_eq
          dsimp [det] at hdet
          ring_nf at hdet_eq
          nlinarith

/-- Step 2 of the blueprint proof of
three_le_genuineCount_step3_step2_bounded_open_subset_line: a bounded set
cannot contain a whole nonzero ray starting at one of its points. -/
private lemma three_le_genuineCount_step3_step2_bounded_open_subset_line_step2_ray_endpoint
    {U : Set Pt} (hbdd : Bornology.IsBounded U) {p v : Pt}
    (hp : p ∈ U) (hv : v ≠ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ p + t • v ∉ U := by
  obtain ⟨r, hr⟩ := hbdd.subset_closedBall p
  have hr0 : 0 ≤ r := by
    have h := hr hp
    rw [Metric.mem_closedBall, dist_self] at h
    exact h
  let t : ℝ := r / ‖v‖ + 1
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  refine ⟨t, ht, ?_⟩
  intro hpt
  have hclosed := hr hpt
  rw [Metric.mem_closedBall] at hclosed
  have hdist : dist (p + t • v) p = ‖t • v‖ := by
    rw [dist_eq_norm]
    congr 1
    abel
  rw [hdist, norm_smul, Real.norm_of_nonneg ht] at hclosed
  dsimp [t] at hclosed
  rw [add_mul, div_mul_cancel₀ r (ne_of_gt hvnorm), one_mul] at hclosed
  linarith

/-- Step 3 of the blueprint proof of
three_le_genuineCount_step3_step2_bounded_open_subset_line: a segment from
an open-set point to an exterior point meets the frontier. -/
private lemma three_le_genuineCount_step3_step2_bounded_open_subset_line_step3_frontier_meets_segment
    {U : Set Pt} (hU : IsOpen U) {p q : Pt} (hp : p ∈ U) (hq : q ∉ U) :
    (segment ℝ p q ∩ frontier U).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hsub : segment ℝ p q ⊆ U ∪ interior Uᶜ := by
    intro z hz
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · right
      by_contra hzi
      have hzf : z ∈ frontier U := by
        rw [hU.frontier_eq, closure_eq_compl_interior_compl]
        exact ⟨hzi, hzU⟩
      have hz' : z ∈ segment ℝ p q ∩ frontier U := ⟨hz, hzf⟩
      rwa [hne] at hz'
  have hd : Disjoint U (interior Uᶜ) := by
    rw [Set.disjoint_left]
    intro z hzU hzUc
    exact (interior_subset hzUc) hzU
  rcases (convex_segment p q).isPreconnected.subset_or_subset
      hU isOpen_interior hd hsub with h | h
  · exact hq (h (right_mem_segment ℝ p q))
  · exact (interior_subset (h (left_mem_segment ℝ p q))) hp

/-- Step 2 of the blueprint proof of three_le_genuineCount_step3: a bounded open set
whose boundary is contained in a line must itself be contained in that line. -/
private lemma three_le_genuineCount_step3_step2_bounded_open_subset_line
    {U : Set Pt} (hU : IsOpen U) (hbdd : Bornology.IsBounded U)
    {L : Set Pt} (hL : Collinear ℝ L) (hfr : frontier U ⊆ L) : U ⊆ L := by
  intro p hp
  by_contra hpL
  obtain ⟨v, hv, hvL⟩ :=
    three_le_genuineCount_step3_step2_bounded_open_subset_line_step1_disjoint_ray hL hpL
  obtain ⟨t, ht, hq⟩ :=
    three_le_genuineCount_step3_step2_bounded_open_subset_line_step2_ray_endpoint hbdd hp hv
  let q : Pt := p + t • v
  have hq' : q ∉ U := by
    simpa [q] using hq
  obtain ⟨z, hzseg, hzfr⟩ :=
    three_le_genuineCount_step3_step2_bounded_open_subset_line_step3_frontier_meets_segment
      hU hp hq'
  rw [segment_eq_image' ℝ p q] at hzseg
  rcases hzseg with ⟨s, hs, hsz⟩
  have hst : 0 ≤ s * t := mul_nonneg hs.1 ht
  apply hvL (s * t) hst
  have hzp : z = p + (s * t) • v := by
    calc
      z = p + s • (q - p) := hsz.symm
      _ = p + (s * t) • v := by
        dsimp [q]
        congr 1
        module
  rw [← hzp]
  exact hfr hzfr

/-- Step 3 of the blueprint proof of `three_le_genuineCount`: if the boundary of a
regular closed set is contained in a line, its interior is empty. -/
private lemma three_le_genuineCount_step3 (h_reg : closure (interior D.carrier) = D.carrier)
    (h : Collinear ℝ (frontier D.carrier)) :
    ¬ (interior D.carrier).Nonempty := by
  set U := interior D.carrier
  have hU : IsOpen U := isOpen_interior
  have hbdd : Bornology.IsBounded U :=
    Bornology.IsBounded.subset D.compact.isBounded interior_subset
  have h_closed : IsClosed D.carrier := D.compact.isClosed
  have hfr_eq : frontier U = frontier D.carrier := by
    have h_fr1 : frontier D.carrier = D.carrier \ U := h_closed.frontier_eq
    have h_fr2 : frontier U = closure U \ U := by
      have hd : closure U \ interior U = frontier U := closure_diff_interior U
      rw [isOpen_interior.interior_eq] at hd
      exact hd.symm
    rw [h_reg] at h_fr2
    rw [h_fr1, h_fr2]
  have hfr : frontier U ⊆ frontier D.carrier := by rw [hfr_eq]
  have h_subset : U ⊆ frontier D.carrier :=
    three_le_genuineCount_step3_step2_bounded_open_subset_line hU hbdd h hfr
  have hU_col : Collinear ℝ U := Collinear.subset h_subset h
  exact three_le_genuineCount_step3_step1_open_collinear_empty hU hU_col

/-- A simple polygon has at least three genuine corners. -/
theorem three_le_genuineCount : 3 ≤ D.genuineCount := by
  by_contra h
  push_neg at h
  exact three_le_genuineCount_step3 D D.regular_closed
    (three_le_genuineCount_step2 D D.frontier_eq (three_le_genuineCount_step1 D h))
    D.interior_nonempty

theorem coarseVertex_injective : Function.Injective D.coarseVertex := by
  intro a b hab
  exact D.genuineEnum.injective (Subtype.ext (D.vertex_injective hab))

private lemma clones_finRotate_ne_self {n : ℕ} (hn : 2 ≤ n)
    (i : Fin n) : finRotate n i ≠ i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have h1 : (1 : Fin (m + 1)) = 0 := by
    have := congrArg (fun x => x - i) h
    simpa using this
  have : NeZero (m + 1) := ⟨by omega⟩
  rw [Fin.one_eq_zero_iff] at h1
  omega

private lemma clones_finRotate_sq_ne {n : ℕ} (hn : 3 ≤ n)
    (i : Fin n) : finRotate n (finRotate n i) ≠ i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_succ_apply, finRotate_succ_apply]
  intro h
  have h2 : (i + 1 + 1).val = i.val := by rw [h]
  rw [Fin.val_add, Fin.val_add, Fin.val_one'] at h2
  have hi := i.isLt
  rcases Nat.lt_or_ge (i.val + 1) (m + 1) with h3 | h3
  · rw [Nat.mod_eq_of_lt (show 1 < m + 1 by omega), Nat.mod_eq_of_lt h3] at h2
    rcases Nat.lt_or_ge (i.val + 1 + 1) (m + 1) with h4 | h4
    · rw [Nat.mod_eq_of_lt h4] at h2
      omega
    · rw [show i.val + 1 + 1 = m + 1 by omega, Nat.mod_self] at h2
      omega
  · rw [Nat.mod_eq_of_lt (show 1 < m + 1 by omega),
      show i.val + 1 = m + 1 by omega, Nat.mod_self] at h2
    rw [Nat.mod_eq_of_lt (show 0 + 1 < m + 1 by omega)] at h2
    omega

/-- A dummy vertex lies strictly between its two cyclic neighbours. -/
private lemma dummy_sbtw (i : Fin D.n) (hi : ¬D.IsGenuineVertex i) :
    Sbtw ℝ (D.vertex ((finRotate D.n).symm i)) (D.vertex i)
      (D.vertex (finRotate D.n i)) := by
  let p := (finRotate D.n).symm i
  let q := finRotate D.n i
  have hp_ne : p ≠ i := by
    intro h
    have := congrArg (finRotate D.n) h
    exact clones_finRotate_ne_self (by have := D.three_le; omega) i
      (by simpa [p, q] using this.symm)
  have hi_ne : i ≠ q :=
    (clones_finRotate_ne_self (by have := D.three_le; omega) i).symm
  have hp_ne_q : p ≠ q := by
    intro h
    have := congrArg (finRotate D.n) h
    exact clones_finRotate_sq_ne D.three_le i (by simpa [p, q] using this.symm)
  have hvpi : D.vertex p ≠ D.vertex i := fun h => hp_ne (D.vertex_injective h)
  have hviq : D.vertex i ≠ D.vertex q := fun h => hi_ne (D.vertex_injective h)
  have hvpq : D.vertex p ≠ D.vertex q := fun h => hp_ne_q (D.vertex_injective h)
  have hcol : Collinear ℝ ({D.vertex p, D.vertex i, D.vertex q} : Set Pt) := by
    simpa [PolygonalDisk.IsGenuineVertex, p, q] using hi
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact ⟨h, hvpi.symm, hviq⟩
  · exfalso
    have hs := D.simple p i hp_ne
    have hp_next : finRotate D.n p = i := by simp [p]
    have hmem := hs ⟨by simpa [hp_next, segment_symm] using h.mem_segment,
      by exact right_mem_segment ℝ _ _⟩
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem.1 with hqp | hqi
    · exact hvpq hqp.symm
    · apply hviq
      rw [← hp_next]
      exact hqi.symm
  · exfalso
    have hs := D.simple p i hp_ne
    have hp_next : finRotate D.n p = i := by simp [p]
    have hmem := hs ⟨by exact left_mem_segment ℝ _ _,
      by simpa [segment_symm] using h.mem_segment⟩
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem.2 with hpi | hpq
    · exact hvpi hpi
    · exact hvpq hpq

private lemma sbtw_chain {w : ℕ → Pt} {a d : ℕ} (hd : 0 < d)
    (hlocal : ∀ r, r < d →
      Sbtw ℝ (w (a + r)) (w (a + r + 1)) (w (a + r + 2))) :
    Sbtw ℝ (w a) (w (a + d)) (w (a + d + 1)) := by
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hd0 : d = 0
      · subst d
        simpa using hlocal 0 (by omega)
      · have hprev := ih (by omega) (fun r hr => hlocal r (by omega))
        have hlast := hlocal d (by omega)
        simpa [Nat.add_assoc] using hprev.trans_expand_right hlast

private lemma chain_wbtw {w : ℕ → Pt} {a m r : ℕ} (hm : 0 < m) (hr : r ≤ m)
    (hlocal : ∀ t, t + 1 < m →
      Sbtw ℝ (w (a + t)) (w (a + t + 1)) (w (a + t + 2))) :
    Wbtw ℝ (w a) (w (a + r)) (w (a + m)) := by
  induction m generalizing r with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        interval_cases r
        · simp
        · simp
      · by_cases hrm : r ≤ m
        · have hprev := ih (by omega) hrm (fun t ht => hlocal t (by omega))
          have hlast := sbtw_chain (a := a) (d := m) (by omega)
            (fun t ht => hlocal t (by omega))
          exact hlast.wbtw.trans_left (by simpa using hprev)
        · have : r = m + 1 := by omega
          subst r
          simp

private lemma segment_split {a b c : Pt} (h : Wbtw ℝ a b c) :
    segment ℝ a c ⊆ segment ℝ a b ∪ segment ℝ b c := by
  rw [← insert_endpoints_openSegment]
  rintro x (rfl | rfl | hx)
  · exact Or.inl (left_mem_segment ℝ _ _)
  · exact Or.inr (right_mem_segment ℝ _ _)
  · have hbline : b ∈ Set.range (AffineMap.lineMap a c : ℝ → Pt) := by
      rcases h with ⟨t, ht, hb⟩
      exact ⟨t, hb⟩
    have hs := openSegment_subset_union a c hbline hx
    rcases hs with hb | hs
    · subst x
      exact Or.inl (right_mem_segment ℝ _ _)
    · rcases hs with hx | hx
      · exact Or.inl (openSegment_subset_segment ℝ _ _ hx)
      · exact Or.inr (openSegment_subset_segment ℝ _ _ hx)

private lemma chain_side_subset {w : ℕ → Pt} {a m r : ℕ} (hm : 0 < m)
    (hr : r < m) (hlocal : ∀ t, t + 1 < m →
      Sbtw ℝ (w (a + t)) (w (a + t + 1)) (w (a + t + 2))) :
    segment ℝ (w (a + r)) (w (a + r + 1)) ⊆ segment ℝ (w a) (w (a + m)) := by
  apply (convex_segment (w a) (w (a + m))).segment_subset
  · exact (chain_wbtw (r := r) hm (by omega) hlocal).mem_segment
  · exact (chain_wbtw (r := r + 1) hm (by omega) hlocal).mem_segment

private lemma chain_segment_subset {w : ℕ → Pt} {a m : ℕ} (hm : 0 < m)
    (hlocal : ∀ t, t + 1 < m →
      Sbtw ℝ (w (a + t)) (w (a + t + 1)) (w (a + t + 2))) :
    segment ℝ (w a) (w (a + m)) ⊆
      ⋃ r ∈ {r : ℕ | r < m}, segment ℝ (w (a + r)) (w (a + r + 1)) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp
      · have hprev := ih (by omega) (fun t ht => hlocal t (by omega))
        have hlast := sbtw_chain (a := a) (d := m) (by omega)
          (fun t ht => hlocal t (by omega))
        apply (segment_split hlast.wbtw).trans
        rintro x (hx | hx)
        · rcases Set.mem_iUnion.mp (hprev hx) with ⟨r, hr⟩
          rcases Set.mem_iUnion.mp hr with ⟨hrm, hxr⟩
          have hrm' : r < m := hrm
          have hrm'' : r ∈ {r : ℕ | r < m + 1} := hrm'.trans (Nat.lt_succ_self m)
          exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hrm'', hxr⟩⟩
        · exact Set.mem_iUnion.mpr
            ⟨m, Set.mem_iUnion.mpr ⟨(show m < m + 1 by omega), by simpa using hx⟩⟩

private def cyclicIndex {n : ℕ} (hn : 0 < n) (a : Fin n) (k : ℕ) : Fin n :=
  ⟨(a.val + k) % n, Nat.mod_lt _ hn⟩

private def cyclicDist {n : ℕ} (a b : Fin n) : ℕ :=
  if a.val ≤ b.val then b.val - a.val else n - a.val + b.val

private lemma cyclicIndex_zero {n : ℕ} (hn : 0 < n) (a : Fin n) :
    cyclicIndex hn a 0 = a := by
  apply Fin.ext
  simp [cyclicIndex, Nat.mod_eq_of_lt a.isLt]

private lemma cyclicIndex_succ {n : ℕ} (hn : 0 < n) (a : Fin n) (k : ℕ) :
    cyclicIndex hn a (k + 1) = finRotate n (cyclicIndex hn a k) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  apply Fin.ext
  simp only [cyclicIndex, finRotate_succ_apply, Fin.val_add, Fin.val_one']
  rw [Nat.add_mod_mod, Nat.mod_add_mod]
  rw [Nat.add_assoc]

private lemma cyclicDist_pos {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    0 < cyclicDist a b := by
  simp only [cyclicDist]
  split_ifs with h
  · have : a.val ≠ b.val := fun h' => hab (Fin.ext h')
    omega
  · have := a.isLt
    omega

private lemma cyclicIndex_dist {n : ℕ} (hn : 0 < n) (a b : Fin n) :
    cyclicIndex hn a (cyclicDist a b) = b := by
  apply Fin.ext
  simp only [cyclicIndex, cyclicDist]
  split_ifs with h
  · rw [show a.val + (b.val - a.val) = b.val by omega,
      Nat.mod_eq_of_lt b.isLt]
  · rw [show a.val + (n - a.val + b.val) = n + b.val by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt b.isLt]

private lemma cyclicIndex_between {n : ℕ} (hn : 0 < n) {a b : Fin n}
    (hab : a < b) {k : ℕ} (hk0 : 0 < k) (hk : k < cyclicDist a b) :
    a < cyclicIndex hn a k ∧ cyclicIndex hn a k < b := by
  have hle : a.val ≤ b.val := hab.le
  have hm : cyclicDist a b = b.val - a.val := by simp [cyclicDist, hle]
  rw [hm] at hk
  have hsum : a.val + k < n := lt_trans (by omega) b.isLt
  simp only [cyclicIndex, Fin.lt_def]
  rw [Nat.mod_eq_of_lt hsum]
  omega

private lemma cyclicIndex_between_wrap {n : ℕ} (hn : 0 < n) {a b : Fin n}
    (hba : b < a) {k : ℕ} (hk0 : 0 < k) (hk : k < cyclicDist a b) :
    a < cyclicIndex hn a k ∨ cyclicIndex hn a k < b := by
  have hnle : ¬a.val ≤ b.val := by omega
  have hm : cyclicDist a b = n - a.val + b.val := by simp [cyclicDist, hnle]
  rw [hm] at hk
  by_cases hkn : a.val + k < n
  · left
    simp only [cyclicIndex, Fin.lt_def]
    rw [Nat.mod_eq_of_lt hkn]
    omega
  · right
    simp only [cyclicIndex, Fin.lt_def]
    have hlt : a.val + k < n + n := by omega
    rw [show a.val + k = n + (a.val + k - n) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : a.val + k - n < n)]
    omega

private lemma clones_finRotate_neg_one {n : ℕ} (hn : 0 < n) [NeZero n] :
    finRotate n (-1) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show (-1 : Fin (m + 1)) = Fin.last m by apply Fin.ext; simp,
    finRotate_last]

private lemma clones_fin_neg_one_val {n : ℕ} (hn : 0 < n) [NeZero n] :
    ((-1 : Fin n) : ℕ) = n - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp

private lemma clones_coe_finRotate_of_ne_neg_one {n : ℕ} (hn : 0 < n)
    [NeZero n] (i : Fin n) (hi : i ≠ -1) : (finRotate n i).val = i.val + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  apply coe_finRotate_of_ne_last
  intro hilast
  apply hi
  rw [hilast]
  apply Fin.ext
  simp

private lemma genuineEnum_intermediate_dummy (i : Fin D.genuineCount) {k : ℕ}
    (hk0 : 0 < k)
    (hk : k < cyclicDist (D.genuineEnum i).1
      (D.genuineEnum (finRotate D.genuineCount i)).1) :
    ¬D.IsGenuineVertex
      (cyclicIndex (by have := D.three_le; omega) (D.genuineEnum i).1 k) := by
  classical
  let a := (D.genuineEnum i).1
  let b := (D.genuineEnum (finRotate D.genuineCount i)).1
  let c := cyclicIndex (by have := D.three_le; omega) a k
  intro hc
  have hcmem : c ∈ D.genuineIdx := by simpa [genuineIdx] using hc
  let sc : D.genuineIdx := ⟨c, hcmem⟩
  let j := (D.genuineEnum).symm sc
  have hej : D.genuineEnum j = sc := D.genuineEnum.apply_symm_apply sc
  letI : NeZero D.genuineCount :=
    ⟨by have := D.three_le_genuineCount; omega⟩
  by_cases hilast : i = -1
  · have hrot : finRotate D.genuineCount i = 0 := by
      rw [hilast]
      exact clones_finRotate_neg_one (by have := D.three_le_genuineCount; omega)
    have hba : b < a := by
      have hzero : (0 : Fin D.genuineCount) < i := by
        rw [hilast, Fin.lt_def]
        rw [clones_fin_neg_one_val (by have := D.three_le_genuineCount; omega)]
        change 0 < D.genuineCount - 1
        have := D.three_le_genuineCount
        omega
      apply D.genuineEnum.lt_iff_lt.mpr at hzero
      simpa [a, b, hrot] using hzero
    rcases cyclicIndex_between_wrap (by have := D.three_le; omega) hba hk0 hk with hac | hcb
    · have hij : i < j := by
        apply D.genuineEnum.lt_iff_lt.mp
        rw [hej]
        simpa [a, c] using hac
      rw [hilast, Fin.lt_def] at hij
      rw [clones_fin_neg_one_val (by have := D.three_le_genuineCount; omega)] at hij
      omega
    · have hji : j < (0 : Fin D.genuineCount) := by
        apply D.genuineEnum.lt_iff_lt.mp
        rw [hej]
        simpa [b, c, hrot] using hcb
      exact (Fin.not_lt_zero j) hji
  · have hi_next : i < finRotate D.genuineCount i :=
      (lt_finRotate_iff_ne_neg_one i).2 hilast
    have hab : a < b := by
      apply D.genuineEnum.lt_iff_lt.mpr at hi_next
      simpa [a, b] using hi_next
    obtain ⟨hac, hcb⟩ :=
      cyclicIndex_between (by have := D.three_le; omega) hab hk0 hk
    have hij : i < j := by
      apply D.genuineEnum.lt_iff_lt.mp
      rw [hej]
      simpa [a, c] using hac
    have hjnext : j < finRotate D.genuineCount i := by
      apply D.genuineEnum.lt_iff_lt.mp
      rw [hej]
      simpa [b, c] using hcb
    have hval := clones_coe_finRotate_of_ne_neg_one
      (by have := D.three_le_genuineCount; omega) i hilast
    omega

private lemma cyclicIndex_sub {n : ℕ} (hn : 0 < n) {a s : Fin n} (has : a ≤ s) :
    cyclicIndex hn a (s.val - a.val) = s := by
  apply Fin.ext
  simp only [cyclicIndex]
  rw [show a.val + (s.val - a.val) = s.val by omega,
    Nat.mod_eq_of_lt s.isLt]

private lemma cyclicIndex_wrap {n : ℕ} (hn : 0 < n) {a s : Fin n} :
    cyclicIndex hn a (n - a.val + s.val) = s := by
  apply Fin.ext
  simp only [cyclicIndex]
  rw [show a.val + (n - a.val + s.val) = n + s.val by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt s.isLt]

private lemma original_index_in_coarse_block (s : Fin D.n) :
    ∃ (i : Fin D.genuineCount) (r : ℕ),
      r < cyclicDist (D.genuineEnum i).1
        (D.genuineEnum (finRotate D.genuineCount i)).1 ∧
      s = cyclicIndex (by have := D.three_le; omega) (D.genuineEnum i).1 r := by
  classical
  letI : NeZero D.genuineCount :=
    ⟨by have := D.three_le_genuineCount; omega⟩
  let T := Finset.univ.filter fun i : Fin D.genuineCount => (D.genuineEnum i).1 ≤ s
  by_cases hT : T.Nonempty
  · let i := T.max' hT
    have hiT : i ∈ T := T.max'_mem hT
    have hais : (D.genuineEnum i).1 ≤ s := (Finset.mem_filter.mp hiT).2
    by_cases hilast : i = -1
    · have hrot : finRotate D.genuineCount i = 0 := by
        rw [hilast]
        exact clones_finRotate_neg_one (by have := D.three_le_genuineCount; omega)
      have hba : (D.genuineEnum (finRotate D.genuineCount i)).1 <
          (D.genuineEnum i).1 := by
        have hzero : (0 : Fin D.genuineCount) < i := by
          rw [hilast, Fin.lt_def,
            clones_fin_neg_one_val (by have := D.three_le_genuineCount; omega)]
          change 0 < D.genuineCount - 1
          have := D.three_le_genuineCount
          omega
        apply D.genuineEnum.lt_iff_lt.mpr at hzero
        simpa [hrot] using hzero
      let r := s.val - (D.genuineEnum i).1.val
      refine ⟨i, r, ?_, ?_⟩
      · simp only [cyclicDist]
        split_ifs with hle
        · exact absurd hba (not_lt_of_ge hle)
        · dsimp only [r]
          have hs := s.isLt
          omega
      · exact (cyclicIndex_sub (by have := D.three_le; omega) hais).symm
    · have hi_next : i < finRotate D.genuineCount i :=
        (lt_finRotate_iff_ne_neg_one i).2 hilast
      have hsb : s < (D.genuineEnum (finRotate D.genuineCount i)).1 := by
        by_contra hnot
        have hb : (D.genuineEnum (finRotate D.genuineCount i)).1 ≤ s := by omega
        have hnextT : finRotate D.genuineCount i ∈ T := by
          simp [T, hb]
        have hle := T.le_max' (finRotate D.genuineCount i) hnextT
        exact (not_lt_of_ge hle) hi_next
      let r := s.val - (D.genuineEnum i).1.val
      refine ⟨i, r, ?_, ?_⟩
      · have hab : (D.genuineEnum i).1.val ≤
            (D.genuineEnum (finRotate D.genuineCount i)).1.val := by
          apply Fin.le_iff_val_le_val.mp
          exact (D.genuineEnum.le_iff_le.mpr hi_next.le)
        simp [r, cyclicDist, hab]
        omega
      · exact (cyclicIndex_sub (by have := D.three_le; omega) hais).symm
  · let i : Fin D.genuineCount := -1
    have hrot : finRotate D.genuineCount i = 0 :=
      clones_finRotate_neg_one (by have := D.three_le_genuineCount; omega)
    have hsb : s < (D.genuineEnum (finRotate D.genuineCount i)).1 := by
      by_contra hnot
      have hb : (D.genuineEnum (0 : Fin D.genuineCount)).1 ≤ s := by
        simpa [hrot] using (show (D.genuineEnum (finRotate D.genuineCount i)).1 ≤ s by omega)
      apply hT
      refine ⟨0, ?_⟩
      simp [T, hb]
    have hba : (D.genuineEnum (finRotate D.genuineCount i)).1 <
        (D.genuineEnum i).1 := by
      have hzero : (0 : Fin D.genuineCount) < i := by
        dsimp only [i]
        rw [Fin.lt_def,
          clones_fin_neg_one_val (by have := D.three_le_genuineCount; omega)]
        change 0 < D.genuineCount - 1
        have := D.three_le_genuineCount
        omega
      apply D.genuineEnum.lt_iff_lt.mpr at hzero
      simpa [hrot] using hzero
    have hsa : s < (D.genuineEnum i).1 := hsb.trans hba
    let r := D.n - (D.genuineEnum i).1.val + s.val
    refine ⟨i, r, ?_, ?_⟩
    · simp only [cyclicDist]
      split_ifs with hle
      · exact absurd hba (not_lt_of_ge hle)
      · dsimp only [r]
        omega
    · exact (cyclicIndex_wrap (by have := D.three_le; omega)).symm

private def coarseLength (D : PolygonalDisk) (i : Fin D.genuineCount) : ℕ :=
  cyclicDist (D.genuineEnum i).1
    (D.genuineEnum (finRotate D.genuineCount i)).1

private def coarseWalk (D : PolygonalDisk) (i : Fin D.genuineCount) (k : ℕ) : Pt :=
  D.vertex (cyclicIndex (by have := D.three_le; omega) (D.genuineEnum i).1 k)

private lemma coarseLength_pos (i : Fin D.genuineCount) : 0 < coarseLength D i := by
  apply cyclicDist_pos
  intro h
  have he := D.genuineEnum.injective (Subtype.ext h)
  exact clones_finRotate_ne_self (by have := D.three_le_genuineCount; omega) i he.symm

private lemma coarseWalk_zero (i : Fin D.genuineCount) :
    coarseWalk D i 0 = D.coarseVertex i := by
  simp [coarseWalk, coarseVertex, cyclicIndex_zero]

private lemma coarseWalk_end (i : Fin D.genuineCount) :
    coarseWalk D i (coarseLength D i) =
      D.coarseVertex (finRotate D.genuineCount i) := by
  simp [coarseWalk, coarseLength, coarseVertex, cyclicIndex_dist]

private lemma coarseWalk_succ (i : Fin D.genuineCount) (k : ℕ) :
    coarseWalk D i (k + 1) =
      D.vertex (finRotate D.n
        (cyclicIndex (by have := D.three_le; omega) (D.genuineEnum i).1 k)) := by
  rw [coarseWalk, cyclicIndex_succ]

private lemma coarseWalk_local (i : Fin D.genuineCount) (t : ℕ)
    (ht : t + 1 < coarseLength D i) :
    Sbtw ℝ (coarseWalk D i t) (coarseWalk D i (t + 1))
      (coarseWalk D i (t + 2)) := by
  let hn : 0 < D.n := by have := D.three_le; omega
  let a := (D.genuineEnum i).1
  let c := cyclicIndex hn a (t + 1)
  have hdummy : ¬D.IsGenuineVertex c := by
    apply genuineEnum_intermediate_dummy D i (k := t + 1) (by omega)
    simpa [coarseLength] using ht
  have hs := dummy_sbtw D c hdummy
  have hprev : (finRotate D.n).symm c = cyclicIndex hn a t := by
    apply (finRotate D.n).injective
    rw [Equiv.apply_symm_apply, ← cyclicIndex_succ]
  have hnext : finRotate D.n c = cyclicIndex hn a (t + 2) := by
    rw [cyclicIndex_succ hn a (t + 1)]
  simpa [coarseWalk, hn, a, c, hprev, hnext] using hs

private lemma original_side_subset_coarse (s : Fin D.n) :
    ∃ i : Fin D.genuineCount,
      segment ℝ (D.vertex s) (D.vertex (finRotate D.n s)) ⊆
        segment ℝ (D.coarseVertex i)
          (D.coarseVertex (finRotate D.genuineCount i)) := by
  obtain ⟨i, r, hr, hs⟩ := original_index_in_coarse_block D s
  refine ⟨i, ?_⟩
  have hsub := chain_side_subset (w := coarseWalk D i) (a := 0)
    (coarseLength_pos D i) hr (fun t ht => by
      simpa only [Nat.zero_add] using coarseWalk_local D i t ht)
  simp only [Nat.zero_add] at hsub
  rw [coarseWalk_zero, coarseWalk_end] at hsub
  have hstep := coarseWalk_succ D i r
  have hbase : coarseWalk D i r = D.vertex s := by
    simp only [coarseWalk]
    rw [hs]
  rw [hbase, hstep, ← hs] at hsub
  exact hsub

private lemma coarse_side_subset_frontier (i : Fin D.genuineCount) :
    segment ℝ (D.coarseVertex i)
        (D.coarseVertex (finRotate D.genuineCount i)) ⊆ frontier D.carrier := by
  have hsub := chain_segment_subset (w := coarseWalk D i) (a := 0)
    (coarseLength_pos D i) (fun t ht => by
      simpa only [Nat.zero_add] using coarseWalk_local D i t ht)
  simp only [Nat.zero_add] at hsub
  rw [coarseWalk_zero, coarseWalk_end] at hsub
  apply hsub.trans
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨r, hr⟩
  rcases Set.mem_iUnion.mp hr with ⟨hrlen, hxr⟩
  rw [D.frontier_eq]
  let s := cyclicIndex (by have := D.three_le; omega) (D.genuineEnum i).1 r
  apply Set.mem_iUnion.mpr
  refine ⟨s, ?_⟩
  have hstep := coarseWalk_succ D i r
  rw [hstep] at hxr
  simpa only [coarseWalk, s] using hxr

/-- Merging collinear sides does not change the boundary. -/
theorem coarse_frontier_eq :
    frontier D.carrier = ⋃ i : Fin D.genuineCount,
      segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)) := by
  apply Set.Subset.antisymm
  · rw [D.frontier_eq]
    apply Set.iUnion_subset
    intro s
    obtain ⟨i, hi⟩ := original_side_subset_coarse D s
    exact hi.trans (Set.subset_iUnion (fun j =>
      segment ℝ (D.coarseVertex j)
        (D.coarseVertex (finRotate D.genuineCount j))) i)
  · apply Set.iUnion_subset
    exact coarse_side_subset_frontier D

/-- Step 1.1 of the blueprint proof of `coarse_simple_step1`: A fine segment that intersects the interior of a coarse segment must be contained in it. -/
private lemma coarse_simple_step1_step1 (i : Fin D.genuineCount) (k : Fin D.n)
    (h_int : ∃ x, x ∈ segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ∧ 
      x ∈ segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)) ∧
      x ≠ D.coarseVertex i ∧ x ≠ D.coarseVertex (finRotate D.genuineCount i)) :
    segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ⊆ 
      segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)) := by
  obtain ⟨x, hxk, hxi, hxi0, hxi1⟩ := h_int
  have hchain := chain_segment_subset (w := coarseWalk D i) (a := 0)
    (coarseLength_pos D i) (fun t ht => by
      simpa only [Nat.zero_add] using coarseWalk_local D i t ht)
  simp only [Nat.zero_add] at hchain
  rw [coarseWalk_zero, coarseWalk_end] at hchain
  rcases Set.mem_iUnion.mp (hchain hxi) with ⟨r, hr⟩
  rcases Set.mem_iUnion.mp hr with ⟨hrm, hxr⟩
  change r < coarseLength D i at hrm
  let hn : 0 < D.n := by have := D.three_le; omega
  let s := cyclicIndex hn (D.genuineEnum i).1 r
  have hstep := coarseWalk_succ D i r
  have hxr' : x ∈ segment ℝ (D.vertex s) (D.vertex (finRotate D.n s)) := by
    rw [hstep] at hxr
    simpa only [coarseWalk, s] using hxr
  by_cases hks : k = s
  · subst k
    have hsub := chain_side_subset (w := coarseWalk D i) (a := 0) (r := r)
      (coarseLength_pos D i) hrm (fun t ht => by
        simpa only [Nat.zero_add] using coarseWalk_local D i t ht)
    simp only [Nat.zero_add] at hsub
    rw [coarseWalk_zero, coarseWalk_end] at hsub
    have hbase : coarseWalk D i r = D.vertex s := by
      simp only [coarseWalk, s]
    rw [hbase, hstep] at hsub
    exact hsub
  have hmem := D.simple k s hks ⟨hxk, hxr'⟩
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hks_cases : k = (finRotate D.n).symm s ∨ k = finRotate D.n s := by
    rcases hmem.1 with hk0 | hk1
    · rcases hmem.2 with hs0 | hs1
      · exfalso
        apply hks
        exact D.vertex_injective (hk0.symm.trans hs0)
      · exact Or.inr (D.vertex_injective (hk0.symm.trans hs1))
    · rcases hmem.2 with hs0 | hs1
      · left
        apply (finRotate D.n).injective
        simpa using D.vertex_injective (hk1.symm.trans hs0)
      · exfalso
        apply hks
        exact (finRotate D.n).injective (D.vertex_injective (hk1.symm.trans hs1))
  rcases hks_cases with hkprev | hknext
  · have hx0 : x = D.vertex s := by
      rcases hmem.1 with hk0 | hk1
      · rcases hmem.2 with hs0 | hs1
        · exact (hks (D.vertex_injective (hk0.symm.trans hs0))).elim
        · exfalso
          apply clones_finRotate_sq_ne D.three_le s
          have heq := D.vertex_injective (hk0.symm.trans hs1)
          have heq' := congrArg (finRotate D.n) (hkprev.symm.trans heq)
          simpa using heq'.symm
      · rcases hmem.2 with hs0 | hs1
        · exact hs0
        · exfalso
          apply hks
          exact (finRotate D.n).injective (D.vertex_injective (hk1.symm.trans hs1))
    have hr0 : r ≠ 0 := by
      intro hr0
      apply hxi0
      calc
        x = D.vertex s := hx0
        _ = coarseWalk D i r := by simp only [coarseWalk, s]
        _ = coarseWalk D i 0 := by rw [hr0]
        _ = D.coarseVertex i := coarseWalk_zero D i
    have hsub := chain_side_subset (w := coarseWalk D i) (a := 0) (r := r - 1)
      (coarseLength_pos D i) (by omega) (fun t ht => by
        simpa only [Nat.zero_add] using coarseWalk_local D i t ht)
    simp only [Nat.zero_add] at hsub
    rw [coarseWalk_zero, coarseWalk_end] at hsub
    have hcyc : cyclicIndex hn (D.genuineEnum i).1 (r - 1) =
        (finRotate D.n).symm s := by
      have hsucc := cyclicIndex_succ hn (D.genuineEnum i).1 (r - 1)
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hr0)] at hsucc
      apply (finRotate D.n).injective
      simpa [s] using hsucc.symm
    have hleft : coarseWalk D i (r - 1) = D.vertex k := by
      simp [coarseWalk, s, hcyc, hkprev]
    have hright : coarseWalk D i (r - 1 + 1) =
        D.vertex (finRotate D.n k) := by
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hr0)]
      simp [coarseWalk, s, hkprev]
    rw [hleft, hright] at hsub
    exact hsub
  · have hx1 : x = D.vertex (finRotate D.n s) := by
      rcases hmem.1 with hk0 | hk1
      · rcases hmem.2 with hs0 | hs1
        · exfalso
          apply hks
          exact D.vertex_injective (hk0.symm.trans hs0)
        · exact hs1
      · rcases hmem.2 with hs0 | hs1
        · exfalso
          apply clones_finRotate_sq_ne D.three_le s
          have heq := D.vertex_injective (hk1.symm.trans hs0)
          simpa [hknext] using heq
        · exfalso
          apply hks
          exact (finRotate D.n).injective (D.vertex_injective (hk1.symm.trans hs1))
    have hrm1 : r + 1 ≠ coarseLength D i := by
      intro heq
      apply hxi1
      calc
        x = D.vertex (finRotate D.n s) := hx1
        _ = coarseWalk D i (r + 1) := by rw [hstep]
        _ = coarseWalk D i (coarseLength D i) := by rw [heq]
        _ = D.coarseVertex (finRotate D.genuineCount i) := coarseWalk_end D i
    have hsub := chain_side_subset (w := coarseWalk D i) (a := 0) (r := r + 1)
      (coarseLength_pos D i) (by omega) (fun t ht => by
        simpa only [Nat.zero_add] using coarseWalk_local D i t ht)
    simp only [Nat.zero_add] at hsub
    rw [coarseWalk_zero, coarseWalk_end] at hsub
    have hleft : coarseWalk D i (r + 1) = D.vertex k := by
      simpa [s, hknext] using hstep
    have hright : coarseWalk D i (r + 1 + 1) =
        D.vertex (finRotate D.n k) := by
      have hstep2 := coarseWalk_succ D i (r + 1)
      have hsucc := cyclicIndex_succ hn (D.genuineEnum i).1 r
      rw [show r + 1 + 1 = (r + 1) + 1 by omega] at hstep2
      rw [hsucc] at hstep2
      simpa [s, hknext] using hstep2
    rw [hleft, hright] at hsub
    exact hsub

/-- Step 1.2 of the blueprint proof of `coarse_simple_step1`: The endpoints of a coarse segment belong to some fine segment contained in that coarse segment. -/
private lemma coarse_simple_step1_step2 (i : Fin D.genuineCount) (x : Pt)
    (h_end : x = D.coarseVertex i ∨ x = D.coarseVertex (finRotate D.genuineCount i)) :
    ∃ k : Fin D.n, x ∈ segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ∧ 
      segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ⊆
        segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)) := by
  rcases h_end with rfl | rfl
  · let k : Fin D.n := (D.genuineEnum i).1
    refine ⟨k, ?_, ?_⟩
    · exact left_mem_segment ℝ _ _
    · have hsub := chain_side_subset (w := coarseWalk D i) (a := 0) (r := 0)
        (m := coarseLength D i) (coarseLength_pos D i)
        (by simpa using coarseLength_pos D i)
        (fun t ht => by
          simpa only [Nat.zero_add] using coarseWalk_local D i t ht)
      have hsub' : segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ⊆
          segment ℝ (D.coarseVertex i)
            (D.coarseVertex (finRotate D.genuineCount i)) := by
        simpa [k, coarseWalk_zero, coarseWalk_succ, cyclicIndex_zero,
          coarseWalk_end] using hsub
      exact hsub'
  · let m : ℕ := coarseLength D i
    let k : Fin D.n := cyclicIndex (by have := D.three_le; omega)
      (D.genuineEnum i).1 (m - 1)
    have hm : 0 < m := coarseLength_pos D i
    have hlast := coarseWalk_succ D i (m - 1)
    have hlast' : coarseWalk D i m = D.vertex (finRotate D.n k) := by
      simpa [m, k, Nat.sub_add_cancel hm] using hlast
    have hlast'' : D.vertex (finRotate D.n k) =
        D.coarseVertex (finRotate D.genuineCount i) := by
      rw [← hlast', coarseWalk_end]
    have hsub := chain_side_subset (w := coarseWalk D i) (a := 0) (r := m - 1)
      (m := m) hm (by omega)
      (fun t ht => by
        simpa only [Nat.zero_add] using coarseWalk_local D i t ht)
    refine ⟨k, ?_, ?_⟩
    · rw [← hlast', ← coarseWalk_end]
      exact right_mem_segment ℝ _ _
    · have hfirst : coarseWalk D i (m - 1) = D.vertex k := by
        rfl
      have hsub' : segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ⊆
          segment ℝ (D.coarseVertex i)
            (D.coarseVertex (finRotate D.genuineCount i)) := by
        simpa [hfirst, Nat.sub_add_cancel hm, hlast', coarseWalk_zero,
          coarseWalk_end, hlast''] using hsub
      exact hsub'

/-- Step 1 of the blueprint proof of `coarse_simple`: Every point on a coarse segment
belongs to a fine segment that is contained within the same coarse segment. -/
private lemma coarse_simple_step1 (i : Fin D.genuineCount) (x : Pt)
    (hx : x ∈ segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i))) :
    ∃ k : Fin D.n, x ∈ segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ∧ 
      segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ⊆
        segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)) := by
  by_cases h_end : x = D.coarseVertex i ∨ x = D.coarseVertex (finRotate D.genuineCount i)
  · exact coarse_simple_step1_step2 D i x h_end
  · push_neg at h_end
    have hx_front : x ∈ frontier D.carrier := by
      rw [D.coarse_frontier_eq]
      exact Set.subset_iUnion _ i hx
    rw [D.frontier_eq, Set.mem_iUnion] at hx_front
    rcases hx_front with ⟨k, hk⟩
    have h_sub := coarse_simple_step1_step1 D i k ⟨x, hk, hx, h_end⟩
    exact ⟨k, hk, h_sub⟩

/-- Step 1 of the blueprint proof of `coarse_simple_step2_step1`: A fine segment contained in
a coarse segment `i` is one of the fine sides of the chain walk from `D.coarseVertex i` to
`D.coarseVertex (finRotate D.genuineCount i)`, i.e. its starting index is `cyclicIndex` of the
starting genuine index by some offset `r` within the coarse block's length. -/
private lemma coarse_simple_step2_step1_step1_mem_block (i : Fin D.genuineCount) (k : Fin D.n)
    (h : segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ⊆
      segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i))) :
    ∃ r, r < coarseLength D i ∧
      k = cyclicIndex (by have := D.three_le; omega) (D.genuineEnum i).1 r := by
  classical
  let hn : 0 < D.n := by have := D.three_le; omega
  let hm : 0 < coarseLength D i := coarseLength_pos D i
  have hm_lt : coarseLength D i < D.n := by
    simp only [coarseLength, cyclicDist]
    split_ifs <;> omega
  have hcyc_inj : ∀ {u v : ℕ}, u < D.n → v < D.n →
      cyclicIndex hn (D.genuineEnum i).1 u =
        cyclicIndex hn (D.genuineEnum i).1 v → u = v := by
    intro u v hu hv huv
    have huv' := congrArg Fin.val huv
    change ((D.genuineEnum i).1.val + u) % D.n =
      ((D.genuineEnum i).1.val + v) % D.n at huv'
    by_cases hu' : (D.genuineEnum i).1.val + u < D.n
    · rw [Nat.mod_eq_of_lt hu'] at huv'
      by_cases hv' : (D.genuineEnum i).1.val + v < D.n
      · rw [Nat.mod_eq_of_lt hv'] at huv'
        omega
      · have hrepr : (D.genuineEnum i).1.val + v = D.n +
            ((D.genuineEnum i).1.val + v - D.n) := by omega
        rw [hrepr, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by have := (D.genuineEnum i).1.isLt; omega)] at huv'
        omega
    · by_cases hv' : (D.genuineEnum i).1.val + v < D.n
      · rw [Nat.mod_eq_of_lt hv'] at huv'
        have hrepr : (D.genuineEnum i).1.val + u = D.n +
            ((D.genuineEnum i).1.val + u - D.n) := by omega
        rw [hrepr, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by have := (D.genuineEnum i).1.isLt; omega)] at huv'
        omega
      · have hrepru : (D.genuineEnum i).1.val + u = D.n +
            ((D.genuineEnum i).1.val + u - D.n) := by omega
        have hreprv : (D.genuineEnum i).1.val + v = D.n +
            ((D.genuineEnum i).1.val + v - D.n) := by omega
        rw [hrepru, hreprv, Nat.add_mod_left, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by have := (D.genuineEnum i).1.isLt; omega),
          Nat.mod_eq_of_lt (by have := (D.genuineEnum i).1.isLt; omega)] at huv'
        omega
  have hvertex : ∀ (q s : Fin D.n),
      D.vertex q ∉ openSegment ℝ (D.vertex s) (D.vertex (finRotate D.n s)) := by
    intro q s hq
    by_cases hqs : q = s
    · subst q
      have hne : D.vertex s ≠ D.vertex (finRotate D.n s) := by
        intro heq
        exact clones_finRotate_ne_self (by have := D.three_le; omega) s
          (D.vertex_injective heq).symm
      exact hne ((left_mem_openSegment_iff).mp hq)
    · have hs := D.simple s q (Ne.symm hqs)
        ⟨openSegment_subset_segment ℝ _ _ hq,
          left_mem_segment ℝ (D.vertex q) (D.vertex (finRotate D.n q))⟩
      rcases hs.1 with hs0 | hs1
      · have heq := left_mem_openSegment_iff.mp (hs0 ▸ hq)
        exact clones_finRotate_ne_self (by have := D.three_le; omega) s
          (D.vertex_injective heq).symm
      · rw [Set.mem_singleton_iff] at hs1
        have heq := right_mem_openSegment_iff.mp (hs1 ▸ hq)
        exact clones_finRotate_ne_self (by have := D.three_le; omega) s
          (D.vertex_injective heq).symm
  have endpoint : ∀ (q : Fin D.n),
      D.vertex q ∈ segment ℝ (D.coarseVertex i)
        (D.coarseVertex (finRotate D.genuineCount i)) →
      ∃ r, r ≤ coarseLength D i ∧ D.vertex q = coarseWalk D i r := by
    intro q hq
    have hchain := chain_segment_subset (w := coarseWalk D i) (a := 0)
      hm (fun t ht => by
        simpa only [Nat.zero_add] using coarseWalk_local D i t ht)
    simp only [Nat.zero_add] at hchain
    rw [coarseWalk_zero, coarseWalk_end] at hchain
    rcases Set.mem_iUnion.mp (hchain hq) with ⟨r, hr⟩
    rcases Set.mem_iUnion.mp hr with ⟨hrm, hqr⟩
    change r < coarseLength D i at hrm
    let s : Fin D.n := cyclicIndex hn (D.genuineEnum i).1 r
    have hstep := coarseWalk_succ D i r
    have hside : D.vertex q ∈ segment ℝ (D.vertex s)
        (D.vertex (finRotate D.n s)) := by
      rw [hstep] at hqr
      simpa only [coarseWalk, s] using hqr
    by_cases hleft : D.vertex q = D.vertex s
    · refine ⟨r, le_of_lt hrm, ?_⟩
      simpa [coarseWalk, s] using hleft
    by_cases hright : D.vertex q = D.vertex (finRotate D.n s)
    · refine ⟨r + 1, by omega, ?_⟩
      exact hright.trans hstep.symm
    · have hopen : D.vertex q ∈ openSegment ℝ (D.vertex s)
          (D.vertex (finRotate D.n s)) :=
        mem_openSegment_of_ne_left_right (Ne.symm hleft) (Ne.symm hright) hside
      exact (hvertex q s hopen).elim
  have hq0 := endpoint k (h (left_mem_segment ℝ _ _))
  have hq1 := endpoint (finRotate D.n k) (h (right_mem_segment ℝ _ _))
  rcases hq0 with ⟨r, hr, hkr⟩
  rcases hq1 with ⟨r', hr', hknr⟩
  have hrr : r ≠ r' := by
    intro heq
    have hfix : k = finRotate D.n k := D.vertex_injective (by
      rw [hkr, hknr, heq])
    exact clones_finRotate_ne_self (by have := D.three_le; omega) k hfix.symm
  by_cases hlt : r < r'
  · by_cases hgap : r + 1 < r'
    · have hmidw := chain_wbtw (w := coarseWalk D i) (a := r)
        (m := r' - r) (r := 1) (by omega) (by omega) (fun t ht => by
          have ht' : r + t + 1 < coarseLength D i := by omega
          simpa only [Nat.add_assoc] using coarseWalk_local D i (r + t) ht')
      have hmid_ne_left : coarseWalk D i (r + 1) ≠ coarseWalk D i r := by
        intro heq
        have hstep := coarseWalk_succ D i r
        have hfix : finRotate D.n (cyclicIndex hn (D.genuineEnum i).1 r) =
            cyclicIndex hn (D.genuineEnum i).1 r := by
          apply D.vertex_injective
          calc
            D.vertex (finRotate D.n (cyclicIndex hn (D.genuineEnum i).1 r)) =
                coarseWalk D i (r + 1) := hstep.symm
            _ = coarseWalk D i r := heq
            _ = D.vertex (cyclicIndex hn (D.genuineEnum i).1 r) := by rfl
        exact clones_finRotate_ne_self (by have := D.three_le; omega) _ hfix
      have hmid_ne_right : coarseWalk D i (r + 1) ≠ coarseWalk D i r' :=
        fun heq => by
          have huv := hcyc_inj (u := r + 1) (v := r') (by omega) (by omega) (by
            apply D.vertex_injective
            simpa [coarseWalk] using heq)
          omega
      have hmid_seg : coarseWalk D i (r + 1) ∈
          segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) := by
        rw [hkr, hknr]
        have hsum : r + (r' - r) = r' := by omega
        simpa [hsum] using hmidw.mem_segment
      have hmid_open : coarseWalk D i (r + 1) ∈
          openSegment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) :=
        mem_openSegment_of_ne_left_right
          (by simpa [hkr] using hmid_ne_left.symm)
          (by simpa [hknr] using hmid_ne_right.symm) hmid_seg
      exact (hvertex (cyclicIndex hn (D.genuineEnum i).1 (r + 1))
        k (by
          simpa [coarseWalk] using hmid_open)).elim
    · have heq : r' = r + 1 := by omega
      refine ⟨r, ?_, ?_⟩
      · omega
      · apply D.vertex_injective
        simpa [coarseWalk] using hkr
  · have hgt : r' < r := by omega
    by_cases hgap : r' + 1 < r
    · have hmidw := chain_wbtw (w := coarseWalk D i) (a := r')
        (m := r - r') (r := 1) (by omega) (by omega) (fun t ht => by
          have ht' : r' + t + 1 < coarseLength D i := by omega
          simpa only [Nat.add_assoc] using coarseWalk_local D i (r' + t) ht')
      have hstep := coarseWalk_succ D i r'
      have hmid_ne_right : coarseWalk D i (r' + 1) ≠ coarseWalk D i r' := by
        intro heq
        have hfix : finRotate D.n (cyclicIndex hn (D.genuineEnum i).1 r') =
            cyclicIndex hn (D.genuineEnum i).1 r' := by
          apply D.vertex_injective
          calc
            D.vertex (finRotate D.n (cyclicIndex hn (D.genuineEnum i).1 r')) =
                coarseWalk D i (r' + 1) := hstep.symm
            _ = coarseWalk D i r' := heq
            _ = D.vertex (cyclicIndex hn (D.genuineEnum i).1 r') := by rfl
        exact clones_finRotate_ne_self (by have := D.three_le; omega) _ hfix
      have hmid_ne_left : coarseWalk D i (r' + 1) ≠ coarseWalk D i r :=
        fun heq => by
          have huv := hcyc_inj (u := r' + 1) (v := r) (by omega) (by omega) (by
            apply D.vertex_injective
            simpa [coarseWalk] using heq)
          omega
      have hmid_seg : coarseWalk D i (r' + 1) ∈
          segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) := by
        rw [hkr, hknr]
        have hsum : r' + (r - r') = r := by omega
        simpa [hsum] using hmidw.symm.mem_segment
      have hmid_open : coarseWalk D i (r' + 1) ∈
          openSegment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) := by
        exact mem_openSegment_of_ne_left_right
          (by simpa [hkr] using hmid_ne_left.symm)
          (by simpa [hknr] using hmid_ne_right.symm) hmid_seg
      exact (hvertex (cyclicIndex hn (D.genuineEnum i).1 (r' + 1))
        k (by
          simpa [coarseWalk] using hmid_open)).elim
    · have heq : r = r' + 1 := by omega
      have hk_eq : D.vertex k = coarseWalk D i (r' + 1) := by
        rw [heq] at hkr
        exact hkr
      have hnext_eq : D.vertex (finRotate D.n k) = coarseWalk D i r' := hknr
      have hsucc := coarseWalk_succ D i r'
      have hk_s : k = finRotate D.n (cyclicIndex hn (D.genuineEnum i).1 r') := by
        apply D.vertex_injective
        rw [hk_eq, hsucc]
      have hnext_s : finRotate D.n k = cyclicIndex hn (D.genuineEnum i).1 r' := by
        apply D.vertex_injective
        simpa [coarseWalk] using hnext_eq
      have hsq := congrArg (finRotate D.n) hk_s
      rw [hnext_s] at hsq
      exact (clones_finRotate_sq_ne D.three_le _ hsq.symm).elim

private lemma coarse_simple_step2_step1_step2_block_unique_aux
    (i i' : Fin D.genuineCount) (r r' : ℕ) (k : Fin D.n)
    (hii : i < i')
    (hr : r < coarseLength D i) (hr' : r' < coarseLength D i')
    (hk : k = cyclicIndex (by have := D.three_le; omega) (D.genuineEnum i).1 r)
    (hk' : k = cyclicIndex (by have := D.three_le; omega) (D.genuineEnum i').1 r') :
    False := by
  letI : NeZero D.genuineCount :=
    ⟨by have := D.three_le_genuineCount; omega⟩
  let hn : 0 < D.n := by have := D.three_le; omega
  have hilast : i ≠ -1 := by
    intro h
    rw [h] at hii
    have hi' := i'.isLt
    rw [Fin.lt_def] at hii
    rw [clones_fin_neg_one_val (by have := D.three_le_genuineCount; omega)] at hii
    omega
  have hi_next : i < finRotate D.genuineCount i :=
    (lt_finRotate_iff_ne_neg_one i).2 hilast
  have hnext_le : finRotate D.genuineCount i ≤ i' := by
    apply Fin.le_iff_val_le_val.mpr
    have hrot := clones_coe_finRotate_of_ne_neg_one
      (by have := D.three_le_genuineCount; omega) i hilast
    rw [hrot]
    omega
  have hab : (D.genuineEnum i).1 <
      (D.genuineEnum (finRotate D.genuineCount i)).1 :=
    D.genuineEnum.lt_iff_lt.mpr hi_next
  have hr_dist : r < cyclicDist (D.genuineEnum i).1
      (D.genuineEnum (finRotate D.genuineCount i)).1 := by
    simpa [coarseLength] using hr
  have hk_lower : (D.genuineEnum i).1 ≤ k := by
    rw [hk]
    by_cases hr0 : r = 0
    · subst r
      rw [cyclicIndex_zero hn]
    · have hbetween := cyclicIndex_between hn hab (Nat.pos_of_ne_zero hr0) hr_dist
      exact hbetween.1.le
  have hk_upper : k < (D.genuineEnum (finRotate D.genuineCount i)).1 := by
    rw [hk]
    by_cases hr0 : r = 0
    · subst r
      rw [cyclicIndex_zero hn]
      exact hab
    · exact (cyclicIndex_between hn hab (Nat.pos_of_ne_zero hr0) hr_dist).2
  have hb_le_a' : (D.genuineEnum (finRotate D.genuineCount i)).1 ≤
      (D.genuineEnum i').1 := D.genuineEnum.monotone hnext_le
  have hk_upper' : k < (D.genuineEnum i').1 := hk_upper.trans_le hb_le_a'
  have hk'_eq : k = cyclicIndex hn (D.genuineEnum i').1 r' := by
    simpa [hn] using hk'
  by_cases hi_last : i' = -1
  · have hrot_last : finRotate D.genuineCount i' = 0 := by
      rw [hi_last]
      exact clones_finRotate_neg_one
        (by have := D.three_le_genuineCount; omega)
    have hca : (D.genuineEnum (finRotate D.genuineCount i')).1 <
        (D.genuineEnum i').1 := by
      apply D.genuineEnum.lt_iff_lt.mpr
      rw [hrot_last, hi_last]
      rw [Fin.lt_def]
      rw [clones_fin_neg_one_val (by have := D.three_le_genuineCount; omega)]
      change 0 < D.genuineCount - 1
      have := D.three_le_genuineCount
      omega
    have hca' : (D.genuineEnum (finRotate D.genuineCount i')).1 ≤
        (D.genuineEnum i).1 := by
      apply D.genuineEnum.monotone
      rw [hrot_last]
      exact Fin.zero_le _
    have hr'_dist : r' < cyclicDist (D.genuineEnum i').1
        (D.genuineEnum (finRotate D.genuineCount i')).1 := by
      simpa [coarseLength] using hr'
    by_cases hr'0 : r' = 0
    · subst r'
      have hkk : k = (D.genuineEnum i').1 := by
        calc
          k = cyclicIndex hn (D.genuineEnum i').1 0 := hk'_eq
          _ = (D.genuineEnum i').1 := cyclicIndex_zero hn _
      exact lt_irrefl _ (hkk ▸ hk_upper')
    · have hwrap := cyclicIndex_between_wrap hn hca (Nat.pos_of_ne_zero hr'0) hr'_dist
      rw [hrot_last] at hwrap
      rcases hwrap with hbig | hsmall
      · rw [← hk'_eq] at hbig
        exact lt_irrefl _ (hbig.trans hk_upper')
      · rw [← hk'_eq] at hsmall
        have hca0 : (D.genuineEnum (0 : Fin D.genuineCount)).1 ≤
            (D.genuineEnum i).1 := by
          rw [hrot_last] at hca'
          exact hca'
        exact lt_irrefl _ (hsmall.trans_le (hca0.trans hk_lower))
  · have hi'_next : i' < finRotate D.genuineCount i' :=
      (lt_finRotate_iff_ne_neg_one i').2 hi_last
    have hbc : (D.genuineEnum i').1 <
        (D.genuineEnum (finRotate D.genuineCount i')).1 := by
      apply D.genuineEnum.lt_iff_lt.mpr
      exact hi'_next
    have hr'_dist : r' < cyclicDist (D.genuineEnum i').1
        (D.genuineEnum (finRotate D.genuineCount i')).1 := by
      simpa [coarseLength] using hr'
    by_cases hr'0 : r' = 0
    · subst r'
      have hkk : k = (D.genuineEnum i').1 := by
        calc
          k = cyclicIndex hn (D.genuineEnum i').1 0 := hk'_eq
          _ = (D.genuineEnum i').1 := cyclicIndex_zero hn _
      exact lt_irrefl _ (hkk ▸ hk_upper')
    · have hbetween := cyclicIndex_between hn hbc (Nat.pos_of_ne_zero hr'0) hr'_dist
      have hkle := hbetween.1
      rw [← hk'_eq] at hkle
      exact (not_lt_of_ge hk_upper'.le) hkle

/-- Step 2 of the blueprint proof of `coarse_simple_step2_step1`: The coarse block (given by a
genuine index `i` and an offset `r` below the block's length) containing a fine index `k` in its
chain walk is unique. -/
private lemma coarse_simple_step2_step1_step2_block_unique
    (i i' : Fin D.genuineCount) (r r' : ℕ) (k : Fin D.n)
    (hr : r < coarseLength D i) (hr' : r' < coarseLength D i')
    (hk : k = cyclicIndex (by have := D.three_le; omega) (D.genuineEnum i).1 r)
    (hk' : k = cyclicIndex (by have := D.three_le; omega) (D.genuineEnum i').1 r') :
    i = i' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hii | hii
  · exact (coarse_simple_step2_step1_step2_block_unique_aux D i i' r r' k hii
      hr hr' hk hk').elim
  · exact (coarse_simple_step2_step1_step2_block_unique_aux D i' i r' r k hii
      hr' hr hk' hk).elim

/-- Step 1 of the blueprint proof of `coarse_simple_step2`: The fine segments `k1` and `k2` must be distinct. -/
private lemma coarse_simple_step2_step1 (i j : Fin D.genuineCount) (hij : i ≠ j)
    (k1 k2 : Fin D.n)
    (h1 : segment ℝ (D.vertex k1) (D.vertex (finRotate D.n k1)) ⊆
      segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)))
    (h2 : segment ℝ (D.vertex k2) (D.vertex (finRotate D.n k2)) ⊆
      segment ℝ (D.coarseVertex j) (D.coarseVertex (finRotate D.genuineCount j))) :
    k1 ≠ k2 := by
  intro heq
  subst heq
  obtain ⟨r, hr, hk⟩ := coarse_simple_step2_step1_step1_mem_block D i k1 h1
  obtain ⟨r', hr', hk'⟩ := coarse_simple_step2_step1_step1_mem_block D j k1 h2
  exact hij (coarse_simple_step2_step1_step2_block_unique D i j r r' k1 hr hr' hk hk')

/-- Step 1 of the blueprint proof of `coarse_simple_step2_step2`: An internal
fine endpoint has both incident fine sides in the same coarse side. -/
private lemma coarse_simple_step2_step2_internal_endpoint_propagates
    (i : Fin D.genuineCount) (k1 k2 : Fin D.n) (x : Pt)
    (h1 : segment ℝ (D.vertex k1) (D.vertex (finRotate D.n k1)) ⊆
      segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)))
    (hx1 : x ∈ ({D.vertex k1, D.vertex (finRotate D.n k1)} : Set Pt))
    (hx2 : x ∈ ({D.vertex k2, D.vertex (finRotate D.n k2)} : Set Pt))
    (hk : k1 ≠ k2)
    (hx : x ∉ ({D.coarseVertex i, D.coarseVertex (finRotate D.genuineCount i)} :
      Set Pt)) :
    segment ℝ (D.vertex k2) (D.vertex (finRotate D.n k2)) ⊆
      segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)) := by
  have _ := hk
  have hx2seg : x ∈ segment ℝ (D.vertex k2) (D.vertex (finRotate D.n k2)) := by
    rcases hx2 with hx2 | hx2
    · rw [← hx2]
      exact left_mem_segment ℝ _ _
    · rw [Set.mem_singleton_iff] at hx2
      rw [← hx2]
      exact right_mem_segment ℝ _ _
  have hx1seg : x ∈ segment ℝ (D.vertex k1) (D.vertex (finRotate D.n k1)) := by
    rcases hx1 with hx1 | hx1
    · rw [← hx1]
      exact left_mem_segment ℝ _ _
    · rw [Set.mem_singleton_iff] at hx1
      rw [← hx1]
      exact right_mem_segment ℝ _ _
  apply coarse_simple_step1_step1 D i k2
  refine ⟨x, hx2seg, h1 hx1seg, ?_, ?_⟩
  · intro hxi
    exact hx (Set.mem_insert_iff.mpr (Or.inl hxi))
  · intro hxi
    exact hx (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hxi)))

/-- Step 2 of the blueprint proof of `coarse_simple_step2_step2`: A nondegenerate
fine side cannot be contained in two distinct coarse sides. -/
private lemma coarse_simple_step2_step2_distinct_coarse_sides_no_common_fine_side
    (i j : Fin D.genuineCount) (hij : i ≠ j) (k : Fin D.n)
    (h1 : segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ⊆
      segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)))
    (h2 : segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ⊆
      segment ℝ (D.coarseVertex j) (D.coarseVertex (finRotate D.genuineCount j))) :
    False := by
  obtain ⟨r, hr, hk⟩ := coarse_simple_step2_step1_step1_mem_block D i k h1
  obtain ⟨r', hr', hk'⟩ := coarse_simple_step2_step1_step1_mem_block D j k h2
  exact hij (coarse_simple_step2_step1_step2_block_unique D i j r r' k hr hr' hk hk')

/-- Step 2 of the blueprint proof of `coarse_simple_step2`: If `x` is a fine endpoint in both fine segments, it is a coarse endpoint. -/
private lemma coarse_simple_step2_step2 (i j : Fin D.genuineCount) (hij : i ≠ j)
    (k1 k2 : Fin D.n) (x : Pt)
    (h1 : segment ℝ (D.vertex k1) (D.vertex (finRotate D.n k1)) ⊆
      segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)))
    (h2 : segment ℝ (D.vertex k2) (D.vertex (finRotate D.n k2)) ⊆
      segment ℝ (D.coarseVertex j) (D.coarseVertex (finRotate D.genuineCount j)))
    (hx_fine : x ∈ ({D.vertex k1, D.vertex (finRotate D.n k1)} : Set Pt) ∩
        {D.vertex k2, D.vertex (finRotate D.n k2)}) :
    x ∈ ({D.coarseVertex i, D.coarseVertex (finRotate D.genuineCount i)} : Set Pt) ∩
        {D.coarseVertex j, D.coarseVertex (finRotate D.genuineCount j)} := by
  have hk : k1 ≠ k2 := coarse_simple_step2_step1 D i j hij k1 k2 h1 h2
  have hx1 : x ∈ ({D.vertex k1, D.vertex (finRotate D.n k1)} : Set Pt) :=
    hx_fine.1
  have hx2 : x ∈ ({D.vertex k2, D.vertex (finRotate D.n k2)} : Set Pt) :=
    hx_fine.2
  have hxi : x ∈ ({D.coarseVertex i, D.coarseVertex (finRotate D.genuineCount i)} :
      Set Pt) := by
    by_contra hxi
    have h2i := coarse_simple_step2_step2_internal_endpoint_propagates D i k1 k2 x
      h1 hx1 hx2 hk hxi
    exact coarse_simple_step2_step2_distinct_coarse_sides_no_common_fine_side D i j hij k2
      h2i h2
  have hxj : x ∈ ({D.coarseVertex j, D.coarseVertex (finRotate D.genuineCount j)} :
      Set Pt) := by
    by_contra hxj
    have h1j := coarse_simple_step2_step2_internal_endpoint_propagates D j k2 k1 x
      h2 hx2 hx1 hk.symm hxj
    exact coarse_simple_step2_step2_distinct_coarse_sides_no_common_fine_side D j i hij.symm k1
      h1j h1
  exact ⟨hxi, hxj⟩

/-- Step 2 of the blueprint proof of `coarse_simple`: If two fine segments are contained
in distinct coarse segments, their intersection (which is a subset of the fine segment
endpoints due to fine simplicity) is an endpoint of both coarse segments. -/
private lemma coarse_simple_step2 (i j : Fin D.genuineCount) (hij : i ≠ j)
    (k1 k2 : Fin D.n) (x : Pt)
    (h1 : segment ℝ (D.vertex k1) (D.vertex (finRotate D.n k1)) ⊆
      segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)))
    (h2 : segment ℝ (D.vertex k2) (D.vertex (finRotate D.n k2)) ⊆
      segment ℝ (D.coarseVertex j) (D.coarseVertex (finRotate D.genuineCount j)))
    (hx1 : x ∈ segment ℝ (D.vertex k1) (D.vertex (finRotate D.n k1)))
    (hx2 : x ∈ segment ℝ (D.vertex k2) (D.vertex (finRotate D.n k2))) :
    x ∈ ({D.coarseVertex i, D.coarseVertex (finRotate D.genuineCount i)} : Set Pt) ∩
        {D.coarseVertex j, D.coarseVertex (finRotate D.genuineCount j)} := by
  have hneq := coarse_simple_step2_step1 D i j hij k1 k2 h1 h2
  have hx_fine : x ∈ ({D.vertex k1, D.vertex (finRotate D.n k1)} : Set Pt) ∩
        {D.vertex k2, D.vertex (finRotate D.n k2)} := by
    exact D.simple k1 k2 hneq ⟨hx1, hx2⟩
  exact coarse_simple_step2_step2 D i j hij k1 k2 x h1 h2 hx_fine

/-- The merged sides still meet only at shared endpoints. -/
theorem coarse_simple : ∀ i j : Fin D.genuineCount, i ≠ j →
    segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)) ∩
        segment ℝ (D.coarseVertex j) (D.coarseVertex (finRotate D.genuineCount j)) ⊆
      ({D.coarseVertex i, D.coarseVertex (finRotate D.genuineCount i)} : Set Pt) ∩
        {D.coarseVertex j, D.coarseVertex (finRotate D.genuineCount j)} := by
  intro i j hij x hx
  have ⟨k1, hk1_x, hk1_sub⟩ := coarse_simple_step1 D i x hx.1
  have ⟨k2, hk2_x, hk2_sub⟩ := coarse_simple_step1 D j x hx.2
  exact coarse_simple_step2 D i j hij k1 k2 x hk1_sub hk2_sub hk1_x hk2_x

/-- The coarsened disk: same carrier, only genuine listed vertices. -/
def coarsen : PolygonalDisk where
  carrier := D.carrier
  n := D.genuineCount
  three_le := D.three_le_genuineCount
  vertex := D.coarseVertex
  vertex_injective := D.coarseVertex_injective
  compact := D.compact
  interior_nonempty := D.interior_nonempty
  regular_closed := D.regular_closed
  interior_pathConnected := D.interior_pathConnected
  frontier_eq := D.coarse_frontier_eq
  simple := D.coarse_simple

end PolygonalDisk

namespace FLC

/-! ## `def:clones`, step 1: the coarsened protoset -/

/-- `def:clones` (first step): erase collinear listed vertices, keeping each
form label (forms with equal carriers stay distinct) and each carrier. -/
def coarsen (P : Protoset) : Protoset where
  Form := P.Form
  fintype := P.fintype
  decEq := P.decEq
  disk := fun p => (P.disk p).coarsen

/-- The coarsened copy of a placed tile. -/
def coarsenTile (A : PlacedTile P) : PlacedTile (coarsen P) := ⟨A.form, A.anchor⟩

theorem coarsenTile_carrier (A : PlacedTile P) : (coarsenTile A).carrier = A.carrier := rfl

private lemma coarsenSubstitution_disjoint (τ : Substitution P) (p : P.Form) :
    DisjointInteriors (coarsenTile '' (τ.rule p).tiles) := by
  dsimp [DisjointInteriors, Set.PairwiseDisjoint, Set.Pairwise, Function.onFun]
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hAB
  have h1 : (coarsenTile A).carrier = A.carrier := coarsenTile_carrier A
  have h2 : (coarsenTile B).carrier = B.carrier := coarsenTile_carrier B
  rw [h1, h2]
  apply (τ.rule p).disjoint hA hB
  intro hab
  apply hAB
  rw [hab]

private lemma coarsenSubstitution_support_eq (τ : Substitution P) (p : P.Form) :
    support (coarsenTile '' (τ.rule p).tiles) = τ.θ • ((coarsen P).disk p).carrier := by
  have : support (coarsenTile '' (τ.rule p).tiles) = support (τ.rule p).tiles := by
    dsimp [support]
    apply Set.ext
    simp only [Set.mem_iUnion, Set.mem_image]
    intro x
    constructor
    · rintro ⟨_, ⟨A, hA, rfl⟩, hx⟩
      exact ⟨A, hA, hx⟩
    · rintro ⟨A, hA, hx⟩
      exact ⟨_, ⟨A, hA, rfl⟩, hx⟩
  rw [this, τ.support_eq]
  rfl

/-- The substitution `τ` read on the coarsened protoset. -/
def coarsenSubstitution (τ : Substitution P) : Substitution (coarsen P) where
  θ := τ.θ
  one_lt := τ.one_lt
  rule := fun p : P.Form =>
    { tiles := coarsenTile '' (τ.rule p).tiles
      finite := (τ.rule p).finite.image coarsenTile
      disjoint := coarsenSubstitution_disjoint τ p }
  support_eq := coarsenSubstitution_support_eq τ

private lemma coarsenTile_translate (A : PlacedTile P) (v : Pt) :
    coarsenTile (A.translate v) = (coarsenTile A).translate v := rfl

private lemma coarsen_translateSet (S : Set (PlacedTile P)) (v : Pt) :
    translateSet v (coarsenTile '' S) = coarsenTile '' translateSet v S := by
  ext B
  simp only [translateSet, Set.mem_image]
  constructor
  · rintro ⟨C, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A.translate v, ⟨A, hA, rfl⟩, (coarsenTile_translate A v).symm⟩
  · rintro ⟨C, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨coarsenTile A, ⟨A, hA, rfl⟩, coarsenTile_translate A v⟩

private lemma coarsen_decomposeTile (τ : Substitution P) (A : PlacedTile P) :
    (coarsenSubstitution τ).decomposeTile (coarsenTile A) =
      coarsenTile '' τ.decomposeTile A := by
  exact coarsen_translateSet (τ.rule A.form).tiles (τ.θ • A.anchor)

private lemma coarsen_decompose (τ : Substitution P) (S : Set (PlacedTile P)) :
    (coarsenSubstitution τ).decompose (coarsenTile '' S) =
      coarsenTile '' τ.decompose S := by
  ext B
  simp only [Substitution.decompose, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨C, ⟨A, hA, rfl⟩, hB⟩
    rw [coarsen_decomposeTile] at hB
    rcases hB with ⟨D, hD, rfl⟩
    exact ⟨D, ⟨A, hA, hD⟩, rfl⟩
  · rintro ⟨D, ⟨A, hA, hD⟩, rfl⟩
    exact ⟨coarsenTile A, ⟨A, hA, rfl⟩, by
      rw [coarsen_decomposeTile]
      exact Set.mem_image_of_mem coarsenTile hD⟩

private lemma coarsen_supertile (τ : Substitution P) (n : ℕ) (p : P.Form) :
    (coarsenSubstitution τ).supertile n p = coarsenTile '' τ.supertile n p := by
  induction n with
  | zero =>
      ext A
      simp [Substitution.supertile, Substitution.decomposeIter, coarsenTile]
  | succ n ih =>
      change (coarsenSubstitution τ).decompose ((coarsenSubstitution τ).supertile n p) =
        coarsenTile '' τ.decompose (τ.supertile n p)
      rw [ih, coarsen_decompose]

private lemma coarsen_crown (S : Set (PlacedTile P)) (w : Pt) :
    crown (coarsenTile '' S) w = coarsenTile '' crown S w := by
  ext B
  simp only [crown, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨A, hA, rfl⟩, hw⟩
    exact ⟨A, ⟨hA, by simpa only [coarsenTile_carrier] using hw⟩, rfl⟩
  · rintro ⟨A, ⟨hA, hw⟩, rfl⟩
    exact ⟨⟨A, hA, rfl⟩, by simpa only [coarsenTile_carrier] using hw⟩

private lemma coarsenTile_vertexSet_subset (A : PlacedTile P) :
    (coarsenTile A).vertexSet ⊆ A.vertexSet := by
  rintro w ⟨i, rfl⟩
  exact ⟨((P.disk A.form).genuineEnum i).1, rfl⟩

private lemma coarsen_isVertexOf (S : Set (PlacedTile P)) (w : Pt)
    (h : IsVertexOf (coarsenTile '' S) w) : IsVertexOf S w := by
  rcases h with ⟨B, ⟨A, hA, rfl⟩, hw⟩
  exact ⟨A, hA, coarsenTile_vertexSet_subset A hw⟩

private lemma coarsen_allowedCrown (τ : Substitution P)
    (K : Set (PlacedTile (coarsen P))) (h : (coarsenSubstitution τ).IsAllowedCrown K) :
    ∃ K' : Set (PlacedTile P), τ.IsAllowedCrown K' ∧ K = coarsenTile '' K' := by
  rcases h with ⟨n, p, w, hw, rfl⟩
  refine ⟨translateSet (-w) (crown (τ.supertile n p) w), ?_, ?_⟩
  · refine ⟨n, p, w, ?_, rfl⟩
    rw [coarsen_supertile] at hw
    exact coarsen_isVertexOf (τ.supertile n p) w hw
  · rw [coarsen_supertile, coarsen_crown, coarsen_translateSet]

/-- FLC survives coarsening. -/
theorem coarsen_flc (τ : Substitution P) (h : τ.FLC) : (coarsenSubstitution τ).FLC := by
  apply Set.Finite.subset (h.image (Set.image coarsenTile))
  rintro K hK
  rcases coarsen_allowedCrown τ K hK with ⟨K', hK', rfl⟩
  exact Set.mem_image_of_mem (Set.image coarsenTile) hK'

/-! ## `lem:finite-neighbourhoods` -/

/-- The neighbourhood of `A` in `S`: all tiles of `S` sharing a point with `A`
(including `A` itself when `A ∈ S`). -/
def neighbourhood (S : Set (PlacedTile P)) (A : PlacedTile P) : Set (PlacedTile P) :=
  {B ∈ S | (A.carrier ∩ B.carrier).Nonempty}

/-- Realized supertile neighbourhoods, normalized so that the selected tile
has anchor `0`; the first component records the selected tile's form.  All
orders `n` are included, in particular singleton order-zero contexts and
incomplete boundary contexts. -/
def realizedContexts (τ : Substitution P) : Set (P.Form × Set (PlacedTile P)) :=
  {N | ∃ (n : ℕ) (p : P.Form), ∃ A ∈ τ.supertile n p,
    N = (A.form, translateSet (-A.anchor) (neighbourhood (τ.supertile n p) A))}

open Pointwise

private def finite_neighbourhoods_CrownContexts (τ : Substitution P) (k : ℕ) :
    Set (P.Form × Set (PlacedTile P)) :=
  {N | ∃ K, τ.IsAllowedCrown K ∧ ∃ S ⊆ τ.decomposeIter k K, ∃ A ∈ S,
    N = (A.form, translateSet (-A.anchor) S)}

/-- The frozen statement below names its proof-irrelevant bound witness. -/
@[unused_variables_ignore_fn]
private meta def finite_neighbourhoods_step6_ignoreUnused : Lean.Linter.IgnoreFunction :=
  fun stx stack _ => stx.getId == `hn &&
    stack.matches [``Lean.binderIdent, `null, ``Lean.bracketedExplicitBinders,
      `null, ``Lean.explicitBinders]

/-- Step 6 of the blueprint proof of `finite_neighbourhoods`: orders n < k
have finitely many possibilities directly. -/
private lemma finite_neighbourhoods_step6 (τ : Substitution P) (k : ℕ) :
    {N | ∃ (n : ℕ) (hn : n < k) (p : P.Form), ∃ A ∈ τ.supertile n p,
      N = (A.form, translateSet (-A.anchor) (neighbourhood (τ.supertile n p) A))}.Finite := by
  have h_eq : {N | ∃ (n : ℕ) (hn : n < k) (p : P.Form), ∃ A ∈ τ.supertile n p,
      N = (A.form, translateSet (-A.anchor) (neighbourhood (τ.supertile n p) A))} =
      ⋃ (n ∈ {m : ℕ | m < k}) (p : P.Form),
        (fun A => (A.form,
          translateSet (-A.anchor) (neighbourhood (τ.supertile n p) A))) '' τ.supertile n p := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨n, hn, p, A, hA, rfl⟩
      exact ⟨n, hn, p, A, hA, rfl⟩
    · rintro ⟨n, hn, p, A, hA, rfl⟩
      exact ⟨n, hn, p, A, hA, rfl⟩
  rw [h_eq]
  apply Set.Finite.biUnion (Set.finite_lt_nat k)
  intro n _hn
  refine Set.finite_iUnion ?_
  intro p
  exact Set.Finite.image _ (Crowns.supertile_finite τ n p)

private lemma finite_neighbourhoods_step5_decomposeTile_finite (τ : Substitution P)
    (A : PlacedTile P) : (τ.decomposeTile A).Finite :=
  Set.Finite.image _ (τ.rule A.form).finite

private lemma finite_neighbourhoods_step5_decompose_finite (τ : Substitution P)
    {S : Set (PlacedTile P)} (hS : S.Finite) : (τ.decompose S).Finite :=
  Set.Finite.biUnion hS (fun A _ => finite_neighbourhoods_step5_decomposeTile_finite τ A)

private lemma finite_neighbourhoods_step5_decomposeIter_finite (τ : Substitution P) (n : ℕ)
    {S : Set (PlacedTile P)} (hS : S.Finite) : (τ.decomposeIter n S).Finite := by
  induction' n with n ih
  · exact hS
  · exact finite_neighbourhoods_step5_decompose_finite τ ih

/-- Step 5 of the blueprint proof of `finite_neighbourhoods`: there are finitely
many allowed crowns and each has a finite kth image, with finitely many selected
subpatches and distinguished tiles. -/
private lemma finite_neighbourhoods_step5 (τ : Substitution P) (h : τ.FLC) (k : ℕ) :
    (finite_neighbourhoods_CrownContexts τ k).Finite := by
  have H1 : {K | τ.IsAllowedCrown K}.Finite := h
  let f : Set (PlacedTile P) → Set (P.Form × Set (PlacedTile P)) :=
    fun K => {N | ∃ S ⊆ τ.decomposeIter k K, ∃ A ∈ S, N = (A.form, translateSet (-A.anchor) S)}
  have h_subset : finite_neighbourhoods_CrownContexts τ k ⊆ ⋃ K ∈ {K | τ.IsAllowedCrown K}, f K :=
    by
      rintro N ⟨K, hK, S, hS, A, hA, rfl⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨K, hK, S, hS, A, hA, rfl⟩
  apply Set.Finite.subset _ h_subset
  apply Set.Finite.biUnion H1
  intro K hK
  have hCat : Crowns.IsCatalogue (Crowns.pointedCatalogue τ) :=
    Crowns.isCatalogue_pointedCatalogue τ h
  have hK_fin : K.Finite := (hCat.2 K hK).1
  have h_dec_fin : (τ.decomposeIter k K).Finite :=
    finite_neighbourhoods_step5_decomposeIter_finite τ k hK_fin
  have h_pow_fin : {S | S ⊆ τ.decomposeIter k K}.Finite := Set.Finite.finite_subsets h_dec_fin
  let g : Set (PlacedTile P) → Set (P.Form × Set (PlacedTile P)) :=
    fun S => {N | ∃ A ∈ S, N = (A.form, translateSet (-A.anchor) S)}
  have h_f_subset : f K ⊆ ⋃ S ∈ {S | S ⊆ τ.decomposeIter k K}, g S := by
    rintro N ⟨S, hS, A, hA, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨S, hS, A, hA, rfl⟩
  apply Set.Finite.subset _ h_f_subset
  apply Set.Finite.biUnion h_pow_fin
  intro S hS
  have hS_fin : S.Finite := Set.Finite.subset h_dec_fin hS
  let p : PlacedTile P → P.Form × Set (PlacedTile P) :=
    fun A => (A.form, translateSet (-A.anchor) S)
  have h_g_eq : g S = p '' S := by
    ext N
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact ⟨A, hA, rfl⟩
    · rintro ⟨A, hA, rfl⟩
      exact ⟨A, hA, rfl⟩
  rw [h_g_eq]
  exact Set.Finite.image p hS_fin

private lemma finite_neighbourhoods_support_translate (v : Pt)
    (S : Set (PlacedTile P)) :
    support (translateSet v S) = v +ᵥ support S := by
  ext x
  simp only [support, translateSet, PlacedTile.translate, PlacedTile.carrier,
    Set.mem_iUnion, Set.mem_image, Set.mem_vadd_set_iff_neg_vadd_mem]
  constructor
  · rintro ⟨A, ⟨B, hB, rfl⟩, hx⟩
    exact ⟨B, hB, by simpa [← add_assoc] using hx⟩
  · rintro ⟨A, hA, hx⟩
    refine ⟨⟨A.form, v +ᵥ A.anchor⟩, ⟨A, hA, rfl⟩, ?_⟩
    simpa [← add_assoc] using hx

private lemma finite_neighbourhoods_translateSet_add (v u : Pt)
    (S : Set (PlacedTile P)) :
    translateSet v (translateSet u S) = translateSet (v + u) S := by
  rw [translateSet, translateSet, translateSet, Set.image_image]
  congr 1
  funext A
  apply PlacedTile.ext
  · rfl
  · simp [PlacedTile.translate, add_assoc]

private lemma finite_neighbourhoods_decompose_translate (τ : Substitution P)
    (v : Pt) (S : Set (PlacedTile P)) :
    τ.decompose (translateSet v S) =
      translateSet (τ.θ • v) (τ.decompose S) := by
  ext C
  simp only [Substitution.decompose, Substitution.decomposeTile, translateSet,
    Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨A, ⟨A₀, hA₀, rfl⟩, B, hB, rfl⟩
    refine ⟨B.translate (τ.θ • A₀.anchor), ⟨A₀, hA₀, B, hB, rfl⟩, ?_⟩
    apply PlacedTile.ext
    · rfl
    · simp only [PlacedTile.translate, vadd_eq_add, smul_add]
      abel
  · rintro ⟨C₀, ⟨A, hA, B, hB, rfl⟩, rfl⟩
    refine ⟨A.translate v, ⟨A, hA, rfl⟩, B, hB, ?_⟩
    apply PlacedTile.ext
    · rfl
    · simp only [PlacedTile.translate, vadd_eq_add, smul_add]
      abel

private lemma finite_neighbourhoods_decomposeIter_translate (τ : Substitution P)
    (k : ℕ) (v : Pt) (S : Set (PlacedTile P)) :
    τ.decomposeIter k (translateSet v S) =
      translateSet (τ.θ ^ k • v) (τ.decomposeIter k S) := by
  induction k with
  | zero => simp [Substitution.decomposeIter]
  | succ k ih =>
      change τ.decompose (τ.decomposeIter k (translateSet v S)) = _
      rw [ih, finite_neighbourhoods_decompose_translate]
      rw [pow_succ', mul_smul]
      rfl

private lemma finite_neighbourhoods_decompose_mono (τ : Substitution P)
    {S T : Set (PlacedTile P)} (hST : S ⊆ T) :
    τ.decompose S ⊆ τ.decompose T := by
  intro A hA
  simp only [Substitution.decompose, Set.mem_iUnion] at hA ⊢
  rcases hA with ⟨B, hB, hAB⟩
  exact ⟨B, hST hB, hAB⟩

private lemma finite_neighbourhoods_decomposeIter_mono (τ : Substitution P)
    (k : ℕ) {S T : Set (PlacedTile P)} (hST : S ⊆ T) :
    τ.decomposeIter k S ⊆ τ.decomposeIter k T := by
  induction k with
  | zero => exact hST
  | succ k ih => exact finite_neighbourhoods_decompose_mono τ ih

private lemma finite_neighbourhoods_decomposeIter_add (τ : Substitution P)
    (a b : ℕ) (S : Set (PlacedTile P)) :
    τ.decomposeIter (a + b) S = τ.decomposeIter b (τ.decomposeIter a S) := by
  induction b with
  | zero => simp [Substitution.decomposeIter]
  | succ b ih =>
      change τ.decomposeIter (a + b + 1) S =
        τ.decompose (τ.decomposeIter b (τ.decomposeIter a S))
      rw [show a + b + 1 = (a + b) + 1 by omega]
      change τ.decompose (τ.decomposeIter (a + b) S) = _
      rw [ih]

private lemma finite_neighbourhoods_supertile_split (τ : Substitution P)
    (a b : ℕ) (p : P.Form) :
    τ.supertile (a + b) p = τ.decomposeIter b (τ.supertile a p) := by
  exact finite_neighbourhoods_decomposeIter_add τ a b {⟨p, 0⟩}

private lemma finite_neighbourhoods_decomposeIter_finite' (τ : Substitution P)
    (k : ℕ) {S : Set (PlacedTile P)} (hS : S.Finite) :
    (τ.decomposeIter k S).Finite := by
  induction k with
  | zero => exact hS
  | succ k ih =>
      exact Set.Finite.biUnion ih fun A _ =>
        Set.Finite.image _ (τ.rule A.form).finite

private lemma finite_neighbourhoods_support_decomposeTile (τ : Substitution P)
    (A : PlacedTile P) :
    support (τ.decomposeTile A) = τ.θ • A.carrier := by
  dsimp [Substitution.decomposeTile]
  rw [finite_neighbourhoods_support_translate, τ.support_eq, PlacedTile.carrier]
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, hx⟩
    refine ⟨A.anchor + y, ?_, ?_⟩
    · simpa
    · rw [smul_add]
      calc
        τ.θ • A.anchor + τ.θ • y =
            τ.θ • A.anchor + (-(τ.θ • A.anchor) + x) := by congr 1
        _ = x := by abel
  · rintro ⟨y, hy, rfl⟩
    refine ⟨-A.anchor + y, ?_, ?_⟩
    · simpa
    · simp [smul_add]

private lemma finite_neighbourhoods_support_decompose (τ : Substitution P)
    (S : Set (PlacedTile P)) :
    support (τ.decompose S) = τ.θ • support S := by
  dsimp [Substitution.decompose, support]
  rw [Set.smul_set_iUnion₂]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨A, ⟨B, hB, hA⟩, hx⟩
    refine ⟨B, hB, ?_⟩
    have h : x ∈ support (τ.decomposeTile B) := by
      simp only [support, Set.mem_iUnion]
      exact ⟨A, hA, hx⟩
    rwa [finite_neighbourhoods_support_decomposeTile] at h
  · rintro ⟨A, hA, hx⟩
    have h : x ∈ support (τ.decomposeTile A) := by
      rwa [finite_neighbourhoods_support_decomposeTile]
    simp only [support, Set.mem_iUnion] at h
    rcases h with ⟨B, hB, hx'⟩
    exact ⟨B, ⟨A, hA, hB⟩, hx'⟩

private lemma finite_neighbourhoods_support_decomposeIter (τ : Substitution P)
    (k : ℕ) (S : Set (PlacedTile P)) :
    support (τ.decomposeIter k S) = τ.θ ^ k • support S := by
  induction k with
  | zero => simp [Substitution.decomposeIter]
  | succ k ih =>
      change support (τ.decompose (τ.decomposeIter k S)) = _
      rw [finite_neighbourhoods_support_decompose, ih, smul_smul, pow_succ']

private lemma finite_neighbourhoods_self_mem {S : Set (PlacedTile P)}
    {A : PlacedTile P} (hA : A ∈ S) : A ∈ neighbourhood S A := by
  refine ⟨hA, ?_⟩
  obtain ⟨x, hx⟩ := (P.disk A.form).interior_nonempty
  have hx' : x ∈ (P.disk A.form).carrier := interior_subset hx
  have hAx : A.anchor +ᵥ x ∈ A.carrier := by
    change A.anchor +ᵥ x ∈ A.anchor +ᵥ (P.disk A.form).carrier
    exact Set.mem_vadd_set.mpr ⟨x, hx', rfl⟩
  exact ⟨A.anchor +ᵥ x, hAx, hAx⟩

private lemma finite_neighbourhoods_neighbourhood_finite
    {S : Set (PlacedTile P)} {A : PlacedTile P} (hS : S.Finite) :
    (neighbourhood S A).Finite :=
  hS.subset fun _ hB => hB.1

private lemma finite_neighbourhoods_support_bounded
    {S : Set (PlacedTile P)} (hS : S.Finite) :
    Bornology.IsBounded (support S) := by
  have h_eq : support S = ⋃ (A ∈ S), A.carrier := by
    ext x
    simp [support, PlacedTile.carrier]
  rw [h_eq]
  exact (hS.isCompact_biUnion fun A _ => by
    dsimp [PlacedTile.carrier, PlacedTile.translate]
    rw [← Set.image_vadd]
    exact (P.disk A.form).compact.image (continuous_const_vadd A.anchor)).isBounded

private lemma finite_neighbourhoods_diam_le (D : ℝ)
    (hD : ∀ q : P.Form, Metric.diam (P.disk q).carrier ≤ D)
    (S : Set (PlacedTile P)) (A : PlacedTile P) :
    Metric.diam (support (neighbourhood S A)) ≤ 3 * D := by
  have hD0 : 0 ≤ D :=
    (Metric.diam_nonneg.trans (hD A.form))
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx z hz
  simp only [support, Set.mem_iUnion] at hx hz
  rcases hx with ⟨B, hB, hxB⟩
  rcases hz with ⟨C, hC, hzC⟩
  obtain ⟨y, hyA, hyB⟩ := hB.2
  obtain ⟨w, hwA, hwC⟩ := hC.2
  have hBA : Metric.diam B.carrier ≤ D := by
    rw [PlacedTile.carrier, diam_vadd]
    exact hD B.form
  have hCA : Metric.diam C.carrier ≤ D := by
    rw [PlacedTile.carrier, diam_vadd]
    exact hD C.form
  have hAA : Metric.diam A.carrier ≤ D := by
    rw [PlacedTile.carrier, diam_vadd]
    exact hD A.form
  have hxy : dist x y ≤ D :=
    (Metric.dist_le_diam_of_mem
      (IsCompact.vadd B.anchor (P.disk B.form).compact).isBounded hxB hyB).trans hBA
  have hyw : dist y w ≤ D :=
    (Metric.dist_le_diam_of_mem
      (IsCompact.vadd A.anchor (P.disk A.form).compact).isBounded hyA hwA).trans hAA
  have hwz : dist w z ≤ D :=
    (Metric.dist_le_diam_of_mem
      (IsCompact.vadd C.anchor (P.disk C.form).compact).isBounded hwC hzC).trans hCA
  calc
    dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
    _ ≤ dist x y + (dist y w + dist w z) := by gcongr; exact dist_triangle _ _ _
    _ ≤ 3 * D := by linarith

private lemma finite_neighbourhoods_exists_scale (τ : Substitution P)
    (ε D : ℝ) (hε : 0 < ε) (hD : 0 ≤ D) :
    ∃ k : ℕ, (τ.θ ^ k)⁻¹ * D < ε := by
  have hθ : 0 < τ.θ := lt_trans zero_lt_one τ.one_lt
  have hq1 : τ.θ⁻¹ < 1 := (inv_lt_one₀ hθ).2 τ.one_lt
  by_cases hD0 : D = 0
  · exact ⟨0, by simp [hD0, hε]⟩
  · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hDpos) hq1
    refine ⟨k, ?_⟩
    rw [← inv_pow]
    exact (lt_div_iff₀ hDpos).mp hk

/-- The frozen target statement names two proof-irrelevant witnesses. -/
@[unused_variables_ignore_fn]
private meta def finite_neighbourhoods_step1to4_ignoreUnused :
    Lean.Linter.IgnoreFunction :=
  fun stx _ _ => stx.getId == `hn || stx.getId == `hA

/-- Steps 1 to 4 of the blueprint proof of `finite_neighbourhoods`: all neighbourhood
supports have bounded diameter, so there is k such that in supertiles of order n >= k,
the neighbourhood is covered by a full pointed crown of order n-k, which implies
the context belongs to CrownContexts. -/
private lemma finite_neighbourhoods_step1to4 (τ : Substitution P) (h : τ.FLC) :
    ∃ k : ℕ, ∀ (n : ℕ) (_hn : k ≤ n) (p : P.Form) (A : PlacedTile P)
      (_hA : A ∈ τ.supertile n p),
      (A.form, translateSet (-A.anchor) (neighbourhood (τ.supertile n p) A)) ∈
        finite_neighbourhoods_CrownContexts τ k := by
  let D := ∑ q : P.Form, Metric.diam (P.disk q).carrier
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun (q : P.Form) _ =>
    Metric.diam_nonneg (s := (P.disk q).carrier)
  have hD : ∀ q : P.Form, Metric.diam (P.disk q).carrier ≤ D := by
    intro q
    dsimp [D]
    exact Finset.single_le_sum
      (fun (r : P.Form) (_ : r ∈ (Finset.univ : Finset P.Form)) =>
        Metric.diam_nonneg (s := (P.disk r).carrier)) (Finset.mem_univ q)
  have hcat := Crowns.isCatalogue_pointedCatalogue τ h
  obtain ⟨ε, hε, hcover⟩ := Crowns.uniformCrownCoverSupertile hcat
  obtain ⟨k, hk⟩ :=
    finite_neighbourhoods_exists_scale τ ε (3 * D) hε (mul_nonneg (by positivity) hD0)
  refine ⟨k, ?_⟩
  intro n hn p A hA
  let m := n - k
  have hmk : m + k = n := Nat.sub_add_cancel hn
  let N := neighbourhood (τ.supertile n p) A
  have hNsub : N ⊆ τ.supertile n p := fun _ hB => hB.1
  have hNfin : N.Finite :=
    finite_neighbourhoods_neighbourhood_finite (Crowns.supertile_finite τ n p)
  have hNbound : Bornology.IsBounded (support N) :=
    finite_neighbourhoods_support_bounded hNfin
  have hNdiam : Metric.diam (support N) ≤ 3 * D :=
    finite_neighbourhoods_diam_le D hD (τ.supertile n p) A
  let c : ℝ := (τ.θ ^ k)⁻¹
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr (pow_nonneg (le_of_lt (lt_trans zero_lt_one τ.one_lt)) k)
  let X : Set Pt := (fun x => c • x) '' support N
  have hLip : LipschitzWith ⟨c, hc0⟩ (fun x : Pt => c • x) := by
    have hcNorm : ‖c‖₊ = ⟨c, hc0⟩ := by
      ext
      exact Real.norm_of_nonneg hc0
    rw [← hcNorm]
    exact lipschitzWith_smul c
  have hXbound : Bornology.IsBounded X := hLip.isBounded_image hNbound
  have hXdiam : Metric.diam X < ε := by
    have hle := hLip.diam_image_le (support N) hNbound
    have hle' : Metric.diam X ≤ c * Metric.diam (support N) := by
      simpa [X] using hle
    exact hle'.trans_lt ((mul_le_mul_of_nonneg_left hNdiam hc0).trans_lt hk)
  let M := Crowns.supertileMacro τ m p
  have hMcrowns : Crowns.AllCrownsIn (Crowns.pointedCatalogue τ) M.tiles := by
    intro w hw
    exact ⟨m, p, w, hw, rfl⟩
  have hXsub : X ⊆ support M.tiles := by
    rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ support (τ.supertile n p) := by
      simp only [support, Set.mem_iUnion] at hy ⊢
      rcases hy with ⟨B, hB, hyB⟩
      exact ⟨B, hNsub hB, hyB⟩
    rw [τ.iterate_support n p] at hy'
    rcases hy' with ⟨z, hz, rfl⟩
    change c • (τ.θ ^ n • z) ∈ support (τ.supertile m p)
    rw [τ.iterate_support m p]
    refine ⟨z, hz, ?_⟩
    rw [smul_smul, ← hmk, pow_add]
    dsimp [c]
    have hθk : τ.θ ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one τ.one_lt))
    rw [mul_comm (τ.θ ^ m) (τ.θ ^ k), ← mul_assoc,
      inv_mul_cancel₀ hθk, one_mul]
  obtain ⟨v, hv, hcovInt⟩ := hcover M hMcrowns X hXbound hXdiam
  have hcov : X ⊆ support (crown M.tiles v) := fun x hx => hcovInt ⟨hx, hXsub hx⟩
  let C := crown (τ.supertile m p) v
  have hCsub : C ⊆ τ.supertile m p := fun _ hB => hB.1
  have hCfin : C.Finite :=
    (Crowns.supertile_finite τ m p).subset hCsub
  have hsupport : support N ⊆ support (τ.decomposeIter k C) := by
    intro x hx
    rw [finite_neighbourhoods_support_decomposeIter]
    refine ⟨c • x, ?_, ?_⟩
    · apply hcov
      exact ⟨x, hx, rfl⟩
    · dsimp [c]
      rw [smul_smul, mul_inv_cancel₀, one_smul]
      exact pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one τ.one_lt))
  have hdescFin : (τ.decomposeIter k C).Finite :=
    finite_neighbourhoods_decomposeIter_finite' τ k hCfin
  have hdescSub : τ.decomposeIter k C ⊆ τ.supertile n p := by
    rw [← hmk, finite_neighbourhoods_supertile_split]
    exact finite_neighbourhoods_decomposeIter_mono τ k hCsub
  let F : Patch P :=
    { tiles := τ.decomposeIter k C
      finite := hdescFin
      disjoint := by
        intro B hB E hE hBE
        exact Crowns.supertile_disjoint τ n p (hdescSub hB) (hdescSub hE) hBE }
  have hNdesc : N ⊆ τ.decomposeIter k C := by
    intro B hB
    apply Patch.mem_of_carrier_subset_union F B
    · intro E hE hEB
      exact Crowns.supertile_disjoint τ n p (hNsub hB) (hdescSub hE) hEB.symm
    · intro x hx
      apply hsupport
      simp only [support, Set.mem_iUnion]
      exact ⟨B, hB, hx⟩
  let u : Pt := τ.θ ^ k • v
  let K := translateSet (-v) C
  let S' := translateSet (-u) N
  let A' := A.translate (-u)
  have hK : τ.IsAllowedCrown K := ⟨m, p, v, hv, rfl⟩
  have hS' : S' ⊆ τ.decomposeIter k K := by
    rw [finite_neighbourhoods_decomposeIter_translate]
    intro B hB
    rcases hB with ⟨B₀, hB₀, rfl⟩
    refine ⟨B₀, hNdesc hB₀, ?_⟩
    apply PlacedTile.ext
    · rfl
    · dsimp [u]
      simp only [PlacedTile.translate, vadd_eq_add, smul_neg]
  have hA'N : A' ∈ S' := by
    exact ⟨A, finite_neighbourhoods_self_mem hA, rfl⟩
  refine ⟨K, hK, S', hS', A', hA'N, ?_⟩
  apply Prod.ext
  · rfl
  · dsimp [A', S', u]
    change translateSet (-A.anchor) N =
      translateSet (-(A.translate (-(τ.θ ^ k • v))).anchor)
        (translateSet (-(τ.θ ^ k • v)) N)
    rw [finite_neighbourhoods_translateSet_add]
    congr 1
    simp [PlacedTile.translate]

/-- `lem:finite-neighbourhoods`: under FLC there are finitely many tile
neighbourhoods in supertiles, up to translation. -/
theorem finite_neighbourhoods (τ : Substitution P) (h : τ.FLC) :
    (realizedContexts τ).Finite := by
  obtain ⟨k, hk⟩ := finite_neighbourhoods_step1to4 τ h
  have H1 := finite_neighbourhoods_step6 τ k
  have H2 := finite_neighbourhoods_step5 τ h k
  have Hsub : realizedContexts τ ⊆
      {N | ∃ (n : ℕ) (_ : n < k) (p : P.Form), ∃ A ∈ τ.supertile n p,
        N = (A.form, translateSet (-A.anchor) (neighbourhood (τ.supertile n p) A))} ∪
      finite_neighbourhoods_CrownContexts τ k := by
    intro N hN
    rcases hN with ⟨n, p, A, hA, rfl⟩
    by_cases hnk : n < k
    · left
      exact ⟨n, hnk, p, A, hA, rfl⟩
    · right
      push_neg at hnk
      exact hk n hnk p A hA
  exact Set.Finite.subset (Set.Finite.union H1 H2) Hsub

/-! ## `def:clones`, step 2: genuine-corner clones -/

/-- `def:clones`: a clone is a form together with a realized (normalized)
supertile neighbourhood context of a tile of that form. -/
structure GenuineCornerClone (τ : Substitution P) where
  form : P.Form
  context : Set (PlacedTile P)
  realized : (form, context) ∈ realizedContexts τ

/-- Genuine corners of a placed tile. -/
def tileGenuineCorners (B : PlacedTile P) : Set Pt :=
  B.anchor +ᵥ (P.disk B.form).genuineCorners

variable {τ : Substitution P}

/-- The listed vertices of a clone disk: genuine corners of underlying context
carriers (including the selected tile itself) lying on the boundary of the
selected form.  Artificial clone vertices of neighbours are not added. -/
def cloneVertexSet (c : GenuineCornerClone τ) : Set Pt :=
  frontier (P.disk c.form).carrier ∩ ⋃ B ∈ c.context, tileGenuineCorners B

private lemma cloneVertexSet_finite (c : GenuineCornerClone τ) :
    (cloneVertexSet c).Finite := by
  rcases c.realized with ⟨n, p, A, hA, hcontext⟩
  have hcontext_finite : c.context.Finite := by
    have hc := congrArg Prod.snd hcontext
    change c.context = translateSet (-A.anchor) (neighbourhood (τ.supertile n p) A) at hc
    rw [hc]
    apply Set.Finite.image
    exact (Crowns.supertile_finite τ n p).subset fun _ h => h.1
  apply Set.Finite.inter_of_right
  apply Set.Finite.biUnion hcontext_finite
  intro B _
  apply ((Set.finite_range (P.disk B.form).vertex).image fun x => B.anchor +ᵥ x).subset
  rintro _ ⟨x, ⟨i, hi, rfl⟩, rfl⟩
  refine ⟨(P.disk B.form).vertex i, ?_, rfl⟩
  exact ⟨i, rfl⟩

private lemma genuineCorners_subset_cloneVertexSet (c : GenuineCornerClone τ) :
    (P.disk c.form).genuineCorners ⊆ cloneVertexSet c := by
  rcases c.realized with ⟨n, p, A, hA, hcontext⟩
  have hform := congrArg Prod.fst hcontext
  have hcontext' := congrArg Prod.snd hcontext
  change c.form = A.form at hform
  change c.context = translateSet (-A.anchor) (neighbourhood (τ.supertile n p) A) at hcontext'
  intro q hq
  constructor
  · rw [(P.disk c.form).frontier_eq]
    rcases hq with ⟨i, hi, rfl⟩
    exact Set.mem_iUnion.2 ⟨i, left_mem_segment ℝ _ _⟩
  · rw [hcontext']
    let B : PlacedTile P := ⟨A.form, 0⟩
    apply Set.mem_iUnion.2 ⟨B, ?_⟩
    apply Set.mem_iUnion.2 ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := (P.disk A.form).interior_nonempty
      exact ⟨A, ⟨hA, ⟨A.anchor +ᵥ x,
        ⟨⟨x, interior_subset hx, rfl⟩, ⟨x, interior_subset hx, rfl⟩⟩⟩⟩, by
          apply PlacedTile.ext
          · rfl
          · change -A.anchor + A.anchor = 0
            simp⟩
    · rw [hform] at hq
      simpa [B, tileGenuineCorners] using hq

private def polygonalDiskReindex (D : PolygonalDisk) (e : Equiv.Perm (Fin D.n))
    (he : ∀ i, e (finRotate D.n i) = finRotate D.n (e i)) : PolygonalDisk where
  carrier := D.carrier
  n := D.n
  three_le := D.three_le
  vertex := D.vertex ∘ e
  vertex_injective := D.vertex_injective.comp e.injective
  compact := D.compact
  interior_nonempty := D.interior_nonempty
  regular_closed := D.regular_closed
  interior_pathConnected := D.interior_pathConnected
  frontier_eq := by
    rw [D.frontier_eq]
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
      apply Set.mem_iUnion.2 ⟨e.symm i, ?_⟩
      simpa [Function.comp_apply, he] using hi
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
      apply Set.mem_iUnion.2 ⟨e i, ?_⟩
      simpa [Function.comp_apply, he] using hi
  simple := by
    intro i j hij
    simpa [Function.comp_apply, he] using D.simple (e i) (e j) (fun h => hij (e.injective h))

private lemma polygonalDiskReindex_vertexSet (D : PolygonalDisk) (e : Equiv.Perm (Fin D.n))
    (he : ∀ i, e (finRotate D.n i) = finRotate D.n (e i)) :
    (polygonalDiskReindex D e he).vertexSet = D.vertexSet := by
  apply Set.Subset.antisymm
  · rintro _ ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨e.symm i, by simp [polygonalDiskReindex]⟩

private lemma segment_split {a b q : Pt} (hq : q ∈ segment ℝ a b) :
    segment ℝ a b = segment ℝ a q ∪ segment ℝ q b := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [← insert_endpoints_openSegment] at hx
    rcases hx with hx | hx | hx
    · subst x
      exact Or.inl (left_mem_segment ℝ _ _)
    · subst x
      exact Or.inr (right_mem_segment ℝ _ _)
    · have hline : q ∈ Set.range (AffineMap.lineMap a b : ℝ → Pt) := by
        rw [segment_eq_image_lineMap] at hq
        rcases hq with ⟨t, ht, rfl⟩
        exact ⟨t, rfl⟩
      rcases openSegment_subset_union a b hline hx with hx | hx
      · rcases hx with rfl
        exact Or.inl (right_mem_segment ℝ _ _)
      · rcases hx with hx | hx
        · exact Or.inl (openSegment_subset_segment ℝ _ _ hx)
        · exact Or.inr (openSegment_subset_segment ℝ _ _ hx)
  · exact union_subset
      ((convex_segment a b).segment_subset (left_mem_segment ℝ _ _) hq)
      ((convex_segment a b).segment_subset hq (right_mem_segment ℝ _ _))

private lemma finRotate_succ_ne_zero {n : ℕ} (hn : 0 < n) (k : Fin n)
    (h : finRotate n k ≠ ⟨0, hn⟩) :
    finRotate (n + 1) k.succ = (finRotate n k).succ := by
  cases n with
  | zero => omega
  | succ n =>
    have hk : k ≠ Fin.last n := by
      intro hk
      apply h
      subst k
      exact finRotate_last
    have hks : k.succ ≠ Fin.last (n + 1) := by
      intro hks
      apply hk
      apply Fin.ext
      have := congrArg Fin.val hks
      simp only [Fin.val_succ, Fin.val_last] at this ⊢
      omega
    apply Fin.ext
    rw [coe_finRotate, if_neg hks, Fin.val_succ, Fin.val_succ, coe_finRotate, if_neg hk]

private lemma finRotate_succ_eq_zero {n : ℕ} (hn : 0 < n) (k : Fin n)
    (h : finRotate n k = ⟨0, hn⟩) :
    finRotate (n + 1) k.succ = (0 : Fin (n + 1)) := by
  ext
  have hv := congrArg Fin.val h
  cases n with
  | zero => omega
  | succ n =>
    have hk : k = Fin.last n :=
      (finRotate (n + 1)).injective (h.trans finRotate_last.symm)
    subst k
    have he : (Fin.last n).succ = Fin.last (n + 1) := Fin.ext rfl
    rw [he, finRotate_last]

private lemma finCons_one {n : ℕ} (hn : 0 < n) {X : Type} (q : X) (v : Fin n → X) :
    (@Fin.cons n (fun _ => X) q v) (1 : Fin (n + 1)) = v ⟨0, hn⟩ := by
  have he : (1 : Fin (n + 1)) = Fin.succ ⟨0, hn⟩ := by
    apply Fin.ext
    norm_num [Fin.val_succ]
    exact hn
  rw [he, Fin.cons_succ]

private def polygonalDiskZero (D : PolygonalDisk) : Fin D.n :=
  ⟨0, lt_of_lt_of_le (by omega) D.three_le⟩

private def polygonalDiskClosing (D : PolygonalDisk) : Fin D.n :=
  (finRotate D.n).symm (polygonalDiskZero D)

private lemma polygonalDisk_finRotate_ne_self (D : PolygonalDisk) (i : Fin D.n) :
    finRotate D.n i ≠ i := by
  generalize hn : D.n = n at i
  have hn3 : 3 ≤ n := hn ▸ D.three_le
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have h1 : (1 : Fin (m + 1)) = 0 := by
    have := congrArg (fun x => x - i) h
    simpa using this
  have : NeZero (m + 1) := ⟨by omega⟩
  rw [Fin.one_eq_zero_iff] at h1
  omega

private lemma polygonalDisk_vertex_ne_next (D : PolygonalDisk) (i : Fin D.n) :
    D.vertex i ≠ D.vertex (finRotate D.n i) := by
  intro h
  exact polygonalDisk_finRotate_ne_self D i (D.vertex_injective h).symm

private lemma polygonalDisk_eq_side_of_open_mem (D : PolygonalDisk) {i j : Fin D.n} {q : Pt}
    (hq : q ∈ openSegment ℝ (D.vertex i) (D.vertex (finRotate D.n i)))
    (hq' : q ∈ segment ℝ (D.vertex j) (D.vertex (finRotate D.n j))) : j = i := by
  by_contra hji
  have h := D.simple i j (Ne.symm hji) ⟨openSegment_subset_segment ℝ _ _ hq, hq'⟩
  have hab := polygonalDisk_vertex_ne_next D i
  rcases h.1 with h1 | h1
  · rw [h1] at hq
    exact hab (left_mem_openSegment_iff.mp hq)
  · rw [Set.mem_singleton_iff] at h1
    rw [h1] at hq
    exact hab (right_mem_openSegment_iff.mp hq)

private lemma polygonalDisk_vertex_not_openSide (D : PolygonalDisk) (k i : Fin D.n) :
    D.vertex k ∉ openSegment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) := by
  intro h
  have hk := polygonalDisk_eq_side_of_open_mem D h (left_mem_segment ℝ _ _)
  subst hk
  exact polygonalDisk_vertex_ne_next D k (left_mem_openSegment_iff.mp h)

set_option maxHeartbeats 800000 in
private def polygonalDiskInsertClosing (D : PolygonalDisk) (q : Pt)
    (hq : q ∈ openSegment ℝ
      (D.vertex (polygonalDiskClosing D)) (D.vertex (polygonalDiskZero D))) : PolygonalDisk where
  carrier := D.carrier
  n := D.n + 1
  three_le := by
    have := D.three_le
    omega
  vertex := Fin.cons q D.vertex
  vertex_injective := Fin.cons_injective_of_injective
    (fun h => by
      rcases h with ⟨i, hi⟩
      apply polygonalDisk_vertex_not_openSide D i (polygonalDiskClosing D)
      simpa [polygonalDiskClosing, polygonalDiskZero] using hi ▸ hq)
    D.vertex_injective
  compact := D.compact
  interior_nonempty := D.interior_nonempty
  regular_closed := D.regular_closed
  interior_pathConnected := D.interior_pathConnected
  frontier_eq := by
    have hn : 0 < D.n := lt_of_lt_of_le (by omega) D.three_le
    let z : Fin D.n := ⟨0, hn⟩
    let l : Fin D.n := (finRotate D.n).symm z
    have hl : finRotate D.n l = z := (finRotate D.n).apply_symm_apply z
    have hq' : q ∈ segment ℝ (D.vertex l) (D.vertex z) :=
      openSegment_subset_segment ℝ _ _ hq
    rw [D.frontier_eq]
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨k, hkx⟩
      by_cases hk : finRotate D.n k = z
      · have hkl : k = l := (finRotate D.n).injective (hk.trans hl.symm)
        subst k
        rw [hl] at hkx
        rw [segment_split hq'] at hkx
        rcases hkx with hkx | hkx
        · apply Set.mem_iUnion.2 ⟨l.succ, ?_⟩
          rw [finRotate_succ_eq_zero hn l hl, Fin.cons_succ, Fin.cons_zero]
          exact hkx
        · apply Set.mem_iUnion.2 ⟨0, ?_⟩
          rw [finRotate_apply_zero, Fin.cons_zero, finCons_one hn]
          exact hkx
      · apply Set.mem_iUnion.2 ⟨k.succ, ?_⟩
        rw [finRotate_succ_ne_zero hn k hk, Fin.cons_succ, Fin.cons_succ]
        exact hkx
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨j, hjx⟩
      induction j using Fin.cases with
      | zero =>
        rw [finRotate_apply_zero, Fin.cons_zero, finCons_one hn] at hjx
        apply Set.mem_iUnion.2 ⟨l, ?_⟩
        simpa [hl] using (convex_segment (D.vertex l) (D.vertex z)).segment_subset hq'
          (right_mem_segment ℝ _ _) hjx
      | succ k =>
        by_cases hk : finRotate D.n k = z
        · rw [finRotate_succ_eq_zero hn k hk, Fin.cons_succ, Fin.cons_zero] at hjx
          apply Set.mem_iUnion.2 ⟨k, ?_⟩
          have hqk : q ∈ segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) := by
            rw [hk]
            have hkl : k = l := (finRotate D.n).injective (hk.trans hl.symm)
            simpa [hkl] using hq'
          exact (convex_segment (D.vertex k) (D.vertex (finRotate D.n k))).segment_subset
            (left_mem_segment ℝ _ _) hqk hjx
        · rw [finRotate_succ_ne_zero hn k hk, Fin.cons_succ, Fin.cons_succ] at hjx
          exact Set.mem_iUnion.2 ⟨k, hjx⟩
  simple := by
    have hn : 0 < D.n := lt_of_lt_of_le (by omega) D.three_le
    let z : Fin D.n := ⟨0, hn⟩
    let l : Fin D.n := (finRotate D.n).symm z
    have hl : finRotate D.n l = z := (finRotate D.n).apply_symm_apply z
    have hq0 : q ∈ openSegment ℝ (D.vertex l) (D.vertex z) := by
      simpa [l, z, polygonalDiskClosing, polygonalDiskZero] using hq
    have hlz : D.vertex l ≠ D.vertex z := by
      simpa [hl] using polygonalDisk_vertex_ne_next D l
    have hs : Sbtw ℝ (D.vertex l) q (D.vertex z) := by
      refine ⟨mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ _ _ hq0), ?_, ?_⟩
      · intro e
        apply hlz
        exact left_mem_openSegment_iff.mp (e ▸ hq0)
      · intro e
        apply hlz.symm
        exact (right_mem_openSegment_iff.mp (e ▸ hq0)).symm
    have hnotLeft : D.vertex l ∉ segment ℝ q (D.vertex z) := by
      exact fun h => hs.not_swap_left (mem_segment_iff_wbtw.mp h)
    have hnotRight : D.vertex z ∉ segment ℝ (D.vertex l) q := by
      exact fun h => hs.not_swap_right (mem_segment_iff_wbtw.mp h)
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ k =>
        rw [finRotate_apply_zero, Fin.cons_zero, finCons_one hn]
        by_cases hk : finRotate D.n k = z
        · have hkl : k = l := (finRotate D.n).injective (hk.trans hl.symm)
          subst k
          rw [finRotate_succ_eq_zero hn l hl, Fin.cons_succ, Fin.cons_zero]
          intro x hx
          have hxq : x = q := by
            have h1 := mem_segment_iff_wbtw.mp hx.1
            have h2 := mem_segment_iff_wbtw.mp hx.2
            exact (h1.swap_left_iff.mp (hs.wbtw.trans_left_right h2)).symm
          subst x
          simp
        · rw [finRotate_succ_ne_zero hn k hk, Fin.cons_succ, Fin.cons_succ]
          intro x hx
          have hlk : l ≠ k := fun e => hk (e ▸ hl)
          have hxold : x ∈ segment ℝ (D.vertex l) (D.vertex (finRotate D.n l)) := by
            simpa [hl] using (convex_segment (D.vertex l) (D.vertex z)).segment_subset
              (mem_segment_iff_wbtw.mpr hs.wbtw) (right_mem_segment ℝ _ _) hx.1
          have hold := D.simple l k hlk ⟨hxold, hx.2⟩
          have hxl : x = D.vertex z := by
            rcases hold.1 with h | h
            · exact (hnotLeft (h ▸ hx.1)).elim
            · simpa [hl] using h
          subst x
          exact ⟨Or.inr rfl, hold.2⟩
    | succ k =>
      induction j using Fin.cases with
      | zero =>
        rw [finRotate_apply_zero, Fin.cons_zero, finCons_one hn]
        by_cases hk : finRotate D.n k = z
        · have hkl : k = l := (finRotate D.n).injective (hk.trans hl.symm)
          subst k
          rw [finRotate_succ_eq_zero hn l hl, Fin.cons_succ, Fin.cons_zero]
          intro x hx
          have hxq : x = q := by
            have h1 := mem_segment_iff_wbtw.mp hx.2
            have h2 := mem_segment_iff_wbtw.mp hx.1
            exact (h1.swap_left_iff.mp (hs.wbtw.trans_left_right h2)).symm
          subst x
          simp
        · rw [finRotate_succ_ne_zero hn k hk, Fin.cons_succ, Fin.cons_succ]
          intro x hx
          have hkl : k ≠ l := fun e => hk (e ▸ hl)
          have hxold : x ∈ segment ℝ (D.vertex l) (D.vertex (finRotate D.n l)) := by
            simpa [hl] using (convex_segment (D.vertex l) (D.vertex z)).segment_subset
              (mem_segment_iff_wbtw.mpr hs.wbtw) (right_mem_segment ℝ _ _) hx.2
          have hold := D.simple k l hkl ⟨hx.1, hxold⟩
          have hxl : x = D.vertex z := by
            rcases hold.2 with h | h
            · exact (hnotLeft (h ▸ hx.2)).elim
            · simpa [hl] using h
          subst x
          exact ⟨hold.1, Or.inr rfl⟩
      | succ m =>
        have hkm : k ≠ m := fun e => hij (congrArg Fin.succ e)
        by_cases hk : finRotate D.n k = z <;>
          by_cases hm : finRotate D.n m = z
        · exact (hkm ((finRotate D.n).injective (hk.trans hm.symm))).elim
        · rw [finRotate_succ_eq_zero hn k hk, finRotate_succ_ne_zero hn m hm]
          simp only [Fin.cons_succ, Fin.cons_zero]
          intro x hx
          have hkl : k = l := (finRotate D.n).injective (hk.trans hl.symm)
          have hqk : q ∈ segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) := by
            simpa [hkl, hl] using mem_segment_iff_wbtw.mpr hs.wbtw
          have hold := D.simple k m hkm ⟨
            (convex_segment (D.vertex k) (D.vertex (finRotate D.n k))).segment_subset
              (left_mem_segment ℝ _ _) hqk hx.1, hx.2⟩
          have hxk : x = D.vertex k := by
            rcases hold.1 with h | h
            · exact h
            · rw [Set.mem_singleton_iff] at h
              have hh : D.vertex (finRotate D.n k) ∈ segment ℝ (D.vertex k) q := h ▸ hx.1
              exact (hnotRight (by simpa [hkl, hl] using hh)).elim
          subst x
          exact ⟨by simp, hold.2⟩
        · rw [finRotate_succ_ne_zero hn k hk, finRotate_succ_eq_zero hn m hm]
          simp only [Fin.cons_succ, Fin.cons_zero]
          intro x hx
          have hml : m = l := (finRotate D.n).injective (hm.trans hl.symm)
          have hqm : q ∈ segment ℝ (D.vertex m) (D.vertex (finRotate D.n m)) := by
            simpa [hml, hl] using mem_segment_iff_wbtw.mpr hs.wbtw
          have hold := D.simple k m hkm ⟨hx.1,
            (convex_segment (D.vertex m) (D.vertex (finRotate D.n m))).segment_subset
              (left_mem_segment ℝ _ _) hqm hx.2⟩
          have hxm : x = D.vertex m := by
            rcases hold.2 with h | h
            · exact h
            · rw [Set.mem_singleton_iff] at h
              have hh : D.vertex (finRotate D.n m) ∈ segment ℝ (D.vertex m) q := h ▸ hx.2
              exact (hnotRight (by simpa [hml, hl] using hh)).elim
          subst x
          exact ⟨hold.1, by simp⟩
        · rw [finRotate_succ_ne_zero hn k hk, finRotate_succ_ne_zero hn m hm]
          simpa only [Fin.cons_succ] using D.simple k m hkm

private lemma polygonalDiskInsertClosing_vertexSet (D : PolygonalDisk) (q : Pt)
    (hq : q ∈ openSegment ℝ
      (D.vertex (polygonalDiskClosing D)) (D.vertex (polygonalDiskZero D))) :
    (polygonalDiskInsertClosing D q hq).vertexSet = insert q D.vertexSet := by
  change Set.range (Fin.cons q D.vertex) = insert q (Set.range D.vertex)
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    induction j using Fin.cases with
    | zero => exact Set.mem_insert _ _
    | succ i =>
      apply Set.mem_insert_of_mem
      refine ⟨i, ?_⟩
      change D.vertex i = (@Fin.cons D.n (fun _ => Pt) q D.vertex) i.succ
      exact (@Fin.cons_succ D.n (fun _ => Pt) q D.vertex i).symm
  · intro hx
    rcases hx with h | ⟨i, hi⟩
    · refine ⟨(0 : Fin (D.n + 1)), ?_⟩
      change (@Fin.cons D.n (fun _ => Pt) q D.vertex) 0 = x
      rw [Fin.cons_zero]
      exact h.symm
    · refine ⟨i.succ, ?_⟩
      change (@Fin.cons D.n (fun _ => Pt) q D.vertex) i.succ = x
      rw [Fin.cons_succ]
      exact hi

private lemma exists_polygonalDisk_insert (D : PolygonalDisk) {q : Pt}
    (hqf : q ∈ frontier D.carrier) (hqv : q ∉ D.vertexSet) :
    ∃ D' : PolygonalDisk, D'.carrier = D.carrier ∧ D'.vertexSet = insert q D.vertexSet := by
  rw [D.frontier_eq] at hqf
  rcases Set.mem_iUnion.1 hqf with ⟨i, hi⟩
  have hiOpen : q ∈ openSegment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) := by
    apply mem_openSegment_of_ne_left_right
    · intro e
      exact hqv ⟨i, e⟩
    · intro e
      exact hqv ⟨finRotate D.n i, e⟩
    · exact hi
  let l := polygonalDiskClosing D
  let e : Equiv.Perm (Fin D.n) := finCycle (i - l)
  have he : ∀ j, e (finRotate D.n j) = finRotate D.n (e j) := by
    intro j
    rw [show e = (finRotate D.n)^[((i - l) : Fin D.n).val] by
      exact finCycle_eq_finRotate_iterate]
    exact ((Function.Commute.refl (finRotate D.n)).iterate_left _).eq j
  have heli : e l = i := by
    simp only [e, finCycle_apply]
    haveI : NeZero D.n := ⟨by have := D.three_le; omega⟩
    rw [add_comm]
    exact sub_add_cancel i l
  let E := polygonalDiskReindex D e he
  have hE : q ∈ openSegment ℝ
      (E.vertex (polygonalDiskClosing E)) (E.vertex (polygonalDiskZero E)) := by
    change q ∈ openSegment ℝ (D.vertex (e (polygonalDiskClosing D)))
      (D.vertex (e (polygonalDiskZero D)))
    rw [show polygonalDiskClosing D = l from rfl, heli]
    have hz : polygonalDiskZero D = finRotate D.n l := by
      exact ((finRotate D.n).apply_symm_apply (polygonalDiskZero D)).symm
    rw [hz, he, heli]
    exact hiOpen
  refine ⟨polygonalDiskInsertClosing E q hE, rfl, ?_⟩
  rw [polygonalDiskInsertClosing_vertexSet]
  exact congrArg (insert q) (polygonalDiskReindex_vertexSet D e he)

private lemma exists_polygonalDisk_refineFinset (D : PolygonalDisk) (s : Finset Pt)
    (hs : ∀ q ∈ s, q ∈ frontier D.carrier) :
    ∃ E : PolygonalDisk, E.carrier = D.carrier ∧ E.vertexSet = D.vertexSet ∪ (s : Set Pt) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨D, rfl, by simp⟩
  | @insert q s hqs ih =>
    obtain ⟨E, hEc, hEv⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
    by_cases hqE : q ∈ E.vertexSet
    · refine ⟨E, hEc, ?_⟩
      rw [hEv]
      ext x
      simp only [Finset.coe_insert, Set.mem_union, Set.mem_insert_iff, Finset.mem_coe]
      constructor
      · intro hx
        exact hx.imp_right (Or.inr ·)
      · rintro (hx | rfl | hx)
        · exact Or.inl hx
        · have ht := hqE
          rw [hEv] at ht
          exact ht
        · exact Or.inr hx
    · obtain ⟨E', hE'c, hE'v⟩ := exists_polygonalDisk_insert E
          (hEc ▸ hs q (Finset.mem_insert_self q s)) hqE
      refine ⟨E', hE'c.trans hEc, ?_⟩
      rw [hE'v, hEv]
      ext x
      simp

private lemma coarsen_vertexSet (D : PolygonalDisk) : D.coarsen.vertexSet = D.genuineCorners := by
  classical
  ext q
  constructor
  · rintro ⟨j, rfl⟩
    have hj := (D.genuineEnum j).2
    simp only [PolygonalDisk.genuineIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨(D.genuineEnum j).1, hj, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    change D.IsGenuineVertex i at hi
    have himem : i ∈ D.genuineIdx := by simp [PolygonalDisk.genuineIdx, hi]
    obtain ⟨j, hj⟩ := D.genuineEnum.surjective ⟨i, himem⟩
    refine ⟨j, ?_⟩
    exact congrArg (fun x : D.genuineIdx => D.vertex x.1) hj

/-- A polygonal disk with the carrier of the selected form and exactly the
clone vertices as listed vertices exists. -/
theorem exists_cloneDisk (c : GenuineCornerClone τ) :
    ∃ D : PolygonalDisk, D.carrier = (P.disk c.form).carrier ∧ D.vertexSet = cloneVertexSet c := by
  classical
  let S := (cloneVertexSet_finite c).toFinset
  have hS : ∀ q ∈ S, q ∈ frontier (P.disk c.form).coarsen.carrier := by
    intro q hq
    exact ((Set.Finite.mem_toFinset (cloneVertexSet_finite c)).mp hq).1
  obtain ⟨D, hDc, hDv⟩ := exists_polygonalDisk_refineFinset (P.disk c.form).coarsen S hS
  refine ⟨D, hDc, ?_⟩
  rw [hDv, coarsen_vertexSet]
  have hSeq : (S : Set Pt) = cloneVertexSet c := by
    ext q
    exact Set.Finite.mem_toFinset (cloneVertexSet_finite c)
  rw [hSeq]
  apply Set.union_eq_right.2
  exact genuineCorners_subset_cloneVertexSet c

/-- The clone disk. -/
def cloneDisk (c : GenuineCornerClone τ) : PolygonalDisk :=
  Classical.choose (exists_cloneDisk c)

theorem cloneDisk_carrier (c : GenuineCornerClone τ) :
    (cloneDisk c).carrier = (P.disk c.form).carrier :=
  (Classical.choose_spec (exists_cloneDisk c)).1

theorem cloneDisk_vertexSet (c : GenuineCornerClone τ) :
    (cloneDisk c).vertexSet = cloneVertexSet c :=
  (Classical.choose_spec (exists_cloneDisk c)).2

variable (τ)

/-- Under FLC there are finitely many clones. -/
theorem GenuineCornerClone.finite_of_flc (h : τ.FLC) : Finite (GenuineCornerClone τ) := by
  have h_fin : (realizedContexts τ).Finite := finite_neighbourhoods τ h
  haveI : Finite (realizedContexts τ) := h_fin.to_subtype
  exact Finite.of_injective (fun c => (⟨(c.form, c.context), c.realized⟩ : realizedContexts τ))
    (fun c₁ c₂ h_eq => by
      cases c₁
      cases c₂
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at h_eq
      rcases h_eq with ⟨h1, h2⟩
      subst h1 h2
      rfl)

/-- Every form has its singleton (order-zero) clone. -/
theorem exists_clone_of_form (p : P.Form) : ∃ c : GenuineCornerClone τ, c.form = p := by
  let A : PlacedTile P := ⟨p, 0⟩
  have hA : A ∈ τ.supertile 0 p := by rfl
  let c : GenuineCornerClone τ := {
    form := p
    context := translateSet (-A.anchor) (neighbourhood (τ.supertile 0 p) A)
    realized := ⟨0, p, A, hA, rfl⟩
  }
  exact ⟨c, rfl⟩

/-- The clone protoset (finite under FLC). -/
def cloneProtoset (h : τ.FLC) : Protoset where
  Form := GenuineCornerClone τ
  fintype := @Fintype.ofFinite _ (GenuineCornerClone.finite_of_flc τ h)
  decEq := Classical.decEq _
  disk := fun c => cloneDisk c

/-- Step 1.1 of the blueprint proof of `childContext_realized`: `translateSet v (translateSet w S) = translateSet (v +ᵥ w) S`. -/
private lemma childContext_realized_step1_shift_step1_translateSet_translateSet
    {P : Protoset} (v w : Pt) (S : Set (PlacedTile P)) :
    translateSet v (translateSet w S) = translateSet (v +ᵥ w) S := by
  ext x
  simp only [translateSet, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    use z, hz
    apply PlacedTile.ext
    · rfl
    · dsimp [PlacedTile.translate, VAdd.vadd]
      abel
  · rintro ⟨y, hy, rfl⟩
    use y.translate w
    constructor
    · use y, hy
    · apply PlacedTile.ext
      · rfl
      · dsimp [PlacedTile.translate, VAdd.vadd]
        abel

/-- Step 1.2 of the blueprint proof of `childContext_realized`: `τ.decompose (translateSet v S) = translateSet (τ.θ • v) (τ.decompose S)`. -/
private lemma childContext_realized_step1_shift_step2_decompose_translateSet
    {P : Protoset} {τ : Substitution P} (v : Pt) (S : Set (PlacedTile P)) :
    τ.decompose (translateSet v S) = translateSet (τ.θ • v) (τ.decompose S) := by
  have hstep : ∀ B : PlacedTile P,
      τ.decomposeTile (B.translate v) = translateSet (τ.θ • v) (τ.decomposeTile B) := by
    intro B
    show translateSet (τ.θ • (v +ᵥ B.anchor)) (τ.rule B.form).tiles =
        translateSet (τ.θ • v) (translateSet (τ.θ • B.anchor) (τ.rule B.form).tiles)
    rw [childContext_realized_step1_shift_step1_translateSet_translateSet]
    congr 1
    change τ.θ • (v + B.anchor) = τ.θ • v + τ.θ • B.anchor
    rw [smul_add]
  show (⋃ A ∈ translateSet v S, τ.decomposeTile A) =
      (fun A : PlacedTile P => A.translate (τ.θ • v)) '' ⋃ B ∈ S, τ.decomposeTile B
  rw [show translateSet v S = (fun A : PlacedTile P => A.translate v) '' S from rfl,
    Set.biUnion_image, Set.image_iUnion₂]
  exact Set.iUnion₂_congr fun B _ => hstep B

/-- Step 1.3 of the blueprint proof of `childContext_realized`: `τ.supertile (n+1) p = τ.decompose (τ.supertile n p)`. -/
private lemma childContext_realized_step1_shift_step3_supertile_succ
    {P : Protoset} {τ : Substitution P} (n : ℕ) (p : P.Form) :
    τ.supertile (n+1) p = τ.decompose (τ.supertile n p) := rfl

/-- Step 1.4 of the blueprint proof of `childContext_realized`: Anchor arithmetic. -/
private lemma childContext_realized_step1_shift_step4_anchor
    {P : Protoset} {τ : Substitution P} (A B : PlacedTile P) :
    -B.anchor +ᵥ τ.θ • -A.anchor = -(B.translate (τ.θ • A.anchor)).anchor := by
  change -B.anchor + τ.θ • -A.anchor = -(τ.θ • A.anchor + B.anchor)
  rw [smul_neg]
  abel

/-- Step 1.5 of the blueprint proof of `childContext_realized`: Translate arithmetic. -/
private lemma childContext_realized_step1_shift_step5_translate_eq
    {P : Protoset} {τ : Substitution P} (A B : PlacedTile P) :
    B.translate (-(τ.θ • -A.anchor)) = B.translate (τ.θ • A.anchor) := by
  congr 1
  simp only [neg_neg, smul_neg]

/-- Step 1.6 of the blueprint proof of `childContext_realized`: `neighbourhood (translateSet v S) A = translateSet v (neighbourhood S (A.translate (-v)))` -/
private lemma childContext_realized_step1_shift_step6_neighbourhood_translateSet
    {P : Protoset} (v : Pt) (S : Set (PlacedTile P)) (A : PlacedTile P) :
    neighbourhood (translateSet v S) A = translateSet v (neighbourhood S (A.translate (-v))) := by
  ext B
  simp only [neighbourhood, translateSet, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨C, hC_in_S, rfl⟩, h_nonempty⟩
    refine ⟨C, ⟨hC_in_S, ?_⟩, rfl⟩
    rcases h_nonempty with ⟨p, hp_A, hp_Cv⟩
    dsimp [PlacedTile.carrier, PlacedTile.translate] at hp_A hp_Cv ⊢
    rcases hp_A with ⟨d1, hd1, hp_A_eq⟩
    rcases hp_Cv with ⟨d2, hd2, hp_Cv_eq⟩
    use p -ᵥ v
    constructor
    · use d1
      refine ⟨hd1, ?_⟩
      dsimp
      rw [←hp_A_eq]
      change (-v + A.anchor) + d1 = A.anchor + d1 - v
      abel
    · use d2
      refine ⟨hd2, ?_⟩
      dsimp
      rw [←hp_Cv_eq]
      change C.anchor + d2 = (v + C.anchor) + d2 - v
      abel
  · rintro ⟨C, ⟨hC_in_S, h_nonempty⟩, rfl⟩
    refine ⟨⟨C, hC_in_S, rfl⟩, ?_⟩
    rcases h_nonempty with ⟨p, hp_Av, hp_C⟩
    dsimp [PlacedTile.carrier, PlacedTile.translate] at hp_Av hp_C ⊢
    rcases hp_Av with ⟨d1, hd1, hp_Av_eq⟩
    rcases hp_C with ⟨d2, hd2, hp_C_eq⟩
    use p +ᵥ v
    constructor
    · use d1
      refine ⟨hd1, ?_⟩
      dsimp
      rw [←hp_Av_eq]
      change A.anchor + d1 = (-v + A.anchor) + d1 + v
      abel
    · use d2
      refine ⟨hd2, ?_⟩
      dsimp
      rw [←hp_C_eq]
      change (v + C.anchor) + d2 = C.anchor + d2 + v
      abel


private lemma childContext_realized_step1_shift_step7_decompose_neighbourhood_step1_nonempty_aux1
    {P : Protoset} (v : Pt) (S : Set (PlacedTile P)) :
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

private lemma childContext_realized_step1_shift_step7_decompose_neighbourhood_step1_nonempty_aux2
    {P : Protoset} {τ : Substitution P} (A : PlacedTile P) :
    support (τ.decomposeTile A) = τ.θ • A.carrier := by
  dsimp [Substitution.decomposeTile]
  rw [childContext_realized_step1_shift_step7_decompose_neighbourhood_step1_nonempty_aux1]
  rw [τ.support_eq, PlacedTile.carrier]
  ext x
  simp only [mem_vadd_set_iff_neg_vadd_mem, mem_smul_set, vadd_eq_add]
  constructor
  · rintro ⟨y, hy, hx⟩
    refine ⟨A.anchor + y, ?_, ?_⟩
    · simpa
    · rw [smul_add]
      rw [hx]
      abel
  · rintro ⟨y, hy, hx⟩
    refine ⟨-A.anchor + y, ?_, ?_⟩
    · simpa
    · rw [smul_add, smul_neg, hx]

/-- Step 1 of the blueprint proof of `childContext_realized_step1_shift_step7_decompose_neighbourhood`:
If `B ∈ τ.decomposeTile A` and `C ∈ τ.decomposeTile D` intersect, then `A` and `D` intersect. -/
private lemma childContext_realized_step1_shift_step7_decompose_neighbourhood_step1_nonempty
    {P : Protoset} {τ : Substitution P} (A B C D : PlacedTile P)
    (hB : B ∈ τ.decomposeTile A) (hC : C ∈ τ.decomposeTile D)
    (h_int : (B.carrier ∩ C.carrier).Nonempty) :
    (A.carrier ∩ D.carrier).Nonempty := by
  have h_B_supp : B.carrier ⊆ support (τ.decomposeTile A) := by
    intros x hx
    simp only [support, mem_iUnion, exists_prop]
    exact ⟨B, hB, hx⟩
  have h_C_supp : C.carrier ⊆ support (τ.decomposeTile D) := by
    intros x hx
    simp only [support, mem_iUnion, exists_prop]
    exact ⟨C, hC, hx⟩
  rw [childContext_realized_step1_shift_step7_decompose_neighbourhood_step1_nonempty_aux2 A]
    at h_B_supp
  rw [childContext_realized_step1_shift_step7_decompose_neighbourhood_step1_nonempty_aux2 D]
    at h_C_supp
  rcases h_int with ⟨x, hx_B, hx_C⟩
  have hx_A := h_B_supp hx_B
  have hx_D := h_C_supp hx_C
  simp only [mem_smul_set] at hx_A hx_D
  rcases hx_A with ⟨yA, hyA, hyA_eq⟩
  rcases hx_D with ⟨yD, hyD, hyD_eq⟩
  have heq : τ.θ • yA = τ.θ • yD := by rw [hyA_eq, hyD_eq]
  have hy_eq : yA = yD := by
    have hθ : τ.θ ≠ 0 := by linarith [τ.one_lt]
    exact smul_right_injective _ hθ heq
  refine ⟨yA, hyA, ?_⟩
  rw [hy_eq]
  exact hyD

/-- Step 1.7 of the blueprint proof of `childContext_realized`: `τ.decompose (neighbourhood S A) = ...` -/
private lemma childContext_realized_step1_shift_step7_decompose_neighbourhood
    {P : Protoset} {τ : Substitution P} (S : Set (PlacedTile P)) (A B : PlacedTile P)
    (hB : B ∈ τ.decomposeTile A) :
    neighbourhood (τ.decompose (neighbourhood S A)) B = neighbourhood (τ.decompose S) B := by
  ext C
  simp only [neighbourhood, decompose, mem_setOf_eq, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨⟨D, ⟨hD_mem, hD_int⟩, hC_mem⟩, h_int⟩
    exact ⟨⟨D, hD_mem, hC_mem⟩, h_int⟩
  · rintro ⟨⟨D, hD_mem, hC_mem⟩, h_int⟩
    refine ⟨⟨D, ⟨hD_mem, ?_⟩, hC_mem⟩, h_int⟩
    exact childContext_realized_step1_shift_step7_decompose_neighbourhood_step1_nonempty A B C D hB hC_mem h_int

/-- Step 1.8 of the blueprint proof of `childContext_realized`: `B ∈ τ.decomposeTile ⟨c.form, 0⟩ → B.translate (τ.θ • A.anchor) ∈ τ.decomposeTile A` -/
private lemma childContext_realized_step1_shift_step8_translate_mem
    {P : Protoset} {τ : Substitution P} (A B : PlacedTile P)
    (hB : B ∈ τ.decomposeTile ⟨A.form, 0⟩) :
    B.translate (τ.θ • A.anchor) ∈ τ.decomposeTile A := by
  dsimp [Substitution.decomposeTile, translateSet] at *
  rcases hB with ⟨C, hC, hCeq⟩
  use C
  refine ⟨hC, ?_⟩
  dsimp
  rw [← hCeq]
  dsimp [PlacedTile.translate]
  ext
  · rfl
  · simp

/-- Step 1 of the blueprint proof of `childContext_realized`: shifting contexts. -/


private lemma childContext_realized_step1_shift {τ : Substitution P} (c : GenuineCornerClone τ)
    (B : PlacedTile P) (hB : B ∈ τ.decomposeTile ⟨c.form, 0⟩) (n : ℕ) (p : P.Form)
    (A : PlacedTile P) (hform : c.form = A.form) (hA : A ∈ τ.supertile n p)
    (hctx : c.context = translateSet (-A.anchor) (neighbourhood (τ.supertile n p) A)) :
    translateSet (-B.anchor) (neighbourhood (τ.decompose c.context) B) =
      translateSet (-(B.translate (τ.θ • A.anchor)).anchor)
        (neighbourhood (τ.supertile (n+1) p) (B.translate (τ.θ • A.anchor))) := by
  have _ := hA
  rw [hctx, childContext_realized_step1_shift_step2_decompose_translateSet]
  rw [childContext_realized_step1_shift_step6_neighbourhood_translateSet]
  rw [childContext_realized_step1_shift_step1_translateSet_translateSet]
  rw [childContext_realized_step1_shift_step3_supertile_succ]
  rw [childContext_realized_step1_shift_step4_anchor]
  rw [childContext_realized_step1_shift_step5_translate_eq]
  congr 1
  apply childContext_realized_step1_shift_step7_decompose_neighbourhood
  apply childContext_realized_step1_shift_step8_translate_mem A B
  rw [←hform]
  exact hB

/-- Step 2 of the blueprint proof of `childContext_realized`: the translated child tile belongs to
the supertile of order n+1. -/
private lemma childContext_realized_step2_A_prime {τ : Substitution P} (c : GenuineCornerClone τ)
    (B : PlacedTile P) (hB : B ∈ τ.decomposeTile ⟨c.form, 0⟩) (n : ℕ) (p : P.Form)
    (A : PlacedTile P) (hform : c.form = A.form) (hA : A ∈ τ.supertile n p) :
    B.translate (τ.θ • A.anchor) ∈ τ.supertile (n+1) p := by
  have H : τ.supertile (n+1) p = ⋃ X ∈ τ.supertile n p, τ.decomposeTile X := rfl
  rw [H]
  simp only [Set.mem_iUnion, exists_prop]
  use A, hA
  have h_dec : τ.decomposeTile A = translateSet (τ.θ • A.anchor) (τ.rule A.form).tiles := rfl
  rw [h_dec]
  have h_dec2 : τ.decomposeTile ⟨c.form, 0⟩ = translateSet (τ.θ • (0:Pt)) (τ.rule c.form).tiles := rfl
  rw [h_dec2] at hB
  rw [smul_zero] at hB
  have hts0 : translateSet (0:Pt) (τ.rule c.form).tiles = (τ.rule c.form).tiles := by
    ext X; simp [translateSet, PlacedTile.translate]
  rw [hts0] at hB
  rw [← hform]
  exact ⟨B, hB, rfl⟩

/-- A child `B` of the selected tile receives the context `(τ S_A)_B`, which is
again realized. -/
theorem childContext_realized (c : GenuineCornerClone τ) (B : PlacedTile P)
    (hB : B ∈ τ.decomposeTile ⟨c.form, 0⟩) :
    (B.form, translateSet (-B.anchor) (neighbourhood (τ.decompose c.context) B)) ∈
      realizedContexts τ := by
  rcases c.realized with ⟨n, p, A, hA, hctx_eq⟩
  have hform : c.form = A.form := congr_arg Prod.fst hctx_eq
  have hctx : c.context =
      translateSet (-A.anchor) (neighbourhood (τ.supertile n p) A) :=
    congr_arg Prod.snd hctx_eq
  let A' := B.translate (τ.θ • A.anchor)
  have hA' : A' ∈ τ.supertile (n+1) p := childContext_realized_step2_A_prime c B hB n p A hform hA
  have hctx' : translateSet (-B.anchor) (neighbourhood (τ.decompose c.context) B) =
    translateSet (-A'.anchor) (neighbourhood (τ.supertile (n+1) p) A') :=
    childContext_realized_step1_shift c B hB n p A hform hA hctx
  use n + 1, p, A', hA'
  rw [hctx']
  rfl

/-- The child clone `(B, (τ S_A)_B)`. -/
def childClone (c : GenuineCornerClone τ) (B : PlacedTile P)
    (hB : B ∈ τ.decomposeTile ⟨c.form, 0⟩) : GenuineCornerClone τ :=
  ⟨B.form, translateSet (-B.anchor) (neighbourhood (τ.decompose c.context) B),
    childContext_realized τ c B hB⟩

/-- The tiles of the refined rule patch of a clone. -/
def refinedRule (h : τ.FLC) (c : GenuineCornerClone τ) :
    Set (PlacedTile (cloneProtoset τ h)) :=
  {X | ∃ (B : PlacedTile P) (hB : B ∈ τ.decomposeTile ⟨c.form, 0⟩),
    X = (⟨childClone τ c B hB, B.anchor⟩ : PlacedTile (cloneProtoset τ h))}
private lemma refinedSubstitution_carrier_eq (h : τ.FLC) (c : GenuineCornerClone τ)
    (B : PlacedTile P) (hB : B ∈ τ.decomposeTile ⟨c.form, 0⟩) :
    (⟨childClone τ c B hB, B.anchor⟩ : PlacedTile (cloneProtoset τ h)).carrier = B.carrier := by
  dsimp [PlacedTile.carrier]
  congr 1
  exact cloneDisk_carrier _

private lemma support_translateSet (v : Pt) (S : Set (PlacedTile P)) :
    support (translateSet v S) = v +ᵥ support S := by
  dsimp [support, translateSet, PlacedTile.translate, PlacedTile.carrier]
  ext x
  simp only [mem_iUnion, mem_image, mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨A', ⟨A, hA, rfl⟩, y, hy, rfl⟩
    refine ⟨y + A.anchor, ⟨A, hA, y, hy, add_comm _ _⟩, ?_⟩
    change v + (y + A.anchor) = (v + A.anchor) + y
    rw [add_assoc, add_comm y A.anchor, ← add_assoc]
  · rintro ⟨z, ⟨A, hA, y, hy, rfl⟩, rfl⟩
    refine ⟨_, ⟨A, hA, rfl⟩, y, hy, ?_⟩
    change (v + A.anchor) + y = v + (A.anchor + y)
    exact (add_assoc (v:Pt) A.anchor y)

private lemma disjointInteriors_translate (v : Pt) (S : Set (PlacedTile P))
    (hd : DisjointInteriors S) : DisjointInteriors (translateSet v S) := by
  intro A hA B hB hAB
  simp only [translateSet, mem_image] at hA hB
  rcases hA with ⟨A', hA', rfl⟩
  rcases hB with ⟨B', hB', rfl⟩
  have hne : A' ≠ B' := by
    rintro rfl
    exact hAB rfl
  have hd' := hd hA' hB' hne
  dsimp [Function.onFun] at hd' ⊢
  have h_carrA : (A'.translate v).carrier = v +ᵥ A'.carrier := by
    dsimp [PlacedTile.translate, PlacedTile.carrier]
    ext x
    simp only [mem_vadd_set, vadd_eq_add]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y + A'.anchor, ⟨y, hy, add_comm _ _⟩, by abel⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, by abel⟩
  have h_carrB : (B'.translate v).carrier = v +ᵥ B'.carrier := by
    dsimp [PlacedTile.translate, PlacedTile.carrier]
    ext x
    simp only [mem_vadd_set, vadd_eq_add]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y + B'.anchor, ⟨y, hy, add_comm _ _⟩, by abel⟩
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, by abel⟩
  rw [h_carrA, h_carrB]
  rw [interior_vadd, interior_vadd]
  exact disjoint_image_of_injective (AddAction.injective v) hd'

private lemma refinedSubstitution_disjoint (h : τ.FLC) (c : GenuineCornerClone τ) :
    DisjointInteriors (refinedRule τ h c) := by
  intro X hX Y hY hXY
  simp only [refinedRule, mem_setOf_eq] at hX hY
  rcases hX with ⟨B_X, hB_X, rfl⟩
  rcases hY with ⟨B_Y, hB_Y, rfl⟩
  have hcX := @refinedSubstitution_carrier_eq P τ h c B_X hB_X
  have hcY := @refinedSubstitution_carrier_eq P τ h c B_Y hB_Y
  dsimp [Function.onFun]
  rw [hcX, hcY]
  have hne : B_X ≠ B_Y := by
    rintro rfl
    exact hXY rfl
  have hd : DisjointInteriors (τ.decomposeTile ⟨c.form, 0⟩) := by
    dsimp [decomposeTile]
    exact disjointInteriors_translate _ _ (τ.rule c.form).disjoint
  exact hd hB_X hB_Y hne

private lemma refinedSubstitution_finite (h : τ.FLC) (c : GenuineCornerClone τ) :
    (refinedRule τ h c).Finite := by
  let f : {B : PlacedTile P // B ∈ τ.decomposeTile ⟨c.form, 0⟩} → PlacedTile (cloneProtoset τ h) :=
    fun ⟨B, hB⟩ => ⟨childClone τ c B hB, B.anchor⟩
  have h_eq : refinedRule τ h c = range f := by
    ext X
    simp only [refinedRule, mem_setOf_eq, mem_range, Subtype.exists]
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact ⟨B, hB, rfl⟩
    · rintro ⟨B, hB, rfl⟩
      exact ⟨B, hB, rfl⟩
  rw [h_eq]
  have h_fin : (τ.decomposeTile ⟨c.form, (0 : Pt)⟩).Finite := by
    dsimp [decomposeTile]
    exact (τ.rule c.form).finite.image _
  haveI : Fintype {B : PlacedTile P // B ∈ τ.decomposeTile ⟨c.form, 0⟩} := h_fin.fintype
  exact finite_range f

private lemma refinedSubstitution_support_eq (h : τ.FLC) (c : GenuineCornerClone τ) :
    support (refinedRule τ h c) = τ.θ • ((cloneProtoset τ h).disk c).carrier := by
  have h_supp : support (refinedRule τ h c) = support (τ.decomposeTile ⟨c.form, 0⟩) := by
    dsimp [support]
    ext x
    simp only [mem_iUnion, refinedRule, mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨_, ⟨B, hB, rfl⟩, hX⟩
      have H1 := @refinedSubstitution_carrier_eq P τ h c B hB
      exact ⟨B, hB, H1 ▸ hX⟩
    · rintro ⟨B, hB, hB'⟩
      have H2 := @refinedSubstitution_carrier_eq P τ h c B hB
      exact ⟨_, ⟨B, hB, rfl⟩, H2.symm ▸ hB'⟩
  rw [h_supp]
  have h_decomp : support (τ.decomposeTile ⟨c.form, (0:Pt)⟩) = τ.θ • (P.disk c.form).carrier := by
    dsimp [decomposeTile]
    have h_rule := τ.support_eq c.form
    rw [support_translateSet]
    rw [h_rule]
    change τ.θ • (0:Pt) +ᵥ _ = _
    rw [smul_zero, zero_vadd]
  rw [h_decomp]
  congr 1
  exact (cloneDisk_carrier c).symm


/-- `def:clones`: the clone (refined) substitution. -/
def refinedSubstitution (h : τ.FLC) : Substitution (cloneProtoset τ h) where
  θ := τ.θ
  one_lt := τ.one_lt
  rule := fun c : GenuineCornerClone τ =>
    { tiles := refinedRule τ h c
      finite := @refinedSubstitution_finite P τ h c
      disjoint := @refinedSubstitution_disjoint P τ h c }
  support_eq := @refinedSubstitution_support_eq P τ h

/-- Forgetting clone labels: a carrier-preserving decoration of `P`. -/
def cloneDecoration (h : τ.FLC) : Decoration P where
  P' := cloneProtoset τ h
  proj := fun c : GenuineCornerClone τ => c.form
  surj := fun p => by
    obtain ⟨c, hc⟩ := exists_clone_of_form τ p
    exact ⟨c, hc⟩
  carrier_eq := fun c : GenuineCornerClone τ => cloneDisk_carrier c

/-! ## `lem:clone-sts` -/

private theorem refinedSubstitution_commutes_translateSet_eq {P : Protoset}
    (v : Pt) (S : Set (PlacedTile P)) :
    translateSet v S = (fun A => A.translate v) '' S := rfl

private theorem refinedSubstitution_commutes_translate_zero_pt {P : Protoset}
    (A : PlacedTile P) : A.translate 0 = A := by
  change ⟨A.form, (0:Pt) +ᵥ A.anchor⟩ = A
  rw [zero_vadd Pt A.anchor]

/-- `lem:clone-sts` (commutation): the clone substitution commutes with
forgetting labels. -/
theorem refinedSubstitution_commutes (h : τ.FLC)
    (S : Set (PlacedTile (cloneProtoset τ h))) :
    (cloneDecoration τ h).projTile '' ((refinedSubstitution τ h).decompose S) =
      τ.decompose ((cloneDecoration τ h).projTile '' S) := by
  ext B
  simp only [Substitution.decompose, mem_image, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨X, ⟨A, hA_S, hX_decA⟩, rfl⟩
    simp only [Substitution.decomposeTile, refinedSubstitution_commutes_translateSet_eq,
      refinedSubstitution, mem_image] at hX_decA
    rcases hX_decA with ⟨Y, hY_rule, rfl⟩
    simp only [refinedRule, mem_setOf_eq] at hY_rule
    rcases hY_rule with ⟨B', hB'_dec, rfl⟩
    simp only [Substitution.decomposeTile, refinedSubstitution_commutes_translateSet_eq,
      smul_zero, mem_image] at hB'_dec
    rcases hB'_dec with ⟨B'', hB''_rule, hB'_eq⟩
    use (cloneDecoration τ h).projTile A
    constructor
    · exact ⟨A, hA_S, rfl⟩
    · simp only [Substitution.decomposeTile, refinedSubstitution_commutes_translateSet_eq,
        mem_image]
      use B''
      constructor
      · exact hB''_rule
      · simp only [Decoration.projTile, cloneDecoration, PlacedTile.translate, childClone]
        subst hB'_eq
        rw [refinedSubstitution_commutes_translate_zero_pt]
  · rintro ⟨A_proj, ⟨A, hA_S, rfl⟩, hB_dec⟩
    simp only [Substitution.decomposeTile, refinedSubstitution_commutes_translateSet_eq,
      mem_image] at hB_dec
    rcases hB_dec with ⟨B'', hB''_rule, rfl⟩
    have hB'_dec : B'' ∈ τ.decomposeTile ⟨A.form.form, 0⟩ := by
      simp only [Substitution.decomposeTile, refinedSubstitution_commutes_translateSet_eq,
        smul_zero, mem_image]
      use B''
      exact ⟨hB''_rule, refinedSubstitution_commutes_translate_zero_pt B''⟩
    use (⟨childClone τ A.form B'' hB'_dec, B''.anchor⟩ :
      PlacedTile (cloneProtoset τ h)).translate (τ.θ • A.anchor)
    constructor
    · use A
      constructor
      · exact hA_S
      · simp only [Substitution.decomposeTile, refinedSubstitution_commutes_translateSet_eq,
          mem_image, refinedSubstitution]
        use ⟨childClone τ A.form B'' hB'_dec, B''.anchor⟩
        constructor
        · simp only [refinedRule, mem_setOf_eq]
          use B''
          exact ⟨hB'_dec, rfl⟩
        · rfl
    · rfl

/-- Auxiliary: translation commutes with `frontier` on the plane. -/
private lemma refinedSubstitution_sts_step1_visible_vertices_aux_frontier_vadd
    (v : Pt) (s : Set Pt) : frontier (v +ᵥ s) = v +ᵥ frontier s := by
  simp only [frontier, closure_vadd, interior_vadd, vadd_set_sdiff]

/-- Auxiliary: every listed side of a placed tile lies in the frontier of its carrier. -/
private lemma refinedSubstitution_sts_step1_visible_vertices_aux_side_subset_frontier
    (A : PlacedTile P) (i : Fin (P.disk A.form).n) : A.side i ⊆ frontier A.carrier := by
  have hD : (P.disk A.form).side i ⊆ frontier (P.disk A.form).carrier := by
    rw [(P.disk A.form).frontier_eq]
    exact Set.subset_iUnion (fun j => segment ℝ ((P.disk A.form).vertex j)
      ((P.disk A.form).vertex (finRotate (P.disk A.form).n j))) i
  show A.anchor +ᵥ (P.disk A.form).side i ⊆ frontier (A.anchor +ᵥ (P.disk A.form).carrier)
  rw [refinedSubstitution_sts_step1_visible_vertices_aux_frontier_vadd]
  exact image_mono hD

/-- Auxiliary: the genuine corners recorded for a placed tile lie in its carrier. -/
private lemma refinedSubstitution_sts_step1_visible_vertices_aux_genuineCorners_subset_carrier
    (D : PlacedTile P) : tileGenuineCorners D ⊆ D.carrier := by
  rintro y ⟨z, ⟨i, -, rfl⟩, rfl⟩
  show D.anchor +ᵥ (P.disk D.form).vertex i ∈ D.anchor +ᵥ (P.disk D.form).carrier
  refine ⟨(P.disk D.form).vertex i, ?_, rfl⟩
  apply (P.disk D.form).compact.isClosed.frontier_subset
  rw [(P.disk D.form).frontier_eq]
  exact Set.mem_iUnion.mpr ⟨i, left_mem_segment ℝ _ _⟩

/-- Step 1 of the blueprint proof of `refinedSubstitution_sts_step1_visible_vertices`:
touching children have touching original parents, so the full one-ring context of a clone
determines every child context; iterating the decomposition realizes a clone's own private
witness context as the actual neighbourhood of a translated copy of a placed tile inside a
single ambient supertile of `τ`, common to every clone tile of the same supertile order `n`
on the same clone form `c`. -/
private lemma refinedSubstitution_sts_step1_visible_vertices_step1_common_witness
    (h : τ.FLC) (n : ℕ) (c : (cloneProtoset τ h).Form) :
    ∃ (m : ℕ) (q : P.Form) (s : Pt), ∀ A ∈ (refinedSubstitution τ h).supertile n c,
      ∃ Ahat : PlacedTile P, Ahat ∈ τ.supertile m q ∧ Ahat.form = A.form.form ∧
        A.anchor = s +ᵥ Ahat.anchor ∧
        A.vertexSet = s +ᵥ (frontier Ahat.carrier ∩
          ⋃ D ∈ neighbourhood (τ.supertile m q) Ahat, tileGenuineCorners D) := by
  sorry

/-- Step 1 of the blueprint proof of `refinedSubstitution_sts`: On overlapping sides
of clone-supertile members, endpoints and further cuts are genuine vertices of underlying
incident carriers visible in both contexts. Thus the sets of listed vertices on the
intersection of two overlapping sides are the same. -/
private lemma refinedSubstitution_sts_step1_visible_vertices (h : τ.FLC)
    (n : ℕ) (c : (cloneProtoset τ h).Form)
    (A B : PlacedTile (cloneProtoset τ h))
    (hA : A ∈ (refinedSubstitution τ h).supertile n c)
    (hB : B ∈ (refinedSubstitution τ h).supertile n c)
    (i : Fin ((cloneProtoset τ h).disk A.form).n)
    (j : Fin ((cloneProtoset τ h).disk B.form).n)
    (h_overlap : OverlapPos (A.side i) (B.side j)) :
    A.vertexSet ∩ (A.side i ∩ B.side j) = B.vertexSet ∩ (A.side i ∩ B.side j) := by
  have _ := h_overlap
  obtain ⟨m, q, s, hwit⟩ :=
    refinedSubstitution_sts_step1_visible_vertices_step1_common_witness _ h n c
  obtain ⟨Ahat, hAhatmem, hAhatform, hAanchor, hAvs⟩ := hwit A hA
  obtain ⟨Bhat, hBhatmem, hBhatform, hBanchor, hBvs⟩ := hwit B hB
  have hAcarrier : A.carrier = s +ᵥ Ahat.carrier := by
    show A.anchor +ᵥ (cloneDisk A.form).carrier = s +ᵥ Ahat.carrier
    rw [cloneDisk_carrier, ← hAhatform, hAanchor]
    show (s +ᵥ Ahat.anchor) +ᵥ (P.disk Ahat.form).carrier =
      s +ᵥ (Ahat.anchor +ᵥ (P.disk Ahat.form).carrier)
    rw [vadd_vadd, vadd_eq_add]
  have hBcarrier : B.carrier = s +ᵥ Bhat.carrier := by
    show B.anchor +ᵥ (cloneDisk B.form).carrier = s +ᵥ Bhat.carrier
    rw [cloneDisk_carrier, ← hBhatform, hBanchor]
    show (s +ᵥ Bhat.anchor) +ᵥ (P.disk Bhat.form).carrier =
      s +ᵥ (Bhat.anchor +ᵥ (P.disk Bhat.form).carrier)
    rw [vadd_vadd, vadd_eq_add]
  have hAside : A.side i ⊆ s +ᵥ frontier Ahat.carrier := by
    have hh := refinedSubstitution_sts_step1_visible_vertices_aux_side_subset_frontier A i
    rwa [hAcarrier, refinedSubstitution_sts_step1_visible_vertices_aux_frontier_vadd] at hh
  have hBside : B.side j ⊆ s +ᵥ frontier Bhat.carrier := by
    have hh := refinedSubstitution_sts_step1_visible_vertices_aux_side_subset_frontier B j
    rwa [hBcarrier, refinedSubstitution_sts_step1_visible_vertices_aux_frontier_vadd] at hh
  have hcore : ∀ p, p ∈ A.side i → p ∈ B.side j → (p ∈ A.vertexSet ↔ p ∈ B.vertexSet) := by
    intro p hp1 hp2
    have hyA : (-s +ᵥ p) ∈ frontier Ahat.carrier := by
      have hh := hAside hp1
      rwa [mem_vadd_set_iff_neg_vadd_mem] at hh
    have hyB : (-s +ᵥ p) ∈ frontier Bhat.carrier := by
      have hh := hBside hp2
      rwa [mem_vadd_set_iff_neg_vadd_mem] at hh
    have hyA' : (-s +ᵥ p) ∈ Ahat.carrier :=
      (IsCompact.vadd Ahat.anchor (P.disk Ahat.form).compact).isClosed.frontier_subset hyA
    have hyB' : (-s +ᵥ p) ∈ Bhat.carrier :=
      (IsCompact.vadd Bhat.anchor (P.disk Bhat.form).compact).isClosed.frontier_subset hyB
    rw [hAvs, hBvs, mem_vadd_set_iff_neg_vadd_mem, mem_vadd_set_iff_neg_vadd_mem]
    simp only [mem_inter_iff, mem_iUnion₂]
    constructor
    · rintro ⟨-, D, hDmem, hyD⟩
      have hDcarrier : (-s +ᵥ p) ∈ D.carrier :=
        refinedSubstitution_sts_step1_visible_vertices_aux_genuineCorners_subset_carrier D hyD
      have hDnbhdB : D ∈ neighbourhood (τ.supertile m q) Bhat := by
        simp only [neighbourhood, mem_setOf_eq]
        exact ⟨hDmem.1, -s +ᵥ p, hyB', hDcarrier⟩
      exact ⟨hyB, D, hDnbhdB, hyD⟩
    · rintro ⟨-, D, hDmem, hyD⟩
      have hDcarrier : (-s +ᵥ p) ∈ D.carrier :=
        refinedSubstitution_sts_step1_visible_vertices_aux_genuineCorners_subset_carrier D hyD
      have hDnbhdA : D ∈ neighbourhood (τ.supertile m q) Ahat := by
        simp only [neighbourhood, mem_setOf_eq]
        exact ⟨hDmem.1, -s +ᵥ p, hyA', hDcarrier⟩
      exact ⟨hyA, D, hDnbhdA, hyD⟩
  ext p
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨hv, h1, h2⟩
    exact ⟨(hcore p h1 h2).mp hv, h1, h2⟩
  · rintro ⟨hv, h1, h2⟩
    exact ⟨(hcore p h1 h2).mpr hv, h1, h2⟩

/-- Step 1 of the blueprint proof of `refinedSubstitution_sts_step2_sides_eq`: the side endpoint intersections with the overlapping segments are equal. -/
private lemma refinedSubstitution_sts_step2_sides_eq_step1_inter_eq (h : τ.FLC)
    (A B : PlacedTile (cloneProtoset τ h))
    (i : Fin ((cloneProtoset τ h).disk A.form).n)
    (j : Fin ((cloneProtoset τ h).disk B.form).n)
    (h_same_verts : A.vertexSet ∩ (A.side i ∩ B.side j) = B.vertexSet ∩ (A.side i ∩ B.side j)) :
    {A.vertex i, A.vertex (finRotate _ i)} ∩ B.side j = {B.vertex j, B.vertex (finRotate _ j)} ∩ A.side i := by
  sorry

/-- Step 2 of the blueprint proof of `refinedSubstitution_sts_step2_sides_eq`: if the side
endpoint intersections with the overlapping segments are equal, and the segments overlap with
positive length, then the segments are identical. -/
private lemma refinedSubstitution_sts_step2_sides_eq_step2_segment_eq (h : τ.FLC)
    (A B : PlacedTile (cloneProtoset τ h))
    (i : Fin ((cloneProtoset τ h).disk A.form).n)
    (j : Fin ((cloneProtoset τ h).disk B.form).n)
    (h_overlap : OverlapPos (A.side i) (B.side j))
    (h_inter_eq : {A.vertex i, A.vertex (finRotate _ i)} ∩ B.side j = {B.vertex j, B.vertex (finRotate _ j)} ∩ A.side i) :
    A.side i = B.side j := by
  sorry

/-- Step 2 of the blueprint proof of `refinedSubstitution_sts`: Since the resulting
subdivision agrees on both sides (the sets of listed vertices on the intersection are
the same), overlapping sides must be exactly equal, proving clone-supertiles STS. -/
private lemma refinedSubstitution_sts_step2_sides_eq (h : τ.FLC)
    (A B : PlacedTile (cloneProtoset τ h))
    (i : Fin ((cloneProtoset τ h).disk A.form).n)
    (j : Fin ((cloneProtoset τ h).disk B.form).n)
    (h_overlap : OverlapPos (A.side i) (B.side j))
    (h_same_verts : A.vertexSet ∩ (A.side i ∩ B.side j) = B.vertexSet ∩ (A.side i ∩ B.side j)) :
    A.side i = B.side j := by
  exact refinedSubstitution_sts_step2_sides_eq_step2_segment_eq τ h A B i j h_overlap
    (refinedSubstitution_sts_step2_sides_eq_step1_inter_eq τ h A B i j h_same_verts)

/-- `lem:clone-sts`: the clone substitution has STS. -/
theorem refinedSubstitution_sts (h : τ.FLC) : (refinedSubstitution τ h).STS := by
  intro n c A hA B hB i j h_overlap
  have h_same_verts :=
    refinedSubstitution_sts_step1_visible_vertices _ h n c A B hA hB i j h_overlap
  exact refinedSubstitution_sts_step2_sides_eq _ h A B i j h_overlap h_same_verts

/-- `lem:clone-sts`: the clone substitution has hereditary listed sides. -/
theorem refinedSubstitution_hereditary (h : τ.FLC) :
    (refinedSubstitution τ h).HereditarySides := by
  sorry

/-! ## `lem:clone-substitution-lift`, `lem:clone-hierarchy-lift` -/

/-- Step 1 of the blueprint proof of `substitution_clone_lift_iff_step1_proj_is_subst`: projection of a
refined supertile is the original supertile. -/
private lemma substitution_clone_lift_iff_step1_proj_is_subst_step1_supertile_proj {τ : Substitution P} (h : τ.FLC)
    (n : ℕ) (c : (cloneProtoset τ h).Form) :
    (cloneDecoration τ h).projTile '' ((refinedSubstitution τ h).supertile n c) = τ.supertile n ((cloneDecoration τ h).proj c) := by
  sorry

/-- Step 2 of the blueprint proof of `substitution_clone_lift_iff_step1_proj_is_subst`: finite subpatch of
projection lifts to a finite subpatch. -/
private lemma substitution_clone_lift_iff_step1_proj_is_subst_step2_finite_preimage {τ : Substitution P} (h : τ.FLC)
    (T' : PlaneTiling (cloneProtoset τ h)) (F : Set (PlacedTile P))
    (hF_sub : F ⊆ (cloneDecoration τ h).projTile '' T'.tiles) (hF_fin : F.Finite) :
    ∃ F' ⊆ T'.tiles, (cloneDecoration τ h).projTile '' F' = F ∧ F'.Finite := by
  sorry

/-- Step 3 of the blueprint proof of `substitution_clone_lift_iff_step1_proj_is_subst`: occurrences project
to occurrences. -/
private lemma substitution_clone_lift_iff_step1_proj_is_subst_step3_occurs_proj {τ : Substitution P} (h : τ.FLC)
    (F' S' : Set (PlacedTile (cloneProtoset τ h))) (h_occ : OccursIn F' S') :
    OccursIn ((cloneDecoration τ h).projTile '' F') ((cloneDecoration τ h).projTile '' S') := by
  sorry

/-- Step 1 of the blueprint proof of `substitution_clone_lift_iff`: projection of a
refined-substitution tiling is a substitution tiling (one direction of the iff). -/
private theorem substitution_clone_lift_iff_step1_proj_is_subst {τ : Substitution P} (h : τ.FLC) (T : PlaneTiling P)
    (T' : PlaneTiling (cloneProtoset τ h))
    (hT' : (refinedSubstitution τ h).IsSubstitutionTiling T')
    (h_proj : (cloneDecoration τ h).project T' = T) :
    τ.IsSubstitutionTiling T := by
  intro F hF hFin
  have h1 : T.tiles = (cloneDecoration τ h).projTile '' T'.tiles := by
    have h1_proj : T.tiles = ((cloneDecoration τ h).project T').tiles := by
      rw [← h_proj]
    exact h1_proj
  have H1 : F ⊆ (cloneDecoration τ h).projTile '' T'.tiles := by
    rw [h1] at hF
    exact hF
  
  have ⟨F', hF'_sub, hF'_eq, hF'_fin⟩ := substitution_clone_lift_iff_step1_proj_is_subst_step2_finite_preimage h T' F H1 hFin
  
  have hF'occurs : ∃ (n : ℕ) (c : (cloneProtoset τ h).Form), OccursIn F' ((refinedSubstitution τ h).supertile n c) :=
    hT' F' hF'_sub hF'_fin
    
  rcases hF'occurs with ⟨n, c, h_occ⟩
  
  use n, (cloneDecoration τ h).proj c
  
  have h_occ_proj := substitution_clone_lift_iff_step1_proj_is_subst_step3_occurs_proj h F' ((refinedSubstitution τ h).supertile n c) h_occ
  rw [hF'_eq] at h_occ_proj
  
  have h_supertile_eq := substitution_clone_lift_iff_step1_proj_is_subst_step1_supertile_proj h n c
  
  rw [h_supertile_eq] at h_occ_proj
  exact h_occ_proj

/-- Step 1 of the blueprint proof of
`substitution_clone_lift_iff_step2_lift_is_subst_step1_lift`: every tile has a finite
neighbourhood in a plane tiling. -/
private lemma substitution_clone_lift_iff_step2_lift_is_subst_step1_lift_step1_neighbourhood_finite
    {P : Protoset} (T : PlaneTiling P) (A : PlacedTile P) (hA : A ∈ T.tiles) :
    (neighbourhood T.tiles A).Finite := by
  have _ := hA
  have hcompact : IsCompact A.carrier := IsCompact.vadd A.anchor (P.disk A.form).compact
  apply Set.Finite.subset (T.locallyFinite hcompact)
  intro B hB
  rw [neighbourhood] at hB
  exact ⟨hB.1, by simpa [Set.inter_comm] using hB.2⟩

/-- Step 2 of the blueprint proof of
`substitution_clone_lift_iff_step2_lift_is_subst_step1_lift`: a finite tile
neighbourhood occurs in a supertile and therefore supplies a realized clone context. -/
private lemma substitution_clone_lift_iff_step2_lift_is_subst_step1_lift_step2_context_realized
    {τ : Substitution P} (T : PlaneTiling P) (hT : τ.IsSubstitutionTiling T)
    (A : PlacedTile P) (hA : A ∈ T.tiles) (hN : (neighbourhood T.tiles A).Finite) :
    ∃ c : GenuineCornerClone τ, c.form = A.form ∧
      c.context = translateSet (-A.anchor) (neighbourhood T.tiles A) := by
  let K₀ : Set Pt := ⋃ p : P.Form, (P.disk p).carrier
  have hK₀ : IsCompact K₀ := by
    have hK₀' : IsCompact (⋃ p ∈ (Set.univ : Set P.Form), (P.disk p).carrier) :=
      Set.Finite.isCompact_biUnion (Set.finite_univ) (fun p _ => (P.disk p).compact)
    simpa [K₀] using hK₀'
  obtain ⟨R, hR⟩ := hK₀.isBounded.subset_closedBall (0 : Pt)
  have hshape : ∀ (p : P.Form) (x : Pt), x ∈ (P.disk p).carrier → dist x 0 ≤ R := by
    intro p x hx
    apply Metric.mem_closedBall.mp
    apply hR
    exact mem_iUnion.2 ⟨p, hx⟩
  have hR_nonneg : 0 ≤ R := by
    obtain ⟨x, hx⟩ := (P.disk A.form).interior_nonempty
    exact le_trans dist_nonneg (hshape A.form x (interior_subset hx))
  have hplaced : ∀ (B : PlacedTile P) (x : Pt), x ∈ B.carrier →
      dist x B.anchor ≤ R := by
    intro B x hx
    rw [PlacedTile.carrier, Set.mem_vadd_set_iff_neg_vadd_mem] at hx
    have h := hshape B.form (-B.anchor +ᵥ x) hx
    simpa [PlacedTile.carrier, dist_eq_norm, vadd_eq_add, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using h
  let K : Set Pt := Metric.closedBall A.anchor (3 * R)
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  let G : Set (PlacedTile P) := {B ∈ T.tiles | (B.carrier ∩ K).Nonempty}
  have hGfin : G.Finite := by
    exact T.locallyFinite hKcompact
  have hNG : neighbourhood T.tiles A ⊆ G := by
    intro B hB
    change B ∈ T.tiles ∧ (B.carrier ∩ K).Nonempty
    refine ⟨hB.1, ?_⟩
    rcases hB.2 with ⟨x, hxA, hxB⟩
    refine ⟨x, hxB, Metric.mem_closedBall.mpr ?_⟩
    exact le_trans (hplaced A x hxA) (by nlinarith [hR_nonneg])
  let F : Set (PlacedTile P) := G ∪ neighbourhood T.tiles A
  have hFfin : F.Finite := hGfin.union hN
  have hFsub : F ⊆ T.tiles := by
    intro B hB
    rcases hB with hB | hB
    · exact hB.1
    · exact hB.1
  have hFG : F ⊆ G := by
    intro B hB
    rcases hB with hB | hB
    · exact hB
    · exact hNG hB
  obtain ⟨n, p, v, hv⟩ := hT F hFsub hFfin
  let A' : PlacedTile P := A.translate v
  have hAG : A ∈ G := by
    change A ∈ T.tiles ∧ (A.carrier ∩ K).Nonempty
    refine ⟨hA, ?_⟩
    obtain ⟨x, hx⟩ := (P.disk A.form).interior_nonempty
    have hxA : A.anchor +ᵥ x ∈ A.carrier := by
      exact Set.vadd_mem_vadd_set (interior_subset hx)
    refine ⟨A.anchor +ᵥ x, hxA, Metric.mem_closedBall.mpr ?_⟩
    exact le_trans (hplaced A (A.anchor +ᵥ x) hxA) (by nlinarith [hR_nonneg])
  have hA' : A' ∈ τ.supertile n p := by
    apply hv
    exact ⟨A, Or.inl hAG, rfl⟩
  have hcarrier_translate (B : PlacedTile P) (w : Pt) :
      (B.translate w).carrier = w +ᵥ B.carrier := by
    ext x
    simp only [PlacedTile.carrier, PlacedTile.translate,
      Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_rev]
    rw [← add_assoc]
  have hinter (B C : PlacedTile P) (w : Pt) :
      ((B.translate w).carrier ∩ (C.translate w).carrier).Nonempty ↔
        (B.carrier ∩ C.carrier).Nonempty := by
    rw [hcarrier_translate B w, hcarrier_translate C w]
    constructor
    · rintro ⟨x, hxB, hxC⟩
      exact ⟨-w +ᵥ x, (Set.mem_vadd_set_iff_neg_vadd_mem.mp hxB),
        (Set.mem_vadd_set_iff_neg_vadd_mem.mp hxC)⟩
    · rintro ⟨x, hxB, hxC⟩
      exact ⟨w +ᵥ x, Set.vadd_mem_vadd_set hxB, Set.vadd_mem_vadd_set hxC⟩
  let F' : Patch P :=
    { tiles := translateSet v F
      finite := by
        change ((fun B => B.translate v) '' F).Finite
        exact hFfin.image (fun B => B.translate v)
      disjoint := by
        intro B hB C hC hne
        rcases hB with ⟨B₀, hB₀, rfl⟩
        rcases hC with ⟨C₀, hC₀, rfl⟩
        change Disjoint (interior (B₀.translate v).carrier)
          (interior (C₀.translate v).carrier)
        have hne₀ : B₀ ≠ C₀ := by
          intro h
          apply hne
          rw [h]
        have hd := T.disjoint (hFsub hB₀) (hFsub hC₀) hne₀
        have hB_eq : (B₀.translate v).carrier = v +ᵥ B₀.carrier :=
          hcarrier_translate B₀ v
        have hC_eq : (C₀.translate v).carrier = v +ᵥ C₀.carrier :=
          hcarrier_translate C₀ v
        rw [hB_eq, hC_eq, interior_vadd, interior_vadd]
        exact (disjoint_image_iff (add_right_injective v)).mpr hd }
  have hbuffer (B : PlacedTile P) (hB : B ∈ τ.supertile n p)
      (hBA : (A'.carrier ∩ B.carrier).Nonempty) : B ∈ F'.tiles := by
    apply Patch.mem_of_carrier_subset_union F' B
    · intro C hC hne
      change C ∈ translateSet v F at hC
      exact (Crowns.supertile_disjoint τ n p) hB (hv hC) hne.symm
    · intro y hy
      change y ∈ support (translateSet v F)
      simp only [support, Set.mem_iUnion]
      rcases hBA with ⟨x, hxA, hxB⟩
      have hyA : dist y A'.anchor ≤ 3 * R := by
        calc
          dist y A'.anchor ≤ dist y x + dist x A'.anchor := dist_triangle _ _ _
          _ ≤ dist y B.anchor + dist B.anchor x + dist x A'.anchor := by
            have htri : dist y x ≤ dist y B.anchor + dist B.anchor x :=
              dist_triangle y B.anchor x
            exact add_le_add htri (le_refl _)
          _ ≤ R + R + R := by
            have hBx : dist B.anchor x ≤ R := by
              simpa [dist_comm] using hplaced B x hxB
            nlinarith [hplaced B y hy, hBx, hplaced A' x hxA]
          _ = 3 * R := by ring
      have hyK : -v +ᵥ y ∈ K := by
        apply Metric.mem_closedBall.mpr
        calc
          dist (-v +ᵥ y) A.anchor = dist (-v +ᵥ y) (-v +ᵥ A'.anchor) := by
            simp [A', PlacedTile.translate, vadd_eq_add]
          _ = dist y A'.anchor := dist_vadd_cancel_left (-v) y A'.anchor
          _ ≤ 3 * R := hyA
      have hycover : -v +ᵥ y ∈ support T.tiles := by
        rw [T.cover]
        exact Set.mem_univ _
      simp only [support, Set.mem_iUnion] at hycover
      rcases hycover with ⟨C, hCT, hyC⟩
      have hCF : C ∈ F := by
        change C ∈ G ∪ neighbourhood T.tiles A
        exact Or.inl ⟨hCT, ⟨-v +ᵥ y, hyC, hyK⟩⟩
      refine ⟨C.translate v, ⟨C, hCF, rfl⟩, ?_⟩
      have hy' : v +ᵥ (-v +ᵥ y) = y := by simp
      rw [hcarrier_translate]
      rw [← hy']
      exact Set.vadd_mem_vadd_set hyC
  have hneigh : neighbourhood (τ.supertile n p) A' =
      translateSet v (neighbourhood T.tiles A) := by
    ext B
    constructor
    · intro hB
      have hBF : B ∈ F'.tiles := hbuffer B hB.1 hB.2
      rcases hBF with ⟨C, hCF, rfl⟩
      change C ∈ F at hCF
      refine ⟨C, ?_, rfl⟩
      change C ∈ T.tiles ∧ (A.carrier ∩ C.carrier).Nonempty
      refine ⟨hFsub hCF, ?_⟩
      apply (hinter A C v).mp
      simpa [A'] using hB.2
    · rintro ⟨C, hC, rfl⟩
      have hCF : C ∈ F := Or.inl (hNG hC)
      have hCS : C.translate v ∈ τ.supertile n p := hv ⟨C, hCF, rfl⟩
      refine ⟨hCS, ?_⟩
      exact (hinter A C v).mpr hC.2
  let c : GenuineCornerClone τ :=
    { form := A'.form
      context := translateSet (-A'.anchor) (neighbourhood (τ.supertile n p) A')
      realized := ⟨n, p, A', hA', rfl⟩ }
  refine ⟨c, ?_, ?_⟩
  · rfl
  · change translateSet (-A'.anchor) (neighbourhood (τ.supertile n p) A') = _
    rw [hneigh]
    rw [childContext_realized_step1_shift_step1_translateSet_translateSet]
    congr 1
    dsimp [A', PlacedTile.translate]
    abel

/-- Step 3 of the blueprint proof of
`substitution_clone_lift_iff_step2_lift_is_subst_step1_lift`: form-compatible
labels can be assembled into a plane tiling without changing carriers. -/
private lemma substitution_clone_lift_iff_step2_lift_is_subst_step1_lift_step3_relabel
    {τ : Substitution P} (h : τ.FLC) (T : PlaneTiling P)
    (label : T.tiles → GenuineCornerClone τ)
    (hform : ∀ A : T.tiles, (label A).form = A.1.form) :
    ∃ T' : PlaneTiling (cloneProtoset τ h),
      T'.tiles = {A' | ∃ A : T.tiles,
        A' = (⟨label A, A.1.anchor⟩ : PlacedTile (cloneProtoset τ h))} ∧
      (cloneDecoration τ h).project T' = T := by
  sorry

/-- Step 1 of the blueprint proof of `substitution_clone_lift_iff_step2_lift_is_subst`: there exists
a lifted plane tiling constructed by labelling each tile with its actual full neighbourhood. -/
private lemma substitution_clone_lift_iff_step2_lift_is_subst_step1_lift
    {τ : Substitution P} (h : τ.FLC) (T : PlaneTiling P) (hT : τ.IsSubstitutionTiling T) :
    ∃ T' : PlaneTiling (cloneProtoset τ h),
      (cloneDecoration τ h).project T' = T ∧
      ∀ A' ∈ T'.tiles, A'.form.context =
        translateSet (-A'.anchor) (neighbourhood T.tiles ((cloneDecoration τ h).projTile A')) := by
  let hreal : ∀ A : T.tiles, ∃ c : GenuineCornerClone τ, c.form = A.1.form ∧
      c.context = translateSet (-A.1.anchor) (neighbourhood T.tiles A.1) := fun A =>
    substitution_clone_lift_iff_step2_lift_is_subst_step1_lift_step2_context_realized T hT A.1 A.2
      (substitution_clone_lift_iff_step2_lift_is_subst_step1_lift_step1_neighbourhood_finite T A.1 A.2)
  let label : T.tiles → GenuineCornerClone τ := fun A => (hreal A).choose
  have hform : ∀ A : T.tiles, (label A).form = A.1.form := by
    intro A
    exact (hreal A).choose_spec.1
  obtain ⟨T', htiles, hproj⟩ :=
    substitution_clone_lift_iff_step2_lift_is_subst_step1_lift_step3_relabel h T label hform
  refine ⟨T', hproj, ?_⟩
  intro A' hA'
  rw [htiles] at hA'
  rcases hA' with ⟨A, rfl⟩
  have hprojTile : (cloneDecoration τ h).projTile
      (⟨label A, A.1.anchor⟩ : PlacedTile (cloneProtoset τ h)) = A.1 := by
    apply PlacedTile.ext
    · exact hform A
    · rfl
  rw [hprojTile]
  exact (hreal A).choose_spec.2

/-- Step 2 of the blueprint proof of `substitution_clone_lift_iff_step2_lift_is_subst`: this
lifted plane tiling is substitutive. -/
private lemma substitution_clone_lift_iff_step2_lift_is_subst_step2_subst
    {τ : Substitution P} (h : τ.FLC) (T : PlaneTiling P) (hT : τ.IsSubstitutionTiling T)
    (T' : PlaneTiling (cloneProtoset τ h)) (hProj : (cloneDecoration τ h).project T' = T)
    (hLift : ∀ A' ∈ T'.tiles, A'.form.context =
      translateSet (-A'.anchor) (neighbourhood T.tiles ((cloneDecoration τ h).projTile A'))) :
    (refinedSubstitution τ h).IsSubstitutionTiling T' := by
  sorry

/-- Step 2 of the blueprint proof of `substitution_clone_lift_iff`: in the other direction,
the lifted plane tiling constructed by labelling each tile with its actual full
neighbourhood is substitutive. -/
private theorem substitution_clone_lift_iff_step2_lift_is_subst {τ : Substitution P} (h : τ.FLC) (T : PlaneTiling P)
    (hT : τ.IsSubstitutionTiling T) :
    ∃ T' : PlaneTiling (cloneProtoset τ h),
      (refinedSubstitution τ h).IsSubstitutionTiling T' ∧
        (cloneDecoration τ h).project T' = T := by
  obtain ⟨T', hProj, hLift⟩ := substitution_clone_lift_iff_step2_lift_is_subst_step1_lift h T hT
  have hS := substitution_clone_lift_iff_step2_lift_is_subst_step2_subst h T hT T' hProj hLift
  exact ⟨T', hS, hProj⟩

/-- `lem:clone-substitution-lift`: a plane tiling is a `τ`-substitution tiling
iff it is the projection of a refined-substitution tiling. -/
theorem substitution_clone_lift_iff (h : τ.FLC) (T : PlaneTiling P) :
    τ.IsSubstitutionTiling T ↔
      ∃ T' : PlaneTiling (cloneProtoset τ h),
        (refinedSubstitution τ h).IsSubstitutionTiling T' ∧
          (cloneDecoration τ h).project T' = T := by
  constructor
  · exact substitution_clone_lift_iff_step2_lift_is_subst h T
  · rintro ⟨T', hT', hProj⟩
    exact substitution_clone_lift_iff_step1_proj_is_subst h T T' hT' hProj

/-- `lem:clone-hierarchy-lift`: a plane tiling is `τ`-hierarchical iff it is
the projection of a refined-substitution hierarchical tiling. -/
theorem hierarchy_clone_lift_iff (h : τ.FLC) (T : PlaneTiling P) :
    τ.IsHierarchical T ↔
      ∃ T' : PlaneTiling (cloneProtoset τ h),
        (refinedSubstitution τ h).IsHierarchical T' ∧
          (cloneDecoration τ h).project T' = T := by
  sorry

/-! ## `lem:segment-rules` -/

/-- Compose two carrier-preserving finite decorations. -/
private def composeDecoration (d : Decoration P) (e : Decoration d.P') : Decoration P where
  P' := e.P'
  proj := d.proj ∘ e.proj
  surj := d.surj.comp e.surj
  carrier_eq := fun q => (e.carrier_eq q).trans (d.carrier_eq (e.proj q))

/-- Projection through a composite decoration is iterated projection. -/
private lemma composeDecoration_project (d : Decoration P) (e : Decoration d.P')
    (T : PlaneTiling e.P') :
    (composeDecoration d e).project T = d.project (e.project T) := by
  cases T with
  | mk tiles cover disjoint =>
      simp only [Decoration.project]
      rw [PlaneTiling.mk.injEq]
      ext A
      simp [Decoration.projTile, composeDecoration]

/-- Composing the presenting decoration with a carrier-preserving projection
transfers any bounded local rule without changing its forbidden patches. -/
private lemma projection_preserves_sofic (d : Decoration P) (G : Set (PlaneTiling d.P'))
    (hG : IsSofic G) : IsSofic (d.project '' G) := by
  obtain ⟨e, R, h⟩ := hG
  refine ⟨composeDecoration d e, R, fun T => ⟨?_, ?_⟩⟩
  · rintro ⟨U, hU, rfl⟩
    obtain ⟨V, hR, hVU⟩ := (h U).mp hU
    refine ⟨V, hR, ?_⟩
    rw [composeDecoration_project, hVU]
  · rintro ⟨V, hR, hVT⟩
    have he : e.project V ∈ G := (h _).mpr ⟨V, hR, rfl⟩
    refine ⟨e.project V, he, ?_⟩
    rw [← composeDecoration_project]
    exact hVT

/-- Every listed side of a polygonal disk lies in its carrier. -/
private lemma disk_side_subset_for_rule (D : PolygonalDisk) (i : Fin D.n) :
    D.side i ⊆ D.carrier := by
  apply (show D.side i ⊆ frontier D.carrier from ?_).trans D.compact.isClosed.frontier_subset
  rw [D.frontier_eq]
  exact Set.subset_iUnion (fun j => segment ℝ (D.vertex j) (D.vertex (finRotate D.n j))) i

/-- Every listed side of a placed tile lies in its carrier. -/
private lemma tile_side_subset_for_rule (A : PlacedTile P) (i : Fin (P.disk A.form).n) :
    A.side i ⊆ A.carrier := by
  exact image_mono (disk_side_subset_for_rule (P.disk A.form) i)

/-- A listed side has an endpoint and hence is nonempty. -/
private lemma tile_side_nonempty_for_rule (A : PlacedTile P) (i : Fin (P.disk A.form).n) :
    (A.side i).Nonempty := by
  refine ⟨A.vertex i, ?_⟩
  exact ⟨(P.disk A.form).vertex i, left_mem_segment ℝ _ _, rfl⟩

/-- The two possible local failures of a side decoration on a pair of tiles. -/
private def SideRuleBad (dec : SideDecoration P) (A B : PlacedTile dec.P') : Prop :=
  ∃ (i : Fin (dec.P'.disk A.form).n) (j : Fin (dec.P'.disk B.form).n),
    (OverlapPos (A.side i) (B.side j) ∧ A.side i ≠ B.side j) ∨
      (A ≠ B ∧ A.side i = B.side j ∧ dec.colour A.form i ≠ dec.colour B.form j)

/-- A pair witnessing a side-rule failure has intersecting carriers. -/
private lemma bad_carriers_meet (dec : SideDecoration P) (A B : PlacedTile dec.P')
    (h : SideRuleBad dec A B) : (A.carrier ∩ B.carrier).Nonempty := by
  obtain ⟨i, j, hbad | hbad⟩ := h
  · obtain ⟨⟨x, y, hxy, hseg⟩, hne⟩ := hbad
    have hx := hseg (left_mem_segment ℝ x y)
    exact ⟨x, tile_side_subset_for_rule A i hx.1, tile_side_subset_for_rule B j hx.2⟩
  · obtain ⟨hne, heq, hcol⟩ := hbad
    obtain ⟨x, hx⟩ := tile_side_nonempty_for_rule A i
    exact ⟨x, tile_side_subset_for_rule A i hx, tile_side_subset_for_rule B j (heq ▸ hx)⟩

/-- The side matching condition as a bounded local rule of forbidden pairs. -/
private def sideLocalRule (dec : SideDecoration P) : LocalRule dec.P' where
  forbidden := {F | ∃ A B, F = {A, B} ∧ SideRuleBad dec A B}
  D := 2 * ∑ q : dec.P'.Form, Metric.diam (dec.P'.disk q).carrier
  bounded := by
    rintro F ⟨A, B, rfl, hbad⟩
    refine ⟨Set.toFinite {A, B}, ?_⟩
    have hmeet : (A.carrier ∩ B.carrier).Nonempty := bad_carriers_meet dec A B hbad
    have hA : Metric.diam A.carrier ≤ ∑ q : dec.P'.Form, Metric.diam (dec.P'.disk q).carrier := by
      rw [PlacedTile.carrier, diam_vadd]
      exact Finset.single_le_sum (f := fun q : dec.P'.Form => Metric.diam (dec.P'.disk q).carrier)
        (fun _ _ => Metric.diam_nonneg) (Finset.mem_univ A.form)
    have hB : Metric.diam B.carrier ≤ ∑ q : dec.P'.Form, Metric.diam (dec.P'.disk q).carrier := by
      rw [PlacedTile.carrier, diam_vadd]
      exact Finset.single_le_sum (f := fun q : dec.P'.Form => Metric.diam (dec.P'.disk q).carrier)
        (fun _ _ => Metric.diam_nonneg) (Finset.mem_univ B.form)
    have hu := Metric.diam_union' hmeet
    rw [show support ({A, B} : Set (PlacedTile dec.P')) = A.carrier ∪ B.carrier by simp [support]]
    calc
      Metric.diam (A.carrier ∪ B.carrier) ≤ Metric.diam A.carrier + Metric.diam B.carrier := hu
      _ ≤ _ := by linarith

private lemma translate_tile_zero (A : PlacedTile P) : A.translate 0 = A := by
  apply PlacedTile.ext <;> simp [PlacedTile.translate]

private lemma translate_tile_injective (v : Pt) :
    Function.Injective (fun A : PlacedTile P => A.translate v) := by
  intro A B h
  have h' := congrArg (fun X : PlacedTile P => X.translate (-v)) h
  have hp : A.form = B.form ∧ A.anchor = B.anchor := by
    simpa [PlacedTile.translate] using h'
  exact PlacedTile.ext hp.1 hp.2

private lemma side_translate_for_rule (A : PlacedTile P) (v : Pt)
    (i : Fin (P.disk A.form).n) : (A.translate v).side i = v +ᵥ A.side i := by
  show (v +ᵥ A.anchor) +ᵥ _ = v +ᵥ (A.anchor +ᵥ _)
  rw [vadd_vadd]
  rfl

private lemma vadd_set_injective (v : Pt) : Function.Injective (fun s : Set Pt => v +ᵥ s) := by
  intro s t h
  ext x
  have hx := Set.ext_iff.mp h (v +ᵥ x)
  rwa [vadd_mem_vadd_set_iff, vadd_mem_vadd_set_iff] at hx

private lemma overlap_vadd (v : Pt) {s t : Set Pt} (h : OverlapPos s t) :
    OverlapPos (v +ᵥ s) (v +ᵥ t) := by
  obtain ⟨x, y, hxy, hseg⟩ := h
  refine ⟨v +ᵥ x, v +ᵥ y, fun h => hxy (add_left_cancel h), ?_⟩
  rw [← vadd_segment]
  rintro z ⟨w, hw, rfl⟩
  exact ⟨⟨w, (hseg hw).1, rfl⟩, ⟨w, (hseg hw).2, rfl⟩⟩

/-- Side-rule failure is invariant under translating both tiles. -/
private lemma sideRuleBad_translate (dec : SideDecoration P) (A B : PlacedTile dec.P')
    (v : Pt) (h : SideRuleBad dec A B) : SideRuleBad dec (A.translate v) (B.translate v) := by
  obtain ⟨i, j, hbad | hbad⟩ := h
  · refine ⟨i, j, Or.inl ⟨?_, ?_⟩⟩
    · rw [side_translate_for_rule, side_translate_for_rule]
      exact overlap_vadd v hbad.1
    · rw [side_translate_for_rule, side_translate_for_rule]
      exact fun heq => hbad.2 (vadd_set_injective v heq)
  · refine ⟨i, j, Or.inr ⟨?_, ?_, hbad.2.2⟩⟩
    · intro heq
      exact hbad.1 (translate_tile_injective v heq)
    rw [side_translate_for_rule, side_translate_for_rule, hbad.2.1]

private lemma translate_set_zero (S : Set (PlacedTile P)) : translateSet 0 S = S := by
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    simpa [translate_tile_zero] using hB
  · intro hA
    exact ⟨A, hA, translate_tile_zero A⟩

/-- The forbidden-pair local rule is equivalent to the strict side rule on plane tilings. -/
private lemma sideLocalRule_proper_iff (dec : SideDecoration P) (T : PlaneTiling dec.P') :
    (sideLocalRule dec).Proper T ↔ dec.Proper T := by
  constructor
  · intro h
    constructor
    · intro A hA B hB i j hover
      by_contra hne
      apply h {A, B} ⟨A, B, rfl, i, j, Or.inl ⟨hover, hne⟩⟩
      refine ⟨0, ?_⟩
      rw [translate_set_zero]
      intro X hX
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl
      · exact hA
      · exact hB
    · intro A hA B hB hAB i j hsides
      by_contra hcol
      apply h {A, B} ⟨A, B, rfl, i, j, Or.inr ⟨hAB, hsides, hcol⟩⟩
      refine ⟨0, ?_⟩
      rw [translate_set_zero]
      intro X hX
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl
      · exact hA
      · exact hB
  · rintro ⟨hsts, hcol⟩ F ⟨A, B, rfl, hbad⟩ ⟨v, hv⟩
    have hAv : A.translate v ∈ T.tiles := hv (by simp [translateSet])
    have hBv : B.translate v ∈ T.tiles := hv (by simp [translateSet])
    obtain ⟨i, j, hbad | hbad⟩ := sideRuleBad_translate dec A B v hbad
    · exact hbad.2 (hsts _ hAv _ hBv i j hbad.1)
    · exact hbad.2.2 (hcol _ hAv _ hBv hbad.1 i j hbad.2.1)

/-- A strict side-to-side presentation is a bounded-local-rule presentation. -/
private lemma sideToSideSofic_isSofic (G : Set (PlaneTiling P))
    (hG : IsSideToSideSofic G) : IsSofic G := by
  obtain ⟨dec, h⟩ := hG
  refine ⟨dec.toDecoration, sideLocalRule dec, ?_⟩
  intro T
  rw [h T]
  constructor
  · rintro ⟨T', hT', rfl⟩
    exact ⟨T', (sideLocalRule_proper_iff dec T').mpr hT', rfl⟩
  · rintro ⟨T', hT', rfl⟩
    exact ⟨T', (sideLocalRule_proper_iff dec T').mp hT', rfl⟩

/-- `lem:segment-rules`: a sofic presentation on decorated (e.g. clone) tiles,
given either by an arbitrary bounded local rule or by the strict side rule on
the refined listed sides, transfers through the carrier-preserving projection
to a sofic presentation (finite decoration + bounded local rule) of the
projected family on the original carriers.  Applied with
`d = cloneDecoration τ h`. -/
theorem forget_vertices_preserves_sofic (d : Decoration P) (G : Set (PlaneTiling d.P'))
    (hG : IsSofic G ∨ IsSideToSideSofic G) : IsSofic (d.project '' G) := by
  apply projection_preserves_sofic d G
  exact hG.elim id (sideToSideSofic_isSofic G)

end FLC

end Tilings

end
