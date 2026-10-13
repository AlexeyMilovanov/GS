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

/-- Step 2 of the blueprint proof of `three_le_genuineCount_step1`:
Every extreme point of the convex hull of the vertices is a genuine vertex. -/
private lemma three_le_genuineCount_step1_step2_extreme_points_subset_genuine :
    extremePoints ℝ (convexHull ℝ D.vertexSet) ⊆ D.vertex '' D.genuineIdx := by
  sorry

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

/-- Merging collinear sides does not change the boundary. -/
theorem coarse_frontier_eq :
    frontier D.carrier = ⋃ i : Fin D.genuineCount,
      segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)) := by
  sorry

/-- Step 1.1 of the blueprint proof of `coarse_simple_step1`: A fine segment that intersects the interior of a coarse segment must be contained in it. -/
private lemma coarse_simple_step1_step1 (i : Fin D.genuineCount) (k : Fin D.n)
    (h_int : ∃ x, x ∈ segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ∧ 
      x ∈ segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)) ∧
      x ≠ D.coarseVertex i ∧ x ≠ D.coarseVertex (finRotate D.genuineCount i)) :
    segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ⊆ 
      segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)) := by
  sorry

/-- Step 1.2 of the blueprint proof of `coarse_simple_step1`: The endpoints of a coarse segment belong to some fine segment contained in that coarse segment. -/
private lemma coarse_simple_step1_step2 (i : Fin D.genuineCount) (x : Pt)
    (h_end : x = D.coarseVertex i ∨ x = D.coarseVertex (finRotate D.genuineCount i)) :
    ∃ k : Fin D.n, x ∈ segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ∧ 
      segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ⊆
        segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)) := by
  sorry

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

/-- Step 1 of the blueprint proof of `coarse_simple_step2`: The fine segments `k1` and `k2` must be distinct. -/
private lemma coarse_simple_step2_step1 (i j : Fin D.genuineCount) (hij : i ≠ j)
    (k1 k2 : Fin D.n)
    (h1 : segment ℝ (D.vertex k1) (D.vertex (finRotate D.n k1)) ⊆
      segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)))
    (h2 : segment ℝ (D.vertex k2) (D.vertex (finRotate D.n k2)) ⊆
      segment ℝ (D.coarseVertex j) (D.coarseVertex (finRotate D.genuineCount j))) :
    k1 ≠ k2 := by
  sorry

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
  sorry

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

/-- The substitution `τ` read on the coarsened protoset. -/
def coarsenSubstitution (τ : Substitution P) : Substitution (coarsen P) where
  θ := τ.θ
  one_lt := τ.one_lt
  rule := fun p : P.Form =>
    { tiles := coarsenTile '' (τ.rule p).tiles
      finite := (τ.rule p).finite.image coarsenTile
      disjoint := sorry }
  support_eq := sorry

/-- FLC survives coarsening. -/
theorem coarsen_flc (τ : Substitution P) (h : τ.FLC) : (coarsenSubstitution τ).FLC := by
  sorry

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

/-- Steps 1 to 4 of the blueprint proof of `finite_neighbourhoods`: all neighbourhood
supports have bounded diameter, so there is k such that in supertiles of order n >= k,
the neighbourhood is covered by a full pointed crown of order n-k, which implies
the context belongs to CrownContexts. -/
private lemma finite_neighbourhoods_step1to4 (τ : Substitution P) (h : τ.FLC) :
    ∃ k : ℕ, ∀ (n : ℕ) (hn : k ≤ n) (p : P.Form) (A : PlacedTile P)
      (hA : A ∈ τ.supertile n p),
      (A.form, translateSet (-A.anchor) (neighbourhood (τ.supertile n p) A)) ∈
        finite_neighbourhoods_CrownContexts τ k := by
  sorry

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

/-- A polygonal disk with the carrier of the selected form and exactly the
clone vertices as listed vertices exists. -/
theorem exists_cloneDisk (c : GenuineCornerClone τ) :
    ∃ D : PolygonalDisk, D.carrier = (P.disk c.form).carrier ∧ D.vertexSet = cloneVertexSet c := by
  sorry

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
  sorry

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

/-- `def:clones`: the clone (refined) substitution. -/
def refinedSubstitution (h : τ.FLC) : Substitution (cloneProtoset τ h) where
  θ := τ.θ
  one_lt := τ.one_lt
  rule := fun c : GenuineCornerClone τ =>
    { tiles := refinedRule τ h c
      finite := sorry
      disjoint := sorry }
  support_eq := sorry

/-- Forgetting clone labels: a carrier-preserving decoration of `P`. -/
def cloneDecoration (h : τ.FLC) : Decoration P where
  P' := cloneProtoset τ h
  proj := fun c : GenuineCornerClone τ => c.form
  surj := fun p => by
    obtain ⟨c, hc⟩ := exists_clone_of_form τ p
    exact ⟨c, hc⟩
  carrier_eq := fun c : GenuineCornerClone τ => cloneDisk_carrier c

/-! ## `lem:clone-sts` -/

/-- `lem:clone-sts` (commutation): the clone substitution commutes with
forgetting labels. -/
theorem refinedSubstitution_commutes (h : τ.FLC)
    (S : Set (PlacedTile (cloneProtoset τ h))) :
    (cloneDecoration τ h).projTile '' ((refinedSubstitution τ h).decompose S) =
      τ.decompose ((cloneDecoration τ h).projTile '' S) := by
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
  sorry

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

/-- Step 1 of the blueprint proof of `substitution_clone_lift_iff_step2_lift_is_subst`: there exists
a lifted plane tiling constructed by labelling each tile with its actual full neighbourhood. -/
private lemma substitution_clone_lift_iff_step2_lift_is_subst_step1_lift
    {τ : Substitution P} (h : τ.FLC) (T : PlaneTiling P) (hT : τ.IsSubstitutionTiling T) :
    ∃ T' : PlaneTiling (cloneProtoset τ h),
      (cloneDecoration τ h).project T' = T ∧
      ∀ A' ∈ T'.tiles, A'.form.context =
        translateSet (-A'.anchor) (neighbourhood T.tiles ((cloneDecoration τ h).projTile A')) := by
  sorry

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
