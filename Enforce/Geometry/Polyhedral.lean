import Enforce.Basic

/-!
# Polyhedral domains and their local geometry

The frontier manifold condition uses relative open neighbourhoods and homeomorphisms
to open subsets of Euclidean space. This is the chosen chart formulation of (H1).
The solid angle is measured in steradians, by `d` times the volume of a unit-ball sector.
-/

open Set Metric MeasureTheory

noncomputable section

namespace Enforce

variable {d : ℕ}

/-- G1, V4 §1.0 (H1): a finite union of convex hulls of finite sets of vertices.
Empty polyhedra are allowed here; domains and cells separately require nonemptiness. -/
def Polyhedron (K : Set (E d)) : Prop :=
  ∃ s : Finset (Finset (E d)), K = ⋃ p ∈ s, convexHull ℝ (p : Set (E d))

/-- G1, V4 §1.0 (H1): local Euclidean charts on a subset, in its subspace topology.
At every point there is a relative open neighbourhood homeomorphic to an open subset
of `E n`. In particular the condition on an empty frontier is harmless. -/
def IsLocallyEuclidean (n : ℕ) (K : Set (E d)) : Prop :=
  ∀ p : K, ∃ U : Set K, IsOpen U ∧ p ∈ U ∧
    ∃ V : Set (E n), IsOpen V ∧ Nonempty (U ≃ₜ V)

/-- G1, V4 §1.0 (H1): a full-dimensional polyhedral manifold domain.
Nonconvexity, cavities, handles and arbitrary Euclidean placements are permitted.
The explicit nonempty interior excludes degenerate or empty prototiles. -/
structure PolyManifoldDomain (d : ℕ) where
  /-- G1, V4 §1.0 (H1): the closed region. -/
  carrier : Set (E d)
  /-- G1, V4 §1.0 (H1): finite polyhedral presentation. -/
  polyhedral : Polyhedron carrier
  /-- G1, V4 §1.0 (H1): compactness, redundant with the finite presentation. -/
  compact : IsCompact carrier
  /-- G1, V4 §1.0 (H1): ambient regular closedness. -/
  regularClosed : IsRegularClosed carrier
  /-- G1, V4 §1.0 (H1): connected interior. -/
  interior_connected : IsConnected (interior carrier)
  /-- G1, V4 §1.0 (H1): full dimensionality. -/
  interior_nonempty : (interior carrier).Nonempty
  /-- G1, V4 §1.0 (H1): the boundary is a topological `(d-1)`-manifold. -/
  frontier_manifold : IsLocallyEuclidean (d - 1) (frontier carrier)

/-- G2, V4 §1.0 (H2): the relative interior in the affine span, as an ambient set. -/
def relint (K : Set (E d)) : Set (E d) := intrinsicInterior ℝ K

/-- G2, V4 §1.0 (H2): relative boundary in the affine span, as an ambient set. -/
def relfrontier (K : Set (E d)) : Set (E d) := intrinsicFrontier ℝ K

/-- G2, V4 §1.0 (H2): the direction space of the affine hull. -/
def cellDirection (K : Set (E d)) : Submodule ℝ (E d) :=
  (affineSpan ℝ K).direction

/-- G2, V4 §1.0 (H2): a flat `j`-cell, regular closed in its own affine span.
The relative boundary charts express that the cell is a polyhedral manifold domain
in that span. A zero-dimensional cell has empty relative boundary. -/
structure IsFlatCell (j : ℕ) (K : Set (E d)) : Prop where
  /-- G2, V4 §1.0 (H2): finite polyhedral carrier. -/
  polyhedral : Polyhedron K
  /-- G2, V4 §1.0 (H2): affine dimension is the listed dimension. -/
  dimension : Module.finrank ℝ (cellDirection K) = j
  /-- G2, V4 §1.0 (H2): compactness. -/
  compact : IsCompact K
  /-- G2, V4 §1.0 (H2): connectedness of the cell. -/
  connected : IsConnected K
  /-- G2, V4 §1.0 (H2)(iii): closure of the relative interior. -/
  regularClosed : closure (relint K) = K
  /-- G2, V4 §1.0 (H2): connected relative interior. -/
  relint_connected : IsConnected (relint K)
  /-- G2, V4 §1.0 (H2): nonempty relative interior. -/
  relint_nonempty : (relint K).Nonempty
  /-- G2, V4 §1.0 (H2): relative boundary manifold condition. -/
  boundary_manifold : IsLocallyEuclidean (j - 1) (relfrontier K)

/-- G2, V4 §1.0 (H2): a flat compact cell with its dimension as data. -/
structure Cell (d : ℕ) where
  /-- G2, V4 §1.0 (H2): closed carrier. -/
  carrier : Set (E d)
  /-- G2, V4 §1.0 (H2): dimension, including zero. -/
  dim : ℕ
  /-- G2, V4 §1.0 (H2): all geometric cell conditions. -/
  flat : IsFlatCell dim carrier

/-- G5, V4 1.0(b): the local radial tangent cone, translated to the origin.
The positive-time germ, rather than a limiting or convexified cone, is used. -/
def tangentCone (K : Set (E d)) (p : E d) : Set (E d) :=
  {v | ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → p + t • v ∈ K}

/-- G5, V4 1.0(b): a finite union of closed convex polyhedral cones.
Each convex piece is a finite intersection of homogeneous closed half-spaces. -/
def IsPolyhedralCone (K : Set (E d)) : Prop :=
  ∃ s : Finset (Finset (E d →ₗ[ℝ] ℝ)),
    K = ⋃ p ∈ s, {v | ∀ ℓ ∈ p, 0 ≤ ℓ v}

/-- G5, V4 1.0(b): solid angle, using radial volume in the Euclidean unit ball.
This equals the usual spherical area for measurable cones. -/
def solidAngle (K : Set (E d)) : ℝ :=
  (d : ℝ) * (volume (K ∩ ball 0 1)).toReal

/-- G5, V4 1.0(b): the full solid angle `ω_d`, in the same normalization. -/
def fullSolidAngle (d : ℕ) : ℝ :=
  (d : ℝ) * (volume (ball (0 : E d) 1)).toReal

/-- Step 1 of the V4 proof of `tangentCone_polyhedral` (V4 1.0(b)):
"A is a polyhedron". A simplex, including a lower-dimensional one, is cut out by
finitely many affine inequalities, using coordinates of an extended affine basis. -/
private lemma tangentCone_polyhedral_step1_simplex_halfspaces
    (s : Finset (E d)) (hs : AffineIndependent ℝ ((↑) : s → E d)) :
    ∃ q : Finset (E d →ᵃ[ℝ] ℝ),
      convexHull ℝ (s : Set (E d)) = {x | ∀ f ∈ q, 0 ≤ f x} := by
  classical
  obtain ⟨t, hst, ht, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hs
  let b : AffineBasis t ℝ (E d) := ⟨(↑), ht, by simpa using hspan⟩
  letI : Finite t := finite_of_fin_dim_affineIndependent ℝ ht
  letI : Fintype t := Fintype.ofFinite t
  let q : Finset (E d →ᵃ[ℝ] ℝ) :=
    Finset.univ.image b.coord ∪
      (Finset.univ.filter fun i : t => (i : E d) ∉ s).image (fun i => -b.coord i)
  refine ⟨q, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx f hf
    apply convexHull_min (t := {x | 0 ≤ f x}) ?_
      (Convex.affine_preimage f (convex_Ici 0)) hx
    intro y hy
    let j : t := ⟨y, hst hy⟩
    change 0 ≤ f (b j)
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
      simp only [b.coord_apply]
      split_ifs <;> norm_num
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hf
      have hij : i ≠ j := by
        intro hij
        have := (Finset.mem_filter.mp hi).2
        exact this (by simpa [hij, j] using hy)
      simp [b.coord_apply_ne hij]
  · intro x hx
    have hpos (i : t) : 0 ≤ b.coord i x :=
      hx _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    have hzero (i : t) (hi : (i : E d) ∉ s) : b.coord i x = 0 := by
      have hn := hx _ (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩))
      have hn' : 0 ≤ -b.coord i x := hn
      exact le_antisymm (by linarith) (hpos i)
    let u : Finset t := Finset.univ.filter fun i : t => (i : E d) ∈ s
    have hsum : ∑ i ∈ u, b.coord i x = 1 := by
      rw [← b.sum_coord_apply_eq_one x]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      exact hzero i (by simpa [u] using hi)
    have hsumv : ∑ i ∈ u, b.coord i x • b i = x := by
      calc
        _ = ∑ i, b.coord i x • b i := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          rw [hzero i (by simpa [u] using hi), zero_smul]
        _ = x := b.linear_combination_coord_eq_self x
    rw [← hsumv]
    apply (convex_convexHull ℝ (s : Set (E d))).sum_mem (fun i _ => hpos i) hsum
    intro i hi
    exact subset_convexHull ℝ (s : Set (E d)) (Finset.mem_filter.mp hi).2

/-- Step 2 of the V4 proof of `tangentCone_polyhedral` (V4 1.0(b)):
"A is a polyhedron". Carathéodory's theorem gives a finite union of simplices,
and hence a finite union of intersections of affine closed half-spaces. -/
private lemma tangentCone_polyhedral_step2_halfspace_presentation
    {K : Set (E d)} (hK : Polyhedron K) :
    ∃ S : Finset (Finset (E d →ᵃ[ℝ] ℝ)),
      K = ⋃ q ∈ S, {x | ∀ f ∈ q, 0 ≤ f x} := by
  classical
  obtain ⟨s, rfl⟩ := hK
  have hrep (t : Finset (E d)) : ∃ q : Finset (E d →ᵃ[ℝ] ℝ),
      AffineIndependent ℝ ((↑) : t → E d) →
        convexHull ℝ (t : Set (E d)) = {x | ∀ f ∈ q, 0 ≤ f x} := by
    by_cases ht : AffineIndependent ℝ ((↑) : t → E d)
    · obtain ⟨q, hq⟩ := tangentCone_polyhedral_step1_simplex_halfspaces t ht
      exact ⟨q, fun _ => hq⟩
    · exact ⟨∅, fun h => (ht h).elim⟩
  choose q hq using hrep
  let S := s.biUnion fun p =>
    (p.powerset.filter fun t : Finset (E d) =>
      AffineIndependent ℝ ((↑) : t → E d)).image q
  refine ⟨S, ?_⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨p, hp, hx⟩
    rw [convexHull_eq_union] at hx
    obtain ⟨t, htp, ht, hxt⟩ := by
      simpa only [Set.mem_iUnion, exists_prop] using hx
    refine ⟨q t, Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨t,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr htp, ht⟩, rfl⟩
    · rwa [hq t ht] at hxt
  · rintro ⟨r, hr, hx⟩
    obtain ⟨p, hp, hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨htp, ht⟩ := Finset.mem_filter.mp ht
    refine ⟨p, hp, convexHull_mono (Finset.mem_powerset.mp htp) ?_⟩
    change x ∈ convexHull ℝ (t : Set (E d))
    rwa [hq t ht]

open scoped Topology in
/-- Step 3 of the V4 proof of `tangentCone_polyhedral` (V4 1.0(b)):
"its tangent cone at any point is a polyhedral cone". Near the base point,
inactive inequalities keep their sign and active inequalities become homogeneous. -/
private lemma tangentCone_polyhedral_step3_local_cone
    (S : Finset (Finset (E d →ᵃ[ℝ] ℝ))) (p : E d) :
    ∃ C : Set (E d), IsPolyhedralCone C ∧
      ∀ᶠ x in 𝓝 p,
        (x ∈ ⋃ q ∈ S, {x | ∀ f ∈ q, 0 ≤ f x}) ↔ x - p ∈ C := by
  classical
  let Q (q : Finset (E d →ᵃ[ℝ] ℝ)) : Finset (E d →ₗ[ℝ] ℝ) :=
    (q.filter fun f => f p = 0).image AffineMap.linear
  let S₀ := S.filter fun q => ∀ f ∈ q, 0 ≤ f p
  let C : Set (E d) := ⋃ r ∈ S₀.image Q, {v | ∀ l ∈ r, 0 ≤ l v}
  have hC (v : E d) : v ∈ C ↔
      ∃ q ∈ S, (∀ f ∈ q, 0 ≤ f p) ∧ ∀ f ∈ q, f p = 0 → 0 ≤ f.linear v := by
    simp [C, S₀, Q]
    constructor
    · rintro ⟨q, ⟨hq, hpq⟩, hvq⟩
      exact ⟨q, hq, hpq, fun f hf hf0 => hvq f.linear f hf hf0 rfl⟩
    · rintro ⟨q, hq, hpq, hvq⟩
      refine ⟨q, ⟨hq, hpq⟩, ?_⟩
      rintro l f hf hf0 rfl
      exact hvq f hf hf0
  refine ⟨C, ⟨S₀.image Q, rfl⟩, ?_⟩
  have hsign (f : E d →ᵃ[ℝ] ℝ) : ∀ᶠ x in 𝓝 p,
      (f p < 0 → f x < 0) ∧ (0 < f p → 0 < f x) := by
    have hc := f.continuous_of_finiteDimensional.continuousAt (x := p)
    apply Filter.Eventually.and
    · by_cases hf : f p < 0
      · exact (hc.eventually_lt_const hf).mono fun x hx _ => hx
      · exact Filter.Eventually.of_forall fun x h => (hf h).elim
    · by_cases hf : 0 < f p
      · exact (hc.eventually_const_lt hf).mono fun x hx _ => hx
      · exact Filter.Eventually.of_forall fun x h => (hf h).elim
  have hall : ∀ᶠ x in 𝓝 p, ∀ q ∈ S, ∀ f ∈ q,
      (f p < 0 → f x < 0) ∧ (0 < f p → 0 < f x) :=
    (Filter.eventually_all_finset S).mpr fun q _ =>
      (Filter.eventually_all_finset q).mpr fun f _ => hsign f
  filter_upwards [hall] with x hx
  rw [hC]
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨q, hq, hxq⟩
    refine ⟨q, hq, ?_, ?_⟩
    · intro f hf
      by_contra hn
      exact (not_lt_of_ge (hxq f hf)) ((hx q hq f hf).1 (lt_of_not_ge hn))
    · intro f hf hfp
      have he : f.linear (x - p) = f x - f p := f.linearMap_vsub x p
      rw [he, hfp, sub_zero]
      exact hxq f hf
  · rintro ⟨q, hq, hpq, hvq⟩
    refine ⟨q, hq, ?_⟩
    intro f hf
    rcases eq_or_lt_of_le (hpq f hf) with hfp | hfp
    · have hv := hvq f hf hfp.symm
      have he : f.linear (x - p) = f x - f p := f.linearMap_vsub x p
      simpa [he, hfp.symm] using hv
    · exact ((hx q hq f hf).2 hfp).le

/-- Step 4 of the V4 proof of `tangentCone_polyhedral` (V4 1.0(b)):
"polyhedral cone". Homogeneous half-space inequalities are invariant under
multiplication by a positive scalar, as is a finite union of their intersections. -/
private lemma tangentCone_polyhedral_step4_positive_scaling
    {C : Set (E d)} (hC : IsPolyhedralCone C) {r : ℝ} (hr : 0 < r) (v : E d) :
    r • v ∈ C ↔ v ∈ C := by
  obtain ⟨S, rfl⟩ := hC
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, map_smul, smul_eq_mul,
    mul_nonneg_iff_of_pos_left hr]

open scoped Topology in
/-- Step 5 of the V4 proof of `tangentCone_polyhedral` (V4 1.0(b)):
"its tangent cone at any point is a polyhedral cone". A local conical model
equals the positive-time radial germ in the definition of `tangentCone`. -/
private lemma tangentCone_polyhedral_step5_radial_germ
    {K C : Set (E d)} (p : E d) (hC : IsPolyhedralCone C)
    (hloc : ∀ᶠ x in 𝓝 p, x ∈ K ↔ x - p ∈ C) : tangentCone K p = C := by
  ext v
  have htend : Filter.Tendsto (fun t : ℝ => p + t • v) (𝓝 0) (𝓝 p) := by
    have hc : Continuous (fun t : ℝ => p + t • v) := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), p + t • v ∈ K ↔ t • v ∈ C := by
    simpa only [add_sub_cancel_left] using htend.eventually hloc
  obtain ⟨δ, hδ, hδloc⟩ := Metric.eventually_nhds_iff.mp hev
  constructor
  · rintro ⟨ε, hε, hv⟩
    let t := min ε δ / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have htε : t < ε := by dsimp [t]; linarith [min_le_left ε δ]
    have htδ : t < δ := by dsimp [t]; linarith [min_le_right ε δ]
    have hnear : dist t 0 < δ := by simpa [Real.dist_eq, abs_of_pos ht] using htδ
    exact (tangentCone_polyhedral_step4_positive_scaling hC ht v).mp
      ((hδloc hnear).mp (hv t ht htε))
  · intro hv
    refine ⟨δ, hδ, fun t ht htδ => ?_⟩
    have hnear : dist t 0 < δ := by simpa [Real.dist_eq, abs_of_pos ht] using htδ
    exact (hδloc hnear).mpr
      ((tangentCone_polyhedral_step4_positive_scaling hC ht v).mpr hv)

open scoped Topology in
/-- Step 6 of the V4 proof of `tangentCone_polyhedral` (V4 1.0(b)):
"regular closedness gives nonempty interior". Interior points approach the base
point, and a small open subset of the domain translates into the local model. -/
private lemma tangentCone_polyhedral_step6_solid
    {K C : Set (E d)} (p : E d) (hp : p ∈ closure (interior K))
    (hloc : ∀ᶠ x in 𝓝 p, x ∈ K ↔ x - p ∈ C) : (interior C).Nonempty := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hloc
  obtain ⟨x, hx, hxp⟩ := Metric.mem_closure_iff.mp hp ε hε
  let U := interior K ∩ ball p ε
  have hxU : x ∈ U := ⟨hx, by simpa [dist_comm] using hxp⟩
  have hopen : IsOpen ((fun y : E d => y - p) '' U) :=
    isOpenMap_sub_right p U (isOpen_interior.inter isOpen_ball)
  have hsub : (fun y : E d => y - p) '' U ⊆ C := by
    rintro v ⟨y, hy, rfl⟩
    exact (hball hy.2).mp (interior_subset hy.1)
  exact ⟨x - p, (hopen.subset_interior_iff.mpr hsub) ⟨x, hxU, rfl⟩⟩

/-- G7, V4 1.0(b): local polyhedrality and solidity of the tangent cone. -/
theorem tangentCone_polyhedral (A : PolyManifoldDomain d) (p : E d)
    (hp : p ∈ frontier A.carrier) :
    IsPolyhedralCone (tangentCone A.carrier p) ∧
      (interior (tangentCone A.carrier p)).Nonempty := by
  obtain ⟨S, hS⟩ := tangentCone_polyhedral_step2_halfspace_presentation A.polyhedral
  obtain ⟨C, hC, hloc⟩ := tangentCone_polyhedral_step3_local_cone S p
  rw [← hS] at hloc
  have hcone := tangentCone_polyhedral_step5_radial_germ p hC hloc
  rw [hcone]
  refine ⟨hC, tangentCone_polyhedral_step6_solid p ?_ hloc⟩
  rw [A.regularClosed]
  exact A.compact.isClosed.frontier_subset hp

/-- G1, V4 §1.0 (H1): the finite-convex-hull definition implies compactness. -/
theorem Polyhedron.isCompact {K : Set (E d)} (hK : Polyhedron K) : IsCompact K := by
  sorry

/-- Sym1, V4 5.6: the full group of Euclidean symmetries of a full-dimensional
polyhedron is finite. No boundary manifold condition or orientation restriction
is needed, and the nonempty interior rules out lower-dimensional stabilizers. -/
theorem polyhedron_symmetries_finite (K : Set (E d)) (hK : Polyhedron K)
    (hfull : (interior K).Nonempty) :
    {g : Iso d | g '' K = K}.Finite := by
  sorry

end Enforce
