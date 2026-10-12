import Tilings.Hierarchy

/-!
# The corrected uniform crown-cover lemma (skeleton)

Statements of the nodes of `crowns.tex` (section "A corrected uniform
crown-cover lemma").  All theorems are `sorry` except
`closedConvexHullDiameter`.

## Modelling choices

* **Local tangent cone.**  `localCone A v` is defined directly, for an
  arbitrary set `A`, as the set of points `x` such that an initial piece
  `v + t • (x - v)`, `0 < t < r`, of the ray from `v` through `x` lies in `A`.
  For a polygonal disk `A ∋ v` this is the closed cone `T_v A` of the
  blueprint (whole plane / inward closed halfplane / closed interior wedge,
  all with apex `v`); for `v ∉ A` it is empty.  `polygonLocalCone` is the
  statement that this cone describes `A` near `v`.
* **Pointed crowns** are normalized to centre `0` (as in `IsAllowedCrown`).
  A *catalogue* is a finite set of finite pointed crowns all of whose tiles
  contain `0` (`IsCatalogue`).  A crown `crown S v` is *represented* in `𝒞`
  if its translate to the origin lies in `𝒞`.
* **Macro patches.**  `MacroPatch P` is a finite patch whose support is
  `u +ᵥ θ^j • B_p` for a root form `p`.  Geometric macro edges are the scaled
  maximal straight boundary segments of the root between genuine corners
  (`PolygonalDisk.IsGeometricEdge`): dummy collinear vertices are merged.
* **Diameters.**  `Metric.diam` of an unbounded set is `0`, so every
  diameter hypothesis is accompanied by `Bornology.IsBounded`.
-/

open Set Pointwise Metric

noncomputable section

namespace Tilings

open Substitution

variable {P : Protoset}

/-! ## Genuine corners and geometric edges of a polygonal disk -/

namespace PolygonalDisk

variable (D : PolygonalDisk)

/-- The genuine (non-straight) corners of a polygonal disk. -/
def genuineCorners : Set Pt := D.vertex '' {i | D.IsGenuineVertex i}

/-- `q` is a genuine corner: a listed vertex whose two incident sides are not
collinear. -/
def IsGenuineCorner (q : Pt) : Prop := q ∈ D.genuineCorners

/-- A geometric edge: a nondegenerate straight segment of the boundary joining
two genuine corners.  For a simple polygon such a segment contains no genuine
corner in its relative interior, so these are exactly the maximal merged
edges obtained by erasing collinear listed vertices.  The relation is
symmetric. -/
def IsGeometricEdge (x y : Pt) : Prop :=
  D.IsGenuineCorner x ∧ D.IsGenuineCorner y ∧ x ≠ y ∧ segment ℝ x y ⊆ frontier D.carrier

/-- `q` is a reflex corner with incident geometric edges towards `a` and `b`:
the bisector of the convex angle `∠ a q b` leaves the carrier immediately,
i.e. the convex wedge between the two edges is exterior.  The exterior wedge
angle is then `∠ a q b ∈ (0, π)`. -/
def IsReflexCorner (q a b : Pt) : Prop :=
  D.IsGeometricEdge q a ∧ D.IsGeometricEdge q b ∧ a ≠ b ∧
    ∀ r : ℝ, 0 < r → ∃ s ∈ Ioo (0 : ℝ) r,
      q + s • (‖a - q‖⁻¹ • (a - q) + ‖b - q‖⁻¹ • (b - q)) ∉ D.carrier

end PolygonalDisk

namespace Crowns

/-! ## Local cones, sectors, catalogues (`def:crown-sector`) -/

/-- The closed local tangent cone of `A` at `v` (apex `v`): points `x` such
that the ray from `v` through `x` starts inside `A`. -/
def localCone (A : Set Pt) (v : Pt) : Set Pt :=
  {x | ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Ioo (0 : ℝ) r, v + t • (x - v) ∈ A}

/-- `Ω(K)` for a crown `K` with centre `v`: the union of the local cones at
`v` of the tiles of `K` (including tiles having `v` on an edge). -/
def Omega (K : Set (PlacedTile P)) (v : Pt) : Set Pt :=
  ⋃ A ∈ K, localCone A.carrier v

/-- The sector `Sec(K, r) = B(v, r) ∩ Ω(K)`. -/
def Sec (K : Set (PlacedTile P)) (v : Pt) (r : ℝ) : Set Pt :=
  ball v r ∩ Omega K v

/-- A pointed crown catalogue: finitely many finite pointed crowns, each with
centre `0` contained in every one of its tiles. -/
def IsCatalogue (𝒞 : Set (Set (PlacedTile P))) : Prop :=
  𝒞.Finite ∧ ∀ K ∈ 𝒞, K.Finite ∧ ∀ A ∈ K, (0 : Pt) ∈ A.carrier

/-- `def:crown-sector`: the pointed catalogue of a substitution, i.e. all
allowed full pointed crowns (including incomplete supertile-boundary
crowns), normalized to centre `0`. -/
def pointedCatalogue (τ : Substitution P) : Set (Set (PlacedTile P)) :=
  {K | τ.IsAllowedCrown K}

/-- The full crown of `S` at `v` is represented in `𝒞`. -/
def Represented (𝒞 : Set (Set (PlacedTile P))) (S : Set (PlacedTile P)) (v : Pt) : Prop :=
  translateSet (-v) (crown S v) ∈ 𝒞

/-- All full pointed crowns of `S` (at listed vertices) are represented in `𝒞`. -/
def AllCrownsIn (𝒞 : Set (Set (PlacedTile P))) (S : Set (PlacedTile P)) : Prop :=
  ∀ v, IsVertexOf S v → Represented 𝒞 S v

/-! ## `lem:polygon-local-cone` -/

private lemma crown_mem_segment_iff {a b x : Pt} :
    x ∈ segment ℝ a b ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = a + t • (b - a) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    exact ⟨t, ht0, ht1, rfl⟩
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩

private lemma crown_mem_openSegment_iff {a b x : Pt} :
    x ∈ openSegment ℝ a b ↔
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = a + t • (b - a) := by
  rw [openSegment_eq_image']
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    exact ⟨t, ht0, ht1, rfl⟩
  · rintro ⟨t, ht0, ht1, rfl⟩
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩

private lemma crown_smul_cancel {u : Pt} (hu : u ≠ 0) {s t : ℝ}
    (h : s • u = t • u) : s = t := by
  exact smul_left_injective ℝ hu h

private lemma crown_finRotate_ne_self {n : ℕ} (hn : 2 ≤ n)
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

private lemma crown_endpoint_on_extended_segment {a b v y x : Pt}
    (hab : a ≠ b) (hv : v ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (hvyx : y ∈ openSegment ℝ v x) (hx : x ∉ segment ℝ a b) :
    (a ≠ v ∧ a ∈ segment ℝ v x) ∨
      (b ≠ v ∧ b ∈ segment ℝ v x) := by
  rw [crown_mem_segment_iff] at hv hy
  rw [crown_mem_openSegment_iff] at hvyx
  obtain ⟨s, hs0, hs1, rfl⟩ := hv
  obtain ⟨u, hu0, hu1, hy⟩ := hy
  obtain ⟨t, ht0, ht1, hyt⟩ := hvyx
  let d := b - a
  have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
  have ht : t ≠ 0 := ne_of_gt ht0
  have htx : x - (a + s • d) = t⁻¹ • (y - (a + s • d)) := by
    rw [hyt, add_sub_cancel_left, inv_smul_smul₀ ht]
  have hxform : x = a + (s + (u - s) / t) • d := by
    rw [hy] at htx
    dsimp only [d] at htx ⊢
    rw [← sub_add_cancel x (a + s • (b - a)), htx]
    rw [div_eq_mul_inv]
    module
  have hw : s + (u - s) / t < 0 ∨ 1 < s + (u - s) / t := by
    by_cases h0 : 0 ≤ s + (u - s) / t
    · by_cases h1 : s + (u - s) / t ≤ 1
      · exfalso
        apply hx
        exact crown_mem_segment_iff.mpr
          ⟨s + (u - s) / t, h0, h1, hxform⟩
      · exact Or.inr (lt_of_not_ge h1)
    · exact Or.inl (lt_of_not_ge h0)
  rcases hw with hw | hw
  · left
    constructor
    · intro hav
      have hs : s = 0 := by
        apply crown_smul_cancel hd
        change a = a + s • d at hav
        simpa using congrArg (fun z => z - a) hav.symm
      subst s
      have hdiv : 0 ≤ u / t := div_nonneg hu0 ht0.le
      exact (not_lt_of_ge hdiv) (by simpa using hw)
    · rw [hxform]
      exact mem_segment_iff_wbtw.mpr (by
        simpa [add_comm] using
          (wbtw_smul_vadd_smul_vadd_of_nonneg_of_nonpos
            (R := ℝ) a d hs0 hw.le))
  · right
    constructor
    · intro hbv
      have hs : s = 1 := by
        apply crown_smul_cancel hd
        rw [one_smul]
        have := congrArg (fun z => z - a) hbv.symm
        simpa [d] using this
      subst s
      have hdiv : (u - 1) / t ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le
      nlinarith
    · rw [hxform]
      have hvform : a + s • d = b + (s - 1) • d := by
        dsimp only [d]
        module
      have hxform' : a + (s + (u - s) / t) • d =
          b + (s + (u - s) / t - 1) • d := by
        dsimp only [d]
        module
      rw [hvform, hxform']
      exact mem_segment_iff_wbtw.mpr (by
        simpa [add_comm] using
          (wbtw_smul_vadd_smul_vadd_of_nonpos_of_nonneg
            (R := ℝ) b d (by linarith) (by linarith)))

private lemma crown_isCompact_segment (a b : Pt) :
    IsCompact (segment ℝ a b) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

private lemma crown_frontier_subset_of_isClosed {A : Set Pt}
    (hA : IsClosed A) : frontier A ⊆ A := by
  exact frontier_subset_closure.trans_eq hA.closure_eq

private lemma crown_sbtw_of_mem_openSegment {a b x : Pt} (hab : a ≠ b)
    (hx : x ∈ openSegment ℝ a b) : Sbtw ℝ a x b := by
  refine ⟨mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ a b hx), ?_, ?_⟩
  · intro hxa
    subst x
    exact hab ((left_mem_openSegment_iff).mp hx)
  · intro hxb
    subst x
    exact hab ((right_mem_openSegment_iff).mp hx)

private lemma crown_mem_openSegment_of_sbtw {a b x : Pt}
    (hx : Sbtw ℝ a x b) : x ∈ openSegment ℝ a b := by
  exact mem_openSegment_of_ne_left_right hx.left_ne hx.right_ne
    hx.wbtw.mem_segment

private lemma crown_frontier_meets_segment {A : Set Pt} (hA : IsClosed A)
    {p q : Pt} (hp : p ∈ A) (hq : q ∉ A) :
    (segment ℝ p q ∩ frontier A).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hsub : segment ℝ p q ⊆ interior A ∪ Aᶜ := by
    intro z hz
    by_cases hzA : z ∈ A
    · left
      by_contra hzi
      have hzf : z ∈ frontier A := by
        rw [frontier, hA.closure_eq]
        exact ⟨hzA, hzi⟩
      have : z ∈ segment ℝ p q ∩ frontier A := ⟨hz, hzf⟩
      rwa [hne] at this
    · exact Or.inr hzA
  have hd : Disjoint (interior A) Aᶜ := by
    rw [Set.disjoint_left]
    exact fun _ hz hzA => hzA (interior_subset hz)
  rcases (convex_segment p q).isPreconnected.subset_or_subset
      isOpen_interior hA.isOpen_compl hd hsub with h | h
  · exact hq (interior_subset (h (right_mem_segment ℝ p q)))
  · exact h (left_mem_segment ℝ p q) hp

private lemma crown_side_subset_carrier (D : PolygonalDisk)
    (i : Fin D.n) : D.side i ⊆ D.carrier := by
  apply (show D.side i ⊆ frontier D.carrier from ?_).trans
    (crown_frontier_subset_of_isClosed D.compact.isClosed)
  rw [D.frontier_eq]
  exact subset_iUnion (fun j => D.side j) i

private lemma crown_local_boundary (D : PolygonalDisk) {v : Pt} :
    ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ ball v r, x ∈ frontier D.carrier →
        ∃ i : Fin D.n, v ∈ D.side i ∧ x ∈ D.side i ∧
          ∀ y ∈ ball v r, x ∈ openSegment ℝ v y → y ∈ D.side i := by
  let K : Set Pt :=
    (⋃ i ∈ {i : Fin D.n | v ∉ D.side i}, D.side i) ∪
      (D.vertexSet \ {v})
  have hKclosed : IsClosed K := by
    apply IsClosed.union
    · exact Set.Finite.isClosed_biUnion (Set.toFinite _)
        (fun i _ => (crown_isCompact_segment _ _).isClosed)
    · exact (Set.finite_range D.vertex).diff.isClosed
  have hvK : v ∉ K := by
    simp [K]
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.mp hKclosed.isOpen_compl v hvK
  refine ⟨r, hr, ?_⟩
  intro x hxr hxf
  rw [D.frontier_eq] at hxf
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxf
  have hvi : v ∈ D.side i := by
    by_contra hvi
    apply hrK hxr
    left
    exact Set.mem_iUnion₂.mpr ⟨i, hvi, hxi⟩
  refine ⟨i, hvi, hxi, ?_⟩
  intro y hyr hxy
  by_contra hyi
  obtain h | h := crown_endpoint_on_extended_segment
    (show D.vertex i ≠ D.vertex (finRotate D.n i) from by
      intro heq
      have := D.vertex_injective heq
      have hn : finRotate D.n i ≠ i :=
        crown_finRotate_ne_self (by have := D.three_le; omega) i
      exact hn this.symm)
    hvi hxi hxy hyi
  · apply hrK ((convex_ball v r).segment_subset (Metric.mem_ball_self hr) hyr h.2)
    right
    exact ⟨⟨i, rfl⟩, h.1⟩
  · apply hrK ((convex_ball v r).segment_subset (Metric.mem_ball_self hr) hyr h.2)
    right
    exact ⟨⟨finRotate D.n i, rfl⟩, h.1⟩

set_option maxHeartbeats 800000 in
private lemma crown_local_cone_eq (D : PolygonalDisk) {v : Pt}
    (hv : v ∈ D.carrier) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball v r,
      (x ∈ D.carrier ↔ x ∈ localCone D.carrier v) := by
  obtain ⟨r, hr, hboundary⟩ := crown_local_boundary D (v := v)
  have hclosed : IsClosed D.carrier := D.compact.isClosed
  have hfront := crown_frontier_subset_of_isClosed hclosed
  refine ⟨r, hr, ?_⟩
  intro x hxr
  constructor
  · intro hxD
    refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    let z := v + t • (x - v)
    have hzx : z ∈ openSegment ℝ v x :=
      crown_mem_openSegment_iff.mpr ⟨t, ht.1, ht.2, rfl⟩
    by_contra hzD
    change z ∉ D.carrier at hzD
    obtain ⟨y, hyseg, hyf⟩ :=
      crown_frontier_meets_segment hclosed hxD hzD
    have hzxr : z ∈ ball v r :=
      (convex_ball v r).segment_subset (Metric.mem_ball_self hr) hxr
        (openSegment_subset_segment ℝ v x hzx)
    have hyr : y ∈ ball v r :=
      (convex_ball v r).segment_subset hxr hzxr hyseg
    obtain ⟨i, hvi, hyi, hext⟩ := hboundary y hyr hyf
    have hxside : x ∈ D.side i := by
      by_cases hyx : y = x
      · simpa [hyx] using hyi
      · apply hext x hxr
        have hyz : y ≠ z := by
          intro hyz'
          subst y
          apply hzD
          exact hfront hyf
        have hyopen : y ∈ openSegment ℝ z x := by
          rw [segment_symm] at hyseg
          exact mem_openSegment_of_ne_left_right (Ne.symm hyz) (Ne.symm hyx) hyseg
        have hvx : v ≠ x := by
          intro hvx
          subst x
          apply hzD
          simpa [z] using hv
        exact crown_mem_openSegment_of_sbtw
          ((crown_sbtw_of_mem_openSegment hvx hzx).trans_right
            (crown_sbtw_of_mem_openSegment (by
              intro h
              apply hzD
              rw [h]
              exact hxD) hyopen))
    apply hzD
    apply crown_side_subset_carrier D i
    change z ∈ segment ℝ (D.vertex i) (D.vertex (finRotate D.n i))
    change v ∈ segment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) at hvi
    change x ∈ segment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) at hxside
    exact (convex_segment (D.vertex i) (D.vertex (finRotate D.n i))).segment_subset
      hvi hxside (openSegment_subset_segment ℝ v x hzx)
  · rintro ⟨rho, hrho, hcone⟩
    by_contra hxD
    let t : ℝ := min (1 / 2) (rho / 2)
    have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
    have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have htrho : t < rho :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith)
    let z := v + t • (x - v)
    have hzx : z ∈ openSegment ℝ v x :=
      crown_mem_openSegment_iff.mpr ⟨t, ht0, ht1, rfl⟩
    have hzD : z ∈ D.carrier := hcone t ⟨ht0, htrho⟩
    obtain ⟨y, hyseg, hyf⟩ :=
      crown_frontier_meets_segment hclosed hzD hxD
    have hzxr : z ∈ ball v r :=
      (convex_ball v r).segment_subset (Metric.mem_ball_self hr) hxr
        (openSegment_subset_segment ℝ v x hzx)
    have hyr : y ∈ ball v r :=
      (convex_ball v r).segment_subset hzxr hxr hyseg
    have hyx : y ≠ x := by
      intro hyx'
      subst y
      exact hxD (hfront hyf)
    have hvx : v ≠ x := by
      intro hvx
      exact hxD (hvx ▸ hv)
    have hyopen : y ∈ openSegment ℝ v x := by
      by_cases hyz : y = z
      · simpa [hyz] using hzx
      · have hyopen' : y ∈ openSegment ℝ z x :=
          mem_openSegment_of_ne_left_right (Ne.symm hyz) (Ne.symm hyx) hyseg
        exact crown_mem_openSegment_of_sbtw
          ((crown_sbtw_of_mem_openSegment hvx hzx).trans_right
            (crown_sbtw_of_mem_openSegment (by
              intro h
              apply hxD
              rw [← h]
              exact hzD) hyopen'))
    obtain ⟨i, -, -, hext⟩ := hboundary y hyr hyf
    exact hxD (crown_side_subset_carrier D i (hext x hxr hyopen))

/-- `lem:polygon-local-cone`: a polygonal disk agrees with its local cone in a
small ball around each of its points. -/
theorem polygonLocalCone (D : PolygonalDisk) {v : Pt} (hv : v ∈ D.carrier) :
    ∃ r : ℝ, 0 < r ∧ D.carrier ∩ ball v r = localCone D.carrier v ∩ ball v r := by
  obtain ⟨r, hr, hlocal⟩ := crown_local_cone_eq D hv
  refine ⟨r, hr, ?_⟩
  ext x
  constructor
  · rintro ⟨hxD, hxr⟩
    exact ⟨(hlocal x hxr).mp hxD, hxr⟩
  · rintro ⟨hxc, hxr⟩
    exact ⟨(hlocal x hxr).mpr hxc, hxr⟩

/-- `lem:polygon-local-cone` for placed tiles. -/
theorem polygonLocalCone_tile (A : PlacedTile P) {v : Pt} (hv : v ∈ A.carrier) :
    ∃ r : ℝ, 0 < r ∧ A.carrier ∩ ball v r = localCone A.carrier v ∩ ball v r := by
  sorry

/-! ## `lem:sector-radius` -/

/-- The conclusion of `lem:sector-radius` for constants `r` (`r_*`) and `δ`
(`δ_*`): for every catalogue crown placed at an arbitrary centre `v`, the
crown agrees with its cone union inside `B(v, r)`, and every listed vertex
`w ≠ v` of its tiles is at distance `≥ δ` from `v`. -/
def SectorRadiusProperty (𝒞 : Set (Set (PlacedTile P))) (r δ : ℝ) : Prop :=
  ∀ K ∈ 𝒞, ∀ v : Pt,
    support (translateSet v K) ∩ ball v r = Omega (translateSet v K) v ∩ ball v r ∧
    ∀ A ∈ translateSet v K, ∀ w ∈ A.vertexSet, w ≠ v → δ ≤ dist w v

/-- `lem:sector-radius`: uniform sector radius `r_*` and vertex separation
`δ_*` for a finite catalogue. -/
theorem uniformSectorRadius {𝒞 : Set (Set (PlacedTile P))} (h𝒞 : IsCatalogue 𝒞) :
    ∃ r : ℝ, 0 < r ∧ ∃ δ : ℝ, 0 < δ ∧ SectorRadiusProperty 𝒞 r δ := by
  sorry

/-! ## Macro patches and their geometric boundary (`def:macro-boundary`) -/

/-- A finite patch `M` with disjoint interiors whose support is the macro
polygon `R = u + θ^j B_p`. -/
structure MacroPatch (P : Protoset) where
  tiles : Set (PlacedTile P)
  finite : tiles.Finite
  disjoint : DisjointInteriors tiles
  θ : ℝ
  one_lt : 1 < θ
  j : ℕ
  root : P.Form
  offset : Pt
  support_eq : support tiles = offset +ᵥ (θ ^ j) • (P.disk root).carrier

namespace MacroPatch

variable (M : MacroPatch P)

/-- The similarity `x ↦ u + θ^j x` from the root polygon onto `R`. -/
def map (x : Pt) : Pt := M.offset + (M.θ ^ M.j) • x

/-- The macro polygon `R`. -/
def region : Set Pt := support M.tiles

end MacroPatch

/-- `def:macro-boundary`: the geometric macro edges of `M`, as ordered pairs
of endpoints: images of the merged (geometric) edges of the root polygon. -/
def geometricMacroBoundary (M : MacroPatch P) : Set (Pt × Pt) :=
  {e | ∃ x y, (P.disk M.root).IsGeometricEdge x y ∧ e = (M.map x, M.map y)}

/-- `def:macro-boundary`: the genuine macro corners of `M`. -/
def genuineMacroCorners (M : MacroPatch P) : Set Pt :=
  M.map '' (P.disk M.root).genuineCorners

/-- A supertile is finite. -/
theorem supertile_finite (τ : Substitution P) (n : ℕ) (p : P.Form) :
    (τ.supertile n p).Finite := by
  induction' n with n ih
  · exact finite_singleton (⟨p, 0⟩ : PlacedTile P)
  · change (τ.decompose (τ.decomposeIter n {⟨p, 0⟩})).Finite
    apply Finite.biUnion ih
    intro A _
    exact Finite.image _ (τ.rule A.form).finite

/-- A supertile has pairwise disjoint interiors. -/
theorem supertile_disjoint (τ : Substitution P) (n : ℕ) (p : P.Form) :
    DisjointInteriors (τ.supertile n p) := by
  sorry

/-- The support of a supertile in the `MacroPatch` normal form. -/
theorem supertile_support_eq (τ : Substitution P) (n : ℕ) (p : P.Form) :
    support (τ.supertile n p) = (0 : Pt) +ᵥ (τ.θ ^ n) • (P.disk p).carrier := by
  sorry

/-- The supertile `τ^n p` as a macro patch. -/
def supertileMacro (τ : Substitution P) (n : ℕ) (p : P.Form) : MacroPatch P where
  tiles := τ.supertile n p
  finite := supertile_finite τ n p
  disjoint := supertile_disjoint τ n p
  θ := τ.θ
  one_lt := τ.one_lt
  j := n
  root := p
  offset := 0
  support_eq := supertile_support_eq τ n p

/-! ## `lem:macrocorner` -/

/-- `lem:macrocorner`: every genuine macro corner is a listed vertex of at
least one child tile. -/
theorem macrocornerIsChildVertex (M : MacroPatch P) {q : Pt}
    (hq : q ∈ genuineMacroCorners M) : IsVertexOf M.tiles q := by
  sorry

/-! ## `lem:endpoint-gap` -/

/-- `lem:endpoint-gap`: with `h = min r_* δ_*`, a child vertex in the relative
interior of a geometric macro edge incident to the genuine macro corner `q`
is at distance at least `h` from `q`. -/
theorem incidentMacroEdgeVertexGap {𝒞 : Set (Set (PlacedTile P))} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hrδ : SectorRadiusProperty 𝒞 r δ)
    (M : MacroPatch P) (hM : AllCrownsIn 𝒞 M.tiles) {q x : Pt}
    (hqx : (q, x) ∈ geometricMacroBoundary M ∨ (x, q) ∈ geometricMacroBoundary M)
    {v : Pt} (hv : IsVertexOf M.tiles v) (hvx : v ∈ openSegment ℝ q x) :
    min r δ ≤ dist v q := by
  sorry

/-! ## `def:crown-separation` -/

/-- `def:crown-separation`: positive root separation constants.
* `ν` bounds from below the distance from a genuine root corner to any
  geometric root edge not incident to it;
* `lam` (`λ`) bounds from below the distance between two geometric root
  edges without common endpoint;
* `μ` (`μ_*`) satisfies `0 < μ ≤ π/2` and `μ ≤ β` for the exterior wedge
  angle `β = ∠ a q b` of every reflex root corner. -/
structure RootSeparation (P : Protoset) where
  ν : ℝ
  lam : ℝ
  μ : ℝ
  ν_pos : 0 < ν
  lam_pos : 0 < lam
  μ_pos : 0 < μ
  μ_le : μ ≤ Real.pi / 2
  ν_le : ∀ (p : P.Form) (q x y : Pt), (P.disk p).IsGenuineCorner q →
    (P.disk p).IsGeometricEdge x y → q ≠ x → q ≠ y →
    ∀ z ∈ segment ℝ x y, ν ≤ dist q z
  lam_le : ∀ (p : P.Form) (x y x' y' : Pt), (P.disk p).IsGeometricEdge x y →
    (P.disk p).IsGeometricEdge x' y' → Disjoint ({x, y} : Set Pt) {x', y'} →
    ∀ z ∈ segment ℝ x y, ∀ z' ∈ segment ℝ x' y', lam ≤ dist z z'
  μ_le_reflex : ∀ (p : P.Form) (q a b : Pt), (P.disk p).IsReflexCorner q a b →
    μ ≤ EuclideanGeometry.angle a q b

/-- Positive root separation constants exist (finite minima of distances
between disjoint compact sets; `1` for empty collections). -/
theorem exists_rootSeparation (P : Protoset) : Nonempty (RootSeparation P) := by
  sorry

/-- `def:crown-separation`: a fixed choice of root separation constants. -/
def rootSeparationConstants (P : Protoset) : RootSeparation P :=
  Classical.choice (exists_rootSeparation P)

/-! ## `lem:ray-bound` -/

/-- `lem:ray-bound`: for unit vectors `a, b` and `t > 0`, the distance from
`q + t a` to the ray `q + ℝ_{≥0} b` is `t sin β` if `β = ∠(a, b) ≤ π/2` and
`t` otherwise. -/
theorem distanceToReflexBoundaryRay (q a b : Pt) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {t : ℝ} (ht : 0 < t) :
    infDist (q + t • a) ((fun s : ℝ => q + s • b) '' Ici 0) =
      if InnerProductGeometry.angle a b ≤ Real.pi / 2 then
        t * Real.sin (InnerProductGeometry.angle a b)
      else t := by
  sorry

/-- `lem:ray-bound`, the form used later: if `0 < μ ≤ π/2` and `μ ≤ β`, the
distance is at least `t sin μ`. -/
theorem distanceToReflexBoundaryRay_ge (q a b : Pt) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {t μ : ℝ} (ht : 0 < t) (hμ0 : 0 < μ) (hμ : μ ≤ Real.pi / 2)
    (hβ : μ ≤ InnerProductGeometry.angle a b) :
    t * Real.sin μ ≤ infDist (q + t • a) ((fun s : ℝ => q + s • b) '' Ici 0) := by
  sorry

/-! ## `lem:relative-crown-ball` -/

/-- The radius `d = ½ min {r_*, ν, λ, h sin μ_*}` with `h = min r_* δ_*`. -/
def crownRadius (r δ : ℝ) (R : RootSeparation P) : ℝ :=
  (1 / 2) * min (min r R.ν) (min R.lam (min r δ * Real.sin R.μ))

/-- `lem:relative-crown-ball`: for every child vertex `v` of a macro patch
whose crowns are represented,
`R ∩ B(v, d) ⊆ Ω(K_M(v)) ∩ B(v, d) ⊆ ⋃ K_M(v)`. -/
theorem uniformRelativeCrownBall {𝒞 : Set (Set (PlacedTile P))} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hrδ : SectorRadiusProperty 𝒞 r δ) (R : RootSeparation P)
    (M : MacroPatch P) (hM : AllCrownsIn 𝒞 M.tiles) {v : Pt} (hv : IsVertexOf M.tiles v) :
    support M.tiles ∩ ball v (crownRadius r δ R) ⊆
        Omega (crown M.tiles v) v ∩ ball v (crownRadius r δ R) ∧
      Omega (crown M.tiles v) v ∩ ball v (crownRadius r δ R) ⊆
        support (crown M.tiles v) := by
  sorry

/-! ## `lem:trimmed-edge-ball` -/

/-- `lem:trimmed-edge-ball`: there is `η > 0` (depending on `P` and `d`) such
that if two placed tiles with disjoint interiors have collinear listed sides
through a common point `e` at distance `≥ d/2` from the endpoints of both
sides, then `B(e, η) ⊆ A ∪ B`.  (Collinearity plus disjoint interiors forces
the overlap near `e` and the opposite local sides.) -/
theorem trimmedEdgeTwoTileBall {d : ℝ} (hd : 0 < d) :
    ∃ η : ℝ, 0 < η ∧ ∀ (A B : PlacedTile P),
      Disjoint (interior A.carrier) (interior B.carrier) →
      ∀ (i : Fin (P.disk A.form).n) (j : Fin (P.disk B.form).n) (e : Pt),
        e ∈ A.side i → e ∈ B.side j →
        Collinear ℝ ({A.vertex i, A.vertex (finRotate _ i),
          B.vertex j, B.vertex (finRotate _ j)} : Set Pt) →
        d / 2 ≤ dist e (A.vertex i) → d / 2 ≤ dist e (A.vertex (finRotate _ i)) →
        d / 2 ≤ dist e (B.vertex j) → d / 2 ≤ dist e (B.vertex (finRotate _ j)) →
        ball e η ⊆ A.carrier ∪ B.carrier := by
  sorry

/-! ## `lem:exterior-excursion` -/

/-- `lem:exterior-excursion`: a bounded convex set `H` of diameter less than
`min {λ, d sin(μ_*/2)}` all of whose points are at distance `≥ d/2` from
every child vertex meets the macro polygon in a convex set. -/
theorem noShortExteriorExcursion (R : RootSeparation P) {d : ℝ} (hd : 0 < d)
    (M : MacroPatch P) {H : Set Pt} (hH : Convex ℝ H) (hb : Bornology.IsBounded H)
    (hdiam : diam H < min R.lam (d * Real.sin (R.μ / 2)))
    (hfar : ∀ x ∈ H, ∀ v, IsVertexOf M.tiles v → d / 2 ≤ dist x v) :
    Convex ℝ (H ∩ support M.tiles) := by
  sorry

/-! ## `lem:crown-convexification` -/

/-- `lem:crown-convexification`: the closed convex hull has the same diameter
(in particular, no greater). -/
theorem closedConvexHullDiameter (S : Set Pt) :
    diam (closedConvexHull ℝ S) = diam S := by
  rw [closedConvexHull_eq_closure_convexHull, Metric.diam_closure, convexHull_diam]

/-! ## `lem:crown-cover-plane`, `lem:crown-cover-supertile` -/

/-- `lem:crown-cover-plane`: there is `ε > 0` such that, in every plane tiling
whose full pointed crowns are represented in the catalogue, every bounded set
of diameter `< ε` lies in the support of one full crown. -/
theorem uniformCrownCoverPlane {𝒞 : Set (Set (PlacedTile P))} (h𝒞 : IsCatalogue 𝒞) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T : PlaneTiling P, AllCrownsIn 𝒞 T.tiles →
      ∀ S : Set Pt, Bornology.IsBounded S → diam S < ε →
        ∃ v, IsVertexOf T.tiles v ∧ S ⊆ support (crown T.tiles v) := by
  sorry

/-- `lem:crown-cover-supertile`: there is `ε > 0` such that for every macro
patch whose full pointed crowns (including incomplete boundary crowns) are
represented, every bounded `S` of diameter `< ε` has `S ∩ R` inside the
support of one full crown of the patch. -/
theorem uniformCrownCoverSupertile {𝒞 : Set (Set (PlacedTile P))} (h𝒞 : IsCatalogue 𝒞) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : MacroPatch P, AllCrownsIn 𝒞 M.tiles →
      ∀ S : Set Pt, Bornology.IsBounded S → diam S < ε →
        ∃ v, IsVertexOf M.tiles v ∧ S ∩ support M.tiles ⊆ support (crown M.tiles v) := by
  sorry

/-! ## `lem:pointed-flc` -/

/-- The article's unpointed FLC: finitely many allowed full crown patches up
to translation (the centre is forgotten). -/
def UnpointedFLC (τ : Substitution P) : Prop :=
  ∃ 𝒦 : Set (Set (PlacedTile P)), 𝒦.Finite ∧
    ∀ (n : ℕ) (p : P.Form) (w : Pt), IsVertexOf (τ.supertile n p) w →
      ∃ K ∈ 𝒦, ∃ u : Pt, crown (τ.supertile n p) w = translateSet u K

/-- `lem:pointed-flc`: finitely many unpointed translation classes of allowed
crowns give finitely many pointed ones. -/
theorem pointedFLCOfFLC (τ : Substitution P) (h : UnpointedFLC τ) : τ.FLC := by
  sorry

/-- Under (pointed) FLC the allowed crowns form a catalogue. -/
theorem isCatalogue_pointedCatalogue (τ : Substitution P) (h : τ.FLC) :
    IsCatalogue (pointedCatalogue τ) := by
  refine ⟨h, fun K hK => ?_⟩
  rcases hK with ⟨n, p, w, _hw, rfl⟩
  constructor
  · apply Set.Finite.image
    exact (supertile_finite τ n p).subset (fun x hx => hx.1)
  · rintro A ⟨B, hB, rfl⟩
    have hwB : w ∈ B.carrier := hB.2
    show (0 : Pt) ∈ (B.translate (-w)).carrier
    have : (B.translate (-w)).carrier = -w +ᵥ B.carrier := by
      dsimp [PlacedTile.carrier, PlacedTile.translate]
      rw [← vadd_assoc, vadd_eq_add]
    rw [this]
    exact ⟨w, hwB, by simp [vadd_eq_add]⟩

/-! ## `thm:corrected-crown-cover` -/

/-- `thm:corrected-crown-cover`: under FLC there is one `ε > 0` such that
(1) in every plane tiling all of whose full pointed crowns are allowed, every
bounded set of diameter `< ε` is covered by one full crown, and (2) in every
supertile `τ^n p`, every bounded `S` of diameter `< ε` has `S ∩ |τ^n p|`
covered by one full crown of the supertile. -/
theorem flcUniformCrownCover (τ : Substitution P) (h : τ.FLC) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ T : PlaneTiling P,
        (∀ v, IsVertexOf T.tiles v → τ.IsAllowedCrown (translateSet (-v) (crown T.tiles v))) →
        ∀ S : Set Pt, Bornology.IsBounded S → diam S < ε →
          ∃ v, IsVertexOf T.tiles v ∧ S ⊆ support (crown T.tiles v)) ∧
      (∀ (n : ℕ) (p : P.Form) (S : Set Pt), Bornology.IsBounded S → diam S < ε →
        ∃ v, IsVertexOf (τ.supertile n p) v ∧
          S ∩ support (τ.supertile n p) ⊆ support (crown (τ.supertile n p) v)) := by
  sorry

end Crowns

end Tilings

end
