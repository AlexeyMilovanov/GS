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

private lemma polygonLocalCone_tile_localCone_vadd
    (c : Pt) (B : Set Pt) (v : Pt) :
    localCone (c +ᵥ B) (c + v) = c +ᵥ localCone B v := by
  ext x
  simp only [localCone, mem_setOf_eq, mem_vadd_set_iff_neg_vadd_mem,
    vadd_eq_add]
  have hpoint : ∀ t : ℝ,
      -c + (c + v + t • (x - (c + v))) = v + t • (-c + x - v) := by
    intro t
    abel_nf
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun t ht => hpoint t ▸ h t ht⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun t ht => (hpoint t).symm ▸ h t ht⟩

private lemma polygonLocalCone_tile_polygonLocalCone_vadd
    (c : Pt) (B : Set Pt) (v : Pt) (r : ℝ) :
    B ∩ ball v r = localCone B v ∩ ball v r ↔
      (c +ᵥ B) ∩ ball (c + v) r =
        localCone (c +ᵥ B) (c + v) ∩ ball (c + v) r := by
  rw [polygonLocalCone_tile_localCone_vadd, ← vadd_eq_add]
  have hball : ball (c +ᵥ v) r = c +ᵥ ball v r := by
    ext x
    simp only [mem_ball, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    have hdist : dist x (c + v) = dist (-c + x) v := by
      rw [dist_eq_norm, dist_eq_norm]
      have hsub : x - (c + v) = -c + x - v := by
        abel_nf
      rw [hsub]
    exact Iff.of_eq (congrArg (fun y => y < r) hdist)
  rw [hball]
  have hinj : Function.Injective (fun x : Pt => c +ᵥ x) :=
    add_right_injective c
  have hB : c +ᵥ B = (fun x => c +ᵥ x) '' B := by rfl
  have hrball : c +ᵥ ball v r = (fun x => c +ᵥ x) '' ball v r := by rfl
  have hcone : c +ᵥ localCone B v =
      (fun x => c +ᵥ x) '' localCone B v := by
    rfl
  rw [hB, hrball, hcone, ← image_inter hinj, ← image_inter hinj]
  exact ⟨fun h => by rw [h], fun h => hinj.image_injective h⟩

/-- `lem:polygon-local-cone` for placed tiles. -/
theorem polygonLocalCone_tile (A : PlacedTile P) {v : Pt} (hv : v ∈ A.carrier) :
    ∃ r : ℝ, 0 < r ∧ A.carrier ∩ ball v r = localCone A.carrier v ∩ ball v r := by
  have hv' : -A.anchor + v ∈ (P.disk A.form).carrier := by
    have h : v ∈ A.anchor +ᵥ (P.disk A.form).carrier := hv
    rwa [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at h
  obtain ⟨r, hr, heq⟩ := polygonLocalCone (P.disk A.form) hv'
  use r, hr
  have hv_eq : v = A.anchor + (-A.anchor + v) := by
    abel_nf
  have hrewrite :
      A.carrier ∩ ball v r = localCone A.carrier v ∩ ball v r ↔
        A.carrier ∩ ball (A.anchor + (-A.anchor + v)) r =
          localCone A.carrier (A.anchor + (-A.anchor + v)) ∩
            ball (A.anchor + (-A.anchor + v)) r := by
    rw [← hv_eq]
  rw [hrewrite, PlacedTile.carrier]
  have htranslate := polygonLocalCone_tile_polygonLocalCone_vadd
    A.anchor (P.disk A.form).carrier (-A.anchor + v) r
  rw [← htranslate]
  exact heq

/-! ## `lem:sector-radius` -/

/-- The conclusion of `lem:sector-radius` for constants `r` (`r_*`) and `δ`
(`δ_*`): for every catalogue crown placed at an arbitrary centre `v`, the
crown agrees with its cone union inside `B(v, r)`, and every listed vertex
`w ≠ v` of its tiles is at distance `≥ δ` from `v`. -/
def SectorRadiusProperty (𝒞 : Set (Set (PlacedTile P))) (r δ : ℝ) : Prop :=
  ∀ K ∈ 𝒞, ∀ v : Pt,
    support (translateSet v K) ∩ ball v r = Omega (translateSet v K) v ∩ ball v r ∧
    ∀ A ∈ translateSet v K, ∀ w ∈ A.vertexSet, w ≠ v → δ ≤ dist w v


/-- Step 2 of the blueprint proof of `uniformSectorRadius`: For a finite catalogue, there is a
uniform radius `r_* > 0`. -/
private lemma uniformSectorRadius_step2_catalogue_radius {𝒞 : Set (Set (PlacedTile P))}
    (h𝒞 : IsCatalogue 𝒞) : ∃ r : ℝ, 0 < r ∧ ∀ K ∈ 𝒞, ∀ A ∈ K,
      A.carrier ∩ ball (0 : Pt) r = localCone A.carrier 0 ∩ ball (0 : Pt) r := by
  let S : Set (PlacedTile P) := ⋃ K ∈ 𝒞, K
  have hS_fin : S.Finite :=
    Set.Finite.biUnion h𝒞.1 (fun K hK => (h𝒞.2 K hK).1)
  have H : ∀ A ∈ S, ∃ r : ℝ, 0 < r ∧
      A.carrier ∩ ball (0 : Pt) r =
        localCone A.carrier 0 ∩ ball (0 : Pt) r := by
    intro A hA
    rw [Set.mem_iUnion₂] at hA
    rcases hA with ⟨K, hK, hAK⟩
    have hA0 : (0 : Pt) ∈ A.carrier := h𝒞.2 K hK |>.2 A hAK
    exact polygonLocalCone_tile A hA0
  choose f hf1 hf2 using H
  by_cases hS : S.Nonempty
  · let fs := hS_fin.toFinset
    have hfs : fs.Nonempty := by
      rwa [Set.Finite.toFinset_nonempty]
    let f' (A : fs) : ℝ :=
      f A.val (Set.Finite.mem_toFinset hS_fin |>.mp A.property)
    have hf'_pos : ∀ A : fs, 0 < f' A := fun A => hf1 A.val _
    use fs.attach.inf' (Finset.attach_nonempty_iff.mpr hfs) f'
    constructor
    · apply (Finset.lt_inf'_iff _).mpr
      intro a _
      exact hf'_pos a
    · intro K hK A hA
      have hAS : A ∈ S := Set.mem_iUnion₂.mpr ⟨K, hK, hA⟩
      have hAfs : A ∈ fs :=
        Set.Finite.mem_toFinset hS_fin |>.mpr hAS
      have hle :
          fs.attach.inf' (Finset.attach_nonempty_iff.mpr hfs) f' ≤
            f A hAS := by
        have Hmem : (⟨A, hAfs⟩ : fs) ∈ fs.attach :=
          Finset.mem_attach _ _
        exact Finset.inf'_le _ Hmem
      have H2 : A.carrier ∩ ball (0 : Pt) (f A hAS) =
          localCone A.carrier 0 ∩ ball (0 : Pt) (f A hAS) :=
        hf2 A hAS
      have H3 :
          ball (0 : Pt)
              (fs.attach.inf' (Finset.attach_nonempty_iff.mpr hfs) f') ⊆
            ball (0 : Pt) (f A hAS) :=
        ball_subset_ball hle
      ext x
      constructor
      · rintro ⟨hx1, hx2⟩
        have hx_in_big :
            x ∈ A.carrier ∩ ball (0 : Pt) (f A hAS) :=
          ⟨hx1, H3 hx2⟩
        rw [H2] at hx_in_big
        exact ⟨hx_in_big.1, hx2⟩
      · rintro ⟨hx1, hx2⟩
        have hx_in_big :
            x ∈ localCone A.carrier 0 ∩ ball (0 : Pt) (f A hAS) :=
          ⟨hx1, H3 hx2⟩
        rw [← H2] at hx_in_big
        exact ⟨hx_in_big.1, hx2⟩
  · use 1
    constructor
    · linarith
    · intro K hK A hA
      exfalso
      apply hS
      use A
      rw [Set.mem_iUnion₂]
      exact ⟨K, hK, hA⟩

/-- Step 3 of the blueprint proof of `uniformSectorRadius`: For a finite catalogue, there is a
uniform vertex separation `δ_* > 0`. -/
private lemma uniformSectorRadius_step3_catalogue_separation {𝒞 : Set (Set (PlacedTile P))}
    (h𝒞 : IsCatalogue 𝒞) : ∃ δ : ℝ, 0 < δ ∧ ∀ K ∈ 𝒞, ∀ A ∈ K, ∀ w ∈ A.vertexSet,
      w ≠ (0 : Pt) → δ ≤ dist w (0 : Pt) := by
  let D : Set ℝ := {d | ∃ K ∈ 𝒞, ∃ A ∈ K, ∃ w ∈ A.vertexSet, w ≠ (0 : Pt) ∧ d = dist w (0 : Pt)}
  have hD_fin : D.Finite := by
    have h1 : 𝒞.Finite := h𝒞.1
    let W : Set Pt := ⋃ K ∈ 𝒞, ⋃ A ∈ K, (A : PlacedTile P).vertexSet
    have hW_fin : W.Finite := by
      refine h1.biUnion fun K hK => ?_
      have hK_fin : K.Finite := (h𝒞.2 K hK).1
      refine hK_fin.biUnion fun A _ => ?_
      exact finite_range _
    have hD_sub : D ⊆ (fun w => dist w (0 : Pt)) '' W := by
      rintro d ⟨K, hK, A, hA, w, hw, _, rfl⟩
      refine ⟨w, ?_, rfl⟩
      simp only [W, mem_iUnion]
      exact ⟨K, hK, A, hA, hw⟩
    exact hW_fin.image _ |>.subset hD_sub
  have hd_pos : ∀ d ∈ D, 0 < (d : ℝ) := by
    rintro d ⟨_, _, _, _, _, _, hne, rfl⟩
    exact dist_pos.mpr hne
  rcases eq_empty_or_nonempty D with hD_emp | hD_nemp
  · use 1
    refine ⟨by norm_num, fun K hK A hA w hw hne => ?_⟩
    exfalso
    have : dist w (0 : Pt) ∈ D := ⟨K, hK, A, hA, w, hw, hne, rfl⟩
    rw [hD_emp] at this
    exact this
  · have ⟨d, hdD, hd_min⟩ : ∃ d ∈ D, ∀ d' ∈ D, d ≤ d' := by
      let D_finset := hD_fin.toFinset
      have hD_finset_nemp : D_finset.Nonempty := by
        rw [Finite.toFinset_nonempty]
        exact hD_nemp
      use D_finset.min' hD_finset_nemp
      refine ⟨?_, fun d' hd' => ?_⟩
      · rw [← Finite.mem_toFinset]
        exact Finset.min'_mem _ _
      · have hd' : d' ∈ D_finset := by
          rw [Finite.mem_toFinset]
          exact hd'
        exact Finset.min'_le _ _ hd'
    use d
    refine ⟨hd_pos d hdD, fun K hK A hA w hw hne => ?_⟩
    exact hd_min _ ⟨K, hK, A, hA, w, hw, hne, rfl⟩

/-- Step 1 of the blueprint proof of `uniformSectorRadius_step4_translation`:
Translations preserve the radius conclusion. -/
private lemma uniformSectorRadius_step4_translation_step1_rad_carrier
    (A : PlacedTile P) (v : Pt) :
    (A.translate v).carrier = (v +ᵥ ·) '' A.carrier := by
  dsimp [PlacedTile.carrier, PlacedTile.translate]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    use A.anchor +ᵥ y
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    change v +ᵥ (A.anchor +ᵥ y) = (v + A.anchor) +ᵥ y
    exact (vadd_assoc v A.anchor y).symm
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    use z
    refine ⟨hz, ?_⟩
    change (v + A.anchor) +ᵥ z = v +ᵥ (A.anchor +ᵥ z)
    exact vadd_assoc v A.anchor z

private lemma uniformSectorRadius_step4_translation_step1_rad_localCone
    (A : Set Pt) (v w : Pt) :
    localCone ((w +ᵥ ·) '' A) (w + v) = (w +ᵥ ·) '' localCone A v := by
  dsimp [localCone]
  ext x
  simp only [mem_setOf_eq, mem_image]
  constructor
  · rintro ⟨r, hr, h⟩
    use -w + x
    refine ⟨?_, by abel⟩
    use r
    refine ⟨hr, ?_⟩
    intro t ht
    have ht' := h t ht
    rcases ht' with ⟨y, hy, hy'⟩
    change w + y = w + v + t • (x - (w + v)) at hy'
    have : y = v + t • (-w + x - v) := by
      calc y = -w + (w + y) := by abel
        _ = -w + (w + v + t • (x - (w + v))) := by rw [hy']
        _ = v + t • (-w + x - v) := by
          have H : x - (w + v) = -w + x - v := by abel
          rw [H]
          abel
    rw [← this]
    exact hy
  · rintro ⟨y, ⟨r, hr, h⟩, rfl⟩
    use r
    refine ⟨hr, ?_⟩
    intro t ht
    have ht' := h t ht
    use v + t • (y - v)
    refine ⟨ht', ?_⟩
    change w + (v + t • (y - v)) = w + v + t • (w + y - (w + v))
    have H : w + y - (w + v) = y - v := by abel
    rw [H]
    abel

private lemma uniformSectorRadius_step4_translation_step1_rad_Omega
    (K : Set (PlacedTile P)) (v : Pt) :
    Omega (translateSet v K) v = (v +ᵥ ·) '' Omega K 0 := by
  simp only [Omega, translateSet, image_iUnion]
  ext x
  simp only [mem_iUnion, mem_image]
  constructor
  · rintro ⟨A, ⟨B, hB, rfl⟩, hx⟩
    rw [uniformSectorRadius_step4_translation_step1_rad_carrier B v] at hx
    use B, hB
    have H : localCone ((v +ᵥ ·) '' B.carrier) v = (v +ᵥ ·) '' localCone B.carrier 0 := by
      have h1 := uniformSectorRadius_step4_translation_step1_rad_localCone B.carrier 0 v
      simp only [add_zero] at h1
      exact h1
    rw [H] at hx
    exact hx
  · rintro ⟨A, hA, ⟨y, hy, rfl⟩⟩
    use A.translate v
    refine ⟨⟨A, hA, rfl⟩, ?_⟩
    rw [uniformSectorRadius_step4_translation_step1_rad_carrier A v]
    have H : localCone ((v +ᵥ ·) '' A.carrier) v = (v +ᵥ ·) '' localCone A.carrier 0 := by
      have h1 := uniformSectorRadius_step4_translation_step1_rad_localCone A.carrier 0 v
      simp only [add_zero] at h1
      exact h1
    rw [H]
    exact ⟨y, hy, rfl⟩

private lemma uniformSectorRadius_step4_translation_step1_rad_ball
    (r : ℝ) (v : Pt) :
    ball v r = (v +ᵥ ·) '' ball 0 r := by
  ext x
  simp only [mem_ball, mem_image]
  constructor
  · intro h
    use -v + x
    refine ⟨?_, ?_⟩
    · have H : dist (-v + x) 0 = dist x v := by
        rw [dist_eq_norm, dist_eq_norm]
        have h1 : -v + x - 0 = x - v := by abel
        rw [h1]
      rwa [H]
    · exact add_neg_cancel_left v x
  · rintro ⟨y, hy, rfl⟩
    have H : dist (v +ᵥ y) v = dist y 0 := by
      rw [dist_eq_norm, dist_eq_norm]
      have h1 : (v +ᵥ y) - v = y - 0 := by
        change v + y - v = y - 0
        abel
      rw [h1]
    rwa [H]

private lemma uniformSectorRadius_step4_translation_step1_rad_support
    (K : Set (PlacedTile P)) (v : Pt) :
    support (translateSet v K) = (v +ᵥ ·) '' support K := by
  dsimp [support, translateSet]
  ext x
  simp only [mem_iUnion, mem_image]
  constructor
  · rintro ⟨A, ⟨B, hB, rfl⟩, hx⟩
    rw [uniformSectorRadius_step4_translation_step1_rad_carrier B v] at hx
    rcases hx with ⟨y, hy, rfl⟩
    use y
    refine ⟨⟨B, hB, hy⟩, rfl⟩
  · rintro ⟨y, ⟨B, hB, hy⟩, rfl⟩
    use B.translate v
    refine ⟨⟨B, hB, rfl⟩, ?_⟩
    rw [uniformSectorRadius_step4_translation_step1_rad_carrier B v]
    use y
    exact ⟨hy, rfl⟩

private lemma uniformSectorRadius_step4_translation_step1_rad {K : Set (PlacedTile P)} {r : ℝ}
    (h_rad : ∀ A ∈ K, A.carrier ∩ ball 0 r = localCone A.carrier 0 ∩ ball 0 r) (v : Pt) :
    support (translateSet v K) ∩ ball v r = Omega (translateSet v K) v ∩ ball v r := by
  rw [uniformSectorRadius_step4_translation_step1_rad_support K v]
  rw [uniformSectorRadius_step4_translation_step1_rad_Omega K v]
  rw [uniformSectorRadius_step4_translation_step1_rad_ball r v]
  have H : (v +ᵥ ·) '' support K ∩ (v +ᵥ ·) '' ball 0 r = (v +ᵥ ·) '' (support K ∩ ball 0 r) := by
    ext x
    simp only [mem_inter_iff, mem_image]
    constructor
    · rintro ⟨⟨y1, hy1, hy1_eq⟩, ⟨y2, hy2, hy2_eq⟩⟩
      have h_eq : y1 = y2 := by
        have H_inj : v + y1 = v + y2 := by
          change v + y1 = x at hy1_eq
          change v + y2 = x at hy2_eq
          calc v + y1 = x := hy1_eq
            _ = v + y2 := hy2_eq.symm
        exact add_left_cancel H_inj
      use y1
      refine ⟨⟨hy1, ?_⟩, hy1_eq⟩
      rw [h_eq]
      exact hy2
    · rintro ⟨y, ⟨hy1, hy2⟩, hy_eq⟩
      exact ⟨⟨y, hy1, hy_eq⟩, ⟨y, hy2, hy_eq⟩⟩
  have H2 : (v +ᵥ ·) '' Omega K 0 ∩ (v +ᵥ ·) '' ball 0 r = (v +ᵥ ·) '' (Omega K 0 ∩ ball 0 r) := by
    ext x
    simp only [mem_inter_iff, mem_image]
    constructor
    · rintro ⟨⟨y1, hy1, hy1_eq⟩, ⟨y2, hy2, hy2_eq⟩⟩
      have h_eq : y1 = y2 := by
        have H_inj : v + y1 = v + y2 := by
          change v + y1 = x at hy1_eq
          change v + y2 = x at hy2_eq
          calc v + y1 = x := hy1_eq
            _ = v + y2 := hy2_eq.symm
        exact add_left_cancel H_inj
      use y1
      refine ⟨⟨hy1, ?_⟩, hy1_eq⟩
      rw [h_eq]
      exact hy2
    · rintro ⟨y, ⟨hy1, hy2⟩, hy_eq⟩
      exact ⟨⟨y, hy1, hy_eq⟩, ⟨y, hy2, hy_eq⟩⟩
  rw [H, H2]
  congr 1
  dsimp [support, Omega]
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨⟨A, hA, hx⟩, hball⟩
    have H_rad := h_rad A hA
    have hx_cone : x ∈ localCone A.carrier 0 := by
      have : x ∈ A.carrier ∩ ball 0 r := ⟨hx, hball⟩
      rw [H_rad] at this
      exact this.1
    refine ⟨⟨A, hA, hx_cone⟩, hball⟩
  · rintro ⟨⟨A, hA, hx⟩, hball⟩
    have H_rad := h_rad A hA
    have hx_carrier : x ∈ A.carrier := by
      have : x ∈ localCone A.carrier 0 ∩ ball 0 r := ⟨hx, hball⟩
      rw [← H_rad] at this
      exact this.1
    refine ⟨⟨A, hA, hx_carrier⟩, hball⟩

/-- Step 2 of the blueprint proof of `uniformSectorRadius_step4_translation`:
Translations preserve the vertex separation conclusion. -/
private lemma uniformSectorRadius_step4_translation_step2_sep {K : Set (PlacedTile P)} {δ : ℝ}
    (h_sep : ∀ A ∈ K, ∀ w ∈ A.vertexSet, w ≠ 0 → δ ≤ dist w 0) (v : Pt) :
    ∀ A ∈ translateSet v K, ∀ w ∈ A.vertexSet, w ≠ v → δ ≤ dist w v := by
  intro A hA w hw hne
  dsimp [translateSet] at hA
  rcases hA with ⟨B, hB, rfl⟩
  dsimp [PlacedTile.translate, PlacedTile.vertexSet, PlacedTile.vertex] at hw ⊢
  rcases hw with ⟨i, rfl⟩
  have hwB : (B.vertex i) ∈ B.vertexSet := by
    dsimp [PlacedTile.vertexSet]
    exact Set.mem_range_self i
  have h_vert_eq :
      ({ form := B.form, anchor := v + B.anchor } : PlacedTile P).vertex i = v + B.vertex i := by
    dsimp [PlacedTile.vertex]
    abel
  rw [h_vert_eq] at hne ⊢
  have hne' : B.vertex i ≠ 0 := by
    intro h
    apply hne
    rw [h, add_zero]
  have H := h_sep B hB (B.vertex i) hwB hne'
  have H2 : dist (v + B.vertex i) v = dist (B.vertex i) 0 := by
    rw [dist_eq_norm, dist_eq_norm]
    have : v + B.vertex i - v = B.vertex i - 0 := by abel
    rw [this]
  rw [H2]
  exact H

/-- Step 4 of the blueprint proof of `uniformSectorRadius`: Translations preserve the
conclusions. -/
private lemma uniformSectorRadius_step4_translation {K : Set (PlacedTile P)} {r δ : ℝ}
    (h_rad : ∀ A ∈ K, A.carrier ∩ ball (0 : Pt) r = localCone A.carrier 0 ∩ ball (0 : Pt) r)
    (h_sep : ∀ A ∈ K, ∀ w ∈ A.vertexSet, w ≠ (0 : Pt) → δ ≤ dist w (0 : Pt)) :
    ∀ v : Pt,
      support (translateSet v K) ∩ ball v r = Omega (translateSet v K) v ∩ ball v r ∧
      ∀ A ∈ translateSet v K, ∀ w ∈ A.vertexSet, w ≠ v → δ ≤ dist w v := by
  intro v
  exact ⟨uniformSectorRadius_step4_translation_step1_rad h_rad v,
         uniformSectorRadius_step4_translation_step2_sep h_sep v⟩

/-- `lem:sector-radius`: uniform sector radius `r_*` and vertex separation
`δ_*` for a finite catalogue. -/
theorem uniformSectorRadius {𝒞 : Set (Set (PlacedTile P))} (h𝒞 : IsCatalogue 𝒞) :
    ∃ r : ℝ, 0 < r ∧ ∃ δ : ℝ, 0 < δ ∧ SectorRadiusProperty 𝒞 r δ := by
  obtain ⟨r, hr, hrad⟩ := uniformSectorRadius_step2_catalogue_radius h𝒞
  obtain ⟨δ, hδ, hsep⟩ := uniformSectorRadius_step3_catalogue_separation h𝒞
  refine ⟨r, hr, δ, hδ, fun K hK v => ?_⟩
  exact uniformSectorRadius_step4_translation (hrad K hK) (hsep K hK) v

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

/-- Step 1 of the blueprint proof of `supertile_disjoint_step1_decompose`: the decomposed tiles of a single tile have disjoint interiors. -/
private lemma supertile_disjoint_step1_decompose_step1 (τ : Substitution P) (A : PlacedTile P) :
    DisjointInteriors (τ.decomposeTile A) := by
  dsimp [Substitution.decomposeTile, translateSet]
  intro T1 hT1 T2 hT2 hne
  rcases hT1 with ⟨B1, hB1, rfl⟩
  rcases hT2 with ⟨B2, hB2, rfl⟩
  have hne' : B1 ≠ B2 := fun h => hne (by rw [h])
  have hd := (τ.rule A.form).disjoint hB1 hB2 hne'
  dsimp [Function.onFun] at hd ⊢
  have heq1 : (B1.translate (τ.θ • A.anchor)).carrier = (τ.θ • A.anchor) +ᵥ B1.carrier := by
    ext x
    simp only [PlacedTile.carrier, PlacedTile.translate, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_rev]
    rw [← add_assoc]
  have heq2 : (B2.translate (τ.θ • A.anchor)).carrier = (τ.θ • A.anchor) +ᵥ B2.carrier := by
    ext x
    simp only [PlacedTile.carrier, PlacedTile.translate, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_rev]
    rw [← add_assoc]
  rw [heq1, heq2, interior_vadd, interior_vadd]
  have hinj : Function.Injective ((τ.θ • A.anchor) +ᵥ · : Pt → Pt) := add_right_injective _
  exact (disjoint_image_iff hinj).mpr hd

/-- Step 2 of the blueprint proof of `supertile_disjoint_step1_decompose`: the interiors
of the supports of decompositions of two disjoint tiles are disjoint. -/
private lemma supertile_disjoint_step1_decompose_step2 (τ : Substitution P) (S : Set (PlacedTile P))
    (hS : DisjointInteriors S) (A B : PlacedTile P) (hA : A ∈ S) (hB : B ∈ S) (hne : A ≠ B) :
    Disjoint (interior (support (τ.decomposeTile A))) (interior (support (τ.decomposeTile B))) := by
  have htranslate : ∀ (v : Pt) (Q : Set (PlacedTile P)),
      support (translateSet v Q) = v +ᵥ support Q := by
    intro v Q
    ext x
    simp only [support, translateSet, PlacedTile.translate, PlacedTile.carrier,
      mem_iUnion, mem_image, mem_vadd_set_iff_neg_vadd_mem]
    constructor
    · rintro ⟨C, ⟨D, hD, rfl⟩, hx⟩
      exact ⟨D, hD, by simpa [← add_assoc] using hx⟩
    · rintro ⟨C, hC, hx⟩
      refine ⟨⟨C.form, v +ᵥ C.anchor⟩, ⟨C, hC, rfl⟩, ?_⟩
      simpa [← add_assoc] using hx
  have hsupport (C : PlacedTile P) :
      support (τ.decomposeTile C) = τ.θ • C.carrier := by
    dsimp [Substitution.decomposeTile]
    rw [htranslate, τ.support_eq, PlacedTile.carrier]
    ext x
    simp only [mem_vadd_set_iff_neg_vadd_mem, mem_smul_set]
    constructor
    · rintro ⟨y, hy, hx⟩
      refine ⟨C.anchor + y, ?_, ?_⟩
      · simpa
      · rw [smul_add]
        calc τ.θ • C.anchor + τ.θ • y =
            τ.θ • C.anchor + (-(τ.θ • C.anchor) + x) := by congr 1
          _ = x := by abel
    · rintro ⟨y, hy, rfl⟩
      refine ⟨-C.anchor + y, ?_, ?_⟩
      · simpa
      · simp [smul_add]
  have hθ : τ.θ ≠ 0 := by linarith [τ.one_lt]
  rw [hsupport A, hsupport B, interior_smul₀ hθ, interior_smul₀ hθ]
  rw [Set.disjoint_left]
  intro x hxA hxB
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hθ] at hxA hxB
  exact (Set.disjoint_left.mp (hS hA hB hne)) hxA hxB

/-- Step 3 of the blueprint proof of `supertile_disjoint_step1_decompose`: the interior of a tile is in the interior of the support of its decomposition. -/
private lemma supertile_disjoint_step1_decompose_step3 (τ : Substitution P) (A : PlacedTile P)
    (T : PlacedTile P) (hT : T ∈ τ.decomposeTile A) :
    interior T.carrier ⊆ interior (support (τ.decomposeTile A)) := by
  apply interior_mono
  dsimp [Substitution.decomposeTile, translateSet] at hT
  rcases hT with ⟨B, hB, rfl⟩
  dsimp [PlacedTile.translate, PlacedTile.carrier, support]
  intro x hx
  let C : PlacedTile P := B.translate (τ.θ • A.anchor)
  refine mem_iUnion.2 ⟨C, mem_iUnion.2 ⟨?_, ?_⟩⟩
  · dsimp [C, Substitution.decomposeTile, translateSet]
    exact ⟨B, hB, rfl⟩
  · simpa [C, PlacedTile.translate] using hx

/-- Step 4 of the blueprint proof of `supertile_disjoint_step1_decompose`: for two tiles T1 and T2
  from the decomposition of A and B, their interiors are disjoint. -/
private lemma supertile_disjoint_step1_decompose_step4 (τ : Substitution P) (S : Set (PlacedTile P))
    (hS : DisjointInteriors S) (A B : PlacedTile P) (hA : A ∈ S) (hB : B ∈ S) (hne : A ≠ B)
    (T1 : PlacedTile P) (h1 : T1 ∈ τ.decomposeTile A)
    (T2 : PlacedTile P) (h2 : T2 ∈ τ.decomposeTile B) :
    Disjoint (interior T1.carrier) (interior T2.carrier) := by
  have h_disj := supertile_disjoint_step1_decompose_step2 τ S hS A B hA hB hne
  have h_sub1 := supertile_disjoint_step1_decompose_step3 τ A T1 h1
  have h_sub2 := supertile_disjoint_step1_decompose_step3 τ B T2 h2
  exact h_disj.mono h_sub1 h_sub2

/-- Step 1 of the blueprint proof of `supertile_disjoint`: decomposition
preserves disjoint interiors. -/
private lemma supertile_disjoint_step1_decompose (τ : Substitution P) (S : Set (PlacedTile P))
    (hS : DisjointInteriors S) : DisjointInteriors (τ.decompose S) := by
  intro T1 hT1 T2 hT2 hne
  dsimp [Substitution.decompose] at hT1 hT2
  simp only [mem_iUnion, exists_prop] at hT1 hT2
  rcases hT1 with ⟨A, hA, hT1A⟩
  rcases hT2 with ⟨B, hB, hT2B⟩
  by_cases hAB : A = B
  · subst hAB
    have h1 := supertile_disjoint_step1_decompose_step1 τ A
    exact h1 hT1A hT2B hne
  · exact supertile_disjoint_step1_decompose_step4 τ S hS A B hA hB hAB T1 hT1A T2 hT2B

/-- A supertile has pairwise disjoint interiors. -/
theorem supertile_disjoint (τ : Substitution P) (n : ℕ) (p : P.Form) :
    DisjointInteriors (τ.supertile n p) := by
  induction n with
  | zero => 
    intro x hx y hy hne
    simp [supertile, decomposeIter] at hx hy
    rcases hx with rfl
    rcases hy with rfl
    contradiction
  | succ n ih => 
    have h : τ.supertile (n + 1) p = τ.decompose (τ.supertile n p) := rfl
    rw [h]
    exact supertile_disjoint_step1_decompose τ (τ.supertile n p) ih

/-- The support of a supertile in the `MacroPatch` normal form. -/
theorem supertile_support_eq (τ : Substitution P) (n : ℕ) (p : P.Form) :
    support (τ.supertile n p) = (0 : Pt) +ᵥ (τ.θ ^ n) • (P.disk p).carrier := by
  rw [τ.iterate_support n p, zero_vadd]

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

private def macroPerp (d : Pt) : Pt := !₂[-d 1, d 0]

private lemma macroPerp_inner (d : Pt) : inner ℝ (macroPerp d) d = 0 := by
  simp [macroPerp, PiLp.inner_apply, Fin.sum_univ_two]
  ring

private lemma macroPerp_ne_zero {d : Pt} (hd : d ≠ 0) : macroPerp d ≠ 0 := by
  intro h
  apply hd
  have h0 := congrFun (congrArg (fun v : Pt => (v : Fin 2 → ℝ)) h) 0
  have h1 := congrFun (congrArg (fun v : Pt => (v : Fin 2 → ℝ)) h) 1
  simp [macroPerp] at h0 h1
  ext i
  fin_cases i <;> simp [h0, h1]

private lemma macro_preconn_sub {s H : Set Pt} (hH : IsPreconnected H)
    (hf : Disjoint H (frontier s)) :
    H ⊆ interior s ∨ H ⊆ (closure s)ᶜ := by
  refine hH.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl ?_ ?_
  · exact disjoint_compl_right.mono_left (interior_subset.trans subset_closure)
  · intro y hy
    by_cases h1 : y ∈ interior s
    · exact Or.inl h1
    · right
      intro h2
      exact hf.ne_of_mem hy ⟨h2, h1⟩ rfl

private lemma macro_segment_compact (x y : Pt) :
    IsCompact (segment ℝ x y) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

private lemma macro_halfdisk (Q : PolygonalDisk) {x : Pt}
    (hx : x ∈ frontier Q.carrier) (hv : x ∉ Q.vertexSet) :
    ∃ (i : Fin Q.n) (ε : ℝ) (d n : Pt),
      0 < ε ∧ d ≠ 0 ∧ n ≠ 0 ∧ inner ℝ n d = 0 ∧
      (∀ s : ℝ, |s| < ε → x + s • d ∈ Q.side i) ∧
      (∀ y, dist y x < ε → 0 < inner ℝ n (y - x) →
        y ∈ interior Q.carrier) := by
  have hx' := hx
  rw [Q.frontier_eq, mem_iUnion] at hx'
  obtain ⟨i, hxi⟩ := hx'
  set v := Q.vertex i with hvdef
  set w := Q.vertex (finRotate Q.n i) with hwdef
  have hxv : x ≠ v := fun h => hv ⟨i, h.symm⟩
  have hxw : x ≠ w := fun h => hv ⟨finRotate Q.n i, h.symm⟩
  rw [segment_eq_image'] at hxi
  obtain ⟨t, ⟨ht0, ht1⟩, hxt⟩ := hxi
  set d := w - v with hd
  have hd0 : d ≠ 0 := by
    intro h
    apply hxv
    rw [← hxt, h]
    simp
  have ht0' : t ≠ 0 := by
    rintro rfl
    apply hxv
    rw [← hxt]
    simp
  have ht1' : t ≠ 1 := by
    rintro rfl
    apply hxw
    rw [← hxt]
    simp [hd]
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
  have htlt : t < 1 := lt_of_le_of_ne ht1 ht1'
  set O : Set Pt :=
    ⋃ j ∈ ({j | j ≠ i} : Set (Fin Q.n)), Q.side j with hO
  have hOc : IsClosed O := by
    apply Set.Finite.isClosed_biUnion (Set.toFinite _)
    intro j _
    exact (macro_segment_compact _ _).isClosed
  have hxO : x ∉ O := by
    simp only [hO, mem_iUnion, mem_setOf_eq, not_exists]
    intro j hj hxj
    have hxi2 : x ∈ Q.side i := by
      rw [PolygonalDisk.side, segment_eq_image']
      exact ⟨t, ⟨ht0, ht1⟩, hxt⟩
    have := Q.simple i j (Ne.symm hj) ⟨hxi2, hxj⟩
    rcases this.1 with h | h
    · exact hxv h
    · exact hxw h
  obtain ⟨ε₁, hε₁, hε₁O⟩ :=
    Metric.isOpen_iff.mp hOc.isOpen_compl x hxO
  have hfr : ∀ y, dist y x < ε₁ → y ∈ frontier Q.carrier →
      ∃ θ : ℝ, y = v + θ • d := by
    intro y hy hyf
    rw [Q.frontier_eq, mem_iUnion] at hyf
    obtain ⟨j, hj⟩ := hyf
    by_cases hji : j = i
    · subst hji
      rw [segment_eq_image'] at hj
      obtain ⟨θ, _, hθ⟩ := hj
      exact ⟨θ, hθ.symm⟩
    · exfalso
      have : y ∈ O := by
        simp only [hO, mem_iUnion, mem_setOf_eq]
        exact ⟨j, hji, hj⟩
      exact hε₁O (Metric.mem_ball.mpr hy) this
  set n₀ := macroPerp d with hn₀
  have hn₀d : inner ℝ n₀ d = 0 := macroPerp_inner d
  have hn₀ne : n₀ ≠ 0 := macroPerp_ne_zero hd0
  have hline : ∀ θ : ℝ, inner ℝ n₀ (v + θ • d - x) = 0 := by
    intro θ
    rw [← hxt]
    have : v + θ • d - (v + t • d) = (θ - t) • d := by
      rw [sub_smul]
      abel
    rw [this, inner_smul_right, hn₀d, mul_zero]
  set ε := min ε₁ (min t (1 - t)) with hε
  have hεpos : 0 < ε := lt_min hε₁ (lt_min htpos (by linarith))
  have hxcl : x ∈ closure (interior Q.carrier) := by
    rw [Q.regular_closed]
    exact Q.compact.isClosed.frontier_subset hx
  obtain ⟨z0, hz0i, hz0x⟩ :=
    Metric.mem_closure_iff.mp hxcl (ε / 2) (by linarith)
  obtain ⟨δ0, hδ0, hδ0b⟩ :=
    Metric.isOpen_iff.mp isOpen_interior z0 hz0i
  have hz : ∃ z ∈ interior Q.carrier, dist z x < ε ∧
      inner ℝ n₀ (z - x) ≠ 0 := by
    by_cases hz0 : inner ℝ n₀ (z0 - x) = 0
    · have hnpos : 0 < ‖n₀‖ := norm_pos_iff.mpr hn₀ne
      set δ := min δ0 (ε / 2) / (2 * ‖n₀‖) with hδ
      have hmin : 0 < min δ0 (ε / 2) :=
        lt_min hδ0 (by linarith)
      have hδpos : 0 < δ := div_pos hmin (by positivity)
      have hnorm : ‖δ • n₀‖ = min δ0 (ε / 2) / 2 := by
        rw [norm_smul, Real.norm_of_nonneg hδpos.le, hδ]
        field_simp
      refine ⟨z0 + δ • n₀, hδ0b ?_, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm]
        have := min_le_left δ0 (ε / 2)
        linarith
      · calc
          dist (z0 + δ • n₀) x ≤
              dist (z0 + δ • n₀) z0 + dist z0 x :=
            dist_triangle _ _ _
          _ < ε := by
            rw [dist_eq_norm, add_sub_cancel_left, hnorm, dist_comm]
            have := min_le_right δ0 (ε / 2)
            linarith
      · have : z0 + δ • n₀ - x = (z0 - x) + δ • n₀ := by
          abel
        rw [this, inner_add_right, hz0, inner_smul_right,
          real_inner_self_eq_norm_sq]
        positivity
    · exact ⟨z0, hz0i, by rw [dist_comm]; linarith, hz0⟩
  obtain ⟨z, hzi, hzx, hzn⟩ := hz
  have hsign : ∃ n : Pt, n ≠ 0 ∧ inner ℝ n d = 0 ∧
      0 < inner ℝ n (z - x) ∧
      ∀ θ : ℝ, inner ℝ n (v + θ • d - x) = 0 := by
    rcases lt_or_gt_of_ne hzn with h | h
    · refine ⟨-n₀, neg_ne_zero.mpr hn₀ne, ?_, ?_, ?_⟩
      · rw [inner_neg_left, hn₀d, neg_zero]
      · rw [inner_neg_left]
        linarith
      · intro θ
        rw [inner_neg_left, hline, neg_zero]
    · exact ⟨n₀, hn₀ne, hn₀d, h, hline⟩
  obtain ⟨n, hn0, hnd, hnz, hnline⟩ := hsign
  refine ⟨i, ε, d, n, hεpos, hd0, hn0, hnd, ?_, ?_⟩
  · intro s hs
    rw [PolygonalDisk.side, segment_eq_image']
    have hs1 : |s| < t :=
      lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_left _ _))
    have hs2 : |s| < 1 - t :=
      lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨t + s, ⟨?_, ?_⟩, ?_⟩
    · have := neg_abs_le s
      linarith
    · have := le_abs_self s
      linarith
    · show v + (t + s) • d = x + s • d
      rw [← hxt, add_smul]
      simp only
      abel
  · set H : Set Pt :=
      Metric.ball x ε ∩ {y | 0 < inner ℝ n (y - x)} with hH
    have hHconv : Convex ℝ H := by
      apply (convex_ball x ε).inter
      intro a ha b hb α β hα hβ hαβ
      simp only [mem_setOf_eq] at ha hb ⊢
      have : α • a + β • b - x =
          α • (a - x) + β • (b - x) := by
        calc
          α • a + β • b - x =
              α • a + β • b - (α + β) • x := by
            rw [hαβ, one_smul]
          _ = α • (a - x) + β • (b - x) := by
            rw [add_smul, smul_sub, smul_sub]
            abel
      rw [this, inner_add_right, inner_smul_right, inner_smul_right]
      rcases hα.eq_or_lt with h | h
      · subst h
        simp at hαβ
        subst hαβ
        simpa using hb
      · have := mul_pos h ha
        nlinarith
    have hHdisj : Disjoint H (frontier Q.carrier) := by
      rw [Set.disjoint_left]
      rintro y ⟨hy1, hy2⟩ hyf
      have hy1' : dist y x < ε₁ :=
        lt_of_lt_of_le (Metric.mem_ball.mp hy1) (min_le_left _ _)
      obtain ⟨θ, rfl⟩ := hfr y hy1' hyf
      simp only [mem_setOf_eq] at hy2
      rw [hnline θ] at hy2
      exact lt_irrefl _ hy2
    rcases macro_preconn_sub hHconv.isPreconnected hHdisj with h | h
    · intro y hy hyn
      exact h ⟨Metric.mem_ball.mpr hy, hyn⟩
    · exfalso
      exact h ⟨Metric.mem_ball.mpr hzx, hnz⟩
        (subset_closure (interior_subset hzi))

private lemma macro_parallel {n a b : Pt} (hn : n ≠ 0) (hb : b ≠ 0)
    (ha0 : inner ℝ n a = 0) (hb0 : inner ℝ n b = 0) :
    ∃ c : ℝ, a = c • b := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
    conj_trivial] at ha0 hb0
  have hcross : a 0 * b 1 = a 1 * b 0 := by
    by_cases h0 : n 0 = 0
    · have h1 : n 1 ≠ 0 := by
        intro h1
        apply hn
        ext i
        fin_cases i <;> simp [h0, h1]
      have e1 : a 1 = 0 := by
        rw [h0] at ha0
        simp at ha0
        rcases ha0 with h | h <;> simp_all
      have e2 : b 1 = 0 := by
        rw [h0] at hb0
        simp at hb0
        rcases hb0 with h | h <;> simp_all
      rw [e1, e2]
      ring
    · have : n 0 * (a 0 * b 1 - a 1 * b 0) = 0 := by
        linear_combination b 1 * ha0 - a 1 * hb0
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h0
      · linarith
  by_cases hb0' : b 0 = 0
  · have hb1 : b 1 ≠ 0 := by
      intro h1
      apply hb
      ext i
      fin_cases i <;> simp [hb0', h1]
    refine ⟨a 1 / b 1, ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
      rw [hb0'] at hcross ⊢
      have : a 0 = 0 := by
        have := hcross
        simp at this
        rcases this with h | h
        · exact h
        · exact absurd h hb1
      rw [this]
      ring
    · simp only [Fin.mk_one, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
      field_simp
  · refine ⟨a 0 / b 0, ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
      field_simp
      linarith

private lemma macro_tile_regular (A : PlacedTile P) :
    closure (interior A.carrier) = A.carrier := by
  unfold PlacedTile.carrier
  rw [interior_vadd, closure_vadd, (P.disk A.form).regular_closed]

private lemma macro_halfdisk_tile (A : PlacedTile P) {x : Pt}
    (hx : x ∈ A.carrier) (hint : x ∉ interior A.carrier)
    (hv : x ∉ A.vertexSet) :
    ∃ (i : Fin (P.disk A.form).n) (ε : ℝ) (d n : Pt),
      0 < ε ∧ d ≠ 0 ∧ n ≠ 0 ∧ inner ℝ n d = 0 ∧
      (∀ s : ℝ, |s| < ε → x + s • d ∈ A.side i) ∧
      (∀ y, dist y x < ε → 0 < inner ℝ n (y - x) →
        y ∈ interior A.carrier) := by
  set Q := P.disk A.form
  have hx' : -A.anchor + x ∈ frontier Q.carrier := by
    unfold PlacedTile.carrier at hx hint
    rw [interior_vadd, mem_vadd_set_iff_neg_vadd_mem] at hint
    rw [mem_vadd_set_iff_neg_vadd_mem] at hx
    rw [Q.compact.isClosed.frontier_eq]
    exact ⟨hx, hint⟩
  have hv' : -A.anchor + x ∉ Q.vertexSet := by
    rintro ⟨k, hk⟩
    apply hv
    refine ⟨k, ?_⟩
    simp only [PlacedTile.vertex, vadd_eq_add]
    rw [hk]
    abel
  obtain ⟨i, ε, d, n, hε, hd, hn, hnd, hs, hy⟩ :=
    macro_halfdisk Q hx' hv'
  refine ⟨i, ε, d, n, hε, hd, hn, hnd, ?_, ?_⟩
  · intro s hs'
    have := hs s hs'
    unfold PlacedTile.side
    rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    convert this using 1
    all_goals abel
  · intro y hyx hyn
    unfold PlacedTile.carrier
    rw [interior_vadd, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    apply hy
    · rw [dist_eq_norm] at hyx ⊢
      convert hyx using 2
      all_goals abel
    · convert hyn using 2
      all_goals abel

private lemma macro_tiles_share_local_side {A B : PlacedTile P}
    (hd : Disjoint (interior A.carrier) (interior B.carrier))
    {x : Pt} (hxA : x ∈ A.carrier) (hxB : x ∈ B.carrier)
    (hvA : x ∉ A.vertexSet) (hvB : x ∉ B.vertexSet) :
    ∃ i j, x ∈ A.side i ∧ x ∈ B.side j ∧
      OverlapPos (A.side i) (B.side j) := by
  have hnotint : ∀ {A B : PlacedTile P},
      Disjoint (interior A.carrier) (interior B.carrier) →
      x ∈ B.carrier → x ∉ interior A.carrier := by
    intro A B hd hxB hxA
    rw [← macro_tile_regular B, mem_closure_iff_nhds] at hxB
    obtain ⟨z, hz1, hz2⟩ :=
      hxB _ (isOpen_interior.mem_nhds hxA)
    exact Set.disjoint_left.mp hd hz1 hz2
  obtain ⟨i, ε₁, d₁, n₁, hε₁, hd₁, hn₁, hnd₁, hs₁, hy₁⟩ :=
    macro_halfdisk_tile A hxA (hnotint hd hxB) hvA
  obtain ⟨j, ε₂, d₂, n₂, hε₂, hd₂, hn₂, hnd₂, hs₂, hy₂⟩ :=
    macro_halfdisk_tile B hxB (hnotint hd.symm hxA) hvB
  have key : inner ℝ n₂ d₁ = 0 := by
    by_contra hne
    obtain ⟨w, hw2, hw1⟩ :
        ∃ w : Pt, 0 < inner ℝ n₂ w ∧ inner ℝ n₁ w = 0 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨-d₁, by rw [inner_neg_right]; linarith,
          by rw [inner_neg_right, hnd₁, neg_zero]⟩
      · exact ⟨d₁, h, hnd₁⟩
    set τ := (|inner ℝ n₂ n₁| + 1) / inner ℝ n₂ w with hτ
    set u := n₁ + τ • w with hu
    have hu2 : 0 < inner ℝ n₂ u := by
      rw [hu, inner_add_right, inner_smul_right, hτ,
        div_mul_cancel₀ _ hw2.ne']
      have := neg_abs_le (inner ℝ n₂ n₁)
      linarith
    have hu1 : 0 < inner ℝ n₁ u := by
      rw [hu, inner_add_right, inner_smul_right, hw1, mul_zero,
        add_zero, real_inner_self_eq_norm_sq]
      have := norm_pos_iff.mpr hn₁
      positivity
    have hu0 : u ≠ 0 := by
      rintro h
      rw [h, inner_zero_right] at hu1
      exact lt_irrefl _ hu1
    have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    set δ := min ε₁ ε₂ / (2 * ‖u‖) with hδ
    have hδpos : 0 < δ :=
      div_pos (lt_min hε₁ hε₂) (by positivity)
    have hdist : dist (x + δ • u) x = min ε₁ ε₂ / 2 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hδpos.le, hδ]
      field_simp
    have h1 : x + δ • u ∈ interior A.carrier := by
      apply hy₁ _ (by rw [hdist]; have := min_le_left ε₁ ε₂; linarith)
      rw [add_sub_cancel_left, inner_smul_right]
      positivity
    have h2 : x + δ • u ∈ interior B.carrier := by
      apply hy₂ _ (by rw [hdist]; have := min_le_right ε₁ ε₂; linarith)
      rw [add_sub_cancel_left, inner_smul_right]
      positivity
    exact Set.disjoint_left.mp hd h1 h2
  obtain ⟨c, hc⟩ := macro_parallel hn₂ hd₂ key hnd₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hd₁
    rw [hc, zero_smul]
  have hcpos : 0 < |c| := abs_pos.mpr hc0
  set s₀ := min ε₁ (ε₂ / |c|) / 2 with hs₀
  have hs₀pos : 0 < s₀ := by
    have : 0 < min ε₁ (ε₂ / |c|) :=
      lt_min hε₁ (div_pos hε₂ hcpos)
    positivity
  have hxi : x ∈ A.side i := by
    simpa using hs₁ 0 (by simpa using hε₁)
  have hxj : x ∈ B.side j := by
    simpa using hs₂ 0 (by simpa using hε₂)
  refine ⟨i, j, hxi, hxj,
    x + (-s₀) • d₁, x + s₀ • d₁, ?_, ?_⟩
  · intro h
    have : (2 * s₀) • d₁ = 0 := by
      have h' := congrArg (fun z => z - x) h
      simp only [add_sub_cancel_left] at h'
      have e : (2 * s₀) • d₁ =
          s₀ • d₁ - (-s₀) • d₁ := by
        rw [neg_smul, sub_neg_eq_add, ← add_smul, two_mul]
      rw [e, h', sub_self]
    rcases smul_eq_zero.mp this with h | h
    · linarith
    · exact hd₁ h
  · rw [segment_eq_image']
    rintro _ ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    have he :
        x + (-s₀) • d₁ +
            θ • (x + s₀ • d₁ - (x + (-s₀) • d₁)) =
          x + ((2 * θ - 1) * s₀) • d₁ := by
      rw [add_sub_add_left_eq_sub, ← sub_smul]
      rw [smul_smul, add_assoc, ← add_smul]
      congr 2
      ring
    simp only
    rw [he]
    have hab : |(2 * θ - 1) * s₀| ≤ s₀ := by
      rw [abs_mul, abs_of_pos hs₀pos]
      have : |2 * θ - 1| ≤ 1 :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      nlinarith [abs_nonneg (2 * θ - 1)]
    have hm1 := min_le_left ε₁ (ε₂ / |c|)
    have hm2 := min_le_right ε₁ (ε₂ / |c|)
    refine ⟨hs₁ _ (by linarith), ?_⟩
    rw [hc, smul_smul]
    apply hs₂
    rw [abs_mul]
    calc
      |(2 * θ - 1) * s₀| * |c| ≤ s₀ * |c| := by gcongr
      _ < ε₂ / |c| * |c| := by
        gcongr
        linarith
      _ = ε₂ := div_mul_cancel₀ _ hcpos.ne'

private lemma macro_tile_side_eq (A : PlacedTile P)
    (i : Fin (P.disk A.form).n) :
    A.side i = segment ℝ (A.vertex i) (A.vertex (finRotate _ i)) := by
  simp [PlacedTile.side, PolygonalDisk.side, PlacedTile.vertex, vadd_segment]

private lemma macro_tile_closed (A : PlacedTile P) : IsClosed A.carrier := by
  unfold PlacedTile.carrier
  exact (P.disk A.form).compact.isClosed.vadd _

private lemma macro_tile_frontier_eq (A : PlacedTile P) :
    frontier A.carrier = ⋃ i, A.side i := by
  unfold PlacedTile.carrier PlacedTile.side
  rw [frontier, interior_vadd, closure_vadd, ← Set.vadd_set_sdiff,
    ← frontier, (P.disk A.form).frontier_eq, Set.vadd_set_iUnion]
  simp only [PolygonalDisk.side]

private lemma macro_tile_local_side (A : PlacedTile P) {q : Pt}
    (hq : q ∈ frontier A.carrier) (hv : q ∉ A.vertexSet) :
    ∃ (i : Fin (P.disk A.form).n) (r : ℝ), 0 < r ∧ q ∈ A.side i ∧
      ∀ z ∈ ball q r, z ∈ frontier A.carrier → z ∈ A.side i := by
  rw [macro_tile_frontier_eq, mem_iUnion] at hq
  obtain ⟨i, hqi⟩ := hq
  have hqopen : q ∈ openSegment ℝ (A.vertex i)
      (A.vertex (finRotate _ i)) := by
    rw [macro_tile_side_eq] at hqi
    apply mem_openSegment_of_ne_left_right
    · intro h
      exact hv ⟨i, h⟩
    · intro h
      exact hv ⟨finRotate _ i, h⟩
    · exact hqi
  let O : Set Pt := ⋃ j ∈ ({j | j ≠ i} : Set (Fin (P.disk A.form).n)),
    A.side j
  have hOc : IsClosed O := by
    apply Set.Finite.isClosed_biUnion (Set.toFinite _)
    intro j _
    rw [macro_tile_side_eq]
    exact (macro_segment_compact _ _).isClosed
  have hqO : q ∉ O := by
    intro h
    simp only [O, mem_iUnion, mem_setOf_eq] at h
    obtain ⟨j, hji, hqj⟩ := h
    rw [macro_tile_side_eq] at hqj
    have hs := (P.disk A.form).simple i j (Ne.symm hji)
    have hqroot : -A.anchor + q ∈
        segment ℝ ((P.disk A.form).vertex i)
          ((P.disk A.form).vertex (finRotate _ i)) := by
      change -A.anchor + q ∈ (P.disk A.form).side i
      unfold PlacedTile.side at hqi
      simpa [vadd_eq_add] using
        (mem_vadd_set_iff_neg_vadd_mem.mp hqi)
    have hqroot' : -A.anchor + q ∈
        segment ℝ ((P.disk A.form).vertex j)
          ((P.disk A.form).vertex (finRotate _ j)) := by
      change -A.anchor + q ∈ (P.disk A.form).side j
      have hqjSide : q ∈ A.side j := by
        rw [macro_tile_side_eq]
        exact hqj
      unfold PlacedTile.side at hqjSide
      simpa [vadd_eq_add] using
        (mem_vadd_set_iff_neg_vadd_mem.mp hqjSide)
    have hend := hs ⟨hqroot, hqroot'⟩
    rcases hend.1 with h | h
    · apply hv
      exact ⟨i,
        by simpa [PlacedTile.vertex] using (congrArg (A.anchor + ·) h).symm⟩
    · apply hv
      rw [Set.mem_singleton_iff] at h
      exact ⟨finRotate _ i,
        by simpa [PlacedTile.vertex] using (congrArg (A.anchor + ·) h).symm⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hOc.isOpen_compl q hqO
  have hqiSide : q ∈ A.side i := by
    rw [macro_tile_side_eq]
    exact openSegment_subset_segment ℝ _ _ hqopen
  refine ⟨i, r, hr, hqiSide, ?_⟩
  intro z hzr hzf
  rw [macro_tile_frontier_eq, mem_iUnion] at hzf
  obtain ⟨j, hzj⟩ := hzf
  by_cases hji : j = i
  · simpa [hji] using hzj
  · apply (hrO hzr).elim
    exact Set.mem_iUnion₂.mpr ⟨j, hji, hzj⟩

private lemma macro_tile_side_unique (A : PlacedTile P) {q : Pt}
    (hv : q ∉ A.vertexSet) {i j : Fin (P.disk A.form).n}
    (hqi : q ∈ A.side i) (hqj : q ∈ A.side j) : i = j := by
  by_contra hij
  have hqiRoot : -A.anchor + q ∈ (P.disk A.form).side i := by
    unfold PlacedTile.side at hqi
    simpa [vadd_eq_add] using
      (mem_vadd_set_iff_neg_vadd_mem.mp hqi)
  have hqjRoot : -A.anchor + q ∈ (P.disk A.form).side j := by
    unfold PlacedTile.side at hqj
    simpa [vadd_eq_add] using
      (mem_vadd_set_iff_neg_vadd_mem.mp hqj)
  have hs := (P.disk A.form).simple i j hij ⟨hqiRoot, hqjRoot⟩
  rcases hs.1 with h | h
  · apply hv
    exact ⟨i,
      by simpa [PlacedTile.vertex] using (congrArg (A.anchor + ·) h).symm⟩
  · rw [Set.mem_singleton_iff] at h
    apply hv
    exact ⟨finRotate _ i,
      by simpa [PlacedTile.vertex] using (congrArg (A.anchor + ·) h).symm⟩

private lemma macro_tile_side_subset_frontier (A : PlacedTile P)
    (i : Fin (P.disk A.form).n) : A.side i ⊆ frontier A.carrier := by
  rw [macro_tile_frontier_eq]
  exact subset_iUnion (fun j => A.side j) i

private lemma macro_finite_pos_lower {X : Type*} {S : Set X}
    (hS : S.Finite) (r : X → ℝ) (hr : ∀ x ∈ S, 0 < r x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, δ ≤ r x := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert a S ha hS ih =>
      obtain ⟨δ, hδ, hδle⟩ := ih (fun x hx => hr x (Set.mem_insert_of_mem a hx))
      refine ⟨min δ (r a), lt_min hδ (hr a (Set.mem_insert a S)), ?_⟩
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hδle x hx)

private lemma macro_support_closed (M : MacroPatch P) :
    IsClosed (support M.tiles) := by
  exact M.finite.isClosed_biUnion fun A _ => macro_tile_closed A

private lemma macro_map_frontier (M : MacroPatch P) {x : Pt}
    (hx : x ∈ frontier (P.disk M.root).carrier) :
    M.map x ∈ frontier (support M.tiles) := by
  have hspos : 0 < M.θ ^ M.j := pow_pos (lt_trans zero_lt_one M.one_lt) _
  have hs : M.θ ^ M.j ≠ 0 := hspos.ne'
  rw [M.support_eq, frontier, interior_vadd, closure_vadd,
    interior_smul₀ hs, closure_smul₀ (M.θ ^ M.j) (P.disk M.root).carrier,
    ← Set.vadd_set_sdiff, ← Set.smul_set_sdiff₀ hs, ← frontier]
  exact Set.vadd_mem_vadd_set (Set.smul_mem_smul_set hx)

private lemma macro_point_on_common_line {a b q z p R : Pt} {t : ℝ}
    (hq : q ∈ segment ℝ a b) (hz : z ∈ segment ℝ a b)
    (hp : p ∈ segment ℝ a b) (hpq : p ≠ q) (ht : 0 < t)
    (hzR : z = q + t • (R - q)) :
    ∃ c : ℝ, R = q + c • (p - q) := by
  rw [crown_mem_segment_iff] at hq hz hp
  obtain ⟨α, _, _, hq⟩ := hq
  obtain ⟨γ, _, _, hz⟩ := hz
  obtain ⟨β, _, _, hp⟩ := hp
  let d := b - a
  have hpform : p - q = (β - α) • d := by
    dsimp only [d]
    rw [hp, hq]
    module
  have hzform : z - q = (γ - α) • d := by
    dsimp only [d]
    rw [hz, hq]
    module
  have hba : β - α ≠ 0 := by
    intro h
    apply hpq
    rw [sub_eq_zero.mp h] at hp
    exact hp.trans hq.symm
  have htform : t • (R - q) = (γ - α) • d := by
    rw [← hzform, hzR, add_sub_cancel_left]
  have hRq : R - q = t⁻¹ • ((γ - α) • d) := by
    have h := congrArg (fun w : Pt => t⁻¹ • w) htform
    simpa [inv_smul_smul₀ ht.ne'] using h
  refine ⟨(γ - α) / (t * (β - α)), ?_⟩
  have heq : R - q =
      ((γ - α) / (t * (β - α))) • (p - q) := by
    rw [hRq, hpform, smul_smul, smul_smul]
    congr 1
    field_simp
  simpa [add_comm] using sub_eq_iff_eq_add.mp heq

/-- `lem:macrocorner`: every genuine macro corner is a listed vertex of at
least one child tile. -/
theorem macrocornerIsChildVertex (M : MacroPatch P) {q : Pt}
    (hq : q ∈ genuineMacroCorners M) : IsVertexOf M.tiles q := by
  classical
  rw [genuineMacroCorners, PolygonalDisk.genuineCorners] at hq
  obtain ⟨v, ⟨k, hk, rfl⟩, rfl⟩ := hq
  let D := P.disk M.root
  change D.IsGenuineVertex k at hk
  let q := M.map (D.vertex k)
  change IsVertexOf M.tiles q
  by_contra hvertex
  rw [IsVertexOf] at hvertex
  push_neg at hvertex
  have hvfront : D.vertex k ∈ frontier D.carrier := by
    rw [D.frontier_eq]
    exact Set.mem_iUnion.mpr
      ⟨k, left_mem_segment ℝ (D.vertex k) (D.vertex (finRotate D.n k))⟩
  have hqfront : q ∈ frontier (support M.tiles) :=
    macro_map_frontier M hvfront
  have hradius : ∀ A : PlacedTile P, ∃ r : ℝ, 0 < r ∧
      (A ∈ M.tiles → ∀ z ∈ ball q r, z ∈ A.carrier →
        z ∉ interior A.carrier →
        ∃ i, q ∈ A.side i ∧ z ∈ A.side i) := by
    intro A
    by_cases hA : A ∈ M.tiles
    · by_cases hqA : q ∈ A.carrier
      · have hqAi : q ∉ interior A.carrier := by
          intro h
          exact hqfront.2 (interior_mono
            (fun x hx => Set.mem_iUnion₂.mpr ⟨A, hA, hx⟩) h)
        have hqAf : q ∈ frontier A.carrier := by
          rw [frontier, (macro_tile_closed A).closure_eq]
          exact ⟨hqA, hqAi⟩
        obtain ⟨i, r, hr, hqi, hlocal⟩ :=
          macro_tile_local_side A hqAf (hvertex A hA)
        refine ⟨r, hr, fun _ z hz hzA hzi => ⟨i, hqi, hlocal z hz ?_⟩⟩
        rw [frontier, (macro_tile_closed A).closure_eq]
        exact ⟨hzA, hzi⟩
      · obtain ⟨r, hr, hball⟩ :=
          Metric.isOpen_iff.mp (macro_tile_closed A).isOpen_compl q hqA
        refine ⟨r, hr, fun _ z hz hzA _ => ?_⟩
        exact (hball hz hzA).elim
    · exact ⟨1, zero_lt_one, fun h => (hA h).elim⟩
  choose rad hradpos hrad using hradius
  obtain ⟨δ, hδ, hδle⟩ :=
    macro_finite_pos_lower M.finite rad (fun A hA => hradpos A)
  have hedge : ∀ rroot : Pt, rroot ≠ D.vertex k →
      segment ℝ (D.vertex k) rroot ⊆ frontier D.carrier →
      ∃ A ∈ M.tiles, ∃ (i : Fin (P.disk A.form).n) (t : ℝ) (z : Pt),
        0 < t ∧ z = q + t • (M.map rroot - q) ∧
        q ∈ A.side i ∧ z ∈ A.side i := by
    intro rroot hrne hrside
    have hscale : M.θ ^ M.j ≠ 0 :=
      (pow_pos (lt_trans zero_lt_one M.one_lt) _).ne'
    have hmapne : M.map rroot ≠ q := by
      intro h
      apply hrne
      apply smul_right_injective Pt hscale
      change M.offset + (M.θ ^ M.j) • rroot =
        M.offset + (M.θ ^ M.j) • D.vertex k at h
      exact add_left_cancel h
    have hnorm : 0 < ‖M.map rroot - q‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hmapne)
    let t : ℝ := min (1 / 2) (δ / (2 * ‖M.map rroot - q‖))
    have ht : 0 < t :=
      lt_min (by norm_num) (div_pos hδ (by positivity))
    have htone : t < 1 :=
      lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    let xroot := D.vertex k + t • (rroot - D.vertex k)
    let z := M.map xroot
    have hxseg : xroot ∈ segment ℝ (D.vertex k) rroot :=
      crown_mem_segment_iff.mpr ⟨t, ht.le, htone.le, rfl⟩
    have hzfront : z ∈ frontier (support M.tiles) :=
      macro_map_frontier M (hrside hxseg)
    have hzsupport : z ∈ support M.tiles :=
      (macro_support_closed M).frontier_subset hzfront
    have hzrel : z = q + t • (M.map rroot - q) := by
      dsimp only [z, xroot, q, MacroPatch.map]
      module
    have hzdist : dist z q < δ := by
      rw [hzrel, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg ht.le]
      have htle : t ≤ δ / (2 * ‖M.map rroot - q‖) :=
        min_le_right _ _
      calc
        t * ‖M.map rroot - q‖ ≤
            (δ / (2 * ‖M.map rroot - q‖)) *
              ‖M.map rroot - q‖ := by gcongr
        _ = δ / 2 := by field_simp
        _ < δ := by linarith
    rw [support, mem_iUnion] at hzsupport
    obtain ⟨A, hzsupport⟩ := hzsupport
    rw [mem_iUnion] at hzsupport
    obtain ⟨hA, hzA⟩ := hzsupport
    have hzi : z ∉ interior A.carrier := by
      intro h
      apply hzfront.2
      exact interior_mono
        (fun x hx => Set.mem_iUnion₂.mpr ⟨A, hA, hx⟩) h
    obtain ⟨i, hqi, hziSide⟩ := hrad A hA z
      (Metric.ball_subset_ball (hδle A hA) hzdist) hzA hzi
    exact ⟨A, hA, i, t, z, ht, hzrel, hqi, hziSide⟩
  let kp : Fin D.n := (finRotate D.n).symm k
  have hkprot : finRotate D.n kp = k := Equiv.apply_symm_apply _ k
  have hkpn : D.vertex kp ≠ D.vertex k := by
    intro h
    have heq : kp = k := D.vertex_injective h
    have hbad := crown_finRotate_ne_self (n := D.n)
      (by have := D.three_le; omega) kp
    apply hbad
    rw [hkprot, heq]
  have hkn : D.vertex (finRotate D.n k) ≠ D.vertex k := by
    intro h
    exact crown_finRotate_ne_self (n := D.n)
      (by have := D.three_le; omega) k
      (D.vertex_injective h)
  have hprev : segment ℝ (D.vertex k) (D.vertex kp) ⊆ frontier D.carrier := by
    intro x hx
    rw [D.frontier_eq]
    apply Set.mem_iUnion.mpr
    refine ⟨kp, ?_⟩
    rw [hkprot, segment_symm]
    exact hx
  have hnext : segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ⊆
      frontier D.carrier := by
    rw [D.frontier_eq]
    exact subset_iUnion
      (fun i => segment ℝ (D.vertex i) (D.vertex (finRotate D.n i))) k
  obtain ⟨A₁, hA₁, i₁, t₁, z₁, ht₁, hz₁, hq₁, hzi₁⟩ :=
    hedge (D.vertex kp) hkpn hprev
  obtain ⟨A₂, hA₂, i₂, t₂, z₂, ht₂, hz₂, hq₂, hzi₂⟩ :=
    hedge (D.vertex (finRotate D.n k)) hkn hnext
  have hcommon : ∃ p : Pt, p ≠ q ∧ p ∈ A₁.side i₁ ∧ p ∈ A₂.side i₂ := by
    by_cases hAeq : A₁ = A₂
    · subst A₂
      have hi : i₁ = i₂ :=
        macro_tile_side_unique A₁ (hvertex A₁ hA₁) hq₁ hq₂
      subst i₂
      refine ⟨z₁, ?_, hzi₁, hzi₁⟩
      intro h
      have hdiff : M.map (D.vertex kp) - q ≠ 0 := by
        rw [sub_ne_zero]
        intro heq
        apply hkpn
        apply smul_right_injective Pt
          ((pow_pos (lt_trans zero_lt_one M.one_lt) M.j).ne')
        change M.offset + (M.θ ^ M.j) • D.vertex kp =
          M.offset + (M.θ ^ M.j) • D.vertex k at heq
        exact add_left_cancel heq
      rw [h] at hz₁
      have hzero : t₁ • (M.map (D.vertex kp) - q) = 0 := by
        simpa using (congrArg (fun w : Pt => w - q) hz₁).symm
      rcases smul_eq_zero.mp hzero with htzero | hzero
      · exact ht₁.ne' htzero
      · exact hdiff hzero
    · obtain ⟨j₁, j₂, hqj₁, hqj₂, x, y, hxy, hseg⟩ :=
        macro_tiles_share_local_side (M.disjoint hA₁ hA₂ hAeq)
          ((macro_tile_closed A₁).frontier_subset
            (macro_tile_side_subset_frontier A₁ i₁ hq₁))
          ((macro_tile_closed A₂).frontier_subset
            (macro_tile_side_subset_frontier A₂ i₂ hq₂))
          (hvertex A₁ hA₁) (hvertex A₂ hA₂)
      have hj₁ : j₁ = i₁ :=
        macro_tile_side_unique A₁ (hvertex A₁ hA₁) hqj₁ hq₁
      have hj₂ : j₂ = i₂ :=
        macro_tile_side_unique A₂ (hvertex A₂ hA₂) hqj₂ hq₂
      subst j₁
      subst j₂
      by_cases hxq : x = q
      · refine ⟨y, ?_, hseg (right_mem_segment ℝ x y) |>.1,
          hseg (right_mem_segment ℝ x y) |>.2⟩
        intro hyq
        exact hxy (hxq.trans hyq.symm)
      · exact ⟨x, hxq, (hseg (left_mem_segment ℝ x y)).1,
          (hseg (left_mem_segment ℝ x y)).2⟩
  obtain ⟨p, hpq, hp₁, hp₂⟩ := hcommon
  rw [macro_tile_side_eq] at hq₁ hzi₁ hp₁ hq₂ hzi₂ hp₂
  obtain ⟨c₁, hc₁⟩ :=
    macro_point_on_common_line hq₁ hzi₁ hp₁ hpq ht₁ hz₁
  obtain ⟨c₂, hc₂⟩ :=
    macro_point_on_common_line hq₂ hzi₂ hp₂ hpq ht₂ hz₂
  have hscale : M.θ ^ M.j ≠ 0 :=
    (pow_pos (lt_trans zero_lt_one M.one_lt) M.j).ne'
  have hpull : ∀ (r : Pt) (c : ℝ),
      M.map r = q + c • (p - q) →
      r = c • ((M.θ ^ M.j)⁻¹ • (p - q)) + D.vertex k := by
    intro r c hc
    have hc' : (M.θ ^ M.j) • (r - D.vertex k) =
        c • (p - q) := by
      dsimp only [q, MacroPatch.map] at hc
      have hc0 : (M.θ ^ M.j) • r =
          (M.θ ^ M.j) • D.vertex k + c • (p - q) := by
        have hcReassoc : M.offset + (M.θ ^ M.j) • r =
            M.offset + ((M.θ ^ M.j) • D.vertex k +
              c • (p - q)) := by
          simpa [add_assoc] using hc
        exact add_left_cancel hcReassoc
      rw [smul_sub]
      apply sub_eq_iff_eq_add.mpr
      simpa [add_comm] using hc0
    have hsub : r - D.vertex k =
        c • ((M.θ ^ M.j)⁻¹ • (p - q)) := by
      calc
        r - D.vertex k = 1 • (r - D.vertex k) :=
          (one_smul ℝ (r - D.vertex k)).symm
        _ = ((M.θ ^ M.j)⁻¹ * (M.θ ^ M.j)) •
            (r - D.vertex k) := by
          simp [inv_mul_cancel₀ hscale]
        _ = (M.θ ^ M.j)⁻¹ •
            ((M.θ ^ M.j) • (r - D.vertex k)) := by
          rw [smul_smul]
        _ = (M.θ ^ M.j)⁻¹ • (c • (p - q)) := by rw [hc']
        _ = c • ((M.θ ^ M.j)⁻¹ • (p - q)) := by
          rw [smul_smul, smul_smul]
          congr 1
          ring
    simpa [add_comm] using sub_eq_iff_eq_add.mp hsub
  apply hk
  rw [collinear_iff_of_mem (show D.vertex k ∈
    ({D.vertex kp, D.vertex k, D.vertex (finRotate D.n k)} : Set Pt) by simp)]
  refine ⟨(M.θ ^ M.j)⁻¹ • (p - q), ?_⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨c₁, hpull _ _ hc₁⟩
  · exact ⟨0, by simp⟩
  · exact ⟨c₂, hpull _ _ hc₂⟩

/-! ## `lem:endpoint-gap` -/

private lemma gap_inner_zero_of_mem_segment {u w p y x d m : Pt}
    (hp : p ∈ segment ℝ u w) (hy : y ∈ segment ℝ u w) (hx : x ∈ segment ℝ u w)
    {s : ℝ} (hs : s ≠ 0) (hd : d ≠ 0) (hxp : x = p + s • d) (hmd : inner ℝ m d = 0) :
    inner ℝ m (y - p) = 0 := by
  rw [crown_mem_segment_iff] at hp hy hx
  obtain ⟨t₁, -, -, rfl⟩ := hp
  obtain ⟨t₂, -, -, rfl⟩ := hy
  obtain ⟨t₃, -, -, h3⟩ := hx
  have key : (t₃ - t₁) • (w - u) = s • d := by
    rw [hxp] at h3
    have h4 : u + t₁ • (w - u) + s • d - (u + t₁ • (w - u)) = u + t₃ • (w - u) - (u + t₁ • (w - u)) := by
      rw [h3]
    rw [add_sub_cancel_left] at h4
    rw [h4]
    module
  have h1 : (t₃ - t₁) * inner ℝ m (w - u) = 0 := by
    rw [← inner_smul_right, key, inner_smul_right, hmd, mul_zero]
  have ht : t₃ - t₁ ≠ 0 := by
    intro h
    rw [h, zero_smul] at key
    exact smul_ne_zero hs hd key.symm
  have h2 : inner ℝ m (w - u) = 0 := (mul_eq_zero.mp h1).resolve_left ht
  have : u + t₂ • (w - u) - (u + t₁ • (w - u)) = (t₂ - t₁) • (w - u) := by module
  rw [this, inner_smul_right, h2, mul_zero]

private lemma gap_endpoint_two_sided_left {u w e : Pt}
    (h1 : u + e ∈ segment ℝ u w) (h2 : u - e ∈ segment ℝ u w) : e = 0 := by
  rw [crown_mem_segment_iff] at h1 h2
  obtain ⟨t, ht0, -, h1⟩ := h1
  obtain ⟨t', ht0', -, h2⟩ := h2
  have he : e = t • (w - u) := add_left_cancel h1
  have he' : -e = t' • (w - u) := by
    rw [sub_eq_add_neg] at h2
    exact add_left_cancel h2
  have hsum : (t + t') • (w - u) = 0 := by
    rw [add_smul, ← he, ← he', add_neg_cancel]
  rcases smul_eq_zero.mp hsum with h | h
  · have : t = 0 := by linarith
    rw [he, this, zero_smul]
  · rw [he, h, smul_zero]

private lemma gap_endpoint_two_sided {u w p e : Pt} (hp : p = u ∨ p = w)
    (h1 : p + e ∈ segment ℝ u w) (h2 : p - e ∈ segment ℝ u w) : e = 0 := by
  rcases hp with rfl | rfl
  · exact gap_endpoint_two_sided_left h1 h2
  · rw [segment_symm] at h1 h2
    exact gap_endpoint_two_sided_left h1 h2

private lemma gap_side_index {D : PolygonalDisk} {k j : Fin D.n}
    (h : D.vertex k ∈ ({D.vertex j, D.vertex (finRotate D.n j)} : Set Pt)) :
    j = k ∨ finRotate D.n j = k := by
  rcases h with h | h
  · exact Or.inl (D.vertex_injective h).symm
  · exact Or.inr (D.vertex_injective (Set.mem_singleton_iff.mp h)).symm

private lemma gap_frontier_on_line (D : PolygonalDisk) {a b p m : Pt} (hab : a ≠ b)
    (hseg : segment ℝ a b ⊆ frontier D.carrier) (hp : p ∈ openSegment ℝ a b)
    (hmd : inner ℝ m (b - a) = 0) :
    ∃ ε > 0, ∀ y ∈ ball p ε, y ∈ frontier D.carrier → inner ℝ m (y - p) = 0 := by
  obtain ⟨r, hr, hloc⟩ := crown_local_boundary D (v := p)
  refine ⟨r, hr, fun y hy hyf => ?_⟩
  by_contra hne
  obtain ⟨t, ht0, ht1, rfl⟩ := crown_mem_openSegment_iff.mp hp
  have hd : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hdn : 0 < ‖b - a‖ := norm_pos_iff.mpr hd
  set s := min (min t (1 - t) / 2) (r / (2 * ‖b - a‖)) with hs_def
  have hmin : 0 < min t (1 - t) := lt_min ht0 (by linarith)
  have hs : 0 < s := lt_min (by positivity) (by positivity)
  have hs1 : s ≤ min t (1 - t) / 2 := min_le_left _ _
  have hs2 : s ≤ r / (2 * ‖b - a‖) := min_le_right _ _
  have hst : s ≤ t / 2 := hs1.trans (by have := min_le_left t (1 - t); linarith)
  have hst' : s ≤ (1 - t) / 2 := hs1.trans (by have := min_le_right t (1 - t); linarith)
  have hsd : ‖s • (b - a)‖ < r := by
    rw [norm_smul, Real.norm_of_nonneg hs.le]
    calc s * ‖b - a‖ ≤ r / (2 * ‖b - a‖) * ‖b - a‖ := by gcongr
      _ = r / 2 := by field_simp
      _ < r := by linarith
  have hplus : a + t • (b - a) + s • (b - a) ∈ segment ℝ a b :=
    crown_mem_segment_iff.mpr ⟨t + s, by linarith, by linarith, by module⟩
  have hminus : a + t • (b - a) - s • (b - a) ∈ segment ℝ a b :=
    crown_mem_segment_iff.mpr ⟨t - s, by linarith, by linarith, by module⟩
  have hbp : a + t • (b - a) + s • (b - a) ∈ ball (a + t • (b - a)) r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hsd
  have hbm : a + t • (b - a) - s • (b - a) ∈ ball (a + t • (b - a)) r := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hsd
  obtain ⟨i, hpi, hyi, -⟩ := hloc y hy hyf
  obtain ⟨j₁, hpj₁, hxj₁, -⟩ := hloc _ hbp (hseg hplus)
  obtain ⟨j₂, hpj₂, hxj₂, -⟩ := hloc _ hbm (hseg hminus)
  have hij₁ : i ≠ j₁ := by
    rintro rfl
    exact hne (gap_inner_zero_of_mem_segment hpi hyi hxj₁ hs.ne' hd rfl hmd)
  have hij₂ : i ≠ j₂ := by
    rintro rfl
    exact hne (gap_inner_zero_of_mem_segment hpi hyi hxj₂ (neg_ne_zero.mpr hs.ne') hd
      (by rw [neg_smul, sub_eq_add_neg]) hmd)
  have hs₁ := D.simple i j₁ hij₁ ⟨hpi, hpj₁⟩
  have hs₂ := D.simple i j₂ hij₂ ⟨hpi, hpj₂⟩
  obtain ⟨k, hk⟩ : ∃ k, D.vertex k = a + t • (b - a) := by
    rcases hs₁.1 with h | h
    · exact ⟨i, h.symm⟩
    · exact ⟨_, (Set.mem_singleton_iff.mp h).symm⟩
  rw [← hk] at hs₁ hs₂
  have hi := gap_side_index hs₁.1
  have hj₁ := gap_side_index hs₁.2
  have hj₂ := gap_side_index hs₂.2
  have hj : j₁ = j₂ := by
    have hinj := (finRotate D.n).injective
    rcases hi with rfl | hi
    · rcases hj₁ with h1 | h1
      · exact absurd h1.symm hij₁
      rcases hj₂ with h2 | h2
      · exact absurd h2.symm hij₂
      exact hinj (h1.trans h2.symm)
    · rcases hj₁ with h1 | h1
      · rcases hj₂ with h2 | h2
        · exact h1.trans h2.symm
        · exact absurd (hinj (hi.trans h2.symm)) hij₂
      · exact absurd (hinj (hi.trans h1.symm)) hij₁
  subst hj
  have hpend : a + t • (b - a) = D.vertex j₁ ∨ a + t • (b - a) = D.vertex (finRotate D.n j₁) := by
    rcases hs₁.2 with h | h
    · exact Or.inl (hk.symm.trans h)
    · exact Or.inr (hk.symm.trans (Set.mem_singleton_iff.mp h))
  have := gap_endpoint_two_sided hpend hxj₁ hxj₂
  exact smul_ne_zero hs.ne' hd this

private def GapSide (D : PolygonalDisk) (p m : Pt) : Prop :=
  ∃ ε > 0, ∀ y ∈ ball p ε, 0 < inner ℝ m (y - p) → y ∈ interior D.carrier

private def GapOut (D : PolygonalDisk) (p m : Pt) : Prop :=
  ∃ ε > 0, ∀ y ∈ ball p ε, 0 < inner ℝ m (y - p) → y ∉ D.carrier

private lemma gap_push_off {O : Set Pt} (hO : IsOpen O) {p z m : Pt} {ε : ℝ} (hm : m ≠ 0)
    (hz : z ∈ O) (hzp : z ∈ ball p ε) :
    ∃ z' ∈ O, z' ∈ ball p ε ∧ inner ℝ m (z - p) < inner ℝ m (z' - p) := by
  obtain ⟨η, hη, hsub⟩ := Metric.isOpen_iff.mp (hO.inter isOpen_ball) z ⟨hz, hzp⟩
  have hmn : 0 < ‖m‖ := norm_pos_iff.mpr hm
  set τ := η / (2 * ‖m‖)
  have hτ : 0 < τ := by positivity
  have hz' : z + τ • m ∈ ball z η := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ.le]
    have : τ * ‖m‖ = η / 2 := by simp only [τ]; field_simp
    rw [this]; linarith
  obtain ⟨h1, h2⟩ := hsub hz'
  refine ⟨_, h1, h2, ?_⟩
  have : z + τ • m - p = (z - p) + τ • m := by abel
  rw [this, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
  have : 0 < τ * ‖m‖ ^ 2 := by positivity
  linarith

private lemma gap_side_out_false {D : PolygonalDisk} {p m : Pt} (hm : m ≠ 0)
    (h1 : GapSide D p m) (h2 : GapOut D p m) : False := by
  obtain ⟨ε₁, hε₁, h1⟩ := h1
  obtain ⟨ε₂, hε₂, h2⟩ := h2
  obtain ⟨z, -, hz, hlt⟩ := gap_push_off isOpen_univ hm (mem_univ p)
    (mem_ball_self (lt_min hε₁ hε₂))
  rw [sub_self, inner_zero_right] at hlt
  exact h2 z (ball_subset_ball (min_le_right _ _) hz) hlt
    (interior_subset (h1 z (ball_subset_ball (min_le_left _ _) hz) hlt))

private lemma gap_halfdisk_convex (p m : Pt) (ε : ℝ) :
    Convex ℝ {y | y ∈ ball p ε ∧ 0 < inner ℝ m (y - p)} := by
  refine (convex_ball p ε).inter ?_
  intro x hx y hy a b ha hb hab
  have hx : 0 < inner ℝ m (x - p) := hx
  have hy : 0 < inner ℝ m (y - p) := hy
  show 0 < inner ℝ m (a • x + b • y - p)
  have : a • x + b • y - p = a • (x - p) + b • (y - p) := by
    have hp : p = (a + b) • p := by rw [hab, one_smul]
    conv_lhs => rw [hp]
    module
  rw [this, inner_add_right, inner_smul_right, inner_smul_right]
  rcases ha.lt_or_eq with ha | ha
  · nlinarith
  · subst ha
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy

private lemma gap_dichotomy (D : PolygonalDisk) {a b p m : Pt} (hab : a ≠ b)
    (hseg : segment ℝ a b ⊆ frontier D.carrier) (hp : p ∈ openSegment ℝ a b)
    (hm : m ≠ 0) (hmd : inner ℝ m (b - a) = 0) :
    (GapSide D p m ∧ GapOut D p (-m)) ∨ (GapSide D p (-m) ∧ GapOut D p m) := by
  obtain ⟨ε, hε, hA⟩ := gap_frontier_on_line D hab hseg hp hmd
  have hclosed : IsClosed D.carrier := D.compact.isClosed
  have half : ∀ m' : Pt, (m' = m ∨ m' = -m) →
      ({y | y ∈ ball p ε ∧ 0 < inner ℝ m' (y - p)} ⊆ interior D.carrier ∨
        {y | y ∈ ball p ε ∧ 0 < inner ℝ m' (y - p)} ⊆ D.carrierᶜ) := by
    intro m' hm'
    have key := macro_preconn_sub (s := D.carrier) (gap_halfdisk_convex p m' ε).isPreconnected ?_
    · rwa [hclosed.closure_eq] at key
    refine Set.disjoint_left.mpr fun y hy hyf => ?_
    obtain ⟨hyb, hy⟩ := hy
    have := hA y hyb hyf
    rcases hm' with rfl | rfl
    · linarith
    · rw [inner_neg_left] at hy; linarith
  have hpf : p ∈ frontier D.carrier := hseg (openSegment_subset_segment _ _ _ hp)
  have hm' : -m ≠ 0 := neg_ne_zero.mpr hm
  rcases half m (Or.inl rfl) with h1 | h1 <;> rcases half (-m) (Or.inr rfl) with h2 | h2
  · exfalso
    have hpc : p ∈ closure D.carrierᶜ := by rw [closure_compl]; exact hpf.2
    obtain ⟨z, hz, hzp⟩ := Metric.mem_closure_iff.mp hpc ε hε
    have hzb : z ∈ ball p ε := by rw [mem_ball, dist_comm]; exact hzp
    rcases lt_trichotomy 0 (inner ℝ m (z - p)) with h | h | h
    · exact hz (interior_subset (h1 ⟨hzb, h⟩))
    · obtain ⟨z', hz', hz'b, hlt⟩ := gap_push_off hclosed.isOpen_compl hm hz hzb
      rw [← h] at hlt
      exact hz' (interior_subset (h1 ⟨hz'b, hlt⟩))
    · exact hz (interior_subset (h2 ⟨hzb, by rw [inner_neg_left]; linarith⟩))
  · exact Or.inl ⟨⟨ε, hε, fun y hy hy' => h1 ⟨hy, hy'⟩⟩, ⟨ε, hε, fun y hy hy' => h2 ⟨hy, hy'⟩⟩⟩
  · exact Or.inr ⟨⟨ε, hε, fun y hy hy' => h2 ⟨hy, hy'⟩⟩, ⟨ε, hε, fun y hy hy' => h1 ⟨hy, hy'⟩⟩⟩
  · exfalso
    have hpD : p ∈ closure (interior D.carrier) := by
      rw [D.regular_closed]; exact hclosed.frontier_subset hpf
    obtain ⟨z, hz, hzp⟩ := Metric.mem_closure_iff.mp hpD ε hε
    have hzb : z ∈ ball p ε := by rw [mem_ball, dist_comm]; exact hzp
    rcases lt_trichotomy 0 (inner ℝ m (z - p)) with h | h | h
    · exact h1 ⟨hzb, h⟩ (interior_subset hz)
    · obtain ⟨z', hz', hz'b, hlt⟩ := gap_push_off isOpen_interior hm hz hzb
      rw [← h] at hlt
      exact h1 ⟨hz'b, hlt⟩ (interior_subset hz')
    · exact h2 ⟨hzb, by rw [inner_neg_left]; linarith⟩ (interior_subset hz)

private lemma gap_shift {Q : Pt → Prop} {p p' m : Pt} {ε : ℝ}
    (h : ∀ y ∈ ball p ε, 0 < inner ℝ m (y - p) → Q y) (hpp : dist p' p < ε / 2)
    (hmpp : inner ℝ m (p' - p) = 0) :
    ∀ y ∈ ball p' (ε / 2), 0 < inner ℝ m (y - p') → Q y := by
  intro y hy hy'
  apply h y
  · rw [mem_ball] at hy ⊢
    linarith [dist_triangle y p' p]
  · have : y - p = (y - p') + (p' - p) := by abel
    rw [this, inner_add_right, hmpp, add_zero]; exact hy'

private lemma gap_side_const (D : PolygonalDisk) {a b m : Pt} (hab : a ≠ b)
    (hseg : segment ℝ a b ⊆ frontier D.carrier) (hm : m ≠ 0) (hmd : inner ℝ m (b - a) = 0)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Ioo (0 : ℝ) 1) (ht₂ : t₂ ∈ Ioo (0 : ℝ) 1)
    (h : GapSide D (a + t₁ • (b - a)) m) : GapSide D (a + t₂ • (b - a)) m := by
  classical
  have hdn : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  let f : ℝ → Bool := fun t => decide (GapSide D (a + t • (b - a)) m)
  have hdist : ∀ t t' : ℝ, dist (a + t' • (b - a)) (a + t • (b - a)) = |t' - t| * ‖b - a‖ := by
    intro t t'
    rw [dist_eq_norm, show a + t' • (b - a) - (a + t • (b - a)) = (t' - t) • (b - a) by module,
      norm_smul, Real.norm_eq_abs]
  have hinn : ∀ t t' : ℝ, inner ℝ m (a + t' • (b - a) - (a + t • (b - a))) = 0 := by
    intro t t'
    rw [show a + t' • (b - a) - (a + t • (b - a)) = (t' - t) • (b - a) by module,
      inner_smul_right, hmd, mul_zero]
  have hloc : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ η > 0, ∀ t', dist t' t < η → f t' = f t := by
    intro t ht
    have hp : a + t • (b - a) ∈ openSegment ℝ a b :=
      crown_mem_openSegment_iff.mpr ⟨t, ht.1, ht.2, rfl⟩
    rcases gap_dichotomy D hab hseg hp hm hmd with ⟨⟨ε, hε, hS⟩, -⟩ | ⟨-, ⟨ε, hε, hO⟩⟩
    · refine ⟨ε / (2 * ‖b - a‖), by positivity, fun t' ht' => ?_⟩
      have hd' : dist (a + t' • (b - a)) (a + t • (b - a)) < ε / 2 := by
        rw [hdist, ← Real.dist_eq]
        calc dist t' t * ‖b - a‖ < ε / (2 * ‖b - a‖) * ‖b - a‖ := by gcongr
          _ = ε / 2 := by field_simp
      have h1 : GapSide D (a + t' • (b - a)) m := ⟨ε / 2, by positivity, gap_shift hS hd' (hinn _ _)⟩
      have h2 : GapSide D (a + t • (b - a)) m := ⟨ε, hε, hS⟩
      simp only [f, h1, h2]
    · refine ⟨ε / (2 * ‖b - a‖), by positivity, fun t' ht' => ?_⟩
      have hd' : dist (a + t' • (b - a)) (a + t • (b - a)) < ε / 2 := by
        rw [hdist, ← Real.dist_eq]
        calc dist t' t * ‖b - a‖ < ε / (2 * ‖b - a‖) * ‖b - a‖ := by gcongr
          _ = ε / 2 := by field_simp
      have h1 : ¬ GapSide D (a + t' • (b - a)) m := fun h1 =>
        gap_side_out_false hm h1 ⟨ε / 2, by positivity, gap_shift hO hd' (hinn _ _)⟩
      have h2 : ¬ GapSide D (a + t • (b - a)) m := fun h2 =>
        gap_side_out_false hm h2 ⟨ε, hε, hO⟩
      simp only [f, h1, h2]
  have hcont : ContinuousOn f (Ioo 0 1) := by
    intro t ht
    obtain ⟨η, hη, hη'⟩ := hloc t ht
    refine (ContinuousAt.congr (f := fun _ => f t) continuousAt_const ?_).continuousWithinAt
    filter_upwards [Metric.ball_mem_nhds t hη] with t' ht' using (hη' t' ht').symm
  have := isPreconnected_Ioo.constant hcont ht₁ ht₂
  simp only [f, decide_eq_decide] at this
  exact this.mp h

private lemma gap_cone_scale {A : Set Pt} {c w : Pt} (hw : w ∈ localCone A c) {lam : ℝ}
    (hl : 0 < lam) : c + lam • (w - c) ∈ localCone A c := by
  obtain ⟨ρ, hρ, h⟩ := hw
  refine ⟨ρ / lam, div_pos hρ hl, fun t ht => ?_⟩
  have := h (t * lam) ⟨mul_pos ht.1 hl, (lt_div_iff₀ hl).mp ht.2⟩
  rw [add_sub_cancel_left, smul_smul]
  exact this

private lemma gap_core (D : PolygonalDisk) {a b p : Pt} (hab : a ≠ b)
    (hseg : segment ℝ a b ⊆ frontier D.carrier) (hp : p ∈ openSegment ℝ a b) :
    ∃ ε > 0, ∀ y ∈ ball p ε, y ∈ interior D.carrier → y ∈ localCone D.carrier a := by
  obtain ⟨t, ht0, ht1, rfl⟩ := crown_mem_openSegment_iff.mp hp
  have hd : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hdn : 0 < ‖b - a‖ := norm_pos_iff.mpr hd
  obtain ⟨m, hm, hmd, hS, hO⟩ : ∃ m : Pt, m ≠ 0 ∧ inner ℝ m (b - a) = 0 ∧
      GapSide D (a + t • (b - a)) m ∧ GapOut D (a + t • (b - a)) (-m) := by
    rcases gap_dichotomy D hab hseg hp (macroPerp_ne_zero hd) (macroPerp_inner _) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, macroPerp_ne_zero hd, macroPerp_inner _, h1, h2⟩
    · refine ⟨-macroPerp (b - a), neg_ne_zero.mpr (macroPerp_ne_zero hd), ?_, h1, ?_⟩
      · rw [inner_neg_left, macroPerp_inner, neg_zero]
      · rwa [neg_neg]
  have haD : a ∈ D.carrier :=
    D.compact.isClosed.frontier_subset (hseg (left_mem_segment ℝ a b))
  obtain ⟨ρ, hρ, hloc⟩ := polygonLocalCone D haD
  set t₀ := min (t / 2) (ρ / (4 * ‖b - a‖)) with ht₀_def
  have ht₀ : 0 < t₀ := lt_min (by linarith) (by positivity)
  have ht₀t : t₀ ≤ t / 2 := min_le_left _ _
  have ht₀ρ : t₀ ≤ ρ / (4 * ‖b - a‖) := min_le_right _ _
  have hS₀ : GapSide D (a + t₀ • (b - a)) m :=
    gap_side_const D hab hseg hm hmd ⟨ht0, ht1⟩ ⟨ht₀, by linarith⟩ hS
  obtain ⟨ε₀, hε₀, hS₀⟩ := hS₀
  obtain ⟨ε₁, hε₁, hO⟩ := hO
  set lam := t / t₀ with hlam_def
  have hlam : 0 < lam := div_pos ht0 ht₀
  refine ⟨min ε₁ (lam * min ε₀ (ρ / 2)), by positivity, fun y hy hyint => ?_⟩
  have hy₁ : y ∈ ball (a + t • (b - a)) ε₁ := ball_subset_ball (min_le_left _ _) hy
  have hpos : 0 < inner ℝ m (y - (a + t • (b - a))) := by
    rcases lt_trichotomy 0 (inner ℝ m (y - (a + t • (b - a)))) with h | h | h
    · exact h
    · exfalso
      obtain ⟨z', hz', hz'b, hlt⟩ := gap_push_off isOpen_interior (neg_ne_zero.mpr hm) hyint hy₁
      rw [inner_neg_left, ← h, neg_zero] at hlt
      exact hO z' hz'b hlt (interior_subset hz')
    · exfalso
      exact hO y hy₁ (by rw [inner_neg_left]; linarith) (interior_subset hyint)
  set w := a + lam⁻¹ • (y - a) with hw_def
  have hlt0 : lam⁻¹ * t = t₀ := by rw [hlam_def]; field_simp
  have hw_eq : w - (a + t₀ • (b - a)) = lam⁻¹ • (y - (a + t • (b - a))) := by
    rw [hw_def, ← hlt0]; module
  have hyd : dist y (a + t • (b - a)) < lam * min ε₀ (ρ / 2) :=
    lt_of_lt_of_le hy (min_le_right _ _)
  have hwdist : dist w (a + t₀ • (b - a)) < min ε₀ (ρ / 2) := by
    rw [dist_eq_norm, hw_eq, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hlam).le, ← dist_eq_norm]
    rw [inv_mul_lt_iff₀ hlam]; exact hyd
  have hwin : 0 < inner ℝ m (w - (a + t₀ • (b - a))) := by
    rw [hw_eq, inner_smul_right]; exact mul_pos (inv_pos.mpr hlam) hpos
  have hwD : w ∈ D.carrier :=
    interior_subset (hS₀ w (lt_of_lt_of_le hwdist (min_le_left _ _)) hwin)
  have hwa : w ∈ ball a ρ := by
    rw [mem_ball]
    have h1 : dist (a + t₀ • (b - a)) a ≤ ρ / 4 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht₀.le]
      calc t₀ * ‖b - a‖ ≤ ρ / (4 * ‖b - a‖) * ‖b - a‖ := by gcongr
        _ = ρ / 4 := by field_simp
    have h2 : dist w (a + t₀ • (b - a)) < ρ / 2 := lt_of_lt_of_le hwdist (min_le_right _ _)
    linarith [dist_triangle w (a + t₀ • (b - a)) a]
  have hwC : w ∈ localCone D.carrier a := by
    have : w ∈ D.carrier ∩ ball a ρ := ⟨hwD, hwa⟩
    rw [hloc] at this
    exact this.1
  have hyw : y = a + lam • (w - a) := by
    rw [hw_def, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul,
      add_sub_cancel]
  rw [hyw]
  exact gap_cone_scale hwC hlam

private lemma gap_macro_core (M : MacroPatch P) {a b p : Pt} (hab : a ≠ b)
    (hseg : segment ℝ a b ⊆ frontier (P.disk M.root).carrier) (hp : p ∈ openSegment ℝ a b) :
    ∃ ε > 0, ∀ y ∈ ball (M.map p) ε, y ∈ interior (support M.tiles) →
      y ∈ localCone (support M.tiles) (M.map a) := by
  obtain ⟨ε, hε, h⟩ := gap_core _ hab hseg hp
  have hc : 0 < M.θ ^ M.j := pow_pos (lt_trans zero_lt_one M.one_lt) _
  refine ⟨M.θ ^ M.j * ε, by positivity, fun y hy hyint => ?_⟩
  rw [M.support_eq, interior_vadd, interior_smul₀ hc.ne'] at hyint
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hyint
  have hzd : dist z p < ε := by
    change dist (M.offset +ᵥ M.θ ^ M.j • z) (M.map p) < M.θ ^ M.j * ε at hy
    rw [dist_eq_norm] at hy
    have : (M.offset +ᵥ M.θ ^ M.j • z) - M.map p = (M.θ ^ M.j) • (z - p) := by
      simp only [MacroPatch.map, vadd_eq_add]; module
    rw [this, norm_smul, Real.norm_of_nonneg hc.le, ← dist_eq_norm] at hy
    exact lt_of_mul_lt_mul_left hy hc.le
  obtain ⟨ρ, hρ, hcone⟩ := h z hzd hz
  refine ⟨ρ, hρ, fun t ht => ?_⟩
  rw [M.support_eq]
  refine Set.mem_vadd_set.mpr ⟨(M.θ ^ M.j) • (a + t • (z - a)),
    Set.smul_mem_smul_set (hcone t ht), ?_⟩
  simp only [MacroPatch.map, vadd_eq_add]
  module

private lemma gap_near_vertex (S : Set (PlacedTile P)) (hS : S.Finite) (q : Pt) :
    ∃ ρ > 0, ∀ y ∈ ball q ρ, y ∈ support S → ∃ A ∈ crown S q, y ∈ localCone A.carrier q := by
  have hrad : ∀ A : PlacedTile P, ∃ ρ > 0, ∀ y ∈ ball q ρ, y ∈ A.carrier →
      q ∈ A.carrier ∧ y ∈ localCone A.carrier q := by
    intro A
    by_cases hqA : q ∈ A.carrier
    · obtain ⟨ρ, hρ, h⟩ := polygonLocalCone_tile A hqA
      refine ⟨ρ, hρ, fun y hy hyA => ⟨hqA, ?_⟩⟩
      have : y ∈ A.carrier ∩ ball q ρ := ⟨hyA, hy⟩
      rw [h] at this
      exact this.1
    · obtain ⟨ρ, hρ, hb⟩ := Metric.isOpen_iff.mp (macro_tile_closed A).isOpen_compl q hqA
      exact ⟨ρ, hρ, fun y hy hyA => absurd hyA (hb hy)⟩
  choose rad hradpos hrad using hrad
  obtain ⟨ρ, hρ, hle⟩ := macro_finite_pos_lower hS rad (fun A _ => hradpos A)
  refine ⟨ρ, hρ, fun y hy hyS => ?_⟩
  rw [support, mem_iUnion₂] at hyS
  obtain ⟨A, hA, hyA⟩ := hyS
  obtain ⟨hqA, hc⟩ := hrad A y (ball_subset_ball (hle A hA) hy) hyA
  exact ⟨A, ⟨hA, hqA⟩, hc⟩

private lemma gap_interior_frontier_union {S : Set (PlacedTile P)} (hS : S.Finite) :
    interior (⋃ A ∈ S, frontier A.carrier) = ∅ := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simp
  | @insert A S hA hS ih =>
    rw [Set.biUnion_insert, interior_union_isClosed_of_interior_empty isClosed_frontier ih,
      interior_frontier (macro_tile_closed A)]

private lemma gap_translateSet_neg (S : Set (PlacedTile P)) (q : Pt) :
    translateSet q (translateSet (-q) S) = S := by
  rw [translateSet, translateSet, Set.image_image]
  convert Set.image_id S using 2
  ext A
  · rfl
  · simp [PlacedTile.translate]

private lemma gap_vertex_mem_carrier (A : PlacedTile P) {v : Pt} (hv : v ∈ A.vertexSet) :
    v ∈ A.carrier := by
  obtain ⟨i, rfl⟩ := hv
  apply (macro_tile_closed A).frontier_subset
  rw [macro_tile_frontier_eq]
  refine mem_iUnion.mpr ⟨i, ?_⟩
  rw [macro_tile_side_eq]
  exact left_mem_segment ℝ _ _


/-- `lem:endpoint-gap`: with `h = min r_* δ_*`, a child vertex in the relative
interior of a geometric macro edge incident to the genuine macro corner `q`
is at distance at least `h` from `q`. -/
theorem incidentMacroEdgeVertexGap {𝒞 : Set (Set (PlacedTile P))} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hrδ : SectorRadiusProperty 𝒞 r δ)
    (M : MacroPatch P) (hM : AllCrownsIn 𝒞 M.tiles) {q x : Pt}
    (hqx : (q, x) ∈ geometricMacroBoundary M ∨ (x, q) ∈ geometricMacroBoundary M)
    {v : Pt} (hv : IsVertexOf M.tiles v) (hvx : v ∈ openSegment ℝ q x) :
    min r δ ≤ dist v q := by
  classical
  have _hpos : 0 < min r δ := lt_min hr hδ
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, b, hab, hseg, hga, rfl, rfl⟩ : ∃ a b, a ≠ b ∧
      segment ℝ a b ⊆ frontier (P.disk M.root).carrier ∧ (P.disk M.root).IsGenuineCorner a ∧
      q = M.map a ∧ x = M.map b := by
    rcases hqx with ⟨a, b, ⟨ha, hb, hne, hs⟩, he⟩ | ⟨a, b, ⟨ha, hb, hne, hs⟩, he⟩
    · simp only [Prod.mk.injEq] at he
      exact ⟨a, b, hne, hs, ha, he.1, he.2⟩
    · simp only [Prod.mk.injEq] at he
      exact ⟨b, a, hne.symm, segment_symm ℝ a b ▸ hs, hb, he.2, he.1⟩
  have hc : 0 < M.θ ^ M.j := pow_pos (lt_trans zero_lt_one M.one_lt) _
  obtain ⟨t, ht0, ht1, hvt⟩ := crown_mem_openSegment_iff.mp hvx
  have hp : a + t • (b - a) ∈ openSegment ℝ a b :=
    crown_mem_openSegment_iff.mpr ⟨t, ht0, ht1, rfl⟩
  have hvp : v = M.map (a + t • (b - a)) := by
    rw [hvt]; simp only [MacroPatch.map]; module
  have hvq : v ≠ M.map a := by
    intro h
    rw [h] at hvx
    have hmap := left_mem_openSegment_iff.mp hvx
    apply hab
    apply smul_right_injective Pt hc.ne'
    exact add_left_cancel hmap
  have hqv : IsVertexOf M.tiles (M.map a) := macrocornerIsChildVertex M ⟨a, hga, rfl⟩
  obtain ⟨hsupp, hsep⟩ := hrδ _ (hM _ hqv) (M.map a)
  rw [gap_translateSet_neg] at hsupp hsep
  obtain ⟨B, hB, hvB⟩ := hv
  have hqB : M.map a ∈ B.carrier := by
    by_contra hqB
    obtain ⟨ρ, hρ, hnear⟩ := gap_near_vertex M.tiles M.finite (M.map a)
    obtain ⟨ε₁, hε₁, hcore⟩ := gap_macro_core M hab hseg hp
    rw [← hvp] at hcore
    set ε := min ε₁ (r - dist v (M.map a)) with hε_def
    have hε : 0 < ε := lt_min hε₁ (by linarith [min_le_left r δ])
    have hsub : interior B.carrier ∩ ball v ε ⊆
        ⋃ A ∈ crown M.tiles (M.map a), frontier A.carrier := by
      rintro y ⟨hyB, hyv⟩
      have hyR : y ∈ interior (support M.tiles) :=
        interior_mono (subset_biUnion_of_mem (u := fun A : PlacedTile P => A.carrier) hB) hyB
      obtain ⟨ρ', hρ', hcone⟩ := hcore y (ball_subset_ball (min_le_left _ _) hyv) hyR
      set s := min (ρ' / 2) (ρ / (2 * (dist y (M.map a) + 1))) with hs_def
      have hs : 0 < s := lt_min (by positivity) (by positivity)
      have hy'R := hcone s ⟨hs, lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ')⟩
      have hy'ball : M.map a + s • (y - M.map a) ∈ ball (M.map a) ρ := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le,
          ← dist_eq_norm]
        have h1 : s ≤ ρ / (2 * (dist y (M.map a) + 1)) := min_le_right _ _
        have h2 : 0 ≤ dist y (M.map a) := dist_nonneg
        calc s * dist y (M.map a) ≤ ρ / (2 * (dist y (M.map a) + 1)) * (dist y (M.map a) + 1) := by
              gcongr; linarith
          _ = ρ / 2 := by field_simp
          _ < ρ := half_lt_self hρ
      obtain ⟨A, hAK, hAc⟩ := hnear _ hy'ball hy'R
      have hyA : y ∈ localCone A.carrier (M.map a) := by
        have := gap_cone_scale hAc (inv_pos.mpr hs)
        rwa [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.ne', one_smul,
          add_sub_cancel] at this
      have hyball_r : y ∈ ball (M.map a) r := by
        rw [mem_ball]
        have h1 : dist y v < ε := by rw [← mem_ball]; exact hyv
        have h2 : ε ≤ r - dist v (M.map a) := min_le_right _ _
        linarith [dist_triangle y v (M.map a)]
      have hyOmega : y ∈ Omega (crown M.tiles (M.map a)) (M.map a) ∩ ball (M.map a) r :=
        ⟨mem_iUnion₂.mpr ⟨A, hAK, hyA⟩, hyball_r⟩
      rw [← hsupp] at hyOmega
      obtain ⟨A', hA'K, hyA'⟩ := mem_iUnion₂.mp hyOmega.1
      refine mem_iUnion₂.mpr ⟨A', hA'K, ?_⟩
      have hne : A' ≠ B := fun h => hqB (h ▸ hA'K.2)
      rw [frontier, (macro_tile_closed A').closure_eq]
      exact ⟨hyA', fun hyA'i => Set.disjoint_left.mp (M.disjoint hA'K.1 hB hne) hyA'i hyB⟩
    have hvBc : v ∈ closure (interior B.carrier) := by
      rw [macro_tile_regular B]; exact gap_vertex_mem_carrier B hvB
    obtain ⟨z, hz, hzv⟩ := Metric.mem_closure_iff.mp hvBc ε hε
    have hint : interior B.carrier ∩ ball v ε ⊆
        interior (⋃ A ∈ crown M.tiles (M.map a), frontier A.carrier) :=
      interior_maximal hsub (isOpen_interior.inter isOpen_ball)
    rw [gap_interior_frontier_union (M.finite.subset (fun A hA => hA.1))] at hint
    exact hint ⟨hz, by rw [mem_ball, dist_comm]; exact hzv⟩
  have := hsep B ⟨hB, hqB⟩ v hvB hvq
  linarith [min_le_right r δ]

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

private lemma crown_vertex_not_mem_open_side (D : PolygonalDisk)
    (k i : Fin D.n) :
    D.vertex k ∉ openSegment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) := by
  intro hk
  by_cases hki : k = i
  · subst k
    have hne : D.vertex i ≠ D.vertex (finRotate D.n i) := by
      intro h
      exact (crown_finRotate_ne_self (by have := D.three_le; omega) i)
        (D.vertex_injective h).symm
    exact hne ((left_mem_openSegment_iff).mp hk)
  · have h := D.simple i k (Ne.symm hki)
      ⟨openSegment_subset_segment ℝ _ _ hk,
        left_mem_segment ℝ (D.vertex k) (D.vertex (finRotate D.n k))⟩
    rcases h.1 with h | h
    · have heq := left_mem_openSegment_iff.mp (h ▸ hk)
      exact (crown_finRotate_ne_self (by have := D.three_le; omega) i)
        (D.vertex_injective heq).symm
    · rw [Set.mem_singleton_iff] at h
      have heq := right_mem_openSegment_iff.mp (h ▸ hk)
      exact (crown_finRotate_ne_self (by have := D.three_le; omega) i)
        (D.vertex_injective heq).symm

private lemma crown_side_through_vertex (D : PolygonalDisk)
    (k i : Fin D.n) (hki : D.vertex k ∈ D.side i) :
    k = i ∨ k = finRotate D.n i := by
  by_contra h
  push_neg at h
  apply crown_vertex_not_mem_open_side D k i
  change D.vertex k ∈ segment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) at hki
  exact mem_openSegment_of_ne_left_right
    (fun hk => h.1 (D.vertex_injective hk.symm))
    (fun hk => h.2 (D.vertex_injective hk.symm)) hki

private lemma crown_exists_near_openSegment {a b : Pt} (hab : a ≠ b)
    {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ ball a r, z ∈ openSegment ℝ a b := by
  let t := min (1 / 2 : ℝ) (r / (2 * ‖b - a‖))
  have hn : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have ht : 0 < t := lt_min (by norm_num) (div_pos hr (by positivity))
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨a + t • (b - a), ?_,
    crown_mem_openSegment_iff.mpr ⟨t, ht, ht1, rfl⟩⟩
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht]
  have hle : t ≤ r / (2 * ‖b - a‖) := min_le_right _ _
  calc
    t * ‖b - a‖ ≤ (r / (2 * ‖b - a‖)) * ‖b - a‖ :=
      mul_le_mul_of_nonneg_right hle hn.le
    _ = r / 2 := by field_simp
    _ < r := by linarith

private lemma crown_angle_eq_zero_of_mem_side {q z z' : Pt}
    {D : PolygonalDisk} {i : Fin D.n} (hq : q = D.vertex i ∨
      q = D.vertex (finRotate D.n i)) (hz : z ∈ D.side i)
    (hz' : z' ∈ D.side i) (hzq : z ≠ q) (hzq' : z' ≠ q) :
    EuclideanGeometry.angle z q z' = 0 := by
  rcases hq with rfl | rfl
  · change z ∈ segment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) at hz
    change z' ∈ segment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) at hz'
    rw [crown_mem_segment_iff] at hz hz'
    obtain ⟨s, hs0, -, rfl⟩ := hz
    obtain ⟨t, ht0, -, rfl⟩ := hz'
    have hs : 0 < s := hs0.lt_of_ne (by
      intro hs
      apply hzq
      simp [hs])
    have ht : 0 < t := ht0.lt_of_ne (by
      intro ht
      apply hzq'
      simp [ht])
    unfold EuclideanGeometry.angle
    simp only [vsub_eq_sub, add_sub_cancel_left]
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
      InnerProductGeometry.angle_smul_right_of_pos _ _ ht]
    exact InnerProductGeometry.angle_self
      (sub_ne_zero.mpr (by
        intro h
        exact (crown_finRotate_ne_self (by have := D.three_le; omega) i)
          (D.vertex_injective h)))
  · change z ∈ segment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) at hz
    change z' ∈ segment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) at hz'
    rw [segment_symm] at hz hz'
    rw [crown_mem_segment_iff] at hz hz'
    obtain ⟨s, hs0, -, rfl⟩ := hz
    obtain ⟨t, ht0, -, rfl⟩ := hz'
    have hs : 0 < s := hs0.lt_of_ne (by
      intro hs
      apply hzq
      simp [hs])
    have ht : 0 < t := ht0.lt_of_ne (by
      intro ht
      apply hzq'
      simp [ht])
    unfold EuclideanGeometry.angle
    simp only [vsub_eq_sub, add_sub_cancel_left]
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hs,
      InnerProductGeometry.angle_smul_right_of_pos _ _ ht]
    exact InnerProductGeometry.angle_self
      (sub_ne_zero.mpr (by
        intro h
        exact (crown_finRotate_ne_self (by have := D.three_le; omega) i)
          (D.vertex_injective h).symm))

private lemma crown_other_endpoint_mem_line {q z x y : Pt}
    {D : PolygonalDisk} {i : Fin D.n} (hq : q = D.vertex i ∨
      q = D.vertex (finRotate D.n i)) (hz : z ∈ D.side i)
    (hzq : z ≠ q) (hqline : q ∈ line[ℝ, x, y])
    (hzline : z ∈ line[ℝ, x, y]) :
    D.vertex i ∈ line[ℝ, x, y] ∧
      D.vertex (finRotate D.n i) ∈ line[ℝ, x, y] := by
  have hline : line[ℝ, q, z] ≤ line[ℝ, x, y] :=
    affineSpan_pair_le_of_mem_of_mem hqline hzline
  rcases hq with hq | hq
  · subst q
    refine ⟨hqline, hline ?_⟩
    apply Wbtw.right_mem_affineSpan_of_left_ne
    · change z ∈ segment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) at hz
      exact mem_segment_iff_wbtw.mp hz
    · exact Ne.symm hzq
  · subst q
    refine ⟨hline ?_, hqline⟩
    apply Wbtw.right_mem_affineSpan_of_left_ne
    · change z ∈ segment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) at hz
      rw [segment_symm] at hz
      exact mem_segment_iff_wbtw.mp hz
    · exact Ne.symm hzq

private lemma crown_genuineCorner_not_mem_geometricEdge (D : PolygonalDisk)
    {q x y : Pt} (hq : D.IsGenuineCorner q)
    (hxy : D.IsGeometricEdge x y) (hqx : q ≠ x) (hqy : q ≠ y) :
    q ∉ segment ℝ x y := by
  intro hqxy
  obtain ⟨k, hk, rfl⟩ := hq
  have hqopen : D.vertex k ∈ openSegment ℝ x y :=
    mem_openSegment_of_ne_left_right (Ne.symm hqx) (Ne.symm hqy) hqxy
  have hbase : Sbtw ℝ x (D.vertex k) y :=
    crown_sbtw_of_mem_openSegment hxy.2.2.1 hqopen
  obtain ⟨r, hr, hboundary⟩ := crown_local_boundary D (v := D.vertex k)
  obtain ⟨z, hzr, hz⟩ := crown_exists_near_openSegment hbase.ne_left hr
  obtain ⟨z', hz'r, hz'⟩ := crown_exists_near_openSegment hbase.ne_right hr
  have hzxy : z ∈ segment ℝ x y :=
    (convex_segment x y).segment_subset hqxy (left_mem_segment ℝ x y)
      (openSegment_subset_segment ℝ _ _ hz)
  have hz'xy : z' ∈ segment ℝ x y :=
    (convex_segment x y).segment_subset hqxy (right_mem_segment ℝ x y)
      (openSegment_subset_segment ℝ _ _ hz')
  obtain ⟨i, hki, hzi, -⟩ := hboundary z hzr (hxy.2.2.2 hzxy)
  obtain ⟨j, hkj, hzj, -⟩ := hboundary z' hz'r (hxy.2.2.2 hz'xy)
  have hi := crown_side_through_vertex D k i hki
  have hj := crown_side_through_vertex D k j hkj
  have hzq : z ≠ D.vertex k :=
    (crown_sbtw_of_mem_openSegment hbase.ne_left hz).ne_left
  have hz'q : z' ≠ D.vertex k :=
    (crown_sbtw_of_mem_openSegment hbase.ne_right hz').ne_left
  have hij : i ≠ j := by
    intro hij
    subst j
    have hzero := crown_angle_eq_zero_of_mem_side
      (D := D) (i := i) (q := D.vertex k) (z := z) (z' := z')
      (hi.elim (fun h => Or.inl (congrArg D.vertex h))
        (fun h => Or.inr (congrArg D.vertex h))) hzi hzj hzq hz'q
    have hxzq : Sbtw ℝ x z (D.vertex k) := by
      rw [sbtw_comm]
      exact crown_sbtw_of_mem_openSegment hbase.ne_left hz
    have hqz'y : Sbtw ℝ (D.vertex k) z' y :=
      crown_sbtw_of_mem_openSegment hbase.ne_right hz'
    have hzqz' : Sbtw ℝ z (D.vertex k) z' :=
      (hbase.trans_left_right hxzq).trans_right_left hqz'y
    linarith [hzqz'.angle₁₂₃_eq_pi, Real.pi_pos]
  have hqline : D.vertex k ∈ line[ℝ, x, y] :=
    (mem_segment_iff_wbtw.mp hqxy).mem_affineSpan
  have hzline : z ∈ line[ℝ, x, y] :=
    (mem_segment_iff_wbtw.mp hzxy).mem_affineSpan
  have hz'line : z' ∈ line[ℝ, x, y] :=
    (mem_segment_iff_wbtw.mp hz'xy).mem_affineSpan
  have hiend := crown_other_endpoint_mem_line (D := D) (i := i)
    (q := D.vertex k) (z := z) (x := x) (y := y)
    (hi.elim (fun h => Or.inl (congrArg D.vertex h))
      (fun h => Or.inr (congrArg D.vertex h))) hzi hzq hqline hzline
  have hjend := crown_other_endpoint_mem_line (D := D) (i := j)
    (q := D.vertex k) (z := z') (x := x) (y := y)
    (hj.elim (fun h => Or.inl (congrArg D.vertex h))
      (fun h => Or.inr (congrArg D.vertex h))) hzj hz'q hqline hz'line
  apply hk
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact (hij (hi.symm.trans hj)).elim
  · subst i
    have hj' : j = (finRotate D.n).symm k := by
      apply (finRotate D.n).injective
      simpa using hj.symm
    subst j
    exact collinear_triple_of_mem_affineSpan_pair
      (p₄ := x) (p₅ := y) hjend.1 hqline hiend.2
  · subst j
    have hi' : i = (finRotate D.n).symm k := by
      apply (finRotate D.n).injective
      simpa using hi.symm
    subst i
    exact collinear_triple_of_mem_affineSpan_pair
      (p₄ := x) (p₅ := y) hiend.1 hqline hjend.2
  · exfalso
    apply hij
    apply (finRotate D.n).injective
    exact hi.symm.trans hj

private lemma crown_reflex_angle_pos (D : PolygonalDisk) {q a b : Pt}
    (h : D.IsReflexCorner q a b) :
    0 < EuclideanGeometry.angle a q b := by
  have hqa : q ≠ a := h.1.2.2.1
  have hqb : q ≠ b := h.2.1.2.2.1
  have hang0 : EuclideanGeometry.angle a q b ≠ 0 := by
    intro hang
    unfold EuclideanGeometry.angle at hang
    obtain ⟨-, t, ht, hba⟩ := InnerProductGeometry.angle_eq_zero_iff.mp hang
    change b - q = t • (a - q) at hba
    have hnorma : 0 < ‖a - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hqa.symm)
    have hnormb : ‖b - q‖ = t * ‖a - q‖ := by
      rw [hba, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hunit : ‖b - q‖⁻¹ • (b - q) = ‖a - q‖⁻¹ • (a - q) := by
      rw [hba]
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_inv, smul_smul]
      congr 1
      field_simp
    obtain ⟨s, ⟨hs0, hslt⟩, hsout⟩ :=
      h.2.2.2 (‖a - q‖ / 2) (by positivity)
    apply hsout
    rw [hunit, ← two_smul ℝ, smul_smul]
    apply crown_frontier_subset_of_isClosed D.compact.isClosed
    apply h.1.2.2.2
    apply crown_mem_segment_iff.mpr
    refine ⟨s * 2 * ‖a - q‖⁻¹, by positivity, ?_, ?_⟩
    · calc
        s * 2 * ‖a - q‖⁻¹ ≤ ‖a - q‖ * ‖a - q‖⁻¹ := by
          apply mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hnorma.le)
        _ = 1 := mul_inv_cancel₀ hnorma.ne'
    · module
  exact (EuclideanGeometry.angle_nonneg a q b).lt_of_ne hang0.symm

private lemma crown_exists_point_segment_bound {q x y : Pt}
    (hq : q ∉ segment ℝ x y) :
    ∃ d : ℝ, 0 < d ∧ ∀ z ∈ segment ℝ x y, d ≤ dist q z := by
  exact (crown_isCompact_segment x y).exists_forall_le'
    (by fun_prop) (fun z hz => dist_pos.mpr (fun hzq => hq (hzq ▸ hz)))

private lemma crown_exists_segment_segment_bound {x y x' y' : Pt}
    (hdisj : Disjoint (segment ℝ x y) (segment ℝ x' y')) :
    ∃ d : ℝ, 0 < d ∧ ∀ z ∈ segment ℝ x y,
      ∀ z' ∈ segment ℝ x' y', d ≤ dist z z' := by
  obtain ⟨d, hd, hdle⟩ :=
    ((crown_isCompact_segment x y).prod (crown_isCompact_segment x' y')).exists_forall_le'
      ((continuous_fst.dist continuous_snd).continuousOn) (fun z hz =>
        dist_pos.mpr (fun heq => Set.disjoint_left.mp hdisj hz.1 (by
          simpa [heq] using hz.2)))
  exact ⟨d, hd, fun z hz z' hz' => hdle (z, z') ⟨hz, hz'⟩⟩

private noncomputable def crownPointSegmentBound (q x y : Pt) : ℝ :=
  by
    classical
    exact if h : q ∉ segment ℝ x y then
      Classical.choose (crown_exists_point_segment_bound h)
    else 1

private lemma crownPointSegmentBound_pos (q x y : Pt) :
    0 < crownPointSegmentBound q x y := by
  classical
  by_cases h : q ∉ segment ℝ x y
  · simpa [crownPointSegmentBound, h] using
      (Classical.choose_spec (crown_exists_point_segment_bound h)).1
  · simp [crownPointSegmentBound, h]

private lemma crownPointSegmentBound_le {q x y z : Pt}
    (hq : q ∉ segment ℝ x y) (hz : z ∈ segment ℝ x y) :
    crownPointSegmentBound q x y ≤ dist q z := by
  classical
  simpa [crownPointSegmentBound, hq] using
    (Classical.choose_spec (crown_exists_point_segment_bound hq)).2 z hz

private noncomputable def crownSegmentSegmentBound (x y x' y' : Pt) : ℝ :=
  by
    classical
    exact if h : Disjoint (segment ℝ x y) (segment ℝ x' y') then
      Classical.choose (crown_exists_segment_segment_bound h)
    else 1

private lemma crownSegmentSegmentBound_pos (x y x' y' : Pt) :
    0 < crownSegmentSegmentBound x y x' y' := by
  classical
  by_cases h : Disjoint (segment ℝ x y) (segment ℝ x' y')
  · simpa [crownSegmentSegmentBound, h] using
      (Classical.choose_spec (crown_exists_segment_segment_bound h)).1
  · simp [crownSegmentSegmentBound, h]

private lemma crownSegmentSegmentBound_le {x y x' y' z z' : Pt}
    (h : Disjoint (segment ℝ x y) (segment ℝ x' y'))
    (hz : z ∈ segment ℝ x y) (hz' : z' ∈ segment ℝ x' y') :
    crownSegmentSegmentBound x y x' y' ≤ dist z z' := by
  classical
  simpa [crownSegmentSegmentBound, h] using
    (Classical.choose_spec (crown_exists_segment_segment_bound h)).2 z hz z' hz'

private noncomputable def crownReflexAngleBound
    (D : PolygonalDisk) (q a b : Pt) : ℝ :=
  by
    classical
    exact if D.IsReflexCorner q a b then
      min (Real.pi / 2) (EuclideanGeometry.angle a q b)
    else Real.pi / 2

private lemma crownReflexAngleBound_pos (D : PolygonalDisk) (q a b : Pt) :
    0 < crownReflexAngleBound D q a b := by
  classical
  by_cases h : D.IsReflexCorner q a b
  · simp only [crownReflexAngleBound, h, ↓reduceIte]
    exact lt_min (by linarith [Real.pi_pos]) (crown_reflex_angle_pos D h)
  · simp [crownReflexAngleBound, h, Real.pi_pos]

private lemma crownReflexAngleBound_le_half_pi (D : PolygonalDisk) (q a b : Pt) :
    crownReflexAngleBound D q a b ≤ Real.pi / 2 := by
  classical
  by_cases h : D.IsReflexCorner q a b
  · simp [crownReflexAngleBound, h]
  · simp [crownReflexAngleBound, h]

private lemma crownReflexAngleBound_le {D : PolygonalDisk} {q a b : Pt}
    (h : D.IsReflexCorner q a b) :
    crownReflexAngleBound D q a b ≤ EuclideanGeometry.angle a q b := by
  classical
  simp [crownReflexAngleBound, h]

private lemma crown_incident_indices_eq {D : PolygonalDisk}
    {k i j l : Fin D.n} (hi : k = i ∨ k = finRotate D.n i)
    (hj : k = j ∨ k = finRotate D.n j)
    (hl : k = l ∨ k = finRotate D.n l) (hij : i ≠ j) (hil : i ≠ l) :
    j = l := by
  rcases hi with hi | hi
  · rcases hj with hj | hj
    · exact (hij (hi.symm.trans hj)).elim
    · rcases hl with hl | hl
      · exact (hil (hi.symm.trans hl)).elim
      · exact (finRotate D.n).injective (hj.symm.trans hl)
  · rcases hj with hj | hj
    · rcases hl with hl | hl
      · exact hj.symm.trans hl
      · exact (hil ((finRotate D.n).injective (hi.symm.trans hl))).elim
    · exact (hij ((finRotate D.n).injective (hi.symm.trans hj))).elim

private lemma crown_collinear_of_shared_side {D : PolygonalDisk}
    {x y x' y' z u v : Pt} {i : Fin D.n}
    (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (hzxy : z ∈ openSegment ℝ x y)
    (hzx'y' : z ∈ openSegment ℝ x' y')
    (hu : u ∈ openSegment ℝ z x) (hv : v ∈ openSegment ℝ z x')
    (hzi : z ∈ D.side i) (hui : u ∈ D.side i) (hvi : v ∈ D.side i) :
    x' ∈ line[ℝ, x, y] ∧ y' ∈ line[ℝ, x, y] := by
  let L := line[ℝ, D.vertex i, D.vertex (finRotate D.n i)]
  have hmem : ∀ {w : Pt}, w ∈ D.side i → w ∈ L := by
    intro w hw
    exact (mem_segment_iff_wbtw.mp hw).mem_affineSpan
  have hzL := hmem hzi
  have huL := hmem hui
  have hvL := hmem hvi
  have hbase := crown_sbtw_of_mem_openSegment hxy hzxy
  have hzx : z ≠ x := hbase.ne_left
  have hzu : z ≠ u := (crown_sbtw_of_mem_openSegment hzx hu).left_ne
  have hbase' := crown_sbtw_of_mem_openSegment hx'y' hzx'y'
  have hzxp : z ≠ x' := hbase'.ne_left
  have hzv : z ≠ v := (crown_sbtw_of_mem_openSegment hzxp hv).left_ne
  have hxL : x ∈ L :=
    (affineSpan_pair_le_of_mem_of_mem hzL huL)
      ((crown_sbtw_of_mem_openSegment hzx hu).wbtw.right_mem_affineSpan_of_left_ne hzu)
  have hyL : y ∈ L :=
    (affineSpan_pair_le_of_mem_of_mem hxL hzL)
      (hbase.wbtw.right_mem_affineSpan_of_left_ne hbase.left_ne)
  have hx'L : x' ∈ L :=
    (affineSpan_pair_le_of_mem_of_mem hzL hvL)
      ((crown_sbtw_of_mem_openSegment hzxp hv).wbtw.right_mem_affineSpan_of_left_ne hzv)
  have hy'L : y' ∈ L :=
    (affineSpan_pair_le_of_mem_of_mem hx'L hzL)
      (hbase'.wbtw.right_mem_affineSpan_of_left_ne hbase'.left_ne)
  have hline : line[ℝ, x, y] = L :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hxL hyL hxy
  have hx'line : x' ∈ line[ℝ, x, y] := hline.symm ▸ hx'L
  have hy'line : y' ∈ line[ℝ, x, y] := hline.symm ▸ hy'L
  exact ⟨hx'line, hy'line⟩

private lemma crown_interval_endpoint {r u s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hsru : s ∈ uIcc r u) :
    r ∈ Icc (0 : ℝ) 1 ∨ u ∈ Icc (0 : ℝ) 1 ∨
      0 ∈ uIcc r u ∨ 1 ∈ uIcc r u := by
  by_cases hr : r ∈ Icc (0 : ℝ) 1
  · exact Or.inl hr
  by_cases hu : u ∈ Icc (0 : ℝ) 1
  · exact Or.inr (Or.inl hu)
  have hr' : r < 0 ∨ 1 < r := by
    simp only [mem_Icc, not_and_or, not_le] at hr
    rcases hr with hr | hr
    · exact Or.inl hr
    · exact Or.inr hr
  have hu' : u < 0 ∨ 1 < u := by
    simp only [mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · exact Or.inl hu
    · exact Or.inr hu
  rw [mem_uIcc] at hsru
  rcases hr' with hr' | hr' <;> rcases hu' with hu' | hu'
  · rcases hsru with hsru | hsru <;> linarith
  · exact Or.inr (Or.inr (Or.inl (mem_uIcc_of_le hr'.le (by linarith))))
  · exact Or.inr (Or.inr (Or.inl (mem_uIcc_of_ge hu'.le (by linarith))))
  · rcases hsru with hsru | hsru <;> linarith

private lemma crown_endpoint_mem_of_collinear_intersection {x y x' y' z : Pt}
    (hxy : x ≠ y) (hzxy : z ∈ openSegment ℝ x y)
    (hzx'y' : z ∈ openSegment ℝ x' y')
    (hx'line : x' ∈ line[ℝ, x, y]) (hy'line : y' ∈ line[ℝ, x, y]) :
    x' ∈ segment ℝ x y ∨ y' ∈ segment ℝ x y ∨
      x ∈ segment ℝ x' y' ∨ y ∈ segment ℝ x' y' := by
  obtain ⟨s, hs0, hs1, hzs⟩ := crown_mem_openSegment_iff.mp hzxy
  obtain ⟨t, ht0, ht1, hzt⟩ := crown_mem_openSegment_iff.mp hzx'y'
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx'line
  obtain ⟨u, hu⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy'line
  have hxr : x' = x + r • (y - x) := by
    simpa [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] using hr.symm
  have hyu : y' = x + u • (y - x) := by
    simpa [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] using hu.symm
  have hcoef : s = r + t * (u - r) := by
    rw [hzs, hxr, hyu] at hzt
    apply crown_smul_cancel (sub_ne_zero.mpr hxy.symm)
    calc
      s • (y - x) = (x + s • (y - x)) - x := by module
      _ = (x + r • (y - x) +
          t • (x + u • (y - x) - (x + r • (y - x)))) - x := by rw [hzt]
      _ = (r + t * (u - r)) • (y - x) := by module
  have hsru : s ∈ uIcc r u := by
    rw [← segment_eq_uIcc, mem_segment_iff_wbtw]
    refine ⟨t, ⟨ht0.le, ht1.le⟩, ?_⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub]
    change t * (u - r) + r = s
    rw [hcoef]
    ring
  have hmap : ∀ {a : ℝ}, a ∈ segment ℝ r u →
      x + a • (y - x) ∈ segment ℝ x' y' := by
    intro a ha
    obtain ⟨c, hc, hca⟩ := mem_segment_iff_wbtw.mp ha
    apply crown_mem_segment_iff.mpr
    refine ⟨c, hc.1, hc.2, ?_⟩
    have hac : a = r + c * (u - r) := by
      simpa [AffineMap.lineMap_apply, vsub_eq_sub, add_comm] using hca.symm
    rw [hxr, hyu, hac]
    module
  rcases crown_interval_endpoint hs0 hs1 hsru with hr | hu | h0 | h1
  · left
    exact crown_mem_segment_iff.mpr ⟨r, hr.1, hr.2, hxr⟩
  · right; left
    exact crown_mem_segment_iff.mpr ⟨u, hu.1, hu.2, hyu⟩
  · right; right; left
    convert hmap (segment_eq_uIcc r u ▸ h0) using 1
    module
  · right; right; right
    convert hmap (segment_eq_uIcc r u ▸ h1) using 1
    module

private lemma crown_geometricEdges_disjoint (D : PolygonalDisk)
    {x y x' y' : Pt} (hxy : D.IsGeometricEdge x y)
    (hx'y' : D.IsGeometricEdge x' y')
    (hend : Disjoint ({x, y} : Set Pt) {x', y'}) :
    Disjoint (segment ℝ x y) (segment ℝ x' y') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  have hends : x ≠ x' ∧ x ≠ y' ∧ y ≠ x' ∧ y ≠ y' := by
    simpa [Set.disjoint_left, and_assoc] using hend
  have hzx : z ≠ x := by
    intro h
    subst z
    exact (crown_genuineCorner_not_mem_geometricEdge D hxy.1 hx'y'
      hends.1 hends.2.1) hz'
  have hzy : z ≠ y := by
    intro h
    subst z
    exact (crown_genuineCorner_not_mem_geometricEdge D hxy.2.1 hx'y'
      hends.2.2.1 hends.2.2.2) hz'
  have hzx' : z ≠ x' := by
    intro h
    subst z
    exact (crown_genuineCorner_not_mem_geometricEdge D hx'y'.1 hxy
      (Ne.symm hends.1) (Ne.symm hends.2.2.1)) hz
  have hzy' : z ≠ y' := by
    intro h
    subst z
    exact (crown_genuineCorner_not_mem_geometricEdge D hx'y'.2.1 hxy
      (Ne.symm hends.2.1) (Ne.symm hends.2.2.2)) hz
  have hzopen : z ∈ openSegment ℝ x y :=
    mem_openSegment_of_ne_left_right (Ne.symm hzx) (Ne.symm hzy) hz
  have hzopen' : z ∈ openSegment ℝ x' y' :=
    mem_openSegment_of_ne_left_right (Ne.symm hzx') (Ne.symm hzy') hz'
  obtain ⟨r, hr, hboundary⟩ := crown_local_boundary D (v := z)
  obtain ⟨u, hur, hu⟩ := crown_exists_near_openSegment hzx hr
  obtain ⟨u', hu'r, hu'⟩ := crown_exists_near_openSegment hzy hr
  obtain ⟨v, hvr, hv⟩ := crown_exists_near_openSegment hzx' hr
  have huz : u ≠ z := (crown_sbtw_of_mem_openSegment hzx hu).ne_left
  have hu'z : u' ≠ z := (crown_sbtw_of_mem_openSegment hzy hu').ne_left
  have hvz : v ≠ z := (crown_sbtw_of_mem_openSegment hzx' hv).ne_left
  have huEdge : u ∈ segment ℝ x y :=
    (convex_segment x y).segment_subset hz (left_mem_segment ℝ x y)
      (openSegment_subset_segment ℝ _ _ hu)
  have hu'Edge : u' ∈ segment ℝ x y :=
    (convex_segment x y).segment_subset hz (right_mem_segment ℝ x y)
      (openSegment_subset_segment ℝ _ _ hu')
  have hvEdge : v ∈ segment ℝ x' y' :=
    (convex_segment x' y').segment_subset hz' (left_mem_segment ℝ x' y')
      (openSegment_subset_segment ℝ _ _ hv)
  obtain ⟨i, hzi, hui, -⟩ := hboundary u hur (hxy.2.2.2 huEdge)
  obtain ⟨i', hzi', hu'i', -⟩ := hboundary u' hu'r (hxy.2.2.2 hu'Edge)
  obtain ⟨j, hzj, hvj, -⟩ := hboundary v hvr (hx'y'.2.2.2 hvEdge)
  have hlines : x' ∈ line[ℝ, x, y] ∧ y' ∈ line[ℝ, x, y] := by
    by_cases hij : i = j
    · subst j
      exact crown_collinear_of_shared_side hxy.2.2.1 hx'y'.2.2.1
        hzopen hzopen' hu hv hzi hui hvj
    · have hs := D.simple i j hij ⟨hzi, hzj⟩
      obtain ⟨k, hzk⟩ : ∃ k : Fin D.n, z = D.vertex k := by
        rcases hs.1 with hs | hs
        · exact ⟨i, hs⟩
        · exact ⟨finRotate D.n i, hs⟩
      subst z
      have hi := crown_side_through_vertex D k i hzi
      have hi' := crown_side_through_vertex D k i' hzi'
      have hj := crown_side_through_vertex D k j hzj
      have hii' : i ≠ i' := by
        intro heq
        subst i'
        have hzero := crown_angle_eq_zero_of_mem_side
          (D := D) (i := i) (q := D.vertex k) (z := u) (z' := u')
          (hi.elim (fun h => Or.inl (congrArg D.vertex h))
            (fun h => Or.inr (congrArg D.vertex h))) hui hu'i' huz hu'z
        have hxu : Sbtw ℝ x u (D.vertex k) := by
          rw [sbtw_comm]
          exact crown_sbtw_of_mem_openSegment hzx hu
        have hzu'y : Sbtw ℝ (D.vertex k) u' y :=
          crown_sbtw_of_mem_openSegment hzy hu'
        have huzu' : Sbtw ℝ u (D.vertex k) u' :=
          ((crown_sbtw_of_mem_openSegment hxy.2.2.1 hzopen).trans_left_right hxu).trans_right_left hzu'y
        linarith [huzu'.angle₁₂₃_eq_pi, Real.pi_pos]
      have hi'j : i' = j := crown_incident_indices_eq hi hi' hj hii' hij
      subst j
      have hline := crown_collinear_of_shared_side hxy.2.2.1.symm hx'y'.2.2.1
        (by rwa [openSegment_symm]) hzopen' hu' hv hzi' hu'i' hvj
      simpa [Set.pair_comm] using hline
  rcases crown_endpoint_mem_of_collinear_intersection hxy.2.2.1 hzopen hzopen'
      hlines.1 hlines.2 with h | h | h | h
  · exact (crown_genuineCorner_not_mem_geometricEdge D hx'y'.1 hxy
      (Ne.symm hends.1) (Ne.symm hends.2.2.1)) h
  · exact (crown_genuineCorner_not_mem_geometricEdge D hx'y'.2.1 hxy
      (Ne.symm hends.2.1) (Ne.symm hends.2.2.2)) h
  · exact (crown_genuineCorner_not_mem_geometricEdge D hxy.1 hx'y'
      hends.1 hends.2.1) h
  · exact (crown_genuineCorner_not_mem_geometricEdge D hxy.2.1 hx'y'
      hends.2.2.1 hends.2.2.2) h

private lemma crown_finset_min_pos {s : Finset ℝ} (hs : s.Nonempty)
    (hpos : ∀ a ∈ s, 0 < a) :
    0 < s.min' hs := hpos _ (Finset.min'_mem s hs)

/-- Positive root separation constants exist (finite minima of distances
between disjoint compact sets; `1` for empty collections). -/
theorem exists_rootSeparation (P : Protoset) : Nonempty (RootSeparation P) := by
  classical
  let Iν := Σ p : P.Form,
    Fin (P.disk p).n × Fin (P.disk p).n × Fin (P.disk p).n
  let fν : Iν → ℝ := fun i => crownPointSegmentBound
    ((P.disk i.1).vertex i.2.1)
    ((P.disk i.1).vertex i.2.2.1) ((P.disk i.1).vertex i.2.2.2)
  let sν : Finset ℝ := insert 1 (Finset.univ.image fν)
  have hsν : sν.Nonempty := by simp [sν]
  let ν := sν.min' hsν
  have hνpos : 0 < ν := by
    apply crown_finset_min_pos hsν
    intro a ha
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · norm_num
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
      exact crownPointSegmentBound_pos _ _ _
  let Ilam := Σ p : P.Form,
    Fin (P.disk p).n × Fin (P.disk p).n ×
      Fin (P.disk p).n × Fin (P.disk p).n
  let flam : Ilam → ℝ := fun i => crownSegmentSegmentBound
    ((P.disk i.1).vertex i.2.1)
    ((P.disk i.1).vertex i.2.2.1)
    ((P.disk i.1).vertex i.2.2.2.1) ((P.disk i.1).vertex i.2.2.2.2)
  let slam : Finset ℝ := insert 1 (Finset.univ.image flam)
  have hslam : slam.Nonempty := by simp [slam]
  let lam := slam.min' hslam
  have hlampos : 0 < lam := by
    apply crown_finset_min_pos hslam
    intro a ha
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · norm_num
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
      exact crownSegmentSegmentBound_pos _ _ _ _
  let Iμ := Σ p : P.Form,
    Fin (P.disk p).n × Fin (P.disk p).n × Fin (P.disk p).n
  let fμ : Iμ → ℝ := fun i => crownReflexAngleBound (P.disk i.1)
    ((P.disk i.1).vertex i.2.1)
    ((P.disk i.1).vertex i.2.2.1) ((P.disk i.1).vertex i.2.2.2)
  let sμ : Finset ℝ := insert (Real.pi / 2) (Finset.univ.image fμ)
  have hsμ : sμ.Nonempty := by simp [sμ]
  let μ := sμ.min' hsμ
  have hμpos : 0 < μ := by
    apply crown_finset_min_pos hsμ
    intro a ha
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · linarith [Real.pi_pos]
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
      exact crownReflexAngleBound_pos _ _ _ _
  refine ⟨{
    ν := ν
    lam := lam
    μ := μ
    ν_pos := hνpos
    lam_pos := hlampos
    μ_pos := hμpos
    μ_le := ?_
    ν_le := ?_
    lam_le := ?_
    μ_le_reflex := ?_ }⟩
  · exact Finset.min'_le sμ (Real.pi / 2) (by simp [sμ])
  · intro p q x y hq hxy hqx hqy z hz
    obtain ⟨qi, hqi, rfl⟩ := hq
    obtain ⟨xi, hxi, rfl⟩ := hxy.1
    obtain ⟨yi, hyi, rfl⟩ := hxy.2.1
    let i : Iν := ⟨p, qi, xi, yi⟩
    calc
      ν ≤ fν i := Finset.min'_le sν (fν i) (by
        apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      _ = crownPointSegmentBound ((P.disk p).vertex qi)
          ((P.disk p).vertex xi) ((P.disk p).vertex yi) := rfl
      _ ≤ dist ((P.disk p).vertex qi) z := crownPointSegmentBound_le
        (crown_genuineCorner_not_mem_geometricEdge (P.disk p)
          ⟨qi, hqi, rfl⟩
          ⟨⟨xi, hxi, rfl⟩, ⟨yi, hyi, rfl⟩, hxy.2.2⟩ hqx hqy) hz
  · intro p x y x' y' hxy hx'y' hend z hz z' hz'
    obtain ⟨xi, hxi, rfl⟩ := hxy.1
    obtain ⟨yi, hyi, rfl⟩ := hxy.2.1
    obtain ⟨xi', hxi', rfl⟩ := hx'y'.1
    obtain ⟨yi', hyi', rfl⟩ := hx'y'.2.1
    let i : Ilam := ⟨p, xi, yi, xi', yi'⟩
    apply le_trans (Finset.min'_le slam (flam i) (by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    apply crownSegmentSegmentBound_le
      (crown_geometricEdges_disjoint (P.disk p) hxy hx'y' hend) hz hz'
  · intro p q a b h
    obtain ⟨qi, hqi, rfl⟩ := h.1.1
    obtain ⟨ai, hai, rfl⟩ := h.1.2.1
    obtain ⟨bi, hbi, rfl⟩ := h.2.1.2.1
    let i : Iμ := ⟨p, qi, ai, bi⟩
    apply le_trans (Finset.min'_le sμ (fμ i) (by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    exact crownReflexAngleBound_le h

/-- `def:crown-separation`: a fixed choice of root separation constants. -/
def rootSeparationConstants (P : Protoset) : RootSeparation P :=
  Classical.choice (exists_rootSeparation P)

/-! ## `lem:ray-bound` -/

/-- Step 1 of the blueprint proof of `distanceToReflexBoundaryRay_step1_infDist_eq`:
translation invariance of infDist. -/
private lemma distanceToReflexBoundaryRay_step1_infDist_eq_step1_trans (q a b : Pt) (t : ℝ) :
    infDist (q + t • a) ((fun s : ℝ => q + s • b) '' Ici 0) =
      infDist (t • a) ((fun s : ℝ => s • b) '' Ici 0) := by
  have hIsom : Isometry (fun (x : Pt) => x + q) := IsometryEquiv.addRight q |>.isometry
  have hImg : (fun s : ℝ => q + s • b) '' Ici 0 = (fun (x : Pt) => x + q) '' ((fun s : ℝ => s • b) '' Ici 0) := by
    ext x
    simp only [mem_image]
    constructor
    · rintro ⟨s, hs, rfl⟩
      use s • b
      refine ⟨⟨s, hs, rfl⟩, ?_⟩
      abel
    · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
      use s
      refine ⟨hs, ?_⟩
      abel
  rw [hImg]
  have hEq : q + t • a = (fun (x : Pt) => x + q) (t • a) := by abel
  rw [hEq]
  exact infDist_image hIsom

/-- Step 2 of the blueprint proof of `distanceToReflexBoundaryRay_step1_infDist_eq`:
infDist equals sInf of distances. -/
private lemma distanceToReflexBoundaryRay_step1_infDist_eq_step2_sInf (a b : Pt) (t : ℝ) :
    infDist (t • a) ((fun s : ℝ => s • b) '' Ici 0) =
      sInf ((fun s : ℝ => ‖t • a - s • b‖) '' Ici 0) := by
  have hne : ((fun s : ℝ => s • b) '' Ici 0).Nonempty :=
    (nonempty_Ici : (Ici (0 : ℝ)).Nonempty).image _
  have hdne :
      ((fun y : Pt => dist (t • a) y) '' ((fun s : ℝ => s • b) '' Ici 0)).Nonempty :=
    hne.image _
  have hglb := Metric.isGLB_infDist (x := t • a) hne
  have hset :
      (fun y : Pt => dist (t • a) y) '' ((fun s : ℝ => s • b) '' Ici 0) =
        (fun s : ℝ => ‖t • a - s • b‖) '' Ici 0 := by
    ext x
    simp only [mem_image]
    constructor
    · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s, hs, by rw [dist_eq_norm]⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s • b, ⟨s, hs, rfl⟩, by rw [dist_eq_norm]⟩
  rw [← hset]
  exact (hglb.csInf_eq hdne).symm

/-- Step 1 of the blueprint proof of `distanceToReflexBoundaryRay`: 
reduce to `sInf` of `‖t a - s b‖`. -/
private lemma distanceToReflexBoundaryRay_step1_infDist_eq (q a b : Pt) (t : ℝ) :
    infDist (q + t • a) ((fun s : ℝ => q + s • b) '' Ici 0) =
      sInf ((fun s : ℝ => ‖t • a - s • b‖) '' Ici 0) := by
  rw [distanceToReflexBoundaryRay_step1_infDist_eq_step1_trans q a b t]
  rw [distanceToReflexBoundaryRay_step1_infDist_eq_step2_sInf a b t]

/-- Step 1 of the blueprint proof of `distanceToReflexBoundaryRay_step2_min_quad_step1_acute`: 
lower bound for the distance. -/
private lemma distanceToReflexBoundaryRay_step2_min_quad_step1_acute_step1_lower (a b : Pt)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {t : ℝ} (ht : 0 < t)
    (h_ang : InnerProductGeometry.angle a b ≤ Real.pi / 2) :
    ∀ s : ℝ, t * Real.sin (InnerProductGeometry.angle a b) ≤ ‖t • a - s • b‖ := by
  intro s
  have hθle : InnerProductGeometry.angle a b ≤ Real.pi :=
    le_trans h_ang (by linarith [Real.pi_pos])
  have hsin : 0 ≤ Real.sin (InnerProductGeometry.angle a b) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (InnerProductGeometry.angle_nonneg a b) hθle
  have hinner : inner ℝ a b = Real.cos (InnerProductGeometry.angle a b) := by
    simpa [ha, hb] using
      (InnerProductGeometry.cos_angle_mul_norm_mul_norm a b).symm
  have hsq := norm_sub_sq_real (t • a) (s • b)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le, ha, hb,
    inner_smul_left, inner_smul_right, hinner, Real.norm_eq_abs] at hsq
  simp at hsq
  have hkey : (t * Real.sin (InnerProductGeometry.angle a b)) ^ 2 ≤
      ‖t • a - s • b‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (s - t * Real.cos (InnerProductGeometry.angle a b)),
      Real.sin_sq_add_cos_sq (InnerProductGeometry.angle a b)]
  exact (pow_le_pow_iff_left₀ (mul_nonneg ht.le hsin) (norm_nonneg _) two_ne_zero).mp hkey

/-- Step 2 of the blueprint proof of `distanceToReflexBoundaryRay_step2_min_quad_step1_acute`: 
the minimum is attained. -/
private lemma distanceToReflexBoundaryRay_step2_min_quad_step1_acute_step2_eq (a b : Pt)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {t : ℝ} (ht : 0 < t)
    (h_ang : InnerProductGeometry.angle a b ≤ Real.pi / 2) :
    ‖t • a - (t * Real.cos (InnerProductGeometry.angle a b)) • b‖ =
      t * Real.sin (InnerProductGeometry.angle a b) := by
  set θ := InnerProductGeometry.angle a b
  have hθ0 : 0 ≤ θ := InnerProductGeometry.angle_nonneg a b
  have hθpi : θ ≤ Real.pi := InnerProductGeometry.angle_le_pi a b
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by
    linarith [Real.pi_pos], h_ang⟩
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθpi
  have hinner : inner ℝ a b = Real.cos θ := by
    simpa [ha, hb] using
      (InnerProductGeometry.cos_angle_mul_norm_mul_norm a b).symm
  have hsq := norm_sub_sq_real (t • a) ((t * Real.cos θ) • b)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le,
    Real.norm_of_nonneg (mul_nonneg ht.le hcos), inner_smul_left,
    inner_smul_right, hinner, ha, hb] at hsq
  simp at hsq
  have hsq' : ‖t • a - (t * Real.cos θ) • b‖ ^ 2 = (t * Real.sin θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hnorm : 0 ≤ ‖t • a - (t * Real.cos θ) • b‖ := norm_nonneg _
  have hright : 0 ≤ t * Real.sin θ := mul_nonneg ht.le hsin
  nlinarith

/-- Step 3 of the blueprint proof of `distanceToReflexBoundaryRay_step2_min_quad_step1_acute`: 
the attained point is nonnegative. -/
private lemma distanceToReflexBoundaryRay_step2_min_quad_step1_acute_step3_nonneg (a b : Pt)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {t : ℝ} (ht : 0 < t)
    (h_ang : InnerProductGeometry.angle a b ≤ Real.pi / 2) :
    0 ≤ t * Real.cos (InnerProductGeometry.angle a b) := by
  have _ := ha
  have _ := hb
  have hcos : 0 ≤ Real.cos (InnerProductGeometry.angle a b) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [InnerProductGeometry.angle_nonneg a b]) h_ang
  exact mul_nonneg ht.le hcos

/-- Step 1 of the blueprint proof of `distanceToReflexBoundaryRay_step2_min_quad`: the acute case. -/
private lemma distanceToReflexBoundaryRay_step2_min_quad_step1_acute (a b : Pt) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) {t : ℝ} (ht : 0 < t) (h_ang : InnerProductGeometry.angle a b ≤ Real.pi / 2) :
    sInf ((fun s : ℝ => ‖t • a - s • b‖) '' Ici 0) =
      t * Real.sin (InnerProductGeometry.angle a b) := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨t * Real.sin (InnerProductGeometry.angle a b), by
      use t * Real.cos (InnerProductGeometry.angle a b)
      constructor
      · exact distanceToReflexBoundaryRay_step2_min_quad_step1_acute_step3_nonneg a b ha hb ht h_ang
      · exact distanceToReflexBoundaryRay_step2_min_quad_step1_acute_step2_eq a b ha hb ht h_ang⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact distanceToReflexBoundaryRay_step2_min_quad_step1_acute_step1_lower a b ha hb ht h_ang s
  · intro w hw
    use t * Real.sin (InnerProductGeometry.angle a b)
    constructor
    · use t * Real.cos (InnerProductGeometry.angle a b)
      have h1 := distanceToReflexBoundaryRay_step2_min_quad_step1_acute_step3_nonneg
        a b ha hb ht h_ang
      have h2 := distanceToReflexBoundaryRay_step2_min_quad_step1_acute_step2_eq
        a b ha hb ht h_ang
      exact ⟨h1, h2⟩
    · exact hw

/-- Step 2 of the blueprint proof of `distanceToReflexBoundaryRay_step2_min_quad`: the obtuse case. -/
private lemma distanceToReflexBoundaryRay_step2_min_quad_step2_obtuse (a b : Pt) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) {t : ℝ} (ht : 0 < t) (h_ang : ¬ (InnerProductGeometry.angle a b ≤ Real.pi / 2)) :
    sInf ((fun s : ℝ => ‖t • a - s • b‖) '' Ici 0) = t := by
  have hθ : Real.pi / 2 < InnerProductGeometry.angle a b := lt_of_not_ge h_ang
  have hcos : Real.cos (InnerProductGeometry.angle a b) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hθ
      (by linarith [InnerProductGeometry.angle_le_pi a b, Real.pi_pos])
  have hinner : inner ℝ a b = Real.cos (InnerProductGeometry.angle a b) := by
    simpa [ha, hb] using
      (InnerProductGeometry.cos_angle_mul_norm_mul_norm a b).symm
  apply le_antisymm
  · refine csInf_le (by
      refine ⟨0, ?_⟩
      rintro y ⟨s, hs, rfl⟩
      exact norm_nonneg _) ⟨0, by simp, ?_⟩
    change ‖t • a - 0 • b‖ = t
    rw [zero_smul, sub_zero, norm_smul, Real.norm_of_nonneg ht.le, ha]
    ring
  · refine le_csInf ?_ ?_
    · exact ⟨t, by
        refine ⟨0, by simp, ?_⟩
        change ‖t • a - 0 • b‖ = t
        rw [zero_smul, sub_zero, norm_smul, Real.norm_of_nonneg ht.le, ha]
        ring⟩
    · rintro y ⟨s, hs, rfl⟩
      have hsq := norm_sub_sq_real (t • a) (s • b)
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le,
        Real.norm_of_nonneg hs, inner_smul_left, inner_smul_right,
        hinner, ha, hb] at hsq
      simp at hsq
      have hnonneg : 0 ≤ ‖t • a - s • b‖ := norm_nonneg _
      have hs0 : 0 ≤ s := hs
      have hprod : t * (s * Real.cos (InnerProductGeometry.angle a b)) ≤ 0 := by
        rw [← mul_assoc]
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ht.le hs0) hcos.le
      nlinarith

/-- Step 2 of the blueprint proof of `distanceToReflexBoundaryRay`: minimize the quadratic form. -/
private lemma distanceToReflexBoundaryRay_step2_min_quad (a b : Pt) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) {t : ℝ} (ht : 0 < t) :
    sInf ((fun s : ℝ => ‖t • a - s • b‖) '' Ici 0) =
      if InnerProductGeometry.angle a b ≤ Real.pi / 2 then
        t * Real.sin (InnerProductGeometry.angle a b)
      else t := by
  have H : (fun s : ℝ => ‖t • a - s • b‖) '' Ici 0 = (fun s : ℝ => ‖t • a - s • b‖) '' Ici (0:ℝ) := rfl
  rw [H]
  split_ifs with h
  · have H1 : (fun s : ℝ => ‖t • a - s • b‖) '' Ici (0:ℝ) = (fun s : ℝ => ‖t • a - s • b‖) '' Ici 0 := rfl
    rw [H1]
    exact distanceToReflexBoundaryRay_step2_min_quad_step1_acute a b ha hb ht h
  · have H2 : (fun s : ℝ => ‖t • a - s • b‖) '' Ici (0:ℝ) = (fun s : ℝ => ‖t • a - s • b‖) '' Ici 0 := rfl
    rw [H2]
    exact distanceToReflexBoundaryRay_step2_min_quad_step2_obtuse a b ha hb ht h

/-- `lem:ray-bound`: for unit vectors `a, b` and `t > 0`, the distance from
`q + t a` to the ray `q + ℝ_{≥0} b` is `t sin β` if `β = ∠(a, b) ≤ π/2` and
`t` otherwise. -/
theorem distanceToReflexBoundaryRay (q a b : Pt) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {t : ℝ} (ht : 0 < t) :
    infDist (q + t • a) ((fun s : ℝ => q + s • b) '' Ici 0) =
      if InnerProductGeometry.angle a b ≤ Real.pi / 2 then
        t * Real.sin (InnerProductGeometry.angle a b)
      else t := by
  rw [distanceToReflexBoundaryRay_step1_infDist_eq q a b t]
  rw [distanceToReflexBoundaryRay_step2_min_quad a b ha hb ht]

/-- `lem:ray-bound`, the form used later: if `0 < μ ≤ π/2` and `μ ≤ β`, the
distance is at least `t sin μ`. -/
theorem distanceToReflexBoundaryRay_ge (q a b : Pt) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {t μ : ℝ} (ht : 0 < t) (hμ0 : 0 < μ) (hμ : μ ≤ Real.pi / 2)
    (hβ : μ ≤ InnerProductGeometry.angle a b) :
    t * Real.sin μ ≤ infDist (q + t • a) ((fun s : ℝ => q + s • b) '' Ici 0) := by
  rw [distanceToReflexBoundaryRay q a b ha hb ht]
  split_ifs with h
  · gcongr
    apply Real.strictMonoOn_sin.monotoneOn
    · exact ⟨by have := Real.pi_pos; linarith, hμ⟩
    · exact ⟨by have := Real.pi_pos; linarith, h⟩
    · exact hβ
  · have h1 : Real.sin μ ≤ 1 := Real.sin_le_one μ
    calc
      t * Real.sin μ ≤ t * 1 := by gcongr
      _ = t := mul_one t

/-! ## `lem:relative-crown-ball` -/

/-- The radius `d = ½ min {r_*, ν, λ, h sin μ_*}` with `h = min r_* δ_*`. -/
def crownRadius (r δ : ℝ) (R : RootSeparation P) : ℝ :=
  (1 / 2) * min (min r R.ν) (min R.lam (min r δ * Real.sin R.μ))

private lemma rcb_mem_seg_line {e d : Pt} {α β s : ℝ} (h : s ∈ segment ℝ α β) :
    e + s • d ∈ segment ℝ (e + α • d) (e + β • d) := by
  rw [segment_eq_image'] at h ⊢
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨t, ht, by simp only [smul_eq_mul]; module⟩

private lemma rcb_side_line {u w e d : Pt} {ε : ℝ} (hε : 0 < ε) (hd : d ≠ 0)
    (he : e ∈ segment ℝ u w) (hed : e - ε • d ∈ segment ℝ u w) :
    ∃ α β : ℝ, u = e + α • d ∧ w = e + β • d ∧ (0 : ℝ) ∈ segment ℝ α β ∧
      -ε ∈ segment ℝ α β := by
  rw [segment_eq_image'] at he hed
  obtain ⟨l1, ⟨hl10, hl11⟩, h1⟩ := he
  obtain ⟨l2, ⟨hl20, hl21⟩, h2⟩ := hed
  have hsub : (l1 - l2) • (w - u) = ε • d := by
    simp only at h1 h2
    rw [sub_smul]
    have : ε • d = e - (e - ε • d) := by abel
    rw [this, ← h2, ← h1]; abel
  have hl : l1 - l2 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hsub
    exact smul_ne_zero hε.ne' hd hsub.symm
  set κ := ε / (l1 - l2) with hκ
  have hwu : w - u = κ • d := by
    rw [hκ, div_eq_inv_mul, mul_smul, ← hsub, smul_smul, inv_mul_cancel₀ hl, one_smul]
  refine ⟨-(l1 * κ), (1 - l1) * κ, ?_, ?_, ?_, ?_⟩
  · rw [← h1, hwu]; module
  · have : w = u + κ • d := by rw [← hwu]; abel
    rw [← h1, hwu, this]; module
  · rw [segment_eq_image']
    exact ⟨l1, ⟨hl10, hl11⟩, by simp only [smul_eq_mul]; ring⟩
  · rw [segment_eq_image']
    refine ⟨l2, ⟨hl20, hl21⟩, ?_⟩
    rw [hκ]; simp only [smul_eq_mul]; field_simp; ring

private lemma rcb_side_subset_frontier (D : PolygonalDisk) (i : Fin D.n) :
    D.side i ⊆ frontier D.carrier := by
  rw [D.frontier_eq]
  exact subset_iUnion (fun j => D.side j) i

private lemma rcb_smul_cancel {e d : Pt} (hd : d ≠ 0) {a b : ℝ} (h : e + a • d = e + b • d) :
    a = b :=
  smul_left_injective ℝ hd (add_left_cancel h)

private lemma rcb_genuine_of_local (D : PolygonalDisk) {k : Fin D.n} {e d : Pt} (hd : d ≠ 0)
    (hk : D.vertex k = e) {γ : ℝ} (hγ : γ ≠ 0)
    (hnb : D.vertex ((finRotate D.n).symm k) = e + γ • d ∨
      D.vertex (finRotate D.n k) = e + γ • d)
    (hmax : ∀ m : ℝ, 0 < m → (∀ s ∈ Icc (0:ℝ) m, e + s • d ∈ frontier D.carrier) → False) :
    D.IsGenuineVertex k := by
  intro hcol
  set kp := (finRotate D.n).symm k with hkp
  set kn := finRotate D.n k with hkn
  have hkpk : finRotate D.n kp = k := by simp [hkp]
  have hn2 : 2 ≤ D.n := by have := D.three_le; omega
  have hkp_ne : kp ≠ k := by
    intro h
    apply crown_finRotate_ne_self hn2 kp
    rw [hkpk, h]
  have hkn_ne : kn ≠ k := crown_finRotate_ne_self hn2 k
  rw [collinear_iff_of_mem (p₀ := D.vertex k) (by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  have hline : ∀ p ∈ ({D.vertex kp, D.vertex k, D.vertex kn} : Set Pt), ∃ c : ℝ, p = e + c • d := by
    have hkn' : ∃ r1 : ℝ, r1 ≠ 0 ∧ r1 • v = γ • d := by
      rcases hnb with h | h
      · obtain ⟨r1, hr1⟩ := hv (D.vertex kp) (by simp)
        rw [h, hk, vadd_eq_add] at hr1
        refine ⟨r1, ?_, ?_⟩
        · rintro rfl
          rw [zero_smul, zero_add] at hr1
          exact smul_ne_zero hγ hd (by simpa using hr1)
        · have := congrArg (· - e) hr1
          simpa using this.symm
      · obtain ⟨r1, hr1⟩ := hv (D.vertex kn) (by simp)
        rw [h, hk, vadd_eq_add] at hr1
        refine ⟨r1, ?_, ?_⟩
        · rintro rfl
          rw [zero_smul, zero_add] at hr1
          exact smul_ne_zero hγ hd (by simpa using hr1)
        · have := congrArg (· - e) hr1
          simpa using this.symm
    obtain ⟨r1, hr1, hr1v⟩ := hkn'
    intro p hp
    obtain ⟨r2, hr2⟩ := hv p hp
    refine ⟨r2 * γ / r1, ?_⟩
    rw [hr2, hk, vadd_eq_add, add_comm]
    congr 1
    have hvv : v = (γ / r1) • d := by
      rw [div_eq_inv_mul, mul_smul, ← hr1v, smul_smul, inv_mul_cancel₀ hr1, one_smul]
    rw [hvv, smul_smul]; congr 1; ring
  obtain ⟨γp, hγp⟩ := hline (D.vertex kp) (by simp)
  obtain ⟨γn, hγn⟩ := hline (D.vertex kn) (by simp)
  have hside_p : ∀ s ∈ segment ℝ γp 0, e + s • d ∈ D.side kp := by
    intro s hs
    have := rcb_mem_seg_line (e := e) (d := d) hs
    rw [zero_smul, add_zero] at this
    change e + s • d ∈ segment ℝ (D.vertex kp) (D.vertex (finRotate D.n kp))
    rw [hkpk, hγp, hk]; exact this
  have hside_n : ∀ s ∈ segment ℝ 0 γn, e + s • d ∈ D.side k := by
    intro s hs
    have := rcb_mem_seg_line (e := e) (d := d) hs
    rw [zero_smul, add_zero] at this
    change e + s • d ∈ segment ℝ (D.vertex k) (D.vertex kn)
    rw [hγn, hk]; exact this
  have hγp0 : γp ≠ 0 := by
    rintro rfl
    apply hkp_ne; apply D.vertex_injective; rw [hγp, hk]; simp
  have hγn0 : γn ≠ 0 := by
    rintro rfl
    apply hkn_ne; apply D.vertex_injective; rw [hγn, hk]; simp
  have hγpneg : γp < 0 := by
    by_contra hpos
    push_neg at hpos
    refine hmax γp (lt_of_le_of_ne hpos (Ne.symm hγp0)) fun s hs => ?_
    apply rcb_side_subset_frontier D kp
    apply hside_p
    rw [segment_eq_uIcc, uIcc_comm]; exact Icc_subset_uIcc hs
  have hγnneg : γn < 0 := by
    by_contra hpos
    push_neg at hpos
    refine hmax γn (lt_of_le_of_ne hpos (Ne.symm hγn0)) fun s hs => ?_
    apply rcb_side_subset_frontier D k
    apply hside_n
    rw [segment_eq_uIcc]; exact Icc_subset_uIcc hs
  set ε' := min (-γp) (-γn) / 2 with hε'
  have hε'0 : 0 < ε' := by
    have := lt_min (neg_pos.mpr hγpneg) (neg_pos.mpr hγnneg)
    rw [hε']; linarith
  have hε'p : ε' < -γp := by
    have := min_le_left (-γp) (-γn); rw [hε']; linarith
  have hε'n : ε' < -γn := by
    have := min_le_right (-γp) (-γn); rw [hε']; linarith
  have hmem1 := hside_p (-ε') (by
    rw [segment_eq_uIcc, mem_uIcc]; left; constructor <;> linarith)
  have hmem2 := hside_n (-ε') (by
    rw [segment_eq_uIcc, mem_uIcc]; right; constructor <;> linarith)
  have hsimple := (D.simple kp k hkp_ne ⟨hmem1, hmem2⟩).1
  rw [hkpk] at hsimple
  rcases hsimple with h | h
  · rw [hγp] at h
    have := rcb_smul_cancel hd h
    linarith
  · rw [hk] at h
    have := rcb_smul_cancel hd (h.trans (add_zero e).symm |>.trans (by rw [zero_smul]))
    linarith

private lemma rcb_frontier_extend (D : PolygonalDisk) {x d : Pt} (hd : d ≠ 0)
    (h1 : ∀ s ∈ Icc (0:ℝ) 1, x + s • d ∈ frontier D.carrier) :
    ∃ T : ℝ, 1 ≤ T ∧ (∀ s ∈ Icc (0:ℝ) T, x + s • d ∈ frontier D.carrier) ∧
      D.IsGenuineCorner (x + T • d) := by
  set F := frontier D.carrier with hF
  set J : Set ℝ := {T | 1 ≤ T ∧ ∀ s ∈ Icc (0:ℝ) T, x + s • d ∈ F} with hJ
  have hnd : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have h1J : (1:ℝ) ∈ J := ⟨le_rfl, h1⟩
  have hbdd : BddAbove J := by
    obtain ⟨C, hC⟩ := D.compact.isBounded.exists_norm_le
    refine ⟨(C + ‖x‖) / ‖d‖, fun T hT => ?_⟩
    have hT0 : 0 ≤ T := by linarith [hT.1]
    have hm : ‖x + T • d‖ ≤ C :=
      hC _ (D.compact.isClosed.frontier_subset (hT.2 T ⟨hT0, le_rfl⟩))
    rw [le_div_iff₀ hnd]
    have h2 : ‖T • d‖ ≤ ‖x + T • d‖ + ‖x‖ := by
      have := norm_sub_le (x + T • d) x
      simpa using this
    rw [norm_smul, Real.norm_of_nonneg hT0] at h2
    linarith
  set T := sSup J with hTdef
  have hT1 : 1 ≤ T := le_csSup hbdd h1J
  have hTJ : ∀ s ∈ Icc (0:ℝ) T, x + s • d ∈ F := by
    have hG : IsClosed {s : ℝ | x + s • d ∈ F} :=
      isClosed_frontier.preimage (by fun_prop)
    have hsub : Ico (0:ℝ) T ⊆ {s : ℝ | x + s • d ∈ F} := by
      intro s hs
      obtain ⟨T', hT'J, hsT'⟩ := exists_lt_of_lt_csSup ⟨1, h1J⟩ hs.2
      exact hT'J.2 s ⟨hs.1, hsT'.le⟩
    have := closure_minimal hsub hG
    rw [closure_Ico (by linarith : (0:ℝ) ≠ T)] at this
    exact this
  set e := x + T • d with he
  have hmax : ∀ m : ℝ, 0 < m → (∀ s ∈ Icc (0:ℝ) m, e + s • d ∈ F) → False := by
    intro m hm hext
    have hmJ : T + m ∈ J := by
      refine ⟨by linarith, fun s hs => ?_⟩
      by_cases hsT : s ≤ T
      · exact hTJ s ⟨hs.1, hsT⟩
      · have := hext (s - T) ⟨by linarith, by linarith [hs.2]⟩
        rw [he, add_assoc, ← add_smul] at this
        simpa using this
    have := le_csSup hbdd hmJ
    linarith
  refine ⟨T, hT1, hTJ, ?_⟩
  obtain ⟨r, hr, hloc⟩ := crown_local_boundary D (v := e)
  set ε := min (T / 2) (r / (2 * ‖d‖)) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by positivity)
  have hpF : e - ε • d ∈ F := by
    have := hTJ (T - ε) ⟨by linarith [min_le_left (T/2) (r / (2 * ‖d‖))], by linarith⟩
    convert this using 1
    rw [he, sub_smul]; abel
  have hpball : e - ε • d ∈ ball e r := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg hε0.le]
    have : ε ≤ r / (2 * ‖d‖) := min_le_right _ _
    calc ε * ‖d‖ ≤ r / (2 * ‖d‖) * ‖d‖ := by gcongr
      _ = r / 2 := by field_simp
      _ < r := by linarith
  obtain ⟨i, hei, hpi, -⟩ := hloc _ hpball hpF
  obtain ⟨α, β, hu, hw, h0, hε'⟩ := rcb_side_line hε0 hd hei hpi
  have hside : ∀ s ∈ segment ℝ α β, e + s • d ∈ F := by
    intro s hs
    apply rcb_side_subset_frontier D i
    change e + s • d ∈ segment ℝ (D.vertex i) (D.vertex (finRotate D.n i))
    rw [hu, hw]
    exact rcb_mem_seg_line hs
  rw [segment_eq_uIcc, mem_uIcc] at h0 hε'
  have hα : α ≤ 0 := by
    by_contra hα
    push_neg at hα
    refine hmax α hα fun s hs => hside s ?_
    rw [segment_eq_uIcc, mem_uIcc]
    rcases h0 with h0 | h0
    · left; constructor <;> linarith [hs.1, hs.2]
    · right; constructor <;> linarith [hs.1, hs.2]
  have hβ : β ≤ 0 := by
    by_contra hβ
    push_neg at hβ
    refine hmax β hβ fun s hs => hside s ?_
    rw [segment_eq_uIcc, mem_uIcc]
    rcases h0 with h0 | h0
    · left; constructor <;> linarith [hs.1, hs.2]
    · right; constructor <;> linarith [hs.1, hs.2]
  rcases h0 with h0 | h0
  · have hβ0 : β = 0 := le_antisymm hβ h0.2
    have hαneg : α < 0 := by rcases hε' with h | h <;> linarith
    refine ⟨finRotate D.n i, ?_, ?_⟩
    · refine rcb_genuine_of_local D hd ?_ hαneg.ne (Or.inl ?_) hmax
      · rw [hw, hβ0, zero_smul, add_zero]
      · rw [Equiv.symm_apply_apply]; exact hu
    · change D.vertex (finRotate D.n i) = e
      rw [hw, hβ0, zero_smul, add_zero]
  · have hα0 : α = 0 := le_antisymm hα h0.2
    have hβneg : β < 0 := by rcases hε' with h | h <;> linarith
    refine ⟨i, ?_, ?_⟩
    · refine rcb_genuine_of_local D hd ?_ hβneg.ne (Or.inr hw) hmax
      rw [hu, hα0, zero_smul, add_zero]
    · change D.vertex i = e
      rw [hu, hα0, zero_smul, add_zero]

private lemma rcb_seg_line_iff {e d z : Pt} {α β : ℝ} :
    z ∈ segment ℝ (e + α • d) (e + β • d) ↔ ∃ s ∈ segment ℝ α β, z = e + s • d := by
  constructor
  · intro hz
    rw [segment_eq_image'] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    refine ⟨α + t • (β - α), ?_, ?_⟩
    · rw [segment_eq_image']; exact ⟨t, ht, rfl⟩
    · simp only [smul_eq_mul]; module
  · rintro ⟨s, hs, rfl⟩
    exact rcb_mem_seg_line hs

private lemma rcb_frontier_mem_geometricEdge (D : PolygonalDisk) {x : Pt}
    (hx : x ∈ frontier D.carrier) :
    ∃ a b, D.IsGeometricEdge a b ∧ x ∈ segment ℝ a b := by
  have hx' := hx
  rw [D.frontier_eq] at hx'
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx'
  set u := D.vertex i with hu
  set w := D.vertex (finRotate D.n i) with hw
  have huw : u ≠ w := by
    intro h
    exact crown_finRotate_ne_self (by have := D.three_le; omega) i (D.vertex_injective h).symm
  have hsideF : segment ℝ u w ⊆ frontier D.carrier := rcb_side_subset_frontier D i
  have hside : ∀ s ∈ Icc (0:ℝ) 1, u + s • (w - u) ∈ frontier D.carrier := by
    intro s hs
    apply hsideF
    rw [segment_eq_image']; exact ⟨s, hs, rfl⟩
  have hside' : ∀ s ∈ Icc (0:ℝ) 1, w + s • (u - w) ∈ frontier D.carrier := by
    intro s hs
    apply hsideF
    rw [segment_symm, segment_eq_image']; exact ⟨s, hs, rfl⟩
  obtain ⟨T1, hT1, hT1F, hg1⟩ := rcb_frontier_extend D (sub_ne_zero.mpr huw.symm) hside
  obtain ⟨T2, hT2, hT2F, hg2⟩ := rcb_frontier_extend D (sub_ne_zero.mpr huw) hside'
  have hrw : w + T2 • (u - w) = u + (1 - T2) • (w - u) := by module
  refine ⟨w + T2 • (u - w), u + T1 • (w - u), ⟨hg2, hg1, ?_, ?_⟩, ?_⟩
  · rw [hrw]
    intro h
    have := rcb_smul_cancel (sub_ne_zero.mpr huw.symm) h
    linarith
  · intro z hz
    rw [hrw, rcb_seg_line_iff] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    rw [segment_eq_uIcc, mem_uIcc] at hs
    by_cases hs0 : 0 ≤ s
    · apply hT1F
      rcases hs with hs | hs <;> constructor <;> linarith [hs.1, hs.2]
    · have := hT2F (1 - s) (by rcases hs with hs | hs <;> constructor <;> linarith [hs.1, hs.2])
      convert this using 1; module
  · rw [hrw]
    rw [segment_eq_image'] at hxi
    obtain ⟨t, ht, rfl⟩ := hxi
    rw [rcb_seg_line_iff]
    refine ⟨t, ?_, rfl⟩
    rw [segment_eq_uIcc, mem_uIcc]
    left; constructor <;> linarith [ht.1, ht.2]

private lemma rcb_ray_bound {A B : Pt} {μ : ℝ} (hμ0 : 0 < μ) (hμ : μ ≤ Real.pi / 2)
    (hβ : μ ≤ InnerProductGeometry.angle A B) : ‖A‖ * Real.sin μ ≤ ‖A - B‖ := by
  set θ := InnerProductGeometry.angle A B with hθ
  have hinner : inner ℝ A B = Real.cos θ * (‖A‖ * ‖B‖) :=
    (InnerProductGeometry.cos_angle_mul_norm_mul_norm A B).symm
  have hsq : ‖A - B‖ ^ 2 = ‖A‖ ^ 2 - 2 * inner ℝ A B + ‖B‖ ^ 2 := norm_sub_sq_real A B
  have hsμ0 : 0 ≤ Real.sin μ := Real.sin_nonneg_of_nonneg_of_le_pi hμ0.le (by linarith [Real.pi_pos])
  have hsμ1 : Real.sin μ ≤ 1 := Real.sin_le_one μ
  have hA := norm_nonneg A
  have hB := norm_nonneg B
  have hpyth := Real.sin_sq_add_cos_sq θ
  have key : (‖A‖ * Real.sin μ) ^ 2 ≤ ‖A - B‖ ^ 2 := by
    rw [hsq, hinner]
    by_cases hc : Real.cos θ ≤ 0
    · have h1 : (‖A‖ * Real.sin μ) ^ 2 ≤ ‖A‖ ^ 2 := by
        rw [mul_pow]
        have : Real.sin μ ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg ‖A‖]
      nlinarith [mul_nonneg hA hB]
    · push_neg at hc
      have hθle : θ ≤ Real.pi / 2 := by
        by_contra h
        push_neg at h
        have : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt h
          (by linarith [InnerProductGeometry.angle_le_pi A B, Real.pi_pos])
        linarith
      have hsin : Real.sin μ ≤ Real.sin θ :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hθle hβ
      have hsθ : 0 ≤ Real.sin θ := le_trans hsμ0 hsin
      have h2 : (‖A‖ * Real.sin μ) ^ 2 ≤ (‖A‖ * Real.sin θ) ^ 2 := by
        apply pow_le_pow_left₀ (mul_nonneg hA hsμ0)
        exact mul_le_mul_of_nonneg_left hsin hA
      nlinarith [sq_nonneg (‖B‖ - ‖A‖ * Real.cos θ)]
  exact (pow_le_pow_iff_left₀ (mul_nonneg (norm_nonneg A) hsμ0) (norm_nonneg _)
    two_ne_zero).mp key

private lemma rcb_tri_convex (q A B : Pt) :
    Convex ℝ {p : Pt | ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α + β < 1 ∧ p = q + α • A + β • B} := by
  intro x hx y hy a b ha hb hab
  obtain ⟨α1, β1, h1, h2, h3, rfl⟩ := hx
  obtain ⟨α2, β2, h4, h5, h6, rfl⟩ := hy
  refine ⟨a * α1 + b * α2, a * β1 + b * β2, ?_, ?_, ?_, ?_⟩
  · rcases ha.lt_or_eq with ha' | ha'
    · nlinarith
    · subst ha'; simp at hab; subst hab; simpa using h4
  · rcases ha.lt_or_eq with ha' | ha'
    · nlinarith
    · subst ha'; simp at hab; subst hab; simpa using h5
  · rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_lt_mul_of_pos_left h3 ha', mul_le_mul_of_nonneg_left h6.le hb]
    · subst ha'; simp at hab; subst hab; simpa using h6
  · have hb' : b = 1 - a := by linarith
    subst hb'
    module

private lemma rcb_geometricEdge_symm {D : PolygonalDisk} {x y : Pt} (h : D.IsGeometricEdge x y) :
    D.IsGeometricEdge y x :=
  ⟨h.2.1, h.1, h.2.2.1.symm, segment_symm ℝ y x ▸ h.2.2.2⟩

private lemma rcb_adjacent_reflex (R : RootSeparation P) (p0 : P.Form) {q a b v' z' : Pt}
    (hqa : (P.disk p0).IsGeometricEdge q a) (hqb : (P.disk p0).IsGeometricEdge q b) (hab : a ≠ b)
    (hv' : v' ∈ openSegment ℝ q a) (hz' : z' ∈ openSegment ℝ q b)
    (hout : ∀ p ∈ openSegment ℝ v' z', p ∉ (P.disk p0).carrier)
    (hν : dist v' z' < R.ν) (hlam : dist v' z' < R.lam) :
    (P.disk p0).IsReflexCorner q a b := by
  set D := P.disk p0 with hD
  have hDcl : IsClosed D.carrier := D.compact.isClosed
  have hedge : ∀ {x y : Pt}, D.IsGeometricEdge x y → segment ℝ x y ⊆ D.carrier :=
    fun h => h.2.2.2.trans hDcl.frontier_subset
  obtain ⟨t1, ht10, ht11, hv'eq⟩ := crown_mem_openSegment_iff.mp hv'
  obtain ⟨t2, ht20, ht21, hz'eq⟩ := crown_mem_openSegment_iff.mp hz'
  set A := v' - q with hA
  set B := z' - q with hB
  have hAt : A = t1 • (a - q) := by rw [hA, hv'eq, add_sub_cancel_left]
  have hBt : B = t2 • (b - q) := by rw [hB, hz'eq, add_sub_cancel_left]
  have haq : a - q = t1⁻¹ • A := by rw [hAt, smul_smul, inv_mul_cancel₀ ht10.ne', one_smul]
  have hbq : b - q = t2⁻¹ • B := by rw [hBt, smul_smul, inv_mul_cancel₀ ht20.ne', one_smul]
  have hA0 : A ≠ 0 := by
    intro h; rw [h, smul_zero] at haq; exact hqa.2.2.1 (sub_eq_zero.mp haq).symm
  have hB0 : B ≠ 0 := by
    intro h; rw [h, smul_zero] at hbq; exact hqb.2.2.1 (sub_eq_zero.mp hbq).symm
  have hv'A : v' = q + A := by rw [hA]; abel
  have hz'B : z' = q + B := by rw [hB]; abel
  have hinA : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → q + s • A ∈ segment ℝ q a := by
    intro s hs0 hs1
    rw [crown_mem_segment_iff]
    refine ⟨s * t1, by positivity, by nlinarith, ?_⟩
    rw [hAt, smul_smul]
  have hinB : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → q + s • B ∈ segment ℝ q b := by
    intro s hs0 hs1
    rw [crown_mem_segment_iff]
    refine ⟨s * t2, by positivity, by nlinarith, ?_⟩
    rw [hBt, smul_smul]
  have hqD : q ∈ D.carrier := hedge hqa (left_mem_segment ℝ q a)
  have hout' : ∀ l : ℝ, 0 < l → l < 1 → q + (1 - l) • A + l • B ∉ D.carrier := by
    intro l hl0 hl1
    apply hout
    rw [crown_mem_openSegment_iff]
    refine ⟨l, hl0, hl1, ?_⟩
    rw [hv'A, hz'B]; module
  have hnotsub : ∀ {x y : Pt}, D.IsGeometricEdge x y → v' ∈ segment ℝ x y →
      z' ∈ segment ℝ x y → False := by
    intro x y hxy hvx hzx
    apply hout' (1 / 2) (by norm_num) (by norm_num)
    apply hedge hxy
    apply (convex_segment x y).segment_subset hvx hzx
    rw [crown_mem_segment_iff]
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    rw [hv'A, hz'B]; module
  have hind : ∀ α β : ℝ, α • A + β • B = 0 → α = 0 ∧ β = 0 := by
    intro α β h
    by_cases hβ : β = 0
    · subst hβ
      rw [zero_smul, add_zero, smul_eq_zero] at h
      rcases h with h | h
      · exact ⟨h, rfl⟩
      · exact absurd h hA0
    · exfalso
      set κ := -α / β with hκ
      have hBκ : B = κ • A := by
        have h2 : β • B = (-α) • A := by rw [neg_smul, ← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h
        rw [hκ, div_eq_inv_mul, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hβ, one_smul]
      have hκ0 : κ ≠ 0 := by
        intro h0; rw [h0, zero_smul] at hBκ; exact hB0 hBκ
      rcases lt_or_gt_of_ne hκ0 with hκn | hκp
      · apply hout' (1 / (1 - κ)) (by apply div_pos one_pos; linarith)
          (by rw [div_lt_one (by linarith)]; linarith)
        convert hqD using 1
        rw [hBκ, smul_smul, add_assoc, ← add_smul]
        have h1k : (1:ℝ) - κ ≠ 0 := by intro h; linarith
        have : 1 - 1 / (1 - κ) + 1 / (1 - κ) * κ = 0 := by
          field_simp; ring
        rw [this, zero_smul, add_zero]
      · by_cases hκ1 : κ ≤ 1
        · refine hnotsub hqa ?_ ?_
          · have := hinA 1 zero_le_one le_rfl; rwa [one_smul, ← hv'A] at this
          · have := hinA κ hκp.le hκ1; rwa [← hBκ, ← hz'B] at this
        · push_neg at hκ1
          refine hnotsub hqb ?_ ?_
          · have := hinB κ⁻¹ (inv_nonneg.mpr hκp.le) (inv_le_one_of_one_le₀ hκ1.le)
            rwa [hBκ, smul_smul, inv_mul_cancel₀ hκ0, one_smul, ← hv'A] at this
          · have := hinB 1 zero_le_one le_rfl; rwa [one_smul, ← hz'B] at this
  have hvz : 0 < dist v' z' := by
    rw [dist_pos]
    intro h
    have := hind 1 (-1) (by rw [hA, hB, h]; simp)
    norm_num at this
  have hdistBA : ‖B - A‖ = dist v' z' := by
    rw [dist_comm, dist_eq_norm, hA, hB]; congr 1; abel
  have hdistT : ∀ α β : ℝ, 0 < α → 0 < β → α + β < 1 →
      dist (q + α • A + β • B) (q + (α + β) • A) < dist v' z' ∧
      dist (q + α • A + β • B) (q + (α + β) • B) < dist v' z' := by
    intro α β hα hβ hαβ
    constructor
    · rw [dist_eq_norm]
      have : q + α • A + β • B - (q + (α + β) • A) = β • (B - A) := by module
      rw [this, norm_smul, Real.norm_of_nonneg hβ.le, hdistBA]
      have := mul_lt_mul_of_pos_right (show β < 1 by linarith) hvz
      linarith
    · rw [dist_eq_norm]
      have : q + α • A + β • B - (q + (α + β) • B) = (-α) • (B - A) := by module
      rw [this, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hα, hdistBA]
      have := mul_lt_mul_of_pos_right (show α < 1 by linarith) hvz
      linarith
  set Tset : Set Pt := {p : Pt | ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ α + β < 1 ∧
    p = q + α • A + β • B} with hTset
  have hTne_q : ∀ α β : ℝ, 0 < α → q + α • A + β • B ≠ q := by
    intro α β hα h
    have := (hind α β (by rw [add_assoc] at h; simpa using h)).1
    linarith
  have hTcorner : ∀ p ∈ Tset, D.IsGenuineCorner p → False := by
    rintro p ⟨α, β, hα, hβ, hαβ, rfl⟩ hc
    obtain ⟨h1, h2⟩ := hdistT α β hα hβ hαβ
    have hpq := hTne_q α β hα
    by_cases hpa : q + α • A + β • B = a
    · have hpb : q + α • A + β • B ≠ b := fun h => hab (hpa.symm.trans h)
      have := R.ν_le p0 _ q b hc hqb hpq hpb _ (hinB (α + β) (by linarith) hαβ.le)
      linarith
    · have := R.ν_le p0 _ q a hc hqa hpq hpa _ (hinA (α + β) (by linarith) hαβ.le)
      linarith
  have hdisj : Disjoint Tset (frontier D.carrier) := by
    rw [Set.disjoint_left]
    rintro f ⟨α, β, hα, hβ, hαβ, rfl⟩ hfF
    obtain ⟨h1, h2⟩ := hdistT α β hα hβ hαβ
    obtain ⟨x3, y3, h3, hf3⟩ := rcb_frontier_mem_geometricEdge D hfF
    have hnd1 : ¬ Disjoint ({x3, y3} : Set Pt) {q, a} := fun hdj => by
      have := R.lam_le p0 x3 y3 q a h3 hqa hdj _ hf3 _ (hinA (α + β) (by linarith) hαβ.le)
      linarith
    have hnd2 : ¬ Disjoint ({x3, y3} : Set Pt) {q, b} := fun hdj => by
      have := R.lam_le p0 x3 y3 q b h3 hqb hdj _ hf3 _ (hinB (α + β) (by linarith) hαβ.le)
      linarith
    rw [Set.not_disjoint_iff] at hnd1 hnd2
    obtain ⟨u1, hu1a, hu1b⟩ := hnd1
    obtain ⟨u2, hu2a, hu2b⟩ := hnd2
    simp only [mem_insert_iff, mem_singleton_iff] at hu1a hu1b hu2a hu2b
    have hcase : (∃ w, D.IsGeometricEdge q w ∧ q + α • A + β • B ∈ segment ℝ q w) ∨
        q + α • A + β • B ∈ segment ℝ a b := by
      by_cases hx3 : x3 = q
      · rw [hx3] at h3 hf3; exact Or.inl ⟨y3, h3, hf3⟩
      by_cases hy3 : y3 = q
      · rw [hy3] at h3 hf3
        exact Or.inl ⟨x3, rcb_geometricEdge_symm h3, by rwa [segment_symm]⟩
      right
      have hu1 : u1 = a := by
        rcases hu1b with h | h
        · rcases hu1a with h' | h'
          · exact absurd (h'.symm.trans h) hx3
          · exact absurd (h'.symm.trans h) hy3
        · exact h
      have hu2 : u2 = b := by
        rcases hu2b with h | h
        · rcases hu2a with h' | h'
          · exact absurd (h'.symm.trans h) hx3
          · exact absurd (h'.symm.trans h) hy3
        · exact h
      rw [hu1] at hu1a
      rw [hu2] at hu2a
      rcases hu1a with ha3 | ha3 <;> rcases hu2a with hb3 | hb3
      · exact absurd (ha3.trans hb3.symm) hab
      · rw [ha3, hb3]; exact hf3
      · rw [ha3, hb3, segment_symm]; exact hf3
      · exact absurd (ha3.trans hb3.symm) hab
    rcases hcase with ⟨w, hqw, hfw⟩ | hfab
    · rw [crown_mem_segment_iff] at hfw
      obtain ⟨l, hl0, hl1, hfl⟩ := hfw
      have hl0' : l ≠ 0 := by
        rintro rfl
        rw [zero_smul, add_zero] at hfl
        exact hTne_q α β hα hfl
      have hlpos : 0 < l := lt_of_le_of_ne hl0 (Ne.symm hl0')
      have hwq : w - q = l⁻¹ • (α • A + β • B) := by
        have hlw : l • (w - q) = α • A + β • B := by
          have := hfl
          rw [add_assoc] at this
          exact (add_left_cancel this).symm
        rw [← hlw, smul_smul, inv_mul_cancel₀ hl0', one_smul]
      have hw : w = q + l⁻¹ • (α • A + β • B) := by rw [← hwq]; abel
      by_cases hσ : (α + β) / l < 1
      · refine hTcorner w ⟨α / l, β / l, div_pos hα hlpos, div_pos hβ hlpos,
          by rwa [← add_div], ?_⟩ hqw.2.1
        rw [hw]; simp only [div_eq_mul_inv]; module
      · push_neg at hσ
        have hαβ0 : 0 < α + β := by linarith
        have hle : l ≤ α + β := by
          have := (le_div_iff₀ hlpos).mp hσ; linarith
        apply hout' (β / (α + β)) (div_pos hβ hαβ0) (by rw [div_lt_one hαβ0]; linarith)
        apply hedge hqw
        rw [crown_mem_segment_iff]
        refine ⟨l / (α + β), by positivity, by rw [div_le_one hαβ0]; exact hle, ?_⟩
        rw [hwq]
        have e1 : 1 - β / (α + β) = (l / (α + β) * l⁻¹) * α := by
          field_simp; ring
        have e2 : β / (α + β) = (l / (α + β) * l⁻¹) * β := by
          field_simp
        rw [e1, e2]; module
    · rw [crown_mem_segment_iff] at hfab
      obtain ⟨l, hl0, hl1, hfl⟩ := hfab
      have heq : q + α • A + β • B = q + ((1 - l) * t1⁻¹) • A + (l * t2⁻¹) • B := by
        rw [hfl]
        have ha' : a = q + t1⁻¹ • A := by rw [← haq]; abel
        have hb' : b = q + t2⁻¹ • B := by rw [← hbq]; abel
        rw [ha', hb']; module
      have heq' : (α - (1 - l) * t1⁻¹) • A + (β - l * t2⁻¹) • B = 0 := by
        rw [← sub_eq_zero.mpr heq]; module
      obtain ⟨e1, e2⟩ := hind _ _ heq'
      have hi1 : 1 ≤ t1⁻¹ := (one_le_inv₀ ht10).mpr ht11.le
      have hi2 : 1 ≤ t2⁻¹ := (one_le_inv₀ ht20).mpr ht21.le
      have h5 := mul_le_mul_of_nonneg_left hi1 (by linarith : (0:ℝ) ≤ 1 - l)
      have h6 := mul_le_mul_of_nonneg_left hi2 hl0
      rw [mul_one] at h5 h6
      linarith
  rcases macro_preconn_sub (rcb_tri_convex q A B).isPreconnected hdisj with hin | hext
  · exfalso
    apply hout' (1 / 2) (by norm_num) (by norm_num)
    have hcl : q + (1 - 1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B ∈ closure Tset := by
      let g : ℝ → Pt := fun τ => q + τ • ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B)
      have hg : Continuous g := by fun_prop
      have h1 : (1:ℝ) ∈ closure (Ioo (0:ℝ) 1) := by
        rw [closure_Ioo zero_ne_one]; exact ⟨zero_le_one, le_rfl⟩
      have himg := hg.continuousWithinAt.mem_closure_image h1
      have hsub : g '' Ioo 0 1 ⊆ Tset := by
        rintro _ ⟨τ, hτ, rfl⟩
        exact ⟨τ / 2, τ / 2, by linarith [hτ.1], by linarith [hτ.1], by linarith [hτ.2],
          by simp only [g]; module⟩
      have hg1 : g 1 = q + (1 - 1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B := by simp only [g]; module
      rw [← hg1]; exact closure_mono hsub himg
    exact hDcl.closure_subset (closure_mono interior_subset (closure_mono hin hcl))
  · refine ⟨hqa, hqb, hab, fun r hr => ?_⟩
    set na := ‖a - q‖ with hna
    set nb := ‖b - q‖ with hnb
    have hna0 : 0 < na := norm_pos_iff.mpr (sub_ne_zero.mpr hqa.2.2.1.symm)
    have hnb0 : 0 < nb := norm_pos_iff.mpr (sub_ne_zero.mpr hqb.2.2.1.symm)
    set ka := na⁻¹ * t1⁻¹ with hka
    set kb := nb⁻¹ * t2⁻¹ with hkb
    have hka0 : 0 < ka := by positivity
    have hkb0 : 0 < kb := by positivity
    set s := min (r / 2) (1 / (2 * (ka + kb))) with hs
    have hs0 : 0 < s := lt_min (by linarith) (by positivity)
    refine ⟨s, ⟨hs0, by linarith [min_le_left (r / 2) (1 / (2 * (ka + kb)))]⟩, ?_⟩
    have hmem : q + s • (na⁻¹ • (a - q) + nb⁻¹ • (b - q)) ∈ Tset := by
      have h1 : s ≤ 1 / (2 * (ka + kb)) := min_le_right _ _
      clear_value s
      refine ⟨s * ka, s * kb, mul_pos hs0 hka0, mul_pos hs0 hkb0, ?_, ?_⟩
      · have h2 := (le_div_iff₀ (by linarith)).mp h1
        have h3 : s * ka + s * kb = s * (2 * (ka + kb)) / 2 := by ring
        linarith
      · rw [haq, hbq, hka, hkb]; module
    intro hD'
    exact hext hmem (subset_closure hD')

private lemma rcb_map_dist (M : MacroPatch P) (x y : Pt) :
    dist (M.map x) (M.map y) = M.θ ^ M.j * dist x y := by
  have hc : 0 < M.θ ^ M.j := pow_pos (lt_trans zero_lt_one M.one_lt) _
  rw [dist_eq_norm, dist_eq_norm]
  have : M.map x - M.map y = (M.θ ^ M.j) • (x - y) := by
    simp only [MacroPatch.map]; module
  rw [this, norm_smul, Real.norm_of_nonneg hc.le]

private lemma rcb_core {𝒞 : Set (Set (PlacedTile P))} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hrδ : SectorRadiusProperty 𝒞 r δ) (R : RootSeparation P)
    (M : MacroPatch P) (hM : AllCrownsIn 𝒞 M.tiles) {v' z' : Pt}
    (hv'F : v' ∈ frontier (P.disk M.root).carrier) (hz'F : z' ∈ frontier (P.disk M.root).carrier)
    (hout : ∀ p ∈ openSegment ℝ v' z', p ∉ (P.disk M.root).carrier)
    (hdist : M.θ ^ M.j * dist v' z' < crownRadius r δ R)
    (hv : IsVertexOf M.tiles (M.map v')) : False := by
  set D := P.disk M.root with hD
  set c := M.θ ^ M.j with hc
  have hc0 : 0 < c := pow_pos (lt_trans zero_lt_one M.one_lt) _
  have hc1 : 1 ≤ c := one_le_pow₀ M.one_lt.le
  have hsinμ : 0 < Real.sin R.μ :=
    Real.sin_pos_of_pos_of_lt_pi R.μ_pos (by linarith [R.μ_le, Real.pi_pos])
  set d := crownRadius r δ R with hd
  have hdν : d ≤ R.ν / 2 := by
    rw [hd, crownRadius]
    have := min_le_left (min r R.ν) (min R.lam (min r δ * Real.sin R.μ))
    have := min_le_right r R.ν
    linarith
  have hdlam : d ≤ R.lam / 2 := by
    rw [hd, crownRadius]
    have := min_le_right (min r R.ν) (min R.lam (min r δ * Real.sin R.μ))
    have := min_le_left R.lam (min r δ * Real.sin R.μ)
    linarith
  have hdsin : d ≤ min r δ * Real.sin R.μ / 2 := by
    rw [hd, crownRadius]
    have := min_le_right (min r R.ν) (min R.lam (min r δ * Real.sin R.μ))
    have := min_le_right R.lam (min r δ * Real.sin R.μ)
    linarith
  have hd0 : 0 ≤ d := le_trans (mul_nonneg hc0.le dist_nonneg) hdist.le
  have hdist1 : dist v' z' ≤ c * dist v' z' := le_mul_of_one_le_left dist_nonneg hc1
  have hν : dist v' z' < R.ν := by linarith [R.ν_pos]
  have hlam : dist v' z' < R.lam := by linarith [R.lam_pos]
  have hDcl : IsClosed D.carrier := D.compact.isClosed
  have hedge : ∀ {x y : Pt}, D.IsGeometricEdge x y → segment ℝ x y ⊆ D.carrier :=
    fun h => h.2.2.2.trans hDcl.frontier_subset
  have hnotsub : ∀ {x y : Pt}, D.IsGeometricEdge x y → v' ∈ segment ℝ x y →
      z' ∈ segment ℝ x y → False := by
    intro x y hxy hvx hzx
    have hm : v' + (1 / 2 : ℝ) • (z' - v') ∈ openSegment ℝ v' z' :=
      crown_mem_openSegment_iff.mpr ⟨1 / 2, by norm_num, by norm_num, rfl⟩
    apply hout _ hm
    apply hedge hxy
    apply (convex_segment x y).segment_subset hvx hzx
    exact openSegment_subset_segment ℝ v' z' hm
  obtain ⟨x1, y1, h1, hv1⟩ := rcb_frontier_mem_geometricEdge D hv'F
  obtain ⟨x2, y2, h2, hz2⟩ := rcb_frontier_mem_geometricEdge D hz'F
  by_cases hdj : Disjoint ({x1, y1} : Set Pt) {x2, y2}
  · have := R.lam_le M.root x1 y1 x2 y2 h1 h2 hdj v' hv1 z' hz2
    linarith
  obtain ⟨q, a, b, hqa, hqb, hva, hzb⟩ : ∃ q a b, D.IsGeometricEdge q a ∧
      D.IsGeometricEdge q b ∧ v' ∈ segment ℝ q a ∧ z' ∈ segment ℝ q b := by
    rw [Set.not_disjoint_iff] at hdj
    obtain ⟨u, hu1, hu2⟩ := hdj
    simp only [mem_insert_iff, mem_singleton_iff] at hu1 hu2
    have e1 : ∃ a, D.IsGeometricEdge u a ∧ v' ∈ segment ℝ u a := by
      rcases hu1 with rfl | rfl
      · exact ⟨y1, h1, hv1⟩
      · exact ⟨x1, rcb_geometricEdge_symm h1, by rwa [segment_symm]⟩
    have e2 : ∃ b, D.IsGeometricEdge u b ∧ z' ∈ segment ℝ u b := by
      rcases hu2 with rfl | rfl
      · exact ⟨y2, h2, hz2⟩
      · exact ⟨x2, rcb_geometricEdge_symm h2, by rwa [segment_symm]⟩
    obtain ⟨a, ha, hva⟩ := e1
    obtain ⟨b, hb, hzb⟩ := e2
    exact ⟨u, a, b, ha, hb, hva, hzb⟩
  by_cases hab : a = b
  · rw [← hab] at hzb
    exact hnotsub hqa hva hzb
  by_cases hvq : v' = q
  · exact hnotsub hqb (hvq ▸ left_mem_segment ℝ q b) hzb
  by_cases hzq : z' = q
  · exact hnotsub hqa hva (hzq ▸ left_mem_segment ℝ q a)
  by_cases hva' : v' = a
  · have := R.ν_le M.root a q b hqa.2.1 hqb hqa.2.2.1.symm hab z' hzb
    rw [← hva'] at this
    linarith
  by_cases hzb' : z' = b
  · have := R.ν_le M.root b q a hqb.2.1 hqa hqb.2.2.1.symm (Ne.symm hab) v' hva
    rw [← hzb', dist_comm] at this
    linarith
  have hvo : v' ∈ openSegment ℝ q a :=
    mem_openSegment_of_ne_left_right (Ne.symm hvq) (Ne.symm hva') hva
  have hzo : z' ∈ openSegment ℝ q b :=
    mem_openSegment_of_ne_left_right (Ne.symm hzq) (Ne.symm hzb') hzb
  have hrefl := rcb_adjacent_reflex R M.root hqa hqb hab hvo hzo hout hν hlam
  have hμ := R.μ_le_reflex M.root q a b hrefl
  obtain ⟨t1, ht10, ht11, hv'eq⟩ := crown_mem_openSegment_iff.mp hvo
  obtain ⟨t2, ht20, ht21, hz'eq⟩ := crown_mem_openSegment_iff.mp hzo
  have hmapopen : M.map v' ∈ openSegment ℝ (M.map q) (M.map a) := by
    rw [crown_mem_openSegment_iff]
    refine ⟨t1, ht10, ht11, ?_⟩
    rw [hv'eq]; simp only [MacroPatch.map]; module
  have hgap := incidentMacroEdgeVertexGap hr hδ hrδ M hM (q := M.map q) (x := M.map a)
    (Or.inl ⟨q, a, hqa, rfl⟩) hv hmapopen
  rw [rcb_map_dist] at hgap
  have hang : R.μ ≤ InnerProductGeometry.angle (v' - q) (z' - q) := by
    rw [hv'eq, hz'eq, add_sub_cancel_left, add_sub_cancel_left,
      InnerProductGeometry.angle_smul_left_of_pos _ _ ht10,
      InnerProductGeometry.angle_smul_right_of_pos _ _ ht20]
    exact hμ
  have hray := rcb_ray_bound R.μ_pos R.μ_le hang
  have hsub : (v' - q) - (z' - q) = v' - z' := by abel
  rw [hsub, ← dist_eq_norm, ← dist_eq_norm] at hray
  have k1 : min r δ * Real.sin R.μ ≤ c * dist v' q * Real.sin R.μ :=
    mul_le_mul_of_nonneg_right hgap hsinμ.le
  have k2 : c * (dist v' q * Real.sin R.μ) ≤ c * dist v' z' :=
    mul_le_mul_of_nonneg_left hray hc0.le
  have k3 : c * dist v' q * Real.sin R.μ = c * (dist v' q * Real.sin R.μ) := by ring
  have hmin0 : 0 < min r δ * Real.sin R.μ := mul_pos (lt_min hr hδ) hsinμ
  linarith

private lemma rcb_mem_disk_iff (M : MacroPatch P) (p : Pt) :
    p ∈ (P.disk M.root).carrier ↔ M.map p ∈ support M.tiles := by
  have hc : M.θ ^ M.j ≠ 0 := (pow_pos (lt_trans zero_lt_one M.one_lt) _).ne'
  rw [M.support_eq, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
    Set.mem_smul_set_iff_inv_smul_mem₀ hc]
  simp only [MacroPatch.map, neg_add_cancel_left, inv_smul_smul₀ hc]

private lemma rcb_frontier_of_ray {S : Set Pt} {x w : Pt} (hx : x ∈ S) (hw : w ≠ x)
    (h : ∀ l ∈ Ioo (0:ℝ) 1, x + l • (w - x) ∉ S) : x ∈ frontier S := by
  refine ⟨subset_closure hx, fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  have hn : 0 < ‖w - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw)
  have hl0 : 0 < min (1 / 2 : ℝ) (ε / (2 * ‖w - x‖)) := lt_min (by norm_num) (by positivity)
  apply h (min (1 / 2 : ℝ) (ε / (2 * ‖w - x‖)))
    ⟨hl0, by linarith [min_le_left (1 / 2 : ℝ) (ε / (2 * ‖w - x‖))]⟩
  apply hball
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hl0.le]
  have : min (1 / 2 : ℝ) (ε / (2 * ‖w - x‖)) ≤ ε / (2 * ‖w - x‖) := min_le_right _ _
  calc min (1 / 2 : ℝ) (ε / (2 * ‖w - x‖)) * ‖w - x‖ ≤ ε / (2 * ‖w - x‖) * ‖w - x‖ := by
        gcongr
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

private lemma rcb_mem_Omega {𝒞 : Set (Set (PlacedTile P))} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hrδ : SectorRadiusProperty 𝒞 r δ) (R : RootSeparation P)
    (M : MacroPatch P) (hM : AllCrownsIn 𝒞 M.tiles) {v : Pt} (hv : IsVertexOf M.tiles v)
    {y : Pt} (hyR : y ∈ support M.tiles) (hyb : y ∈ ball v (crownRadius r δ R)) :
    y ∈ Omega (crown M.tiles v) v := by
  obtain ⟨ρ, hρ, hnear⟩ := gap_near_vertex M.tiles M.finite v
  suffices h : ∃ s : ℝ, 0 < s ∧ v + s • (y - v) ∈ support M.tiles ∧
      v + s • (y - v) ∈ ball v ρ by
    obtain ⟨s, hs, hsR, hsb⟩ := h
    obtain ⟨A, hA, hcone⟩ := hnear _ hsb hsR
    have := gap_cone_scale hcone (inv_pos.mpr hs)
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.ne', one_smul, add_sub_cancel] at this
    exact mem_iUnion₂.mpr ⟨A, hA, this⟩
  by_cases hyv : y = v
  · refine ⟨1, one_pos, ?_, ?_⟩
    · rw [hyv, sub_self, smul_zero, add_zero, ← hyv]; exact hyR
    · rw [hyv, sub_self, smul_zero, add_zero]; exact mem_ball_self hρ
  have hn : 0 < ‖y - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyv)
  have hs00 : 0 < min 1 (ρ / (2 * ‖y - v‖)) := lt_min one_pos (by positivity)
  set s0 := min 1 (ρ / (2 * ‖y - v‖)) with hs0
  have hs01 : s0 ≤ 1 := min_le_left _ _
  have hball : ∀ s, 0 < s → s ≤ s0 → v + s • (y - v) ∈ ball v ρ := by
    intro s hs hss
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    have : s ≤ ρ / (2 * ‖y - v‖) := hss.trans (min_le_right _ _)
    calc s * ‖y - v‖ ≤ ρ / (2 * ‖y - v‖) * ‖y - v‖ := by gcongr
      _ = ρ / 2 := by field_simp
      _ < ρ := by linarith
  by_contra hcon
  push_neg at hcon
  have hgap : ∀ s, 0 < s → s ≤ s0 → v + s • (y - v) ∉ support M.tiles :=
    fun s hs hss hmem => hcon s hs hmem (hball s hs hss)
  set K := {s : ℝ | s ∈ Icc s0 1 ∧ v + s • (y - v) ∈ support M.tiles} with hK
  have hKcl : IsClosed K :=
    isClosed_Icc.inter ((macro_support_closed M).preimage (by fun_prop))
  have h1K : (1:ℝ) ∈ K := ⟨⟨hs01, le_rfl⟩, by simpa using hyR⟩
  have hKbdd : BddBelow K := ⟨s0, fun s hs => hs.1.1⟩
  have hcK : sInf K ∈ K := hKcl.csInf_mem ⟨1, h1K⟩ hKbdd
  set c := sInf K with hc
  have hc0 : 0 < c := lt_of_lt_of_le hs00 hcK.1.1
  have hc1 : c ≤ 1 := hcK.1.2
  have hbefore : ∀ s, 0 < s → s < c → v + s • (y - v) ∉ support M.tiles := by
    intro s hs hsc hmem
    by_cases hss : s ≤ s0
    · exact hgap s hs hss hmem
    · push_neg at hss
      have : c ≤ s := csInf_le hKbdd ⟨⟨hss.le, by linarith⟩, hmem⟩
      linarith
  have hθc : 0 < M.θ ^ M.j := pow_pos (lt_trans zero_lt_one M.one_lt) _
  have hmapinv : ∀ x, M.map ((M.θ ^ M.j)⁻¹ • (-M.offset + x)) = x := by
    intro x
    simp only [MacroPatch.map]
    rw [smul_inv_smul₀ hθc.ne']; abel
  set z := v + c • (y - v) with hz
  set v' := (M.θ ^ M.j)⁻¹ • (-M.offset + v) with hv'
  set z' := (M.θ ^ M.j)⁻¹ • (-M.offset + z) with hz'
  have hmv : M.map v' = v := hmapinv v
  have hmz : M.map z' = z := hmapinv z
  have hmap_seg : ∀ l : ℝ, M.map (v' + l • (z' - v')) = v + (l * c) • (y - v) := by
    intro l
    have : M.map (v' + l • (z' - v')) = M.map v' + l • (M.map z' - M.map v') := by
      simp only [MacroPatch.map]; module
    rw [this, hmv, hmz, hz]; module
  have hvR : v ∈ support M.tiles := by
    obtain ⟨B, hB, hvB⟩ := hv
    exact mem_iUnion₂.mpr ⟨B, hB, gap_vertex_mem_carrier B hvB⟩
  have hv'D : v' ∈ (P.disk M.root).carrier := (rcb_mem_disk_iff M v').mpr (hmv ▸ hvR)
  have hz'D : z' ∈ (P.disk M.root).carrier := (rcb_mem_disk_iff M z').mpr (hmz ▸ hcK.2)
  have hout : ∀ p ∈ openSegment ℝ v' z', p ∉ (P.disk M.root).carrier := by
    intro p hp hpD
    obtain ⟨l, hl0, hl1, rfl⟩ := crown_mem_openSegment_iff.mp hp
    rw [rcb_mem_disk_iff, hmap_seg] at hpD
    have : l * c < c := by nlinarith
    exact hbefore (l * c) (mul_pos hl0 hc0) this hpD
  have hvz : z' ≠ v' := by
    intro h
    have h2 : z = v := by rw [← hmz, ← hmv, h]
    rw [hz] at h2
    have h3 : c • (y - v) = 0 := by
      have := congrArg (· - v) h2
      simpa using this
    rcases smul_eq_zero.mp h3 with h4 | h4
    · linarith
    · exact hyv (sub_eq_zero.mp h4)
  have hv'F : v' ∈ frontier (P.disk M.root).carrier :=
    rcb_frontier_of_ray hv'D hvz fun l hl =>
      hout _ (crown_mem_openSegment_iff.mpr ⟨l, hl.1, hl.2, rfl⟩)
  have hz'F : z' ∈ frontier (P.disk M.root).carrier := by
    refine rcb_frontier_of_ray hz'D hvz.symm fun l hl => hout _ ?_
    rw [crown_mem_openSegment_iff]
    refine ⟨1 - l, by linarith [hl.2], by linarith [hl.1], ?_⟩
    module
  have hdist : M.θ ^ M.j * dist v' z' < crownRadius r δ R := by
    rw [← rcb_map_dist, hmv, hmz, hz, dist_eq_norm]
    have h1 : v - (v + c • (y - v)) = (-c) • (y - v) := by module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hc0]
    have h2 : dist y v < crownRadius r δ R := hyb
    rw [dist_eq_norm] at h2
    have h3 : c * ‖y - v‖ ≤ ‖y - v‖ := by
      have := mul_le_mul_of_nonneg_right hc1 (norm_nonneg (y - v))
      linarith
    linarith
  exact rcb_core hr hδ hrδ R M hM hv'F hz'F hout hdist (hmv ▸ hv)

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
  constructor
  · rintro y ⟨hyR, hyb⟩
    exact ⟨rcb_mem_Omega hr hδ hrδ R M hM hv hyR hyb, hyb⟩
  · rintro y ⟨hyO, hyb⟩
    have hdr : crownRadius r δ R ≤ r := by
      rw [crownRadius]
      have := min_le_left (min r R.ν) (min R.lam (min r δ * Real.sin R.μ))
      have := min_le_left r R.ν
      linarith
    obtain ⟨hsupp, -⟩ := hrδ _ (hM v hv) v
    rw [gap_translateSet_neg] at hsupp
    have hy : y ∈ Omega (crown M.tiles v) v ∩ ball v r := ⟨hyO, ball_subset_ball hdr hyb⟩
    rw [← hsupp] at hy
    exact hy.1

/-! ## `lem:trimmed-edge-ball` -/

private def trimmedJcr (u v : Pt) : ℝ := u 0 * v 1 - u 1 * v 0

private def trimmedJrot (u : Pt) : Pt := !₂[-(u 1), u 0]

private lemma trimmedJcr_add_right (u v w : Pt) :
    trimmedJcr u (v + w) = trimmedJcr u v + trimmedJcr u w := by
  simp [trimmedJcr]
  ring

private lemma trimmedJcr_smul_right (u v : Pt) (c : ℝ) :
    trimmedJcr u (c • v) = c * trimmedJcr u v := by
  simp [trimmedJcr]
  ring

private lemma trimmedJcr_smul_left (u v : Pt) (c : ℝ) :
    trimmedJcr (c • u) v = c * trimmedJcr u v := by
  simp [trimmedJcr]
  ring

private lemma trimmedJcr_self (u : Pt) : trimmedJcr u u = 0 := by
  simp [trimmedJcr]
  ring

private lemma trimmed_norm_sq (u : Pt) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]

private lemma trimmedJcr_jrot (u : Pt) : trimmedJcr u (trimmedJrot u) = ‖u‖ ^ 2 := by
  rw [trimmed_norm_sq]
  simp [trimmedJcr, trimmedJrot]
  ring

private lemma trimmed_norm_jrot (u : Pt) : ‖trimmedJrot u‖ = ‖u‖ := by
  have h1 := trimmed_norm_sq (trimmedJrot u)
  have h2 := trimmed_norm_sq u
  simp [trimmedJrot] at h1
  change ‖!₂[-(u 1), u 0]‖ = ‖u‖
  have h : ‖trimmedJrot u‖ ^ 2 = ‖u‖ ^ 2 := by
    simpa [trimmedJrot, h1, h2] using
      (show u 1 ^ 2 + u 0 ^ 2 = u 0 ^ 2 + u 1 ^ 2 by ring)
  have hleft : 0 ≤ ‖trimmedJrot u‖ := norm_nonneg _
  have hright : 0 ≤ ‖u‖ := norm_nonneg _
  change ‖trimmedJrot u‖ = ‖u‖
  nlinarith

private lemma trimmed_pt_ext {u v : Pt} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i
  fin_cases i <;> simp [h0, h1]

private lemma trimmed_exists_smul_of_jcr_eq_zero {u v : Pt} (hu : u ≠ 0)
    (h : trimmedJcr u v = 0) : ∃ t : ℝ, v = t • u := by
  have hp : 0 < u 0 ^ 2 + u 1 ^ 2 := by
    rw [← trimmed_norm_sq]
    positivity
  refine ⟨(u 0 * v 0 + u 1 * v 1) / (u 0 ^ 2 + u 1 ^ 2), ?_⟩
  unfold trimmedJcr at h
  apply trimmed_pt_ext <;> simp <;> field_simp
  · linear_combination (-(u 1)) * h
  · linear_combination (u 0) * h

private lemma trimmed_vertex_ne_next (D : PolygonalDisk) (i : Fin D.n) :
    D.vertex i ≠ D.vertex (finRotate D.n i) := by
  intro h
  have hn := crown_finRotate_ne_self (by have := D.three_le; omega) i
  exact hn (D.vertex_injective h).symm

private lemma trimmed_eq_of_openSegment_inter_side (D : PolygonalDisk)
    {i j : Fin D.n} {q : Pt}
    (hq : q ∈ openSegment ℝ (D.vertex i) (D.vertex (finRotate D.n i)))
    (hq' : q ∈ D.side j) : j = i := by
  by_contra hji
  have h := D.simple i j (Ne.symm hji)
    ⟨openSegment_subset_segment ℝ _ _ hq, hq'⟩
  have hab := trimmed_vertex_ne_next D i
  rcases h.1 with h1 | h1
  · rw [h1] at hq
    exact hab ((left_mem_openSegment_iff).1 hq)
  · rw [Set.mem_singleton_iff] at h1
    rw [h1] at hq
    exact hab ((right_mem_openSegment_iff).1 hq)

private def TrimmedHalfDiskOn (D : PolygonalDisk) (i : Fin D.n) (U : Set Pt) : Prop :=
  ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ U,
    (x ∈ D.carrier ↔
      0 ≤ σ * trimmedJcr (D.vertex (finRotate D.n i) - D.vertex i) (x - D.vertex i)) ∧
    (x ∈ interior D.carrier ↔
      0 < σ * trimmedJcr (D.vertex (finRotate D.n i) - D.vertex i) (x - D.vertex i))

private lemma trimmedHalfDiskOn_mono {D : PolygonalDisk} {i : Fin D.n} {U V : Set Pt}
    (h : TrimmedHalfDiskOn D i V) (hUV : U ⊆ V) : TrimmedHalfDiskOn D i U := by
  obtain ⟨σ, hσ, h⟩ := h
  exact ⟨σ, hσ, fun x hx => h x (hUV hx)⟩

private lemma trimmed_local_halfdisk (D : PolygonalDisk) (i : Fin D.n) {q : Pt}
    (hq : q ∈ openSegment ℝ (D.vertex i) (D.vertex (finRotate D.n i))) :
    ∃ r > 0, TrimmedHalfDiskOn D i (ball q r) := by
  set a := D.vertex i with ha_def
  set b := D.vertex (finRotate D.n i) with hb_def
  have hab : a ≠ b := trimmed_vertex_ne_next D i
  set u := b - a with hu_def
  have hu : u ≠ 0 := sub_ne_zero.2 hab.symm
  have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
  obtain ⟨s, hs0, hs1, hqs⟩ := crown_mem_openSegment_iff.1 hq
  obtain ⟨r0, hr0, hboundary⟩ := crown_local_boundary D (v := q)
  have hm : 0 < min s (1 - s) := lt_min hs0 (by linarith)
  set r := min r0 (min s (1 - s) * ‖u‖) with hr_def
  have hr : 0 < r := lt_min hr0 (mul_pos hm hun)
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hru : r ≤ min s (1 - s) * ‖u‖ := min_le_right _ _
  set c : Pt → ℝ := fun x => trimmedJcr u (x - a) with hc_def
  have hcq : c q = 0 := by
    simp only [hc_def, hqs, add_sub_cancel_left, ← hu_def,
      trimmedJcr_smul_right, trimmedJcr_self, mul_zero]
  have hside : ∀ x ∈ ball q r, (x ∈ segment ℝ a b ↔ c x = 0) := by
    intro x hx
    constructor
    · intro hxs
      obtain ⟨t, -, -, rfl⟩ := crown_mem_segment_iff.1 hxs
      simp [hc_def, ← hu_def, trimmedJcr_smul_right, trimmedJcr_self]
    · intro hcx
      obtain ⟨t, ht⟩ := trimmed_exists_smul_of_jcr_eq_zero hu hcx
      have hx' : x = a + t • u := by rw [← ht]; abel
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have hxq : x - q = (t - s) • u := by rw [hx', hqs]; module
      rw [hxq, norm_smul, Real.norm_eq_abs] at hx
      have h2 : |t - s| < min s (1 - s) := by
        have hlt := lt_of_lt_of_le hx hru
        exact (mul_lt_mul_iff_of_pos_right hun).1 hlt
      have h3 := lt_of_lt_of_le h2 (min_le_left _ _)
      have h4 := lt_of_lt_of_le h2 (min_le_right _ _)
      rw [abs_lt] at h3 h4
      exact crown_mem_segment_iff.2 ⟨t, by linarith, by linarith, hx'⟩
  have hfront : ∀ x ∈ ball q r,
      (x ∈ frontier D.carrier ↔ x ∈ segment ℝ a b) := by
    intro x hx
    constructor
    · intro hxf
      obtain ⟨j, hqj, hxj, -⟩ := hboundary x (Metric.ball_subset_ball hrr0 hx) hxf
      have hji : j = i := trimmed_eq_of_openSegment_inter_side D hq hqj
      simpa [hji] using hxj
    · intro hxs
      rw [D.frontier_eq]
      exact Set.mem_iUnion.2 ⟨i, hxs⟩
  have hclosed : IsClosed D.carrier := D.compact.isClosed
  set H : ℝ → Set Pt := fun τ => {x | x ∈ ball q r ∧ 0 < τ * c x} with hH_def
  have hHconv : ∀ τ, Convex ℝ (H τ) := by
    intro τ x hx y hy α β hα hβ hαβ
    refine ⟨(convex_ball q r) hx.1 hy.1 hα hβ hαβ, ?_⟩
    have hcxy : c (α • x + β • y) = α * c x + β * c y := by
      simp only [hc_def]
      have he : α • x + β • y - a = α • (x - a) + β • (y - a) := by
        rw [show β = 1 - α by linarith]
        module
      rw [he, trimmedJcr_add_right, trimmedJcr_smul_right, trimmedJcr_smul_right]
    rw [hcxy]
    rcases eq_or_lt_of_le hα with hα0 | hαpos
    · subst α
      simp at hαβ
      subst β
      simpa using hy.2
    · nlinarith [mul_pos hαpos hx.2, mul_nonneg hβ hy.2.le]
  have hHsplit : ∀ τ, H τ ⊆ interior D.carrier ∨ H τ ⊆ D.carrierᶜ := by
    intro τ
    refine (hHconv τ).isPreconnected.subset_or_subset isOpen_interior
      hclosed.isOpen_compl ?_ ?_
    · rw [Set.disjoint_iff]
      intro x hx
      exact hx.2 (interior_subset hx.1)
    · intro x hx
      by_cases hxc : x ∈ D.carrier
      · left
        by_contra hxi
        have hxf : x ∈ frontier D.carrier := by
          rw [← self_diff_frontier] at hxi
          by_contra hh
          exact hxi ⟨hxc, hh⟩
        have hc0 := (hside x hx.1).1 ((hfront x hx.1).1 hxf)
        have hxpos : 0 < τ * c x := hx.2
        rw [hc0, mul_zero] at hxpos
        exact lt_irrefl _ hxpos
      · exact Or.inr hxc
  have hcJ : ∀ (y : Pt) (δ : ℝ),
      c (y + δ • trimmedJrot u) = c y + δ * ‖u‖ ^ 2 := by
    intro y δ
    simp only [hc_def]
    rw [show y + δ • trimmedJrot u - a = (y - a) + δ • trimmedJrot u by abel,
      trimmedJcr_add_right, trimmedJcr_smul_right, trimmedJcr_jrot]
  have happrox : ∀ x ∈ ball q r, c x = 0 → ∀ τ, (τ = 1 ∨ τ = -1) →
      ∀ ε > 0, ∃ y ∈ H τ, dist x y < ε := by
    intro x hx hcx τ hτ ε hε
    have hxq : 0 < r - dist x q := by rw [Metric.mem_ball] at hx; linarith
    set δ := min ε (r - dist x q) / (2 * ‖u‖) with hδ
    have hδpos : 0 < δ := div_pos (lt_min hε hxq) (by positivity)
    set y := x + (τ * δ) • trimmedJrot u with hy_def
    have hτabs : |τ| = 1 := by rcases hτ with rfl | rfl <;> norm_num
    have hτ2 : τ * τ = 1 := by rcases hτ with rfl | rfl <;> norm_num
    have hdist : dist x y = δ * ‖u‖ := by
      rw [dist_eq_norm, show x - y = -((τ * δ) • trimmedJrot u) by rw [hy_def]; abel,
        norm_neg, norm_smul, trimmed_norm_jrot, Real.norm_eq_abs, abs_mul, hτabs,
        abs_of_pos hδpos, one_mul]
    have hδu : δ * ‖u‖ = min ε (r - dist x q) / 2 := by
      rw [hδ]
      field_simp
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball]
      calc
        dist y q ≤ dist y x + dist x q := dist_triangle _ _ _
        _ < r := by
          rw [dist_comm, hdist, hδu]
          have := min_le_right ε (r - dist x q)
          linarith
    · rw [hy_def, hcJ, hcx]
      have heq : τ * (0 + τ * δ * ‖u‖ ^ 2) =
          (τ * τ) * (δ * ‖u‖ ^ 2) := by ring
      rw [heq, hτ2, one_mul]
      positivity
    · rw [hdist, hδu]
      have := min_le_left ε (r - dist x q)
      linarith
  have hqint : q ∉ interior D.carrier := by
    have hqf : q ∈ frontier D.carrier := by
      rw [D.frontier_eq]
      exact Set.mem_iUnion.2 ⟨i, openSegment_subset_segment ℝ _ _ hq⟩
    exact fun h => hqf.2 h
  have hqc : q ∈ D.carrier :=
    crown_side_subset_carrier D i (openSegment_subset_segment ℝ _ _ hq)
  have hnotboth : ¬ (H 1 ⊆ interior D.carrier ∧ H (-1) ⊆ interior D.carrier) := by
    rintro ⟨h1, h2⟩
    apply hqint
    rw [mem_interior_iff_mem_nhds]
    apply Filter.mem_of_superset (Metric.ball_mem_nhds q hr)
    intro x hx
    rcases lt_trichotomy (c x) 0 with hlt | heq | hgt
    · exact interior_subset (h2 ⟨hx, by linarith⟩)
    · rw [← hclosed.closure_eq, Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨y, hy, hxy⟩ := happrox x hx heq 1 (Or.inl rfl) ε hε
      exact ⟨y, interior_subset (h1 hy), hxy⟩
    · exact interior_subset (h1 ⟨hx, by linarith⟩)
  have hnotnone : ¬ (H 1 ⊆ D.carrierᶜ ∧ H (-1) ⊆ D.carrierᶜ) := by
    rintro ⟨h1, h2⟩
    have hq' := hqc
    rw [← D.regular_closed, Metric.mem_closure_iff] at hq'
    obtain ⟨y, hyi, hqy⟩ := hq' r hr
    have hyb : y ∈ ball q r := by rw [Metric.mem_ball, dist_comm]; exact hqy
    obtain ⟨ε, hε, hεi⟩ := Metric.isOpen_iff.1 isOpen_interior y hyi
    rcases lt_trichotomy (c y) 0 with hlt | heq | hgt
    · exact h2 ⟨hyb, by linarith⟩ (interior_subset hyi)
    · obtain ⟨z, hz, hyz⟩ := happrox y hyb heq 1 (Or.inl rfl) ε hε
      exact h1 hz (interior_subset (hεi (by rw [Metric.mem_ball, dist_comm]; exact hyz)))
    · exact h1 ⟨hyb, by linarith⟩ (interior_subset hyi)
  have key : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      H σ ⊆ interior D.carrier ∧ H (-σ) ⊆ D.carrierᶜ := by
    rcases hHsplit 1 with h1 | h1 <;> rcases hHsplit (-1) with h2 | h2
    · exact absurd ⟨h1, h2⟩ hnotboth
    · exact ⟨1, Or.inl rfl, h1, h2⟩
    · exact ⟨-1, Or.inr rfl, h2, by simpa using h1⟩
    · exact absurd ⟨h1, h2⟩ hnotnone
  obtain ⟨σ, hσ, hint, hext⟩ := key
  refine ⟨r, hr, σ, hσ, fun x hx => ⟨?_, ?_⟩⟩
  · change (x ∈ D.carrier ↔ 0 ≤ σ * c x)
    constructor
    · intro hxc
      by_contra hneg
      push_neg at hneg
      exact hext ⟨hx, by linarith⟩ hxc
    · intro h
      rcases eq_or_lt_of_le h with h0 | hpos
      · have hc0 : c x = 0 := by rcases hσ with rfl | rfl <;> linarith
        exact crown_frontier_subset_of_isClosed hclosed
          ((hfront x hx).2 ((hside x hx).2 hc0))
      · exact interior_subset (hint ⟨hx, hpos⟩)
  · change (x ∈ interior D.carrier ↔ 0 < σ * c x)
    constructor
    · intro hxi
      by_contra hneg
      push_neg at hneg
      rcases eq_or_lt_of_le hneg with h0 | hneg'
      · have hc0 : c x = 0 := by rcases hσ with rfl | rfl <;> linarith
        exact ((hfront x hx).2 ((hside x hx).2 hc0)).2 hxi
      · exact hext ⟨hx, by linarith⟩ (interior_subset hxi)
    · exact fun hpos => hint ⟨hx, hpos⟩

private lemma trimmed_pair_uniform {d : ℝ} (hd : 0 < d)
    (D : PolygonalDisk) (i : Fin D.n) :
    ∃ δ > 0, ∀ q ∈ D.side i,
      d / 2 ≤ dist q (D.vertex i) →
      d / 2 ≤ dist q (D.vertex (finRotate D.n i)) →
      TrimmedHalfDiskOn D i (ball q δ) := by
  let K : Set Pt := D.side i ∩ {q | d / 2 ≤ dist q (D.vertex i)} ∩
    {q | d / 2 ≤ dist q (D.vertex (finRotate D.n i))}
  have hclosed1 : IsClosed {q : Pt | d / 2 ≤ dist q (D.vertex i)} := by
    exact isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hclosed2 : IsClosed {q : Pt |
      d / 2 ≤ dist q (D.vertex (finRotate D.n i))} := by
    exact isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hK : IsCompact K :=
    ((crown_isCompact_segment (D.vertex i) (D.vertex (finRotate D.n i))).inter_right
      hclosed1).inter_right hclosed2
  have hopen : ∀ q : K, ∃ r > 0,
      IsOpen (ball (q : Pt) r) ∧ TrimmedHalfDiskOn D i (ball (q : Pt) r) := by
    intro q
    have hqside : (q : Pt) ∈ D.side i := q.2.1.1
    have hq1 : d / 2 ≤ dist (q : Pt) (D.vertex i) := q.2.1.2
    have hq2 : d / 2 ≤ dist (q : Pt) (D.vertex (finRotate D.n i)) := q.2.2
    have hne1 : (q : Pt) ≠ D.vertex i := by
      intro heq
      rw [heq, dist_self] at hq1
      linarith
    have hne2 : (q : Pt) ≠ D.vertex (finRotate D.n i) := by
      intro heq
      rw [heq, dist_self] at hq2
      linarith
    have hqopen : (q : Pt) ∈
        openSegment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) :=
      mem_openSegment_of_ne_left_right hne1.symm hne2.symm hqside
    obtain ⟨r, hr, hhalf⟩ := trimmed_local_halfdisk D i hqopen
    exact ⟨r, hr, isOpen_ball, hhalf⟩
  let ρ : K → ℝ := fun q => Classical.choose (hopen q)
  let U : K → Set Pt := fun q => ball (q : Pt) (ρ q)
  have hρ : ∀ q : K, 0 < ρ q := fun q => (Classical.choose_spec (hopen q)).1
  have hUopen : ∀ q, IsOpen (U q) := fun q => by
    dsimp [U]
    exact isOpen_ball
  have hUhalf : ∀ q, TrimmedHalfDiskOn D i (U q) := fun q => by
    dsimp [U, ρ]
    exact (Classical.choose_spec (hopen q)).2.2
  have hcover : K ⊆ ⋃ q, U q := by
    intro q hq
    exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, Metric.mem_ball_self (hρ ⟨q, hq⟩)⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK hUopen hcover
  refine ⟨δ, hδ, ?_⟩
  intro q hq hq1 hq2
  have hqK : q ∈ K := ⟨⟨hq, hq1⟩, hq2⟩
  obtain ⟨z, hz⟩ := hleb q hqK
  exact trimmedHalfDiskOn_mono (hUhalf z) hz

private lemma trimmed_protoset_uniform {d : ℝ} (hd : 0 < d) :
    ∃ η > 0, ∀ (p : P.Form) (i : Fin (P.disk p).n) (q : Pt),
      q ∈ (P.disk p).side i →
      d / 2 ≤ dist q ((P.disk p).vertex i) →
      d / 2 ≤ dist q ((P.disk p).vertex (finRotate _ i)) →
      TrimmedHalfDiskOn (P.disk p) i (ball q η) := by
  let I := Σ p : P.Form, Fin (P.disk p).n
  let pair : ∀ k : I, ∃ δ > 0, ∀ q ∈ (P.disk k.1).side k.2,
      d / 2 ≤ dist q ((P.disk k.1).vertex k.2) →
      d / 2 ≤ dist q ((P.disk k.1).vertex (finRotate _ k.2)) →
      TrimmedHalfDiskOn (P.disk k.1) k.2 (ball q δ) :=
    fun k => trimmed_pair_uniform hd (P.disk k.1) k.2
  let δ : I → ℝ := fun k => Classical.choose (pair k)
  have hδpos : ∀ k, 0 < δ k := fun k => (Classical.choose_spec (pair k)).1
  by_cases hI : (Finset.univ : Finset I).Nonempty
  · let η := Finset.univ.inf' hI δ
    have hη : 0 < η := (Finset.lt_inf'_iff hI).2 fun k _ => hδpos k
    refine ⟨η, hη, ?_⟩
    intro p i q hq hq1 hq2
    let k : I := ⟨p, i⟩
    have hηδ : η ≤ δ k := Finset.inf'_le δ (Finset.mem_univ k)
    have hpair := (Classical.choose_spec (pair k)).2 q hq hq1 hq2
    exact trimmedHalfDiskOn_mono hpair (Metric.ball_subset_ball hηδ)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro p i
    exfalso
    apply hI
    exact ⟨⟨p, i⟩, Finset.mem_univ _⟩

private def TrimmedPlacedHalfDiskOn (A : PlacedTile P)
    (i : Fin (P.disk A.form).n) (U : Set Pt) : Prop :=
  ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ U,
    (x ∈ A.carrier ↔
      0 ≤ σ * trimmedJcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i)) ∧
    (x ∈ interior A.carrier ↔
      0 < σ * trimmedJcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i))

private lemma trimmed_placed_halfdisk {d η : ℝ}
    (hbase : ∀ (p : P.Form) (i : Fin (P.disk p).n) (q : Pt),
      q ∈ (P.disk p).side i →
      d / 2 ≤ dist q ((P.disk p).vertex i) →
      d / 2 ≤ dist q ((P.disk p).vertex (finRotate _ i)) →
      TrimmedHalfDiskOn (P.disk p) i (ball q η))
    (A : PlacedTile P) (i : Fin (P.disk A.form).n) (e : Pt)
    (hei : e ∈ A.side i)
    (h1 : d / 2 ≤ dist e (A.vertex i))
    (h2 : d / 2 ≤ dist e (A.vertex (finRotate _ i))) :
    TrimmedPlacedHalfDiskOn A i (ball e η) := by
  let q : Pt := (-A.anchor) +ᵥ e
  have hqside : q ∈ (P.disk A.form).side i := by
    change e ∈ A.anchor +ᵥ (P.disk A.form).side i at hei
    rw [mem_vadd_set_iff_neg_vadd_mem] at hei
    exact hei
  have hq1 : d / 2 ≤ dist q ((P.disk A.form).vertex i) := by
    calc
      d / 2 ≤ dist e (A.vertex i) := h1
      _ = dist q ((P.disk A.form).vertex i) := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        simp [q, PlacedTile.vertex, vadd_eq_add]
        abel
  have hq2 : d / 2 ≤ dist q ((P.disk A.form).vertex (finRotate _ i)) := by
    calc
      d / 2 ≤ dist e (A.vertex (finRotate _ i)) := h2
      _ = dist q ((P.disk A.form).vertex (finRotate _ i)) := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        simp [q, PlacedTile.vertex, vadd_eq_add]
        abel
  obtain ⟨σ, hσ, hhalf⟩ := hbase A.form i q hqside hq1 hq2
  refine ⟨σ, hσ, ?_⟩
  intro x hx
  let y : Pt := (-A.anchor) +ᵥ x
  have hy : y ∈ ball q η := by
    rw [Metric.mem_ball] at hx ⊢
    simpa [y, q, dist_eq_norm, vadd_eq_add] using hx
  have h := hhalf y hy
  have hcarrier : x ∈ A.carrier ↔ y ∈ (P.disk A.form).carrier := by
    change x ∈ A.anchor +ᵥ (P.disk A.form).carrier ↔ _
    rw [mem_vadd_set_iff_neg_vadd_mem]
  have hinterior : x ∈ interior A.carrier ↔ y ∈ interior (P.disk A.form).carrier := by
    rw [PlacedTile.carrier, interior_vadd]
    exact mem_vadd_set_iff_neg_vadd_mem
  have hdirection : A.vertex (finRotate _ i) - A.vertex i =
      (P.disk A.form).vertex (finRotate _ i) - (P.disk A.form).vertex i := by
    simp [PlacedTile.vertex, vadd_eq_add]
  have hpoint : x - A.vertex i = y - (P.disk A.form).vertex i := by
    simp [PlacedTile.vertex, y, vadd_eq_add]
    abel
  simpa only [hcarrier, hinterior, hdirection, hpoint] using h

private lemma trimmed_tile_side_eq (A : PlacedTile P)
    (i : Fin (P.disk A.form).n) :
    A.side i = segment ℝ (A.vertex i) (A.vertex (finRotate _ i)) := by
  simp [PlacedTile.side, PolygonalDisk.side, PlacedTile.vertex, vadd_segment]

private lemma trimmed_tile_vertex_ne_next (A : PlacedTile P)
    (i : Fin (P.disk A.form).n) :
    A.vertex i ≠ A.vertex (finRotate _ i) := by
  simp only [PlacedTile.vertex, ne_eq, vadd_left_cancel_iff]
  exact trimmed_vertex_ne_next (P.disk A.form) i

private lemma trimmed_jcr_zero_of_mem_segment {a b x : Pt}
    (hx : x ∈ segment ℝ a b) : trimmedJcr (b - a) (x - a) = 0 := by
  obtain ⟨t, -, -, rfl⟩ := crown_mem_segment_iff.1 hx
  rw [add_sub_cancel_left, trimmedJcr_smul_right, trimmedJcr_self, mul_zero]

private lemma trimmed_collinear_directions {a b c f : Pt}
    (hab : a ≠ b) (hcf : c ≠ f)
    (hcol : Collinear ℝ ({a, b, c, f} : Set Pt)) :
    ∃ t : ℝ, t ≠ 0 ∧ f - c = t • (b - a) := by
  rw [collinear_iff_of_mem (show a ∈ ({a, b, c, f} : Set Pt) by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨rb, hb⟩ := hv b (by simp)
  obtain ⟨rc, hc⟩ := hv c (by simp)
  obtain ⟨rf, hf⟩ := hv f (by simp)
  have hrb : rb ≠ 0 := by
    intro hrb
    apply hab
    rw [hb, hrb, zero_smul, zero_vadd]
  let t := (rf - rc) / rb
  have hba : b - a = rb • v := by
    rw [hb]
    simp [vadd_eq_add]
  have hfc : f - c = (rf - rc) • v := by
    rw [hf, hc]
    simp [vadd_eq_add]
    module
  have heq : f - c = t • (b - a) := by
    rw [hfc, hba, smul_smul]
    congr 1
    dsimp [t]
    field_simp
  have ht : t ≠ 0 := by
    intro ht0
    apply hcf
    have : f - c = 0 := by rw [heq, ht0, zero_smul]
    exact (sub_eq_zero.mp this).symm
  exact ⟨t, ht, heq⟩

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
  obtain ⟨η, hη, hbase⟩ := trimmed_protoset_uniform (P := P) hd
  refine ⟨η, hη, ?_⟩
  intro A B hDisj i j e hei hej hCollinear hA1 hA2 hB1 hB2
  obtain ⟨σA, hσA, hA⟩ :=
    trimmed_placed_halfdisk hbase A i e hei hA1 hA2
  obtain ⟨σB, hσB, hB⟩ :=
    trimmed_placed_halfdisk hbase B j e hej hB1 hB2
  let a := A.vertex i
  let b := A.vertex (finRotate _ i)
  let c := B.vertex j
  let f := B.vertex (finRotate _ j)
  have hab : a ≠ b := by
    simpa [a, b] using trimmed_tile_vertex_ne_next A i
  have hcf : c ≠ f := by
    simpa [c, f] using trimmed_tile_vertex_ne_next B j
  obtain ⟨t, ht, hdir⟩ :=
    trimmed_collinear_directions hab hcf hCollinear
  have heA : e ∈ segment ℝ a b := by
    rw [← trimmed_tile_side_eq A i]
    exact hei
  have heB : e ∈ segment ℝ c f := by
    rw [← trimmed_tile_side_eq B j]
    exact hej
  have hcAe : trimmedJcr (b - a) (e - a) = 0 :=
    trimmed_jcr_zero_of_mem_segment heA
  have hcBe : trimmedJcr (f - c) (e - c) = 0 :=
    trimmed_jcr_zero_of_mem_segment heB
  have hcAec : trimmedJcr (b - a) (e - c) = 0 := by
    have hz : t * trimmedJcr (b - a) (e - c) = 0 := by
      rw [← trimmedJcr_smul_left, ← hdir]
      exact hcBe
    exact (mul_eq_zero.mp hz).resolve_left ht
  have hcross : ∀ x : Pt,
      trimmedJcr (f - c) (x - c) = t * trimmedJcr (b - a) (x - a) := by
    intro x
    calc
      trimmedJcr (f - c) (x - c) =
          trimmedJcr (t • (b - a)) ((x - e) + (e - c)) := by
            rw [← hdir]
            congr 2
            abel
      _ = t * (trimmedJcr (b - a) (x - e) +
          trimmedJcr (b - a) (e - c)) := by
            rw [trimmedJcr_smul_left, trimmedJcr_add_right]
      _ = t * trimmedJcr (b - a) (x - e) := by rw [hcAec, add_zero]
      _ = t * (trimmedJcr (b - a) (x - e) +
          trimmedJcr (b - a) (e - a)) := by rw [hcAe, add_zero]
      _ = t * trimmedJcr (b - a) (x - a) := by
            rw [← trimmedJcr_add_right]
            congr 2
            abel
  have hσA2 : σA * σA = 1 := by
    rcases hσA with rfl | rfl <;> norm_num
  have hσBne : σB ≠ 0 := by
    rcases hσB with rfl | rfl <;> norm_num
  have hσAne : σA ≠ 0 := by
    rcases hσA with rfl | rfl <;> norm_num
  let κ := σB * t * σA
  have hκne : κ ≠ 0 := by
    dsimp [κ]
    exact mul_ne_zero (mul_ne_zero hσBne ht) hσAne
  have hcoeff : ∀ x : Pt,
      σB * trimmedJcr (f - c) (x - c) =
        κ * (σA * trimmedJcr (b - a) (x - a)) := by
    intro x
    rw [hcross]
    apply Eq.symm
    calc
      κ * (σA * trimmedJcr (b - a) (x - a)) =
          σB * t * (σA * σA) * trimmedJcr (b - a) (x - a) := by
            simp [κ]
            ring
      _ = σB * (t * trimmedJcr (b - a) (x - a)) := by
            rw [hσA2]
            ring
  have hκneg : κ < 0 := by
    by_contra hn
    have hκnonneg : 0 ≤ κ := le_of_not_gt hn
    have hκpos : 0 < κ := lt_of_le_of_ne hκnonneg hκne.symm
    have hdirpos : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hab.symm)
    let ρ := η / (2 * ‖b - a‖)
    have hρ : 0 < ρ := div_pos hη (by positivity)
    let z := e + (σA * ρ) • trimmedJrot (b - a)
    have hdist : dist e z = ρ * ‖b - a‖ := by
      have hσAabs : |σA| = 1 := by
        rcases hσA with rfl | rfl <;> norm_num
      rw [dist_eq_norm, show e - z = -((σA * ρ) • trimmedJrot (b - a)) by
        dsimp [z]; abel, norm_neg, norm_smul, trimmed_norm_jrot, Real.norm_eq_abs,
        abs_mul, hσAabs, abs_of_pos hρ, one_mul]
    have hρnorm : ρ * ‖b - a‖ = η / 2 := by
      dsimp [ρ]
      field_simp
    have hzball : z ∈ ball e η := by
      rw [Metric.mem_ball, dist_comm, hdist, hρnorm]
      linarith
    have hcAz : trimmedJcr (b - a) (z - a) =
        σA * ρ * ‖b - a‖ ^ 2 := by
      rw [show z - a = (e - a) + (σA * ρ) • trimmedJrot (b - a) by
        dsimp [z]; abel, trimmedJcr_add_right, trimmedJcr_smul_right,
        trimmedJcr_jrot, hcAe, zero_add]
    have hkAz : 0 < σA * trimmedJcr (b - a) (z - a) := by
      rw [hcAz]
      have heq : σA * (σA * ρ * ‖b - a‖ ^ 2) = ρ * ‖b - a‖ ^ 2 := by
        calc
          σA * (σA * ρ * ‖b - a‖ ^ 2) =
              (σA * σA) * ρ * ‖b - a‖ ^ 2 := by ring
          _ = ρ * ‖b - a‖ ^ 2 := by rw [hσA2]; ring
      rw [heq]
      exact mul_pos hρ (sq_pos_of_pos hdirpos)
    have hzA : z ∈ interior A.carrier := (hA z hzball).2.mpr hkAz
    have hkBz : 0 < σB * trimmedJcr (f - c) (z - c) := by
      rw [hcoeff]
      exact mul_pos hκpos hkAz
    have hzB : z ∈ interior B.carrier := (hB z hzball).2.mpr hkBz
    exact Set.disjoint_left.1 hDisj hzA hzB
  intro x hx
  by_cases hxA : 0 ≤ σA * trimmedJcr (b - a) (x - a)
  · left
    exact (hA x hx).1.mpr hxA
  · right
    apply (hB x hx).1.mpr
    rw [hcoeff]
    exact (mul_pos_of_neg_of_neg hκneg (lt_of_not_ge hxA)).le

/-! ## `lem:exterior-excursion` -/

/-- Step 1 of the blueprint proof of `noShortExteriorExcursion_step1_excursion`:
failure of convexity supplies a segment with endpoints in the set and an open
interior point outside it. -/
private lemma noShortExteriorExcursion_step1_excursion_step1_witness
    {S : Set Pt} (hS : ¬ Convex ℝ S) :
    ∃ x y z : Pt, x ∈ S ∧ y ∈ S ∧ z ∈ openSegment ℝ x y ∧ z ∉ S := by
  rw [convex_iff_segment_subset] at hS
  push_neg at hS
  obtain ⟨x, hx, y, hy, hseg⟩ := hS
  rw [not_subset] at hseg
  obtain ⟨z, hz, hznot⟩ := hseg
  exact ⟨x, y, z, hx, hy,
    mem_openSegment_of_ne_left_right (by aesop) (by aesop) hz, hznot⟩

/-- The component of an open subset of a real interval containing an interior
point is bounded by points of the complement (possibly the interval's own
endpoints). -/
private lemma noShortExteriorExcursion_step1_excursion_step2_interval
    {T : Set ℝ} (hTopen : IsOpen T) {a b c : ℝ}
    (ha : a ∉ T) (hb : b ∉ T) (hc : c ∈ T) (hac : a < c) (hcb : c < b) :
    ∃ p q : ℝ, a ≤ p ∧ p < c ∧ c < q ∧ q ≤ b ∧
      p ∉ T ∧ q ∉ T ∧ Ioo p q ⊆ T ∧ p ∈ closure T ∧ q ∈ closure T := by
  let A : Set ℝ := Icc a c ∩ Tᶜ
  have hAcl : IsClosed A := isClosed_Icc.inter hTopen.isClosed_compl
  have haA : a ∈ A := ⟨⟨le_rfl, hac.le⟩, ha⟩
  have hAbdd : BddAbove A := ⟨c, fun _ hr => hr.1.2⟩
  let p := sSup A
  have hpA : p ∈ A := by
    exact hAcl.csSup_mem ⟨a, haA⟩ hAbdd
  have hap : a ≤ p := hpA.1.1
  have hpc : p < c := lt_of_le_of_ne hpA.1.2 fun h => hpA.2 (h ▸ hc)
  have hpcT : Ioo p c ⊆ T := by
    intro r hr
    by_contra hrT
    have hrA : r ∈ A :=
      ⟨⟨hap.trans hr.1.le, hr.2.le⟩, hrT⟩
    exact (not_le_of_gt hr.1) (le_csSup hAbdd hrA)
  have hpcl : p ∈ closure T := by
    apply closure_mono hpcT
    rw [closure_Ioo hpc.ne]
    exact left_mem_Icc.mpr hpc.le
  let B : Set ℝ := Icc c b ∩ Tᶜ
  have hBcl : IsClosed B := isClosed_Icc.inter hTopen.isClosed_compl
  have hbB : b ∈ B := ⟨⟨hcb.le, le_rfl⟩, hb⟩
  have hBbdd : BddBelow B := ⟨c, fun _ hr => hr.1.1⟩
  let q := sInf B
  have hqB : q ∈ B := by
    exact hBcl.csInf_mem ⟨b, hbB⟩ hBbdd
  have hqb : q ≤ b := hqB.1.2
  have hcq : c < q := lt_of_le_of_ne hqB.1.1 fun h => hqB.2 (h.symm ▸ hc)
  have hcqT : Ioo c q ⊆ T := by
    intro r hr
    by_contra hrT
    have hrB : r ∈ B :=
      ⟨⟨hr.1.le, hr.2.le.trans hqb⟩, hrT⟩
    exact (not_le_of_gt hr.2) (csInf_le hBbdd hrB)
  have hqcl : q ∈ closure T := by
    apply closure_mono hcqT
    rw [closure_Ioo hcq.ne]
    exact right_mem_Icc.mpr hcq.le
  refine ⟨p, q, hap, hpc, hcq, hqb, hpA.2, hqB.2, ?_, hpcl, hqcl⟩
  intro r hr
  rcases lt_trichotomy r c with hrc | rfl | hcr
  · exact hpcT ⟨hr.1, hrc⟩
  · exact hc
  · exact hcqT ⟨hcr, hr.2⟩

/-- Step 2 of the blueprint proof of `noShortExteriorExcursion_step1_excursion`:
for a closed set, a segment whose endpoints lie in the set and which has an
interior point outside it contains a nonempty open exterior excursion between
two distinct frontier points. -/
private lemma noShortExteriorExcursion_step1_excursion_step2_first_excursion
    {S : Set Pt} (hSclosed : IsClosed S) {x y z : Pt}
    (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ openSegment ℝ x y) (hzout : z ∉ S) :
    ∃ E F : Pt, E ∈ segment ℝ x y ∧ F ∈ segment ℝ x y ∧ E ≠ F ∧
      E ∈ frontier S ∧ F ∈ frontier S ∧
      openSegment ℝ E F ⊆ Sᶜ := by
  obtain ⟨t, ht0, ht1, hzt⟩ := crown_mem_openSegment_iff.mp hz
  let f : ℝ → Pt := fun s => x + s • (y - x)
  let T : Set ℝ := f ⁻¹' Sᶜ
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hTopen : IsOpen T := hSclosed.isOpen_compl.preimage hcont
  have h0T : (0 : ℝ) ∉ T := by
    simpa [T, f] using hx
  have h1T : (1 : ℝ) ∉ T := by
    simpa [T, f] using hy
  have htT : t ∈ T := by
    have hft : f t = z := by simpa [f] using hzt.symm
    simpa [T, hft] using hzout
  obtain ⟨p, q, hp0, hpt, htq, hq1, hpT, hqT, hpqT, hpcl, hqcl⟩ :=
    noShortExteriorExcursion_step1_excursion_step2_interval
      hTopen h0T h1T htT ht0 ht1
  let E : Pt := f p
  let F : Pt := f q
  have hxy : x ≠ y := by
    intro hxy
    subst y
    have : z = x := by
      rw [hzt]
      simp
    exact hzout (this ▸ hx)
  have hEseg : E ∈ segment ℝ x y := by
    rw [crown_mem_segment_iff]
    exact ⟨p, hp0, (hpt.trans ht1).le, rfl⟩
  have hFseg : F ∈ segment ℝ x y := by
    rw [crown_mem_segment_iff]
    exact ⟨q, (ht0.trans htq).le, hq1, rfl⟩
  have hEF : E ≠ F := by
    intro hEF
    have hpq : p = q := by
      apply crown_smul_cancel (sub_ne_zero.mpr hxy.symm)
      have := congrArg (fun w : Pt => w - x) hEF
      simpa [E, F, f] using this
    linarith
  have hES : E ∈ S := by
    simpa [E, T] using hpT
  have hFS : F ∈ S := by
    simpa [F, T] using hqT
  have hmap : MapsTo f T Sᶜ := fun _ hs => hs
  have hEcl : E ∈ closure Sᶜ := by
    simpa [E] using map_mem_closure hcont hpcl hmap
  have hFcl : F ∈ closure Sᶜ := by
    simpa [F] using map_mem_closure hcont hqcl hmap
  have hEfront : E ∈ frontier S := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hES, hEcl⟩
  have hFfront : F ∈ frontier S := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hFS, hFcl⟩
  refine ⟨E, F, hEseg, hFseg, hEF, hEfront, hFfront, ?_⟩
  intro w hw
  obtain ⟨u, hu0, hu1, huw⟩ := crown_mem_openSegment_iff.mp hw
  have hwu : w = f (p + u * (q - p)) := by
    rw [huw]
    dsimp [E, F, f]
    module
  rw [hwu]
  exact hpqT ⟨by nlinarith, by nlinarith⟩

/-- Step 1 of the blueprint proof of `noShortExteriorExcursion`: a failure of
convexity produces two distinct points of `H` on the macro boundary whose open
chord is an exterior excursion. -/
private theorem noShortExteriorExcursion_step1_excursion
    (M : MacroPatch P) {H : Set Pt} (hH : Convex ℝ H)
    (hnconv : ¬ Convex ℝ (H ∩ support M.tiles)) :
    ∃ E F : Pt, E ∈ H ∧ F ∈ H ∧ E ≠ F ∧
      E ∈ frontier (support M.tiles) ∧ F ∈ frontier (support M.tiles) ∧
      openSegment ℝ E F ⊆ (support M.tiles)ᶜ := by
  obtain ⟨x, y, z, hx, hy, hz, hzout⟩ :=
    noShortExteriorExcursion_step1_excursion_step1_witness hnconv
  have hzH : z ∈ H :=
    hH.segment_subset hx.1 hy.1 (openSegment_subset_segment ℝ x y hz)
  have hzout' : z ∉ support M.tiles := by
    intro hzsupport
    exact hzout ⟨hzH, hzsupport⟩
  obtain ⟨E, F, hEx, hFx, hEF, hEfront, hFfront, hout⟩ :=
    noShortExteriorExcursion_step1_excursion_step2_first_excursion
      (S := support M.tiles) (macro_support_closed M) hx.2 hy.2 hz hzout'
  refine ⟨E, F, ?_, ?_, hEF, hEfront, hFfront, hout⟩
  · exact hH.segment_subset hx.1 hy.1 hEx
  · exact hH.segment_subset hx.1 hy.1 hFx

/-- Auxiliary lemma for `noShortExteriorExcursion_step2_classify`: a point of the
macro frontier corresponds to a point of the root frontier under `M.map`. -/
private lemma noShortExteriorExcursion_step2_classify_aux1 (M : MacroPatch P) (p : Pt) :
    p ∈ frontier (P.disk M.root).carrier ↔ M.map p ∈ frontier (support M.tiles) := by
  have hs : M.θ ^ M.j ≠ 0 := (pow_pos (lt_trans zero_lt_one M.one_lt) _).ne'
  have hcl : closure (support M.tiles) =
      M.offset +ᵥ (M.θ ^ M.j) • closure (P.disk M.root).carrier := by
    rw [M.support_eq, closure_vadd, closure_smul₀ (M.θ ^ M.j) (P.disk M.root).carrier]
  have hin : interior (support M.tiles) =
      M.offset +ᵥ (M.θ ^ M.j) • interior (P.disk M.root).carrier := by
    rw [M.support_eq, interior_vadd, interior_smul₀ hs]
  have hfr : frontier (support M.tiles) =
      M.offset +ᵥ (M.θ ^ M.j) • frontier (P.disk M.root).carrier := by
    simp only [frontier]
    rw [hcl, hin, ← Set.vadd_set_sdiff, ← Set.smul_set_sdiff₀ hs]
  rw [hfr, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
    Set.mem_smul_set_iff_inv_smul_mem₀ hs]
  simp only [MacroPatch.map, neg_add_cancel_left, inv_smul_smul₀ hs]

/-- Auxiliary lemma for `noShortExteriorExcursion_step2_classify`: every point of the
macro frontier is `M.map` of a point of the root frontier. -/
private lemma noShortExteriorExcursion_step2_classify_aux2 (M : MacroPatch P) {x : Pt}
    (hx : x ∈ frontier (support M.tiles)) :
    ∃ v, v ∈ frontier (P.disk M.root).carrier ∧ M.map v = x := by
  have hs : M.θ ^ M.j ≠ 0 := (pow_pos (lt_trans zero_lt_one M.one_lt) _).ne'
  have hmap : M.map ((M.θ ^ M.j)⁻¹ • (x - M.offset)) = x := by
    simp only [MacroPatch.map, smul_smul, mul_inv_cancel₀ hs, one_smul]
    abel
  exact ⟨(M.θ ^ M.j)⁻¹ • (x - M.offset),
    (noShortExteriorExcursion_step2_classify_aux1 M _).mpr (by rw [hmap]; exact hx), hmap⟩

/-- Auxiliary lemma for `noShortExteriorExcursion_step2_classify`: `M.map` sends segments
to segments. -/
private lemma noShortExteriorExcursion_step2_classify_aux3 (M : MacroPatch P) {x y z : Pt}
    (hz : z ∈ segment ℝ x y) : M.map z ∈ segment ℝ (M.map x) (M.map y) := by
  rw [crown_mem_segment_iff] at hz ⊢
  obtain ⟨t, ht0, ht1, rfl⟩ := hz
  exact ⟨t, ht0, ht1, by simp only [MacroPatch.map]; module⟩

/-- Auxiliary lemma for `noShortExteriorExcursion_step2_classify`: `M.map` sends open
segments to open segments. -/
private lemma noShortExteriorExcursion_step2_classify_aux4 (M : MacroPatch P) {x y z : Pt}
    (hz : z ∈ openSegment ℝ x y) : M.map z ∈ openSegment ℝ (M.map x) (M.map y) := by
  rw [crown_mem_openSegment_iff] at hz ⊢
  obtain ⟨t, ht0, ht1, rfl⟩ := hz
  exact ⟨t, ht0, ht1, by simp only [MacroPatch.map]; module⟩

/-- Auxiliary lemma for `noShortExteriorExcursion_step2_classify`: `M.map` is injective. -/
private lemma noShortExteriorExcursion_step2_classify_aux5 (M : MacroPatch P) :
    Function.Injective M.map := by
  intro x y hxy
  have hs : M.θ ^ M.j ≠ 0 := (pow_pos (lt_trans zero_lt_one M.one_lt) _).ne'
  apply smul_right_injective Pt hs
  change M.offset + (M.θ ^ M.j) • x = M.offset + (M.θ ^ M.j) • y at hxy
  exact add_left_cancel hxy

/-- Auxiliary lemma for `noShortExteriorExcursion_step2_classify`: `M.map`, a positive
homothety composed with a translation, preserves angles. -/
private lemma noShortExteriorExcursion_step2_classify_aux6 (M : MacroPatch P) (x y z : Pt) :
    EuclideanGeometry.angle (M.map x) (M.map y) (M.map z) = EuclideanGeometry.angle x y z := by
  have hc : 0 < M.θ ^ M.j := pow_pos (lt_trans zero_lt_one M.one_lt) _
  show InnerProductGeometry.angle (M.map x - M.map y) (M.map z - M.map y) =
      InnerProductGeometry.angle (x - y) (z - y)
  have h1 : M.map x - M.map y = (M.θ ^ M.j) • (x - y) := by
    simp only [MacroPatch.map]; module
  have h2 : M.map z - M.map y = (M.θ ^ M.j) • (z - y) := by
    simp only [MacroPatch.map]; module
  rw [h1, h2, InnerProductGeometry.angle_smul_left_of_pos _ _ hc,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hc]

/-- Step 1 of the blueprint proof of `noShortExteriorExcursion_step2_classify`: if two
geometric edges of a polygonal disk share a genuine corner `q`, and the open chord
between a relative-interior point of each edge lies entirely outside the disk, then
`q` is a reflex corner of the two edges (the convex wedge between them is exterior). -/
private theorem noShortExteriorExcursion_step2_classify_step1_reflexCorner
    (D : PolygonalDisk) {q a b v z : Pt}
    (hqa : D.IsGeometricEdge q a) (hqb : D.IsGeometricEdge q b) (hab : a ≠ b)
    (hv : v ∈ openSegment ℝ q a) (hz : z ∈ openSegment ℝ q b)
    (hout : ∀ p ∈ openSegment ℝ v z, p ∉ D.carrier) :
    D.IsReflexCorner q a b := by
  sorry

/-- Step 2 of the blueprint proof of `noShortExteriorExcursion`: an exterior
chord on the finite macro boundary either uses nonadjacent geometric edges or
crosses the exterior wedge at adjacent edges.  In the latter case the common
genuine corner is a child vertex and the endpoint angle is at least the root
separation angle. -/
private theorem noShortExteriorExcursion_step2_classify
    (R : RootSeparation P) (M : MacroPatch P) {E F : Pt} (hEF : E ≠ F)
    (hEfront : E ∈ frontier (support M.tiles))
    (hFfront : F ∈ frontier (support M.tiles))
    (hEnv : ∀ v, IsVertexOf M.tiles v → E ≠ v)
    (hFnv : ∀ v, IsVertexOf M.tiles v → F ≠ v)
    (hout : openSegment ℝ E F ⊆ (support M.tiles)ᶜ) :
    (∃ a b a' b' : Pt,
      (a, b) ∈ geometricMacroBoundary M ∧
      (a', b') ∈ geometricMacroBoundary M ∧
      Disjoint ({a, b} : Set Pt) {a', b'} ∧
      E ∈ segment ℝ a b ∧ F ∈ segment ℝ a' b') ∨
    (∃ q a b : Pt,
      (q, a) ∈ geometricMacroBoundary M ∧
      (q, b) ∈ geometricMacroBoundary M ∧ a ≠ b ∧
      E ∈ segment ℝ q a ∧ F ∈ segment ℝ q b ∧
      IsVertexOf M.tiles q ∧ R.μ ≤ EuclideanGeometry.angle E q F) := by
  have _ := hEF
  set D := P.disk M.root with hD
  have hDcl : IsClosed D.carrier := D.compact.isClosed
  obtain ⟨v', hv'F, hv'E⟩ := noShortExteriorExcursion_step2_classify_aux2 M hEfront
  obtain ⟨z', hz'F, hz'E⟩ := noShortExteriorExcursion_step2_classify_aux2 M hFfront
  have hv'nc : ¬ D.IsGenuineCorner v' := by
    intro hv'
    exact hEnv E (macrocornerIsChildVertex M ⟨v', hv', hv'E⟩) rfl
  have hz'nc : ¬ D.IsGenuineCorner z' := by
    intro hz'
    exact hFnv F (macrocornerIsChildVertex M ⟨z', hz', hz'E⟩) rfl
  obtain ⟨a, b, hab_edge, hv'ab⟩ := rcb_frontier_mem_geometricEdge D hv'F
  obtain ⟨a', b', hab'_edge, hz'ab'⟩ := rcb_frontier_mem_geometricEdge D hz'F
  have hv'a : v' ≠ a := by intro h; apply hv'nc; rw [h]; exact hab_edge.1
  have hv'b : v' ≠ b := by intro h; apply hv'nc; rw [h]; exact hab_edge.2.1
  have hz'a' : z' ≠ a' := by intro h; apply hz'nc; rw [h]; exact hab'_edge.1
  have hz'b' : z' ≠ b' := by intro h; apply hz'nc; rw [h]; exact hab'_edge.2.1
  have hv'o : v' ∈ openSegment ℝ a b :=
    mem_openSegment_of_ne_left_right (Ne.symm hv'a) (Ne.symm hv'b) hv'ab
  have hz'o : z' ∈ openSegment ℝ a' b' :=
    mem_openSegment_of_ne_left_right (Ne.symm hz'a') (Ne.symm hz'b') hz'ab'
  have hout_root : ∀ p ∈ openSegment ℝ v' z', p ∉ D.carrier := by
    intro p hp hpD
    have hpE : M.map p ∈ openSegment ℝ E F := by
      rw [← hv'E, ← hz'E]
      exact noShortExteriorExcursion_step2_classify_aux4 M hp
    have hpS : M.map p ∈ support M.tiles := (rcb_mem_disk_iff M p).mp hpD
    exact hout hpE hpS
  by_cases hdisj : Disjoint ({a, b} : Set Pt) {a', b'}
  · left
    refine ⟨M.map a, M.map b, M.map a', M.map b', ⟨a, b, hab_edge, rfl⟩,
      ⟨a', b', hab'_edge, rfl⟩, ?_, ?_, ?_⟩
    · rw [← Set.image_pair M.map a b, ← Set.image_pair M.map a' b']
      exact (Set.disjoint_image_iff (noShortExteriorExcursion_step2_classify_aux5 M)).mpr hdisj
    · rw [← hv'E]; exact noShortExteriorExcursion_step2_classify_aux3 M hv'ab
    · rw [← hz'E]; exact noShortExteriorExcursion_step2_classify_aux3 M hz'ab'
  · right
    rw [Set.not_disjoint_iff] at hdisj
    obtain ⟨u, hu1, hu2⟩ := hdisj
    simp only [mem_insert_iff, mem_singleton_iff] at hu1 hu2
    obtain ⟨p0, hup0, hv'up0⟩ : ∃ p0, D.IsGeometricEdge u p0 ∧ v' ∈ openSegment ℝ u p0 := by
      rcases hu1 with h | h
      · refine ⟨b, by rw [h]; exact hab_edge, by rw [h]; exact hv'o⟩
      · refine ⟨a, by rw [h]; exact rcb_geometricEdge_symm hab_edge,
          by rw [h, openSegment_symm]; exact hv'o⟩
    obtain ⟨r0, hur0, hz'ur0⟩ : ∃ r0, D.IsGeometricEdge u r0 ∧ z' ∈ openSegment ℝ u r0 := by
      rcases hu2 with h | h
      · refine ⟨b', by rw [h]; exact hab'_edge, by rw [h]; exact hz'o⟩
      · refine ⟨a', by rw [h]; exact rcb_geometricEdge_symm hab'_edge,
          by rw [h, openSegment_symm]; exact hz'o⟩
    by_cases hpr : p0 = r0
    · exfalso
      subst hpr
      have hmidopen : v' + (1 / 2 : ℝ) • (z' - v') ∈ openSegment ℝ v' z' :=
        crown_mem_openSegment_iff.mpr ⟨1 / 2, by norm_num, by norm_num, rfl⟩
      have hmidseg : v' + (1 / 2 : ℝ) • (z' - v') ∈ segment ℝ u p0 := by
        apply (convex_segment u p0).segment_subset
          (openSegment_subset_segment ℝ u p0 hv'up0)
          (openSegment_subset_segment ℝ u p0 hz'ur0)
        exact crown_mem_segment_iff.mpr ⟨1 / 2, by norm_num, by norm_num, rfl⟩
      have hmidcarrier : v' + (1 / 2 : ℝ) • (z' - v') ∈ D.carrier :=
        (hup0.2.2.2.trans hDcl.frontier_subset) hmidseg
      exact hout_root _ hmidopen hmidcarrier
    · have hrefl : D.IsReflexCorner u p0 r0 :=
        noShortExteriorExcursion_step2_classify_step1_reflexCorner D hup0 hur0 hpr hv'up0
          hz'ur0 hout_root
      have hμ : R.μ ≤ EuclideanGeometry.angle p0 u r0 := R.μ_le_reflex M.root u p0 r0 hrefl
      obtain ⟨t1, ht10, ht11, hv'eq⟩ := crown_mem_openSegment_iff.mp hv'up0
      obtain ⟨t2, ht20, ht21, hz'eq⟩ := crown_mem_openSegment_iff.mp hz'ur0
      have hang : R.μ ≤ EuclideanGeometry.angle v' u z' := by
        show R.μ ≤ InnerProductGeometry.angle (v' - u) (z' - u)
        rw [hv'eq, hz'eq, add_sub_cancel_left, add_sub_cancel_left,
          InnerProductGeometry.angle_smul_left_of_pos _ _ ht10,
          InnerProductGeometry.angle_smul_right_of_pos _ _ ht20]
        exact hμ
      refine ⟨M.map u, M.map p0, M.map r0, ⟨u, p0, hup0, rfl⟩, ⟨u, r0, hur0, rfl⟩,
        fun h => hpr (noShortExteriorExcursion_step2_classify_aux5 M h), ?_, ?_,
        macrocornerIsChildVertex M ⟨u, hup0.1, rfl⟩, ?_⟩
      · rw [← hv'E]
        exact noShortExteriorExcursion_step2_classify_aux3 M
          (openSegment_subset_segment ℝ u p0 hv'up0)
      · rw [← hz'E]
        exact noShortExteriorExcursion_step2_classify_aux3 M
          (openSegment_subset_segment ℝ u r0 hz'ur0)
      · rw [← hv'E, ← hz'E, noShortExteriorExcursion_step2_classify_aux6]
        exact hang

/-- Step 3 of the blueprint proof of `noShortExteriorExcursion`: points on
nonadjacent macro edges are separated by the root constant `λ`. -/
private theorem noShortExteriorExcursion_step3_nonadjacent
    (R : RootSeparation P) (M : MacroPatch P) {E F a b a' b' : Pt}
    (hEedge : (a, b) ∈ geometricMacroBoundary M)
    (hFedge : (a', b') ∈ geometricMacroBoundary M)
    (hdisj : Disjoint ({a, b} : Set Pt) {a', b'})
    (hEseg : E ∈ segment ℝ a b) (hFseg : F ∈ segment ℝ a' b') :
    R.lam ≤ dist E F := by
  rcases hEedge with ⟨x, y, hxy, hEedge⟩
  rcases hFedge with ⟨x', y', hx'y', hFedge⟩
  have ha : a = M.map x := congrArg Prod.fst hEedge
  have hb : b = M.map y := congrArg Prod.snd hEedge
  have ha' : a' = M.map x' := congrArg Prod.fst hFedge
  have hb' : b' = M.map y' := congrArg Prod.snd hFedge
  subst a
  subst b
  subst a'
  subst b'
  have hdisj' : Disjoint ({x, y} : Set Pt) {x', y'} := by
    rw [Set.disjoint_left] at hdisj ⊢
    intro z hz hz'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz hz'
    rcases hz with rfl | rfl <;> rcases hz' with rfl | rfl
    all_goals apply hdisj (a := M.map z) <;> simp
  rw [segment_eq_image'] at hEseg hFseg
  obtain ⟨t, ht, hE⟩ := hEseg
  obtain ⟨t', ht', hF⟩ := hFseg
  let z := x + t • (y - x)
  let z' := x' + t' • (y' - x')
  have hz : z ∈ segment ℝ x y := by
    exact crown_mem_segment_iff.mpr ⟨t, ht.1, ht.2, rfl⟩
  have hz' : z' ∈ segment ℝ x' y' := by
    exact crown_mem_segment_iff.mpr ⟨t', ht'.1, ht'.2, rfl⟩
  have hEz : M.map z = E := by
    calc
      M.map z = M.map x + t • (M.map y - M.map x) := by
        dsimp [z, MacroPatch.map]
        module
      _ = E := hE
  have hFz : M.map z' = F := by
    calc
      M.map z' = M.map x' + t' • (M.map y' - M.map x') := by
        dsimp [z', MacroPatch.map]
        module
      _ = F := hF
  have hroot := R.lam_le M.root x y x' y' hxy hx'y' hdisj' z hz z' hz'
  have hc : 1 ≤ M.θ ^ M.j := one_le_pow₀ M.one_lt.le
  have hdist : dist E F = (M.θ ^ M.j) * dist z z' := by
    rw [← hEz, ← hFz, rcb_map_dist]
  rw [hdist]
  have hscale : dist z z' ≤ (M.θ ^ M.j) * dist z z' := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hc (dist_nonneg : 0 ≤ dist z z')
  exact hroot.trans hscale

/-- Step 4 of the blueprint proof of `noShortExteriorExcursion`: two points
at distance at least `d/2` from a common vertex and separated by an angle at
least `μ` are at mutual distance at least `d sin (μ/2)`. -/
private theorem noShortExteriorExcursion_step4_adjacent_metric
    {E F q : Pt} {d μ : ℝ} (hd : 0 < d) (hμ : 0 < μ)
    (hμπ : μ ≤ Real.pi / 2) (hE : d / 2 ≤ dist E q)
    (hF : d / 2 ≤ dist F q)
    (hangle : μ ≤ EuclideanGeometry.angle E q F) :
    d * Real.sin (μ / 2) ≤ dist E F := by
  let A : Pt := E - q
  let B : Pt := F - q
  let θ : ℝ := InnerProductGeometry.angle A B
  let a : ℝ := ‖A‖
  let b : ℝ := ‖B‖
  have hA : d / 2 ≤ a := by
    dsimp [a, A]
    simpa [dist_eq_norm] using hE
  have hB : d / 2 ≤ b := by
    dsimp [b, B]
    simpa [dist_eq_norm] using hF
  have hθ : μ ≤ θ := by
    dsimp [θ, A, B]
    simpa [EuclideanGeometry.angle] using hangle
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    exact InnerProductGeometry.angle_nonneg _ _
  have hθpi : θ ≤ Real.pi := by
    dsimp [θ]
    exact InnerProductGeometry.angle_le_pi _ _
  have hcosμ1 : Real.cos μ ≤ 1 := Real.cos_le_one μ
  have hcos : Real.cos θ ≤ Real.cos μ := by
    apply (Real.strictAntiOn_cos.le_iff_ge ⟨hθ0, hθpi⟩
      ⟨hμ.le, by linarith [Real.pi_pos]⟩).2
    exact hθ
  have hinner : inner ℝ A B = Real.cos θ * (a * b) := by
    dsimp [θ, a, b]
    exact (InnerProductGeometry.cos_angle_mul_norm_mul_norm A B).symm
  have hsq : ‖A - B‖ ^ 2 = a ^ 2 - 2 * (Real.cos θ * (a * b)) + b ^ 2 := by
    rw [norm_sub_sq_real A B, hinner]
  have hhalf : Real.sin (μ / 2) ^ 2 = (1 - Real.cos μ) / 2 := by
    have hh := Real.sin_sq_eq_half_sub (μ / 2)
    rw [show 2 * (μ / 2) = μ by ring] at hh
    nlinarith [hh]
  have hs : 0 ≤ Real.sin (μ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
    (by linarith [Real.pi_pos])
  have hquad : d ^ 2 * (1 - Real.cos μ) / 2 ≤
      a ^ 2 + b ^ 2 - 2 * a * b * Real.cos μ := by
    let x := a - d / 2
    let y := b - d / 2
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hxy : 0 ≤ x * y := mul_nonneg hx hy
    have hc : 0 ≤ 1 - Real.cos μ := sub_nonneg.mpr hcosμ1
    have hfirst : 0 ≤ (x - y) ^ 2 + 2 * (1 - Real.cos μ) * (x * y) := by
      exact add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hc) hxy)
    have hsecond : 0 ≤ d * (1 - Real.cos μ) * (x + y) := by
      exact mul_nonneg (mul_nonneg hd.le hc) (add_nonneg hx hy)
    dsimp [x, y] at hfirst hsecond ⊢
    nlinarith
  have hab : 0 ≤ a * b := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsqbound : (d * Real.sin (μ / 2)) ^ 2 ≤ ‖A - B‖ ^ 2 := by
    rw [hsq]
    nlinarith [hquad, hhalf, mul_nonneg hab (sub_nonneg.mpr hcos)]
  have hnorm : d * Real.sin (μ / 2) ≤ ‖A - B‖ :=
    (pow_le_pow_iff_left₀ (mul_nonneg hd.le hs) (norm_nonneg _) two_ne_zero).mp hsqbound
  have hdist : ‖A - B‖ = dist E F := by
    dsimp [A, B]
    rw [dist_eq_norm]
    congr 1
    abel
  rwa [hdist] at hnorm

/-- `lem:exterior-excursion`: a bounded convex set `H` of diameter less than
`min {λ, d sin(μ_*/2)}` all of whose points are at distance `≥ d/2` from
every child vertex meets the macro polygon in a convex set. -/
theorem noShortExteriorExcursion (R : RootSeparation P) {d : ℝ} (hd : 0 < d)
    (M : MacroPatch P) {H : Set Pt} (hH : Convex ℝ H) (hb : Bornology.IsBounded H)
    (hdiam : diam H < min R.lam (d * Real.sin (R.μ / 2)))
    (hfar : ∀ x ∈ H, ∀ v, IsVertexOf M.tiles v → d / 2 ≤ dist x v) :
    Convex ℝ (H ∩ support M.tiles) := by
  by_contra hnconv
  obtain ⟨E, F, hEH, hFH, hEF, hEfront, hFfront, hout⟩ :=
    noShortExteriorExcursion_step1_excursion M hH hnconv
  have hEnv : ∀ v, IsVertexOf M.tiles v → E ≠ v := by
    intro v hv hEv
    have h := hfar E hEH v hv
    rw [hEv, dist_self] at h
    linarith
  have hFnv : ∀ v, IsVertexOf M.tiles v → F ≠ v := by
    intro v hv hFv
    have h := hfar F hFH v hv
    rw [hFv, dist_self] at h
    linarith
  obtain hcase := noShortExteriorExcursion_step2_classify R M hEF hEfront hFfront
    hEnv hFnv hout
  have hEFdiam : dist E F ≤ diam H := dist_le_diam_of_mem hb hEH hFH
  rcases hcase with hnon | hadj
  · obtain ⟨a, b, a', b', hEedge, hFedge, hdisj, hEseg, hFseg⟩ := hnon
    have hlam := noShortExteriorExcursion_step3_nonadjacent R M hEedge hFedge
      hdisj hEseg hFseg
    have hltlam : diam H < R.lam := lt_of_lt_of_le hdiam (min_le_left _ _)
    linarith
  · obtain ⟨q, a, b, -, -, -, -, -, hqv, hangle⟩ := hadj
    have hEq : d / 2 ≤ dist E q := hfar E hEH q hqv
    have hFq : d / 2 ≤ dist F q := hfar F hFH q hqv
    have hmetric := noShortExteriorExcursion_step4_adjacent_metric hd R.μ_pos R.μ_le
      hEq hFq hangle
    have hltshort : diam H < d * Real.sin (R.μ / 2) :=
      lt_of_lt_of_le hdiam (min_le_right _ _)
    linarith

/-! ## `lem:crown-convexification` -/

/-- `lem:crown-convexification`: the closed convex hull has the same diameter
(in particular, no greater). -/
theorem closedConvexHullDiameter (S : Set Pt) :
    diam (closedConvexHull ℝ S) = diam S := by
  rw [closedConvexHull_eq_closure_convexHull, Metric.diam_closure, convexHull_diam]

/-! ## `lem:crown-cover-plane`, `lem:crown-cover-supertile` -/

/-- Auxiliary step of the blueprint proof of
`uniformCrownCoverPlane_step1_close_step1_crown_covers_ball`: at a vertex `v` of a plane
tiling, the local cones of the tiles containing `v` (the full crown there) cover the whole
plane. -/
private lemma uniformCrownCoverPlane_step1_close_step1_crown_covers_ball_aux1
    (T : PlaneTiling P) {v : Pt} (hv : IsVertexOf T.tiles v) :
    Omega (crown T.tiles v) v = Set.univ := by
  obtain ⟨A₀, hA₀T, hvA₀⟩ := hv
  have hvA₀c : v ∈ A₀.carrier := gap_vertex_mem_carrier A₀ hvA₀
  have hA₀crown : A₀ ∈ crown T.tiles v := ⟨hA₀T, hvA₀c⟩
  have hS_fin : {A ∈ T.tiles | (A.carrier ∩ closedBall v 1).Nonempty}.Finite :=
    T.locallyFinite (isCompact_closedBall v 1)
  obtain ⟨ρ₀, hρ₀, hprop⟩ :=
    gap_near_vertex {A ∈ T.tiles | (A.carrier ∩ closedBall v 1).Nonempty} hS_fin v
  have hd : 0 < min ρ₀ 1 := lt_min hρ₀ one_pos
  have hball_sub : ball v (min ρ₀ 1) ⊆ Omega (crown T.tiles v) v := by
    intro y hy
    have hyT : y ∈ support T.tiles := by rw [T.cover]; exact mem_univ y
    rw [support, mem_iUnion₂] at hyT
    obtain ⟨A, hAT, hyA⟩ := hyT
    have hy1 : y ∈ closedBall v 1 :=
      ball_subset_closedBall (ball_subset_ball (min_le_right ρ₀ 1) hy)
    have hAmem : A ∈ {A ∈ T.tiles | (A.carrier ∩ closedBall v 1).Nonempty} :=
      ⟨hAT, ⟨y, hyA, hy1⟩⟩
    have hyS : y ∈ support {A ∈ T.tiles | (A.carrier ∩ closedBall v 1).Nonempty} := by
      rw [support, mem_iUnion₂]
      exact ⟨A, hAmem, hyA⟩
    have hyb : y ∈ ball v ρ₀ := ball_subset_ball (min_le_left ρ₀ 1) hy
    obtain ⟨A', hA'crown, hyA'⟩ := hprop y hyb hyS
    rw [Omega, mem_iUnion₂]
    exact ⟨A', ⟨hA'crown.1.1, hA'crown.2⟩, hyA'⟩
  apply Set.eq_univ_of_forall
  intro z
  by_cases hzv : z = v
  · subst hzv
    rw [Omega, mem_iUnion₂]
    refine ⟨A₀, hA₀crown, 1, one_pos, fun t _ => ?_⟩
    simpa using hvA₀c
  · have hzvpos : 0 < dist z v := dist_pos.mpr hzv
    have hzvne : dist z v ≠ 0 := hzvpos.ne'
    have hc : (0 : ℝ) < min ρ₀ 1 / (2 * dist z v) := by positivity
    set w : Pt := v + (min ρ₀ 1 / (2 * dist z v)) • (z - v) with hw_def
    have hwdist : dist w v = min ρ₀ 1 / 2 := by
      rw [hw_def, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hc.le, ← dist_eq_norm]
      field_simp
    have hwball : w ∈ ball v (min ρ₀ 1) := by
      rw [mem_ball, hwdist]; linarith
    have hwmem : w ∈ Omega (crown T.tiles v) v := hball_sub hwball
    rw [Omega, mem_iUnion₂] at hwmem
    obtain ⟨A, hAcrown, hwA⟩ := hwmem
    have ht : (0 : ℝ) < 2 * dist z v / min ρ₀ 1 := by positivity
    have hzA : z ∈ localCone A.carrier v := by
      have hscaled := gap_cone_scale hwA ht
      have heq : v + (2 * dist z v / min ρ₀ 1) • (w - v) = z := by
        rw [hw_def, add_sub_cancel_left, smul_smul]
        have hcoef : 2 * dist z v / min ρ₀ 1 * (min ρ₀ 1 / (2 * dist z v)) = 1 := by
          field_simp
        rw [hcoef, one_smul]
        abel
      rwa [heq] at hscaled
    rw [Omega, mem_iUnion₂]
    exact ⟨A, hAcrown, hzA⟩

/-- Step 1 of the blueprint proof of `uniformCrownCoverPlane_step1_close`: In a plane tiling,
the support of a crown at `v` represented in the catalogue covers a ball of uniform radius `d`
around `v`. -/
private lemma uniformCrownCoverPlane_step1_close_step1_crown_covers_ball {𝒞 : Set (Set (PlacedTile P))} (h𝒞 : IsCatalogue 𝒞) :
    ∃ d : ℝ, 0 < d ∧ ∀ T : PlaneTiling P, AllCrownsIn 𝒞 T.tiles →
      ∀ v : Pt, IsVertexOf T.tiles v →
        ball v d ⊆ support (crown T.tiles v) := by
  obtain ⟨r, hr, δ, hδ, hrδ⟩ := uniformSectorRadius h𝒞
  refine ⟨r, hr, fun T hT v hv => ?_⟩
  have hK : translateSet (-v) (crown T.tiles v) ∈ 𝒞 := hT v hv
  obtain ⟨hsupp, -⟩ := hrδ (translateSet (-v) (crown T.tiles v)) hK v
  simp only [gap_translateSet_neg] at hsupp
  rw [uniformCrownCoverPlane_step1_close_step1_crown_covers_ball_aux1 T hv, univ_inter] at hsupp
  intro y hy
  have hy' : y ∈ support (crown T.tiles v) ∩ ball v r := by rw [hsupp]; exact hy
  exact hy'.1

/-- Step 2 of the blueprint proof of `uniformCrownCoverPlane_step1_close`: If the closed convex hull
  `H` of `S` has a point within `d/2` of `v`, and the diameter of `S` is less than `d/2`, then `S`
  is strictly contained in the ball of radius `d` around `v`. -/
private lemma uniformCrownCoverPlane_step1_close_step2_subset_ball {S H : Set Pt} {v : Pt} {d : ℝ}
    (hS_bound : Bornology.IsBounded S) (hS_diam : diam S < d / 2)
    (hH : H = closedConvexHull ℝ S) (hx : ∃ x ∈ H, dist x v < d / 2) :
    S ⊆ ball v d := by
  rcases hx with ⟨x, hxH, hxv⟩
  have hH_bound : Bornology.IsBounded H := by
    rw [hH, closedConvexHull_eq_closure_convexHull]
    exact (isBounded_convexHull.mpr hS_bound).closure
  have hdist : ∀ s ∈ S, dist s x ≤ diam S := by
    intro s hs
    have hsH : s ∈ H := by
      rw [hH]
      exact (subset_closedConvexHull (𝕜 := ℝ) hs)
    have hdist' := Metric.dist_le_diam_of_mem hH_bound hsH hxH
    rw [hH, closedConvexHullDiameter] at hdist'
    exact hdist'
  intro s hs
  rw [mem_ball]
  have hsx : dist s x < d / 2 := (hdist s hs).trans_lt hS_diam
  calc
    dist s v ≤ dist s x + dist x v := dist_triangle _ _ _
    _ < d / 2 + d / 2 := add_lt_add hsx hxv
    _ = d := by ring

/-- Step 1 of the blueprint proof of `uniformCrownCoverPlane`: If `H` (the closed convex
hull of `S`) comes within `d/2` of a tile vertex `v`, and `diam S < d/2`, then all of `H`
(and thus `S`) is within distance `d` of `v`. The complete crown at `v` covers `B(v, d)`
and therefore covers `S`. -/
private lemma uniformCrownCoverPlane_step1_close {𝒞 : Set (Set (PlacedTile P))}
    (h𝒞 : IsCatalogue 𝒞) :
    ∃ d : ℝ, 0 < d ∧ ∀ T : PlaneTiling P, AllCrownsIn 𝒞 T.tiles →
      ∀ S : Set Pt, Bornology.IsBounded S → diam S < d / 2 →
        ∀ H : Set Pt, H = closedConvexHull ℝ S →
        ∀ v : Pt, IsVertexOf T.tiles v →
        (∃ x ∈ H, dist x v < d / 2) →
        S ⊆ support (crown T.tiles v) := by
  obtain ⟨d, hd, hd_prop⟩ := uniformCrownCoverPlane_step1_close_step1_crown_covers_ball h𝒞
  use d, hd
  intro T hT S hS_bound hS_diam H hH v hv hx
  have h1 := uniformCrownCoverPlane_step1_close_step2_subset_ball hS_bound hS_diam hH hx
  have h2 := hd_prop T hT v hv
  exact Set.Subset.trans h1 h2

/-- Step 1 of the blueprint proof of `uniformCrownCoverPlane_step2_far`: if a tile `A` meets
a convex set `H` without containing it, the segment from a point of `A ∩ H` to a point of
`H \ A` exits `A`'s carrier at a point of one of its listed sides that lies in `H`. -/
private lemma uniformCrownCoverPlane_step2_far_step1_exit_point (A : PlacedTile P) {H : Set Pt}
    (hH : Convex ℝ H) {p q : Pt} (hpA : p ∈ A.carrier) (hpH : p ∈ H) (hqH : q ∈ H)
    (hqA : q ∉ A.carrier) :
    ∃ (i : Fin (P.disk A.form).n) (e : Pt), e ∈ A.side i ∧ e ∈ H := by
  obtain ⟨e, heSeg, heFront⟩ := crown_frontier_meets_segment (macro_tile_closed A) hpA hqA
  have heH : e ∈ H := hH.segment_subset hpH hqH heSeg
  rw [macro_tile_frontier_eq, mem_iUnion] at heFront
  exact ⟨heFront.choose, e, heFront.choose_spec, heH⟩

private lemma uniformCrownCoverPlane_overlap_collinear {p q r s x y : Pt}
    (hxy : x ≠ y) (hx1 : x ∈ segment ℝ p q) (hy1 : y ∈ segment ℝ p q)
    (hx2 : x ∈ segment ℝ r s) (hy2 : y ∈ segment ℝ r s) :
    Collinear ℝ ({p, q, r, s} : Set Pt) := by
  have hxp : x ∈ line[ℝ, p, q] := (mem_segment_iff_wbtw.mp hx1).mem_affineSpan
  have hyp : y ∈ line[ℝ, p, q] := (mem_segment_iff_wbtw.mp hy1).mem_affineSpan
  have hxr : x ∈ line[ℝ, r, s] := (mem_segment_iff_wbtw.mp hx2).mem_affineSpan
  have hyr : y ∈ line[ℝ, r, s] := (mem_segment_iff_wbtw.mp hy2).mem_affineSpan
  have hpq : Collinear ℝ ({x, y, p, q} : Set Pt) :=
    collinear_insert_insert_of_mem_affineSpan_pair hxp hyp
  have hrs : Collinear ℝ ({x, y, r, s} : Set Pt) :=
    collinear_insert_insert_of_mem_affineSpan_pair hxr hyr
  have hp : p ∈ line[ℝ, x, y] :=
    hpq.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy
  have hq : q ∈ line[ℝ, x, y] :=
    hpq.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy
  have hr : r ∈ line[ℝ, x, y] :=
    hrs.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy
  have hs : s ∈ line[ℝ, x, y] :=
    hrs.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy
  have hline : Collinear ℝ (↑(line[ℝ, x, y]) : Set Pt) := by
    show Module.rank ℝ (vectorSpan ℝ (↑(line[ℝ, x, y]) : Set Pt)) ≤ 1
    rw [← AffineSubspace.direction_eq_vectorSpan, direction_affineSpan]
    exact collinear_pair ℝ x y
  refine hline.subset ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact hp
  · exact hq
  · exact hr
  · exact hs

private lemma uniformCrownCoverPlane_endpoint_between {c d p e : Pt} (hcd : c ≠ d)
    (hp : p ∈ openSegment ℝ c d) (heline : e ∈ line[ℝ, c, d])
    (he : e ∉ segment ℝ c d) :
    c ∈ openSegment ℝ e p ∨ d ∈ openSegment ℝ p e := by
  have hcol : Collinear ℝ ({c, d, e} : Set Pt) := by
    refine (collinear_insert_of_mem_affineSpan_pair heline).subset ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with rfl | rfl | rfl <;> simp
  have hcpd : Sbtw ℝ c p d := crown_sbtw_of_mem_openSegment hcd hp
  rcases hcol.wbtw_or_wbtw_or_wbtw with hcde | hdec | hecd
  · have hde : d ≠ e := by
      intro h
      apply he
      rw [← h]
      exact right_mem_segment ℝ c d
    have hcde' : Sbtw ℝ c d e := ⟨hcde, hcd.symm, hde⟩
    exact Or.inr (crown_mem_openSegment_of_sbtw (hcde'.trans_left_right hcpd))
  · exfalso
    apply he
    rw [segment_symm]
    exact hdec.mem_segment
  · have hce : c ≠ e := by
      intro h
      apply he
      rw [← h]
      exact left_mem_segment ℝ c d
    have hecd' : Sbtw ℝ e c d := ⟨hecd, hce, hcd⟩
    exact Or.inl (crown_mem_openSegment_of_sbtw (hecd'.trans_right_left hcpd))

/-- Step 2 of the blueprint proof of `uniformCrownCoverPlane_step2_far`: near a point `e` of a
listed side of a tile `A` of a plane tiling `T` that is not one of that side's two endpoints,
disjoint interiors together with the tiles covering the whole plane force a second tile `B`
with an edge through `e` collinear with `A`'s edge, on the opposite side. -/
private lemma uniformCrownCoverPlane_step2_far_step2_opposite_tile
    (T : PlaneTiling P) {A : PlacedTile P} (hA : A ∈ T.tiles) (i : Fin (P.disk A.form).n)
    {e : Pt} (hei : e ∈ A.side i) (hne1 : e ≠ A.vertex i) (hne2 : e ≠ A.vertex (finRotate _ i)) :
    ∃ (B : PlacedTile P) (j : Fin (P.disk B.form).n), B ∈ T.tiles ∧
      Disjoint (interior A.carrier) (interior B.carrier) ∧ e ∈ B.side j ∧
      Collinear ℝ ({A.vertex i, A.vertex (finRotate _ i),
        B.vertex j, B.vertex (finRotate _ j)} : Set Pt) := by
  classical
  have heopen : e ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)) := by
    apply mem_openSegment_of_ne_left_right hne1.symm hne2.symm
    rwa [← macro_tile_side_eq A i]
  let F : Set (PlacedTile P) :=
    {B ∈ T.tiles | (B.carrier ∩ closedBall e 1).Nonempty}
  have hFfin : F.Finite := T.locallyFinite (isCompact_closedBall e 1)
  have heAcarrier : e ∈ A.carrier :=
    (macro_tile_closed A).frontier_subset (macro_tile_side_subset_frontier A i hei)
  have hAF : A ∈ F := ⟨hA, ⟨e, heAcarrier, mem_closedBall_self (by norm_num)⟩⟩
  let V : Set Pt := ⋃ B ∈ F, B.vertexSet
  have hVfin : V.Finite := by
    apply hFfin.biUnion
    intro B hB
    exact Set.finite_range B.vertex
  have hVclosed : IsClosed (V \ {e}) :=
    (hVfin.diff : (V \ {e}).Finite).isClosed
  have heVcompl : e ∈ (V \ {e})ᶜ := by simp
  obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.mp hVclosed.isOpen_compl e heVcompl
  obtain ⟨p, hpball, hpep⟩ := crown_exists_near_openSegment hne1
    (lt_min hδ (by norm_num : (0 : ℝ) < 1 / 4))
  have hpδ : p ∈ ball e δ := ball_subset_ball (min_le_left δ (1 / 4)) hpball
  have hpquarter : p ∈ ball e (1 / 4) :=
    ball_subset_ball (min_le_right δ (1 / 4)) hpball
  have hpne : p ≠ e := (crown_sbtw_of_mem_openSegment hne1 hpep).ne_left
  have hpV : p ∉ V := by
    intro hp
    exact hδball hpδ ⟨hp, by simpa using hpne⟩
  have hpAi : p ∈ A.side i := by
    have hconv : Convex ℝ (A.side i) := by
      rw [macro_tile_side_eq]
      exact convex_segment _ _
    exact hconv.segment_subset hei (by
      rw [macro_tile_side_eq]
      exact left_mem_segment ℝ _ _) (openSegment_subset_segment ℝ _ _ hpep)
  have hpAcarrier : p ∈ A.carrier :=
    (macro_tile_closed A).frontier_subset (macro_tile_side_subset_frontier A i hpAi)
  have hpfront : p ∈ frontier A.carrier := macro_tile_side_subset_frontier A i hpAi
  have hpcompl : p ∈ closure A.carrierᶜ := by
    rw [frontier_eq_closure_inter_closure] at hpfront
    exact hpfront.2
  have hFCclosed : IsClosed (support (F \ {A})) :=
    (hFfin.diff : (F \ {A}).Finite).isClosed_biUnion fun B _ => macro_tile_closed B
  have hpFC : p ∈ support (F \ {A}) := by
    rw [← hFCclosed.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨y, hyout, hypy⟩ := Metric.mem_closure_iff.mp hpcompl (min ε (1 / 2))
      (lt_min hε (by norm_num))
    have hycover : y ∈ support T.tiles := by rw [T.cover]; exact mem_univ y
    rw [support, mem_iUnion₂] at hycover
    obtain ⟨B, hBT, hyB⟩ := hycover
    have hBA : B ≠ A := fun h => hyout (h ▸ hyB)
    have hypy' : dist y p < 1 / 2 := by
      rw [dist_comm]
      exact hypy.trans_le (min_le_right _ _)
    have hpe' : dist p e < 1 / 4 := by simpa [Metric.mem_ball] using hpquarter
    have hye : dist y e ≤ 1 := by
      calc
        dist y e ≤ dist y p + dist p e := dist_triangle _ _ _
        _ ≤ 1 := by linarith
    have hBF : B ∈ F := ⟨hBT, ⟨y, hyB, by simpa [mem_closedBall] using hye⟩⟩
    refine ⟨y, ?_, hypy.trans_le (min_le_left _ _)⟩
    rw [support, mem_iUnion₂]
    exact ⟨B, Set.mem_diff_singleton.mpr ⟨hBF, hBA⟩, hyB⟩
  rw [support, mem_iUnion₂] at hpFC
  obtain ⟨B, hBFdiff, hpBcarrier⟩ := hpFC
  have hBF : B ∈ F := (Set.mem_diff_singleton.mp hBFdiff).1
  have hBA : B ≠ A := (Set.mem_diff_singleton.mp hBFdiff).2
  have hBT : B ∈ T.tiles := hBF.1
  have hpAvertex : p ∉ A.vertexSet := by
    intro hp
    apply hpV
    exact mem_iUnion₂.mpr ⟨A, hAF, hp⟩
  have hpBvertex : p ∉ B.vertexSet := by
    intro hp
    apply hpV
    exact mem_iUnion₂.mpr ⟨B, hBF, hp⟩
  have hdisj : Disjoint (interior A.carrier) (interior B.carrier) :=
    T.disjoint hA hBT hBA.symm
  obtain ⟨k, j, hpk, hpj, hoverlap⟩ :=
    macro_tiles_share_local_side hdisj hpAcarrier hpBcarrier hpAvertex hpBvertex
  have hki : k = i := macro_tile_side_unique A hpAvertex hpk hpAi
  subst k
  obtain ⟨x, y, hxy, hxySides⟩ := hoverlap
  have hcol : Collinear ℝ ({A.vertex i, A.vertex (finRotate _ i),
      B.vertex j, B.vertex (finRotate _ j)} : Set Pt) := by
    apply uniformCrownCoverPlane_overlap_collinear hxy
    · rw [← macro_tile_side_eq A i]
      exact (hxySides (left_mem_segment ℝ x y)).1
    · rw [← macro_tile_side_eq A i]
      exact (hxySides (right_mem_segment ℝ x y)).1
    · rw [← macro_tile_side_eq B j]
      exact (hxySides (left_mem_segment ℝ x y)).2
    · rw [← macro_tile_side_eq B j]
      exact (hxySides (right_mem_segment ℝ x y)).2
  have hBne : B.vertex j ≠ B.vertex (finRotate _ j) := trimmed_tile_vertex_ne_next B j
  have hpBopen : p ∈ openSegment ℝ (B.vertex j) (B.vertex (finRotate _ j)) := by
    apply mem_openSegment_of_ne_left_right
    · intro h
      exact hpBvertex ⟨j, h⟩
    · intro h
      exact hpBvertex ⟨finRotate _ j, h⟩
    · rwa [← macro_tile_side_eq B j]
  have hAne : A.vertex i ≠ A.vertex (finRotate _ i) := trimmed_tile_vertex_ne_next A i
  have hcA : B.vertex j ∈ line[ℝ, A.vertex i, A.vertex (finRotate _ i)] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAne
  have hdA : B.vertex (finRotate _ j) ∈
      line[ℝ, A.vertex i, A.vertex (finRotate _ i)] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAne
  have hlines : line[ℝ, B.vertex j, B.vertex (finRotate _ j)] =
      line[ℝ, A.vertex i, A.vertex (finRotate _ i)] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hcA hdA hBne
  have heAline : e ∈ line[ℝ, A.vertex i, A.vertex (finRotate _ i)] :=
    (mem_segment_iff_wbtw.mp (macro_tile_side_eq A i ▸ hei)).mem_affineSpan
  have heBline : e ∈ line[ℝ, B.vertex j, B.vertex (finRotate _ j)] := by
    rw [hlines]
    exact heAline
  have heBj : e ∈ B.side j := by
    rw [macro_tile_side_eq]
    by_contra he
    rcases uniformCrownCoverPlane_endpoint_between hBne hpBopen heBline he with hc | hd
    · have hcball : B.vertex j ∈ ball e δ :=
        (convex_ball e δ).segment_subset (mem_ball_self hδ) hpδ
          (openSegment_subset_segment ℝ e p hc)
      have hcV : B.vertex j ∈ V := mem_iUnion₂.mpr ⟨B, hBF, ⟨j, rfl⟩⟩
      exact hδball hcball ⟨hcV, by
        simpa using (crown_sbtw_of_mem_openSegment (by
          exact fun h => hpne h.symm) hc).ne_left⟩
    · have hdball : B.vertex (finRotate _ j) ∈ ball e δ :=
        (convex_ball e δ).segment_subset hpδ (mem_ball_self hδ)
          (openSegment_subset_segment ℝ p e hd)
      have hdV : B.vertex (finRotate _ j) ∈ V :=
        mem_iUnion₂.mpr ⟨B, hBF, ⟨finRotate _ j, rfl⟩⟩
      exact hδball hdball ⟨hdV, by
        simpa using (crown_sbtw_of_mem_openSegment hpne hd).ne_right⟩
  exact ⟨B, j, hBT, hdisj, heBj, hcol⟩

/-- Step 3 of the blueprint proof of `uniformCrownCoverPlane_step2_far`: if sides of two tiles
`A` and `B` meet at a common point `e` and the four endpoints of those sides are collinear,
one of those four endpoints lies in both carriers. -/
private lemma uniformCrownCoverPlane_step2_far_step3_shared_vertex
    {A B : PlacedTile P} (i : Fin (P.disk A.form).n) (j : Fin (P.disk B.form).n) {e : Pt}
    (hei : e ∈ A.side i) (hej : e ∈ B.side j)
    (hcol : Collinear ℝ ({A.vertex i, A.vertex (finRotate _ i),
      B.vertex j, B.vertex (finRotate _ j)} : Set Pt)) :
    ∃ v, (v = A.vertex i ∨ v = A.vertex (finRotate _ i) ∨
            v = B.vertex j ∨ v = B.vertex (finRotate _ j)) ∧
      v ∈ A.carrier ∧ v ∈ B.carrier := by
  have hsideA : A.side i ⊆ A.carrier := by
    intro x hx
    exact (macro_tile_closed A).frontier_subset
      (macro_tile_side_subset_frontier A i hx)
  have hsideB : B.side j ⊆ B.carrier := by
    intro x hx
    exact (macro_tile_closed B).frontier_subset
      (macro_tile_side_subset_frontier B j hx)
  have hAne : A.vertex i ≠ A.vertex (finRotate _ i) :=
    trimmed_tile_vertex_ne_next A i
  by_cases heA1 : e = A.vertex i
  · refine ⟨A.vertex i, Or.inl rfl, gap_vertex_mem_carrier A ⟨i, rfl⟩, ?_⟩
    rw [← heA1]
    exact hsideB hej
  by_cases heA2 : e = A.vertex (finRotate _ i)
  · refine ⟨A.vertex (finRotate _ i), Or.inr (Or.inl rfl),
      gap_vertex_mem_carrier A ⟨finRotate _ i, rfl⟩, ?_⟩
    rw [← heA2]
    exact hsideB hej
  by_cases heB1 : e = B.vertex j
  · refine ⟨B.vertex j, Or.inr (Or.inr (Or.inl rfl)), ?_,
      gap_vertex_mem_carrier B ⟨j, rfl⟩⟩
    rw [← heB1]
    exact hsideA hei
  by_cases heB2 : e = B.vertex (finRotate _ j)
  · refine ⟨B.vertex (finRotate _ j), Or.inr (Or.inr (Or.inr rfl)), ?_,
      gap_vertex_mem_carrier B ⟨finRotate _ j, rfl⟩⟩
    rw [← heB2]
    exact hsideA hei
  have hA1 : A.vertex i ≠ e := by
    intro h
    exact heA1 h.symm
  have hA2 : A.vertex (finRotate _ i) ≠ e := by
    intro h
    exact heA2 h.symm
  have hB1 : B.vertex j ≠ e := by
    intro h
    exact heB1 h.symm
  have hB2 : B.vertex (finRotate _ j) ≠ e := by
    intro h
    exact heB2 h.symm
  have heAopen : e ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)) := by
    apply mem_openSegment_of_ne_left_right hA1 hA2
    rw [← trimmed_tile_side_eq A i]
    exact hei
  have heBopen : e ∈ openSegment ℝ (B.vertex j) (B.vertex (finRotate _ j)) := by
    apply mem_openSegment_of_ne_left_right hB1 hB2
    rw [← trimmed_tile_side_eq B j]
    exact hej
  have hline1 : B.vertex j ∈ line[ℝ, A.vertex i, A.vertex (finRotate _ i)] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAne
  have hline2 : B.vertex (finRotate _ j) ∈
      line[ℝ, A.vertex i, A.vertex (finRotate _ i)] :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hAne
  rcases crown_endpoint_mem_of_collinear_intersection hAne heAopen heBopen hline1 hline2 with
    h | h | h | h
  · refine ⟨B.vertex j, Or.inr (Or.inr (Or.inl rfl)), ?_,
      gap_vertex_mem_carrier B ⟨j, rfl⟩⟩
    apply hsideA
    rw [trimmed_tile_side_eq A i]
    exact h
  · refine ⟨B.vertex (finRotate _ j), Or.inr (Or.inr (Or.inr rfl)), ?_,
      gap_vertex_mem_carrier B ⟨finRotate _ j, rfl⟩⟩
    apply hsideA
    rw [trimmed_tile_side_eq A i]
    exact h
  · refine ⟨A.vertex i, Or.inl rfl, gap_vertex_mem_carrier A ⟨i, rfl⟩, ?_⟩
    apply hsideB
    rw [trimmed_tile_side_eq B j]
    exact h
  · refine ⟨A.vertex (finRotate _ i), Or.inr (Or.inl rfl),
      gap_vertex_mem_carrier A ⟨finRotate _ i, rfl⟩, ?_⟩
    apply hsideB
    rw [trimmed_tile_side_eq B j]
    exact h

/-- Step 2 of the blueprint proof of `uniformCrownCoverPlane`: Otherwise `H` stays at
distance at least `d/2` from every vertex. The structural lemma covers `H` using tiles
meeting `H` or opposite tiles, and their common vertex will have a crown containing `H`
and thus `S`. -/
private lemma uniformCrownCoverPlane_step2_far {𝒞 : Set (Set (PlacedTile P))} (h𝒞 : IsCatalogue 𝒞)
    (d : ℝ) (hd : 0 < d) :
    ∃ η : ℝ, 0 < η ∧ ∀ T : PlaneTiling P, AllCrownsIn 𝒞 T.tiles →
      ∀ S : Set Pt, Bornology.IsBounded S → diam S < η →
        ∀ H : Set Pt, H = closedConvexHull ℝ S →
        (∀ x ∈ H, ∀ v, IsVertexOf T.tiles v → d / 2 ≤ dist x v) →
        ∃ v, IsVertexOf T.tiles v ∧ S ⊆ support (crown T.tiles v) := by
  have _ := h𝒞
  obtain ⟨η, hη, hball⟩ := trimmedEdgeTwoTileBall (P := P) hd
  refine ⟨η, hη, ?_⟩
  intro T hT S hS_bound hS_diam H hH hfar
  have hH_bound : Bornology.IsBounded H := by
    rw [hH, closedConvexHull_eq_closure_convexHull]
    exact (isBounded_convexHull.mpr hS_bound).closure
  have hH_diam : diam H < η := by rw [hH, closedConvexHullDiameter]; exact hS_diam
  have hSH : S ⊆ H := by rw [hH]; exact subset_closedConvexHull (𝕜 := ℝ)
  have hHconv : Convex ℝ H := by
    rw [hH, closedConvexHull_eq_closure_convexHull]
    exact (convex_convexHull ℝ S).closure
  have htiles_ne : T.tiles.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hsupp : support T.tiles = ∅ := by rw [hempty, support]; simp
    rw [T.cover] at hsupp
    exact Set.univ_nonempty.ne_empty hsupp
  by_cases hcase : ∃ A ∈ T.tiles, H ⊆ A.carrier
  · obtain ⟨A, hA, hAH⟩ := hcase
    have hn3 : 3 ≤ (P.disk A.form).n := (P.disk A.form).three_le
    let i0 : Fin (P.disk A.form).n := ⟨0, by omega⟩
    have hvA : A.vertex i0 ∈ A.vertexSet := ⟨i0, rfl⟩
    have hvIs : IsVertexOf T.tiles (A.vertex i0) := ⟨A, hA, hvA⟩
    have hvCarrier : A.vertex i0 ∈ A.carrier := gap_vertex_mem_carrier A hvA
    have hAcrown : A ∈ crown T.tiles (A.vertex i0) := ⟨hA, hvCarrier⟩
    refine ⟨A.vertex i0, hvIs, hSH.trans (hAH.trans ?_)⟩
    intro x hx
    rw [support, mem_iUnion₂]
    exact ⟨A, hAcrown, hx⟩
  · push_neg at hcase
    have hHne : H.Nonempty := by
      rcases Set.eq_empty_or_nonempty H with hHempty | hHne
      · exfalso
        obtain ⟨A₀, hA₀⟩ := htiles_ne
        have hHe : H ⊆ A₀.carrier := by rw [hHempty]; exact Set.empty_subset _
        exact hcase A₀ hA₀ hHe
      · exact hHne
    obtain ⟨p, hpH⟩ := hHne
    have hpcover : p ∈ support T.tiles := by rw [T.cover]; exact mem_univ p
    rw [support, mem_iUnion₂] at hpcover
    obtain ⟨A, hA, hpA⟩ := hpcover
    have hAH' : ¬ H ⊆ A.carrier := hcase A hA
    rw [Set.not_subset] at hAH'
    obtain ⟨q, hqH, hqA⟩ := hAH'
    obtain ⟨i, e, hei, heH⟩ :=
      uniformCrownCoverPlane_step2_far_step1_exit_point A hHconv hpA hpH hqH hqA
    have he1 : e ≠ A.vertex i := by
      intro heq
      have hc := hfar e heH (A.vertex i) ⟨A, hA, ⟨i, rfl⟩⟩
      rw [heq, dist_self] at hc
      linarith
    have he2 : e ≠ A.vertex (finRotate _ i) := by
      intro heq
      have hc := hfar e heH (A.vertex (finRotate _ i)) ⟨A, hA, ⟨finRotate _ i, rfl⟩⟩
      rw [heq, dist_self] at hc
      linarith
    obtain ⟨B, j, hB, hdisj, hej, hcol⟩ :=
      uniformCrownCoverPlane_step2_far_step2_opposite_tile T hA i hei he1 he2
    have hA1 : d / 2 ≤ dist e (A.vertex i) := hfar e heH (A.vertex i) ⟨A, hA, ⟨i, rfl⟩⟩
    have hA2 : d / 2 ≤ dist e (A.vertex (finRotate _ i)) :=
      hfar e heH (A.vertex (finRotate _ i)) ⟨A, hA, ⟨finRotate _ i, rfl⟩⟩
    have hB1 : d / 2 ≤ dist e (B.vertex j) := hfar e heH (B.vertex j) ⟨B, hB, ⟨j, rfl⟩⟩
    have hB2 : d / 2 ≤ dist e (B.vertex (finRotate _ j)) :=
      hfar e heH (B.vertex (finRotate _ j)) ⟨B, hB, ⟨finRotate _ j, rfl⟩⟩
    have hballAB := hball A B hdisj i j e hei hej hcol hA1 hA2 hB1 hB2
    have hHball : H ⊆ ball e η := by
      intro x hx
      rw [mem_ball]
      calc dist x e ≤ diam H := Metric.dist_le_diam_of_mem hH_bound hx heH
        _ < η := hH_diam
    have hHAB : H ⊆ A.carrier ∪ B.carrier := hHball.trans hballAB
    obtain ⟨v, hv4, hvA, hvB⟩ :=
      uniformCrownCoverPlane_step2_far_step3_shared_vertex i j hei hej hcol
    have hvIs : IsVertexOf T.tiles v := by
      rcases hv4 with h | h | h | h
      · exact ⟨A, hA, by rw [h]; exact Set.mem_range_self i⟩
      · exact ⟨A, hA, by rw [h]; exact Set.mem_range_self (finRotate _ i)⟩
      · exact ⟨B, hB, by rw [h]; exact Set.mem_range_self j⟩
      · exact ⟨B, hB, by rw [h]; exact Set.mem_range_self (finRotate _ j)⟩
    have hAcrown : A ∈ crown T.tiles v := ⟨hA, hvA⟩
    have hBcrown : B ∈ crown T.tiles v := ⟨hB, hvB⟩
    refine ⟨v, hvIs, hSH.trans ?_⟩
    intro x hx
    rw [support, mem_iUnion₂]
    rcases hHAB hx with hxA | hxB
    · exact ⟨A, hAcrown, hxA⟩
    · exact ⟨B, hBcrown, hxB⟩

/-- `lem:crown-cover-plane`: there is `ε > 0` such that, in every plane tiling
whose full pointed crowns are represented in the catalogue, every bounded set
of diameter `< ε` lies in the support of one full crown. -/
theorem uniformCrownCoverPlane {𝒞 : Set (Set (PlacedTile P))} (h𝒞 : IsCatalogue 𝒞) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T : PlaneTiling P, AllCrownsIn 𝒞 T.tiles →
      ∀ S : Set Pt, Bornology.IsBounded S → diam S < ε →
        ∃ v, IsVertexOf T.tiles v ∧ S ⊆ support (crown T.tiles v) := by
  obtain ⟨d, hd_pos, h_close⟩ := uniformCrownCoverPlane_step1_close h𝒞
  obtain ⟨η, hη_pos, h_far⟩ := uniformCrownCoverPlane_step2_far h𝒞 d hd_pos
  use min (d / 2) η
  refine ⟨lt_min (half_pos hd_pos) hη_pos, fun T hT S hS_bound hS_diam => ?_⟩
  let H := closedConvexHull ℝ S
  by_cases h : ∃ x ∈ H, ∃ v, IsVertexOf T.tiles v ∧ dist x v < d / 2
  · rcases h with ⟨x, hx, v, hv, hxv⟩
    exact ⟨v, hv,
      h_close T hT S hS_bound (hS_diam.trans_le (min_le_left _ _)) H rfl v hv ⟨x, hx, hxv⟩⟩
  · push_neg at h
    refine h_far T hT S hS_bound (hS_diam.trans_le (min_le_right _ _)) H rfl h

/-- Step 1 of the blueprint proof of `uniformCrownCoverSupertile`: obtaining sector bounds. -/
private lemma uniformCrownCoverSupertile_step1_radius
    {𝒞 : Set (Set (PlacedTile P))} (h𝒞 : IsCatalogue 𝒞) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ SectorRadiusProperty 𝒞 r δ ∧
    0 < crownRadius r δ (rootSeparationConstants P) := by
  obtain ⟨r, hr, δ, hδ, hrδ⟩ := uniformSectorRadius h𝒞
  use r, δ, hr, hδ, hrδ
  dsimp [crownRadius]
  set hR := rootSeparationConstants P
  refine mul_pos (by positivity) (lt_min (lt_min hr hR.ν_pos) (lt_min hR.lam_pos ?_))
  refine mul_pos (lt_min hr hδ) (Real.sin_pos_of_mem_Ioo ⟨hR.μ_pos, hR.μ_le.trans_lt (by linarith [Real.pi_pos])⟩)

/-- Step 2 of the blueprint proof of `uniformCrownCoverSupertile`: convex hull near a child. -/
private lemma uniformCrownCoverSupertile_step2_case1
    {𝒞 : Set (Set (PlacedTile P))} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hrδ : SectorRadiusProperty 𝒞 r δ)
    (M : MacroPatch P) (hM : AllCrownsIn 𝒞 M.tiles)
    {S : Set Pt} (hS_bound : Bornology.IsBounded S)
    {ε : ℝ} (hε_d : ε ≤ crownRadius r δ (rootSeparationConstants P) / 2)
    (hdiam : diam S < ε) (v : Pt) (hv : IsVertexOf M.tiles v)
    (h_near : ∃ x ∈ closedConvexHull ℝ S,
      dist x v < crownRadius r δ (rootSeparationConstants P) / 2) :
    S ∩ support M.tiles ⊆ support (crown M.tiles v) := by
  have hS_diam : diam S < crownRadius r δ (rootSeparationConstants P) / 2 :=
    hdiam.trans_le hε_d
  have hS_ball : S ⊆ ball v (crownRadius r δ (rootSeparationConstants P)) :=
    uniformCrownCoverPlane_step1_close_step2_subset_ball hS_bound hS_diam rfl h_near
  have hcov := uniformRelativeCrownBall hr hδ hrδ (rootSeparationConstants P) M hM hv
  intro y hy
  exact hcov.2 (hcov.1 ⟨hy.2, hS_ball hy.1⟩)

/-! The remaining far case is split into numerical selection, convexification,
and the local two-tile crown-selection argument. -/

/-- Step 3 of the blueprint proof of
`uniformCrownCoverSupertile_step3_epsilon_and_case2`: choose the positive
radius and edge-ball constants needed in the far case. -/
private lemma uniformCrownCoverSupertile_step3_epsilon_and_case2_step1_constants
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    ∃ d η ε : ℝ, 0 < d ∧ 0 < η ∧ d = crownRadius r δ (rootSeparationConstants P) ∧
    0 < ε ∧
    ε ≤ crownRadius r δ (rootSeparationConstants P) / 2 ∧
    ε ≤ η ∧ ε ≤ (rootSeparationConstants P).lam ∧
    ε ≤ d * Real.sin ((rootSeparationConstants P).μ / 2) ∧
    ∀ (A B : PlacedTile P),
      Disjoint (interior A.carrier) (interior B.carrier) →
      ∀ (i : Fin (P.disk A.form).n) (j : Fin (P.disk B.form).n) (e : Pt),
        e ∈ A.side i → e ∈ B.side j →
        Collinear ℝ ({A.vertex i, A.vertex (finRotate _ i),
          B.vertex j, B.vertex (finRotate _ j)} : Set Pt) →
        d / 2 ≤ dist e (A.vertex i) →
        d / 2 ≤ dist e (A.vertex (finRotate _ i)) →
        d / 2 ≤ dist e (B.vertex j) →
        d / 2 ≤ dist e (B.vertex (finRotate _ j)) →
        ball e η ⊆ A.carrier ∪ B.carrier := by
  have hc : 0 < crownRadius r δ (rootSeparationConstants P) := by
    dsimp [crownRadius]
    set hR := rootSeparationConstants P
    refine mul_pos (by positivity) (lt_min (lt_min hr hR.ν_pos)
      (lt_min hR.lam_pos ?_))
    refine mul_pos (lt_min hr hδ)
      (Real.sin_pos_of_mem_Ioo ⟨hR.μ_pos,
        hR.μ_le.trans_lt (by linarith [Real.pi_pos])⟩)
  obtain ⟨η, hη, hη_ball⟩ := trimmedEdgeTwoTileBall hc
  let d := crownRadius r δ (rootSeparationConstants P)
  let ε := min (d / 2) (min η (min (rootSeparationConstants P).lam
    (d * Real.sin ((rootSeparationConstants P).μ / 2))))
  have hsin : 0 < Real.sin ((rootSeparationConstants P).μ / 2) := by
    exact Real.sin_pos_of_mem_Ioo ⟨by linarith [(rootSeparationConstants P).μ_pos],
      by linarith [Real.pi_pos, (rootSeparationConstants P).μ_le]
        ⟩
  refine ⟨d, η, ε, hc, hη, rfl, ?_, ?_, ?_, ?_, ?_, hη_ball⟩
  · dsimp [ε]
    exact lt_min (half_pos hc) (lt_min hη (lt_min
      (rootSeparationConstants P).lam_pos
      (by
        dsimp [d]
        exact mul_pos hc hsin)))
  · dsimp [ε, d]
    exact min_le_left _ _
  · dsimp [ε]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  · dsimp [ε]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  · dsimp [ε]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))

/-- Step 3 of the blueprint proof of
`uniformCrownCoverSupertile_step3_epsilon_and_case2`: pass from a bounded set
to its closed convex hull without increasing its diameter. -/
private lemma uniformCrownCoverSupertile_step3_epsilon_and_case2_step2_hull
    {S : Set Pt} {ε : ℝ} (hS_bound : Bornology.IsBounded S)
    (hS_diam : diam S < ε) :
    ∃ H : Set Pt, H = closedConvexHull ℝ S ∧ Convex ℝ H ∧
      Bornology.IsBounded H ∧ diam H < ε ∧ S ⊆ H := by
  refine ⟨closedConvexHull ℝ S, rfl, convex_closedConvexHull, ?_, ?_,
    subset_closedConvexHull (𝕜 := ℝ)⟩
  · rw [closedConvexHull_eq_closure_convexHull]
    exact (isBounded_convexHull.mpr hS_bound).closure
  · rw [closedConvexHullDiameter]
    exact hS_diam

/-- Step 3 of the blueprint proof of
`uniformCrownCoverSupertile_step3_epsilon_and_case2`: the exterior-excursion
lemma makes the far convex hull intersect the macro support convexly. -/
private lemma uniformCrownCoverSupertile_step3_epsilon_and_case2_step2_convex
    {d ε : ℝ} (hd : 0 < d) (hε_lam : ε ≤ (rootSeparationConstants P).lam)
    (hε_sin : ε ≤ d * Real.sin ((rootSeparationConstants P).μ / 2))
    (M : MacroPatch P) {H : Set Pt} (hHconv : Convex ℝ H)
    (hHbound : Bornology.IsBounded H) (hHdiam : diam H < ε)
    (hfar : ∀ x ∈ H, ∀ v, IsVertexOf M.tiles v → d / 2 ≤ dist x v) :
    Convex ℝ (H ∩ support M.tiles) := by
  exact noShortExteriorExcursion (rootSeparationConstants P) hd M hHconv hHbound
    (lt_min (hHdiam.trans_le hε_lam) (hHdiam.trans_le hε_sin)) hfar

/-! The remaining local argument is split into the exit-point construction and the
endpoint observation for the two tiles at that exit. -/

/-- Step 0 of the blueprint proof of
`uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover`: a
macro patch has at least one listed child vertex. -/
private lemma uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover_step0_vertex
    (M : MacroPatch P) : ∃ v, IsVertexOf M.tiles v := by
  have hroot : (P.disk M.root).carrier.Nonempty :=
    (P.disk M.root).interior_nonempty.mono interior_subset
  obtain ⟨x, hx⟩ := hroot
  have hsupp : (support M.tiles).Nonempty := by
    rw [M.support_eq]
    refine ⟨M.offset + (M.θ ^ M.j) • x, ?_⟩
    rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    refine Set.mem_smul_set.mpr ⟨x, hx, ?_⟩
    abel
  obtain ⟨v, hv⟩ := hsupp
  rw [support, mem_iUnion₂] at hv
  obtain ⟨A, hA, -⟩ := hv
  let i : Fin (P.disk A.form).n :=
    ⟨0, by have := (P.disk A.form).three_le; omega⟩
  exact ⟨A.vertex i, A, hA, ⟨i, rfl⟩⟩

/-- Auxiliary step of the blueprint proof of
`uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover_step1_exit`: if two
segments `pq` and `rs` overlap with positive length, their four endpoints are collinear. -/
private lemma uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover_step1_exit_aux1
    {p q r s x y : Pt} (hxy : x ≠ y)
    (hx1 : x ∈ segment ℝ p q) (hy1 : y ∈ segment ℝ p q)
    (hx2 : x ∈ segment ℝ r s) (hy2 : y ∈ segment ℝ r s) :
    Collinear ℝ ({p, q, r, s} : Set Pt) := by
  have hxp : x ∈ line[ℝ, p, q] := (mem_segment_iff_wbtw.mp hx1).mem_affineSpan
  have hyp : y ∈ line[ℝ, p, q] := (mem_segment_iff_wbtw.mp hy1).mem_affineSpan
  have hxr : x ∈ line[ℝ, r, s] := (mem_segment_iff_wbtw.mp hx2).mem_affineSpan
  have hyr : y ∈ line[ℝ, r, s] := (mem_segment_iff_wbtw.mp hy2).mem_affineSpan
  have hcolA : Collinear ℝ ({x, y, p, q} : Set Pt) :=
    collinear_insert_insert_of_mem_affineSpan_pair hxp hyp
  have hcolB : Collinear ℝ ({x, y, r, s} : Set Pt) :=
    collinear_insert_insert_of_mem_affineSpan_pair hxr hyr
  have hpxy : p ∈ line[ℝ, x, y] :=
    hcolA.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy
  have hqxy : q ∈ line[ℝ, x, y] :=
    hcolA.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy
  have hrxy : r ∈ line[ℝ, x, y] :=
    hcolB.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy
  have hsxy : s ∈ line[ℝ, x, y] :=
    hcolB.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy
  have hline : Collinear ℝ (↑(line[ℝ, x, y]) : Set Pt) := by
    show Module.rank ℝ (vectorSpan ℝ (↑(line[ℝ, x, y]) : Set Pt)) ≤ 1
    rw [← AffineSubspace.direction_eq_vectorSpan, direction_affineSpan]
    exact collinear_pair ℝ x y
  refine hline.subset ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact hpxy
  · exact hqxy
  · exact hrxy
  · exact hsxy

/-- Auxiliary step of the blueprint proof of
`uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover_step1_exit`: if a ray from
`a` towards `b` lies in a closed set `S` for every parameter in `(t0, 1]` and `t0 < 1`, the point
at parameter `t0` lies in `S` too (it is a limit of points of `S`). -/
private lemma uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover_step1_exit_aux2
    {S : Set Pt} (hS : IsClosed S) {a b : Pt} (hab : a ≠ b) {t0 : ℝ} (ht0 : t0 < 1)
    (h : ∀ t : ℝ, t0 < t → t ≤ 1 → a + t • (b - a) ∈ S) :
    a + t0 • (b - a) ∈ S := by
  rw [← hS.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  have hnorm : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  set δ := min ((1 - t0) / 2) (ε / (2 * ‖b - a‖)) with hδ_def
  have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
  have hδ1 : δ ≤ (1 - t0) / 2 := min_le_left _ _
  refine ⟨a + (t0 + δ) • (b - a), h (t0 + δ) (by linarith) (by linarith), ?_⟩
  rw [dist_comm, dist_eq_norm]
  have heq : a + (t0 + δ) • (b - a) - (a + t0 • (b - a)) = δ • (b - a) := by module
  rw [heq, norm_smul, Real.norm_of_nonneg hδpos.le]
  have hδ2 : δ ≤ ε / (2 * ‖b - a‖) := min_le_right _ _
  calc δ * ‖b - a‖ ≤ ε / (2 * ‖b - a‖) * ‖b - a‖ := by gcongr
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- Step 1 of the blueprint proof of
`uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover`: if a
nonempty convex far region is not contained in one tile, an exit point lies in
the relative interiors of two collinear tile sides, with all four endpoints
still far away. -/
private lemma uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover_step1_exit
    (M : MacroPatch P) {W : Set Pt} {d : ℝ}
    (hWconv : Convex ℝ W) (hWnonempty : W.Nonempty)
    (hWsub : W ⊆ support M.tiles)
    (hNoTile : ∀ A ∈ M.tiles, ¬ W ⊆ A.carrier) (hd : 0 < d)
    (hfar : ∀ x ∈ W, ∀ v, IsVertexOf M.tiles v → d / 2 ≤ dist x v) :
    ∃ A B i j e, A ∈ M.tiles ∧ B ∈ M.tiles ∧
      Disjoint (interior A.carrier) (interior B.carrier) ∧ e ∈ W ∧
      e ∈ A.side i ∧ e ∈ B.side j ∧
      Collinear ℝ ({A.vertex i, A.vertex (finRotate _ i),
        B.vertex j, B.vertex (finRotate _ j)} : Set Pt) ∧
      d / 2 ≤ dist e (A.vertex i) ∧
      d / 2 ≤ dist e (A.vertex (finRotate _ i)) ∧
      d / 2 ≤ dist e (B.vertex j) ∧
      d / 2 ≤ dist e (B.vertex (finRotate _ j)) := by
  obtain ⟨p, hpW⟩ := hWnonempty
  have hpsupp : p ∈ support M.tiles := hWsub hpW
  rw [support, mem_iUnion₂] at hpsupp
  obtain ⟨A, hA, hpA⟩ := hpsupp
  have hAW : ¬ W ⊆ A.carrier := hNoTile A hA
  rw [Set.not_subset] at hAW
  obtain ⟨q, hqW, hqA⟩ := hAW
  have hpq : p ≠ q := fun h => hqA (h ▸ hpA)
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ p + t • (q - p) ∈ A.carrier} with hS_def
  have hSclosed : IsClosed S := isClosed_Icc.inter ((macro_tile_closed A).preimage (by fun_prop))
  have hSne : S.Nonempty := ⟨0, ⟨le_refl 0, zero_le_one⟩, by simpa using hpA⟩
  have hSbdd : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  have ht0S : sSup S ∈ S := hSclosed.csSup_mem hSne hSbdd
  set t0 := sSup S with ht0_def
  obtain ⟨ht0_mem, ht0A⟩ := ht0S
  have ht0_lt1 : t0 < 1 := by
    rcases eq_or_lt_of_le ht0_mem.2 with h | h
    · exfalso
      apply hqA
      have hqeq : q = p + t0 • (q - p) := by rw [h]; module
      rw [hqeq]
      exact ht0A
    · exact h
  have hnotA : ∀ t : ℝ, t0 < t → t ≤ 1 → p + t • (q - p) ∉ A.carrier := by
    intro t ht0t ht1 hmem
    have htS : t ∈ S := ⟨⟨by linarith [ht0_mem.1], ht1⟩, hmem⟩
    have hle : t ≤ sSup S := le_csSup hSbdd htS
    rw [← ht0_def] at hle
    linarith
  have heW : p + t0 • (q - p) ∈ W := by
    have hseg : p + t0 • (q - p) ∈ segment ℝ p q :=
      crown_mem_segment_iff.mpr ⟨t0, ht0_mem.1, ht0_mem.2, rfl⟩
    exact (hWconv.segment_subset hpW hqW) hseg
  have hCclosed : IsClosed (support (M.tiles \ {A})) :=
    M.finite.diff.isClosed_biUnion (fun A' _ => macro_tile_closed A')
  have hAB_in : ∀ t : ℝ, t0 < t → t ≤ 1 → p + t • (q - p) ∈ support (M.tiles \ {A}) := by
    intro t ht0t ht1
    have hseg : p + t • (q - p) ∈ segment ℝ p q :=
      crown_mem_segment_iff.mpr ⟨t, by linarith [ht0_mem.1], ht1, rfl⟩
    have hWmem : p + t • (q - p) ∈ W := (hWconv.segment_subset hpW hqW) hseg
    have hsupp : p + t • (q - p) ∈ support M.tiles := hWsub hWmem
    rw [support, mem_iUnion₂] at hsupp
    obtain ⟨A', hA', hA'mem⟩ := hsupp
    have hA'neA : A' ≠ A := by
      intro h
      apply hnotA t ht0t ht1
      rw [← h]
      exact hA'mem
    rw [support, mem_iUnion₂]
    exact ⟨A', Set.mem_diff_singleton.mpr ⟨hA', hA'neA⟩, hA'mem⟩
  have heC : p + t0 • (q - p) ∈ support (M.tiles \ {A}) :=
    uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover_step1_exit_aux2
      hCclosed hpq ht0_lt1 hAB_in
  set e := p + t0 • (q - p) with he_def
  rw [support, mem_iUnion₂] at heC
  obtain ⟨B, hBdiff, heB⟩ := heC
  have hB : B ∈ M.tiles := (Set.mem_diff_singleton.mp hBdiff).1
  have hBneA : B ≠ A := (Set.mem_diff_singleton.mp hBdiff).2
  have hvA : e ∉ A.vertexSet := by
    rintro ⟨k, hk⟩
    have hvertex : IsVertexOf M.tiles (A.vertex k) := ⟨A, hA, ⟨k, rfl⟩⟩
    have hd2 := hfar _ heW _ hvertex
    rw [hk, dist_self] at hd2
    linarith
  have hvB : e ∉ B.vertexSet := by
    rintro ⟨k, hk⟩
    have hvertex : IsVertexOf M.tiles (B.vertex k) := ⟨B, hB, ⟨k, rfl⟩⟩
    have hd2 := hfar _ heW _ hvertex
    rw [hk, dist_self] at hd2
    linarith
  have hdisjAB : Disjoint (interior A.carrier) (interior B.carrier) :=
    M.disjoint hA hB (Ne.symm hBneA)
  obtain ⟨i, j, heAi, heBj, hoverlap⟩ :=
    macro_tiles_share_local_side hdisjAB ht0A heB hvA hvB
  obtain ⟨x, y, hxy, hsub⟩ := hoverlap
  have hxAi : x ∈ A.side i := (hsub (left_mem_segment ℝ x y)).1
  have hyAi : y ∈ A.side i := (hsub (right_mem_segment ℝ x y)).1
  have hxBj : x ∈ B.side j := (hsub (left_mem_segment ℝ x y)).2
  have hyBj : y ∈ B.side j := (hsub (right_mem_segment ℝ x y)).2
  rw [macro_tile_side_eq] at hxAi hyAi hxBj hyBj
  have hcol : Collinear ℝ ({A.vertex i, A.vertex (finRotate _ i),
      B.vertex j, B.vertex (finRotate _ j)} : Set Pt) :=
    uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover_step1_exit_aux1
      hxy hxAi hyAi hxBj hyBj
  have hAi_far : d / 2 ≤ dist e (A.vertex i) := hfar e heW (A.vertex i) ⟨A, hA, ⟨i, rfl⟩⟩
  have hArot_far : d / 2 ≤ dist e (A.vertex (finRotate _ i)) :=
    hfar e heW _ ⟨A, hA, ⟨finRotate _ i, rfl⟩⟩
  have hBj_far : d / 2 ≤ dist e (B.vertex j) := hfar e heW _ ⟨B, hB, ⟨j, rfl⟩⟩
  have hBrot_far : d / 2 ≤ dist e (B.vertex (finRotate _ j)) :=
    hfar e heW _ ⟨B, hB, ⟨finRotate _ j, rfl⟩⟩
  exact ⟨A, B, i, j, e, hA, hB, hdisjAB, heW, heAi, heBj, hcol,
    hAi_far, hArot_far, hBj_far, hBrot_far⟩

/-- Step 2 of the blueprint proof of
`uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover`: an
edge crossing supplied by Step 1 has an endpoint whose full patch crown
contains both incident tiles. -/
private lemma uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover_step2_endpoint
    (M : MacroPatch P) {A B : PlacedTile P} {d : ℝ}
    (hA : A ∈ M.tiles) (hB : B ∈ M.tiles)
    (hdisj : Disjoint (interior A.carrier) (interior B.carrier))
    {i : Fin (P.disk A.form).n} {j : Fin (P.disk B.form).n} {e : Pt}
    (hei : e ∈ A.side i) (hej : e ∈ B.side j)
    (hcol : Collinear ℝ ({A.vertex i, A.vertex (finRotate _ i),
      B.vertex j, B.vertex (finRotate _ j)} : Set Pt))
    (hAi : d / 2 ≤ dist e (A.vertex i))
    (hArot : d / 2 ≤ dist e (A.vertex (finRotate _ i)))
    (hBj : d / 2 ≤ dist e (B.vertex j))
    (hBrot : d / 2 ≤ dist e (B.vertex (finRotate _ j))) :
    ∃ v, IsVertexOf M.tiles v ∧ A ∈ crown M.tiles v ∧ B ∈ crown M.tiles v := by
  have _ := hdisj
  have _ := hAi
  have _ := hArot
  have _ := hBj
  have _ := hBrot
  obtain ⟨v, hv, hvA, hvB⟩ :=
    uniformCrownCoverPlane_step2_far_step3_shared_vertex i j hei hej hcol
  have hvM : IsVertexOf M.tiles v := by
    rcases hv with h | h | h | h
    · exact ⟨A, hA, by rw [h]; exact Set.mem_range_self i⟩
    · exact ⟨A, hA, by rw [h]; exact Set.mem_range_self (finRotate _ i)⟩
    · exact ⟨B, hB, by rw [h]; exact Set.mem_range_self j⟩
    · exact ⟨B, hB, by rw [h]; exact Set.mem_range_self (finRotate _ j)⟩
  exact ⟨v, hvM, ⟨hA, hvA⟩, ⟨hB, hvB⟩⟩

/-- Step 3 of the blueprint proof of
`uniformCrownCoverSupertile_step3_epsilon_and_case2`: after convexification and
the exterior-excursion step, the trimmed two-tile argument selects one full
crown covering the far region. -/
private lemma uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover
    {𝒞 : Set (Set (PlacedTile P))} (h𝒞 : IsCatalogue 𝒞)
    {r δ d η : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hrδ : SectorRadiusProperty 𝒞 r δ) (hd : 0 < d) (hη : 0 < η)
    (hη_ball : ∀ (A B : PlacedTile P),
      Disjoint (interior A.carrier) (interior B.carrier) →
      ∀ (i : Fin (P.disk A.form).n) (j : Fin (P.disk B.form).n) (e : Pt),
        e ∈ A.side i → e ∈ B.side j →
        Collinear ℝ ({A.vertex i, A.vertex (finRotate _ i),
          B.vertex j, B.vertex (finRotate _ j)} : Set Pt) →
        d / 2 ≤ dist e (A.vertex i) →
        d / 2 ≤ dist e (A.vertex (finRotate _ i)) →
        d / 2 ≤ dist e (B.vertex j) →
        d / 2 ≤ dist e (B.vertex (finRotate _ j)) →
        ball e η ⊆ A.carrier ∪ B.carrier)
    (M : MacroPatch P) (hM : AllCrownsIn 𝒞 M.tiles) {H : Set Pt}
    (hHconv : Convex ℝ H) (hHbound : Bornology.IsBounded H)
    (hHdiam : diam H < η)
    (hfar : ∀ x ∈ H, ∀ v, IsVertexOf M.tiles v →
      d / 2 ≤ dist x v)
    (hHregion : Convex ℝ (H ∩ support M.tiles)) :
    ∃ v, IsVertexOf M.tiles v ∧
      H ∩ support M.tiles ⊆ support (crown M.tiles v) := by
  have _ := h𝒞
  have _ := hr
  have _ := hδ
  have _ := hrδ
  have _ := hη
  have _ := hM
  have _ := hHconv
  obtain ⟨v₀, hv₀⟩ :=
    uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover_step0_vertex M
  let W : Set Pt := H ∩ support M.tiles
  by_cases hW : W.Nonempty
  · have hWconv : Convex ℝ W := by
      simpa [W] using hHregion
    have hWsub : W ⊆ support M.tiles := fun x hx => hx.2
    by_cases htile : ∃ A ∈ M.tiles, W ⊆ A.carrier
    · obtain ⟨A, hA, hWA⟩ := htile
      let i : Fin (P.disk A.form).n :=
        ⟨0, by have := (P.disk A.form).three_le; omega⟩
      let v := A.vertex i
      have hvA : v ∈ A.vertexSet := by
        exact ⟨i, rfl⟩
      have hv : IsVertexOf M.tiles v := ⟨A, hA, hvA⟩
      refine ⟨v, hv, ?_⟩
      intro x hx
      have hxA : x ∈ A.carrier := hWA hx
      rw [support, mem_iUnion₂]
      exact ⟨A, ⟨hA, gap_vertex_mem_carrier A hvA⟩, hxA⟩
    · have hNoTile : ∀ A ∈ M.tiles, ¬ W ⊆ A.carrier := by
        intro A hA hWA
        exact htile ⟨A, hA, hWA⟩
      have hfarW : ∀ x ∈ W, ∀ v, IsVertexOf M.tiles v →
          d / 2 ≤ dist x v := by
        intro x hx v hv
        exact hfar x hx.1 v hv
      obtain ⟨A, B, i, j, e, hA, hB, hdisj, heW, hei, hej, hcol,
          hAi, hArot, hBj, hBrot⟩ :=
        uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover_step1_exit
          M hWconv hW hWsub hNoTile hd hfarW
      obtain ⟨v, hv, hAcrown, hBcrown⟩ :=
        uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover_step2_endpoint
          M hA hB hdisj hei hej hcol hAi hArot hBj hBrot
      have hball : ball e η ⊆ A.carrier ∪ B.carrier :=
        hη_ball A B hdisj i j e hei hej hcol hAi hArot hBj hBrot
      have hWball : W ⊆ ball e η := by
        intro x hx
        have hxe : dist x e ≤ diam H := dist_le_diam_of_mem hHbound hx.1 heW.1
        exact mem_ball.mpr (hxe.trans_lt hHdiam)
      refine ⟨v, hv, ?_⟩
      intro x hx
      have hxAB : x ∈ A.carrier ∪ B.carrier := hball (hWball ⟨hx.1, hx.2⟩)
      rw [support, mem_iUnion₂]
      rcases hxAB with hxA | hxB
      · exact ⟨A, hAcrown, hxA⟩
      · exact ⟨B, hBcrown, hxB⟩
  · refine ⟨v₀, hv₀, ?_⟩
    intro x hx
    exact False.elim (hW ⟨x, hx⟩)

/-- Step 3 of the blueprint proof of `uniformCrownCoverSupertile`: convex hull stays far. -/
private lemma uniformCrownCoverSupertile_step3_epsilon_and_case2
    {𝒞 : Set (Set (PlacedTile P))} (h𝒞 : IsCatalogue 𝒞)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hrδ : SectorRadiusProperty 𝒞 r δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ crownRadius r δ (rootSeparationConstants P) / 2 ∧
    ∀ (M : MacroPatch P) (_hM : AllCrownsIn 𝒞 M.tiles)
    {S : Set Pt} (_hS_bound : Bornology.IsBounded S), diam S < ε →
    (∀ x ∈ closedConvexHull ℝ S, ∀ v, IsVertexOf M.tiles v →
      crownRadius r δ (rootSeparationConstants P) / 2 ≤ dist x v) →
    ∃ v, IsVertexOf M.tiles v ∧ S ∩ support M.tiles ⊆ support (crown M.tiles v) := by
  obtain ⟨d, η, ε, hd, hη, hd_eq, hε, hε_crown, hε_eta, hε_lam, hε_sin,
      hη_ball⟩ :=
    uniformCrownCoverSupertile_step3_epsilon_and_case2_step1_constants hr hδ
  refine ⟨ε, hε, hε_crown, ?_⟩
  intro M hM S hS_bound hS_diam hfar
  obtain ⟨H, hH, hHconv, hHbound, hHdiam, hSsub⟩ :=
    uniformCrownCoverSupertile_step3_epsilon_and_case2_step2_hull hS_bound hS_diam
  have hfar' : ∀ x ∈ H, ∀ v, IsVertexOf M.tiles v → d / 2 ≤ dist x v := by
    simpa [hH, hd_eq] using hfar
  have hHregion := uniformCrownCoverSupertile_step3_epsilon_and_case2_step2_convex
    hd hε_lam hε_sin M hHconv hHbound hHdiam hfar'
  obtain ⟨v, hv, hcover⟩ :=
    uniformCrownCoverSupertile_step3_epsilon_and_case2_step3_crown_cover
      h𝒞 hr hδ hrδ hd hη hη_ball M hM hHconv hHbound
      (hHdiam.trans_le hε_eta) hfar' hHregion
  refine ⟨v, hv, ?_⟩
  intro x hx
  exact hcover ⟨hSsub hx.1, hx.2⟩

/-- `lem:crown-cover-supertile`: there is `ε > 0` such that for every macro
patch whose full pointed crowns (including incomplete boundary crowns) are
represented, every bounded `S` of diameter `< ε` has `S ∩ R` inside the
support of one full crown of the patch. -/
theorem uniformCrownCoverSupertile {𝒞 : Set (Set (PlacedTile P))} (h𝒞 : IsCatalogue 𝒞) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : MacroPatch P, AllCrownsIn 𝒞 M.tiles →
      ∀ S : Set Pt, Bornology.IsBounded S → diam S < ε →
        ∃ v, IsVertexOf M.tiles v ∧ S ∩ support M.tiles ⊆ support (crown M.tiles v) := by
  obtain ⟨r, δ, hr, hδ, hrδ, hd_pos⟩ := uniformCrownCoverSupertile_step1_radius h𝒞
  obtain ⟨ε, hε_pos, hε_d, h_far_case⟩ :=
    uniformCrownCoverSupertile_step3_epsilon_and_case2 h𝒞 hr hδ hrδ
  use ε, hε_pos
  intro M hM S hS_bound hdiam
  by_cases h_near : ∃ x ∈ closedConvexHull ℝ S, ∃ v, IsVertexOf M.tiles v ∧
    dist x v < crownRadius r δ (rootSeparationConstants P) / 2
  · rcases h_near with ⟨x, hx, v, hv, hdist⟩
    have h_subset := uniformCrownCoverSupertile_step2_case1
      hr hδ hrδ M hM hS_bound hε_d hdiam v hv ⟨x, hx, hdist⟩
    exact ⟨v, hv, h_subset⟩
  · push_neg at h_near
    have _ := hd_pos
    exact h_far_case M hM hS_bound hdiam h_near

/-! ## `lem:pointed-flc` -/

/-- The article's unpointed FLC: finitely many allowed full crown patches up
to translation (the centre is forgotten). -/
def UnpointedFLC (τ : Substitution P) : Prop :=
  ∃ 𝒦 : Set (Set (PlacedTile P)), 𝒦.Finite ∧
    ∀ (n : ℕ) (p : P.Form) (w : Pt), IsVertexOf (τ.supertile n p) w →
      ∃ K ∈ 𝒦, ∃ u : Pt, crown (τ.supertile n p) w = translateSet u K

private lemma pointedFLCOfFLC_step1_choose_finite_patches_translateSet_add
    (S : Set (PlacedTile P)) (u v : Pt) :
    translateSet v (translateSet u S) = translateSet (v + u) S := by
  rw [translateSet, translateSet, translateSet, Set.image_image]
  congr 1
  funext A
  simp [PlacedTile.translate, vadd_eq_add, add_assoc]

/-- Step 1 of the blueprint proof of `pointedFLCOfFLC`:
Choose one finite patch for each unpointed translation class. -/
private lemma pointedFLCOfFLC_step1_choose_finite_patches (P : Protoset) (τ : Substitution P)
  (h : UnpointedFLC τ) :
  ∃ f : Set (PlacedTile P) → Pt, ∀ K ∈ {K | τ.IsAllowedCrown K},
    ∃ K' ∈ Classical.choose h, K = translateSet (f K) K' := by
  classical
  have hcov := (Classical.choose_spec h).2
  have key : ∀ K : Set (PlacedTile P), ∃ v : Pt,
      τ.IsAllowedCrown K → ∃ K' ∈ Classical.choose h, K = translateSet v K' := by
    intro K
    by_cases hK : τ.IsAllowedCrown K
    · obtain ⟨n, p, w, hvw, hKeq⟩ := hK
      obtain ⟨K', hK'mem, u, hueq⟩ := hcov n p w hvw
      refine ⟨-w + u, fun _ => ⟨K', hK'mem, ?_⟩⟩
      rw [hKeq, hueq]
      exact pointedFLCOfFLC_step1_choose_finite_patches_translateSet_add K' u (-w)
    · exact ⟨0, fun h' => absurd h' hK⟩
  choose f hf using key
  exact ⟨f, hf⟩

private lemma pointedFLCOfFLC_step2_finite_centres_translate_vertex_iff
  (A : PlacedTile P) (v x : Pt) :
    x ∈ (A.translate v).vertexSet ↔ x - v ∈ A.vertexSet := by
  dsimp [PlacedTile.vertexSet, PlacedTile.vertex, PlacedTile.translate]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp only [PlacedTile.vertex, vadd_eq_add] at hi ⊢
    change A.anchor + (P.disk A.form).vertex i = x - v
    calc
      A.anchor + (P.disk A.form).vertex i = -v +
          (v + A.anchor + (P.disk A.form).vertex i) := by abel
      _ = -v + x := by rw [hi]
      _ = x - v := by abel
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp only [PlacedTile.vertex, vadd_eq_add] at hi ⊢
    change A.anchor + (P.disk A.form).vertex i = x - v at hi
    calc
      v + A.anchor + (P.disk A.form).vertex i =
          v + (A.anchor + (P.disk A.form).vertex i) := by abel
      _ = v + (x - v) := by rw [hi]
      _ = x := by abel

/-- Step 2 of the blueprint proof of `pointedFLCOfFLC`:
A crown centre is a listed vertex of at least one of its tiles, so each chosen patch has only finitely many possible centres. -/
private lemma pointedFLCOfFLC_step2_finite_centres (P : Protoset) (τ : Substitution P)
  (h : UnpointedFLC τ) (f : Set (PlacedTile P) → Pt)
  (hf : ∀ K ∈ {K | τ.IsAllowedCrown K}, ∃ K' ∈ Classical.choose h, K = translateSet (f K) K') :
  ∀ K' ∈ Classical.choose h, {u | ∃ K ∈ {K | τ.IsAllowedCrown K}, f K = u ∧ K = translateSet u K'}.Finite := by
  intro K' hK'
  have _ := h
  have _ := hf
  have _ := hK'
  by_cases hnonempty :
      {u | ∃ K ∈ {K | τ.IsAllowedCrown K}, f K = u ∧ K = translateSet u K'}.Nonempty
  · obtain ⟨u₀, K₀, hK₀, hfu₀, hK₀_eq⟩ := hnonempty
    have hK₀fin : K₀.Finite := by
      rcases hK₀ with ⟨n, p, w, hw, rfl⟩
      apply Set.Finite.image
      exact (supertile_finite τ n p).subset (fun A hA => hA.1)
    have hK'fin : K'.Finite := by
      rw [← gap_translateSet_neg K' (-u₀)]
      simp only [neg_neg]
      rw [← hK₀_eq]
      exact hK₀fin.image _
    have hfin : {u : Pt | ∃ B ∈ K', -u ∈ B.vertexSet}.Finite := by
      apply Set.Finite.subset
        (Set.Finite.biUnion hK'fin (fun B _ =>
          (Set.finite_range B.vertex).image (fun v : Pt => -v)))
      intro u hu
      rcases hu with ⟨B, hB, huB⟩
      refine Set.mem_iUnion.mpr ⟨B, Set.mem_iUnion.mpr ⟨hB, ?_⟩⟩
      exact ⟨-u, huB, by simp⟩
    apply hfin.subset
    intro u hu
    rcases hu with ⟨K, hK, hfu, hK_eq⟩
    rcases hK with ⟨n, p, w, hw, rfl⟩
    rcases hw with ⟨A, hA, hwA⟩
    have hAw : w ∈ A.carrier := gap_vertex_mem_carrier A hwA
    have hAcrown : A ∈ crown (τ.supertile n p) w := ⟨hA, hAw⟩
    have hA0 : 0 ∈ (A.translate (-w)).vertexSet := by
      exact (pointedFLCOfFLC_step2_finite_centres_translate_vertex_iff A (-w) 0).mpr
        (by simpa using hwA)
    have hA_mem : A.translate (-w) ∈ translateSet (-w)
        (crown (τ.supertile n p) w) := ⟨A, hAcrown, rfl⟩
    rw [hK_eq] at hA_mem
    rcases hA_mem with ⟨B, hB, hBA⟩
    refine ⟨B, hB, ?_⟩
    have hBA' : B.translate u = A.translate (-w) := hBA
    have hB0 : 0 ∈ (B.translate u).vertexSet := by
      rw [hBA']
      exact hA0
    have hBu :=
      (pointedFLCOfFLC_step2_finite_centres_translate_vertex_iff B u 0).mp hB0
    simpa using hBu
  · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty]
    exact Set.finite_empty

/-- `lem:pointed-flc`: finitely many unpointed translation classes of allowed
crowns give finitely many pointed ones. -/
theorem pointedFLCOfFLC (τ : Substitution P) (h : UnpointedFLC τ) : τ.FLC := by
  dsimp [FLC]
  obtain ⟨f, hf⟩ := pointedFLCOfFLC_step1_choose_finite_patches P τ h
  have h1 : {K | τ.IsAllowedCrown K} ⊆
      ⋃ K' ∈ Classical.choose h, (fun u => translateSet u K') ''
        {u | ∃ K ∈ {K | τ.IsAllowedCrown K}, f K = u ∧ K = translateSet u K'} := by
    intro K hK
    rcases hf K hK with ⟨K', hK', hKeq⟩
    rw [Set.mem_iUnion₂]
    exact ⟨K', hK', f K, ⟨K, hK, rfl, hKeq⟩, hKeq.symm⟩
  apply Set.Finite.subset _ h1
  apply Set.Finite.biUnion (Classical.choose_spec h).1
  intro K' hK'
  apply Set.Finite.image
  exact pointedFLCOfFLC_step2_finite_centres P τ h f hf K' hK'

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

section AllowedHierarchy

open Substitution Crowns

/-- Step 1 of the blueprint proof of `allowed_crowns_hierarchy_is_substitutive_step1_radius`:
There exists an `ε > 0` bounding the diameter for uniform crown covers. -/
private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step1_epsilon
    (τ : Substitution P) (hflc : τ.FLC) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ T : PlaneTiling P,
        (∀ v, IsVertexOf T.tiles v → τ.IsAllowedCrown (translateSet (-v) (crown T.tiles v))) →
        ∀ S : Set Pt, Bornology.IsBounded S → Metric.diam S < ε →
          ∃ v, IsVertexOf T.tiles v ∧ S ⊆ support (crown T.tiles v) := by
  have hc : IsCatalogue (pointedCatalogue τ) := isCatalogue_pointedCatalogue τ hflc
  obtain ⟨ε, hε_pos, hcover⟩ := uniformCrownCoverPlane hc
  use ε, hε_pos
  intro T hcrown S hS_b hS_diam
  have h_all : AllCrownsIn (pointedCatalogue τ) T.tiles := by
    intro v hv
    exact hcrown v hv
  exact hcover T h_all S hS_b hS_diam

/-- Step 2 of the blueprint proof of `allowed_crowns_hierarchy_is_substitutive_step1_radius`:
Since the patch `F` is finite, its support is bounded and has a finite diameter.
Thus we can choose an integer `k` such that `θ^{-km} * diam(support F) < ε`. -/
private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step2_k
    (τ : Substitution P) (ε : ℝ) (hε : 0 < ε)
    (F : Set (PlacedTile P)) (hF_fin : F.Finite) (m : ℕ) (hm : 0 < m) :
    ∃ k : ℕ, (τ.θ ^ (k * m))⁻¹ * Metric.diam (support F) < ε := by
  have _ := hF_fin
  let D := Metric.diam (support F)
  have hD : 0 ≤ D := Metric.diam_nonneg
  have hD1 : 0 < D + 1 := by linarith
  have hθm : 1 < τ.θ ^ m := one_lt_pow₀ τ.one_lt (Nat.ne_of_gt hm)
  have hθm_pos : 0 < τ.θ ^ m := pow_pos (lt_trans zero_lt_one τ.one_lt) m
  have hq_pos : 0 < (τ.θ ^ m)⁻¹ :=
    inv_pos.mpr hθm_pos
  have hq_lt : (τ.θ ^ m)⁻¹ < 1 := (inv_lt_one₀ hθm_pos).2 hθm
  have hx_pos : 0 < ε / (D + 1) := div_pos hε hD1
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hx_pos hq_lt
  refine ⟨k, ?_⟩
  have hq_nonneg : 0 ≤ ((τ.θ ^ m)⁻¹) ^ k := (pow_nonneg hq_pos.le k)
  have hD_le : D ≤ D + 1 := by linarith
  have hmul_le : ((τ.θ ^ m)⁻¹) ^ k * D ≤
      ((τ.θ ^ m)⁻¹) ^ k * (D + 1) :=
    mul_le_mul_of_nonneg_left hD_le hq_nonneg
  have hmul_lt : ((τ.θ ^ m)⁻¹) ^ k * (D + 1) <
      (ε / (D + 1)) * (D + 1) :=
    mul_lt_mul_of_pos_right hk hD1
  have hratio : (ε / (D + 1)) * (D + 1) = ε := by
    field_simp
  have hpow : τ.θ ^ (k * m) = (τ.θ ^ m) ^ k := by
    rw [Nat.mul_comm, pow_mul]
  change (τ.θ ^ (k * m))⁻¹ * D < ε
  rw [hpow, ← inv_pow]
  exact hmul_le.trans_lt (hmul_lt.trans_eq hratio)


private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step3_cover_step1_bounded
    {P : Protoset} (F : Set (PlacedTile P)) (hF_fin : F.Finite) :
    Bornology.IsBounded (support F) := by
  have h_eq : support F = ⋃ (t ∈ F), t.carrier := by
    ext x
    simp [support, PlacedTile.carrier]
  rw [h_eq]
  exact (hF_fin.isCompact_biUnion (fun t _ => by
    dsimp [PlacedTile.carrier, PlacedTile.translate]
    rw [← Set.image_vadd]
    exact (P.disk t.form).compact.image (continuous_const_vadd t.anchor)
  )).isBounded

private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step3_cover_step2_diam
    (c : ℝ) (hc : 0 ≤ c) (S : Set Pt) (h_bound : Bornology.IsBounded S) :
    Metric.diam ((fun x => c • x) '' S) = c * Metric.diam S := by
  have : ‖c‖₊ = ⟨c, hc⟩ := by ext; exact Real.norm_of_nonneg hc
  have hl : LipschitzWith ⟨c, hc⟩ (fun x : Pt => c • x) := by
    rw [← this]
    exact lipschitzWith_smul c
  rcases eq_or_lt_of_le hc with rfl | hc_pos
  · rcases Set.eq_empty_or_nonempty S with rfl | ⟨x, hx⟩
    · simp
    · have h_eq : (fun (a : Pt) => (0 : ℝ) • a) '' S = {0} := by
        ext y
        simp only [zero_smul, Set.mem_image, Set.mem_singleton_iff]
        constructor
        · rintro ⟨a, _ha, rfl⟩; rfl
        · rintro rfl; exact ⟨x, hx, rfl⟩
      rw [h_eq]
      simp
  · apply le_antisymm
    · exact hl.diam_image_le S h_bound
    · have hl_inv : LipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc⟩ (fun x : Pt => c⁻¹ • x) := by
        have : ‖c⁻¹‖₊ = ⟨c⁻¹, inv_nonneg.mpr hc⟩ := by
          ext; exact Real.norm_of_nonneg (inv_nonneg.mpr hc)
        rw [← this]
        exact lipschitzWith_smul c⁻¹
      have h_bound_inv : Bornology.IsBounded ((fun x => c • x) '' S) := (hl.isBounded_image h_bound)
      have h2 := hl_inv.diam_image_le ((fun x => c • x) '' S) h_bound_inv
      have h_eq : (fun (x : Pt) => c⁻¹ • x) '' ((fun (x : Pt) => c • x) '' S) = S := by
        ext y
        simp only [Set.mem_image]
        constructor
        · rintro ⟨y1, ⟨y2, hy2, rfl⟩, rfl⟩
          rw [← mul_smul, inv_mul_cancel₀ (ne_of_gt hc_pos), one_smul]
          exact hy2
        · rintro hy
          have h_inv : c⁻¹ * c = 1 := inv_mul_cancel₀ (ne_of_gt hc_pos)
          exact ⟨c • y, ⟨y, hy, rfl⟩, by rw [← mul_smul, h_inv, one_smul]⟩
      rw [h_eq] at h2
      have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt hc_pos)
      have hc_coe : (NNReal.toReal ⟨c⁻¹, inv_nonneg.mpr hc⟩) = c⁻¹ := rfl
      rw [hc_coe, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc_pos), one_mul] at h3
      exact h3

private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step3_cover_step3_bounded
    {P : Protoset} (τ : Substitution P) (m : ℕ) (k : ℕ) (F : Set (PlacedTile P))
    (hF_fin : F.Finite) :
    Bornology.IsBounded ((fun x => (τ.θ ^ (k * m))⁻¹ • x) '' support F) := by
  have h_pos : 0 ≤ (τ.θ ^ (k * m))⁻¹ := by
    apply inv_nonneg.mpr
    apply pow_nonneg
    exact le_of_lt (lt_trans zero_lt_one τ.one_lt)
  have hl : LipschitzWith ⟨(τ.θ ^ (k * m))⁻¹, h_pos⟩ (fun x : Pt => (τ.θ ^ (k * m))⁻¹ • x) := by
    have h_norm : ‖(τ.θ ^ (k * m))⁻¹‖₊ = ⟨(τ.θ ^ (k * m))⁻¹, h_pos⟩ := by
      ext; exact Real.norm_of_nonneg h_pos
    rw [← h_norm]
    exact lipschitzWith_smul (τ.θ ^ (k * m))⁻¹
  have h_bound :=
    allowed_crowns_hierarchy_is_substitutive_step1_radius_step3_cover_step1_bounded F hF_fin
  exact hl.isBounded_image h_bound

/-- Step 3 of the blueprint proof of `allowed_crowns_hierarchy_is_substitutive_step1_radius`:
By the choice of `k`, the inverse-scaled support of `F` is covered by a crown `C` of `seq k`
(playing the role of `T_{km}`). -/
private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step3_cover
    (τ : Substitution P) (m : ℕ) (seq : ℕ → PlaneTiling P)
    (hcrown : ∀ k (w : Pt), IsVertexOf (seq k).tiles w →
      τ.IsAllowedCrown (translateSet (-w) (crown (seq k).tiles w)))
    (F : Set (PlacedTile P)) (k : ℕ)
    (ε : ℝ) (h_cover : ∀ T : PlaneTiling P,
        (∀ v, IsVertexOf T.tiles v → τ.IsAllowedCrown (translateSet (-v) (crown T.tiles v))) →
        ∀ S : Set Pt, Bornology.IsBounded S → Metric.diam S < ε →
          ∃ v, IsVertexOf T.tiles v ∧ S ⊆ support (crown T.tiles v))
    (hk : (τ.θ ^ (k * m))⁻¹ * Metric.diam (support F) < ε)
    (hF_fin : F.Finite) :
    ∃ w : Pt, IsVertexOf (seq k).tiles w ∧
      (fun x => (τ.θ ^ (k * m))⁻¹ • x) '' support F ⊆ support (crown (seq k).tiles w) := by
  let S := (fun x => (τ.θ ^ (k * m))⁻¹ • x) '' support F
  have hS_bound : Bornology.IsBounded S :=
    allowed_crowns_hierarchy_is_substitutive_step1_radius_step3_cover_step3_bounded τ m k F hF_fin
  have h_pos : 0 ≤ (τ.θ ^ (k * m))⁻¹ := by
    apply inv_nonneg.mpr
    apply pow_nonneg
    exact le_of_lt (lt_trans zero_lt_one τ.one_lt)
  have hS_diam : Metric.diam S < ε := by
    have h_bound :=
      allowed_crowns_hierarchy_is_substitutive_step1_radius_step3_cover_step1_bounded F hF_fin
    have h_diam_eq := allowed_crowns_hierarchy_is_substitutive_step1_radius_step3_cover_step2_diam
      (τ.θ ^ (k * m))⁻¹ h_pos (support F) h_bound
    rw [h_diam_eq]
    exact hk
  rcases h_cover (seq k) (hcrown k) S hS_bound hS_diam with ⟨v, hv, h_subset⟩
  exact ⟨v, hv, h_subset⟩

/-- Step 1 of the blueprint proof of `allowed_crowns_hierarchy_is_substitutive_step1_radius_step4_supp`:
The support of `k` iterations of decomposition on a set of tiles `S`
is the support of `S` scaled by `θ^k`. -/
private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step4_supp_iter_aux0
    (v : Pt) (S : Set (PlacedTile P)) :
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

private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step4_supp_iter_aux2
    (τ : Substitution P) (A : PlacedTile P) :
    support (τ.decomposeTile A) = τ.θ • A.carrier := by
  dsimp [Substitution.decomposeTile]
  rw [allowed_crowns_hierarchy_is_substitutive_step1_radius_step4_supp_iter_aux0,
    τ.support_eq, PlacedTile.carrier]
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

private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step4_supp_iter_aux3
    (τ : Substitution P) (S : Set (PlacedTile P)) :
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
    rw [allowed_crowns_hierarchy_is_substitutive_step1_radius_step4_supp_iter_aux2]
      at h
    exact h
  · rintro ⟨A, hA, hx⟩
    have h : x ∈ support (τ.decomposeTile A) := by
      rw [allowed_crowns_hierarchy_is_substitutive_step1_radius_step4_supp_iter_aux2]
      exact hx
    simp only [support, Set.mem_iUnion] at h
    rcases h with ⟨B, hB, hx'⟩
    exact ⟨B, ⟨A, hA, hB⟩, hx'⟩

private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step4_supp_iter
    (τ : Substitution P) (k : ℕ) (S : Set (PlacedTile P)) :
    support (τ.decomposeIter k S) = τ.θ ^ k • support S := by
  induction k with
  | zero => simp [Substitution.decomposeIter]
  | succ k ih =>
      change support (τ.decompose (τ.decomposeIter k S)) =
        τ.θ ^ (k + 1) • support S
      rw [allowed_crowns_hierarchy_is_substitutive_step1_radius_step4_supp_iter_aux3,
        ih, smul_smul, pow_succ']

/-- Step 4 of the blueprint proof of `allowed_crowns_hierarchy_is_substitutive_step1_radius`:
Because the inverse-scaled support of `F` is covered by a crown of `seq k`,
the actual support of `F` is covered by the support of the descendant patch `τ^{km} C`. -/
private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step4_supp
    (τ : Substitution P) (m : ℕ) (hm : 0 < m) (seq : ℕ → PlaneTiling P)
    (hseq : ∀ k, (τ.pow m hm).IsComposition (seq (k + 1)) (seq k))
    (F : Set (PlacedTile P)) (hF : F ⊆ (seq 0).tiles) (k : ℕ)
    (w : Pt) (hw : IsVertexOf (seq k).tiles w)
    (h_cover : (fun x => (τ.θ ^ (k * m))⁻¹ • x) '' support F ⊆ support (crown (seq k).tiles w)) :
    support F ⊆ support (τ.decomposeIter (k * m) (crown (seq k).tiles w)) := by
  have _ := hseq
  have _ := hF
  have _ := hw
  intro x hx
  have h1 : (τ.θ ^ (k * m))⁻¹ • x ∈ support (crown (seq k).tiles w) := by
    apply h_cover
    exact Set.mem_image_of_mem _ hx
  rw [allowed_crowns_hierarchy_is_substitutive_step1_radius_step4_supp_iter]
  use (τ.θ ^ (k * m))⁻¹ • x
  constructor
  · exact h1
  · dsimp only
    rw [smul_smul, mul_inv_cancel₀, one_smul]
    have := τ.one_lt
    positivity

#print axioms allowed_crowns_hierarchy_is_substitutive_step1_radius_step4_supp
private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_decompose_translate
    (σ : Substitution P) (v : Pt) (S : Set (PlacedTile P)) :
    σ.decompose (translateSet v S) = translateSet (σ.θ • v) (σ.decompose S) := by
  ext A
  simp only [Substitution.decompose, Substitution.decomposeTile, translateSet,
    PlacedTile.translate, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨B, ⟨C, hC, rfl⟩, D, hD, rfl⟩
    refine ⟨D.translate (σ.θ • C.anchor), ⟨C, hC, D, hD, ?_⟩, ?_⟩
    · apply PlacedTile.ext
      · rfl
      · simp [PlacedTile.translate]
    · apply PlacedTile.ext
      · rfl
      · change σ.θ • v + (σ.θ • C.anchor + D.anchor) =
          σ.θ • (v + C.anchor) + D.anchor
        rw [smul_add]
        abel
  · rintro ⟨B, ⟨C, hC, D, hD, rfl⟩, rfl⟩
    refine ⟨C.translate v, ⟨C, hC, rfl⟩, D, hD, ?_⟩
    apply PlacedTile.ext
    · rfl
    · change σ.θ • (v + C.anchor) + D.anchor =
        σ.θ • v + (σ.θ • C.anchor + D.anchor)
      rw [smul_add]
      abel

private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_decompose_iUnion
    (σ : Substitution P) {ι : Sort*} (S : ι → Set (PlacedTile P)) :
    σ.decompose (⋃ i, S i) = ⋃ i, σ.decompose (S i) := by
  ext A
  simp only [Substitution.decompose, Set.mem_iUnion]
  constructor
  · rintro ⟨i, ⟨j, hji⟩, hA⟩
    exact ⟨j, i, hji, hA⟩
  · rintro ⟨i, j, hji, hA⟩
    exact ⟨j, ⟨i, hji⟩, hA⟩

private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_decomposeIter_iUnion
    (σ : Substitution P) (n : ℕ) {ι : Sort*} (S : ι → Set (PlacedTile P)) :
    σ.decomposeIter n (⋃ i, S i) = ⋃ i, σ.decomposeIter n (S i) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change σ.decompose (σ.decomposeIter n (⋃ i, S i)) = _
      rw [ih, allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_decompose_iUnion]
      rfl

private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_step1_pow
    (τ : Substitution P) (m : ℕ) (hm : 0 < m) (S : Set (PlacedTile P)) :
    (τ.pow m hm).decompose S = τ.decomposeIter m S := by
  have h_iter_translate : ∀ (n : ℕ) (v : Pt) (S : Set (PlacedTile P)),
      τ.decomposeIter n (translateSet v S) =
        translateSet ((τ.θ ^ n) • v) (τ.decomposeIter n S) := by
    intro n
    induction n with
    | zero =>
        intro v S
        simp [Substitution.decomposeIter]
    | succ n ih =>
        intro v S
        change τ.decompose (τ.decomposeIter n (translateSet v S)) = _
        rw [ih,
          allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_decompose_translate]
        congr 1
        rw [pow_succ', mul_smul]
  have h_singleton (A : PlacedTile P) :
      ({A} : Set (PlacedTile P)) = translateSet A.anchor {⟨A.form, 0⟩} := by
    ext B
    simp [translateSet, PlacedTile.translate, PlacedTile.ext_iff]
  let I := {A : PlacedTile P // A ∈ S}
  have hS : S = ⋃ A : I, ({A.1} : Set (PlacedTile P)) := by
    ext A
    simp [I]
  rw [hS]
  calc
    (τ.pow m hm).decompose (⋃ A : I, ({A.1} : Set (PlacedTile P))) =
        ⋃ A : I, (τ.pow m hm).decompose ({A.1} : Set (PlacedTile P)) :=
      allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_decompose_iUnion
        (τ.pow m hm) (ι := I)
        (fun A : I => ({A.1} : Set (PlacedTile P)))
    _ = ⋃ A : I, τ.decomposeIter m ({A.1} : Set (PlacedTile P)) := by
      apply iUnion_congr
      intro A
      rw [h_singleton,
        allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_decompose_translate,
        h_iter_translate]
      congr 1
      ext B
      simp [Substitution.decompose, Substitution.decomposeTile, Substitution.pow,
        Substitution.supertile, translateSet, PlacedTile.translate]
    _ = τ.decomposeIter m (⋃ A : I, ({A.1} : Set (PlacedTile P))) :=
      (allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_decomposeIter_iUnion
        τ m (ι := I) (fun A : I => ({A.1} : Set (PlacedTile P)))).symm

private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_step2_chain
    (τ : Substitution P) (m : ℕ) (hm : 0 < m) (seq : ℕ → PlaneTiling P)
    (hseq : ∀ k, (τ.pow m hm).IsComposition (seq (k + 1)) (seq k)) :
    ∀ k, τ.decomposeIter (k * m) (seq k).tiles = (seq 0).tiles := by
  have hpow := allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_step1_pow
    τ m hm
  have h_iter_add : ∀ (a b : ℕ) (S : Set (PlacedTile P)),
      τ.decomposeIter (a + b) S = τ.decomposeIter a (τ.decomposeIter b S) := by
    intro a
    induction a with
    | zero =>
        intro b S
        simp [Substitution.decomposeIter]
    | succ a ih =>
        intro b S
        rw [show a + 1 + b = (a + b) + 1 by omega]
        change τ.decompose (τ.decomposeIter (a + b) S) = _
        rw [ih]
        rfl
  intro k
  induction k with
  | zero =>
      simp [Substitution.decomposeIter]
  | succ k ih =>
      rw [Nat.succ_mul, h_iter_add, ← hpow, hseq k, ih]

private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_step3_finite
    (T : PlaneTiling P) (w : Pt) :
    (crown T.tiles w).Finite := by
  apply Set.Finite.subset (T.locallyFinite (isCompact_closedBall w 1))
  intro A hA
  exact ⟨hA.1, ⟨w, hA.2, mem_closedBall_self (by norm_num)⟩⟩

/-- Step 5 of the blueprint proof of `allowed_crowns_hierarchy_is_substitutive_step1_radius`:
Coverage by the descendants and disjoint interiors give actual tile inclusion,
not only support inclusion, by Lemma `lem:covered-tile-belongs`.  The composition
hypothesis `hseq` makes the decomposed crown a subpatch of `seq 0`; without it the
statement fails (unrelated `seq 0` and `seq k`). -/
private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile
    (τ : Substitution P) (m : ℕ) (hm : 0 < m) (seq : ℕ → PlaneTiling P)
    (hseq : ∀ k, (τ.pow m hm).IsComposition (seq (k + 1)) (seq k))
    (F : Set (PlacedTile P)) (hF : F ⊆ (seq 0).tiles) (hF_fin : F.Finite)
    (k : ℕ) (w : Pt) (hw : IsVertexOf (seq k).tiles w)
    (h_supp : support F ⊆ support (τ.decomposeIter (k * m) (crown (seq k).tiles w))) :
    F ⊆ τ.decomposeIter (k * m) (crown (seq k).tiles w) := by
  have _ := hF_fin
  have _ := hw
  have hchain := allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_step2_chain
    τ m hm seq hseq
  have h_iter_mono : ∀ (n : ℕ) {S T : Set (PlacedTile P)}, S ⊆ T →
      τ.decomposeIter n S ⊆ τ.decomposeIter n T := by
    intro n
    induction n with
    | zero =>
        intro S T hST
        exact hST
    | succ n ih =>
        intro S T hST
        change τ.decompose (τ.decomposeIter n S) ⊆
          τ.decompose (τ.decomposeIter n T)
        intro A hA
        simp only [Substitution.decompose, Set.mem_iUnion] at hA ⊢
        rcases hA with ⟨B, hB, hAB⟩
        refine ⟨B, ?_, hAB⟩
        exact ih (S := S) (T := T) hST hB
  let D := τ.decomposeIter (k * m) (crown (seq k).tiles w)
  have h_crown_sub : crown (seq k).tiles w ⊆ (seq k).tiles := by
    intro A hA
    exact hA.1
  have hD_sub : D ⊆ (seq 0).tiles := by
    dsimp [D]
    rw [← hchain k]
    exact h_iter_mono _ (S := crown (seq k).tiles w) (T := (seq k).tiles) h_crown_sub
  have hD_fin : D.Finite := by
    have h_crown_fin :=
      allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile_step3_finite
        (seq k) w
    have h_iter_fin : ∀ (n : ℕ) {S : Set (PlacedTile P)}, S.Finite →
        (τ.decomposeIter n S).Finite := by
      intro n
      induction n with
      | zero =>
          intro S hS
          exact hS
      | succ n ih =>
          intro S hS
          change (τ.decompose (τ.decomposeIter n S)).Finite
          apply Set.Finite.biUnion (ih hS)
          intro A _
          exact Set.Finite.image _ (τ.rule A.form).finite
    exact h_iter_fin _ h_crown_fin
  have hD_disj : DisjointInteriors D := by
    intro A hA B hB hne
    exact (seq 0).disjoint (hD_sub hA) (hD_sub hB) hne
  let D_patch : Patch P := ⟨D, hD_fin, hD_disj⟩
  intro A hA
  have hA_seq : A ∈ (seq 0).tiles := hF hA
  have hA_support : A.carrier ⊆ support D := by
    intro x hx
    apply h_supp
    simp only [support, Set.mem_iUnion]
    exact ⟨A, hA, hx⟩
  apply Patch.mem_of_carrier_subset_union D_patch A
  · intro B hB hBA
    exact (seq 0).disjoint hA_seq (hD_sub hB) hBA.symm
  · exact hA_support

/-- Step 1 of the blueprint proof of `allowed_crowns_hierarchy_is_substitutive`:
Given a finite patch $F\subset T$, choose $k$ with $\theta^{-km}\operatorname{diam}|F|<\varepsilon$.
The inverse-scaled support is covered by a crown $C$ of $T_{km}$.
All the level-zero tiles of $F$ belong to descendants of this crown:
coverage by the descendants and disjoint interiors give actual tile
inclusion, not only support inclusion, by Lemma `lem:covered-tile-belongs`. -/
private lemma allowed_crowns_hierarchy_is_substitutive_step1_radius
    (τ : Substitution P) (hflc : τ.FLC) (m : ℕ) (hm : 0 < m)
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ k, (τ.pow m hm).IsComposition (seq (k + 1)) (seq k))
    (hcrown : ∀ k (w : Pt), IsVertexOf (seq k).tiles w →
      τ.IsAllowedCrown (translateSet (-w) (crown (seq k).tiles w)))
    (F : Set (PlacedTile P)) (hF : F ⊆ (seq 0).tiles) (hF_fin : F.Finite) :
    ∃ k : ℕ, ∃ w : Pt, IsVertexOf (seq k).tiles w ∧
      F ⊆ τ.decomposeIter (k * m) (crown (seq k).tiles w) := by
  obtain ⟨ε, hε_pos, h_cover⟩ :=
    allowed_crowns_hierarchy_is_substitutive_step1_radius_step1_epsilon τ hflc
  obtain ⟨k, hk⟩ :=
    allowed_crowns_hierarchy_is_substitutive_step1_radius_step2_k τ ε hε_pos F hF_fin m hm
  obtain ⟨w, hw, h_cover_w⟩ :=
    allowed_crowns_hierarchy_is_substitutive_step1_radius_step3_cover τ m seq hcrown F k ε h_cover
      hk hF_fin
  have h_supp := allowed_crowns_hierarchy_is_substitutive_step1_radius_step4_supp τ m hm seq
    hseq F hF k w hw h_cover_w
  have h_inc := allowed_crowns_hierarchy_is_substitutive_step1_radius_step5_tile τ m hm seq
    hseq F hF hF_fin k w hw h_supp
  exact ⟨k, w, hw, h_inc⟩

/-- Step 1 of the blueprint proof of `allowed_crowns_hierarchy_is_substitutive_step2_supertile`:
Show that the crown `C` is a subset of the translated supertile. -/
private lemma allowed_crowns_hierarchy_is_substitutive_step2_supertile_step1_C_subset
    (τ : Substitution P) (w : Pt) (C : Set (PlacedTile P))
    (n : ℕ) (p : P.Form) (w' : Pt)
    (h_eq : translateSet (-w) C = translateSet (-w') (Tilings.Substitution.crown (τ.supertile n p) w')) :
    C ⊆ translateSet (w - w') (τ.supertile n p) := by
  intro A hA
  have hAw : A.translate (-w) ∈ translateSet (-w) C := ⟨A, hA, rfl⟩
  rw [h_eq] at hAw
  rcases hAw with ⟨B, hB, hBA⟩
  refine ⟨B, hB.1, ?_⟩
  apply PlacedTile.ext
  · simpa [PlacedTile.translate] using congrArg PlacedTile.form hBA
  · have hanchor := congrArg PlacedTile.anchor hBA
    dsimp [PlacedTile.translate] at hanchor ⊢
    calc
      w - w' + B.anchor = w + (-w' + B.anchor) := by rw [sub_eq_add_neg, add_assoc]
      _ = w + (-w + A.anchor) := by rw [hanchor]
      _ = A.anchor := by abel

private lemma allowed_crowns_hierarchy_is_substitutive_step2_supertile_step2_decompose_translate
    (τ : Substitution P) (v : Pt) (S : Set (PlacedTile P)) :
    τ.decompose (translateSet v S) = translateSet (τ.θ • v) (τ.decompose S) := by
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

private lemma allowed_crowns_hierarchy_is_substitutive_step2_supertile_step2_decompose_mono
    (τ : Substitution P) {S T : Set (PlacedTile P)} (hST : S ⊆ T) :
    τ.decompose S ⊆ τ.decompose T := by
  intro A hA
  simp only [Substitution.decompose, Set.mem_iUnion] at hA ⊢
  rcases hA with ⟨B, hB, hAB⟩
  exact ⟨B, hST hB, hAB⟩

/-- Step 2 of the blueprint proof of `allowed_crowns_hierarchy_is_substitutive_step2_supertile`:
Show that decomposing `C` iteratively maintains the subset property for the decomposed supertile. -/
private lemma allowed_crowns_hierarchy_is_substitutive_step2_supertile_step2_decompose_subset
    (τ : Substitution P) (C : Set (PlacedTile P))
    (n km : ℕ) (p : P.Form) (v : Pt)
    (hC : C ⊆ translateSet v (τ.supertile n p)) :
    τ.decomposeIter km C ⊆ translateSet (τ.θ^km • v) (τ.supertile (n + km) p) := by
  induction km with
  | zero =>
      simpa [Substitution.decomposeIter, Substitution.supertile] using hC
  | succ km ih =>
      change τ.decompose (τ.decomposeIter km C) ⊆
        translateSet (τ.θ ^ (Nat.succ km) • v)
          (τ.supertile (n + Nat.succ km) p)
      apply Set.Subset.trans
        (allowed_crowns_hierarchy_is_substitutive_step2_supertile_step2_decompose_mono τ ih)
      rw [allowed_crowns_hierarchy_is_substitutive_step2_supertile_step2_decompose_translate]
      rw [pow_succ', mul_smul]
      rfl

/-- Step 3 of the blueprint proof of `allowed_crowns_hierarchy_is_substitutive_step2_supertile`:
Conclude that if `F` is a subset of the translated supertile, it occurs in it. -/
private lemma allowed_crowns_hierarchy_is_substitutive_step2_supertile_step3_occurs
    (τ : Substitution P) (F : Set (PlacedTile P)) (km : ℕ) (n : ℕ) (p : P.Form) (v : Pt)
    (hF : F ⊆ translateSet v (τ.supertile (n + km) p)) :
    OccursIn F (τ.supertile (n + km) p) := by
  refine ⟨-v, ?_⟩
  calc
    translateSet (-v) F ⊆ translateSet (-v) (translateSet v (τ.supertile (n + km) p)) :=
      image_mono hF
    _ = τ.supertile (n + km) p := by
      simpa using gap_translateSet_neg (τ.supertile (n + km) p) (-v)

/-- Step 2 of the blueprint proof of `allowed_crowns_hierarchy_is_substitutive`:
The allowed crown $C$ occurs in some supertile $S$. Thus $F \subset \tau^{km}S$,
which is a supertile. -/
private lemma allowed_crowns_hierarchy_is_substitutive_step2_supertile
    (τ : Substitution P) (F : Set (PlacedTile P)) (km : ℕ)
    (w : Pt) (C : Set (PlacedTile P))
    (hF : F ⊆ τ.decomposeIter km C)
    (h_allowed : τ.IsAllowedCrown (translateSet (-w) C)) :
    ∃ (n : ℕ) (p : P.Form), OccursIn F (τ.supertile n p) := by
  rcases h_allowed with ⟨n, p, w', hw', h_eq⟩
  have hC : C ⊆ translateSet (w - w') (τ.supertile n p) :=
    allowed_crowns_hierarchy_is_substitutive_step2_supertile_step1_C_subset τ w C n p w' h_eq
  have hC_dec : τ.decomposeIter km C ⊆ translateSet (τ.θ^km • (w - w')) (τ.supertile (n + km) p) :=
    allowed_crowns_hierarchy_is_substitutive_step2_supertile_step2_decompose_subset τ C n km p (w - w') hC
  have hF_sub : F ⊆ translateSet (τ.θ^km • (w - w')) (τ.supertile (n + km) p) :=
    Set.Subset.trans hF hC_dec
  use (n + km), p
  exact allowed_crowns_hierarchy_is_substitutive_step2_supertile_step3_occurs τ F km n p (τ.θ^km • (w - w')) hF_sub

/-- `lem:allowed-hierarchy`: if `τ` has FLC and `T = seq 0, seq 1, …` is a
`τ^m`-hierarchy (`seq k` plays the role of `T_{km}`) all of whose full
pointed crowns, at every level and every listed vertex, are `τ`-allowed,
then `T` is a `τ`-substitution tiling. -/
theorem allowed_crowns_hierarchy_is_substitutive (τ : Substitution P) (hflc : τ.FLC)
    (m : ℕ) (hm : 0 < m) (seq : ℕ → PlaneTiling P)
    (hseq : ∀ k, (τ.pow m hm).IsComposition (seq (k + 1)) (seq k))
    (hcrown : ∀ k (w : Pt), IsVertexOf (seq k).tiles w →
      τ.IsAllowedCrown (translateSet (-w) (crown (seq k).tiles w))) :
    τ.IsSubstitutionTiling (seq 0) := by
  intro F hF hF_fin
  rcases allowed_crowns_hierarchy_is_substitutive_step1_radius τ hflc m hm seq hseq hcrown F hF hF_fin with ⟨k, w, hw, hF_sub⟩
  exact allowed_crowns_hierarchy_is_substitutive_step2_supertile τ F (k * m) w (crown (seq k).tiles w) hF_sub (hcrown k w hw)

end AllowedHierarchy

end Tilings

end
