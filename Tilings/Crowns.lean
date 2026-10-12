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
      A.carrier ∩ ball (0 : Pt) r = localCone A.carrier 0 ∩ ball (0 : Pt) r := by sorry

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

/-- Step 4 of the blueprint proof of `uniformSectorRadius`: Translations preserve the
conclusions. -/
private lemma uniformSectorRadius_step4_translation {K : Set (PlacedTile P)} {r δ : ℝ}
    (h_rad : ∀ A ∈ K, A.carrier ∩ ball (0 : Pt) r = localCone A.carrier 0 ∩ ball (0 : Pt) r)
    (h_sep : ∀ A ∈ K, ∀ w ∈ A.vertexSet, w ≠ (0 : Pt) → δ ≤ dist w (0 : Pt)) :
    ∀ v : Pt,
      support (translateSet v K) ∩ ball v r = Omega (translateSet v K) v ∩ ball v r ∧
      ∀ A ∈ translateSet v K, ∀ w ∈ A.vertexSet, w ≠ v → δ ≤ dist w v := by sorry

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

/-- Step 1 of the blueprint proof of `supertile_disjoint`: decomposition
preserves disjoint interiors. -/
private lemma supertile_disjoint_step1_decompose (τ : Substitution P) (S : Set (PlacedTile P))
    (hS : DisjointInteriors S) : DisjointInteriors (τ.decompose S) := sorry

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

/-- Step 1 of the blueprint proof of `distanceToReflexBoundaryRay`: 
reduce to `sInf` of `‖t a - s b‖`. -/
private lemma distanceToReflexBoundaryRay_step1_infDist_eq (q a b : Pt) (t : ℝ) :
    infDist (q + t • a) ((fun s : ℝ => q + s • b) '' Ici 0) =
      sInf ((fun s : ℝ => ‖t • a - s • b‖) '' Ici 0) := by
  sorry

/-- Step 2 of the blueprint proof of `distanceToReflexBoundaryRay`: minimize the quadratic form. -/
private lemma distanceToReflexBoundaryRay_step2_min_quad (a b : Pt) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) {t : ℝ} (ht : 0 < t) :
    sInf ((fun s : ℝ => ‖t • a - s • b‖) '' Ici 0) =
      if InnerProductGeometry.angle a b ≤ Real.pi / 2 then
        t * Real.sin (InnerProductGeometry.angle a b)
      else t := by
  sorry

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
  sorry

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
  sorry

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

section AllowedHierarchy

open Substitution Crowns

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
  sorry

end AllowedHierarchy

end Tilings

end
