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

/-- `lem:polygon-local-cone`: a polygonal disk agrees with its local cone in a
small ball around each of its points. -/
theorem polygonLocalCone (D : PolygonalDisk) {v : Pt} (hv : v ∈ D.carrier) :
    ∃ r : ℝ, 0 < r ∧ D.carrier ∩ ball v r = localCone D.carrier v ∩ ball v r := by
  sorry

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
  sorry

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
