import Tilings.Geometry.Grouping
import Tilings.Crowns
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Endpoint schedules and whole-side ports (statements only)

Skeleton for the alignment part of `main.tex`: finite endpoint schedules
(`def:endpoint-schedule`), alignment of all intermediate levels
(`lem:alignment-tuple`), whole-side ports without nested subdivisions
(`lem:whole-ports`) and the STS part of strict schedule composition
(`lem:schedule-compose`).

Conventions.  A parent grouped form `A` of a grouped family `G`, a power `m`
and `s = θ^m` are fixed.  The fine tiles of `A` are `τ^m Δ A`; a whole fine
outer side is given by its ordered pair of endpoints `(x, y)` (a listed side
of a fine tile contained in `∂(s A)`).  Each unoriented line direction has a
canonical unit direction (`canonDir`): the representative with positive first
coordinate, or with first coordinate zero and positive second coordinate.
The canonical frame `[0, |e|]` of a segment starts at the endpoint from which
the other one lies in the canonical direction.  All of this is translation
invariant, so two owners of a coincident side compute the same frame.
-/

open Set Pointwise

noncomputable section

namespace Tilings

namespace Alignment

open Geometry

variable {P : Protoset}

/-! ## Canonical frames -/

/-- The canonical unit direction of the unoriented line direction of `v`. -/
def canonDir (v : Pt) : Pt :=
  if 0 < v 0 ∨ (v 0 = 0 ∧ 0 < v 1) then ‖v‖⁻¹ • v else -(‖v‖⁻¹ • v)

/-- The canonical first endpoint of the segment `{x, y}`. -/
def frameOrigin (x y : Pt) : Pt :=
  if 0 < (y - x) 0 ∨ ((y - x) 0 = 0 ∧ 0 < (y - x) 1) then x else y

/-- Coordinate of `z` along the unit direction `u` from the origin `o`. -/
def coord (o u z : Pt) : ℝ := u 0 * (z 0 - o 0) + u 1 * (z 1 - o 1)

/-- Coordinate of `z` in the canonical frame of the segment `{x, y}`. -/
def segCoord (x y z : Pt) : ℝ := coord (frameOrigin x y) (canonDir (y - x)) z

/-! ## Layers and schedules (`def:endpoint-schedule`) -/

/-- Uniform layer tags: `top` (layer `G`, the listed sides of `s A`) and
`level j` for `j = 0, …, m - 1` (the listed boundary sides of
`θ^(m-j) τ^j Δ A`).  The tag does not depend on the form. -/
inductive LayerTag (m : ℕ) where
  | top : LayerTag m
  | level : Fin m → LayerTag m
  deriving DecidableEq

variable (τ : Substitution P) (G : GroupedFamily P)

/-- The scaled parent region `s A`, `s = θ^m`. -/
def parentRegion (m : ℕ) (A : G.P'.Form) : Set Pt := (τ.θ ^ m) • (G.P'.disk A).carrier

/-- The fine tiles `τ^m Δ A` of the parent form `A`. -/
def fineTiles (m : ℕ) (A : G.P'.Form) : Set (PlacedTile P) :=
  τ.decomposeIter m (G.dissect A).tiles

/-- Whole fine outer sides of `A`, as ordered endpoint pairs. -/
def fineOuterSides (m : ℕ) (A : G.P'.Form) : Set (Pt × Pt) :=
  {e | ∃ B ∈ fineTiles τ G m A, ∃ i : Fin (P.disk B.form).n,
    e = (B.vertex i, B.vertex (finRotate _ i)) ∧
      segment ℝ e.1 e.2 ⊆ frontier (parentRegion τ G m A)}

/-- The scaled `a`-th listed side of the parent `A`, as an endpoint pair. -/
def parentSide (m : ℕ) (A : G.P'.Form) (a : Fin (G.P'.disk A).n) : Pt × Pt :=
  ((τ.θ ^ m) • (G.P'.disk A).vertex a, (τ.θ ^ m) • (G.P'.disk A).vertex (finRotate _ a))

/-- The listed boundary sides of a layer, scaled to the fine level. -/
def layerSides (m : ℕ) (A : G.P'.Form) : LayerTag m → Set (Pt × Pt)
  | .top => {c | ∃ a : Fin (G.P'.disk A).n, c = parentSide τ G m A a}
  | .level j => {c | ∃ B ∈ τ.decomposeIter (j : ℕ) (G.dissect A).tiles,
      ∃ i : Fin (P.disk B.form).n,
        c = ((τ.θ ^ (m - (j : ℕ))) • B.vertex i,
          (τ.θ ^ (m - (j : ℕ))) • B.vertex (finRotate _ i)) ∧
        segment ℝ c.1 c.2 ⊆ frontier (parentRegion τ G m A)}

/-- The atom `(u, v; p, q)` of a coarse side `c` on the fine side `e`, in the
canonical frame `[0, |e|]` of `e`: `[u, v] = [p, q] ∩ [0, |e|]`, where `[p, q]`
are the coordinates of the endpoints of `c` (possibly outside `e`). -/
def atom (e c : Pt × Pt) : ℝ × ℝ × ℝ × ℝ :=
  let p := min (segCoord e.1 e.2 c.1) (segCoord e.1 e.2 c.2)
  let q := max (segCoord e.1 e.2 c.1) (segCoord e.1 e.2 c.2)
  (max 0 p, min (dist e.1 e.2) q, p, q)

/-- `def:endpoint-schedule`: the layered schedule `W(A, e)` of a whole fine
outer side `e` of the parent `A`: for every layer tag, the set of atoms
`(u, v; p, q)` of the listed boundary sides of that layer meeting `e` with
positive length.  Its value is the geometric data only (not the owner form or
an edge identifier).  Layer `top` duplicates layer `level 0`. -/
def EndpointSchedule (m : ℕ) (A : G.P'.Form) (e : Pt × Pt) (t : LayerTag m) :
    Set (ℝ × ℝ × ℝ × ℝ) :=
  {r | ∃ c ∈ layerSides τ G m A t,
    OverlapPos (segment ℝ c.1 c.2) (segment ℝ e.1 e.2) ∧ r = atom e c}

/-- The segment of an endpoint pair translated by `v`. -/
def placedSeg (v : Pt) (e : Pt × Pt) : Set Pt := segment ℝ (v + e.1) (v + e.2)

/-- Schedule alignment in a grouped plane tiling `T'`: physically coincident
whole fine outer sides of two parents carry equal schedules. -/
def SchedulesAligned (m : ℕ) (T' : PlaneTiling G.P') : Prop :=
  ∀ A ∈ T'.tiles, ∀ A' ∈ T'.tiles,
    ∀ e ∈ fineOuterSides τ G m A.form, ∀ e' ∈ fineOuterSides τ G m A'.form,
      placedSeg ((τ.θ ^ m) • A.anchor) e = placedSeg ((τ.θ ^ m) • A'.anchor) e' →
        EndpointSchedule τ G m A.form e = EndpointSchedule τ G m A'.form e'

private lemma fs1_segment_infinite {x y : Pt} (hxy : x ≠ y) : (segment ℝ x y).Infinite := by
  rw [segment_eq_image_lineMap]
  refine (Set.Icc_infinite (zero_lt_one' ℝ)).image ?_
  exact (AffineMap.lineMap_injective ℝ hxy).injOn

private lemma fs1_cover {x y : Pt} (hxy : x ≠ y) {S : Set (Set Pt)} (hS : S.Finite)
    (hconv : ∀ T ∈ S, Convex ℝ T) (hcov : segment ℝ x y ⊆ ⋃₀ S) :
    ∃ T ∈ S, ∃ u v : Pt, u ≠ v ∧ segment ℝ u v ⊆ segment ℝ x y ∩ T := by
  by_contra hcon
  push_neg at hcon
  have hsub : ∀ T ∈ S, (segment ℝ x y ∩ T).Subsingleton := by
    intro T hT u hu v hv
    by_contra huv
    exact hcon T hT u v huv (((convex_segment x y).inter (hconv T hT)).segment_subset hu hv)
  apply fs1_segment_infinite hxy
  refine Set.Finite.subset (hS.biUnion fun T hT => (hsub T hT).finite) ?_
  intro z hz
  obtain ⟨T, hT, hzT⟩ := hcov hz
  exact Set.mem_biUnion hT ⟨hz, hzT⟩

private lemma fs1_placedSeg_eq (v : Pt) (e : Pt × Pt) :
    placedSeg v e = v +ᵥ segment ℝ e.1 e.2 := (vadd_segment _ _ _ _).symm

private lemma fs1_tile_side_eq (B : PlacedTile P) (i : Fin (P.disk B.form).n) :
    B.side i = segment ℝ (B.vertex i) (B.vertex (finRotate _ i)) := by
  simp [PlacedTile.side, PolygonalDisk.side, PlacedTile.vertex, vadd_segment]

private lemma fs1_translate_side (B : PlacedTile P) (v : Pt) (i : Fin (P.disk B.form).n) :
    (B.translate v).side i = placedSeg v (B.vertex i, B.vertex (finRotate _ i)) := by
  rw [fs1_tile_side_eq, placedSeg]
  simp only [PlacedTile.translate, PlacedTile.vertex, vadd_eq_add, add_assoc]

private lemma fs1_frontier_vadd (v : Pt) (s : Set Pt) : frontier (v +ᵥ s) = v +ᵥ frontier s := by
  have := (Homeomorph.addLeft v).image_frontier s
  rw [Homeomorph.coe_addLeft] at this
  exact this.symm

private lemma fs1_frontier_smul {c : ℝ} (hc : c ≠ 0) (s : Set Pt) : frontier (c • s) = c • frontier s :=
  ((Homeomorph.smulOfNeZero c hc).image_frontier s).symm

private lemma fs1_frontier_carrier (B : PlacedTile P) : frontier B.carrier = ⋃ i, B.side i := by
  rw [PlacedTile.carrier, fs1_frontier_vadd, (P.disk B.form).frontier_eq, Set.vadd_set_iUnion]
  rfl

private lemma fs1_closure_interior_carrier (B : PlacedTile P) :
    closure (interior B.carrier) = B.carrier := by
  rw [PlacedTile.carrier, interior_vadd, closure_vadd, (P.disk B.form).regular_closed]

private lemma fs1_carrier_closed (B : PlacedTile P) : IsClosed B.carrier := by
  rw [← fs1_closure_interior_carrier]; exact isClosed_closure

private lemma fs1_side_subset_carrier (B : PlacedTile P) (i : Fin (P.disk B.form).n) :
    B.side i ⊆ B.carrier := by
  intro z hz
  have : z ∈ frontier B.carrier := by
    rw [fs1_frontier_carrier]; exact Set.mem_iUnion.2 ⟨i, hz⟩
  exact (fs1_carrier_closed B).frontier_subset this

private lemma fs1_translate_carrier (B : PlacedTile P) (v : Pt) :
    (B.translate v).carrier = v +ᵥ B.carrier := by
  ext x
  simp only [PlacedTile.carrier, PlacedTile.translate, Set.mem_vadd_set_iff_neg_vadd_mem,
    vadd_eq_add, neg_add_rev]
  rw [← add_assoc]


private lemma fs1_decomposeIter_mono (n : ℕ) {S S' : Set (PlacedTile P)} (h : S ⊆ S') :
    τ.decomposeIter n S ⊆ τ.decomposeIter n S' := by
  induction n with
  | zero => exact h
  | succ n ih =>
    intro B hB
    change B ∈ τ.decompose (τ.decomposeIter n S) at hB
    change B ∈ τ.decompose (τ.decomposeIter n S')
    simp only [Substitution.decompose, Set.mem_iUnion] at hB ⊢
    obtain ⟨C, hC, hBC⟩ := hB
    exact ⟨C, ih hC, hBC⟩

private lemma fs1_decomposeIter_translate (n : ℕ) (v : Pt) (S : Set (PlacedTile P))
    (B : PlacedTile P) (hB : B ∈ τ.decomposeIter n S) :
    B.translate ((τ.θ ^ n) • v) ∈ τ.decomposeIter n (translateSet v S) := by
  induction n generalizing B with
  | zero =>
    show B.translate ((τ.θ ^ 0) • v) ∈ translateSet v S
    rw [pow_zero, one_smul]
    exact ⟨B, hB, rfl⟩
  | succ n ih =>
    change B ∈ τ.decompose (τ.decomposeIter n S) at hB
    change _ ∈ τ.decompose (τ.decomposeIter n (translateSet v S))
    simp only [Substitution.decompose, Set.mem_iUnion] at hB ⊢
    obtain ⟨C, hC, hBC⟩ := hB
    refine ⟨C.translate ((τ.θ ^ n) • v), ih C hC, ?_⟩
    simp only [Substitution.decomposeTile, translateSet, Set.mem_image] at hBC ⊢
    obtain ⟨R, hR, rfl⟩ := hBC
    refine ⟨R, hR, ?_⟩
    simp only [PlacedTile.translate, PlacedTile.mk.injEq, true_and, vadd_eq_add, smul_add,
      pow_succ', mul_smul]
    abel

private lemma fs1_fine_mem (m : ℕ) (T' : PlaneTiling G.P') (A : PlacedTile G.P')
    (hA : A ∈ T'.tiles) (B : PlacedTile P) (hB : B ∈ fineTiles τ G m A.form) :
    B.translate ((τ.θ ^ m) • A.anchor) ∈ τ.decomposeIter m (G.scatter T'.tiles) := by
  apply fs1_decomposeIter_mono τ m (S := G.scatterTile A)
  · intro C hC
    exact Set.mem_biUnion hA hC
  · exact fs1_decomposeIter_translate τ m A.anchor _ B hB

private lemma fs1_support_translateSet (v : Pt) (S : Set (PlacedTile P)) :
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

private lemma fs1_support_decomposeTile (A : PlacedTile P) :
    support (τ.decomposeTile A) = τ.θ • A.carrier := by
  dsimp [Substitution.decomposeTile]
  rw [fs1_support_translateSet, τ.support_eq, PlacedTile.carrier]
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

private lemma fs1_support_decompose (S : Set (PlacedTile P)) :
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
    rwa [fs1_support_decomposeTile] at h
  · rintro ⟨A, hA, hx⟩
    have h : x ∈ support (τ.decomposeTile A) := by
      rwa [fs1_support_decomposeTile]
    simp only [support, Set.mem_iUnion] at h
    rcases h with ⟨B, hB, hxB⟩
    exact ⟨B, ⟨A, hA, hB⟩, hxB⟩

private lemma fs1_fineTiles_support (m : ℕ) (A : G.P'.Form) :
    support (fineTiles τ G m A) = parentRegion τ G m A := by
  induction m with
  | zero => simpa [fineTiles, parentRegion, Substitution.decomposeIter] using G.support_eq A
  | succ m ih =>
      change support (τ.decompose (τ.decomposeIter m (G.dissect A).tiles)) = _
      rw [fs1_support_decompose]
      change support (τ.decomposeIter m (G.dissect A).tiles) = _ at ih
      rw [ih, parentRegion, parentRegion, smul_smul, pow_succ']

private lemma fs1_fineTiles_finite (m : ℕ) (A : G.P'.Form) : (fineTiles τ G m A).Finite := by
  unfold fineTiles
  have key : ∀ n (S : Set (PlacedTile P)), S.Finite → (τ.decomposeIter n S).Finite := by
    intro n S hS
    induction n with
    | zero => exact hS
    | succ n ih =>
      change (τ.decompose (τ.decomposeIter n S)).Finite
      exact ih.biUnion fun B _ => (τ.rule B.form).finite.image _
  exact key m _ (G.dissect A).finite

private lemma fs1_region_closed (m : ℕ) (A : G.P'.Form) : IsClosed (parentRegion τ G m A) :=
  ((G.P'.disk A).compact.smul (τ.θ ^ m)).isClosed

private lemma fs1_region_eq (m : ℕ) (A : PlacedTile G.P') :
    ((τ.θ ^ m) • A.anchor) +ᵥ parentRegion τ G m A.form = (τ.θ ^ m) • A.carrier := by
  simp only [parentRegion, PlacedTile.carrier, ← Set.image_vadd, ← Set.image_smul, Set.image_image,
    vadd_eq_add, smul_add]

private lemma fs1_frontier_cover (m : ℕ) (α : G.P'.Form) (a : Pt) :
    frontier (a +ᵥ parentRegion τ G m α) ⊆ ⋃₀ {T | ∃ B ∈ fineTiles τ G m α,
      ∃ i : Fin (P.disk B.form).n, T = placedSeg a (B.vertex i, B.vertex (finRotate _ i))} := by
  intro z hz
  rw [fs1_frontier_vadd, Set.mem_vadd_set] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hwR : w ∈ parentRegion τ G m α := (fs1_region_closed τ G m α).frontier_subset hw
  rw [← fs1_fineTiles_support] at hwR
  simp only [support, Set.mem_iUnion] at hwR
  obtain ⟨B, hB, hwB⟩ := hwR
  have hBR : B.carrier ⊆ parentRegion τ G m α := by
    rw [← fs1_fineTiles_support]
    exact Set.subset_biUnion_of_mem (u := fun B => B.carrier) hB
  have hwF : w ∈ frontier B.carrier := ⟨subset_closure hwB, fun h => hw.2 (interior_mono hBR h)⟩
  rw [fs1_frontier_carrier, Set.mem_iUnion] at hwF
  obtain ⟨i, hi⟩ := hwF
  refine ⟨_, ⟨B, hB, i, rfl⟩, ?_⟩
  rw [fs1_placedSeg_eq, ← fs1_tile_side_eq]
  exact Set.vadd_mem_vadd_set hi

private lemma fs1_cover_finite (m : ℕ) (α : G.P'.Form) (a : Pt) :
    {T | ∃ B ∈ fineTiles τ G m α, ∃ i : Fin (P.disk B.form).n,
      T = placedSeg a (B.vertex i, B.vertex (finRotate _ i))}.Finite := by
  refine Set.Finite.subset ((fs1_fineTiles_finite τ G m α).biUnion fun B _ =>
    Set.finite_range (fun i : Fin (P.disk B.form).n =>
      placedSeg a (B.vertex i, B.vertex (finRotate _ i)))) ?_
  rintro T ⟨B, hB, i, rfl⟩
  exact Set.mem_biUnion hB ⟨i, rfl⟩

private lemma fs1_placed_side_sub (m : ℕ) (α : G.P'.Form) (a : Pt) (B : PlacedTile P)
    (hB : B ∈ fineTiles τ G m α) (i : Fin (P.disk B.form).n) :
    placedSeg a (B.vertex i, B.vertex (finRotate _ i)) ⊆
      closure (interior (a +ᵥ parentRegion τ G m α)) := by
  rw [← fs1_translate_side]
  refine (fs1_side_subset_carrier (B.translate a) i).trans ?_
  rw [← fs1_closure_interior_carrier]
  refine closure_mono (interior_mono ?_)
  rw [fs1_translate_carrier]
  apply Set.vadd_set_mono
  rw [← fs1_fineTiles_support]
  exact Set.subset_biUnion_of_mem (u := fun B => B.carrier) hB

private lemma fs1_outer (m : ℕ) (α : G.P'.Form) (a : Pt) (B : PlacedTile P)
    (hB : B ∈ fineTiles τ G m α) (i : Fin (P.disk B.form).n) (X : Set Pt)
    (hX : placedSeg a (B.vertex i, B.vertex (finRotate _ i)) ⊆ closure (interior X))
    (hdisj : Disjoint (interior (a +ᵥ parentRegion τ G m α)) (interior X)) :
    segment ℝ (B.vertex i) (B.vertex (finRotate _ i)) ⊆ frontier (parentRegion τ G m α) := by
  intro w hw
  have hwR : w ∈ parentRegion τ G m α := by
    rw [← fs1_fineTiles_support]
    exact Set.mem_biUnion hB (fs1_side_subset_carrier B i (by rwa [fs1_tile_side_eq]))
  refine ⟨subset_closure hwR, fun hint => ?_⟩
  have h1 : a +ᵥ w ∈ interior (a +ᵥ parentRegion τ G m α) := by
    rw [interior_vadd]
    exact Set.vadd_mem_vadd_set hint
  have h2 : a +ᵥ w ∈ closure (interior X) := hX (by
    rw [fs1_placedSeg_eq]
    exact Set.vadd_mem_vadd_set hw)
  rw [mem_closure_iff] at h2
  obtain ⟨q, hq1, hq2⟩ := h2 _ isOpen_interior h1
  exact Set.disjoint_left.mp hdisj hq1 hq2

private lemma fs1_disj (m : ℕ) (T' : PlaneTiling G.P') (A A'' : PlacedTile G.P')
    (hA : A ∈ T'.tiles) (hA'' : A'' ∈ T'.tiles) (hne : A ≠ A'') :
    Disjoint (interior (((τ.θ ^ m) • A.anchor) +ᵥ parentRegion τ G m A.form))
      (interior (((τ.θ ^ m) • A''.anchor) +ᵥ parentRegion τ G m A''.form)) := by
  have hs : τ.θ ^ m ≠ 0 := pow_ne_zero _ (by linarith [τ.one_lt])
  rw [fs1_region_eq, fs1_region_eq, interior_smul₀ hs, interior_smul₀ hs]
  exact (Set.disjoint_image_iff (smul_right_injective Pt hs)).mpr (T'.disjoint hA hA'' hne)

private lemma fs1_core (m : ℕ) (T' : PlaneTiling G.P')
    (hfine : SideToSideSet (τ.decomposeIter m (G.scatter T'.tiles)))
    (A A'' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA'' : A'' ∈ T'.tiles) (hne : A ≠ A'')
    (x y : Pt) (hxy : x ≠ y)
    (hJ : segment ℝ x y ⊆ frontier (((τ.θ ^ m) • A.anchor) +ᵥ parentRegion τ G m A.form) ∩
      frontier (((τ.θ ^ m) • A''.anchor) +ᵥ parentRegion τ G m A''.form)) :
    ∃ e ∈ fineOuterSides τ G m A.form, ∃ e'' ∈ fineOuterSides τ G m A''.form,
      placedSeg ((τ.θ ^ m) • A.anchor) e = placedSeg ((τ.θ ^ m) • A''.anchor) e'' ∧
      ∃ u v : Pt, u ≠ v ∧ segment ℝ u v ⊆ segment ℝ x y ∩ placedSeg ((τ.θ ^ m) • A.anchor) e := by
  obtain ⟨T1, ⟨B, hB, i, rfl⟩, u1, v1, huv1, hsub1⟩ :=
    fs1_cover hxy (fs1_cover_finite τ G m A.form _) (by rintro T ⟨B, -, i, rfl⟩; exact convex_segment _ _)
      ((Set.subset_inter_iff.mp hJ).1.trans (fs1_frontier_cover τ G m A.form _))
  have hJ1 : segment ℝ u1 v1 ⊆ frontier (((τ.θ ^ m) • A''.anchor) +ᵥ parentRegion τ G m A''.form) :=
    fun z hz => (hJ (hsub1 hz).1).2
  obtain ⟨T2, ⟨B'', hB'', j, rfl⟩, u2, v2, huv2, hsub2⟩ :=
    fs1_cover huv1 (fs1_cover_finite τ G m A''.form _) (by rintro T ⟨B, -, i, rfl⟩; exact convex_segment _ _)
      (hJ1.trans (fs1_frontier_cover τ G m A''.form _))
  have hmem := fs1_fine_mem τ G m T' A hA B hB
  have hmem'' := fs1_fine_mem τ G m T' A'' hA'' B'' hB''
  have hside := hfine _ hmem _ hmem'' i j ⟨u2, v2, huv2, by
    rw [fs1_translate_side, fs1_translate_side]
    exact fun z hz => ⟨(hsub1 (hsub2 hz).1).2, (hsub2 hz).2⟩⟩
  rw [fs1_translate_side, fs1_translate_side] at hside
  refine ⟨_, ⟨B, hB, i, rfl, ?_⟩, _, ⟨B'', hB'', j, rfl, ?_⟩, hside, u1, v1, huv1, hsub1⟩
  · refine fs1_outer τ G m A.form _ B hB i _ ?_ (fs1_disj τ G m T' A A'' hA hA'' hne)
    rw [hside]
    exact fs1_placed_side_sub τ G m A''.form _ B'' hB'' j
  · refine fs1_outer τ G m A''.form _ B'' hB'' j _ ?_ (fs1_disj τ G m T' A A'' hA hA'' hne).symm
    rw [← hside]
    exact fs1_placed_side_sub τ G m A.form _ B hB i

private lemma fs1_layer_frontier (m : ℕ) (α : G.P'.Form) (t : LayerTag m) (c : Pt × Pt)
    (hc : c ∈ layerSides τ G m α t) : segment ℝ c.1 c.2 ⊆ frontier (parentRegion τ G m α) := by
  cases t with
  | top =>
    obtain ⟨k, rfl⟩ := hc
    have hs : τ.θ ^ m ≠ 0 := pow_ne_zero _ (by linarith [τ.one_lt])
    rw [parentRegion, fs1_frontier_smul hs, parentSide]
    let f : Pt →ᵃ[ℝ] Pt := (LinearMap.lsmul ℝ Pt (τ.θ ^ m)).toAffineMap
    have hseg : segment ℝ ((τ.θ ^ m) • (G.P'.disk α).vertex k)
        ((τ.θ ^ m) • (G.P'.disk α).vertex (finRotate _ k)) =
        (τ.θ ^ m) • segment ℝ ((G.P'.disk α).vertex k) ((G.P'.disk α).vertex (finRotate _ k)) :=
      (image_segment ℝ f _ _).symm
    rw [hseg]
    apply Set.smul_set_mono
    rw [(G.P'.disk α).frontier_eq]
    exact Set.subset_iUnion (fun i => segment ℝ ((G.P'.disk α).vertex i)
      ((G.P'.disk α).vertex (finRotate _ i))) k
  | level j =>
    obtain ⟨B, -, i, rfl, h⟩ := hc
    exact h

private lemma fs1_overlap_of_placed {w : Pt} {p q : Pt × Pt} {u v : Pt} (huv : u ≠ v)
    (h : segment ℝ u v ⊆ placedSeg w p ∩ placedSeg w q) :
    OverlapPos (segment ℝ p.1 p.2) (segment ℝ q.1 q.2) := by
  refine ⟨-w +ᵥ u, -w +ᵥ v, fun h' => huv (vadd_left_cancel _ h'), ?_⟩
  rw [← vadd_segment]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨h1, h2⟩ := h hz
  rw [fs1_placedSeg_eq] at h1 h2
  obtain ⟨z1, hz1, rfl⟩ := h1
  obtain ⟨z2, hz2, he⟩ := h2
  refine ⟨by simpa using hz1, ?_⟩
  have : z2 = z1 := vadd_left_cancel _ he
  subst this
  simpa using hz2

private lemma fs1_other {Q : Protoset} (T : PlaneTiling Q) {s : ℝ} (hs : s ≠ 0) (A : PlacedTile Q)
    (hA : A ∈ T.tiles) {x y : Pt} (hxy : x ≠ y) (hI : segment ℝ x y ⊆ frontier (s • A.carrier)) :
    ∃ A'' ∈ T.tiles, A ≠ A'' ∧ ∃ u v : Pt, u ≠ v ∧
      segment ℝ u v ⊆ segment ℝ x y ∩ frontier (s • A''.carrier) := by
  have hAc : IsCompact A.carrier := by
    rw [PlacedTile.carrier, ← Set.image_vadd]
    exact (Q.disk A.form).compact.image (continuous_const_vadd A.anchor)
  have hK : IsCompact (Metric.cthickening 1 A.carrier) := hAc.cthickening
  have hF := T.locallyFinite hK
  set F := {A'' ∈ T.tiles | (A''.carrier ∩ Metric.cthickening 1 A.carrier).Nonempty}
  have hFne : {A'' | A'' ∈ F ∧ A ≠ A''}.Finite := hF.subset fun _ h => h.1
  have hS : {X | ∃ A'' ∈ F, A ≠ A'' ∧ ∃ k : Fin (Q.disk A''.form).n, X = s • A''.side k}.Finite := by
    refine Set.Finite.subset (hF.biUnion fun A'' _ =>
      Set.finite_range (fun k : Fin (Q.disk A''.form).n => s • A''.side k)) ?_
    rintro X ⟨A'', hA'', -, k, rfl⟩
    exact Set.mem_biUnion hA'' ⟨k, rfl⟩
  have hconv : ∀ X ∈ {X | ∃ A'' ∈ F, A ≠ A'' ∧ ∃ k : Fin (Q.disk A''.form).n, X = s • A''.side k},
      Convex ℝ X := by
    rintro X ⟨A'', -, -, k, rfl⟩
    rw [fs1_tile_side_eq]
    exact (convex_segment _ _).smul s
  have hcov : segment ℝ x y ⊆
      ⋃₀ {X | ∃ A'' ∈ F, A ≠ A'' ∧ ∃ k : Fin (Q.disk A''.form).n, X = s • A''.side k} := by
    intro p hp
    have hp' := hI hp
    rw [fs1_frontier_smul hs] at hp'
    obtain ⟨z, hz, rfl⟩ := hp'
    have hzA : z ∈ A.carrier := (fs1_carrier_closed A).frontier_subset hz
    have hY : IsClosed (⋃ A'' ∈ {A'' | A'' ∈ F ∧ A ≠ A''}, A''.carrier) :=
      hFne.isClosed_biUnion fun B _ => fs1_carrier_closed B
    have hsub : Metric.ball z 1 ∩ (A.carrier)ᶜ ⊆ ⋃ A'' ∈ {A'' | A'' ∈ F ∧ A ≠ A''}, A''.carrier := by
      rintro w ⟨hw1, hw2⟩
      have hw : w ∈ support T.tiles := by rw [T.cover]; trivial
      simp only [support, Set.mem_iUnion] at hw
      obtain ⟨A'', hA'', hwA''⟩ := hw
      have hne : A ≠ A'' := by
        rintro rfl
        exact hw2 hwA''
      refine Set.mem_biUnion (x := A'') ⟨⟨hA'', w, hwA'', ?_⟩, hne⟩ hwA''
      exact Metric.mem_cthickening_of_dist_le w z 1 A.carrier hzA (Metric.mem_ball.mp hw1).le
    have hzcl : z ∈ closure (Metric.ball z 1 ∩ (A.carrier)ᶜ) := by
      apply Metric.isOpen_ball.inter_closure
      refine ⟨Metric.mem_ball_self one_pos, ?_⟩
      rw [← frontier_compl] at hz
      exact frontier_subset_closure hz
    have hzY := hY.closure_subset (closure_mono hsub hzcl)
    simp only [Set.mem_iUnion] at hzY
    obtain ⟨A'', ⟨hA''F, hne⟩, hzA''⟩ := hzY
    have hzF : z ∈ frontier A''.carrier := by
      refine ⟨subset_closure hzA'', fun hint => ?_⟩
      have hzcl' : z ∈ closure (interior A.carrier) := by rwa [fs1_closure_interior_carrier]
      rw [mem_closure_iff] at hzcl'
      obtain ⟨q, hq1, hq2⟩ := hzcl' _ isOpen_interior hint
      exact Set.disjoint_left.mp (T.disjoint hA hA''F.1 hne) hq2 hq1
    rw [fs1_frontier_carrier, Set.mem_iUnion] at hzF
    obtain ⟨k, hk⟩ := hzF
    exact ⟨_, ⟨A'', hA''F, hne, k, rfl⟩, Set.smul_mem_smul_set hk⟩
  obtain ⟨X, ⟨A'', hA''F, hne, k, rfl⟩, u, v, huv, hsub⟩ := fs1_cover hxy hS hconv hcov
  refine ⟨A'', hA''F.1, hne, u, v, huv, fun z hz => ⟨(hsub hz).1, ?_⟩⟩
  rw [fs1_frontier_smul hs, fs1_frontier_carrier]
  exact Set.smul_set_mono (Set.subset_iUnion (fun k => A''.side k) k) (hsub hz).2

/-- Step 1 of the blueprint proof of `schedule_intermediate_sts_step1_boundary_align`:
There exist whole fine outer sides of `A` and `A'` that coincide and positively overlap
the coarse sides `c` and `d`. -/
private lemma schedule_intermediate_sts_step1_boundary_align_step1_fine_sides
    (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (T' : PlaneTiling G.P')
    (hfine : SideToSideSet (τ.decomposeIter m (G.scatter T'.tiles)))
    (A A' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles)
    (t : LayerTag m) (c d : Pt × Pt)
    (hc : c ∈ layerSides τ G m A.form t) (hd : d ∈ layerSides τ G m A'.form t)
    (hoverlap : OverlapPos (placedSeg ((τ.θ ^ m) • A.anchor) c)
      (placedSeg ((τ.θ ^ m) • A'.anchor) d)) :
    ∃ (e : Pt × Pt) (_he : e ∈ fineOuterSides τ G m A.form)
      (e' : Pt × Pt) (_he' : e' ∈ fineOuterSides τ G m A'.form),
      placedSeg ((τ.θ ^ m) • A.anchor) e = placedSeg ((τ.θ ^ m) • A'.anchor) e' ∧
      OverlapPos (segment ℝ c.1 c.2) (segment ℝ e.1 e.2) ∧
      OverlapPos (segment ℝ d.1 d.2) (segment ℝ e'.1 e'.2) := by
  have hs : τ.θ ^ m ≠ 0 := pow_ne_zero _ (by linarith [τ.one_lt])
  obtain ⟨x, y, hxy, hI⟩ := hoverlap
  have hIA : segment ℝ x y ⊆ frontier (((τ.θ ^ m) • A.anchor) +ᵥ parentRegion τ G m A.form) := by
    intro z hz
    have h1 := (hI hz).1
    rw [fs1_placedSeg_eq] at h1
    rw [fs1_frontier_vadd]
    exact Set.vadd_set_mono (fs1_layer_frontier τ G m A.form t c hc) h1
  have hIA' : segment ℝ x y ⊆ frontier (((τ.θ ^ m) • A'.anchor) +ᵥ parentRegion τ G m A'.form) := by
    intro z hz
    have h1 := (hI hz).2
    rw [fs1_placedSeg_eq] at h1
    rw [fs1_frontier_vadd]
    exact Set.vadd_set_mono (fs1_layer_frontier τ G m A'.form t d hd) h1
  by_cases hAA : A = A'
  · subst hAA
    have hI2 : segment ℝ x y ⊆ frontier ((τ.θ ^ m) • A.carrier) := by
      rw [← fs1_region_eq]
      exact hIA
    obtain ⟨A'', hA'', hne, u, v, huv, hJ⟩ := fs1_other T' hs A hA hxy hI2
    obtain ⟨e, he, e'', -, -, u', v', huv', hsub⟩ := fs1_core τ G m T' hfine A A'' hA hA'' hne u v huv
      (fun z hz => ⟨hIA (hJ hz).1, by rw [fs1_region_eq]; exact (hJ hz).2⟩)
    exact ⟨e, he, e, he, rfl,
      fs1_overlap_of_placed huv' fun z hz => ⟨(hI (hJ (hsub hz).1).1).1, (hsub hz).2⟩,
      fs1_overlap_of_placed huv' fun z hz => ⟨(hI (hJ (hsub hz).1).1).2, (hsub hz).2⟩⟩
  · obtain ⟨e, he, e', he', heq, u, v, huv, hsub⟩ :=
      fs1_core τ G m T' hfine A A' hA hA' hAA x y hxy (fun z hz => ⟨hIA hz, hIA' hz⟩)
    exact ⟨e, he, e', he', heq,
      fs1_overlap_of_placed huv fun z hz => ⟨(hI (hsub hz).1).1, (hsub hz).2⟩,
      fs1_overlap_of_placed huv fun z hz => ⟨(hI (hsub hz).1).2, heq ▸ (hsub hz).2⟩⟩
/-- Copy of the frame reconstruction: a point on the affine line of a nondegenerate segment is recovered from
its canonical coordinate. -/
private lemma sa1_ba_frame_reconstruct
    (x y z : Pt) (hxy : x ≠ y)
    (hz : z ∈ affineSpan ℝ ({x, y} : Set Pt)) :
    frameOrigin x y + segCoord x y z • canonDir (y - x) = z := by
  obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hz
  rw [AffineMap.lineMap_apply] at hr
  have hv : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hn : 0 < ‖y - x‖ := norm_pos_iff.mpr hv
  have hnorm : ‖y - x‖ ^ 2 = (y - x) 0 ^ 2 + (y - x) 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  have hsub0 : (y - x) 0 = y 0 - x 0 := by rfl
  have hsub1 : (y - x) 1 = y 1 - x 1 := by rfl
  by_cases hdir : 0 < (y - x) 0 ∨ ((y - x) 0 = 0 ∧ 0 < (y - x) 1)
  · rw [← hr]
    simp only [frameOrigin, canonDir, hdir, if_true, coord, segCoord]
    simp only [vadd_eq_add, vsub_eq_sub]
    dsimp
    ext i
    fin_cases i <;> simp
    all_goals field_simp [ne_of_gt hn]
    all_goals rw [hnorm]
    all_goals rw [hsub0, hsub1]
    all_goals ring
  · rw [← hr]
    simp only [frameOrigin, canonDir, hdir, if_false, coord, segCoord]
    simp only [vadd_eq_add, vsub_eq_sub]
    dsimp
    ext i
    fin_cases i <;> simp
    all_goals field_simp [ne_of_gt hn]
    all_goals rw [hnorm]
    all_goals rw [hsub0, hsub1]
    all_goals ring

private lemma sa1_ba_overlap_span
    {a b x y : Pt}
    (h : OverlapPos (segment ℝ a b) (segment ℝ x y)) :
    affineSpan ℝ ({a, b} : Set Pt) = affineSpan ℝ ({x, y} : Set Pt) := by
  obtain ⟨u, v, huv, huvsub⟩ := h
  have hmem {r s : Pt} {z : Pt} (hz : z ∈ segment ℝ r s) :
      z ∈ affineSpan ℝ ({r, s} : Set Pt) := by
    rw [segment_eq_image'] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    change r + q • (s - r) ∈ affineSpan ℝ ({r, s} : Set Pt)
    simpa [vadd_eq_add, vsub_eq_sub, add_comm] using
      (smul_vsub_vadd_mem_affineSpan_pair q r s)
  have huv_ab : affineSpan ℝ ({u, v} : Set Pt) = affineSpan ℝ ({a, b} : Set Pt) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne (hmem (huvsub (left_mem_segment ℝ u v)).1)
      (hmem (huvsub (right_mem_segment ℝ u v)).1) huv
  have huv_xy : affineSpan ℝ ({u, v} : Set Pt) = affineSpan ℝ ({x, y} : Set Pt) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne (hmem (huvsub (left_mem_segment ℝ u v)).2)
      (hmem (huvsub (right_mem_segment ℝ u v)).2) huv
  exact huv_ab.symm.trans huv_xy

private lemma sa1_ba_mem_segment
    {a b x : Pt} :
    x ∈ segment ℝ a b ↔ ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ x = a + r • (b - a) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr.1, hr.2, rfl⟩
  · rintro ⟨r, hr0, hr1, rfl⟩
    exact ⟨r, ⟨hr0, hr1⟩, rfl⟩

private lemma sa1_ba_smul_cancel
    {u : Pt} (hu : u ≠ 0) {r s : ℝ} (h : r • u = s • u) : r = s := by
  exact smul_left_injective ℝ hu h

private lemma sa1_ba_segment_endpoints
    {a b c d : Pt} (hab : a ≠ b) (h : segment ℝ a b = segment ℝ c d) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  have hc : c ∈ segment ℝ a b := h ▸ left_mem_segment ℝ c d
  have hd : d ∈ segment ℝ a b := h ▸ right_mem_segment ℝ c d
  have ha : a ∈ segment ℝ c d := h ▸ left_mem_segment ℝ a b
  have hb : b ∈ segment ℝ c d := h ▸ right_mem_segment ℝ a b
  rw [sa1_ba_mem_segment] at hc hd ha hb
  obtain ⟨r, hr0, hr1, rfl⟩ := hc
  obtain ⟨s, hs0, hs1, rfl⟩ := hd
  obtain ⟨u, hu0, hu1, hu⟩ := ha
  obtain ⟨v, hv0, hv1, hv⟩ := hb
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hk0 : a + r • (b - a) + u •
      (a + s • (b - a) - (a + r • (b - a))) =
      a + (r + u * (s - r)) • (b - a) := by module
  have hk1 : a + r • (b - a) + v •
      (a + s • (b - a) - (a + r • (b - a))) =
      a + (r + v * (s - r)) • (b - a) := by module
  have hzero : (0 : ℝ) • (b - a) = (r + u * (s - r)) • (b - a) := by
    rw [zero_smul]
    exact (add_eq_left.mp (hu.trans hk0).symm).symm
  have hone : (1 : ℝ) • (b - a) = (r + v * (s - r)) • (b - a) := by
    rw [one_smul]
    have h' : a + (b - a) = a + (r + v * (s - r)) • (b - a) := by
      calc
        a + (b - a) = b := by abel
        _ = a + r • (b - a) + v •
            (a + s • (b - a) - (a + r • (b - a))) := hv
        _ = a + (r + v * (s - r)) • (b - a) := hk1
    exact add_left_cancel h'
  have hz := sa1_ba_smul_cancel hne hzero
  have ho := sa1_ba_smul_cancel hne hone
  have hk : (r = 0 ∧ s = 1) ∨ (r = 1 ∧ s = 0) := by
    have h1 : r * (1 - u) = 0 := by
      nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hu1), mul_nonneg hu0 hs0]
    have h2 : u * s = 0 := by
      nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hu1), mul_nonneg hu0 hs0]
    rcases mul_eq_zero.mp h1 with h1 | h1
    · subst h1
      have : v * s = 1 := by linarith
      left
      refine ⟨rfl, ?_⟩
      nlinarith
    · have huone : u = 1 := by linarith
      subst huone
      have hs : s = 0 := by linarith
      subst hs
      right
      refine ⟨?_, rfl⟩
      nlinarith
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    constructor <;> simp
  · right
    constructor <;> simp

private lemma sa1_ba_canonDir_neg (v : Pt) : canonDir (-v) = canonDir v := by
  rcases lt_trichotomy (v 0) 0 with hv0 | hv0 | hv0
  · have hn : 0 < (-v) 0 ∨ ((-v) 0 = 0 ∧ 0 < (-v) 1) := by
      left
      simpa using neg_pos.mpr hv0
    have hp : ¬(0 < v 0 ∨ (v 0 = 0 ∧ 0 < v 1)) := by
      rintro (h | ⟨h, _⟩) <;> linarith
    unfold canonDir
    rw [if_pos hn, if_neg hp, norm_neg]
    module
  · rcases lt_trichotomy (v 1) 0 with hv1 | hv1 | hv1
    · have hn : 0 < (-v) 0 ∨ ((-v) 0 = 0 ∧ 0 < (-v) 1) := by
        right
        exact ⟨by simpa using congrArg Neg.neg hv0, by simpa using neg_pos.mpr hv1⟩
      have hp : ¬(0 < v 0 ∨ (v 0 = 0 ∧ 0 < v 1)) := by
        rintro (h | ⟨_, h⟩) <;> linarith
      unfold canonDir
      rw [if_pos hn, if_neg hp, norm_neg]
      module
    · have hz : v = 0 := by
        ext i
        fin_cases i
        · simpa using hv0
        · simpa using hv1
      subst v
      simp [canonDir]
    · have hp : 0 < v 0 ∨ (v 0 = 0 ∧ 0 < v 1) := by
        exact Or.inr ⟨hv0, hv1⟩
      have hn : ¬(0 < (-v) 0 ∨ ((-v) 0 = 0 ∧ 0 < (-v) 1)) := by
        rintro (h | ⟨_, h⟩)
        · change 0 < -(v 0) at h
          linarith
        · change 0 < -(v 1) at h
          linarith
      unfold canonDir
      rw [if_neg hn, if_pos hp, norm_neg]
      module
  · have hp : 0 < v 0 ∨ (v 0 = 0 ∧ 0 < v 1) := Or.inl hv0
    have hn : ¬(0 < (-v) 0 ∨ ((-v) 0 = 0 ∧ 0 < (-v) 1)) := by
      rintro (h | ⟨h, _⟩)
      · change 0 < -(v 0) at h
        linarith
      · change -(v 0) = 0 at h
        linarith
    unfold canonDir
    rw [if_neg hn, if_pos hp, norm_neg]
    module

private lemma sa1_ba_frameOrigin_swap (x y : Pt) :
    frameOrigin y x = frameOrigin x y := by
  rcases lt_trichotomy (x 0) (y 0) with h0 | h0 | h0
  · have hp : 0 < (y - x) 0 ∨ ((y - x) 0 = 0 ∧ 0 < (y - x) 1) := by
      left
      change 0 < y 0 - x 0
      linarith
    have hn : ¬(0 < (x - y) 0 ∨ ((x - y) 0 = 0 ∧ 0 < (x - y) 1)) := by
      push_neg
      constructor
      · change x 0 - y 0 ≤ 0
        linarith
      · intro h
        change x 0 - y 0 = 0 at h
        linarith
    unfold frameOrigin
    rw [if_neg hn, if_pos hp]
  · rcases lt_trichotomy (x 1) (y 1) with h1 | h1 | h1
    · have hp : 0 < (y - x) 0 ∨ ((y - x) 0 = 0 ∧ 0 < (y - x) 1) := by
        right
        constructor
        · change y 0 - x 0 = 0
          linarith
        · change 0 < y 1 - x 1
          linarith
      have hn : ¬(0 < (x - y) 0 ∨ ((x - y) 0 = 0 ∧ 0 < (x - y) 1)) := by
        push_neg
        constructor
        · change x 0 - y 0 ≤ 0
          linarith
        · intro _
          change x 1 - y 1 ≤ 0
          linarith
      unfold frameOrigin
      rw [if_neg hn, if_pos hp]
    · have hxy : x = y := by
        ext i
        fin_cases i
        · exact h0
        · exact h1
      subst y
      rfl
    · have hn : 0 < (x - y) 0 ∨ ((x - y) 0 = 0 ∧ 0 < (x - y) 1) := by
        right
        constructor
        · change x 0 - y 0 = 0
          linarith
        · change 0 < x 1 - y 1
          linarith
      have hp : ¬(0 < (y - x) 0 ∨ ((y - x) 0 = 0 ∧ 0 < (y - x) 1)) := by
        push_neg
        constructor
        · change y 0 - x 0 ≤ 0
          linarith
        · intro _
          change y 1 - x 1 ≤ 0
          linarith
      unfold frameOrigin
      rw [if_pos hn, if_neg hp]
  · have hn : 0 < (x - y) 0 ∨ ((x - y) 0 = 0 ∧ 0 < (x - y) 1) := by
      left
      change 0 < x 0 - y 0
      linarith
    have hp : ¬(0 < (y - x) 0 ∨ ((y - x) 0 = 0 ∧ 0 < (y - x) 1)) := by
      push_neg
      constructor
      · change y 0 - x 0 ≤ 0
        linarith
      · intro h
        change y 0 - x 0 = 0 at h
        linarith
    unfold frameOrigin
    rw [if_pos hn, if_neg hp]

private lemma sa1_ba_overlap_ne
    {a b c d : Pt} (h : OverlapPos (segment ℝ a b) (segment ℝ c d)) :
    a ≠ b ∧ c ≠ d := by
  obtain ⟨x, y, hxy, hsub⟩ := h
  constructor
  · intro hab
    subst b
    have hx : x = a := by
      have hx' := (hsub (left_mem_segment ℝ x y)).1
      simpa only [segment_same, mem_singleton_iff] using hx'
    have hy : y = a := by
      have hy' := (hsub (right_mem_segment ℝ x y)).1
      simpa only [segment_same, mem_singleton_iff] using hy'
    exact hxy (hx.trans hy.symm)
  · intro hcd
    subst d
    have hx : x = c := by
      have hx' := (hsub (left_mem_segment ℝ x y)).2
      simpa only [segment_same, mem_singleton_iff] using hx'
    have hy : y = c := by
      have hy' := (hsub (right_mem_segment ℝ x y)).2
      simpa only [segment_same, mem_singleton_iff] using hy'
    exact hxy (hx.trans hy.symm)

private lemma sa1_ba_frameOrigin_add (v x y : Pt) :
    frameOrigin (v + x) (v + y) = v + frameOrigin x y := by
  have hd : v + y - (v + x) = y - x := by abel
  simp only [frameOrigin, hd]
  split_ifs <;> rfl

private lemma sa1_ba_segment_eq_coord_bounds
    (z w o u : Pt) (r s : ℝ)
    (hz : o + r • u = z) (hw : o + s • u = w) :
    segment ℝ z w = segment ℝ (o + min r s • u) (o + max r s • u) := by
  rcases le_total r s with hrs | hsr
  · rw [min_eq_left hrs, max_eq_right hrs, hz, hw]
  · rw [min_eq_right hsr, max_eq_left hsr, hz, hw, segment_symm]

/-- Equal atoms on coinciding fine sides give coinciding placed coarse sides
(the argument of `step2_eq`, with arbitrary translations). -/
private lemma sa1_atom_placed_eq {va vb : Pt} {c d e e' : Pt × Pt}
    (heq : placedSeg va e = placedSeg vb e')
    (hov_c : OverlapPos (segment ℝ c.1 c.2) (segment ℝ e.1 e.2))
    (hov_d : OverlapPos (segment ℝ d.1 d.2) (segment ℝ e'.1 e'.2))
    (hatom : atom e c = atom e' d) :
    placedSeg va c = placedSeg vb d := by
  have he_ne : e.1 ≠ e.2 := (sa1_ba_overlap_ne hov_c).2
  have he'_ne : e'.1 ≠ e'.2 := (sa1_ba_overlap_ne hov_d).2
  have hE_ne : va + e.1 ≠ va + e.2 := by
    intro h
    exact he_ne (add_left_cancel h)
  have hends :
      (vb + e'.1 = va + e.1 ∧ vb + e'.2 = va + e.2) ∨
        (vb + e'.1 = va + e.2 ∧ vb + e'.2 = va + e.1) := by
    apply sa1_ba_segment_endpoints hE_ne
    simpa only [placedSeg] using heq
  have hO : va + frameOrigin e.1 e.2 = vb + frameOrigin e'.1 e'.2 := by
    rw [← sa1_ba_frameOrigin_add, ← sa1_ba_frameOrigin_add]
    rcases hends with hends | hends
    · rw [hends.1, hends.2]
    · rw [hends.1, hends.2, sa1_ba_frameOrigin_swap]
  have hD : canonDir (e.2 - e.1) = canonDir (e'.2 - e'.1) := by
    rcases hends with hends | hends
    · have hv : e'.2 - e'.1 = e.2 - e.1 := by
        have hg := congrArg₂ (fun x y : Pt => x - y) hends.2 hends.1
        calc
          e'.2 - e'.1 = (vb + e'.2) - (vb + e'.1) := by abel
          _ = (va + e.2) - (va + e.1) := hg
          _ = e.2 - e.1 := by abel
      rw [hv]
    · have hv : e'.2 - e'.1 = -(e.2 - e.1) := by
        have hg := congrArg₂ (fun x y : Pt => x - y) hends.2 hends.1
        calc
          e'.2 - e'.1 = (vb + e'.2) - (vb + e'.1) := by abel
          _ = (va + e.1) - (va + e.2) := hg
          _ = -(e.2 - e.1) := by abel
      rw [hv]
      exact (sa1_ba_canonDir_neg (e.2 - e.1)).symm
  have hp :
      min (segCoord e.1 e.2 c.1) (segCoord e.1 e.2 c.2) =
        min (segCoord e'.1 e'.2 d.1) (segCoord e'.1 e'.2 d.2) := by
    have h := congrArg (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.1) hatom
    simpa only [atom] using h
  have hq :
      max (segCoord e.1 e.2 c.1) (segCoord e.1 e.2 c.2) =
        max (segCoord e'.1 e'.2 d.1) (segCoord e'.1 e'.2 d.2) := by
    have h := congrArg (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.2) hatom
    simpa only [atom] using h
  have hspan_c := sa1_ba_overlap_span hov_c
  have hspan_d := sa1_ba_overlap_span hov_d
  have hc1_line : c.1 ∈ affineSpan ℝ ({e.1, e.2} : Set Pt) := by
    rw [← hspan_c]
    exact subset_affineSpan ℝ ({c.1, c.2} : Set Pt) (by simp)
  have hc2_line : c.2 ∈ affineSpan ℝ ({e.1, e.2} : Set Pt) := by
    rw [← hspan_c]
    exact subset_affineSpan ℝ ({c.1, c.2} : Set Pt) (by simp)
  have hd1_line : d.1 ∈ affineSpan ℝ ({e'.1, e'.2} : Set Pt) := by
    rw [← hspan_d]
    exact subset_affineSpan ℝ ({d.1, d.2} : Set Pt) (by simp)
  have hd2_line : d.2 ∈ affineSpan ℝ ({e'.1, e'.2} : Set Pt) := by
    rw [← hspan_d]
    exact subset_affineSpan ℝ ({d.1, d.2} : Set Pt) (by simp)
  have hc1 := sa1_ba_frame_reconstruct e.1 e.2 c.1 he_ne hc1_line
  have hc2 := sa1_ba_frame_reconstruct e.1 e.2 c.2 he_ne hc2_line
  have hd1 := sa1_ba_frame_reconstruct e'.1 e'.2 d.1 he'_ne hd1_line
  have hd2 := sa1_ba_frame_reconstruct e'.1 e'.2 d.2 he'_ne hd2_line
  have hc1g :
      va + frameOrigin e.1 e.2 + segCoord e.1 e.2 c.1 • canonDir (e.2 - e.1) = va + c.1 := by
    calc
      _ = va + (frameOrigin e.1 e.2 +
          segCoord e.1 e.2 c.1 • canonDir (e.2 - e.1)) := by abel
      _ = va + c.1 := congrArg (va + ·) hc1
  have hc2g :
      va + frameOrigin e.1 e.2 + segCoord e.1 e.2 c.2 • canonDir (e.2 - e.1) = va + c.2 := by
    calc
      _ = va + (frameOrigin e.1 e.2 +
          segCoord e.1 e.2 c.2 • canonDir (e.2 - e.1)) := by abel
      _ = va + c.2 := congrArg (va + ·) hc2
  have hd1g :
      vb + frameOrigin e'.1 e'.2 + segCoord e'.1 e'.2 d.1 • canonDir (e'.2 - e'.1) = vb + d.1 := by
    calc
      _ = vb + (frameOrigin e'.1 e'.2 +
          segCoord e'.1 e'.2 d.1 • canonDir (e'.2 - e'.1)) := by abel
      _ = vb + d.1 := congrArg (vb + ·) hd1
  have hd2g :
      vb + frameOrigin e'.1 e'.2 + segCoord e'.1 e'.2 d.2 • canonDir (e'.2 - e'.1) = vb + d.2 := by
    calc
      _ = vb + (frameOrigin e'.1 e'.2 +
          segCoord e'.1 e'.2 d.2 • canonDir (e'.2 - e'.1)) := by abel
      _ = vb + d.2 := congrArg (vb + ·) hd2
  change segment ℝ (va + c.1) (va + c.2) = segment ℝ (vb + d.1) (vb + d.2)
  calc
    segment ℝ (va + c.1) (va + c.2) =
        segment ℝ
          (va + frameOrigin e.1 e.2 +
            min (segCoord e.1 e.2 c.1) (segCoord e.1 e.2 c.2) • canonDir (e.2 - e.1))
          (va + frameOrigin e.1 e.2 +
            max (segCoord e.1 e.2 c.1) (segCoord e.1 e.2 c.2) • canonDir (e.2 - e.1)) :=
      sa1_ba_segment_eq_coord_bounds _ _ _ _ _ _ hc1g hc2g
    _ = segment ℝ
          (vb + frameOrigin e'.1 e'.2 +
            min (segCoord e'.1 e'.2 d.1) (segCoord e'.1 e'.2 d.2) • canonDir (e'.2 - e'.1))
          (vb + frameOrigin e'.1 e'.2 +
            max (segCoord e'.1 e'.2 d.1) (segCoord e'.1 e'.2 d.2) • canonDir (e'.2 - e'.1)) := by
      rw [hO, hD, hp, hq]
    _ = segment ℝ (vb + d.1) (vb + d.2) :=
      (sa1_ba_segment_eq_coord_bounds _ _ _ _ _ _ hd1g hd2g).symm

private lemma sa1_segment_isClosed (p q : Pt) : IsClosed (segment ℝ p q) := by
  rw [segment_eq_image_lineMap]
  exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed

private lemma sa1_segment_smul (s : ℝ) (p q : Pt) :
    segment ℝ (s • p) (s • q) = s • segment ℝ p q := by
  let f : Pt →ᵃ[ℝ] Pt := (LinearMap.lsmul ℝ Pt s).toAffineMap
  exact (image_segment ℝ f _ _).symm

private lemma sa1_overlap_unscale {s : ℝ} (hs : s ≠ 0) {p q p' q' : Pt}
    (h : OverlapPos (segment ℝ (s • p) (s • q)) (segment ℝ (s • p') (s • q'))) :
    OverlapPos (segment ℝ p q) (segment ℝ p' q') := by
  obtain ⟨x, y, hxy, hsub⟩ := h
  refine ⟨s⁻¹ • x, s⁻¹ • y, fun h' => hxy ?_, ?_⟩
  · simpa [smul_smul, hs] using congrArg (s • ·) h'
  · rw [sa1_segment_smul]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨h1, h2⟩ := hsub hw
    rw [sa1_segment_smul] at h1 h2
    obtain ⟨w1, hw1, rfl⟩ := h1
    obtain ⟨w2, hw2, he⟩ := h2
    have : w2 = w1 := smul_right_injective Pt hs he
    subst this
    show s⁻¹ • s • w2 ∈ _
    rw [inv_smul_smul₀ hs]
    exact ⟨hw1, hw2⟩

private lemma sa1_overlap_false {p q p' q' : Pt} (hov : OverlapPos (segment ℝ p q) (segment ℝ p' q'))
    (hs : segment ℝ p q ∩ segment ℝ p' q' ⊆ ({p, q} : Set Pt) ∩ {p', q'}) : False := by
  obtain ⟨x, y, hxy, hsub⟩ := hov
  exact fs1_segment_infinite hxy
    ((((Set.finite_singleton q).insert p).inter_of_left _).subset (hsub.trans hs))

private lemma sa1_placed_simple (B : PlacedTile P) {i j : Fin (P.disk B.form).n} (hij : i ≠ j) {z : Pt}
    (hi : z ∈ B.side i) (hj : z ∈ B.side j) : z = B.vertex i ∨ z = B.vertex (finRotate _ i) := by
  simp only [PlacedTile.side, PolygonalDisk.side] at hi hj
  obtain ⟨z0, hz0, rfl⟩ := hi
  obtain ⟨z1, hz1, he⟩ := hj
  have : z1 = z0 := vadd_left_cancel _ he
  subst this
  have h := ((P.disk B.form).simple i j hij ⟨hz0, hz1⟩).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl
  · left; rfl
  · right; rfl

private lemma sa1_same_tile_side (B : PlacedTile P) (i j : Fin (P.disk B.form).n)
    (h : OverlapPos (B.side i) (B.side j)) : i = j := by
  by_contra hij
  rw [fs1_tile_side_eq, fs1_tile_side_eq] at h
  refine sa1_overlap_false h ?_
  rintro z ⟨hz1, hz2⟩
  rw [← fs1_tile_side_eq] at hz1 hz2
  refine ⟨?_, ?_⟩
  · rcases sa1_placed_simple B hij hz1 hz2 with rfl | rfl <;> simp
  · rcases sa1_placed_simple B (Ne.symm hij) hz2 hz1 with rfl | rfl <;> simp

/-- The cross product with `w`, a continuous linear functional vanishing on `w`. -/
private def sa1_cross (w : Pt) : Pt →L[ℝ] ℝ :=
  w 0 • EuclideanSpace.proj (1 : Fin 2) - w 1 • EuclideanSpace.proj (0 : Fin 2)

private lemma sa1_cross_apply (w p : Pt) : sa1_cross w p = w 0 * p 1 - w 1 * p 0 := by
  simp [sa1_cross]

private lemma sa1_cross_on_segment {a b x y p : Pt} (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (hp : p ∈ segment ℝ a b) : sa1_cross (y - x) p = sa1_cross (y - x) x := by
  rw [segment_eq_image'] at hx hy hp
  obtain ⟨r, -, rfl⟩ := hx
  obtain ⟨s, -, rfl⟩ := hy
  obtain ⟨t, -, rfl⟩ := hp
  simp only [sa1_cross_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private lemma sa1_tendsto (p n : Pt) :
    Filter.Tendsto (fun δ : ℝ => p + δ • n) (nhdsWithin 0 (Set.Ioi 0)) (nhds p) := by
  have : Filter.Tendsto (fun δ : ℝ => p + δ • n) (nhds 0) (nhds (p + (0 : ℝ) • n)) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
  simpa using this.mono_left nhdsWithin_le_nhds

private lemma sa1_eventually {U : Set Pt} (hU : IsOpen U) {p : Pt} (hp : p ∈ U) (n : Pt) :
    ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), p + δ • n ∈ U ∧ 0 < δ :=
  ((sa1_tendsto p n).eventually (hU.mem_nhds hp)).and self_mem_nhdsWithin

private lemma sa1_half {C U : Set Pt} (hC : IsClosed C) (hU : IsOpen U) (hUc : Convex ℝ U)
    (g : Pt →L[ℝ] ℝ) (k : ℝ) {n : Pt} (hn : 0 < g n) {z : Pt} (hz : z ∈ U)
    (hzC : z ∈ closure (interior C)) (hfr : ∀ p ∈ U, p ∈ frontier C → g p = k) :
    U ∩ {p | k < g p} ⊆ interior C ∨ U ∩ {p | g p < k} ⊆ interior C := by
  have hsplit : ∀ H ⊆ U, IsPreconnected H → (∀ p ∈ H, g p ≠ k) → H ⊆ interior C ∨ H ⊆ Cᶜ := by
    intro H hHU hH hHk
    refine hH.subset_or_subset isOpen_interior hC.isOpen_compl ?_ ?_
    · exact Set.disjoint_left.mpr fun p hp hpc => hpc (interior_subset hp)
    · intro p hp
      by_cases hpi : p ∈ interior C
      · exact Or.inl hpi
      · right
        intro hpC
        exact hHk p hp (hfr p (hHU hp) ⟨subset_closure hpC, hpi⟩)
  have hconvP : Convex ℝ (U ∩ {p | k < g p}) := hUc.inter (convex_halfSpace_gt g.toLinearMap.isLinear k)
  have hconvM : Convex ℝ (U ∩ {p | g p < k}) := hUc.inter (convex_halfSpace_lt g.toLinearMap.isLinear k)
  rcases hsplit _ Set.inter_subset_left hconvP.isPreconnected (fun p hp => ne_of_gt hp.2) with h1 | h1
  · exact Or.inl h1
  rcases hsplit _ Set.inter_subset_left hconvM.isPreconnected (fun p hp => ne_of_lt hp.2) with h2 | h2
  · exact Or.inr h2
  exfalso
  obtain ⟨p, hpU, hpi⟩ := mem_closure_iff.mp hzC U hU hz
  have hpC : p ∈ C := interior_subset hpi
  have hgp : g p = k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact h2 ⟨hpU, hlt⟩ hpC
    · exact h1 ⟨hpU, hgt⟩ hpC
  obtain ⟨δ, hδU, hδ⟩ := (sa1_eventually (hU.inter isOpen_interior) ⟨hpU, hpi⟩ n).exists
  refine h1 ⟨hδU.1, ?_⟩ (interior_subset hδU.2)
  show k < g (p + δ • n)
  rw [map_add, map_smul, hgp, smul_eq_mul]
  nlinarith

/-- Two tiles of a family with disjoint interiors inside a region `R` cannot have
positively overlapping sides on the frontier of `R`, unless they are the same tile. -/
private lemma sa1_frontier_tiles_eq (S : Set (PlacedTile P)) (hS : DisjointInteriors S) (R : Set Pt)
    (hR : ∀ B ∈ S, B.carrier ⊆ R) {B1 B2 : PlacedTile P} (h1 : B1 ∈ S) (h2 : B2 ∈ S)
    (i1 : Fin (P.disk B1.form).n) (i2 : Fin (P.disk B2.form).n)
    (hf1 : B1.side i1 ⊆ frontier R) (hov : OverlapPos (B1.side i1) (B2.side i2)) : B1 = B2 := by
  by_contra hne
  obtain ⟨x, y, hxy, hsub⟩ := hov
  obtain ⟨z, hzxy, hzF⟩ := ((fs1_segment_infinite hxy).diff (Set.toFinite ({B1.vertex i1,
    B1.vertex (finRotate _ i1), B2.vertex i2, B2.vertex (finRotate _ i2)} : Set Pt))).nonempty
  have hz1 : z ∈ B1.side i1 := (hsub hzxy).1
  have hz2 : z ∈ B2.side i2 := (hsub hzxy).2
  set g := sa1_cross (y - x) with hg
  set k := g x with hk
  have hl : ∀ (B : PlacedTile P) (i : Fin (P.disk B.form).n), segment ℝ x y ⊆ B.side i →
      ∀ p ∈ B.side i, g p = k := by
    intro B i hxyB p hp
    rw [fs1_tile_side_eq] at hxyB hp
    exact sa1_cross_on_segment (hxyB (left_mem_segment ℝ x y)) (hxyB (right_mem_segment ℝ x y)) hp
  have hl1 := hl B1 i1 fun w hw => (hsub hw).1
  have hl2 := hl B2 i2 fun w hw => (hsub hw).2
  have hK : ∀ (B : PlacedTile P) (i : Fin (P.disk B.form).n), z ∈ B.side i → z ≠ B.vertex i →
      z ≠ B.vertex (finRotate _ i) →
      ∃ r > 0, ∀ p ∈ Metric.ball z r, p ∈ frontier B.carrier → p ∈ B.side i := by
    intro B i hzi hza hzb
    let K := ⋃ j ∈ ({i}ᶜ : Set (Fin (P.disk B.form).n)), B.side j
    have hKc : IsClosed K := (Set.toFinite _).isClosed_biUnion fun j _ => by
      rw [fs1_tile_side_eq]; exact sa1_segment_isClosed _ _
    have hzK : z ∉ K := by
      simp only [K, Set.mem_iUnion]
      rintro ⟨j, hj, hzj⟩
      rcases sa1_placed_simple B (Set.mem_compl_singleton_iff.mp hj).symm hzi hzj with h | h
      exacts [hza h, hzb h]
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hKc.isOpen_compl z hzK
    refine ⟨r, hr, fun p hp hpf => ?_⟩
    rw [fs1_frontier_carrier, Set.mem_iUnion] at hpf
    obtain ⟨j, hj⟩ := hpf
    by_cases hji : j = i
    · subst hji; exact hj
    · exact absurd (Set.mem_biUnion (x := j) (Set.mem_compl_singleton_iff.mpr hji) hj) (hball hp)
  obtain ⟨r1, hr1, hb1⟩ := hK B1 i1 hz1 (fun h => hzF (by simp [h])) (fun h => hzF (by simp [h]))
  obtain ⟨r2, hr2, hb2⟩ := hK B2 i2 hz2 (fun h => hzF (by simp [h])) (fun h => hzF (by simp [h]))
  set U := Metric.ball z (min r1 r2) with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := Metric.mem_ball_self (lt_min hr1 hr2)
  have hw : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  set n : Pt := !₂[-((y - x) 1), (y - x) 0] with hndef
  have hn : 0 < g n := by
    rw [hg, sa1_cross_apply]
    have h0 : n 0 = -((y - x) 1) := by simp [hndef]
    have h1' : n 1 = (y - x) 0 := by simp [hndef]
    rw [h0, h1']
    have : (y - x) 0 ≠ 0 ∨ (y - x) 1 ≠ 0 := by
      by_contra h
      push_neg at h
      apply hw
      ext i
      fin_cases i
      · simpa using h.1
      · simpa using h.2
    rcases this with h | h
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg ((y - x) 1)]
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg ((y - x) 0)]
  have hgz : g z = k := hl1 z hz1
  have half1 := sa1_half (fs1_carrier_closed B1) hU (convex_ball _ _) g k hn hzU
    (by rw [fs1_closure_interior_carrier]; exact fs1_side_subset_carrier B1 i1 hz1)
    (fun p hp hpf => hl1 p (hb1 p (Metric.ball_subset_ball (min_le_left _ _) hp) hpf))
  have half2 := sa1_half (fs1_carrier_closed B2) hU (convex_ball _ _) g k hn hzU
    (by rw [fs1_closure_interior_carrier]; exact fs1_side_subset_carrier B2 i2 hz2)
    (fun p hp hpf => hl2 p (hb2 p (Metric.ball_subset_ball (min_le_right _ _) hp) hpf))
  have hdisj : Disjoint (interior B1.carrier) (interior B2.carrier) := hS h1 h2 hne
  obtain ⟨δ, hδU, hδ⟩ := (sa1_eventually hU hzU n).exists
  obtain ⟨δ', hδU', hδ'⟩ := (sa1_eventually hU hzU (-n)).exists
  have hP : z + δ • n ∈ U ∩ {p | k < g p} := by
    refine ⟨hδU, ?_⟩
    show k < g (z + δ • n)
    rw [map_add, map_smul, hgz, smul_eq_mul]
    nlinarith
  have hM : z + δ' • (-n) ∈ U ∩ {p | g p < k} := by
    refine ⟨hδU', ?_⟩
    show g (z + δ' • (-n)) < k
    rw [map_add, map_smul, map_neg, hgz, smul_eq_mul]
    nlinarith
  have hcl : ∀ p ∈ U, g p = k → p ∈ closure (U ∩ {p | k < g p}) := by
    intro p hp hgp
    refine mem_closure_of_tendsto (sa1_tendsto p n) ?_
    filter_upwards [sa1_eventually hU hp n] with δ hδ
    refine ⟨hδ.1, ?_⟩
    show k < g (p + δ • n)
    rw [map_add, map_smul, hgp, smul_eq_mul]
    nlinarith [hδ.2]
  have hopp : ∀ (C1 C2 : Set Pt), IsClosed C1 → C1 ⊆ R → C2 ⊆ R →
      U ∩ {p | k < g p} ⊆ interior C1 → U ∩ {p | g p < k} ⊆ interior C2 → False := by
    intro C1 C2 hC1 hC1R hC2R hP1 hM2
    have hUR : U ⊆ R := by
      intro p hp
      rcases lt_trichotomy (g p) k with hlt | heq | hgt
      · exact hC2R (interior_subset (hM2 ⟨hp, hlt⟩))
      · exact hC1R (hC1.closure_subset_iff.mpr (hP1.trans interior_subset) (hcl p hp heq))
      · exact hC1R (interior_subset (hP1 ⟨hp, hgt⟩))
    exact (hf1 hz1).2 (interior_maximal hUR hU hzU)
  rcases half1 with h1P | h1M <;> rcases half2 with h2P | h2M
  · exact Set.disjoint_left.mp hdisj (h1P hP) (h2P hP)
  · exact hopp _ _ (fs1_carrier_closed B1) (hR B1 h1) (hR B2 h2) h1P h2M
  · exact hopp _ _ (fs1_carrier_closed B2) (hR B2 h2) (hR B1 h1) h2P h1M
  · exact Set.disjoint_left.mp hdisj (h1M hM) (h2M hM)

private lemma sa1_disjoint_decompose (S : Set (PlacedTile P)) (hS : DisjointInteriors S) :
    DisjointInteriors (τ.decompose S) := by
  intro C1 hC1 C2 hC2 hne
  simp only [Substitution.decompose, Set.mem_iUnion] at hC1 hC2
  obtain ⟨B1, hB1, hC1⟩ := hC1
  obtain ⟨B2, hB2, hC2⟩ := hC2
  show Disjoint (interior C1.carrier) (interior C2.carrier)
  have hθ : τ.θ ≠ 0 := by linarith [τ.one_lt]
  have hsub : ∀ B C, C ∈ τ.decomposeTile B → interior C.carrier ⊆ τ.θ • interior B.carrier := by
    intro B C hC
    rw [← interior_smul₀ hθ, ← fs1_support_decomposeTile τ B]
    exact interior_mono (Set.subset_biUnion_of_mem (u := fun B => B.carrier) hC)
  by_cases hB : B1 = B2
  · subst hB
    simp only [Substitution.decomposeTile, translateSet, Set.mem_image] at hC1 hC2
    obtain ⟨R1, hR1, rfl⟩ := hC1
    obtain ⟨R2, hR2, rfl⟩ := hC2
    have hR : R1 ≠ R2 := fun h => hne (h ▸ rfl)
    have hd : Disjoint (interior R1.carrier) (interior R2.carrier) := (τ.rule B1.form).disjoint hR1 hR2 hR
    rw [fs1_translate_carrier, fs1_translate_carrier, interior_vadd, interior_vadd,
      ← Set.image_vadd, ← Set.image_vadd]
    exact (Set.disjoint_image_iff (fun a b h => vadd_left_cancel (τ.θ • B1.anchor) h)).mpr hd
  · refine Disjoint.mono (hsub B1 C1 hC1) (hsub B2 C2 hC2) ?_
    rw [← Set.image_smul, ← Set.image_smul]
    exact (Set.disjoint_image_iff (smul_right_injective Pt hθ)).mpr (hS hB1 hB2 hB)

private lemma sa1_disjoint_iter (n : ℕ) (S : Set (PlacedTile P)) (hS : DisjointInteriors S) :
    DisjointInteriors (τ.decomposeIter n S) := by
  induction n with
  | zero => exact hS
  | succ n ih => exact sa1_disjoint_decompose τ _ ih

/-- Two listed sides of the same layer that overlap with positive length are equal. -/
private lemma sa1_layer_eq (m : ℕ) (α : G.P'.Form) (t : LayerTag m) (c c' : Pt × Pt)
    (hc : c ∈ layerSides τ G m α t) (hc' : c' ∈ layerSides τ G m α t)
    (hov : OverlapPos (segment ℝ c.1 c.2) (segment ℝ c'.1 c'.2)) : c = c' := by
  have hθm : τ.θ ^ m ≠ 0 := pow_ne_zero _ (by linarith [τ.one_lt])
  cases t with
  | top =>
    obtain ⟨a, rfl⟩ := hc
    obtain ⟨b, rfl⟩ := hc'
    simp only [parentSide] at hov
    have h := sa1_overlap_unscale hθm hov
    by_cases hab : a = b
    · rw [hab]
    · exact (sa1_overlap_false h ((G.P'.disk α).simple a b hab)).elim
  | level j =>
    obtain ⟨B, hB, i, rfl, hfr⟩ := hc
    obtain ⟨B', hB', i', rfl, -⟩ := hc'
    have hs : τ.θ ^ (m - (j : ℕ)) ≠ 0 := pow_ne_zero _ (by linarith [τ.one_lt])
    have h := sa1_overlap_unscale hs hov
    rw [← fs1_tile_side_eq, ← fs1_tile_side_eq] at h
    have hfr' : B.side i ⊆ frontier (parentRegion τ G (j : ℕ) α) := by
      have hθj : τ.θ ^ (j : ℕ) ≠ 0 := pow_ne_zero _ (by linarith [τ.one_lt])
      rw [fs1_tile_side_eq]
      simp only at hfr
      rw [sa1_segment_smul, parentRegion, fs1_frontier_smul hθm] at hfr
      rw [parentRegion, fs1_frontier_smul hθj]
      have hpow : τ.θ ^ m = τ.θ ^ (m - (j : ℕ)) * τ.θ ^ (j : ℕ) := by
        rw [← pow_add, Nat.sub_add_cancel j.isLt.le]
      rw [hpow, mul_smul] at hfr
      exact (smul_set_subset_smul_set_iff₀ hs).mp hfr
    have hBB := sa1_frontier_tiles_eq _ (sa1_disjoint_iter τ _ _ (G.dissect α).disjoint)
      (parentRegion τ G (j : ℕ) α) (fun B hB => by
        rw [← fs1_fineTiles_support]
        exact Set.subset_biUnion_of_mem (u := fun B => B.carrier) hB)
      hB hB' i i' hfr' h
    subst hBB
    have := sa1_same_tile_side B i i' h
    subst this
    rfl

/-- Step 1 of the blueprint proof of `schedule_intermediate_sts_step1_boundary_align_step2_endpoints`:
Equal schedules give the same atom through that point. -/
private lemma schedule_intermediate_sts_step1_boundary_align_step2_endpoints_step1_atom
    (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (A A' : PlacedTile G.P')
    (t : LayerTag m) (c d : Pt × Pt)
    (hc : c ∈ layerSides τ G m A.form t) (hd : d ∈ layerSides τ G m A'.form t)
    (e e' : Pt × Pt)
    (he : e ∈ fineOuterSides τ G m A.form) (he' : e' ∈ fineOuterSides τ G m A'.form)
    (heq : placedSeg ((τ.θ ^ m) • A.anchor) e = placedSeg ((τ.θ ^ m) • A'.anchor) e')
    (hov_c : OverlapPos (segment ℝ c.1 c.2) (segment ℝ e.1 e.2))
    (hov_d : OverlapPos (segment ℝ d.1 d.2) (segment ℝ e'.1 e'.2))
    (h_sch : EndpointSchedule τ G m A.form e t = EndpointSchedule τ G m A'.form e' t)
    (hoverlap : OverlapPos (placedSeg ((τ.θ ^ m) • A.anchor) c)
      (placedSeg ((τ.θ ^ m) • A'.anchor) d)) :
    atom e c = atom e' d := by
  have _ := he
  have _ := he'
  have _ := hov_d
  have hmem : atom e c ∈ EndpointSchedule τ G m A.form e t := ⟨c, hc, hov_c, rfl⟩
  rw [h_sch] at hmem
  obtain ⟨d', hd', hov_d', hat⟩ := hmem
  have hpl : placedSeg ((τ.θ ^ m) • A.anchor) c = placedSeg ((τ.θ ^ m) • A'.anchor) d' :=
    sa1_atom_placed_eq heq hov_c hov_d' hat
  have hdd : d' = d := by
    apply sa1_layer_eq τ G m A'.form t d' d hd' hd
    obtain ⟨x, y, hxy, hsub⟩ := hoverlap
    exact fs1_overlap_of_placed hxy (fun z hz => ⟨hpl ▸ (hsub hz).1, (hsub hz).2⟩)
  rw [hat, hdd]

/-- A point on the affine line of a nondegenerate segment is recovered from
its canonical coordinate. -/
private lemma boundary_align_frame_reconstruct
    (x y z : Pt) (hxy : x ≠ y)
    (hz : z ∈ affineSpan ℝ ({x, y} : Set Pt)) :
    frameOrigin x y + segCoord x y z • canonDir (y - x) = z := by
  obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hz
  rw [AffineMap.lineMap_apply] at hr
  have hv : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hn : 0 < ‖y - x‖ := norm_pos_iff.mpr hv
  have hnorm : ‖y - x‖ ^ 2 = (y - x) 0 ^ 2 + (y - x) 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  have hsub0 : (y - x) 0 = y 0 - x 0 := by rfl
  have hsub1 : (y - x) 1 = y 1 - x 1 := by rfl
  by_cases hdir : 0 < (y - x) 0 ∨ ((y - x) 0 = 0 ∧ 0 < (y - x) 1)
  · rw [← hr]
    simp only [frameOrigin, canonDir, hdir, if_true, coord, segCoord]
    simp only [vadd_eq_add, vsub_eq_sub]
    dsimp
    ext i
    fin_cases i <;> simp
    all_goals field_simp [ne_of_gt hn]
    all_goals rw [hnorm]
    all_goals rw [hsub0, hsub1]
    all_goals ring
  · rw [← hr]
    simp only [frameOrigin, canonDir, hdir, if_false, coord, segCoord]
    simp only [vadd_eq_add, vsub_eq_sub]
    dsimp
    ext i
    fin_cases i <;> simp
    all_goals field_simp [ne_of_gt hn]
    all_goals rw [hnorm]
    all_goals rw [hsub0, hsub1]
    all_goals ring

private lemma boundary_align_overlap_span
    {a b x y : Pt}
    (h : OverlapPos (segment ℝ a b) (segment ℝ x y)) :
    affineSpan ℝ ({a, b} : Set Pt) = affineSpan ℝ ({x, y} : Set Pt) := by
  obtain ⟨u, v, huv, huvsub⟩ := h
  have hmem {r s : Pt} {z : Pt} (hz : z ∈ segment ℝ r s) :
      z ∈ affineSpan ℝ ({r, s} : Set Pt) := by
    rw [segment_eq_image'] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    change r + q • (s - r) ∈ affineSpan ℝ ({r, s} : Set Pt)
    simpa [vadd_eq_add, vsub_eq_sub, add_comm] using
      (smul_vsub_vadd_mem_affineSpan_pair q r s)
  have huv_ab : affineSpan ℝ ({u, v} : Set Pt) = affineSpan ℝ ({a, b} : Set Pt) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne (hmem (huvsub (left_mem_segment ℝ u v)).1)
      (hmem (huvsub (right_mem_segment ℝ u v)).1) huv
  have huv_xy : affineSpan ℝ ({u, v} : Set Pt) = affineSpan ℝ ({x, y} : Set Pt) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne (hmem (huvsub (left_mem_segment ℝ u v)).2)
      (hmem (huvsub (right_mem_segment ℝ u v)).2) huv
  exact huv_ab.symm.trans huv_xy

private lemma boundary_align_mem_segment
    {a b x : Pt} :
    x ∈ segment ℝ a b ↔ ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ x = a + r • (b - a) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr.1, hr.2, rfl⟩
  · rintro ⟨r, hr0, hr1, rfl⟩
    exact ⟨r, ⟨hr0, hr1⟩, rfl⟩

private lemma boundary_align_smul_cancel
    {u : Pt} (hu : u ≠ 0) {r s : ℝ} (h : r • u = s • u) : r = s := by
  exact smul_left_injective ℝ hu h

private lemma boundary_align_segment_endpoints
    {a b c d : Pt} (hab : a ≠ b) (h : segment ℝ a b = segment ℝ c d) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  have hc : c ∈ segment ℝ a b := h ▸ left_mem_segment ℝ c d
  have hd : d ∈ segment ℝ a b := h ▸ right_mem_segment ℝ c d
  have ha : a ∈ segment ℝ c d := h ▸ left_mem_segment ℝ a b
  have hb : b ∈ segment ℝ c d := h ▸ right_mem_segment ℝ a b
  rw [boundary_align_mem_segment] at hc hd ha hb
  obtain ⟨r, hr0, hr1, rfl⟩ := hc
  obtain ⟨s, hs0, hs1, rfl⟩ := hd
  obtain ⟨u, hu0, hu1, hu⟩ := ha
  obtain ⟨v, hv0, hv1, hv⟩ := hb
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hk0 : a + r • (b - a) + u •
      (a + s • (b - a) - (a + r • (b - a))) =
      a + (r + u * (s - r)) • (b - a) := by module
  have hk1 : a + r • (b - a) + v •
      (a + s • (b - a) - (a + r • (b - a))) =
      a + (r + v * (s - r)) • (b - a) := by module
  have hzero : (0 : ℝ) • (b - a) = (r + u * (s - r)) • (b - a) := by
    rw [zero_smul]
    exact (add_eq_left.mp (hu.trans hk0).symm).symm
  have hone : (1 : ℝ) • (b - a) = (r + v * (s - r)) • (b - a) := by
    rw [one_smul]
    have h' : a + (b - a) = a + (r + v * (s - r)) • (b - a) := by
      calc
        a + (b - a) = b := by abel
        _ = a + r • (b - a) + v •
            (a + s • (b - a) - (a + r • (b - a))) := hv
        _ = a + (r + v * (s - r)) • (b - a) := hk1
    exact add_left_cancel h'
  have hz := boundary_align_smul_cancel hne hzero
  have ho := boundary_align_smul_cancel hne hone
  have hk : (r = 0 ∧ s = 1) ∨ (r = 1 ∧ s = 0) := by
    have h1 : r * (1 - u) = 0 := by
      nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hu1), mul_nonneg hu0 hs0]
    have h2 : u * s = 0 := by
      nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hu1), mul_nonneg hu0 hs0]
    rcases mul_eq_zero.mp h1 with h1 | h1
    · subst h1
      have : v * s = 1 := by linarith
      left
      refine ⟨rfl, ?_⟩
      nlinarith
    · have huone : u = 1 := by linarith
      subst huone
      have hs : s = 0 := by linarith
      subst hs
      right
      refine ⟨?_, rfl⟩
      nlinarith
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    constructor <;> simp
  · right
    constructor <;> simp

private lemma boundary_align_canonDir_neg (v : Pt) : canonDir (-v) = canonDir v := by
  rcases lt_trichotomy (v 0) 0 with hv0 | hv0 | hv0
  · have hn : 0 < (-v) 0 ∨ ((-v) 0 = 0 ∧ 0 < (-v) 1) := by
      left
      simpa using neg_pos.mpr hv0
    have hp : ¬(0 < v 0 ∨ (v 0 = 0 ∧ 0 < v 1)) := by
      rintro (h | ⟨h, _⟩) <;> linarith
    unfold canonDir
    rw [if_pos hn, if_neg hp, norm_neg]
    module
  · rcases lt_trichotomy (v 1) 0 with hv1 | hv1 | hv1
    · have hn : 0 < (-v) 0 ∨ ((-v) 0 = 0 ∧ 0 < (-v) 1) := by
        right
        exact ⟨by simpa using congrArg Neg.neg hv0, by simpa using neg_pos.mpr hv1⟩
      have hp : ¬(0 < v 0 ∨ (v 0 = 0 ∧ 0 < v 1)) := by
        rintro (h | ⟨_, h⟩) <;> linarith
      unfold canonDir
      rw [if_pos hn, if_neg hp, norm_neg]
      module
    · have hz : v = 0 := by
        ext i
        fin_cases i
        · simpa using hv0
        · simpa using hv1
      subst v
      simp [canonDir]
    · have hp : 0 < v 0 ∨ (v 0 = 0 ∧ 0 < v 1) := by
        exact Or.inr ⟨hv0, hv1⟩
      have hn : ¬(0 < (-v) 0 ∨ ((-v) 0 = 0 ∧ 0 < (-v) 1)) := by
        rintro (h | ⟨_, h⟩)
        · change 0 < -(v 0) at h
          linarith
        · change 0 < -(v 1) at h
          linarith
      unfold canonDir
      rw [if_neg hn, if_pos hp, norm_neg]
      module
  · have hp : 0 < v 0 ∨ (v 0 = 0 ∧ 0 < v 1) := Or.inl hv0
    have hn : ¬(0 < (-v) 0 ∨ ((-v) 0 = 0 ∧ 0 < (-v) 1)) := by
      rintro (h | ⟨h, _⟩)
      · change 0 < -(v 0) at h
        linarith
      · change -(v 0) = 0 at h
        linarith
    unfold canonDir
    rw [if_neg hn, if_pos hp, norm_neg]
    module

private lemma boundary_align_frameOrigin_swap (x y : Pt) :
    frameOrigin y x = frameOrigin x y := by
  rcases lt_trichotomy (x 0) (y 0) with h0 | h0 | h0
  · have hp : 0 < (y - x) 0 ∨ ((y - x) 0 = 0 ∧ 0 < (y - x) 1) := by
      left
      change 0 < y 0 - x 0
      linarith
    have hn : ¬(0 < (x - y) 0 ∨ ((x - y) 0 = 0 ∧ 0 < (x - y) 1)) := by
      push_neg
      constructor
      · change x 0 - y 0 ≤ 0
        linarith
      · intro h
        change x 0 - y 0 = 0 at h
        linarith
    unfold frameOrigin
    rw [if_neg hn, if_pos hp]
  · rcases lt_trichotomy (x 1) (y 1) with h1 | h1 | h1
    · have hp : 0 < (y - x) 0 ∨ ((y - x) 0 = 0 ∧ 0 < (y - x) 1) := by
        right
        constructor
        · change y 0 - x 0 = 0
          linarith
        · change 0 < y 1 - x 1
          linarith
      have hn : ¬(0 < (x - y) 0 ∨ ((x - y) 0 = 0 ∧ 0 < (x - y) 1)) := by
        push_neg
        constructor
        · change x 0 - y 0 ≤ 0
          linarith
        · intro _
          change x 1 - y 1 ≤ 0
          linarith
      unfold frameOrigin
      rw [if_neg hn, if_pos hp]
    · have hxy : x = y := by
        ext i
        fin_cases i
        · exact h0
        · exact h1
      subst y
      rfl
    · have hn : 0 < (x - y) 0 ∨ ((x - y) 0 = 0 ∧ 0 < (x - y) 1) := by
        right
        constructor
        · change x 0 - y 0 = 0
          linarith
        · change 0 < x 1 - y 1
          linarith
      have hp : ¬(0 < (y - x) 0 ∨ ((y - x) 0 = 0 ∧ 0 < (y - x) 1)) := by
        push_neg
        constructor
        · change y 0 - x 0 ≤ 0
          linarith
        · intro _
          change y 1 - x 1 ≤ 0
          linarith
      unfold frameOrigin
      rw [if_pos hn, if_neg hp]
  · have hn : 0 < (x - y) 0 ∨ ((x - y) 0 = 0 ∧ 0 < (x - y) 1) := by
      left
      change 0 < x 0 - y 0
      linarith
    have hp : ¬(0 < (y - x) 0 ∨ ((y - x) 0 = 0 ∧ 0 < (y - x) 1)) := by
      push_neg
      constructor
      · change y 0 - x 0 ≤ 0
        linarith
      · intro h
        change y 0 - x 0 = 0 at h
        linarith
    unfold frameOrigin
    rw [if_pos hn, if_neg hp]

private lemma boundary_align_overlap_ne
    {a b c d : Pt} (h : OverlapPos (segment ℝ a b) (segment ℝ c d)) :
    a ≠ b ∧ c ≠ d := by
  obtain ⟨x, y, hxy, hsub⟩ := h
  constructor
  · intro hab
    subst b
    have hx : x = a := by
      have hx' := (hsub (left_mem_segment ℝ x y)).1
      simpa only [segment_same, mem_singleton_iff] using hx'
    have hy : y = a := by
      have hy' := (hsub (right_mem_segment ℝ x y)).1
      simpa only [segment_same, mem_singleton_iff] using hy'
    exact hxy (hx.trans hy.symm)
  · intro hcd
    subst d
    have hx : x = c := by
      have hx' := (hsub (left_mem_segment ℝ x y)).2
      simpa only [segment_same, mem_singleton_iff] using hx'
    have hy : y = c := by
      have hy' := (hsub (right_mem_segment ℝ x y)).2
      simpa only [segment_same, mem_singleton_iff] using hy'
    exact hxy (hx.trans hy.symm)

private lemma boundary_align_frameOrigin_add (v x y : Pt) :
    frameOrigin (v + x) (v + y) = v + frameOrigin x y := by
  have hd : v + y - (v + x) = y - x := by abel
  simp only [frameOrigin, hd]
  split_ifs <;> rfl

private lemma boundary_align_segment_eq_coord_bounds
    (z w o u : Pt) (r s : ℝ)
    (hz : o + r • u = z) (hw : o + s • u = w) :
    segment ℝ z w = segment ℝ (o + min r s • u) (o + max r s • u) := by
  rcases le_total r s with hrs | hsr
  · rw [min_eq_left hrs, max_eq_right hrs, hz, hw]
  · rw [min_eq_right hsr, max_eq_left hsr, hz, hw, segment_symm]

/-- Step 2 of the blueprint proof of `schedule_intermediate_sts_step1_boundary_align_step2_endpoints`:
The same two coordinates $p,q$ for its coarse containing side means $c,d$ have exactly the same endpoints. -/
private lemma schedule_intermediate_sts_step1_boundary_align_step2_endpoints_step2_eq
    (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (A A' : PlacedTile G.P')
    (t : LayerTag m) (c d : Pt × Pt)
    (hc : c ∈ layerSides τ G m A.form t) (hd : d ∈ layerSides τ G m A'.form t)
    (e e' : Pt × Pt)
    (he : e ∈ fineOuterSides τ G m A.form) (he' : e' ∈ fineOuterSides τ G m A'.form)
    (heq : placedSeg ((τ.θ ^ m) • A.anchor) e = placedSeg ((τ.θ ^ m) • A'.anchor) e')
    (hov_c : OverlapPos (segment ℝ c.1 c.2) (segment ℝ e.1 e.2))
    (hov_d : OverlapPos (segment ℝ d.1 d.2) (segment ℝ e'.1 e'.2))
    (h_sch : EndpointSchedule τ G m A.form e t = EndpointSchedule τ G m A'.form e' t)
    (hoverlap : OverlapPos (placedSeg ((τ.θ ^ m) • A.anchor) c)
      (placedSeg ((τ.θ ^ m) • A'.anchor) d))
    (hatom : atom e c = atom e' d) :
    placedSeg ((τ.θ ^ m) • A.anchor) c = placedSeg ((τ.θ ^ m) • A'.anchor) d := by
  have _ := hc
  have _ := hd
  have _ := he
  have _ := he'
  have _ := h_sch
  have _ := hoverlap
  let va : Pt := (τ.θ ^ m) • A.anchor
  let vb : Pt := (τ.θ ^ m) • A'.anchor
  have he_ne : e.1 ≠ e.2 := (boundary_align_overlap_ne hov_c).2
  have he'_ne : e'.1 ≠ e'.2 := (boundary_align_overlap_ne hov_d).2
  have hE_ne : va + e.1 ≠ va + e.2 := by
    intro h
    exact he_ne (add_left_cancel h)
  have hends :
      (vb + e'.1 = va + e.1 ∧ vb + e'.2 = va + e.2) ∨
        (vb + e'.1 = va + e.2 ∧ vb + e'.2 = va + e.1) := by
    apply boundary_align_segment_endpoints hE_ne
    simpa only [placedSeg, va, vb] using heq
  have hO : va + frameOrigin e.1 e.2 = vb + frameOrigin e'.1 e'.2 := by
    rw [← boundary_align_frameOrigin_add, ← boundary_align_frameOrigin_add]
    rcases hends with hends | hends
    · rw [hends.1, hends.2]
    · rw [hends.1, hends.2, boundary_align_frameOrigin_swap]
  have hD : canonDir (e.2 - e.1) = canonDir (e'.2 - e'.1) := by
    rcases hends with hends | hends
    · have hv : e'.2 - e'.1 = e.2 - e.1 := by
        have hg := congrArg₂ (fun x y : Pt => x - y) hends.2 hends.1
        calc
          e'.2 - e'.1 = (vb + e'.2) - (vb + e'.1) := by abel
          _ = (va + e.2) - (va + e.1) := hg
          _ = e.2 - e.1 := by abel
      rw [hv]
    · have hv : e'.2 - e'.1 = -(e.2 - e.1) := by
        have hg := congrArg₂ (fun x y : Pt => x - y) hends.2 hends.1
        calc
          e'.2 - e'.1 = (vb + e'.2) - (vb + e'.1) := by abel
          _ = (va + e.1) - (va + e.2) := hg
          _ = -(e.2 - e.1) := by abel
      rw [hv]
      exact (boundary_align_canonDir_neg (e.2 - e.1)).symm
  have hp :
      min (segCoord e.1 e.2 c.1) (segCoord e.1 e.2 c.2) =
        min (segCoord e'.1 e'.2 d.1) (segCoord e'.1 e'.2 d.2) := by
    have h := congrArg (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.1) hatom
    simpa only [atom] using h
  have hq :
      max (segCoord e.1 e.2 c.1) (segCoord e.1 e.2 c.2) =
        max (segCoord e'.1 e'.2 d.1) (segCoord e'.1 e'.2 d.2) := by
    have h := congrArg (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.2) hatom
    simpa only [atom] using h
  have hspan_c := boundary_align_overlap_span hov_c
  have hspan_d := boundary_align_overlap_span hov_d
  have hc1_line : c.1 ∈ affineSpan ℝ ({e.1, e.2} : Set Pt) := by
    rw [← hspan_c]
    exact subset_affineSpan ℝ ({c.1, c.2} : Set Pt) (by simp)
  have hc2_line : c.2 ∈ affineSpan ℝ ({e.1, e.2} : Set Pt) := by
    rw [← hspan_c]
    exact subset_affineSpan ℝ ({c.1, c.2} : Set Pt) (by simp)
  have hd1_line : d.1 ∈ affineSpan ℝ ({e'.1, e'.2} : Set Pt) := by
    rw [← hspan_d]
    exact subset_affineSpan ℝ ({d.1, d.2} : Set Pt) (by simp)
  have hd2_line : d.2 ∈ affineSpan ℝ ({e'.1, e'.2} : Set Pt) := by
    rw [← hspan_d]
    exact subset_affineSpan ℝ ({d.1, d.2} : Set Pt) (by simp)
  have hc1 := boundary_align_frame_reconstruct e.1 e.2 c.1 he_ne hc1_line
  have hc2 := boundary_align_frame_reconstruct e.1 e.2 c.2 he_ne hc2_line
  have hd1 := boundary_align_frame_reconstruct e'.1 e'.2 d.1 he'_ne hd1_line
  have hd2 := boundary_align_frame_reconstruct e'.1 e'.2 d.2 he'_ne hd2_line
  have hc1g :
      va + frameOrigin e.1 e.2 + segCoord e.1 e.2 c.1 • canonDir (e.2 - e.1) = va + c.1 := by
    calc
      _ = va + (frameOrigin e.1 e.2 +
          segCoord e.1 e.2 c.1 • canonDir (e.2 - e.1)) := by abel
      _ = va + c.1 := congrArg (va + ·) hc1
  have hc2g :
      va + frameOrigin e.1 e.2 + segCoord e.1 e.2 c.2 • canonDir (e.2 - e.1) = va + c.2 := by
    calc
      _ = va + (frameOrigin e.1 e.2 +
          segCoord e.1 e.2 c.2 • canonDir (e.2 - e.1)) := by abel
      _ = va + c.2 := congrArg (va + ·) hc2
  have hd1g :
      vb + frameOrigin e'.1 e'.2 + segCoord e'.1 e'.2 d.1 • canonDir (e'.2 - e'.1) = vb + d.1 := by
    calc
      _ = vb + (frameOrigin e'.1 e'.2 +
          segCoord e'.1 e'.2 d.1 • canonDir (e'.2 - e'.1)) := by abel
      _ = vb + d.1 := congrArg (vb + ·) hd1
  have hd2g :
      vb + frameOrigin e'.1 e'.2 + segCoord e'.1 e'.2 d.2 • canonDir (e'.2 - e'.1) = vb + d.2 := by
    calc
      _ = vb + (frameOrigin e'.1 e'.2 +
          segCoord e'.1 e'.2 d.2 • canonDir (e'.2 - e'.1)) := by abel
      _ = vb + d.2 := congrArg (vb + ·) hd2
  change segment ℝ (va + c.1) (va + c.2) = segment ℝ (vb + d.1) (vb + d.2)
  calc
    segment ℝ (va + c.1) (va + c.2) =
        segment ℝ
          (va + frameOrigin e.1 e.2 +
            min (segCoord e.1 e.2 c.1) (segCoord e.1 e.2 c.2) • canonDir (e.2 - e.1))
          (va + frameOrigin e.1 e.2 +
            max (segCoord e.1 e.2 c.1) (segCoord e.1 e.2 c.2) • canonDir (e.2 - e.1)) :=
      boundary_align_segment_eq_coord_bounds _ _ _ _ _ _ hc1g hc2g
    _ = segment ℝ
          (vb + frameOrigin e'.1 e'.2 +
            min (segCoord e'.1 e'.2 d.1) (segCoord e'.1 e'.2 d.2) • canonDir (e'.2 - e'.1))
          (vb + frameOrigin e'.1 e'.2 +
            max (segCoord e'.1 e'.2 d.1) (segCoord e'.1 e'.2 d.2) • canonDir (e'.2 - e'.1)) := by
      rw [hO, hD, hp, hq]
    _ = segment ℝ (vb + d.1) (vb + d.2) :=
      (boundary_align_segment_eq_coord_bounds _ _ _ _ _ _ hd1g hd2g).symm

/-- Step 2 of the blueprint proof of `schedule_intermediate_sts_step1_boundary_align`:
Equal schedules on coinciding fine outer sides, together with the fact that `c` and `d`
positively overlap, force their corresponding schedule atoms to have the same `p, q` coordinates,
which means `c` and `d` have exactly the same endpoints in space. -/
private lemma schedule_intermediate_sts_step1_boundary_align_step2_endpoints
    (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (A A' : PlacedTile G.P')
    (t : LayerTag m) (c d : Pt × Pt)
    (hc : c ∈ layerSides τ G m A.form t) (hd : d ∈ layerSides τ G m A'.form t)
    (e e' : Pt × Pt)
    (he : e ∈ fineOuterSides τ G m A.form) (he' : e' ∈ fineOuterSides τ G m A'.form)
    (heq : placedSeg ((τ.θ ^ m) • A.anchor) e = placedSeg ((τ.θ ^ m) • A'.anchor) e')
    (hov_c : OverlapPos (segment ℝ c.1 c.2) (segment ℝ e.1 e.2))
    (hov_d : OverlapPos (segment ℝ d.1 d.2) (segment ℝ e'.1 e'.2))
    (h_sch : EndpointSchedule τ G m A.form e t = EndpointSchedule τ G m A'.form e' t)
    (hoverlap : OverlapPos (placedSeg ((τ.θ ^ m) • A.anchor) c)
      (placedSeg ((τ.θ ^ m) • A'.anchor) d)) :
    placedSeg ((τ.θ ^ m) • A.anchor) c = placedSeg ((τ.θ ^ m) • A'.anchor) d := by
  have hatom := schedule_intermediate_sts_step1_boundary_align_step2_endpoints_step1_atom τ G m A A' t c d hc hd e e' he he' heq hov_c hov_d h_sch hoverlap
  exact schedule_intermediate_sts_step1_boundary_align_step2_endpoints_step2_eq τ G m A A' t c d hc hd e e' he he' heq hov_c hov_d h_sch hoverlap hatom

/-- Step 1 of the blueprint proof of `schedule_intermediate_sts`:
Equal schedules on shared whole outer fine sides force positively overlapping coarse listed sides
on opposite macroblock boundaries, in the same layer tag, to have exactly the same endpoints. -/
private theorem schedule_intermediate_sts_step1_boundary_align
    (hτ : τ.STS) (m : ℕ) (T' : PlaneTiling G.P')
    (hfine : SideToSideSet (τ.decomposeIter m (G.scatter T'.tiles)))
    (halign : SchedulesAligned τ G m T')
    (A A' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles)
    (t : LayerTag m) (c d : Pt × Pt)
    (hc : c ∈ layerSides τ G m A.form t) (hd : d ∈ layerSides τ G m A'.form t)
    (hoverlap : OverlapPos (placedSeg ((τ.θ ^ m) • A.anchor) c)
      (placedSeg ((τ.θ ^ m) • A'.anchor) d)) :
    placedSeg ((τ.θ ^ m) • A.anchor) c = placedSeg ((τ.θ ^ m) • A'.anchor) d := by
  have _ := hτ
  obtain ⟨e, he, e', he', heq, hov_c, hov_d⟩ :=
    schedule_intermediate_sts_step1_boundary_align_step1_fine_sides τ G m T' hfine A A' hA hA' t c d
      hc hd hoverlap
  have h_sch : EndpointSchedule τ G m A.form e t = EndpointSchedule τ G m A'.form e' t := by
    have h_sch_eq := halign A hA A' hA' e he e' he' heq
    exact congr_fun h_sch_eq t
  exact schedule_intermediate_sts_step1_boundary_align_step2_endpoints τ G m A A' t c d hc hd e e'
    he he' heq hov_c hov_d h_sch hoverlap

private lemma schedule_intermediate_sts_step2_smul_segment (s : ℝ) (x y : Pt) :
    s • segment ℝ x y = segment ℝ (s • x) (s • y) := by
  let f : Pt →ᵃ[ℝ] Pt := (LinearMap.lsmul ℝ Pt s).toAffineMap
  change f '' segment ℝ x y = segment ℝ (f x) (f y)
  exact image_segment ℝ f x y

private lemma schedule_intermediate_sts_step2_overlap_smul {s : ℝ} (hs : s ≠ 0)
    {u v : Set Pt} (h : OverlapPos u v) : OverlapPos (s • u) (s • v) := by
  obtain ⟨x, y, hxy, hsegment⟩ := h
  refine ⟨s • x, s • y, ?_, ?_⟩
  · exact fun hxy' => hxy (smul_right_injective Pt hs hxy')
  · rw [← schedule_intermediate_sts_step2_smul_segment, ← Set.smul_set_inter₀ hs]
    exact Set.smul_set_mono hsegment

private lemma schedule_intermediate_sts_step2_placedSeg
    (m : ℕ) (A : PlacedTile G.P') (i : Fin (G.P'.disk A.form).n) :
    placedSeg ((τ.θ ^ m) • A.anchor) (parentSide τ G m A.form i) = (τ.θ ^ m) • A.side i := by
  simp [placedSeg, parentSide, PlacedTile.side, PolygonalDisk.side, vadd_segment,
    schedule_intermediate_sts_step2_smul_segment, smul_add]

/-- Step 2 of the blueprint proof of `schedule_intermediate_sts`:
Inside a block each original layer is already an STS supertile patch.
Thus, to check STS for the parent level, we only need to compare sides that
arise from opposite macroblock boundaries, which correspond to `top` layer sides. -/
private theorem schedule_intermediate_sts_step2_parents_sts
    (m : ℕ) (T' : PlaneTiling G.P')
    (h_align : ∀ (A A' : PlacedTile G.P') (_hA : A ∈ T'.tiles) (_hA' : A' ∈ T'.tiles)
       (c d : Pt × Pt)
       (_hc : c ∈ layerSides τ G m A.form .top) (_hd : d ∈ layerSides τ G m A'.form .top),
       OverlapPos (placedSeg ((τ.θ ^ m) • A.anchor) c)
         (placedSeg ((τ.θ ^ m) • A'.anchor) d) →
       placedSeg ((τ.θ ^ m) • A.anchor) c = placedSeg ((τ.θ ^ m) • A'.anchor) d) :
    SideToSideSet T'.tiles := by
  intro A hA A' hA' i j hoverlap
  let c := parentSide τ G m A.form i
  let d := parentSide τ G m A'.form j
  have hc : c ∈ layerSides τ G m A.form .top := ⟨i, rfl⟩
  have hd : d ∈ layerSides τ G m A'.form .top := ⟨j, rfl⟩
  have hs : τ.θ ^ m ≠ 0 := pow_ne_zero m (ne_of_gt (lt_trans zero_lt_one τ.one_lt))
  have heqA := schedule_intermediate_sts_step2_placedSeg τ G m A i
  have heqA' := schedule_intermediate_sts_step2_placedSeg τ G m A' j
  have hoverlap' :
      OverlapPos (placedSeg ((τ.θ ^ m) • A.anchor) c)
        (placedSeg ((τ.θ ^ m) • A'.anchor) d) := by
    rw [heqA, heqA']
    exact schedule_intermediate_sts_step2_overlap_smul hs hoverlap
  have heq := h_align A A' hA hA' c d hc hd hoverlap'
  rw [heqA, heqA'] at heq
  exact (Set.image_injective.mpr (smul_right_injective Pt hs)) heq

/-- Step 1 of the blueprint proof of `schedule_intermediate_sts_step3_levels_sts`:
Decomposition of a scattered tiling is the union of the decompositions of its
individual scattered parents, so every intermediate tile has a parent witness. -/
private lemma schedule_intermediate_sts_step3_levels_sts_step1_scatter_membership
    (m : ℕ) (T' : PlaneTiling G.P') (X : PlacedTile P)
    (hX : X ∈ τ.decomposeIter m (G.scatter T'.tiles)) :
    ∃ A ∈ T'.tiles, X ∈ τ.decomposeIter m (G.scatterTile A) := by
  induction m generalizing X with
  | zero =>
    change X ∈ ⋃ A ∈ T'.tiles, G.scatterTile A at hX
    rcases Set.mem_iUnion.1 hX with ⟨A, hX⟩
    rcases Set.mem_iUnion.1 hX with ⟨hA, hXA⟩
    exact ⟨A, hA, hXA⟩
  | succ m ih =>
    change X ∈ τ.decompose (τ.decomposeIter m (G.scatter T'.tiles)) at hX
    simp only [Substitution.decompose, Set.mem_iUnion] at hX
    rcases hX with ⟨Y, hY, hXY⟩
    obtain ⟨A, hA, hYA⟩ := ih Y hY
    refine ⟨A, hA, ?_⟩
    change X ∈ τ.decompose (τ.decomposeIter m (G.scatterTile A))
    simp only [Substitution.decompose, Set.mem_iUnion]
    exact ⟨Y, hYA, hXY⟩

/-- Step 2 of the blueprint proof of `schedule_intermediate_sts_step3_levels_sts`:
Within one grouped parent, the translated and iterated dissected patch is
side-to-side by the corresponding instance of `hΔ`. -/
private theorem schedule_intermediate_sts_step3_levels_sts_step2_within_group
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (G.dissect α).tiles))
    (j : ℕ) (A : PlacedTile G.P') :
    SideToSideSet (τ.decomposeIter j (G.scatterTile A)) := by
  have htranslate : ∀ (n : ℕ) (v : Pt) (S : Set (PlacedTile P)),
      τ.decomposeIter n (translateSet v S) =
        translateSet (τ.θ ^ n • v) (τ.decomposeIter n S) := by
    have hdecompose : ∀ (v : Pt) (S : Set (PlacedTile P)),
        τ.decompose (translateSet v S) =
          translateSet (τ.θ • v) (τ.decompose S) := by
      intro v S
      ext X
      simp only [Substitution.decompose, Substitution.decomposeTile, translateSet,
        Set.mem_iUnion, Set.mem_image, PlacedTile.translate, exists_prop]
      constructor
      · rintro ⟨_, ⟨A, hA, rfl⟩, Y, hY, rfl⟩
        refine ⟨⟨Y.form, τ.θ • A.anchor +ᵥ Y.anchor⟩,
          ⟨A, hA, Y, hY, rfl⟩, ?_⟩
        simp only [vadd_eq_add, smul_add, add_assoc]
      · rintro ⟨_, ⟨A, hA, Y, hY, rfl⟩, rfl⟩
        refine ⟨⟨A.form, v +ᵥ A.anchor⟩, ⟨A, hA, rfl⟩, Y, hY, ?_⟩
        simp only [vadd_eq_add, smul_add, add_assoc]
    intro n
    induction n with
    | zero =>
      intro v S
      simp [Substitution.decomposeIter]
    | succ n ih =>
      intro v S
      change τ.decompose (τ.decomposeIter n (translateSet v S)) =
        translateSet (τ.θ ^ (n + 1) • v) (τ.decompose (τ.decomposeIter n S))
      rw [ih, hdecompose, smul_smul, pow_succ']
  change SideToSideSet
    (τ.decomposeIter j (translateSet A.anchor (G.dissect A.form).tiles))
  rw [htranslate j A.anchor (G.dissect A.form).tiles]
  have hsts := hΔ A.form j
  intro X hX Y hY i i' hXY
  rcases hX with ⟨X₀, hX₀, rfl⟩
  rcases hY with ⟨Y₀, hY₀, rfl⟩
  have hsideX : (X₀.translate ((τ.θ ^ j) • A.anchor)).side i =
      (τ.θ ^ j) • A.anchor +ᵥ X₀.side i := by
    simp [PlacedTile.translate, PlacedTile.side, vadd_vadd]
  have hsideY : (Y₀.translate ((τ.θ ^ j) • A.anchor)).side i' =
      (τ.θ ^ j) • A.anchor +ᵥ Y₀.side i' := by
    simp [PlacedTile.translate, PlacedTile.side, vadd_vadd]
  have hXY₀ : OverlapPos (X₀.side i) (Y₀.side i') := by
    obtain ⟨x, y, hxy, hseg⟩ := hXY
    refine ⟨-((τ.θ ^ j) • A.anchor) +ᵥ x,
      -((τ.θ ^ j) • A.anchor) +ᵥ y, by simpa using hxy, ?_⟩
    rw [hsideX, hsideY] at hseg
    rw [← vadd_segment]
    rintro z ⟨w, hw, rfl⟩
    exact ⟨by simpa [Set.mem_vadd_set_iff_neg_vadd_mem, add_assoc] using (hseg hw).1,
      by simpa [Set.mem_vadd_set_iff_neg_vadd_mem, add_assoc] using (hseg hw).2⟩
  have hEq := hsts X₀ hX₀ Y₀ hY₀ i i' hXY₀
  rw [hsideX, hsideY]
  exact congrArg (fun s : Set Pt => (τ.θ ^ j) • A.anchor +ᵥ s) hEq

/-- Two tiles of a family with disjoint interiors inside `R` cannot share a nondegenerate
segment of their sides lying on the frontier of `R`, unless they are the same tile. -/
private lemma cgb_frontier_tiles_eq (S : Set (PlacedTile P)) (hS : DisjointInteriors S) (R : Set Pt)
    (hR : ∀ B ∈ S, B.carrier ⊆ R) {B1 B2 : PlacedTile P} (h1 : B1 ∈ S) (h2 : B2 ∈ S)
    (i1 : Fin (P.disk B1.form).n) (i2 : Fin (P.disk B2.form).n) {x y : Pt} (hxy : x ≠ y)
    (hsub : segment ℝ x y ⊆ B1.side i1 ∩ B2.side i2) (hfr : segment ℝ x y ⊆ frontier R) :
    B1 = B2 := by
  by_contra hne
  obtain ⟨z, hzxy, hzF⟩ := ((fs1_segment_infinite hxy).diff (Set.toFinite ({B1.vertex i1,
    B1.vertex (finRotate _ i1), B2.vertex i2, B2.vertex (finRotate _ i2)} : Set Pt))).nonempty
  have hz1 : z ∈ B1.side i1 := (hsub hzxy).1
  have hz2 : z ∈ B2.side i2 := (hsub hzxy).2
  set g := sa1_cross (y - x) with hg
  set k := g x with hk
  have hl : ∀ (B : PlacedTile P) (i : Fin (P.disk B.form).n), segment ℝ x y ⊆ B.side i →
      ∀ p ∈ B.side i, g p = k := by
    intro B i hxyB p hp
    rw [fs1_tile_side_eq] at hxyB hp
    exact sa1_cross_on_segment (hxyB (left_mem_segment ℝ x y)) (hxyB (right_mem_segment ℝ x y)) hp
  have hl1 := hl B1 i1 fun w hw => (hsub hw).1
  have hl2 := hl B2 i2 fun w hw => (hsub hw).2
  have hK : ∀ (B : PlacedTile P) (i : Fin (P.disk B.form).n), z ∈ B.side i → z ≠ B.vertex i →
      z ≠ B.vertex (finRotate _ i) →
      ∃ r > 0, ∀ p ∈ Metric.ball z r, p ∈ frontier B.carrier → p ∈ B.side i := by
    intro B i hzi hza hzb
    let K := ⋃ j ∈ ({i}ᶜ : Set (Fin (P.disk B.form).n)), B.side j
    have hKc : IsClosed K := (Set.toFinite _).isClosed_biUnion fun j _ => by
      rw [fs1_tile_side_eq]; exact sa1_segment_isClosed _ _
    have hzK : z ∉ K := by
      simp only [K, Set.mem_iUnion]
      rintro ⟨j, hj, hzj⟩
      rcases sa1_placed_simple B (Set.mem_compl_singleton_iff.mp hj).symm hzi hzj with h | h
      exacts [hza h, hzb h]
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hKc.isOpen_compl z hzK
    refine ⟨r, hr, fun p hp hpf => ?_⟩
    rw [fs1_frontier_carrier, Set.mem_iUnion] at hpf
    obtain ⟨j, hj⟩ := hpf
    by_cases hji : j = i
    · subst hji; exact hj
    · exact absurd (Set.mem_biUnion (x := j) (Set.mem_compl_singleton_iff.mpr hji) hj) (hball hp)
  obtain ⟨r1, hr1, hb1⟩ := hK B1 i1 hz1 (fun h => hzF (by simp [h])) (fun h => hzF (by simp [h]))
  obtain ⟨r2, hr2, hb2⟩ := hK B2 i2 hz2 (fun h => hzF (by simp [h])) (fun h => hzF (by simp [h]))
  set U := Metric.ball z (min r1 r2) with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := Metric.mem_ball_self (lt_min hr1 hr2)
  have hw : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  set n : Pt := !₂[-((y - x) 1), (y - x) 0] with hndef
  have hn : 0 < g n := by
    rw [hg, sa1_cross_apply]
    have h0 : n 0 = -((y - x) 1) := by simp [hndef]
    have h1' : n 1 = (y - x) 0 := by simp [hndef]
    rw [h0, h1']
    have : (y - x) 0 ≠ 0 ∨ (y - x) 1 ≠ 0 := by
      by_contra h
      push_neg at h
      apply hw
      ext i
      fin_cases i
      · simpa using h.1
      · simpa using h.2
    rcases this with h | h
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg ((y - x) 1)]
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg ((y - x) 0)]
  have hgz : g z = k := hl1 z hz1
  have half1 := sa1_half (fs1_carrier_closed B1) hU (convex_ball _ _) g k hn hzU
    (by rw [fs1_closure_interior_carrier]; exact fs1_side_subset_carrier B1 i1 hz1)
    (fun p hp hpf => hl1 p (hb1 p (Metric.ball_subset_ball (min_le_left _ _) hp) hpf))
  have half2 := sa1_half (fs1_carrier_closed B2) hU (convex_ball _ _) g k hn hzU
    (by rw [fs1_closure_interior_carrier]; exact fs1_side_subset_carrier B2 i2 hz2)
    (fun p hp hpf => hl2 p (hb2 p (Metric.ball_subset_ball (min_le_right _ _) hp) hpf))
  have hdisj : Disjoint (interior B1.carrier) (interior B2.carrier) := hS h1 h2 hne
  obtain ⟨δ, hδU, hδ⟩ := (sa1_eventually hU hzU n).exists
  obtain ⟨δ', hδU', hδ'⟩ := (sa1_eventually hU hzU (-n)).exists
  have hP : z + δ • n ∈ U ∩ {p | k < g p} := by
    refine ⟨hδU, ?_⟩
    show k < g (z + δ • n)
    rw [map_add, map_smul, hgz, smul_eq_mul]
    nlinarith
  have hM : z + δ' • (-n) ∈ U ∩ {p | g p < k} := by
    refine ⟨hδU', ?_⟩
    show g (z + δ' • (-n)) < k
    rw [map_add, map_smul, map_neg, hgz, smul_eq_mul]
    nlinarith
  have hcl : ∀ p ∈ U, g p = k → p ∈ closure (U ∩ {p | k < g p}) := by
    intro p hp hgp
    refine mem_closure_of_tendsto (sa1_tendsto p n) ?_
    filter_upwards [sa1_eventually hU hp n] with δ hδ
    refine ⟨hδ.1, ?_⟩
    show k < g (p + δ • n)
    rw [map_add, map_smul, hgp, smul_eq_mul]
    nlinarith [hδ.2]
  have hopp : ∀ (C1 C2 : Set Pt), IsClosed C1 → C1 ⊆ R → C2 ⊆ R →
      U ∩ {p | k < g p} ⊆ interior C1 → U ∩ {p | g p < k} ⊆ interior C2 → False := by
    intro C1 C2 hC1 hC1R hC2R hP1 hM2
    have hUR : U ⊆ R := by
      intro p hp
      rcases lt_trichotomy (g p) k with hlt | heq | hgt
      · exact hC2R (interior_subset (hM2 ⟨hp, hlt⟩))
      · exact hC1R (hC1.closure_subset_iff.mpr (hP1.trans interior_subset) (hcl p hp heq))
      · exact hC1R (interior_subset (hP1 ⟨hp, hgt⟩))
    exact (hfr hzxy).2 (interior_maximal hUR hU hzU)
  rcases half1 with h1P | h1M <;> rcases half2 with h2P | h2M
  · exact Set.disjoint_left.mp hdisj (h1P hP) (h2P hP)
  · exact hopp _ _ (fs1_carrier_closed B1) (hR B1 h1) (hR B2 h2) h1P h2M
  · exact hopp _ _ (fs1_carrier_closed B2) (hR B2 h2) (hR B1 h1) h2P h1M
  · exact Set.disjoint_left.mp hdisj (h1M hM) (h2M hM)

/-- Every tile of an iterated decomposition of a translated set is a translate of a tile of
the iterated decomposition of the original set. -/
private lemma cgb_decomposeIter_translate_inv (n : ℕ) (v : Pt) (S : Set (PlacedTile P))
    (X : PlacedTile P) (hX : X ∈ τ.decomposeIter n (translateSet v S)) :
    ∃ B ∈ τ.decomposeIter n S, X = B.translate ((τ.θ ^ n) • v) := by
  induction n generalizing X with
  | zero =>
    obtain ⟨B, hB, rfl⟩ := hX
    exact ⟨B, hB, by simp⟩
  | succ n ih =>
    change X ∈ τ.decompose (τ.decomposeIter n (translateSet v S)) at hX
    simp only [Substitution.decompose, Set.mem_iUnion] at hX
    obtain ⟨C, hC, hXC⟩ := hX
    obtain ⟨D, hD, rfl⟩ := ih C hC
    simp only [Substitution.decomposeTile, translateSet, Set.mem_image] at hXC
    obtain ⟨R, hR, rfl⟩ := hXC
    refine ⟨R.translate (τ.θ • D.anchor), ?_, ?_⟩
    · change _ ∈ τ.decompose (τ.decomposeIter n S)
      simp only [Substitution.decompose, Set.mem_iUnion]
      exact ⟨D, hD, R, hR, rfl⟩
    · simp only [PlacedTile.translate, PlacedTile.mk.injEq, true_and, vadd_eq_add, smul_add,
        pow_succ', mul_smul]
      abel

/-- Pulling back a segment through a translation. -/
private lemma cgb_untranslate (a : Pt) {x y : Pt} {U V : Set Pt}
    (h : segment ℝ x y ⊆ (a +ᵥ U) ∩ (a +ᵥ V)) :
    segment ℝ (-a +ᵥ x) (-a +ᵥ y) ⊆ U ∩ V := by
  intro z hz
  have hz' : a +ᵥ z ∈ segment ℝ x y := by
    have := Set.vadd_mem_vadd_set (a := a) hz
    rwa [vadd_segment, vadd_neg_vadd, vadd_neg_vadd] at this
  exact ⟨Set.vadd_mem_vadd_set_iff.1 (h hz').1, Set.vadd_mem_vadd_set_iff.1 (h hz').2⟩

/-- A side of an original-layer tile containing a nondegenerate frontier segment of the
block lies entirely on the frontier of the block (uses that the layer is STS). -/
private lemma cgb_core (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (G.dissect α).tiles))
    (j : ℕ) (α : G.P'.Form) (B : PlacedTile P) (hB : B ∈ fineTiles τ G j α)
    (i : Fin (P.disk B.form).n) {x y : Pt} (hxy : x ≠ y)
    (hsub : segment ℝ x y ⊆ B.side i ∩ frontier (parentRegion τ G j α)) :
    B.side i ⊆ frontier (parentRegion τ G j α) := by
  set R := parentRegion τ G j α with hRdef
  have hBR : ∀ C ∈ fineTiles τ G j α, C.carrier ⊆ R := fun C hC => by
    rw [hRdef, ← fs1_fineTiles_support]
    exact Set.subset_biUnion_of_mem (u := fun B => B.carrier) hC
  have hdisj : DisjointInteriors (fineTiles τ G j α) :=
    sa1_disjoint_iter τ _ _ (G.dissect α).disjoint
  intro w hw
  have hwR : w ∈ R := hBR B hB (fs1_side_subset_carrier B i hw)
  by_contra hwF
  have hwI : w ∈ interior R := by
    by_contra h
    exact hwF ⟨subset_closure hwR, h⟩
  have hconv : Convex ℝ (B.side i) := by rw [fs1_tile_side_eq]; exact convex_segment _ _
  obtain ⟨o, ho, how⟩ : ∃ o ∈ B.side i, o ≠ w := by
    by_contra hcon
    push_neg at hcon
    exact hxy ((hcon x (hsub (left_mem_segment ℝ x y)).1).trans
      (hcon y (hsub (right_mem_segment ℝ x y)).1).symm)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w hwI
  have htend : Filter.Tendsto (fun t : ℝ => AffineMap.lineMap w o t) (nhdsWithin 0 (Set.Ioi 0))
      (nhds w) := by
    have : Filter.Tendsto (fun t : ℝ => AffineMap.lineMap w o t) (nhds 0)
        (nhds (AffineMap.lineMap w o (0 : ℝ))) :=
      AffineMap.lineMap_continuous.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, htb, ht⟩ :=
    ((htend.eventually (Metric.ball_mem_nhds w hr)).and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  set v := AffineMap.lineMap w o t with hvdef
  have hvw : w ≠ v := by
    intro h
    have h0 : AffineMap.lineMap w o (0 : ℝ) = AffineMap.lineMap w o t := by simpa using h
    exact ht.1.ne (AffineMap.lineMap_injective ℝ how.symm h0)
  have hv : v ∈ B.side i := by
    have hvseg : v ∈ segment ℝ w o := by
      rw [segment_eq_image_lineMap]
      exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    exact hconv.segment_subset hw ho hvseg
  have hsw : segment ℝ w v ⊆ B.side i := hconv.segment_subset hw hv
  have hsI : segment ℝ w v ⊆ interior R :=
    ((convex_ball w r).segment_subset (Metric.mem_ball_self hr) htb).trans hball
  set K : Set (Set Pt) := {T | ∃ Z ∈ fineTiles τ G j α, Z ≠ B ∧ ∃ k : Fin (P.disk Z.form).n,
    T = Z.side k} with hKdef
  have hKfin : K.Finite := by
    refine Set.Finite.subset ((fs1_fineTiles_finite τ G j α).biUnion fun Z _ =>
      Set.finite_range (fun k : Fin (P.disk Z.form).n => Z.side k)) ?_
    rintro T ⟨Z, hZ, -, k, rfl⟩
    exact Set.mem_biUnion hZ ⟨k, rfl⟩
  have hKconv : ∀ T ∈ K, Convex ℝ T := by
    rintro T ⟨Z, -, -, k, rfl⟩
    rw [fs1_tile_side_eq]
    exact convex_segment _ _
  have hKcov : segment ℝ w v ⊆ ⋃₀ K := by
    intro z hz
    have hzI : z ∈ interior R := hsI hz
    have hzB : z ∈ B.side i := hsw hz
    have hY : IsClosed (⋃ Z ∈ {Z | Z ∈ fineTiles τ G j α ∧ Z ≠ B}, Z.carrier) :=
      ((fs1_fineTiles_finite τ G j α).subset fun _ h => h.1).isClosed_biUnion
        fun Z _ => fs1_carrier_closed Z
    have hsubY : interior R ∩ (B.carrier)ᶜ ⊆ ⋃ Z ∈ {Z | Z ∈ fineTiles τ G j α ∧ Z ≠ B},
        Z.carrier := by
      rintro p ⟨hp1, hp2⟩
      have hp : p ∈ support (fineTiles τ G j α) := by
        rw [fs1_fineTiles_support]; exact interior_subset hp1
      simp only [support, Set.mem_iUnion] at hp
      obtain ⟨Z, hZ, hpZ⟩ := hp
      have hne : Z ≠ B := by
        rintro rfl
        exact hp2 hpZ
      exact Set.mem_biUnion (x := Z) ⟨hZ, hne⟩ hpZ
    have hzfr : z ∈ frontier B.carrier := by
      rw [fs1_frontier_carrier]; exact Set.mem_iUnion.2 ⟨i, hzB⟩
    have hzcl : z ∈ closure (interior R ∩ (B.carrier)ᶜ) := by
      apply isOpen_interior.inter_closure
      refine ⟨hzI, ?_⟩
      rw [← frontier_compl] at hzfr
      exact frontier_subset_closure hzfr
    have hzY := hY.closure_subset (closure_mono hsubY hzcl)
    simp only [Set.mem_iUnion] at hzY
    obtain ⟨Z, ⟨hZ, hZB⟩, hzZ⟩ := hzY
    have hzF : z ∈ frontier Z.carrier := by
      refine ⟨subset_closure hzZ, fun hint => ?_⟩
      have hzcl' : z ∈ closure (interior B.carrier) := by
        rw [fs1_closure_interior_carrier]; exact fs1_side_subset_carrier B i hzB
      rw [mem_closure_iff] at hzcl'
      obtain ⟨q, hq1, hq2⟩ := hzcl' _ isOpen_interior hint
      exact Set.disjoint_left.mp (hdisj hZ hB hZB) hq1 hq2
    rw [fs1_frontier_carrier, Set.mem_iUnion] at hzF
    obtain ⟨k, hk⟩ := hzF
    exact ⟨_, ⟨Z, hZ, hZB, k, rfl⟩, hk⟩
  obtain ⟨T, ⟨Z, hZ, hZB, k, rfl⟩, u', v', huv', hsub'⟩ := fs1_cover hvw hKfin hKconv hKcov
  have hov : OverlapPos (B.side i) (Z.side k) :=
    ⟨u', v', huv', fun z hz => ⟨hsw (hsub' hz).1, (hsub' hz).2⟩⟩
  have heq : B.side i = Z.side k := hΔ α j B hB Z hZ i k hov
  have hBZ := cgb_frontier_tiles_eq (fineTiles τ G j α) hdisj R hBR hB hZ i k hxy
    (fun z hz => ⟨(hsub hz).1, heq ▸ (hsub hz).1⟩) (fun z hz => (hsub hz).2)
  exact hZB hBZ.symm

/-- A boundary side of an original-layer tile is a listed `.level j` side. -/
private lemma cgb_level_mem (m : ℕ) (j : Fin m) (α : G.P'.Form) (B : PlacedTile P)
    (hB : B ∈ τ.decomposeIter (j : ℕ) (G.dissect α).tiles) (i : Fin (P.disk B.form).n)
    (hfr : B.side i ⊆ frontier (parentRegion τ G (j : ℕ) α)) :
    ((τ.θ ^ (m - (j : ℕ))) • B.vertex i, (τ.θ ^ (m - (j : ℕ))) • B.vertex (finRotate _ i)) ∈
      layerSides τ G m α (.level j) := by
  refine ⟨B, hB, i, rfl, ?_⟩
  have hs : τ.θ ^ (m - (j : ℕ)) ≠ 0 := pow_ne_zero _ (by linarith [τ.one_lt])
  have hpow : τ.θ ^ m = τ.θ ^ (m - (j : ℕ)) * τ.θ ^ (j : ℕ) := by
    rw [← pow_add, Nat.sub_add_cancel j.isLt.le]
  have hreg : parentRegion τ G m α = τ.θ ^ (m - (j : ℕ)) • parentRegion τ G (j : ℕ) α := by
    rw [parentRegion, parentRegion, hpow, mul_smul]
  simp only
  rw [sa1_segment_smul, hreg, fs1_frontier_smul hs, ← fs1_tile_side_eq]
  exact Set.smul_set_mono hfr

/-- The placed scaled level side equals the scaled side of the translated tile. -/
private lemma cgb_placed_eq (m : ℕ) (j : ℕ) (hj : j ≤ m) (A : PlacedTile G.P') (B : PlacedTile P)
    (i : Fin (P.disk B.form).n) :
    placedSeg ((τ.θ ^ m) • A.anchor)
        ((τ.θ ^ (m - j)) • B.vertex i, (τ.θ ^ (m - j)) • B.vertex (finRotate _ i)) =
      (τ.θ ^ (m - j)) • (B.translate ((τ.θ ^ j) • A.anchor)).side i := by
  have hpow : τ.θ ^ m = τ.θ ^ (m - j) * τ.θ ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  rw [fs1_translate_side, placedSeg, placedSeg, ← sa1_segment_smul]
  simp only [smul_add, smul_smul, ← hpow]

/-- Step 3 of the blueprint proof of `schedule_intermediate_sts_step3_levels_sts`:
For distinct grouped parents, an overlapping intermediate side is a scaled
`.level j` boundary side of each parent.  The displayed equalities identify
those boundary sides with the scaled original sides.  The hypothesis `hΔ` (each original layer
inside one block is STS) is needed: without it a level-`j` side of one block may continue into
the interior of the block, so it is not a boundary side (codex's θ = 2 counterexample with a
non-side-to-side L rule, 14 October 2026). -/
private theorem schedule_intermediate_sts_step3_levels_sts_step3_cross_group_boundary
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (G.dissect α).tiles))
    (m : ℕ) (T' : PlaneTiling G.P') (j : Fin m)
    (A A' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles)
    (hAA' : A ≠ A') (X Y : PlacedTile P)
    (hX : X ∈ τ.decomposeIter (j : ℕ) (G.scatterTile A))
    (hY : Y ∈ τ.decomposeIter (j : ℕ) (G.scatterTile A'))
    (i : Fin (P.disk X.form).n) (i' : Fin (P.disk Y.form).n)
    (hXY : OverlapPos (X.side i) (Y.side i')) :
    ∃ c d,
      c ∈ layerSides τ G m A.form (.level j) ∧
      d ∈ layerSides τ G m A'.form (.level j) ∧
      placedSeg ((τ.θ ^ m) • A.anchor) c =
        (τ.θ ^ (m - (j : ℕ))) • X.side i ∧
      placedSeg ((τ.θ ^ m) • A'.anchor) d =
        (τ.θ ^ (m - (j : ℕ))) • Y.side i' := by
  have hjm : (j : ℕ) ≤ m := j.isLt.le
  revert i i' hXY
  obtain ⟨B, hB, rfl⟩ := cgb_decomposeIter_translate_inv τ (j : ℕ) A.anchor _ X hX
  obtain ⟨B', hB', rfl⟩ := cgb_decomposeIter_translate_inv τ (j : ℕ) A'.anchor _ Y hY
  intro i i' hXY
  obtain ⟨x, y, hxy, hs⟩ := hXY
  have hdisj := fs1_disj τ G (j : ℕ) T' A A' hA hA' hAA'
  have hBR : ∀ (α : G.P'.Form) (C : PlacedTile P), C ∈ fineTiles τ G (j : ℕ) α →
      C.carrier ⊆ parentRegion τ G (j : ℕ) α := fun α C hC => by
    rw [← fs1_fineTiles_support]
    exact Set.subset_biUnion_of_mem (u := fun B => B.carrier) hC
  have hsideX : (B.translate ((τ.θ ^ (j : ℕ)) • A.anchor)).side i = ((τ.θ ^ (j : ℕ)) • A.anchor) +ᵥ B.side i := by
    simp [PlacedTile.translate, PlacedTile.side, vadd_vadd]
  have hsideY : (B'.translate ((τ.θ ^ (j : ℕ)) • A'.anchor)).side i' = ((τ.θ ^ (j : ℕ)) • A'.anchor) +ᵥ B'.side i' := by
    simp [PlacedTile.translate, PlacedTile.side, vadd_vadd]
  have hfrA : segment ℝ x y ⊆ frontier (((τ.θ ^ (j : ℕ)) • A.anchor) +ᵥ parentRegion τ G (j : ℕ) A.form) := by
    intro z hz
    have hzX := (hs hz).1
    have hzY := (hs hz).2
    have hzR : z ∈ ((τ.θ ^ (j : ℕ)) • A.anchor) +ᵥ parentRegion τ G (j : ℕ) A.form := by
      have := fs1_side_subset_carrier _ i hzX
      rw [fs1_translate_carrier] at this
      exact Set.vadd_set_mono (hBR _ B hB) this
    refine ⟨subset_closure hzR, fun hint => ?_⟩
    rw [fs1_translate_side] at hzY
    have hcl := fs1_placed_side_sub τ G (j : ℕ) A'.form ((τ.θ ^ (j : ℕ)) • A'.anchor) B' hB' i' hzY
    rw [mem_closure_iff] at hcl
    obtain ⟨q, hq1, hq2⟩ := hcl _ isOpen_interior hint
    exact Set.disjoint_left.mp hdisj hq1 hq2
  have hfrA' : segment ℝ x y ⊆ frontier (((τ.θ ^ (j : ℕ)) • A'.anchor) +ᵥ parentRegion τ G (j : ℕ) A'.form) := by
    intro z hz
    have hzX := (hs hz).1
    have hzY := (hs hz).2
    have hzR : z ∈ ((τ.θ ^ (j : ℕ)) • A'.anchor) +ᵥ parentRegion τ G (j : ℕ) A'.form := by
      have := fs1_side_subset_carrier _ i' hzY
      rw [fs1_translate_carrier] at this
      exact Set.vadd_set_mono (hBR _ B' hB') this
    refine ⟨subset_closure hzR, fun hint => ?_⟩
    rw [fs1_translate_side] at hzX
    have hcl := fs1_placed_side_sub τ G (j : ℕ) A.form ((τ.θ ^ (j : ℕ)) • A.anchor) B hB i hzX
    rw [mem_closure_iff] at hcl
    obtain ⟨q, hq1, hq2⟩ := hcl _ isOpen_interior hint
    exact Set.disjoint_left.mp hdisj hq2 hq1
  have hcoreA : B.side i ⊆ frontier (parentRegion τ G (j : ℕ) A.form) := by
    refine cgb_core τ G hΔ (j : ℕ) A.form B hB i (x := -((τ.θ ^ (j : ℕ)) • A.anchor) +ᵥ x) (y := -((τ.θ ^ (j : ℕ)) • A.anchor) +ᵥ y)
      (fun h => hxy (vadd_left_cancel _ h)) (cgb_untranslate ((τ.θ ^ (j : ℕ)) • A.anchor) ?_)
    intro z hz
    refine ⟨?_, ?_⟩
    · rw [← hsideX]; exact (hs hz).1
    · rw [← fs1_frontier_vadd]; exact hfrA hz
  have hcoreA' : B'.side i' ⊆ frontier (parentRegion τ G (j : ℕ) A'.form) := by
    refine cgb_core τ G hΔ (j : ℕ) A'.form B' hB' i' (x := -((τ.θ ^ (j : ℕ)) • A'.anchor) +ᵥ x) (y := -((τ.θ ^ (j : ℕ)) • A'.anchor) +ᵥ y)
      (fun h => hxy (vadd_left_cancel _ h)) (cgb_untranslate ((τ.θ ^ (j : ℕ)) • A'.anchor) ?_)
    intro z hz
    refine ⟨?_, ?_⟩
    · rw [← hsideY]; exact (hs hz).2
    · rw [← fs1_frontier_vadd]; exact hfrA' hz
  exact ⟨_, _, cgb_level_mem τ G m j A.form B hB i hcoreA,
    cgb_level_mem τ G m j A'.form B' hB' i' hcoreA',
    cgb_placed_eq τ G m (j : ℕ) hjm A B i, cgb_placed_eq τ G m (j : ℕ) hjm A' B' i'⟩

/-- Step 3 of the blueprint proof of `schedule_intermediate_sts`:
Inside a block each original layer is already an STS supertile patch.
Thus, to check STS for any intermediate layer, we only need to compare sides that
arise from opposite macroblock boundaries, which correspond to `level j` layer sides. -/
private theorem schedule_intermediate_sts_step3_levels_sts
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (G.dissect α).tiles))
    (m : ℕ) (T' : PlaneTiling G.P')
    (hfine : SideToSideSet (τ.decomposeIter m (G.scatter T'.tiles)))
    (h_align : ∀ (A A' : PlacedTile G.P') (_hA : A ∈ T'.tiles) (_hA' : A' ∈ T'.tiles)
       (j : Fin m) (c d : Pt × Pt)
       (_hc : c ∈ layerSides τ G m A.form (.level j))
       (_hd : d ∈ layerSides τ G m A'.form (.level j)),
       OverlapPos (placedSeg ((τ.θ ^ m) • A.anchor) c)
         (placedSeg ((τ.θ ^ m) • A'.anchor) d) →
       placedSeg ((τ.θ ^ m) • A.anchor) c = placedSeg ((τ.θ ^ m) • A'.anchor) d) :
    ∀ j ≤ m, SideToSideSet (τ.decomposeIter j (G.scatter T'.tiles)) := by
  intro j hj
  by_cases hjm : j = m
  · subst j
    exact hfine
  have hjlt : j < m := lt_of_le_of_ne hj hjm
  let j' : Fin m := ⟨j, hjlt⟩
  intro X hX Y hY i i' hXY
  obtain ⟨A, hA, hXA⟩ :=
    schedule_intermediate_sts_step3_levels_sts_step1_scatter_membership
      τ G j T' X hX
  obtain ⟨A', hA', hYA⟩ :=
    schedule_intermediate_sts_step3_levels_sts_step1_scatter_membership
      τ G j T' Y hY
  by_cases hAA' : A = A'
  · subst A'
    exact schedule_intermediate_sts_step3_levels_sts_step2_within_group τ G hΔ j A
      X hXA Y hYA i i' hXY
  obtain ⟨c, d, hc, hd, hcx, hdy⟩ :=
    schedule_intermediate_sts_step3_levels_sts_step3_cross_group_boundary
      τ G hΔ m T' j' A A' hA hA' hAA' X Y hXA hYA i i' hXY
  have hs : τ.θ ^ (m - j) ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one τ.one_lt))
  have hscaled :
      OverlapPos ((τ.θ ^ (m - j)) • X.side i) ((τ.θ ^ (m - j)) • Y.side i') :=
    schedule_intermediate_sts_step2_overlap_smul hs hXY
  have hboundary :
      OverlapPos (placedSeg ((τ.θ ^ m) • A.anchor) c)
        (placedSeg ((τ.θ ^ m) • A'.anchor) d) := by
    rw [hcx, hdy]
    exact hscaled
  have heq := h_align A A' hA hA' j' c d hc hd hboundary
  have heq' :
      (τ.θ ^ (m - j)) • X.side i = (τ.θ ^ (m - j)) • Y.side i' := by
    exact hcx.symm.trans (heq.trans hdy)
  exact (Set.image_injective.mpr (smul_right_injective Pt hs)) heq'

/-- `lem:alignment-tuple`: if the fine level `τ^m (Δ T')` of a grouped plane
tiling is STS and schedules are aligned, then the grouped parents and every
inserted original level `τ^j (Δ T')`, `j ≤ m`, are STS.  The hypothesis `hΔ`
records that inside one block each original layer is an STS supertile
patch. -/
theorem schedule_intermediate_sts (hτ : τ.STS)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (G.dissect α).tiles))
    (m : ℕ) (T' : PlaneTiling G.P')
    (hfine : SideToSideSet (τ.decomposeIter m (G.scatter T'.tiles)))
    (halign : SchedulesAligned τ G m T') :
    SideToSideSet T'.tiles ∧ ∀ j ≤ m, SideToSideSet (τ.decomposeIter j (G.scatter T'.tiles)) := by
  constructor
  · apply schedule_intermediate_sts_step2_parents_sts τ G m T'
    intro A A' hA hA' c d hc hd hoverlap
    exact schedule_intermediate_sts_step1_boundary_align τ G hτ m T' hfine halign A A' hA hA'
      .top c d hc hd hoverlap
  · apply schedule_intermediate_sts_step3_levels_sts τ G hΔ m T' hfine
    intro A A' hA hA' j c d hc hd hoverlap
    exact schedule_intermediate_sts_step1_boundary_align τ G hτ m T' hfine halign A A' hA hA'
      (.level j) c d hc hd hoverlap

/-! ## Whole-side ports (`lem:whole-ports`) -/

/-- The whole fine outer sides whose closed segments lie strictly inside the
scaled parent side `s a`. -/
def sidesInside (m : ℕ) (A : G.P'.Form) (a : Fin (G.P'.disk A).n) : Set (Pt × Pt) :=
  {e ∈ fineOuterSides τ G m A |
    segment ℝ e.1 e.2 ⊆ openSegment ℝ (parentSide τ G m A a).1 (parentSide τ G m A a).2}

/-- Ordering key of a segment along the unit direction `u`: the coordinate of
its midpoint. -/
def sideKey (u : Pt) (e : Pt × Pt) : ℝ := coord 0 u ((1 / 2 : ℝ) • (e.1 + e.2))

/-- One-based rank of `e` in `X`, counted in the direction `u`. -/
def rankIn (X : Set (Pt × Pt)) (u : Pt) (e : Pt × Pt) : ℕ :=
  {e' ∈ X | sideKey u e' < sideKey u e}.ncard + 1

/-- The `(r+1)`-th interior sixth-quantile `⌈(r+1) L / 6⌉`, `r = 0, …, 4`. -/
def portIndex (L : ℕ) (r : Fin 5) : ℕ := (((r : ℕ) + 1) * L + 5) / 6

/-- The global canonical direction of the parent side `a`. -/
def parentDir (m : ℕ) (A : G.P'.Form) (a : Fin (G.P'.disk A).n) : Pt :=
  canonDir ((parentSide τ G m A a).2 - (parentSide τ G m A a).1)

/-- The `r`-th port of the parent side `a`: the whole fine side inside `s a`
of rank `⌈(r+1) L / 6⌉`, counted in the global canonical direction. -/
def port (m : ℕ) (A : G.P'.Form) (a : Fin (G.P'.disk A).n) (r : Fin 5) : Pt × Pt :=
  Classical.epsilon fun e =>
    e ∈ sidesInside τ G m A a ∧
      rankIn (sidesInside τ G m A a) (parentDir τ G m A a) e =
        portIndex (sidesInside τ G m A a).ncard r

/-- Step 1 of the blueprint proof of `whole_side_ports`: the length of the parent
side is the scaled length of the original side. -/
private lemma whole_side_ports_step1_parent_length (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) :
    dist (parentSide τ G m A a).1 (parentSide τ G m A a).2 =
      (τ.θ ^ m) * dist ((G.P'.disk A).vertex a) ((G.P'.disk A).vertex (finRotate _ a)) := by
  dsimp [parentSide]
  rw [dist_smul₀]
  have h : 0 < τ.θ := by linarith [τ.one_lt]
  rw [Real.norm_eq_abs, abs_of_pos (pow_pos h m)]

private lemma sl_line_of_two {p q x y : Pt} (hpq : p ≠ q) {t1 t2 : ℝ} (h12 : t1 ≠ t2)
    (h1 : AffineMap.lineMap p q t1 ∈ segment ℝ x y) (h2 : AffineMap.lineMap p q t2 ∈ segment ℝ x y) :
    ∃ a b : ℝ, x = AffineMap.lineMap p q a ∧ y = AffineMap.lineMap p q b := by
  rw [segment_eq_image_lineMap] at h1 h2
  obtain ⟨s1, -, hs1⟩ := h1
  obtain ⟨s2, -, hs2⟩ := h2
  simp only [AffineMap.lineMap_apply_module'] at hs1 hs2 ⊢
  have hs : s1 ≠ s2 := by
    rintro rfl
    apply h12
    have h' : (t1 - t2) • (q - p) = 0 := by
      linear_combination (norm := module) hs2 - hs1
    rcases smul_eq_zero.mp h' with h0 | h0
    · linarith [sub_eq_zero.mp h0]
    · exact absurd (sub_eq_zero.mp h0).symm hpq
  have hd : s2 - s1 ≠ 0 := sub_ne_zero.mpr hs.symm
  have hyx : y - x = ((t2 - t1) / (s2 - s1)) • (q - p) := by
    have : (s2 - s1) • (y - x) = (t2 - t1) • (q - p) := by
      linear_combination (norm := module) hs2 - hs1
    rw [div_eq_inv_mul, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hd, one_smul]
  have hx2 : x = t1 • (q - p) + p - s1 • (y - x) := by
    linear_combination (norm := module) hs1
  refine ⟨t1 - s1 * ((t2 - t1) / (s2 - s1)),
    t1 - s1 * ((t2 - t1) / (s2 - s1)) + (t2 - t1) / (s2 - s1), ?_, ?_⟩
  · linear_combination (norm := module) hx2 - s1 • hyx
  · linear_combination (norm := module) hx2 + (1 - s1) • hyx

private lemma sl_preimage_segment {p q : Pt} (hpq : p ≠ q) (a b : ℝ) :
    AffineMap.lineMap p q ⁻¹' segment ℝ (AffineMap.lineMap p q a) (AffineMap.lineMap p q b) =
      uIcc a b := by
  rw [← image_segment, (AffineMap.lineMap_injective ℝ hpq).preimage_image, segment_eq_uIcc]

private lemma sl_measure {ι : Type*} (s : Finset ι) (I : ι → Set ℝ) (len : ι → ℝ) (c : ℝ)
    (F : Set ℝ) (hF : F.Countable) (hc : 0 ≤ c)
    (hI : ∀ i ∈ s, MeasureTheory.volume (I i) ≤ ENNReal.ofReal (len i)) (hlen : ∀ i ∈ s, 0 ≤ len i)
    (hcov : Icc (0 : ℝ) 1 ⊆ (⋃ i ∈ s, I i) ∪ Icc 0 c ∪ Icc (1 - c) 1 ∪ F) :
    1 ≤ ∑ i ∈ s, len i + 2 * c := by
  have h := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hcov
  rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_one] at h
  have h2 : MeasureTheory.volume ((⋃ i ∈ s, I i) ∪ Icc 0 c ∪ Icc (1 - c) 1 ∪ F) ≤
      ∑ i ∈ s, ENNReal.ofReal (len i) + ENNReal.ofReal c + ENNReal.ofReal c := by
    refine (MeasureTheory.measure_union_le _ _).trans ?_
    rw [hF.measure_zero, add_zero]
    refine (MeasureTheory.measure_union_le _ _).trans ?_
    refine add_le_add ((MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ ?_)) ?_
    · exact (MeasureTheory.measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum hI)
    · rw [Real.volume_Icc, sub_zero]
    · rw [Real.volume_Icc]; apply le_of_eq; congr 1; ring
  have h3 := h.trans h2
  rw [← ENNReal.ofReal_sum_of_nonneg hlen, ← ENNReal.ofReal_add (Finset.sum_nonneg hlen) hc,
    ← ENNReal.ofReal_add (by linarith [Finset.sum_nonneg hlen]) hc, ← ENNReal.ofReal_one,
    ENNReal.ofReal_le_ofReal_iff (by linarith [Finset.sum_nonneg hlen])] at h3
  linarith

private lemma sl_side_le (M : MeshConstants P) (B : PlacedTile P) (i : Fin (P.disk B.form).n) :
    dist (B.vertex i) (B.vertex (finRotate _ i)) ≤ M.D := by
  have hmem : ∀ j : Fin (P.disk B.form).n, (P.disk B.form).vertex j ∈ (P.disk B.form).carrier := by
    intro j
    have hfr : (P.disk B.form).vertex j ∈ frontier (P.disk B.form).carrier := by
      rw [PolygonalDisk.frontier_eq]
      exact mem_iUnion.mpr ⟨j, left_mem_segment ℝ _ _⟩
    have hclosed : IsClosed (P.disk B.form).carrier := (P.disk B.form).compact.isClosed
    rw [← hclosed.closure_eq]
    exact frontier_subset_closure hfr
  have hbdd : Bornology.IsBounded (P.disk B.form).carrier := (P.disk B.form).compact.isBounded
  rw [PlacedTile.vertex, PlacedTile.vertex, dist_vadd]
  exact (Metric.dist_le_diam_of_mem hbdd (hmem i) (hmem (finRotate _ i))).trans (M.diam_le _)

/-- Step 1 of the blueprint proof of `whole_side_ports_step2_length_bound`: the length of the
parent side is at most the total length of the whole fine sides strictly inside it plus `2D`.
Accounting: every point of the open parent side lies on a fine side along its line (the fine
tiles cover the parent region and a boundary point lies on a side of an adjacent tile); a fine
side along the parent side that is contained in the open parent side is outer, hence in
`sidesInside`; any other fine side covering a piece of it contains an endpoint of the parent
side, and there is at most one such side per endpoint (two of them would bound tiles with
overlapping interiors), each of length at most `D`.  No side-to-side hypothesis is used: such a
side may be an outer side crossing a dummy parent vertex, or a non-outer side running through a
reflex parent corner, half on the parent side and half inside the region (Aristotle's L-shape
counterexample of 14 October 2026 to the earlier version, which summed only over outer sides
overlapping the parent side). -/
private lemma whole_side_ports_step2_length_bound_step1_all_edges_bound_step1_sum_lengths
    (τ : Substitution P) (G : GroupedFamily P) (M : MeshConstants P) (m : ℕ)
    (A : G.P'.Form) (a : Fin (G.P'.disk A).n) (h_fin : (sidesInside τ G m A a).Finite) :
    dist (parentSide τ G m A a).1 (parentSide τ G m A a).2 ≤
      ∑ e ∈ h_fin.toFinset, dist e.1 e.2 + 2 * M.D := by
  classical
  set p := (parentSide τ G m A a).1 with hp
  set q := (parentSide τ G m A a).2 with hq
  have hsum0 : 0 ≤ ∑ e ∈ h_fin.toFinset, dist e.1 e.2 := Finset.sum_nonneg fun _ _ => dist_nonneg
  by_cases hpq : p = q
  · rw [hpq, dist_self]; linarith [M.D_pos]
  have hL : 0 < dist p q := dist_pos.mpr hpq
  have hfrontier : segment ℝ p q ⊆ frontier (parentRegion τ G m A) :=
    fs1_layer_frontier τ G m A .top _ ⟨a, rfl⟩
  have hdl : ∀ u v : ℝ, dist (AffineMap.lineMap p q u) (AffineMap.lineMap p q v) = |u - v| * dist p q := by
    intro u v
    rw [dist_lineMap_lineMap, Real.dist_eq]
  let E := {e : Pt × Pt | ∃ B ∈ fineTiles τ G m A, ∃ i : Fin (P.disk B.form).n,
    e = (B.vertex i, B.vertex (finRotate _ i))}
  have hE : E.Finite := by
    refine Set.Finite.subset ((fs1_fineTiles_finite τ G m A).biUnion fun B _ =>
      Set.finite_range (fun i : Fin (P.disk B.form).n => (B.vertex i, B.vertex (finRotate _ i)))) ?_
    rintro e ⟨B, hB, i, rfl⟩
    exact Set.mem_biUnion hB ⟨i, rfl⟩
  let T : Pt × Pt → Set ℝ := fun e => AffineMap.lineMap p q ⁻¹' segment ℝ e.1 e.2 ∩ Icc 0 1
  let F := ⋃ e ∈ {e ∈ E | (T e).Subsingleton}, T e
  have hF : F.Countable :=
    (hE.subset (sep_subset _ _)).countable.biUnion fun e he => he.2.finite.countable
  have key := sl_measure h_fin.toFinset (fun e => AffineMap.lineMap p q ⁻¹' segment ℝ e.1 e.2)
    (fun e => dist e.1 e.2 / dist p q) (M.D / dist p q) F hF (div_nonneg M.D_pos.le hL.le) ?_
    (fun _ _ => div_nonneg dist_nonneg hL.le) ?_
  · have heq : ∑ e ∈ h_fin.toFinset, dist e.1 e.2 / dist p q + 2 * (M.D / dist p q) =
        (∑ e ∈ h_fin.toFinset, dist e.1 e.2 + 2 * M.D) / dist p q := by
      rw [← Finset.sum_div]; ring
    rw [heq, one_le_div hL] at key
    exact key
  · intro e he
    have he' : e ∈ sidesInside τ G m A a := h_fin.mem_toFinset.mp he
    have h1 : e.1 ∈ openSegment ℝ p q := he'.2 (left_mem_segment ℝ _ _)
    have h2 : e.2 ∈ openSegment ℝ p q := he'.2 (right_mem_segment ℝ _ _)
    rw [openSegment_eq_image_lineMap] at h1 h2
    obtain ⟨a1, -, ha1⟩ := h1
    obtain ⟨b1, -, hb1⟩ := h2
    simp only
    rw [← ha1, ← hb1, sl_preimage_segment hpq, Real.volume_interval, hdl,
      mul_div_cancel_right₀ _ hL.ne', abs_sub_comm]
  · intro t ht
    have hft : AffineMap.lineMap p q t ∈ frontier ((0 : Pt) +ᵥ parentRegion τ G m A) := by
      rw [zero_vadd]
      exact hfrontier (by rw [segment_eq_image_lineMap]; exact mem_image_of_mem _ ht)
    obtain ⟨T0, ⟨B, hB, i, rfl⟩, hT0⟩ := fs1_frontier_cover τ G m A 0 hft
    set e : Pt × Pt := (B.vertex i, B.vertex (finRotate _ i)) with he_def
    have heE : e ∈ E := ⟨B, hB, i, rfl⟩
    have htT : t ∈ T e := by
      refine ⟨?_, ht⟩
      simpa [placedSeg] using hT0
    by_cases hsub : (T e).Subsingleton
    · exact Or.inr (Set.mem_biUnion (x := e) ⟨heE, hsub⟩ htT)
    obtain ⟨t1, ht1, t2, ht2, h12⟩ := Set.not_subsingleton_iff.mp hsub
    obtain ⟨a1, b1, ha1, hb1⟩ := sl_line_of_two hpq h12 ht1.1 ht2.1
    have hpre : AffineMap.lineMap p q ⁻¹' segment ℝ e.1 e.2 = uIcc a1 b1 := by
      rw [ha1, hb1, sl_preimage_segment hpq]
    have ht' : t ∈ uIcc a1 b1 := hpre ▸ htT.1
    have hDe : |a1 - b1| * dist p q ≤ M.D := by
      rw [← hdl, ← ha1, ← hb1]
      exact sl_side_le M B i
    by_cases hin : uIcc a1 b1 ⊆ Ioo 0 1
    · have hseg : segment ℝ e.1 e.2 ⊆ openSegment ℝ p q := by
        rw [ha1, hb1, ← image_segment, segment_eq_uIcc, openSegment_eq_image_lineMap]
        exact image_mono hin
      have heS : e ∈ sidesInside τ G m A a :=
        ⟨⟨B, hB, i, rfl, hseg.trans ((openSegment_subset_segment ℝ p q).trans hfrontier)⟩, hseg⟩
      refine Or.inl (Or.inl (Or.inl (Set.mem_biUnion (h_fin.mem_toFinset.mpr heS) ?_)))
      exact htT.1
    · obtain ⟨s, hs, hsn⟩ := Set.not_subset.mp hin
      rcases le_or_gt s 0 with hs0 | hs0
      · have h0 : (0 : ℝ) ∈ uIcc a1 b1 := Set.ordConnected_uIcc.out hs ht' ⟨hs0, ht.1⟩
        have hle := Set.abs_sub_le_of_uIcc_subset_uIcc (Set.uIcc_subset_uIcc h0 ht')
        refine Or.inl (Or.inl (Or.inr ⟨ht.1, ?_⟩))
        rw [le_div_iff₀ hL]
        rw [abs_of_nonneg (by linarith [ht.1]), abs_sub_comm] at hle
        nlinarith
      · have hs1 : 1 ≤ s := by
          by_contra hcon
          exact hsn ⟨hs0, lt_of_not_ge hcon⟩
        have h1 : (1 : ℝ) ∈ uIcc a1 b1 := Set.ordConnected_uIcc.out ht' hs ⟨ht.2, hs1⟩
        have hle := Set.abs_sub_le_of_uIcc_subset_uIcc (Set.uIcc_subset_uIcc ht' h1)
        refine Or.inl (Or.inr ⟨?_, ht.2⟩)
        rw [abs_of_nonneg (by linarith [ht.2]), abs_sub_comm] at hle
        have : M.D / dist p q ≥ 1 - t := by
          rw [ge_iff_le, le_div_iff₀ hL]; nlinarith
        linarith

/-- Step 2 of the blueprint proof of `whole_side_ports_step2_length_bound_step1_all_edges_bound`: bound the length of each edge. -/
private lemma whole_side_ports_step2_length_bound_step1_all_edges_bound_step2_edge_bound
    (τ : Substitution P) (G : GroupedFamily P) (M : MeshConstants P) (m : ℕ)
    (A : G.P'.Form) (e : Pt × Pt) (he : e ∈ fineOuterSides τ G m A) :
    dist e.1 e.2 ≤ M.D := by
  obtain ⟨B, -, i, he1, -⟩ := he
  have hmem : ∀ j : Fin (P.disk B.form).n, (P.disk B.form).vertex j ∈ (P.disk B.form).carrier := by
    intro j
    have hfr : (P.disk B.form).vertex j ∈ frontier (P.disk B.form).carrier := by
      rw [PolygonalDisk.frontier_eq]
      exact mem_iUnion.mpr ⟨j, left_mem_segment ℝ _ _⟩
    have hclosed : IsClosed (P.disk B.form).carrier := (P.disk B.form).compact.isClosed
    rw [← hclosed.closure_eq]
    exact frontier_subset_closure hfr
  have hbdd : Bornology.IsBounded (P.disk B.form).carrier := (P.disk B.form).compact.isBounded
  have hd : dist ((P.disk B.form).vertex i) ((P.disk B.form).vertex (finRotate _ i)) ≤ M.D :=
    (Metric.dist_le_diam_of_mem hbdd (hmem i) (hmem (finRotate _ i))).trans (M.diam_le _)
  rw [he1]
  show dist (B.vertex i) (B.vertex (finRotate _ i)) ≤ M.D
  rw [PlacedTile.vertex, PlacedTile.vertex, dist_vadd]
  exact hd

private lemma whole_side_ports_step2_length_bound_step1_all_edges_bound_step3_finite_aux1
    (τ : Substitution P) (n : ℕ) {S : Set (PlacedTile P)} (hS : S.Finite) :
    (τ.decomposeIter n S).Finite := by
  induction n with
  | zero => exact hS
  | succ n ih =>
    change (τ.decompose (τ.decomposeIter n S)).Finite
    apply Set.Finite.biUnion ih
    intro A _
    exact Set.Finite.image _ (τ.rule A.form).finite

private lemma whole_side_ports_step2_length_bound_step1_all_edges_bound_step3_finite_aux2
    (τ : Substitution P) (G : GroupedFamily P) (m : ℕ) (A : G.P'.Form) :
    (fineOuterSides τ G m A).Finite := by
  have hfine : (fineTiles τ G m A).Finite :=
    whole_side_ports_step2_length_bound_step1_all_edges_bound_step3_finite_aux1 τ m
      (G.dissect A).finite
  have hsub : fineOuterSides τ G m A ⊆
      ⋃ B ∈ fineTiles τ G m A, Set.range (fun i : Fin (P.disk B.form).n =>
        ((B.vertex i, B.vertex (finRotate _ i)) : Pt × Pt)) := by
    rintro e ⟨B, hB, i, hei, -⟩
    exact Set.mem_biUnion hB ⟨i, hei.symm⟩
  exact (Set.Finite.biUnion hfine fun B _ => Set.finite_range _).subset hsub

/-- Step 3 of the blueprint proof of `whole_side_ports_step2_length_bound_step1_all_edges_bound`: the set of fine edges on the parent side is finite. -/
private lemma whole_side_ports_step2_length_bound_step1_all_edges_bound_step3_finite
    (τ : Substitution P) (G : GroupedFamily P) (m : ℕ)
    (A : G.P'.Form) (a : Fin (G.P'.disk A).n) :
    {e ∈ fineOuterSides τ G m A | OverlapPos (segment ℝ e.1 e.2)
        (segment ℝ (parentSide τ G m A a).1 (parentSide τ G m A a).2)}.Finite :=
  (whole_side_ports_step2_length_bound_step1_all_edges_bound_step3_finite_aux2 τ G m A).sep _

private lemma omitted_count_support_translateSet (v : Pt) (S : Set (PlacedTile P)) :
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

private lemma omitted_count_support_decomposeTile (A : PlacedTile P) :
    support (τ.decomposeTile A) = τ.θ • A.carrier := by
  dsimp [Substitution.decomposeTile]
  rw [omitted_count_support_translateSet, τ.support_eq, PlacedTile.carrier]
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

private lemma omitted_count_support_decompose (S : Set (PlacedTile P)) :
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
    rwa [omitted_count_support_decomposeTile] at h
  · rintro ⟨A, hA, hx⟩
    have h : x ∈ support (τ.decomposeTile A) := by
      rwa [omitted_count_support_decomposeTile]
    simp only [support, Set.mem_iUnion] at h
    rcases h with ⟨B, hB, hxB⟩
    exact ⟨B, ⟨A, hA, hB⟩, hxB⟩

private lemma omitted_count_fineTiles_support (m : ℕ) (A : G.P'.Form) :
    support (fineTiles τ G m A) = (τ.θ ^ m) • (G.P'.disk A).carrier := by
  induction m with
  | zero => simpa [fineTiles, Substitution.decomposeIter] using G.support_eq A
  | succ m ih =>
      change support (τ.decompose (τ.decomposeIter m (G.dissect A).tiles)) = _
      rw [omitted_count_support_decompose]
      change support (τ.decomposeIter m (G.dissect A).tiles) = _ at ih
      rw [ih, smul_smul, pow_succ']

private lemma omitted_count_decomposeTile_disjoint (A : PlacedTile P) :
    DisjointInteriors (τ.decomposeTile A) := by
  dsimp [Substitution.decomposeTile, translateSet]
  intro T₁ hT₁ T₂ hT₂ hne
  rcases hT₁ with ⟨B₁, hB₁, rfl⟩
  rcases hT₂ with ⟨B₂, hB₂, rfl⟩
  have hne' : B₁ ≠ B₂ := fun h => hne (by rw [h])
  have hd := (τ.rule A.form).disjoint hB₁ hB₂ hne'
  dsimp [Function.onFun] at hd ⊢
  have heq₁ : (B₁.translate (τ.θ • A.anchor)).carrier =
      (τ.θ • A.anchor) +ᵥ B₁.carrier := by
    ext x
    simp only [PlacedTile.carrier, PlacedTile.translate, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_rev]
    rw [← add_assoc]
  have heq₂ : (B₂.translate (τ.θ • A.anchor)).carrier =
      (τ.θ • A.anchor) +ᵥ B₂.carrier := by
    ext x
    simp only [PlacedTile.carrier, PlacedTile.translate, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_rev]
    rw [← add_assoc]
  rw [heq₁, heq₂, interior_vadd, interior_vadd]
  have hinj : Function.Injective ((τ.θ • A.anchor) +ᵥ · : Pt → Pt) := add_right_injective _
  exact (Set.disjoint_image_iff hinj).mpr hd

private lemma omitted_count_decompose_disjoint (S : Set (PlacedTile P))
    (hS : DisjointInteriors S) : DisjointInteriors (τ.decompose S) := by
  intro T₁ hT₁ T₂ hT₂ hne
  dsimp [Substitution.decompose] at hT₁ hT₂
  simp only [Set.mem_iUnion, exists_prop] at hT₁ hT₂
  rcases hT₁ with ⟨A, hA, hT₁A⟩
  rcases hT₂ with ⟨B, hB, hT₂B⟩
  by_cases hAB : A = B
  · subst hAB
    exact omitted_count_decomposeTile_disjoint τ A hT₁A hT₂B hne
  · have hθ : τ.θ ≠ 0 := by linarith [τ.one_lt]
    have hscaled : Disjoint (interior (τ.θ • A.carrier)) (interior (τ.θ • B.carrier)) := by
      rw [interior_smul₀ hθ, interior_smul₀ hθ]
      exact (Set.disjoint_image_iff (smul_right_injective Pt hθ)).mpr (hS hA hB hAB)
    apply hscaled.mono
    · apply interior_mono
      intro x hx
      rw [← omitted_count_support_decomposeTile τ A]
      exact Set.mem_iUnion₂.2 ⟨T₁, hT₁A, hx⟩
    · apply interior_mono
      intro x hx
      rw [← omitted_count_support_decomposeTile τ B]
      exact Set.mem_iUnion₂.2 ⟨T₂, hT₂B, hx⟩

private lemma omitted_count_fineTiles_disjoint (m : ℕ) (A : G.P'.Form) :
    DisjointInteriors (fineTiles τ G m A) := by
  induction m with
  | zero => simpa [fineTiles, Substitution.decomposeIter] using (G.dissect A).disjoint
  | succ m ih =>
      exact omitted_count_decompose_disjoint τ _ ih

private lemma omitted_count_finRotate_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    finRotate n i ≠ i := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have h₁ : (1 : Fin (k + 1)) = 0 := by
    have h₂ := congrArg (fun x => x - i) h
    simpa using h₂
  have : NeZero (k + 1) := ⟨by omega⟩
  rw [Fin.one_eq_zero_iff] at h₁
  omega

private lemma omitted_count_tile_vertex_ne_next (B : PlacedTile P)
    (i : Fin (P.disk B.form).n) : B.vertex i ≠ B.vertex (finRotate _ i) := by
  intro h
  have h' := (vadd_left_cancel_iff B.anchor).mp h
  have hi := (P.disk B.form).vertex_injective h'
  exact omitted_count_finRotate_ne_self (by have := (P.disk B.form).three_le; omega) i hi.symm

private lemma omitted_count_parent_endpoints_ne (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) :
    (parentSide τ G m A a).1 ≠ (parentSide τ G m A a).2 := by
  dsimp [parentSide]
  intro h
  have h' := smul_right_injective Pt (pow_ne_zero _ (by linarith [τ.one_lt])) h
  exact (G.P'.disk A).vertex_injective.ne
    (Ne.symm (omitted_count_finRotate_ne_self
      (by have := (G.P'.disk A).three_le; omega) a)) h'

private lemma omitted_count_endpoint_of_subsegment {p q x y : Pt} (hpq : p ≠ q)
    (hsub : segment ℝ x y ⊆ segment ℝ p q)
    (hp : p ∈ segment ℝ x y) : p = x ∨ p = y := by
  have hx : Wbtw ℝ p x q := mem_segment_iff_wbtw.mp (hsub (left_mem_segment ℝ x y))
  have hy : Wbtw ℝ p y q := mem_segment_iff_wbtw.mp (hsub (right_mem_segment ℝ x y))
  have hsame : SameRay ℝ (x -ᵥ p) (y -ᵥ p) := by
    apply hx.sameRay_vsub_left.trans hy.sameRay_vsub_left.symm
    intro hqp
    exact False.elim (hpq (sub_eq_zero.mp hqp).symm)
  have hp' : Wbtw ℝ x p y := mem_segment_iff_wbtw.mp hp
  rcases wbtw_total_of_sameRay_vsub_left hsame with h | h
  · exact Or.inl (hp'.swap_left_iff.mp h).symm
  · exact Or.inr (hp'.symm.swap_left_iff.mp h).symm

private lemma omitted_count_common_open_from_endpoint {p q r s : Pt} (hpq : p ≠ q)
    (hrp : r ≠ p) (hsp : s ≠ p) (hr : r ∈ segment ℝ p q)
    (hs : s ∈ segment ℝ p q) :
    ∃ z, z ∈ openSegment ℝ p r ∧ z ∈ openSegment ℝ p s := by
  have hpr : Wbtw ℝ p r q := mem_segment_iff_wbtw.mp hr
  have hps : Wbtw ℝ p s q := mem_segment_iff_wbtw.mp hs
  have hsame : SameRay ℝ (r -ᵥ p) (s -ᵥ p) := by
    apply hpr.sameRay_vsub_left.trans hps.sameRay_vsub_left.symm
    intro hqp
    exact False.elim (hpq (sub_eq_zero.mp hqp).symm)
  rcases wbtw_total_of_sameRay_vsub_left hsame with hrs | hsr
  · let z := AffineMap.lineMap p r (1 / 2 : ℝ)
    have hzpr : z ∈ openSegment ℝ p r :=
      lineMap_mem_openSegment (𝕜 := ℝ) p r (by norm_num)
    have hzp : z ≠ p := by
      intro hzp
      rw [hzp] at hzpr
      exact hrp (left_mem_openSegment_iff.mp hzpr).symm
    have hzr : z ≠ r := by
      intro hzr
      rw [hzr] at hzpr
      exact hrp (right_mem_openSegment_iff.mp hzpr).symm
    have hzstrict : Sbtw ℝ p z r :=
      ⟨mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ p r hzpr),
        hzp, hzr⟩
    have hzps := hrs.trans_sbtw_left hzstrict
    exact ⟨z, hzpr, mem_openSegment_of_ne_left_right hzps.left_ne hzps.right_ne
      hzps.wbtw.mem_segment⟩
  · let z := AffineMap.lineMap p s (1 / 2 : ℝ)
    have hzps : z ∈ openSegment ℝ p s :=
      lineMap_mem_openSegment (𝕜 := ℝ) p s (by norm_num)
    have hzp : z ≠ p := by
      intro hzp
      rw [hzp] at hzps
      exact hsp (left_mem_openSegment_iff.mp hzps).symm
    have hzs : z ≠ s := by
      intro hzs
      rw [hzs] at hzps
      exact hsp (right_mem_openSegment_iff.mp hzps).symm
    have hzstrict : Sbtw ℝ p z s :=
      ⟨mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ p s hzps),
        hzp, hzs⟩
    have hzpr := hsr.trans_sbtw_left hzstrict
    exact ⟨z, mem_openSegment_of_ne_left_right hzpr.left_ne hzpr.right_ne
      hzpr.wbtw.mem_segment, hzps⟩

private lemma omitted_count_common_open {p q x y u v : Pt} (hpq : p ≠ q)
    (hxy : x ≠ y) (huv : u ≠ v)
    (hsub₁ : segment ℝ x y ⊆ segment ℝ p q)
    (hsub₂ : segment ℝ u v ⊆ segment ℝ p q)
    (hp₁ : p ∈ segment ℝ x y) (hp₂ : p ∈ segment ℝ u v) :
    ∃ z, z ∈ openSegment ℝ x y ∧ z ∈ openSegment ℝ u v := by
  have hx := hsub₁ (left_mem_segment ℝ x y)
  have hy := hsub₁ (right_mem_segment ℝ x y)
  have hu := hsub₂ (left_mem_segment ℝ u v)
  have hv := hsub₂ (right_mem_segment ℝ u v)
  rcases omitted_count_endpoint_of_subsegment hpq hsub₁ hp₁ with hpx | hpy <;>
    rcases omitted_count_endpoint_of_subsegment hpq hsub₂ hp₂ with hpu | hpv
  · subst x; subst u
    exact omitted_count_common_open_from_endpoint hpq hxy.symm huv.symm hy hv
  · subst x; subst v
    simpa [openSegment_symm] using
      omitted_count_common_open_from_endpoint hpq hxy.symm huv hy hu
  · subst y; subst u
    simpa [openSegment_symm] using
      omitted_count_common_open_from_endpoint hpq hxy huv.symm hx hv
  · subst y; subst v
    simpa [openSegment_symm] using
      omitted_count_common_open_from_endpoint hpq hxy huv hx hu

private lemma omitted_count_collinear_of_segment_subset {p q x y u v : Pt}
    (h₁ : segment ℝ x y ⊆ segment ℝ p q)
    (h₂ : segment ℝ u v ⊆ segment ℝ p q) :
    Collinear ℝ ({x, y, u, v} : Set Pt) := by
  rw [collinear_iff_of_mem (show x ∈ ({x, y, u, v} : Set Pt) by simp)]
  refine ⟨q - p, ?_⟩
  have hform : ∀ {z : Pt}, z ∈ segment ℝ p q →
      ∃ t : ℝ, z = t • (q - p) + p := by
    intro z hz
    rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨b, ?_⟩
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    module
  have hx := h₁ (left_mem_segment ℝ x y)
  obtain ⟨tx, htx⟩ := hform hx
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  have hzseg : z ∈ segment ℝ p q := by
    rcases hz with h | h | h | h
    · exact h ▸ hx
    · exact h ▸ h₁ (right_mem_segment ℝ x y)
    · exact h ▸ h₂ (left_mem_segment ℝ u v)
    · exact h ▸ h₂ (right_mem_segment ℝ u v)
  obtain ⟨tz, htz⟩ := hform hzseg
  refine ⟨tz - tx, ?_⟩
  change z = (tz - tx) • (q - p) + x
  calc
    z = tz • (q - p) + p := htz
    _ = (tz - tx) • (q - p) + (tx • (q - p) + p) := by module
    _ = (tz - tx) • (q - p) + x := by rw [← htx]

private lemma omitted_count_tile_side_eq (B : PlacedTile P)
    (i : Fin (P.disk B.form).n) :
    B.side i = segment ℝ (B.vertex i) (B.vertex (finRotate _ i)) := by
  simp [PlacedTile.side, PolygonalDisk.side, PlacedTile.vertex, vadd_segment]

private lemma omitted_count_open_ne_left {x y z : Pt} (hxy : x ≠ y)
    (hz : z ∈ openSegment ℝ x y) : z ≠ x := by
  intro h
  rw [h] at hz
  exact hxy (left_mem_openSegment_iff.mp hz)

private lemma omitted_count_open_ne_right {x y z : Pt} (hxy : x ≠ y)
    (hz : z ∈ openSegment ℝ x y) : z ≠ y := by
  intro h
  rw [h] at hz
  exact hxy (right_mem_openSegment_iff.mp hz)

private lemma omitted_count_same_tile_side_index (B : PlacedTile P)
    (i j : Fin (P.disk B.form).n) (z : Pt)
    (hi : z ∈ openSegment ℝ (B.vertex i) (B.vertex (finRotate _ i)))
    (hj : z ∈ segment ℝ (B.vertex j) (B.vertex (finRotate _ j))) : i = j := by
  have hi' := hi
  have hj' := hj
  change z ∈ openSegment ℝ
    (B.anchor +ᵥ (P.disk B.form).vertex i)
    (B.anchor +ᵥ (P.disk B.form).vertex (finRotate _ i)) at hi'
  change z ∈ segment ℝ
    (B.anchor +ᵥ (P.disk B.form).vertex j)
    (B.anchor +ᵥ (P.disk B.form).vertex (finRotate _ j)) at hj'
  rw [← vadd_openSegment, Set.mem_vadd_set_iff_neg_vadd_mem] at hi'
  rw [← vadd_segment, Set.mem_vadd_set_iff_neg_vadd_mem] at hj'
  by_contra hij
  have hs := (P.disk B.form).simple i j hij
    ⟨openSegment_subset_segment ℝ _ _ hi', hj'⟩
  have hne : (P.disk B.form).vertex i ≠
      (P.disk B.form).vertex (finRotate _ i) :=
    (P.disk B.form).vertex_injective.ne
      (Ne.symm (omitted_count_finRotate_ne_self
        (by have := (P.disk B.form).three_le; omega) i))
  rcases hs.1 with h | h
  · rw [h] at hi'
    exact hne (left_mem_openSegment_iff.mp hi')
  · rw [Set.mem_singleton_iff] at h
    rw [h] at hi'
    exact hne (right_mem_openSegment_iff.mp hi')

set_option maxHeartbeats 800000 in
private lemma omitted_count_edge_unique_at_endpoint
    (m : ℕ) (A : G.P'.Form) (p q : Pt) (e f : Pt × Pt) (hpq : p ≠ q)
    (he : e ∈ fineOuterSides τ G m A) (hf : f ∈ fineOuterSides τ G m A)
    (hesub : segment ℝ e.1 e.2 ⊆ segment ℝ p q)
    (hfsub : segment ℝ f.1 f.2 ⊆ segment ℝ p q)
    (hpₑ : p ∈ segment ℝ e.1 e.2) (hp_f : p ∈ segment ℝ f.1 f.2) : e = f := by
  obtain ⟨B, hB, i, heq, hefront⟩ := he
  obtain ⟨C, hC, j, hfeq, hffront⟩ := hf
  subst e
  subst f
  have hBi := omitted_count_tile_vertex_ne_next B i
  have hCj := omitted_count_tile_vertex_ne_next C j
  obtain ⟨z, hzB, hzC⟩ := omitted_count_common_open
    hpq hBi hCj hesub hfsub hpₑ hp_f
  have hBC : B = C := by
    by_contra hBC
    have hdisj : Disjoint (interior B.carrier) (interior C.carrier) :=
      omitted_count_fineTiles_disjoint τ G m A hB hC hBC
    have hzBi : z ∈ B.side i := by
      rw [omitted_count_tile_side_eq]
      exact openSegment_subset_segment ℝ _ _ hzB
    have hzCj : z ∈ C.side j := by
      rw [omitted_count_tile_side_eq]
      exact openSegment_subset_segment ℝ _ _ hzC
    have hcol : Collinear ℝ ({B.vertex i, B.vertex (finRotate _ i),
        C.vertex j, C.vertex (finRotate _ j)} : Set Pt) :=
      omitted_count_collinear_of_segment_subset hesub hfsub
    have hzBi₁ : z ≠ B.vertex i := omitted_count_open_ne_left hBi hzB
    have hzBi₂ : z ≠ B.vertex (finRotate _ i) := omitted_count_open_ne_right hBi hzB
    have hzCj₁ : z ≠ C.vertex j := omitted_count_open_ne_left hCj hzC
    have hzCj₂ : z ≠ C.vertex (finRotate _ j) := omitted_count_open_ne_right hCj hzC
    let δ := min (dist z (B.vertex i))
      (min (dist z (B.vertex (finRotate _ i)))
        (min (dist z (C.vertex j)) (dist z (C.vertex (finRotate _ j)))))
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (dist_pos.mpr hzBi₁)
        (lt_min (dist_pos.mpr hzBi₂) (lt_min (dist_pos.mpr hzCj₁) (dist_pos.mpr hzCj₂)))
    have hhalf : (2 * δ) / 2 = δ := by ring
    obtain ⟨η, hη, hball⟩ :=
      Crowns.trimmedEdgeTwoTileBall (P := P) (d := 2 * δ) (by positivity)
    have hcover : Metric.ball z η ⊆ B.carrier ∪ C.carrier := by
      apply hball B C hdisj i j z hzBi hzCj hcol
      all_goals rw [hhalf]
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hballRegion : Metric.ball z η ⊆ parentRegion τ G m A := by
      intro x hx
      rw [parentRegion, ← omitted_count_fineTiles_support τ G]
      rcases hcover hx with hxB | hxC
      · exact Set.mem_iUnion₂.2 ⟨B, hB, hxB⟩
      · exact Set.mem_iUnion₂.2 ⟨C, hC, hxC⟩
    have hzint : z ∈ interior (parentRegion τ G m A) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (Metric.ball_mem_nhds z hη) hballRegion
    exact (hefront (openSegment_subset_segment ℝ _ _ hzB)).2 hzint
  subst C
  have hij := omitted_count_same_tile_side_index B i j z hzB
    (openSegment_subset_segment ℝ _ _ hzC)
  subst j
  rfl

/-- Step 2's endpoint uniqueness substep: two overlapping fine outer sides that both contain
the same endpoint of the parent side coincide. -/
private lemma whole_side_ports_step2_length_bound_step2_omitted_count_edge_unique_at_endpoint
    (τ : Substitution P) (G : GroupedFamily P) (m : ℕ) (A : G.P'.Form)
    (p q : Pt) (e f : Pt × Pt) (hpq : p ≠ q)
    (he : e ∈ fineOuterSides τ G m A) (hf : f ∈ fineOuterSides τ G m A)
    (heov : OverlapPos (segment ℝ e.1 e.2) (segment ℝ p q))
    (hfov : OverlapPos (segment ℝ f.1 f.2) (segment ℝ p q))
    (hpe : p ∈ segment ℝ e.1 e.2) (hpf : p ∈ segment ℝ f.1 f.2) : e = f := by
  have hcommon : OverlapPos (segment ℝ e.1 e.2) (segment ℝ f.1 f.2) := by
    obtain ⟨x, y, hxy, hxe⟩ := heov
    obtain ⟨u, v, huv, hxf⟩ := hfov
    have hex : ∃ r, r ≠ p ∧ r ∈ segment ℝ e.1 e.2 ∧ r ∈ segment ℝ p q := by
      by_cases hxp : x = p
      · refine ⟨y, ?_, (hxe (right_mem_segment ℝ x y)).1,
          (hxe (right_mem_segment ℝ x y)).2⟩
        intro hyp
        exact hxy (hxp.trans hyp.symm)
      · exact ⟨x, hxp, (hxe (left_mem_segment ℝ x y)).1,
          (hxe (left_mem_segment ℝ x y)).2⟩
    have hfu : ∃ s, s ≠ p ∧ s ∈ segment ℝ f.1 f.2 ∧ s ∈ segment ℝ p q := by
      by_cases hup : u = p
      · refine ⟨v, ?_, (hxf (right_mem_segment ℝ u v)).1,
          (hxf (right_mem_segment ℝ u v)).2⟩
        intro hpv
        exact huv (hup.trans hpv.symm)
      · exact ⟨u, hup, (hxf (left_mem_segment ℝ u v)).1,
          (hxf (left_mem_segment ℝ u v)).2⟩
    obtain ⟨r, hrp, hre, hrpq⟩ := hex
    obtain ⟨s, hsp, hsf, hspq⟩ := hfu
    obtain ⟨z, hzpr, hzps⟩ := omitted_count_common_open_from_endpoint hpq hrp hsp hrpq hspq
    have hpr_e : segment ℝ p r ⊆ segment ℝ e.1 e.2 :=
      (convex_segment _ _).segment_subset hpe hre
    have hps_f : segment ℝ p s ⊆ segment ℝ f.1 f.2 :=
      (convex_segment _ _).segment_subset hpf hsf
    have hpz_r : segment ℝ p z ⊆ segment ℝ p r :=
      (convex_segment _ _).segment_subset (left_mem_segment ℝ p r)
        (openSegment_subset_segment ℝ _ _ hzpr)
    have hpz_s : segment ℝ p z ⊆ segment ℝ p s :=
      (convex_segment _ _).segment_subset (left_mem_segment ℝ p s)
        (openSegment_subset_segment ℝ _ _ hzps)
    refine ⟨p, z, (omitted_count_open_ne_left hrp.symm hzpr).symm, ?_⟩
    intro w hw
    exact ⟨hpr_e (hpz_r hw), hps_f (hpz_s hw)⟩
  obtain ⟨B, hB, i, heq, hefront⟩ := he
  obtain ⟨C, hC, j, hfeq, hffront⟩ := hf
  have hR : ∀ D ∈ fineTiles τ G m A, D.carrier ⊆ parentRegion τ G m A := by
    intro D hD x hx
    rw [parentRegion, ← omitted_count_fineTiles_support τ G m A]
    exact Set.mem_iUnion₂.2 ⟨D, hD, hx⟩
  have hfront : B.side i ⊆ frontier (parentRegion τ G m A) := by
    rw [omitted_count_tile_side_eq]
    simpa [heq] using hefront
  have hBC := sa1_frontier_tiles_eq (fineTiles τ G m A)
    (omitted_count_fineTiles_disjoint τ G m A) (parentRegion τ G m A) hR hB hC i j hfront
    (by
      rw [omitted_count_tile_side_eq, omitted_count_tile_side_eq]
      simpa [heq, hfeq] using hcommon)
  subst C
  have hside : OverlapPos (B.side i) (B.side j) := by
    rw [omitted_count_tile_side_eq, omitted_count_tile_side_eq]
    simpa [heq, hfeq] using hcommon
  have hij := sa1_same_tile_side B i j hside
  subst j
  rw [heq, hfeq]

private lemma whole_side_ports_step2_length_bound_step2_omitted_count_overlap_inside_or_endpoint
    {p q x y : Pt} (hpq : p ≠ q)
    (hov : OverlapPos (segment ℝ x y) (segment ℝ p q)) :
    segment ℝ x y ⊆ openSegment ℝ p q ∨ p ∈ segment ℝ x y ∨ q ∈ segment ℝ x y := by
  have hspan := sa1_ba_overlap_span hov
  obtain ⟨u, v, huv, huvsub⟩ := hov
  have hline : ∀ z ∈ affineSpan ℝ ({p, q} : Set Pt),
      ∃ r : ℝ, z = p + r • (q - p) := by
    intro z hz
    obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hz
    rw [AffineMap.lineMap_apply] at hr
    exact ⟨r, by simpa [vsub_eq_sub, vadd_eq_add, add_comm] using hr.symm⟩
  have hpoint : ∀ {a b t : ℝ}, a < b → a ≤ t → t ≤ b →
      p + t • (q - p) ∈ segment ℝ (p + a • (q - p)) (p + b • (q - p)) := by
    intro a b t hab hat htb
    rw [segment_eq_image']
    let r := (t - a) / (b - a)
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact div_nonneg (sub_nonneg.mpr hat) (le_of_lt (sub_pos.mpr hab))
    have hr1 : r ≤ 1 := by
      dsimp [r]
      apply (div_le_iff₀ (sub_pos.mpr hab)).2
      linarith
    refine ⟨r, ⟨hr0, hr1⟩, ?_⟩
    dsimp [r]
    have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    have hscalar : a + (t - a) / (b - a) * (b - a) = t := by
      field_simp [hden]
      ring
    calc
      (p + a • (q - p)) + r • ((p + b • (q - p)) - (p + a • (q - p))) =
          p + (a + (t - a) / (b - a) * (b - a)) • (q - p) := by
        dsimp [r]
        module
      _ = p + t • (q - p) := by rw [hscalar]
  have hpd : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hxline : x ∈ affineSpan ℝ ({p, q} : Set Pt) := by
    rw [← hspan]
    exact left_mem_affineSpan_pair ℝ x y
  have hyline : y ∈ affineSpan ℝ ({p, q} : Set Pt) := by
    rw [← hspan]
    exact right_mem_affineSpan_pair ℝ x y
  obtain ⟨rx, hrx⟩ := hline x hxline
  obtain ⟨ry, hry⟩ := hline y hyline
  have hmem_scalar : ∀ {a b t : ℝ}, a ≤ t → t ≤ b →
      p + t • (q - p) ∈ segment ℝ (p + a • (q - p)) (p + b • (q - p)) := by
    intro a b t hat htb
    by_cases hab : a < b
    · exact hpoint hab hat htb
    · have hba : b ≤ a := le_of_not_gt hab
      have h : a = b := le_antisymm (le_trans hat htb) hba
      subst h
      have ht : t = a := le_antisymm htb hat
      subst t
      rw [segment_same]
      rfl
  by_cases hpE : p ∈ segment ℝ x y
  · exact Or.inr (Or.inl hpE)
  by_cases hqE : q ∈ segment ℝ x y
  · exact Or.inr (Or.inr hqE)
  have huP : u ∈ segment ℝ p q := (huvsub (left_mem_segment ℝ u v)).2
  obtain ⟨t, ht0, ht1, hut⟩ := (sa1_ba_mem_segment).1 huP
  have huE : u ∈ segment ℝ x y := (huvsub (left_mem_segment ℝ u v)).1
  rw [segment_eq_image'] at huE
  obtain ⟨s, hs, hus⟩ := huE
  have hscalar : t = rx + s * (ry - rx) := by
    have heq : p + t • (q - p) = p + (rx + s * (ry - rx)) • (q - p) := by
      calc
        p + t • (q - p) = u := hut.symm
        _ = x + s • (y - x) := hus.symm
        _ = p + (rx + s * (ry - rx)) • (q - p) := by rw [hrx, hry]; module
    exact sa1_ba_smul_cancel hpd (add_left_cancel heq)
  have hbetween : (rx ≤ t ∧ t ≤ ry) ∨ (ry ≤ t ∧ t ≤ rx) := by
    by_cases hxy' : rx ≤ ry
    · left
      constructor <;> nlinarith [hs.1, hs.2]
    · right
      have hyx : ry ≤ rx := le_of_not_ge hxy'
      constructor <;> nlinarith [hs.1, hs.2]
  have hzero : ¬ ((rx ≤ 0 ∧ 0 ≤ ry) ∨ (ry ≤ 0 ∧ 0 ≤ rx)) := by
    rintro (h | h)
    · exact hpE (by simpa [hrx, hry] using hmem_scalar h.1 h.2)
    · exact hpE (by simpa [hrx, hry, segment_symm] using hmem_scalar h.1 h.2)
  have hone : ¬ ((rx ≤ 1 ∧ 1 ≤ ry) ∨ (ry ≤ 1 ∧ 1 ≤ rx)) := by
    rintro (h | h)
    · exact hqE (by simpa [hrx, hry] using hmem_scalar h.1 h.2)
    · exact hqE (by simpa [hrx, hry, segment_symm] using hmem_scalar h.1 h.2)
  have hrx0 : 0 < rx := by
    rcases hbetween with h | h
    · by_contra h'
      exact hzero (Or.inl ⟨not_lt.mp h', le_trans ht0 h.2⟩)
    · by_contra h'
      exact hzero (Or.inr ⟨h.1.trans (le_trans h.2 (not_lt.mp h')),
        le_trans ht0 h.2⟩)
  have hry0 : 0 < ry := by
    rcases hbetween with h | h
    · by_contra h'
      exact hzero (Or.inl ⟨h.1.trans (le_trans h.2 (not_lt.mp h')),
        le_trans ht0 h.2⟩)
    · by_contra h'
      exact hzero (Or.inr ⟨not_lt.mp h', le_trans ht0 h.2⟩)
  have hrx1 : rx < 1 := by
    rcases hbetween with h | h
    · by_contra h'
      exact hone (Or.inl ⟨le_trans h.1 ht1,
        le_trans (not_lt.mp h') (le_trans h.1 h.2)⟩)
    · by_contra h'
      exact hone (Or.inr ⟨le_trans h.1 ht1, not_lt.mp h'⟩)
  have hry1 : ry < 1 := by
    rcases hbetween with h | h
    · by_contra h'
      exact hone (Or.inl ⟨le_trans h.1 ht1, not_lt.mp h'⟩)
    · by_contra h'
      exact hone (Or.inr ⟨le_trans h.1 ht1,
        le_trans (not_lt.mp h') (le_trans h.1 h.2)⟩)
  left
  intro z hz
  rw [segment_eq_image'] at hz
  obtain ⟨r, hr, hzr⟩ := hz
  rw [openSegment_eq_image']
  refine ⟨rx + r * (ry - rx), ?_, ?_⟩
  · constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hr.2) (le_of_lt hrx0),
        mul_nonneg hr.1 (le_of_lt hry0)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr (le_of_lt hrx1)),
        mul_nonneg hr.1 (sub_nonneg.mpr (le_of_lt hry1))]
  · rw [hrx, hry] at hzr
    symm
    change z = p + (rx + r * (ry - rx)) • (q - p)
    calc
      z = (p + rx • (q - p)) + r • ((p + ry • (q - p)) -
        (p + rx • (q - p))) := hzr.symm
      _ = p + (rx + r * (ry - rx)) • (q - p) := by module

/-- Step 2 of the blueprint proof of `whole_side_ports_step2_length_bound`: among the fine
outer sides overlapping the parent side positively, at most two are not strictly inside it
(one may cross or touch each endpoint). -/
private lemma whole_side_ports_step2_length_bound_step2_omitted_count
    (τ : Substitution P) (G : GroupedFamily P) (m : ℕ) (A : G.P'.Form) (a : Fin (G.P'.disk A).n) :
    {e ∈ fineOuterSides τ G m A | OverlapPos (segment ℝ e.1 e.2)
        (segment ℝ (parentSide τ G m A a).1 (parentSide τ G m A a).2)}.ncard ≤
      (sidesInside τ G m A a).ncard + 2 := by
  let p := (parentSide τ G m A a).1
  let q := (parentSide τ G m A a).2
  let S := {e ∈ fineOuterSides τ G m A | OverlapPos (segment ℝ e.1 e.2) (segment ℝ p q)}
  let I := sidesInside τ G m A a
  let L := {e ∈ S | p ∈ segment ℝ e.1 e.2}
  let R := {e ∈ S | q ∈ segment ℝ e.1 e.2}
  have hpq : p ≠ q := omitted_count_parent_endpoints_ne τ G m A a
  have hSfin : S.Finite := by
    simpa [S, p, q] using
      (whole_side_ports_step2_length_bound_step1_all_edges_bound_step3_finite τ G m A a)
  have hIfin : I.Finite := by
    apply hSfin.subset
    rintro e ⟨hefine, heopen⟩
    have hefine' := hefine
    obtain ⟨B, hB, i, heq, -⟩ := hefine'
    refine ⟨hefine, ?_⟩
    refine ⟨e.1, e.2, ?_, ?_⟩
    · rw [heq]
      exact omitted_count_tile_vertex_ne_next B i
    · intro z hz
      exact ⟨hz, openSegment_subset_segment ℝ _ _ (heopen hz)⟩
  have hLfin : L.Finite := hSfin.sep _
  have hRfin : R.Finite := hSfin.sep _
  have hL : L.ncard ≤ 1 := by
    rw [Set.ncard_le_one hLfin]
    intro e he f hf
    exact whole_side_ports_step2_length_bound_step2_omitted_count_edge_unique_at_endpoint
      τ G m A p q e f hpq he.1.1 hf.1.1 he.1.2 hf.1.2 he.2 hf.2
  have hR : R.ncard ≤ 1 := by
    rw [Set.ncard_le_one hRfin]
    intro e he f hf
    apply whole_side_ports_step2_length_bound_step2_omitted_count_edge_unique_at_endpoint
      τ G m A q p e f hpq.symm he.1.1 hf.1.1
    · simpa [segment_symm] using he.1.2
    · simpa [segment_symm] using hf.1.2
    · exact he.2
    · exact hf.2
  have hsub : S ⊆ I ∪ (L ∪ R) := by
    intro e he
    rcases whole_side_ports_step2_length_bound_step2_omitted_count_overlap_inside_or_endpoint
        hpq he.2 with heopen | hzp | hzq
    · exact Or.inl ⟨he.1, heopen⟩
    · exact Or.inr (Or.inl ⟨he, hzp⟩)
    · exact Or.inr (Or.inr ⟨he, hzq⟩)
  have hUnionFin : (I ∪ (L ∪ R)).Finite := hIfin.union (hLfin.union hRfin)
  change S.ncard ≤ I.ncard + 2
  calc
    S.ncard ≤ (I ∪ (L ∪ R)).ncard := Set.ncard_le_ncard hsub hUnionFin
    _ ≤ I.ncard + (L ∪ R).ncard := Set.ncard_union_le I (L ∪ R)
    _ ≤ I.ncard + (L.ncard + R.ncard) :=
      Nat.add_le_add_left (Set.ncard_union_le L R) I.ncard
    _ ≤ I.ncard + 2 := by omega

/-- Step 2 of the blueprint proof of `whole_side_ports`: the length of the parent
side is bounded by the number of inside edges times D plus the omitted length 2D. -/
private lemma whole_side_ports_step2_length_bound (M : MeshConstants P) (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) :
    dist (parentSide τ G m A a).1 (parentSide τ G m A a).2 ≤
      ((sidesInside τ G m A a).ncard : ℝ) * M.D + 2 * M.D := by
  have h_fin : (sidesInside τ G m A a).Finite :=
    (whole_side_ports_step2_length_bound_step1_all_edges_bound_step3_finite_aux2 τ G m A).subset
      fun _ he => he.1
  have h1 := whole_side_ports_step2_length_bound_step1_all_edges_bound_step1_sum_lengths
    τ G M m A a h_fin
  have h2 : ∑ e ∈ h_fin.toFinset, dist e.1 e.2 ≤ ∑ _e ∈ h_fin.toFinset, M.D :=
    Finset.sum_le_sum fun e he =>
      whole_side_ports_step2_length_bound_step1_all_edges_bound_step2_edge_bound τ G M m A e
        (h_fin.mem_toFinset.mp he).1
  rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ h_fin] at h2
  linarith

/-- `lem:whole-ports` (count): the list of whole fine sides strictly inside
`s a` has at least `(s|a| - 2D)/D` entries. -/
theorem whole_side_ports (M : MeshConstants P) (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) :
    ((τ.θ ^ m) * dist ((G.P'.disk A).vertex a) ((G.P'.disk A).vertex (finRotate _ a)) -
        2 * M.D) / M.D ≤ ((sidesInside τ G m A a).ncard : ℝ) := by
  have h1 := whole_side_ports_step1_parent_length τ G m A a
  have h2 := whole_side_ports_step2_length_bound τ G M m A a
  have hd : 0 < M.D := M.D_pos
  rw [div_le_iff₀ hd, sub_le_iff_le_add]
  linarith

/-- Step 1 of the blueprint proof of `whole_side_ports_distinct_step1_growth`: for large `m`,
the algebraic lower bound is at least 6. -/
private lemma whole_side_ports_distinct_step1_growth_step1_uniform_bound (M : MeshConstants P) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (A : G.P'.Form) (a : Fin (G.P'.disk A).n),
      (6 : ℝ) ≤ ((τ.θ ^ m) * dist ((G.P'.disk A).vertex a) ((G.P'.disk A).vertex (finRotate _ a)) -
        2 * M.D) / M.D := by
  have hpow : Filter.Tendsto (fun m : ℕ => τ.θ ^ m) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt τ.one_lt
  obtain ⟨M'⟩ := MeshConstants.nonempty G.P'
  have hlim : Filter.Tendsto (fun m : ℕ => (τ.θ ^ m) * M'.γ) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const M'.γ_pos hpow
  obtain ⟨m₀, hm₀⟩ := (Filter.tendsto_atTop_atTop.mp hlim) (8 * M.D)
  use m₀
  intro m hm A a
  have hm1 : 8 * M.D ≤ (τ.θ ^ m) * M'.γ := hm₀ m hm
  have hside := M'.side_ge A a
  have hm2 : (τ.θ ^ m) * M'.γ ≤
      (τ.θ ^ m) * dist ((G.P'.disk A).vertex a)
        ((G.P'.disk A).vertex (finRotate _ a)) := by
    apply mul_le_mul_of_nonneg_left hside
    exact pow_nonneg (le_of_lt (lt_trans zero_lt_one τ.one_lt)) m
  have hbound : 8 * M.D ≤
      (τ.θ ^ m) * dist ((G.P'.disk A).vertex a)
        ((G.P'.disk A).vertex (finRotate _ a)) := hm1.trans hm2
  rw [le_div_iff₀ M.D_pos]
  linarith

/-- Step 1 of the blueprint proof of `whole_side_ports_distinct`: for large `m`, the number of
fine sides strictly inside `s a` is at least 6. -/
private lemma whole_side_ports_distinct_step1_growth :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (A : G.P'.Form) (a : Fin (G.P'.disk A).n),
      6 ≤ (sidesInside τ G m A a).ncard := by
  obtain ⟨M⟩ := MeshConstants.nonempty P
  obtain ⟨m₀, hm₀⟩ := whole_side_ports_distinct_step1_growth_step1_uniform_bound (τ := τ) (G := G) M
  use m₀
  intro m hm A a
  have h1 : (6 : ℝ) ≤ _ := hm₀ m hm A a
  have h2 := whole_side_ports (τ := τ) (G := G) M m A a
  have h3 : (6 : ℝ) ≤ ((sidesInside τ G m A a).ncard : ℝ) := le_trans h1 h2
  exact_mod_cast h3

/-- Step 2 of the blueprint proof of `whole_side_ports_distinct`: if `L ≥ 6`, then `portIndex L`
is injective on `Fin 5` and its values are in `1..L`. -/
private lemma whole_side_ports_distinct_step2_index {L : ℕ} (h : 6 ≤ L) :
    Function.Injective (portIndex L) ∧
      ∀ r : Fin 5, 1 ≤ portIndex L r ∧ portIndex L r ≤ L := by
  constructor
  · intro a b hab
    unfold portIndex at hab
    fin_cases a <;> fin_cases b <;> (try rfl) <;> (dsimp at hab; omega)
  · intro r
    unfold portIndex
    fin_cases r <;> (dsimp; omega)

private lemma whole_side_ports_distinct_step3_rank_step1_finite_decomposeTile
    (τ : Substitution P) (A : PlacedTile P) : (τ.decomposeTile A).Finite := by
  unfold Substitution.decomposeTile
  apply Set.Finite.image
  exact (τ.rule A.form).finite

private lemma whole_side_ports_distinct_step3_rank_step1_finite_decompose
    (τ : Substitution P) (S : Set (PlacedTile P)) (h : S.Finite) :
    (τ.decompose S).Finite := by
  unfold Substitution.decompose
  apply Set.Finite.biUnion h
  intro A _
  exact whole_side_ports_distinct_step3_rank_step1_finite_decomposeTile τ A

private lemma whole_side_ports_distinct_step3_rank_step1_finite_decomposeIter
    (τ : Substitution P) (n : ℕ) (S : Set (PlacedTile P)) (h : S.Finite) :
    (τ.decomposeIter n S).Finite := by
  induction' n with n ih
  · exact h
  · unfold Substitution.decomposeIter
    dsimp
    exact whole_side_ports_distinct_step3_rank_step1_finite_decompose
      τ (τ.decomposeIter n S) ih

/-- Step 1 of the blueprint proof of `whole_side_ports_distinct_step3_rank`: the set of inside sides is finite. -/
private lemma whole_side_ports_distinct_step3_rank_step1_finite (τ : Substitution P)
    (G : GroupedFamily P) (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) : (sidesInside τ G m A a).Finite := by
  have _ := a
  have h1 : sidesInside τ G m A a ⊆ fineOuterSides τ G m A := by
    intro e he
    unfold sidesInside at he
    exact he.1
  apply Set.Finite.subset _ h1
  unfold fineOuterSides
  have h_tiles : (fineTiles τ G m A).Finite := by
    unfold fineTiles
    apply whole_side_ports_distinct_step3_rank_step1_finite_decomposeIter
    exact (G.dissect A).finite
  have h2 :
      {e | ∃ B ∈ fineTiles τ G m A, ∃ i : Fin (P.disk B.form).n,
        e = (B.vertex i, B.vertex (finRotate _ i)) ∧
          segment ℝ e.1 e.2 ⊆ frontier (parentRegion τ G m A)} ⊆
        ⋃ B ∈ fineTiles τ G m A,
          {e | ∃ i : Fin (P.disk B.form).n,
            e = (B.vertex i, B.vertex (finRotate _ i))} := by
    intro e he
    simp only [mem_iUnion, mem_setOf_eq]
    rcases he with ⟨B, hB, i, heq, _⟩
    use B, hB, i
  apply Set.Finite.subset _ h2
  apply Set.Finite.biUnion h_tiles
  intro B _
  have h3 :
      {e | ∃ i : Fin (P.disk B.form).n,
        e = (B.vertex i, B.vertex (finRotate _ i))} =
        (fun i => (B.vertex i, B.vertex (finRotate _ i))) '' univ := by
    ext e
    simp only [mem_setOf_eq, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      use i, hi.symm
    · rintro ⟨i, hi⟩
      use i, hi.symm
  rw [h3]
  apply Set.Finite.image
  exact finite_univ

/-- Step 2 of the blueprint proof of `whole_side_ports_distinct_step3_rank_step2_inj`: the interiors of distinct inside sides are disjoint. -/
private lemma whole_side_ports_distinct_step3_rank_step2_inj_step1_disjoint (τ : Substitution P)
    (G : GroupedFamily P) (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) (e1 e2 : Pt × Pt)
    (h1 : e1 ∈ sidesInside τ G m A a) (h2 : e2 ∈ sidesInside τ G m A a)
    (hne : e1 ≠ e2) : Disjoint (openSegment ℝ e1.1 e1.2) (openSegment ℝ e2.1 e2.2) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  exfalso
  apply hne
  have hsub1 : segment ℝ e1.1 e1.2 ⊆
      segment ℝ (parentSide τ G m A a).1 (parentSide τ G m A a).2 :=
    (h1.2.trans (openSegment_subset_segment ℝ _ _))
  have hsub2 : segment ℝ e2.1 e2.2 ⊆
      segment ℝ (parentSide τ G m A a).1 (parentSide τ G m A a).2 :=
    (h2.2.trans (openSegment_subset_segment ℝ _ _))
  obtain ⟨B, hB, i, heq1, hfront1⟩ := h1.1
  obtain ⟨C, hC, j, heq2, hfront2⟩ := h2.1
  subst e1
  subst e2
  have hBi := omitted_count_tile_vertex_ne_next B i
  have hCj := omitted_count_tile_vertex_ne_next C j
  have hBC : B = C := by
    by_contra hBC
    have hdisj : Disjoint (interior B.carrier) (interior C.carrier) :=
      omitted_count_fineTiles_disjoint τ G m A hB hC hBC
    have hzBi : z ∈ B.side i := by
      rw [omitted_count_tile_side_eq]
      exact openSegment_subset_segment ℝ _ _ hz1
    have hzCj : z ∈ C.side j := by
      rw [omitted_count_tile_side_eq]
      exact openSegment_subset_segment ℝ _ _ hz2
    have hcol : Collinear ℝ ({B.vertex i, B.vertex (finRotate _ i),
        C.vertex j, C.vertex (finRotate _ j)} : Set Pt) :=
      omitted_count_collinear_of_segment_subset hsub1 hsub2
    have hzBi₁ : z ≠ B.vertex i := omitted_count_open_ne_left hBi hz1
    have hzBi₂ : z ≠ B.vertex (finRotate _ i) := omitted_count_open_ne_right hBi hz1
    have hzCj₁ : z ≠ C.vertex j := omitted_count_open_ne_left hCj hz2
    have hzCj₂ : z ≠ C.vertex (finRotate _ j) := omitted_count_open_ne_right hCj hz2
    let δ := min (dist z (B.vertex i))
      (min (dist z (B.vertex (finRotate _ i)))
        (min (dist z (C.vertex j)) (dist z (C.vertex (finRotate _ j)))))
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (dist_pos.mpr hzBi₁)
        (lt_min (dist_pos.mpr hzBi₂) (lt_min (dist_pos.mpr hzCj₁) (dist_pos.mpr hzCj₂)))
    have hhalf : (2 * δ) / 2 = δ := by ring
    obtain ⟨η, hη, hball⟩ :=
      Crowns.trimmedEdgeTwoTileBall (P := P) (d := 2 * δ) (by positivity)
    have hcover : Metric.ball z η ⊆ B.carrier ∪ C.carrier := by
      apply hball B C hdisj i j z hzBi hzCj hcol
      all_goals rw [hhalf]
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
      · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hballRegion : Metric.ball z η ⊆ parentRegion τ G m A := by
      intro x hx
      rw [parentRegion, ← omitted_count_fineTiles_support τ G]
      rcases hcover hx with hxB | hxC
      · exact Set.mem_iUnion₂.2 ⟨B, hB, hxB⟩
      · exact Set.mem_iUnion₂.2 ⟨C, hC, hxC⟩
    have hzint : z ∈ interior (parentRegion τ G m A) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (Metric.ball_mem_nhds z hη) hballRegion
    exact (hfront1 (openSegment_subset_segment ℝ _ _ hz1)).2 hzint
  subst C
  have hij := omitted_count_same_tile_side_index B i j z hz1
    (openSegment_subset_segment ℝ _ _ hz2)
  subst j
  rfl

private lemma whole_side_ports_distinct_key_coefficient_ne (v : Pt) (hv : v ≠ 0) :
    canonDir v 0 * v 0 + canonDir v 1 * v 1 ≠ 0 := by
  have hsquares : v 0 * v 0 + v 1 * v 1 ≠ 0 := by
    intro h
    have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    apply hv
    ext i
    fin_cases i <;> assumption
  unfold canonDir
  split_ifs
  · simp only [PiLp.smul_apply, smul_eq_mul]
    rw [show ‖v‖⁻¹ * v 0 * v 0 + ‖v‖⁻¹ * v 1 * v 1 =
        ‖v‖⁻¹ * (v 0 * v 0 + v 1 * v 1) by ring]
    exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hv)) hsquares
  · simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
    rw [show -(‖v‖⁻¹ * v 0) * v 0 + -(‖v‖⁻¹ * v 1) * v 1 =
        -‖v‖⁻¹ * (v 0 * v 0 + v 1 * v 1) by ring]
    exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hv))) hsquares

private lemma whole_side_ports_distinct_key_injective_on_segment {p q z1 z2 : Pt}
    (hpq : p ≠ q) (hz1 : z1 ∈ segment ℝ p q) (hz2 : z2 ∈ segment ℝ p q)
    (hcoord : coord 0 (canonDir (q - p)) z1 = coord 0 (canonDir (q - p)) z2) :
    z1 = z2 := by
  rw [segment_eq_image'] at hz1 hz2
  obtain ⟨t1, -, rfl⟩ := hz1
  obtain ⟨t2, -, rfl⟩ := hz2
  have hv : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hcoef := whole_side_ports_distinct_key_coefficient_ne (q - p) hv
  have haffine (t : ℝ) :
      coord 0 (canonDir (q - p)) (p + t • (q - p)) =
        coord 0 (canonDir (q - p)) p +
          t * (canonDir (q - p) 0 * (q - p) 0 +
            canonDir (q - p) 1 * (q - p) 1) := by
    unfold coord
    simp only [PiLp.zero_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      sub_zero, smul_eq_mul]
    ring
  have ht : t1 = t2 := by
    rw [haffine, haffine] at hcoord
    exact mul_right_cancel₀ hcoef (add_left_cancel hcoord)
  rw [ht]

/-- Step 2 of the blueprint proof of `whole_side_ports_distinct_step3_rank_step2_inj`: sides with disjoint interiors have distinct sideKeys. -/
private lemma whole_side_ports_distinct_step3_rank_step2_inj_step2_key_ne (τ : Substitution P)
    (G : GroupedFamily P) (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) (e1 e2 : Pt × Pt)
    (h1 : e1 ∈ sidesInside τ G m A a) (h2 : e2 ∈ sidesInside τ G m A a)
    (hdisj : Disjoint (openSegment ℝ e1.1 e1.2) (openSegment ℝ e2.1 e2.2)) :
    sideKey (parentDir τ G m A a) e1 ≠ sideKey (parentDir τ G m A a) e2 := by
  intro hkey
  let z1 : Pt := (1 / 2 : ℝ) • (e1.1 + e1.2)
  let z2 : Pt := (1 / 2 : ℝ) • (e2.1 + e2.2)
  have hz1seg : z1 ∈ segment ℝ e1.1 e1.2 := by
    rw [segment_eq_image']
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    dsimp [z1]
    module
  have hz2seg : z2 ∈ segment ℝ e2.1 e2.2 := by
    rw [segment_eq_image']
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    dsimp [z2]
    module
  have hz1parent : z1 ∈ segment ℝ (parentSide τ G m A a).1
      (parentSide τ G m A a).2 :=
    (openSegment_subset_segment ℝ _ _) (h1.2 hz1seg)
  have hz2parent : z2 ∈ segment ℝ (parentSide τ G m A a).1
      (parentSide τ G m A a).2 :=
    (openSegment_subset_segment ℝ _ _) (h2.2 hz2seg)
  have hcoord : coord 0 (parentDir τ G m A a) z1 =
      coord 0 (parentDir τ G m A a) z2 := by
    simpa [sideKey, z1, z2] using hkey
  have hz : z1 = z2 := by
    apply whole_side_ports_distinct_key_injective_on_segment
      (omitted_count_parent_endpoints_ne τ G m A a) hz1parent hz2parent
    simpa [parentDir] using hcoord
  have hz1open : z1 ∈ openSegment ℝ e1.1 e1.2 := by
    rw [openSegment_eq_image']
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    dsimp [z1]
    module
  have hz2open : z2 ∈ openSegment ℝ e2.1 e2.2 := by
    rw [openSegment_eq_image']
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    dsimp [z2]
    module
  exact Set.disjoint_left.1 hdisj hz1open (hz ▸ hz2open)

/-- Step 2 of the blueprint proof of `whole_side_ports_distinct_step3_rank`: `sideKey` is injective on the inside sides. -/
private lemma whole_side_ports_distinct_step3_rank_step2_inj (τ : Substitution P)
    (G : GroupedFamily P) (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) : (sidesInside τ G m A a).InjOn (sideKey (parentDir τ G m A a)) := by
  intro e1 h1 e2 h2 heq
  by_contra hne
  have hdisj := whole_side_ports_distinct_step3_rank_step2_inj_step1_disjoint τ G m A a e1 e2 h1 h2 hne
  have hkey := whole_side_ports_distinct_step3_rank_step2_inj_step2_key_ne τ G m A a e1 e2 h1 h2 hdisj
  exact hkey heq

/-- Helper for `whole_side_ports_distinct_step3_rank_step3_exists_step1_sorted_list`: strong
induction on the cardinality of `X`, repeatedly peeling off the element of least `sideKey`. -/
private lemma whole_side_ports_distinct_step3_rank_step3_exists_step1_sorted_list_aux1 :
    ∀ n : ℕ, ∀ X : Set (Pt × Pt), X.Finite → X.ncard = n → ∀ u : Pt,
      X.InjOn (sideKey u) →
      ∃ l : List (Pt × Pt), l.length = X.ncard ∧ (∀ x, x ∈ l ↔ x ∈ X) ∧
        l.Pairwise (fun e1 e2 => sideKey u e1 < sideKey u e2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hXfin hXcard u hInj
    rcases X.eq_empty_or_nonempty with rfl | hXne
    · exact ⟨[], by simp, by simp, List.Pairwise.nil⟩
    · obtain ⟨a, haX, hamin⟩ := Set.exists_min_image X (sideKey u) hXfin hXne
      have hX'card : (X \ {a}).ncard = X.ncard - 1 := Set.ncard_diff_singleton_of_mem haX
      have hcardpos : 0 < X.ncard := (Set.ncard_pos hXfin).mpr hXne
      have hlt : X.ncard - 1 < n := by omega
      obtain ⟨l', hl'len, hl'mem, hl'pw⟩ :=
        ih (X.ncard - 1) hlt (X \ {a}) (hXfin.subset Set.diff_subset) hX'card u
          (hInj.mono Set.diff_subset)
      refine ⟨a :: l', ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro x
        rw [List.mem_cons]
        constructor
        · rintro (rfl | hx)
          · exact haX
          · exact ((hl'mem x).mp hx).1
        · intro hx
          rcases eq_or_ne x a with rfl | hne
          · exact Or.inl rfl
          · exact Or.inr ((hl'mem x).mpr ⟨hx, hne⟩)
      · rw [List.pairwise_cons]
        refine ⟨fun b hb => ?_, hl'pw⟩
        have hbX' : b ∈ X \ {a} := (hl'mem b).mp hb
        have hba : b ≠ a := by simpa using hbX'.2
        have hle : sideKey u a ≤ sideKey u b := hamin b hbX'.1
        rcases hle.lt_or_eq with hlt' | heq
        · exact hlt'
        · exact absurd (hInj haX hbX'.1 heq) hba.symm

/-- Step 1 of the blueprint proof of `whole_side_ports_distinct_step3_rank_step3_exists`: construct a strictly sorted list of elements of `X`. -/
private lemma whole_side_ports_distinct_step3_rank_step3_exists_step1_sorted_list
    (X : Set (Pt × Pt)) (h_fin : X.Finite) (u : Pt) (h_inj : X.InjOn (sideKey u)) :
    ∃ l : List (Pt × Pt), l.length = X.ncard ∧ (∀ x, x ∈ l ↔ x ∈ X) ∧ l.Pairwise (fun e1 e2 => sideKey u e1 < sideKey u e2) :=
  whole_side_ports_distinct_step3_rank_step3_exists_step1_sorted_list_aux1 X.ncard X h_fin rfl u
    h_inj

/-- Step 2 of the blueprint proof of `whole_side_ports_distinct_step3_rank_step3_exists`:
the set of elements in `X` with strictly smaller sideKey than the k-th element has size k-1. -/
private lemma whole_side_ports_distinct_step3_rank_step3_exists_step2_rank (X : Set (Pt × Pt)) (u : Pt) (l : List (Pt × Pt))
    (hl_mem : ∀ x, x ∈ l ↔ x ∈ X) (hl_pw : l.Pairwise (fun e1 e2 => sideKey u e1 < sideKey u e2))
    (k : ℕ) (hk : k - 1 < l.length) :
    {e' ∈ X | sideKey u e' < sideKey u (l.get ⟨k - 1, hk⟩)}.ncard = k - 1 := by
  let n := k - 1
  let z := l.get ⟨n, hk⟩
  have hnodup : l.Nodup := (List.nodup_iff_pairwise_ne).2 (hl_pw.imp fun h hab =>
    (ne_of_lt h) (congrArg (sideKey u) hab))
  have hmem_take : ∀ x, x ∈ l.take n → sideKey u x < sideKey u z := by
    intro x hx
    have hx' : x ∈ l := List.mem_of_mem_take hx
    obtain ⟨i, hxi⟩ := List.get_of_mem hx'
    have hidx : List.idxOf x l < n := (List.mem_take_iff_idxOf_lt hx').mp hx
    rw [← hxi, List.get_idxOf hnodup] at hidx
    rw [← hxi]
    exact List.pairwise_iff_get.1 hl_pw i ⟨n, hk⟩ (by simpa using hidx)
  have hset : {e' ∈ X | sideKey u e' < sideKey u z} = {x | x ∈ l.take n} := by
    ext x
    constructor
    · intro hx
      have hxl : x ∈ l := (hl_mem x).2 hx.1
      obtain ⟨i, hxi⟩ := List.get_of_mem hxl
      have hidx : List.idxOf x l = i := by
        rw [← hxi, List.get_idxOf hnodup]
      have hin : i < n := by
        by_contra hnot
        have hcases : n ≤ i := Nat.le_of_not_gt hnot
        rcases hcases.eq_or_lt with heq | hni
        · have hieq : i = ⟨n, hk⟩ := Fin.ext heq.symm
          have hxz : sideKey u x = sideKey u z := by
            rw [← hxi, hieq]
          exact (lt_irrefl _ (hxz ▸ hx.2))
        · have hzx := List.pairwise_iff_get.1 hl_pw ⟨n, hk⟩ i hni
          have hzx' : sideKey u z < sideKey u x := by
            change sideKey u (l.get ⟨n, hk⟩) < sideKey u x
            rw [hxi] at hzx
            exact hzx
          exact (not_lt_of_ge (le_of_lt hzx')) hx.2
      change x ∈ l.take n
      rw [List.mem_take_iff_idxOf_lt hxl, hidx]
      exact hin
    · intro hx
      exact ⟨(hl_mem x).1 (List.mem_of_mem_take hx), hmem_take x hx⟩
  have hcard : {x | x ∈ l.take n}.ncard = n := by
    apply Set.ncard_eq_of_bijective
      (fun i hi => l.get ⟨i, lt_of_lt_of_le hi (Nat.le_of_lt hk)⟩)
    · intro x hx
      have hxl : x ∈ l := List.mem_of_mem_take hx
      obtain ⟨i, hxi⟩ := List.get_of_mem hxl
      have hidx : List.idxOf x l = i := by
        rw [← hxi, List.get_idxOf hnodup]
      have hin : i < n := by
        rw [← hidx]
        exact (List.mem_take_iff_idxOf_lt hxl).mp hx
      refine ⟨i, hin, ?_⟩
      simpa using hxi
    · intro i hi
      change l.get ⟨i, lt_of_lt_of_le hi (Nat.le_of_lt hk)⟩ ∈ l.take n
      rw [List.mem_take_iff_idxOf_lt (List.get_mem l _), List.get_idxOf hnodup]
      exact hi
    · intro i j hi hj hij
      have hfin : (⟨i, lt_of_lt_of_le hi (Nat.le_of_lt hk)⟩ : Fin l.length) =
          ⟨j, lt_of_lt_of_le hj (Nat.le_of_lt hk)⟩ :=
        (List.nodup_iff_injective_get.mp hnodup) hij
      exact congrArg Fin.val hfin
  rw [hset]
  simpa [n] using hcard

/-- Step 3 of the blueprint proof of `whole_side_ports_distinct_step3_rank`: an abstract lemma showing that any rank is attained. -/
private lemma whole_side_ports_distinct_step3_rank_step3_exists (X : Set (Pt × Pt))
    (h_fin : X.Finite) (u : Pt) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ X.ncard)
    (h_inj : X.InjOn (sideKey u)) :
    ∃ e ∈ X, rankIn X u e = k := by
  obtain ⟨l, hl_len, hl_mem, hl_pw⟩ := whole_side_ports_distinct_step3_rank_step3_exists_step1_sorted_list X h_fin u h_inj
  have hk_lt : k - 1 < l.length := by omega
  use l.get ⟨k - 1, hk_lt⟩
  constructor
  · rw [← hl_mem]
    exact List.get_mem _ _
  · have h_rank : rankIn X u (l.get ⟨k - 1, hk_lt⟩) = {e' ∈ X | sideKey u e' < sideKey u (l.get ⟨k - 1, hk_lt⟩)}.ncard + 1 := rfl
    rw [h_rank]
    rw [whole_side_ports_distinct_step3_rank_step3_exists_step2_rank X u l hl_mem hl_pw k hk_lt]
    omega

/-- Step 3 of the blueprint proof of `whole_side_ports_distinct`: every rank from 1 to `L`
is attained by some fine side. -/
private lemma whole_side_ports_distinct_step3_rank (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ (sidesInside τ G m A a).ncard) :
    ∃ e ∈ sidesInside τ G m A a, rankIn (sidesInside τ G m A a) (parentDir τ G m A a) e = k := by
  exact whole_side_ports_distinct_step3_rank_step3_exists (sidesInside τ G m A a)
    (whole_side_ports_distinct_step3_rank_step1_finite τ G m A a)
    (parentDir τ G m A a) k hk1 hk2
    (whole_side_ports_distinct_step3_rank_step2_inj τ G m A a)

/-- `lem:whole-ports` (distinctness): for large `s` the five quantile ports
exist and are distinct. -/
theorem whole_side_ports_distinct :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (A : G.P'.Form) (a : Fin (G.P'.disk A).n),
      Function.Injective (port τ G m A a) ∧
        ∀ r, port τ G m A a r ∈ sidesInside τ G m A a ∧
          rankIn (sidesInside τ G m A a) (parentDir τ G m A a) (port τ G m A a r) =
            portIndex (sidesInside τ G m A a).ncard r := by
  obtain ⟨m₀, hm₀⟩ := whole_side_ports_distinct_step1_growth (τ := τ) (G := G)
  use m₀
  intro m hm A a
  have hL : 6 ≤ (sidesInside τ G m A a).ncard := hm₀ m hm A a
  have h2 := whole_side_ports_distinct_step2_index hL
  have H_exist : ∀ r, ∃ e ∈ sidesInside τ G m A a,
      rankIn (sidesInside τ G m A a) (parentDir τ G m A a) e =
        portIndex (sidesInside τ G m A a).ncard r := by
    intro r
    have h_bounds := h2.2 r
    exact whole_side_ports_distinct_step3_rank (τ := τ) (G := G) m A a
      (portIndex (sidesInside τ G m A a).ncard r) h_bounds.1 h_bounds.2
  have H_spec : ∀ r, port τ G m A a r ∈ sidesInside τ G m A a ∧
      rankIn (sidesInside τ G m A a) (parentDir τ G m A a) (port τ G m A a r) =
        portIndex (sidesInside τ G m A a).ncard r := by
    intro r
    have H_ex := H_exist r
    have H_eps := Classical.epsilon_spec H_ex
    exact H_eps
  refine ⟨?_, H_spec⟩
  intro r1 r2 hr
  have hr1 := H_spec r1
  have hr2 := H_spec r2
  rw [hr] at hr1
  have h_eq : portIndex (sidesInside τ G m A a).ncard r1 =
      portIndex (sidesInside τ G m A a).ncard r2 := by
    rw [←hr1.2, ←hr2.2]
  exact h2.1 h_eq


private lemma whole_side_ports_coincide_step1_parentDir_eq_step1_diff_step1_ends_aux1
    {a b x : Pt} : x ∈ segment ℝ a b ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = a + t • (b - a) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨t, h0, h1, rfl⟩
  · rintro ⟨t, h0, h1, rfl⟩; exact ⟨t, ⟨h0, h1⟩, rfl⟩

private lemma whole_side_ports_coincide_step1_parentDir_eq_step1_diff_step1_ends_aux2
    {u : Pt} (hu : u ≠ 0) {s t : ℝ} (h : s • u = t • u) : s = t :=
  smul_left_injective ℝ hu h

/-- Step 1 of the blueprint proof of `whole_side_ports_coincide_step1_parentDir_eq_step1_diff`:
equal closed segments have equal or swapped endpoints. -/
private lemma whole_side_ports_coincide_step1_parentDir_eq_step1_diff_step1_ends
    (a b c d : Pt) (h : segment ℝ a b = segment ℝ c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases hab : a = b
  · subst hab
    have hca : c ∈ segment ℝ a a := h ▸ left_mem_segment ℝ c d
    have hda : d ∈ segment ℝ a a := h ▸ right_mem_segment ℝ c d
    rw [segment_same] at hca hda
    exact Or.inl ⟨hca.symm, hda.symm⟩
  · have hc : c ∈ segment ℝ a b := h ▸ left_mem_segment ℝ c d
    have hd : d ∈ segment ℝ a b := h ▸ right_mem_segment ℝ c d
    have ha : a ∈ segment ℝ c d := h ▸ left_mem_segment ℝ a b
    have hb : b ∈ segment ℝ c d := h ▸ right_mem_segment ℝ a b
    rw [whole_side_ports_coincide_step1_parentDir_eq_step1_diff_step1_ends_aux1] at hc hd ha hb
    obtain ⟨s, hs0, hs1, rfl⟩ := hc
    obtain ⟨t, ht0, ht1, rfl⟩ := hd
    obtain ⟨α, ha0, ha1, hα⟩ := ha
    obtain ⟨β, hb0, hb1, hβ⟩ := hb
    have hu : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    have k1 : a + s • (b - a) + α • (a + t • (b - a) - (a + s • (b - a))) =
        a + (s + α * (t - s)) • (b - a) := by module
    have k2 : a + s • (b - a) + β • (a + t • (b - a) - (a + s • (b - a))) =
        a + (s + β * (t - s)) • (b - a) := by module
    rw [k1] at hα
    rw [k2] at hβ
    have e1 : (0 : ℝ) • (b - a) = (s + α * (t - s)) • (b - a) := by
      rw [zero_smul]; exact (add_eq_left.1 hα.symm).symm
    have e2 : (1 : ℝ) • (b - a) = (s + β * (t - s)) • (b - a) := by
      rw [one_smul]
      have : a + (b - a) = a + (s + β * (t - s)) • (b - a) := by rw [← hβ]; abel
      exact add_left_cancel this
    have f1 := whole_side_ports_coincide_step1_parentDir_eq_step1_diff_step1_ends_aux2 hu e1
    have f2 := whole_side_ports_coincide_step1_parentDir_eq_step1_diff_step1_ends_aux2 hu e2
    have key : (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
      have h3 : s * (1 - α) = 0 := by
        nlinarith [mul_nonneg hs0 (sub_nonneg.2 ha1), mul_nonneg ha0 ht0]
      have h4 : α * t = 0 := by
        nlinarith [mul_nonneg hs0 (sub_nonneg.2 ha1), mul_nonneg ha0 ht0]
      rcases mul_eq_zero.1 h3 with h3 | h3
      · subst h3
        have : β * t = 1 := by linarith
        left; refine ⟨rfl, ?_⟩; nlinarith
      · have hα1 : α = 1 := by linarith
        subst hα1
        have ht : t = 0 := by linarith
        subst ht
        right; refine ⟨?_, rfl⟩; nlinarith
    rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; constructor <;> simp
    · right; constructor <;> simp

/-- Step 1 of the blueprint proof of `whole_side_ports_coincide_step1_parentDir_eq`: if the placed
segments are equal, their vector differences are either equal or opposite. -/
private lemma whole_side_ports_coincide_step1_parentDir_eq_step1_diff (m : ℕ)
    (A A' : PlacedTile G.P') (a : Fin (G.P'.disk A.form).n) (a' : Fin (G.P'.disk A'.form).n)
    (hside : placedSeg ((τ.θ ^ m) • A.anchor) (parentSide τ G m A.form a) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (parentSide τ G m A'.form a')) :
    (parentSide τ G m A.form a).2 - (parentSide τ G m A.form a).1 =
      (parentSide τ G m A'.form a').2 - (parentSide τ G m A'.form a').1 ∨
    (parentSide τ G m A.form a).2 - (parentSide τ G m A.form a).1 =
      - ((parentSide τ G m A'.form a').2 - (parentSide τ G m A'.form a').1) := by
  simp only [placedSeg] at hside
  have h_ends := whole_side_ports_coincide_step1_parentDir_eq_step1_diff_step1_ends _ _ _ _ hside
  rcases h_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have e : (((τ.θ ^ m) • A.anchor) + (parentSide τ G m A.form a).2) -
        (((τ.θ ^ m) • A.anchor) + (parentSide τ G m A.form a).1) =
        (((τ.θ ^ m) • A'.anchor) + (parentSide τ G m A'.form a').2) -
        (((τ.θ ^ m) • A'.anchor) + (parentSide τ G m A'.form a').1) :=
      congrArg₂ HSub.hSub h2 h1
    simpa [add_sub_add_left_eq_sub] using e
  · right
    have e : (((τ.θ ^ m) • A.anchor) + (parentSide τ G m A.form a).2) -
        (((τ.θ ^ m) • A.anchor) + (parentSide τ G m A.form a).1) =
        (((τ.θ ^ m) • A'.anchor) + (parentSide τ G m A'.form a').1) -
        (((τ.θ ^ m) • A'.anchor) + (parentSide τ G m A'.form a').2) :=
      congrArg₂ HSub.hSub h2 h1
    have h_sub_neg : ((parentSide τ G m A'.form a').1) - ((parentSide τ G m A'.form a').2) =
        - (((parentSide τ G m A'.form a').2) - ((parentSide τ G m A'.form a').1)) := by abel
    simp [add_sub_add_left_eq_sub] at e
    rw [e, h_sub_neg]

/-- Step 2 of the blueprint proof of `whole_side_ports_coincide_step1_parentDir_eq`: the canonical
direction of two vectors is the same if one is equal to or the opposite of the other. -/
private lemma whole_side_ports_coincide_step1_parentDir_eq_step2_canonDir (v w : Pt)
    (h : v = w ∨ v = -w) : canonDir v = canonDir w := by
  rcases h with h | h
  · subst v
    rfl
  · subst v
    by_cases hv : 0 < w 0 ∨ (w 0 = 0 ∧ 0 < w 1)
    · unfold canonDir
      have hleft : ¬(0 < (-w) 0 ∨ ((-w) 0 = 0 ∧ 0 < (-w) 1)) := by
        intro hleft
        rcases hv with hv0 | ⟨hv0, hv1⟩
        · rcases hleft with hleft0 | ⟨hleft0, hleft1⟩
          · change 0 < -w 0 at hleft0
            linarith
          · change -w 0 = 0 at hleft0
            linarith
        · rcases hleft with hleft0 | ⟨hleft0, hleft1⟩
          · change 0 < -w 0 at hleft0
            linarith
          · change -w 0 = 0 at hleft0
            change 0 < -w 1 at hleft1
            linarith
      rw [if_neg hleft, if_pos hv, norm_neg, smul_neg]
      simp
    · by_cases hneg : 0 < (-w) 0 ∨ ((-w) 0 = 0 ∧ 0 < (-w) 1)
      · unfold canonDir
        rw [if_neg hv, if_pos hneg, norm_neg, smul_neg]
      · unfold canonDir
        rw [if_neg hv, if_neg hneg, norm_neg]
        have hw0 : w 0 = 0 := by
          by_contra hw0
          rcases lt_or_gt_of_ne hw0 with hw0 | hw0
          · have : 0 < (-w) 0 := by
              change 0 < -w 0
              linarith
            exact hneg (Or.inl this)
          · exact hv (Or.inl hw0)
        have hw1 : w 1 = 0 := by
          by_contra hw1
          rcases lt_or_gt_of_ne hw1 with hw1 | hw1
          · have : 0 < (-w) 1 := by
              change 0 < -w 1
              linarith
            have hz : (-w) 0 = 0 := by
              rw [PiLp.neg_apply, hw0, neg_zero]
            exact hneg (Or.inr ⟨hz, this⟩)
          · exact hv (Or.inr ⟨hw0, hw1⟩)
        have : w = 0 := by
          ext i
          fin_cases i
          · exact hw0
          · exact hw1
        rw [this]
        simp

/-- Step 1 of the blueprint proof of `whole_side_ports_coincide`: the global canonical direction
of the coincident parent sides is the same. -/
private lemma whole_side_ports_coincide_step1_parentDir_eq (m : ℕ)
    (A A' : PlacedTile G.P') (a : Fin (G.P'.disk A.form).n) (a' : Fin (G.P'.disk A'.form).n)
    (hside : placedSeg ((τ.θ ^ m) • A.anchor) (parentSide τ G m A.form a) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (parentSide τ G m A'.form a')) :
    parentDir τ G m A.form a = parentDir τ G m A'.form a' := by
  dsimp [parentDir]
  have h1 := whole_side_ports_coincide_step1_parentDir_eq_step1_diff τ G m A A' a a' hside
  exact whole_side_ports_coincide_step1_parentDir_eq_step2_canonDir
    ((parentSide τ G m A.form a).2 - (parentSide τ G m A.form a).1)
    ((parentSide τ G m A'.form a').2 - (parentSide τ G m A'.form a').1) h1

/- The next three facts isolate the three geometric steps needed for the
   pointwise existence-and-uniqueness statement. -/

/-- Step 1 of the blueprint proof of
`whole_side_ports_coincide_step2_sidesInside_bijection_step1_exists_unique`:
given a fixed fine side strictly inside a parent side, fine STS and schedule
alignment match it with a fine outer side of the other parent. -/
private lemma whole_side_ports_coincide_step2_sidesInside_bijection_step1_exists_unique_step1_matching_fine_side
    (m : ℕ) (T' : PlaneTiling G.P')
    (hfine : SideToSideSet (τ.decomposeIter m (G.scatter T'.tiles)))
    (halign : SchedulesAligned τ G m T')
    (A A' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles)
    (a : Fin (G.P'.disk A.form).n) (a' : Fin (G.P'.disk A'.form).n)
    (hside : placedSeg ((τ.θ ^ m) • A.anchor) (parentSide τ G m A.form a) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (parentSide τ G m A'.form a'))
    (e : Pt × Pt) (he : e ∈ sidesInside τ G m A.form a) :
    ∃ e' ∈ fineOuterSides τ G m A'.form,
      placedSeg ((τ.θ ^ m) • A.anchor) e =
        placedSeg ((τ.θ ^ m) • A'.anchor) e' := by
  have _ := halign
  by_cases hAA : A = A'
  · subst hAA
    exact ⟨e, he.1, rfl⟩
  · obtain ⟨⟨B, hB, i, rfl, hF⟩, hIn⟩ := he
    have he_ne : B.vertex i ≠ B.vertex (finRotate _ i) := omitted_count_tile_vertex_ne_next B i
    have hJ1 : segment ℝ (B.vertex i) (B.vertex (finRotate _ i)) ⊆
        frontier (parentRegion τ G m A.form) := hF
    have hJ2 : placedSeg ((τ.θ ^ m) • A.anchor) (B.vertex i, B.vertex (finRotate _ i)) ⊆
        frontier (((τ.θ ^ m) • A'.anchor) +ᵥ parentRegion τ G m A'.form) := by
      intro z hz
      have hz2 : z ∈ placedSeg ((τ.θ ^ m) • A.anchor) (parentSide τ G m A.form a) := by
        rw [fs1_placedSeg_eq] at hz ⊢
        obtain ⟨z0, hz0, rfl⟩ := hz
        exact ⟨z0, openSegment_subset_segment ℝ _ _ (hIn hz0), rfl⟩
      rw [hside] at hz2
      rw [fs1_placedSeg_eq] at hz2
      obtain ⟨z0, hz0, rfl⟩ := hz2
      have hfr : segment ℝ (parentSide τ G m A'.form a').1 (parentSide τ G m A'.form a').2 ⊆ frontier (parentRegion τ G m A'.form) :=
        fs1_layer_frontier τ G m A'.form .top (parentSide τ G m A'.form a') ⟨a', rfl⟩
      rw [fs1_frontier_vadd]
      exact ⟨z0, hfr hz0, rfl⟩
    have hJ : placedSeg ((τ.θ ^ m) • A.anchor) (B.vertex i, B.vertex (finRotate _ i)) ⊆
        frontier (((τ.θ ^ m) • A.anchor) +ᵥ parentRegion τ G m A.form) ∩
        frontier (((τ.θ ^ m) • A'.anchor) +ᵥ parentRegion τ G m A'.form) := by
      intro z hz
      refine ⟨?_, hJ2 hz⟩
      rw [fs1_placedSeg_eq] at hz
      rw [fs1_frontier_vadd]
      obtain ⟨z0, hz0, rfl⟩ := hz
      exact ⟨z0, hJ1 hz0, rfl⟩
    have he_pts : ((τ.θ ^ m) • A.anchor) + B.vertex i ≠ ((τ.θ ^ m) • A.anchor) + B.vertex (finRotate _ i) := by
      intro h
      apply he_ne
      exact add_left_cancel h
    have hcore := fs1_core τ G m T' hfine A A' hA hA' hAA
      (((τ.θ ^ m) • A.anchor) + B.vertex i) (((τ.θ ^ m) • A.anchor) + B.vertex (finRotate _ i)) he_pts hJ
    obtain ⟨e1, he1, e', he', heq_e1, u, v, huv, hsub_uv⟩ := hcore
    obtain ⟨B1, hB1, i1, rfl, hF1⟩ := he1
    have hov_seg : OverlapPos (segment ℝ (B.vertex i) (B.vertex (finRotate _ i)))
        (segment ℝ (B1.vertex i1) (B1.vertex (finRotate _ i1))) := by
      apply fs1_overlap_of_placed (w := ((τ.θ ^ m) • A.anchor))
        (p := (B.vertex i, B.vertex (finRotate _ i)))
        (q := (B1.vertex i1, B1.vertex (finRotate _ i1))) huv
      intro z hz
      have hz1 := (hsub_uv hz).1
      have hz2 := (hsub_uv hz).2
      exact ⟨hz1, hz2⟩
    have hov : OverlapPos (B.side i) (B1.side i1) := by
      obtain ⟨x0, y0, hxy0, hsub0⟩ := hov_seg
      refine ⟨x0, y0, hxy0, ?_⟩
      rw [omitted_count_tile_side_eq B i, omitted_count_tile_side_eq B1 i1]
      exact hsub0
    have hR : ∀ D ∈ fineTiles τ G m A.form, D.carrier ⊆ parentRegion τ G m A.form := by
      intro D hD x hx
      have := omitted_count_fineTiles_support τ G m A.form
      unfold parentRegion
      rw [← this]
      exact Set.mem_iUnion₂.2 ⟨D, hD, hx⟩
    have hfront : B.side i ⊆ frontier (parentRegion τ G m A.form) := by
      rw [omitted_count_tile_side_eq]
      exact hF
    have hB_eq_B1 := sa1_frontier_tiles_eq (fineTiles τ G m A.form)
      (omitted_count_fineTiles_disjoint τ G m A.form) (parentRegion τ G m A.form) hR hB hB1 i i1 hfront hov
    obtain ⟨tB, cB⟩ := B
    obtain ⟨tB1, cB1⟩ := B1
    injection hB_eq_B1 with ht hc
    subst ht hc
    have hov_symm : OverlapPos (PlacedTile.side { form := tB, anchor := cB } i1)
        (PlacedTile.side { form := tB, anchor := cB } i) := by
      obtain ⟨x0, y0, hxy0, hsub0⟩ := hov
      exact ⟨x0, y0, hxy0, fun z hz => ⟨(hsub0 hz).2, (hsub0 hz).1⟩⟩
    have hi_eq_i1 : i1 = i := sa1_same_tile_side { form := tB, anchor := cB } i1 i hov_symm
    subst hi_eq_i1
    exact ⟨e', he', heq_e1⟩

/-- Step 2 of the blueprint proof of
`whole_side_ports_coincide_step2_sidesInside_bijection_step1_exists_unique`:
strict containment in a parent side is transported through equal placed segments. -/
private lemma whole_side_ports_coincide_step2_sidesInside_bijection_step1_exists_unique_step2_transport_inside
    (m : ℕ) (A A' : PlacedTile G.P')
    (a : Fin (G.P'.disk A.form).n) (a' : Fin (G.P'.disk A'.form).n)
    (hside : placedSeg ((τ.θ ^ m) • A.anchor) (parentSide τ G m A.form a) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (parentSide τ G m A'.form a'))
    (e e' : Pt × Pt) (he : e ∈ sidesInside τ G m A.form a)
    (he' : e' ∈ fineOuterSides τ G m A'.form)
    (heq : placedSeg ((τ.θ ^ m) • A.anchor) e =
      placedSeg ((τ.θ ^ m) • A'.anchor) e') :
    e' ∈ sidesInside τ G m A'.form a' := by
  unfold sidesInside at he ⊢
  simp only [mem_setOf_eq] at he ⊢
  refine ⟨he', ?_⟩
  set va := (τ.θ ^ m) • A.anchor
  set vb := (τ.θ ^ m) • A'.anchor
  have hne : (parentSide τ G m A.form a).1 ≠ (parentSide τ G m A.form a).2 :=
    omitted_count_parent_endpoints_ne τ G m A.form a
  have hne_placed : va + (parentSide τ G m A.form a).1 ≠ va + (parentSide τ G m A.form a).2 := by
    intro h
    exact hne (add_left_cancel h)
  have hside2 : segment ℝ (va + (parentSide τ G m A.form a).1)
      (va + (parentSide τ G m A.form a).2) =
      segment ℝ (vb + (parentSide τ G m A'.form a').1)
      (vb + (parentSide τ G m A'.form a').2) := by
    simpa only [placedSeg] using hside
  have hends := sa1_ba_segment_endpoints hne_placed hside2
  
  have hopen : openSegment ℝ (va + (parentSide τ G m A.form a).1)
      (va + (parentSide τ G m A.form a).2) =
      openSegment ℝ (vb + (parentSide τ G m A'.form a').1)
      (vb + (parentSide τ G m A'.form a').2) := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, openSegment_symm]
  
  intro x hx
  have hx_mapped : vb +ᵥ x ∈ vb +ᵥ segment ℝ e'.1 e'.2 := by
    exact vadd_mem_vadd_set_iff.mpr hx
  
  have hvadd_e' : placedSeg vb e' = vb +ᵥ segment ℝ e'.1 e'.2 := fs1_placedSeg_eq vb e'
  have hvadd_e : placedSeg va e = va +ᵥ segment ℝ e.1 e.2 := fs1_placedSeg_eq va e
  
  have hx_eq : vb +ᵥ x ∈ placedSeg va e := by
    rw [← hvadd_e'] at hx_mapped
    rw [← heq] at hx_mapped
    exact hx_mapped
  
  rw [hvadd_e] at hx_eq
  have he2 := he.2
  
  have hincl : va +ᵥ segment ℝ e.1 e.2 ⊆
      va +ᵥ openSegment ℝ (parentSide τ G m A.form a).1 (parentSide τ G m A.form a).2 := by
    intro y hy
    rcases hy with ⟨y_orig, hy_orig, hy_eq⟩
    rw [← hy_eq]
    exact ⟨y_orig, he2 hy_orig, rfl⟩
    
  have hx_open : vb +ᵥ x ∈
      va +ᵥ openSegment ℝ (parentSide τ G m A.form a).1 (parentSide τ G m A.form a).2 :=
    hincl hx_eq
    
  have hvadd_open_a : va +ᵥ openSegment ℝ (parentSide τ G m A.form a).1
      (parentSide τ G m A.form a).2 =
      openSegment ℝ (va + (parentSide τ G m A.form a).1) (va + (parentSide τ G m A.form a).2) := by
    rw [← vadd_eq_add, ← vadd_eq_add, ← vadd_openSegment]
    
  have hvadd_open_b : vb +ᵥ openSegment ℝ (parentSide τ G m A'.form a').1
      (parentSide τ G m A'.form a').2 =
      openSegment ℝ (vb + (parentSide τ G m A'.form a').1) (vb + (parentSide τ G m A'.form a').2) := by
    rw [← vadd_eq_add, ← vadd_eq_add, ← vadd_openSegment]
    
  rw [hvadd_open_a] at hx_open
  rw [hopen] at hx_open
  rw [← hvadd_open_b] at hx_open
  exact (vadd_mem_vadd_set_iff (a := vb) (x := x)).mp hx_open

/-- Step 3 of the blueprint proof of
`whole_side_ports_coincide_step2_sidesInside_bijection_step1_exists_unique`:
on one parent, a translated physical segment determines an inside side uniquely. -/
private lemma whole_side_ports_coincide_step2_sidesInside_bijection_step1_exists_unique_step3_unique_same_anchor
    (m : ℕ) (A : PlacedTile G.P') (a : Fin (G.P'.disk A.form).n)
    (e₁ e₂ : sidesInside τ G m A.form a)
    (heq : placedSeg ((τ.θ ^ m) • A.anchor) (e₁ : Pt × Pt) =
      placedSeg ((τ.θ ^ m) • A.anchor) (e₂ : Pt × Pt)) :
    e₁ = e₂ := by
  apply Subtype.ext
  apply whole_side_ports_distinct_step3_rank_step2_inj τ G m A.form a e₁.2 e₂.2
  set v := (τ.θ ^ m) • A.anchor
  obtain ⟨B, -, i, he₁, -⟩ := e₁.2.1
  have hne : v + (e₁ : Pt × Pt).1 ≠ v + (e₁ : Pt × Pt).2 := by
    intro h
    apply omitted_count_tile_vertex_ne_next B i
    rw [he₁] at h
    exact add_left_cancel h
  have hsegments : segment ℝ (v + (e₁ : Pt × Pt).1) (v + (e₁ : Pt × Pt).2) =
      segment ℝ (v + (e₂ : Pt × Pt).1) (v + (e₂ : Pt × Pt).2) := by
    simpa only [placedSeg] using heq
  rcases sa1_ba_segment_endpoints hne hsegments with hends | hends
  · obtain ⟨h₁, h₂⟩ := hends
    have h₁' : (e₂ : Pt × Pt).1 = (e₁ : Pt × Pt).1 := add_left_cancel h₁
    have h₂' : (e₂ : Pt × Pt).2 = (e₁ : Pt × Pt).2 := add_left_cancel h₂
    simp only [sideKey]
    rw [h₁', h₂']
  · obtain ⟨h₁, h₂⟩ := hends
    have h₁' : (e₂ : Pt × Pt).1 = (e₁ : Pt × Pt).2 := add_left_cancel h₁
    have h₂' : (e₂ : Pt × Pt).2 = (e₁ : Pt × Pt).1 := add_left_cancel h₂
    simp only [sideKey]
    rw [h₁', h₂', add_comm]

/-- Step 2 of the blueprint proof of `whole_side_ports_coincide`: fine STS gives identical
whole-edge subdivision of their common support... -/
private lemma whole_side_ports_coincide_step2_sidesInside_bijection_step1_exists_unique
    (m : ℕ) (T' : PlaneTiling G.P')
    (hfine : SideToSideSet (τ.decomposeIter m (G.scatter T'.tiles)))
    (halign : SchedulesAligned τ G m T')
    (A A' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles)
    (a : Fin (G.P'.disk A.form).n) (a' : Fin (G.P'.disk A'.form).n)
    (hside : placedSeg ((τ.θ ^ m) • A.anchor) (parentSide τ G m A.form a) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (parentSide τ G m A'.form a')) :
    ∀ e : sidesInside τ G m A.form a, ∃! e' : sidesInside τ G m A'.form a',
      placedSeg ((τ.θ ^ m) • A.anchor) (e : Pt × Pt) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (e' : Pt × Pt) := by
  intro e
  obtain ⟨e', he', heq⟩ :=
whole_side_ports_coincide_step2_sidesInside_bijection_step1_exists_unique_step1_matching_fine_side
      τ G m T' hfine halign A A' hA hA' a a' hside e e.2
  have he'inside :=
    whole_side_ports_coincide_step2_sidesInside_bijection_step1_exists_unique_step2_transport_inside
      τ G m A A' a a' hside (e : Pt × Pt) e' e.2 he' heq
  refine ⟨⟨e', he'inside⟩, heq, ?_⟩
  intro y hy
  symm
  apply
whole_side_ports_coincide_step2_sidesInside_bijection_step1_exists_unique_step3_unique_same_anchor
    τ G m A' a' ⟨e', he'inside⟩ y
  exact heq.symm.trans hy

/-- Step 2 of the blueprint proof of `whole_side_ports_coincide`: fine STS gives identical
whole-edge subdivision of their common support... -/
private lemma whole_side_ports_coincide_step2_sidesInside_bijection_step2_exists_unique_rev
    (m : ℕ) (T' : PlaneTiling G.P')
    (hfine : SideToSideSet (τ.decomposeIter m (G.scatter T'.tiles)))
    (halign : SchedulesAligned τ G m T')
    (A A' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles)
    (a : Fin (G.P'.disk A.form).n) (a' : Fin (G.P'.disk A'.form).n)
    (hside : placedSeg ((τ.θ ^ m) • A.anchor) (parentSide τ G m A.form a) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (parentSide τ G m A'.form a')) :
    ∀ e' : sidesInside τ G m A'.form a', ∃! e : sidesInside τ G m A.form a,
      placedSeg ((τ.θ ^ m) • A.anchor) (e : Pt × Pt) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (e' : Pt × Pt) := by
  sorry

/-- Step 2 of the blueprint proof of `whole_side_ports_coincide`: fine STS gives identical
whole-edge subdivision of their common support, so there is a bijection between their sides inside
the parent side. -/
private lemma whole_side_ports_coincide_step2_sidesInside_bijection (m : ℕ) (T' : PlaneTiling G.P')
    (hfine : SideToSideSet (τ.decomposeIter m (G.scatter T'.tiles)))
    (halign : SchedulesAligned τ G m T')
    (A A' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles)
    (a : Fin (G.P'.disk A.form).n) (a' : Fin (G.P'.disk A'.form).n)
    (hside : placedSeg ((τ.θ ^ m) • A.anchor) (parentSide τ G m A.form a) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (parentSide τ G m A'.form a')) :
    ∃ f : sidesInside τ G m A.form a ≃ sidesInside τ G m A'.form a',
      ∀ (e : sidesInside τ G m A.form a), placedSeg ((τ.θ ^ m) • A.anchor) (e : Pt × Pt) =
        placedSeg ((τ.θ ^ m) • A'.anchor) (f e : Pt × Pt) := by
  have h1 := whole_side_ports_coincide_step2_sidesInside_bijection_step1_exists_unique τ G m T' hfine halign A A' hA hA' a a' hside
  have h2 := whole_side_ports_coincide_step2_sidesInside_bijection_step2_exists_unique_rev τ G m T' hfine halign A A' hA hA' a a' hside
  let f : sidesInside τ G m A.form a → sidesInside τ G m A'.form a' := fun e => Classical.choose (h1 e)
  have hf : ∀ e : sidesInside τ G m A.form a, placedSeg ((τ.θ ^ m) • A.anchor) (e : Pt × Pt) = placedSeg ((τ.θ ^ m) • A'.anchor) (f e : Pt × Pt) :=
    fun e => (Classical.choose_spec (h1 e)).1
  let g : sidesInside τ G m A'.form a' → sidesInside τ G m A.form a := fun e' => Classical.choose (h2 e')
  have hg : ∀ e' : sidesInside τ G m A'.form a', placedSeg ((τ.θ ^ m) • A.anchor) (g e' : Pt × Pt) = placedSeg ((τ.θ ^ m) • A'.anchor) (e' : Pt × Pt) :=
    fun e' => (Classical.choose_spec (h2 e')).1
  have left_inv : ∀ e : sidesInside τ G m A.form a, g (f e) = e := by
    intro e
    have h_eq : placedSeg ((τ.θ ^ m) • A.anchor) (e : Pt × Pt) = placedSeg ((τ.θ ^ m) • A'.anchor) (f e : Pt × Pt) := hf e
    have H2 := (Classical.choose_spec (h2 (f e))).2
    exact (H2 e h_eq).symm
  have right_inv : ∀ e' : sidesInside τ G m A'.form a', f (g e') = e' := by
    intro e'
    have h_eq : placedSeg ((τ.θ ^ m) • A.anchor) (g e' : Pt × Pt) = placedSeg ((τ.θ ^ m) • A'.anchor) (e' : Pt × Pt) := hg e'
    have H1 := (Classical.choose_spec (h1 (g e'))).2
    exact (H1 e' h_eq).symm
  exact ⟨⟨f, g, left_inv, right_inv⟩, hf⟩

/-- Equal translated segments have equal translated midpoints. -/
private lemma whole_side_ports_coincide_step3_rankIn_eq_midpoint
    (v w : Pt) (e e' : Pt × Pt) (h : placedSeg v e = placedSeg w e') :
    v + (1 / 2 : ℝ) • (e.1 + e.2) = w + (1 / 2 : ℝ) • (e'.1 + e'.2) := by
  unfold placedSeg at h
  rcases whole_side_ports_coincide_step1_parentDir_eq_step1_diff_step1_ends
      (v + e.1) (v + e.2) (w + e'.1) (w + e'.2) h with hends | hends
  · rcases hends with ⟨h1, h2⟩
    calc
      v + (1 / 2 : ℝ) • (e.1 + e.2) =
          (1 / 2 : ℝ) • ((v + e.1) + (v + e.2)) := by module
      _ = (1 / 2 : ℝ) • ((w + e'.1) + (w + e'.2)) := by rw [h1, h2]
      _ = w + (1 / 2 : ℝ) • (e'.1 + e'.2) := by module
  · rcases hends with ⟨h1, h2⟩
    calc
      v + (1 / 2 : ℝ) • (e.1 + e.2) =
          (1 / 2 : ℝ) • ((v + e.1) + (v + e.2)) := by module
      _ = (1 / 2 : ℝ) • ((w + e'.2) + (w + e'.1)) := by rw [h1, h2]
      _ = w + (1 / 2 : ℝ) • (e'.1 + e'.2) := by module

/-- Translation of a segment adds a constant to its key in any fixed direction. -/
private lemma whole_side_ports_coincide_step3_rankIn_eq_key
    (u v w : Pt) (e e' : Pt × Pt) (h : placedSeg v e = placedSeg w e') :
    sideKey u e + coord 0 u v = sideKey u e' + coord 0 u w := by
  have hmid := whole_side_ports_coincide_step3_rankIn_eq_midpoint v w e e' h
  have hcoord := congrArg (coord 0 u) hmid
  simp [sideKey, coord, mul_add] at hcoord ⊢
  linarith

/-- Equal translated segment families have the same strict side-key order. -/
private lemma whole_side_ports_coincide_step3_rankIn_eq_order
    (v w u : Pt) (e1 e2 e1' e2' : Pt × Pt)
    (h1 : placedSeg v e1 = placedSeg w e1') (h2 : placedSeg v e2 = placedSeg w e2') :
    sideKey u e1 < sideKey u e2 ↔ sideKey u e1' < sideKey u e2' := by
  have hk1 := whole_side_ports_coincide_step3_rankIn_eq_key u v w e1 e1' h1
  have hk2 := whole_side_ports_coincide_step3_rankIn_eq_key u v w e2 e2' h2
  constructor <;> intro hlt <;> linarith

/-- Step 3 of the blueprint proof of `whole_side_ports_coincide`: the bijection preserves the
rank in the canonical direction. -/
private lemma whole_side_ports_coincide_step3_rankIn_eq (m : ℕ)
    (A A' : PlacedTile G.P') (a : Fin (G.P'.disk A.form).n) (a' : Fin (G.P'.disk A'.form).n)
    (f : sidesInside τ G m A.form a ≃ sidesInside τ G m A'.form a')
    (hf : ∀ (e : sidesInside τ G m A.form a), placedSeg ((τ.θ ^ m) • A.anchor) (e : Pt × Pt) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (f e : Pt × Pt))
    (hdir : parentDir τ G m A.form a = parentDir τ G m A'.form a')
    (e : sidesInside τ G m A.form a) :
    rankIn (sidesInside τ G m A.form a) (parentDir τ G m A.form a) (e : Pt × Pt) =
      rankIn (sidesInside τ G m A'.form a') (parentDir τ G m A'.form a') (f e : Pt × Pt) := by
  unfold rankIn
  congr 1
  apply Set.ncard_congr (fun x hx => (f ⟨x, hx.1⟩ : Pt × Pt))
  · intro x hx
    refine ⟨(f ⟨x, hx.1⟩).2, ?_⟩
    rw [← hdir]
    exact (whole_side_ports_coincide_step3_rankIn_eq_order
      ((τ.θ ^ m) • A.anchor) ((τ.θ ^ m) • A'.anchor)
      (parentDir τ G m A.form a) x (e : Pt × Pt) (f ⟨x, hx.1⟩ : Pt × Pt)
      (f e : Pt × Pt) (hf ⟨x, hx.1⟩) (hf e)).1 hx.2
  · intro x y hx hy hxy
    have hfeq : f ⟨x, hx.1⟩ = f ⟨y, hy.1⟩ := Subtype.ext hxy
    have heq : (⟨x, hx.1⟩ : sidesInside τ G m A.form a) = ⟨y, hy.1⟩ := f.injective hfeq
    exact congrArg Subtype.val heq
  · intro y hy
    let y' : sidesInside τ G m A'.form a' := ⟨y, hy.1⟩
    let x' : sidesInside τ G m A.form a := f.symm y'
    refine ⟨(x' : Pt × Pt), ?_, ?_⟩
    · refine ⟨x'.2, ?_⟩
      rw [← hdir] at hy
      have horder := whole_side_ports_coincide_step3_rankIn_eq_order
        ((τ.θ ^ m) • A.anchor) ((τ.θ ^ m) • A'.anchor)
        (parentDir τ G m A.form a) (x' : Pt × Pt) (e : Pt × Pt)
        (f x' : Pt × Pt) (f e : Pt × Pt) (hf x') (hf e)
      apply horder.2
      simpa [x', y'] using hy.2
    · have happly : f x' = y' := Equiv.apply_symm_apply f y'
      exact congrArg Subtype.val happly

/-- Step 4 of the blueprint proof of `whole_side_ports_coincide`: a bijection between the sets
implies they have the same cardinality. -/
private lemma whole_side_ports_coincide_step4_ncard_eq (m : ℕ)
    (A A' : PlacedTile G.P') (a : Fin (G.P'.disk A.form).n) (a' : Fin (G.P'.disk A'.form).n)
    (f : sidesInside τ G m A.form a ≃ sidesInside τ G m A'.form a') :
    (sidesInside τ G m A.form a).ncard = (sidesInside τ G m A'.form a').ncard := by
  exact Set.ncard_congr (fun e he => f ⟨e, he⟩) (fun e he => (f ⟨e, he⟩).2)
    (fun e1 e2 he1 he2 h => by
      have h1 : (f ⟨e1, he1⟩).1 = (f ⟨e2, he2⟩).1 := h
      have h2 : f ⟨e1, he1⟩ = f ⟨e2, he2⟩ := Subtype.ext h1
      have h3 : (⟨e1, he1⟩ : sidesInside τ G m A.form a) = ⟨e2, he2⟩ := Equiv.injective f h2
      exact congrArg Subtype.val h3)
    (fun e' he' => by
      use (f.symm ⟨e', he'⟩).1
      use (f.symm ⟨e', he'⟩).2
      have h : f (f.symm ⟨e', he'⟩) = ⟨e', he'⟩ := Equiv.apply_symm_apply f ⟨e', he'⟩
      exact congrArg Subtype.val h)

/-- Helper for `whole_side_ports_coincide_step5_port_eq_step1_port_rank`: index bounds. -/
private lemma whole_side_ports_coincide_step5_port_eq_step1_port_rank_aux1 {L : ℕ} (h : 5 ≤ L) :
    ∀ r : Fin 5, 1 ≤ portIndex L r ∧ portIndex L r ≤ L := by
  intro r
  unfold portIndex
  fin_cases r <;> (dsimp; omega)

/-- Step 5 of the blueprint proof of `whole_side_ports_coincide_step5_port_eq`: the port has the defined rank. -/
private lemma whole_side_ports_coincide_step5_port_eq_step1_port_rank (τ : Substitution P)
    (G : Geometry.GroupedFamily P) (m : ℕ)
    (A : G.P'.Form) (a : Fin (G.P'.disk A).n)
    (hL : 5 ≤ (sidesInside τ G m A a).ncard) (r : Fin 5) :
    rankIn (sidesInside τ G m A a) (parentDir τ G m A a) (port τ G m A a r) =
      portIndex (sidesInside τ G m A a).ncard r := by
  have h_bounds := whole_side_ports_coincide_step5_port_eq_step1_port_rank_aux1 hL r
  have H_exist : ∃ e ∈ sidesInside τ G m A a,
      rankIn (sidesInside τ G m A a) (parentDir τ G m A a) e =
        portIndex (sidesInside τ G m A a).ncard r := by
    exact whole_side_ports_distinct_step3_rank (τ := τ) (G := G) m A a
      (portIndex (sidesInside τ G m A a).ncard r) h_bounds.1 h_bounds.2
  have H_eps := Classical.epsilon_spec H_exist
  unfold port
  exact H_eps.2

/-- Step 5 of the blueprint proof of `whole_side_ports_coincide_step5_port_eq`: the port belongs to the inside sides. -/
private lemma whole_side_ports_coincide_step5_port_eq_step2_port_mem (τ : Substitution P)
    (G : Geometry.GroupedFamily P) (m : ℕ)
    (A : G.P'.Form) (a : Fin (G.P'.disk A).n)
    (hL : 5 ≤ (sidesInside τ G m A a).ncard) (r : Fin 5) :
    port τ G m A a r ∈ sidesInside τ G m A a := by
  have H_bounds : 1 ≤ portIndex (sidesInside τ G m A a).ncard r ∧ portIndex (sidesInside τ G m A a).ncard r ≤ (sidesInside τ G m A a).ncard := by
    unfold portIndex
    have : (r : ℕ) ≤ 4 := by omega
    have hl : 5 ≤ (sidesInside τ G m A a).ncard := hL
    set L := (sidesInside τ G m A a).ncard
    have h1 : 1 ≤ (((r : ℕ) + 1) * L + 5) / 6 := by
      have : 6 ≤ ((r : ℕ) + 1) * L + 5 := by
        have : 1 * 5 ≤ ((r : ℕ) + 1) * L := Nat.mul_le_mul (by omega) hl
        omega
      omega
    have h2 : (((r : ℕ) + 1) * L + 5) / 6 ≤ L := by
      have : ((r : ℕ) + 1) * L + 5 ≤ 5 * L + 5 := Nat.add_le_add_right (Nat.mul_le_mul_right L (by omega)) 5
      have : 5 * L + 5 ≤ 6 * L := by
        have : 5 ≤ L := hl
        omega
      omega
    exact ⟨h1, h2⟩
  have H_exist : ∃ e, e ∈ sidesInside τ G m A a ∧ rankIn (sidesInside τ G m A a) (parentDir τ G m A a) e = portIndex (sidesInside τ G m A a).ncard r := by
    obtain ⟨e, he, hr⟩ := whole_side_ports_distinct_step3_rank τ G m A a (portIndex (sidesInside τ G m A a).ncard r) H_bounds.1 H_bounds.2
    exact ⟨e, he, hr⟩
  have H_eps := Classical.epsilon_spec H_exist
  unfold port
  exact H_eps.1














/-- Step 5 of the blueprint proof of `whole_side_ports_coincide_step5_port_eq_step3_rank_inj`: rank equality implies key equality. -/
private lemma whole_side_ports_coincide_step5_port_eq_step3_rank_inj_step1_rank_to_key
    (X : Set (Pt × Pt)) (h_fin : X.Finite) (u : Pt)
    (e1 e2 : Pt × Pt) (he1 : e1 ∈ X) (he2 : e2 ∈ X)
    (h_rank : rankIn X u e1 = rankIn X u e2) :
    sideKey u e1 = sideKey u e2 := by
  dsimp [rankIn] at h_rank
  by_contra h_ne
  rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
  · have h1 : {e' ∈ X | sideKey u e' < sideKey u e1} ⊆ {e' ∈ X | sideKey u e' < sideKey u e2} := by
      intro e he
      simp only [Set.mem_setOf_eq] at he ⊢
      exact ⟨he.1, lt_trans he.2 h_lt⟩
    have h2 : e1 ∈ {e' ∈ X | sideKey u e' < sideKey u e2} := by
      simp only [Set.mem_setOf_eq]
      exact ⟨he1, h_lt⟩
    have h3 : e1 ∉ {e' ∈ X | sideKey u e' < sideKey u e1} := by
      simp only [Set.mem_setOf_eq, lt_self_iff_false, not_false_eq_true, and_false]
    have h4 : {e' ∈ X | sideKey u e' < sideKey u e1} ⊂ {e' ∈ X | sideKey u e' < sideKey u e2} := by
      refine Set.ssubset_iff_subset_ne.mpr ⟨h1, ?_⟩
      intro heq
      have hh3 : e1 ∉ {e' ∈ X | sideKey u e' < sideKey u e2} := by
        rw [← heq]
        exact h3
      exact hh3 h2
    have h5 : {e' ∈ X | sideKey u e' < sideKey u e2}.Finite := by
      exact h_fin.subset (fun _ h => h.1)
    have h6 := Set.ncard_lt_ncard h4 h5
    omega
  · have h1 : {e' ∈ X | sideKey u e' < sideKey u e2} ⊆ {e' ∈ X | sideKey u e' < sideKey u e1} := by
      intro e he
      simp only [Set.mem_setOf_eq] at he ⊢
      exact ⟨he.1, lt_trans he.2 h_gt⟩
    have h2 : e2 ∈ {e' ∈ X | sideKey u e' < sideKey u e1} := by
      simp only [Set.mem_setOf_eq]
      exact ⟨he2, h_gt⟩
    have h3 : e2 ∉ {e' ∈ X | sideKey u e' < sideKey u e2} := by
      simp only [Set.mem_setOf_eq, lt_self_iff_false, not_false_eq_true, and_false]
    have h4 : {e' ∈ X | sideKey u e' < sideKey u e2} ⊂ {e' ∈ X | sideKey u e' < sideKey u e1} := by
      refine Set.ssubset_iff_subset_ne.mpr ⟨h1, ?_⟩
      intro heq
      have hh3 : e2 ∉ {e' ∈ X | sideKey u e' < sideKey u e1} := by
        rw [← heq]
        exact h3
      exact hh3 h2
    have h5 : {e' ∈ X | sideKey u e' < sideKey u e1}.Finite := by
      exact h_fin.subset (fun _ h => h.1)
    have h6 := Set.ncard_lt_ncard h4 h5
    omega

/-- Step 5 of the blueprint proof of `whole_side_ports_coincide_step5_port_eq`: rank is injective. -/
private lemma whole_side_ports_coincide_step5_port_eq_step3_rank_inj (τ : Substitution P)
    (G : Geometry.GroupedFamily P) (m : ℕ)
    (A : G.P'.Form) (a : Fin (G.P'.disk A).n)
    (e1 e2 : Pt × Pt) (he1 : e1 ∈ sidesInside τ G m A a) (he2 : e2 ∈ sidesInside τ G m A a)
    (h : rankIn (sidesInside τ G m A a) (parentDir τ G m A a) e1 =
      rankIn (sidesInside τ G m A a) (parentDir τ G m A a) e2) :
    e1 = e2 := by
  have h_fin : (sidesInside τ G m A a).Finite :=
    whole_side_ports_distinct_step3_rank_step1_finite τ G m A a
  have h_inj : (sidesInside τ G m A a).InjOn (sideKey (parentDir τ G m A a)) :=
    whole_side_ports_distinct_step3_rank_step2_inj τ G m A a
  have h_key : sideKey (parentDir τ G m A a) e1 = sideKey (parentDir τ G m A a) e2 :=
    whole_side_ports_coincide_step5_port_eq_step3_rank_inj_step1_rank_to_key
      (sidesInside τ G m A a) h_fin (parentDir τ G m A a) e1 e2 he1 he2 h
  exact h_inj he1 he2 h_key

/-- Step 5 of the blueprint proof of `whole_side_ports_coincide`: the chosen ports coincide
because they are uniquely determined by the physical subdivision. -/
private lemma whole_side_ports_coincide_step5_port_eq (m : ℕ)
    (A A' : PlacedTile G.P') (a : Fin (G.P'.disk A.form).n) (a' : Fin (G.P'.disk A'.form).n)
    (f : sidesInside τ G m A.form a ≃ sidesInside τ G m A'.form a')
    (hf : ∀ (e : sidesInside τ G m A.form a), placedSeg ((τ.θ ^ m) • A.anchor) (e : Pt × Pt) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (f e : Pt × Pt))
    (hdir : parentDir τ G m A.form a = parentDir τ G m A'.form a')
    (hcard : (sidesInside τ G m A.form a).ncard = (sidesInside τ G m A'.form a').ncard)
    (hrank : ∀ (e : sidesInside τ G m A.form a),
      rankIn (sidesInside τ G m A.form a) (parentDir τ G m A.form a) (e : Pt × Pt) =
        rankIn (sidesInside τ G m A'.form a') (parentDir τ G m A'.form a') (f e : Pt × Pt))
    (hL : 5 ≤ (sidesInside τ G m A.form a).ncard) (r : Fin 5) :
    placedSeg ((τ.θ ^ m) • A.anchor) (port τ G m A.form a r) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (port τ G m A'.form a' r) := by
  have _ := hdir
  have hport_mem := whole_side_ports_coincide_step5_port_eq_step2_port_mem τ G m A.form a hL r
  have hport_rank := whole_side_ports_coincide_step5_port_eq_step1_port_rank τ G m A.form a hL r
  have hL' : 5 ≤ (sidesInside τ G m A'.form a').ncard := by linarith
  have hport_mem' := whole_side_ports_coincide_step5_port_eq_step2_port_mem τ G m A'.form a' hL' r
  have hport_rank' := whole_side_ports_coincide_step5_port_eq_step1_port_rank τ G m A'.form a' hL' r
  have H1 := hrank ⟨port τ G m A.form a r, hport_mem⟩
  dsimp at H1
  rw [hport_rank] at H1
  rw [hcard] at H1
  have H2 : rankIn (sidesInside τ G m A'.form a') (parentDir τ G m A'.form a') (f ⟨port τ G m A.form a r, hport_mem⟩ : Pt × Pt) =
    rankIn (sidesInside τ G m A'.form a') (parentDir τ G m A'.form a') (port τ G m A'.form a' r) := by
    rw [← H1]
    exact hport_rank'.symm
  have H3 := whole_side_ports_coincide_step5_port_eq_step3_rank_inj τ G m A'.form a'
    (f ⟨port τ G m A.form a r, hport_mem⟩ : Pt × Pt) (port τ G m A'.form a' r)
    (f ⟨port τ G m A.form a r, hport_mem⟩).2 hport_mem' H2
  have Hf := hf ⟨port τ G m A.form a r, hport_mem⟩
  rw [H3] at Hf
  exact Hf

/-- `lem:whole-ports` (coincidence): in a grouped plane tiling with STS fine
level and aligned schedules, physically coincident parent sides have the same
physical port lists, numbered in the global direction.
The parent side must contain at least five whole fine sides (`L ≥ 5`, "for
sufficiently large `L`" in the blueprint; review addition of 13 October 2026:
with `L < 5` the ports are junk and the conclusion can fail). -/
theorem whole_side_ports_coincide (m : ℕ) (T' : PlaneTiling G.P')
    (hfine : SideToSideSet (τ.decomposeIter m (G.scatter T'.tiles)))
    (halign : SchedulesAligned τ G m T')
    (A A' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles)
    (a : Fin (G.P'.disk A.form).n) (a' : Fin (G.P'.disk A'.form).n)
    (hside : placedSeg ((τ.θ ^ m) • A.anchor) (parentSide τ G m A.form a) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (parentSide τ G m A'.form a'))
    (hL : 5 ≤ (sidesInside τ G m A.form a).ncard) :
    ∀ r, placedSeg ((τ.θ ^ m) • A.anchor) (port τ G m A.form a r) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (port τ G m A'.form a' r) := by
  intro r
  have h1 := whole_side_ports_coincide_step1_parentDir_eq τ G m A A' a a' hside
  have ⟨f, hf⟩ := whole_side_ports_coincide_step2_sidesInside_bijection τ G m T' hfine halign A A'
    hA hA' a a' hside
  have h2 : ∀ (e : sidesInside τ G m A.form a),
      rankIn (sidesInside τ G m A.form a) (parentDir τ G m A.form a) (e : Pt × Pt) =
      rankIn (sidesInside τ G m A'.form a') (parentDir τ G m A'.form a') (f e : Pt × Pt) :=
    fun e => whole_side_ports_coincide_step3_rankIn_eq τ G m A A' a a' f hf h1 e
  have h3 := whole_side_ports_coincide_step4_ncard_eq τ G m A A' a a' f
  exact whole_side_ports_coincide_step5_port_eq τ G m A A' a a' f hf h1 h3 h2 hL r

/-! ## Strict schedule composition (`lem:schedule-compose`) -/

/-- The strict variant of the coloured grouped substitution: a side decoration
`dec` of the grouped forms, a coloured substitution `σc` projecting onto the
grouped substitution, and the strict-variant generated field: every outer
side of a child of a coloured template carries the tagged endpoint schedule
`W(A, e)` of its parent, and equal side colours force equal schedule fields.
To be instantiated by the strict typed decoration of the control chapter. -/
structure StrictScheduleSystem (τ : Substitution P) where
  GS : GroupedSubstitution τ
  dec : SideDecoration GS.G.P'
  σc : Substitution dec.P'
  θ_eq : σc.θ = GS.σ.θ
  rule_proj : ∀ q, dec.toDecoration.projTile '' (σc.rule q).tiles = (GS.σ.rule (dec.proj q)).tiles
  outerSchedule : ∀ q : dec.P'.Form, Fin (dec.P'.disk q).n →
    Option (LayerTag GS.k → Set (ℝ × ℝ × ℝ × ℝ))
  schedule_spec : ∀ q, ∀ X ∈ (σc.rule q).tiles, ∀ i : Fin (dec.P'.disk X.form).n,
    X.side i ⊆ frontier (σc.θ • (dec.P'.disk q).carrier) →
      outerSchedule X.form i =
        some (EndpointSchedule τ GS.G GS.k (dec.proj q) (X.vertex i, X.vertex (finRotate _ i)))
  schedule_colour : ∀ (q q' : dec.P'.Form) (i : Fin (dec.P'.disk q).n)
    (i' : Fin (dec.P'.disk q').n), dec.colour q i = dec.colour q' i' →
      outerSchedule q i = outerSchedule q' i'

private lemma strict_schedule_composition_endpointSchedule_swap
    (τ : Substitution P) (G : GroupedFamily P) (m : ℕ)
    (A : G.P'.Form) (x y : Pt) :
    EndpointSchedule τ G m A (x, y) = EndpointSchedule τ G m A (y, x) := by
  have hcoord : ∀ z, segCoord y x z = segCoord x y z := by
    intro z
    unfold segCoord
    rw [boundary_align_frameOrigin_swap]
    have hsub : x - y = -(y - x) := by abel
    rw [hsub, boundary_align_canonDir_neg]
  funext t
  ext r
  simp only [EndpointSchedule, Set.mem_setOf_eq]
  constructor <;> rintro ⟨c, hc, hov, rfl⟩
  · refine ⟨c, hc, ?_, ?_⟩
    · simpa [segment_symm] using hov
    · simp only [atom, hcoord, dist_comm]
  · refine ⟨c, hc, ?_, ?_⟩
    · simpa [segment_symm] using hov
    · simp only [atom, hcoord, dist_comm]

private lemma strict_schedule_composition_step1_side_carrier
    (X : PlacedTile P) (i : Fin (P.disk X.form).n) : X.side i ⊆ X.carrier := by
  have hfront : (P.disk X.form).side i ⊆ frontier (P.disk X.form).carrier := by
    rw [(P.disk X.form).frontier_eq]
    exact Set.subset_iUnion (fun j => (P.disk X.form).side j) i
  intro z hz
  change z ∈ X.anchor +ᵥ (P.disk X.form).side i at hz
  change z ∈ X.anchor +ᵥ (P.disk X.form).carrier
  rw [mem_vadd_set_iff_neg_vadd_mem] at hz ⊢
  exact (P.disk X.form).compact.isClosed.frontier_subset (hfront hz)

private lemma strict_schedule_composition_step1_regular
    (A : PlacedTile P) : closure (interior A.carrier) = A.carrier := by
  unfold PlacedTile.carrier
  rw [interior_vadd, closure_vadd, (P.disk A.form).regular_closed]

private lemma strict_schedule_composition_step1_frontier
    (A : PlacedTile P) : frontier A.carrier = ⋃ i : Fin (P.disk A.form).n, A.side i := by
  have hclosed : IsClosed A.carrier := by
    rw [← strict_schedule_composition_step1_regular A]
    exact isClosed_closure
  ext z
  constructor
  · intro hz
    rw [hclosed.frontier_eq] at hz
    have hcar := hz.1
    have hint := hz.2
    rw [PlacedTile.carrier, mem_vadd_set_iff_neg_vadd_mem] at hcar
    rw [PlacedTile.carrier, interior_vadd,
      mem_vadd_set_iff_neg_vadd_mem] at hint
    have hz' : -A.anchor +ᵥ z ∈ frontier (P.disk A.form).carrier := by
      rw [(P.disk A.form).compact.isClosed.frontier_eq]
      exact ⟨hcar, hint⟩
    rw [(P.disk A.form).frontier_eq] at hz'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz'
    exact Set.mem_iUnion.2 ⟨i, by
      change z ∈ A.anchor +ᵥ (P.disk A.form).side i
      rw [mem_vadd_set_iff_neg_vadd_mem]
      exact hi⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    rw [hclosed.frontier_eq]
    refine ⟨strict_schedule_composition_step1_side_carrier A i hi, ?_⟩
    intro hzi
    rw [PlacedTile.side, PolygonalDisk.side] at hi
    rw [PlacedTile.carrier, interior_vadd] at hzi
    rw [mem_vadd_set_iff_neg_vadd_mem] at hi hzi
    have hfront : (P.disk A.form).side i ⊆ frontier (P.disk A.form).carrier := by
      rw [(P.disk A.form).frontier_eq]
      exact Set.subset_iUnion (fun j => (P.disk A.form).side j) i
    exact Set.disjoint_left.mp disjoint_interior_frontier hzi (hfront hi)

private lemma strict_schedule_composition_step1_carrier
    (G : GroupedFamily P) (A : PlacedTile G.P')
    (X : PlacedTile P) (hX : X ∈ G.scatterTile A) : X.carrier ⊆ A.carrier := by
  rcases hX with ⟨X₀, hX₀, rfl⟩
  have hbase : X₀.carrier ⊆ (G.P'.disk A.form).carrier := by
    intro z hz
    rw [← G.support_eq A.form]
    exact Set.mem_iUnion.2 ⟨X₀, Set.mem_iUnion.2 ⟨hX₀, hz⟩⟩
  intro z hz
  change z ∈ (A.anchor +ᵥ X₀.anchor) +ᵥ (P.disk X₀.form).carrier at hz
  change z ∈ A.anchor +ᵥ (G.P'.disk A.form).carrier
  have hz' : z ∈ A.anchor +ᵥ (X₀.anchor +ᵥ (P.disk X₀.form).carrier) := by
    simpa only [vadd_vadd] using hz
  obtain ⟨w, hw, rfl⟩ := hz'
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  exact ⟨X₀.anchor +ᵥ w₀, hbase ⟨w₀, hw₀, rfl⟩, by simp [vadd_eq_add]⟩

private lemma strict_schedule_composition_step1_finite_cover
    {x y : Pt} (hxy : x ≠ y) {n : ℕ}
    (s : Fin n → Set Pt) (hsub : segment ℝ x y ⊆ ⋃ i, s i)
    (hconv : ∀ i, Convex ℝ (s i)) : ∃ i, OverlapPos (segment ℝ x y) (s i) := by
  by_contra h
  push_neg at h
  have hss : ∀ i : Fin n, Set.Subsingleton (segment ℝ x y ∩ s i) := by
    intro i p hp q hq
    by_contra hpq
    have hpqsub : segment ℝ p q ⊆ segment ℝ x y ∩ s i :=
      (convex_segment _ _).inter (hconv i) |>.segment_subset hp hq
    exact (h i) ⟨p, q, hpq, hpqsub⟩
  have hfin : (⋃ i : Fin n, segment ℝ x y ∩ s i).Finite := by
    simpa using
      (Set.toFinite (Set.univ : Set (Fin n))).biUnion (fun i _ => (hss i).finite)
  have hseg : segment ℝ x y ⊆ ⋃ i : Fin n, segment ℝ x y ∩ s i := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hsub hz)
    exact Set.mem_iUnion.2 ⟨i, hz, hi⟩
  letI : Infinite (Set.Ioo (0 : ℝ) 1) := Set.Ioo.infinite (by norm_num)
  have hinf : (segment ℝ x y).Infinite := by
    apply Set.infinite_of_injective_forall_mem
      (f := fun t : Set.Ioo (0 : ℝ) 1 => AffineMap.lineMap x y t.1)
    · intro a b hab
      apply Subtype.ext
      exact (AffineMap.lineMap_injective ℝ hxy) hab
    · intro t
      rw [segment_eq_image_lineMap]
      exact ⟨t.1, Set.mem_Icc.mpr ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩, rfl⟩
  exact hinf (hfin.subset hseg)

private lemma strict_schedule_composition_step1_translate_side
    (X : PlacedTile P) (v : Pt) (i : Fin (P.disk X.form).n) :
    (X.translate v).side i = v +ᵥ X.side i := by
  simp [PlacedTile.translate, PlacedTile.side, vadd_vadd]

private lemma strict_schedule_composition_step1_translate_overlap
    (X Y : PlacedTile P) (v : Pt)
    (i : Fin (P.disk X.form).n) (j : Fin (P.disk Y.form).n)
    (h : OverlapPos ((X.translate v).side i) ((Y.translate v).side j)) :
    OverlapPos (X.side i) (Y.side j) := by
  obtain ⟨x, y, hxy, hseg⟩ := h
  refine ⟨-v +ᵥ x, -v +ᵥ y, by simpa using hxy, ?_⟩
  rw [strict_schedule_composition_step1_translate_side,
    strict_schedule_composition_step1_translate_side] at hseg
  intro z hz
  have hz' : v +ᵥ z ∈ segment ℝ x y := by
    rw [segment_eq_image'] at hz ⊢
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨t, ht, by simp only [vadd_eq_add]; abel⟩
  have hz'' := hseg hz'
  exact ⟨by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hz''.1,
    by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hz''.2⟩

private lemma strict_schedule_composition_step1_side_eq
    {D E : PolygonalDisk} (hd : D = E) (i : Fin E.n) :
    D.side (Fin.cast (congrArg (fun Q : PolygonalDisk => Q.n) hd).symm i) =
      E.side i := by
  cases hd
  rfl

private theorem strict_schedule_composition_step1_boundary_lifting
    {P : Protoset} {τ : Substitution P} (Sys : StrictScheduleSystem τ)
    (T T'' : PlaneTiling Sys.dec.P')
    (hcomp : Sys.σc.IsComposition T'' T)
    (A : PlacedTile Sys.GS.G.P')
    (hA : A ∈ (Sys.dec.toDecoration.project T'').tiles)
    (e : Pt × Pt) (he : e ∈ fineOuterSides τ Sys.GS.G Sys.GS.k A.form) :
    ∃ (q : PlacedTile Sys.dec.P') (_hq : q ∈ T''.tiles)
      (Y : PlacedTile Sys.dec.P') (_hY : Y ∈ (Sys.σc.rule q.form).tiles)
      (i : Fin (Sys.dec.P'.disk Y.form).n),
      Sys.dec.toDecoration.projTile q = A ∧
      Y.side i ⊆ frontier (Sys.σc.θ • (Sys.dec.P'.disk q.form).carrier) ∧
      (e = (Y.vertex i, Y.vertex (finRotate _ i)) ∨
        e = (Y.vertex (finRotate _ i), Y.vertex i)) ∧
      Y.translate (Sys.σc.θ • q.anchor) ∈ T.tiles ∧
      placedSeg ((τ.θ ^ Sys.GS.k) • A.anchor) e =
        (Y.translate (Sys.σc.θ • q.anchor)).side i := by
  rcases hA with ⟨q, hq, rfl⟩
  rcases he with ⟨B, hB, j, rfl, hBfront⟩
  have hB' : B ∈ Sys.GS.G.scatter
      (Sys.GS.σ.rule (Sys.dec.proj q.form)).tiles := by
    rw [Sys.GS.compat]
    exact hB
  rcases Set.mem_iUnion.1 hB' with ⟨X, hB'⟩
  rcases Set.mem_iUnion.1 hB' with ⟨hX, hBX⟩
  have hX' : X ∈ Sys.dec.toDecoration.projTile ''
      (Sys.σc.rule q.form).tiles := by
    rw [Sys.rule_proj]
    exact hX
  rcases hX' with ⟨Y, hY, rfl⟩
  let X := Sys.dec.toDecoration.projTile Y
  have hBcarrier : B.carrier ⊆ X.carrier :=
    strict_schedule_composition_step1_carrier Sys.GS.G X B hBX
  have hXparent : X.carrier ⊆
      parentRegion τ Sys.GS.G Sys.GS.k (Sys.dec.proj q.form) := by
    intro z hz
    rw [parentRegion, ← Sys.GS.θ_eq, ← Sys.GS.σ.support_eq]
    exact Set.mem_iUnion.2 ⟨X, Set.mem_iUnion.2 ⟨hX, hz⟩⟩
  have hBside : B.side j ⊆ frontier X.carrier := by
    intro z hz
    have hzB :=
      strict_schedule_composition_step1_side_carrier B j hz
    have hzX := hBcarrier hzB
    have hzseg : z ∈ segment ℝ (B.vertex j) (B.vertex (finRotate _ j)) := by
      rw [← omitted_count_tile_side_eq B j]
      exact hz
    have hzfront := hBfront hzseg
    have hclosed : IsClosed X.carrier := by
      rw [← strict_schedule_composition_step1_regular X]
      exact isClosed_closure
    rw [hclosed.frontier_eq]
    refine ⟨hzX, ?_⟩
    intro hzint
    exact Set.disjoint_left.mp disjoint_interior_frontier
      (interior_mono hXparent hzint) hzfront
  have hBunion : B.side j ⊆ ⋃ i : Fin (Sys.GS.G.P'.disk X.form).n, X.side i := by
    rw [← strict_schedule_composition_step1_frontier]
    exact hBside
  obtain ⟨i, hover⟩ :=
    strict_schedule_composition_step1_finite_cover
      (omitted_count_tile_vertex_ne_next B j) (fun i => X.side i) (by
        rw [← omitted_count_tile_side_eq B j]
        exact hBunion)
      (fun i => by
        change Convex ℝ (X.anchor +ᵥ (Sys.GS.G.P'.disk X.form).side i)
        exact (convex_segment _ _).vadd X.anchor)
  obtain ⟨C, hC, l, hCl⟩ := Sys.GS.G.side_whole X.form i
  have hCX : (C.translate X.anchor).side l = X.side i := by
    simpa [PlacedTile.translate, PlacedTile.side, vadd_vadd] using
      congrArg (fun s : Set Pt => X.anchor +ᵥ s) hCl
  have hover' : OverlapPos (B.side j) ((C.translate X.anchor).side l) := by
    rw [hCX, omitted_count_tile_side_eq]
    exact hover
  rcases hBX with ⟨B₀, hB₀, rfl⟩
  have hover₀ :=
    strict_schedule_composition_step1_translate_overlap B₀ C X.anchor j l hover'
  have heq₀ : B₀.side j = C.side l :=
    Sys.GS.G.sts X.form B₀ hB₀ C hC j l hover₀
  have heq : (B₀.translate X.anchor).side j = X.side i := by
    rw [strict_schedule_composition_step1_translate_side, heq₀]
    simpa [PlacedTile.translate, PlacedTile.side, vadd_vadd] using hCX
  let hd := Sys.dec.disk_eq Y.form
  let i' : Fin (Sys.dec.P'.disk Y.form).n :=
    Fin.cast (congrArg (fun D : PolygonalDisk => D.n) hd).symm i
  have hYi : Y.side i' = X.side i := by
    change Y.anchor +ᵥ (Sys.dec.P'.disk Y.form).side i' =
      Y.anchor +ᵥ (Sys.GS.G.P'.disk (Sys.dec.proj Y.form)).side i
    exact congrArg (fun s : Set Pt => Y.anchor +ᵥ s)
      (strict_schedule_composition_step1_side_eq hd i)
  have hside : (B₀.translate X.anchor).side j = Y.side i' := heq.trans hYi.symm
  have hends :
      (Y.vertex i' = (B₀.translate X.anchor).vertex j ∧
        Y.vertex (finRotate _ i') = (B₀.translate X.anchor).vertex (finRotate _ j)) ∨
      (Y.vertex i' = (B₀.translate X.anchor).vertex (finRotate _ j) ∧
        Y.vertex (finRotate _ i') = (B₀.translate X.anchor).vertex j) := by
    apply boundary_align_segment_endpoints
      (omitted_count_tile_vertex_ne_next (B₀.translate X.anchor) j)
    simpa only [omitted_count_tile_side_eq] using hside
  have horient :
      ((B₀.translate X.anchor).vertex j,
          (B₀.translate X.anchor).vertex (finRotate _ j)) =
          (Y.vertex i', Y.vertex (finRotate _ i')) ∨
      ((B₀.translate X.anchor).vertex j,
          (B₀.translate X.anchor).vertex (finRotate _ j)) =
          (Y.vertex (finRotate _ i'), Y.vertex i') := by
    rcases hends with hends | hends
    · exact Or.inl (Prod.ext hends.1.symm hends.2.symm)
    · exact Or.inr (Prod.ext hends.2.symm hends.1.symm)
  refine ⟨q, hq, Y, hY, i', rfl, ?_, horient, ?_, ?_⟩
  · rw [← hside]
    intro z hz
    have hzseg : z ∈ segment ℝ
        ((B₀.translate X.anchor).vertex j)
        ((B₀.translate X.anchor).vertex (finRotate _ j)) := by
      rw [← omitted_count_tile_side_eq]
      exact hz
    have hzfront := hBfront hzseg
    simpa [parentRegion, Sys.θ_eq, Sys.GS.θ_eq, Sys.dec.disk_eq] using hzfront
  · rw [← hcomp]
    exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, ⟨Y, hY, rfl⟩⟩⟩
  · rw [Sys.θ_eq, Sys.GS.θ_eq]
    dsimp [X] at hside ⊢
    let v := (τ.θ ^ Sys.GS.k) • q.anchor
    change placedSeg v
      ((B₀.translate (Sys.dec.toDecoration.projTile Y).anchor).vertex j,
        (B₀.translate (Sys.dec.toDecoration.projTile Y).anchor).vertex
          (finRotate _ j)) = (Y.translate v).side i'
    calc
      placedSeg v
          ((B₀.translate (Sys.dec.toDecoration.projTile Y).anchor).vertex j,
            (B₀.translate (Sys.dec.toDecoration.projTile Y).anchor).vertex
              (finRotate _ j)) =
          v +ᵥ (B₀.translate (Sys.dec.toDecoration.projTile Y).anchor).side j := by
            simp [placedSeg, omitted_count_tile_side_eq, vadd_segment]
      _ = v +ᵥ Y.side i' := congrArg (fun s : Set Pt => v +ᵥ s) hside
      _ = (Y.translate v).side i' :=
        (strict_schedule_composition_step1_translate_side Y v i').symm

private lemma strict_schedule_composition_step1_same_tile_colour
    (dec : SideDecoration P) (Z Z' : PlacedTile dec.P') (hZZ : Z = Z')
    (i : Fin (dec.P'.disk Z.form).n) (i' : Fin (dec.P'.disk Z'.form).n)
    (hside : Z.side i = Z'.side i') :
    dec.colour Z.form i = dec.colour Z'.form i' := by
  subst Z'
  let z := AffineMap.lineMap (Z.vertex i) (Z.vertex (finRotate _ i)) (1 / 2 : ℝ)
  have hzopen : z ∈ openSegment ℝ (Z.vertex i) (Z.vertex (finRotate _ i)) :=
    lineMap_mem_openSegment (𝕜 := ℝ) _ _ (by norm_num)
  have hzside : z ∈ Z.side i' := by
    rw [← hside, omitted_count_tile_side_eq]
    exact openSegment_subset_segment ℝ _ _ hzopen
  have hzseg : z ∈ segment ℝ (Z.vertex i') (Z.vertex (finRotate _ i')) := by
    rw [← omitted_count_tile_side_eq Z i']
    exact hzside
  have hii := omitted_count_same_tile_side_index Z i i' z hzopen hzseg
  subst i'
  rfl

private theorem strict_schedule_composition_step1_schedule_transfer
    {P : Protoset} {τ : Substitution P} (Sys : StrictScheduleSystem τ)
    (T : PlaneTiling Sys.dec.P') (hp : Sys.dec.Proper T)
    (A A' : PlacedTile Sys.GS.G.P') (e e' : Pt × Pt)
    (q q' : PlacedTile Sys.dec.P') (Y Y' : PlacedTile Sys.dec.P')
    (i : Fin (Sys.dec.P'.disk Y.form).n)
    (i' : Fin (Sys.dec.P'.disk Y'.form).n)
    (hproj : Sys.dec.toDecoration.projTile q = A)
    (hproj' : Sys.dec.toDecoration.projTile q' = A')
    (hY : Y ∈ (Sys.σc.rule q.form).tiles)
    (hY' : Y' ∈ (Sys.σc.rule q'.form).tiles)
    (hfront : Y.side i ⊆ frontier (Sys.σc.θ • (Sys.dec.P'.disk q.form).carrier))
    (hfront' : Y'.side i' ⊆
      frontier (Sys.σc.θ • (Sys.dec.P'.disk q'.form).carrier))
    (horient : e = (Y.vertex i, Y.vertex (finRotate _ i)) ∨
      e = (Y.vertex (finRotate _ i), Y.vertex i))
    (horient' : e' = (Y'.vertex i', Y'.vertex (finRotate _ i')) ∨
      e' = (Y'.vertex (finRotate _ i'), Y'.vertex i'))
    (hT : Y.translate (Sys.σc.θ • q.anchor) ∈ T.tiles)
    (hT' : Y'.translate (Sys.σc.θ • q'.anchor) ∈ T.tiles)
    (hside : (Y.translate (Sys.σc.θ • q.anchor)).side i =
      (Y'.translate (Sys.σc.θ • q'.anchor)).side i') :
    EndpointSchedule τ Sys.GS.G Sys.GS.k A.form e =
      EndpointSchedule τ Sys.GS.G Sys.GS.k A'.form e' := by
  have hform : Sys.dec.proj q.form = A.form :=
    congrArg PlacedTile.form hproj
  have hform' : Sys.dec.proj q'.form = A'.form :=
    congrArg PlacedTile.form hproj'
  have hs := Sys.schedule_spec q.form Y hY i hfront
  have hs' := Sys.schedule_spec q'.form Y' hY' i' hfront'
  rw [hform] at hs
  rw [hform'] at hs'
  have hsched : Sys.outerSchedule Y.form i =
      some (EndpointSchedule τ Sys.GS.G Sys.GS.k A.form e) := by
    rcases horient with rfl | rfl
    · exact hs
    · rw [← strict_schedule_composition_endpointSchedule_swap] at hs
      exact hs
  have hsched' : Sys.outerSchedule Y'.form i' =
      some (EndpointSchedule τ Sys.GS.G Sys.GS.k A'.form e') := by
    rcases horient' with rfl | rfl
    · exact hs'
    · rw [← strict_schedule_composition_endpointSchedule_swap] at hs'
      exact hs'
  have hcolour : Sys.dec.colour Y.form i = Sys.dec.colour Y'.form i' := by
    let Z := Y.translate (Sys.σc.θ • q.anchor)
    let Z' := Y'.translate (Sys.σc.θ • q'.anchor)
    by_cases hne : Z ≠ Z'
    · exact hp.2 Z hT Z' hT' hne i i' hside
    · exact strict_schedule_composition_step1_same_tile_colour
        Sys.dec Z Z' (not_ne_iff.mp hne) i i' hside
  have hout := Sys.schedule_colour Y.form Y'.form i i' hcolour
  rw [hsched, hsched'] at hout
  exact Option.some.inj hout

/-- Step 1 of the blueprint proof of `strict_schedule_composition`: boundary-edge lifting — every
fine outer side is the projection of an outer side of a coloured rule child, so
schedule_spec/schedule_colour + properness give aligned schedules. -/
private theorem strict_schedule_composition_step1_aligned {P : Protoset} {τ : Substitution P} (hτ : τ.STS)
    (Sys : StrictScheduleSystem τ)
    (T T'' : PlaneTiling Sys.dec.P') (hp : Sys.dec.Proper T)
    (hcomp : Sys.σc.IsComposition T'' T) :
    SchedulesAligned τ Sys.GS.G Sys.GS.k (Sys.dec.toDecoration.project T'') := by
  have _ := hτ
  intro A hA A' hA' e he e' he' hseg
  obtain ⟨q, _, Y, hY, i, hproj, hfront, horient, hT, hphys⟩ :=
    strict_schedule_composition_step1_boundary_lifting
      Sys T T'' hcomp A hA e he
  obtain ⟨q', _, Y', hY', i', hproj', hfront', horient', hT', hphys'⟩ :=
    strict_schedule_composition_step1_boundary_lifting
      Sys T T'' hcomp A' hA' e' he'
  have hside : (Y.translate (Sys.σc.θ • q.anchor)).side i =
      (Y'.translate (Sys.σc.θ • q'.anchor)).side i' := by
    rw [← hphys, hseg, hphys']
  exact strict_schedule_composition_step1_schedule_transfer
    Sys T hp A A' e e' q q' Y Y' i i' hproj hproj' hY hY' hfront hfront'
    horient horient' hT hT' hside

private theorem strict_schedule_composition_step2_fine_sts_step1_reduce_translate
    (τ : Substitution P) (v : Pt) (S : Set (PlacedTile P)) :
    τ.decompose (translateSet v S) = translateSet (τ.θ • v) (τ.decompose S) := by
  ext X
  simp only [Substitution.decompose, Substitution.decomposeTile, translateSet,
    Set.mem_iUnion, Set.mem_image, PlacedTile.translate, exists_prop]
  constructor
  · rintro ⟨_, ⟨A, hA, rfl⟩, Y, hY, rfl⟩
    refine ⟨⟨Y.form, τ.θ • A.anchor +ᵥ Y.anchor⟩,
      ⟨A, hA, Y, hY, rfl⟩, ?_⟩
    simp only [vadd_eq_add, smul_add, add_assoc]
  · rintro ⟨_, ⟨A, hA, Y, hY, rfl⟩, rfl⟩
    refine ⟨⟨A.form, v +ᵥ A.anchor⟩, ⟨A, hA, rfl⟩, Y, hY, ?_⟩
    simp only [vadd_eq_add, smul_add, add_assoc]

private theorem strict_schedule_composition_step2_fine_sts_step1_reduce_iter_translate
    (τ : Substitution P) (j : ℕ) (v : Pt) (S : Set (PlacedTile P)) :
    τ.decomposeIter j (translateSet v S) =
      translateSet (τ.θ ^ j • v) (τ.decomposeIter j S) := by
  induction j with
  | zero => simp [Substitution.decomposeIter]
  | succ j ih =>
    show τ.decompose (τ.decomposeIter j (translateSet v S)) =
      translateSet (τ.θ ^ (j + 1) • v) (τ.decompose (τ.decomposeIter j S))
    rw [ih, strict_schedule_composition_step2_fine_sts_step1_reduce_translate,
      smul_smul, pow_succ']

private theorem strict_schedule_composition_step2_fine_sts_step1_reduce_iUnion
    (τ : Substitution P) (n : ℕ) (ι : Type) (S : ι → Set (PlacedTile P)) :
    τ.decomposeIter n (⋃ i, S i) = ⋃ i, τ.decomposeIter n (S i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change τ.decompose (τ.decomposeIter n (⋃ i, S i)) = _
    rw [ih]
    simp [Substitution.decompose, Substitution.decomposeIter, Set.mem_iUnion]
    rw [iUnion_comm]

private theorem strict_schedule_composition_step2_fine_sts_step1_reduce_biUnion
    (τ : Substitution P) (n : ℕ) {α : Type} (S : Set α)
    (f : α → Set (PlacedTile P)) :
    τ.decomposeIter n (⋃ A ∈ S, f A) =
      ⋃ A ∈ S, τ.decomposeIter n (f A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change τ.decompose (τ.decomposeIter n (⋃ A ∈ S, f A)) = _
    rw [ih]
    simp [Substitution.decompose, Substitution.decomposeIter, Set.mem_iUnion]

private theorem strict_schedule_composition_step2_fine_sts_step1_reduce_scatterTile
    (τ : Substitution P) (G : GroupedFamily P) (k : ℕ) (A : PlacedTile G.P') :
    τ.decomposeIter k (G.scatterTile A) =
      translateSet (τ.θ ^ k • A.anchor)
        (τ.decomposeIter k (G.dissect A.form).tiles) := by
  exact strict_schedule_composition_step2_fine_sts_step1_reduce_iter_translate
    τ k A.anchor (G.dissect A.form).tiles

private theorem strict_schedule_composition_step2_fine_sts_step1_reduce_scatter
    (τ : Substitution P) (G : GroupedFamily P) (k : ℕ)
    (S : Set (PlacedTile G.P')) :
    τ.decomposeIter k (G.scatter S) =
      ⋃ A ∈ S, translateSet (τ.θ ^ k • A.anchor)
        (τ.decomposeIter k (G.dissect A.form).tiles) := by
  rw [show G.scatter S = ⋃ A ∈ S, G.scatterTile A by rfl]
  rw [strict_schedule_composition_step2_fine_sts_step1_reduce_biUnion]
  congr 1
  funext A
  rw [strict_schedule_composition_step2_fine_sts_step1_reduce_scatterTile]

private theorem strict_schedule_composition_step2_fine_sts_step1_reduce_scatter_translate
    (G : GroupedFamily P) (v : Pt) (S : Set (PlacedTile G.P')) :
    G.scatter (translateSet v S) = translateSet v (G.scatter S) := by
  ext Z
  simp only [GroupedFamily.scatter, GroupedFamily.scatterTile, translateSet,
    Set.mem_iUnion, Set.mem_image, PlacedTile.translate]
  constructor
  · rintro ⟨i, ⟨x, hx, rfl⟩, y, hy, rfl⟩
    refine ⟨⟨y.form, x.anchor +ᵥ y.anchor⟩, ⟨x, hx, y, hy, rfl⟩, ?_⟩
    simp only [vadd_eq_add, add_assoc]
  · rintro ⟨z, ⟨i, hi, y, hy, rfl⟩, rfl⟩
    refine ⟨⟨i.form, v +ᵥ i.anchor⟩, ⟨i, hi, rfl⟩, y, hy, ?_⟩
    simp only [vadd_eq_add, add_assoc]

private theorem strict_schedule_composition_step2_fine_sts_step1_reduce_project_tile
    {P : Protoset} {τ : Substitution P} (Sys : StrictScheduleSystem τ)
    (X : PlacedTile Sys.dec.P') :
    Sys.dec.toDecoration.projTile '' Sys.σc.decomposeTile X =
      translateSet (Sys.σc.θ • X.anchor)
        (Sys.dec.toDecoration.projTile '' (Sys.σc.rule X.form).tiles) := by
  ext Z
  simp only [Substitution.decomposeTile, translateSet, Set.mem_image,
    PlacedTile.translate]
  constructor
  · rintro ⟨Y, ⟨B, hB, rfl⟩, rfl⟩
    refine ⟨Sys.dec.toDecoration.projTile B, ⟨B, hB, rfl⟩, ?_⟩
    rfl
  · rintro ⟨Y, ⟨B, hB, rfl⟩, rfl⟩
    refine ⟨⟨B.form, Sys.σc.θ • X.anchor +ᵥ B.anchor⟩,
      ⟨B, hB, rfl⟩, rfl⟩

private theorem strict_schedule_composition_step2_fine_sts_step1_reduce_tile
    {P : Protoset} {τ : Substitution P} (Sys : StrictScheduleSystem τ)
    (X : PlacedTile Sys.dec.P') :
    τ.decomposeIter Sys.GS.k (Sys.GS.G.scatter
      ({Sys.dec.toDecoration.projTile X} : Set (PlacedTile Sys.GS.G.P'))) =
      Sys.GS.G.scatter (Sys.dec.toDecoration.projTile ''
        (Sys.σc.decomposeTile X)) := by
  have hsingle : Sys.GS.G.scatter
      ({Sys.dec.toDecoration.projTile X} : Set (PlacedTile Sys.GS.G.P')) =
      Sys.GS.G.scatterTile (Sys.dec.toDecoration.projTile X) := by
    ext Z
    simp [GroupedFamily.scatter]
  rw [hsingle, strict_schedule_composition_step2_fine_sts_step1_reduce_scatterTile]
  have hchild : Sys.GS.G.scatter (Sys.dec.toDecoration.projTile ''
      (Sys.σc.decomposeTile X)) =
      translateSet (Sys.σc.θ • X.anchor)
        (Sys.GS.G.scatter (Sys.GS.σ.rule (Sys.dec.proj X.form)).tiles) := by
    rw [strict_schedule_composition_step2_fine_sts_step1_reduce_project_tile,
      strict_schedule_composition_step2_fine_sts_step1_reduce_scatter_translate,
      Sys.rule_proj]
  rw [hchild]
  rw [Sys.θ_eq, Sys.GS.θ_eq, Sys.GS.compat]
  rfl

private theorem strict_schedule_composition_step2_fine_sts_step1_reduce_image
    {P : Protoset} (G : GroupedFamily P) {α : Type}
    (f : α → PlacedTile G.P') (S : Set α) :
    G.scatter (f '' S) = ⋃ x ∈ S, G.scatter {f x} := by
  ext Z
  simp [GroupedFamily.scatter]

private theorem strict_schedule_composition_step2_fine_sts_step1_reduce_image_biUnion
    {P : Protoset} (G : GroupedFamily P) {α : Type}
    (f : α → PlacedTile G.P') (S : Set α) (U : α → Set α) :
    G.scatter (f '' (⋃ x ∈ S, U x)) =
      ⋃ x ∈ S, G.scatter (f '' U x) := by
  ext Z
  simp [GroupedFamily.scatter]

/-- Step 1 of the blueprint proof of `strict_schedule_composition_step2_fine_sts`: `rule_proj`,
`θ_eq` and `GroupedSubstitution.compat` show that decomposing the scattered projection of the
coloured composition `T''` exactly `Sys.GS.k` times lands on the scattered projection of `T`
(the coloured rule children of each tile of `T''`, scattered and projected, are precisely the
`Sys.GS.k`-fold decomposition of that tile's scattered projection). -/
private theorem strict_schedule_composition_step2_fine_sts_step1_reduce {P : Protoset}
    {τ : Substitution P} (Sys : StrictScheduleSystem τ)
    (T T'' : PlaneTiling Sys.dec.P') (hcomp : Sys.σc.IsComposition T'' T) :
    τ.decomposeIter Sys.GS.k (Sys.GS.G.scatter (Sys.dec.toDecoration.project T'').tiles) =
      Sys.GS.G.scatter (Sys.dec.toDecoration.project T).tiles := by
  change τ.decomposeIter Sys.GS.k
      (Sys.GS.G.scatter (Sys.dec.toDecoration.projTile '' T''.tiles)) =
    Sys.GS.G.scatter (Sys.dec.toDecoration.projTile '' T.tiles)
  rw [strict_schedule_composition_step2_fine_sts_step1_reduce_image,
    strict_schedule_composition_step2_fine_sts_step1_reduce_biUnion]
  rw [← hcomp]
  rw [show Sys.σc.decompose T''.tiles =
      ⋃ X ∈ T''.tiles, Sys.σc.decomposeTile X by rfl]
  rw [strict_schedule_composition_step2_fine_sts_step1_reduce_image_biUnion]
  apply congrArg (fun F : PlacedTile Sys.dec.P' → Set (PlacedTile P) =>
    ⋃ X ∈ T''.tiles, F X)
  funext X
  exact strict_schedule_composition_step2_fine_sts_step1_reduce_tile Sys X

/-- Step 1 of the blueprint proof of `strict_schedule_composition_step2_fine_sts_step2_dissect_sts`:
within a single grouped parent, the translated dissected patch is side-to-side by the
level-zero instance of the hypotheses on the dissected patches. -/
private theorem strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step1_within_group
    {P : Protoset} {τ : Substitution P} (G : GroupedFamily P)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (G.dissect α).tiles))
    (A : PlacedTile G.P') : SideToSideSet (G.scatterTile A) := by
  change SideToSideSet (translateSet A.anchor (G.dissect A.form).tiles)
  have hsts : SideToSideSet (G.dissect A.form).tiles := by
    simpa [Substitution.decomposeIter] using hΔ A.form 0
  intro X hX Y hY i j hXY
  rcases hX with ⟨X₀, hX₀, rfl⟩
  rcases hY with ⟨Y₀, hY₀, rfl⟩
  have hsideX : (X₀.translate A.anchor).side i = A.anchor +ᵥ X₀.side i := by
    change (A.anchor +ᵥ X₀.anchor) +ᵥ (P.disk X₀.form).side i =
      A.anchor +ᵥ (X₀.anchor +ᵥ (P.disk X₀.form).side i)
    rw [vadd_vadd]
    simp only [vadd_eq_add]
  have hsideY : (Y₀.translate A.anchor).side j = A.anchor +ᵥ Y₀.side j := by
    change (A.anchor +ᵥ Y₀.anchor) +ᵥ (P.disk Y₀.form).side j =
      A.anchor +ᵥ (Y₀.anchor +ᵥ (P.disk Y₀.form).side j)
    rw [vadd_vadd]
    simp only [vadd_eq_add]
  have hXY' : OverlapPos (X₀.side i) (Y₀.side j) := by
    obtain ⟨x, y, hxy, hseg⟩ := hXY
    refine ⟨-A.anchor +ᵥ x, -A.anchor +ᵥ y, ?_, ?_⟩
    · simpa using hxy
    · rw [hsideX, hsideY] at hseg
      rw [← vadd_segment]
      rintro z ⟨w, hw, rfl⟩
      exact ⟨by simpa [Set.mem_vadd_set_iff_neg_vadd_mem, add_assoc] using (hseg hw).1,
        by simpa [Set.mem_vadd_set_iff_neg_vadd_mem, add_assoc] using (hseg hw).2⟩
  have hEq := hsts X₀ hX₀ Y₀ hY₀ i j hXY'
  change (X₀.translate A.anchor).side i = (Y₀.translate A.anchor).side j
  rw [hsideX, hsideY]
  exact congrArg (fun s : Set Pt => A.anchor +ᵥ s) hEq

private lemma
strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_finite
    {x y : Pt} (hxy : x ≠ y) {n : ℕ}
    (s : Fin n → Set Pt) (hsub : segment ℝ x y ⊆ ⋃ i, s i)
    (hconv : ∀ i, Convex ℝ (s i)) : ∃ i, OverlapPos (segment ℝ x y) (s i) := by
  by_contra h
  push_neg at h
  have hss : ∀ i : Fin n, Set.Subsingleton (segment ℝ x y ∩ s i) := by
    intro i p hp q hq
    by_contra hpq
    have hseg : segment ℝ p q ⊆ segment ℝ x y ∩ s i :=
      (convex_segment _ _).inter (hconv i) |>.segment_subset hp hq
    exact (h i) ⟨p, q, hpq, hseg⟩
  have hfin : (⋃ i : Fin n, segment ℝ x y ∩ s i).Finite := by
    simpa using
      (Set.toFinite (Set.univ : Set (Fin n))).biUnion (fun i _ => (hss i).finite)
  have hseg : segment ℝ x y ⊆ ⋃ i : Fin n, segment ℝ x y ∩ s i := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hsub hz)
    exact Set.mem_iUnion.2 ⟨i, hz, hi⟩
  letI : Infinite (Set.Ioo (0 : ℝ) 1) := Set.Ioo.infinite (by norm_num)
  have hinf : (segment ℝ x y).Infinite := by
    apply Set.infinite_of_injective_forall_mem
      (f := fun t : Set.Ioo (0 : ℝ) 1 => AffineMap.lineMap x y t.1)
    · intro a b hab
      apply Subtype.ext
      exact (AffineMap.lineMap_injective ℝ hxy) hab
    · intro t
      rw [segment_eq_image_lineMap]
      exact ⟨t.1, Set.mem_Icc.mpr ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩, rfl⟩
  exact hinf (hfin.subset hseg)

private lemma
strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_side_carrier
    (X : PlacedTile P) (i : Fin (P.disk X.form).n) :
    X.side i ⊆ X.carrier := by
  have hfront :
      (P.disk X.form).side i ⊆ frontier (P.disk X.form).carrier := by
    rw [(P.disk X.form).frontier_eq]
    exact Set.subset_iUnion (fun j => (P.disk X.form).side j) i
  have hcar : frontier (P.disk X.form).carrier ⊆ (P.disk X.form).carrier :=
    (P.disk X.form).compact.isClosed.frontier_subset
  intro z hz
  change z ∈ X.anchor +ᵥ (P.disk X.form).side i at hz
  change z ∈ X.anchor +ᵥ (P.disk X.form).carrier
  rw [mem_vadd_set_iff_neg_vadd_mem] at hz ⊢
  exact hcar (hfront hz)

private lemma strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_regular
    (A : PlacedTile G.P') : closure (interior A.carrier) = A.carrier := by
  unfold PlacedTile.carrier
  rw [interior_vadd, closure_vadd, (G.P'.disk A.form).regular_closed]

private lemma
strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_frontier
    (A : PlacedTile G.P') :
    frontier A.carrier = ⋃ i : Fin (G.P'.disk A.form).n, A.side i := by
  have hclosed : IsClosed A.carrier := by
    rw [←
      strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_regular G A]
    exact isClosed_closure
  ext z
  constructor
  · intro hz
    rw [hclosed.frontier_eq] at hz
    have hcar : z ∈ A.carrier := hz.1
    have hint : z ∉ interior A.carrier := hz.2
    rw [PlacedTile.carrier] at hcar
    rw [PlacedTile.carrier, interior_vadd] at hint
    rw [mem_vadd_set_iff_neg_vadd_mem] at hcar hint
    have hz' : -A.anchor +ᵥ z ∈ frontier (G.P'.disk A.form).carrier := by
      rw [(G.P'.disk A.form).compact.isClosed.frontier_eq]
      exact ⟨hcar, hint⟩
    rw [(G.P'.disk A.form).frontier_eq] at hz'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz'
    exact Set.mem_iUnion.2 ⟨i, by
      change z ∈ A.anchor +ᵥ (G.P'.disk A.form).side i
      rw [mem_vadd_set_iff_neg_vadd_mem]
      exact hi⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    rw [hclosed.frontier_eq]
    constructor
    · exact
        strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_side_carrier
          A i hi
    · intro hzi
      rw [PlacedTile.side, PolygonalDisk.side] at hi
      rw [PlacedTile.carrier, interior_vadd] at hzi
      rw [mem_vadd_set_iff_neg_vadd_mem] at hi hzi
      have hfront :
          (G.P'.disk A.form).side i ⊆ frontier (G.P'.disk A.form).carrier := by
        rw [(G.P'.disk A.form).frontier_eq]
        exact Set.subset_iUnion (fun j => (G.P'.disk A.form).side j) i
      exact Set.disjoint_left.mp disjoint_interior_frontier hzi (hfront hi)

private lemma
strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_carrier
    (G : GroupedFamily P) (A : PlacedTile G.P')
    (X : PlacedTile P) (hX : X ∈ G.scatterTile A) : X.carrier ⊆ A.carrier := by
  rcases hX with ⟨X₀, hX₀, rfl⟩
  have hbase : X₀.carrier ⊆ (G.P'.disk A.form).carrier := by
    intro z hz
    rw [← G.support_eq A.form]
    exact Set.mem_iUnion.2 ⟨X₀, Set.mem_iUnion.2 ⟨hX₀, hz⟩⟩
  intro z hz
  change z ∈ (A.anchor +ᵥ X₀.anchor) +ᵥ (P.disk X₀.form).carrier at hz
  change z ∈ A.anchor +ᵥ (G.P'.disk A.form).carrier
  have hz' : z ∈ A.anchor +ᵥ (X₀.anchor +ᵥ (P.disk X₀.form).carrier) := by
    simpa only [vadd_vadd] using hz
  obtain ⟨w, hw, rfl⟩ := hz'
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  exact ⟨X₀.anchor +ᵥ w₀, hbase ⟨w₀, hw₀, rfl⟩, by simp [vadd_eq_add]⟩

private lemma
strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_translate
    (X : PlacedTile P) (v : Pt) (i : Fin (P.disk X.form).n) :
    (X.translate v).side i = v +ᵥ X.side i := by
  simp [PlacedTile.translate, PlacedTile.side, vadd_vadd]

private lemma
strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_overlap
    (X Y : PlacedTile P) (v : Pt)
    (i : Fin (P.disk X.form).n) (j : Fin (P.disk Y.form).n)
    (h : OverlapPos ((X.translate v).side i) ((Y.translate v).side j)) :
    OverlapPos (X.side i) (Y.side j) := by
  obtain ⟨x, y, hxy, hseg⟩ := h
  refine ⟨-v +ᵥ x, -v +ᵥ y, ?_, ?_⟩
  · simpa using hxy
  · rw [
      strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_translate,
      strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_translate]
      at hseg
    intro z hz
    have hz' : v +ᵥ z ∈ segment ℝ x y := by
      rw [segment_eq_image'] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      rw [segment_eq_image']
      exact ⟨t, ht, by simp only [vadd_eq_add]; abel⟩
    have hz'' := hseg hz'
    exact ⟨by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hz''.1,
      by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hz''.2⟩

private lemma
strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_side_eq
    {D E : PolygonalDisk} (hd : D = E) (i : Fin E.n) :
    D.side (Fin.cast (congrArg (fun Q : PolygonalDisk => Q.n) hd).symm i) = E.side i := by
  cases hd
  rfl

private lemma
strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_project
    {P : Protoset} (dec : SideDecoration P) (T : PlaneTiling dec.P')
    (hT : T.SideToSide) : SideToSideSet (dec.toDecoration.project T).tiles := by
  intro A hA B hB i j h
  rcases hA with ⟨A', hA', rfl⟩
  rcases hB with ⟨B', hB', rfl⟩
  let hdA := dec.disk_eq A'.form
  let hdB := dec.disk_eq B'.form
  let i' : Fin (dec.P'.disk A'.form).n :=
    Fin.cast (congrArg (fun D : PolygonalDisk => D.n) hdA).symm i
  let j' : Fin (dec.P'.disk B'.form).n :=
    Fin.cast (congrArg (fun D : PolygonalDisk => D.n) hdB).symm j
  have hi : A'.side i' = (dec.toDecoration.projTile A').side i := by
    change A'.anchor +ᵥ (dec.P'.disk A'.form).side i' =
      A'.anchor +ᵥ (P.disk (dec.proj A'.form)).side i
    exact congrArg (fun s : Set Pt => A'.anchor +ᵥ s)
      (strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_side_eq
        hdA i)
  have hj : B'.side j' = (dec.toDecoration.projTile B').side j := by
    change B'.anchor +ᵥ (dec.P'.disk B'.form).side j' =
      B'.anchor +ᵥ (P.disk (dec.proj B'.form)).side j
    exact congrArg (fun s : Set Pt => B'.anchor +ᵥ s)
      (strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_side_eq
        hdB j)
  have h' : OverlapPos (A'.side i') (B'.side j') := by
    rw [hi, hj]
    exact h
  have heq := hT A' hA' B' hB' i' j' h'
  rw [hi, hj] at heq
  exact heq

/-- Step 2 of the blueprint proof of `strict_schedule_composition_step2_fine_sts_step2_dissect_sts`:
for distinct projected parents in a proper decorated tiling, any positively overlapping
sides of their dissected tiles are equal. -/
private theorem strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group
    {P : Protoset} (G : GroupedFamily P) (dec : SideDecoration G.P')
    (T : PlaneTiling dec.P') (hp : dec.Proper T) :
    ∀ A ∈ dec.toDecoration.project T, ∀ B ∈ dec.toDecoration.project T, A ≠ B →
      ∀ X ∈ G.scatterTile A, ∀ Y ∈ G.scatterTile B,
        ∀ i j, OverlapPos (X.side i) (Y.side j) → X.side i = Y.side j := by
  intro A hA B hB hAB X hX Y hY i j hXY
  have hregA :=
    strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_regular G A
  have hregB :=
    strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_regular G B
  have hclosedA : IsClosed A.carrier := by
    rw [← hregA]
    exact isClosed_closure
  have hclosedB : IsClosed B.carrier := by
    rw [← hregB]
    exact isClosed_closure
  have hsideX :=
    strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_side_carrier
      X i
  have hsideY :=
    strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_side_carrier
      Y j
  have hXA :=
    strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_carrier
      G A X hX
  have hYB :=
    strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_carrier
      G B Y hY
  obtain ⟨x, y, hxy, hseg⟩ := hXY
  have hfrontA : segment ℝ x y ⊆ frontier A.carrier := by
    intro z hz
    have hzA : z ∈ A.carrier := hXA (hsideX (hseg hz).1)
    have hzB : z ∈ B.carrier := hYB (hsideY (hseg hz).2)
    rw [hclosedA.frontier_eq]
    refine ⟨hzA, ?_⟩
    intro hzint
    rw [← hregB, Metric.mem_closure_iff] at hzB
    obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 isOpen_interior z hzint
    obtain ⟨w, hwB, hzw⟩ := hzB ε hε
    have hwA : w ∈ interior A.carrier := hεB (by
      rw [Metric.mem_ball, dist_comm]
      exact hzw)
    exact Set.disjoint_left.mp
      ((dec.toDecoration.project T).disjoint hA hB hAB) hwA hwB
  have hfrontB : segment ℝ x y ⊆ frontier B.carrier := by
    intro z hz
    have hzA : z ∈ A.carrier := hXA (hsideX (hseg hz).1)
    have hzB : z ∈ B.carrier := hYB (hsideY (hseg hz).2)
    rw [hclosedB.frontier_eq]
    refine ⟨hzB, ?_⟩
    intro hzint
    rw [← hregA, Metric.mem_closure_iff] at hzA
    obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.1 isOpen_interior z hzint
    obtain ⟨w, hwA, hzw⟩ := hzA ε hε
    have hwB : w ∈ interior B.carrier := hεA (by
      rw [Metric.mem_ball, dist_comm]
      exact hzw)
    exact Set.disjoint_left.mp
      ((dec.toDecoration.project T).disjoint hA hB hAB).symm hwB hwA
  have hunionA : segment ℝ x y ⊆ ⋃ p : Fin (G.P'.disk A.form).n, A.side p := by
    rw [←
      strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_frontier G A]
    exact hfrontA
  obtain ⟨p, hpA⟩ :=
    strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_finite
        hxy (fun p : Fin (G.P'.disk A.form).n => A.side p)
      hunionA (fun p => by
        change Convex ℝ (A.anchor +ᵥ (G.P'.disk A.form).side p)
        exact (convex_segment _ _).vadd A.anchor)
  obtain ⟨u, v, huv, huvsub⟩ := hpA
  have hfrontBuv : segment ℝ u v ⊆ frontier B.carrier := by
    intro z hz
    exact hfrontB (huvsub hz).1
  have hunionBuv : segment ℝ u v ⊆ ⋃ q : Fin (G.P'.disk B.form).n, B.side q := by
    rw [←
      strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_frontier G B]
    exact hfrontBuv
  obtain ⟨q, hq⟩ :=
    strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_finite
        huv (fun q : Fin (G.P'.disk B.form).n => B.side q)
      hunionBuv (fun q => by
        change Convex ℝ (B.anchor +ᵥ (G.P'.disk B.form).side q)
        exact (convex_segment _ _).vadd B.anchor)
  obtain ⟨C, hC, k, hk⟩ := G.side_whole A.form p
  obtain ⟨D, hD, l, hl⟩ := G.side_whole B.form q
  have hCp : (C.translate A.anchor).side k = A.side p := by
    simpa [PlacedTile.translate, PlacedTile.side, vadd_vadd] using
      congrArg (fun s : Set Pt => A.anchor +ᵥ s) hk
  have hDl : (D.translate B.anchor).side l = B.side q := by
    simpa [PlacedTile.translate, PlacedTile.side, vadd_vadd] using
      congrArg (fun s : Set Pt => B.anchor +ᵥ s) hl
  have hXC : OverlapPos (X.side i) ((C.translate A.anchor).side k) := by
    refine ⟨u, v, huv, ?_⟩
    intro z hz
    exact ⟨(hseg (huvsub hz).1).1, hCp ▸ (huvsub hz).2⟩
  have hYD : OverlapPos (Y.side j) ((D.translate B.anchor).side l) := by
    obtain ⟨r, s, hrs, hrssub⟩ := hq
    refine ⟨r, s, hrs, ?_⟩
    intro z hz
    exact ⟨(hseg (huvsub (hrssub hz).1).1).2, hDl ▸ (hrssub hz).2⟩
  obtain ⟨X₀, hX₀, rfl⟩ := hX
  obtain ⟨Y₀, hY₀, rfl⟩ := hY
  have hXC₀ :=
    strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_overlap
      X₀ C A.anchor i k hXC
  have hYD₀ :=
    strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_overlap
      Y₀ D B.anchor j l hYD
  have hXeq := G.sts A.form X₀ hX₀ C hC i k hXC₀
  have hYeq := G.sts B.form Y₀ hY₀ D hD j l hYD₀
  have hXparent : (X₀.translate A.anchor).side i = A.side p := by
    rw [strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_translate,
      hXeq]
    simpa [PlacedTile.translate, PlacedTile.side, vadd_vadd] using hCp
  have hYparent : (Y₀.translate B.anchor).side j = B.side q := by
    rw [strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_translate,
      hYeq]
    simpa [PlacedTile.translate, PlacedTile.side, vadd_vadd] using hDl
  have hpq : A.side p = B.side q := by
    have hproj :=
      strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group_project
        dec T hp.1
    apply hproj A hA B hB p q
    obtain ⟨r, s, hrs, hrssub⟩ := hq
    exact ⟨r, s, hrs, fun z hz =>
      ⟨(huvsub (hrssub hz).1).2, (hrssub hz).2⟩⟩
  exact hXparent.trans (hpq.trans hYparent.symm)


/-- Dissected tiles of distinct projected parents of a proper decorated tiling meet side to side:
public form of `strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group`
(reused by `dissection_preserves_sts_sofic` in `LocalRules.lean`). -/
theorem dissect_cross_group_sideToSide {P : Protoset} (G : GroupedFamily P)
    (dec : SideDecoration G.P') (T : PlaneTiling dec.P') (hp : dec.Proper T) :
    ∀ A ∈ dec.toDecoration.project T, ∀ B ∈ dec.toDecoration.project T, A ≠ B →
      ∀ X ∈ G.scatterTile A, ∀ Y ∈ G.scatterTile B,
        ∀ i j, OverlapPos (X.side i) (Y.side j) → X.side i = Y.side j :=
  strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group G dec T hp

/-- Step 2 of the blueprint proof of `strict_schedule_composition_step2_fine_sts`: dissecting a
proper strict coloured tiling preserves side-to-sideness. Within one grouped tile the dissect is
STS by `hΔ` (the `j = 0` case); across two distinct tiles of the (side-to-side, by `hp`) projected
tiling, the grouped family's `side_whole`/`vertex_retained` structure forces any overlap of
dissect pieces to come from an overlap of the whole parent sides, which coincide. -/
private theorem strict_schedule_composition_step2_fine_sts_step2_dissect_sts {P : Protoset}
    {τ : Substitution P} (Sys : StrictScheduleSystem τ)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (Sys.GS.G.dissect α).tiles))
    (T : PlaneTiling Sys.dec.P') (hp : Sys.dec.Proper T) :
    SideToSideSet (Sys.GS.G.scatter (Sys.dec.toDecoration.project T).tiles) := by
  have hwithin :=
    strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step1_within_group
      Sys.GS.G hΔ
  have hcross :=
    strict_schedule_composition_step2_fine_sts_step2_dissect_sts_step2_cross_group
      Sys.GS.G Sys.dec T hp
  intro X hX Y hY i j hXY
  rcases Set.mem_iUnion.1 hX with ⟨A, hX⟩
  rcases Set.mem_iUnion.1 hX with ⟨hA, hXA⟩
  rcases Set.mem_iUnion.1 hY with ⟨B, hY⟩
  rcases Set.mem_iUnion.1 hY with ⟨hB, hYB⟩
  by_cases hAB : A = B
  · subst B
    exact hwithin A X hXA Y hYB i j hXY
  · exact hcross A hA B hB hAB X hXA Y hYB i j hXY

/-- Step 2 of the blueprint proof of `strict_schedule_composition`: the scattered projected
composition is STS at the fine level (rule_proj, θ_eq, GroupedSubstitution.compat reduce it to T,
then dissect preserves STS via hΔ). -/
private theorem strict_schedule_composition_step2_fine_sts {P : Protoset} {τ : Substitution P} (hτ : τ.STS)
    (Sys : StrictScheduleSystem τ)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (Sys.GS.G.dissect α).tiles))
    (T T'' : PlaneTiling Sys.dec.P') (hp : Sys.dec.Proper T)
    (hcomp : Sys.σc.IsComposition T'' T) :
    SideToSideSet (τ.decomposeIter Sys.GS.k
      (Sys.GS.G.scatter (Sys.dec.toDecoration.project T'').tiles)) := by
  have _ := hτ
  rw [strict_schedule_composition_step2_fine_sts_step1_reduce Sys T T'' hcomp]
  exact strict_schedule_composition_step2_fine_sts_step2_dissect_sts Sys hΔ T hp

/-- `lem:schedule-compose` (STS part): if a proper strict coloured tiling `T`
is the decomposition of a coloured tiling `T''`, then the grouped parents of
`T''` and all scattered intermediate original levels are STS.  The existence
of the exact proper legal composition `T''` is the strict-variant instance of
the control chapter's composition theorem and is not restated here. -/
theorem strict_schedule_composition (hτ : τ.STS)
    (Sys : StrictScheduleSystem τ)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (Sys.GS.G.dissect α).tiles))
    (T T'' : PlaneTiling Sys.dec.P') (hp : Sys.dec.Proper T)
    (hcomp : Sys.σc.IsComposition T'' T) :
    SideToSideSet (Sys.dec.toDecoration.projTile '' T''.tiles) ∧
      ∀ j ≤ Sys.GS.k, SideToSideSet
        (τ.decomposeIter j (Sys.GS.G.scatter (Sys.dec.toDecoration.projTile '' T''.tiles))) := by
  have halign := strict_schedule_composition_step1_aligned hτ Sys T T'' hp hcomp
  have hfine := strict_schedule_composition_step2_fine_sts hτ Sys hΔ T T'' hp hcomp
  simpa only [Decoration.project] using schedule_intermediate_sts τ Sys.GS.G hτ hΔ Sys.GS.k (Sys.dec.toDecoration.project T'') hfine halign

/-- Existence half of `lem:schedule-compose`: every proper strict coloured
plane tiling has an exact proper coloured composition. -/
def StrictScheduleSystem.HasCompositions {τ : Substitution P} (Sys : StrictScheduleSystem τ) :
    Prop :=
  ∀ T : PlaneTiling Sys.dec.P', Sys.dec.Proper T →
    ∃ T'' : PlaneTiling Sys.dec.P', Sys.dec.Proper T'' ∧ Sys.σc.IsComposition T'' T

/-- Completeness of the strict presentation (`thm:sts-stshierarchy`, "origin
chains give legal tiles"): every grouped `σ'`-hierarchy whose levels and whose
scattered intermediate original levels (the levels `τ^j Δ (seq' (n+1))`,
`0 ≤ j ≤ k`, between consecutive grouped levels; nothing below the bottom level
`seq' 0` is assumed, codex 13 October 2026) are all side-to-side is the
projection of a proper strict coloured plane tiling. -/
def StrictScheduleSystem.Complete {τ : Substitution P} (Sys : StrictScheduleSystem τ) : Prop :=
  ∀ seq' : ℕ → PlaneTiling Sys.GS.G.P',
    (∀ n, Sys.GS.σ.IsComposition (seq' (n + 1)) (seq' n)) →
    (∀ n, (seq' n).SideToSide) →
    (∀ n, ∀ j ≤ Sys.GS.k,
      SideToSideSet (τ.decomposeIter j (Sys.GS.G.scatter (seq' (n + 1)).tiles))) →
    ∃ T : PlaneTiling Sys.dec.P', Sys.dec.Proper T ∧ Sys.dec.toDecoration.project T = seq' 0

end Alignment

end Tilings

end
