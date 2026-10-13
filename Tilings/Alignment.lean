import Tilings.Geometry.Grouping

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
    ∃ (e : Pt × Pt) (he : e ∈ fineOuterSides τ G m A.form)
      (e' : Pt × Pt) (he' : e' ∈ fineOuterSides τ G m A'.form),
      placedSeg ((τ.θ ^ m) • A.anchor) e = placedSeg ((τ.θ ^ m) • A'.anchor) e' ∧
      OverlapPos (segment ℝ c.1 c.2) (segment ℝ e.1 e.2) ∧
      OverlapPos (segment ℝ d.1 d.2) (segment ℝ e'.1 e'.2) := by
  sorry

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
  sorry

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
  sorry

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

/-- Step 2 of the blueprint proof of `schedule_intermediate_sts`:
Inside a block each original layer is already an STS supertile patch.
Thus, to check STS for the parent level, we only need to compare sides that
arise from opposite macroblock boundaries, which correspond to `top` layer sides. -/
private theorem schedule_intermediate_sts_step2_parents_sts
    (m : ℕ) (T' : PlaneTiling G.P')
    (h_align : ∀ (A A' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles)
       (c d : Pt × Pt)
       (hc : c ∈ layerSides τ G m A.form .top) (hd : d ∈ layerSides τ G m A'.form .top),
       OverlapPos (placedSeg ((τ.θ ^ m) • A.anchor) c)
         (placedSeg ((τ.θ ^ m) • A'.anchor) d) →
       placedSeg ((τ.θ ^ m) • A.anchor) c = placedSeg ((τ.θ ^ m) • A'.anchor) d) :
    SideToSideSet T'.tiles := by
  sorry

/-- Step 3 of the blueprint proof of `schedule_intermediate_sts`:
Inside a block each original layer is already an STS supertile patch.
Thus, to check STS for any intermediate layer, we only need to compare sides that
arise from opposite macroblock boundaries, which correspond to `level j` layer sides. -/
private theorem schedule_intermediate_sts_step3_levels_sts
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (G.dissect α).tiles))
    (m : ℕ) (T' : PlaneTiling G.P')
    (hfine : SideToSideSet (τ.decomposeIter m (G.scatter T'.tiles)))
    (h_align : ∀ (A A' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles)
       (j : Fin m) (c d : Pt × Pt)
       (hc : c ∈ layerSides τ G m A.form (.level j))
       (hd : d ∈ layerSides τ G m A'.form (.level j)),
       OverlapPos (placedSeg ((τ.θ ^ m) • A.anchor) c)
         (placedSeg ((τ.θ ^ m) • A'.anchor) d) →
       placedSeg ((τ.θ ^ m) • A.anchor) c = placedSeg ((τ.θ ^ m) • A'.anchor) d) :
    ∀ j ≤ m, SideToSideSet (τ.decomposeIter j (G.scatter T'.tiles)) := by
  sorry

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

/-- Step 1 of the blueprint proof of `whole_side_ports_step2_length_bound_step1_all_edges_bound`: sum of lengths of fine edges on the parent side. -/
private lemma whole_side_ports_step2_length_bound_step1_all_edges_bound_step1_sum_lengths
    (τ : Substitution P) (G : GroupedFamily P) (m : ℕ)
    (A : G.P'.Form) (a : Fin (G.P'.disk A).n)
    (h_fin : {e ∈ fineOuterSides τ G m A | segment ℝ e.1 e.2 ⊆
        segment ℝ (parentSide τ G m A a).1 (parentSide τ G m A a).2}.Finite) :
    dist (parentSide τ G m A a).1 (parentSide τ G m A a).2 ≤
      ∑ e ∈ h_fin.toFinset, dist e.1 e.2 := by
  sorry

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
    {e ∈ fineOuterSides τ G m A | segment ℝ e.1 e.2 ⊆
        segment ℝ (parentSide τ G m A a).1 (parentSide τ G m A a).2}.Finite :=
  (whole_side_ports_step2_length_bound_step1_all_edges_bound_step3_finite_aux2 τ G m A).sep _

/-- Step 1 of the blueprint proof of `whole_side_ports_step2_length_bound`: the length of the
parent side is bounded by the total number of fine edges on it times D. -/
private lemma whole_side_ports_step2_length_bound_step1_all_edges_bound
    (τ : Substitution P) (G : GroupedFamily P) (M : MeshConstants P) (m : ℕ)
    (A : G.P'.Form) (a : Fin (G.P'.disk A).n) :
    dist (parentSide τ G m A a).1 (parentSide τ G m A a).2 ≤
      ({e ∈ fineOuterSides τ G m A | segment ℝ e.1 e.2 ⊆
        segment ℝ (parentSide τ G m A a).1 (parentSide τ G m A a).2}.ncard : ℝ) * M.D := by
  have h_fin := whole_side_ports_step2_length_bound_step1_all_edges_bound_step3_finite τ G m A a
  rw [Set.ncard_eq_toFinset_card _ h_fin]
  calc dist (parentSide τ G m A a).1 (parentSide τ G m A a).2
    _ ≤ ∑ e ∈ h_fin.toFinset, dist e.1 e.2 :=
      whole_side_ports_step2_length_bound_step1_all_edges_bound_step1_sum_lengths τ G m A a h_fin
    _ ≤ ∑ e ∈ h_fin.toFinset, M.D := by
      apply Finset.sum_le_sum
      intro e he
      have he2 := h_fin.mem_toFinset.mp he
      exact whole_side_ports_step2_length_bound_step1_all_edges_bound_step2_edge_bound τ G M m A e he2.1
    _ = (h_fin.toFinset.card : ℝ) * M.D := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Step 2 of the blueprint proof of `whole_side_ports_step2_length_bound`: the number of fine
edges on the parent side is bounded by the number of strictly inside fine edges plus 2. -/
private lemma whole_side_ports_step2_length_bound_step2_omitted_count
    (τ : Substitution P) (G : GroupedFamily P) (m : ℕ) (A : G.P'.Form) (a : Fin (G.P'.disk A).n) :
    {e ∈ fineOuterSides τ G m A | segment ℝ e.1 e.2 ⊆
        segment ℝ (parentSide τ G m A a).1 (parentSide τ G m A a).2}.ncard ≤
      (sidesInside τ G m A a).ncard + 2 := by
  sorry

/-- Step 2 of the blueprint proof of `whole_side_ports`: the length of the parent
side is bounded by the number of inside edges times D plus the omitted length 2D. -/
private lemma whole_side_ports_step2_length_bound (M : MeshConstants P) (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) :
    dist (parentSide τ G m A a).1 (parentSide τ G m A a).2 ≤
      ((sidesInside τ G m A a).ncard : ℝ) * M.D + 2 * M.D := by
  have h1 := whole_side_ports_step2_length_bound_step1_all_edges_bound τ G M m A a
  have h2 := whole_side_ports_step2_length_bound_step2_omitted_count τ G m A a
  have h2r : ({e ∈ fineOuterSides τ G m A | segment ℝ e.1 e.2 ⊆
      segment ℝ (parentSide τ G m A a).1 (parentSide τ G m A a).2}.ncard : ℝ) ≤
      ((sidesInside τ G m A a).ncard : ℝ) + 2 := by exact_mod_cast h2
  have hd : 0 ≤ M.D := le_of_lt M.D_pos
  have h3 : ({e ∈ fineOuterSides τ G m A | segment ℝ e.1 e.2 ⊆
      segment ℝ (parentSide τ G m A a).1 (parentSide τ G m A a).2}.ncard : ℝ) * M.D ≤
      (((sidesInside τ G m A a).ncard : ℝ) + 2) * M.D := mul_le_mul_of_nonneg_right h2r hd
  rw [add_mul] at h3
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
  sorry

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

/-- Step 1 of the blueprint proof of `whole_side_ports_distinct_step3_rank`: the set of inside sides is finite. -/
private lemma whole_side_ports_distinct_step3_rank_step1_finite (τ : Substitution P)
    (G : GroupedFamily P) (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) : (sidesInside τ G m A a).Finite := by
  sorry

/-- Step 2 of the blueprint proof of `whole_side_ports_distinct_step3_rank_step2_inj`: the interiors of distinct inside sides are disjoint. -/
private lemma whole_side_ports_distinct_step3_rank_step2_inj_step1_disjoint (τ : Substitution P)
    (G : GroupedFamily P) (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) (e1 e2 : Pt × Pt)
    (h1 : e1 ∈ sidesInside τ G m A a) (h2 : e2 ∈ sidesInside τ G m A a)
    (hne : e1 ≠ e2) : Disjoint (openSegment ℝ e1.1 e1.2) (openSegment ℝ e2.1 e2.2) := by
  sorry

/-- Step 2 of the blueprint proof of `whole_side_ports_distinct_step3_rank_step2_inj`: sides with disjoint interiors have distinct sideKeys. -/
private lemma whole_side_ports_distinct_step3_rank_step2_inj_step2_key_ne (τ : Substitution P)
    (G : GroupedFamily P) (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) (e1 e2 : Pt × Pt)
    (h1 : e1 ∈ sidesInside τ G m A a) (h2 : e2 ∈ sidesInside τ G m A a)
    (hdisj : Disjoint (openSegment ℝ e1.1 e1.2) (openSegment ℝ e2.1 e2.2)) :
    sideKey (parentDir τ G m A a) e1 ≠ sideKey (parentDir τ G m A a) e2 := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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

/-- Step 1 of the blueprint proof of `strict_schedule_composition`: boundary-edge lifting — every
fine outer side is the projection of an outer side of a coloured rule child, so
schedule_spec/schedule_colour + properness give aligned schedules. -/
private theorem strict_schedule_composition_step1_aligned {P : Protoset} {τ : Substitution P} (hτ : τ.STS)
    (Sys : StrictScheduleSystem τ)
    (T T'' : PlaneTiling Sys.dec.P') (hp : Sys.dec.Proper T)
    (hcomp : Sys.σc.IsComposition T'' T) :
    SchedulesAligned τ Sys.GS.G Sys.GS.k (Sys.dec.toDecoration.project T'') := by
  sorry

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
  sorry

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
