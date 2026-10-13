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
  let p := (parentSide τ G m A a).1
  let q := (parentSide τ G m A a).2
  let S := {e ∈ fineOuterSides τ G m A | segment ℝ e.1 e.2 ⊆ segment ℝ p q}
  let I := sidesInside τ G m A a
  let L := {e ∈ S | p ∈ segment ℝ e.1 e.2}
  let R := {e ∈ S | q ∈ segment ℝ e.1 e.2}
  have hpq : p ≠ q := omitted_count_parent_endpoints_ne τ G m A a
  have hSfin : S.Finite := by
    apply (whole_side_ports_step2_length_bound_step1_all_edges_bound_step3_finite τ G m A a).subset
    intro e he
    exact he
  have hIfin : I.Finite := by
    apply hSfin.subset
    rintro e ⟨he, heopen⟩
    exact ⟨he, heopen.trans (openSegment_subset_segment ℝ p q)⟩
  have hLfin : L.Finite := hSfin.sep _
  have hRfin : R.Finite := hSfin.sep _
  have hL : L.ncard ≤ 1 := by
    rw [Set.ncard_le_one hLfin]
    intro e he f hf
    exact omitted_count_edge_unique_at_endpoint τ G m A p q e f hpq
      he.1.1 hf.1.1 he.1.2 hf.1.2 he.2 hf.2
  have hR : R.ncard ≤ 1 := by
    rw [Set.ncard_le_one hRfin]
    intro e he f hf
    apply omitted_count_edge_unique_at_endpoint τ G m A q p e f hpq.symm
    · exact he.1.1
    · exact hf.1.1
    · simpa [segment_symm] using he.1.2
    · simpa [segment_symm] using hf.1.2
    · exact he.2
    · exact hf.2
  have hsub : S ⊆ I ∪ (L ∪ R) := by
    intro e he
    by_cases heopen : segment ℝ e.1 e.2 ⊆ openSegment ℝ p q
    · exact Or.inl ⟨he.1, heopen⟩
    · rw [Set.not_subset] at heopen
      obtain ⟨z, hz, hzopen⟩ := heopen
      have hzparent := he.2 hz
      rw [← insert_endpoints_openSegment] at hzparent
      simp only [Set.mem_insert_iff] at hzparent
      rcases hzparent with hzp | hzq | hzopen'
      · exact Or.inr (Or.inl ⟨he, hzp ▸ hz⟩)
      · exact Or.inr (Or.inr ⟨he, hzq ▸ hz⟩)
      · exact False.elim (hzopen hzopen')
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
  sorry

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
