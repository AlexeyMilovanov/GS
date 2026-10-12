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
  sorry

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

/-- Step 1 of the blueprint proof of `whole_side_ports_step2_length_bound`: the length of the
parent side is bounded by the total number of fine edges on it times D. -/
private lemma whole_side_ports_step2_length_bound_step1_all_edges_bound
    (τ : Substitution P) (G : GroupedFamily P) (M : MeshConstants P) (m : ℕ)
    (A : G.P'.Form) (a : Fin (G.P'.disk A).n) :
    dist (parentSide τ G m A a).1 (parentSide τ G m A a).2 ≤
      ({e ∈ fineOuterSides τ G m A | segment ℝ e.1 e.2 ⊆
        segment ℝ (parentSide τ G m A a).1 (parentSide τ G m A a).2}.ncard : ℝ) * M.D := by
  sorry

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

/-- Step 2 of the blueprint proof of `whole_side_ports_distinct_step3_rank`: `sideKey` is injective on the inside sides. -/
private lemma whole_side_ports_distinct_step3_rank_step2_inj (τ : Substitution P)
    (G : GroupedFamily P) (m : ℕ) (A : G.P'.Form)
    (a : Fin (G.P'.disk A).n) : (sidesInside τ G m A a).InjOn (sideKey (parentDir τ G m A a)) := by
  sorry

/-- Step 3 of the blueprint proof of `whole_side_ports_distinct_step3_rank`: an abstract lemma showing that any rank is attained. -/
private lemma whole_side_ports_distinct_step3_rank_step3_exists (X : Set (Pt × Pt))
    (h_fin : X.Finite) (u : Pt) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ X.ncard)
    (h_inj : X.InjOn (sideKey u)) :
    ∃ e ∈ X, rankIn X u e = k := by
  sorry

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

/-- Step 1 of the blueprint proof of `whole_side_ports_coincide`: the global canonical direction
of the coincident parent sides is the same. -/
private lemma whole_side_ports_coincide_step1_parentDir_eq (m : ℕ)
    (A A' : PlacedTile G.P') (a : Fin (G.P'.disk A.form).n) (a' : Fin (G.P'.disk A'.form).n)
    (hside : placedSeg ((τ.θ ^ m) • A.anchor) (parentSide τ G m A.form a) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (parentSide τ G m A'.form a')) :
    parentDir τ G m A.form a = parentDir τ G m A'.form a' := by
  sorry

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
    (r : Fin 5) :
    placedSeg ((τ.θ ^ m) • A.anchor) (port τ G m A.form a r) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (port τ G m A'.form a' r) := by
  sorry

/-- `lem:whole-ports` (coincidence): in a grouped plane tiling with STS fine
level and aligned schedules, physically coincident parent sides have the same
physical port lists, numbered in the global direction. -/
theorem whole_side_ports_coincide (m : ℕ) (T' : PlaneTiling G.P')
    (hfine : SideToSideSet (τ.decomposeIter m (G.scatter T'.tiles)))
    (halign : SchedulesAligned τ G m T')
    (A A' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles)
    (a : Fin (G.P'.disk A.form).n) (a' : Fin (G.P'.disk A'.form).n)
    (hside : placedSeg ((τ.θ ^ m) • A.anchor) (parentSide τ G m A.form a) =
      placedSeg ((τ.θ ^ m) • A'.anchor) (parentSide τ G m A'.form a')) :
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
  exact whole_side_ports_coincide_step5_port_eq τ G m A A' a a' f hf h1 h3 h2 r

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
  sorry


end Alignment

end Tilings

end
