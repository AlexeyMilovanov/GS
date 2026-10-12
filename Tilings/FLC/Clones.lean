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
  sorry

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

/-- Step 3 of the blueprint proof of `three_le_genuineCount`: if the boundary of a
regular closed set is contained in a line, its interior is empty. -/
private lemma three_le_genuineCount_step3 (h_reg : closure (interior D.carrier) = D.carrier)
    (h : Collinear ℝ (frontier D.carrier)) :
    ¬ (interior D.carrier).Nonempty := by
  sorry

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

/-- Step 1 of the blueprint proof of `coarse_simple`: Every point on a coarse segment
belongs to a fine segment that is contained within the same coarse segment. -/
private lemma coarse_simple_step1 (i : Fin D.genuineCount) (x : Pt)
    (hx : x ∈ segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i))) :
    ∃ k : Fin D.n, x ∈ segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ∧ 
      segment ℝ (D.vertex k) (D.vertex (finRotate D.n k)) ⊆
        segment ℝ (D.coarseVertex i) (D.coarseVertex (finRotate D.genuineCount i)) := by
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
  sorry

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

/-- Step 6 of the blueprint proof of `finite_neighbourhoods`: orders n < k
have finitely many possibilities directly. -/
private lemma finite_neighbourhoods_step6 (τ : Substitution P) (k : ℕ) :
    {N | ∃ (n : ℕ) (hn : n < k) (p : P.Form), ∃ A ∈ τ.supertile n p,
      N = (A.form, translateSet (-A.anchor) (neighbourhood (τ.supertile n p) A))}.Finite := by
  sorry

/-- Step 5 of the blueprint proof of `finite_neighbourhoods`: there are finitely
many allowed crowns and each has a finite kth image, with finitely many selected
subpatches and distinguished tiles. -/
private lemma finite_neighbourhoods_step5 (τ : Substitution P) (h : τ.FLC) (k : ℕ) :
    (finite_neighbourhoods_CrownContexts τ k).Finite := by
  sorry

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
  sorry

/-- Step 1.2 of the blueprint proof of `childContext_realized`: `τ.decompose (translateSet v S) = translateSet (τ.θ • v) (τ.decompose S)`. -/
private lemma childContext_realized_step1_shift_step2_decompose_translateSet
    {P : Protoset} {τ : Substitution P} (v : Pt) (S : Set (PlacedTile P)) :
    τ.decompose (translateSet v S) = translateSet (τ.θ • v) (τ.decompose S) := by
  sorry

/-- Step 1.3 of the blueprint proof of `childContext_realized`: `τ.supertile (n+1) p = τ.decompose (τ.supertile n p)`. -/
private lemma childContext_realized_step1_shift_step3_supertile_succ
    {P : Protoset} {τ : Substitution P} (n : ℕ) (p : P.Form) :
    τ.supertile (n+1) p = τ.decompose (τ.supertile n p) := rfl

/-- Step 1.4 of the blueprint proof of `childContext_realized`: Anchor arithmetic. -/
private lemma childContext_realized_step1_shift_step4_anchor
    {P : Protoset} {τ : Substitution P} (A B : PlacedTile P) :
    -B.anchor +ᵥ τ.θ • -A.anchor = -(B.translate (τ.θ • A.anchor)).anchor := by
  sorry

/-- Step 1.5 of the blueprint proof of `childContext_realized`: Translate arithmetic. -/
private lemma childContext_realized_step1_shift_step5_translate_eq
    {P : Protoset} {τ : Substitution P} (A B : PlacedTile P) :
    B.translate (-(τ.θ • -A.anchor)) = B.translate (τ.θ • A.anchor) := by
  sorry

/-- Step 1.6 of the blueprint proof of `childContext_realized`: `neighbourhood (translateSet v S) A = translateSet v (neighbourhood S (A.translate (-v)))` -/
private lemma childContext_realized_step1_shift_step6_neighbourhood_translateSet
    {P : Protoset} (v : Pt) (S : Set (PlacedTile P)) (A : PlacedTile P) :
    neighbourhood (translateSet v S) A = translateSet v (neighbourhood S (A.translate (-v))) := by
  sorry

/-- Step 1.7 of the blueprint proof of `childContext_realized`: `τ.decompose (neighbourhood S A) = ...` -/
private lemma childContext_realized_step1_shift_step7_decompose_neighbourhood
    {P : Protoset} {τ : Substitution P} (S : Set (PlacedTile P)) (A B : PlacedTile P)
    (hB : B ∈ τ.decomposeTile A) :
    neighbourhood (τ.decompose (neighbourhood S A)) B = neighbourhood (τ.decompose S) B := by
  sorry

/-- Step 1.8 of the blueprint proof of `childContext_realized`: `B ∈ τ.decomposeTile ⟨c.form, 0⟩ → B.translate (τ.θ • A.anchor) ∈ τ.decomposeTile A` -/
private lemma childContext_realized_step1_shift_step8_translate_mem
    {P : Protoset} {τ : Substitution P} (A B : PlacedTile P)
    (hB : B ∈ τ.decomposeTile ⟨A.form, 0⟩) :
    B.translate (τ.θ • A.anchor) ∈ τ.decomposeTile A := by
  sorry

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
  sorry

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

/-- `lem:segment-rules`: a sofic presentation on decorated (e.g. clone) tiles,
given either by an arbitrary bounded local rule or by the strict side rule on
the refined listed sides, transfers through the carrier-preserving projection
to a sofic presentation (finite decoration + bounded local rule) of the
projected family on the original carriers.  Applied with
`d = cloneDecoration τ h`. -/
theorem forget_vertices_preserves_sofic (d : Decoration P) (G : Set (PlaneTiling d.P'))
    (hG : IsSofic G ∨ IsSideToSideSofic G) : IsSofic (d.project '' G) := by
  sorry

end FLC

end Tilings

end

