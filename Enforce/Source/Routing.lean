import Enforce.Source.Sites

/-!
# Internal skeletons, principal components, birth-ascent routing, and Req′

DEVIATION: the standard skeleton and primitive facets in this file are expressed
in the unexpanded prototype `A`. Applying `σ^k` gives precisely the sets in `σ^k A`
of V4 1.24--1.25. This common invertible linear change of coordinates preserves
all inclusions, incidences, connected components, and recorded role words.
-/

open Set

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- P19, V4 1.24, preceding definition: a descendant's full prototype frame
in the unexpanded root, obtained by pulling its native placement back by `σ⁻ʲ`. -/
def prototypeDescendantFrame (A : S.ι) (j : ℕ) (w : S.RoleWord A j) :
    E d ≃ᵃ[ℝ] E d :=
  (S.nativeTile A j w).frame.toAffineEquiv.trans (S.σ ^ j).symm.toAffineEquiv

/-- P19, V4 1.24, preceding definition: a primitive facet with its birth address.
The local carrier has an existential owning side, so the two paired sides represent
one facet. No arbitrary orientation or duplicate side is built into facet identity.
DEVIATION: its root carrier is normalized in the unexpanded prototype, as above. -/
structure PrimitiveFacet (S : SubstSystem d) (A : S.ι) where
  /-- P19, V4 1.24: depth of the birth parent within the root. -/
  depth : ℕ
  /-- P19, V4 1.24: complete role word to that birth parent. -/
  word : S.RoleWord A depth
  /-- P19, V4 1.24: provider carrier in the standard expanded birth-parent prototype. -/
  localCarrier : Set (E d)
  /-- P19, V4 1.24: an actual first-generation internal facet, with an owning cell name. -/
  realization : ∃ (i : S.I (S.nativeTile A depth word).ty)
    (f : FacetName S (S.child (S.nativeTile A depth word).ty i).ty),
    localCarrier = placedSet (S.child (S.nativeTile A depth word).ty i).frame
      f.val.carrier ∧
    relint localCarrier ⊆ interior (S.supertile 1 (S.nativeTile A depth word).ty)

namespace PrimitiveFacet

variable {A : S.ι}

/-- P19, V4 1.24: birth-parent type. -/
def birthType (f : PrimitiveFacet S A) : S.ι := (S.nativeTile A f.depth f.word).ty

/-- P19, V4 1.24: the tree address of the birth parent. -/
def birthAddress (f : PrimitiveFacet S A) : Σ j : ℕ, S.RoleWord A j := ⟨f.depth, f.word⟩

/-- P19, V4 1.24: the birth-parent prototype frame in root coordinates. -/
def birthFrame (f : PrimitiveFacet S A) : E d ≃ᵃ[ℝ] E d :=
  prototypeDescendantFrame A f.depth f.word

/-- P19, V4 1.24: normalized carrier of the primitive facet. -/
def carrier (f : PrimitiveFacet S A) : Set (E d) :=
  f.birthFrame '' (S.σ.symm '' f.localCarrier)

/-- P21, V4 1.25: birth-parent node in the standard height-`k` root.
All routing statements require `f.depth < k`, so this height is positive. -/
def birthNode (f : PrimitiveFacet S A) (k : ℕ) : FramedNode S :=
  S.descendantNode A (k - f.depth) f.depth f.word

/-- P21, V4 1.25: a birth-parent cell in root coordinates. -/
def birthCell (f : PrimitiveFacet S A) (e : Cell d) : Set (E d) :=
  f.birthFrame '' e.carrier

/-- P21, V4 1.25: a cell of an immediate child of the birth parent. -/
def childCell (f : PrimitiveFacet S A) (i : S.I f.birthType) (e : Cell d) : Set (E d) :=
  f.birthFrame '' (S.σ.symm '' placedSet (S.child f.birthType i).frame e.carrier)

/-- P21, V4 1.25: the immediate child's entire support in root coordinates. -/
def childSupport (f : PrimitiveFacet S A) (i : S.I f.birthType) : Set (E d) :=
  f.birthFrame '' (S.σ.symm '' placedSet (S.child f.birthType i).frame
    (S.proto (S.child f.birthType i).ty).carrier)

/-- P21, V4 1.25: listedness in a named child of the birth parent. -/
def ChildLists (f : PrimitiveFacet S A) (i : S.I f.birthType) (q : E d) : Prop :=
  ∃ v ∈ (S.cx (S.child f.birthType i).ty).vertices, q ∈ f.childCell i v

/-- P21, V4 1.25: a vertex of the primitive facet, named in an owning child's complex. -/
def IsVertex (f : PrimitiveFacet S A) (q : E d) : Prop :=
  q ∈ f.carrier ∧ ∃ (i : S.I f.birthType)
    (e : FacetName S (S.child f.birthType i).ty),
      f.localCarrier = placedSet (S.child f.birthType i).frame e.val.carrier ∧
        f.ChildLists i q

/-- P21, V4 1.25: common-listed seed in the complete immediate subdivision. -/
def CommonListed (f : PrimitiveFacet S A) (q : E d) : Prop :=
  ∀ i : S.I f.birthType, q ∈ f.childSupport i → f.ChildLists i q

end PrimitiveFacet

/-- P19, V4 1.24, preceding definition: primitive facets born at depth `j`. -/
def primitiveFacetAtDepth (S : SubstSystem d) (A : S.ι) (j : ℕ) :
    Set (PrimitiveFacet S A) := {f | f.depth = j}

/-- P19, V4 1.24: finitely many primitive facets through any fixed finite depth. -/
theorem primitiveFacets_finite (S : SubstSystem d) (A : S.ι) (k : ℕ) :
    {f : PrimitiveFacet S A | f.depth < k}.Finite := by
  sorry

/-- P19, V4 1.24, preceding definition: the depth-`k` internal skeleton,
normalized in `A`; only native facets not contained in the root boundary enter it.
DEVIATION: apply `σ^k` to recover the printed ambient skeleton in `σ^k A`. -/
def internalSkeleton (S : SubstSystem d) (A : S.ι) (k : ℕ) : Set (E d) :=
  {x | ∃ (w : S.RoleWord A k) (f : FacetName S (S.nativeTile A k w).ty),
    ¬ (S.nativeTile A k w).cell 0 f.val ⊆ frontier (S.supertile k A) ∧
      (S.σ ^ k) x ∈ (S.nativeTile A k w).cell 0 f.val}

/-- P19, V4 1.24, preceding definition: the internal skeleton is exactly the
union of primitive facets born before depth `k`. -/
theorem internalSkeleton_eq_primitives (S : SubstSystem d) (A : S.ι) (k : ℕ) :
    internalSkeleton S A k = ⋃ f : {f : PrimitiveFacet S A // f.depth < k},
      f.val.carrier := by
  sorry

/-- P20, V4 1.24: a nonempty actual connected component of the internal skeleton. -/
def IsSkeletonComponent (S : SubstSystem d) (A : S.ι) (k : ℕ)
    (E₀ : Set (E d)) : Prop :=
  ∃ x ∈ internalSkeleton S A k, E₀ = connectedComponentIn (internalSkeleton S A k) x

/-- P20, V4 1.24: the set `E_A` includes every primitive facet meeting the
chosen connected component, at all birth depths smaller than `k`. -/
def principalFacets (S : SubstSystem d) (A : S.ι) (k : ℕ)
    (E₀ : Set (E d)) : Set (PrimitiveFacet S A) :=
  {f | f.depth < k ∧ (f.carrier ∩ E₀).Nonempty}

/-- Step 1 of the V4 proof of `principal_component` (V4 1.24): "For a native
tile `t` let `U(t)` be the unbounded component ... and `K(t) = ℝᵈ ∖ U(t)`".
For a compact set in dimension at least two, this is the set together with the
bounded components of its complement; points of the set have empty components. -/
private def principal_component_step1_filledHull (t : Set (E d)) : Set (E d) :=
  {x | Bornology.IsBounded (connectedComponentIn tᶜ x)}

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"`K(t) = ℝᵈ ∖ U(t)`". Points of the original set belong to the filled hull. -/
private theorem principal_component_step1_hull_geometry_step1_contains (t : Set (E d)) :
    t ⊆ principal_component_step1_filledHull t := by
  intro x hx
  change Bornology.IsBounded (connectedComponentIn tᶜ x)
  rw [connectedComponentIn_eq_empty (by simpa using hx)]
  exact Bornology.isBounded_empty

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"cavities ... are filled in `K(t)`". Each bounded complementary component is open
and is contained in the interior of the filled hull. -/
private theorem principal_component_step1_hull_geometry_step2_cavity_open
    {t : Set (E d)} (ht : IsClosed t) {x : E d}
    (hx : x ∈ principal_component_step1_filledHull t) :
    connectedComponentIn tᶜ x ⊆ interior (principal_component_step1_filledHull t) := by
  apply interior_maximal _ ht.isOpen_compl.connectedComponentIn
  intro y hy
  change Bornology.IsBounded (connectedComponentIn tᶜ y)
  exact connectedComponentIn_eq hy ▸ hx

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"`U(t)` is open ... and its frontier is contained in `∂t`". -/
private theorem principal_component_step1_hull_geometry_step3_closed_frontier
    {t : Set (E d)} (ht : IsClosed t) :
    IsClosed (principal_component_step1_filledHull t) ∧
      frontier (principal_component_step1_filledHull t) ⊆ frontier t := by
  have hcontains := principal_component_step1_hull_geometry_step1_contains t
  have hclosed : IsClosed (principal_component_step1_filledHull t) := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_forall_mem_open.mpr
    intro x hx
    have hxt : x ∈ tᶜ := fun h => hx (hcontains h)
    refine ⟨connectedComponentIn tᶜ x, ?_, ht.isOpen_compl.connectedComponentIn,
      mem_connectedComponentIn hxt⟩
    intro y hy hyK
    apply hx
    change Bornology.IsBounded (connectedComponentIn tᶜ x)
    change Bornology.IsBounded (connectedComponentIn tᶜ y) at hyK
    exact (connectedComponentIn_eq hy).symm ▸ hyK
  refine ⟨hclosed, ?_⟩
  intro x hx
  have hxK := (frontier_subset_iff_isClosed.mpr hclosed) hx
  have hxt : x ∈ t := by
    by_contra hxt
    exact hx.2 (principal_component_step1_hull_geometry_step2_cavity_open ht hxK
      (mem_connectedComponentIn hxt))
  exact ⟨ht.closure_eq.symm ▸ hxt, fun hi => hx.2 (interior_mono hcontains hi)⟩

/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"every point ... is a limit of points of `int t` (regular closedness)".
Adding open complementary components preserves regular closedness. -/
private theorem principal_component_step1_hull_geometry_step4_regular
    {t : Set (E d)} (ht : IsClosed t) (hreg : IsRegularClosed t) :
    IsRegularClosed (principal_component_step1_filledHull t) := by
  have hclosed := (principal_component_step1_hull_geometry_step3_closed_frontier ht).1
  apply Set.Subset.antisymm (closure_minimal interior_subset hclosed)
  intro x hx
  by_cases hxt : x ∈ t
  · rw [← hreg] at hxt
    exact closure_mono
      (interior_mono (principal_component_step1_hull_geometry_step1_contains t)) hxt
  · exact subset_closure (principal_component_step1_hull_geometry_step2_cavity_open ht hx
      (mem_connectedComponentIn hxt))

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"a point outside `conv t` is separated from `t` by a hyperplane, hence joined to
infinity in the complement of `t`". -/
private theorem principal_component_step1_hull_geometry_step5_convex_bound
    {t : Set (E d)} (hne : t.Nonempty) (hc : IsClosed (convexHull ℝ t)) :
    principal_component_step1_filledHull t ⊆ convexHull ℝ t := by
  intro x hx
  by_contra hxc
  obtain ⟨f, a, hfa, hax⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ t) hc hxc
  obtain ⟨y, hy⟩ := hne
  have hfy : f y < f x := (hfa y (subset_convexHull ℝ t hy)).trans hax
  have hhalf : {z | f x ≤ f z} ⊆ connectedComponentIn tᶜ x := by
    apply (convex_halfSpace_ge f.toLinearMap.isLinear (f x)).isPreconnected.subset_connectedComponentIn
      (show f x ≤ f x from le_rfl)
    intro z hz hzt
    exact (not_lt_of_ge hz) ((hfa z (subset_convexHull ℝ t hzt)).trans hax)
  have hb : Bornology.IsBounded (f '' connectedComponentIn tᶜ x) :=
    f.lipschitz.isBounded_image hx
  obtain ⟨M, hM⟩ := hb.bddAbove
  let r := (max 0 (M - f x) + 1) / (f x - f y)
  have hr : 0 ≤ r := le_of_lt (div_pos (by positivity) (sub_pos.mpr hfy))
  have hrval : r * (f x - f y) = max 0 (M - f x) + 1 :=
    div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hfy))
  have hzval : f (x + r • (x - y)) = f x + r * (f x - f y) := by
    simp only [map_add, map_smul, map_sub, smul_eq_mul]
  have hz : x + r • (x - y) ∈ connectedComponentIn tᶜ x := by
    apply hhalf
    change f x ≤ f (x + r • (x - y))
    rw [hzval]
    nlinarith
  have hMz := hM (Set.mem_image_of_mem f hz)
  rw [hzval, hrval] at hMz
  linarith [le_max_right 0 (M - f x)]

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"`∂t` is ... compact" and "`K(t) ⊆ conv t`". The finite polyhedral presentation
makes the convex hull compact, also after an affine change of coordinates. -/
private theorem principal_component_step1_hull_geometry_step6_convex_compact
    (P : PolyManifoldDomain d) (F : E d ≃ᵃ[ℝ] E d) :
    IsCompact (convexHull ℝ (F '' P.carrier)) := by
  classical
  obtain ⟨s, hs⟩ := P.polyhedral
  let v : Finset (E d) := s.biUnion id
  have hconv : convexHull ℝ P.carrier = convexHull ℝ (v : Set (E d)) := by
    apply Set.Subset.antisymm
    · apply convexHull_min _ (convex_convexHull ℝ _)
      rw [hs]
      intro x hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
      apply convexHull_mono (t := (v : Set (E d))) _ hxp
      intro z hz
      exact Finset.mem_biUnion.mpr ⟨p, hp, hz⟩
    · apply convexHull_mono
      intro x hx
      obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx
      rw [hs]
      exact Set.mem_iUnion₂.mpr ⟨p, hp, subset_convexHull ℝ _ hxp⟩
  change IsCompact (convexHull ℝ (F.toAffineMap '' P.carrier))
  rw [← F.toAffineMap.image_convexHull, hconv]
  exact (Set.Finite.isCompact_convexHull v.finite_toSet).image
    F.toHomeomorphOfFiniteDimensional.continuous

/-- Step 7 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"a connected union of facets of `t`". Lower-dimensional cells cannot separate
an open convex set: two segments through a generic intermediate point avoid them. -/
private theorem principal_component_step1_hull_geometry_step7_avoid_cells
    (L : Finset (Cell d)) (hL : ∀ e ∈ L, e.dim + 1 < d)
    {V : Set (E d)} (hV : IsOpen V) (hVconv : Convex ℝ V)
    {a b : E d} (haV : a ∈ V) (hbV : b ∈ V)
    (ha : ∀ e ∈ L, a ∉ e.carrier) (hb : ∀ e ∈ L, b ∉ e.carrier) :
    ∃ J : Set (E d), IsPreconnected J ∧ a ∈ J ∧ b ∈ J ∧ J ⊆ V ∧
      ∀ e ∈ L, Disjoint J e.carrier := by
  classical
  have hspan (e : Cell d) (he : e.dim + 1 < d) (a : E d) :
      Dense (affineSpan ℝ (insert a e.carrier) : Set (E d))ᶜ := by
    have hdim := finrank_vectorSpan_insert_le_set ℝ e.carrier a
    have hedim : Module.finrank ℝ (vectorSpan ℝ e.carrier) = e.dim := by
      rw [← direction_affineSpan]
      exact e.flat.dimension
    have hproper : affineSpan ℝ (insert a e.carrier) ≠ ⊤ := by
      intro htop
      have hh := congrArg (fun S : AffineSubspace ℝ (E d) =>
        Module.finrank ℝ S.direction) htop
      change Module.finrank ℝ (affineSpan ℝ (insert a e.carrier)).direction =
        Module.finrank ℝ (⊤ : AffineSubspace ℝ (E d)).direction at hh
      rw [direction_affineSpan, AffineSubspace.direction_top, finrank_top,
        finrank_euclideanSpace, Fintype.card_fin] at hh
      omega
    apply interior_eq_empty_iff_dense_compl.mp
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hconv := (affineSpan ℝ (insert a e.carrier)).convex
    have htop := hconv.interior_nonempty_iff_affineSpan_eq_top.mp ⟨x, hx⟩
    rw [AffineSubspace.affineSpan_coe] at htop
    exact hproper htop
  have hsegment (e : Cell d) {a z : E d} (ha : a ∉ e.carrier)
      (hz : z ∉ affineSpan ℝ (insert a e.carrier)) :
      Disjoint (segment ℝ a z) e.carrier := by
    apply Set.disjoint_left.mpr
    intro q hq hqe
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    have hr0 : r ≠ 0 := by
      intro hr0
      subst r
      exact ha (by simpa using hqe)
    have haA : a ∈ affineSpan ℝ (insert a e.carrier) := mem_affineSpan ℝ (mem_insert a _)
    have hqA : AffineMap.lineMap a z r ∈ affineSpan ℝ (insert a e.carrier) :=
      mem_affineSpan ℝ (mem_insert_of_mem _ hqe)
    have hzA := AffineMap.lineMap_mem (r⁻¹) haA hqA
    rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ hr0, AffineMap.lineMap_apply_one] at hzA
    exact hz hzA
  have hdense (x : E d) : Dense (⋂ e ∈ L,
      (affineSpan ℝ (insert x e.carrier) : Set (E d))ᶜ) := by
    apply dense_biInter_of_isOpen
      (fun e _ => (affineSpan ℝ (insert x e.carrier)).closed_of_finiteDimensional.isOpen_compl)
      L.finite_toSet.countable
    intro e he
    exact hspan e (hL e he) x
  have hopen (x : E d) : IsOpen (⋂ e ∈ L,
      (affineSpan ℝ (insert x e.carrier) : Set (E d))ᶜ) :=
    isOpen_biInter_finset (fun e _ =>
      (affineSpan ℝ (insert x e.carrier)).closed_of_finiteDimensional.isOpen_compl)
  obtain ⟨z, hzV, hz⟩ :=
    ((hdense a).inter_of_isOpen_left (hdense b) (hopen a)).inter_open_nonempty V hV ⟨a, haV⟩
  refine ⟨segment ℝ a z ∪ segment ℝ b z,
    IsPreconnected.union' ⟨z, right_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩
      (convex_segment (𝕜 := ℝ) a z).isPreconnected
      (convex_segment (𝕜 := ℝ) b z).isPreconnected,
    Or.inl (left_mem_segment ℝ _ _), Or.inr (left_mem_segment ℝ _ _),
    union_subset (hVconv.segment_subset haV hzV) (hVconv.segment_subset hbV hzV), ?_⟩
  intro e he
  exact disjoint_union_left.mpr
    ⟨hsegment e (ha e he) (Set.mem_iInter₂.mp hz.1 e he),
      hsegment e (hb e he) (Set.mem_iInter₂.mp hz.2 e he)⟩

/-- Step 8 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"its frontier is contained in `∂t`; it is nonempty". A proper closed filling
has a frontier point in the relative interior of a facet of the original domain. -/
private theorem principal_component_step1_hull_geometry_step8_frontier_facet
    (P : PolyManifoldDomain d) (C : CellComplex P) {H : Set (E d)}
    (hHclosed : IsClosed H) (hPH : P.carrier ⊆ H) (hHproper : H ≠ univ)
    (hHfront : frontier H ⊆ frontier P.carrier) :
    ∃ (p : E d) (f : Cell d), p ∈ frontier H ∧ f ∈ C.facets ∧ p ∈ relint f.carrier := by
  classical
  obtain ⟨a, ha⟩ := P.interior_nonempty
  obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem H).mp hHproper
  have hcellfront (e : Cell d) (he : e ∈ C.cells) : e.carrier ⊆ frontier P.carrier := by
    rw [← e.flat.regularClosed]
    apply closure_minimal _ isClosed_frontier
    intro x hx
    rw [← C.cover]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hx⟩
  let L := C.cells.filter (fun e => e.dim + 1 < d)
  obtain ⟨J, hJ, haJ, hbJ, -, hJL⟩ :=
    principal_component_step1_hull_geometry_step7_avoid_cells L
      (fun e he => (Finset.mem_filter.mp he).2) isOpen_univ convex_univ
      (Set.mem_univ a) (Set.mem_univ b)
      (fun e he hae => (hcellfront e (Finset.mem_filter.mp he).1 hae).2 ha)
      (fun e he hbe => hb (hPH ((frontier_subset_iff_isClosed.mpr P.compact.isClosed)
        (hcellfront e (Finset.mem_filter.mp he).1 hbe))))
  have hmeet : (J ∩ frontier H).Nonempty := by
    by_contra hmeet
    have havoid : ∀ x ∈ J, x ∉ frontier H := fun x hx hxf => hmeet ⟨x, hx, hxf⟩
    have hsplit : J ⊆ interior H ∪ Hᶜ := by
      intro x hx
      by_cases hxH : x ∈ H
      · left
        by_contra hxint
        exact havoid x hx ⟨hHclosed.closure_eq.symm ▸ hxH, hxint⟩
      · exact Or.inr hxH
    obtain ⟨x, -, hxint, hxout⟩ := hJ (interior H) Hᶜ isOpen_interior hHclosed.isOpen_compl
      hsplit ⟨a, haJ, interior_mono hPH ha⟩ ⟨b, hbJ, hb⟩
    exact hxout (interior_subset hxint)
  obtain ⟨p, hpJ, hpH⟩ := hmeet
  have hpP := hHfront hpH
  rw [← C.cover] at hpP
  obtain ⟨f, hf, hpf⟩ := Set.mem_iUnion₂.mp hpP
  refine ⟨p, f, hpH, ?_, hpf⟩
  apply Finset.mem_filter.mpr
  refine ⟨hf, ?_⟩
  by_contra hdim
  have hfL : f ∈ L := Finset.mem_filter.mpr ⟨hf, by
    have := C.dim_lt f hf
    have hd : 2 ≤ d := Fact.out
    omega⟩
  exact Set.disjoint_left.mp (hJL f hfL) hpJ (f.flat.regularClosed ▸ subset_closure hpf)

/-- Step 9 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"near which the complement locally is on the other side". At a relative-interior
facet point this follows from the half-ball description of V4 1.0(a). -/
private theorem principal_component_step1_hull_geometry_step9_facet_side
    (P : PolyManifoldDomain d) (C : CellComplex P) (F : E d ≃ᵃ[ℝ] E d)
    (f : Cell d) (hf : f ∈ C.facets) (p : E d) (hp : p ∈ relint f.carrier) :
    ∃ V : Set (E d), IsOpen V ∧ F p ∈ V ∧
      IsPreconnected (V ∩ (F '' P.carrier)ᶜ) := by
  obtain ⟨r, hr, v, -, -, -, hhalf⟩ := facet_halfball P C f hf p hp
  have hcompl : Metric.ball p r ∩ P.carrierᶜ =
      Metric.ball p r ∩ {x | inner ℝ v x < inner ℝ v p} := by
    ext x
    have hh := Set.ext_iff.mp hhalf x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, inner_sub_right] at hh
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, hxc⟩
      refine ⟨hx, ?_⟩
      by_contra hn
      exact hxc ((hh.mpr ⟨sub_nonneg.mpr (le_of_not_gt hn), hx⟩).1)
    · rintro ⟨hx, hxv⟩
      exact ⟨hx, fun hxc => (not_le_of_gt hxv) (sub_nonneg.mp (hh.mp ⟨hxc, hx⟩).1)⟩
  have hconn : IsPreconnected (Metric.ball p r ∩ P.carrierᶜ) := by
    rw [hcompl]
    exact ((convex_ball p r).inter
      (convex_halfSpace_lt (innerSL ℝ v).toLinearMap.isLinear (inner ℝ v p))).isPreconnected
  let e := F.toHomeomorphOfFiniteDimensional
  refine ⟨e '' Metric.ball p r, e.isOpenMap _ Metric.isOpen_ball,
    Set.mem_image_of_mem e (Metric.mem_ball_self hr), ?_⟩
  change IsPreconnected ((e '' Metric.ball p r) ∩ (e '' P.carrier)ᶜ)
  rw [← e.image_compl, ← Set.image_inter e.injective]
  exact hconn.image _ e.continuous.continuousOn

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"`∂t` is a compact `(d-1)`-manifold". Transport the relative Euclidean charts
across a homeomorphism, in particular across the affine placement of a tile. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step1_transport_charts
    {n : ℕ} {K L : Set (E d)} (e : K ≃ₜ L)
    (hK : IsLocallyEuclidean n K) : IsLocallyEuclidean n L := by
  intro p
  obtain ⟨U, hU, hp, V, hV, ⟨f⟩⟩ := hK (e.symm p)
  refine ⟨e '' U, e.isOpenMap _ hU, ?_, V, hV, ⟨(e.image U).symm.trans f⟩⟩
  exact ⟨e.symm p, hp, e.apply_symm_apply p⟩

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"with finitely many components, each a closed hypersurface". A manifold is locally
connected, so its connected components are relatively open and inherit its charts. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step2_component_charts
    {n : ℕ} {K : Set (E d)} (hK : IsLocallyEuclidean n K)
    (p : E d) (hp : p ∈ K) :
    IsLocallyEuclidean n (connectedComponentIn K p) := by
  letI : LocallyConnectedSpace K := by
    apply locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr
    intro q W hW
    obtain ⟨U, hU, hqU, V, hV, ⟨e⟩⟩ := hK q
    letI : LocallyConnectedSpace V := hV.locallyConnectedSpace
    letI : LocallyConnectedSpace U := e.isOpenEmbedding.locallyConnectedSpace
    have hW' : (Subtype.val : U → K) ⁻¹' W ∈ nhds (⟨q, hqU⟩ : U) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hW
    obtain ⟨O, hOW, hO, hqO, hOconn⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance _ _ hW'
    refine ⟨Subtype.val '' O, ?_, hU.isOpenMap_subtype_val _ hO,
      ⟨⟨q, hqU⟩, hqO, rfl⟩, hOconn.image _ continuous_subtype_val.continuousOn⟩
    rintro x ⟨y, hy, rfl⟩
    exact hOW hy
  let Γ := connectedComponentIn K p
  have hΓK : Γ ⊆ K := connectedComponentIn_subset _ _
  have hΓopen : IsOpen ((Subtype.val : K → E d) ⁻¹' Γ) := by
    dsimp only [Γ]
    rw [connectedComponentIn_eq_image hp, Set.preimage_image_eq _ Subtype.val_injective]
    exact isOpen_connectedComponent
  have hi : Topology.IsOpenEmbedding (Set.inclusion hΓK) :=
    Topology.IsOpenEmbedding.inclusion hΓK hΓopen
  intro q
  obtain ⟨U, hU, hqU, V, hV, ⟨e⟩⟩ := hK (Set.inclusion hΓK q)
  let f := U.restrictPreimage (Set.inclusion hΓK)
  have hf : Topology.IsOpenEmbedding f :=
    hi.restrict (fun _ hx => hx) (hU.preimage hi.continuous)
  let g := (Subtype.val : V → E n) ∘ e ∘ f
  have hg : Topology.IsOpenEmbedding g :=
    hV.isOpenEmbedding_subtypeVal.comp (e.isOpenEmbedding.comp hf)
  exact ⟨(Set.inclusion hΓK) ⁻¹' U, hU.preimage hi.continuous, hqU,
    Set.range g, hg.isOpen_range, ⟨hg.isEmbedding.toHomeomorph⟩⟩

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"`∂t` is a compact `(d-1)`-manifold ... each a closed hypersurface". The selected
boundary component is nonempty, compact, connected, and locally Euclidean. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step3_compact_component
    (P : PolyManifoldDomain d) (F : E d ≃ᵃ[ℝ] E d)
    (p : E d) (hp : p ∈ frontier (F '' P.carrier)) :
    IsCompact (connectedComponentIn (frontier (F '' P.carrier)) p) ∧
      IsConnected (connectedComponentIn (frontier (F '' P.carrier)) p) ∧
      IsLocallyEuclidean (d - 1) (connectedComponentIn (frontier (F '' P.carrier)) p) := by
  have ht : IsCompact (F '' P.carrier) :=
    P.compact.image F.toHomeomorphOfFiniteDimensional.continuous
  have hclosed : IsClosed (connectedComponentIn (frontier (F '' P.carrier)) p) := by
    rw [connectedComponentIn_eq_image hp]
    exact isClosed_frontier.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hmanifold : IsLocallyEuclidean (d - 1) (frontier (F '' P.carrier)) := by
    let e := F.toHomeomorphOfFiniteDimensional
    exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step1_transport_charts
      ((e.image (frontier P.carrier)).trans (Homeomorph.setCongr (e.image_frontier P.carrier)))
      P.frontier_manifold
  refine ⟨ht.of_isClosed_subset hclosed ?_, isConnected_connectedComponentIn_iff.mpr hp,
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step2_component_charts hmanifold p hp⟩
  exact (connectedComponentIn_subset _ _).trans
    (frontier_subset_iff_isClosed.mpr ht.isClosed)

/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"placed prototiles". An affine placement preserves the finite
convex hull presentation of a polyhedron. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step4_affine_polyhedral
    {Q : Set (E d)} (hQ : Polyhedron Q) (F : E d ≃ᵃ[ℝ] E d) :
    Polyhedron (F '' Q) := by
  classical
  obtain ⟨s, rfl⟩ := hQ
  refine ⟨s.image (fun p => p.image F), ?_⟩
  have himage (p : Finset (E d)) :
      F '' convexHull ℝ (p : Set (E d)) = convexHull ℝ (p.image F : Set (E d)) := by
    rw [Finset.coe_image]
    exact F.toAffineMap.image_convexHull (p : Set (E d))
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp hy
    refine Set.mem_iUnion₂.mpr ⟨p.image F, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    rw [← himage]
    exact Set.mem_image_of_mem F hyp
  · intro hx
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    rw [← himage] at hxq
    obtain ⟨y, hy, rfl⟩ := hxq
    exact ⟨y, Set.mem_iUnion₂.mpr ⟨p, hp, hy⟩, rfl⟩

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral` (V4 1.24):
"a connected union of facets of `t`". Extend an affinely independent vertex set
to an affine basis. Nonnegative barycentric coordinates, with zero coordinates
outside the original set, give a finite closed halfspace presentation of the simplex. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step1_simplex_halfspaces
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

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral` (V4 1.24):
"a connected union of facets of `t`". Carathéodory's theorem expresses each
finite convex hull as a finite union of simplices. Their affine inequalities give
a finite union of intersections of closed halfspaces. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step2_halfspace_presentation
    {K : Set (E d)} (hK : Polyhedron K) :
    ∃ S : Finset (Finset (E d →ᵃ[ℝ] ℝ)),
      K = ⋃ q ∈ S, {x | ∀ f ∈ q, 0 ≤ f x} := by
  classical
  obtain ⟨s, rfl⟩ := hK
  have hrep (t : Finset (E d)) : ∃ q : Finset (E d →ᵃ[ℝ] ℝ),
      AffineIndependent ℝ ((↑) : t → E d) →
        convexHull ℝ (t : Set (E d)) = {x | ∀ f ∈ q, 0 ≤ f x} := by
    by_cases ht : AffineIndependent ℝ ((↑) : t → E d)
    · obtain ⟨q, hq⟩ :=
        principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step1_simplex_halfspaces t ht
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
/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral` (V4 1.24):
"a connected union of facets of `t`". An extreme point of a finite intersection
of closed halfspaces is uniquely determined among feasible points by its active
constraints: otherwise the line through another such point extends past it. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step3_active_unique
    (q : Finset (E d →ᵃ[ℝ] ℝ)) {x y : E d}
    (hx : x ∈ ({z | ∀ f ∈ q, 0 ≤ f z} : Set (E d)).extremePoints ℝ)
    (hy : ∀ f ∈ q, 0 ≤ f y)
    (hactive : ∀ f ∈ q, f x = 0 → f y = 0) : x = y := by
  let L : ℝ →ᵃ[ℝ] E d := AffineMap.lineMap y x
  have hnear : ∀ᶠ t in 𝓝 (1 : ℝ), ∀ f ∈ q, 0 ≤ f (L t) := by
    apply (Filter.eventually_all_finset q).mpr
    intro f hf
    by_cases hfx : f x = 0
    · have hfy := hactive f hf hfx
      exact Filter.Eventually.of_forall fun t => by
        simp [L, f.apply_lineMap, hfx, hfy]
    · have hpos : 0 < f x := lt_of_le_of_ne (hx.1 f hf) (Ne.symm hfx)
      have hc : Continuous (fun t => f (L t)) :=
        f.continuous_of_finiteDimensional.comp L.continuous_of_finiteDimensional
      have hp : 0 < f (L 1) := by simpa [L] using hpos
      exact (hc.continuousAt.eventually_const_lt hp).mono fun _ ht => ht.le
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let t : ℝ := 1 + ε / 2
  have ht : 1 < t := by dsimp [t]; linarith
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hLt : ∀ f ∈ q, 0 ≤ f (L t) := hball (by
    change dist t 1 < ε
    rw [Real.dist_eq, abs_of_pos (by dsimp [t]; linarith)]
    dsimp [t]
    linarith)
  apply Eq.symm
  apply hx.2 hy hLt
  have hmem := lineMap_mem_openSegment ℝ y (L t)
    (show t⁻¹ ∈ Ioo (0 : ℝ) 1 from ⟨inv_pos.mpr ht0, inv_lt_one_of_one_lt₀ ht⟩)
  simpa [L, AffineMap.lineMap_lineMap_right, ne_of_gt ht0] using hmem

/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral` (V4 1.24):
"a connected union of facets of `t`". A bounded intersection of finitely many
closed halfspaces has finitely many extreme points, since their active constraint
sets are distinct. Compactness and Krein–Milman express it as their convex hull. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step4_bounded_halfspaces
    (q : Finset (E d →ᵃ[ℝ] ℝ))
    (hb : Bornology.IsBounded {x | ∀ f ∈ q, 0 ≤ f x}) :
    ∃ p : Finset (E d), {x | ∀ f ∈ q, 0 ≤ f x} = convexHull ℝ (p : Set (E d)) := by
  classical
  let C : Set (E d) := {x | ∀ f ∈ q, 0 ≤ f x}
  let active (x : E d) := q.filter fun f => f x = 0
  have hfinite : (C.extremePoints ℝ).Finite := by
    apply Set.Finite.of_injOn (f := active) (t := (q.powerset : Set _))
    · intro x _
      exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    · intro x hx y hy hxy
      apply principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step3_active_unique
        q hx hy.1
      intro f hf hfx
      have hmem : f ∈ active x := Finset.mem_filter.mpr ⟨hf, hfx⟩
      rw [hxy] at hmem
      exact (Finset.mem_filter.mp hmem).2
    · exact Finset.finite_toSet _
  have hC : C = ⋂ f ∈ q, {x | 0 ≤ f x} := by ext x; simp [C]
  have hclosed : IsClosed C := by
    rw [hC]
    exact isClosed_biInter fun f _ => isClosed_le continuous_const f.continuous_of_finiteDimensional
  have hconv : Convex ℝ C := by
    rw [hC]
    exact convex_iInter fun f => convex_iInter fun _ =>
      (convex_Ici (0 : ℝ)).affine_preimage f
  refine ⟨hfinite.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact (hfinite.isClosed_convexHull.closure_eq.symm.trans
    (closure_convexHull_extremePoints
      (Metric.isCompact_of_isClosed_isBounded hclosed hb) hconv)).symm

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral` (V4 1.24):
"a connected union of facets of `t`". For a nonempty region defined by strict
affine inequalities, its closure is obtained by making those inequalities weak.
Segments from a strictly feasible point approximate every weakly feasible point. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step5_closure_strict
    (q : Finset (E d →ᵃ[ℝ] ℝ))
    (hne : ({x | ∀ f ∈ q, 0 < f x} : Set (E d)).Nonempty) :
    closure {x | ∀ f ∈ q, 0 < f x} = {x | ∀ f ∈ q, 0 ≤ f x} := by
  have hclosed : IsClosed {x : E d | ∀ f ∈ q, 0 ≤ f x} := by
    simp only [Set.setOf_forall]
    exact isClosed_biInter fun f _ => isClosed_le continuous_const f.continuous_of_finiteDimensional
  apply Set.Subset.antisymm
  · exact closure_minimal (fun x hx f hf => (hx f hf).le) hclosed
  · obtain ⟨y, hy⟩ := hne
    intro x hx
    have hseg : openSegment ℝ y x ⊆ {z | ∀ f ∈ q, 0 < f z} := by
      rw [openSegment_eq_image_lineMap]
      rintro z ⟨t, ht, rfl⟩ f hf
      rw [f.apply_lineMap, AffineMap.lineMap_apply_ring]
      exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr ht.2) (hy f hf)) (mul_nonneg ht.1.le (hx f hf))
    exact closure_mono hseg (segment_subset_closure_openSegment (right_mem_segment ℝ y x))

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral` (V4 1.24):
"a connected union of facets of `t`". Finite De Morgan expansion expresses the
complement of the closed halfspace pieces as a finite union of nonempty regions
defined by strict affine inequalities. Discarding empty regions permits taking closures. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step6_complement_regions
    (S : Finset (Finset (E d →ᵃ[ℝ] ℝ))) :
    ∃ T : Finset (Finset (E d →ᵃ[ℝ] ℝ)),
      (⋃ q ∈ S, {x | ∀ f ∈ q, 0 ≤ f x})ᶜ = ⋃ t ∈ T, {x | ∀ f ∈ t, 0 < f x} ∧
      ∀ t ∈ T, ({x | ∀ f ∈ t, 0 < f x} : Set (E d)).Nonempty := by
  classical
  let A := S.biUnion id
  let T₀ := A.powerset.filter fun t =>
    (∀ q ∈ S, ∃ f ∈ q, f ∈ t) ∧ ({x | ∀ f ∈ t, f x < 0} : Set (E d)).Nonempty
  let neg (t : Finset (E d →ᵃ[ℝ] ℝ)) := t.image fun f => -f
  have hneg (t : Finset (E d →ᵃ[ℝ] ℝ)) (x : E d) :
      (∀ f ∈ neg t, 0 < f x) ↔ ∀ f ∈ t, f x < 0 := by
    constructor
    · intro hx f hf
      have h := hx (-f) (Finset.mem_image.mpr ⟨f, hf, rfl⟩)
      simpa using h
    · intro hx f hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
      simpa using hx g hg
  refine ⟨T₀.image neg, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      have hviol : ∀ q ∈ S, ∃ f ∈ q, f x < 0 := by
        intro q hq
        by_contra hn
        apply hx
        refine Set.mem_iUnion₂.mpr ⟨q, hq, ?_⟩
        intro f hf
        by_contra hfx
        exact hn ⟨f, hf, lt_of_not_ge hfx⟩
      let t := A.filter fun f => f x < 0
      have ht : t ∈ T₀ := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_, ?_⟩
        · intro q hq
          obtain ⟨f, hfq, hfx⟩ := hviol q hq
          exact ⟨f, hfq, Finset.mem_filter.mpr
            ⟨Finset.mem_biUnion.mpr ⟨q, hq, hfq⟩, hfx⟩⟩
        · exact ⟨x, fun f hf => (Finset.mem_filter.mp hf).2⟩
      refine Set.mem_iUnion₂.mpr ⟨neg t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
      exact (hneg t x).mpr fun f hf => (Finset.mem_filter.mp hf).2
    · intro hx hxS
      obtain ⟨r, hr, hxr⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hxS
      obtain ⟨f, hfq, hft⟩ := (Finset.mem_filter.mp ht).2.1 q hq
      exact (not_lt_of_ge (hxq f hfq)) ((hneg t x).mp hxr f hft)
  · intro r hr
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp ht).2.2
    exact ⟨x, (hneg t x).mpr hx⟩

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"a connected union of facets of `t`". Subdividing the finitely many convex pieces along their
supporting hyperplanes expresses the frontier as another finite union of convex
hulls. This statement makes no manifold or separation assertion. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral
    {Q : Set (E d)} (hQ : Polyhedron Q) : Polyhedron (frontier Q) := by
  classical
  have hcompact : IsCompact Q := by
    obtain ⟨s, hs⟩ := hQ
    rw [hs]
    exact s.isCompact_biUnion fun p _ => p.finite_toSet.isCompact_convexHull
  obtain ⟨S, hS⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step2_halfspace_presentation hQ
  obtain ⟨T, hT, hne⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step6_complement_regions S
  have hclosure : closure Qᶜ = ⋃ t ∈ T, {x | ∀ f ∈ t, 0 ≤ f x} := by
    rw [hS, hT, Finset.closure_biUnion]
    apply Set.iUnion_congr
    intro t
    apply Set.iUnion_congr
    intro ht
    exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step5_closure_strict
      t (hne t ht)
  let I := S.product T
  have hrep (u : I) : ∃ p : Finset (E d),
      {x | ∀ f ∈ u.val.1 ∪ u.val.2, 0 ≤ f x} = convexHull ℝ (p : Set (E d)) := by
    apply principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step4_bounded_halfspaces
    apply hcompact.isBounded.subset
    intro x hx
    rw [hS]
    exact Set.mem_iUnion₂.mpr ⟨u.val.1, (Finset.mem_product.mp u.property).1,
      fun f hf => hx f (Finset.mem_union_left _ hf)⟩
  choose p hp using hrep
  refine ⟨Finset.univ.image p, ?_⟩
  ext x
  rw [frontier_eq_closure_inter_closure, hcompact.isClosed.closure_eq, hclosure]
  constructor
  · rintro ⟨hxQ, hxT⟩
    rw [hS] at hxQ
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hxQ
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hxT
    let u : I := ⟨(q, t), Finset.mem_product.mpr ⟨hq, ht⟩⟩
    refine Set.mem_iUnion₂.mpr ⟨p u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [← hp u]
    intro f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · exact hxq f hf
    · exact hxt f hf
  · intro hx
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
    rw [← hp u] at hxv
    refine ⟨?_, ?_⟩
    · rw [hS]
      exact Set.mem_iUnion₂.mpr ⟨u.val.1, (Finset.mem_product.mp u.property).1,
        fun f hf => hxv f (Finset.mem_union_left _ hf)⟩
    · exact Set.mem_iUnion₂.mpr ⟨u.val.2, (Finset.mem_product.mp u.property).2,
        fun f hf => hxv f (Finset.mem_union_right _ hf)⟩

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"a connected component of a finite union of closed connected sets contains every
member it meets". Select exactly those convex pieces meeting the component. The
argument also covers the empty component of a point outside the polyhedron. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step6_component_polyhedral
    {Q : Set (E d)} (hQ : Polyhedron Q) (p : E d) :
    Polyhedron (connectedComponentIn Q p) := by
  classical
  obtain ⟨s, hs⟩ := hQ
  let Γ := connectedComponentIn Q p
  refine ⟨s.filter (fun t => (convexHull ℝ (t : Set (E d)) ∩ Γ).Nonempty), ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    have hxQ : x ∈ Q := connectedComponentIn_subset _ _ hx
    rw [hs] at hxQ
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hxQ
    exact Set.mem_iUnion₂.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, x, hxt, hx⟩, hxt⟩
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hts, z, hzt, hzΓ⟩ := Finset.mem_filter.mp ht
    have htQ : convexHull ℝ (t : Set (E d)) ⊆ Q := by
      rw [hs]
      exact Set.subset_iUnion₂_of_subset t hts Set.Subset.rfl
    have hsub := (convex_convexHull ℝ (t : Set (E d))).isPreconnected.subset_connectedComponentIn hzt htQ
    rw [← connectedComponentIn_eq hzΓ] at hsub
    exact hsub hxt

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation` (V4 1.24):
"a connected union of facets of `t`". Cut the convex pieces by all their defining
hyperplanes. The resulting bounded sign cells cover the original polyhedron and
any two meet in a common convex face, expressed by `IsExtreme`. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step1_common_refinement {Q : Set (E d)} (hQ : Polyhedron Q) :
    ∃ T : Finset (Finset (E d)),
      Q = ⋃ p ∈ T, convexHull ℝ (p : Set (E d)) ∧
      ∀ p ∈ T, ∀ q ∈ T,
        IsExtreme ℝ (convexHull ℝ (p : Set (E d)))
          (convexHull ℝ (p : Set (E d)) ∩ convexHull ℝ (q : Set (E d))) := by
  classical
  have hcompact : IsCompact Q := by
    obtain ⟨s, hs⟩ := hQ
    rw [hs]
    exact s.isCompact_biUnion fun p _ => p.finite_toSet.isCompact_convexHull
  obtain ⟨S, hS⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step2_halfspace_presentation hQ
  let A := S.biUnion id
  let T := A.powerset.filter fun t => ∃ q ∈ S, q ⊆ t
  let C (t : Finset (E d →ᵃ[ℝ] ℝ)) : Set (E d) :=
    {x | ∀ f ∈ A, if f ∈ t then 0 ≤ f x else f x ≤ 0}
  have hsub (t : T) : C t.val ⊆ Q := by
    obtain ⟨q, hq, hqt⟩ := (Finset.mem_filter.mp t.property).2
    intro x hx
    rw [hS]
    refine Set.mem_iUnion₂.mpr ⟨q, hq, ?_⟩
    intro f hf
    have hfA : f ∈ A := Finset.mem_biUnion.mpr ⟨q, hq, hf⟩
    simpa only [if_pos (hqt hf)] using hx f hfA
  have hrep (t : T) : ∃ p : Finset (E d), C t.val = convexHull ℝ (p : Set (E d)) := by
    let q := t.val ∪ (A \ t.val).image (fun f => -f)
    have hC : C t.val = {x | ∀ f ∈ q, 0 ≤ f x} := by
      ext x
      constructor
      · intro hx f hf
        rcases Finset.mem_union.mp hf with hf | hf
        · have hfA := Finset.mem_powerset.mp (Finset.mem_filter.mp t.property).1 hf
          simpa only [if_pos hf] using hx f hfA
        · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
          obtain ⟨hgA, hgt⟩ := Finset.mem_sdiff.mp hg
          have hgx := hx g hgA
          simpa only [if_neg hgt, AffineMap.coe_neg, Pi.neg_apply, neg_nonneg] using hgx
      · intro hx f hfA
        by_cases hft : f ∈ t.val
        · simpa only [if_pos hft] using hx f (Finset.mem_union_left _ hft)
        · have hneg := hx (-f) (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨f, Finset.mem_sdiff.mpr ⟨hfA, hft⟩, rfl⟩))
          simpa only [if_neg hft, AffineMap.coe_neg, Pi.neg_apply, neg_nonneg] using hneg
    rw [hC]
    apply principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral_step4_bounded_halfspaces
    rw [← hC]
    exact hcompact.isBounded.subset (hsub t)
  choose p hp using hrep
  refine ⟨Finset.univ.image p, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      let t := A.filter fun f => 0 ≤ f x
      have ht : t ∈ T := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
        rw [hS] at hx
        obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
        refine ⟨q, hq, fun f hf => ?_⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨q, hq, hf⟩, hxq f hf⟩
      let u : T := ⟨t, ht⟩
      refine Set.mem_iUnion₂.mpr ⟨p u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩, ?_⟩
      rw [← hp u]
      intro f hfA
      by_cases hfx : 0 ≤ f x
      · simp only [u, t, Finset.mem_filter, hfA, hfx, and_self, if_true]
      · simp only [u, t, Finset.mem_filter, hfA, hfx, and_false, if_false]
        exact (lt_of_not_ge hfx).le
    · intro x hx
      obtain ⟨r, hr, hxr⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
      exact hsub t (by rwa [hp t])
  · intro r hr s hs
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hs
    rw [← hp t, ← hp u]
    refine ⟨Set.inter_subset_left, ?_⟩
    intro x hx y hy z hz hseg
    refine ⟨hx, ?_⟩
    rw [openSegment_eq_image_lineMap] at hseg
    obtain ⟨a, ha, rfl⟩ := hseg
    intro f hfA
    have hxf := hx f hfA
    have hyf := hy f hfA
    have hzf := hz.2 f hfA
    rw [f.apply_lineMap, AffineMap.lineMap_apply_ring] at hzf
    by_cases hfu : f ∈ u.val
    · simp only [if_pos hfu] at hzf ⊢
      by_cases hft : f ∈ t.val
      · simpa only [if_pos hft] using hxf
      · simp only [if_neg hft] at hxf hyf
        have hmul : 0 ≤ (1 - a) * f x := by
          nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.1.le hyf]
        exact (mul_nonneg_iff_of_pos_left (sub_pos.mpr ha.2)).mp hmul
    · simp only [if_neg hfu] at hzf ⊢
      by_cases hft : f ∈ t.val
      · simp only [if_pos hft] at hxf hyf
        have hmul : (1 - a) * f x ≤ 0 := by
          nlinarith [mul_nonneg ha.1.le hyf]
        exact nonpos_of_mul_nonpos_right hmul (sub_pos.mpr ha.2)
      · simpa only [if_neg hft] using hxf

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "taking barycentres of their nonempty
faces". The cells of the subdivision: the nonempty convex extreme subsets (faces) of the
given convex polytopes. This definition contains no proof. -/
private def principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces (T : Finset (Finset (E d))) : Set (Set (E d)) :=
  {F | ∃ p ∈ T, IsExtreme ℝ (convexHull ℝ (p : Set (E d))) F ∧ Convex ℝ F ∧ F.Nonempty}

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "convex polytopes". A convex face of
`conv p` is the hull of the points of `p` it contains: every point of `p` carrying
positive weight in a convex combination lies on an open segment through the point. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step1_face_eq_hull {p : Finset (E d)} {F : Set (E d)}
    (hext : IsExtreme ℝ (convexHull ℝ (p : Set (E d))) F) (hconv : Convex ℝ F) :
    F = convexHull ℝ (F ∩ (p : Set (E d))) := by
  classical
  apply Set.Subset.antisymm
  · intro x hxF
    obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp (hext.1 hxF)
    have hv : ∀ v ∈ p, 0 < w v → v ∈ F := by
      intro v hv hwv
      have hsplit := Finset.add_sum_erase p w hv
      have hsplitx := Finset.add_sum_erase p (fun u => w u • u) hv
      have hrest0 : ∀ u ∈ p.erase v, 0 ≤ w u := fun u hu => hw0 u (Finset.mem_of_mem_erase hu)
      have hle : w v ≤ 1 := by
        rw [← hw1, ← hsplit]
        linarith [Finset.sum_nonneg hrest0]
      rcases hle.lt_or_eq with hlt | heq
      · set r : ℝ := 1 - w v with hr
        have hrpos : 0 < r := by rw [hr]; linarith
        have hsumr : ∑ u ∈ p.erase v, w u = r := by rw [hr, ← hw1, ← hsplit]; ring
        let x' : E d := ∑ u ∈ p.erase v, (r⁻¹ * w u) • u
        have hx' : x' ∈ convexHull ℝ (p : Set (E d)) := by
          apply (convex_convexHull ℝ (p : Set (E d))).sum_mem
          · intro u hu
            exact mul_nonneg (inv_nonneg.mpr hrpos.le) (hrest0 u hu)
          · rw [← Finset.mul_sum, hsumr, inv_mul_cancel₀ hrpos.ne']
          · intro u hu
            exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hu))
        have hrx' : r • x' = ∑ u ∈ p.erase v, w u • u := by
          simp only [x', Finset.smul_sum, smul_smul, ← mul_assoc, mul_inv_cancel₀ hrpos.ne',
            one_mul]
        have hseg : x ∈ openSegment ℝ v x' := by
          refine ⟨w v, r, hwv, hrpos, by rw [hr]; ring, ?_⟩
          rw [hrx', hsplitx]
          exact hwx
        exact hext.2 (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)) hx' hxF hseg
      · have hrest : ∑ u ∈ p.erase v, w u = 0 := by
          have := hsplit
          rw [hw1, heq] at this
          linarith
        have hzero := (Finset.sum_eq_zero_iff_of_nonneg hrest0).mp hrest
        have hz : ∑ u ∈ p.erase v, w u • u = 0 :=
          Finset.sum_eq_zero (fun u hu => by rw [hzero u hu, zero_smul])
        have hxv : x = v := by
          rw [← hwx, ← hsplitx]
          beta_reduce
          rw [heq, one_smul, hz, add_zero]
        exact hxv ▸ hxF
    let q := p.filter (fun u => 0 < w u)
    have hq : (q : Set (E d)) ⊆ F ∩ (p : Set (E d)) := by
      intro u hu
      obtain ⟨hup, hwu⟩ := Finset.mem_filter.mp hu
      exact ⟨hv u hup hwu, hup⟩
    refine convexHull_mono hq (Finset.mem_convexHull'.mpr ⟨w, ?_, ?_, ?_⟩)
    · intro u hu
      exact hw0 u (Finset.mem_filter.mp hu).1
    · rw [Finset.sum_filter_of_ne]
      · exact hw1
      · intro u hu hne
        exact lt_of_le_of_ne (hw0 u hu) (Ne.symm hne)
    · rw [Finset.sum_filter_of_ne]
      · exact hwx
      · intro u hu hne
        refine lt_of_le_of_ne (hw0 u hu) (Ne.symm ?_)
        intro h0
        exact hne (by rw [h0, zero_smul])
  · exact convexHull_min Set.inter_subset_left hconv

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "a finite family of convex polytopes".
Each face is the hull of a subset of a polytope's vertex set (previous step), hence
there are finitely many faces. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step1_faces_finite (T : Finset (Finset (E d))) :
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T).Finite := by
  classical
  apply Set.Finite.subset (((T.biUnion fun p => p.powerset) : Set (Finset (E d))).toFinite.image
    (fun q : Finset (E d) => convexHull ℝ (q : Set (E d))))
  rintro F ⟨p, hp, hext, hconv, -⟩
  refine ⟨p.filter (· ∈ F), ?_, ?_⟩
  · exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨p, hp,
      Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩)
  · change convexHull ℝ ((p.filter (· ∈ F) : Finset (E d)) : Set (E d)) = F
    conv_rhs => rw [principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step1_face_eq_hull hext hconv]
    congr 1
    ext u
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_coe]
    exact and_comm

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "convex polytopes meeting in common
faces". If a face of one polytope lies in a face of another, it is a face of the
latter: it is extreme in the common face `conv p ∩ conv q`, which is extreme in `conv q`. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step2_face_extreme (T : Finset (Finset (E d)))
    (hface : ∀ p ∈ T, ∀ q ∈ T,
      IsExtreme ℝ (convexHull ℝ (p : Set (E d)))
        (convexHull ℝ (p : Set (E d)) ∩ convexHull ℝ (q : Set (E d))))
    {F G : Set (E d)} (hF : F ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T) (hG : G ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T) (hFG : F ⊆ G) :
    IsExtreme ℝ G F := by
  obtain ⟨p, hp, hpF, -, -⟩ := hF
  obtain ⟨q, hq, hqG, -, -⟩ := hG
  have hFq : F ⊆ convexHull ℝ (q : Set (E d)) := hFG.trans hqG.1
  have h1 : IsExtreme ℝ (convexHull ℝ (p : Set (E d)) ∩ convexHull ℝ (q : Set (E d))) F :=
    hpF.mono Set.inter_subset_left (Set.subset_inter hpF.1 hFq)
  have h2 := hface q hq p hp
  rw [Set.inter_comm] at h2
  exact (h2.trans h1).mono hqG.1 hFG

open scoped Topology in
/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "taking barycentres of their nonempty
faces". From a relative-interior point `u` of a set, the line towards any point `v` of
its affine span can be continued a little beyond `u` inside the set. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step3_extend_past {S : Set (E d)} {u v : E d}
    (hu : u ∈ intrinsicInterior ℝ S) (hv : v ∈ affineSpan ℝ S) :
    ∃ t : ℝ, 1 < t ∧ AffineMap.lineMap v u t ∈ S ∧
      u ∈ openSegment ℝ v (AffineMap.lineMap v u t) := by
  obtain ⟨y, hy, hyu⟩ := mem_intrinsicInterior.mp hu
  have huA : u ∈ affineSpan ℝ S := subset_affineSpan ℝ S (intrinsicInterior_subset hu)
  let γ : ℝ → affineSpan ℝ S := fun t =>
    ⟨AffineMap.lineMap v u t, AffineMap.lineMap_mem t hv huA⟩
  have hγ : Continuous γ :=
    ((AffineMap.lineMap v u : ℝ →ᵃ[ℝ] E d).continuous_of_finiteDimensional).subtype_mk _
  have hγ1 : γ 1 = y := Subtype.ext (by simp [γ, hyu])
  have hnhds : interior ((↑) ⁻¹' S : Set (affineSpan ℝ S)) ∈ 𝓝 (γ 1) := by
    rw [hγ1]
    exact isOpen_interior.mem_nhds hy
  have hnear : γ ⁻¹' interior ((↑) ⁻¹' S : Set (affineSpan ℝ S)) ∈ 𝓝 (1 : ℝ) :=
    hγ.continuousAt.preimage_mem_nhds hnhds
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let t : ℝ := 1 + ε / 2
  have ht : 1 < t := by dsimp [t]; linarith
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hin := hball (show t ∈ Metric.ball (1 : ℝ) ε by
    change dist t 1 < ε
    rw [Real.dist_eq, abs_of_pos (by dsimp [t]; linarith)]
    dsimp [t]
    linarith)
  have hin' : γ t ∈ interior ((↑) ⁻¹' S : Set (affineSpan ℝ S)) := hin
  refine ⟨t, ht, (interior_subset hin' : γ t ∈ ((↑) ⁻¹' S : Set (affineSpan ℝ S))), ?_⟩
  have hmem := lineMap_mem_openSegment ℝ v (AffineMap.lineMap v u t)
    (show t⁻¹ ∈ Ioo (0 : ℝ) 1 from ⟨inv_pos.mpr ht0, inv_lt_one_of_one_lt₀ ht⟩)
  simpa [AffineMap.lineMap_lineMap_right, ne_of_gt ht0] using hmem

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "taking barycentres of their nonempty
faces". A relative-interior point of a convex set is not in the affine span of a
proper convex face: such a span meets the set only in the face, and a relative-interior
point lying in a face forces the face to be everything. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step3_relint_not_mem_affineSpan {F G : Set (E d)} (hF : Convex ℝ F)
    (hG : Convex ℝ G) (hFG : IsExtreme ℝ G F) (hne : F ≠ G) {x : E d}
    (hx : x ∈ intrinsicInterior ℝ G) : x ∉ affineSpan ℝ F := by
  intro hxF
  have hxG : x ∈ G := intrinsicInterior_subset hx
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · rw [AffineSubspace.span_empty] at hxF
    exact Set.notMem_empty _ hxF
  obtain ⟨u, hu⟩ := hFne.intrinsicInterior hF
  have hxF' : x ∈ F := by
    obtain ⟨t, -, hwF, hseg⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step3_extend_past hu hxF
    exact hFG.2 hxG (hFG.1 hwF) (intrinsicInterior_subset hu) hseg
  obtain ⟨y, hyG, hyF⟩ : ∃ y ∈ G, y ∉ F := by
    by_contra h
    push_neg at h
    exact hne (Set.Subset.antisymm hFG.1 h)
  obtain ⟨t, -, hwG, hseg⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step3_extend_past hx (subset_affineSpan ℝ G hyG)
  exact hyF (hFG.2 hyG hwG hxF' hseg)

/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "simplices indexed by chains of faces".
A nonempty finite chain of sets has a largest member. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step4_chain_top {c : Finset (Set (E d))} (hne : c.Nonempty)
    (hch : IsChain (· ⊆ ·) (c : Set (Set (E d)))) : ∃ G ∈ c, ∀ F ∈ c, F ⊆ G := by
  obtain ⟨G, hG⟩ := c.exists_maximal hne
  refine ⟨G, hG.1, fun F hF => ?_⟩
  by_cases h : F = G
  · exact h ▸ subset_rfl
  · rcases hch (Finset.mem_coe.mpr hF) (Finset.mem_coe.mpr hG.1) h with h' | h'
    · exact h'
    · exact hG.2 hF h'

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "simplices indexed by chains of faces".
The barycentres of a chain of faces are affinely independent: the barycentre of the
top face is outside the affine span of the next face, which contains all the others. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step5_chain_indep (T : Finset (Finset (E d)))
    (hface : ∀ p ∈ T, ∀ q ∈ T,
      IsExtreme ℝ (convexHull ℝ (p : Set (E d)))
        (convexHull ℝ (p : Set (E d)) ∩ convexHull ℝ (q : Set (E d))))
    (b : Set (E d) → E d) (hb : ∀ F ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T, b F ∈ intrinsicInterior ℝ F)
    (c : Finset (Set (E d))) (hc : (c : Set (Set (E d))) ⊆ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T)
    (hch : IsChain (· ⊆ ·) (c : Set (Set (E d)))) :
    AffineIndependent ℝ ((↑) : (b '' (c : Set (Set (E d)))) → E d) := by
  classical
  induction c using Finset.strongInduction with
  | H c ih =>
  rcases c.eq_empty_or_nonempty with rfl | hne
  · haveI : Subsingleton (b '' ((∅ : Finset (Set (E d))) : Set (Set (E d)))) :=
      ⟨fun ⟨_, F, hF, _⟩ => (Finset.notMem_empty F hF).elim⟩
    exact affineIndependent_of_subsingleton ℝ _
  obtain ⟨G, hGc, hsubG⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step4_chain_top hne hch
  have hG : G ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T := hc hGc
  have hGconv : Convex ℝ G := by obtain ⟨_, _, _, h, _⟩ := hG; exact h
  have hout : ∀ F ∈ c, F ≠ G → b G ∉ affineSpan ℝ F := by
    intro F hF hFG
    have hFf : F ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T := hc hF
    have hFconv : Convex ℝ F := by obtain ⟨_, _, _, h, _⟩ := hFf; exact h
    exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step3_relint_not_mem_affineSpan hFconv hGconv
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step2_face_extreme T hface hFf hG (hsubG F hF)) hFG (hb G hG)
  have hinj : ∀ F ∈ c, F ≠ G → b F ≠ b G := by
    intro F hF hFG h
    apply hout F hF hFG
    rw [← h]
    exact subset_affineSpan ℝ F (intrinsicInterior_subset (hb F (hc hF)))
  let c' := c.erase G
  have hc'c : (c' : Set (Set (E d))) ⊆ c := Finset.coe_subset.mpr (c.erase_subset G)
  have ih' := ih c' (Finset.erase_ssubset hGc) (hc'c.trans hc) (hch.mono hc'c)
  let i : (b '' (c : Set (Set (E d)))) := ⟨b G, Set.mem_image_of_mem b hGc⟩
  apply AffineIndependent.affineIndependent_of_notMem_span (i := i)
  · apply AffineIndependent.of_set_of_injective
    · have hrange : Set.range (fun x : {y : (b '' (c : Set (Set (E d)))) // y ≠ i} =>
          ((x : (b '' (c : Set (Set (E d))))) : E d)) = b '' (c' : Set (Set (E d))) := by
        ext z
        constructor
        · rintro ⟨⟨⟨z, hz⟩, hzi⟩, rfl⟩
          obtain ⟨F, hF, rfl⟩ := hz
          have hFG : F ≠ G := by
            rintro rfl
            exact hzi rfl
          exact ⟨F, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hFG, hF⟩), rfl⟩
        · rintro ⟨F, hF, rfl⟩
          obtain ⟨hFG, hF⟩ := Finset.mem_erase.mp hF
          refine ⟨⟨⟨b F, Set.mem_image_of_mem b hF⟩, ?_⟩, rfl⟩
          intro h
          exact hinj F hF hFG (congrArg Subtype.val h)
      rw [hrange]
      exact ih'
    · intro u v huv
      exact Subtype.ext (Subtype.ext huv)
  · intro hmem
    have himg : ∀ z ∈ ((↑) : (b '' (c : Set (Set (E d)))) → E d) '' {x | x ≠ i},
        ∃ F ∈ c', z = b F := by
      rintro z ⟨⟨z, hz⟩, hzi, rfl⟩
      obtain ⟨F, hF, rfl⟩ := hz
      have hFG : F ≠ G := by
        rintro rfl
        exact hzi rfl
      exact ⟨F, Finset.mem_erase.mpr ⟨hFG, hF⟩, rfl⟩
    rcases c'.eq_empty_or_nonempty with hempty | hne'
    · have hset : ((↑) : (b '' (c : Set (Set (E d)))) → E d) '' {x | x ≠ i} = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro z hz
        obtain ⟨F, hF, -⟩ := himg z hz
        rw [hempty] at hF
        exact Finset.notMem_empty F hF
      rw [hset, AffineSubspace.span_empty] at hmem
      exact Set.notMem_empty _ hmem
    · obtain ⟨M, hMc', hsubM⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step4_chain_top hne' (hch.mono hc'c)
      obtain ⟨hMG, hMc⟩ := Finset.mem_erase.mp hMc'
      apply hout M hMc hMG
      refine affineSpan_mono ℝ ?_ hmem
      intro z hz
      obtain ⟨F, hF, rfl⟩ := himg z hz
      exact hsubM F hF (intrinsicInterior_subset (hb F (hc (hc'c hF))))

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "taking barycentres of their nonempty
faces". Coning from a relative-interior point: every other point of a face lies on a
segment from that point to a point of a proper face (the ray leaves the compact face
through its relative boundary, which is covered by proper faces). -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step6_cone (T : Finset (Finset (E d))) {G : Set (E d)}
    (hG : G ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T) {z : E d} (hz : z ∈ intrinsicInterior ℝ G) {x : E d}
    (hx : x ∈ G) :
    x = z ∨ ∃ F ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T, F ⊆ G ∧ F ≠ G ∧ ∃ y ∈ F, x ∈ segment ℝ z y := by
  classical
  by_cases hxz : x = z
  · exact Or.inl hxz
  right
  have hGmem := hG
  obtain ⟨p, hp, hpG, hGconv, -⟩ := hG
  have hzG : z ∈ G := intrinsicInterior_subset hz
  have hGclosed : IsClosed G := by
    rw [principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step1_face_eq_hull hpG hGconv]
    exact (p.finite_toSet.subset Set.inter_subset_right).isClosed_convexHull
  have hGbdd : Bornology.IsBounded G :=
    (p.finite_toSet.isCompact_convexHull).isBounded.subset hpG.1
  let L : ℝ → E d := fun t => t • (x - z) + z
  have hLc : Continuous L := (continuous_id.smul continuous_const).add continuous_const
  let Λ : Set ℝ := {t | 1 ≤ t ∧ L t ∈ G}
  have hΛclosed : IsClosed Λ := isClosed_Ici.inter (hGclosed.preimage hLc)
  have hΛne : Λ.Nonempty := ⟨1, le_rfl, by simpa [L] using hx⟩
  have hΛbdd : BddAbove Λ := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hGbdd
    have hxz' : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
    refine ⟨(C + ‖z‖) / ‖x - z‖, fun t ht => ?_⟩
    have h1 := hC _ ht.2
    have h2 : ‖t • (x - z)‖ ≤ ‖L t‖ + ‖z‖ := by
      have : t • (x - z) = L t - z := by simp [L]
      rw [this]
      exact norm_sub_le _ _
    rw [norm_smul, Real.norm_of_nonneg (by linarith [ht.1])] at h2
    rw [le_div_iff₀ hxz']
    linarith
  obtain ⟨t₀, ht₀def⟩ : ∃ t₀, t₀ = sSup Λ := ⟨_, rfl⟩
  have ht₀Λ : t₀ ∈ Λ := ht₀def ▸ hΛclosed.csSup_mem hΛne hΛbdd
  have hmax : ∀ t ∈ Λ, t ≤ t₀ := fun t ht => ht₀def ▸ le_csSup hΛbdd ht
  have ht₀1 : 1 ≤ t₀ := ht₀Λ.1
  obtain ⟨y, hydef⟩ : ∃ y, y = t₀ • (x - z) + z := ⟨_, rfl⟩
  have hyG : y ∈ G := hydef ▸ ht₀Λ.2
  let F : Set (E d) := {w | w ∈ G ∧ ∃ ε : ℝ, 0 < ε ∧ y + ε • (y - w) ∈ G}
  have hshrink : ∀ {v : E d} {ε ε' : ℝ}, 0 < ε' → ε' ≤ ε → y + ε • v ∈ G →
      y + ε' • v ∈ G := by
    intro v ε ε' hε' hle hv
    have hε : 0 < ε := lt_of_lt_of_le hε' hle
    have hcomb := hGconv hyG hv
      (show 0 ≤ 1 - ε' / ε by rw [sub_nonneg, div_le_one hε]; exact hle)
      (show 0 ≤ ε' / ε by positivity) (by ring)
    have heq : y + ε' • v = (1 - ε' / ε) • y + (ε' / ε) • (y + ε • v) := by
      rw [smul_add, smul_smul, div_mul_cancel₀ _ hε.ne']
      module
    rw [heq]
    exact hcomb
  have hyF : y ∈ F := ⟨hyG, 1, one_pos, by simpa using hyG⟩
  have hzF : z ∉ F := by
    rintro ⟨-, ε, hε, hzε⟩
    have hL : y + ε • (y - z) = (t₀ * (1 + ε)) • (x - z) + z := by
      rw [hydef]
      module
    have hmem : t₀ * (1 + ε) ∈ Λ := ⟨by nlinarith, by
      change (t₀ * (1 + ε)) • (x - z) + z ∈ G
      rw [← hL]
      exact hzε⟩
    have := hmax _ hmem
    nlinarith
  have hFconv : Convex ℝ F := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    obtain ⟨hw₁G, ε₁, hε₁, h₁⟩ := hw₁
    obtain ⟨hw₂G, ε₂, hε₂, h₂⟩ := hw₂
    refine ⟨hGconv hw₁G hw₂G ha hb hab, min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
    have h₁' := hshrink (lt_min hε₁ hε₂) (min_le_left _ _) h₁
    have h₂' := hshrink (lt_min hε₁ hε₂) (min_le_right _ _) h₂
    have hc := hGconv h₁' h₂' ha hb hab
    have heq : y + min ε₁ ε₂ • (y - (a • w₁ + b • w₂)) =
        a • (y + min ε₁ ε₂ • (y - w₁)) + b • (y + min ε₁ ε₂ • (y - w₂)) := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      module
    rw [heq]
    exact hc
  have hFext : IsExtreme ℝ G F := by
    refine ⟨fun w hw => hw.1, ?_⟩
    intro a ha b hb w hwF hseg
    obtain ⟨hwG, ε, hε, hu⟩ := hwF
    obtain ⟨l₁, l₂, hl₁, hl₂, hl, hw⟩ := hseg
    refine ⟨ha, ε * l₁ / (1 + ε * l₂), by positivity, ?_⟩
    obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 1 + ε * l₂ := ⟨_, rfl⟩
    rw [← hDdef]
    have hD : 0 < D := by rw [hDdef]; positivity
    have hc := hGconv hu hb (show 0 ≤ 1 / D by positivity)
      (show 0 ≤ ε * l₂ / D by positivity)
      (by rw [div_add_div_same, div_eq_one_iff_eq hD.ne', hDdef])
    have e1 : 1 / D * D = 1 := one_div_mul_cancel hD.ne'
    have e2 : 1 / D * (ε * l₁) = ε * l₁ / D := by rw [div_mul_eq_mul_div, one_mul]
    have e3 : 1 / D * (ε * l₂) = ε * l₂ / D := by rw [div_mul_eq_mul_div, one_mul]
    have heq : y + (ε * l₁ / D) • (y - a) =
        (1 / D) • (y + ε • (y - w)) + (ε * l₂ / D) • b := by
      calc y + (ε * l₁ / D) • (y - a) = (1 / D) • (D • y + (ε * l₁) • (y - a)) := by
            rw [smul_add, smul_smul, smul_smul, e1, e2, one_smul]
        _ = (1 / D) • (y + ε • (y - w) + (ε * l₂) • b) := by
            congr 1
            rw [← hw, hDdef]
            have hl₁' : l₁ = 1 - l₂ := by linarith
            subst hl₁'
            module
        _ = (1 / D) • (y + ε • (y - w)) + (ε * l₂ / D) • b := by
            rw [smul_add, smul_smul, e3]
    rw [heq]
    exact hc
  refine ⟨F, ⟨p, hp, hpG.trans hFext, hFconv, ⟨y, hyF⟩⟩, fun w hw => hw.1,
    fun h => hzF (by rw [h]; exact hzG), y, hyF, ?_⟩
  have ht₀ne : t₀ ≠ 0 := by positivity
  refine ⟨1 - t₀⁻¹, t₀⁻¹, by
    rw [sub_nonneg]; exact inv_le_one_of_one_le₀ ht₀1, by positivity, by ring, ?_⟩
  rw [hydef, smul_add, smul_smul, inv_mul_cancel₀ ht₀ne, one_smul]
  module

/-- Step 7 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "simplices indexed by chains of faces".
The chain simplices cover every polytope: by induction on the number of subfaces,
cone the subdivision of the proper faces from the barycentre (Step 6). -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step7_cover (T : Finset (Finset (E d)))
    (b : Set (E d) → E d) (hb : ∀ F ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T, b F ∈ intrinsicInterior ℝ F)
    {p : Finset (E d)} (hp : p ∈ T) {x : E d} (hx : x ∈ convexHull ℝ (p : Set (E d))) :
    ∃ c : Finset (Set (E d)), (c : Set (Set (E d))) ⊆ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T ∧
      IsChain (· ⊆ ·) (c : Set (Set (E d))) ∧
      x ∈ convexHull ℝ (b '' (c : Set (Set (E d)))) := by
  classical
  have hfin := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step1_faces_finite T
  have key : ∀ n : ℕ, ∀ G ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T, {F | F ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T ∧ F ⊆ G}.ncard = n →
      ∀ x ∈ G, ∃ c : Finset (Set (E d)), (c : Set (Set (E d))) ⊆ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T ∧
        IsChain (· ⊆ ·) (c : Set (Set (E d))) ∧ (∀ F ∈ c, F ⊆ G) ∧
        x ∈ convexHull ℝ (b '' (c : Set (Set (E d)))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro G hG hn x hx
    rcases principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step6_cone T hG (hb G hG) hx with rfl | ⟨F, hF, hFG, hne, y, hy, hxy⟩
    · refine ⟨{G}, by simpa using hG, ?_, by simp, ?_⟩
      · rw [Finset.coe_singleton]
        exact Set.subsingleton_singleton.isChain
      · rw [Finset.coe_singleton, Set.image_singleton]
        exact subset_convexHull ℝ _ (Set.mem_singleton _)
    · have hlt : {F' | F' ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T ∧ F' ⊆ F}.ncard < n := by
        rw [← hn]
        apply Set.ncard_lt_ncard _ (hfin.subset (fun _ h => h.1))
        refine ssubset_of_subset_not_subset (fun F' h => ⟨h.1, h.2.trans hFG⟩) ?_
        intro hsub
        exact hne (Set.Subset.antisymm hFG (hsub ⟨hG, subset_rfl⟩).2)
      obtain ⟨c, hc, hch, hcF, hyc⟩ := ih _ hlt F hF rfl y hy
      refine ⟨insert G c, ?_, ?_, ?_, ?_⟩
      · rw [Finset.coe_insert]
        exact Set.insert_subset hG hc
      · rw [Finset.coe_insert]
        exact hch.insert fun F' hF' _ => Or.inr ((hcF F' (Finset.mem_coe.mp hF')).trans hFG)
      · intro F' hF'
        rcases Finset.mem_insert.mp hF' with rfl | hF'
        · exact subset_rfl
        · exact (hcF F' hF').trans hFG
      · apply (convex_convexHull ℝ _).segment_subset _ _ hxy
        · exact subset_convexHull ℝ _ (Set.mem_image_of_mem b (by simp))
        · refine convexHull_mono (Set.image_mono ?_) hyc
          rw [Finset.coe_insert]
          exact Set.subset_insert _ _
  have hpF : convexHull ℝ (p : Set (E d)) ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T :=
    ⟨p, hp, IsExtreme.rfl, convex_convexHull ℝ _, ⟨x, hx⟩⟩
  obtain ⟨c, hc, hch, -, hxc⟩ := key _ _ hpF rfl x hx
  exact ⟨c, hc, hch, hxc⟩

/-- Step 8 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "convex polytopes meeting in common
faces". Two faces of the family meet in a face of each: inside the common face
`conv p ∩ conv q`, the two intersections are faces, hence so is their intersection. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step8_inter_extreme (T : Finset (Finset (E d)))
    (hface : ∀ p ∈ T, ∀ q ∈ T,
      IsExtreme ℝ (convexHull ℝ (p : Set (E d)))
        (convexHull ℝ (p : Set (E d)) ∩ convexHull ℝ (q : Set (E d))))
    {F G : Set (E d)} (hF : F ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T) (hG : G ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T) :
    IsExtreme ℝ F (F ∩ G) := by
  obtain ⟨p, hp, hpF, -, -⟩ := hF
  obtain ⟨q, hq, hqG, -, -⟩ := hG
  have hCp := hface p hp q hq
  have hCq := hface q hq p hp
  rw [Set.inter_comm] at hCq
  have h1 : IsExtreme ℝ (convexHull ℝ (p : Set (E d)) ∩ convexHull ℝ (q : Set (E d)))
      (G ∩ (convexHull ℝ (p : Set (E d)) ∩ convexHull ℝ (q : Set (E d)))) :=
    (hqG.inter hCq).mono Set.inter_subset_right Set.inter_subset_right
  have h3 := hpF.inter (hCp.trans h1)
  have heq : F ∩ (G ∩ (convexHull ℝ (p : Set (E d)) ∩ convexHull ℝ (q : Set (E d)))) =
      F ∩ G := by
    ext z
    constructor
    · rintro ⟨hzF, hzG, -⟩
      exact ⟨hzF, hzG⟩
    · rintro ⟨hzF, hzG⟩
      exact ⟨hzF, hzG, hpF.1 hzF, hqG.1 hzG⟩
  rw [heq] at h3
  exact h3.mono hpF.1 Set.inter_subset_left

/-- Step 8 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "taking barycentres of their nonempty
faces". A face of the family containing a relative-interior point of another face
contains that whole face (Step 3 applied to the common face). -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step8_relint_subset (T : Finset (Finset (E d)))
    (hface : ∀ p ∈ T, ∀ q ∈ T,
      IsExtreme ℝ (convexHull ℝ (p : Set (E d)))
        (convexHull ℝ (p : Set (E d)) ∩ convexHull ℝ (q : Set (E d))))
    {F G : Set (E d)} (hF : F ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T) (hG : G ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T) {z : E d}
    (hz : z ∈ intrinsicInterior ℝ F) (hzG : z ∈ G) : F ⊆ G := by
  have hFconv : Convex ℝ F := by obtain ⟨_, _, _, h, _⟩ := hF; exact h
  have hGconv : Convex ℝ G := by obtain ⟨_, _, _, h, _⟩ := hG; exact h
  by_contra hsub
  have hne : F ∩ G ≠ F := fun h => hsub (by rw [← h]; exact Set.inter_subset_right)
  exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step3_relint_not_mem_affineSpan (hFconv.inter hGconv) hFconv
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step8_inter_extreme T hface hF hG) hne hz
    (subset_affineSpan ℝ _ ⟨intrinsicInterior_subset hz, hzG⟩)

open Classical in
/-- Step 8 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "simplices indexed by chains of faces".
A point of a chain simplex is the top barycentre, a point of the simplex of the
shorter chain, or lies strictly between the top barycentre and such a point. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step8_chain_split {b : Set (E d) → E d} {c : Finset (Set (E d))}
    {G : Set (E d)} (hGc : G ∈ c) {x : E d}
    (hx : x ∈ convexHull ℝ (b '' (c : Set (Set (E d))))) :
    x = b G ∨ ∃ y ∈ convexHull ℝ (b '' ((c.erase G : Finset (Set (E d))) : Set (Set (E d)))),
      x = y ∨ x ∈ openSegment ℝ (b G) y := by
  classical
  have himg : b '' (c : Set (Set (E d))) =
      insert (b G) (b '' ((c.erase G : Finset (Set (E d))) : Set (Set (E d)))) := by
    rw [Finset.coe_erase, ← Set.image_insert_eq, Set.insert_diff_singleton,
      Set.insert_eq_of_mem (Finset.mem_coe.mpr hGc)]
  rw [himg] at hx
  rcases (b '' ((c.erase G : Finset (Set (E d))) : Set (Set (E d)))).eq_empty_or_nonempty
    with he | hne
  · left
    rw [he] at hx
    simpa using hx
  · rw [convexHull_insert hne, mem_convexJoin] at hx
    obtain ⟨a, ha, y, hy, hxy⟩ := hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [← insert_endpoints_openSegment] at hxy
    rcases Set.mem_insert_iff.mp hxy with h | h
    · exact Or.inl h
    rcases Set.mem_insert_iff.mp h with h | h
    · exact Or.inr ⟨y, hy, Or.inl h⟩
    · exact Or.inr ⟨y, hy, Or.inr h⟩

/-- Step 8 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "simplices indexed by chains of faces".
The ray from the barycentre through a point leaves the face only once: two points of
proper faces beyond the same point on that ray coincide, since a nearer one would lie
strictly between the barycentre and the farther one. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step8_ray_unique {G H₁ H₂ : Set (E d)} (h₁ : IsExtreme ℝ G H₁)
    (h₂ : IsExtreme ℝ G H₂) {z x y₁ y₂ : E d} (hz : z ∈ G) (hz₁ : z ∉ H₁) (hz₂ : z ∉ H₂)
    (hy₁ : y₁ ∈ H₁) (hy₂ : y₂ ∈ H₂)
    (hx₁ : x ∈ openSegment ℝ z y₁) (hx₂ : x ∈ openSegment ℝ z y₂) : y₁ = y₂ := by
  have hray : ∀ {y : E d}, x ∈ openSegment ℝ z y → ∃ r : ℝ, 0 ≤ r ∧ y = r • (x -ᵥ z) +ᵥ z := by
    intro y hy
    rw [openSegment_eq_image_lineMap] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    refine ⟨t⁻¹, (inv_pos.mpr ht.1).le, ?_⟩
    rw [AffineMap.lineMap_apply]
    simp [smul_smul, inv_mul_cancel₀ ht.1.ne']
  have key : ∀ {H H' : Set (E d)} {a a' : E d}, IsExtreme ℝ G H → z ∉ H → a ∈ H →
      a' ∈ H' → H' ⊆ G → Wbtw ℝ z a a' → a = a' := by
    intro H H' a a' hH hzH ha ha' hH' hw
    by_contra hne
    have hseg' : a ∈ segment ℝ z a' := mem_segment_iff_wbtw.mpr hw
    rw [← insert_endpoints_openSegment] at hseg'
    rcases Set.mem_insert_iff.mp hseg' with h | h
    · exact hzH (h ▸ ha)
    rcases Set.mem_insert_iff.mp h with h | h
    · exact hne h
    exact hzH (hH.left_mem_of_mem_openSegment hz (hH' ha') ha h)
  obtain ⟨r₁, hr₁, hy₁e⟩ := hray hx₁
  obtain ⟨r₂, hr₂, hy₂e⟩ := hray hx₂
  rcases wbtw_or_wbtw_smul_vadd_of_nonneg z (x -ᵥ z) hr₁ hr₂ with hw | hw
  · rw [← hy₁e, ← hy₂e] at hw
    exact key h₁ hz₁ hy₁ hy₂ h₂.1 hw
  · rw [← hy₁e, ← hy₂e] at hw
    exact (key h₂ hz₂ hy₂ hy₁ h₁.1 hw).symm

/-- Step 8 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells` (V4 1.24): "simplices indexed by chains of faces".
Two chain simplices meet in the simplex of the common subchain: by induction on the
chain lengths, a common point either lies in a shorter chain simplex, or both top faces
coincide (they contain each other's barycentres) and the ray from the common top
barycentre reduces to a common point of the shorter chains. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step8_chain_inter (T : Finset (Finset (E d)))
    (hface : ∀ p ∈ T, ∀ q ∈ T,
      IsExtreme ℝ (convexHull ℝ (p : Set (E d)))
        (convexHull ℝ (p : Set (E d)) ∩ convexHull ℝ (q : Set (E d))))
    (b : Set (E d) → E d) (hb : ∀ F ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T, b F ∈ intrinsicInterior ℝ F)
    (c₁ c₂ : Finset (Set (E d))) (hc₁ : (c₁ : Set (Set (E d))) ⊆ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T)
    (hc₂ : (c₂ : Set (Set (E d))) ⊆ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T)
    (hch₁ : IsChain (· ⊆ ·) (c₁ : Set (Set (E d))))
    (hch₂ : IsChain (· ⊆ ·) (c₂ : Set (Set (E d)))) :
    convexHull ℝ (b '' (c₁ : Set (Set (E d)))) ∩ convexHull ℝ (b '' (c₂ : Set (Set (E d)))) ⊆
      convexHull ℝ (b '' ((c₁ : Set (Set (E d))) ∩ c₂)) := by
  classical
  have hconvF : ∀ {F : Set (E d)}, F ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T → Convex ℝ F := by
    rintro F ⟨_, _, _, h, _⟩
    exact h
  have hin : ∀ {c : Finset (Set (E d))} {G : Set (E d)}, (c : Set (Set (E d))) ⊆ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T →
      (∀ F ∈ c, F ⊆ G) → Convex ℝ G → convexHull ℝ (b '' (c : Set (Set (E d)))) ⊆ G := by
    intro c G hc hG hconv
    refine convexHull_min ?_ hconv
    rintro _ ⟨F, hF, rfl⟩
    exact hG F hF (intrinsicInterior_subset (hb F (hc hF)))
  suffices H : ∀ n : ℕ, ∀ c₁ c₂ : Finset (Set (E d)), c₁.card + c₂.card = n →
      (c₁ : Set (Set (E d))) ⊆ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T → (c₂ : Set (Set (E d))) ⊆ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T →
      IsChain (· ⊆ ·) (c₁ : Set (Set (E d))) → IsChain (· ⊆ ·) (c₂ : Set (Set (E d))) →
      ∀ x, x ∈ convexHull ℝ (b '' (c₁ : Set (Set (E d)))) →
        x ∈ convexHull ℝ (b '' (c₂ : Set (Set (E d)))) →
        x ∈ convexHull ℝ (b '' ((c₁ : Set (Set (E d))) ∩ c₂)) by
    rintro x ⟨hx₁, hx₂⟩
    exact H _ c₁ c₂ rfl hc₁ hc₂ hch₁ hch₂ x hx₁ hx₂
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c₁ c₂ hn hc₁ hc₂ hch₁ hch₂ x hx₁ hx₂
  rcases c₁.eq_empty_or_nonempty with rfl | hne₁
  · simp at hx₁
  rcases c₂.eq_empty_or_nonempty with rfl | hne₂
  · simp at hx₂
  obtain ⟨G₁, hG₁c, hG₁⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step4_chain_top hne₁ hch₁
  obtain ⟨G₂, hG₂c, hG₂⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step4_chain_top hne₂ hch₂
  have hG₁f : G₁ ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T := hc₁ hG₁c
  have hG₂f : G₂ ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T := hc₂ hG₂c
  have hsub₁ : ((c₁.erase G₁ : Finset (Set (E d))) : Set (Set (E d))) ⊆ c₁ :=
    Finset.coe_subset.mpr (c₁.erase_subset G₁)
  have hsub₂ : ((c₂.erase G₂ : Finset (Set (E d))) : Set (Set (E d))) ⊆ c₂ :=
    Finset.coe_subset.mpr (c₂.erase_subset G₂)
  have hlt₁ := Finset.card_erase_lt_of_mem hG₁c
  have hlt₂ := Finset.card_erase_lt_of_mem hG₂c
  by_cases hr₁ : x ∈ convexHull ℝ (b '' ((c₁.erase G₁ : Finset (Set (E d))) : Set (Set (E d))))
  · exact convexHull_mono (Set.image_mono (Set.inter_subset_inter_left _ hsub₁))
      (ih _ (by omega) (c₁.erase G₁) c₂ rfl (hsub₁.trans hc₁) hc₂ (hch₁.mono hsub₁) hch₂
        x hr₁ hx₂)
  by_cases hr₂ : x ∈ convexHull ℝ (b '' ((c₂.erase G₂ : Finset (Set (E d))) : Set (Set (E d))))
  · exact convexHull_mono (Set.image_mono (Set.inter_subset_inter_right _ hsub₂))
      (ih _ (by omega) c₁ (c₂.erase G₂) rfl hc₁ (hsub₂.trans hc₂) hch₁ (hch₂.mono hsub₂)
        x hx₁ hr₂)
  have P₁ : x = b G₁ ∨ ∃ y ∈ convexHull ℝ
      (b '' ((c₁.erase G₁ : Finset (Set (E d))) : Set (Set (E d)))),
      x ∈ openSegment ℝ (b G₁) y := by
    rcases principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step8_chain_split hG₁c hx₁ with h | ⟨y, hy, h | h⟩
    · exact Or.inl h
    · exact absurd (h ▸ hy) hr₁
    · exact Or.inr ⟨y, hy, h⟩
  have P₂ : x = b G₂ ∨ ∃ y ∈ convexHull ℝ
      (b '' ((c₂.erase G₂ : Finset (Set (E d))) : Set (Set (E d)))),
      x ∈ openSegment ℝ (b G₂) y := by
    rcases principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step8_chain_split hG₂c hx₂ with h | ⟨y, hy, h | h⟩
    · exact Or.inl h
    · exact absurd (h ▸ hy) hr₂
    · exact Or.inr ⟨y, hy, h⟩
  have hxG₁ : x ∈ G₁ := hin hc₁ hG₁ (hconvF hG₁f) hx₁
  have hxG₂ : x ∈ G₂ := hin hc₂ hG₂ (hconvF hG₂f) hx₂
  have hcross : ∀ {G G' : Set (E d)} {y : E d}, G ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T → G' ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T →
      x ∈ G → x ∈ G' → y ∈ G → (x = b G ∨ x ∈ openSegment ℝ (b G) y) → G ⊆ G' := by
    intro G G' y hG hG' hxG hxG' hyG h
    apply principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step8_relint_subset T hface hG hG' (hb G hG)
    rcases h with h | h
    · exact h ▸ hxG'
    · exact ((principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step8_inter_extreme T hface hG hG').left_mem_of_mem_openSegment
        (intrinsicInterior_subset (hb G hG)) hyG ⟨hxG, hxG'⟩ h).2
  have hside : ∀ {c : Finset (Set (E d))} {G : Set (E d)}, (c : Set (Set (E d))) ⊆ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T →
      G ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T → (∀ F ∈ c, F ⊆ G) → x ∈ G →
      (x = b G ∨ ∃ y ∈ convexHull ℝ
        (b '' ((c.erase G : Finset (Set (E d))) : Set (Set (E d)))),
        x ∈ openSegment ℝ (b G) y) →
      ∀ {G' : Set (E d)}, G' ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T → x ∈ G' → G ⊆ G' := by
    intro c G hc hGf hG hxG P G' hG' hxG'
    rcases P with h | ⟨y, hy, h⟩
    · exact hcross hGf hG' hxG hxG' (intrinsicInterior_subset (hb G hGf)) (Or.inl h)
    · have hsub : ((c.erase G : Finset (Set (E d))) : Set (Set (E d))) ⊆ c :=
        Finset.coe_subset.mpr (c.erase_subset G)
      have hyG : y ∈ G := hin (hsub.trans hc) (fun F hF => hG F (Finset.mem_of_mem_erase hF))
        (hconvF hGf) hy
      exact hcross hGf hG' hxG hxG' hyG (Or.inr h)
  have hG12 : G₁ ⊆ G₂ := hside hc₁ hG₁f hG₁ hxG₁ P₁ hG₂f hxG₂
  have hG21 : G₂ ⊆ G₁ := hside hc₂ hG₂f hG₂ hxG₂ P₂ hG₁f hxG₁
  have hG : G₁ = G₂ := Set.Subset.antisymm hG12 hG21
  subst hG
  have hGboth : b G₁ ∈ b '' ((c₁ : Set (Set (E d))) ∩ c₂) := ⟨G₁, ⟨hG₁c, hG₂c⟩, rfl⟩
  rcases P₁ with h | ⟨y₁, hy₁, h₁⟩
  · rw [h]
    exact subset_convexHull ℝ _ hGboth
  rcases P₂ with h | ⟨y₂, hy₂, h₂⟩
  · rw [h]
    exact subset_convexHull ℝ _ hGboth
  have htop : ∀ {c : Finset (Set (E d))} {y : E d}, (c : Set (Set (E d))) ⊆ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T →
      IsChain (· ⊆ ·) (c : Set (Set (E d))) → (∀ F ∈ c, F ⊆ G₁) →
      y ∈ convexHull ℝ (b '' ((c.erase G₁ : Finset (Set (E d))) : Set (Set (E d)))) →
      ∃ H : Set (E d), IsExtreme ℝ G₁ H ∧ b G₁ ∉ H ∧ y ∈ H := by
    intro c y hc hch hG hy
    have hsub : ((c.erase G₁ : Finset (Set (E d))) : Set (Set (E d))) ⊆ c :=
      Finset.coe_subset.mpr (c.erase_subset G₁)
    have hne : (c.erase G₁).Nonempty := by
      rcases (c.erase G₁).eq_empty_or_nonempty with he | h
      · rw [he] at hy
        simp at hy
      · exact h
    obtain ⟨H, hHc, hH⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step4_chain_top hne (hch.mono hsub)
    have hHf : H ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T := hc (hsub hHc)
    have hHG : H ⊆ G₁ := hG H (Finset.mem_of_mem_erase hHc)
    have hHne : H ≠ G₁ := Finset.ne_of_mem_erase hHc
    have hext := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step2_face_extreme T hface hHf hG₁f hHG
    refine ⟨H, hext, fun h => ?_, hin (hsub.trans hc) hH (hconvF hHf) hy⟩
    exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step3_relint_not_mem_affineSpan (hconvF hHf) (hconvF hG₁f) hext hHne
      (hb G₁ hG₁f) (subset_affineSpan ℝ _ h)
  obtain ⟨H₁, hext₁, hz₁, hy₁H⟩ := htop hc₁ hch₁ hG₁ hy₁
  obtain ⟨H₂, hext₂, hz₂, hy₂H⟩ := htop hc₂ hch₂ hG₂ hy₂
  have hyy := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step8_ray_unique hext₁ hext₂ (intrinsicInterior_subset (hb G₁ hG₁f))
    hz₁ hz₂ hy₁H hy₂H h₁ h₂
  subst hyy
  have hy := ih _ (by omega) (c₁.erase G₁) (c₂.erase G₁) rfl (hsub₁.trans hc₁)
    (hsub₂.trans hc₂) (hch₁.mono hsub₁) (hch₂.mono hsub₂) y₁ hy₁ hy₂
  have hy' : y₁ ∈ convexHull ℝ (b '' ((c₁ : Set (Set (E d))) ∩ c₂)) :=
    convexHull_mono (Set.image_mono (Set.inter_subset_inter hsub₁ hsub₂)) hy
  exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ hGboth) hy'
    (openSegment_subset_segment ℝ _ _ h₁)

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation` (V4 1.24):
"a compact `(d-1)`-manifold". Subdivide a finite family of convex polytopes
meeting in common faces by taking barycentres of their nonempty faces and simplices
indexed by chains of faces. This step only constructs a finite geometric complex. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells
    (T : Finset (Finset (E d)))
    (hface : ∀ p ∈ T, ∀ q ∈ T,
      IsExtreme ℝ (convexHull ℝ (p : Set (E d)))
        (convexHull ℝ (p : Set (E d)) ∩ convexHull ℝ (q : Set (E d)))) :
    ∃ K : Geometry.SimplicialComplex ℝ (E d), K.faces.Finite ∧
      K.space = ⋃ p ∈ T, convexHull ℝ (p : Set (E d)) := by
  classical
  have hrel : ∀ F ∈ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T, ∃ z, z ∈ intrinsicInterior ℝ F := by
    rintro F ⟨_, _, _, hc, hne⟩
    exact hne.intrinsicInterior hc
  choose! b hb using hrel
  let faces : Set (Finset (E d)) := {s | ∃ c : Finset (Set (E d)),
    (c : Set (Set (E d))) ⊆ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T ∧ c.Nonempty ∧ IsChain (· ⊆ ·) (c : Set (Set (E d))) ∧
      (s : Set (E d)) = b '' (c : Set (Set (E d)))}
  have hindep : ∀ {s : Finset (E d)}, s ∈ faces → AffineIndependent ℝ ((↑) : s → E d) := by
    rintro s ⟨c, hc, -, hch, hs⟩
    have h := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step5_chain_indep T hface b hb c hc hch
    rw [← hs] at h
    exact h
  have hlower : IsRelLowerSet faces Finset.Nonempty := by
    rintro s ⟨c, hc, hne, hch, hs⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨F, hF⟩ := hne
      have hmem : b F ∈ (s : Set (E d)) := hs ▸ Set.mem_image_of_mem b (Finset.mem_coe.mpr hF)
      exact ⟨_, hmem⟩
    · intro t hts htne
      have hts' : ∀ z ∈ t, ∃ F ∈ c, b F = z := by
        intro z hz
        have hz' : z ∈ (s : Set (E d)) := Finset.mem_coe.mpr (hts hz)
        rw [hs] at hz'
        obtain ⟨F, hF, rfl⟩ := hz'
        exact ⟨F, hF, rfl⟩
      refine ⟨c.filter (fun F => b F ∈ t), ?_, ?_, ?_, ?_⟩
      · exact (Finset.coe_subset.mpr (Finset.filter_subset _ _)).trans hc
      · obtain ⟨z, hz⟩ := htne
        obtain ⟨F, hF, rfl⟩ := hts' z hz
        exact ⟨F, Finset.mem_filter.mpr ⟨hF, hz⟩⟩
      · exact hch.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
      · ext z
        constructor
        · intro hz
          obtain ⟨F, hF, rfl⟩ := hts' z hz
          exact ⟨F, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hF, hz⟩), rfl⟩
        · rintro ⟨F, hF, rfl⟩
          exact (Finset.mem_filter.mp hF).2
  have hinter : ∀ {s t : Finset (E d)}, s ∈ faces → t ∈ faces →
      convexHull ℝ ↑s ∩ convexHull ℝ ↑t ⊆ convexHull ℝ (s ∩ t : Set (E d)) := by
    rintro s t ⟨c₁, hc₁, -, hch₁, hs⟩ ⟨c₂, hc₂, -, hch₂, ht⟩
    rw [hs, ht]
    exact (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step8_chain_inter T hface b hb c₁ c₂ hc₁ hc₂ hch₁ hch₂).trans
      (convexHull_mono (Set.image_inter_subset _ _ _))
  let K : Geometry.SimplicialComplex ℝ (E d) :=
    { faces := faces
      indep := hindep
      isRelLowerSet_faces := hlower
      inter_subset_convexHull := hinter }
  refine ⟨K, ?_, ?_⟩
  · apply Set.Finite.subset
      ((((principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step1_faces_finite T).image b).finite_subsets).preimage
        Finset.coe_injective.injOn)
    rintro s ⟨c, hc, -, -, hs⟩
    show (s : Set (E d)) ⊆ b '' principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_faces T
    rw [hs]
    exact Set.image_mono hc
  · apply Set.Subset.antisymm
    · intro x hx
      rw [Geometry.SimplicialComplex.mem_space_iff] at hx
      obtain ⟨s, ⟨c, hc, hne, hch, hs⟩, hxs⟩ := hx
      obtain ⟨G, hGc, hG⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step4_chain_top hne hch
      obtain ⟨p, hp, hpG, hGconv, -⟩ := hc (Finset.mem_coe.mpr hGc)
      refine Set.mem_iUnion₂.mpr ⟨p, hp, hpG.1 ?_⟩
      rw [hs] at hxs
      refine convexHull_min ?_ hGconv hxs
      rintro z ⟨F, hF, rfl⟩
      exact hG F hF (intrinsicInterior_subset (hb F (hc hF)))
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨c, hc, hch, hxc⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells_step7_cover T b hb hp hxp
      rw [Geometry.SimplicialComplex.mem_space_iff]
      have hne : c.Nonempty := by
        rcases c.eq_empty_or_nonempty with rfl | h
        · simp at hxc
        · exact h
      refine ⟨c.image b, ⟨c, hc, hne, hch, by simp⟩, ?_⟩
      simpa using hxc

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation` (V4 1.24):
"a compact `(d-1)`-manifold". Inside a maximal simplex, avoid the affine spans
of its intersections with the other faces. Finiteness then gives an ambient open
set on which the complex agrees with the affine span of that simplex. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step3_facet_patch
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (f : Finset (E d)) (hf : f ∈ K.facets) :
    ∃ W : Set (E d), IsOpen W ∧ (W ∩ K.space).Nonempty ∧
      W ∩ K.space = W ∩ (affineSpan ℝ (f : Set (E d)) : Set (E d)) := by
  classical
  let A := affineSpan ℝ (f : Set (E d))
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hf.1
  letI : Nonempty A := ⟨⟨v, subset_affineSpan ℝ _ hv⟩⟩
  have hAclosed : IsClosed (A : Set (E d)) := A.closed_of_finiteDimensional
  letI : CompleteSpace A := hAclosed.completeSpace_coe
  let bad := K.faces \ {f}
  have hbadfin : bad.Finite := hfin.diff
  let L (g : Finset (E d)) : AffineSubspace ℝ A :=
    (affineSpan ℝ ((f ∩ g : Finset (E d)) : Set (E d))).comap A.subtype
  have hLne (g : Finset (E d)) (hg : g ∈ bad) : L g ≠ ⊤ := by
    intro htop
    have hfg : ¬ f ⊆ g := by
      intro hfg
      exact hg.2 (hf.2 hg.1 hfg).symm
    obtain ⟨w, hwf, hwg⟩ := Finset.not_subset.mp hfg
    let wA : A := ⟨w, subset_affineSpan ℝ _ hwf⟩
    have hwL : wA ∈ L g := by rw [htop]; trivial
    have hwspan : w ∈ affineSpan ℝ ((f ∩ g : Finset (E d)) : Set (E d)) := hwL
    have himg : ((↑) : f → E d) '' {i : f | (i : E d) ∈ g} =
        ((f ∩ g : Finset (E d)) : Set (E d)) := by
      ext z
      simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_inter]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i.property, hi⟩
      · rintro ⟨hzf, hzg⟩
        exact ⟨⟨z, hzf⟩, hzg, rfl⟩
    rw [← himg] at hwspan
    exact hwg ((K.indep hf.1).mem_affineSpan_iff ⟨w, hwf⟩ _ |>.mp hwspan)
  have hLdense (g : Finset (E d)) (hg : g ∈ bad) : Dense ((L g : Set A)ᶜ) := by
    apply interior_eq_empty_iff_dense_compl.mp
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have htop := isOpen_interior.affineSpan_eq_top ⟨x, hx⟩
    apply hLne g hg
    apply top_unique
    rw [← htop]
    exact affineSpan_le.mpr interior_subset
  have hdense : Dense (⋂ g ∈ bad, (L g : Set A)ᶜ) :=
    dense_biInter_of_isOpen (fun g _ => (L g).closed_of_finiteDimensional.isOpen_compl)
      hbadfin.countable hLdense
  have hri : (interior ((↑) ⁻¹' convexHull ℝ (f : Set (E d)) : Set A)).Nonempty := by
    have hn := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (f : Set (E d)))
      ⟨v, subset_convexHull ℝ (f : Set (E d)) hv⟩
    rw [intrinsicInterior, Set.image_nonempty, affineSpan_convexHull] at hn
    exact hn
  obtain ⟨x, hxri, hxavoid⟩ := hdense.inter_open_nonempty _ isOpen_interior hri
  have hi : Topology.IsInducing (Subtype.val : A → E d) := .subtypeVal
  obtain ⟨U, hU, hUri⟩ := hi.isOpen_iff.mp
    (isOpen_interior : IsOpen (interior ((↑) ⁻¹' convexHull ℝ (f : Set (E d)) : Set A)))
  let B : Set (E d) := ⋃ g ∈ bad, convexHull ℝ (g : Set (E d))
  have hBclosed : IsClosed B := hbadfin.isClosed_biUnion fun g _ =>
    g.finite_toSet.isCompact_convexHull.isClosed
  have hxf := interior_subset hxri
  have hxB : (x : E d) ∉ B := by
    intro hxB
    obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.mp hxB
    have hxfg := K.inter_subset_convexHull hf.1 hg.1 ⟨hxf, hxg⟩
    have hxspan : (x : E d) ∈ affineSpan ℝ ((f ∩ g : Finset (E d)) : Set (E d)) := by
      apply convexHull_subset_affineSpan
      simpa only [Finset.coe_inter] using hxfg
    exact (Set.mem_iInter₂.mp hxavoid g hg) hxspan
  refine ⟨U \ B, IsOpen.sdiff (show IsOpen U from hU) hBclosed, ?_, ?_⟩
  · refine ⟨x, ⟨?_, hxB⟩, K.convexHull_subset_space hf.1 hxf⟩
    change x ∈ (↑) ⁻¹' U
    rwa [hUri]
  · ext z
    constructor
    · rintro ⟨hzW, hzK⟩
      refine ⟨hzW, ?_⟩
      obtain ⟨g, hg, hzg⟩ := K.mem_space_iff.mp hzK
      by_cases hgf : g = f
      · subst g
        exact convexHull_subset_affineSpan _ hzg
      · exact (hzW.2 (Set.mem_iUnion₂.mpr ⟨g, ⟨hg, hgf⟩, hzg⟩)).elim
    · rintro ⟨hzW, hzA⟩
      refine ⟨hzW, K.convexHull_subset_space hf.1 ?_⟩
      have hzU : (⟨z, hzA⟩ : A) ∈ (↑) ⁻¹' U := hzW.1
      rw [hUri] at hzU
      have hz := interior_subset hzU
      exact hz

/-- Vertex `m` (`0 ≤ m ≤ k`) of the Kuhn simplex with base point `x : Fin k → Fin M` and
permutation `σ` of the grid `{0,…,M}^k`: `x + Σ_{σ j < m} e_j` (coordinate `j` is raised at
step `σ j`). Part of the proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex`. -/
private def principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex {k M : ℕ} (s : (Fin k → Fin M) × Equiv.Perm (Fin k)) (m : Fin (k + 1)) :
    Fin k → Fin (M + 1) :=
  fun j => ⟨(s.1 j : ℕ) + if ((s.2 j : Fin k) : ℕ) < (m : ℕ) then 1 else 0, by
    have := (s.1 j).isLt; split_ifs <;> omega⟩

/-- The labelling induced on the face `z 0 = M` of the grid `{0,…,M}^(k+1)`: the label of
`Fin.cons M y`, with the colour `some i.succ` renamed to `some i` (the colour `some 0` does
not occur on that face under the Sperner boundary condition and is sent to `none`). Part
of the proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex`. -/
private def principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_faceLabel {k M : ℕ} (ℓ : (Fin (k + 1) → Fin (M + 1)) → Option (Fin (k + 1))) :
    (Fin k → Fin (M + 1)) → Option (Fin k) :=
  fun y => (ℓ (Fin.cons (α := fun _ => Fin (M + 1)) (Fin.last M) y)).bind
    (fun i => if h : i = 0 then none else some (i.pred h))

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of dimension; Gale's Hex theorem, proved here
through Kuhn's cubical Sperner lemma).
Door count in one simplex: for `f : Fin (n+1) → α` with `|α| = n+1` and a label `a`, the
number of facets (omitted index `m`) whose labels are exactly `α ∖ {a}` is odd iff `f` is
surjective (it is `1` when `f` is a bijection, and `0` or `2` otherwise). -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step1_local_doors {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (f : Fin (n + 1) → α) (hα : Fintype.card α = n + 1) (a : α) :
    Odd (Finset.univ.filter
      (fun m => (Finset.univ.erase m).image f = Finset.univ.erase a)).card ↔
      Function.Surjective f := by
  classical
  constructor
  · intro hodd
    by_contra hns
    apply (Nat.not_even_iff_odd.mpr hodd)
    set S := Finset.univ.filter
      (fun m => (Finset.univ.erase m).image f = Finset.univ.erase a) with hS
    rcases S.eq_empty_or_nonempty with h0 | ⟨m, hm⟩
    · rw [h0]; exact ⟨0, rfl⟩
    · have hm' : (Finset.univ.erase m).image f = Finset.univ.erase a :=
        (Finset.mem_filter.mp hm).2
      have hfm : f m ≠ a := by
        intro hfa; apply hns; intro b
        by_cases hb : b = a
        · exact ⟨m, hfa.trans hb.symm⟩
        · have : b ∈ (Finset.univ.erase m).image f := by rw [hm']; simp [hb]
          obtain ⟨m0, -, h⟩ := Finset.mem_image.mp this
          exact ⟨m0, h⟩
      have hfm2 : f m ∈ (Finset.univ.erase m).image f := by rw [hm']; simp [hfm]
      obtain ⟨m', hm'1, hm'2⟩ := Finset.mem_image.mp hfm2
      have hmm' : m' ≠ m := Finset.ne_of_mem_erase hm'1
      have hinj : ∀ x ∈ S, Set.InjOn f ↑(Finset.univ.erase x) := by
        intro x hx
        have hx' := (Finset.mem_filter.mp hx).2
        rw [← Finset.card_image_iff, hx']
        simp [Finset.card_erase_of_mem, hα]
      have himg : ∀ x, x = m ∨ x = m' →
          (Finset.univ.erase x).image f = Finset.univ.image f := by
        intro x hx
        apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _))
        intro b hb
        obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hb
        by_cases hyx : y = x
        · rcases hx with hx | hx
          · rw [hyx, hx]
            exact Finset.mem_image.mpr
              ⟨m', Finset.mem_erase.mpr ⟨hmm', Finset.mem_univ _⟩, hm'2⟩
          · rw [hyx, hx]
            exact Finset.mem_image.mpr
              ⟨m, Finset.mem_erase.mpr ⟨hmm'.symm, Finset.mem_univ _⟩, hm'2.symm⟩
        · exact Finset.mem_image_of_mem f (Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ _⟩)
      have hS2 : S = {m, m'} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx
          by_contra hxx
          push_neg at hxx
          exact hmm' (hinj x hx
            (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hxx.2.symm, Finset.mem_univ _⟩))
            (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hxx.1.symm, Finset.mem_univ _⟩)) hm'2)
        · rintro (h | h)
          · rw [h]; exact hm
          · rw [h, hS, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            rw [himg _ (Or.inr rfl), ← himg m (Or.inl rfl), hm']
      rw [hS2, Finset.card_pair hmm'.symm]
      exact even_two
  · intro hsurj
    have hbij : Function.Bijective f := by
      rw [Fintype.bijective_iff_surjective_and_card]
      exact ⟨hsurj, by simp [hα]⟩
    obtain ⟨m0, hm0⟩ := hsurj a
    have hS1 : Finset.univ.filter
        (fun m => (Finset.univ.erase m).image f = Finset.univ.erase a) = {m0} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [Finset.image_erase hbij.1, Finset.image_univ_of_surjective hsurj]
      constructor
      · intro h
        apply hbij.1
        rw [hm0]
        by_contra hne
        have hmem : f m ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
        rw [← h] at hmem
        simp at hmem
      · intro h
        rw [h, hm0]
    rw [hS1, Finset.card_singleton]
    exact odd_one

/-- The pivot map of the Kuhn triangulation on pairs (Kuhn simplex of `{0,…,M}^(k+1)`,
omitted vertex index `m`): it returns the other Kuhn simplex through the same facet and the
index of its omitted vertex. For `m = 0` the base point moves up along the first step
(which becomes the last one), for `m = k + 1` it moves down along the last step (which
becomes the first one), otherwise the steps `m - 1` and `m` of the permutation are swapped
(coordinates are truncated so that the map is total). Part of the proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex`. -/
private def principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap {k M : ℕ} (p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2)) :
    ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2) :=
  if h0 : (p.2 : ℕ) = 0 then
    ((fun j => if j = p.1.2.symm 0 then
        ⟨min ((p.1.1 j : ℕ) + 1) (M - 1), by have := (p.1.1 j).isLt; omega⟩ else p.1.1 j,
      p.1.2.trans (finRotate (k + 1)).symm), Fin.last (k + 1))
  else if hl : (p.2 : ℕ) = k + 1 then
    ((fun j => if j = p.1.2.symm (Fin.last k) then
        ⟨(p.1.1 j : ℕ) - 1, by have := (p.1.1 j).isLt; omega⟩ else p.1.1 j,
      p.1.2.trans (finRotate (k + 1))), 0)
  else
    ((p.1.1, p.1.2.trans (Equiv.swap ⟨(p.2 : ℕ) - 1, by have := p.2.isLt; omega⟩
      ⟨p.2, by have := p.2.isLt; omega⟩)), p.2)

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of dimension; Gale's Hex theorem, proved here
through Kuhn's cubical Sperner lemma).
The pivot map at an omitted first vertex (`m = 0`): the new omitted index is the last one,
the permutation is rotated, the base point is raised (truncated) along the first step. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step2_pivot_first {k M : ℕ} (p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2))
    (h0 : (p.2 : ℕ) = 0) :
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).2 = Fin.last (k + 1) ∧ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).1.2 = p.1.2.trans (finRotate (k + 1)).symm ∧
      ∀ j, ((principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).1.1 j : ℕ) =
        if j = p.1.2.symm 0 then min ((p.1.1 j : ℕ) + 1) (M - 1) else p.1.1 j := by
  unfold principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap
  rw [dif_pos h0]
  refine ⟨rfl, rfl, fun j => ?_⟩
  try dsimp only
  split_ifs <;> rfl

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of dimension; Gale's Hex theorem, proved here
through Kuhn's cubical Sperner lemma).
The pivot map at an omitted last vertex (`m = k + 1`): the new omitted index is `0`, the
permutation is rotated back, the base point is lowered along the last step. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step3_pivot_last {k M : ℕ} (p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2))
    (h0 : ¬ (p.2 : ℕ) = 0) (hl : (p.2 : ℕ) = k + 1) :
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).2 = 0 ∧ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).1.2 = p.1.2.trans (finRotate (k + 1)) ∧
      ∀ j, ((principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).1.1 j : ℕ) =
        if j = p.1.2.symm (Fin.last k) then (p.1.1 j : ℕ) - 1 else p.1.1 j := by
  unfold principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap
  rw [dif_neg h0, dif_pos hl]
  refine ⟨rfl, rfl, fun j => ?_⟩
  try dsimp only
  split_ifs <;> rfl

/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of dimension; Gale's Hex theorem, proved here
through Kuhn's cubical Sperner lemma).
The pivot map at an inner omitted vertex (`0 < m < k + 1`): the steps `m - 1` and `m` of the
permutation are exchanged; base point and omitted index stay. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step4_pivot_swap {k M : ℕ} (p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2))
    (h0 : ¬ (p.2 : ℕ) = 0) (hl : ¬ (p.2 : ℕ) = k + 1) :
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).2 = p.2 ∧ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).1.1 = p.1.1 ∧
      ∀ j, (((principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).1.2 j : Fin (k + 1)) : ℕ) =
        if ((p.1.2 j : Fin (k + 1)) : ℕ) = (p.2 : ℕ) - 1 then (p.2 : ℕ)
        else if ((p.1.2 j : Fin (k + 1)) : ℕ) = p.2 then (p.2 : ℕ) - 1
        else ((p.1.2 j : Fin (k + 1)) : ℕ) := by
  unfold principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap
  rw [dif_neg h0, dif_neg hl]
  refine ⟨rfl, rfl, fun j => ?_⟩
  try dsimp only
  rw [Equiv.trans_apply, Equiv.swap_apply_def]
  have := p.2.isLt
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> omega

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of dimension; Gale's Hex theorem, proved here
through Kuhn's cubical Sperner lemma).
Pairing of interior doors (the pseudomanifold property of the Kuhn triangulation): under
the Sperner conditions, the doors (facets of Kuhn simplices labelled with all labels except
`some 0`) that do not lie on the face `z 0 = M` come in pairs, so their number is even. The
partner of a door is the other Kuhn simplex through the same facet (swap two consecutive
steps of `σ`, or shift the base point along the first/last step); a door on another
boundary face is impossible: on `z j = M` (`j ≠ 0`) the label `some j` is excluded, on
`z j = 0` the label `none` is excluded. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step5_pivot_pairs (k M : ℕ) (ℓ : (Fin (k + 1) → Fin (M + 1)) → Option (Fin (k + 1)))
    (hsome : ∀ z i, ℓ z = some i → (z i : ℕ) < M)
    (hnone : ∀ z, ℓ z = none → ∀ j, 0 < (z j : ℕ)) :
    Even (Finset.univ.filter
      (fun p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2) =>
        (Finset.univ.erase p.2).image (fun m => ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m)) =
            Finset.univ.erase (some 0) ∧
          ¬ ∀ m, m ≠ p.2 → (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m 0 : ℕ) = M)).card := by
  classical
  let F : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2) →
      Finset (Fin (k + 1) → Fin (M + 1)) :=
    fun p => (Finset.univ.erase p.2).image (fun m => principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m)
  have hdoorF : ∀ p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2),
      (Finset.univ.erase p.2).image (fun m => ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m)) = (F p).image ℓ := by
    intro p
    simp only [F, Finset.image_image]
    rfl
  have hfaceF : ∀ p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2),
      (∀ m, m ≠ p.2 → (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m 0 : ℕ) = M) ↔ ∀ v ∈ F p, (v 0 : ℕ) = M := by
    intro p
    simp only [F, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro h v ⟨m, hm, rfl⟩
      exact h m hm
    · intro h m hm
      exact h _ ⟨m, hm, rfl⟩
  have hkv : ∀ (s : (Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) (m : Fin (k + 2)) j,
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex s m j : ℕ) = (s.1 j : ℕ) + if ((s.2 j : Fin (k + 1)) : ℕ) < (m : ℕ) then 1 else 0 :=
    fun _ _ _ => rfl
  have hrot : ∀ a : Fin (k + 1), (a : ℕ) =
      if (finRotate (k + 1)).symm a = Fin.last k then 0
      else ((finRotate (k + 1)).symm a : ℕ) + 1 := by
    intro a
    conv_lhs => rw [← Equiv.apply_symm_apply (finRotate (k + 1)) a]
    exact coe_finRotate _
  -- case B: vertices
  have hvB : ∀ p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2),
      (p.2 : ℕ) = 0 → (p.1.1 (p.1.2.symm 0) : ℕ) + 1 < M →
      ∀ i : Fin (k + 1), principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).1 i.castSucc = principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 i.succ := by
    intro p h0 hx i
    obtain ⟨-, hσ, hxv⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step2_pivot_first p h0
    funext j
    apply Fin.ext
    rw [hkv, hkv, hxv j, hσ, Equiv.trans_apply, Fin.val_castSucc, Fin.val_succ]
    have hr := hrot (p.1.2 j)
    have hi := i.isLt
    by_cases hj : j = p.1.2.symm 0
    · rw [if_pos hj]
      have hσv : ((p.1.2 j : Fin (k + 1)) : ℕ) = 0 := by rw [hj, Equiv.apply_symm_apply]; rfl
      have hxj : (p.1.1 j : ℕ) + 1 < M := by rw [hj]; exact hx
      split_ifs at hr with hrl
      · have : (((finRotate (k + 1)).symm (p.1.2 j) : Fin (k + 1)) : ℕ) = k := by
          rw [hrl, Fin.val_last]
        split_ifs <;> omega
      · omega
    · rw [if_neg hj]
      have hσv : ((p.1.2 j : Fin (k + 1)) : ℕ) ≠ 0 := by
        intro h
        apply hj
        rw [Equiv.eq_symm_apply]
        exact Fin.ext h
      split_ifs at hr with hrl
      · omega
      · split_ifs <;> omega
  have hFB : ∀ p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2),
      (p.2 : ℕ) = 0 → (p.1.1 (p.1.2.symm 0) : ℕ) + 1 < M → F (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p) = F p := by
    intro p h0 hx
    have h2 := (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step2_pivot_first p h0).1
    have hp0 : p.2 = 0 := Fin.ext h0
    ext v
    simp only [F, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, h2, hp0]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨(i.castPred hi).succ, Fin.succ_ne_zero _, ?_⟩
      rw [← hvB p h0 hx, Fin.castSucc_castPred]
    · rintro ⟨i, hi, rfl⟩
      refine ⟨(i.pred hi).castSucc, (Fin.castSucc_lt_last _).ne, ?_⟩
      rw [hvB p h0 hx, Fin.succ_pred]
  -- involution, case B
  have hinvB : ∀ p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2),
      (p.2 : ℕ) = 0 → (p.1.1 (p.1.2.symm 0) : ℕ) + 1 < M → principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p) = p := by
    intro p h0 hx
    obtain ⟨h2, hσ, hxv⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step2_pivot_first p h0
    have hq0 : ¬ ((principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).2 : ℕ) = 0 := by rw [h2, Fin.val_last]; omega
    have hql : ((principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).2 : ℕ) = k + 1 := by rw [h2, Fin.val_last]
    obtain ⟨h2', hσ', hxv'⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step3_pivot_last (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p) hq0 hql
    have hj1 : (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).1.2.symm (Fin.last k) = p.1.2.symm 0 := by
      rw [hσ, Equiv.symm_trans_apply, Equiv.symm_symm, finRotate_last]
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · funext j
      apply Fin.ext
      rw [hxv', hj1, hxv j]
      by_cases hj : j = p.1.2.symm 0
      · rw [if_pos hj, if_pos hj]
        have : (p.1.1 j : ℕ) + 1 < M := by rw [hj]; exact hx
        omega
      · rw [if_neg hj, if_neg hj]
    · rw [hσ', hσ]
      ext j
      simp
    · rw [h2', Fin.ext_iff, h0]; rfl
  -- case C
  have hinvC : ∀ p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2),
      ¬ (p.2 : ℕ) = 0 → (p.2 : ℕ) = k + 1 → 1 ≤ (p.1.1 (p.1.2.symm (Fin.last k)) : ℕ) →
      ((principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).2 : ℕ) = 0 ∧ ((principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).1.1 ((principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).1.2.symm 0) : ℕ) + 1 < M ∧ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p) = p := by
    intro p h0 hl hx
    obtain ⟨h2, hσ, hxv⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step3_pivot_last p h0 hl
    have hq0 : ((principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).2 : ℕ) = 0 := by rw [h2]; rfl
    obtain ⟨h2', hσ', hxv'⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step2_pivot_first (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p) hq0
    have hj0 : (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).1.2.symm 0 = p.1.2.symm (Fin.last k) := by
      rw [Equiv.symm_apply_eq, hσ, Equiv.trans_apply, Equiv.apply_symm_apply, finRotate_last]
    refine ⟨hq0, ?_, ?_⟩
    · rw [hj0, hxv, if_pos rfl]
      have := (p.1.1 (p.1.2.symm (Fin.last k))).isLt
      omega
    · refine Prod.ext (Prod.ext ?_ ?_) ?_
      · funext j
        apply Fin.ext
        rw [hxv', hj0, hxv j]
        by_cases hj : j = p.1.2.symm (Fin.last k)
        · rw [if_pos hj, if_pos hj]
          have h1 : 1 ≤ (p.1.1 j : ℕ) := by rw [hj]; exact hx
          have := (p.1.1 j).isLt
          omega
        · rw [if_neg hj, if_neg hj]
      · rw [hσ', hσ]
        ext j
        simp
      · rw [h2', Fin.ext_iff, hl, Fin.val_last]
  -- case A
  have hvA : ∀ p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2),
      ¬ (p.2 : ℕ) = 0 → ¬ (p.2 : ℕ) = k + 1 → F (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p) = F p := by
    intro p h0 hl
    obtain ⟨h2, hx, hσ⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step4_pivot_swap p h0 hl
    simp only [F, h2]
    apply Finset.image_congr
    intro i hi
    have hi' : i ≠ p.2 := Finset.ne_of_mem_erase (Finset.mem_coe.mp hi)
    have hiv : (i : ℕ) ≠ p.2 := fun h => hi' (Fin.ext h)
    funext j
    apply Fin.ext
    rw [hkv, hkv, hx, hσ j]
    split_ifs <;> omega
  have hinvA : ∀ p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2),
      ¬ (p.2 : ℕ) = 0 → ¬ (p.2 : ℕ) = k + 1 → principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p) = p ∧ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p ≠ p := by
    intro p h0 hl
    obtain ⟨h2, hx, hσ⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step4_pivot_swap p h0 hl
    have h0' : ¬ ((principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).2 : ℕ) = 0 := by rw [h2]; exact h0
    have hl' : ¬ ((principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p).2 : ℕ) = k + 1 := by rw [h2]; exact hl
    obtain ⟨h22, hx2, hσ2⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step4_pivot_swap (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p) h0' hl'
    refine ⟨Prod.ext (Prod.ext (by rw [hx2, hx]) ?_) (by rw [h22, h2]), ?_⟩
    · ext j
      rw [hσ2 j, hσ j, h2]
      split_ifs <;> omega
    · intro he
      have hlt := p.2.isLt
      have key := hσ (p.1.2.symm ⟨(p.2 : ℕ) - 1, by omega⟩)
      rw [he, Equiv.apply_symm_apply] at key
      simp only [Fin.val_mk] at key
      split_ifs at key <;> omega
  -- saturation
  have hsatB : ∀ p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2),
      (p.2 : ℕ) = 0 →
      (Finset.univ.erase p.2).image (fun m => ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m)) = Finset.univ.erase (some 0) →
      (¬ ∀ m, m ≠ p.2 → (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m 0 : ℕ) = M) →
      (p.1.1 (p.1.2.symm 0) : ℕ) + 1 < M := by
    intro p h0 hd hf
    by_contra hcon
    have hxlt := (p.1.1 (p.1.2.symm 0)).isLt
    have hall : ∀ m, m ≠ p.2 → (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m (p.1.2.symm 0) : ℕ) = M := by
      intro m hm
      have hm0 : (m : ℕ) ≠ 0 := fun h => hm (Fin.ext (by rw [h, h0]))
      rw [hkv, Equiv.apply_symm_apply]
      simp only [Fin.val_zero]
      split_ifs <;> omega
    by_cases hj : p.1.2.symm 0 = 0
    · apply hf
      intro m hm
      have := hall m hm
      rw [hj] at this
      exact this
    · have hmem : some (p.1.2.symm 0) ∈ Finset.univ.erase (some 0) := by
        simp [hj]
      rw [← hd, Finset.mem_image] at hmem
      obtain ⟨m, hm, hlab⟩ := hmem
      have := hsome _ _ hlab
      rw [hall m (Finset.ne_of_mem_erase hm)] at this
      omega
  have hsatC : ∀ p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2),
      (p.2 : ℕ) = k + 1 →
      (Finset.univ.erase p.2).image (fun m => ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m)) = Finset.univ.erase (some 0) →
      1 ≤ (p.1.1 (p.1.2.symm (Fin.last k)) : ℕ) := by
    intro p hl hd
    by_contra hcon
    have hmem : (none : Option (Fin (k + 1))) ∈ Finset.univ.erase (some 0) := by simp
    rw [← hd, Finset.mem_image] at hmem
    obtain ⟨m, hm, hlab⟩ := hmem
    have := hnone _ hlab (p.1.2.symm (Fin.last k))
    have hm' : (m : ℕ) ≠ k + 1 := fun h => Finset.ne_of_mem_erase hm (Fin.ext (by rw [h, hl]))
    have hmlt := m.isLt
    rw [hkv, Equiv.apply_symm_apply, Fin.val_last] at this
    split_ifs at this <;> omega
  -- the set and the involution
  set S := Finset.univ.filter
      (fun p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2) =>
        (Finset.univ.erase p.2).image (fun m => ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m)) =
            Finset.univ.erase (some 0) ∧
          ¬ ∀ m, m ≠ p.2 → (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m 0 : ℕ) = M) with hS
  have htrans : ∀ p q, F q = F p → p ∈ S → q ∈ S := by
    intro p q hFq hp
    rw [hS, Finset.mem_filter] at hp ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [hdoorF, hFq, ← hdoorF]; exact hp.2.1
    · rw [hfaceF, hFq, ← hfaceF]; exact hp.2.2
  have hmemS : ∀ p ∈ S, F (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p) = F p ∧ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p) = p ∧ principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p ≠ p := by
    intro p hp
    have hp' := hp
    rw [hS, Finset.mem_filter] at hp'
    by_cases h0 : (p.2 : ℕ) = 0
    · have hx := hsatB p h0 hp'.2.1 hp'.2.2
      refine ⟨hFB p h0 hx, hinvB p h0 hx, ?_⟩
      intro he
      have := (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step2_pivot_first p h0).1
      rw [he] at this
      have := congrArg Fin.val this
      rw [Fin.val_last] at this
      omega
    · by_cases hl : (p.2 : ℕ) = k + 1
      · have hx := hsatC p hl hp'.2.1
        obtain ⟨hq0, hqx, hinv⟩ := hinvC p h0 hl hx
        refine ⟨?_, hinv, ?_⟩
        · have := hFB (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p) hq0 hqx
          rw [hinv] at this
          exact this.symm
        · intro he
          rw [he] at hq0
          exact h0 hq0
      · exact ⟨hvA p h0 hl, (hinvA p h0 hl).1, (hinvA p h0 hl).2⟩
  have hsum : ∑ p ∈ S, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun p _ => principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p) (fun _ _ => rfl)
      (fun p hp _ => (hmemS p hp).2.2)
      (fun p hp => htrans p (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_pivotMap p) (hmemS p hp).1 hp)
      (fun p hp => (hmemS p hp).2.1)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact (ZMod.natCast_eq_zero_iff_even).mp hsum

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of dimension; Gale's Hex theorem, proved here
through Kuhn's cubical Sperner lemma).
Doors on the face `z 0 = M` are exactly the facets `{v 1, …, v (k+1)}` of the Kuhn
simplices with `x 0 = M - 1`, `σ 0 = 0`, and they correspond bijectively to the fully
labelled Kuhn simplices of the face, labelled by the induced face labelling. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step6_face_doors (k M : ℕ) (ℓ : (Fin (k + 1) → Fin (M + 1)) → Option (Fin (k + 1)))
    (hsome : ∀ z i, ℓ z = some i → (z i : ℕ) < M) (hM : 0 < M) :
    (Finset.univ.filter
      (fun p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2) =>
        (Finset.univ.erase p.2).image (fun m => ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m)) =
            Finset.univ.erase (some 0) ∧
          ∀ m, m ≠ p.2 → (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m 0 : ℕ) = M)).card =
      (Finset.univ.filter (fun s : (Fin k → Fin M) × Equiv.Perm (Fin k) =>
        ∀ o : Option (Fin k), ∃ m, principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_faceLabel ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex s m) = o)).card := by
  classical
  let x0 : Fin M := ⟨M - 1, by omega⟩
  let jmap : (Fin k → Fin M) × Equiv.Perm (Fin k) →
      ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2) :=
    fun t => ((Fin.cons x0 t.1, Equiv.Perm.decomposeFin.symm (0, t.2)), 0)
  let imap : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2) →
      (Fin k → Fin M) × Equiv.Perm (Fin k) :=
    fun p => (Fin.tail p.1.1, (Equiv.Perm.decomposeFin p.1.2).2)
  have hvert : ∀ t : (Fin k → Fin M) × Equiv.Perm (Fin k), ∀ m : Fin (k + 1),
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex (jmap t).1 m.succ = Fin.cons (α := fun _ => Fin (M + 1)) (Fin.last M) (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex t m) := by
    intro t m
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · apply Fin.ext
      simp only [principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex, jmap, x0, Fin.cons_zero, Equiv.Perm.decomposeFin_symm_apply_zero,
        Fin.val_succ, Fin.val_zero, Fin.val_last]
      split_ifs <;> omega
    · apply Fin.ext
      simp only [principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex, jmap, Fin.cons_succ, Equiv.Perm.decomposeFin_symm_apply_succ,
        Equiv.swap_self, Equiv.refl_apply, Fin.val_succ]
      split_ifs <;> omega
  have hfl : ∀ u : Option (Fin (k + 1)), u ≠ some 0 → ∀ o : Option (Fin k),
      (u.bind (fun i => if h : i = 0 then none else some (i.pred h)) = o ↔
        u = o.map Fin.succ) := by
    intro u hu o
    cases u with
    | none => cases o <;> simp
    | some i =>
      have hi : i ≠ 0 := fun h => hu (by rw [h])
      cases o with
      | none => simp [hi]
      | some o' => simp [hi, Fin.pred_eq_iff_eq_succ]
  have hg0 : ∀ y : Fin k → Fin (M + 1),
      ℓ (Fin.cons (α := fun _ => Fin (M + 1)) (Fin.last M) y) ≠ some 0 := by
    intro y h
    have := hsome _ _ h
    rw [Fin.cons_zero] at this
    simp at this
  have hdoor : ∀ t : (Fin k → Fin M) × Equiv.Perm (Fin k),
      ((Finset.univ.erase (jmap t).2).image (fun m => ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex (jmap t).1 m)) =
          Finset.univ.erase (some 0)) ↔
        ∀ o : Option (Fin k), ∃ m, principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_faceLabel ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex t m) = o := by
    intro t
    have himg : ∀ o', o' ∈ (Finset.univ.erase (jmap t).2).image (fun m => ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex (jmap t).1 m)) ↔
        ∃ m : Fin (k + 1), ℓ (Fin.cons (α := fun _ => Fin (M + 1)) (Fin.last M) (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex t m)) = o' := by
      intro o'
      simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · rintro ⟨m, hm, h⟩
        refine ⟨m.pred hm, ?_⟩
        rw [← hvert, Fin.succ_pred]
        exact h
      · rintro ⟨m, h⟩
        exact ⟨m.succ, Fin.succ_ne_zero m, by rw [hvert]; exact h⟩
    have hfl' : ∀ m o, principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_faceLabel ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex t m) = o ↔
        ℓ (Fin.cons (α := fun _ => Fin (M + 1)) (Fin.last M) (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex t m)) = o.map Fin.succ :=
      fun m o => hfl _ (hg0 _) o
    rw [Finset.ext_iff]
    simp only [himg, hfl', Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro h o
      exact (h (o.map Fin.succ)).2 (by cases o <;> simp [Fin.succ_ne_zero])
    · intro h o'
      constructor
      · rintro ⟨m, hm⟩
        rw [← hm]
        exact hg0 _
      · intro ho'
        cases o' with
        | none => obtain ⟨m, hm⟩ := h none; exact ⟨m, hm⟩
        | some i =>
          have hi : i ≠ 0 := fun hh => ho' (by rw [hh])
          obtain ⟨m, hm⟩ := h (some (i.pred hi))
          refine ⟨m, ?_⟩
          rw [hm]
          simp
  have hfst : ∀ σ : Equiv.Perm (Fin (k + 1)), (Equiv.Perm.decomposeFin σ).1 = σ 0 := by
    intro σ
    have := Equiv.Perm.decomposeFin_symm_apply_zero (Equiv.Perm.decomposeFin σ).1
      (Equiv.Perm.decomposeFin σ).2
    rw [Prod.mk.eta, Equiv.symm_apply_apply] at this
    exact this.symm
  have hshape : ∀ p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2),
      (∀ m, m ≠ p.2 → (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m 0 : ℕ) = M) → jmap (imap p) = p := by
    rintro ⟨⟨x, σ⟩, m⟩ hf
    have hx := (x 0).isLt
    have hm0 : m = 0 := by
      by_contra hm
      have := hf 0 (Ne.symm hm)
      simp only [principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex, Fin.val_zero] at this
      split_ifs at this <;> omega
    subst hm0
    have h1 := hf 1 (by simp)
    simp only [principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex, Fin.val_one] at h1
    have hσ : σ 0 = 0 := by
      by_contra hne
      have : (1 : ℕ) ≤ (σ 0 : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => hne (Fin.ext h))
      split_ifs at h1 <;> omega
    have hx0 : x 0 = x0 := by
      apply Fin.ext
      show (x 0 : ℕ) = M - 1
      split_ifs at h1 <;> omega
    simp only [jmap, imap]
    refine Prod.ext (Prod.ext ?_ ?_) rfl
    · show Fin.cons x0 (Fin.tail x) = x
      rw [← hx0, Fin.cons_self_tail]
    · show Equiv.Perm.decomposeFin.symm (0, (Equiv.Perm.decomposeFin σ).2) = σ
      rw [← hσ, ← hfst σ, Prod.mk.eta, Equiv.symm_apply_apply]
  apply Finset.card_nbij' imap jmap
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hdoor, hshape p hp.2.2]
    exact hp.2.1
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter] at ht
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (hdoor t).2 ht.2, ?_⟩
    intro m hm
    have hm' : m ≠ 0 := hm
    rw [← Fin.succ_pred m hm', hvert, Fin.cons_zero, Fin.val_last]
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    exact hshape p hp.2.2
  · intro t _
    simp only [jmap, imap, Fin.tail_cons, Equiv.apply_symm_apply]

/-- Step 7 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of dimension; Gale's Hex theorem, proved here
through Kuhn's cubical Sperner lemma).
Kuhn's cubical Sperner lemma, counting form: under the boundary conditions (a label
`some i` only off the face `z i = M`, the label `none` only off all faces `z j = 0`) the
number of fully labelled Kuhn simplices of `{0,…,M}^k` is odd. Induction on `k` by door
counting (Steps 1–3). -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step7_odd_count (k M : ℕ) : ∀ (ℓ : (Fin k → Fin (M + 1)) → Option (Fin k)),
    (∀ z i, ℓ z = some i → (z i : ℕ) < M) →
    (∀ z, ℓ z = none → ∀ j, 0 < (z j : ℕ)) →
    Odd (Finset.univ.filter (fun s : (Fin k → Fin M) × Equiv.Perm (Fin k) =>
      ∀ o : Option (Fin k), ∃ m, ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex s m) = o)).card := by
  induction k with
  | zero =>
    intro ℓ _ _
    rw [Finset.filter_true_of_mem]
    · simp
    · intro s _ o
      refine ⟨0, ?_⟩
      cases o with
      | none =>
        cases h : ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex s 0) with
        | none => rfl
        | some i => exact i.elim0
      | some i => exact i.elim0
  | succ k ih =>
    intro ℓ hsome hnone
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      exfalso
      cases h : ℓ (fun _ => 0) with
      | none => have := hnone _ h 0; simp at this
      | some i => have := hsome _ i h; simp at this
    have hsome' : ∀ y i, principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_faceLabel ℓ y = some i → (y i : ℕ) < M := by
      intro y i h
      simp only [principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_faceLabel, Option.bind_eq_some_iff] at h
      obtain ⟨i', hi', h2⟩ := h
      split_ifs at h2 with h0
      obtain rfl := Option.some.inj h2
      have := hsome _ _ hi'
      rw [← Fin.succ_pred i' h0, Fin.cons_succ] at this
      exact this
    have hnone' : ∀ y, principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_faceLabel ℓ y = none → ∀ j, 0 < (y j : ℕ) := by
      intro y h j
      cases h' : ℓ (Fin.cons (α := fun _ => Fin (M + 1)) (Fin.last M) y) with
      | none =>
        have := hnone _ h' j.succ
        rw [Fin.cons_succ] at this
        exact this
      | some i' =>
        simp only [principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_faceLabel, h', Option.bind_some] at h
        split_ifs at h with h0
        have := hsome _ _ h'
        rw [h0, Fin.cons_zero] at this
        simp at this
    have hface := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step6_face_doors k M ℓ hsome hM
    have hpiv := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step5_pivot_pairs k M ℓ hsome hnone
    have hIH := ih (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_faceLabel ℓ) hsome' hnone'
    have hDsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter
        (fun p : ((Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1))) × Fin (k + 2) =>
          (Finset.univ.erase p.2).image (fun m => ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m)) =
            Finset.univ.erase (some 0)))
      (fun p => ∀ m, m ≠ p.2 → (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex p.1 m 0 : ℕ) = M)
    rw [Finset.filter_filter, Finset.filter_filter, hface] at hDsplit
    have hDodd := hDsplit ▸ hIH.add_even hpiv
    rw [Finset.card_filter, Fintype.sum_prod_type] at hDodd
    simp only [← Finset.card_filter] at hDodd
    rw [Finset.odd_sum_iff_odd_card_odd] at hDodd
    have hcongr : (Finset.univ.filter (fun s : (Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1)) =>
        ∀ o : Option (Fin (k + 1)), ∃ m, ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex s m) = o)) =
        Finset.univ.filter (fun s : (Fin (k + 1) → Fin M) × Equiv.Perm (Fin (k + 1)) =>
          Odd (Finset.univ.filter (fun m : Fin (k + 2) =>
            (Finset.univ.erase m).image (fun m => ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex s m)) =
              Finset.univ.erase (some 0))).card) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step1_local_doors (fun m => ℓ (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex s m)) (by simp) (some 0)).symm
    rw [hcongr]
    convert hDodd

/-- Step 8 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of dimension; Gale's Hex theorem, proved here
through Kuhn's cubical Sperner lemma).
Existence form of Kuhn's cubical Sperner lemma: some chain `v 0 ≤ … ≤ v k` of grid points
with differences in `{0,1}^k` carries all `k + 1` labels. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step8_kuhn_sperner (k M : ℕ) (ℓ : (Fin k → Fin (M + 1)) → Option (Fin k))
    (hsome : ∀ z i, ℓ z = some i → (z i : ℕ) < M)
    (hnone : ∀ z, ℓ z = none → ∀ j, 0 < (z j : ℕ)) :
    ∃ v : Fin (k + 1) → (Fin k → Fin (M + 1)),
      (∀ a b : Fin (k + 1), a ≤ b → ∀ j, (v a j : ℕ) ≤ v b j ∧ (v b j : ℕ) ≤ v a j + 1) ∧
      ∀ o : Option (Fin k), ∃ a, ℓ (v a) = o := by
  obtain ⟨s, hs⟩ := Finset.card_pos.mp (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step7_odd_count k M ℓ hsome hnone).pos
  rw [Finset.mem_filter] at hs
  refine ⟨principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex s, ?_, hs.2⟩
  intro a b hab j
  have hab' : (a : ℕ) ≤ b := hab
  simp only [principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_kuhnVertex]
  split_ifs <;> omega

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of Euclidean dimension, used to read off the
local dimension of the manifold). The combinatorial core, Gale's `k`-dimensional Hex
theorem (D. Gale, "The game of Hex and the Brouwer fixed-point theorem", 1979): colour
every point of the grid `{0,…,N}^k` with one of `k` colours; then for some colour `i`
there is a chain of `i`-coloured grid points, consecutive ones Hex-adjacent (their
difference lies in `{0,1}^k` or in `{0,-1}^k`; repetitions allowed), running from the face
`z i = 0` to the opposite face `z i = N`. (`k = 0`: no colouring exists; `N = 0`: a
one-point chain.) A finite statement about colourings, with no topology. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex (k N : ℕ) (c : (Fin k → Fin (N + 1)) → Fin k) :
    ∃ i : Fin k, ∃ L : ℕ, ∃ p : ℕ → (Fin k → Fin (N + 1)),
      ((p 0 i : ℕ) = 0) ∧ ((p L i : ℕ) = N) ∧ (∀ t ≤ L, c (p t) = i) ∧
      ∀ t < L, (∀ j, (p t j : ℕ) ≤ p (t + 1) j ∧ (p (t + 1) j : ℕ) ≤ p t j + 1) ∨
        (∀ j, (p (t + 1) j : ℕ) ≤ p t j ∧ (p t j : ℕ) ≤ p (t + 1) j + 1) := by
  classical
  by_contra hcon
  let sh : (Fin k → Fin (N + 2)) → (Fin k → Fin (N + 1)) :=
    fun z j => ⟨(z j : ℕ) - 1, by omega⟩
  have hsh : ∀ z j, ((sh z j : Fin (N + 1)) : ℕ) = (z j : ℕ) - 1 := fun _ _ => rfl
  let col : (Fin k → Fin (N + 2)) → Fin k := fun z =>
    if h : ∃ j, (z j : ℕ) = 0 then h.choose else c (sh z)
  have hcol_virt : ∀ z i, col z = i → (∃ j, (z j : ℕ) = 0) → (z i : ℕ) = 0 := by
    intro z i hzi h
    simp only [col, dif_pos h] at hzi
    subst hzi
    exact h.choose_spec
  have hcol_real : ∀ z, (∀ j, 0 < (z j : ℕ)) → col z = c (sh z) := by
    intro z hz
    have : ¬ ∃ j, (z j : ℕ) = 0 := fun ⟨j, hj⟩ => by have := hz j; omega
    simp only [col, dif_neg this]
  let Adj : (Fin k → Fin (N + 2)) → (Fin k → Fin (N + 2)) → Prop := fun a b =>
    (∀ j, (a j : ℕ) ≤ b j ∧ (b j : ℕ) ≤ a j + 1) ∨
      (∀ j, (b j : ℕ) ≤ a j ∧ (a j : ℕ) ≤ b j + 1)
  let R : Fin k → (Fin k → Fin (N + 2)) → Prop := fun i z =>
    ∃ L : ℕ, ∃ p : ℕ → (Fin k → Fin (N + 2)), (p 0 i : ℕ) = 0 ∧ p L = z ∧
      (∀ t ≤ L, col (p t) = i) ∧ ∀ t < L, Adj (p t) (p (t + 1))
  have htop : ∀ i z, R i z → (z i : ℕ) < N + 1 := by
    rintro i z ⟨L, p, h0, hL, hc, ha⟩
    by_contra hz
    have hzN : (z i : ℕ) = N + 1 := by have := (z i).isLt; omega
    have hvirt : ∀ t ≤ L, ¬ (∀ j, 0 < (p t j : ℕ)) → (p t i : ℕ) = 0 := by
      intro t ht hnr
      push_neg at hnr
      obtain ⟨j, hj⟩ := hnr
      exact hcol_virt _ _ (hc t ht) ⟨j, by omega⟩
    set s := Nat.findGreatest (fun t => ¬ ∀ j, 0 < (p t j : ℕ)) L with hs_def
    have hs0 : ¬ ∀ j, 0 < (p s j : ℕ) := by
      apply Nat.findGreatest_spec (P := fun t => ¬ ∀ j, 0 < (p t j : ℕ)) (m := 0)
        (Nat.zero_le _)
      intro h; have := h i; omega
    have hsL : s ≤ L := Nat.findGreatest_le L
    have hsi : (p s i : ℕ) = 0 := hvirt s hsL hs0
    have hslt : s < L := by
      rcases Nat.lt_or_ge s L with h | h
      · exact h
      · have hsL' : s = L := le_antisymm hsL h
        rw [hsL', hL] at hsi; omega
    have hreal : ∀ t, s < t → t ≤ L → ∀ j, 0 < (p t j : ℕ) := by
      intro t h1 h2
      by_contra hn
      have := Nat.le_findGreatest (P := fun t => ¬ ∀ j, 0 < (p t j : ℕ)) h2 hn
      omega
    apply hcon
    refine ⟨i, L - (s + 1), fun t => sh (p (s + 1 + t)), ?_, ?_, ?_, ?_⟩
    · rw [hsh]
      have h1 := hreal (s + 1) (by omega) (by omega) i
      rcases ha s hslt with h2 | h2
      · have := (h2 i).2; simp only [Nat.add_zero]; omega
      · have := (h2 i).1; simp only [Nat.add_zero]; omega
    · rw [hsh]
      have e : s + 1 + (L - (s + 1)) = L := by omega
      rw [e, hL]; omega
    · intro t ht
      rw [← hcol_real _ (hreal _ (by omega) (by omega))]
      exact hc _ (by omega)
    · intro t ht
      have h1 := hreal (s + 1 + t) (by omega) (by omega)
      have h2 := hreal (s + 1 + (t + 1)) (by omega) (by omega)
      have h3 := ha (s + 1 + t) (by omega)
      have e : s + 1 + t + 1 = s + 1 + (t + 1) := by omega
      rw [e] at h3
      rcases h3 with h3 | h3
      · left; intro j
        have := h3 j; have := h1 j; have := h2 j
        simp only [hsh]; omega
      · right; intro j
        have := h3 j; have := h1 j; have := h2 j
        simp only [hsh]; omega
  let ℓ : (Fin k → Fin (N + 2)) → Option (Fin k) := fun z =>
    if R (col z) z then some (col z) else none
  have hsome : ∀ z i, ℓ z = some i → (z i : ℕ) < N + 1 := by
    intro z i h
    simp only [ℓ] at h
    split_ifs at h with hR
    obtain rfl := Option.some.inj h
    exact htop _ _ hR
  have hnone : ∀ z, ℓ z = none → ∀ j, 0 < (z j : ℕ) := by
    intro z h j
    by_contra hj
    have hz : ∃ j, (z j : ℕ) = 0 := ⟨j, by omega⟩
    have hR : R (col z) z :=
      ⟨0, fun _ => z, hcol_virt z _ rfl hz, rfl, fun _ _ => rfl,
        fun t ht => absurd ht (Nat.not_lt_zero _)⟩
    simp only [ℓ, if_pos hR] at h
    cases h
  obtain ⟨v, hv, hlab⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex_step8_kuhn_sperner k (N + 1) ℓ hsome hnone
  obtain ⟨a, ha⟩ := hlab none
  have hnR : ¬ R (col (v a)) (v a) := by
    intro hR
    simp only [ℓ, if_pos hR] at ha
    cases ha
  obtain ⟨b, hb⟩ := hlab (some (col (v a)))
  have hRb : R (col (v b)) (v b) := by
    by_contra hR
    simp only [ℓ, if_neg hR] at hb
    cases hb
  have hcb : col (v b) = col (v a) := by
    simp only [ℓ, if_pos hRb] at hb
    exact Option.some.inj hb
  rw [hcb] at hRb
  obtain ⟨L, p, h0, hL, hc, hadj⟩ := hRb
  apply hnR
  refine ⟨L + 1, fun t => if t ≤ L then p t else v a, ?_, ?_, ?_, ?_⟩
  · simp only [if_pos (Nat.zero_le L)]; exact h0
  · simp only [if_neg (show ¬ L + 1 ≤ L by omega)]
  · intro t ht
    by_cases htL : t ≤ L
    · simp only [if_pos htL]; exact hc t htL
    · simp only [if_neg htL]
  · intro t ht
    by_cases htL : t < L
    · simp only [if_pos htL.le, if_pos (show t + 1 ≤ L by omega)]
      exact hadj t htL
    · have htL' : t = L := by omega
      subst htL'
      simp only [le_refl, if_true, if_neg (show ¬ t + 1 ≤ t by omega), hL]
      rcases le_total a b with hab | hba
      · right; intro j; exact hv a b hab j
      · left; intro j; exact hv b a hba j

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of Euclidean dimension, used to read off the
local dimension of the manifold). Approximate fixed points from Hex (Gale's argument): a
continuous self-map `G` of the unit cube `[0,1]^k` has, for every `ε > 0`, a point moved by
less than `ε` in every coordinate. Otherwise colour each grid point `z / N` by a coordinate
`i` moved by at least `ε`; along the Hex chain of colour `i` the sign of `G_i - x_i` goes
from `+` (face `x_i = 0`) to `-` (face `x_i = 1`), and at the switch two adjacent grid
points contradict uniform continuity. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step2_approx_fixed (k : ℕ) (G : (Fin k → ℝ) → (Fin k → ℝ))
    (hG : ContinuousOn G (Set.pi univ fun _ => Icc (0 : ℝ) 1))
    (hmaps : MapsTo G (Set.pi univ fun _ => Icc (0 : ℝ) 1) (Set.pi univ fun _ => Icc (0 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ Set.pi univ (fun _ => Icc (0 : ℝ) 1), ∀ i, |G x i - x i| < ε := by
  classical
  set C : Set (Fin k → ℝ) := Set.pi univ fun _ => Icc (0 : ℝ) 1 with hC
  by_contra hcon
  push_neg at hcon
  have hCc : IsCompact C := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hCc.uniformContinuousOn_of_continuous hG) (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / δ) (4 / ε))
  have hNd : 1 < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNe : 4 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_right _ _) hN)
  have hNpos : (0 : ℝ) < N := by
    rcases (Nat.cast_nonneg N : (0 : ℝ) ≤ N).lt_or_eq with h | h
    · exact h
    · rw [← h] at hNd; simp at hNd; linarith
  have h1δ : (1 : ℝ) / N ≤ δ := by rw [div_le_iff₀ hNpos]; linarith
  have h1ε : (1 : ℝ) / N ≤ ε / 4 := by rw [div_le_iff₀ hNpos]; linarith
  let e : (Fin k → Fin (N + 1)) → (Fin k → ℝ) := fun z j => ((z j : ℕ) : ℝ) / N
  have he : ∀ z, e z ∈ C := by
    intro z j _
    have hz : ((z j : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (z j).isLt
    refine ⟨by positivity, ?_⟩
    show ((z j : ℕ) : ℝ) / N ≤ 1
    rw [div_le_one hNpos]; exact hz
  let c : (Fin k → Fin (N + 1)) → Fin k := fun z => Classical.choose (hcon (e z) (he z))
  have hc : ∀ z, ε ≤ |G (e z) (c z) - e z (c z)| := fun z =>
    Classical.choose_spec (hcon (e z) (he z))
  obtain ⟨i, L, p, h0, hL, hcol, hadj⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step1_hex k N c
  let D : ℕ → ℝ := fun t => G (e (p t)) i - e (p t) i
  have hDabs : ∀ t ≤ L, ε ≤ |D t| := by
    intro t ht
    have := hc (p t)
    rwa [hcol t ht] at this
  have hD0 : ε ≤ D 0 := by
    have hx : e (p 0) i = 0 := by simp [e, h0]
    have hGi := (hmaps (he (p 0)) i (mem_univ _)).1
    rcases le_abs.mp (hDabs 0 (Nat.zero_le _)) with h | h
    · exact h
    · simp only [D, hx] at h hGi ⊢; linarith
  have hDL : ¬ ε ≤ D L := by
    have hx : e (p L) i = 1 := by
      simp only [e, hL]; exact div_self hNpos.ne'
    have hGi := (hmaps (he (p L)) i (mem_univ _)).2
    simp only [D, hx]; linarith
  have ivt : ∀ (P : ℕ → Prop) (L : ℕ), P 0 → ¬ P L → ∃ t < L, P t ∧ ¬ P (t + 1) := by
    intro P L hP0 hPL
    induction L with
    | zero => exact absurd hP0 hPL
    | succ L ih =>
      by_cases hP : P L
      · exact ⟨L, Nat.lt_succ_self L, hP, hPL⟩
      · obtain ⟨t, ht, h⟩ := ih hP
        exact ⟨t, Nat.lt_succ_of_lt ht, h⟩
  obtain ⟨t, ht, hpos, hneg⟩ := ivt (fun t => ε ≤ D t) L hD0 hDL
  have hneg' : D (t + 1) ≤ -ε := by
    rcases le_abs.mp (hDabs (t + 1) ht) with h | h
    · exact absurd h hneg
    · linarith
  have hstep : ∀ j, |e (p t) j - e (p (t + 1)) j| ≤ 1 / N := by
    intro j
    have hj : ((p t j : ℕ) : ℝ) ≤ (p (t + 1) j : ℕ) + 1 ∧
        ((p (t + 1) j : ℕ) : ℝ) ≤ (p t j : ℕ) + 1 := by
      have hn : (p t j : ℕ) ≤ (p (t + 1) j : ℕ) + 1 ∧ (p (t + 1) j : ℕ) ≤ (p t j : ℕ) + 1 := by
        rcases hadj t ht with h | h
        · obtain ⟨h1, h2⟩ := h j; exact ⟨by omega, h2⟩
        · obtain ⟨h1, h2⟩ := h j; exact ⟨h2, by omega⟩
      exact ⟨by exact_mod_cast hn.1, by exact_mod_cast hn.2⟩
    simp only [e]
    rw [← sub_div, abs_div, abs_of_pos hNpos]
    exact div_le_div_of_nonneg_right
      (abs_sub_le_iff.mpr ⟨by linarith [hj.1], by linarith [hj.2]⟩) hNpos.le
  have hdist : dist (e (p t)) (e (p (t + 1))) ≤ δ :=
    (dist_pi_le_iff hδ.le).mpr fun j => by rw [Real.dist_eq]; exact (hstep j).trans h1δ
  have hGd := (dist_le_pi_dist _ _ i).trans (hδG _ (he _) _ (he _) hdist)
  rw [Real.dist_eq] at hGd
  have hA := (abs_le.mp hGd).2
  have hB := (abs_le.mp ((hstep i).trans h1ε)).1
  simp only [D] at hpos hneg'
  linarith

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of Euclidean dimension, used to read off the
local dimension of the manifold). Brouwer's fixed point theorem for the cube `[0,1]^k`, from
the approximate fixed points of Step 2 by compactness: otherwise `x ↦ dist (G x) x` has a
positive minimum on the cube, and Step 2 with that `ε` gives a contradiction. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step3_cube_fixed (k : ℕ) (G : (Fin k → ℝ) → (Fin k → ℝ))
    (hG : ContinuousOn G (Set.pi univ fun _ => Icc (0 : ℝ) 1))
    (hmaps : MapsTo G (Set.pi univ fun _ => Icc (0 : ℝ) 1) (Set.pi univ fun _ => Icc (0 : ℝ) 1)) :
    ∃ x ∈ Set.pi univ (fun _ => Icc (0 : ℝ) 1), G x = x := by
  by_contra hcon
  push_neg at hcon
  have hCc : IsCompact (Set.pi univ fun _ : Fin k => Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hCne : (Set.pi univ fun _ : Fin k => Icc (0 : ℝ) 1).Nonempty :=
    ⟨fun _ => 0, fun _ _ => ⟨le_refl _, zero_le_one⟩⟩
  have hdc : ContinuousOn (fun x => dist (G x) x) (Set.pi univ fun _ : Fin k => Icc (0 : ℝ) 1) :=
    continuous_dist.comp_continuousOn (hG.prodMk continuousOn_id)
  obtain ⟨x0, hx0, hmin⟩ := hCc.exists_isMinOn hCne hdc
  have hm : 0 < dist (G x0) x0 := dist_pos.mpr (hcon x0 hx0)
  obtain ⟨x, hx, hxε⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step2_approx_fixed k G hG hmaps hm
  have hlt : dist (G x) x < dist (G x0) x0 :=
    (dist_pi_lt_iff hm).mpr fun i => by rw [Real.dist_eq]; exact hxε i
  have h3 : dist (G x0) x0 ≤ dist (G x) x := hmin hx
  exact (not_le.mpr hlt) h3

/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of Euclidean dimension, used to read off the
local dimension of the manifold). Brouwer's fixed point theorem for the closed unit ball of
`E k`, from Step 3: rescale the cube `[0,1]^k` onto `[-1,1]^k ⊇ closedBall 0 1`, compose `F`
with the radial retraction `x ↦ x / max 1 ‖x‖` onto the ball, and rescale back. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step4_ball_fixed (k : ℕ) (F : E k → E k)
    (hF : ContinuousOn F (Metric.closedBall 0 1))
    (hmaps : MapsTo F (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ x ∈ Metric.closedBall (0 : E k) 1, F x = x := by
  let ι : (Fin k → ℝ) → E k := fun y => WithLp.toLp 2 (fun j => 2 * y j - 1)
  let ρ : E k → E k := fun x => (max 1 ‖x‖)⁻¹ • x
  have hmax : ∀ x : E k, 0 < max 1 ‖x‖ := fun x => lt_of_lt_of_le one_pos (le_max_left _ _)
  have hρ : ∀ x, ρ x ∈ Metric.closedBall (0 : E k) 1 := by
    intro x
    rw [Metric.mem_closedBall, dist_zero_right]
    show ‖(max 1 ‖x‖)⁻¹ • x‖ ≤ 1
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (hmax x).le, inv_mul_le_iff₀ (hmax x), mul_one]
    exact le_max_right _ _
  have hρid : ∀ x ∈ Metric.closedBall (0 : E k) 1, ρ x = x := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    show (max 1 ‖x‖)⁻¹ • x = x
    rw [max_eq_left hx, inv_one, one_smul]
  have hρc : Continuous ρ :=
    ((continuous_const.max continuous_norm).inv₀ fun x => (hmax x).ne').smul continuous_id
  have hιc : Continuous ι := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    exact (continuous_const.mul (continuous_apply j)).sub continuous_const
  have hcomp : Continuous fun y => F (ρ (ι y)) :=
    hF.comp_continuous (hρc.comp hιc) fun y => hρ _
  let G : (Fin k → ℝ) → (Fin k → ℝ) := fun y j => (F (ρ (ι y)) j + 1) / 2
  have hGc : Continuous G := by
    refine continuous_pi fun j => ?_
    exact (((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hcomp).add
      continuous_const).div_const 2
  have hGm : MapsTo G (Set.pi univ fun _ => Icc (0 : ℝ) 1) (Set.pi univ fun _ => Icc (0 : ℝ) 1) := by
    intro y _ j _
    have hb := hmaps (hρ (ι y))
    rw [Metric.mem_closedBall, dist_zero_right] at hb
    have hj := (abs_le.mp ((Real.norm_eq_abs _).symm.le.trans
      ((PiLp.norm_apply_le (F (ρ (ι y))) j).trans hb)))
    show (F (ρ (ι y)) j + 1) / 2 ∈ Icc (0 : ℝ) 1
    constructor <;> linarith [hj.1, hj.2]
  obtain ⟨y, _, hy⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step3_cube_fixed k G hGc.continuousOn hGm
  have hfix : F (ρ (ι y)) = ι y := by
    ext j
    have := congrFun hy j
    simp only [G] at this
    show F (ρ (ι y)) j = 2 * y j - 1
    linarith
  have hin : ι y ∈ Metric.closedBall (0 : E k) 1 := hfix ▸ hmaps (hρ (ι y))
  refine ⟨ι y, hin, ?_⟩
  have h2 := hfix
  rwa [hρid _ hin] at h2

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of Euclidean dimension, used to read off the
local dimension of the manifold). Stability of zeros, from Brouwer (Step 4): a continuous map on the
closed unit ball that moves no point by more than `1` has a zero (apply the fixed point
theorem to `x ↦ x - F x`). -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step5_zero_stability (k : ℕ)
    (hB : ∀ F : E k → E k, ContinuousOn F (Metric.closedBall 0 1) →
      MapsTo F (Metric.closedBall 0 1) (Metric.closedBall 0 1) →
      ∃ x ∈ Metric.closedBall (0 : E k) 1, F x = x)
    (F : E k → E k) (hF : ContinuousOn F (Metric.closedBall 0 1))
    (hclose : ∀ x ∈ Metric.closedBall (0 : E k) 1, ‖F x - x‖ ≤ 1) :
    ∃ x ∈ Metric.closedBall (0 : E k) 1, F x = 0 := by
  obtain ⟨x, hx, hfix⟩ := hB (fun x => x - F x) (continuousOn_id.sub hF) (by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, ← norm_neg, neg_sub]
    exact hclose x hx)
  exact ⟨x, hx, by simpa using hfix⟩

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of Euclidean dimension, used to read off the
local dimension of the manifold). Perturbation off zero on a sphere: a continuous map
`E k → E k` can be changed by less than `δ` on a compact set so that it has no zero on a
given sphere (smooth approximation; the smooth image of the null sphere is null, so a small
translate misses `0`). -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step6_avoid_zero_on_sphere (k : ℕ) (G : E k → E k) (hG : Continuous G) {K : Set (E k)}
    (hK : IsCompact K) (c : E k) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ G' : E k → E k, Continuous G' ∧ (∀ y ∈ K, ‖G' y - G y‖ < δ) ∧
      ∀ y ∈ Metric.sphere c ε, G' y ≠ 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨G, hG, fun y _ => by simpa using hδ, fun y hy => ?_⟩
    exfalso
    have hyc : y = c := by
      ext i
      exact i.elim0
    rw [Metric.mem_sphere, hyc, dist_self] at hy
    exact hε.ne hy
  haveI : Nontrivial (E k) := ⟨⟨0, EuclideanSpace.single ⟨0, hk⟩ 1, by
    intro h
    have := congrArg (fun z : E k => z ⟨0, hk⟩) h
    simp at this⟩⟩
  have hL : IsCompact (Metric.cthickening 1 K) := hK.cthickening
  obtain ⟨r0, hr0, hr0G⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hL.uniformContinuousOn_of_continuous hG.continuousOn) (δ / 2) (half_pos hδ)
  have hr : 0 < min r0 1 := lt_min hr0 one_pos
  obtain ⟨H, hHc, hHG⟩ := hG.exists_contDiff_dist_le_of_forall_mem_ball_dist_le hr
  have hHK : ∀ a ∈ K, ‖H a - G a‖ ≤ δ / 2 := by
    intro a ha
    rw [← dist_eq_norm]
    refine hHG a (δ / 2) fun x hx => ?_
    have hxa : dist x a < min r0 1 := hx
    have m1 := min_le_left r0 1
    have m2 := min_le_right r0 1
    exact hr0G x (Metric.mem_cthickening_of_dist_le x a 1 K ha (by linarith))
      a (Metric.mem_cthickening_of_dist_le a a 1 K ha (by simp)) (by linarith)
  have hnull : MeasureTheory.volume (H '' Metric.sphere c ε) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      MeasureTheory.volume (hHc.differentiable (by simp)).differentiableOn
      (MeasureTheory.Measure.addHaar_sphere MeasureTheory.volume c ε)
  obtain ⟨v, hv, hvH⟩ : ∃ v ∈ Metric.ball (0 : E k) (δ / 2), v ∉ H '' Metric.sphere c ε := by
    by_contra hcon
    push_neg at hcon
    have hle := MeasureTheory.measure_mono (μ := MeasureTheory.volume)
      (show Metric.ball (0 : E k) (δ / 2) ⊆ H '' Metric.sphere c ε from hcon)
    rw [hnull] at hle
    exact (Metric.measure_ball_pos MeasureTheory.volume (0 : E k) (half_pos hδ)).ne'
      (le_antisymm hle (zero_le _))
  refine ⟨fun y => H y - v, hHc.continuous.sub continuous_const, fun y hy => ?_,
    fun y hy h0 => hvH ⟨y, hy, sub_eq_zero.mp h0⟩⟩
  have h1 := hHK y hy
  have h2 : ‖v‖ < δ / 2 := by simpa using hv
  calc ‖H y - v - G y‖ = ‖(H y - G y) - v‖ := by congr 1; abel
    _ ≤ ‖H y - G y‖ + ‖v‖ := norm_sub_le _ _
    _ < δ := by linarith

/-- Step 7 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of Euclidean dimension, used to read off the
local dimension of the manifold). Local invariance of domain from stability of zeros
(Tao's argument: Tietze-extend the inverse of `g`, push the image off a hypothetical missing
value onto a small sphere, perturb off zero there with Step 6, contradict Step 5): a continuous
injective map from the closed unit ball of `E k` to `E k` sends the centre to an interior point
of its image. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step7_domain_invariance (k : ℕ)
    (hZ : ∀ F : E k → E k, ContinuousOn F (Metric.closedBall 0 1) →
      (∀ x ∈ Metric.closedBall (0 : E k) 1, ‖F x - x‖ ≤ 1) →
      ∃ x ∈ Metric.closedBall (0 : E k) 1, F x = 0)
    (g : Metric.closedBall (0 : E k) 1 → E k) (hg : Continuous g)
    (hinj : Function.Injective g) :
    g ⟨0, Metric.mem_closedBall_self zero_le_one⟩ ∈ interior (range g) := by
  classical
  haveI : CompactSpace (Metric.closedBall (0 : E k) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hce : Topology.IsClosedEmbedding g := hg.isClosedEmbedding hinj
  obtain ⟨G, hGg⟩ := (⟨Subtype.val, continuous_subtype_val⟩ :
    C(Metric.closedBall (0 : E k) 1, E k)).exists_extension' hce
  have hGx : ∀ x, G (g x) = (x : E k) := fun x => congrFun hGg x
  set x0 : Metric.closedBall (0 : E k) 1 := ⟨0, Metric.mem_closedBall_self zero_le_one⟩
    with hx0
  set p := g x0 with hp
  have hGp : G p = 0 := hGx x0
  obtain ⟨η, hη, hηG⟩ := Metric.continuous_iff.mp G.continuous p (1 / 10) (by norm_num)
  have hGsmall : ∀ y, dist y p < η → ‖G y‖ < 1 / 10 := by
    intro y hy
    have := hηG y hy
    rwa [hGp, dist_zero_right] at this
  set ε := η / 3 with hεdef
  have hε : 0 < ε := by positivity
  rw [mem_interior]
  refine ⟨Metric.ball p ε, ?_, Metric.isOpen_ball, Metric.mem_ball_self hε⟩
  intro c hc
  rw [Metric.mem_ball] at hc
  by_contra hcr
  set S1 : Set (E k) := range g ∩ {y | ε ≤ dist y c} with hS1
  have hS1c : IsCompact S1 :=
    (isCompact_range hg).inter_right
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hGne : ∀ y ∈ S1, G y ≠ 0 := by
    rintro y ⟨⟨x, rfl⟩, hy⟩ h0
    rw [hGx] at h0
    have hx : g x = p := by rw [show x = x0 from Subtype.ext h0]
    simp only [mem_setOf_eq, hx] at hy
    rw [dist_comm] at hy
    linarith
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > 0, ∀ y ∈ S1, δ ≤ ‖G y‖ := by
    rcases S1.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨y0, hy0, hmin⟩ :=
        hS1c.exists_isMinOn h (continuous_norm.comp G.continuous).continuousOn
      exact ⟨‖G y0‖, norm_pos_iff.mpr (hGne y0 hy0), fun y hy => hmin hy⟩
  set δ' := min δ (1 / 10) with hδ'def
  have hδ' : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'1 : δ' ≤ δ := min_le_left _ _
  have hδ'2 : δ' ≤ 1 / 10 := min_le_right _ _
  obtain ⟨G', hG'c, hG'close, hG'ne⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step6_avoid_zero_on_sphere k G G.continuous (hS1c.union (isCompact_sphere c ε)) c hε hδ'
  have hcne : ∀ x, g x - c ≠ 0 := fun x h => hcr ⟨x, sub_eq_zero.mp h⟩
  let Φ : E k → E k := fun y => c + max (ε / ‖y - c‖) 1 • (y - c)
  have hΦc : Continuous fun x => Φ (g x) := by
    refine continuous_const.add (Continuous.smul ?_ (hg.sub continuous_const))
    exact (continuous_const.div (continuous_norm.comp (hg.sub continuous_const))
      (fun x => norm_ne_zero_iff.mpr (hcne x))).max continuous_const
  have key : ∀ x, G' (Φ (g x)) ≠ 0 ∧ ‖G' (Φ (g x)) - x‖ ≤ 1 := by
    intro x
    have hpos : 0 < ‖g x - c‖ := norm_pos_iff.mpr (hcne x)
    by_cases hfar : ε ≤ dist (g x) c
    · have hmax : max (ε / ‖g x - c‖) 1 = 1 := by
        apply max_eq_right
        rw [div_le_one hpos]
        rwa [dist_eq_norm] at hfar
      have hΦ : Φ (g x) = g x := by
        show c + max (ε / ‖g x - c‖) 1 • (g x - c) = g x
        rw [hmax, one_smul, add_sub_cancel]
      have hmem : g x ∈ S1 := ⟨⟨x, rfl⟩, hfar⟩
      have hcl := hG'close (g x) (Or.inl hmem)
      rw [hΦ]
      constructor
      · intro h0
        have := hδle _ hmem
        rw [h0, zero_sub, norm_neg] at hcl
        linarith
      · rw [hGx] at hcl
        linarith
    · push_neg at hfar
      have hd : ‖g x - c‖ < ε := by rwa [dist_eq_norm] at hfar
      have hmax : max (ε / ‖g x - c‖) 1 = ε / ‖g x - c‖ := by
        apply max_eq_left
        rw [le_div_iff₀ hpos]
        linarith
      have hsph : Φ (g x) ∈ Metric.sphere c ε := by
        rw [Metric.mem_sphere, dist_eq_norm]
        show ‖c + max (ε / ‖g x - c‖) 1 • (g x - c) - c‖ = ε
        rw [hmax, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity),
          div_mul_cancel₀ _ hpos.ne']
      have hcl := hG'close _ (Or.inr hsph)
      refine ⟨hG'ne _ hsph, ?_⟩
      have h1 : dist (Φ (g x)) p < η := by
        have := dist_triangle (Φ (g x)) c p
        rw [Metric.mem_sphere] at hsph
        linarith
      have h2 : dist (g x) p < η := by
        have := dist_triangle (g x) c p
        linarith
      have hA := hGsmall _ h1
      have hB := hGsmall _ h2
      rw [hGx] at hB
      have e1 := norm_sub_le (G' (Φ (g x))) (x : E k)
      have e2 := norm_sub_norm_le (G' (Φ (g x))) (G (Φ (g x)))
      linarith
  let F : E k → E k := fun z =>
    if h : z ∈ Metric.closedBall (0 : E k) 1 then G' (Φ (g ⟨z, h⟩)) else 0
  have hFc : ContinuousOn F (Metric.closedBall 0 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have : (Metric.closedBall (0 : E k) 1).restrict F = fun x => G' (Φ (g x)) := by
      funext x
      simp only [restrict_apply, F, dif_pos x.2]
    rw [this]
    exact hG'c.comp hΦc
  obtain ⟨z, hz, hFz⟩ := hZ F hFc (fun z hz => by
    have := (key ⟨z, hz⟩).2
    simpa only [F, dif_pos hz] using this)
  exact (key ⟨z, hz⟩).1 (by simpa only [F, dif_pos hz] using hFz)

/-- Step 8 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of Euclidean dimension, used to read off the
local dimension of the manifold). A closed `k`-ball does not embed continuously into
`E j` for `j < k`: composing with the coordinate inclusion `E j → E k`, the image would lie
in a proper coordinate hyperplane (empty interior), contradicting Step 7. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step8_ball_embedding_le {k j : ℕ} (g : Metric.closedBall (0 : E k) 1 → E j)
    (hg : Continuous g) (hinj : Function.Injective g) : k ≤ j := by
  by_contra hjk
  push_neg at hjk
  let ι : E j → E k := fun y =>
    WithLp.toLp 2 (fun i : Fin k => if h : (i : ℕ) < j then y ⟨i, h⟩ else 0)
  have hιc : Continuous ι := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    by_cases h : (i : ℕ) < j
    · simp only [h, dif_pos]
      exact (EuclideanSpace.proj (𝕜 := ℝ) (⟨i, h⟩ : Fin j)).continuous
    · simp only [h, dif_neg, not_false_eq_true]
      exact continuous_const
  have hιi : Function.Injective ι := by
    intro y y' hyy
    ext i
    have := congrArg (fun z : E k => z (Fin.castLE hjk.le i)) hyy
    simpa [ι] using this
  let j' : Fin k := ⟨j, hjk⟩
  let S : Submodule ℝ (E k) := LinearMap.ker (EuclideanSpace.proj (𝕜 := ℝ) j').toLinearMap
  have hrange : range (ι ∘ g) ⊆ (S : Set (E k)) := by
    rintro _ ⟨x, rfl⟩
    simp [S, ι, j']
  have hint := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step7_domain_invariance k (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step5_zero_stability k (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step4_ball_fixed k)) (ι ∘ g) (hιc.comp hg) (hιi.comp hinj)
  have hS : S = ⊤ :=
    S.eq_top_of_nonempty_interior' ⟨_, interior_mono hrange hint⟩
  have hmem : EuclideanSpace.single j' (1 : ℝ) ∈ S := by rw [hS]; trivial
  simp [S] at hmem

/-- Step 9 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension` (V4 1.24):
"a compact `(d-1)`-manifold" (invariance of Euclidean dimension, used to read off the
local dimension of the manifold). A nonempty open subset of `E a` admitting a continuous
injection into `E b` forces `a ≤ b`: restrict to a small closed ball and apply Step 8. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step9_open_embedding_le {a b : ℕ} {W : Set (E a)} (hW : IsOpen W) (hne : W.Nonempty)
    (ψ : W → E b) (hψ : Continuous ψ) (hinj : Function.Injective ψ) : a ≤ b := by
  obtain ⟨w, hw⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW w hw
  have hr : 0 < ε / 2 := half_pos hε
  have hmem (z : Metric.closedBall (0 : E a) 1) : w + (ε / 2) • (z : E a) ∈ W := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.le]
    have hz : ‖(z : E a)‖ ≤ 1 := by
      have := z.property
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    nlinarith
  refine principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step8_ball_embedding_le (fun z => ψ ⟨w + (ε / 2) • (z : E a), hmem z⟩)
    (hψ.comp (Continuous.subtype_mk (by fun_prop) _)) ?_
  intro z z' hzz
  have h1 := Subtype.mk.inj (hinj hzz)
  have h2 : (ε / 2) • (z : E a) = (ε / 2) • (z' : E a) := add_left_cancel h1
  exact Subtype.ext (smul_right_injective _ hr.ne' h2)

/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation` (V4 1.24):
"a compact `(d-1)`-manifold". Invariance of Euclidean dimension: nonempty
open subsets of two Euclidean spaces can be homeomorphic only when their
dimensions agree. Nonemptiness is essential here. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension
    {m n : ℕ} {U : Set (E m)} {V : Set (E n)}
    (hU : IsOpen U) (hV : IsOpen V) (hne : U.Nonempty)
    (h : Nonempty (U ≃ₜ V)) : m = n := by
  obtain ⟨φ⟩ := h
  obtain ⟨u, hu⟩ := hne
  refine le_antisymm
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step9_open_embedding_le hU ⟨u, hu⟩
      (fun x => (φ x : E n)) (by fun_prop)
      (fun x y hxy => φ.injective (Subtype.ext hxy)))
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step9_open_embedding_le hV ⟨_, (φ ⟨u, hu⟩).property⟩
      (fun y => (φ.symm y : E m)) (by fun_prop)
      (fun x y hxy => φ.symm.injective (Subtype.ext hxy)))

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation` (V4 1.24):
"a compact `(d-1)`-manifold". Restrict a manifold chart to a nonempty open
affine patch. Affine coordinates identify the patch with an open subset of the
Euclidean space of the affine direction dimension; compare the two charts. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step5_local_dimension
    {n : ℕ} {Q : Set (E d)} (hman : IsLocallyEuclidean n Q)
    (A : AffineSubspace ℝ (E d)) (W : Set (E d)) (hW : IsOpen W)
    (hne : (W ∩ Q).Nonempty) (hmodel : W ∩ Q = W ∩ (A : Set (E d))) :
    Module.finrank ℝ A.direction = n := by
  obtain ⟨p, hpW, hpQ⟩ := hne
  have hQofA {z : E d} (hzW : z ∈ W) (hzA : z ∈ A) : z ∈ Q := by
    have hz : z ∈ W ∩ (A : Set (E d)) := ⟨hzW, hzA⟩
    rw [← hmodel] at hz
    exact hz.2
  have hAofQ {z : E d} (hzW : z ∈ W) (hzQ : z ∈ Q) : z ∈ A := by
    have hz : z ∈ W ∩ Q := ⟨hzW, hzQ⟩
    rw [hmodel] at hz
    exact hz.2
  obtain ⟨U, hU, hpU, V, hV, ⟨e⟩⟩ := hman ⟨p, hpQ⟩
  obtain ⟨Z, hZ, hZU⟩ := isOpen_induced_iff.mp hU
  have hmemU {z : Q} (hz : (z : E d) ∈ Z) : z ∈ U := by
    rwa [← hZU]
  have hmemZ {z : Q} (hz : z ∈ U) : (z : E d) ∈ Z := by
    rwa [← hZU] at hz
  let a : A := ⟨p, hAofQ hpW hpQ⟩
  letI : Nonempty A := ⟨a⟩
  let c : A ≃ₜ E (Module.finrank ℝ A.direction) :=
    (AffineIsometryEquiv.constVSub ℝ a).toHomeomorph.trans
      (toEuclidean (E := A.direction)).toHomeomorph
  let D : Set A := (Subtype.val : A → E d) ⁻¹' (W ∩ Z)
  let H : Set U := (fun z : U => (z.val.val : E d)) ⁻¹' W
  have hD : IsOpen D := (hW.inter hZ).preimage continuous_subtype_val
  have hH : IsOpen H := hW.preimage (by fun_prop)
  let eDH : D ≃ₜ H :=
    { toFun := fun z =>
        ⟨⟨⟨z.val.val, hQofA z.property.1 z.val.property⟩,
          hmemU z.property.2⟩, z.property.1⟩
      invFun := fun z =>
        ⟨⟨z.val.val.val, hAofQ z.property z.val.val.property⟩,
          z.property, hmemZ z.val.property⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let f : D → E (Module.finrank ℝ A.direction) := c ∘ Subtype.val
  let g : H → E n := (Subtype.val : V → E n) ∘ e ∘ Subtype.val
  have hf : Topology.IsOpenEmbedding f :=
    c.isOpenEmbedding.comp hD.isOpenEmbedding_subtypeVal
  have hg : Topology.IsOpenEmbedding g :=
    hV.isOpenEmbedding_subtypeVal.comp (e.isOpenEmbedding.comp hH.isOpenEmbedding_subtypeVal)
  have hfne : (Set.range f).Nonempty :=
    ⟨f ⟨a, hpW, hmemZ hpU⟩, ⟨⟨a, hpW, hmemZ hpU⟩, rfl⟩⟩
  exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension
    hf.isOpen_range hg.isOpen_range hfne
    ⟨hf.isEmbedding.toHomeomorph.symm.trans (eDH.trans hg.isEmbedding.toHomeomorph)⟩

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation` (V4 1.24):
"a compact `(d-1)`-manifold". Affine independence makes the number of
vertices of a nonempty simplex one more than the dimension of its affine span. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step6_simplex_cardinality
    (K : Geometry.SimplicialComplex ℝ (E d))
    (f : Finset (E d)) (hf : f ∈ K.faces) :
    Module.finrank ℝ (affineSpan ℝ (f : Set (E d))).direction + 1 = f.card := by
  classical
  haveI : Nonempty f := (K.nonempty_of_mem_faces hf).to_subtype
  rw [direction_affineSpan]
  have hcard := (K.indep hf).finrank_vectorSpan_add_one
  have hrange : Set.range ((↑) : f → E d) = (f : Set (E d)) := Subtype.range_val
  rw [hrange] at hcard
  exact hcard.trans (Fintype.card_coe f)

/-- Step 7 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"a compact `(d-1)`-manifold". Triangulate a finite polyhedron compatibly with all
its convex pieces. Local Euclidean dimension makes every maximal simplex have
`d` vertices. No property of the ambient complement is requested. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation
    {Q : Set (E d)} (hQ : Polyhedron Q) (hman : IsLocallyEuclidean (d - 1) Q) :
    ∃ K : Geometry.SimplicialComplex ℝ (E d), K.faces.Finite ∧ K.space = Q ∧
      ∀ f ∈ K.facets, f.card = d := by
  obtain ⟨T, hT, hface⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step1_common_refinement hQ
  obtain ⟨K, hfin, hK⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step2_subdivide_cells T hface
  have hKQ : K.space = Q := hK.trans hT.symm
  rw [← hKQ] at hman
  refine ⟨K, hfin, hKQ, ?_⟩
  intro f hf
  obtain ⟨W, hW, hne, hmodel⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step3_facet_patch K hfin f hf
  have hdim :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step5_local_dimension
      hman (affineSpan ℝ (f : Set (E d))) W hW hne hmodel
  have hcard :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step6_simplex_cardinality K f hf.1
  have hd : 2 ≤ d := Fact.out
  omega

/-- Step 8 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"`∂t` is a compact `(d-1)`-manifold". Subdivide the finite polyhedral presentation
of the selected component into a finite pure geometric simplicial complex. This
asserts triangulation and dimension only, with no claim about its complement. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step8_triangulate
    (P : PolyManifoldDomain d) (F : E d ≃ᵃ[ℝ] E d)
    (p : E d) (hp : p ∈ frontier (F '' P.carrier)) :
    ∃ K : Geometry.SimplicialComplex ℝ (E d), K.faces.Finite ∧
      K.space = connectedComponentIn (frontier (F '' P.carrier)) p ∧
      ∀ f ∈ K.facets, f.card = d := by
  have hplaced :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step4_affine_polyhedral P.polyhedral F
  have hfront :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step5_frontier_polyhedral hplaced
  have hcomponent :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step6_component_polyhedral hfront p
  exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation
    hcomponent
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step3_compact_component P F p hp).2.2

/-- Step 9 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"a connected union of facets". In a finite complex every face is contained in a
maximal face, so the closed facets cover its space. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step9_facets_cover
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite) :
    K.space = ⋃ f : K.facets, convexHull ℝ (f.val : Set (E d)) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    let L := hfin.toFinset.filter (fun t => s ⊆ t)
    have hsL : s ∈ L := by simp [L, hs]
    obtain ⟨t, ht, hmax⟩ := L.exists_max_image Finset.card ⟨s, hsL⟩
    have htK : t ∈ K.faces := hfin.mem_toFinset.mp (Finset.mem_filter.mp ht).1
    have hst : s ⊆ t := (Finset.mem_filter.mp ht).2
    have htf : t ∈ K.facets := by
      refine ⟨htK, ?_⟩
      intro u hu htu
      apply Finset.eq_of_subset_of_card_le htu
      exact hmax u (Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hu, hst.trans htu⟩)
    exact Set.mem_iUnion.mpr ⟨⟨t, htf⟩, convexHull_mono (by simpa using hst) hxs⟩
  · exact Set.iUnion_subset fun f => K.convexHull_subset_space f.property.1

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree` (V4 1.24):
"a connected union of facets". Every face of a finite complex is contained in a
maximal face. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step1_facet_extension
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    {s : Finset (E d)} (hs : s ∈ K.faces) :
    ∃ f ∈ K.facets, s ⊆ f := by
  classical
  let L := hfin.toFinset.filter (fun t => s ⊆ t)
  have hsL : s ∈ L := by simp [L, hs]
  obtain ⟨f, hf, hmax⟩ := L.exists_max_image Finset.card ⟨s, hsL⟩
  have hfK : f ∈ K.faces := hfin.mem_toFinset.mp (Finset.mem_filter.mp hf).1
  have hsf : s ⊆ f := (Finset.mem_filter.mp hf).2
  refine ⟨f, ⟨hfK, ?_⟩, hsf⟩
  intro g hg hfg
  apply Finset.eq_of_subset_of_card_le hfg
  exact hmax g (Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hg, hsf.trans hfg⟩)

open scoped Topology in
/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree` (V4 1.24):
"a connected union of facets". An affine function nonnegative on a set is
strictly positive at each relative interior point if it is positive somewhere
on that set. Extrapolating a segment proves this supporting-hyperplane fact. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step2_positive_coordinate
    {C : Set (E d)} {p x : E d} (hp : p ∈ relint C) (hx : x ∈ C)
    (l : E d →ᵃ[ℝ] ℝ) (hl : ∀ y ∈ C, 0 ≤ l y) (hxpos : 0 < l x) :
    0 < l p := by
  by_contra hn
  have hpzero : l p = 0 := le_antisymm (le_of_not_gt hn) (hl p (intrinsicInterior_subset hp))
  obtain ⟨q, hq, rfl⟩ := hp
  let γ : ℝ → affineSpan ℝ C := fun t =>
    ⟨AffineMap.lineMap (q : E d) x (-t),
      AffineMap.lineMap_mem _ q.property (subset_affineSpan ℝ C hx)⟩
  have hγ : Continuous γ := by
    apply Continuous.subtype_mk
    fun_prop
  have hγ0 : γ 0 = q := by ext; simp [γ]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (γ t : E d) ∈ C := by
    exact (hγ.tendsto 0).eventually (show ∀ᶠ (y : affineSpan ℝ C) in 𝓝 (γ 0), (y : E d) ∈ C from by
      rw [hγ0]
      exact mem_interior_iff_mem_nhds.mp hq)
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  have hmem : (γ (δ / 2) : E d) ∈ C := hnear (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < δ / 2)]
    linarith)
  have hnonneg := hl _ hmem
  change 0 ≤ l (AffineMap.lineMap (q : E d) x (-(δ / 2))) at hnonneg
  rw [l.apply_lineMap, AffineMap.lineMap_apply_ring, hpzero] at hnonneg
  nlinarith

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree` (V4 1.24):
"a connected union of facets". A simplex containing a relative interior point
of a face contains that whole face. Barycentric coordinates detect every vertex. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step3_relint_incidence
    (K : Geometry.SimplicialComplex ℝ (E d)) {s t : Finset (E d)}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) {p : E d}
    (hp : p ∈ relint (convexHull ℝ (s : Set (E d))))
    (hpt : p ∈ convexHull ℝ (t : Set (E d))) : s ⊆ t := by
  classical
  obtain ⟨u, hsu, hu, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top (K.indep hs)
  let b : AffineBasis u ℝ (E d) := ⟨(↑), hu, by simpa using hspan⟩
  intro v hv
  by_contra hvt
  let i : u := ⟨v, hsu hv⟩
  have hnonneg : ∀ y ∈ convexHull ℝ (s : Set (E d)), 0 ≤ b.coord i y := by
    apply convexHull_min (t := {y | 0 ≤ b.coord i y}) ?_
      (Convex.affine_preimage (b.coord i) (convex_Ici 0))
    intro y hy
    change 0 ≤ b.coord i (b ⟨y, hsu hy⟩)
    simp only [b.coord_apply]
    split_ifs <;> norm_num
  have hpos : 0 < b.coord i p :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step2_positive_coordinate hp (subset_convexHull ℝ _ hv)
      (b.coord i) hnonneg (by change 0 < b.coord i (b i); simp)
  have hzero : convexHull ℝ (s ∩ t : Set (E d)) ⊆ {y | b.coord i y = 0} := by
    apply convexHull_min ?_ (Convex.affine_preimage (b.coord i) (convex_singleton 0))
    intro y hy
    let j : u := ⟨y, hsu hy.1⟩
    have hij : i ≠ j := by
      intro he
      have hvy : v = y := congrArg Subtype.val he
      exact hvt (by simpa only [hvy] using hy.2)
    change b.coord i (b j) = 0
    exact b.coord_apply_ne hij
  exact (ne_of_gt hpos) (hzero (K.inter_subset_convexHull hs ht ⟨intrinsicInterior_subset hp, hpt⟩))

/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree` (V4 1.24):
"with finitely many components, each a closed hypersurface". Remove the finitely
many closed facets not containing the chosen face. The remaining neighbourhood
meets only incident facets. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step4_star_neighborhood
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    {s : Finset (E d)} (hs : s ∈ K.faces) {p : E d}
    (hp : p ∈ relint (convexHull ℝ (s : Set (E d)))) :
    ∃ O : Set (E d), IsOpen O ∧ p ∈ O ∧
      K.space ∩ O ⊆ ⋃ f ∈ {f ∈ K.facets | s ⊆ f}, convexHull ℝ (f : Set (E d)) := by
  let B := {f ∈ K.facets | ¬ s ⊆ f}
  have hBfin : B.Finite := hfin.subset fun _ hf => hf.1.1
  have hclosed : IsClosed (⋃ f ∈ B, convexHull ℝ (f : Set (E d))) :=
    hBfin.isClosed_biUnion fun f _ => f.finite_toSet.isClosed_convexHull
  refine ⟨(⋃ f ∈ B, convexHull ℝ (f : Set (E d)))ᶜ, hclosed.isOpen_compl, ?_, ?_⟩
  · intro hpB
    obtain ⟨f, hf, hpf⟩ := Set.mem_iUnion₂.mp hpB
    exact hf.2 (principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step3_relint_incidence K hs hf.1.1 hp hpf)
  · rintro x ⟨hxK, hxO⟩
    obtain ⟨t, ht, hxt⟩ := K.mem_space_iff.mp hxK
    obtain ⟨f, hf, htf⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step1_facet_extension K hfin ht
    have hxf := convexHull_mono (𝕜 := ℝ) htf hxt
    have hsf : s ⊆ f := by
      by_contra hns
      exact hxO (Set.mem_iUnion₂.mpr ⟨f, ⟨hf, hns⟩, hxf⟩)
    exact Set.mem_iUnion₂.mpr ⟨f, ⟨hf, hsf⟩, hxf⟩

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree` (V4 1.24):
"each a closed hypersurface". Restrict Euclidean charts to an ambient open set. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step5_open_charts
    {n : ℕ} {Q O : Set (E d)} (hQ : IsLocallyEuclidean n Q) (hO : IsOpen O) :
    IsLocallyEuclidean n (Q ∩ O) := by
  have hsub : Q ∩ O ⊆ Q := Set.inter_subset_left
  have hopen : IsOpen ((Subtype.val : Q → E d) ⁻¹' (Q ∩ O)) := by
    have heq : (Subtype.val : Q → E d) ⁻¹' (Q ∩ O) =
        (Subtype.val : Q → E d) ⁻¹' O := by
      ext q
      simp [q.property]
    rw [heq]
    exact hO.preimage continuous_subtype_val
  have hi : Topology.IsOpenEmbedding (Set.inclusion hsub) :=
    Topology.IsOpenEmbedding.inclusion hsub hopen
  intro q
  obtain ⟨U, hU, hqU, V, hV, ⟨e⟩⟩ := hQ (Set.inclusion hsub q)
  let f := U.restrictPreimage (Set.inclusion hsub)
  have hf : Topology.IsOpenEmbedding f :=
    hi.restrict (fun _ hx => hx) (hU.preimage hi.continuous)
  let g := (Subtype.val : V → E n) ∘ e ∘ f
  have hg : Topology.IsOpenEmbedding g :=
    hV.isOpenEmbedding_subtypeVal.comp (e.isOpenEmbedding.comp hf)
  exact ⟨(Set.inclusion hsub) ⁻¹' U, hU.preimage hi.continuous, hqU,
    Set.range g, hg.isOpen_range, ⟨hg.isEmbedding.toHomeomorph⟩⟩

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step6_simplex_boundary` (V4 1.24):
"each a closed hypersurface". Local invariance of domain (Brouwer): a continuous
map injective on a closed ball of `E n` sends the centre to an interior point of
the image of the ball. Rescale the ball to the unit ball and apply the local invariance of
domain already derived (via Brouwer from Gale's Hex theorem) in the
`step7_pure_triangulation_step4_invariance_dimension` chain above. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step6_simplex_boundary_step1_local_invariance
    {n : ℕ} {x : E n} {r : ℝ} (hr : 0 < r) (g : E n → E n)
    (hg : ContinuousOn g (Metric.closedBall x r))
    (hinj : Set.InjOn g (Metric.closedBall x r)) :
    g x ∈ interior (g '' Metric.closedBall x r) := by
  have hmem (z : Metric.closedBall (0 : E n) 1) : x + r • (z : E n) ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.le]
    have hz : ‖(z : E n)‖ ≤ 1 := by
      have := z.property
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    nlinarith
  let h : Metric.closedBall (0 : E n) 1 → E n := fun z => g (x + r • (z : E n))
  have hc : Continuous h := by
    have hk : Continuous fun z : Metric.closedBall (0 : E n) 1 =>
        (⟨x + r • (z : E n), hmem z⟩ : Metric.closedBall x r) :=
      Continuous.subtype_mk (by fun_prop) _
    exact (continuousOn_iff_continuous_restrict.mp hg).comp hk
  have hi : Function.Injective h := by
    intro z z' hzz
    have h1 := hinj (hmem z) (hmem z') hzz
    have h2 : r • (z : E n) = r • (z' : E n) := add_left_cancel h1
    exact Subtype.ext (smul_right_injective _ hr.ne' h2)
  have hint := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step7_domain_invariance n
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step5_zero_stability n (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step4_ball_fixed n)) h hc hi
  have hrange : Set.range h ⊆ g '' Metric.closedBall x r := by
    rintro _ ⟨z, rfl⟩
    exact ⟨_, hmem z, rfl⟩
  have h0 : h ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = g x := by
    show g (x + r • (0 : E n)) = g x
    rw [smul_zero, add_zero]
  rw [← h0]
  exact interior_mono hrange hint

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step6_simplex_boundary` (V4 1.24):
"each a closed hypersurface". Invariance of domain: a continuous map injective
on an open subset of `E n` has an open image, by the local statement on small
closed balls. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step6_simplex_boundary_step2_invariance_domain
    {n : ℕ} {V : Set (E n)} (hV : IsOpen V) (g : E n → E n)
    (hg : ContinuousOn g V) (hinj : Set.InjOn g V) :
    IsOpen (g '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV x hx
  have hsub : Metric.closedBall x (r / 2) ⊆ V :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hint :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step6_simplex_boundary_step1_local_invariance
      (half_pos hr) g (hg.mono hsub) (hinj.mono hsub)
  exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp hint) (Set.image_mono hsub)

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step6_simplex_boundary` (V4 1.24):
"each a closed hypersurface". At a point of a proper facet the simplex lies in a
closed half-space of its affine span: the normal is the component of the
omitted vertex orthogonal to the facet. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step6_simplex_boundary_step3_supporting_normal
    (f s : Finset (E d)) (hf : AffineIndependent ℝ ((↑) : f → E d))
    {v : E d} (hvf : v ∈ f) (hvs : v ∉ s) (hfs : ∀ y ∈ f, y ∈ s ∨ y = v) (hsf : s ⊆ f)
    {p : E d} (hp : p ∈ convexHull ℝ (s : Set (E d))) :
    ∃ b ∈ vectorSpan ℝ (f : Set (E d)), b ≠ 0 ∧
      ∀ x ∈ convexHull ℝ (f : Set (E d)), 0 ≤ inner ℝ b (x - p) := by
  classical
  set D := (affineSpan ℝ (s : Set (E d))).direction with hD
  have hpaff : p ∈ affineSpan ℝ (s : Set (E d)) := convexHull_subset_affineSpan _ hp
  set b := (v - p) - D.starProjection (v - p) with hb
  have hbD : b ∈ Dᗮ := D.sub_starProjection_mem_orthogonal (v - p)
  have hvspan : v ∉ affineSpan ℝ (s : Set (E d)) := by
    have himage : (Subtype.val : f → E d) '' {i : f | i.val ∈ s} = (s : Set (E d)) := by
      ext y
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hy
        exact ⟨⟨y, hsf hy⟩, hy, rfl⟩
    have hiff := hf.mem_affineSpan_iff (⟨v, hvf⟩ : f) {i : f | i.val ∈ s}
    rw [himage] at hiff
    exact fun hv => hvs (hiff.mp hv)
  have hpf : p ∈ affineSpan ℝ (f : Set (E d)) :=
    convexHull_subset_affineSpan _ (convexHull_mono (Finset.coe_subset.mpr hsf) hp)
  have hDf : D ≤ vectorSpan ℝ (f : Set (E d)) := by
    rw [hD, direction_affineSpan]
    exact vectorSpan_mono ℝ (Finset.coe_subset.mpr hsf)
  refine ⟨b, ?_, ?_, ?_⟩
  · have h1 : v - p ∈ vectorSpan ℝ (f : Set (E d)) := by
      rw [← direction_affineSpan]
      exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ (Finset.mem_coe.mpr hvf)) hpf
    exact Submodule.sub_mem _ h1 (hDf (D.starProjection_apply_mem (v - p)))
  · intro hb0
    apply hvspan
    have hmem : v - p ∈ D := by
      have : v - p = D.starProjection (v - p) := by
        rw [hb] at hb0
        exact sub_eq_zero.mp hb0
      rw [this]
      exact D.starProjection_apply_mem (v - p)
    have := AffineSubspace.vadd_mem_of_mem_direction hmem hpaff
    simpa [vadd_eq_add] using this
  · have hconv : Convex ℝ {x : E d | inner ℝ b p ≤ inner ℝ b x} :=
      convex_halfSpace_ge (innerₛₗ ℝ b).isLinear _
    have hsubset : convexHull ℝ (f : Set (E d)) ⊆ {x : E d | inner ℝ b p ≤ inner ℝ b x} := by
      apply convexHull_min _ hconv
      intro y hy
      simp only [Set.mem_setOf_eq]
      rcases hfs y (Finset.mem_coe.mp hy) with hys | rfl
      · have hyD : y - p ∈ D :=
          AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ (Finset.mem_coe.mpr hys)) hpaff
        have h0 : inner ℝ b (y - p) = 0 := Submodule.inner_left_of_mem_orthogonal hyD hbD
        rw [inner_sub_right] at h0
        linarith
      · have hPD : D.starProjection (y - p) ∈ D := D.starProjection_apply_mem (y - p)
        have h0 : inner ℝ b (D.starProjection (y - p)) = 0 :=
          Submodule.inner_left_of_mem_orthogonal hPD hbD
        have h1 : inner ℝ b (y - p) = inner ℝ b b := by
          have : y - p = b + D.starProjection (y - p) := by rw [hb]; abel
          rw [this, inner_add_right, h0, add_zero]
        have h2 : 0 ≤ inner ℝ b b := real_inner_self_nonneg
        rw [inner_sub_right] at h1
        linarith
    intro x hx
    have := hsubset hx
    simp only [Set.mem_setOf_eq] at this
    rw [inner_sub_right]
    linarith

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree` (V4 1.24):
"each a closed hypersurface". A neighbourhood of a point on a proper facet of
one `(d-1)`-simplex has boundary and cannot be locally Euclidean of dimension
`d-1`. This is the single half-space obstruction; it involves no complex. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step6_simplex_boundary
    (f s : Finset (E d)) (hf : AffineIndependent ℝ ((↑) : f → E d))
    (hfc : f.card = d) (hsf : s ⊆ f) (hsc : s.card = d - 1)
    {p : E d} (hp : p ∈ convexHull ℝ (s : Set (E d)))
    {O : Set (E d)} (hO : IsOpen O) (hpO : p ∈ O) :
    ¬ IsLocallyEuclidean (d - 1) (convexHull ℝ (f : Set (E d)) ∩ O) := by
  classical
  intro hloc
  have hd : 2 ≤ d := Fact.out
  have hcard1 : (f \ s).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsf, hfc, hsc]
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard1
  have hvfs : v ∈ f \ s := by rw [hv]; exact Finset.mem_singleton_self v
  have hvf : v ∈ f := (Finset.mem_sdiff.mp hvfs).1
  have hvs : v ∉ s := (Finset.mem_sdiff.mp hvfs).2
  have hfs : ∀ y ∈ f, y ∈ s ∨ y = v := by
    intro y hy
    by_cases hys : y ∈ s
    · exact Or.inl hys
    · right
      have : y ∈ f \ s := Finset.mem_sdiff.mpr ⟨hy, hys⟩
      rw [hv] at this
      exact Finset.mem_singleton.mp this
  obtain ⟨b, hbspan, hb0, hbpos⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step6_simplex_boundary_step3_supporting_normal
      f s hf hvf hvs hfs hsf hp
  set Dir := vectorSpan ℝ (f : Set (E d)) with hDir
  have hfin : Module.finrank ℝ Dir = d - 1 := by
    have hrange : Set.range ((↑) : f → E d) = (f : Set (E d)) := Subtype.range_val
    have h := hf.finrank_vectorSpan (n := d - 1) (by rw [Fintype.card_coe, hfc]; omega)
    rw [hrange] at h
    exact h
  let L : Dir ≃L[ℝ] E (d - 1) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hfin, finrank_euclideanSpace_fin])
  have hpΔ : p ∈ convexHull ℝ (f : Set (E d)) := convexHull_mono (Finset.coe_subset.mpr hsf) hp
  have hpf : p ∈ affineSpan ℝ (f : Set (E d)) := convexHull_subset_affineSpan _ hpΔ
  have hmemDir (z : ↥(convexHull ℝ (f : Set (E d)) ∩ O)) : (z : E d) - p ∈ Dir := by
    rw [hDir, ← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction (convexHull_subset_affineSpan _ z.property.1) hpf
  obtain ⟨U, hU, hpU, V, hV, ⟨e⟩⟩ := hloc ⟨p, hpΔ, hpO⟩
  let φ : V → E (d - 1) := fun y => L ⟨((e.symm y : U) : E d) - p, hmemDir _⟩
  have hφc : Continuous φ := by
    apply L.continuous.comp
    apply Continuous.subtype_mk
    fun_prop
  let g : E (d - 1) → E (d - 1) := fun y => if h : y ∈ V then φ ⟨y, h⟩ else 0
  have hgV : V.restrict g = φ := by
    funext y
    simp [g, Set.restrict, y.property]
  have hgc : ContinuousOn g V := by
    rw [continuousOn_iff_continuous_restrict, hgV]
    exact hφc
  have hginj : Set.InjOn g V := by
    intro y₁ h₁ y₂ h₂ heq
    have heq' : φ ⟨y₁, h₁⟩ = φ ⟨y₂, h₂⟩ := by simpa [g, h₁, h₂] using heq
    have h3 := L.injective heq'
    have h4 : ((e.symm ⟨y₁, h₁⟩ : U) : E d) = ((e.symm ⟨y₂, h₂⟩ : U) : E d) := by
      have := congrArg Subtype.val h3
      simpa using this
    have h5 : e.symm ⟨y₁, h₁⟩ = e.symm ⟨y₂, h₂⟩ := Subtype.ext (Subtype.ext h4)
    have h6 := congrArg Subtype.val (e.symm.injective h5)
    simpa using h6
  have hopen :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step6_simplex_boundary_step2_invariance_domain
      hV g hgc hginj
  -- the base point
  let y₀ : V := e ⟨⟨p, hpΔ, hpO⟩, hpU⟩
  have hgy₀ : g y₀ = 0 := by
    have : φ y₀ = 0 := by
      simp only [φ, y₀, Homeomorph.symm_apply_apply, sub_self]
      exact map_eq_zero_iff L L.injective |>.mpr rfl
    simpa [g, y₀.property] using this
  have h0mem : (0 : E (d - 1)) ∈ g '' V := ⟨y₀, y₀.property, hgy₀⟩
  -- a path of directions leaving the half-space
  let ψ : ℝ → E (d - 1) := fun t => L ⟨-(t • b), Submodule.neg_mem _ (Submodule.smul_mem _ t hbspan)⟩
  have hψc : Continuous ψ := by
    apply L.continuous.comp
    apply Continuous.subtype_mk
    fun_prop
  have hψ0 : ψ 0 = 0 := by
    simp only [ψ, zero_smul, neg_zero]
    exact map_eq_zero_iff L L.injective |>.mpr rfl
  have hpre : IsOpen (ψ ⁻¹' (g '' V)) := hopen.preimage hψc
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hpre 0 (by simpa [hψ0] using h0mem)
  have htmem : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith
  obtain ⟨y, hyV, hy⟩ := hδsub htmem
  have hy' : φ ⟨y, hyV⟩ = ψ (δ / 2) := by simpa [g, hyV] using hy
  have h3 := L.injective hy'
  have h4 : ((e.symm ⟨y, hyV⟩ : U) : E d) - p = -((δ / 2) • b) := by
    have := congrArg Subtype.val h3
    simpa using this
  have hxΔ : ((e.symm ⟨y, hyV⟩ : U) : E d) ∈ convexHull ℝ (f : Set (E d)) :=
    ((e.symm ⟨y, hyV⟩ : U) : ↥(convexHull ℝ (f : Set (E d)) ∩ O)).property.1
  have hnn := hbpos _ hxΔ
  rw [h4, inner_neg_right, inner_smul_right] at hnn
  have hbb : 0 < inner ℝ b b := real_inner_self_pos.mpr hb0
  have : 0 < δ / 2 * inner ℝ b b := mul_pos (half_pos hδ) hbb
  linarith

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood` (V4 1.24):
"each relative interior point of that face". A relative-interior point has a ball whose
trace on the affine span lies in the set. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood_step1_relint_ball {S : Set (E d)} {p : E d}
    (hp : p ∈ relint S) :
    ∃ r : ℝ, 0 < r ∧ (affineSpan ℝ S : Set (E d)) ∩ Metric.ball p r ⊆ S := by
  rw [relint, mem_intrinsicInterior] at hp
  obtain ⟨y, hy, rfl⟩ := hp
  rw [mem_interior_iff_mem_nhds, mem_nhds_subtype] at hy
  obtain ⟨u, hu, hsub⟩ := hy
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hu
  refine ⟨r, hr, ?_⟩
  rintro x ⟨hxA, hxB⟩
  exact hsub (show (⟨x, hxA⟩ : affineSpan ℝ S) ∈ Subtype.val ⁻¹' u from hball hxB)

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood` (V4 1.24):
"unfold two simplices sharing a codimension-one face to a Euclidean patch". On one
side of the ridge the unfolding `(h, t) ↦ (1 - t) • h + t • (c - p)` is injective,
since the apex direction `c - p` is transverse to the ridge direction. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood_step2_same_side {H : Submodule ℝ (E d)} {c p : E d} (hc : c - p ∉ H)
    {h h' : E d} (hh : h ∈ H) (hh' : h' ∈ H) {t t' : ℝ} (ht : t < 1)
    (heq : (1 - t) • h + t • (c - p) = (1 - t') • h' + t' • (c - p)) :
    t = t' ∧ h = h' := by
  have hmem : (t - t') • (c - p) ∈ H := by
    have : (t - t') • (c - p) = (1 - t') • h' - (1 - t) • h := by
      rw [← sub_eq_zero] at heq ⊢
      rw [← heq]; module
    rw [this]
    exact H.sub_mem (H.smul_mem _ hh') (H.smul_mem _ hh)
  have htt : t = t' := by
    by_contra hne
    apply hc
    have h0 : t - t' ≠ 0 := sub_ne_zero.mpr hne
    have := H.smul_mem (t - t')⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this
  subst htt
  refine ⟨rfl, ?_⟩
  have h1 : (1 - t) • h = (1 - t) • h' := add_right_cancel heq
  exact smul_right_injective _ (by linarith : (1 - t) ≠ 0) h1

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood` (V4 1.24):
"unfold two simplices sharing a codimension-one face to a Euclidean patch". A point of
one half of the patch lying in the ridge direction has height `0` over the ridge. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood_step3_on_ridge {H : Submodule ℝ (E d)} {c p : E d} (hc : c - p ∉ H)
    {h : E d} (hh : h ∈ H) {t : ℝ}
    (hmem : (1 - t) • h + t • (c - p) ∈ H) : t = 0 := by
  by_contra hne
  apply hc
  have h2 : t • (c - p) ∈ H := by
    have := H.sub_mem hmem (H.smul_mem (1 - t) hh)
    simpa using this
  have := H.smul_mem t⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this


/-- Step 7 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree` (V4 1.24):
"each a closed hypersurface". Unfold two simplices sharing a codimension-one
face to a Euclidean patch. Invariance of domain in a chart of the containing
manifold makes this patch a neighbourhood at each relative interior point of
that face. This is a statement about two simplices, with no finite complex. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood
    (f g : Finset (E d))
    (hf : AffineIndependent ℝ ((↑) : f → E d))
    (hg : AffineIndependent ℝ ((↑) : g → E d))
    (hfc : f.card = d) (hgc : g.card = d) (hfgc : (f ∩ g).card = d - 1)
    (hinter : convexHull ℝ (f : Set (E d)) ∩ convexHull ℝ (g : Set (E d)) =
      convexHull ℝ ((f ∩ g : Finset (E d)) : Set (E d)))
    {Q : Set (E d)} (hQ : IsLocallyEuclidean (d - 1) Q)
    (hfQ : convexHull ℝ (f : Set (E d)) ⊆ Q)
    (hgQ : convexHull ℝ (g : Set (E d)) ⊆ Q)
    {p : E d} (hp : p ∈ relint (convexHull ℝ ((f ∩ g : Finset (E d)) : Set (E d)))) :
    ∃ O : Set (E d), IsOpen O ∧ p ∈ O ∧
      Q ∩ O ⊆ convexHull ℝ (f : Set (E d)) ∪ convexHull ℝ (g : Set (E d)) := by
  classical
  have hd : 2 ≤ d := Fact.out
  set s : Finset (E d) := f ∩ g with hs_def
  set A : AffineSubspace ℝ (E d) := affineSpan ℝ (s : Set (E d)) with hA_def
  set H : Submodule ℝ (E d) := A.direction with hH_def
  -- the two apexes
  have hapex : ∀ (u v : Finset (E d)), AffineIndependent ℝ ((↑) : u → E d) →
      u.card = d → (u ∩ v).card = d - 1 →
      ∃ a ∈ u, a ∉ v ∧ a ∉ affineSpan ℝ (((u ∩ v : Finset (E d)) : Set (E d))) := by
    intro u v hu huc huvc
    have hex : ∃ a ∈ u, a ∉ v := by
      by_contra hcon
      push_neg at hcon
      have : u ∩ v = u := Finset.inter_eq_left.mpr hcon
      rw [this] at huvc
      omega
    obtain ⟨a, hau, hav⟩ := hex
    refine ⟨a, hau, hav, ?_⟩
    have hni := hu.notMem_affineSpan_diff ⟨a, hau⟩ {x : u | (x : E d) ∈ v}
    intro hmem
    apply hni
    refine affineSpan_mono ℝ ?_ hmem
    intro y hy
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe] at hy
    refine ⟨⟨y, hy.1⟩, ⟨hy.2, ?_⟩, rfl⟩
    intro hya
    simp only [Set.mem_singleton_iff, Subtype.mk.injEq] at hya
    exact hav (hya ▸ hy.2)
  obtain ⟨a, haf, hag, haA⟩ := hapex f g hf hfc hfgc
  obtain ⟨b, hbg, hbf, hbA⟩ := hapex g f hg hgc (by rw [Finset.inter_comm]; exact hfgc)
  rw [Finset.inter_comm g f] at hbA
  -- the base point
  have hpS : p ∈ convexHull ℝ (s : Set (E d)) := intrinsicInterior_subset hp
  have hpA : p ∈ A := convexHull_subset_affineSpan _ hpS
  have hsf : convexHull ℝ (s : Set (E d)) ⊆ convexHull ℝ (f : Set (E d)) :=
    convexHull_mono (by simp [s])
  have hsg : convexHull ℝ (s : Set (E d)) ⊆ convexHull ℝ (g : Set (E d)) :=
    convexHull_mono (by simp [s])
  have hpQ : p ∈ Q := hfQ (hsf hpS)
  have haH : a - p ∉ H := by
    intro h
    apply haA
    have h' : (a - p) +ᵥ p ∈ A := AffineSubspace.vadd_mem_of_mem_direction h hpA
    rw [vadd_eq_add, sub_add_cancel] at h'
    exact h'
  have hbH : b - p ∉ H := by
    intro h
    apply hbA
    have h' : (b - p) +ᵥ p ∈ A := AffineSubspace.vadd_mem_of_mem_direction h hpA
    rw [vadd_eq_add, sub_add_cancel] at h'
    exact h'
  obtain ⟨ε, hε, hball⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood_step1_relint_ball hp
  rw [affineSpan_convexHull] at hball
  -- dimension count
  have hsind : AffineIndependent ℝ ((↑) : s → E d) :=
    hf.mono (s := (s : Set (E d))) (t := (f : Set (E d))) (by simp [s])
  have hHrank : Module.finrank ℝ H = d - 2 := by
    have h1 := hsind.finrank_vectorSpan (n := d - 2) (by simp only [Fintype.card_coe]; omega)
    have h2 : Set.range ((↑) : s → E d) = (s : Set (E d)) := by ext; simp
    rw [h2] at h1
    rw [hH_def, hA_def, direction_affineSpan]
    exact h1
  have hXrank : Module.finrank ℝ (E (d - 1)) = Module.finrank ℝ (H × ℝ) := by
    rw [Module.finrank_prod, Module.finrank_self, hHrank, finrank_euclideanSpace_fin]
    omega
  let L : E (d - 1) ≃L[ℝ] (H × ℝ) :=
    (LinearEquiv.ofFinrankEq (E (d - 1)) (H × ℝ) hXrank).toContinuousLinearEquiv
  -- the unfolding map
  let F : H × ℝ → E d := fun x =>
    p + (x.1 : E d) + max x.2 0 • (a - (p + x.1)) + max (-x.2) 0 • (b - (p + x.1))
  have hFc : Continuous F := by
    have h1 : Continuous fun x : H × ℝ => (x.1 : E d) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.add h1).add
      ((continuous_snd.max continuous_const).smul (continuous_const.sub
        (continuous_const.add h1)))).add
      ((continuous_snd.neg.max continuous_const).smul (continuous_const.sub
        (continuous_const.add h1)))
  have hF0 : F 0 = p := by simp [F]
  have hFpos : ∀ x : H × ℝ, 0 ≤ x.2 →
      F x = p + ((1 - x.2) • (x.1 : E d) + x.2 • (a - p)) := by
    intro x hx
    simp only [F, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), zero_smul, add_zero]
    module
  have hFneg : ∀ x : H × ℝ, x.2 ≤ 0 →
      F x = p + ((1 - -x.2) • (x.1 : E d) + (-x.2) • (b - p)) := by
    intro x hx
    simp only [F, max_eq_right hx, max_eq_left (neg_nonneg.mpr hx), zero_smul, add_zero]
    module
  have hbase : ∀ x : H × ℝ, ‖(x.1 : E d)‖ < ε →
      p + (x.1 : E d) ∈ convexHull ℝ (s : Set (E d)) := by
    intro x hx
    apply hball
    refine ⟨?_, ?_⟩
    · have := AffineSubspace.vadd_mem_of_mem_direction x.1.2 hpA
      simpa [add_comm] using this
    · rw [Metric.mem_ball, dist_eq_norm]
      simpa using hx
  have hFf : ∀ x : H × ℝ, ‖(x.1 : E d)‖ < ε → 0 ≤ x.2 → x.2 ≤ 1 →
      F x ∈ convexHull ℝ (f : Set (E d)) := by
    intro x hx h0 h1
    have : F x = (p + x.1) + x.2 • (a - (p + x.1)) := by
      simp only [F, max_eq_left h0, max_eq_right (neg_nonpos.mpr h0), zero_smul, add_zero]
    rw [this]
    exact (convex_convexHull ℝ _).add_smul_sub_mem (hsf (hbase x hx))
      (subset_convexHull ℝ _ (by simpa using haf)) ⟨h0, h1⟩
  have hFg : ∀ x : H × ℝ, ‖(x.1 : E d)‖ < ε → x.2 ≤ 0 → -1 ≤ x.2 →
      F x ∈ convexHull ℝ (g : Set (E d)) := by
    intro x hx h0 h1
    have : F x = (p + x.1) + (-x.2) • (b - (p + x.1)) := by
      simp only [F, max_eq_right h0, max_eq_left (neg_nonneg.mpr h0), zero_smul, add_zero]
    rw [this]
    exact (convex_convexHull ℝ _).add_smul_sub_mem (hsg (hbase x hx))
      (subset_convexHull ℝ _ (by simpa using hbg)) ⟨by linarith, by linarith⟩
  -- the region where the unfolding is an injective patch
  let R : Set (H × ℝ) := {x | ‖(x.1 : E d)‖ < ε ∧ |x.2| < 1}
  have hFR : ∀ x ∈ R, F x ∈ convexHull ℝ (f : Set (E d)) ∪ convexHull ℝ (g : Set (E d)) := by
    rintro x ⟨hx1, hx2⟩
    rw [abs_lt] at hx2
    rcases le_total 0 x.2 with h | h
    · exact Or.inl (hFf x hx1 h hx2.2.le)
    · exact Or.inr (hFg x hx1 h hx2.1.le)
  have hridge : ∀ x ∈ R, F x ∈ convexHull ℝ (f : Set (E d)) →
      F x ∈ convexHull ℝ (g : Set (E d)) → x.2 = 0 := by
    rintro x ⟨hx1, hx2⟩ hxf hxg
    have hxs : F x ∈ A := by
      have : F x ∈ convexHull ℝ (s : Set (E d)) := by rw [← hinter]; exact ⟨hxf, hxg⟩
      exact convexHull_subset_affineSpan _ this
    have hdir : F x - p ∈ H := by
      have := AffineSubspace.vsub_mem_direction hxs hpA
      simpa using this
    rcases le_total 0 x.2 with h | h
    · rw [hFpos x h, add_sub_cancel_left] at hdir
      exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood_step3_on_ridge haH x.1.2 hdir
    · rw [hFneg x h, add_sub_cancel_left] at hdir
      have := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood_step3_on_ridge hbH x.1.2 hdir
      linarith
  have hFinj : ∀ x ∈ R, ∀ y ∈ R, F x = F y → x = y := by
    intro x hx y hy hxy
    have hx' := hx; have hy' := hy
    obtain ⟨hx1, hx2⟩ := hx'
    obtain ⟨hy1, hy2⟩ := hy'
    rw [abs_lt] at hx2 hy2
    have key : x.2 = y.2 ∧ (x.1 : E d) = y.1 := by
      rcases le_total 0 x.2 with h | h <;> rcases le_total 0 y.2 with h' | h'
      · rw [hFpos x h, hFpos y h'] at hxy
        exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood_step2_same_side haH x.1.2 y.1.2 hx2.2 (add_left_cancel hxy)
      · have hxf := hFf x hx1 h hx2.2.le
        have hyg := hFg y hy1 h' hy2.1.le
        have e1 : x.2 = 0 := hridge x hx hxf (hxy ▸ hyg)
        have e2 : y.2 = 0 := hridge y hy (hxy ▸ hxf) hyg
        rw [hFpos x h, hFpos y (le_of_eq e2.symm)] at hxy
        exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood_step2_same_side haH x.1.2 y.1.2 hx2.2 (add_left_cancel hxy)
      · have hxg := hFg x hx1 h hx2.1.le
        have hyf := hFf y hy1 h' hy2.2.le
        have e1 : x.2 = 0 := hridge x hx (hxy ▸ hyf) hxg
        rw [hFpos x (le_of_eq e1.symm), hFpos y h'] at hxy
        exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood_step2_same_side haH x.1.2 y.1.2 hx2.2 (add_left_cancel hxy)
      · rw [hFneg x h, hFneg y h'] at hxy
        obtain ⟨k1, k2⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood_step2_same_side hbH x.1.2 y.1.2 (by linarith) (add_left_cancel hxy)
        exact ⟨by linarith, k2⟩
    exact Prod.ext (Subtype.ext key.2) key.1
  -- the chart at `p`
  obtain ⟨U, hU, hpU, V, hV, ⟨φ⟩⟩ := hQ ⟨p, hpQ⟩
  obtain ⟨U', hU'o, hU'eq⟩ := isOpen_induced_iff.mp hU
  have hpU' : p ∈ U' := by
    have : (⟨p, hpQ⟩ : Q) ∈ Subtype.val ⁻¹' U' := by rw [hU'eq]; exact hpU
    exact this
  let N : Set (H × ℝ) := R ∩ F ⁻¹' U'
  have hNo : IsOpen N := by
    refine IsOpen.inter ?_ (hU'o.preimage hFc)
    exact (isOpen_lt ((continuous_norm.comp (continuous_subtype_val.comp continuous_fst)))
      continuous_const).inter (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)
  have h0N : (0 : H × ℝ) ∈ N := ⟨⟨by simpa using hε, by simp⟩, by rw [Set.mem_preimage, hF0]; exact hpU'⟩
  obtain ⟨ρ, hρ, hρball⟩ := Metric.isOpen_iff.mp (hNo.preimage L.continuous) 0
    (by simpa using h0N)
  have hmemN : ∀ z : Metric.closedBall (0 : E (d - 1)) 1, L ((ρ / 2) • (z : E (d - 1))) ∈ N := by
    intro z
    apply hρball
    have hz : ‖(z : E (d - 1))‖ ≤ 1 := by
      have := z.property
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
    nlinarith
  let g0 : Metric.closedBall (0 : E (d - 1)) 1 → E d := fun z => F (L ((ρ / 2) • (z : E (d - 1))))
  have hg0c : Continuous g0 :=
    hFc.comp (L.continuous.comp (continuous_const.smul continuous_subtype_val))
  have hg0P : ∀ z, g0 z ∈ convexHull ℝ (f : Set (E d)) ∪ convexHull ℝ (g : Set (E d)) :=
    fun z => hFR _ (hmemN z).1
  have hg0Q : ∀ z, g0 z ∈ Q := fun z => (hg0P z).elim (fun h => hfQ h) (fun h => hgQ h)
  have hg0U : ∀ z, (⟨g0 z, hg0Q z⟩ : Q) ∈ U := by
    intro z
    rw [← hU'eq]
    exact (hmemN z).2
  have hg0inj : Function.Injective g0 := by
    intro z z' hzz
    have h1 := hFinj _ (hmemN z).1 _ (hmemN z').1 hzz
    have h2 := L.injective h1
    exact Subtype.ext (smul_right_injective _ (by positivity : ρ / 2 ≠ 0) h2)
  let gU : Metric.closedBall (0 : E (d - 1)) 1 → U := fun z => ⟨⟨g0 z, hg0Q z⟩, hg0U z⟩
  have hgUc : Continuous gU := (hg0c.subtype_mk _).subtype_mk _
  let ψ : Metric.closedBall (0 : E (d - 1)) 1 → E (d - 1) := fun z => (φ (gU z) : E (d - 1))
  have hψc : Continuous ψ := continuous_subtype_val.comp (φ.continuous.comp hgUc)
  have hψinj : Function.Injective ψ := by
    intro z z' hzz
    have h1 : gU z = gU z' := φ.injective (Subtype.ext hzz)
    apply hg0inj
    have := congrArg (fun u : U => ((u : Q) : E d)) h1
    exact this
  have hDIψ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step7_domain_invariance (d - 1)
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step5_zero_stability (d - 1)
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation_step4_invariance_dimension_step4_ball_fixed (d - 1))) ψ hψc hψinj
  have hgU0 : gU ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = ⟨⟨p, hpQ⟩, hpU⟩ := by
    apply Subtype.ext; apply Subtype.ext
    show F (L ((ρ / 2) • (0 : E (d - 1)))) = p
    rw [smul_zero, map_zero, hF0]
  -- the neighbourhood
  let S : Set U := {u | (φ u : E (d - 1)) ∈ interior (range ψ)}
  have hSo : IsOpen S :=
    isOpen_interior.preimage (continuous_subtype_val.comp φ.continuous)
  have hTo : IsOpen (Subtype.val '' S : Set Q) := hU.isOpenMap_subtype_val S hSo
  obtain ⟨O, hOo, hOeq⟩ := isOpen_induced_iff.mp hTo
  refine ⟨O, hOo, ?_, ?_⟩
  · have : (⟨p, hpQ⟩ : Q) ∈ Subtype.val ⁻¹' O := by
      rw [hOeq]
      refine ⟨⟨⟨p, hpQ⟩, hpU⟩, ?_, rfl⟩
      show (φ ⟨⟨p, hpQ⟩, hpU⟩ : E (d - 1)) ∈ interior (range ψ)
      rw [← hgU0]
      exact hDIψ
    exact this
  · rintro y ⟨hyQ, hyO⟩
    have : (⟨y, hyQ⟩ : Q) ∈ Subtype.val ⁻¹' O := hyO
    rw [hOeq] at this
    obtain ⟨u, huS, hu⟩ := this
    obtain ⟨z, hz⟩ := interior_subset huS
    have h1 : gU z = u := φ.injective (Subtype.ext hz)
    have h2 : g0 z = y := by
      have h3 : g0 z = ((u : Q) : E d) := congrArg (fun v : U => ((v : Q) : E d)) h1
      have hy : ((u : Q) : E d) = y := by rw [hu]
      exact h3.trans hy
    rw [← h2]
    exact hg0P z

/-- Step 8 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree` (V4 1.24):
"a connected union of facets". Two distinct pure facets containing a ridge
intersect in precisely that ridge, by counting vertices. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step8_coface_intersection
    {s f g : Finset (E d)} (hsf : s ⊆ f) (hsg : s ⊆ g)
    (hsc : s.card = d - 1) (hfc : f.card = d) (hgc : g.card = d) (hne : f ≠ g) :
    f ∩ g = s := by
  classical
  have hsub : s ⊆ f ∩ g := Finset.subset_inter hsf hsg
  have hlt : (f ∩ g).card < d := by
    have hle : (f ∩ g).card ≤ d := by
      calc
        (f ∩ g).card ≤ f.card := Finset.card_le_card Finset.inter_subset_left
        _ = d := hfc
    apply lt_of_le_of_ne hle
    intro heq
    have hef : f ∩ g = f := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have heg : f ∩ g = g := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (hef.symm.trans heg)
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

open scoped Topology in
/-- Step 9 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree` (V4 1.24):
"a connected union of facets". At every point of a proper simplex face, points
of the larger simplex outside that face occur arbitrarily close. A segment to
an omitted vertex leaves the affine span of the face immediately. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step9_escape_face
    (f s : Finset (E d)) (hf : AffineIndependent ℝ ((↑) : f → E d))
    (hsf : s ⊆ f) (hne : s ≠ f) {p : E d}
    (hp : p ∈ convexHull ℝ (s : Set (E d)))
    {O : Set (E d)} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ x ∈ convexHull ℝ (f : Set (E d)) ∩ O,
      x ∉ convexHull ℝ (s : Set (E d)) := by
  classical
  obtain ⟨v, hvf, hvs⟩ : ∃ v ∈ f, v ∉ s := by
    by_contra hn
    push_neg at hn
    exact hne (Finset.Subset.antisymm hsf hn)
  have hvspan : v ∉ affineSpan ℝ (s : Set (E d)) := by
    have himage : (Subtype.val : f → E d) '' {i : f | i.val ∈ s} = (s : Set (E d)) := by
      ext y
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hy
        exact ⟨⟨y, hsf hy⟩, hy, rfl⟩
    have hiff := hf.mem_affineSpan_iff (⟨v, hvf⟩ : f) {i : f | i.val ∈ s}
    rw [himage] at hiff
    exact fun hv => hvs (hiff.mp hv)
  have hpaff : p ∈ affineSpan ℝ (s : Set (E d)) := convexHull_subset_affineSpan (s : Set (E d)) hp
  have hcont : Continuous (fun t : ℝ => AffineMap.lineMap p v t) := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), AffineMap.lineMap p v t ∈ O := by
    apply (hcont.tendsto 0).eventually
    simpa only [AffineMap.lineMap_apply_zero] using hO.mem_nhds hpO
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  let t := min δ 1 / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := by dsimp [t]; linarith [min_le_left δ 1]
  have ht1 : t < 1 := by dsimp [t]; linarith [min_le_right δ 1]
  have hxt : AffineMap.lineMap p v t ∈ convexHull ℝ (f : Set (E d)) := by
    apply (convex_convexHull ℝ (f : Set (E d))).segment_subset
      (convexHull_mono hsf hp) (subset_convexHull ℝ _ hvf)
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.le, ht1.le⟩, rfl⟩
  refine ⟨AffineMap.lineMap p v t, ⟨hxt, hnear ?_⟩, ?_⟩
  · simpa [Real.dist_eq, abs_of_pos ht] using htδ
  · intro hxs
    have hxaff : AffineMap.lineMap p v t ∈ affineSpan ℝ (s : Set (E d)) :=
      convexHull_subset_affineSpan (s : Set (E d)) hxs
    have hv := AffineMap.lineMap_mem t⁻¹ hpaff hxaff
    rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ (ne_of_gt ht),
      AffineMap.lineMap_apply_one] at hv
    exact hvspan hv

/-- Step 10 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree` (V4 1.24):
"each a closed hypersurface". There must be two distinct incident facets:
otherwise the finite-star neighbourhood would be a simplex with boundary. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step10_two_facets
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d)
    (hman : IsLocallyEuclidean (d - 1) K.space)
    {s : Finset (E d)} (hs : s ∈ K.faces) (hsc : s.card = d - 1)
    {p : E d} (hp : p ∈ relint (convexHull ℝ (s : Set (E d)))) :
    ∃ f ∈ K.facets, ∃ g ∈ K.facets, s ⊆ f ∧ s ⊆ g ∧ f ≠ g := by
  classical
  obtain ⟨f, hf, hsf⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step1_facet_extension K hfin hs
  by_contra hn
  have honly : ∀ g ∈ K.facets, s ⊆ g → g = f := by
    intro g hg hsg
    by_contra hne
    exact hn ⟨f, hf, g, hg, hsf, hsg, Ne.symm hne⟩
  obtain ⟨O, hO, hpO, hstar⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step4_star_neighborhood K hfin hs hp
  have heq : K.space ∩ O = convexHull ℝ (f : Set (E d)) ∩ O := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxK, hxO⟩
      obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.mp (hstar ⟨hxK, hxO⟩)
      exact ⟨honly g hg.1 hg.2 ▸ hxg, hxO⟩
    · exact Set.inter_subset_inter_left O (K.convexHull_subset_space hf.1)
  have hm := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step5_open_charts hman hO
  rw [heq] at hm
  exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step6_simplex_boundary f s (K.indep hf.1) (hpure f hf) hsf hsc
    (intrinsicInterior_subset hp) hO hpO hm

/-- Step 11 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree` (V4 1.24):
"each a closed hypersurface". The patch made by two incident facets excludes a
third: that facet would approach the ridge through points outside the patch. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step11_exhaust_facets
    (K : Geometry.SimplicialComplex ℝ (E d))
    (hpure : ∀ f ∈ K.facets, f.card = d)
    (hman : IsLocallyEuclidean (d - 1) K.space)
    {s f g : Finset (E d)} (hsc : s.card = d - 1)
    (hf : f ∈ K.facets) (hg : g ∈ K.facets)
    (hsf : s ⊆ f) (hsg : s ⊆ g) (hfg : f ≠ g)
    {p : E d} (hp : p ∈ relint (convexHull ℝ (s : Set (E d)))) :
    ∀ h ∈ K.facets, s ⊆ h → h = f ∨ h = g := by
  classical
  have hfgs := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step8_coface_intersection hsf hsg hsc (hpure f hf) (hpure g hg) hfg
  have hpc : p ∈ relint (convexHull ℝ ((f ∩ g : Finset (E d)) : Set (E d))) := by simpa only [hfgs] using hp
  obtain ⟨O, hO, hpO, hpair⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step7_pair_neighborhood f g (K.indep hf.1) (K.indep hg.1)
    (hpure f hf) (hpure g hg) (by simpa only [hfgs] using hsc)
    (by simpa only [Finset.coe_inter] using K.convexHull_inter_convexHull hf.1 hg.1)
    hman (K.convexHull_subset_space hf.1) (K.convexHull_subset_space hg.1) hpc
  intro h hh hsh
  by_contra hn
  push_neg at hn
  have hhfs := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step8_coface_intersection hsh hsf hsc (hpure h hh) (hpure f hf) hn.1
  have hhgs := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step8_coface_intersection hsh hsg hsc (hpure h hh) (hpure g hg) hn.2
  have hne : s ≠ h := by
    intro heq
    have hd : 2 ≤ d := Fact.out
    have hc := hpure h hh
    rw [← heq] at hc
    omega
  obtain ⟨x, hx, hxs⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step9_escape_face h s (K.indep hh.1) hsh hne
    (intrinsicInterior_subset hp) hO hpO
  rcases hpair ⟨K.convexHull_subset_space hh.1 hx.1, hx.2⟩ with hxf | hxg
  · apply hxs
    have hxi := K.inter_subset_convexHull hh.1 hf.1 ⟨hx.1, hxf⟩
    simpa only [← Finset.coe_inter, hhfs] using hxi
  · apply hxs
    have hxi := K.inter_subset_convexHull hh.1 hg.1 ⟨hx.1, hxg⟩
    simpa only [← Finset.coe_inter, hhgs] using hxi

/-- Step 10 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"each a closed hypersurface". At the relative interior of a ridge of a finite
triangulated manifold without boundary, exactly two top dimensional simplices
meet. This is the local zero dimensional link calculation. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d)
    (hman : IsLocallyEuclidean (d - 1) K.space) :
    ∀ s ∈ K.faces, s.card = d - 1 →
      {f ∈ K.facets | s ⊆ f}.ncard = 2 := by
  classical
  intro s hs hsc
  obtain ⟨p, hp⟩ := (intrinsicInterior_nonempty (convex_convexHull ℝ (s : Set (E d)))).mpr
    (convexHull_nonempty_iff.mpr (K.nonempty_of_mem_faces hs))
  obtain ⟨f, hf, g, hg, hsf, hsg, hfg⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step10_two_facets K hfin hpure hman hs hsc hp
  have hexhaust := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step11_exhaust_facets K hpure hman hsc hf hg hsf hsg hfg hp
  have heq : {h ∈ K.facets | s ⊆ h} = {f, g} := by
    ext h
    constructor
    · intro hh
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hexhaust h hh.1 hh.2
    · intro hh
      rcases Set.mem_insert_iff.mp hh with rfl | hh
      · exact ⟨hf, hsf⟩
      · have : h = g := Set.mem_singleton_iff.mp hh
        subst h
        exact ⟨hg, hsg⟩
  rw [heq, Set.ncard_pair hfg]

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains` (V4 1.24):
"a connected union of facets". In a finite closed cover of a preconnected
set, every member meeting the set is reached from every other member through
meeting members: the unions of reachable and unreachable members would
otherwise separate the set. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains_step1_closed_cover
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (C : ι → Set X) (hclosed : ∀ i, IsClosed (C i))
    {U : Set X} (hconn : IsPreconnected U) (hcover : U ⊆ ⋃ i, C i)
    (hne : ∀ i, (U ∩ C i).Nonempty) (R : ι → ι → Prop)
    (hmeet : ∀ i j, (U ∩ (C i ∩ C j)).Nonempty → i = j ∨ R i j) :
    ∀ i j, Relation.ReflTransGen R i j := by
  classical
  intro a b
  by_contra hn
  let A := {i : ι // Relation.ReflTransGen R a i}
  let B := {i : ι // ¬ Relation.ReflTransGen R a i}
  let F : Set X := ⋃ i : A, C i.val
  let G : Set X := ⋃ i : B, C i.val
  have hF : IsClosed F := isClosed_iUnion_of_finite fun i : A => hclosed i.val
  have hG : IsClosed G := isClosed_iUnion_of_finite fun i : B => hclosed i.val
  have hcov : U ⊆ F ∪ G := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
    by_cases hai : Relation.ReflTransGen R a i
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨i, hai⟩, hi⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i, hai⟩, hi⟩)
  have hUF : (U ∩ F).Nonempty := by
    obtain ⟨x, hxU, hxa⟩ := hne a
    exact ⟨x, hxU, Set.mem_iUnion.mpr ⟨⟨a, Relation.ReflTransGen.refl⟩, hxa⟩⟩
  have hUG : (U ∩ G).Nonempty := by
    obtain ⟨x, hxU, hxb⟩ := hne b
    exact ⟨x, hxU, Set.mem_iUnion.mpr ⟨⟨b, hn⟩, hxb⟩⟩
  obtain ⟨x, hxU, hxF, hxG⟩ :=
    isPreconnected_closed_iff.mp hconn F G hF hG hcov hUF hUG
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxF
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxG
  apply j.property
  rcases hmeet i.val j.val ⟨x, hxU, hxi, hxj⟩ with heq | hR
  · exact heq ▸ i.property
  · exact i.property.tail hR

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains` (V4 1.24):
"a connected union of facets". The closed facets of a finite complex cover its
connected space, so any two facets are joined by a chain of facets in which
consecutive members share at least one vertex. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains_step2_meet_chains
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hconn : IsConnected K.space) :
    ∀ f g : K.facets, Relation.ReflTransGen
      (fun u v : K.facets => (u.val ∩ v.val).Nonempty) f g := by
  classical
  letI : Finite K.facets := (hfin.subset K.facets_subset).to_subtype
  have hcover :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step9_facets_cover K hfin
  refine principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains_step1_closed_cover
    (fun f : K.facets => convexHull ℝ (f.val : Set (E d)))
    (fun f => f.val.finite_toSet.isCompact_convexHull.isClosed) hconn.isPreconnected
    hcover.subset ?_ _ ?_
  · intro f
    obtain ⟨x, hx⟩ : (convexHull ℝ (f.val : Set (E d))).Nonempty :=
      convexHull_nonempty_iff.mpr
        (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces f.property.1))
    exact ⟨x, K.convexHull_subset_space f.property.1 hx, hx⟩
  · rintro f g ⟨x, -, hxf, hxg⟩
    right
    have hxi : x ∈ convexHull ℝ ((f.val : Set (E d)) ∩ (g.val : Set (E d))) :=
      K.inter_subset_convexHull f.property.1 g.property.1 ⟨hxf, hxg⟩
    have hh : (convexHull ℝ ((f.val ∩ g.val : Finset (E d)) : Set (E d))).Nonempty :=
      ⟨x, by simpa using hxi⟩
    exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp hh)

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains` (V4 1.24):
"`∂t` is a compact `(d-1)`-manifold". A chart of dimension at least two gives
arbitrarily small relative neighbourhoods of a point whose punctured versions are
preconnected: they are chart images of punctured round balls. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains_step3_punctured_charts
    {n : ℕ} (hn : 2 ≤ n) {X : Set (E d)} (hX : IsLocallyEuclidean n X)
    {v : E d} (hv : v ∈ X) {r : ℝ} (hr : 0 < r) :
    ∃ W : Set (E d), W ⊆ X ∩ Metric.ball v r ∧ (∃ ε > 0, X ∩ Metric.ball v ε ⊆ W) ∧
      IsPreconnected (W \ {v}) := by
  classical
  obtain ⟨U, hUo, hvU, V, hVo, ⟨φ⟩⟩ := hX ⟨v, hv⟩
  let u₀ : U := ⟨⟨v, hv⟩, hvU⟩
  let c : E n := (φ u₀ : E n)
  let ψ : V → E d := fun y => ((φ.symm y : U) : X).val
  have hψ : Continuous ψ :=
    continuous_subtype_val.comp (continuous_subtype_val.comp φ.symm.continuous)
  have hψc : ψ (φ u₀) = v := by simp [ψ, u₀]
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact φ.symm.injective (Subtype.ext (Subtype.ext hab))
  let S : Set V := ψ ⁻¹' Metric.ball v r
  have hSo : IsOpen S := Metric.isOpen_ball.preimage hψ
  have hSo' : IsOpen (Subtype.val '' S : Set (E n)) := hVo.isOpenMap_subtype_val S hSo
  have hcS : c ∈ (Subtype.val '' S : Set (E n)) :=
    ⟨φ u₀, by simp [S, hψc, hr], rfl⟩
  obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.mp hSo' c hcS
  let T : Set V := Subtype.val ⁻¹' Metric.ball c δ
  have hTo : IsOpen T := Metric.isOpen_ball.preimage continuous_subtype_val
  have hTS : T ⊆ S := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hδS hy
    have : z = y := Subtype.ext hzy
    exact this ▸ hz
  refine ⟨ψ '' T, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨((φ.symm y : U) : X).property, hTS hy⟩
  · let W' : Set X := Subtype.val '' (φ ⁻¹' T)
    have hW'o : IsOpen W' := hUo.isOpenMap_subtype_val _ (hTo.preimage φ.continuous)
    obtain ⟨O, hOo, hOW⟩ := isOpen_induced_iff.mp hW'o
    have hvW' : (⟨v, hv⟩ : X) ∈ W' :=
      ⟨u₀, by simp [T, c, hδ], rfl⟩
    have hvO : v ∈ O := by
      have : (⟨v, hv⟩ : X) ∈ Subtype.val ⁻¹' O := hOW ▸ hvW'
      exact this
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hOo v hvO
    refine ⟨ε, hε, ?_⟩
    rintro x ⟨hxX, hxε⟩
    have hx : (⟨x, hxX⟩ : X) ∈ W' := by
      rw [← hOW]
      exact hεO hxε
    obtain ⟨u, hu, hux⟩ := hx
    refine ⟨φ u, hu, ?_⟩
    simp only [ψ, Homeomorph.symm_apply_apply, hux]
  · have hpT : φ u₀ ∈ T := by simp [T, c, hδ]
    have himg : ψ '' T \ {v} = ψ '' (T \ {φ u₀}) := by
      rw [Set.image_diff hψinj, Set.image_singleton, hψc]
    rw [himg]
    apply IsPreconnected.image _ _ hψ.continuousOn
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    have hball : ∀ y ∈ Metric.ball c δ, y ∈ V := by
      intro y hy
      obtain ⟨z, -, hz⟩ := hδS hy
      exact hz ▸ z.property
    have heq : (Subtype.val '' (T \ {φ u₀}) : Set (E n)) =
        (OpenPartialHomeomorph.univBall c δ) '' ({0}ᶜ) := by
      ext z
      constructor
      · rintro ⟨y, ⟨hyT, hyp⟩, rfl⟩
        have hyb : (y : E n) ∈ (OpenPartialHomeomorph.univBall c δ).target := by
          rw [OpenPartialHomeomorph.univBall_target c hδ]
          exact hyT
        refine ⟨(OpenPartialHomeomorph.univBall c δ).symm y, ?_,
          (OpenPartialHomeomorph.univBall c δ).right_inv hyb⟩
        intro h0
        apply hyp
        apply Subtype.ext
        have := (OpenPartialHomeomorph.univBall c δ).right_inv hyb
        rw [Set.mem_singleton_iff.mp h0, OpenPartialHomeomorph.univBall_apply_zero] at this
        exact this.symm
      · rintro ⟨y, hy0, rfl⟩
        have hyb : (OpenPartialHomeomorph.univBall c δ) y ∈ Metric.ball c δ := by
          rw [← OpenPartialHomeomorph.univBall_target c hδ]
          exact (OpenPartialHomeomorph.univBall c δ).map_source
            (by rw [OpenPartialHomeomorph.univBall_source]; trivial)
        refine ⟨⟨_, hball _ hyb⟩, ⟨hyb, ?_⟩, rfl⟩
        intro hyc
        apply hy0
        have hyc' : (OpenPartialHomeomorph.univBall c δ) y = c := congrArg Subtype.val hyc
        have h1 := (OpenPartialHomeomorph.univBall c δ).left_inv
          (x := y) (by rw [OpenPartialHomeomorph.univBall_source]; trivial)
        rw [hyc', OpenPartialHomeomorph.univBall_symm_apply_center] at h1
        exact h1.symm
    rw [heq]
    have hrank : 1 < Module.rank ℝ (E n) := by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      exact_mod_cast (by omega : 1 < n)
    exact ((isConnected_compl_singleton_of_one_lt_rank hrank 0).isPreconnected.image _
      (OpenPartialHomeomorph.continuous_univBall c δ).continuousOn)

/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains` (V4 1.24):
"`∂t` is a compact `(d-1)`-manifold ... a connected union of facets". Vertex
links: in a finite pure triangulation of a `(d-1)`-manifold with `d - 1 ≥ 2`, the
facets through a vertex `v` are joined by chains of facets through `v` in which
consecutive members share a vertex other than `v`. Otherwise the reachable and the
unreachable facets through `v` form two closed sets meeting only at `v`; a small
punctured chart neighbourhood of `v` (Step 3) lies in their union, meets both, and
would be separated. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains_step4_vertex_links
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d)
    (hman : IsLocallyEuclidean (d - 1) K.space)
    {σ : Finset (E d)} (hσ : σ ∈ K.faces) (hσc : σ.card = 1) (hσd : σ.card + 2 ≤ d) :
    ∀ f g : K.facets, σ ⊆ f.val → σ ⊆ g.val → Relation.ReflTransGen
      (fun u v : K.facets => σ ⊆ u.val ∧ σ ⊆ v.val ∧ σ.card < (u.val ∩ v.val).card) f g := by
  classical
  letI : Finite K.facets := (hfin.subset K.facets_subset).to_subtype
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hσc
  rw [Finset.card_singleton] at hσd
  intro f g hf hg
  by_contra hfg
  let R := fun u w : K.facets => ({v} : Finset (E d)) ⊆ u.val ∧
    ({v} : Finset (E d)) ⊆ w.val ∧ ({v} : Finset (E d)).card < (u.val ∩ w.val).card
  have hvf : v ∈ f.val := Finset.singleton_subset_iff.mp hf
  have hvg : v ∈ g.val := Finset.singleton_subset_iff.mp hg
  let P : Set (E d) := ⋃ h : {h : K.facets // Relation.ReflTransGen R f h},
    convexHull ℝ (h.val.val : Set (E d))
  let Q : Set (E d) := ⋃ h : {h : K.facets // v ∈ h.val ∧ ¬ Relation.ReflTransGen R f h},
    convexHull ℝ (h.val.val : Set (E d))
  let Fr : Set (E d) := ⋃ h : {h : K.facets // v ∉ h.val}, convexHull ℝ (h.val.val : Set (E d))
  have hcl : ∀ h : K.facets, IsClosed (convexHull ℝ (h.val : Set (E d))) :=
    fun h => h.val.finite_toSet.isCompact_convexHull.isClosed
  have hP : IsClosed P := isClosed_iUnion_of_finite fun h => hcl h.val
  have hQ : IsClosed Q := isClosed_iUnion_of_finite fun h => hcl h.val
  have hFr : IsClosed Fr := isClosed_iUnion_of_finite fun h => hcl h.val
  have hreach_v : ∀ h : K.facets, Relation.ReflTransGen R f h → v ∈ h.val := by
    intro h hh
    induction hh with
    | refl => exact hvf
    | tail _ hst _ => exact Finset.singleton_subset_iff.mp hst.2.1
  have hvhull : v ∈ convexHull ℝ ((({v} : Finset (E d)) : Set (E d))) :=
    subset_convexHull ℝ _ (by simp)
  have hvFr : v ∉ Fr := by
    intro hx
    obtain ⟨h, hxh⟩ := Set.mem_iUnion.mp hx
    have hxi := K.inter_subset_convexHull h.val.property.1 hσ ⟨hxh, hvhull⟩
    have hempty : ((h.val.val : Set (E d)) ∩ (({v} : Finset (E d)) : Set (E d))) = ∅ := by
      ext y
      simp only [Finset.coe_singleton, Set.mem_inter_iff, Finset.mem_coe,
        Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro hy rfl
      exact h.property hy
    rw [hempty, convexHull_empty] at hxi
    exact hxi
  obtain ⟨r, hr, hrFr⟩ := Metric.isOpen_iff.mp hFr.isOpen_compl v hvFr
  have hd2 : 2 ≤ d - 1 := by omega
  obtain ⟨W, hWsub, ⟨ε, hε, hεW⟩, hWc⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains_step3_punctured_charts
      hd2 hman (K.convexHull_subset_space hσ hvhull) hr
  have hcover :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step9_facets_cover K hfin
  have hWPQ : W \ {v} ⊆ P ∪ Q := by
    rintro x ⟨hxW, -⟩
    have hxK := (hWsub hxW).1
    rw [hcover] at hxK
    obtain ⟨h, hxh⟩ := Set.mem_iUnion.mp hxK
    by_cases hvh : v ∈ h.val
    · by_cases hrh : Relation.ReflTransGen R f h
      · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨h, hrh⟩, hxh⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨h, hvh, hrh⟩, hxh⟩)
    · exact absurd (Set.mem_iUnion.mpr ⟨⟨h, hvh⟩, hxh⟩) (hrFr (hWsub hxW).2)
  have hPQ : P ∩ Q ⊆ {v} := by
    rintro x ⟨hxP, hxQ⟩
    obtain ⟨h, hxh⟩ := Set.mem_iUnion.mp hxP
    obtain ⟨h', hxh'⟩ := Set.mem_iUnion.mp hxQ
    have hxi := K.inter_subset_convexHull h.val.property.1 h'.val.property.1 ⟨hxh, hxh'⟩
    have hvh := hreach_v h.val h.property
    have hmem : v ∈ h.val.val ∩ h'.val.val := Finset.mem_inter.mpr ⟨hvh, h'.property.1⟩
    have hcard : (h.val.val ∩ h'.val.val).card ≤ 1 := by
      by_contra hc
      apply h'.property.2
      exact h.property.tail ⟨Finset.singleton_subset_iff.mpr hvh,
        Finset.singleton_subset_iff.mpr h'.property.1, by rw [Finset.card_singleton]; omega⟩
    have heq : h.val.val ∩ h'.val.val = {v} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hmem, fun y hy => Finset.card_le_one.mp hcard y hy v hmem⟩
    have hs : ((h.val.val : Set (E d)) ∩ (h'.val.val : Set (E d))) = {v} := by
      rw [← Finset.coe_inter, heq, Finset.coe_singleton]
    rw [hs, convexHull_singleton] at hxi
    exact hxi
  have hnear : ∀ h : K.facets, v ∈ h.val →
      ∃ p ∈ convexHull ℝ (h.val : Set (E d)), p ≠ v ∧ dist p v < ε := by
    intro h hvh
    have h1 : 1 < h.val.card := by rw [hpure h.val h.property]; omega
    obtain ⟨w, hw, hwv⟩ := Finset.exists_mem_ne h1 v
    have hdist : 0 < dist v w := dist_pos.mpr (Ne.symm hwv)
    let t : ℝ := min (1 / 2) (ε / (2 * dist v w))
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
    have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have htε : t * dist v w < ε := by
      calc t * dist v w ≤ ε / (2 * dist v w) * dist v w :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hdist.le
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    refine ⟨AffineMap.lineMap v w t, ?_, ?_, ?_⟩
    · apply segment_subset_convexHull (Finset.mem_coe.mpr hvh) (Finset.mem_coe.mpr hw)
      rw [segment_eq_image_lineMap]
      exact ⟨t, ⟨ht0.le, ht1⟩, rfl⟩
    · intro heq
      have hd := dist_lineMap_left v w t
      rw [heq, dist_self, Real.norm_eq_abs, abs_of_pos ht0] at hd
      have : 0 < t * dist v w := mul_pos ht0 hdist
      linarith
    · rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_pos ht0]
      exact htε
  obtain ⟨p, hpf, hpv, hpε⟩ := hnear f hvf
  obtain ⟨q, hqg, hqv, hqε⟩ := hnear g hvg
  have hpW : p ∈ W \ {v} :=
    ⟨hεW ⟨K.convexHull_subset_space f.property.1 hpf, Metric.mem_ball.mpr hpε⟩, hpv⟩
  have hqW : q ∈ W \ {v} :=
    ⟨hεW ⟨K.convexHull_subset_space g.property.1 hqg, Metric.mem_ball.mpr hqε⟩, hqv⟩
  obtain ⟨x, hxW, hxP, hxQ⟩ := isPreconnected_closed_iff.mp hWc P Q hP hQ hWPQ
    ⟨p, hpW, Set.mem_iUnion.mpr ⟨⟨f, Relation.ReflTransGen.refl⟩, hpf⟩⟩
    ⟨q, hqW, Set.mem_iUnion.mpr ⟨⟨g, hvg, hfg⟩, hqg⟩⟩
  exact hxW.2 (hPQ ⟨hxP, hxQ⟩)

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains` (V4 1.24):
"`∂t` is a compact `(d-1)`-manifold ... a connected union of facets". Links of
higher faces: for a face `σ` with `2 ≤ |σ|` and `|σ| + 2 ≤ d` (dimension at most
`(d-1) - 2`, at least `1`) of a finite pure triangulation of a `(d-1)`-manifold, the
facets containing `σ` are joined by chains of facets containing `σ` in which
consecutive members share a vertex outside `σ` (the link of `σ` is connected).
Standard proof: the open star of `σ` is `relint σ × cone(Lk σ)`; local homology of
the manifold at a point of `relint σ` makes `Lk σ` a homology sphere of dimension
`d - 1 - |σ| ≥ 1`, hence connected. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains_step5_face_links
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d)
    (hman : IsLocallyEuclidean (d - 1) K.space)
    {σ : Finset (E d)} (hσ : σ ∈ K.faces) (hσc : 2 ≤ σ.card) (hσd : σ.card + 2 ≤ d) :
    ∀ f g : K.facets, σ ⊆ f.val → σ ⊆ g.val → Relation.ReflTransGen
      (fun u v : K.facets => σ ⊆ u.val ∧ σ ⊆ v.val ∧ σ.card < (u.val ∩ v.val).card) f g := by
  sorry

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains` (V4 1.24):
"a connected union of facets". Connected links of all faces of codimension at
least two turn meeting facets into ridge chains: by downward induction on the size
of the common face `f ∩ g`, a link chain around `f ∩ g` consists of steps with
strictly larger common faces. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains_step6_ridge_of_meet
    (K : Geometry.SimplicialComplex ℝ (E d))
    (hpure : ∀ f ∈ K.facets, f.card = d)
    (hlink : ∀ σ ∈ K.faces, σ.card + 2 ≤ d → ∀ f g : K.facets, σ ⊆ f.val → σ ⊆ g.val →
      Relation.ReflTransGen
        (fun u v : K.facets => σ ⊆ u.val ∧ σ ⊆ v.val ∧ σ.card < (u.val ∩ v.val).card) f g) :
    ∀ f g : K.facets, (f.val ∩ g.val).Nonempty → Relation.ReflTransGen
      (fun u v : K.facets => (u.val ∩ v.val).card = d - 1) f g := by
  classical
  suffices h : ∀ n : ℕ, ∀ f g : K.facets, d - (f.val ∩ g.val).card ≤ n →
      (f.val ∩ g.val).Nonempty → Relation.ReflTransGen
        (fun u v : K.facets => (u.val ∩ v.val).card = d - 1) f g by
    intro f g hne
    exact h _ f g le_rfl hne
  intro n
  induction n with
  | zero =>
    intro f g hn _
    have hle : (f.val ∩ g.val).card ≤ f.val.card :=
      Finset.card_le_card Finset.inter_subset_left
    have hfc := hpure f.val f.property
    have heq : f.val ∩ g.val = f.val :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hfg : f = g := by
      apply Subtype.ext
      apply f.property.2 g.property.1
      rw [← heq]
      exact Finset.inter_subset_right
    subst hfg
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro f g hn hne
    by_cases hbig : d - (f.val ∩ g.val).card ≤ n
    · exact ih f g hbig hne
    by_cases hridge : (f.val ∩ g.val).card = d - 1
    · exact Relation.ReflTransGen.single hridge
    have hle : (f.val ∩ g.val).card ≤ d := by
      have := Finset.card_le_card (Finset.inter_subset_left (s₁ := f.val) (s₂ := g.val))
      rw [hpure f.val f.property] at this
      exact this
    have hσd : (f.val ∩ g.val).card + 2 ≤ d := by omega
    have hσ : f.val ∩ g.val ∈ K.faces :=
      K.down_closed f.property.1 Finset.inter_subset_left hne
    have hch := hlink _ hσ hσd f g Finset.inter_subset_left Finset.inter_subset_right
    have h2 : Relation.ReflTransGen (Relation.ReflTransGen
        (fun u v : K.facets => (u.val ∩ v.val).card = d - 1)) f g := by
      refine Relation.ReflTransGen.mono ?_ hch
      rintro u v ⟨hu, hv, hlt⟩
      have hule : (u.val ∩ v.val).card ≤ d := by
        have := Finset.card_le_card (Finset.inter_subset_left (s₁ := u.val) (s₂ := v.val))
        rw [hpure u.val u.property] at this
        exact this
      exact ih u v (by omega) (hne.mono (Finset.subset_inter hu hv))
    rwa [Relation.reflTransGen_idem] at h2

/-- Step 11 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"a connected union of facets". The facets in a finite triangulation of a connected
manifold are joined by chains across ridges. This concerns the manifold itself,
not components of its ambient complement. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d)
    (hconn : IsConnected K.space) (hman : IsLocallyEuclidean (d - 1) K.space) :
    ∀ f g : K.facets, Relation.ReflTransGen
      (fun u v : K.facets => (u.val ∩ v.val).card = d - 1) f g := by
  classical
  have hmeet :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains_step2_meet_chains
      K hfin hconn
  have hlink : ∀ σ ∈ K.faces, σ.card + 2 ≤ d → ∀ f g : K.facets, σ ⊆ f.val → σ ⊆ g.val →
      Relation.ReflTransGen
        (fun u v : K.facets => σ ⊆ u.val ∧ σ ⊆ v.val ∧ σ.card < (u.val ∩ v.val).card) f g := by
    intro σ hσ hσd
    rcases Nat.lt_or_ge σ.card 2 with h | h
    · have h1 : σ.card = 1 := by
        have := (K.nonempty_of_mem_faces hσ).card_pos
        omega
      exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains_step4_vertex_links
        K hfin hpure hman hσ h1 hσd
    · exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains_step5_face_links
        K hfin hpure hman hσ h hσd
  have hridge :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains_step6_ridge_of_meet
      K hpure hlink
  intro f g
  have h2 := Relation.ReflTransGen.mono (fun u v huv => hridge u v huv) (hmeet f g)
  rwa [Relation.reflTransGen_idem] at h2

/-- Step 12 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"crosses them transversally at finitely many points". A regular segment has
endpoints off the complex and meets it only transversally in facet interiors. -/
private def principal_component_step1_hull_geometry_step10_jordan_brouwer_step12_RegularSegment
    (K : Geometry.SimplicialComplex ℝ (E d)) (a b : E d) : Prop :=
  a ∉ K.space ∧ b ∉ K.space ∧ (segment ℝ a b ∩ K.space).Finite ∧
    ∀ x ∈ segment ℝ a b ∩ K.space, ∃ f ∈ K.facets,
      x ∈ relint (convexHull ℝ (f : Set (E d))) ∧
      a ∉ (affineSpan ℝ (f : Set (E d)) : Set (E d)) ∧
      b ∉ (affineSpan ℝ (f : Set (E d)) : Set (E d))

/-- Step 13 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"in general position ... crosses them transversally". For the parity calculation,
a triangular section avoids faces of codimension at least three and meets each
ridge it encounters transversally in one point. The disjointness clauses record
that the three sides have no common crossing at a triangle vertex. -/
private def principal_component_step1_hull_geometry_step10_jordan_brouwer_step13_TrianglePosition
    (K : Geometry.SimplicialComplex ℝ (E d)) (a b c : E d) : Prop :=
  let T := convexHull ℝ ({a, b, c} : Set (E d))
  let A := (affineSpan ℝ ({a, b, c} : Set (E d)) : Set (E d))
  AffineIndependent ℝ ![a, b, c] ∧
  principal_component_step1_hull_geometry_step10_jordan_brouwer_step12_RegularSegment K a b ∧
  principal_component_step1_hull_geometry_step10_jordan_brouwer_step12_RegularSegment K b c ∧
  principal_component_step1_hull_geometry_step10_jordan_brouwer_step12_RegularSegment K c a ∧
  Disjoint (segment ℝ a b ∩ K.space) (segment ℝ b c ∩ K.space) ∧
  Disjoint ((segment ℝ a b ∩ K.space) ∪ (segment ℝ b c ∩ K.space))
    (segment ℝ c a ∩ K.space) ∧
  (∀ s ∈ K.faces, s.card + 1 < d → Disjoint T (convexHull ℝ (s : Set (E d)))) ∧
  (∀ s ∈ K.faces, s.card = d - 1 →
    (T ∩ convexHull ℝ (s : Set (E d))).Nonempty →
    (A ∩ (affineSpan ℝ (s : Set (E d)) : Set (E d))).Subsingleton) ∧
  ∀ f ∈ K.facets, ¬ A ⊆ (affineSpan ℝ (f : Set (E d)) : Set (E d))

/-- Step 14 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"the complement locally is on the other side". This certificate names two
opposite normal sample points in one flat facet patch. It imposes no global
separation or connectedness condition. -/
private def principal_component_step1_hull_geometry_step10_jordan_brouwer_step14_FacetSides
    (K : Geometry.SimplicialComplex ℝ (E d)) (f : Finset (E d)) (a b : E d) : Prop :=
  ∃ q : E d, ∃ r : ℝ, ∃ v : E d,
    q ∈ relint (convexHull ℝ (f : Set (E d))) ∧ 0 < r ∧ ‖v‖ = 1 ∧
    (affineSpan ℝ (f : Set (E d)) : Set (E d)) = {x | inner ℝ v (x - q) = 0} ∧
    K.space ∩ Metric.ball q r =
      (affineSpan ℝ (f : Set (E d)) : Set (E d)) ∩ Metric.ball q r ∧
    a = q + (r / 2) • v ∧ b = q - (r / 2) • v

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples` (V4 1.24):
"a compact `(d-1)`-manifold". The affine span of a simplex with `d` vertices
in `E d` is a hyperplane, and hence has a unit normal. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step1_unit_normal
    (f : Finset (E d)) (hi : AffineIndependent ℝ ((↑) : f → E d))
    (hne : f.Nonempty) (hcard : f.card = d) {q : E d}
    (hq : q ∈ affineSpan ℝ (f : Set (E d))) :
    ∃ v : E d, ‖v‖ = 1 ∧
      (affineSpan ℝ (f : Set (E d)) : Set (E d)) =
        {x | inner ℝ v (x - q) = 0} := by
  classical
  let V := (affineSpan ℝ (f : Set (E d))).direction
  haveI : Nonempty f := hne.to_subtype
  have hdim : Module.finrank ℝ V + 1 = d := by
    dsimp only [V]
    rw [direction_affineSpan]
    have hrange : Set.range ((↑) : f → E d) = (f : Set (E d)) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    have hdim' := hi.finrank_vectorSpan_add_one
    rw [hrange] at hdim'
    simpa only [Fintype.card_coe, hcard] using hdim'
  have horth : Module.finrank ℝ Vᗮ = 1 := by
    apply Submodule.finrank_add_finrank_orthogonal'
    simpa using hdim
  haveI : Nontrivial Vᗮ := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank ℝ Vᗮ by omega)
  obtain ⟨v, hv⟩ := exists_norm_eq Vᗮ (show (0 : ℝ) ≤ 1 by norm_num)
  have hv0 : (v : E d) ≠ 0 := by
    intro h
    have hv' : ‖(v : E d)‖ = 1 := hv
    simpa [h] using hv'
  have hspan : (ℝ ∙ (v : E d)) = Vᗮ := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr v.property)
    · rw [finrank_span_singleton hv0, horth]
  have hV : V = (ℝ ∙ (v : E d))ᗮ := by
    rw [hspan, Submodule.orthogonal_orthogonal]
  refine ⟨v, hv, ?_⟩
  ext x
  have hx : x ∈ affineSpan ℝ (f : Set (E d)) ↔ x - q ∈ V := by
    simpa using (affineSpan ℝ (f : Set (E d))).vadd_mem_iff_mem_direction (x - q) hq
  change x ∈ affineSpan ℝ (f : Set (E d)) ↔ inner ℝ (v : E d) (x - q) = 0
  exact hx.trans ((congrArg (fun W : Submodule ℝ (E d) => x - q ∈ W) hV).to_iff.trans
    Submodule.mem_orthogonal_singleton_iff_inner_right)

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples` (V4 1.24):
"the complement locally is on the other side". At an interior point of a
maximal simplex, all other simplices can be excluded by a ball; within that
ball the simplex fills its affine span. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step2_flat_patch
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (f : K.facets) {q : E d}
    (hq : q ∈ relint (convexHull ℝ (f.val : Set (E d)))) :
    ∃ r : ℝ, 0 < r ∧ K.space ∩ Metric.ball q r =
      (affineSpan ℝ (f.val : Set (E d)) : Set (E d)) ∩ Metric.ball q r := by
  classical
  have hqC : q ∈ convexHull ℝ (f.val : Set (E d)) := intrinsicInterior_subset hq
  have hqH : q ∈ affineSpan ℝ (f.val : Set (E d)) := convexHull_subset_affineSpan _ hqC
  have hq' := hq
  unfold relint intrinsicInterior at hq'
  rw [affineSpan_convexHull] at hq'
  obtain ⟨q', hqi, hqe⟩ := hq'
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hqi)
  have hfill : (affineSpan ℝ (f.val : Set (E d)) : Set (E d)) ∩ Metric.ball q r ⊆
      convexHull ℝ (f.val : Set (E d)) := by
    intro x hx
    apply hball (a := ⟨x, hx.1⟩)
    simpa only [Metric.mem_ball, Subtype.dist_eq, hqe] using hx.2
  obtain ⟨s, hfs, hsind, hsspan⟩ :=
    exists_subset_affineIndependent_affineSpan_eq_top (K.indep f.property.1)
  let b : AffineBasis s ℝ (E d) := ⟨(↑), hsind, by simpa using hsspan⟩
  have hinc {g : Finset (E d)} (hg : g ∈ K.faces)
      (hqg : q ∈ convexHull ℝ (g : Set (E d))) : f.val ⊆ g := by
    intro p hp
    by_contra hpg
    let i : s := ⟨p, hfs hp⟩
    have hnonneg : convexHull ℝ (f.val : Set (E d)) ⊆ {x | 0 ≤ b.coord i x} := by
      apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage (b.coord i))
      intro y hy
      let j : s := ⟨y, hfs hy⟩
      change 0 ≤ b.coord i (b j)
      simp only [b.coord_apply]
      split_ifs <;> norm_num
    have hzero : convexHull ℝ ((f.val : Set (E d)) ∩ (g : Set (E d))) ⊆
        {x | b.coord i x = 0} := by
      apply convexHull_min ?_ ((convex_singleton (0 : ℝ)).affine_preimage (b.coord i))
      intro y hy
      let j : s := ⟨y, hfs hy.1⟩
      have hij : i ≠ j := by
        intro h
        have hpy : p = y := congrArg Subtype.val h
        exact hpg (by simpa only [hpy] using hy.2)
      change b.coord i (b j) = 0
      exact b.coord_apply_ne hij
    have hcoordq : b.coord i q = 0 :=
      hzero (K.inter_subset_convexHull f.property.1 hg ⟨hqC, hqg⟩)
    have hcoordp : b.coord i p = 1 := b.coord_apply_eq i
    obtain ⟨ε, hε, hεr⟩ := exists_pos_mul_lt hr ‖q - p‖
    let z := q + ε • (q - p)
    have hzH : z ∈ affineSpan ℝ (f.val : Set (E d)) := by
      have hpH : p ∈ affineSpan ℝ (f.val : Set (E d)) := subset_affineSpan ℝ _ hp
      simpa only [vsub_eq_sub, vadd_eq_add, add_comm] using
        AffineSubspace.vadd_mem_of_mem_direction
          ((affineSpan ℝ (f.val : Set (E d))).direction.smul_mem ε
            (AffineSubspace.vsub_mem_direction hqH hpH)) hqH
    have hzball : z ∈ Metric.ball q r := by
      simpa [z, Metric.mem_ball, dist_eq_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos hε, mul_comm] using hεr
    have hzcoord : b.coord i z = -ε := by
      calc
        b.coord i z = b.coord i (ε • (q -ᵥ p) +ᵥ q) := by
          simp only [z, vsub_eq_sub, vadd_eq_add, add_comm]
        _ = ε • (b.coord i q -ᵥ b.coord i p) +ᵥ b.coord i q := by
          rw [AffineMap.map_vadd, LinearMap.map_smul, AffineMap.linearMap_vsub]
        _ = -ε := by simp [hcoordq, hcoordp]
    have := hnonneg (hfill ⟨hzH, hzball⟩)
    change 0 ≤ b.coord i z at this
    rw [hzcoord] at this
    linarith
  let U : Set (E d) := ⋃ g ∈ K.faces \ {f.val}, convexHull ℝ (g : Set (E d))
  have hUclosed : IsClosed U :=
    hfin.diff.isClosed_biUnion (fun g _ => g.finite_toSet.isClosed_convexHull)
  have hqU : q ∉ U := by
    intro h
    obtain ⟨g, hg, hqg⟩ := Set.mem_iUnion₂.mp h
    exact hg.2 (Set.mem_singleton_iff.mpr (f.property.2 hg.1 (hinc hg.1 hqg)).symm)
  obtain ⟨t, ht, htball⟩ := Metric.mem_nhds_iff.mp (hUclosed.isOpen_compl.mem_nhds hqU)
  refine ⟨min r t, lt_min hr ht, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg, hxg⟩ := K.mem_space_iff.mp hx.1
    by_cases hgf : g = f.val
    · subst g
      exact ⟨convexHull_subset_affineSpan _ hxg, hx.2⟩
    · exact False.elim (htball (Metric.ball_subset_ball (min_le_right _ _) hx.2)
        (Set.mem_iUnion₂.mpr ⟨g, ⟨hg, hgf⟩, hxg⟩))
  · intro hx
    exact ⟨K.convexHull_subset_space f.property.1
      (hfill ⟨hx.1, Metric.ball_subset_ball (min_le_left _ _) hx.2⟩), hx.2⟩

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples` (V4 1.24):
"every point ... is a limit of points". A nonempty closed simplex has connected
relative interior, and that relative interior is dense in the simplex. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step3_relative_interior
    (f : Finset (E d)) (hne : f.Nonempty) :
    IsConnected (relint (convexHull ℝ (f : Set (E d)))) ∧
      closure (relint (convexHull ℝ (f : Set (E d)))) =
        convexHull ℝ (f : Set (E d)) := by
  let C := convexHull ℝ (f : Set (E d))
  have hconv : Convex ℝ C := convex_convexHull ℝ _
  have hclosed : IsClosed C := f.finite_toSet.isClosed_convexHull
  obtain ⟨p, hp⟩ := hne
  have hpC : p ∈ C := subset_convexHull ℝ _ hp
  let H := affineSpan ℝ C
  haveI : Nonempty H := ⟨⟨p, subset_affineSpan ℝ C hpC⟩⟩
  let e := (AffineIsometryEquiv.constVSub ℝ
    (⟨p, subset_affineSpan ℝ C hpC⟩ : H)).symm
  let φ : H.direction →ᵃ[ℝ] E d := H.subtype.comp e.toAffineEquiv.toAffineMap
  let T : Set H.direction := φ ⁻¹' C
  have hφ : Continuous φ := φ.continuous_of_finiteDimensional
  have hT : Convex ℝ T := hconv.affine_preimage φ
  have hrel : relint C = φ '' interior T := by
    calc
      relint C = (Subtype.val : H → E d) '' interior (Subtype.val ⁻¹' C) := rfl
      _ = Subtype.val '' (e.toHomeomorph ''
          (e.toHomeomorph ⁻¹' interior (Subtype.val ⁻¹' C))) := by
        rw [e.toHomeomorph.image_preimage]
      _ = φ '' interior T := by
        rw [e.toHomeomorph.preimage_interior, Set.image_image]
        rfl
  have hneRel : (relint C).Nonempty :=
    Set.Nonempty.intrinsicInterior hconv ⟨p, hpC⟩
  have hneT : (interior T).Nonempty := Set.image_nonempty.mp (hrel ▸ hneRel)
  refine ⟨⟨hneRel, ?_⟩, Set.Subset.antisymm ?_ ?_⟩
  · change IsPreconnected (relint C)
    rw [hrel]
    exact hT.interior.isPreconnected.image φ hφ.continuousOn
  · exact hclosed.closure_subset_iff.mpr intrinsicInterior_subset
  · intro x hx
    let z : H.direction := e.symm ⟨x, subset_affineSpan ℝ C hx⟩
    have hz : φ z = x := by simp [φ, z]
    have hzT : z ∈ T := by change φ z ∈ C; rwa [hz]
    change x ∈ closure (relint C)
    rw [hrel]
    apply image_closure_subset_closure_image hφ
    refine ⟨z, ?_, hz⟩
    rw [hT.closure_interior_eq_closure_of_nonempty_interior hneT]
    exact subset_closure hzT

/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples` (V4 1.24):
"the complement locally is on the other side". A normal half-ball is convex,
lies in one complementary component, and accumulates at its centre. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step4_half_ball
    (T : Set (E d)) (q v : E d) (r : ℝ) (hr : 0 < r) (hv : ‖v‖ = 1)
    (hflat : ∀ x ∈ T ∩ Metric.ball q r, inner ℝ v (x - q) = 0) :
    (Metric.ball q r ∩ {x | 0 < inner ℝ v (x - q)}) ⊆
        connectedComponentIn Tᶜ (q + (r / 2) • v) ∧
      q ∈ closure (connectedComponentIn Tᶜ (q + (r / 2) • v)) := by
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hdist (t : ℝ) (ht : 0 ≤ t) : dist (q + t • v) q = t := by
    simp [dist_eq_norm, norm_smul, hv, Real.norm_eq_abs, abs_of_nonneg ht]
  have hmem (t : ℝ) (ht : 0 < t) (htr : t < r) :
      q + t • v ∈ Metric.ball q r ∩ {x | 0 < inner ℝ v (x - q)} := by
    constructor
    · simpa only [Metric.mem_ball, hdist t ht.le] using htr
    · simpa [inner_smul_right, hvv, hv] using ht
  have hconv : Convex ℝ (Metric.ball q r ∩ {x | 0 < inner ℝ v (x - q)}) := by
    apply (convex_ball q r).inter
    simpa only [inner_sub_right, sub_pos] using
      (convex_Ioi (inner ℝ v q)).linear_preimage (innerSL ℝ v).toLinearMap
  have hsub : Metric.ball q r ∩ {x | 0 < inner ℝ v (x - q)} ⊆
      connectedComponentIn Tᶜ (q + (r / 2) • v) := by
    apply hconv.isPreconnected.subset_connectedComponentIn
      (hmem (r / 2) (by linarith) (by linarith))
    intro x hx hxT
    exact (ne_of_gt hx.2) (hflat x ⟨hxT, hx.1⟩)
  refine ⟨hsub, Metric.mem_closure_iff.mpr ?_⟩
  intro ε hε
  let t := min (r / 2) (ε / 2)
  have ht : 0 < t := lt_min (by linarith) (by linarith)
  have htr : t < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htε : t < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  exact ⟨q + t • v, hsub (hmem t ht htr), by rw [dist_comm, hdist t ht.le]; exact htε⟩

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples` (V4 1.24):
"has all its points adjacent to the same complementary component". On a
connected subset of a fixed hyperplane with flat neighbourhoods, the component
on a chosen normal side is locally constant, hence constant. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step5_side_transport
    (T R : Set (E d)) (hconn : IsPreconnected R) (q v : E d) (hq : q ∈ R)
    (hv : ‖v‖ = 1) (hplane : ∀ x ∈ R, inner ℝ v (x - q) = 0)
    (hlocal : ∀ x ∈ R, ∃ s : ℝ, 0 < s ∧
      ∀ y ∈ T ∩ Metric.ball x s, inner ℝ v (y - x) = 0)
    (r : ℝ) (hr : 0 < r)
    (hflat : ∀ x ∈ T ∩ Metric.ball q r, inner ℝ v (x - q) = 0) :
    R ⊆ closure (connectedComponentIn Tᶜ (q + (r / 2) • v)) := by
  classical
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hcompare {x y : E d} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
      (hx : ∀ z ∈ T ∩ Metric.ball x s, inner ℝ v (z - x) = 0)
      (hy : ∀ z ∈ T ∩ Metric.ball y t, inner ℝ v (z - y) = 0)
      (hxy : inner ℝ v (y - x) = 0) (hnear : dist y x < s) :
      connectedComponentIn Tᶜ (x + (s / 2) • v) =
        connectedComponentIn Tᶜ (y + (t / 2) • v) := by
    let u := min (t / 2) ((s - dist y x) / 2)
    have hu : 0 < u := lt_min (by linarith) (by linarith)
    have hut : u < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hus : u + dist y x < s := by
      have := min_le_right (t / 2) ((s - dist y x) / 2)
      dsimp [u]
      linarith
    let z := y + u • v
    have hzy : dist z y = u := by
      simp [z, dist_eq_norm, norm_smul, hv, Real.norm_eq_abs, abs_of_pos hu]
    have hzx : dist z x < s := by
      calc
        dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ = u + dist y x := by rw [hzy]
        _ < s := hus
    have hzinner : inner ℝ v (z - x) = u := by
      have : z - x = (y - x) + u • v := by dsimp [z]; abel
      rw [this, inner_add_right, inner_smul_right, hxy, hvv]
      ring
    have hzinner' : inner ℝ v (z - y) = u := by
      simp [z, inner_smul_right, hvv, hv]
    have hz₁ :=
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step4_half_ball
        T x v s hs hv hx).1 ⟨hzx, by simpa only [Set.mem_setOf_eq, hzinner] using hu⟩
    have hz₂ : z ∈ connectedComponentIn Tᶜ (y + (t / 2) • v) :=
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step4_half_ball
        T y v t ht hv hy).1
        ⟨by simpa only [Metric.mem_ball, hzy] using hut,
          by simpa only [Set.mem_setOf_eq, hzinner'] using hu⟩
    exact (connectedComponentIn_eq hz₁).trans (connectedComponentIn_eq hz₂).symm
  choose ρ hρ hρflat using fun x : R => hlocal x x.property
  let c (x : R) := connectedComponentIn Tᶜ ((x : E d) + (ρ x / 2) • v)
  have hconstant : IsLocallyConstant c := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    have hnear : ∀ᶠ y : R in nhds x, (y : E d) ∈ Metric.ball (x : E d) (ρ x) :=
      continuous_subtype_val.continuousAt.eventually
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hρ x)))
    filter_upwards [hnear] with y hy
    apply (hcompare (hρ x) (hρ y) (hρflat x) (hρflat y) ?_ hy).symm
    have hxq := hplane x x.property
    have hyq := hplane y y.property
    simp only [inner_sub_right] at hxq hyq ⊢
    linarith
  have hcq : c ⟨q, hq⟩ = connectedComponentIn Tᶜ (q + (r / 2) • v) := by
    apply hcompare (hρ ⟨q, hq⟩) hr (hρflat ⟨q, hq⟩) hflat
    · simp
    · simpa using hρ ⟨q, hq⟩
  have hR : IsPreconnected (Set.univ : Set R) :=
    (Subtype.preconnectedSpace hconn).isPreconnected_univ
  intro x hx
  have hcx : c ⟨x, hx⟩ = connectedComponentIn Tᶜ (q + (r / 2) • v) :=
    (hconstant.apply_eq_of_isPreconnected hR (Set.mem_univ ⟨x, hx⟩)
      (Set.mem_univ ⟨q, hq⟩)).trans hcq
  rw [← hcx]
  exact
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step4_half_ball
      T x v (ρ ⟨x, hx⟩) (hρ ⟨x, hx⟩) hv (hρflat ⟨x, hx⟩)).2

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples` (V4 1.24):
"crosses them transversally at finitely many points". A segment between opposite
normal samples in a flat facet patch meets the complex exactly at its centre. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step6_single_crossing
    (K : Geometry.SimplicialComplex ℝ (E d)) (f : K.facets) {a b : E d}
    (hsides : principal_component_step1_hull_geometry_step10_jordan_brouwer_step14_FacetSides K f.val a b) :
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step12_RegularSegment K a b ∧
      (segment ℝ a b ∩ K.space).ncard = 1 := by
  obtain ⟨q, r, v, hq, hr, hv, hplane, hpatch, rfl, rfl⟩ := hsides
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have ha : q + (r / 2) • v ∈ Metric.ball q r := by
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, hv, mul_one, abs_of_pos (show 0 < r / 2 by linarith)]
    linarith
  have hb : q - (r / 2) • v ∈ Metric.ball q r := by
    rw [sub_eq_add_neg, ← neg_smul]
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_neg, hv, mul_one] using ha
  have haH : q + (r / 2) • v ∉ affineSpan ℝ (f.val : Set (E d)) := by
    rw [← SetLike.mem_coe, hplane]
    simp only [Set.mem_setOf_eq, add_sub_cancel_left, inner_smul_right, hvv, mul_one]
    linarith
  have hbH : q - (r / 2) • v ∉ affineSpan ℝ (f.val : Set (E d)) := by
    rw [← SetLike.mem_coe, hplane]
    simp only [Set.mem_setOf_eq, sub_sub_cancel_left, inner_neg_right, inner_smul_right,
      hvv, mul_one, neg_eq_zero]
    linarith
  have haK : q + (r / 2) • v ∉ K.space :=
    fun h => haH ((Set.ext_iff.mp hpatch _).mp ⟨h, ha⟩).1
  have hbK : q - (r / 2) • v ∉ K.space :=
    fun h => hbH ((Set.ext_iff.mp hpatch _).mp ⟨h, hb⟩).1
  have hseg : segment ℝ (q + (r / 2) • v) (q - (r / 2) • v) ⊆ Metric.ball q r :=
    (convex_ball q r).segment_subset ha hb
  have hcross : segment ℝ (q + (r / 2) • v) (q - (r / 2) • v) ∩ K.space = {q} := by
    ext x
    constructor
    · intro hx
      have hxH := ((Set.ext_iff.mp hpatch x).mp ⟨hx.2, hseg hx.1⟩).1
      rw [hplane] at hxH
      obtain ⟨α, β, hα, hβ, hab, hxeq⟩ := hx.1
      have heq : x = q + ((α - β) * (r / 2)) • v := by
        rw [← hxeq]
        calc
          _ = (α + β) • q + ((α - β) * (r / 2)) • v := by module
          _ = _ := by rw [hab, one_smul]
      rw [heq] at hxH
      have hz : (α - β) * (r / 2) = 0 := by
        simpa [inner_smul_right, hvv, hv] using hxH
      simpa [heq, hz]
    · rintro rfl
      constructor
      · refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
        module
      · exact K.convexHull_subset_space f.property.1 (intrinsicInterior_subset hq)
  refine ⟨⟨haK, hbK, ?_, ?_⟩, ?_⟩
  · rw [hcross]
    exact Set.finite_singleton q
  · intro x hx
    have hxq : x = q := by simpa only [hcross, Set.mem_singleton_iff] using hx
    subst x
    exact ⟨f.val, f.property, hq, haH, hbH⟩
  · rw [hcross, Set.ncard_singleton]

/-- Step 15 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"near which the complement locally is on the other side". Choose normal samples
at a facet interior. Its two open normal collars are connected, and their closures
contain the entire closed simplex. The joining segment crosses exactly once. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d) (f : K.facets) :
    ∃ a b : E d,
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step14_FacetSides K f.val a b ∧
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step12_RegularSegment K a b ∧
      (segment ℝ a b ∩ K.space).ncard = 1 ∧
      convexHull ℝ (f.val : Set (E d)) ⊆ frontier (connectedComponentIn K.spaceᶜ a) ∧
      convexHull ℝ (f.val : Set (E d)) ⊆ frontier (connectedComponentIn K.spaceᶜ b) := by
  have hfne := K.nonempty_of_mem_faces f.property.1
  obtain ⟨hconn, hclosure⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step3_relative_interior
      f.val hfne
  obtain ⟨q, hq⟩ := hconn.nonempty
  have hqH : q ∈ affineSpan ℝ (f.val : Set (E d)) :=
    convexHull_subset_affineSpan _ (intrinsicInterior_subset hq)
  obtain ⟨v, hv, hplane⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step1_unit_normal
      f.val (K.indep f.property.1) hfne (hpure f.val f.property) hqH
  obtain ⟨r, hr, hpatch⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step2_flat_patch
      K hfin f hq
  have hsides :
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step14_FacetSides K f.val
        (q + (r / 2) • v) (q - (r / 2) • v) :=
    ⟨q, r, v, hq, hr, hv, hplane, hpatch, rfl, rfl⟩
  obtain ⟨hreg, hcard⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step6_single_crossing
      K f hsides
  have hfront (w : E d) (hw : ‖w‖ = 1)
      (hwplane : (affineSpan ℝ (f.val : Set (E d)) : Set (E d)) =
        {x | inner ℝ w (x - q) = 0}) :
      convexHull ℝ (f.val : Set (E d)) ⊆
        frontier (connectedComponentIn K.spaceᶜ (q + (r / 2) • w)) := by
    have hzero {x : E d} (hx : x ∈ affineSpan ℝ (f.val : Set (E d))) :
        inner ℝ w (x - q) = 0 := by
      change x ∈ (affineSpan ℝ (f.val : Set (E d)) : Set (E d)) at hx
      simpa only [hwplane, Set.mem_setOf_eq] using hx
    have hrel :=
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step5_side_transport
        K.space (relint (convexHull ℝ (f.val : Set (E d)))) hconn.isPreconnected q w hq hw
        (fun x hx => hzero (convexHull_subset_affineSpan _ (intrinsicInterior_subset hx)))
        (by
          intro x hx
          obtain ⟨s, hs, hspatch⟩ :=
            principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples_step2_flat_patch
              K hfin f hx
          refine ⟨s, hs, ?_⟩
          intro y hy
          have hyq := hzero ((Set.ext_iff.mp hspatch y).mp hy).1
          have hxq := hzero (convexHull_subset_affineSpan _ (intrinsicInterior_subset hx))
          simp only [inner_sub_right] at hxq hyq ⊢
          linarith)
        r hr (fun x hx => hzero ((Set.ext_iff.mp hpatch x).mp hx).1)
    have hcl : convexHull ℝ (f.val : Set (E d)) ⊆
        closure (connectedComponentIn K.spaceᶜ (q + (r / 2) • w)) := by
      rw [← hclosure]
      exact closure_minimal hrel isClosed_closure
    intro x hx
    exact ⟨hcl hx, fun hi =>
      (connectedComponentIn_subset _ _ (interior_subset hi))
        (K.convexHull_subset_space f.property.1 hx)⟩
  refine ⟨q + (r / 2) • v, q - (r / 2) • v, hsides, hreg, hcard, hfront v hv hplane, ?_⟩
  have hnplane : (affineSpan ℝ (f.val : Set (E d)) : Set (E d)) =
      {x | inner ℝ (-v) (x - q) = 0} := by
    simpa only [inner_neg_left, neg_eq_zero] using hplane
  simpa only [smul_neg, sub_eq_add_neg] using hfront (-v) (by simpa using hv) hnplane

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport` (V4 1.24):
"a connected union of facets". A simplex meeting the relative interior of a
face contains that face. This is the face-incidence property of a geometric
simplicial complex, with no assertion about its complement. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step1_interior_incidence
    (K : Geometry.SimplicialComplex ℝ (E d)) {s t : Finset (E d)}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) {x : E d}
    (hx : x ∈ relint (convexHull ℝ (s : Set (E d))))
    (hxt : x ∈ convexHull ℝ (t : Set (E d))) : s ⊆ t := by
  classical
  have hxs : x ∈ convexHull ℝ (s : Set (E d)) := intrinsicInterior_subset hx
  have hxst : x ∈ convexHull ℝ ((s ∩ t : Finset (E d)) : Set (E d)) := by
    simpa only [Finset.coe_inter] using K.inter_subset_convexHull hs ht ⟨hxs, hxt⟩
  obtain ⟨u, hsu, hu, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top (K.indep hs)
  let b : AffineBasis u ℝ (E d) := ⟨(↑), hu, by simpa using hspan⟩
  intro y hys
  by_contra hyt
  let i : u := ⟨y, hsu hys⟩
  have hpos : ∀ z ∈ convexHull ℝ (s : Set (E d)), 0 ≤ b.coord i z := by
    apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage (b.coord i))
    intro z hz
    let j : u := ⟨z, hsu hz⟩
    change 0 ≤ b.coord i (b j)
    rw [b.coord_apply]
    split_ifs <;> norm_num
  have hzero : ∀ z ∈ convexHull ℝ ((s ∩ t : Finset (E d)) : Set (E d)), b.coord i z = 0 := by
    apply convexHull_min _ ((convex_singleton (0 : ℝ)).affine_preimage (b.coord i))
    intro z hz
    have hzs : z ∈ s := (Finset.mem_inter.mp hz).1
    have hzt : z ∈ t := (Finset.mem_inter.mp hz).2
    let j : u := ⟨z, hsu hzs⟩
    have hij : i ≠ j := by
      intro hij
      have hyz : y = z := congrArg Subtype.val hij
      exact hyt (hyz.symm ▸ hzt)
    change b.coord i (b j) = 0
    exact b.coord_apply_ne hij
  have hx0 : b.coord i x = 0 := hzero x hxst
  have hy1 : b.coord i y = 1 := b.coord_apply_eq i
  rcases hx with ⟨x', hx', rfl⟩
  let H := affineSpan ℝ (convexHull ℝ (s : Set (E d)))
  have hyH : y ∈ H := subset_affineSpan ℝ _ (subset_convexHull ℝ _ hys)
  let L : ℝ → H := fun a =>
    ⟨AffineMap.lineMap (x' : E d) y a, AffineMap.lineMap_mem a x'.property hyH⟩
  have hLc : Continuous L := AffineMap.lineMap_continuous.subtype_mk _
  have hL0 : L 0 = x' := by
    apply Subtype.ext
    simp [L]
  have hnear : ∀ᶠ a in nhds (0 : ℝ),
      L a ∈ (Subtype.val ⁻¹' convexHull ℝ (s : Set (E d)) : Set H) := by
    apply hLc.continuousAt.eventually
    rw [hL0]
    exact mem_interior_iff_mem_nhds.mp hx'
  obtain ⟨a, ha, haC⟩ := hnear.exists_lt
  have hnonneg := hpos (L a) haC
  have heval : b.coord i (L a) = a := by
    change b.coord i (AffineMap.lineMap (x' : E d) y a) = a
    rw [AffineMap.apply_lineMap, hx0, hy1]
    simp [AffineMap.lineMap_apply_ring]
  rw [heval] at hnonneg
  exact (not_lt_of_ge hnonneg) ha

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport` (V4 1.24):
"each a closed hypersurface". The degree-two hypothesis identifies the complete
list of facets containing the common ridge; there are no other incident facets. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step2_ridge_star
    (K : Geometry.SimplicialComplex ℝ (E d))
    (hpure : ∀ f ∈ K.facets, f.card = d)
    (hridge : ∀ s ∈ K.faces, s.card = d - 1 → {f ∈ K.facets | s ⊆ f}.ncard = 2)
    (f g : K.facets) (hfg : (f.val ∩ g.val).card = d - 1) :
    {h ∈ K.facets | f.val ∩ g.val ⊆ h} = {f.val, g.val} := by
  classical
  have hd : 2 ≤ d := Fact.out
  have hne : (f.val ∩ g.val).Nonempty := Finset.card_pos.mp (by omega)
  have hs : f.val ∩ g.val ∈ K.faces :=
    K.down_closed f.property.1 Finset.inter_subset_left hne
  have hdiff : f.val ≠ g.val := by
    intro h
    have hc := hpure g.val g.property
    rw [h, Finset.inter_self, hc] at hfg
    omega
  have hcard := hridge _ hs hfg
  have hsub : ({f.val, g.val} : Set (Finset (E d))) ⊆
      {h ∈ K.facets | f.val ∩ g.val ⊆ h} := by
    intro h hh
    rcases Set.mem_insert_iff.mp hh with rfl | hh
    · exact ⟨f.property, Finset.inter_subset_left⟩
    · rw [Set.mem_singleton_iff] at hh
      subst h
      exact ⟨g.property, Finset.inter_subset_right⟩
  symm
  exact Set.eq_of_subset_of_ncard_le hsub (by simp [hcard, hdiff])
    (Set.finite_of_ncard_ne_zero (by omega))

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport` (V4 1.24):
"the complement locally is on the other side". At an interior point of the
common ridge, finiteness permits a ball avoiding every nonincident facet. Inside
that ball the complex is exactly the union of the two incident closed simplices. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step3_ridge_ball
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d)
    (hridge : ∀ s ∈ K.faces, s.card = d - 1 → {f ∈ K.facets | s ⊆ f}.ncard = 2)
    (f g : K.facets) (hfg : (f.val ∩ g.val).card = d - 1) :
    ∃ q ∈ relint (convexHull ℝ ((f.val ∩ g.val : Finset (E d)) : Set (E d))),
      ∃ r : ℝ, 0 < r ∧
        K.space ∩ Metric.ball q r =
          (convexHull ℝ (f.val : Set (E d)) ∪ convexHull ℝ (g.val : Set (E d))) ∩
            Metric.ball q r := by
  classical
  have hd : 2 ≤ d := Fact.out
  have hsne : (f.val ∩ g.val).Nonempty := Finset.card_pos.mp (by omega)
  have hs : f.val ∩ g.val ∈ K.faces :=
    K.down_closed f.property.1 Finset.inter_subset_left hsne
  have hSne : (convexHull ℝ ((f.val ∩ g.val : Finset (E d)) : Set (E d))).Nonempty :=
    convexHull_nonempty_iff.mpr (by obtain ⟨z, hz⟩ := hsne; exact ⟨z, hz⟩)
  obtain ⟨q, hq⟩ : (relint (convexHull ℝ ((f.val ∩ g.val : Finset (E d)) : Set (E d)))).Nonempty :=
    Set.Nonempty.intrinsicInterior (convex_convexHull _ _) hSne
  have hstar :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step2_ridge_star
      K hpure hridge f g hfg
  let bad := {h ∈ K.facets | h ≠ f.val ∧ h ≠ g.val}
  let T := ⋃ h ∈ bad, convexHull ℝ (h : Set (E d))
  have hbad : bad.Finite := hfin.subset (fun h hh => hh.1.1)
  have hclosed : IsClosed T := hbad.isClosed_biUnion
    (fun h _ => h.finite_toSet.isCompact_convexHull.isClosed)
  have hqT : q ∉ T := by
    intro hqT
    obtain ⟨h, hh, hqh⟩ := Set.mem_iUnion₂.mp hqT
    have hsh :=
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step1_interior_incidence
        K hs hh.1.1 hq hqh
    have hhstar : h ∈ {u ∈ K.facets | f.val ∩ g.val ⊆ u} := ⟨hh.1, hsh⟩
    rw [hstar, Set.mem_insert_iff, Set.mem_singleton_iff] at hhstar
    exact hhstar.elim hh.2.1 hh.2.2
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl q hqT
  refine ⟨q, hq, r, hr, ?_⟩
  ext x
  constructor
  · rintro ⟨hxK, hxr⟩
    rw [principal_component_step1_hull_geometry_step10_jordan_brouwer_step9_facets_cover K hfin] at hxK
    obtain ⟨h, hxh⟩ := Set.mem_iUnion.mp hxK
    refine ⟨?_, hxr⟩
    by_cases hhf : h.val = f.val
    · exact Or.inl (hhf ▸ hxh)
    by_cases hhg : h.val = g.val
    · exact Or.inr (hhg ▸ hxh)
    exact (hball hxr (Set.mem_iUnion₂.mpr ⟨h.val, ⟨h.property, hhf, hhg⟩, hxh⟩)).elim
  · rintro ⟨hxf | hxg, hxr⟩
    · exact ⟨K.convexHull_subset_space f.property.1 hxf, hxr⟩
    · exact ⟨K.convexHull_subset_space g.property.1 hxg, hxr⟩

/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport` (V4 1.24):
"has all its points adjacent to the same complementary component". Along one
flat simplex interior, the positive and negative normal collars are connected.
Each collar contains the prescribed sample and all sufficiently short normal
segments at every interior base point. No ridge or second facet is involved. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step4_facet_collars
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite) (f : K.facets)
    {q : E d} {r : ℝ} {v : E d}
    (hq : q ∈ relint (convexHull ℝ (f.val : Set (E d)))) (hr : 0 < r)
    (hv : ‖v‖ = 1)
    (hn : (affineSpan ℝ (f.val : Set (E d)) : Set (E d)) =
      {x | inner ℝ v (x - q) = 0})
    (hpatch : K.space ∩ Metric.ball q r =
      (affineSpan ℝ (f.val : Set (E d)) : Set (E d)) ∩ Metric.ball q r) :
    ∃ A B : Set (E d), IsPreconnected A ∧ IsPreconnected B ∧
      A ⊆ K.spaceᶜ ∧ B ⊆ K.spaceᶜ ∧
      q + (r / 2) • v ∈ A ∧ q - (r / 2) • v ∈ B ∧
      ∀ x ∈ relint (convexHull ℝ (f.val : Set (E d))),
        ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
          x + t • v ∈ A ∧ x - t • v ∈ B := by
  classical
  let C := convexHull ℝ (f.val : Set (E d))
  let S := relint C
  let H := affineSpan ℝ (f.val : Set (E d))
  have hSC : S ⊆ C := intrinsicInterior_subset
  have hSH : S ⊆ H := hSC.trans (convexHull_subset_affineSpan _)
  have hqC : q ∈ C := hSC hq
  have hqH : q ∈ H := hSH hq
  have hSc : Convex ℝ S := by
    let H' := affineSpan ℝ C
    let q' : H' := ⟨q, subset_affineSpan ℝ C hqC⟩
    letI : Nonempty H' := ⟨q'⟩
    let e := (AffineIsometryEquiv.constVSub ℝ q').symm
    let F : H'.direction →ᵃ[ℝ] E d := H'.subtype.comp e.toAffineEquiv.toAffineMap
    have hrep : F '' interior (F ⁻¹' C) = S := by
      change (Subtype.val ∘ e) '' interior ((Subtype.val ∘ e) ⁻¹' C) =
        Subtype.val '' interior (Subtype.val ⁻¹' C : Set H')
      rw [Set.preimage_comp, Set.image_comp]
      congr 1
      simpa only [AffineIsometryEquiv.coe_toHomeomorph] using
        (e.toHomeomorph.image_interior (e.toHomeomorph ⁻¹' (Subtype.val ⁻¹' C))).trans
          (congrArg interior (e.toHomeomorph.image_preimage (Subtype.val ⁻¹' C)))
    rw [← hrep]
    exact ((convex_convexHull ℝ (f.val : Set (E d))).affine_preimage F).interior.affine_image F
  let bad := {h ∈ K.facets | h ≠ f.val}
  let T := ⋃ h ∈ bad, convexHull ℝ (h : Set (E d))
  have hbad : bad.Finite := hfin.subset (fun h hh => hh.1.1)
  have hTc : IsClosed T := hbad.isClosed_biUnion
    (fun h _ => h.finite_toSet.isCompact_convexHull.isClosed)
  have hST : S ⊆ Tᶜ := by
    intro x hx hxT
    obtain ⟨h, hh, hxh⟩ := Set.mem_iUnion₂.mp hxT
    have hfh :=
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step1_interior_incidence
        K f.property.1 hh.1.1 hx hxh
    exact hh.2 (f.property.2 hh.1.1 hfh).symm
  have hcover : K.space ⊆ C ∪ T := by
    intro x hx
    rw [principal_component_step1_hull_geometry_step10_jordan_brouwer_step9_facets_cover K hfin] at hx
    obtain ⟨h, hxh⟩ := Set.mem_iUnion.mp hx
    by_cases hh : h.val = f.val
    · exact Or.inl (by change x ∈ convexHull ℝ (f.val : Set (E d)); simpa only [hh] using hxh)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨h.val, ⟨h.property, hh⟩, hxh⟩)
  have hside (w : E d) (hw : ‖w‖ = 1)
      (hnw : (H : Set (E d)) = {z | inner ℝ w (z - q) = 0}) :
      q + (r / 2) • w ∈ K.spaceᶜ ∧
        ∀ x ∈ S, ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
          x + t • w ∈ connectedComponentIn K.spaceᶜ (q + (r / 2) • w) := by
    have heval (y : E d) (hy : y ∈ H) (t : ℝ) :
        inner ℝ w ((y + t • w) - q) = t := by
      have hy0 : inner ℝ w (y - q) = 0 := (Set.ext_iff.mp hnw y).mp hy
      rw [show (y + t • w) - q = (y - q) + t • w by abel]
      simp [inner_add_right, inner_smul_right, hy0, hw]
    have hdist (y : E d) (t : ℝ) : dist (y + t • w) y = |t| := by
      simp [dist_eq_norm, norm_smul, hw, Real.norm_eq_abs]
    have hnear (t : ℝ) (ht : t ∈ Set.Ioo 0 r) : q + t • w ∈ K.spaceᶜ := by
      intro htK
      have htball : q + t • w ∈ Metric.ball q r := by
        rw [Metric.mem_ball, hdist, abs_of_pos ht.1]
        exact ht.2
      have htH : q + t • w ∈ H := by
        have hh : q + t • w ∈ K.space ∩ Metric.ball q r := ⟨htK, htball⟩
        rw [hpatch] at hh
        exact hh.1
      have hz : inner ℝ w ((q + t • w) - q) = 0 := (Set.ext_iff.mp hnw _).mp htH
      rw [heval q hqH t] at hz
      exact (ne_of_gt ht.1) hz
    refine ⟨hnear (r / 2) ⟨half_pos hr, half_lt_self hr⟩, ?_⟩
    intro x hx
    have hsegS : segment ℝ q x ⊆ S := hSc.segment_subset hq hx
    have hsegc : IsCompact (segment ℝ q x) := by
      rw [← convexHull_pair]
      exact ((Set.finite_singleton x).insert q).isCompact_convexHull
    obtain ⟨δ, hδ, hδT⟩ := hsegc.exists_thickening_subset_open hTc.isOpen_compl (hsegS.trans hST)
    refine ⟨min δ (r / 2), lt_min hδ (half_pos hr), ?_⟩
    intro t ht hte
    have htδ : t < δ := hte.trans_le (min_le_left _ _)
    have htr : t < r / 2 := hte.trans_le (min_le_right _ _)
    let I := (fun u : ℝ => q + u • w) '' Set.Icc t (r / 2)
    let J := (fun y : E d => y + t • w) '' segment ℝ q x
    have hIc : IsPreconnected I := isPreconnected_Icc.image _ (by fun_prop)
    have hJc : IsPreconnected J := (convex_segment (𝕜 := ℝ) q x).isPreconnected.image _ (by fun_prop)
    have hIK : I ⊆ K.spaceᶜ := by
      rintro z ⟨u, hu, rfl⟩
      exact hnear u ⟨ht.trans_le hu.1, hu.2.trans_lt (half_lt_self hr)⟩
    have hJK : J ⊆ K.spaceᶜ := by
      rintro z ⟨y, hy, rfl⟩ hzK
      rcases hcover hzK with hzC | hzT
      · have hzH : y + t • w ∈ H := convexHull_subset_affineSpan _ hzC
        have hz : inner ℝ w ((y + t • w) - q) = 0 := (Set.ext_iff.mp hnw _).mp hzH
        rw [heval y (hSH (hsegS hy)) t] at hz
        exact (ne_of_gt ht) hz
      · apply hδT (Metric.mem_thickening_iff.mpr ⟨y, hy, ?_⟩) hzT
        rw [hdist, abs_of_pos ht]
        exact htδ
    have hqI : q + t • w ∈ I :=
      Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr htr.le)
    have hqJ : q + t • w ∈ J := Set.mem_image_of_mem _ (left_mem_segment ℝ q x)
    have haI : q + (r / 2) • w ∈ I :=
      Set.mem_image_of_mem _ (Set.right_mem_Icc.mpr htr.le)
    have hxJ : x + t • w ∈ J := Set.mem_image_of_mem _ (right_mem_segment ℝ q x)
    exact (hIc.union (q + t • w) hqI hqJ hJc).subset_connectedComponentIn
      (Or.inl haI) (Set.union_subset hIK hJK) (Or.inr hxJ)
  obtain ⟨ha, hpos⟩ := hside v hv hn
  have hnegNormal : (H : Set (E d)) = {z | inner ℝ (-v) (z - q) = 0} := by
    simpa only [inner_neg_left, neg_eq_zero] using hn
  obtain ⟨hb, hneg⟩ := hside (-v) (by simpa using hv) hnegNormal
  have hminus (x : E d) (t : ℝ) : x + t • (-v) = x - t • v := by
    rw [smul_neg, sub_eq_add_neg]
  simp only [hminus] at hb hneg
  refine ⟨connectedComponentIn K.spaceᶜ (q + (r / 2) • v),
    connectedComponentIn K.spaceᶜ (q - (r / 2) • v),
    isPreconnected_connectedComponentIn, isPreconnected_connectedComponentIn,
    connectedComponentIn_subset _ _, connectedComponentIn_subset _ _,
    mem_connectedComponentIn ha, mem_connectedComponentIn hb, ?_⟩
  intro x hx
  obtain ⟨ε₁, hε₁, hp⟩ := hpos x hx
  obtain ⟨ε₂, hε₂, hm⟩ := hneg x hx
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro t ht hte
  exact ⟨hp t ht (hte.trans_le (min_le_left _ _)), hm t ht (hte.trans_le (min_le_right _ _))⟩

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport` (V4 1.24):
"the complement locally is on the other side". Put the two simplices in affine
halfspace coordinates. If their spans differ, each has just one vertex off the
ridge, so the normal of the other span has a constant strict sign on its
interior; orient both signs positively. The two independent normal forms also
have a common negative point arbitrarily close to the ridge. If the spans
coincide, use the same normal form twice. This certificate contains only affine
inequalities and interior points, with no connectedness or component assertion. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step5_affine_normal_form
    (f g : Finset (E d))
    (hif : AffineIndependent ℝ ((↑) : f → E d))
    (hig : AffineIndependent ℝ ((↑) : g → E d))
    (hcf : f.card = d) (hcg : g.card = d) (hfg : (f ∩ g).card = d - 1)
    (hinter : convexHull ℝ (f : Set (E d)) ∩ convexHull ℝ (g : Set (E d)) =
      convexHull ℝ ((f ∩ g : Finset (E d)) : Set (E d)))
    {q : E d} (hq : q ∈ relint (convexHull ℝ ((f ∩ g : Finset (E d)) : Set (E d))))
    {r : ℝ} (hr : 0 < r) {qf qg vf vg : E d}
    (hvf : ‖vf‖ = 1) (hvg : ‖vg‖ = 1)
    (hnf : (affineSpan ℝ (f : Set (E d)) : Set (E d)) =
      {x | inner ℝ vf (x - qf) = 0})
    (hng : (affineSpan ℝ (g : Set (E d)) : Set (E d)) =
      {x | inner ℝ vg (x - qg) = 0}) :
    ∃ xf ∈ relint (convexHull ℝ (f : Set (E d))),
      ∃ xg ∈ relint (convexHull ℝ (g : Set (E d))),
        xf ∈ Metric.ball q r ∧ xg ∈ Metric.ball q r ∧
        ∃ L M : E d →ᵃ[ℝ] ℝ,
          (∀ x ∈ convexHull ℝ (f : Set (E d)), L x = 0 ∧ 0 ≤ M x) ∧
          (∀ x ∈ convexHull ℝ (g : Set (E d)), M x = 0 ∧ 0 ≤ L x) ∧
          L.linear vf ≠ 0 ∧ M.linear vg ≠ 0 ∧
          (0 < M xf ∨ M = L) ∧ (0 < L xg ∨ L = M) ∧
          ∃ z ∈ Metric.ball q r, L z < 0 ∧ M z < 0 := by
  classical
  have relint_near (C : Set (E d)) (hC : Convex ℝ C) {q : E d} (hq : q ∈ C)
      {r : ℝ} (hr : 0 < r) : ∃ x ∈ relint C, x ∈ Metric.ball q r := by
    let H := affineSpan ℝ C
    let q' : H := ⟨q, subset_affineSpan ℝ C hq⟩
    letI : Nonempty H := ⟨q'⟩
    let e := (AffineIsometryEquiv.constVSub ℝ q').symm
    let F : H.direction →ᵃ[ℝ] E d := H.subtype.comp e.toAffineEquiv.toAffineMap
    have hrep : F '' interior (F ⁻¹' C) = relint C := by
      change (Subtype.val ∘ e) '' interior ((Subtype.val ∘ e) ⁻¹' C) =
        Subtype.val '' interior (Subtype.val ⁻¹' C : Set H)
      rw [Set.preimage_comp, Set.image_comp]
      congr 1
      simpa only [AffineIsometryEquiv.coe_toHomeomorph] using
        (e.toHomeomorph.image_interior (e.toHomeomorph ⁻¹' (Subtype.val ⁻¹' C))).trans
          (congrArg interior (e.toHomeomorph.image_preimage (Subtype.val ⁻¹' C)))
    have hSne : (relint C).Nonempty := Set.Nonempty.intrinsicInterior hC ⟨q, hq⟩
    rw [← hrep, Set.image_nonempty] at hSne
    have hcl := (hC.affine_preimage F).closure_interior_eq_closure_of_nonempty_interior hSne
    let y0 := e.symm q'
    have hy0 : F y0 = q := by
      change ((e (e.symm q') : H) : E d) = q
      simp [q']
    have hyC : y0 ∈ F ⁻¹' C := by change F y0 ∈ C; rwa [hy0]
    have hycl : y0 ∈ closure (interior (F ⁻¹' C)) := by rw [hcl]; exact subset_closure hyC
    obtain ⟨y, hyball, hyint⟩ := mem_closure_iff.mp hycl (F ⁻¹' Metric.ball q r)
      (Metric.isOpen_ball.preimage F.continuous_of_finiteDimensional)
      (by change F y0 ∈ Metric.ball q r; rw [hy0]; exact Metric.mem_ball_self hr)
    refine ⟨F y, ?_, hyball⟩
    rw [← hrep]
    exact Set.mem_image_of_mem F hyint
  have strict_sign (C : Set (E d)) (A : E d →ᵃ[ℝ] ℝ)
      (hA : ∀ z ∈ C, 0 ≤ A z) {x y : E d}
      (hx : x ∈ relint C) (hy : y ∈ C) (hyA : 0 < A y) : 0 < A x := by
    have hxA : 0 ≤ A x := hA x (intrinsicInterior_subset hx)
    by_contra hnx
    have hx0 : A x = 0 := le_antisymm (le_of_not_gt hnx) hxA
    rcases hx with ⟨x', hx', rfl⟩
    let H := affineSpan ℝ C
    have hyH : y ∈ H := subset_affineSpan ℝ _ hy
    let c : ℝ → H := fun t =>
      ⟨AffineMap.lineMap (x' : E d) y t, AffineMap.lineMap_mem t x'.property hyH⟩
    have hc : Continuous c := AffineMap.lineMap_continuous.subtype_mk _
    have hc0 : c 0 = x' := by apply Subtype.ext; simp [c]
    have hnear : ∀ᶠ t in nhds (0 : ℝ), c t ∈ (Subtype.val ⁻¹' C : Set H) := by
      apply hc.continuousAt.eventually
      rw [hc0]
      exact mem_interior_iff_mem_nhds.mp hx'
    obtain ⟨t, ht, htC⟩ := hnear.exists_lt
    have hnonneg := hA (c t) htC
    have heval : A (c t) = t * A y := by
      change A (AffineMap.lineMap (x' : E d) y t) = t * A y
      rw [AffineMap.apply_lineMap, hx0, AffineMap.lineMap_apply_ring]
      ring
    rw [heval] at hnonneg
    exact (not_lt_of_ge hnonneg) (mul_neg_of_neg_of_pos ht hyA)
  have hd : 2 ≤ d := Fact.out
  let Hf := affineSpan ℝ (f : Set (E d))
  let Hg := affineSpan ℝ (g : Set (E d))
  have hqfC : q ∈ convexHull ℝ (f : Set (E d)) :=
    convexHull_mono (fun x hx => (Finset.mem_inter.mp hx).1) (intrinsicInterior_subset hq)
  have hqgC : q ∈ convexHull ℝ (g : Set (E d)) :=
    convexHull_mono (fun x hx => (Finset.mem_inter.mp hx).2) (intrinsicInterior_subset hq)
  have hqfH : q ∈ Hf := convexHull_subset_affineSpan _ hqfC
  have hqgH : q ∈ Hg := convexHull_subset_affineSpan _ hqgC
  obtain ⟨xf, hxf, hxfb⟩ := relint_near _ (convex_convexHull ℝ _) hqfC hr
  obtain ⟨xg, hxg, hxgb⟩ := relint_near _ (convex_convexHull ℝ _) hqgC hr
  let N (v p : E d) : E d →ᵃ[ℝ] ℝ :=
    { toFun := fun x => inner ℝ v (x - p)
      linear := (innerSL ℝ v).toLinearMap
      map_vadd' := by
        intro x w
        change inner ℝ v ((w + x) - p) = inner ℝ v w + inner ℝ v (x - p)
        rw [add_sub_assoc, inner_add_right] }
  let A := N vf qf
  let B := N vg qg
  have hAf (x : E d) : x ∈ Hf ↔ A x = 0 := Set.ext_iff.mp hnf x
  have hBg (x : E d) : x ∈ Hg ↔ B x = 0 := Set.ext_iff.mp hng x
  have hAq : A q = 0 := (hAf q).mp hqfH
  have hBq : B q = 0 := (hBg q).mp hqgH
  have hAf0 : ∀ x ∈ convexHull ℝ (f : Set (E d)), A x = 0 :=
    fun x hx => (hAf x).mp (convexHull_subset_affineSpan _ hx)
  have hBg0 : ∀ x ∈ convexHull ℝ (g : Set (E d)), B x = 0 :=
    fun x hx => (hBg x).mp (convexHull_subset_affineSpan _ hx)
  have hAv : A.linear vf = 1 := by change inner ℝ vf vf = 1; simp [hvf]
  have hBv : B.linear vg = 1 := by change inner ℝ vg vg = 1; simp [hvg]
  have hadd (L : E d →ᵃ[ℝ] ℝ) (x y : E d) : L (x + y) = L x + L.linear y := by
    simpa [vadd_eq_add, add_comm] using L.map_vadd x y
  have hshift (L : E d →ᵃ[ℝ] ℝ) (w : E d) (t : ℝ) :
      L (q - t • w) = L q - t * L.linear w := by
    rw [sub_eq_add_neg, hadd, map_neg, map_smul]
    rfl
  have hsmall (w : E d) : ∃ t : ℝ, 0 < t ∧ q - t • w ∈ Metric.ball q r := by
    have hc : Continuous (fun t : ℝ => q - t • w) := by fun_prop
    have he : ∀ᶠ t in nhds (0 : ℝ), q - t • w ∈ Metric.ball q r :=
      hc.continuousAt.eventually (by simpa using Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
    exact he.exists_gt
  by_cases hplanes : Hf = Hg
  · have hAg0 : ∀ x ∈ convexHull ℝ (g : Set (E d)), A x = 0 := by
      intro x hx
      apply (hAf x).mp
      rw [hplanes]
      exact convexHull_subset_affineSpan _ hx
    have hAvg : A.linear vg ≠ 0 := by
      intro hzero
      have hmemf : q + vg ∈ Hf := (hAf _).mpr (by rw [hadd, hAq, hzero, add_zero])
      have hmemg : q + vg ∈ Hg := hplanes ▸ hmemf
      have hb := (hBg _).mp hmemg
      rw [hadd, hBq, hBv] at hb
      norm_num at hb
    obtain ⟨t, ht, htball⟩ := hsmall vf
    have hz : A (q - t • vf) < 0 := by rw [hshift, hAq, hAv]; linarith
    refine ⟨xf, hxf, xg, hxg, hxfb, hxgb, A, A, ?_, ?_, ?_, hAvg,
      Or.inr rfl, Or.inr rfl, q - t • vf, htball, hz, hz⟩
    · intro x hx
      simp [hAf0 x hx]
    · intro x hx
      simp [hAg0 x hx]
    · rw [hAv]
      norm_num
  · have hdim (s : Finset (E d)) (hi : AffineIndependent ℝ ((↑) : s → E d)) (hc : s.card = d) :
        Module.finrank ℝ (affineSpan ℝ (s : Set (E d))).direction = d - 1 := by
      have h := hi.finrank_vectorSpan (n := d - 1) (by simpa only [Fintype.card_coe, hc] using (show d = d - 1 + 1 by omega))
      have hrange : Set.range ((↑) : s → E d) = (s : Set (E d)) := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact y.property
        · intro hx
          exact ⟨⟨x, hx⟩, rfl⟩
      rw [hrange] at h
      rw [direction_affineSpan]
      exact h
    have heq (s t : Finset (E d)) (hi : AffineIndependent ℝ ((↑) : s → E d))
        (hj : AffineIndependent ℝ ((↑) : t → E d)) (hc : s.card = d) (hc' : t.card = d)
        (hle : affineSpan ℝ (s : Set (E d)) ≤ affineSpan ℝ (t : Set (E d))) :
        affineSpan ℝ (s : Set (E d)) = affineSpan ℝ (t : Set (E d)) := by
      have h := hi.affineSpan_eq_of_le_of_card_eq_finrank_add_one
        (sp := affineSpan ℝ (t : Set (E d))) (by simpa using hle)
        (by rw [hdim t hj hc']; simpa only [Fintype.card_coe, hc] using (show d = d - 1 + 1 by omega))
      simpa using h
    obtain ⟨pf, hpfset⟩ := Finset.card_eq_one.mp
      (show (f \ g).card = 1 by rw [Finset.card_sdiff, Finset.inter_comm g f, hcf, hfg]; omega)
    obtain ⟨pg, hpgset⟩ := Finset.card_eq_one.mp
      (show (g \ f).card = 1 by rw [Finset.card_sdiff, hcg, hfg]; omega)
    have hpf : pf ∈ f ∧ pf ∉ g := Finset.mem_sdiff.mp (by rw [hpfset]; simp)
    have hpg : pg ∈ g ∧ pg ∉ f := Finset.mem_sdiff.mp (by rw [hpgset]; simp)
    have hpfC : pf ∈ convexHull ℝ (f : Set (E d)) := subset_convexHull ℝ _ hpf.1
    have hpgC : pg ∈ convexHull ℝ (g : Set (E d)) := subset_convexHull ℝ _ hpg.1
    have hfp (x : E d) (hx : x ∈ f) (hxg : x ∉ g) : x = pf := by
      have h : x ∈ f \ g := Finset.mem_sdiff.mpr ⟨hx, hxg⟩
      rw [hpfset] at h
      exact Finset.mem_singleton.mp h
    have hgp (x : E d) (hx : x ∈ g) (hxf : x ∉ f) : x = pg := by
      have h : x ∈ g \ f := Finset.mem_sdiff.mpr ⟨hx, hxf⟩
      rw [hpgset] at h
      exact Finset.mem_singleton.mp h
    have hBpf : B pf ≠ 0 := by
      intro hz
      apply hplanes
      apply heq f g hif hig hcf hcg
      apply affineSpan_le.mpr
      intro x hx
      by_cases hxg : x ∈ g
      · exact subset_affineSpan ℝ _ hxg
      · rw [hfp x hx hxg]
        exact (hBg pf).mpr hz
    have hApg : A pg ≠ 0 := by
      intro hz
      apply hplanes
      symm
      apply heq g f hig hif hcg hcf
      apply affineSpan_le.mpr
      intro x hx
      by_cases hxf : x ∈ f
      · exact subset_affineSpan ℝ _ hxf
      · rw [hgp x hx hxf]
        exact (hAf pg).mpr hz
    let L := A pg • A
    let M := B pf • B
    have hLf0 : ∀ x ∈ convexHull ℝ (f : Set (E d)), L x = 0 := by
      intro x hx
      change A pg * A x = 0
      rw [hAf0 x hx, mul_zero]
    have hMg0 : ∀ x ∈ convexHull ℝ (g : Set (E d)), M x = 0 := by
      intro x hx
      change B pf * B x = 0
      rw [hBg0 x hx, mul_zero]
    have hLpg : 0 < L pg := by change 0 < A pg * A pg; exact mul_self_pos.mpr hApg
    have hMpf : 0 < M pf := by change 0 < B pf * B pf; exact mul_self_pos.mpr hBpf
    have hMf : ∀ x ∈ convexHull ℝ (f : Set (E d)), 0 ≤ M x := by
      apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage M)
      intro x hx
      by_cases hxg : x ∈ g
      · have hxB : B x = 0 := (hBg x).mp (subset_affineSpan ℝ _ hxg)
        change 0 ≤ B pf * B x
        rw [hxB, mul_zero]
      · rw [hfp x hx hxg]
        exact hMpf.le
    have hLg : ∀ x ∈ convexHull ℝ (g : Set (E d)), 0 ≤ L x := by
      apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage L)
      intro x hx
      by_cases hxf : x ∈ f
      · have hxA : A x = 0 := (hAf x).mp (subset_affineSpan ℝ _ hxf)
        change 0 ≤ A pg * A x
        rw [hxA, mul_zero]
      · rw [hgp x hx hxf]
        exact hLpg.le
    have hLvf : L.linear vf ≠ 0 := by
      change A pg * A.linear vf ≠ 0
      rwa [hAv, mul_one]
    have hMvg : M.linear vg ≠ 0 := by
      change B pf * B.linear vg ≠ 0
      rwa [hBv, mul_one]
    have hMxf : 0 < M xf := strict_sign _ M hMf hxf hpfC hMpf
    have hLxg : 0 < L xg := strict_sign _ L hLg hxg hpgC hLpg
    have hLq : L q = 0 := hLf0 q hqfC
    have hMq : M q = 0 := hMg0 q hqgC
    let w := (pf - q) + (pg - q)
    have hLw : L.linear w = L pg := by
      change L.linear ((pf - q) + (pg - q)) = L pg
      rw [map_add, ← vsub_eq_sub pf q, ← vsub_eq_sub pg q, L.linearMap_vsub, L.linearMap_vsub]
      simp [hLq, hLf0 pf hpfC]
    have hMw : M.linear w = M pf := by
      change M.linear ((pf - q) + (pg - q)) = M pf
      rw [map_add, ← vsub_eq_sub pf q, ← vsub_eq_sub pg q, M.linearMap_vsub, M.linearMap_vsub]
      simp [hMq, hMg0 pg hpgC]
    obtain ⟨t, ht, htb⟩ := hsmall w
    refine ⟨xf, hxf, xg, hxg, hxfb, hxgb, L, M,
      (fun x hx => ⟨hLf0 x hx, hMf x hx⟩), (fun x hx => ⟨hMg0 x hx, hLg x hx⟩),
      hLvf, hMvg, Or.inl hMxf, Or.inl hLxg, q - t • w, htb, ?_, ?_⟩
    · rw [hshift, hLq, hLw, zero_sub]
      exact neg_neg_of_pos (mul_pos ht hLpg)
    · rw [hshift, hMq, hMw, zero_sub]
      exact neg_neg_of_pos (mul_pos ht hMpf)

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport` (V4 1.24):
"the complement locally is on the other side". For just two simplices glued
along a ridge, a sufficiently small normal two dimensional disc has two sectors.
Thickening these sectors in ridge directions gives preconnected sets, each
containing one short normal ray from each simplex. The order of the rays at the
second simplex may be reversed. This is a local affine statement, independent
of any ambient complex or global complementary components. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step5_normal_sectors
    (f g : Finset (E d))
    (hif : AffineIndependent ℝ ((↑) : f → E d))
    (hig : AffineIndependent ℝ ((↑) : g → E d))
    (hcf : f.card = d) (hcg : g.card = d) (hfg : (f ∩ g).card = d - 1)
    (hinter : convexHull ℝ (f : Set (E d)) ∩ convexHull ℝ (g : Set (E d)) =
      convexHull ℝ ((f ∩ g : Finset (E d)) : Set (E d)))
    {q : E d} (hq : q ∈ relint (convexHull ℝ ((f ∩ g : Finset (E d)) : Set (E d))))
    {r : ℝ} (hr : 0 < r) {qf qg vf vg : E d}
    (hvf : ‖vf‖ = 1) (hvg : ‖vg‖ = 1)
    (hnf : (affineSpan ℝ (f : Set (E d)) : Set (E d)) =
      {x | inner ℝ vf (x - qf) = 0})
    (hng : (affineSpan ℝ (g : Set (E d)) : Set (E d)) =
      {x | inner ℝ vg (x - qg) = 0}) :
    ∃ xf ∈ relint (convexHull ℝ (f : Set (E d))),
      ∃ xg ∈ relint (convexHull ℝ (g : Set (E d))),
        ∃ ε : ℝ, 0 < ε ∧ ∃ U V : Set (E d),
          IsPreconnected U ∧ IsPreconnected V ∧
          U ⊆ Metric.ball q r \ (convexHull ℝ (f : Set (E d)) ∪ convexHull ℝ (g : Set (E d))) ∧
          V ⊆ Metric.ball q r \ (convexHull ℝ (f : Set (E d)) ∪ convexHull ℝ (g : Set (E d))) ∧
          (∀ t : ℝ, 0 < t → t < ε → xf + t • vf ∈ U ∧ xf - t • vf ∈ V) ∧
          ((∀ t : ℝ, 0 < t → t < ε → xg + t • vg ∈ U ∧ xg - t • vg ∈ V) ∨
            (∀ t : ℝ, 0 < t → t < ε → xg + t • vg ∈ V ∧ xg - t • vg ∈ U)) := by
  obtain ⟨xf, hxf, xg, hxg, hxfb, hxgb, L, M, hLf, hMg, hLv, hMv, hMf, hLg, z, hzb, hLz, hMz⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step5_affine_normal_form
      f g hif hig hcf hcg hfg hinter hq hr hvf hvg hnf hng
  let Pos (A B : E d →ᵃ[ℝ] ℝ) := Metric.ball q r ∩ {x | 0 < A x ∧ 0 < B x}
  let Neg (A B : E d →ᵃ[ℝ] ℝ) := Metric.ball q r ∩ {x | A x < 0 ∨ B x < 0}
  have hcross (A B : E d →ᵃ[ℝ] ℝ) (x w : E d)
      (hxb : x ∈ Metric.ball q r) (hAx : A x = 0)
      (hBx : 0 < B x ∨ B = A) (hw : A.linear w ≠ 0) :
      ∃ ε : ℝ, 0 < ε ∧
        ((∀ t : ℝ, 0 < t → t < ε → x + t • w ∈ Pos A B ∧ x - t • w ∈ Neg A B) ∨
          (∀ t : ℝ, 0 < t → t < ε → x + t • w ∈ Neg A B ∧ x - t • w ∈ Pos A B)) := by
    have hp : Continuous (fun t : ℝ => x + t • w) := by fun_prop
    have hm : Continuous (fun t : ℝ => x - t • w) := by fun_prop
    have hpb : ∀ᶠ t in nhds (0 : ℝ), x + t • w ∈ Metric.ball q r :=
      hp.continuousAt.eventually (by simpa using Metric.isOpen_ball.mem_nhds hxb)
    have hmb : ∀ᶠ t in nhds (0 : ℝ), x - t • w ∈ Metric.ball q r :=
      hm.continuousAt.eventually (by simpa using Metric.isOpen_ball.mem_nhds hxb)
    have hBn : ∀ᶠ t in nhds (0 : ℝ),
        (0 < B (x + t • w) ∧ 0 < B (x - t • w)) ∨ B = A := by
      rcases hBx with hBx | hBA
      · have hBp : ∀ᶠ t in nhds (0 : ℝ), 0 < B (x + t • w) :=
          (B.continuous_of_finiteDimensional.comp hp).continuousAt.eventually
            (by simpa using IsOpen.mem_nhds isOpen_Ioi hBx)
        have hBm : ∀ᶠ t in nhds (0 : ℝ), 0 < B (x - t • w) :=
          (B.continuous_of_finiteDimensional.comp hm).continuousAt.eventually
            (by simpa using IsOpen.mem_nhds isOpen_Ioi hBx)
        exact (hBp.and hBm).mono (fun _ h => Or.inl h)
      · exact Filter.Eventually.of_forall (fun _ => Or.inr hBA)
    obtain ⟨ε, hε, hnear⟩ := Metric.mem_nhds_iff.mp ((hpb.and hmb).and hBn)
    have hval (t : ℝ) : A (x + t • w) = t * A.linear w := by
      simpa [vadd_eq_add, add_comm, hAx] using A.map_vadd x (t • w)
    have hvalm (t : ℝ) : A (x - t • w) = -(t * A.linear w) := by
      simpa [sub_eq_add_neg, neg_smul] using hval (-t)
    have hnear' (t : ℝ) (ht : 0 < t) (hte : t < ε) :=
      hnear (show t ∈ Metric.ball (0 : ℝ) ε by simpa [Real.dist_eq, abs_of_pos ht] using hte)
    refine ⟨ε, hε, ?_⟩
    rcases lt_or_gt_of_ne hw with hw | hw
    · right
      intro t ht hte
      obtain ⟨⟨hpt, hmt⟩, hBt⟩ := hnear' t ht hte
      have hAp : A (x + t • w) < 0 := by rw [hval]; exact mul_neg_of_pos_of_neg ht hw
      have hAm : 0 < A (x - t • w) := by rw [hvalm]; exact neg_pos.mpr (mul_neg_of_pos_of_neg ht hw)
      refine ⟨⟨hpt, Or.inl hAp⟩, ⟨hmt, hAm, ?_⟩⟩
      rcases hBt with hBt | rfl
      · exact hBt.2
      · exact hAm
    · left
      intro t ht hte
      obtain ⟨⟨hpt, hmt⟩, hBt⟩ := hnear' t ht hte
      have hAp : 0 < A (x + t • w) := by rw [hval]; exact mul_pos ht hw
      have hAm : A (x - t • w) < 0 := by rw [hvalm]; exact neg_neg_of_pos (mul_pos ht hw)
      refine ⟨⟨hpt, hAp, ?_⟩, ⟨hmt, Or.inl hAm⟩⟩
      rcases hBt with hBt | rfl
      · exact hBt.1
      · exact hAp
  have hPc : IsPreconnected (Pos L M) :=
    ((convex_ball q r).inter (((convex_Ioi (0 : ℝ)).affine_preimage L).inter
      ((convex_Ioi (0 : ℝ)).affine_preimage M))).isPreconnected
  have hNc : IsPreconnected (Neg L M) := by
    have hNL : IsPreconnected (Metric.ball q r ∩ {x | L x < 0}) :=
      ((convex_ball q r).inter ((convex_Iio (0 : ℝ)).affine_preimage L)).isPreconnected
    have hNM : IsPreconnected (Metric.ball q r ∩ {x | M x < 0}) :=
      ((convex_ball q r).inter ((convex_Iio (0 : ℝ)).affine_preimage M)).isPreconnected
    have heq : Neg L M = (Metric.ball q r ∩ {x | L x < 0}) ∪
        (Metric.ball q r ∩ {x | M x < 0}) := by
      ext x
      simp only [Neg, Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq]
      tauto
    rw [heq]
    exact hNL.union z ⟨hzb, hLz⟩ ⟨hzb, hMz⟩ hNM
  have hPsub : Pos L M ⊆ Metric.ball q r \
      (convexHull ℝ (f : Set (E d)) ∪ convexHull ℝ (g : Set (E d))) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    rintro (hxf | hxg)
    · exact (ne_of_gt hx.2.1) (hLf x hxf).1
    · exact (ne_of_gt hx.2.2) (hMg x hxg).1
  have hNsub : Neg L M ⊆ Metric.ball q r \
      (convexHull ℝ (f : Set (E d)) ∪ convexHull ℝ (g : Set (E d))) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    rintro (hxf | hxg)
    · obtain ⟨hL0, hM0⟩ := hLf x hxf
      exact hx.2.elim (by intro h; linarith) (not_lt_of_ge hM0)
    · obtain ⟨hM0, hL0⟩ := hMg x hxg
      exact hx.2.elim (not_lt_of_ge hL0) (by intro h; linarith)
  obtain ⟨εf, hεf, hf⟩ := hcross L M xf vf hxfb (hLf xf (intrinsicInterior_subset hxf)).1 hMf hLv
  obtain ⟨εg, hεg, hg⟩ := hcross M L xg vg hxgb (hMg xg (intrinsicInterior_subset hxg)).1 hLg hMv
  have hPsym : Pos M L = Pos L M := by ext x; simp [Pos, and_comm]
  have hNsym : Neg M L = Neg L M := by ext x; simp [Neg, or_comm]
  rw [hPsym, hNsym] at hg
  let ε := min εf εg
  have hε : 0 < ε := lt_min hεf hεg
  rcases hf with hf | hf
  · refine ⟨xf, hxf, xg, hxg, ε, hε, Pos L M, Neg L M, hPc, hNc, hPsub, hNsub, ?_, ?_⟩
    · exact fun t ht hte => hf t ht (hte.trans_le (min_le_left _ _))
    · rcases hg with hg | hg
      · exact Or.inl (fun t ht hte => hg t ht (hte.trans_le (min_le_right _ _)))
      · exact Or.inr (fun t ht hte => hg t ht (hte.trans_le (min_le_right _ _)))
  · refine ⟨xf, hxf, xg, hxg, ε, hε, Neg L M, Pos L M, hNc, hPc, hNsub, hPsub, ?_, ?_⟩
    · exact fun t ht hte => hf t ht (hte.trans_le (min_le_left _ _))
    · rcases hg with hg | hg
      · exact Or.inr (fun t ht hte => hg t ht (hte.trans_le (min_le_right _ _)))
      · exact Or.inl (fun t ht hte => hg t ht (hte.trans_le (min_le_right _ _)))

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport` (V4 1.24):
"a connected component of a finite union of closed connected sets contains every
member it meets". Two points of any preconnected subset of the complement
belong to the same complementary component. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step6_component_eq
    {C T : Set (E d)} (hT : IsPreconnected T) (hTC : T ⊆ C)
    {x y : E d} (hx : x ∈ T) (hy : y ∈ T) :
    connectedComponentIn C x = connectedComponentIn C y := by
  exact connectedComponentIn_eq (hT.subset_connectedComponentIn hx hTC hy)

/-- Step 16 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"has all its points adjacent to the same complementary component". Across one
ridge incident to exactly two facets, a small normal two dimensional disc has two
sectors. Each sector joins one normal sample from each facet. Thus the unordered
pair of complementary components is unchanged across this one ridge. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d)
    (hridge : ∀ s ∈ K.faces, s.card = d - 1 → {f ∈ K.facets | s ⊆ f}.ncard = 2)
    (f g : K.facets) (hfg : (f.val ∩ g.val).card = d - 1)
    {a b c e : E d}
    (hf : principal_component_step1_hull_geometry_step10_jordan_brouwer_step14_FacetSides K f.val a b)
    (hg : principal_component_step1_hull_geometry_step10_jordan_brouwer_step14_FacetSides K g.val c e) :
    ({connectedComponentIn K.spaceᶜ a, connectedComponentIn K.spaceᶜ b} : Set (Set (E d))) =
      {connectedComponentIn K.spaceᶜ c, connectedComponentIn K.spaceᶜ e} := by
  rcases hf with ⟨qf, rf, vf, hqf, hrf, hvf, hnf, hpf, rfl, rfl⟩
  rcases hg with ⟨qg, rg, vg, hqg, hrg, hvg, hng, hpg, rfl, rfl⟩
  obtain ⟨A, B, hAc, hBc, hAK, hBK, ha, hb, hfab⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step4_facet_collars
      K hfin f hqf hrf hvf hnf hpf
  obtain ⟨D, F, hDc, hFc, hDK, hFK, hc, he, hgce⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step4_facet_collars
      K hfin g hqg hrg hvg hng hpg
  obtain ⟨q, hq, r, hr, hball⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step3_ridge_ball
      K hfin hpure hridge f g hfg
  obtain ⟨xf, hxf, xg, hxg, ε, hε, U, V, hUc, hVc, hU, hV, hfUV, hgUV⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step5_normal_sectors
      f.val g.val (K.indep f.property.1) (K.indep g.property.1)
      (hpure f.val f.property) (hpure g.val g.property) hfg
      (by simpa only [Finset.coe_inter] using K.convexHull_inter_convexHull f.property.1 g.property.1)
      hq hr hvf hvg hnf hng
  have hlocal : Metric.ball q r \
      (convexHull ℝ (f.val : Set (E d)) ∪ convexHull ℝ (g.val : Set (E d))) ⊆ K.spaceᶜ := by
    intro x hx hxK
    have hx' : x ∈ K.space ∩ Metric.ball q r := ⟨hxK, hx.1⟩
    rw [hball] at hx'
    exact hx.2 hx'.1
  have hUK := hU.trans hlocal
  have hVK := hV.trans hlocal
  obtain ⟨δf, hδf, hδfab⟩ := hfab xf hxf
  obtain ⟨δg, hδg, hδgce⟩ := hgce xg hxg
  let tf := min ε δf / 2
  let tg := min ε δg / 2
  have htf : 0 < tf := half_pos (lt_min hε hδf)
  have htg : 0 < tg := half_pos (lt_min hε hδg)
  have htfe : tf < ε := (half_lt_self (lt_min hε hδf)).trans_le (min_le_left _ _)
  have htfd : tf < δf := (half_lt_self (lt_min hε hδf)).trans_le (min_le_right _ _)
  have htge : tg < ε := (half_lt_self (lt_min hε hδg)).trans_le (min_le_left _ _)
  have htgd : tg < δg := (half_lt_self (lt_min hε hδg)).trans_le (min_le_right _ _)
  have hab := hδfab tf htf htfd
  have hce := hδgce tg htg htgd
  have hfUV' := hfUV tf htf htfe
  have ha' :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step6_component_eq
      hAc hAK ha hab.1
  have hb' :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step6_component_eq
      hBc hBK hb hab.2
  have hc' :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step6_component_eq
      hDc hDK hc hce.1
  have he' :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step6_component_eq
      hFc hFK he hce.2
  rcases hgUV with hgUV | hgVU
  · have hgUV' := hgUV tg htg htge
    have hac := ha'.trans ((
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step6_component_eq
        hUc hUK hfUV'.1 hgUV'.1).trans hc'.symm)
    have hbe := hb'.trans ((
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step6_component_eq
        hVc hVK hfUV'.2 hgUV'.2).trans he'.symm)
    rw [hac, hbe]
  · have hgVU' := hgVU tg htg htge
    have hae := ha'.trans ((
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step6_component_eq
        hUc hUK hfUV'.1 hgVU'.2).trans he'.symm)
    have hbc := hb'.trans ((
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step6_component_eq
        hVc hVK hfUV'.2 hgVU'.1).trans hc'.symm)
    rw [hae, hbc, Set.pair_comm]

open scoped Topology in
/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet` (V4 1.24):
"a connected union of facets". A point on the relative boundary of a simplex
lies in the convex hull of a proper subset of its vertices; use a vanishing
barycentric coordinate. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step1_simplex_boundary (s : Finset (E d))
    (hs : AffineIndependent ℝ ((↑) : s → E d)) {z : E d}
    (hz : z ∈ convexHull ℝ (s : Set (E d)))
    (hzi : z ∉ relint (convexHull ℝ (s : Set (E d)))) :
    ∃ t : Finset (E d), t ⊂ s ∧ z ∈ convexHull ℝ (t : Set (E d)) := by
  classical
  obtain ⟨t, hst, ht, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hs
  let b : AffineBasis t ℝ (E d) := ⟨(↑), ht, by simpa using hspan⟩
  letI : Finite t := finite_of_fin_dim_affineIndependent ℝ ht
  letI : Fintype t := Fintype.ofFinite t
  have hnonneg (i : t) : 0 ≤ b.coord i z := by
    apply convexHull_min (t := {w | 0 ≤ b.coord i w}) ?_
      ((convex_Ici (0 : ℝ)).affine_preimage (b.coord i)) hz
    intro w hw
    let j : t := ⟨w, hst hw⟩
    change 0 ≤ b.coord i (b j)
    simp only [b.coord_apply]
    split_ifs <;> norm_num
  have hzero (i : t) (hi : (i : E d) ∉ s) {w : E d}
      (hw : w ∈ affineSpan ℝ (s : Set (E d))) : b.coord i w = 0 := by
    have heq : Set.EqOn (b.coord i) (AffineMap.const ℝ (E d) (0 : ℝ)) (s : Set (E d)) := by
      intro p hp
      let j : t := ⟨p, hst hp⟩
      have hij : i ≠ j := by intro hh; exact hi (by simpa [hh, j] using hp)
      change b.coord i (b j) = 0
      exact b.coord_apply_ne hij
    exact AffineMap.eqOn_affineSpan heq hw
  have hmem (u : Finset (E d)) (w : E d)
      (hwpos : ∀ i : t, 0 ≤ b.coord i w)
      (hwzero : ∀ i : t, (i : E d) ∉ u → b.coord i w = 0) :
      w ∈ convexHull ℝ (u : Set (E d)) := by
    let I : Finset t := Finset.univ.filter fun i => (i : E d) ∈ u
    have hsum : ∑ i ∈ I, b.coord i w = 1 := by
      rw [← b.sum_coord_apply_eq_one w]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      exact hwzero i (by simpa [I] using hi)
    have hsumv : ∑ i ∈ I, b.coord i w • b i = w := by
      calc
        _ = ∑ i, b.coord i w • b i := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          rw [hwzero i (by simpa [I] using hi), zero_smul]
        _ = w := b.linear_combination_coord_eq_self w
    rw [← hsumv]
    apply (convex_convexHull ℝ (u : Set (E d))).sum_mem (fun i _ => hwpos i) hsum
    intro i hi
    exact subset_convexHull ℝ (u : Set (E d)) (Finset.mem_filter.mp hi).2
  by_cases hpos : ∀ i : t, (i : E d) ∈ s → 0 < b.coord i z
  · exfalso
    apply hzi
    let A := affineSpan ℝ (convexHull ℝ (s : Set (E d)))
    let zA : A := ⟨z, subset_affineSpan ℝ _ hz⟩
    let U : Set (E d) := {w | ∀ i : t, (i : E d) ∈ s → 0 < b.coord i w}
    have hU : IsOpen U := by
      simp only [U, Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun _ =>
        isOpen_lt continuous_const (b.coord i).continuous_of_finiteDimensional
    refine mem_intrinsicInterior.mpr ⟨zA, ?_, rfl⟩
    apply mem_interior_iff_mem_nhds.mpr
    have hzU : zA ∈ (Subtype.val ⁻¹' U : Set A) := hpos
    have hUnh : (Subtype.val ⁻¹' U : Set A) ∈ 𝓝 zA :=
      (hU.preimage continuous_subtype_val).mem_nhds hzU
    apply Filter.mem_of_superset hUnh
    intro w hw
    have hwA : (w : E d) ∈ affineSpan ℝ (s : Set (E d)) := by
      have hh := w.property
      simpa [A, affineSpan_convexHull] using hh
    apply hmem s w
    · intro i
      by_cases hi : (i : E d) ∈ s
      · exact (hw i hi).le
      · rw [hzero i hi hwA]
    · intro i hi
      exact hzero i hi hwA
  · push_neg at hpos
    obtain ⟨i, hi, hle⟩ := hpos
    have hizero : b.coord i z = 0 := le_antisymm hle (hnonneg i)
    refine ⟨s.erase (i : E d), Finset.erase_ssubset hi, hmem _ _ hnonneg ?_⟩
    intro j hj
    by_cases hji : j = i
    · simpa [hji] using hizero
    · apply hzero j
      · intro hjs
        apply hj
        exact Finset.mem_erase.mpr ⟨(Subtype.coe_injective.ne hji), hjs⟩
      · exact convexHull_subset_affineSpan _ hz

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet` (V4 1.24):
"a connected union of facets". Outside the affine spans of the faces with
fewer than `d` vertices, every point of the complex is in a facet interior. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step2_lower_skeleton (K : Geometry.SimplicialComplex ℝ (E d))
    (hfin : K.faces.Finite) (hpure : ∀ f ∈ K.facets, f.card = d)
    {z : E d} (hz : z ∈ K.space)
    (havoid : ∀ s ∈ K.faces, s.card < d →
      z ∉ (affineSpan ℝ (s : Set (E d)) : Set (E d))) :
    ∃ f : K.facets, z ∈ relint (convexHull ℝ (f.val : Set (E d))) := by
  classical
  rw [principal_component_step1_hull_geometry_step10_jordan_brouwer_step9_facets_cover K hfin] at hz
  obtain ⟨f, hzf⟩ := Set.mem_iUnion.mp hz
  refine ⟨f, ?_⟩
  by_contra hzi
  obtain ⟨t, htf, hzt⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step1_simplex_boundary f.val (K.indep f.property.1) hzf hzi
  have htne : t.Nonempty := by
    exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨z, hzt⟩)
  exact havoid t (K.down_closed f.property.1 htf.1 htne)
    (by simpa [hpure f.val f.property] using Finset.card_lt_card htf)
    (convexHull_subset_affineSpan _ hzt)

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet` (V4 1.24):
"in general position". Choose the initial point in any prescribed nonempty
open set, avoiding the finitely many affine spans obtained by adjoining the fixed
endpoint to a lower dimensional face. The segment then avoids those faces away
from its endpoint. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step3_generic_segment (T : Set (Finset (E d))) (hT : T.Finite)
    (hcard : ∀ s ∈ T, s.card < d) {U : Set (E d)}
    (hU : IsOpen U) (hne : U.Nonempty) (q : E d) :
    ∃ y ∈ U, ∀ s ∈ T, ∀ z ∈ segment ℝ y q, z ≠ q →
      z ∉ (affineSpan ℝ (s : Set (E d)) : Set (E d)) := by
  classical
  let A (s : Finset (E d)) := affineSpan ℝ (insert q (s : Set (E d)))
  have hproper (s : Finset (E d)) (hs : s ∈ T) : A s ≠ ⊤ := by
    let t := insert q s
    haveI : Nonempty t := (Finset.insert_nonempty q s).to_subtype
    have htpos : 1 ≤ t.card := Finset.card_pos.mpr (Finset.insert_nonempty q s)
    have hdim : Module.finrank ℝ (vectorSpan ℝ (t : Set (E d))) ≤ t.card - 1 := by
      have hh := finrank_vectorSpan_image_finset_le ℝ (fun w : E d => w) t
        (Nat.sub_add_cancel htpos).symm
      have himage : vectorSpan ℝ ((t.image (fun w : E d => w)) : Set (E d)) =
          vectorSpan ℝ (t : Set (E d)) := by rw [Finset.image_id']
      have hrank := congrArg (fun p : Submodule ℝ (E d) => Module.finrank ℝ p) himage
      exact hrank.symm.le.trans hh
    intro htop
    have hdir : vectorSpan ℝ (t : Set (E d)) = ⊤ := by
      have hh := congrArg AffineSubspace.direction htop
      simpa [A, t, Finset.coe_insert, direction_affineSpan] using hh
    rw [hdir, finrank_top, finrank_euclideanSpace, Fintype.card_fin] at hdim
    have hle : t.card ≤ s.card + 1 := Finset.card_insert_le _ _
    have := hcard s hs
    omega
  have hdense (s : Finset (E d)) (hs : s ∈ T) : Dense ((A s : Set (E d))ᶜ) := by
    apply interior_eq_empty_iff_dense_compl.mp
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    apply hproper s hs
    apply top_unique
    rw [← isOpen_interior.affineSpan_eq_top ⟨p, hp⟩]
    exact affineSpan_le.mpr interior_subset
  have hd : Dense (⋂ s ∈ T, (A s : Set (E d))ᶜ) :=
    dense_biInter_of_isOpen (fun s _ => (A s).closed_of_finiteDimensional.isOpen_compl)
      hT.countable hdense
  obtain ⟨y, hyU, hy⟩ := hd.inter_open_nonempty U hU hne
  refine ⟨y, hyU, ?_⟩
  intro s hs z hz hzq hzspan
  apply Set.mem_iInter₂.mp hy s hs
  have hqA : q ∈ A s := subset_affineSpan ℝ _ (Set.mem_insert q _)
  have hzA : z ∈ A s := affineSpan_mono ℝ (Set.subset_insert q _) hzspan
  rw [segment_symm, segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have htne : t ≠ 0 := by intro he; apply hzq; simp [he]
  have h := AffineMap.lineMap_mem t⁻¹ hqA hzA
  simpa [AffineMap.lineMap_lineMap_right, htne] using h

/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet` (V4 1.24):
"its frontier ... is nonempty". A visible point of a closed obstacle is a
limit of the complementary component containing the initial point: the half-open
segment stays in that component. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step4_visible_closure {Γ : Set (E d)} {y z : E d}
    (hy : y ∉ Γ) (hz : z ∈ Γ) (hvis : IsVisible ℝ Γ y z) :
    z ∈ closure (connectedComponentIn Γᶜ y) := by
  have hyz : y ≠ z := by rintro rfl; exact hy hz
  let L : ℝ →ᵃ[ℝ] E d := AffineMap.lineMap y z
  let C := L '' Ico (0 : ℝ) 1
  have hC : IsPreconnected C :=
    (convex_Ico (0 : ℝ) 1).isPreconnected.image L L.continuous_of_finiteDimensional.continuousOn
  have hyC : y ∈ C := ⟨0, ⟨le_rfl, zero_lt_one⟩, by simp [L]⟩
  have hCΓ : C ⊆ Γᶜ := by
    rintro p ⟨t, ht, rfl⟩
    by_cases ht0 : t = 0
    · simpa [L, ht0] using hy
    · exact (isVisible_iff_lineMap hyz).mp hvis t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
  have hsub := hC.subset_connectedComponentIn hyC hCΓ
  apply closure_mono hsub
  have hopen : openSegment ℝ y z ⊆ C := by
    rw [openSegment_eq_image_lineMap]
    exact Set.image_mono Ioo_subset_Ico_self
  exact closure_mono hopen (segment_subset_closure_openSegment (right_mem_segment ℝ y z))

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet` (V4 1.24):
"its frontier ... is nonempty". Perturb the initial point inside its open
complementary component and take the first contact along a generic segment to
the complex. The contact lies in a facet interior. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step5_facet_access (K : Geometry.SimplicialComplex ℝ (E d))
    (hfin : K.faces.Finite) (hpure : ∀ f ∈ K.facets, f.card = d)
    {q : E d} (hq : ∃ f : K.facets, q ∈ relint (convexHull ℝ (f.val : Set (E d))))
    {x : E d} (hx : x ∉ K.space) :
    ∃ (f : K.facets) (z : E d), z ∈ relint (convexHull ℝ (f.val : Set (E d))) ∧
      z ∈ closure (connectedComponentIn K.spaceᶜ x) := by
  have hclosed : IsClosed K.space := hfin.isClosed_biUnion fun s _ =>
    s.finite_toSet.isCompact_convexHull.isClosed
  let U := connectedComponentIn K.spaceᶜ x
  obtain ⟨y, hy, havoid⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step3_generic_segment {s ∈ K.faces | s.card < d}
    (hfin.subset (by intro s hs; exact hs.1)) (fun _ hs => hs.2)
    hclosed.isOpen_compl.connectedComponentIn ⟨x, mem_connectedComponentIn hx⟩ q
  have hyK : y ∉ K.space := connectedComponentIn_subset _ _ hy
  have hqK : q ∈ K.space := by
    obtain ⟨f, hf⟩ := hq
    exact K.convexHull_subset_space f.property.1 (intrinsicInterior_subset hf)
  obtain ⟨z, hzK, hzseg, hvis⟩ := hclosed.exists_wbtw_isVisible hqK y
  have hzri : ∃ f : K.facets, z ∈ relint (convexHull ℝ (f.val : Set (E d))) := by
    by_cases hzq : z = q
    · simpa [hzq] using hq
    · apply principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step2_lower_skeleton K hfin hpure hzK
      intro s hs hcard
      exact havoid s ⟨hs, hcard⟩ z hzseg.mem_segment hzq
  obtain ⟨f, hzf⟩ := hzri
  refine ⟨f, z, hzf, ?_⟩
  rw [connectedComponentIn_eq hy]
  exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step4_visible_closure hyK hzK hvis

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet` (V4 1.24):
"a connected polyhedral set". The relative interior of a convex set is
convex. Translate its affine span to its direction space and use convexity of
the ordinary interior there. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step6_convex_relint {C : Set (E d)} (hC : Convex ℝ C) : Convex ℝ (relint C) := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
  · simpa [relint] using (convex_empty : Convex ℝ (∅ : Set (E d)))
  let A := affineSpan ℝ C
  let qA : A := ⟨q, subset_affineSpan ℝ C hq⟩
  letI : Nonempty A := ⟨qA⟩
  let e := AffineIsometryEquiv.vaddConst ℝ qA
  let F : A.direction →ᵃ[ℝ] E d := A.subtype.comp e.toAffineEquiv.toAffineMap
  have hrepr : F '' interior (F ⁻¹' C) = relint C := by
    change F '' interior (F ⁻¹' C) = Subtype.val '' interior (Subtype.val ⁻¹' C : Set A)
    calc
      _ = (Subtype.val : A → E d) ''
          (e '' interior (e ⁻¹' (Subtype.val ⁻¹' C : Set A))) :=
        (Set.image_image _ _ _).symm
      _ = Subtype.val '' interior (Subtype.val ⁻¹' C : Set A) := by
        have he : e '' interior (e ⁻¹' (Subtype.val ⁻¹' C : Set A)) =
            interior (Subtype.val ⁻¹' C : Set A) := by
          have hh := (e.toHomeomorph.image_interior
            (e.toHomeomorph ⁻¹' (Subtype.val ⁻¹' C : Set A))).trans
            (congrArg interior (e.toHomeomorph.surjective.image_preimage
              (Subtype.val ⁻¹' C : Set A)))
          simpa only [AffineIsometryEquiv.coe_toHomeomorph] using hh
        exact congrArg (fun W : Set A => (Subtype.val : A → E d) '' W) he
  rw [← hrepr]
  exact ((hC.affine_preimage F).interior).affine_image F

open scoped Topology in
/-- Step 7 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet` (V4 1.24):
"the complement locally is on the other side". An affine functional
nonnegative on a set and positive at one of its points is positive throughout
its relative interior; otherwise a short extension of a line gives a negative
value inside the set. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step7_relint_positive {C : Set (E d)} (l : E d →ᵃ[ℝ] ℝ)
    (hnonneg : ∀ p ∈ C, 0 ≤ l p) {v z : E d}
    (hv : v ∈ C) (hvpos : 0 < l v) (hz : z ∈ relint C) : 0 < l z := by
  obtain ⟨zA, hzA, rfl⟩ := mem_intrinsicInterior.mp hz
  have hzC : (zA : E d) ∈ C :=
    (show zA ∈ Subtype.val ⁻¹' C from interior_subset hzA)
  by_contra hn
  have hzero : l (zA : E d) = 0 := le_antisymm (le_of_not_gt hn) (hnonneg _ hzC)
  let L : ℝ → affineSpan ℝ C := fun t =>
    ⟨AffineMap.lineMap (zA : E d) v t,
      AffineMap.lineMap_mem t zA.property (subset_affineSpan ℝ C hv)⟩
  have hL : Continuous L := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, (L t : E d) ∈ C := by
    have ht : Filter.Tendsto L (𝓝 0) (𝓝 zA) := by simpa [L] using hL.tendsto 0
    exact ht (mem_interior_iff_mem_nhds.mp hzA)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hneg : (L (-ε / 2) : E d) ∈ C := hball (by
    simp only [Real.dist_eq, sub_zero, abs_div, abs_neg, abs_of_pos hε, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith)
  have hbad := hnonneg _ hneg
  change 0 ≤ l (AffineMap.lineMap (zA : E d) v (-ε / 2)) at hbad
  rw [l.apply_lineMap, AffineMap.lineMap_apply_ring, hzero] at hbad
  nlinarith

/-- Step 8 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet` (V4 1.24):
"the complement locally is on the other side". A simplex interior misses
every proper subface. A barycentric coordinate of an omitted vertex is positive
on that interior and vanishes on the subface. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step8_relint_disjoint_subface (s t : Finset (E d))
    (hs : AffineIndependent ℝ ((↑) : s → E d)) (ht : t ⊂ s) :
    Disjoint (relint (convexHull ℝ (s : Set (E d))))
      (convexHull ℝ (t : Set (E d))) := by
  classical
  obtain ⟨u, hsu, hu, huspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hs
  let b : AffineBasis u ℝ (E d) := ⟨(↑), hu, by simpa using huspan⟩
  obtain ⟨v, hvs, hvt⟩ := Finset.exists_of_ssubset ht
  let i : u := ⟨v, hsu hvs⟩
  have hnonneg : ∀ p ∈ convexHull ℝ (s : Set (E d)), 0 ≤ b.coord i p := by
    apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage (b.coord i))
    intro p hp
    let j : u := ⟨p, hsu hp⟩
    change 0 ≤ b.coord i (b j)
    simp only [b.coord_apply]
    split_ifs <;> norm_num
  have hzero : ∀ p ∈ convexHull ℝ (t : Set (E d)), b.coord i p = 0 := by
    apply convexHull_min ?_ ((convex_singleton (0 : ℝ)).affine_preimage (b.coord i))
    intro p hp
    let j : u := ⟨p, hsu (ht.1 hp)⟩
    have hij : i ≠ j := by
      intro he
      apply hvt
      have he' : v = p := congrArg Subtype.val he
      simpa [he'] using hp
    change b.coord i (b j) = 0
    exact b.coord_apply_ne hij
  apply Set.disjoint_left.mpr
  intro p hps hpt
  have hpos := principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step7_relint_positive (b.coord i) hnonneg (subset_convexHull ℝ _ hvs)
    (show 0 < b.coord i v by change 0 < b.coord i (b i); simp) hps
  exact (ne_of_gt hpos) (hzero p hpt)

/-- Step 9 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet` (V4 1.24):
"the complement locally is on the other side". A compact segment in one
facet interior has a uniformly thin neighborhood on which the complex agrees
with the facet affine span. Finiteness excludes the other faces. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step9_facet_tube (K : Geometry.SimplicialComplex ℝ (E d))
    (hfin : K.faces.Finite) (f : K.facets) {q z : E d}
    (hq : q ∈ relint (convexHull ℝ (f.val : Set (E d))))
    (hz : z ∈ relint (convexHull ℝ (f.val : Set (E d)))) :
    ∃ ε : ℝ, 0 < ε ∧
      K.space ∩ Metric.thickening ε (segment ℝ q z) =
        (affineSpan ℝ (f.val : Set (E d)) : Set (E d)) ∩
          Metric.thickening ε (segment ℝ q z) := by
  classical
  let C := convexHull ℝ (f.val : Set (E d))
  let A := affineSpan ℝ C
  let bad := K.faces \ {f.val}
  let B : Set (E d) := ⋃ g ∈ bad, convexHull ℝ (g : Set (E d))
  have hB : IsClosed B := (hfin.diff : bad.Finite).isClosed_biUnion fun g _ =>
    g.finite_toSet.isCompact_convexHull.isClosed
  have hdisj : Disjoint (relint C) B := by
    apply Set.disjoint_left.mpr
    intro p hp hpB
    obtain ⟨g, hg, hpg⟩ := Set.mem_iUnion₂.mp hpB
    have hsub : f.val ∩ g ⊂ f.val := by
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro hh
      exact hg.2 (f.property.2 hg.1 (hh.trans Finset.inter_subset_right)).symm
    have hpf : p ∈ convexHull ℝ (f.val : Set (E d)) := intrinsicInterior_subset hp
    have hpfg : p ∈ convexHull ℝ ((f.val ∩ g : Finset (E d)) : Set (E d)) := by
      simpa only [Finset.coe_inter] using K.inter_subset_convexHull f.property.1 hg.1 ⟨hpf, hpg⟩
    exact Set.disjoint_left.mp (principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step8_relint_disjoint_subface f.val _ (K.indep f.property.1) hsub) hp hpfg
  have hi : Topology.IsInducing (Subtype.val : A → E d) := .subtypeVal
  obtain ⟨U, hU, hUi⟩ := hi.isOpen_iff.mp
    (isOpen_interior : IsOpen (interior (Subtype.val ⁻¹' C : Set A)))
  have hriU : relint C ⊆ U := by
    rintro p ⟨w, hw, rfl⟩
    change w ∈ Subtype.val ⁻¹' U
    rwa [hUi]
  have hUri : U ∩ (A : Set (E d)) ⊆ C := by
    rintro p ⟨hpU, hpA⟩
    have hp : (⟨p, hpA⟩ : A) ∈ Subtype.val ⁻¹' U := hpU
    rw [hUi] at hp
    exact (show (⟨p, hpA⟩ : A) ∈ Subtype.val ⁻¹' C from interior_subset hp)
  have hseg : segment ℝ q z ⊆ U \ B := by
    intro p hp
    have hpri : p ∈ relint C :=
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step6_convex_relint (convex_convexHull ℝ (f.val : Set (E d)))).segment_subset hq hz hp
    exact ⟨hriU hpri, fun hpB => Set.disjoint_left.mp hdisj hpri hpB⟩
  have hcompact : IsCompact (segment ℝ q z) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨ε, hε, hεW⟩ := hcompact.exists_thickening_subset_open
    (hU.sdiff hB) hseg
  refine ⟨ε, hε, ?_⟩
  ext p
  constructor
  · rintro ⟨hpK, hpT⟩
    refine ⟨?_, hpT⟩
    obtain ⟨g, hg, hpg⟩ := K.mem_space_iff.mp hpK
    by_cases hgf : g = f.val
    · subst g
      exact convexHull_subset_affineSpan _ hpg
    · exact ((hεW hpT).2 (Set.mem_iUnion₂.mpr ⟨g, ⟨hg, hgf⟩, hpg⟩)).elim
  · rintro ⟨hpA, hpT⟩
    refine ⟨K.convexHull_subset_space f.property.1 (hUri ⟨(hεW hpT).1, ?_⟩), hpT⟩
    simpa [A, C, affineSpan_convexHull] using hpA

/-- Step 10 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet` (V4 1.24):
"the complement locally is on the other side". The positive half of a
convex neighborhood cut by an affine functional is connected and avoids an
obstacle contained in the zero hyperplane. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step10_positive_component {Γ U : Set (E d)} (hU : Convex ℝ U)
    (l : E d →ᵃ[ℝ] ℝ) (hzero : ∀ p ∈ U, p ∈ Γ → l p = 0)
    {a y : E d} (haU : a ∈ U) (ha : 0 < l a) (hyU : y ∈ U) (hy : 0 < l y) :
    y ∈ connectedComponentIn Γᶜ a := by
  have hc : Convex ℝ (U ∩ l ⁻¹' Ioi (0 : ℝ)) :=
    hU.inter ((convex_Ioi (0 : ℝ)).affine_preimage l)
  apply hc.isPreconnected.subset_connectedComponentIn ⟨haU, ha⟩ _ ⟨hyU, hy⟩
  intro p hp hpΓ
  exact (ne_of_gt hp.2) (hzero p hp.1 hpΓ)

set_option maxHeartbeats 1200000 in
/-- Step 11 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet` (V4 1.24):
"has all its points adjacent to the same complementary component". Move
a short normal offset along a segment inside one facet interior, then join it
to the prescribed normal sample. Both half-balls at the other endpoint therefore
belong to the components of the two prescribed samples. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step11_local_cover (K : Geometry.SimplicialComplex ℝ (E d))
    (hfin : K.faces.Finite) (f : K.facets) {a b z : E d}
    (hs : principal_component_step1_hull_geometry_step10_jordan_brouwer_step14_FacetSides K f.val a b)
    (hz : z ∈ relint (convexHull ℝ (f.val : Set (E d)))) :
    ∃ t : ℝ, 0 < t ∧ Metric.ball z t \ K.space ⊆
      connectedComponentIn K.spaceᶜ a ∪ connectedComponentIn K.spaceᶜ b := by
  obtain ⟨q, r, v, hq, hr, hv, hplane, hpatch, rfl, rfl⟩ := hs
  obtain ⟨ε, hε, htube⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step9_facet_tube K hfin f hq hz
  let l : E d →ᵃ[ℝ] ℝ := (innerSL ℝ v).toLinearMap.toAffineMap -
    AffineMap.const ℝ (E d) (inner ℝ v q)
  have hl (w : E d) : l w = inner ℝ v (w - q) := by
    simp [l, inner_sub_right]
  have hlq : l q = 0 := by simp [hl]
  have hlz : l z = 0 := by
    rw [hl]
    have hzA : z ∈ (affineSpan ℝ (f.val : Set (E d)) : Set (E d)) :=
      convexHull_subset_affineSpan _ (intrinsicInterior_subset hz)
    rwa [hplane] at hzA
  have hln (w : E d) (c : ℝ) : l (w + c • v) = l w + c := by
    simp only [hl, add_sub_right_comm, inner_add_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hv]
    simp
  have hzero (w : E d) (hw : w ∈ Metric.ball q r) (hwK : w ∈ K.space) : l w = 0 := by
    have hwA : w ∈ (affineSpan ℝ (f.val : Set (E d)) : Set (E d)) :=
      ((Set.ext_iff.mp hpatch w).mp ⟨hwK, hw⟩).1
    rwa [hplane, Set.mem_setOf_eq, ← hl] at hwA
  have hzeroT (w : E d) (hw : w ∈ Metric.thickening ε (segment ℝ q z))
      (hwK : w ∈ K.space) : l w = 0 := by
    have hwA : w ∈ (affineSpan ℝ (f.val : Set (E d)) : Set (E d)) :=
      ((Set.ext_iff.mp htube w).mp ⟨hwK, hw⟩).1
    rwa [hplane, Set.mem_setOf_eq, ← hl] at hwA
  let t := min r ε / 2
  have ht : 0 < t := half_pos (lt_min hr hε)
  have htr : t < r := (half_lt_self (lt_min hr hε)).trans_le (min_le_left _ _)
  have htε : t < ε := (half_lt_self (lt_min hr hε)).trans_le (min_le_right _ _)
  have hdist (w : E d) (c : ℝ) : dist (w + c • v) w = |c| := by
    simp [dist_eq_norm, norm_smul, hv]
  have hballT : Metric.ball z t ⊆ Metric.thickening ε (segment ℝ q z) := by
    intro w hw
    exact Metric.mem_thickening_iff.mpr ⟨z, right_mem_segment ℝ q z,
      (Metric.mem_ball.mp hw).trans htε⟩
  have hlink (sgn : ℝ) (hsgn : |sgn| = 1) :
      z + (sgn * (t / 2)) • v ∈
        connectedComponentIn K.spaceᶜ (q + (sgn * (r / 2)) • v) := by
    let c := sgn * (t / 2)
    have hcabs : |c| = t / 2 := by simp [c, abs_mul, hsgn, abs_of_pos (half_pos ht)]
    have hcne : c ≠ 0 := by intro hc; have := hcabs; rw [hc, abs_zero] at this; linarith
    have hstart : q + c • v ∈ connectedComponentIn K.spaceᶜ (q + (sgn * (r / 2)) • v) := by
      apply principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step10_positive_component (convex_ball q r) (sgn • l)
        (fun w hw hwK => by simp [hzero w hw hwK])
      · rw [Metric.mem_ball, hdist, abs_mul, hsgn, abs_of_pos (half_pos hr), one_mul]
        exact half_lt_self hr
      · change 0 < sgn * l (q + (sgn * (r / 2)) • v)
        rw [hln, hlq, zero_add]
        have hsquare : sgn * sgn = 1 := by nlinarith [sq_abs sgn]
        nlinarith
      · rw [Metric.mem_ball, hdist, hcabs]
        exact (half_lt_self ht).trans htr
      · change 0 < sgn * l (q + c • v)
        rw [hln, hlq, zero_add]
        have hsquare : sgn * sgn = 1 := by nlinarith [sq_abs sgn]
        dsimp [c]
        nlinarith
    let L : E d →ᵃ[ℝ] E d := (AffineEquiv.constVAdd ℝ (E d) (c • v)).toAffineMap
    have hL (w : E d) : L w = w + c • v := by simp [L, add_comm]
    have hstrip : L '' segment ℝ q z ⊆ K.spaceᶜ := by
      rintro w ⟨p, hp, rfl⟩ hwK
      have hpzero : l p = 0 := by
        have hpA := (affineSpan ℝ (f.val : Set (E d))).convex.segment_subset
          (convexHull_subset_affineSpan _ (intrinsicInterior_subset hq))
          (convexHull_subset_affineSpan _ (intrinsicInterior_subset hz)) hp
        rwa [hplane, Set.mem_setOf_eq, ← hl] at hpA
      have hwT : L p ∈ Metric.thickening ε (segment ℝ q z) := by
        apply Metric.mem_thickening_iff.mpr
        refine ⟨p, hp, ?_⟩
        rw [hL, hdist, hcabs]
        exact (half_lt_self ht).trans htε
      have hh := hzeroT (L p) hwT hwK
      rw [hL, hln, hpzero, zero_add] at hh
      exact hcne hh
    have hcconn := ((convex_segment q z : Convex ℝ (segment ℝ q z)).affine_image L).isPreconnected.subset_connectedComponentIn
      (Set.mem_image_of_mem L (left_mem_segment ℝ q z)) hstrip
    have hzconn := hcconn (Set.mem_image_of_mem L (right_mem_segment ℝ q z))
    rw [hL, hL] at hzconn
    rw [connectedComponentIn_eq hstart]
    exact hzconn
  have hplus := hlink 1 (by norm_num)
  have hminus := hlink (-1) (by norm_num)
  simp only [one_mul, neg_one_mul] at hplus hminus
  refine ⟨t, ht, ?_⟩
  rintro y ⟨hyball, hyK⟩
  have hyne : l y ≠ 0 := by
    intro hly
    apply hyK
    have hyA : y ∈ (affineSpan ℝ (f.val : Set (E d)) : Set (E d)) := by
      rwa [hplane, Set.mem_setOf_eq, ← hl]
    exact ((Set.ext_iff.mp htube y).mpr ⟨hyA, hballT hyball⟩).1
  have hcball (sgn : ℝ) (hsgn : |sgn| = 1) :
      z + (sgn * (t / 2)) • v ∈ Metric.ball z t := by
    rw [Metric.mem_ball, hdist, abs_mul, hsgn, abs_of_pos (half_pos ht), one_mul]
    exact half_lt_self ht
  rcases lt_or_gt_of_ne hyne with hyneg | hypos
  · right
    have hh : y ∈ connectedComponentIn K.spaceᶜ (z + (-(t / 2)) • v) := by
      apply principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step10_positive_component (convex_ball z t) (-l)
        (fun w hw hwK => by simp [hzeroT w (hballT hw) hwK])
      · simpa using hcball (-1) (by norm_num)
      · change 0 < -l (z + (-(t / 2)) • v)
        rw [hln, hlz, zero_add, neg_neg]
        exact half_pos ht
      · exact hyball
      · exact neg_pos.mpr hyneg
    have hh' : y ∈ connectedComponentIn K.spaceᶜ (q + (-(r / 2)) • v) := by
      rwa [connectedComponentIn_eq hminus]
    simpa [sub_eq_add_neg, neg_smul] using hh'
  · left
    have hh : y ∈ connectedComponentIn K.spaceᶜ (z + (t / 2) • v) := by
      apply principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step10_positive_component (convex_ball z t) l
        (fun w hw hwK => hzeroT w (hballT hw) hwK)
      · simpa using hcball 1 (by norm_num)
      · rw [hln, hlz, zero_add]
        exact half_pos ht
      · exact hyball
      · exact hypos
    rwa [connectedComponentIn_eq hplus]

/-- Step 17 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"its frontier ... is nonempty". A generic polygonal path to a nonempty finite
pure codimension one complex first meets a facet interior. Hence any complementary
component contains one of the chosen normal samples of some facet. No manifold
or ridge incidence hypothesis is needed for this access argument. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d) (hne : K.space.Nonempty)
    (a b : K.facets → E d)
    (hsides : ∀ f, principal_component_step1_hull_geometry_step10_jordan_brouwer_step14_FacetSides
      K f.val (a f) (b f)) {x : E d} (hx : x ∉ K.space) :
    ∃ f : K.facets, x ∈ connectedComponentIn K.spaceᶜ (a f) ∨
      x ∈ connectedComponentIn K.spaceᶜ (b f) := by
  obtain ⟨p, hp⟩ := hne
  rw [principal_component_step1_hull_geometry_step10_jordan_brouwer_step9_facets_cover K hfin] at hp
  obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hp
  obtain ⟨q, r, v, hq, _⟩ := hsides g
  obtain ⟨f, z, hz, hcl⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step5_facet_access K hfin hpure ⟨g, hq⟩ hx
  obtain ⟨t, ht, hcover⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step11_local_cover K hfin f (hsides f) hz
  obtain ⟨y, hyball, hyx⟩ := mem_closure_iff.mp hcl _ Metric.isOpen_ball (Metric.mem_ball_self ht)
  have hyK : y ∉ K.space := connectedComponentIn_subset _ _ hyx
  refine ⟨f, ?_⟩
  rcases hcover ⟨hyball, hyK⟩ with hya | hyb
  · left
    rw [connectedComponentIn_eq hya, ← connectedComponentIn_eq hyx]
    exact mem_connectedComponentIn hx
  · right
    rw [connectedComponentIn_eq hyb, ← connectedComponentIn_eq hyx]
    exact mem_connectedComponentIn hx

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"crosses them transversally". In an affine basis extending a simplex, membership
in a face is equivalent to nonnegative coordinates, with coordinates outside
that face equal to zero. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step1_coordinates
    {ι : Type*} [Fintype ι] (b : AffineBasis ι ℝ (E d))
    (f : Finset (E d)) (hf : (f : Set (E d)) ⊆ Set.range b) (x : E d) :
    x ∈ convexHull ℝ (f : Set (E d)) ↔
      (∀ i, 0 ≤ b.coord i x) ∧ (∀ i, b i ∉ f → b.coord i x = 0) := by
  classical
  constructor
  · intro hx
    constructor
    · intro i
      apply convexHull_min (t := {x | 0 ≤ b.coord i x}) ?_
        (Convex.affine_preimage (b.coord i) (convex_Ici 0)) hx
      intro y hy
      obtain ⟨j, rfl⟩ := hf hy
      change 0 ≤ b.coord i (b j)
      simp only [b.coord_apply]
      split_ifs <;> norm_num
    · intro i hi
      apply convexHull_min (t := {x | b.coord i x = 0}) ?_
        (Convex.affine_preimage (b.coord i) (convex_singleton 0)) hx
      intro y hy
      obtain ⟨j, rfl⟩ := hf hy
      exact b.coord_apply_ne (fun he => hi (he.symm ▸ hy))
  · rintro ⟨hpos, hzero⟩
    let u : Finset ι := Finset.univ.filter fun i => b i ∈ f
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
    apply (convex_convexHull ℝ (f : Set (E d))).sum_mem (fun i _ => hpos i) hsum
    intro i hi
    exact subset_convexHull ℝ (f : Set (E d)) (Finset.mem_filter.mp hi).2

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"in general position". A coordinate outside a simplex vanishes on its whole
affine span, because affine maps agreeing on its vertices agree on that span. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step2_span_coordinate
    {ι : Type*} (b : AffineBasis ι ℝ (E d))
    (f : Finset (E d)) (hf : (f : Set (E d)) ⊆ Set.range b)
    {i : ι} (hi : b i ∉ f) {x : E d} (hx : x ∈ affineSpan ℝ (f : Set (E d))) :
    b.coord i x = 0 := by
  have heq : Set.EqOn (b.coord i) (AffineMap.const ℝ (E d) (0 : ℝ)) (f : Set (E d)) := by
    intro y hy
    obtain ⟨j, rfl⟩ := hf hy
    exact b.coord_apply_ne (fun h => hi (h.symm ▸ hy))
  exact AffineMap.eqOn_affineSpan heq hx

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"in general position". A zero barycentric coordinate deletes its vertex from
the supporting face. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step3_delete_coordinate
    {ι : Type*} [Fintype ι] (b : AffineBasis ι ℝ (E d))
    (f : Finset (E d)) (hf : (f : Set (E d)) ⊆ Set.range b)
    {x : E d} (hx : x ∈ convexHull ℝ (f : Set (E d))) (i : ι) :
    x ∈ convexHull ℝ ((f.erase (b i) : Finset (E d)) : Set (E d)) ↔ b.coord i x = 0 := by
  classical
  have hferase : (f.erase (b i) : Set (E d)) ⊆ Set.range b :=
    fun y hy => hf (Finset.mem_of_mem_erase hy)
  rw [principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step1_coordinates
    b (f.erase (b i)) hferase x]
  have hcoord :=
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step1_coordinates
      b f hf x).mp hx
  refine ⟨fun h => h.2 i (by simp), fun hzero => ⟨hcoord.1, ?_⟩⟩
  intro j hj
  by_cases hjf : b j ∈ f
  · have he : b j = b i := by
      by_contra hn
      exact hj (Finset.mem_erase.mpr ⟨hn, hjf⟩)
    have he' : j = i := b.ind.injective he
    simpa only [he'] using hzero
  · exact hcoord.2 j hjf

open scoped Topology in
/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"crosses them transversally". Finitely many affine inequalities on a line,
nonnegative at zero and with at most one equality there, have another nearby
feasible parameter. Choose the sign allowed by the one possible equality. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step4_line_inequalities
    {ι : Type*} [Fintype ι] (l : ι → ℝ →ᵃ[ℝ] ℝ)
    (h0 : ∀ i, 0 ≤ l i 0) (hz : {i | l i 0 = 0}.Subsingleton) :
    ∃ t : ℝ, t ≠ 0 ∧ ∀ i, 0 ≤ l i t := by
  classical
  by_cases hn : ∃ i, l i 0 = 0
  · obtain ⟨i, hi⟩ := hn
    have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ j, j ≠ i → 0 ≤ l j t := by
      apply Filter.eventually_all.mpr
      intro j
      by_cases hji : j = i
      · exact Filter.Eventually.of_forall fun t h => (h hji).elim
      · have hp : 0 < l j 0 := lt_of_le_of_ne (h0 j) fun he => hji (hz he.symm hi)
        exact ((l j).continuous_of_finiteDimensional.continuousAt.eventually_const_lt hp).mono
          fun t ht _ => ht.le
    obtain ⟨δ, hδ, hδmem⟩ := Metric.eventually_nhds_iff.mp hev
    have heq (t : ℝ) : l i t = t * l i 1 := by
      have h := (l i).apply_lineMap (0 : ℝ) 1 t
      simpa only [AffineMap.lineMap_apply_ring, hi, mul_zero, zero_add, mul_one] using h
    by_cases hsign : 0 ≤ l i 1
    · refine ⟨δ / 2, by positivity, fun j => ?_⟩
      by_cases hji : j = i
      · subst j
        rw [heq]
        exact mul_nonneg (by positivity) hsign
      · exact hδmem (by
          rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < δ / 2)]
          linarith) j hji
    · refine ⟨-(δ / 2), by linarith, fun j => ?_⟩
      by_cases hji : j = i
      · subst j
        rw [heq]
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (le_of_not_ge hsign)
      · exact hδmem (by
          rw [Real.dist_eq, sub_zero, abs_of_neg (by linarith : -(δ / 2) < 0)]
          linarith) j hji
  · have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 ≤ l i t := by
      apply Filter.eventually_all.mpr
      intro i
      have hp : 0 < l i 0 := lt_of_le_of_ne (h0 i) fun he => hn ⟨i, he.symm⟩
      exact ((l i).continuous_of_finiteDimensional.continuousAt.eventually_const_lt hp).mono
        fun t ht => ht.le
    obtain ⟨δ, hδ, hδmem⟩ := Metric.eventually_nhds_iff.mp hev
    exact ⟨δ / 2, by positivity, hδmem (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < δ / 2)]
      linarith)⟩

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"crosses them transversally". A plane and a hyperplane through a point have
a nonzero common direction, by the dimension formula for subspaces. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step5_common_line
    (A B : AffineSubspace ℝ (E d)) (hA : Module.finrank ℝ A.direction = 2)
    (hB : Module.finrank ℝ B.direction + 1 = d)
    {x : E d} (hxA : x ∈ A) (hxB : x ∈ B) :
    ∃ y : E d, y ≠ x ∧ y ∈ A ∧ y ∈ B := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq A.direction B.direction
  have hle : Module.finrank ℝ ↥(A.direction ⊔ B.direction) ≤ d := by
    simpa using (Submodule.finrank_le (A.direction ⊔ B.direction))
  have hpos : 0 < Module.finrank ℝ ↥(A.direction ⊓ B.direction) := by omega
  letI : Nontrivial ↥(A.direction ⊓ B.direction) := Module.finrank_pos_iff.mp hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : ↥(A.direction ⊓ B.direction))
  have hvne : (v : E d) ≠ 0 := fun h => hv (Subtype.ext h)
  refine ⟨(v : E d) +ᵥ x, ?_, ?_, ?_⟩
  · change (v : E d) + x ≠ x
    simpa only [ne_eq, add_eq_right] using hvne
  · exact A.vadd_mem_of_mem_direction v.property.1 hxA
  · exact B.vadd_mem_of_mem_direction v.property.2 hxB

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"crosses them transversally". A nonempty section of one facet cannot be a
singleton. On their common affine line, at most one barycentric inequality is
an equality: two facet equalities would meet a smaller face, two triangle
equalities would meet a triangle vertex, and a boundary crossing is in a facet
interior. Thus one sign of the line gives another point of the section. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step6_nonsingleton
    (K : Geometry.SimplicialComplex ℝ (E d))
    (hpure : ∀ f ∈ K.facets, f.card = d)
    {a b c : E d}
    (hpos : principal_component_step1_hull_geometry_step10_jordan_brouwer_step13_TrianglePosition K a b c)
    {f : Finset (E d)} (hf : f ∈ K.facets)
    (hcut : (convexHull ℝ ({a, b, c} : Set (E d)) ∩
      convexHull ℝ (f : Set (E d))).Nonempty) :
    ¬ (convexHull ℝ ({a, b, c} : Set (E d)) ∩
      convexHull ℝ (f : Set (E d))).Subsingleton := by
  classical
  obtain ⟨x, hxT, hxf⟩ := hcut
  have hxK : x ∈ K.space := K.convexHull_subset_space hf.1 hxf
  let t : Finset (E d) := {a, b, c}
  have ht : (t : Set (E d)) = {a, b, c} := by simp [t]
  have hxt : x ∈ convexHull ℝ (t : Set (E d)) := by simpa only [ht] using hxT
  have hrange : Set.range ![a, b, c] = (t : Set (E d)) := by
    ext z
    simp [t, Matrix.range_cons, or_comm, or_left_comm, or_assoc]
  have hai : AffineIndependent ℝ ![a, b, c] := hpos.1
  have htri : AffineIndependent ℝ ((↑) : t → E d) := by
    have h := hai.range
    rwa [hrange] at h
  have hab : a ≠ b := by simpa using hai.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac : a ≠ c := by simpa using hai.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc : b ≠ c := by simpa using hai.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have htcard : t.card = 3 := by simp [t, hab, hac, hbc]
  have hverts (z : E d) (hz : z ∈ t) : z ∉ K.space := by
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz
    · subst z; exact hpos.2.1.1
    · subst z; exact hpos.2.1.2.1
    · subst z; exact hpos.2.2.1.2.1
  let T := convexHull ℝ ({a, b, c} : Set (E d))
  let D := segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a
  have hdelete (v : E d) (hv : v ∈ t) :
      convexHull ℝ ((t.erase v : Finset (E d)) : Set (E d)) ⊆ D := by
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv | hv
    · subst v
      have hs : t.erase a ⊆ ({b, c} : Finset (E d)) := by
        intro z hz
        simp only [t, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        tauto
      have hc := convexHull_mono (𝕜 := ℝ) (show (t.erase a : Set (E d)) ⊆ {b, c} by
        simpa only [Finset.coe_insert, Finset.coe_singleton] using (Finset.coe_subset.mpr hs))
      rw [convexHull_pair] at hc
      exact hc.trans fun z hz => Or.inl (Or.inr hz)
    · subst v
      have hs : t.erase b ⊆ ({c, a} : Finset (E d)) := by
        intro z hz
        simp only [t, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        tauto
      have hc := convexHull_mono (𝕜 := ℝ) (show (t.erase b : Set (E d)) ⊆ {c, a} by
        simpa only [Finset.coe_insert, Finset.coe_singleton] using (Finset.coe_subset.mpr hs))
      rw [convexHull_pair] at hc
      exact hc.trans fun z hz => Or.inr hz
    · subst v
      have hs : t.erase c ⊆ ({a, b} : Finset (E d)) := by
        intro z hz
        simp only [t, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        tauto
      have hc := convexHull_mono (𝕜 := ℝ) (show (t.erase c : Set (E d)) ⊆ {a, b} by
        simpa only [Finset.coe_insert, Finset.coe_singleton] using (Finset.coe_subset.mpr hs))
      rw [convexHull_pair] at hc
      exact hc.trans fun z hz => Or.inl (Or.inl hz)
  obtain ⟨u, hfu, hu, huspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top (K.indep hf.1)
  obtain ⟨w, htw, hw, hwspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top htri
  let bf : AffineBasis u ℝ (E d) := ⟨(↑), hu, by simpa using huspan⟩
  let bt : AffineBasis w ℝ (E d) := ⟨(↑), hw, by simpa using hwspan⟩
  letI : Finite u := finite_of_fin_dim_affineIndependent ℝ hu
  letI : Finite w := finite_of_fin_dim_affineIndependent ℝ hw
  letI : Fintype u := Fintype.ofFinite u
  letI : Fintype w := Fintype.ofFinite w
  have hfrange : (f : Set (E d)) ⊆ Set.range bf := fun z hz => ⟨⟨z, hfu hz⟩, rfl⟩
  have htrange : (t : Set (E d)) ⊆ Set.range bt := fun z hz => ⟨⟨z, htw hz⟩, rfl⟩
  let cf : f → E d →ᵃ[ℝ] ℝ := fun i => bf.coord ⟨i.val, hfu i.property⟩
  let ct : t → E d →ᵃ[ℝ] ℝ := fun i => bt.coord ⟨i.val, htw i.property⟩
  have hcoordf (z : E d) :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step1_coordinates
      bf f hfrange z
  have hcoordt (z : E d) :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step1_coordinates
      bt t htrange z
  have hff (i j : f) (hi : cf i x = 0) (hj : cf j x = 0) : i = j := by
    by_contra hne
    have hij : (i : E d) ≠ (j : E d) := fun he => hne (Subtype.ext he)
    have hxi :=
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step3_delete_coordinate
        bf f hfrange hxf ⟨i.val, hfu i.property⟩).mpr hi
    have hxij :=
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step3_delete_coordinate
        bf (f.erase i.val) (fun z hz => hfrange (Finset.mem_of_mem_erase hz)) hxi
          ⟨j.val, hfu j.property⟩).mpr hj
    let s := (f.erase i.val).erase j.val
    have hsf : s ⊆ f := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hs : s ∈ K.faces := K.down_closed hf.1 hsf (convexHull_nonempty_iff.mp ⟨x, hxij⟩)
    have hjmem : j.val ∈ f.erase i.val := Finset.mem_erase.mpr ⟨hij.symm, j.property⟩
    have hsc : s.card + 1 < d := by
      dsimp [s]
      rw [Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem i.property, hpure f hf]
      have hd : 2 ≤ d := Fact.out
      omega
    exact Set.disjoint_left.mp (hpos.2.2.2.2.2.2.1 s hs hsc) hxT hxij
  have htt (i j : t) (hi : ct i x = 0) (hj : ct j x = 0) : i = j := by
    by_contra hne
    have hij : (i : E d) ≠ (j : E d) := fun he => hne (Subtype.ext he)
    have hxi :=
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step3_delete_coordinate
        bt t htrange hxt ⟨i.val, htw i.property⟩).mpr hi
    have hxij :=
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step3_delete_coordinate
        bt (t.erase i.val) (fun z hz => htrange ((Finset.erase_subset i.val t) hz)) hxi
          ⟨j.val, htw j.property⟩).mpr hj
    let s := (t.erase i.val).erase j.val
    have hst : s ⊆ t := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hjmem : j.val ∈ t.erase i.val := Finset.mem_erase.mpr ⟨hij.symm, j.property⟩
    have hsc : s.card = 1 := by
      dsimp [s]
      rw [Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem i.property, htcard]
    obtain ⟨z, hsz⟩ := Finset.card_eq_one.mp hsc
    have hxz : x = z := by
      change x ∈ convexHull ℝ (s : Set (E d)) at hxij
      simpa only [hsz, Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using hxij
    have hzt : z ∈ t := hst (by rw [hsz]; simp)
    exact hverts z hzt (hxz ▸ hxK)
  have hft (i : f) (j : t) (hi : cf i x = 0) (hj : ct j x = 0) : False := by
    have hxj :=
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step3_delete_coordinate
        bt t htrange hxt ⟨j.val, htw j.property⟩).mpr hj
    have hxD : x ∈ D := hdelete j.val j.property hxj
    have hrel : ∃ g ∈ K.facets, x ∈ relint (convexHull ℝ (g : Set (E d))) := by
      rcases hxD with (hab | hbc) | hca
      · obtain ⟨g, hg, hxg, -⟩ := hpos.2.1.2.2.2 x ⟨hab, hxK⟩
        exact ⟨g, hg, hxg⟩
      · obtain ⟨g, hg, hxg, -⟩ := hpos.2.2.1.2.2.2 x ⟨hbc, hxK⟩
        exact ⟨g, hg, hxg⟩
      · obtain ⟨g, hg, hxg, -⟩ := hpos.2.2.2.1.2.2.2 x ⟨hca, hxK⟩
        exact ⟨g, hg, hxg⟩
    obtain ⟨g, hg, hxg⟩ := hrel
    have hgf : g = f := hg.2 hf.1
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step3_relint_incidence
        K hg.1 hf.1 hxg hxf)
    subst g
    have hpositive : 0 < cf i x :=
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step2_positive_coordinate
        hxg (subset_convexHull ℝ _ i.property) (cf i)
        (fun z hz => ((hcoordf z).mp hz).1 ⟨i.val, hfu i.property⟩)
        (by change 0 < bf.coord ⟨i.val, hfu i.property⟩ (bf ⟨i.val, hfu i.property⟩); simp)
    exact (ne_of_gt hpositive) hi
  let A := affineSpan ℝ (t : Set (E d))
  let B := affineSpan ℝ (f : Set (E d))
  have hA : Module.finrank ℝ A.direction = 2 := by
    have h := htri.finrank_vectorSpan (n := 2) (by simpa using htcard)
    change Module.finrank ℝ (affineSpan ℝ (t : Set (E d))).direction = 2
    rw [direction_affineSpan]
    have hr : Set.range ((↑) : t → E d) = (t : Set (E d)) := Subtype.range_val
    rwa [hr] at h
  have hB : Module.finrank ℝ B.direction + 1 = d := by
    letI : Nonempty f := (K.nonempty_of_mem_faces hf.1).to_subtype
    have h := (K.indep hf.1).finrank_vectorSpan_add_one
    change Module.finrank ℝ (affineSpan ℝ (f : Set (E d))).direction + 1 = d
    rw [direction_affineSpan]
    have hr : Set.range ((↑) : f → E d) = (f : Set (E d)) := Subtype.range_val
    rw [hr] at h
    simpa only [Fintype.card_coe, hpure f hf] using h
  have hxA : x ∈ A := convexHull_subset_affineSpan _ hxt
  have hxB : x ∈ B := convexHull_subset_affineSpan _ hxf
  obtain ⟨y, hy, hyA, hyB⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step5_common_line
      A B hA hB hxA hxB
  let L : ℝ →ᵃ[ℝ] E d := AffineMap.lineMap x y
  have hLinj : Function.Injective L := AffineMap.lineMap_injective ℝ hy.symm
  have hLA (r : ℝ) : L r ∈ A := AffineMap.lineMap_mem r hxA hyA
  have hLB (r : ℝ) : L r ∈ B := AffineMap.lineMap_mem r hxB hyB
  let l : f ⊕ t → ℝ →ᵃ[ℝ] ℝ := Sum.elim (fun i => (cf i).comp L) (fun i => (ct i).comp L)
  have hl0 : ∀ i, 0 ≤ l i 0 := by
    intro i
    cases i with
    | inl i => simpa [l, L, cf] using ((hcoordf x).mp hxf).1 ⟨i.val, hfu i.property⟩
    | inr i => simpa [l, L, ct] using ((hcoordt x).mp hxt).1 ⟨i.val, htw i.property⟩
  have hlz : {i | l i 0 = 0}.Subsingleton := by
    intro i hi j hj
    cases i with
    | inl i =>
      have hi' : cf i x = 0 := by simpa [l, L] using hi
      cases j with
      | inl j =>
        exact congrArg Sum.inl (hff i j hi' (by simpa [l, L] using hj))
      | inr j => exact (hft i j hi' (by simpa [l, L] using hj)).elim
    | inr i =>
      have hi' : ct i x = 0 := by simpa [l, L] using hi
      cases j with
      | inl j => exact (hft j i (by simpa [l, L] using hj) hi').elim
      | inr j =>
        exact congrArg Sum.inr (htt i j hi' (by simpa [l, L] using hj))
  obtain ⟨r, hr, hlr⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step4_line_inequalities
      l hl0 hlz
  have hrf : L r ∈ convexHull ℝ (f : Set (E d)) := by
    apply (hcoordf (L r)).mpr
    have hz (i : u) (hi : bf i ∉ f) : bf.coord i (L r) = 0 :=
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step2_span_coordinate
        bf f hfrange hi (hLB r)
    refine ⟨fun i => ?_, hz⟩
    by_cases hi : bf i ∈ f
    · simpa [l, cf, bf] using hlr (Sum.inl ⟨bf i, hi⟩)
    · rw [hz i hi]
  have hrt : L r ∈ convexHull ℝ (t : Set (E d)) := by
    apply (hcoordt (L r)).mpr
    have hz (i : w) (hi : bt i ∉ t) : bt.coord i (L r) = 0 :=
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step2_span_coordinate
        bt t htrange hi (hLA r)
    refine ⟨fun i => ?_, hz⟩
    by_cases hi : bt i ∈ t
    · simpa [l, ct, bt] using hlr (Sum.inr ⟨bt i, hi⟩)
    · rw [hz i hi]
  intro hsub
  have heq : L r = x := hsub ⟨by simpa only [ht] using hrt, hrf⟩ ⟨hxT, hxf⟩
  exact hr (hLinj (heq.trans (by simp [L])))
/-- Step 7 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"crosses them transversally". A compact convex collinear set containing two
distinct points is a nondegenerate closed segment, by parametrizing its line
and taking the minimum and maximum parameters. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step7_interval
    {C : Set (E d)} (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hline : Collinear ℝ C) (hne : ¬ C.Subsingleton) :
    ∃ p q : E d, p ≠ q ∧ C = segment ℝ p q := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp hne
  let L : ℝ →ᵃ[ℝ] E d := AffineMap.lineMap a b
  have hLinj : Function.Injective L := AffineMap.lineMap_injective ℝ hab
  have hL : Topology.IsClosedEmbedding L := by
    have h := (Homeomorph.addRight a).isClosedEmbedding.comp
      (isClosedEmbedding_smul_left (𝕜 := ℝ) (sub_ne_zero.mpr hab.symm))
    change Topology.IsClosedEmbedding (fun t : ℝ => t • (b - a) + a) at h
    simpa only [L, AffineMap.lineMap_apply_module'] using h
  let I : Set ℝ := L ⁻¹' C
  have hI : IsCompact I := hL.isCompact_preimage hcompact
  have hI0 : (0 : ℝ) ∈ I := by simpa [I, L] using ha
  have hI1 : (1 : ℝ) ∈ I := by simpa [I, L] using hb
  have hIeq : I = Set.Icc (sInf I) (sSup I) :=
    eq_Icc_of_connected_compact ⟨⟨0, hI0⟩, (hconvex.affine_preimage L).isPreconnected⟩ hI
  have hCI : C = L '' I := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
        (hline.mem_affineSpan_of_mem_of_ne ha hb hx hab)
      exact ⟨r, by change L r ∈ C; simpa only [L, hr] using hx, hr⟩
    · exact Set.image_preimage_subset _ _
  have hlo : sInf I ≤ 0 := (hIeq ▸ hI0).1
  have hhi : 1 ≤ sSup I := (hIeq ▸ hI1).2
  have hlt : sInf I < sSup I := by linarith
  refine ⟨L (sInf I), L (sSup I), fun he => hlt.ne (hLinj he), ?_⟩
  calc
    C = L '' I := hCI
    _ = L '' Set.Icc (sInf I) (sSup I) := congrArg (fun s => L '' s) hIeq
    _ = segment ℝ (L (sInf I)) (L (sSup I)) := by
      rw [← segment_eq_Icc hlt.le, image_segment]

/-- Step 8 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"in general position". Intersecting a plane with an affine subspace which does
not contain it gives a collinear set: a proper nonempty affine subspace of a
two-dimensional affine space has direction of dimension at most one. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step8_plane_section
    (A B : AffineSubspace ℝ (E d)) (hA : Module.finrank ℝ A.direction = 2)
    (hnot : ¬ A ≤ B) : Collinear ℝ ((A : Set (E d)) ∩ (B : Set (E d))) := by
  by_cases hn : ((A : Set (E d)) ∩ (B : Set (E d))).Nonempty
  · have hlt : A ⊓ B < A := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro he
      apply hnot
      rw [← he]
      exact inf_le_right
    have hdim := Submodule.finrank_lt_finrank_of_lt
      (AffineSubspace.direction_lt_of_nonempty hlt hn)
    apply collinear_iff_finrank_le_one.mpr
    change Module.finrank ℝ (vectorSpan ℝ ((A ⊓ B : AffineSubspace ℝ (E d)) : Set (E d))) ≤ 1
    rw [← AffineSubspace.direction_eq_vectorSpan]
    omega
  · rw [Set.not_nonempty_iff_eq_empty.mp hn]
    exact collinear_empty ℝ (E d)

/-- Step 9 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"crosses them transversally at finitely many points". The intersection of one
facet with the filled triangle, when nonempty, is a nondegenerate closed segment.
The triangle plane is not contained in the facet hyperplane; regular boundary
crossings and transverse ridge crossings rule out a singleton intersection. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step9_facet_segment
    (K : Geometry.SimplicialComplex ℝ (E d))
    (hpure : ∀ f ∈ K.facets, f.card = d)
    {a b c : E d}
    (hpos : principal_component_step1_hull_geometry_step10_jordan_brouwer_step13_TrianglePosition K a b c)
    {f : Finset (E d)} (hf : f ∈ K.facets)
    (hcut : (convexHull ℝ ({a, b, c} : Set (E d)) ∩
      convexHull ℝ (f : Set (E d))).Nonempty) :
    ∃ p q : E d, p ≠ q ∧
      convexHull ℝ ({a, b, c} : Set (E d)) ∩ convexHull ℝ (f : Set (E d)) =
        segment ℝ p q := by
  let A := affineSpan ℝ ({a, b, c} : Set (E d))
  let B := affineSpan ℝ (f : Set (E d))
  have hA : Module.finrank ℝ A.direction = 2 := by
    have ha : AffineIndependent ℝ ![a, b, c] := hpos.1
    have h := ha.finrank_vectorSpan (n := 2) (by simp)
    have hr : Set.range ![a, b, c] = ({a, b, c} : Set (E d)) := by
      ext z
      simp [Matrix.range_cons, or_comm, or_left_comm, or_assoc]
    rw [hr] at h
    change Module.finrank ℝ (affineSpan ℝ ({a, b, c} : Set (E d))).direction = 2
    rw [direction_affineSpan]
    exact h
  have hline : Collinear ℝ (convexHull ℝ ({a, b, c} : Set (E d)) ∩
      convexHull ℝ (f : Set (E d))) :=
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step8_plane_section
      A B hA (hpos.2.2.2.2.2.2.2.2 f hf)).subset
      (show convexHull ℝ ({a, b, c} : Set (E d)) ∩ convexHull ℝ (f : Set (E d)) ⊆
        (A : Set (E d)) ∩ (B : Set (E d)) from
          fun x hx => ⟨convexHull_subset_affineSpan _ hx.1, convexHull_subset_affineSpan _ hx.2⟩)
  exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step7_interval
    ((Set.toFinite ({a, b, c} : Set (E d))).isCompact_convexHull.inter_right
      f.finite_toSet.isClosed_convexHull)
    ((convex_convexHull ℝ _).inter (convex_convexHull ℝ _)) hline
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step6_nonsingleton
      K hpure hpos hf hcut)

/-- Step 10 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"crosses them transversally". Every face of a simplex is an extreme subset of
that simplex. A barycentric coordinate vanishing at an interior point of a
segment vanishes at both ends, since the coordinates are nonnegative. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step10_simplex_faces
    (f s : Finset (E d)) (hf : AffineIndependent ℝ ((↑) : f → E d)) (hsf : s ⊆ f) :
    IsExtreme ℝ (convexHull ℝ (f : Set (E d))) (convexHull ℝ (s : Set (E d))) := by
  classical
  obtain ⟨u, hfu, hu, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hf
  let b : AffineBasis u ℝ (E d) := ⟨(↑), hu, by simpa using hspan⟩
  letI : Finite u := finite_of_fin_dim_affineIndependent ℝ hu
  letI : Fintype u := Fintype.ofFinite u
  have hmem (t : Finset (E d)) (htu : (t : Set (E d)) ⊆ u) (x : E d) :
      x ∈ convexHull ℝ (t : Set (E d)) ↔
        (∀ i : u, 0 ≤ b.coord i x) ∧ (∀ i : u, (i : E d) ∉ t → b.coord i x = 0) := by
    constructor
    · intro hx
      constructor
      · intro i
        apply convexHull_min (t := {x | 0 ≤ b.coord i x}) ?_
          (Convex.affine_preimage (b.coord i) (convex_Ici 0)) hx
        intro y hy
        change 0 ≤ b.coord i (b ⟨y, htu hy⟩)
        simp only [b.coord_apply]
        split_ifs <;> norm_num
      · intro i hi
        apply convexHull_min (t := {x | b.coord i x = 0}) ?_
          (Convex.affine_preimage (b.coord i) (convex_singleton 0)) hx
        intro y hy
        have hiy : i ≠ ⟨y, htu hy⟩ := by
          intro he
          exact hi (by simpa only [he] using hy)
        change b.coord i (b ⟨y, htu hy⟩) = 0
        exact b.coord_apply_ne hiy
    · rintro ⟨hpos, hzero⟩
      let v : Finset u := Finset.univ.filter fun i : u => (i : E d) ∈ t
      have hsum : ∑ i ∈ v, b.coord i x = 1 := by
        rw [← b.sum_coord_apply_eq_one x]
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        exact hzero i (by simpa [v] using hi)
      have hsumv : ∑ i ∈ v, b.coord i x • b i = x := by
        calc
          _ = ∑ i, b.coord i x • b i := by
            apply Finset.sum_subset (Finset.subset_univ _)
            intro i _ hi
            rw [hzero i (by simpa [v] using hi), zero_smul]
          _ = x := b.linear_combination_coord_eq_self x
      rw [← hsumv]
      apply (convex_convexHull ℝ (t : Set (E d))).sum_mem (fun i _ => hpos i) hsum
      intro i hi
      exact subset_convexHull ℝ (t : Set (E d)) (Finset.mem_filter.mp hi).2
  refine ⟨convexHull_mono (by simpa using hsf), ?_⟩
  intro x hx y hy z hz hxyz
  rw [openSegment_eq_image_lineMap] at hxyz
  obtain ⟨r, hr, rfl⟩ := hxyz
  have hxp := ((hmem f hfu x).mp hx).1
  have hyp := ((hmem f hfu y).mp hy).1
  have hzp := ((hmem s (fun z hz => hfu (hsf hz)) _).mp hz).2
  apply (hmem s (fun z hz => hfu (hsf hz)) x).mpr
  refine ⟨hxp, fun i hi => ?_⟩
  have hz0 := hzp i hi
  rw [(b.coord i).apply_lineMap, AffineMap.lineMap_apply_ring] at hz0
  have hnonneg := mul_nonneg hr.1.le (hyp i)
  have hprod : (1 - r) * b.coord i x = 0 := le_antisymm (by linarith)
    (mul_nonneg (sub_nonneg.mpr hr.2.le) (hxp i))
  exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (sub_pos.mpr hr.2))

open scoped Topology in
/-- Step 11 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"in general position". At a point of a finite convex hull lying in none of
the hulls obtained by deleting a vertex, all barycentric weights are positive.
Consequently every segment within the hull extends a little past that point. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step11_extend
    (f : Finset (E d)) {x y : E d}
    (hx : x ∈ convexHull ℝ (f : Set (E d)))
    (hy : y ∈ convexHull ℝ (f : Set (E d)))
    (hface : ∀ v ∈ f, x ∉ convexHull ℝ ((f.erase v : Finset (E d)) : Set (E d))) :
    ∀ᶠ t : ℝ in 𝓝 0, AffineMap.lineMap x y t ∈ convexHull ℝ (f : Set (E d)) := by
  classical
  obtain ⟨w, hw, hw1, hwx⟩ := Finset.mem_convexHull'.mp hx
  obtain ⟨u, hu, hu1, huy⟩ := Finset.mem_convexHull'.mp hy
  have hwpos (v : E d) (hv : v ∈ f) : 0 < w v := by
    by_contra hn
    have hzero : w v = 0 := le_antisymm (le_of_not_gt hn) (hw v hv)
    apply hface v hv
    apply Finset.mem_convexHull'.mpr
    refine ⟨w, fun z hz => hw z (Finset.mem_of_mem_erase hz), ?_, ?_⟩
    · simpa only [hzero, add_zero] using (Finset.sum_erase_add f w hv).trans hw1
    · simpa only [hzero, zero_smul, add_zero] using
        (Finset.sum_erase_add f (fun z => w z • z) hv).trans hwx
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ v ∈ f, 0 ≤ (1 - t) * w v + t * u v := by
    apply (Filter.eventually_all_finset f).mpr
    intro v hv
    have hc : Continuous (fun t : ℝ => (1 - t) * w v + t * u v) := by fun_prop
    have hp : 0 < (1 - (0 : ℝ)) * w v + 0 * u v := by simpa using hwpos v hv
    exact (hc.continuousAt.eventually_const_lt hp).mono fun t ht => ht.le
  filter_upwards [hev] with t ht
  apply Finset.mem_convexHull'.mpr
  refine ⟨fun v => (1 - t) * w v + t * u v, ht, ?_, ?_⟩
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hw1, hu1, mul_one]
    ring
  · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, hwx, huy]
    exact (AffineMap.lineMap_apply_module x y t).symm

/-- Step 12 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"crosses them transversally". For one facet section, its two endpoints are
exactly the points on the triangle boundary or on a ridge of that facet. The
avoidance of smaller faces and the transverse ridge condition exclude any
other endpoint or any ridge point in the open section segment. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step12_endpoints
    (K : Geometry.SimplicialComplex ℝ (E d))
    (hpure : ∀ f ∈ K.facets, f.card = d)
    {a b c : E d}
    (hpos : principal_component_step1_hull_geometry_step10_jordan_brouwer_step13_TrianglePosition K a b c)
    {f : Finset (E d)} (hf : f ∈ K.facets) {p q : E d} (hne : p ≠ q)
    (hcut : convexHull ℝ ({a, b, c} : Set (E d)) ∩ convexHull ℝ (f : Set (E d)) =
      segment ℝ p q) (x : E d) :
    (x = p ∨ x = q) ↔
      x ∈ convexHull ℝ ({a, b, c} : Set (E d)) ∩ convexHull ℝ (f : Set (E d)) ∧
        (x ∈ segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a ∨
          ∃ s ∈ K.faces, s.card = d - 1 ∧ s ⊆ f ∧
            x ∈ convexHull ℝ (s : Set (E d))) := by
  classical
  let T := convexHull ℝ ({a, b, c} : Set (E d))
  let D := segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a
  let t : Finset (E d) := {a, b, c}
  have ht : convexHull ℝ (t : Set (E d)) = T := by simp [t, T]
  have hp : p ∈ T ∩ convexHull ℝ (f : Set (E d)) := by
    rw [hcut]
    exact left_mem_segment ℝ _ _
  have hq : q ∈ T ∩ convexHull ℝ (f : Set (E d)) := by
    rw [hcut]
    exact right_mem_segment ℝ _ _
  have hdelete (v : E d) (hv : v ∈ t) :
      convexHull ℝ ((t.erase v : Finset (E d)) : Set (E d)) ⊆ D := by
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv | hv
    · subst v
      have hs : t.erase a ⊆ ({b, c} : Finset (E d)) := by
        intro z hz
        simp only [t, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        tauto
      have hc := convexHull_mono (𝕜 := ℝ) (show (t.erase a : Set (E d)) ⊆ {b, c} by simpa only [Finset.coe_insert, Finset.coe_singleton] using (Finset.coe_subset.mpr hs))
      rw [convexHull_pair] at hc
      exact hc.trans fun z hz => Or.inl (Or.inr hz)
    · subst v
      have hs : t.erase b ⊆ ({c, a} : Finset (E d)) := by
        intro z hz
        simp only [t, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        tauto
      have hc := convexHull_mono (𝕜 := ℝ) (show (t.erase b : Set (E d)) ⊆ {c, a} by simpa only [Finset.coe_insert, Finset.coe_singleton] using (Finset.coe_subset.mpr hs))
      rw [convexHull_pair] at hc
      exact hc.trans fun z hz => Or.inr hz
    · subst v
      have hs : t.erase c ⊆ ({a, b} : Finset (E d)) := by
        intro z hz
        simp only [t, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        tauto
      have hc := convexHull_mono (𝕜 := ℝ) (show (t.erase c : Set (E d)) ⊆ {a, b} by simpa only [Finset.coe_insert, Finset.coe_singleton] using (Finset.coe_subset.mpr hs))
      rw [convexHull_pair] at hc
      exact hc.trans fun z hz => Or.inl (Or.inl hz)
  have endpoint (u v : E d) (huv : u ≠ v)
      (heq : T ∩ convexHull ℝ (f : Set (E d)) = segment ℝ u v) :
      u ∈ T ∩ convexHull ℝ (f : Set (E d)) ∧
        (u ∈ D ∨ ∃ s ∈ K.faces, s.card = d - 1 ∧ s ⊆ f ∧
          u ∈ convexHull ℝ (s : Set (E d))) := by
    have hu : u ∈ T ∩ convexHull ℝ (f : Set (E d)) := by
      rw [heq]; exact left_mem_segment ℝ u v
    have hv : v ∈ T ∩ convexHull ℝ (f : Set (E d)) := by
      rw [heq]; exact right_mem_segment ℝ u v
    refine ⟨hu, ?_⟩
    by_contra hn
    push_neg at hn
    have hevT :=
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step11_extend
        t (ht.symm ▸ hu.1) (ht.symm ▸ hv.1) (fun w hw hmem => hn.1 (hdelete w hw hmem))
    have hevf :=
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step11_extend
        f hu.2 hv.2 (by
          intro w hw hmem
          have hcard : (f.erase w).card = d - 1 := by rw [Finset.card_erase_of_mem hw, hpure f hf]
          have hd : 2 ≤ d := Fact.out
          have hs : f.erase w ∈ K.faces := K.down_closed hf.1 (Finset.erase_subset _ _)
            (Finset.card_pos.mp (by omega))
          exact hn.2 (f.erase w) hs hcard (Finset.erase_subset _ _) hmem)
    obtain ⟨δ, hδ, hδmem⟩ := Metric.eventually_nhds_iff.mp (hevT.and hevf)
    have hneg : -(δ / 2) < (0 : ℝ) := by linarith
    have hz := hδmem (show dist (-(δ / 2)) (0 : ℝ) < δ by
      rw [Real.dist_eq, sub_zero, abs_of_neg hneg]
      linarith)
    rw [ht] at hz
    have hzseg : AffineMap.lineMap u v (-(δ / 2)) ∈ segment ℝ u v := heq ▸ hz
    rw [segment_eq_image_lineMap] at hzseg
    obtain ⟨r, hr, he⟩ := hzseg
    have he' := AffineMap.lineMap_injective ℝ huv he
    linarith [hr.1]
  constructor
  · rintro (hx | hx)
    · subst x
      exact endpoint p q hne hcut
    · subst x
      exact endpoint q p hne.symm (hcut.trans (segment_symm ℝ p q))
  · rintro ⟨hx, hkind⟩
    by_contra hn
    push_neg at hn
    have hxseg : x ∈ segment ℝ p q := hcut ▸ hx
    have hxopen : x ∈ openSegment ℝ p q :=
      mem_openSegment_of_ne_left_right hn.1.symm hn.2.symm hxseg
    rcases hkind with hxD | ⟨s, hs, hsc, hsf, hxs⟩
    · have htri : AffineIndependent ℝ ((↑) : t → E d) := by
        have hr : Set.range ![a, b, c] = (t : Set (E d)) := by
          ext z
          simp [t, Matrix.range_cons, or_comm, or_left_comm, or_assoc]
        have ha : AffineIndependent ℝ ![a, b, c] := hpos.1
        have hai := ha.range
        rw [hr] at hai
        exact hai
      have hface (u v : E d) (hsub : ({u, v} : Finset (E d)) ⊆ t) :
          IsExtreme ℝ T (segment ℝ u v) := by
        have h :=
          principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step10_simplex_faces
            t {u, v} htri hsub
        simpa only [ht, Finset.coe_insert, Finset.coe_singleton, convexHull_pair] using h
      have hinf : (segment ℝ p q).Infinite := by
        rw [segment_eq_image_lineMap]
        exact (Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num)).image
          (AffineMap.lineMap_injective ℝ hne).injOn
      have impossible (u v : E d) (hext : IsExtreme ℝ T (segment ℝ u v))
          (hfinite : (segment ℝ u v ∩ K.space).Finite) (hxuv : x ∈ segment ℝ u v) : False := by
        have hpuv := hext.left_mem_of_mem_openSegment hp.1 hq.1 hxuv hxopen
        have hquv := hext.right_mem_of_mem_openSegment hp.1 hq.1 hxuv hxopen
        apply hinf
        apply hfinite.subset
        intro z hz
        exact ⟨(convex_segment u v).segment_subset hpuv hquv hz,
          K.convexHull_subset_space hf.1 ((hcut.symm ▸ hz).2)⟩
      rcases hxD with (hab | hbc) | hca
      · exact impossible a b (hface a b (by simp [t])) hpos.2.1.2.2.1 hab
      · exact impossible b c (hface b c (by simp [t])) hpos.2.2.1.2.2.1 hbc
      · exact impossible c a (hface c a (by
          intro z hz
          simp only [t, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
          tauto)) hpos.2.2.2.1.2.2.1 hca
    · have hext :=
        principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step10_simplex_faces
          f s (K.indep hf.1) hsf
      have hps := hext.left_mem_of_mem_openSegment hp.2 hq.2 hxs hxopen
      have hqs := hext.right_mem_of_mem_openSegment hp.2 hq.2 hxs hxopen
      exact hne (hpos.2.2.2.2.2.2.2.1 s hs hsc ⟨x, hx.1, hxs⟩
        ⟨convexHull_subset_affineSpan _ hp.1, convexHull_subset_affineSpan _ hps⟩
        ⟨convexHull_subset_affineSpan _ hq.1, convexHull_subset_affineSpan _ hqs⟩)

/-- Step 13 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"in general position". Two distinct facet sections meet in at most one point:
their common face is either avoided by the triangle or is a transverse ridge. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step13_intersections
    (K : Geometry.SimplicialComplex ℝ (E d))
    (hpure : ∀ f ∈ K.facets, f.card = d)
    {a b c : E d}
    (hpos : principal_component_step1_hull_geometry_step10_jordan_brouwer_step13_TrianglePosition K a b c)
    {f g : Finset (E d)} (hf : f ∈ K.facets) (hg : g ∈ K.facets) (hne : f ≠ g) :
    (convexHull ℝ ({a, b, c} : Set (E d)) ∩
      (convexHull ℝ (f : Set (E d)) ∩ convexHull ℝ (g : Set (E d)))).Subsingleton := by
  classical
  intro x hx y hy
  let s := f ∩ g
  have hxs : x ∈ convexHull ℝ (s : Set (E d)) := by
    simpa only [s, Finset.coe_inter] using K.inter_subset_convexHull hf.1 hg.1 hx.2
  have hys : y ∈ convexHull ℝ (s : Set (E d)) := by
    simpa only [s, Finset.coe_inter] using K.inter_subset_convexHull hf.1 hg.1 hy.2
  have hsne : s.Nonempty := convexHull_nonempty_iff.mp ⟨x, hxs⟩
  have hs : s ∈ K.faces := K.down_closed hf.1 Finset.inter_subset_left hsne
  have hcard : s.card < d := by
    have hle : s.card ≤ f.card := Finset.card_le_card Finset.inter_subset_left
    have hnf : s ≠ f := by
      intro he
      have hfg : f ⊆ g := he ▸ (Finset.inter_subset_right : s ⊆ g)
      exact hne (hf.2 hg.1 hfg)
    have hlt : s.card < f.card := lt_of_le_of_ne hle fun he =>
      hnf (Finset.eq_of_subset_of_card_le Finset.inter_subset_left he.ge)
    simpa only [hpure f hf] using hlt
  have hdim : s.card = d - 1 := by
    by_contra hn
    have hsmall : s.card + 1 < d := by omega
    exact Set.disjoint_left.mp (hpos.2.2.2.2.2.2.1 s hs hsmall) hx.1 hxs
  exact hpos.2.2.2.2.2.2.2.1 s hs hdim ⟨x, hx.1, hxs⟩
    ⟨convexHull_subset_affineSpan _ hx.1, convexHull_subset_affineSpan _ hxs⟩
    ⟨convexHull_subset_affineSpan _ hy.1, convexHull_subset_affineSpan _ hys⟩

/-- Step 14 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"crosses them transversally". A triangle boundary crossing belongs to precisely
one facet, since each regular side crosses a relative facet interior. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step14_boundary_facet
    (K : Geometry.SimplicialComplex ℝ (E d)) {a b c : E d}
    (hpos : principal_component_step1_hull_geometry_step10_jordan_brouwer_step13_TrianglePosition K a b c)
    {x : E d} (hxK : x ∈ K.space)
    (hxD : x ∈ segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a) :
    ∃ f ∈ K.facets, x ∈ convexHull ℝ (f : Set (E d)) ∧
      ∀ g ∈ K.facets, x ∈ convexHull ℝ (g : Set (E d)) → g = f := by
  have hx : ∃ f ∈ K.facets, x ∈ relint (convexHull ℝ (f : Set (E d))) := by
    rcases hxD with (hab | hbc) | hca
    · obtain ⟨f, hf, hx, -⟩ := hpos.2.1.2.2.2 x ⟨hab, hxK⟩
      exact ⟨f, hf, hx⟩
    · obtain ⟨f, hf, hx, -⟩ := hpos.2.2.1.2.2.2 x ⟨hbc, hxK⟩
      exact ⟨f, hf, hx⟩
    · obtain ⟨f, hf, hx, -⟩ := hpos.2.2.2.1.2.2.2 x ⟨hca, hxK⟩
      exact ⟨f, hf, hx⟩
  obtain ⟨f, hf, hx⟩ := hx
  refine ⟨f, hf, intrinsicInterior_subset hx, ?_⟩
  intro g hg hxg
  exact (hf.2 hg.1
    (principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step3_relint_incidence
      K hf.1 hg.1 hx hxg)).symm

/-- Step 15 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"each crossed ridge has exactly two incident facets". At a point where the
triangle meets a ridge, the facets containing the point are precisely the
facets containing that ridge. A smaller intersection face is excluded by
general position. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step15_ridge_incidence
    (K : Geometry.SimplicialComplex ℝ (E d)) {a b c : E d}
    (hpos : principal_component_step1_hull_geometry_step10_jordan_brouwer_step13_TrianglePosition K a b c)
    {s : Finset (E d)} (hs : s ∈ K.faces) (hsc : s.card = d - 1)
    {x : E d} (hxT : x ∈ convexHull ℝ ({a, b, c} : Set (E d)))
    (hxs : x ∈ convexHull ℝ (s : Set (E d)))
    {f : Finset (E d)} (hf : f ∈ K.facets) :
    x ∈ convexHull ℝ (f : Set (E d)) ↔ s ⊆ f := by
  classical
  refine ⟨fun hxf => ?_, fun hsf => convexHull_mono (by simpa using hsf) hxs⟩
  by_contra hns
  let t := s ∩ f
  have hxt : x ∈ convexHull ℝ (t : Set (E d)) := by
    simpa only [t, Finset.coe_inter] using K.inter_subset_convexHull hs hf.1 ⟨hxs, hxf⟩
  have ht : t ∈ K.faces := K.down_closed hs Finset.inter_subset_left
    (convexHull_nonempty_iff.mp ⟨x, hxt⟩)
  have hne : t ≠ s := by
    intro he
    exact hns (he ▸ (Finset.inter_subset_right : t ⊆ f))
  have hlt : t.card < s.card := lt_of_le_of_ne (Finset.card_le_card Finset.inter_subset_left)
    fun he => hne (Finset.eq_of_subset_of_card_le Finset.inter_subset_left he.ge)
  have hsmall : t.card + 1 < d := by omega
  exact Set.disjoint_left.mp (hpos.2.2.2.2.2.2.1 t ht hsmall) hxT hxt

/-- Step 16 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph` (V4 1.24):
"crosses them transversally at finitely many points". A finite family of
nondegenerate segments with distinct unordered endpoint pairs defines a simple
graph. Its vertex degrees count incident members of the family. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step16_realize
    {ι : Type*} [Fintype ι] (p q : ι → E d)
    (hne : ∀ f, p f ≠ q f)
    (huniq : ∀ f g, (p f = p g ∧ q f = q g) ∨ (p f = q g ∧ q f = p g) → f = g) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n → E d),
      Function.Injective v ∧
      Set.range v = Set.range p ∪ Set.range q ∧
      (⋃ (i : Fin n) (j : Fin n) (_ : G.Adj i j), segment ℝ (v i) (v j)) =
        ⋃ f, segment ℝ (p f) (q f) ∧
      ∀ i, (G.neighborSet i).ncard = {f | v i = p f ∨ v i = q f}.ncard := by
  classical
  let V := Set.range p ∪ Set.range q
  have hV : V.Finite := (Set.finite_range p).union (Set.finite_range q)
  letI : Fintype V := hV.fintype
  let n := Fintype.card V
  let e : Fin n ≃ V := (Fintype.equivFin V).symm
  let v : Fin n → E d := fun i => (e i).val
  have hv : Function.Injective v := Subtype.val_injective.comp e.injective
  have hrange : Set.range v = V := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp [v]⟩
  let G : SimpleGraph (Fin n) :=
    { Adj := fun i j => ∃ f, (v i = p f ∧ v j = q f) ∨ (v i = q f ∧ v j = p f)
      symm := by
        rintro i j ⟨f, h | h⟩
        · exact ⟨f, Or.inr ⟨h.2, h.1⟩⟩
        · exact ⟨f, Or.inl ⟨h.2, h.1⟩⟩
      loopless := by
        constructor
        rintro i ⟨f, h | h⟩
        · exact hne f (h.1.symm.trans h.2)
        · exact hne f (h.2.symm.trans h.1) }
  refine ⟨n, G, v, hv, hrange, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hij, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨f, h | h⟩ := hij
      · exact Set.mem_iUnion.mpr ⟨f, by simpa only [h.1, h.2] using hx⟩
      · exact Set.mem_iUnion.mpr ⟨f, by simpa only [h.1, h.2, segment_symm ℝ] using hx⟩
    · intro hx
      obtain ⟨f, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨i, hi⟩ := hrange.symm.subset (Or.inl ⟨f, rfl⟩)
      obtain ⟨j, hj⟩ := hrange.symm.subset (Or.inr ⟨f, rfl⟩)
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j,
        Set.mem_iUnion.mpr ⟨⟨f, Or.inl ⟨hi, hj⟩⟩, by simpa only [hi, hj] using hx⟩⟩⟩
  · intro i
    let I : Set ι := {f | v i = p f ∨ v i = q f}
    let w : ι → Fin n := fun f =>
      e.symm ⟨if v i = p f then q f else p f, by
        split_ifs
        · exact Or.inr ⟨f, rfl⟩
        · exact Or.inl ⟨f, rfl⟩⟩
    have hw (f : ι) : v (w f) = if v i = p f then q f else p f := by
      simp [v, w]
    have himage : G.neighborSet i = w '' I := by
      ext j
      constructor
      · rintro ⟨f, h | h⟩
        · refine ⟨f, Or.inl h.1, hv ?_⟩
          simp only [hw, if_pos h.1, h.2]
        · refine ⟨f, Or.inr h.1, hv ?_⟩
          have hn : v i ≠ p f := fun he => hne f (he.symm.trans h.1)
          simp only [hw, if_neg hn, h.2]
      · rintro ⟨f, hf, rfl⟩
        rcases hf with hf | hf
        · exact ⟨f, Or.inl ⟨hf, by simpa only [hw, if_pos hf]⟩⟩
        · have hn : v i ≠ p f := fun he => hne f (he.symm.trans hf)
          exact ⟨f, Or.inr ⟨hf, by simpa only [hw, if_neg hn]⟩⟩
    have hinj : Set.InjOn w I := by
      intro f hf g hg heq
      have he := congrArg v heq
      rw [hw, hw] at he
      apply huniq f g
      rcases hf with hf | hf <;> rcases hg with hg | hg
      · exact Or.inl ⟨hf.symm.trans hg, by simpa only [if_pos hf, if_pos hg] using he⟩
      · have hng : v i ≠ p g := fun h => hne g (h.symm.trans hg)
        exact Or.inr ⟨hf.symm.trans hg, by simpa only [if_pos hf, if_neg hng] using he⟩
      · have hnf : v i ≠ p f := fun h => hne f (h.symm.trans hf)
        exact Or.inr ⟨by simpa only [if_neg hnf, if_pos hg] using he, hf.symm.trans hg⟩
      · have hnf : v i ≠ p f := fun h => hne f (h.symm.trans hf)
        have hng : v i ≠ p g := fun h => hne g (h.symm.trans hg)
        exact Or.inl ⟨by simpa only [if_neg hnf, if_neg hng] using he, hf.symm.trans hg⟩
    rw [himage, hinj.ncard_image]


/-- Step 18 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"crosses them transversally at finitely many points". Slice the simplices by one
generic filled triangle. The slice is a finite embedded graph: crossings on the
triangle boundary have degree one, and interior vertices have degree two, since
each crossed ridge has exactly two incident facets. This is a finite affine
intersection calculation; no complementary components occur in its statement. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d)
    (hridge : ∀ s ∈ K.faces, s.card = d - 1 → {f ∈ K.facets | s ⊆ f}.ncard = 2)
    {a b c : E d}
    (hpos : principal_component_step1_hull_geometry_step10_jordan_brouwer_step13_TrianglePosition K a b c) :
    let T := convexHull ℝ ({a, b, c} : Set (E d))
    let D := segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n → E d),
      Function.Injective v ∧
      (∀ i, v i ∈ T ∩ K.space) ∧
      (T ∩ K.space = ⋃ (i : Fin n) (j : Fin n) (_ : G.Adj i j), segment ℝ (v i) (v j)) ∧
      (Set.range v ∩ D = K.space ∩ D) ∧
      (∀ i, v i ∈ D → (G.neighborSet i).ncard = 1) ∧
      (∀ i, v i ∉ D → (G.neighborSet i).ncard = 2) := by
  classical
  let T := convexHull ℝ ({a, b, c} : Set (E d))
  let D := segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a
  let F := {f : Finset (E d) // f ∈ K.facets ∧
    (T ∩ convexHull ℝ (f : Set (E d))).Nonempty}
  have hFfin : {f | f ∈ K.facets ∧
      (T ∩ convexHull ℝ (f : Set (E d))).Nonempty}.Finite :=
    hfin.subset fun f hf => hf.1.1
  letI : Fintype F := hFfin.fintype
  have hsegments (f : F) : ∃ p q : E d, p ≠ q ∧
      T ∩ convexHull ℝ (f.val : Set (E d)) = segment ℝ p q :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step9_facet_segment
      K hpure hpos f.property.1 f.property.2
  choose p q hne hcut using hsegments
  have hp (f : F) : p f ∈ T ∩ convexHull ℝ (f.val : Set (E d)) := by
    rw [hcut f]
    exact left_mem_segment ℝ _ _
  have hq (f : F) : q f ∈ T ∩ convexHull ℝ (f.val : Set (E d)) := by
    rw [hcut f]
    exact right_mem_segment ℝ _ _
  have hend (f : F) (x : E d) : (x = p f ∨ x = q f) ↔
      x ∈ T ∩ convexHull ℝ (f.val : Set (E d)) ∧
        (x ∈ D ∨ ∃ s ∈ K.faces, s.card = d - 1 ∧ s ⊆ f.val ∧
          x ∈ convexHull ℝ (s : Set (E d))) :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step12_endpoints
      K hpure hpos f.property.1 (hne f) (hcut f) x
  have huniq (f g : F)
      (hfg : (p f = p g ∧ q f = q g) ∨ (p f = q g ∧ q f = p g)) : f = g := by
    apply Subtype.ext
    by_contra hfg'
    have hpg : p f ∈ T ∩ convexHull ℝ (g.val : Set (E d)) := by
      rcases hfg with h | h
      · rw [h.1]; exact hp g
      · rw [h.1]; exact hq g
    have hqg : q f ∈ T ∩ convexHull ℝ (g.val : Set (E d)) := by
      rcases hfg with h | h
      · rw [h.2]; exact hq g
      · rw [h.2]; exact hp g
    exact hne f
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step13_intersections
        K hpure hpos f.property.1 g.property.1 hfg'
        ⟨(hp f).1, (hp f).2, hpg.2⟩ ⟨(hq f).1, (hq f).2, hqg.2⟩)
  obtain ⟨n, G, v, hinj, hrange, hreal, hdegree⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step16_realize
      p q hne huniq
  have hvertex {x : E d} (hx : x ∈ Set.range v) : x ∈ T ∩ K.space := by
    rw [hrange] at hx
    rcases hx with ⟨f, rfl⟩ | ⟨f, rfl⟩
    · exact ⟨(hp f).1, K.convexHull_subset_space f.property.1.1 (hp f).2⟩
    · exact ⟨(hq f).1, K.convexHull_subset_space f.property.1.1 (hq f).2⟩
  have hcover : T ∩ K.space = ⋃ f : F, segment ℝ (p f) (q f) := by
    ext x
    constructor
    · rintro ⟨hxT, hxK⟩
      rw [principal_component_step1_hull_geometry_step10_jordan_brouwer_step9_facets_cover K hfin] at hxK
      obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hxK
      let g : F := ⟨f.val, f.property, ⟨x, hxT, hxf⟩⟩
      exact Set.mem_iUnion.mpr ⟨g, by rw [← hcut g]; exact ⟨hxT, hxf⟩⟩
    · intro hx
      obtain ⟨f, hx⟩ := Set.mem_iUnion.mp hx
      rw [← hcut f] at hx
      exact ⟨hx.1, K.convexHull_subset_space f.property.1.1 hx.2⟩
  have hDT : D ⊆ T := by
    intro x hx
    have ha : a ∈ T := subset_convexHull ℝ _ (by simp)
    have hb : b ∈ T := subset_convexHull ℝ _ (by simp)
    have hc : c ∈ T := subset_convexHull ℝ _ (by simp)
    rcases hx with (hx | hx) | hx
    · exact (convex_convexHull ℝ _).segment_subset ha hb hx
    · exact (convex_convexHull ℝ _).segment_subset hb hc hx
    · exact (convex_convexHull ℝ _).segment_subset hc ha hx
  refine ⟨n, G, v, hinj, fun i => hvertex ⟨i, rfl⟩, hcover.trans hreal.symm, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hx, hxD⟩
      exact ⟨(hvertex hx).2, hxD⟩
    · rintro ⟨hxK, hxD⟩
      obtain ⟨f, hf, hxf, -⟩ :=
        principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step14_boundary_facet
          K hpos hxK hxD
      let g : F := ⟨f, hf, ⟨x, hDT hxD, hxf⟩⟩
      have hxend := (hend g x).mpr ⟨⟨hDT hxD, hxf⟩, Or.inl hxD⟩
      refine ⟨?_, hxD⟩
      rw [hrange]
      rcases hxend with hx | hx
      · exact Or.inl ⟨g, hx.symm⟩
      · exact Or.inr ⟨g, hx.symm⟩
  · intro i hi
    have hxi := hvertex ⟨i, rfl⟩
    obtain ⟨f, hf, hxf, hfu⟩ :=
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step14_boundary_facet
        K hpos hxi.2 hi
    let g : F := ⟨f, hf, ⟨v i, hxi.1, hxf⟩⟩
    have heq : {f : F | v i = p f ∨ v i = q f} = {g} := by
      ext u
      constructor
      · intro hu
        apply Set.mem_singleton_iff.mpr
        apply Subtype.ext
        exact hfu u.val u.property.1 ((hend u (v i)).mp hu).1.2
      · intro hu
        have : u = g := Set.mem_singleton_iff.mp hu
        subst u
        exact (hend g (v i)).mpr ⟨⟨hxi.1, hxf⟩, Or.inl hi⟩
    rw [hdegree i, heq, Set.ncard_singleton]
  · intro i hi
    have hxi := hvertex ⟨i, rfl⟩
    have hxrange : v i ∈ Set.range p ∪ Set.range q := hrange ▸ Set.mem_range_self i
    obtain ⟨f, hxf⟩ : ∃ f : F, v i = p f ∨ v i = q f := by
      rcases hxrange with ⟨f, hf⟩ | ⟨f, hf⟩
      · exact ⟨f, Or.inl hf.symm⟩
      · exact ⟨f, Or.inr hf.symm⟩
    obtain ⟨s, hs, hsc, hsf, hxs⟩ := ((hend f (v i)).mp hxf).2.resolve_left hi
    have himage : (Subtype.val : F → Finset (E d)) '' {f : F | v i = p f ∨ v i = q f} =
        {g ∈ K.facets | s ⊆ g} := by
      ext u
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨g.property.1,
          (principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph_step15_ridge_incidence
            K hpos hs hsc hxi.1 hxs g.property.1).mp ((hend g (v i)).mp hg).1.2⟩
      · rintro ⟨hu, hsu⟩
        have hxu : v i ∈ convexHull ℝ (u : Set (E d)) :=
          convexHull_mono (by simpa using hsu) hxs
        let g : F := ⟨u, hu, ⟨v i, hxi.1, hxu⟩⟩
        exact ⟨g, (hend g (v i)).mpr
          ⟨⟨hxi.1, hxu⟩, Or.inr ⟨s, hs, hsc, hsu, hxs⟩⟩, rfl⟩
    rw [hdegree i, ← Set.ncard_image_of_injective _ (Subtype.val_injective :
      Function.Injective (Subtype.val : F → Finset (E d))), himage]
    exact hridge s hs hsc

/-- Step 19 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"separating `ℝᵈ`". The handshaking lemma makes the boundary of a finite section
graph even: degree one vertices are its boundary and all other degrees are two. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step19_handshake
    {X : Type*} {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → X)
    (hinj : Function.Injective v) (D : Set X)
    (hodd : ∀ i, Odd (G.neighborSet i).ncard ↔ v i ∈ D) :
    Even (Set.range v ∩ D).ncard := by
  classical
  have hdegree (i : Fin n) : (G.neighborSet i).ncard = G.degree i := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have heq : Set.range v ∩ D = v '' {i | Odd (G.degree i)} := by
    ext x
    constructor
    · rintro ⟨⟨i, rfl⟩, hi⟩
      exact ⟨i, by change Odd (G.degree i); rw [← hdegree]; exact (hodd i).mpr hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, rfl⟩, (hodd i).mp (by rwa [hdegree])⟩
  rw [heq, Set.ncard_image_of_injective _ hinj, Set.ncard_eq_toFinset_card']
  simpa using G.even_card_odd_degree_vertices

/-- Step 20 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"separating `ℝᵈ`". Apply handshaking to a triangular section. Its three finite
sets of boundary crossings are disjoint, so their total cardinality is even. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step20_triangle_parity
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d)
    (hridge : ∀ s ∈ K.faces, s.card = d - 1 → {f ∈ K.facets | s ⊆ f}.ncard = 2)
    {a b c : E d}
    (hpos : principal_component_step1_hull_geometry_step10_jordan_brouwer_step13_TrianglePosition K a b c) :
    Even ((segment ℝ a b ∩ K.space).ncard + (segment ℝ b c ∩ K.space).ncard +
      (segment ℝ c a ∩ K.space).ncard) := by
  obtain ⟨n, G, v, hinj, -, -, hboundary, hdeg1, hdeg2⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step18_section_graph
      K hfin hpure hridge hpos
  have h := principal_component_step1_hull_geometry_step10_jordan_brouwer_step19_handshake
    G v hinj (segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a) (by
      intro i
      by_cases hi : v i ∈ segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a
      · rw [hdeg1 i hi]; simp [hi]
      · rw [hdeg2 i hi]; simp [hi])
  rw [hboundary] at h
  have hsplit : K.space ∩ (segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a) =
      (segment ℝ a b ∩ K.space) ∪ (segment ℝ b c ∩ K.space) ∪
        (segment ℝ c a ∩ K.space) := by aesop
  rw [hsplit, Set.ncard_union_eq hpos.2.2.2.2.2.1
      (hpos.2.1.2.2.1.union hpos.2.2.1.2.2.1) hpos.2.2.2.1.2.2.1,
    Set.ncard_union_eq hpos.2.2.2.2.1 hpos.2.1.2.2.1 hpos.2.2.1.2.2.1] at h
  exact h

/-- Step 1 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan` (V4 1.24):
"in general position". A set of at most `d` vertices has a proper affine span in `E d`. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step1_proper_span (s : Finset (E d)) (hc : s.card ≤ d) :
    affineSpan ℝ (s : Set (E d)) ≠ ⊤ := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  haveI : Nonempty s := hs.to_subtype
  have hdim := finrank_vectorSpan_range_add_one_le ℝ ((↑) : s → E d)
  have hrange : Set.range ((↑) : s → E d) = (s : Set (E d)) := by
    ext x
    simp
  rw [hrange, Fintype.card_coe] at hdim
  intro htop
  have hdir := congrArg AffineSubspace.direction htop
  rw [direction_affineSpan, AffineSubspace.direction_top] at hdir
  rw [hdir, finrank_top, finrank_euclideanSpace, Fintype.card_fin] at hdim
  omega

/-- Step 2 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan` (V4 1.24):
"in general position". The complement of a proper affine subspace is open and dense. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step2_dense_compl (A : AffineSubspace ℝ (E d)) (hA : A ≠ ⊤) :
    IsOpen (A : Set (E d))ᶜ ∧ Dense (A : Set (E d))ᶜ := by
  refine ⟨A.closed_of_finiteDimensional.isOpen_compl, ?_⟩
  apply interior_eq_empty_iff_dense_compl.mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  apply hA
  apply top_unique
  rw [← isOpen_interior.affineSpan_eq_top ⟨p, hp⟩]
  exact affineSpan_le.mpr interior_subset

/-- Step 3 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan` (V4 1.24):
"in general position". Intersect the finitely many open dense sets of permitted cone
vertices. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step3_finite_conditions {ι : Type*} [Finite ι] (P : ι → E d → Prop)
    (hP : ∀ i, ∃ U : Set (E d), IsOpen U ∧ Dense U ∧ ∀ z ∈ U, P i z) :
    ∃ U : Set (E d), IsOpen U ∧ Dense U ∧ ∀ z ∈ U, ∀ i, P i z := by
  classical
  choose U hU hdU hUP using hP
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite hU, dense_iInter_of_isOpen hU hdU, ?_⟩
  intro z hz i
  exact hUP i z (Set.mem_iInter.mp hz i)

/-- Step 4 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan` (V4 1.24):
"in general position". A segment from an affine subspace to a point outside it meets that
subspace only at its initial endpoint. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step4_segment_span (A : AffineSubspace ℝ (E d)) {p z x : E d}
    (hp : p ∈ A) (hz : z ∉ A) (hx : x ∈ segment ℝ p z) (hxA : x ∈ A) : x = p := by
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  by_cases ht0 : t = 0
  · simp [ht0]
  · exfalso
    apply hz
    have h := AffineMap.lineMap_mem t⁻¹ hp hxA
    simpa [AffineMap.lineMap_lineMap_right, ht0] using h

/-- Step 5 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan` (V4 1.24):
"in general position". A segment with one endpoint outside an affine subspace meets that
subspace in at most one point. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step5_segment_inter_subsingleton (A : AffineSubspace ℝ (E d)) {p z : E d}
    (hz : z ∉ A) : (segment ℝ p z ∩ (A : Set (E d))).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hcol : Collinear ℝ {x, y, z} := by
    apply collinear_triple_of_mem_affineSpan_pair (p₄ := p) (p₅ := z)
    · exact convexHull_subset_affineSpan _ (by simpa [convexHull_pair] using hx.1)
    · exact convexHull_subset_affineSpan _ (by simpa [convexHull_pair] using hy.1)
    · exact right_mem_affineSpan_pair ℝ p z
  apply hz
  exact (affineSpan_le.mpr (Set.pair_subset hx.2 hy.2))
    (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy)

/-- Step 6 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan` (V4 1.24):
"in general position". Avoiding facet spans and the spans obtained by adjoining the fixed
endpoint to smaller faces makes the new segment regular. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step6_regular_from_avoid
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d) {p z : E d}
    (hp : p ∉ K.space)
    (hz : ∀ f ∈ K.facets, z ∉ affineSpan ℝ (f : Set (E d)))
    (hsmall : ∀ s ∈ K.faces, s.card < d →
      z ∉ affineSpan ℝ (insert p (s : Set (E d)))) :
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step12_RegularSegment K p z := by
  have hzK : z ∉ K.space := by
    intro hzK
    rw [principal_component_step1_hull_geometry_step10_jordan_brouwer_step9_facets_cover K hfin] at hzK
    obtain ⟨f, hzf⟩ := Set.mem_iUnion.mp hzK
    exact hz f.val f.property (convexHull_subset_affineSpan _ hzf)
  have hfinite : (segment ℝ p z ∩ K.space).Finite := by
    rw [principal_component_step1_hull_geometry_step10_jordan_brouwer_step9_facets_cover K hfin,
      Set.inter_iUnion]
    haveI : Finite K.facets := (hfin.subset (fun _ h => h.1)).to_subtype
    apply Set.finite_iUnion
    intro f
    exact (principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step5_segment_inter_subsingleton (affineSpan ℝ (f.val : Set (E d)))
      (hz f.val f.property)).finite.subset (Set.inter_subset_inter_right _ (convexHull_subset_affineSpan _))
  refine ⟨hp, hzK, hfinite, ?_⟩
  intro x hx
  have hxp : x ≠ p := by rintro rfl; exact hp hx.2
  obtain ⟨f, hxf⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet_step2_lower_skeleton
      K hfin hpure hx.2 (by
        intro s hs hc hxs
        have h := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step4_segment_span (affineSpan ℝ (insert p (s : Set (E d))))
          (subset_affineSpan ℝ _ (Set.mem_insert p _)) (hsmall s hs hc) hx.1
          (affineSpan_mono ℝ (Set.subset_insert p _) hxs)
        exact hxp h)
  refine ⟨f.val, f.property, hxf, ?_, hz f.val f.property⟩
  intro hpf
  exact hxp (principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step4_segment_span (affineSpan ℝ (f.val : Set (E d))) hpf
    (hz f.val f.property) hx.1 (convexHull_subset_affineSpan _ (intrinsicInterior_subset hxf)))

/-- Step 7 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan` (V4 1.24):
"in general position". A regular segment misses every face of positive codimension inside
the pure complex. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step7_regular_avoids_face
    (K : Geometry.SimplicialComplex ℝ (E d))
    (hpure : ∀ f ∈ K.facets, f.card = d) {a b : E d}
    (hab : principal_component_step1_hull_geometry_step10_jordan_brouwer_step12_RegularSegment K a b)
    {s : Finset (E d)} (hs : s ∈ K.faces) (hc : s.card < d) :
    Disjoint (segment ℝ a b) (convexHull ℝ (s : Set (E d))) := by
  apply Set.disjoint_left.mpr
  intro x hx hxs
  obtain ⟨f, hf, hxf, -⟩ := hab.2.2.2 x ⟨hx, K.convexHull_subset_space hs hxs⟩
  have hfs := principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport_step1_interior_incidence
    K hf.1 hs hxf hxs
  have hle := Finset.card_le_card hfs
  rw [hpure f hf] at hle
  omega

/-- Step 8 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan` (V4 1.24):
"in general position". If an affine subspace contains the base and the obstacle, a cone
vertex outside it cannot create an intersection with the obstacle. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step8_triangle_avoids (C : Set (E d)) (A : AffineSubspace ℝ (E d))
    {a b z : E d} (ha : a ∈ A) (hb : b ∈ A) (hC : C ⊆ A)
    (hz : z ∉ A) (hab : Disjoint (segment ℝ a b) C) :
    Disjoint (convexHull ℝ ({a, b, z} : Set (E d))) C := by
  apply Set.disjoint_left.mpr
  intro x hx hxC
  have heq : ({a, b, z} : Set (E d)) = insert z {a, b} := by ext; simp; tauto
  rw [heq, convexHull_insert (Set.insert_nonempty a {b}), convexHull_pair,
    convexJoin_singleton_left] at hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
  have hxy' := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step4_segment_span A (A.convex.segment_subset ha hb hy) hz
    (by simpa only [segment_symm] using hxy) (hC hxC)
  exact Set.disjoint_left.mp hab (hxy'.symm ▸ hy) hxC

/-- Step 9 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan` (V4 1.24):
"in general position". For a fixed endpoint outside the complex, an open dense set of second
endpoints gives regular segments and avoids all facet spans. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step9_regular_open
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d) (p : E d) (hp : p ∉ K.space) :
    ∃ U : Set (E d), IsOpen U ∧ Dense U ∧ ∀ z ∈ U,
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step12_RegularSegment K p z ∧
      ∀ f ∈ K.facets, z ∉ affineSpan ℝ (f : Set (E d)) := by
  classical
  haveI : Finite K.faces := hfin.to_subtype
  obtain ⟨U, hU, hdU, hUP⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step3_finite_conditions
    (fun (s : K.faces) z => z ∉ affineSpan ℝ (s.val : Set (E d)) ∧
      (s.val.card < d → z ∉ affineSpan ℝ (insert p (s.val : Set (E d))))) (by
        intro s
        obtain ⟨f, hf, hsf⟩ :=
          principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree_step1_facet_extension
            K hfin s.property
        have hc : s.val.card ≤ d := (Finset.card_le_card hsf).trans_eq (hpure f hf)
        obtain ⟨hA, hdA⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step2_dense_compl (affineSpan ℝ (s.val : Set (E d))) (principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step1_proper_span s.val hc)
        by_cases hs : s.val.card < d
        · have hi : (insert p s.val).card ≤ d := (Finset.card_insert_le p s.val).trans (by omega)
          obtain ⟨hB, hdB⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step2_dense_compl (affineSpan ℝ (insert p (s.val : Set (E d))))
            (by simpa only [Finset.coe_insert] using principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step1_proper_span (insert p s.val) hi)
          exact ⟨_, hA.inter hB, hdA.inter_of_isOpen_right hdB hB,
            fun z hz => ⟨hz.1, fun _ => hz.2⟩⟩
        · exact ⟨_, hA, hdA, fun z hz => ⟨hz, fun hc => (hs hc).elim⟩⟩)
  refine ⟨U, hU, hdU, ?_⟩
  intro z hz
  have hf : ∀ f ∈ K.facets, z ∉ affineSpan ℝ (f : Set (E d)) :=
    fun f hf => (hUP z hz ⟨f, hf.1⟩).1
  exact ⟨principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step6_regular_from_avoid K hfin hpure hp hf
    (fun s hs hc => (hUP z hz ⟨s, hs⟩).2 hc), hf⟩

/-- Step 10 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan` (V4 1.24):
"in general position". When the base direction is parallel to a ridge, avoid its affine join
with the base; otherwise avoid the sum of the ridge and base direction spaces. These
conditions give transverse triangular sections. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step10_ridge_open (s : Finset (E d)) (hs : s.Nonempty) (hc : s.card < d)
    {a b : E d} (hab : Disjoint (segment ℝ a b) (convexHull ℝ (s : Set (E d)))) :
    ∃ U : Set (E d), IsOpen U ∧ Dense U ∧ ∀ z ∈ U,
      (convexHull ℝ ({a, b, z} : Set (E d)) ∩ convexHull ℝ (s : Set (E d))).Nonempty →
      ((affineSpan ℝ ({a, b, z} : Set (E d)) : Set (E d)) ∩
        (affineSpan ℝ (s : Set (E d)) : Set (E d))).Subsingleton := by
  classical
  let H := affineSpan ℝ (s : Set (E d))
  by_cases hw : b - a ∈ H.direction
  · let B := affineSpan ℝ (insert a (s : Set (E d)))
    have hBproper : B ≠ ⊤ := by
      simpa only [B, Finset.coe_insert] using
        principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step1_proper_span (insert a s) (by have := Finset.card_insert_le a s; omega)
    obtain ⟨hB, hdB⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step2_dense_compl B hBproper
    have hHB : H ≤ B := affineSpan_mono ℝ (Set.subset_insert a _)
    have haB : a ∈ B := subset_affineSpan ℝ _ (Set.mem_insert a _)
    have hbB : b ∈ B := by
      have h := B.vadd_mem_of_mem_direction (AffineSubspace.direction_le hHB hw) haB
      simpa only [vadd_eq_add, sub_add_cancel] using h
    refine ⟨(B : Set (E d))ᶜ, hB, hdB, ?_⟩
    intro z hz hcut
    have hd := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step8_triangle_avoids (convexHull ℝ (s : Set (E d))) B haB hbB
      ((convexHull_subset_affineSpan _).trans hHB) hz hab
    obtain ⟨x, hx, hxs⟩ := hcut
    exact (Set.disjoint_left.mp hd hx hxs).elim
  · let W := H.direction ⊔ Submodule.span ℝ {b - a}
    let B := AffineSubspace.mk' a W
    haveI : Nonempty s := hs.to_subtype
    have hdim : Module.finrank ℝ H.direction + 1 ≤ s.card := by
      have hrange : Set.range ((↑) : s → E d) = (s : Set (E d)) := by ext; simp
      dsimp only [H]
      rw [direction_affineSpan]
      have hh := finrank_vectorSpan_range_add_one_le ℝ ((↑) : s → E d)
      rw [hrange, Fintype.card_coe] at hh
      exact hh
    have hdimW := Submodule.finrank_add_le_finrank_add_finrank
      H.direction (Submodule.span ℝ {b - a})
    have hdimspan : Module.finrank ℝ (Submodule.span ℝ {b - a}) ≤ 1 := by
      simpa using finrank_span_le_card ({b - a} : Set (E d))
    have hBproper : B ≠ ⊤ := by
      intro htop
      have hh := congrArg AffineSubspace.direction htop
      have hh : W = ⊤ := by
        simpa only [B, AffineSubspace.direction_mk', AffineSubspace.direction_top] using hh
      change Module.finrank ℝ W ≤ _ at hdimW
      rw [hh, finrank_top, finrank_euclideanSpace, Fintype.card_fin] at hdimW
      omega
    obtain ⟨hB, hdB⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step2_dense_compl B hBproper
    refine ⟨(B : Set (E d))ᶜ, hB, hdB, ?_⟩
    intro z hz _
    have hzW : z - a ∉ W := hz
    have hwu : Disjoint (Submodule.span ℝ {b - a}) H.direction :=
      (Submodule.disjoint_span_singleton_of_notMem hw).symm
    have hzw : Disjoint (Submodule.span ℝ {z - a})
        (Submodule.span ℝ {b - a} ⊔ H.direction) := by
      simpa only [W, sup_comm] using (Submodule.disjoint_span_singleton_of_notMem hzW).symm
    have hdis := hwu.disjoint_sup_left_of_disjoint_sup_right hzw
    have hAdir : (affineSpan ℝ ({a, b, z} : Set (E d))).direction =
        Submodule.span ℝ {z - a} ⊔ Submodule.span ℝ {b - a} := by
      have heq : ({a, b, z} : Set (E d)) = insert z {a, b} := by ext; simp; tauto
      rw [heq, ← affineSpan_insert_affineSpan,
        AffineSubspace.direction_affineSpan_insert (left_mem_affineSpan_pair ℝ a b),
        direction_affineSpan, vectorSpan_pair_rev]
      rfl
    intro x hx y hy
    have hxy : x - y ∈ (Submodule.span ℝ {z - a} ⊔ Submodule.span ℝ {b - a}) ⊓
        H.direction := by
      constructor
      · rw [← hAdir]
        exact AffineSubspace.vsub_mem_direction hx.1 hy.1
      · exact AffineSubspace.vsub_mem_direction hx.2 hy.2
    rw [hdis.eq_bot] at hxy
    simpa only [Submodule.mem_bot, sub_eq_zero] using hxy

/-- Step 11 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan` (V4 1.24):
"in general position". Adjoining both base vertices to a face of codimension at least three
still gives a proper affine span, whose complement prevents the triangle from meeting that
face. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step11_small_face_open (s : Finset (E d)) (hc : s.card + 1 < d)
    {a b : E d} (hab : Disjoint (segment ℝ a b) (convexHull ℝ (s : Set (E d)))) :
    ∃ U : Set (E d), IsOpen U ∧ Dense U ∧ ∀ z ∈ U,
      Disjoint (convexHull ℝ ({a, b, z} : Set (E d))) (convexHull ℝ (s : Set (E d))) := by
  classical
  let B := affineSpan ℝ (insert a (insert b (s : Set (E d))))
  have hcard : (insert a (insert b s)).card ≤ d := by
    have h1 := Finset.card_insert_le a (insert b s)
    have h2 := Finset.card_insert_le b s
    omega
  have hBproper : B ≠ ⊤ := by
    simpa only [Finset.coe_insert] using principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step1_proper_span (insert a (insert b s)) hcard
  obtain ⟨hB, hdB⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step2_dense_compl B hBproper
  refine ⟨(B : Set (E d))ᶜ, hB, hdB, ?_⟩
  intro z hz
  apply principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step8_triangle_avoids (convexHull ℝ (s : Set (E d))) B
    (subset_affineSpan ℝ _ (by simp)) (subset_affineSpan ℝ _ (by simp)) ?_ hz hab
  exact (convexHull_subset_affineSpan _).trans
    (affineSpan_mono ℝ ((Set.subset_insert b _).trans (Set.subset_insert a _)))

/-- Step 12 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan` (V4 1.24):
"in general position". Noncollinear triangle sides meet only at their shared vertices, so
their crossings with a set avoiding those vertices are disjoint. -/
private lemma principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step12_triangle_boundary (T : Set (E d)) {a b z : E d} (hab : a ≠ b)
    (hz : z ∉ affineSpan ℝ ({a, b} : Set (E d))) (haT : a ∉ T) (hbT : b ∉ T) (hzT : z ∉ T) :
    AffineIndependent ℝ ![a, b, z] ∧
    Disjoint (segment ℝ a b ∩ T) (segment ℝ b z ∩ T) ∧
    Disjoint ((segment ℝ a b ∩ T) ∪ (segment ℝ b z ∩ T)) (segment ℝ z a ∩ T) := by
  have hncol : ¬ Collinear ℝ ({a, b, z} : Set (E d)) := by
    intro hcol
    exact hz (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab)
  have ha : a ∉ affineSpan ℝ ({b, z} : Set (E d)) := by
    intro ha
    exact hncol (collinear_insert_of_mem_affineSpan_pair ha)
  refine ⟨affineIndependent_iff_not_collinear_set.mpr hncol, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hxA : x ∈ affineSpan ℝ ({a, b} : Set (E d)) :=
      convexHull_subset_affineSpan _ (by simpa only [convexHull_pair] using hx.1)
    have heq := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step4_segment_span (affineSpan ℝ ({a, b} : Set (E d)))
      (right_mem_affineSpan_pair ℝ a b) hz hy.1 hxA
    exact hbT (heq ▸ hx.2)
  · apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx
    · have hxA : x ∈ affineSpan ℝ ({a, b} : Set (E d)) :=
        convexHull_subset_affineSpan _ (by simpa only [convexHull_pair] using hx.1)
      have heq := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step4_segment_span (affineSpan ℝ ({a, b} : Set (E d)))
        (left_mem_affineSpan_pair ℝ a b) hz (by simpa only [segment_symm] using hy.1) hxA
      exact haT (heq ▸ hx.2)
    · have hxA : x ∈ affineSpan ℝ ({b, z} : Set (E d)) :=
        convexHull_subset_affineSpan _ (by simpa only [convexHull_pair] using hx.1)
      have heq := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step4_segment_span (affineSpan ℝ ({b, z} : Set (E d)))
        (right_mem_affineSpan_pair ℝ b z) ha hy.1 hxA
      exact hzT (heq ▸ hx.2)

/-- Step 21 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"in general position". For finitely many nonconstant regular segments, choose one
cone vertex making every resulting triangle transverse to all simplices. Only
finitely many proper affine conditions must be avoided. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d) (L : Finset (E d × E d))
    (hL : ∀ e ∈ L, e.1 ≠ e.2 ∧
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step12_RegularSegment K e.1 e.2) :
    ∃ z : E d, ∀ e ∈ L,
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step13_TrianglePosition K e.1 e.2 z := by
  classical
  haveI : Finite K.faces := hfin.to_subtype
  obtain ⟨U, hU, hdU, hUP⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step3_finite_conditions
    (fun (e : L) z => principal_component_step1_hull_geometry_step10_jordan_brouwer_step13_TrianglePosition
      K e.val.1 e.val.2 z) (by
        intro e
        obtain ⟨hne, hreg⟩ := hL e.val e.property
        obtain ⟨Ua, hUa, hdUa, hUaP⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step9_regular_open K hfin hpure e.val.1 hreg.1
        obtain ⟨Ub, hUb, hdUb, hUbP⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step9_regular_open K hfin hpure e.val.2 hreg.2.1
        obtain ⟨Us, hUs, hdUs, hUsP⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step3_finite_conditions
          (fun (s : {s : K.faces // s.val.card + 1 < d}) z =>
            Disjoint (convexHull ℝ ({e.val.1, e.val.2, z} : Set (E d)))
              (convexHull ℝ (s.val.val : Set (E d)))) (by
                intro s
                exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step11_small_face_open s.val.val s.property
                  (principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step7_regular_avoids_face K hpure hreg s.val.property (by omega)))
        obtain ⟨Ur, hUr, hdUr, hUrP⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step3_finite_conditions
          (fun (s : {s : K.faces // s.val.card = d - 1}) z =>
            (convexHull ℝ ({e.val.1, e.val.2, z} : Set (E d)) ∩
              convexHull ℝ (s.val.val : Set (E d))).Nonempty →
            ((affineSpan ℝ ({e.val.1, e.val.2, z} : Set (E d)) : Set (E d)) ∩
              (affineSpan ℝ (s.val.val : Set (E d)) : Set (E d))).Subsingleton) (by
                intro s
                have hc : s.val.val.card < d := by have hd : 2 ≤ d := Fact.out; omega
                exact principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step10_ridge_open s.val.val (K.nonempty_of_mem_faces s.val.property) hc
                  (principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step7_regular_avoids_face K hpure hreg s.val.property hc))
        let B := affineSpan ℝ ({e.val.1, e.val.2} : Set (E d))
        have hBproper : B ≠ ⊤ := by
          have hd : 2 ≤ d := Fact.out
          have hc : ({e.val.1, e.val.2} : Finset (E d)).card ≤ d :=
            Finset.card_le_two.trans hd
          simpa only [B, Finset.coe_insert, Finset.coe_singleton] using
            principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step1_proper_span {e.val.1, e.val.2} hc
        obtain ⟨hB, hdB⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step2_dense_compl B hBproper
        refine ⟨(B : Set (E d))ᶜ ∩ (Ua ∩ (Ub ∩ (Us ∩ Ur))),
          hB.inter (hUa.inter (hUb.inter (hUs.inter hUr))),
          hdB.inter_of_isOpen_right (hdUa.inter_of_isOpen_right
            (hdUb.inter_of_isOpen_right (hdUs.inter_of_isOpen_right hdUr hUr)
              (hUs.inter hUr)) (hUb.inter (hUs.inter hUr)))
            (hUa.inter (hUb.inter (hUs.inter hUr))), ?_⟩
        rintro z ⟨hzB, hza, hzb, hzs, hzr⟩
        obtain ⟨haz, hzfacets⟩ := hUaP z hza
        obtain ⟨hbz, -⟩ := hUbP z hzb
        have hza' : principal_component_step1_hull_geometry_step10_jordan_brouwer_step12_RegularSegment
            K z e.val.1 := by
          refine ⟨haz.2.1, haz.1, ?_, ?_⟩
          · simpa only [segment_symm] using haz.2.2.1
          · intro x hx
            obtain ⟨f, hf, hxf, haf, hzf⟩ := haz.2.2.2 x (by simpa only [segment_symm] using hx)
            exact ⟨f, hf, hxf, hzf, haf⟩
        obtain ⟨hai, hd1, hd2⟩ := principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan_step12_triangle_boundary K.space hne hzB hreg.1 hreg.2.1 haz.2.1
        refine ⟨hai, hreg, hbz, hza', hd1, hd2, ?_, ?_, ?_⟩
        · intro s hs hc
          exact hUsP z hzs ⟨⟨s, hs⟩, hc⟩
        · intro s hs hc hcut
          exact hUrP z hzr ⟨⟨s, hs⟩, hc⟩ hcut
        · intro f hf hsub
          exact hzfacets f hf (hsub (subset_affineSpan ℝ _ (by simp))))
  obtain ⟨z, hz⟩ := hdU.nonempty
  exact ⟨z, fun e he => hUP z hz ⟨e, he⟩⟩

/-- Step 22 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"choose polygonal paths ... (connected)". In an open connected Euclidean set,
points are joined by a finite chain of nonconstant segments in that set. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step22_polygonal
    {U : Set (E d)} (hopen : IsOpen U) (hconn : IsPreconnected U)
    {a b : E d} (ha : a ∈ U) (hb : b ∈ U) :
    ∃ L : Finset (E d × E d),
      (∀ e ∈ L, e.1 ≠ e.2 ∧ segment ℝ e.1 e.2 ⊆ U) ∧
      Relation.ReflTransGen (fun x y => (x, y) ∈ L) a b := by
  classical
  let R := fun x y : E d => x ≠ y ∧ segment ℝ x y ⊆ U
  let J := {x | Relation.ReflTransGen R a x}
  have haJ : a ∈ J := Relation.ReflTransGen.refl
  have hJU : J ⊆ U := by
    intro x hx
    induction hx with
    | refl => exact ha
    | tail _ hxy _ => exact hxy.2 (right_mem_segment ℝ _ _)
  have hJopen : IsOpen J := by
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x (hJU hx)
    refine ⟨r, hr, ?_⟩
    intro y hy
    by_cases hxy : x = y
    · exact hxy ▸ hx
    · exact hx.tail ⟨hxy, ((convex_ball x r).segment_subset (Metric.mem_ball_self hr) hy).trans hball⟩
  have hVopen : IsOpen (U \ J) := by
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hx.1
    refine ⟨r, hr, ?_⟩
    intro y hy
    refine ⟨hball hy, ?_⟩
    intro hyJ
    apply hx.2
    by_cases hyx : y = x
    · exact hyx ▸ hyJ
    · exact hyJ.tail ⟨hyx,
        ((convex_ball x r).segment_subset hy (Metric.mem_ball_self hr)).trans hball⟩
  have hUJ : U ⊆ J := by
    rcases hconn.subset_or_subset hJopen hVopen disjoint_sdiff_right
        (by intro x hx; by_cases hxJ : x ∈ J <;> simp_all) with h | h
    · exact h
    · exact (h ha).2 haJ |>.elim
  have hchain := hUJ hb
  clear hb
  induction hchain with
  | refl => exact ⟨∅, by simp, Relation.ReflTransGen.refl⟩
  | @tail x y hax hxy ih =>
    obtain ⟨L, hL, hpath⟩ := ih
    refine ⟨insert (x, y) L, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hxy
      · exact hL e he
    · have hmap : ∀ {u v}, Relation.ReflTransGen (fun u v => (u, v) ∈ L) u v →
          Relation.ReflTransGen (fun u v => (u, v) ∈ insert (x, y) L) u v := by
        intro u v h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ huv ih => exact ih.tail (Finset.mem_insert_of_mem huv)
      exact (hmap hpath).tail (Finset.mem_insert_self _ _)

/-- Step 23 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"separating `ℝᵈ`". Opposite normal samples cannot be in the same complementary
component: a polygonal return path would close their single crossing. Cone all
its segments to one generic vertex; triangle parity propagates a parity value
along the return path, while the single crossing changes it. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step23_opposite_distinct
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d) (hclosed : IsClosed K.space)
    (hridge : ∀ s ∈ K.faces, s.card = d - 1 → {f ∈ K.facets | s ⊆ f}.ncard = 2)
    {a b : E d}
    (hreg : principal_component_step1_hull_geometry_step10_jordan_brouwer_step12_RegularSegment K a b)
    (hone : (segment ℝ a b ∩ K.space).ncard = 1) :
    connectedComponentIn K.spaceᶜ a ≠ connectedComponentIn K.spaceᶜ b := by
  classical
  intro heq
  have hne : a ≠ b := by
    rintro rfl
    have hempty : segment ℝ a a ∩ K.space = ∅ := by
      simp [segment_same, Set.singleton_inter_eq_empty.mpr hreg.1]
    rw [hempty, Set.ncard_empty] at hone
    omega
  let C := connectedComponentIn K.spaceᶜ a
  have hCa : a ∈ C := mem_connectedComponentIn hreg.1
  have hCb : b ∈ C := by
    change b ∈ connectedComponentIn K.spaceᶜ a
    rw [heq]
    exact mem_connectedComponentIn hreg.2.1
  obtain ⟨L, hL, hpath⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step22_polygonal
      hclosed.isOpen_compl.connectedComponentIn isPreconnected_connectedComponentIn hCa hCb
  have hLempty : ∀ e ∈ L, segment ℝ e.1 e.2 ∩ K.space = ∅ := by
    intro e he
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact connectedComponentIn_subset _ _ ((hL e he).2 hx.1) hx.2
  have hLreg : ∀ e ∈ L,
      principal_component_step1_hull_geometry_step10_jordan_brouwer_step12_RegularSegment K e.1 e.2 := by
    intro e he
    refine ⟨connectedComponentIn_subset _ _ ((hL e he).2 (left_mem_segment ℝ _ _)),
      connectedComponentIn_subset _ _ ((hL e he).2 (right_mem_segment ℝ _ _)), ?_, ?_⟩
    · rw [hLempty e he]; exact Set.finite_empty
    · rw [hLempty e he]; simp
  obtain ⟨z, hz⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step21_generic_fan
      K hfin hpure (insert (a, b) L) (by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact ⟨hne, hreg⟩
        · exact ⟨(hL e he).1, hLreg e he⟩)
  let χ := fun x : E d => (segment ℝ x z ∩ K.space).ncard % 2
  have hstep : ∀ x y, (x, y) ∈ L → χ x = χ y := by
    intro x y hxy
    have h := principal_component_step1_hull_geometry_step10_jordan_brouwer_step20_triangle_parity
      K hfin hpure hridge (hz (x, y) (Finset.mem_insert_of_mem hxy))
    rw [hLempty (x, y) hxy, Set.ncard_empty, zero_add, segment_symm ℝ z x] at h
    have hmod := Nat.even_iff.mp h
    dsimp only at hmod
    dsimp [χ]
    omega
  have htrans : ∀ {u v}, Relation.ReflTransGen (fun x y => (x, y) ∈ L) u v → χ u = χ v := by
    intro u v h
    induction h with
    | refl => rfl
    | tail _ hxy ih => exact ih.trans (hstep _ _ hxy)
  have hχ : χ a = χ b := htrans hpath
  have h := principal_component_step1_hull_geometry_step10_jordan_brouwer_step20_triangle_parity
    K hfin hpure hridge (hz (a, b) (Finset.mem_insert_self _ _))
  rw [hone, segment_symm ℝ z a] at h
  have hmod := Nat.even_iff.mp h
  dsimp only at hmod
  dsimp [χ] at hχ
  omega

/-- Step 24 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"its frontier is contained in `∂t`". Every complementary component of a closed set
has frontier in that set, since the other complementary components are open. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step24_frontier_subset
    {Γ : Set (E d)} (hΓ : IsClosed Γ) {a : E d} :
    frontier (connectedComponentIn Γᶜ a) ⊆ Γ := by
  intro x hx
  by_contra hxΓ
  have hopen : IsOpen (connectedComponentIn Γᶜ x) := hΓ.isOpen_compl.connectedComponentIn
  obtain ⟨y, hyx, hya⟩ := mem_closure_iff.mp hx.1 _ hopen (mem_connectedComponentIn hxΓ)
  have heq : connectedComponentIn Γᶜ x = connectedComponentIn Γᶜ a :=
    (connectedComponentIn_eq hyx).trans (connectedComponentIn_eq hya).symm
  have hxa : x ∈ connectedComponentIn Γᶜ a := heq ▸ mem_connectedComponentIn hxΓ
  apply hx.2
  rw [hΓ.isOpen_compl.connectedComponentIn.interior_eq]
  exact hxa

/-- Step 25 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"has all its points adjacent to the same complementary component". Propagate the
unordered pair of components along facet chains. Every complementary component
accesses a facet; every closed facet belongs to both frontiers. Crossing parity
makes the two propagated components distinct. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step25_two_components
    (K : Geometry.SimplicialComplex ℝ (E d)) (hfin : K.faces.Finite)
    (hpure : ∀ f ∈ K.facets, f.card = d)
    (hcompact : IsCompact K.space) (hconn : IsConnected K.space)
    (hman : IsLocallyEuclidean (d - 1) K.space) :
    ∃ A D : Set (E d), IsOpen A ∧ IsConnected A ∧ IsOpen D ∧ IsConnected D ∧
      Disjoint A D ∧ K.spaceᶜ = A ∪ D ∧ frontier A = K.space ∧ frontier D = K.space := by
  classical
  have hridge := principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree
    K hfin hpure hman
  have hchain := principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains
    K hfin hpure hconn hman
  have hcover := principal_component_step1_hull_geometry_step10_jordan_brouwer_step9_facets_cover K hfin
  choose a b hsides hreg hone hfronta hfrontb using
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step15_facet_samples K hfin hpure
  obtain ⟨q, hq⟩ := hconn.nonempty
  rw [hcover] at hq
  obtain ⟨f₀, -⟩ := Set.mem_iUnion.mp hq
  let A := connectedComponentIn K.spaceᶜ (a f₀)
  let D := connectedComponentIn K.spaceᶜ (b f₀)
  have hpairs (f g : K.facets) :
      ({connectedComponentIn K.spaceᶜ (a f), connectedComponentIn K.spaceᶜ (b f)} : Set (Set (E d))) =
        {connectedComponentIn K.spaceᶜ (a g), connectedComponentIn K.spaceᶜ (b g)} := by
    have h := hchain f g
    induction h with
    | refl => rfl
    | @tail u v huv hstep ih =>
      exact ih.trans
        (principal_component_step1_hull_geometry_step10_jordan_brouwer_step16_ridge_transport
          K hfin hpure hridge u v hstep (hsides u) (hsides v))
  have hfront (T : Set (E d)) (hT : T ∈ ({A, D} : Set (Set (E d)))) : K.space ⊆ frontier T := by
    intro x hx
    rw [hcover] at hx
    obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp hx
    have hfT : T ∈ ({connectedComponentIn K.spaceᶜ (a f), connectedComponentIn K.spaceᶜ (b f)} :
        Set (Set (E d))) := by
      rw [hpairs f f₀]
      exact hT
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfT
    rcases hfT with rfl | rfl
    · exact hfronta f hxf
    · exact hfrontb f hxf
  have hne : A ≠ D :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step23_opposite_distinct
      K hfin hpure hcompact.isClosed hridge (hreg f₀) (hone f₀)
  have hdisj : Disjoint A D := Set.disjoint_left.mpr fun x hxA hxD =>
    hne ((connectedComponentIn_eq hxA).trans (connectedComponentIn_eq hxD).symm)
  have hcompcover : K.spaceᶜ = A ∪ D := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨f, hxf⟩ :=
        principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet
          K hfin hpure hconn.nonempty a b hsides hx
      have hsub (T : Set (E d))
          (hT : T ∈ ({connectedComponentIn K.spaceᶜ (a f), connectedComponentIn K.spaceᶜ (b f)} :
            Set (Set (E d)))) : T ⊆ A ∪ D := by
        rw [hpairs f f₀] at hT
        change T ∈ ({A, D} : Set (Set (E d))) at hT
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT
        rcases hT with rfl | rfl
        · exact Set.subset_union_left
        · exact Set.subset_union_right
      rcases hxf with hxa | hxb
      · exact hsub _ (by simp) hxa
      · exact hsub _ (by simp) hxb
    · exact union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)
  refine ⟨A, D, hcompact.isClosed.isOpen_compl.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr (hreg f₀).1,
    hcompact.isClosed.isOpen_compl.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr (hreg f₀).2.1,
    hdisj, hcompcover, ?_, ?_⟩
  · exact Set.Subset.antisymm
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step24_frontier_subset hcompact.isClosed)
      (hfront A (by simp))
  · exact Set.Subset.antisymm
      (principal_component_step1_hull_geometry_step10_jordan_brouwer_step24_frontier_subset hcompact.isClosed)
      (hfront D (by simp))

/-- Step 26 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"a bounded and an unbounded part". Two disjoint open connected sides of a bounded
set cannot both be unbounded: they would both meet a large connected sphere.
They cannot both be bounded either, since their union is the set's complement. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step26_bounded_side
    {Γ B U : Set (E d)} (hΓ : Bornology.IsBounded Γ)
    (hBopen : IsOpen B) (hBconn : IsConnected B)
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (hdisj : Disjoint B U) (hcover : Γᶜ = B ∪ U) :
    (Bornology.IsBounded B ∧ ¬ Bornology.IsBounded U) ∨
      (Bornology.IsBounded U ∧ ¬ Bornology.IsBounded B) := by
  haveI : NeZero d := ⟨by have hd : 2 ≤ d := Fact.out; omega⟩
  have hrank : 1 < Module.rank ℝ (E d) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast (show 1 < d by have hd : 2 ≤ d := Fact.out; omega)
  have hnotboth : ¬ (Bornology.IsBounded B ∧ Bornology.IsBounded U) := by
    rintro ⟨hB, hU⟩
    apply NormedSpace.unbounded_univ ℝ (E d)
    have hb := hΓ.union (hB.union hU)
    rwa [← hcover, union_compl_self] at hb
  have hone : Bornology.IsBounded B ∨ Bornology.IsBounded U := by
    by_contra h
    obtain ⟨hB, hU⟩ := not_or.mp h
    obtain ⟨a, ha⟩ := hBconn.nonempty
    obtain ⟨b, hb⟩ := hUconn.nonempty
    obtain ⟨r, hr, hΓr⟩ := hΓ.subset_ball_lt (max ‖a‖ ‖b‖) (0 : E d)
    have hmeet (C : Set (E d)) (hC : IsPreconnected C)
        (hCbdd : ¬ Bornology.IsBounded C) {c : E d} (hc : c ∈ C) (hcr : ‖c‖ ≤ r) :
        (Metric.sphere (0 : E d) r ∩ C).Nonempty := by
      have hex : ∃ z ∈ C, r < ‖z‖ := by
        by_contra hex
        push_neg at hex
        exact hCbdd (isBounded_iff_forall_norm_le.mpr ⟨r, hex⟩)
      obtain ⟨z, hz, hrz⟩ := hex
      obtain ⟨w, hw, hwr⟩ := hC.intermediate_value hc hz continuous_norm.continuousOn
        (show r ∈ Icc ‖c‖ ‖z‖ from ⟨hcr, hrz.le⟩)
      exact ⟨w, by simpa only [Metric.mem_sphere, dist_zero_right] using hwr, hw⟩
    have hScover : Metric.sphere (0 : E d) r ⊆ B ∪ U := by
      rw [← hcover]
      intro x hx hxΓ
      have hin := hΓr hxΓ
      rw [Metric.mem_ball, dist_zero_right] at hin
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact (ne_of_lt hin) hx
    obtain ⟨x, -, hxB, hxU⟩ := (isPreconnected_sphere hrank (0 : E d) r) B U
      hBopen hUopen hScover
      (hmeet B hBconn.isPreconnected hB ha ((le_max_left _ _).trans hr.le))
      (hmeet U hUconn.isPreconnected hU hb ((le_max_right _ _).trans hr.le))
    exact Set.disjoint_left.mp hdisj hxB hxU
  rcases hone with hB | hU
  · exact Or.inl ⟨hB, fun hU => hnotboth ⟨hB, hU⟩⟩
  · exact Or.inr ⟨hU, fun hB => hnotboth ⟨hB, hU⟩⟩

/-- Step 10 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"each a closed hypersurface separating `ℝᵈ` into a bounded and an unbounded part
(Jordan–Brouwer)". This is separation by one connected boundary component. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer
    (P : PolyManifoldDomain d) (F : E d ≃ᵃ[ℝ] E d)
    (p : E d) (hp : p ∈ frontier (F '' P.carrier)) :
    let Γ := connectedComponentIn (frontier (F '' P.carrier)) p
    ∃ B U : Set (E d),
      IsOpen B ∧ IsConnected B ∧ Bornology.IsBounded B ∧
      IsOpen U ∧ IsConnected U ∧ ¬ Bornology.IsBounded U ∧
      Disjoint B U ∧ Γᶜ = B ∪ U ∧ frontier B = Γ ∧ frontier U = Γ := by
  obtain ⟨hcompact, hconn, hman⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step3_compact_component P F p hp
  obtain ⟨K, hfin, hK, hpure⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step8_triangulate P F p hp
  rw [← hK] at hcompact hconn hman ⊢
  obtain ⟨A, D, hAo, hAc, hDo, hDc, hdisj, hcover, hAf, hDf⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer_step25_two_components
      K hfin hpure hcompact hconn hman
  rcases principal_component_step1_hull_geometry_step10_jordan_brouwer_step26_bounded_side
    hcompact.isBounded hAo hAc hDo hDc hdisj hcover with ⟨hAb, hDb⟩ | ⟨hDb, hAb⟩
  · exact ⟨A, D, hAo, hAc, hAb, hDo, hDc, hDb, hdisj, hcover, hAf, hDf⟩
  · exact ⟨D, A, hDo, hDc, hDb, hAo, hAc, hAb,
      hdisj.symm, hcover.trans (union_comm _ _), hDf, hAf⟩

/-- Step 11 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"a connected union of facets of `t`". The boundary complex is pure: its facet
carriers cover the frontier, including all lower-dimensional cells. -/
private theorem principal_component_step1_hull_geometry_step11_facets_cover
    (P : PolyManifoldDomain d) (C : CellComplex P) :
    frontier P.carrier ⊆ ⋃ e : {e // e ∈ C.facets}, e.val.carrier := by
  classical
  have hd : 2 ≤ d := Fact.out
  let Q : Set (E d) := ⋃ e ∈ C.facets, e.carrier
  have hQclosed : IsClosed Q := isClosed_biUnion_finset (fun e _ => e.flat.compact.isClosed)
  intro p hp
  by_contra hpF
  have hpQ : p ∉ Q := by
    intro hpQ
    obtain ⟨e, he, hpe⟩ := Set.mem_iUnion₂.mp hpQ
    exact hpF (Set.mem_iUnion.mpr ⟨⟨e, he⟩, hpe⟩)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hQclosed.isOpen_compl p hpQ
  have hpclosure : p ∈ closure (interior P.carrier) := by
    rw [P.regularClosed]
    exact (frontier_subset_iff_isClosed.mpr P.compact.isClosed) hp
  obtain ⟨a, haB, ha⟩ := mem_closure_iff.mp hpclosure (Metric.ball p r) Metric.isOpen_ball
    (Metric.mem_ball_self hr)
  have hpout : p ∈ closure P.carrierᶜ := by
    rw [frontier_eq_closure_inter_closure] at hp
    exact hp.2
  obtain ⟨b, hbB, hb⟩ := mem_closure_iff.mp hpout (Metric.ball p r)
    Metric.isOpen_ball (Metric.mem_ball_self hr)
  let L := C.cells.filter (fun e => e.dim + 1 < d)
  have hcellfront (e : Cell d) (he : e ∈ C.cells) : e.carrier ⊆ frontier P.carrier := by
    rw [← e.flat.regularClosed]
    apply closure_minimal _ isClosed_frontier
    intro x hx
    rw [← C.cover]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hx⟩
  have haout (e : Cell d) (he : e ∈ C.cells) : a ∉ e.carrier :=
    fun hae => (hcellfront e he hae).2 ha
  have hbout (e : Cell d) (he : e ∈ C.cells) : b ∉ e.carrier :=
    fun hbe => hb ((frontier_subset_iff_isClosed.mpr P.compact.isClosed) (hcellfront e he hbe))
  obtain ⟨J, hJconn, haJ, hbJ, hJB, hJL⟩ :=
    principal_component_step1_hull_geometry_step7_avoid_cells L
      (fun e he => (Finset.mem_filter.mp he).2) Metric.isOpen_ball (convex_ball p r)
      haB hbB (fun e he => haout e (Finset.mem_filter.mp he).1)
      (fun e he => hbout e (Finset.mem_filter.mp he).1)
  have hJfront : ∀ x ∈ J, x ∉ frontier P.carrier := by
    intro x hx hxf
    rw [← C.cover] at hxf
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hxf
    have hxec : x ∈ e.carrier := e.flat.regularClosed ▸ subset_closure hxe
    by_cases heF : e ∈ C.facets
    · exact hball (hJB hx) (Set.mem_iUnion₂.mpr ⟨e, heF, hxec⟩)
    · have heL : e ∈ L := by
        apply Finset.mem_filter.mpr
        refine ⟨he, ?_⟩
        have hdim := C.dim_lt e he
        have hne : e.dim ≠ d - 1 := by
          intro hh
          exact heF (Finset.mem_filter.mpr ⟨he, hh⟩)
        omega
      exact Set.disjoint_left.mp (hJL e heL) hx hxec
  have hsplit : J ⊆ interior P.carrier ∪ P.carrierᶜ := by
    intro x hx
    by_cases hxt : x ∈ P.carrier
    · left
      by_contra hxint
      exact hJfront x hx ⟨P.compact.isClosed.closure_eq.symm ▸ hxt, hxint⟩
    · exact Or.inr hxt
  obtain ⟨x, _, hxint, hxout⟩ := hJconn (interior P.carrier) P.carrierᶜ
    isOpen_interior P.compact.isClosed.isOpen_compl hsplit
    ⟨a, haJ, ha⟩
    ⟨b, hbJ, hb⟩
  exact hxout (interior_subset hxint)

/-- Step 12 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"Components other than `Σ₀` bound bounded complementary components ... which are
filled in `K(t)`". Local one-sidedness puts a cavity's frontier inside the hull. -/
private theorem principal_component_step1_hull_geometry_step12_cavity_frontier
    (P : PolyManifoldDomain d) (F : E d ≃ᵃ[ℝ] E d)
    {B : Set (E d)} (hB : IsOpen B) (hBconn : IsConnected B)
    (hBbdd : Bornology.IsBounded B) (hBsub : B ⊆ (F '' P.carrier)ᶜ)
    (hBfront : frontier B ⊆ F '' P.carrier)
    {p : E d} (hp : p ∈ frontier B)
    (hlocal : ∃ V : Set (E d), IsOpen V ∧ p ∈ V ∧
      IsPreconnected (V ∩ (F '' P.carrier)ᶜ)) :
    p ∈ interior (principal_component_step1_filledHull (F '' P.carrier)) := by
  let t := F '' P.carrier
  obtain ⟨V, hV, hpV, hVconn⟩ := hlocal
  obtain ⟨q, hqV, hqB⟩ := mem_closure_iff.mp hp.1 V hV hpV
  have hcomp : connectedComponentIn tᶜ q = B := by
    apply Set.Subset.antisymm
    · apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hB
        ⟨q, mem_connectedComponentIn (hBsub hqB), hqB⟩
      intro x hx
      by_contra hxB
      exact connectedComponentIn_subset tᶜ q hx.2
        (hBfront ⟨hx.1, by simpa only [hB.interior_eq] using hxB⟩)
    · exact hBconn.isPreconnected.subset_connectedComponentIn hqB hBsub
  have hVsub : V ∩ tᶜ ⊆ B := by
    rw [← hcomp]
    exact hVconn.subset_connectedComponentIn ⟨hqV, hBsub hqB⟩ inter_subset_right
  apply mem_interior.mpr
  refine ⟨V, ?_, hV, hpV⟩
  intro x hxV
  by_cases hxt : x ∈ t
  · exact principal_component_step1_hull_geometry_step1_contains t hxt
  · have hxB := hVsub ⟨hxV, hxt⟩
    change Bornology.IsBounded (connectedComponentIn tᶜ x)
    rw [← connectedComponentIn_eq (hcomp.symm ▸ hxB), hcomp]
    exact hBbdd

/-- Step 13 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"separating ... into a bounded and an unbounded part". The closure of either
Jordan–Brouwer side is the complement of the other side. -/
private theorem principal_component_step1_hull_geometry_step13_side_closure
    {Γ B U : Set (E d)} (hdisj : Disjoint B U) (hcover : Γᶜ = B ∪ U)
    (hfront : frontier B = Γ) : closure B = Uᶜ := by
  rw [closure_eq_self_union_frontier, hfront]
  apply Set.Subset.antisymm
  · intro x hx hxU
    rcases hx with hxB | hxΓ
    · exact Set.disjoint_left.mp hdisj hxB hxU
    · have hxout : x ∈ Γᶜ := by rw [hcover]; exact Or.inr hxU
      exact hxout hxΓ
  · intro x hxU
    by_cases hxΓ : x ∈ Γ
    · exact Or.inr hxΓ
    · have hxBU : x ∈ B ∪ U := by rw [← hcover]; exact hxΓ
      exact Or.inl (hxBU.resolve_right hxU)

/-- Step 14 of the V4 proof of `principal_component_step1_hull_geometry` (V4 1.24):
"`int t` on its bounded side and `U(t)` on its unbounded side". Once this side
is identified, the definition by bounded complementary components fills it. -/
private theorem principal_component_step1_hull_geometry_step14_fill_side
    {t Γ B U : Set (E d)} (hBopen : IsOpen B) (hBbdd : Bornology.IsBounded B)
    (hUopen : IsOpen U) (hUconn : IsConnected U) (hUbdd : ¬ Bornology.IsBounded U)
    (hdisj : Disjoint B U) (hcover : Γᶜ = B ∪ U)
    (hclB : closure B = Uᶜ) (hΓt : Γ ⊆ t) (htB : t ⊆ closure B) :
    principal_component_step1_filledHull t = Uᶜ := by
  have hUt : U ⊆ tᶜ := by
    intro x hxU hxt
    have := htB hxt
    rw [hclB] at this
    exact this hxU
  apply Set.Subset.antisymm
  · intro x hxK hxU
    change Bornology.IsBounded (connectedComponentIn tᶜ x) at hxK
    exact hUbdd (hxK.subset
      (hUconn.isPreconnected.subset_connectedComponentIn hxU hUt))
  · intro x hxU
    by_cases hxt : x ∈ t
    · exact principal_component_step1_hull_geometry_step1_contains t hxt
    · have hxB : x ∈ B := by
        have hxΓ : x ∈ Γᶜ := fun hx => hxt (hΓt hx)
        rw [hcover] at hxΓ
        exact hxΓ.resolve_right hxU
      have hc : connectedComponentIn tᶜ x ⊆ B := by
        apply isPreconnected_connectedComponentIn.subset_left_of_subset_union
          hBopen hUopen hdisj _ ⟨x, mem_connectedComponentIn hxt, hxB⟩
        intro y hy
        rw [← hcover]
        exact fun hyΓ => connectedComponentIn_subset tᶜ x hy (hΓt hyΓ)
      exact hBbdd.subset hc

/-- Step 1 of the V4 proof of `principal_component` (V4 1.24): "`K(t)` has
connected interior, its boundary is a connected union of facets of `t`, and
`K(t) ⊆ conv t`". The affine frame permits normalized prototype coordinates.
This is the single-domain Jordan--Brouwer/filling obligation. -/
private theorem principal_component_step1_hull_geometry
    (P : PolyManifoldDomain d) (C : CellComplex P) (F : E d ≃ᵃ[ℝ] E d) :
    let t := F '' P.carrier
    let K := principal_component_step1_filledHull t
    t ⊆ K ∧ IsCompact K ∧ IsRegularClosed K ∧
      IsConnected (interior K) ∧ IsConnected (frontier K) ∧
      K ⊆ convexHull ℝ t ∧
      frontier K ⊆ ⋃ e : {e // e ∈ C.facets}, F '' e.val.carrier := by
  let t := F '' P.carrier
  let K := principal_component_step1_filledHull t
  change t ⊆ K ∧ IsCompact K ∧ IsRegularClosed K ∧
    IsConnected (interior K) ∧ IsConnected (frontier K) ∧
    K ⊆ convexHull ℝ t ∧
    frontier K ⊆ ⋃ e : {e // e ∈ C.facets}, F '' e.val.carrier
  let e := F.toHomeomorphOfFiniteDimensional
  have htcompact : IsCompact t := P.compact.image e.continuous
  have htreg : IsRegularClosed t := by
    change closure (interior (e '' P.carrier)) = e '' P.carrier
    rw [← e.image_interior, ← e.image_closure, P.regularClosed]
  have htconn : IsConnected (interior t) := by
    change IsConnected (interior (e '' P.carrier))
    rw [← e.image_interior]
    exact P.interior_connected.image _ e.continuous.continuousOn
  have hcontains : t ⊆ K := principal_component_step1_hull_geometry_step1_contains t
  obtain ⟨hKclosed, hKfront⟩ :=
    principal_component_step1_hull_geometry_step3_closed_frontier htcompact.isClosed
  have hconvcompact := principal_component_step1_hull_geometry_step6_convex_compact P F
  have hconv : K ⊆ convexHull ℝ t :=
    principal_component_step1_hull_geometry_step5_convex_bound
      (htconn.nonempty.mono interior_subset) hconvcompact.isClosed
  have hKcompact : IsCompact K := hconvcompact.of_isClosed_subset hKclosed hconv
  have hKreg : IsRegularClosed K :=
    principal_component_step1_hull_geometry_step4_regular htcompact.isClosed htreg
  haveI : NeZero d := ⟨by have hd : 2 ≤ d := Fact.out; omega⟩
  -- Choose a facet point of the hull frontier in prototype coordinates.
  let H := e ⁻¹' K
  have hHclosed : IsClosed H := hKclosed.preimage e.continuous
  have hPH : P.carrier ⊆ H := fun x hx => hcontains ⟨x, hx, rfl⟩
  have hHproper : H ≠ univ := by
    intro hH
    apply hKcompact.ne_univ
    apply Set.eq_univ_of_forall
    intro x
    have hx : e.symm x ∈ H := hH.symm ▸ Set.mem_univ _
    simpa only [H, Set.mem_preimage, e.apply_symm_apply] using hx
  have hHfront : frontier H ⊆ frontier P.carrier := by
    intro x hx
    have hxK : e x ∈ frontier K := by
      rw [show frontier H = e ⁻¹' frontier K from (e.preimage_frontier K).symm] at hx
      exact hx
    have hxP : e x ∈ frontier (e '' P.carrier) := hKfront hxK
    rw [← e.image_frontier] at hxP
    obtain ⟨y, hy, hxy⟩ := hxP
    exact e.injective hxy ▸ hy
  obtain ⟨q, f, hq, hf, hqf⟩ :=
    principal_component_step1_hull_geometry_step8_frontier_facet P C hHclosed hPH hHproper hHfront
  let p := e q
  have hp : p ∈ frontier K := by
    rw [show frontier H = e ⁻¹' frontier K from (e.preimage_frontier K).symm] at hq
    exact hq
  have hlocal := principal_component_step1_hull_geometry_step9_facet_side P C F f hf q hqf
  have hpt : p ∈ frontier t := hKfront hp
  let Γ := connectedComponentIn (frontier t) p
  have hpΓ : p ∈ Γ := mem_connectedComponentIn hpt
  have hΓfront : Γ ⊆ frontier t := connectedComponentIn_subset _ _
  have hΓt : Γ ⊆ t := hΓfront.trans
    (frontier_subset_iff_isClosed.mpr htcompact.isClosed)
  obtain ⟨B, U, hBopen, hBconn, hBbdd, hUopen, hUconn, hUbdd,
      hdisj, hcover, hBfront, hUfront⟩ :=
    principal_component_step1_hull_geometry_step10_jordan_brouwer P F p hpt
  have hclB : closure B = Uᶜ :=
    principal_component_step1_hull_geometry_step13_side_closure hdisj hcover hBfront
  have hclU : closure U = Bᶜ :=
    principal_component_step1_hull_geometry_step13_side_closure hdisj.symm
      (hcover.trans (union_comm _ _)) hUfront
  have hside : interior t ⊆ B ∨ interior t ⊆ U := by
    apply htconn.isPreconnected.subset_or_subset hBopen hUopen hdisj
    intro x hx
    rw [← hcover]
    exact fun hxΓ => (hΓfront hxΓ).2 hx
  -- The selected component cannot bound a cavity: its local exterior would then
  -- be filled, making the selected frontier point an interior point of K.
  have htB : t ⊆ closure B := by
    rcases hside with hside | hside
    · rw [← htreg]
      exact closure_mono hside
    · have htU : t ⊆ closure U := by rw [← htreg]; exact closure_mono hside
      have hBout : B ⊆ tᶜ := by
        intro x hxB hxt
        have := htU hxt
        rw [hclU] at this
        exact this hxB
      have hpint := principal_component_step1_hull_geometry_step12_cavity_frontier
        P F hBopen hBconn hBbdd hBout (by rw [hBfront]; exact hΓt)
        (by rw [hBfront]; exact hpΓ) hlocal
      exact (hp.2 hpint).elim
  have hKU : K = Uᶜ := principal_component_step1_hull_geometry_step14_fill_side
    hBopen hBbdd hUopen hUconn hUbdd hdisj hcover hclB hΓt htB
  have hKint : interior K = B := by rw [hKU, interior_compl, hclU, compl_compl]
  have hKboundary : frontier K = Γ := by rw [hKU, frontier_compl]; exact hUfront
  refine ⟨hcontains, hKcompact, hKreg, hKint.symm ▸ hBconn,
    hKboundary.symm ▸ isConnected_connectedComponentIn_iff.mpr hpt, hconv, ?_⟩
  intro x hx
  have hxfront : x ∈ e '' frontier P.carrier := by
    rw [e.image_frontier]
    exact hKfront hx
  obtain ⟨y, hy, rfl⟩ := hxfront
  obtain ⟨f, hyf⟩ := Set.mem_iUnion.mp
    (principal_component_step1_hull_geometry_step11_facets_cover P C hy)
  exact Set.mem_iUnion.mpr ⟨f, y, hyf, rfl⟩

/-- Step 2 of the V4 proof of `principal_component` (V4 1.24): "filled hulls
of distinct native tiles are nested or have disjoint interiors". This is a
two-domain statement, before any subdivision, scale choice, or routing. -/
private theorem principal_component_step2_hulls_nested
    (P Q : PolyManifoldDomain d) (CP : CellComplex P) (CQ : CellComplex Q)
    (F G : E d ≃ᵃ[ℝ] E d)
    (hdisj : Disjoint (interior (F '' P.carrier)) (interior (G '' Q.carrier))) :
    let K := principal_component_step1_filledHull (F '' P.carrier)
    let L := principal_component_step1_filledHull (G '' Q.carrier)
    K ⊆ L ∨ L ⊆ K ∨ Disjoint (interior K) (interior L) := by
  have hself (t : Set (E d)) : t ⊆ principal_component_step1_filledHull t := by
    intro x hx
    change Bornology.IsBounded (connectedComponentIn tᶜ x)
    rw [connectedComponentIn_eq_empty (by simpa using hx)]
    exact Bornology.isBounded_empty
  have hmono {t u : Set (E d)} (htu : t ⊆ u) :
      principal_component_step1_filledHull t ⊆ principal_component_step1_filledHull u := by
    intro x hx
    change Bornology.IsBounded (connectedComponentIn tᶜ x) at hx
    change Bornology.IsBounded (connectedComponentIn uᶜ x)
    exact hx.subset (connectedComponentIn_mono x (Set.compl_subset_compl.mpr htu))
  have hidem (t : Set (E d)) :
      principal_component_step1_filledHull (principal_component_step1_filledHull t) =
        principal_component_step1_filledHull t := by
    refine Set.Subset.antisymm ?_ (hself _)
    intro x hx
    change Bornology.IsBounded
      (connectedComponentIn (principal_component_step1_filledHull t)ᶜ x) at hx
    change Bornology.IsBounded (connectedComponentIn tᶜ x)
    by_contra hn
    have hxt : x ∈ tᶜ := fun hxt => hn (hself t hxt)
    have hsub : connectedComponentIn tᶜ x ⊆ (principal_component_step1_filledHull t)ᶜ := by
      intro y hy hyfill
      change Bornology.IsBounded (connectedComponentIn tᶜ y) at hyfill
      exact hn ((connectedComponentIn_eq hy).symm ▸ hyfill)
    have hsub' := isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hxt) hsub
    exact hn (hx.subset hsub')
  have hreg (R : PolyManifoldDomain d) (J : E d ≃ᵃ[ℝ] E d) :
      IsRegularClosed (J '' R.carrier) := by
    let e := J.toHomeomorphOfFiniteDimensional
    change closure (interior (e '' R.carrier)) = e '' R.carrier
    rw [← e.image_interior, ← e.image_closure, R.regularClosed]
  have hconn (R : PolyManifoldDomain d) (J : E d ≃ᵃ[ℝ] E d) :
      IsConnected (interior (J '' R.carrier)) := by
    let e := J.toHomeomorphOfFiniteDimensional
    change IsConnected (interior (e '' R.carrier))
    rw [← e.image_interior]
    exact R.interior_connected.image _ e.continuous.continuousOn
  have hcases (t u : Set (E d)) (hureg : IsRegularClosed u)
      (huconn : IsConnected (interior u))
      (hclosed : IsClosed (principal_component_step1_filledHull t))
      (huout : interior u ⊆ tᶜ) :
      u ⊆ principal_component_step1_filledHull t ∨
        Disjoint u (interior (principal_component_step1_filledHull t)) := by
    obtain ⟨p, hp⟩ := huconn.nonempty
    have hcomp := huconn.isPreconnected.subset_connectedComponentIn hp huout
    by_cases hb : Bornology.IsBounded (connectedComponentIn tᶜ p)
    · left
      have hi : interior u ⊆ principal_component_step1_filledHull t := by
        intro x hx
        change Bornology.IsBounded (connectedComponentIn tᶜ x)
        exact connectedComponentIn_eq (hcomp hx) ▸ hb
      rw [← hureg]
      exact closure_minimal hi hclosed
    · right
      have hi : interior u ⊆ (principal_component_step1_filledHull t)ᶜ := by
        intro x hx hxf
        exact hb ((connectedComponentIn_eq (hcomp hx)).symm ▸ hxf)
      have hcl := closure_mono hi
      rw [hureg, closure_compl] at hcl
      exact Set.disjoint_left.mpr (fun x hx hxi => hcl hx hxi)
  have hboundary (R : PolyManifoldDomain d) (CR : CellComplex R)
      (J : E d ≃ᵃ[ℝ] E d) :
      frontier (principal_component_step1_filledHull (J '' R.carrier)) ⊆ J '' R.carrier := by
    obtain ⟨-, -, -, -, -, -, hfacets⟩ := principal_component_step1_hull_geometry R CR J
    intro x hx
    obtain ⟨e, y, hye, rfl⟩ := Set.mem_iUnion.mp (hfacets hx)
    refine ⟨y, ?_, rfl⟩
    have hcell : e.val.carrier ⊆ frontier R.carrier := by
      rw [← e.val.flat.regularClosed]
      apply closure_minimal _ isClosed_frontier
      intro z hz
      rw [← CR.cover]
      exact Set.mem_iUnion₂.mpr ⟨e.val, (Finset.mem_filter.mp e.property).1, hz⟩
    exact (frontier_subset_iff_isClosed.mpr R.compact.isClosed) (hcell hye)
  let t := F '' P.carrier
  let u := G '' Q.carrier
  let K := principal_component_step1_filledHull t
  let L := principal_component_step1_filledHull u
  change K ⊆ L ∨ L ⊆ K ∨ Disjoint (interior K) (interior L)
  have htreg : IsRegularClosed t := hreg P F
  have hureg : IsRegularClosed u := hreg Q G
  obtain ⟨htK, hKcompact, -, hKconn, -⟩ := principal_component_step1_hull_geometry P CP F
  obtain ⟨-, hLcompact, -⟩ := principal_component_step1_hull_geometry Q CQ G
  have htu : Disjoint (interior t) u := by
    rw [← hureg]
    exact hdisj.closure_right isOpen_interior
  have hut : Disjoint t (interior u) := by
    rw [← htreg]
    exact hdisj.closure_left isOpen_interior
  rcases hcases t u hureg (hconn Q G) hKcompact.isClosed
    (fun x hx hxt => Set.disjoint_left.mp hut hxt hx) with huK | huK
  · exact Or.inr (Or.inl (by simpa only [hidem t] using hmono huK))
  rcases hcases u t htreg (hconn P F) hLcompact.isClosed
    (fun x hx hxu => Set.disjoint_left.mp htu hx hxu) with htL | htL
  · exact Or.inl (by simpa only [hidem u] using hmono htL)
  right; right
  have hbdL : frontier L ⊆ u := hboundary Q CQ G
  have havoid : ∀ x ∈ interior K, x ∉ frontier L := by
    intro x hx hxbd
    exact Set.disjoint_left.mp huK (hbdL hxbd) hx
  have hsplit : interior K ⊆ interior L ∪ Lᶜ := by
    intro x hx
    by_cases hxL : x ∈ L
    · left
      by_contra hxint
      exact havoid x hx ⟨hLcompact.isClosed.closure_eq.symm ▸ hxL, hxint⟩
    · exact Or.inr hxL
  obtain ⟨a, ha⟩ := (hconn P F).nonempty
  have haK : a ∈ interior K := interior_mono htK ha
  have haout : a ∈ Lᶜ := by
    rcases hsplit haK with hai | hao
    · exact (Set.disjoint_left.mp htL (interior_subset ha) hai).elim
    · exact hao
  apply Set.disjoint_left.mpr
  intro z hzK hzL
  obtain ⟨b, -, hbL, hbout⟩ := hKconn.isPreconnected (interior L) Lᶜ
    isOpen_interior hLcompact.isClosed.isOpen_compl hsplit ⟨z, hzK, hzL⟩ ⟨a, haK, haout⟩
  exact hbout (interior_subset hbL)

/-- Step 3 of the V4 proof of `principal_component` (V4 1.24): "filled hulls
of all native tiles". Here both the native support and its filled hull have
been pulled back to the fixed prototype coordinates. -/
private def principal_component_step3_nativeHull (A : S.ι) (k : ℕ)
    (w : S.RoleWord A k) : Set (E d) :=
  principal_component_step1_filledHull
    (prototypeDescendantFrame A k w '' (S.proto (S.nativeTile A k w).ty).carrier)

/-- Step 3 of the V4 proof of `principal_component` (V4 1.24): "take the
maximal ones under inclusion; by Step 2 they have pairwise disjoint interiors,
cover all native tiles". Regular closedness makes their intersections lie on
both boundaries. No scale or prescribed facets enter this finite selection. -/
private theorem principal_component_step3_maximal_hulls (A : S.ι) (k : ℕ) :
    ∃ M : Finset (Set (E d)),
      (∀ K ∈ M, ∃ w : S.RoleWord A k, K = principal_component_step3_nativeHull A k w) ∧
      (S.proto A).carrier ⊆ ⋃ K ∈ M, K ∧
      ∀ K ∈ M, ∀ L ∈ M, K ≠ L → K ∩ L ⊆ frontier K ∩ frontier L := by
  classical
  have hgeometry (w : S.RoleWord A k) :=
    principal_component_step1_hull_geometry (S.proto (S.nativeTile A k w).ty)
      (S.cx (S.nativeTile A k w).ty) (prototypeDescendantFrame A k w)
  have hsupport (w : S.RoleWord A k) :
      prototypeDescendantFrame A k w '' (S.proto (S.nativeTile A k w).ty).carrier =
        (S.σ ^ k).symm '' (S.nativeTile A k w).carrier 0 := by
    simp [prototypeDescendantFrame, FramedNode.carrier, placedSet, SubstSystem.supertile,
      Set.image_image]
  have hcover : (S.proto A).carrier ⊆ ⋃ w : S.RoleWord A k,
      principal_component_step3_nativeHull A k w := by
    intro x hx
    have hσx : (S.σ ^ k) x ∈ S.supertile k A := ⟨x, hx, rfl⟩
    rw [← S.native_cover A k] at hσx
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hσx
    refine Set.mem_iUnion.mpr ⟨w, (hgeometry w).1 ?_⟩
    rw [hsupport w]
    exact ⟨(S.σ ^ k) x, hw, (S.σ ^ k).symm_apply_apply x⟩
  have hnested (v w : S.RoleWord A k) :
      principal_component_step3_nativeHull A k v ⊆ principal_component_step3_nativeHull A k w ∨
      principal_component_step3_nativeHull A k w ⊆ principal_component_step3_nativeHull A k v ∨
      Disjoint (interior (principal_component_step3_nativeHull A k v))
        (interior (principal_component_step3_nativeHull A k w)) := by
    by_cases hvw : v = w
    · exact Or.inl (hvw ▸ Set.Subset.rfl)
    apply principal_component_step2_hulls_nested
      (S.proto (S.nativeTile A k v).ty) (S.proto (S.nativeTile A k w).ty)
      (S.cx (S.nativeTile A k v).ty) (S.cx (S.nativeTile A k w).ty)
      (prototypeDescendantFrame A k v) (prototypeDescendantFrame A k w)
    rw [hsupport v, hsupport w]
    let e := (S.σ ^ k).symm.toContinuousLinearEquiv.toHomeomorph
    change Disjoint (interior (e '' (S.nativeTile A k v).carrier 0))
      (interior (e '' (S.nativeTile A k w).carrier 0))
    rw [← e.image_interior, ← e.image_interior]
    exact (Set.disjoint_image_iff e.injective).mpr (S.native_disjoint A k hvw)
  let all := Finset.univ.image (principal_component_step3_nativeHull (S := S) A k)
  let M := all.filter (fun K => Maximal (· ∈ all) K)
  have hnative : ∀ K ∈ M, ∃ w : S.RoleWord A k,
      K = principal_component_step3_nativeHull A k w := by
    intro K hK
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hK).1
    exact ⟨w, hw.symm⟩
  refine ⟨M, hnative, ?_, ?_⟩
  · intro x hx
    obtain ⟨w, hxw⟩ := Set.mem_iUnion.mp (hcover hx)
    have hw : principal_component_step3_nativeHull A k w ∈ all :=
      Finset.mem_image.mpr ⟨w, Finset.mem_univ w, rfl⟩
    obtain ⟨K, hwK, hK⟩ := all.exists_le_maximal hw
    exact Set.mem_iUnion₂.mpr ⟨K, Finset.mem_filter.mpr ⟨hK.prop, hK⟩, hwK hxw⟩
  · intro K hKM L hLM hKL
    have hKmax := (Finset.mem_filter.mp hKM).2
    have hLmax := (Finset.mem_filter.mp hLM).2
    obtain ⟨v, rfl⟩ := hnative K hKM
    obtain ⟨w, rfl⟩ := hnative L hLM
    rcases hnested v w with hsub | hsub | hdisj
    · exact (hKL (hKmax.eq_of_le hLmax.prop hsub)).elim
    · exact (hKL (hLmax.eq_of_le hKmax.prop hsub).symm).elim
    · obtain ⟨-, hvcompact, hvreg, -⟩ := hgeometry v
      obtain ⟨-, hwcompact, hwreg, -⟩ := hgeometry w
      change closure (interior (principal_component_step3_nativeHull A k v)) =
        principal_component_step3_nativeHull A k v at hvreg
      change closure (interior (principal_component_step3_nativeHull A k w)) =
        principal_component_step3_nativeHull A k w at hwreg
      have hleft : Disjoint (principal_component_step3_nativeHull A k v)
          (interior (principal_component_step3_nativeHull A k w)) := by
        rw [← hvreg]
        exact hdisj.closure_left isOpen_interior
      have hright : Disjoint (interior (principal_component_step3_nativeHull A k v))
          (principal_component_step3_nativeHull A k w) := by
        rw [← hwreg]
        exact hdisj.closure_right isOpen_interior
      intro x hx
      exact ⟨⟨hvcompact.isClosed.closure_eq.symm ▸ hx.1,
        fun hxi => Set.disjoint_left.mp hright hxi hx.2⟩,
        ⟨hwcompact.isClosed.closure_eq.symm ▸ hx.2,
        fun hxi => Set.disjoint_left.mp hleft hx.1 hxi⟩⟩

/-- Step 3 of the V4 proof of `principal_component` (V4 1.24): "if `K` lies
at positive distance from the boundary ... then `∂K ⊆ Sk_k(A)`". The local
form only needs each boundary point to be in the prototype interior. -/
private theorem principal_component_step3_boundary_internal (A : S.ι) (k : ℕ)
    (w : S.RoleWord A k)
    (hinside : frontier (principal_component_step3_nativeHull A k w) ⊆
      interior (S.proto A).carrier) :
    frontier (principal_component_step3_nativeHull A k w) ⊆ internalSkeleton S A k := by
  obtain ⟨-, -, -, -, -, -, hfacets⟩ :=
    principal_component_step1_hull_geometry (S.proto (S.nativeTile A k w).ty)
      (S.cx (S.nativeTile A k w).ty) (prototypeDescendantFrame A k w)
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.mp (hfacets hx)
  have hcell : (S.σ ^ k) x ∈ (S.nativeTile A k w).cell 0 f.val := by
    obtain ⟨y, hy, rfl⟩ := hxf
    refine ⟨y, hy, ?_⟩
    simp [prototypeDescendantFrame, FramedNode.prototypeFrame]
  have hinterior : (S.σ ^ k) x ∈ interior (S.supertile k A) := by
    let e := (S.σ ^ k).toContinuousLinearEquiv.toHomeomorph
    change e x ∈ interior (e '' (S.proto A).carrier)
    rw [← e.image_interior]
    exact ⟨x, hinside hx, rfl⟩
  exact ⟨w, f, fun h => (h hcell).2 hinterior, hcell⟩

/-- Step 4 of the V4 proof of `principal_component` (V4 1.24): "Replace each
maximal subpath inside a maximal hull `K` by a path in `∂K`". For the required
connectedness conclusion, finite closed-cover gluing suffices: the hulls met by
a connected set have a connected intersection graph, and every intersection
belongs to both connected boundaries. This avoids general-position choices. -/
private theorem principal_component_step4_boundary_detour
    (C : Set (E d)) (hC : IsConnected C) (M : Finset (Set (E d)))
    (hcover : C ⊆ ⋃ K ∈ M, K)
    (hclosed : ∀ K ∈ M, IsClosed K)
    (hmeet : ∀ K ∈ M, (C ∩ K).Nonempty)
    (hboundary : ∀ K ∈ M, IsConnected (frontier K))
    (hoverlap : ∀ K ∈ M, ∀ L ∈ M, K ≠ L → K ∩ L ⊆ frontier K ∩ frontier L) :
    IsConnected (⋃ K ∈ M, frontier K) := by
  classical
  let B := ⋃ K ∈ M, frontier K
  obtain ⟨p, hp⟩ := hC.nonempty
  obtain ⟨K₀, hK₀, -⟩ := Set.mem_iUnion₂.mp (hcover hp)
  obtain ⟨x, hx⟩ := (hboundary K₀ hK₀).nonempty
  have hsub : ∀ K ∈ M, frontier K ⊆ B :=
    fun K hK y hy => Set.mem_iUnion₂.mpr ⟨K, hK, hy⟩
  have hxB : x ∈ B := hsub K₀ hK₀ hx
  let E₀ := connectedComponentIn B x
  have hjoin : ∀ K ∈ M, (frontier K ∩ E₀).Nonempty → frontier K ⊆ E₀ := by
    intro K hK ⟨y, hyK, hyE⟩
    change frontier K ⊆ connectedComponentIn B x
    rw [connectedComponentIn_eq hyE]
    exact (hboundary K hK).isPreconnected.subset_connectedComponentIn hyK (hsub K hK)
  have hK₀E : frontier K₀ ⊆ E₀ :=
    (hboundary K₀ hK₀).isPreconnected.subset_connectedComponentIn hx (hsub K₀ hK₀)
  let good := M.filter (fun K => frontier K ⊆ E₀)
  let bad := M.filter (fun K => ¬ frontier K ⊆ E₀)
  have hclosedGood : IsClosed (⋃ K ∈ good, K) :=
    isClosed_biUnion_finset (fun K hK => hclosed K (Finset.mem_filter.mp hK).1)
  have hclosedBad : IsClosed (⋃ K ∈ bad, K) :=
    isClosed_biUnion_finset (fun K hK => hclosed K (Finset.mem_filter.mp hK).1)
  have hcover' : C ⊆ (⋃ K ∈ good, K) ∪ (⋃ K ∈ bad, K) := by
    intro y hy
    obtain ⟨K, hKM, hyK⟩ := Set.mem_iUnion₂.mp (hcover hy)
    by_cases hKE : frontier K ⊆ E₀
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨K, Finset.mem_filter.mpr ⟨hKM, hKE⟩, hyK⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨K, Finset.mem_filter.mpr ⟨hKM, hKE⟩, hyK⟩)
  have hall : ∀ K ∈ M, frontier K ⊆ E₀ := by
    intro K hKM
    by_contra hKE
    obtain ⟨a, haC, haK₀⟩ := hmeet K₀ hK₀
    obtain ⟨b, hbC, hbK⟩ := hmeet K hKM
    obtain ⟨z, -, hzGood, hzBad⟩ := isPreconnected_closed_iff.mp hC.isPreconnected
      _ _ hclosedGood hclosedBad hcover'
      ⟨a, haC, Set.mem_iUnion₂.mpr ⟨K₀, Finset.mem_filter.mpr ⟨hK₀, hK₀E⟩, haK₀⟩⟩
      ⟨b, hbC, Set.mem_iUnion₂.mpr ⟨K, Finset.mem_filter.mpr ⟨hKM, hKE⟩, hbK⟩⟩
    obtain ⟨J, hJ, hzJ⟩ := Set.mem_iUnion₂.mp hzGood
    obtain ⟨L, hL, hzL⟩ := Set.mem_iUnion₂.mp hzBad
    obtain ⟨hJM, hJE⟩ := Finset.mem_filter.mp hJ
    obtain ⟨hLM, hLE⟩ := Finset.mem_filter.mp hL
    have hJL : J ≠ L := by
      intro h
      exact hLE (h ▸ hJE)
    have hzbd := hoverlap J hJM L hLM hJL ⟨hzJ, hzL⟩
    exact hLE (hjoin L hLM ⟨z, hzbd.2, hJE hzbd.1⟩)
  have hBE : B ⊆ E₀ := by
    intro y hy
    obtain ⟨K, hKM, hyK⟩ := Set.mem_iUnion₂.mp hy
    exact hall K hKM hyK
  have hEq : B = E₀ := hBE.antisymm (connectedComponentIn_subset B x)
  rw [show (⋃ K ∈ M, frontier K) = E₀ from hEq]
  exact isConnected_connectedComponentIn_iff.mpr hxB

/-- Step 5 of the V4 proof of `principal_component` (V4 1.24): "choose ... a
point `p_i ∈ relint Φ_i ∩ int σ^r A` ... and a relative `(d-1)`-disc".
Only a second, distinct point of the facet is needed below: a sufficiently
small hull containing `p_i` cannot contain this whole connected facet. -/
private theorem principal_component_step5_facet_points {A : S.ι}
    (f : PrimitiveFacet S A) :
    ∃ p ∈ f.carrier, p ∈ interior (S.proto A).carrier ∧
      ∃ q ∈ f.carrier, p ≠ q := by
  obtain ⟨i, e, he, hrel⟩ := f.realization
  obtain ⟨u, hu⟩ := e.val.flat.relint_nonempty
  have hue : u ∈ e.val.carrier := intrinsicInterior_subset hu
  have htwo : ∃ v ∈ e.val.carrier, u ≠ v := by
    by_contra hn
    have heq : e.val.carrier = {u} := by
      apply Set.Subset.antisymm
      · intro v hv
        have huv : u = v := by
          by_contra huv
          exact hn ⟨v, hv, huv⟩
        exact Set.mem_singleton_iff.mpr huv.symm
      · exact singleton_subset_iff.mpr hue
    have hdim := e.val.flat.dimension
    have hedim : e.val.dim = d - 1 := (Finset.mem_filter.mp e.property).2
    have hd : 2 ≤ d := Fact.out
    rw [cellDirection, heq, direction_affineSpan, vectorSpan_singleton,
      finrank_bot] at hdim
    omega
  obtain ⟨v, hv, huv⟩ := htwo
  let ψ := ((S.child (S.nativeTile A f.depth f.word).ty i).frame.toAffineEquiv.trans
    S.σ.symm.toAffineEquiv).trans f.birthFrame
  have hcarrier : f.carrier = ψ '' e.val.carrier := by
    simp [PrimitiveFacet.carrier, he, placedSet, ψ, Set.image_image]
  have hlocal : (S.child (S.nativeTile A f.depth f.word).ty i).frame u ∈
      relint f.localCarrier := by
    rw [he]
    change (S.child (S.nativeTile A f.depth f.word).ty i).frame u ∈
      intrinsicInterior ℝ ((S.child (S.nativeTile A f.depth f.word).ty i).frame.toAffineIsometry ''
        e.val.carrier)
    rw [(S.child (S.nativeTile A f.depth f.word).ty i).frame.toAffineIsometry.image_intrinsicInterior]
    exact ⟨u, hu, rfl⟩
  have hnormal : S.σ.symm ((S.child (S.nativeTile A f.depth f.word).ty i).frame u) ∈
      interior (S.proto (S.nativeTile A f.depth f.word).ty).carrier := by
    let L := S.σ.toContinuousLinearEquiv.toHomeomorph
    have hh : (S.child (S.nativeTile A f.depth f.word).ty i).frame u ∈
        L '' interior (S.proto (S.nativeTile A f.depth f.word).ty).carrier := by
      rw [L.image_interior]
      simpa [SubstSystem.supertile] using hrel hlocal
    obtain ⟨z, hz, hzeq⟩ := hh
    have hzeq' : z = S.σ.symm ((S.child (S.nativeTile A f.depth f.word).ty i).frame u) :=
      (S.σ.symm_apply_apply z).symm.trans (congrArg S.σ.symm hzeq)
    exact hzeq' ▸ hz
  have hparent : f.birthFrame '' (S.proto (S.nativeTile A f.depth f.word).ty).carrier ⊆
      (S.proto A).carrier := by
    have hsub : (S.nativeTile A f.depth f.word).carrier 0 ⊆ S.supertile f.depth A := by
      rw [← S.native_cover A f.depth]
      exact Set.subset_iUnion
        (fun w : S.RoleWord A f.depth => (S.nativeTile A f.depth w).carrier 0) f.word
    have hsub' := Set.image_mono (f := (S.σ ^ f.depth).symm) hsub
    simpa [PrimitiveFacet.birthFrame, prototypeDescendantFrame, FramedNode.carrier,
      placedSet, SubstSystem.supertile, Set.image_image] using hsub'
  refine ⟨ψ u, hcarrier ▸ Set.mem_image_of_mem ψ hue, ?_,
    ψ v, hcarrier ▸ Set.mem_image_of_mem ψ hv, fun h => huv (ψ.injective h)⟩
  apply interior_mono hparent
  change f.birthFrame (S.σ.symm ((S.child (S.nativeTile A f.depth f.word).ty i).frame u)) ∈
    interior (f.birthFrame '' (S.proto (S.nativeTile A f.depth f.word).ty).carrier)
  have hframe := f.birthFrame.toHomeomorphOfFiniteDimensional.image_interior
    (S.proto (S.nativeTile A f.depth f.word).ty).carrier
  change f.birthFrame '' interior (S.proto (S.nativeTile A f.depth f.word).ty).carrier =
    interior (f.birthFrame '' (S.proto (S.nativeTile A f.depth f.word).ty).carrier) at hframe
  rw [← hframe]
  exact ⟨_, hnormal, rfl⟩

/-- Step 5 of the V4 proof of `principal_component` (V4 1.24): "choose
polygonal paths ... joining these points ... Their union ... is a compact
subset of that interior". Continuous paths suffice here. A nonempty connected
open set also supplies a compact connector for the empty list of points. -/
private theorem principal_component_step5_compact_connector
    (U : Set (E d)) (hU : IsOpen U) (hc : IsConnected U)
    (p : Finset (E d)) (hp : (p : Set (E d)) ⊆ U) :
    ∃ C : Set (E d), IsCompact C ∧ IsConnected C ∧ C ⊆ U ∧ (p : Set (E d)) ⊆ C := by
  classical
  induction p using Finset.induction_on with
  | empty =>
    obtain ⟨x, hx⟩ := hc.nonempty
    exact ⟨{x}, isCompact_singleton, isConnected_singleton, singleton_subset_iff.mpr hx,
      by simp⟩
  | @insert x p hxp ih =>
    obtain ⟨C, hCcompact, hCconn, hCU, hpC⟩ := ih (by
      intro y hy
      exact hp (Finset.mem_insert_of_mem hy))
    obtain ⟨z, hz⟩ := hCconn.nonempty
    have hpath := (hU.isConnected_iff_isPathConnected.mp hc).joinedIn
      x (hp (Finset.mem_insert_self x p)) z (hCU hz)
    let γ := hpath.somePath
    refine ⟨C ∪ Set.range γ, hCcompact.union (isCompact_range γ.continuous),
      hCconn.union ?_ (isConnected_range γ.continuous), ?_, ?_⟩
    · exact ⟨z, hz, γ.target_mem_range⟩
    · rintro y (hy | ⟨t, rfl⟩)
      · exact hCU hy
      · exact hpath.somePath_mem t
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Or.inr γ.source_mem_range
      · exact Or.inl (hpC hy)

/-- Step 5 of the V4 proof of `principal_component` (V4 1.24): "choose `k`
so that all clearances exceed `3D` and each inflated disc contains a segment
of length `> D`". In normalized coordinates the equivalent quantitative fact
is that every native convex hull has arbitrarily small diameter, uniformly in
the role word. This uses only strict expansion and the finite prototype list. -/
private theorem principal_component_step5_small_hulls (A : S.ι) (r : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, r ≤ k ∧ 1 ≤ k ∧ ∀ w : S.RoleWord A k,
      ∀ x ∈ convexHull ℝ
        (prototypeDescendantFrame A k w '' (S.proto (S.nativeTile A k w).ty).carrier),
      ∀ y ∈ convexHull ℝ
        (prototypeDescendantFrame A k w '' (S.proto (S.nativeTile A k w).ty).carrier),
      dist x y < δ := by
  have hc : 0 < S.c := lt_trans zero_lt_one S.c_gt_one
  have hexpand : ∀ n : ℕ, ∀ x : E d, S.c ^ n * ‖x‖ ≤ ‖(S.σ ^ n) x‖ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      calc
        S.c ^ (n + 1) * ‖x‖ = S.c * (S.c ^ n * ‖x‖) := by ring
        _ ≤ S.c * ‖(S.σ ^ n) x‖ := mul_le_mul_of_nonneg_left (ih x) hc.le
        _ ≤ ‖S.σ ((S.σ ^ n) x)‖ := S.expand _
        _ = ‖(S.σ ^ (n + 1)) x‖ := by rw [pow_succ']; rfl
  have hdist : ∀ n : ℕ, ∀ x y : E d,
      S.c ^ n * dist x y ≤ dist ((S.σ ^ n) x) ((S.σ ^ n) y) := by
    intro n x y
    simpa only [dist_eq_norm, map_sub] using hexpand n (x - y)
  let T := ⋃ B : S.ι, (S.proto B).carrier
  have hT : IsCompact T := isCompact_iUnion (fun B => (S.proto B).compact)
  have hlarge : ∀ᶠ k : ℕ in Filter.atTop, Metric.diam T < S.c ^ k * δ := by
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt S.c_gt_one).eventually
      (Filter.eventually_gt_atTop (Metric.diam T / δ))] with k hk
    exact (div_lt_iff₀ hδ).mp hk
  obtain ⟨k, hk, hlarge⟩ := ((Filter.eventually_ge_atTop (max r 1)).and hlarge).exists
  refine ⟨k, (le_max_left _ _).trans hk, (le_max_right _ _).trans hk, ?_⟩
  intro w x hx y hy
  obtain ⟨x', ⟨u, hu, rfl⟩, y', ⟨v, hv, rfl⟩, hxy⟩ :=
    convexHull_exists_dist_ge2 hx hy
  apply hxy.trans_lt
  have huv : dist u v ≤ Metric.diam T := Metric.dist_le_diam_of_mem hT.isBounded
    (Set.mem_iUnion.mpr ⟨(S.nativeTile A k w).ty, hu⟩)
    (Set.mem_iUnion.mpr ⟨(S.nativeTile A k w).ty, hv⟩)
  have hscaled : S.c ^ k * dist (prototypeDescendantFrame A k w u)
      (prototypeDescendantFrame A k w v) ≤ dist u v := by
    simpa [prototypeDescendantFrame, (S.nativeTile A k w).frame.isometry.dist_eq]
      using hdist k (prototypeDescendantFrame A k w u) (prototypeDescendantFrame A k w v)
  exact (mul_lt_mul_iff_right₀ (pow_pos hc k)).mp ((hscaled.trans huv).trans_lt hlarge)

/-- Step 5 of the V4 proof of `principal_component` (V4 1.24): "Its first
boundary point `z_i`". A connected set with a point in a closed hull and a
point outside it meets its frontier; this is the attachment part alone. -/
private theorem principal_component_step5_attach
    (F K : Set (E d)) (hF : IsPreconnected F) (hK : IsClosed K)
    (hin : (F ∩ K).Nonempty) (hout : (F \ K).Nonempty) :
    (F ∩ frontier K).Nonempty := by
  by_contra hn
  have hinside : ∀ x ∈ F, x ∈ K → x ∈ interior K := by
    intro x hx hxK
    by_contra hxi
    exact hn ⟨x, hx, hK.closure_eq.symm ▸ hxK, hxi⟩
  obtain ⟨p, hpF, hpK⟩ := hin
  obtain ⟨q, hqF, hqK⟩ := hout
  obtain ⟨x, -, hxi, hxK⟩ := hF (interior K) Kᶜ isOpen_interior hK.isOpen_compl
    (fun x hx => by
      by_cases hxK : x ∈ K
      · exact Or.inl (hinside x hx hxK)
      · exact Or.inr hxK)
    ⟨p, hpF, hinside p hpF hpK⟩ ⟨q, hqF, hqK⟩
  exact hxK (interior_subset hxi)

/-- Step 5 of the V4 proof of `principal_component` (V4 1.24): "Since ...
`Φ_i` is a union of native facets (heredity)". In normalized coordinates a
primitive facet is in every skeleton above its birth depth. -/
private theorem principal_component_step5_carrier_subset {A : S.ι}
    (f : PrimitiveFacet S A) (k : ℕ) (hk : f.depth < k) :
    f.carrier ⊆ internalSkeleton S A k := by
  rw [internalSkeleton_eq_primitives S A k]
  exact fun _ hx => Set.mem_iUnion.2 ⟨⟨f, hk⟩, hx⟩

/-- Step 5 of the V4 proof of `principal_component` (V4 1.24): "Each required
facet is connected". Its carrier is a continuous affine image of a flat cell. -/
private theorem principal_component_step5_carrier_connected {A : S.ι}
    (f : PrimitiveFacet S A) : IsConnected f.carrier := by
  obtain ⟨i, e, he, -⟩ := f.realization
  have h1 : IsConnected f.localCarrier := by
    rw [he]
    exact e.val.flat.connected.image _
      (AffineIsometryEquiv.continuous (S.child (S.nativeTile A f.depth f.word).ty i).frame).continuousOn
  have h2 : IsConnected (S.σ.symm '' f.localCarrier) :=
    h1.image _ (LinearMap.continuous_of_finiteDimensional
      (S.σ.symm : E d →ₗ[ℝ] E d)).continuousOn
  exact h2.image _ (f.birthFrame.toAffineMap.continuous_of_finiteDimensional).continuousOn

/-- P20, V4 1.24: every finite prescribed list lies in one component after
sufficient refinement. A prototype supplies nonempty geometry even for an empty list. -/
theorem principal_component (A : S.ι) (r : ℕ) (Φ : Finset (PrimitiveFacet S A))
    (hΦ : ∀ f ∈ Φ, f.depth < r) :
    ∃ k : ℕ, r ≤ k ∧ 1 ≤ k ∧ ∃ E₀ : Set (E d),
      IsSkeletonComponent S A k E₀ ∧ ∀ f ∈ Φ, f.carrier ⊆ E₀ := by
  classical
  choose p hp hpint q hq hpq using
    (fun f : PrimitiveFacet S A => principal_component_step5_facet_points f)
  obtain ⟨C, hCcompact, hCconn, hCint, hpC⟩ :=
    principal_component_step5_compact_connector (interior (S.proto A).carrier)
      isOpen_interior (S.proto A).interior_connected (Φ.image p) (by
        intro x hx
        obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hx
        exact hpint f)
  obtain ⟨ε, hε, hclear⟩ :=
    hCcompact.exists_cthickening_subset_open isOpen_interior hCint
  have hscale : ∀ Ψ : Finset (PrimitiveFacet S A),
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∀ f ∈ Ψ, δ < dist (p f) (q f) := by
    intro Ψ
    induction Ψ using Finset.induction_on with
    | empty => exact ⟨ε, hε, le_rfl, by simp⟩
    | @insert f Ψ hf ih =>
      obtain ⟨δ, hδ, hδε, hδf⟩ := ih
      refine ⟨min δ (dist (p f) (q f) / 2),
        lt_min hδ (half_pos (dist_pos.mpr (hpq f))),
        (min_le_left _ _).trans hδε, ?_⟩
      intro g hg
      rcases Finset.mem_insert.mp hg with hg | hg
      · subst g
        exact (min_le_right _ _).trans_lt (half_lt_self (dist_pos.mpr (hpq f)))
      · exact (min_le_left _ _).trans_lt (hδf g hg)
  obtain ⟨δ, hδ, hδε, hδf⟩ := hscale Φ
  obtain ⟨k, hrk, h1k, hsmall⟩ := principal_component_step5_small_hulls A r δ hδ
  obtain ⟨M, hMnative, hMcover, hMpair⟩ := principal_component_step3_maximal_hulls A k
  let L := M.filter (fun K => (C ∩ K).Nonempty)
  have hLmem : ∀ K ∈ L, K ∈ M ∧ (C ∩ K).Nonempty := by
    intro K hK
    exact Finset.mem_filter.mp hK
  have hLcover : C ⊆ ⋃ K ∈ L, K := by
    intro x hx
    obtain ⟨K, hKM, hxK⟩ := Set.mem_iUnion₂.mp (hMcover (interior_subset (hCint hx)))
    exact Set.mem_iUnion₂.mpr ⟨K, Finset.mem_filter.mpr ⟨hKM, x, hx, hxK⟩, hxK⟩
  have hLgeom : ∀ K ∈ L, IsClosed K ∧ IsConnected (frontier K) ∧
      frontier K ⊆ internalSkeleton S A k ∧ ∀ x ∈ K, ∀ y ∈ K, dist x y < δ := by
    intro K hKL
    obtain ⟨w, rfl⟩ := hMnative K (hLmem K hKL).1
    obtain ⟨-, hcompact, -, -, hboundary, hconv, -⟩ :=
      principal_component_step1_hull_geometry (S.proto (S.nativeTile A k w).ty)
        (S.cx (S.nativeTile A k w).ty) (prototypeDescendantFrame A k w)
    have hdiam : ∀ x ∈ principal_component_step3_nativeHull A k w,
        ∀ y ∈ principal_component_step3_nativeHull A k w, dist x y < δ :=
      fun x hx y hy => hsmall w x (hconv hx) y (hconv hy)
    have hinside : principal_component_step3_nativeHull A k w ⊆
        interior (S.proto A).carrier := by
      obtain ⟨z, hzC, hzK⟩ := (hLmem _ hKL).2
      intro x hx
      exact hclear (Metric.mem_cthickening_of_dist_le x z ε C hzC
        ((hdiam x hx z hzK).le.trans hδε))
    exact ⟨hcompact.isClosed, hboundary,
      principal_component_step3_boundary_internal A k w
        ((frontier_subset_iff_isClosed.mpr hcompact.isClosed).trans hinside), hdiam⟩
  have hBconn : IsConnected (⋃ K ∈ L, frontier K) :=
    principal_component_step4_boundary_detour C hCconn L hLcover
      (fun K hK => (hLgeom K hK).1) (fun K hK => (hLmem K hK).2)
      (fun K hK => (hLgeom K hK).2.1)
      (fun K hK J hJ => hMpair K (hLmem K hK).1 J (hLmem J hJ).1)
  have hBsk : (⋃ K ∈ L, frontier K) ⊆ internalSkeleton S A k := by
    intro x hx
    obtain ⟨K, hKL, hxK⟩ := Set.mem_iUnion₂.mp hx
    exact (hLgeom K hKL).2.2.1 hxK
  obtain ⟨x, hxB⟩ := hBconn.nonempty
  let E₀ := connectedComponentIn (internalSkeleton S A k) x
  have hBE : (⋃ K ∈ L, frontier K) ⊆ E₀ :=
    hBconn.isPreconnected.subset_connectedComponentIn hxB hBsk
  refine ⟨k, hrk, h1k, E₀, ⟨x, hBsk hxB, rfl⟩, ?_⟩
  intro f hf
  have hpfC : p f ∈ C := hpC (Finset.mem_image.mpr ⟨f, hf, rfl⟩)
  obtain ⟨K, hKL, hpfK⟩ := Set.mem_iUnion₂.mp (hLcover hpfC)
  have hqfK : q f ∉ K := by
    intro hqfK
    exact (lt_asymm (hδf f hf) ((hLgeom K hKL).2.2.2 _ hpfK _ hqfK))
  obtain ⟨z, hzf, hzK⟩ := principal_component_step5_attach f.carrier K
    (principal_component_step5_carrier_connected f).isPreconnected
    (hLgeom K hKL).1 ⟨p f, hp f, hpfK⟩ ⟨q f, hq f, hqfK⟩
  have hzE : z ∈ E₀ := hBE (Set.mem_iUnion₂.mpr ⟨K, hKL, hzK⟩)
  change f.carrier ⊆ connectedComponentIn (internalSkeleton S A k) x
  rw [connectedComponentIn_eq hzE]
  exact (principal_component_step5_carrier_connected f).isPreconnected.subset_connectedComponentIn
    hzf (principal_component_step5_carrier_subset f k ((hΦ f hf).trans_le hrk))

/-- P20, V4 1.24: all facets meeting the component are wholly contained in it,
and their union is the entire component. -/
theorem principalFacets_spec (A : S.ι) (k : ℕ) (E₀ : Set (E d))
    (hE : IsSkeletonComponent S A k E₀) :
    (principalFacets S A k E₀).Finite ∧
      (∀ f ∈ principalFacets S A k E₀, f.carrier ⊆ E₀) ∧
      E₀ = ⋃ f ∈ principalFacets S A k E₀, f.carrier := by
  sorry

/-- Step 1 of the V4 proof of `principal_component_refines` (V4 1.24): the
internal skeleton increases with the depth (it is the union of the primitive
facets born before that depth). -/
private theorem principal_component_refines_step1_skeleton_mono (A : S.ι) (k l : ℕ)
    (hkl : k ≤ l) : internalSkeleton S A k ⊆ internalSkeleton S A l := by
  rw [internalSkeleton_eq_primitives, internalSkeleton_eq_primitives]
  intro x hx
  simp only [Set.mem_iUnion, Subtype.exists] at hx ⊢
  rcases hx with ⟨f, hfk, hx⟩
  exact ⟨f, lt_of_lt_of_le hfk hkl, hx⟩

/-- P20, V4 1.24: principal-component choices persist under further refinement. -/
theorem principal_component_refines (A : S.ι) (k l : ℕ) (hkl : k ≤ l)
    (E₀ : Set (E d)) (hE : IsSkeletonComponent S A k E₀) :
    ∃ E₁ : Set (E d), IsSkeletonComponent S A l E₁ ∧ E₀ ⊆ E₁ := by
  obtain ⟨x, hx, rfl⟩ := hE
  have hmono := principal_component_refines_step1_skeleton_mono (S := S) A k l hkl
  exact ⟨connectedComponentIn (internalSkeleton S A l) x, ⟨x, hmono hx, rfl⟩,
    connectedComponentIn_mono x hmono⟩

/-- P21, V4 1.25: same-parent links include a common-listed vertex of both facets. -/
def SameParentLink {A : S.ι} (f g : PrimitiveFacet S A) : Prop :=
  f.birthAddress = g.birthAddress ∧ ∃ q : E d,
    f.IsVertex q ∧ g.IsVertex q ∧ f.CommonListed q

/-- P21, V4 1.25: ascent links include the exact birth-tree ancestry, a facet
of the lower birth node in the higher provider, a common-listed seed, and an
`e`-facing port. Thus zero-trace sectors are retained without inventing a port. -/
def AscentLink {A : S.ι} (k : ℕ) (f g : PrimitiveFacet S A) : Prop :=
  g.depth < f.depth ∧
    (f.birthNode k).IsDescendant (k - f.depth) (g.birthNode k) (k - g.depth) ∧
    ∃ e : FacetName S f.birthType, f.birthCell e.val ⊆ g.carrier ∧
      ∃ q : E d, f.IsVertex q ∧ q ∈ f.birthCell e.val ∧ f.CommonListed q ∧
        ∃ (i : S.I f.birthType) (c : FacetName S (S.child f.birthType i).ty),
          q ∈ f.childCell i c.val ∧ f.childCell i c.val ⊆ f.birthCell e.val

/-- P21, V4 1.25: the undirected routing links. -/
def RoutingLink {A : S.ι} (k : ℕ) (f g : PrimitiveFacet S A) : Prop :=
  SameParentLink f g ∨ AscentLink k f g ∨ AscentLink k g f

/-- P21, V4 1.25: restrict any link to principal facets passing through `p`. -/
def ThroughLink {A : S.ι} (Q : Set (PrimitiveFacet S A)) (p : E d)
    (R : PrimitiveFacet S A → PrimitiveFacet S A → Prop)
    (f g : PrimitiveFacet S A) : Prop :=
  f ∈ Q ∧ p ∈ f.carrier ∧ g ∈ Q ∧ p ∈ g.carrier ∧ R f g

/-- Step 1 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"Let `P₀` be the least common ancestor within `A`'s subdivision of all native
... tiles of `A` containing `p`". Record its standard address, the common
ancestry condition, and minimal height, before proving its existence. -/
private def birth_ascent_routing_step1_top_birth
    (A : S.ι) (k : ℕ) (p : E d) (b : ℕ) (P : FramedNode S) : Prop :=
  S.IsStandardNode A k b P ∧
    (∀ w : S.RoleWord A k, (S.σ ^ k) p ∈ (S.nativeTile A k w).carrier 0 →
      (S.nativeTile A k w).IsDescendant 0 P b) ∧
    ∀ (b' : ℕ) (P' : FramedNode S), S.IsStandardNode A k b' P' →
      (∀ w : S.RoleWord A k, (S.σ ^ k) p ∈ (S.nativeTile A k w).carrier 0 →
        (S.nativeTile A k w).IsDescendant 0 P' b') → b ≤ b'

/-- Step 7 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"the facets of the top class (those born in the least common ancestor `P₀`)".
Membership retains both the point and the selected principal component. -/
private def birth_ascent_routing_step7_top_class
    (A : S.ι) (k : ℕ) (E₀ : Set (E d)) (p : E d)
    (b : ℕ) (P : FramedNode S) : Set (PrimitiveFacet S A) :=
  {f | f ∈ principalFacets S A k E₀ ∧ p ∈ f.carrier ∧
    k - f.depth = b ∧ f.birthNode k = P}

/-- Step 1 of the V4 proof of `birth_ascent_routing` (V4 1.25): "Let `P₀` be
the least common ancestor within `A`'s subdivision of all native ... tiles
of `A` containing `p`". The root is a common ancestor, so the set of possible
heights has a least element, even before positivity is established. -/
private theorem birth_ascent_routing_step1_least_height (A : S.ι) (k : ℕ) (p : E d) :
    ∃ (b : ℕ) (P : FramedNode S), b ≤ k ∧ birth_ascent_routing_step1_top_birth A k p b P := by
  classical
  let Q : ℕ → Prop := fun b => ∃ P : FramedNode S,
    S.IsStandardNode A k b P ∧
      ∀ w : S.RoleWord A k, (S.σ ^ k) p ∈ (S.nativeTile A k w).carrier 0 →
        (S.nativeTile A k w).IsDescendant 0 P b
  have hroot : Q k := by
    refine ⟨⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩,
      ⟨0, by omega, (), rfl⟩, ?_⟩
    intro w _
    refine ⟨k, by omega, w, ?_⟩
    simp [SubstSystem.nativeTile, FramedNode.move]
  have hex : ∃ b, Q b := ⟨k, hroot⟩
  obtain ⟨P, hP, hleaves⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, P, Nat.find_min' hex hroot, hP, hleaves, ?_⟩
  intro b' P' hP' hleaves'
  exact Nat.find_min' hex ⟨P', hP', hleaves'⟩

open scoped Topology in
/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "Any vertex `q` of `κ`".
An extreme point in the relative interior of a cell forces that cell to be a singleton. -/
private theorem birth_ascent_routing_step2_extreme_relint_singleton (K L : Set (E d)) (hLK : L ⊆ K)
    (q : E d) (hq : q ∈ K.extremePoints ℝ) (hqL : q ∈ relint L) : L = {q} := by
  obtain ⟨q', hq', rfl⟩ := mem_intrinsicInterior.mp hqL
  have hqL : (q' : E d) ∈ L := (show q' ∈ Subtype.val ⁻¹' L from interior_subset hq')
  apply Set.Subset.antisymm
  · intro x hx
    let γ : ℝ → affineSpan ℝ L := fun t =>
      ⟨AffineMap.lineMap (q' : E d) x t,
        AffineMap.lineMap_mem t q'.property (subset_affineSpan ℝ L hx)⟩
    have hγ : Continuous γ := by fun_prop
    have hsmall : ∀ᶠ t : ℝ in 𝓝 0,
        (γ t : E d) ∈ L ∧ (γ (-t) : E d) ∈ L := by
      have h₁ : Filter.Tendsto γ (𝓝 0) (𝓝 q') := by
        simpa [γ] using hγ.tendsto 0
      have h₂ : Filter.Tendsto (fun t => γ (-t)) (𝓝 0) (𝓝 q') := by
        simpa [γ] using (hγ.comp continuous_neg).tendsto 0
      exact Filter.Eventually.and (h₁ (mem_interior_iff_mem_nhds.mp hq'))
        (h₂ (mem_interior_iff_mem_nhds.mp hq'))
    obtain ⟨ε, hε, hεL⟩ := Metric.eventually_nhds_iff.mp hsmall
    let t := ε / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have htε : dist t 0 < ε := by simp [t, abs_of_pos hε]; linarith
    obtain ⟨hplus, hminus⟩ := hεL htε
    have hseg : (q' : E d) ∈ openSegment ℝ (γ t : E d) (γ (-t) : E d) := by
      refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
      simp only [γ, AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
      module
    have hplus_eq : (γ t : E d) = (q' : E d) := hq.2 (hLK hplus) (hLK hminus) hseg
    have hzero : t • (x - (q' : E d)) = 0 := by
      simpa [γ, AffineMap.lineMap_apply] using hplus_eq
    have hxeq : x = (q' : E d) := sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left ht.ne')
    exact Set.mem_singleton_iff.mpr hxeq
  · exact singleton_subset_iff.mpr hqL

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "Any vertex `q` of `κ`".
Every listed cell contains a listed vertex, obtained from an extreme point and its minimal cell. -/
private theorem birth_ascent_routing_step2_cell_vertex (P : PolyManifoldDomain d) (C : CellComplex P)
    (e : Cell d) (he : e ∈ C.cells) :
    ∃ v ∈ C.vertices, v.carrier ⊆ e.carrier := by
  obtain ⟨q, hq⟩ := e.flat.compact.extremePoints_nonempty e.flat.connected.nonempty
  have hqP : q ∈ frontier P.carrier := by
    rw [← C.carriers_cover]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hq.1⟩
  let v := C.minimalCell q hqP
  have hv := C.minimalCell_mem q hqP
  have hvsub := C.minimalCell_subset q hqP e he hq.1
  have hvsing : v.carrier = {q} := birth_ascent_routing_step2_extreme_relint_singleton e.carrier v.carrier hvsub q hq
    (C.mem_relint_minimalCell q hqP)
  refine ⟨v, Finset.mem_filter.mpr ⟨hv, ?_⟩, hvsub⟩
  have hdim := v.flat.dimension
  rw [cellDirection, hvsing, direction_affineSpan, vectorSpan_singleton, finrank_bot] at hdim
  exact hdim.symm

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "by Lemma 1.1 within `C`".
The descendant relation includes the node itself with its exact frame. -/
private theorem birth_ascent_routing_step2_desc_refl (N : FramedNode S) (n : ℕ) : N.IsDescendant n N n := by
  refine ⟨0, by omega, (), ?_⟩
  simp [SubstSystem.descendantNode, FramedNode.move]

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "Lemma 1.1 for the ancestor cell `e` of `P_b` and its child `C`".
An immediate child has the required exact descendant witness. -/
private theorem birth_ascent_routing_step2_child_desc (N : FramedNode S) (n : ℕ) (i : S.I N.ty) :
    (N.child n i).IsDescendant n N (n + 1) := by
  refine ⟨1, rfl, ⟨i, ()⟩, ?_⟩
  simp [SubstSystem.descendantNode, FramedNode.move, FramedNode.child]

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "take the minimal cell `κ = mc_C(p)`".
Every placed listed cell belongs to its owner’s frontier. -/
private theorem birth_ascent_routing_step2_cell_front (N : FramedNode S) (n : ℕ)
    (e : Cell d) (he : e ∈ (S.cx N.ty).cells) : N.cell n e ⊆ frontier (N.carrier n) := by
  have hsub : e.carrier ⊆ frontier (S.proto N.ty).carrier := by
    rw [← (S.cx N.ty).carriers_cover]
    exact Set.subset_iUnion₂_of_subset e he (Set.Subset.refl _)
  have hcarrier : N.carrier n = N.prototypeFrame n '' (S.proto N.ty).carrier := by
    simp [FramedNode.carrier, FramedNode.prototypeFrame, placedSet,
      SubstSystem.supertile, Set.image_image]
  rw [hcarrier]
  let H := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  change H '' e.carrier ⊆ frontier (H '' (S.proto N.ty).carrier)
  rw [← H.image_frontier]
  exact Set.image_mono hsub

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "Any vertex `q` of `κ` is a vertex of `C`".
Transport a listed vertex through the full prototype frame. -/
private theorem birth_ascent_routing_step2_placed_vertex (N : FramedNode S) (n : ℕ)
    (e : CellName S N.ty) : ∃ q ∈ N.cell n e.val, N.Lists n q := by
  obtain ⟨v, hv, hve⟩ := birth_ascent_routing_step2_cell_vertex (S.proto N.ty) (S.cx N.ty) e.val e.property
  obtain ⟨q, hq⟩ := v.flat.connected.nonempty
  refine ⟨N.prototypeFrame n q, Set.mem_image_of_mem _ (hve hq), v, hv, ?_⟩
  exact Set.mem_image_of_mem _ hq

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "`κ` is a cell of `C′` ... contained in `f′`".
Sibling minimal-cell equality and vertex inheritance give a common-listed seed. -/
private theorem birth_ascent_routing_step2_sibling_seed (P : FramedNode S) (n : ℕ) (i j : S.I P.ty)
    (f : FacetName S (P.child n i).ty) (g : FacetName S (P.child n j).ty)
    (hint : relint ((P.child n i).cell n f.val) ⊆ interior (P.carrier (n + 1)))
    (hmeet : ((P.child n i).cell n f.val ∩ (P.child n j).cell n g.val).Nonempty) :
    ∃ q : E d, q ∈ (P.child n i).cell n f.val ∧ q ∈ (P.child n j).cell n g.val ∧
      (P.child n i).Lists n q ∧ (P.child n j).Lists n q ∧
      ∀ l : S.I P.ty, q ∈ (P.child n l).carrier n → (P.child n l).Lists n q := by
  obtain ⟨p, hpf, hpg⟩ := hmeet
  have hf := (Finset.mem_filter.mp f.property).1
  have hg := (Finset.mem_filter.mp g.property).1
  have hpi := birth_ascent_routing_step2_cell_front (P.child n i) n f.val hf hpf
  have hpj := birth_ascent_routing_step2_cell_front (P.child n j) n g.val hg hpg
  let e := placedMinimalCell (P.child n i) n p hpi
  have he := placedMinimalCell_spec (P.child n i) n p hpi
  have hef : (P.child n i).cell n e.val ⊆ (P.child n i).cell n f.val :=
    hereditary_trace _ _ n n (birth_ascent_routing_step2_desc_refl _ _) f.val e.val hf e.property ⟨p, he, hpf⟩
  have heg : (P.child n i).cell n e.val ⊆ (P.child n j).cell n g.val := by
    by_cases hij : i = j
    · subst j
      exact hereditary_trace _ _ n n (birth_ascent_routing_step2_desc_refl _ _) g.val e.val hg e.property ⟨p, he, hpg⟩
    · let e' := placedMinimalCell (P.child n j) n p hpj
      have he' := placedMinimalCell_spec (P.child n j) n p hpj
      rw [sibling_minimalCell_eq P n i j hij p e e' he he']
      exact hereditary_trace _ _ n n (birth_ascent_routing_step2_desc_refl _ _) g.val e'.val hg e'.property ⟨p, he', hpg⟩
  obtain ⟨q, hqe, hqi⟩ := birth_ascent_routing_step2_placed_vertex (P.child n i) n e
  have hall := primitive_vertex_listed P n i f hint q hqi (hef hqe)
  refine ⟨q, hef hqe, heg hqe, hqi, hall j ?_, hall⟩
  have hc : IsClosed ((P.child n j).carrier n) := by
    exact (((S.proto (P.child n j).ty).compact.image
      (S.σ ^ n).toContinuousLinearEquiv.continuous).image (P.child n j).frame.continuous).isClosed
  exact (frontier_subset_iff_isClosed.mpr hc) (birth_ascent_routing_step2_cell_front _ _ _ hg (heg hqe))

/-- Step 6 of the V4 proof of `birth_ascent_routing` (V4 1.25): "at least one child containing `q` has a facet piece inside `e`".
Hereditary trace puts a vertex of the minimal child cell on the parent facet; the boundary-facet cover supplies its facing port. -/
private theorem birth_ascent_routing_step6_parent_seed_port (P : FramedNode S) (n : ℕ) (i : S.I P.ty)
    (f : FacetName S (P.child n i).ty) (e : FacetName S P.ty)
    (hint : relint ((P.child n i).cell n f.val) ⊆ interior (P.carrier (n + 1)))
    (hmeet : ((P.child n i).cell n f.val ∩ P.cell (n + 1) e.val).Nonempty) :
    ∃ q : E d, q ∈ (P.child n i).cell n f.val ∧ q ∈ P.cell (n + 1) e.val ∧
      (P.child n i).Lists n q ∧
      (∀ j : S.I P.ty, q ∈ (P.child n j).carrier n → (P.child n j).Lists n q) ∧
      ∃ (j : S.I P.ty) (c : FacetName S (P.child n j).ty),
        q ∈ (P.child n j).cell n c.val ∧ (P.child n j).cell n c.val ⊆ P.cell (n + 1) e.val := by
  obtain ⟨p, hpf, hpe⟩ := hmeet
  have hf := (Finset.mem_filter.mp f.property).1
  have hpi := birth_ascent_routing_step2_cell_front (P.child n i) n f.val hf hpf
  let κ := placedMinimalCell (P.child n i) n p hpi
  have hκ := placedMinimalCell_spec (P.child n i) n p hpi
  have hκf : (P.child n i).cell n κ.val ⊆ (P.child n i).cell n f.val :=
    hereditary_trace _ _ n n (birth_ascent_routing_step2_desc_refl _ _) f.val κ.val hf κ.property ⟨p, hκ, hpf⟩
  have hκe : (P.child n i).cell n κ.val ⊆ P.cell (n + 1) e.val :=
    hereditary_trace _ _ (n + 1) n (birth_ascent_routing_step2_child_desc P n i) e.val κ.val
      (Finset.mem_filter.mp e.property).1 κ.property ⟨p, hκ, hpe⟩
  obtain ⟨q, hqκ, hqi⟩ := birth_ascent_routing_step2_placed_vertex (P.child n i) n κ
  refine ⟨q, hκf hqκ, hκe hqκ, hqi,
    primitive_vertex_listed P n i f hint q hqi (hκf hqκ), ?_⟩
  have hqe := hκe hqκ
  rw [← (boundary_facet_adjacency P n e).1] at hqe
  obtain ⟨a, hqa⟩ := Set.mem_iUnion.mp hqe
  exact ⟨a.val.1, a.val.2, hqa, a.property⟩

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "both first-generation facets of `P₀`".
At height zero the prescribed child placement is the original rigid frame. -/
private theorem birth_ascent_routing_step2_place_zero (B : S.ι) (i : S.I B) : S.placeChild 0 i = (S.child B i).frame := by
  ext x
  simp [SubstSystem.placeChild, SubstSystem.childRotation, linearConj, Child.frame, rigidMotion]

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "both first-generation facets of `P₀`".
Identify the listed cell of a standard ground child with its prescribed placement. -/
private theorem birth_ascent_routing_step2_child_cell_zero (B : S.ι) (i : S.I B) (e : Cell d) :
    ((⟨B, AffineIsometryEquiv.refl ℝ (E d)⟩ : FramedNode S).child 0 i).cell 0 e =
      placedSet (S.child B i).frame e.carrier := by
  simp [FramedNode.cell, FramedNode.prototypeFrame, FramedNode.child, birth_ascent_routing_step2_place_zero, placedSet]

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "owners ... children of `P₀`".
Identify the ground child support in the same coordinates. -/
private theorem birth_ascent_routing_step2_child_support_zero (B : S.ι) (i : S.I B) :
    ((⟨B, AffineIsometryEquiv.refl ℝ (E d)⟩ : FramedNode S).child 0 i).carrier 0 =
      placedSet (S.child B i).frame (S.proto (S.child B i).ty).carrier := by
  simp [FramedNode.carrier, SubstSystem.supertile, FramedNode.child, birth_ascent_routing_step2_place_zero, placedSet]

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "common-listed in `P₀`’s immediate subdivision".
Common listedness is preserved by the normalized birth frame. -/
private theorem birth_ascent_routing_step2_local_common {A : S.ι} (f : PrimitiveFacet S A) (q : E d)
    (h : ∀ i : S.I f.birthType,
      q ∈ placedSet (S.child f.birthType i).frame (S.proto (S.child f.birthType i).ty).carrier →
        ∃ v ∈ (S.cx (S.child f.birthType i).ty).vertices,
          q ∈ placedSet (S.child f.birthType i).frame v.carrier) :
    f.CommonListed (f.birthFrame (S.σ.symm q)) := by
  intro i hqi
  obtain ⟨a, ⟨b, hb, hab⟩, ha⟩ := hqi
  have hqb : q = b := S.σ.symm.injective (f.birthFrame.injective ha |>.symm.trans hab.symm)
  obtain ⟨v, hv, hqv⟩ := h i (hqb.symm ▸ hb)
  exact ⟨v, hv, S.σ.symm q, ⟨q, hqv, rfl⟩, rfl⟩

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "Any vertex `q` of `κ` is a vertex ... of `f` and `f′`".
The sibling seed transfers to primitive facets with the same full address. -/
private theorem birth_ascent_routing_step2_same_address_seed {A : S.ι} (f g : PrimitiveFacet S A)
    (hparent : f.birthAddress = g.birthAddress)
    (hmeet : (f.carrier ∩ g.carrier).Nonempty) : SameParentLink f g := by
  rcases f with ⟨a, u, F, hF⟩
  rcases g with ⟨b, v, G, hG⟩
  have hab : a = b := congrArg Sigma.fst hparent
  subst b
  have huv : u = v := eq_of_heq (Sigma.mk.inj hparent).2
  subst v
  let f : PrimitiveFacet S A := ⟨a, u, F, hF⟩
  let g : PrimitiveFacet S A := ⟨a, u, G, hG⟩
  change SameParentLink f g
  change (f.carrier ∩ g.carrier).Nonempty at hmeet
  have hF' := hF
  have hG' := hG
  obtain ⟨i, f₀, hFc, hint⟩ := hF'
  obtain ⟨j, g₀, hGc, -⟩ := hG'
  let P : FramedNode S := ⟨f.birthType, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hfcell : (P.child 0 i).cell 0 f₀.val = F := by
    rw [birth_ascent_routing_step2_child_cell_zero]; exact hFc.symm
  have hgcell : (P.child 0 j).cell 0 g₀.val = G := by
    rw [birth_ascent_routing_step2_child_cell_zero]; exact hGc.symm
  have hmeet' : ((P.child 0 i).cell 0 f₀.val ∩ (P.child 0 j).cell 0 g₀.val).Nonempty := by
    rw [hfcell, hgcell]
    obtain ⟨p, ⟨a, ⟨q, hq, hqa⟩, hap⟩, ⟨b, ⟨r, hr, hrb⟩, hbp⟩⟩ := hmeet
    have hqr : q = r := S.σ.symm.injective
      (hqa.trans ((f.birthFrame.injective (hap.trans hbp.symm)).trans hrb.symm))
    exact ⟨q, hq, hqr.symm ▸ hr⟩
  have hint' : relint ((P.child 0 i).cell 0 f₀.val) ⊆ interior (P.carrier 1) := by
    rw [hfcell]
    simpa [P, f, PrimitiveFacet.birthType, FramedNode.carrier, placedSet] using hint
  obtain ⟨q, hqf, hqg, hqi, hqj, hall⟩ := birth_ascent_routing_step2_sibling_seed P 0 i j f₀ g₀ hint' hmeet'
  rw [hfcell] at hqf
  rw [hgcell] at hqg
  refine ⟨rfl, f.birthFrame (S.σ.symm q), ?_, ?_, ?_⟩
  · refine ⟨⟨S.σ.symm q, ⟨q, hqf, rfl⟩, rfl⟩, i, f₀, hFc, ?_⟩
    obtain ⟨v, hv, hqv⟩ := hqi
    rw [birth_ascent_routing_step2_child_cell_zero] at hqv
    exact ⟨v, hv, S.σ.symm q, ⟨q, hqv, rfl⟩, rfl⟩
  · refine ⟨⟨S.σ.symm q, ⟨q, hqg, rfl⟩, rfl⟩, j, g₀, hGc, ?_⟩
    obtain ⟨v, hv, hqv⟩ := hqj
    rw [birth_ascent_routing_step2_child_cell_zero] at hqv
    exact ⟨v, hv, S.σ.symm q, ⟨q, hqv, rfl⟩, rfl⟩
  · apply birth_ascent_routing_step2_local_common f q
    intro l hql
    obtain ⟨v, hv, hqv⟩ := hall l (by simpa [P, birth_ascent_routing_step2_child_support_zero] using hql)
    rw [birth_ascent_routing_step2_child_cell_zero] at hqv
    exact ⟨v, hv, hqv⟩

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "both first-generation facets of `P₀`".
Changing the standard height conjugates each child frame by the expansion. -/
private theorem birth_ascent_routing_step2_place_scaled (n : ℕ) {A : S.ι} (i : S.I A) (x : E d) :
    S.placeChild n i ((S.σ ^ n) x) = (S.σ ^ n) ((S.child A i).frame x) := by
  rw [S.placeChild_apply]
  simp [linearConj, Child.frame, rigidMotion, LinearEquiv.mul_apply,
    zpow_natCast, zpow_neg, AffineIsometryEquiv.coe_trans]

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "both first-generation facets of `P₀`".
The same conjugacy compares any two base heights. -/
private theorem birth_ascent_routing_step2_place_shift (h k : ℕ) {A : S.ι} (i : S.I A) (x : E d) :
    S.placeChild (h + k) i ((S.σ ^ h) x) = (S.σ ^ h) (S.placeChild k i x) := by
  have h₁ := birth_ascent_routing_step2_place_scaled (h + k) i ((S.σ ^ k).symm x)
  have h₂ := birth_ascent_routing_step2_place_scaled k i ((S.σ ^ k).symm x)
  simp only [pow_add, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply] at h₁ h₂
  rw [← h₂] at h₁
  exact h₁

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "both first-generation facets of `P₀`".
Iterating child conjugacy compares the complete descendant frames. -/
private theorem birth_ascent_routing_step2_descendant_scaled (A : S.ι) (h j : ℕ)
    (w : S.RoleWord A j) (x : E d) :
    (S.descendantNode A h j w).frame ((S.σ ^ h) x) =
      (S.σ ^ h) ((S.nativeTile A j w).frame x) := by
  induction j generalizing A with
  | zero => rfl
  | succ j ih =>
    change S.placeChild (h + j) w.1
      ((S.descendantNode (S.child A w.1).ty h j w.2).frame ((S.σ ^ h) x)) =
      (S.σ ^ h) (S.placeChild (0 + j) w.1
        ((S.nativeTile (S.child A w.1).ty j w.2).frame x))
    rw [ih, birth_ascent_routing_step2_place_shift, Nat.zero_add]

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "both first-generation facets of `P₀`".
The type at the end of an address is independent of its base height. -/
private theorem birth_ascent_routing_step2_descendant_type (A : S.ι) (h j : ℕ) (w : S.RoleWord A j) :
    (S.descendantNode A h j w).ty = (S.nativeTile A j w).ty := by
  induction j generalizing A with
  | zero => rfl
  | succ j ih => exact ih (S.child A w.1).ty w.2

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "both first-generation facets of `P₀`".
The level at height `h` is the linear image of the corresponding native partition. -/
private theorem birth_ascent_routing_step2_descendant_carrier (A : S.ι) (h j : ℕ) (w : S.RoleWord A j) :
    (S.descendantNode A h j w).carrier h = (S.σ ^ h) '' (S.nativeTile A j w).carrier 0 := by
  have hz : (S.nativeTile A j w).carrier 0 =
      (S.nativeTile A j w).frame '' (S.proto (S.nativeTile A j w).ty).carrier := by
    simp [FramedNode.carrier, SubstSystem.supertile, placedSet]
  rw [hz]
  simp only [FramedNode.carrier, SubstSystem.supertile, placedSet, birth_ascent_routing_step2_descendant_type]
  rw [Set.image_image, Set.image_image]
  congr 1
  funext x
  exact birth_ascent_routing_step2_descendant_scaled A h j w x

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "born in the same node".
Native interior disjointness makes the address-to-standard-node map injective. -/
private theorem birth_ascent_routing_step2_descendant_injective (A : S.ι) (h j : ℕ) :
    Function.Injective (S.descendantNode A h j) := by
  intro u v huv
  by_contra hne
  have hcar : (S.nativeTile A j u).carrier 0 = (S.nativeTile A j v).carrier 0 := by
    apply Set.image_injective.mpr (S.σ ^ h).injective
    rw [← birth_ascent_routing_step2_descendant_carrier, ← birth_ascent_routing_step2_descendant_carrier, huv]
  have hdisj := S.native_disjoint A j hne
  dsimp only at hdisj
  rw [hcar, disjoint_self] at hdisj
  have hnonempty : (interior ((S.nativeTile A j v).carrier 0)).Nonempty := by
    have hz : (S.nativeTile A j v).carrier 0 =
        (S.nativeTile A j v).frame.toHomeomorph '' (S.proto (S.nativeTile A j v).ty).carrier := by
      simp [FramedNode.carrier, SubstSystem.supertile, placedSet]
    rw [hz, ← (S.nativeTile A j v).frame.toHomeomorph.image_interior]
    exact (S.proto _).interior_nonempty.image _
  exact hnonempty.ne_empty hdisj

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "born in the same node".
Equal positive birth heights and equal standard frames recover the full birth address. -/
private theorem birth_ascent_routing_step2_equal_address {A : S.ι} (k : ℕ) (f g : PrimitiveFacet S A)
    (hf : f.depth < k) (hg : g.depth < k) (hheight : k - f.depth = k - g.depth)
    (hnode : f.birthNode k = g.birthNode k) : f.birthAddress = g.birthAddress := by
  rcases f with ⟨a, u, F, hF⟩
  rcases g with ⟨b, v, G, hG⟩
  have hab : a = b := by change a < k at hf; change b < k at hg; change k - a = k - b at hheight; omega
  subst b
  have huv : u = v := birth_ascent_routing_step2_descendant_injective A (k - a) a hnode
  subst v
  rfl

/-- Step 2 of the V4 proof of `birth_ascent_routing` (V4 1.25): "Any vertex
`q` of `κ` is a vertex ... of `f` and `f'` ... and common-listed in `P₀`'s
immediate subdivision". Equal standard birth nodes at equal positive heights
identify the full birth address, and meeting facets have a same-parent seed. -/
private theorem birth_ascent_routing_step2_same_parent {A : S.ι} (k : ℕ)
    (f g : PrimitiveFacet S A) (hf : f.depth < k) (hg : g.depth < k)
    (hheight : k - f.depth = k - g.depth) (hnode : f.birthNode k = g.birthNode k)
    (hmeet : (f.carrier ∩ g.carrier).Nonempty) : SameParentLink f g := by
  exact birth_ascent_routing_step2_same_address_seed f g
    (birth_ascent_routing_step2_equal_address k f g hf hg hheight hnode) hmeet

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Ambient motion preserves exact node identity. -/
private theorem birth_ascent_routing_step3_move_inj (g : Iso d) : Function.Injective (fun N : FramedNode S => N.move g) := by
  intro N M h
  apply FramedNode.ext
  · have ht := congrArg (fun N : FramedNode S => N.ty) h
    exact ht
  · ext x : 1
    exact g.injective (congrArg (fun N : FramedNode S => N.frame x) h)

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Split a role word at an intermediate ancestor, retaining its complete frame. -/
private theorem birth_ascent_routing_step3_split_word (A : S.ι) (h m j : ℕ) (w : S.RoleWord A (m + j)) :
    ∃ u : S.RoleWord A j, ∃ v : S.RoleWord (S.descendantNode A (h + m) j u).ty m,
      S.descendantNode A h (m + j) w =
        (S.descendantNode (S.descendantNode A (h + m) j u).ty h m v).move
          (S.descendantNode A (h + m) j u).frame := by
  induction j generalizing A with
  | zero =>
    refine ⟨(), w, ?_⟩
    simp [SubstSystem.descendantNode, FramedNode.move]
  | succ j ih =>
    obtain ⟨u, v, hv⟩ := ih (S.child A w.1).ty w.2
    refine ⟨⟨w.1, u⟩, v, ?_⟩
    change (S.descendantNode (S.child A w.1).ty h (m + j) w.2).move
      (S.placeChild (h + (m + j)) w.1) = _
    rw [hv]
    simp [SubstSystem.descendantNode, FramedNode.move, Nat.add_assoc,
      ← AffineIsometryEquiv.trans_assoc]

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Concatenate the path to an ancestor with the path inside that ancestor. -/
private theorem birth_ascent_routing_step3_join_words (A : S.ι) (h m j : ℕ) (u : S.RoleWord A j)
    (v : S.RoleWord (S.descendantNode A (h + m) j u).ty m) :
    ∃ w : S.RoleWord A (m + j),
      S.descendantNode A h (m + j) w =
        (S.descendantNode (S.descendantNode A (h + m) j u).ty h m v).move
          (S.descendantNode A (h + m) j u).frame := by
  induction j generalizing A with
  | zero =>
    refine ⟨v, ?_⟩
    simp [SubstSystem.descendantNode, FramedNode.move]
  | succ j ih =>
    obtain ⟨w, hw⟩ := ih (S.child A u.1).ty u.2 v
    refine ⟨⟨u.1, w⟩, ?_⟩
    change (S.descendantNode (S.child A u.1).ty h (m + j) w).move
      (S.placeChild (h + (m + j)) u.1) = _
    rw [hw]
    simp [SubstSystem.descendantNode, FramedNode.move, Nat.add_assoc,
      ← AffineIsometryEquiv.trans_assoc]

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Compose exact descendant witnesses and their frames. -/
private theorem birth_ascent_routing_step3_desc_trans (L N P : FramedNode S) (a b c : ℕ)
    (hLN : L.IsDescendant a N b) (hNP : N.IsDescendant b P c) : L.IsDescendant a P c := by
  obtain ⟨m, rfl, v, rfl⟩ := hLN
  obtain ⟨j, rfl, u, rfl⟩ := hNP
  obtain ⟨w, hw⟩ := birth_ascent_routing_step3_join_words P.ty a m j u v
  refine ⟨m + j, by omega, w, ?_⟩
  rw [hw]
  rfl

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Every prescribed child carrier is contained in its parent carrier. -/
private theorem birth_ascent_routing_step3_child_subset (N : FramedNode S) (n : ℕ) (i : S.I N.ty) :
    (N.child n i).carrier n ⊆ N.carrier (n + 1) := by
  rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hmem : (S.child N.ty i).frame x ∈ S.σ '' (S.proto N.ty).carrier := by
    rw [S.children_cover]
    exact mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩
  obtain ⟨y, hy, he⟩ := hmem
  refine ⟨(S.σ ^ (n + 1)) y, ⟨y, hy, rfl⟩, ?_⟩
  change N.frame ((S.σ ^ (n + 1)) y) = N.frame (S.placeChild n i ((S.σ ^ n) x))
  rw [birth_ascent_routing_step2_place_scaled, ← he, pow_succ]
  rfl

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Iterate child containment along the exact descendant address. -/
private theorem birth_ascent_routing_step3_desc_subset (D N : FramedNode S) (m n : ℕ)
    (h : D.IsDescendant m N n) : D.carrier m ⊆ N.carrier n := by
  obtain ⟨r, rfl, w, rfl⟩ := h
  induction r generalizing N with
  | zero => simpa [SubstSystem.descendantNode, FramedNode.move] using
      (Subset.rfl : N.carrier m ⊆ N.carrier m)
  | succ r ih =>
    have he : (S.descendantNode N.ty m (r + 1) w).move N.frame =
        (S.descendantNode (N.child (m + r) w.1).ty m r w.2).move
          (N.child (m + r) w.1).frame := rfl
    rw [he]
    exact (ih (N.child (m + r) w.1) w.2).trans (birth_ascent_routing_step3_child_subset N (m + r) w.1)

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Descendants of a standard node remain standard in the same root. -/
private theorem birth_ascent_routing_step3_standard_desc (A : S.ι) (k a b : ℕ) (N P : FramedNode S)
    (hP : S.IsStandardNode A k b P) (hN : N.IsDescendant a P b) :
    S.IsStandardNode A k a N := by
  obtain ⟨m, rfl, v, rfl⟩ := hN
  obtain ⟨j, hj, u, rfl⟩ := hP
  obtain ⟨w, hw⟩ := birth_ascent_routing_step3_join_words A a m j u v
  exact ⟨m + j, by omega, w, hw.symm⟩

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
A standard node has a standard ancestor at each intermediate height. -/
private theorem birth_ascent_routing_step3_standard_raise (A : S.ι) (k a b : ℕ) (N : FramedNode S)
    (hN : S.IsStandardNode A k a N) (hab : a ≤ b) (hbk : b ≤ k) :
    ∃ P : FramedNode S, S.IsStandardNode A k b P ∧ N.IsDescendant a P b := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hab
  obtain ⟨j, hj, w, rfl⟩ := hN
  have hmj : m ≤ j := by omega
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hmj
  obtain ⟨u, v, hv⟩ := birth_ascent_routing_step3_split_word A a m l w
  exact ⟨S.descendantNode A (a + m) l u, ⟨l, by omega, u, rfl⟩, m, rfl, v, hv⟩

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Different standard nodes at one height have disjoint interiors. -/
private theorem birth_ascent_routing_step3_standard_disjoint (A : S.ι) (k n : ℕ) (N P : FramedNode S)
    (hN : S.IsStandardNode A k n N) (hP : S.IsStandardNode A k n P) (hne : N ≠ P) :
    Disjoint (interior (N.carrier n)) (interior (P.carrier n)) := by
  obtain ⟨j, hj, u, rfl⟩ := hN
  obtain ⟨l, hl, v, rfl⟩ := hP
  have hjl : j = l := by omega
  subst l
  have huv : u ≠ v := fun h => hne (h ▸ rfl)
  rw [birth_ascent_routing_step2_descendant_carrier, birth_ascent_routing_step2_descendant_carrier]
  let e := (S.σ ^ n).toContinuousLinearEquiv.toHomeomorph
  change Disjoint (interior (e '' _)) (interior (e '' _))
  rw [← e.image_interior, ← e.image_interior]
  exact Set.disjoint_image_of_injective e.injective (S.native_disjoint A j huv)

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Every placed node has nonempty interior. -/
private theorem birth_ascent_routing_step3_node_interior_nonempty (N : FramedNode S) (n : ℕ) :
    (interior (N.carrier n)).Nonempty := by
  let e := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  have hc : N.carrier n = e '' (S.proto N.ty).carrier := by
    simp [e, FramedNode.prototypeFrame, FramedNode.carrier, SubstSystem.supertile, placedSet,
      Set.image_image]
  rw [hc, ← e.image_interior]
  exact (S.proto N.ty).interior_nonempty.image _

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Two standard nodes at one height sharing a descendant are equal. -/
private theorem birth_ascent_routing_step3_common_desc_eq (A : S.ι) (k n l : ℕ) (N P L : FramedNode S)
    (hN : S.IsStandardNode A k n N) (hP : S.IsStandardNode A k n P)
    (hLN : L.IsDescendant l N n) (hLP : L.IsDescendant l P n) : N = P := by
  by_contra hne
  have hdisj := birth_ascent_routing_step3_standard_disjoint A k n N P hN hP hne
  obtain ⟨x, hx⟩ := birth_ascent_routing_step3_node_interior_nonempty L l
  exact Set.disjoint_left.mp hdisj
    (interior_mono (birth_ascent_routing_step3_desc_subset L N l n hLN) hx)
    (interior_mono (birth_ascent_routing_step3_desc_subset L P l n hLP) hx)

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Standard ancestors of a common descendant are comparable by height. -/
private theorem birth_ascent_routing_step3_common_desc_compare (A : S.ι) (k a b l : ℕ) (N P L : FramedNode S)
    (hN : S.IsStandardNode A k a N) (hP : S.IsStandardNode A k b P)
    (hLN : L.IsDescendant l N a) (hLP : L.IsDescendant l P b) (hab : a ≤ b) :
    N.IsDescendant a P b := by
  have hbk : b ≤ k := by obtain ⟨j, hj, _⟩ := hP; omega
  obtain ⟨Q, hQ, hNQ⟩ := birth_ascent_routing_step3_standard_raise A k a b N hN hab hbk
  have hQP := birth_ascent_routing_step3_common_desc_eq A k b l Q P L hQ hP (birth_ascent_routing_step3_desc_trans L N Q l a b hLN hNQ) hLP
  exact hQP ▸ hNQ

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Native coverage supplies a leaf through any point of a node. -/
private theorem birth_ascent_routing_step3_leaf_through (N : FramedNode S) (n : ℕ) (x : E d) (hx : x ∈ N.carrier n) :
    ∃ L : FramedNode S, L.IsDescendant 0 N n ∧ x ∈ L.carrier 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← S.native_cover] at hy
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hy
  refine ⟨(S.nativeTile N.ty n w).move N.frame, ⟨n, by omega, w, rfl⟩, ?_⟩
  obtain ⟨z, hz, rfl⟩ := hw
  exact ⟨z, hz, rfl⟩

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Distinct child roles give distinct framed nodes. -/
private theorem birth_ascent_routing_step3_child_injective (N : FramedNode S) (n : ℕ) : Function.Injective (N.child n) := by
  intro i j hij
  have hh : (S.descendantNode N.ty n 1 ⟨i, ()⟩).move N.frame =
      (S.descendantNode N.ty n 1 ⟨j, ()⟩).move N.frame := by
    simpa [SubstSystem.descendantNode, FramedNode.child, FramedNode.move] using hij
  have hw := birth_ascent_routing_step2_descendant_injective N.ty n 1 (birth_ascent_routing_step3_move_inj N.frame hh)
  exact congrArg Sigma.fst hw

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
A listed cell lies in its closed owner. -/
private theorem birth_ascent_routing_step3_cell_subset (N : FramedNode S) (n : ℕ)
    (e : Cell d) (he : e ∈ (S.cx N.ty).cells) : N.cell n e ⊆ N.carrier n := by
  have hc : IsClosed (N.carrier n) :=
    (((S.proto N.ty).compact.image (S.σ ^ n).toContinuousLinearEquiv.continuous).image N.frame.continuous).isClosed
  exact (birth_ascent_routing_step2_cell_front N n e he).trans (frontier_subset_iff_isClosed.mpr hc)

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
The normalized birth frame and the standard height-k prototype frame agree after expansion. -/
private theorem birth_ascent_routing_step3_birth_frame {A : S.ι} (f : PrimitiveFacet S A) (k : ℕ)
    (hf : f.depth ≤ k) (x : E d) :
    (S.σ ^ k) (f.birthFrame x) = (f.birthNode k).prototypeFrame (k - f.depth) x := by
  change (S.σ ^ k) ((S.σ ^ f.depth).symm ((S.nativeTile A f.depth f.word).frame x)) =
    (S.descendantNode A (k - f.depth) f.depth f.word).frame ((S.σ ^ (k - f.depth)) x)
  rw [birth_ascent_routing_step2_descendant_scaled]
  have hp : S.σ ^ k = (S.σ ^ (k - f.depth)) * (S.σ ^ f.depth) := by
    rw [← pow_add, Nat.sub_add_cancel hf]
  rw [hp]
  simp

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Internal-facet pairing gives two distinct immediate children through the point, in the standard coordinates. -/
private theorem birth_ascent_routing_step3_primitive_two_children {A : S.ι} (k : ℕ)
    (f : PrimitiveFacet S A) (hf : f.depth < k) (p : E d) (hp : p ∈ f.carrier) :
    ∃ (n : ℕ) (N : FramedNode S), k - f.depth = n + 1 ∧ N = f.birthNode k ∧
      ∃ i j : S.I N.ty, i ≠ j ∧
        (S.σ ^ k) p ∈ (N.child n i).carrier n ∧ (S.σ ^ k) p ∈ (N.child n j).carrier n := by
  have hb : 0 < k - f.depth := by omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  let N : FramedNode S := ⟨f.birthType, (f.birthNode k).frame⟩
  have hN : N = f.birthNode k := by
    apply FramedNode.ext
    · exact (birth_ascent_routing_step2_descendant_type A (k - f.depth) f.depth f.word).symm
    · rfl
  obtain ⟨i, f₀, hF, hint⟩ := f.realization
  let R : FramedNode S := ⟨f.birthType, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hcell : (R.child 0 i).cell 0 f₀.val = f.localCarrier := by
    rw [birth_ascent_routing_step2_child_cell_zero]; exact hF.symm
  have hint' : relint ((R.child 0 i).cell 0 f₀.val) ⊆ interior (R.carrier 1) := by
    rw [hcell]
    simpa [R, FramedNode.carrier, placedSet] using hint
  have hne : (relint ((R.child 0 i).cell 0 f₀.val)).Nonempty := by
    rw [birth_ascent_routing_step2_child_cell_zero]
    change (intrinsicInterior ℝ ((S.child f.birthType i).frame.toAffineIsometry '' f₀.val.carrier)).Nonempty
    rw [(S.child f.birthType i).frame.toAffineIsometry.image_intrinsicInterior]
    exact f₀.val.flat.relint_nonempty.image _
  obtain ⟨x, hx⟩ := hne
  obtain ⟨j, ⟨hji, f₁, heq, -⟩, -⟩ := (internal_facet_pairing R 0 i f₀ ⟨x, hx, hint' hx⟩).2
  obtain ⟨a, ⟨q, hq, hqa⟩, hap⟩ := hp
  have hpoint : (S.σ ^ k) p = N.frame ((S.σ ^ n) q) := by
    rw [← hap, ← hqa, birth_ascent_routing_step3_birth_frame f k hf.le]
    change (f.birthNode k).frame ((S.σ ^ (k - f.depth)) (S.σ.symm q)) = _
    rw [hn, pow_succ]
    simp [N]
  have hq₀ : q ∈ (R.child 0 i).cell 0 f₀.val := hcell.symm ▸ hq
  have hq₁ : q ∈ (R.child 0 j).cell 0 f₁.val := heq.symm ▸ hq₀
  have hqi := birth_ascent_routing_step3_cell_subset (R.child 0 i) 0 f₀.val (Finset.mem_filter.mp f₀.property).1 hq₀
  have hqj := birth_ascent_routing_step3_cell_subset (R.child 0 j) 0 f₁.val (Finset.mem_filter.mp f₁.property).1 hq₁
  have hlift (l : S.I f.birthType) (hql : q ∈ (R.child 0 l).carrier 0) :
      (S.σ ^ k) p ∈ (N.child n l).carrier n := by
    rw [birth_ascent_routing_step2_child_support_zero] at hql
    obtain ⟨y, hy, hyq⟩ := hql
    refine ⟨(S.σ ^ n) y, ⟨y, hy, rfl⟩, ?_⟩
    change N.frame (S.placeChild n l ((S.σ ^ n) y)) = (S.σ ^ k) p
    rw [birth_ascent_routing_step2_place_scaled, hyq, hpoint]
  exact ⟨n, N, hn, hN, i, j, hji.symm, hlift i hqi, hlift j hqj⟩

/-- Step 3 of the V4 proof of `birth_ascent_routing` (V4 1.25): "`f` is shared
by two children of `P_b` ... which both contain `p`, hence contain `A`-owned
native tiles through `p`, so their least common ancestor `P_b` is a descendant
of `P₀`". This concerns only ancestry, without selecting an ascent. -/
private theorem birth_ascent_routing_step3_birth_below_top {A : S.ι} (k : ℕ)
    (p : E d) (b : ℕ) (P : FramedNode S) (hP : birth_ascent_routing_step1_top_birth A k p b P)
    (f : PrimitiveFacet S A) (hf : f.depth < k) (hp : p ∈ f.carrier) :
    (f.birthNode k).IsDescendant (k - f.depth) P b := by
  obtain ⟨n, N, hn, hN, i, j, hij, hpi, hpj⟩ := birth_ascent_routing_step3_primitive_two_children k f hf p hp
  have hstd : S.IsStandardNode A k (n + 1) N := by
    rw [hN, ← hn]
    exact ⟨f.depth, by omega, f.word, rfl⟩
  have hstdi := birth_ascent_routing_step3_standard_desc A k n (n + 1) (N.child n i) N hstd (birth_ascent_routing_step2_child_desc N n i)
  have hstdj := birth_ascent_routing_step3_standard_desc A k n (n + 1) (N.child n j) N hstd (birth_ascent_routing_step2_child_desc N n j)
  obtain ⟨L, hLi, hpL⟩ := birth_ascent_routing_step3_leaf_through (N.child n i) n _ hpi
  obtain ⟨M, hMj, hpM⟩ := birth_ascent_routing_step3_leaf_through (N.child n j) n _ hpj
  have hcover (L : FramedNode S) (hL : S.IsStandardNode A k 0 L)
      (hpL : (S.σ ^ k) p ∈ L.carrier 0) : L.IsDescendant 0 P b := by
    obtain ⟨r, hr, w, rfl⟩ := hL
    have hrk : r = k := by omega
    subst r
    exact hP.2.1 w hpL
  have hLP := hcover L (birth_ascent_routing_step3_standard_desc A k 0 n L (N.child n i) hstdi hLi) hpL
  have hMP := hcover M (birth_ascent_routing_step3_standard_desc A k 0 n M (N.child n j) hstdj hMj) hpM
  have hLN := birth_ascent_routing_step3_desc_trans L (N.child n i) N 0 n (n + 1) hLi (birth_ascent_routing_step2_child_desc N n i)
  have hle : n + 1 ≤ b := by
    by_contra hnb
    have hbn : b ≤ n := by omega
    have hnk : n ≤ k := by obtain ⟨r, hr, _⟩ := hstd; omega
    obtain ⟨Q, hQ, hPQ⟩ := birth_ascent_routing_step3_standard_raise A k b n P hP.1 hbn hnk
    have hiQ := birth_ascent_routing_step3_common_desc_eq A k n 0 (N.child n i) Q L hstdi hQ hLi
      (birth_ascent_routing_step3_desc_trans L P Q 0 b n hLP hPQ)
    have hjQ := birth_ascent_routing_step3_common_desc_eq A k n 0 (N.child n j) Q M hstdj hQ hMj
      (birth_ascent_routing_step3_desc_trans M P Q 0 b n hMP hPQ)
    exact hij (birth_ascent_routing_step3_child_injective N n (hiQ.trans hjQ.symm))
  rw [hn, ← hN]
  exact birth_ascent_routing_step3_common_desc_compare A k (n + 1) b 0 N P L hstd hP.1 hLN hLP hle

/-- Step 4 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"choose a point `y ∈ int P_b` near `p`". The full prototype frame preserves
closedness and regular closedness, so every point of a node is approached by
its interior points. -/
private theorem birth_ascent_routing_step4_regular_closed
    (N : FramedNode S) (n : ℕ) :
    IsClosed (N.carrier n) ∧ IsRegularClosed (N.carrier n) := by
  let H := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  have hc : N.carrier n = H '' (S.proto N.ty).carrier := by
    simp [H, FramedNode.prototypeFrame, FramedNode.carrier,
      SubstSystem.supertile, placedSet, Set.image_image]
  rw [hc]
  refine ⟨H.isClosedMap _ (S.proto N.ty).compact.isClosed, ?_⟩
  change closure (interior (H '' (S.proto N.ty).carrier)) = _
  rw [← H.image_interior, ← H.image_closure, (S.proto N.ty).regularClosed]

/-- Step 4 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"an `A`-owned native tile not in `P_b` (exists by minimality of `P₀`)".
Raise such a native tile to the height of `P_b`; its ancestor is a different
standard node through the point and is still below `P₀`. -/
private theorem birth_ascent_routing_step4_other_node
    {A : S.ι} (k : ℕ) (p : E d) (b : ℕ) (P : FramedNode S)
    (hP : birth_ascent_routing_step1_top_birth A k p b P) (n : ℕ) (N : FramedNode S)
    (hN : S.IsStandardNode A k n N) (hlt : n < b) :
    ∃ M : FramedNode S, S.IsStandardNode A k n M ∧
      M.IsDescendant n P b ∧ M ≠ N ∧ (S.σ ^ k) p ∈ M.carrier n := by
  classical
  have hex : ∃ w : S.RoleWord A k,
      (S.σ ^ k) p ∈ (S.nativeTile A k w).carrier 0 ∧
        ¬ (S.nativeTile A k w).IsDescendant 0 N n := by
    by_contra h
    have hcover : ∀ w : S.RoleWord A k,
        (S.σ ^ k) p ∈ (S.nativeTile A k w).carrier 0 →
          (S.nativeTile A k w).IsDescendant 0 N n := by
      intro w hw
      by_contra hn
      exact h ⟨w, hw, hn⟩
    exact (not_le_of_gt hlt) (hP.2.2 n N hN hcover)
  obtain ⟨w, hpw, hwN⟩ := hex
  have hwstd : S.IsStandardNode A k 0 (S.nativeTile A k w) :=
    ⟨k, by omega, w, rfl⟩
  have hnk : n ≤ k := by obtain ⟨j, hj, _⟩ := hN; omega
  obtain ⟨M, hM, hwM⟩ := birth_ascent_routing_step3_standard_raise A k 0 n
    (S.nativeTile A k w) hwstd (Nat.zero_le n) hnk
  refine ⟨M, hM, ?_, ?_, ?_⟩
  · exact birth_ascent_routing_step3_common_desc_compare A k n b 0 M P
      (S.nativeTile A k w) hM hP.1 hwM (hP.2.1 w hpw) hlt.le
  · intro heq
    exact hwN (heq ▸ hwM)
  · exact birth_ascent_routing_step3_desc_subset _ M 0 n hwM hpw

/-- Step 4 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"near a boundary point the polyhedral boundary separates a small ball into
two sides and `int P₀` is one of them". At a facet interior, the half-ball
description makes every sufficiently small intersection convex. -/
private theorem birth_ascent_routing_step4_facet_neighborhood
    (D : PolyManifoldDomain d) (C : CellComplex D)
    (e : Cell d) (he : e ∈ C.facets) (p : E d) (hp : p ∈ relint e.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      IsPreconnected (interior D.carrier ∩ Metric.ball p r) := by
  obtain ⟨ε, hε, v, _, _, _, hhalf⟩ := facet_halfball D C e he p hp
  refine ⟨ε, hε, ?_⟩
  intro r _ hr
  have hsub := Metric.ball_subset_ball hr.le (x := p)
  have hlocal : D.carrier ∩ Metric.ball p r =
      {x | 0 ≤ inner ℝ v (x - p)} ∩ Metric.ball p r := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ D.carrier ∩ Metric.ball p ε := ⟨hx.1, hsub hx.2⟩
      rw [hhalf] at hx'
      exact ⟨hx'.1, hx.2⟩
    · intro hx
      have hx' : x ∈ {x | 0 ≤ inner ℝ v (x - p)} ∩ Metric.ball p ε :=
        ⟨hx.1, hsub hx.2⟩
      rw [← hhalf] at hx'
      exact ⟨hx'.1, hx.2⟩
  have hhalfconv : Convex ℝ {x | 0 ≤ inner ℝ v (x - p)} := by
    simpa only [inner_sub_right, sub_nonneg] using
      convex_halfSpace_ge (innerSL ℝ v).toLinearMap.isLinear (inner ℝ v p)
  have hconv : Convex ℝ (D.carrier ∩ Metric.ball p r) := by
    rw [hlocal]
    exact hhalfconv.inter (convex_ball p r)
  simpa only [interior_inter, Metric.isOpen_ball.interior_eq] using
    hconv.interior.isPreconnected

/-- Step 1 of the V4 proof of `birth_ascent_routing_step4_lower_cell_neighborhood`
(V4 1.25, using (H1) of V4 §1.0): "the polyhedral boundary separates a small
ball into two sides" — at a codimension-two cell. Ridge degree: since
`∂P₀` is a topological `(d-1)`-manifold, a listed boundary cell `g` of
dimension `d-2` lies in exactly two listed facets (near `relint g` the frontier
is a book of half-hyperplanes bounded by `aff g`; a book with `k ≠ 2` pages is
not a `(d-1)`-manifold, `k ≤ 1` being excluded already by regular closedness).
This is the cell-complex analogue of
`principal_component_step1_hull_geometry_step10_jordan_brouwer_step10_ridge_degree`. -/
private lemma birth_ascent_routing_step4_lower_cell_neighborhood_step1_ridge_two_facets
    (D : PolyManifoldDomain d) (C : CellComplex D) (g : Cell d) (hg : g ∈ C.cells)
    (hgd : g.dim + 2 = d) :
    {f : Cell d | f ∈ C.cells ∧ f.dim = d - 1 ∧ g.carrier ⊆ f.carrier}.ncard = 2 := by
  sorry

/-- Step 2 of the V4 proof of `birth_ascent_routing_step4_lower_cell_neighborhood`
(V4 1.25): "the polyhedral boundary separates a small ball into two sides and
`int P₀` is one of them" — at a relative interior point `y` of a codimension-two
cell `g` lying in exactly two facets. Elementary geometry, no manifold
hypothesis: near `y` the only cells are `g` and its two facets, each a
half-hyperplane bounded by `aff g` (relative interiors are disjoint and
`closure (relint f) = f`); the two distinct half-hyperplanes cut a small ball
into two open wedges, each inside `int P₀` or inside the exterior; not both
inside (`y` is a frontier point) and not both outside (`P₀` is regular closed).
So `int P₀ ∩ B(y, δ)` is one wedge, which is path connected. -/
private lemma birth_ascent_routing_step4_lower_cell_neighborhood_step2_ridge_germ
    (D : PolyManifoldDomain d) (C : CellComplex D) (g : Cell d) (hg : g ∈ C.cells)
    (hgd : g.dim + 2 = d)
    (htwo : {f : Cell d | f ∈ C.cells ∧ f.dim = d - 1 ∧ g.carrier ⊆ f.carrier}.ncard = 2)
    (y : E d) (hy : y ∈ relint g.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      IsPreconnected (interior D.carrier ∩ Metric.ball y δ) := by
  sorry

/-- Step 3 of the V4 proof of `birth_ascent_routing_step4_lower_cell_neighborhood`
(V4 1.25): "join them by a path ... in general position (avoiding the
`(d-2)`-skeleton ... and crossing facets transversally)". Every component `Q`
of `int P₀ ∩ B(p,r)` has in its closure a frontier point of the ball that lies
on no listed cell of dimension `≤ d-3`, i.e. a point of the relative interior
of a facet or of a codimension-two cell. Proof: `Q ≠ B(p,r)` as `p ∉ int P₀`,
the points of `closure Q ∩ B(p,r) \ Q` are frontier points of `P₀`; if all of
them lay on the codimension `≥ 3` skeleton `Z`, then `Q` would be clopen in the
connected set `B(p,r) \ Z` (a finite union of flat cells of codimension `≥ 2`
does not separate a ball), so `B(p,r) ⊆ closure Q ⊆ P₀`, contradicting
`p ∈ ∂P₀`. No manifold hypothesis is used. Cell-complex analogue of
`principal_component_step1_hull_geometry_step10_jordan_brouwer_step17_reaches_facet`. -/
private lemma birth_ascent_routing_step4_lower_cell_neighborhood_step3_reach_wall
    (D : PolyManifoldDomain d) (C : CellComplex D) (p : E d)
    (hp : p ∈ frontier D.carrier) (r : ℝ) (hr : 0 < r) (x : E d)
    (hx : x ∈ interior D.carrier ∩ Metric.ball p r) :
    ∃ y ∈ frontier D.carrier ∩ Metric.ball p r,
      (∀ c ∈ C.cells, y ∈ c.carrier → d ≤ c.dim + 2) ∧
      y ∈ closure (connectedComponentIn (interior D.carrier ∩ Metric.ball p r) x) := by
  sorry

/-- Step 4 of the V4 proof of `birth_ascent_routing_step4_lower_cell_neighborhood`
(V4 1.25, using (H1) of V4 §1.0): "the polyhedral boundary ... a small ball".
Strong connectivity of the boundary near `p`: for small `r`, the part of
`∂P₀ ∩ B(p,r)` off the listed cells of dimension `≤ d-3` (the union of the
relative interiors of the facets and codimension-two cells through `p`) is
connected. This is a statement about the frontier only (no interior side):
`∂P₀ ∩ B(p,r)` is a cone over the link of `p`, which is connected because
`∂P₀` is a `(d-1)`-manifold, and a codimension-two polyhedral subset does not
disconnect a polyhedral manifold. Local analogue of
`principal_component_step1_hull_geometry_step10_jordan_brouwer_step11_facet_chains`. -/
private lemma birth_ascent_routing_step4_lower_cell_neighborhood_step4_wall_connected
    (D : PolyManifoldDomain d) (C : CellComplex D) (p : E d)
    (hp : p ∈ frontier D.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      IsPreconnected {y | y ∈ frontier D.carrier ∩ Metric.ball p r ∧
        ∀ c ∈ C.cells, y ∈ c.carrier → d ≤ c.dim + 2} := by
  sorry

/-- Step 5 of the V4 proof of `birth_ascent_routing_step4_lower_cell_neighborhood`
(V4 1.25): "near a boundary point the polyhedral boundary separates a small ball
into two sides and `int P₀` is one of them", at the wall points (facet or
codimension-two relative interiors): the facet half-ball case
(`birth_ascent_routing_step4_facet_neighborhood`) and Steps 1–2. -/
private lemma birth_ascent_routing_step4_lower_cell_neighborhood_step5_wall_germ
    (D : PolyManifoldDomain d) (C : CellComplex D) (y : E d)
    (hy : y ∈ frontier D.carrier) (hyc : ∀ c ∈ C.cells, y ∈ c.carrier → d ≤ c.dim + 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      IsPreconnected (interior D.carrier ∩ Metric.ball y δ) := by
  rw [← C.cover] at hy
  obtain ⟨c, hc, hyc'⟩ := Set.mem_iUnion₂.mp hy
  have h1 := hyc c hc (intrinsicInterior_subset hyc')
  have h2 := C.dim_lt c hc
  by_cases hcd : c.dim = d - 1
  · exact birth_ascent_routing_step4_facet_neighborhood D C c
      (Finset.mem_filter.mpr ⟨hc, hcd⟩) y hyc'
  · have hcd' : c.dim + 2 = d := by omega
    exact birth_ascent_routing_step4_lower_cell_neighborhood_step2_ridge_germ D C c hc hcd'
      (birth_ascent_routing_step4_lower_cell_neighborhood_step1_ridge_two_facets D C c hc hcd')
      y hyc'

/-- Step 4 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"near a boundary point the polyhedral boundary separates a small ball into
two sides and `int P₀` is one of them". This is only the remaining local
connectivity assertion at a lower-dimensional listed boundary cell of a
single polyhedral manifold domain; no subdivision or routing is involved. -/
private theorem birth_ascent_routing_step4_lower_cell_neighborhood
    (D : PolyManifoldDomain d) (C : CellComplex D)
    (e : Cell d) (he : e ∈ C.cells) (hdim : e.dim + 1 < d)
    (p : E d) (hp : p ∈ relint e.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      IsPreconnected (interior D.carrier ∩ Metric.ball p r) := by
  have hpf : p ∈ frontier D.carrier := by
    rw [← C.cover]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hp⟩
  obtain ⟨ε, hε, hwall⟩ :=
    birth_ascent_routing_step4_lower_cell_neighborhood_step4_wall_connected D C p hpf
  refine ⟨ε, hε, fun r hr hrε => ?_⟩
  set I := interior D.carrier ∩ Metric.ball p r with hIdef
  set Y := {y | y ∈ frontier D.carrier ∩ Metric.ball p r ∧
    ∀ c ∈ C.cells, y ∈ c.carrier → d ≤ c.dim + 2} with hYdef
  have hYconn : IsPreconnected Y := hwall r hr hrε
  have hIopen : IsOpen I := isOpen_interior.inter Metric.isOpen_ball
  -- a preconnected interior germ at every wall point, inside the ball
  have hgerm : ∀ y ∈ Y, ∃ δ : ℝ, 0 < δ ∧ Metric.ball y δ ⊆ Metric.ball p r ∧
      IsPreconnected (interior D.carrier ∩ Metric.ball y δ) := by
    rintro y ⟨⟨hyf, hyb⟩, hyc⟩
    obtain ⟨η, hη, hconn⟩ :=
      birth_ascent_routing_step4_lower_cell_neighborhood_step5_wall_germ D C y hyf hyc
    have hyr : 0 < r - dist y p := by
      rw [Metric.mem_ball] at hyb
      linarith
    have hpos : 0 < min (η / 2) (r - dist y p) := lt_min (by linarith) hyr
    refine ⟨min (η / 2) (r - dist y p), hpos, ?_, hconn _ hpos ?_⟩
    · exact Metric.ball_subset_ball' (by linarith [min_le_right (η / 2) (r - dist y p)])
    · linarith [min_le_left (η / 2) (r - dist y p)]
  choose! δ hδpos hδsub hδconn using hgerm
  -- wall points are adherent to the interior
  have hDcl : ∀ y ∈ Y, ∀ s : Set (E d), IsOpen s → y ∈ s →
      (s ∩ interior D.carrier).Nonempty := by
    rintro y ⟨⟨hyf, -⟩, -⟩ s hs hys
    have hyD : y ∈ closure (interior D.carrier) := by
      rw [D.regularClosed]
      exact (frontier_subset_iff_isClosed.mpr D.compact.isClosed) hyf
    exact mem_closure_iff.mp hyD s hs hys
  -- a germ meeting a component lies in it
  have hsub : ∀ x₀ : E d, ∀ y ∈ Y, ∀ z ∈ Metric.ball y (δ y),
      z ∈ connectedComponentIn I x₀ →
        interior D.carrier ∩ Metric.ball y (δ y) ⊆ connectedComponentIn I x₀ := by
    intro x₀ y hy z hzb hzQ
    have hzI : z ∈ I := connectedComponentIn_subset _ _ hzQ
    have hSI : interior D.carrier ∩ Metric.ball y (δ y) ⊆ I :=
      fun w hw => ⟨hw.1, hδsub y hy hw.2⟩
    have h := (hδconn y hy).subset_connectedComponentIn ⟨hzI.1, hzb⟩ hSI
    rwa [← connectedComponentIn_eq hzQ] at h
  -- a component adherent to a wall point contains its germ
  have hgermsub : ∀ x₀ : E d, ∀ y ∈ Y, y ∈ closure (connectedComponentIn I x₀) →
      interior D.carrier ∩ Metric.ball y (δ y) ⊆ connectedComponentIn I x₀ := by
    intro x₀ y hy hcl
    obtain ⟨z, hzb, hzQ⟩ := mem_closure_iff.mp hcl (Metric.ball y (δ y)) Metric.isOpen_ball
      (Metric.mem_ball_self (hδpos y hy))
    exact hsub x₀ y hy z hzb hzQ
  -- adherence propagates to nearby wall points
  have hnear : ∀ x₀ : E d, ∀ y ∈ Y, y ∈ closure (connectedComponentIn I x₀) →
      ∀ w ∈ Y, w ∈ Metric.ball y (δ y) → w ∈ closure (connectedComponentIn I x₀) := by
    intro x₀ y hy hcl w hw hwb
    have hS := hgermsub x₀ y hy hcl
    refine mem_closure_iff.mpr fun s hs hws => ?_
    obtain ⟨z, ⟨hzs, hzb⟩, hzD⟩ :=
      hDcl w hw (s ∩ Metric.ball y (δ y)) (hs.inter Metric.isOpen_ball) ⟨hws, hwb⟩
    exact ⟨z, hzs, hS ⟨hzD, hzb⟩⟩
  have hback : ∀ x₀ : E d, ∀ b ∈ Y, ∀ w ∈ Y, w ∈ Metric.ball b (δ b) →
      w ∈ closure (connectedComponentIn I x₀) → b ∈ closure (connectedComponentIn I x₀) := by
    intro x₀ b hb w hw hwb hcl
    obtain ⟨z, hzb, hzQ⟩ := mem_closure_iff.mp hcl (Metric.ball b (δ b)) Metric.isOpen_ball hwb
    have hS := hsub x₀ b hb z hzb hzQ
    refine mem_closure_iff.mpr fun s hs hbs => ?_
    obtain ⟨u, ⟨hus, hub⟩, huD⟩ :=
      hDcl b hb (s ∩ Metric.ball b (δ b)) (hs.inter Metric.isOpen_ball)
        ⟨hbs, Metric.mem_ball_self (hδpos b hb)⟩
    exact ⟨u, hus, hS ⟨huD, hub⟩⟩
  -- every component is adherent to every wall point
  have hall : ∀ x₀ ∈ I, ∀ y ∈ Y, y ∈ closure (connectedComponentIn I x₀) := by
    intro x₀ hx₀
    obtain ⟨y₀, hy₀, hy₀c, hy₀cl⟩ :=
      birth_ascent_routing_step4_lower_cell_neighborhood_step3_reach_wall D C p hpf r hr x₀ hx₀
    have hy₀Y : y₀ ∈ Y := ⟨hy₀, hy₀c⟩
    by_contra hne
    push_neg at hne
    obtain ⟨y₁, hy₁Y, hy₁⟩ := hne
    let u := ⋃ y ∈ {y | y ∈ Y ∧ y ∈ closure (connectedComponentIn I x₀)},
      Metric.ball y (δ y)
    let v := ⋃ y ∈ {y | y ∈ Y ∧ y ∉ closure (connectedComponentIn I x₀)},
      Metric.ball y (δ y)
    have hu : IsOpen u := isOpen_biUnion fun _ _ => Metric.isOpen_ball
    have hv : IsOpen v := isOpen_biUnion fun _ _ => Metric.isOpen_ball
    have hcov : Y ⊆ u ∪ v := by
      intro y hy
      by_cases hyc : y ∈ closure (connectedComponentIn I x₀)
      · exact Or.inl (Set.mem_biUnion ⟨hy, hyc⟩ (Metric.mem_ball_self (hδpos y hy)))
      · exact Or.inr (Set.mem_biUnion ⟨hy, hyc⟩ (Metric.mem_ball_self (hδpos y hy)))
    obtain ⟨w, hwY, hwu, hwv⟩ := hYconn u v hu hv hcov
      ⟨y₀, hy₀Y, Set.mem_biUnion ⟨hy₀Y, hy₀cl⟩ (Metric.mem_ball_self (hδpos y₀ hy₀Y))⟩
      ⟨y₁, hy₁Y, Set.mem_biUnion ⟨hy₁Y, hy₁⟩ (Metric.mem_ball_self (hδpos y₁ hy₁Y))⟩
    obtain ⟨a, ⟨haY, hacl⟩, hwa⟩ := Set.mem_iUnion₂.mp hwu
    obtain ⟨b, ⟨hbY, hbcl⟩, hwb⟩ := Set.mem_iUnion₂.mp hwv
    exact hbcl (hback x₀ b hbY w hwY hwb (hnear x₀ a haY hacl w hwY hwa))
  refine isPreconnected_of_forall_pair fun x hx x' hx' => ?_
  refine ⟨connectedComponentIn I x, connectedComponentIn_subset _ _,
    mem_connectedComponentIn hx, ?_, isPreconnected_connectedComponentIn⟩
  obtain ⟨y', hy', hy'c, hy'cl⟩ :=
    birth_ascent_routing_step4_lower_cell_neighborhood_step3_reach_wall D C p hpf r hr x' hx'
  have hy'Y : y' ∈ Y := ⟨hy', hy'c⟩
  have hS := hgermsub x y' hy'Y (hall x hx y' hy'Y)
  have hS' := hgermsub x' y' hy'Y hy'cl
  obtain ⟨z, hzb, hzD⟩ := hDcl y' hy'Y (Metric.ball y' (δ y')) Metric.isOpen_ball
    (Metric.mem_ball_self (hδpos y' hy'Y))
  have hzQ := hS ⟨hzD, hzb⟩
  have hzQ' := hS' ⟨hzD, hzb⟩
  rw [connectedComponentIn_eq hzQ, ← connectedComponentIn_eq hzQ']
  exact mem_connectedComponentIn hx'

/-- Step 4 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"`int P₀ ∩ B(p,ρ)` is connected for small `ρ`". The relative-interior
partition of the frontier separates the facet and lower-cell cases. -/
private theorem birth_ascent_routing_step4_boundary_neighborhood
    (D : PolyManifoldDomain d) (C : CellComplex D)
    (p : E d) (hp : p ∈ frontier D.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      IsPreconnected (interior D.carrier ∩ Metric.ball p r) := by
  rw [← C.cover] at hp
  obtain ⟨e, he, hpe⟩ := Set.mem_iUnion₂.mp hp
  by_cases hdim : e.dim = d - 1
  · exact birth_ascent_routing_step4_facet_neighborhood D C e
      (Finset.mem_filter.mpr ⟨he, hdim⟩) p hpe
  · have hlt := C.dim_lt e he
    exact birth_ascent_routing_step4_lower_cell_neighborhood D C e he (by omega) p hpe

/-- Step 4 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"`int P₀ ∩ B(p,ρ)` is connected for small `ρ` ... near an interior point
it is a ball". Transport the small connected interior neighborhood through
the full affine frame; it can be chosen inside any prescribed open neighborhood. -/
private theorem birth_ascent_routing_step4_interior_neighborhood
    (N : FramedNode S) (n : ℕ) (p : E d) (hp : p ∈ N.carrier n)
    (U : Set (E d)) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ V : Set (E d), IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      IsPreconnected (interior (N.carrier n) ∩ V) := by
  let H := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  have hc : N.carrier n = H '' (S.proto N.ty).carrier := by
    simp [H, FramedNode.prototypeFrame, FramedNode.carrier,
      SubstSystem.supertile, placedSet, Set.image_image]
  let q := H.symm p
  have hq : q ∈ (S.proto N.ty).carrier := by
    rw [hc] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    simpa [q] using hz
  have hqU : q ∈ H ⁻¹' U := by simpa [q] using hpU
  obtain ⟨r, hr, hrU, hrconn⟩ : ∃ r : ℝ, 0 < r ∧
      Metric.ball q r ⊆ H ⁻¹' U ∧
        IsPreconnected (interior (S.proto N.ty).carrier ∩ Metric.ball q r) := by
    by_cases hi : q ∈ interior (S.proto N.ty).carrier
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
        (isOpen_interior.inter (hU.preimage H.continuous)) q ⟨hi, hqU⟩
      refine ⟨r, hr, fun x hx => (hball hx).2, ?_⟩
      rw [inter_eq_right.mpr (fun x hx => (hball hx).1)]
      exact (convex_ball q r).isPreconnected
    · have hf : q ∈ frontier (S.proto N.ty).carrier :=
        ⟨(S.proto N.ty).compact.isClosed.closure_eq.symm ▸ hq, hi⟩
      obtain ⟨ε, hε, hconn⟩ :=
        birth_ascent_routing_step4_boundary_neighborhood
          (S.proto N.ty) (S.cx N.ty) q hf
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hU.preimage H.continuous) q hqU
      let r := min ε δ / 2
      have hr : 0 < r := by dsimp [r]; positivity
      have hrε : r < ε := by dsimp [r]; linarith [min_le_left ε δ]
      have hrδ : r ≤ δ := by dsimp [r]; linarith [min_le_right ε δ]
      exact ⟨r, hr, (Metric.ball_subset_ball hrδ).trans hball, hconn r hr hrε⟩
  refine ⟨H '' Metric.ball q r, H.isOpenMap _ Metric.isOpen_ball,
    ⟨q, Metric.mem_ball_self hr, H.apply_symm_apply p⟩, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hrU hx
  · have heq : interior (N.carrier n) ∩ H '' Metric.ball q r =
        H '' (interior (S.proto N.ty).carrier ∩ Metric.ball q r) := by
      rw [hc, ← H.image_interior, Set.image_inter H.injective]
    rw [heq]
    exact hrconn.image H H.continuous.continuousOn

/-- Step 4 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"`ρ` smaller than the distance from `p` to all cells ... not containing `p`
(finitely many)". Remove the finite closed union of facets missing the point. -/
private theorem birth_ascent_routing_step4_avoid_facets
    (N : FramedNode S) (n : ℕ) (p : E d) :
    ∃ U : Set (E d), IsOpen U ∧ p ∈ U ∧
      ∀ (e : FacetName S N.ty) (x : E d), x ∈ U → x ∈ N.cell n e.val →
        p ∈ N.cell n e.val := by
  classical
  let bad := (S.cx N.ty).facets.filter (fun e => p ∉ N.cell n e)
  let U := (⋃ e ∈ bad, N.cell n e)ᶜ
  have hc (e : Cell d) : IsClosed (N.cell n e) :=
    (e.flat.compact.image (N.prototypeFrame n).continuous_of_finiteDimensional).isClosed
  refine ⟨U, (isClosed_biUnion_finset (fun e _ => hc e)).isOpen_compl, ?_, ?_⟩
  · intro h
    obtain ⟨e, he, hpe⟩ := Set.mem_iUnion₂.mp h
    exact (Finset.mem_filter.mp he).2 hpe
  · intro e x hx hxe
    by_contra hpe
    exact hx (Set.mem_iUnion₂.mpr ⟨e.val,
      Finset.mem_filter.mpr ⟨e.property, hpe⟩, hxe⟩)

/-- Step 4 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"At the first exit from `P_b`". A connected set meeting the interior and
the complement of a closed set meets its frontier. -/
private theorem birth_ascent_routing_step4_crossing
    {K V : Set (E d)} (hK : IsClosed K) (hV : IsPreconnected V)
    (hin : (V ∩ interior K).Nonempty) (hout : (V ∩ Kᶜ).Nonempty) :
    (V ∩ frontier K).Nonempty := by
  by_contra h
  have hsplit : V ⊆ interior K ∪ Kᶜ := by
    intro x hx
    by_cases hxK : x ∈ K
    · left
      by_contra hi
      exact h ⟨x, hx, hK.closure_eq.symm ▸ hxK, hi⟩
    · exact Or.inr hxK
  obtain ⟨x, _, hxi, hxo⟩ := hV (interior K) Kᶜ
    isOpen_interior hK.isOpen_compl hsplit hin hout
  exact hxo (interior_subset hxi)

/-- Step 4 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"the path crosses a facet `e`". The closed facets of the finite boundary
complex cover every frontier point, also after applying the node's full frame. -/
private theorem birth_ascent_routing_step4_frontier_facets
    (N : FramedNode S) (n : ℕ) {x : E d} (hx : x ∈ frontier (N.carrier n)) :
    ∃ e : FacetName S N.ty, x ∈ N.cell n e.val := by
  let H := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  have hc : N.carrier n = H '' (S.proto N.ty).carrier := by
    simp [H, FramedNode.prototypeFrame, FramedNode.carrier,
      SubstSystem.supertile, placedSet, Set.image_image]
  rw [hc, ← H.image_frontier] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨e, hye⟩ := Set.mem_iUnion.mp
    (principal_component_step1_hull_geometry_step11_facets_cover
      (S.proto N.ty) (S.cx N.ty) hy)
  exact ⟨e, y, hye, rfl⟩

/-- Step 4 of the V4 proof of `birth_ascent_routing` (V4 1.25): "At the first
exit from `P_b` the path crosses a facet `e` ... lying in `int P₀`"; choosing
the ball smaller than the distances to cells not containing `p` ensures
"the crossed facet `e` contains `p`". All sets in this conclusion are compared
in the standard height-`k` coordinates. -/
private theorem birth_ascent_routing_step4_exit_facet {A : S.ι} (k : ℕ)
    (p : E d) (b : ℕ) (P : FramedNode S) (hP : birth_ascent_routing_step1_top_birth A k p b P)
    (f : PrimitiveFacet S A) (hf : f.depth < k) (hp : p ∈ f.carrier)
    (hancestor : (f.birthNode k).IsDescendant (k - f.depth) P b)
    (hstrict : k - f.depth < b) :
    ∃ e : FacetName S f.birthType, p ∈ f.birthCell e.val ∧
      relint ((S.σ ^ k) '' f.birthCell e.val) ⊆ interior (P.carrier b) := by
  let n := k - f.depth
  let x := (S.σ ^ k) p
  let N : FramedNode S := ⟨f.birthType, (f.birthNode k).frame⟩
  have hN : N = f.birthNode k := by
    apply FramedNode.ext
    · exact (birth_ascent_routing_step2_descendant_type A n f.depth f.word).symm
    · rfl
  have hstd : S.IsStandardNode A k n N := by
    rw [hN]
    exact ⟨f.depth, by dsimp [n]; omega, f.word, rfl⟩
  have hNP : N.IsDescendant n P b := hN.symm ▸ hancestor
  have hxN : x ∈ N.carrier n := by
    obtain ⟨r, R, hr, hR, i, j, hij, hpi, hpj⟩ :=
      birth_ascent_routing_step3_primitive_two_children k f hf p hp
    have hmem := birth_ascent_routing_step3_child_subset R r i hpi
    rwa [hR, ← hr, ← hN] at hmem
  have hNsub := birth_ascent_routing_step3_desc_subset N P n b hNP
  obtain ⟨M, hM, hMP, hne, hxM⟩ :=
    birth_ascent_routing_step4_other_node k p b P hP n N hstd hstrict
  have hMsub := birth_ascent_routing_step3_desc_subset M P n b hMP
  obtain ⟨U, hU, hxU, hfacets⟩ :=
    birth_ascent_routing_step4_avoid_facets N n x
  obtain ⟨V, hV, hxV, hVU, hconn⟩ :=
    birth_ascent_routing_step4_interior_neighborhood
      P b x (hNsub hxN) U hU hxU
  obtain ⟨hNclosed, hNreg⟩ := birth_ascent_routing_step4_regular_closed N n
  obtain ⟨_, hMreg⟩ := birth_ascent_routing_step4_regular_closed M n
  have hxNi : x ∈ closure (interior (N.carrier n)) := hNreg.symm ▸ hxN
  have hxMi : x ∈ closure (interior (M.carrier n)) := hMreg.symm ▸ hxM
  obtain ⟨y, hyV, hyN⟩ := mem_closure_iff.mp hxNi V hV hxV
  obtain ⟨z, hzV, hzM⟩ := mem_closure_iff.mp hxMi V hV hxV
  have hdisj : Disjoint (N.carrier n) (interior (M.carrier n)) := by
    rw [← hNreg]
    exact (birth_ascent_routing_step3_standard_disjoint A k n N M hstd hM hne.symm).closure_left
      isOpen_interior
  have hzout : z ∉ N.carrier n := fun hzN => Set.disjoint_left.mp hdisj hzN hzM
  obtain ⟨q, ⟨hqP, hqV⟩, hqfront⟩ :=
    birth_ascent_routing_step4_crossing hNclosed hconn
      ⟨y, ⟨interior_mono hNsub hyN, hyV⟩, hyN⟩
      ⟨z, ⟨interior_mono hMsub hzM, hzV⟩, hzout⟩
  obtain ⟨e, hqe⟩ := birth_ascent_routing_step4_frontier_facets N n hqfront
  have hxe : x ∈ N.cell n e.val := hfacets e q (hVU hqV) hqe
  have hinternal : relint (N.cell n e.val) ⊆ interior (P.carrier b) := by
    rcases facet_dichotomy P N b n hNP e with hboundary | hi
    · obtain ⟨F, hF, _⟩ := hboundary
      exact False.elim ((birth_ascent_routing_step2_cell_front P b F.val
        (Finset.mem_filter.mp F.property).1 (hF hqe)).2 hqP)
    · exact hi
  have hcell : N.cell n e.val = (S.σ ^ k) '' f.birthCell e.val := by
    change N.prototypeFrame n '' e.val.carrier =
      (S.σ ^ k) '' (f.birthFrame '' e.val.carrier)
    rw [Set.image_image]
    apply Set.image_congr
    intro a _
    rw [hN]
    exact (birth_ascent_routing_step3_birth_frame f k hf.le a).symm
  refine ⟨e, ?_, ?_⟩
  · rw [hcell] at hxe
    exact (S.σ ^ k).injective.mem_set_image.mp hxe
  · rwa [← hcell]

/-- Step 5 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"`e` has a finite first provider `g` ... and `e ⊆ g`".
Relative interiors commute with the full affine frames, including anisotropic expansion. -/
private theorem birth_ascent_routing_step5_relint_image (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
    relint (e '' K) = e '' relint K := by
  let h := e.toHomeomorphOfFiniteDimensional
  have hspan : h '' (affineSpan ℝ K : Set (E d)) =
      (affineSpan ℝ (e '' K) : Set (E d)) := by
    exact congrArg (fun A : AffineSubspace ℝ (E d) => (A : Set (E d)))
      (AffineSubspace.map_span e.toAffineMap K)
  let f : (affineSpan ℝ K) ≃ₜ (affineSpan ℝ (e '' K)) :=
    (h.image _).trans (Homeomorph.setCongr hspan)
  have hf (x : affineSpan ℝ K) : (f x).val = e x.val := rfl
  have hp : (f ⁻¹' ((↑) ⁻¹' (e '' K) : Set (affineSpan ℝ (e '' K)))) =
      ((↑) ⁻¹' K : Set (affineSpan ℝ K)) := by
    ext x
    change e x.val ∈ e '' K ↔ x.val ∈ K
    exact e.injective.mem_set_image
  have hi := f.preimage_interior ((↑) ⁻¹' (e '' K) : Set (affineSpan ℝ (e '' K)))
  rw [hp] at hi
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hm : f.symm y ∈ interior ((↑) ⁻¹' K : Set (affineSpan ℝ K)) := by
      rw [← hi]
      simpa using hy
    refine ⟨(f.symm y).val, ⟨f.symm y, hm, rfl⟩, ?_⟩
    simpa only [f.apply_symm_apply] using (hf (f.symm y)).symm
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨f w, ?_, hf w⟩
    change w ∈ f ⁻¹' interior ((↑) ⁻¹' (e '' K) : Set (affineSpan ℝ (e '' K)))
    rwa [hi]

/-- Step 5 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"`e` has a finite first provider `g` ... and `e ⊆ g`".
Every placed facet has nonempty relative interior, so interior containment cannot be vacuous. -/
private theorem birth_ascent_routing_step5_cell_relint_nonempty (N : FramedNode S) (n : ℕ) (e : Cell d) :
    (relint (N.cell n e)).Nonempty := by
  rw [FramedNode.cell, birth_ascent_routing_step5_relint_image]
  exact e.flat.relint_nonempty.image _

/-- Step 5 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"`e` has a finite first provider `g` ... and `e ⊆ g`".
An internal child facet of a standard node gives a primitive facet with the exact birth address and normalized carrier. -/
private theorem birth_ascent_routing_step5_primitive_from_child (A : S.ι) (k n : ℕ) (Q : FramedNode S)
    (hQ : S.IsStandardNode A k (n + 1) Q) (i : S.I Q.ty)
    (e : FacetName S (Q.child n i).ty)
    (hint : relint ((Q.child n i).cell n e.val) ⊆ interior (Q.carrier (n + 1))) :
    ∃ g : PrimitiveFacet S A, k - g.depth = n + 1 ∧ g.birthNode k = Q ∧
      (S.σ ^ k) '' g.carrier = (Q.child n i).cell n e.val := by
  obtain ⟨j, hk, w, hQ⟩ := hQ
  have hty : (S.nativeTile A j w).ty = Q.ty :=
    (birth_ascent_routing_step2_descendant_type A (n + 1) j w).symm.trans (congrArg FramedNode.ty hQ.symm)
  let F := placedSet (S.child Q.ty i).frame e.val.carrier
  let T : E d ≃ᵃ[ℝ] E d := (S.σ ^ n).toAffineEquiv.trans Q.frame.toAffineEquiv
  have hcell : (Q.child n i).cell n e.val = T '' F := by
    simp only [FramedNode.cell, FramedNode.prototypeFrame, FramedNode.child,
      AffineEquiv.coe_trans, AffineIsometryEquiv.coe_toAffineEquiv,
      AffineIsometryEquiv.coe_trans, LinearEquiv.coe_toAffineEquiv,
      T, F, placedSet, Set.image_image]
    congr 1
    funext x
    exact congrArg Q.frame (birth_ascent_routing_step2_place_scaled n i x)
  have hcarrier : Q.carrier (n + 1) = T '' S.supertile 1 Q.ty := by
    simp [FramedNode.carrier, SubstSystem.supertile, placedSet, T,
      Set.image_image, pow_succ, LinearEquiv.mul_apply]
  have hlocal : relint F ⊆ interior (S.supertile 1 Q.ty) := by
    intro x hx
    have hh : T x ∈ interior (Q.carrier (n + 1)) := by
      apply hint
      rw [hcell, birth_ascent_routing_step5_relint_image]
      exact Set.mem_image_of_mem T hx
    rw [hcarrier] at hh
    let H := T.toHomeomorphOfFiniteDimensional
    change H x ∈ interior (H '' S.supertile 1 Q.ty) at hh
    rw [← H.image_interior] at hh
    exact H.injective.mem_set_image.mp hh
  have hreal : ∃ (i : S.I (S.nativeTile A j w).ty)
      (e : FacetName S (S.child (S.nativeTile A j w).ty i).ty),
      F = placedSet (S.child (S.nativeTile A j w).ty i).frame e.val.carrier ∧
        relint F ⊆ interior (S.supertile 1 (S.nativeTile A j w).ty) := by
    rw [hty]
    exact ⟨i, e, rfl, hlocal⟩
  let g : PrimitiveFacet S A := ⟨j, w, F, hreal⟩
  have hg : k - g.depth = n + 1 := by change k - j = n + 1; omega
  have hgj : g.depth < k := by change j < k; omega
  have hnode : g.birthNode k = Q := by
    change S.descendantNode A (k - j) j w = Q
    rw [show k - j = n + 1 by omega]
    exact hQ.symm
  refine ⟨g, hg, hnode, ?_⟩
  rw [hcell]
  change (S.σ ^ k) '' (g.birthFrame '' (S.σ.symm '' F)) = T '' F
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro x _
  change (S.σ ^ k) (g.birthFrame (S.σ.symm x)) = T x
  rw [birth_ascent_routing_step3_birth_frame g k hgj.le, hg, hnode]
  change Q.frame ((S.σ ^ (n + 1)) (S.σ.symm x)) = Q.frame ((S.σ ^ n) x)
  rw [pow_succ]
  simp

/-- Step 5 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"`e` has a finite first provider `g` ... and `e ⊆ g`".
A strict descendant has an immediate predecessor inside the given standard ancestor. -/
private theorem birth_ascent_routing_step5_parent_within (A : S.ι) (k h b : ℕ) (N P : FramedNode S)
    (hN : S.IsStandardNode A k h N) (hP : S.IsStandardNode A k b P)
    (hNP : N.IsDescendant h P b) (hlt : h < b) :
    ∃ Q : FramedNode S, S.IsStandardNode A k (h + 1) Q ∧ Q.IsDescendant (h + 1) P b ∧
      ∃ i : S.I Q.ty, N = Q.child h i := by
  have hbk : b ≤ k := by obtain ⟨j, hj, _⟩ := hP; omega
  obtain ⟨Q, hQ, hNQ⟩ := birth_ascent_routing_step3_standard_raise A k h (h + 1) N hN (by omega) (by omega)
  have hQP := birth_ascent_routing_step3_common_desc_compare A k (h + 1) b h Q P N hQ hP hNQ hNP (by omega)
  obtain ⟨r, hr, w, hw⟩ := hNQ
  have hrone : r = 1 := by omega
  subst r
  refine ⟨Q, hQ, hQP, w.1, ?_⟩
  simpa [SubstSystem.descendantNode, FramedNode.child, FramedNode.move] using hw

/-- Step 5 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"`e` has a finite first provider `g` ... and `e ⊆ g`".
Ascend through boundary facets until the first internal facet. Facet dichotomy and the finite ancestor distance ensure termination. -/
private theorem birth_ascent_routing_step5_finite_provider (A : S.ι) (k b : ℕ) (P : FramedNode S)
    (hP : S.IsStandardNode A k b P) (h : ℕ) (N : FramedNode S)
    (hN : S.IsStandardNode A k h N) (hNP : N.IsDescendant h P b)
    (e : FacetName S N.ty)
    (hint : relint (N.cell h e.val) ⊆ interior (P.carrier b)) :
    ∃ g : PrimitiveFacet S A, g.depth < k ∧ h < k - g.depth ∧
      N.IsDescendant h (g.birthNode k) (k - g.depth) ∧
      N.cell h e.val ⊆ (S.σ ^ k) '' g.carrier := by
  have aux : ∀ r h : ℕ, b = h + r → ∀ N : FramedNode S,
      S.IsStandardNode A k h N → N.IsDescendant h P b →
      ∀ e : FacetName S N.ty, relint (N.cell h e.val) ⊆ interior (P.carrier b) →
      ∃ g : PrimitiveFacet S A, g.depth < k ∧ h < k - g.depth ∧
        N.IsDescendant h (g.birthNode k) (k - g.depth) ∧
        N.cell h e.val ⊆ (S.σ ^ k) '' g.carrier := by
    intro r
    induction r with
    | zero =>
      intro h hb N hN hNP e hint
      have hbh : b = h := by omega
      subst b
      obtain ⟨r, hr, w, hw⟩ := hNP
      have hr0 : r = 0 := by omega
      subst r
      have hNP : N = P := by simpa [SubstSystem.descendantNode, FramedNode.move] using hw
      subst N
      obtain ⟨x, hx⟩ := birth_ascent_routing_step5_cell_relint_nonempty P h e.val
      exact False.elim ((birth_ascent_routing_step2_cell_front P h e.val (Finset.mem_filter.mp e.property).1
        (intrinsicInterior_subset hx)).2 (hint hx))
    | succ r ih =>
      intro h hb N hN hNP e hint
      obtain ⟨Q, hQ, hQP, i, rfl⟩ := birth_ascent_routing_step5_parent_within A k h b N P hN hP hNP (by omega)
      rcases facet_dichotomy Q (Q.child h i) (h + 1) h (birth_ascent_routing_step2_child_desc Q h i) e with hboundary | hinternal
      · obtain ⟨F, hF, -⟩ := hboundary
        have hFint : relint (Q.cell (h + 1) F.val) ⊆ interior (P.carrier b) := by
          rcases facet_dichotomy P Q b (h + 1) hQP F with hboundary' | hinternal'
          · obtain ⟨F₀, hF₀, -⟩ := hboundary'
            obtain ⟨x, hx⟩ := birth_ascent_routing_step5_cell_relint_nonempty (Q.child h i) h e.val
            exact False.elim ((birth_ascent_routing_step2_cell_front P b F₀.val (Finset.mem_filter.mp F₀.property).1
              (hF₀ (hF (intrinsicInterior_subset hx)))).2 (hint hx))
          · exact hinternal'
        obtain ⟨g, hg, hheight, hQg, hFg⟩ := ih (h + 1) (by omega) Q hQ hQP F hFint
        exact ⟨g, hg, by omega, birth_ascent_routing_step3_desc_trans _ _ _ h (h + 1) (k - g.depth)
          (birth_ascent_routing_step2_child_desc Q h i) hQg, hF.trans hFg⟩
      · obtain ⟨g, hg, hnode, hcell⟩ := birth_ascent_routing_step5_primitive_from_child A k h Q hQ i e hinternal
        refine ⟨g, by omega, by omega, ?_, ?_⟩
        · rw [hg, hnode]
          exact birth_ascent_routing_step2_child_desc Q h i
        · rw [hcell]
  have hNP' := hNP
  obtain ⟨r, hr, _⟩ := hNP'
  exact aux r h hr N hN hNP e hint

/-- Step 5 of the V4 proof of `birth_ascent_routing` (V4 1.25): "`e` has a
finite first provider `g` with birth parent `P_{b'}`, `b < b' ≤` height of
`P₀`, and `e ⊆ g`". This is the finite provider construction for a boundary
facet internal to a specified standard ancestor; no vertex or port is asserted. -/
private theorem birth_ascent_routing_step5_provider {A : S.ι} (k b : ℕ)
    (P : FramedNode S) (hP : S.IsStandardNode A k b P)
    (f : PrimitiveFacet S A) (hf : f.depth < k)
    (hancestor : (f.birthNode k).IsDescendant (k - f.depth) P b)
    (e : FacetName S f.birthType)
    (he : relint ((S.σ ^ k) '' f.birthCell e.val) ⊆ interior (P.carrier b)) :
    ∃ g : PrimitiveFacet S A, g.depth < f.depth ∧
      (f.birthNode k).IsDescendant (k - f.depth) (g.birthNode k) (k - g.depth) ∧
      f.birthCell e.val ⊆ g.carrier := by
  let N : FramedNode S := ⟨f.birthType, (f.birthNode k).frame⟩
  have hN : N = f.birthNode k := by
    apply FramedNode.ext
    · exact (birth_ascent_routing_step2_descendant_type A (k - f.depth) f.depth f.word).symm
    · rfl
  have hstd : S.IsStandardNode A k (k - f.depth) N := by
    rw [hN]
    exact ⟨f.depth, by omega, f.word, rfl⟩
  have hcell : N.cell (k - f.depth) e.val = (S.σ ^ k) '' f.birthCell e.val := by
    change N.prototypeFrame (k - f.depth) '' e.val.carrier =
      (S.σ ^ k) '' (f.birthFrame '' e.val.carrier)
    rw [Set.image_image]
    apply Set.image_congr
    intro x _
    rw [hN]
    exact (birth_ascent_routing_step3_birth_frame f k hf.le x).symm
  obtain ⟨g, hg, hheight, hNg, hsub⟩ := birth_ascent_routing_step5_finite_provider A k b P hP (k - f.depth) N hstd
    (hN.symm ▸ hancestor) e (by rwa [hcell])
  refine ⟨g, by omega, hN ▸ hNg, ?_⟩
  rw [hcell] at hsub
  exact (Set.image_subset_image_iff (S.σ ^ k).injective).mp hsub

/-- Step 6 of the V4 proof of `birth_ascent_routing` (V4 1.25): "let `q` be a
vertex of `mc_C(p)` ... `q` is common-listed" and "at least one child
containing `q` has a facet piece inside `e`". The hypothesis is precisely a
nonempty intersection of the primitive facet with the birth-parent facet. -/
private theorem birth_ascent_routing_step6_seed_port {A : S.ι}
    (f : PrimitiveFacet S A) (e : FacetName S f.birthType)
    (hmeet : (f.carrier ∩ f.birthCell e.val).Nonempty) :
    ∃ q : E d, f.IsVertex q ∧ q ∈ f.birthCell e.val ∧ f.CommonListed q ∧
      ∃ (i : S.I f.birthType) (c : FacetName S (S.child f.birthType i).ty),
        q ∈ f.childCell i c.val ∧ f.childCell i c.val ⊆ f.birthCell e.val := by
  obtain ⟨i, f₀, hF, hint⟩ := f.realization
  let P : FramedNode S := ⟨f.birthType, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hfcell : (P.child 0 i).cell 0 f₀.val = f.localCarrier := by
    rw [birth_ascent_routing_step2_child_cell_zero]; exact hF.symm
  have hpcell : P.cell 1 e.val = S.σ '' e.val.carrier := by
    simp [P, FramedNode.cell, FramedNode.prototypeFrame]
  have hmeet' : ((P.child 0 i).cell 0 f₀.val ∩ P.cell 1 e.val).Nonempty := by
    rw [hfcell, hpcell]
    obtain ⟨p, ⟨a, ⟨q, hq, hqa⟩, hap⟩, ⟨z, hz, hzp⟩⟩ := hmeet
    have hqz : S.σ.symm q = z := hqa.trans (f.birthFrame.injective (hap.trans hzp.symm))
    exact ⟨q, hq, z, hz, (congrArg S.σ hqz).symm.trans (S.σ.apply_symm_apply q)⟩
  have hint' : relint ((P.child 0 i).cell 0 f₀.val) ⊆ interior (P.carrier 1) := by
    rw [hfcell]
    simpa [P, FramedNode.carrier, placedSet] using hint
  obtain ⟨q, hqf, hqe, hqi, hall, j, c, hqc, hce⟩ :=
    birth_ascent_routing_step6_parent_seed_port P 0 i f₀ e hint' hmeet'
  rw [hfcell] at hqf
  have hqe' : S.σ.symm q ∈ e.val.carrier := by
    rw [hpcell] at hqe
    obtain ⟨z, hz, rfl⟩ := hqe
    simpa using hz
  have hlists : f.ChildLists i (f.birthFrame (S.σ.symm q)) := by
    obtain ⟨v, hv, hqv⟩ := hqi
    rw [birth_ascent_routing_step2_child_cell_zero] at hqv
    exact ⟨v, hv, S.σ.symm q, ⟨q, hqv, rfl⟩, rfl⟩
  refine ⟨f.birthFrame (S.σ.symm q), ⟨?_, i, f₀, hF, hlists⟩,
    ⟨S.σ.symm q, hqe', rfl⟩, ?_, j, c, ?_, ?_⟩
  · exact ⟨S.σ.symm q, ⟨q, hqf, rfl⟩, rfl⟩
  · apply birth_ascent_routing_step2_local_common f q
    intro l hql
    obtain ⟨v, hv, hqv⟩ := hall l (by simpa [P, birth_ascent_routing_step2_child_support_zero] using hql)
    rw [birth_ascent_routing_step2_child_cell_zero] at hqv
    exact ⟨v, hv, hqv⟩
  · rw [birth_ascent_routing_step2_child_cell_zero] at hqc
    exact ⟨S.σ.symm q, ⟨q, hqc, rfl⟩, rfl⟩
  · rintro z ⟨a, ⟨b, hb, hba⟩, haz⟩
    have hbe : b ∈ S.σ '' e.val.carrier := by
      rw [← hpcell]
      exact hce (by simpa [P, birth_ascent_routing_step2_child_cell_zero] using hb)
    obtain ⟨x, hx, hxb⟩ := hbe
    refine ⟨x, hx, ?_⟩
    have hxa : x = a := (S.σ.symm_apply_apply x).symm.trans ((congrArg S.σ.symm hxb).trans hba)
    exact congrArg f.birthFrame hxa |>.trans haz

/-- Step 7 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"`p ∈ f ⊆ E`" and "by component closure". A connected primitive carrier
meeting a skeleton component is wholly contained in that component. -/
private theorem birth_ascent_routing_step7_component_closed (A : S.ι) (k : ℕ)
    (E₀ : Set (E d)) (hE : IsSkeletonComponent S A k E₀)
    (f : PrimitiveFacet S A) (hf : f ∈ principalFacets S A k E₀) :
    f.carrier ⊆ E₀ := by
  obtain ⟨x, _, rfl⟩ := hE
  obtain ⟨q, hqf, hqE⟩ := hf.2
  rw [connectedComponentIn_eq hqE]
  exact (principal_component_step5_carrier_connected f).isPreconnected.subset_connectedComponentIn
    hqf (principal_component_step5_carrier_subset f k hf.1)

/-- Step 7 of the V4 proof of `birth_ascent_routing` (V4 1.25): "`g` meets
`E` at `p ∈ f ⊆ E`, so `g ∈ E_A` by component closure". The exit facet,
its provider, and its common-listed facing port give one directed ascent. -/
private theorem birth_ascent_routing_step7_one_ascent (A : S.ι) (k : ℕ)
    (E₀ : Set (E d)) (hE : IsSkeletonComponent S A k E₀) (p : E d)
    (b : ℕ) (P : FramedNode S) (hP : birth_ascent_routing_step1_top_birth A k p b P)
    (f : PrimitiveFacet S A) (hf : f ∈ principalFacets S A k E₀)
    (hp : p ∈ f.carrier) (hnot : f ∉ birth_ascent_routing_step7_top_class A k E₀ p b P) :
    ∃ g ∈ principalFacets S A k E₀, p ∈ g.carrier ∧ AscentLink k f g := by
  have hancestor := birth_ascent_routing_step3_birth_below_top k p b P hP f hf.1 hp
  have hstrict : k - f.depth < b := by
    obtain ⟨r, hr, w, hw⟩ := hancestor
    by_cases hzero : r = 0
    · subst r
      have heq : b = k - f.depth := by omega
      have hnode : f.birthNode k = P := by
        simpa [SubstSystem.descendantNode, FramedNode.move] using hw
      exact False.elim (hnot ⟨hf, hp, heq.symm, hnode⟩)
    · omega
  obtain ⟨e, hpe, he⟩ :=
    birth_ascent_routing_step4_exit_facet k p b P hP f hf.1 hp hancestor hstrict
  obtain ⟨g, hdepth, hfg, heg⟩ :=
    birth_ascent_routing_step5_provider k b P hP.1 f hf.1 hancestor e he
  have hpE : p ∈ E₀ := birth_ascent_routing_step7_component_closed A k E₀ hE f hf hp
  exact ⟨g, ⟨hdepth.trans hf.1, p, heg hpe, hpE⟩, heg hpe,
    hdepth, hfg, e, heg, birth_ascent_routing_step6_seed_port f e ⟨p, hp, hpe⟩⟩

/-- Step 8 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"Birth height strictly increases ... so at most `k` steps". Strictly
smaller birth depths make repeated ascents terminate in the specified class. -/
private theorem birth_ascent_routing_step8_reaches_top {A : S.ι} (k : ℕ)
    (Q T : Set (PrimitiveFacet S A)) (p : E d)
    (hstep : ∀ f ∈ Q, p ∈ f.carrier → f ∉ T →
      ∃ g ∈ Q, p ∈ g.carrier ∧ AscentLink k f g)
    (u : PrimitiveFacet S A) (hu : u ∈ Q) (hpu : p ∈ u.carrier) :
    ∃ v ∈ T, v ∈ Q ∧ p ∈ v.carrier ∧
      Relation.ReflTransGen (ThroughLink Q p (RoutingLink k)) u v := by
  classical
  have aux : ∀ n : ℕ, ∀ u : PrimitiveFacet S A, u.depth = n →
      u ∈ Q → p ∈ u.carrier →
      ∃ v ∈ T, v ∈ Q ∧ p ∈ v.carrier ∧
        Relation.ReflTransGen (ThroughLink Q p (RoutingLink k)) u v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hun hu hpu
      by_cases hut : u ∈ T
      · exact ⟨u, hut, hu, hpu, Relation.ReflTransGen.refl⟩
      · obtain ⟨v, hv, hpv, hlink⟩ := hstep u hu hpu hut
        obtain ⟨w, hw, hwQ, hpw, hroute⟩ :=
          ih v.depth (hun ▸ hlink.1) v rfl hv hpv
        refine ⟨w, hw, hwQ, hpw, ?_⟩
        exact (Relation.ReflTransGen.single
          ⟨hu, hpu, hv, hpv, Or.inr (Or.inl hlink)⟩).trans hroute
  exact aux u.depth u rfl hu hpu

/-- Step 9 of the V4 proof of `birth_ascent_routing` (V4 1.25):
"connected by a chain of the following two kinds of links". The links can
be traversed in either direction; for a same-parent link the common seed
construction also supplies the reversed listedness witness. -/
private theorem birth_ascent_routing_step9_reverse_link {A : S.ι} (k : ℕ)
    (Q : Set (PrimitiveFacet S A)) (p : E d) :
    Symmetric (ThroughLink Q p (RoutingLink k)) := by
  intro f g h
  obtain ⟨hf, hpf, hg, hpg, hlink⟩ := h
  refine ⟨hg, hpg, hf, hpf, ?_⟩
  rcases hlink with hs | ha | ha
  · exact Or.inl (birth_ascent_routing_step2_same_address_seed g f
      hs.1.symm ⟨p, hpg, hpf⟩)
  · exact Or.inr (Or.inr ha)
  · exact Or.inr (Or.inl ha)

/-- P21, V4 1.25: primitive facets of the principal component through a common
point are connected by exactly the same-parent and ascent links. -/
theorem birth_ascent_routing (A : S.ι) (k : ℕ) (E₀ : Set (E d))
    (hE : IsSkeletonComponent S A k E₀) (p : E d)
    (f g : PrimitiveFacet S A) (hf : f ∈ principalFacets S A k E₀)
    (hg : g ∈ principalFacets S A k E₀) (hpf : p ∈ f.carrier) (hpg : p ∈ g.carrier) :
    Relation.ReflTransGen (ThroughLink (principalFacets S A k E₀) p (RoutingLink k))
      f g := by
  obtain ⟨b, P, _, hP⟩ := birth_ascent_routing_step1_least_height A k p
  have hroutes := birth_ascent_routing_step8_reaches_top k
    (principalFacets S A k E₀) (birth_ascent_routing_step7_top_class A k E₀ p b P) p
    (birth_ascent_routing_step7_one_ascent A k E₀ hE p b P hP)
  obtain ⟨u, hu, huQ, hpu, hfu⟩ := hroutes f hf hpf
  obtain ⟨v, hv, hvQ, hpv, hgv⟩ := hroutes g hg hpg
  have huv : SameParentLink u v :=
    birth_ascent_routing_step2_same_parent k u v huQ.1 hvQ.1
      (hu.2.2.1.trans hv.2.2.1.symm) (hu.2.2.2.trans hv.2.2.2.symm)
      ⟨p, hpu, hpv⟩
  exact (hfu.trans (Relation.ReflTransGen.single
    ⟨huQ, hpu, hvQ, hpv, Or.inl huv⟩)).trans
      (Relation.ReflTransGen.symmetric
        (birth_ascent_routing_step9_reverse_link k (principalFacets S A k E₀) p) hgv)

/-- P21, V4 1.25: the least standard ancestor containing every root-owned native
tile through the point, with minimal birth height among all such common ancestors. -/
def IsTopBirth (A : S.ι) (k : ℕ) (p : E d) (b : ℕ) (P : FramedNode S) : Prop :=
  S.IsStandardNode A k b P ∧
    (∀ w : S.RoleWord A k, (S.σ ^ k) p ∈ (S.nativeTile A k w).carrier 0 →
      (S.nativeTile A k w).IsDescendant 0 P b) ∧
    ∀ (b' : ℕ) (P' : FramedNode S), S.IsStandardNode A k b' P' →
      (∀ w : S.RoleWord A k, (S.σ ^ k) p ∈ (S.nativeTile A k w).carrier 0 →
        (S.nativeTile A k w).IsDescendant 0 P' b') → b ≤ b'

/-- P21, V4 1.25: top-class facets, with their actual least common birth parent. -/
def topClass (A : S.ι) (k : ℕ) (E₀ : Set (E d)) (p : E d)
    (b : ℕ) (P : FramedNode S) : Set (PrimitiveFacet S A) :=
  {f | f ∈ principalFacets S A k E₀ ∧ p ∈ f.carrier ∧
    k - f.depth = b ∧ f.birthNode k = P}

/-- P21, V4 1.25: number of strict ascent links in a finite route. -/
def routeAscents {A : S.ι} (k : ℕ) (path : List (PrimitiveFacet S A)) : ℕ := by
  classical
  exact ((path.zip path.tail).filter (fun q => AscentLink k q.1 q.2)).length

/-- Step 1 of the V4 proof of `birth_ascent_top` (V4 1.25): "Let `P₀` be
the least common ancestor within `A`'s subdivision of all native ... tiles
of `A` containing `p`". The root is a common ancestor, so the set of possible
heights has a least element, even before positivity is established. -/
private theorem birth_ascent_top_step1_least_height (A : S.ι) (k : ℕ) (p : E d) :
    ∃ (b : ℕ) (P : FramedNode S), b ≤ k ∧ IsTopBirth A k p b P := by
  classical
  let Q : ℕ → Prop := fun b => ∃ P : FramedNode S,
    S.IsStandardNode A k b P ∧
      ∀ w : S.RoleWord A k, (S.σ ^ k) p ∈ (S.nativeTile A k w).carrier 0 →
        (S.nativeTile A k w).IsDescendant 0 P b
  have hroot : Q k := by
    refine ⟨⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩,
      ⟨0, by omega, (), rfl⟩, ?_⟩
    intro w _
    refine ⟨k, by omega, w, ?_⟩
    simp [SubstSystem.nativeTile, FramedNode.move]
  have hex : ∃ b, Q b := ⟨k, hroot⟩
  obtain ⟨P, hP, hleaves⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, P, Nat.find_min' hex hroot, hP, hleaves, ?_⟩
  intro b' P' hP' hleaves'
  exact Nat.find_min' hex ⟨P', hP', hleaves'⟩

open scoped Topology in
/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "Any vertex `q` of `κ`".
An extreme point in the relative interior of a cell forces that cell to be a singleton. -/
private theorem birth_ascent_top_step2_extreme_relint_singleton (K L : Set (E d)) (hLK : L ⊆ K)
    (q : E d) (hq : q ∈ K.extremePoints ℝ) (hqL : q ∈ relint L) : L = {q} := by
  obtain ⟨q', hq', rfl⟩ := mem_intrinsicInterior.mp hqL
  have hqL : (q' : E d) ∈ L := (show q' ∈ Subtype.val ⁻¹' L from interior_subset hq')
  apply Set.Subset.antisymm
  · intro x hx
    let γ : ℝ → affineSpan ℝ L := fun t =>
      ⟨AffineMap.lineMap (q' : E d) x t,
        AffineMap.lineMap_mem t q'.property (subset_affineSpan ℝ L hx)⟩
    have hγ : Continuous γ := by fun_prop
    have hsmall : ∀ᶠ t : ℝ in 𝓝 0,
        (γ t : E d) ∈ L ∧ (γ (-t) : E d) ∈ L := by
      have h₁ : Filter.Tendsto γ (𝓝 0) (𝓝 q') := by
        simpa [γ] using hγ.tendsto 0
      have h₂ : Filter.Tendsto (fun t => γ (-t)) (𝓝 0) (𝓝 q') := by
        simpa [γ] using (hγ.comp continuous_neg).tendsto 0
      exact Filter.Eventually.and (h₁ (mem_interior_iff_mem_nhds.mp hq'))
        (h₂ (mem_interior_iff_mem_nhds.mp hq'))
    obtain ⟨ε, hε, hεL⟩ := Metric.eventually_nhds_iff.mp hsmall
    let t := ε / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have htε : dist t 0 < ε := by simp [t, abs_of_pos hε]; linarith
    obtain ⟨hplus, hminus⟩ := hεL htε
    have hseg : (q' : E d) ∈ openSegment ℝ (γ t : E d) (γ (-t) : E d) := by
      refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
      simp only [γ, AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
      module
    have hplus_eq : (γ t : E d) = (q' : E d) := hq.2 (hLK hplus) (hLK hminus) hseg
    have hzero : t • (x - (q' : E d)) = 0 := by
      simpa [γ, AffineMap.lineMap_apply] using hplus_eq
    have hxeq : x = (q' : E d) := sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left ht.ne')
    exact Set.mem_singleton_iff.mpr hxeq
  · exact singleton_subset_iff.mpr hqL

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "Any vertex `q` of `κ`".
Every listed cell contains a listed vertex, obtained from an extreme point and its minimal cell. -/
private theorem birth_ascent_top_step2_cell_vertex (P : PolyManifoldDomain d) (C : CellComplex P)
    (e : Cell d) (he : e ∈ C.cells) :
    ∃ v ∈ C.vertices, v.carrier ⊆ e.carrier := by
  obtain ⟨q, hq⟩ := e.flat.compact.extremePoints_nonempty e.flat.connected.nonempty
  have hqP : q ∈ frontier P.carrier := by
    rw [← C.carriers_cover]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hq.1⟩
  let v := C.minimalCell q hqP
  have hv := C.minimalCell_mem q hqP
  have hvsub := C.minimalCell_subset q hqP e he hq.1
  have hvsing : v.carrier = {q} := birth_ascent_top_step2_extreme_relint_singleton e.carrier v.carrier hvsub q hq
    (C.mem_relint_minimalCell q hqP)
  refine ⟨v, Finset.mem_filter.mpr ⟨hv, ?_⟩, hvsub⟩
  have hdim := v.flat.dimension
  rw [cellDirection, hvsing, direction_affineSpan, vectorSpan_singleton, finrank_bot] at hdim
  exact hdim.symm

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "by Lemma 1.1 within `C`".
The descendant relation includes the node itself with its exact frame. -/
private theorem birth_ascent_top_step2_desc_refl (N : FramedNode S) (n : ℕ) : N.IsDescendant n N n := by
  refine ⟨0, by omega, (), ?_⟩
  simp [SubstSystem.descendantNode, FramedNode.move]

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "Lemma 1.1 for the ancestor cell `e` of `P_b` and its child `C`".
An immediate child has the required exact descendant witness. -/
private theorem birth_ascent_top_step2_child_desc (N : FramedNode S) (n : ℕ) (i : S.I N.ty) :
    (N.child n i).IsDescendant n N (n + 1) := by
  refine ⟨1, rfl, ⟨i, ()⟩, ?_⟩
  simp [SubstSystem.descendantNode, FramedNode.move, FramedNode.child]

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "take the minimal cell `κ = mc_C(p)`".
Every placed listed cell belongs to its owner’s frontier. -/
private theorem birth_ascent_top_step2_cell_front (N : FramedNode S) (n : ℕ)
    (e : Cell d) (he : e ∈ (S.cx N.ty).cells) : N.cell n e ⊆ frontier (N.carrier n) := by
  have hsub : e.carrier ⊆ frontier (S.proto N.ty).carrier := by
    rw [← (S.cx N.ty).carriers_cover]
    exact Set.subset_iUnion₂_of_subset e he (Set.Subset.refl _)
  have hcarrier : N.carrier n = N.prototypeFrame n '' (S.proto N.ty).carrier := by
    simp [FramedNode.carrier, FramedNode.prototypeFrame, placedSet,
      SubstSystem.supertile, Set.image_image]
  rw [hcarrier]
  let H := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  change H '' e.carrier ⊆ frontier (H '' (S.proto N.ty).carrier)
  rw [← H.image_frontier]
  exact Set.image_mono hsub

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "Any vertex `q` of `κ` is a vertex of `C`".
Transport a listed vertex through the full prototype frame. -/
private theorem birth_ascent_top_step2_placed_vertex (N : FramedNode S) (n : ℕ)
    (e : CellName S N.ty) : ∃ q ∈ N.cell n e.val, N.Lists n q := by
  obtain ⟨v, hv, hve⟩ := birth_ascent_top_step2_cell_vertex (S.proto N.ty) (S.cx N.ty) e.val e.property
  obtain ⟨q, hq⟩ := v.flat.connected.nonempty
  refine ⟨N.prototypeFrame n q, Set.mem_image_of_mem _ (hve hq), v, hv, ?_⟩
  exact Set.mem_image_of_mem _ hq

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "`κ` is a cell of `C′` ... contained in `f′`".
Sibling minimal-cell equality and vertex inheritance give a common-listed seed. -/
private theorem birth_ascent_top_step2_sibling_seed (P : FramedNode S) (n : ℕ) (i j : S.I P.ty)
    (f : FacetName S (P.child n i).ty) (g : FacetName S (P.child n j).ty)
    (hint : relint ((P.child n i).cell n f.val) ⊆ interior (P.carrier (n + 1)))
    (hmeet : ((P.child n i).cell n f.val ∩ (P.child n j).cell n g.val).Nonempty) :
    ∃ q : E d, q ∈ (P.child n i).cell n f.val ∧ q ∈ (P.child n j).cell n g.val ∧
      (P.child n i).Lists n q ∧ (P.child n j).Lists n q ∧
      ∀ l : S.I P.ty, q ∈ (P.child n l).carrier n → (P.child n l).Lists n q := by
  obtain ⟨p, hpf, hpg⟩ := hmeet
  have hf := (Finset.mem_filter.mp f.property).1
  have hg := (Finset.mem_filter.mp g.property).1
  have hpi := birth_ascent_top_step2_cell_front (P.child n i) n f.val hf hpf
  have hpj := birth_ascent_top_step2_cell_front (P.child n j) n g.val hg hpg
  let e := placedMinimalCell (P.child n i) n p hpi
  have he := placedMinimalCell_spec (P.child n i) n p hpi
  have hef : (P.child n i).cell n e.val ⊆ (P.child n i).cell n f.val :=
    hereditary_trace _ _ n n (birth_ascent_top_step2_desc_refl _ _) f.val e.val hf e.property ⟨p, he, hpf⟩
  have heg : (P.child n i).cell n e.val ⊆ (P.child n j).cell n g.val := by
    by_cases hij : i = j
    · subst j
      exact hereditary_trace _ _ n n (birth_ascent_top_step2_desc_refl _ _) g.val e.val hg e.property ⟨p, he, hpg⟩
    · let e' := placedMinimalCell (P.child n j) n p hpj
      have he' := placedMinimalCell_spec (P.child n j) n p hpj
      rw [sibling_minimalCell_eq P n i j hij p e e' he he']
      exact hereditary_trace _ _ n n (birth_ascent_top_step2_desc_refl _ _) g.val e'.val hg e'.property ⟨p, he', hpg⟩
  obtain ⟨q, hqe, hqi⟩ := birth_ascent_top_step2_placed_vertex (P.child n i) n e
  have hall := primitive_vertex_listed P n i f hint q hqi (hef hqe)
  refine ⟨q, hef hqe, heg hqe, hqi, hall j ?_, hall⟩
  have hc : IsClosed ((P.child n j).carrier n) := by
    exact (((S.proto (P.child n j).ty).compact.image
      (S.σ ^ n).toContinuousLinearEquiv.continuous).image (P.child n j).frame.continuous).isClosed
  exact (frontier_subset_iff_isClosed.mpr hc) (birth_ascent_top_step2_cell_front _ _ _ hg (heg hqe))

/-- Step 6 of the V4 proof of `birth_ascent_top` (V4 1.25): "at least one child containing `q` has a facet piece inside `e`".
Hereditary trace puts a vertex of the minimal child cell on the parent facet; the boundary-facet cover supplies its facing port. -/
private theorem birth_ascent_top_step6_parent_seed_port (P : FramedNode S) (n : ℕ) (i : S.I P.ty)
    (f : FacetName S (P.child n i).ty) (e : FacetName S P.ty)
    (hint : relint ((P.child n i).cell n f.val) ⊆ interior (P.carrier (n + 1)))
    (hmeet : ((P.child n i).cell n f.val ∩ P.cell (n + 1) e.val).Nonempty) :
    ∃ q : E d, q ∈ (P.child n i).cell n f.val ∧ q ∈ P.cell (n + 1) e.val ∧
      (P.child n i).Lists n q ∧
      (∀ j : S.I P.ty, q ∈ (P.child n j).carrier n → (P.child n j).Lists n q) ∧
      ∃ (j : S.I P.ty) (c : FacetName S (P.child n j).ty),
        q ∈ (P.child n j).cell n c.val ∧ (P.child n j).cell n c.val ⊆ P.cell (n + 1) e.val := by
  obtain ⟨p, hpf, hpe⟩ := hmeet
  have hf := (Finset.mem_filter.mp f.property).1
  have hpi := birth_ascent_top_step2_cell_front (P.child n i) n f.val hf hpf
  let κ := placedMinimalCell (P.child n i) n p hpi
  have hκ := placedMinimalCell_spec (P.child n i) n p hpi
  have hκf : (P.child n i).cell n κ.val ⊆ (P.child n i).cell n f.val :=
    hereditary_trace _ _ n n (birth_ascent_top_step2_desc_refl _ _) f.val κ.val hf κ.property ⟨p, hκ, hpf⟩
  have hκe : (P.child n i).cell n κ.val ⊆ P.cell (n + 1) e.val :=
    hereditary_trace _ _ (n + 1) n (birth_ascent_top_step2_child_desc P n i) e.val κ.val
      (Finset.mem_filter.mp e.property).1 κ.property ⟨p, hκ, hpe⟩
  obtain ⟨q, hqκ, hqi⟩ := birth_ascent_top_step2_placed_vertex (P.child n i) n κ
  refine ⟨q, hκf hqκ, hκe hqκ, hqi,
    primitive_vertex_listed P n i f hint q hqi (hκf hqκ), ?_⟩
  have hqe := hκe hqκ
  rw [← (boundary_facet_adjacency P n e).1] at hqe
  obtain ⟨a, hqa⟩ := Set.mem_iUnion.mp hqe
  exact ⟨a.val.1, a.val.2, hqa, a.property⟩

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "both first-generation facets of `P₀`".
At height zero the prescribed child placement is the original rigid frame. -/
private theorem birth_ascent_top_step2_place_zero (B : S.ι) (i : S.I B) : S.placeChild 0 i = (S.child B i).frame := by
  ext x
  simp [SubstSystem.placeChild, SubstSystem.childRotation, linearConj, Child.frame, rigidMotion]

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "both first-generation facets of `P₀`".
Identify the listed cell of a standard ground child with its prescribed placement. -/
private theorem birth_ascent_top_step2_child_cell_zero (B : S.ι) (i : S.I B) (e : Cell d) :
    ((⟨B, AffineIsometryEquiv.refl ℝ (E d)⟩ : FramedNode S).child 0 i).cell 0 e =
      placedSet (S.child B i).frame e.carrier := by
  simp [FramedNode.cell, FramedNode.prototypeFrame, FramedNode.child, birth_ascent_top_step2_place_zero, placedSet]

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "owners ... children of `P₀`".
Identify the ground child support in the same coordinates. -/
private theorem birth_ascent_top_step2_child_support_zero (B : S.ι) (i : S.I B) :
    ((⟨B, AffineIsometryEquiv.refl ℝ (E d)⟩ : FramedNode S).child 0 i).carrier 0 =
      placedSet (S.child B i).frame (S.proto (S.child B i).ty).carrier := by
  simp [FramedNode.carrier, SubstSystem.supertile, FramedNode.child, birth_ascent_top_step2_place_zero, placedSet]

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "common-listed in `P₀`’s immediate subdivision".
Common listedness is preserved by the normalized birth frame. -/
private theorem birth_ascent_top_step2_local_common {A : S.ι} (f : PrimitiveFacet S A) (q : E d)
    (h : ∀ i : S.I f.birthType,
      q ∈ placedSet (S.child f.birthType i).frame (S.proto (S.child f.birthType i).ty).carrier →
        ∃ v ∈ (S.cx (S.child f.birthType i).ty).vertices,
          q ∈ placedSet (S.child f.birthType i).frame v.carrier) :
    f.CommonListed (f.birthFrame (S.σ.symm q)) := by
  intro i hqi
  obtain ⟨a, ⟨b, hb, hab⟩, ha⟩ := hqi
  have hqb : q = b := S.σ.symm.injective (f.birthFrame.injective ha |>.symm.trans hab.symm)
  obtain ⟨v, hv, hqv⟩ := h i (hqb.symm ▸ hb)
  exact ⟨v, hv, S.σ.symm q, ⟨q, hqv, rfl⟩, rfl⟩

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "Any vertex `q` of `κ` is a vertex ... of `f` and `f′`".
The sibling seed transfers to primitive facets with the same full address. -/
private theorem birth_ascent_top_step2_same_address_seed {A : S.ι} (f g : PrimitiveFacet S A)
    (hparent : f.birthAddress = g.birthAddress)
    (hmeet : (f.carrier ∩ g.carrier).Nonempty) : SameParentLink f g := by
  rcases f with ⟨a, u, F, hF⟩
  rcases g with ⟨b, v, G, hG⟩
  have hab : a = b := congrArg Sigma.fst hparent
  subst b
  have huv : u = v := eq_of_heq (Sigma.mk.inj hparent).2
  subst v
  let f : PrimitiveFacet S A := ⟨a, u, F, hF⟩
  let g : PrimitiveFacet S A := ⟨a, u, G, hG⟩
  change SameParentLink f g
  change (f.carrier ∩ g.carrier).Nonempty at hmeet
  have hF' := hF
  have hG' := hG
  obtain ⟨i, f₀, hFc, hint⟩ := hF'
  obtain ⟨j, g₀, hGc, -⟩ := hG'
  let P : FramedNode S := ⟨f.birthType, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hfcell : (P.child 0 i).cell 0 f₀.val = F := by
    rw [birth_ascent_top_step2_child_cell_zero]; exact hFc.symm
  have hgcell : (P.child 0 j).cell 0 g₀.val = G := by
    rw [birth_ascent_top_step2_child_cell_zero]; exact hGc.symm
  have hmeet' : ((P.child 0 i).cell 0 f₀.val ∩ (P.child 0 j).cell 0 g₀.val).Nonempty := by
    rw [hfcell, hgcell]
    obtain ⟨p, ⟨a, ⟨q, hq, hqa⟩, hap⟩, ⟨b, ⟨r, hr, hrb⟩, hbp⟩⟩ := hmeet
    have hqr : q = r := S.σ.symm.injective
      (hqa.trans ((f.birthFrame.injective (hap.trans hbp.symm)).trans hrb.symm))
    exact ⟨q, hq, hqr.symm ▸ hr⟩
  have hint' : relint ((P.child 0 i).cell 0 f₀.val) ⊆ interior (P.carrier 1) := by
    rw [hfcell]
    simpa [P, f, PrimitiveFacet.birthType, FramedNode.carrier, placedSet] using hint
  obtain ⟨q, hqf, hqg, hqi, hqj, hall⟩ := birth_ascent_top_step2_sibling_seed P 0 i j f₀ g₀ hint' hmeet'
  rw [hfcell] at hqf
  rw [hgcell] at hqg
  refine ⟨rfl, f.birthFrame (S.σ.symm q), ?_, ?_, ?_⟩
  · refine ⟨⟨S.σ.symm q, ⟨q, hqf, rfl⟩, rfl⟩, i, f₀, hFc, ?_⟩
    obtain ⟨v, hv, hqv⟩ := hqi
    rw [birth_ascent_top_step2_child_cell_zero] at hqv
    exact ⟨v, hv, S.σ.symm q, ⟨q, hqv, rfl⟩, rfl⟩
  · refine ⟨⟨S.σ.symm q, ⟨q, hqg, rfl⟩, rfl⟩, j, g₀, hGc, ?_⟩
    obtain ⟨v, hv, hqv⟩ := hqj
    rw [birth_ascent_top_step2_child_cell_zero] at hqv
    exact ⟨v, hv, S.σ.symm q, ⟨q, hqv, rfl⟩, rfl⟩
  · apply birth_ascent_top_step2_local_common f q
    intro l hql
    obtain ⟨v, hv, hqv⟩ := hall l (by simpa [P, birth_ascent_top_step2_child_support_zero] using hql)
    rw [birth_ascent_top_step2_child_cell_zero] at hqv
    exact ⟨v, hv, hqv⟩

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "both first-generation facets of `P₀`".
Changing the standard height conjugates each child frame by the expansion. -/
private theorem birth_ascent_top_step2_place_scaled (n : ℕ) {A : S.ι} (i : S.I A) (x : E d) :
    S.placeChild n i ((S.σ ^ n) x) = (S.σ ^ n) ((S.child A i).frame x) := by
  rw [S.placeChild_apply]
  simp [linearConj, Child.frame, rigidMotion, LinearEquiv.mul_apply,
    zpow_natCast, zpow_neg, AffineIsometryEquiv.coe_trans]

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "both first-generation facets of `P₀`".
The same conjugacy compares any two base heights. -/
private theorem birth_ascent_top_step2_place_shift (h k : ℕ) {A : S.ι} (i : S.I A) (x : E d) :
    S.placeChild (h + k) i ((S.σ ^ h) x) = (S.σ ^ h) (S.placeChild k i x) := by
  have h₁ := birth_ascent_top_step2_place_scaled (h + k) i ((S.σ ^ k).symm x)
  have h₂ := birth_ascent_top_step2_place_scaled k i ((S.σ ^ k).symm x)
  simp only [pow_add, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply] at h₁ h₂
  rw [← h₂] at h₁
  exact h₁

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "both first-generation facets of `P₀`".
Iterating child conjugacy compares the complete descendant frames. -/
private theorem birth_ascent_top_step2_descendant_scaled (A : S.ι) (h j : ℕ)
    (w : S.RoleWord A j) (x : E d) :
    (S.descendantNode A h j w).frame ((S.σ ^ h) x) =
      (S.σ ^ h) ((S.nativeTile A j w).frame x) := by
  induction j generalizing A with
  | zero => rfl
  | succ j ih =>
    change S.placeChild (h + j) w.1
      ((S.descendantNode (S.child A w.1).ty h j w.2).frame ((S.σ ^ h) x)) =
      (S.σ ^ h) (S.placeChild (0 + j) w.1
        ((S.nativeTile (S.child A w.1).ty j w.2).frame x))
    rw [ih, birth_ascent_top_step2_place_shift, Nat.zero_add]

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "both first-generation facets of `P₀`".
The type at the end of an address is independent of its base height. -/
private theorem birth_ascent_top_step2_descendant_type (A : S.ι) (h j : ℕ) (w : S.RoleWord A j) :
    (S.descendantNode A h j w).ty = (S.nativeTile A j w).ty := by
  induction j generalizing A with
  | zero => rfl
  | succ j ih => exact ih (S.child A w.1).ty w.2

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "both first-generation facets of `P₀`".
The level at height `h` is the linear image of the corresponding native partition. -/
private theorem birth_ascent_top_step2_descendant_carrier (A : S.ι) (h j : ℕ) (w : S.RoleWord A j) :
    (S.descendantNode A h j w).carrier h = (S.σ ^ h) '' (S.nativeTile A j w).carrier 0 := by
  have hz : (S.nativeTile A j w).carrier 0 =
      (S.nativeTile A j w).frame '' (S.proto (S.nativeTile A j w).ty).carrier := by
    simp [FramedNode.carrier, SubstSystem.supertile, placedSet]
  rw [hz]
  simp only [FramedNode.carrier, SubstSystem.supertile, placedSet, birth_ascent_top_step2_descendant_type]
  rw [Set.image_image, Set.image_image]
  congr 1
  funext x
  exact birth_ascent_top_step2_descendant_scaled A h j w x

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "born in the same node".
Native interior disjointness makes the address-to-standard-node map injective. -/
private theorem birth_ascent_top_step2_descendant_injective (A : S.ι) (h j : ℕ) :
    Function.Injective (S.descendantNode A h j) := by
  intro u v huv
  by_contra hne
  have hcar : (S.nativeTile A j u).carrier 0 = (S.nativeTile A j v).carrier 0 := by
    apply Set.image_injective.mpr (S.σ ^ h).injective
    rw [← birth_ascent_top_step2_descendant_carrier, ← birth_ascent_top_step2_descendant_carrier, huv]
  have hdisj := S.native_disjoint A j hne
  dsimp only at hdisj
  rw [hcar, disjoint_self] at hdisj
  have hnonempty : (interior ((S.nativeTile A j v).carrier 0)).Nonempty := by
    have hz : (S.nativeTile A j v).carrier 0 =
        (S.nativeTile A j v).frame.toHomeomorph '' (S.proto (S.nativeTile A j v).ty).carrier := by
      simp [FramedNode.carrier, SubstSystem.supertile, placedSet]
    rw [hz, ← (S.nativeTile A j v).frame.toHomeomorph.image_interior]
    exact (S.proto _).interior_nonempty.image _
  exact hnonempty.ne_empty hdisj

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "born in the same node".
Equal positive birth heights and equal standard frames recover the full birth address. -/
private theorem birth_ascent_top_step2_equal_address {A : S.ι} (k : ℕ) (f g : PrimitiveFacet S A)
    (hf : f.depth < k) (hg : g.depth < k) (hheight : k - f.depth = k - g.depth)
    (hnode : f.birthNode k = g.birthNode k) : f.birthAddress = g.birthAddress := by
  rcases f with ⟨a, u, F, hF⟩
  rcases g with ⟨b, v, G, hG⟩
  have hab : a = b := by change a < k at hf; change b < k at hg; change k - a = k - b at hheight; omega
  subst b
  have huv : u = v := birth_ascent_top_step2_descendant_injective A (k - a) a hnode
  subst v
  rfl

/-- Step 2 of the V4 proof of `birth_ascent_top` (V4 1.25): "Any vertex
`q` of `κ` is a vertex ... of `f` and `f'` ... and common-listed in `P₀`'s
immediate subdivision". Equal standard birth nodes at equal positive heights
identify the full birth address, and meeting facets have a same-parent seed. -/
private theorem birth_ascent_top_step2_same_parent {A : S.ι} (k : ℕ)
    (f g : PrimitiveFacet S A) (hf : f.depth < k) (hg : g.depth < k)
    (hheight : k - f.depth = k - g.depth) (hnode : f.birthNode k = g.birthNode k)
    (hmeet : (f.carrier ∩ g.carrier).Nonempty) : SameParentLink f g := by
  exact birth_ascent_top_step2_same_address_seed f g
    (birth_ascent_top_step2_equal_address k f g hf hg hheight hnode) hmeet

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Ambient motion preserves exact node identity. -/
private theorem birth_ascent_top_step3_move_inj (g : Iso d) : Function.Injective (fun N : FramedNode S => N.move g) := by
  intro N M h
  apply FramedNode.ext
  · have ht := congrArg (fun N : FramedNode S => N.ty) h
    exact ht
  · ext x : 1
    exact g.injective (congrArg (fun N : FramedNode S => N.frame x) h)

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Split a role word at an intermediate ancestor, retaining its complete frame. -/
private theorem birth_ascent_top_step3_split_word (A : S.ι) (h m j : ℕ) (w : S.RoleWord A (m + j)) :
    ∃ u : S.RoleWord A j, ∃ v : S.RoleWord (S.descendantNode A (h + m) j u).ty m,
      S.descendantNode A h (m + j) w =
        (S.descendantNode (S.descendantNode A (h + m) j u).ty h m v).move
          (S.descendantNode A (h + m) j u).frame := by
  induction j generalizing A with
  | zero =>
    refine ⟨(), w, ?_⟩
    simp [SubstSystem.descendantNode, FramedNode.move]
  | succ j ih =>
    obtain ⟨u, v, hv⟩ := ih (S.child A w.1).ty w.2
    refine ⟨⟨w.1, u⟩, v, ?_⟩
    change (S.descendantNode (S.child A w.1).ty h (m + j) w.2).move
      (S.placeChild (h + (m + j)) w.1) = _
    rw [hv]
    simp [SubstSystem.descendantNode, FramedNode.move, Nat.add_assoc,
      ← AffineIsometryEquiv.trans_assoc]

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Concatenate the path to an ancestor with the path inside that ancestor. -/
private theorem birth_ascent_top_step3_join_words (A : S.ι) (h m j : ℕ) (u : S.RoleWord A j)
    (v : S.RoleWord (S.descendantNode A (h + m) j u).ty m) :
    ∃ w : S.RoleWord A (m + j),
      S.descendantNode A h (m + j) w =
        (S.descendantNode (S.descendantNode A (h + m) j u).ty h m v).move
          (S.descendantNode A (h + m) j u).frame := by
  induction j generalizing A with
  | zero =>
    refine ⟨v, ?_⟩
    simp [SubstSystem.descendantNode, FramedNode.move]
  | succ j ih =>
    obtain ⟨w, hw⟩ := ih (S.child A u.1).ty u.2 v
    refine ⟨⟨u.1, w⟩, ?_⟩
    change (S.descendantNode (S.child A u.1).ty h (m + j) w).move
      (S.placeChild (h + (m + j)) u.1) = _
    rw [hw]
    simp [SubstSystem.descendantNode, FramedNode.move, Nat.add_assoc,
      ← AffineIsometryEquiv.trans_assoc]

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Compose exact descendant witnesses and their frames. -/
private theorem birth_ascent_top_step3_desc_trans (L N P : FramedNode S) (a b c : ℕ)
    (hLN : L.IsDescendant a N b) (hNP : N.IsDescendant b P c) : L.IsDescendant a P c := by
  obtain ⟨m, rfl, v, rfl⟩ := hLN
  obtain ⟨j, rfl, u, rfl⟩ := hNP
  obtain ⟨w, hw⟩ := birth_ascent_top_step3_join_words P.ty a m j u v
  refine ⟨m + j, by omega, w, ?_⟩
  rw [hw]
  rfl

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Every prescribed child carrier is contained in its parent carrier. -/
private theorem birth_ascent_top_step3_child_subset (N : FramedNode S) (n : ℕ) (i : S.I N.ty) :
    (N.child n i).carrier n ⊆ N.carrier (n + 1) := by
  rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hmem : (S.child N.ty i).frame x ∈ S.σ '' (S.proto N.ty).carrier := by
    rw [S.children_cover]
    exact mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩
  obtain ⟨y, hy, he⟩ := hmem
  refine ⟨(S.σ ^ (n + 1)) y, ⟨y, hy, rfl⟩, ?_⟩
  change N.frame ((S.σ ^ (n + 1)) y) = N.frame (S.placeChild n i ((S.σ ^ n) x))
  rw [birth_ascent_top_step2_place_scaled, ← he, pow_succ]
  rfl

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Iterate child containment along the exact descendant address. -/
private theorem birth_ascent_top_step3_desc_subset (D N : FramedNode S) (m n : ℕ)
    (h : D.IsDescendant m N n) : D.carrier m ⊆ N.carrier n := by
  obtain ⟨r, rfl, w, rfl⟩ := h
  induction r generalizing N with
  | zero => simpa [SubstSystem.descendantNode, FramedNode.move] using
      (Subset.rfl : N.carrier m ⊆ N.carrier m)
  | succ r ih =>
    have he : (S.descendantNode N.ty m (r + 1) w).move N.frame =
        (S.descendantNode (N.child (m + r) w.1).ty m r w.2).move
          (N.child (m + r) w.1).frame := rfl
    rw [he]
    exact (ih (N.child (m + r) w.1) w.2).trans (birth_ascent_top_step3_child_subset N (m + r) w.1)

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Descendants of a standard node remain standard in the same root. -/
private theorem birth_ascent_top_step3_standard_desc (A : S.ι) (k a b : ℕ) (N P : FramedNode S)
    (hP : S.IsStandardNode A k b P) (hN : N.IsDescendant a P b) :
    S.IsStandardNode A k a N := by
  obtain ⟨m, rfl, v, rfl⟩ := hN
  obtain ⟨j, hj, u, rfl⟩ := hP
  obtain ⟨w, hw⟩ := birth_ascent_top_step3_join_words A a m j u v
  exact ⟨m + j, by omega, w, hw.symm⟩

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
A standard node has a standard ancestor at each intermediate height. -/
private theorem birth_ascent_top_step3_standard_raise (A : S.ι) (k a b : ℕ) (N : FramedNode S)
    (hN : S.IsStandardNode A k a N) (hab : a ≤ b) (hbk : b ≤ k) :
    ∃ P : FramedNode S, S.IsStandardNode A k b P ∧ N.IsDescendant a P b := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hab
  obtain ⟨j, hj, w, rfl⟩ := hN
  have hmj : m ≤ j := by omega
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hmj
  obtain ⟨u, v, hv⟩ := birth_ascent_top_step3_split_word A a m l w
  exact ⟨S.descendantNode A (a + m) l u, ⟨l, by omega, u, rfl⟩, m, rfl, v, hv⟩

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Different standard nodes at one height have disjoint interiors. -/
private theorem birth_ascent_top_step3_standard_disjoint (A : S.ι) (k n : ℕ) (N P : FramedNode S)
    (hN : S.IsStandardNode A k n N) (hP : S.IsStandardNode A k n P) (hne : N ≠ P) :
    Disjoint (interior (N.carrier n)) (interior (P.carrier n)) := by
  obtain ⟨j, hj, u, rfl⟩ := hN
  obtain ⟨l, hl, v, rfl⟩ := hP
  have hjl : j = l := by omega
  subst l
  have huv : u ≠ v := fun h => hne (h ▸ rfl)
  rw [birth_ascent_top_step2_descendant_carrier, birth_ascent_top_step2_descendant_carrier]
  let e := (S.σ ^ n).toContinuousLinearEquiv.toHomeomorph
  change Disjoint (interior (e '' _)) (interior (e '' _))
  rw [← e.image_interior, ← e.image_interior]
  exact Set.disjoint_image_of_injective e.injective (S.native_disjoint A j huv)

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Every placed node has nonempty interior. -/
private theorem birth_ascent_top_step3_node_interior_nonempty (N : FramedNode S) (n : ℕ) :
    (interior (N.carrier n)).Nonempty := by
  let e := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  have hc : N.carrier n = e '' (S.proto N.ty).carrier := by
    simp [e, FramedNode.prototypeFrame, FramedNode.carrier, SubstSystem.supertile, placedSet,
      Set.image_image]
  rw [hc, ← e.image_interior]
  exact (S.proto N.ty).interior_nonempty.image _

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Two standard nodes at one height sharing a descendant are equal. -/
private theorem birth_ascent_top_step3_common_desc_eq (A : S.ι) (k n l : ℕ) (N P L : FramedNode S)
    (hN : S.IsStandardNode A k n N) (hP : S.IsStandardNode A k n P)
    (hLN : L.IsDescendant l N n) (hLP : L.IsDescendant l P n) : N = P := by
  by_contra hne
  have hdisj := birth_ascent_top_step3_standard_disjoint A k n N P hN hP hne
  obtain ⟨x, hx⟩ := birth_ascent_top_step3_node_interior_nonempty L l
  exact Set.disjoint_left.mp hdisj
    (interior_mono (birth_ascent_top_step3_desc_subset L N l n hLN) hx)
    (interior_mono (birth_ascent_top_step3_desc_subset L P l n hLP) hx)

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Standard ancestors of a common descendant are comparable by height. -/
private theorem birth_ascent_top_step3_common_desc_compare (A : S.ι) (k a b l : ℕ) (N P L : FramedNode S)
    (hN : S.IsStandardNode A k a N) (hP : S.IsStandardNode A k b P)
    (hLN : L.IsDescendant l N a) (hLP : L.IsDescendant l P b) (hab : a ≤ b) :
    N.IsDescendant a P b := by
  have hbk : b ≤ k := by obtain ⟨j, hj, _⟩ := hP; omega
  obtain ⟨Q, hQ, hNQ⟩ := birth_ascent_top_step3_standard_raise A k a b N hN hab hbk
  have hQP := birth_ascent_top_step3_common_desc_eq A k b l Q P L hQ hP (birth_ascent_top_step3_desc_trans L N Q l a b hLN hNQ) hLP
  exact hQP ▸ hNQ

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Native coverage supplies a leaf through any point of a node. -/
private theorem birth_ascent_top_step3_leaf_through (N : FramedNode S) (n : ℕ) (x : E d) (hx : x ∈ N.carrier n) :
    ∃ L : FramedNode S, L.IsDescendant 0 N n ∧ x ∈ L.carrier 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← S.native_cover] at hy
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hy
  refine ⟨(S.nativeTile N.ty n w).move N.frame, ⟨n, by omega, w, rfl⟩, ?_⟩
  obtain ⟨z, hz, rfl⟩ := hw
  exact ⟨z, hz, rfl⟩

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Distinct child roles give distinct framed nodes. -/
private theorem birth_ascent_top_step3_child_injective (N : FramedNode S) (n : ℕ) : Function.Injective (N.child n) := by
  intro i j hij
  have hh : (S.descendantNode N.ty n 1 ⟨i, ()⟩).move N.frame =
      (S.descendantNode N.ty n 1 ⟨j, ()⟩).move N.frame := by
    simpa [SubstSystem.descendantNode, FramedNode.child, FramedNode.move] using hij
  have hw := birth_ascent_top_step2_descendant_injective N.ty n 1 (birth_ascent_top_step3_move_inj N.frame hh)
  exact congrArg Sigma.fst hw

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
A listed cell lies in its closed owner. -/
private theorem birth_ascent_top_step3_cell_subset (N : FramedNode S) (n : ℕ)
    (e : Cell d) (he : e ∈ (S.cx N.ty).cells) : N.cell n e ⊆ N.carrier n := by
  have hc : IsClosed (N.carrier n) :=
    (((S.proto N.ty).compact.image (S.σ ^ n).toContinuousLinearEquiv.continuous).image N.frame.continuous).isClosed
  exact (birth_ascent_top_step2_cell_front N n e he).trans (frontier_subset_iff_isClosed.mpr hc)

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
The normalized birth frame and the standard height-k prototype frame agree after expansion. -/
private theorem birth_ascent_top_step3_birth_frame {A : S.ι} (f : PrimitiveFacet S A) (k : ℕ)
    (hf : f.depth ≤ k) (x : E d) :
    (S.σ ^ k) (f.birthFrame x) = (f.birthNode k).prototypeFrame (k - f.depth) x := by
  change (S.σ ^ k) ((S.σ ^ f.depth).symm ((S.nativeTile A f.depth f.word).frame x)) =
    (S.descendantNode A (k - f.depth) f.depth f.word).frame ((S.σ ^ (k - f.depth)) x)
  rw [birth_ascent_top_step2_descendant_scaled]
  have hp : S.σ ^ k = (S.σ ^ (k - f.depth)) * (S.σ ^ f.depth) := by
    rw [← pow_add, Nat.sub_add_cancel hf]
  rw [hp]
  simp

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25):
"their least common ancestor `P_b` is a descendant of `P₀`".
Internal-facet pairing gives two distinct immediate children through the point, in the standard coordinates. -/
private theorem birth_ascent_top_step3_primitive_two_children {A : S.ι} (k : ℕ)
    (f : PrimitiveFacet S A) (hf : f.depth < k) (p : E d) (hp : p ∈ f.carrier) :
    ∃ (n : ℕ) (N : FramedNode S), k - f.depth = n + 1 ∧ N = f.birthNode k ∧
      ∃ i j : S.I N.ty, i ≠ j ∧
        (S.σ ^ k) p ∈ (N.child n i).carrier n ∧ (S.σ ^ k) p ∈ (N.child n j).carrier n := by
  have hb : 0 < k - f.depth := by omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  let N : FramedNode S := ⟨f.birthType, (f.birthNode k).frame⟩
  have hN : N = f.birthNode k := by
    apply FramedNode.ext
    · exact (birth_ascent_top_step2_descendant_type A (k - f.depth) f.depth f.word).symm
    · rfl
  obtain ⟨i, f₀, hF, hint⟩ := f.realization
  let R : FramedNode S := ⟨f.birthType, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hcell : (R.child 0 i).cell 0 f₀.val = f.localCarrier := by
    rw [birth_ascent_top_step2_child_cell_zero]; exact hF.symm
  have hint' : relint ((R.child 0 i).cell 0 f₀.val) ⊆ interior (R.carrier 1) := by
    rw [hcell]
    simpa [R, FramedNode.carrier, placedSet] using hint
  have hne : (relint ((R.child 0 i).cell 0 f₀.val)).Nonempty := by
    rw [birth_ascent_top_step2_child_cell_zero]
    change (intrinsicInterior ℝ ((S.child f.birthType i).frame.toAffineIsometry '' f₀.val.carrier)).Nonempty
    rw [(S.child f.birthType i).frame.toAffineIsometry.image_intrinsicInterior]
    exact f₀.val.flat.relint_nonempty.image _
  obtain ⟨x, hx⟩ := hne
  obtain ⟨j, ⟨hji, f₁, heq, -⟩, -⟩ := (internal_facet_pairing R 0 i f₀ ⟨x, hx, hint' hx⟩).2
  obtain ⟨a, ⟨q, hq, hqa⟩, hap⟩ := hp
  have hpoint : (S.σ ^ k) p = N.frame ((S.σ ^ n) q) := by
    rw [← hap, ← hqa, birth_ascent_top_step3_birth_frame f k hf.le]
    change (f.birthNode k).frame ((S.σ ^ (k - f.depth)) (S.σ.symm q)) = _
    rw [hn, pow_succ]
    simp [N]
  have hq₀ : q ∈ (R.child 0 i).cell 0 f₀.val := hcell.symm ▸ hq
  have hq₁ : q ∈ (R.child 0 j).cell 0 f₁.val := heq.symm ▸ hq₀
  have hqi := birth_ascent_top_step3_cell_subset (R.child 0 i) 0 f₀.val (Finset.mem_filter.mp f₀.property).1 hq₀
  have hqj := birth_ascent_top_step3_cell_subset (R.child 0 j) 0 f₁.val (Finset.mem_filter.mp f₁.property).1 hq₁
  have hlift (l : S.I f.birthType) (hql : q ∈ (R.child 0 l).carrier 0) :
      (S.σ ^ k) p ∈ (N.child n l).carrier n := by
    rw [birth_ascent_top_step2_child_support_zero] at hql
    obtain ⟨y, hy, hyq⟩ := hql
    refine ⟨(S.σ ^ n) y, ⟨y, hy, rfl⟩, ?_⟩
    change N.frame (S.placeChild n l ((S.σ ^ n) y)) = (S.σ ^ k) p
    rw [birth_ascent_top_step2_place_scaled, hyq, hpoint]
  exact ⟨n, N, hn, hN, i, j, hji.symm, hlift i hqi, hlift j hqj⟩

/-- Step 3 of the V4 proof of `birth_ascent_top` (V4 1.25): "`f` is shared
by two children of `P_b` ... which both contain `p`, hence contain `A`-owned
native tiles through `p`, so their least common ancestor `P_b` is a descendant
of `P₀`". This concerns only ancestry, without selecting an ascent. -/
private theorem birth_ascent_top_step3_birth_below_top {A : S.ι} (k : ℕ)
    (p : E d) (b : ℕ) (P : FramedNode S) (hP : IsTopBirth A k p b P)
    (f : PrimitiveFacet S A) (hf : f.depth < k) (hp : p ∈ f.carrier) :
    (f.birthNode k).IsDescendant (k - f.depth) P b := by
  obtain ⟨n, N, hn, hN, i, j, hij, hpi, hpj⟩ := birth_ascent_top_step3_primitive_two_children k f hf p hp
  have hstd : S.IsStandardNode A k (n + 1) N := by
    rw [hN, ← hn]
    exact ⟨f.depth, by omega, f.word, rfl⟩
  have hstdi := birth_ascent_top_step3_standard_desc A k n (n + 1) (N.child n i) N hstd (birth_ascent_top_step2_child_desc N n i)
  have hstdj := birth_ascent_top_step3_standard_desc A k n (n + 1) (N.child n j) N hstd (birth_ascent_top_step2_child_desc N n j)
  obtain ⟨L, hLi, hpL⟩ := birth_ascent_top_step3_leaf_through (N.child n i) n _ hpi
  obtain ⟨M, hMj, hpM⟩ := birth_ascent_top_step3_leaf_through (N.child n j) n _ hpj
  have hcover (L : FramedNode S) (hL : S.IsStandardNode A k 0 L)
      (hpL : (S.σ ^ k) p ∈ L.carrier 0) : L.IsDescendant 0 P b := by
    obtain ⟨r, hr, w, rfl⟩ := hL
    have hrk : r = k := by omega
    subst r
    exact hP.2.1 w hpL
  have hLP := hcover L (birth_ascent_top_step3_standard_desc A k 0 n L (N.child n i) hstdi hLi) hpL
  have hMP := hcover M (birth_ascent_top_step3_standard_desc A k 0 n M (N.child n j) hstdj hMj) hpM
  have hLN := birth_ascent_top_step3_desc_trans L (N.child n i) N 0 n (n + 1) hLi (birth_ascent_top_step2_child_desc N n i)
  have hle : n + 1 ≤ b := by
    by_contra hnb
    have hbn : b ≤ n := by omega
    have hnk : n ≤ k := by obtain ⟨r, hr, _⟩ := hstd; omega
    obtain ⟨Q, hQ, hPQ⟩ := birth_ascent_top_step3_standard_raise A k b n P hP.1 hbn hnk
    have hiQ := birth_ascent_top_step3_common_desc_eq A k n 0 (N.child n i) Q L hstdi hQ hLi
      (birth_ascent_top_step3_desc_trans L P Q 0 b n hLP hPQ)
    have hjQ := birth_ascent_top_step3_common_desc_eq A k n 0 (N.child n j) Q M hstdj hQ hMj
      (birth_ascent_top_step3_desc_trans M P Q 0 b n hMP hPQ)
    exact hij (birth_ascent_top_step3_child_injective N n (hiQ.trans hjQ.symm))
  rw [hn, ← hN]
  exact birth_ascent_top_step3_common_desc_compare A k (n + 1) b 0 N P L hstd hP.1 hLN hLP hle

/-- Step 1 of the V4 proof of `birth_ascent_top_step4_exit_facet` (V4 1.25):
"choose a point `y ∈ int P_b` near `p`". The full prototype frame preserves
closedness and regular closedness, so every point of a node is approached by
its interior points. -/
private theorem birth_ascent_top_step4_exit_facet_step1_regular_closed
    (N : FramedNode S) (n : ℕ) :
    IsClosed (N.carrier n) ∧ IsRegularClosed (N.carrier n) := by
  let H := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  have hc : N.carrier n = H '' (S.proto N.ty).carrier := by
    simp [H, FramedNode.prototypeFrame, FramedNode.carrier,
      SubstSystem.supertile, placedSet, Set.image_image]
  rw [hc]
  refine ⟨H.isClosedMap _ (S.proto N.ty).compact.isClosed, ?_⟩
  change closure (interior (H '' (S.proto N.ty).carrier)) = _
  rw [← H.image_interior, ← H.image_closure, (S.proto N.ty).regularClosed]

/-- Step 2 of the V4 proof of `birth_ascent_top_step4_exit_facet` (V4 1.25):
"an `A`-owned native tile not in `P_b` (exists by minimality of `P₀`)".
Raise such a native tile to the height of `P_b`; its ancestor is a different
standard node through the point and is still below `P₀`. -/
private theorem birth_ascent_top_step4_exit_facet_step2_other_node
    {A : S.ι} (k : ℕ) (p : E d) (b : ℕ) (P : FramedNode S)
    (hP : IsTopBirth A k p b P) (n : ℕ) (N : FramedNode S)
    (hN : S.IsStandardNode A k n N) (hlt : n < b) :
    ∃ M : FramedNode S, S.IsStandardNode A k n M ∧
      M.IsDescendant n P b ∧ M ≠ N ∧ (S.σ ^ k) p ∈ M.carrier n := by
  classical
  have hex : ∃ w : S.RoleWord A k,
      (S.σ ^ k) p ∈ (S.nativeTile A k w).carrier 0 ∧
        ¬ (S.nativeTile A k w).IsDescendant 0 N n := by
    by_contra h
    have hcover : ∀ w : S.RoleWord A k,
        (S.σ ^ k) p ∈ (S.nativeTile A k w).carrier 0 →
          (S.nativeTile A k w).IsDescendant 0 N n := by
      intro w hw
      by_contra hn
      exact h ⟨w, hw, hn⟩
    exact (not_le_of_gt hlt) (hP.2.2 n N hN hcover)
  obtain ⟨w, hpw, hwN⟩ := hex
  have hwstd : S.IsStandardNode A k 0 (S.nativeTile A k w) :=
    ⟨k, by omega, w, rfl⟩
  have hnk : n ≤ k := by obtain ⟨j, hj, _⟩ := hN; omega
  obtain ⟨M, hM, hwM⟩ := birth_ascent_top_step3_standard_raise A k 0 n
    (S.nativeTile A k w) hwstd (Nat.zero_le n) hnk
  refine ⟨M, hM, ?_, ?_, ?_⟩
  · exact birth_ascent_top_step3_common_desc_compare A k n b 0 M P
      (S.nativeTile A k w) hM hP.1 hwM (hP.2.1 w hpw) hlt.le
  · intro heq
    exact hwN (heq ▸ hwM)
  · exact birth_ascent_top_step3_desc_subset _ M 0 n hwM hpw

/-- Step 3 of the V4 proof of `birth_ascent_top_step4_exit_facet` (V4 1.25):
"near a boundary point the polyhedral boundary separates a small ball into
two sides and `int P₀` is one of them". This is the local connectedness
assertion for a single polyhedral manifold domain, with no subdivision or
facet selection. -/
private theorem birth_ascent_top_step4_exit_facet_step3_boundary_neighborhood
    (D : PolyManifoldDomain d) (p : E d) (hp : p ∈ frontier D.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      IsPreconnected (interior D.carrier ∩ Metric.ball p r) := by
  sorry

/-- Step 4 of the V4 proof of `birth_ascent_top_step4_exit_facet` (V4 1.25):
"`int P₀ ∩ B(p,ρ)` is connected for small `ρ` ... near an interior point
it is a ball". Transport the small connected interior neighborhood through
the full affine frame; it can be chosen inside any prescribed open neighborhood. -/
private theorem birth_ascent_top_step4_exit_facet_step4_interior_neighborhood
    (N : FramedNode S) (n : ℕ) (p : E d) (hp : p ∈ N.carrier n)
    (U : Set (E d)) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ V : Set (E d), IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      IsPreconnected (interior (N.carrier n) ∩ V) := by
  let H := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  have hc : N.carrier n = H '' (S.proto N.ty).carrier := by
    simp [H, FramedNode.prototypeFrame, FramedNode.carrier,
      SubstSystem.supertile, placedSet, Set.image_image]
  let q := H.symm p
  have hq : q ∈ (S.proto N.ty).carrier := by
    rw [hc] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    simpa [q] using hz
  have hqU : q ∈ H ⁻¹' U := by simpa [q] using hpU
  obtain ⟨r, hr, hrU, hrconn⟩ : ∃ r : ℝ, 0 < r ∧
      Metric.ball q r ⊆ H ⁻¹' U ∧
        IsPreconnected (interior (S.proto N.ty).carrier ∩ Metric.ball q r) := by
    by_cases hi : q ∈ interior (S.proto N.ty).carrier
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
        (isOpen_interior.inter (hU.preimage H.continuous)) q ⟨hi, hqU⟩
      refine ⟨r, hr, fun x hx => (hball hx).2, ?_⟩
      rw [inter_eq_right.mpr (fun x hx => (hball hx).1)]
      exact (convex_ball q r).isPreconnected
    · have hf : q ∈ frontier (S.proto N.ty).carrier :=
        ⟨(S.proto N.ty).compact.isClosed.closure_eq.symm ▸ hq, hi⟩
      obtain ⟨ε, hε, hconn⟩ :=
        birth_ascent_top_step4_exit_facet_step3_boundary_neighborhood
          (S.proto N.ty) q hf
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hU.preimage H.continuous) q hqU
      let r := min ε δ / 2
      have hr : 0 < r := by dsimp [r]; positivity
      have hrε : r < ε := by dsimp [r]; linarith [min_le_left ε δ]
      have hrδ : r ≤ δ := by dsimp [r]; linarith [min_le_right ε δ]
      exact ⟨r, hr, (Metric.ball_subset_ball hrδ).trans hball, hconn r hr hrε⟩
  refine ⟨H '' Metric.ball q r, H.isOpenMap _ Metric.isOpen_ball,
    ⟨q, Metric.mem_ball_self hr, H.apply_symm_apply p⟩, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hrU hx
  · have heq : interior (N.carrier n) ∩ H '' Metric.ball q r =
        H '' (interior (S.proto N.ty).carrier ∩ Metric.ball q r) := by
      rw [hc, ← H.image_interior, Set.image_inter H.injective]
    rw [heq]
    exact hrconn.image H H.continuous.continuousOn

/-- Step 5 of the V4 proof of `birth_ascent_top_step4_exit_facet` (V4 1.25):
"`ρ` smaller than the distance from `p` to all cells ... not containing `p`
(finitely many)". Remove the finite closed union of facets missing the point. -/
private theorem birth_ascent_top_step4_exit_facet_step5_avoid_facets
    (N : FramedNode S) (n : ℕ) (p : E d) :
    ∃ U : Set (E d), IsOpen U ∧ p ∈ U ∧
      ∀ (e : FacetName S N.ty) (x : E d), x ∈ U → x ∈ N.cell n e.val →
        p ∈ N.cell n e.val := by
  classical
  let bad := (S.cx N.ty).facets.filter (fun e => p ∉ N.cell n e)
  let U := (⋃ e ∈ bad, N.cell n e)ᶜ
  have hc (e : Cell d) : IsClosed (N.cell n e) :=
    (e.flat.compact.image (N.prototypeFrame n).continuous_of_finiteDimensional).isClosed
  refine ⟨U, (isClosed_biUnion_finset (fun e _ => hc e)).isOpen_compl, ?_, ?_⟩
  · intro h
    obtain ⟨e, he, hpe⟩ := Set.mem_iUnion₂.mp h
    exact (Finset.mem_filter.mp he).2 hpe
  · intro e x hx hxe
    by_contra hpe
    exact hx (Set.mem_iUnion₂.mpr ⟨e.val,
      Finset.mem_filter.mpr ⟨e.property, hpe⟩, hxe⟩)

/-- Step 6 of the V4 proof of `birth_ascent_top_step4_exit_facet` (V4 1.25):
"At the first exit from `P_b`". A connected set meeting the interior and
the complement of a closed set meets its frontier. -/
private theorem birth_ascent_top_step4_exit_facet_step6_crossing
    {K V : Set (E d)} (hK : IsClosed K) (hV : IsPreconnected V)
    (hin : (V ∩ interior K).Nonempty) (hout : (V ∩ Kᶜ).Nonempty) :
    (V ∩ frontier K).Nonempty := by
  by_contra h
  have hsplit : V ⊆ interior K ∪ Kᶜ := by
    intro x hx
    by_cases hxK : x ∈ K
    · left
      by_contra hi
      exact h ⟨x, hx, hK.closure_eq.symm ▸ hxK, hi⟩
    · exact Or.inr hxK
  obtain ⟨x, _, hxi, hxo⟩ := hV (interior K) Kᶜ
    isOpen_interior hK.isOpen_compl hsplit hin hout
  exact hxo (interior_subset hxi)

/-- Step 7 of the V4 proof of `birth_ascent_top_step4_exit_facet` (V4 1.25):
"the path crosses a facet `e`". The closed facets of the finite boundary
complex cover every frontier point, also after applying the node's full frame. -/
private theorem birth_ascent_top_step4_exit_facet_step7_frontier_facets
    (N : FramedNode S) (n : ℕ) {x : E d} (hx : x ∈ frontier (N.carrier n)) :
    ∃ e : FacetName S N.ty, x ∈ N.cell n e.val := by
  let H := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  have hc : N.carrier n = H '' (S.proto N.ty).carrier := by
    simp [H, FramedNode.prototypeFrame, FramedNode.carrier,
      SubstSystem.supertile, placedSet, Set.image_image]
  rw [hc, ← H.image_frontier] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨e, hye⟩ := Set.mem_iUnion.mp
    (principal_component_step1_hull_geometry_step11_facets_cover
      (S.proto N.ty) (S.cx N.ty) hy)
  exact ⟨e, y, hye, rfl⟩

/-- Step 4 of the V4 proof of `birth_ascent_top` (V4 1.25): "At the first
exit from `P_b` the path crosses a facet `e` ... lying in `int P₀`"; choosing
the ball smaller than the distances to cells not containing `p` ensures
"the crossed facet `e` contains `p`". All sets in this conclusion are compared
in the standard height-`k` coordinates. -/
private theorem birth_ascent_top_step4_exit_facet {A : S.ι} (k : ℕ)
    (p : E d) (b : ℕ) (P : FramedNode S) (hP : IsTopBirth A k p b P)
    (f : PrimitiveFacet S A) (hf : f.depth < k) (hp : p ∈ f.carrier)
    (hancestor : (f.birthNode k).IsDescendant (k - f.depth) P b)
    (hstrict : k - f.depth < b) :
    ∃ e : FacetName S f.birthType, p ∈ f.birthCell e.val ∧
      relint ((S.σ ^ k) '' f.birthCell e.val) ⊆ interior (P.carrier b) := by
  let n := k - f.depth
  let x := (S.σ ^ k) p
  let N : FramedNode S := ⟨f.birthType, (f.birthNode k).frame⟩
  have hN : N = f.birthNode k := by
    apply FramedNode.ext
    · exact (birth_ascent_top_step2_descendant_type A n f.depth f.word).symm
    · rfl
  have hstd : S.IsStandardNode A k n N := by
    rw [hN]
    exact ⟨f.depth, by dsimp [n]; omega, f.word, rfl⟩
  have hNP : N.IsDescendant n P b := hN.symm ▸ hancestor
  have hxN : x ∈ N.carrier n := by
    obtain ⟨r, R, hr, hR, i, j, hij, hpi, hpj⟩ :=
      birth_ascent_top_step3_primitive_two_children k f hf p hp
    have hmem := birth_ascent_top_step3_child_subset R r i hpi
    rwa [hR, ← hr, ← hN] at hmem
  have hNsub := birth_ascent_top_step3_desc_subset N P n b hNP
  obtain ⟨M, hM, hMP, hne, hxM⟩ :=
    birth_ascent_top_step4_exit_facet_step2_other_node k p b P hP n N hstd hstrict
  have hMsub := birth_ascent_top_step3_desc_subset M P n b hMP
  obtain ⟨U, hU, hxU, hfacets⟩ :=
    birth_ascent_top_step4_exit_facet_step5_avoid_facets N n x
  obtain ⟨V, hV, hxV, hVU, hconn⟩ :=
    birth_ascent_top_step4_exit_facet_step4_interior_neighborhood
      P b x (hNsub hxN) U hU hxU
  obtain ⟨hNclosed, hNreg⟩ := birth_ascent_top_step4_exit_facet_step1_regular_closed N n
  obtain ⟨_, hMreg⟩ := birth_ascent_top_step4_exit_facet_step1_regular_closed M n
  have hxNi : x ∈ closure (interior (N.carrier n)) := hNreg.symm ▸ hxN
  have hxMi : x ∈ closure (interior (M.carrier n)) := hMreg.symm ▸ hxM
  obtain ⟨y, hyV, hyN⟩ := mem_closure_iff.mp hxNi V hV hxV
  obtain ⟨z, hzV, hzM⟩ := mem_closure_iff.mp hxMi V hV hxV
  have hdisj : Disjoint (N.carrier n) (interior (M.carrier n)) := by
    rw [← hNreg]
    exact (birth_ascent_top_step3_standard_disjoint A k n N M hstd hM hne.symm).closure_left
      isOpen_interior
  have hzout : z ∉ N.carrier n := fun hzN => Set.disjoint_left.mp hdisj hzN hzM
  obtain ⟨q, ⟨hqP, hqV⟩, hqfront⟩ :=
    birth_ascent_top_step4_exit_facet_step6_crossing hNclosed hconn
      ⟨y, ⟨interior_mono hNsub hyN, hyV⟩, hyN⟩
      ⟨z, ⟨interior_mono hMsub hzM, hzV⟩, hzout⟩
  obtain ⟨e, hqe⟩ := birth_ascent_top_step4_exit_facet_step7_frontier_facets N n hqfront
  have hxe : x ∈ N.cell n e.val := hfacets e q (hVU hqV) hqe
  have hinternal : relint (N.cell n e.val) ⊆ interior (P.carrier b) := by
    rcases facet_dichotomy P N b n hNP e with hboundary | hi
    · obtain ⟨F, hF, _⟩ := hboundary
      exact False.elim ((birth_ascent_top_step2_cell_front P b F.val
        (Finset.mem_filter.mp F.property).1 (hF hqe)).2 hqP)
    · exact hi
  have hcell : N.cell n e.val = (S.σ ^ k) '' f.birthCell e.val := by
    change N.prototypeFrame n '' e.val.carrier =
      (S.σ ^ k) '' (f.birthFrame '' e.val.carrier)
    rw [Set.image_image]
    apply Set.image_congr
    intro a _
    rw [hN]
    exact (birth_ascent_top_step3_birth_frame f k hf.le a).symm
  refine ⟨e, ?_, ?_⟩
  · rw [hcell] at hxe
    exact (S.σ ^ k).injective.mem_set_image.mp hxe
  · rwa [← hcell]

/-- Step 5 of the V4 proof of `birth_ascent_top` (V4 1.25):
"`e` has a finite first provider `g` ... and `e ⊆ g`".
Relative interiors commute with the full affine frames, including anisotropic expansion. -/
private theorem birth_ascent_top_step5_relint_image (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
    relint (e '' K) = e '' relint K := by
  let h := e.toHomeomorphOfFiniteDimensional
  have hspan : h '' (affineSpan ℝ K : Set (E d)) =
      (affineSpan ℝ (e '' K) : Set (E d)) := by
    exact congrArg (fun A : AffineSubspace ℝ (E d) => (A : Set (E d)))
      (AffineSubspace.map_span e.toAffineMap K)
  let f : (affineSpan ℝ K) ≃ₜ (affineSpan ℝ (e '' K)) :=
    (h.image _).trans (Homeomorph.setCongr hspan)
  have hf (x : affineSpan ℝ K) : (f x).val = e x.val := rfl
  have hp : (f ⁻¹' ((↑) ⁻¹' (e '' K) : Set (affineSpan ℝ (e '' K)))) =
      ((↑) ⁻¹' K : Set (affineSpan ℝ K)) := by
    ext x
    change e x.val ∈ e '' K ↔ x.val ∈ K
    exact e.injective.mem_set_image
  have hi := f.preimage_interior ((↑) ⁻¹' (e '' K) : Set (affineSpan ℝ (e '' K)))
  rw [hp] at hi
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hm : f.symm y ∈ interior ((↑) ⁻¹' K : Set (affineSpan ℝ K)) := by
      rw [← hi]
      simpa using hy
    refine ⟨(f.symm y).val, ⟨f.symm y, hm, rfl⟩, ?_⟩
    simpa only [f.apply_symm_apply] using (hf (f.symm y)).symm
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨f w, ?_, hf w⟩
    change w ∈ f ⁻¹' interior ((↑) ⁻¹' (e '' K) : Set (affineSpan ℝ (e '' K)))
    rwa [hi]

/-- Step 5 of the V4 proof of `birth_ascent_top` (V4 1.25):
"`e` has a finite first provider `g` ... and `e ⊆ g`".
Every placed facet has nonempty relative interior, so interior containment cannot be vacuous. -/
private theorem birth_ascent_top_step5_cell_relint_nonempty (N : FramedNode S) (n : ℕ) (e : Cell d) :
    (relint (N.cell n e)).Nonempty := by
  rw [FramedNode.cell, birth_ascent_top_step5_relint_image]
  exact e.flat.relint_nonempty.image _

/-- Step 5 of the V4 proof of `birth_ascent_top` (V4 1.25):
"`e` has a finite first provider `g` ... and `e ⊆ g`".
An internal child facet of a standard node gives a primitive facet with the exact birth address and normalized carrier. -/
private theorem birth_ascent_top_step5_primitive_from_child (A : S.ι) (k n : ℕ) (Q : FramedNode S)
    (hQ : S.IsStandardNode A k (n + 1) Q) (i : S.I Q.ty)
    (e : FacetName S (Q.child n i).ty)
    (hint : relint ((Q.child n i).cell n e.val) ⊆ interior (Q.carrier (n + 1))) :
    ∃ g : PrimitiveFacet S A, k - g.depth = n + 1 ∧ g.birthNode k = Q ∧
      (S.σ ^ k) '' g.carrier = (Q.child n i).cell n e.val := by
  obtain ⟨j, hk, w, hQ⟩ := hQ
  have hty : (S.nativeTile A j w).ty = Q.ty :=
    (birth_ascent_top_step2_descendant_type A (n + 1) j w).symm.trans (congrArg FramedNode.ty hQ.symm)
  let F := placedSet (S.child Q.ty i).frame e.val.carrier
  let T : E d ≃ᵃ[ℝ] E d := (S.σ ^ n).toAffineEquiv.trans Q.frame.toAffineEquiv
  have hcell : (Q.child n i).cell n e.val = T '' F := by
    simp only [FramedNode.cell, FramedNode.prototypeFrame, FramedNode.child,
      AffineEquiv.coe_trans, AffineIsometryEquiv.coe_toAffineEquiv,
      AffineIsometryEquiv.coe_trans, LinearEquiv.coe_toAffineEquiv,
      T, F, placedSet, Set.image_image]
    congr 1
    funext x
    exact congrArg Q.frame (birth_ascent_top_step2_place_scaled n i x)
  have hcarrier : Q.carrier (n + 1) = T '' S.supertile 1 Q.ty := by
    simp [FramedNode.carrier, SubstSystem.supertile, placedSet, T,
      Set.image_image, pow_succ, LinearEquiv.mul_apply]
  have hlocal : relint F ⊆ interior (S.supertile 1 Q.ty) := by
    intro x hx
    have hh : T x ∈ interior (Q.carrier (n + 1)) := by
      apply hint
      rw [hcell, birth_ascent_top_step5_relint_image]
      exact Set.mem_image_of_mem T hx
    rw [hcarrier] at hh
    let H := T.toHomeomorphOfFiniteDimensional
    change H x ∈ interior (H '' S.supertile 1 Q.ty) at hh
    rw [← H.image_interior] at hh
    exact H.injective.mem_set_image.mp hh
  have hreal : ∃ (i : S.I (S.nativeTile A j w).ty)
      (e : FacetName S (S.child (S.nativeTile A j w).ty i).ty),
      F = placedSet (S.child (S.nativeTile A j w).ty i).frame e.val.carrier ∧
        relint F ⊆ interior (S.supertile 1 (S.nativeTile A j w).ty) := by
    rw [hty]
    exact ⟨i, e, rfl, hlocal⟩
  let g : PrimitiveFacet S A := ⟨j, w, F, hreal⟩
  have hg : k - g.depth = n + 1 := by change k - j = n + 1; omega
  have hgj : g.depth < k := by change j < k; omega
  have hnode : g.birthNode k = Q := by
    change S.descendantNode A (k - j) j w = Q
    rw [show k - j = n + 1 by omega]
    exact hQ.symm
  refine ⟨g, hg, hnode, ?_⟩
  rw [hcell]
  change (S.σ ^ k) '' (g.birthFrame '' (S.σ.symm '' F)) = T '' F
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro x _
  change (S.σ ^ k) (g.birthFrame (S.σ.symm x)) = T x
  rw [birth_ascent_top_step3_birth_frame g k hgj.le, hg, hnode]
  change Q.frame ((S.σ ^ (n + 1)) (S.σ.symm x)) = Q.frame ((S.σ ^ n) x)
  rw [pow_succ]
  simp

/-- Step 5 of the V4 proof of `birth_ascent_top` (V4 1.25):
"`e` has a finite first provider `g` ... and `e ⊆ g`".
A strict descendant has an immediate predecessor inside the given standard ancestor. -/
private theorem birth_ascent_top_step5_parent_within (A : S.ι) (k h b : ℕ) (N P : FramedNode S)
    (hN : S.IsStandardNode A k h N) (hP : S.IsStandardNode A k b P)
    (hNP : N.IsDescendant h P b) (hlt : h < b) :
    ∃ Q : FramedNode S, S.IsStandardNode A k (h + 1) Q ∧ Q.IsDescendant (h + 1) P b ∧
      ∃ i : S.I Q.ty, N = Q.child h i := by
  have hbk : b ≤ k := by obtain ⟨j, hj, _⟩ := hP; omega
  obtain ⟨Q, hQ, hNQ⟩ := birth_ascent_top_step3_standard_raise A k h (h + 1) N hN (by omega) (by omega)
  have hQP := birth_ascent_top_step3_common_desc_compare A k (h + 1) b h Q P N hQ hP hNQ hNP (by omega)
  obtain ⟨r, hr, w, hw⟩ := hNQ
  have hrone : r = 1 := by omega
  subst r
  refine ⟨Q, hQ, hQP, w.1, ?_⟩
  simpa [SubstSystem.descendantNode, FramedNode.child, FramedNode.move] using hw

/-- Step 5 of the V4 proof of `birth_ascent_top` (V4 1.25):
"`e` has a finite first provider `g` ... and `e ⊆ g`".
Ascend through boundary facets until the first internal facet. Facet dichotomy and the finite ancestor distance ensure termination. -/
private theorem birth_ascent_top_step5_finite_provider (A : S.ι) (k b : ℕ) (P : FramedNode S)
    (hP : S.IsStandardNode A k b P) (h : ℕ) (N : FramedNode S)
    (hN : S.IsStandardNode A k h N) (hNP : N.IsDescendant h P b)
    (e : FacetName S N.ty)
    (hint : relint (N.cell h e.val) ⊆ interior (P.carrier b)) :
    ∃ g : PrimitiveFacet S A, g.depth < k ∧ h < k - g.depth ∧
      N.IsDescendant h (g.birthNode k) (k - g.depth) ∧
      N.cell h e.val ⊆ (S.σ ^ k) '' g.carrier := by
  have aux : ∀ r h : ℕ, b = h + r → ∀ N : FramedNode S,
      S.IsStandardNode A k h N → N.IsDescendant h P b →
      ∀ e : FacetName S N.ty, relint (N.cell h e.val) ⊆ interior (P.carrier b) →
      ∃ g : PrimitiveFacet S A, g.depth < k ∧ h < k - g.depth ∧
        N.IsDescendant h (g.birthNode k) (k - g.depth) ∧
        N.cell h e.val ⊆ (S.σ ^ k) '' g.carrier := by
    intro r
    induction r with
    | zero =>
      intro h hb N hN hNP e hint
      have hbh : b = h := by omega
      subst b
      obtain ⟨r, hr, w, hw⟩ := hNP
      have hr0 : r = 0 := by omega
      subst r
      have hNP : N = P := by simpa [SubstSystem.descendantNode, FramedNode.move] using hw
      subst N
      obtain ⟨x, hx⟩ := birth_ascent_top_step5_cell_relint_nonempty P h e.val
      exact False.elim ((birth_ascent_top_step2_cell_front P h e.val (Finset.mem_filter.mp e.property).1
        (intrinsicInterior_subset hx)).2 (hint hx))
    | succ r ih =>
      intro h hb N hN hNP e hint
      obtain ⟨Q, hQ, hQP, i, rfl⟩ := birth_ascent_top_step5_parent_within A k h b N P hN hP hNP (by omega)
      rcases facet_dichotomy Q (Q.child h i) (h + 1) h (birth_ascent_top_step2_child_desc Q h i) e with hboundary | hinternal
      · obtain ⟨F, hF, -⟩ := hboundary
        have hFint : relint (Q.cell (h + 1) F.val) ⊆ interior (P.carrier b) := by
          rcases facet_dichotomy P Q b (h + 1) hQP F with hboundary' | hinternal'
          · obtain ⟨F₀, hF₀, -⟩ := hboundary'
            obtain ⟨x, hx⟩ := birth_ascent_top_step5_cell_relint_nonempty (Q.child h i) h e.val
            exact False.elim ((birth_ascent_top_step2_cell_front P b F₀.val (Finset.mem_filter.mp F₀.property).1
              (hF₀ (hF (intrinsicInterior_subset hx)))).2 (hint hx))
          · exact hinternal'
        obtain ⟨g, hg, hheight, hQg, hFg⟩ := ih (h + 1) (by omega) Q hQ hQP F hFint
        exact ⟨g, hg, by omega, birth_ascent_top_step3_desc_trans _ _ _ h (h + 1) (k - g.depth)
          (birth_ascent_top_step2_child_desc Q h i) hQg, hF.trans hFg⟩
      · obtain ⟨g, hg, hnode, hcell⟩ := birth_ascent_top_step5_primitive_from_child A k h Q hQ i e hinternal
        refine ⟨g, by omega, by omega, ?_, ?_⟩
        · rw [hg, hnode]
          exact birth_ascent_top_step2_child_desc Q h i
        · rw [hcell]
  have hNP' := hNP
  obtain ⟨r, hr, _⟩ := hNP'
  exact aux r h hr N hN hNP e hint

/-- Step 5 of the V4 proof of `birth_ascent_top` (V4 1.25): "`e` has a
finite first provider `g` with birth parent `P_{b'}`, `b < b' ≤` height of
`P₀`, and `e ⊆ g`". This is the finite provider construction for a boundary
facet internal to a specified standard ancestor; no vertex or port is asserted. -/
private theorem birth_ascent_top_step5_provider {A : S.ι} (k b : ℕ)
    (P : FramedNode S) (hP : S.IsStandardNode A k b P)
    (f : PrimitiveFacet S A) (hf : f.depth < k)
    (hancestor : (f.birthNode k).IsDescendant (k - f.depth) P b)
    (e : FacetName S f.birthType)
    (he : relint ((S.σ ^ k) '' f.birthCell e.val) ⊆ interior (P.carrier b)) :
    ∃ g : PrimitiveFacet S A, g.depth < f.depth ∧
      (f.birthNode k).IsDescendant (k - f.depth) (g.birthNode k) (k - g.depth) ∧
      f.birthCell e.val ⊆ g.carrier := by
  let N : FramedNode S := ⟨f.birthType, (f.birthNode k).frame⟩
  have hN : N = f.birthNode k := by
    apply FramedNode.ext
    · exact (birth_ascent_top_step2_descendant_type A (k - f.depth) f.depth f.word).symm
    · rfl
  have hstd : S.IsStandardNode A k (k - f.depth) N := by
    rw [hN]
    exact ⟨f.depth, by omega, f.word, rfl⟩
  have hcell : N.cell (k - f.depth) e.val = (S.σ ^ k) '' f.birthCell e.val := by
    change N.prototypeFrame (k - f.depth) '' e.val.carrier =
      (S.σ ^ k) '' (f.birthFrame '' e.val.carrier)
    rw [Set.image_image]
    apply Set.image_congr
    intro x _
    rw [hN]
    exact (birth_ascent_top_step3_birth_frame f k hf.le x).symm
  obtain ⟨g, hg, hheight, hNg, hsub⟩ := birth_ascent_top_step5_finite_provider A k b P hP (k - f.depth) N hstd
    (hN.symm ▸ hancestor) e (by rwa [hcell])
  refine ⟨g, by omega, hN ▸ hNg, ?_⟩
  rw [hcell] at hsub
  exact (Set.image_subset_image_iff (S.σ ^ k).injective).mp hsub

/-- Step 6 of the V4 proof of `birth_ascent_top` (V4 1.25): "let `q` be a
vertex of `mc_C(p)` ... `q` is common-listed" and "at least one child
containing `q` has a facet piece inside `e`". The hypothesis is precisely a
nonempty intersection of the primitive facet with the birth-parent facet. -/
private theorem birth_ascent_top_step6_seed_port {A : S.ι}
    (f : PrimitiveFacet S A) (e : FacetName S f.birthType)
    (hmeet : (f.carrier ∩ f.birthCell e.val).Nonempty) :
    ∃ q : E d, f.IsVertex q ∧ q ∈ f.birthCell e.val ∧ f.CommonListed q ∧
      ∃ (i : S.I f.birthType) (c : FacetName S (S.child f.birthType i).ty),
        q ∈ f.childCell i c.val ∧ f.childCell i c.val ⊆ f.birthCell e.val := by
  obtain ⟨i, f₀, hF, hint⟩ := f.realization
  let P : FramedNode S := ⟨f.birthType, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hfcell : (P.child 0 i).cell 0 f₀.val = f.localCarrier := by
    rw [birth_ascent_top_step2_child_cell_zero]; exact hF.symm
  have hpcell : P.cell 1 e.val = S.σ '' e.val.carrier := by
    simp [P, FramedNode.cell, FramedNode.prototypeFrame]
  have hmeet' : ((P.child 0 i).cell 0 f₀.val ∩ P.cell 1 e.val).Nonempty := by
    rw [hfcell, hpcell]
    obtain ⟨p, ⟨a, ⟨q, hq, hqa⟩, hap⟩, ⟨z, hz, hzp⟩⟩ := hmeet
    have hqz : S.σ.symm q = z := hqa.trans (f.birthFrame.injective (hap.trans hzp.symm))
    exact ⟨q, hq, z, hz, (congrArg S.σ hqz).symm.trans (S.σ.apply_symm_apply q)⟩
  have hint' : relint ((P.child 0 i).cell 0 f₀.val) ⊆ interior (P.carrier 1) := by
    rw [hfcell]
    simpa [P, FramedNode.carrier, placedSet] using hint
  obtain ⟨q, hqf, hqe, hqi, hall, j, c, hqc, hce⟩ :=
    birth_ascent_top_step6_parent_seed_port P 0 i f₀ e hint' hmeet'
  rw [hfcell] at hqf
  have hqe' : S.σ.symm q ∈ e.val.carrier := by
    rw [hpcell] at hqe
    obtain ⟨z, hz, rfl⟩ := hqe
    simpa using hz
  have hlists : f.ChildLists i (f.birthFrame (S.σ.symm q)) := by
    obtain ⟨v, hv, hqv⟩ := hqi
    rw [birth_ascent_top_step2_child_cell_zero] at hqv
    exact ⟨v, hv, S.σ.symm q, ⟨q, hqv, rfl⟩, rfl⟩
  refine ⟨f.birthFrame (S.σ.symm q), ⟨?_, i, f₀, hF, hlists⟩,
    ⟨S.σ.symm q, hqe', rfl⟩, ?_, j, c, ?_, ?_⟩
  · exact ⟨S.σ.symm q, ⟨q, hqf, rfl⟩, rfl⟩
  · apply birth_ascent_top_step2_local_common f q
    intro l hql
    obtain ⟨v, hv, hqv⟩ := hall l (by simpa [P, birth_ascent_top_step2_child_support_zero] using hql)
    rw [birth_ascent_top_step2_child_cell_zero] at hqv
    exact ⟨v, hv, hqv⟩
  · rw [birth_ascent_top_step2_child_cell_zero] at hqc
    exact ⟨S.σ.symm q, ⟨q, hqc, rfl⟩, rfl⟩
  · rintro z ⟨a, ⟨b, hb, hba⟩, haz⟩
    have hbe : b ∈ S.σ '' e.val.carrier := by
      rw [← hpcell]
      exact hce (by simpa [P, birth_ascent_top_step2_child_cell_zero] using hb)
    obtain ⟨x, hx, hxb⟩ := hbe
    refine ⟨x, hx, ?_⟩
    have hxa : x = a := (S.σ.symm_apply_apply x).symm.trans ((congrArg S.σ.symm hxb).trans hba)
    exact congrArg f.birthFrame hxa |>.trans haz

/-- Step 7 of the V4 proof of `birth_ascent_top` (V4 1.25): "`g` meets
`E` at `p ∈ f ⊆ E`, so `g ∈ E_A` by component closure". The exit facet,
its provider, and its common-listed facing port give one directed ascent. -/
private theorem birth_ascent_top_step7_one_ascent (A : S.ι) (k : ℕ)
    (E₀ : Set (E d)) (hE : IsSkeletonComponent S A k E₀) (p : E d)
    (b : ℕ) (P : FramedNode S) (hP : IsTopBirth A k p b P)
    (f : PrimitiveFacet S A) (hf : f ∈ principalFacets S A k E₀)
    (hp : p ∈ f.carrier) (hnot : f ∉ topClass A k E₀ p b P) :
    ∃ g ∈ principalFacets S A k E₀, p ∈ g.carrier ∧ AscentLink k f g := by
  have hancestor := birth_ascent_top_step3_birth_below_top k p b P hP f hf.1 hp
  have hstrict : k - f.depth < b := by
    obtain ⟨r, hr, w, hw⟩ := hancestor
    by_cases hzero : r = 0
    · subst r
      have heq : b = k - f.depth := by omega
      have hnode : f.birthNode k = P := by
        simpa [SubstSystem.descendantNode, FramedNode.move] using hw
      exact False.elim (hnot ⟨hf, hp, heq.symm, hnode⟩)
    · omega
  obtain ⟨e, hpe, he⟩ :=
    birth_ascent_top_step4_exit_facet k p b P hP f hf.1 hp hancestor hstrict
  obtain ⟨g, hdepth, hfg, heg⟩ :=
    birth_ascent_top_step5_provider k b P hP.1 f hf.1 hancestor e he
  have hpE : p ∈ E₀ := (principalFacets_spec A k E₀ hE).2.1 f hf hp
  exact ⟨g, ⟨hdepth.trans hf.1, p, heg hpe, hpE⟩, heg hpe,
    hdepth, hfg, e, heg, birth_ascent_top_step6_seed_port f e ⟨p, hp, hpe⟩⟩

/-- Step 8 of the V4 proof of `birth_ascent_top` (V4 1.25): "Birth height
strictly increases ... so at most `k` steps". Induction on the starting depth
constructs a route of strict ascents and proves the stronger bound by that depth. -/
private theorem birth_ascent_top_step8_routes {A : S.ι} (k : ℕ)
    (Q T : Set (PrimitiveFacet S A)) (p : E d)
    (hstep : ∀ f ∈ Q, p ∈ f.carrier → f ∉ T →
      ∃ g ∈ Q, p ∈ g.carrier ∧ AscentLink k f g)
    (u : PrimitiveFacet S A) (hu : u ∈ Q) (hpu : p ∈ u.carrier) :
    ∃ (v : PrimitiveFacet S A) (path : List (PrimitiveFacet S A)),
      v ∈ T ∧ path.head? = some u ∧ path.getLast? = some v ∧
      (∀ z ∈ path, z ∈ Q ∧ p ∈ z.carrier) ∧
      path.IsChain (fun a c => SameParentLink a c ∨ AscentLink k a c) ∧
      routeAscents k path ≤ u.depth := by
  classical
  have hroute : ∀ n : ℕ, ∀ u : PrimitiveFacet S A, u.depth = n →
      u ∈ Q → p ∈ u.carrier →
      ∃ (v : PrimitiveFacet S A) (path : List (PrimitiveFacet S A)),
        v ∈ T ∧ path.head? = some u ∧ path.getLast? = some v ∧
        (∀ z ∈ path, z ∈ Q ∧ p ∈ z.carrier) ∧
        path.IsChain (fun a c => SameParentLink a c ∨ AscentLink k a c) ∧
        routeAscents k path ≤ u.depth := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hun hu hpu
      by_cases hut : u ∈ T
      · refine ⟨u, [u], hut, rfl, rfl, ?_, by simp, ?_⟩
        · simpa using And.intro hu hpu
        · simp [routeAscents]
      · obtain ⟨g, hg, hpg, hlink⟩ := hstep u hu hpu hut
        obtain ⟨v, path, hv, hhead, hlast, hmem, hchain, hbound⟩ :=
          ih g.depth (hun ▸ hlink.1) g rfl hg hpg
        cases path with
        | nil => simp at hhead
        | cons a tail =>
          have hag : a = g := by simpa using hhead
          subst a
          refine ⟨v, u :: g :: tail, hv, rfl, ?_, ?_, ?_, ?_⟩
          · simpa using hlast
          · intro z hz
            rcases List.mem_cons.mp hz with rfl | hz
            · exact ⟨hu, hpu⟩
            · exact hmem z hz
          · exact List.isChain_cons_cons.mpr ⟨Or.inr hlink, hchain⟩
          · have hcount : routeAscents k (u :: g :: tail) =
                routeAscents k (g :: tail) + 1 := by
              simp [routeAscents, hlink]
            rw [hcount]
            have hdepth := hlink.1
            omega
  exact hroute u.depth u rfl hu hpu

/-- P21, V4 1.25 (moreover): from every facet through `p`, an upward route
reaches the nonempty top class with at most `k` ascents. The top class itself is
connected by same-parent links. Two distinct facets ensure a positive birth height. -/
theorem birth_ascent_top (A : S.ι) (k : ℕ) (E₀ : Set (E d))
    (hE : IsSkeletonComponent S A k E₀) (p : E d)
    (f g : PrimitiveFacet S A) (hfg : f ≠ g)
    (hf : f ∈ principalFacets S A k E₀) (hg : g ∈ principalFacets S A k E₀)
    (hpf : p ∈ f.carrier) (hpg : p ∈ g.carrier) :
    ∃ (b : ℕ) (P : FramedNode S), 1 ≤ b ∧ b ≤ k ∧ IsTopBirth A k p b P ∧
      (topClass A k E₀ p b P).Nonempty ∧
      (∀ u ∈ topClass A k E₀ p b P, ∀ v ∈ topClass A k E₀ p b P,
        Relation.ReflTransGen (ThroughLink (topClass A k E₀ p b P) p SameParentLink)
          u v) ∧
      ∀ u ∈ principalFacets S A k E₀, p ∈ u.carrier →
        ∃ (v : PrimitiveFacet S A) (path : List (PrimitiveFacet S A)),
          v ∈ topClass A k E₀ p b P ∧ path.head? = some u ∧
          path.getLast? = some v ∧
          (∀ z ∈ path, z ∈ principalFacets S A k E₀ ∧ p ∈ z.carrier) ∧
          path.IsChain (fun a c => SameParentLink a c ∨ AscentLink k a c) ∧
          routeAscents k path ≤ k := by
  obtain ⟨b, P, hbk, hP⟩ := birth_ascent_top_step1_least_height A k p
  have hpos : 1 ≤ b := by
    obtain ⟨r, hr, -⟩ := birth_ascent_top_step3_birth_below_top k p b P hP f hf.1 hpf
    have hdepth := hf.1
    omega
  have hroutes := birth_ascent_top_step8_routes k (principalFacets S A k E₀)
    (topClass A k E₀ p b P) p (birth_ascent_top_step7_one_ascent A k E₀ hE p b P hP)
  obtain ⟨v, _, hv, _⟩ := hroutes f hf hpf
  refine ⟨b, P, hpos, hbk, hP, ⟨v, hv⟩, ?_, ?_⟩
  · intro u hu v hv
    apply Relation.ReflTransGen.single
    refine ⟨hu, hu.2.1, hv, hv.2.1, ?_⟩
    exact birth_ascent_top_step2_same_parent k u v hu.1.1 hv.1.1
      (hu.2.2.1.trans hv.2.2.1.symm) (hu.2.2.2.trans hv.2.2.2.symm)
      ⟨p, hu.2.1, hv.2.1⟩
  · intro u hu hpu
    obtain ⟨v, path, hv, hhead, hlast, hmem, hchain, hbound⟩ := hroutes u hu hpu
    exact ⟨v, path, hv, hhead, hlast, hmem, hchain, hbound.trans (Nat.le_of_lt hu.1)⟩

/-- P22, V4 8.3: a role word follows the unique child at every step. -/
def OnlyChildWord (S : SubstSystem d) :
    (A : S.ι) → (n : ℕ) → S.RoleWord A n → Prop
  | _, 0, _ => True
  | A, n + 1, w => Fintype.card (S.I A) = 1 ∧
      OnlyChildWord S (S.child A w.1).ty n w.2

/-- P22, V4 8.3: first branching address, uniquely determined by the one-child
run. Existence and the bound are supplied by stage-1 C3, V4 1.28. -/
theorem firstBranching_exists_unique (A : S.ι) :
    ∃! a : Σ n : ℕ, S.RoleWord A n,
      OnlyChildWord S A a.1 a.2 ∧
        2 ≤ Fintype.card (S.I (S.nativeTile A a.1 a.2).ty) ∧
        a.1 ≤ Fintype.card S.ι - 1 := by
  sorry

/-- P22, V4 8.3: the actual first branching address, without an arbitrary
branching-descendant choice. -/
def firstBranching (A : S.ι) : Σ n : ℕ, S.RoleWord A n :=
  Classical.choose (firstBranching_exists_unique A)

/-- P22, V4 8.3: characterization and depth bound of the first branching node. -/
theorem firstBranching_spec (A : S.ι) :
    OnlyChildWord S A (firstBranching A).1 (firstBranching A).2 ∧
      2 ≤ Fintype.card (S.I (S.nativeTile A (firstBranching A).1
        (firstBranching A).2).ty) ∧
      (firstBranching A).1 ≤ Fintype.card S.ι - 1 :=
  (Classical.choose_spec (firstBranching_exists_unique A)).1

/-- P22, V4 8.3: `F(A)`, all first-generation internal facets at the first
branching descendant, including their positions and complete role words relative to A. -/
def firstBranchingFacets (A : S.ι) : Set (PrimitiveFacet S A) :=
  {f | f.birthAddress = firstBranching A}

/-- P22, V4 8.3: the first branching descendant has an internal facet.
This explicit nonemptiness prevents a vacuous required-list construction. -/
theorem firstBranchingFacets_nonempty (A : S.ι) :
    (firstBranchingFacets A).Nonempty := by
  sorry

/-- P22, V4 8.3: placement of the child's first branching address in the parent.
The initial role is retained, so different child occurrences stay distinguished. -/
def childFirstBranchingAddress (A : S.ι) (i : S.I A) : Σ n : ℕ, S.RoleWord A n :=
  ⟨(firstBranching (S.child A i).ty).1 + 1, ⟨i, (firstBranching (S.child A i).ty).2⟩⟩

/-- P22, V4 8.3: the three required families as a set of positioned primitive
facets: first generation, `F(A)`, and `iF(A_i)` for every child role. -/
def requiredSet (A : S.ι) : Set (PrimitiveFacet S A) :=
  {f | f.depth = 0 ∨ f ∈ firstBranchingFacets A ∨
    ∃ i : S.I A, f.birthAddress = childFirstBranchingAddress A i}

/-- P22, V4 8.3: the required set is finite and every required facet has birth
depth at most `p+1`, where `p = |T|-1`. -/
theorem requiredSet_finite (A : S.ι) :
    (requiredSet A).Finite ∧
      ∀ f ∈ requiredSet A, f.depth ≤ (Fintype.card S.ι - 1) + 1 := by
  have H : ∀ f ∈ requiredSet A, f.depth ≤ (Fintype.card S.ι - 1) + 1 := by
    intro f hf
    rcases hf with h0 | h1 | h2
    · rw [h0]
      exact Nat.zero_le _
    · have h_addr : f.birthAddress = firstBranching A := h1
      have h_depth : f.depth = (firstBranching A).1 := congrArg Sigma.fst h_addr
      have h_spec := firstBranching_spec A
      have h_card : 1 ≤ Fintype.card S.ι := Fintype.card_pos_iff.mpr ⟨A⟩
      omega
    · rcases h2 with ⟨i, hi⟩
      have h_depth : f.depth = (firstBranching (S.child A i).ty).1 + 1 := congrArg Sigma.fst hi
      have h_spec := firstBranching_spec (S.child A i).ty
      have h_card : 1 ≤ Fintype.card S.ι := Fintype.card_pos_iff.mpr ⟨A⟩
      omega
  refine ⟨?_, H⟩
  have H2 : requiredSet A ⊆ {f | f.depth < (Fintype.card S.ι - 1) + 2} := by
    intro f hf
    have := H f hf
    have : f.depth < Fintype.card S.ι - 1 + 2 := by omega
    exact this

  exact Set.Finite.subset (primitiveFacets_finite S A _) H2


/-- P22, V4 8.3: the actual finite required list `Req′(A)`.
No selected site arm and no propagation of a selected arm through placeholders occurs. -/
def required_list (A : S.ι) : Finset (PrimitiveFacet S A) :=
  (requiredSet_finite A).1.toFinset

/-- P22, V4 8.3: exact membership specification of `Req′(A)`. -/
theorem mem_required_list (A : S.ι) (f : PrimitiveFacet S A) :
    f ∈ required_list A ↔ f.depth = 0 ∨ f ∈ firstBranchingFacets A ∨
      ∃ i : S.I A, f.birthAddress = childFirstBranchingAddress A i := by
  simp only [required_list, Set.Finite.mem_toFinset, requiredSet, Set.mem_setOf_eq]

/-- P22/P20, V4 8.3, 1.24: the replacement list fits a principal component
at any prescribed lower bound on `k`. Existence uses the nonempty `F(A)`. -/
theorem required_principal_component (A : S.ι) (k₀ : ℕ) :
    ∃ k : ℕ, k₀ ≤ k ∧ ∃ E₀ : Set (E d), IsSkeletonComponent S A k E₀ ∧
      ∀ f ∈ required_list A, f ∈ principalFacets S A k E₀ := by
  let r := max ((Fintype.card S.ι - 1) + 2) (k₀ + 1)
  have h_bound : ∀ f ∈ required_list A, f.depth < r := by
    intro f hf
    have h_depth : f.depth ≤ (Fintype.card S.ι - 1) + 1 := by
      have H := (requiredSet_finite A).2 f (by simpa [required_list] using hf)
      exact H
    omega
  obtain ⟨k, hk_r, hk_pos, E₀, hE₀, h_subset⟩ := principal_component A r (required_list A) h_bound
  use k
  refine ⟨by omega, E₀, hE₀, ?_⟩
  intro f hf
  have h_sub := h_subset f hf
  have H_nonempty : (f.carrier).Nonempty := by
    obtain ⟨i, e, h_loc, h_rel⟩ := f.realization
    have he : (e.val.carrier).Nonempty := e.val.flat.relint_nonempty.mono intrinsicInterior_subset
    have h1 : (f.localCarrier).Nonempty := by
      rw [h_loc, placedSet]
      exact he.image _
    have h2 : (f.carrier).Nonempty := by
      change (f.birthFrame '' (S.σ.symm '' f.localCarrier)).Nonempty
      exact (h1.image _).image _
    exact h2
  have H_inter : (f.carrier ∩ E₀).Nonempty := H_nonempty.mono (Set.subset_inter_iff.mpr ⟨Set.Subset.refl _, h_sub⟩)
  have h_k_depth : f.depth < k := by
    have h_depth : f.depth ≤ (Fintype.card S.ι - 1) + 1 := (requiredSet_finite A).2 f (by simpa [required_list] using hf)
    have hr : r = max ((Fintype.card S.ι - 1) + 2) (k₀ + 1) := rfl
    omega
  exact ⟨h_k_depth, H_inter⟩

/-- P19, V4 1.24: normalized skeletons increase under further subdivision. -/
theorem internalSkeleton_mono (A : S.ι) (k l : ℕ) (hkl : k ≤ l) :
    internalSkeleton S A k ⊆ internalSkeleton S A l := by
  rw [internalSkeleton_eq_primitives, internalSkeleton_eq_primitives]
  intro x hx
  simp only [Set.mem_iUnion, Subtype.exists] at hx ⊢
  rcases hx with ⟨f, hfk, hx⟩
  exact ⟨f, lt_of_lt_of_le hfk hkl, hx⟩

/-- P19/P21, V4 1.24--1.25: the normalized birth frame is exactly the full
prototype frame of the actual standard birth node pulled back by `σ⁻ᵏ`. -/
theorem PrimitiveFacet.birthFrame_spec {A : S.ι} (f : PrimitiveFacet S A)
    (k : ℕ) (hf : f.depth ≤ k) :
    (f.birthNode k).ty = f.birthType ∧
      ((f.birthNode k).prototypeFrame (k - f.depth)).trans
        (S.σ ^ k).symm.toAffineEquiv = f.birthFrame := by
  sorry

/-- P21, V4 1.25: meeting first-generation facets of one birth node always
have the common-listed vertex needed for a same-parent link. -/
theorem sameParent_seed {A : S.ι} (f g : PrimitiveFacet S A)
    (hparent : f.birthAddress = g.birthAddress)
    (hmeet : (f.carrier ∩ g.carrier).Nonempty) : SameParentLink f g := by
  sorry

/-- P21, V4 1.25: each same-parent intersection is a union of cells common
to the owning child complexes; at every point one can name such a minimal cell. -/
theorem sameParent_intersection_cells {A : S.ι} (f g : PrimitiveFacet S A)
    (hparent : f.birthAddress = g.birthAddress) (p : E d)
    (hp : p ∈ f.carrier ∩ g.carrier) :
    ∃ (i : S.I f.birthType) (e : CellName S (S.child f.birthType i).ty),
      p ∈ relint (f.childCell i e.val) ∧ f.childCell i e.val ⊆ f.carrier ∩ g.carrier := by
  sorry

/-- P21, V4 1.25: a directed ascent strictly increases the actual birth height. -/
theorem AscentLink.birthHeight_lt {A : S.ι} (k : ℕ) (f g : PrimitiveFacet S A)
    (hf : f.depth < k) (hlink : AscentLink k f g) : k - f.depth < k - g.depth := by
  have hdepth := hlink.1
  omega

/-- P22, V4 8.3: first branching occurs at depth zero precisely when the
original type already has at least two children. -/
theorem firstBranching_zero_iff (A : S.ι) :
    (firstBranching A).1 = 0 ↔ 2 ≤ Fintype.card (S.I A) := by
  have h := firstBranching_spec A
  revert h
  generalize firstBranching A = a
  obtain ⟨n, w⟩ := a
  cases n with
  | zero =>
    intro h
    exact ⟨fun _ => h.2.1, fun _ => rfl⟩
  | succ m =>
    intro h
    have h1 : Fintype.card (S.I A) = 1 := h.1.1
    constructor
    · intro h0
      exact absurd h0 (Nat.succ_ne_zero m)
    · intro h2
      omega

/-- P22, V4 8.3: the replacement required list is never empty for an actual type. -/
theorem required_list_nonempty (A : S.ι) : (required_list A).Nonempty := by
  obtain ⟨f, hf⟩ := firstBranchingFacets_nonempty A
  refine ⟨f, (mem_required_list A f).mpr ?_⟩
  exact Or.inr (Or.inl hf)

/-- P22, V4 8.3: every child contributes its own positioned first-branching
facets to the parent's list, retaining the initial role of that child. -/
theorem required_child_firstBranching (A : S.ι) (i : S.I A) :
    ∃ f ∈ required_list A, f.birthAddress = childFirstBranchingAddress A i := by
  obtain ⟨f, hf⟩ := firstBranchingFacets_nonempty (S.child A i).ty
  let f' : PrimitiveFacet S A := {
    depth := f.depth + 1
    word := ⟨i, f.word⟩
    localCarrier := f.localCarrier
    realization := by
      obtain ⟨j, fac, h1, h2⟩ := f.realization
      use j, fac
      exact ⟨h1, h2⟩
  }
  use f'
  rw [mem_required_list]
  have hf_addr : f.birthAddress = firstBranching (S.child A i).ty := hf
  have hf_eq : (⟨f'.depth, f'.word⟩ : Σ n, S.RoleWord A n) = childFirstBranchingAddress A i := by
    dsimp [f', PrimitiveFacet.birthAddress, childFirstBranchingAddress]
    have : (⟨f.depth, f.word⟩ : Σ n, S.RoleWord (S.child A i).ty n) = firstBranching (S.child A i).ty := hf_addr
    revert this
    generalize hx : firstBranching (S.child A i).ty = x
    intro this
    cases this
    rfl
  constructor
  · exact Or.inr (Or.inr ⟨i, hf_eq⟩)
  · exact hf_eq

end Enforce
