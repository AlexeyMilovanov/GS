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
  sorry

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

/-- P20, V4 1.24: principal-component choices persist under further refinement. -/
theorem principal_component_refines (A : S.ι) (k l : ℕ) (hkl : k ≤ l)
    (E₀ : Set (E d)) (hE : IsSkeletonComponent S A k E₀) :
    ∃ E₁ : Set (E d), IsSkeletonComponent S A l E₁ ∧ E₀ ⊆ E₁ := by
  sorry

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

/-- P21, V4 1.25: primitive facets of the principal component through a common
point are connected by exactly the same-parent and ascent links. -/
theorem birth_ascent_routing (A : S.ι) (k : ℕ) (E₀ : Set (E d))
    (hE : IsSkeletonComponent S A k E₀) (p : E d)
    (f g : PrimitiveFacet S A) (hf : f ∈ principalFacets S A k E₀)
    (hg : g ∈ principalFacets S A k E₀) (hpf : p ∈ f.carrier) (hpg : p ∈ g.carrier) :
    Relation.ReflTransGen (ThroughLink (principalFacets S A k E₀) p (RoutingLink k))
      f g := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- P19, V4 1.24: normalized skeletons increase under further subdivision. -/
theorem internalSkeleton_mono (A : S.ι) (k l : ℕ) (hkl : k ≤ l) :
    internalSkeleton S A k ⊆ internalSkeleton S A l := by
  sorry

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
  sorry

/-- P22, V4 8.3: the replacement required list is never empty for an actual type. -/
theorem required_list_nonempty (A : S.ι) : (required_list A).Nonempty := by
  sorry

/-- P22, V4 8.3: every child contributes its own positioned first-branching
facets to the parent's list, retaining the initial role of that child. -/
theorem required_child_firstBranching (A : S.ι) (i : S.I A) :
    ∃ f ∈ required_list A, f.birthAddress = childFirstBranchingAddress A i := by
  sorry

end Enforce
