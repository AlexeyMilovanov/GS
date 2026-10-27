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

/-- Step 7 of the V4 proof of `principal_component_step1_hull_geometry_step10_jordan_brouwer` (V4 1.24):
"a compact `(d-1)`-manifold". Triangulate a finite polyhedron compatibly with all
its convex pieces. Local Euclidean dimension makes every maximal simplex have
`d` vertices. No property of the ambient complement is requested. -/
private theorem principal_component_step1_hull_geometry_step10_jordan_brouwer_step7_pure_triangulation
    {Q : Set (E d)} (hQ : Polyhedron Q) (hman : IsLocallyEuclidean (d - 1) Q) :
    ∃ K : Geometry.SimplicialComplex ℝ (E d), K.faces.Finite ∧ K.space = Q ∧
      ∀ f ∈ K.facets, f.card = d := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
