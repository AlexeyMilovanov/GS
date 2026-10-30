import Enforce.Parser.Host

/-!
# Assembly, forward states, the all-height hierarchy, and W4

R7--R13, V4 3.7--3.13 and 3.1, with the Req′ proof of V4 8.3.
A new parent first has geometry and old child states. Its state is then the
parent slot of a readable facet in the first child's first branching descendant.
Routing and the child equations are conclusions, never assumptions on that state.

The all-height theorem produces a single nested sequence of decoded levels,
and a coherent hierarchy on the exact native projection of Y. Its low levels
are exactly the inner nodes of the certificate base. Choices of levels, hierarchy
and states are made from that one theorem, preserving all correlations.

DEVIATION: the unnamed first child C₁ of Definition 3.9 is selected using
Classical.choice, since substitution roles are finite types without an order.
The readable facet is selected from Lemma 3.8. Lemma 3.10 states independence
of these choices by equality on every PRESENT parent slot in E_P.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d} {P : Params S}
variable {C : ClusterData S P}

namespace Parser

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ}

/-- R7, V4 3.7: the set of proposed parents, identifying repeated framed copies. -/
def proposedParents (D : DecodedLevel Y n) : Set (FramedNode S) :=
  {N | ∃ B : Block Y n, ∃ hB : B ∈ D.geometry.blocks, proposedParent D B hB = N}

/-- R7, V4 3.7: the complete geometric assembly assertion for a new level.
Its roots are exactly the proposed parents; all prescribed children have their
old decoded frames and first letters, so every child proposes that same parent. -/
structure AssemblyGeometry (D : DecodedLevel Y n) (G : GeometricLevel Y (n + 1)) : Prop where
  /-- R7, V4 3.7: no proposed parent is omitted and no extra root is introduced. -/
  roots_eq : G.roots = proposedParents D
  /-- R7, V4 3.7: every root has all prescribed children with the old first letters. -/
  children : ∀ N ∈ G.roots, Nonempty (AssembledParent D N)
  /-- R7, V4 3.7: every old root is a prescribed child of its proposed parent. -/
  old_child : ∀ (B : Block Y n) (hB : B ∈ D.geometry.blocks),
    ∃ i : S.I (proposedParent D B hB).ty,
      B.node = (proposedParent D B hB).child n i

end Parser

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "with the frames
prescribed by the substitution". Relative interiors commute with the full
affine prototype frame, including an anisotropic expansion. -/
private theorem assembly_step1_relint_image
    (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
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

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "the placed children
of σⁿ⁺¹ A_P". A child prototype frame factors through its unscaled placement. -/
private theorem assembly_step1_child_frame (N : FramedNode S) (n : ℕ)
    (i : S.I N.ty) :
    (N.child n i).prototypeFrame n =
      (S.child N.ty i).frame.toAffineEquiv.trans (N.prototypeFrame n) := by
  apply AffineEquiv.ext
  intro x
  change N.frame (S.placeChild n i ((S.σ ^ n) x)) =
    N.frame ((S.σ ^ n) ((S.child N.ty i).frame x))
  congr 1
  rw [S.placeChild_apply]
  simp [linearConj, Child.frame, rigidMotion, zpow_neg,
    LinearEquiv.mul_apply, ← map_add]

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "sharing a
first-generation facet". Normalize the placed facet by the parent's height-n frame. -/
private theorem assembly_step1_child_cell (N : FramedNode S) (n : ℕ)
    (i : S.I N.ty) (f : Cell d) :
    (N.child n i).cell n f = N.prototypeFrame n ''
      placedSet (S.child N.ty i).frame f.carrier := by
  rw [FramedNode.cell, assembly_step1_child_frame]
  simp only [placedSet, Set.image_image]
  rfl

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "int σ A_P is
connected". The parent carrier is the same affine image of the first substitution. -/
private theorem assembly_step1_parent_carrier (N : FramedNode S) (n : ℕ) :
    N.carrier (n + 1) = N.prototypeFrame n '' S.supertile 1 N.ty := by
  simp only [FramedNode.carrier, FramedNode.prototypeFrame, SubstSystem.supertile,
    placedSet, Set.image_image, pow_one]
  congr 1

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "children sharing
that facet". Every named placed boundary cell lies in its closed block carrier. -/
private theorem assembly_step1_cell_subset (N : FramedNode S) (n : ℕ)
    (f : CellName S N.ty) : N.cell n f.val ⊆ N.carrier n := by
  have hf : f.val.carrier ⊆ (S.proto N.ty).carrier := by
    have hrel : relint f.val.carrier ⊆ frontier (S.proto N.ty).carrier := by
      intro x hx
      rw [← (S.cx N.ty).cover]
      exact Set.mem_iUnion₂.mpr ⟨f.val, f.property, hx⟩
    have hcl := closure_mono hrel
    rw [f.val.flat.regularClosed, isClosed_frontier.closure_eq] at hcl
    exact hcl.trans (S.proto N.ty).compact.isClosed.frontier_subset
  change N.prototypeFrame n '' f.val.carrier ⊆ _
  have hcarrier : N.carrier n = N.prototypeFrame n '' (S.proto N.ty).carrier := by
    simp only [FramedNode.carrier, FramedNode.prototypeFrame, SubstSystem.supertile,
      placedSet, Set.image_image]
    rfl
  rw [hcarrier]
  exact Set.image_mono hf

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "relative interiors
of first-generation facets". A nonempty relative interior has positive
Hausdorff measure in its affine dimension. -/
private theorem assembly_step1_relint_measure (K : Set (E d))
    (hne : (relint K).Nonempty) :
    0 < (MeasureTheory.Measure.hausdorffMeasure
      (Module.finrank ℝ (affineSpan ℝ K).direction : ℝ)) K := by
  classical
  let A := affineSpan ℝ K
  obtain ⟨z, x, hx, rfl⟩ := hne
  letI : Nonempty A := ⟨x⟩
  let e := AffineIsometryEquiv.vaddConst ℝ x
  let U : Set A := interior ((↑) ⁻¹' K)
  let V : Set A.direction := e ⁻¹' U
  have hV : IsOpen V := isOpen_interior.preimage e.continuous
  have hVne : V.Nonempty := ⟨e.symm x, by simpa [V, U] using hx⟩
  letI : (MeasureTheory.Measure.hausdorffMeasure (Module.finrank ℝ A.direction : ℝ) :
      MeasureTheory.Measure A.direction).IsAddHaarMeasure :=
    MeasureTheory.isAddHaarMeasure_hausdorffMeasure
  have hpos : 0 < (MeasureTheory.Measure.hausdorffMeasure
      (Module.finrank ℝ A.direction : ℝ)) V := hV.measure_pos _ hVne
  have heV : e '' V = U := e.surjective.image_preimage U
  have hm := e.isometry.hausdorffMeasure_image
    (Or.inl (Nat.cast_nonneg (Module.finrank ℝ A.direction))) V
  rw [heV] at hm
  have hi : Isometry (Subtype.val : A → E d) := fun _ _ => rfl
  have hm' := hi.hausdorffMeasure_image
    (Or.inl (Nat.cast_nonneg (Module.finrank ℝ A.direction))) U
  have hsub : (Subtype.val '' U : Set (E d)) ⊆ K := by
    rintro y ⟨x, hx, rfl⟩
    exact interior_subset (s := (Subtype.val ⁻¹' K : Set A)) hx
  exact (hpos.trans_eq (hm'.trans hm).symm).trans_le (MeasureTheory.measure_mono hsub)

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "pairs sharing a
first-generation facet". A placed facet has strictly positive facet measure. -/
private theorem assembly_step1_facet_measure
    (N : FramedNode S) (n : ℕ) (f : FacetName S N.ty) :
    0 < MeasureTheory.Measure.hausdorffMeasure (d - 1 : ℝ) (N.cell n f.val) := by
  have hdim : Module.finrank ℝ (affineSpan ℝ (N.cell n f.val)).direction = d - 1 := by
    change Module.finrank ℝ
      (affineSpan ℝ ((N.prototypeFrame n).toAffineMap '' f.val.carrier)).direction = _
    rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
    exact ((N.prototypeFrame n).linear.finrank_map_eq _).trans
      (f.val.flat.dimension.trans (Finset.mem_filter.mp f.property).2)
  have hne : (relint (N.cell n f.val)).Nonempty := by
    rw [FramedNode.cell, assembly_step1_relint_image]
    exact f.val.flat.relint_nonempty.image _
  have h := assembly_step1_relint_measure _ hne
  have hd : 1 ≤ d := by have := (Fact.out : 2 ≤ d); omega
  simpa only [hdim, Nat.cast_sub hd, Nat.cast_one] using h

/-- Step 2 of the V4 proof of `assembly` (V4 3.7): "each neighbour
across a facet". Whole-facet pairing identifies the unique opposite child
among all prescribed children containing that facet. -/
private theorem assembly_step2_opposite_unique
    (N : FramedNode S) (n : ℕ) (i : S.I N.ty)
    (f : FacetName S (N.child n i).ty)
    (hint : (relint ((N.child n i).cell n f.val) ∩
      interior (N.carrier (n + 1))).Nonempty)
    (j k : S.I N.ty) (hji : j ≠ i) (hki : k ≠ i)
    (hj : (N.child n i).cell n f.val ⊆ (N.child n j).carrier n)
    (hk : (N.child n i).cell n f.val ⊆ (N.child n k).carrier n) : j = k := by
  obtain ⟨l, ⟨hli, g, hcell, hzero⟩, _⟩ := (internal_facet_pairing N n i f hint).2
  have hpos := assembly_step1_facet_measure (N.child n i) n f
  have howner (q : S.I N.ty) (hqi : q ≠ i)
      (hq : (N.child n i).cell n f.val ⊆ (N.child n q).carrier n) : q = l := by
    by_contra hql
    have hz := hzero q hqi hql
    rw [Set.inter_eq_right.mpr hq] at hz
    exact (ne_of_gt hpos) hz
  exact (howner j hji hj).trans (howner k hki hk).symm

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "pairs sharing a
first-generation facet". Edges retain both named facets and their internalness. -/
private def assembly_step1_adjacent (N : FramedNode S) (n : ℕ)
    (i j : S.I N.ty) : Prop :=
  i ≠ j ∧ ∃ (f : FacetName S (N.child n i).ty)
    (g : FacetName S (N.child n j).ty),
    (N.child n i).cell n f.val = (N.child n j).cell n g.val ∧
      relint ((N.child n i).cell n f.val) ⊆ interior (N.carrier (n + 1))

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "avoided by general
position". A proper affine subspace has dense complement. -/
private theorem assembly_step1_affine_dense (A : AffineSubspace ℝ (E d))
    (hA : A ≠ ⊤) : Dense (A : Set (E d))ᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have htop := A.convex.interior_nonempty_iff_affineSpan_eq_top.mp ⟨x, hx⟩
  rw [AffineSubspace.affineSpan_coe] at htop
  exact hA htop

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "dimension ≤ d-2".
An affine subspace of smaller dimension is proper. -/
private theorem assembly_step1_affine_proper (A : AffineSubspace ℝ (E d))
    (hA : Module.finrank ℝ A.direction < d) : A ≠ ⊤ := by
  intro heq
  rw [heq, AffineSubspace.direction_top, finrank_top,
    finrank_euclideanSpace, Fintype.card_fin] at hA
  exact (lt_irrefl d) hA

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "the lower-dimensional
cells ... avoided by general position". The complement of finitely many
proper affine subspaces is dense, also for an empty family. -/
private theorem assembly_step1_avoid_dense (L : Finset (AffineSubspace ℝ (E d)))
    (hL : ∀ A ∈ L, Module.finrank ℝ A.direction < d) :
    Dense (⋂ A ∈ L, (A : Set (E d))ᶜ) := by
  apply dense_biInter_of_isOpen
    (fun A _ => A.closed_of_finiteDimensional.isOpen_compl) L.finite_toSet.countable
  intro A hA
  exact assembly_step1_affine_dense A (assembly_step1_affine_proper A (hL A hA))

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "a generic path ...
crosses only relative interiors of first-generation facets". In an open
convex neighborhood, two segments through a generic point avoid all the
specified affine subspaces of codimension at least two. -/
private theorem assembly_step1_avoid_local (L : Finset (AffineSubspace ℝ (E d)))
    (hL : ∀ A ∈ L, Module.finrank ℝ A.direction + 1 < d)
    {V : Set (E d)} (hV : IsOpen V) (hconv : Convex ℝ V)
    {a b : E d} (haV : a ∈ V) (hbV : b ∈ V)
    (ha : a ∈ ⋂ A ∈ L, (A : Set (E d))ᶜ)
    (hb : b ∈ ⋂ A ∈ L, (A : Set (E d))ᶜ) :
    ∃ J : Set (E d), J ⊆ V ∩ (⋂ A ∈ L, (A : Set (E d))ᶜ) ∧
      a ∈ J ∧ b ∈ J ∧ IsPreconnected J := by
  classical
  have hspan (A : AffineSubspace ℝ (E d))
      (hA : Module.finrank ℝ A.direction + 1 < d) (x : E d) :
      Dense (affineSpan ℝ (insert x (A : Set (E d))) : Set (E d))ᶜ := by
    have hdim := finrank_vectorSpan_insert_le_set ℝ (A : Set (E d)) x
    have hAdim : Module.finrank ℝ (vectorSpan ℝ (A : Set (E d))) =
        Module.finrank ℝ A.direction := by
      rw [← direction_affineSpan, AffineSubspace.affineSpan_coe]
    rw [hAdim] at hdim
    apply assembly_step1_affine_dense
    apply assembly_step1_affine_proper
    rw [direction_affineSpan]
    omega
  have hsegment (A : AffineSubspace ℝ (E d)) {x z : E d}
      (hx : x ∉ A) (hz : z ∉ affineSpan ℝ (insert x (A : Set (E d)))) :
      Disjoint (segment ℝ x z) (A : Set (E d)) := by
    apply Set.disjoint_left.mpr
    intro q hq hqA
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    have ht0 : t ≠ 0 := by
      intro ht0
      subst t
      exact hx (by simpa using hqA)
    have hxA : x ∈ affineSpan ℝ (insert x (A : Set (E d))) :=
      mem_affineSpan ℝ (mem_insert x _)
    have hqA' : AffineMap.lineMap x z t ∈ affineSpan ℝ (insert x (A : Set (E d))) :=
      mem_affineSpan ℝ (mem_insert_of_mem _ hqA)
    have hzA := AffineMap.lineMap_mem t⁻¹ hxA hqA'
    rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ ht0,
      AffineMap.lineMap_apply_one] at hzA
    exact hz hzA
  have hdense (x : E d) : Dense (⋂ A ∈ L,
      (affineSpan ℝ (insert x (A : Set (E d))) : Set (E d))ᶜ) := by
    apply dense_biInter_of_isOpen
      (fun (A : AffineSubspace ℝ (E d)) _ =>
        (affineSpan ℝ (insert x (A : Set (E d)))).closed_of_finiteDimensional.isOpen_compl)
      L.finite_toSet.countable
    intro A hA
    exact hspan A (hL A hA) x
  have hopen (x : E d) : IsOpen (⋂ A ∈ L,
      (affineSpan ℝ (insert x (A : Set (E d))) : Set (E d))ᶜ) :=
    isOpen_biInter_finset fun A _ =>
      (affineSpan ℝ (insert x (A : Set (E d)))).closed_of_finiteDimensional.isOpen_compl
  obtain ⟨z, hzV, hz⟩ :=
    ((hdense a).inter_of_isOpen_left (hdense b) (hopen a)).inter_open_nonempty V hV ⟨a, haV⟩
  let J := segment ℝ a z ∪ segment ℝ b z
  have hJ (A : AffineSubspace ℝ (E d)) (hA : A ∈ L) : Disjoint J (A : Set (E d)) :=
    disjoint_union_left.mpr
      ⟨hsegment A (Set.mem_iInter₂.mp ha A hA) (Set.mem_iInter₂.mp hz.1 A hA),
        hsegment A (Set.mem_iInter₂.mp hb A hA) (Set.mem_iInter₂.mp hz.2 A hA)⟩
  refine ⟨J, ?_, Or.inl (left_mem_segment ℝ _ _),
    Or.inr (left_mem_segment ℝ _ _), ?_⟩
  · intro x hx
    refine ⟨(union_subset (hconv.segment_subset haV hzV)
      (hconv.segment_subset hbV hzV)) hx, ?_⟩
    exact Set.mem_iInter₂.mpr fun A hA => Set.disjoint_left.mp (hJ A hA) hx
  · exact IsPreconnected.union' ⟨z, right_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩
      (convex_segment (𝕜 := ℝ) a z).isPreconnected
      (convex_segment (𝕜 := ℝ) b z).isPreconnected

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "int σ A_P is
connected ... avoided by general position". Removing finitely many affine
subspaces of codimension at least two preserves connectedness of an open set.
The local two-segment construction makes each component's closure open in U. -/
private theorem assembly_step1_avoid_connected (L : Finset (AffineSubspace ℝ (E d)))
    (hL : ∀ A ∈ L, Module.finrank ℝ A.direction + 1 < d)
    {U : Set (E d)} (hU : IsOpen U) (hconn : IsPreconnected U) :
    IsPreconnected (U ∩ (⋂ A ∈ L, (A : Set (E d))ᶜ)) := by
  apply isPreconnected_of_forall_pair
  intro a ha b hb
  let G := ⋂ A ∈ L, (A : Set (E d))ᶜ
  let V := U ∩ G
  let H := connectedComponentIn V a
  have hdense : Dense G := assembly_step1_avoid_dense L (fun A hA => by
    have := hL A hA
    omega)
  have hV : IsOpen V := hU.inter
    (isOpen_biInter_finset fun A _ => A.closed_of_finiteDimensional.isOpen_compl)
  have hHV : H ⊆ V := connectedComponentIn_subset V a
  have haH : a ∈ H := mem_connectedComponentIn ha
  have hlocal (p : E d) (hpU : p ∈ U) (hpH : p ∈ closure H) :
      ∃ r : ℝ, 0 < r ∧ ball p r ⊆ U ∩ closure H := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU p hpU
    obtain ⟨q, hqball, hqH⟩ := mem_closure_iff.mp hpH (ball p r) isOpen_ball (mem_ball_self hr)
    have hgood : ball p r ∩ G ⊆ H := by
      rintro x ⟨hxball, hxG⟩
      obtain ⟨J, hJ, hqJ, hxJ, hJconn⟩ :=
        assembly_step1_avoid_local L hL isOpen_ball (convex_ball p r)
          hqball hxball (hHV hqH).2 hxG
      have hJV : J ⊆ V := fun y hy => ⟨hball (hJ hy).1, (hJ hy).2⟩
      have hJH : J ⊆ H := by
        change J ⊆ connectedComponentIn V a
        rw [connectedComponentIn_eq hqH]
        exact hJconn.subset_connectedComponentIn hqJ hJV
      exact hJH hxJ
    refine ⟨r, hr, fun x hx => ⟨hball hx, ?_⟩⟩
    apply _root_.mem_closure_iff.mpr
    intro O hO hxO
    obtain ⟨z, hz, hzG⟩ := hdense.inter_open_nonempty (ball p r ∩ O)
      (isOpen_ball.inter hO) ⟨x, hx, hxO⟩
    exact ⟨z, hz.2, hgood ⟨hz.1, hzG⟩⟩
  have hW : IsOpen (U ∩ closure H) := Metric.isOpen_iff.mpr fun p hp =>
    hlocal p hp.1 hp.2
  have hUW : U ⊆ U ∩ closure H := by
    apply hconn.subset_of_closure_inter_subset hW
      ⟨a, ha.1, ha.1, subset_closure haH⟩
    rintro p ⟨hp, hpU⟩
    refine ⟨hpU, ?_⟩
    have hc := closure_mono (show U ∩ closure H ⊆ closure H from inter_subset_right) hp
    simpa only [closure_closure] using hc
  have hbH : b ∈ H := by
    obtain ⟨z, hz, hzH⟩ := mem_closure_iff.mp (hUW hb.1).2
      (connectedComponentIn V b) hV.connectedComponentIn (mem_connectedComponentIn hb)
    have heq : H = connectedComponentIn V b :=
      (connectedComponentIn_eq hzH).trans (connectedComponentIn_eq hz).symm
    rw [heq]
    exact mem_connectedComponentIn hb
  exact ⟨H, hHV, haH, hbH, isPreconnected_connectedComponentIn⟩

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "placed children".
The closed carrier is the affine image of the prototype carrier. -/
private theorem assembly_step1_carrier_image (N : FramedNode S) (n : ℕ) :
    N.carrier n = N.prototypeFrame n '' (S.proto N.ty).carrier := by
  simp only [FramedNode.carrier, FramedNode.prototypeFrame, SubstSystem.supertile,
    placedSet, Set.image_image]
  rfl

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "int σ A_P is
connected". Placed nodes retain closedness, regular closedness and connected
nonempty interiors from their prototypes. -/
private theorem assembly_step1_node_regular (N : FramedNode S) (n : ℕ) :
    IsClosed (N.carrier n) ∧ IsRegularClosed (N.carrier n) ∧
      IsConnected (interior (N.carrier n)) := by
  let e := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  have hcar : N.carrier n = e '' (S.proto N.ty).carrier :=
    assembly_step1_carrier_image N n
  rw [hcar]
  refine ⟨((S.proto N.ty).compact.image e.continuous).isClosed, ?_, ?_⟩
  · change closure (interior (e '' (S.proto N.ty).carrier)) = _
    rw [← e.image_interior, ← e.image_closure, (S.proto N.ty).regularClosed]
  · rw [← e.image_interior]
    exact (S.proto N.ty).interior_connected.image e e.continuous.continuousOn

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "the children tile
it". Normalize each child carrier by the common parent frame. -/
private theorem assembly_step1_child_carrier (N : FramedNode S) (n : ℕ)
    (i : S.I N.ty) :
    (N.child n i).carrier n = N.prototypeFrame n ''
      placedSet (S.child N.ty i).frame (S.proto (S.child N.ty i).ty).carrier := by
  rw [assembly_step1_carrier_image, assembly_step1_child_frame]
  simp only [placedSet, Set.image_image]
  rfl

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "the children tile
it". The prescribed child carriers cover the placed parent exactly. -/
private theorem assembly_step1_children_cover (N : FramedNode S) (n : ℕ) :
    N.carrier (n + 1) = ⋃ i : S.I N.ty, (N.child n i).carrier n := by
  rw [assembly_step1_parent_carrier]
  change N.prototypeFrame n '' (S.σ '' (S.proto N.ty).carrier) = _
  rw [S.children_cover, Set.image_iUnion]
  apply Set.iUnion_congr
  intro i
  exact (assembly_step1_child_carrier N n i).symm

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "the children tile
it". Different prescribed roles have disjoint interiors at every height. -/
private theorem assembly_step1_children_disjoint (N : FramedNode S) (n : ℕ)
    (i j : S.I N.ty) (hij : i ≠ j) :
    Disjoint (interior ((N.child n i).carrier n))
      (interior ((N.child n j).carrier n)) := by
  let e := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  rw [assembly_step1_child_carrier, assembly_step1_child_carrier]
  change Disjoint
    (interior (e '' placedSet (S.child N.ty i).frame (S.proto (S.child N.ty i).ty).carrier))
    (interior (e '' placedSet (S.child N.ty j).frame (S.proto (S.child N.ty j).ty).carrier))
  rw [← e.image_interior, ← e.image_interior]
  exact Set.disjoint_image_of_injective e.injective (S.children_disjoint N.ty hij)

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "dimension ≤ d-2".
Placing a cell with the full affine frame preserves its affine dimension. -/
private theorem assembly_step1_cell_dimension (N : FramedNode S) (n : ℕ)
    (f : Cell d) :
    Module.finrank ℝ (affineSpan ℝ (N.cell n f)).direction = f.dim := by
  change Module.finrank ℝ
    (affineSpan ℝ ((N.prototypeFrame n).toAffineMap '' f.carrier)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  exact ((N.prototypeFrame n).linear.finrank_map_eq _).trans f.flat.dimension

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "each crossing
passing between two children sharing that facet". At an interior point of
the parent outside all lower-dimensional cells, any two owning children
share an internal named facet. -/
private theorem assembly_step1_common_point_edge (N : FramedNode S) (n : ℕ)
    (x : E d) (hx : x ∈ interior (N.carrier (n + 1)))
    (havoid : ∀ (k : S.I N.ty) (e : CellName S (N.child n k).ty),
      e.val.dim + 1 < d → x ∉ (N.child n k).cell n e.val)
    (i j : S.I N.ty) (hne : i ≠ j)
    (hxi : x ∈ (N.child n i).carrier n) (hxj : x ∈ (N.child n j).carrier n) :
    assembly_step1_adjacent N n i j := by
  have hfront (i j : S.I N.ty) (hne : i ≠ j)
      (hi : x ∈ (N.child n i).carrier n) (hj : x ∈ (N.child n j).carrier n) :
      x ∈ frontier ((N.child n i).carrier n) := by
    rw [(assembly_step1_node_regular (N.child n i) n).1.frontier_eq]
    refine ⟨hi, ?_⟩
    have hd := (assembly_step1_children_disjoint N n i j hne).closure_right isOpen_interior
    rw [(assembly_step1_node_regular (N.child n j) n).2.1] at hd
    exact fun hxint => Set.disjoint_left.mp hd hxint hj
  obtain ⟨e, he, _⟩ := placedMinimalCell_exists_unique (N.child n i) n x (hfront i j hne hxi hxj)
  obtain ⟨e', he', _⟩ := placedMinimalCell_exists_unique (N.child n j) n x (hfront j i hne.symm hxj hxi)
  have hdim (k : S.I N.ty) (e : CellName S (N.child n k).ty)
      (he : x ∈ relint ((N.child n k).cell n e.val)) : e.val.dim = d - 1 := by
    have hlt := (S.cx (N.child n k).ty).dim_lt e.val e.property
    have hnot : ¬ e.val.dim + 1 < d := fun h => havoid k e h (intrinsicInterior_subset he)
    omega
  let f : FacetName S (N.child n i).ty :=
    ⟨e.val, Finset.mem_filter.mpr ⟨e.property, hdim i e he⟩⟩
  let g : FacetName S (N.child n j).ty :=
    ⟨e'.val, Finset.mem_filter.mpr ⟨e'.property, hdim j e' he'⟩⟩
  exact ⟨hne, f, g, sibling_minimalCell_eq N n i j hne x e e' he he',
    (internal_facet_pairing N n i f ⟨x, he, hx⟩).1⟩

/-- Step 1 of the V4 proof of `assembly` (V4 3.7): "the dual graph of the
children of σ A_P ... is connected". This is solely a finite subdivision
statement; it includes the reflexive path for a one-child type. -/
private theorem assembly_step1_connected (N : FramedNode S) (n : ℕ)
    (i j : S.I N.ty) :
    Relation.ReflTransGen (assembly_step1_adjacent N n) i j := by
  classical
  let L : Finset (AffineSubspace ℝ (E d)) := Finset.univ.biUnion fun k : S.I N.ty =>
    ((S.cx (N.child n k).ty).cells.filter fun e => e.dim + 1 < d).image
      (fun e => affineSpan ℝ ((N.child n k).cell n e))
  have hL : ∀ A ∈ L, Module.finrank ℝ A.direction + 1 < d := by
    intro A hA
    obtain ⟨k, _, hA⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hA
    rw [assembly_step1_cell_dimension]
    exact (Finset.mem_filter.mp he).2
  let V := interior (N.carrier (n + 1)) ∩ (⋂ A ∈ L, (A : Set (E d))ᶜ)
  have hconn : IsPreconnected V := assembly_step1_avoid_connected L hL isOpen_interior
    (assembly_step1_node_regular N (n + 1)).2.2.isPreconnected
  have hdense := assembly_step1_avoid_dense L (fun A hA => by
    have := hL A hA
    omega)
  have hchild (k : S.I N.ty) : (N.child n k).carrier n ⊆ N.carrier (n + 1) := by
    rw [assembly_step1_children_cover]
    exact Set.subset_iUnion (fun q : S.I N.ty => (N.child n q).carrier n) k
  have hpoint (k : S.I N.ty) : ∃ x ∈ V, x ∈ (N.child n k).carrier n := by
    obtain ⟨x, hx, hxG⟩ := hdense.inter_open_nonempty (interior ((N.child n k).carrier n))
      isOpen_interior (assembly_step1_node_regular (N.child n k) n).2.2.nonempty
    exact ⟨x, ⟨interior_mono (hchild k) hx, hxG⟩, interior_subset hx⟩
  by_contra hnot
  let R := {k | Relation.ReflTransGen (assembly_step1_adjacent N n) i k}
  let K := ⋃ k ∈ R, (N.child n k).carrier n
  let K' := ⋃ k ∈ Rᶜ, (N.child n k).carrier n
  have hK : IsClosed K := R.toFinite.isClosed_biUnion
    (fun k _ => (assembly_step1_node_regular (N.child n k) n).1)
  have hK' : IsClosed K' := Rᶜ.toFinite.isClosed_biUnion
    (fun k _ => (assembly_step1_node_regular (N.child n k) n).1)
  have hcover : V ⊆ K ∪ K' := by
    intro x hx
    have hxN := interior_subset hx.1
    rw [assembly_step1_children_cover] at hxN
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxN
    by_cases hk : k ∈ R
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨k, hk, hxk⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨k, hk, hxk⟩)
  obtain ⟨x, hxV, hxi⟩ := hpoint i
  obtain ⟨y, hyV, hyj⟩ := hpoint j
  have hxK : x ∈ K := Set.mem_iUnion₂.mpr ⟨i, Relation.ReflTransGen.refl, hxi⟩
  have hyK' : y ∈ K' := Set.mem_iUnion₂.mpr ⟨j, hnot, hyj⟩
  obtain ⟨z, hzV, hzK, hzK'⟩ := (isPreconnected_closed_iff.mp hconn) K K' hK hK'
    hcover ⟨x, hxV, hxK⟩ ⟨y, hyV, hyK'⟩
  obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hzK
  obtain ⟨l, hl, hzl⟩ := Set.mem_iUnion₂.mp hzK'
  have hne : k ≠ l := by intro heq; subst l; exact hl hk
  have havoid (q : S.I N.ty) (e : CellName S (N.child n q).ty)
      (he : e.val.dim + 1 < d) : z ∉ (N.child n q).cell n e.val := by
    have hmem : affineSpan ℝ ((N.child n q).cell n e.val) ∈ L :=
      Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, Finset.mem_image.mpr
        ⟨e.val, Finset.mem_filter.mpr ⟨e.property, he⟩, rfl⟩⟩
    exact fun hz => (Set.mem_iInter₂.mp hzV.2 _ hmem) (mem_affineSpan ℝ hz)
  exact hl (hk.tail (assembly_step1_common_point_edge N n z hzV.1 havoid k l hne hzk hzl))

/-- Step 2 of the V4 proof of `assembly` (V4 3.7): "with that child in
that role and frame is unique". Cancelling the prescribed child isometry
recovers the entire proposed-parent frame. -/
private theorem assembly_step2_parent_frame
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (N : FramedNode S) (i : S.I N.ty)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks)
    (hnode : B.node = N.child n i) (hrole : firstRole D B hB = ⟨N.ty, i⟩) :
    proposedParent D B hB = N := by
  calc
    proposedParent D B hB =
        ⟨N.ty, (S.placeChild n i).symm.trans B.node.frame⟩ :=
      congrArg (fun q : S.Role => (⟨q.1,
        (S.placeChild n q.2).symm.trans B.node.frame⟩ : FramedNode S)) hrole
    _ = N := by
      rw [hnode]
      apply FramedNode.ext
      · rfl
      · simp [FramedNode.child, AffineIsometryEquiv.trans_assoc]

/-- Step 2 of the V4 proof of `assembly` (V4 3.7): "each neighbour
across a facet ... with first address letter equal to its role". The serving
role and the positioned opposite facet identify the opposite role uniquely. -/
private theorem assembly_step2_record_role
    (N : FramedNode S) (n : ℕ) (i j : S.I N.ty)
    (f : FacetName S (N.child n i).ty)
    (hint : (relint ((N.child n i).cell n f.val) ∩
      interior (N.carrier (n + 1))).Nonempty)
    (hji : j ≠ i) (hj : (N.child n i).cell n f.val ⊆ (N.child n j).carrier n)
    (r : FacetRecord P)
    (hrole : r.incidence.val.sideRole r.sideIndex = ⟨N.ty, i⟩)
    (hfacet : ((⟨r.incidence.val.ty, N.frame⟩ : FramedNode S).child n
      (r.incidence.val.sideIndex (!r.sideIndex))).cell n
        (r.incidence.val.sideFacet (!r.sideIndex)).val = (N.child n i).cell n f.val) :
    r.incidence.val.sideRole (!r.sideIndex) = ⟨N.ty, j⟩ := by
  rcases N with ⟨T, φ⟩
  have ht : r.incidence.val.ty = T := congrArg Sigma.fst hrole
  subst T
  have hi : r.incidence.val.sideIndex r.sideIndex = i := by
    simpa only [PrimitiveIncidence.sideRole, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hrole
  have hki : r.incidence.val.sideIndex (!r.sideIndex) ≠ i := by
    rw [← hi]
    cases hb : r.sideIndex <;>
      simp [PrimitiveIncidence.sideIndex, r.incidence.val.distinct,
        Ne.symm r.incidence.val.distinct]
  have hk : ((⟨r.incidence.val.ty, φ⟩ : FramedNode S).child n i).cell n f.val ⊆
      ((⟨r.incidence.val.ty, φ⟩ : FramedNode S).child n
        (r.incidence.val.sideIndex (!r.sideIndex))).carrier n := by
    rw [← hfacet]
    exact assembly_step1_cell_subset _ n
      ⟨(r.incidence.val.sideFacet (!r.sideIndex)).val,
        (Finset.mem_filter.mp (r.incidence.val.sideFacet (!r.sideIndex)).property).1⟩
  have hkj := assembly_step2_opposite_unique ⟨r.incidence.val.ty, φ⟩ n i f hint
    (r.incidence.val.sideIndex (!r.sideIndex)) j hki hji hk hj
  exact congrArg (fun q => (⟨r.incidence.val.ty, q⟩ : S.Role)) hkj

/-- Step 2 of the V4 proof of `assembly` (V4 3.7): "its age-one facets are
those internal to σ A_P by Corollary 2.4(a)". At one specified dual edge,
the record names exactly the opposite prescribed role and its full frame. -/
private theorem assembly_step2_neighbor_record
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (hD : Inv D) (N : FramedNode S)
    (i j : S.I N.ty) (hij : assembly_step1_adjacent N n i j)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks)
    (hnode : B.node = N.child n i) (hrole : firstRole D B hB = ⟨N.ty, i⟩) :
    ∃ (f : FacetName S B.node.ty) (a : Parser.AgeOneFacet D B hB f),
      proposedSibling D B hB f a = N.child n j ∧
        a.record.incidence.val.sideRole (!a.record.sideIndex) = ⟨N.ty, j⟩ := by
  classical
  obtain ⟨hne, f, g, hfg, hint⟩ := hij
  let fB : FacetName S B.node.ty :=
    ⟨f.val, by rw [hnode]; exact f.property⟩
  let s := D.blockState B hB
  let fs : FacetName S s.ty :=
    ⟨f.val, by rw [(hD.I1 B hB).2.1]; exact fB.property⟩
  have hinternal : s.InternalFacet fs := by
    change relint (placedSet
      (S.child (firstRole D B hB).1 (firstRole D B hB).2).frame f.val.carrier) ⊆
        interior (S.supertile 1 (firstRole D B hB).1)
    rw [hrole]
    rw [assembly_step1_child_cell, assembly_step1_relint_image,
      assembly_step1_parent_carrier] at hint
    have hi : interior (N.prototypeFrame n '' S.supertile 1 N.ty) =
        N.prototypeFrame n '' interior (S.supertile 1 N.ty) :=
      ((N.prototypeFrame n).toHomeomorphOfFiniteDimensional.image_interior _).symm
    rw [hi] at hint
    exact (Set.image_subset_image_iff (N.prototypeFrame n).injective).mp hint
  obtain ⟨r, hr, hage⟩ :=
    (state_semantics_a P s (hD.I1 B hB).1 fs).1.mp hinternal
  let a : Parser.AgeOneFacet D B hB fB := {
    record := r
    readout := by
      change stateRecordAt s f.val = some r
      unfold stateRecordAt
      split_ifs with hf
      · exact hr
      · exact (hf fs.property).elim
    age_one := hage.1 }
  have hPP := assembly_step2_parent_frame D N i B hB hnode hrole
  have hsem := Parser.ageOneFacet_semantics D hD B hB fB a
  have hserving : a.record.incidence.val.sideRole a.record.sideIndex = ⟨N.ty, i⟩ :=
    a.record.side_eq.symm.trans (hsem.2.2.1.trans hrole)
  have hfacet : ((⟨a.record.incidence.val.ty, N.frame⟩ : FramedNode S).child n
      (a.record.incidence.val.sideIndex (!a.record.sideIndex))).cell n
        (a.record.incidence.val.sideFacet (!a.record.sideIndex)).val =
          (N.child n i).cell n f.val := by
    simpa only [proposedSibling, hPP, hnode] using hsem.2.2.2
  have hrel : (relint ((N.child n i).cell n f.val)).Nonempty := by
    rw [FramedNode.cell, assembly_step1_relint_image]
    exact f.val.flat.relint_nonempty.image _
  have hj : (N.child n i).cell n f.val ⊆ (N.child n j).carrier n := by
    rw [hfg]
    exact assembly_step1_cell_subset _ n ⟨g.val, (Finset.mem_filter.mp g.property).1⟩
  have hother := assembly_step2_record_role N n i j f
    (hrel.mono fun _ hx => ⟨hx, hint hx⟩) (Ne.symm hne) hj a.record hserving hfacet
  refine ⟨fB, a, ?_, hother⟩
  unfold proposedSibling
  rw [hPP]
  exact congrArg (fun q : S.Role => (⟨(S.child q.1 q.2).ty,
    (S.placeChild n q.2).trans N.frame⟩ : FramedNode S)) hother

/-- Step 2 of the V4 proof of `assembly` (V4 3.7): "applying Proposition
3.6 along a path of the dual graph". One host step extends the family of
actual children, retaining the exact first letter supplied by that theorem. -/
private theorem assembly_step2_host
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (hY : MProper Y) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (i j : S.I N.ty) (hij : assembly_step1_adjacent N n i j)
    (hi : ∃ B : Block Y n, ∃ hB : B ∈ D.geometry.blocks,
      B.node = N.child n i ∧ firstRole D B hB = ⟨N.ty, i⟩) :
    ∃ B : Block Y n, ∃ hB : B ∈ D.geometry.blocks,
      B.node = N.child n j ∧ firstRole D B hB = ⟨N.ty, j⟩ := by
  obtain ⟨B, hB, hnode, hrole⟩ := hi
  obtain ⟨f, a, hsibling, hother⟩ :=
    assembly_step2_neighbor_record D hD N i j hij B hB hnode hrole
  obtain ⟨B', hB', hnode', hrole', _⟩ := host_step Y hY n hn D hD B hB f a
  exact ⟨B', hB', hnode'.trans hsibling, hrole'.trans hother⟩

/-- Step 3 of the V4 proof of `assembly` (V4 3.7): "Starting from B
(child i)". The recorded first role has the block's type, and the proposed
parent frame cancels to the block's full frame in that role. -/
private theorem assembly_step3_original_child
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (hD : Inv D) (B : Block Y n)
    (hB : B ∈ D.geometry.blocks) :
    (proposedParent D B hB).child n (firstRole D B hB).2 = B.node := by
  apply FramedNode.ext
  · exact (D.blockState B hB).address_start.trans (hD.I1 B hB).2.1
  · simp [FramedNode.child, proposedParent, AffineIsometryEquiv.trans_assoc]

/-- Step 3 of the V4 proof of `assembly` (V4 3.7): "Starting from B
(child i) ... all children are present". Induction on a finite dual path
produces the entire prescribed family, also when the path has length zero. -/
private theorem assembly_step3_children
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (hY : MProper Y) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) :
    Nonempty (Parser.AssembledParent D (proposedParent D B hB)) := by
  classical
  let N := proposedParent D B hB
  let i : S.I N.ty := (firstRole D B hB).2
  have hstart : ∃ B' : Block Y n, ∃ hB' : B' ∈ D.geometry.blocks,
      B'.node = N.child n i ∧ firstRole D B' hB' = ⟨N.ty, i⟩ :=
    ⟨B, hB, (assembly_step3_original_child D hD B hB).symm, rfl⟩
  have hall (j : S.I N.ty) : ∃ B' : Block Y n, ∃ hB' : B' ∈ D.geometry.blocks,
      B'.node = N.child n j ∧ firstRole D B' hB' = ⟨N.ty, j⟩ := by
    have hpath := assembly_step1_connected N n i j
    induction hpath with
    | refl => exact hstart
    | tail _ hedge ih => exact assembly_step2_host hY hn D hD N _ _ hedge ih
  choose child hmem hnode hrole using hall
  exact ⟨⟨fun j => ⟨child j, hmem j⟩, hnode, hrole⟩⟩

/-- Step 3 of the V4 proof of `assembly` (V4 3.7): "its standard
subdivision consists of tiles of Y with the right types and frames".
Split a native address into its first role and its address inside that child. -/
private theorem assembly_step3_actual
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    {D : DecodedLevel Y n} {N : FramedNode S} (A : Parser.AssembledParent D N) :
    IsBlock Y (n + 1) N := by
  intro w
  have hactual : IsBlock Y n (N.child n w.1) :=
    (A.child_eq w.1) ▸ (A.children w.1).val.actual
  obtain ⟨t, ht, hnode⟩ := hactual w.2
  refine ⟨t, ht, ?_⟩
  simpa only [SubstSystem.nativeTile, SubstSystem.descendantNode, Nat.zero_add,
    FramedNode.move, FramedNode.child, AffineIsometryEquiv.trans_assoc] using hnode

/-- Step 3 of the V4 proof of `assembly` (V4 3.7): "each a union of
level-n blocks (its children)". Substitute the actual child frames into the
geometric substitution cover. -/
private theorem assembly_step3_union
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    {D : DecodedLevel Y n} {N : FramedNode S} (A : Parser.AssembledParent D N) :
    N.carrier (n + 1) = ⋃ i : S.I N.ty, (A.children i).val.carrier := by
  rw [assembly_step1_children_cover]
  apply Set.iUnion_congr
  intro i
  change (N.child n i).carrier n = (A.children i).val.node.carrier n
  rw [A.child_eq]

/-- Step 3 of the V4 proof of `assembly` (V4 3.7): "PP(C) = PP(B)
for all of them". The first letter and full child frame recover the same parent. -/
private theorem assembly_step3_parent_eq
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    {D : DecodedLevel Y n} {N : FramedNode S}
    (A : Parser.AssembledParent D N) (i : S.I N.ty) :
    proposedParent D (A.children i).val (A.children i).property = N :=
  assembly_step2_parent_frame D N i (A.children i).val (A.children i).property
    (A.child_eq i) (A.first_letters i)

/-- Step 4 of the V4 proof of `assembly` (V4 3.7): "a common interior
point ... lies in the interior of a level-n block ... a child of both".
Regular closedness of the old children gives this directly, by two successive
interior approximations inside the open overlap. -/
private theorem assembly_step4_common_child
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (N M : FramedNode S)
    (A : Parser.AssembledParent D N) (A' : Parser.AssembledParent D M)
    (hmeet : (interior (N.carrier (n + 1)) ∩
      interior (M.carrier (n + 1))).Nonempty) :
    ∃ (i : S.I N.ty) (j : S.I M.ty), A.children i = A'.children j := by
  let U := interior (N.carrier (n + 1)) ∩ interior (M.carrier (n + 1))
  have hU : IsOpen U := isOpen_interior.inter isOpen_interior
  obtain ⟨x, hx⟩ := hmeet
  have hxN := interior_subset hx.1
  rw [assembly_step3_union A] at hxN
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxN
  have hxcl : x ∈ closure (interior (A.children i).val.carrier) := by
    change x ∈ closure (interior ((A.children i).val.node.carrier n))
    rw [(assembly_step1_node_regular (A.children i).val.node n).2.1]
    exact hxi
  obtain ⟨y, hyU, hyi⟩ := mem_closure_iff.mp hxcl U hU hx
  have hyM := interior_subset hyU.2
  rw [assembly_step3_union A'] at hyM
  obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hyM
  have hycl : y ∈ closure (interior (A'.children j).val.carrier) := by
    change y ∈ closure (interior ((A'.children j).val.node.carrier n))
    rw [(assembly_step1_node_regular (A'.children j).val.node n).2.1]
    exact hyj
  obtain ⟨z, hz, hzj⟩ := mem_closure_iff.mp hycl
    (U ∩ interior (A.children i).val.carrier) (hU.inter isOpen_interior) ⟨hyU, hyi⟩
  refine ⟨i, j, Subtype.ext ?_⟩
  by_contra hne
  exact Set.disjoint_left.mp
    (D.geometry.disjoint (A.children i).property (A'.children j).property hne) hz.2 hzj

/-- Step 4 of the V4 proof of `assembly` (V4 3.7): "PP(B) = PP(B̂) =
PP(B̃)". A common old child identifies both parents, including their frames. -/
private theorem assembly_step4_separation
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (N M : FramedNode S)
    (A : Parser.AssembledParent D N) (A' : Parser.AssembledParent D M)
    (hne : N ≠ M) :
    Disjoint (interior (N.carrier (n + 1))) (interior (M.carrier (n + 1))) := by
  apply Set.disjoint_left.mpr
  intro x hxN hxM
  obtain ⟨i, j, hchild⟩ := assembly_step4_common_child D N M A A' ⟨x, hxN, hxM⟩
  apply hne
  calc
    N = proposedParent D (A.children i).val (A.children i).property :=
      (assembly_step3_parent_eq A i).symm
    _ = proposedParent D (A'.children j).val (A'.children j).property := by rw [hchild]
    _ = M := assembly_step3_parent_eq A' j

/-- R7, V4 3.7: all proposed parents form a genuine geometric level n+1,
with disjoint interiors and whole-space coverage. Each parent is the union of
its actual level-n children, in their prescribed frames, and PP(C) = PP(B).
The one-child case is included; no branching hypothesis is added. -/
theorem assembly (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D) :
    ∃ G : GeometricLevel Y (n + 1), Parser.AssemblyGeometry D G := by
  classical
  have hparents (N : FramedNode S) (hN : N ∈ Parser.proposedParents D) :
      Nonempty (Parser.AssembledParent D N) := by
    obtain ⟨B, hB, rfl⟩ := hN
    exact assembly_step3_children hY hn D hD B hB
  let A (N : FramedNode S) (hN : N ∈ Parser.proposedParents D) :=
    Classical.choice (hparents N hN)
  let parent (N : FramedNode S) (hN : N ∈ Parser.proposedParents D) : Block Y (n + 1) :=
    ⟨N, assembly_step3_actual (A N hN)⟩
  let G : GeometricLevel Y (n + 1) := {
    blocks := {B | B.node ∈ Parser.proposedParents D}
    disjoint := by
      intro B hB B' hB' hne
      exact assembly_step4_separation D B.node B'.node (A B.node hB) (A B'.node hB')
        (fun heq => hne (Block.ext heq))
    cover := by
      intro x
      obtain ⟨B, hB, hx⟩ := D.geometry.cover x
      let N := proposedParent D B hB
      have hN : N ∈ Parser.proposedParents D := ⟨B, hB, rfl⟩
      let a := A N hN
      refine ⟨parent N hN, hN, ?_⟩
      change x ∈ N.carrier (n + 1)
      rw [assembly_step3_union a]
      apply Set.mem_iUnion.mpr
      refine ⟨(firstRole D B hB).2, ?_⟩
      have heq : (a.children (firstRole D B hB).2).val = B := by
        apply Block.ext
        exact (a.child_eq _).trans (assembly_step3_original_child D hD B hB)
      simpa only [heq] using hx }
  have hroots : G.roots = Parser.proposedParents D := by
    ext N
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact hB
    · intro hN
      exact ⟨parent N hN, hN, rfl⟩
  refine ⟨G, hroots, ?_, ?_⟩
  · intro N hN
    exact hparents N (hroots ▸ hN)
  · intro B hB
    exact ⟨(firstRole D B hB).2, (assembly_step3_original_child D hD B hB).symm⟩

namespace Parser

/-- R7, V4 3.7: the assembled geometry selected from the complete assembly theorem.
An actual proper output and its decoded old level supply the existence witness. -/
def assembledGeometry (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D) :
    GeometricLevel Y (n + 1) := Classical.choose (assembly Y hY n hn D hD)

/-- R7, V4 3.7: the selected geometry has exactly the proposed roots and child data. -/
theorem assembledGeometry_spec (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D) :
    AssemblyGeometry D (assembledGeometry Y hY n hn D hD) :=
  Classical.choose_spec (assembly Y hY n hn D hD)

/-- R7, V4 3.7: choose the already assembled child family at a new root.
This chooses only old geometric blocks and their proven first letters. -/
def assembledParent (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (hN : N ∈ (assembledGeometry Y hY n hn D hD).roots) :
    AssembledParent D N :=
  Classical.choice ((assembledGeometry_spec Y hY n hn D hD).children N hN)

/-- R7, V4 3.7: every strict descendant of an assembled parent already had a state.
The strict inequality excludes only the newly assembled root itself. -/
theorem assembled_inner_mem {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (N : FramedNode S) (A : AssembledParent D N)
    (m : ℕ) (M : FramedNode S) (hm : m < n + 1)
    (hM : M.IsDescendant m N (n + 1)) : M ∈ D.geometry.nodes m := by
  sorry

/-- R8, V4 3.8, replacement V4 8.3: a readable facet for one assembled child.
It belongs to F(A_C), has a positive birth inside C, belongs to both E_C and
E_P, and its honest attached packet has both indicated slots PRESENT.
No field assumes a state of the new parent or a routing conclusion. -/
structure ReadableFacet {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (N : FramedNode S) (A : AssembledParent D N)
    (i : S.I N.ty) where
  /-- R8, V4 3.8, 8.3: the positioned primitive facet in child prototype coordinates. -/
  facet : PrimitiveFacet S (A.children i).val.node.ty
  /-- R8, V4 3.8, 8.3: the facet is in the first branching descendant's F(A_C). -/
  first_branching : facet ∈ firstBranchingFacets (A.children i).val.node.ty
  /-- R8, V4 3.8, 8.3: the birth remains strictly above native tiles. -/
  depth_lt : facet.depth < n
  /-- R8, V4 3.8, 8.3: the same primitive occurrence in ambient framed coordinates. -/
  birthFacet : BornFacet P
  /-- R8, V4 3.8, 8.3: exact absolute birth height. -/
  height_eq : birthFacet.height = n - facet.depth
  /-- R8, V4 3.8, 8.3: exact birth node and frame in the child subdivision. -/
  birth_eq : birthFacet.birth = (facet.birthNode n).move (A.children i).val.node.frame
  /-- R8, V4 3.8, 8.3: the two coordinate descriptions have the same primitive support. -/
  carrier_eq : birthFacet.carrier = (A.children i).val.node.prototypeFrame n '' facet.carrier
  /-- R8, V4 3.8, 8.3: the birth is inside this actual child, with its prescribed frame. -/
  inside_child : birthFacet.birth.IsDescendant birthFacet.height (A.children i).val.node n
  /-- R8, V4 3.8, 8.3: membership in the child's principal set. -/
  child_principal : P.InPrincipal (A.children i).val.node n birthFacet.carrier
  /-- R8, V4 3.8, 8.3: membership in the parent's principal set by the iF(A_i) list. -/
  parent_principal : P.InPrincipal N (n + 1) birthFacet.carrier
  /-- R8, V4 3.8: the child's slot in the finite packet window. -/
  childSlot : Fin P.k
  /-- R8, V4 3.8: slots count upward from the positive birth height. -/
  childSlot_eq : childSlot.val = n - birthFacet.height
  /-- R8, V4 3.8: the immediately following parent slot. -/
  parentSlot : Fin P.k
  /-- R8, V4 3.8: the parent's exact upward slot index. -/
  parentSlot_eq : parentSlot.val = n + 1 - birthFacet.height
  /-- R8, V4 3.8: the packet is read from the actual left-side native pieces. -/
  constancy : BoundaryPackets Y (birthFacet.height - 1) birthFacet.leftNode
  /-- R8, V4 3.8: the non-NULL attached packet. -/
  packet : Packet P
  /-- R8, V4 3.8: attachment is the actual output marking's pre-pattern readout. -/
  attached : birthFacet.packet constancy = some packet
  /-- R8, V4 3.8: the packet belongs to the original finite honest alphabet. -/
  honest : packet ∈ honestPackets S P
  /-- R8, V4 3.8: the old child slot equals the child's existing assigned state. -/
  child_decode : decode packet childSlot =
    some (D.blockState (A.children i).val (A.children i).property)
  /-- R8/R9, V4 3.8--3.9: the value of the PRESENT parent slot, before naming S(P). -/
  parentState : State P
  /-- R8/R9, V4 3.8--3.9: presence of the parent slot with this exact value. -/
  parent_decode : decode packet parentSlot = some parentState

end Parser

/-- R8, V4 3.8, replacement V4 8.3: every assembled child has a readable facet
in F(A_C) ∩ E_C ∩ E_P, born inside C, with both slots PRESENT.
The child supplies a first branching descendant even for a placeholder type;
n ≥ K and the parameter inequalities make its birth positive. -/
theorem readable_facet (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N) (i : S.I N.ty) :
    Nonempty (Parser.ReadableFacet D N A i) := by
  sorry

namespace Parser

/-- R9, V4 3.9: select C₁ from the nonempty prescribed child list.
DEVIATION: roles have no preferred enumeration; Classical.choice supplies the
paper's unnamed first child. Routing will give the same state from every child. -/
def firstChild (A : S.ι) : S.I A := Classical.choice (roles_nonempty A)

/-- R8/R9, V4 3.8--3.9: choose a readable facet with its actual packet slots.
The existence comes from the geometric first branching descendant, not an
assumed state or child equation for the new parent. -/
def readableFacet (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : AssembledParent D N) (i : S.I N.ty) :
    ReadableFacet D N A i := Classical.choice (readable_facet Y hY n hn D hD N A i)

end Parser

/-- R9, V4 3.9: S(P) is the PRESENT parent slot of the chosen readable facet
of C₁. It is read from the actual attached packet, not chosen as a free honest
state. DEVIATION: the unordered role type's first child is `Parser.firstChild`;
V4 3.10 will assert that every principal primitive facet gives this same value. -/
def newState (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N) : State P :=
  (Parser.readableFacet Y hY n hn D hD N A (Parser.firstChild N.ty)).parentState

section Forward

variable (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
variable (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
variable (N : FramedNode S) (A : Parser.AssembledParent D N)

include hY hn hD A

/-- R9, V4 3.9: the defining parent slot is PRESENT and literally equals newState. -/
theorem newState_readout :
    let r := Parser.readableFacet Y hY n hn D hD N A (Parser.firstChild N.ty)
    decode r.packet r.parentSlot = some (newState Y hY n hn D hD N A) :=
  (Parser.readableFacet Y hY n hn D hD N A (Parser.firstChild N.ty)).parent_decode

section RoutingConstant

omit hY hn hD A

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"Every primitive facet f in E_P" is an actual positioned birth. This relation
retains its birth depth, full birth frame, and carrier, in the normalized
coordinates used by Lemma 1.25. -/
private def routing_constant_step1_realizes (N : FramedNode S) (m : ℕ)
    (f : PrimitiveFacet S N.ty) (g : Parser.BornFacet P) : Prop :=
  g.height + f.depth = m ∧
    g.birth = (f.birthNode m).move N.frame ∧
    g.carrier = N.prototypeFrame m '' f.carrier

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"born strictly below P" refers to the prescribed subdivision. A normalized
birth realization gives the actual framed descendant relation. -/
private theorem routing_constant_step1_descendant (N : FramedNode S) (m : ℕ)
    (f : PrimitiveFacet S N.ty) (g : Parser.BornFacet P)
    (h : routing_constant_step1_realizes N m f g) :
    g.birth.IsDescendant g.height N m := by
  refine ⟨f.depth, h.1.symm, f.word, ?_⟩
  have hsum := h.1
  have hh : m - f.depth = g.height := by omega
  simpa only [PrimitiveFacet.birthNode, hh] using h.2.1

/-- Step 1 of the V4 proof of `routing_constant` (V4 3.10):
"applied inside P". Transport the normalized birth frame to the assembled
parent, retaining the full anisotropic prototype frame. -/
private theorem routing_constant_step1_frame (N : FramedNode S) (m : ℕ)
    (f : PrimitiveFacet S N.ty) (hf : f.depth ≤ m) :
    ((f.birthNode m).move N.frame).prototypeFrame (m - f.depth) =
      f.birthFrame.trans (N.prototypeFrame m) := by
  have h := (f.birthFrame_spec m hf).2
  apply AffineEquiv.ext
  intro x
  have hx := congrArg (fun e : E d ≃ᵃ[ℝ] E d => e x) h
  change (S.σ ^ m).symm ((f.birthNode m).prototypeFrame (m - f.depth)
    x) = f.birthFrame x at hx
  have hx' := congrArg (fun z => N.frame ((S.σ ^ m) z)) hx
  simpa only [LinearEquiv.apply_symm_apply] using hx'

/-- Step 1 of the V4 proof of `routing_constant` (V4 3.10):
"For b = n+1 the facet is first-generation in P". A descendant at the same
height is exactly the root, including its frame. -/
private theorem routing_constant_step1_equal_height (N M : FramedNode S) (m : ℕ)
    (h : M.IsDescendant m N m) : M = N := by
  obtain ⟨r, hr, w, hw⟩ := h
  have : r = 0 := by omega
  subst r
  simpa only [SubstSystem.descendantNode, FramedNode.move,
    AffineIsometryEquiv.refl_trans] using hw

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"its address gives the actual path up to P". The type at the end of a fixed
role word is independent of the absolute height. -/
private theorem routing_constant_step1_descendant_type (T : S.ι) (h r : ℕ)
    (w : S.RoleWord T r) :
    (S.descendantNode T h r w).ty = (S.nativeTile T r w).ty := by
  induction r generalizing T with
  | zero => rfl
  | succ r ih => exact ih (S.child T w.1).ty w.2

/-- Step 1 of the V4 proof of `routing_constant` (V4 3.10):
"born in a node P_b inside P". Express a born facet using the normalized
incidence and the prototype frame of that birth node. -/
private theorem routing_constant_step1_carrier (g : Parser.BornFacet P) :
    g.carrier = g.birth.prototypeFrame g.height ''
      (S.σ.symm '' g.incidence.val.positioned) := by
  simp only [Parser.BornFacet.carrier, Params.incidencePlacement,
    PrimitiveIncidence.positioned, placedSet, Set.image_image]
  rfl

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"Every primitive facet f in E_P". Normalize an actual principal birth by
its own descendant address; principal membership follows from the carrier
and depth, without assuming uniqueness of primitive addresses. -/
private theorem routing_constant_step1_normalize (N : FramedNode S) (m : ℕ)
    (g : Parser.BornFacet P) (hbirth : g.birth.IsDescendant g.height N m)
    (hdepth : m - g.height < P.k) (hprincipal : P.InPrincipal N m g.carrier) :
    ∃ f ∈ P.E_A N.ty, routing_constant_step1_realizes N m f g := by
  obtain ⟨r, hr, w, hw⟩ := hbirth
  have ht : (S.nativeTile N.ty r w).ty = g.incidence.val.ty :=
    ((congrArg FramedNode.ty hw).trans
      (routing_constant_step1_descendant_type N.ty g.height r w)).symm.trans
        g.parent_type.symm
  let f : PrimitiveFacet S N.ty := {
    depth := r
    word := w
    localCarrier := g.incidence.val.positioned
    realization := by
      rw [ht]
      exact ⟨g.incidence.val.left, g.incidence.val.leftFacet, rfl,
        g.incidence.val.internal⟩ }
  have hd : f.depth < P.k := by change r < P.k; omega
  have hm : f.depth ≤ m := by change r ≤ m; omega
  have hh : m - f.depth = g.height := by change m - r = g.height; omega
  have hb : g.birth = (f.birthNode m).move N.frame := by
    simpa only [PrimitiveFacet.birthNode, hh] using hw
  have hframe : g.birth.prototypeFrame g.height =
      f.birthFrame.trans (N.prototypeFrame m) := by
    rw [hb, ← hh]
    exact routing_constant_step1_frame N m f hm
  have hcarrier : g.carrier = N.prototypeFrame m '' f.carrier := by
    rw [routing_constant_step1_carrier, hframe]
    simp only [PrimitiveFacet.carrier, Set.image_image]
    rfl
  refine ⟨f, ?_, hr.symm, hb, hcarrier⟩
  obtain ⟨e, he, hec⟩ := hprincipal
  have he' : e ∈ principalFacets S N.ty P.k (P.component N.ty) := by
    rw [← P.E_A_eq N.ty]
    exact he
  have hfe : f.carrier = e.carrier :=
    (N.prototypeFrame m).injective.image_injective (hcarrier.symm.trans hec.symm)
  change f ∈ (P.E_A N.ty : Set (PrimitiveFacet S N.ty))
  rw [P.E_A_eq]
  exact ⟨hd, hfe.symm ▸ he'.2⟩

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"first-generation facets". At native height the conjugated child placement
is the original prescribed isometry. -/
private theorem routing_constant_step1_ground_child (T : S.ι) (i : S.I T)
    (e : Cell d) :
    ((⟨T, AffineIsometryEquiv.refl ℝ (E d)⟩ : FramedNode S).child 0 i).cell 0 e =
      placedSet (S.child T i).frame e.carrier := by
  have hp : S.placeChild 0 i = (S.child T i).frame := by
    ext x
    simp [SubstSystem.placeChild_apply, linearConj, Child.frame, rigidMotion]
  simp [FramedNode.cell, FramedNode.prototypeFrame, FramedNode.child, hp, placedSet]

/-- Step 1 of the V4 proof of `routing_constant` (V4 3.10):
"the record with incidence iota(g)". Whole-facet pairing and the canonical
transversal assign the normalized facet its side-independent incidence. -/
private theorem routing_constant_step1_incidence {T : S.ι}
    (f : PrimitiveFacet S T) :
    ∃ a : P.Incidence, a.val.ty = f.birthType ∧ a.val.positioned = f.localCarrier := by
  obtain ⟨i, e, he, hint⟩ := f.realization
  let B : FramedNode S := ⟨f.birthType, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hc : B.carrier (0 + 1) = S.supertile 1 f.birthType := by
    simp [B, FramedNode.carrier, placedSet]
  have hne : (relint (placedSet (S.child f.birthType i).frame e.val.carrier)).Nonempty := by
    change (intrinsicInterior ℝ
      ((S.child f.birthType i).frame.toAffineIsometry '' e.val.carrier)).Nonempty
    rw [AffineIsometry.image_intrinsicInterior]
    exact e.val.flat.relint_nonempty.image _
  have hpair := internal_facet_pairing B 0 i e (by
    rw [routing_constant_step1_ground_child, hc]
    rw [he] at hint
    exact hne.mono (fun _ hx => ⟨hx, hint hx⟩))
  obtain ⟨j, ⟨hji, e', he', _⟩, _⟩ := hpair.2
  let a : PrimitiveIncidence S := {
    ty := f.birthType
    left := i
    right := j
    distinct := Ne.symm hji
    leftFacet := e
    rightFacet := e'
    paired := by
      rw [routing_constant_step1_ground_child, routing_constant_step1_ground_child] at he'
      exact he'.symm
    internal := by rw [he] at hint; exact hint }
  refine ⟨P.canonical a, (P.canonical_spec a).1.symm, ?_⟩
  exact (P.canonical_spec a).2.symm.trans he.symm

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"Every primitive facet f in E_P has a well-defined attached packet".
First realize each normalized facet as a positive-height framed birth. -/
private theorem routing_constant_step1_realize (N : FramedNode S) (m : ℕ)
    (f : PrimitiveFacet S N.ty) (hf : f.depth < m) :
    ∃ g : Parser.BornFacet P, routing_constant_step1_realizes N m f g := by
  obtain ⟨a, hat, hac⟩ := routing_constant_step1_incidence (P := P) f
  let g : Parser.BornFacet P := {
    height := m - f.depth
    positive := by omega
    birth := (f.birthNode m).move N.frame
    incidence := a
    parent_type := hat.trans (f.birthFrame_spec m (Nat.le_of_lt hf)).1.symm }
  refine ⟨g, ?_, rfl, ?_⟩
  · change m - f.depth + f.depth = m
    omega
  · rw [routing_constant_step1_carrier]
    change ((f.birthNode m).move N.frame).prototypeFrame (m - f.depth) ''
      (S.σ.symm '' a.val.positioned) = N.prototypeFrame m '' f.carrier
    rw [routing_constant_step1_frame N m f (Nat.le_of_lt hf), hac]
    simp only [PrimitiveFacet.carrier, Set.image_image]
    rfl

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"the attached packet". A fixed normalized facet has a unique born-facet
representation: its height and frame are fixed, and the incidence catalogue
has one representative of each positioned provider. -/
private theorem routing_constant_step1_unique (N : FramedNode S) (m : ℕ)
    (f : PrimitiveFacet S N.ty) (g g' : Parser.BornFacet P)
    (hg : routing_constant_step1_realizes N m f g)
    (hg' : routing_constant_step1_realizes N m f g') : g = g' := by
  have hh : g.height = g'.height := by have := hg.1; have := hg'.1; omega
  have hb : g.birth = g'.birth := hg.2.1.trans hg'.2.1.symm
  have hc : g.carrier = g'.carrier := hg.2.2.trans hg'.2.2.symm
  rw [routing_constant_step1_carrier, routing_constant_step1_carrier, hb, hh] at hc
  have hp : g.incidence.val.positioned = g'.incidence.val.positioned :=
    S.σ.symm.injective.image_injective
      ((g'.birth.prototypeFrame g'.height).injective.image_injective hc)
  have hi : g.incidence = g'.incidence := by
    have h := P.canonical_unique g.incidence.val g'.incidence
      ⟨g.parent_type.trans ((congrArg FramedNode.ty hb).trans g'.parent_type.symm), hp⟩
    simpa only [P.canonical_idempotent] using h
  cases g
  cases g'
  cases hh
  cases hb
  cases hi
  rfl

/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"For a facet born strictly below P, this follows from (I5) and Lemma 3.4
inside a child; for a first-generation facet of P, it follows from the second
assertion of Lemma 3.4". Both cases supply an actual honest packet. -/
private theorem routing_constant_step2_attachment
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (g : Parser.BornFacet P) (hbirth : g.birth.IsDescendant g.height N (n + 1)) :
    ∃ hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode,
      ∃ q : Packet P, g.packet hl = some q ∧ q ∈ honestPackets S P := by
  have hle := Parser.descendant_height_le _ _ _ _ hbirth
  by_cases hlt : g.height < n + 1
  · have hg := Parser.assembled_inner_mem D N A g.height g.birth hlt hbirth
    obtain ⟨hl, _, _, q, hq, _, hread, _⟩ := two_sided_constancy Y hY n hn D hD g hg
    exact ⟨hl, q, hread, hq⟩
  · have hh : g.height = n + 1 := by omega
    have hb : g.birth = N := routing_constant_step1_equal_height N g.birth (n + 1)
      (by simpa only [hh] using hbirth)
    obtain ⟨hl, _, _, q, hq, _, hread⟩ :=
      two_sided_constancy_assembled Y hY n hn D hD N A g hh hb
    exact ⟨hl, q, hread, hq⟩

/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"the head is the state of its birth node". The old two-sided theorem also
identifies the incidence, independently of the supplied constancy proof. -/
private theorem routing_constant_step2_old_readout
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (g : Parser.BornFacet P) (hg : g.birth ∈ D.geometry.nodes g.height)
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (q : Packet P) (hq : g.packet hl = some q) :
    q.incidence = g.incidence ∧ q.head = D.stateAt g.height g.birth hg := by
  obtain ⟨hl', _, _, q', _, hi, ha, _, hh⟩ := two_sided_constancy Y hY n hn D hD g hg
  have he : q = q' := Option.some.inj (hq.symm.trans ha)
  simpa only [he] using And.intro hi hh

/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"its address gives the actual path up to P". To read the address, realize
one honest old state at its actual height and frame, using the congruent
scale transfer of V4 1.13(c). No joint realization of the new parent is assumed. -/
private theorem routing_constant_step2_source_realization
    (s : State P) (hs : s ∈ honestStates S P) (N : FramedNode S) (n : ℕ)
    (hty : s.ty = N.ty) (hres : s.residue.val = n % P.L) :
    ∃ (U : HonestSource S) (hN : N ∈ U.hierarchy.nodes n),
      stateOf U P ⟨n, ⟨N, hN⟩⟩ = s := by
  obtain ⟨U, q, rfl⟩ := hs
  have hmod : q.1 % P.L = n % P.L := hres
  have hshift : (q.1 - n) % P.L = (n - q.1) % P.L := by
    rcases le_total q.1 n with h | h
    · rw [Nat.sub_eq_zero_of_le h, Nat.zero_mod]
      exact (Nat.dvd_iff_mod_eq_zero.mp ((Nat.modEq_iff_dvd' h).mp hmod)).symm
    · rw [Nat.sub_eq_zero_of_le h, Nat.zero_mod]
      exact Nat.dvd_iff_mod_eq_zero.mp ((Nat.modEq_iff_dvd' h).mp hmod.symm)
  obtain ⟨V, e, N', he⟩ := exactScaleTransfer U q.1 q.2.val q.2.property n
    (AffineIsometryEquiv.refl ℝ (E d))
  have hs' : stateOf V P ⟨n, N'⟩ = stateOf U P q := by
    have h := state_scaleTransfer P e hshift ⟨q, Nat.sub_le _ _⟩
    rw [he] at h
    exact h.symm
  have hty' : N'.val.ty = N.ty := by
    have h := e.types ⟨q, Nat.sub_le _ _⟩
    rw [he] at h
    exact h.trans hty
  let J := N'.val.frame.symm.trans N.frame
  obtain ⟨W, f, N'', hf⟩ := exactScaleTransfer V n N'.val N'.property n J
  have hs'' : stateOf W P ⟨n, N''⟩ = stateOf V P ⟨n, N'⟩ := by
    have h := state_scaleTransfer P f rfl ⟨⟨n, N'⟩, Nat.sub_le _ _⟩
    rw [hf] at h
    exact h.symm
  have hnode : N''.val = N := by
    apply FramedNode.ext
    · have h := f.types ⟨⟨n, N'⟩, Nat.sub_le _ _⟩
      rw [hf] at h
      exact h.trans hty'
    · have h := f.frames ⟨⟨n, N'⟩, Nat.sub_le _ _⟩
      rw [hf] at h
      apply AffineIsometryEquiv.ext
      intro x
      have hx := congrArg (fun g : E d ≃ᵃ[ℝ] E d => g ((S.σ ^ n).symm x)) h
      simpa [FramedNode.prototypeFrame, J] using hx
  obtain ⟨N'', hN''⟩ := N''
  dsimp only at hnode
  subst N''
  exact ⟨W, hN'', hs''.trans hs'⟩


/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"by (I2) and the children's first letters". Inside one old child, (I2)
identifies every descendant state and its ancestor in a fixed honest
realization of that child's state. -/
private theorem routing_constant_step2_source_descent
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) (hD : Inv D)
    (U : HonestSource S) (h r : ℕ) (N : FramedNode S)
    (hN : N ∈ D.geometry.nodes (h + r)) (hU : N ∈ U.hierarchy.nodes (h + r))
    (hs : stateOf U P ⟨h + r, ⟨N, hU⟩⟩ = D.stateAt (h + r) N hN)
    (w : S.RoleWord N.ty r) :
    let M := (S.descendantNode N.ty h r w).move N.frame
    ∃ (hM : M ∈ D.geometry.nodes h) (hMU : M ∈ U.hierarchy.nodes h),
      stateOf U P ⟨h, ⟨M, hMU⟩⟩ = D.stateAt h M hM ∧
        U.hierarchy.ancestor ⟨h, ⟨M, hMU⟩⟩ r = ⟨h + r, ⟨N, hU⟩⟩ := by
  induction r generalizing N with
  | zero =>
    have hnode : (S.descendantNode N.ty h 0 w).move N.frame = N := by
      cases N
      simp [SubstSystem.descendantNode, FramedNode.move]
    simp only [hnode]
    exact ⟨hN, hU, hs, rfl⟩
  | succ r ih =>
    let i := w.1
    let N' := N.child (h + r) i
    have hN' : N' ∈ D.geometry.nodes (h + r) := D.geometry.child_mem _ N hN i
    have hU' : N' ∈ U.hierarchy.nodes (h + r) := U.hierarchy.children_mem _ N hU i
    have hs' : stateOf U P ⟨h + r, ⟨N', hU'⟩⟩ = D.stateAt (h + r) N' hN' := by
      rw [hD.I2.1 (h + r) N hN i]
      simp only [Nat.add_assoc]
      rw [← hs]
      have hc := childMap_spec U P ⟨h + r + 1, ⟨N, hU⟩⟩
        (by change 1 ≤ h + r + 1; omega) i
      simpa [HonestSource.childNode, N'] using hc
    obtain ⟨hM, hMU, hstate, hanc⟩ := ih N' hN' hU' hs' w.2
    have hnode : (S.descendantNode N.ty h (r + 1) w).move N.frame =
        (S.descendantNode N'.ty h r w.2).move N'.frame := by
      simp [SubstSystem.descendantNode, FramedNode.move, FramedNode.child, N', i,
        AffineIsometryEquiv.trans_assoc]
    simp only [hnode]
    refine ⟨hM, hMU, hstate, ?_⟩
    rw [CoherentHierarchy.ancestor, Function.iterate_succ_apply']
    change U.hierarchy.parentNode (U.hierarchy.ancestor _ r) = _
    rw [hanc]
    apply Sigma.ext
    · simp [CoherentHierarchy.parentNode, Nat.add_assoc]
    · apply heq_of_eq
      apply Subtype.ext
      exact (U.hierarchy.parent_unique (h + r) ⟨N', hU'⟩ N hU ⟨i, rfl⟩).symm


/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"the children's first letters". A prescribed child and its globally distinct
role determine the parent type and full frame. -/
private theorem routing_constant_step2_parent_from_child
    (M N : FramedNode S) (m : ℕ) (j : S.I M.ty) (i : S.I N.ty)
    (hr : (⟨M.ty, j⟩ : S.Role) = ⟨N.ty, i⟩) (hc : M.child m j = N.child m i) : M = N := by
  rcases M with ⟨T, φ⟩
  rcases N with ⟨T', ψ⟩
  obtain ⟨ht, hj⟩ := Sigma.mk.inj_iff.mp hr
  dsimp only at ht hj
  subst T'
  have hi : j = i := eq_of_heq hj
  subst i
  congr 1
  have hf := congrArg FramedNode.frame hc
  apply AffineIsometryEquiv.ext
  intro x
  have hx := congrArg (fun e : Iso d => e ((S.placeChild m j).symm x)) hf
  simpa only [FramedNode.child, AffineIsometryEquiv.coe_trans, Function.comp_apply,
    AffineIsometryEquiv.apply_symm_apply] using hx

/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"Its P-slot is consequently PRESENT by Lemma 2.6(a)". Realize the containing
old child, descend to the birth using (I2), and identify the next source
parent by that child's first letter. Then apply the geometric mask theorem. -/
private theorem routing_constant_step2_address_mask
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (hD : Inv D) (N : FramedNode S)
    (A : Parser.AssembledParent D N) (g : Parser.BornFacet P)
    (hg : g.birth ∈ D.geometry.nodes g.height)
    (hbirth : g.birth.IsDescendant g.height N (n + 1))
    (hdepth : n + 1 - g.height < P.k) (hprincipal : P.InPrincipal N (n + 1) g.carrier) :
    packetMask P g.incidence (D.stateAt g.height g.birth hg)
      ⟨n + 1 - g.height, hdepth⟩ := by
  have hle := D.geometry.nodes_height _ _ hg
  obtain ⟨r, hr, w, hw⟩ := hbirth
  have hrpos : 0 < r := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
  have hn : n = g.height + r := by omega
  subst n
  let B := N.child (g.height + r) w.1
  have hB : B ∈ D.geometry.nodes (g.height + r) := by
    change N.child (g.height + r) w.1 ∈ D.geometry.nodes (g.height + r)
    rw [← A.child_eq w.1]
    exact D.geometry.root_mem (A.children w.1).val (A.children w.1).property
  obtain ⟨U, hU, hs⟩ := routing_constant_step2_source_realization
    (D.stateAt (g.height + r) B hB) (D.state_honest _ _)
    B (g.height + r) (hD.node_type_residue _ _ hB).1 (hD.node_type_residue _ _ hB).2
  have hnode : (S.descendantNode B.ty g.height r w.2).move B.frame = g.birth := by
    rw [hw]
    simp [B, SubstSystem.descendantNode, FramedNode.move, FramedNode.child,
      AffineIsometryEquiv.trans_assoc]
  have hdown := routing_constant_step2_source_descent D hD U g.height r B hB hU hs w.2
  dsimp only at hdown
  rw [hnode] at hdown
  obtain ⟨_, hGU, hstate, hanc⟩ := hdown
  let c : U.Node := ⟨g.height + r, ⟨B, hU⟩⟩
  have hrole : U.hierarchy.nodeRole c = ⟨N.ty, w.1⟩ := by
    change (stateOf U P c).address ⟨0, P.k_pos⟩ = _
    rw [hs]
    have h := A.first_letters w.1
    simpa only [firstRole, DecodedLevel.blockState, A.child_eq] using h
  have hparent : (U.hierarchy.parentNode c).2.val = N := by
    have hc := U.hierarchy.child_eq (g.height + r) c.2
    exact routing_constant_step2_parent_from_child (U.hierarchy.parentNode c).2.val N
      (g.height + r) (U.hierarchy.role (g.height + r) c.2) w.1 hrole hc.symm
  let occ : PrimitiveOccurrence U P := {
    birth := ⟨g.height, ⟨g.birth, hGU⟩⟩
    positive := g.positive
    incidence := g.incidence
    parent_type := g.parent_type }
  have hanc' : U.hierarchy.ancestor occ.birth (r + 1) = U.hierarchy.parentNode c := by
    rw [CoherentHierarchy.ancestor, Function.iterate_succ_apply']
    change U.hierarchy.parentNode (U.hierarchy.ancestor occ.birth r) = _
    rw [hanc]
  have hm : mask U P occ ⟨g.height + r + 1 - g.height, hdepth⟩ := by
    change P.InPrincipal (U.hierarchy.ancestor occ.birth _).2.val
      (U.hierarchy.ancestor occ.birth _).1 g.carrier
    dsimp only [Fin.val_mk]
    have he : g.height + r + 1 - g.height = r + 1 := by omega
    rw [he, hanc', hparent]
    exact hprincipal
  have hmask := (packet_mask_fn U P occ ⟨g.height + r + 1 - g.height, hdepth⟩).mp hm
  change packetMask P g.incidence (stateOf U P ⟨g.height, ⟨g.birth, hGU⟩⟩) _ at hmask
  simpa only [hstate] using hmask

/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"If b = n+1, the P-slot is its head, always PRESENT". Below the new parent,
the address mask and honesty give presence; at the new parent use slot zero. -/
private theorem routing_constant_step2_present
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (g : Parser.BornFacet P) (hbirth : g.birth.IsDescendant g.height N (n + 1))
    (hdepth : n + 1 - g.height < P.k) (hprincipal : P.InPrincipal N (n + 1) g.carrier)
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (q : Packet P) (hq : g.packet hl = some q) (hhon : q ∈ honestPackets S P) :
    ∃ s, decode q ⟨n + 1 - g.height, hdepth⟩ = some s := by
  have hle := Parser.descendant_height_le _ _ _ _ hbirth
  by_cases hlt : g.height < n + 1
  · have hg := Parser.assembled_inner_mem D N A g.height g.birth hlt hbirth
    obtain ⟨hi, hh⟩ := routing_constant_step2_old_readout Y hY n hn D hD g hg hl q hq
    have hm : q.mask ⟨n + 1 - g.height, hdepth⟩ := by
      change packetMask P q.incidence q.head _
      rw [hi, hh]
      exact routing_constant_step2_address_mask D hD N A g hg hbirth hdepth hprincipal
    have hj := (honest_packet_admissible P q hhon).2.2.2.1 _ hm
    refine ⟨q.reconstructed ⟨n + 1 - g.height, hdepth⟩, ?_⟩
    unfold decode
    exact if_pos ⟨hj, hm⟩
  · have he : (⟨n + 1 - g.height, hdepth⟩ : Fin P.k) = ⟨0, P.k_pos⟩ := by
      apply Fin.ext
      change n + 1 - g.height = 0
      omega
    exact ⟨q.head, he ▸ (honest_packet_admissible P q hhon).1⟩

/-- Step 1 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3):
"two first-generation facets of a node Q". Equality of birth addresses
transports to equality of their actual heights and framed birth nodes. -/
private theorem routing_constant_step3_same_parent_ports_step1_same_birth
    (N : FramedNode S) (m : ℕ) (f f' : PrimitiveFacet S N.ty)
    (g g' : Parser.BornFacet P)
    (hg : routing_constant_step1_realizes N m f g)
    (hg' : routing_constant_step1_realizes N m f' g')
    (h : f.birthAddress = f'.birthAddress) :
    g.height = g'.height ∧ g.birth = g'.birth := by
  have hd : f.depth = f'.depth := congrArg Sigma.fst h
  refine ⟨by have := hg.1; have := hg'.1; omega, ?_⟩
  have hb := congrArg (fun a : Σ r : ℕ, S.RoleWord N.ty r =>
    (S.descendantNode N.ty (m - a.1) a.1 a.2).move N.frame) h
  exact hg.2.1.trans (hb.trans hg'.2.1.symm)

/-- Step 1 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 1.5):
"common-listed vertex". Every listed cell lies in its prototype support. -/
private theorem routing_constant_step3_same_parent_ports_step1_cell_subset (A : S.ι) (e : Cell d) (he : e ∈ (S.cx A).cells) :
    e.carrier ⊆ (S.proto A).carrier := by
  intro x hx
  apply (S.proto A).compact.isClosed.frontier_subset
  rw [← (S.cx A).carriers_cover]
  exact mem_iUnion₂.mpr ⟨e, he, hx⟩

/-- Step 1 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3):
"inside the children of Q owning the facet". The left child's prototype
frame is the canonical incidence-side placement at the positive birth height. -/
private theorem routing_constant_step3_same_parent_ports_step1_left_frame
    (g : Parser.BornFacet P) :
    g.leftNode.prototypeFrame (g.height - 1) =
      ((S.child g.incidence.val.ty g.incidence.val.left).frame.toAffineEquiv.trans
        S.σ.symm.toAffineEquiv).trans (g.birth.prototypeFrame g.height) := by
  have hh : g.height = g.height - 1 + 1 := by have := g.positive; omega
  apply AffineEquiv.ext
  intro x
  change g.birth.frame (S.placeChild (g.height - 1) g.incidence.val.left
      ((S.σ ^ (g.height - 1)) x)) =
    g.birth.frame ((S.σ ^ g.height)
      (S.σ.symm ((S.child g.incidence.val.ty g.incidence.val.left).frame x)))
  rw [S.placeChild_apply]
  rw [hh]
  simp [linearConj, Child.frame, rigidMotion, pow_succ, zpow_neg,
    LinearEquiv.mul_apply, ← map_add]

/-- Step 1 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3):
"in its actual position". Realization transports the whole birth frame
and identifies the canonical local primitive carrier. -/
private theorem routing_constant_step3_same_parent_ports_step1_coordinates
    (N : FramedNode S) (m : ℕ) (f : PrimitiveFacet S N.ty)
    (g : Parser.BornFacet P) (hg : routing_constant_step1_realizes N m f g) :
    g.incidence.val.ty = f.birthType ∧
      g.birth.prototypeFrame g.height = f.birthFrame.trans (N.prototypeFrame m) ∧
      g.incidence.val.positioned = f.localCarrier := by
  have hm : f.depth ≤ m := by have := hg.1; omega
  have hh : m - f.depth = g.height := by have := hg.1; omega
  have hf : g.birth.prototypeFrame g.height = f.birthFrame.trans (N.prototypeFrame m) := by
    rw [hg.2.1, ← hh]
    exact routing_constant_step1_frame N m f hm
  refine ⟨g.parent_type.trans ((congrArg FramedNode.ty hg.2.1).trans
    (f.birthFrame_spec m hm).1), hf, ?_⟩
  have hc := hg.2.2
  rw [routing_constant_step1_carrier, hf] at hc
  have hc' : (N.prototypeFrame m) '' (f.birthFrame ''
      (S.σ.symm '' g.incidence.val.positioned)) =
      (N.prototypeFrame m) '' (f.birthFrame '' (S.σ.symm '' f.localCarrier)) := by
    simpa only [PrimitiveFacet.carrier, Set.image_image] using hc
  exact S.σ.symm.injective.image_injective
    (f.birthFrame.injective.image_injective ((N.prototypeFrame m).injective.image_injective hc'))

/-- Step 1 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3):
"a common-listed vertex q". The normalized common-listed seed is listed
in the actual canonical left owner of either realized facet containing it. -/
private theorem routing_constant_step3_same_parent_ports_step1_left_listed
    (N : FramedNode S) (m : ℕ) (f : PrimitiveFacet S N.ty)
    (g : Parser.BornFacet P) (hg : routing_constant_step1_realizes N m f g)
    (p : E d) (hp : p ∈ f.carrier) (hc : f.CommonListed p) :
    g.leftNode.Lists (g.height - 1) (N.prototypeFrame m p) := by
  obtain ⟨ht, hframe, hcarrier⟩ :=
    routing_constant_step3_same_parent_ports_step1_coordinates N m f g hg
  have hcommon : ∀ i : S.I g.incidence.val.ty,
      p ∈ f.birthFrame '' (S.σ.symm '' placedSet (S.child g.incidence.val.ty i).frame
        (S.proto (S.child g.incidence.val.ty i).ty).carrier) →
      ∃ v ∈ (S.cx (S.child g.incidence.val.ty i).ty).vertices,
        p ∈ f.birthFrame '' (S.σ.symm '' placedSet (S.child g.incidence.val.ty i).frame
          v.carrier) := by
    rw [ht]
    exact hc
  have hsupport : p ∈ f.birthFrame '' (S.σ.symm ''
      placedSet (S.child g.incidence.val.ty g.incidence.val.left).frame
        (S.proto (S.child g.incidence.val.ty g.incidence.val.left).ty).carrier) := by
    change p ∈ f.birthFrame '' (S.σ.symm '' f.localCarrier) at hp
    rw [← hcarrier] at hp
    exact Set.image_mono (Set.image_mono (Set.image_mono
      (routing_constant_step3_same_parent_ports_step1_cell_subset _ _
        (Finset.mem_filter.mp g.incidence.val.leftFacet.property).1))) hp
  obtain ⟨v, hv, x, ⟨y, ⟨z, hz, rfl⟩, rfl⟩, hzp⟩ :=
    hcommon g.incidence.val.left hsupport
  refine ⟨v, hv, z, hz, ?_⟩
  change g.leftNode.prototypeFrame (g.height - 1) z = N.prototypeFrame m p
  rw [routing_constant_step3_same_parent_ports_step1_left_frame, hframe]
  exact congrArg (N.prototypeFrame m) hzp

/-- Step 2 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3, 1.5, 1.8):
"A native descendant along either facet at q". Heredity and inherited
listedness give an actual native facet piece with that listed vertex. -/
private theorem routing_constant_step3_same_parent_ports_step2_native_piece
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (B : Block Y n)
    (f : FacetName S B.node.ty) (p : E d) (hp : B.node.Lists n p)
    (hpf : p ∈ B.node.cell n f.val) :
    ∃ (t : PlacedMarkedTile (systemM S P C)) (g : FacetName S (tileNode t).ty)
      (v : VertexName S (tileNode t).ty),
      Parser.IsFacetPiece Y n B.node f t g ∧ v.val.carrier ⊆ g.val.carrier ∧
        compilerFrame C t (vertexPoint v) = p := by
  classical
  obtain ⟨parts, hparts⟩ := S.heredity_iter B.node.ty n f.val
    (Finset.mem_filter.mp f.property).1
  obtain ⟨x, hxf, hxp⟩ := hpf
  have hσx : (S.σ ^ n) x ∈ (S.σ ^ n) '' f.val.carrier := ⟨x, hxf, rfl⟩
  rw [hparts] at hσx
  obtain ⟨q, hq, y, hy, hxy⟩ := mem_iUnion₂.mp hσx
  obtain ⟨t, ht, hnode⟩ := B.actual q.1
  let g : FacetName S (tileNode t).ty := ⟨q.2.val, by
    rw [hnode]
    exact Finset.mem_filter.mpr ⟨q.2.property.1,
      q.2.property.2.trans (Finset.mem_filter.mp f.property).2⟩⟩
  have hdesc : (tileNode t).IsDescendant 0 B.node n := ⟨n, by omega, q.1, hnode⟩
  have hsub : (tileNode t).cell 0 g.val ⊆ B.node.cell n f.val := by
    rintro z ⟨w, hw, rfl⟩
    have hmem : (S.nativeTile B.node.ty n q.1).frame w ∈ (S.σ ^ n) '' f.val.carrier := by
      rw [hparts]
      exact mem_iUnion₂.mpr ⟨q, hq, w, hw, rfl⟩
    obtain ⟨z, hz, he⟩ := hmem
    refine ⟨z, hz, ?_⟩
    rw [hnode]
    change B.node.frame ((S.σ ^ n) z) = B.node.frame ((S.nativeTile B.node.ty n q.1).frame w)
    exact congrArg B.node.frame he
  have hpoint : (tileNode t).prototypeFrame 0 y = p := by
    rw [hnode]
    change B.node.frame ((S.nativeTile B.node.ty n q.1).frame y) = p
    rw [hxy]
    exact hxp
  have hmem : p ∈ (tileNode t).carrier 0 := by
    rw [← hpoint, hnode]
    refine ⟨(S.σ ^ 0) y, ⟨y, ?_, rfl⟩, rfl⟩
    exact routing_constant_step3_same_parent_ports_step1_cell_subset _ q.2.val q.2.property.1 hy
  obtain ⟨v, hv, hvp⟩ := commonListed_inherited B.node (tileNode t) n 0 hdesc p hp hmem
  let v' : VertexName S (tileNode t).ty := ⟨v, hv⟩
  have hvpoint : compilerFrame C t (vertexPoint v') = p := by
    obtain ⟨z, hz, hzp⟩ := hvp
    change z ∈ v'.val.carrier at hz
    have hzv : z = vertexPoint v' := by simpa only [vertexPoint_spec v', mem_singleton_iff] using hz
    subst z
    exact hzp
  have hvg : v.carrier ⊆ g.val.carrier := by
    rw [vertexPoint_spec v']
    apply singleton_subset_iff.mpr
    have hyv : y = vertexPoint v' := by
      apply (compilerFrame C t).injective
      exact hpoint.trans hvpoint.symm
    simpa only [← hyv] using hy
  exact ⟨t, g, v', ⟨ht, hdesc, hsub⟩, hvg, hvpoint⟩

/-- Step 3 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3):
"This also holds when Q = P, since the children's age-one records are
known from Corollary 2.4(a)". Realize one old child state in an honest source
whose actual parent is the prescribed birth node. At the new root, only
the child's first letter is used to recover that parent. -/
private theorem routing_constant_step3_same_parent_ports_step3_child_source
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (hD : Inv D) (N : FramedNode S)
    (A : Parser.AssembledParent D N) (m : ℕ) (Q : FramedNode S)
    (hQ : Q.IsDescendant (m + 1) N (n + 1)) (i : S.I Q.ty) :
    ∃ (hB : Q.child m i ∈ D.geometry.nodes m) (U : HonestSource S)
      (hU : Q.child m i ∈ U.hierarchy.nodes m),
      stateOf U P ⟨m, ⟨Q.child m i, hU⟩⟩ = D.stateAt m (Q.child m i) hB ∧
      (U.hierarchy.parentNode ⟨m, ⟨Q.child m i, hU⟩⟩).2.val = Q := by
  have hmn : m ≤ n := by
    have := Parser.descendant_height_le _ _ _ _ hQ
    omega
  have hB : Q.child m i ∈ D.geometry.nodes m :=
    Parser.assembled_inner_mem D N A m (Q.child m i) (by omega)
      (Parser.descendant_trans _ _ _ _ _ _ (Parser.child_descendant Q m i) hQ)
  refine ⟨hB, ?_⟩
  by_cases hlt : m < n
  · have hQD : Q ∈ D.geometry.nodes (m + 1) :=
      Parser.assembled_inner_mem D N A (m + 1) Q (by omega) hQ
    obtain ⟨U, hU, hs⟩ := routing_constant_step2_source_realization
      (D.stateAt (m + 1) Q hQD) (D.state_honest _ _) Q (m + 1)
      (hD.node_type_residue _ _ hQD).1 (hD.node_type_residue _ _ hQD).2
    have hBU := U.hierarchy.children_mem m Q hU i
    refine ⟨U, hBU, ?_, ?_⟩
    · rw [hD.I2.1 m Q hQD i, ← hs]
      simpa [HonestSource.childNode] using
        (childMap_spec U P ⟨m + 1, ⟨Q, hU⟩⟩ (by change 1 ≤ m + 1; omega) i)
    · exact (U.hierarchy.parent_unique m ⟨Q.child m i, hBU⟩ Q hU ⟨i, rfl⟩).symm
  · have hmn' : m = n := by omega
    subst m
    have hQN : Q = N := routing_constant_step1_equal_height N Q (n + 1) hQ
    subst Q
    obtain ⟨U, hU, hs⟩ := routing_constant_step2_source_realization
      (D.stateAt n (N.child n i) hB) (D.state_honest _ _) (N.child n i) n
      (hD.node_type_residue _ _ hB).1 (hD.node_type_residue _ _ hB).2
    refine ⟨U, hU, hs, ?_⟩
    let c : U.Node := ⟨n, ⟨N.child n i, hU⟩⟩
    have hr : U.hierarchy.nodeRole c = ⟨N.ty, i⟩ := by
      change (stateOf U P c).address ⟨0, P.k_pos⟩ = _
      rw [hs]
      simpa only [firstRole, DecodedLevel.blockState, A.child_eq] using A.first_letters i
    exact routing_constant_step2_parent_from_child (U.hierarchy.parentNode c).2.val N
      n (U.hierarchy.role n c.2) i hr (U.hierarchy.child_eq n c.2).symm

/-- Step 3 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3, 2.3):
"an END header with realised cone T_q Q". This is the full geometric
header of the birth node at the shared point, expressed in the central
native tile's frame; it contains no state of the newly assembled parent. -/
private def routing_constant_step3_same_parent_ports_step3_header (Q : FramedNode S) (n : ℕ)
    (φ : Iso d) (p : E d) : State.Header P := by
  classical
  let normalize := fun K : Set (E d) => φ.linearIsometryEquiv.symm '' K
  let pos := fun ι : P.Incidence => P.incidencePlacement Q (n + 1) ι
  exact {
    birthType := Q.ty
    parentCone := normalize (tangentCone (Q.carrier (n + 1)) p)
    childCones := fun i =>
      let N := Q.child n i
      if p ∈ N.carrier n then some (normalize (tangentCone (N.carrier n) p)) else none
    boundaryCones := fun F => if p ∈ Q.cell (n + 1) F.val then
      some (normalize (tangentCone (Q.cell (n + 1) F.val) p)) else none
    primitiveCones := fun ι => if ι.val.ty = Q.ty ∧
        p ∈ pos ι '' ι.val.leftFacet.val.carrier then
      some (normalize (tangentCone (pos ι '' ι.val.leftFacet.val.carrier) p)) else none
    flagTangent := fun ι => if ι.val.ty = Q.ty ∧
        (p = pos ι (P.flag ι).initial ∨ p = pos ι (P.flag ι).terminal) then
      some {
        cones := fun j => normalize
          (tangentCone (pos ι '' ((P.flag ι).flag.cell j).val.carrier) p)
        initial := decide (p = pos ι (P.flag ι).initial)
        sides := fun j => normalize ((pos ι).linear '' (P.flag ι).sides j) }
      else none }

/-- Step 3 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 2.3):
"in its actual position". Relative interiors commute with the full affine
frames, including the anisotropic expansion. -/
private theorem routing_constant_step3_same_parent_ports_step3_relint_image
    (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
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

/-- Step 3 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3, 2.3):
"from its owner's age-one record". A native listed vertex that is also
listed in its serving child maps to a zero-dimensional provider stratum. -/
private theorem routing_constant_step3_same_parent_ports_step3_provider_vertex
    (U : HonestSource S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (v : VertexName S q.2.val.ty)
    (hv : v.val.carrier ⊆ f.val.carrier)
    (hp : (U.hierarchy.servingChild q f hf).2.val.Lists
      (U.hierarchy.servingChild q f hf).1
      (q.2.val.prototypeFrame q.1 (vertexPoint v))) :
    (U.recordTau P q f hf ⟨vertexCell v, hv⟩).val.val.dim = 0 := by
  obtain ⟨w, hw, hpw⟩ := hp
  let w' : VertexName S (U.hierarchy.servingChild q f hf).2.val.ty := ⟨w, hw⟩
  have hpoint : q.2.val.prototypeFrame q.1 (vertexPoint v) =
      (U.hierarchy.servingChild q f hf).2.val.prototypeFrame
        (U.hierarchy.servingChild q f hf).1 (vertexPoint w') := by
    change _ ∈ (U.hierarchy.servingChild q f hf).2.val.cell
      (U.hierarchy.servingChild q f hf).1 w'.val at hpw
    simpa only [FramedNode.cell, vertexPoint_spec w', Set.image_singleton,
      Set.mem_singleton_iff] using hpw
  have hcell : q.2.val.cell q.1 (vertexCell v).val =
      (U.hierarchy.servingChild q f hf).2.val.cell
        (U.hierarchy.servingChild q f hf).1 (vertexCell w').val := by
    simp only [FramedNode.cell, vertexCell, vertexPoint_spec, Set.image_singleton, hpoint]
  have hstratum : U.hierarchy.stratumMap q f hf (vertexCell v)
      (U.cellInFacet_placed q f ⟨vertexCell v, hv⟩) = vertexCell w' := by
    exact ((Classical.choose_spec (U.hierarchy.stratum_exists_unique q f hf
      (vertexCell v) (U.cellInFacet_placed q f ⟨vertexCell v, hv⟩))).2
        (vertexCell w') (by rw [hcell])).symm
  have htau := record_tau_spec U P q f hf ⟨vertexCell v, hv⟩
  rw [hstratum] at htau
  change U.providerPlacement P q f hf ''
      (U.recordTau P q f hf ⟨vertexCell v, hv⟩).val.val.carrier =
    (U.hierarchy.servingChild q f hf).2.val.prototypeFrame
      (U.hierarchy.servingChild q f hf).1 '' w'.val.carrier at htau
  rw [vertexPoint_spec, Set.image_singleton] at htau
  let e := U.recordTau P q f hf ⟨vertexCell v, hv⟩
  have hsingleton : e.val.val.carrier =
      {(U.providerPlacement P q f hf).symm
        ((U.hierarchy.servingChild q f hf).2.val.prototypeFrame
          (U.hierarchy.servingChild q f hf).1 (vertexPoint w'))} := by
    apply (U.providerPlacement P q f hf).injective.image_injective
    simpa only [Set.image_singleton, AffineEquiv.apply_symm_apply] using htau
  change e.val.val.dim = 0
  rw [← e.val.val.flat.dimension, hsingleton]
  simp [cellDirection, direction_affineSpan]

/-- Step 3 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3):
"two first-generation facets of a node Q". The relative interior of a
positive-height born facet is internal to its actual birth node. -/
private theorem routing_constant_step3_same_parent_ports_step3_internal
    (g : Parser.BornFacet P) :
    relint g.carrier ⊆ interior (g.birth.carrier g.height) := by
  let e : E d ≃ᵃ[ℝ] E d := S.σ.symm.toAffineEquiv.trans
    (g.birth.prototypeFrame g.height)
  have hcarrier : g.carrier = e '' g.incidence.val.positioned := by
    rw [routing_constant_step1_carrier, Set.image_image]
    rfl
  have hparent : g.birth.carrier g.height = e '' S.supertile 1 g.incidence.val.ty := by
    simp [e, FramedNode.carrier, FramedNode.prototypeFrame, SubstSystem.supertile,
      placedSet, Set.image_image, g.parent_type]
  rw [hcarrier, hparent,
    routing_constant_step3_same_parent_ports_step3_relint_image]
  have he : e '' interior (S.supertile 1 g.incidence.val.ty) =
      interior (e '' S.supertile 1 g.incidence.val.ty) :=
    e.toHomeomorphOfFiniteDimensional.image_interior _
  rw [← he]
  exact Set.image_mono g.incidence.val.internal

/-- Step 3 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3, 2.3):
"A native descendant along either facet at q inherits an END header with
realised cone T_q Q, from its owner's age-one record". Descend a single
honest child realization to the given native piece, and read its actual
leaf state using (I2). No template or second port is asserted here. -/
private theorem routing_constant_step3_same_parent_ports_step3_inherited_slot
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (hD : Inv D) (N : FramedNode S)
    (A : Parser.AssembledParent D N) (g : Parser.BornFacet P)
    (hbirth : g.birth.IsDescendant g.height N (n + 1))
    (p : E d) (hp : g.leftNode.Lists (g.height - 1) p)
    (t : PlacedMarkedTile (systemM S P C)) (e : FacetName S (tileNode t).ty)
    (v : VertexName S (tileNode t).ty)
    (hpiece : Parser.IsFacetPiece Y (g.height - 1) g.leftNode
      g.incidence.val.leftFacet t e)
    (hv : v.val.carrier ⊆ e.val.carrier) (hvp : compilerFrame C t (vertexPoint v) = p)
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (q : Packet P) (hq : g.packet hl = some q) :
    ∃ j : EndSlot (compilerLeaf C t), j.facet = e ∧
      Compiler.endVertex (compilerFrame C t) j = p ∧
      j.header = routing_constant_step3_same_parent_ports_step3_header
        g.birth (g.height - 1) (compilerFrame C t) p := by
  classical
  let Q : FramedNode S := ⟨g.incidence.val.ty, g.birth.frame⟩
  have hQ : Q = g.birth := FramedNode.ext g.parent_type rfl
  have hh : g.height - 1 + 1 = g.height := by have := g.positive; omega
  obtain ⟨hB, U, hU, hs, hpar⟩ :=
    routing_constant_step3_same_parent_ports_step3_child_source D hD N A
      (g.height - 1) Q (by rw [hQ, hh]; exact hbirth) g.incidence.val.left
  let c : U.Node := ⟨g.height - 1, ⟨g.leftNode, hU⟩⟩
  have hparent : (U.hierarchy.parentNode c).2.val = g.birth := hpar.trans hQ
  have hint : relint (c.2.val.cell c.1 g.incidence.val.leftFacet.val) ⊆
      interior ((U.hierarchy.parentNode c).2.val.carrier (U.hierarchy.parentNode c).1) := by
    change relint (g.leftNode.cell (g.height - 1) g.incidence.val.leftFacet.val) ⊆
      interior ((U.hierarchy.parentNode c).2.val.carrier (g.height - 1 + 1))
    rw [g.sides_carrier.1, hparent, hh]
    exact routing_constant_step3_same_parent_ports_step3_internal g
  obtain ⟨hF, _, hFbirth, _⟩ :=
    U.hierarchy.restriction_det_internal c g.incidence.val.leftFacet hint
  obtain ⟨r, hr, w, htile⟩ := hpiece.2.1
  have hrn : r = g.height - 1 := by omega
  subst r
  have hreal {k : ℕ} (hk : k = g.height - 1)
      (hD' : g.leftNode ∈ D.geometry.nodes k) (hU' : g.leftNode ∈ U.hierarchy.nodes k) :
      stateOf U P ⟨k, ⟨g.leftNode, hU'⟩⟩ = D.stateAt k g.leftNode hD' := by
    subst k
    exact hs
  have hnode {k : ℕ} (hk : k = g.height - 1)
      (hU' : g.leftNode ∈ U.hierarchy.nodes k) :
      (⟨k, ⟨g.leftNode, hU'⟩⟩ : U.Node) = c := by
    subst k
    rfl
  have hdesc : ∃ (htD : tileNode t ∈ D.geometry.nodes 0)
      (htU : tileNode t ∈ U.hierarchy.nodes 0),
      stateOf U P ⟨0, ⟨tileNode t, htU⟩⟩ = D.stateAt 0 (tileNode t) htD ∧
        U.hierarchy.ancestor ⟨0, ⟨tileNode t, htU⟩⟩ (g.height - 1) = c := by
    obtain ⟨htD, htU, htstate, hanc⟩ :=
      routing_constant_step2_source_descent D hD U 0 (g.height - 1)
      g.leftNode (by simpa only [Nat.zero_add] using hB)
      (by simpa only [Nat.zero_add] using hU)
      (hreal (Nat.zero_add _) _ _) w
    rw [htile]
    exact ⟨htD, htU, htstate, hanc.trans (hnode (Nat.zero_add _) _)⟩
  obtain ⟨htD, htU, htstate, hanc⟩ := hdesc
  let u : U.Node := ⟨0, ⟨tileNode t, htU⟩⟩
  have hleaf : stateOf U P u = (compilerLeaf C t).prePattern.state :=
    htstate.trans (hD.I2.2 (tileNode t) htD t hpiece.1 rfl)
  obtain ⟨he, _, heb⟩ := U.hierarchy.provider_inherited c u (g.height - 1) hanc
    g.incidence.val.leftFacet e hF hpiece.2.2
  have hb : U.hierarchy.birthParent u e he = U.hierarchy.parentNode c := heb.trans hFbirth
  have hserv : U.hierarchy.servingChild u e he = c := by
    have hheight := congrArg (fun x : U.Node => x.1) hb
    have hoff := (U.hierarchy.birthHeight_age_spec u e he).1
    have ho : (U.hierarchy.firstProvider u e he).1 = g.height - 1 := by
      change U.hierarchy.birthHeight u e he = g.height - 1 + 1 at hheight
      change U.hierarchy.birthHeight u e he = 0 + _ + 1 at hoff
      omega
    simpa only [CoherentHierarchy.servingChild, ho] using hanc
  have hframe : u.2.val.prototypeFrame u.1 = (compilerFrame C t).toAffineEquiv := by
    ext x
    rfl
  have hpoint : u.2.val.prototypeFrame u.1 (vertexPoint v) = p := by
    rw [hframe]
    exact hvp
  have hzero := routing_constant_step3_same_parent_ports_step3_provider_vertex
    (P := P) U u e he v hv (by rw [hserv, hpoint]; exact hp)
  have hrleaf : leafRecord (compilerLeaf C t) e.val = some (U.recordOf P u e he) := by
    unfold leafRecord
    rw [← hleaf]
    simp only [stateRecordAt, stateOf, u, dif_pos e.property,
      HonestSource.facetRecordOf, dif_neg he]
  have hheader : leafHeader (compilerLeaf C t) v.val e.val =
      some (U.headerOf P u e he v) := by
    unfold leafHeader
    rw [← hleaf]
    simp only [stateOf, u, dif_pos v.property, dif_pos e.property,
      HonestSource.headerRecordOf, dif_pos hv, dif_neg he, hzero, if_pos True.intro]
  have hvc : v.val ∈ (S.cx (tileNode t).ty).cells := (vertexCell v).property
  let j : EndSlot (compilerLeaf C t) := {
    facet := e
    record := U.recordOf P u e he
    record_eq := hrleaf
    type_eq := rfl
    facet_eq := rfl
    vertex := v
    onFacet := hv
    providerVertex := U.recordTau P u e he ⟨vertexCell v, hv⟩
    tau_vertex := by
      simp only [FacetRecord.tauAt, HonestSource.recordOf, u,
        dif_pos hvc, dif_pos hv]
      rfl
    provider_zero := hzero
    header := U.headerOf P u e he v
    header_eq := hheader
    packet := q
    packet_eq := (attachedPacket_spec hl g.incidence.val.leftFacet t e hpiece).trans hq }
  refine ⟨j, rfl, hvp, ?_⟩
  change U.headerOf P u e he v = _
  have hnorm (K : Set (E d)) : U.normalizeCone u K =
      (compilerFrame C t).linearIsometryEquiv.symm '' K := by
    rw [HonestSource.normalizeCone, hframe]
    rfl
  rw [← hparent]
  unfold HonestSource.headerOf
  rw [hb]
  simp only [show (U.hierarchy.parentNode c).1 = g.height - 1 + 1 from rfl,
    hpoint, Nat.add_sub_cancel, hnorm,
    routing_constant_step3_same_parent_ports_step3_header]

/-- Step 1 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3):
"a common-listed vertex q". Common listedness depends only on the birth
address, and so applies to both facets of a same-parent link. -/
private theorem routing_constant_step3_same_parent_ports_step1_transfer_listed
    {T : S.ι} (f f' : PrimitiveFacet S T) (h : f.birthAddress = f'.birthAddress)
    (p : E d) (hp : f.CommonListed p) : f'.CommonListed p := by
  rcases f with ⟨r, w, F, hF⟩
  rcases f' with ⟨r', w', F', hF'⟩
  obtain ⟨hr, hw⟩ := Sigma.mk.inj_iff.mp h
  dsimp only at hr hw
  subst r'
  have he : w = w' := eq_of_heq hw
  subst w'
  exact hp

/-- Step 4 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 3.3):
"inside the children of Q". A native descendant is contained in its
ancestor's closed carrier, by the exact substitution cover. -/
private theorem routing_constant_step3_same_parent_ports_step4_ground_subset
    (M N : FramedNode S) (n : ℕ) (h : M.IsDescendant 0 N n) :
    M.carrier 0 ⊆ N.carrier n := by
  obtain ⟨r, hr, w, hm⟩ := h
  have hrn : r = n := by omega
  subst r
  rw [hm]
  have hc := Set.subset_iUnion (fun w : S.RoleWord N.ty n =>
    (S.nativeTile N.ty n w).carrier 0) w
  rw [S.native_cover N.ty n] at hc
  have hc' : (S.nativeTile N.ty n w).frame ''
      (S.proto (S.nativeTile N.ty n w).ty).carrier ⊆ S.supertile n N.ty := by
    simpa [FramedNode.carrier, SubstSystem.supertile, placedSet] using hc
  simpa [FramedNode.carrier, FramedNode.move, SubstSystem.supertile,
    placedSet, SubstSystem.nativeTile, Set.image_image] using
      (Set.image_mono (f := N.frame) hc')

/-- Step 4 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 1.0(b), 3.3):
"the realised cone T_q Q". Finite polyhedral presentations transport
through the full affine prototype frame. -/
private theorem routing_constant_step3_same_parent_ports_step4_polyhedron_image
    (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) (hK : Polyhedron K) :
    Polyhedron (e '' K) := by
  classical
  obtain ⟨s, hs⟩ := hK
  have he (a : Finset (E d)) : convexHull ℝ (↑(a.image e) : Set (E d)) =
      e '' convexHull ℝ (a : Set (E d)) := by
    simpa only [Finset.coe_image] using
      (e.toAffineMap.image_convexHull (a : Set (E d))).symm
  refine ⟨s.image (fun a => a.image e), ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hs] at hx
    obtain ⟨a, ha, hx⟩ := mem_iUnion₂.mp hx
    apply mem_iUnion₂.mpr
    refine ⟨a.image e, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    rw [he]
    exact Set.mem_image_of_mem e hx
  · intro hy
    obtain ⟨a, ha, hy⟩ := mem_iUnion₂.mp hy
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
    subst a
    rw [he] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hs ▸ mem_iUnion₂.mpr ⟨b, hb, hx⟩, rfl⟩

/-- Step 4 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 1.0(b), 3.3):
"interior points in the recorded cone arbitrarily close to q". Near any
point, a polyhedron is contained in its translated radial tangent cone:
remove the finitely many closed convex pieces that do not contain the point. -/
private theorem routing_constant_step3_same_parent_ports_step4_local_sector
    (K : Set (E d)) (hK : Polyhedron K) (p : E d) :
    ∃ O : Set (E d), IsOpen O ∧ p ∈ O ∧
      K ∩ O ⊆ (fun u => p + u) '' tangentCone K p := by
  classical
  obtain ⟨s, hs⟩ := hK
  let bad := s.filter (fun a : Finset (E d) => p ∉ convexHull ℝ (a : Set (E d)))
  let O : Set (E d) := (⋃ a : Finset (E d), ⋃ (_ : a ∈ bad),
    convexHull ℝ (a : Set (E d)))ᶜ
  refine ⟨O, ?_, ?_, ?_⟩
  · exact (isClosed_biUnion_finset (s := bad)
      (fun a _ => a.finite_toSet.isCompact_convexHull.isClosed)).isOpen_compl
  · intro hp
    obtain ⟨a, ha, hpa⟩ := mem_iUnion₂.mp hp
    exact (Finset.mem_filter.mp ha).2 hpa
  · rintro y ⟨hy, hyO⟩
    rw [hs] at hy
    obtain ⟨a, ha, hya⟩ := mem_iUnion₂.mp hy
    have hpa : p ∈ convexHull ℝ (a : Set (E d)) := by
      by_contra h
      exact hyO (mem_iUnion₂.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, h⟩, hya⟩)
    refine ⟨y - p, ⟨1, zero_lt_one, fun t ht ht1 => ?_⟩, by module⟩
    rw [hs]
    refine mem_iUnion₂.mpr ⟨a, ha, ?_⟩
    have hm := (convex_convexHull ℝ (a : Set (E d))) hpa hya
      (by linarith : 0 ≤ 1 - t) ht.le (by ring : (1 - t) + t = 1)
    convert hm using 1 <;> module

/-- Step 4 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3, 3.3):
"Tiles along the facet at q have interior points in int(q + T_q Q)
arbitrarily close to q". Regular closedness and the local polyhedral
cone suffice; no packet or template is used in this geometric assertion. -/
private theorem routing_constant_step3_same_parent_ports_step4_approaches
    (t : PlacedMarkedTile (systemM S P C)) (Q : FramedNode S) (m : ℕ)
    (hsub : t.carrier ⊆ Q.carrier m) (p : E d) (hp : p ∈ t.carrier) :
    Parser.ApproachesSector t p ((fun u => p + u) '' tangentCone (Q.carrier m) p) := by
  have hpoly : Polyhedron (Q.carrier m) := by
    have h := routing_constant_step3_same_parent_ports_step4_polyhedron_image
      (Q.prototypeFrame m) _ (S.proto Q.ty).polyhedral
    simpa only [FramedNode.carrier, FramedNode.prototypeFrame,
      SubstSystem.supertile, placedSet, Set.image_image] using h
  obtain ⟨O, hO, hpO, hlocal⟩ :=
    routing_constant_step3_same_parent_ports_step4_local_sector (Q.carrier m) hpoly p
  have hreg : closure (interior t.carrier) = t.carrier := by
    obtain ⟨B, _, φ, hcarrier, _⟩ := t.realization
    rw [hcarrier]
    change closure (interior (φ.toHomeomorph '' B.carrier)) = φ.toHomeomorph '' B.carrier
    rw [← φ.toHomeomorph.image_interior, ← φ.toHomeomorph.image_closure, B.regularClosed]
  have hpcl : p ∈ closure (interior t.carrier) := hreg.symm ▸ hp
  intro ε hε
  obtain ⟨x, hxO, hxt⟩ := mem_closure_iff.mp hpcl (O ∩ ball p ε)
    (hO.inter isOpen_ball) ⟨hpO, mem_ball_self hε⟩
  have hin : interior t.carrier ∩ O ⊆
      (fun u => p + u) '' tangentCone (Q.carrier m) p :=
    fun _ hx => hlocal ⟨hsub (interior_subset hx.1), hx.2⟩
  have hxint : x ∈ interior ((fun u => p + u) '' tangentCone (Q.carrier m) p) := by
    apply interior_mono hin
    rw [(isOpen_interior.inter hO).interior_eq]
    exact ⟨hxt, hxO.1⟩
  exact ⟨x, ⟨hxt, hxint⟩, hxO.2⟩

open private honest_rows_step1_cont_geometry_step1_spans
  honest_rows_step4_cont_packet_step1_germ
  honest_rows_step4_cont_packet_step3_relint_transfer
  honest_rows_step6_end_E2_step3_placed_cell
  restrictionOp_source_step5_cell_closure from Enforce.State.Rows in
open private host_step_step1_seed_step5_trace_step5_placed_span
  host_step_step2_strand_step3_no_false_endpoint_step3_facet_port_step3_identify
  from Enforce.Parser.Host in
/-- Step 5 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3, 3.10):
"the geometry of θ_q identifies f₁- and f₂-ports (faces of the recorded
cones)". In a complete honest END geometry with the actual birth header,
a listed facet of one of its tiles lying on a first-generation facet is
one of its primitive ports. This is a statement about positioned geometry
only, with no output labels, rows, states, or packet equality. -/
private theorem routing_constant_step3_same_parent_ports_step5_identify_port
    (g : Parser.BornFacet P) (p : E d) (φ : Iso d)
    (Z : EndGeometry P) (hZ : Z ∈ honestEndGeometries S P)
    (hheader : Z.header = routing_constant_step3_same_parent_ports_step3_header
      g.birth (g.height - 1) φ p)
    (hapex : φ (vertexPoint Z.vertex) = p)
    (M : FramedNode S) (hM : M ∈ Z.tiles)
    (e : FacetName S M.ty) (v : VertexName S M.ty)
    (hv : v.val.carrier ⊆ e.val.carrier)
    (hvp : (M.frame.trans φ) (vertexPoint v) = p)
    (hdesc : (M.move φ).IsDescendant 0 g.leftNode (g.height - 1))
    (hfacet : (M.move φ).cell 0 e.val ⊆ g.carrier) :
    ∃ a ∈ Z.primitivePorts, a.tile = M ∧ a.facet.val = e.val := by
  classical
  have hheight : g.height - 1 + 1 = g.height := by have := g.positive; omega
  let χ := P.incidencePlacement g.birth g.height g.incidence
  let F : Cell d := g.incidence.val.leftFacet.val
  let K : Set (E d) := χ '' F.carrier
  let T : Set (E d) := tangentCone K p
  have hK : g.carrier = K := rfl
  have hpv : vertexPoint v ∈ e.val.carrier := by
    apply hv
    rw [vertexPoint_spec v]
    exact Set.mem_singleton _
  have hpcell : p ∈ (M.move φ).cell 0 e.val := by
    rw [← hvp]
    exact ⟨vertexPoint v, hpv, rfl⟩
  have hpK : p ∈ K := hfacet hpcell
  -- the primitive cone of the actual birth header
  have hG : Z.header.primitiveCones g.incidence =
      some (φ.linearIsometryEquiv.symm '' T) := by
    rw [hheader]
    simp only [routing_constant_step3_same_parent_ports_step3_header, hheight]
    rw [if_pos ⟨g.parent_type, hpK⟩]
  -- the translated cone agrees with the facet near `p`
  have hgerm := honest_rows_step4_cont_packet_step1_germ
    (honest_rows_step6_end_E2_step3_placed_cell χ F).1 p
  obtain ⟨V, hVsub, hV, hpV⟩ := _root_.mem_nhds_iff.mp hgerm
  let L : Set (E d) := (fun u => p + u) '' T
  have heq : K ∩ V = L ∩ V := by
    ext x
    constructor
    · rintro ⟨hx, hxV⟩
      refine ⟨⟨x - p, (hVsub hxV).mp hx, by abel⟩, hxV⟩
    · rintro ⟨⟨u, hu, rfl⟩, hxV⟩
      refine ⟨(hVsub hxV).mpr ?_, hxV⟩
      simpa only [add_sub_cancel_left] using hu
  have hspan : affineSpan ℝ K = affineSpan ℝ L :=
    (host_step_step1_seed_step5_trace_step5_placed_span χ F p hpK).symm
  have hdim : e.val.dim = F.dim :=
    (Finset.mem_filter.mp e.property).2.trans
      (Finset.mem_filter.mp g.incidence.val.leftFacet.property).2.symm
  have hrel : relint ((M.move φ).cell 0 e.val) ⊆ relint K :=
    (honest_rows_step1_cont_geometry_step1_spans ((M.move φ).prototypeFrame 0) χ
      e.val F hdim hfacet).2
  have hcl : p ∈ closure (relint ((M.move φ).cell 0 e.val)) := by
    rw [restrictionOp_source_step5_cell_closure]
    exact hpcell
  have hcone : (fun w => φ (vertexPoint Z.vertex) + φ.linearIsometryEquiv w) ''
      (φ.linearIsometryEquiv.symm '' T) = L := by
    rw [Set.image_image, hapex]
    simp only [LinearIsometryEquiv.apply_symm_apply, L]
  apply host_step_step2_strand_step3_no_false_endpoint_step3_facet_port_step3_identify
    φ Z hZ g.incidence _ hG M hM e
  rw [hcone, hapex, _root_.mem_closure_iff]
  intro U hU hpU
  obtain ⟨y, hyUV, hy⟩ := _root_.mem_closure_iff.mp hcl (U ∩ V) (hU.inter hV) ⟨hpU, hpV⟩
  exact ⟨y, hyUV.1, hy,
    honest_rows_step4_cont_packet_step3_relint_transfer hspan hV heq (hrel hy) hyUV.2⟩

/-- Step 6 of the V4 proof of `routing_constant_step3_same_parent_ports` (V4 8.3, 2.17, 3.3):
"Theorem 2.17 and Lemma 3.3 put the ports ... into the endpoint template".
Coverage places a given actual native facet piece in the template, the
geometric port identification locates its port, and boundary constancy
reads its supplied packet. No equality of packet slots is used. -/
private theorem routing_constant_step3_same_parent_ports_step6_read_port
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Parser.BornFacet P) (p : E d)
    (t₀ : PlacedMarkedTile (systemM S P C)) (ht₀ : t₀ ∈ Y.tiles)
    (j : EndSlot (compilerLeaf C t₀)) (T : EndTemplate j)
    (hrow : endRow T) (hactual : TemplateOccurs C Y (compilerFrame C t₀) T.configuration)
    (hp : Compiler.endVertex (compilerFrame C t₀) j = p)
    (hh : j.header = routing_constant_step3_same_parent_ports_step3_header
      g.birth (g.height - 1) (compilerFrame C t₀) p)
    (t : PlacedMarkedTile (systemM S P C)) (e : FacetName S (tileNode t).ty)
    (v : VertexName S (tileNode t).ty)
    (hpiece : Parser.IsFacetPiece Y (g.height - 1) g.leftNode
      g.incidence.val.leftFacet t e)
    (hv : v.val.carrier ⊆ e.val.carrier) (hvp : compilerFrame C t (vertexPoint v) = p)
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (q : Packet P) (hq : g.packet hl = some q) :
    ∃ (a : PrimitivePort P) (u : LeafType P), a ∈ T.geometry.primitivePorts ∧
      (a.tile, u) ∈ T.configuration.tiles ∧ leafPacket u a.facet.val = some q := by
  classical
  have hcarrier : (tileNode t).carrier 0 = t.carrier := by
    rw [compilerFrame_carrier C t]
    simp [tileNode, FramedNode.carrier, SubstSystem.supertile, placedSet]
  have hsub : t.carrier ⊆ g.birth.carrier g.height := by
    rw [← hcarrier]
    exact routing_constant_step3_same_parent_ports_step4_ground_subset _ _ _
      (Parser.descendant_trans _ _ _ _ _ _ hpiece.2.1 g.sides_descendant.1)
  have hpt : p ∈ t.carrier := by
    rw [← hvp, compilerFrame_carrier C t]
    apply Set.mem_image_of_mem
    exact routing_constant_step3_same_parent_ports_step1_cell_subset _ v.val
      (vertexCell v).property (by rw [vertexPoint_spec]; exact Set.mem_singleton _)
  have hheight : g.height - 1 + 1 = g.height := by have := g.positive; omega
  have hsector : Compiler.endSector (compilerFrame C t₀) j =
      (fun u => p + u) '' tangentCone (g.birth.carrier g.height) p := by
    simp only [Compiler.endSector, hp, hh,
      routing_constant_step3_same_parent_ports_step3_header, Set.image_image,
      LinearIsometryEquiv.apply_symm_apply, hheight]
  have hnear : Parser.ApproachesSector t (Compiler.endVertex (compilerFrame C t₀) j)
      (Compiler.endSector (compilerFrame C t₀) j) := by
    rw [hp, hsector]
    exact routing_constant_step3_same_parent_ports_step4_approaches t g.birth g.height hsub p hpt
  obtain ⟨⟨⟨M, l⟩, hMl, hplaced⟩, _, _⟩ :=
    trigger_coverage Y hY t₀ ht₀ j T.configuration ⟨T, rfl, hrow⟩ hactual t hpiece.1 hnear
  have hleaf : compilerLeaf C t = l := by
    rw [hplaced]
    exact (compiler_decode_unique C _ _).1
  have hφ : compilerFrame C t = M.frame.trans (compilerFrame C t₀) := by
    rw [hplaced]
    exact (compiler_decode_unique C _ _).2
  have hnode : tileNode t = M.move (compilerFrame C t₀) := by
    apply FramedNode.ext
    · change (compilerLeaf C t).prototype = M.ty
      rw [hleaf]
      exact (T.configuration.types_match _ hMl).symm
    · exact hφ
  have hM : M ∈ T.geometry.tiles := by
    rw [← T.tiles_eq]
    exact Finset.mem_image.mpr ⟨(M, l), hMl, rfl⟩
  have hvertex : vertexPoint T.geometry.vertex = vertexPoint j.vertex := by
    apply Set.singleton_injective
    exact (vertexPoint_spec T.geometry.vertex).symm.trans
      ((congrArg Cell.carrier T.vertex_eq).trans (vertexPoint_spec j.vertex))
  have hapex : compilerFrame C t₀ (vertexPoint T.geometry.vertex) = p := by
    rw [hvertex]
    exact hp
  have hty : (tileNode t).ty = M.ty := by
    simpa only [FramedNode.move] using congrArg FramedNode.ty hnode
  let e' : FacetName S M.ty := ⟨e.val, by rw [← hty]; exact e.property⟩
  let v' : VertexName S M.ty := ⟨v.val, by rw [← hty]; exact v.property⟩
  have hv' : vertexPoint v' = vertexPoint v := by
    apply Set.singleton_injective
    exact (vertexPoint_spec v').symm.trans (vertexPoint_spec v)
  obtain ⟨a, ha, haM, hae⟩ :=
    routing_constant_step3_same_parent_ports_step5_identify_port g p (compilerFrame C t₀)
      T.geometry T.honest_geometry (T.header_eq.trans hh) hapex M hM e' v' hv
      (by rw [hv', ← hφ]; exact hvp)
      (by rw [← hnode]; exact hpiece.2.1)
      (by rw [← hnode]; exact hpiece.2.2.trans_eq g.sides_carrier.1)
  refine ⟨a, l, ha, ?_, ?_⟩
  · rw [haM]
    exact hMl
  · rw [hae, ← hleaf]
    exact (attachedPacket_spec hl g.incidence.val.leftFacet t e hpiece).trans hq

/-- Step 3 of the V4 proof of `routing_constant` (V4 8.3):
"Theorem 2.17 and Lemma 3.3 put the ports of both facets into the endpoint
template." For a same-parent link, construct one actual END template and
primitive ports reading the two attached packets. This includes a birth at
the new parent: its children's age-one records come from their first letters.
No equality of packet slots is part of this geometric obligation. -/
private theorem routing_constant_step3_same_parent_ports
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (f f' : PrimitiveFacet S N.ty) (g g' : Parser.BornFacet P)
    (hg : routing_constant_step1_realizes N (n + 1) f g)
    (hg' : routing_constant_step1_realizes N (n + 1) f' g')
    (hlink : SameParentLink f f')
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (hl' : Parser.BoundaryPackets Y (g'.height - 1) g'.leftNode)
    (q q' : Packet P) (hq : g.packet hl = some q) (hq' : g'.packet hl' = some q') :
    ∃ t ∈ Y.tiles, ∃ (slot : EndSlot (compilerLeaf C t)) (T : EndTemplate slot),
      TemplateOccurs C Y (compilerFrame C t) T.configuration ∧ endRow T ∧
        ∃ (a b : PrimitivePort P) (u v : LeafType P),
          a ∈ T.geometry.primitivePorts ∧ b ∈ T.geometry.primitivePorts ∧
          (a.tile, u) ∈ T.configuration.tiles ∧ (b.tile, v) ∈ T.configuration.tiles ∧
          leafPacket u a.facet.val = some q ∧ leafPacket v b.facet.val = some q' := by
  obtain ⟨hh, hb⟩ := routing_constant_step3_same_parent_ports_step1_same_birth
    N (n + 1) f f' g g' hg hg' hlink.1
  obtain ⟨x, hx, hx', hlisted⟩ := hlink.2
  let p := N.prototypeFrame (n + 1) x
  have hp : p ∈ g.carrier := by
    rw [hg.2.2]
    exact Set.mem_image_of_mem _ hx.1
  have hp' : p ∈ g'.carrier := by
    rw [hg'.2.2]
    exact Set.mem_image_of_mem _ hx'.1
  have hlists : g.leftNode.Lists (g.height - 1) p :=
    routing_constant_step3_same_parent_ports_step1_left_listed N (n + 1) f g hg x hx.1 hlisted
  have hlists' : g'.leftNode.Lists (g'.height - 1) p :=
    routing_constant_step3_same_parent_ports_step1_left_listed N (n + 1) f' g' hg' x hx'.1
      (routing_constant_step3_same_parent_ports_step1_transfer_listed f f' hlink.1 x hlisted)
  have hbirth := routing_constant_step1_descendant N (n + 1) f g hg
  have hbirth' := routing_constant_step1_descendant N (n + 1) f' g' hg'
  have hleft (G : Parser.BornFacet P)
      (hG : G.birth.IsDescendant G.height N (n + 1)) :
      IsBlock Y (G.height - 1) G.leftNode := by
    have hle := Parser.descendant_height_le _ _ _ _ hG
    have hpos := G.positive
    exact D.geometry.node_actual _ _ (Parser.assembled_inner_mem D N A _ _ (by omega)
      (Parser.descendant_trans _ _ _ _ _ _ G.sides_descendant.1 hG))
  obtain ⟨t, e, v, ht, hv, hvp⟩ :=
    routing_constant_step3_same_parent_ports_step2_native_piece Y (g.height - 1)
      ⟨g.leftNode, hleft g hbirth⟩ g.incidence.val.leftFacet p hlists
      (by change p ∈ g.leftNode.cell (g.height - 1) g.incidence.val.leftFacet.val
          rw [g.sides_carrier.1]; exact hp)
  obtain ⟨t', e', v', ht', hv', hvp'⟩ :=
    routing_constant_step3_same_parent_ports_step2_native_piece Y (g'.height - 1)
      ⟨g'.leftNode, hleft g' hbirth'⟩ g'.incidence.val.leftFacet p hlists'
      (by change p ∈ g'.leftNode.cell (g'.height - 1) g'.incidence.val.leftFacet.val
          rw [g'.sides_carrier.1]; exact hp')
  obtain ⟨j, _, hj, hheader⟩ :=
    routing_constant_step3_same_parent_ports_step3_inherited_slot D hD N A g hbirth p
      hlists t e v ht hv hvp hl q hq
  obtain ⟨θ, hθ, _, hactual⟩ := compiler_events C Y hY t ht.1 (.end_ j)
  obtain ⟨T, rfl, hrow⟩ := hθ
  obtain ⟨a, u, ha, hu, hqu⟩ := routing_constant_step3_same_parent_ports_step6_read_port
    Y hY g p t ht.1 j T hrow hactual hj hheader t e v ht hv hvp hl q hq
  have hheader' : j.header = routing_constant_step3_same_parent_ports_step3_header
      g'.birth (g'.height - 1) (compilerFrame C t) p := by
    simpa only [hh, hb] using hheader
  obtain ⟨b, w, hbport, hw, hqw⟩ := routing_constant_step3_same_parent_ports_step6_read_port
    Y hY g' p t ht.1 j T hrow hactual hj hheader' t' e' v' ht' hv' hvp' hl' q' hq'
  exact ⟨t, ht.1, j, T, hactual, hrow, a, b, u, w, ha, hbport, hu, hw, hqu, hqw⟩

/-- Step 3 of the V4 proof of `routing_constant` (V4 8.3):
"Row (E4) equates their slots". Once both primitive ports are identified,
E4 gives equality at every common PRESENT index. -/
private theorem routing_constant_step3_same_parent_agree
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (f f' : PrimitiveFacet S N.ty) (g g' : Parser.BornFacet P)
    (hg : routing_constant_step1_realizes N (n + 1) f g)
    (hg' : routing_constant_step1_realizes N (n + 1) f' g')
    (hlink : SameParentLink f f')
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (hl' : Parser.BoundaryPackets Y (g'.height - 1) g'.leftNode)
    (q q' : Packet P) (hq : g.packet hl = some q) (hq' : g'.packet hl' = some q') :
    AgreePresent q q' := by
  obtain ⟨t, ht, slot, T, _, hrow, a, b, u, v, ha, hb, hu, hv, hqu, hqv⟩ :=
    routing_constant_step3_same_parent_ports Y hY n hn D hD N A f f' g g'
      hg hg' hlink hl hl' q q' hq hq'
  obtain ⟨p, hp, _, hagree⟩ := hrow.2.2.2.1 a ha u hu
  have he : p = q := Option.some.inj (hp.symm.trans hqu)
  exact he ▸ hagree b hb v hv q' hqv

/-- Step 1 of the V4 proof of `routing_constant_step4_inherited_record` (V4 1.3):
"a facet e of Q contained in g". Relative interiors commute with the full
affine frames, including the anisotropic expansion. -/
private theorem routing_constant_step4_inherited_record_step1_relint_image
    (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
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

/-- Step 1 of the V4 proof of `routing_constant_step4_inherited_record` (V4 1.3):
"a facet e of Q contained in g". Equal facet dimensions make containment
preserve relative interiors, even when the two facets have different frames. -/
private theorem routing_constant_step4_inherited_record_step1_relint_mono
    (M N : FramedNode S) (m n : ℕ)
    (e : FacetName S M.ty) (f : FacetName S N.ty)
    (hsub : M.cell m e.val ⊆ N.cell n f.val) :
    relint (M.cell m e.val) ⊆ relint (N.cell n f.val) := by
  have hdim (Q : FramedNode S) (h : ℕ) (F : FacetName S Q.ty) :
      Module.finrank ℝ (affineSpan ℝ (Q.cell h F.val)).direction = d - 1 := by
    change Module.finrank ℝ
      (affineSpan ℝ ((Q.prototypeFrame h).toAffineMap '' F.val.carrier)).direction = d - 1
    rw [← AffineSubspace.map_span (Q.prototypeFrame h).toAffineMap,
      AffineSubspace.map_direction]
    exact ((Q.prototypeFrame h).linear.finrank_map_eq _).trans
      (F.val.flat.dimension.trans (Finset.mem_filter.mp F.property).2)
  have hspan := affineSpan_mono ℝ hsub
  have heq : affineSpan ℝ (M.cell m e.val) = affineSpan ℝ (N.cell n f.val) := by
    apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le _ _ hspan
    · exact Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hspan)
        ((hdim M m e).trans (hdim N n f).symm)
    · exact (e.val.flat.connected.nonempty.image (M.prototypeFrame m)).mono
        (subset_affineSpan ℝ _)
  unfold relint intrinsicInterior
  rw [heq]
  exact image_mono (interior_mono (preimage_mono hsub))

/-- Step 1 of the V4 proof of `routing_constant_step4_inherited_record` (V4 1.3):
"a facet e of Q" lies on the boundary of its framed owner. -/
private theorem routing_constant_step4_inherited_record_step1_boundary
    (N : FramedNode S) (n : ℕ) (f : FacetName S N.ty) :
    N.cell n f.val ⊆ frontier (N.carrier n) := by
  let h := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  have hcar : N.carrier n = h '' (S.proto N.ty).carrier := by
    simp [h, FramedNode.carrier, FramedNode.prototypeFrame, SubstSystem.supertile,
      placedSet, Set.image_image]
  rw [hcar, ← h.image_frontier]
  apply image_mono
  rw [← (S.cx N.ty).carriers_cover]
  exact subset_iUnion₂_of_subset f.val (Finset.mem_filter.mp f.property).1 Subset.rfl

/-- Step 1 of the V4 proof of `routing_constant_step4_inherited_record` (V4 1.0(a)):
"the child of Q'" is the closure of its interior in its actual frame. -/
private theorem routing_constant_step4_inherited_record_step1_regular
    (N : FramedNode S) (n : ℕ) : closure (interior (N.carrier n)) = N.carrier n := by
  let h := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  have hcar : N.carrier n = h '' (S.proto N.ty).carrier := by
    simp [h, FramedNode.carrier, FramedNode.prototypeFrame, SubstSystem.supertile,
      placedSet, Set.image_image]
  rw [hcar, ← h.image_interior, ← h.image_closure, (S.proto N.ty).regularClosed]

/-- Step 2 of the V4 proof of `routing_constant_step4_inherited_record` (V4 1.3--1.4):
"start with the age-one record in the child of Q'". A descendant facet
contained in a sibling facet lifts to that same whole facet in its own child.
Facet dichotomy excludes the interior case; sibling conformity identifies the names. -/
private theorem routing_constant_step4_inherited_record_step2_child_facet
    (N M : FramedNode S) (n b : ℕ) (i j : S.I N.ty)
    (hdesc : M.IsDescendant b (N.child n i) n)
    (e : FacetName S M.ty) (f : FacetName S (N.child n j).ty)
    (he : M.cell b e.val ⊆ (N.child n j).cell n f.val) :
    ∃ F : FacetName S (N.child n i).ty,
      M.cell b e.val ⊆ (N.child n i).cell n F.val ∧
        (N.child n i).cell n F.val = (N.child n j).cell n f.val := by
  classical
  by_cases hij : i = j
  · subst j
    exact ⟨f, he, rfl⟩
  have hdisj : Disjoint (interior ((N.child n i).carrier n))
      (interior ((N.child n j).carrier n)) := by
    let h := ((S.σ ^ n).toContinuousLinearEquiv.toHomeomorph).trans N.frame.toHomeomorph
    have hcar (i : S.I N.ty) : (N.child n i).carrier n =
        h '' placedSet (S.child N.ty i).frame (S.proto (S.child N.ty i).ty).carrier := by
      simp only [FramedNode.carrier, FramedNode.child, SubstSystem.supertile,
        placedSet, Set.image_image]
      congr 1
      funext x
      change N.frame (S.placeChild n i ((S.σ ^ n) x)) =
        N.frame ((S.σ ^ n) ((S.child N.ty i).frame x))
      congr 1
      rw [S.placeChild_apply]
      simp [linearConj, Child.frame, rigidMotion, zpow_neg,
        LinearEquiv.mul_apply, ← map_add]
    rw [hcar i, hcar j, ← h.image_interior, ← h.image_interior]
    exact Set.disjoint_image_of_injective h.injective (S.children_disjoint N.ty hij)
  have hne : (relint (M.cell b e.val)).Nonempty := by
    rw [FramedNode.cell, routing_constant_step4_inherited_record_step1_relint_image]
    exact e.val.flat.relint_nonempty.image _
  obtain ⟨x, hx⟩ := hne
  rcases facet_dichotomy (N.child n i) M n b hdesc e with ⟨F, hF, _⟩ | hint
  · refine ⟨F, hF, ?_⟩
    exact sibling_minimalCell_eq N n i j hij x (facetCell F) (facetCell f)
      (routing_constant_step4_inherited_record_step1_relint_mono _ _ _ _ e F hF hx)
      (routing_constant_step4_inherited_record_step1_relint_mono _ _ _ _ e f he hx)
  · have hd := hdisj.closure_right isOpen_interior
    rw [routing_constant_step4_inherited_record_step1_regular] at hd
    have hclosed : IsClosed ((N.child n j).carrier n) := by
      rw [← routing_constant_step4_inherited_record_step1_regular]
      exact isClosed_closure
    exact False.elim (Set.disjoint_left.mp hd (hint hx)
      (hclosed.frontier_subset
        (routing_constant_step4_inherited_record_step1_boundary _ _ f
          (he (intrinsicInterior_subset hx)))))

/-- Step 3 of the V4 proof of `routing_constant_step4_inherited_record` (V4 8.3):
"restrict down to Q". In an honest hierarchy the exact descendant address
recovers its ancestor, including its full frame. -/
private theorem routing_constant_step4_inherited_record_step3_ancestor
    (U : HonestSource S) (h r : ℕ) (N : FramedNode S)
    (hN : N ∈ U.hierarchy.nodes (h + r)) (w : S.RoleWord N.ty r)
    (hc : (S.descendantNode N.ty h r w).move N.frame ∈ U.hierarchy.nodes h) :
    U.hierarchy.ancestor ⟨h, ⟨(S.descendantNode N.ty h r w).move N.frame, hc⟩⟩ r =
      ⟨h + r, ⟨N, hN⟩⟩ := by
  induction r generalizing N with
  | zero =>
    simp [CoherentHierarchy.ancestor, SubstSystem.descendantNode, FramedNode.move]
  | succ r ih =>
    have hchild := U.hierarchy.children_mem (h + r) N
      (by simpa only [Nat.add_assoc] using hN) w.1
    have hc' : (S.descendantNode (N.child (h + r) w.1).ty h r w.2).move
        (N.child (h + r) w.1).frame ∈ U.hierarchy.nodes h := hc
    have hi := ih (N.child (h + r) w.1) hchild w.2 hc'
    rw [← U.hierarchy.ancestor_add]
    change U.hierarchy.parentNode (U.hierarchy.ancestor _ r) = _
    have he : (⟨h, ⟨(S.descendantNode N.ty h (r + 1) w).move N.frame, hc⟩⟩ : U.Node) =
        ⟨h, ⟨(S.descendantNode (N.child (h + r) w.1).ty h r w.2).move
          (N.child (h + r) w.1).frame, hc'⟩⟩ := rfl
    rw [he, hi]
    apply Sigma.ext
    · simp only [CoherentHierarchy.parentNode, Nat.add_assoc]
    · apply heq_of_eq
      apply Subtype.ext
      exact (U.hierarchy.parent_unique (h + r) _ N hN ⟨w.1, rfl⟩).symm

/-- Step 4 of the V4 proof of `routing_constant_step4_inherited_record` (V4 8.3):
"using (I2)" and "the children's first letters". Realize the old child
containing the node, descend using the child equations, and recover the newly
assembled parent from the child's first role. -/
private theorem routing_constant_step4_inherited_record_step4_realization
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (hD : Inv D) (N : FramedNode S)
    (A : Parser.AssembledParent D N) (b : ℕ) (M : FramedNode S)
    (hM : M ∈ D.geometry.nodes b) (hb : b < n + 1)
    (hdesc : M.IsDescendant b N (n + 1)) :
    ∃ (U : HonestSource S) (hMU : M ∈ U.hierarchy.nodes b),
      N ∈ U.hierarchy.nodes (n + 1) ∧
        stateOf U P ⟨b, ⟨M, hMU⟩⟩ = D.stateAt b M hM := by
  obtain ⟨r, hr, w, hw⟩ := hdesc
  have hrpos : 0 < r := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
  have hn : n = b + r := by omega
  subst n
  let B := N.child (b + r) w.1
  have hB : B ∈ D.geometry.nodes (b + r) := by
    change N.child (b + r) w.1 ∈ D.geometry.nodes (b + r)
    rw [← A.child_eq w.1]
    exact D.geometry.root_mem (A.children w.1).val (A.children w.1).property
  obtain ⟨U, hU, hs⟩ := routing_constant_step2_source_realization
    (D.stateAt (b + r) B hB) (D.state_honest _ _)
    B (b + r) (hD.node_type_residue _ _ hB).1 (hD.node_type_residue _ _ hB).2
  have hnode : (S.descendantNode B.ty b r w.2).move B.frame = M := by
    rw [hw]
    simp [B, SubstSystem.descendantNode, FramedNode.move, FramedNode.child,
      AffineIsometryEquiv.trans_assoc]
  have hdown := routing_constant_step2_source_descent D hD U b r B hB hU hs w.2
  dsimp only at hdown
  rw [hnode] at hdown
  obtain ⟨_, hMU, hstate, _⟩ := hdown
  let c : U.Node := ⟨b + r, ⟨B, hU⟩⟩
  have hrole : U.hierarchy.nodeRole c = ⟨N.ty, w.1⟩ := by
    change (stateOf U P c).address ⟨0, P.k_pos⟩ = _
    rw [hs]
    have h := A.first_letters w.1
    simpa only [firstRole, DecodedLevel.blockState, A.child_eq] using h
  have hparent : (U.hierarchy.parentNode c).2.val = N := by
    have hc := U.hierarchy.child_eq (b + r) c.2
    exact routing_constant_step2_parent_from_child (U.hierarchy.parentNode c).2.val N
      (b + r) (U.hierarchy.role (b + r) c.2) w.1 hrole hc.symm
  refine ⟨U, hMU, ?_, hstate⟩
  simpa only [hparent] using (U.hierarchy.parentNode c).2.property

/-- Step 5 of the V4 proof of `routing_constant_step4_inherited_record` (V4 2.3):
"Internal case ... birth parent B, age 1". A born facet's relative interior
is inside its actual birth parent, after applying the full prototype frame. -/
private theorem routing_constant_step4_inherited_record_step5_internal
    (g : Parser.BornFacet P) :
    relint g.carrier ⊆ interior (g.birth.carrier g.height) := by
  let T := S.σ.symm.toAffineEquiv.trans (g.birth.prototypeFrame g.height)
  have hcell : g.carrier = T '' g.incidence.val.positioned := by
    simp only [Parser.BornFacet.carrier, Params.incidencePlacement,
      PrimitiveIncidence.positioned, placedSet, Set.image_image]
    rfl
  have hcar : g.birth.carrier g.height = T '' S.supertile 1 g.incidence.val.ty := by
    rw [g.parent_type]
    simp [T, FramedNode.carrier, FramedNode.prototypeFrame, SubstSystem.supertile,
      placedSet, Set.image_image]
  rw [hcell, routing_constant_step4_inherited_record_step1_relint_image, hcar]
  change T.toHomeomorphOfFiniteDimensional '' _ ⊆
    interior (T.toHomeomorphOfFiniteDimensional '' _)
  rw [← Homeomorph.image_interior]
  exact image_mono g.incidence.val.internal

/-- Step 6 of the V4 proof of `routing_constant_step4_inherited_record` (V4 1.7(c), 2.3):
"same incidence ... and provider; age min(age+1,C)". Restriction from an
internal serving facet preserves its birth and canonical incidence; its exact
height difference gives the age whenever the cap is not reached. -/
private theorem routing_constant_step4_inherited_record_step6_restrict
    (U : HonestSource S) (c q : U.Node) (a : ℕ)
    (hanc : U.hierarchy.ancestor q a = c)
    (F : FacetName S c.2.val.ty) (e : FacetName S q.2.val.ty)
    (he : q.2.val.cell q.1 e.val ⊆ c.2.val.cell c.1 F.val)
    (hint : relint (c.2.val.cell c.1 F.val) ⊆
      interior ((U.hierarchy.parentNode c).2.val.carrier (U.hierarchy.parentNode c).1))
    (ι : P.Incidence) (hty : ι.val.ty = (U.hierarchy.parentNode c).2.val.ty)
    (hpos : c.2.val.cell c.1 F.val =
      P.incidencePlacement (U.hierarchy.parentNode c).2.val
        (U.hierarchy.parentNode c).1 ι '' ι.val.leftFacet.val.carrier)
    (hcap : c.1 + 1 - q.1 < P.C) :
    ∃ r : FacetRecord P, stateRecordAt (stateOf U P q) e.val = some r ∧
      r.incidence = ι ∧ r.age.val = c.1 + 1 - q.1 := by
  obtain ⟨hF, hcarrier, hbirth, _⟩ := U.hierarchy.restriction_det_internal c F hint
  obtain ⟨hefinite, hprovider, hbirth'⟩ :=
    U.hierarchy.provider_inherited c q a hanc F e hF he
  have hb : U.hierarchy.birthParent q e hefinite = U.hierarchy.parentNode c :=
    hbirth'.trans hbirth
  have hi : U.recordIncidence P q e hefinite = ι := by
    have hs := U.hierarchy.providerIncidence_spec q e hefinite
    apply P.canonical_unique
    constructor
    · exact hs.1.trans ((congrArg (fun N : U.Node => N.2.val.ty) hb).trans hty.symm)
    · have h := hprovider.trans (hcarrier.trans hpos)
      rw [hs.2.2.2] at h
      change (U.hierarchy.birthParent q e hefinite).2.val.prototypeFrame
          (U.hierarchy.birthParent q e hefinite).1 ''
          (S.σ.symm '' (U.hierarchy.providerIncidence q e hefinite).positioned) = _ at h
      rw [hb] at h
      have hp : P.incidencePlacement (U.hierarchy.parentNode c).2.val
          (U.hierarchy.parentNode c).1 ι '' ι.val.leftFacet.val.carrier =
          (U.hierarchy.parentNode c).2.val.prototypeFrame (U.hierarchy.parentNode c).1 ''
            (S.σ.symm '' ι.val.positioned) := by
        simp only [Params.incidencePlacement, PrimitiveIncidence.positioned, placedSet,
          Set.image_image]
        rfl
      rw [hp] at h
      exact S.σ.symm.injective.image_injective
        (((U.hierarchy.parentNode c).2.val.prototypeFrame
          (U.hierarchy.parentNode c).1).injective.image_injective h)
  refine ⟨U.recordOf P q e hefinite, ?_, hi, ?_⟩
  · simp only [stateRecordAt, stateOf, dif_pos e.property, HonestSource.facetRecordOf,
      dif_neg hefinite]
  · change min (U.hierarchy.birthHeight q e hefinite - q.1) P.C = _
    rw [CoherentHierarchy.birthHeight, hb]
    exact min_eq_left hcap.le

/-- Step 4 of the V4 proof of `routing_constant` (V4 8.3):
"start with the age-one record in the child of Q' and restrict down to Q
using (I2) and Proposition 2.3". The actual descendant boundary facet has
the higher birth's incidence and exact age. The strict age-cap hypothesis
excludes saturation, and the strict height inequality excludes age zero.
The higher birth may be the newly assembled parent. -/
private theorem routing_constant_step4_inherited_record
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (hD : Inv D) (N : FramedNode S)
    (A : Parser.AssembledParent D N) (b : ℕ) (M : FramedNode S)
    (hM : M ∈ D.geometry.nodes b) (g : Parser.BornFacet P)
    (hbirth : g.birth.IsDescendant g.height N (n + 1))
    (hdesc : M.IsDescendant b g.birth g.height) (hb : b < g.height)
    (e : FacetName S M.ty) (he : M.cell b e.val ⊆ g.carrier)
    (huncapped : g.height - b < P.C) :
    ∃ r : FacetRecord P, stateRecordAt (D.stateAt b M hM) e.val = some r ∧
      r.incidence = g.incidence ∧ r.age.val = g.height - b := by
  have hle := Parser.descendant_height_le _ _ _ _ hbirth
  have hMN := Parser.descendant_trans M g.birth N b g.height (n + 1) hdesc hbirth
  obtain ⟨U, hMU, hNU, hs⟩ :=
    routing_constant_step4_inherited_record_step4_realization D hD N A b M hM
      (by omega) hMN
  have hGU := Parser.hierarchy_descendant_mem U.hierarchy (n + 1) g.height
    N g.birth hNU hbirth
  rcases g with ⟨H, hpositive, ⟨T, φ⟩, ι, htype⟩
  dsimp only at htype
  subst T
  obtain ⟨k, hH, w, hw⟩ := hdesc
  have hkpos : 0 < k := by dsimp only at hb hH; omega
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  have hH' : H = b + a + 1 := by dsimp only at hH; omega
  subst H
  let B : FramedNode S := ⟨ι.val.ty, φ⟩
  let cNode := B.child (b + a) w.1
  have hCU : cNode ∈ U.hierarchy.nodes (b + a) :=
    U.hierarchy.children_mem (b + a) B hGU w.1
  let c : U.Node := ⟨b + a, ⟨cNode, hCU⟩⟩
  let G : Parser.BornFacet P := ⟨b + a + 1, hpositive, B, ι, rfl⟩
  have hnode : (S.descendantNode cNode.ty b a w.2).move cNode.frame = M := by
    rw [hw]
    simp [cNode, B, SubstSystem.descendantNode, FramedNode.move, FramedNode.child,
      AffineIsometryEquiv.trans_assoc]
  have hcdesc : M.IsDescendant b cNode (b + a) := ⟨a, rfl, w.2, hnode.symm⟩
  have hanc := routing_constant_step4_inherited_record_step3_ancestor U b a cNode
    hCU w.2 (by rw [hnode]; exact hMU)
  have hanc' : U.hierarchy.ancestor ⟨b, ⟨M, hMU⟩⟩ a = c := by
    simpa only [hnode] using hanc
  have hparent : U.hierarchy.parentNode c = ⟨b + a + 1, ⟨B, hGU⟩⟩ := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (U.hierarchy.parent_unique (b + a) c.2 B hGU ⟨w.1, rfl⟩).symm
  have hleft : (B.child (b + a) ι.val.left).cell (b + a) ι.val.leftFacet.val =
      G.carrier := by
    simpa only [Parser.BornFacet.leftNode, G, B, Nat.add_sub_cancel] using
      G.sides_carrier.1
  have hsub : M.cell b e.val ⊆
      (B.child (b + a) ι.val.left).cell (b + a) ι.val.leftFacet.val := by
    rw [hleft]
    exact he
  obtain ⟨F, hF, hFG⟩ := routing_constant_step4_inherited_record_step2_child_facet
    B M (b + a) b w.1 ι.val.left hcdesc e ι.val.leftFacet hsub
  have hFG' : c.2.val.cell c.1 F.val = G.carrier := hFG.trans hleft
  have hint : relint (c.2.val.cell c.1 F.val) ⊆
      interior ((U.hierarchy.parentNode c).2.val.carrier (U.hierarchy.parentNode c).1) := by
    rw [hFG', hparent]
    exact routing_constant_step4_inherited_record_step5_internal G
  have hty : ι.val.ty = (U.hierarchy.parentNode c).2.val.ty := by rw [hparent]
  have hpos : c.2.val.cell c.1 F.val =
      P.incidencePlacement (U.hierarchy.parentNode c).2.val
        (U.hierarchy.parentNode c).1 ι '' ι.val.leftFacet.val.carrier := by
    rw [hparent]
    exact hFG'
  obtain ⟨r, hr, hi, ha⟩ := routing_constant_step4_inherited_record_step6_restrict
    U c ⟨b, ⟨M, hMU⟩⟩ a hanc' F e hF hint ι hty hpos huncapped
  exact ⟨r, by rwa [hs] at hr, hi, ha⟩

/-- Step 1 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 8.3):
"let f be born in Q of height b". The prescribed child frame intertwines
the full expansion at its height with the original child placement. -/
private theorem routing_constant_step4_ascent_ports_step1_child_scaled
    (h : ℕ) {T : S.ι} (i : S.I T) (x : E d) :
    S.placeChild h i ((S.σ ^ h) x) = (S.σ ^ h) ((S.child T i).frame x) := by
  rw [S.placeChild_apply]
  simp [linearConj, Child.frame, rigidMotion, LinearEquiv.mul_apply,
    zpow_natCast, zpow_neg, AffineIsometryEquiv.coe_trans]

/-- Step 1 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 8.3):
"born in its ancestor Q'". Raising both heights conjugates the same child
placement, so the role identifying the child is unchanged. -/
private theorem routing_constant_step4_ascent_ports_step1_child_shift
    (h k : ℕ) {T : S.ι} (i : S.I T) (x : E d) :
    S.placeChild (h + k) i ((S.σ ^ h) x) = (S.σ ^ h) (S.placeChild k i x) := by
  have h₁ := routing_constant_step4_ascent_ports_step1_child_scaled (h + k) i
    ((S.σ ^ k).symm x)
  have h₂ := routing_constant_step4_ascent_ports_step1_child_scaled k i
    ((S.σ ^ k).symm x)
  simp only [pow_add, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply] at h₁ h₂
  rw [← h₂] at h₁
  exact h₁

/-- Step 1 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 8.3):
"both nodes descendants of A". Iterate the child-frame identity along a
fixed role word, without imposing scalar expansion. -/
private theorem routing_constant_step4_ascent_ports_step1_descendant_scaled
    (T : S.ι) (h r : ℕ) (w : S.RoleWord T r) (x : E d) :
    (S.descendantNode T h r w).frame ((S.σ ^ h) x) =
      (S.σ ^ h) ((S.nativeTile T r w).frame x) := by
  induction r generalizing T with
  | zero => rfl
  | succ r ih =>
    change S.placeChild (h + r) w.1
      ((S.descendantNode (S.child T w.1).ty h r w.2).frame ((S.σ ^ h) x)) =
      (S.σ ^ h) (S.placeChild (0 + r) w.1
        ((S.nativeTile (S.child T w.1).ty r w.2).frame x))
    rw [ih, routing_constant_step4_ascent_ports_step1_child_shift, Nat.zero_add]

/-- Step 1 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.25):
"both nodes descendants of A". The relative prototype frame of a role word
does not depend on the absolute height of its root. -/
private theorem routing_constant_step4_ascent_ports_step1_relative_frame
    (M : FramedNode S) (h r : ℕ) (w : S.RoleWord M.ty r) :
    ((S.descendantNode M.ty h r w).move M.frame).prototypeFrame h =
      (prototypeDescendantFrame M.ty r w).trans (M.prototypeFrame (h + r)) := by
  apply AffineEquiv.ext
  intro x
  change M.frame ((S.descendantNode M.ty h r w).frame ((S.σ ^ h) x)) =
    M.frame ((S.σ ^ (h + r)) ((S.σ ^ r).symm ((S.nativeTile M.ty r w).frame x)))
  rw [routing_constant_step4_ascent_ports_step1_descendant_scaled, pow_add]
  simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]

/-- Step 1 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.25):
"born in a strict ancestor". A common affine change of prototype frames
transports exact descent when it preserves the height difference and types. -/
private theorem routing_constant_step4_ascent_ports_step1_descent_transport
    (M Q M' Q' : FramedNode S) (a b a' b' : ℕ) (F : E d ≃ᵃ[ℝ] E d)
    (hMt : M'.ty = M.ty) (hQt : Q'.ty = Q.ty)
    (hM : M'.prototypeFrame a' = (M.prototypeFrame a).trans F)
    (hQ : Q'.prototypeFrame b' = (Q.prototypeFrame b).trans F)
    (hdiff : b' + a = b + a') (hdesc : M.IsDescendant a Q b) :
    M'.IsDescendant a' Q' b' := by
  rcases Q with ⟨T, φ⟩
  rcases Q' with ⟨T', ψ⟩
  dsimp only at hQt
  subst T'
  obtain ⟨r, hr, w, hw⟩ := hdesc
  have hr' : b' = a' + r := by omega
  refine ⟨r, hr', w, ?_⟩
  apply FramedNode.ext
  · exact hMt.trans ((congrArg FramedNode.ty hw).trans
      ((routing_constant_step1_descendant_type T a r w).trans
        (routing_constant_step1_descendant_type T a' r w).symm))
  · have hframe : M'.prototypeFrame a' =
        ((S.descendantNode T a' r w).move ψ).prototypeFrame a' := by
      rw [hM, hw, routing_constant_step4_ascent_ports_step1_relative_frame, ← hr]
      rw [routing_constant_step4_ascent_ports_step1_relative_frame
        (⟨T, ψ⟩ : FramedNode S), ← hr', hQ]
      exact AffineEquiv.trans_assoc _ _ _
    apply AffineIsometryEquiv.ext
    intro x
    have hx := congrArg (fun e : E d ≃ᵃ[ℝ] E d => e ((S.σ ^ a').symm x)) hframe
    simpa only [FramedNode.prototypeFrame, AffineEquiv.coe_trans, Function.comp_apply,
      LinearEquiv.coe_toAffineEquiv, AffineIsometryEquiv.coe_toAffineEquiv,
      LinearEquiv.apply_symm_apply] using hx

/-- Step 1 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 8.3):
"let g be born in its ancestor Q'". Transport the ascent's exact descendant
relation from the height-k model to the assembled parent's actual frame. -/
private theorem routing_constant_step4_ascent_ports_step1_ancestry
    (N : FramedNode S) (m : ℕ) (f f' : PrimitiveFacet S N.ty)
    (hf : f.depth < P.k) (hf' : f'.depth < P.k) (g g' : Parser.BornFacet P)
    (hg : routing_constant_step1_realizes N m f g)
    (hg' : routing_constant_step1_realizes N m f' g')
    (hlink : AscentLink P.k f f') :
    g.birth.IsDescendant g.height g'.birth g'.height := by
  have hfm : f.depth ≤ m := by have := hg.1; omega
  have hfm' : f'.depth ≤ m := by have := hg'.1; omega
  have hh : m - f.depth = g.height := by have := hg.1; omega
  have hh' : m - f'.depth = g'.height := by have := hg'.1; omega
  let F := (S.σ ^ P.k).symm.toAffineEquiv.trans (N.prototypeFrame m)
  have hframe (a : PrimitiveFacet S N.ty) (G : Parser.BornFacet P)
      (ha : a.depth < P.k) (ham : a.depth ≤ m)
      (hG : routing_constant_step1_realizes N m a G)
      (hheight : m - a.depth = G.height) :
      G.birth.prototypeFrame G.height =
        ((a.birthNode P.k).prototypeFrame (P.k - a.depth)).trans F := by
    rw [hG.2.1, ← hheight, routing_constant_step1_frame N m a ham]
    change _ = ((a.birthNode P.k).prototypeFrame (P.k - a.depth)).trans
      ((S.σ ^ P.k).symm.toAffineEquiv.trans (N.prototypeFrame m))
    rw [← AffineEquiv.trans_assoc, (a.birthFrame_spec P.k ha.le).2]
  apply routing_constant_step4_ascent_ports_step1_descent_transport
    (f.birthNode P.k) (f'.birthNode P.k) g.birth g'.birth
    (P.k - f.depth) (P.k - f'.depth) g.height g'.height F
  · rw [hg.2.1]
    exact (f.birthFrame_spec m hfm).1.trans (f.birthFrame_spec P.k hf.le).1.symm
  · rw [hg'.2.1]
    exact (f'.birthFrame_spec m hfm').1.trans (f'.birthFrame_spec P.k hf'.le).1.symm
  · exact hframe f g hf hfm hg hh
  · exact hframe f' g' hf' hfm' hg' hh'
  · have := hg.1
    have := hg'.1
    omega
  · exact hlink.2.1

/-- Step 1 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.25):
"with some child ... having a facet piece inside e". Place a child cell
using its parent's full prototype frame, also at the lowest positive height. -/
private theorem routing_constant_step4_ascent_ports_step1_child_frame
    (M : FramedNode S) (b : ℕ) (hb : 1 ≤ b) (i : S.I M.ty) :
    (M.child (b - 1) i).prototypeFrame (b - 1) =
      ((S.child M.ty i).frame.toAffineEquiv.trans S.σ.symm.toAffineEquiv).trans
        (M.prototypeFrame b) := by
  apply AffineEquiv.ext
  intro x
  change M.frame (S.placeChild (b - 1) i ((S.σ ^ (b - 1)) x)) =
    M.frame ((S.σ ^ b) (S.σ.symm ((S.child M.ty i).frame x)))
  rw [routing_constant_step4_ascent_ports_step1_child_scaled,
    show b = (b - 1) + 1 from (Nat.sub_add_cancel hb).symm, pow_succ]
  simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply, Nat.add_sub_cancel]

/-- Step 1 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.25):
"both nodes descendants of A". The full prototype frame places the entire
node support, as well as every one of its named cells. -/
private theorem routing_constant_step4_ascent_ports_step1_carrier_frame
    (Q : FramedNode S) (b : ℕ) :
    Q.carrier b = Q.prototypeFrame b '' (S.proto Q.ty).carrier := by
  simp only [FramedNode.carrier, FramedNode.prototypeFrame, SubstSystem.supertile,
    placedSet, Set.image_image]
  rfl

/-- Step 1 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.25):
"the common-listed vertex and the e-facing port". All named cells, the
common-listed seed, and the facing child survive the same affine transport. -/
private theorem routing_constant_step4_ascent_ports_step1_seed_geometry
    (N : FramedNode S) (m : ℕ) (f : PrimitiveFacet S N.ty)
    (M : FramedNode S) (b : ℕ) (hb : 1 ≤ b) (ht : M.ty = f.birthType)
    (hframe : M.prototypeFrame b = f.birthFrame.trans (N.prototypeFrame m))
    (e : FacetName S f.birthType) (p : E d) (hpe : p ∈ f.birthCell e.val)
    (hcommon : f.CommonListed p)
    (hface : ∃ (i : S.I f.birthType) (c : FacetName S (S.child f.birthType i).ty),
      p ∈ f.childCell i c.val ∧ f.childCell i c.val ⊆ f.birthCell e.val) :
    ∃ E : FacetName S M.ty, E.val = e.val ∧
      M.cell b E.val = N.prototypeFrame m '' f.birthCell e.val ∧
      N.prototypeFrame m p ∈ M.cell b E.val ∧
      (∀ i : S.I M.ty, N.prototypeFrame m p ∈ (M.child (b - 1) i).carrier (b - 1) →
        (M.child (b - 1) i).Lists (b - 1) (N.prototypeFrame m p)) ∧
      ∃ (i : S.I M.ty) (c : FacetName S (M.child (b - 1) i).ty),
        N.prototypeFrame m p ∈ (M.child (b - 1) i).cell (b - 1) c.val ∧
          (M.child (b - 1) i).cell (b - 1) c.val ⊆ M.cell b E.val := by
  rcases M with ⟨T, φ⟩
  dsimp only at ht
  subst T
  let M : FramedNode S := ⟨f.birthType, φ⟩
  change M.prototypeFrame b = f.birthFrame.trans (N.prototypeFrame m) at hframe
  have hcell (c : Cell d) : M.cell b c = N.prototypeFrame m '' f.birthCell c := by
    simp only [FramedNode.cell, hframe, PrimitiveFacet.birthCell, Set.image_image]
    rfl
  have hchild (i : S.I f.birthType) (K : Set (E d)) :
      (M.child (b - 1) i).prototypeFrame (b - 1) '' K =
        N.prototypeFrame m '' (f.birthFrame ''
          (S.σ.symm '' placedSet (S.child f.birthType i).frame K)) := by
    rw [routing_constant_step4_ascent_ports_step1_child_frame M b hb i, hframe]
    simp only [Set.image_image, placedSet]
    rfl
  refine ⟨e, rfl, hcell e.val, (hcell e.val).symm ▸ Set.mem_image_of_mem _ hpe, ?_, ?_⟩
  · intro i hi
    change N.prototypeFrame m p ∈ (M.child (b - 1) i).carrier (b - 1) at hi
    rw [routing_constant_step4_ascent_ports_step1_carrier_frame, hchild] at hi
    have hpchild : p ∈ f.childSupport i := (N.prototypeFrame m).injective.mem_set_image.mp hi
    obtain ⟨v, hv, hpv⟩ := hcommon i hpchild
    refine ⟨v, hv, ?_⟩
    change N.prototypeFrame m p ∈ (M.child (b - 1) i).prototypeFrame (b - 1) '' v.carrier
    rw [hchild]
    exact Set.mem_image_of_mem _ hpv
  · obtain ⟨i, c, hpc, hce⟩ := hface
    refine ⟨i, c, ?_, ?_⟩
    · change N.prototypeFrame m p ∈ (M.child (b - 1) i).prototypeFrame (b - 1) '' c.val.carrier
      rw [hchild]
      exact Set.mem_image_of_mem _ hpc
    · change (M.child (b - 1) i).prototypeFrame (b - 1) '' c.val.carrier ⊆ _
      rw [hchild, hcell]
      exact Set.image_mono hce

/-- Step 2 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.25):
"some child ... having a facet piece inside e". A listed cell belongs to its closed prototype support. -/
private theorem routing_constant_step4_ascent_ports_step2_cell_subset (A : S.ι) (e : Cell d) (he : e ∈ (S.cx A).cells) :
    e.carrier ⊆ (S.proto A).carrier := by
  intro x hx
  apply (S.proto A).compact.isClosed.frontier_subset
  rw [← (S.cx A).carriers_cover]
  exact mem_iUnion₂.mpr ⟨e, he, hx⟩

/-- Step 2 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.25):
"some child ... at q". A placed named facet belongs to its owning node,
including every point of its closed boundary. -/
private theorem routing_constant_step4_ascent_ports_step2_cell_carrier
    (Q : FramedNode S) (b : ℕ) (e : FacetName S Q.ty) :
    Q.cell b e.val ⊆ Q.carrier b := by
  rw [routing_constant_step4_ascent_ports_step1_carrier_frame]
  exact Set.image_mono (routing_constant_step4_ascent_ports_step2_cell_subset
    _ e.val (facetCell e).property)


/-- Step 2 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.5, 1.8):
"A native descendant along either facet at q". Iterated heredity supplies an actual native facet piece and a listed vertex at the prescribed point. -/
private theorem routing_constant_step4_ascent_ports_step2_facet_at_vertex
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (B : Block Y n)
    (f : FacetName S B.node.ty) (p : E d) (hp : B.node.Lists n p)
    (hpf : p ∈ B.node.cell n f.val) :
    ∃ (t : PlacedMarkedTile (systemM S P C)) (g : FacetName S (tileNode t).ty)
      (v : VertexName S (tileNode t).ty),
      Parser.IsFacetPiece Y n B.node f t g ∧ v.val.carrier ⊆ g.val.carrier ∧
        compilerFrame C t (vertexPoint v) = p := by
  classical
  obtain ⟨parts, hparts⟩ := S.heredity_iter B.node.ty n f.val
    (Finset.mem_filter.mp f.property).1
  obtain ⟨x, hxf, hxp⟩ := hpf
  have hσx : (S.σ ^ n) x ∈ (S.σ ^ n) '' f.val.carrier := ⟨x, hxf, rfl⟩
  rw [hparts] at hσx
  obtain ⟨q, hq, y, hy, hxy⟩ := mem_iUnion₂.mp hσx
  obtain ⟨t, ht, hnode⟩ := B.actual q.1
  let g : FacetName S (tileNode t).ty := ⟨q.2.val, by
    rw [hnode]
    exact Finset.mem_filter.mpr ⟨q.2.property.1,
      q.2.property.2.trans (Finset.mem_filter.mp f.property).2⟩⟩
  have hdesc : (tileNode t).IsDescendant 0 B.node n := ⟨n, by omega, q.1, hnode⟩
  have hsub : (tileNode t).cell 0 g.val ⊆ B.node.cell n f.val := by
    rintro z ⟨w, hw, rfl⟩
    have hmem : (S.nativeTile B.node.ty n q.1).frame w ∈ (S.σ ^ n) '' f.val.carrier := by
      rw [hparts]
      exact mem_iUnion₂.mpr ⟨q, hq, w, hw, rfl⟩
    obtain ⟨z, hz, he⟩ := hmem
    refine ⟨z, hz, ?_⟩
    rw [hnode]
    change B.node.frame ((S.σ ^ n) z) = B.node.frame ((S.nativeTile B.node.ty n q.1).frame w)
    exact congrArg B.node.frame he
  have hpoint : (tileNode t).prototypeFrame 0 y = p := by
    rw [hnode]
    change B.node.frame ((S.nativeTile B.node.ty n q.1).frame y) = p
    rw [hxy]
    exact hxp
  have hmem : p ∈ (tileNode t).carrier 0 := by
    rw [← hpoint, hnode]
    refine ⟨(S.σ ^ 0) y, ⟨y, ?_, rfl⟩, rfl⟩
    exact routing_constant_step4_ascent_ports_step2_cell_subset _ q.2.val q.2.property.1 hy
  obtain ⟨v, hv, hvp⟩ := commonListed_inherited B.node (tileNode t) n 0 hdesc p hp hmem
  let v' : VertexName S (tileNode t).ty := ⟨v, hv⟩
  have hvpoint : compilerFrame C t (vertexPoint v') = p := by
    obtain ⟨z, hz, hzp⟩ := hvp
    change z ∈ v'.val.carrier at hz
    have hzv : z = vertexPoint v' := by simpa only [vertexPoint_spec v', mem_singleton_iff] using hz
    subst z
    exact hzp
  have hvg : v.carrier ⊆ g.val.carrier := by
    rw [vertexPoint_spec v']
    apply singleton_subset_iff.mpr
    have hyv : y = vertexPoint v' := by
      apply (compilerFrame C t).injective
      exact hpoint.trans hvpoint.symm
    simpa only [← hyv] using hy
  exact ⟨t, g, v', ⟨ht, hdesc, hsub⟩, hvg, hvpoint⟩


/-- Step 3 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 2.3, 8.3):
"inherits an END header". A vertex listed by the serving child has a zero-dimensional provider stratum after restriction to a native facet piece. -/
private theorem routing_constant_step4_ascent_ports_step3_provider_zero
    (U : HonestSource S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (v : VertexName S q.2.val.ty)
    (hv : v.val.carrier ⊆ f.val.carrier)
    (hp : (U.hierarchy.servingChild q f hf).2.val.Lists
      (U.hierarchy.servingChild q f hf).1
      (q.2.val.prototypeFrame q.1 (vertexPoint v))) :
    (U.recordTau P q f hf ⟨vertexCell v, hv⟩).val.val.dim = 0 := by
  obtain ⟨w, hw, hpw⟩ := hp
  let w' : VertexName S (U.hierarchy.servingChild q f hf).2.val.ty := ⟨w, hw⟩
  have hpoint : q.2.val.prototypeFrame q.1 (vertexPoint v) =
      (U.hierarchy.servingChild q f hf).2.val.prototypeFrame
        (U.hierarchy.servingChild q f hf).1 (vertexPoint w') := by
    change _ ∈ (U.hierarchy.servingChild q f hf).2.val.cell
      (U.hierarchy.servingChild q f hf).1 w'.val at hpw
    simpa only [FramedNode.cell, vertexPoint_spec w', Set.image_singleton,
      Set.mem_singleton_iff] using hpw
  have hcell : q.2.val.cell q.1 (vertexCell v).val =
      (U.hierarchy.servingChild q f hf).2.val.cell
        (U.hierarchy.servingChild q f hf).1 (vertexCell w').val := by
    simp only [FramedNode.cell, vertexCell, vertexPoint_spec, Set.image_singleton, hpoint]
  have hstratum : U.hierarchy.stratumMap q f hf (vertexCell v)
      (U.cellInFacet_placed q f ⟨vertexCell v, hv⟩) = vertexCell w' := by
    exact ((Classical.choose_spec (U.hierarchy.stratum_exists_unique q f hf
      (vertexCell v) (U.cellInFacet_placed q f ⟨vertexCell v, hv⟩))).2
        (vertexCell w') (by rw [hcell])).symm
  have htau := record_tau_spec U P q f hf ⟨vertexCell v, hv⟩
  rw [hstratum] at htau
  change U.providerPlacement P q f hf ''
      (U.recordTau P q f hf ⟨vertexCell v, hv⟩).val.val.carrier =
    (U.hierarchy.servingChild q f hf).2.val.prototypeFrame
      (U.hierarchy.servingChild q f hf).1 '' w'.val.carrier at htau
  rw [vertexPoint_spec, Set.image_singleton] at htau
  let e := U.recordTau P q f hf ⟨vertexCell v, hv⟩
  have hsingleton : e.val.val.carrier =
      {(U.providerPlacement P q f hf).symm
        ((U.hierarchy.servingChild q f hf).2.val.prototypeFrame
          (U.hierarchy.servingChild q f hf).1 (vertexPoint w'))} := by
    apply (U.providerPlacement P q f hf).injective.image_injective
    simpa only [Set.image_singleton, AffineEquiv.apply_symm_apply] using htau
  change e.val.val.dim = 0
  rw [← e.val.val.flat.dimension, hsingleton]
  simp [cellDirection, direction_affineSpan]

/-- Step 2 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.25, 8.3):
"the e-facing tiles (tiles inside Q with pieces in e at q)". Refine the
given facing child facet to one actual native facet piece through the same
listed vertex. This statement concerns only the prescribed subdivision. -/
private theorem routing_constant_step4_ascent_ports_step2_boundary_piece
    (Y : MarkedTiling (systemM S P C)) (b : ℕ) (Q : FramedNode S)
    (hb : 1 ≤ b) (hQ : IsBlock Y b Q) (e : FacetName S Q.ty) (p : E d)
    (hcommon : ∀ i : S.I Q.ty, p ∈ (Q.child (b - 1) i).carrier (b - 1) →
      (Q.child (b - 1) i).Lists (b - 1) p)
    (hface : ∃ (i : S.I Q.ty) (c : FacetName S (Q.child (b - 1) i).ty),
      p ∈ (Q.child (b - 1) i).cell (b - 1) c.val ∧
        (Q.child (b - 1) i).cell (b - 1) c.val ⊆ Q.cell b e.val) :
    ∃ (t : PlacedMarkedTile (systemM S P C)) (f : FacetName S (tileNode t).ty)
      (v : VertexName S (tileNode t).ty),
      Parser.IsFacetPiece Y b Q e t f ∧ v.val.carrier ⊆ f.val.carrier ∧
        compilerFrame C t (vertexPoint v) = p := by
  obtain ⟨i, c, hpc, hce⟩ := hface
  have hchild : (Q.child (b - 1) i).IsDescendant (b - 1) Q b := by
    simpa only [Nat.sub_add_cancel hb] using Parser.child_descendant Q (b - 1) i
  let B : Block Y (b - 1) := (⟨Q, hQ⟩ : Block Y b).innerBlock
    (b - 1) (Q.child (b - 1) i) hchild
  have hpcar : p ∈ (Q.child (b - 1) i).carrier (b - 1) := by
    exact routing_constant_step4_ascent_ports_step2_cell_carrier _ _ c hpc
  obtain ⟨t, f, v, hpiece, hv, hvp⟩ :=
    routing_constant_step4_ascent_ports_step2_facet_at_vertex Y (b - 1) B c p
      (hcommon i hpcar) hpc
  exact ⟨t, f, v, ⟨hpiece.1,
    Parser.descendant_trans _ _ _ _ _ _ hpiece.2.1 hchild,
    hpiece.2.2.trans hce⟩, hv, hvp⟩


/-- Step 3 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.1, 8.3):
"a facet ... born in Q". Relative interiors commute with the full affine prototype frames, so internality is preserved. -/
private theorem routing_constant_step4_ascent_ports_step3_relint_image
    (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
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


/-- Step 3 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 8.3):
"an END template with cone T_q Q". This is the complete geometric header
of a positive-height birth, expressed in the distinguished native frame. -/
private def routing_constant_step4_ascent_ports_step3_header
    (Q : FramedNode S) (b : ℕ) (φ : Iso d) (p : E d) : State.Header P := by
  classical
  let normalize := fun K : Set (E d) => φ.linearIsometryEquiv.symm '' K
  let pos := fun ι : P.Incidence => P.incidencePlacement Q b ι
  exact {
    birthType := Q.ty
    parentCone := normalize (tangentCone (Q.carrier b) p)
    childCones := fun i =>
      let M := Q.child (b - 1) i
      if p ∈ M.carrier (b - 1) then
        some (normalize (tangentCone (M.carrier (b - 1)) p)) else none
    boundaryCones := fun F => if p ∈ Q.cell b F.val then
      some (normalize (tangentCone (Q.cell b F.val) p)) else none
    primitiveCones := fun ι => if ι.val.ty = Q.ty ∧
        p ∈ pos ι '' ι.val.leftFacet.val.carrier then
      some (normalize (tangentCone (pos ι '' ι.val.leftFacet.val.carrier) p)) else none
    flagTangent := fun ι => if ι.val.ty = Q.ty ∧
        (p = pos ι (P.flag ι).initial ∨ p = pos ι (P.flag ι).terminal) then
      some {
        cones := fun j => normalize
          (tangentCone (pos ι '' ((P.flag ι).flag.cell j).val.carrier) p)
        initial := decide (p = pos ι (P.flag ι).initial)
        sides := fun j => normalize ((pos ι).linear '' (P.flag ι).sides j) }
      else none }

/-- Step 3 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 8.3):
"a native descendant along ... f". The incidence's left owner is a named
immediate child of its birth parent, with the same full frame. -/
private theorem routing_constant_step4_ascent_ports_step3_left_child
    (g : Parser.BornFacet P) :
    ∃ i : S.I g.birth.ty, g.leftNode = g.birth.child (g.height - 1) i := by
  rcases g with ⟨b, hb, ⟨T, φ⟩, ι, hι⟩
  dsimp only at hι
  subst T
  exact ⟨ι.val.left, rfl⟩

/-- Step 3 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 8.3):
"f born in Q". The left incidence facet is internal to the actual birth
parent; the assertion includes the anisotropic expansion and the ambient frame. -/
private theorem routing_constant_step4_ascent_ports_step3_internal
    (g : Parser.BornFacet P) : relint g.carrier ⊆ interior (g.birth.carrier g.height) := by
  let φ : E d ≃ᵃ[ℝ] E d :=
    (S.σ ^ (g.height - 1)).toAffineEquiv.trans g.birth.frame.toAffineEquiv
  have hcarrier : g.carrier = φ '' g.incidence.val.positioned := by
    rw [routing_constant_step1_carrier]
    have hp : S.σ ^ g.height = S.σ ^ (g.height - 1) * S.σ := by
      rw [← pow_succ, Nat.sub_add_cancel g.positive]
    simp only [FramedNode.prototypeFrame, Set.image_image, AffineEquiv.coe_trans,
      LinearEquiv.coe_toAffineEquiv, AffineIsometryEquiv.coe_toAffineEquiv,
      Function.comp_apply, hp, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
    rfl
  have hbirth : g.birth.carrier g.height = φ '' S.supertile 1 g.incidence.val.ty := by
    rw [g.parent_type]
    simp only [FramedNode.carrier, SubstSystem.supertile, placedSet, φ,
      Set.image_image, AffineEquiv.coe_trans, LinearEquiv.coe_toAffineEquiv,
      AffineIsometryEquiv.coe_toAffineEquiv, Function.comp_apply, pow_one]
    have hp : S.σ ^ g.height = S.σ ^ (g.height - 1) * S.σ := by
      rw [← pow_succ, Nat.sub_add_cancel g.positive]
    rw [hp]
    rfl
  have hi : φ '' interior (S.supertile 1 g.incidence.val.ty) =
      interior (φ '' S.supertile 1 g.incidence.val.ty) :=
    φ.toHomeomorphOfFiniteDimensional.image_interior _
  rw [hcarrier, routing_constant_step4_ascent_ports_step3_relint_image, hbirth, ← hi]
  exact Set.image_mono g.incidence.val.internal

/-- Step 3 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 2.3, 8.3):
"restrict down ... using (I2)". In a fixed honest realization of an old
node, every prescribed descendant has its actual decoded state and ancestor. -/
private theorem routing_constant_step4_ascent_ports_step3_source_descendant
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) (hD : Inv D)
    (U : HonestSource S) (b : ℕ) (Q : FramedNode S)
    (hQ : Q ∈ D.geometry.nodes b) (hU : Q ∈ U.hierarchy.nodes b)
    (hs : stateOf U P ⟨b, ⟨Q, hU⟩⟩ = D.stateAt b Q hQ)
    (a : ℕ) (M : FramedNode S) (hdesc : M.IsDescendant a Q b) :
    ∃ (hM : M ∈ D.geometry.nodes a) (hMU : M ∈ U.hierarchy.nodes a),
      stateOf U P ⟨a, ⟨M, hMU⟩⟩ = D.stateAt a M hM ∧
        U.hierarchy.ancestor ⟨a, ⟨M, hMU⟩⟩ (b - a) = ⟨b, ⟨Q, hU⟩⟩ := by
  obtain ⟨r, rfl, w, rfl⟩ := hdesc
  simpa only [Nat.add_sub_cancel_left] using
    routing_constant_step2_source_descent D hD U a r Q hQ hU hs w

/-- Step 3 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 2.3, 8.3):
"A native descendant ... inherits an END header ... from its owner's
age-one record". Given the native facet piece, identify its provider and
read its actual header and central packet. No template is asserted here. -/
private theorem routing_constant_step4_ascent_ports_step3_slot
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) (hD : Inv D)
    (g : Parser.BornFacet P) (hg : g.birth ∈ D.geometry.nodes g.height)
    (p : E d) (hp : g.leftNode.Lists (g.height - 1) p)
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (q : Packet P) (hq : g.packet hl = some q)
    (t : PlacedMarkedTile (systemM S P C)) (f : FacetName S (tileNode t).ty)
    (v : VertexName S (tileNode t).ty)
    (hpiece : Parser.IsFacetPiece Y (g.height - 1) g.leftNode
      g.incidence.val.leftFacet t f)
    (hv : v.val.carrier ⊆ f.val.carrier)
    (hvp : compilerFrame C t (vertexPoint v) = p) :
    ∃ j : EndSlot (compilerLeaf C t), j.packet = q ∧
      Compiler.endVertex (compilerFrame C t) j = p ∧
      j.header = routing_constant_step4_ascent_ports_step3_header
        g.birth g.height (compilerFrame C t) p := by
  classical
  obtain ⟨U, hU, hs⟩ := routing_constant_step2_source_realization
    (D.stateAt g.height g.birth hg) (D.state_honest _ _)
    g.birth g.height (hD.node_type_residue _ _ hg).1 (hD.node_type_residue _ _ hg).2
  let B : U.Node := ⟨g.height, ⟨g.birth, hU⟩⟩
  obtain ⟨hL, hLU, hsL, hancL⟩ :=
    routing_constant_step4_ascent_ports_step3_source_descendant D hD U
      g.height g.birth hg hU hs (g.height - 1) g.leftNode g.sides_descendant.1
  let L : U.Node := ⟨g.height - 1, ⟨g.leftNode, hLU⟩⟩
  have hparent : U.hierarchy.parentNode L = B := by
    have he : g.height - (g.height - 1) = 1 := by have := g.positive; omega
    simpa only [he, CoherentHierarchy.ancestor, Function.iterate_one] using hancL
  obtain ⟨hF, _, hbirthL, _⟩ := U.hierarchy.restriction_det_internal L
    g.incidence.val.leftFacet (by
      rw [hparent]
      change relint (g.leftNode.cell (g.height - 1) g.incidence.val.leftFacet.val) ⊆ _
      rw [g.sides_carrier.1]
      exact routing_constant_step4_ascent_ports_step3_internal g)
  obtain ⟨htD, htU, htstate, hanc⟩ :=
    routing_constant_step4_ascent_ports_step3_source_descendant D hD U
      (g.height - 1) g.leftNode hL hLU hsL 0 (tileNode t) hpiece.2.1
  let c : U.Node := ⟨0, ⟨tileNode t, htU⟩⟩
  have hleaf : stateOf U P c = (compilerLeaf C t).prePattern.state :=
    htstate.trans (hD.I2.2 (tileNode t) htD t hpiece.1 rfl)
  obtain ⟨hf, _, hbirth⟩ := U.hierarchy.provider_inherited L c (g.height - 1)
    (by simpa only [Nat.sub_zero] using hanc) g.incidence.val.leftFacet f hF hpiece.2.2
  have hbirth' : U.hierarchy.birthParent c f hf = B :=
    hbirth.trans (hbirthL.trans hparent)
  have hserv : U.hierarchy.servingChild c f hf = L := by
    have hh := congrArg (fun z : U.Node => z.1) hbirth'
    have hoff := (U.hierarchy.birthHeight_age_spec c f hf).1
    have he : (U.hierarchy.firstProvider c f hf).1 = g.height - 1 := by
      change U.hierarchy.birthHeight c f hf = g.height at hh
      change U.hierarchy.birthHeight c f hf = 0 + _ + 1 at hoff
      omega
    simpa only [CoherentHierarchy.servingChild, he, Nat.sub_zero] using hanc
  have hframe : c.2.val.prototypeFrame c.1 = (compilerFrame C t).toAffineEquiv := by
    ext x
    rfl
  have hpoint : c.2.val.prototypeFrame c.1 (vertexPoint v) = p := by
    rw [hframe]
    exact hvp
  have hzero := routing_constant_step4_ascent_ports_step3_provider_zero (P := P)
    U c f hf v hv (by rw [hserv, hpoint]; exact hp)
  have hrleaf : leafRecord (compilerLeaf C t) f.val = some (U.recordOf P c f hf) := by
    unfold leafRecord
    rw [← hleaf]
    simp only [stateRecordAt, stateOf, c, dif_pos f.property,
      HonestSource.facetRecordOf, dif_neg hf]
  have hheader : leafHeader (compilerLeaf C t) v.val f.val =
      some (U.headerOf P c f hf v) := by
    unfold leafHeader
    rw [← hleaf]
    simp only [stateOf, c, dif_pos v.property, dif_pos f.property,
      HonestSource.headerRecordOf, dif_pos hv, dif_neg hf, hzero, if_pos True.intro]
  have hpacket : leafPacket (compilerLeaf C t) f.val = some q :=
    (attachedPacket_eq_leaf hl g.incidence.val.leftFacet t f hpiece).symm.trans hq
  have hvc : v.val ∈ (S.cx (tileNode t).ty).cells := (vertexCell v).property
  let j : EndSlot (compilerLeaf C t) := {
    facet := f
    record := U.recordOf P c f hf
    record_eq := hrleaf
    type_eq := rfl
    facet_eq := rfl
    vertex := v
    onFacet := hv
    providerVertex := U.recordTau P c f hf ⟨vertexCell v, hv⟩
    tau_vertex := by
      simp only [FacetRecord.tauAt, HonestSource.recordOf, c, dif_pos hvc, dif_pos hv]
      rfl
    provider_zero := hzero
    header := U.headerOf P c f hf v
    header_eq := hheader
    packet := q
    packet_eq := hpacket }
  refine ⟨j, rfl, hvp, ?_⟩
  change U.headerOf P c f hf v = _
  have hnorm (K : Set (E d)) : U.normalizeCone c K =
      (compilerFrame C t).linearIsometryEquiv.symm '' K := by
    rw [HonestSource.normalizeCone, hframe]
    rfl
  unfold HonestSource.headerOf
  rw [hbirth']
  simp only [B, hpoint, hnorm, routing_constant_step4_ascent_ports_step3_header]

/-- Step 3 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 8.3):
"A native descendant along ... f at q inherits an END header". Choose a
piece on the actual left owner and apply its inherited state and header
readout. The lower birth is old; no state of the new parent is used. -/
private theorem routing_constant_step4_ascent_ports_step3_seed
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) (hD : Inv D)
    (g : Parser.BornFacet P) (hg : g.birth ∈ D.geometry.nodes g.height)
    (p : E d) (hpg : p ∈ g.carrier)
    (hcommon : ∀ i : S.I g.birth.ty,
      p ∈ (g.birth.child (g.height - 1) i).carrier (g.height - 1) →
        (g.birth.child (g.height - 1) i).Lists (g.height - 1) p)
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (q : Packet P) (hq : g.packet hl = some q) :
    ∃ t ∈ Y.tiles, ∃ j : EndSlot (compilerLeaf C t), j.packet = q ∧
      Compiler.endVertex (compilerFrame C t) j = p ∧
      j.header = routing_constant_step4_ascent_ports_step3_header
        g.birth g.height (compilerFrame C t) p := by
  have hL := D.geometry.descendant_mem _ _ _ _ hg g.sides_descendant.1
  let B : Block Y (g.height - 1) :=
    ⟨g.leftNode, D.geometry.node_actual _ _ hL⟩
  have hpf : p ∈ g.leftNode.cell (g.height - 1) g.incidence.val.leftFacet.val := by
    rwa [g.sides_carrier.1]
  have hpcar : p ∈ g.leftNode.carrier (g.height - 1) :=
    routing_constant_step4_ascent_ports_step2_cell_carrier _ _ g.incidence.val.leftFacet hpf
  have hp : g.leftNode.Lists (g.height - 1) p := by
    obtain ⟨i, hi⟩ := routing_constant_step4_ascent_ports_step3_left_child g
    rw [hi] at hpcar ⊢
    exact hcommon i hpcar
  obtain ⟨t, f, v, hpiece, hv, hvp⟩ :=
    routing_constant_step4_ascent_ports_step2_facet_at_vertex Y (g.height - 1)
      B g.incidence.val.leftFacet p hp hpf
  obtain ⟨j, hqj, hpj, hheader⟩ := routing_constant_step4_ascent_ports_step3_slot
    D hD g hg p hp hl q hq t f v hpiece hv hvp
  exact ⟨t, hpiece.1, j, hqj, hpj, hheader⟩

/-- Step 4 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 2.17, 8.3):
"Theorem 2.17 ... put[s] the ports ... into the endpoint template".
Compilation of the already constructed END slot supplies an actual labelled
configuration and all six END rows. -/
private theorem routing_constant_step4_ascent_ports_step4_event
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (j : EndSlot (compilerLeaf C t)) :
    ∃ T : EndTemplate j,
      TemplateOccurs C Y (compilerFrame C t) T.configuration ∧ endRow T := by
  obtain ⟨θ, ⟨T, rfl, hrow⟩, _, hactual⟩ := compiler_events C Y hY t ht (.end_ j)
  exact ⟨T, hactual, hrow⟩

/-- Step 6 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.4, 1.25):
"g contains a facet e of Q". Nonempty relative interior gives positive
Hausdorff measure in the affine dimension, including dimension zero. -/
private theorem routing_constant_step4_ascent_ports_step6_relint_measure (K : Set (E d)) (hne : (relint K).Nonempty) :
    0 < (MeasureTheory.Measure.hausdorffMeasure (Module.finrank ℝ (affineSpan ℝ K).direction : ℝ)) K := by
  classical
  let A := affineSpan ℝ K
  obtain ⟨z, x, hx, rfl⟩ := hne
  letI : Nonempty A := ⟨x⟩
  let e := AffineIsometryEquiv.vaddConst ℝ x
  let U : Set A := interior ((↑) ⁻¹' K)
  let V : Set A.direction := e ⁻¹' U
  have hV : IsOpen V := isOpen_interior.preimage e.continuous
  have hVne : V.Nonempty := ⟨e.symm x, by simpa [V, U] using hx⟩
  letI : (MeasureTheory.Measure.hausdorffMeasure (Module.finrank ℝ A.direction : ℝ) :
      MeasureTheory.Measure A.direction).IsAddHaarMeasure := MeasureTheory.isAddHaarMeasure_hausdorffMeasure
  have hpos : 0 < (MeasureTheory.Measure.hausdorffMeasure (Module.finrank ℝ A.direction : ℝ)) V :=
    hV.measure_pos _ hVne
  have heV : e '' V = U := e.surjective.image_preimage U
  have hm := e.isometry.hausdorffMeasure_image
    (Or.inl (Nat.cast_nonneg (Module.finrank ℝ A.direction))) V
  rw [heV] at hm
  have hi : Isometry (Subtype.val : A → E d) := fun _ _ => rfl
  have hm' := hi.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg (Module.finrank ℝ A.direction))) U
  have hsub : (Subtype.val '' U : Set (E d)) ⊆ K := by
    rintro y ⟨x, hx, rfl⟩
    exact interior_subset (s := (Subtype.val ⁻¹' K : Set A)) hx
  exact (hpos.trans_eq (hm'.trans hm).symm).trans_le (MeasureTheory.measure_mono hsub)

/-- Step 6 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.4, 1.25):
"g contains a facet e of Q". Every placed facet has positive facet measure;
the affine prototype frame preserves its dimension and nonempty relative interior. -/
private theorem routing_constant_step4_ascent_ports_step6_facet_measure
    (Q : FramedNode S) (b : ℕ) (e : FacetName S Q.ty) :
    0 < MeasureTheory.Measure.hausdorffMeasure (d - 1 : ℝ) (Q.cell b e.val) := by
  have hdim : Module.finrank ℝ (affineSpan ℝ (Q.cell b e.val)).direction = d - 1 := by
    change Module.finrank ℝ
      (affineSpan ℝ ((Q.prototypeFrame b).toAffineMap '' e.val.carrier)).direction = _
    rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
    exact ((Q.prototypeFrame b).linear.finrank_map_eq _).trans
      (e.val.flat.dimension.trans (Finset.mem_filter.mp e.property).2)
  have hne : (relint (Q.cell b e.val)).Nonempty := by
    rw [FramedNode.cell, routing_constant_step4_ascent_ports_step3_relint_image]
    exact e.val.flat.relint_nonempty.image _
  have h := routing_constant_step4_ascent_ports_step6_relint_measure _ hne
  have hd : 1 ≤ d := by have := (Fact.out : 2 ≤ d); omega
  simpa only [hdim, Nat.cast_sub hd, Nat.cast_one] using h

/-- Step 6 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.25):
"born in its ancestor". A prescribed child is contained in its parent,
with the full conjugated frame at the given height. -/
private theorem routing_constant_step4_ascent_ports_step6_child_subset
    (N : FramedNode S) (n : ℕ) (i : S.I N.ty) :
    (N.child n i).carrier n ⊆ N.carrier (n + 1) := by
  rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hmem : (S.child N.ty i).frame x ∈ S.σ '' (S.proto N.ty).carrier := by
    rw [S.children_cover]
    exact mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩
  obtain ⟨y, hy, he⟩ := hmem
  refine ⟨(S.σ ^ (n + 1)) y, ⟨y, hy, rfl⟩, ?_⟩
  change N.frame ((S.σ ^ (n + 1)) y) = N.frame (S.placeChild n i ((S.σ ^ n) x))
  rw [routing_constant_step4_ascent_ports_step1_child_scaled, ← he, pow_succ]
  rfl

/-- Step 6 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.25):
"both nodes descendants of A". Iterate child containment along the exact
role word; this includes the zero-length descendant. -/
private theorem routing_constant_step4_ascent_ports_step6_descendant_subset
    (M N : FramedNode S) (m n : ℕ) (h : M.IsDescendant m N n) :
    M.carrier m ⊆ N.carrier n := by
  obtain ⟨r, rfl, w, rfl⟩ := h
  induction r generalizing N with
  | zero => simpa [SubstSystem.descendantNode, FramedNode.move] using
      (Subset.rfl : N.carrier m ⊆ N.carrier m)
  | succ r ih =>
    have he : (S.descendantNode N.ty m (r + 1) w).move N.frame =
        (S.descendantNode (N.child (m + r) w.1).ty m r w.2).move
          (N.child (m + r) w.1).frame := rfl
    rw [he]
    exact (ih (N.child (m + r) w.1) w.2).trans
      (routing_constant_step4_ascent_ports_step6_child_subset N (m + r) w.1)

/-- Step 6 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.4, 1.25):
"g contains a facet e of Q". The two owning children are the only children
with positive facet overlap. The first child on Q's address therefore is one
of those owners; a whole descendant facet cannot fit in a zero-measure overlap. -/
private theorem routing_constant_step4_ascent_ports_step6_two_owners
    (R : FramedNode S) (m : ℕ) (i j : S.I R.ty) (hij : i ≠ j)
    (F : FacetName S (R.child m i).ty) (G : FacetName S (R.child m j).ty)
    (hpair : (R.child m j).cell m G.val = (R.child m i).cell m F.val)
    (hint : relint ((R.child m i).cell m F.val) ⊆ interior (R.carrier (m + 1)))
    (b : ℕ) (Q : FramedNode S) (hdesc : Q.IsDescendant b R (m + 1))
    (hb : b < m + 1) (e : FacetName S Q.ty)
    (he : Q.cell b e.val ⊆ (R.child m i).cell m F.val) :
    Q.IsDescendant b (R.child m i) m ∨ Q.IsDescendant b (R.child m j) m := by
  have hne : (relint ((R.child m i).cell m F.val)).Nonempty := by
    rw [FramedNode.cell, routing_constant_step4_ascent_ports_step3_relint_image]
    exact F.val.flat.relint_nonempty.image _
  obtain ⟨x, hx⟩ := hne
  obtain ⟨j₀, ⟨_, _, _, hzero⟩, _⟩ :=
    (internal_facet_pairing R m i F ⟨x, hx, hint hx⟩).2
  have hj : j = j₀ := by
    by_contra hji
    have hz := hzero j hij.symm hji
    have hsub : (R.child m j).cell m G.val ⊆
        (R.child m j).carrier m ∩ (R.child m i).cell m F.val := by
      intro y hy
      exact ⟨routing_constant_step4_ascent_ports_step2_cell_carrier _ _ G hy, hpair ▸ hy⟩
    exact (ne_of_gt (routing_constant_step4_ascent_ports_step6_facet_measure _ _ G))
      (MeasureTheory.measure_mono_null hsub hz)
  subst j₀
  obtain ⟨r, hr, w, hw⟩ := hdesc
  have hrpos : 0 < r := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
  have hm : m = b + r := by omega
  have hdown : Q.IsDescendant b (R.child m w.1) m := by
    refine ⟨r, hm, w.2, ?_⟩
    simpa only [SubstSystem.descendantNode, FramedNode.child, FramedNode.move, hm,
      AffineIsometryEquiv.trans_assoc] using hw
  by_cases hi : w.1 = i
  · exact Or.inl (hi ▸ hdown)
  by_cases hj : w.1 = j
  · exact Or.inr (hj ▸ hdown)
  have hsub : Q.cell b e.val ⊆
      (R.child m w.1).carrier m ∩ (R.child m i).cell m F.val := by
    intro y hy
    exact ⟨routing_constant_step4_ascent_ports_step6_descendant_subset _ _ _ _ hdown
      (routing_constant_step4_ascent_ports_step2_cell_carrier _ _ e hy), he hy⟩
  exact False.elim ((ne_of_gt (routing_constant_step4_ascent_ports_step6_facet_measure Q b e))
    (MeasureTheory.measure_mono_null hsub (hzero w.1 hi hj)))

/-- Step 6 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.4, 1.25):
"g contains a facet e of Q (so g is the first provider of e)". A strict
descendant with an entire facet in this primitive provider lies in one of
its two owning children. Nonempty facet interiors exclude all other children. -/
private theorem routing_constant_step4_ascent_ports_step6_side_ownership
    (g : Parser.BornFacet P) (b : ℕ) (Q : FramedNode S)
    (hdesc : Q.IsDescendant b g.birth g.height) (hb : b < g.height)
    (e : FacetName S Q.ty) (he : Q.cell b e.val ⊆ g.carrier) :
    Q.IsDescendant b g.leftNode (g.height - 1) ∨
      Q.IsDescendant b g.rightNode (g.height - 1) := by
  rcases g with ⟨h, hpos, ⟨T, φ⟩, ι, hι⟩
  dsimp only at hι
  subst T
  let g : Parser.BornFacet P := ⟨h, hpos, ⟨ι.val.ty, φ⟩, ι, rfl⟩
  have hh : h - 1 + 1 = h := Nat.sub_add_cancel hpos
  refine routing_constant_step4_ascent_ports_step6_two_owners
    g.birth (h - 1) ι.val.left ι.val.right ι.val.distinct
    ι.val.leftFacet ι.val.rightFacet ?_ ?_ b Q ?_ ?_ e ?_
  · exact g.sides_carrier.2.trans g.sides_carrier.1.symm
  · change relint (g.leftNode.cell (g.height - 1) g.incidence.val.leftFacet.val) ⊆
      interior (g.birth.carrier (h - 1 + 1))
    rw [hh, g.sides_carrier.1]
    exact routing_constant_step4_ascent_ports_step3_internal g
  · simpa only [hh] using hdesc
  · simpa only [hh] using hb
  · change Q.cell b e.val ⊆ g.leftNode.cell (g.height - 1) g.incidence.val.leftFacet.val
    rwa [g.sides_carrier.1]

/-- Step 6 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 3.4, 8.3):
"every primitive facet ... has a well-defined attached packet". Retain the
right-side readout of the higher birth, including a birth at the newly
assembled parent, where the second clause of two-sided constancy applies. -/
private theorem routing_constant_step4_ascent_ports_step6_right_packet
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (g : Parser.BornFacet P) (hbirth : g.birth.IsDescendant g.height N (n + 1))
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (q : Packet P) (hq : g.packet hl = some q) :
    ∃ hr : Parser.BoundaryPackets Y (g.height - 1) g.rightNode,
      attachedPacket hr g.incidence.val.rightFacet = some q := by
  have hle := Parser.descendant_height_le _ _ _ _ hbirth
  by_cases hlt : g.height < n + 1
  · have hg := Parser.assembled_inner_mem D N A g.height g.birth hlt hbirth
    obtain ⟨_, hr, hpair, _⟩ := two_sided_constancy Y hY n hn D hD g hg
    exact ⟨hr, hpair.symm.trans hq⟩
  · have hh : g.height = n + 1 := by omega
    have hb : g.birth = N := routing_constant_step1_equal_height N g.birth (n + 1)
      (by simpa only [hh] using hbirth)
    obtain ⟨_, hr, hpair, _⟩ := two_sided_constancy_assembled Y hY n hn D hD N A g hh hb
    exact ⟨hr, hpair.symm.trans hq⟩

/-- Step 6 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 3.4, 8.3):
"the e-facing port" reads the provider's attached packet. Once its owning
side is identified, boundary inheritance and two-sided constancy identify the
whole packet, including when the provider is the newly assembled parent. -/
private theorem routing_constant_step4_ascent_ports_step6_boundary_packet
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (g : Parser.BornFacet P) (hbirth : g.birth.IsDescendant g.height N (n + 1))
    (b : ℕ) (Q : FramedNode S) (hQ : Q ∈ D.geometry.nodes b)
    (hdesc : Q.IsDescendant b g.birth g.height) (hb : b < g.height)
    (e : FacetName S Q.ty) (he : Q.cell b e.val ⊆ g.carrier)
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (q : Packet P) (hq : g.packet hl = some q)
    (u : PlacedMarkedTile (systemM S P C)) (f : FacetName S (tileNode u).ty)
    (hpiece : Parser.IsFacetPiece Y b Q e u f) :
    leafPacket (compilerLeaf C u) f.val = some q := by
  let hM := hD.boundaryPackets b Q hQ
  have hread : attachedPacket hM e = some q := by
    rcases routing_constant_step4_ascent_ports_step6_side_ownership g b Q hdesc hb e he
      with hleft | hright
    · have h := Parser.boundaryPacket_inherited Y (g.height - 1) b g.leftNode Q
        (D.geometry.node_actual _ _ hQ) hleft g.incidence.val.leftFacet e
        (by rwa [g.sides_carrier.1]) hl hM
      exact h.symm.trans hq
    · obtain ⟨hr, hqr⟩ := routing_constant_step4_ascent_ports_step6_right_packet
        Y hY n hn D hD N A g hbirth hl q hq
      have h := Parser.boundaryPacket_inherited Y (g.height - 1) b g.rightNode Q
        (D.geometry.node_actual _ _ hQ) hright g.incidence.val.rightFacet e
        (by rwa [g.sides_carrier.2]) hr hM
      exact h.symm.trans hqr
  exact (attachedPacket_eq_leaf hM e u f hpiece).symm.trans hread

/-- Step 7 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 2.5, 8.3):
"with a facet e of Q contained in g". The complete header records exactly
the boundary facets through the apex; retain this lookup for row (E3). -/
private theorem routing_constant_step4_ascent_ports_step7_boundary_cone
    (Q : FramedNode S) (b : ℕ) (φ : Iso d) (p : E d)
    (e : FacetName S Q.ty) (hp : p ∈ Q.cell b e.val)
    (H : State.Header P)
    (hH : H = routing_constant_step4_ascent_ports_step3_header Q b φ p)
    (F : FacetName S H.birthType) (hF : F.val = e.val) :
    ∃ G, H.boundaryCones F = some G := by
  classical
  subst H
  change ∃ G, (if p ∈ Q.cell b F.val then
    some (φ.linearIsometryEquiv.symm '' tangentCone (Q.cell b F.val) p) else none) = some G
  rw [hF, if_pos hp]
  exact ⟨_, rfl⟩

open scoped BigOperators Topology in
/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.0(b), 3.3, 8.3):
"with cone T_q Q". A finite simplex, including a lower-dimensional one, has a finite affine half-space presentation. -/
private lemma routing_constant_step4_ascent_ports_step5_simplex_halfspaces
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

open scoped BigOperators Topology in
/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.0(b), 3.3, 8.3):
"with cone T_q Q". A finite polyhedron has a finite union of affine half-space presentations. -/
private lemma routing_constant_step4_ascent_ports_step5_halfspace_presentation
    {K : Set (E d)} (hK : Polyhedron K) :
    ∃ S : Finset (Finset (E d →ᵃ[ℝ] ℝ)),
      K = ⋃ q ∈ S, {x | ∀ f ∈ q, 0 ≤ f x} := by
  classical
  obtain ⟨s, rfl⟩ := hK
  have hrep (t : Finset (E d)) : ∃ q : Finset (E d →ᵃ[ℝ] ℝ),
      AffineIndependent ℝ ((↑) : t → E d) →
        convexHull ℝ (t : Set (E d)) = {x | ∀ f ∈ q, 0 ≤ f x} := by
    by_cases ht : AffineIndependent ℝ ((↑) : t → E d)
    · obtain ⟨q, hq⟩ := routing_constant_step4_ascent_ports_step5_simplex_halfspaces t ht
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

open scoped BigOperators Topology in
/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.0(b), 3.3, 8.3):
"with cone T_q Q". Near the apex, inactive affine inequalities keep their sign and active inequalities become homogeneous. -/
private lemma routing_constant_step4_ascent_ports_step5_local_cone
    (S : Finset (Finset (E d →ᵃ[ℝ] ℝ))) (p : E d) :
    ∃ C : Set (E d), IsPolyhedralCone C ∧
      ∀ᶠ x in 𝓝 p,
        (x ∈ ⋃ q ∈ S, {x | ∀ f ∈ q, 0 ≤ f x}) ↔ x - p ∈ C := by
  classical
  let Q (q : Finset (E d →ᵃ[ℝ] ℝ)) : Finset (E d →ₗ[ℝ] ℝ) :=
    (q.filter fun f => f p = 0).image AffineMap.linear
  let S₀ := S.filter fun q => ∀ f ∈ q, 0 ≤ f p
  let C : Set (E d) := ⋃ r ∈ S₀.image Q, {v | ∀ l ∈ r, 0 ≤ l v}
  have hC (v : E d) : v ∈ C ↔
      ∃ q ∈ S, (∀ f ∈ q, 0 ≤ f p) ∧ ∀ f ∈ q, f p = 0 → 0 ≤ f.linear v := by
    simp [C, S₀, Q]
    constructor
    · rintro ⟨q, ⟨hq, hpq⟩, hvq⟩
      exact ⟨q, hq, hpq, fun f hf hf0 => hvq f.linear f hf hf0 rfl⟩
    · rintro ⟨q, hq, hpq, hvq⟩
      refine ⟨q, ⟨hq, hpq⟩, ?_⟩
      rintro l f hf hf0 rfl
      exact hvq f hf hf0
  refine ⟨C, ⟨S₀.image Q, rfl⟩, ?_⟩
  have hsign (f : E d →ᵃ[ℝ] ℝ) : ∀ᶠ x in 𝓝 p,
      (f p < 0 → f x < 0) ∧ (0 < f p → 0 < f x) := by
    have hc := f.continuous_of_finiteDimensional.continuousAt (x := p)
    apply Filter.Eventually.and
    · by_cases hf : f p < 0
      · exact (hc.eventually_lt_const hf).mono fun x hx _ => hx
      · exact Filter.Eventually.of_forall fun x h => (hf h).elim
    · by_cases hf : 0 < f p
      · exact (hc.eventually_const_lt hf).mono fun x hx _ => hx
      · exact Filter.Eventually.of_forall fun x h => (hf h).elim
  have hall : ∀ᶠ x in 𝓝 p, ∀ q ∈ S, ∀ f ∈ q,
      (f p < 0 → f x < 0) ∧ (0 < f p → 0 < f x) :=
    (Filter.eventually_all_finset S).mpr fun q _ =>
      (Filter.eventually_all_finset q).mpr fun f _ => hsign f
  filter_upwards [hall] with x hx
  rw [hC]
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨q, hq, hxq⟩
    refine ⟨q, hq, ?_, ?_⟩
    · intro f hf
      by_contra hn
      exact (not_lt_of_ge (hxq f hf)) ((hx q hq f hf).1 (lt_of_not_ge hn))
    · intro f hf hfp
      have he : f.linear (x - p) = f x - f p := f.linearMap_vsub x p
      rw [he, hfp, sub_zero]
      exact hxq f hf
  · rintro ⟨q, hq, hpq, hvq⟩
    refine ⟨q, hq, ?_⟩
    intro f hf
    rcases eq_or_lt_of_le (hpq f hf) with hfp | hfp
    · have hv := hvq f hf hfp.symm
      have he : f.linear (x - p) = f x - f p := f.linearMap_vsub x p
      simpa [he, hfp.symm] using hv
    · exact ((hx q hq f hf).2 hfp).le

open scoped BigOperators Topology in
/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.0(b), 3.3, 8.3):
"with cone T_q Q". Positive radial scaling preserves each homogeneous half-space and each finite union of their intersections. -/
private lemma routing_constant_step4_ascent_ports_step5_positive_scaling
    {C : Set (E d)} (hC : IsPolyhedralCone C) {r : ℝ} (hr : 0 < r) (v : E d) :
    r • v ∈ C ↔ v ∈ C := by
  obtain ⟨S, rfl⟩ := hC
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, map_smul, smul_eq_mul,
    mul_nonneg_iff_of_pos_left hr]

open scoped BigOperators Topology in
/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.0(b), 3.3, 8.3):
"with cone T_q Q". A local homogeneous model is exactly the radial tangent cone used in the recorded header. -/
private lemma routing_constant_step4_ascent_ports_step5_radial_germ
    {K C : Set (E d)} (p : E d) (hC : IsPolyhedralCone C)
    (hloc : ∀ᶠ x in 𝓝 p, x ∈ K ↔ x - p ∈ C) : tangentCone K p = C := by
  ext v
  have htend : Filter.Tendsto (fun t : ℝ => p + t • v) (𝓝 0) (𝓝 p) := by
    have hc : Continuous (fun t : ℝ => p + t • v) := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), p + t • v ∈ K ↔ t • v ∈ C := by
    simpa only [add_sub_cancel_left] using htend.eventually hloc
  obtain ⟨δ, hδ, hδloc⟩ := Metric.eventually_nhds_iff.mp hev
  constructor
  · rintro ⟨ε, hε, hv⟩
    let t := min ε δ / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have htε : t < ε := by dsimp [t]; linarith [min_le_left ε δ]
    have htδ : t < δ := by dsimp [t]; linarith [min_le_right ε δ]
    have hnear : dist t 0 < δ := by simpa [Real.dist_eq, abs_of_pos ht] using htδ
    exact (routing_constant_step4_ascent_ports_step5_positive_scaling hC ht v).mp
      ((hδloc hnear).mp (hv t ht htε))
  · intro hv
    refine ⟨δ, hδ, fun t ht htδ => ?_⟩
    have hnear : dist t 0 < δ := by simpa [Real.dist_eq, abs_of_pos ht] using htδ
    exact (hδloc hnear).mpr
      ((routing_constant_step4_ascent_ports_step5_positive_scaling hC ht v).mpr hv)

open scoped BigOperators Topology in
/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.0(b), 3.3, 8.3):
"the actual frames". An affine prototype frame preserves the finite polyhedral presentation. -/
private theorem routing_constant_step4_ascent_ports_step5_polyhedron_image
    (K : Set (E d)) (hK : Polyhedron K) (φ : E d ≃ᵃ[ℝ] E d) :
    Polyhedron (φ '' K) := by
  classical
  obtain ⟨s, hs⟩ := hK
  have hmap (p : Finset (E d)) : φ '' convexHull ℝ (p : Set (E d)) =
      convexHull ℝ (φ '' (p : Set (E d))) := φ.toAffineMap.image_convexHull _
  refine ⟨s.image (fun p => p.image φ), ?_⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hs] at hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp hz
    refine mem_iUnion₂.mpr ⟨p.image φ, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    rw [Finset.coe_image, ← hmap]
    exact mem_image_of_mem φ hzp
  · intro hy
    obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    rw [Finset.coe_image, ← hmap] at hyq
    obtain ⟨z, hz, rfl⟩ := hyq
    refine ⟨z, ?_, rfl⟩
    rw [hs]
    exact mem_iUnion₂.mpr ⟨p, hp, hz⟩

open scoped BigOperators Topology in
/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.0(b), 3.3, 8.3):
"the realised cone T_q Q". Tangent directions transform by the linear part of the full affine frame. -/
private theorem routing_constant_step4_ascent_ports_step5_tangent_image
    (φ : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) (x : E d) :
    tangentCone (φ '' K) (φ x) = φ.linear '' tangentCone K x := by
  have hmap (t : ℝ) (u : E d) : φ (x + t • u) = φ x + t • φ.linear u := by
    simpa only [vadd_eq_add, map_smul, add_comm] using φ.map_vadd x (t • u)
  ext u
  constructor
  · rintro ⟨ε, hε, hmem⟩
    refine ⟨φ.linear.symm u, ⟨ε, hε, ?_⟩, φ.linear.apply_symm_apply u⟩
    intro t ht htε
    have hm := hmem t ht htε
    rw [← φ.linear.apply_symm_apply u, ← hmap] at hm
    exact φ.injective.mem_set_image.mp hm
  · rintro ⟨u, ⟨ε, hε, hmem⟩, rfl⟩
    exact ⟨ε, hε, fun t ht htε => hmap t u ▸
      Set.mem_image_of_mem φ (hmem t ht htε)⟩

open scoped Topology in
/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.0(b), 3.3):
"with cone T_q Q". A finite polyhedron and its radial tangent cone give
the same membership test in a neighbourhood of the apex. -/
private theorem routing_constant_step4_ascent_ports_step5_local_model
    (K : Set (E d)) (hK : Polyhedron K) (p : E d) :
    ∀ᶠ x in 𝓝 p, x ∈ K ↔ x - p ∈ tangentCone K p := by
  obtain ⟨s, hs⟩ := routing_constant_step4_ascent_ports_step5_halfspace_presentation hK
  obtain ⟨G, hG, hlocal⟩ := routing_constant_step4_ascent_ports_step5_local_cone s p
  rw [← hs] at hlocal
  rwa [routing_constant_step4_ascent_ports_step5_radial_germ p hG hlocal]

/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.1, 3.3):
"tiles ... with pieces in e at q". Relative interior points of a placed
cell approach every point of its closed carrier. -/
private theorem routing_constant_step4_ascent_ports_step5_cell_regular
    (Q : FramedNode S) (b : ℕ) (e : Cell d) :
    closure (relint (Q.cell b e)) = Q.cell b e := by
  have hcl : Q.prototypeFrame b '' closure (relint e.carrier) =
      closure (Q.prototypeFrame b '' relint e.carrier) :=
    (Q.prototypeFrame b).toHomeomorphOfFiniteDimensional.image_closure _
  rw [FramedNode.cell, routing_constant_step4_ascent_ports_step3_relint_image,
    ← hcl, e.flat.regularClosed]

open scoped Topology in
/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.1, 3.3):
"the geometry ... identifies ... ports". Equal boundary tangent cones give
a local meeting of relative interiors; hereditary trace extends that meeting
to the entire named native facet. -/
private theorem routing_constant_step4_ascent_ports_step5_same_cone_trace
    (M Q : FramedNode S) (m b : ℕ) (hdesc : M.IsDescendant m Q b)
    (f : FacetName S M.ty) (e : FacetName S Q.ty)
    (K : Set (E d)) (hK : Polyhedron K) (hsub : M.cell m f.val ⊆ K)
    (p : E d) (hp : p ∈ M.cell m f.val)
    (hcone : tangentCone (Q.cell b e.val) p = tangentCone K p) :
    M.cell m f.val ⊆ Q.cell b e.val := by
  have hpoly : Polyhedron (Q.cell b e.val) :=
    routing_constant_step4_ascent_ports_step5_polyhedron_image _ e.val.flat.polyhedral _
  have hlocal : ∀ᶠ x in 𝓝 p, x ∈ Q.cell b e.val ↔ x ∈ K := by
    filter_upwards [routing_constant_step4_ascent_ports_step5_local_model _ hpoly p,
      routing_constant_step4_ascent_ports_step5_local_model K hK p] with x hx hy
    rw [hx, hy, hcone]
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hlocal
  have hpcl : p ∈ closure (relint (M.cell m f.val)) := by
    rwa [routing_constant_step4_ascent_ports_step5_cell_regular]
  obtain ⟨x, hx, hxp⟩ := Metric.mem_closure_iff.mp hpcl ε hε
  apply hereditary_trace Q M b m hdesc e.val f.val (facetCell e).property (facetCell f).property
  exact ⟨x, hx, (hnear (by simpa only [dist_comm] using hxp)).mpr
    (hsub (intrinsicInterior_subset hx))⟩

/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 3.3):
"the actual frames". Moving a node carries its named cells by the same
isometry; raw cell names require no dependent transport. -/
private theorem routing_constant_step4_ascent_ports_step5_cell_move
    (Q : FramedNode S) (b : ℕ) (e : Cell d) (φ : Iso d) :
    (Q.move φ).cell b e = φ '' Q.cell b e := by
  simp only [FramedNode.cell, FramedNode.prototypeFrame, FramedNode.move, Set.image_image]
  rfl

/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 3.3):
"the actual frames". A common isometry preserves the exact role word and
heights in a descendant relation. -/
private theorem routing_constant_step4_ascent_ports_step5_descendant_move
    (M Q : FramedNode S) (m b : ℕ) (hdesc : M.IsDescendant m Q b) (φ : Iso d) :
    (M.move φ).IsDescendant m (Q.move φ) b := by
  obtain ⟨r, hr, w, hw⟩ := hdesc
  refine ⟨r, hr, w, ?_⟩
  rw [hw]
  simp only [FramedNode.move, AffineIsometryEquiv.trans_assoc]

/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 3.3):
"the common-listed vertex". Equal singleton cells have equal anchor points,
even when their vertex names belong to different prototype types. -/
private theorem routing_constant_step4_ascent_ports_step5_vertex_point
    {A B : S.ι} (v : VertexName S A) (w : VertexName S B) (h : v.val = w.val) :
    vertexPoint v = vertexPoint w := by
  have hs : ({vertexPoint v} : Set (E d)) = {vertexPoint w} :=
    (vertexPoint_spec v).symm.trans ((congrArg Cell.carrier h).trans (vertexPoint_spec w))
  exact Set.singleton_injective hs

/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 1.19, 3.3, 8.3):
"with interior points in int(q + T_q Q) near q". A native facet piece
at the event vertex approaches the parent's cone because it is a descendant
of that parent and its own listed vertex has a local cone neighbourhood. -/
private theorem routing_constant_step4_ascent_ports_step5_approaches
    (Y : MarkedTiling (systemM S P C)) (b : ℕ) (Q : FramedNode S)
    (hQ : IsBlock Y b Q) (e : FacetName S Q.ty) (p : E d)
    (t : PlacedMarkedTile (systemM S P C)) (j : EndSlot (compilerLeaf C t))
    (hp : Compiler.endVertex (compilerFrame C t) j = p)
    (hheader : j.header = routing_constant_step4_ascent_ports_step3_header
      Q b (compilerFrame C t) p)
    (u : PlacedMarkedTile (systemM S P C)) (f : FacetName S (tileNode u).ty)
    (v : VertexName S (tileNode u).ty) (hpiece : Parser.IsFacetPiece Y b Q e u f)
    (hv : v.val.carrier ⊆ f.val.carrier)
    (hvp : compilerFrame C u (vertexPoint v) = p) :
    Parser.ApproachesSector u (Compiler.endVertex (compilerFrame C t) j)
      (Compiler.endSector (compilerFrame C t) j) := by
  have hphys : u.carrier = (tileNode u).carrier 0 := by
    rw [compilerFrame_carrier]
    simp [tileNode, FramedNode.carrier, SubstSystem.supertile]
  have hpf : p ∈ (tileNode u).cell 0 f.val :=
    ⟨vertexPoint v, hv (by rw [vertexPoint_spec]; exact Set.mem_singleton _), hvp⟩
  have hpcar := routing_constant_step4_ascent_ports_step2_cell_carrier _ _ f hpf
  have hlisted : (tileNode u).Lists 0 p :=
    ⟨v.val, v.property, vertexPoint v, by rw [vertexPoint_spec]; exact Set.mem_singleton _, hvp⟩
  obtain ⟨r, hr, hrad⟩ := uniform_prototype_cone_radius S
  have hlocal := hrad (tileNode u) p hlisted
  have hsub := routing_constant_step4_ascent_ports_step6_descendant_subset _ _ _ _ hpiece.2.1
  have hcones : tangentCone ((tileNode u).carrier 0) p ⊆ tangentCone (Q.carrier b) p := by
    rintro w ⟨δ, hδ, hw⟩
    exact ⟨δ, hδ, fun s hs hsδ => hsub (hw s hs hsδ)⟩
  have hsector : Compiler.endSector (compilerFrame C t) j =
      (fun w => p + w) '' tangentCone (Q.carrier b) p := by
    simp only [Compiler.endSector, hp, hheader, routing_constant_step4_ascent_ports_step3_header,
      Set.image_image, LinearIsometryEquiv.apply_symm_apply]
  have hregular : IsRegularClosed ((tileNode u).carrier 0) :=
    ((⟨Q, hQ⟩ : Block Y b).innerBlock 0 (tileNode u) hpiece.2.1).carrier_regular.2.1
  have hpcl : p ∈ closure (interior ((tileNode u).carrier 0)) := by
    rw [hregular]
    exact hpcar
  intro ε hε
  obtain ⟨x, hx, hxp⟩ := Metric.mem_closure_iff.mp hpcl (min r ε) (lt_min hr hε)
  let V := interior ((tileNode u).carrier 0) ∩ ball p (min r ε)
  have hopen : IsOpen V := isOpen_interior.inter isOpen_ball
  have hxV : x ∈ V := ⟨hx, by simpa only [mem_ball, dist_comm] using hxp⟩
  have hVS : V ⊆ Compiler.endSector (compilerFrame C t) j := by
    rintro y ⟨hy, hyr⟩
    have hm : y ∈ (tileNode u).carrier 0 ∩ ball p r :=
      ⟨interior_subset hy, mem_ball.mpr
        (lt_of_lt_of_le (mem_ball.mp hyr) (min_le_left _ _))⟩
    rw [hlocal] at hm
    rw [hsector]
    exact Set.image_mono hcones hm.1
  have hVI : V ⊆ interior (Compiler.endSector (compilerFrame C t) j) :=
    hopen.subset_interior_iff.mpr hVS
  exact ⟨x, ⟨hphys.symm ▸ hx, hVI hxV⟩,
    hp.symm ▸ mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hxV.2) (min_le_right _ _))⟩

/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 2.3, 3.3):
"the realised cone T_q Q". At native height, the honest source header is
normalized by precisely the central tile's isometric frame. -/
private theorem routing_constant_step4_ascent_ports_step5_native_header
    (U : HonestSource S) (t : U.Node) (ht : t.1 = 0)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) :
    U.headerOf P t f hf v = routing_constant_step4_ascent_ports_step3_header
      (U.hierarchy.birthParent t f hf).2.val (U.hierarchy.birthParent t f hf).1
      t.2.val.frame (t.2.val.prototypeFrame t.1 (vertexPoint v)) := by
  have hframe : t.2.val.prototypeFrame t.1 = t.2.val.frame.toAffineEquiv := by
    simp only [ht]
    ext x
    rfl
  have hnorm (K : Set (E d)) : U.normalizeCone t K =
      t.2.val.frame.linearIsometryEquiv.symm '' K := by
    rw [HonestSource.normalizeCone, hframe]
    rfl
  unfold HonestSource.headerOf
  simp only [hnorm, routing_constant_step4_ascent_ports_step3_header]

/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 2.5, 3.3):
"the geometry ... identifies ... ports". Equality of complete headers
identifies the same raw boundary name and its normalized tangent cone. -/
private theorem routing_constant_step4_ascent_ports_step5_header_boundary
    (R Q : FramedNode S) (c b : ℕ) (φ ψ : Iso d) (x p : E d)
    (hheader : routing_constant_step4_ascent_ports_step3_header (P := P) R c φ x =
      routing_constant_step4_ascent_ports_step3_header Q b ψ p)
    (e : FacetName S Q.ty) (hp : p ∈ Q.cell b e.val) :
    ∃ E : FacetName S R.ty, E.val = e.val ∧ x ∈ R.cell c E.val ∧
      φ.linearIsometryEquiv.symm '' tangentCone (R.cell c E.val) x =
        ψ.linearIsometryEquiv.symm '' tangentCone (Q.cell b e.val) p := by
  classical
  have hty : R.ty = Q.ty := congrArg State.Header.birthType hheader
  let E : FacetName S R.ty := ⟨e.val, by rw [hty]; exact e.property⟩
  have hlookup := congrArg (fun H : State.Header P =>
    if h : e.val ∈ (S.cx H.birthType).facets then H.boundaryCones ⟨e.val, h⟩ else none)
    hheader
  have he : e.val ∈ (S.cx R.ty).facets := E.property
  simp only [routing_constant_step4_ascent_ports_step3_header, dif_pos he,
    dif_pos e.property, if_pos hp] at hlookup
  by_cases hx : x ∈ R.cell c e.val
  · rw [if_pos hx] at hlookup
    exact ⟨E, rfl, hx, Option.some.inj hlookup⟩
  · rw [if_neg hx] at hlookup
    cases hlookup

/-- Step 5 of the V4 proof of `routing_constant_step4_ascent_ports` (V4 3.3, 8.3):
"the e-facing tiles ... belong to the template". In an already occurring
complete END star with the actual birth header, a given native boundary piece
at its apex is one of the annotated ports on that same named parent facet.
This is only the geometric port identification, without a packet assertion. -/
private theorem routing_constant_step4_ascent_ports_step5_boundary_port
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (b : ℕ) (Q : FramedNode S) (hb : 1 ≤ b) (hQ : IsBlock Y b Q)
    (e : FacetName S Q.ty) (p : E d)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (j : EndSlot (compilerLeaf C t))
    (hp : Compiler.endVertex (compilerFrame C t) j = p)
    (hheader : j.header = routing_constant_step4_ascent_ports_step3_header
      Q b (compilerFrame C t) p)
    (T : EndTemplate j) (hrow : endRow T)
    (hactual : TemplateOccurs C Y (compilerFrame C t) T.configuration)
    (u : PlacedMarkedTile (systemM S P C)) (f : FacetName S (tileNode u).ty)
    (v : VertexName S (tileNode u).ty) (hpiece : Parser.IsFacetPiece Y b Q e u f)
    (hv : v.val.carrier ⊆ f.val.carrier)
    (hvp : compilerFrame C u (vertexPoint v) = p) :
    ∃ a : BoundaryPort P T.geometry.header.birthType,
      a ∈ T.geometry.boundaryPorts ∧ (a.tile, compilerLeaf C u) ∈ T.configuration.tiles ∧
        a.parentFacet.val = e.val ∧ a.facet.val = f.val := by
  classical
  have hnear := routing_constant_step4_ascent_ports_step5_approaches
    Y b Q hQ e p t j hp hheader u f v hpiece hv hvp
  obtain ⟨z, hz, huz⟩ := (trigger_coverage Y hY t ht j T.configuration
    ⟨T, rfl, hrow⟩ hactual u hpiece.1 hnear).1
  have hul : compilerLeaf C u = z.2 := by
    rw [huz]
    exact (compiler_decode_unique C _ _).1
  have huframe : compilerFrame C u = z.1.frame.trans (compilerFrame C t) := by
    rw [huz]
    exact (compiler_decode_unique C _ _).2
  obtain ⟨U, t₀, ht₀, f₀, hf₀, v₀, hv₀, _, hreal⟩ := T.honest_geometry
  let B := U.hierarchy.birthParent t₀ f₀ hf₀
  let x := t₀.2.val.prototypeFrame t₀.1 (vertexPoint v₀)
  let J := t₀.2.val.frame.symm.trans (compilerFrame C t)
  have hgeom : z.1 ∈ T.geometry.tiles := by
    rw [← T.tiles_eq]
    exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  rw [hreal.2.2.2.1] at hgeom
  obtain ⟨q₀, hq₀, hqz⟩ := Finset.mem_image.mp hgeom
  have hstar : q₀.1 = 0 ∧ U.hierarchy.ancestor q₀ B.1 = B ∧
      x ∈ q₀.2.val.carrier q₀.1 := by
    simpa only [ownedStar, Set.Finite.mem_toFinset, ownedStarSet, Set.mem_setOf_eq]
      using hq₀
  have hqty : q₀.2.val.ty = (tileNode u).ty := by
    change q₀.2.val.ty = (compilerLeaf C u).prototype
    rw [hul]
    exact (congrArg FramedNode.ty hqz).trans (T.configuration.types_match z hz)
  let F : FacetName S q₀.2.val.ty := ⟨f.val, by rw [hqty]; exact f.property⟩
  let w : VertexName S q₀.2.val.ty := ⟨v.val, by rw [hqty]; exact v.property⟩
  have hnode : q₀.2.val.move J = tileNode u := by
    apply FramedNode.ext
    · exact hqty
    · change q₀.2.val.frame.trans J = compilerFrame C u
      rw [huframe, ← hqz]
      rfl
  have hvertex : vertexPoint v₀ = vertexPoint j.vertex :=
    (routing_constant_step4_ascent_ports_step5_vertex_point T.geometry.vertex v₀
      hreal.2.1).symm.trans
    (routing_constant_step4_ascent_ports_step5_vertex_point T.geometry.vertex j.vertex
      T.vertex_eq)
  have hx : x = t₀.2.val.frame (vertexPoint v₀) := by
    dsimp only [x]
    simp only [ht₀]
    rfl
  have hxp : J x = p := by
    change compilerFrame C t (t₀.2.val.frame.symm x) = p
    rw [hx, AffineIsometryEquiv.symm_apply_apply, hvertex]
    exact hp
  have hpf : p ∈ (tileNode u).cell 0 f.val :=
    ⟨vertexPoint v, hv (by rw [vertexPoint_spec]; exact Set.mem_singleton _), hvp⟩
  have hhead : routing_constant_step4_ascent_ports_step3_header (P := P)
      B.2.val B.1 t₀.2.val.frame x =
      routing_constant_step4_ascent_ports_step3_header Q b (compilerFrame C t) p :=
    (routing_constant_step4_ascent_ports_step5_native_header U t₀ ht₀ f₀ hf₀ v₀).symm.trans
      (hreal.2.2.1.symm.trans (T.header_eq.trans hheader))
  obtain ⟨e₀, hE, hxE, hcones⟩ :=
    routing_constant_step4_ascent_ports_step5_header_boundary B.2.val Q B.1 b
      t₀.2.val.frame (compilerFrame C t) x p hhead e (hpiece.2.2 hpf)
  have hcone : tangentCone ((B.2.val.move J).cell B.1 e₀.val) p =
      tangentCone (Q.cell b e.val) p := by
    rw [routing_constant_step4_ascent_ports_step5_cell_move]
    have htan := routing_constant_step4_ascent_ports_step5_tangent_image
      J.toAffineEquiv (B.2.val.cell B.1 e₀.val) x
    change tangentCone (J '' B.2.val.cell B.1 e₀.val) (J x) = _ at htan
    rw [hxp] at htan
    rw [htan]
    have hc := congrArg (fun K : Set (E d) =>
      (compilerFrame C t).linearIsometryEquiv '' K) hcones
    simpa only [Set.image_image, LinearIsometryEquiv.apply_symm_apply,
      Set.image_id'] using hc
  have hdesc := U.hierarchy.ancestor_descendant q₀ B.1
  rw [hstar.2.1] at hdesc
  have hdescJ := routing_constant_step4_ascent_ports_step5_descendant_move
    _ _ _ _ hdesc J
  have htrace : (q₀.2.val.move J).cell q₀.1 F.val ⊆
      (B.2.val.move J).cell B.1 e₀.val := by
    apply routing_constant_step4_ascent_ports_step5_same_cone_trace _ _ _ _
      hdescJ F e₀ (Q.cell b e.val)
      (routing_constant_step4_ascent_ports_step5_polyhedron_image _ e.val.flat.polyhedral _)
      (by simpa only [hnode, hstar.1] using hpiece.2.2) p
      (by simpa only [hnode, hstar.1] using hpf) hcone
  have htrace₀ : q₀.2.val.cell q₀.1 F.val ⊆ B.2.val.cell B.1 e₀.val := by
    rw [routing_constant_step4_ascent_ports_step5_cell_move,
      routing_constant_step4_ascent_ports_step5_cell_move] at htrace
    intro y hy
    obtain ⟨z, hz, heq⟩ := htrace (Set.mem_image_of_mem J hy)
    rwa [J.injective heq] at hz
  have hw : vertexPoint w = vertexPoint v :=
    routing_constant_step4_ascent_ports_step5_vertex_point w v rfl
  have hxw : x = q₀.2.val.prototypeFrame q₀.1 (vertexPoint w) := by
    apply J.injective
    rw [hxp]
    simp only [hstar.1]
    change p = (q₀.2.val.move J).frame (vertexPoint w)
    rw [hnode, hw]
    exact hvp.symm
  have hbB : 1 ≤ B.1 := (U.providerOccurrence_data P t₀ f₀ hf₀).1
  obtain ⟨path, hpath⟩ := sourceRestrictionPath_exists U B q₀
    (by rw [hstar.1]; omega) (by simpa only [hstar.1, Nat.sub_zero] using hstar.2.1)
    e₀ F htrace₀
  have hBty : T.geometry.header.birthType = B.2.val.ty :=
    congrArg State.Header.birthType hreal.2.2.1
  let a : BoundaryPort P T.geometry.header.birthType := {
    tile := q₀.2.val.move t₀.2.val.frame.symm
    facet := F
    vertex := w
    onFacet := hv
    parentFacet := ⟨e₀.val, by rw [hBty]; exact e₀.property⟩
    restriction := restrictionOp path }
  refine ⟨a, (hreal.2.2.2.2.2 a).mpr ?_, ?_, hE, rfl⟩
  · exact ⟨q₀, hq₀, e₀, F, w, hv, hxw, htrace₀, rfl, rfl, rfl, rfl,
      path, hpath, rfl⟩
  · change (q₀.2.val.move t₀.2.val.frame.symm, compilerLeaf C u) ∈ _
    rwa [hqz, hul]

/-- Step 4 of the V4 proof of `routing_constant` (V4 8.3):
"The common-listed vertex and the e-facing port given by Lemma 1.25 belong
to an END template with cone T_q Q". Transport the ascent to the actual
frames and identify a boundary port reading the higher facet's packet in
an END event whose central packet is the lower facet's packet. The named
boundary facet and its recorded cone are retained for applying E3. -/
private theorem routing_constant_step4_ascent_ports
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (f f' : PrimitiveFacet S N.ty) (hf : f.depth < P.k) (hf' : f'.depth < P.k)
    (g g' : Parser.BornFacet P)
    (hg : routing_constant_step1_realizes N (n + 1) f g)
    (hg' : routing_constant_step1_realizes N (n + 1) f' g')
    (hlink : AscentLink P.k f f')
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (hl' : Parser.BoundaryPackets Y (g'.height - 1) g'.leftNode)
    (q q' : Packet P) (hq : g.packet hl = some q) (hq' : g'.packet hl' = some q') :
    g.birth.IsDescendant g.height g'.birth g'.height ∧
      ∃ e : FacetName S g.birth.ty, g.birth.cell g.height e.val ⊆ g'.carrier ∧
        ∃ t ∈ Y.tiles, ∃ (slot : EndSlot (compilerLeaf C t)) (T : EndTemplate slot),
          TemplateOccurs C Y (compilerFrame C t) T.configuration ∧ endRow T ∧
            slot.packet = q ∧
            ∃ (a : BoundaryPort P T.geometry.header.birthType) (u : LeafType P),
              a ∈ T.geometry.boundaryPorts ∧ (a.tile, u) ∈ T.configuration.tiles ∧
              a.parentFacet.val = e.val ∧
              (∃ G, T.geometry.header.boundaryCones a.parentFacet = some G) ∧
              leafPacket u a.facet.val = some q' := by
  classical
  have hsum := hg.1
  have hsum' := hg'.1
  have hdepth := hlink.1
  have hlt : g.height < g'.height := by omega
  have hold : g.height < n + 1 := by omega
  have hfm : f.depth ≤ n + 1 := by omega
  have hh : n + 1 - f.depth = g.height := by omega
  have hbirth := routing_constant_step1_descendant N (n + 1) f g hg
  have hbirth' := routing_constant_step1_descendant N (n + 1) f' g' hg'
  have hdesc := routing_constant_step4_ascent_ports_step1_ancestry
    N (n + 1) f f' hf hf' g g' hg hg' hlink
  obtain ⟨e₀, he₀, p, hp, hpe, hcommon, hface⟩ := hlink.2.2
  have htype : g.birth.ty = f.birthType := by
    rw [hg.2.1]
    exact (f.birthFrame_spec (n + 1) hfm).1
  have hframe : g.birth.prototypeFrame g.height =
      f.birthFrame.trans (N.prototypeFrame (n + 1)) := by
    rw [hg.2.1, ← hh]
    exact routing_constant_step1_frame N (n + 1) f hfm
  obtain ⟨e, _, hcell, hpe', hcommon', hface'⟩ :=
    routing_constant_step4_ascent_ports_step1_seed_geometry N (n + 1) f
      g.birth g.height g.positive htype hframe e₀ p hpe hcommon hface
  have he : g.birth.cell g.height e.val ⊆ g'.carrier := by
    rw [hcell, hg'.2.2]
    exact Set.image_mono he₀
  have hpg : N.prototypeFrame (n + 1) p ∈ g.carrier := by
    rw [hg.2.2]
    exact Set.mem_image_of_mem _ hp.1
  have hG := Parser.assembled_inner_mem D N A g.height g.birth hold hbirth
  obtain ⟨t, ht, slot, hslot, hpoint, hheader⟩ :=
    routing_constant_step4_ascent_ports_step3_seed D hD g hG
      (N.prototypeFrame (n + 1) p) hpg hcommon' hl q hq
  obtain ⟨T, hactual, hrow⟩ :=
    routing_constant_step4_ascent_ports_step4_event Y hY t ht slot
  obtain ⟨u, F, v, hpiece, hv, hvp⟩ :=
    routing_constant_step4_ascent_ports_step2_boundary_piece Y g.height g.birth
      g.positive (D.geometry.node_actual _ _ hG) e (N.prototypeFrame (n + 1) p)
      hcommon' hface'
  obtain ⟨a, ha, hau, hae, haf⟩ :=
    routing_constant_step4_ascent_ports_step5_boundary_port Y hY g.height g.birth
      g.positive (D.geometry.node_actual _ _ hG) e (N.prototypeFrame (n + 1) p)
      t ht slot hpoint hheader T hrow hactual u F v hpiece hv hvp
  have hcone := routing_constant_step4_ascent_ports_step7_boundary_cone
    g.birth g.height (compilerFrame C t) (N.prototypeFrame (n + 1) p) e hpe'
    T.geometry.header (T.header_eq.trans hheader) a.parentFacet hae
  have hpacket := routing_constant_step4_ascent_ports_step6_boundary_packet
    Y hY n hn D hD N A g' hbirth' g.height g.birth hG hdesc hlt e he
      hl' q' hq' u F hpiece
  exact ⟨hdesc, e, he, t, ht, slot, T, hactual, hrow, hslot,
    a, compilerLeaf C u, ha, hau, hae, hcone, haf.symm ▸ hpacket⟩

/-- Step 4 of the V4 proof of `routing_constant` (V4 8.3):
"Row (E3) gives P(g)[s] = P(f)[s+delta]". The lower birth is old, so its
packet head is its assigned state. The uncapped record and actual boundary
port identify the GROUP packet, giving the exact height shift. -/
private theorem routing_constant_step4_ascent_agree
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (f f' : PrimitiveFacet S N.ty) (hf : f.depth < P.k) (hf' : f'.depth < P.k)
    (g g' : Parser.BornFacet P)
    (hg : routing_constant_step1_realizes N (n + 1) f g)
    (hg' : routing_constant_step1_realizes N (n + 1) f' g')
    (hlink : AscentLink P.k f f')
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (hl' : Parser.BoundaryPackets Y (g'.height - 1) g'.leftNode)
    (q q' : Packet P) (hq : g.packet hl = some q) (hq' : g'.packet hl' = some q') :
    ShiftedAgree q' q (g'.height - g.height) := by
  have hsum := hg.1
  have hsum' := hg'.1
  have hdepth := hlink.1
  have hh : g.height < g'.height := by omega
  have hold : g.height < n + 1 := by omega
  have huncapped : g'.height - g.height < P.C := by rw [P.C_eq]; omega
  have hbirth := routing_constant_step1_descendant N (n + 1) f g hg
  have hbirth' := routing_constant_step1_descendant N (n + 1) f' g' hg'
  have hM := Parser.assembled_inner_mem D N A g.height g.birth hold hbirth
  obtain ⟨hdesc, e, he, t, ht, slot, T, _, hrow, hslot, a, u, ha, hu, heq, hcone, hport⟩ :=
    routing_constant_step4_ascent_ports Y hY n hn D hD N A f f' hf hf' g g'
      hg hg' hlink hl hl' q q' hq hq'
  obtain ⟨r, hr, _, hage⟩ := routing_constant_step4_inherited_record D hD N A
    g.height g.birth hM g' hbirth' hdesc hh e he huncapped
  have hhead := (routing_constant_step2_old_readout Y hY n hn D hD g hM hl q hq).2
  have hread : stateRecordAt slot.packet.head a.parentFacet.val = some r := by
    rw [hslot, hhead, heq]
    exact hr
  have hgroup := hrow.2.2.1.2 a.parentFacet hcone
  rw [hread] at hgroup
  obtain ⟨p, _, _, _, hports, hshift⟩ := hgroup
  have hp : p = q' := Option.some.inj ((hports a ha rfl u hu).symm.trans hport)
  have hshift' := hshift (by simpa only [hage] using huncapped)
  simpa only [hp, hslot, hage] using hshift'

/-- Step 5 of the V4 proof of `routing_constant` (V4 8.3):
"this finite union of closed sets". Every primitive carrier is a nonempty
compact affine image of its realizing facet cell. -/
private theorem routing_constant_step5_facet_compact {T : S.ι}
    (f : PrimitiveFacet S T) : IsCompact f.carrier ∧ f.carrier.Nonempty := by
  obtain ⟨i, e, he, _⟩ := f.realization
  have hc : IsCompact f.localCarrier := by
    rw [he]
    exact e.val.flat.compact.image (S.child _ i).frame.continuous
  have hn : f.localCarrier.Nonempty := by
    rw [he]
    exact e.val.flat.connected.nonempty.image _
  exact ⟨(hc.image (LinearMap.continuous_of_finiteDimensional
    (S.σ.symm : E d →ₗ[ℝ] E d))).image
      f.birthFrame.toAffineMap.continuous_of_finiteDimensional,
    (hn.image _).image _⟩

/-- Step 5 of the V4 proof of `routing_constant` (V4 8.3):
"a disconnected intersection graph would split this finite union of closed
sets into two disjoint nonempty closed subsets". Values agreeing on
intersections are constant on a preconnected finite union. Nonemptiness of
each member is explicit, so empty members cannot carry arbitrary values. -/
private theorem routing_constant_step5_finite_closed_values
    {X ι V : Type*} [TopologicalSpace X] [Finite ι]
    (K : ι → Set X) (v : ι → V)
    (hc : ∀ i, IsClosed (K i)) (hne : ∀ i, (K i).Nonempty)
    (hconn : IsPreconnected (⋃ i, K i))
    (hlocal : ∀ i j, (K i ∩ K j).Nonempty → v i = v j) (i j : ι) :
    v i = v j := by
  classical
  by_contra hij
  let U : Set X := ⋃ a ∈ {a | v a = v i}, K a
  let W : Set X := ⋃ a ∈ {a | v a ≠ v i}, K a
  have hU : IsClosed U := (Set.toFinite _).isClosed_biUnion (fun a _ => hc a)
  have hW : IsClosed W := (Set.toFinite _).isClosed_biUnion (fun a _ => hc a)
  have hcover : (⋃ a, K a) ⊆ U ∪ W := by
    intro x hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    by_cases hv : v a = v i
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨a, hv, ha⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨a, hv, ha⟩)
  obtain ⟨x, hx⟩ := hne i
  obtain ⟨y, hy⟩ := hne j
  have hi : ((⋃ a, K a) ∩ U).Nonempty :=
    ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩, Set.mem_iUnion₂.mpr ⟨i, rfl, hx⟩⟩
  have hj : ((⋃ a, K a) ∩ W).Nonempty :=
    ⟨y, Set.mem_iUnion.mpr ⟨j, hy⟩,
      Set.mem_iUnion₂.mpr ⟨j, Ne.symm hij, hy⟩⟩
  obtain ⟨z, _, hzU, hzW⟩ :=
    (isPreconnected_closed_iff.mp hconn) U W hU hW hcover hi hj
  obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp hzU
  obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.mp hzW
  exact hb ((hlocal a b ⟨z, hza, hzb⟩).symm.trans ha)

/-- Step 5 of the V4 proof of `routing_constant` (V4 8.3):
"At an intersection point, Lemma 1.25 connects the facets by same-parent
and ascent links." Apply that route at each intersection, then use the
finite closed cover of the selected connected component. -/
private theorem routing_constant_step5_connected_values (T : S.ι) {V : Type*}
    (v : {f : PrimitiveFacet S T // f ∈ P.E_A T} → V)
    (hlink : ∀ f g, RoutingLink P.k f.val g.val → v f = v g)
    (f g : {f : PrimitiveFacet S T // f ∈ P.E_A T}) : v f = v g := by
  classical
  have hmem : ∀ a : PrimitiveFacet S T,
      a ∈ P.E_A T ↔ a ∈ principalFacets S T P.k (P.component T) := by
    intro a
    exact Set.ext_iff.mp (P.E_A_eq T) a
  have hconn : IsPreconnected (P.component T) := by
    obtain ⟨x, hx, he⟩ := P.component_valid T
    rw [he]
    exact isPreconnected_connectedComponentIn
  have hunion : (⋃ a : {f : PrimitiveFacet S T // f ∈ P.E_A T}, a.val.carrier) =
      P.component T := by
    rw [(principalFacets_spec T P.k (P.component T) (P.component_valid T)).2.2]
    ext x
    simp only [Set.mem_iUnion, exists_prop, Subtype.exists]
    exact exists_congr (fun a => and_congr_left (fun _ => hmem a))
  apply routing_constant_step5_finite_closed_values (fun a => a.val.carrier) v
    (fun a => (routing_constant_step5_facet_compact a.val).1.isClosed)
    (fun a => (routing_constant_step5_facet_compact a.val).2)
    (hunion.symm ▸ hconn) ?_ f g
  intro a b hab
  obtain ⟨x, hxa, hxb⟩ := hab
  have route := birth_ascent_routing T P.k (P.component T) (P.component_valid T)
    x a.val b.val ((hmem a.val).mp a.property) ((hmem b.val).mp b.property) hxa hxb
  have H : ∀ c, Relation.ReflTransGen
      (ThroughLink (principalFacets S T P.k (P.component T)) x (RoutingLink P.k))
      a.val c → ∀ hc : c ∈ P.E_A T, v a = v ⟨c, hc⟩ := by
    intro c route
    induction route with
    | refl => intro _; rfl
    | @tail c e _ hce ih =>
      intro he
      have hc := (hmem c).mpr hce.1
      exact (ih hc).trans (hlink ⟨c, hc⟩ ⟨e, he⟩ hce.2.2.2.2)
  exact H b.val route b.property

end RoutingConstant

/-- R9, V4 3.10, replacement V4 8.3: every primitive facet of E_P born
inside P within depth k-1 has its P-slot PRESENT and equal to newState.
The attached packet is honest. First-generation births of P are included,
using R5's second clause without assuming any state of P beforehand. -/
theorem routing_constant (g : Parser.BornFacet P)
    (hbirth : g.birth.IsDescendant g.height N (n + 1))
    (hdepth : n + 1 - g.height < P.k) (hprincipal : P.InPrincipal N (n + 1) g.carrier) :
    ∃ hleft : Parser.BoundaryPackets Y (g.height - 1) g.leftNode,
      ∃ q : Packet P, g.packet hleft = some q ∧ q ∈ honestPackets S P ∧
        decode q ⟨n + 1 - g.height, hdepth⟩ = some (newState Y hY n hn D hD N A) := by
  classical
  let F := {f : PrimitiveFacet S N.ty // f ∈ P.E_A N.ty}
  have hex (f : F) : ∃ (G : Parser.BornFacet P)
      (hl : Parser.BoundaryPackets Y (G.height - 1) G.leftNode)
      (q : Packet P) (s : State P),
      routing_constant_step1_realizes N (n + 1) f.val G ∧
      G.packet hl = some q ∧ q ∈ honestPackets S P ∧
      decode q ⟨f.val.depth, P.principal_depth _ _ f.property⟩ = some s := by
    have hf := P.principal_depth _ _ f.property
    obtain ⟨G, hG⟩ := routing_constant_step1_realize (P := P) N (n + 1) f.val
      (by have := P.K_address; omega)
    have hb := routing_constant_step1_descendant N (n + 1) f.val G hG
    have hd : n + 1 - G.height = f.val.depth := by have := hG.1; omega
    have hdp : n + 1 - G.height < P.k := by omega
    have hp : P.InPrincipal N (n + 1) G.carrier := ⟨f.val, f.property, hG.2.2.symm⟩
    obtain ⟨hl, q, hq, hhon⟩ := routing_constant_step2_attachment Y hY n hn D hD N A G hb
    obtain ⟨s, hs⟩ := routing_constant_step2_present Y hY n hn D hD N A G hb hdp hp hl q hq hhon
    exact ⟨G, hl, q, s, hG, hq, hhon, by simpa only [hd] using hs⟩
  choose G HL Q V HG HQ HH HV using hex
  have hlinks : ∀ (f f' : F), RoutingLink P.k f.val f'.val → V f = V f' := by
    intro f f' hlink
    rcases hlink with hs | ha | ha
    · have h := routing_constant_step3_same_parent_agree Y hY n hn D hD N A
        f.val f'.val (G f) (G f') (HG f) (HG f') hs (HL f) (HL f') (Q f) (Q f')
        (HQ f) (HQ f')
      have hd : f.val.depth = f'.val.depth := congrArg Sigma.fst hs.1
      exact h _ _ _ (HV f) (by simpa only [hd] using HV f')
    · have h := routing_constant_step4_ascent_agree Y hY n hn D hD N A
        f.val f'.val (P.principal_depth _ _ f.property) (P.principal_depth _ _ f'.property)
        (G f) (G f') (HG f) (HG f') ha (HL f) (HL f') (Q f) (Q f') (HQ f) (HQ f')
      have he : f.val.depth = f'.val.depth + ((G f').height - (G f).height) := by
        have := (HG f).1; have := (HG f').1; have := ha.1; omega
      exact (h _ _ _ _ he (HV f') (HV f)).symm
    · have h := routing_constant_step4_ascent_agree Y hY n hn D hD N A
        f'.val f.val (P.principal_depth _ _ f'.property) (P.principal_depth _ _ f.property)
        (G f') (G f) (HG f') (HG f) ha (HL f') (HL f) (Q f') (Q f) (HQ f') (HQ f)
      have he : f'.val.depth = f.val.depth + ((G f).height - (G f').height) := by
        have := (HG f).1; have := (HG f').1; have := ha.1; omega
      exact h _ _ _ _ he (HV f) (HV f')
  let r := Parser.readableFacet Y hY n hn D hD N A (Parser.firstChild N.ty)
  have hrbirth : r.birthFacet.birth.IsDescendant r.birthFacet.height N (n + 1) :=
    Parser.descendant_trans _ _ _ _ _ _ r.inside_child (by
      rw [A.child_eq]
      exact Parser.child_descendant N n _)
  have hrdepth : n + 1 - r.birthFacet.height < P.k := by
    rw [← r.parentSlot_eq]
    exact r.parentSlot.isLt
  obtain ⟨f₀, hf₀, hr⟩ := routing_constant_step1_normalize N (n + 1) r.birthFacet
    hrbirth hrdepth r.parent_principal
  let a₀ : F := ⟨f₀, hf₀⟩
  have hG₀ : G a₀ = r.birthFacet :=
    routing_constant_step1_unique N (n + 1) f₀ (G a₀) r.birthFacet (HG a₀) hr
  have hQ₀ : Q a₀ = r.packet := by
    have hread : r.birthFacet.packet r.constancy = some (Q a₀) := by
      simpa only [hG₀] using HQ a₀
    exact Option.some.inj (hread.symm.trans r.attached)
  have hj₀ : (⟨f₀.depth, P.principal_depth _ _ hf₀⟩ : Fin P.k) = r.parentSlot := by
    apply Fin.ext
    have := hr.1
    have := r.parentSlot_eq
    dsimp only
    omega
  have hV₀ : V a₀ = newState Y hY n hn D hD N A := by
    have h := HV a₀
    change decode (Q a₀) ⟨f₀.depth, _⟩ = some (V a₀) at h
    rw [hQ₀, hj₀] at h
    exact Option.some.inj (h.symm.trans r.parent_decode)
  obtain ⟨f, hf, hg⟩ := routing_constant_step1_normalize N (n + 1) g hbirth hdepth hprincipal
  let a : F := ⟨f, hf⟩
  have hG : G a = g := routing_constant_step1_unique N (n + 1) f (G a) g (HG a) hg
  have hV : V a = newState Y hY n hn D hD N A :=
    (routing_constant_step5_connected_values N.ty V hlinks a a₀).trans hV₀
  subst g
  refine ⟨HL a, Q a, HQ a, HH a, ?_⟩
  have hd : n + 1 - (G a).height = f.depth := by
    have hsum : (G a).height + f.depth = n + 1 := (HG a).1
    omega
  simpa only [hd] using (HV a).trans (congrArg some hV)

/-- R9, V4 3.10: in particular every first-generation primitive facet of P
has head S(P), the entire compressed packet's reconstructed bottom state. -/
theorem first_generation_head (g : Parser.BornFacet P)
    (hheight : g.height = n + 1) (hbirth : g.birth = N)
    (hleft : Parser.BoundaryPackets Y (g.height - 1) g.leftNode) :
    ∃ q : Packet P, g.packet hleft = some q ∧ q ∈ honestPackets S P ∧
      q.head = newState Y hY n hn D hD N A := by
  sorry

/-- R9, V4 3.10: the new parent state belongs to the honest state alphabet. -/
theorem newState_honest : newState Y hY n hn D hD N A ∈ honestStates S P := by
  sorry

/-- R9, V4 3.10: the new state has the assembled parent's actual prototype. -/
theorem newState_type : (newState Y hY n hn D hD N A).ty = N.ty := by
  sorry

/-- R10, V4 3.11: every actual child's old state is the deterministic child
of S(P) at the prescribed globally distinct role (A_P,i). -/
theorem child_equations (i : S.I N.ty) :
    D.blockState (A.children i).val (A.children i).property =
      childMap P (newState Y hY n hn D hD N A) ⟨N.ty, i⟩ := by
  sorry

/-- R9/R10, V4 3.10--3.11, 3.1 (I1): child descent fixes the new height residue. -/
theorem newState_residue :
    (newState Y hY n hn D hD N A).residue.val = (n + 1) % P.L := by
  sorry


section PacketConstancy

omit hY hn hD A

/-- Step 1 of the V4 proof of `packet_constancy` (V4 3.12(a), 1.1):
"the facets of children of P contained in F tile F". A strict descendant
of the parent passes through one immediate child, read off its role word. -/
private theorem packet_constancy_step1_through_child (R Q : FramedNode S) (m b : ℕ)
    (hdesc : Q.IsDescendant b R (m + 1)) (hb : b < m + 1) :
    ∃ i : S.I R.ty, Q.IsDescendant b (R.child m i) m := by
  obtain ⟨r, hr, w, hw⟩ := hdesc
  have hrpos : 0 < r := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
  have hm : m = b + r := by omega
  refine ⟨w.1, r, hm, w.2, ?_⟩
  simpa only [SubstSystem.descendantNode, FramedNode.child, FramedNode.move, hm,
    AffineIsometryEquiv.trans_assoc] using hw

/-- Step 1 of the V4 proof of `packet_constancy` (V4 3.12(a), 1.3, 1.8):
"the facets of children of P contained in F tile F". A native piece on the
parent facet F is a native piece on one child facet contained in F: facet
dichotomy places it in a child facet, and the hereditary trace puts that
whole child facet in F. -/
private theorem packet_constancy_step1_piece_descends
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (N : FramedNode S) (F : FacetName S N.ty)
    (t : PlacedMarkedTile (systemM S P C)) (g : FacetName S (tileNode t).ty)
    (hpiece : Parser.IsFacetPiece Y (n + 1) N F t g) :
    ∃ (i : S.I N.ty) (f : FacetName S (N.child n i).ty),
      (N.child n i).cell n f.val ⊆ N.cell (n + 1) F.val ∧
        Parser.IsFacetPiece Y n (N.child n i) f t g := by
  obtain ⟨i, hi⟩ :=
    packet_constancy_step1_through_child N (tileNode t) n 0 hpiece.2.1 (by omega)
  have hne : (relint ((tileNode t).cell 0 g.val)).Nonempty := by
    rw [FramedNode.cell, routing_constant_step4_inherited_record_step1_relint_image]
    exact g.val.flat.relint_nonempty.image _
  obtain ⟨x, hx⟩ := hne
  have hxF : x ∈ N.cell (n + 1) F.val := hpiece.2.2 (intrinsicInterior_subset hx)
  have hxfront : x ∈ closure (N.carrier (n + 1)) \ interior (N.carrier (n + 1)) :=
    routing_constant_step4_inherited_record_step1_boundary N (n + 1) F hxF
  rcases facet_dichotomy (N.child n i) (tileNode t) n 0 hi g with ⟨f, hf, _⟩ | hint
  · have hxf := routing_constant_step4_inherited_record_step1_relint_mono _ _ _ _ g f hf hx
    have hfF : (N.child n i).cell n f.val ⊆ N.cell (n + 1) F.val :=
      hereditary_trace N (N.child n i) (n + 1) n (Parser.child_descendant N n i) F.val f.val
        (facetCell F).property (facetCell f).property ⟨x, hxf, hxF⟩
    exact ⟨i, f, hfF, hpiece.1, hi, hf⟩
  · exact False.elim (hxfront.2 (interior_mono
      (routing_constant_step4_ascent_ports_step6_child_subset N n i) (hint hx)))

/-- Step 2 of the V4 proof of `packet_constancy` (V4 3.12(a), 3.7):
"each child facet has a constant attached packet ((I5) for the children)".
Every assembled child is an old decoded node, so (I5) applies to it. -/
private theorem packet_constancy_step2_child_node {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (N : FramedNode S) (A : Parser.AssembledParent D N)
    (i : S.I N.ty) : N.child n i ∈ D.geometry.nodes n := by
  rw [← A.child_eq i]
  exact D.geometry.root_mem (A.children i).val (A.children i).property

/-- Step 3 of the V4 proof of `packet_constancy` (V4 3.12(a), 2.3):
"inherited facets lying in the same parent facet are related". A coalescence
witness for the parent tracks lifts one level to the contained child tracks. -/
private theorem packet_constancy_step3_tracks
    (U : HonestSource S) (q c : U.Node) (hparent : U.hierarchy.parentNode c = q)
    (F F' : FacetName S q.2.val.ty) (f f' : FacetName S c.2.val.ty)
    (hf : c.2.val.cell c.1 f.val ⊆ q.2.val.cell q.1 F.val)
    (hf' : c.2.val.cell c.1 f'.val ⊆ q.2.val.cell q.1 F'.val)
    (hE : U.TracksCoalesce q F F') : U.TracksCoalesce c f f' := by
  have hanc (a : ℕ) : U.hierarchy.ancestor c (a + 1) = U.hierarchy.ancestor q a := by
    simp only [CoherentHierarchy.ancestor, Function.iterate_succ_apply, hparent]
  obtain ⟨a, hboundary, G, hFG, hF'G⟩ := hE
  let G' : FacetName S (U.hierarchy.ancestor c (a + 1)).2.val.ty :=
    ⟨G.val, (congrArg (fun z : U.Node => z.2.val.ty) (hanc a).symm) ▸ G.property⟩
  have hcell := congrArg (fun z : U.Node => z.2.val.cell z.1 G.val) (hanc a)
  dsimp only at hcell
  refine ⟨a + 1, ?_, G', ?_, ?_⟩
  · intro j hj
    cases j with
    | zero =>
      exact ⟨routing_constant_step4_inherited_record_step1_boundary c.2.val c.1 f,
        routing_constant_step4_inherited_record_step1_boundary c.2.val c.1 f'⟩
    | succ j =>
      have hfront := congrArg (fun z : U.Node => frontier (z.2.val.carrier z.1)) (hanc j)
      dsimp only at hfront
      have hb := hboundary j (by omega)
      constructor
      · change c.2.val.cell c.1 f.val ⊆ _
        rw [hfront]
        exact hf.trans hb.1
      · change c.2.val.cell c.1 f'.val ⊆ _
        rw [hfront]
        exact hf'.trans hb.2
  · change c.2.val.cell c.1 f.val ⊆ (U.hierarchy.ancestor c (a + 1)).2.val.cell
      (U.hierarchy.ancestor c (a + 1)).1 G.val
    rw [hcell]
    exact hf.trans hFG
  · change c.2.val.cell c.1 f'.val ⊆ (U.hierarchy.ancestor c (a + 1)).2.val.cell
      (U.hierarchy.ancestor c (a + 1)).1 G.val
    rw [hcell]
    exact hf'.trans hF'G

/-- Step 3 of the V4 proof of `packet_constancy` (V4 3.12(a), 3.11):
"S(C) = D_S(S(P),i) ... E_C is the relation computed from S(P)". Realize
the honest parent state and use deterministic child descent. -/
private theorem packet_constancy_step3_child_E
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N) (i : S.I N.ty)
    (F F' : FacetName S N.ty) (f f' : FacetName S (N.child n i).ty)
    (hf : (N.child n i).cell n f.val ⊆ N.cell (n + 1) F.val)
    (hf' : (N.child n i).cell n f'.val ⊆ N.cell (n + 1) F'.val)
    (hE : stateEAt (newState Y hY n hn D hD N A) F.val F'.val) :
    stateEAt (childMap P (newState Y hY n hn D hD N A) ⟨N.ty, i⟩) f.val f'.val := by
  obtain ⟨U, hU, hs⟩ := routing_constant_step2_source_realization
    (newState Y hY n hn D hD N A) (newState_honest Y hY n hn D hD N A) N (n + 1)
    (newState_type Y hY n hn D hD N A) (newState_residue Y hY n hn D hD N A)
  let q : U.Node := ⟨n + 1, ⟨N, hU⟩⟩
  change stateOf U P q = newState Y hY n hn D hD N A at hs
  have hq : 1 ≤ q.1 := by change 1 ≤ n + 1; omega
  let c := U.childNode q hq i
  have hparent : U.hierarchy.parentNode c = q := by
    apply Sigma.ext
    · simp [c, q, HonestSource.childNode, CoherentHierarchy.parentNode]
    · apply heq_of_eq
      apply Subtype.ext
      exact (U.hierarchy.parent_unique n _ N hU ⟨i, rfl⟩).symm
  have htracks : U.TracksCoalesce q F F' := by
    rw [← hs] at hE
    obtain ⟨_, _, hE⟩ := hE
    exact (U.mem_coalescenceTable q F F').mp hE
  have hchild := packet_constancy_step3_tracks U q c hparent F F' f f' hf hf' htracks
  have hEc : stateEAt (stateOf U P c) f.val f'.val :=
    ⟨f.property, f'.property, (U.mem_coalescenceTable c f f').mpr hchild⟩
  simpa only [c, childMap_spec U P q hq i, hs] using hEc

/-- Step 3 of the V4 proof of `packet_constancy` (V4 3.12(a), 2.3, 3.11):
"If C = C': both f, f' are inherited from F, so E_C(f,f') is true ...
f ∩ f' ⊇ κ ≠ ∅; by (I5) for C, equal packets". The parent relation is
reflexive, so the (S5) rule relates the two inherited child facets. -/
private theorem packet_constancy_step3_same_child
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N) (i : S.I N.ty)
    (F : FacetName S N.ty) (f f' : FacetName S (N.child n i).ty)
    (hf : (N.child n i).cell n f.val ⊆ N.cell (n + 1) F.val)
    (hf' : (N.child n i).cell n f'.val ⊆ N.cell (n + 1) F.val)
    (hmeet : ((N.child n i).cell n f.val ∩ (N.child n i).cell n f'.val).Nonempty) :
    attachedPacket (hD.boundaryPackets n (N.child n i)
        (packet_constancy_step2_child_node D N A i)) f =
      attachedPacket (hD.boundaryPackets n (N.child n i)
        (packet_constancy_step2_child_node D N A i)) f' := by
  have hB := packet_constancy_step2_child_node D N A i
  have hstate : D.stateAt n (N.child n i) hB =
      childMap P (newState Y hY n hn D hD N A) ⟨N.ty, i⟩ := by
    simpa only [DecodedLevel.blockState, A.child_eq] using child_equations Y hY n hn D hD N A i
  obtain ⟨hc, hEc⟩ := hD.I5 n (N.child n i) hB
  have hF : F.val ∈ (S.cx (newState Y hY n hn D hD N A).ty).facets := by
    rw [newState_type Y hY n hn D hD N A]
    exact F.property
  have hE : stateEAt (newState Y hY n hn D hD N A) F.val F.val :=
    ⟨hF, hF, (newState Y hY n hn D hD N A).E_refl ⟨F.val, hF⟩⟩
  have hEchild : stateEAt (D.stateAt n (N.child n i) hB) f.val f'.val := by
    rw [hstate]
    exact packet_constancy_step3_child_E Y hY n hn D hD N A i F F f f' hf hf' hE
  exact hEc f f' hEchild hmeet
/-- Step 4 of the V4 proof of `packet_constancy` (V4 3.12(a), 1.3):
"a first-generation facet h of P". Normalize the internal child facet and
assign its canonical primitive incidence, retaining the actual birth frame. -/
private theorem packet_constancy_step4_birth
    (N : FramedNode S) (n : ℕ) (i : S.I N.ty) (f : FacetName S (N.child n i).ty)
    (hint : relint ((N.child n i).cell n f.val) ⊆ interior (N.carrier (n + 1))) :
    ∃ g : Parser.BornFacet P, g.height = n + 1 ∧ g.birth = N ∧
      g.carrier = (N.child n i).cell n f.val := by
  let H := ((S.σ ^ n).toAffineEquiv.trans N.frame.toAffineEquiv).toHomeomorphOfFiniteDimensional
  let K := placedSet (S.child N.ty i).frame f.val.carrier
  have hf : (N.child n i).cell n f.val = H '' K := by
    simp only [FramedNode.cell, Set.image_image, K, placedSet]
    apply Set.image_congr
    intro x _
    exact congrArg N.frame (routing_constant_step4_ascent_ports_step1_child_scaled n i x)
  have hN : N.carrier (n + 1) = H '' S.supertile 1 N.ty := by
    simp [H, FramedNode.carrier, SubstSystem.supertile, placedSet, Set.image_image,
      pow_succ, LinearEquiv.mul_apply]
  have hlocal : relint K ⊆ interior (S.supertile 1 N.ty) := by
    intro x hx
    have hm := hint (hf.symm ▸ (routing_constant_step4_ascent_ports_step3_relint_image
      ((S.σ ^ n).toAffineEquiv.trans N.frame.toAffineEquiv) K).symm ▸
        Set.mem_image_of_mem H hx)
    rw [hN, ← H.image_interior] at hm
    exact H.injective.mem_set_image.mp hm
  let f₀ : PrimitiveFacet S N.ty := ⟨0, (), K, ⟨i, f, rfl, hlocal⟩⟩
  obtain ⟨a, hat, hac⟩ := routing_constant_step1_incidence (P := P) f₀
  let g : Parser.BornFacet P := ⟨n + 1, by omega, N, a, hat⟩
  refine ⟨g, rfl, rfl, ?_⟩
  rw [routing_constant_step1_carrier]
  change N.prototypeFrame (n + 1) '' (S.σ.symm '' a.val.positioned) = _
  rw [hac]
  change N.prototypeFrame (n + 1) '' (S.σ.symm '' K) = _
  rw [hf]
  simp only [Set.image_image]
  apply Set.image_congr
  intro x _
  change N.frame ((S.σ ^ (n + 1)) (S.σ.symm x)) = N.frame ((S.σ ^ n) x)
  rw [pow_succ]
  simp

open scoped Topology in
/-- Step 5 of the V4 proof of `packet_constancy` (V4 3.12(a), 1.8):
"a vertex q of κ". An extreme point in the relative interior of a cell
forces that cell to be a singleton. -/
private theorem packet_constancy_step5_extreme_cell (K L : Set (E d)) (hLK : L ⊆ K)
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

/-- Step 5 of the V4 proof of `packet_constancy` (V4 3.12(a), 1.8):
"a vertex q of κ". Every listed cell contains a listed vertex. -/
private theorem packet_constancy_step5_cell_vertex
    (Q : PolyManifoldDomain d) (K : CellComplex Q) (e : Cell d) (he : e ∈ K.cells) :
    ∃ v ∈ K.vertices, v.carrier ⊆ e.carrier := by
  obtain ⟨q, hq⟩ := e.flat.compact.extremePoints_nonempty e.flat.connected.nonempty
  have hqP : q ∈ frontier Q.carrier := by
    rw [← K.carriers_cover]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hq.1⟩
  let v := K.minimalCell q hqP
  have hv := K.minimalCell_mem q hqP
  have hvsub := K.minimalCell_subset q hqP e he hq.1
  have hvsing : v.carrier = {q} := packet_constancy_step5_extreme_cell e.carrier v.carrier hvsub q hq
    (K.mem_relint_minimalCell q hqP)
  refine ⟨v, Finset.mem_filter.mpr ⟨hv, ?_⟩, hvsub⟩
  have hdim := v.flat.dimension
  rw [cellDirection, hvsing, direction_affineSpan, vectorSpan_singleton, finrank_bot] at hdim
  exact hdim.symm

/-- Step 5 of the V4 proof of `packet_constancy` (V4 3.12(a), 2.4, 3.10):
"Tiles along h at q have END slots at q with recorded cone T_qP ... let
θ_q be the template". The common-listed vertex q of a first-generation
facet h of P carries an actual END event whose row holds. -/
private theorem packet_constancy_step5_event
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (p : E d)
    (hcommon : ∀ i : S.I N.ty, p ∈ (N.child n i).carrier n → (N.child n i).Lists n p)
    (g : Parser.BornFacet P) (hh : g.height = n + 1) (hb : g.birth = N)
    (hpg : p ∈ g.carrier) :
    ∃ t ∈ Y.tiles, ∃ (j : EndSlot (compilerLeaf C t)) (T : EndTemplate j),
      Compiler.endVertex (compilerFrame C t) j = p ∧
      j.header = routing_constant_step4_ascent_ports_step3_header
        N (n + 1) (compilerFrame C t) p ∧
      TemplateOccurs C Y (compilerFrame C t) T.configuration ∧ endRow T := by
  have hdesc : g.birth.IsDescendant g.height N (n + 1) := by
    rw [hh, hb]
    exact Parser.descendant_refl N (n + 1)
  have hL : g.leftNode ∈ D.geometry.nodes (g.height - 1) :=
    Parser.assembled_inner_mem D N A _ _ (by omega)
      (Parser.descendant_trans _ _ _ _ _ _ g.sides_descendant.1 hdesc)
  have hl := hD.boundaryPackets _ _ hL
  obtain ⟨q, hq, _, _⟩ := first_generation_head Y hY n hn D hD N A g hh hb hl
  have hpf : p ∈ g.leftNode.cell (g.height - 1) g.incidence.val.leftFacet.val := by
    rwa [g.sides_carrier.1]
  have hpcar := routing_constant_step4_ascent_ports_step2_cell_carrier
    g.leftNode (g.height - 1) g.incidence.val.leftFacet hpf
  have hpL : g.leftNode.Lists (g.height - 1) p := by
    obtain ⟨i, hi⟩ := routing_constant_step4_ascent_ports_step3_left_child g
    rw [hi] at hpcar ⊢
    have hh' : g.height - 1 = n := by omega
    rw [hh'] at hpcar ⊢
    subst hb
    exact hcommon i hpcar
  obtain ⟨t, f, v, hpiece, hv, hvp⟩ :=
    routing_constant_step4_ascent_ports_step2_facet_at_vertex Y (g.height - 1)
      ⟨g.leftNode, D.geometry.node_actual _ _ hL⟩ g.incidence.val.leftFacet p hpL hpf
  obtain ⟨j, _, hjp, hjheader⟩ :=
    routing_constant_step3_same_parent_ports_step3_inherited_slot D hD N A g hdesc p
      hpL t f v hpiece hv hvp hl q hq
  obtain ⟨T, hactual, hrow⟩ :=
    routing_constant_step4_ascent_ports_step4_event Y hY t hpiece.1 j
  refine ⟨t, hpiece.1, j, T, hjp, ?_, hactual, hrow⟩
  rw [hh, hb] at hjheader
  exact hjheader

/-- Step 6 of the V4 proof of `packet_constancy` (V4 3.12(a), 1.8, 2.5):
"If C ≠ C': Lemma 1.8 provides a first-generation facet h of P with κ ⊆ h
and a vertex q of κ ... common-listed ... Row (E6) equates their packets".
Adjacent facets of two different children carry equal attached packets. -/
private theorem packet_constancy_step6_cross_child
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N) (F : FacetName S N.ty)
    (a b : BoundaryFacet N n F) (hab : boundaryFacetAdjacent N n F a b)
    (hchild : a.val.1 ≠ b.val.1) :
    attachedPacket (hD.boundaryPackets n (N.child n a.val.1)
        (packet_constancy_step2_child_node D N A a.val.1)) a.val.2 =
      attachedPacket (hD.boundaryPackets n (N.child n b.val.1)
        (packet_constancy_step2_child_node D N A b.val.1)) b.val.2 := by
  obtain ⟨_, e, e', hed, _, hee', hea, he'b⟩ := id hab
  have hκb : (N.child n a.val.1).cell n e.val ⊆ (N.child n b.val.1).cell n b.val.2.val :=
    hee' ▸ he'b
  obtain ⟨v, hv, hve⟩ :=
    packet_constancy_step5_cell_vertex (S.proto (N.child n a.val.1).ty)
      (S.cx (N.child n a.val.1).ty) e.val e.property
  obtain ⟨x, hx⟩ := v.flat.connected.nonempty
  have hpL : (N.child n a.val.1).Lists n ((N.child n a.val.1).prototypeFrame n x) :=
    ⟨v, hv, x, hx, rfl⟩
  have hpκ : (N.child n a.val.1).prototypeFrame n x ∈ (N.child n a.val.1).cell n e.val :=
    ⟨x, hve hx, rfl⟩
  obtain ⟨i₀, h, hint, _, hlist⟩ :=
    adjacency_primitive_seed N n F a b hab hchild e hed hea hκb
  obtain ⟨_, hph, hcommon⟩ := hlist _ hpL hpκ
  obtain ⟨g, hh, hb, hg⟩ := packet_constancy_step4_birth (P := P) N n i₀ h hint
  obtain ⟨t, ht, j, T, hjp, hjheader, hactual, hrow⟩ :=
    packet_constancy_step5_event Y hY n hn D hD N A _ hcommon g hh hb (hg.symm ▸ hph)
  have hBa := packet_constancy_step2_child_node D N A a.val.1
  have hBb := packet_constancy_step2_child_node D N A b.val.1
  have hpb : (N.child n a.val.1).prototypeFrame n x ∈ (N.child n b.val.1).cell n b.val.2.val :=
    hκb hpκ
  obtain ⟨u, fu, vu, hpu, hvu, hvpu⟩ :=
    routing_constant_step4_ascent_ports_step2_facet_at_vertex Y n
      ⟨N.child n a.val.1, D.geometry.node_actual _ _ hBa⟩ a.val.2 _ hpL (hea hpκ)
  obtain ⟨u', fu', vu', hpu', hvu', hvpu'⟩ :=
    routing_constant_step4_ascent_ports_step2_facet_at_vertex Y n
      ⟨N.child n b.val.1, D.geometry.node_actual _ _ hBb⟩ b.val.2 _
      (hcommon b.val.1 (routing_constant_step4_ascent_ports_step2_cell_carrier _ _ _ hpb)) hpb
  have hNu : Parser.IsFacetPiece Y (n + 1) N F u fu :=
    ⟨hpu.1, Parser.descendant_trans _ _ _ _ _ _ hpu.2.1 (Parser.child_descendant N n a.val.1),
      hpu.2.2.trans a.property⟩
  have hNu' : Parser.IsFacetPiece Y (n + 1) N F u' fu' :=
    ⟨hpu'.1, Parser.descendant_trans _ _ _ _ _ _ hpu'.2.1 (Parser.child_descendant N n b.val.1),
      hpu'.2.2.trans b.property⟩
  obtain ⟨α, hα, hαu, hαF, hαf⟩ :=
    routing_constant_step4_ascent_ports_step5_boundary_port Y hY (n + 1) N (by omega) A.actual
      F _ t ht j hjp hjheader T hrow hactual u fu vu hNu hvu hvpu
  obtain ⟨β, hβ, hβu, hβF, hβf⟩ :=
    routing_constant_step4_ascent_ports_step5_boundary_port Y hY (n + 1) N (by omega) A.actual
      F _ t ht j hjp hjheader T hrow hactual u' fu' vu' hNu' hvu' hvpu'
  have hE6 := hrow.2.2.2.2.2 α hα β hβ (hαF.trans hβF.symm) _ _ hαu hβu
  rw [hαf, hβf] at hE6
  rw [attachedPacket_eq_leaf _ _ u fu hpu, attachedPacket_eq_leaf _ _ u' fu' hpu']
  exact hE6

end PacketConstancy

/-- R11, V4 3.12(a): every boundary facet of the new parent has one constant
actual native-packet readout. NULL is retained, so this also covers faults. -/
theorem packet_constancy : Parser.BoundaryPackets Y (n + 1) N := by
  intro F
  let hc : ∀ i : S.I N.ty, Parser.BoundaryPackets Y n (N.child n i) := fun i =>
    hD.boundaryPackets n (N.child n i) (packet_constancy_step2_child_node D N A i)
  let val : BoundaryFacet N n F → Option (Packet P) := fun a =>
    attachedPacket (hc a.val.1) a.val.2
  have hadj : ∀ a b, boundaryFacetAdjacent N n F a b → val a = val b := by
    intro a b hab
    by_cases hchild : a.val.1 = b.val.1
    · rcases a with ⟨⟨i, f⟩, hf⟩
      rcases b with ⟨⟨i', f'⟩, hf'⟩
      dsimp only at hchild hf hf'
      subst hchild
      obtain ⟨_, e, e', _, _, hee', hea, he'b⟩ := hab
      obtain ⟨y, hy⟩ := e.val.flat.connected.nonempty
      have hye : (N.child n i).prototypeFrame n y ∈ (N.child n i).cell n e.val := ⟨y, hy, rfl⟩
      have hye' : (N.child n i).prototypeFrame n y ∈ (N.child n i).cell n e'.val := by
        rw [← hee']
        exact hye
      exact packet_constancy_step3_same_child Y hY n hn D hD N A i F f f' hf hf'
        ⟨_, hea hye, he'b hye'⟩
    · exact packet_constancy_step6_cross_child Y hY n hn D hD N A F a b hab hchild
  have hall : ∀ a b, Relation.ReflTransGen (boundaryFacetAdjacent N n F) a b →
      val a = val b := by
    intro a b h
    induction h with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (hadj _ _ hbc)
  obtain ⟨a₀⟩ := (boundary_facet_adjacency N n F).2.2.1
  have hconst : Parser.ConstantPacket Y (n + 1) N F (val a₀) := by
    intro t g hpiece
    obtain ⟨i, f, hfF, hp⟩ := packet_constancy_step1_piece_descends Y n N F t g hpiece
    exact (attachedPacket_eq_leaf (hc i) f t g hp).symm.trans
      (hall ⟨⟨i, f⟩, hfF⟩ a₀ ((boundary_facet_adjacency N n F).2.2.2 _ _))
  exact ⟨val a₀, hconst, fun q hq =>
    Parser.constantPacket_unique Y (n + 1) N A.actual F q (val a₀) hq hconst⟩

section PacketEEquality

omit hY hn hD A

open scoped Topology in
/-- Step 1 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"we may take q a vertex". An extreme point in the relative interior of
one of the intersection's cells forces that cell to be a singleton. -/
private theorem packet_E_equality_step1_extreme_cell (K L : Set (E d)) (hLK : L ⊆ K)
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

/-- Step 1 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"F ∩ F' is a union of cells". Every listed cell contains a listed
zero-dimensional cell, so choosing the minimal intersection cell suffices. -/
private theorem packet_E_equality_step1_cell_vertex
    (Q : PolyManifoldDomain d) (K : CellComplex Q) (e : Cell d) (he : e ∈ K.cells) :
    ∃ v ∈ K.vertices, v.carrier ⊆ e.carrier := by
  obtain ⟨q, hq⟩ := e.flat.compact.extremePoints_nonempty e.flat.connected.nonempty
  have hqP : q ∈ frontier Q.carrier := by
    rw [← K.carriers_cover]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hq.1⟩
  let v := K.minimalCell q hqP
  have hv := K.minimalCell_mem q hqP
  have hvsub := K.minimalCell_subset q hqP e he hq.1
  have hvsing : v.carrier = {q} := packet_E_equality_step1_extreme_cell e.carrier v.carrier hvsub q hq
    (K.mem_relint_minimalCell q hqP)
  refine ⟨v, Finset.mem_filter.mpr ⟨hv, ?_⟩, hvsub⟩
  have hdim := v.flat.dimension
  rw [cellDirection, hvsing, direction_affineSpan, vectorSpan_singleton, finrank_bot] at hdim
  exact hdim.symm

/-- Step 1 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"we may take q a vertex of P in F ∩ F'". The minimal cell at an
intersection point lies in both facets, and contains a listed vertex. -/
private theorem packet_E_equality_step1_common_vertex
    (N : FramedNode S) (m : ℕ) (F F' : FacetName S N.ty)
    (hmeet : (N.cell m F.val ∩ N.cell m F'.val).Nonempty) :
    ∃ p : E d, N.Lists m p ∧ p ∈ N.cell m F.val ∧ p ∈ N.cell m F'.val := by
  obtain ⟨p, ⟨x, hx, hxp⟩, hp'⟩ := hmeet
  have hx' : x ∈ F'.val.carrier := by
    rw [← hxp] at hp'
    exact (N.prototypeFrame m).injective.mem_set_image.mp hp'
  have hxfront : x ∈ frontier (S.proto N.ty).carrier := by
    rw [← (S.cx N.ty).carriers_cover]
    exact mem_iUnion₂.mpr ⟨F.val, (facetCell F).property, hx⟩
  let e := (S.cx N.ty).minimalCell x hxfront
  have he := (S.cx N.ty).minimalCell_mem x hxfront
  have heF := (S.cx N.ty).minimalCell_subset x hxfront F.val (facetCell F).property hx
  have heF' := (S.cx N.ty).minimalCell_subset x hxfront F'.val (facetCell F').property hx'
  obtain ⟨v, hv, hve⟩ :=
    packet_E_equality_step1_cell_vertex
      (S.proto N.ty) (S.cx N.ty) e he
  obtain ⟨q, hq⟩ := v.flat.connected.nonempty
  exact ⟨N.prototypeFrame m q, ⟨v, hv, q, hq, rfl⟩,
    ⟨q, heF (hve hq), rfl⟩, ⟨q, heF' (hve hq), rfl⟩⟩

/-- Step 2 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"interior points of two different children containing q" lie on disjoint
sides. The full affine scale transports the prescribed disjoint interiors. -/
private theorem packet_E_equality_step2_child_disjoint
    (N : FramedNode S) (n : ℕ) (i j : S.I N.ty) (hij : i ≠ j) :
    Disjoint (interior ((N.child n i).carrier n))
      (interior ((N.child n j).carrier n)) := by
  let H := ((S.σ ^ n).toAffineEquiv.trans N.frame.toAffineEquiv).toHomeomorphOfFiniteDimensional
  have hc (k : S.I N.ty) : (N.child n k).carrier n =
      H '' placedSet (S.child N.ty k).frame (S.proto (S.child N.ty k).ty).carrier := by
    simp only [FramedNode.carrier, SubstSystem.supertile, placedSet, Set.image_image]
    apply Set.image_congr
    intro x _
    exact congrArg N.frame (routing_constant_step4_ascent_ports_step1_child_scaled n k x)
  rw [hc i, hc j, ← H.image_interior, ← H.image_interior]
  exact Set.disjoint_image_of_injective H.injective (S.children_disjoint N.ty hij)

/-- Step 2 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"the interior link of P at q is connected (P is a polyhedral manifold
 domain)". A sufficiently small ball about a boundary point has connected
intersection with the domain's interior. This is a local assertion for one
polyhedral manifold domain; it involves no subdivision, states or packets. -/
private theorem packet_E_equality_step2_boundary_neighborhood
    (Q : PolyManifoldDomain d) (p : E d) (hp : p ∈ frontier Q.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      IsPreconnected (interior Q.carrier ∩ ball p r) := by
  sorry

/-- Step 2 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"the interior link of P at q is connected (P is a polyhedral manifold
domain)". Inside any prescribed open neighborhood of a point of the
closed domain there is a smaller open neighborhood with connected interior
trace. No convexity or smoothness of the boundary is assumed. -/
private theorem packet_E_equality_step2_local_link
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
        packet_E_equality_step2_boundary_neighborhood
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

/-- Step 2 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"a generic short path" avoids cells of codimension at least two.
Two segments through a generic intermediate point suffice in a convex open set. -/
private theorem packet_E_equality_step2_avoid_lower_cells
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

/-- Step 2 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"crosses a facet h of a child". A finite union of lower-dimensional
cells cannot separate interior from exterior in an open ball, so the closed
facets cover the boundary. Flat subdivided facets are included. -/
private theorem packet_E_equality_step2_facets_cover
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
    packet_E_equality_step2_avoid_lower_cells L
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

/-- Step 2 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"a facet h of a child". The facets of a proper boundary complex cover
the whole frontier, including its lower-dimensional cells. -/
private theorem packet_E_equality_step2_frontier_facets
    (N : FramedNode S) (n : ℕ) {x : E d} (hx : x ∈ frontier (N.carrier n)) :
    ∃ f : FacetName S N.ty, x ∈ N.cell n f.val := by
  let H := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  have hc : N.carrier n = H '' (S.proto N.ty).carrier := by
    simp [H, FramedNode.prototypeFrame, FramedNode.carrier,
      SubstSystem.supertile, placedSet, Set.image_image]
  rw [hc, ← H.image_frontier] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨e, hye⟩ := Set.mem_iUnion.mp
    (packet_E_equality_step2_facets_cover
      (S.proto N.ty) (S.cx N.ty) hy)
  exact ⟨e, y, hye, rfl⟩

/-- Step 2 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"smaller than the distance to cells not containing q". The complement
of the finite closed union of facets missing q is a suitable neighborhood. -/
private theorem packet_E_equality_step2_avoid_facets
    (N : FramedNode S) (n : ℕ) (p : E d) :
    ∃ U : Set (E d), IsOpen U ∧ p ∈ U ∧
      ∀ (f : FacetName S N.ty) (x : E d), x ∈ U → x ∈ N.cell n f.val →
        p ∈ N.cell n f.val := by
  classical
  let bad := (S.cx N.ty).facets.filter (fun e => p ∉ N.cell n e)
  let U := (⋃ e ∈ bad, N.cell n e)ᶜ
  have hc (e : Cell d) : IsClosed (N.cell n e) :=
    (e.flat.compact.image (N.prototypeFrame n).continuous_of_finiteDimensional).isClosed
  refine ⟨U, (isClosed_biUnion_finset (fun e _ => hc e)).isOpen_compl, ?_, ?_⟩
  · intro h
    obtain ⟨e, he, hpe⟩ := mem_iUnion₂.mp h
    exact (Finset.mem_filter.mp he).2 hpe
  · intro f x hx hxf
    by_contra hpf
    exact hx (mem_iUnion₂.mpr ⟨f.val, Finset.mem_filter.mpr ⟨f.property, hpf⟩, hxf⟩)

/-- Step 2 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"crosses a facet h of a child". A connected set meeting the interior
and the exterior of a closed child must meet its frontier. -/
private theorem packet_E_equality_step2_crossing
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

/-- Step 2 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"the interior link of P at q is connected" and the crossing facet contains
q when the neighborhood avoids all facets missing q. This uses the existing
local interior-neighborhood lemma for polyhedral manifold domains. -/
private theorem packet_E_equality_step2_internal_facet
    (N : FramedNode S) (n : ℕ) (p : E d) (i j : S.I N.ty) (hij : i ≠ j)
    (hpi : p ∈ (N.child n i).carrier n) (hpj : p ∈ (N.child n j).carrier n) :
    ∃ f : FacetName S (N.child n i).ty, p ∈ (N.child n i).cell n f.val ∧
      relint ((N.child n i).cell n f.val) ⊆ interior (N.carrier (n + 1)) := by
  have hisub := routing_constant_step4_ascent_ports_step6_child_subset N n i
  have hjsub := routing_constant_step4_ascent_ports_step6_child_subset N n j
  obtain ⟨U, hU, hpU, hfacets⟩ :=
    packet_E_equality_step2_avoid_facets
      (N.child n i) n p
  obtain ⟨V, hV, hpV, hVU, hconn⟩ :=
    packet_E_equality_step2_local_link
      N (n + 1) p (hisub hpi) U hU hpU
  have hireg := routing_constant_step4_inherited_record_step1_regular (N.child n i) n
  have hjreg := routing_constant_step4_inherited_record_step1_regular (N.child n j) n
  have hclosed : IsClosed ((N.child n i).carrier n) := hireg ▸ isClosed_closure
  obtain ⟨x, hxV, hxi⟩ := mem_closure_iff.mp (hireg.symm ▸ hpi) V hV hpV
  obtain ⟨y, hyV, hyj⟩ := mem_closure_iff.mp (hjreg.symm ▸ hpj) V hV hpV
  have hdisj : Disjoint ((N.child n i).carrier n) (interior ((N.child n j).carrier n)) := by
    rw [← hireg]
    exact (packet_E_equality_step2_child_disjoint N n i j hij).closure_left isOpen_interior
  have hyout : y ∉ (N.child n i).carrier n :=
    fun hyi => Set.disjoint_left.mp hdisj hyi hyj
  obtain ⟨z, ⟨hzN, hzV⟩, hzfront⟩ :=
    packet_E_equality_step2_crossing
      hclosed hconn ⟨x, ⟨interior_mono hisub hxi, hxV⟩, hxi⟩
      ⟨y, ⟨interior_mono hjsub hyj, hyV⟩, hyout⟩
  obtain ⟨f, hzf⟩ :=
    packet_E_equality_step2_frontier_facets
      (N.child n i) n hzfront
  refine ⟨f, hfacets f z (hVU hzV) hzf, ?_⟩
  rcases facet_dichotomy N (N.child n i) (n + 1) n (Parser.child_descendant N n i) f
    with ⟨F, hfF, _⟩ | hint
  · exact False.elim ((routing_constant_step4_inherited_record_step1_boundary N (n + 1) F
      (hfF hzf)).2 hzN)
  · exact hint

/-- Step 3 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"h is first-generation". Normalize the internal child facet and assign
its canonical primitive incidence, retaining the actual birth frame. -/
private theorem packet_E_equality_step3_birth
    (N : FramedNode S) (n : ℕ) (i : S.I N.ty) (f : FacetName S (N.child n i).ty)
    (hint : relint ((N.child n i).cell n f.val) ⊆ interior (N.carrier (n + 1))) :
    ∃ g : Parser.BornFacet P, g.height = n + 1 ∧ g.birth = N ∧
      g.carrier = (N.child n i).cell n f.val := by
  let H := ((S.σ ^ n).toAffineEquiv.trans N.frame.toAffineEquiv).toHomeomorphOfFiniteDimensional
  let K := placedSet (S.child N.ty i).frame f.val.carrier
  have hf : (N.child n i).cell n f.val = H '' K := by
    simp only [FramedNode.cell, Set.image_image, K, placedSet]
    apply Set.image_congr
    intro x _
    exact congrArg N.frame (routing_constant_step4_ascent_ports_step1_child_scaled n i x)
  have hN : N.carrier (n + 1) = H '' S.supertile 1 N.ty := by
    simp [H, FramedNode.carrier, SubstSystem.supertile, placedSet, Set.image_image,
      pow_succ, LinearEquiv.mul_apply]
  have hlocal : relint K ⊆ interior (S.supertile 1 N.ty) := by
    intro x hx
    have hm := hint (hf.symm ▸ (routing_constant_step4_ascent_ports_step3_relint_image
      ((S.σ ^ n).toAffineEquiv.trans N.frame.toAffineEquiv) K).symm ▸
        Set.mem_image_of_mem H hx)
    rw [hN, ← H.image_interior] at hm
    exact H.injective.mem_set_image.mp hm
  let f₀ : PrimitiveFacet S N.ty := ⟨0, (), K, ⟨i, f, rfl, hlocal⟩⟩
  obtain ⟨a, hat, hac⟩ := routing_constant_step1_incidence (P := P) f₀
  let g : Parser.BornFacet P := ⟨n + 1, by omega, N, a, hat⟩
  refine ⟨g, rfl, rfl, ?_⟩
  rw [routing_constant_step1_carrier]
  change N.prototypeFrame (n + 1) '' (S.σ.symm '' a.val.positioned) = _
  rw [hac]
  change N.prototypeFrame (n + 1) '' (S.σ.symm '' K) = _
  rw [hf]
  simp only [Set.image_image]
  apply Set.image_congr
  intro x _
  change N.frame ((S.σ ^ (n + 1)) (S.σ.symm x)) = N.frame ((S.σ ^ n) x)
  rw [pow_succ]
  simp

/-- Step 4 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"The tiles along h at q have END slots at q (cone T_q P)" and
"the head of P(h) is S(P)". An age-one child readout supplies the
actual END event; no joint honest realization of its labels is assumed. -/
private theorem packet_E_equality_step4_event
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (p : E d) (hp : N.Lists (n + 1) p)
    (g : Parser.BornFacet P) (hh : g.height = n + 1) (hb : g.birth = N)
    (hpg : p ∈ g.carrier) :
    ∃ t ∈ Y.tiles, ∃ (j : EndSlot (compilerLeaf C t)) (T : EndTemplate j),
      Compiler.endVertex (compilerFrame C t) j = p ∧
      j.header = routing_constant_step4_ascent_ports_step3_header
        N (n + 1) (compilerFrame C t) p ∧
      j.packet.head = newState Y hY n hn D hD N A ∧
      TemplateOccurs C Y (compilerFrame C t) T.configuration ∧ endRow T := by
  have hdesc : g.birth.IsDescendant g.height N (n + 1) := by
    rw [hh, hb]
    exact Parser.descendant_refl N (n + 1)
  have hL : g.leftNode ∈ D.geometry.nodes (g.height - 1) :=
    Parser.assembled_inner_mem D N A _ _ (by omega)
      (Parser.descendant_trans _ _ _ _ _ _ g.sides_descendant.1 hdesc)
  have hl := hD.boundaryPackets _ _ hL
  obtain ⟨q, hq, _, hhead⟩ := first_generation_head Y hY n hn D hD N A g hh hb hl
  have hpf : p ∈ g.leftNode.cell (g.height - 1) g.incidence.val.leftFacet.val := by
    rwa [g.sides_carrier.1]
  have hpcar := routing_constant_step4_ascent_ports_step2_cell_carrier
    g.leftNode (g.height - 1) g.incidence.val.leftFacet hpf
  have hpL : g.leftNode.Lists (g.height - 1) p := by
    obtain ⟨i, hi⟩ := routing_constant_step4_ascent_ports_step3_left_child g
    rw [hi] at hpcar ⊢
    apply vertex_inherited g.birth (g.height - 1) p _ i hpcar
    simpa only [hh, hb, Nat.add_sub_cancel] using hp
  obtain ⟨t, f, v, hpiece, hv, hvp⟩ :=
    routing_constant_step4_ascent_ports_step2_facet_at_vertex Y (g.height - 1)
      ⟨g.leftNode, D.geometry.node_actual _ _ hL⟩ g.incidence.val.leftFacet p hpL hpf
  obtain ⟨j, hjf, hjp, hjheader⟩ :=
    routing_constant_step3_same_parent_ports_step3_inherited_slot D hD N A g hdesc p
      hpL t f v hpiece hv hvp hl q hq
  have hjq : j.packet = q := by
    apply Option.some.inj
    calc
      some j.packet = leafPacket (compilerLeaf C t) f.val := by
        rw [← hjf]
        exact j.packet_eq.symm
      _ = some q := (attachedPacket_spec hl g.incidence.val.leftFacet t f hpiece).trans hq
  obtain ⟨T, hactual, hrow⟩ :=
    routing_constant_step4_ascent_ports_step4_event Y hY t hpiece.1 j
  refine ⟨t, hpiece.1, j, T, hjp, ?_, hjq ▸ hhead, hactual, hrow⟩
  rw [hh, hb] at hjheader
  exact hjheader

/-- Step 5 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"tiles inside P with pieces in F ... at q, belonging to theta_q by
Lemma 3.3". A boundary port of the actual event reads the constant
packet on its named parent facet, including a NULL packet. -/
private theorem packet_E_equality_step5_boundary_readout
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (m : ℕ) (N : FramedNode S) (hm : 1 ≤ m) (hN : IsBlock Y m N)
    (hconst : Parser.BoundaryPackets Y m N)
    (p : E d) (hp : N.Lists m p) (F : FacetName S N.ty) (hpF : p ∈ N.cell m F.val)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (j : EndSlot (compilerLeaf C t)) (T : EndTemplate j)
    (hjp : Compiler.endVertex (compilerFrame C t) j = p)
    (hjheader : j.header = routing_constant_step4_ascent_ports_step3_header
      N m (compilerFrame C t) p)
    (hactual : TemplateOccurs C Y (compilerFrame C t) T.configuration) (hrow : endRow T) :
    ∃ (a : BoundaryPort P T.geometry.header.birthType) (u : LeafType P),
      a ∈ T.geometry.boundaryPorts ∧ (a.tile, u) ∈ T.configuration.tiles ∧
      a.parentFacet.val = F.val ∧ leafPacket u a.facet.val = attachedPacket hconst F := by
  obtain ⟨u, f, v, hpiece, hv, hvp⟩ :=
    routing_constant_step4_ascent_ports_step2_facet_at_vertex Y m ⟨N, hN⟩ F p hp hpF
  obtain ⟨a, ha, hu, haF, haf⟩ :=
    routing_constant_step4_ascent_ports_step5_boundary_port Y hY m N hm hN F p t ht
      j hjp hjheader T hrow hactual u f v hpiece hv hvp
  refine ⟨a, compilerLeaf C u, ha, hu, haF, ?_⟩
  rw [haf]
  exact (attachedPacket_eq_leaf hconst F u f hpiece).symm

/-- Step 6 of the V4 proof of `packet_E_equality` (V4 3.12(b), 2.3):
"inherited facets on different parent facets use the parent's relation".
A coalescence witness for the parent tracks becomes a witness one level
higher for the two contained child tracks. -/
private theorem packet_E_equality_step6_tracks
    (U : HonestSource S) (q c : U.Node) (hparent : U.hierarchy.parentNode c = q)
    (F F' : FacetName S q.2.val.ty) (f f' : FacetName S c.2.val.ty)
    (hf : c.2.val.cell c.1 f.val ⊆ q.2.val.cell q.1 F.val)
    (hf' : c.2.val.cell c.1 f'.val ⊆ q.2.val.cell q.1 F'.val)
    (hE : U.TracksCoalesce q F F') : U.TracksCoalesce c f f' := by
  have hanc (a : ℕ) : U.hierarchy.ancestor c (a + 1) = U.hierarchy.ancestor q a := by
    simp only [CoherentHierarchy.ancestor, Function.iterate_succ_apply, hparent]
  obtain ⟨a, hboundary, G, hFG, hF'G⟩ := hE
  let G' : FacetName S (U.hierarchy.ancestor c (a + 1)).2.val.ty :=
    ⟨G.val, (congrArg (fun z : U.Node => z.2.val.ty) (hanc a).symm) ▸ G.property⟩
  have hcell := congrArg (fun z : U.Node => z.2.val.cell z.1 G.val) (hanc a)
  dsimp only at hcell
  refine ⟨a + 1, ?_, G', ?_, ?_⟩
  · intro j hj
    cases j with
    | zero =>
      exact ⟨routing_constant_step4_inherited_record_step1_boundary c.2.val c.1 f,
        routing_constant_step4_inherited_record_step1_boundary c.2.val c.1 f'⟩
    | succ j =>
      have hfront := congrArg (fun z : U.Node => frontier (z.2.val.carrier z.1)) (hanc j)
      dsimp only at hfront
      have hb := hboundary j (by omega)
      constructor
      · change c.2.val.cell c.1 f.val ⊆ _
        rw [hfront]
        exact hf.trans hb.1
      · change c.2.val.cell c.1 f'.val ⊆ _
        rw [hfront]
        exact hf'.trans hb.2
  · change c.2.val.cell c.1 f.val ⊆ (U.hierarchy.ancestor c (a + 1)).2.val.cell
      (U.hierarchy.ancestor c (a + 1)).1 G.val
    rw [hcell]
    exact hf.trans hFG
  · change c.2.val.cell c.1 f'.val ⊆ (U.hierarchy.ancestor c (a + 1)).2.val.cell
      (U.hierarchy.ancestor c (a + 1)).1 G.val
    rw [hcell]
    exact hf'.trans hF'G

/-- Step 6 of the V4 proof of `packet_E_equality` (V4 3.12(b), 3.11):
"By the (S5) rule, E_C(f,f') = E_P(F,F') = true". Realize the honest
parent state in its exact frame, then use deterministic child descent. -/
private theorem packet_E_equality_step6_child_E
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N) (i : S.I N.ty)
    (F F' : FacetName S N.ty) (f f' : FacetName S (N.child n i).ty)
    (hf : (N.child n i).cell n f.val ⊆ N.cell (n + 1) F.val)
    (hf' : (N.child n i).cell n f'.val ⊆ N.cell (n + 1) F'.val)
    (hE : stateEAt (newState Y hY n hn D hD N A) F.val F'.val) :
    stateEAt (childMap P (newState Y hY n hn D hD N A) ⟨N.ty, i⟩) f.val f'.val := by
  obtain ⟨U, hU, hs⟩ := routing_constant_step2_source_realization
    (newState Y hY n hn D hD N A) (newState_honest Y hY n hn D hD N A) N (n + 1)
    (newState_type Y hY n hn D hD N A) (newState_residue Y hY n hn D hD N A)
  let q : U.Node := ⟨n + 1, ⟨N, hU⟩⟩
  change stateOf U P q = newState Y hY n hn D hD N A at hs
  have hq : 1 ≤ q.1 := by change 1 ≤ n + 1; omega
  let c := U.childNode q hq i
  have hparent : U.hierarchy.parentNode c = q := by
    apply Sigma.ext
    · simp [c, q, HonestSource.childNode, CoherentHierarchy.parentNode]
    · apply heq_of_eq
      apply Subtype.ext
      exact (U.hierarchy.parent_unique n _ N hU ⟨i, rfl⟩).symm
  have htracks : U.TracksCoalesce q F F' := by
    rw [← hs] at hE
    obtain ⟨_, _, hE⟩ := hE
    exact (U.mem_coalescenceTable q F F').mp hE
  have hchild := packet_E_equality_step6_tracks U q c hparent F F' f f' hf hf' htracks
  have hEc : stateEAt (stateOf U P c) f.val f'.val :=
    ⟨f.property, f'.property, (U.mem_coalescenceTable c f f').mpr hchild⟩
  simpa only [c, childMap_spec U P q hq i, hs] using hEc

/-- Step 7 of the V4 proof of `packet_E_equality` (V4 3.12(b)):
"By (I5) for C ... and by (a) these are P_P(F), P_P(F')".
Meeting inherited facets of one old child transfer its packet equality
to the parent. The child need not be the only child at the meeting point. -/
private theorem packet_E_equality_step7_inherited_packets
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N) (i : S.I N.ty)
    (F F' : FacetName S N.ty) (f f' : FacetName S (N.child n i).ty)
    (hf : (N.child n i).cell n f.val ⊆ N.cell (n + 1) F.val)
    (hf' : (N.child n i).cell n f'.val ⊆ N.cell (n + 1) F'.val)
    (hmeet : ((N.child n i).cell n f.val ∩ (N.child n i).cell n f'.val).Nonempty)
    (hE : stateEAt (newState Y hY n hn D hD N A) F.val F'.val)
    (hconst : Parser.BoundaryPackets Y (n + 1) N) :
    attachedPacket hconst F = attachedPacket hconst F' := by
  have hB : N.child n i ∈ D.geometry.nodes n := by
    rw [← A.child_eq i]
    exact D.geometry.root_mem (A.children i).val (A.children i).property
  have hstate : D.stateAt n (N.child n i) hB =
      childMap P (newState Y hY n hn D hD N A) ⟨N.ty, i⟩ := by
    simpa only [DecodedLevel.blockState, A.child_eq] using child_equations Y hY n hn D hD N A i
  obtain ⟨hc, hEc⟩ := hD.I5 n (N.child n i) hB
  have hEchild : stateEAt (D.stateAt n (N.child n i) hB) f.val f'.val := by
    rw [hstate]
    exact packet_E_equality_step6_child_E Y hY n hn D hD N A i F F' f f' hf hf' hE
  have heq := hEc f f' hEchild hmeet
  have hF := Parser.boundaryPacket_inherited Y (n + 1) n N (N.child n i)
    (D.geometry.node_actual _ _ hB) (Parser.child_descendant N n i) F f hf hconst hc
  have hF' := Parser.boundaryPacket_inherited Y (n + 1) n N (N.child n i)
    (D.geometry.node_actual _ _ hB) (Parser.child_descendant N n i) F' f' hf' hconst hc
  exact hF.trans (heq.trans hF'.symm)

end PacketEEquality

/-- R11, V4 3.12(b): meeting facets related by E in the newly decoded parent
state have equal attached packets. Attachment uses R11(a), and its value is
independent of which proof of constancy was supplied. -/
theorem packet_E_equality (F F' : FacetName S N.ty)
    (hE : stateEAt (newState Y hY n hn D hD N A) F.val F'.val)
    (hmeet : (N.cell (n + 1) F.val ∩ N.cell (n + 1) F'.val).Nonempty)
    (hconst : Parser.BoundaryPackets Y (n + 1) N) :
    attachedPacket hconst F = attachedPacket hconst F' := by
  classical
  obtain ⟨p, hp, hpF, hpF'⟩ := packet_E_equality_step1_common_vertex N (n + 1) F F' hmeet
  obtain ⟨a, hpa⟩ := mem_iUnion.mp ((boundary_facet_adjacency N n F).1.symm ▸ hpF)
  obtain ⟨b, hpb⟩ := mem_iUnion.mp ((boundary_facet_adjacency N n F').1.symm ▸ hpF')
  rcases a with ⟨⟨i, f⟩, hf⟩
  rcases b with ⟨⟨i', f'⟩, hf'⟩
  dsimp only at hpa hpb hf hf'
  by_cases hii' : i = i'
  · subst i'
    exact packet_E_equality_step7_inherited_packets Y hY n hn D hD N A i F F' f f'
      hf hf' ⟨p, hpa, hpb⟩ hE hconst
  · obtain ⟨h, hph, hint⟩ := packet_E_equality_step2_internal_facet N n p i i' hii'
      (routing_constant_step4_ascent_ports_step2_cell_carrier _ _ f hpa)
      (routing_constant_step4_ascent_ports_step2_cell_carrier _ _ f' hpb)
    obtain ⟨g, hh, hb, hg⟩ := packet_E_equality_step3_birth (P := P) N n i h hint
    obtain ⟨t, ht, j, T, hjp, hjheader, hhead, hactual, hrow⟩ :=
      packet_E_equality_step4_event Y hY n hn D hD N A p hp g hh hb (hg.symm ▸ hph)
    obtain ⟨a, u, ha, hu, haF, hread⟩ := packet_E_equality_step5_boundary_readout
      Y hY (n + 1) N (by omega) A.actual hconst p hp F hpF t ht j T hjp hjheader hactual hrow
    obtain ⟨b, v, hb, hv, hbF, hread'⟩ := packet_E_equality_step5_boundary_readout
      Y hY (n + 1) N (by omega) A.actual hconst p hp F' hpF' t ht j T hjp hjheader hactual hrow
    have hE' : stateEAt j.packet.head a.parentFacet.val b.parentFacet.val := by
      rw [hhead, haF, hbF]
      exact hE
    exact hread.symm.trans ((hrow.2.2.2.2.1 a ha b hb hE' u v hu hv).trans hread')

/-- R9, V4 3.10: every readable child yields the same parent slot value,
including every choice of facet in its first branching descendant. -/
theorem readable_parent_state (i : S.I N.ty) (r : Parser.ReadableFacet D N A i) :
    r.parentState = newState Y hY n hn D hD N A := by
  sorry

end Forward

namespace Parser

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ}

/-- R12, V4 3.1, induction step: exact nesting of consecutive decoded levels.
Every new root has exactly its prescribed old children; every old root has
one such parent, and all states already assigned below agree literally. -/
structure NestedLevels (D : DecodedLevel Y n) (D' : DecodedLevel Y (n + 1)) : Prop where
  /-- R12, V4 3.1, 3.7: all new roots are unions of their actual prescribed old children. -/
  children : ∀ B' ∈ D'.geometry.blocks, ∀ i : S.I B'.node.ty,
    ∃ B ∈ D.geometry.blocks, B.node = B'.node.child n i
  /-- R12, V4 3.1, 3.7: every old root has exactly one new root as a parent. -/
  parents : ∀ B ∈ D.geometry.blocks, ∃! B' : {B' // B' ∈ D'.geometry.blocks},
    ∃ i : S.I B'.val.node.ty, B.node = B'.val.node.child n i
  /-- R12, V4 3.1: all inner old nodes remain nodes inside the new blocks. -/
  nodes : ∀ m : ℕ, D.geometry.nodes m ⊆ D'.geometry.nodes m
  /-- R12, V4 3.1: all retained states agree, including native leaves and inner nodes. -/
  states : ∀ (m : ℕ) (M : FramedNode S) (hM : M ∈ D.geometry.nodes m)
    (hM' : M ∈ D'.geometry.nodes m), D.stateAt m M hM = D'.stateAt m M hM'

end Parser

/-- R12, V4 3.1 (forward induction step), 3.7--3.12: the proposed geometry
with states defined by 3.9 extends the old decoded level and satisfies all four
invariants. This packages the forward step without imposing its conclusions
as hypotheses on an assembled parent. -/
theorem forward_level (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D) :
    ∃ D' : DecodedLevel Y (n + 1), Inv D' ∧ Parser.NestedLevels D D' ∧
      D'.geometry.roots = Parser.proposedParents D ∧
      ∀ (B' : Block Y (n + 1)) (hB' : B' ∈ D'.geometry.blocks),
        ∃ A : Parser.AssembledParent D B'.node,
          D'.blockState B' hB' = newState Y hY n hn D hD B'.node A := by
  sorry

namespace DecodedLevel

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)

/-- R12, V4 3.1: read the assigned state of a framed root without choosing
a representative block; the geometric top-node equality supplies membership. -/
def rootState (N : FramedNode S) (hN : N ∈ D.geometry.roots) : State P :=
  D.stateAt n N (by rw [D.geometry.nodes_top]; exact hN)

/-- R12, V4 3.1: root-state readout is the original block-state readout. -/
theorem rootState_block (B : Block Y n) (hB : B ∈ D.geometry.blocks) :
    D.rootState B.node ⟨B, hB, rfl⟩ = D.blockState B hB := rfl

end DecodedLevel

namespace Parser

variable (Y : MarkedTiling (systemM S P C))

/-- R12, V4 3.1: realization of one nested sequence as a coherent hierarchy.
The full decoded levels also expose low-height states; their roots are exactly
the hierarchy nodes, and every inner state agrees with the corresponding root
state. Below K the hierarchy is explicitly the certificate subdivision. -/
structure HierarchyRealizes (levels : ∀ n : ℕ, P.K ≤ n → DecodedLevel Y n)
    (H : CoherentHierarchy S (Y.project (nativeDecoration S P C))) where
  /-- R12, V4 3.1: every level in the induction sequence has Inv(n). -/
  invariant : ∀ n hn, Inv (levels n hn)
  /-- R12, V4 3.1: the one-step nesting retains all previously assigned states. -/
  nested : ∀ n hn, NestedLevels (levels n hn)
    (levels (n + 1) (Nat.le_trans hn (Nat.le_succ n)))
  /-- R12, V4 3.1, 3.2: the initial level is the actual forced certificate base. -/
  base : CertificateBase (levels P.K le_rfl)
  /-- R12, V4 3.1: decoded families at every height, including heights less than K. -/
  fullLevels : ∀ n : ℕ, DecodedLevel Y n
  /-- R12, V4 3.1: the four invariant clauses hold at every height. -/
  full_invariant : ∀ n : ℕ, Inv (fullLevels n)
  /-- R12, V4 3.1: the high full levels are the very same induction sequence. -/
  upper_eq : ∀ n hn, fullLevels n = levels n hn
  /-- R12, V4 3.1: roots, including their frames, are exactly the hierarchy nodes. -/
  roots : ∀ n, (fullLevels n).geometry.roots = H.nodes n
  /-- R12, V4 3.1: every lower full level is exactly the inner subdivision of a higher one. -/
  inner_nodes : ∀ n m : ℕ, m ≤ n → (fullLevels n).geometry.nodes m = H.nodes m
  /-- R12, V4 3.1: low levels are the nodes inside the actual K-certificate blocks. -/
  below_K : ∀ n : ℕ, n < P.K → H.nodes n = (levels P.K le_rfl).geometry.nodes n
  /-- R12, V4 3.1: state assignments agree at every shared inner node. -/
  states : ∀ (n m : ℕ) (N : FramedNode S)
    (hn : N ∈ (fullLevels n).geometry.nodes m)
    (hm : N ∈ (fullLevels m).geometry.nodes m),
      (fullLevels n).stateAt m N hn = (fullLevels m).stateAt m N hm
  /-- R12, V4 3.1, §3.2: parents at and above K are exactly the proposed parents. -/
  parents : ∀ (n : ℕ) (hn : P.K ≤ n) (B : Block Y n)
    (hB : B ∈ (levels n hn).geometry.blocks) (hN : B.node ∈ H.nodes n),
      (H.parent n ⟨B.node, hN⟩).val = proposedParent (levels n hn) B hB
  /-- R12, V4 3.1 (I2): each root's first address letter is its actual hierarchy role. -/
  roles : ∀ q : H.Node,
    ((fullLevels q.1).rootState q.2.val (by rw [roots]; exact q.2.property)).address
      ⟨0, P.k_pos⟩ = H.nodeRole q

namespace HierarchyRealizes

variable {Y} {levels : ∀ n : ℕ, P.K ≤ n → DecodedLevel Y n}
variable {H : CoherentHierarchy S (Y.project (nativeDecoration S P C))}
variable (R : HierarchyRealizes Y levels H)

/-- R12, V4 3.1: the single state assigned to each actual hierarchy node,
read from its full decoded level and using the exact root correspondence. -/
def state (q : H.Node) : State P :=
  (R.fullLevels q.1).rootState q.2.val (by rw [R.roots]; exact q.2.property)

/-- R12, V4 3.1: every assigned hierarchy state is honest. -/
theorem state_honest (q : H.Node) : R.state q ∈ honestStates S P :=
  (R.fullLevels q.1).state_honest q.1 _

/-- R12, V4 3.1: every assigned hierarchy state has the node type and height residue. -/
theorem state_type_residue (q : H.Node) :
    (R.state q).ty = q.2.val.ty ∧ (R.state q).residue.val = q.1 % P.L := by
  sorry

/-- R12, V4 3.1: the hierarchy state is the existing inner state in every
decoded level containing that framed node, not an independent marginal choice. -/
theorem state_agrees (n m : ℕ) (N : FramedNode S)
    (hN : N ∈ (R.fullLevels n).geometry.nodes m) (hm : N ∈ H.nodes m) :
    (R.fullLevels n).stateAt m N hN = R.state ⟨m, ⟨N, hm⟩⟩ := by
  have hm_root : N ∈ (R.fullLevels m).geometry.roots := by
    rwa [R.roots m]
  have hm_node : N ∈ (R.fullLevels m).geometry.nodes m := by
    rwa [(R.fullLevels m).geometry.nodes_top]
  change (R.fullLevels n).stateAt m N hN = (R.fullLevels m).stateAt m N hm_node
  exact R.states n m N hN hm_node

/-- R12, V4 3.1: the global state assignment obeys every actual child equation. -/
theorem state_child (q : H.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (hc : q.2.val.child (q.1 - 1) i ∈ H.nodes (q.1 - 1)) :
    R.state ⟨q.1 - 1, ⟨q.2.val.child (q.1 - 1) i, hc⟩⟩ =
      childMap P (R.state q) ⟨q.2.val.ty, i⟩ := by
  sorry

/-- R12, V4 3.1: ground hierarchy states are the actual output leaf states. -/
theorem state_ground (q : H.Node) (hq : q.1 = 0)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (heq : tileNode t = q.2.val) : R.state q = (compilerLeaf C t).prePattern.state := by
  obtain ⟨_ | n, N⟩ := q
  · have hm_node : N.val ∈ (R.fullLevels 0).geometry.nodes 0 := by
      rw [(R.fullLevels 0).geometry.nodes_top, R.roots 0]
      exact N.property
    change (R.fullLevels 0).stateAt 0 N.val hm_node = (compilerLeaf C t).prePattern.state
    exact (R.full_invariant 0).I2.2 N.val hm_node t ht heq
  · contradiction

/-- R12, V4 3.1: the assigned state's first role is the actual parent role. -/
theorem state_role (q : H.Node) : (R.state q).address ⟨0, P.k_pos⟩ = H.nodeRole q :=
  R.roles q

/-- R12, V4 3.1 (I5): every hierarchy node, at every height, has constant
side packets and E-equality on meeting boundary facets. -/
theorem boundary_invariant (q : H.Node) :
    ∃ h : BoundaryPackets Y q.1 q.2.val, ∀ F F' : FacetName S q.2.val.ty,
      stateEAt (R.state q) F.val F'.val →
      (q.2.val.cell q.1 F.val ∩ q.2.val.cell q.1 F'.val).Nonempty →
        attachedPacket h F = attachedPacket h F' := by
  have h_root : q.2.val ∈ (R.fullLevels q.1).geometry.roots := by
    rw [R.roots q.1]
    exact q.2.property
  have h_node : q.2.val ∈ (R.fullLevels q.1).geometry.nodes q.1 := by
    rw [(R.fullLevels q.1).geometry.nodes_top]
    exact h_root
  have h_I5 := (R.full_invariant q.1).I5 q.1 q.2.val h_node
  exact h_I5

/-- R12, V4 3.1 (I4): the global assignment satisfies the principal PRESENT-slot
invariant at every height, including all certificate-subdivision nodes below K. -/
theorem principal_invariant (q : H.Node) (g : BornFacet P)
    (hbirth : g.birth.IsDescendant g.height q.2.val q.1)
    (hdepth : q.1 - g.height < P.k) (hprincipal : P.InPrincipal q.2.val q.1 g.carrier) :
    ∃ hleft : BoundaryPackets Y (g.height - 1) g.leftNode, ∃ p : Packet P,
      g.packet hleft = some p ∧
        decode p ⟨q.1 - g.height, hdepth⟩ = some (R.state q) := by
  have hI4 := (R.full_invariant q.1).I4
  have hN : q.2.val ∈ (R.fullLevels q.1).geometry.nodes q.1 := by
    rw [(R.fullLevels q.1).geometry.nodes_top, R.roots q.1]
    exact q.2.property
  exact hI4 q.1 q.2.val hN g hbirth hdepth hprincipal

end HierarchyRealizes

end Parser

/-- Step 1 of the V4 proof of `all_height_hierarchy` (V4 3.1): "Induction on
n ≥ K: Lemma 3.2 gives the base. Given a decoded level n with Inv(n),
Proposition 3.7 gives the level n+1 ...". The recursively chosen sequence of
decoded levels with Inv, starting from the base level of Lemma 3.2 and
continuing by the forward step. Heights below K never occur in a use. -/
private def all_height_hierarchy_step1_aux (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) : (n : ℕ) → P.K ≤ n → {D : DecodedLevel Y n // Inv D}
  | 0, h => cast (congrArg (fun k => {D : DecodedLevel Y k // Inv D})
      (Nat.le_zero.mp h)) ⟨baseLevel Y hY, baseLevel_invariant Y hY⟩
  | m + 1, h =>
      if hm : P.K ≤ m then
        ⟨Classical.choose (forward_level Y hY m hm
            (all_height_hierarchy_step1_aux Y hY m hm).1
            (all_height_hierarchy_step1_aux Y hY m hm).2),
          (Classical.choose_spec (forward_level Y hY m hm
            (all_height_hierarchy_step1_aux Y hY m hm).1
            (all_height_hierarchy_step1_aux Y hY m hm).2)).1⟩
      else cast (congrArg (fun k => {D : DecodedLevel Y k // Inv D})
        (by omega : P.K = m + 1)) ⟨baseLevel Y hY, baseLevel_invariant Y hY⟩

/-- Step 1 of the V4 proof of `all_height_hierarchy` (V4 3.1, Lemma 3.2):
"Lemma 3.2 gives the base": the sequence starts at the certificate base. -/
private theorem all_height_hierarchy_step1_aux_base (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) : ∀ (n : ℕ) (h : P.K ≤ n) (e : P.K = n),
      all_height_hierarchy_step1_aux Y hY n h =
        cast (congrArg (fun k => {D : DecodedLevel Y k // Inv D}) e)
          ⟨baseLevel Y hY, baseLevel_invariant Y hY⟩ := by
  intro n
  cases n with
  | zero => intro h e; rfl
  | succ m =>
      intro h e
      have hm : ¬ P.K ≤ m := by omega
      simp only [all_height_hierarchy_step1_aux, dif_neg hm]

/-- Step 1 of the V4 proof of `all_height_hierarchy` (V4 3.1): "Given a decoded
level n with Inv(n), Proposition 3.7 gives the level n+1": the successor term
of the sequence is the forward level of the previous term. -/
private theorem all_height_hierarchy_step1_aux_succ (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (n : ℕ) (hn : P.K ≤ n) (h : P.K ≤ n + 1) :
    all_height_hierarchy_step1_aux Y hY (n + 1) h =
      ⟨Classical.choose (forward_level Y hY n hn
          (all_height_hierarchy_step1_aux Y hY n hn).1
          (all_height_hierarchy_step1_aux Y hY n hn).2),
        (Classical.choose_spec (forward_level Y hY n hn
          (all_height_hierarchy_step1_aux Y hY n hn).1
          (all_height_hierarchy_step1_aux Y hY n hn).2)).1⟩ := by
  simp only [all_height_hierarchy_step1_aux, dif_pos hn]

/-- Step 1 of the V4 proof of `all_height_hierarchy` (V4 3.1): "Induction on
n ≥ K: Lemma 3.2 gives the base. Given a decoded level n with Inv(n),
Proposition 3.7 gives the level n+1 geometrically; ... The levels are nested by
construction (each (n+1)-block is the union of its children)". One nested
sequence with Inv at every height n ≥ K, the certificate base at K, and roots
of each next level equal to the proposed parents. -/
private theorem all_height_hierarchy_step1_sequence (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) :
    ∃ levels : ∀ n : ℕ, P.K ≤ n → DecodedLevel Y n,
      (∀ n hn, Inv (levels n hn)) ∧
      (∀ n hn, Parser.NestedLevels (levels n hn)
        (levels (n + 1) (Nat.le_trans hn (Nat.le_succ n)))) ∧
      Parser.CertificateBase (levels P.K le_rfl) ∧
      (∀ n hn, (levels (n + 1) (Nat.le_trans hn (Nat.le_succ n))).geometry.roots =
        Parser.proposedParents (levels n hn)) := by
  refine ⟨fun n hn => (all_height_hierarchy_step1_aux Y hY n hn).1,
    fun n hn => (all_height_hierarchy_step1_aux Y hY n hn).2, ?_, ?_, ?_⟩
  · intro n hn
    show Parser.NestedLevels (all_height_hierarchy_step1_aux Y hY n hn).1
      (all_height_hierarchy_step1_aux Y hY (n + 1) _).1
    rw [all_height_hierarchy_step1_aux_succ Y hY n hn]
    exact (Classical.choose_spec (forward_level Y hY n hn _ _)).2.1
  · show Parser.CertificateBase (all_height_hierarchy_step1_aux Y hY P.K le_rfl).1
    rw [all_height_hierarchy_step1_aux_base Y hY P.K le_rfl rfl]
    exact baseLevel_certificates Y hY
  · intro n hn
    show (all_height_hierarchy_step1_aux Y hY (n + 1) _).1.geometry.roots = _
    rw [all_height_hierarchy_step1_aux_succ Y hY n hn]
    exact (Classical.choose_spec (forward_level Y hY n hn _ _)).2.2.1

/-- Step 1 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 3.1):
"The levels are nested by construction (each (n+1)-block is the union of its
children)". Below the new root height, the inner nodes of the next level are
exactly those of the previous one: a strict descendant of a new root passes
through one of its prescribed children, which is an old chosen block. -/
private theorem all_height_hierarchy_step2_hierarchy_step1_nodes_succ
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)
    (D' : DecodedLevel Y (n + 1)) (h : Parser.NestedLevels D D') (m : ℕ) (hm : m ≤ n) :
    D'.geometry.nodes m = D.geometry.nodes m := by
  apply Set.Subset.antisymm _ (h.nodes m)
  rintro N ⟨B', hB', hdesc⟩
  obtain ⟨i, hi⟩ := packet_constancy_step1_through_child B'.node N n m hdesc (by omega)
  obtain ⟨B, hB, hBeq⟩ := h.children B' hB' i
  refine ⟨B, hB, ?_⟩
  show N.IsDescendant m B.node n
  rw [hBeq]
  exact hi

/-- Step 1 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 3.1):
"The levels are nested by construction". Iterating the one-step nesting, the
height-m inner nodes do not change along the sequence from level n on. -/
private theorem all_height_hierarchy_step2_hierarchy_step1_nodes_stable
    {Y : MarkedTiling (systemM S P C)} (levels : ∀ n : ℕ, P.K ≤ n → DecodedLevel Y n)
    (hnest : ∀ n hn, Parser.NestedLevels (levels n hn)
      (levels (n + 1) (Nat.le_trans hn (Nat.le_succ n))))
    (n : ℕ) (hn : P.K ≤ n) (k m : ℕ) (hm : m ≤ n) :
    (levels (n + k) (Nat.le_trans hn (Nat.le_add_right n k))).geometry.nodes m =
      (levels n hn).geometry.nodes m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (all_height_hierarchy_step2_hierarchy_step1_nodes_succ _ _
      (hnest (n + k) (Nat.le_trans hn (Nat.le_add_right n k))) m (by omega)).trans ih

/-- Step 1 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 3.1):
"they define a coherent hierarchy": any two levels n, n' ≥ K with m ≤ n, n'
have the same height-m inner nodes. -/
private theorem all_height_hierarchy_step2_hierarchy_step1_nodes_eq
    {Y : MarkedTiling (systemM S P C)} (levels : ∀ n : ℕ, P.K ≤ n → DecodedLevel Y n)
    (hnest : ∀ n hn, Parser.NestedLevels (levels n hn)
      (levels (n + 1) (Nat.le_trans hn (Nat.le_succ n))))
    (n n' : ℕ) (hn : P.K ≤ n) (hn' : P.K ≤ n') (m : ℕ) (hm : m ≤ n) (hm' : m ≤ n') :
    (levels n' hn').geometry.nodes m = (levels n hn).geometry.nodes m := by
  rcases le_total n n' with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact all_height_hierarchy_step2_hierarchy_step1_nodes_stable levels hnest n hn k m hm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (all_height_hierarchy_step2_hierarchy_step1_nodes_stable levels hnest n' hn' k m
      hm').symm

/-- Step 2 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 §1.0, 3.1):
"with nodes of height < K given by the certificate subdivisions". A descendant
of depth r+1 is a prescribed child of the descendant of depth r one height up
(peeling off the last letter of its role word). -/
private theorem all_height_hierarchy_step2_hierarchy_step2_last_letter
    (N : FramedNode S) (m r : ℕ) (w : S.RoleWord N.ty (r + 1)) :
    ∃ (w' : S.RoleWord N.ty r)
      (i : S.I ((S.descendantNode N.ty (m + 1) r w').move N.frame).ty),
      (S.descendantNode N.ty m (r + 1) w).move N.frame =
        ((S.descendantNode N.ty (m + 1) r w').move N.frame).child m i := by
  induction r generalizing N with
  | zero =>
    obtain ⟨i, u⟩ := w
    refine ⟨(), i, ?_⟩
    apply FramedNode.ext
    · rfl
    · show ((AffineIsometryEquiv.refl ℝ (E d)).trans (S.placeChild m i)).trans N.frame =
        (S.placeChild m i).trans ((AffineIsometryEquiv.refl ℝ (E d)).trans N.frame)
      rw [AffineIsometryEquiv.refl_trans, AffineIsometryEquiv.refl_trans]
  | succ r ih =>
    obtain ⟨i, a⟩ := w
    obtain ⟨a', j, h⟩ := ih (N.child (m + (r + 1)) i) a
    refine ⟨⟨i, a'⟩, j, ?_⟩
    have hp : S.placeChild (m + (r + 1)) i = S.placeChild (m + 1 + r) i := by
      rw [show m + (r + 1) = m + 1 + r by omega]
    refine h.trans ?_
    apply FramedNode.ext
    · rfl
    · show (S.placeChild m j).trans ((S.descendantNode (S.child N.ty i).ty (m + 1) r a').frame.trans
          ((S.placeChild (m + (r + 1)) i).trans N.frame)) =
        (S.placeChild m j).trans ((S.descendantNode (S.child N.ty i).ty (m + 1) r a').frame.trans
          ((S.placeChild (m + 1 + r) i).trans N.frame))
      rw [hp]

/-- Step 2 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 §1.0, 3.1):
"each (n+1)-block is the union of its children". The height-m descendants of a
node of height m+r cover it. -/
private theorem all_height_hierarchy_step2_hierarchy_step2_cover_desc
    (N : FramedNode S) (m r : ℕ) (x : E d) (hx : x ∈ N.carrier (m + r)) :
    ∃ w : S.RoleWord N.ty r, x ∈ ((S.descendantNode N.ty m r w).move N.frame).carrier m := by
  induction r generalizing N with
  | zero =>
    refine ⟨(), ?_⟩
    simpa [SubstSystem.descendantNode, FramedNode.move] using hx
  | succ r ih =>
    have hx' : x ∈ N.carrier (m + r + 1) := hx
    rw [assembly_step1_children_cover N (m + r)] at hx'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
    obtain ⟨w, hw⟩ := ih (N.child (m + r) i) hi
    exact ⟨⟨i, w⟩, hw⟩

/-- Step 2 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 §1.0 (H3), 3.1):
distinct children have disjoint interiors, hence distinct height-m descendants
of one node have disjoint interiors. -/
private theorem all_height_hierarchy_step2_hierarchy_step2_disjoint_desc
    (N : FramedNode S) (m r : ℕ) (w w' : S.RoleWord N.ty r)
    (hne : (S.descendantNode N.ty m r w).move N.frame ≠
      (S.descendantNode N.ty m r w').move N.frame) :
    Disjoint (interior (((S.descendantNode N.ty m r w).move N.frame).carrier m))
      (interior (((S.descendantNode N.ty m r w').move N.frame).carrier m)) := by
  induction r generalizing N with
  | zero =>
    cases w
    cases w'
    exact (hne rfl).elim
  | succ r ih =>
    obtain ⟨i, a⟩ := w
    obtain ⟨j, b⟩ := w'
    by_cases hij : i = j
    · subst hij
      exact ih (N.child (m + r) i) a b hne
    · have hsi := routing_constant_step4_ascent_ports_step6_descendant_subset
        ((S.descendantNode (N.child (m + r) i).ty m r a).move (N.child (m + r) i).frame)
        (N.child (m + r) i) m (m + r) ⟨r, rfl, a, rfl⟩
      have hsj := routing_constant_step4_ascent_ports_step6_descendant_subset
        ((S.descendantNode (N.child (m + r) j).ty m r b).move (N.child (m + r) j).frame)
        (N.child (m + r) j) m (m + r) ⟨r, rfl, b, rfl⟩
      exact Disjoint.mono (interior_mono hsi) (interior_mono hsj)
        (assembly_step1_children_disjoint N (m + r) i j hij)

/-- Step 2 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 3.1):
"they define a coherent hierarchy": the height-m inner nodes of a geometric
level cover space. -/
private theorem all_height_hierarchy_step2_hierarchy_step2_level_cover
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (G : GeometricLevel Y n) (m : ℕ)
    (hm : m ≤ n) (x : E d) : ∃ N ∈ G.nodes m, x ∈ N.carrier m := by
  obtain ⟨B, hB, hxB⟩ := G.cover x
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hm
  have hx : x ∈ B.node.carrier (m + r) := hr ▸ hxB
  obtain ⟨w, hw⟩ := all_height_hierarchy_step2_hierarchy_step2_cover_desc B.node m r x hx
  exact ⟨_, ⟨B, hB, r, hr, w, rfl⟩, hw⟩

/-- Step 2 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 3.1):
"they define a coherent hierarchy": distinct height-m inner nodes of a
geometric level have disjoint interiors (distinct blocks have disjoint
interiors, distinct descendants of one block too). -/
private theorem all_height_hierarchy_step2_hierarchy_step2_level_disjoint
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (G : GeometricLevel Y n) (m : ℕ) :
    (G.nodes m).PairwiseDisjoint (fun N => interior (N.carrier m)) := by
  rintro N ⟨B, hB, r, hr, w, rfl⟩ N' ⟨B', hB', r', hr', w', rfl⟩ hne
  by_cases hBB : B = B'
  · subst hBB
    have hrr : r = r' := by omega
    subst hrr
    exact all_height_hierarchy_step2_hierarchy_step2_disjoint_desc B.node m r w w' hne
  · have h1 := routing_constant_step4_ascent_ports_step6_descendant_subset _ B.node m n
      ⟨r, hr, w, rfl⟩
    have h2 := routing_constant_step4_ascent_ports_step6_descendant_subset _ B'.node m n
      ⟨r', hr', w', rfl⟩
    exact Disjoint.mono (interior_mono h1) (interior_mono h2) (G.disjoint hB hB' hBB)

/-- Step 2 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 3.1):
"they define a coherent hierarchy": every inner node below the root height is
a prescribed child of an inner node one height up. -/
private theorem all_height_hierarchy_step2_hierarchy_step2_level_parent_exists
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (G : GeometricLevel Y n) (m : ℕ)
    (N : FramedNode S) (hN : N ∈ G.nodes m) (hm : m < n) :
    ∃ Q ∈ G.nodes (m + 1), ∃ i : S.I Q.ty, N = Q.child m i := by
  obtain ⟨B, hB, r, hr, w, rfl⟩ := hN
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨w', i, h⟩ := all_height_hierarchy_step2_hierarchy_step2_last_letter B.node m r w
  exact ⟨_, ⟨B, hB, r, by omega, w', rfl⟩, i, h⟩

/-- Step 2 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 §1.0, 3.1):
"a node belongs to only one parent": two inner nodes of one height sharing a
prescribed child coincide, since the child has nonempty interior inside both. -/
private theorem all_height_hierarchy_step2_hierarchy_step2_level_parent_unique
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (G : GeometricLevel Y n) (m : ℕ)
    (Q Q' : FramedNode S) (hQ : Q ∈ G.nodes (m + 1)) (hQ' : Q' ∈ G.nodes (m + 1))
    (i : S.I Q.ty) (i' : S.I Q'.ty) (h : Q.child m i = Q'.child m i') : Q = Q' := by
  by_contra hne
  have hd : Disjoint (interior (Q.carrier (m + 1))) (interior (Q'.carrier (m + 1))) :=
    all_height_hierarchy_step2_hierarchy_step2_level_disjoint G (m + 1) hQ hQ' hne
  obtain ⟨x, hx⟩ := (assembly_step1_node_regular (Q.child m i) m).2.2.nonempty
  have hx' : x ∈ interior ((Q'.child m i').carrier m) := by rw [← h]; exact hx
  exact Set.disjoint_left.mp hd
    (interior_mono (routing_constant_step4_ascent_ports_step6_child_subset Q m i) hx)
    (interior_mono (routing_constant_step4_ascent_ports_step6_child_subset Q' m i') hx')

/-- Step 3 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 §3.0, F.2):
a physical tile and its decoded ground node describe the same projected native tile. -/
private theorem all_height_hierarchy_step2_hierarchy_step3_tileNode_toTile
    (t : PlacedMarkedTile (systemM S P C)) :
    (tileNode t).toTile = t.native (nativeDecoration S P C) := by
  apply PlacedTile.ext
  · rfl
  · rw [PlacedMarkedTile.native_carrier]
    exact (compilerFrame_carrier C t).symm

/-- Step 3 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 §3.0, 3.1):
"the blocks [of a level] have disjoint interiors and cover", and each block is
the union of its actual native tiles. Hence every physical tile of Y lies inside
one block of the level: an open piece of its interior meets the interior of some
block, hence of one of that block's actual leaf tiles, which by disjointness of
the tile interiors of Y is the tile itself. -/
private theorem all_height_hierarchy_step2_hierarchy_step3_tile_in_block
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (G : GeometricLevel Y n)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles) :
    ∃ B ∈ G.blocks, t.carrier ⊆ B.carrier := by
  classical
  have hcar : ∀ u : PlacedMarkedTile (systemM S P C), (tileNode u).carrier 0 = u.carrier := by
    intro u
    rw [compilerFrame_carrier C u]
    change placedSet (compilerFrame C u) (S.supertile 0 (compilerLeaf C u).prototype) = _
    unfold SubstSystem.supertile
    rw [pow_zero]
    congr 1
    first
      | simp
      | (ext z; simp)
  obtain ⟨x₀, hx₀⟩ : (interior t.carrier).Nonempty := by
    rw [← hcar t]
    exact (assembly_step1_node_regular (tileNode t) 0).2.2.nonempty
  have hUo : IsOpen (interior t.carrier ∩ Metric.ball x₀ 1) :=
    isOpen_interior.inter Metric.isOpen_ball
  have hUne : (interior t.carrier ∩ Metric.ball x₀ 1).Nonempty :=
    ⟨x₀, hx₀, Metric.mem_ball_self one_pos⟩
  have hfin := G.locallyFinite.2 (Metric.ball x₀ 1) Metric.isBounded_ball
  haveI : Finite {B : Block Y n | B ∈ G.blocks ∧ (Metric.ball x₀ 1 ∩ B.carrier).Nonempty} :=
    hfin.to_subtype
  let f : Option (Σ B : {B : Block Y n | B ∈ G.blocks ∧ (Metric.ball x₀ 1 ∩ B.carrier).Nonempty},
      S.RoleWord B.val.node.ty n) → Set (E d) := fun o =>
    match o with
    | none => (Metric.ball x₀ 1)ᶜ
    | some q => ((S.nativeTile q.1.val.node.ty n q.2).move q.1.val.node.frame).carrier 0
  have hc : ∀ o, IsClosed (f o) := by
    rintro (_ | q)
    · exact Metric.isOpen_ball.isClosed_compl
    · exact (assembly_step1_node_regular _ 0).1
  have hcov : ⋃ o, f o = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases hy : y ∈ Metric.ball x₀ 1
    · obtain ⟨B, hB, hyB⟩ := G.cover y
      have hy' : y ∈ B.node.carrier (0 + n) := by rw [Nat.zero_add]; exact hyB
      obtain ⟨w, hw⟩ := all_height_hierarchy_step2_hierarchy_step2_cover_desc B.node 0 n y hy'
      exact Set.mem_iUnion.mpr ⟨some ⟨⟨B, hB, y, hy, hyB⟩, w⟩, hw⟩
    · exact Set.mem_iUnion.mpr ⟨none, hy⟩
  obtain ⟨y, hyU, hy⟩ :=
    (dense_iUnion_interior_of_closed hc hcov).inter_open_nonempty _ hUo hUne
  obtain ⟨o, hyo⟩ := Set.mem_iUnion.mp hy
  rcases o with _ | ⟨⟨B, hB, hBm⟩, w⟩
  · exact absurd hyU.2 (interior_subset hyo)
  · obtain ⟨t', ht', ht'eq⟩ := B.actual w
    have hyt' : y ∈ interior t'.carrier := by
      rw [← hcar t', ht'eq]
      exact hyo
    have htt : t' = t := by
      by_contra hne
      have hd : Disjoint (interior t'.carrier) (interior t.carrier) := Y.disjoint ht' ht hne
      exact Set.disjoint_left.mp hd hyt' hyU.1
    refine ⟨B, hB, ?_⟩
    rw [← htt, ← hcar t', ht'eq]
    exact routing_constant_step4_ascent_ports_step6_descendant_subset _ B.node 0 n
      ⟨n, by omega, w, rfl⟩

/-- Step 3 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 §1.0, 3.1):
"height zero is exactly the given physical tiling": the ground inner nodes of a
level are exactly the projected tiles of Y. -/
private theorem all_height_hierarchy_step2_hierarchy_step3_ground
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (G : GeometricLevel Y n) :
    {t | ∃ N ∈ G.nodes 0, N.toTile = t} = (Y.project (nativeDecoration S P C)).tiles := by
  have hproj : (Y.project (nativeDecoration S P C)).tiles =
      (fun u => u.native (nativeDecoration S P C)) '' Y.tiles := rfl
  rw [hproj]
  ext t
  constructor
  · rintro ⟨N, hN, rfl⟩
    obtain ⟨u, hu, hue⟩ := G.node_actual 0 N hN ()
    have hN' : (S.nativeTile N.ty 0 ()).move N.frame = N := by
      apply FramedNode.ext
      · rfl
      · show (AffineIsometryEquiv.refl ℝ (E d)).trans N.frame = N.frame
        rw [AffineIsometryEquiv.refl_trans]
    refine ⟨u, hu, ?_⟩
    show u.native (nativeDecoration S P C) = N.toTile
    rw [← all_height_hierarchy_step2_hierarchy_step3_tileNode_toTile, hue, hN']
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨B, hB, hsub⟩ := all_height_hierarchy_step2_hierarchy_step3_tile_in_block G u hu
    obtain ⟨_, w, hw⟩ := (Set.ext_iff.mp B.tiles_exact u).mp ⟨hu, hsub⟩
    exact ⟨tileNode u, ⟨B, hB, n, by omega, w, hw⟩,
      all_height_hierarchy_step2_hierarchy_step3_tileNode_toTile u⟩

/-- Step 3 of the V4 proof of `all_height_hierarchy_step2_hierarchy` (V4 §1.0, 3.0):
"physical tiles contained in a node are exactly its native tiles", for every
inner node of a level, transported to the native projection. -/
private theorem all_height_hierarchy_step2_hierarchy_step3_native_tiles
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (G : GeometricLevel Y n) (m : ℕ)
    (N : FramedNode S) (hN : N ∈ G.nodes m) :
    {t | t ∈ (Y.project (nativeDecoration S P C)).tiles ∧ t.carrier ⊆ N.carrier m} =
      {t | ∃ w : S.RoleWord N.ty m, ((S.nativeTile N.ty m w).move N.frame).toTile = t} := by
  have hproj : (Y.project (nativeDecoration S P C)).tiles =
      (fun u => u.native (nativeDecoration S P C)) '' Y.tiles := rfl
  have hex := (⟨N, G.node_actual m N hN⟩ : Block Y m).tiles_exact
  rw [hproj]
  ext t
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hsub⟩
    have hc : u.carrier ⊆ N.carrier m := by
      rw [← PlacedMarkedTile.native_carrier (nativeDecoration S P C) u]
      exact hsub
    obtain ⟨_, w, hw⟩ := (Set.ext_iff.mp hex u).mp ⟨hu, hc⟩
    exact ⟨w, (congrArg FramedNode.toTile hw).symm.trans
      (all_height_hierarchy_step2_hierarchy_step3_tileNode_toTile u)⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨u, hu, hue⟩ := G.node_actual m N hN w
    have hm := ((Set.ext_iff.mp hex u).mpr ⟨hu, w, hue⟩).2
    have heq : ((S.nativeTile N.ty m w).move N.frame).toTile =
        u.native (nativeDecoration S P C) := by
      rw [← hue]
      exact all_height_hierarchy_step2_hierarchy_step3_tileNode_toTile u
    refine ⟨⟨u, hu, heq.symm⟩, ?_⟩
    rw [heq, PlacedMarkedTile.native_carrier]
    exact hm

/-- Step 2 of the V4 proof of `all_height_hierarchy` (V4 3.1): "The levels are
nested by construction (each (n+1)-block is the union of its children), so they
define a coherent hierarchy on Y with nodes of height < K given by the
certificate subdivisions." The hierarchy whose height-m nodes are the height-m
inner nodes of every level n ≥ max m K, whose parents at heights ≥ K are the
proposed parents (V4 3.2, 3.7). -/
private theorem all_height_hierarchy_step2_hierarchy (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (levels : ∀ n : ℕ, P.K ≤ n → DecodedLevel Y n)
    (hinv : ∀ n hn, Inv (levels n hn))
    (hnest : ∀ n hn, Parser.NestedLevels (levels n hn)
      (levels (n + 1) (Nat.le_trans hn (Nat.le_succ n))))
    (hbase : Parser.CertificateBase (levels P.K le_rfl))
    (hroots : ∀ n hn, (levels (n + 1) (Nat.le_trans hn (Nat.le_succ n))).geometry.roots =
      Parser.proposedParents (levels n hn)) :
    ∃ H : CoherentHierarchy S (Y.project (nativeDecoration S P C)),
      (∀ (n m : ℕ) (hn : P.K ≤ n), m ≤ n → H.nodes m = (levels n hn).geometry.nodes m) ∧
      (∀ (n : ℕ) (hn : P.K ≤ n) (B : Block Y n)
        (hB : B ∈ (levels n hn).geometry.blocks) (hN : B.node ∈ H.nodes n),
          (H.parent n ⟨B.node, hN⟩).val = proposedParent (levels n hn) B hB) := by
  classical
  let Hn : ℕ → Set (FramedNode S) := fun m =>
    (levels (max m P.K) (le_max_right m P.K)).geometry.nodes m
  have hHn : ∀ (n m : ℕ) (hn : P.K ≤ n), m ≤ n → Hn m = (levels n hn).geometry.nodes m :=
    fun n m hn hm => all_height_hierarchy_step2_hierarchy_step1_nodes_eq levels hnest n
      (max m P.K) hn (le_max_right m P.K) m hm (le_max_left m P.K)
  have hpex : ∀ (m : ℕ) (N : {N // N ∈ Hn m}),
      ∃ Q : {Q // Q ∈ Hn (m + 1)}, ∃ i : S.I Q.val.ty, N.val = Q.val.child m i := by
    intro m N
    have hle : m ≤ max (m + 1) P.K := le_trans (Nat.le_succ m) (le_max_left _ _)
    have hN : N.val ∈ (levels (max (m + 1) P.K) (le_max_right _ _)).geometry.nodes m :=
      (Set.ext_iff.mp (hHn (max (m + 1) P.K) m (le_max_right _ _) hle) _).mp N.property
    obtain ⟨Q, hQ, i, hi⟩ :=
      all_height_hierarchy_step2_hierarchy_step2_level_parent_exists _ m N.val hN
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_left _ _))
    exact ⟨⟨Q, hQ⟩, i, hi⟩
  have hunique : ∀ (m : ℕ) (Q Q' : FramedNode S), Q ∈ Hn (m + 1) → Q' ∈ Hn (m + 1) →
      ∀ (i : S.I Q.ty) (i' : S.I Q'.ty), Q.child m i = Q'.child m i' → Q = Q' :=
    fun m Q Q' hQ hQ' i i' h =>
      all_height_hierarchy_step2_hierarchy_step2_level_parent_unique
        (levels (max (m + 1) P.K) (le_max_right _ _)).geometry m Q Q' hQ hQ' i i' h
  refine ⟨{
    nodes := Hn
    ground := all_height_hierarchy_step2_hierarchy_step3_ground
      (levels (max 0 P.K) (le_max_right 0 P.K)).geometry
    cover := fun m x => all_height_hierarchy_step2_hierarchy_step2_level_cover
      (levels (max m P.K) (le_max_right m P.K)).geometry m (le_max_left m P.K) x
    disjoint := fun m => all_height_hierarchy_step2_hierarchy_step2_level_disjoint
      (levels (max m P.K) (le_max_right m P.K)).geometry m
    parent := fun m N => Classical.choose (hpex m N)
    role := fun m N => Classical.choose (Classical.choose_spec (hpex m N))
    child_eq := fun m N => Classical.choose_spec (Classical.choose_spec (hpex m N))
    children_mem := fun m Q hQ i => by
      have h1 := (levels (max (m + 1) P.K) (le_max_right _ _)).geometry.child_mem m Q hQ i
      exact (Set.ext_iff.mp (hHn (max (m + 1) P.K) m (le_max_right _ _)
        (le_trans (Nat.le_succ m) (le_max_left _ _))) _).mpr h1
    parent_unique := fun m N Q hQ ⟨i, hi⟩ =>
      hunique m Q _ hQ (Classical.choose (hpex m N)).property i
        (Classical.choose (Classical.choose_spec (hpex m N)))
        (hi.symm.trans (Classical.choose_spec (Classical.choose_spec (hpex m N))))
    native_tiles := fun m Q hQ => all_height_hierarchy_step2_hierarchy_step3_native_tiles
      (levels (max m P.K) (le_max_right m P.K)).geometry m Q hQ }, ?_, ?_⟩
  · exact fun n m hn hm => hHn n m hn hm
  · intro n hn B hB hN
    show (Classical.choose (hpex n ⟨B.node, hN⟩)).val = proposedParent (levels n hn) B hB
    have hmem : proposedParent (levels n hn) B hB ∈
        (levels (n + 1) (Nat.le_trans hn (Nat.le_succ n))).geometry.roots := by
      rw [hroots n hn]
      exact ⟨B, hB, rfl⟩
    obtain ⟨B'', hB'', hB''eq⟩ := hmem
    have hPP : proposedParent (levels n hn) B hB ∈ Hn (n + 1) := by
      rw [hHn (n + 1) (n + 1) (Nat.le_trans hn (Nat.le_succ n)) le_rfl, ← hB''eq]
      exact GeometricLevel.root_mem _ B'' hB''
    have hj := Classical.choose_spec (Classical.choose_spec (hpex n ⟨B.node, hN⟩))
    exact (hunique n _ _ hPP (Classical.choose (hpex n ⟨B.node, hN⟩)).property
      (firstRole (levels n hn) B hB).2 _
      ((Parser.proposedParent_child (levels n hn) (hinv n hn) B hB).trans hj)).symm

/-- Step 1 of the V4 proof of `all_height_hierarchy_step3_low_levels` (V4 3.1):
"𝒩_n for n<K the nodes inside the K-blocks". The empty role word names the root. -/
private theorem all_height_hierarchy_step3_low_levels_step1_move_zero (R : FramedNode S)
    (n : ℕ) (u : S.RoleWord R.ty 0) :
    (S.descendantNode R.ty n 0 u).move R.frame = R := by
  rfl

/-- Step 1 of the V4 proof of `all_height_hierarchy_step3_low_levels` (V4 3.1):
"𝒩_n for n<K the nodes inside the K-blocks". Peeling the first letter of a role
word: a depth-(k+1) descendant is a depth-k descendant of the prescribed child. -/
private theorem all_height_hierarchy_step3_low_levels_step1_move_succ (R : FramedNode S)
    (n k : ℕ) (u : S.RoleWord R.ty (k + 1)) :
    (S.descendantNode R.ty n (k + 1) u).move R.frame =
      (S.descendantNode (R.child (n + k) u.1).ty n k u.2).move
        (R.child (n + k) u.1).frame := by
  rfl

open private exists_honest_step7_child_subset from Enforce.Tiling in
/-- Step 2 of the V4 proof of `all_height_hierarchy_step3_low_levels` (V4 3.1):
"the nodes inside the K-blocks". Every height-n inner node lies in its root. -/
private theorem all_height_hierarchy_step3_low_levels_step2_subset (n : ℕ) :
    ∀ (k : ℕ) (R : FramedNode S) (u : S.RoleWord R.ty k),
      ((S.descendantNode R.ty n k u).move R.frame).carrier n ⊆ R.carrier (n + k) := by
  intro k
  induction k with
  | zero =>
    intro R u x hx
    rw [all_height_hierarchy_step3_low_levels_step1_move_zero R n u] at hx
    exact hx
  | succ k ih =>
    intro R u
    rw [all_height_hierarchy_step3_low_levels_step1_move_succ R n k u]
    exact (ih (R.child (n + k) u.1) u.2).trans
      (exists_honest_step7_child_subset R (n + k) u.1)

/-- Step 3 of the V4 proof of `all_height_hierarchy_step3_low_levels` (V4 3.1, 3.7):
"the children tile it", iterated: the height-n inner nodes cover their root. -/
private theorem all_height_hierarchy_step3_low_levels_step3_cover (n : ℕ) :
    ∀ (k : ℕ) (R : FramedNode S), R.carrier (n + k) ⊆
      ⋃ u : S.RoleWord R.ty k, ((S.descendantNode R.ty n k u).move R.frame).carrier n := by
  intro k
  induction k with
  | zero =>
    intro R x hx
    refine Set.mem_iUnion.mpr ⟨(), ?_⟩
    rw [all_height_hierarchy_step3_low_levels_step1_move_zero R n ()]
    exact hx
  | succ k ih =>
    intro R x hx
    have hx' : x ∈ R.carrier (n + k + 1) := hx
    rw [assembly_step1_children_cover R (n + k)] at hx'
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp (ih (R.child (n + k) i) hi)
    refine Set.mem_iUnion.mpr ⟨⟨i, u⟩, ?_⟩
    rw [all_height_hierarchy_step3_low_levels_step1_move_succ R n k ⟨i, u⟩]
    exact hu

/-- Step 4 of the V4 proof of `all_height_hierarchy_step3_low_levels` (V4 3.1, 3.7):
"the children tile it", iterated: distinct height-n inner nodes of one root have
disjoint interiors. -/
private theorem all_height_hierarchy_step3_low_levels_step4_disjoint (n : ℕ) :
    ∀ (k : ℕ) (R : FramedNode S) (u v : S.RoleWord R.ty k),
      (S.descendantNode R.ty n k u).move R.frame ≠
          (S.descendantNode R.ty n k v).move R.frame →
        Disjoint (interior (((S.descendantNode R.ty n k u).move R.frame).carrier n))
          (interior (((S.descendantNode R.ty n k v).move R.frame).carrier n)) := by
  intro k
  induction k with
  | zero =>
    intro R u v hne
    exact (hne rfl).elim
  | succ k ih =>
    intro R u v hne
    obtain ⟨i, u⟩ := u
    obtain ⟨j, v⟩ := v
    rw [all_height_hierarchy_step3_low_levels_step1_move_succ R n k ⟨i, u⟩,
      all_height_hierarchy_step3_low_levels_step1_move_succ R n k ⟨j, v⟩] at hne ⊢
    by_cases hij : i = j
    · subst hij
      exact ih (R.child (n + k) i) u v hne
    · have h1 := all_height_hierarchy_step3_low_levels_step2_subset n k (R.child (n + k) i) u
      have h2 := all_height_hierarchy_step3_low_levels_step2_subset n k (R.child (n + k) j) v
      exact (assembly_step1_children_disjoint R (n + k) i j hij).mono
        (interior_mono h1) (interior_mono h2)

open private exists_honest_step7_split_word from Enforce.Tiling in
/-- Step 5 of the V4 proof of `all_height_hierarchy_step3_low_levels` (V4 3.1):
"𝒩_n for n<K the nodes inside the K-blocks": a lower inner node of a root lies
inside one of its height-n inner nodes. -/
private theorem all_height_hierarchy_step3_low_levels_step5_factor (R N : FramedNode S)
    (m n K : ℕ) (hmn : m ≤ n) (hnK : n ≤ K) (h : N.IsDescendant m R K) :
    ∃ M : FramedNode S, M.IsDescendant n R K ∧ N.IsDescendant m M n := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnK
  obtain ⟨r, hr, w, rfl⟩ := h
  obtain rfl : r = j + k := by omega
  obtain ⟨u, v, hv⟩ := exists_honest_step7_split_word R.ty m j k w
  refine ⟨(S.descendantNode R.ty (m + j) k u).move R.frame, ⟨k, rfl, u, rfl⟩, j, rfl, v, ?_⟩
  rw [hv]
  rfl

/-- Step 3 of the V4 proof of `all_height_hierarchy` (V4 3.1): "(with 𝒩_n for
n<K the nodes inside the K-blocks)" and, for the certificate tables, "for heights
<K the certificate tables" (V4 4.4(i)). For every height n < K, the height-n
inner nodes of the base level K, regarded as blocks with the restricted states
of the base level, form a decoded level with Inv(n); its nodes of height m ≤ n
are those of the base level and its states are the base states. -/
private theorem all_height_hierarchy_step3_low_levels (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (D : DecodedLevel Y P.K) (hD : Inv D)
    (hbase : Parser.CertificateBase D) (n : ℕ) (hn : n < P.K) :
    ∃ L : DecodedLevel Y n, Inv L ∧ L.geometry.roots = D.geometry.nodes n ∧
      (∀ m : ℕ, m ≤ n → L.geometry.nodes m = D.geometry.nodes m) ∧
      ∀ (m : ℕ) (N : FramedNode S) (hL : N ∈ L.geometry.nodes m)
        (hK : N ∈ D.geometry.nodes m), L.stateAt m N hL = D.stateAt m N hK := by
  have hdisj : ({B : Block Y n | B.node ∈ D.geometry.nodes n}).PairwiseDisjoint
      (fun B => interior B.carrier) := by
    intro B1 hB1 B2 hB2 hne
    obtain ⟨R1, hR1, k1, hk1, w1, he1⟩ := hB1
    obtain ⟨R2, hR2, k2, hk2, w2, he2⟩ := hB2
    have hne' : B1.node ≠ B2.node := fun h => hne (Block.ext h)
    show Disjoint (interior (B1.node.carrier n)) (interior (B2.node.carrier n))
    by_cases hR : R1 = R2
    · subst hR
      obtain rfl : k2 = k1 := by omega
      rw [he1, he2] at hne' ⊢
      exact all_height_hierarchy_step3_low_levels_step4_disjoint n _ R1.node w1 w2 hne'
    · have h1 : B1.node.carrier n ⊆ R1.carrier := by
        have h := all_height_hierarchy_step3_low_levels_step2_subset n k1 R1.node w1
        rw [← hk1, ← he1] at h
        exact h
      have h2 : B2.node.carrier n ⊆ R2.carrier := by
        have h := all_height_hierarchy_step3_low_levels_step2_subset n k2 R2.node w2
        rw [← hk2, ← he2] at h
        exact h
      exact (D.geometry.disjoint hR1 hR2 hR).mono (interior_mono h1) (interior_mono h2)
  have hcov : ∀ x : E d, ∃ B ∈ {B : Block Y n | B.node ∈ D.geometry.nodes n},
      x ∈ B.carrier := by
    intro x
    obtain ⟨R, hR, hx⟩ := D.geometry.cover x
    have hK : P.K = n + (P.K - n) := by omega
    have hx' : x ∈ R.node.carrier (n + (P.K - n)) := by
      rw [← hK]
      exact hx
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp
      (all_height_hierarchy_step3_low_levels_step3_cover n (P.K - n) R.node hx')
    have hM : (S.descendantNode R.node.ty n (P.K - n) u).move R.node.frame ∈
        D.geometry.nodes n := ⟨R, hR, P.K - n, hK, u, rfl⟩
    exact ⟨⟨_, D.geometry.node_actual n _ hM⟩, hM, hu⟩
  have hGsub : ∀ (m : ℕ) (N : FramedNode S),
      N ∈ (⟨_, hdisj, hcov⟩ : GeometricLevel Y n).nodes m → N ∈ D.geometry.nodes m := by
    rintro m N ⟨B, hB, h⟩
    exact D.geometry.descendant_mem n m B.node N hB h
  refine ⟨⟨⟨_, hdisj, hcov⟩, fun m N => D.state m ⟨N.1, hGsub m N.1 N.2⟩,
    fun m N => D.state_honest m _⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, fun _ _ _ _ => rfl⟩
  · intro B hB
    have hB' : B.node ∈ D.geometry.nodes n := hB
    exact ⟨D.state_honest n _, (hD.node_type_residue n B.node hB').1,
      (hD.node_type_residue n B.node hB').2⟩
  · exact ⟨fun m N hN i => hD.I2.1 m N (hGsub _ _ hN) i,
      fun N hN t ht heq => hD.I2.2 N (hGsub _ _ hN) t ht heq⟩
  · exact fun m N hN g hb hdepth hp => hD.I4 m N (hGsub _ _ hN) g hb hdepth hp
  · exact fun m N hN => hD.I5 m N (hGsub _ _ hN)
  · ext N
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact hB
    · intro hN
      exact ⟨⟨N, D.geometry.node_actual n N hN⟩, hN, rfl⟩
  · intro m hm
    ext N
    constructor
    · exact hGsub m N
    · rintro ⟨R, hR, h⟩
      obtain ⟨M, hM, hNM⟩ :=
        all_height_hierarchy_step3_low_levels_step5_factor R.node N m n P.K hm hn.le h
      exact ⟨⟨M, D.geometry.node_actual n M ⟨R, hR, hM⟩⟩, ⟨R, hR, hM⟩, hNM⟩

open private exists_childMap_step2_role from Enforce.State.State in
/-- Step 4 of the V4 proof of `all_height_hierarchy` (V4 3.1): "Consequently Y
carries a coherent hierarchy (𝒩_n)_{n≥0} (with 𝒩_n for n<K the nodes inside the
K-blocks) with states satisfying (I1),(I2),(I4),(I5) at every height." Given the
nested sequence, the hierarchy of Step 2 and the low levels of Step 3 (the
restrictions of the K-level), the full decoded levels, the state agreement along
the nesting and the first-letter roles (from (I2)) assemble the realization. -/
private theorem all_height_hierarchy_step4_realize (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (levels : ∀ n : ℕ, P.K ≤ n → DecodedLevel Y n)
    (H : CoherentHierarchy S (Y.project (nativeDecoration S P C)))
    (hinv : ∀ n hn, Inv (levels n hn))
    (hnest : ∀ n hn, Parser.NestedLevels (levels n hn)
      (levels (n + 1) (Nat.le_trans hn (Nat.le_succ n))))
    (hbase : Parser.CertificateBase (levels P.K le_rfl))
    (hroots : ∀ n hn, (levels (n + 1) (Nat.le_trans hn (Nat.le_succ n))).geometry.roots =
      Parser.proposedParents (levels n hn))
    (hnodes : ∀ (n m : ℕ) (hn : P.K ≤ n), m ≤ n →
      H.nodes m = (levels n hn).geometry.nodes m)
    (hpar : ∀ (n : ℕ) (hn : P.K ≤ n) (B : Block Y n)
        (hB : B ∈ (levels n hn).geometry.blocks) (hN : B.node ∈ H.nodes n),
          (H.parent n ⟨B.node, hN⟩).val = proposedParent (levels n hn) B hB)
    (hlow : ∀ n : ℕ, n < P.K → ∃ L : DecodedLevel Y n, Inv L ∧
      L.geometry.roots = (levels P.K le_rfl).geometry.nodes n ∧
      (∀ m : ℕ, m ≤ n → L.geometry.nodes m = (levels P.K le_rfl).geometry.nodes m) ∧
      ∀ (m : ℕ) (N : FramedNode S) (hL : N ∈ L.geometry.nodes m)
        (hK : N ∈ (levels P.K le_rfl).geometry.nodes m),
          L.stateAt m N hL = (levels P.K le_rfl).stateAt m N hK) :
    Nonempty (Parser.HierarchyRealizes Y levels H) := by
  classical
  -- the full levels: the induction sequence above K, the low levels of Step 3 below K
  let F : ∀ n : ℕ, DecodedLevel Y n := fun n =>
    if h : P.K ≤ n then levels n h else Classical.choose (hlow n (lt_of_not_ge h))
  have hFu : ∀ n (hn : P.K ≤ n), F n = levels n hn := fun n hn => dif_pos hn
  have hFl : ∀ n (hn : ¬ P.K ≤ n), F n = Classical.choose (hlow n (lt_of_not_ge hn)) :=
    fun n hn => dif_neg hn
  -- transport of an inner state along an equality of decoded levels
  have htr : ∀ {k : ℕ} {D D' : DecodedLevel Y k}, D = D' →
      ∀ (m : ℕ) (N : FramedNode S) (h : N ∈ D.geometry.nodes m),
        ∃ h' : N ∈ D'.geometry.nodes m, D.stateAt m N h = D'.stateAt m N h' := by
    intro k D D' e m N h
    subst e
    exact ⟨h, rfl⟩
  -- states agree along the nesting
  have hmono : ∀ (a : ℕ) (ha : P.K ≤ a) (d m : ℕ) (N : FramedNode S)
      (h : N ∈ (levels a ha).geometry.nodes m),
        ∃ h' : N ∈ (levels (a + d) (le_trans ha (Nat.le_add_right a d))).geometry.nodes m,
          (levels a ha).stateAt m N h =
            (levels (a + d) (le_trans ha (Nat.le_add_right a d))).stateAt m N h' := by
    intro a ha d
    induction d with
    | zero => intro m N h; exact ⟨h, rfl⟩
    | succ d ih =>
      intro m N h
      obtain ⟨h1, e1⟩ := ih m N h
      have hN := hnest (a + d) (le_trans ha (Nat.le_add_right a d))
      exact ⟨hN.nodes m h1, e1.trans (hN.states m N h1 (hN.nodes m h1))⟩
  have hagree : ∀ (a : ℕ) (ha : P.K ≤ a) (b : ℕ) (hb : P.K ≤ b) (m : ℕ) (N : FramedNode S)
      (h : N ∈ (levels a ha).geometry.nodes m), m ≤ b →
        ∃ h' : N ∈ (levels b hb).geometry.nodes m,
          (levels a ha).stateAt m N h = (levels b hb).stateAt m N h' := by
    intro a ha b hb m N h hmb
    have hma := (levels a ha).geometry.nodes_height m N h
    have h' : N ∈ (levels b hb).geometry.nodes m := by
      rw [← hnodes b m hb hmb, hnodes a m ha hma]
      exact h
    rcases le_total a b with hab | hba
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
      exact hmono a ha d m N h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hba
      obtain ⟨h2, e2⟩ := hmono b hb d m N h'
      exact ⟨h', e2.symm⟩
  -- every inner state of every full level is the state of one reference level
  have hstate : ∀ (n m : ℕ) (N : FramedNode S) (h : N ∈ (F n).geometry.nodes m),
      ∃ h' : N ∈ (levels (max P.K (m + 1)) (le_max_left _ _)).geometry.nodes m,
        (F n).stateAt m N h =
          (levels (max P.K (m + 1)) (le_max_left _ _)).stateAt m N h' := by
    intro n m N h
    have hmn : m ≤ n := (F n).geometry.nodes_height m N h
    by_cases hn : P.K ≤ n
    · obtain ⟨h1, e1⟩ := htr (hFu n hn) m N h
      obtain ⟨h2, e2⟩ := hagree n hn _ (le_max_left _ _) m N h1
        (le_trans (Nat.le_succ m) (le_max_right _ _))
      exact ⟨h2, e1.trans e2⟩
    · have hlt : n < P.K := lt_of_not_ge hn
      have spec := Classical.choose_spec (hlow n hlt)
      obtain ⟨h1, e1⟩ := htr (hFl n hn) m N h
      have hK : N ∈ (levels P.K le_rfl).geometry.nodes m := by
        rw [← spec.2.2.1 m hmn]
        exact h1
      have e2 := spec.2.2.2 m N h1 hK
      obtain ⟨h3, e3⟩ := hagree P.K le_rfl _ (le_max_left _ _) m N hK
        (le_trans (Nat.le_succ m) (le_max_right _ _))
      exact ⟨h3, e1.trans (e2.trans e3)⟩
  -- (I2) in one honest realization: the first letter of a child state is its role
  have hrole_of : ∀ {k : ℕ} (D : DecodedLevel Y k) (hD : Inv D) (m : ℕ) (Q : FramedNode S)
      (hQ : Q ∈ D.geometry.nodes (m + 1)) (i : S.I Q.ty),
        (D.stateAt m (Q.child m i) (D.geometry.child_mem m Q hQ i)).address ⟨0, P.k_pos⟩ =
          ⟨Q.ty, i⟩ := by
    intro k D hD m Q hQ i
    obtain ⟨U, hU, hs⟩ := routing_constant_step2_source_realization
      (D.stateAt (m + 1) Q hQ) (D.state_honest _ _) Q (m + 1)
      (hD.node_type_residue _ _ hQ).1 (hD.node_type_residue _ _ hQ).2
    rw [hD.I2.1 m Q hQ i, ← hs]
    have hc := childMap_spec U P ⟨m + 1, ⟨Q, hU⟩⟩ (by change 1 ≤ m + 1; omega) i
    rw [show childMap P (stateOf U P ⟨m + 1, ⟨Q, hU⟩⟩) ⟨Q.ty, i⟩ =
      stateOf U P (U.childNode ⟨m + 1, ⟨Q, hU⟩⟩ (by change 1 ≤ m + 1; omega) i)
      from hc.symm]
    exact exists_childMap_step2_role U ⟨m + 1, ⟨Q, hU⟩⟩ (by change 1 ≤ m + 1; omega) i
  have hroles : ∀ (m : ℕ) (N : FramedNode S) (hN : N ∈ H.nodes m)
      (h : N ∈ (F m).geometry.nodes m),
        ((F m).stateAt m N h).address ⟨0, P.k_pos⟩ = H.nodeRole ⟨m, ⟨N, hN⟩⟩ := by
    intro m N hN h
    obtain ⟨h', he⟩ := hstate m m N h
    rw [he]
    have hr : P.K ≤ max P.K (m + 1) := le_max_left _ _
    have hQ : (H.parent m ⟨N, hN⟩).val ∈
        (levels (max P.K (m + 1)) hr).geometry.nodes (m + 1) := by
      rw [← hnodes _ (m + 1) hr (le_max_right _ _)]
      exact (H.parent m ⟨N, hN⟩).property
    have key := hrole_of _ (hinv _ hr) m _ hQ (H.role m ⟨N, hN⟩)
    have aux : ∀ (N' : FramedNode S) (h1 : N' ∈ (levels (max P.K (m + 1)) hr).geometry.nodes m),
        N' = (H.parent m ⟨N, hN⟩).val.child m (H.role m ⟨N, hN⟩) →
          ((levels (max P.K (m + 1)) hr).stateAt m N' h1).address ⟨0, P.k_pos⟩ =
            ⟨(H.parent m ⟨N, hN⟩).val.ty, H.role m ⟨N, hN⟩⟩ := by
      rintro _ h1 rfl
      exact key
    exact aux N h' (H.child_eq m ⟨N, hN⟩)
  refine ⟨{
    invariant := hinv
    nested := hnest
    base := hbase
    fullLevels := F
    full_invariant := ?_
    upper_eq := hFu
    roots := ?_
    inner_nodes := ?_
    below_K := fun n hn => hnodes P.K n le_rfl hn.le
    states := ?_
    parents := hpar
    roles := ?_ }⟩
  · intro n
    by_cases hn : P.K ≤ n
    · rw [hFu n hn]; exact hinv n hn
    · rw [hFl n hn]; exact (Classical.choose_spec (hlow n (lt_of_not_ge hn))).1
  · intro n
    by_cases hn : P.K ≤ n
    · rw [hFu n hn, ← (levels n hn).geometry.nodes_top, hnodes n n hn le_rfl]
    · rw [hFl n hn, (Classical.choose_spec (hlow n (lt_of_not_ge hn))).2.1,
        hnodes P.K n le_rfl (lt_of_not_ge hn).le]
  · intro n m hmn
    by_cases hn : P.K ≤ n
    · rw [hFu n hn]; exact (hnodes n m hn hmn).symm
    · rw [hFl n hn, (Classical.choose_spec (hlow n (lt_of_not_ge hn))).2.2.1 m hmn]
      exact (hnodes P.K m le_rfl (le_trans hmn (lt_of_not_ge hn).le)).symm
  · intro n m N hn hm
    obtain ⟨h1, e1⟩ := hstate n m N hn
    obtain ⟨h2, e2⟩ := hstate m m N hm
    exact e1.trans e2.symm
  · rintro ⟨m, ⟨N, hN⟩⟩
    exact hroles m N hN _

/-- R12, V4 3.1: one nested sequence of decoded levels exists for all n ≥ K,
with Inv(n) and agreeing inner states, and realizes a coherent hierarchy on the
exact native projection of the arbitrary proper output Y. At heights below K,
the nodes and their states come from the forced honest K-certificates.
The existential witnesses are correlated through HierarchyRealizes; they do not
assert independent existence at each height or source-species membership of Y.
An actual M-proper Y supplies the base, so no species nonemptiness is assumed. -/
theorem all_height_hierarchy (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    ∃ levels : ∀ n : ℕ, P.K ≤ n → DecodedLevel Y n,
      ∃ H : CoherentHierarchy S (Y.project (nativeDecoration S P C)),
        Nonempty (Parser.HierarchyRealizes Y levels H) := by
  obtain ⟨levels, hinv, hnest, hbase, hroots⟩ := all_height_hierarchy_step1_sequence Y hY
  obtain ⟨H, hnodes, hpar⟩ :=
    all_height_hierarchy_step2_hierarchy Y hY levels hinv hnest hbase hroots
  exact ⟨levels, H,
    all_height_hierarchy_step4_realize Y hY levels H hinv hnest hbase hroots hnodes hpar
      (fun n hn => all_height_hierarchy_step3_low_levels Y hY _ (hinv P.K le_rfl) hbase n hn)⟩

/-- R12, V4 3.1: the chosen correlated induction sequence, from the single
all-height existence theorem. Definitions contain no proof holes. -/
def parsedLevels (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    ∀ n : ℕ, P.K ≤ n → DecodedLevel Y n :=
  Classical.choose (all_height_hierarchy Y hY)

/-- R12, V4 3.1: the parsed coherent hierarchy, chosen from all_height_hierarchy
after fixing that theorem's one sequence of decoded levels. Its low levels are
the actual K-block inner nodes, by parsedHierarchy_below_K. -/
def parsedHierarchy (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    CoherentHierarchy S (Y.project (nativeDecoration S P C)) :=
  Classical.choose (Classical.choose_spec (all_height_hierarchy Y hY))

/-- R12, V4 3.1: the realization data for those very same levels and hierarchy.
The final nonempty witness retains all state assignments and their agreements. -/
def parsedRealization (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    Parser.HierarchyRealizes Y (parsedLevels Y hY) (parsedHierarchy Y hY) :=
  Classical.choice (Classical.choose_spec
    (Classical.choose_spec (all_height_hierarchy Y hY)))

/-- R12, V4 3.1: the decoded level at any height in the chosen realization,
including heights below K. Its state table is part of the one parsed hierarchy. -/
def parsedDecodedLevel (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) : DecodedLevel Y n := (parsedRealization Y hY).fullLevels n

/-- R12, V4 3.1: the assigned state of an actual node of the parsed hierarchy. -/
def parsedState (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) : State P := (parsedRealization Y hY).state q

/-- R12, V4 3.1: every chosen high decoded level satisfies Inv(n). -/
theorem parsedLevels_invariant (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) : Inv (parsedLevels Y hY n hn) :=
  (parsedRealization Y hY).invariant n hn

/-- R12, V4 3.1: consecutive chosen levels are nested and their states agree. -/
theorem parsedLevels_nested (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) :
    Parser.NestedLevels (parsedLevels Y hY n hn)
      (parsedLevels Y hY (n + 1) (Nat.le_trans hn (Nat.le_succ n))) :=
  (parsedRealization Y hY).nested n hn

/-- R12, V4 3.1: all four invariants hold for decoded levels at every height. -/
theorem parsedHierarchy_invariant (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) : Inv (parsedDecodedLevel Y hY n) :=
  (parsedRealization Y hY).full_invariant n

/-- R12, V4 3.1: high decoded levels are literally the induction witnesses. -/
theorem parsedDecodedLevel_upper (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) : parsedDecodedLevel Y hY n = parsedLevels Y hY n hn :=
  (parsedRealization Y hY).upper_eq n hn

/-- R12, V4 3.1: the full decoded roots are exactly the parsed framed nodes. -/
theorem parsedHierarchy_nodes (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) : (parsedDecodedLevel Y hY n).geometry.roots = (parsedHierarchy Y hY).nodes n :=
  (parsedRealization Y hY).roots n

/-- R12, V4 3.1: at n < K, the parsed nodes are exactly the inner nodes of
the K-certificate base; no fresh low-height subdivision is chosen. -/
theorem parsedHierarchy_below_K (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : n < P.K) :
    (parsedHierarchy Y hY).nodes n = (parsedLevels Y hY P.K le_rfl).geometry.nodes n :=
  (parsedRealization Y hY).below_K n hn

/-- R12, V4 3.1, 3.2: the chosen base is precisely the compiler certificate family,
and its entire table agrees with every certificate's honest inner-node table. -/
theorem parsedHierarchy_base (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    Parser.CertificateBase (parsedLevels Y hY P.K le_rfl) :=
  (parsedRealization Y hY).base

/-- R12, V4 3.1: every actual parsed state is honest with the correct type and residue. -/
theorem parsedState_type_residue (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) :
    parsedState Y hY q ∈ honestStates S P ∧ (parsedState Y hY q).ty = q.2.val.ty ∧
      (parsedState Y hY q).residue.val = q.1 % P.L :=
  ⟨(parsedRealization Y hY).state_honest q, (parsedRealization Y hY).state_type_residue q⟩

/-- R12, V4 3.1: the parsed state's first role agrees with the actual parent. -/
theorem parsedState_role (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) :
    (parsedState Y hY q).address ⟨0, P.k_pos⟩ = (parsedHierarchy Y hY).nodeRole q :=
  (parsedRealization Y hY).state_role q

/-- R12, V4 3.1: all actual parent-child state equations hold in the parsed hierarchy. -/
theorem parsedState_child (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (hc : q.2.val.child (q.1 - 1) i ∈ (parsedHierarchy Y hY).nodes (q.1 - 1)) :
    parsedState Y hY ⟨q.1 - 1, ⟨q.2.val.child (q.1 - 1) i, hc⟩⟩ =
      childMap P (parsedState Y hY q) ⟨q.2.val.ty, i⟩ :=
  (parsedRealization Y hY).state_child q hq i hc

/-- R12, V4 3.1 (I5): parsed hierarchy boundary attachment is available at
every height, with equality on meeting E-related facets and NULL retained. -/
theorem parsedState_boundary (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) :
    ∃ h : Parser.BoundaryPackets Y q.1 q.2.val, ∀ F F' : FacetName S q.2.val.ty,
      stateEAt (parsedState Y hY q) F.val F'.val →
      (q.2.val.cell q.1 F.val ∩ q.2.val.cell q.1 F'.val).Nonempty →
        attachedPacket h F = attachedPacket h F' :=
  (parsedRealization Y hY).boundary_invariant q

/-- R12, V4 3.1: all inner nodes of a chosen higher level give exactly the
corresponding lower hierarchy level, including the actual framed ground tiles. -/
theorem parsedHierarchy_inner_nodes (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n m : ℕ) (hmn : m ≤ n) :
    (parsedDecodedLevel Y hY n).geometry.nodes m = (parsedHierarchy Y hY).nodes m :=
  (parsedRealization Y hY).inner_nodes n m hmn

/-- R12, V4 3.1: the global state agrees with every containing decoded table.
Thus passing to a higher block never reassigns an earlier inner node's state. -/
theorem parsedState_agrees (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n m : ℕ) (N : FramedNode S)
    (hN : N ∈ (parsedDecodedLevel Y hY n).geometry.nodes m)
    (hm : N ∈ (parsedHierarchy Y hY).nodes m) :
    (parsedDecodedLevel Y hY n).stateAt m N hN = parsedState Y hY ⟨m, ⟨N, hm⟩⟩ :=
  (parsedRealization Y hY).state_agrees n m N hN hm

/-- R12, V4 3.1 (I2): parsed height-zero states are the physical tiles'
pre-pattern states, with the leaf type and frame decoded from the actual marking. -/
theorem parsedState_ground (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : q.1 = 0)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (heq : tileNode t = q.2.val) : parsedState Y hY q = (compilerLeaf C t).prePattern.state :=
  (parsedRealization Y hY).state_ground q hq t ht heq

/-- R12, V4 3.1 (I4): every principal primitive facet born inside a parsed
node has that node's actual state in its PRESENT slot, at every height. -/
theorem parsedState_principal (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (g : Parser.BornFacet P)
    (hbirth : g.birth.IsDescendant g.height q.2.val q.1)
    (hdepth : q.1 - g.height < P.k) (hprincipal : P.InPrincipal q.2.val q.1 g.carrier) :
    ∃ hleft : Parser.BoundaryPackets Y (g.height - 1) g.leftNode, ∃ p : Packet P,
      g.packet hleft = some p ∧
        decode p ⟨q.1 - g.height, hdepth⟩ = some (parsedState Y hY q) :=
  (parsedRealization Y hY).principal_invariant q g hbirth hdepth hprincipal

/-- R12/R13, V4 3.1, 3.13: every letter in the assigned upward address is
the actual globally distinct role of the indicated hierarchy ancestor. -/
theorem parsedState_address (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (j : Fin P.k) :
    (parsedState Y hY q).address j =
      (parsedHierarchy Y hY).nodeRole ((parsedHierarchy Y hY).ancestor q j.val) := by
  sorry

/-- R12, V4 3.1, §3.2: the actual high-level parent is the proposed parent
computed from the old block's first address letter, with the exact full frame. -/
theorem parsedLevels_parent (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (B : Block Y n)
    (hB : B ∈ (parsedLevels Y hY n hn).geometry.blocks)
    (hN : B.node ∈ (parsedHierarchy Y hY).nodes n) :
    ((parsedHierarchy Y hY).parent n ⟨B.node, hN⟩).val =
      proposedParent (parsedLevels Y hY n hn) B hB :=
  (parsedRealization Y hY).parents n hn B hB hN

/-- R12, V4 3.1 (I5): the constancy proof supplied by the single parsed state
assignment. This selects a proof, not a packet or an additional source witness. -/
def parsedBoundaryPackets (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) : Parser.BoundaryPackets Y q.1 q.2.val :=
  (parsedState_boundary Y hY q).choose

/-- R12, V4 3.1 (I5): the packet attached to a boundary facet from one parsed
node, read from the actual tile pre-patterns. Its value may be NULL or a packet;
persistent faults are subject only to constancy and E-equality. -/
def parsedFacetPacket (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (F : FacetName S q.2.val.ty) : Option (Packet P) :=
  attachedPacket (parsedBoundaryPackets Y hY q) F

/-- R12, V4 3.1 (I5): parsed attachment has the defining actual leaf-readout property. -/
theorem parsedFacetPacket_spec (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (F : FacetName S q.2.val.ty) :
    Parser.ConstantPacket Y q.1 q.2.val F (parsedFacetPacket Y hY q F) :=
  attachedPacket_spec (parsedBoundaryPackets Y hY q) F

/-- R12, V4 3.1 (I5): meeting E-related parsed facets carry exactly equal packets. -/
theorem parsedFacetPacket_E (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (F F' : FacetName S q.2.val.ty)
    (hE : stateEAt (parsedState Y hY q) F.val F'.val)
    (hmeet : (q.2.val.cell q.1 F.val ∩ q.2.val.cell q.1 F'.val).Nonempty) :
    parsedFacetPacket Y hY q F = parsedFacetPacket Y hY q F' :=
  (parsedState_boundary Y hY q).choose_spec F F' hE hmeet

/-- R12, V4 3.1 (I5): every non-NULL parsed boundary packet belongs to the
honest packet alphabet, even when its facet is a persistent fault of Y. This
asserts admissibility of the readout, not actuality of its claimed provider. -/
theorem parsedFacetPacket_honest (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (F : FacetName S q.2.val.ty) (p : Packet P)
    (hp : parsedFacetPacket Y hY q F = some p) : p ∈ honestPackets S P := by
  sorry

/-- R12, V4 3.1 (I5): a boundary track retains the same attached packet in
every descendant facet piece. The assertion includes NULL and phantom packets. -/
theorem parsedFacetPacket_inherited (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q c : (parsedHierarchy Y hY).Node)
    (hdesc : c.2.val.IsDescendant c.1 q.2.val q.1)
    (F : FacetName S q.2.val.ty) (f : FacetName S c.2.val.ty)
    (hsub : c.2.val.cell c.1 f.val ⊆ q.2.val.cell q.1 F.val) :
    parsedFacetPacket Y hY q F = parsedFacetPacket Y hY c f := by
  sorry

namespace Parser.BornFacet

/-- R13, V4 3.13: the actual birth node of a primitive facet in a specified
coherent hierarchy. Membership is explicit; no source hierarchy is assumed. -/
def hierarchyBirth {Y : MarkedTiling (systemM S P C)}
    (H : CoherentHierarchy S (Y.project (nativeDecoration S P C)))
    (g : Parser.BornFacet P) (hg : g.birth ∈ H.nodes g.height) : H.Node :=
  ⟨g.height, ⟨g.birth, hg⟩⟩

end Parser.BornFacet

/-- R13, V4 3.13: the primitive packet in the parsed output, initially read
from the canonical left child. Its two-sided and non-NULL calibration is W4.
This definition uses (I5) on the actual left hierarchy node and makes no new
choice of a state, source occurrence or provider. -/
def parsedPrimitivePacket (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Parser.BornFacet P) (hg : g.birth ∈ (parsedHierarchy Y hY).nodes g.height) :
    Option (Packet P) :=
  parsedFacetPacket Y hY ⟨g.height - 1, ⟨g.leftNode, g.left_mem (parsedHierarchy Y hY) hg⟩⟩
    g.incidence.val.leftFacet

/-- R13, V4 3.13 (W4): for every actual finite primitive birth in the parsed
hierarchy, the attached packet is two-sided, honest and has that birth's state
as head. At each index 0 ≤ j ≤ k-1 its mask is PRESENT exactly when its carrier
belongs to the actual ancestor's E-set, and every PRESENT slot is the state
assigned to that ancestor by Theorem 3.1. Persistent faults are not finite births
and receive no additional provider or NULL assertion here (Remark 3.14). -/
theorem calibration_W4 (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Parser.BornFacet P) (hg : g.birth ∈ (parsedHierarchy Y hY).nodes g.height) :
    ∃ hleft : Parser.BoundaryPackets Y (g.height - 1) g.leftNode,
      ∃ hright : Parser.BoundaryPackets Y (g.height - 1) g.rightNode,
        attachedPacket hleft g.incidence.val.leftFacet =
          attachedPacket hright g.incidence.val.rightFacet ∧
        ∃ q : Packet P, g.packet hleft = some q ∧ q ∈ honestPackets S P ∧
          q.incidence = g.incidence ∧
          q.head = parsedState Y hY (g.hierarchyBirth (parsedHierarchy Y hY) hg) ∧
          ∀ j : Fin P.k,
            let ancestor := (parsedHierarchy Y hY).ancestor
              (g.hierarchyBirth (parsedHierarchy Y hY) hg) j.val
            (q.mask j ↔ P.InPrincipal ancestor.2.val ancestor.1 g.carrier) ∧
              (q.mask j → decode q j = some (parsedState Y hY ancestor)) := by
  sorry

/-- R13, V4 3.13: every finite primitive birth has a non-NULL honest attached
packet of its actual incidence, and the canonical left/right readouts are equal. -/
theorem parsedPrimitivePacket_spec (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Parser.BornFacet P) (hg : g.birth ∈ (parsedHierarchy Y hY).nodes g.height) :
    parsedPrimitivePacket Y hY g hg =
      parsedFacetPacket Y hY
        ⟨g.height - 1, ⟨g.rightNode, g.right_mem (parsedHierarchy Y hY) hg⟩⟩
        g.incidence.val.rightFacet ∧
      ∃ p : Packet P, parsedPrimitivePacket Y hY g hg = some p ∧
        p ∈ honestPackets S P ∧ p.incidence = g.incidence := by
  sorry

/-- R13, V4 3.13: W4 for a specified actual packet readout. Its complete mask
and every PRESENT slot refer to the actual ancestors and their assigned states. -/
theorem calibration_W4_readout (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Parser.BornFacet P) (hg : g.birth ∈ (parsedHierarchy Y hY).nodes g.height)
    (p : Packet P) (hp : parsedPrimitivePacket Y hY g hg = some p) (j : Fin P.k) :
    let ancestor := (parsedHierarchy Y hY).ancestor
      (g.hierarchyBirth (parsedHierarchy Y hY) hg) j.val
    (p.mask j ↔ P.InPrincipal ancestor.2.val ancestor.1 g.carrier) ∧
      (p.mask j → decode p j = some (parsedState Y hY ancestor)) := by
  sorry

/-- R13, V4 3.13: slots outside the actual principal set are ABSENT, as
required by the one-state packet decoder; this is the other direction of W4. -/
theorem calibration_W4_absent (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Parser.BornFacet P) (hg : g.birth ∈ (parsedHierarchy Y hY).nodes g.height)
    (p : Packet P) (hp : parsedPrimitivePacket Y hY g hg = some p) (j : Fin P.k)
    (habsent : ¬ P.InPrincipal
      ((parsedHierarchy Y hY).ancestor (g.hierarchyBirth (parsedHierarchy Y hY) hg) j.val).2.val
      ((parsedHierarchy Y hY).ancestor (g.hierarchyBirth (parsedHierarchy Y hY) hg) j.val).1
      g.carrier) : decode p j = none := by
  sorry

end Enforce
