import Enforce.Geometry.Polyhedral

/-!
# Proper boundary complexes and Lemma 1.0

Cells need not be maximal geometric faces. Flat subdivisions and listed vertices
are allowed. Relative interiors, rather than carriers, partition the boundary.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ}

/-- G3, V4 §1.0 (H2): a finite proper boundary complex on a prototile. -/
structure CellComplex (A : PolyManifoldDomain d) where
  /-- G3, V4 §1.0 (H2): the finite list of closed flat cells. -/
  cells : Finset (Cell d)
  /-- G3, V4 §1.0 (H2): all cells have boundary dimensions. -/
  dim_lt : ∀ e ∈ cells, e.dim < d
  /-- G3, V4 §1.0 (H2)(i): distinct relative interiors are disjoint. -/
  relint_disjoint : ∀ e ∈ cells, ∀ f ∈ cells, e ≠ f →
    Disjoint (relint e.carrier) (relint f.carrier)
  /-- G3, V4 §1.0 (H2)(i): the relative interiors partition the entire frontier. -/
  cover : (⋃ e ∈ cells, relint e.carrier) = frontier A.carrier
  /-- G3, V4 §1.0 (H2)(ii): each relative boundary is a union of listed cells.
  Condition (iii) is `Cell.flat.regularClosed`. -/
  boundary_union : ∀ e ∈ cells, ∃ b : Finset (Cell d), b ⊆ cells ∧
    relfrontier e.carrier = ⋃ f ∈ b, f.carrier

namespace CellComplex

variable {A : PolyManifoldDomain d} (K : CellComplex A)

/-- G3, V4 §1.0 (H2): the `(d-1)`-cells, including flat subdivided facets. -/
def facets : Finset (Cell d) := by
  classical
  exact K.cells.filter (fun e => e.dim = d - 1)

/-- G3, V4 §1.0 (H2): the listed one-dimensional edges. -/
def edges : Finset (Cell d) := by
  classical
  exact K.cells.filter (fun e => e.dim = 1)

/-- G3, V4 §1.0 (H2): the listed vertices, including flat listed vertices. -/
def vertices : Finset (Cell d) := by
  classical
  exact K.cells.filter (fun e => e.dim = 0)

/-- G3, V4 §1.0 (H2): every frontier point belongs to exactly one relative
interior. The existence is used to define `minimalCell`, without partial choices. -/
theorem exists_unique_minimalCell (p : E d) (hp : p ∈ frontier A.carrier) :
    ∃! e : {e // e ∈ K.cells}, p ∈ relint e.val.carrier := by
  sorry

/-- G3, V4 §1.0 (H2): the unique cell whose relative interior contains `p`.
It is defined only on the frontier; the existence theorem supplies the choice. -/
def minimalCell (p : E d) (hp : p ∈ frontier A.carrier) : Cell d :=
  (Classical.choose (K.exists_unique_minimalCell p hp)).val

/-- G3, V4 §1.0 (H2): the chosen minimal cell is listed. -/
theorem minimalCell_mem (p : E d) (hp : p ∈ frontier A.carrier) :
    K.minimalCell p hp ∈ K.cells :=
  (Classical.choose (K.exists_unique_minimalCell p hp)).property

/-- G3, V4 §1.0 (H2): the defining relative-interior property. -/
theorem mem_relint_minimalCell (p : E d) (hp : p ∈ frontier A.carrier) :
    p ∈ relint (K.minimalCell p hp).carrier :=
  (Classical.choose_spec (K.exists_unique_minimalCell p hp)).1

/-- G4, V4 §1.0 (H2): descend through relative boundaries to the minimal cell. -/
theorem minimalCell_subset (p : E d) (hp : p ∈ frontier A.carrier)
    (e : Cell d) (he : e ∈ K.cells) (hpe : p ∈ e.carrier) :
    (K.minimalCell p hp).carrier ⊆ e.carrier := by
  sorry

/-- G3, V4 §1.0 (H2): the closed cell carriers also cover the frontier. -/
theorem carriers_cover : (⋃ e ∈ K.cells, e.carrier) = frontier A.carrier := by
  sorry

end CellComplex

/-- G3, V4 §1.0 (H2), 1.15: a complete nested flag of listed boundary cells.
Index zero is a vertex and index `d-1` is a facet. -/
structure CellFlag {A : PolyManifoldDomain d} (K : CellComplex A) where
  /-- G3, V4 1.15: cell at each dimension. -/
  cell : Fin d → Cell d
  /-- G3, V4 1.15: all cells are listed. -/
  mem : ∀ j, cell j ∈ K.cells
  /-- G3, V4 1.15: dimensions are exact. -/
  dimension : ∀ j, (cell j).dim = j.val
  /-- G3, V4 1.15: cells in increasing order are nested. -/
  nested : ∀ i j, i ≤ j → (cell i).carrier ⊆ (cell j).carrier

/-- G6, V4 1.0(a): near a relative-interior facet point, the frontier and the
facet agree with their affine hyperplane, and the domain is a closed half-ball.
The normal may point to either side, so no orientation is imposed. -/
theorem facet_halfball [Fact (2 ≤ d)] (A : PolyManifoldDomain d) (K : CellComplex A)
    (F : Cell d) (hF : F ∈ K.facets) (p : E d) (hp : p ∈ relint F.carrier) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : E d, ‖v‖ = 1 ∧
      frontier A.carrier ∩ ball p r =
        (affineSpan ℝ F.carrier : Set (E d)) ∩ ball p r ∧
      F.carrier ∩ ball p r = (affineSpan ℝ F.carrier : Set (E d)) ∩ ball p r ∧
      A.carrier ∩ ball p r = {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p r := by
  sorry

/-- Step 1 of the V4 proof of `solidAngle_constant_on_cell` (V4 1.0(a)):
"each component is inside or outside A". On a connected set on which boundary
membership is constant, membership in a closed set is constant as well. -/
private lemma solidAngle_constant_on_cell_step1_connected_membership
    {X : Type*} [TopologicalSpace X] {S T : Set X}
    (hS : IsClosed S) (hT : IsPreconnected T)
    (hb : ∀ x ∈ T, ∀ y ∈ T, x ∈ frontier S ↔ y ∈ frontier S)
    {x y : X} (hx : x ∈ T) (hy : y ∈ T) : x ∈ S ↔ y ∈ S := by
  by_cases hxb : x ∈ frontier S
  · exact iff_of_true (hS.frontier_subset hxb) (hS.frontier_subset ((hb x hx y hy).mp hxb))
  have havoid : ∀ z ∈ T, z ∉ frontier S := by
    intro z hz hzb
    exact hxb ((hb x hx z hz).mpr hzb)
  have hcover : T ⊆ interior S ∪ Sᶜ := by
    intro z hz
    by_cases hzs : z ∈ S
    · left
      by_contra hzi
      exact havoid z hz (by rw [hS.frontier_eq]; exact ⟨hzs, hzi⟩)
    · exact Or.inr hzs
  have hdis : Disjoint (interior S) Sᶜ :=
    Set.disjoint_left.mpr fun _ hi hc => hc (interior_subset hi)
  rcases hT.subset_or_subset isOpen_interior hS.isOpen_compl hdis hcover with h | h
  · exact iff_of_true (interior_subset (h hx)) (interior_subset (h hy))
  · exact iff_of_false (h hx) (h hy)

/-- Step 2 of the V4 proof of `solidAngle_constant_on_cell` (V4 1.0(b)):
"the local structure is constant by (a) applied to the cell complex". Translation
invariance of the relative boundary of a closed set extends to the set itself,
provided the translations are parallel to its affine span. -/
private lemma solidAngle_constant_on_cell_step2_fill
    {S : Set (E d)} (hS : IsClosed S) (V : Submodule ℝ (E d))
    (hV : V ≤ (affineSpan ℝ S).direction) (p : E d) (r : ℝ)
    (hb : ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V →
      (x ∈ relfrontier S ↔ y ∈ relfrontier S)) :
    ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V → (x ∈ S ↔ y ∈ S) := by
  have hforward : ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V → x ∈ S → y ∈ S := by
    intro x hx y hy hyx hxs
    have hxaff : x ∈ affineSpan ℝ S := subset_affineSpan ℝ S hxs
    let γ : ℝ → affineSpan ℝ S := fun t =>
      ⟨t • (y - x) + x,
        AffineSubspace.vadd_mem_of_mem_direction
          ((affineSpan ℝ S).direction.smul_mem t (hV hyx)) hxaff⟩
    have hγcont : Continuous γ := by
      apply Continuous.subtype_mk
      fun_prop
    have hγball : ∀ t ∈ Icc (0 : ℝ) 1, (γ t : E d) ∈ ball p r := by
      intro t ht
      have hseg : (γ t : E d) ∈ segment ℝ x y := by
        rw [segment_eq_image_lineMap]
        exact ⟨t, ht, rfl⟩
      exact (convex_ball p r).segment_subset hx hy hseg
    have hfront (z : affineSpan ℝ S) :
        z ∈ frontier ((↑) ⁻¹' S : Set (affineSpan ℝ S)) ↔ (z : E d) ∈ relfrontier S := by
      change _ ↔ (z : E d) ∈ Subtype.val '' frontier _
      exact (Subtype.val_injective.mem_set_image).symm
    have hinv : ∀ a ∈ γ '' Icc (0 : ℝ) 1, ∀ b ∈ γ '' Icc (0 : ℝ) 1,
        a ∈ frontier ((↑) ⁻¹' S : Set (affineSpan ℝ S)) ↔
        b ∈ frontier ((↑) ⁻¹' S : Set (affineSpan ℝ S)) := by
      rintro a ⟨s, hs, rfl⟩ b ⟨t, ht, rfl⟩
      rw [hfront, hfront]
      apply hb _ (hγball s hs) _ (hγball t ht)
      change (t • (y - x) + x) - (s • (y - x) + x) ∈ V
      simpa only [add_sub_add_right_eq_sub] using
        V.sub_mem (V.smul_mem t hyx) (V.smul_mem s hyx)
    have heq := solidAngle_constant_on_cell_step1_connected_membership
      (hS.preimage continuous_subtype_val)
      (isPreconnected_Icc.image γ hγcont.continuousOn) hinv
      (mem_image_of_mem γ (left_mem_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)))
      (mem_image_of_mem γ (right_mem_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)))
    simpa [γ] using heq.mp (by simpa [γ] using hxs)
  intro x hx y hy hyx
  exact ⟨hforward x hx y hy hyx,
    hforward y hy x hx (by simpa only [neg_sub] using V.neg_mem hyx)⟩

/-- Step 3 of the V4 proof of `solidAngle_constant_on_cell` (V4 1.0(a)):
"if p ∈ e ... then mc_A(p) ⊆ e". A listed cell meeting the relative interior
of another listed cell contains the whole latter cell. -/
private lemma solidAngle_constant_on_cell_step3_incidence
    {A : PolyManifoldDomain d} (K : CellComplex A)
    {e f : Cell d} (he : e ∈ K.cells) (hf : f ∈ K.cells)
    {p : E d} (hp : p ∈ relint e.carrier) (hpf : p ∈ f.carrier) :
    e.carrier ⊆ f.carrier := by
  have hpA : p ∈ frontier A.carrier := by
    rw [← K.cover]
    exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨he, hp⟩⟩
  have hmin : K.minimalCell p hpA = e := by
    by_contra hne
    exact Set.disjoint_left.mp
      (K.relint_disjoint _ (K.minimalCell_mem p hpA) e he hne)
      (K.mem_relint_minimalCell p hpA) hp
  simpa only [hmin] using K.minimalCell_subset p hpA f hf hpf

/-- Step 4 of the V4 proof of `solidAngle_constant_on_cell` (V4 1.0(a)):
"Cells are closed and finitely many, so some ball U ...". Finitely many local
translation invariances hold on a common ball, including for an empty family. -/
private lemma solidAngle_constant_on_cell_step4_common_ball
    {ι : Type*} (s : Finset ι) (C : ι → Set (E d))
    (V : Submodule ℝ (E d)) (p : E d)
    (h : ∀ i ∈ s, ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V → (x ∈ C i ↔ y ∈ C i)) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s,
      ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V → (x ∈ C i ↔ y ∈ C i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨ra, hra, hca⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨rs, hrs, hcs⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨min ra rs, lt_min hra hrs, ?_⟩
    intro i hi x hx y hy hv
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hca x (ball_subset_ball (min_le_left _ _) hx)
        y (ball_subset_ball (min_le_left _ _) hy) hv
    · exact hcs i hi x (ball_subset_ball (min_le_right _ _) hx)
        y (ball_subset_ball (min_le_right _ _) hy) hv

/-- Step 5 of the V4 proof of `solidAngle_constant_on_cell` (V4 1.0(b)):
"the local structure is constant by (a) applied to the cell complex". Induction
through relative boundaries makes every listed carrier locally invariant in the
directions of the cell containing the base point in its relative interior. -/
private lemma solidAngle_constant_on_cell_step5_cell_invariance
    {A : PolyManifoldDomain d} (K : CellComplex A) (e : Cell d) (he : e ∈ K.cells)
    (p : E d) (hp : p ∈ relint e.carrier) (f : Cell d) (hf : f ∈ K.cells) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
      y - x ∈ cellDirection e.carrier → (x ∈ f.carrier ↔ y ∈ f.carrier) := by
  classical
  let N (f : Cell d) := (K.cells.filter fun g => g.carrier ⊆ f.carrier).card
  have main : ∀ n : ℕ, ∀ f : Cell d, f ∈ K.cells → N f = n →
      ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
        y - x ∈ cellDirection e.carrier → (x ∈ f.carrier ↔ y ∈ f.carrier) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf hN
      by_cases hpf : p ∈ f.carrier
      · have hef := solidAngle_constant_on_cell_step3_incidence K he hf hp hpf
        have hV : cellDirection e.carrier ≤ (affineSpan ℝ f.carrier).direction :=
          AffineSubspace.direction_le (affineSpan_mono ℝ hef)
        obtain ⟨b, hb, hboundary⟩ := K.boundary_union f hf
        have hsmall : ∀ g ∈ b, N g < N f := by
          intro g hg
          have hgb : g.carrier ⊆ relfrontier f.carrier := by
            intro z hz
            rw [hboundary]
            exact mem_iUnion.mpr ⟨g, mem_iUnion.mpr ⟨hg, hz⟩⟩
          have hgf : g.carrier ⊆ f.carrier :=
            hgb.trans (intrinsicFrontier_subset f.flat.compact.isClosed)
          have hnfg : ¬ f.carrier ⊆ g.carrier := by
            intro hfg
            obtain ⟨z, hz⟩ := f.flat.relint_nonempty
            have hzb := hgb (hfg (intrinsicInterior_subset hz))
            change z ∈ intrinsicFrontier ℝ f.carrier at hzb
            rw [← closure_diff_intrinsicInterior] at hzb
            exact hzb.2 hz
          apply Finset.card_lt_card
          apply (Finset.ssubset_iff_of_subset ?_).mpr
          · refine ⟨f, Finset.mem_filter.mpr ⟨hf, Subset.rfl⟩, ?_⟩
            intro hfg
            exact hnfg (Finset.mem_filter.mp hfg).2
          · intro g' hg'
            obtain ⟨hg'K, hg'g⟩ := Finset.mem_filter.mp hg'
            exact Finset.mem_filter.mpr ⟨hg'K, hg'g.trans hgf⟩
        obtain ⟨r, hr, hc⟩ := solidAngle_constant_on_cell_step4_common_ball b
          Cell.carrier (cellDirection e.carrier) p (fun g hg =>
            ih (N g) (by simpa only [hN] using hsmall g hg) g (hb hg) rfl)
        refine ⟨r, hr, solidAngle_constant_on_cell_step2_fill f.flat.compact.isClosed
          (cellDirection e.carrier) hV p r ?_⟩
        intro x hx y hy hv
        rw [hboundary]
        simp only [mem_iUnion, exists_prop]
        constructor
        · rintro ⟨g, hg, hxg⟩
          exact ⟨g, hg, (hc g hg x hx y hy hv).mp hxg⟩
        · rintro ⟨g, hg, hyg⟩
          exact ⟨g, hg, (hc g hg x hx y hy hv).mpr hyg⟩
      · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp f.flat.compact.isClosed.isOpen_compl p hpf
        exact ⟨r, hr, fun x hx y hy _ => iff_of_false (hball hx) (hball hy)⟩
  exact main (N f) f hf rfl

/-- Step 6 of the V4 proof of `solidAngle_constant_on_cell` (V4 1.0(a)):
"each component is inside or outside A". A segment parallel to a locally
translation-invariant frontier stays either on that frontier or on one side. -/
private lemma solidAngle_constant_on_cell_step6_ambient_fill
    {S : Set (E d)} (hS : IsClosed S) (V : Submodule ℝ (E d)) (p : E d) (r : ℝ)
    (hb : ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V →
      (x ∈ frontier S ↔ y ∈ frontier S)) :
    ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V → (x ∈ S ↔ y ∈ S) := by
  intro x hx y hy hv
  have hseg : segment ℝ x y ⊆ ball p r := (convex_ball p r).segment_subset hx hy
  apply solidAngle_constant_on_cell_step1_connected_membership hS
    (convex_segment x y).isPreconnected ?_ (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  intro a ha b hb'
  apply hb a (hseg ha) b (hseg hb')
  rw [segment_eq_image_lineMap] at ha hb'
  obtain ⟨s, _, rfl⟩ := ha
  obtain ⟨t, _, rfl⟩ := hb'
  simpa only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
    add_sub_add_right_eq_sub] using V.sub_mem (V.smul_mem t hv) (V.smul_mem s hv)

/-- Step 7 of the V4 proof of `solidAngle_constant_on_cell` (V4 1.0(b)):
"along relint of a cell the local structure is constant". Combine the finitely
many carrier germs covering the frontier, and then fill the closed domain. -/
private lemma solidAngle_constant_on_cell_step7_domain_invariance
    {A : PolyManifoldDomain d} (K : CellComplex A) (e : Cell d) (he : e ∈ K.cells)
    (p : E d) (hp : p ∈ relint e.carrier) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
      y - x ∈ cellDirection e.carrier → (x ∈ A.carrier ↔ y ∈ A.carrier) := by
  have hcover : (⋃ f ∈ K.cells, f.carrier) = frontier A.carrier := by
    apply Subset.antisymm
    · simp only [iUnion_subset_iff]
      intro f hf
      rw [← f.flat.regularClosed]
      apply closure_minimal ?_ isClosed_frontier
      intro x hx
      rw [← K.cover]
      exact mem_iUnion.mpr ⟨f, mem_iUnion.mpr ⟨hf, hx⟩⟩
    · rw [← K.cover]
      intro x hx
      obtain ⟨f, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hf, hx⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨f, mem_iUnion.mpr ⟨hf, intrinsicInterior_subset hx⟩⟩
  obtain ⟨r, hr, hc⟩ := solidAngle_constant_on_cell_step4_common_ball K.cells
    Cell.carrier (cellDirection e.carrier) p
    (solidAngle_constant_on_cell_step5_cell_invariance K e he p hp)
  refine ⟨r, hr, solidAngle_constant_on_cell_step6_ambient_fill A.compact.isClosed
    (cellDirection e.carrier) p r ?_⟩
  intro x hx y hy hv
  rw [← hcover]
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨f, hf, hxf⟩
    exact ⟨f, hf, (hc f hf x hx y hy hv).mp hxf⟩
  · rintro ⟨f, hf, hyf⟩
    exact ⟨f, hf, (hc f hf x hx y hy hv).mpr hyf⟩

open scoped Topology in
/-- Step 8 of the V4 proof of `solidAngle_constant_on_cell` (V4 1.0(b)):
"the local structure is constant". Equal translated germs give equal radial
tangent cones; only sufficiently short positive portions of each ray matter. -/
private lemma solidAngle_constant_on_cell_step8_tangent_germ
    (S : Set (E d)) (V : Submodule ℝ (E d)) (p q : E d)
    (r : ℝ) (hr : 0 < r) (hq : q ∈ ball p r) (hv : q - p ∈ V)
    (hloc : ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V → (x ∈ S ↔ y ∈ S)) :
    tangentCone S p = tangentCone S q := by
  ext v
  have hnear (a : E d) (ha : a ∈ ball p r) :
      ∀ᶠ t : ℝ in 𝓝 0, a + t • v ∈ ball p r := by
    have hc : Continuous (fun t : ℝ => a + t • v) := by fun_prop
    have ht : Filter.Tendsto (fun t : ℝ => a + t • v) (𝓝 0) (𝓝 a) := by
      simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
    exact ht.eventually (isOpen_ball.mem_nhds ha)
  obtain ⟨δ, hδ, hδnear⟩ := Metric.eventually_nhds_iff.mp
    ((hnear p (mem_ball_self hr)).and (hnear q hq))
  have heq (t : ℝ) (ht : 0 < t) (htδ : t < δ) :
      p + t • v ∈ S ↔ q + t • v ∈ S := by
    have hdist : dist t 0 < δ := by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using htδ
    have hpair := hδnear hdist
    apply hloc _ hpair.1 _ hpair.2
    simpa only [add_sub_add_right_eq_sub] using hv
  constructor
  · rintro ⟨ε, hε, hεray⟩
    refine ⟨min ε δ, lt_min hε hδ, fun t ht htεδ => ?_⟩
    exact (heq t ht (lt_of_lt_of_le htεδ (min_le_right _ _))).mp
      (hεray t ht (lt_of_lt_of_le htεδ (min_le_left _ _)))
  · rintro ⟨ε, hε, hεray⟩
    refine ⟨min ε δ, lt_min hε hδ, fun t ht htεδ => ?_⟩
    exact (heq t ht (lt_of_lt_of_le htεδ (min_le_right _ _))).mpr
      (hεray t ht (lt_of_lt_of_le htεδ (min_le_left _ _)))

/-- G7, V4 1.0(b): the solid angle depends only on the minimal cell. -/
theorem solidAngle_constant_on_cell [Fact (2 ≤ d)] (A : PolyManifoldDomain d)
    (K : CellComplex A) (e : Cell d) (he : e ∈ K.cells) (p q : E d)
    (hp : p ∈ relint e.carrier) (hq : q ∈ relint e.carrier) :
    solidAngle (tangentCone A.carrier p) = solidAngle (tangentCone A.carrier q) := by
  have hloc : IsLocallyConstant (fun x : relint e.carrier => tangentCone A.carrier x) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    obtain ⟨r, hr, hball⟩ :=
      solidAngle_constant_on_cell_step7_domain_invariance K e he x x.property
    have hnear : ∀ᶠ y : relint e.carrier in nhds x, (y : E d) ∈ ball (x : E d) r :=
      continuous_subtype_val.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hnear] with y hy
    apply (solidAngle_constant_on_cell_step8_tangent_germ A.carrier
      (cellDirection e.carrier) x y r hr hy ?_ hball).symm
    exact AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ e.carrier (intrinsicInterior_subset y.property))
      (subset_affineSpan ℝ e.carrier (intrinsicInterior_subset x.property))
  have hconn : IsPreconnected (univ : Set (relint e.carrier)) :=
    (Subtype.preconnectedSpace e.flat.relint_connected.isPreconnected).isPreconnected_univ
  exact congrArg solidAngle (hloc.apply_eq_of_isPreconnected hconn
    (x := ⟨p, hp⟩) (y := ⟨q, hq⟩) (mem_univ _) (mem_univ _))

/-- G7, V4 1.0(b): the catalogue of boundary solid angles, indexed geometrically
by relative interiors of listed cells. It is a set of real numbers, not a choice
of representative points or an enumeration with repetitions. -/
def boundaryAngles {ι : Type*} (proto : ι → PolyManifoldDomain d)
    (cx : ∀ A, CellComplex (proto A)) : Set ℝ :=
  {θ | ∃ (A : ι) (e : Cell d), e ∈ (cx A).cells ∧
    ∃ p ∈ relint e.carrier, θ = solidAngle (tangentCone (proto A).carrier p)}

/-- G7, V4 1.0(b): finitely many boundary angles, all strictly positive. -/
theorem boundaryAngles_finite [Fact (2 ≤ d)] {ι : Type*} [Fintype ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) :
    (boundaryAngles proto cx).Finite ∧
      ∀ θ ∈ boundaryAngles proto cx, 0 < θ := by
  sorry

/-- G7, V4 1.0(b): the paper's `β` is the positive minimum of the finite
angle catalogue. The nonempty type catalogue supplies an actual boundary cell;
the separate uniform-bound theorem also handles an empty catalogue. -/
theorem minimum_solidAngle [Fact (2 ≤ d)] {ι : Type*} [Fintype ι] [Nonempty ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) :
    ∃ β : ℝ, IsLeast (boundaryAngles proto cx) β ∧ 0 < β := by
  sorry

/-- G7, V4 1.0(b): the actual minimum `β` of the finite boundary-angle catalogue.
The preceding existence lemma supplies the choice; the definition has no proof hole. -/
def minimumAngle [Fact (2 ≤ d)] {ι : Type*} [Fintype ι] [Nonempty ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) : ℝ :=
  Classical.choose (minimum_solidAngle proto cx)

/-- G7, V4 1.0(b): the chosen angle is the least catalogue element and is positive. -/
theorem minimumAngle_spec [Fact (2 ≤ d)] {ι : Type*} [Fintype ι] [Nonempty ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) :
    IsLeast (boundaryAngles proto cx) (minimumAngle proto cx) ∧
      0 < minimumAngle proto cx :=
  Classical.choose_spec (minimum_solidAngle proto cx)

/-- G7, V4 1.0(b): the paper's exact numerical bound `M₀ = floor (ω_d / β)`. -/
def multiplicityBound [Fact (2 ≤ d)] {ι : Type*} [Fintype ι] [Nonempty ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) : ℕ :=
  ⌊fullSolidAngle d / minimumAngle proto cx⌋₊

/-- G7, V4 1.0(b): the common-point bound using precisely the minimum-angle
constant, rather than an arbitrary positive lower estimate for the angles. -/
theorem point_count_le [Fact (2 ≤ d)] {ι : Type*} [Fintype ι] [Nonempty ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A))
    {α : Type*} (ty : α → ι) (φ : α → Iso d)
    (hdisjoint : Pairwise (fun a b => Disjoint
      (interior (placedSet (φ a) (proto (ty a)).carrier))
      (interior (placedSet (φ b) (proto (ty b)).carrier)))) (p : E d) :
    {a | p ∈ placedSet (φ a) (proto (ty a)).carrier}.Finite ∧
      Set.ncard {a | p ∈ placedSet (φ a) (proto (ty a)).carrier} ≤
        multiplicityBound proto cx := by
  sorry

/-- G7, V4 1.0(b): a uniform positive lower bound for angles at boundary cells.
The conclusion also covers an empty prototile catalogue (any positive bound works). -/
theorem uniform_solidAngle [Fact (2 ≤ d)] {ι : Type*} [Fintype ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) :
    ∃ β : ℝ, 0 < β ∧ β ≤ fullSolidAngle d ∧
      ∀ A e, e ∈ (cx A).cells → ∀ p ∈ relint e.carrier,
        β ≤ solidAngle (tangentCone (proto A).carrier p) := by
  sorry

/-- G7, V4 1.0(b): at most `floor (ω_d / β)` disjoint placed prototiles
contain any one point. This includes points in the interiors of prototiles. -/
theorem point_multiplicity_bound [Fact (2 ≤ d)] {ι : Type*} [Fintype ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) :
    ∃ β : ℝ, 0 < β ∧ β ≤ fullSolidAngle d ∧
      (∀ A e, e ∈ (cx A).cells → ∀ p ∈ relint e.carrier,
        β ≤ solidAngle (tangentCone (proto A).carrier p)) ∧
      ∀ (α : Type) (ty : α → ι) (φ : α → Iso d),
        Pairwise (fun a b => Disjoint
          (interior (placedSet (φ a) (proto (ty a)).carrier))
          (interior (placedSet (φ b) (proto (ty b)).carrier))) →
        ∀ p : E d, {a | p ∈ placedSet (φ a) (proto (ty a)).carrier}.Finite ∧
          Set.ncard {a | p ∈ placedSet (φ a) (proto (ty a)).carrier} ≤
            ⌊fullSolidAngle d / β⌋₊ := by
  sorry

/-- G8, V4 1.0(c): a family of placed prototiles with pairwise disjoint
interiors is locally finite, and every bounded set meets only finitely many. -/
theorem locallyFinite_disjointInteriors {ι : Type*} [Fintype ι]
    (proto : ι → PolyManifoldDomain d) {α : Type*} (ty : α → ι) (φ : α → Iso d)
    (hdisjoint : Pairwise (fun a b => Disjoint
      (interior (placedSet (φ a) (proto (ty a)).carrier))
      (interior (placedSet (φ b) (proto (ty b)).carrier)))) :
    LocallyFinite (fun a => placedSet (φ a) (proto (ty a)).carrier) ∧
      ∀ B : Set (E d), Bornology.IsBounded B →
        {a | (B ∩ placedSet (φ a) (proto (ty a)).carrier).Nonempty}.Finite := by
  sorry

/-- G9, V4 1.16(b): one closed side of a codimension-one pair `W ≤ V`.
The kernel condition determines the wall inside `V`, not in all of `E`. -/
def IsClosedSide (dirs : Set (Submodule ℝ (E d))) (K : Set (E d)) : Prop :=
  ∃ V W : Submodule ℝ (E d), (V ∈ dirs ∨ V = ⊤) ∧ (W ∈ dirs ∨ W = ⊤) ∧
    W ≤ V ∧ Module.finrank ℝ V = Module.finrank ℝ W + 1 ∧
    ∃ ℓ : E d →ₗ[ℝ] ℝ, {x | x ∈ V ∧ ℓ x = 0} = (W : Set (E d)) ∧
      K = {x | x ∈ V ∧ 0 ≤ ℓ x}

/-- G9, V4 1.16(b): finite unions of finite intersections of allowed subspaces
and closed sides. Supply `Π = HΠ` from the substitution rotation group. -/
def HPiCone (dirs : Set (Submodule ℝ (E d))) (K : Set (E d)) : Prop :=
  ∃ s : Finset (Finset (Set (E d))), K = (⋃ p ∈ s, ⋂ C ∈ p, C) ∧
    ∀ p ∈ s, ∀ C ∈ p,
      (∃ V : Submodule ℝ (E d), (V ∈ dirs ∨ V = ⊤) ∧ C = (V : Set (E d))) ∨
        IsClosedSide dirs C

end Enforce
