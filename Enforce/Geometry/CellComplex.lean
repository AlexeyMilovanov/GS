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

/-- Step 1 of the V4 proof of `point_count_le` (V4 1.0(b)): "Disjoint interiors of
tiles give disjoint interiors of tangent cones at a common point" uses the tangent
cones of *placed* tiles. Placing by an isometry pulls the tangent cone back along
the linear part of the inverse isometry. -/
private lemma point_count_le_step1_tangentCone_placed (K : Set (E d)) (φ : Iso d)
    (p : E d) :
    tangentCone (placedSet φ K) p =
      φ.symm.linearIsometryEquiv ⁻¹' tangentCone K (φ.symm p) := by
  have key : ∀ (t : ℝ) (v : E d), p + t • v ∈ placedSet φ K ↔
      φ.symm p + t • φ.symm.linearIsometryEquiv v ∈ K := by
    intro t v
    have hsymm : φ.symm (p + t • v) = φ.symm p + t • φ.symm.linearIsometryEquiv v := by
      have h := φ.symm.map_vadd p (t • v)
      simp only [vadd_eq_add, map_smul] at h
      rw [add_comm p, h, add_comm]
    rw [← hsymm]
    constructor
    · rintro ⟨x, hx, hxe⟩
      rw [← hxe, φ.symm_apply_apply]
      exact hx
    · intro h
      exact ⟨_, h, φ.apply_symm_apply _⟩
  ext v
  simp only [tangentCone, mem_preimage, mem_setOf_eq, key]

open private tangentCone_polyhedral_step2_halfspace_presentation
  tangentCone_polyhedral_step3_local_cone tangentCone_polyhedral_step5_radial_germ
  from Enforce.Geometry.Polyhedral in
/-- Step 2 of the V4 proof of `point_count_le` (V4 1.0(b)): "`A` is a polyhedron, so
its tangent cone at any point is a polyhedral cone". The radial tangent cone of a
prototile at any point is a finite union of closed convex cones, hence closed. -/
private lemma point_count_le_step2_cone_closed (A : PolyManifoldDomain d) (x : E d) :
    IsClosed (tangentCone A.carrier x) := by
  obtain ⟨S, hS⟩ := tangentCone_polyhedral_step2_halfspace_presentation A.polyhedral
  obtain ⟨C, hC, hloc⟩ := tangentCone_polyhedral_step3_local_cone S x
  rw [← hS] at hloc
  rw [tangentCone_polyhedral_step5_radial_germ x hC hloc]
  obtain ⟨s, rfl⟩ := hC
  refine isClosed_biUnion_finset fun q _ => ?_
  have : {v : E d | ∀ ℓ ∈ q, 0 ≤ ℓ v} = ⋂ ℓ ∈ q, {v | 0 ≤ ℓ v} := by
    ext v; simp
  rw [this]
  exact isClosed_biInter fun ℓ _ =>
    isClosed_le continuous_const ℓ.continuous_of_finiteDimensional

/-- Step 2' of the V4 proof of `point_count_le` (V4 1.0(b)): the tangent cone of a
placed prototile is closed, hence (null-)measurable. -/
private lemma point_count_le_step2_cone_measurable (A : PolyManifoldDomain d) (φ : Iso d)
    (p : E d) :
    MeasureTheory.NullMeasurableSet (tangentCone (placedSet φ A.carrier) p) := by
  rw [point_count_le_step1_tangentCone_placed]
  exact ((point_count_le_step2_cone_closed A _).preimage
    φ.symm.linearIsometryEquiv.continuous).measurableSet.nullMeasurableSet

/-- Step 2'' of the V4 proof of `point_count_le` (V4 1.0(b)): "the solid angle"
is invariant under the isometric placement of a prototile. -/
private lemma point_count_le_step2_solidAngle_placed (A : PolyManifoldDomain d)
    (φ : Iso d) (p : E d) :
    solidAngle (tangentCone (placedSet φ A.carrier) p) =
      solidAngle (tangentCone A.carrier (φ.symm p)) := by
  rw [point_count_le_step1_tangentCone_placed]
  unfold solidAngle
  congr 2
  set L := φ.symm.linearIsometryEquiv
  have hball : L ⁻¹' ball (0 : E d) 1 = ball 0 1 := by
    ext v; simp [L]
  conv_lhs => rw [← hball, ← preimage_inter]
  exact (L.measurePreserving).measure_preimage
    (((point_count_le_step2_cone_closed A _).measurableSet.inter
      measurableSet_ball).nullMeasurableSet)

/-- Step 3 of the V4 proof of `point_count_le` (V4 1.0(b)): "its solid angle depends
only on `mc_A(p)`, and `β := min` over all prototiles and cells". At a point of a
prototile the tangent cone has solid angle at least `β`: at a frontier point it is
a catalogue angle (relative interior of the minimal cell); at an interior point the
cone is everything, of full angle `ω_d ≥ β`. -/
private lemma point_count_le_step3_angle_lower [Fact (2 ≤ d)] {ι : Type*} [Fintype ι]
    [Nonempty ι] (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A))
    (A : ι) (x : E d) (hx : x ∈ (proto A).carrier) :
    minimumAngle proto cx ≤ solidAngle (tangentCone (proto A).carrier x) := by
  have hspec := (minimumAngle_spec proto cx).1
  by_cases hfr : x ∈ frontier (proto A).carrier
  · apply hspec.2
    exact ⟨A, (cx A).minimalCell x hfr, (cx A).minimalCell_mem x hfr,
      x, (cx A).mem_relint_minimalCell x hfr, rfl⟩
  · have hint : x ∈ interior (proto A).carrier := by
      rw [frontier, mem_diff, not_and, not_not] at hfr
      exact hfr (subset_closure hx)
    have huniv : tangentCone (proto A).carrier x = univ := by
      ext v
      simp only [mem_univ, iff_true]
      obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.mp isOpen_interior x hint
      refine ⟨r / (‖v‖ + 1), by positivity, fun t ht htr => interior_subset (hrb ?_)⟩
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
      have h1 : t * ‖v‖ ≤ t * (‖v‖ + 1) := by nlinarith
      have h2 : t * (‖v‖ + 1) < r := by
        rwa [lt_div_iff₀ (by positivity)] at htr
      linarith
    obtain ⟨B, e, he, y, hy, heq⟩ := hspec.1
    rw [heq, huniv]
    unfold solidAngle
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    exact ENNReal.toReal_mono (by simpa using (MeasureTheory.measure_ball_lt_top (μ := MeasureTheory.volume) (x := (0 : E d)) (r := 1)).ne)
      (MeasureTheory.measure_mono (by simp))

open private tangentCone_polyhedral_step2_halfspace_presentation
  tangentCone_polyhedral_step3_local_cone tangentCone_polyhedral_step5_radial_germ
  from Enforce.Geometry.Polyhedral in
/-- Step 4a of the V4 proof of `point_count_le` (V4 1.0(b)): "`A` is a polyhedron, so
its tangent cone at any point is a polyhedral cone". A finite union of closed convex
cones has null boundary, since each convex piece has null boundary. -/
private lemma point_count_le_step4a_cone_frontier_null (A : PolyManifoldDomain d)
    (x : E d) : MeasureTheory.volume (frontier (tangentCone A.carrier x)) = 0 := by
  obtain ⟨S, hS⟩ := tangentCone_polyhedral_step2_halfspace_presentation A.polyhedral
  obtain ⟨C, hC, hloc⟩ := tangentCone_polyhedral_step3_local_cone S x
  rw [← hS] at hloc
  rw [tangentCone_polyhedral_step5_radial_germ x hC hloc]
  obtain ⟨s, rfl⟩ := hC
  refine MeasureTheory.measure_mono_null
    (t := ⋃ q ∈ s, frontier {v : E d | ∀ ℓ ∈ q, 0 ≤ ℓ v}) ?_ ?_
  · intro v hv
    have h1 : v ∈ ⋃ q ∈ s, closure {v : E d | ∀ ℓ ∈ q, 0 ≤ ℓ v} :=
      (Finset.closure_biUnion s _).subset hv.1
    obtain ⟨q, hq, hvq⟩ := mem_iUnion₂.mp h1
    refine mem_iUnion₂.mpr ⟨q, hq, hvq, fun hint => hv.2 ?_⟩
    exact interior_mono (fun w hw => mem_iUnion₂.mpr ⟨q, hq, hw⟩) hint
  · refine le_antisymm ((MeasureTheory.measure_biUnion_finset_le s _).trans ?_) (zero_le _)
    refine (Finset.sum_eq_zero fun q _ => ?_).le
    refine Convex.addHaar_frontier _ ?_
    intro a ha b hb α β hα hβ _
    show ∀ ℓ ∈ q, 0 ≤ ℓ (α • a + β • b)
    intro ℓ hℓ
    rw [map_add, map_smul, map_smul]
    exact add_nonneg (smul_nonneg hα (ha ℓ hℓ)) (smul_nonneg hβ (hb ℓ hℓ))

/-- Step 4b of the V4 proof of `point_count_le` (V4 1.0(b)): the boundary of the
tangent cone of a placed prototile is null (isometric pull-back of Step 4a). -/
private lemma point_count_le_step4b_placed_frontier_null (A : PolyManifoldDomain d)
    (φ : Iso d) (p : E d) :
    MeasureTheory.volume (frontier (tangentCone (placedSet φ A.carrier) p)) = 0 := by
  rw [point_count_le_step1_tangentCone_placed]
  set L := φ.symm.linearIsometryEquiv
  have hfr : frontier (L ⁻¹' tangentCone A.carrier (φ.symm p)) =
      L ⁻¹' frontier (tangentCone A.carrier (φ.symm p)) :=
    (L.toHomeomorph.preimage_frontier _).symm
  rw [hfr, (L.measurePreserving).measure_preimage
    isClosed_frontier.measurableSet.nullMeasurableSet]
  exact point_count_le_step4a_cone_frontier_null A _

open private tangentCone_polyhedral_step2_halfspace_presentation
  tangentCone_polyhedral_step3_local_cone tangentCone_polyhedral_step4_positive_scaling
  tangentCone_polyhedral_step5_radial_germ from Enforce.Geometry.Polyhedral in
/-- Step 4c(i) of the V4 proof of `point_count_le` (V4 1.0(b)): "Near `p` each
polyhedron coincides with `p` plus its tangent cone". Hence an interior direction of
the tangent cone of a prototile at `q` points into the interior of the prototile for
all small positive times. -/
private lemma point_count_le_step4c_interior_ray (A : PolyManifoldDomain d) (q v : E d)
    (hv : v ∈ interior (tangentCone A.carrier q)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → q + t • v ∈ interior A.carrier := by
  obtain ⟨S, hS⟩ := tangentCone_polyhedral_step2_halfspace_presentation A.polyhedral
  obtain ⟨C, hC, hloc⟩ := tangentCone_polyhedral_step3_local_cone S q
  rw [← hS] at hloc
  rw [tangentCone_polyhedral_step5_radial_germ q hC hloc] at hv
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hloc
  obtain ⟨η, hη, hηC⟩ := Metric.isOpen_iff.mp isOpen_interior v hv
  refine ⟨δ / (‖v‖ + η), by positivity, fun t ht htε => ?_⟩
  have htε' : t * (‖v‖ + η) < δ := by
    rwa [lt_div_iff₀ (by positivity)] at htε
  rw [mem_interior]
  refine ⟨ball (q + t • v) (t * η), fun y hy => ?_, isOpen_ball,
    mem_ball_self (by positivity)⟩
  rw [mem_ball, dist_eq_norm] at hy
  have hyq : dist y q < δ := by
    have h1 : dist y q ≤ ‖y - (q + t • v)‖ + ‖t • v‖ := by
      rw [dist_eq_norm]
      have : y - q = (y - (q + t • v)) + t • v := by abel
      rw [this]
      exact norm_add_le _ _
    rw [norm_smul, Real.norm_of_nonneg ht.le] at h1
    nlinarith
  refine (hball hyq).mpr ?_
  have hw : t⁻¹ • (y - q) ∈ C := by
    apply interior_subset
    apply hηC
    rw [mem_ball, dist_eq_norm]
    have : t⁻¹ • (y - q) - v = t⁻¹ • (y - (q + t • v)) := by
      rw [smul_sub (t⁻¹) y (q + t • v), smul_add, smul_smul, inv_mul_cancel₀ ht.ne',
        one_smul, smul_sub]
      abel
    rw [this, norm_smul, norm_inv, Real.norm_of_nonneg ht.le]
    rw [inv_mul_lt_iff₀ ht]
    exact hy
  have := (tangentCone_polyhedral_step4_positive_scaling hC ht (t⁻¹ • (y - q))).mpr hw
  rwa [smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at this

/-- Step 4c(ii) of the V4 proof of `point_count_le` (V4 1.0(b)): placing by an
isometry carries interior points of the prototile along the ray `q + t • L v` to
interior points of the placed tile along the ray `p + t • v`. -/
private lemma point_count_le_step4c_placed_ray (K : Set (E d)) (χ : Iso d) (p v : E d)
    (t : ℝ) (h : χ.symm p + t • χ.symm.linearIsometryEquiv v ∈ interior K) :
    p + t • v ∈ interior (placedSet χ K) := by
  have hsymm : χ.symm (p + t • v) = χ.symm p + t • χ.symm.linearIsometryEquiv v := by
    have h := χ.symm.map_vadd p (t • v)
    simp only [vadd_eq_add, map_smul] at h
    rw [add_comm p, h, add_comm]
  have hopen : IsOpen (χ '' interior K) := by
    simpa using χ.toHomeomorph.isOpenMap _ isOpen_interior
  refine (hopen.subset_interior_iff.mpr (image_mono interior_subset)) ⟨_, h, ?_⟩
  rw [← hsymm, χ.apply_symm_apply]

/-- Step 4c of the V4 proof of `point_count_le` (V4 1.0(b)): "Disjoint interiors of
tiles give disjoint interiors of tangent cones at a common point". (Near `p` each
placed polyhedron coincides with `p` plus its tangent cone, so a common interior
direction would give a common interior point of the two tiles.) -/
private lemma point_count_le_step4c_cone_interiors_disjoint (A B : PolyManifoldDomain d)
    (φ ψ : Iso d) (p : E d) (hpA : p ∈ placedSet φ A.carrier)
    (hpB : p ∈ placedSet ψ B.carrier)
    (hdisj : Disjoint (interior (placedSet φ A.carrier)) (interior (placedSet ψ B.carrier))) :
    Disjoint (interior (tangentCone (placedSet φ A.carrier) p))
      (interior (tangentCone (placedSet ψ B.carrier) p)) := by
  rw [Set.disjoint_left]
  intro v hvA hvB
  have hint (χ : Iso d) (K : Set (E d)) (hv : v ∈ interior (tangentCone (placedSet χ K) p)) :
      χ.symm.linearIsometryEquiv v ∈ interior (tangentCone K (χ.symm p)) := by
    rw [point_count_le_step1_tangentCone_placed K χ p] at hv
    change v ∈ interior (⇑(χ.symm.linearIsometryEquiv.toHomeomorph) ⁻¹'
      tangentCone K (χ.symm p)) at hv
    rw [← Homeomorph.preimage_interior] at hv
    exact hv
  obtain ⟨εA, hεA, hA⟩ := point_count_le_step4c_interior_ray A _ _ (hint φ A.carrier hvA)
  obtain ⟨εB, hεB, hB⟩ := point_count_le_step4c_interior_ray B _ _ (hint ψ B.carrier hvB)
  set t := min εA εB / 2 with ht_def
  have ht : 0 < t := by positivity
  have htA : t < εA := by have := min_le_left εA εB; linarith
  have htB : t < εB := by have := min_le_right εA εB; linarith
  exact Set.disjoint_left.mp hdisj
    (point_count_le_step4c_placed_ray A.carrier φ p v t (hA t ht htA))
    (point_count_le_step4c_placed_ray B.carrier ψ p v t (hB t ht htB))

/-- Step 4 of the V4 proof of `point_count_le` (V4 1.0(b)): "Disjoint interiors of
tiles give disjoint interiors of tangent cones at a common point". Two placed
prototiles with disjoint interiors, both containing `p`, have tangent cones at `p`
meeting only in a null set (the cones are polyhedral, so their boundaries are null,
and their interiors are disjoint). -/
private lemma point_count_le_step4_cones_aedisjoint (A B : PolyManifoldDomain d)
    (φ ψ : Iso d) (p : E d) (hpA : p ∈ placedSet φ A.carrier)
    (hpB : p ∈ placedSet ψ B.carrier)
    (hdisj : Disjoint (interior (placedSet φ A.carrier)) (interior (placedSet ψ B.carrier))) :
    MeasureTheory.volume (tangentCone (placedSet φ A.carrier) p ∩
      tangentCone (placedSet ψ B.carrier) p) = 0 := by
  have hcA := point_count_le_step1_tangentCone_placed A.carrier φ p
  have hclA : IsClosed (tangentCone (placedSet φ A.carrier) p) := by
    rw [hcA]
    exact (point_count_le_step2_cone_closed A _).preimage
      φ.symm.linearIsometryEquiv.continuous
  have hclB : IsClosed (tangentCone (placedSet ψ B.carrier) p) := by
    rw [point_count_le_step1_tangentCone_placed B.carrier ψ p]
    exact (point_count_le_step2_cone_closed B _).preimage
      ψ.symm.linearIsometryEquiv.continuous
  have hint := point_count_le_step4c_cone_interiors_disjoint A B φ ψ p hpA hpB hdisj
  refine MeasureTheory.measure_mono_null (t := frontier (tangentCone (placedSet φ A.carrier) p) ∪
    frontier (tangentCone (placedSet ψ B.carrier) p)) ?_ ?_
  · rintro v ⟨hva, hvb⟩
    by_cases hia : v ∈ interior (tangentCone (placedSet φ A.carrier) p)
    · right
      rw [hclB.frontier_eq]
      exact ⟨hvb, fun hib => hint.le_bot ⟨hia, hib⟩⟩
    · left
      rw [hclA.frontier_eq]
      exact ⟨hva, hia⟩
  · exact MeasureTheory.measure_union_null (point_count_le_step4b_placed_frontier_null A φ p)
      (point_count_le_step4b_placed_frontier_null B ψ p)

/-- Step 5 of the V4 proof of `point_count_le` (V4 1.0(b)): "Consequently at most
`M₀ := ⌊ω_d/β⌋` placed prototiles with disjoint interiors can contain a common point".
Packing: finitely many tiles through `p` give a.e.-disjoint pieces of the unit ball of
radial volume `≥ β/d` each, so their number `n` satisfies `n β ≤ ω_d`. -/
private lemma point_count_le_step5_finset_card [Fact (2 ≤ d)] {ι : Type*} [Fintype ι]
    [Nonempty ι] (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A))
    {α : Type*} (ty : α → ι) (φ : α → Iso d)
    (hdisjoint : Pairwise (fun a b => Disjoint
      (interior (placedSet (φ a) (proto (ty a)).carrier))
      (interior (placedSet (φ b) (proto (ty b)).carrier)))) (p : E d) (T : Finset α)
    (hT : ∀ a ∈ T, p ∈ placedSet (φ a) (proto (ty a)).carrier) :
    T.card ≤ multiplicityBound proto cx := by
  set C : α → Set (E d) := fun a =>
    tangentCone (placedSet (φ a) (proto (ty a)).carrier) p ∩ ball 0 1 with hC
  have hball : MeasureTheory.volume (ball (0 : E d) 1) ≠ ⊤ :=
    (MeasureTheory.measure_ball_lt_top (μ := MeasureTheory.volume)).ne
  have hfin : ∀ a, MeasureTheory.volume (C a) ≠ ⊤ := fun a =>
    ne_top_of_le_ne_top hball (MeasureTheory.measure_mono inter_subset_right)
  have hunion : MeasureTheory.volume (⋃ a ∈ T, C a) = ∑ a ∈ T, MeasureTheory.volume (C a) := by
    refine MeasureTheory.measure_biUnion_finset₀ ?_ ?_
    · intro a ha b hb hab
      have h0 := point_count_le_step4_cones_aedisjoint (proto (ty a)) (proto (ty b)) (φ a) (φ b)
        p (hT a ha) (hT b hb) (hdisjoint hab)
      show MeasureTheory.volume (C a ∩ C b) = 0
      exact MeasureTheory.measure_mono_null
        (inter_subset_inter inter_subset_left inter_subset_left) h0
    · intro a _
      exact (point_count_le_step2_cone_measurable (proto (ty a)) (φ a) p).inter
        measurableSet_ball.nullMeasurableSet
  have hsum : ∑ a ∈ T, (MeasureTheory.volume (C a)).toReal ≤
      (MeasureTheory.volume (ball (0 : E d) 1)).toReal := by
    rw [← ENNReal.toReal_sum (fun a _ => hfin a), ← hunion]
    exact ENNReal.toReal_mono hball
      (MeasureTheory.measure_mono (iUnion₂_subset fun a _ => inter_subset_right))
  have hβ := (minimumAngle_spec proto cx).2
  have hlow : ∀ a ∈ T, minimumAngle proto cx ≤ (d : ℝ) * (MeasureTheory.volume (C a)).toReal :=
    fun a ha => by
      have h := point_count_le_step3_angle_lower proto cx (ty a) ((φ a).symm p) ?_
      · rw [← point_count_le_step2_solidAngle_placed] at h
        exact h
      · obtain ⟨y, hy, hyp⟩ := hT a ha
        rw [← hyp, (φ a).symm_apply_apply]
        exact hy
  have hcard : (T.card : ℝ) * minimumAngle proto cx ≤ fullSolidAngle d := by
    calc (T.card : ℝ) * minimumAngle proto cx = ∑ a ∈ T, minimumAngle proto cx := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ T, (d : ℝ) * (MeasureTheory.volume (C a)).toReal := Finset.sum_le_sum hlow
      _ = (d : ℝ) * ∑ a ∈ T, (MeasureTheory.volume (C a)).toReal := by rw [Finset.mul_sum]
      _ ≤ (d : ℝ) * (MeasureTheory.volume (ball (0 : E d) 1)).toReal :=
          mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)
      _ = fullSolidAngle d := rfl
  unfold multiplicityBound
  apply Nat.le_floor
  rw [le_div_iff₀ hβ]
  exact hcard

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
  set S := {a | p ∈ placedSet (φ a) (proto (ty a)).carrier} with hS
  have hS_fin : S.Finite := by
    by_contra hinf
    obtain ⟨T, hTS, hTcard⟩ :=
      (Set.not_finite.mp hinf).exists_subset_card_eq (multiplicityBound proto cx + 1)
    have := point_count_le_step5_finset_card proto cx ty φ hdisjoint p T (fun a ha => hTS ha)
    omega
  refine ⟨hS_fin, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hS_fin]
  exact point_count_le_step5_finset_card proto cx ty φ hdisjoint p hS_fin.toFinset
    (fun a ha => (Set.Finite.mem_toFinset hS_fin).mp ha)

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
