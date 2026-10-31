import Enforce.Tiling

/-!
# Hereditary source geometry and first providers

Cells retain their prototype names. Their carriers are placed by the full affine
prototype frame, so the same interface covers native tiles and positive-height nodes.
Ancestors are indexed by the number of parent steps, starting with the node itself.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- P1, V4 1.1: a listed cell name in a prototype complex. -/
abbrev CellName (S : SubstSystem d) (A : S.ι) := {e // e ∈ (S.cx A).cells}

/-- P3, V4 1.3: a listed facet name in a prototype complex. -/
abbrev FacetName (S : SubstSystem d) (A : S.ι) := {e // e ∈ (S.cx A).facets}

/-- P1, V4 1.1: place a prototype cell at the actual height of a framed node. -/
def FramedNode.cell (N : FramedNode S) (n : ℕ) (e : Cell d) : Set (E d) :=
  N.prototypeFrame n '' e.carrier

/-- P5, V4 1.5: a listed vertex of a placed node, including flat listed vertices. -/
def FramedNode.Lists (N : FramedNode S) (n : ℕ) (p : E d) : Prop :=
  ∃ e ∈ (S.cx N.ty).vertices, p ∈ N.cell n e

/-- P1, V4 1.1: descendant relation retaining the exact recursive frame. -/
def FramedNode.IsDescendant (C : FramedNode S) (h : ℕ)
    (P : FramedNode S) (n : ℕ) : Prop :=
  ∃ r : ℕ, n = h + r ∧ ∃ w : S.RoleWord P.ty r,
    C = (S.descendantNode P.ty h r w).move P.frame

/-- Step 1 of the V4 proof of `hereditary_trace` (V4 1.1): relative interiors commute
with the full invertible affine prototype frames. -/
private theorem hereditary_trace_step1_relint_image
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

/-- Step 1 of the V4 proof of `hereditary_trace` (V4 1.1): "`F ∩ C`", cells lie on the
boundary: a listed cell lies in the frontier of its placed owner ((H2) transported
through the prototype frame). -/
private theorem hereditary_trace_step1_cell_frontier (N : FramedNode S) (n : ℕ)
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

/-- Step 1 of the V4 proof of `hereditary_trace` (V4 1.1): "`C ⊆ P`" — a listed cell
lies in its closed placed owner. -/
private theorem hereditary_trace_step1_cell_subset (N : FramedNode S) (n : ℕ)
    (e : Cell d) (he : e ∈ (S.cx N.ty).cells) : N.cell n e ⊆ N.carrier n := by
  have hc : IsClosed (N.carrier n) :=
    (((S.proto N.ty).compact.image
      (S.σ ^ n).toContinuousLinearEquiv.continuous).image N.frame.continuous).isClosed
  exact (hereditary_trace_step1_cell_frontier N n e he).trans
    (frontier_subset_iff_isClosed.mpr hc)

/-- Step 1 of the V4 proof of `hereditary_trace` (V4 1.1): "every `p ∈ F ∩ C` lies in
`relint mc_C(p)`" — every frontier point of a placed node lies in the relative interior
of a listed placed cell ((H2)(i) transported through the affine prototype frame). -/
private theorem hereditary_trace_step1_frontier_relint (N : FramedNode S) (n : ℕ) (p : E d)
    (hp : p ∈ frontier (N.carrier n)) :
    ∃ e ∈ (S.cx N.ty).cells, p ∈ relint (N.cell n e) := by
  have hcarrier : N.carrier n = N.prototypeFrame n '' (S.proto N.ty).carrier := by
    simp [FramedNode.carrier, FramedNode.prototypeFrame, placedSet,
      SubstSystem.supertile, Set.image_image]
  rw [hcarrier] at hp
  let H := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  change p ∈ frontier (H '' (S.proto N.ty).carrier) at hp
  rw [← H.image_frontier] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [← (S.cx N.ty).cover] at hq
  obtain ⟨e, he, hqe⟩ := mem_iUnion₂.mp hq
  refine ⟨e, he, ?_⟩
  rw [FramedNode.cell, hereditary_trace_step1_relint_image]
  exact ⟨q, hqe, rfl⟩

/-- Step 1 of the V4 proof of `hereditary_trace` (V4 1.1): "`p ∈ relint g` ... hence
`e₀ = g`" — distinct listed cells of one placed node have disjoint relative interiors
((H2)(i) transported through the affine prototype frame). -/
private theorem hereditary_trace_step1_relint_unique (N : FramedNode S) (n : ℕ)
    (e f : Cell d) (he : e ∈ (S.cx N.ty).cells) (hf : f ∈ (S.cx N.ty).cells) (p : E d)
    (hpe : p ∈ relint (N.cell n e)) (hpf : p ∈ relint (N.cell n f)) : e = f := by
  rw [FramedNode.cell, hereditary_trace_step1_relint_image] at hpe hpf
  obtain ⟨a, ha, rfl⟩ := hpe
  obtain ⟨b, hb, hab⟩ := hpf
  have hba : b = a := (N.prototypeFrame n).injective hab
  subst hba
  by_contra hne
  exact Set.disjoint_left.mp ((S.cx N.ty).relint_disjoint e he f hf hne) ha hb

/-- Step 1 of the V4 proof of `hereditary_trace` (V4 1.1): "Since `C ⊆ P`" — a placed
child lies in its placed parent ((H3) children cover the expanded parent). -/
private theorem hereditary_trace_step1_child_carrier (P : FramedNode S) (m : ℕ)
    (i : S.I P.ty) : (P.child m i).carrier m ⊆ P.carrier (m + 1) := by
  rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hmem : (S.child P.ty i).frame x ∈ S.σ '' (S.proto P.ty).carrier := by
    rw [S.children_cover]
    exact mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩
  obtain ⟨y, hy, he⟩ := hmem
  refine ⟨(S.σ ^ (m + 1)) y, ⟨y, hy, rfl⟩, ?_⟩
  change P.frame ((S.σ ^ (m + 1)) y) = P.frame (S.placeChild m i ((S.σ ^ m) x))
  have hplace : S.placeChild m i ((S.σ ^ m) x) =
      (S.σ ^ m) ((S.child P.ty i).frame x) := by
    change linearConj S.σ (m : ℤ) (S.child P.ty i).rotation.toLinearEquiv
        ((S.σ ^ m) x) + (S.σ ^ m) (S.child P.ty i).offset =
      (S.σ ^ m) ((S.child P.ty i).rotation x + (S.child P.ty i).offset)
    simp [linearConj, zpow_neg, LinearEquiv.mul_apply]
  rw [hplace, ← he, pow_succ]
  rfl

/-- Step 2 of the V4 proof of `hereditary_trace` (V4 1.1), "Case `p ∈ ∂F`": a subset with
the same affine span has relative interior inside the larger relative interior. -/
private theorem hereditary_trace_step2_relint_mono (s t : Set (E d)) (hst : s ⊆ t)
    (hspan : affineSpan ℝ s = affineSpan ℝ t) :
    intrinsicInterior ℝ s ⊆ intrinsicInterior ℝ t := by
  intro x hx
  rw [mem_intrinsicInterior] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  let f : (affineSpan ℝ s) ≃ₜ (affineSpan ℝ t) :=
    Homeomorph.setCongr (congrArg (fun A : AffineSubspace ℝ (E d) => (A : Set (E d))) hspan)
  have himg : f '' interior ((↑) ⁻¹' s : Set (affineSpan ℝ s)) ⊆
      interior ((↑) ⁻¹' t : Set (affineSpan ℝ t)) := by
    rw [f.image_interior]
    apply interior_mono
    rintro _ ⟨z, hz, rfl⟩
    exact hst hz
  exact ⟨f y, himg ⟨y, hy, rfl⟩, rfl⟩

/-- Step 2 of the V4 proof of `hereditary_trace` (V4 1.1), "Case `p ∈ ∂F`", in prototype
coordinates: a point of `F` off its relative interior lies in a listed cell of the
relative boundary, of smaller dimension ((H2)(ii)). -/
private theorem hereditary_trace_step2_proto (A : PolyManifoldDomain d) (K : CellComplex A)
    (F : Cell d) (hF : F ∈ K.cells) (a : E d) (haF : a ∈ F.carrier)
    (hai : a ∉ relint F.carrier) :
    ∃ F' ∈ K.cells, F'.dim < F.dim ∧ F'.carrier ⊆ F.carrier ∧ a ∈ F'.carrier := by
  have hcl : IsClosed F.carrier := F.flat.compact.isClosed
  have hfr : a ∈ relfrontier F.carrier := by
    unfold relfrontier
    rw [← closure_diff_intrinsicInterior, hcl.closure_eq]
    exact ⟨haF, hai⟩
  obtain ⟨b, hb, heq⟩ := K.boundary_union F hF
  have hfr' := hfr
  rw [heq] at hfr'
  obtain ⟨f, hfb, haf⟩ := mem_iUnion₂.mp hfr'
  have hfsub : f.carrier ⊆ relfrontier F.carrier := by
    rw [heq]
    exact subset_iUnion₂_of_subset f hfb Subset.rfl
  have hrfF : relfrontier F.carrier ⊆ F.carrier := intrinsicFrontier_subset hcl
  refine ⟨f, hb hfb, ?_, hfsub.trans hrfF, haf⟩
  have hspanle : affineSpan ℝ f.carrier ≤ affineSpan ℝ F.carrier :=
    affineSpan_mono ℝ (hfsub.trans hrfF)
  have hle : cellDirection f.carrier ≤ cellDirection F.carrier :=
    AffineSubspace.direction_le hspanle
  rw [← f.flat.dimension, ← F.flat.dimension]
  refine lt_of_le_of_ne (Submodule.finrank_mono hle) ?_
  intro hdim
  have hdir : cellDirection f.carrier = cellDirection F.carrier :=
    Submodule.eq_of_le_of_finrank_eq hle hdim
  obtain ⟨x, hx⟩ := f.flat.relint_nonempty
  have hne : (affineSpan ℝ f.carrier : Set (E d)).Nonempty :=
    ⟨x, subset_affineSpan ℝ _ (intrinsicInterior_subset hx)⟩
  have hspan : affineSpan ℝ f.carrier = affineSpan ℝ F.carrier :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir hne hspanle
  have hxF : x ∈ relint F.carrier :=
    hereditary_trace_step2_relint_mono _ _ (hfsub.trans hrfF) hspan hx
  have hxb : x ∈ relfrontier F.carrier := hfsub (intrinsicInterior_subset hx)
  unfold relfrontier at hxb
  rw [← intrinsicClosure_diff_intrinsicInterior] at hxb
  exact hxb.2 hxF

/-- Step 2 of the V4 proof of `hereditary_trace` (V4 1.1), "Case `p ∈ ∂F`": then `p` lies
in a listed cell `F' ⊆ ∂F` of smaller dimension ((H2)(ii): the relative boundary is a
union of listed cells, all of lower dimension). -/
private theorem hereditary_trace_step2_boundary (N : FramedNode S) (n : ℕ) (F : Cell d)
    (hF : F ∈ (S.cx N.ty).cells) (p : E d) (hpF : p ∈ N.cell n F)
    (hpi : p ∉ relint (N.cell n F)) :
    ∃ F' ∈ (S.cx N.ty).cells, F'.dim < F.dim ∧ N.cell n F' ⊆ N.cell n F ∧
      p ∈ N.cell n F' := by
  obtain ⟨a, haF, rfl⟩ := hpF
  have hai : a ∉ relint F.carrier := by
    intro ha
    apply hpi
    rw [FramedNode.cell, hereditary_trace_step1_relint_image]
    exact ⟨a, ha, rfl⟩
  obtain ⟨F', hF', hlt, hsub, haF'⟩ :=
    hereditary_trace_step2_proto (S.proto N.ty) (S.cx N.ty) F hF a haF hai
  exact ⟨F', hF', hlt, Set.image_mono hsub, ⟨a, haF', rfl⟩⟩

/-- Step 3 of the V4 proof of `hereditary_trace` (V4 1.1): the placed child frame at height
`m` is the expanded prototype child frame (frames of (H3)). -/
private theorem hereditary_trace_step3_place (P : FramedNode S) (m : ℕ) (j : S.I P.ty)
    (x : E d) : S.placeChild m j ((S.σ ^ m) x) = (S.σ ^ m) ((S.child P.ty j).frame x) := by
  change linearConj S.σ (m : ℤ) (S.child P.ty j).rotation.toLinearEquiv
      ((S.σ ^ m) x) + (S.σ ^ m) (S.child P.ty j).offset =
    (S.σ ^ m) ((S.child P.ty j).rotation x + (S.child P.ty j).offset)
  simp [linearConj, zpow_neg, LinearEquiv.mul_apply]

/-- Step 3 of the V4 proof of `hereditary_trace` (V4 1.1): a placed child cell is the
height-`m` image of the prescribed child cell. -/
private theorem hereditary_trace_step3_child_cell (P : FramedNode S) (m : ℕ) (j : S.I P.ty)
    (e : Cell d) : (P.child m j).cell m e =
      (fun y => P.frame ((S.σ ^ m) y)) '' placedSet (S.child P.ty j).frame e.carrier := by
  unfold FramedNode.cell placedSet
  rw [Set.image_image]
  apply Set.image_congr
  intro y _
  change P.frame (S.placeChild m j ((S.σ ^ m) y)) = _
  rw [hereditary_trace_step3_place]

/-- Step 3 of the V4 proof of `hereditary_trace` (V4 1.1): a placed parent cell is the
height-`m` image of the expanded prototype cell. -/
private theorem hereditary_trace_step3_parent_cell (P : FramedNode S) (m : ℕ) (F : Cell d) :
    P.cell (m + 1) F = (fun y => P.frame ((S.σ ^ m) y)) '' (S.σ '' F.carrier) := by
  unfold FramedNode.cell
  rw [Set.image_image]
  apply Set.image_congr
  intro y _
  change P.frame ((S.σ ^ (m + 1)) y) = _
  rw [pow_succ]
  rfl

/-- Step 3 of the V4 proof of `hereditary_trace` (V4 1.1): a listed subcell has no larger
dimension. -/
private theorem hereditary_trace_step3_dim_mono (e f : Cell d) (h : e.carrier ⊆ f.carrier) :
    e.dim ≤ f.dim := by
  rw [← e.flat.dimension, ← f.flat.dimension]
  exact Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ h))

/-- Step 3 of the V4 proof of `hereditary_trace` (V4 1.1), "Case `p ∈ relint F`,
`dim F ≤ d-2`": by (H5) `F` is a union of placed `dim F`-cells of children; take `e₁ ⊆ F`
of a child `B` through `p` and `e₀ = mc_B(p) ⊆ e₁`; if `B = C` then `e₀ = g`, otherwise
(H6) makes `e₀` a cell of `C` with `p` in its relative interior, so again `e₀ = g ⊆ F`. -/
private theorem hereditary_trace_step3_lowdim (P : FramedNode S) (m : ℕ) (i : S.I P.ty)
    (F g : Cell d) (hF : F ∈ (S.cx P.ty).cells) (hg : g ∈ (S.cx (P.child m i).ty).cells)
    (hlow : F.dim ≤ d - 2) (p : E d) (hpg : p ∈ relint ((P.child m i).cell m g))
    (hpF : p ∈ relint (P.cell (m + 1) F)) :
    (P.child m i).cell m g ⊆ P.cell (m + 1) F := by
  let ψ : E d → E d := fun y => P.frame ((S.σ ^ m) y)
  have hψ : Function.Injective ψ := fun a b hab =>
    (S.σ ^ m).injective (P.frame.injective hab)
  have hpF' : p ∈ P.cell (m + 1) F := intrinsicInterior_subset hpF
  rw [hereditary_trace_step3_parent_cell] at hpF'
  obtain ⟨_, ⟨a, haF, rfl⟩, hpa⟩ := hpF'
  obtain ⟨fs, hfs⟩ := S.heredity P.ty F hF
  have hsa : S.σ a ∈ ⋃ q ∈ fs, placedSet (S.child P.ty q.1).frame q.2.val.carrier := by
    rw [← hfs]; exact ⟨a, haF, rfl⟩
  obtain ⟨⟨j, e1, he1, hdim1⟩, hq, hx⟩ := mem_iUnion₂.mp hsa
  obtain ⟨x, hx1, hxa⟩ := hx
  -- the child cell `e₁` lies in `F`
  have he1F : (P.child m j).cell m e1 ⊆ P.cell (m + 1) F := by
    rw [hereditary_trace_step3_child_cell, hereditary_trace_step3_parent_cell, hfs]
    exact Set.image_mono (subset_iUnion₂_of_subset ⟨j, e1, he1, hdim1⟩ hq Subset.rfl)
  -- the minimal cell `e₀ = mc_B(p)`
  have hxfr : x ∈ frontier (S.proto (S.child P.ty j).ty).carrier := by
    rw [← (S.cx (S.child P.ty j).ty).carriers_cover]
    exact mem_iUnion₂.mpr ⟨e1, he1, hx1⟩
  let K := S.cx (S.child P.ty j).ty
  let e0 := K.minimalCell x hxfr
  have he0 : e0 ∈ K.cells := K.minimalCell_mem x hxfr
  have hxe0 : x ∈ relint e0.carrier := K.mem_relint_minimalCell x hxfr
  have he01 : e0.carrier ⊆ e1.carrier := K.minimalCell_subset x hxfr e1 he1 hx1
  have hpx : (P.child m j).prototypeFrame m x = p := by
    change P.frame (S.placeChild m j ((S.σ ^ m) x)) = p
    rw [hereditary_trace_step3_place, hxa]
    exact hpa
  have hpe0 : p ∈ relint ((P.child m j).cell m e0) := by
    rw [FramedNode.cell, hereditary_trace_step1_relint_image]
    exact ⟨x, hxe0, hpx⟩
  have he0F : (P.child m j).cell m e0 ⊆ P.cell (m + 1) F :=
    (Set.image_mono he01).trans he1F
  by_cases hji : j = i
  · subst hji
    rw [hereditary_trace_step1_relint_unique (P.child m j) m g e0 hg he0 p hpg hpe0]
    exact he0F
  · -- (H6): `e₀` is a cell of `C`
    have hpC : p ∈ (P.child m i).carrier m :=
      hereditary_trace_step1_cell_subset _ m g hg (intrinsicInterior_subset hpg)
    obtain ⟨_, ⟨y, hy, rfl⟩, hyp⟩ := hpC
    have hyi : (S.child P.ty i).frame y = S.σ a := by
      apply hψ
      change P.frame ((S.σ ^ m) ((S.child P.ty i).frame y)) = P.frame ((S.σ ^ m) (S.σ a))
      rw [← hereditary_trace_step3_place]
      exact hyp.trans hpa.symm
    have hlow0 : e0.dim ≤ d - 2 :=
      (hereditary_trace_step3_dim_mono e0 e1 he01).trans (hdim1 ▸ hlow)
    have hsymm : (S.child P.ty j).frame.symm (S.σ a) = x := by
      rw [← hxa]; exact (S.child P.ty j).frame.symm_apply_apply x
    obtain ⟨f, hf, hfe⟩ := S.sibling_conformity P.ty j i hji (S.σ a)
      ⟨x, (S.proto (S.child P.ty j).ty).compact.isClosed.frontier_subset hxfr, hxa⟩
      ⟨y, hy, hyi⟩ e0 he0 (by rw [hsymm]; exact hxe0) hlow0
    have hcell : (P.child m j).cell m e0 = (P.child m i).cell m f := by
      rw [hereditary_trace_step3_child_cell, hereditary_trace_step3_child_cell, hfe]
    rw [hcell] at hpe0 he0F
    rw [hereditary_trace_step1_relint_unique (P.child m i) m g f hg hf p hpg hpe0]
    exact he0F

/-- Step 4 of the V4 proof of `hereditary_trace` (V4 1.1), "Case `p ∈ relint F`,
`dim F = d-1`", local part: "Let `U` be as in Lemma 1.0(a) for `P` and `F`: `P ∩ U` is the
closed half-ball `U ∩ Π⁺` with `∂Π⁺ = aff F`. Since `C ⊆ P`, `g ∩ U ⊆ Π⁺` ... so
`relint g ∩ U' ⊆ aff F ∩ U = F ∩ U` for a smaller ball `U' ∋ q`." -/
private theorem hereditary_trace_step4_local (P : FramedNode S) (m : ℕ) (i : S.I P.ty)
    (F g : Cell d) (hF : F ∈ (S.cx P.ty).cells) (hg : g ∈ (S.cx (P.child m i).ty).cells)
    (hdim : F.dim = d - 1) (q : E d) (hqg : q ∈ relint ((P.child m i).cell m g))
    (hqF : q ∈ relint (P.cell (m + 1) F)) :
    ∃ r : ℝ, 0 < r ∧ relint ((P.child m i).cell m g) ∩ ball q r ⊆ P.cell (m + 1) F := by
  let φ := P.prototypeFrame (m + 1)
  let A := (S.proto P.ty).carrier
  have hcarrier : P.carrier (m + 1) = φ '' A := by
    simp [φ, A, FramedNode.carrier, FramedNode.prototypeFrame, placedSet,
      SubstSystem.supertile, Set.image_image]
  have hCA : (P.child m i).cell m g ⊆ φ '' A := by
    rw [← hcarrier]
    exact (hereditary_trace_step1_cell_subset _ m g hg).trans
      (hereditary_trace_step1_child_carrier P m i)
  have hqC : q ∈ (P.child m i).cell m g := intrinsicInterior_subset hqg
  -- relative openness of `relint g` at `q`
  have hε : ∃ ε > 0, ∀ z ∈ affineSpan ℝ ((P.child m i).cell m g), dist z q < ε →
      z ∈ (P.child m i).cell m g := by
    unfold relint at hqg
    rw [mem_intrinsicInterior] at hqg
    obtain ⟨y, hy, hyq⟩ := hqg
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hy
    refine ⟨ε, hε, fun z hz hzq => ?_⟩
    have hzb : (⟨z, hz⟩ : affineSpan ℝ ((P.child m i).cell m g)) ∈ ball y ε := by
      rw [mem_ball, Subtype.dist_eq, hyq]
      exact hzq
    have h2 := interior_subset (hball hzb)
    exact h2
  obtain ⟨ε, hε, hεC⟩ := hε
  -- the half-ball of Lemma 1.0(a)
  rw [FramedNode.cell, hereditary_trace_step1_relint_image] at hqF
  obtain ⟨a, ha, rfl⟩ := hqF
  have hFf : F ∈ (S.cx P.ty).facets := by
    unfold CellComplex.facets
    exact Finset.mem_filter.mpr ⟨hF, hdim⟩
  obtain ⟨r, hr, v, hv, hfront, hFb, hAb⟩ :=
    facet_halfball (S.proto P.ty) (S.cx P.ty) F hFf a ha
  obtain ⟨δ, hδ, hδr⟩ := Metric.continuousAt_iff.mp
    (φ.symm.continuous_of_finiteDimensional.continuousAt (x := φ a)) r hr
  refine ⟨min ε δ, lt_min hε hδ, ?_⟩
  rintro x ⟨hxg, hxb⟩
  have hxC : x ∈ (P.child m i).cell m g := intrinsicInterior_subset hxg
  have hxε : dist x (φ a) < ε := lt_of_lt_of_le (mem_ball.mp hxb) (min_le_left _ _)
  have hxδ : dist x (φ a) < δ := lt_of_lt_of_le (mem_ball.mp hxb) (min_le_right _ _)
  set x' := AffineMap.lineMap x (φ a) (2 : ℝ) with hx'
  have hx'span : x' ∈ affineSpan ℝ ((P.child m i).cell m g) :=
    AffineMap.lineMap_mem 2 (subset_affineSpan ℝ _ hxC) (subset_affineSpan ℝ _ hqC)
  have hdist : dist x' (φ a) = dist x (φ a) := by
    rw [hx', dist_lineMap_right]
    norm_num
  have hx'C : x' ∈ (P.child m i).cell m g := hεC x' hx'span (hdist ▸ hxε)
  have hx'δ : dist x' (φ a) < δ := hdist ▸ hxδ
  obtain ⟨y, hyA, rfl⟩ := hCA hxC
  have hy'A : AffineMap.lineMap y a (2 : ℝ) ∈ A := by
    obtain ⟨y', hy'A, hy'⟩ := hCA hx'C
    have : y' = AffineMap.lineMap y a (2 : ℝ) := by
      apply φ.injective
      rw [hy', hx']
      exact (AffineMap.apply_lineMap φ.toAffineMap y a 2).symm
    exact this ▸ hy'A
  have hyr : dist y a < r := by
    have := hδr hxδ
    simpa using this
  have hy'r : dist (AffineMap.lineMap y a (2 : ℝ)) a < r := by
    rw [dist_lineMap_right]
    norm_num
    exact hyr
  have hin1 : 0 ≤ inner ℝ v (y - a) := by
    have : y ∈ A ∩ ball a r := ⟨hyA, mem_ball.mpr hyr⟩
    rw [hAb] at this
    exact this.1
  have hin2 : 0 ≤ inner ℝ v (AffineMap.lineMap y a (2 : ℝ) - a) := by
    have : AffineMap.lineMap y a (2 : ℝ) ∈ A ∩ ball a r := ⟨hy'A, mem_ball.mpr hy'r⟩
    rw [hAb] at this
    exact this.1
  have hlin : AffineMap.lineMap y a (2 : ℝ) - a = (-1 : ℝ) • (y - a) := by
    rw [← vsub_eq_sub, AffineMap.lineMap_vsub_right, vsub_eq_sub]
    norm_num
  rw [hlin, inner_smul_right] at hin2
  have hzero : inner ℝ v (y - a) = 0 := by linarith
  -- `y` is a frontier point of the prototile
  have hyfr : y ∈ frontier A := by
    refine ⟨subset_closure hyA, fun hint => ?_⟩
    obtain ⟨ε2, hε2, hball2⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
    set t := min (ε2 / 2) ((r - dist y a) / 2) with ht
    have htpos : 0 < t := lt_min (by linarith) (by linarith)
    have hzy : dist (y - t • v) y = t := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hv, mul_one,
        Real.norm_of_nonneg htpos.le]
    have hzA : y - t • v ∈ A := hball2 (by
      rw [mem_ball, hzy]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith))
    have hza : dist (y - t • v) a < r := by
      have h1 := dist_triangle (y - t • v) y a
      have h2 : t ≤ (r - dist y a) / 2 := min_le_right _ _
      linarith
    have hz : y - t • v ∈ A ∩ ball a r := ⟨hzA, mem_ball.mpr hza⟩
    rw [hAb] at hz
    have hz1 : 0 ≤ inner ℝ v (y - t • v - a) := hz.1
    have hcalc : inner ℝ v (y - t • v - a) = inner ℝ v (y - a) - t := by
      rw [show y - t • v - a = (y - a) - t • v by abel, inner_sub_right, inner_smul_right,
        real_inner_self_eq_norm_sq, hv]
      ring
    rw [hcalc, hzero] at hz1
    linarith
  have hyF : y ∈ F.carrier := by
    have h1 : y ∈ frontier A ∩ ball a r := ⟨hyfr, mem_ball.mpr hyr⟩
    rw [hfront, ← hFb] at h1
    exact h1.1
  exact ⟨y, hyF, rfl⟩

/-- Step 4 of the V4 proof of `hereditary_trace` (V4 1.1), "Case `p ∈ relint F`,
`dim F = d-1`": by Lemma 1.0(a) `P` is a closed half-ball near `p` bounded by `aff F`, and
`C ⊆ P`, so `relint g ∩ F` is a neighbourhood of `p` in `relint g`; together with the
boundary case (hypothesis `hbd`) the set `relint g ∩ F` is relatively clopen in the
connected set `relint g`, hence `g = closure (relint g) ⊆ F`. -/
private theorem hereditary_trace_step4_facet (P : FramedNode S) (m : ℕ) (i : S.I P.ty)
    (F g : Cell d) (hF : F ∈ (S.cx P.ty).cells) (hg : g ∈ (S.cx (P.child m i).ty).cells)
    (hdim : F.dim = d - 1)
    (hbd : ∀ q, q ∈ relint ((P.child m i).cell m g) → q ∈ P.cell (m + 1) F →
      q ∉ relint (P.cell (m + 1) F) → (P.child m i).cell m g ⊆ P.cell (m + 1) F)
    (p : E d) (hpg : p ∈ relint ((P.child m i).cell m g))
    (hpF : p ∈ relint (P.cell (m + 1) F)) :
    (P.child m i).cell m g ⊆ P.cell (m + 1) F := by
  by_cases hex : ∃ q, q ∈ relint ((P.child m i).cell m g) ∧ q ∈ P.cell (m + 1) F ∧
      q ∉ relint (P.cell (m + 1) F)
  · obtain ⟨q, h1, h2, h3⟩ := hex
    exact hbd q h1 h2 h3
  push_neg at hex
  let φ := (P.child m i).prototypeFrame m
  have hXimg : relint ((P.child m i).cell m g) = φ '' relint g.carrier := by
    rw [FramedNode.cell, hereditary_trace_step1_relint_image]
  have hconn : IsPreconnected (relint ((P.child m i).cell m g)) := by
    rw [hXimg]
    exact (g.flat.relint_connected.image _
      φ.continuous_of_finiteDimensional.continuousOn).isPreconnected
  have hclosedF : IsClosed (P.cell (m + 1) F) :=
    (F.flat.compact.image (P.prototypeFrame (m + 1)).continuous_of_finiteDimensional).isClosed
  have hsub : relint ((P.child m i).cell m g) ⊆ P.cell (m + 1) F := by
    haveI := isPreconnected_iff_preconnectedSpace.mp hconn
    let T : Set (relint ((P.child m i).cell m g)) := {x | x.val ∈ P.cell (m + 1) F}
    have hTc : IsClosed T := hclosedF.preimage continuous_subtype_val
    have hTo : IsOpen T := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨r, hr, hball⟩ := hereditary_trace_step4_local P m i F g hF hg hdim x.val
        x.property (hex x.val x.property hx)
      refine Filter.mem_of_superset
        ((isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hr)) ?_
      intro y hy
      exact hball ⟨y.property, hy⟩
    have hTne : T.Nonempty :=
      ⟨⟨p, hpg⟩, show p ∈ P.cell (m + 1) F from intrinsicInterior_subset hpF⟩
    have huniv := IsClopen.eq_univ ⟨hTc, hTo⟩ hTne
    intro x hx
    have hxT : (⟨x, hx⟩ : relint ((P.child m i).cell m g)) ∈ T := huniv ▸ mem_univ _
    exact hxT
  have hcl : closure (relint ((P.child m i).cell m g)) = (P.child m i).cell m g := by
    rw [hXimg]
    let H := φ.toHomeomorphOfFiniteDimensional
    change closure (H '' relint g.carrier) = H '' g.carrier
    rw [← H.image_closure, g.flat.regularClosed]
  rw [← hcl]
  exact closure_minimal hsub hclosedF

/-- Step 5 of the V4 proof of `hereditary_trace` (V4 1.1): the one-step statement for a
child, by induction on `dim F` over the three cases. -/
private theorem hereditary_trace_step5_child (P : FramedNode S) (m : ℕ) (i : S.I P.ty)
    (F g : Cell d) (hF : F ∈ (S.cx P.ty).cells) (hg : g ∈ (S.cx (P.child m i).ty).cells)
    (hmeet : (relint ((P.child m i).cell m g) ∩ P.cell (m + 1) F).Nonempty) :
    (P.child m i).cell m g ⊆ P.cell (m + 1) F := by
  suffices H : ∀ k, ∀ F : Cell d, F.dim = k → F ∈ (S.cx P.ty).cells → ∀ p,
      p ∈ relint ((P.child m i).cell m g) → p ∈ P.cell (m + 1) F →
      (P.child m i).cell m g ⊆ P.cell (m + 1) F by
    obtain ⟨p, hpg, hpF⟩ := hmeet
    exact H _ F rfl hF p hpg hpF
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro F hk hF p hpg hpF
    have hbd : ∀ q, q ∈ relint ((P.child m i).cell m g) → q ∈ P.cell (m + 1) F →
        q ∉ relint (P.cell (m + 1) F) → (P.child m i).cell m g ⊆ P.cell (m + 1) F := by
      intro q hqg hqF hqi
      obtain ⟨F', hF', hlt, hsub, hqF'⟩ :=
        hereditary_trace_step2_boundary P (m + 1) F hF q hqF hqi
      exact (ih F'.dim (by omega) F' rfl hF' q hqg hqF').trans hsub
    by_cases hpi : p ∈ relint (P.cell (m + 1) F)
    · have hlt : F.dim < d := (S.cx P.ty).dim_lt F hF
      by_cases hlow : F.dim ≤ d - 2
      · exact hereditary_trace_step3_lowdim P m i F g hF hg hlow p hpg hpi
      · exact hereditary_trace_step4_facet P m i F g hF hg (by omega) hbd p hpg hpi
    · exact hbd p hpg hpF hpi

/-- Step 6 of the V4 proof of `hereditary_trace` (V4 1.1): the same statement inside a
single complex (descendant of depth zero), by induction on `dim F`. -/
private theorem hereditary_trace_step6_same (N : FramedNode S) (n : ℕ) (F g : Cell d)
    (hF : F ∈ (S.cx N.ty).cells) (hg : g ∈ (S.cx N.ty).cells)
    (hmeet : (relint (N.cell n g) ∩ N.cell n F).Nonempty) :
    N.cell n g ⊆ N.cell n F := by
  suffices H : ∀ k, ∀ F : Cell d, F.dim = k → F ∈ (S.cx N.ty).cells → ∀ p,
      p ∈ relint (N.cell n g) → p ∈ N.cell n F → N.cell n g ⊆ N.cell n F by
    obtain ⟨p, hpg, hpF⟩ := hmeet
    exact H _ F rfl hF p hpg hpF
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro F hk hF p hpg hpF
    by_cases hpi : p ∈ relint (N.cell n F)
    · rw [hereditary_trace_step1_relint_unique N n g F hg hF p hpg hpi]
    · obtain ⟨F', hF', hlt, hsub, hpF'⟩ :=
        hereditary_trace_step2_boundary N n F hF p hpF hpi
      exact (ih F'.dim (by omega) F' rfl hF' p hpg hpF').trans hsub

/-- Step 7 of the V4 proof of `hereditary_trace` (V4 1.1): a descendant of depth zero is
the node itself. -/
private theorem hereditary_trace_step7_zero (P C : FramedNode S) (h : ℕ)
    (hC : C.IsDescendant h P h) : C = P := by
  obtain ⟨r, hr, w, rfl⟩ := hC
  have h0 : r = 0 := by omega
  subst h0
  apply FramedNode.ext
  · rfl
  · ext x
    rfl

/-- Step 7 of the V4 proof of `hereditary_trace` (V4 1.1): "`C` is a child of `C'`" —
a descendant of positive depth is a descendant of one child of the node. -/
private theorem hereditary_trace_step7_peel (P C : FramedNode S) (h r : ℕ)
    (hC : C.IsDescendant h P (h + (r + 1))) :
    ∃ i : S.I P.ty, C.IsDescendant h (P.child (h + r) i) (h + r) := by
  obtain ⟨r', hr', w, rfl⟩ := hC
  have h1 : r' = r + 1 := by omega
  subst h1
  refine ⟨w.1, r, rfl, w.2, ?_⟩
  apply FramedNode.ext
  · rfl
  · ext x
    rfl

/-- Step 7 of the V4 proof of `hereditary_trace` (V4 1.1): descendants lie in their
ancestors. -/
private theorem hereditary_trace_step7_carrier (P C : FramedNode S) (h r : ℕ)
    (hC : C.IsDescendant h P (h + r)) : C.carrier h ⊆ P.carrier (h + r) := by
  induction r generalizing P with
  | zero =>
    rw [hereditary_trace_step7_zero P C h hC]
    exact Subset.rfl
  | succ r ih =>
    obtain ⟨i, hC'⟩ := hereditary_trace_step7_peel P C h r hC
    exact (ih _ hC').trans (hereditary_trace_step1_child_carrier P (h + r) i)

/-- Step 7 of the V4 proof of `hereditary_trace` (V4 1.1), "For deeper descendants":
iterate the one-step statement through the intermediate descendant. -/
private theorem hereditary_trace_step7_descend (C : FramedNode S) (h : ℕ) (g : Cell d)
    (hg : g ∈ (S.cx C.ty).cells) (r : ℕ) :
    ∀ (P : FramedNode S) (F : Cell d), C.IsDescendant h P (h + r) →
      F ∈ (S.cx P.ty).cells → (relint (C.cell h g) ∩ P.cell (h + r) F).Nonempty →
      C.cell h g ⊆ P.cell (h + r) F := by
  induction r with
  | zero =>
    intro P F hC hF hmeet
    have hCP := hereditary_trace_step7_zero P C h hC
    subst hCP
    exact hereditary_trace_step6_same C h F g hF hg hmeet
  | succ r ih =>
    intro P F hC hF hmeet
    obtain ⟨i, hC'⟩ := hereditary_trace_step7_peel P C h r hC
    obtain ⟨p, hpg, hpF⟩ := hmeet
    have hpC : p ∈ C.carrier h :=
      hereditary_trace_step1_cell_subset C h g hg (intrinsicInterior_subset hpg)
    have hpP' : p ∈ (P.child (h + r) i).carrier (h + r) :=
      hereditary_trace_step7_carrier _ C h r hC' hpC
    have hfr : p ∈ frontier (P.carrier (h + (r + 1))) :=
      hereditary_trace_step1_cell_frontier P _ F hF hpF
    have hpfr : p ∈ frontier ((P.child (h + r) i).carrier (h + r)) := by
      refine ⟨subset_closure hpP', fun hint => hfr.2 ?_⟩
      exact interior_mono (hereditary_trace_step1_child_carrier P (h + r) i) hint
    obtain ⟨g', hg', hpg'⟩ :=
      hereditary_trace_step1_frontier_relint (P.child (h + r) i) (h + r) p hpfr
    have h1 : (P.child (h + r) i).cell (h + r) g' ⊆ P.cell (h + r + 1) F :=
      hereditary_trace_step5_child P (h + r) i F g' hF hg' ⟨p, hpg', hpF⟩
    have h2 : C.cell h g ⊆ (P.child (h + r) i).cell (h + r) g' :=
      ih _ g' hC' hg' ⟨p, hpg, intrinsicInterior_subset hpg'⟩
    exact h2.trans h1

/-- P1, V4 1.1: hereditary trace, for descendants of arbitrary depth. -/
theorem hereditary_trace (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (F g : Cell d)
    (hF : F ∈ (S.cx P.ty).cells) (hg : g ∈ (S.cx C.ty).cells)
    (hmeet : (relint (C.cell h g) ∩ P.cell n F).Nonempty) :
    C.cell h g ⊆ P.cell n F := by
  obtain ⟨r, rfl, -⟩ := id hC
  exact hereditary_trace_step7_descend C h g hg r P F hC hF hmeet

/-- P1, V4 1.1: the entire trace on a descendant is a union of its listed cells. -/
theorem hereditary_trace_union (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (F : Cell d) (hF : F ∈ (S.cx P.ty).cells) :
    P.cell n F ∩ C.carrier h =
      ⋃ e ∈ (S.cx C.ty).cells, ⋃ (_ : C.cell h e ⊆ P.cell n F), C.cell h e := by
  sorry

/-- P2, V4 1.2: existence and uniqueness of the ancestral stratum.
Nonempty relative interior of the listed cell supplies an actual point. -/
theorem ancestralStratum_exists_unique (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (g : CellName S C.ty)
    (hg : C.cell h g.val ⊆ frontier (P.carrier n)) :
    ∃! F : CellName S P.ty,
      relint (C.cell h g.val) ⊆ relint (P.cell n F.val) := by
  sorry

/-- P2, V4 1.2: the unique ancestral stratum, chosen from the existence lemma. -/
def ancestralStratum (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (g : CellName S C.ty)
    (hg : C.cell h g.val ⊆ frontier (P.carrier n)) : CellName S P.ty :=
  Classical.choose (ancestralStratum_exists_unique P C n h hC g hg)

/-- P2, V4 1.2: relative-interior characterization and dimension monotonicity. -/
theorem ancestralStratum_spec (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (g : CellName S C.ty)
    (hg : C.cell h g.val ⊆ frontier (P.carrier n)) :
    relint (C.cell h g.val) ⊆
        relint (P.cell n (ancestralStratum P C n h hC g hg).val) ∧
      g.val.dim ≤ (ancestralStratum P C n h hC g hg).val.dim := by
  sorry

/-- P2, V4 1.2: ancestral strata preserve inclusion of incident cells. -/
theorem ancestralStratum_mono (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (g g' : CellName S C.ty)
    (hg : C.cell h g.val ⊆ frontier (P.carrier n))
    (hg' : C.cell h g'.val ⊆ frontier (P.carrier n))
    (hsub : C.cell h g'.val ⊆ C.cell h g.val) :
    P.cell n (ancestralStratum P C n h hC g' hg').val ⊆
      P.cell n (ancestralStratum P C n h hC g hg).val := by
  sorry

/-- P3, V4 1.3: exactly one ancestral facet contains a boundary facet;
otherwise its entire relative interior is interior to the ancestor. -/
theorem facet_dichotomy (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (f : FacetName S C.ty) :
    (∃! F : FacetName S P.ty, C.cell h f.val ⊆ P.cell n F.val) ∨
      relint (C.cell h f.val) ⊆ interior (P.carrier n) := by
  sorry

/-- P4, V4 1.4(a): sibling minimal cells agree as placed carriers.
The relative-interior hypotheses name the minimal cells without boundary casts. -/
theorem sibling_minimalCell_eq (P : FramedNode S) (n : ℕ)
    (i j : S.I P.ty) (hij : i ≠ j) (p : E d)
    (e : CellName S (P.child n i).ty) (f : CellName S (P.child n j).ty)
    (he : p ∈ relint ((P.child n i).cell n e.val))
    (hf : p ∈ relint ((P.child n j).cell n f.val)) :
    (P.child n i).cell n e.val = (P.child n j).cell n f.val := by
  sorry

/-- P4, V4 1.4(a): sibling intersections are unions of common listed cells. -/
theorem sibling_intersection_cells (P : FramedNode S) (n : ℕ)
    (i j : S.I P.ty) (hij : i ≠ j) :
    (P.child n i).carrier n ∩ (P.child n j).carrier n =
      ⋃ e : CellName S (P.child n i).ty,
        ⋃ f : CellName S (P.child n j).ty,
          ⋃ (_ : (P.child n i).cell n e.val = (P.child n j).cell n f.val),
            (P.child n i).cell n e.val := by
  sorry

/-- P4, V4 1.4(b): positive facet measure, expressed by Hausdorff measure. -/
def PositiveFacetOverlap (K L : Set (E d)) : Prop :=
  0 < MeasureTheory.Measure.hausdorffMeasure (d - 1 : ℝ) (K ∩ L)

/-- Step 0 of the V4 proof of `sibling_facet_eq` (V4 1.4(b)): a listed facet name is a
listed cell of dimension `d-1` ((H2), facets are the `(d-1)`-cells). -/
private theorem sibling_facet_eq_step0_facet {N : FramedNode S} (e : FacetName S N.ty) :
    e.val ∈ (S.cx N.ty).cells ∧ e.val.dim = d - 1 := by
  have h := e.property
  unfold CellComplex.facets at h
  exact Finset.mem_filter.mp h

/-- Step 0 of the V4 proof of `sibling_facet_eq` (V4 1.4(b)): "by dimension" — the
dimension of the affine hull is invariant under the invertible affine prototype frames. -/
private theorem sibling_facet_eq_step0_finrank_image (φ : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
    Module.finrank ℝ (cellDirection (φ '' K)) = Module.finrank ℝ (cellDirection K) := by
  unfold cellDirection
  have h := AffineSubspace.map_span φ.toAffineMap K
  rw [show φ '' K = φ.toAffineMap '' K from rfl, ← h, AffineSubspace.map_direction]
  exact LinearEquiv.finrank_map_eq φ.linear _

/-- Step 1a of the V4 proof of `sibling_facet_eq` (V4 1.4(b)): "positive overlap minus
the null sets `∂g_B ∪ ∂g_C`" — a placed listed cell of dimension at most `d-2` lies in an
affine subspace of dimension at most `d-2`, hence has `(d-1)`-dimensional Hausdorff
measure zero. -/
private theorem sibling_facet_eq_step1_lowcell_null (N : FramedNode S) (n : ℕ) (g : Cell d)
    (hg : g.dim ≤ d - 2) :
    MeasureTheory.Measure.hausdorffMeasure (d - 1 : ℝ) (N.cell n g) = 0 := by
  have hfin : Module.finrank ℝ (affineSpan ℝ (N.cell n g)).direction = g.dim := by
    change Module.finrank ℝ (cellDirection (N.cell n g)) = g.dim
    rw [← g.flat.dimension]
    exact sibling_facet_eq_step0_finrank_image (N.prototypeFrame n) g.carrier
  by_cases hne : (N.cell n g).Nonempty
  · obtain ⟨p0, hp0⟩ := hne
    have hp0Q : p0 ∈ affineSpan ℝ (N.cell n g) := subset_affineSpan ℝ _ hp0
    let ι : (affineSpan ℝ (N.cell n g)).direction → E d := fun v => (v : E d) + p0
    have hι : Isometry ι := Isometry.of_dist_eq fun x y => by
      simp only [ι, dist_add_right]
      rfl
    have hsub : N.cell n g ⊆ ι '' univ := by
      intro x hx
      refine ⟨⟨x -ᵥ p0, AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ _ hx) hp0Q⟩, trivial, ?_⟩
      simp [ι]
    have hdim : dimH (N.cell n g) ≤ (g.dim : ENNReal) := by
      calc dimH (N.cell n g) ≤ dimH (ι '' univ) := dimH_mono hsub
        _ = dimH (univ : Set (affineSpan ℝ (N.cell n g)).direction) := hι.dimH_image univ
        _ = (Module.finrank ℝ (affineSpan ℝ (N.cell n g)).direction : ENNReal) :=
          Real.dimH_univ_eq_finrank _
        _ = g.dim := by rw [hfin]
    have hd2 : 2 ≤ d := Fact.out
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    let D : NNReal := ⟨(d : ℝ) - 1, by linarith⟩
    have hgR : (g.dim : ℝ) + 2 ≤ d := by
      have : g.dim + 2 ≤ d := by omega
      exact_mod_cast this
    have hlt : dimH (N.cell n g) < (D : ENNReal) := by
      refine lt_of_le_of_lt hdim ?_
      have h1 : ((g.dim : NNReal)) < D := by
        rw [← NNReal.coe_lt_coe]
        change (g.dim : ℝ) < (d : ℝ) - 1
        linarith
      exact_mod_cast h1
    have key : MeasureTheory.Measure.hausdorffMeasure ((D : NNReal) : ℝ) (N.cell n g) = 0 :=
      hausdorffMeasure_of_dimH_lt hlt
    have hD : ((D : NNReal) : ℝ) = (d : ℝ) - 1 := rfl
    rw [hD] at key
    exact key
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact MeasureTheory.measure_empty

/-- Step 1 of the V4 proof of `sibling_facet_eq` (V4 1.4(b)): "It is nonempty (positive
overlap minus the null sets `∂g_B ∪ ∂g_C`)" — a positive-measure overlap of two placed
facets contains a point of both relative interiors. -/
private theorem sibling_facet_eq_step1_common_relint (P : FramedNode S) (n : ℕ)
    (i j : S.I P.ty) (e : FacetName S (P.child n i).ty) (f : FacetName S (P.child n j).ty)
    (hover : PositiveFacetOverlap ((P.child n i).cell n e.val)
      ((P.child n j).cell n f.val)) :
    ∃ p, p ∈ relint ((P.child n i).cell n e.val) ∧
      p ∈ relint ((P.child n j).cell n f.val) := by
  by_contra hno
  push_neg at hno
  have hnull : ∀ N : FramedNode S, MeasureTheory.Measure.hausdorffMeasure (d - 1 : ℝ)
      (⋃ F' ∈ (S.cx N.ty).cells.filter (fun F' => F'.dim ≤ d - 2), N.cell n F') = 0 := by
    intro N
    refine le_antisymm ((MeasureTheory.measure_biUnion_finset_le _ _).trans
      (Finset.sum_eq_zero fun F' hF' => ?_).le) (zero_le _)
    exact sibling_facet_eq_step1_lowcell_null N n F' (Finset.mem_filter.mp hF').2
  have hlow : ∀ (N : FramedNode S) (g : FacetName S N.ty) (x : E d), x ∈ N.cell n g.val →
      x ∉ relint (N.cell n g.val) →
      x ∈ ⋃ F' ∈ (S.cx N.ty).cells.filter (fun F' => F'.dim ≤ d - 2), N.cell n F' := by
    intro N g x hx hxi
    obtain ⟨hgc, hgd⟩ := sibling_facet_eq_step0_facet g
    obtain ⟨F', hF', hlt, -, hxF'⟩ := hereditary_trace_step2_boundary N n g.val hgc x hx hxi
    exact mem_iUnion₂.mpr ⟨F', Finset.mem_filter.mpr ⟨hF', by omega⟩, hxF'⟩
  have hsub : (P.child n i).cell n e.val ∩ (P.child n j).cell n f.val ⊆
      (⋃ F' ∈ (S.cx (P.child n i).ty).cells.filter (fun F' => F'.dim ≤ d - 2),
        (P.child n i).cell n F') ∪
      (⋃ F' ∈ (S.cx (P.child n j).ty).cells.filter (fun F' => F'.dim ≤ d - 2),
        (P.child n j).cell n F') := by
    rintro x ⟨hxe, hxf⟩
    by_cases hx : x ∈ relint ((P.child n i).cell n e.val)
    · exact Or.inr (hlow _ f x hxf (hno x hx))
    · exact Or.inl (hlow _ e x hxe hx)
  have hzero := MeasureTheory.measure_mono_null hsub
    (MeasureTheory.measure_union_null (hnull _) (hnull _))
  unfold PositiveFacetOverlap at hover
  exact hover.ne' hzero

/-- Step 2 of the V4 proof of `sibling_facet_eq` (V4 1.4(b)): "Claim:
`relint g_B ∩ ∂g_C = ∅`. If `p` were in it, `e := mc_C(p) ⊆ ∂g_C` has `dim e ≤ d-2` and
`p ∈ relint e ∩ B`, so by (H6) `e` is a cell of `B` with `p ∈ relint e`, forcing
`e = mc_B(p) = g_B`, impossible by dimension." -/
private theorem sibling_facet_eq_step2_no_boundary (P : FramedNode S) (n : ℕ)
    (i j : S.I P.ty) (hij : i ≠ j) (e : FacetName S (P.child n i).ty) (g : Cell d)
    (hg : g ∈ (S.cx (P.child n j).ty).cells) (p : E d)
    (hpe : p ∈ relint ((P.child n i).cell n e.val)) (hpg : p ∈ (P.child n j).cell n g) :
    p ∈ relint ((P.child n j).cell n g) := by
  by_contra hpi
  have hd2 : 2 ≤ d := Fact.out
  obtain ⟨heC, heD⟩ := sibling_facet_eq_step0_facet e
  obtain ⟨F', hF', hlt, -, hpF'⟩ :=
    hereditary_trace_step2_boundary (P.child n j) n g hg p hpg hpi
  have hgd : g.dim < d := (S.cx (P.child n j).ty).dim_lt g hg
  obtain ⟨x, hxF', hpx⟩ := hpF'
  let K := S.cx (S.child P.ty j).ty
  have hxfr : x ∈ frontier (S.proto (S.child P.ty j).ty).carrier := by
    rw [← K.carriers_cover]
    exact mem_iUnion₂.mpr ⟨F', hF', hxF'⟩
  have hex : ∃ e0 ∈ K.cells, x ∈ relint e0.carrier ∧ e0.carrier ⊆ F'.carrier :=
    ⟨K.minimalCell x hxfr, K.minimalCell_mem x hxfr, K.mem_relint_minimalCell x hxfr,
      K.minimalCell_subset x hxfr F' hF' hxF'⟩
  obtain ⟨e0, he0, hxe0, he0F'⟩ := hex
  have hlow0 : e0.dim ≤ d - 2 := by
    have := hereditary_trace_step3_dim_mono e0 F' he0F'
    omega
  have hpe0 : p ∈ relint ((P.child n j).cell n e0) := by
    rw [FramedNode.cell, hereditary_trace_step1_relint_image]
    exact ⟨x, hxe0, hpx⟩
  have hpB : p ∈ (P.child n i).carrier n :=
    hereditary_trace_step1_cell_subset _ n e.val heC (intrinsicInterior_subset hpe)
  obtain ⟨_, ⟨y, hy, rfl⟩, hyp⟩ := hpB
  have hψ : Function.Injective (fun y => P.frame ((S.σ ^ n) y)) := fun a b hab =>
    (S.σ ^ n).injective (P.frame.injective hab)
  have hyx : (S.child P.ty i).frame y = (S.child P.ty j).frame x := by
    apply hψ
    change P.frame ((S.σ ^ n) ((S.child P.ty i).frame y)) =
      P.frame ((S.σ ^ n) ((S.child P.ty j).frame x))
    rw [← hereditary_trace_step3_place P n i, ← hereditary_trace_step3_place P n j]
    exact hyp.trans hpx.symm
  have hsymm : (S.child P.ty j).frame.symm ((S.child P.ty j).frame x) = x :=
    (S.child P.ty j).frame.symm_apply_apply x
  obtain ⟨f', hf', hfe⟩ := S.sibling_conformity P.ty j i hij.symm ((S.child P.ty j).frame x)
    ⟨x, (S.proto (S.child P.ty j).ty).compact.isClosed.frontier_subset hxfr, rfl⟩
    ⟨y, hy, hyx⟩ e0 he0 (by rw [hsymm]; exact hxe0) hlow0
  have hcell : (P.child n j).cell n e0 = (P.child n i).cell n f' := by
    rw [hereditary_trace_step3_child_cell, hereditary_trace_step3_child_cell, hfe]
  have hpf' : p ∈ relint ((P.child n i).cell n f') := hcell ▸ hpe0
  have hef := hereditary_trace_step1_relint_unique (P.child n i) n e.val f' heC hf' _ hpe hpf'
  have hdims : e.val.dim = e0.dim := by
    rw [← e.val.flat.dimension, ← e0.flat.dimension,
      ← sibling_facet_eq_step0_finrank_image ((P.child n i).prototypeFrame n) e.val.carrier,
      ← sibling_facet_eq_step0_finrank_image ((P.child n j).prototypeFrame n) e0.carrier]
    change Module.finrank ℝ (cellDirection ((P.child n i).cell n e.val)) =
      Module.finrank ℝ (cellDirection ((P.child n j).cell n e0))
    rw [hcell, hef]
  omega

/-- Step 3a of the V4 proof of `sibling_facet_eq` (V4 1.0(a), used in 1.4(b)): in
prototype coordinates, near a relative-interior facet point the domain is the closed
half-ball `{⟪v, x - a⟫ ≥ 0}` and the facet is the bounding hyperplane piece. -/
private theorem sibling_facet_eq_step3a_proto_halfball (A : PolyManifoldDomain d)
    (K : CellComplex A) (F : Cell d) (hF : F ∈ K.facets) (a : E d)
    (ha : a ∈ relint F.carrier) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : E d, ‖v‖ = 1 ∧
      A.carrier ∩ ball a r = {x | 0 ≤ inner ℝ v (x - a)} ∩ ball a r ∧
      F.carrier ∩ ball a r = {x | inner ℝ v (x - a) = 0} ∩ ball a r := by
  obtain ⟨r, hr, v, hv, hfront, hFb, hAb⟩ := facet_halfball A K F hF a ha
  refine ⟨r, hr, v, hv, hAb, ?_⟩
  have hFc : F ∈ K.cells := by
    unfold CellComplex.facets at hF
    exact (Finset.mem_filter.mp hF).1
  have haF : a ∈ F.carrier := intrinsicInterior_subset ha
  have haS : a ∈ affineSpan ℝ F.carrier := subset_affineSpan ℝ _ haF
  have hFA : F.carrier ⊆ A.carrier := fun x hx => by
    have hfr : x ∈ frontier A.carrier := by
      rw [← K.carriers_cover]
      exact mem_iUnion₂.mpr ⟨F, hFc, hx⟩
    exact A.compact.isClosed.frontier_subset hfr
  ext x
  constructor
  · rintro ⟨hxF, hxb⟩
    refine ⟨?_, hxb⟩
    have hx' : AffineMap.lineMap x a (2 : ℝ) ∈ F.carrier ∩ ball a r := by
      rw [hFb]
      refine ⟨AffineMap.lineMap_mem 2 (subset_affineSpan ℝ _ hxF) haS, ?_⟩
      rw [mem_ball] at hxb ⊢
      have hdist : dist (AffineMap.lineMap x a (2 : ℝ)) a = dist x a := by
        rw [dist_lineMap_right]
        norm_num
      rw [hdist]
      exact hxb
    have h1 : x ∈ A.carrier ∩ ball a r := ⟨hFA hxF, hxb⟩
    have h2 : AffineMap.lineMap x a (2 : ℝ) ∈ A.carrier ∩ ball a r := ⟨hFA hx'.1, hx'.2⟩
    rw [hAb] at h1 h2
    have hin1 : 0 ≤ inner ℝ v (x - a) := h1.1
    have hin2 : 0 ≤ inner ℝ v (AffineMap.lineMap x a (2 : ℝ) - a) := h2.1
    have hlin : AffineMap.lineMap x a (2 : ℝ) - a = (-1 : ℝ) • (x - a) := by
      rw [← vsub_eq_sub, AffineMap.lineMap_vsub_right, vsub_eq_sub]
      norm_num
    rw [hlin, inner_smul_right] at hin2
    show inner ℝ v (x - a) = 0
    linarith
  · rintro ⟨hx0, hxb⟩
    have hx0' : inner ℝ v (x - a) = 0 := hx0
    have hxA : x ∈ A.carrier := by
      have : x ∈ {x | 0 ≤ inner ℝ v (x - a)} ∩ ball a r := ⟨le_of_eq hx0'.symm, hxb⟩
      rw [← hAb] at this
      exact this.1
    have hxfr : x ∈ frontier A.carrier := by
      refine ⟨subset_closure hxA, fun hint => ?_⟩
      obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.mp isOpen_interior x hint
      have hxr : dist x a < r := mem_ball.mp hxb
      set t := min (ε / 2) ((r - dist x a) / 2) with ht
      have htpos : 0 < t := lt_min (half_pos hε) (by linarith)
      have hzx : dist (x - t • v) x = t := by
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hv, mul_one,
          Real.norm_of_nonneg htpos.le]
      have hzI : x - t • v ∈ interior A.carrier := hεA (by
        rw [mem_ball, hzx]
        exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))
      have hzb : x - t • v ∈ ball a r := by
        rw [mem_ball]
        have h1 := dist_triangle (x - t • v) x a
        have h2 : t ≤ (r - dist x a) / 2 := min_le_right _ _
        linarith
      have hzA : x - t • v ∈ A.carrier ∩ ball a r := ⟨interior_subset hzI, hzb⟩
      rw [hAb] at hzA
      have hz : inner ℝ v (x - t • v - a) = -t := by
        rw [show x - t • v - a = (x - a) - t • v by abel, inner_sub_right, inner_smul_right,
          real_inner_self_eq_norm_sq, hv, hx0']
        ring
      have := hzA.1
      simp only [mem_setOf_eq] at this
      linarith
    have : x ∈ frontier A.carrier ∩ ball a r := ⟨hxfr, hxb⟩
    rw [hfront, ← hFb] at this
    exact this

/-- Step 3 of the V4 proof of `sibling_facet_eq` (V4 1.0(a), used in 1.4(b)): "By 1.0(a)
`B` is a closed half-ball near `p` bounded by `aff g_B`", transported to a placed node
through its invertible affine prototype frame (the normal is renormalised). -/
private theorem sibling_facet_eq_step3_halfball (N : FramedNode S) (n : ℕ)
    (F : FacetName S N.ty) (p : E d) (hp : p ∈ relint (N.cell n F.val)) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : E d, ‖v‖ = 1 ∧
      N.carrier n ∩ ball p r = {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p r ∧
      N.cell n F.val ∩ ball p r = {x | inner ℝ v (x - p) = 0} ∩ ball p r := by
  have hcarrier : N.carrier n = N.prototypeFrame n '' (S.proto N.ty).carrier := by
    simp [FramedNode.carrier, FramedNode.prototypeFrame, placedSet,
      SubstSystem.supertile, Set.image_image]
  have hcell : N.cell n F.val = N.prototypeFrame n '' F.val.carrier := rfl
  rw [hcarrier, hcell]
  rw [FramedNode.cell, hereditary_trace_step1_relint_image] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨r, hr, s, hs, hA, hFb⟩ :=
    sibling_facet_eq_step3a_proto_halfball (S.proto N.ty) (S.cx N.ty) F.val F.property a ha
  set ψ := N.prototypeFrame n with hψdef
  let L : E d →ₗ[ℝ] E d := ψ.symm.toAffineMap.linear
  have hL : ∀ x, ψ.symm x - a = L (x - ψ a) := by
    intro x
    have h := ψ.symm.toAffineMap.linearMap_vsub x (ψ a)
    simp only [vsub_eq_sub, AffineEquiv.coe_toAffineMap, AffineEquiv.symm_apply_apply] at h
    exact h.symm
  let s' := LinearMap.adjoint L s
  have hs' : ∀ x, inner ℝ s (ψ.symm x - a) = inner ℝ s' (x - ψ a) := by
    intro x
    rw [hL, LinearMap.adjoint_inner_left]
  have hs'0 : s' ≠ 0 := by
    intro h0
    have h := hs' (ψ (a + s))
    rw [ψ.symm_apply_apply, add_sub_cancel_left, h0, inner_zero_left,
      real_inner_self_eq_norm_sq, hs] at h
    norm_num at h
  have hn : 0 < ‖s'‖ := norm_pos_iff.mpr hs'0
  have key : ∀ x, inner ℝ (‖s'‖⁻¹ • s') (x - ψ a) =
      ‖s'‖⁻¹ * inner ℝ s (ψ.symm x - a) := by
    intro x
    rw [real_inner_smul_left, hs']
  have hmem : ∀ (X : Set (E d)) x, x ∈ ψ '' X ↔ ψ.symm x ∈ X := fun X x =>
    ⟨by rintro ⟨y, hy, rfl⟩; rwa [ψ.symm_apply_apply],
      fun h => ⟨_, h, ψ.apply_symm_apply x⟩⟩
  obtain ⟨δ, hδ, hδr⟩ := Metric.continuousAt_iff.mp
    (ψ.symm.continuous_of_finiteDimensional.continuousAt (x := ψ a)) r hr
  have hball : ∀ x, x ∈ ball (ψ a) δ → ψ.symm x ∈ ball a r := fun x hx => by
    have h := hδr (mem_ball.mp hx)
    rw [ψ.symm_apply_apply] at h
    exact h
  have hinv : 0 < ‖s'‖⁻¹ := inv_pos.mpr hn
  refine ⟨δ, hδ, ‖s'‖⁻¹ • s', ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  · ext x
    constructor
    · rintro ⟨hx, hxb⟩
      refine ⟨?_, hxb⟩
      have h : ψ.symm x ∈ (S.proto N.ty).carrier ∩ ball a r :=
        ⟨(hmem _ x).mp hx, hball x hxb⟩
      rw [hA] at h
      show 0 ≤ inner ℝ (‖s'‖⁻¹ • s') (x - ψ a)
      rw [key]
      exact mul_nonneg hinv.le h.1
    · rintro ⟨hx, hxb⟩
      refine ⟨(hmem _ x).mpr ?_, hxb⟩
      have hx' : 0 ≤ inner ℝ (‖s'‖⁻¹ • s') (x - ψ a) := hx
      rw [key] at hx'
      have h : ψ.symm x ∈ {y | 0 ≤ inner ℝ s (y - a)} ∩ ball a r :=
        ⟨(mul_nonneg_iff_of_pos_left hinv).mp hx', hball x hxb⟩
      rw [← hA] at h
      exact h.1
  · ext x
    constructor
    · rintro ⟨hx, hxb⟩
      refine ⟨?_, hxb⟩
      have h : ψ.symm x ∈ F.val.carrier ∩ ball a r := ⟨(hmem _ x).mp hx, hball x hxb⟩
      rw [hFb] at h
      show inner ℝ (‖s'‖⁻¹ • s') (x - ψ a) = 0
      rw [key]
      have h1 : inner ℝ s (ψ.symm x - a) = 0 := h.1
      rw [h1, mul_zero]
    · rintro ⟨hx, hxb⟩
      refine ⟨(hmem _ x).mpr ?_, hxb⟩
      have hx' : inner ℝ (‖s'‖⁻¹ • s') (x - ψ a) = 0 := hx
      rw [key, mul_eq_zero] at hx'
      have h0 : inner ℝ s (ψ.symm x - a) = 0 := hx'.resolve_left hinv.ne'
      have h : ψ.symm x ∈ {y | inner ℝ s (y - a) = 0} ∩ ball a r := ⟨h0, hball x hxb⟩
      rw [← hFb] at h
      exact h.1

/-- Step 4 of the V4 proof of `sibling_facet_eq` (V4 1.4(a),(b)): "If the hyperplanes
differed, the two open half-balls would intersect in an open set near `p` ...,
contradicting disjoint interiors; so ... the children lie on opposite sides": two
closed half-balls at `p` with disjoint interiors have opposite unit normals. -/
private theorem sibling_facet_eq_step4_opposite (X Y : Set (E d)) (p v w : E d) (r : ℝ)
    (hr : 0 < r) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hX : X ∩ ball p r = {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p r)
    (hY : Y ∩ ball p r = {x | 0 ≤ inner ℝ w (x - p)} ∩ ball p r)
    (hXY : Disjoint (interior X) (interior Y)) : w = -v := by
  by_contra hne
  have hu0 : v + w ≠ 0 := by
    intro h
    apply hne
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  have hnu : 0 < ‖v + w‖ := norm_pos_iff.mpr hu0
  have hcomm : inner ℝ w v = inner ℝ v w := real_inner_comm v w
  have hsq : ‖v + w‖ ^ 2 = 2 + 2 * inner ℝ v w := by
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hv, hw, hcomm]
    ring
  have hpos : 0 < 1 + inner ℝ v w := by nlinarith [sq_pos_of_pos hnu]
  have hvu : 0 < inner ℝ v (v + w) := by
    rw [inner_add_right, real_inner_self_eq_norm_sq, hv]
    linarith
  have hwu : 0 < inner ℝ w (v + w) := by
    rw [inner_add_right, real_inner_self_eq_norm_sq, hw, hcomm]
    linarith
  set t := r / (2 * ‖v + w‖) with ht
  have htpos : 0 < t := div_pos hr (by positivity)
  let O := {x : E d | 0 < inner ℝ v (x - p)} ∩ {x | 0 < inner ℝ w (x - p)} ∩ ball p r
  have hO : IsOpen O := by
    refine ((isOpen_lt continuous_const ?_).inter (isOpen_lt continuous_const ?_)).inter
      isOpen_ball
    · exact continuous_const.inner (continuous_id.sub continuous_const)
    · exact continuous_const.inner (continuous_id.sub continuous_const)
  have hOX : O ⊆ X := by
    rintro x ⟨⟨h1, -⟩, hb⟩
    have : x ∈ {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p r :=
      ⟨show 0 ≤ inner ℝ v (x - p) from le_of_lt h1, hb⟩
    rw [← hX] at this
    exact this.1
  have hOY : O ⊆ Y := by
    rintro x ⟨⟨-, h2⟩, hb⟩
    have : x ∈ {x | 0 ≤ inner ℝ w (x - p)} ∩ ball p r :=
      ⟨show 0 ≤ inner ℝ w (x - p) from le_of_lt h2, hb⟩
    rw [← hY] at this
    exact this.1
  have hx0 : p + t • (v + w) ∈ O := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show 0 < inner ℝ v (p + t • (v + w) - p)
      rw [add_sub_cancel_left, inner_smul_right]
      exact mul_pos htpos hvu
    · show 0 < inner ℝ w (p + t • (v + w) - p)
      rw [add_sub_cancel_left, inner_smul_right]
      exact mul_pos htpos hwu
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg htpos.le]
      have : t * ‖v + w‖ = r / 2 := by
        rw [ht, div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by norm_num)]
        ring
      rw [this]
      linarith
  exact Set.disjoint_left.mp hXY (interior_maximal hOX hO hx0) (interior_maximal hOY hO hx0)

/-- Step 5 of the V4 proof of `sibling_facet_eq` (V4 1.4, (H3)): a placed child carrier is
the height-`n` image of the prescribed child placement. -/
private theorem sibling_facet_eq_step5_child_carrier (P : FramedNode S) (n : ℕ)
    (i : S.I P.ty) :
    (P.child n i).carrier n = P.prototypeFrame n ''
      placedSet (S.child P.ty i).frame (S.proto (S.child P.ty i).ty).carrier := by
  unfold FramedNode.carrier placedSet SubstSystem.supertile
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro y _
  change P.frame (S.placeChild n i ((S.σ ^ n) y)) =
    P.frame ((S.σ ^ n) ((S.child P.ty i).frame y))
  rw [hereditary_trace_step3_place]

/-- Step 5 of the V4 proof of `sibling_facet_eq` (V4 1.4, (H3)): "contradicting disjoint
interiors" — distinct placed children have disjoint interiors. -/
private theorem sibling_facet_eq_step5_disjoint (P : FramedNode S) (n : ℕ)
    (i j : S.I P.ty) (hij : i ≠ j) :
    Disjoint (interior ((P.child n i).carrier n)) (interior ((P.child n j).carrier n)) := by
  rw [sibling_facet_eq_step5_child_carrier, sibling_facet_eq_step5_child_carrier]
  let H := (P.prototypeFrame n).toHomeomorphOfFiniteDimensional
  change Disjoint (interior (H '' _)) (interior (H '' _))
  rw [← H.image_interior, ← H.image_interior]
  exact Set.disjoint_image_of_injective H.injective (S.children_disjoint P.ty hij)

/-- Step 6 of the V4 proof of `sibling_facet_eq` (V4 1.4(a),(b)): at a point of both
relative interiors, "`B` and `C` are closed half-balls near `p` bounded by `aff g_B`,
`aff g_C`", the normals are opposite, hence the hyperplanes and the facets agree near `p`
and the children lie on opposite sides. -/
private theorem sibling_facet_eq_step6_local (P : FramedNode S) (n : ℕ)
    (i j : S.I P.ty) (hij : i ≠ j)
    (e : FacetName S (P.child n i).ty) (f : FacetName S (P.child n j).ty) (q : E d)
    (hqe : q ∈ relint ((P.child n i).cell n e.val))
    (hqf : q ∈ relint ((P.child n j).cell n f.val)) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : E d, ‖v‖ = 1 ∧
      (P.child n i).carrier n ∩ ball q r = {x | 0 ≤ inner ℝ v (x - q)} ∩ ball q r ∧
      (P.child n j).carrier n ∩ ball q r = {x | inner ℝ v (x - q) ≤ 0} ∩ ball q r ∧
      (P.child n i).cell n e.val ∩ ball q r = (P.child n j).cell n f.val ∩ ball q r := by
  obtain ⟨r1, hr1, v, hv, hB, hgB⟩ := sibling_facet_eq_step3_halfball (P.child n i) n e q hqe
  obtain ⟨r2, hr2, w, hw, hC, hgC⟩ := sibling_facet_eq_step3_halfball (P.child n j) n f q hqf
  have hr : 0 < min r1 r2 := lt_min hr1 hr2
  have shrink : ∀ {X Y : Set (E d)} {ρ : ℝ}, min r1 r2 ≤ ρ →
      X ∩ ball q ρ = Y ∩ ball q ρ → X ∩ ball q (min r1 r2) = Y ∩ ball q (min r1 r2) := by
    intro X Y ρ hρ h
    ext x
    constructor
    · rintro ⟨hx, hxb⟩
      have : x ∈ X ∩ ball q ρ := ⟨hx, ball_subset_ball hρ hxb⟩
      rw [h] at this
      exact ⟨this.1, hxb⟩
    · rintro ⟨hx, hxb⟩
      have : x ∈ Y ∩ ball q ρ := ⟨hx, ball_subset_ball hρ hxb⟩
      rw [← h] at this
      exact ⟨this.1, hxb⟩
  have hB' := shrink (min_le_left _ _) hB
  have hC' := shrink (min_le_right _ _) hC
  have hgB' := shrink (min_le_left _ _) hgB
  have hgC' := shrink (min_le_right _ _) hgC
  have hwv : w = -v := sibling_facet_eq_step4_opposite _ _ q v w _ hr hv hw hB' hC'
    (sibling_facet_eq_step5_disjoint P n i j hij)
  subst hwv
  refine ⟨min r1 r2, hr, v, hv, hB', ?_, ?_⟩
  · rw [hC']
    ext x
    simp [inner_neg_left]
  · rw [hgB', hgC']
    ext x
    simp [inner_neg_left]

/-- Step 7 of the V4 proof of `sibling_facet_eq` (V4 1.4(b)): "Hence
`g_C ∩ relint g_B = relint g_C ∩ relint g_B`, which is relatively closed in `relint g_B`
... and relatively open ... It is nonempty ... By connectedness `relint g_B ⊆ relint g_C`";
closures then give `g_B ⊆ g_C`. -/
private theorem sibling_facet_eq_step7_subset (P : FramedNode S) (n : ℕ)
    (i j : S.I P.ty) (hij : i ≠ j)
    (e : FacetName S (P.child n i).ty) (f : FacetName S (P.child n j).ty) (p : E d)
    (hpe : p ∈ relint ((P.child n i).cell n e.val))
    (hpf : p ∈ (P.child n j).cell n f.val) :
    (P.child n i).cell n e.val ⊆ (P.child n j).cell n f.val := by
  let φ := (P.child n i).prototypeFrame n
  have hXimg : relint ((P.child n i).cell n e.val) = φ '' relint e.val.carrier := by
    rw [FramedNode.cell, hereditary_trace_step1_relint_image]
  have hconn : IsPreconnected (relint ((P.child n i).cell n e.val)) := by
    rw [hXimg]
    exact (e.val.flat.relint_connected.image _
      φ.continuous_of_finiteDimensional.continuousOn).isPreconnected
  have hclosedF : IsClosed ((P.child n j).cell n f.val) :=
    (f.val.flat.compact.image
      ((P.child n j).prototypeFrame n).continuous_of_finiteDimensional).isClosed
  have hfC : f.val ∈ (S.cx (P.child n j).ty).cells := (sibling_facet_eq_step0_facet f).1
  have hsub : relint ((P.child n i).cell n e.val) ⊆ (P.child n j).cell n f.val := by
    haveI := isPreconnected_iff_preconnectedSpace.mp hconn
    let T : Set (relint ((P.child n i).cell n e.val)) :=
      {x | x.val ∈ (P.child n j).cell n f.val}
    have hTc : IsClosed T := hclosedF.preimage continuous_subtype_val
    have hTo : IsOpen T := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      have hxf := sibling_facet_eq_step2_no_boundary P n i j hij e f.val hfC x.val
        x.property hx
      obtain ⟨r, hr, v, -, -, -, hball⟩ :=
        sibling_facet_eq_step6_local P n i j hij e f x.val x.property hxf
      refine Filter.mem_of_superset
        ((isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hr)) ?_
      intro y hy
      have : y.val ∈ (P.child n i).cell n e.val ∩ ball x.val r :=
        ⟨intrinsicInterior_subset y.property, hy⟩
      rw [hball] at this
      exact this.1
    have hTne : T.Nonempty := ⟨⟨p, hpe⟩, hpf⟩
    have huniv := IsClopen.eq_univ ⟨hTc, hTo⟩ hTne
    intro x hx
    have hxT : (⟨x, hx⟩ : relint ((P.child n i).cell n e.val)) ∈ T := huniv ▸ mem_univ _
    exact hxT
  have hcl : closure (relint ((P.child n i).cell n e.val)) = (P.child n i).cell n e.val := by
    rw [hXimg]
    let H := φ.toHomeomorphOfFiniteDimensional
    change closure (H '' relint e.val.carrier) = H '' e.val.carrier
    rw [← H.image_closure, e.val.flat.regularClosed]
  rw [← hcl]
  exact closure_minimal hsub hclosedF

/-- P4, V4 1.4(b): positive-measure sibling facet overlap forces whole equality,
and the children occupy opposite closed half-balls at every relative-interior point. -/
theorem sibling_facet_eq (P : FramedNode S) (n : ℕ)
    (i j : S.I P.ty) (hij : i ≠ j)
    (e : FacetName S (P.child n i).ty) (f : FacetName S (P.child n j).ty)
    (hover : PositiveFacetOverlap ((P.child n i).cell n e.val)
      ((P.child n j).cell n f.val)) :
    (P.child n i).cell n e.val = (P.child n j).cell n f.val ∧
      ∀ p ∈ relint ((P.child n i).cell n e.val), ∃ r : ℝ, 0 < r ∧
        ∃ v : E d, ‖v‖ = 1 ∧
          (P.child n i).carrier n ∩ ball p r =
            {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p r ∧
          (P.child n j).carrier n ∩ ball p r =
            {x | inner ℝ v (x - p) ≤ 0} ∩ ball p r := by
  obtain ⟨p, hpe, hpf⟩ := sibling_facet_eq_step1_common_relint P n i j e f hover
  have heq : (P.child n i).cell n e.val = (P.child n j).cell n f.val :=
    Set.Subset.antisymm
      (sibling_facet_eq_step7_subset P n i j hij e f p hpe (intrinsicInterior_subset hpf))
      (sibling_facet_eq_step7_subset P n j i hij.symm f e p hpf (intrinsicInterior_subset hpe))
  refine ⟨heq, fun q hq => ?_⟩
  have hqf : q ∈ relint ((P.child n j).cell n f.val) := by
    rw [← heq]
    exact hq
  obtain ⟨r, hr, v, hv, hB, hC, -⟩ := sibling_facet_eq_step6_local P n i j hij e f q hq hqf
  exact ⟨r, hr, v, hv, hB, hC⟩

/-- Step 1 of the V4 proof of `internal_facet_pairing` (V4 1.4(c)): relint(F) is a subset of the macro-tile interior. -/
private lemma internal_facet_pairing_step1_relint_subset
    (P : FramedNode S) (n : ℕ) (i : S.I P.ty)
    (f : FacetName S (P.child n i).ty)
    (hint : (relint ((P.child n i).cell n f.val) ∩
      interior (P.carrier (n + 1))).Nonempty) :
    relint ((P.child n i).cell n f.val) ⊆ interior (P.carrier (n + 1)) := by sorry

/-- Step 2a of the V4 proof of `internal_facet_pairing` (V4 1.4(c)): coverage provides a child having the internal facet as a facet. -/
private lemma internal_facet_pairing_step2a_existence
    (P : FramedNode S) (n : ℕ) (i : S.I P.ty)
    (f : FacetName S (P.child n i).ty)
    (hint : relint ((P.child n i).cell n f.val) ⊆ interior (P.carrier (n + 1))) :
    ∃ j : S.I P.ty, j ≠ i ∧
      ∃ g : FacetName S (P.child n j).ty,
        (P.child n j).cell n g.val = (P.child n i).cell n f.val := by sorry

/-- Step 2b of the V4 proof of `internal_facet_pairing` (V4 1.4(c)): children not having it as a facet meet it in lower cells, of measure zero. -/
private lemma internal_facet_pairing_step2b_nullity
    (P : FramedNode S) (n : ℕ) (i : S.I P.ty)
    (f : FacetName S (P.child n i).ty)
    (l : S.I P.ty) (hl : l ≠ i)
    (hl' : ∀ g : FacetName S (P.child n l).ty, (P.child n l).cell n g.val ≠ (P.child n i).cell n f.val) :
    MeasureTheory.Measure.hausdorffMeasure (d - 1 : ℝ)
      ((P.child n l).carrier n ∩ (P.child n i).cell n f.val) = 0 := by sorry

/-- Step 2c of the V4 proof of `internal_facet_pairing` (V4 1.4(c)): there is exactly one child (other than i) having F as a facet. -/
private lemma internal_facet_pairing_step2c_uniqueness
    (P : FramedNode S) (n : ℕ) (i : S.I P.ty)
    (f : FacetName S (P.child n i).ty)
    (j k : S.I P.ty) (hj : j ≠ i) (hk : k ≠ i)
    (g_j : FacetName S (P.child n j).ty) (heq_j : (P.child n j).cell n g_j.val = (P.child n i).cell n f.val)
    (g_k : FacetName S (P.child n k).ty) (heq_k : (P.child n k).cell n g_k.val = (P.child n i).cell n f.val) :
    j = k := by sorry

/-- P4, V4 1.4(c): an internal facet has one other owning child;
all remaining children have zero facet measure on it. Existence comes from coverage. -/
theorem internal_facet_pairing (P : FramedNode S) (n : ℕ) (i : S.I P.ty)
    (f : FacetName S (P.child n i).ty)
    (hint : (relint ((P.child n i).cell n f.val) ∩
      interior (P.carrier (n + 1))).Nonempty) :
    relint ((P.child n i).cell n f.val) ⊆ interior (P.carrier (n + 1)) ∧
      ∃! j : S.I P.ty, j ≠ i ∧
        ∃ g : FacetName S (P.child n j).ty,
          (P.child n j).cell n g.val = (P.child n i).cell n f.val ∧
          ∀ l : S.I P.ty, l ≠ i → l ≠ j →
            MeasureTheory.Measure.hausdorffMeasure (d - 1 : ℝ)
              ((P.child n l).carrier n ∩ (P.child n i).cell n f.val) = 0 := by
  have h1 := internal_facet_pairing_step1_relint_subset P n i f hint
  refine ⟨h1, ?_⟩
  obtain ⟨j, hj, g, hg⟩ := internal_facet_pairing_step2a_existence P n i f h1
  use j
  refine ⟨⟨hj, g, hg, ?_⟩, ?_⟩
  · intro l hli hlj
    apply internal_facet_pairing_step2b_nullity P n i f l hli
    intro g_l heq_l
    exact hlj (internal_facet_pairing_step2c_uniqueness P n i f j l hj hli g hg g_l heq_l).symm
  · rintro k ⟨hki, g_k, hgk, -⟩
    exact internal_facet_pairing_step2c_uniqueness P n i f k j hki hj g_k hgk g hg

/-- P5, V4 1.5(a): listed vertices pass to every containing child. -/
theorem vertex_inherited (P : FramedNode S) (n : ℕ) (p : E d)
    (hp : P.Lists (n + 1) p) (i : S.I P.ty)
    (hi : p ∈ (P.child n i).carrier n) : (P.child n i).Lists n p := by
  sorry

/-- P5, V4 1.5(b): listedness passes to all containing descendants.
This node form also applies separately to every member of a compatible patch. -/
theorem commonListed_inherited (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (p : E d) (hp : P.Lists n p)
    (hpC : p ∈ C.carrier h) : C.Lists h p := by
  sorry

/-- P5, V4 1.5(c): a listed vertex on an internal facet is common-listed
in the entire immediate subdivision, including children meeting only at that vertex. -/
theorem primitive_vertex_listed (P : FramedNode S) (n : ℕ) (i : S.I P.ty)
    (f : FacetName S (P.child n i).ty)
    (hint : relint ((P.child n i).cell n f.val) ⊆ interior (P.carrier (n + 1)))
    (p : E d) (hp : (P.child n i).Lists n p)
    (hpf : p ∈ (P.child n i).cell n f.val)
    (j : S.I P.ty) (hpj : p ∈ (P.child n j).carrier n) :
    (P.child n j).Lists n p := by
  sorry

/-- P6, V4 1.6: finite primitive incidence, with both cell names and both roles.
The roles are ordered to record the serving side; exchanging them gives the other side. -/
structure PrimitiveIncidence (S : SubstSystem d) where
  /-- P6, V4 1.6: birth-parent prototype. -/
  ty : S.ι
  /-- P6, V4 1.6: serving child role. -/
  left : S.I ty
  /-- P6, V4 1.6: opposite child role. -/
  right : S.I ty
  /-- P6, V4 1.6: paired children are distinct. -/
  distinct : left ≠ right
  /-- P6, V4 1.6: provider name in the serving child's complex. -/
  leftFacet : FacetName S (S.child ty left).ty
  /-- P6, V4 1.6: provider name in the opposite child's complex. -/
  rightFacet : FacetName S (S.child ty right).ty
  /-- P6, V4 1.6: the two names have identical placed carriers in `σ A`. -/
  paired : placedSet (S.child ty left).frame leftFacet.val.carrier =
    placedSet (S.child ty right).frame rightFacet.val.carrier
  /-- P6, V4 1.6: the common facet is first-generation internal. -/
  internal : relint (placedSet (S.child ty left).frame leftFacet.val.carrier) ⊆
    interior (S.supertile 1 ty)

/-- P6, V4 1.6: the catalogue of primitive incidences is finite. -/
theorem primitiveIncidence_finite (S : SubstSystem d) : Finite (PrimitiveIncidence S) := by
  sorry

namespace CoherentHierarchy

variable {T : Tiling S} (H : CoherentHierarchy S T)

/-- P6, V4 1.6: the ancestor after `r` parent steps, including step zero. -/
def ancestor (q : H.Node) (r : ℕ) : H.Node := (H.parentNode^[r]) q

/-- P6, V4 1.6: the height of an ancestor is the original height plus its offset. -/
theorem ancestor_height (q : H.Node) (r : ℕ) : (H.ancestor q r).1 = q.1 + r := by
  induction' r with r ih generalizing q
  · rfl
  · have ih' := ih (H.parentNode q)
    change (H.parentNode^[r] (H.parentNode q)).1 = q.1 + (r + 1)
    dsimp [ancestor] at ih'
    rw [ih']
    dsimp [parentNode]
    omega

/-- P6, V4 1.6: actual ancestors satisfy the recursive framed descendant relation. -/
theorem ancestor_descendant (q : H.Node) (r : ℕ) :
    q.2.val.IsDescendant q.1 (H.ancestor q r).2.val (H.ancestor q r).1 := by
  sorry

/-- P6, V4 1.6: offsets for which the original facet remains on the boundary. -/
def boundaryOffsets (q : H.Node) (f : FacetName S q.2.val.ty) : Set ℕ :=
  {r | q.2.val.cell q.1 f.val ⊆
    frontier ((H.ancestor q r).2.val.carrier (H.ancestor q r).1)}

/-- P6, V4 1.6: persistent boundary facets have no finite provider. -/
def IsFault (q : H.Node) (f : FacetName S q.2.val.ty) : Prop :=
  ∀ r : ℕ, r ∈ H.boundaryOffsets q f

/-- P6, V4 1.6: boundary heights form an initial segment, or persist forever.
A finite segment includes offset zero and ends immediately before the birth. -/
theorem boundaryOffsets_initial (q : H.Node) (f : FacetName S q.2.val.ty) :
    (∃ b : ℕ, 1 ≤ b ∧ H.boundaryOffsets q f = {r | r < b}) ∨ H.IsFault q f := by
  sorry

/-- P6, V4 1.6: possible serving-child offsets and named provider facets. -/
abbrev ProviderCandidate (q : H.Node) :=
  Σ r : ℕ, FacetName S (H.ancestor q r).2.val.ty

/-- P6, V4 1.6: a candidate is the first provider precisely when it is the
unique serving facet at the last boundary offset and is internal to the next ancestor. -/
def IsProvider (q : H.Node) (f : FacetName S q.2.val.ty)
    (v : H.ProviderCandidate q) : Prop :=
  H.boundaryOffsets q f = {r | r < v.1 + 1} ∧
    q.2.val.cell q.1 f.val ⊆
      (H.ancestor q v.1).2.val.cell (H.ancestor q v.1).1 v.2.val ∧
    relint ((H.ancestor q v.1).2.val.cell (H.ancestor q v.1).1 v.2.val) ⊆
      interior ((H.ancestor q (v.1 + 1)).2.val.carrier (H.ancestor q (v.1 + 1)).1)

/-- P6/P7, V4 1.6, 1.7(a): a nonfault facet has exactly one first provider.
Nonfaultness gives a finite endpoint of the initial segment. -/
theorem provider_exists_unique (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : ∃! v : H.ProviderCandidate q, H.IsProvider q f v := by
  sorry

/-- P6, V4 1.6: first provider, with the serving ancestor and its facet name. -/
def firstProvider (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : H.ProviderCandidate q :=
  Classical.choose (H.provider_exists_unique q f hf)

/-- P6, V4 1.6: specification of the chosen finite provider. -/
theorem firstProvider_spec (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : H.IsProvider q f (H.firstProvider q f hf) :=
  (Classical.choose_spec (H.provider_exists_unique q f hf)).1

/-- P6, V4 1.6: the serving child at the last boundary height. -/
def servingChild (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : H.Node := H.ancestor q (H.firstProvider q f hf).1

/-- P6, V4 1.6: birth parent, one parent step above the serving child. -/
def birthParent (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : H.Node := H.parentNode (H.servingChild q f hf)

/-- P6, V4 1.6: absolute birth height. -/
def birthHeight (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : ℕ := (H.birthParent q f hf).1

/-- P6, V4 1.6: provider age relative to the original node. -/
def age (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : ℕ := H.birthHeight q f hf - q.1

/-- P6, V4 1.6: the geometric carrier of the first provider. -/
def providerCarrier (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : Set (E d) :=
  (H.servingChild q f hf).2.val.cell (H.servingChild q f hf).1
    (H.firstProvider q f hf).2.val

/-- P6, V4 1.6: exact incidence realization, including the serving role and
its named facet. This fixes the side rather than allowing the opposite orientation. -/
def RealizesProviderIncidence (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (ι : PrimitiveIncidence S) : Prop :=
  ι.ty = (H.birthParent q f hf).2.val.ty ∧
    (⟨ι.ty, ι.left⟩ : S.Role) = H.nodeRole (H.servingChild q f hf) ∧
    ι.leftFacet.val = (H.firstProvider q f hf).2.val ∧
    H.providerCarrier q f hf =
      (H.birthParent q f hf).2.val.prototypeFrame (H.birthHeight q f hf) ''
        (S.σ.symm '' placedSet (S.child ι.ty ι.left).frame ι.leftFacet.val.carrier)

/-- P6, V4 1.6: the actual paired children and their two cell names determine
one primitive incidence. Existence is supplied by whole-facet sibling pairing. -/
theorem provider_incidence_exists (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) :
    ∃! ι : PrimitiveIncidence S, H.RealizesProviderIncidence q f hf ι := by
  sorry

/-- P6, V4 1.6: the finite primitive incidence with its distinguished serving side. -/
def providerIncidence (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : PrimitiveIncidence S :=
  Classical.choose (H.provider_incidence_exists q f hf)

/-- P6, V4 1.6: specification of the chosen incidence, with both paired roles. -/
theorem providerIncidence_spec (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) :
    H.RealizesProviderIncidence q f hf (H.providerIncidence q f hf) :=
  (Classical.choose_spec (H.provider_incidence_exists q f hf)).1

/-- P7, V4 1.7(a): uniqueness of the provider as a serving offset and facet name. -/
theorem provider_unique (q : H.Node) (f : FacetName S q.2.val.ty)
    (v w : H.ProviderCandidate q) (hv : H.IsProvider q f v) (hw : H.IsProvider q f w) :
    v = w := by
  have hf : ¬ H.IsFault q f := by
    intro hfault
    have h : H.boundaryOffsets q f = Set.univ := Set.ext (fun x => ⟨fun _ => trivial, fun _ => hfault x⟩)
    have hv1 := hv.1
    rw [h] at hv1
    have h2 : Set.univ = {r : ℕ | r < v.fst + 1} := hv1
    have contra : v.fst + 1 ∈ Set.univ := Set.mem_univ _
    rw [h2] at contra
    simp at contra
  have h1 := (Classical.choose_spec (H.provider_exists_unique q f hf)).2 v hv
  have h2 := (Classical.choose_spec (H.provider_exists_unique q f hf)).2 w hw
  rw [h1, h2]

/-- P7, V4 1.7(a): restriction to any contained descendant facet preserves the
provider carrier and the exact birth parent; existence of the restricted provider
is part of the conclusion. -/
theorem provider_inherited (q c : H.Node) (r : ℕ) (hc : H.ancestor c r = q)
    (f : FacetName S q.2.val.ty) (g : FacetName S c.2.val.ty)
    (hf : ¬ H.IsFault q f) (hsub : c.2.val.cell c.1 g.val ⊆ q.2.val.cell q.1 f.val) :
    ∃ hg : ¬ H.IsFault c g,
      H.providerCarrier c g hg = H.providerCarrier q f hf ∧
        H.birthParent c g hg = H.birthParent q f hf := by
  sorry

/-- P7, V4 1.7(b): existence of the provider stratum for any cell in the facet. -/
theorem stratum_exists_unique (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (s : CellName S q.2.val.ty)
    (hs : q.2.val.cell q.1 s.val ⊆ q.2.val.cell q.1 f.val) :
    ∃! t : CellName S (H.servingChild q f hf).2.val.ty,
      relint (q.2.val.cell q.1 s.val) ⊆
        relint ((H.servingChild q f hf).2.val.cell (H.servingChild q f hf).1 t.val) := by
  have H_anc := H.ancestor_descendant q (H.firstProvider q f hf).1
  have H_prov := H.firstProvider_spec q f hf
  have H_boundary_eq : H.boundaryOffsets q f = {r | r < (H.firstProvider q f hf).1 + 1} := H_prov.1
  have H_mem : (H.firstProvider q f hf).1 ∈ H.boundaryOffsets q f := by
    rw [H_boundary_eq]
    simp only [Set.mem_setOf_eq, lt_add_iff_pos_right, zero_lt_one]
  have H_boundary : q.2.val.cell q.1 f.val ⊆ frontier ((H.servingChild q f hf).2.val.carrier (H.servingChild q f hf).1) := H_mem
  exact ancestralStratum_exists_unique (H.servingChild q f hf).2.val q.2.val (H.servingChild q f hf).1 q.1 H_anc s
    (Set.Subset.trans hs H_boundary)
/-- P7, V4 1.7(b): the provider stratum map `τ_f`, defined by unique existence. -/
def stratumMap (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (s : CellName S q.2.val.ty)
    (hs : q.2.val.cell q.1 s.val ⊆ q.2.val.cell q.1 f.val) :
    CellName S (H.servingChild q f hf).2.val.ty :=
  Classical.choose (H.stratum_exists_unique q f hf s hs)

/-- P7, V4 1.7(b): characterization, dimension bound, and containment in the provider. -/
theorem stratumMap_spec (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (s : CellName S q.2.val.ty)
    (hs : q.2.val.cell q.1 s.val ⊆ q.2.val.cell q.1 f.val) :
    relint (q.2.val.cell q.1 s.val) ⊆
        relint ((H.servingChild q f hf).2.val.cell (H.servingChild q f hf).1
          (H.stratumMap q f hf s hs).val) ∧
      s.val.dim ≤ (H.stratumMap q f hf s hs).val.dim ∧
      (H.servingChild q f hf).2.val.cell (H.servingChild q f hf).1
        (H.stratumMap q f hf s hs).val ⊆ H.providerCarrier q f hf := by
  sorry

/-- P7, V4 1.7(b): incidence preservation of the provider stratum map. -/
theorem stratumMap_mono (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (s t : CellName S q.2.val.ty)
    (hs : q.2.val.cell q.1 s.val ⊆ q.2.val.cell q.1 f.val)
    (ht : q.2.val.cell q.1 t.val ⊆ q.2.val.cell q.1 f.val)
    (hst : s.val.carrier ⊆ t.val.carrier) :
    (H.stratumMap q f hf s hs).val.carrier ⊆
      (H.stratumMap q f hf t ht).val.carrier := by
  sorry

/-- P7, V4 1.7(b): the facet itself maps to the whole first provider. -/
theorem stratumMap_facet (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (s : CellName S q.2.val.ty) (hs : s.val = f.val) :
    ∃ hsub : q.2.val.cell q.1 s.val ⊆ q.2.val.cell q.1 f.val,
      (H.stratumMap q f hf s hsub).val = (H.firstProvider q f hf).2.val := by
  sorry

/-- P7, V4 1.7(c): an internal child facet is its own provider, of age one. -/
theorem restriction_det_internal (c : H.Node) (f : FacetName S c.2.val.ty)
    (hint : relint (c.2.val.cell c.1 f.val) ⊆
      interior ((H.parentNode c).2.val.carrier (H.parentNode c).1)) :
    ∃ hf : ¬ H.IsFault c f,
      H.providerCarrier c f hf = c.2.val.cell c.1 f.val ∧
        H.birthParent c f hf = H.parentNode c ∧ H.age c f hf = 1 := by
  sorry

/-- P7, V4 1.7(c): inherited finite facets retain provider and birth, gain one
unit of age, and their strata compose with the immediate ancestral strata. -/
theorem restriction_det_inherited (c : H.Node)
    (f : FacetName S (H.parentNode c).2.val.ty) (g : FacetName S c.2.val.ty)
    (hf : ¬ H.IsFault (H.parentNode c) f)
    (hsub : c.2.val.cell c.1 g.val ⊆
      (H.parentNode c).2.val.cell (H.parentNode c).1 f.val) :
    ∃ hg : ¬ H.IsFault c g,
      H.providerCarrier c g hg = H.providerCarrier (H.parentNode c) f hf ∧
      H.birthParent c g hg = H.birthParent (H.parentNode c) f hf ∧
      H.age c g hg = H.age (H.parentNode c) f hf + 1 ∧
      ∀ (s : CellName S c.2.val.ty)
        (hs : c.2.val.cell c.1 s.val ⊆ c.2.val.cell c.1 g.val),
        ∃ (t : CellName S (H.parentNode c).2.val.ty)
          (ht : (H.parentNode c).2.val.cell (H.parentNode c).1 t.val ⊆
            (H.parentNode c).2.val.cell (H.parentNode c).1 f.val),
          relint (c.2.val.cell c.1 s.val) ⊆
            relint ((H.parentNode c).2.val.cell (H.parentNode c).1 t.val) ∧
          (H.servingChild c g hg).2.val.cell (H.servingChild c g hg).1
            (H.stratumMap c g hg s hs).val =
          (H.servingChild (H.parentNode c) f hf).2.val.cell
            (H.servingChild (H.parentNode c) f hf).1
            (H.stratumMap (H.parentNode c) f hf t ht).val := by
  sorry

/-- P7, V4 1.7(c): faults restrict to faults. -/
theorem restriction_det_fault (c : H.Node)
    (f : FacetName S (H.parentNode c).2.val.ty) (g : FacetName S c.2.val.ty)
    (hf : H.IsFault (H.parentNode c) f)
    (hsub : c.2.val.cell c.1 g.val ⊆
      (H.parentNode c).2.val.cell (H.parentNode c).1 f.val) : H.IsFault c g := by
  intro r
  cases r with
  | zero =>
    have hg : g.val ∈ (S.cx c.2.val.ty).cells :=
      (Finset.mem_filter.mp g.property).1
    exact hereditary_trace_step1_cell_frontier c.2.val c.1 g.val hg
  | succ r =>
    have h1 : (H.parentNode c).2.val.cell (H.parentNode c).1 f.val ⊆
        frontier ((H.ancestor (H.parentNode c) r).2.val.carrier
          (H.ancestor (H.parentNode c) r).1) := hf r
    exact hsub.trans h1

end CoherentHierarchy

/-- P7/P17, V4 1.7(d), 1.22: a positive-dimensional full flag ending at a facet.
Vertices are omitted, as in 1.7(d); the edge is indexed by `1`. -/
structure FacetFlag (S : SubstSystem d) (A : S.ι) where
  /-- P7, V4 1.7(d): cell at each positive boundary dimension. -/
  cell : {j : ℕ // 1 ≤ j ∧ j < d} → CellName S A
  /-- P7, V4 1.7(d): exact dimensions. -/
  dimension : ∀ j, (cell j).val.dim = j.val
  /-- P7, V4 1.7(d): nested carriers. -/
  nested : ∀ i j, i.val ≤ j.val → (cell i).val.carrier ⊆ (cell j).val.carrier

namespace CoherentHierarchy

variable {T : Tiling S} (H : CoherentHierarchy S T)

/-- P7, V4 1.7(d): a full flag is active when every stratum is the prescribed
provider cell; carrier equalities avoid dependent casts between serving nodes. -/
def ActiveFlag (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (s : FacetFlag S q.2.val.ty)
    (F : FacetFlag S (H.servingChild q f hf).2.val.ty) : Prop :=
  ∀ j, ∃ hs : q.2.val.cell q.1 (s.cell j).val ⊆ q.2.val.cell q.1 f.val,
    (H.stratumMap q f hf (s.cell j) hs).val = (F.cell j).val

/-- P7, V4 1.7(d): active descendant flags lift through every intermediate
ancestor with exact dimensions and nestedness, and the provider strata stay equal. -/
theorem active_flags_hereditary (q c : H.Node) (r : ℕ) (hc : H.ancestor c r = q)
    (f : FacetName S q.2.val.ty) (g : FacetName S c.2.val.ty)
    (hf : ¬ H.IsFault q f) (hg : ¬ H.IsFault c g)
    (hsub : c.2.val.cell c.1 g.val ⊆ q.2.val.cell q.1 f.val)
    (s : FacetFlag S c.2.val.ty)
    (F : FacetFlag S (H.servingChild c g hg).2.val.ty)
    (ha : H.ActiveFlag c g hg s F) :
    ∃ t : FacetFlag S q.2.val.ty, ∀ j,
      relint (c.2.val.cell c.1 (s.cell j).val) ⊆
        relint (q.2.val.cell q.1 (t.cell j).val) ∧
      ∃ ht : q.2.val.cell q.1 (t.cell j).val ⊆ q.2.val.cell q.1 f.val,
        (H.servingChild q f hf).2.val.cell (H.servingChild q f hf).1
          (H.stratumMap q f hf (t.cell j) ht).val =
        (H.servingChild c g hg).2.val.cell (H.servingChild c g hg).1 (F.cell j).val := by
  sorry

end CoherentHierarchy

/-- P8, V4 1.8: a child facet occurrence inside a specified parent facet. -/
abbrev BoundaryFacet (P : FramedNode S) (n : ℕ) (g : FacetName S P.ty) :=
  {q : Σ i : S.I P.ty, FacetName S (P.child n i).ty //
    (P.child n q.1).cell n q.2.val ⊆ P.cell (n + 1) g.val}

/-- P8, V4 1.8: adjacency through a common listed codimension-two cell. -/
def boundaryFacetAdjacent (P : FramedNode S) (n : ℕ) (g : FacetName S P.ty)
    (a b : BoundaryFacet P n g) : Prop :=
  a ≠ b ∧ ∃ (e : CellName S (P.child n a.val.1).ty)
    (f : CellName S (P.child n b.val.1).ty),
    e.val.dim = d - 2 ∧ f.val.dim = d - 2 ∧
    (P.child n a.val.1).cell n e.val = (P.child n b.val.1).cell n f.val ∧
    (P.child n a.val.1).cell n e.val ⊆ (P.child n a.val.1).cell n a.val.2.val ∧
    (P.child n b.val.1).cell n f.val ⊆ (P.child n b.val.1).cell n b.val.2.val

/-- Step 1 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "transported by
the frame". The height-`n` frame of the child of role `i` is the parent's
height-`n+1` frame after the prescribed child frame and `σ⁻¹`. -/
private theorem boundary_facet_adjacency_step1_child_frame (N : FramedNode S)
    (n : ℕ) (i : S.I N.ty) (x : E d) :
    (N.child n i).prototypeFrame n x =
      N.prototypeFrame (n + 1) (S.σ.symm ((S.child N.ty i).frame x)) := by
  change N.frame (S.placeChild n i ((S.σ ^ n) x)) =
    N.frame ((S.σ ^ (n + 1)) (S.σ.symm ((S.child N.ty i).frame x)))
  congr 1
  rw [S.placeChild_apply]
  simp [linearConj, Child.frame, rigidMotion, pow_succ, zpow_neg,
    LinearEquiv.mul_apply, ← map_add]

/-- Step 1 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "Covering:
`g = φ(F)` ... by (H5) `σF` is a union of placed `(d-1)`-cells of the children ...;
transported by the frame, `g` is a union of facets of children of `A`, each
contained in `g`." -/
private theorem boundary_facet_adjacency_step1_cover (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) :
    (⋃ a : BoundaryFacet P n g, (P.child n a.val.1).cell n a.val.2.val) =
        P.cell (n + 1) g.val := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun a => a.property
  · rintro x ⟨y, hy, rfl⟩
    have hg := Finset.mem_filter.mp g.property
    obtain ⟨f, hf⟩ := S.heredity P.ty g.val hg.1
    have hσy : S.σ y ∈ S.σ '' g.val.carrier := ⟨y, hy, rfl⟩
    rw [hf] at hσy
    obtain ⟨q, hqf, hq⟩ := Set.mem_iUnion₂.mp hσy
    obtain ⟨z, hz, hzy⟩ := hq
    have hqfac : q.2.val ∈ (S.cx (P.child n q.1).ty).facets := by
      refine Finset.mem_filter.mpr ⟨q.2.property.1, ?_⟩
      rw [q.2.property.2, hg.2]
    have hsub : (P.child n q.1).cell n q.2.val ⊆ P.cell (n + 1) g.val := by
      rintro w ⟨u, hu, rfl⟩
      have hmem : (S.child P.ty q.1).frame u ∈ S.σ '' g.val.carrier := by
        rw [hf]
        exact Set.mem_iUnion₂.mpr ⟨q, hqf, ⟨u, hu, rfl⟩⟩
      obtain ⟨v, hv, hvu⟩ := hmem
      refine ⟨v, hv, ?_⟩
      rw [boundary_facet_adjacency_step1_child_frame, ← hvu, S.σ.symm_apply_apply]
    refine Set.mem_iUnion.mpr ⟨⟨⟨q.1, ⟨q.2.val, hqfac⟩⟩, hsub⟩, ⟨z, hz, ?_⟩⟩
    change (P.child n q.1).prototypeFrame n z = P.prototypeFrame (n + 1) y
    rw [boundary_facet_adjacency_step1_child_frame]
    rw [hzy, S.σ.symm_apply_apply]

omit [Fact (2 ≤ d)] in
/-- Step 2 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "transported by
the frame". Relative interiors commute with invertible affine maps. -/
private theorem boundary_facet_adjacency_step2_relint_image (e : E d ≃ᵃ[ℝ] E d)
    (K : Set (E d)) : relint (e '' K) = e '' relint K := by
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

/-- Step 4 of the V4 proof of `boundary_facet_adjacency` (V4 1.8, via 1.1): a
listed cell whose relative interior meets a listed cell is contained in it
(it is the minimal cell of the meeting point). -/
private theorem boundary_facet_adjacency_step4_minimal {A : PolyManifoldDomain d}
    (K : CellComplex A) (e f : Cell d) (he : e ∈ K.cells) (hf : f ∈ K.cells)
    (x : E d) (hx : x ∈ relint e.carrier) (hxf : x ∈ f.carrier) :
    e.carrier ⊆ f.carrier := by
  have hfr : x ∈ frontier A.carrier := by
    rw [← K.cover]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hx⟩
  have hmin : K.minimalCell x hfr = e := by
    have hu := (K.exists_unique_minimalCell x hfr).unique
      (y₁ := ⟨K.minimalCell x hfr, K.minimalCell_mem x hfr⟩) (y₂ := ⟨e, he⟩)
      (K.mem_relint_minimalCell x hfr) hx
    exact congrArg Subtype.val hu
  rw [← hmin]
  exact K.minimalCell_subset x hfr f hf hxf

omit [Fact (2 ≤ d)] in
/-- Step 4 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): a common cell
of two children has one dimension (isometries preserve affine dimension). -/
private theorem boundary_facet_adjacency_step4_dim (φ ψ : Iso d) (e f : Cell d)
    (h : φ '' e.carrier = ψ '' f.carrier) : e.dim = f.dim := by
  have key : ∀ (χ : Iso d) (K : Set (E d)), Module.finrank ℝ (cellDirection (χ '' K)) =
      Module.finrank ℝ (cellDirection K) := by
    intro χ K
    have hs : affineSpan ℝ (χ '' K) =
        (affineSpan ℝ K).map (χ.toAffineEquiv : E d →ᵃ[ℝ] E d) :=
      (AffineSubspace.map_span (χ.toAffineEquiv : E d →ᵃ[ℝ] E d) K).symm
    unfold cellDirection
    rw [hs, AffineSubspace.map_direction]
    exact LinearEquiv.finrank_map_eq χ.toAffineEquiv.linear _
  rw [← e.flat.dimension, ← f.flat.dimension, ← key φ e.carrier, ← key ψ f.carrier, h]

/-- Step 2 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "two child
facets inside `g` from the same child have disjoint relative interiors by (H2)".
Distinct listed facets of one child have disjoint placed relative interiors. -/
private theorem boundary_facet_adjacency_step2_same_child (P : FramedNode S) (n : ℕ)
    (i : S.I P.ty) (e f : FacetName S (P.child n i).ty) (hef : e ≠ f) :
    Disjoint (relint ((P.child n i).cell n e.val))
      (relint ((P.child n i).cell n f.val)) := by
  change Disjoint (relint ((P.child n i).prototypeFrame n '' e.val.carrier))
    (relint ((P.child n i).prototypeFrame n '' f.val.carrier))
  rw [boundary_facet_adjacency_step2_relint_image,
    boundary_facet_adjacency_step2_relint_image,
    Set.disjoint_image_iff ((P.child n i).prototypeFrame n).injective]
  exact (S.cx _).relint_disjoint _ (Finset.mem_filter.mp e.property).1 _
    (Finset.mem_filter.mp f.property).1 (fun h => hef (Subtype.ext h))

omit [Fact (2 ≤ d)] in
/-- Step 2 of the V4 proof of `boundary_facet_adjacency` (V4 1.8, via Lemma 1.0(a)):
"a common relative-interior point would make both children lie on the same side ...
contradicting disjoint interiors" — the local point-reflection argument. Two closed sets
which near `q` are closed half-balls `{0 ≤ fₖ}` (with `fₖ` odd under the point reflection
at `q`) and have disjoint interiors cover a ball around `q`: a point outside both would
reflect to a point inside both interiors. Hence `q` is interior to any common superset. -/
private theorem boundary_facet_adjacency_step2_reflect_cover (W C₁ C₂ : Set (E d))
    (q : E d) (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (f₁ f₂ : E d → ℝ)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (ho₁ : ∀ y, f₁ (q + (q - y)) = - f₁ y) (ho₂ : ∀ y, f₂ (q + (q - y)) = - f₂ y)
    (hs₁ : C₁ ∩ ball q r₁ = {y | 0 ≤ f₁ y} ∩ ball q r₁)
    (hs₂ : C₂ ∩ ball q r₂ = {y | 0 ≤ f₂ y} ∩ ball q r₂)
    (h₁W : C₁ ⊆ W) (h₂W : C₂ ⊆ W) (hdisj : Disjoint (interior C₁) (interior C₂)) :
    q ∈ interior W := by
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have hb₁ : ball q (min r₁ r₂) ⊆ ball q r₁ := ball_subset_ball (min_le_left _ _)
  have hb₂ : ball q (min r₁ r₂) ⊆ ball q r₂ := ball_subset_ball (min_le_right _ _)
  have hin₁ : ∀ y ∈ ball q (min r₁ r₂), 0 ≤ f₁ y → y ∈ C₁ := by
    intro y hy h
    have hy1 : y ∈ C₁ ∩ ball q r₁ := by
      rw [hs₁]
      exact ⟨h, hb₁ hy⟩
    exact hy1.1
  have hin₂ : ∀ y ∈ ball q (min r₁ r₂), 0 ≤ f₂ y → y ∈ C₂ := by
    intro y hy h
    have hy2 : y ∈ C₂ ∩ ball q r₂ := by
      rw [hs₂]
      exact ⟨h, hb₂ hy⟩
    exact hy2.1
  rw [mem_interior]
  refine ⟨ball q (min r₁ r₂), ?_, isOpen_ball, mem_ball_self hr⟩
  intro y hy
  by_contra hyW
  have h₁ : f₁ y < 0 := not_le.mp fun h => hyW (h₁W (hin₁ y hy h))
  have h₂ : f₂ y < 0 := not_le.mp fun h => hyW (h₂W (hin₂ y hy h))
  have hy'b : q + (q - y) ∈ ball q (min r₁ r₂) := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, ← dist_eq_norm, dist_comm]
    exact hy
  let U : Set (E d) := ({z | 0 < f₁ z} ∩ {z | 0 < f₂ z}) ∩ ball q (min r₁ r₂)
  have hU : IsOpen U :=
    ((isOpen_lt continuous_const hf₁).inter (isOpen_lt continuous_const hf₂)).inter
      isOpen_ball
  have hy'U : q + (q - y) ∈ U := by
    refine ⟨⟨?_, ?_⟩, hy'b⟩
    · show 0 < f₁ (q + (q - y))
      rw [ho₁]
      linarith
    · show 0 < f₂ (q + (q - y))
      rw [ho₂]
      linarith
  have hU₁ : U ⊆ C₁ := fun z hz => hin₁ z hz.2 hz.1.1.le
  have hU₂ : U ⊆ C₂ := fun z hz => hin₂ z hz.2 hz.1.2.le
  exact Set.disjoint_left.mp hdisj (interior_maximal hU₁ hU hy'U)
    (interior_maximal hU₂ hU hy'U)

/-- Step 2 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "Lemma 1.0(a) ...
at a point of `relint`" of a facet, transported by an isometric child frame: near the
image of a relative-interior facet point, the placed prototile is a closed half-ball
`{0 ≤ f}` with `f` continuous and odd under the point reflection at that point. -/
private theorem boundary_facet_adjacency_step2_child_halfball (A : S.ι) (φ : Iso d)
    (F : Cell d) (hF : F ∈ (S.cx A).facets) (x : E d) (hx : x ∈ relint F.carrier) :
    ∃ r : ℝ, 0 < r ∧ ∃ f : E d → ℝ, Continuous f ∧
      (∀ y, f (φ x + (φ x - y)) = - f y) ∧
      placedSet φ (S.proto A).carrier ∩ ball (φ x) r = {y | 0 ≤ f y} ∩ ball (φ x) r := by
  obtain ⟨r, hr, v, -, -, -, hside⟩ := facet_halfball (S.proto A) (S.cx A) F hF x hx
  refine ⟨r, hr, fun y => inner ℝ v (φ.symm y - x), ?_, ?_, ?_⟩
  · exact continuous_const.inner (φ.symm.continuous.sub continuous_const)
  · intro y
    show inner ℝ v (φ.symm (φ x + (φ x - y)) - x) = - inner ℝ v (φ.symm y - x)
    rw [← inner_neg_right]
    congr 1
    have k1 := (φ.symm.toAffineEquiv.toAffineMap).linearMap_vsub (φ x + (φ x - y)) (φ x)
    have k2 := (φ.symm.toAffineEquiv.toAffineMap).linearMap_vsub y (φ x)
    simp only [vsub_eq_sub, add_sub_cancel_left, AffineEquiv.coe_toAffineMap,
      AffineIsometryEquiv.coe_toAffineEquiv, AffineIsometryEquiv.symm_apply_apply] at k1 k2
    rw [← k1, ← k2, ← map_neg, neg_sub]
  · ext y
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, hwB⟩
      have hwB' : w ∈ ball x r := by
        rw [mem_ball, ← φ.dist_map w x]
        exact hwB
      have hw2 : w ∈ (S.proto A).carrier ∩ ball x r := ⟨hw, hwB'⟩
      rw [hside] at hw2
      refine ⟨?_, hwB⟩
      show 0 ≤ inner ℝ v (φ.symm (φ w) - x)
      rw [φ.symm_apply_apply]
      exact hw2.1
    · rintro ⟨hy0, hyB⟩
      have hwB' : φ.symm y ∈ ball x r := by
        rw [mem_ball, ← φ.dist_map (φ.symm y) x, φ.apply_symm_apply]
        exact hyB
      have hw2 : φ.symm y ∈ {z | 0 ≤ inner ℝ v (z - x)} ∩ ball x r := ⟨hy0, hwB'⟩
      rw [← hside] at hw2
      exact ⟨⟨φ.symm y, hw2.1, φ.apply_symm_apply y⟩, hyB⟩

/-- Step 2 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "from distinct
children `C, C'` a common relative-interior point would make both children lie on
the same side of `aff g` as `A` (Lemma 1.0(a) for `A` at a point of `relint g`, and
`C, C' ⊆ A`), contradicting disjoint interiors." -/
private theorem boundary_facet_adjacency_step2_distinct_children (P : FramedNode S)
    (n : ℕ) (g : FacetName S P.ty) (a b : BoundaryFacet P n g)
    (hab : a.val.1 ≠ b.val.1) :
    Disjoint (relint ((P.child n a.val.1).cell n a.val.2.val))
      (relint ((P.child n b.val.1).cell n b.val.2.val)) := by
  obtain ⟨⟨i, F⟩, hF⟩ := a
  obtain ⟨⟨j, G⟩, hG⟩ := b
  dsimp only at hab hF hG ⊢
  rw [Set.disjoint_left]
  intro p hpF hpG
  change p ∈ relint ((P.child n i).prototypeFrame n '' F.val.carrier) at hpF
  change p ∈ relint ((P.child n j).prototypeFrame n '' G.val.carrier) at hpG
  rw [boundary_facet_adjacency_step2_relint_image] at hpF hpG
  obtain ⟨x, hx, rfl⟩ := hpF
  obtain ⟨z, hz, hzx⟩ := hpG
  have hzx' : (S.child P.ty j).frame z = (S.child P.ty i).frame x := by
    change (P.child n j).prototypeFrame n z = (P.child n i).prototypeFrame n x at hzx
    rw [boundary_facet_adjacency_step1_child_frame,
      boundary_facet_adjacency_step1_child_frame] at hzx
    exact S.σ.symm.injective ((P.prototypeFrame (n + 1)).injective hzx)
  obtain ⟨r₁, hr₁, f₁, hf₁, ho₁, hs₁⟩ := boundary_facet_adjacency_step2_child_halfball
    (P.child n i).ty (S.child P.ty i).frame F.val F.property x hx
  obtain ⟨r₂, hr₂, f₂, hf₂, ho₂, hs₂⟩ := boundary_facet_adjacency_step2_child_halfball
    (P.child n j).ty (S.child P.ty j).frame G.val G.property z hz
  rw [hzx'] at ho₂ hs₂
  have hsubW : ∀ k : S.I P.ty, placedSet (S.child P.ty k).frame
      (S.proto (S.child P.ty k).ty).carrier ⊆ S.σ '' (S.proto P.ty).carrier := by
    intro k
    rw [S.children_cover]
    exact Set.subset_iUnion (fun l : S.I P.ty =>
      placedSet (S.child P.ty l).frame (S.proto (S.child P.ty l).ty).carrier) k
  have hint := boundary_facet_adjacency_step2_reflect_cover (S.σ '' (S.proto P.ty).carrier)
    _ _ _ r₁ r₂ hr₁ hr₂ f₁ f₂ hf₁ hf₂ ho₁ ho₂ hs₁ hs₂ (hsubW i) (hsubW j)
    (S.children_disjoint P.ty hab)
  have hpg : (P.child n i).prototypeFrame n x ∈ P.cell (n + 1) g.val :=
    hF ⟨x, intrinsicInterior_subset hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hpg
  rw [boundary_facet_adjacency_step1_child_frame] at hyx
  have hyq : S.σ y = (S.child P.ty i).frame x := by
    rw [(P.prototypeFrame (n + 1)).injective hyx]
    exact S.σ.apply_symm_apply _
  have hgc : g.val ∈ (S.cx P.ty).cells := (Finset.mem_filter.mp g.property).1
  have hyfr : y ∈ frontier (S.proto P.ty).carrier := by
    rw [← (S.cx P.ty).carriers_cover]
    exact Set.mem_iUnion₂.mpr ⟨g.val, hgc, hy⟩
  have hfr : S.σ y ∈ frontier (S.σ '' (S.proto P.ty).carrier) := by
    let H := S.σ.toContinuousLinearEquiv.toHomeomorph
    change H y ∈ frontier (H '' (S.proto P.ty).carrier)
    rw [← H.image_frontier]
    exact ⟨y, hyfr, rfl⟩
  rw [hyq] at hfr
  exact Set.disjoint_left.mp disjoint_interior_frontier hint hfr

/-- Step 4 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "Each crossing
passes between two child facets sharing a relatively open piece of a `(d-2)`-cell."
If `p` is in the relative interior of a `(d-2)`-cell `e ⊆ a` of `a`'s child and
`p` lies in `b`, then `e` is (by minimality, and by (H6) for a different child) a
common listed `(d-2)`-cell of both facets. -/
private theorem boundary_facet_adjacency_step4_crossing (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) (a b : BoundaryFacet P n g) (hab : a ≠ b)
    (e : CellName S (P.child n a.val.1).ty) (he : e.val.dim = d - 2)
    (hea : (P.child n a.val.1).cell n e.val ⊆ (P.child n a.val.1).cell n a.val.2.val)
    (p : E d) (hp : p ∈ relint ((P.child n a.val.1).cell n e.val))
    (hpb : p ∈ (P.child n b.val.1).cell n b.val.2.val) :
    boundaryFacetAdjacent P n g a b := by
  obtain ⟨⟨i, F⟩, hF⟩ := a
  obtain ⟨⟨j, G⟩, hG⟩ := b
  dsimp only at e he hea hp hpb ⊢
  change p ∈ relint ((P.child n i).prototypeFrame n '' e.val.carrier) at hp
  rw [boundary_facet_adjacency_step2_relint_image] at hp
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨z, hz, hzx⟩ := hpb
  have hGc := (Finset.mem_filter.mp G.property).1
  by_cases hij : i = j
  · subst hij
    have hxG : x ∈ G.val.carrier := by
      rw [((P.child n i).prototypeFrame n).injective hzx] at hz
      exact hz
    refine ⟨hab, e, e, he, he, rfl, hea, ?_⟩
    have hsub := boundary_facet_adjacency_step4_minimal _ _ _ e.property hGc x hx hxG
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, hsub hu, rfl⟩
  · have hzx' : (S.child P.ty j).frame z = (S.child P.ty i).frame x := by
      change (P.child n j).prototypeFrame n z = (P.child n i).prototypeFrame n x at hzx
      rw [boundary_facet_adjacency_step1_child_frame,
        boundary_facet_adjacency_step1_child_frame] at hzx
      exact S.σ.symm.injective ((P.prototypeFrame (n + 1)).injective hzx)
    have hfront : ∀ (k : S.ι) (c : Cell d), c ∈ (S.cx k).cells →
        c.carrier ⊆ (S.proto k).carrier := by
      intro k c hc w hw
      apply (S.proto k).compact.isClosed.frontier_subset
      rw [← (S.cx k).carriers_cover]
      exact Set.mem_iUnion₂.mpr ⟨c, hc, hw⟩
    have hxA := hfront _ e.val e.property (intrinsicInterior_subset hx)
    have hzA := hfront _ G.val hGc hz
    have hxe : (S.child P.ty i).frame.symm ((S.child P.ty i).frame x) ∈
        relint e.val.carrier := by
      rw [(S.child P.ty i).frame.symm_apply_apply]
      exact hx
    obtain ⟨f, hf, hfe⟩ := S.sibling_conformity P.ty i j hij ((S.child P.ty i).frame x)
      ⟨x, hxA, rfl⟩ ⟨z, hzA, hzx'⟩ e.val e.property hxe (le_of_eq he)
    have himg : ∀ (k : S.I P.ty) (c : Cell d), (P.child n k).cell n c =
        (fun w => P.prototypeFrame (n + 1) (S.σ.symm w)) ''
          placedSet (S.child P.ty k).frame c.carrier := by
      intro k c
      ext w
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨_, ⟨u, hu, rfl⟩, (boundary_facet_adjacency_step1_child_frame P n k u).symm⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨u, hu, boundary_facet_adjacency_step1_child_frame P n k u⟩
    have hcell : (P.child n i).cell n e.val = (P.child n j).cell n f := by
      rw [himg, himg, hfe]
    have hfdim : f.dim = d - 2 := by
      rw [← boundary_facet_adjacency_step4_dim _ _ _ _ hfe, he]
    have hrel : (S.child P.ty i).frame.toAffineEquiv '' relint e.val.carrier =
        (S.child P.ty j).frame.toAffineEquiv '' relint f.carrier := by
      rw [← boundary_facet_adjacency_step2_relint_image,
        ← boundary_facet_adjacency_step2_relint_image]
      exact congrArg relint hfe
    have hzf : z ∈ relint f.carrier := by
      have hm : (S.child P.ty j).frame.toAffineEquiv z ∈
          (S.child P.ty j).frame.toAffineEquiv '' relint f.carrier := by
        rw [← hrel]
        exact ⟨x, hx, hzx'.symm⟩
      exact (S.child P.ty j).frame.toAffineEquiv.injective.mem_set_image.mp hm
    refine ⟨hab, e, ⟨f, hf⟩, he, hfdim, hcell, hea, ?_⟩
    have hsub := boundary_facet_adjacency_step4_minimal _ _ _ hf hGc z hzf hz
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, hsub hu, rfl⟩

/-- Step 2 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "Disjointness of
relative interiors": the same-child case (H2) and the distinct-children case combined. -/
private theorem boundary_facet_adjacency_step2_pairwise (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) :
    Pairwise (fun a b : BoundaryFacet P n g => Disjoint
      (relint ((P.child n a.val.1).cell n a.val.2.val))
      (relint ((P.child n b.val.1).cell n b.val.2.val))) := by
  intro a b hab
  by_cases hi : a.val.1 = b.val.1
  · obtain ⟨⟨i, e⟩, hae⟩ := a
    obtain ⟨⟨j, f⟩, hbf⟩ := b
    dsimp only at hi
    subst hi
    have hef : e ≠ f := by
      intro h
      subst h
      exact hab rfl
    exact boundary_facet_adjacency_step2_same_child P n i e f hef
  · exact boundary_facet_adjacency_step2_distinct_children P n g a b hi

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "The lower-dimensional
cells of the child facets form a finite polyhedral set `Z` of dimension `≤ d-2` in the
`(d-1)`-dimensional `relint g`" — affine dimensions are invariant under the full affine
frames (including the anisotropic inflation). -/
private theorem boundary_facet_adjacency_step3_finrank_image (φ : E d ≃ᵃ[ℝ] E d)
    (K : Set (E d)) :
    Module.finrank ℝ (cellDirection (φ '' K)) = Module.finrank ℝ (cellDirection K) := by
  have hs : affineSpan ℝ (φ '' K) = (affineSpan ℝ K).map (φ : E d →ᵃ[ℝ] E d) :=
    (AffineSubspace.map_span (φ : E d →ᵃ[ℝ] E d) K).symm
  unfold cellDirection
  rw [hs, AffineSubspace.map_direction]
  exact LinearEquiv.finrank_map_eq φ.linear _

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `boundary_facet_adjacency` (V4 1.8, (H2)): `relint g` is
open in `aff g`: a point of the relative interior has a ball in the affine hull around it
inside the relative interior. -/
private theorem boundary_facet_adjacency_step3_relint_ball (K : Set (E d)) (u : E d)
    (hu : u ∈ relint K) :
    ∃ δ > 0, ∀ z ∈ affineSpan ℝ K, dist z u < δ → z ∈ relint K := by
  rw [relint, mem_intrinsicInterior] at hu
  obtain ⟨y, hy, hyu⟩ := hu
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hy
  refine ⟨δ, hδ, fun z hz hzd => ?_⟩
  show z ∈ intrinsicInterior ℝ K
  rw [mem_intrinsicInterior]
  refine ⟨⟨z, hz⟩, hball ?_, rfl⟩
  rw [Metric.mem_ball, Subtype.dist_eq, hyu]
  exact hzd

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "generic
perturbation" — near any point `y` of an affine subspace `A` there is a point of `A`
outside finitely many affine hulls of dimension below `dim A` (move along a line of `A`
whose direction lies in none of their directions; each hull meets it at most once). -/
private theorem boundary_facet_adjacency_step3_generic_point {ι : Type*} [Finite ι]
    (A : AffineSubspace ℝ (E d)) (y : E d) (hy : y ∈ A) (ε : ℝ) (hε : 0 < ε)
    (M : ι → Set (E d))
    (hM : ∀ i, Module.finrank ℝ (cellDirection (M i)) < Module.finrank ℝ A.direction) :
    ∃ c ∈ A, dist c y < ε ∧ ∀ i, c ∉ affineSpan ℝ (M i) := by
  obtain ⟨w, hw⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun i => (affineSpan ℝ (M i)).direction.comap A.direction.subtype)
    (fun i htop => by
      have hle : A.direction ≤ (affineSpan ℝ (M i)).direction := by
        intro u hu
        have hmem : (⟨u, hu⟩ : A.direction) ∈
            (affineSpan ℝ (M i)).direction.comap A.direction.subtype := by
          have htop' : (affineSpan ℝ (M i)).direction.comap A.direction.subtype = ⊤ := htop
          rw [htop']
          exact Submodule.mem_top
        simpa using hmem
      have h1 := Submodule.finrank_mono hle
      have h2 := hM i
      unfold cellDirection at h2
      omega)
  have hvZ : ∀ i, (w : E d) ∉ (affineSpan ℝ (M i)).direction := fun i h =>
    hw i (by simpa using h)
  have hbad : ∀ i, {t : ℝ | t • (w : E d) + y ∈ affineSpan ℝ (M i)}.Subsingleton := by
    intro i s hs t ht
    have hs' : s • (w : E d) + y ∈ affineSpan ℝ (M i) := hs
    have ht' : t • (w : E d) + y ∈ affineSpan ℝ (M i) := ht
    by_contra hst
    have hdir := AffineSubspace.vsub_mem_direction hs' ht'
    have heq : (s • (w : E d) + y) -ᵥ (t • (w : E d) + y) = (s - t) • (w : E d) := by
      rw [vsub_eq_sub, sub_smul]
      abel
    rw [heq] at hdir
    apply hvZ i
    have hm := Submodule.smul_mem _ (s - t)⁻¹ hdir
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hst), one_smul] at hm
  have hfin : {t : ℝ | ∃ i, t • (w : E d) + y ∈ affineSpan ℝ (M i)}.Finite := by
    have hU : {t : ℝ | ∃ i, t • (w : E d) + y ∈ affineSpan ℝ (M i)} =
        ⋃ i, {t : ℝ | t • (w : E d) + y ∈ affineSpan ℝ (M i)} := by
      ext t
      simp
    rw [hU]
    exact Set.finite_iUnion fun i => (hbad i).finite
  have hn0 : 0 < ‖(w : E d)‖ + 1 := by positivity
  have hη0 : 0 < ε / (‖(w : E d)‖ + 1) := div_pos hε hn0
  obtain ⟨t, ⟨ht0, htη⟩, htbad⟩ := ((Set.Ioo_infinite hη0).diff hfin).nonempty
  have hdist : dist (t • (w : E d) + y) y < ε := by
    rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg ht0.le]
    have h1 : t * ‖(w : E d)‖ ≤ t * (‖(w : E d)‖ + 1) := by
      nlinarith [norm_nonneg (w : E d)]
    have h2 : t * (‖(w : E d)‖ + 1) < ε / (‖(w : E d)‖ + 1) * (‖(w : E d)‖ + 1) :=
      mul_lt_mul_of_pos_right htη hn0
    rw [div_mul_cancel₀ _ hn0.ne'] at h2
    linarith
  exact ⟨t • (w : E d) + y,
    AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t w.property) hy,
    hdist, fun i hi => htbad ⟨i, hi⟩⟩

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): the join of a point
and a set has affine dimension at most one more. -/
private theorem boundary_facet_adjacency_step3_join_finrank (y : E d) (s : Set (E d)) :
    Module.finrank ℝ (cellDirection (insert y s)) ≤
      Module.finrank ℝ (cellDirection s) + 1 := by
  unfold cellDirection
  rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · rw [insert_empty_eq, direction_affineSpan, vectorSpan_singleton, finrank_bot]
    omega
  · rw [← affineSpan_insert_affineSpan,
      AffineSubspace.direction_affineSpan_insert (mem_affineSpan ℝ hp)]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℝ {y -ᵥ p})
      (affineSpan ℝ s).direction
    have h2 : Module.finrank ℝ (Submodule.span ℝ ({y -ᵥ p} : Set (E d))) ≤ 1 :=
      (finrank_span_le_card ({y -ᵥ p} : Set (E d))).trans (by simp)
    omega

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "its subset of
dimension `≤ d-3` can be avoided by a generic perturbation" — genericity: a finite union
of sets whose affine hulls have dimension below `dim aff K` is nowhere dense in
`relint K`, so the points of `relint K` off that union are dense in `relint K`.
(No convexity is needed: `relint K` is open in `aff K` and each `aff Zᵢ ∩ aff K` is a
proper affine subspace of `aff K`.) -/
private theorem boundary_facet_adjacency_step3_generic_dense {ι : Type*} [Finite ι]
    (K : Set (E d)) (Z : ι → Set (E d))
    (hZ : ∀ i, Module.finrank ℝ (cellDirection (Z i)) <
      Module.finrank ℝ (cellDirection K)) :
    relint K ⊆ closure (relint K \ ⋃ i, Z i) := by
  intro x hx
  obtain ⟨δ, hδ, hball⟩ := boundary_facet_adjacency_step3_relint_ball K x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hxA : x ∈ affineSpan ℝ K := subset_affineSpan ℝ K (intrinsicInterior_subset hx)
  obtain ⟨c, hcA, hcd, hcZ⟩ := boundary_facet_adjacency_step3_generic_point
    (affineSpan ℝ K) x hxA (min δ ε) (lt_min hδ hε) Z hZ
  refine ⟨c, ⟨hball c hcA (lt_of_lt_of_le hcd (min_le_left _ _)), ?_⟩, ?_⟩
  · intro h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact hcZ i (subset_affineSpan ℝ _ hi)
  · rw [dist_comm]
    exact lt_of_lt_of_le hcd (min_le_right _ _)

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "Join two points ...
by a polygonal path in `relint g`" — the path is assembled from local pieces: a dense
subset `W` of a connected set `U` is connected as soon as every point of `U` has an open
neighbourhood meeting `W` in a connected set (pure topology). -/
private theorem boundary_facet_adjacency_step3_local_to_global {X : Type*}
    [TopologicalSpace X] (U W : Set X) (hWU : W ⊆ U) (hUW : U ⊆ closure W)
    (hU : IsPreconnected U)
    (hloc : ∀ u ∈ U, ∃ O : Set X, IsOpen O ∧ u ∈ O ∧ IsPreconnected (O ∩ W)) :
    IsPreconnected W := by
  intro u v hu hv hcov hWu hWv
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hside : ∀ O : Set X, IsPreconnected (O ∩ W) → O ∩ W ⊆ u ∨ O ∩ W ⊆ v := by
    intro O hO
    refine (isPreconnected_iff_subset_of_disjoint.mp hO) u v hu hv
      (fun z hz => hcov hz.2) ?_
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hz' : z ∈ W ∩ (u ∩ v) := ⟨hz.1.2, hz.2⟩
    rw [hne] at hz'
    exact hz'
  let U₁ : Set X := ⋃₀ {O | IsOpen O ∧ IsPreconnected (O ∩ W) ∧ O ∩ W ⊆ u}
  let U₂ : Set X := ⋃₀ {O | IsOpen O ∧ IsPreconnected (O ∩ W) ∧ O ∩ W ⊆ v}
  have hU₁ : IsOpen U₁ := isOpen_sUnion fun O hO => hO.1
  have hU₂ : IsOpen U₂ := isOpen_sUnion fun O hO => hO.1
  have hmem : ∀ x ∈ U, x ∈ U₁ ∨ x ∈ U₂ := by
    intro x hx
    obtain ⟨O, hO, hxO, hOW⟩ := hloc x hx
    rcases hside O hOW with h | h
    · exact Or.inl (Set.mem_sUnion.mpr ⟨O, ⟨hO, hOW, h⟩, hxO⟩)
    · exact Or.inr (Set.mem_sUnion.mpr ⟨O, ⟨hO, hOW, h⟩, hxO⟩)
  have hcontra : ∀ w ∈ W, w ∈ u → w ∈ v → False := by
    intro w hw hwu hwv
    have hw' : w ∈ W ∩ (u ∩ v) := ⟨hw, hwu, hwv⟩
    rw [hne] at hw'
    exact hw'
  obtain ⟨x, hxU, hx₁, hx₂⟩ := hU U₁ U₂ hU₁ hU₂ (fun x hx => hmem x hx)
    (by
      obtain ⟨w, hwW, hwu⟩ := hWu
      refine ⟨w, hWU hwW, ?_⟩
      rcases hmem w (hWU hwW) with h | h
      · exact h
      · obtain ⟨O, ⟨-, -, hOv⟩, hwO⟩ := Set.mem_sUnion.mp h
        exact (hcontra w hwW hwu (hOv ⟨hwO, hwW⟩)).elim)
    (by
      obtain ⟨w, hwW, hwv⟩ := hWv
      refine ⟨w, hWU hwW, ?_⟩
      rcases hmem w (hWU hwW) with h | h
      · obtain ⟨O, ⟨-, -, hOu⟩, hwO⟩ := Set.mem_sUnion.mp h
        exact (hcontra w hwW (hOu ⟨hwO, hwW⟩) hwv).elim
      · exact h)
  obtain ⟨O₁, ⟨hO₁, -, hO₁u⟩, hxO₁⟩ := Set.mem_sUnion.mp hx₁
  obtain ⟨O₂, ⟨hO₂, -, hO₂v⟩, hxO₂⟩ := Set.mem_sUnion.mp hx₂
  obtain ⟨w, ⟨hw₁, hw₂⟩, hwW⟩ :=
    mem_closure_iff.mp (hUW hxU) _ (hO₁.inter hO₂) ⟨hxO₁, hxO₂⟩
  exact hcontra w hwW (hO₁u ⟨hw₁, hwW⟩) (hO₂v ⟨hw₂, hwW⟩)

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "its subset of
dimension `≤ d-3` can be avoided by a generic perturbation of the path" — the local,
convex case: a ball of an affine subspace `A`, minus finitely many sets whose affine hulls
have codimension at least two in `A`, is connected (join any two of its points through a
generic centre `c`; the segments `[x, c]`, `[c, y]` miss the removed sets because `c`
avoids the joins `aff(x ∪ Zᵢ)`, which are proper in `A`). -/
private theorem boundary_facet_adjacency_step3_ball_avoid {ι : Type*} [Finite ι]
    (A : AffineSubspace ℝ (E d)) (x : E d) (δ : ℝ) (Z : ι → Set (E d))
    (hZ : ∀ i, Module.finrank ℝ (cellDirection (Z i)) + 2 ≤
      Module.finrank ℝ A.direction) :
    IsPreconnected ((Metric.ball x δ ∩ (A : Set (E d))) \ ⋃ i, Z i) := by
  apply isPreconnected_of_forall_pair
  intro y hy z hz
  have hyb : y ∈ Metric.ball x δ := hy.1.1
  have hε : 0 < δ - dist y x := sub_pos.mpr (Metric.mem_ball.mp hyb)
  obtain ⟨c, hcA, hcd, hcM⟩ := boundary_facet_adjacency_step3_generic_point A y hy.1.2
    (δ - dist y x) hε
    (Sum.elim (fun i => insert y (Z i)) (fun i => insert z (Z i))) (fun q => by
      cases q with
      | inl i =>
        have h1 := boundary_facet_adjacency_step3_join_finrank y (Z i)
        have h2 := hZ i
        simp only [Sum.elim_inl]
        omega
      | inr i =>
        have h1 := boundary_facet_adjacency_step3_join_finrank z (Z i)
        have h2 := hZ i
        simp only [Sum.elim_inr]
        omega)
  have hcb : c ∈ Metric.ball x δ := by
    rw [Metric.mem_ball]
    have := dist_triangle c y x
    linarith
  have hconv : Convex ℝ (Metric.ball x δ ∩ (A : Set (E d))) :=
    (convex_ball x δ).inter A.convex
  have hseg : ∀ p, p ∈ (Metric.ball x δ ∩ (A : Set (E d))) \ ⋃ i, Z i →
      (∀ i, c ∉ affineSpan ℝ (insert p (Z i))) →
      segment ℝ p c ⊆ (Metric.ball x δ ∩ (A : Set (E d))) \ ⋃ i, Z i := by
    intro p hp hpc q hq
    refine ⟨hconv.segment_subset hp.1 ⟨hcb, hcA⟩ hq, ?_⟩
    intro hqZ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hqZ
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hq
    by_cases hb0 : b = 0
    · subst hb0
      have ha1 : a = 1 := by linarith
      subst ha1
      apply hp.2
      exact Set.mem_iUnion.mpr ⟨i, by simpa using hi⟩
    · apply hpc i
      have hpS : p ∈ affineSpan ℝ (insert p (Z i)) :=
        subset_affineSpan ℝ _ (Set.mem_insert _ _)
      have hqS : a • p + b • c ∈ affineSpan ℝ (insert p (Z i)) :=
        subset_affineSpan ℝ _ (Set.mem_insert_of_mem _ hi)
      have hdir := AffineSubspace.vsub_mem_direction hqS hpS
      have hm := Submodule.smul_mem _ b⁻¹ hdir
      have heq : b⁻¹ • ((a • p + b • c) -ᵥ p) +ᵥ p = c := by
        rw [vsub_eq_sub, vadd_eq_add]
        have ha' : a = 1 - b := by linarith
        subst ha'
        rw [show (1 - b) • p + b • c - p = b • (c - p) by
          rw [sub_smul, one_smul, smul_sub]
          abel]
        rw [smul_smul, inv_mul_cancel₀ hb0, one_smul, sub_add_cancel]
      rw [← heq]
      exact AffineSubspace.vadd_mem_of_mem_direction hm hpS
  refine ⟨segment ℝ y c ∪ segment ℝ c z, Set.union_subset
    (hseg y hy fun i => hcM (Sum.inl i)) ?_, Or.inl (left_mem_segment ℝ y c),
    Or.inr (right_mem_segment ℝ c z), ?_⟩
  · rw [segment_symm]
    exact hseg z hz fun i => hcM (Sum.inr i)
  · exact (convex_segment y c).isPreconnected.union c (right_mem_segment ℝ y c)
      (left_mem_segment ℝ c z) (convex_segment c z).isPreconnected

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "`relint g` is
connected (H2). Join two points `x, y` ... by a polygonal path in `relint g`. ... its
subset of dimension `≤ d-3` can be avoided by a generic perturbation of the path" —
removing from a connected relatively open set finitely many sets whose affine hulls have
codimension at least two (in `aff K`) keeps it connected. -/
private theorem boundary_facet_adjacency_step3_codim_two_connected {ι : Type*} [Finite ι]
    (K : Set (E d)) (hK : IsPreconnected (relint K)) (Z : ι → Set (E d))
    (hZ : ∀ i, Module.finrank ℝ (cellDirection (Z i)) + 2 ≤
      Module.finrank ℝ (cellDirection K)) :
    IsPreconnected (relint K \ ⋃ i, Z i) := by
  have hdense := boundary_facet_adjacency_step3_generic_dense K Z (fun i => by
    have := hZ i
    omega)
  refine boundary_facet_adjacency_step3_local_to_global (relint K) (relint K \ ⋃ i, Z i)
    Set.diff_subset hdense hK ?_
  intro u hu
  obtain ⟨δ, hδ, hball⟩ := boundary_facet_adjacency_step3_relint_ball K u hu
  refine ⟨Metric.ball u δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_⟩
  have heq : Metric.ball u δ ∩ (relint K \ ⋃ i, Z i) =
      (Metric.ball u δ ∩ (affineSpan ℝ K : Set (E d))) \ ⋃ i, Z i := by
    ext z
    constructor
    · rintro ⟨hz1, hz2, hz3⟩
      exact ⟨⟨hz1, subset_affineSpan ℝ K (intrinsicInterior_subset hz2)⟩, hz3⟩
    · rintro ⟨⟨hz1, hz2⟩, hz3⟩
      exact ⟨hz1, hball z hz2 (Metric.mem_ball.mp hz1), hz3⟩
  rw [heq]
  exact boundary_facet_adjacency_step3_ball_avoid _ u δ Z hZ

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): the avoiding paths may
start and end at arbitrary points of `g` off the codimension-two set: a regular closed
cell with connected relative interior stays connected after removing finitely many sets
of codimension at least two (they are nowhere dense, so `K \ Z` lies between
`relint K \ Z` and its closure). -/
private theorem boundary_facet_adjacency_step3_closed_connected {ι : Type*} [Finite ι]
    (K : Set (E d)) (hreg : closure (relint K) = K) (hK : IsPreconnected (relint K))
    (Z : ι → Set (E d))
    (hZ : ∀ i, Module.finrank ℝ (cellDirection (Z i)) + 2 ≤
      Module.finrank ℝ (cellDirection K)) :
    IsPreconnected (K \ ⋃ i, Z i) := by
  have h1 := boundary_facet_adjacency_step3_codim_two_connected K hK Z hZ
  have h2 := boundary_facet_adjacency_step3_generic_dense K Z (fun i => by
    have := hZ i
    omega)
  refine h1.subset_closure ?_ ?_
  · exact Set.diff_subset_diff_left intrinsicInterior_subset
  · intro x hx
    have hx' : x ∈ closure (relint K) := by
      rw [hreg]
      exact hx.1
    exact closure_minimal h2 isClosed_closure hx'

/-- Step 3 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): placed cells keep the
geometric facts used by the path argument: connected relative interior (H2), regular
closedness (H2)(iii) and affine dimension, transported by a full affine frame. -/
private theorem boundary_facet_adjacency_step3_placed (φ : E d ≃ᵃ[ℝ] E d) (c : Cell d) :
    closure (relint (φ '' c.carrier)) = φ '' c.carrier ∧
      IsPreconnected (relint (φ '' c.carrier)) ∧
      Module.finrank ℝ (cellDirection (φ '' c.carrier)) = c.dim ∧
      (relint (φ '' c.carrier)).Nonempty := by
  let h := φ.toHomeomorphOfFiniteDimensional
  have hrel : relint (φ '' c.carrier) = h '' relint c.carrier :=
    hereditary_trace_step1_relint_image φ c.carrier
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrel, ← h.image_closure, c.flat.regularClosed]
    rfl
  · rw [hrel]
    exact c.flat.relint_connected.isPreconnected.image _ h.continuous.continuousOn
  · rw [boundary_facet_adjacency_step3_finrank_image, c.flat.dimension]
  · rw [hrel]
    exact c.flat.relint_nonempty.image _

/-- Step 3 of the V4 proof of `boundary_facet_adjacency` (V4 1.8, via 1.1): a point of a
child facet lies in the relative interior of its minimal cell in that child, a listed
cell contained in the facet. -/
private theorem boundary_facet_adjacency_step3_lift (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) (x : BoundaryFacet P n g) (p : E d)
    (hp : p ∈ (P.child n x.val.1).cell n x.val.2.val) :
    ∃ e : CellName S (P.child n x.val.1).ty,
      e.val.carrier ⊆ x.val.2.val.carrier ∧
        p ∈ relint ((P.child n x.val.1).cell n e.val) := by
  obtain ⟨z, hz, rfl⟩ := hp
  have hxc := (Finset.mem_filter.mp x.val.2.property).1
  have hzA : z ∈ frontier (S.proto (P.child n x.val.1).ty).carrier := by
    rw [← (S.cx _).carriers_cover]
    exact Set.mem_iUnion₂.mpr ⟨_, hxc, hz⟩
  refine ⟨⟨(S.cx _).minimalCell z hzA, (S.cx _).minimalCell_mem z hzA⟩,
    (S.cx _).minimalCell_subset z hzA _ hxc hz, ?_⟩
  change _ ∈ relint ((P.child n x.val.1).prototypeFrame n '' _)
  rw [hereditary_trace_step1_relint_image]
  exact ⟨z, (S.cx _).mem_relint_minimalCell z hzA, rfl⟩

/-- Step 3 of the V4 proof of `boundary_facet_adjacency` (V4 1.8, via (H2)): a listed
cell contained in a listed cell of the same dimension is that cell (same affine hull, so
their relative interiors meet). -/
private theorem boundary_facet_adjacency_step3_cell_eq {A : PolyManifoldDomain d}
    (K : CellComplex A) (e f : Cell d) (he : e ∈ K.cells) (hf : f ∈ K.cells)
    (hef : e.carrier ⊆ f.carrier) (hdim : e.dim = f.dim) : e = f := by
  have hle : affineSpan ℝ e.carrier ≤ affineSpan ℝ f.carrier := affineSpan_mono ℝ hef
  obtain ⟨x, hx⟩ := e.flat.relint_nonempty
  have hspan : affineSpan ℝ e.carrier = affineSpan ℝ f.carrier := by
    refine AffineSubspace.eq_of_direction_eq_of_nonempty_of_le ?_
      ((affineSpan_nonempty (k := ℝ)).mpr ⟨x, intrinsicInterior_subset hx⟩) hle
    apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
    have h1 := e.flat.dimension
    have h2 := f.flat.dimension
    unfold cellDirection at h1 h2
    rw [h1, h2, hdim]
  by_contra hne
  have hxf : x ∈ relint f.carrier :=
    hereditary_trace_step2_relint_mono _ _ hef hspan hx
  exact Set.disjoint_left.mp (K.relint_disjoint e he f hf hne) hx hxf

/-- Step 4 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): adjacency is
symmetric. -/
private theorem boundary_facet_adjacency_step4_symm (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) (a b : BoundaryFacet P n g)
    (h : boundaryFacetAdjacent P n g a b) : boundaryFacetAdjacent P n g b a := by
  obtain ⟨hab, e, f, he, hf, hef, hea, hfb⟩ := h
  exact ⟨Ne.symm hab, f, e, hf, he, hef.symm, hfb, hea⟩

/-- Step 4 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "Each crossing passes
between two child facets sharing a relatively open piece of a `(d-2)`-cell." At a point
`p` of a facet `x`, off all child cells of dimension `≤ d-3`, the minimal cell of `p` in
`x`'s child has dimension `d-2` (then `x` is adjacent to every other facet through `p`)
or `d-1` (then it is `x` and `p ∈ relint x`). -/
private theorem boundary_facet_adjacency_step4_relint_or_cross (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) (x y : BoundaryFacet P n g) (hxy : x ≠ y) (p : E d)
    (hpx : p ∈ (P.child n x.val.1).cell n x.val.2.val)
    (hpy : p ∈ (P.child n y.val.1).cell n y.val.2.val)
    (hpZ : ∀ (k : S.I P.ty) (c : CellName S (P.child n k).ty), c.val.dim + 3 ≤ d →
      p ∉ (P.child n k).cell n c.val) :
    p ∈ relint ((P.child n x.val.1).cell n x.val.2.val) ∨
      boundaryFacetAdjacent P n g x y := by
  obtain ⟨e, hex, hpe⟩ := boundary_facet_adjacency_step3_lift P n g x p hpx
  have hxc := Finset.mem_filter.mp x.val.2.property
  have hle : e.val.dim ≤ d - 1 := by
    rw [← hxc.2]
    exact hereditary_trace_step3_dim_mono _ _ hex
  have hge : ¬ e.val.dim + 3 ≤ d := fun h => hpZ _ e h (intrinsicInterior_subset hpe)
  by_cases h2 : e.val.dim = d - 2
  · right
    exact boundary_facet_adjacency_step4_crossing P n g x y hxy e h2
      (Set.image_mono hex) p hpe hpy
  · left
    have hd : e.val.dim = x.val.2.val.dim := by
      rw [hxc.2]
      omega
    have hee := boundary_facet_adjacency_step3_cell_eq (S.cx _) _ _ e.property hxc.1 hex hd
    rwa [hee] at hpe

/-- Step 4 of the V4 proof of `boundary_facet_adjacency` (V4 1.8): "Each crossing passes
between two child facets sharing a relatively open piece of a `(d-2)`-cell": two distinct
child facets inside `g` meeting at a point off the codimension-`≥ 3` child cells are
adjacent (a common relative-interior point is excluded by the disjointness of Step 2). -/
private theorem boundary_facet_adjacency_step4_meet (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) (x y : BoundaryFacet P n g) (hxy : x ≠ y) (p : E d)
    (hpx : p ∈ (P.child n x.val.1).cell n x.val.2.val)
    (hpy : p ∈ (P.child n y.val.1).cell n y.val.2.val)
    (hpZ : ∀ (k : S.I P.ty) (c : CellName S (P.child n k).ty), c.val.dim + 3 ≤ d →
      p ∉ (P.child n k).cell n c.val) :
    boundaryFacetAdjacent P n g x y := by
  rcases boundary_facet_adjacency_step4_relint_or_cross P n g x y hxy p hpx hpy hpZ with
    h | h
  · rcases boundary_facet_adjacency_step4_relint_or_cross P n g y x (Ne.symm hxy) p hpy hpx
      hpZ with h' | h'
    · exact absurd (boundary_facet_adjacency_step2_pairwise P n g hxy)
        (Set.not_disjoint_iff.mpr ⟨p, h, h'⟩)
    · exact boundary_facet_adjacency_step4_symm P n g y x h'
  · exact h

/-- P8, V4 1.8: the boundary tiling and connected adjacency graph.
The nonempty facet guarantees at least one graph vertex. -/
theorem boundary_facet_adjacency (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) :
    (⋃ a : BoundaryFacet P n g, (P.child n a.val.1).cell n a.val.2.val) =
        P.cell (n + 1) g.val ∧
      Pairwise (fun a b : BoundaryFacet P n g => Disjoint
        (relint ((P.child n a.val.1).cell n a.val.2.val))
        (relint ((P.child n b.val.1).cell n b.val.2.val))) ∧
      Nonempty (BoundaryFacet P n g) ∧
      ∀ a b : BoundaryFacet P n g,
        Relation.ReflTransGen (boundaryFacetAdjacent P n g) a b := by
  have hcover := boundary_facet_adjacency_step1_cover P n g
  have hpair := boundary_facet_adjacency_step2_pairwise P n g
  refine ⟨hcover, hpair, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := g.val.flat.relint_nonempty
    have hx' : P.prototypeFrame (n + 1) x ∈ P.cell (n + 1) g.val :=
      ⟨x, intrinsicInterior_subset hx, rfl⟩
    rw [← hcover] at hx'
    obtain ⟨a, _⟩ := Set.mem_iUnion.mp hx'
    exact ⟨a⟩
  · intro a b
    classical
    by_contra hab
    let Z : (Σ k : S.I P.ty, {c : CellName S (P.child n k).ty // c.val.dim + 3 ≤ d}) →
        Set (E d) := fun q => (P.child n q.1).cell n q.2.val.val
    have hZdim : ∀ q, Module.finrank ℝ (cellDirection (Z q)) = q.2.val.val.dim :=
      fun q => (boundary_facet_adjacency_step3_placed _ q.2.val.val).2.2.1
    have hgfac := Finset.mem_filter.mp g.property
    have hgP := boundary_facet_adjacency_step3_placed (P.prototypeFrame (n + 1)) g.val
    have hgreg : closure (relint (P.cell (n + 1) g.val)) = P.cell (n + 1) g.val := hgP.1
    have hgcon : IsPreconnected (relint (P.cell (n + 1) g.val)) := hgP.2.1
    have hgdim : Module.finrank ℝ (cellDirection (P.cell (n + 1) g.val)) = g.val.dim :=
      hgP.2.2.1
    have hK : IsPreconnected (P.cell (n + 1) g.val \ ⋃ q, Z q) :=
      boundary_facet_adjacency_step3_closed_connected _ hgreg hgcon Z (fun q => by
        rw [hZdim, hgdim, hgfac.2]
        have := q.2.property
        omega)
    have hoff : ∀ x : BoundaryFacet P n g, ∃ w ∈ (P.child n x.val.1).cell n x.val.2.val,
        w ∉ ⋃ q, Z q := by
      intro x
      have hxfac := Finset.mem_filter.mp x.val.2.property
      have hxP := boundary_facet_adjacency_step3_placed
        ((P.child n x.val.1).prototypeFrame n) x.val.2.val
      have hxdim : Module.finrank ℝ (cellDirection ((P.child n x.val.1).cell n
          x.val.2.val)) = x.val.2.val.dim := hxP.2.2.1
      have hxne : (relint ((P.child n x.val.1).cell n x.val.2.val)).Nonempty := hxP.2.2.2
      have hd := boundary_facet_adjacency_step3_generic_dense
        ((P.child n x.val.1).cell n x.val.2.val) Z (fun q => by
          rw [hZdim, hxdim, hxfac.2]
          have := q.2.property
          omega)
      by_contra hno
      push_neg at hno
      have hempty : relint ((P.child n x.val.1).cell n x.val.2.val) \ ⋃ q, Z q = ∅ := by
        ext w
        simp only [Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
        exact fun hw => hno w (intrinsicInterior_subset hw)
      obtain ⟨w, hw⟩ := hxne
      have hw' := hd hw
      rw [hempty, closure_empty] at hw'
      exact hw'
    let R : BoundaryFacet P n g → Prop := fun x =>
      Relation.ReflTransGen (boundaryFacetAdjacent P n g) a x
    have hclosed : ∀ x : BoundaryFacet P n g,
        IsClosed ((P.child n x.val.1).cell n x.val.2.val) := fun x =>
      (x.val.2.val.flat.compact.image
        ((P.child n x.val.1).prototypeFrame n).toHomeomorphOfFiniteDimensional.continuous).isClosed
    have hU : IsClosed (⋃ x : {x // R x}, (P.child n x.val.val.1).cell n x.val.val.2.val) :=
      isClosed_iUnion_of_finite fun x => hclosed x.val
    have hV : IsClosed (⋃ x : {x // ¬ R x},
        (P.child n x.val.val.1).cell n x.val.val.2.val) :=
      isClosed_iUnion_of_finite fun x => hclosed x.val
    have hsub : P.cell (n + 1) g.val \ ⋃ q, Z q ⊆
        (⋃ x : {x // R x}, (P.child n x.val.val.1).cell n x.val.val.2.val) ∪
          ⋃ x : {x // ¬ R x}, (P.child n x.val.val.1).cell n x.val.val.2.val := by
      intro w hw
      have hw1 := hw.1
      rw [← hcover] at hw1
      obtain ⟨x, hwx⟩ := Set.mem_iUnion.mp hw1
      by_cases hx : R x
      · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hwx⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hwx⟩)
    obtain ⟨wa, hwa, hwaZ⟩ := hoff a
    obtain ⟨wb, hwb, hwbZ⟩ := hoff b
    obtain ⟨p, ⟨-, hpZ⟩, hpU, hpV⟩ := isPreconnected_closed_iff.mp hK _ _ hU hV hsub
      ⟨wa, ⟨a.property hwa, hwaZ⟩,
        Set.mem_iUnion.mpr ⟨⟨a, Relation.ReflTransGen.refl⟩, hwa⟩⟩
      ⟨wb, ⟨b.property hwb, hwbZ⟩, Set.mem_iUnion.mpr ⟨⟨b, hab⟩, hwb⟩⟩
    obtain ⟨⟨x, hx⟩, hpx⟩ := Set.mem_iUnion.mp hpU
    obtain ⟨⟨y, hy⟩, hpy⟩ := Set.mem_iUnion.mp hpV
    have hxy : x ≠ y := by
      rintro rfl
      exact hy hx
    have hpZ' : ∀ (k : S.I P.ty) (c : CellName S (P.child n k).ty), c.val.dim + 3 ≤ d →
        p ∉ (P.child n k).cell n c.val := fun k c hc hpc =>
      hpZ (Set.mem_iUnion.mpr ⟨⟨k, ⟨c, hc⟩⟩, hpc⟩)
    exact hy (hx.tail (boundary_facet_adjacency_step4_meet P n g x y hxy p hpx hpy hpZ'))

/-- Step 3 of the V4 proof of `adjacency_primitive_seed` (V4 1.8): "the frame
transports relative interiors". Relative interiors commute with every full affine
frame, including the anisotropic inflation. -/
private theorem adjacency_primitive_seed_step3_relint_image (e : E d ≃ᵃ[ℝ] E d)
    (K : Set (E d)) : relint (e '' K) = e '' relint K := by
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

/-- Step 3 of the V4 proof of `adjacency_primitive_seed` (V4 1.8): "`κ = mc(p)` and
`p ∈ h`, so `κ ⊆ h`" (Lemma 1.1 / (H2)(ii)), in a prototype complex. -/
private theorem adjacency_primitive_seed_step3_proto_minimal (A : S.ι) (e f : Cell d)
    (he : e ∈ (S.cx A).cells) (hf : f ∈ (S.cx A).cells) (x : E d)
    (hxe : x ∈ relint e.carrier) (hxf : x ∈ f.carrier) : e.carrier ⊆ f.carrier := by
  have hfront : x ∈ frontier (S.proto A).carrier := by
    rw [← (S.cx A).cover]
    exact Set.mem_iUnion₂.2 ⟨e, he, hxe⟩
  have heq : (S.cx A).minimalCell x hfront = e := by
    have hu := (S.cx A).exists_unique_minimalCell x hfront
    have := hu.unique
      (y₁ := ⟨(S.cx A).minimalCell x hfront, (S.cx A).minimalCell_mem x hfront⟩)
      (y₂ := ⟨e, he⟩) ((S.cx A).mem_relint_minimalCell x hfront) hxe
    exact congrArg Subtype.val this
  rw [← heq]
  exact (S.cx A).minimalCell_subset x hfront f hf hxf

/-- Step 3 of the V4 proof of `adjacency_primitive_seed` (V4 1.8): "`κ = mc(p)` and
`p ∈ h`, so `κ ⊆ h`", for placed cells of a framed node. -/
private theorem adjacency_primitive_seed_step3_placed_minimal (N : FramedNode S) (m : ℕ)
    (e f : Cell d) (he : e ∈ (S.cx N.ty).cells) (hf : f ∈ (S.cx N.ty).cells) (p : E d)
    (hpe : p ∈ relint (N.cell m e)) (hpf : p ∈ N.cell m f) : N.cell m e ⊆ N.cell m f := by
  rw [FramedNode.cell, adjacency_primitive_seed_step3_relint_image] at hpe
  obtain ⟨x, hx, rfl⟩ := hpe
  have hxf : x ∈ f.carrier := by
    obtain ⟨y, hy, hyx⟩ := hpf
    rwa [(N.prototypeFrame m).injective hyx] at hy
  exact Set.image_mono
    (adjacency_primitive_seed_step3_proto_minimal N.ty e f he hf x hx hxf)

/-- Step 4 of the V4 proof of `adjacency_primitive_seed` (V4 1.8): relative interiors
are monotone between sets with the same affine span. -/
private theorem adjacency_primitive_seed_step4_relint_mono {s t : Set (E d)} (hst : s ⊆ t)
    (hspan : affineSpan ℝ s = affineSpan ℝ t) : relint s ⊆ relint t := by
  unfold relint intrinsicInterior
  rw [hspan]
  exact Set.image_mono (interior_mono (Set.preimage_mono hst))

/-- Step 4 of the V4 proof of `adjacency_primitive_seed` (V4 1.8): "near `p`,
`∂A = aff g`": a facet of the node containing a relative-interior point of the
facet `g` is `g` itself. -/
private theorem adjacency_primitive_seed_step4_facet_unique (P : FramedNode S) (m : ℕ)
    (g F : FacetName S P.ty) (p : E d) (hpg : p ∈ relint (P.cell m g.val))
    (hpF : p ∈ P.cell m F.val) : F = g := by
  have hg := g.property
  have hF := F.property
  simp only [CellComplex.facets, Finset.mem_filter] at hg hF
  rw [FramedNode.cell, adjacency_primitive_seed_step3_relint_image] at hpg
  obtain ⟨x, hx, rfl⟩ := hpg
  have hxF : x ∈ F.val.carrier := by
    obtain ⟨y, hy, hyx⟩ := hpF
    rwa [(P.prototypeFrame m).injective hyx] at hy
  have hsub := adjacency_primitive_seed_step3_proto_minimal P.ty g.val F.val hg.1 hF.1 x hx hxF
  have hle : affineSpan ℝ g.val.carrier ≤ affineSpan ℝ F.val.carrier := affineSpan_mono ℝ hsub
  have hspan : affineSpan ℝ g.val.carrier = affineSpan ℝ F.val.carrier := by
    apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le _ _ hle
    · apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
      have h1 := g.val.flat.dimension
      have h2 := F.val.flat.dimension
      unfold cellDirection at h1 h2
      rw [h1, h2, hg.2, hF.2]
    · exact (affineSpan_nonempty ℝ).2 ⟨x, intrinsicInterior_subset hx⟩
  have hxF' : x ∈ relint F.val.carrier :=
    adjacency_primitive_seed_step4_relint_mono hsub hspan hx
  apply Subtype.ext
  by_contra hne
  exact Set.disjoint_left.mp ((S.cx P.ty).relint_disjoint F.val hF.1 g.val hg.1 hne) hxF' hx

/-- Step 1 of the V4 proof of `adjacency_primitive_seed` (V4 1.8): "let
`p ∈ relint κ` be generic ... `p ∈ relint g` since `κ ⊆ g` and `p` is in the
relative interior of a `(d-2)`-cell of the child tiling of `g` which is not in
`∂g` by Lemma 1.1 [... adjacency across a piece of `∂g` is impossible since both
facets lie inside `g` on the same side]". -/
private theorem adjacency_primitive_seed_step1_seed_point (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) (a b : BoundaryFacet P n g) (hchild : a.val.1 ≠ b.val.1)
    (κ : CellName S (P.child n a.val.1).ty) (hκ : κ.val.dim = d - 2)
    (hκa : (P.child n a.val.1).cell n κ.val ⊆
      (P.child n a.val.1).cell n a.val.2.val)
    (hκb : (P.child n a.val.1).cell n κ.val ⊆
      (P.child n b.val.1).cell n b.val.2.val) :
    ∃ p, p ∈ relint ((P.child n a.val.1).cell n κ.val) ∧
      p ∈ relint (P.cell (n + 1) g.val) := by
  sorry

/-- Step 1 of the V4 proof of `adjacency_primitive_seed_step2_other_sheet` (V4 1.8):
"moving angularly towards the sector of C' we must cross at least one ray...
the trace of a facet h of a child of A, with p ∈ h".
There is another facet h of the child a distinct from a.val.2. -/
private lemma adjacency_primitive_seed_step2_other_sheet_step1_ray (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) (a : BoundaryFacet P n g)
    (κ : CellName S (P.child n a.val.1).ty) (hκ : κ.val.dim = d - 2)
    (hκa : (P.child n a.val.1).cell n κ.val ⊆ (P.child n a.val.1).cell n a.val.2.val)
    (p : E d) (hpκ : p ∈ relint ((P.child n a.val.1).cell n κ.val)) :
    ∃ h : FacetName S (P.child n a.val.1).ty, h ≠ a.val.2 ∧
      p ∈ (P.child n a.val.1).cell n h.val := by
  sorry

/-- Step 2 of the V4 proof of `adjacency_primitive_seed_step2_other_sheet` (V4 1.8):
"the second boundary sheet of C through p either leaves g, or ... overlapping the relative interior of f'."
A second facet h of the child through p satisfies the alternative. -/
private lemma adjacency_primitive_seed_step2_other_sheet_step2_cases (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) (a b : BoundaryFacet P n g) (hchild : a.val.1 ≠ b.val.1)
    (κ : CellName S (P.child n a.val.1).ty) (hκ : κ.val.dim = d - 2)
    (hκa : (P.child n a.val.1).cell n κ.val ⊆
      (P.child n a.val.1).cell n a.val.2.val)
    (hκb : (P.child n a.val.1).cell n κ.val ⊆
      (P.child n b.val.1).cell n b.val.2.val)
    (p : E d) (hpκ : p ∈ relint ((P.child n a.val.1).cell n κ.val))
    (hpg : p ∈ relint (P.cell (n + 1) g.val))
    (h : FacetName S (P.child n a.val.1).ty) (h_neq : h ≠ a.val.2)
    (hph : p ∈ (P.child n a.val.1).cell n h.val) :
    ¬(P.child n a.val.1).cell n h.val ⊆ P.cell (n + 1) g.val ∨
    (relint ((P.child n a.val.1).cell n h.val) ∩
      relint ((P.child n b.val.1).cell n b.val.2.val)).Nonempty := by
  sorry

/-- Step 2 of the V4 proof of `adjacency_primitive_seed` (V4 1.8): "the sectors of
`C` and `C'` are both bounded by the ray `Π ∩ aff g` and lie on the `A`-side ...
moving angularly towards the sector of `C'` we must cross at least one ray ...
the trace of a facet `h` of a child of `A`, with `p ∈ h`, and `h` is not inside
`g`". Taken at the extreme sector of the child `C` owning `a`: the second boundary
sheet of `C` through `p` either leaves `g`, or (if `∂C` were flat at `p`) it lies
in `g` on the side of `f'`, overlapping the relative interior of `f'`. -/
private theorem adjacency_primitive_seed_step2_other_sheet (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) (a b : BoundaryFacet P n g) (hchild : a.val.1 ≠ b.val.1)
    (κ : CellName S (P.child n a.val.1).ty) (hκ : κ.val.dim = d - 2)
    (hκa : (P.child n a.val.1).cell n κ.val ⊆
      (P.child n a.val.1).cell n a.val.2.val)
    (hκb : (P.child n a.val.1).cell n κ.val ⊆
      (P.child n b.val.1).cell n b.val.2.val) (p : E d)
    (hpκ : p ∈ relint ((P.child n a.val.1).cell n κ.val))
    (hpg : p ∈ relint (P.cell (n + 1) g.val)) :
    ∃ h : FacetName S (P.child n a.val.1).ty,
      p ∈ (P.child n a.val.1).cell n h.val ∧
      (¬ (P.child n a.val.1).cell n h.val ⊆ P.cell (n + 1) g.val ∨
        (relint ((P.child n a.val.1).cell n h.val) ∩
          relint ((P.child n b.val.1).cell n b.val.2.val)).Nonempty) := by
  obtain ⟨h, h_neq, hph⟩ :=
    adjacency_primitive_seed_step2_other_sheet_step1_ray P n g a κ hκ hκa p hpκ
  refine ⟨h, hph, ?_⟩
  exact adjacency_primitive_seed_step2_other_sheet_step2_cases P n g a b hchild κ hκ hκa hκb p hpκ hpg h h_neq hph

/-- P8, V4 1.8 (moreover): distinct-child adjacency supplies a primitive facet
containing the common cell, with all of that cell's vertices common-listed. -/
theorem adjacency_primitive_seed (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) (a b : BoundaryFacet P n g)
    (hab : boundaryFacetAdjacent P n g a b) (hchild : a.val.1 ≠ b.val.1)
    (κ : CellName S (P.child n a.val.1).ty) (hκ : κ.val.dim = d - 2)
    (hκa : (P.child n a.val.1).cell n κ.val ⊆
      (P.child n a.val.1).cell n a.val.2.val)
    (hκb : (P.child n a.val.1).cell n κ.val ⊆
      (P.child n b.val.1).cell n b.val.2.val) :
    ∃ (i : S.I P.ty) (h : FacetName S (P.child n i).ty),
      relint ((P.child n i).cell n h.val) ⊆ interior (P.carrier (n + 1)) ∧
      (P.child n a.val.1).cell n κ.val ⊆ (P.child n i).cell n h.val ∧
      ∀ q : E d, (P.child n a.val.1).Lists n q →
        q ∈ (P.child n a.val.1).cell n κ.val →
        (P.child n i).Lists n q ∧ q ∈ (P.child n i).cell n h.val ∧
          ∀ j : S.I P.ty, q ∈ (P.child n j).carrier n → (P.child n j).Lists n q := by
  obtain ⟨p, hpκ, hpg⟩ :=
    adjacency_primitive_seed_step1_seed_point P n g a b hchild κ hκ hκa hκb
  obtain ⟨h, hph, hcases⟩ :=
    adjacency_primitive_seed_step2_other_sheet P n g a b hchild κ hκ hκa hκb p hpκ hpg
  have hnot : ¬ (P.child n a.val.1).cell n h.val ⊆ P.cell (n + 1) g.val := by
    intro hsub
    rcases hcases with hc | hc
    · exact hc hsub
    · let c : BoundaryFacet P n g := ⟨⟨a.val.1, h⟩, hsub⟩
      have hcb : c ≠ b := by
        intro hcb
        have h1 : c.val.1 = b.val.1 :=
          congrArg (fun q : BoundaryFacet P n g => q.val.1) hcb
        exact hchild h1
      have hd := (boundary_facet_adjacency P n g).2.1 hcb
      obtain ⟨x, hx1, hx2⟩ := hc
      exact Set.disjoint_left.mp hd hx1 hx2
  have hdesc : (P.child n a.val.1).IsDescendant n P (n + 1) := by
    refine ⟨1, rfl, ⟨a.val.1, ()⟩, ?_⟩
    simp [SubstSystem.descendantNode, FramedNode.move, FramedNode.child]
  have hint : relint ((P.child n a.val.1).cell n h.val) ⊆ interior (P.carrier (n + 1)) := by
    rcases facet_dichotomy P (P.child n a.val.1) (n + 1) n hdesc h with ⟨F, hF, -⟩ | hint
    · exfalso
      have hFg := adjacency_primitive_seed_step4_facet_unique P (n + 1) g F p hpg (hF hph)
      rw [hFg] at hF
      exact hnot hF
    · exact hint
  have hhcell : h.val ∈ (S.cx (P.child n a.val.1).ty).cells := by
    have hh := h.property
    simp only [CellComplex.facets, Finset.mem_filter] at hh
    exact hh.1
  have hκh : (P.child n a.val.1).cell n κ.val ⊆ (P.child n a.val.1).cell n h.val :=
    adjacency_primitive_seed_step3_placed_minimal (P.child n a.val.1) n κ.val h.val
      κ.property hhcell p hpκ hph
  refine ⟨a.val.1, h, hint, hκh, ?_⟩
  intro q hq hqκ
  exact ⟨hq, hκh hqκ, fun j hj =>
    primitive_vertex_listed P n a.val.1 h hint q hq (hκh hqκ) j hj⟩

/-- P1/P2, V4 1.1--1.2: placed minimal cells exist uniquely at every boundary
point, including at positive height. This extends the stage-1 prototype API. -/
theorem placedMinimalCell_exists_unique (N : FramedNode S) (n : ℕ) (p : E d)
    (hp : p ∈ frontier (N.carrier n)) :
    ∃! e : CellName S N.ty, p ∈ relint (N.cell n e.val) := by
  sorry

/-- P1/P2, V4 1.1--1.2: the unique placed minimal cell, retaining its prototype name. -/
def placedMinimalCell (N : FramedNode S) (n : ℕ) (p : E d)
    (hp : p ∈ frontier (N.carrier n)) : CellName S N.ty :=
  Classical.choose (placedMinimalCell_exists_unique N n p hp)

/-- P1/P2, V4 1.1--1.2: the chosen cell contains the point in its relative interior. -/
theorem placedMinimalCell_spec (N : FramedNode S) (n : ℕ) (p : E d)
    (hp : p ∈ frontier (N.carrier n)) :
    p ∈ relint (N.cell n (placedMinimalCell N n p hp).val) :=
  (Classical.choose_spec (placedMinimalCell_exists_unique N n p hp)).1

/-- P2, V4 1.2: the ancestral stratum is the ancestor's minimal cell at every
relative-interior point of the descendant cell, rather than just one chosen anchor. -/
theorem ancestralStratum_eq_minimalCell (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (g : CellName S C.ty)
    (hg : C.cell h g.val ⊆ frontier (P.carrier n)) (p : E d)
    (hp : p ∈ relint (C.cell h g.val)) (hpP : p ∈ frontier (P.carrier n)) :
    ancestralStratum P C n h hC g hg = placedMinimalCell P n p hpP := by
  obtain ⟨e, _, he_unique⟩ := placedMinimalCell_exists_unique P n p hpP
  have h1 := he_unique (ancestralStratum P C n h hC g hg) ((ancestralStratum_spec P C n h hC g hg).1 hp)
  have h2 := he_unique (placedMinimalCell P n p hpP) (placedMinimalCell_spec P n p hpP)
  rw [h1, h2]


namespace CoherentHierarchy

variable {T : Tiling S} (H : CoherentHierarchy S T)

/-- P6, V4 1.6: ancestor iteration is additive, including zero parent steps. -/
theorem ancestor_add (q : H.Node) (r s : ℕ) :
    H.ancestor (H.ancestor q r) s = H.ancestor q (r + s) := by
  dsimp [ancestor]
  rw [← Function.iterate_add_apply]
  rw [add_comm s r]

/-- P6, V4 1.6: boundary offsets are downward closed and contain zero. -/
theorem boundaryOffsets_downward (q : H.Node) (f : FacetName S q.2.val.ty) :
    0 ∈ H.boundaryOffsets q f ∧
      ∀ r s : ℕ, r ≤ s → s ∈ H.boundaryOffsets q f → r ∈ H.boundaryOffsets q f := by
  sorry

/-- P6, V4 1.6: all offsets from the finite birth on are interior alternatives. -/
theorem after_birth_interior (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (r : ℕ) (hr : (H.firstProvider q f hf).1 < r) :
    relint (q.2.val.cell q.1 f.val) ⊆
      interior ((H.ancestor q r).2.val.carrier (H.ancestor q r).1) := by
  have H_spec := H.firstProvider_spec q f hf
  have H_initial := H_spec.1
  have hr_not_in : r ∉ H.boundaryOffsets q f := by
    rw [H_initial]
    intro hr'
    have : r < (H.firstProvider q f hf).1 + 1 := hr'
    omega
  have hdesc := H.ancestor_descendant q r
  have h_dicho := facet_dichotomy (H.ancestor q r).2.val q.2.val (H.ancestor q r).1 q.1 hdesc f
  cases h_dicho with
  | inl h_dicho_l =>
    obtain ⟨F, hF, _⟩ := h_dicho_l
    exfalso
    apply hr_not_in
    change q.2.val.cell q.1 f.val ⊆ frontier ((H.ancestor q r).2.val.carrier (H.ancestor q r).1)
    intro x hx
    have hx_in_F := hF hx
    have F_prop_cells : F.val ∈ (S.cx (H.ancestor q r).2.val.ty).cells := by
      have hh := F.property
      simp only [CellComplex.facets, Finset.mem_filter] at hh
      exact hh.1
    have hx_front := hereditary_trace_step1_cell_frontier (H.ancestor q r).2.val (H.ancestor q r).1 _ F_prop_cells
    exact hx_front hx_in_F
  | inr h_dicho_r =>
    exact h_dicho_r

/-- P6, V4 1.6: birth height and age are exactly the serving offset plus one. -/
theorem birthHeight_age_spec (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) :
    H.birthHeight q f hf = q.1 + (H.firstProvider q f hf).1 + 1 ∧
      H.age q f hf = (H.firstProvider q f hf).1 + 1 ∧ 1 ≤ H.age q f hf := by
  have ancestor_height (r : ℕ) : (H.ancestor q r).1 = q.1 + r := by
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [← ancestor_add H q r 1]
      dsimp [ancestor]
      have : (H.parentNode (H.parentNode^[r] q)).1 = (H.parentNode^[r] q).1 + 1 := rfl
      rw [this]
      change (H.ancestor q r).1 + 1 = q.1 + (r + 1)
      rw [ih]
      omega
  
  have h_serve : (H.servingChild q f hf).1 = q.1 + (H.firstProvider q f hf).1 := by
    dsimp [servingChild]
    rw [ancestor_height]
  
  have h_birth : H.birthHeight q f hf = q.1 + (H.firstProvider q f hf).1 + 1 := by
    change (H.servingChild q f hf).1 + 1 = _
    rw [h_serve]

  have h_age : H.age q f hf = (H.firstProvider q f hf).1 + 1 := by
    change H.birthHeight q f hf - q.1 = _
    rw [h_birth]
    omega

  exact ⟨h_birth, h_age, by rw [h_age]; omega⟩

/-- P6, V4 1.6: a total provider record, using `none = NULL` on persistent faults. -/
def providerOrNull (q : H.Node) (f : FacetName S q.2.val.ty) :
    Option (H.ProviderCandidate q) := by
  classical
  exact if hf : H.IsFault q f then none else some (H.firstProvider q f hf)

/-- P6, V4 1.6: the NULL case is exactly persistent boundary, not a failed choice. -/
theorem providerOrNull_eq_none (q : H.Node) (f : FacetName S q.2.val.ty) :
    H.providerOrNull q f = none ↔ H.IsFault q f := by
  classical
  simp only [providerOrNull]
  split <;> simp_all

/-- P7, V4 1.7(b): at age one, the stratum map is the identity on every named cell. -/
theorem stratumMap_age_one (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (hage : H.age q f hf = 1)
    (s : CellName S q.2.val.ty)
    (hs : q.2.val.cell q.1 s.val ⊆ q.2.val.cell q.1 f.val) :
    (H.stratumMap q f hf s hs).val = s.val := by
  have h_prov_len : (H.firstProvider q f hf).1 = 0 := by
    have h := H.birthHeight_age_spec q f hf
    omega
  have hc : (H.servingChild q f hf) = q := by
    dsimp [CoherentHierarchy.servingChild, CoherentHierarchy.ancestor]
    rw [h_prov_len]
    rfl
  dsimp [CoherentHierarchy.stratumMap]
  have hd := Classical.choose_spec (H.stratum_exists_unique q f hf s hs)
  obtain ⟨hd1, hd2⟩ := hd
  have H2 : ∀ (c : H.Node) (h : c = q), (cast (by rw [h]) s : CellName S c.2.val.ty).val = s.val := by
    intro c h
    subst h
    rfl
  have heq2 : (cast (by rw [hc]) s : CellName S (H.servingChild q f hf).2.val.ty).val = s.val := H2 (H.servingChild q f hf) hc

  have H3 : ∀ (c : H.Node) (h : c = q), relint (q.2.val.cell q.1 s.val) ⊆ relint (c.2.val.cell c.1 (cast (by rw [h]) s : CellName S c.2.val.ty).val) := by
    intro c h
    subst h
    exact subset_rfl
  have heq3 : relint (q.2.val.cell q.1 s.val) ⊆ relint ((H.servingChild q f hf).2.val.cell (H.servingChild q f hf).1 (cast (by rw [hc]) s : CellName S (H.servingChild q f hf).2.val.ty).val) := H3 (H.servingChild q f hf) hc

  have heq4 := hd2 _ heq3
  have heq5 : (Classical.choose (H.stratum_exists_unique q f hf s hs)).val = (cast (by rw [hc]) s : CellName S (H.servingChild q f hf).2.val.ty).val := by
    rw [heq4]
  rw [heq5]
  exact heq2

/-- P7, V4 1.7(d), final clause: an active edge lies in an edge of every
intermediate ancestor, with the same one-dimensional provider stratum. -/
theorem active_edge_hereditary (q c : H.Node) (r : ℕ) (hc : H.ancestor c r = q)
    (f : FacetName S q.2.val.ty) (g : FacetName S c.2.val.ty)
    (hf : ¬ H.IsFault q f) (hg : ¬ H.IsFault c g)
    (hsub : c.2.val.cell c.1 g.val ⊆ q.2.val.cell q.1 f.val)
    (s : CellName S c.2.val.ty) (hdim : s.val.dim = 1)
    (hs : c.2.val.cell c.1 s.val ⊆ c.2.val.cell c.1 g.val)
    (hactive : (H.stratumMap c g hg s hs).val.dim = 1) :
    ∃ (t : CellName S q.2.val.ty)
      (ht : q.2.val.cell q.1 t.val ⊆ q.2.val.cell q.1 f.val),
      t.val.dim = 1 ∧ relint (c.2.val.cell c.1 s.val) ⊆
        relint (q.2.val.cell q.1 t.val) ∧
      (H.servingChild q f hf).2.val.cell (H.servingChild q f hf).1
        (H.stratumMap q f hf t ht).val =
      (H.servingChild c g hg).2.val.cell (H.servingChild c g hg).1
        (H.stratumMap c g hg s hs).val := by
  sorry

end CoherentHierarchy

/-- P6/P7/T9, V4 1.6--1.7, 1.13(c): exact scale transfer preserves faults
on the entire surviving tails, including their arbitrarily high ancestors. -/
theorem ScaleTailEquiv.faults {U V : HonestSource S} {a b : ℕ} {J : Iso d}
    (e : ScaleTailEquiv U V a b J) (q : U.hierarchy.Tail a)
    (f : FacetName S q.val.2.val.ty)
    (g : FacetName S (e.toEquiv q).val.2.val.ty) (hfg : f.val = g.val) :
    U.hierarchy.IsFault q.val f ↔ V.hierarchy.IsFault (e.toEquiv q).val g := by
  sorry

/-- P6/P7/T9, V4 1.6--1.7, 1.13(c): finite providers keep their exact serving
offset, facet name, primitive incidence, and age under exact scale transfer. -/
theorem ScaleTailEquiv.providers {U V : HonestSource S} {a b : ℕ} {J : Iso d}
    (e : ScaleTailEquiv U V a b J) (q : U.hierarchy.Tail a)
    (f : FacetName S q.val.2.val.ty)
    (g : FacetName S (e.toEquiv q).val.2.val.ty) (hfg : f.val = g.val)
    (hf : ¬ U.hierarchy.IsFault q.val f)
    (hg : ¬ V.hierarchy.IsFault (e.toEquiv q).val g) :
    (U.hierarchy.firstProvider q.val f hf).1 =
        (V.hierarchy.firstProvider (e.toEquiv q).val g hg).1 ∧
      (U.hierarchy.firstProvider q.val f hf).2.val =
        (V.hierarchy.firstProvider (e.toEquiv q).val g hg).2.val ∧
      U.hierarchy.providerIncidence q.val f hf =
        V.hierarchy.providerIncidence (e.toEquiv q).val g hg ∧
      U.hierarchy.age q.val f hf = V.hierarchy.age (e.toEquiv q).val g hg ∧
      J '' ((U.expansion ^ ((b : ℤ) - (a : ℤ))) ''
        U.hierarchy.providerCarrier q.val f hf) =
          V.hierarchy.providerCarrier (e.toEquiv q).val g hg := by
  sorry

/-- P7/T9, V4 1.7(b), 1.13(c): provider strata retain literal prototype names
under the same full-tail transfer as the nodes and the provider incidences. -/
theorem ScaleTailEquiv.strata {U V : HonestSource S} {a b : ℕ} {J : Iso d}
    (e : ScaleTailEquiv U V a b J) (q : U.hierarchy.Tail a)
    (f : FacetName S q.val.2.val.ty)
    (g : FacetName S (e.toEquiv q).val.2.val.ty) (hfg : f.val = g.val)
    (hf : ¬ U.hierarchy.IsFault q.val f)
    (hg : ¬ V.hierarchy.IsFault (e.toEquiv q).val g)
    (s : CellName S q.val.2.val.ty) (t : CellName S (e.toEquiv q).val.2.val.ty)
    (hst : s.val = t.val)
    (hs : q.val.2.val.cell q.val.1 s.val ⊆ q.val.2.val.cell q.val.1 f.val)
    (ht : (e.toEquiv q).val.2.val.cell (e.toEquiv q).val.1 t.val ⊆
      (e.toEquiv q).val.2.val.cell (e.toEquiv q).val.1 g.val) :
    (U.hierarchy.stratumMap q.val f hf s hs).val =
      (V.hierarchy.stratumMap (e.toEquiv q).val g hg t ht).val := by
  sorry

end Enforce
