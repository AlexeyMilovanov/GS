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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- P6, V4 1.6: birth height and age are exactly the serving offset plus one. -/
theorem birthHeight_age_spec (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) :
    H.birthHeight q f hf = q.1 + (H.firstProvider q f hf).1 + 1 ∧
      H.age q f hf = (H.firstProvider q f hf).1 + 1 ∧ 1 ≤ H.age q f hf := by
  sorry

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
  sorry

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
