import Enforce.Source.Headers
import Enforce.Source.Edges
open private coarsen_desc_mem from Enforce.Tiling

/-!
# Recursive coface traces and ordinary sites

A trace piece records its owner and every coface in the fixed flag. Thus owners
without a full coface chain never enter the trace. The bottom dimension is two,
except in dimension two, where it is one, exactly as prescribed after V4 1.22(c).
No selected site arms or statement 1.23(d) are included (Proposition 8.3).
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- P17, V4 1.22, dimension-two paragraph: dimension of the recursive trace. -/
def traceDimension (d : ℕ) : ℕ := min 2 (d - 1)

/-- P17, V4 1.22: the trace dimension is positive in every allowed dimension. -/
theorem traceDimension_pos : 1 ≤ traceDimension d := by
  have hd : 2 ≤ d := Fact.out
  unfold traceDimension
  omega

/-- P17, V4 1.22: the trace is a boundary-dimensional cell. -/
theorem traceDimension_lt : traceDimension d < d := by
  have hd : 2 ≤ d := Fact.out
  unfold traceDimension
  omega

/-- P17, V4 1.22(c): indices of a coface chain starting at dimension `j`. -/
abbrev ChainIndex (d j : ℕ) := {i : Fin d // j ≤ i.val ∧ 1 ≤ i.val}

/-- P17, V4 1.22(c): an occurrence has a complete chain up to the outer facet.
The target flag is in the standard height-`r` root; the owner may have any height. -/
structure ChainOccurrence (A : S.ι) (F : FacetFlag S A) (r : ℕ)
    (C : FramedNode S) (h j : ℕ) where
  /-- P17, V4 1.22(c): named cells of the owner at every required dimension. -/
  cell : ChainIndex d j → CellName S C.ty
  /-- P17, V4 1.22(c): exact dimension at each index. -/
  dimension : ∀ i, (cell i).val.dim = i.val.val
  /-- P17, V4 1.22(c): the entire chain is nested. -/
  nested : ∀ i k, i.val.val ≤ k.val.val →
    (cell i).val.carrier ⊆ (cell k).val.carrier
  /-- P17, V4 1.22(c): every coface lies in the prescribed ancestral flag cell. -/
  contained : ∀ i, C.cell h (cell i).val ⊆
    (S.σ ^ r) '' (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier

/-- P17, V4 1.22(a): a native trace polygon (or edge) and its complete owner chain. -/
structure TracePiece (A : S.ι) (F : FacetFlag S A) (r : ℕ) where
  /-- P17, V4 1.22(a): exact native owner address. -/
  owner : S.RoleWord A r
  /-- P17, V4 1.22(a): recorded chain from the trace cell to the facet. -/
  chain : ChainOccurrence A F r (S.nativeTile A r owner) 0 (traceDimension d)

namespace TracePiece

variable {A : S.ι} {F : FacetFlag S A} {r : ℕ}

/-- P17, V4 1.22(a): the actual selected native owner. -/
def tile (a : TracePiece A F r) : FramedNode S := S.nativeTile A r a.owner

/-- P17, V4 1.22(a): bottom index of the coface chain. -/
def bottomIndex : ChainIndex d (traceDimension d) :=
  ⟨⟨traceDimension d, traceDimension_lt⟩, le_rfl, traceDimension_pos⟩

/-- P17, V4 1.22(a): the named polygon (or edge in dimension two). -/
def bottom (a : TracePiece A F r) : CellName S a.tile.ty :=
  a.chain.cell bottomIndex

/-- P17, V4 1.22(a): its actual native-scale placed carrier. -/
def carrier (a : TracePiece A F r) : Set (E d) := a.tile.cell 0 a.bottom.val

/-- P17, V4 1.22(a): native cell names of the recorded chain, with absent lower
indices recorded by `none`. These labels are finite and preserve all coface names. -/
def chainNames (a : TracePiece A F r) (i : Fin d) : Option (Cell d) := by
  classical
  exact if hi : traceDimension d ≤ i.val ∧ 1 ≤ i.val then
    some (a.chain.cell ⟨i, hi⟩).val else none

end TracePiece

/-- P17, V4 1.22(a): only finitely many owner/chain occurrences at a fixed depth. -/
theorem tracePieces_finite (A : S.ι) (F : FacetFlag S A) (r : ℕ) :
    Finite (TracePiece A F r) := by
  haveI := S.roleWord_finite A r
  let f : TracePiece A F r →
      Σ w : S.RoleWord A r,
        (ChainIndex d (traceDimension d) → CellName S (S.nativeTile A r w).ty) :=
    fun a => ⟨a.owner, a.chain.cell⟩
  have hf : Function.Injective f := by
    rintro ⟨o1, c1⟩ ⟨o2, c2⟩ h
    simp only [f, Sigma.mk.injEq] at h
    obtain ⟨rfl, hc⟩ := h
    have hc' : c1.cell = c2.cell := eq_of_heq hc
    cases c1
    cases c2
    simp only at hc'
    subst hc'
    rfl
  exact Finite.of_injective f hf

/-- P17, V4 1.22(a): the recursive trace `𝓟₂`, with owners and full recorded chains.
All chains are required to lie inside the fixed successive cofaces. The geometric
trace theorem proves that these occurrences give exactly a tiling of the bottom cell. -/
def recursiveTrace (A : S.ι) (F : FacetFlag S A) (r : ℕ) : Finset (TracePiece A F r) := by
  classical
  letI := tracePieces_finite A F r
  letI := Fintype.ofFinite (TracePiece A F r)
  exact Finset.univ

/-- Step 0 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a)): "native tiles of the
depth-`r` subdivision". A ground cell is placed directly by its tile frame. -/
private theorem recursiveTrace_tiles_step0_cell_zero (C : FramedNode S) (e : Cell d) :
    C.cell 0 e = C.frame '' e.carrier := by
  simp [FramedNode.cell, FramedNode.prototypeFrame]

/-- Step 0 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a)): relative interiors of
placed ground cells are the placed relative interiors (the frame is an isometry). -/
private theorem recursiveTrace_tiles_step0_relint_cell (C : FramedNode S) (e : Cell d) :
    relint (C.cell 0 e) = C.frame '' relint e.carrier := by
  rw [recursiveTrace_tiles_step0_cell_zero]
  exact C.frame.toAffineIsometry.image_intrinsicInterior e.carrier

/-- Step 0 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a)): the standard root
`H` at height `r` places its cells by `σ^r`. -/
private theorem recursiveTrace_tiles_step0_root_cell (A : S.ι) (r : ℕ) (e : Cell d) :
    (⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩ : FramedNode S).cell r e =
      (S.σ ^ r) '' e.carrier := by
  first
  | rfl
  | simp [FramedNode.cell, FramedNode.prototypeFrame]

/-- Step 0 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a)): "native tiles of the
depth-`r` subdivision" are descendants of the standard root `H`. -/
private theorem recursiveTrace_tiles_step0_native_desc (A : S.ι) (r : ℕ)
    (w : S.RoleWord A r) :
    (S.nativeTile A r w).IsDescendant 0
      (⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩ : FramedNode S) r :=
  ⟨r, (zero_add r).symm, w, by
    simp [SubstSystem.nativeTile, FramedNode.move, AffineIsometryEquiv.trans_refl]⟩

/-- Step 0 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a), via (H2)): every node is
its own depth-zero descendant, so Lemma 1.1 also applies inside one tile. -/
private theorem recursiveTrace_tiles_step0_self_desc (C : FramedNode S) :
    C.IsDescendant 0 C 0 :=
  ⟨0, rfl, (), by
    cases C
    simp [SubstSystem.descendantNode, FramedNode.move, AffineIsometryEquiv.refl_trans]⟩

/-- Step 0 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a)): affine equivalences
preserve the dimension of affine hulls. -/
private theorem recursiveTrace_tiles_step0_finrank_image (g : E d ≃ᵃ[ℝ] E d)
    (K : Set (E d)) :
    Module.finrank ℝ (cellDirection (g '' K)) = Module.finrank ℝ (cellDirection K) := by
  change Module.finrank ℝ (affineSpan ℝ (g.toAffineMap '' K)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  exact LinearEquiv.finrank_map_eq g.linear (cellDirection K)

/-- Step 1 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a)): "a recorded chain of
cells ... with `G_j ⊆ F_j` and `aff G_j = aff F_j`". Containment and equality of
dimensions give equality of affine hulls. -/
private theorem recursiveTrace_tiles_step1_span {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (a : TracePiece A F r) (i : ChainIndex d (traceDimension d)) :
    affineSpan ℝ (a.tile.cell 0 (a.chain.cell i).val) =
      affineSpan ℝ ((S.σ ^ r) ''
        (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier) := by
  have hsub : a.tile.cell 0 (a.chain.cell i).val ⊆ (S.σ ^ r) ''
      (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier := a.chain.contained i
  have hle : cellDirection (a.tile.cell 0 (a.chain.cell i).val) ≤
      cellDirection ((S.σ ^ r) ''
        (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier) := by
    simpa only [cellDirection, direction_affineSpan] using vectorSpan_mono ℝ hsub
  have hdir : cellDirection (a.tile.cell 0 (a.chain.cell i).val) =
      cellDirection ((S.σ ^ r) ''
        (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier) := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    have hleft : Module.finrank ℝ (cellDirection
        (a.tile.cell 0 (a.chain.cell i).val)) = i.val.val := by
      rw [recursiveTrace_tiles_step0_cell_zero]
      exact (recursiveTrace_tiles_step0_finrank_image a.tile.frame.toAffineEquiv _).trans
        ((a.chain.cell i).val.flat.dimension.trans (a.chain.dimension i))
    have hright : Module.finrank ℝ (cellDirection ((S.σ ^ r) ''
        (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier)) = i.val.val :=
      (recursiveTrace_tiles_step0_finrank_image (S.σ ^ r).toAffineEquiv _).trans
        ((F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.flat.dimension.trans
          (F.dimension ⟨i.val.val, i.property.2, i.val.isLt⟩))
    exact hleft.trans hright.symm
  have hne : (a.tile.cell 0 (a.chain.cell i).val).Nonempty := by
    obtain ⟨y, hy⟩ := (a.chain.cell i).val.flat.relint_nonempty
    rw [recursiveTrace_tiles_step0_cell_zero]
    exact ⟨_, Set.mem_image_of_mem _ (intrinsicInterior_subset hy)⟩
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir
    ((affineSpan_nonempty ℝ).2 hne) (affineSpan_mono ℝ hsub)

/-- Step 2 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a), "or to the same one,
excluded by (H2)"): two listed cells of one tile whose placed relative interiors meet
are the same listed cell. -/
private theorem recursiveTrace_tiles_step2_same_name (C : FramedNode S)
    (e f : CellName S C.ty)
    (h : (relint (C.cell 0 e.val) ∩ relint (C.cell 0 f.val)).Nonempty) : e = f := by
  by_contra hne
  have hd := (S.cx C.ty).relint_disjoint e.val e.property f.val f.property
    (fun h => hne (Subtype.ext h))
  obtain ⟨x, hx1, hx2⟩ := h
  rw [recursiveTrace_tiles_step0_relint_cell] at hx1 hx2
  obtain ⟨y, hy, rfl⟩ := hx1
  obtain ⟨z, hz, hzy⟩ := hx2
  rw [C.frame.injective hzy] at hz
  exact Set.disjoint_left.1 hd hy hz

/-- Auxiliary for `recursiveTrace_tiles_step3_halfspace_lift` (V4 1.0(H2)): the relative
interior is the set of points with a small ball of the affine span inside the set. -/
private lemma recursiveTrace_tiles_step3_halfspace_lift_lem_relint {K : Set (E d)} {x : E d} :
    x ∈ relint K ↔
      x ∈ K ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ affineSpan ℝ K, dist y x < ρ → y ∈ K := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.mp hx
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
    have hyK : y ∈ (Subtype.val ⁻¹' K : Set (affineSpan ℝ K)) := interior_subset hy
    refine ⟨hyK, ρ, hρ, fun z hz hdist => ?_⟩
    exact hball (show (⟨z, hz⟩ : affineSpan ℝ K) ∈ ball y ρ from hdist)
  · rintro ⟨hxK, ρ, hρ, h⟩
    refine mem_intrinsicInterior.mpr ⟨⟨x, subset_affineSpan ℝ K hxK⟩, ?_, rfl⟩
    refine mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨ρ, hρ, fun z hz => ?_⟩)
    exact h z z.2 hz

/-- Auxiliary for `recursiveTrace_tiles_step3_halfspace_lift` (V4 1.0(H2)(i)--(ii)):
a listed cell through a relative-interior point of another listed cell contains it. -/
private lemma recursiveTrace_tiles_step3_halfspace_lift_lem_incidence
    {A : PolyManifoldDomain d} (K : CellComplex A) {e f : Cell d}
    (he : e ∈ K.cells) (hf : f ∈ K.cells) {p : E d} (hp : p ∈ relint e.carrier)
    (hpf : p ∈ f.carrier) : e.carrier ⊆ f.carrier := by
  classical
  let N (f : Cell d) := (K.cells.filter fun g => g.carrier ⊆ f.carrier).card
  have main : ∀ n : ℕ, ∀ f : Cell d, f ∈ K.cells → N f = n → p ∈ f.carrier →
      e.carrier ⊆ f.carrier := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf hN hpf
      obtain ⟨b, hb, hboundary⟩ := K.boundary_union f hf
      have hgb (g : Cell d) (hg : g ∈ b) : g.carrier ⊆ relfrontier f.carrier := by
        intro z hz
        rw [hboundary]
        exact mem_iUnion.mpr ⟨g, mem_iUnion.mpr ⟨hg, hz⟩⟩
      have hgf (g : Cell d) (hg : g ∈ b) : g.carrier ⊆ f.carrier :=
        (hgb g hg).trans (intrinsicFrontier_subset f.flat.compact.isClosed)
      have hsmall : ∀ g ∈ b, N g < N f := by
        intro g hg
        have hnfg : ¬ f.carrier ⊆ g.carrier := by
          intro hfg
          obtain ⟨z, hz⟩ := f.flat.relint_nonempty
          have hzb := hgb g hg (hfg (intrinsicInterior_subset hz))
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
          exact Finset.mem_filter.mpr ⟨hg'K, hg'g.trans (hgf g hg)⟩
      by_cases hpi : p ∈ relint f.carrier
      · have hef : e = f := by
          by_contra hne
          exact Set.disjoint_left.mp (K.relint_disjoint e he f hf hne) hp hpi
        exact hef ▸ Subset.rfl
      · have hpb : p ∈ relfrontier f.carrier := by
          change p ∈ intrinsicFrontier ℝ f.carrier
          rw [← closure_diff_intrinsicInterior, f.flat.compact.isClosed.closure_eq]
          exact ⟨hpf, hpi⟩
        rw [hboundary] at hpb
        obtain ⟨g, hpg⟩ := mem_iUnion.mp hpb
        obtain ⟨hg, hpg⟩ := mem_iUnion.mp hpg
        exact (ih (N g) (by simpa only [hN] using hsmall g hg) g (hb hg) rfl hpg).trans
          (hgf g hg)
  exact main (N f) f hf rfl hpf

/-- Auxiliary for `recursiveTrace_tiles_step3_halfspace_lift` (V4 1.0(H2)): a cell inside the
relative boundary of another cell has strictly smaller dimension. -/
private lemma recursiveTrace_tiles_step3_halfspace_lift_lem_frontier_dim {g C : Cell d}
    (hg : g.carrier ⊆ relfrontier C.carrier) :
    Module.finrank ℝ (cellDirection g.carrier) <
      Module.finrank ℝ (cellDirection C.carrier) := by
  have hgC : g.carrier ⊆ C.carrier :=
    hg.trans (intrinsicFrontier_subset C.flat.compact.isClosed)
  have hle : cellDirection g.carrier ≤ cellDirection C.carrier :=
    AffineSubspace.direction_le (affineSpan_mono ℝ hgC)
  by_contra hlt
  have hdir : cellDirection g.carrier = cellDirection C.carrier :=
    Submodule.eq_of_le_of_finrank_le hle (not_lt.mp hlt)
  obtain ⟨z, hz⟩ := g.flat.relint_nonempty
  have hzg : z ∈ g.carrier := intrinsicInterior_subset hz
  have hspan : affineSpan ℝ g.carrier = affineSpan ℝ C.carrier :=
    AffineSubspace.ext_of_direction_eq hdir
      ⟨z, subset_affineSpan ℝ _ hzg, subset_affineSpan ℝ _ (hgC hzg)⟩
  have hrel : relint g.carrier ⊆ relint C.carrier := by
    unfold relint intrinsicInterior
    rw [← hspan]
    exact Set.image_mono (interior_mono (Set.preimage_mono hgC))
  have hzb := hg hzg
  change z ∈ intrinsicFrontier ℝ C.carrier at hzb
  rw [← closure_diff_intrinsicInterior] at hzb
  exact hzb.2 (hrel hz)

/-- Auxiliary for `recursiveTrace_tiles_step3_halfspace_lift` (V4 1.16(b)): a codimension-one
pair `W ≤ V` is cut out in `V` by a functional taking the value `1` on a vector of `V`. -/
private lemma recursiveTrace_tiles_step3_halfspace_lift_lem_functional {V W : Submodule ℝ (E d)}
    (hWV : W ≤ V) (hdim : Module.finrank ℝ V = Module.finrank ℝ W + 1) :
    ∃ ℓ : E d →ₗ[ℝ] ℝ, ∃ n ∈ V, ℓ n = 1 ∧
      {x | x ∈ V ∧ ℓ x = 0} = (W : Set (E d)) := by
  have hlt : W < V := lt_of_le_of_ne hWV (by
    intro h
    rw [h] at hdim
    omega)
  obtain ⟨u, huV, huW⟩ := SetLike.exists_of_lt hlt
  obtain ⟨f, hfu, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem huW inferInstance
  have hWker : ∀ w ∈ W, f w = 0 := by
    intro w hw
    have h : f w ∈ W.map f := Submodule.mem_map_of_mem hw
    rw [hfW] at h
    exact (Submodule.mem_bot ℝ).mp h
  have hsup : W ⊔ Submodule.span ℝ {u} = V := by
    apply Submodule.eq_of_le_of_finrank_le
      (sup_le hWV ((Submodule.span_singleton_le_iff_mem _ _).mpr huV))
    have hlt' : W < W ⊔ Submodule.span ℝ {u} := lt_of_le_of_ne le_sup_left (by
      intro h
      apply huW
      rw [h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self u))
    have := Submodule.finrank_lt_finrank_of_lt hlt'
    omega
  refine ⟨(f u)⁻¹ • f, u, huV, by
    rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfu], ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨hxV, hx0⟩
    rw [← hsup] at hxV
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hxV
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_add, map_smul, hWker w hw, zero_add, smul_eq_mul] at hx0
    have hc : c = 0 := by
      have h' : (f u)⁻¹ * (c * f u) = c := by
        rw [mul_comm c, ← mul_assoc, inv_mul_cancel₀ hfu, one_mul]
      rw [h'] at hx0
      exact hx0
    subst hc
    simpa using hw
  · intro hxW
    exact ⟨hWV hxW, by rw [hWker x hxW, mul_zero]⟩

open scoped Topology in
/-- Auxiliary for `recursiveTrace_tiles_step3_halfspace_lift` (V4 1.16(b)): near a listed
codimension-one subcell, the relative boundary of the coface lies in the subcell's span. -/
private lemma recursiveTrace_tiles_step3_halfspace_lift_lem_local_frontier
    {A : PolyManifoldDomain d} (K : CellComplex A) {e C : Cell d}
    (he : e ∈ K.cells) (hC : C ∈ K.cells) (hdim : C.dim = e.dim + 1)
    {a : E d} (ha : a ∈ relint e.carrier) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball a r, x ∈ relfrontier C.carrier →
      x ∈ affineSpan ℝ e.carrier := by
  classical
  obtain ⟨b, hb, hboundary⟩ := K.boundary_union C hC
  have hev : ∀ g ∈ b, ∀ᶠ x in 𝓝 a, x ∈ g.carrier → x ∈ affineSpan ℝ e.carrier := by
    intro g hg
    by_cases hag : a ∈ g.carrier
    · refine Filter.Eventually.of_forall (fun x hx => ?_)
      have hgb : g.carrier ⊆ relfrontier C.carrier := by
        intro z hz
        rw [hboundary]
        exact mem_iUnion.mpr ⟨g, mem_iUnion.mpr ⟨hg, hz⟩⟩
      have heg := recursiveTrace_tiles_step3_halfspace_lift_lem_incidence K he (hb hg) ha hag
      have hlt := recursiveTrace_tiles_step3_halfspace_lift_lem_frontier_dim hgb
      have hle : cellDirection e.carrier ≤ cellDirection g.carrier :=
        AffineSubspace.direction_le (affineSpan_mono ℝ heg)
      have hdir : cellDirection e.carrier = cellDirection g.carrier := by
        apply Submodule.eq_of_le_of_finrank_le hle
        rw [C.flat.dimension, g.flat.dimension, hdim] at hlt
        rw [e.flat.dimension, g.flat.dimension]
        omega
      have hspan : affineSpan ℝ e.carrier = affineSpan ℝ g.carrier :=
        AffineSubspace.ext_of_direction_eq hdir
          ⟨a, subset_affineSpan ℝ _ (intrinsicInterior_subset ha), subset_affineSpan ℝ _ hag⟩
      rw [hspan]
      exact subset_affineSpan ℝ _ hx
    · filter_upwards [g.flat.compact.isClosed.isOpen_compl.mem_nhds hag] with x hx hxg
      exact (hx hxg).elim
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff.mp ((Filter.eventually_all_finset b).mpr hev)
  refine ⟨r, hr, fun x hx hxf => ?_⟩
  rw [hboundary] at hxf
  obtain ⟨g, hxg⟩ := mem_iUnion.mp hxf
  obtain ⟨hg, hxg⟩ := mem_iUnion.mp hxg
  exact hball hx g hg hxg

/-- Auxiliary for `recursiveTrace_tiles_step3_halfspace_lift` (V4 1.16(b)): an open half-ball
of the span avoiding the relative boundary lies inside or outside the closed set. -/
private lemma recursiveTrace_tiles_step3_halfspace_lift_lem_dichotomy {Cs : Set (E d)}
    (hcl : IsClosed Cs) (ℓ : E d →ₗ[ℝ] ℝ) (a : E d) (r : ℝ)
    (hint : ∀ x ∈ ball a r, x ∈ affineSpan ℝ Cs → ℓ a < ℓ x → x ∈ Cs → x ∈ relint Cs) :
    (∀ x ∈ ball a r, x ∈ affineSpan ℝ Cs → ℓ a < ℓ x → x ∈ Cs) ∨
      (∀ x ∈ ball a r, x ∈ affineSpan ℝ Cs → ℓ a < ℓ x → x ∉ Cs) := by
  let H : Set (E d) := ball a r ∩ ((affineSpan ℝ Cs : Set (E d)) ∩ {x | ℓ a < ℓ x})
  have hconv : Convex ℝ H :=
    (convex_ball a r).inter ((affineSpan ℝ Cs).convex.inter
      (convex_halfSpace_gt ℓ.isLinear _))
  let U : Set (E d) := {x | ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ affineSpan ℝ Cs, dist y x < ρ → y ∈ Cs}
  have hU : IsOpen U := by
    rw [Metric.isOpen_iff]
    rintro x ⟨ρ, hρ, hx⟩
    refine ⟨ρ / 2, half_pos hρ, fun z hz => ⟨ρ / 2, half_pos hρ, fun y hy hyz => hx y hy ?_⟩⟩
    have := dist_triangle y z x
    rw [mem_ball] at hz
    linarith
  have hcover : H ⊆ U ∪ Csᶜ := by
    rintro x ⟨hx, hxs, hxl⟩
    by_cases hxC : x ∈ Cs
    · exact Or.inl (recursiveTrace_tiles_step3_halfspace_lift_lem_relint.mp
        (hint x hx hxs hxl hxC)).2
    · exact Or.inr hxC
  have hdisj : H ∩ (U ∩ Csᶜ) = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro x ⟨⟨_, hxs, _⟩, ⟨ρ, hρ, hρx⟩, hxC⟩
    exact hxC (hρx x hxs (by simpa using hρ))
  rcases (isPreconnected_iff_subset_of_disjoint.mp hconv.isPreconnected) U Csᶜ hU
      hcl.isOpen_compl hcover hdisj with h | h
  · left
    intro x hx hxs hxl
    obtain ⟨ρ, hρ, hρx⟩ := h ⟨hx, hxs, hxl⟩
    exact hρx x hxs (by simpa using hρ)
  · right
    intro x hx hxs hxl
    exact h ⟨hx, hxs, hxl⟩

open scoped Topology in
/-- Auxiliary for `recursiveTrace_tiles_step3_halfspace_lift` (V4 1.16(b)): a closed set
containing an open half-ball of its span contains the closed half-ball. -/
private lemma recursiveTrace_tiles_step3_halfspace_lift_lem_closure {Cs : Set (E d)}
    (hcl : IsClosed Cs) (ℓ : E d →ₗ[ℝ] ℝ) (a n : E d) (r : ℝ)
    (hn : n ∈ (affineSpan ℝ Cs).direction) (hℓn : ℓ n = 1)
    (hpos : ∀ x ∈ ball a r, x ∈ affineSpan ℝ Cs → ℓ a < ℓ x → x ∈ Cs)
    {y : E d} (hy : y ∈ ball a r) (hys : y ∈ affineSpan ℝ Cs) (hyl : ℓ a ≤ ℓ y) :
    y ∈ Cs := by
  have ht : Filter.Tendsto (fun s : ℝ => y + s • n) (𝓝[>] 0) (𝓝 y) := by
    have hc : Continuous (fun s : ℝ => y + s • n) := by fun_prop
    simpa only [zero_smul, add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply hcl.mem_of_tendsto ht
  filter_upwards [ht.eventually (isOpen_ball.mem_nhds hy), self_mem_nhdsWithin] with s hs hs0
  apply hpos _ hs
  · have := AffineSubspace.vadd_mem_of_mem_direction
      ((affineSpan ℝ Cs).direction.smul_mem s hn) hys
    simpa only [vadd_eq_add, add_comm] using this
  · rw [map_add, map_smul, hℓn, smul_eq_mul, mul_one]
    have : (0 : ℝ) < s := hs0
    linarith


/-- Auxiliary for `recursiveTrace_tiles_step3_halfspace_lift` (V4 1.0(a), "which applies
to every cell by (H2)"): at a relative-interior point `a` of a listed codimension-one
subcell `e` of a listed cell `C`, the cell `C` coincides near `a` with one closed
half-space of `aff C` bounded by `aff e`: the open side `ℓ a < ℓ x` lies in `relint C`
and the opposite open side misses `C`. -/
private lemma recursiveTrace_tiles_step3_halfspace_lift_lem_side
    {A : PolyManifoldDomain d} (K : CellComplex A) {e C : Cell d}
    (he : e ∈ K.cells) (hC : C ∈ K.cells) (hsub : e.carrier ⊆ C.carrier)
    (hdim : C.dim = e.dim + 1) {a : E d} (ha : a ∈ relint e.carrier) :
    ∃ ℓ : E d →ₗ[ℝ] ℝ,
      (∀ v ∈ cellDirection C.carrier, ℓ v = 0 → v ∈ cellDirection e.carrier) ∧
      ∃ r : ℝ, 0 < r ∧
        (∀ x ∈ ball a r, x ∈ affineSpan ℝ C.carrier → ℓ a < ℓ x → x ∈ relint C.carrier) ∧
        (∀ x ∈ ball a r, x ∈ affineSpan ℝ C.carrier → ℓ x < ℓ a → x ∉ C.carrier) := by
  have hWV : cellDirection e.carrier ≤ cellDirection C.carrier :=
    AffineSubspace.direction_le (affineSpan_mono ℝ hsub)
  have hfin : Module.finrank ℝ (cellDirection C.carrier) =
      Module.finrank ℝ (cellDirection e.carrier) + 1 := by
    rw [C.flat.dimension, e.flat.dimension, hdim]
  obtain ⟨ℓ, n, hnV, hℓn, hker⟩ := recursiveTrace_tiles_step3_halfspace_lift_lem_functional hWV hfin
  have hcl : IsClosed C.carrier := C.flat.compact.isClosed
  have hae : a ∈ e.carrier := intrinsicInterior_subset ha
  have haC : a ∈ C.carrier := hsub hae
  have haeS : a ∈ affineSpan ℝ e.carrier := subset_affineSpan ℝ _ hae
  have hne : e ≠ C := by
    intro h
    rw [h] at hdim
    omega
  have hnotint : a ∉ relint C.carrier := fun h =>
    Set.disjoint_left.mp (K.relint_disjoint e he C hC hne) ha h
  obtain ⟨r, hr, hloc⟩ := recursiveTrace_tiles_step3_halfspace_lift_lem_local_frontier K he hC hdim ha
  have hoff : ∀ x ∈ ball a r, x ∈ affineSpan ℝ C.carrier → ℓ x ≠ ℓ a → x ∈ C.carrier →
      x ∈ relint C.carrier := by
    intro x hx _ hxl hxC
    by_contra hxi
    have hxb : x ∈ relfrontier C.carrier := by
      change x ∈ intrinsicFrontier ℝ C.carrier
      rw [← closure_diff_intrinsicInterior, hcl.closure_eq]
      exact ⟨hxC, hxi⟩
    have hxe := hloc x hx hxb
    have hW : x - a ∈ cellDirection e.carrier := by
      simpa only [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hxe haeS
    have h0 : ℓ (x - a) = 0 := by
      have h' : x - a ∈ {x | x ∈ cellDirection C.carrier ∧ ℓ x = 0} := by
        rw [hker]
        exact hW
      exact h'.2
    rw [map_sub, sub_eq_zero] at h0
    exact hxl h0
  have hd1 := recursiveTrace_tiles_step3_halfspace_lift_lem_dichotomy hcl ℓ a r
    (fun x hx hxS hxl hxC => hoff x hx hxS hxl.ne' hxC)
  have hd2 := recursiveTrace_tiles_step3_halfspace_lift_lem_dichotomy hcl (-ℓ) a r
    (fun x hx hxS hxl hxC => hoff x hx hxS (by
      simp only [LinearMap.neg_apply, neg_lt_neg_iff] at hxl
      exact hxl.ne) hxC)
  have hnS : n ∈ (affineSpan ℝ C.carrier).direction := hnV
  have hnS' : -n ∈ (affineSpan ℝ C.carrier).direction :=
    (affineSpan ℝ C.carrier).direction.neg_mem hnV
  have hℓn' : (-ℓ) (-n) = 1 := by simp [hℓn]
  have hnotboth : ¬ ((∀ x ∈ ball a r, x ∈ affineSpan ℝ C.carrier → ℓ a < ℓ x → x ∈ C.carrier) ∧
      (∀ x ∈ ball a r, x ∈ affineSpan ℝ C.carrier → (-ℓ) a < (-ℓ) x → x ∈ C.carrier)) := by
    rintro ⟨h1, h2⟩
    apply hnotint
    refine recursiveTrace_tiles_step3_halfspace_lift_lem_relint.mpr ⟨haC, r, hr, fun y hy hyd => ?_⟩
    rcases le_total (ℓ a) (ℓ y) with hle | hle
    · exact recursiveTrace_tiles_step3_halfspace_lift_lem_closure hcl ℓ a n r hnS hℓn h1 hyd hy hle
    · exact recursiveTrace_tiles_step3_halfspace_lift_lem_closure hcl (-ℓ) a (-n) r hnS' hℓn' h2
        hyd hy (by simpa using hle)
  have hnotnone : ¬ ((∀ x ∈ ball a r, x ∈ affineSpan ℝ C.carrier → ℓ a < ℓ x →
        x ∉ C.carrier) ∧
      (∀ x ∈ ball a r, x ∈ affineSpan ℝ C.carrier → (-ℓ) a < (-ℓ) x → x ∉ C.carrier)) := by
    rintro ⟨h1, h2⟩
    have hacl : a ∈ closure (relint C.carrier) := by
      rw [C.flat.regularClosed]
      exact haC
    obtain ⟨z, hzr, hz⟩ :=
      mem_closure_iff.mp hacl (ball a (r / 2)) isOpen_ball (mem_ball_self (half_pos hr))
    obtain ⟨hzC, ρ, hρ, hzρ⟩ := recursiveTrace_tiles_step3_halfspace_lift_lem_relint.mp hz
    have hzS : z ∈ affineSpan ℝ C.carrier := subset_affineSpan ℝ _ hzC
    rcases lt_or_ge (ℓ z) (ℓ a) with hlt | hle
    · exact h2 z (ball_subset_ball (half_le_self hr.le) hzr) hzS (by simpa using hlt) hzC
    · have hm : 0 < min ρ (r / 2) := lt_min hρ (half_pos hr)
      obtain ⟨s, hs0, hsn⟩ := exists_pos_mul_lt hm ‖n‖
      have hz'S : z + s • n ∈ affineSpan ℝ C.carrier := by
        have := AffineSubspace.vadd_mem_of_mem_direction
          ((affineSpan ℝ C.carrier).direction.smul_mem s hnS) hzS
        simpa only [vadd_eq_add, add_comm] using this
      have hdist : dist (z + s • n) z < min ρ (r / 2) := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0.le,
          mul_comm]
        exact hsn
      have hz'C : z + s • n ∈ C.carrier :=
        hzρ _ hz'S (lt_of_lt_of_le hdist (min_le_left _ _))
      have hz'ball : z + s • n ∈ ball a r := by
        rw [mem_ball] at hzr ⊢
        have h1 := dist_triangle (z + s • n) z a
        have h2 := min_le_right ρ (r / 2)
        linarith
      apply h1 _ hz'ball hz'S _ hz'C
      rw [map_add, map_smul, hℓn, smul_eq_mul, mul_one]
      linarith
  have hk : ∀ v ∈ cellDirection C.carrier, ℓ v = 0 → v ∈ cellDirection e.carrier := by
    intro v hv h0
    have hv' : v ∈ {x | x ∈ cellDirection C.carrier ∧ ℓ x = 0} := ⟨hv, h0⟩
    rw [hker] at hv'
    exact hv'
  rcases hd1 with h1 | h1
  · rcases hd2 with h2 | h2
    · exact (hnotboth ⟨h1, h2⟩).elim
    · refine ⟨ℓ, hk, r, hr, fun x hx hxS hxl => hoff x hx hxS hxl.ne' (h1 x hx hxS hxl), ?_⟩
      intro x hx hxS hxl
      exact h2 x hx hxS (by simpa using hxl)
  · rcases hd2 with h2 | h2
    · refine ⟨-ℓ, fun v hv h0 => hk v hv (by simpa using h0), r, hr, fun x hx hxS hxl =>
        hoff x hx hxS (by simp only [LinearMap.neg_apply, neg_lt_neg_iff] at hxl; exact hxl.ne)
          (h2 x hx hxS hxl), ?_⟩
      intro x hx hxS hxl
      exact h1 x hx hxS (by simpa using hxl)
    · exact (hnotnone ⟨h1, h2⟩).elim

/-- Auxiliary for `recursiveTrace_tiles_step3_halfspace_lift` (V4 1.0(a) for a placed
cell): the half-space description of `lem_side`, transported by an affine equivalence `g`
and stated along rays `g p + t • v`, `v` in the direction of the placed cell. -/
private lemma recursiveTrace_tiles_step3_halfspace_lift_lem_placed
    {A : PolyManifoldDomain d} (K : CellComplex A) {e C : Cell d}
    (he : e ∈ K.cells) (hC : C ∈ K.cells) (hsub : e.carrier ⊆ C.carrier)
    (hdim : C.dim = e.dim + 1) (g : E d ≃ᵃ[ℝ] E d) {p : E d} (hp : p ∈ relint e.carrier) :
    ∃ ℓ : E d →ₗ[ℝ] ℝ,
      (∀ v ∈ cellDirection (g '' C.carrier), ℓ v = 0 →
        v ∈ cellDirection (g '' e.carrier)) ∧
      (∀ v ∈ cellDirection (g '' C.carrier), 0 < ℓ v → ∃ ε : ℝ, 0 < ε ∧
        ∀ t : ℝ, 0 < t → t < ε → g p + t • v ∈ g '' relint C.carrier) ∧
      (∀ v ∈ cellDirection (g '' C.carrier), ℓ v < 0 → ∃ ε : ℝ, 0 < ε ∧
        ∀ t : ℝ, 0 < t → t < ε → g p + t • v ∉ g '' C.carrier) := by
  obtain ⟨ℓ, hk, r, hr, hpos, hneg⟩ :=
    recursiveTrace_tiles_step3_halfspace_lift_lem_side K he hC hsub hdim hp
  have hdir : ∀ X : Set (E d),
      cellDirection (g '' X) = (cellDirection X).map g.linear.toLinearMap := by
    intro X
    change (affineSpan ℝ (g.toAffineMap '' X)).direction = _
    rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
    rfl
  have hpC : p ∈ C.carrier := hsub (intrinsicInterior_subset hp)
  have hray : ∀ v0 : E d, v0 ∈ cellDirection C.carrier → ∀ t : ℝ, 0 < t →
      t < r / (‖v0‖ + 1) →
      t • v0 + p ∈ ball p r ∧ t • v0 + p ∈ affineSpan ℝ C.carrier ∧
        ℓ (t • v0 + p) = ℓ p + t * ℓ v0 ∧ g (t • v0 + p) = g p + t • g.linear v0 := by
    intro v0 hv0 t ht htε
    have htr' : t * (‖v0‖ + 1) < r := by rwa [lt_div_iff₀ (by positivity)] at htε
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg ht.le]
      nlinarith [norm_nonneg v0]
    · exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t hv0)
        (subset_affineSpan ℝ _ hpC)
    · rw [map_add, map_smul, smul_eq_mul, add_comm]
    · have h := g.map_vadd p (t • v0)
      rw [vadd_eq_add, vadd_eq_add, map_smul] at h
      rw [add_comm (g p)]
      exact h
  refine ⟨ℓ.comp g.linear.symm.toLinearMap, ?_, ?_, ?_⟩
  · intro v hv h0
    rw [hdir] at hv ⊢
    obtain ⟨v0, hv0, rfl⟩ := Submodule.mem_map.mp hv
    have h0' : ℓ v0 = 0 := by simpa using h0
    exact Submodule.mem_map.mpr ⟨v0, hk v0 hv0 h0', rfl⟩
  · intro v hv hlv
    rw [hdir] at hv
    obtain ⟨v0, hv0, rfl⟩ := Submodule.mem_map.mp hv
    have hlv' : 0 < ℓ v0 := by simpa using hlv
    refine ⟨r / (‖v0‖ + 1), by positivity, fun t ht htε => ?_⟩
    obtain ⟨hb, hs, hl, hg⟩ := hray v0 hv0 t ht htε
    show g p + t • g.linear v0 ∈ g '' relint C.carrier
    rw [← hg]
    refine ⟨_, hpos _ hb hs ?_, rfl⟩
    rw [hl]
    nlinarith
  · intro v hv hlv
    rw [hdir] at hv
    obtain ⟨v0, hv0, rfl⟩ := Submodule.mem_map.mp hv
    have hlv' : ℓ v0 < 0 := by simpa using hlv
    refine ⟨r / (‖v0‖ + 1), by positivity, fun t ht htε => ?_⟩
    obtain ⟨hb, hs, hl, hg⟩ := hray v0 hv0 t ht htε
    show g p + t • g.linear v0 ∉ g '' C.carrier
    rw [← hg]
    rintro ⟨z, hz, hzg⟩
    rw [g.injective hzg] at hz
    refine hneg _ hb hs ?_ hz
    rw [hl]
    nlinarith

/-- Auxiliary for `recursiveTrace_tiles_step3_halfspace_lift` (V4 1.0(H2)): relative
interiors pull back along affine equivalences. -/
private lemma recursiveTrace_tiles_step3_halfspace_lift_lem_relint_preimage
    (g : E d ≃ᵃ[ℝ] E d) {K : Set (E d)} {q : E d} (hq : g q ∈ relint (g '' K)) :
    q ∈ relint K := by
  obtain ⟨hqK, ρ, hρ, h⟩ := recursiveTrace_tiles_step3_halfspace_lift_lem_relint.mp hq
  have hcont : Continuous g := g.toAffineMap.continuous_of_finiteDimensional
  obtain ⟨δ, hδ, hδρ⟩ := Metric.continuous_iff.mp hcont q ρ hρ
  refine recursiveTrace_tiles_step3_halfspace_lift_lem_relint.mpr
    ⟨g.injective.mem_set_image.mp hqK, δ, hδ, fun y hy hyq => ?_⟩
  have hgy : g y ∈ affineSpan ℝ (g '' K) := by
    have hm : g y ∈ (affineSpan ℝ K).map g.toAffineMap :=
      AffineSubspace.mem_map.mpr ⟨y, hy, rfl⟩
    rw [AffineSubspace.map_span] at hm
    exact hm
  exact g.injective.mem_set_image.mp (h (g y) hgy (hδρ y hyq))

/-- Step 3 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(c), step from `j+1` to `j`,
also used in 1.22(a)): "suppose `x ∈ relint S_j ∩ relint S'_j` ... near `x` the cell
`F_{j+1}` coincides with a closed half-space of `aff F_{j+1}` bounded by `aff F_j`
(Lemma 1.0(a)) ... `S_j` is a facet of the `(j+1)`-cell `S_{j+1}`; by Lemma 1.0(a) for
`S_{j+1}` at `x`, `S_{j+1}` coincides near `x` with the closed half-space of
`aff F_{j+1}` bounded by `aff F_j` on the side of `F_{j+1}`. The same holds for
`S'_{j+1}`. Hence `relint S_{j+1} ∩ relint S'_{j+1} ≠ ∅`." Here the two recorded chains
may have the same or different owners. -/
private theorem recursiveTrace_tiles_step3_halfspace_lift {A : S.ι} {F : FacetFlag S A}
    {r : ℕ} (a b : TracePiece A F r) (i k : ChainIndex d (traceDimension d))
    (hik : k.val.val = i.val.val + 1)
    (h : (relint (a.tile.cell 0 (a.chain.cell i).val) ∩
      relint (b.tile.cell 0 (b.chain.cell i).val)).Nonempty) :
    (relint (a.tile.cell 0 (a.chain.cell k).val) ∩
      relint (b.tile.cell 0 (b.chain.cell k).val)).Nonempty := by
  classical
  obtain ⟨x, hxa0, hxb0⟩ := h
  have hle : i.val.val ≤ k.val.val := by omega
  have hdim_a : (a.chain.cell k).val.dim = (a.chain.cell i).val.dim + 1 := by
    rw [a.chain.dimension, a.chain.dimension, hik]
  have hdim_b : (b.chain.cell k).val.dim = (b.chain.cell i).val.dim + 1 := by
    rw [b.chain.dimension, b.chain.dimension, hik]
  have hxa := hxa0
  have hxb := hxb0
  rw [recursiveTrace_tiles_step0_relint_cell] at hxa hxb
  obtain ⟨pa, hpa, hpax⟩ := hxa
  obtain ⟨pb, hpb, hpbx⟩ := hxb
  obtain ⟨ℓa, hka, hposa, -⟩ := recursiveTrace_tiles_step3_halfspace_lift_lem_placed _
    (a.chain.cell i).property (a.chain.cell k).property (a.chain.nested i k hle) hdim_a
    a.tile.frame.toAffineEquiv hpa
  obtain ⟨ℓb, hkb, hposb, -⟩ := recursiveTrace_tiles_step3_halfspace_lift_lem_placed _
    (b.chain.cell i).property (b.chain.cell k).property (b.chain.nested i k hle) hdim_b
    b.tile.frame.toAffineEquiv hpb
  -- the flag cells `F_j ⊆ F_{j+1}` of the root, placed by `σ^r`
  let jF : {j : ℕ // 1 ≤ j ∧ j < d} := ⟨i.val.val, i.property.2, i.val.isLt⟩
  let kF : {j : ℕ // 1 ≤ j ∧ j < d} := ⟨k.val.val, k.property.2, k.val.isLt⟩
  have hsubF : (F.cell jF).val.carrier ⊆ (F.cell kF).val.carrier := F.nested jF kF hle
  have hdimF : (F.cell kF).val.dim = (F.cell jF).val.dim + 1 := by
    rw [F.dimension, F.dimension]
    exact hik
  let g : E d ≃ᵃ[ℝ] E d := (S.σ ^ r).toAffineEquiv
  have hxF : x ∈ relint (g '' (F.cell jF).val.carrier) := by
    obtain ⟨hxe, ρ, hρ, hball⟩ :=
      recursiveTrace_tiles_step3_halfspace_lift_lem_relint.mp hxa0
    refine recursiveTrace_tiles_step3_halfspace_lift_lem_relint.mpr
      ⟨a.chain.contained i hxe, ρ, hρ, fun y hy hyx => a.chain.contained i
        (hball y ?_ hyx)⟩
    rw [recursiveTrace_tiles_step1_span a i]
    exact hy
  have hgq : g ((S.σ ^ r).symm x) = x := (S.σ ^ r).apply_symm_apply x
  have hq : (S.σ ^ r).symm x ∈ relint (F.cell jF).val.carrier := by
    apply recursiveTrace_tiles_step3_halfspace_lift_lem_relint_preimage g
    rw [hgq]
    exact hxF
  obtain ⟨ℓF, hkF, -, hnegF⟩ := recursiveTrace_tiles_step3_halfspace_lift_lem_placed _
    (F.cell jF).property (F.cell kF).property hsubF hdimF g hq
  rw [hgq] at hnegF
  rw [show a.tile.frame.toAffineEquiv pa = x from hpax] at hposa
  rw [show b.tile.frame.toAffineEquiv pb = x from hpbx] at hposb
  -- direction spaces
  let M := cellDirection (g '' (F.cell kF).val.carrier)
  let W := cellDirection (g '' (F.cell jF).val.carrier)
  have hdir : ∀ (c : TracePiece A F r) (m : ChainIndex d (traceDimension d)),
      cellDirection (c.tile.frame.toAffineEquiv '' (c.chain.cell m).val.carrier) =
        cellDirection (g '' (F.cell ⟨m.val.val, m.property.2, m.val.isLt⟩).val.carrier) := by
    intro c m
    have h1 := congrArg AffineSubspace.direction (recursiveTrace_tiles_step1_span c m)
    rw [recursiveTrace_tiles_step0_cell_zero] at h1
    exact h1
  have hMa := hdir a k
  have hMb := hdir b k
  have hWa := hdir a i
  have hWb := hdir b i
  have hWM : W ≤ M := AffineSubspace.direction_le (affineSpan_mono ℝ (Set.image_mono hsubF))
  have hfin : ∀ j : {j : ℕ // 1 ≤ j ∧ j < d},
      Module.finrank ℝ (cellDirection (g '' (F.cell j).val.carrier)) = j.val := fun j =>
    (recursiveTrace_tiles_step0_finrank_image g _).trans
      ((F.cell j).val.flat.dimension.trans (F.dimension j))
  have hlt : W < M := lt_of_le_of_ne hWM (fun hWMeq =>
    absurd ((hfin jF).symm.trans
      ((congrArg (fun U : Submodule ℝ (E d) => Module.finrank ℝ U) hWMeq).trans (hfin kF)))
      (by show i.val.val ≠ k.val.val; omega))
  obtain ⟨n0, hn0M, hn0W⟩ := SetLike.exists_of_lt hlt
  -- the lift, for a direction on the positive side of the first chain
  have key : ∀ n ∈ M, n ∉ W → 0 < ℓa n →
      (relint (a.tile.cell 0 (a.chain.cell k).val) ∩
        relint (b.tile.cell 0 (b.chain.cell k).val)).Nonempty := by
    intro n hnM hnW hpos
    have hnb : ℓb n ≠ 0 := fun h0 => hnW (by
      have := hkb n (by rw [hMb]; exact hnM) h0
      rw [hWb] at this
      exact this)
    have hnF : ℓF n ≠ 0 := fun h0 => hnW (hkF n hnM h0)
    obtain ⟨εa, hεa, hA⟩ := hposa n (by rw [hMa]; exact hnM) hpos
    have hinA : ∀ t, 0 < t → t < εa → x + t • n ∈ g '' (F.cell kF).val.carrier := by
      intro t ht htε
      obtain ⟨z, hz, hzx⟩ := hA t ht htε
      have hmem : x + t • n ∈ a.tile.cell 0 (a.chain.cell k).val := by
        rw [recursiveTrace_tiles_step0_cell_zero, ← hzx]
        exact Set.mem_image_of_mem _ (intrinsicInterior_subset hz)
      exact a.chain.contained k hmem
    rcases lt_or_gt_of_ne hnb with hbneg | hbpos
    · -- opposite sides: impossible, since `F_{j+1}` lies on one side of `aff F_j`
      exfalso
      obtain ⟨εb, hεb, hB⟩ := hposb (-n) (by rw [hMb]; exact M.neg_mem hnM)
        (by rw [map_neg]; linarith)
      have hinB : ∀ t, 0 < t → t < εb → x + t • (-n) ∈ g '' (F.cell kF).val.carrier := by
        intro t ht htε
        obtain ⟨z, hz, hzx⟩ := hB t ht htε
        have hmem : x + t • (-n) ∈ b.tile.cell 0 (b.chain.cell k).val := by
          rw [recursiveTrace_tiles_step0_cell_zero, ← hzx]
          exact Set.mem_image_of_mem _ (intrinsicInterior_subset hz)
        exact b.chain.contained k hmem
      rcases lt_or_gt_of_ne hnF with hFneg | hFpos
      · obtain ⟨εF, hεF, hC⟩ := hnegF n hnM hFneg
        have ht : 0 < min εa εF / 2 := half_pos (lt_min hεa hεF)
        exact hC _ ht (by linarith [min_le_right εa εF])
          (hinA _ ht (by linarith [min_le_left εa εF]))
      · obtain ⟨εF, hεF, hC⟩ := hnegF (-n) (M.neg_mem hnM) (by rw [map_neg]; linarith)
        have ht : 0 < min εb εF / 2 := half_pos (lt_min hεb hεF)
        exact hC _ ht (by linarith [min_le_right εb εF])
          (hinB _ ht (by linarith [min_le_left εb εF]))
    · -- same side: a common point of both relative interiors
      obtain ⟨εb, hεb, hB⟩ := hposb n (by rw [hMb]; exact hnM) hbpos
      have ht : 0 < min εa εb / 2 := half_pos (lt_min hεa hεb)
      rw [recursiveTrace_tiles_step0_relint_cell, recursiveTrace_tiles_step0_relint_cell]
      exact ⟨x + (min εa εb / 2) • n, hA _ ht (by linarith [min_le_left εa εb]),
        hB _ ht (by linarith [min_le_right εa εb])⟩
  have hna : ℓa n0 ≠ 0 := fun h0 => hn0W (by
    have := hka n0 (by rw [hMa]; exact hn0M) h0
    rw [hWa] at this
    exact this)
  rcases lt_or_gt_of_ne hna with hneg | hpos
  · exact key (-n0) (M.neg_mem hn0M) (fun h' => hn0W (by simpa using W.neg_mem h'))
      (by rw [map_neg]; linarith)
  · exact key n0 hn0M hn0W hpos

/-- Step 12 of the V4 proof of `recursiveTrace_tiles` (V4 1.0(a), used in 1.22(c) for
`j = d-1`): "near a point of the relative interior of a facet the tile is a closed
half-ball". At a relative-interior point of a placed ground facet, the tile coincides
near the point with a closed half-space whose unit normal is orthogonal to the facet. -/
private theorem recursiveTrace_tiles_step12_placed_halfball (C : FramedNode S)
    (e : CellName S C.ty) (he : e.val.dim = d - 1) (y : E d)
    (hy : y ∈ relint (C.cell 0 e.val)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ u : E d, ‖u‖ = 1 ∧
      (∀ w ∈ cellDirection (C.cell 0 e.val), inner ℝ u w = 0) ∧
      ∀ z ∈ ball y ρ, (z ∈ C.carrier 0 ↔ 0 ≤ inner ℝ u (z - y)) := by
  have hfacet : e.val ∈ (S.cx C.ty).facets := Finset.mem_filter.2 ⟨e.property, he⟩
  rw [recursiveTrace_tiles_step0_relint_cell] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  obtain ⟨ρ, hρ, v, hv, hfr, -, hA⟩ :=
    facet_halfball (S.proto C.ty) (S.cx C.ty) e.val hfacet p hp
  have hP : IsClosed (S.proto C.ty).carrier := (S.proto C.ty).compact.isClosed
  have horth0 : ∀ w ∈ cellDirection e.val.carrier, inner ℝ v w = 0 := by
    intro w hw
    have hden : 0 < 2 * (‖w‖ + 1) := by positivity
    have ht : 0 < ρ / (2 * (‖w‖ + 1)) := div_pos hρ hden
    have hx_aff : (ρ / (2 * (‖w‖ + 1))) • w + p ∈
        (affineSpan ℝ e.val.carrier : Set (E d)) :=
      AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ _ hw)
        (subset_affineSpan ℝ _ (intrinsicInterior_subset hp))
    have hx_ball : (ρ / (2 * (‖w‖ + 1))) • w + p ∈ ball p ρ := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht]
      have h1 : ρ / (2 * (‖w‖ + 1)) * (2 * (‖w‖ + 1)) = ρ := div_mul_cancel₀ ρ hden.ne'
      nlinarith [norm_nonneg w]
    have hfront : (ρ / (2 * (‖w‖ + 1))) • w + p ∈ frontier (S.proto C.ty).carrier := by
      have hmem : (ρ / (2 * (‖w‖ + 1))) • w + p ∈
          (affineSpan ℝ e.val.carrier : Set (E d)) ∩ ball p ρ := ⟨hx_aff, hx_ball⟩
      rw [← hfr] at hmem
      exact hmem.1
    have hval : inner ℝ v ((ρ / (2 * (‖w‖ + 1))) • w + p - p) =
        ρ / (2 * (‖w‖ + 1)) * inner ℝ v w := by
      rw [add_sub_cancel_right, real_inner_smul_right]
    rcases lt_trichotomy (inner ℝ v w) 0 with hneg | hzero | hpos
    · exfalso
      have hin : (ρ / (2 * (‖w‖ + 1))) • w + p ∈ (S.proto C.ty).carrier ∩ ball p ρ :=
        ⟨hP.frontier_subset hfront, hx_ball⟩
      rw [hA] at hin
      have h0 := hin.1
      simp only [Set.mem_setOf_eq] at h0
      rw [hval] at h0
      nlinarith [mul_neg_of_pos_of_neg ht hneg]
    · exact hzero
    · exfalso
      have hopen : IsOpen ({z : E d | 0 < inner ℝ v (z - p)} ∩ ball p ρ) :=
        (isOpen_lt continuous_const
          (continuous_const.inner (continuous_id.sub continuous_const))).inter isOpen_ball
      have hsub : {z : E d | 0 < inner ℝ v (z - p)} ∩ ball p ρ ⊆
          (S.proto C.ty).carrier := by
        intro z hz
        have hz' : z ∈ {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p ρ := ⟨show 0 ≤ inner ℝ v (z - p) from le_of_lt hz.1, hz.2⟩
        rw [← hA] at hz'
        exact hz'.1
      have hint : (ρ / (2 * (‖w‖ + 1))) • w + p ∈ interior (S.proto C.ty).carrier := by
        refine interior_maximal hsub hopen ⟨?_, hx_ball⟩
        show 0 < inner ℝ v ((ρ / (2 * (‖w‖ + 1))) • w + p - p)
        rw [hval]
        exact mul_pos ht hpos
      exact Set.disjoint_left.1 disjoint_interior_frontier hint hfront
  have hdir : cellDirection (C.frame '' e.val.carrier) =
      (cellDirection e.val.carrier).map C.frame.toAffineEquiv.toAffineMap.linear := by
    change (affineSpan ℝ (C.frame.toAffineEquiv.toAffineMap '' e.val.carrier)).direction = _
    rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
    rfl
  have hvsub : ∀ z x : E d, C.frame z - C.frame x = C.frame.linearIsometryEquiv (z - x) :=
    fun z x => (C.frame.toAffineEquiv.toAffineMap.linearMap_vsub z x).symm
  have hcar : C.carrier 0 = C.frame '' (S.proto C.ty).carrier := by
    simp [FramedNode.carrier, placedSet, SubstSystem.supertile]
  refine ⟨ρ, hρ, C.frame.linearIsometryEquiv v, by rw [LinearIsometryEquiv.norm_map, hv],
    ?_, ?_⟩
  · intro w hw
    rw [recursiveTrace_tiles_step0_cell_zero, hdir] at hw
    obtain ⟨w0, hw0, rfl⟩ := Submodule.mem_map.1 hw
    rw [show C.frame.toAffineEquiv.toAffineMap.linear w0 = C.frame.linearIsometryEquiv w0
      from rfl, LinearIsometryEquiv.inner_map_map]
    exact horth0 w0 hw0
  · intro z hz
    obtain ⟨x, rfl⟩ : ∃ x, C.frame x = z := ⟨C.frame.symm z, C.frame.apply_symm_apply z⟩
    have hxb : x ∈ ball p ρ := by
      rw [Metric.mem_ball, ← C.frame.dist_map]
      exact hz
    rw [hcar, C.frame.injective.mem_set_image, hvsub, LinearIsometryEquiv.inner_map_map]
    constructor
    · intro hxP
      have hm : x ∈ (S.proto C.ty).carrier ∩ ball p ρ := ⟨hxP, hxb⟩
      rw [hA] at hm
      exact hm.1
    · intro hle
      have hm : x ∈ {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p ρ := ⟨hle, hxb⟩
      rw [← hA] at hm
      exact hm.1

/-- Step 4 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(c), base `j = d-1`, and
Lemma 1.8): "Facets of distinct children inside one facet `e` ... have disjoint relative
interiors". At native scale: two depth-`r` native facets inside the facet `σ^r F_{d-1}`
of the root whose relative interiors meet have the same native owner (both owners fill
the same inner half-ball there, contradicting disjoint native interiors). -/
private theorem recursiveTrace_tiles_step4_top_owner {A : S.ι} {F : FacetFlag S A}
    {r : ℕ} (a b : TracePiece A F r) (k : ChainIndex d (traceDimension d))
    (hk : k.val.val = d - 1)
    (h : (relint (a.tile.cell 0 (a.chain.cell k).val) ∩
      relint (b.tile.cell 0 (b.chain.cell k).val)).Nonempty) :
    a.owner = b.owner := by
  classical
  by_contra hne
  have h2 : 2 ≤ d := Fact.out
  obtain ⟨y, hya, hyb⟩ := h
  have hdima : (a.chain.cell k).val.dim = d - 1 := (a.chain.dimension k).trans hk
  have hdimb : (b.chain.cell k).val.dim = d - 1 := (b.chain.dimension k).trans hk
  obtain ⟨ρa, hρa, ua, hua, horta, hhalfa⟩ :=
    recursiveTrace_tiles_step12_placed_halfball a.tile (a.chain.cell k) hdima y hya
  obtain ⟨ρb, hρb, ub, hub, hortb, hhalfb⟩ :=
    recursiveTrace_tiles_step12_placed_halfball b.tile (b.chain.cell k) hdimb y hyb
  have hspan : cellDirection (a.tile.cell 0 (a.chain.cell k).val) =
      cellDirection (b.tile.cell 0 (b.chain.cell k).val) := by
    unfold cellDirection
    rw [recursiveTrace_tiles_step1_span a k, recursiveTrace_tiles_step1_span b k]
  have hDfin : Module.finrank ℝ (cellDirection (a.tile.cell 0 (a.chain.cell k).val)) =
      d - 1 := by
    rw [recursiveTrace_tiles_step0_cell_zero]
    exact (recursiveTrace_tiles_step0_finrank_image a.tile.frame.toAffineEquiv _).trans
      ((a.chain.cell k).val.flat.dimension.trans hdima)
  have huaD : ua ∈ (cellDirection (a.tile.cell 0 (a.chain.cell k).val))ᗮ :=
    (Submodule.mem_orthogonal' _ ua).2 fun w hw => horta w hw
  have hubD : ub ∈ (cellDirection (a.tile.cell 0 (a.chain.cell k).val))ᗮ :=
    (Submodule.mem_orthogonal' _ ub).2 fun w hw => hortb w (by rw [← hspan]; exact hw)
  have hperp : Module.finrank ℝ
      (cellDirection (a.tile.cell 0 (a.chain.cell k).val))ᗮ = 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal
      (cellDirection (a.tile.cell 0 (a.chain.cell k).val))
    rw [finrank_euclideanSpace_fin, hDfin] at hsum
    omega
  have hnz : (⟨ua, huaD⟩ : (cellDirection (a.tile.cell 0 (a.chain.cell k).val))ᗮ) ≠ 0 := by
    intro h0
    have hu0 : ua = 0 := by simpa using congrArg Subtype.val h0
    rw [hu0, norm_zero] at hua
    norm_num at hua
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hnz).1 hperp ⟨ub, hubD⟩
  have hcu : c • ua = ub := congrArg Subtype.val hc
  have hρ : 0 < min ρa ρb := lt_min hρa hρb
  rcases le_or_gt c 0 with hc0 | hc0
  · have hball : ball y (min ρa ρb) ⊆ S.supertile r A := by
      intro z hz
      rw [← S.native_cover A r]
      by_cases hz0 : 0 ≤ inner ℝ ua (z - y)
      · exact Set.mem_iUnion.2 ⟨a.owner,
          (hhalfa z (Metric.ball_subset_ball (min_le_left _ _) hz)).2 hz0⟩
      · refine Set.mem_iUnion.2 ⟨b.owner,
          (hhalfb z (Metric.ball_subset_ball (min_le_right _ _) hz)).2 ?_⟩
        rw [← hcu, real_inner_smul_left]
        push_neg at hz0
        exact mul_nonneg_of_nonpos_of_nonpos hc0 hz0.le
    have hint : y ∈ interior (S.supertile r A) :=
      interior_maximal hball Metric.isOpen_ball (Metric.mem_ball_self hρ)
    have hyF : y ∈ frontier (S.supertile r A) := by
      have hy1 : y ∈ a.tile.cell 0 (a.chain.cell k).val := intrinsicInterior_subset hya
      obtain ⟨x, hx, rfl⟩ := a.chain.contained k hy1
      have hxf : x ∈ frontier (S.proto A).carrier := by
        rw [← (S.cx A).carriers_cover]
        exact Set.mem_iUnion₂.2 ⟨_, (F.cell _).property, hx⟩
      have hh := (S.σ ^ r).toContinuousLinearEquiv.toHomeomorph.image_frontier
        (S.proto A).carrier
      have hmem : (S.σ ^ r) x ∈ (S.σ ^ r).toContinuousLinearEquiv.toHomeomorph ''
          frontier (S.proto A).carrier := ⟨x, hxf, rfl⟩
      rw [hh] at hmem
      exact hmem
    exact Set.disjoint_left.1 disjoint_interior_frontier hint hyF
  · have hopen : IsOpen ({z : E d | 0 < inner ℝ ua (z - y)} ∩ ball y (min ρa ρb)) :=
      (isOpen_lt continuous_const
        (continuous_const.inner (continuous_id.sub continuous_const))).inter
          Metric.isOpen_ball
    have hsubA : {z : E d | 0 < inner ℝ ua (z - y)} ∩ ball y (min ρa ρb) ⊆
        a.tile.carrier 0 := fun z hz =>
      (hhalfa z (Metric.ball_subset_ball (min_le_left _ _) hz.2)).2 hz.1.le
    have hsubB : {z : E d | 0 < inner ℝ ua (z - y)} ∩ ball y (min ρa ρb) ⊆
        b.tile.carrier 0 := by
      intro z hz
      refine (hhalfb z (Metric.ball_subset_ball (min_le_right _ _) hz.2)).2 ?_
      rw [← hcu, real_inner_smul_left]
      exact mul_nonneg hc0.le hz.1.le
    have hz0 : (min ρa ρb / 2) • ua + y ∈
        {z : E d | 0 < inner ℝ ua (z - y)} ∩ ball y (min ρa ρb) := by
      refine ⟨?_, ?_⟩
      · show 0 < inner ℝ ua ((min ρa ρb / 2) • ua + y - y)
        rw [add_sub_cancel_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hua]
        linarith
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul, hua,
          Real.norm_eq_abs, abs_of_pos (half_pos hρ)]
        linarith
    exact Set.disjoint_left.1 (S.native_disjoint A r hne)
      (interior_maximal hsubA hopen hz0) (interior_maximal hsubB hopen hz0)

/-- Step 5 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a)): "two distinct cells ...
with overlapping relative interiors would belong to two distinct cells of the tiling of
`F_j` (or to the same one, excluded by (H2))". Lift the overlap to the top facet
(Step 3), identify the owners there (Step 4), and then all recorded cells (Step 2). -/
private theorem recursiveTrace_tiles_step5_disjoint (A : S.ι) (F : FacetFlag S A) (r : ℕ) :
    Pairwise (fun a b : TracePiece A F r =>
      Disjoint (relint a.carrier) (relint b.carrier)) := by
  intro a b hab
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  intro hx
  have hall : ∀ n : ℕ, ∀ k : ChainIndex d (traceDimension d),
      k.val.val = traceDimension d + n →
      (relint (a.tile.cell 0 (a.chain.cell k).val) ∩
        relint (b.tile.cell 0 (b.chain.cell k).val)).Nonempty := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have hkb : k = TracePiece.bottomIndex :=
        Subtype.ext (Fin.ext (by simpa [TracePiece.bottomIndex] using hk))
      subst hkb
      exact hx
    | succ n ih =>
      intro k hk
      have hi : traceDimension d + n < d := by have := k.val.isLt; omega
      have hpos := traceDimension_pos (d := d)
      exact recursiveTrace_tiles_step3_halfspace_lift a b
        ⟨⟨traceDimension d + n, hi⟩, Nat.le_add_right _ _, by
          show 1 ≤ traceDimension d + n; omega⟩ k
        (by show k.val.val = traceDimension d + n + 1; omega) (ih _ rfl)
  have htop : ∀ k : ChainIndex d (traceDimension d),
      (relint (a.tile.cell 0 (a.chain.cell k).val) ∩
        relint (b.tile.cell 0 (b.chain.cell k).val)).Nonempty := by
    intro k
    exact hall (k.val.val - traceDimension d) k (by have := k.property.1; omega)
  have h2 : 2 ≤ d := Fact.out
  have hlt := traceDimension_lt (d := d)
  let T : ChainIndex d (traceDimension d) :=
    ⟨⟨d - 1, by omega⟩, by show traceDimension d ≤ d - 1; omega, by
      show 1 ≤ d - 1; omega⟩
  have howner := recursiveTrace_tiles_step4_top_owner a b T rfl (htop T)
  apply hab
  obtain ⟨wa, ca⟩ := a
  obtain ⟨wb, cb⟩ := b
  change wa = wb at howner
  subst howner
  have hcell : ∀ k, ca.cell k = cb.cell k := fun k =>
    recursiveTrace_tiles_step2_same_name (S.nativeTile A r wa) _ _ (htop k)
  obtain ⟨c1, _, _, _⟩ := ca
  obtain ⟨c2, _, _, _⟩ := cb
  have hc : c1 = c2 := funext fun k => hcell k
  subst hc
  rfl

/-- Step 6 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a), first stage): "The
facets of native tiles of the depth-`r` subdivision contained in `g` tile `g`" — every
point of `σ^r F_{d-1}` lies in a native facet inside it (heredity (H5)), which is a
one-element recorded chain. -/
private theorem recursiveTrace_tiles_step6_top_cover (A : S.ι) (F : FacetFlag S A)
    (r : ℕ) (hj : 1 ≤ d - 1) (hjd : d - 1 < d) (x : E d)
    (hx : x ∈ (S.σ ^ r) '' (F.cell ⟨d - 1, hj, hjd⟩).val.carrier) :
    ∃ (w : S.RoleWord A r) (c : ChainOccurrence A F r (S.nativeTile A r w) 0 (d - 1)),
      x ∈ (S.nativeTile A r w).cell 0 (c.cell ⟨⟨d - 1, hjd⟩, le_rfl, hj⟩).val := by
  classical
  obtain ⟨f, hf⟩ := S.heredity_iter A r (F.cell ⟨d - 1, hj, hjd⟩).val
    (F.cell ⟨d - 1, hj, hjd⟩).property
  have hx' := hx
  rw [hf] at hx'
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 hx'
  have hidx : ∀ i : ChainIndex d (d - 1),
      (⟨i.val.val, i.property.2, i.val.isLt⟩ : {j : ℕ // 1 ≤ j ∧ j < d}) =
        ⟨d - 1, hj, hjd⟩ := by
    intro i
    apply Subtype.ext
    have := i.property.1
    have := i.val.isLt
    show i.val.val = d - 1
    omega
  refine ⟨q.1, ⟨fun _ => ⟨q.2.val, q.2.property.1⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    show q.2.val.dim = i.val.val
    rw [q.2.property.2, F.dimension]
    have := i.property.1
    have := i.val.isLt
    show d - 1 = i.val.val
    omega
  · intro i k _
    exact Set.Subset.rfl
  · intro i
    rw [hidx i, hf, recursiveTrace_tiles_step0_cell_zero]
    intro z hz
    exact Set.mem_iUnion₂.2 ⟨q, hq, hz⟩
  · rw [recursiveTrace_tiles_step0_cell_zero]
    exact hxq

/-- Step 7 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a), restriction step): "the
minimal cell of that point in the complex of the owning tile lies in `F_{j-1}` by Lemma
1.1 and in the `j`-cell by (H2) ... The owner and chain are inherited." A `j`-cell of the
owner whose relative interior meets `σ^r F_j` and the recorded `(j+1)`-cell extends the
recorded chain. -/
private theorem recursiveTrace_tiles_step7_extend {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (w : S.RoleWord A r) (j : ℕ) (hj : 1 ≤ j) (hjd : j + 1 < d)
    (c : ChainOccurrence A F r (S.nativeTile A r w) 0 (j + 1))
    (e : CellName S (S.nativeTile A r w).ty) (he : e.val.dim = j) (x : E d)
    (hxe : x ∈ relint ((S.nativeTile A r w).cell 0 e.val))
    (hxc : x ∈ (S.nativeTile A r w).cell 0
      (c.cell ⟨⟨j + 1, hjd⟩, le_rfl, Nat.le_add_left 1 j⟩).val)
    (hxF : x ∈ (S.σ ^ r) '' (F.cell ⟨j, hj, by omega⟩).val.carrier) :
    ∃ c' : ChainOccurrence A F r (S.nativeTile A r w) 0 j,
      c'.cell ⟨⟨j, by omega⟩, le_rfl, hj⟩ = e := by
  classical
  let up : ∀ i : ChainIndex d j, i.val.val ≠ j → ChainIndex d (j + 1) :=
    fun i hi => ⟨i.val, by have := i.property.1; omega, i.property.2⟩
  let top : ChainIndex d (j + 1) := ⟨⟨j + 1, hjd⟩, le_rfl, Nat.le_add_left 1 j⟩
  have hsubP : (S.nativeTile A r w).cell 0 e.val ⊆
      (S.σ ^ r) '' (F.cell ⟨j, hj, by omega⟩).val.carrier := by
    have := hereditary_trace ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩ (S.nativeTile A r w) r 0
      (recursiveTrace_tiles_step0_native_desc A r w) (F.cell ⟨j, hj, by omega⟩).val
      e.val (F.cell ⟨j, hj, by omega⟩).property e.property
      ⟨x, hxe, by rw [recursiveTrace_tiles_step0_root_cell]; exact hxF⟩
    rwa [recursiveTrace_tiles_step0_root_cell] at this
  have hsubS : e.val.carrier ⊆ (c.cell top).val.carrier := by
    have := hereditary_trace (S.nativeTile A r w) (S.nativeTile A r w) 0 0
      (recursiveTrace_tiles_step0_self_desc _) (c.cell top).val
      e.val (c.cell top).property e.property ⟨x, hxe, hxc⟩
    rw [recursiveTrace_tiles_step0_cell_zero, recursiveTrace_tiles_step0_cell_zero] at this
    exact (Set.image_subset_image_iff (S.nativeTile A r w).frame.injective).1 this
  have key : ∀ l : {l : ℕ // 1 ≤ l ∧ l < d}, l.val = j →
      (S.σ ^ r) '' (F.cell l).val.carrier =
        (S.σ ^ r) '' (F.cell ⟨j, hj, by omega⟩).val.carrier := by
    rintro ⟨l, hl⟩ rfl
    rfl
  refine ⟨⟨fun i => if hi : i.val.val = j then e else c.cell (up i hi), ?_, ?_, ?_⟩, ?_⟩
  · intro i
    by_cases hi : i.val.val = j
    · dsimp only
      rw [dif_pos hi, he, hi]
    · dsimp only
      rw [dif_neg hi]
      exact c.dimension _
  · intro i k hik
    by_cases hi : i.val.val = j <;> by_cases hk : k.val.val = j
    · simp only [dif_pos hi, dif_pos hk, subset_refl]
    · dsimp only
      rw [dif_pos hi, dif_neg hk]
      exact hsubS.trans (c.nested top (up k hk)
        (by show j + 1 ≤ k.val.val; have := k.property.1; omega))
    · exfalso
      have := i.property.1
      omega
    · dsimp only
      rw [dif_neg hi, dif_neg hk]
      exact c.nested _ _ hik
  · intro i
    by_cases hi : i.val.val = j
    · dsimp only
      rw [dif_pos hi, key ⟨i.val.val, i.property.2, i.val.isLt⟩ hi]
      exact hsubP
    · dsimp only
      rw [dif_neg hi]
      exact c.contained (up i hi)
  · first
    | exact dif_pos rfl
    | simp

/-- Step 8 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a), restriction step): "the
minimal cell of that point in the complex of the owning tile lies in `F_{j-1}` by Lemma
1.1". At a point of `σ^r F_j` on the recorded `(j+1)`-cell that avoids all lower-dimensional
cells of the owner, the minimal cell has dimension exactly `j`. -/
private theorem recursiveTrace_tiles_step8_generic_minimal {A : S.ι} {F : FacetFlag S A}
    {r : ℕ} (w : S.RoleWord A r) (j : ℕ) (hj : 1 ≤ j) (hjd : j + 1 < d)
    (c : ChainOccurrence A F r (S.nativeTile A r w) 0 (j + 1)) (y : E d)
    (hyc : y ∈ (S.nativeTile A r w).cell 0
      (c.cell ⟨⟨j + 1, hjd⟩, le_rfl, Nat.le_add_left 1 j⟩).val)
    (hyF : y ∈ (S.σ ^ r) '' (F.cell ⟨j, hj, by omega⟩).val.carrier)
    (hgen : ∀ e : CellName S (S.nativeTile A r w).ty, e.val.dim < j →
      y ∉ (S.nativeTile A r w).cell 0 e.val) :
    ∃ e : CellName S (S.nativeTile A r w).ty, e.val.dim = j ∧
      y ∈ relint ((S.nativeTile A r w).cell 0 e.val) := by
  classical
  have hcellfin : ∀ m : Cell d, Module.finrank ℝ
      (cellDirection ((S.nativeTile A r w).cell 0 m)) = m.dim := by
    intro m
    rw [recursiveTrace_tiles_step0_cell_zero]
    exact (recursiveTrace_tiles_step0_finrank_image
      (S.nativeTile A r w).frame.toAffineEquiv _).trans m.flat.dimension
  have hfront : y ∈ frontier ((S.nativeTile A r w).carrier 0) := by
    have hcar : (S.nativeTile A r w).carrier 0 = (S.nativeTile A r w).frame ''
        (S.proto (S.nativeTile A r w).ty).carrier := by
      simp [FramedNode.carrier, placedSet, SubstSystem.supertile]
    have himg : (S.nativeTile A r w).frame ''
        frontier (S.proto (S.nativeTile A r w).ty).carrier =
        frontier ((S.nativeTile A r w).frame ''
          (S.proto (S.nativeTile A r w).ty).carrier) :=
      (S.nativeTile A r w).frame.toHomeomorph.image_frontier _
    rw [hcar, ← himg]
    rw [recursiveTrace_tiles_step0_cell_zero] at hyc
    obtain ⟨z, hz, rfl⟩ := hyc
    refine ⟨z, ?_, rfl⟩
    rw [← (S.cx _).carriers_cover]
    exact Set.mem_iUnion₂.2 ⟨_, (c.cell _).property, hz⟩
  obtain ⟨m, hm, -⟩ := placedMinimalCell_exists_unique (S.nativeTile A r w) 0 y hfront
  have hmF := hereditary_trace ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩ (S.nativeTile A r w)
    r 0 (recursiveTrace_tiles_step0_native_desc A r w) (F.cell ⟨j, hj, by omega⟩).val
    m.val (F.cell ⟨j, hj, by omega⟩).property m.property
    ⟨y, hm, by rw [recursiveTrace_tiles_step0_root_cell]; exact hyF⟩
  rw [recursiveTrace_tiles_step0_root_cell] at hmF
  have h1 := Submodule.finrank_mono (show cellDirection ((S.nativeTile A r w).cell 0 m.val) ≤
      cellDirection ((S.σ ^ r) '' (F.cell ⟨j, hj, by omega⟩).val.carrier) by
    simpa only [cellDirection, direction_affineSpan] using vectorSpan_mono ℝ hmF)
  have h2 : Module.finrank ℝ (cellDirection ((S.σ ^ r) ''
      (F.cell ⟨j, hj, by omega⟩).val.carrier)) = j :=
    (recursiveTrace_tiles_step0_finrank_image (S.σ ^ r).toAffineEquiv _).trans
      ((F.cell ⟨j, hj, by omega⟩).val.flat.dimension.trans
        (F.dimension ⟨j, hj, by omega⟩))
  have h3 := hcellfin m.val
  have hle : m.val.dim ≤ j := by
    simp only at h1
    omega
  have hge : j ≤ m.val.dim := by
    by_contra hlt
    exact hgen m (by omega) (intrinsicInterior_subset hm)
  exact ⟨m, le_antisymm hle hge, hm⟩

/-- Step 13 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a), "the cells of the
tiling that are contained in `F_{j-1}` cover it", genericity): near a point of a
`j`-dimensional set at which it contains a relative ball, there are points of the set
avoiding finitely many sets of affine dimension `< j` (move along a direction outside all
their direction spaces; a real vector space is not a finite union of proper subspaces). -/
private theorem recursiveTrace_tiles_step13_generic_avoid {ι : Type*} [Finite ι] (L : Set (E d))
    (j : ℕ) (hL : Module.finrank ℝ (cellDirection L) = j) (N : ι → Set (E d))
    (hN : ∀ i, Module.finrank ℝ (cellDirection (N i)) < j) (y : E d) (hy : y ∈ L)
    (δ : ℝ) (hδ : 0 < δ) (hball : ∀ z ∈ affineSpan ℝ L, dist z y < δ → z ∈ L) :
    ∃ z ∈ L, dist z y < δ ∧ ∀ i, z ∉ N i := by
  classical
  have hW : ∃ v : cellDirection L, ∀ i, v ∉ (cellDirection (N i)).comap
      (cellDirection L).subtype := by
    by_contra hcon
    push_neg at hcon
    have hcov : ⋃ i, (((cellDirection (N i)).comap (cellDirection L).subtype :
        Submodule ℝ (cellDirection L)) : Set (cellDirection L)) = Set.univ := by
      ext v
      simp only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_univ, iff_true]
      exact hcon v
    obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
    have hle : cellDirection L ≤ cellDirection (N i) := by
      intro v hv
      have hmem : (⟨v, hv⟩ : cellDirection L) ∈
          (cellDirection (N i)).comap (cellDirection L).subtype := by
        rw [hi]
        exact Submodule.mem_top
      exact Submodule.mem_comap.1 hmem
    have h1 := Submodule.finrank_mono hle
    have h2 := hN i
    omega
  obtain ⟨⟨v, hvV⟩, hv⟩ := hW
  have hv' : ∀ i, v ∉ cellDirection (N i) := fun i h => hv i (Submodule.mem_comap.2 h)
  have hT : ∀ i, {t : ℝ | t • v + y ∈ N i}.Subsingleton := by
    intro i t1 ht1 t2 ht2
    by_contra hne
    apply hv' i
    have hsub : (t1 • v + y) - (t2 • v + y) ∈ cellDirection (N i) := by
      simp only [cellDirection, direction_affineSpan]
      exact vsub_mem_vectorSpan ℝ ht1 ht2
    have heq : (t1 • v + y) - (t2 • v + y) = (t1 - t2) • v := by
      rw [sub_smul]
      abel
    rw [heq] at hsub
    have h12 : t1 - t2 ≠ 0 := sub_ne_zero.mpr hne
    have := (cellDirection (N i)).smul_mem (t1 - t2)⁻¹ hsub
    rwa [smul_smul, inv_mul_cancel₀ h12, one_smul] at this
  have hfin : (⋃ i, {t : ℝ | t • v + y ∈ N i}).Finite :=
    Set.finite_iUnion fun i => (hT i).finite
  have hpos : 0 < ‖v‖ + 1 := by positivity
  have hη : 0 < δ / (‖v‖ + 1) := div_pos hδ hpos
  obtain ⟨t, ht, htn⟩ := (Set.Ioo_infinite hη).exists_notMem_finite hfin
  have hdist : dist (t • v + y) y < δ := by
    rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    have h1 : t * ‖v‖ ≤ δ / (‖v‖ + 1) * ‖v‖ :=
      mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg v)
    have h2 : δ / (‖v‖ + 1) * (‖v‖ + 1) = δ := div_mul_cancel₀ δ hpos.ne'
    nlinarith [ht.2]
  refine ⟨t • v + y, ?_, hdist, ?_⟩
  · apply hball _ _ hdist
    exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t hvV)
      (subset_affineSpan ℝ L hy)
  · intro i hi
    exact htn (Set.mem_iUnion.2 ⟨i, hi⟩)

/-- Step 14 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a), genericity): a flat
`j`-cell is the closure of its points avoiding finitely many sets of affine dimension
`< j` (it is the closure of its relative interior, (H2)(iii), and Step 13 applies there). -/
private theorem recursiveTrace_tiles_step14_generic_closure {ι : Type*} [Finite ι] (L : Set (E d))
    (j : ℕ) (hLcell : IsFlatCell j L) (N : ι → Set (E d))
    (hN : ∀ i, Module.finrank ℝ (cellDirection (N i)) < j) :
    L ⊆ closure (L \ ⋃ i, N i) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hx' : x ∈ closure (relint L) := by
    rw [hLcell.regularClosed]
    exact hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx' (ε / 2) (half_pos hε)
  obtain ⟨y', hy', rfl⟩ := mem_intrinsicInterior.1 hy
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy')
  have hball : ∀ z ∈ affineSpan ℝ L, dist z (y' : E d) < δ → z ∈ L := by
    intro z hz hzd
    exact hδball (show (⟨z, hz⟩ : affineSpan ℝ L) ∈ Metric.ball y' δ from hzd)
  obtain ⟨z, hzL, hzd, hzN⟩ := recursiveTrace_tiles_step13_generic_avoid L j hLcell.dimension N hN
    y' (intrinsicInterior_subset hy) (min δ (ε / 2)) (lt_min hδ (half_pos hε))
    (fun z hz hzd => hball z hz (lt_of_lt_of_le hzd (min_le_left _ _)))
  refine ⟨z, ⟨hzL, by simpa using hzN⟩, ?_⟩
  calc dist x z ≤ dist x (y' : E d) + dist (y' : E d) z := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hxy (by
        rw [dist_comm]
        exact lt_of_lt_of_le hzd (min_le_right _ _))
    _ = ε := add_halves ε

/-- Step 9 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a), "the cells of the tiling
that are contained in `F_{j-1}` cover it"): the depth-`r` native cells of dimension `< j`
form a finite union of compact sets of affine dimension `< j`, hence are nowhere dense in
the `j`-cell `σ^r F_j`; so the points of `σ^r F_j` avoiding them are dense in it. -/
private theorem recursiveTrace_tiles_step9_generic_dense (A : S.ι) (F : FacetFlag S A)
    (r j : ℕ) (hj : 1 ≤ j) (hjd : j < d) :
    (S.σ ^ r) '' (F.cell ⟨j, hj, hjd⟩).val.carrier ⊆
      closure ((S.σ ^ r) '' (F.cell ⟨j, hj, hjd⟩).val.carrier \
        ⋃ (w : S.RoleWord A r) (e : CellName S (S.nativeTile A r w).ty)
          (_ : e.val.dim < j), (S.nativeTile A r w).cell 0 e.val) := by
  classical
  intro x hx
  obtain ⟨x0, hx0, rfl⟩ := hx
  let N : (Σ w : S.RoleWord A r,
      {e : CellName S (S.nativeTile A r w).ty // e.val.dim < j}) → Set (E d) :=
    fun q => (S.σ ^ r).symm.toAffineEquiv '' (S.nativeTile A r q.1).cell 0 q.2.val.val
  have hN : ∀ q, Module.finrank ℝ (cellDirection (N q)) < j := by
    intro q
    have h1 := recursiveTrace_tiles_step0_finrank_image (S.σ ^ r).symm.toAffineEquiv
      ((S.nativeTile A r q.1).cell 0 q.2.val.val)
    have h2 : Module.finrank ℝ (cellDirection ((S.nativeTile A r q.1).cell 0 q.2.val.val)) =
        q.2.val.val.dim := by
      rw [recursiveTrace_tiles_step0_cell_zero]
      exact (recursiveTrace_tiles_step0_finrank_image
        (S.nativeTile A r q.1).frame.toAffineEquiv _).trans q.2.val.val.flat.dimension
    exact lt_of_eq_of_lt (h1.trans h2) q.2.property
  have hflat : IsFlatCell j (F.cell ⟨j, hj, hjd⟩).val.carrier := by
    have := (F.cell ⟨j, hj, hjd⟩).val.flat
    rwa [F.dimension] at this
  have hcl := recursiveTrace_tiles_step14_generic_closure _ j hflat N hN hx0
  have hcont : Continuous (S.σ ^ r) :=
    (S.σ ^ r).toLinearMap.continuous_of_finiteDimensional
  refine closure_mono ?_ (image_closure_subset_closure_image hcont ⟨x0, hcl, rfl⟩)
  rintro _ ⟨z, ⟨hzL, hzN⟩, rfl⟩
  refine ⟨⟨z, hzL, rfl⟩, ?_⟩
  intro hB
  simp only [Set.mem_iUnion] at hB
  obtain ⟨w, e, he, hze⟩ := hB
  exact hzN (Set.mem_iUnion.2 ⟨⟨w, ⟨e, he⟩⟩, ⟨_, hze, by simp⟩⟩)

/-- Step 10 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a)): the union of the
recorded `j`-cells over the finitely many owners and cell names is closed. -/
private theorem recursiveTrace_tiles_step10_closed (A : S.ι) (F : FacetFlag S A)
    (r j : ℕ) (hj : 1 ≤ j) (hjd : j < d) :
    IsClosed (⋃ (w : S.RoleWord A r) (e : CellName S (S.nativeTile A r w).ty)
      (_ : ∃ c : ChainOccurrence A F r (S.nativeTile A r w) 0 j,
        c.cell ⟨⟨j, hjd⟩, le_rfl, hj⟩ = e),
      (S.nativeTile A r w).cell 0 e.val) := by
  refine isClosed_iUnion_of_finite fun w => isClosed_iUnion_of_finite fun e =>
    isClosed_iUnion_of_finite fun _ => ?_
  rw [recursiveTrace_tiles_step0_cell_zero]
  exact (e.val.flat.compact.image (S.nativeTile A r w).frame.continuous).isClosed

/-- Step 11 of the V4 proof of `recursiveTrace_tiles` (V4 1.22(a)): "iterating down to
`F_2`": by downward induction from the facet, every point of `σ^r F_j` lies in the
`j`-cell of a recorded chain from `j` to `d-1` (Steps 6--10). -/
private theorem recursiveTrace_tiles_step11_cover (A : S.ι) (F : FacetFlag S A) (r : ℕ) :
    ∀ n j : ℕ, ∀ (hj : 1 ≤ j) (hjd : j < d), j + n = d - 1 →
      ∀ x ∈ (S.σ ^ r) '' (F.cell ⟨j, hj, hjd⟩).val.carrier,
        ∃ (w : S.RoleWord A r) (c : ChainOccurrence A F r (S.nativeTile A r w) 0 j),
          x ∈ (S.nativeTile A r w).cell 0 (c.cell ⟨⟨j, hjd⟩, le_rfl, hj⟩).val := by
  intro n
  induction n with
  | zero =>
    intro j hj hjd hjn x hx
    obtain rfl : j = d - 1 := by omega
    exact recursiveTrace_tiles_step6_top_cover A F r hj hjd x hx
  | succ n ih =>
    intro j hj hjd hjn
    have hjd' : j + 1 < d := by omega
    have hU := recursiveTrace_tiles_step10_closed A F r j hj hjd
    have hG : ((S.σ ^ r) '' (F.cell ⟨j, hj, hjd⟩).val.carrier \
        ⋃ (w : S.RoleWord A r) (e : CellName S (S.nativeTile A r w).ty)
          (_ : e.val.dim < j), (S.nativeTile A r w).cell 0 e.val) ⊆
        ⋃ (w : S.RoleWord A r) (e : CellName S (S.nativeTile A r w).ty)
          (_ : ∃ c : ChainOccurrence A F r (S.nativeTile A r w) 0 j,
            c.cell ⟨⟨j, hjd⟩, le_rfl, hj⟩ = e),
          (S.nativeTile A r w).cell 0 e.val := by
      rintro y ⟨hyF, hygen⟩
      have hyF1 : y ∈ (S.σ ^ r) '' (F.cell ⟨j + 1, by omega, hjd'⟩).val.carrier :=
        Set.image_mono (F.nested ⟨j, hj, hjd⟩ ⟨j + 1, by omega, hjd'⟩ (Nat.le_succ j)) hyF
      obtain ⟨w, c, hyc⟩ := ih (j + 1) (by omega) hjd' (by omega) y hyF1
      obtain ⟨e, he, hye⟩ := recursiveTrace_tiles_step8_generic_minimal w j hj hjd' c y hyc
        hyF (fun e he hy => hygen (Set.mem_iUnion₂.2 ⟨w, e, Set.mem_iUnion.2 ⟨he, hy⟩⟩))
      obtain ⟨c', hc'⟩ := recursiveTrace_tiles_step7_extend w j hj hjd' c e he y hye hyc hyF
      exact Set.mem_iUnion₂.2 ⟨w, e, Set.mem_iUnion.2 ⟨⟨c', hc'⟩,
        intrinsicInterior_subset hye⟩⟩
    intro x hx
    have hxU := (closure_minimal hG hU)
      (recursiveTrace_tiles_step9_generic_dense A F r j hj hjd hx)
    simp only [Set.mem_iUnion] at hxU
    obtain ⟨w, e, ⟨c, hce⟩, hxe⟩ := hxU
    refine ⟨w, c, ?_⟩
    rw [hce]
    exact hxe

/-- P17, V4 1.22(a): the trace tiles the designated two-cell, or the edge when
`d = 2`, and its distinct occurrences have disjoint relative interiors. -/
theorem recursiveTrace_tiles (A : S.ι) (F : FacetFlag S A) (r : ℕ) :
    (⋃ a ∈ recursiveTrace A F r, a.carrier) =
      (S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
        traceDimension_lt⟩).val.carrier ∧
    Pairwise (fun a b : TracePiece A F r => Disjoint (relint a.carrier)
      (relint b.carrier)) ∧
    ∀ a : TracePiece A F r, ∀ i : ChainIndex d (traceDimension d),
      affineSpan ℝ (a.tile.cell 0 (a.chain.cell i).val) =
        affineSpan ℝ ((S.σ ^ r) ''
          (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier) := by
  refine ⟨?_, recursiveTrace_tiles_step5_disjoint A F r,
    fun a i => recursiveTrace_tiles_step1_span a i⟩
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun a _ => ?_
    exact a.chain.contained TracePiece.bottomIndex
  · intro x hx
    have hlt := traceDimension_lt (d := d)
    obtain ⟨w, c, hxc⟩ := recursiveTrace_tiles_step11_cover A F r
      (d - 1 - traceDimension d) (traceDimension d) traceDimension_pos traceDimension_lt
      (by omega) x hx
    exact Set.mem_iUnion₂.2 ⟨⟨w, c⟩, by simp [recursiveTrace], hxc⟩

/-- P17, V4 1.22(b): all standard native frames are compatible. -/
theorem nativeFrame_mem (A : S.ι) (r : ℕ) (w : S.RoleWord A r) :
    (S.nativeTile A r w).frame.linearIsometryEquiv ∈ S.rotGroup := by
  have hd := S.descendant_frames A 0 r w (AffineIsometryEquiv.refl ℝ (E d))
  obtain ⟨R, hR, eq⟩ := hd
  have h_eq : (S.nativeTile A r w).frame.linearIsometryEquiv = R := by
    dsimp [SubstSystem.nativeTile]
    have hz : (AffineIsometryEquiv.refl ℝ (E d)).linearIsometryEquiv = 1 := rfl
    rw [hz, one_mul] at eq
    dsimp [FramedNode.move] at eq
    exact eq
  rw [h_eq]
  exact hR

/-- P17, V4 1.22(b): inflate a native owner to a height-`s` node, keeping its
entire native subdivision, rather than choosing a geometric containing tile. -/
def inflatedNative (A : S.ι) (r : ℕ) (w : S.RoleWord A r) (s : ℕ) : FramedNode S :=
  ⟨(S.nativeTile A r w).ty,
    compatibleInflatedFrame (S.nativeTile A r w) (nativeFrame_mem A r w) s⟩

/-- P17, V4 1.22(b): finer trace pieces refine both the owner and every coface.
Native-scale levels `r` and `r+s` are compared by the common ambient map `σˢ`. -/
theorem trace_refines (A : S.ι) (F : FacetFlag S A) (r s : ℕ)
    (b : TracePiece A F (r + s)) :
    ∃ a : TracePiece A F r,
      b.tile.IsDescendant 0 (inflatedNative A r a.owner s) s ∧
      ∀ i : ChainIndex d (traceDimension d),
        b.tile.cell 0 (b.chain.cell i).val ⊆
          (S.σ ^ s) '' (a.tile.cell 0 (a.chain.cell i).val) := by
  sorry

open private ancestor_descendant_child
  hereditary_trace_step7_carrier hereditary_trace_step1_cell_frontier
  facet_dichotomy_step1c_unique_sub hereditary_trace_step2_relint_mono
  hereditary_trace_step1_relint_unique
  boundary_facet_adjacency_step2_distinct_children
  from Enforce.Source.Trace in
/-- Step 1 of the V4 proof of `chain_occurrences_disjoint` (V4 1.22(c)): For j=d-1, facets of
distinct children have disjoint relative interiors by containment in facets of P and Lemma 1.8. -/
private lemma chain_occurrences_disjoint_step1_top {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}
    (A : S.ι) (F : FacetFlag S A) (r h : ℕ)
    (P : FramedNode S) (hP : S.IsStandardNode A r (h + 1) P)
    (i l : S.I P.ty) (hil : i ≠ l) (j0 : ℕ)
    (a : ChainOccurrence A F r (P.child h i) h j0)
    (b : ChainOccurrence A F r (P.child h l) h j0)
    (k : ℕ) (hjk : j0 ≤ k) (hk1 : 1 ≤ k) (hkd : k < d) (htop : k + 1 = d) :
    Disjoint (relint ((P.child h i).cell h (a.cell ⟨⟨k, hkd⟩, hjk, hk1⟩).val))
             (relint ((P.child h l).cell h (b.cell ⟨⟨k, hkd⟩, hjk, hk1⟩).val)) := by
  let q : ChainIndex d j0 := ⟨⟨k, hkd⟩, hjk, hk1⟩
  let fa : FacetName S (P.child h i).ty :=
    ⟨(a.cell q).val, Finset.mem_filter.mpr
      ⟨(a.cell q).property, by
        have hd := a.dimension q
        change (a.cell q).val.dim = k at hd
        omega⟩⟩
  let fb : FacetName S (P.child h l).ty :=
    ⟨(b.cell q).val, Finset.mem_filter.mpr
      ⟨(b.cell q).property, by
        have hd := b.dimension q
        change (b.cell q).val.dim = k at hd
        omega⟩⟩
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hPR : P.carrier (h+1) ⊆ R.carrier r := by
    obtain ⟨t, ht, w, hw⟩ := hP
    have ht_eq : h + 1 + t = r := by omega
    have h_desc : P.IsDescendant (h + 1) R (h + 1 + t) := by
      refine ⟨t, rfl, w, ?_⟩
      simpa [R, FramedNode.move] using hw
    have H1 := hereditary_trace_step7_carrier R P (h + 1) t h_desc
    rwa [ht_eq] at H1
  rw [Set.disjoint_left]
  intro x hxa hxb
  have hxR : x ∈ frontier (R.carrier r) := by
    apply hereditary_trace_step1_cell_frontier R r
      (F.cell ⟨k,hk1,hkd⟩).val (F.cell ⟨k,hk1,hkd⟩).property
    rw [recursiveTrace_tiles_step0_root_cell]
    exact a.contained q (intrinsicInterior_subset hxa)
  have lift (u : S.I P.ty) (f : FacetName S (P.child h u).ty)
      (hx : x ∈ relint ((P.child h u).cell h f.val)) :
      ∃ e : FacetName S P.ty,
        (P.child h u).cell h f.val ⊆ P.cell (h+1) e.val := by
    rcases facet_dichotomy P (P.child h u) (h+1) h
        (ancestor_descendant_child P h u) f with he | hint
    · obtain ⟨e, he, _⟩ := he
      exact ⟨e, he⟩
    · exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier
        (interior_mono hPR (hint hx)) hxR)
  obtain ⟨e, ha⟩ := lift i fa hxa
  obtain ⟨e', hb⟩ := lift l fb hxb
  have hxe := hereditary_trace_step2_relint_mono _ _ ha
    (facet_dichotomy_step1c_unique_sub P (P.child h i) (h+1) h fa e ha) hxa
  have hxe' := hereditary_trace_step2_relint_mono _ _ hb
    (facet_dichotomy_step1c_unique_sub P (P.child h l) (h+1) h fb e' hb) hxb
  have he : e = e' := Subtype.ext
    (hereditary_trace_step1_relint_unique P (h+1) e.val e'.val
      (Finset.mem_filter.mp e.property).1
      (Finset.mem_filter.mp e'.property).1 x hxe hxe')
  subst e'
  let aa : BoundaryFacet P h e := ⟨⟨i,fa⟩,ha⟩
  let bb : BoundaryFacet P h e := ⟨⟨l,fb⟩,hb⟩
  exact Set.disjoint_left.mp
    (boundary_facet_adjacency_step2_distinct_children P h e aa bb hil) hxa hxb

/-- Step 2 of the V4 proof of `chain_occurrences_disjoint` (V4 1.22(c)): Step from j+1 to j.
If the relative interiors of the j-cells intersect, half-space geometry implies that the
relative interiors of the (j+1)-cells also intersect, contradicting the induction hypothesis. -/
private theorem chain_occurrences_disjoint_step2_down {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}
    (A : S.ι) (F : FacetFlag S A) (r h : ℕ)
    (P : FramedNode S) (hP : S.IsStandardNode A r (h + 1) P)
    (i l : S.I P.ty) (hil : i ≠ l) (j0 : ℕ)
    (a : ChainOccurrence A F r (P.child h i) h j0)
    (b : ChainOccurrence A F r (P.child h l) h j0)
    (k : ℕ) (hjk : j0 ≤ k) (hk1 : 1 ≤ k) (hkd : k < d) (hkd' : k + 1 < d)
    (hjk1 : j0 ≤ k + 1) (hk11 : 1 ≤ k + 1)
    (ih : Disjoint (relint ((P.child h i).cell h (a.cell ⟨⟨k+1, hkd'⟩, hjk1, hk11⟩).val))
                   (relint ((P.child h l).cell h (b.cell ⟨⟨k+1, hkd'⟩, hjk1, hk11⟩).val))) :
    Disjoint (relint ((P.child h i).cell h (a.cell ⟨⟨k, hkd⟩, hjk, hk1⟩).val))
             (relint ((P.child h l).cell h (b.cell ⟨⟨k, hkd⟩, hjk, hk1⟩).val)) := by
  sorry

private theorem chain_occurrences_disjoint_aux {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}
    (A : S.ι) (F : FacetFlag S A) (r h : ℕ)
    (P : FramedNode S) (hP : S.IsStandardNode A r (h + 1) P)
    (i l : S.I P.ty) (hil : i ≠ l) (j0 : ℕ)
    (a : ChainOccurrence A F r (P.child h i) h j0)
    (b : ChainOccurrence A F r (P.child h l) h j0) (n : ℕ) :
    ∀ (k : ℕ) (hjk : j0 ≤ k) (hk1 : 1 ≤ k) (hkd : k < d), k + n = d - 1 →
    Disjoint (relint ((P.child h i).cell h (a.cell ⟨⟨k, hkd⟩, hjk, hk1⟩).val))
             (relint ((P.child h l).cell h (b.cell ⟨⟨k, hkd⟩, hjk, hk1⟩).val)) := by
  induction n with
  | zero =>
    intro k hjk hk1 hkd hn
    exact chain_occurrences_disjoint_step1_top A F r h P hP i l hil j0 a b k hjk hk1 hkd (by omega)
  | succ n ih =>
    intro k hjk hk1 hkd hn
    have hkd' : k + 1 < d := by omega
    have hjk1 : j0 ≤ k + 1 := by omega
    have hk11 : 1 ≤ k + 1 := by omega
    exact chain_occurrences_disjoint_step2_down A F r h P hP i l hil j0 a b k hjk hk1 hkd hkd'
      hjk1 hk11 (ih (k + 1) hjk1 hk11 hkd' (by omega))

/-- P17, V4 1.22(c): disjointness is asserted only for children with the full
coface chain, including zero-trace sectors correctly by excluding chainless cells. -/
theorem chain_occurrences_disjoint (A : S.ι) (F : FacetFlag S A) (r h : ℕ)
    (P : FramedNode S) (hP : S.IsStandardNode A r (h + 1) P)
    (i l : S.I P.ty) (hil : i ≠ l) (j : ℕ) (hj : 1 ≤ j) (hjd : j < d)
    (a : ChainOccurrence A F r (P.child h i) h j)
    (b : ChainOccurrence A F r (P.child h l) h j) :
    Disjoint (relint ((P.child h i).cell h
      (a.cell ⟨⟨j, hjd⟩, le_rfl, hj⟩).val))
      (relint ((P.child h l).cell h (b.cell ⟨⟨j, hjd⟩, le_rfl, hj⟩).val)) := by
  exact chain_occurrences_disjoint_aux A F r h P hP i l hil j a b (d - 1 - j) j le_rfl hj hjd (by omega)

/-- P18, V4 1.23: the original flag edge at native scale after `r` expansions. -/
def flagEdge (A : S.ι) (F : FacetFlag S A) (r : ℕ) : Set (E d) :=
  (S.σ ^ r) '' (F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val.carrier

/-- P18, V4 1.23: an edge of a trace polygon lying along the outer flag edge,
with the specified endpoint. This also covers the one-dimensional trace. -/
def BoundaryTraceEdge {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (a : TracePiece A F r) (q : E d) (K : Set (E d)) : Prop :=
  ∃ e : CellName S a.tile.ty, e.val.dim = 1 ∧ K = a.tile.cell 0 e.val ∧
    K ⊆ a.carrier ∧ K ⊆ flagEdge A F r ∧ q ∈ K ∧ a.tile.Lists 0 q

/-- P18, V4 1.23, dimension-two paragraph: inward trace arms.
For a planar trace the arm is an internal tile edge leaving the boundary edge;
otherwise it is an edge of a trace polygon entering the relative interior of `F₂`. -/
def InwardTraceArm (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d) : Prop :=
  if d = 2 then
    ∃ (w : S.RoleWord A r) (e : CellName S (S.nativeTile A r w).ty),
      e.val.dim = 1 ∧ (S.nativeTile A r w).Lists 0 q ∧
      q ∈ (S.nativeTile A r w).cell 0 e.val ∧
      relint ((S.nativeTile A r w).cell 0 e.val) ⊆ interior (S.supertile r A)
  else
    ∃ (a : TracePiece A F r) (e : CellName S a.tile.ty),
      e.val.dim = 1 ∧ a.tile.Lists 0 q ∧ q ∈ a.tile.cell 0 e.val ∧
      a.tile.cell 0 e.val ⊆ a.carrier ∧
      relint (a.tile.cell 0 e.val) ⊆
        relint ((S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
          traceDimension_lt⟩).val.carrier)

/-- P18, V4 1.23: ordinary sites, with two distinct owners adjacent along the
edge and an inward arm. Distinct native owners have least common ancestor at a
strictly smaller depth; the explicit common standard ancestor retains that condition. -/
def IsSite (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d) : Prop :=
  q ∈ relint (flagEdge A F r) ∧ InwardTraceArm A F r q ∧
    ∃ (a b : TracePiece A F r) (K L : Set (E d)),
      a.owner ≠ b.owner ∧ BoundaryTraceEdge a q K ∧ BoundaryTraceEdge b q L ∧
      (∃ x ∈ relint K, ∃ y ∈ relint L, q ∈ openSegment ℝ x y) ∧
      ∃ (j : ℕ) (P : FramedNode S), j < r ∧ S.IsStandardNode A r (r - j) P ∧
        a.tile.IsDescendant 0 P (r - j) ∧ b.tile.IsDescendant 0 P (r - j)

/-- P18, V4 1.23(a): an owner change on the flag edge: a relative-interior point of
the edge where two boundary edges of trace pieces with distinct owners meet from
opposite sides. These are exactly the "junction points at which the owners differ". -/
private def sitesExistOwnerChange (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d) : Prop :=
  q ∈ relint (flagEdge A F r) ∧
    ∃ (a b : TracePiece A F r) (K L : Set (E d)),
      a.owner ≠ b.owner ∧ BoundaryTraceEdge a q K ∧ BoundaryTraceEdge b q L ∧
      (∃ x ∈ relint K, ∃ y ∈ relint L, q ∈ openSegment ℝ x y)

/-- Step 1 of the V4 proof of `sites_exist` (V4 1.23(a), (H3)): a one-dimensional
cell, such as the prototype flag edge `h₀`, has two distinct points (so `|h₀| > 0`). -/
private theorem sites_exist_step1_two_points (e : Cell d) (he : e.dim = 1) :
    ∃ x ∈ e.carrier, ∃ y ∈ e.carrier, x ≠ y := by
  by_contra hne
  push_neg at hne
  have hbot : cellDirection e.carrier = ⊥ := by
    unfold cellDirection
    rw [direction_affineSpan, vectorSpan_def, Submodule.span_eq_bot]
    rintro z ⟨x, hx, y, hy, rfl⟩
    rw [hne x hx y hy]
    exact vsub_self y
  have h1 : Module.finrank ℝ (cellDirection e.carrier) = 1 := e.flat.dimension.trans he
  rw [hbot, finrank_bot] at h1
  exact zero_ne_one h1

/-- Step 1 of the V4 proof of `sites_exist` (V4 1.23(a), (7.1)/(H3)):
"The length of `h` in `σ^r A` is `≥ c^r |h| → ∞` (H3)"; i.e.
`|h_r| ≥ a b^r |h₀| → ∞`. For every bound `L`, from some depth on the flag edge
contains two points at distance at least `L`. -/
private theorem sites_exist_step1_long_edge (A : S.ι) (F : FacetFlag S A) (L : ℝ) :
    ∃ r : ℕ, ∀ r' : ℕ, r ≤ r' →
      ∃ x ∈ flagEdge A F r', ∃ y ∈ flagEdge A F r', L ≤ dist x y := by
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
  obtain ⟨x, hx, y, hy, hxy⟩ := sites_exist_step1_two_points
    (F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val (F.dimension _)
  have hpos : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨r, hr⟩ : ∃ r : ℕ, L / dist x y < S.c ^ r :=
    ((tendsto_pow_atTop_atTop_of_one_lt S.c_gt_one).eventually
      (Filter.eventually_gt_atTop _)).exists
  refine ⟨r, fun r' hr' => ?_⟩
  refine ⟨(S.σ ^ r') x, by unfold flagEdge; exact ⟨x, hx, rfl⟩,
    (S.σ ^ r') y, by unfold flagEdge; exact ⟨y, hy, rfl⟩, ?_⟩
  have hmono : S.c ^ r ≤ S.c ^ r' := pow_le_pow_right₀ S.c_gt_one.le hr'
  calc
    L ≤ S.c ^ r * dist x y := by
      have := (div_lt_iff₀ hpos).mp hr
      linarith
    _ ≤ S.c ^ r' * dist x y := mul_le_mul_of_nonneg_right hmono hpos.le
    _ ≤ _ := hdist r' x y

/-- Step 1 of the V4 proof of `sites_exist_step2_owner_changes` (V4 1.23(a)): "Let `D`
bound native tile diameters ... since that run lies in one native tile". Trace pieces
with the same owner lie in one native tile, an isometric copy of one of the finitely
many prototiles, so all their points are within a uniform distance `D`. -/
private theorem sites_exist_step2_owner_changes_step1_diameter (A : S.ι) (F : FacetFlag S A) :
    ∃ D : ℝ, ∀ (r : ℕ) (a b : TracePiece A F r), a.owner = b.owner →
      ∀ u ∈ a.carrier, ∀ v ∈ b.carrier, dist u v ≤ D := by
  have hB : Bornology.IsBounded (⋃ T : S.ι, (S.proto T).carrier) :=
    Bornology.isBounded_iUnion.2 fun T => (S.proto T).compact.isBounded
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hB
  refine ⟨C, fun r a b hab u hu v hv => ?_⟩
  have key : ∀ c : TracePiece A F r,
      c.carrier ⊆ c.tile.frame '' (S.proto c.tile.ty).carrier := by
    intro c
    have he : relint c.bottom.val.carrier ⊆ frontier (S.proto c.tile.ty).carrier := by
      rw [← (S.cx c.tile.ty).cover]
      exact Set.subset_iUnion_of_subset c.bottom.val
        (Set.subset_iUnion_of_subset c.bottom.property (Set.Subset.refl _))
    have hsub : c.bottom.val.carrier ⊆ (S.proto c.tile.ty).carrier := by
      calc c.bottom.val.carrier = closure (relint c.bottom.val.carrier) :=
          c.bottom.val.flat.regularClosed.symm
        _ ⊆ closure (frontier (S.proto c.tile.ty).carrier) := closure_mono he
        _ = frontier (S.proto c.tile.ty).carrier := isClosed_frontier.closure_eq
        _ ⊆ closure (S.proto c.tile.ty).carrier := frontier_subset_closure
        _ = (S.proto c.tile.ty).carrier :=
          (S.proto c.tile.ty).compact.isClosed.closure_eq
    rw [TracePiece.carrier, recursiveTrace_tiles_step0_cell_zero]
    exact Set.image_mono hsub
  have htile : a.tile = b.tile := by
    unfold TracePiece.tile
    rw [hab]
  have hv' := key b hv
  rw [← htile] at hv'
  obtain ⟨u', hu', rfl⟩ := key a hu
  obtain ⟨v', hv'', rfl⟩ := hv'
  rw [a.tile.frame.dist_map]
  exact hC (Set.mem_iUnion.2 ⟨_, hu'⟩) (Set.mem_iUnion.2 ⟨_, hv''⟩)

/-- Step 2 of the V4 proof of `sites_exist_step2_owner_changes` (V4 1.23(a), (H2)): "the
prototype flag edge `h_0`". A one-dimensional compact connected flat cell is a
nondegenerate segment. -/
private theorem sites_exist_step2_owner_changes_step2_cell_segment (e : Cell d)
    (he : e.dim = 1) : ∃ a b : E d, a ≠ b ∧ e.carrier = segment ℝ a b := by
  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := sites_exist_step1_two_points e he
  set w : E d := b₀ - a₀ with hw_def
  have hw : w ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hwn : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hw)
  let ℓ : E d → ℝ := fun z => inner ℝ (z - a₀) w / ‖w‖ ^ 2
  let g : ℝ →ᵃ[ℝ] E d := AffineMap.lineMap a₀ b₀
  have hV : Module.finrank ℝ (cellDirection e.carrier) = 1 := e.flat.dimension.trans he
  have hcoord : ∀ z ∈ e.carrier, g (ℓ z) = z := by
    intro z hz
    have hzV : z -ᵥ a₀ ∈ cellDirection e.carrier := by
      unfold cellDirection
      rw [direction_affineSpan]
      exact vsub_mem_vectorSpan ℝ hz ha₀
    have hwV : b₀ -ᵥ a₀ ∈ cellDirection e.carrier := by
      unfold cellDirection
      rw [direction_affineSpan]
      exact vsub_mem_vectorSpan ℝ hb₀ ha₀
    have hwV0 : (⟨b₀ -ᵥ a₀, hwV⟩ : cellDirection e.carrier) ≠ 0 := by
      intro h
      apply hw
      have := congrArg Subtype.val h
      simpa [hw_def] using this
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hwV0).1 hV ⟨z -ᵥ a₀, hzV⟩
    have hc' : c • w = z - a₀ := by
      have := congrArg Subtype.val hc
      simpa [hw_def] using this
    have hℓ : ℓ z = c := by
      change inner ℝ (z - a₀) w / ‖w‖ ^ 2 = c
      rw [← hc', real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    rw [hℓ]
    change AffineMap.lineMap a₀ b₀ c = z
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    change c • w + a₀ = z
    rw [hc']
    abel
  have hcont : Continuous ℓ :=
    ((continuous_id.sub continuous_const).inner continuous_const).div_const _
  set T := ℓ '' e.carrier with hT_def
  have hTc : IsCompact T := e.flat.compact.image hcont
  have hTp : IsPreconnected T :=
    e.flat.connected.isPreconnected.image ℓ hcont.continuousOn
  have hne : T.Nonempty := ⟨ℓ a₀, a₀, ha₀, rfl⟩
  have hm : sInf T ∈ T := hTc.sInf_mem hne
  have hM : sSup T ∈ T := hTc.sSup_mem hne
  have hTeq : T = Icc (sInf T) (sSup T) := by
    apply Set.Subset.antisymm
    · intro t ht
      exact ⟨csInf_le hTc.bddBelow ht, le_csSup hTc.bddAbove ht⟩
    · exact hTp.Icc_subset hm hM
  have hK : e.carrier = g '' T := by
    ext z
    constructor
    · intro hz
      exact ⟨ℓ z, ⟨z, hz, rfl⟩, hcoord z hz⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [hcoord z hz]
      exact hz
  have hℓa : ℓ a₀ = 0 := by
    change inner ℝ (a₀ - a₀) w / ‖w‖ ^ 2 = 0
    simp
  have hℓb : ℓ b₀ = 1 := by
    change inner ℝ (b₀ - a₀) w / ‖w‖ ^ 2 = 1
    rw [← hw_def, real_inner_self_eq_norm_sq, div_self hwn]
  have hmM : sInf T < sSup T := by
    have h0 : sInf T ≤ 0 := hℓa ▸ csInf_le hTc.bddBelow ⟨a₀, ha₀, rfl⟩
    have h1 : 1 ≤ sSup T := hℓb ▸ le_csSup hTc.bddAbove ⟨b₀, hb₀, rfl⟩
    linarith
  refine ⟨g (sInf T), g (sSup T), ?_, ?_⟩
  · exact (AffineMap.lineMap_injective ℝ hab).ne hmM.ne
  · have hgT : g '' T = segment ℝ (g (sInf T)) (g (sSup T)) := by
      rw [← image_segment, segment_eq_Icc hmM.le, ← hTeq]
    rw [hK, hgT]

/-- Step 2 of the V4 proof of `sites_exist_step2_owner_changes` (V4 1.23(a)): "Let
`h_r = σ^r h_0`". The depth-`r` flag edge, the image of the one-dimensional compact
connected flag cell `h_0` under the linear equivalence `σ^r`, is a nondegenerate
segment. -/
private theorem sites_exist_step2_owner_changes_step2_flag_segment (A : S.ι)
    (F : FacetFlag S A) (r : ℕ) :
    ∃ p₀ p₁ : E d, p₀ ≠ p₁ ∧ flagEdge A F r = segment ℝ p₀ p₁ := by
  obtain ⟨a, b, hab, hK⟩ := sites_exist_step2_owner_changes_step2_cell_segment
    (F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val (F.dimension _)
  refine ⟨(S.σ ^ r) a, (S.σ ^ r) b, (S.σ ^ r).injective.ne hab, ?_⟩
  unfold flagEdge
  rw [hK]
  exact image_segment ℝ (S.σ ^ r).toLinearMap.toAffineMap a b

open private hereditary_trace_step6_same hereditary_trace_step1_relint_unique
  hereditary_trace_step2_relint_mono hereditary_trace_step3_dim_mono
  from Enforce.Source.Trace in
/-- Step 2 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (local half-disc geometry at the flag edge; the same argument as Step 1 of `sites_exist_step3_inward_arm`, which is stated later in the file) (V4 1.23(a), via (H2)):
"`F₂` ... near `q` is a half-plane, by Lemma 1.0(a) applied to its boundary edge" uses
that the only listed cell of dimension `≤ 1` of the root `H` through a relative-interior
point `q` of the flag edge `h` is `h` itself (relative interiors are disjoint). -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step21_edge_cell (A : S.ι) (F : FacetFlag S A)
    (r : ℕ) (q : E d) (hq : q ∈ relint (flagEdge A F r)) (G : CellName S A)
    (hG : G.val.dim ≤ 1) (hqG : q ∈ (S.σ ^ r) '' G.val.carrier) :
    G.val = (F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val := by
  set h := F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩ with hh
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hR : ∀ e : Cell d, R.cell r e = (S.σ ^ r) '' e.carrier :=
    recursiveTrace_tiles_step0_root_cell A r
  have hqh : q ∈ relint (R.cell r h.val) := by rw [hR]; exact hq
  have hsubI : R.cell r h.val ⊆ R.cell r G.val :=
    hereditary_trace_step6_same R r G.val h.val G.property h.property
      ⟨q, hqh, by rw [hR]; exact hqG⟩
  have hsub : h.val.carrier ⊆ G.val.carrier := by
    have h' := hsubI
    rw [hR, hR, Set.image_subset_image_iff (S.σ ^ r).injective] at h'
    exact h'
  have hdim : G.val.dim = 1 := le_antisymm hG
    ((F.dimension _).symm.le.trans (hereditary_trace_step3_dim_mono _ _ hsub))
  have hdir : cellDirection (R.cell r h.val) = cellDirection (R.cell r G.val) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · simpa only [cellDirection, direction_affineSpan] using vectorSpan_mono ℝ hsubI
    · have h1 : Module.finrank ℝ (cellDirection (R.cell r h.val)) = 1 := by
        rw [hR]
        exact (recursiveTrace_tiles_step0_finrank_image (S.σ ^ r).toAffineEquiv _).trans
          (h.val.flat.dimension.trans (F.dimension _))
      have h2 : Module.finrank ℝ (cellDirection (R.cell r G.val)) = 1 := by
        rw [hR]
        exact (recursiveTrace_tiles_step0_finrank_image (S.σ ^ r).toAffineEquiv _).trans
          (G.val.flat.dimension.trans hdim)
      rw [h1, h2]
  have hspan : affineSpan ℝ (R.cell r h.val) = affineSpan ℝ (R.cell r G.val) :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir
      ((affineSpan_nonempty ℝ).2 ⟨q, intrinsicInterior_subset hqh⟩) (affineSpan_mono ℝ hsubI)
  have hqG' : q ∈ relint (R.cell r G.val) :=
    hereditary_trace_step2_relint_mono _ _ hsubI hspan hqh
  exact (hereditary_trace_step1_relint_unique R r h.val G.val h.property G.property q
    hqh hqG').symm
/-- Step 2 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (local half-disc geometry at the flag edge; the same argument as Step 11 of `sites_exist_step3_inward_arm`, which is stated later in the file) (V4 1.23(a), (H2)): "the
finitely many polygons ... containing `q`": listed cells of a tile missing `q` are at
positive distance from `q`, so near `q` only listed cells through `q` are met. -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step211_local_cells (C : FramedNode S) (q : E d)
    (P : Set (E d)) (Φ : Cell d → Prop)
    (hall : ∀ e ∈ (S.cx C.ty).cells, Φ e → q ∈ C.cell 0 e → C.cell 0 e ⊆ P) :
    ∃ ρ > 0, ∀ x ∈ ball q ρ, ∀ e ∈ (S.cx C.ty).cells, Φ e → x ∈ C.cell 0 e → x ∈ P := by
  classical
  let U : Set (E d) := ⋃ e ∈ (S.cx C.ty).cells.filter (fun e => q ∉ C.cell 0 e), C.cell 0 e
  have hU : IsClosed U := by
    refine isClosed_biUnion_finset fun e _ => ?_
    rw [recursiveTrace_tiles_step0_cell_zero]
    exact (e.flat.compact.image C.frame.continuous).isClosed
  have hqU : q ∉ U := by
    intro h
    obtain ⟨e, he, hqe⟩ := Set.mem_iUnion₂.1 h
    exact (Finset.mem_filter.1 he).2 hqe
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU.isOpen_compl q hqU
  refine ⟨ρ, hρ, fun x hx e he hΦ hxe => ?_⟩
  by_cases hqe : q ∈ C.cell 0 e
  · exact hall e he hΦ hqe hxe
  · exact (hball hx (Set.mem_iUnion₂.2 ⟨e, Finset.mem_filter.2 ⟨he, hqe⟩, hxe⟩)).elim

/-- Step 2 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (local half-disc geometry at the flag edge; the same argument as Step 12 of `sites_exist_step3_inward_arm`, which is stated later in the file) (V4 1.23(a), (H2)): a listed
vertex is a single point ("the listed vertices through `q` are `{q}`"). -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step212_point (C : FramedNode S) (e : Cell d)
    (he : e.dim = 0) {x y : E d} (hx : x ∈ C.cell 0 e) (hy : y ∈ C.cell 0 e) : x = y := by
  have h0 : Module.finrank ℝ (cellDirection (C.cell 0 e)) = 0 := by
    rw [recursiveTrace_tiles_step0_cell_zero]
    exact (recursiveTrace_tiles_step0_finrank_image C.frame.toAffineEquiv _).trans
      (e.flat.dimension.trans he)
  have hbot : cellDirection (C.cell 0 e) = ⊥ := Submodule.finrank_eq_zero.1 h0
  have hv : x -ᵥ y ∈ cellDirection (C.cell 0 e) := by
    unfold cellDirection
    rw [direction_affineSpan]
    exact vsub_mem_vectorSpan ℝ hx hy
  rw [hbot, Submodule.mem_bot] at hv
  exact vsub_eq_zero_iff_eq.1 hv

open private hereditary_trace_step2_boundary from Enforce.Source.Trace in
/-- Step 2 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (local half-disc geometry at the flag edge; the same argument as Step 4 of `sites_exist_step3_inward_arm`, which is stated later in the file) (V4 1.23(a), fan paragraph):
"A trace polygon containing `q` in an edge interior would have that edge along the
boundary line". If every listed edge of a trace polygon (or trace edge) through `q`
lies along the flag edge, then near `q` its whole relative boundary lies along the flag
edge: the relative boundary is a finite union of listed cells (H2)(ii); those missing
`q` are at positive distance, the listed vertices through `q` are `{q}`, and a listed
cell inside the relative boundary of a polygon has dimension `≤ 1`. -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step24_flat_plane (A : S.ι) (F : FacetFlag S A)
    (r : ℕ) (q : E d) (c : TracePiece A F r) (hqF : q ∈ flagEdge A F r)
    (hall : ∀ e : CellName S c.tile.ty, e.val.dim = 1 → q ∈ c.tile.cell 0 e.val →
      c.tile.cell 0 e.val ⊆ c.carrier → c.tile.cell 0 e.val ⊆ flagEdge A F r) :
    ∃ ρ > 0, relfrontier c.carrier ∩ ball q ρ ⊆ flagEdge A F r := by
  obtain ⟨ρ, hρ, hloc⟩ := sites_exist_step2_owner_changes_step3_edge_cover_step211_local_cells c.tile q
    (flagEdge A F r) (fun e => e.dim ≤ 1 ∧ c.tile.cell 0 e ⊆ c.carrier) (by
      rintro e he ⟨hdim, hsub⟩ hqe
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hdim with h0 | h1
      · intro y hy
        rw [sites_exist_step2_owner_changes_step3_edge_cover_step212_point c.tile e h0 hy hqe]
        exact hqF
      · exact hall ⟨e, he⟩ h1 hqe hsub)
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  obtain ⟨hxf, hxb⟩ := hx
  have hcl : IsClosed c.carrier := by
    unfold TracePiece.carrier
    rw [recursiveTrace_tiles_step0_cell_zero]
    exact (c.bottom.val.flat.compact.image c.tile.frame.continuous).isClosed
  have hxc : x ∈ c.carrier ∧ x ∉ relint c.carrier := by
    unfold relfrontier at hxf
    rw [← closure_diff_intrinsicInterior, hcl.closure_eq] at hxf
    exact hxf
  obtain ⟨G, hG, hlt, hsubG, hxG⟩ := hereditary_trace_step2_boundary c.tile 0 c.bottom.val
    c.bottom.property x hxc.1 hxc.2
  have hbd : c.bottom.val.dim = traceDimension d := c.chain.dimension TracePiece.bottomIndex
  have h2 : traceDimension d ≤ 2 := min_le_left _ _
  exact hloc x hxb G hG ⟨by omega, hsubG⟩ hxG

open private hereditary_trace_step2_relint_mono from Enforce.Source.Trace in
/-- Step 2 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (local half-disc geometry at the flag edge; the same argument as Step 6 of `sites_exist_step3_inward_arm`, which is stated later in the file) (V4 1.23(a), fan paragraph):
"... overlapping one of the two adjacent polygons". Every trace polygon through `q` has
relative-interior points arbitrarily close to `q` (its cell is the closure of its
relative interior, (H2)(iii)), and these lie in `relint F₂` (`G₂ ⊆ F₂`,
`aff G₂ = aff F₂`). -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step26_overlap_plane (A : S.ι)
    (F : FacetFlag S A) (r : ℕ) (q : E d) (b : TracePiece A F r) (hqb : q ∈ b.carrier)
    (ρ : ℝ) (hρ : 0 < ρ) :
    (relint b.carrier ∩ ball q ρ).Nonempty ∧
      relint b.carrier ⊆ relint ((S.σ ^ r) '' (F.cell ⟨traceDimension d,
        traceDimension_pos, traceDimension_lt⟩).val.carrier) := by
  refine ⟨?_, ?_⟩
  · have hcl : closure (relint b.carrier) = b.carrier := by
      unfold TracePiece.carrier
      rw [recursiveTrace_tiles_step0_relint_cell, recursiveTrace_tiles_step0_cell_zero]
      have h := b.tile.frame.toHomeomorph.image_closure (relint b.bottom.val.carrier)
      rw [AffineIsometryEquiv.coe_toHomeomorph] at h
      rw [← h, b.bottom.val.flat.regularClosed]
    have hq' : q ∈ closure (relint b.carrier) := by rw [hcl]; exact hqb
    obtain ⟨y, hy, hyq⟩ := Metric.mem_closure_iff.1 hq' ρ hρ
    exact ⟨y, hy, by rw [mem_ball, dist_comm]; exact hyq⟩
  · exact hereditary_trace_step2_relint_mono _ _ (b.chain.contained TracePiece.bottomIndex)
      (recursiveTrace_tiles_step1_span b TracePiece.bottomIndex)
/-- Step 2 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (local half-disc geometry at the flag edge; the same argument as Step 14 of `sites_exist_step3_inward_arm`, which is stated later in the file) (linear algebra behind
"near `q` the two-dimensional flag cell is a half-plane"): a line `L` inside a plane
`P` through `q` is the zero set in `P` of a linear functional, nonzero on `P`. -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step214_functional (L P : AffineSubspace ℝ (E d))
    (q : E d) (hqL : q ∈ L) (hLP : L ≤ P) (hdimL : Module.finrank ℝ L.direction = 1)
    (hdimP : Module.finrank ℝ P.direction = 2) :
    ∃ f : E d →ₗ[ℝ] ℝ, ∃ v ∈ P.direction, f v ≠ 0 ∧
      (∀ x ∈ P, f x = f q → x ∈ L) ∧ (∀ x ∈ L, f x = f q) := by
  have hqP : q ∈ P := hLP hqL
  have hdirle := AffineSubspace.direction_le hLP
  have hlt : L.direction < P.direction := by
    refine lt_of_le_of_ne hdirle fun h => ?_
    rw [h] at hdimL
    omega
  obtain ⟨v, hvP, hvL⟩ := SetLike.exists_of_lt hlt
  obtain ⟨f, hfv, hfL⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hvL inferInstance
  have hfL' : ∀ l ∈ L.direction, f l = 0 := fun l hl => by
    have hm : f l ∈ L.direction.map f := Submodule.mem_map_of_mem hl
    rw [hfL] at hm
    exact (Submodule.mem_bot ℝ).1 hm
  have hvle : ℝ ∙ v ≤ P.direction := (Submodule.span_singleton_le_iff_mem _ _).2 hvP
  have hsup : L.direction ⊔ ℝ ∙ v = P.direction := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le hdirle hvle)
    have hlt2 : L.direction < L.direction ⊔ ℝ ∙ v := by
      refine lt_of_le_of_ne le_sup_left fun h => hvL ?_
      rw [h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt2
    have h3 := Submodule.finrank_mono (sup_le hdirle hvle)
    try simp only at h3
    omega
  refine ⟨f, v, hvP, hfv, ?_, ?_⟩
  · intro x hx hfx
    have hxq : x -ᵥ q ∈ P.direction := AffineSubspace.vsub_mem_direction hx hqP
    rw [← hsup, Submodule.mem_sup] at hxq
    obtain ⟨y, hy, z, hz, hyz⟩ := hxq
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have hfxq : f (x -ᵥ q) = t * f v := by
      rw [← hyz, map_add, hfL' y hy, map_smul, smul_eq_mul, zero_add]
    have h0 : t * f v = 0 := by
      rw [← hfxq, vsub_eq_sub, map_sub, hfx, sub_self]
    have ht : t = 0 := (mul_eq_zero.1 h0).resolve_right hfv
    subst ht
    rw [zero_smul, add_zero] at hyz
    rw [hyz] at hy
    exact (AffineSubspace.vsub_right_mem_direction_iff_mem hqL x).1 hy
  · intro x hx
    have hxq : x -ᵥ q ∈ L.direction := AffineSubspace.vsub_mem_direction hx hqL
    have := hfL' _ hxq
    rw [vsub_eq_sub, map_sub, sub_eq_zero] at this
    exact this

/-- Step 2 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (local half-disc geometry at the flag edge; the same argument as Step 15 of `sites_exist_step3_inward_arm`, which is stated later in the file) (V4 1.23(a), Lemma 1.0(a)
for the flag cell, topological part): if near `q` the relative boundary of a closed
plane cell `T` lies on the line `{f = f q}` of its plane, and that line misses
`relint T`, then near `q` the relative interior of `T` is one of the two open half-discs
(or empty), hence convex: each half-disc is connected and misses the relative boundary,
and both cannot lie in `T` since `q ∉ relint T`. -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step215_core (T E0 : Set (E d)) (q : E d)
    (f : E d →ₗ[ℝ] ℝ) (v : E d) (hvP : v ∈ (affineSpan ℝ T).direction) (hfv : f v ≠ 0)
    (hTcl : IsClosed T) (hqE : q ∈ E0) (hqP : q ∈ affineSpan ℝ T)
    (hEdisj : ∀ p ∈ E0, p ∉ relint T) (hLf : ∀ x ∈ E0, f x = f q)
    (O : Set (E d)) (hO : IsOpen O) (hOeq : relint T = O ∩ (affineSpan ℝ T : Set (E d)))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hloc : ∀ x ∈ ball q ρ, x ∈ T → x ∉ relint T → x ∈ E0)
    (hlineK : ∀ x ∈ ball q ρ, x ∈ affineSpan ℝ T → f x = f q → x ∈ E0) :
    ∃ ρ' > 0, Convex ℝ (relint T ∩ ball q ρ') := by
  have hsep : ∀ Hs : Set (E d), Convex ℝ Hs → Hs ⊆ affineSpan ℝ T → Hs ⊆ ball q ρ →
      (∀ x ∈ Hs, f x ≠ f q) → Hs ⊆ relint T ∨ Hs ⊆ Tᶜ := by
    intro Hs hHc hHP hHb hHf
    have hcover : Hs ⊆ O ∪ Tᶜ := by
      intro x hx
      by_cases hxT : x ∈ T
      · left
        by_cases hxr : x ∈ relint T
        · rw [hOeq] at hxr
          exact hxr.1
        · exact (hHf x hx (hLf x (hloc x (hHb hx)
            hxT hxr))).elim
      · exact Or.inr hxT
    have hempty : ¬ (Hs ∩ (O ∩ Tᶜ)).Nonempty := by
      rintro ⟨x, hx, hxO, hxT⟩
      have hxr : x ∈ relint T := by rw [hOeq]; exact ⟨hxO, hHP hx⟩
      exact hxT (intrinsicInterior_subset hxr)
    rcases (isPreconnected_iff_subset_of_disjoint.1 hHc.isPreconnected) O Tᶜ hO
        hTcl.isOpen_compl hcover (Set.not_nonempty_iff_eq_empty.1 hempty) with h | h
    · left
      intro x hx
      rw [hOeq]
      exact ⟨h hx, hHP hx⟩
    · exact Or.inr h
  let Hp : Set (E d) := {x | f q < f x} ∩ (affineSpan ℝ T : Set (E d)) ∩ ball q ρ
  let Hm : Set (E d) := {x | f x < f q} ∩ (affineSpan ℝ T : Set (E d)) ∩ ball q ρ
  have hHpc : Convex ℝ Hp :=
    ((convex_halfSpace_gt f.isLinear (f q)).inter (affineSpan ℝ T).convex).inter
      (convex_ball q ρ)
  have hHmc : Convex ℝ Hm :=
    ((convex_halfSpace_lt f.isLinear (f q)).inter (affineSpan ℝ T).convex).inter
      (convex_ball q ρ)
  have hsplit : relint T ∩ ball q ρ ⊆ Hp ∪ Hm := by
    rintro x ⟨hxr, hxb⟩
    have hxP : x ∈ affineSpan ℝ T := mem_affineSpan ℝ (intrinsicInterior_subset hxr)
    rcases lt_trichotomy (f x) (f q) with h | h | h
    · exact Or.inr ⟨⟨h, hxP⟩, hxb⟩
    · exact (hEdisj x (hlineK x hxb hxP h) hxr).elim
    · exact Or.inl ⟨⟨h, hxP⟩, hxb⟩
  rcases hsep Hp hHpc (fun x hx => hx.1.2) (fun x hx => hx.2) (fun x hx => hx.1.1.ne') with
    hp | hp <;>
  rcases hsep Hm hHmc (fun x hx => hx.1.2) (fun x hx => hx.2) (fun x hx => hx.1.1.ne) with
    hm | hm
  · -- both half-discs are inside: then `q ∈ relint F₂`, impossible
    exfalso
    have hPT : ∀ x ∈ affineSpan ℝ T, x ∈ ball q ρ → x ∈ T := by
      intro x hxP hxb
      rcases lt_trichotomy (f x) (f q) with h | h | h
      · exact intrinsicInterior_subset (hm ⟨⟨h, hxP⟩, hxb⟩)
      · rw [← hTcl.closure_eq, Metric.mem_closure_iff]
        intro ε hε
        have hδ : 0 < min ε (ρ - dist x q) := lt_min hε (sub_pos.2 (mem_ball.1 hxb))
        set s := min ε (ρ - dist x q) / (2 * (‖v‖ + 1)) with hs
        have hs0 : 0 < s := div_pos hδ (by positivity)
        have hsv : s * ‖v‖ < min ε (ρ - dist x q) := by
          rw [hs, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg v]
        have hy1 : dist x (x + s • v) = s * ‖v‖ := by
          rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hs0.le]
        have hyP : x + s • v ∈ affineSpan ℝ T := by
          have : s • v +ᵥ x ∈ affineSpan ℝ T :=
            AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ s hvP) hxP
          rwa [vadd_eq_add, add_comm] at this
        have hyb : x + s • v ∈ ball q ρ := by
          rw [mem_ball]
          calc dist (x + s • v) q ≤ dist (x + s • v) x + dist x q := dist_triangle _ _ _
            _ = s * ‖v‖ + dist x q := by rw [dist_comm, hy1]
            _ < ρ := by have := min_le_right ε (ρ - dist x q); linarith
        have hfy : f (x + s • v) ≠ f q := by
          rw [map_add, map_smul, smul_eq_mul, h]
          intro h'
          have : s * f v = 0 := by linarith
          exact hfv ((mul_eq_zero.1 this).resolve_left hs0.ne')
        refine ⟨x + s • v, ?_, ?_⟩
        · rcases lt_or_gt_of_ne hfy with h' | h'
          · exact intrinsicInterior_subset (hm ⟨⟨h', hyP⟩, hyb⟩)
          · exact intrinsicInterior_subset (hp ⟨⟨h', hyP⟩, hyb⟩)
        · rw [hy1]
          exact lt_of_lt_of_le hsv (min_le_left _ _)
      · exact intrinsicInterior_subset (hp ⟨⟨h, hxP⟩, hxb⟩)
    have hsubB : (Subtype.val ⁻¹' ball q ρ : Set (affineSpan ℝ T)) ⊆
        Subtype.val ⁻¹' T := by
      intro y hy
      rw [Set.mem_preimage] at hy ⊢
      exact hPT y.1 y.2 hy
    have hopenB : IsOpen (Subtype.val ⁻¹' ball q ρ : Set (affineSpan ℝ T)) :=
      isOpen_ball.preimage continuous_subtype_val
    have hqB : (⟨q, hqP⟩ : affineSpan ℝ T) ∈ (Subtype.val ⁻¹' ball q ρ : Set (affineSpan ℝ T)) := by
      rw [Set.mem_preimage]
      exact mem_ball_self hρ
    have hint : (⟨q, hqP⟩ : affineSpan ℝ T) ∈
        interior (Subtype.val ⁻¹' T : Set (affineSpan ℝ T)) :=
      interior_maximal hsubB hopenB hqB
    have hqr : q ∈ intrinsicInterior ℝ T := mem_intrinsicInterior.2 ⟨⟨q, hqP⟩, hint, rfl⟩
    exact hEdisj q hqE hqr
  · refine ⟨ρ, hρ, ?_⟩
    have : relint T ∩ ball q ρ = Hp := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hsplit hx with h | h
        · exact h
        · exact (hm h (intrinsicInterior_subset hx.1)).elim
      · intro x hx
        exact ⟨hp hx, hx.2⟩
    rw [this]
    exact hHpc
  · refine ⟨ρ, hρ, ?_⟩
    have : relint T ∩ ball q ρ = Hm := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hsplit hx with h | h
        · exact (hp h (intrinsicInterior_subset hx.1)).elim
        · exact h
      · intro x hx
        exact ⟨hm hx, hx.2⟩
    rw [this]
    exact hHmc
  · refine ⟨ρ, hρ, ?_⟩
    have : relint T ∩ ball q ρ = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x hx
      rcases hsplit hx with h | h
      · exact hp h (intrinsicInterior_subset hx.1)
      · exact hm h (intrinsicInterior_subset hx.1)
    rw [this]
    exact convex_empty

open private hereditary_trace_step6_same hereditary_trace_step3_dim_mono
  hereditary_trace_step2_boundary from Enforce.Source.Trace in
set_option maxHeartbeats 1600000 in
/-- Step 2 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (local half-disc geometry at the flag edge; the same argument as Step 13 of `sites_exist_step3_inward_arm`, which is stated later in the file) (V4 1.23(a), Lemma 1.0(a)
for the flag cell): "For `d ≥ 3`, near `q` the two-dimensional flag cell is a
half-plane, by Lemma 1.0(a) applied to its boundary edge." Hence, near `q ∈ relint h`,
the relative interior of `F₂` is an open half-disc, in particular convex. -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step213_half_disc (hd : d ≠ 2) (A : S.ι)
    (F : FacetFlag S A) (r : ℕ) (q : E d) (hq : q ∈ relint (flagEdge A F r)) :
    ∃ ρ > 0, Convex ℝ (relint ((S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
      traceDimension_lt⟩).val.carrier) ∩ ball q ρ) := by
  classical
  have h2 : 2 ≤ d := Fact.out
  have htd : traceDimension d = 2 := by unfold traceDimension; omega
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hR : ∀ e : Cell d, R.cell r e = (S.σ ^ r) '' e.carrier :=
    recursiveTrace_tiles_step0_root_cell A r
  set T := (S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
    traceDimension_lt⟩).val.carrier with hT
  have hqE : q ∈ flagEdge A F r := intrinsicInterior_subset hq
  have hET : flagEdge A F r ⊆ T :=
    Set.image_mono (F.nested ⟨1, le_rfl, by omega⟩
      ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩ (by show 1 ≤ traceDimension d; omega))
  have hTcl : IsClosed T :=
    ((F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.flat.compact.image
      (S.σ ^ r).toContinuousLinearEquiv.continuous).isClosed
  -- the flag edge misses `relint F₂`
  have hEdisj : ∀ p ∈ flagEdge A F r, p ∉ relint T := by
    intro p hp hpT
    have hsub := hereditary_trace_step6_same R r
      (F.cell ⟨1, le_rfl, by omega⟩).val
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val
      (F.cell _).property (F.cell _).property
      ⟨p, by rw [hR]; exact hpT, by rw [hR]; exact hp⟩
    rw [hR, hR, Set.image_subset_image_iff (S.σ ^ r).injective] at hsub
    have hle := hereditary_trace_step3_dim_mono _ _ hsub
    have h1 : (F.cell ⟨1, le_rfl, by omega⟩).val.dim = 1 := F.dimension _
    have h2' : (F.cell ⟨traceDimension d, traceDimension_pos,
        traceDimension_lt⟩).val.dim = traceDimension d := F.dimension _
    omega
  -- near `q`, the relative boundary of `F₂` lies in the flag edge
  obtain ⟨ρ1, hρ1, hloc⟩ : ∃ ρ1 > 0, ∀ x ∈ ball q ρ1, x ∈ T → x ∉ relint T →
      x ∈ flagEdge A F r := by
    let U : Set (E d) := ⋃ G ∈ (S.cx A).cells.filter
      (fun G => q ∉ (S.σ ^ r) '' G.carrier), (S.σ ^ r) '' G.carrier
    have hU : IsClosed U := isClosed_biUnion_finset fun G _ =>
      (G.flat.compact.image (S.σ ^ r).toContinuousLinearEquiv.continuous).isClosed
    have hqU : q ∉ U := by
      intro h
      obtain ⟨G, hG, hqG⟩ := Set.mem_iUnion₂.1 h
      exact (Finset.mem_filter.1 hG).2 hqG
    obtain ⟨ρ1, hρ1, hball⟩ := Metric.isOpen_iff.1 hU.isOpen_compl q hqU
    refine ⟨ρ1, hρ1, fun x hx hxT hxr => ?_⟩
    obtain ⟨G, hG, hlt, -, hxG⟩ := hereditary_trace_step2_boundary R r
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val
      (F.cell _).property x (by rw [hR]; exact hxT) (by rw [hR]; exact hxr)
    rw [hR] at hxG
    by_cases hqG : q ∈ (S.σ ^ r) '' G.carrier
    · have hGd : G.dim ≤ 1 := by
        have : (F.cell ⟨traceDimension d, traceDimension_pos,
          traceDimension_lt⟩).val.dim = traceDimension d := F.dimension _
        omega
      have hGh := sites_exist_step2_owner_changes_step3_edge_cover_step21_edge_cell A F r q hq ⟨G, hG⟩ hGd hqG
      change x ∈ (S.σ ^ r) '' (⟨G, hG⟩ : CellName S A).val.carrier at hxG
      rw [hGh] at hxG
      exact hxG
    · exact (hball hx (Set.mem_iUnion₂.2 ⟨G, Finset.mem_filter.2 ⟨hG, hqG⟩, hxG⟩)).elim
  -- near `q`, the line of the flag edge lies in the flag edge
  obtain ⟨ρ2, hρ2, hline⟩ : ∃ ρ2 > 0, ∀ x ∈ ball q ρ2,
      x ∈ (affineSpan ℝ (flagEdge A F r) : Set (E d)) → x ∈ flagEdge A F r := by
    have hopen := (isOpen_interior : IsOpen (interior
      ((↑) ⁻¹' flagEdge A F r : Set (affineSpan ℝ (flagEdge A F r)))))
    obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.1 hopen
    have hq' := hq
    rw [relint, mem_intrinsicInterior] at hq'
    obtain ⟨y, hy, hyq⟩ := hq'
    have hqO : q ∈ O := by
      rw [← hpre] at hy
      rw [← hyq]
      exact hy
    obtain ⟨ρ2, hρ2, hb⟩ := Metric.isOpen_iff.1 hO q hqO
    refine ⟨ρ2, hρ2, fun x hx hxA => ?_⟩
    have hxi : (⟨x, hxA⟩ : affineSpan ℝ (flagEdge A F r)) ∈
        interior ((↑) ⁻¹' flagEdge A F r : Set (affineSpan ℝ (flagEdge A F r))) := by
      rw [← hpre]
      exact hb hx
    have hxm := interior_subset hxi
    exact hxm
  -- `relint F₂` is open in the plane `aff F₂`
  obtain ⟨O, hO, hOeq⟩ : ∃ O : Set (E d), IsOpen O ∧
      relint T = O ∩ (affineSpan ℝ T : Set (E d)) := by
    have hopen := (isOpen_interior :
      IsOpen (interior ((↑) ⁻¹' T : Set (affineSpan ℝ T))))
    obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.1 hopen
    refine ⟨O, hO, ?_⟩
    ext x
    constructor
    · intro hx
      rw [relint, mem_intrinsicInterior] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [← hpre] at hy
      exact ⟨hy, y.property⟩
    · rintro ⟨hxO, hxA⟩
      rw [relint, mem_intrinsicInterior]
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      rw [← hpre]
      exact hxO
  obtain ⟨f, v, hvP, hfv, hK, hLf⟩ := sites_exist_step2_owner_changes_step3_edge_cover_step214_functional
    (affineSpan ℝ (flagEdge A F r)) (affineSpan ℝ T) q (mem_affineSpan ℝ hqE)
    (affineSpan_mono ℝ hET)
    ((recursiveTrace_tiles_step0_finrank_image (S.σ ^ r).toAffineEquiv _).trans
      ((F.cell ⟨1, le_rfl, by omega⟩).val.flat.dimension.trans (F.dimension _)))
    ((recursiveTrace_tiles_step0_finrank_image (S.σ ^ r).toAffineEquiv _).trans
      ((F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.flat.dimension.trans
        ((F.dimension _).trans htd)))
  exact sites_exist_step2_owner_changes_step3_edge_cover_step215_core T (flagEdge A F r) q f v hvP hfv hTcl hqE
    (mem_affineSpan ℝ (hET hqE)) hEdisj (fun x hx => hLf x (mem_affineSpan ℝ hx)) O hO hOeq (min ρ1 ρ2) (lt_min hρ1 hρ2)
    (fun x hx hxT hxr => hloc x (ball_subset_ball (min_le_left _ _) hx) hxT hxr)
    (fun x hx hxP hfx => hline x (ball_subset_ball (min_le_right _ _) hx) (hK x hxP hfx))

open private hereditary_trace_step6_same hereditary_trace_step3_dim_mono
  from Enforce.Source.Trace in
/-- Step 2 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (local half-disc geometry at the flag edge; the same argument as Step 5 of `sites_exist_step3_inward_arm`, which is stated later in the file) (V4 1.23(a), fan paragraph,
`d ≥ 3`): "near `q` the two-dimensional flag cell is a half-plane, by Lemma 1.0(a)
applied to its boundary edge. A trace polygon ... would ... occupy a whole half-disc".
A trace polygon through `q` whose relative boundary near `q` lies along the flag edge
contains, near `q`, the whole open half-disc `relint F₂` (connectedness of the half-disc,
which misses the relative boundary of the polygon and meets its relative interior). -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step25_fill_plane (hd : d ≠ 2) (A : S.ι)
    (F : FacetFlag S A) (r : ℕ) (q : E d) (hq : q ∈ relint (flagEdge A F r))
    (c : TracePiece A F r) (hqc : q ∈ c.carrier) (ρ : ℝ) (hρ : 0 < ρ)
    (hfl : relfrontier c.carrier ∩ ball q ρ ⊆ flagEdge A F r) :
    ∃ ρ' > 0, relint ((S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
      traceDimension_lt⟩).val.carrier) ∩ ball q ρ' ⊆ relint c.carrier := by
  obtain ⟨ρ0, hρ0, hconv⟩ := sites_exist_step2_owner_changes_step3_edge_cover_step213_half_disc hd A F r q hq
  set T := (S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
    traceDimension_lt⟩).val.carrier with hT
  refine ⟨min ρ0 ρ, lt_min hρ0 hρ, ?_⟩
  have hDc : Convex ℝ (relint T ∩ ball q (min ρ0 ρ)) := by
    have hD : relint T ∩ ball q (min ρ0 ρ) =
        (relint T ∩ ball q ρ0) ∩ ball q (min ρ0 ρ) := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, ball_subset_ball (min_le_left _ _) h2⟩, h2⟩
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
    rw [hD]
    exact hconv.inter (convex_ball _ _)
  have hEdisj : ∀ p ∈ flagEdge A F r, p ∉ relint T := by
    intro p hp hpT
    let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
    have hR : ∀ e : Cell d, R.cell r e = (S.σ ^ r) '' e.carrier :=
      recursiveTrace_tiles_step0_root_cell A r
    have hsub := hereditary_trace_step6_same R r
      (F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val
      (F.cell _).property (F.cell _).property
      ⟨p, by rw [hR]; exact hpT, by rw [hR]; exact hp⟩
    rw [hR, hR, Set.image_subset_image_iff (S.σ ^ r).injective] at hsub
    have hle := hereditary_trace_step3_dim_mono _ _ hsub
    have h1 : (F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val.dim = 1 :=
      F.dimension _
    have h2 : (F.cell ⟨traceDimension d, traceDimension_pos,
        traceDimension_lt⟩).val.dim = traceDimension d := F.dimension _
    have h3 : traceDimension d = 2 := by
      unfold traceDimension
      have := (Fact.out : 2 ≤ d)
      omega
    omega
  have hccl : IsClosed c.carrier := by
    unfold TracePiece.carrier
    rw [recursiveTrace_tiles_step0_cell_zero]
    exact (c.bottom.val.flat.compact.image c.tile.frame.continuous).isClosed
  obtain ⟨O, hO, hOeq⟩ : ∃ O : Set (E d), IsOpen O ∧
      relint c.carrier = O ∩ (affineSpan ℝ c.carrier : Set (E d)) := by
    have hopen := (isOpen_interior :
      IsOpen (interior ((↑) ⁻¹' c.carrier : Set (affineSpan ℝ c.carrier))))
    obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.1 hopen
    refine ⟨O, hO, ?_⟩
    ext x
    constructor
    · intro hx
      rw [relint, mem_intrinsicInterior] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [← hpre] at hy
      exact ⟨hy, y.property⟩
    · rintro ⟨hxO, hxA⟩
      rw [relint, mem_intrinsicInterior]
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      rw [← hpre]
      exact hxO
  have hspan : affineSpan ℝ c.carrier = affineSpan ℝ T :=
    recursiveTrace_tiles_step1_span c TracePiece.bottomIndex
  have hDA : ∀ x ∈ relint T ∩ ball q (min ρ0 ρ),
      x ∈ (affineSpan ℝ c.carrier : Set (E d)) := by
    intro x hx
    rw [hspan]
    exact mem_affineSpan ℝ (intrinsicInterior_subset hx.1)
  have hcover : relint T ∩ ball q (min ρ0 ρ) ⊆ O ∪ c.carrierᶜ := by
    intro x hx
    by_cases hxc : x ∈ c.carrier
    · left
      by_cases hxr : x ∈ relint c.carrier
      · rw [hOeq] at hxr
        exact hxr.1
      · exfalso
        have hxf : x ∈ relfrontier c.carrier := by
          unfold relfrontier
          rw [← closure_diff_intrinsicInterior, hccl.closure_eq]
          exact ⟨hxc, hxr⟩
        exact hEdisj x (hfl ⟨hxf, ball_subset_ball (min_le_right _ _) hx.2⟩) hx.1
    · exact Or.inr hxc
  have hempty : ¬ (relint T ∩ ball q (min ρ0 ρ) ∩ (O ∩ c.carrierᶜ)).Nonempty := by
    rintro ⟨x, hxD, hxO, hxc⟩
    have hxr : x ∈ relint c.carrier := by rw [hOeq]; exact ⟨hxO, hDA x hxD⟩
    exact hxc (intrinsicInterior_subset hxr)
  rcases (isPreconnected_iff_subset_of_disjoint.1 hDc.isPreconnected) O c.carrierᶜ hO
      hccl.isOpen_compl hcover (Set.not_nonempty_iff_eq_empty.1 hempty) with hsub | hsub
  · intro x hx
    rw [hOeq]
    exact ⟨hsub hx, hDA x hx⟩
  · obtain ⟨⟨y, hyc, hyb⟩, hcF⟩ := sites_exist_step2_owner_changes_step3_edge_cover_step26_overlap_plane A F r q c
      hqc (min ρ0 ρ) (lt_min hρ0 hρ)
    exact (hsub ⟨hcF hyc, hyb⟩ (intrinsicInterior_subset hyc)).elim

/-- Step 1 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (V4 1.22(a),
restriction to `F₁ = h`): "the cells of the tiling that are contained in `F_{j-1}` cover it,
iterating down": every point of the flag edge lies on a listed edge of a trace owner, inside
the trace polygon (or trace edge) and inside the flag edge (the chain down to index `1`,
restricted to the trace indices, is a trace piece). -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step1_cover (A : S.ι)
    (F : FacetFlag S A) (r : ℕ) (x : E d) (hx : x ∈ flagEdge A F r) :
    ∃ (a : TracePiece A F r) (e : CellName S a.tile.ty), e.val.dim = 1 ∧
      x ∈ a.tile.cell 0 e.val ∧ a.tile.cell 0 e.val ⊆ a.carrier ∧
      a.tile.cell 0 e.val ⊆ flagEdge A F r := by
  have hd : 2 ≤ d := Fact.out
  obtain ⟨w, c, hxc⟩ := recursiveTrace_tiles_step11_cover A F r (d - 2) 1 le_rfl (by omega)
    (by omega) x hx
  let c' : ChainOccurrence A F r (S.nativeTile A r w) 0 (traceDimension d) :=
    { cell := fun i => c.cell ⟨i.val, i.property.2, i.property.2⟩
      dimension := fun i => c.dimension _
      nested := fun i k hik => c.nested _ _ hik
      contained := fun i => c.contained _ }
  have hle : 1 ≤ traceDimension d := traceDimension_pos
  refine ⟨⟨w, c'⟩, c.cell ⟨⟨1, by omega⟩, le_rfl, le_rfl⟩, c.dimension _, hxc, ?_,
    c.contained _⟩
  show (S.nativeTile A r w).cell 0 (c.cell ⟨⟨1, by omega⟩, le_rfl, le_rfl⟩).val ⊆
    (S.nativeTile A r w).cell 0
      (c.cell ⟨TracePiece.bottomIndex.val, hle, hle⟩).val
  exact Set.image_mono (c.nested _ _ hle)

/-- Step 3 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (V4 1.23(a),
"consecutive edges meet at a point ... which is a vertex"): an endpoint of a nondegenerate
segment is not in its relative interior. -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step3_endpoint (u v : E d)
    (huv : u ≠ v) : u ∉ relint (segment ℝ u v) := by
  intro hu
  have hsp : affineSpan ℝ (segment ℝ u v) = line[ℝ, u, v] := by
    rw [← convexHull_pair, affineSpan_convexHull]
  unfold relint at hu
  rw [mem_intrinsicInterior] at hu
  obtain ⟨y, hy, hyu⟩ := hu
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy
  obtain ⟨δ, hδ, hball⟩ := hy
  have hd : 0 < dist u v := dist_pos.mpr huv
  set t : ℝ := δ / 2 / dist u v with ht
  have htpos : 0 < t := by positivity
  have htd : t * dist u v = δ / 2 := div_mul_cancel₀ (δ / 2) hd.ne'
  have hw : AffineMap.lineMap u v (-t) ∈ affineSpan ℝ (segment ℝ u v) := by
    rw [hsp]
    exact AffineMap.lineMap_mem_affineSpan_pair _ u v
  have hmem := hball (show (⟨_, hw⟩ : affineSpan ℝ (segment ℝ u v)) ∈ Metric.ball y δ by
    rw [Metric.mem_ball, Subtype.dist_eq, hyu, dist_lineMap_left, norm_neg,
      Real.norm_eq_abs, abs_of_pos htpos, htd]
    linarith)
  change AffineMap.lineMap u v (-t) ∈ segment ℝ u v at hmem
  rw [segment_eq_image_lineMap] at hmem
  obtain ⟨s, ⟨hs0, -⟩, hs⟩ := hmem
  have := (AffineMap.lineMap_injective ℝ huv) hs
  linarith

open private hereditary_trace_step2_boundary from Enforce.Source.Trace in
/-- Step 4 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (V4 1.23(a),
(H2)(ii)): "consecutive edges meet at a point ... which is a vertex of both polygons": a
listed edge of a placed tile is a nondegenerate segment whose two endpoints are listed
vertices (they lie in the relative boundary, a union of lower-dimensional listed cells). -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step4_listed_segment
    (N : FramedNode S) (e : CellName S N.ty) (he : e.val.dim = 1) :
    ∃ u v : E d, u ≠ v ∧ N.cell 0 e.val = segment ℝ u v ∧ N.Lists 0 u ∧ N.Lists 0 v := by
  obtain ⟨a, b, hab, hK⟩ := sites_exist_step2_owner_changes_step2_cell_segment e.val he
  have hseg : N.cell 0 e.val = segment ℝ (N.frame a) (N.frame b) := by
    rw [recursiveTrace_tiles_step0_cell_zero, hK]
    exact image_segment ℝ N.frame.toAffineEquiv.toAffineMap a b
  have hne : N.frame a ≠ N.frame b := N.frame.injective.ne hab
  have hlist : ∀ u v : E d, u ≠ v → N.cell 0 e.val = segment ℝ u v → N.Lists 0 u := by
    intro u v huv huv'
    have hu : u ∈ N.cell 0 e.val := by rw [huv']; exact left_mem_segment ℝ u v
    have hnot : u ∉ relint (N.cell 0 e.val) := by
      rw [huv']
      exact sites_exist_step2_owner_changes_step3_edge_cover_step3_endpoint u v huv
    obtain ⟨F', hF', hlt, -, huF'⟩ :=
      hereditary_trace_step2_boundary N 0 e.val e.property u hu hnot
    refine ⟨F', ?_, huF'⟩
    simp only [CellComplex.vertices, Finset.mem_filter]
    exact ⟨hF', by omega⟩
  exact ⟨_, _, hne, hseg, hlist _ _ hne hseg,
    hlist _ _ hne.symm (hseg.trans (segment_symm ℝ _ _))⟩

open private hereditary_trace_step2_relint_mono from Enforce.Source.Trace in
/-- Step 5 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (V4 1.23(a),
"edges along `h`"): a nonempty subset of the same affine dimension has its relative interior
inside the larger relative interior (the affine spans agree). -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step5_relint_mono
    (K L : Set (E d)) (hKL : K ⊆ L) (hK : K.Nonempty)
    (hdim : Module.finrank ℝ (cellDirection K) = Module.finrank ℝ (cellDirection L)) :
    relint K ⊆ relint L := by
  have hle : affineSpan ℝ K ≤ affineSpan ℝ L := affineSpan_mono ℝ hKL
  have hdir : cellDirection K = cellDirection L :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) hdim
  have hne : (affineSpan ℝ K : Set (E d)).Nonempty := hK.mono (subset_affineSpan ℝ K)
  exact hereditary_trace_step2_relint_mono K L hKL
    (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir hne hle)

open private hereditary_trace_step1_relint_unique hereditary_trace_step2_boundary
  from Enforce.Source.Trace in
/-- Step 6 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (V4 1.23(a)
with Lemma 1.22(a)): "list these edges in the orientation of `h`" — distinct boundary edges
have disjoint relative interiors: two edges of one owner by (H2)(i); edges of distinct trace
pieces because, near a common relative-interior point, both pieces would fill the half-disc
of `F₂` (or, for `d = 2`, the edges are the trace edges themselves), contradicting the
disjointness of the trace (Lemma 1.22(a)). -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step6_disjoint (A : S.ι)
    (F : FacetFlag S A) (r : ℕ)
    (i j : Σ a : TracePiece A F r, {e : CellName S a.tile.ty // e.val.dim = 1 ∧
      a.tile.cell 0 e.val ⊆ a.carrier ∧ a.tile.cell 0 e.val ⊆ flagEdge A F r})
    (hij : i ≠ j) :
    Disjoint (relint (i.1.tile.cell 0 i.2.val.val)) (relint (j.1.tile.cell 0 j.2.val.val)) := by
  obtain ⟨a, e, he1, hea, heF⟩ := i
  obtain ⟨b, f, hf1, hfb, hfF⟩ := j
  rw [Set.disjoint_left]
  intro x hxe hxf
  dsimp only at hxe hxf
  have hcellfin : ∀ (C : FramedNode S) (m : Cell d),
      Module.finrank ℝ (cellDirection (C.cell 0 m)) = m.dim := by
    intro C m
    rw [recursiveTrace_tiles_step0_cell_zero]
    exact (recursiveTrace_tiles_step0_finrank_image C.frame.toAffineEquiv _).trans
      m.flat.dimension
  have hflagfin : Module.finrank ℝ (cellDirection (flagEdge A F r)) = 1 :=
    (recursiveTrace_tiles_step0_finrank_image (S.σ ^ r).toAffineEquiv _).trans
      ((F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val.flat.dimension.trans
        (F.dimension _))
  by_cases hab : a = b
  · subst hab
    have hef : e.val = f.val :=
      hereditary_trace_step1_relint_unique a.tile 0 e.val f.val e.property f.property x hxe hxf
    have hef' : e = f := Subtype.ext hef
    subst hef'
    exact hij rfl
  · have hxE : x ∈ relint (flagEdge A F r) :=
      sites_exist_step2_owner_changes_step3_edge_cover_step5_relint_mono _ _ heF
        ⟨x, intrinsicInterior_subset hxe⟩ (by rw [hcellfin, hflagfin, he1]) hxe
    by_cases hd : d = 2
    · have hcar : ∀ c : TracePiece A F r,
          Module.finrank ℝ (cellDirection c.carrier) = 1 := by
        intro c
        unfold TracePiece.carrier
        have hbd : c.bottom.val.dim = traceDimension d := c.chain.dimension TracePiece.bottomIndex
        rw [hcellfin, hbd]
        unfold traceDimension
        omega
      have hxa : x ∈ relint a.carrier :=
        sites_exist_step2_owner_changes_step3_edge_cover_step5_relint_mono _ _ hea
          ⟨x, intrinsicInterior_subset hxe⟩ (by rw [hcellfin, hcar, he1]) hxe
      have hxb : x ∈ relint b.carrier :=
        sites_exist_step2_owner_changes_step3_edge_cover_step5_relint_mono _ _ hfb
          ⟨x, intrinsicInterior_subset hxf⟩ (by rw [hcellfin, hcar, hf1]) hxf
      exact Set.disjoint_left.1 ((recursiveTrace_tiles A F r).2.1 hab) hxa hxb
    · have hall : ∀ e' : CellName S a.tile.ty, e'.val.dim = 1 → x ∈ a.tile.cell 0 e'.val →
          a.tile.cell 0 e'.val ⊆ a.carrier → a.tile.cell 0 e'.val ⊆ flagEdge A F r := by
        intro e' he' hxe' _
        by_cases hx' : x ∈ relint (a.tile.cell 0 e'.val)
        · have h1 : e.val = e'.val := hereditary_trace_step1_relint_unique a.tile 0 e.val
            e'.val e.property e'.property x hxe hx'
          have h2 : e = e' := Subtype.ext h1
          subst h2
          exact heF
        · exfalso
          obtain ⟨G, hG, hlt, -, hxG⟩ :=
            hereditary_trace_step2_boundary a.tile 0 e'.val e'.property x hxe' hx'
          have hG0 : G.dim = 0 := by omega
          have hsingle : a.tile.cell 0 G = {x} :=
            Set.eq_singleton_iff_unique_mem.2 ⟨hxG, fun y hy =>
              sites_exist_step2_owner_changes_step3_edge_cover_step212_point a.tile G hG0
                hy hxG⟩
          have hxrG : x ∈ relint (a.tile.cell 0 G) := by
            rw [hsingle]
            unfold relint
            rw [intrinsicInterior_singleton]
            rfl
          have h1 : e.val = G := hereditary_trace_step1_relint_unique a.tile 0 e.val G
            e.property hG x hxe hxrG
          rw [← h1] at hG0
          omega
      obtain ⟨ρ, hρ, hfl⟩ := sites_exist_step2_owner_changes_step3_edge_cover_step24_flat_plane
        A F r x a (intrinsicInterior_subset hxE) hall
      obtain ⟨ρ', hρ', hfill⟩ :=
        sites_exist_step2_owner_changes_step3_edge_cover_step25_fill_plane hd A F r x hxE a
          (hea (intrinsicInterior_subset hxe)) ρ hρ hfl
      obtain ⟨⟨y, hyb, hyball⟩, hbF⟩ :=
        sites_exist_step2_owner_changes_step3_edge_cover_step26_overlap_plane A F r x b
          (hfb (intrinsicInterior_subset hxf)) ρ' hρ'
      exact Set.disjoint_left.1 ((recursiveTrace_tiles A F r).2.1 hab)
        (hfill ⟨hbF hyb, hyball⟩) hyb

/-- Step 7 of the V4 proof of `sites_exist_step2_owner_changes_step3_edge_cover` (V4 1.23(a),
"consecutive edges meet at a point of `relint h`"; the same one-dimensional fact as Step 5 of
`sites_exist_step2_owner_changes`, stated later): the open segment of a nondegenerate
segment lies in its relative interior. -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover_step7_open_relint (x y : E d)
    (hxy : x ≠ y) : openSegment ℝ x y ⊆ relint (segment ℝ x y) := by
  intro z hz
  have hsp : affineSpan ℝ (segment ℝ x y) = line[ℝ, x, y] := by
    rw [← convexHull_pair, affineSpan_convexHull]
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨l, ⟨hl0, hl1⟩, rfl⟩ := hz
  have hzs : AffineMap.lineMap x y l ∈ affineSpan ℝ (segment ℝ x y) := by
    rw [hsp]
    exact AffineMap.lineMap_mem_affineSpan_pair l x y
  unfold relint
  rw [mem_intrinsicInterior]
  refine ⟨⟨_, hzs⟩, ?_, rfl⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  have hd : 0 < dist x y := dist_pos.mpr hxy
  refine ⟨min l (1 - l) * dist x y, mul_pos (lt_min hl0 (by linarith)) hd, ?_⟩
  rintro ⟨w, hw⟩ hwb
  have hw' := hw
  rw [hsp] at hw'
  have hdir := AffineSubspace.vsub_mem_direction hw' (left_mem_affineSpan_pair ℝ x y)
  rw [direction_affineSpan, mem_vectorSpan_pair_rev] at hdir
  obtain ⟨r, hr⟩ := hdir
  have hwr : w = AffineMap.lineMap x y r := by
    rw [AffineMap.lineMap_apply, hr, vsub_vadd]
  subst hwr
  rw [Metric.mem_ball, Subtype.dist_eq, dist_lineMap_lineMap] at hwb
  have hrl : dist r l < min l (1 - l) := lt_of_mul_lt_mul_right hwb hd.le
  rw [Real.dist_eq, abs_lt] at hrl
  have h1 := min_le_left l (1 - l)
  have h2 := min_le_right l (1 - l)
  change AffineMap.lineMap x y r ∈ segment ℝ x y
  rw [segment_eq_image_lineMap]
  exact ⟨r, ⟨by linarith, by linarith⟩, rfl⟩

/-- Step 3 of the V4 proof of `sites_exist_step2_owner_changes` (V4 1.23(a), with
Lemma 1.22(a)): "The recursive trace of Lemma 1.22 covers `h_r` by consecutive edges
with recorded owners" ("the polygons adjacent to `h` along `h` (those having an edge
contained in `h`) cover `h` by their edges along `h` ... consecutive edges meet at a
point of `relint h` which is a vertex of both polygons"). Concretely: finitely many
nondegenerate boundary edges `[u, v]` of trace pieces, with both endpoints listed by
the owner, cover the flag edge and have pairwise disjoint open segments. -/
private theorem sites_exist_step2_owner_changes_step3_edge_cover (A : S.ι)
    (F : FacetFlag S A) (r : ℕ) :
    ∃ s : Finset (TracePiece A F r × E d × E d),
      (∀ t ∈ s, t.2.1 ≠ t.2.2 ∧ BoundaryTraceEdge t.1 t.2.1 (segment ℝ t.2.1 t.2.2) ∧
        BoundaryTraceEdge t.1 t.2.2 (segment ℝ t.2.1 t.2.2)) ∧
      flagEdge A F r ⊆ ⋃ t ∈ s, segment ℝ t.2.1 t.2.2 ∧
      (∀ t ∈ s, ∀ t' ∈ s, t ≠ t' →
        Disjoint (openSegment ℝ t.2.1 t.2.2) (openSegment ℝ t'.2.1 t'.2.2)) := by
  classical
  haveI : Finite (TracePiece A F r) := tracePieces_finite A F r
  have hseg : ∀ i : (Σ a : TracePiece A F r, {e : CellName S a.tile.ty // e.val.dim = 1 ∧
      a.tile.cell 0 e.val ⊆ a.carrier ∧ a.tile.cell 0 e.val ⊆ flagEdge A F r}),
      ∃ uv : E d × E d, uv.1 ≠ uv.2 ∧ i.1.tile.cell 0 i.2.val.val = segment ℝ uv.1 uv.2 ∧
        i.1.tile.Lists 0 uv.1 ∧ i.1.tile.Lists 0 uv.2 := by
    intro i
    obtain ⟨u, v, h⟩ :=
      sites_exist_step2_owner_changes_step3_edge_cover_step4_listed_segment i.1.tile i.2.val
        i.2.property.1
    exact ⟨(u, v), h⟩
  choose g hg using hseg
  haveI : Fintype (Σ a : TracePiece A F r, {e : CellName S a.tile.ty // e.val.dim = 1 ∧
      a.tile.cell 0 e.val ⊆ a.carrier ∧ a.tile.cell 0 e.val ⊆ flagEdge A F r}) :=
    Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun i => (i.1, g i)), ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨hne, hcell, hu, hv⟩ := hg i
    dsimp only
    refine ⟨hne, ⟨i.2.val, i.2.property.1, hcell.symm, ?_, ?_, left_mem_segment ℝ _ _, hu⟩,
      ⟨i.2.val, i.2.property.1, hcell.symm, ?_, ?_, right_mem_segment ℝ _ _, hv⟩⟩
    · rw [← hcell]; exact i.2.property.2.1
    · rw [← hcell]; exact i.2.property.2.2
    · rw [← hcell]; exact i.2.property.2.1
    · rw [← hcell]; exact i.2.property.2.2
  · intro x hx
    obtain ⟨a, e, he1, hxe, hea, heF⟩ :=
      sites_exist_step2_owner_changes_step3_edge_cover_step1_cover A F r x hx
    refine Set.mem_iUnion₂.2 ⟨(a, g ⟨a, e, he1, hea, heF⟩),
      Finset.mem_image.2 ⟨⟨a, e, he1, hea, heF⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    have h := (hg ⟨a, e, he1, hea, heF⟩).2.1
    dsimp only at h ⊢
    rw [← h]
    exact hxe
  · intro t ht t' ht' hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht'
    have hij : i ≠ j := by
      rintro rfl
      exact hne rfl
    have hD := sites_exist_step2_owner_changes_step3_edge_cover_step6_disjoint A F r i j hij
    rw [(hg i).2.1, (hg j).2.1] at hD
    exact Disjoint.mono
      (sites_exist_step2_owner_changes_step3_edge_cover_step7_open_relint _ _ (hg i).1)
      (sites_exist_step2_owner_changes_step3_edge_cover_step7_open_relint _ _ (hg j).1) hD

/-- Step 4 of the V4 proof of `sites_exist_step2_owner_changes` (V4 1.23(a)): "the
recursive trace covers `h_r` by consecutive edges". In coordinates on `[0, 1]`: a finite
closed cover by intervals `[a t, b t]` has, at every `ξ < 1`, a piece starting at or
before `ξ` and ending after it. -/
private theorem sites_exist_step2_owner_changes_step4_right_piece {ι : Type*}
    (s : Finset ι) (a b : ι → ℝ)
    (hcov : ∀ τ ∈ Icc (0 : ℝ) 1, ∃ t ∈ s, τ ∈ Icc (a t) (b t))
    (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ < 1) :
    ∃ t ∈ s, a t ≤ ξ ∧ ξ < b t := by
  classical
  by_contra hcon
  push_neg at hcon
  let C : Set ℝ := ⋃ t ∈ s.filter (fun t => ξ < a t), Icc (a t) (b t)
  have hC : IsClosed C := isClosed_biUnion_finset (fun t _ => isClosed_Icc)
  have hξC : ξ ∉ C := by
    intro h
    obtain ⟨t, ht, hξt⟩ := Set.mem_iUnion₂.1 h
    exact absurd hξt.1 (not_le.2 (Finset.mem_filter.1 ht).2)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hC.isOpen_compl ξ hξC
  set τ := ξ + min (ε / 2) (1 - ξ) with hτ
  have hpos : 0 < min (ε / 2) (1 - ξ) := lt_min (by linarith) (by linarith)
  have hτ1 : τ ≤ 1 := by
    have := min_le_right (ε / 2) (1 - ξ)
    linarith
  obtain ⟨t, ht, hτt⟩ := hcov τ ⟨by linarith, hτ1⟩
  by_cases hat : ξ < a t
  · have hτC : τ ∈ C := Set.mem_iUnion₂.2 ⟨t, Finset.mem_filter.2 ⟨ht, hat⟩, hτt⟩
    have hτb : τ ∈ Metric.ball ξ ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      have := min_le_left (ε / 2) (1 - ξ)
      constructor <;> linarith
    exact hball hτb hτC
  · have := hcon t ht (not_lt.1 hat)
    have := hτt.2
    linarith

/-- Step 4 of the V4 proof of `sites_exist_step2_owner_changes` (V4 1.23(a)): "Every
maximal consecutive run with one owner has total length at most `D`". In coordinates:
starting at `ξ` with `ξ + D < 1`, the run of the owner of the piece leaving `ξ` ends at
a junction `p ∈ (ξ, ξ + D]` where a piece of that owner ends and a piece of another owner
starts. -/
private theorem sites_exist_step2_owner_changes_step4_first_junction {ι α : Type*}
    (s : Finset ι) (a b : ι → ℝ) (o : ι → α) (D : ℝ)
    (hab : ∀ t ∈ s, a t < b t)
    (hcov : ∀ τ ∈ Icc (0 : ℝ) 1, ∃ t ∈ s, τ ∈ Icc (a t) (b t))
    (hdisj : ∀ t ∈ s, ∀ t' ∈ s, t ≠ t' → Disjoint (Ioo (a t) (b t)) (Ioo (a t') (b t')))
    (hdiam : ∀ t ∈ s, ∀ t' ∈ s, o t = o t' →
      ∀ z ∈ Icc (a t) (b t), ∀ w ∈ Icc (a t') (b t'), |z - w| ≤ D)
    (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξD : ξ + D < 1) :
    ∃ p : ℝ, ξ < p ∧ p ≤ ξ + D ∧
      ∃ t ∈ s, ∃ t' ∈ s, o t ≠ o t' ∧ b t = p ∧ a t' = p := by
  classical
  have hD : 0 ≤ D := by
    obtain ⟨t, ht, hτ⟩ := hcov 0 ⟨le_rfl, zero_le_one⟩
    have := hdiam t ht t ht rfl 0 hτ 0 hτ
    simpa using this
  obtain ⟨t₀, ht₀, hat₀, hbt₀⟩ :=
    sites_exist_step2_owner_changes_step4_right_piece s a b hcov ξ hξ0 (by linarith)
  let sc := s.filter (fun t => o t = o t₀ ∧ ξ < b t)
  have ht₀c : t₀ ∈ sc := Finset.mem_filter.2 ⟨ht₀, rfl, hbt₀⟩
  obtain ⟨t₁, ht₁c, hmax⟩ := sc.exists_max_image b ⟨t₀, ht₀c⟩
  obtain ⟨ht₁, ho₁, hb₁⟩ := Finset.mem_filter.1 ht₁c
  have hpD : b t₁ ≤ ξ + D := by
    have := hdiam t₁ ht₁ t₀ ht₀ ho₁ (b t₁) ⟨(hab t₁ ht₁).le, le_rfl⟩ ξ ⟨hat₀, hbt₀.le⟩
    rw [abs_le] at this
    linarith [this.2]
  obtain ⟨t', ht', hat', hbt'⟩ :=
    sites_exist_step2_owner_changes_step4_right_piece s a b hcov (b t₁)
      (by linarith) (by linarith)
  have ho' : o t' ≠ o t₀ := by
    intro h
    have := hmax t' (Finset.mem_filter.2 ⟨ht', h, by linarith⟩)
    linarith
  have hne : t₁ ≠ t' := by
    rintro rfl
    exact ho' ho₁
  have ha' : a t' = b t₁ := by
    by_contra hlt
    have hlt' : a t' < b t₁ := lt_of_le_of_ne hat' hlt
    have h1 := hab t₁ ht₁
    set z := (max (a t₁) (a t') + b t₁) / 2 with hz
    have hm1 := le_max_left (a t₁) (a t')
    have hm2 := le_max_right (a t₁) (a t')
    have hm3 : max (a t₁) (a t') < b t₁ := max_lt h1 hlt'
    have hz1 : z ∈ Ioo (a t₁) (b t₁) := ⟨by linarith, by linarith⟩
    have hz2 : z ∈ Ioo (a t') (b t') := ⟨by linarith, by linarith⟩
    exact Set.disjoint_left.1 (hdisj t₁ ht₁ t' ht' hne) hz1 hz2
  refine ⟨b t₁, by linarith, hpD, t₁, ht₁, t', ht', ?_, rfl, ha'⟩
  rw [ho₁]
  exact fun h => ho' h.symm

/-- Step 4 of the V4 proof of `sites_exist_step2_owner_changes` (V4 1.23(a)): "Thus the
number of changes of owner is at least `|h_r|/D - 1`". In coordinates on `[0, 1]`: an
interval `[ξ, η]` of length `≥ (M+1) D` contains `M` distinct owner junctions in its
interior (iterate the first junction, each within `D` of the previous one). -/
private theorem sites_exist_step2_owner_changes_step4_real_count {ι α : Type*}
    (s : Finset ι) (a b : ι → ℝ) (o : ι → α) (D : ℝ) (hD : 0 < D)
    (hab : ∀ t ∈ s, a t < b t)
    (hcov : ∀ τ ∈ Icc (0 : ℝ) 1, ∃ t ∈ s, τ ∈ Icc (a t) (b t))
    (hdisj : ∀ t ∈ s, ∀ t' ∈ s, t ≠ t' → Disjoint (Ioo (a t) (b t)) (Ioo (a t') (b t')))
    (hdiam : ∀ t ∈ s, ∀ t' ∈ s, o t = o t' →
      ∀ z ∈ Icc (a t) (b t), ∀ w ∈ Icc (a t') (b t'), |z - w| ≤ D)
    (η : ℝ) (hη : η ≤ 1) :
    ∀ (M : ℕ) (ξ : ℝ), 0 ≤ ξ → ξ + ((M : ℝ) + 1) * D ≤ η →
      ∃ q : Finset ℝ, M ≤ q.card ∧ ∀ p ∈ q, ξ < p ∧ p < η ∧
        ∃ t ∈ s, ∃ t' ∈ s, o t ≠ o t' ∧ b t = p ∧ a t' = p := by
  classical
  intro M
  induction M with
  | zero => exact fun _ _ _ => ⟨∅, le_rfl, by simp⟩
  | succ M ih =>
    intro ξ hξ0 hξη
    push_cast at hξη
    have hMD : 0 ≤ (M : ℝ) * D := mul_nonneg (Nat.cast_nonneg M) hD.le
    obtain ⟨p, hξp, hpD, hj⟩ := sites_exist_step2_owner_changes_step4_first_junction
      s a b o D hab hcov hdisj hdiam ξ hξ0 (by nlinarith)
    obtain ⟨q, hq, hqp⟩ := ih p (by linarith) (by nlinarith)
    have hpq : p ∉ q := fun h => lt_irrefl p (hqp p h).1
    refine ⟨insert p q, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hpq]
      omega
    · intro p' hp'
      rcases Finset.mem_insert.1 hp' with rfl | hp'
      · exact ⟨hξp, by nlinarith, hj⟩
      · obtain ⟨h1, h2, h3⟩ := hqp p' hp'
        exact ⟨by linarith, h2, h3⟩

/-- Step 4 of the V4 proof of `sites_exist_step2_owner_changes` (V4 1.23(a)): "Every
maximal consecutive run with one owner has total length at most `D` ... Thus the
number of changes of owner is at least `|h_r|/D - 1`." Pure one-dimensional counting:
if finitely many nondegenerate labelled subsegments with disjoint open parts cover the
segment `[p₀, p₁]`, and same-label pieces stay within distance `D > 0`, then between
two points at distance `≥ (M+1) D` there are `M` distinct junctions, each a common
endpoint of two pieces with distinct labels lying on opposite sides. -/
private theorem sites_exist_step2_owner_changes_step4_count {ι α : Type*}
    (s : Finset ι) (u v : ι → E d) (o : ι → α) (D : ℝ) (hD : 0 < D)
    (p₀ p₁ x y : E d) (M : ℕ)
    (huv : ∀ t ∈ s, u t ≠ v t)
    (hsub : ∀ t ∈ s, segment ℝ (u t) (v t) ⊆ segment ℝ p₀ p₁)
    (hcov : segment ℝ p₀ p₁ ⊆ ⋃ t ∈ s, segment ℝ (u t) (v t))
    (hdisj : ∀ t ∈ s, ∀ t' ∈ s, t ≠ t' →
      Disjoint (openSegment ℝ (u t) (v t)) (openSegment ℝ (u t') (v t')))
    (hdiam : ∀ t ∈ s, ∀ t' ∈ s, o t = o t' →
      ∀ z ∈ segment ℝ (u t) (v t), ∀ w ∈ segment ℝ (u t') (v t'), dist z w ≤ D)
    (hx : x ∈ segment ℝ p₀ p₁) (hy : y ∈ segment ℝ p₀ p₁)
    (hxy : ((M : ℝ) + 1) * D ≤ dist x y) :
    ∃ q : Finset (E d), M ≤ q.card ∧ ∀ p ∈ q, p ∈ openSegment ℝ p₀ p₁ ∧
      ∃ t ∈ s, ∃ t' ∈ s, o t ≠ o t' ∧ (p = u t ∨ p = v t) ∧ (p = u t' ∨ p = v t') ∧
        ∃ z ∈ openSegment ℝ (u t) (v t), ∃ w ∈ openSegment ℝ (u t') (v t'),
          p ∈ openSegment ℝ z w := by
  classical
  have hMD : 0 < ((M : ℝ) + 1) * D := by positivity
  have hLxy : 0 < dist x y := lt_of_lt_of_le hMD hxy
  have hp01 : p₀ ≠ p₁ := by
    rintro rfl
    rw [segment_same, Set.mem_singleton_iff] at hx hy
    rw [hx, hy, dist_self] at hLxy
    exact lt_irrefl _ hLxy
  set w : E d := p₁ - p₀ with hw_def
  have hw : w ≠ 0 := sub_ne_zero.2 (Ne.symm hp01)
  have hwn : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hw)
  let g : ℝ →ᵃ[ℝ] E d := AffineMap.lineMap p₀ p₁
  let ℓ : E d → ℝ := fun z => inner ℝ (z - p₀) w / ‖w‖ ^ 2
  have hgapp : ∀ τ : ℝ, g τ = τ • w + p₀ := by
    intro τ
    change AffineMap.lineMap p₀ p₁ τ = τ • w + p₀
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hℓg : ∀ τ : ℝ, ℓ (g τ) = τ := by
    intro τ
    change inner ℝ (g τ - p₀) w / ‖w‖ ^ 2 = τ
    rw [hgapp, add_sub_cancel_right, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hginj : Function.Injective g := fun τ τ' h => by
    rw [← hℓg τ, ← hℓg τ', h]
  have hseg : segment ℝ p₀ p₁ = g '' Icc 0 1 := segment_eq_image_lineMap ℝ p₀ p₁
  have hgℓ : ∀ z ∈ segment ℝ p₀ p₁, g (ℓ z) = z ∧ ℓ z ∈ Icc (0 : ℝ) 1 := by
    intro z hz
    rw [hseg] at hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    rw [hℓg]
    exact ⟨rfl, hτ⟩
  have hdist : ∀ τ τ' : ℝ, dist (g τ) (g τ') = |τ - τ'| * dist p₀ p₁ := by
    intro τ τ'
    change dist (AffineMap.lineMap p₀ p₁ τ) (AffineMap.lineMap p₀ p₁ τ') = _
    rw [dist_lineMap_lineMap, Real.dist_eq]
  have hL : 0 < dist p₀ p₁ := dist_pos.2 hp01
  let α : ι → ℝ := fun t => ℓ (u t)
  let β : ι → ℝ := fun t => ℓ (v t)
  have hu : ∀ t ∈ s, g (α t) = u t ∧ α t ∈ Icc (0 : ℝ) 1 := fun t ht =>
    hgℓ _ (hsub t ht (left_mem_segment ℝ _ _))
  have hv : ∀ t ∈ s, g (β t) = v t ∧ β t ∈ Icc (0 : ℝ) 1 := fun t ht =>
    hgℓ _ (hsub t ht (right_mem_segment ℝ _ _))
  have hαβ : ∀ t ∈ s, α t ≠ β t := by
    intro t ht h
    apply huv t ht
    rw [← (hu t ht).1, ← (hv t ht).1, h]
  have hseg_t : ∀ t ∈ s,
      segment ℝ (u t) (v t) = g '' Icc (min (α t) (β t)) (max (α t) (β t)) := by
    intro t ht
    have e1 := (hu t ht).1
    have e2 := (hv t ht).1
    rw [← e1, ← e2, ← image_segment, segment_eq_uIcc]
    rfl
  have hopen_t : ∀ t ∈ s,
      openSegment ℝ (u t) (v t) = g '' Ioo (min (α t) (β t)) (max (α t) (β t)) := by
    intro t ht
    have e1 := (hu t ht).1
    have e2 := (hv t ht).1
    rw [← e1, ← e2, ← image_openSegment, openSegment_eq_Ioo' (hαβ t ht)]
  have hopen01 : openSegment ℝ p₀ p₁ = g '' Ioo 0 1 := by
    rw [← openSegment_eq_Ioo (zero_lt_one' ℝ), image_openSegment]
    simp [g]
  obtain ⟨hxg, hxI⟩ := hgℓ x hx
  obtain ⟨hyg, hyI⟩ := hgℓ y hy
  have hD' : 0 < D / dist p₀ p₁ := div_pos hD hL
  have hlen : min (ℓ x) (ℓ y) + ((M : ℝ) + 1) * (D / dist p₀ p₁) ≤ max (ℓ x) (ℓ y) := by
    have h1 : dist x y = |ℓ x - ℓ y| * dist p₀ p₁ := by
      rw [← hdist, hxg, hyg]
    have h2 : ((M : ℝ) + 1) * (D / dist p₀ p₁) ≤ |ℓ x - ℓ y| := by
      rw [← mul_div_assoc, div_le_iff₀ hL, ← h1]
      exact hxy
    have h3 : max (ℓ x) (ℓ y) - min (ℓ x) (ℓ y) = |ℓ x - ℓ y| := by
      rw [max_sub_min_eq_abs, abs_sub_comm]
    linarith
  obtain ⟨q', hq'card, hq'⟩ := sites_exist_step2_owner_changes_step4_real_count s
    (fun t => min (α t) (β t)) (fun t => max (α t) (β t)) o (D / dist p₀ p₁) hD'
    (fun t ht => min_lt_max.2 (hαβ t ht))
    (by
      intro τ hτ
      have hgτ : g τ ∈ segment ℝ p₀ p₁ := by
        rw [hseg]
        exact Set.mem_image_of_mem g hτ
      obtain ⟨t, ht, hτt⟩ := Set.mem_iUnion₂.1 (hcov hgτ)
      rw [hseg_t t ht] at hτt
      obtain ⟨τ', hτ', he⟩ := hτt
      exact ⟨t, ht, hginj he ▸ hτ'⟩)
    (by
      intro t ht t' ht' hne
      rw [Set.disjoint_left]
      intro τ h1 h2
      have k1 : g τ ∈ openSegment ℝ (u t) (v t) := by
        rw [hopen_t t ht]
        exact Set.mem_image_of_mem g h1
      have k2 : g τ ∈ openSegment ℝ (u t') (v t') := by
        rw [hopen_t t' ht']
        exact Set.mem_image_of_mem g h2
      exact Set.disjoint_left.1 (hdisj t ht t' ht' hne) k1 k2)
    (by
      intro t ht t' ht' ho z hz w' hw'
      have k1 : g z ∈ segment ℝ (u t) (v t) := by
        rw [hseg_t t ht]
        exact Set.mem_image_of_mem g hz
      have k2 : g w' ∈ segment ℝ (u t') (v t') := by
        rw [hseg_t t' ht']
        exact Set.mem_image_of_mem g hw'
      have := hdiam t ht t' ht' ho _ k1 _ k2
      rw [hdist] at this
      rw [le_div_iff₀ hL]
      exact this)
    (max (ℓ x) (ℓ y)) (max_le hxI.2 hyI.2) M (min (ℓ x) (ℓ y)) (le_min hxI.1 hyI.1) hlen
  refine ⟨q'.image g, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hginj]
    exact hq'card
  · intro p hp
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨hξp, hpη, t, ht, t', ht', hne, hb, ha⟩ := hq' p' hp'
    have hp'0 : 0 < p' := lt_of_le_of_lt (le_min hxI.1 hyI.1) hξp
    have hp'1 : p' < 1 := lt_of_lt_of_le hpη (max_le hxI.2 hyI.2)
    have hlt : min (α t) (β t) < max (α t) (β t) := min_lt_max.2 (hαβ t ht)
    have hlt' : min (α t') (β t') < max (α t') (β t') := min_lt_max.2 (hαβ t' ht')
    have hb : max (α t) (β t) = p' := hb
    have ha : min (α t') (β t') = p' := ha
    refine ⟨?_, t, ht, t', ht', hne, ?_, ?_, g ((min (α t) (β t) + p') / 2), ?_,
      g ((p' + max (α t') (β t')) / 2), ?_, ?_⟩
    · rw [hopen01]
      exact Set.mem_image_of_mem g ⟨hp'0, hp'1⟩
    · rcases max_choice (α t) (β t) with h | h
      · left
        rw [← hb, h, (hu t ht).1]
      · right
        rw [← hb, h, (hv t ht).1]
    · rcases min_choice (α t') (β t') with h | h
      · left
        rw [← ha, h, (hu t' ht').1]
      · right
        rw [← ha, h, (hv t' ht').1]
    · rw [hopen_t t ht]
      exact Set.mem_image_of_mem g ⟨by linarith, by linarith⟩
    · rw [hopen_t t' ht']
      exact Set.mem_image_of_mem g ⟨by linarith, by linarith⟩
    · rw [← image_openSegment, openSegment_eq_Ioo (by linarith)]
      exact Set.mem_image_of_mem g ⟨by linarith, by linarith⟩

/-- Step 5 of the V4 proof of `sites_exist_step2_owner_changes` (V4 1.23(a)):
"consecutive edges meet at a point of `relint h`". Every point of the open segment of a
nondegenerate segment lies in its relative interior (one-dimensional fact). -/
private theorem sites_exist_step2_owner_changes_step5_open_relint (x y : E d)
    (hxy : x ≠ y) : openSegment ℝ x y ⊆ relint (segment ℝ x y) := by
  intro z hz
  have hsp : affineSpan ℝ (segment ℝ x y) = line[ℝ, x, y] := by
    rw [← convexHull_pair, affineSpan_convexHull]
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨l, ⟨hl0, hl1⟩, rfl⟩ := hz
  have hzs : AffineMap.lineMap x y l ∈ affineSpan ℝ (segment ℝ x y) := by
    rw [hsp]
    exact AffineMap.lineMap_mem_affineSpan_pair l x y
  unfold relint
  rw [mem_intrinsicInterior]
  refine ⟨⟨_, hzs⟩, ?_, rfl⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  have hd : 0 < dist x y := dist_pos.mpr hxy
  refine ⟨min l (1 - l) * dist x y, mul_pos (lt_min hl0 (by linarith)) hd, ?_⟩
  rintro ⟨w, hw⟩ hwb
  have hw' := hw
  rw [hsp] at hw'
  have hdir := AffineSubspace.vsub_mem_direction hw' (left_mem_affineSpan_pair ℝ x y)
  rw [direction_affineSpan, mem_vectorSpan_pair_rev] at hdir
  obtain ⟨r, hr⟩ := hdir
  have hwr : w = AffineMap.lineMap x y r := by
    rw [AffineMap.lineMap_apply, hr, vsub_vadd]
  subst hwr
  rw [Metric.mem_ball, Subtype.dist_eq, dist_lineMap_lineMap] at hwb
  have hrl : dist r l < min l (1 - l) := lt_of_mul_lt_mul_right hwb hd.le
  rw [Real.dist_eq, abs_lt] at hrl
  have h1 := min_le_left l (1 - l)
  have h2 := min_le_right l (1 - l)
  change AffineMap.lineMap x y r ∈ segment ℝ x y
  rw [segment_eq_image_lineMap]
  exact ⟨r, ⟨by linarith, by linarith⟩, rfl⟩

/-- Step 2 of the V4 proof of `sites_exist` (V4 1.23(a), counting paragraph):
"Let `D` bound native tile diameters. The recursive trace of Lemma 1.22 covers `h_r`
by consecutive edges with recorded owners. Every maximal consecutive run with one
owner has total length at most `D`, since that run lies in one native tile. Thus the
number of changes of owner is at least `|h_r|/D - 1`." Concretely: there is a uniform
`D` such that two points of the depth-`r` flag edge at distance `≥ (M+1) D` have at
least `M` distinct owner changes (consecutive edges, `q ∈ relint h`, distinct owners)
of the trace along the edge. -/
private theorem sites_exist_step2_owner_changes (A : S.ι) (F : FacetFlag S A) :
    ∃ D : ℝ, ∀ (r M : ℕ) (x y : E d), x ∈ flagEdge A F r → y ∈ flagEdge A F r →
      ((M : ℝ) + 1) * D ≤ dist x y →
      ∃ q : Finset (E d), M ≤ q.card ∧ ∀ p ∈ q, sitesExistOwnerChange A F r p := by
  obtain ⟨C, hC⟩ := sites_exist_step2_owner_changes_step1_diameter A F
  refine ⟨max C 1, ?_⟩
  intro r M x y hx hy hxy
  obtain ⟨p₀, p₁, hp, hflag⟩ := sites_exist_step2_owner_changes_step2_flag_segment A F r
  obtain ⟨s, hs, hcov, hdisj⟩ := sites_exist_step2_owner_changes_step3_edge_cover A F r
  have hcarrier : ∀ t ∈ s, segment ℝ t.2.1 t.2.2 ⊆ t.1.carrier := by
    intro t ht
    obtain ⟨_, _, _, hK, _⟩ := (hs t ht).2.1
    exact hK
  have hedge : ∀ t ∈ s, segment ℝ t.2.1 t.2.2 ⊆ segment ℝ p₀ p₁ := by
    intro t ht
    obtain ⟨_, _, _, _, hK, _⟩ := (hs t ht).2.1
    rw [← hflag]
    exact hK
  rw [hflag] at hx hy hcov
  obtain ⟨q, hcard, hq⟩ := sites_exist_step2_owner_changes_step4_count s
    (fun t => t.2.1) (fun t => t.2.2) (fun t => t.1.owner) (max C 1)
    (lt_of_lt_of_le zero_lt_one (le_max_right C 1)) p₀ p₁ x y M
    (fun t ht => (hs t ht).1) hedge hcov hdisj
    (fun t ht t' ht' ho z hz w hw =>
      (hC r t.1 t'.1 ho z (hcarrier t ht hz) w (hcarrier t' ht' hw)).trans
        (le_max_left C 1))
    hx hy hxy
  refine ⟨q, hcard, fun p hp' => ?_⟩
  obtain ⟨hp01, t, ht, t', ht', hne, hpt, hpt', z, hz, w, hw, hpzw⟩ := hq p hp'
  refine ⟨?_, t.1, t'.1, segment ℝ t.2.1 t.2.2, segment ℝ t'.2.1 t'.2.2, hne, ?_, ?_,
    z, sites_exist_step2_owner_changes_step5_open_relint _ _ (hs t ht).1 hz,
    w, sites_exist_step2_owner_changes_step5_open_relint _ _ (hs t' ht').1 hw, hpzw⟩
  · rw [hflag]
    exact sites_exist_step2_owner_changes_step5_open_relint _ _ hp hp01
  · rcases hpt with h | h
    · rw [h]; exact (hs t ht).2.1
    · rw [h]; exact (hs t ht).2.2
  · rcases hpt' with h | h
    · rw [h]; exact (hs t' ht').2.1
    · rw [h]; exact (hs t' ht').2.2

open private hereditary_trace_step6_same hereditary_trace_step1_relint_unique
  hereditary_trace_step2_relint_mono hereditary_trace_step3_dim_mono
  from Enforce.Source.Trace in
/-- Step 1 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a), via (H2)):
"`F₂` ... near `q` is a half-plane, by Lemma 1.0(a) applied to its boundary edge" uses
that the only listed cell of dimension `≤ 1` of the root `H` through a relative-interior
point `q` of the flag edge `h` is `h` itself (relative interiors are disjoint). -/
private theorem sites_exist_step3_inward_arm_step1_edge_cell (A : S.ι) (F : FacetFlag S A)
    (r : ℕ) (q : E d) (hq : q ∈ relint (flagEdge A F r)) (G : CellName S A)
    (hG : G.val.dim ≤ 1) (hqG : q ∈ (S.σ ^ r) '' G.val.carrier) :
    G.val = (F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val := by
  set h := F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩ with hh
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hR : ∀ e : Cell d, R.cell r e = (S.σ ^ r) '' e.carrier :=
    recursiveTrace_tiles_step0_root_cell A r
  have hqh : q ∈ relint (R.cell r h.val) := by rw [hR]; exact hq
  have hsubI : R.cell r h.val ⊆ R.cell r G.val :=
    hereditary_trace_step6_same R r G.val h.val G.property h.property
      ⟨q, hqh, by rw [hR]; exact hqG⟩
  have hsub : h.val.carrier ⊆ G.val.carrier := by
    have h' := hsubI
    rw [hR, hR, Set.image_subset_image_iff (S.σ ^ r).injective] at h'
    exact h'
  have hdim : G.val.dim = 1 := le_antisymm hG
    ((F.dimension _).symm.le.trans (hereditary_trace_step3_dim_mono _ _ hsub))
  have hdir : cellDirection (R.cell r h.val) = cellDirection (R.cell r G.val) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · simpa only [cellDirection, direction_affineSpan] using vectorSpan_mono ℝ hsubI
    · have h1 : Module.finrank ℝ (cellDirection (R.cell r h.val)) = 1 := by
        rw [hR]
        exact (recursiveTrace_tiles_step0_finrank_image (S.σ ^ r).toAffineEquiv _).trans
          (h.val.flat.dimension.trans (F.dimension _))
      have h2 : Module.finrank ℝ (cellDirection (R.cell r G.val)) = 1 := by
        rw [hR]
        exact (recursiveTrace_tiles_step0_finrank_image (S.σ ^ r).toAffineEquiv _).trans
          (G.val.flat.dimension.trans hdim)
      rw [h1, h2]
  have hspan : affineSpan ℝ (R.cell r h.val) = affineSpan ℝ (R.cell r G.val) :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir
      ((affineSpan_nonempty ℝ).2 ⟨q, intrinsicInterior_subset hqh⟩) (affineSpan_mono ℝ hsubI)
  have hqG' : q ∈ relint (R.cell r G.val) :=
    hereditary_trace_step2_relint_mono _ _ hsubI hspan hqh
  exact (hereditary_trace_step1_relint_unique R r h.val G.val h.property G.property q
    hqh hqG').symm

open private hereditary_trace_step2_boundary from Enforce.Source.Trace in
/-- Step 2 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a), with Lemma 1.1):
"some separating edge enters the half-disc: this is the required inward arm". An edge of
a trace polygon through `q` that does not lie along the flag edge has its whole relative
interior in `relint F₂`: otherwise, by heredity (Lemma 1.1), it would lie in a cell of
`H` of dimension `≤ 1` through `q`, i.e. in `h` itself (Step 1). -/
private theorem sites_exist_step3_inward_arm_step2_heredity_plane (A : S.ι)
    (F : FacetFlag S A) (r : ℕ) (q : E d) (hq : q ∈ relint (flagEdge A F r))
    (c : TracePiece A F r) (e : CellName S c.tile.ty) (hqe : q ∈ c.tile.cell 0 e.val)
    (hsub : c.tile.cell 0 e.val ⊆ c.carrier)
    (hne : ¬ c.tile.cell 0 e.val ⊆ flagEdge A F r) :
    relint (c.tile.cell 0 e.val) ⊆ relint ((S.σ ^ r) '' (F.cell ⟨traceDimension d,
      traceDimension_pos, traceDimension_lt⟩).val.carrier) := by
  intro x hx
  by_contra hxF
  set T := F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩ with hT
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hR : ∀ e : Cell d, R.cell r e = (S.σ ^ r) '' e.carrier :=
    recursiveTrace_tiles_step0_root_cell A r
  have hxT : x ∈ R.cell r T.val := by
    rw [hR]
    exact c.chain.contained TracePiece.bottomIndex (hsub (intrinsicInterior_subset hx))
  obtain ⟨G, hG, hlt, -, hxG⟩ := hereditary_trace_step2_boundary R r T.val T.property x hxT
    (by rw [hR]; exact hxF)
  have hcG : c.tile.cell 0 e.val ⊆ R.cell r G :=
    hereditary_trace R c.tile r 0 (recursiveTrace_tiles_step0_native_desc A r c.owner)
      G e.val hG e.property ⟨x, hx, hxG⟩
  have hTd : T.val.dim = traceDimension d := F.dimension _
  have hG1 : G.dim ≤ 1 := by
    have : traceDimension d ≤ 2 := min_le_left _ _
    omega
  have hqG : q ∈ (S.σ ^ r) '' G.carrier := by rw [← hR]; exact hcG hqe
  have hGh := sites_exist_step3_inward_arm_step1_edge_cell A F r q hq ⟨G, hG⟩ hG1 hqG
  apply hne
  intro y hy
  have hy' := hcG hy
  rw [hR] at hy'
  unfold flagEdge
  change y ∈ (S.σ ^ r) '' (⟨G, hG⟩ : CellName S A).val.carrier at hy'
  rw [hGh] at hy'
  exact hy'

open private hereditary_trace_step1_frontier_relint hereditary_trace_step1_cell_subset
  hereditary_trace_step7_carrier from Enforce.Source.Trace in
/-- Step 3 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a), dimension two,
with Lemma 1.1): "In `d = 2` the same argument uses the native tiles in the half-disc
inside the node." An edge of a native tile through `q` not lying along the flag edge
has its relative interior in the interior of the node: a frontier point in its relative
interior would put it, by heredity, in a boundary cell of `H` through `q`, i.e. in `h`. -/
private theorem sites_exist_step3_inward_arm_step3_heredity_domain (hd : d = 2) (A : S.ι)
    (F : FacetFlag S A) (r : ℕ) (q : E d) (hq : q ∈ relint (flagEdge A F r))
    (w : S.RoleWord A r) (e : CellName S (S.nativeTile A r w).ty)
    (hqe : q ∈ (S.nativeTile A r w).cell 0 e.val)
    (hne : ¬ (S.nativeTile A r w).cell 0 e.val ⊆ flagEdge A F r) :
    relint ((S.nativeTile A r w).cell 0 e.val) ⊆ interior (S.supertile r A) := by
  intro x hx
  by_contra hxi
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hR : ∀ e : Cell d, R.cell r e = (S.σ ^ r) '' e.carrier :=
    recursiveTrace_tiles_step0_root_cell A r
  have hRc : R.carrier r = S.supertile r A := by
    simp [R, FramedNode.carrier, placedSet]
  have hC : (S.nativeTile A r w).IsDescendant 0 R (0 + r) := by
    rw [zero_add]; exact recursiveTrace_tiles_step0_native_desc A r w
  have hxS : x ∈ R.carrier r := by
    have := hereditary_trace_step7_carrier R (S.nativeTile A r w) 0 r hC
      (hereditary_trace_step1_cell_subset _ 0 e.val e.property (intrinsicInterior_subset hx))
    rwa [zero_add] at this
  have hfr : x ∈ frontier (R.carrier r) := by
    refine ⟨subset_closure hxS, ?_⟩
    rw [hRc]; exact hxi
  obtain ⟨G, hG, hxG⟩ := hereditary_trace_step1_frontier_relint R r x hfr
  have hcG : (S.nativeTile A r w).cell 0 e.val ⊆ R.cell r G :=
    hereditary_trace R (S.nativeTile A r w) r 0 (recursiveTrace_tiles_step0_native_desc A r w)
      G e.val hG e.property ⟨x, hx, intrinsicInterior_subset hxG⟩
  have hG1 : G.dim ≤ 1 := by
    have := (S.cx A).dim_lt G hG
    omega
  have hqG : q ∈ (S.σ ^ r) '' G.carrier := by rw [← hR]; exact hcG hqe
  have hGh := sites_exist_step3_inward_arm_step1_edge_cell A F r q hq ⟨G, hG⟩ hG1 hqG
  apply hne
  intro y hy
  have hy' := hcG hy
  rw [hR] at hy'
  unfold flagEdge
  change y ∈ (S.σ ^ r) '' (⟨G, hG⟩ : CellName S A).val.carrier at hy'
  rw [hGh] at hy'
  exact hy'

/-- Step 11 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a), (H2)): "the
finitely many polygons ... containing `q`": listed cells of a tile missing `q` are at
positive distance from `q`, so near `q` only listed cells through `q` are met. -/
private theorem sites_exist_step3_inward_arm_step11_local_cells (C : FramedNode S) (q : E d)
    (P : Set (E d)) (Φ : Cell d → Prop)
    (hall : ∀ e ∈ (S.cx C.ty).cells, Φ e → q ∈ C.cell 0 e → C.cell 0 e ⊆ P) :
    ∃ ρ > 0, ∀ x ∈ ball q ρ, ∀ e ∈ (S.cx C.ty).cells, Φ e → x ∈ C.cell 0 e → x ∈ P := by
  classical
  let U : Set (E d) := ⋃ e ∈ (S.cx C.ty).cells.filter (fun e => q ∉ C.cell 0 e), C.cell 0 e
  have hU : IsClosed U := by
    refine isClosed_biUnion_finset fun e _ => ?_
    rw [recursiveTrace_tiles_step0_cell_zero]
    exact (e.flat.compact.image C.frame.continuous).isClosed
  have hqU : q ∉ U := by
    intro h
    obtain ⟨e, he, hqe⟩ := Set.mem_iUnion₂.1 h
    exact (Finset.mem_filter.1 he).2 hqe
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU.isOpen_compl q hqU
  refine ⟨ρ, hρ, fun x hx e he hΦ hxe => ?_⟩
  by_cases hqe : q ∈ C.cell 0 e
  · exact hall e he hΦ hqe hxe
  · exact (hball hx (Set.mem_iUnion₂.2 ⟨e, Finset.mem_filter.2 ⟨he, hqe⟩, hxe⟩)).elim

/-- Step 12 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a), (H2)): a listed
vertex is a single point ("the listed vertices through `q` are `{q}`"). -/
private theorem sites_exist_step3_inward_arm_step12_point (C : FramedNode S) (e : Cell d)
    (he : e.dim = 0) {x y : E d} (hx : x ∈ C.cell 0 e) (hy : y ∈ C.cell 0 e) : x = y := by
  have h0 : Module.finrank ℝ (cellDirection (C.cell 0 e)) = 0 := by
    rw [recursiveTrace_tiles_step0_cell_zero]
    exact (recursiveTrace_tiles_step0_finrank_image C.frame.toAffineEquiv _).trans
      (e.flat.dimension.trans he)
  have hbot : cellDirection (C.cell 0 e) = ⊥ := Submodule.finrank_eq_zero.1 h0
  have hv : x -ᵥ y ∈ cellDirection (C.cell 0 e) := by
    unfold cellDirection
    rw [direction_affineSpan]
    exact vsub_mem_vectorSpan ℝ hx hy
  rw [hbot, Submodule.mem_bot] at hv
  exact vsub_eq_zero_iff_eq.1 hv

open private hereditary_trace_step2_boundary from Enforce.Source.Trace in
/-- Step 4 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a), fan paragraph):
"A trace polygon containing `q` in an edge interior would have that edge along the
boundary line". If every listed edge of a trace polygon (or trace edge) through `q`
lies along the flag edge, then near `q` its whole relative boundary lies along the flag
edge: the relative boundary is a finite union of listed cells (H2)(ii); those missing
`q` are at positive distance, the listed vertices through `q` are `{q}`, and a listed
cell inside the relative boundary of a polygon has dimension `≤ 1`. -/
private theorem sites_exist_step3_inward_arm_step4_flat_plane (A : S.ι) (F : FacetFlag S A)
    (r : ℕ) (q : E d) (c : TracePiece A F r) (hqF : q ∈ flagEdge A F r)
    (hall : ∀ e : CellName S c.tile.ty, e.val.dim = 1 → q ∈ c.tile.cell 0 e.val →
      c.tile.cell 0 e.val ⊆ c.carrier → c.tile.cell 0 e.val ⊆ flagEdge A F r) :
    ∃ ρ > 0, relfrontier c.carrier ∩ ball q ρ ⊆ flagEdge A F r := by
  obtain ⟨ρ, hρ, hloc⟩ := sites_exist_step3_inward_arm_step11_local_cells c.tile q
    (flagEdge A F r) (fun e => e.dim ≤ 1 ∧ c.tile.cell 0 e ⊆ c.carrier) (by
      rintro e he ⟨hdim, hsub⟩ hqe
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hdim with h0 | h1
      · intro y hy
        rw [sites_exist_step3_inward_arm_step12_point c.tile e h0 hy hqe]
        exact hqF
      · exact hall ⟨e, he⟩ h1 hqe hsub)
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  obtain ⟨hxf, hxb⟩ := hx
  have hcl : IsClosed c.carrier := by
    unfold TracePiece.carrier
    rw [recursiveTrace_tiles_step0_cell_zero]
    exact (c.bottom.val.flat.compact.image c.tile.frame.continuous).isClosed
  have hxc : x ∈ c.carrier ∧ x ∉ relint c.carrier := by
    unfold relfrontier at hxf
    rw [← closure_diff_intrinsicInterior, hcl.closure_eq] at hxf
    exact hxf
  obtain ⟨G, hG, hlt, hsubG, hxG⟩ := hereditary_trace_step2_boundary c.tile 0 c.bottom.val
    c.bottom.property x hxc.1 hxc.2
  have hbd : c.bottom.val.dim = traceDimension d := c.chain.dimension TracePiece.bottomIndex
  have h2 : traceDimension d ≤ 2 := min_le_left _ _
  exact hloc x hxb G hG ⟨by omega, hsubG⟩ hxG

open private hereditary_trace_step2_relint_mono from Enforce.Source.Trace in
/-- Step 6 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a), fan paragraph):
"... overlapping one of the two adjacent polygons". Every trace polygon through `q` has
relative-interior points arbitrarily close to `q` (its cell is the closure of its
relative interior, (H2)(iii)), and these lie in `relint F₂` (`G₂ ⊆ F₂`,
`aff G₂ = aff F₂`). -/
private theorem sites_exist_step3_inward_arm_step6_overlap_plane (A : S.ι)
    (F : FacetFlag S A) (r : ℕ) (q : E d) (b : TracePiece A F r) (hqb : q ∈ b.carrier)
    (ρ : ℝ) (hρ : 0 < ρ) :
    (relint b.carrier ∩ ball q ρ).Nonempty ∧
      relint b.carrier ⊆ relint ((S.σ ^ r) '' (F.cell ⟨traceDimension d,
        traceDimension_pos, traceDimension_lt⟩).val.carrier) := by
  refine ⟨?_, ?_⟩
  · have hcl : closure (relint b.carrier) = b.carrier := by
      unfold TracePiece.carrier
      rw [recursiveTrace_tiles_step0_relint_cell, recursiveTrace_tiles_step0_cell_zero]
      have h := b.tile.frame.toHomeomorph.image_closure (relint b.bottom.val.carrier)
      rw [AffineIsometryEquiv.coe_toHomeomorph] at h
      rw [← h, b.bottom.val.flat.regularClosed]
    have hq' : q ∈ closure (relint b.carrier) := by rw [hcl]; exact hqb
    obtain ⟨y, hy, hyq⟩ := Metric.mem_closure_iff.1 hq' ρ hρ
    exact ⟨y, hy, by rw [mem_ball, dist_comm]; exact hyq⟩
  · exact hereditary_trace_step2_relint_mono _ _ (b.chain.contained TracePiece.bottomIndex)
      (recursiveTrace_tiles_step1_span b TracePiece.bottomIndex)

/-- Step 14 of the V4 proof of `sites_exist_step3_inward_arm` (linear algebra behind
"near `q` the two-dimensional flag cell is a half-plane"): a line `L` inside a plane
`P` through `q` is the zero set in `P` of a linear functional, nonzero on `P`. -/
private theorem sites_exist_step3_inward_arm_step14_functional (L P : AffineSubspace ℝ (E d))
    (q : E d) (hqL : q ∈ L) (hLP : L ≤ P) (hdimL : Module.finrank ℝ L.direction = 1)
    (hdimP : Module.finrank ℝ P.direction = 2) :
    ∃ f : E d →ₗ[ℝ] ℝ, ∃ v ∈ P.direction, f v ≠ 0 ∧
      (∀ x ∈ P, f x = f q → x ∈ L) ∧ (∀ x ∈ L, f x = f q) := by
  have hqP : q ∈ P := hLP hqL
  have hdirle := AffineSubspace.direction_le hLP
  have hlt : L.direction < P.direction := by
    refine lt_of_le_of_ne hdirle fun h => ?_
    rw [h] at hdimL
    omega
  obtain ⟨v, hvP, hvL⟩ := SetLike.exists_of_lt hlt
  obtain ⟨f, hfv, hfL⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hvL inferInstance
  have hfL' : ∀ l ∈ L.direction, f l = 0 := fun l hl => by
    have hm : f l ∈ L.direction.map f := Submodule.mem_map_of_mem hl
    rw [hfL] at hm
    exact (Submodule.mem_bot ℝ).1 hm
  have hvle : ℝ ∙ v ≤ P.direction := (Submodule.span_singleton_le_iff_mem _ _).2 hvP
  have hsup : L.direction ⊔ ℝ ∙ v = P.direction := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le hdirle hvle)
    have hlt2 : L.direction < L.direction ⊔ ℝ ∙ v := by
      refine lt_of_le_of_ne le_sup_left fun h => hvL ?_
      rw [h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt2
    have h3 := Submodule.finrank_mono (sup_le hdirle hvle)
    try simp only at h3
    omega
  refine ⟨f, v, hvP, hfv, ?_, ?_⟩
  · intro x hx hfx
    have hxq : x -ᵥ q ∈ P.direction := AffineSubspace.vsub_mem_direction hx hqP
    rw [← hsup, Submodule.mem_sup] at hxq
    obtain ⟨y, hy, z, hz, hyz⟩ := hxq
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have hfxq : f (x -ᵥ q) = t * f v := by
      rw [← hyz, map_add, hfL' y hy, map_smul, smul_eq_mul, zero_add]
    have h0 : t * f v = 0 := by
      rw [← hfxq, vsub_eq_sub, map_sub, hfx, sub_self]
    have ht : t = 0 := (mul_eq_zero.1 h0).resolve_right hfv
    subst ht
    rw [zero_smul, add_zero] at hyz
    rw [hyz] at hy
    exact (AffineSubspace.vsub_right_mem_direction_iff_mem hqL x).1 hy
  · intro x hx
    have hxq : x -ᵥ q ∈ L.direction := AffineSubspace.vsub_mem_direction hx hqL
    have := hfL' _ hxq
    rw [vsub_eq_sub, map_sub, sub_eq_zero] at this
    exact this

/-- Step 15 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a), Lemma 1.0(a)
for the flag cell, topological part): if near `q` the relative boundary of a closed
plane cell `T` lies on the line `{f = f q}` of its plane, and that line misses
`relint T`, then near `q` the relative interior of `T` is one of the two open half-discs
(or empty), hence convex: each half-disc is connected and misses the relative boundary,
and both cannot lie in `T` since `q ∉ relint T`. -/
private theorem sites_exist_step3_inward_arm_step15_core (T E0 : Set (E d)) (q : E d)
    (f : E d →ₗ[ℝ] ℝ) (v : E d) (hvP : v ∈ (affineSpan ℝ T).direction) (hfv : f v ≠ 0)
    (hTcl : IsClosed T) (hqE : q ∈ E0) (hqP : q ∈ affineSpan ℝ T)
    (hEdisj : ∀ p ∈ E0, p ∉ relint T) (hLf : ∀ x ∈ E0, f x = f q)
    (O : Set (E d)) (hO : IsOpen O) (hOeq : relint T = O ∩ (affineSpan ℝ T : Set (E d)))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hloc : ∀ x ∈ ball q ρ, x ∈ T → x ∉ relint T → x ∈ E0)
    (hlineK : ∀ x ∈ ball q ρ, x ∈ affineSpan ℝ T → f x = f q → x ∈ E0) :
    ∃ ρ' > 0, Convex ℝ (relint T ∩ ball q ρ') := by
  have hsep : ∀ Hs : Set (E d), Convex ℝ Hs → Hs ⊆ affineSpan ℝ T → Hs ⊆ ball q ρ →
      (∀ x ∈ Hs, f x ≠ f q) → Hs ⊆ relint T ∨ Hs ⊆ Tᶜ := by
    intro Hs hHc hHP hHb hHf
    have hcover : Hs ⊆ O ∪ Tᶜ := by
      intro x hx
      by_cases hxT : x ∈ T
      · left
        by_cases hxr : x ∈ relint T
        · rw [hOeq] at hxr
          exact hxr.1
        · exact (hHf x hx (hLf x (hloc x (hHb hx)
            hxT hxr))).elim
      · exact Or.inr hxT
    have hempty : ¬ (Hs ∩ (O ∩ Tᶜ)).Nonempty := by
      rintro ⟨x, hx, hxO, hxT⟩
      have hxr : x ∈ relint T := by rw [hOeq]; exact ⟨hxO, hHP hx⟩
      exact hxT (intrinsicInterior_subset hxr)
    rcases (isPreconnected_iff_subset_of_disjoint.1 hHc.isPreconnected) O Tᶜ hO
        hTcl.isOpen_compl hcover (Set.not_nonempty_iff_eq_empty.1 hempty) with h | h
    · left
      intro x hx
      rw [hOeq]
      exact ⟨h hx, hHP hx⟩
    · exact Or.inr h
  let Hp : Set (E d) := {x | f q < f x} ∩ (affineSpan ℝ T : Set (E d)) ∩ ball q ρ
  let Hm : Set (E d) := {x | f x < f q} ∩ (affineSpan ℝ T : Set (E d)) ∩ ball q ρ
  have hHpc : Convex ℝ Hp :=
    ((convex_halfSpace_gt f.isLinear (f q)).inter (affineSpan ℝ T).convex).inter
      (convex_ball q ρ)
  have hHmc : Convex ℝ Hm :=
    ((convex_halfSpace_lt f.isLinear (f q)).inter (affineSpan ℝ T).convex).inter
      (convex_ball q ρ)
  have hsplit : relint T ∩ ball q ρ ⊆ Hp ∪ Hm := by
    rintro x ⟨hxr, hxb⟩
    have hxP : x ∈ affineSpan ℝ T := mem_affineSpan ℝ (intrinsicInterior_subset hxr)
    rcases lt_trichotomy (f x) (f q) with h | h | h
    · exact Or.inr ⟨⟨h, hxP⟩, hxb⟩
    · exact (hEdisj x (hlineK x hxb hxP h) hxr).elim
    · exact Or.inl ⟨⟨h, hxP⟩, hxb⟩
  rcases hsep Hp hHpc (fun x hx => hx.1.2) (fun x hx => hx.2) (fun x hx => hx.1.1.ne') with
    hp | hp <;>
  rcases hsep Hm hHmc (fun x hx => hx.1.2) (fun x hx => hx.2) (fun x hx => hx.1.1.ne) with
    hm | hm
  · -- both half-discs are inside: then `q ∈ relint F₂`, impossible
    exfalso
    have hPT : ∀ x ∈ affineSpan ℝ T, x ∈ ball q ρ → x ∈ T := by
      intro x hxP hxb
      rcases lt_trichotomy (f x) (f q) with h | h | h
      · exact intrinsicInterior_subset (hm ⟨⟨h, hxP⟩, hxb⟩)
      · rw [← hTcl.closure_eq, Metric.mem_closure_iff]
        intro ε hε
        have hδ : 0 < min ε (ρ - dist x q) := lt_min hε (sub_pos.2 (mem_ball.1 hxb))
        set s := min ε (ρ - dist x q) / (2 * (‖v‖ + 1)) with hs
        have hs0 : 0 < s := div_pos hδ (by positivity)
        have hsv : s * ‖v‖ < min ε (ρ - dist x q) := by
          rw [hs, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg v]
        have hy1 : dist x (x + s • v) = s * ‖v‖ := by
          rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hs0.le]
        have hyP : x + s • v ∈ affineSpan ℝ T := by
          have : s • v +ᵥ x ∈ affineSpan ℝ T :=
            AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ s hvP) hxP
          rwa [vadd_eq_add, add_comm] at this
        have hyb : x + s • v ∈ ball q ρ := by
          rw [mem_ball]
          calc dist (x + s • v) q ≤ dist (x + s • v) x + dist x q := dist_triangle _ _ _
            _ = s * ‖v‖ + dist x q := by rw [dist_comm, hy1]
            _ < ρ := by have := min_le_right ε (ρ - dist x q); linarith
        have hfy : f (x + s • v) ≠ f q := by
          rw [map_add, map_smul, smul_eq_mul, h]
          intro h'
          have : s * f v = 0 := by linarith
          exact hfv ((mul_eq_zero.1 this).resolve_left hs0.ne')
        refine ⟨x + s • v, ?_, ?_⟩
        · rcases lt_or_gt_of_ne hfy with h' | h'
          · exact intrinsicInterior_subset (hm ⟨⟨h', hyP⟩, hyb⟩)
          · exact intrinsicInterior_subset (hp ⟨⟨h', hyP⟩, hyb⟩)
        · rw [hy1]
          exact lt_of_lt_of_le hsv (min_le_left _ _)
      · exact intrinsicInterior_subset (hp ⟨⟨h, hxP⟩, hxb⟩)
    have hsubB : (Subtype.val ⁻¹' ball q ρ : Set (affineSpan ℝ T)) ⊆
        Subtype.val ⁻¹' T := by
      intro y hy
      rw [Set.mem_preimage] at hy ⊢
      exact hPT y.1 y.2 hy
    have hopenB : IsOpen (Subtype.val ⁻¹' ball q ρ : Set (affineSpan ℝ T)) :=
      isOpen_ball.preimage continuous_subtype_val
    have hqB : (⟨q, hqP⟩ : affineSpan ℝ T) ∈ (Subtype.val ⁻¹' ball q ρ : Set (affineSpan ℝ T)) := by
      rw [Set.mem_preimage]
      exact mem_ball_self hρ
    have hint : (⟨q, hqP⟩ : affineSpan ℝ T) ∈
        interior (Subtype.val ⁻¹' T : Set (affineSpan ℝ T)) :=
      interior_maximal hsubB hopenB hqB
    have hqr : q ∈ intrinsicInterior ℝ T := mem_intrinsicInterior.2 ⟨⟨q, hqP⟩, hint, rfl⟩
    exact hEdisj q hqE hqr
  · refine ⟨ρ, hρ, ?_⟩
    have : relint T ∩ ball q ρ = Hp := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hsplit hx with h | h
        · exact h
        · exact (hm h (intrinsicInterior_subset hx.1)).elim
      · intro x hx
        exact ⟨hp hx, hx.2⟩
    rw [this]
    exact hHpc
  · refine ⟨ρ, hρ, ?_⟩
    have : relint T ∩ ball q ρ = Hm := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hsplit hx with h | h
        · exact (hp h (intrinsicInterior_subset hx.1)).elim
        · exact h
      · intro x hx
        exact ⟨hm hx, hx.2⟩
    rw [this]
    exact hHmc
  · refine ⟨ρ, hρ, ?_⟩
    have : relint T ∩ ball q ρ = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x hx
      rcases hsplit hx with h | h
      · exact hp h (intrinsicInterior_subset hx.1)
      · exact hm h (intrinsicInterior_subset hx.1)
    rw [this]
    exact convex_empty

open private hereditary_trace_step6_same hereditary_trace_step3_dim_mono
  hereditary_trace_step2_boundary from Enforce.Source.Trace in
set_option maxHeartbeats 1600000 in
/-- Step 13 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a), Lemma 1.0(a)
for the flag cell): "For `d ≥ 3`, near `q` the two-dimensional flag cell is a
half-plane, by Lemma 1.0(a) applied to its boundary edge." Hence, near `q ∈ relint h`,
the relative interior of `F₂` is an open half-disc, in particular convex. -/
private theorem sites_exist_step3_inward_arm_step13_half_disc (hd : d ≠ 2) (A : S.ι)
    (F : FacetFlag S A) (r : ℕ) (q : E d) (hq : q ∈ relint (flagEdge A F r)) :
    ∃ ρ > 0, Convex ℝ (relint ((S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
      traceDimension_lt⟩).val.carrier) ∩ ball q ρ) := by
  classical
  have h2 : 2 ≤ d := Fact.out
  have htd : traceDimension d = 2 := by unfold traceDimension; omega
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hR : ∀ e : Cell d, R.cell r e = (S.σ ^ r) '' e.carrier :=
    recursiveTrace_tiles_step0_root_cell A r
  set T := (S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
    traceDimension_lt⟩).val.carrier with hT
  have hqE : q ∈ flagEdge A F r := intrinsicInterior_subset hq
  have hET : flagEdge A F r ⊆ T :=
    Set.image_mono (F.nested ⟨1, le_rfl, by omega⟩
      ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩ (by show 1 ≤ traceDimension d; omega))
  have hTcl : IsClosed T :=
    ((F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.flat.compact.image
      (S.σ ^ r).toContinuousLinearEquiv.continuous).isClosed
  -- the flag edge misses `relint F₂`
  have hEdisj : ∀ p ∈ flagEdge A F r, p ∉ relint T := by
    intro p hp hpT
    have hsub := hereditary_trace_step6_same R r
      (F.cell ⟨1, le_rfl, by omega⟩).val
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val
      (F.cell _).property (F.cell _).property
      ⟨p, by rw [hR]; exact hpT, by rw [hR]; exact hp⟩
    rw [hR, hR, Set.image_subset_image_iff (S.σ ^ r).injective] at hsub
    have hle := hereditary_trace_step3_dim_mono _ _ hsub
    have h1 : (F.cell ⟨1, le_rfl, by omega⟩).val.dim = 1 := F.dimension _
    have h2' : (F.cell ⟨traceDimension d, traceDimension_pos,
        traceDimension_lt⟩).val.dim = traceDimension d := F.dimension _
    omega
  -- near `q`, the relative boundary of `F₂` lies in the flag edge
  obtain ⟨ρ1, hρ1, hloc⟩ : ∃ ρ1 > 0, ∀ x ∈ ball q ρ1, x ∈ T → x ∉ relint T →
      x ∈ flagEdge A F r := by
    let U : Set (E d) := ⋃ G ∈ (S.cx A).cells.filter
      (fun G => q ∉ (S.σ ^ r) '' G.carrier), (S.σ ^ r) '' G.carrier
    have hU : IsClosed U := isClosed_biUnion_finset fun G _ =>
      (G.flat.compact.image (S.σ ^ r).toContinuousLinearEquiv.continuous).isClosed
    have hqU : q ∉ U := by
      intro h
      obtain ⟨G, hG, hqG⟩ := Set.mem_iUnion₂.1 h
      exact (Finset.mem_filter.1 hG).2 hqG
    obtain ⟨ρ1, hρ1, hball⟩ := Metric.isOpen_iff.1 hU.isOpen_compl q hqU
    refine ⟨ρ1, hρ1, fun x hx hxT hxr => ?_⟩
    obtain ⟨G, hG, hlt, -, hxG⟩ := hereditary_trace_step2_boundary R r
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val
      (F.cell _).property x (by rw [hR]; exact hxT) (by rw [hR]; exact hxr)
    rw [hR] at hxG
    by_cases hqG : q ∈ (S.σ ^ r) '' G.carrier
    · have hGd : G.dim ≤ 1 := by
        have : (F.cell ⟨traceDimension d, traceDimension_pos,
          traceDimension_lt⟩).val.dim = traceDimension d := F.dimension _
        omega
      have hGh := sites_exist_step3_inward_arm_step1_edge_cell A F r q hq ⟨G, hG⟩ hGd hqG
      change x ∈ (S.σ ^ r) '' (⟨G, hG⟩ : CellName S A).val.carrier at hxG
      rw [hGh] at hxG
      exact hxG
    · exact (hball hx (Set.mem_iUnion₂.2 ⟨G, Finset.mem_filter.2 ⟨hG, hqG⟩, hxG⟩)).elim
  -- near `q`, the line of the flag edge lies in the flag edge
  obtain ⟨ρ2, hρ2, hline⟩ : ∃ ρ2 > 0, ∀ x ∈ ball q ρ2,
      x ∈ (affineSpan ℝ (flagEdge A F r) : Set (E d)) → x ∈ flagEdge A F r := by
    have hopen := (isOpen_interior : IsOpen (interior
      ((↑) ⁻¹' flagEdge A F r : Set (affineSpan ℝ (flagEdge A F r)))))
    obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.1 hopen
    have hq' := hq
    rw [relint, mem_intrinsicInterior] at hq'
    obtain ⟨y, hy, hyq⟩ := hq'
    have hqO : q ∈ O := by
      rw [← hpre] at hy
      rw [← hyq]
      exact hy
    obtain ⟨ρ2, hρ2, hb⟩ := Metric.isOpen_iff.1 hO q hqO
    refine ⟨ρ2, hρ2, fun x hx hxA => ?_⟩
    have hxi : (⟨x, hxA⟩ : affineSpan ℝ (flagEdge A F r)) ∈
        interior ((↑) ⁻¹' flagEdge A F r : Set (affineSpan ℝ (flagEdge A F r))) := by
      rw [← hpre]
      exact hb hx
    have hxm := interior_subset hxi
    exact hxm
  -- `relint F₂` is open in the plane `aff F₂`
  obtain ⟨O, hO, hOeq⟩ : ∃ O : Set (E d), IsOpen O ∧
      relint T = O ∩ (affineSpan ℝ T : Set (E d)) := by
    have hopen := (isOpen_interior :
      IsOpen (interior ((↑) ⁻¹' T : Set (affineSpan ℝ T))))
    obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.1 hopen
    refine ⟨O, hO, ?_⟩
    ext x
    constructor
    · intro hx
      rw [relint, mem_intrinsicInterior] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [← hpre] at hy
      exact ⟨hy, y.property⟩
    · rintro ⟨hxO, hxA⟩
      rw [relint, mem_intrinsicInterior]
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      rw [← hpre]
      exact hxO
  obtain ⟨f, v, hvP, hfv, hK, hLf⟩ := sites_exist_step3_inward_arm_step14_functional
    (affineSpan ℝ (flagEdge A F r)) (affineSpan ℝ T) q (mem_affineSpan ℝ hqE)
    (affineSpan_mono ℝ hET)
    ((recursiveTrace_tiles_step0_finrank_image (S.σ ^ r).toAffineEquiv _).trans
      ((F.cell ⟨1, le_rfl, by omega⟩).val.flat.dimension.trans (F.dimension _)))
    ((recursiveTrace_tiles_step0_finrank_image (S.σ ^ r).toAffineEquiv _).trans
      ((F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.flat.dimension.trans
        ((F.dimension _).trans htd)))
  exact sites_exist_step3_inward_arm_step15_core T (flagEdge A F r) q f v hvP hfv hTcl hqE
    (mem_affineSpan ℝ (hET hqE)) hEdisj (fun x hx => hLf x (mem_affineSpan ℝ hx)) O hO hOeq (min ρ1 ρ2) (lt_min hρ1 hρ2)
    (fun x hx hxT hxr => hloc x (ball_subset_ball (min_le_left _ _) hx) hxT hxr)
    (fun x hx hxP hfx => hline x (ball_subset_ball (min_le_right _ _) hx) (hK x hxP hfx))

open private hereditary_trace_step6_same hereditary_trace_step3_dim_mono
  from Enforce.Source.Trace in
/-- Step 5 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a), fan paragraph,
`d ≥ 3`): "near `q` the two-dimensional flag cell is a half-plane, by Lemma 1.0(a)
applied to its boundary edge. A trace polygon ... would ... occupy a whole half-disc".
A trace polygon through `q` whose relative boundary near `q` lies along the flag edge
contains, near `q`, the whole open half-disc `relint F₂` (connectedness of the half-disc,
which misses the relative boundary of the polygon and meets its relative interior). -/
private theorem sites_exist_step3_inward_arm_step5_fill_plane (hd : d ≠ 2) (A : S.ι)
    (F : FacetFlag S A) (r : ℕ) (q : E d) (hq : q ∈ relint (flagEdge A F r))
    (c : TracePiece A F r) (hqc : q ∈ c.carrier) (ρ : ℝ) (hρ : 0 < ρ)
    (hfl : relfrontier c.carrier ∩ ball q ρ ⊆ flagEdge A F r) :
    ∃ ρ' > 0, relint ((S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
      traceDimension_lt⟩).val.carrier) ∩ ball q ρ' ⊆ relint c.carrier := by
  obtain ⟨ρ0, hρ0, hconv⟩ := sites_exist_step3_inward_arm_step13_half_disc hd A F r q hq
  set T := (S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
    traceDimension_lt⟩).val.carrier with hT
  refine ⟨min ρ0 ρ, lt_min hρ0 hρ, ?_⟩
  have hDc : Convex ℝ (relint T ∩ ball q (min ρ0 ρ)) := by
    have hD : relint T ∩ ball q (min ρ0 ρ) =
        (relint T ∩ ball q ρ0) ∩ ball q (min ρ0 ρ) := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, ball_subset_ball (min_le_left _ _) h2⟩, h2⟩
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
    rw [hD]
    exact hconv.inter (convex_ball _ _)
  have hEdisj : ∀ p ∈ flagEdge A F r, p ∉ relint T := by
    intro p hp hpT
    let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
    have hR : ∀ e : Cell d, R.cell r e = (S.σ ^ r) '' e.carrier :=
      recursiveTrace_tiles_step0_root_cell A r
    have hsub := hereditary_trace_step6_same R r
      (F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val
      (F.cell _).property (F.cell _).property
      ⟨p, by rw [hR]; exact hpT, by rw [hR]; exact hp⟩
    rw [hR, hR, Set.image_subset_image_iff (S.σ ^ r).injective] at hsub
    have hle := hereditary_trace_step3_dim_mono _ _ hsub
    have h1 : (F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val.dim = 1 :=
      F.dimension _
    have h2 : (F.cell ⟨traceDimension d, traceDimension_pos,
        traceDimension_lt⟩).val.dim = traceDimension d := F.dimension _
    have h3 : traceDimension d = 2 := by
      unfold traceDimension
      have := (Fact.out : 2 ≤ d)
      omega
    omega
  have hccl : IsClosed c.carrier := by
    unfold TracePiece.carrier
    rw [recursiveTrace_tiles_step0_cell_zero]
    exact (c.bottom.val.flat.compact.image c.tile.frame.continuous).isClosed
  obtain ⟨O, hO, hOeq⟩ : ∃ O : Set (E d), IsOpen O ∧
      relint c.carrier = O ∩ (affineSpan ℝ c.carrier : Set (E d)) := by
    have hopen := (isOpen_interior :
      IsOpen (interior ((↑) ⁻¹' c.carrier : Set (affineSpan ℝ c.carrier))))
    obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.1 hopen
    refine ⟨O, hO, ?_⟩
    ext x
    constructor
    · intro hx
      rw [relint, mem_intrinsicInterior] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [← hpre] at hy
      exact ⟨hy, y.property⟩
    · rintro ⟨hxO, hxA⟩
      rw [relint, mem_intrinsicInterior]
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      rw [← hpre]
      exact hxO
  have hspan : affineSpan ℝ c.carrier = affineSpan ℝ T :=
    recursiveTrace_tiles_step1_span c TracePiece.bottomIndex
  have hDA : ∀ x ∈ relint T ∩ ball q (min ρ0 ρ),
      x ∈ (affineSpan ℝ c.carrier : Set (E d)) := by
    intro x hx
    rw [hspan]
    exact mem_affineSpan ℝ (intrinsicInterior_subset hx.1)
  have hcover : relint T ∩ ball q (min ρ0 ρ) ⊆ O ∪ c.carrierᶜ := by
    intro x hx
    by_cases hxc : x ∈ c.carrier
    · left
      by_cases hxr : x ∈ relint c.carrier
      · rw [hOeq] at hxr
        exact hxr.1
      · exfalso
        have hxf : x ∈ relfrontier c.carrier := by
          unfold relfrontier
          rw [← closure_diff_intrinsicInterior, hccl.closure_eq]
          exact ⟨hxc, hxr⟩
        exact hEdisj x (hfl ⟨hxf, ball_subset_ball (min_le_right _ _) hx.2⟩) hx.1
    · exact Or.inr hxc
  have hempty : ¬ (relint T ∩ ball q (min ρ0 ρ) ∩ (O ∩ c.carrierᶜ)).Nonempty := by
    rintro ⟨x, hxD, hxO, hxc⟩
    have hxr : x ∈ relint c.carrier := by rw [hOeq]; exact ⟨hxO, hDA x hxD⟩
    exact hxc (intrinsicInterior_subset hxr)
  rcases (isPreconnected_iff_subset_of_disjoint.1 hDc.isPreconnected) O c.carrierᶜ hO
      hccl.isOpen_compl hcover (Set.not_nonempty_iff_eq_empty.1 hempty) with hsub | hsub
  · intro x hx
    rw [hOeq]
    exact ⟨hsub hx, hDA x hx⟩
  · obtain ⟨⟨y, hyc, hyb⟩, hcF⟩ := sites_exist_step3_inward_arm_step6_overlap_plane A F r q c
      hqc (min ρ0 ρ) (lt_min hρ0 hρ)
    exact (hsub ⟨hcF hyc, hyb⟩ (intrinsicInterior_subset hyc)).elim


open private hereditary_trace_step1_frontier_relint from Enforce.Source.Trace in
/-- Step 7 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a), dimension two):
"the same argument uses the native tiles in the half-disc inside the node". If every
listed edge through `q` of a native tile lies along the flag edge, then near `q` the
whole frontier of the tile lies along the flag edge ((H2): the frontier is the finite
union of listed cells, of dimension `≤ 1 = d - 1`). -/
private theorem sites_exist_step3_inward_arm_step7_flat_domain (hd : d = 2) (A : S.ι)
    (F : FacetFlag S A) (r : ℕ) (q : E d) (w : S.RoleWord A r) (hqF : q ∈ flagEdge A F r)
    (hall : ∀ e : CellName S (S.nativeTile A r w).ty, e.val.dim = 1 →
      q ∈ (S.nativeTile A r w).cell 0 e.val →
      (S.nativeTile A r w).cell 0 e.val ⊆ flagEdge A F r) :
    ∃ ρ > 0, frontier ((S.nativeTile A r w).carrier 0) ∩ ball q ρ ⊆ flagEdge A F r := by
  obtain ⟨ρ, hρ, hloc⟩ := sites_exist_step3_inward_arm_step11_local_cells
    (S.nativeTile A r w) q (flagEdge A F r) (fun e => e.dim ≤ 1) (by
      intro e he hdim hqe
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hdim with h0 | h1
      · intro y hy
        rw [sites_exist_step3_inward_arm_step12_point _ e h0 hy hqe]
        exact hqF
      · exact hall ⟨e, he⟩ h1 hqe)
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  obtain ⟨hxf, hxb⟩ := hx
  obtain ⟨G, hG, hxG⟩ := hereditary_trace_step1_frontier_relint _ 0 x hxf
  have hlt := (S.cx (S.nativeTile A r w).ty).dim_lt G hG
  exact hloc x hxb G hG (by omega) (intrinsicInterior_subset hxG)

open private hereditary_trace_step7_carrier from Enforce.Source.Trace in
/-- Step 9 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a), dimension two):
"overlapping one of the two adjacent" tiles. A native tile through `q` has interior
points of the node arbitrarily close to `q` ((H1): the tile is regular closed and lies
in the node). -/
private theorem sites_exist_step3_inward_arm_step9_overlap_domain (A : S.ι) (r : ℕ)
    (q : E d) (w : S.RoleWord A r) (hqC : q ∈ (S.nativeTile A r w).carrier 0) (ρ : ℝ)
    (hρ : 0 < ρ) :
    (interior ((S.nativeTile A r w).carrier 0) ∩ interior (S.supertile r A) ∩
      ball q ρ).Nonempty := by
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hRc : R.carrier r = S.supertile r A := by
    simp [R, FramedNode.carrier, placedSet]
  have hC : (S.nativeTile A r w).IsDescendant 0 R (0 + r) := by
    rw [zero_add]; exact recursiveTrace_tiles_step0_native_desc A r w
  have hsub : (S.nativeTile A r w).carrier 0 ⊆ S.supertile r A := by
    have := hereditary_trace_step7_carrier R (S.nativeTile A r w) 0 r hC
    rwa [zero_add, hRc] at this
  let φ := ((S.nativeTile A r w).prototypeFrame 0).toHomeomorphOfFiniteDimensional
  have hcar0 : (S.nativeTile A r w).carrier 0 = (S.nativeTile A r w).prototypeFrame 0 ''
      (S.proto (S.nativeTile A r w).ty).carrier := by
    simp [FramedNode.carrier, FramedNode.prototypeFrame, placedSet,
      SubstSystem.supertile, Set.image_image]
  have hcar : (S.nativeTile A r w).carrier 0 = φ '' (S.proto (S.nativeTile A r w).ty).carrier :=
    hcar0
  have hreg : closure (interior ((S.nativeTile A r w).carrier 0)) =
      (S.nativeTile A r w).carrier 0 := by
    rw [hcar, ← φ.image_interior, ← φ.image_closure,
      (S.proto (S.nativeTile A r w).ty).regularClosed]
  have hq' : q ∈ closure (interior ((S.nativeTile A r w).carrier 0)) := by
    rw [hreg]; exact hqC
  obtain ⟨y, hy, hyq⟩ := Metric.mem_closure_iff.1 hq' ρ hρ
  exact ⟨y, ⟨hy, interior_mono hsub hy⟩, by rw [mem_ball, dist_comm]; exact hyq⟩

open private hereditary_trace_step1_relint_image hereditary_trace_step1_cell_frontier
  from Enforce.Source.Trace in
/-- Step 8 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a), dimension two,
Lemma 1.0(a)): near `q ∈ relint h` the node is a closed half-disc bounded by the flag
edge; a native tile through `q` whose frontier near `q` lies along the flag edge fills
the open half-disc (it is connected, misses the tile frontier and meets its interior). -/
private theorem sites_exist_step3_inward_arm_step8_fill_domain (hd : d = 2) (A : S.ι)
    (F : FacetFlag S A) (r : ℕ) (q : E d) (hq : q ∈ relint (flagEdge A F r))
    (w : S.RoleWord A r) (hqC : q ∈ (S.nativeTile A r w).carrier 0) (ρ : ℝ) (hρ : 0 < ρ)
    (hfl : frontier ((S.nativeTile A r w).carrier 0) ∩ ball q ρ ⊆ flagEdge A F r) :
    ∃ ρ' > 0, interior (S.supertile r A) ∩ ball q ρ' ⊆
      interior ((S.nativeTile A r w).carrier 0) := by
  set h := F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩ with hh
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hR : ∀ e : Cell d, R.cell r e = (S.σ ^ r) '' e.carrier :=
    recursiveTrace_tiles_step0_root_cell A r
  have hRc : R.carrier r = S.supertile r A := by
    simp [R, FramedNode.carrier, placedSet]
  have hEF : flagEdge A F r ⊆ frontier (S.supertile r A) := by
    have := hereditary_trace_step1_cell_frontier R r h.val h.property
    rw [hR, hRc] at this
    exact this
  have himg : relint (flagEdge A F r) = (S.σ ^ r) '' relint h.val.carrier :=
    hereditary_trace_step1_relint_image (S.σ ^ r).toAffineEquiv h.val.carrier
  rw [himg] at hq
  obtain ⟨q0, hq0, rfl⟩ := hq
  have hF : h.val ∈ (S.cx A).facets := by
    unfold CellComplex.facets
    have h1 : h.val.dim = 1 := F.dimension _
    exact Finset.mem_filter.2 ⟨h.property, by omega⟩
  obtain ⟨r0, hr0, v, -, -, -, hAb⟩ := facet_halfball (S.proto A) (S.cx A) h.val hF q0 hq0
  let φ := (S.σ ^ r).toContinuousLinearEquiv.toHomeomorph
  have hsup : S.supertile r A = φ '' (S.proto A).carrier := rfl
  have hHc : Convex ℝ {x : E d | 0 ≤ inner ℝ v (x - q0)} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have heq : a • x + b • y - q0 = a • (x - q0) + b • (y - q0) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
    rw [heq, inner_add_right, inner_smul_right, inner_smul_right]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hIc : Convex ℝ (interior (S.proto A).carrier ∩ ball q0 r0) := by
    have hI : interior (S.proto A).carrier ∩ ball q0 r0 =
        interior ({x : E d | 0 ≤ inner ℝ v (x - q0)} ∩ ball q0 r0) := by
      rw [← hAb, interior_inter, isOpen_ball.interior_eq]
    rw [hI]
    exact (hHc.inter (convex_ball q0 r0)).interior
  have hWo : IsOpen (φ '' ball q0 r0) := φ.isOpenMap _ isOpen_ball
  obtain ⟨ρ1, hρ1, hball1⟩ := Metric.isOpen_iff.1 hWo (φ q0) ⟨q0, mem_ball_self hr0, rfl⟩
  refine ⟨min ρ1 ρ, lt_min hρ1 hρ, ?_⟩
  have hDeq : interior (S.supertile r A) ∩ ball ((S.σ ^ r) q0) (min ρ1 ρ) =
      φ '' (interior (S.proto A).carrier ∩ ball q0 r0) ∩ ball ((S.σ ^ r) q0) (min ρ1 ρ) := by
    ext x
    constructor
    · rintro ⟨hxi, hxb⟩
      obtain ⟨z, hz, rfl⟩ := hball1 (ball_subset_ball (min_le_left _ _) hxb)
      refine ⟨⟨z, ⟨?_, hz⟩, rfl⟩, hxb⟩
      rw [hsup, ← φ.image_interior] at hxi
      obtain ⟨z', hz', hzz⟩ := hxi
      rwa [← φ.injective hzz]
    · rintro ⟨⟨z, ⟨hzi, hz⟩, rfl⟩, hxb⟩
      refine ⟨?_, hxb⟩
      rw [hsup, ← φ.image_interior]
      exact ⟨z, hzi, rfl⟩
  have hDc : Convex ℝ (interior (S.supertile r A) ∩ ball ((S.σ ^ r) q0) (min ρ1 ρ)) := by
    rw [hDeq]
    exact (hIc.linear_image (S.σ ^ r).toLinearMap).inter (convex_ball _ _)
  have hCcl : IsClosed ((S.nativeTile A r w).carrier 0) :=
    (((S.proto _).compact.image (S.σ ^ 0).toContinuousLinearEquiv.continuous).image
      (S.nativeTile A r w).frame.continuous).isClosed
  have hcover : interior (S.supertile r A) ∩ ball ((S.σ ^ r) q0) (min ρ1 ρ) ⊆
      interior ((S.nativeTile A r w).carrier 0) ∪ ((S.nativeTile A r w).carrier 0)ᶜ := by
    intro x hx
    by_cases hxC : x ∈ (S.nativeTile A r w).carrier 0
    · left
      by_contra hxi
      have hxf : x ∈ frontier ((S.nativeTile A r w).carrier 0) := by
        rw [hCcl.frontier_eq]; exact ⟨hxC, hxi⟩
      have hxE := hfl ⟨hxf, ball_subset_ball (min_le_right _ _) hx.2⟩
      exact (hEF hxE).2 hx.1
    · exact Or.inr hxC
  rcases hDc.isPreconnected.subset_or_subset isOpen_interior hCcl.isOpen_compl
      (Set.disjoint_left.2 fun _ hi hc => hc (interior_subset hi)) hcover with hsub | hsub
  · exact hsub
  · obtain ⟨y, ⟨hyC, hyS⟩, hyb⟩ := sites_exist_step3_inward_arm_step9_overlap_domain A r _ w
      hqC (min ρ1 ρ) (lt_min hρ1 hρ)
    exact ((hsub ⟨hyS, hyb⟩) (interior_subset hyC)).elim

open private hereditary_trace_step1_cell_subset from Enforce.Source.Trace in
/-- Step 10 of the V4 proof of `sites_exist_step3_inward_arm` (V4 1.23(a)): "the polygons
of `C₁`, `C₂`" lie in their owners: a trace carrier lies in the native owner tile. -/
private theorem sites_exist_step3_inward_arm_step10_carrier (A : S.ι) (F : FacetFlag S A)
    (r : ℕ) (a : TracePiece A F r) :
    a.carrier ⊆ (S.nativeTile A r a.owner).carrier 0 :=
  hereditary_trace_step1_cell_subset a.tile 0 a.bottom.val a.bottom.property

/-- Step 3 of the V4 proof of `sites_exist` (V4 1.23(a), fan paragraph):
"At such a change `q`, the adjacent trace polygons have distinct owners. For `d ≥ 3`,
near `q` the two-dimensional flag cell is a half-plane ... Thus all trace polygons
through `q` list it as a vertex. Their finite fan has different extreme members, so
some separating edge enters the half-disc: this is the required inward arm. In `d = 2`
the same argument uses the native tiles in the half-disc inside the node." -/
private theorem sites_exist_step3_inward_arm (A : S.ι) (F : FacetFlag S A) (r : ℕ)
    (q : E d) (hq : sitesExistOwnerChange A F r q) : InwardTraceArm A F r q := by
  obtain ⟨hqrel, a, b, K, L, hab, ⟨eK, heK, rfl, hKa, hKF, hqK, hlist⟩,
    ⟨eL, heL, rfl, hLb, hLF, hqL, hlistb⟩, -⟩ := hq
  have hqF : q ∈ flagEdge A F r := intrinsicInterior_subset hqrel
  unfold InwardTraceArm
  by_cases hd : d = 2
  · rw [if_pos hd]
    by_cases hex : ∃ e : CellName S a.tile.ty, e.val.dim = 1 ∧ q ∈ a.tile.cell 0 e.val ∧
        ¬ a.tile.cell 0 e.val ⊆ flagEdge A F r
    · obtain ⟨e, he, hqe, hne⟩ := hex
      exact ⟨a.owner, e, he, hlist, hqe,
        sites_exist_step3_inward_arm_step3_heredity_domain hd A F r q hqrel a.owner e hqe hne⟩
    · push_neg at hex
      have hqa : q ∈ (S.nativeTile A r a.owner).carrier 0 :=
        sites_exist_step3_inward_arm_step10_carrier A F r a (hKa hqK)
      have hqb : q ∈ (S.nativeTile A r b.owner).carrier 0 :=
        sites_exist_step3_inward_arm_step10_carrier A F r b (hLb hqL)
      obtain ⟨ρ, hρ, hfl⟩ :=
        sites_exist_step3_inward_arm_step7_flat_domain hd A F r q a.owner hqF hex
      obtain ⟨ρ', hρ', hfill⟩ :=
        sites_exist_step3_inward_arm_step8_fill_domain hd A F r q hqrel a.owner hqa ρ hρ hfl
      obtain ⟨y, ⟨hyb, hyS⟩, hyball⟩ :=
        sites_exist_step3_inward_arm_step9_overlap_domain A r q b.owner hqb ρ' hρ'
      exact (Set.disjoint_left.1 (S.native_disjoint A r hab) (hfill ⟨hyS, hyball⟩) hyb).elim
  · rw [if_neg hd]
    by_cases hex : ∃ e : CellName S a.tile.ty, e.val.dim = 1 ∧ q ∈ a.tile.cell 0 e.val ∧
        a.tile.cell 0 e.val ⊆ a.carrier ∧ ¬ a.tile.cell 0 e.val ⊆ flagEdge A F r
    · obtain ⟨e, he, hqe, hsub, hne⟩ := hex
      exact ⟨a, e, he, hlist, hqe, hsub,
        sites_exist_step3_inward_arm_step2_heredity_plane A F r q hqrel a e hqe hsub hne⟩
    · push_neg at hex
      obtain ⟨ρ, hρ, hfl⟩ := sites_exist_step3_inward_arm_step4_flat_plane A F r q a hqF hex
      obtain ⟨ρ', hρ', hfill⟩ :=
        sites_exist_step3_inward_arm_step5_fill_plane hd A F r q hqrel a (hKa hqK) ρ hρ hfl
      obtain ⟨⟨y, hyb, hyball⟩, hbF⟩ :=
        sites_exist_step3_inward_arm_step6_overlap_plane A F r q b (hLb hqL) ρ' hρ'
      have hneq : a ≠ b := fun h => hab (h ▸ rfl)
      exact (Set.disjoint_left.1 ((recursiveTrace_tiles A F r).2.1 hneq)
        (hfill ⟨hbF hyb, hyball⟩) hyb).elim

/-- Step 4 of the V4 proof of `sites_exist` (V4 1.23(a)): "The distinct depth-`r`
owners have a least common ancestor of depth less than `r`". Distinct role words force
`r ≥ 1`, and the root `σ^r A` itself (depth `0 < r`) is a common standard ancestor. -/
private theorem sites_exist_step4_common_root (A : S.ι) (F : FacetFlag S A) (r : ℕ)
    (a b : TracePiece A F r) (hab : a.owner ≠ b.owner) :
    ∃ (j : ℕ) (P : FramedNode S), j < r ∧ S.IsStandardNode A r (r - j) P ∧
      a.tile.IsDescendant 0 P (r - j) ∧ b.tile.IsDescendant 0 P (r - j) := by
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      exact absurd (show (a.owner : Unit) = b.owner from rfl) hab
    · exact h
  let P : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hP (c : TracePiece A F r) : c.tile.IsDescendant 0 P (r - 0) := by
    refine ⟨r, by omega, c.owner, ?_⟩
    change S.nativeTile A r c.owner =
      ⟨(S.descendantNode A 0 r c.owner).ty,
        (S.descendantNode A 0 r c.owner).frame.trans (AffineIsometryEquiv.refl ℝ (E d))⟩
    rw [AffineIsometryEquiv.trans_refl]
    rfl
  refine ⟨0, P, hr, ⟨0, by omega, (show S.RoleWord A 0 from ()), rfl⟩, hP a, hP b⟩

/-- P18, V4 1.23(a): arbitrarily many ordinary sites occur from some depth on.
The sites in the finite witness set are distinct; expansion provides the length. -/
theorem sites_exist (A : S.ι) (F : FacetFlag S A) (N : ℕ) (hN : 1 ≤ N) :
    ∃ r : ℕ, ∀ r' : ℕ, r ≤ r' →
      ∃ q : Finset (E d), N ≤ q.card ∧ ∀ p ∈ q, IsSite A F r' p := by
  obtain ⟨D, hD⟩ := sites_exist_step2_owner_changes A F
  obtain ⟨r, hr⟩ := sites_exist_step1_long_edge A F (((N : ℝ) + 1) * D)
  refine ⟨r, fun r' hr' => ?_⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hr r' hr'
  obtain ⟨q, hcard, hq⟩ := hD r' N x y hx hy hxy
  refine ⟨q, hcard, fun p hp => ?_⟩
  obtain ⟨hrel, a, b, K, L, hab, hK, hL, hseg⟩ := hq p hp
  exact ⟨hrel, sites_exist_step3_inward_arm A F r' p (hq p hp), a, b, K, L, hab, hK, hL,
    hseg, sites_exist_step4_common_root A F r' a b hab⟩

/-- P18, V4 1.23(b): a selected-owner template records full relative frames,
vertex names and all recorded coface names, together with the normalized site. -/
abbrev SiteTemplate (S : SubstSystem d) :=
  E d × Set (FramedNode S × Cell d × (Fin d → Option (Cell d)))

/-- P18, V4 1.23(b): complete positioned star of selected owners at a site,
expressed in any one selected owner's frame. Owners without a trace chain are absent. -/
def siteTemplate {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (q : E d) (anchor : TracePiece A F r) : SiteTemplate S :=
  (anchor.tile.frame.symm q,
    {z | ∃ (a : TracePiece A F r) (v : Cell d), q ∈ a.carrier ∧
      v ∈ (S.cx a.tile.ty).vertices ∧ q ∈ a.tile.cell 0 v ∧
      z = (a.tile.move anchor.tile.frame.symm, v, a.chainNames)})

/-- P18, V4 1.23(b): all native-scale selected-owner templates, uniformly in
type, flag, depth, site and reference owner. -/
def siteTemplates (S : SubstSystem d) : Set (SiteTemplate S) :=
  {t | ∃ (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d)
    (anchor : TracePiece A F r), IsSite A F r q ∧ q ∈ anchor.carrier ∧
      t = siteTemplate q anchor}

/-- Step 1 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"translations are fixed by the common vertex". The native vertex coordinates
form a finite set, including when the type catalogue is empty. -/
private theorem site_fan_finite_step1_vertices (S : SubstSystem d) :
    {p : E d | ∃ A : S.ι, ∃ v ∈ (S.cx A).vertices, p ∈ v.carrier}.Finite := by
  have hv : ∀ (A : S.ι) (v : Cell d), v ∈ (S.cx A).vertices → v.carrier.Finite := by
    intro A v hv
    have hdim : v.dim = 0 := (Finset.mem_filter.mp hv).2
    have hzero : cellDirection v.carrier = ⊥ :=
      Submodule.finrank_eq_zero.mp (v.flat.dimension.trans hdim)
    apply ((vectorSpan_eq_bot_iff_subsingleton ℝ).mp ?_).finite
    simpa [cellDirection, direction_affineSpan] using hzero
  have hf := Set.finite_iUnion fun A : S.ι =>
    (S.cx A).vertices.finite_toSet.biUnion (hv A)
  exact hf.subset (by intro p hp; simpa using hp)

/-- Step 2 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"finitely many native choices". A full flag is determined by its finitely
many named cells; the geometric conditions add no further data. -/
private theorem site_fan_finite_step2_flags (A : S.ι) : Finite (FacetFlag S A) := by
  letI : Finite {j : ℕ // 1 ≤ j ∧ j < d} :=
    Finite.of_injective (fun j => (⟨j.val, j.property.2⟩ : Fin d))
      (by intro i j h; exact Subtype.ext (congrArg Fin.val h))
  apply Finite.of_injective (fun F : FacetFlag S A => F.cell)
  intro F G h
  cases F
  cases G
  cases h
  rfl

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"sign choices on the successive one-dimensional complements". On a real
line, fixing the norm of a vector leaves at most the two sign choices. -/
private theorem site_fan_finite_step3_line (V : Submodule ℝ (E d))
    (hV : Module.finrank ℝ V = 1) (z : E d) (hz : z ∈ V) :
    {x : E d | x ∈ V ∧ ‖x‖ = ‖z‖}.Finite := by
  apply (Set.toFinite ({z, -z} : Set (E d))).subset
  rintro x ⟨hx, hn⟩
  by_cases hzero : z = 0
  · have hxzero : x = 0 := norm_eq_zero.mp (by simpa [hzero] using hn)
    simp [hzero, hxzero]
  have hz' : (⟨z, hz⟩ : V) ≠ 0 := by simpa using hzero
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨z, hz⟩ : V) hz').mp hV ⟨x, hx⟩
  have heq : c • z = x := congrArg Subtype.val hc
  have hcabs : |c| = 1 := by
    have hnorm : |c| * ‖z‖ = 1 * ‖z‖ := by
      simpa [← heq, norm_smul, Real.norm_eq_abs] using hn
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hzero) hnorm
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hcabs with hc | hc
  · simp [← heq, hc]
  · simp [← heq, hc]

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"sign choices on the successive one-dimensional complements". An
orthogonal stabilizer of a complete flag has finite orbits on vectors. -/
private theorem site_fan_finite_step3_flag_orbit
    (V : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    ∀ k ≤ d, ∀ x ∈ V k,
      {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = V i}.image
        (fun R => R x) |>.Finite := by
  intro k
  induction k with
  | zero =>
      intro hk x hx
      have hV : V 0 = ⊥ := Submodule.finrank_eq_zero.mp (hdim 0 (by omega))
      have hxzero : x = 0 := by simpa [hV] using hx
      subst x
      exact (Set.finite_singleton (0 : E d)).subset
        (by rintro _ ⟨R, hR, rfl⟩; simp)
  | succ k ih =>
      intro hk x hx
      obtain ⟨y, hy, z, hz, hsum⟩ := (V k).exists_add_mem_mem_orthogonal x
      have hle : V k ≤ V (k + 1) := hmono k (by omega)
      have hzV : z ∈ V (k + 1) := by
        have heq : z = x - y := by rw [hsum]; abel
        rw [heq]
        exact (V (k + 1)).sub_mem hx (hle hy)
      have hline : Module.finrank ℝ ((V k)ᗮ ⊓ V (k + 1) : Submodule ℝ (E d)) = 1 := by
        have hh := Submodule.finrank_add_inf_finrank_orthogonal hle
        rw [hdim k (by omega), hdim (k + 1) hk] at hh
        omega
      have hyfinite := ih (by omega) y hy
      have hzfinite := site_fan_finite_step3_line ((V k)ᗮ ⊓ V (k + 1)) hline z ⟨hz, hzV⟩
      apply ((hyfinite.prod hzfinite).image (fun yz : E d × E d => yz.1 + yz.2)).subset
      rintro _ ⟨R, hR, rfl⟩
      refine ⟨(R y, R z), ⟨⟨R, hR, rfl⟩, ?_⟩, ?_⟩
      · refine ⟨⟨?_, ?_⟩, R.norm_map z⟩
        · have horth : ((V k)ᗮ).map R.toLinearEquiv.toLinearMap = (V k)ᗮ := by
            rw [Submodule.map_orthogonal_equiv, hR k (by omega)]
          rw [← horth]
          exact Submodule.mem_map_of_mem hz
        · rw [← hR (k + 1) hk]
          exact Submodule.mem_map_of_mem hzV
      · simpa [map_add] using (congrArg R hsum).symm

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"sign choices on the successive one-dimensional complements". Values on
one basis turn the finite vector orbits into a finite orthogonal stabilizer. -/
private theorem site_fan_finite_step3_flag_stabilizer
    (V : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = V i}.Finite := by
  let H := {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = V i}
  let b := stdOrthonormalBasis ℝ (E d)
  have htop : V d = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using hdim d le_rfl)
  have hpoint : ∀ i, (H.image (fun R => R (b i))).Finite := by
    intro i
    exact site_fan_finite_step3_flag_orbit V hdim hmono d le_rfl (b i) (by simp [htop])
  have heval : ((fun R : Ortho d => fun i => R (b i)) '' H).Finite :=
    (Set.Finite.pi' hpoint).subset (by rintro _ ⟨R, hR, rfl⟩ i; exact ⟨R, hR, rfl⟩)
  apply Set.Finite.of_finite_image heval
  intro R hR T hT heq
  exact b.toBasis.ext_linearIsometryEquiv (fun i => congrFun heq i)

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"all relative placements ... lie in a finite set" once two full flags are
specified. The transporter is a translate of the finite flag stabilizer. -/
private theorem site_fan_finite_step3_flag_transporters
    (V W : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = W i}.Finite := by
  classical
  let T := {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = W i}
  by_cases hT : T.Nonempty
  · obtain ⟨R₀, hR₀⟩ := hT
    apply ((site_fan_finite_step3_flag_stabilizer V hdim hmono).image
      (fun R => R.trans R₀)).subset
    intro R hR
    refine ⟨R.trans R₀.symm, ?_, ?_⟩
    · intro i hi
      change (V i).map (R₀.symm.toLinearEquiv.toLinearMap.comp
        R.toLinearEquiv.toLinearMap) = V i
      rw [Submodule.map_comp, hR i hi, ← hR₀ i hi, ← Submodule.map_comp]
      simp
    · apply LinearIsometryEquiv.ext
      intro x
      exact R₀.apply_symm_apply (R x)
  · exact Set.finite_empty.subset (by intro R hR; exact (hT ⟨R, hR⟩).elim)

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"The chains ... have direction spaces equal". Direction spaces commute
with the linear part of the actual isometric frame. -/
private theorem site_fan_finite_step3_direction_image (g : Iso d) (K : Set (E d)) :
    cellDirection (g '' K) =
      (cellDirection K).map g.linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  change (affineSpan ℝ (g.toAffineEquiv.toAffineMap '' K)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  rfl

/-- Full flags include the zero subspace and the ambient space when used
as a complete sequence of direction spaces. -/
private def siteFanFlagDirections {A : S.ι} (F : FacetFlag S A)
    (i : ℕ) : Submodule ℝ (E d) :=
  if hi : 1 ≤ i ∧ i < d then cellDirection (F.cell ⟨i, hi⟩).val.carrier
  else if i = 0 then ⊥ else ⊤

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"preserving this partial flag" with an additional polygon edge gives a
complete flag of direction spaces, of dimensions zero through `d`. -/
private theorem site_fan_finite_step3_flag_directions {A : S.ι}
    (F : FacetFlag S A) :
    (∀ i ≤ d, Module.finrank ℝ (siteFanFlagDirections F i) = i) ∧
    (∀ i < d, siteFanFlagDirections F i ≤ siteFanFlagDirections F (i + 1)) := by
  constructor
  · intro i hi
    by_cases hmid : 1 ≤ i ∧ i < d
    · rw [show siteFanFlagDirections F i =
          cellDirection (F.cell ⟨i, hmid⟩).val.carrier from dif_pos hmid]
      exact (F.cell ⟨i, hmid⟩).val.flat.dimension.trans (F.dimension ⟨i, hmid⟩)
    · by_cases hz : i = 0
      · simp [siteFanFlagDirections, hmid, hz]
      · have hid : i = d := by omega
        rw [show siteFanFlagDirections F i = ⊤ by
          simp only [siteFanFlagDirections, dif_neg hmid, if_neg hz]]
        simp [hid]
  · intro i hi
    by_cases hz : i = 0
    · simp [siteFanFlagDirections, hz]
    by_cases ht : i + 1 < d
    · have hmid : 1 ≤ i ∧ i < d := ⟨by omega, hi⟩
      have hnext : 1 ≤ i + 1 ∧ i + 1 < d := ⟨by omega, ht⟩
      simp only [siteFanFlagDirections, dif_pos hmid, dif_pos hnext]
      simpa only [cellDirection, direction_affineSpan] using
        vectorSpan_mono ℝ (F.nested ⟨i, hmid⟩ ⟨i + 1, hnext⟩ (by simp))
    · have hnext : ¬(1 ≤ i + 1 ∧ i + 1 < d) := by omega
      simp only [siteFanFlagDirections, dif_neg hnext, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, if_false]
      exact le_top

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"translations are fixed by the common vertex". Two full native flags and
one prescribed point image admit only finitely many isometric frames. -/
private theorem site_fan_finite_step3_affine_transporters
    {A B : S.ι} (F : FacetFlag S A) (G : FacetFlag S B) (p q : E d) :
    {g : Iso d | g p = q ∧ ∀ i,
      cellDirection (g '' (F.cell i).val.carrier) =
        cellDirection (G.cell i).val.carrier}.Finite := by
  have hF := site_fan_finite_step3_flag_directions F
  have hrot := site_fan_finite_step3_flag_transporters
    (siteFanFlagDirections F) (siteFanFlagDirections G) hF.1 hF.2
  have himage : (AffineIsometryEquiv.linearIsometryEquiv ''
      {g : Iso d | g p = q ∧ ∀ i,
        cellDirection (g '' (F.cell i).val.carrier) =
          cellDirection (G.cell i).val.carrier}).Finite := by
    apply hrot.subset
    rintro _ ⟨g, hg, rfl⟩ i hi
    by_cases hmid : 1 ≤ i ∧ i < d
    · simpa only [siteFanFlagDirections, dif_pos hmid,
        site_fan_finite_step3_direction_image] using hg.2 ⟨i, hmid⟩
    · simp only [siteFanFlagDirections, dif_neg hmid]
      split_ifs <;> simp
  apply Set.Finite.of_finite_image himage
  intro g hg h hh heq
  apply AffineIsometryEquiv.ext
  intro x
  have hgx := g.map_vadd p (x - p)
  have hhx := h.map_vadd p (x - p)
  simp only [vadd_eq_add, sub_add_cancel, hg.1, hh.1, heq] at hgx hhx
  exact hgx.trans hhx.symm

/-- Step 4 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"at native scale". A height-zero named cell is placed by the native
isometric frame alone. -/
private theorem site_fan_finite_step4_cell_zero (C : FramedNode S) (e : Cell d) :
    C.cell 0 e = C.frame '' e.carrier := by
  simp [FramedNode.cell, FramedNode.prototypeFrame]

/-- Step 4 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"translations are fixed by the common vertex". Pulling a listed point
back by its owner's frame gives one of the native vertex coordinates. -/
private theorem site_fan_finite_step4_listed_coordinate (C : FramedNode S)
    (q : E d) (hq : C.Lists 0 q) :
    ∃ A : S.ι, ∃ v ∈ (S.cx A).vertices, C.frame.symm q ∈ v.carrier := by
  obtain ⟨v, hv, hp⟩ := hq
  rw [site_fan_finite_step4_cell_zero] at hp
  obtain ⟨p, hp, rfl⟩ := hp
  exact ⟨C.ty, v, hv, by simpa using hp⟩

/-- Two native owners have aligned full flags when all their placed
flag direction spaces, including the edge line, agree. -/
private def siteFanAligned (C D : FramedNode S) : Prop :=
  ∃ (F : FacetFlag S C.ty) (G : FacetFlag S D.ty), ∀ i,
    cellDirection (C.cell 0 (F.cell i).val) =
      cellDirection (D.cell 0 (G.cell i).val)

/-- Step 4 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"finitely many native choices ... and reflections". For owners sharing a
listed point and aligned full flags, their relative frame belongs to one
finite alphabet, independent of the common point or subdivision depth. -/
private theorem site_fan_finite_step4_transitions (S : SubstSystem d) :
    ∃ D : Set (Iso d), D.Finite ∧ ∀ (C B : FramedNode S) (q : E d),
      C.Lists 0 q → B.Lists 0 q → siteFanAligned C B →
      C.frame.trans B.frame.symm ∈ D := by
  classical
  let V := {p : E d | ∃ A : S.ι, ∃ v ∈ (S.cx A).vertices, p ∈ v.carrier}
  have hV : V.Finite := site_fan_finite_step1_vertices S
  letI : ∀ A : S.ι, Finite (FacetFlag S A) := site_fan_finite_step2_flags
  let D : Set (Iso d) := ⋃ (A : S.ι) (B : S.ι) (F : FacetFlag S A)
      (G : FacetFlag S B) (p ∈ V) (q ∈ V),
    {g : Iso d | g p = q ∧ ∀ i,
      cellDirection (g '' (F.cell i).val.carrier) =
        cellDirection (G.cell i).val.carrier}
  refine ⟨D, ?_, ?_⟩
  · exact Set.finite_iUnion fun A => Set.finite_iUnion fun B =>
      Set.finite_iUnion fun F => Set.finite_iUnion fun G =>
      hV.biUnion fun p hp => hV.biUnion fun q hq =>
        site_fan_finite_step3_affine_transporters F G p q
  · intro C B q hC hB hCB
    obtain ⟨F, G, hFG⟩ := hCB
    refine Set.mem_iUnion.mpr ⟨C.ty, Set.mem_iUnion.mpr ⟨B.ty,
      Set.mem_iUnion.mpr ⟨F, Set.mem_iUnion.mpr ⟨G,
      Set.mem_iUnion.mpr ⟨C.frame.symm q, Set.mem_iUnion.mpr
        ⟨site_fan_finite_step4_listed_coordinate C q hC,
      Set.mem_iUnion.mpr ⟨B.frame.symm q, Set.mem_iUnion.mpr
        ⟨site_fan_finite_step4_listed_coordinate B q hB, ?_⟩⟩⟩⟩⟩⟩⟩⟩
    constructor
    · simp
    · intro i
      have heq := congrArg
        (fun U : Submodule ℝ (E d) =>
          U.map B.frame.symm.linearIsometryEquiv.toLinearEquiv.toLinearMap) (hFG i)
      simp only [site_fan_finite_step4_cell_zero,
        ← site_fan_finite_step3_direction_image] at heq
      simpa [← Set.image_comp] using heq

/-- The selected owners, forgetting duplicate chain occurrences of one owner. -/
private def siteFanOwners {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (q : E d) : Set (FramedNode S) :=
  {C | ∃ a : TracePiece A F r, q ∈ a.carrier ∧ C = a.tile}

/-- Join distinct selected owners whenever their full native flags align.
Consecutive sectors in the planar fan supply such edges. -/
private def siteFanGraph {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (q : E d) : SimpleGraph (siteFanOwners (A := A) (F := F) (r := r) q) where
  Adj C B := C ≠ B ∧ siteFanAligned C.val B.val
  symm := by
    rintro C B ⟨hne, F, G, hFG⟩
    exact ⟨hne.symm, G, F, fun i => (hFG i).symm⟩
  loopless := ⟨by intro C h; exact h.1 rfl⟩

/-- Step 1 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.23(b)):
"The chains ... have direction spaces equal". Affine placement preserves
cell dimensions, also for the expanded ancestral flag. -/
private theorem site_fan_finite_step5_listed_step1_dimension
    (g : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
    Module.finrank ℝ (cellDirection (g '' K)) =
      Module.finrank ℝ (cellDirection K) := by
  change Module.finrank ℝ (affineSpan ℝ (g.toAffineMap '' K)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  exact LinearEquiv.finrank_map_eq g.linear (cellDirection K)

/-- Step 1 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.23(b)):
"a vertex of a cell of C is a vertex of C". Every placed listed cell lies
on its owner's frontier. -/
private theorem site_fan_finite_step5_listed_step1_cell_frontier
    (C : FramedNode S) (n : ℕ) (e : CellName S C.ty) :
    C.cell n e.val ⊆ frontier (C.carrier n) := by
  have he : e.val.carrier ⊆ frontier (S.proto C.ty).carrier := by
    rw [← (S.cx C.ty).carriers_cover]
    exact subset_iUnion_of_subset e.val (subset_iUnion_of_subset e.property Subset.rfl)
  let g := (C.prototypeFrame n).toHomeomorphOfFiniteDimensional
  have hc : C.carrier n = g '' (S.proto C.ty).carrier := by
    simp [g, FramedNode.prototypeFrame, FramedNode.carrier, SubstSystem.supertile,
      placedSet, Set.image_image]
  rw [hc, ← g.image_frontier]
  exact image_mono he

/-- Step 1 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.23(b)):
"at native scale". The relative interior and its closure commute with
an owner's isometric native frame. -/
private theorem site_fan_finite_step5_listed_step1_native_relint
    (C : FramedNode S) (e : Cell d) :
    relint (C.cell 0 e) = C.frame '' relint e.carrier ∧
      closure (relint (C.cell 0 e)) = C.cell 0 e := by
  have hc : C.cell 0 e = C.frame '' e.carrier := by
    simp [FramedNode.cell, FramedNode.prototypeFrame]
  have hi : relint (C.cell 0 e) = C.frame '' relint e.carrier := by
    rw [hc]
    exact C.frame.toAffineIsometry.image_intrinsicInterior e.carrier
  refine ⟨hi, ?_⟩
  rw [hi, hc]
  simpa only [e.flat.regularClosed] using
    (C.frame.toHomeomorph.image_closure (relint e.carrier)).symm

/-- Step 2 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.22(c)):
"applied to the descendant". Child placement at positive height is the
conjugate of the prescribed native placement. -/
private theorem site_fan_finite_step5_listed_step2_place_scaled (n : ℕ) {A : S.ι}
    (i : S.I A) (x : E d) :
    S.placeChild n i ((S.σ ^ n) x) = (S.σ ^ n) ((S.child A i).frame x) := by
  rw [S.placeChild_apply]
  simp [linearConj, Child.frame, rigidMotion, LinearEquiv.mul_apply,
    zpow_natCast, zpow_neg, AffineIsometryEquiv.coe_trans]

/-- Step 2 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.22(c)):
"applied to the descendant". Every child is contained in its parent. -/
private theorem site_fan_finite_step5_listed_step2_child_subset
    (N : FramedNode S) (n : ℕ) (i : S.I N.ty) :
    (N.child n i).carrier n ⊆ N.carrier (n + 1) := by
  have hc := Set.subset_iUnion (fun i : S.I N.ty =>
    placedSet (S.child N.ty i).frame (S.proto (S.child N.ty i).ty).carrier) i
  rw [← S.children_cover N.ty] at hc
  rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
  change N.frame (S.placeChild n i ((S.σ ^ n) x)) ∈ N.frame '' S.supertile (n + 1) N.ty
  rw [site_fan_finite_step5_listed_step2_place_scaled]
  obtain ⟨p, hp, heq⟩ := hc ⟨x, hx, rfl⟩
  refine ⟨(S.σ ^ n) ((S.child N.ty i).frame x), ⟨p, hp, ?_⟩, rfl⟩
  rw [pow_succ, LinearEquiv.mul_apply, heq]

/-- Step 2 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.22(c)):
"applied to the descendant". Iterating child containment gives containment
for every recorded descendant. -/
private theorem site_fan_finite_step5_listed_step2_descendant_subset
    (P C : FramedNode S) (n h : ℕ) (hC : C.IsDescendant h P n) :
    C.carrier h ⊆ P.carrier n := by
  obtain ⟨k, rfl, w, rfl⟩ := hC
  induction k generalizing P with
  | zero => simpa [SubstSystem.descendantNode, FramedNode.move]
  | succ k ih =>
    have hc := ih (P.child (h + k) w.1) w.2
    have heq : (S.descendantNode P.ty h (k + 1) w).move P.frame =
        (S.descendantNode (P.child (h + k) w.1).ty h k w.2).move
          (P.child (h + k) w.1).frame := by
      simp [SubstSystem.descendantNode, FramedNode.move, FramedNode.child,
        ← AffineIsometryEquiv.trans_assoc]
    rw [heq]
    exact hc.trans (site_fan_finite_step5_listed_step2_child_subset P (h + k) w.1)

/-- Step 2 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.22(c)):
"the least common ancestor". Concatenation retains the exact standard
frames, so a child of a standard node is again standard. -/
private theorem site_fan_finite_step5_listed_step2_join_words
    (A : S.ι) (h m k : ℕ) (u : S.RoleWord A k)
    (v : S.RoleWord (S.descendantNode A (h + m) k u).ty m) :
    ∃ w : S.RoleWord A (m + k),
      S.descendantNode A h (m + k) w =
        (S.descendantNode (S.descendantNode A (h + m) k u).ty h m v).move
          (S.descendantNode A (h + m) k u).frame := by
  induction k generalizing A with
  | zero =>
    refine ⟨v, ?_⟩
    simp [SubstSystem.descendantNode, FramedNode.move]
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih (S.child A u.1).ty u.2 v
    refine ⟨⟨u.1, w⟩, ?_⟩
    change (S.descendantNode (S.child A u.1).ty h (m + k) w).move
      (S.placeChild (h + (m + k)) u.1) = _
    rw [hw]
    simp [SubstSystem.descendantNode, FramedNode.move, Nat.add_assoc,
      ← AffineIsometryEquiv.trans_assoc]

/-- Step 2 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.22(c)):
"the least common ancestor". Child occurrences stay in the same standard
hierarchy as the original flag. -/
private theorem site_fan_finite_step5_listed_step2_standard_child
    (A : S.ι) (r n : ℕ) (P : FramedNode S)
    (hP : S.IsStandardNode A r (n + 1) P) (i : S.I P.ty) :
    S.IsStandardNode A r n (P.child n i) := by
  obtain ⟨k, hk, u, rfl⟩ := hP
  obtain ⟨w, hw⟩ := site_fan_finite_step5_listed_step2_join_words A n 1 k u ⟨i, ()⟩
  refine ⟨1 + k, by omega, w, ?_⟩
  simpa [SubstSystem.descendantNode, FramedNode.move, FramedNode.child] using hw.symm

/-- Step 2 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.22(c)):
"applied to the descendant". A standard node has the root as an exact
recorded ancestor, including when it is the root itself. -/
private theorem site_fan_finite_step5_listed_step2_standard_descendant
    (A : S.ι) (r h : ℕ) (P : FramedNode S)
    (hP : S.IsStandardNode A r h P) :
    P.IsDescendant h ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩ r := by
  obtain ⟨k, hk, w, rfl⟩ := hP
  refine ⟨k, hk, w, ?_⟩
  simp [FramedNode.move]

/-- Step 3 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.22(c)):
"the cell of the ancestor whose relative interior meets" the descendant
cell is taken inside a closed ancestor carrier. -/
private theorem site_fan_finite_step5_listed_step3_carrier_closed
    (C : FramedNode S) (n : ℕ) : IsClosed (C.carrier n) := by
  have hc : C.carrier n =
      (C.prototypeFrame n).toHomeomorphOfFiniteDimensional '' (S.proto C.ty).carrier := by
    simp [FramedNode.prototypeFrame, FramedNode.carrier, SubstSystem.supertile,
      placedSet, Set.image_image]
  rw [hc]
  exact ((S.proto C.ty).compact.image
    (C.prototypeFrame n).toHomeomorphOfFiniteDimensional.continuous).isClosed

/-- Step 3 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.22(c)):
"the cell of the ancestor whose relative interior meets" the descendant
cell lies in the same outer flag cell, by heredity. -/
private theorem site_fan_finite_step5_listed_step3_lift_chain
    {A : S.ι} {F : FacetFlag S A} {r h j : ℕ}
    (P C : FramedNode S) (hP : S.IsStandardNode A r h P)
    (hC : C.IsDescendant 0 P h) (a : ChainOccurrence A F r C 0 j) :
    ∃ b : ChainOccurrence A F r P h j, ∀ i,
      relint (C.cell 0 (a.cell i).val) ⊆ relint (P.cell h (b.cell i).val) := by
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hPR : P.IsDescendant h R r :=
    site_fan_finite_step5_listed_step2_standard_descendant A r h P hP
  have hPsub := site_fan_finite_step5_listed_step2_descendant_subset R P r h hPR
  have hCsub := site_fan_finite_step5_listed_step2_descendant_subset P C h 0 hC
  have hfront (i : ChainIndex d j) :
      C.cell 0 (a.cell i).val ⊆ frontier (P.carrier h) := by
    intro x hx
    have hxC : x ∈ C.carrier 0 :=
      (site_fan_finite_step5_listed_step3_carrier_closed C 0).frontier_subset
        (site_fan_finite_step5_listed_step1_cell_frontier C 0 (a.cell i) hx)
    have hxR : x ∈ frontier (R.carrier r) := by
      apply site_fan_finite_step5_listed_step1_cell_frontier R r
        (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩)
      simpa [R, FramedNode.cell, FramedNode.prototypeFrame] using a.contained i hx
    exact ⟨subset_closure (hCsub hxC), fun hi => hxR.2 (interior_mono hPsub hi)⟩
  let c (i : ChainIndex d j) := ancestralStratum P C h 0 hC (a.cell i) (hfront i)
  have hs (i : ChainIndex d j) :=
    ancestralStratum_spec P C h 0 hC (a.cell i) (hfront i)
  have hcont (i : ChainIndex d j) :
      P.cell h (c i).val ⊆
        (S.σ ^ r) '' (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier := by
    have hn : (relint (C.cell 0 (a.cell i).val)).Nonempty := by
      rw [(site_fan_finite_step5_listed_step1_native_relint C (a.cell i).val).1]
      exact (a.cell i).val.flat.relint_nonempty.image C.frame
    obtain ⟨x, hx⟩ := hn
    have ht := hereditary_trace R P r h hPR
      (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val (c i).val
      (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).property (c i).property
      ⟨x, (hs i).1 hx, by
        simpa [R, FramedNode.cell, FramedNode.prototypeFrame] using
          a.contained i (intrinsicInterior_subset hx)⟩
    simpa [R, FramedNode.cell, FramedNode.prototypeFrame] using ht
  refine ⟨{ cell := c, dimension := ?_, nested := ?_, contained := hcont }, ?_⟩
  · intro i
    have hlo : i.val.val ≤ (c i).val.dim := by simpa [a.dimension i] using (hs i).2
    have hle := Submodule.finrank_mono
      (AffineSubspace.direction_le (affineSpan_mono ℝ (hcont i)))
    have hdimL : Module.finrank ℝ (cellDirection (P.cell h (c i).val)) =
        (c i).val.dim :=
      (site_fan_finite_step5_listed_step1_dimension (P.prototypeFrame h) _).trans
        (c i).val.flat.dimension
    have hdimR : Module.finrank ℝ (cellDirection ((S.σ ^ r) ''
        (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier)) = i.val.val :=
      (site_fan_finite_step5_listed_step1_dimension (S.σ ^ r).toAffineEquiv _).trans
        ((F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.flat.dimension.trans
          (F.dimension ⟨i.val.val, i.property.2, i.val.isLt⟩))
    simp only [cellDirection] at hdimL hdimR
    exact le_antisymm (by simpa only [hdimL, hdimR] using hle) hlo
  · intro i k hik
    have ht := ancestralStratum_mono P C h 0 hC (a.cell k) (a.cell i)
      (hfront k) (hfront i) (image_mono (a.nested i k hik))
    exact (Set.image_subset_image_iff (P.prototypeFrame h).injective).mp ht
  · intro i
    exact (hs i).1

/-- Step 4 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.22(c)):
"the two chain occurrences". A role word's first letter selects its
child, and the remaining letters retain the same native owner frame. -/
private theorem site_fan_finite_step5_listed_step4_native_tail
    (P : FramedNode S) (n : ℕ) (i : S.I P.ty)
    (w : S.RoleWord (S.child P.ty i).ty n) :
    (S.nativeTile P.ty (n + 1) ⟨i, w⟩).move P.frame =
      (S.nativeTile (P.child n i).ty n w).move (P.child n i).frame := by
  simp [SubstSystem.nativeTile, SubstSystem.descendantNode, FramedNode.move,
    FramedNode.child, ← AffineIsometryEquiv.trans_assoc]

/-- Step 4 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.22(c)):
"contradicting Lemma 1.22(c) for the two chain occurrences". Full edge
chains of distinct native owners have disjoint edge interiors: lift both
chains to their first distinct children of a common standard ancestor. -/
private theorem site_fan_finite_step5_listed_step4_edge_chains_disjoint
    {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (n : ℕ) (P : FramedNode S) (hP : S.IsStandardNode A r n P)
    (u v : S.RoleWord P.ty n) (huv : u ≠ v)
    (C D : FramedNode S)
    (hC : C = (S.nativeTile P.ty n u).move P.frame)
    (hD : D = (S.nativeTile P.ty n v).move P.frame)
    (a : ChainOccurrence A F r C 0 1) (b : ChainOccurrence A F r D 0 1) :
    Disjoint
      (relint (C.cell 0 (a.cell ⟨⟨1, by have := (Fact.out : 2 ≤ d); omega⟩,
        le_rfl, le_rfl⟩).val))
      (relint (D.cell 0 (b.cell ⟨⟨1, by have := (Fact.out : 2 ≤ d); omega⟩,
        le_rfl, le_rfl⟩).val)) := by
  induction n generalizing P C D with
  | zero => exact (huv (@Subsingleton.elim Unit _ u v)).elim
  | succ n ih =>
    obtain ⟨i, u⟩ := u
    obtain ⟨l, v⟩ := v
    have hCi : C = (S.nativeTile (P.child n i).ty n u).move (P.child n i).frame :=
      hC.trans (site_fan_finite_step5_listed_step4_native_tail P n i u)
    have hDl : D = (S.nativeTile (P.child n l).ty n v).move (P.child n l).frame :=
      hD.trans (site_fan_finite_step5_listed_step4_native_tail P n l v)
    by_cases hil : i = l
    · subst l
      have huv' : u ≠ v := by
        intro heq
        exact huv (by cases heq; rfl)
      exact ih (P.child n i)
        (site_fan_finite_step5_listed_step2_standard_child A r n P hP i)
        u v huv' C D hCi hDl a b
    · have hCi' : C.IsDescendant 0 (P.child n i) n :=
        ⟨n, by omega, u, hCi⟩
      have hDl' : D.IsDescendant 0 (P.child n l) n :=
        ⟨n, by omega, v, hDl⟩
      obtain ⟨a', ha'⟩ := site_fan_finite_step5_listed_step3_lift_chain
        (P.child n i) C (site_fan_finite_step5_listed_step2_standard_child A r n P hP i)
        hCi' a
      obtain ⟨b', hb'⟩ := site_fan_finite_step5_listed_step3_lift_chain
        (P.child n l) D (site_fan_finite_step5_listed_step2_standard_child A r n P hP l)
        hDl' b
      exact (chain_occurrences_disjoint A F r n P hP i l hil 1 le_rfl
        (by have := (Fact.out : 2 ≤ d); omega) a' b').mono (ha' _) (hb' _)

/-- Step 5 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.23(b)):
"a vertex of a cell of C is a vertex of C". A cell whose relative interior
contains the point is contained in every other incident listed cell. -/
private theorem site_fan_finite_step5_listed_step5_incidence
    (C : FramedNode S) (e f : CellName S C.ty) (q : E d)
    (he : q ∈ relint (C.cell 0 e.val)) (hf : q ∈ C.cell 0 f.val) :
    e.val.carrier ⊆ f.val.carrier := by
  rw [(site_fan_finite_step5_listed_step1_native_relint C e.val).1] at he
  obtain ⟨p, hp, rfl⟩ := he
  have hpf : p ∈ f.val.carrier := by
    have hc : C.cell 0 f.val = C.frame '' f.val.carrier := by
      simp [FramedNode.cell, FramedNode.prototypeFrame]
    rw [hc] at hf
    exact C.frame.injective.mem_set_image.mp hf
  have hpA : p ∈ frontier (S.proto C.ty).carrier := by
    rw [← (S.cx C.ty).cover]
    exact mem_iUnion.mpr ⟨e.val, mem_iUnion.mpr ⟨e.property, hp⟩⟩
  have hmin : (S.cx C.ty).minimalCell p hpA = e.val := by
    by_contra hne
    exact Set.disjoint_left.mp
      ((S.cx C.ty).relint_disjoint _ ((S.cx C.ty).minimalCell_mem p hpA)
        e.val e.property hne)
      ((S.cx C.ty).mem_relint_minimalCell p hpA) hp
  simpa only [hmin] using (S.cx C.ty).minimalCell_subset p hpA f.val f.property hpf

/-- Step 5 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.23(a)):
"an edge through q in its relative interior would have to lie along h".
Heredity puts the selected owner's minimal cell in the flag edge, so an
unlisted point lies in the relative interior of a listed one-cell there. -/
private theorem site_fan_finite_step5_listed_step5_minimal_edge
    {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (a : TracePiece A F r) (q : E d) (ha : q ∈ a.carrier)
    (hq : q ∈ flagEdge A F r) (hn : ¬ a.tile.Lists 0 q) :
    ∃ e : CellName S a.tile.ty, e.val.dim = 1 ∧
      q ∈ relint (a.tile.cell 0 e.val) ∧
      a.tile.cell 0 e.val ⊆ flagEdge A F r ∧
      e.val.carrier ⊆ a.bottom.val.carrier := by
  have hqa := site_fan_finite_step5_listed_step1_cell_frontier a.tile 0 a.bottom ha
  obtain ⟨e, he, _⟩ := placedMinimalCell_exists_unique a.tile 0 q hqa
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  let k : {j : ℕ // 1 ≤ j ∧ j < d} :=
    ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩
  have hdesc : a.tile.IsDescendant 0 R r := by
    refine ⟨r, by omega, a.owner, ?_⟩
    simp [TracePiece.tile, SubstSystem.nativeTile, FramedNode.move, R]
  have hsub : a.tile.cell 0 e.val ⊆ flagEdge A F r := by
    have ht := hereditary_trace R a.tile r 0 hdesc (F.cell k).val e.val
      (F.cell k).property e.property
      ⟨q, he, by simpa [R, k, FramedNode.cell, FramedNode.prototypeFrame, flagEdge] using hq⟩
    simpa [R, k, FramedNode.cell, FramedNode.prototypeFrame, flagEdge] using ht
  have hdim : e.val.dim ≤ 1 := by
    have hle := Submodule.finrank_mono
      (AffineSubspace.direction_le (affineSpan_mono ℝ hsub))
    have hl : Module.finrank ℝ (cellDirection (a.tile.cell 0 e.val)) = e.val.dim :=
      (site_fan_finite_step5_listed_step1_dimension (a.tile.prototypeFrame 0) _).trans
        e.val.flat.dimension
    have hr : Module.finrank ℝ (cellDirection (flagEdge A F r)) = 1 :=
      (site_fan_finite_step5_listed_step1_dimension (S.σ ^ r).toAffineEquiv _).trans
        ((F.cell k).val.flat.dimension.trans (F.dimension k))
    simp only [cellDirection] at hl hr
    simpa only [hl, hr] using hle
  have hzero : e.val.dim ≠ 0 := by
    intro hz
    exact hn ⟨e.val, Finset.mem_filter.mpr ⟨e.property, hz⟩, intrinsicInterior_subset he⟩
  exact ⟨e, by omega, he, hsub,
    site_fan_finite_step5_listed_step5_incidence a.tile e a.bottom q he ha⟩

/-- Step 6 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.22(c)):
"a chain occurrence". A listed edge inside the bottom trace cell and
along the flag edge extends the trace's recorded cofaces down to dimension one. -/
private theorem site_fan_finite_step5_listed_step6_extend_edge
    {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (a : TracePiece A F r) (e : CellName S a.tile.ty) (he : e.val.dim = 1)
    (hsub : e.val.carrier ⊆ a.bottom.val.carrier)
    (hflag : a.tile.cell 0 e.val ⊆ flagEdge A F r) :
    ∃ b : ChainOccurrence A F r a.tile 0 1,
      b.cell ⟨⟨1, by have := (Fact.out : 2 ≤ d); omega⟩, le_rfl, le_rfl⟩ = e := by
  classical
  have ht : traceDimension d ≤ 2 := min_le_left _ _
  let c (i : ChainIndex d 1) : CellName S a.tile.ty :=
    if hi : i.val.val = 1 then e
    else a.chain.cell ⟨i.val, by omega, i.property.2⟩
  refine ⟨{ cell := c, dimension := ?_, nested := ?_, contained := ?_ }, ?_⟩
  · intro i
    dsimp only [c]
    split_ifs with hi
    · exact he.trans hi.symm
    · exact a.chain.dimension _
  · intro i k hik
    by_cases hi : i.val.val = 1
    · by_cases hk : k.val.val = 1
      · simp only [c, dif_pos hi, dif_pos hk]
        exact Subset.rfl
      · simp only [c, dif_pos hi, dif_neg hk]
        exact hsub.trans (a.chain.nested TracePiece.bottomIndex _ (by
          change traceDimension d ≤ k.val.val
          have := k.property.2
          omega))
    · have hk : k.val.val ≠ 1 := by
        have := i.property.2
        omega
      simp only [c, dif_neg hi, dif_neg hk]
      exact a.chain.nested _ _ hik
  · intro i
    dsimp only [c]
    split_ifs with hi
    · simpa [flagEdge, hi] using hflag
    · exact a.chain.contained _
  · simp [c]

/-- Step 7 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.23(a)):
"that edge along h". Every native one-cell contained in the flag edge
has the same affine line as that flag edge. -/
private theorem site_fan_finite_step5_listed_step7_edge_span
    {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (C : FramedNode S) (e : CellName S C.ty) (he : e.val.dim = 1)
    (hsub : C.cell 0 e.val ⊆ flagEdge A F r) :
    affineSpan ℝ (C.cell 0 e.val) = affineSpan ℝ (flagEdge A F r) := by
  have hl : Module.finrank ℝ (cellDirection (C.cell 0 e.val)) = 1 :=
    (site_fan_finite_step5_listed_step1_dimension (C.prototypeFrame 0) _).trans
      (e.val.flat.dimension.trans he)
  have hr : Module.finrank ℝ (cellDirection (flagEdge A F r)) = 1 :=
    (site_fan_finite_step5_listed_step1_dimension (S.σ ^ r).toAffineEquiv _).trans
      ((F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val.flat.dimension.trans
        (F.dimension ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩))
  have hle := affineSpan_mono ℝ hsub
  have hn : (relint (C.cell 0 e.val)).Nonempty := by
    rw [(site_fan_finite_step5_listed_step1_native_relint C e.val).1]
    exact e.val.flat.relint_nonempty.image C.frame
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) (hl.trans hr.symm))
    (hn.mono (intrinsicInterior_subset.trans (subset_affineSpan ℝ _))) hle

/-- Step 7 of the V4 proof of `site_fan_finite_step5_listed` (V4 1.23(a)):
"overlapping the polygon of C₁ or C₂". In a common affine span, the
relative interior of one set meets any relative interior accumulating at
one of its points. This includes the one-dimensional boundary trace. -/
private theorem site_fan_finite_step5_listed_step7_overlap
    {K L : Set (E d)} (hspan : affineSpan ℝ K = affineSpan ℝ L)
    {q : E d} (hqK : q ∈ relint K) (hqL : q ∈ closure (relint L)) :
    (relint K ∩ relint L).Nonempty := by
  obtain ⟨p, hp, rfl⟩ := hqK
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hqL ε hε
  have hyspan : y ∈ affineSpan ℝ K := by
    rw [hspan]
    exact subset_affineSpan ℝ L (intrinsicInterior_subset hy)
  refine ⟨y, ⟨⟨y, hyspan⟩, hball ?_, rfl⟩, hy⟩
  change dist y (p : E d) < ε
  simpa only [dist_comm] using hdist

/-- Step 5 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"Each selected owner C lists q (as q is a vertex of its polygon ... and
a vertex of a cell of C is a vertex of C)." The two boundary trace edges
at a site exclude a selected polygon filling a whole half-disc at q. -/
private theorem site_fan_finite_step5_listed {A : S.ι} {F : FacetFlag S A}
    {r : ℕ} (q : E d) (hq : IsSite A F r q) (a : TracePiece A F r)
    (ha : q ∈ a.carrier) : a.tile.Lists 0 q := by
  obtain ⟨left, right, K, L, hne, hleft, hright, hbetween, hancestor⟩ := hq.2.2
  have hl : left.tile.Lists 0 q := by
    obtain ⟨e, he, hK, hsub, hflag, hqK, hl⟩ := hleft
    exact hl
  have hr : right.tile.Lists 0 q := by
    obtain ⟨e, he, hL, hsub, hflag, hqL, hr⟩ := hright
    exact hr
  by_cases h : a.owner = left.owner
  · simpa [TracePiece.tile, h] using hl
  by_cases h' : a.owner = right.owner
  · simpa [TracePiece.tile, h'] using hr
  by_contra hn
  obtain ⟨e, he, hqe, hflage, hsube⟩ :=
    site_fan_finite_step5_listed_step5_minimal_edge a q ha (intrinsicInterior_subset hq.1) hn
  obtain ⟨ae, hae⟩ := site_fan_finite_step5_listed_step6_extend_edge a e he hsube hflage
  obtain ⟨f, hf, rfl, hsubf, hflagf, hqf, _⟩ := hleft
  have hsubf' : f.val.carrier ⊆ left.bottom.val.carrier :=
    (Set.image_subset_image_iff (left.tile.prototypeFrame 0).injective).mp hsubf
  obtain ⟨bf, hbf⟩ := site_fan_finite_step5_listed_step6_extend_edge left f hf hsubf' hflagf
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hd := site_fan_finite_step5_listed_step4_edge_chains_disjoint r R
    (show S.IsStandardNode A r r R from ⟨0, by omega, (), rfl⟩)
    a.owner left.owner h a.tile left.tile
    (by simp [R, FramedNode.move, TracePiece.tile])
    (by simp [R, FramedNode.move, TracePiece.tile]) ae bf
  rw [hae, hbf] at hd
  have hspan := (site_fan_finite_step5_listed_step7_edge_span a.tile e he hflage).trans
    (site_fan_finite_step5_listed_step7_edge_span left.tile f hf hflagf).symm
  obtain ⟨p, hpe, hpf⟩ := site_fan_finite_step5_listed_step7_overlap hspan hqe
    (show q ∈ closure (relint (left.tile.cell 0 f.val)) by
      rwa [(site_fan_finite_step5_listed_step1_native_relint left.tile f.val).2])
  exact Set.disjoint_left.mp hd hpe hpf

/-- Step 6 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"The chains ... have direction spaces equal to those of F₂ ... F_{d-1}."
Containment and equality of dimensions give equality of direction spaces;
the ambient expansion need not be a similarity. -/
private theorem site_fan_finite_step6_chain_directions {A : S.ι}
    {F : FacetFlag S A} {r : ℕ} (a : TracePiece A F r)
    (i : ChainIndex d (traceDimension d)) :
    cellDirection (a.tile.cell 0 (a.chain.cell i).val) =
      cellDirection ((S.σ ^ r) ''
        (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier) := by
  have hdim (g : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
      Module.finrank ℝ (cellDirection (g '' K)) =
        Module.finrank ℝ (cellDirection K) := by
    change Module.finrank ℝ (affineSpan ℝ (g.toAffineMap '' K)).direction = _
    rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
    exact LinearEquiv.finrank_map_eq g.linear (cellDirection K)
  have hle : cellDirection (a.tile.cell 0 (a.chain.cell i).val) ≤
      cellDirection ((S.σ ^ r) ''
        (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier) := by
    simpa only [cellDirection, direction_affineSpan] using
      vectorSpan_mono ℝ (a.chain.contained i)
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hleft : Module.finrank ℝ (cellDirection
      (a.tile.cell 0 (a.chain.cell i).val)) = i.val.val := by
    rw [site_fan_finite_step4_cell_zero]
    exact (hdim a.tile.frame.toAffineEquiv _).trans
      ((a.chain.cell i).val.flat.dimension.trans (a.chain.dimension i))
  have hright : Module.finrank ℝ (cellDirection ((S.σ ^ r) ''
      (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier)) = i.val.val :=
    (hdim (S.σ ^ r).toAffineEquiv _).trans
      ((F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.flat.dimension.trans
        (F.dimension ⟨i.val.val, i.property.2, i.val.isLt⟩))
  exact hleft.trans hright.symm

/-- Step 1 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.23(b)):
"the polygons ... meeting q". A positive-dimensional connected cell has
points other than q in every neighborhood of q. -/
private theorem site_fan_finite_step6_connected_step1_accumulation
    (c : Cell d) (hc : 0 < c.dim) (g : Iso d) (q : E d)
    (hq : q ∈ g '' c.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ g '' c.carrier, x ∈ ball q ε ∧ x ≠ q := by
  have hn : c.carrier.Nontrivial := by
    apply Set.not_subsingleton_iff.mp
    intro hs
    have hz : cellDirection c.carrier = ⊥ := by
      simpa [cellDirection, direction_affineSpan] using
        (vectorSpan_eq_bot_iff_subsingleton ℝ).mpr hs
    have hzero : Module.finrank ℝ (cellDirection c.carrier) = 0 := by
      rw [hz]
      exact finrank_bot ℝ (E d)
    have hh := c.flat.dimension
    omega
  have hn' : (g '' c.carrier).Nontrivial := hn.image g.injective
  have hp := (c.flat.connected.image g g.continuous.continuousOn).isPreconnected
    |>.preperfect_of_nontrivial hn'
  obtain ⟨x, hx, hne⟩ := preperfect_iff_nhds.mp hp q hq (ball q ε) (ball_mem_nhds q hε)
  exact ⟨x, hx.2, hx.1, hne⟩

/-- Step 2 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.23(b)):
"the polygons ... meeting q". A small common ball misses every member of a
finite closed family that does not contain q. -/
private theorem site_fan_finite_step6_connected_step2_common_ball
    {ι : Type*} [Finite ι] (K : ι → Set (E d))
    (hK : ∀ i, IsClosed (K i)) (q : E d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i x, x ∈ ball q ε → x ∈ K i → q ∈ K i := by
  let U : Set (E d) := ⋂ i : {i // q ∉ K i}, (K i.val)ᶜ
  have hU : IsOpen U := isOpen_iInter_of_finite fun i => (hK i.val).isOpen_compl
  have hqU : q ∈ U := by simp [U]
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hU q hqU
  refine ⟨ε, hε, ?_⟩
  intro i x hx hxi
  by_contra hqi
  exact (Set.mem_iInter.mp (hb hx) ⟨i, hqi⟩) hxi

/-- Step 3 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.0(a)):
"each component is inside or outside A". On a connected set on which boundary
membership is constant, membership in a closed set is constant as well. -/
private lemma site_fan_finite_step6_connected_step3_connected_membership
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

/-- Step 3 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.0(b)):
"the local structure is constant by (a) applied to the cell complex". Translation
invariance of the relative boundary of a closed set extends to the set itself,
provided the translations are parallel to its affine span. -/
private lemma site_fan_finite_step6_connected_step3_fill
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
    have heq := site_fan_finite_step6_connected_step3_connected_membership
      (hS.preimage continuous_subtype_val)
      (isPreconnected_Icc.image γ hγcont.continuousOn) hinv
      (mem_image_of_mem γ (left_mem_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)))
      (mem_image_of_mem γ (right_mem_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)))
    simpa [γ] using heq.mp (by simpa [γ] using hxs)
  intro x hx y hy hyx
  exact ⟨hforward x hx y hy hyx,
    hforward y hy x hx (by simpa only [neg_sub] using V.neg_mem hyx)⟩

/-- Step 3 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.0(a)):
"if p ∈ e ... then mc_A(p) ⊆ e". A listed cell meeting the relative interior
of another listed cell contains the whole latter cell. -/
private lemma site_fan_finite_step6_connected_step3_incidence
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

/-- Step 3 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.0(a)):
"Cells are closed and finitely many, so some ball U ...". Finitely many local
translation invariances hold on a common ball, including for an empty family. -/
private lemma site_fan_finite_step6_connected_step3_invariance_ball
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

/-- Step 3 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.0(b)):
"the local structure is constant by (a) applied to the cell complex". Induction
through relative boundaries makes every listed carrier locally invariant in the
directions of the cell containing the base point in its relative interior. -/
private lemma site_fan_finite_step6_connected_step3_cell_invariance
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
      · have hef := site_fan_finite_step6_connected_step3_incidence K he hf hp hpf
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
        obtain ⟨r, hr, hc⟩ := site_fan_finite_step6_connected_step3_invariance_ball b
          Cell.carrier (cellDirection e.carrier) p (fun g hg =>
            ih (N g) (by simpa only [hN] using hsmall g hg) g (hb hg) rfl)
        refine ⟨r, hr, site_fan_finite_step6_connected_step3_fill f.flat.compact.isClosed
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

/-- Step 3 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.23(b)):
"at native scale". Relative interiors commute with invertible affine placements. -/
private theorem site_fan_finite_step6_connected_step3_relint_image
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

/-- Step 3 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.23(b)):
"the polygons ... form a finite planar fan". A polyhedron is locally
star convex at each of its points, by discarding convex pieces missing the point. -/
private theorem site_fan_finite_step6_connected_step3_local_star
    {K : Set (E d)} (hK : Polyhedron K) (q : E d) :
    ∃ ε : ℝ, 0 < ε ∧ StarConvex ℝ q (K ∩ ball q ε) := by
  classical
  obtain ⟨s, rfl⟩ := hK
  obtain ⟨ε, hε, hnear⟩ := site_fan_finite_step6_connected_step2_common_ball
    (fun p : s => convexHull ℝ (p.val : Set (E d)))
    (fun p => p.val.finite_toSet.isCompact_convexHull.isClosed) q
  refine ⟨ε, hε, ?_⟩
  intro x hx a b ha hb hab
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx.1
  have hqp := hnear ⟨p, hp⟩ x hx.2 hxp
  exact ⟨Set.mem_iUnion₂.mpr ⟨p, hp,
    (convex_convexHull ℝ (p : Set (E d))) hqp hxp ha hb hab⟩,
    (convex_ball q ε) (mem_ball_self hε) hx.2 ha hb hab⟩

/-- Step 3 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.23(b)):
"near a point of relint h ... a half-plane". Relative interior contains
a small ball in the affine span. -/
private theorem site_fan_finite_step6_connected_step3_relint_ball
    {K : Set (E d)} {q : E d} (hq : q ∈ relint K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ ball q ε,
      x ∈ affineSpan ℝ K → x ∈ relint K := by
  obtain ⟨p, hp, hpq⟩ := hq
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  refine ⟨ε, hε, ?_⟩
  intro x hx hxaff
  refine ⟨⟨x, hxaff⟩, hb ?_, rfl⟩
  simpa only [mem_ball, Subtype.dist_eq, hpq] using hx

/-- Step 3 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.23(b)):
"the polygons ... form a finite planar fan". Local radial segments and translation along
an edge connect the punctured neighborhood through a point off the edge line. -/
private theorem site_fan_finite_step6_connected_step3_punctured_star
    (K : Set (E d)) (V : Submodule ℝ (E d)) (q : E d) (ε : ℝ)
    (hstar : StarConvex ℝ q (K ∩ ball q ε))
    (hinv : ∀ x ∈ ball q ε, ∀ y ∈ ball q ε, y - x ∈ V → (x ∈ K ↔ y ∈ K))
    (u w : E d) (hu : u ∈ ball q ε) (huV : u - q ∈ V) (huq : u ≠ q)
    (hw : w ∈ K ∩ ball q ε) (hwV : w - q ∉ V) :
    IsPreconnected ((K ∩ ball q ε) \ {q}) := by
  let U := (K ∩ ball q ε) \ {q}
  have hjoin (v z : E d) (hv : v ∈ ball q ε) (hvV : v - q ∈ V) (hvq : v ≠ q)
      (hz : z ∈ K ∩ ball q ε) (hzV : z - q ∉ V) : JoinedIn U v z := by
    apply JoinedIn.of_segment_subset
    rintro y ⟨a, b, ha, hb, hab, rfl⟩
    have hrad := hstar hz ha hb hab
    have hball := (convex_ball q ε) hv hz.2 ha hb hab
    have hshift : (a • v + b • z) - (a • q + b • z) ∈ V := by
      convert V.smul_mem a hvV using 1 <;> module
    refine ⟨⟨(hinv _ hrad.2 _ hball hshift).mp hrad.1, hball⟩, ?_⟩
    change a • v + b • z ≠ q
    intro heq
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      exact hvq (by simpa [ha1, hb0] using heq)
    · apply hzV
      have hzmem : b • (z - q) ∈ V := by
        have hid : b • (z - q) = -(a • (v - q)) := by
          calc
            _ = (a • v + b • z - q) - a • (v - q) := by
              rw [show a = 1 - b by linarith]
              module
            _ = _ := by rw [heq, sub_self, zero_sub]
        rw [hid]
        exact V.neg_mem (V.smul_mem a hvV)
      simpa [smul_smul, hb0] using V.smul_mem b⁻¹ hzmem
  have hwq : w ≠ q := by intro h; exact hwV (by simp [h])
  have hpath : IsPathConnected U := by
    refine ⟨w, ⟨hw, hwq⟩, ?_⟩
    intro x hx
    by_cases hxV : x - q ∈ V
    · exact (hjoin x w hx.1.2 hxV hx.2 hw hwV).symm
    · exact (hjoin u w hu huV huq hw hwV).symm.trans
        (hjoin u x hu huV huq hx.1 hxV)
  exact hpath.isConnected.isPreconnected

set_option maxHeartbeats 800000 in
/-- Step 3 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.23(b), 1.0(a)):
"the polygons ... form a finite planar fan".
At a relative-interior edge point of a listed polygon, radial segments and
local translation along the edge give connected punctured neighborhoods,
also after an invertible affine placement. -/
private theorem site_fan_finite_step6_connected_step3_punctured_polygon
    {P : PolyManifoldDomain d} (K : CellComplex P) (c e : Cell d)
    (hc : c ∈ K.cells) (he : e ∈ K.cells) (hc2 : c.dim = 2) (he1 : e.dim = 1)
    (hec : e.carrier ⊆ c.carrier) (g : E d ≃ᵃ[ℝ] E d)
    (q : E d) (hq : q ∈ relint (g '' e.carrier)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧
      IsPreconnected ((g '' c.carrier ∩ ball q ε) \ {q}) := by
  rw [site_fan_finite_step6_connected_step3_relint_image] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  have hpe : p ∈ e.carrier := intrinsicInterior_subset hp
  have hpc : p ∈ c.carrier := hec hpe
  let V := cellDirection e.carrier
  let W := V.map g.linear.toLinearMap
  obtain ⟨ri, hri, hinv⟩ :=
    site_fan_finite_step6_connected_step3_cell_invariance K e he p hp c hc
  obtain ⟨rs, hrs, hstar⟩ :=
    site_fan_finite_step6_connected_step3_local_star c.flat.polyhedral p
  have hpre : IsOpen (g.symm ⁻¹' ball p (min ri rs)) :=
    isOpen_ball.preimage g.symm.toHomeomorphOfFiniteDimensional.continuous
  have hgp : g p ∈ g.symm ⁻¹' ball p (min ri rs) := by
    simp only [Set.mem_preimage, g.symm_apply_apply]
    exact mem_ball_self (lt_min hri hrs)
  obtain ⟨r, hr, hmap⟩ := Metric.isOpen_iff.mp hpre (g p) hgp
  let ε := min r δ
  have hε : 0 < ε := lt_min hr hδ
  have hmap' (x : E d) (hx : x ∈ ball (g p) ε) :
      g.symm x ∈ ball p ri ∧ g.symm x ∈ ball p rs := by
    have hh := hmap (ball_subset_ball (min_le_left r δ) hx)
    exact ⟨ball_subset_ball (min_le_left ri rs) hh,
      ball_subset_ball (min_le_right ri rs) hh⟩
  have hinv' : ∀ x ∈ ball (g p) ε, ∀ y ∈ ball (g p) ε,
      y - x ∈ W → (x ∈ g '' c.carrier ↔ y ∈ g '' c.carrier) := by
    intro x hx y hy hxy
    have hxy' : g.symm y - g.symm x ∈ V := by
      obtain ⟨v, hv, hveq⟩ := hxy
      have hl : g.linear (g.symm y - g.symm x) = y - x := by
        simpa using g.toAffineMap.linearMap_vsub (g.symm y) (g.symm x)
      have hv' : v = g.symm y - g.symm x :=
        g.linear.injective (hveq.trans hl.symm)
      simpa only [hv'] using hv
    change (x ∈ g.toEquiv '' c.carrier ↔ y ∈ g.toEquiv '' c.carrier)
    simpa only [Set.mem_image_equiv] using
      hinv (g.symm x) (hmap' x hx).1 (g.symm y) (hmap' y hy).1 hxy'
  have hstar' : StarConvex ℝ (g p) (g '' c.carrier ∩ ball (g p) ε) := by
    have hh := (hstar.affine_image g.toAffineMap).inter
      ((convex_ball (g p) ε) (mem_ball_self hε))
    have hset : (g '' (c.carrier ∩ ball p rs)) ∩ ball (g p) ε =
        g '' c.carrier ∩ ball (g p) ε := by
      ext x
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hx⟩
        exact ⟨⟨z, hz.1, rfl⟩, hx⟩
      · rintro ⟨⟨z, hz, hzx⟩, hx⟩
        refine ⟨⟨z, ⟨hz, ?_⟩, hzx⟩, hx⟩
        simpa only [← hzx, g.symm_apply_apply] using (hmap' x hx).2
    change StarConvex ℝ (g p) ((g '' (c.carrier ∩ ball p rs)) ∩ ball (g p) ε) at hh
    rwa [hset] at hh
  obtain ⟨re, hre, hedge⟩ := site_fan_finite_step6_connected_step3_relint_ball (K := e.carrier) (q := p) hp
  have hopen : IsOpen (g ⁻¹' ball (g p) ε) :=
    isOpen_ball.preimage g.toHomeomorphOfFiniteDimensional.continuous
  have hpopen : p ∈ g ⁻¹' ball (g p) ε := by
    change dist (g p) (g p) < ε
    simpa only [dist_self] using hε
  obtain ⟨t, ht, htmap⟩ := Metric.isOpen_iff.mp hopen p hpopen
  let s := min t re
  have hs : 0 < s := lt_min ht hre
  have hmapball (z : E d) (hz : z ∈ ball p s) : g z ∈ ball (g p) ε :=
    htmap (ball_subset_ball (min_le_left t re) hz)
  obtain ⟨u, hue, hu, hup⟩ := site_fan_finite_step6_connected_step1_accumulation
    e (by omega) (AffineIsometryEquiv.refl ℝ (E d)) p (by simpa using hpe) hs
  have hue' : u ∈ e.carrier := by simpa using hue
  have huV : u - p ∈ V := AffineSubspace.vsub_mem_direction
    (subset_affineSpan ℝ _ hue') (subset_affineSpan ℝ _ hpe)
  have hguW : g u - g p ∈ W := by
    have hlin : g.linear (u - p) = g u - g p := g.toAffineMap.linearMap_vsub u p
    rw [← hlin]
    exact Submodule.mem_map_of_mem huV
  have hpcl : p ∈ closure (relint c.carrier) := by
    rw [c.flat.regularClosed]
    exact hpc
  obtain ⟨w, hwc, hwp⟩ := Metric.mem_closure_iff.mp hpcl s hs
  have hw : w ∈ ball p s := by simpa only [mem_ball, dist_comm] using hwp
  have hwV : w - p ∉ V := by
    intro hwpV
    have hwspan : w ∈ affineSpan ℝ e.carrier := by
      simpa using AffineSubspace.vadd_mem_of_mem_direction hwpV
        (subset_affineSpan ℝ _ hpe)
    have hwe := hedge w (ball_subset_ball (min_le_right t re) hw) hwspan
    have hec' : e ≠ c := by intro h; have := congrArg Cell.dim h; omega
    exact Set.disjoint_left.mp (K.relint_disjoint e he c hc hec') hwe hwc
  have hgwW : g w - g p ∉ W := by
    rintro ⟨v, hv, hveq⟩
    have hv' : v = w - p := g.linear.injective (hveq.trans (g.toAffineMap.linearMap_vsub w p).symm)
    exact hwV (by simpa only [hv'] using hv)
  refine ⟨ε, hε, min_le_right r δ, ?_⟩
  exact site_fan_finite_step6_connected_step3_punctured_star
    (g '' c.carrier) W (g p) ε hstar' hinv' (g u) (g w)
    (hmapball u hu) hguW (g.injective.ne hup)
    ⟨⟨w, intrinsicInterior_subset hwc, rfl⟩, hmapball w hw⟩ hgwW

/-- Step 4 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.23(b)):
"the polygons ... form a finite planar fan". In one affine plane, disjoint
relative interiors keep either polygon's carrier out of the other's interior. -/
private theorem site_fan_finite_step6_connected_step4_disjoint_interior
    {K L : Set (E d)} (hspan : affineSpan ℝ K = affineSpan ℝ L)
    (hL : closure (relint L) = L) (hdis : Disjoint (relint K) (relint L)) :
    Disjoint (relint K) L := by
  let V := affineSpan ℝ K
  have himage : ((↑) : V → E d) '' (((↑) : V → E d) ⁻¹' relint L) = relint L := by
    apply Set.image_preimage_eq_of_subset
    intro x hx
    have hxV : x ∈ V := by
      change x ∈ affineSpan ℝ K
      rw [hspan]
      exact subset_affineSpan ℝ L (intrinsicInterior_subset hx)
    exact ⟨⟨x, hxV⟩, rfl⟩
  have hd : Disjoint (interior (((↑) : V → E d) ⁻¹' K))
      (((↑) : V → E d) ⁻¹' relint L) := by
    apply Set.disjoint_left.mpr
    intro x hxK hxL
    exact Set.disjoint_left.mp hdis ⟨x, hxK, rfl⟩ hxL
  apply Set.disjoint_left.mpr
  rintro x ⟨y, hy, rfl⟩ hxL
  have hyL : y ∈ closure (((↑) : V → E d) ⁻¹' relint L) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, himage, hL]
    exact hxL
  exact Set.disjoint_left.mp (hd.closure_right isOpen_interior) hy hyL

/-- Step 5 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.23(b)):
"Consecutive sectors share an edge line". At a boundary point of a listed
polygon, its minimal cell is an edge if that cell also contains a second point. -/
private theorem site_fan_finite_step6_connected_step5_boundary_edge
    {P : PolyManifoldDomain d} (K : CellComplex P) (c : Cell d)
    (hc : c ∈ K.cells) (hdim : c.dim = 2) (x q : E d) (hxq : x ≠ q)
    (hx : x ∈ c.carrier) (hxi : x ∉ relint c.carrier)
    (hnear : ∀ e ∈ K.cells, x ∈ e.carrier → q ∈ e.carrier) :
    ∃ e ∈ K.cells, e.dim = 1 ∧ x ∈ e.carrier ∧ q ∈ e.carrier ∧
      e.carrier ⊆ c.carrier := by
  have hxP : x ∈ frontier P.carrier := by
    rw [← K.carriers_cover]
    exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, hx⟩⟩
  let e := K.minimalCell x hxP
  have he : e ∈ K.cells := K.minimalCell_mem x hxP
  have hxe : x ∈ relint e.carrier := K.mem_relint_minimalCell x hxP
  have hxem : x ∈ e.carrier := intrinsicInterior_subset hxe
  have hqe : q ∈ e.carrier := hnear e he hxem
  have hec : e.carrier ⊆ c.carrier := K.minimalCell_subset x hxP c hc hx
  have hdir : cellDirection e.carrier ≤ cellDirection c.carrier :=
    AffineSubspace.direction_le (affineSpan_mono ℝ hec)
  have hle : e.dim ≤ 2 := by
    have hh := Submodule.finrank_mono hdir
    rwa [e.flat.dimension, c.flat.dimension, hdim] at hh
  have hne0 : e.dim ≠ 0 := by
    intro he0
    have hz : cellDirection e.carrier = ⊥ :=
      Submodule.finrank_eq_zero.mp (e.flat.dimension.trans he0)
    have hs : e.carrier.Subsingleton :=
      (vectorSpan_eq_bot_iff_subsingleton ℝ).mp (by
        simpa [cellDirection, direction_affineSpan] using hz)
    exact hxq (hs hxem hqe)
  have hne2 : e.dim ≠ 2 := by
    intro he2
    have heq : cellDirection e.carrier = cellDirection c.carrier :=
      Submodule.eq_of_le_of_finrank_eq hdir (by
        rw [e.flat.dimension, c.flat.dimension, he2, hdim])
    have hspan : affineSpan ℝ e.carrier = affineSpan ℝ c.carrier :=
      AffineSubspace.eq_of_direction_eq_of_nonempty_of_le heq
        ⟨x, subset_affineSpan ℝ _ hxem⟩ (affineSpan_mono ℝ hec)
    have hrel : relint e.carrier ⊆ relint c.carrier := by
      unfold relint intrinsicInterior
      rw [hspan]
      exact Set.image_mono (interior_mono (Set.preimage_mono hec))
    exact hxi (hrel hxe)
  exact ⟨e, he, by omega, hxem, hqe, hec⟩

/-- Step 6 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.23(b)):
"Consecutive sectors share an edge line". Two one-dimensional carriers
containing the same two distinct points have equal direction spaces. -/
private theorem site_fan_finite_step6_connected_step6_edge_line
    {K L : Set (E d)} (hK : Module.finrank ℝ (cellDirection K) = 1)
    (hL : Module.finrank ℝ (cellDirection L) = 1)
    {x q : E d} (hxq : x ≠ q) (hxK : x ∈ K) (hqK : q ∈ K)
    (hxL : x ∈ L) (hqL : q ∈ L) : cellDirection K = cellDirection L := by
  have hv : x - q ≠ 0 := sub_ne_zero.mpr hxq
  have hdK : x - q ∈ cellDirection K :=
    AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K hxK)
      (subset_affineSpan ℝ K hqK)
  have hdL : x - q ∈ cellDirection L :=
    AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ L hxL)
      (subset_affineSpan ℝ L hqL)
  have hspanK : ℝ ∙ (x - q) = cellDirection K :=
    Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hdK)
      ((finrank_span_singleton hv).trans hK.symm)
  have hspanL : ℝ ∙ (x - q) = cellDirection L :=
    Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hdL)
      ((finrank_span_singleton hv).trans hL.symm)
  exact hspanK.symm.trans hspanL

/-- Step 7 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.23(b)):
"The chains ... have direction spaces equal". Appending a named edge of
the bottom polygon extends its recorded coface chain to a full flag. -/
private theorem site_fan_finite_step6_connected_step7_extend_flag
    {A : S.ι} {F : FacetFlag S A} {r : ℕ} (hd : traceDimension d = 2)
    (a : TracePiece A F r) (e : CellName S a.tile.ty) (he : e.val.dim = 1)
    (hsub : e.val.carrier ⊆ a.bottom.val.carrier) :
    ∃ G : FacetFlag S a.tile.ty,
      (∀ i, i.val = 1 → G.cell i = e) ∧
      ∀ (i : {j : ℕ // 1 ≤ j ∧ j < d}) (hi : traceDimension d ≤ i.val),
        G.cell i = a.chain.cell ⟨⟨i.val, i.property.2⟩, hi, i.property.1⟩ := by
  let idx (i : {j : ℕ // 1 ≤ j ∧ j < d}) (hi : i.val ≠ 1) :
      ChainIndex d (traceDimension d) :=
    ⟨⟨i.val, i.property.2⟩, by change traceDimension d ≤ i.val; have := i.property.1; omega, i.property.1⟩
  let G : FacetFlag S a.tile.ty :=
    { cell := fun i => if hi : i.val = 1 then e else a.chain.cell (idx i hi)
      dimension := by
        intro i
        split_ifs with hi
        · exact he.trans hi.symm
        · exact a.chain.dimension (idx i hi)
      nested := by
        intro i j hij
        split_ifs with hi hj hj
        · exact Set.Subset.refl _
        · exact hsub.trans (a.chain.nested TracePiece.bottomIndex (idx j hj)
            (by have := j.property.1; change traceDimension d ≤ j.val; omega))
        · have := i.property.1
          omega
        · exact a.chain.nested (idx i hi) (idx j hj) hij }
  refine ⟨G, ?_, ?_⟩
  · intro i hi
    simp [G, hi]
  · intro i hi
    have hi' : i.val ≠ 1 := by omega
    simp [G, hi', idx]

/-- Step 8 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.23(b)):
"Consecutive sectors share an edge line". Away from the site, an overlap
in a ball avoiding nonincident cells gives a common edge direction, which
completes both recorded coface chains to aligned full flags. -/
private theorem site_fan_finite_step6_connected_step8_overlap_flags
    {A : S.ι} {F : FacetFlag S A} {r : ℕ} (hd : traceDimension d = 2)
    (a b : TracePiece A F r) (hab : a ≠ b) (x q : E d) (hxq : x ≠ q)
    (hxa : x ∈ a.carrier) (hxb : x ∈ b.carrier)
    (hnear : ∀ (c : TracePiece A F r) (e : CellName S c.tile.ty),
      x ∈ c.tile.cell 0 e.val → q ∈ c.tile.cell 0 e.val) :
    siteFanAligned a.tile b.tile := by
  have hreg (c : TracePiece A F r) : closure (relint c.carrier) = c.carrier := by
    change closure (relint (c.tile.cell 0 c.bottom.val)) = c.tile.cell 0 c.bottom.val
    rw [site_fan_finite_step4_cell_zero]
    change closure (intrinsicInterior ℝ (c.tile.frame.toAffineIsometry ''
      c.bottom.val.carrier)) = _
    rw [AffineIsometry.image_intrinsicInterior]
    change closure (c.tile.frame.toHomeomorph '' relint c.bottom.val.carrier) = _
    rw [← c.tile.frame.toHomeomorph.image_closure, c.bottom.val.flat.regularClosed]
    rfl
  have hspan : affineSpan ℝ a.carrier = affineSpan ℝ b.carrier :=
    ((recursiveTrace_tiles A F r).2.2 a TracePiece.bottomIndex).trans
      ((recursiveTrace_tiles A F r).2.2 b TracePiece.bottomIndex).symm
  have hdis := (recursiveTrace_tiles A F r).2.1 hab
  have hna : x ∉ relint a.carrier := fun hx =>
    Set.disjoint_left.mp
      (site_fan_finite_step6_connected_step4_disjoint_interior hspan (hreg b) hdis) hx hxb
  have hnb : x ∉ relint b.carrier := fun hx =>
    Set.disjoint_left.mp
      (site_fan_finite_step6_connected_step4_disjoint_interior hspan.symm (hreg a) hdis.symm)
      hx hxa
  have hedge (c : TracePiece A F r) (hxc : x ∈ c.carrier)
      (hnc : x ∉ relint c.carrier) :
      ∃ e : CellName S c.tile.ty, e.val.dim = 1 ∧
        x ∈ c.tile.cell 0 e.val ∧ q ∈ c.tile.cell 0 e.val ∧
        e.val.carrier ⊆ c.bottom.val.carrier := by
    have hxc' : c.tile.frame.symm x ∈ c.bottom.val.carrier := by
      obtain ⟨y, hy, hxy⟩ := (show x ∈ c.tile.frame '' c.bottom.val.carrier by
        simpa [TracePiece.carrier, site_fan_finite_step4_cell_zero] using hxc)
      simpa [← hxy] using hy
    have hnc' : c.tile.frame.symm x ∉ relint c.bottom.val.carrier := by
      intro hi
      apply hnc
      change x ∈ intrinsicInterior ℝ (c.tile.cell 0 c.bottom.val)
      rw [site_fan_finite_step4_cell_zero]
      change x ∈ intrinsicInterior ℝ (c.tile.frame.toAffineIsometry '' c.bottom.val.carrier)
      rw [AffineIsometry.image_intrinsicInterior]
      exact ⟨c.tile.frame.symm x, hi, c.tile.frame.apply_symm_apply x⟩
    obtain ⟨e, he, he1, hxe, hqe, hec⟩ :=
      site_fan_finite_step6_connected_step5_boundary_edge (S.cx c.tile.ty)
        c.bottom.val c.bottom.property ((c.chain.dimension TracePiece.bottomIndex).trans hd)
        (c.tile.frame.symm x) (c.tile.frame.symm q)
        (fun h => hxq (c.tile.frame.symm.injective h)) hxc' hnc' (by
          intro e he hxe
          have hqe := hnear c ⟨e, he⟩ (by
            rw [site_fan_finite_step4_cell_zero]
            exact ⟨c.tile.frame.symm x, hxe, c.tile.frame.apply_symm_apply x⟩)
          rw [site_fan_finite_step4_cell_zero] at hqe
          obtain ⟨z, hz, hqz⟩ := hqe
          simpa [← hqz] using hz)
    refine ⟨⟨e, he⟩, he1, ?_, ?_, hec⟩
    · rw [site_fan_finite_step4_cell_zero]
      exact ⟨c.tile.frame.symm x, hxe, c.tile.frame.apply_symm_apply x⟩
    · rw [site_fan_finite_step4_cell_zero]
      exact ⟨c.tile.frame.symm q, hqe, c.tile.frame.apply_symm_apply q⟩
  obtain ⟨e, he, hxe, hqe, hea⟩ := hedge a hxa hna
  obtain ⟨f, hf, hxf, hqf, hfb⟩ := hedge b hxb hnb
  have hdim (c : TracePiece A F r) (e : CellName S c.tile.ty) (he : e.val.dim = 1) :
      Module.finrank ℝ (cellDirection (c.tile.cell 0 e.val)) = 1 := by
    rw [site_fan_finite_step4_cell_zero, site_fan_finite_step3_direction_image]
    exact (LinearEquiv.finrank_map_eq c.tile.frame.linearIsometryEquiv.toLinearEquiv _).trans
      (e.val.flat.dimension.trans he)
  have hline := site_fan_finite_step6_connected_step6_edge_line
    (hdim a e he) (hdim b f hf) hxq hxe hqe hxf hqf
  obtain ⟨Fa, hFa1, hFa⟩ := site_fan_finite_step6_connected_step7_extend_flag hd a e he hea
  obtain ⟨Fb, hFb1, hFb⟩ := site_fan_finite_step6_connected_step7_extend_flag hd b f hf hfb
  refine ⟨Fa, Fb, ?_⟩
  intro i
  by_cases hi : i.val = 1
  · rw [hFa1 i hi, hFb1 i hi]
    exact hline
  · have hi' : traceDimension d ≤ i.val := by have := i.property.1; omega
    rw [hFa i hi', hFb i hi']
    exact (site_fan_finite_step6_chain_directions a _).trans
      (site_fan_finite_step6_chain_directions b _).symm

/-- Step 9 of the V4 proof of `site_fan_finite_step6_connected` (V4 1.23(b)):
"the polygons ... form a finite planar fan". A finite closed cover of a
preconnected set connects all members meeting that set by overlap transitions. -/
private theorem site_fan_finite_step6_connected_step9_closed_cover
    {X ι V : Type*} [TopologicalSpace X] [Finite ι]
    (G : SimpleGraph V) (f : ι → V) (K : ι → Set X) (U : Set X)
    (hU : IsPreconnected U) (hK : ∀ i, IsClosed (K i))
    (hcover : U ⊆ ⋃ i, K i)
    (hstep : ∀ i j x, x ∈ U → x ∈ K i → x ∈ K j → G.Reachable (f i) (f j))
    (a b : ι) (ha : (U ∩ K a).Nonempty) (hb : (U ∩ K b).Nonempty) :
    G.Reachable (f a) (f b) := by
  classical
  by_contra hnot
  let L : Set X := ⋃ i : {i // G.Reachable (f a) (f i)}, K i.val
  let R : Set X := ⋃ i : {i // ¬G.Reachable (f a) (f i)}, K i.val
  have hL : IsClosed L := isClosed_iUnion_of_finite fun i => hK i.val
  have hR : IsClosed R := isClosed_iUnion_of_finite fun i => hK i.val
  have hcov : U ⊆ L ∪ R := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
    by_cases hr : G.Reachable (f a) (f i)
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨i, hr⟩, hi⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i, hr⟩, hi⟩)
  have hUL : (U ∩ L).Nonempty := by
    obtain ⟨x, hxU, hxa⟩ := ha
    exact ⟨x, hxU, Set.mem_iUnion.mpr ⟨⟨a, .refl _⟩, hxa⟩⟩
  have hUR : (U ∩ R).Nonempty := by
    obtain ⟨x, hxU, hxb⟩ := hb
    exact ⟨x, hxU, Set.mem_iUnion.mpr ⟨⟨b, hnot⟩, hxb⟩⟩
  obtain ⟨x, hxU, hxL, hxR⟩ :=
    isPreconnected_closed_iff.mp hU L R hL hR hcov hUL hUR
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxL
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxR
  exact j.property (i.property.trans (hstep i.val j.val x hxU hxi hxj))

/-- Step 6 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"the polygons ... form a finite planar fan". Consecutive sectors share an
edge line, which extends their recorded coface chains to aligned full flags.
Thus all selected owners are connected by these full-flag transitions.
For `d = 2` the recorded chains already include the common edge line. -/
private theorem site_fan_finite_step6_connected {A : S.ι} {F : FacetFlag S A}
    {r : ℕ} (q : E d) (hq : IsSite A F r q) :
    ∀ C B : siteFanOwners (A := A) (F := F) (r := r) q,
      (siteFanGraph q).Reachable C B := by
  by_cases hd : traceDimension d = 1
  · intro C B
    by_cases hCB : C = B
    · subst B
      exact SimpleGraph.Reachable.refl C
    obtain ⟨a, ha, hCa⟩ := C.property
    obtain ⟨b, hb, hBb⟩ := B.property
    let idx : {j : ℕ // 1 ≤ j ∧ j < d} → ChainIndex d (traceDimension d) :=
      fun j => ⟨⟨j.val, j.property.2⟩, by simpa [hd] using j.property.1, j.property.1⟩
    let full : (a : TracePiece A F r) → FacetFlag S a.tile.ty := fun a =>
      { cell := fun j => a.chain.cell (idx j)
        dimension := fun j => a.chain.dimension (idx j)
        nested := fun i j hij => a.chain.nested (idx i) (idx j) hij }
    have hfull : siteFanAligned a.tile b.tile := by
      refine ⟨full a, full b, ?_⟩
      intro i
      exact (site_fan_finite_step6_chain_directions a (idx i)).trans
        (site_fan_finite_step6_chain_directions b (idx i)).symm
    exact SimpleGraph.Adj.reachable (show (siteFanGraph q).Adj C B from
      ⟨hCB, by simpa [hCa, hBb] using hfull⟩)
  · classical
    have hd2 : traceDimension d = 2 := by
      have hd0 : 2 ≤ d := Fact.out
      unfold traceDimension at hd ⊢
      omega
    letI : Finite (TracePiece A F r) := tracePieces_finite A F r
    intro C B
    obtain ⟨a, ha, hCa⟩ := C.property
    obtain ⟨b, hb, hBb⟩ := B.property
    obtain ⟨δ, hδ, hnear⟩ := site_fan_finite_step6_connected_step2_common_ball
      (fun z : Σ c : TracePiece A F r, CellName S c.tile.ty =>
        z.1.tile.cell 0 z.2.val)
      (by
        intro z
        change IsClosed (z.1.tile.cell 0 z.2.val)
        rw [site_fan_finite_step4_cell_zero]
        exact (z.2.val.flat.compact.image z.1.tile.frame.continuous).isClosed) q
    let i₁ : {j : ℕ // 1 ≤ j ∧ j < d} :=
      ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩
    let i₂ : {j : ℕ // 1 ≤ j ∧ j < d} :=
      ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩
    let root : Cell d := (F.cell i₂).val
    let K : Set (E d) := (S.σ ^ r) '' root.carrier
    obtain ⟨ε, hε, hεδ, hconn⟩ :=
      site_fan_finite_step6_connected_step3_punctured_polygon (S.cx A) root (F.cell i₁).val
        (F.cell i₂).property (F.cell i₁).property ((F.dimension i₂).trans hd2)
        (F.dimension i₁) (F.nested i₁ i₂ traceDimension_pos)
        (S.σ ^ r).toAffineEquiv q hq.1 δ hδ
    let I := {c : TracePiece A F r // q ∈ c.carrier}
    let owner : I → siteFanOwners (A := A) (F := F) (r := r) q :=
      fun c => ⟨c.val.tile, c.val, c.property, rfl⟩
    let U : Set (E d) := (K ∩ ball q ε) \ {q}
    have hcover : U ⊆ ⋃ c : I, c.val.carrier := by
      intro x hx
      have hxK : x ∈ (S.σ ^ r) ''
          (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.carrier := hx.1.1
      rw [← (recursiveTrace_tiles A F r).1] at hxK
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hxK
      have hqc : q ∈ c.carrier :=
        hnear ⟨c, c.bottom⟩ x (ball_subset_ball hεδ hx.1.2) hxc
      exact Set.mem_iUnion.mpr ⟨⟨c, hqc⟩, hxc⟩
    have hmeet (c : I) : (U ∩ c.val.carrier).Nonempty := by
      obtain ⟨x, hxc, hxε, hxq⟩ :=
        site_fan_finite_step6_connected_step1_accumulation c.val.bottom.val
          (by
            have hh := c.val.chain.dimension TracePiece.bottomIndex
            change c.val.bottom.val.dim = traceDimension d at hh
            rw [hh, hd2]
            norm_num)
          c.val.tile.frame q
          (by simpa [TracePiece.carrier, site_fan_finite_step4_cell_zero] using c.property) hε
      have hxc' : x ∈ c.val.carrier := by
        simpa [TracePiece.carrier, site_fan_finite_step4_cell_zero] using hxc
      exact ⟨x, ⟨⟨c.val.chain.contained TracePiece.bottomIndex hxc', hxε⟩, hxq⟩, hxc'⟩
    have hreach := site_fan_finite_step6_connected_step9_closed_cover
      (siteFanGraph q) owner (fun c : I => c.val.carrier) U hconn
      (by
        intro c
        change IsClosed (c.val.tile.cell 0 c.val.bottom.val)
        rw [site_fan_finite_step4_cell_zero]
        exact (c.val.bottom.val.flat.compact.image c.val.tile.frame.continuous).isClosed)
      hcover (by
        intro c e x hx hxc hxe
        by_cases hce : owner c = owner e
        · exact hce ▸ SimpleGraph.Reachable.refl _
        · have hce' : c.val ≠ e.val := by
            intro heq
            have hh : c = e := Subtype.ext heq
            exact hce (congrArg owner hh)
          apply SimpleGraph.Adj.reachable
          refine ⟨hce, ?_⟩
          exact site_fan_finite_step6_connected_step8_overlap_flags hd2 c.val e.val hce'
            x q hx.2 hxc hxe (fun c e he =>
              hnear ⟨c, e⟩ x (ball_subset_ball hεδ hx.1.2) he))
      (⟨a, ha⟩ : I) (⟨b, hb⟩ : I) (hmeet ⟨a, ha⟩) (hmeet ⟨b, hb⟩)
    have hownerA : owner ⟨a, ha⟩ = C := Subtype.ext hCa.symm
    have hownerB : owner ⟨b, hb⟩ = B := Subtype.ext hBb.symm
    simpa only [hownerA, hownerB] using hreach

/-- Step 7 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"owners of polygons ... meeting q". A selected trace cell is contained
in its native owner, so the native tile multiplicity bound applies. -/
private theorem site_fan_finite_step7_carrier_subset {A : S.ι} {F : FacetFlag S A}
    {r : ℕ} (a : TracePiece A F r) : a.carrier ⊆ a.tile.carrier 0 := by
  have he : relint a.bottom.val.carrier ⊆ frontier (S.proto a.tile.ty).carrier := by
    rw [← (S.cx a.tile.ty).cover]
    exact Set.subset_iUnion_of_subset a.bottom.val
      (Set.subset_iUnion_of_subset a.bottom.property (Set.Subset.refl _))
  have hsub : a.bottom.val.carrier ⊆ (S.proto a.tile.ty).carrier := by
    calc a.bottom.val.carrier = closure (relint a.bottom.val.carrier) :=
        a.bottom.val.flat.regularClosed.symm
      _ ⊆ closure (frontier (S.proto a.tile.ty).carrier) := closure_mono he
      _ = frontier (S.proto a.tile.ty).carrier := isClosed_frontier.closure_eq
      _ ⊆ closure (S.proto a.tile.ty).carrier := frontier_subset_closure
      _ = (S.proto a.tile.ty).carrier := (S.proto a.tile.ty).compact.isClosed.closure_eq
  simpa [TracePiece.carrier, site_fan_finite_step4_cell_zero,
    FramedNode.carrier, SubstSystem.supertile, placedSet] using
      Set.image_mono (f := a.tile.frame) hsub

/-- Step 7 of the V4 proof of `site_fan_finite` (V4 1.23(b), 1.0(c)):
"there are at most ... of them". The uniform native tile multiplicity
bound bounds the number of selected owners, even without a site hypothesis.
This supplies a bound on transition-word length without choosing angles. -/
private theorem site_fan_finite_step7_owner_bound (S : SubstSystem d) :
    ∃ M : ℕ, ∀ (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d),
      (siteFanOwners (A := A) (F := F) (r := r) q).Finite ∧
      Nat.card (siteFanOwners (A := A) (F := F) (r := r) q) ≤ M := by
  obtain ⟨β, hβ, hβfull, hangle, hbound⟩ := point_multiplicity_bound S.proto S.cx
  refine ⟨⌊fullSolidAngle d / β⌋₊, ?_⟩
  intro A F r q
  have hdisj : Pairwise (fun a b : S.RoleWord A r => Disjoint
      (interior (placedSet (S.nativeTile A r a).frame
        (S.proto (S.nativeTile A r a).ty).carrier))
      (interior (placedSet (S.nativeTile A r b).frame
        (S.proto (S.nativeTile A r b).ty).carrier))) := by
    simpa [FramedNode.carrier, SubstSystem.supertile] using S.native_disjoint A r
  obtain ⟨hfinite, hcard⟩ := hbound (S.RoleWord A r)
    (fun w => (S.nativeTile A r w).ty) (fun w => (S.nativeTile A r w).frame) hdisj q
  let I := {w : S.RoleWord A r | q ∈ placedSet (S.nativeTile A r w).frame
    (S.proto (S.nativeTile A r w).ty).carrier}
  have hsub : siteFanOwners (A := A) (F := F) (r := r) q ⊆
      S.nativeTile A r '' I := by
    rintro C ⟨a, ha, rfl⟩
    refine ⟨a.owner, ?_, rfl⟩
    have hc := site_fan_finite_step7_carrier_subset a ha
    simpa [I, TracePiece.tile, FramedNode.carrier, SubstSystem.supertile] using hc
  have hfimage : (S.nativeTile A r '' I).Finite := hfinite.image _
  refine ⟨hfimage.subset hsub, ?_⟩
  exact (Set.ncard_le_ncard hsub hfimage).trans ((Set.ncard_image_le hfinite).trans hcard)

/-- Products of at most `n` transitions, using composition in the order
of relative frames along a path. -/
private def siteFanProducts (D : Set (Iso d)) : ℕ → Set (Iso d)
  | 0 => {AffineIsometryEquiv.refl ℝ (E d)}
  | n + 1 => siteFanProducts D n ∪
      (fun gh : Iso d × Iso d => gh.1.trans gh.2) '' (siteFanProducts D n ×ˢ D)

/-- Step 8 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"their angle word is one of finitely many". Bounded words in the finite
alphabet of full-flag transitions have finitely many products. -/
private theorem site_fan_finite_step8_products (D : Set (Iso d)) (hD : D.Finite) :
    ∀ n, (siteFanProducts D n).Finite := by
  intro n
  induction n with
  | zero => exact Set.finite_singleton _
  | succ n ih => exact ih.union ((ih.prod hD).image _)

/-- Step 8 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"their angle word is one of finitely many". Increasing the permitted
length only enlarges the set of transition products. -/
private theorem site_fan_finite_step8_products_mono (D : Set (Iso d)) :
    Monotone (siteFanProducts D) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left

/-- Step 8 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"all relative placements ... lie in a finite set". Along a graph walk,
successive relative frames telescope to the relative frame of its endpoints. -/
private theorem site_fan_finite_step8_walk {α : Type} (G : SimpleGraph α)
    (f : α → Iso d) (D : Set (Iso d))
    (hstep : ∀ a b, G.Adj a b → (f b).trans (f a).symm ∈ D)
    {a b : α} (p : G.Walk a b) :
    (f b).trans (f a).symm ∈ siteFanProducts D p.length := by
  induction p with
  | nil => simp [siteFanProducts]
  | @cons a b c hab p ih =>
      apply Or.inr
      refine ⟨((f c).trans (f b).symm, (f b).trans (f a).symm),
        ⟨ih, hstep a b hab⟩, ?_⟩
      apply AffineIsometryEquiv.ext
      intro x
      simp

/-- Step 8 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"at most ... of them" bounds the word length. Erasing loops from a walk
gives a path shorter than the number of owners. -/
private theorem site_fan_finite_step8_reachable {α : Type} [Finite α]
    (G : SimpleGraph α) (f : α → Iso d) (D : Set (Iso d)) (M : ℕ)
    (hcard : Nat.card α ≤ M)
    (hstep : ∀ a b, G.Adj a b → (f b).trans (f a).symm ∈ D)
    {a b : α} (hreach : G.Reachable a b) :
    (f b).trans (f a).symm ∈ siteFanProducts D M := by
  classical
  letI := Fintype.ofFinite α
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hlen : p.length ≤ M := by
    have hh := hp.length_lt
    rw [Nat.card_eq_fintype_card] at hcard
    omega
  exact site_fan_finite_step8_products_mono D hlen
    (site_fan_finite_step8_walk G f D hstep p)

/-- Step 9 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"Hence all relative placements of the selected owners lie in a finite
set". Connect the owners, erase loops, and multiply their finitely many
possible full-flag transitions. -/
private theorem site_fan_finite_step9_frames (S : SubstSystem d) :
    ∃ K : Set (Iso d), K.Finite ∧
      ∀ (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d), IsSite A F r q →
      ∀ (anchor a : TracePiece A F r), q ∈ anchor.carrier → q ∈ a.carrier →
        a.tile.frame.trans anchor.tile.frame.symm ∈ K := by
  obtain ⟨D, hD, hstep⟩ := site_fan_finite_step4_transitions S
  obtain ⟨M, hM⟩ := site_fan_finite_step7_owner_bound S
  refine ⟨siteFanProducts D M, site_fan_finite_step8_products D hD M, ?_⟩
  intro A F r q hq anchor a hanchor ha
  let O := siteFanOwners (A := A) (F := F) (r := r) q
  letI : Finite O := (hM A F r q).1.to_subtype
  let C : O := ⟨anchor.tile, anchor, hanchor, rfl⟩
  let B : O := ⟨a.tile, a, ha, rfl⟩
  have hlisted : ∀ C : O, C.val.Lists 0 q := by
    rintro ⟨C, a, ha, rfl⟩
    exact site_fan_finite_step5_listed q hq a ha
  exact site_fan_finite_step8_reachable (siteFanGraph q)
    (fun C : O => C.val.frame) D M (hM A F r q).2
    (fun C B hCB => hstep B.val C.val q (hlisted B) (hlisted C)
      (by obtain ⟨F, G, hFG⟩ := hCB.2; exact ⟨G, F, fun i => (hFG i).symm⟩))
    (site_fan_finite_step6_connected q hq C B)

/-- Step 10 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"with their chains". Vertex names and every optional coface name range
over a finite alphabet from the finite prototype complexes. -/
private theorem site_fan_finite_step10_labels (S : SubstSystem d) :
    ∃ L : Set (Cell d × (Fin d → Option (Cell d))), L.Finite ∧
      ∀ (A : S.ι) (F : FacetFlag S A) (r : ℕ) (a : TracePiece A F r)
        (v : Cell d), v ∈ (S.cx a.tile.ty).vertices → (v, a.chainNames) ∈ L := by
  classical
  let C : Set (Cell d) := ⋃ A : S.ι, (S.cx A).cells
  have hC : C.Finite := Set.finite_iUnion (fun A => (S.cx A).cells.finite_toSet)
  let L : Set (Fin d → Option (Cell d)) :=
    {c | ∀ i, c i ∈ insert none (some '' C)}
  have hL : L.Finite := Set.Finite.pi' (fun _ => (hC.image some).insert none)
  refine ⟨C ×ˢ L, hC.prod hL, ?_⟩
  intro A F r a v hv
  constructor
  · exact Set.mem_iUnion.mpr ⟨a.tile.ty, (Finset.mem_filter.mp hv).1⟩
  · intro i
    change a.chainNames i ∈ insert none (some '' C)
    unfold TracePiece.chainNames
    split_ifs with hi
    · exact Set.mem_insert_of_mem _ ⟨(a.chain.cell ⟨i, hi⟩).val,
        Set.mem_iUnion.mpr ⟨a.tile.ty, (a.chain.cell ⟨i, hi⟩).property⟩, rfl⟩
    · exact Set.mem_insert _ _

/-- P18, V4 1.23(b): finitely many positioned selected-owner fan templates. -/
theorem site_fan_finite (S : SubstSystem d) : (siteTemplates S).Finite := by
  obtain ⟨K, hK, hframes⟩ := site_fan_finite_step9_frames S
  obtain ⟨L, hL, hlabels⟩ := site_fan_finite_step10_labels S
  let V := {p : E d | ∃ A : S.ι, ∃ v ∈ (S.cx A).vertices, p ∈ v.carrier}
  have hV : V.Finite := site_fan_finite_step1_vertices S
  let N : Set (FramedNode S) := (fun z : S.ι × Iso d => ⟨z.1, z.2⟩) '' (Set.univ ×ˢ K)
  have hN : N.Finite := (Set.finite_univ.prod hK).image _
  apply (hV.prod (hN.prod hL).powerset).subset
  rintro t ⟨A, F, r, q, anchor, hq, hanchor, rfl⟩
  constructor
  · exact site_fan_finite_step4_listed_coordinate anchor.tile q
      (site_fan_finite_step5_listed q hq anchor hanchor)
  · rintro z ⟨a, v, ha, hv, hqv, rfl⟩
    constructor
    · exact ⟨(a.tile.ty, a.tile.frame.trans anchor.tile.frame.symm),
        ⟨Set.mem_univ _, hframes A F r q hq anchor a hanchor ha⟩, rfl⟩
    · exact hlabels A F r a v hv

/-- Step 1 of the V4 proof of `site_fan_geometry` (V4 1.0(b), tangent cones of polyhedra):
"A is a polyhedron". A simplex, including a lower-dimensional one, is cut out by
finitely many affine inequalities, using coordinates of an extended affine basis. -/
private lemma site_fan_geometry_step1_simplex_halfspaces
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

/-- Step 2 of the V4 proof of `site_fan_geometry` (V4 1.0(b), tangent cones of polyhedra):
"A is a polyhedron". Carathéodory's theorem gives a finite union of simplices,
and hence a finite union of intersections of affine closed half-spaces. -/
private lemma site_fan_geometry_step2_halfspace_presentation
    {K : Set (E d)} (hK : Polyhedron K) :
    ∃ S : Finset (Finset (E d →ᵃ[ℝ] ℝ)),
      K = ⋃ q ∈ S, {x | ∀ f ∈ q, 0 ≤ f x} := by
  classical
  obtain ⟨s, rfl⟩ := hK
  have hrep (t : Finset (E d)) : ∃ q : Finset (E d →ᵃ[ℝ] ℝ),
      AffineIndependent ℝ ((↑) : t → E d) →
        convexHull ℝ (t : Set (E d)) = {x | ∀ f ∈ q, 0 ≤ f x} := by
    by_cases ht : AffineIndependent ℝ ((↑) : t → E d)
    · obtain ⟨q, hq⟩ := site_fan_geometry_step1_simplex_halfspaces t ht
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
/-- Step 3 of the V4 proof of `site_fan_geometry` (V4 1.0(b), tangent cones of polyhedra):
"its tangent cone at any point is a polyhedral cone". Near the base point,
inactive inequalities keep their sign and active inequalities become homogeneous. -/
private lemma site_fan_geometry_step3_local_cone
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

/-- Step 4 of the V4 proof of `site_fan_geometry` (V4 1.0(b), tangent cones of polyhedra):
"polyhedral cone". Homogeneous half-space inequalities are invariant under
multiplication by a positive scalar, as is a finite union of their intersections. -/
private lemma site_fan_geometry_step4_positive_scaling
    {C : Set (E d)} (hC : IsPolyhedralCone C) {r : ℝ} (hr : 0 < r) (v : E d) :
    r • v ∈ C ↔ v ∈ C := by
  obtain ⟨S, rfl⟩ := hC
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, map_smul, smul_eq_mul,
    mul_nonneg_iff_of_pos_left hr]

open scoped Topology in
/-- Step 5 of the V4 proof of `site_fan_geometry` (V4 1.0(b), tangent cones of polyhedra):
"its tangent cone at any point is a polyhedral cone". A local conical model
equals the positive-time radial germ in the definition of `tangentCone`. -/
private lemma site_fan_geometry_step5_radial_germ
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
    exact (site_fan_geometry_step4_positive_scaling hC ht v).mp
      ((hδloc hnear).mp (hv t ht htε))
  · intro hv
    refine ⟨δ, hδ, fun t ht htδ => ?_⟩
    have hnear : dist t 0 < δ := by simpa [Real.dist_eq, abs_of_pos ht] using htδ
    exact (hδloc hnear).mpr
      ((site_fan_geometry_step4_positive_scaling hC ht v).mpr hv)


open scoped Topology in
/-- Step 6 of the V4 proof of `site_fan_geometry` (V4 1.0(b)): "its tangent cone at any
point is a polyhedral cone" in the strong local form: near the base point a polyhedron
coincides with the translate of its own radial tangent cone. -/
private theorem site_fan_geometry_step6_local {K : Set (E d)} (hK : Polyhedron K) (p : E d) :
    ∀ᶠ x in 𝓝 p, x ∈ K ↔ x - p ∈ tangentCone K p := by
  obtain ⟨T, hT⟩ := site_fan_geometry_step2_halfspace_presentation hK
  obtain ⟨C, hC, hloc⟩ := site_fan_geometry_step3_local_cone T p
  rw [← hT] at hloc
  rw [site_fan_geometry_step5_radial_germ p hC hloc]
  exact hloc

/-- Step 7 of the V4 proof of `site_fan_geometry` (V4 1.0(H1)): affine images of
polyhedra are polyhedra (images of convex hulls are convex hulls of images). -/
private theorem site_fan_geometry_step7_polyhedron_image {K : Set (E d)} (hK : Polyhedron K)
    (g : E d →ᵃ[ℝ] E d) : Polyhedron (g '' K) := by
  classical
  obtain ⟨s, rfl⟩ := hK
  refine ⟨s.image (fun p => p.image g), ?_⟩
  rw [Set.image_iUnion₂]
  ext x
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hx⟩
    refine ⟨p.image g, ⟨p, hp, rfl⟩, ?_⟩
    rw [Finset.coe_image, ← AffineMap.image_convexHull]
    exact hx
  · rintro ⟨p', ⟨p, hp, rfl⟩, hx⟩
    refine ⟨p, hp, ?_⟩
    rw [Finset.coe_image, ← AffineMap.image_convexHull] at hx
    exact hx

/-- Step 8 of the V4 proof of `site_fan_geometry` (V4 1.22(a)): a trace polygon is a
placed cell of its owner, hence a polyhedron. -/
private theorem site_fan_geometry_step8_carrier_polyhedron {A : S.ι} {F : FacetFlag S A}
    {r : ℕ} (a : TracePiece A F r) : Polyhedron a.carrier := by
  rw [TracePiece.carrier, recursiveTrace_tiles_step0_cell_zero]
  exact site_fan_geometry_step7_polyhedron_image a.bottom.val.flat.polyhedral
    a.tile.frame.toAffineIsometry.toAffineMap

/-- Step 8 of the V4 proof of `site_fan_geometry` (V4 1.22(a), (H2)(iii)): a trace polygon
is the closure of its relative interior. -/
private theorem site_fan_geometry_step8_closure_relint {A : S.ι} {F : FacetFlag S A}
    {r : ℕ} (a : TracePiece A F r) : closure (relint a.carrier) = a.carrier := by
  rw [TracePiece.carrier, recursiveTrace_tiles_step0_relint_cell,
    recursiveTrace_tiles_step0_cell_zero]
  have h := a.tile.frame.toHomeomorph.image_closure (relint a.bottom.val.carrier)
  simp only [AffineIsometryEquiv.coe_toHomeomorph] at h
  rw [← h, a.bottom.val.flat.regularClosed]

/-- Step 9 of the V4 proof of `site_fan_geometry` (V4 1.0(b)): the radial tangent cone
is invariant under positive scaling. -/
private theorem site_fan_geometry_step9_smul {K : Set (E d)} {p v : E d} {s : ℝ}
    (hs : 0 < s) (hv : v ∈ tangentCone K p) : s • v ∈ tangentCone K p := by
  obtain ⟨ε, hε, h⟩ := hv
  refine ⟨ε / s, div_pos hε hs, fun t ht hts => ?_⟩
  have := h (t * s) (mul_pos ht hs) (by rwa [lt_div_iff₀ hs] at hts)
  rwa [smul_smul]

open scoped Topology in
/-- Step 10 of the V4 proof of `site_fan_geometry` (V4 1.23(b), via Lemma 1.22(a)):
"the half-disc of `F₂` at `q` is tiled by the finitely many polygons containing `q`".
Near `q` the cell `F₂` is the union of the pieces through `q`, and each piece coincides
with the translate of its tangent cone. -/
private theorem site_fan_geometry_step10_germ (A : S.ι) (F : FacetFlag S A) (r : ℕ)
    (q : E d) :
    ∀ᶠ x in 𝓝 q, (x ∈ (S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
          traceDimension_lt⟩).val.carrier ↔
        ∃ a : TracePiece A F r, q ∈ a.carrier ∧ x ∈ a.carrier) ∧
      ∀ a : TracePiece A F r, (x ∈ a.carrier ↔ x - q ∈ tangentCone a.carrier q) := by
  haveI := tracePieces_finite A F r
  have hfar : ∀ᶠ x in 𝓝 q, ∀ a : TracePiece A F r, q ∉ a.carrier → x ∉ a.carrier := by
    rw [Filter.eventually_all]
    intro a
    by_cases hqa : q ∈ a.carrier
    · exact Filter.Eventually.of_forall fun x h => (h hqa).elim
    · have hclosed : IsClosed a.carrier :=
        (site_fan_geometry_step8_carrier_polyhedron a).isCompact.isClosed
      exact Filter.mem_of_superset (hclosed.isOpen_compl.mem_nhds hqa) fun x hx _ => hx
  have hloc : ∀ᶠ x in 𝓝 q, ∀ a : TracePiece A F r,
      (x ∈ a.carrier ↔ x - q ∈ tangentCone a.carrier q) :=
    Filter.eventually_all.2 fun a =>
      site_fan_geometry_step6_local (site_fan_geometry_step8_carrier_polyhedron a) q
  filter_upwards [hfar, hloc] with x hx hx'
  refine ⟨⟨fun hxF => ?_, ?_⟩, hx'⟩
  · rw [← (recursiveTrace_tiles A F r).1] at hxF
    obtain ⟨a, -, hxa⟩ := Set.mem_iUnion₂.1 hxF
    by_cases hqa : q ∈ a.carrier
    · exact ⟨a, hqa, hxa⟩
    · exact (hx a hqa hxa).elim
  · rintro ⟨a, -, hxa⟩
    exact a.chain.contained TracePiece.bottomIndex hxa

open scoped Topology in
/-- Step 11 of the V4 proof of `site_fan_geometry` (V4 1.23(b), (H2)(iii)): at a point of a
regular closed cell, its tangent cone spans the whole direction space of the cell. -/
private theorem site_fan_geometry_step11_direction {K : Set (E d)} {q : E d}
    (hloc : ∀ᶠ x in 𝓝 q, x ∈ K ↔ x - q ∈ tangentCone K q) (hqK : q ∈ K)
    (hcl : q ∈ closure (relint K)) :
    ∀ w ∈ (affineSpan ℝ K).direction, w ∈ affineSpan ℝ (tangentCone K q) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hloc
  obtain ⟨z, hzrel, hzq⟩ := Metric.mem_closure_iff.1 hcl (δ / 2) (by linarith)
  obtain ⟨hzK, ρ, hρ, hzball⟩ := recursiveTrace_tiles_step3_halfspace_lift_lem_relint.1 hzrel
  have hzq' : dist z q < δ / 2 := by rwa [dist_comm]
  have hz0 : z - q ∈ tangentCone K q := (hball (by linarith : dist z q < δ)).1 hzK
  have h0T : (0 : E d) ∈ tangentCone K q :=
    ⟨1, one_pos, fun t _ _ => by simpa using hqK⟩
  have h0 : (0 : E d) ∈ affineSpan ℝ (tangentCone K q) := subset_affineSpan ℝ _ h0T
  intro w hw
  obtain ⟨ρ', hρ', hρ'ρ, hρ'δ⟩ : ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ρ' ≤ δ / 2 :=
    ⟨min ρ (δ / 2), lt_min hρ (by linarith), min_le_left _ _, min_le_right _ _⟩
  have hpos : 0 < 2 * (‖w‖ + 1) := by linarith [norm_nonneg w]
  obtain ⟨s, hs, hsw⟩ : ∃ s : ℝ, 0 < s ∧ s * ‖w‖ < ρ' :=
    ⟨ρ' / (2 * (‖w‖ + 1)), div_pos hρ' hpos, by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]; nlinarith [norm_nonneg w]⟩
  have hy_span : z + s • w ∈ affineSpan ℝ K := by
    have := AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ s hw)
      (subset_affineSpan ℝ K hzK)
    rwa [vadd_eq_add, add_comm] at this
  have hyz : dist (z + s • w) z < ρ' := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    exact hsw
  have hyK : z + s • w ∈ K := hzball _ hy_span (lt_of_lt_of_le hyz hρ'ρ)
  have hyq : dist (z + s • w) q < δ := by
    have := dist_triangle (z + s • w) z q
    linarith
  have hy0 : z + s • w - q ∈ tangentCone K q := (hball hyq).1 hyK
  have hdiff : s • w ∈ (affineSpan ℝ (tangentCone K q)).direction := by
    have := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hy0)
      (subset_affineSpan ℝ _ hz0)
    have e : z + s • w - q - (z - q) = s • w := by abel
    rwa [vsub_eq_sub, e] at this
  have hw' : w ∈ (affineSpan ℝ (tangentCone K q)).direction := by
    have := Submodule.smul_mem _ s⁻¹ hdiff
    rwa [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] at this
  have := (AffineSubspace.vsub_right_mem_direction_iff_mem h0 w).1
    (by rwa [vsub_eq_sub, sub_zero])
  exact this

/-- Step 12 of the V4 proof of `site_fan_geometry` (V4 1.23(b)): a direction in the
relative interior of the tangent cone points into the relative interior of the cell. -/
private theorem site_fan_geometry_step12_point {K : Set (E d)} {q v : E d} {t ρ δ : ℝ}
    (ht : 0 < t) (hρ : 0 < ρ) (htδ : t * (‖v‖ + ρ) < δ)
    (hloc : ∀ y, dist y q < δ → (y ∈ K ↔ y - q ∈ tangentCone K q))
    (hdir : ∀ w ∈ (affineSpan ℝ K).direction, w ∈ affineSpan ℝ (tangentCone K q))
    (hqK : q ∈ K) (hvT : v ∈ tangentCone K q)
    (hv : ∀ u ∈ affineSpan ℝ (tangentCone K q), dist u v < ρ → u ∈ tangentCone K q) :
    q + t • v ∈ relint K := by
  have hx0q : dist (q + t • v) q = t * ‖v‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
  have hρt : 0 < t * ρ := mul_pos ht hρ
  refine recursiveTrace_tiles_step3_halfspace_lift_lem_relint.2 ⟨?_, t * ρ, hρt, ?_⟩
  · refine (hloc _ (by rw [hx0q]; nlinarith)).2 ?_
    rw [add_sub_cancel_left]
    exact site_fan_geometry_step9_smul ht hvT
  · intro y hy hyx
    have hyq_dir : y - q ∈ (affineSpan ℝ K).direction := by
      have := AffineSubspace.vsub_mem_direction hy (subset_affineSpan ℝ K hqK)
      rwa [vsub_eq_sub] at this
    have hu_span : t⁻¹ • (y - q) ∈ affineSpan ℝ (tangentCone K q) :=
      hdir _ (Submodule.smul_mem _ _ hyq_dir)
    have key : t⁻¹ • (y - q) - v = t⁻¹ • (y - (q + t • v)) := by
      rw [show y - (q + t • v) = (y - q) - t • v by abel, smul_sub (t⁻¹) (y - q) (t • v),
        smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    have hudist : dist (t⁻¹ • (y - q)) v < ρ := by
      rw [dist_eq_norm, key, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le),
        ← dist_eq_norm, inv_mul_lt_iff₀ ht]
      exact hyx
    have huT := hv _ hu_span hudist
    have htu : t • t⁻¹ • (y - q) = y - q := by
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hyq : dist y q < δ := by
      have := dist_triangle y (q + t • v) q
      rw [hx0q] at this
      nlinarith
    refine (hloc y hyq).2 ?_
    rw [← htu]
    exact site_fan_geometry_step9_smul ht huT

/-- Step 13 of the V4 proof of `site_fan_geometry` (V4 1.23(b)): "the polygons ... meeting
`q` form a finite planar fan": two cells through `q` with disjoint relative interiors have
tangent cones at `q` with disjoint relative interiors. -/
private theorem site_fan_geometry_step13_disjoint {K L : Set (E d)} {q : E d}
    (hK : Polyhedron K) (hL : Polyhedron L) (hqK : q ∈ K) (hqL : q ∈ L)
    (hKc : q ∈ closure (relint K)) (hLc : q ∈ closure (relint L))
    (hdisj : Disjoint (relint K) (relint L)) :
    Disjoint (relint (tangentCone K q)) (relint (tangentCone L q)) := by
  rw [Set.disjoint_left]
  intro v hvK hvL
  obtain ⟨hvTK, ρK, hρK, hK'⟩ := recursiveTrace_tiles_step3_halfspace_lift_lem_relint.1 hvK
  obtain ⟨hvTL, ρL, hρL, hL'⟩ := recursiveTrace_tiles_step3_halfspace_lift_lem_relint.1 hvL
  have hlocK := site_fan_geometry_step6_local hK q
  have hlocL := site_fan_geometry_step6_local hL q
  obtain ⟨δK, hδK, hbK⟩ := Metric.eventually_nhds_iff.1 hlocK
  obtain ⟨δL, hδL, hbL⟩ := Metric.eventually_nhds_iff.1 hlocL
  obtain ⟨ρ, hρ, hρK', hρL'⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρK ∧ ρ ≤ ρL :=
    ⟨min ρK ρL, lt_min hρK hρL, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨δ, hδ, hδK', hδL'⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δK ∧ δ ≤ δL :=
    ⟨min δK δL, lt_min hδK hδL, min_le_left _ _, min_le_right _ _⟩
  have hpos : 0 < ‖v‖ + ρ + 1 := by linarith [norm_nonneg v]
  obtain ⟨t, ht, htδ⟩ : ∃ t : ℝ, 0 < t ∧ t * (‖v‖ + ρ) < δ :=
    ⟨δ / (‖v‖ + ρ + 1), div_pos hδ hpos, by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]; nlinarith⟩
  have hxK := site_fan_geometry_step12_point ht hρ (lt_of_lt_of_le htδ hδK')
    (fun y hy => hbK hy) (site_fan_geometry_step11_direction hlocK hqK hKc) hqK hvTK
    (fun u hu hd => hK' u hu (lt_of_lt_of_le hd hρK'))
  have hxL := site_fan_geometry_step12_point ht hρ (lt_of_lt_of_le htδ hδL')
    (fun y hy => hbL hy) (site_fan_geometry_step11_direction hlocL hqL hLc) hqL hvTL
    (fun u hu hd => hL' u hu (lt_of_lt_of_le hd hρL'))
  exact Set.disjoint_left.1 hdisj hxK hxL

/-- Step 14 of the V4 proof of `site_fan_geometry` (V4 1.23(b), 1.0(c)): "there are at most
... of them": a trace piece through `q` is an owner through `q` (finitely many, uniformly
bounded by the multiplicity bound) together with a chain of named cells of its type
(finitely many per type, and there are finitely many types). -/
private theorem site_fan_geometry_step14_card (S : SubstSystem d) :
    ∃ M : ℕ, ∀ (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d),
      Nat.card {a : TracePiece A F r // q ∈ a.carrier} ≤ M := by
  classical
  obtain ⟨β, -, -, -, hbound⟩ := point_multiplicity_bound S.proto S.cx
  let Kmax : ℕ := Finset.univ.sup fun τ : S.ι =>
    Fintype.card (ChainIndex d (traceDimension d) → CellName S τ)
  have hK : ∀ τ : S.ι,
      Fintype.card (ChainIndex d (traceDimension d) → CellName S τ) ≤ Kmax := fun τ =>
    Finset.le_sup (f := fun τ : S.ι =>
      Fintype.card (ChainIndex d (traceDimension d) → CellName S τ)) (Finset.mem_univ τ)
  refine ⟨⌊fullSolidAngle d / β⌋₊ * Kmax, ?_⟩
  intro A F r q
  have hdisj : Pairwise (fun a b : S.RoleWord A r => Disjoint
      (interior (placedSet (S.nativeTile A r a).frame
        (S.proto (S.nativeTile A r a).ty).carrier))
      (interior (placedSet (S.nativeTile A r b).frame
        (S.proto (S.nativeTile A r b).ty).carrier))) := by
    simpa [FramedNode.carrier, SubstSystem.supertile] using S.native_disjoint A r
  obtain ⟨hfinite, hcard⟩ := hbound (S.RoleWord A r)
    (fun w => (S.nativeTile A r w).ty) (fun w => (S.nativeTile A r w).frame) hdisj q
  let I : Set (S.RoleWord A r) := {w | q ∈ placedSet (S.nativeTile A r w).frame
    (S.proto (S.nativeTile A r w).ty).carrier}
  haveI : Finite I := hfinite.to_subtype
  have hmem : ∀ a : {a : TracePiece A F r // q ∈ a.carrier}, a.val.owner ∈ I := by
    intro a
    have hc := site_fan_finite_step7_carrier_subset a.val a.property
    simpa [I, TracePiece.tile, FramedNode.carrier, SubstSystem.supertile] using hc
  let f : {a : TracePiece A F r // q ∈ a.carrier} →
      Σ w : I, (ChainIndex d (traceDimension d) → CellName S (S.nativeTile A r w.val).ty) :=
    fun a => ⟨⟨a.val.owner, hmem a⟩, a.val.chain.cell⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨o1, c1⟩, h1⟩ ⟨⟨o2, c2⟩, h2⟩ h
    simp only [f, Sigma.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨rfl, hc⟩ := h
    have hc' : c1.cell = c2.cell := eq_of_heq hc
    cases c1
    cases c2
    simp only at hc'
    subst hc'
    rfl
  let g : (Σ w : I, (ChainIndex d (traceDimension d) →
      CellName S (S.nativeTile A r w.val).ty)) → I × Fin Kmax :=
    fun x => (x.1, Fin.castLE (hK _) (Fintype.equivFin _ x.2))
  have hg : Function.Injective g := by
    rintro ⟨w1, c1⟩ ⟨w2, c2⟩ h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have := (Fintype.equivFin _).injective (Fin.castLE_injective _ h)
    subst this
    rfl
  calc Nat.card {a : TracePiece A F r // q ∈ a.carrier}
      ≤ Nat.card (I × Fin Kmax) := Nat.card_le_card_of_injective (g ∘ f) (hg.comp hf)
    _ = I.ncard * Kmax := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin Kmax), Fintype.card_fin,
          Nat.card_coe_set_eq]
    _ ≤ ⌊fullSolidAngle d / β⌋₊ * Kmax := Nat.mul_le_mul_right _ hcard

/-- P18, V4 1.23(b): the actual trace pieces at a site form a finite fan:
their direction cones cover the outer half-plane (half-line when `d=2`) and have
disjoint relative interiors. Their number has one uniform bound over all depths. -/
theorem site_fan_geometry (S : SubstSystem d) :
    ∃ M : ℕ, ∀ (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d),
      IsSite A F r q →
      Nat.card {a : TracePiece A F r // q ∈ a.carrier} ≤ M ∧
      (⋃ a : {a : TracePiece A F r // q ∈ a.carrier},
        tangentCone a.val.carrier q) =
        tangentCone ((S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
          traceDimension_lt⟩).val.carrier) q ∧
      Pairwise (fun a b : {a : TracePiece A F r // q ∈ a.carrier} =>
        Disjoint (relint (tangentCone a.val.carrier q))
          (relint (tangentCone b.val.carrier q))) := by
  obtain ⟨M, hM⟩ := site_fan_geometry_step14_card S
  refine ⟨M, fun A F r q _hq => ⟨hM A F r q, ?_, ?_⟩⟩
  · apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun a => ?_
      rintro v ⟨ε, hε, hv⟩
      exact ⟨ε, hε, fun t ht htε => a.val.chain.contained TracePiece.bottomIndex (hv t ht htε)⟩
    · intro v hv
      obtain ⟨ε, hε, hvε⟩ := hv
      obtain ⟨δ, hδ, hgerm⟩ := Metric.eventually_nhds_iff.1 (site_fan_geometry_step10_germ A F r q)
      have hpos : 0 < ‖v‖ + 1 := by linarith [norm_nonneg v]
      obtain ⟨t, ht, htε, htδ⟩ : ∃ t : ℝ, 0 < t ∧ t < ε ∧ t * ‖v‖ < δ := by
        refine ⟨min (ε / 2) (δ / (‖v‖ + 1)), lt_min (by linarith) (div_pos hδ hpos),
          lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
        calc min (ε / 2) (δ / (‖v‖ + 1)) * ‖v‖ ≤ (δ / (‖v‖ + 1)) * ‖v‖ :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
          _ < δ := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]; nlinarith [norm_nonneg v]
      have hdist : dist (q + t • v) q < δ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
        exact htδ
      obtain ⟨hF, hloc⟩ := hgerm hdist
      obtain ⟨a, hqa, hxa⟩ := hF.1 (hvε t ht htε)
      have hta : t • v ∈ tangentCone a.carrier q := by
        have := (hloc a).1 hxa
        rwa [add_sub_cancel_left] at this
      have hva := site_fan_geometry_step9_smul (inv_pos.2 ht) hta
      rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at hva
      exact Set.mem_iUnion.2 ⟨⟨a, hqa⟩, hva⟩
  · intro a b hab
    have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    exact site_fan_geometry_step13_disjoint (site_fan_geometry_step8_carrier_polyhedron a.val)
      (site_fan_geometry_step8_carrier_polyhedron b.val) a.property b.property
      (by rw [site_fan_geometry_step8_closure_relint]; exact a.property)
      (by rw [site_fan_geometry_step8_closure_relint]; exact b.property)
      ((recursiveTrace_tiles A F r).2.1 hab')

open private hereditary_trace_step1_relint_image from Enforce.Source.Trace in
/-- Step 1 of the V4 proof of `site_listed` (V4 1.23(c)): "Once a site `q` of depth `r`
is fixed": native-scale positions at depth `r + s` are compared by `σˢ`, and `σˢ` (an
affine automorphism) carries relative interiors of depth-`r` cells `σʳ X` onto relative
interiors of the depth-`(r+s)` cells `σʳ⁺ˢ X`; in particular `σˢ q ∈ relint h`. -/
private theorem site_listed_step1_relint_scale (r s : ℕ) (X : Set (E d)) {y : E d}
    (hy : y ∈ relint ((S.σ ^ r) '' X)) : (S.σ ^ s) y ∈ relint ((S.σ ^ (r + s)) '' X) := by
  have hE : (S.σ ^ (r + s)) '' X = (S.σ ^ s).toAffineEquiv '' ((S.σ ^ r) '' X) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [add_comm r s, pow_add]
    rfl
  rw [hE, hereditary_trace_step1_relint_image]
  exact ⟨y, hy, rfl⟩

open private hereditary_trace_step1_relint_unique from Enforce.Source.Trace in
/-- Step 2 of the V4 proof of `site_listed` (V4 1.23(c), `d ≥ 3`): "`G' ⊆ F₂` lies on one
side of `h`": a relative-interior point of the flag edge `h` is not a relative-interior
point of the flag polygon `F₂` (distinct listed cells of the root have disjoint relative
interiors, and `dim h = 1 < 2 = dim F₂`). -/
private theorem site_listed_step2_flag_not_plane (hd : d ≠ 2) (A : S.ι) (F : FacetFlag S A)
    (r : ℕ) (q : E d) (hq : q ∈ relint (flagEdge A F r)) :
    q ∉ relint ((S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
      traceDimension_lt⟩).val.carrier) := by
  intro hqT
  have h2d : 2 ≤ d := Fact.out
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hR : ∀ e : Cell d, R.cell r e = (S.σ ^ r) '' e.carrier :=
    recursiveTrace_tiles_step0_root_cell A r
  have h1 : q ∈ relint (R.cell r
      (F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val) := by
    rw [hR]; exact hq
  have h2 : q ∈ relint (R.cell r
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val) := by
    rw [hR]; exact hqT
  have heq := hereditary_trace_step1_relint_unique R r _ _ (F.cell _).property
    (F.cell _).property q h1 h2
  have hA : (F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val.dim = 1 :=
    F.dimension _
  have hB : (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.dim =
      traceDimension d := F.dimension _
  have hT2 : traceDimension d = 2 := by unfold traceDimension; omega
  rw [heq] at hA
  omega

open private hereditary_trace_step1_cell_frontier from Enforce.Source.Trace in
/-- Step 2' of the V4 proof of `site_listed` (V4 1.23(c), `d = 2`, Lemma 1.0(a)): the flag
edge `h` lies on the frontier of the node, so it misses the interior of the node. -/
private theorem site_listed_step2_flag_frontier (A : S.ι) (F : FacetFlag S A) (r : ℕ)
    (x : E d) (hx : x ∈ flagEdge A F r) : x ∉ interior (S.supertile r A) := by
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hR : ∀ e : Cell d, R.cell r e = (S.σ ^ r) '' e.carrier :=
    recursiveTrace_tiles_step0_root_cell A r
  have hRc : R.carrier r = S.supertile r A := by
    simp [R, FramedNode.carrier, placedSet]
  have hEF : flagEdge A F r ⊆ frontier (S.supertile r A) := by
    have := hereditary_trace_step1_cell_frontier R r
      (F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val (F.cell _).property
    rw [hR, hRc] at this
    exact this
  exact (hEF hx).2

open private hereditary_trace_step2_boundary from Enforce.Source.Trace in
/-- Step 3 of the V4 proof of `site_listed` (V4 1.23(c)): "Hence `q` is a vertex of `G'`".
A point of a listed edge outside its relative interior lies in a listed vertex below it
((H2)(ii)); that vertex cell is the single point, hence inside any set containing it. -/
private theorem site_listed_step3_vertex (C : FramedNode S) (e : Cell d)
    (he : e ∈ (S.cx C.ty).cells) (he1 : e.dim = 1) (p : E d) (hpe : p ∈ C.cell 0 e)
    (hpi : p ∉ relint (C.cell 0 e)) (K : Set (E d)) (hpK : p ∈ K) :
    ∃ v ∈ (S.cx C.ty).vertices, p ∈ C.cell 0 v ∧ C.cell 0 v ⊆ K := by
  obtain ⟨v, hv, hlt, -, hpv⟩ := hereditary_trace_step2_boundary C 0 e he p hpe hpi
  have hv0 : v.dim = 0 := by omega
  refine ⟨v, ?_, hpv, fun x hx => ?_⟩
  · unfold CellComplex.vertices
    exact Finset.mem_filter.2 ⟨hv, hv0⟩
  · rw [sites_exist_step3_inward_arm_step12_point C v hv0 hx hpv]
    exact hpK

/-- Step 4 of the V4 proof of `site_listed` (V4 1.23(c)): "the inward arm at `q`" reaches
every neighbourhood of `σˢ q`: a listed cell through `q` has relative-interior points
arbitrarily close to `q` ((H2)(iii), regular closedness), and `σˢ` is continuous. -/
private theorem site_listed_step4_arm_approach (C : FramedNode S) (e : Cell d) (s : ℕ)
    (q : E d) (hqe : q ∈ C.cell 0 e) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ y ∈ relint (C.cell 0 e), (S.σ ^ s) y ∈ ball ((S.σ ^ s) q) ρ := by
  have hcont : Continuous (S.σ ^ s) :=
    LinearMap.continuous_of_finiteDimensional (S.σ ^ s).toLinearMap
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hcont q ρ hρ
  have hcl : closure (relint (C.cell 0 e)) = C.cell 0 e := by
    rw [recursiveTrace_tiles_step0_relint_cell, recursiveTrace_tiles_step0_cell_zero]
    have h := C.frame.toHomeomorph.image_closure (relint e.carrier)
    rw [AffineIsometryEquiv.coe_toHomeomorph] at h
    rw [← h, e.flat.regularClosed]
  have hq' : q ∈ closure (relint (C.cell 0 e)) := by rw [hcl]; exact hqe
  obtain ⟨y, hy, hyq⟩ := Metric.mem_closure_iff.1 hq' δ hδ
  exact ⟨y, hy, hball y (by rw [dist_comm]; exact hyq)⟩

open private hereditary_trace_step1_relint_image hereditary_trace_step2_relint_mono
  hereditary_trace_step6_same hereditary_trace_step1_relint_unique from Enforce.Source.Trace in
/-- Step 5 of the V4 proof of `site_listed` (V4 1.23(c), `d ≥ 3`): "the inward arm at `q`
is an edge of the depth-`r` tiling, which (by heredity of cells and Lemma 1.22(b)) is a
union of deeper polygon edges". The `σˢ`-image of a listed edge `e` of a depth-`r` trace
polygon `c` (an edge inside `c`) misses the relative interior of every depth-`(r+s)`
trace polygon `b`: by Lemma 1.22(b) `b` lies in `σˢ c'` for a depth-`r` polygon `c'` with
the same plane; a point of `σˢ e` in `relint b` would lie in `relint σˢ c'`, forcing
`c' = c` (disjoint relative interiors of the depth-`r` trace) and then a point of the
boundary edge `e` in `relint c`. -/
private theorem site_listed_step5_arm_miss_plane (hd : d ≠ 2) (A : S.ι) (F : FacetFlag S A)
    (r s : ℕ) (c : TracePiece A F r) (e : CellName S c.tile.ty) (he : e.val.dim = 1)
    (hec : c.tile.cell 0 e.val ⊆ c.carrier) (b : TracePiece A F (r + s)) (y : E d)
    (hy : y ∈ c.tile.cell 0 e.val) : (S.σ ^ s) y ∉ relint b.carrier := by
  intro hyb
  have h2d : 2 ≤ d := Fact.out
  have hT2 : traceDimension d = 2 := by unfold traceDimension; omega
  obtain ⟨c', -, hsub⟩ := trace_refines A F r s b
  have hbc : b.carrier ⊆ (S.σ ^ s).toAffineEquiv '' c'.carrier := hsub TracePiece.bottomIndex
  have hE : ∀ X : Set (E d),
      (S.σ ^ (r + s)) '' X = (S.σ ^ s).toAffineEquiv '' ((S.σ ^ r) '' X) := by
    intro X
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [add_comm r s, pow_add]
    rfl
  have hspan_b : affineSpan ℝ b.carrier = affineSpan ℝ ((S.σ ^ (r + s)) ''
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.carrier) :=
    recursiveTrace_tiles_step1_span b TracePiece.bottomIndex
  have hspan_c' : affineSpan ℝ c'.carrier = affineSpan ℝ ((S.σ ^ r) ''
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.carrier) :=
    recursiveTrace_tiles_step1_span c' TracePiece.bottomIndex
  have hspan_c : affineSpan ℝ c.carrier = affineSpan ℝ ((S.σ ^ r) ''
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.carrier) :=
    recursiveTrace_tiles_step1_span c TracePiece.bottomIndex
  have hmap : ∀ X : Set (E d), affineSpan ℝ ((S.σ ^ s).toAffineEquiv '' X) =
      (affineSpan ℝ X).map ((S.σ ^ s).toAffineEquiv : E d →ᵃ[ℝ] E d) := fun X =>
    (AffineSubspace.map_span ((S.σ ^ s).toAffineEquiv : E d →ᵃ[ℝ] E d) X).symm
  have hspan : affineSpan ℝ b.carrier =
      affineSpan ℝ ((S.σ ^ s).toAffineEquiv '' c'.carrier) := by
    rw [hspan_b, hE, hmap, hmap, hspan_c']
  have hy1 : (S.σ ^ s) y ∈ relint ((S.σ ^ s).toAffineEquiv '' c'.carrier) :=
    hereditary_trace_step2_relint_mono _ _ hbc hspan hyb
  rw [hereditary_trace_step1_relint_image] at hy1
  obtain ⟨y0, hy0, hyy⟩ := hy1
  have hy0y : y0 = y := (S.σ ^ s).injective hyy
  rw [hy0y] at hy0
  have hyc : y ∈ c.carrier := hec hy
  have hcl : closure (relint c.carrier) = c.carrier := by
    unfold TracePiece.carrier
    rw [recursiveTrace_tiles_step0_relint_cell, recursiveTrace_tiles_step0_cell_zero]
    have h := c.tile.frame.toHomeomorph.image_closure (relint c.bottom.val.carrier)
    rw [AffineIsometryEquiv.coe_toHomeomorph] at h
    rw [← h, c.bottom.val.flat.regularClosed]
  have hcc : c' = c := by
    by_contra hne
    have hy0' := hy0
    unfold relint at hy0'
    rw [mem_intrinsicInterior] at hy0'
    obtain ⟨z, hz, hzy⟩ := hy0'
    obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.1
      (isOpen_interior (s := ((↑) ⁻¹' c'.carrier : Set (affineSpan ℝ c'.carrier))))
    have hzO : (z : E d) ∈ O := by
      have : z ∈ (Subtype.val ⁻¹' O : Set (affineSpan ℝ c'.carrier)) := by
        rw [hOeq]; exact hz
      exact this
    rw [hzy] at hzO
    have hycl : y ∈ closure (relint c.carrier) := by rw [hcl]; exact hyc
    obtain ⟨y', hy'O, hy'c⟩ := mem_closure_iff.1 hycl O hO hzO
    have hy'P : y' ∈ affineSpan ℝ c'.carrier := by
      rw [hspan_c', ← hspan_c]
      exact mem_affineSpan ℝ (intrinsicInterior_subset hy'c)
    have hy'c' : y' ∈ relint c'.carrier := by
      unfold relint
      rw [mem_intrinsicInterior]
      refine ⟨⟨y', hy'P⟩, ?_, rfl⟩
      rw [← hOeq]
      exact hy'O
    exact Set.disjoint_left.1 ((recursiveTrace_tiles A F r).2.1 hne) hy'c' hy'c
  rw [hcc] at hy0
  have hsub2 : c.tile.cell 0 c.bottom.val ⊆ c.tile.cell 0 e.val :=
    hereditary_trace_step6_same c.tile 0 e.val c.bottom.val e.property c.bottom.property
      ⟨y, hy0, hy⟩
  have heq : c.carrier = c.tile.cell 0 e.val := Set.Subset.antisymm hsub2 hec
  have hye : y ∈ relint (c.tile.cell 0 e.val) := by rw [← heq]; exact hy0
  have hbe := hereditary_trace_step1_relint_unique c.tile 0 _ _ c.bottom.property
    e.property y hy0 hye
  have hbd : c.bottom.val.dim = traceDimension d := c.chain.dimension TracePiece.bottomIndex
  rw [hbe] at hbd
  omega

/-- Step 6 of the V4 proof of `site_listed` (V4 1.23(c), `d = 2`): `σˢ` carries interior
points of the node `σʳ A` to interior points of `σʳ⁺ˢ A` (a homeomorphism). -/
private theorem site_listed_step6_interior_scale (A : S.ι) (r s : ℕ) {y : E d}
    (hy : y ∈ interior (S.supertile r A)) :
    (S.σ ^ s) y ∈ interior (S.supertile (r + s) A) := by
  let φ := (S.σ ^ s).toContinuousLinearEquiv.toHomeomorph
  have hE : S.supertile (r + s) A = φ '' S.supertile r A := by
    unfold SubstSystem.supertile
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [add_comm r s, pow_add]
    rfl
  rw [hE, ← φ.image_interior]
  exact ⟨y, hy, rfl⟩

open private hereditary_trace_step7_carrier from Enforce.Source.Trace in
/-- Step 7a of the V4 proof of `site_listed` (V4 1.23(c), with (H3) and Lemma 1.22(b),
"heredity of cells"): every native tile of depth `r + s` lies in the `σˢ`-image of a
native tile of depth `r` (its depth-`r` ancestor): placing children commutes with `σ`,
`σ^(s+n) R σ^(-(s+n)) σˢ = σˢ σⁿ R σ⁻ⁿ`. -/
private theorem site_listed_step7_native_refines (A : S.ι) (r s : ℕ)
    (w' : S.RoleWord A (r + s)) :
    ∃ w : S.RoleWord A r, (S.nativeTile A (r + s) w').carrier 0 ⊆
      (S.σ ^ s) '' (S.nativeTile A r w).carrier 0 := by
  suffices H : ∀ (n : ℕ) (B : S.ι) (m : ℕ) (_hm : s + n = m) (v : S.RoleWord B m),
      ∃ u : S.RoleWord B n, (S.nativeTile B m v).carrier 0 ⊆
        (S.σ ^ s) '' (S.nativeTile B n u).carrier 0 from
    H r A (r + s) (add_comm s r) w'
  have hmove : ∀ (N : FramedNode S) (g : Iso d), (N.move g).carrier 0 = g '' N.carrier 0 := by
    intro N g
    simp only [FramedNode.move, FramedNode.carrier, placedSet, Set.image_image]
    rfl
  intro n
  induction n with
  | zero =>
    intro B m hm v
    subst hm
    refine ⟨(), ?_⟩
    have hC : (S.nativeTile B (s + 0) v).IsDescendant 0
        ⟨B, AffineIsometryEquiv.refl ℝ (E d)⟩ (0 + (s + 0)) := by
      rw [zero_add]; exact recursiveTrace_tiles_step0_native_desc B (s + 0) v
    intro x hx
    have h1 := hereditary_trace_step7_carrier _ _ 0 (s + 0) hC hx
    simpa [FramedNode.carrier, placedSet, SubstSystem.supertile, SubstSystem.nativeTile,
      SubstSystem.descendantNode] using h1
  | succ n ih =>
    intro B m hm v
    subst hm
    change (Σ i : S.I B, S.RoleWord (S.child B i).ty (s + n)) at v
    obtain ⟨i, v2⟩ := v
    obtain ⟨u', hu'⟩ := ih (S.child B i).ty (s + n) rfl v2
    refine ⟨⟨i, u'⟩, ?_⟩
    have hdef : S.nativeTile B (s + (n + 1)) ⟨i, v2⟩ =
        (S.nativeTile (S.child B i).ty (s + n) v2).move (S.placeChild (0 + (s + n)) i) := rfl
    have hdef' : S.nativeTile B (n + 1) ⟨i, u'⟩ =
        (S.nativeTile (S.child B i).ty n u').move (S.placeChild (0 + n) i) := rfl
    have key : ∀ R : E d ≃ₗ[ℝ] E d,
        S.σ ^ (((s + n : ℕ)) : ℤ) * R * S.σ ^ (-((s + n : ℕ) : ℤ)) * S.σ ^ (s : ℤ) =
          S.σ ^ (s : ℤ) * (S.σ ^ (n : ℤ) * R * S.σ ^ (-(n : ℤ))) := by
      intro R
      push_cast
      group
    have hcomm : ∀ x : E d, S.placeChild (0 + (s + n)) i ((S.σ ^ s) x) =
        (S.σ ^ s) (S.placeChild (0 + n) i x) := by
      intro x
      rw [S.placeChild_apply, S.placeChild_apply, map_add]
      have h1 := congrArg (fun f : E d ≃ₗ[ℝ] E d => f x)
        (key (S.child B i).rotation.toLinearEquiv)
      have h2 : (S.σ ^ (0 + (s + n))) (S.child B i).offset =
          (S.σ ^ s) ((S.σ ^ (0 + n)) (S.child B i).offset) := by
        rw [zero_add, zero_add, ← LinearEquiv.mul_apply, ← pow_add]
      rw [h2]
      congr 1
      simp only [linearConj, LinearEquiv.mul_apply, zero_add, Nat.cast_add, zpow_natCast]
        at h1 ⊢
      exact h1
    rw [hdef, hdef', hmove, hmove]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hu' hx
    exact ⟨S.placeChild (0 + n) i y, ⟨y, hy, rfl⟩, (hcomm y).symm⟩

open private hereditary_trace_step1_cell_frontier hereditary_trace_step1_cell_subset
  from Enforce.Source.Trace in
/-- Step 7 of the V4 proof of `site_listed` (V4 1.23(c), dimension-two convention): the
inward arm, an edge of a native depth-`r` tile `w`, stays a union of deeper tile edges:
its `σˢ`-image misses the interior of every native depth-`(r+s)` tile `w'`. Indeed `w'`
lies in `σˢ` of a native depth-`r` tile `w''` (heredity of the subdivision); a point of
`σˢ e` interior to `w'` is interior to `σˢ w''`, so `w''` meets the interior of `w`
(regular closedness), whence `w'' = w` (disjoint native interiors), contradicting that
the listed edge `e` lies on the frontier of `w`. -/
private theorem site_listed_step7_arm_miss_domain (A : S.ι) (r s : ℕ) (w : S.RoleWord A r)
    (e : CellName S (S.nativeTile A r w).ty) (w' : S.RoleWord A (r + s)) (y : E d)
    (hy : y ∈ (S.nativeTile A r w).cell 0 e.val) :
    (S.σ ^ s) y ∉ interior ((S.nativeTile A (r + s) w').carrier 0) := by
  intro hyi
  obtain ⟨w'', hsub⟩ := site_listed_step7_native_refines A r s w'
  let φ := (S.σ ^ s).toContinuousLinearEquiv.toHomeomorph
  have hsub' : (S.nativeTile A (r + s) w').carrier 0 ⊆
      φ '' (S.nativeTile A r w'').carrier 0 := hsub
  have h1 : (S.σ ^ s) y ∈ φ '' interior ((S.nativeTile A r w'').carrier 0) := by
    rw [φ.image_interior]; exact interior_mono hsub' hyi
  obtain ⟨y0, hy0, hyy⟩ := h1
  have hy0y : y0 = y := (S.σ ^ s).injective hyy
  rw [hy0y] at hy0
  have hyF : y ∈ frontier ((S.nativeTile A r w).carrier 0) :=
    hereditary_trace_step1_cell_frontier _ 0 e.val e.property hy
  have hyC : y ∈ (S.nativeTile A r w).carrier 0 :=
    hereditary_trace_step1_cell_subset _ 0 e.val e.property hy
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy0
  obtain ⟨z, ⟨hzw, -⟩, hzb⟩ :=
    sites_exist_step3_inward_arm_step9_overlap_domain A r y w hyC ρ hρ
  have hww : w = w'' := by
    by_contra hne
    exact Set.disjoint_left.1 (S.native_disjoint A r hne) hzw (hball hzb)
  rw [← hww] at hy0
  exact hyF.2 hy0

/-- P18, V4 1.23(c): every deeper trace polygon meeting a fixed site lists it,
as does its selected owner. Native-scale positions are compared by `σˢ`. -/
theorem site_listed (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d)
    (hq : IsSite A F r q) (s : ℕ) (a : TracePiece A F (r + s))
    (ha : (S.σ ^ s) q ∈ a.carrier) :
    ∃ v ∈ (S.cx a.tile.ty).vertices,
      (S.σ ^ s) q ∈ a.tile.cell 0 v ∧ a.tile.cell 0 v ⊆ a.carrier := by
  have hq' : (S.σ ^ s) q ∈ relint (flagEdge A F (r + s)) :=
    site_listed_step1_relint_scale r s _ hq.1
  have hqF : (S.σ ^ s) q ∈ flagEdge A F (r + s) := intrinsicInterior_subset hq'
  have harm := hq.2.1
  unfold InwardTraceArm at harm
  by_cases hd : d = 2
  · rw [if_pos hd] at harm
    obtain ⟨w, e, -, -, hqe, hrel⟩ := harm
    by_cases hex : ∃ e : CellName S a.tile.ty, e.val.dim = 1 ∧
        (S.σ ^ s) q ∈ a.tile.cell 0 e.val ∧ ¬ a.tile.cell 0 e.val ⊆ flagEdge A F (r + s)
    · obtain ⟨e', he', hqe', hne⟩ := hex
      have hin := sites_exist_step3_inward_arm_step3_heredity_domain hd A F (r + s) _ hq'
        a.owner e' hqe' hne
      exact site_listed_step3_vertex a.tile e'.val e'.property he' _ hqe'
        (fun hqi => site_listed_step2_flag_frontier A F (r + s) _ hqF (hin hqi)) _ ha
    · push_neg at hex
      have hqa : (S.σ ^ s) q ∈ (S.nativeTile A (r + s) a.owner).carrier 0 :=
        sites_exist_step3_inward_arm_step10_carrier A F (r + s) a ha
      obtain ⟨ρ, hρ, hfl⟩ :=
        sites_exist_step3_inward_arm_step7_flat_domain hd A F (r + s) _ a.owner hqF hex
      obtain ⟨ρ', hρ', hfill⟩ :=
        sites_exist_step3_inward_arm_step8_fill_domain hd A F (r + s) _ hq' a.owner hqa
          ρ hρ hfl
      obtain ⟨y, hy, hyb⟩ :=
        site_listed_step4_arm_approach (S.nativeTile A r w) e.val s q hqe ρ' hρ'
      have hyS := site_listed_step6_interior_scale A r s (hrel hy)
      exact (site_listed_step7_arm_miss_domain A r s w e a.owner y
        (intrinsicInterior_subset hy) (hfill ⟨hyS, hyb⟩)).elim
  · rw [if_neg hd] at harm
    obtain ⟨c, e, he, -, hqe, hec, hrel⟩ := harm
    by_cases hex : ∃ e : CellName S a.tile.ty, e.val.dim = 1 ∧
        (S.σ ^ s) q ∈ a.tile.cell 0 e.val ∧ a.tile.cell 0 e.val ⊆ a.carrier ∧
        ¬ a.tile.cell 0 e.val ⊆ flagEdge A F (r + s)
    · obtain ⟨e', he', hqe', hsub, hne⟩ := hex
      have hin := sites_exist_step3_inward_arm_step2_heredity_plane A F (r + s) _ hq' a e'
        hqe' hsub hne
      exact site_listed_step3_vertex a.tile e'.val e'.property he' _ hqe'
        (fun hqi => site_listed_step2_flag_not_plane hd A F (r + s) _ hq' (hin hqi)) _ ha
    · push_neg at hex
      obtain ⟨ρ, hρ, hfl⟩ :=
        sites_exist_step3_inward_arm_step4_flat_plane A F (r + s) _ a hqF hex
      obtain ⟨ρ', hρ', hfill⟩ :=
        sites_exist_step3_inward_arm_step5_fill_plane hd A F (r + s) _ hq' a ha ρ hρ hfl
      obtain ⟨y, hy, hyb⟩ := site_listed_step4_arm_approach c.tile e.val s q hqe ρ' hρ'
      have hyT := site_listed_step1_relint_scale r s _ (hrel hy)
      exact (site_listed_step5_arm_miss_plane hd A F r s c e he hec a y
        (intrinsicInterior_subset hy) (hfill ⟨hyT, hyb⟩)).elim

/-- P18, V4 1.23(a),(c): an ordinary site persists at every deeper subdivision. -/
theorem site_persists (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d)
    (hq : IsSite A F r q) (s : ℕ) : IsSite A F (r + s) ((S.σ ^ s) q) := by
  sorry

/-- P17/P18, V4 1.22--1.23: the scale normalization from a native-scale
height-`r` root to the depth-`r` subdivision of a placed height-`n` node.
Applications below require `r ≤ n`; the linear part need not be a similarity. -/
def tracePlacement (N : FramedNode S) (n r : ℕ) : E d ≃ᵃ[ℝ] E d :=
  (S.σ ^ (n - r)).toAffineEquiv.trans N.frame.toAffineEquiv

/-- P17, V4 1.22(a): the actual height-`n-r` owner of a placed trace piece,
with the exact role word and recursive hierarchy frame. -/
def placedTraceOwner (N : FramedNode S) (n r : ℕ) (F : FacetFlag S N.ty)
    (a : TracePiece N.ty F r) : FramedNode S :=
  (S.descendantNode N.ty (n - r) r a.owner).move N.frame

/-- P17, V4 1.22(a): placed trace polygon or edge, retaining its native-scale
owner and chain as the index rather than making fresh geometric choices. -/
def placedTraceCarrier (N : FramedNode S) (n r : ℕ) (F : FacetFlag S N.ty)
    (a : TracePiece N.ty F r) : Set (E d) := tracePlacement N n r '' a.carrier

open private exists_honest_step7_descendant_scaled from Enforce.Tiling in

/-- P17, V4 1.22(a): every recorded named cell is carried to the corresponding
cell of the actual owner node, at its actual height. -/
theorem placedTraceOwner_cells (N : FramedNode S) (n r : ℕ) (hr : r ≤ n)
    (F : FacetFlag S N.ty) (a : TracePiece N.ty F r) (e : Cell d) :
    (placedTraceOwner N n r F a).cell (n - r) e =
      tracePlacement N n r '' (a.tile.cell 0 e) := by
  dsimp [placedTraceOwner, tracePlacement, FramedNode.cell, FramedNode.prototypeFrame, FramedNode.move]
  ext x
  simp
  constructor
  · rintro ⟨y, hy, rfl⟩
    use y
    refine ⟨hy, ?_⟩
    change N.frame ((S.σ ^ (n - r)) (a.tile.frame y)) = N.frame ((S.descendantNode N.ty (n - r) r a.owner).frame ((S.σ ^ (n - r)) y))
    apply congrArg
    dsimp [TracePiece.tile, SubstSystem.nativeTile]
    symm
    exact exists_honest_step7_descendant_scaled N.ty (n - r) r a.owner y
  · rintro ⟨y, hy, rfl⟩
    use y
    refine ⟨hy, ?_⟩
    change N.frame ((S.descendantNode N.ty (n - r) r a.owner).frame ((S.σ ^ (n - r)) y)) = N.frame ((S.σ ^ (n - r)) (a.tile.frame y))
    apply congrArg
    dsimp [TracePiece.tile, SubstSystem.nativeTile]
    exact exists_honest_step7_descendant_scaled N.ty (n - r) r a.owner y

open private hereditary_trace_step1_relint_image from Enforce.Source.Trace in
/-- P17, V4 1.22(a): recursive traces tile the prescribed cell of every placed
node, with disjoint relative interiors, for every permitted subdivision depth. -/
theorem placed_recursiveTrace_tiles (N : FramedNode S) (n r : ℕ) (hr : r ≤ n)
    (F : FacetFlag S N.ty) :
    (⋃ a : TracePiece N.ty F r, placedTraceCarrier N n r F a) =
      N.cell n (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val ∧
    Pairwise (fun a b : TracePiece N.ty F r =>
      Disjoint (relint (placedTraceCarrier N n r F a))
        (relint (placedTraceCarrier N n r F b))) := by
  have H := recursiveTrace_tiles N.ty F r
  have h1 : (⋃ a : TracePiece N.ty F r, placedTraceCarrier N n r F a) =
    (⋃ a : TracePiece N.ty F r, tracePlacement N n r '' a.carrier) := rfl
  have h_rec_eq : (⋃ (a : TracePiece N.ty F r), a.carrier) = ⋃ a ∈ recursiveTrace N.ty F r, a.carrier := by
    ext x; simp [recursiveTrace]
  have h2 : (⋃ (a : TracePiece N.ty F r), a.carrier) = (S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.carrier := by
    rw [h_rec_eq]
    exact H.1
  constructor
  · rw [h1, ← Set.image_iUnion, h2]
    unfold tracePlacement
    unfold FramedNode.cell
    dsimp [FramedNode.prototypeFrame]
    ext x
    simp only [Set.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      use z
      refine ⟨hz, ?_⟩
      have h3 : (S.σ ^ (n - r)) ((S.σ ^ r) z) = (S.σ ^ n) z := by
        change ((S.σ ^ (n - r)) * (S.σ ^ r)) z = _
        rw [← pow_add]
        have h_add : n - r + r = n := Nat.sub_add_cancel hr
        rw [h_add]
      rw [h3]
    · rintro ⟨y, hy, rfl⟩
      use (S.σ ^ r) y
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      have h3 : (S.σ ^ (n - r)) ((S.σ ^ r) y) = (S.σ ^ n) y := by
        change ((S.σ ^ (n - r)) * (S.σ ^ r)) y = _
        rw [← pow_add]
        have h_add : n - r + r = n := Nat.sub_add_cancel hr
        rw [h_add]
      rw [h3]
  · intro a b hab
    have H_disj := H.2.1 hab
    unfold placedTraceCarrier
    have h_relint1 : relint (tracePlacement N n r '' a.carrier) = tracePlacement N n r '' relint a.carrier := by
      exact hereditary_trace_step1_relint_image (tracePlacement N n r) a.carrier
    have h_relint2 : relint (tracePlacement N n r '' b.carrier) = tracePlacement N n r '' relint b.carrier := by
      exact hereditary_trace_step1_relint_image (tracePlacement N n r) b.carrier
    rw [h_relint1, h_relint2]
    exact Set.disjoint_image_of_injective (tracePlacement N n r).injective H_disj

/-- P17, V4 1.22(a): a selected trace owner is an actual node of the fixed
coherent hierarchy, rather than merely a congruent tile in an unrelated source. -/
theorem CoherentHierarchy.placedTraceOwner_mem {T : Tiling S}
    (H : CoherentHierarchy S T) (N : FramedNode S) (n r : ℕ)
    (hN : N ∈ H.nodes n) (hr : r ≤ n) (F : FacetFlag S N.ty)
    (a : TracePiece N.ty F r) : placedTraceOwner N n r F a ∈ H.nodes (n - r) := by
  dsimp [placedTraceOwner]
  have h_eq : n = (n - r) + r := by omega
  have hN' : N ∈ H.nodes ((n - r) + r) := by rwa [← h_eq]
  exact coarsen_desc_mem H (n - r) r N hN' a.owner

open private exists_honest_step7_descendant_type from Enforce.Tiling in
/-- P18, V4 1.23(c): persistence in one placed source node, at every deeper
subdivision still available in that node. The same ambient point is used at each
depth; scale normalization changes the native coordinates, not the point itself. -/
theorem placed_site_listed (N : FramedNode S) (n r r' : ℕ)
    (hrr' : r ≤ r') (hr'n : r' ≤ n) (F : FacetFlag S N.ty) (q : E d)
    (hq : IsSite N.ty F r q) (a : TracePiece N.ty F r')
    (ha : tracePlacement N n r q ∈ placedTraceCarrier N n r' F a) :
    (placedTraceOwner N n r' F a).Lists (n - r') (tracePlacement N n r q) := by
  obtain ⟨s, rfl⟩ : ∃ s, r' = r + s := ⟨r' - r, by omega⟩
  have hplace : tracePlacement N n (r + s) ((S.σ ^ s) q) =
      tracePlacement N n r q := by
    change N.frame ((S.σ ^ (n - (r + s))) ((S.σ ^ s) q)) =
      N.frame ((S.σ ^ (n - r)) q)
    apply congrArg N.frame
    change ((S.σ ^ (n - (r + s))) * (S.σ ^ s)) q = _
    rw [← pow_add, show n - (r + s) + s = n - r by omega]
  have hqa : (S.σ ^ s) q ∈ a.carrier := by
    obtain ⟨x, hx, heq⟩ := ha
    have hxeq : x = (S.σ ^ s) q :=
      (tracePlacement N n (r + s)).injective (heq.trans hplace.symm)
    exact hxeq ▸ hx
  obtain ⟨v, hv, hqv, -⟩ := site_listed N.ty F r q hq s a hqa
  have hty : (placedTraceOwner N n (r + s) F a).ty = a.tile.ty := by
    exact exists_honest_step7_descendant_type N.ty (n - (r + s)) (r + s) a.owner
  refine ⟨v, ?_, ?_⟩
  · rw [hty]
    exact hv
  · rw [placedTraceOwner_cells N n (r + s) hr'n F a v]
    exact ⟨(S.σ ^ s) q, hqv, hplace⟩

end Enforce
