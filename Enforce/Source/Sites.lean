import Enforce.Source.Headers
import Enforce.Source.Edges

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- Step 3 of the V4 proof of `sites_exist` (V4 1.23(a), fan paragraph):
"At such a change `q`, the adjacent trace polygons have distinct owners. For `d ≥ 3`,
near `q` the two-dimensional flag cell is a half-plane ... Thus all trace polygons
through `q` list it as a vertex. Their finite fan has different extreme members, so
some separating edge enters the half-disc: this is the required inward arm. In `d = 2`
the same argument uses the native tiles in the half-disc inside the node." -/
private theorem sites_exist_step3_inward_arm (A : S.ι) (F : FacetFlag S A) (r : ℕ)
    (q : E d) (hq : sitesExistOwnerChange A F r q) : InwardTraceArm A F r q := by
  sorry

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
  sorry

/-- P18, V4 1.23(c): every deeper trace polygon meeting a fixed site lists it,
as does its selected owner. Native-scale positions are compared by `σˢ`. -/
theorem site_listed (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d)
    (hq : IsSite A F r q) (s : ℕ) (a : TracePiece A F (r + s))
    (ha : (S.σ ^ s) q ∈ a.carrier) :
    ∃ v ∈ (S.cx a.tile.ty).vertices,
      (S.σ ^ s) q ∈ a.tile.cell 0 v ∧ a.tile.cell 0 v ⊆ a.carrier := by
  sorry

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

/-- P17, V4 1.22(a): every recorded named cell is carried to the corresponding
cell of the actual owner node, at its actual height. -/
theorem placedTraceOwner_cells (N : FramedNode S) (n r : ℕ) (hr : r ≤ n)
    (F : FacetFlag S N.ty) (a : TracePiece N.ty F r) (e : Cell d) :
    (placedTraceOwner N n r F a).cell (n - r) e =
      tracePlacement N n r '' (a.tile.cell 0 e) := by
  sorry

/-- P17, V4 1.22(a): recursive traces tile the prescribed cell of every placed
node, with disjoint relative interiors, for every permitted subdivision depth. -/
theorem placed_recursiveTrace_tiles (N : FramedNode S) (n r : ℕ) (hr : r ≤ n)
    (F : FacetFlag S N.ty) :
    (⋃ a : TracePiece N.ty F r, placedTraceCarrier N n r F a) =
      N.cell n (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val ∧
    Pairwise (fun a b : TracePiece N.ty F r =>
      Disjoint (relint (placedTraceCarrier N n r F a))
        (relint (placedTraceCarrier N n r F b))) := by
  sorry

/-- P17, V4 1.22(a): a selected trace owner is an actual node of the fixed
coherent hierarchy, rather than merely a congruent tile in an unrelated source. -/
theorem CoherentHierarchy.placedTraceOwner_mem {T : Tiling S}
    (H : CoherentHierarchy S T) (N : FramedNode S) (n r : ℕ)
    (hN : N ∈ H.nodes n) (hr : r ≤ n) (F : FacetFlag S N.ty)
    (a : TracePiece N.ty F r) : placedTraceOwner N n r F a ∈ H.nodes (n - r) := by
  sorry

/-- P18, V4 1.23(c): persistence in one placed source node, at every deeper
subdivision still available in that node. The same ambient point is used at each
depth; scale normalization changes the native coordinates, not the point itself. -/
theorem placed_site_listed (N : FramedNode S) (n r r' : ℕ)
    (hrr' : r ≤ r') (hr'n : r' ≤ n) (F : FacetFlag S N.ty) (q : E d)
    (hq : IsSite N.ty F r q) (a : TracePiece N.ty F r')
    (ha : tracePlacement N n r q ∈ placedTraceCarrier N n r' F a) :
    (placedTraceOwner N n r' F a).Lists (n - r') (tracePlacement N n r q) := by
  sorry

end Enforce
