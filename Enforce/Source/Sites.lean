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
  sorry

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

/-- P18, V4 1.23(a): arbitrarily many ordinary sites occur from some depth on.
The sites in the finite witness set are distinct; expansion provides the length. -/
theorem sites_exist (A : S.ι) (F : FacetFlag S A) (N : ℕ) (hN : 1 ≤ N) :
    ∃ r : ℕ, ∀ r' : ℕ, r ≤ r' →
      ∃ q : Finset (E d), N ≤ q.card ∧ ∀ p ∈ q, IsSite A F r' p := by
  sorry

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

/-- P18, V4 1.23(b): finitely many positioned selected-owner fan templates. -/
theorem site_fan_finite (S : SubstSystem d) : (siteTemplates S).Finite := by
  sorry

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
