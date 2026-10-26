import Enforce.State.Packets

/-!
# CONT and END event rows

Q12--Q14, V4 §2.5 and Lemma 2.8. Geometry comes from honest positioned
configurations. Leaf labels range independently over the finite honest leaf-type
alphabet, with matching prototype types; the rows impose their correlations.

DEVIATION: a restriction path records the inherited facet at each role step as
well as the role word. A role word alone does not specify which facet to restrict.
The annotation is the resulting total function on the finite facet-record alphabet.
Its values on records of a different source facet are immaterial and are totalized
by the identity. On the source facet every field follows V4 2.3, inherited case.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

attribute [local instance] Classical.decEq

/-- Q13, V4 §2.5 (annotation): the entire raw (S4) alphabet is finite.
This claim concerns facet records, which have no header cones, not whole states. -/
theorem facetRecords_finite (P : Params S) : Finite (FacetRecord P) := by
  sorry

/-- Q12/Q13, V4 §2.5: read a record using a listed cell name, without dependent casts. -/
def stateRecordAt {P : Params S} (s : State P) (f : Cell d) : Option (FacetRecord P) := by
  classical
  exact if hf : f ∈ (S.cx s.ty).facets then s.facetRecord ⟨f, hf⟩ else none

/-- Q12/Q13, V4 §2.5: record of a labelled native tile's named facet. -/
def leafRecord {P : Params S} (l : LeafType P) (f : Cell d) : Option (FacetRecord P) :=
  stateRecordAt l.prePattern.state f

/-- Q12/Q13, V4 §2.5: packet of a labelled native tile's named facet. -/
def leafPacket {P : Params S} (l : LeafType P) (f : Cell d) : Option (Packet P) := by
  classical
  exact if hf : f ∈ (S.cx l.prePattern.ty).facets then
    l.prePattern.packets ⟨f, hf⟩ else none

/-- Q13, V4 §2.5: header of a labelled native tile at a named vertex-facet pair. -/
def leafHeader {P : Params S} (l : LeafType P) (v f : Cell d) :
    Option (State.Header P) := by
  classical
  let s := l.prePattern.state
  exact if hv : v ∈ (S.cx s.ty).vertices then
    if hf : f ∈ (S.cx s.ty).facets then s.header ⟨v, hv⟩ ⟨f, hf⟩ else none
    else none

/-- Q13, V4 §2.5 (E5): the head's E relation on named facets. -/
def stateEAt {P : Params S} (s : State P) (f g : Cell d) : Prop :=
  ∃ (hf : f ∈ (S.cx s.ty).facets) (hg : g ∈ (S.cx s.ty).facets),
    s.E ⟨f, hf⟩ ⟨g, hg⟩

namespace FacetRecord

variable {P : Params S} (r : FacetRecord P)

/-- Q12/Q13, V4 §2.5: stratum readout on a named cell, absent off the facet. -/
def tauAt (e : Cell d) : Option (Cell d) := by
  classical
  exact if he : e ∈ (S.cx r.ty).cells then
    if hs : e.carrier ⊆ r.facet.val.carrier then some (r.tau ⟨⟨e, he⟩, hs⟩).val.val
      else none
    else none

/-- Q13, V4 §2.5: chain data carry no continuous orientation choices. -/
theorem chain_cell_subset (c : OrientedChain r.facet) (j : FlagIndex d) :
    (c.chain.val.cell j).val.carrier ⊆ r.facet.val.carrier := by
  have h := c.chain.val.nested j facetIndex (by
    change j.val ≤ d - 1
    have := j.property.2
    omega)
  simpa only [c.chain.property] using h

end FacetRecord

/-- Q12/Q13, V4 §2.5: a chain's oriented edge vector in its own prototype. -/
def chainVector {A : S.ι} {f : FacetName S A} (c : OrientedChain f) : E d :=
  let e : EdgeName S := ⟨A, ⟨(c.chain.val.cell edgeIndex).val, by
    classical
    simp only [CellComplex.edges, Finset.mem_filter]
    exact ⟨(c.chain.val.cell edgeIndex).property, c.chain.val.dimension edgeIndex⟩⟩⟩
  if c.forward then edgeVector e else -edgeVector e

/-- Q13, V4 2.3 (inherited case): containing-cell lookup in the fixed substitution.
This is the normalized instance of the existing `ancestralStratum` API. -/
theorem inheritedCell_exists {P : Params S} (r : FacetRecord P) (i : S.I r.ty)
    (g : FacetName S (S.child r.ty i).ty)
    (h : placedSet (S.child r.ty i).frame g.val.carrier ⊆ S.σ '' r.facet.val.carrier)
    (e : CellsInFacet (S.child r.ty i).ty g) :
    ∃! t : CellsInFacet r.ty r.facet,
      relint (placedSet (S.child r.ty i).frame e.val.val.carrier) ⊆
        relint (S.σ '' t.val.val.carrier) := by
  sorry

/-- Q13, V4 2.3: actual deterministic immediate containing-cell lookup. -/
def inheritedCell {P : Params S} (r : FacetRecord P) (i : S.I r.ty)
    (g : FacetName S (S.child r.ty i).ty)
    (h : placedSet (S.child r.ty i).frame g.val.carrier ⊆ S.σ '' r.facet.val.carrier)
    (e : CellsInFacet (S.child r.ty i).ty g) : CellsInFacet r.ty r.facet :=
  Classical.choose (inheritedCell_exists r i g h e)

/-- Q13, V4 2.3 (active chains): full-chain inheritance, with induced orientation.
No edge is declared active by an isolated one-dimensional stratum test. -/
def InheritedChain {P : Params S} (r : FacetRecord P) (i : S.I r.ty)
    (g : FacetName S (S.child r.ty i).ty)
    (h : placedSet (S.child r.ty i).frame g.val.carrier ⊆ S.σ '' r.facet.val.carrier)
    (c : OrientedChain g) : Prop :=
  ∃ c₀ ∈ r.chains,
    (∀ j, ∃ hs : (c.chain.val.cell j).val.carrier ⊆ g.val.carrier,
      (inheritedCell r i g h ⟨c.chain.val.cell j, hs⟩).val.val =
        (c₀.chain.val.cell j).val) ∧
    0 < inner ℝ ((S.child r.ty i).rotation (chainVector c)) (S.σ (chainVector c₀))

/-- Q13, V4 2.3 (active chains): the child's finite oriented-chain table. -/
def restrictedChains {P : Params S} (r : FacetRecord P) (i : S.I r.ty)
    (g : FacetName S (S.child r.ty i).ty)
    (h : placedSet (S.child r.ty i).frame g.val.carrier ⊆ S.σ '' r.facet.val.carrier) :
    Finset (OrientedChain g) := by
  classical
  exact (allOrientedChains g).filter (InheritedChain r i g h)

/-- Q13, V4 2.3 (profile lookup): restrict a shallow role word to mature constants.
The extended role word places each child cell in the original serving prototype. -/
def wordConstants {P : Params S} (r : FacetRecord P) (i : S.I r.ty)
    (g : FacetName S (S.child r.ty i).ty) (chains : Finset (OrientedChain g))
    (word : List S.Role) : ConstantProfile P (S.child r.ty i).ty := by
  classical
  exact {
    value := fun e => if ∃ c ∈ chains, (c.chain.val.cell edgeIndex).val = e.val then
      some ⟨(Finset.univ.filter (fun a : Fin P.N => inner ℝ r.servingDirection
        (P.sites r.incidence r.sideIndex a - wordPlacement word (cellAnchor e.val)) < 0)).card,
        by
          have hle := Finset.card_le_card
            (Finset.filter_subset (fun a : Fin P.N => inner ℝ r.servingDirection
              (P.sites r.incidence r.sideIndex a - wordPlacement word (cellAnchor e.val)) < 0)
              Finset.univ)
          simp only [Finset.card_univ, Fintype.card_fin] at hle
          omega⟩
      else none
    endpointSite := fun v => if ∃ c ∈ chains,
        vertexPoint v ∈ (c.chain.val.cell edgeIndex).val.carrier then
      some ((Finset.univ : Finset (Fin P.N)).toList.any (fun a =>
        decide (P.sites r.incidence r.sideIndex a = wordPlacement word (vertexPoint v))))
      else none }

/-- Q13, V4 2.3 (constant profile): constants inherit along the containing edge;
old endpoint site flags inherit, while a newly created vertex is not a site. -/
def inheritedConstants {P : Params S} (r : FacetRecord P) (i : S.I r.ty)
    (g : FacetName S (S.child r.ty i).ty)
    (h : placedSet (S.child r.ty i).frame g.val.carrier ⊆ S.σ '' r.facet.val.carrier)
    (c₀ : ConstantProfile P r.ty) : ConstantProfile P (S.child r.ty i).ty := by
  classical
  let chains := restrictedChains r i g h
  exact {
    value := fun e => if ha : ∃ c ∈ chains, (c.chain.val.cell edgeIndex).val = e.val then
      if hs : e.val.carrier ⊆ g.val.carrier then
        c₀.value (inheritedCell r i g h ⟨e, hs⟩).val else none
      else none
    endpointSite := fun v => if ∃ c ∈ chains,
        vertexPoint v ∈ (c.chain.val.cell edgeIndex).val.carrier then
      some (if hv : ∃ v₀ : VertexName S r.ty,
          S.σ (vertexPoint v₀) = (S.child r.ty i).frame (vertexPoint v) then
        (c₀.endpointSite (Classical.choose hv)).getD false else false)
      else none }

/-- Q13, V4 2.3 (counter profile): append the child role while shallow, convert
by finite site lookup at depth r, and inherit constants once already mature. -/
def restrictedCounter {P : Params S} (r : FacetRecord P) (i : S.I r.ty)
    (g : FacetName S (S.child r.ty i).ty)
    (h : placedSet (S.child r.ty i).frame g.val.carrier ⊆ S.σ '' r.facet.val.carrier) :
    ConstantProfile P (S.child r.ty i).ty ⊕ ShortProfile P := by
  classical
  exact match r.counter with
  | .inl c => .inl (inheritedConstants r i g h c)
  | .inr w =>
    let word := w.word ++ [⟨r.ty, i⟩]
    if hw : word.length < P.siteDepth r.incidence r.sideIndex then
      .inr ⟨word, lt_trans hw (P.siteDepth_lt _ _)⟩
    else .inl (wordConstants r i g (restrictedChains r i g h) word)

/-- Q13, V4 2.3 (inherited case): one genuine facet-record restriction step.
Incidence, side and beta are unchanged; age increments with cap; tau composes with
the immediate containing-cell lookup; full chains and both profile branches restrict. -/
def restrictOne {P : Params S} (r : FacetRecord P) (i : S.I r.ty)
    (g : FacetName S (S.child r.ty i).ty)
    (h : placedSet (S.child r.ty i).frame g.val.carrier ⊆ S.σ '' r.facet.val.carrier) :
    FacetRecord P where
  ty := (S.child r.ty i).ty
  facet := g
  incidence := r.incidence
  sideIndex := r.sideIndex
  side := r.side
  side_eq := r.side_eq
  age := ⟨min (r.age.val + 1) P.C, by omega⟩
  beta := r.beta
  tau := fun e => r.tau (inheritedCell r i g h e)
  chains := restrictedChains r i g h
  counter := restrictedCounter r i g h

/-- Q13, V4 §2.5 (restriction annotation): a named inherited step of a role word.
Source and target facet names remove any ambiguity about which track is followed. -/
structure RestrictionStep (S : SubstSystem d) where
  /-- Q13, V4 §2.5: globally distinct downward child role. -/
  role : S.Role
  /-- Q13, V4 §2.5: parent boundary facet. -/
  source : FacetName S role.1
  /-- Q13, V4 §2.5: child facet inherited from it. -/
  target : FacetName S (S.child role.1 role.2).ty
  /-- Q13, V4 1.7(c), 2.3: actual inherited containment in the standard subdivision. -/
  inherited : placedSet (S.child role.1 role.2).frame target.val.carrier ⊆
    S.σ '' source.val.carrier

/-- Q13, V4 §2.5: a total restriction step on the common finite record alphabet.
Only matching source facets are restricted. The identity on other inputs is the
explicit totalization convention; those values are never read by an END row. -/
def RestrictionStep.apply {P : Params S} (a : RestrictionStep S) (r : FacetRecord P) :
    FacetRecord P := by
  classical
  exact if hm : ∃ (i : S.I r.ty) (g : FacetName S (S.child r.ty i).ty),
      (⟨r.ty, i⟩ : S.Role) = a.role ∧ r.facet.val = a.source.val ∧
        g.val = a.target.val ∧
        placedSet (S.child r.ty i).frame g.val.carrier ⊆ S.σ '' r.facet.val.carrier then
    let i := Classical.choose hm
    let g := Classical.choose (Classical.choose_spec hm)
    restrictOne r i g (Classical.choose_spec (Classical.choose_spec hm)).2.2.2
    else r

/-- Q13, V4 §2.5: annotation operator, by recursion along the downward role path.
The path's `map RestrictionStep.role` is the role word. No operator is postulated. -/
def restrictionOp {P : Params S} : List (RestrictionStep S) → FacetRecord P → FacetRecord P
  | [], r => r
  | a :: as, r => restrictionOp as (a.apply r)

/-- Q13, V4 §2.5: operator composition follows concatenation of role paths. -/
theorem restrictionOp_append {P : Params S} (a b : List (RestrictionStep S))
    (r : FacetRecord P) : restrictionOp (a ++ b) r = restrictionOp b (restrictionOp a r) := by
  induction a generalizing r with
  | nil => rfl
  | cons x xs ih => exact ih (x.apply r)

/-- Q13, V4 §2.5: finite operator alphabet, even for arbitrarily long role paths. -/
theorem restrictionOps_finite (P : Params S) :
    (Set.range (fun a : List (RestrictionStep S) =>
      (restrictionOp a : FacetRecord P → FacetRecord P))).Finite := by
  sorry

/-- Q13, V4 §2.5: a complete named path follows the actual downward roles,
starts at F, ends at f, and matches intermediate facets. Every step is inherited. -/
def SourceRestrictionPath (U : HonestSource S) (B t : U.Node)
    (F : FacetName S B.2.val.ty) (f : FacetName S t.2.val.ty)
    (path : List (RestrictionStep S)) : Prop :=
  t.1 < B.1 ∧ U.hierarchy.ancestor t (B.1 - t.1) = B ∧
    path.length = B.1 - t.1 ∧ path.map RestrictionStep.role = U.downRoles t (B.1 - t.1) ∧
    path.head?.map (fun a => a.source.val) = some F.val ∧
    path.getLast?.map (fun a => a.target.val) = some f.val ∧
    path.IsChain (fun a b => (S.child a.role.1 a.role.2).ty = b.role.1 ∧
      a.target.val = b.source.val)

/-- Q13, V4 §2.5: the inherited facet path exists in every actual boundary track.
Existence follows by iterating the existing V4 1.7(c) restriction geometry. -/
theorem sourceRestrictionPath_exists (U : HonestSource S) (B t : U.Node)
    (hlt : t.1 < B.1) (hanc : U.hierarchy.ancestor t (B.1 - t.1) = B)
    (F : FacetName S B.2.val.ty) (f : FacetName S t.2.val.ty)
    (hsub : t.2.val.cell t.1 f.val ⊆ B.2.val.cell B.1 F.val) :
    ∃ path : List (RestrictionStep S), SourceRestrictionPath U B t F f path := by
  sorry

/-- Q13, V4 §2.5: annotation agrees with the actual inherited record whenever finite.
This is V4 2.3's inherited case iterated along the explicit source role path. -/
theorem restrictionOp_source (U : HonestSource S) (P : Params S) (B t : U.Node)
    (F : FacetName S B.2.val.ty) (f : FacetName S t.2.val.ty)
    (hF : ¬ U.hierarchy.IsFault B F) (hf : ¬ U.hierarchy.IsFault t f)
    (path : List (RestrictionStep S)) (hp : SourceRestrictionPath U B t F f path) :
    restrictionOp path (U.recordOf P B F hF) = U.recordOf P t f hf := by
  sorry

/-- Q13, V4 §2.5: all native B-owned nodes incident to an ambient point.
The ancestor equality specifies ownership, including zero-trace sectors. -/
def ownedStarSet (U : HonestSource S) (B : U.Node) (x : E d) : Set U.Node :=
  {q | q.1 = 0 ∧ U.hierarchy.ancestor q B.1 = B ∧ x ∈ q.2.val.carrier q.1}

/-- Q13, V4 §2.5, 1.18: a complete owned star is finite at every occurrence. -/
theorem ownedStarSet_finite (U : HonestSource S) (B : U.Node) (x : E d) :
    (ownedStarSet U B x).Finite := by
  sorry

/-- Q13, V4 §2.5: the actual complete finite B-owned star. -/
def ownedStar (U : HonestSource S) (B : U.Node) (x : E d) : Finset U.Node :=
  (ownedStarSet_finite U B x).toFinset

/-- Q13, V4 §2.5: a port on a first-generation facet of the birth parent. -/
structure PrimitivePort (P : Params S) where
  /-- Q13, V4 §2.5: positioned native tile. -/
  tile : FramedNode S
  /-- Q13, V4 §2.5: its port facet. -/
  facet : FacetName S tile.ty
  /-- Q13, V4 §2.5: its listed vertex at the event point. -/
  vertex : VertexName S tile.ty
  /-- Q13, V4 §2.5: the vertex lies on the port. -/
  onFacet : vertex.val.carrier ⊆ facet.val.carrier
  /-- Q13, V4 §2.5 (E1): geometry-dictated first-generation incidence. -/
  incidence : P.Incidence
  /-- Q13, V4 §2.5 (E1): index of the geometry-dictated serving side. -/
  sideIndex : Bool
  /-- Q13, V4 §2.5 (E1): geometry-dictated globally distinct serving role. -/
  side : S.Role
  /-- Q13, V4 §2.5 (E1): the role names the selected side of the incidence. -/
  side_eq : side = incidence.val.sideRole sideIndex
  /-- Q13, V4 §2.5 (E1): geometry-dictated provider vertex in the common complex. -/
  providerVertex : ProviderCell incidence.val
  /-- Q13, V4 §2.5 (E1): this is a vertex, not an edge-stratum port. -/
  provider_zero : providerVertex.val.val.dim = 0

/-- Q13, V4 §2.5: a port on a boundary facet of the birth parent, with annotation. -/
structure BoundaryPort (P : Params S) (A : S.ι) where
  /-- Q13, V4 §2.5: positioned native tile. -/
  tile : FramedNode S
  /-- Q13, V4 §2.5: its port facet. -/
  facet : FacetName S tile.ty
  /-- Q13, V4 §2.5: its listed vertex at the event point. -/
  vertex : VertexName S tile.ty
  /-- Q13, V4 §2.5: the vertex lies on the port facet. -/
  onFacet : vertex.val.carrier ⊆ facet.val.carrier
  /-- Q13, V4 §2.5: which parent boundary facet contains this port. -/
  parentFacet : FacetName S A
  /-- Q13, V4 §2.5 (annotation): the composed restriction function. -/
  restriction : FacetRecord P → FacetRecord P

/-- Q13, V4 §2.5: full positioned geometry and its finite annotation, before labels.
The complete honest geometry catalogue is specified by `EndGeometryRealizes`.
Arbitrary values of this raw structure do not enter that catalogue. -/
structure EndGeometry (P : Params S) where
  /-- Q13, V4 §2.5: prototype of the distinguished native tile. -/
  centralType : S.ι
  /-- Q13, V4 §2.5: event vertex in the central prototype frame. -/
  vertex : VertexName S centralType
  /-- Q13, V4 §2.5: the complete provider-zero header in that frame. -/
  header : State.Header P
  /-- Q13, V4 §2.5: every B-owned native tile incident to the event point. -/
  tiles : Finset (FramedNode S)
  /-- Q13, V4 §2.5: the central tile is in its identity frame. -/
  central_mem : (⟨centralType, AffineIsometryEquiv.refl ℝ (E d)⟩ : FramedNode S) ∈ tiles
  /-- Q13, V4 §2.5: interiors of distinct positioned tiles are disjoint. -/
  disjoint : (tiles : Set (FramedNode S)).PairwiseDisjoint (fun u => interior (u.carrier 0))
  /-- Q13, V4 §2.5: all tiles list the common event point. -/
  listed : ∀ u ∈ tiles, u.Lists 0 (vertexPoint vertex)
  /-- Q13, V4 §2.5: every first-generation port, on both sides. -/
  primitivePorts : Finset (PrimitivePort P)
  /-- Q13, V4 §2.5: every boundary port, including multiple ports on one facet. -/
  boundaryPorts : Finset (BoundaryPort P header.birthType)
  /-- Q13, V4 §2.5: primitive ports belong to actual template tiles. -/
  primitive_tiles : ∀ a ∈ primitivePorts, a.tile ∈ tiles
  /-- Q13, V4 §2.5: boundary ports belong to actual template tiles. -/
  boundary_tiles : ∀ a ∈ boundaryPorts, a.tile ∈ tiles
  /-- Q13, V4 §2.5: every primitive port is anchored at the physical event point. -/
  primitive_anchor : ∀ a ∈ primitivePorts, a.tile.frame (vertexPoint a.vertex) =
    vertexPoint vertex
  /-- Q13, V4 §2.5: every boundary port is anchored at the same physical point. -/
  boundary_anchor : ∀ a ∈ boundaryPorts, a.tile.frame (vertexPoint a.vertex) =
    vertexPoint vertex

/-- Q13, V4 §2.5: source meaning of a first-generation port.
It uses only actual geometry, provider names and canonical strata, not leaf labels. -/
def IsSourcePrimitivePort (U : HonestSource S) (P : Params S) (t : U.Node)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (a : PrimitivePort P) : Prop :=
  let B := U.hierarchy.birthParent t f hf
  let x := t.2.val.prototypeFrame t.1 (vertexPoint v)
  ∃ q ∈ ownedStar U B x, ∃ (g : FacetName S q.2.val.ty)
    (hg : ¬ U.hierarchy.IsFault q g) (w : VertexName S q.2.val.ty)
    (hw : w.val.carrier ⊆ g.val.carrier),
    x = q.2.val.prototypeFrame q.1 (vertexPoint w) ∧
    U.hierarchy.birthParent q g hg = B ∧
    a.tile = q.2.val.move t.2.val.frame.symm ∧ a.facet.val = g.val ∧ a.vertex.val = w.val ∧
    a.incidence = U.recordIncidence P q g hg ∧ a.sideIndex = U.recordSide P q g hg ∧
    a.providerVertex.val.val = (U.recordTau P q g hg ⟨vertexCell w, hw⟩).val.val

/-- Q13, V4 §2.5: source meaning of an annotated boundary port.
All named inherited paths realizing this occurrence are allowed; their annotation
is the actual recursively composed restriction function, not an arbitrary function. -/
def IsSourceBoundaryPort {A : S.ι} (U : HonestSource S) (P : Params S) (t : U.Node)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (a : BoundaryPort P A) : Prop :=
  let B := U.hierarchy.birthParent t f hf
  let x := t.2.val.prototypeFrame t.1 (vertexPoint v)
  ∃ q ∈ ownedStar U B x, ∃ (F : FacetName S B.2.val.ty)
    (g : FacetName S q.2.val.ty) (w : VertexName S q.2.val.ty),
    w.val.carrier ⊆ g.val.carrier ∧ x = q.2.val.prototypeFrame q.1 (vertexPoint w) ∧
    q.2.val.cell q.1 g.val ⊆ B.2.val.cell B.1 F.val ∧
    a.tile = q.2.val.move t.2.val.frame.symm ∧ a.facet.val = g.val ∧ a.vertex.val = w.val ∧
    a.parentFacet.val = F.val ∧ ∃ path : List (RestrictionStep S),
      SourceRestrictionPath U B q F g path ∧ a.restriction = restrictionOp path

/-- Q13, V4 §2.5: exact realization of the complete annotated star in the central frame.
The two biconditionals require every geometric port, including zero-trace sectors;
no selection of a proper subset of the star is permitted. -/
def EndGeometryRealizes (U : HonestSource S) (P : Params S) (t : U.Node)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (G : EndGeometry P) : Prop :=
  G.centralType = t.2.val.ty ∧ G.vertex.val = v.val ∧ G.header = U.headerOf P t f hf v ∧
    G.tiles = (ownedStar U (U.hierarchy.birthParent t f hf)
      (t.2.val.prototypeFrame t.1 (vertexPoint v))).image
        (fun q => q.2.val.move t.2.val.frame.symm) ∧
    (∀ a, a ∈ G.primitivePorts ↔ IsSourcePrimitivePort U P t f hf v a) ∧
    ∀ a, a ∈ G.boundaryPorts ↔ IsSourceBoundaryPort U P t f hf v a

/-- Q13, V4 §2.5, 1.17--1.18: every provider-zero occurrence has its complete
annotated positioned geometry. Nonemptiness is supplied by that actual occurrence. -/
theorem endGeometry_exists (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (hv : v.val.carrier ⊆ f.val.carrier)
    (hz : (U.recordTau P t f hf ⟨vertexCell v, hv⟩).val.val.dim = 0) :
    ∃ G : EndGeometry P, EndGeometryRealizes U P t f hf v G := by
  sorry

/-- Q13, V4 §2.5: all complete honest positioned geometries, with their annotations. -/
def honestEndGeometries (S : SubstSystem d) (P : Params S) : Set (EndGeometry P) :=
  {G | ∃ (U : HonestSource S) (t : U.Node) (_ht : t.1 = 0)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (hv : v.val.carrier ⊆ f.val.carrier),
    (U.recordTau P t f hf ⟨vertexCell v, hv⟩).val.val.dim = 0 ∧
      EndGeometryRealizes U P t f hf v G}

/-- Q13, V4 §2.5, 1.17--1.18: complete annotated END geometries form a finite set.
Finiteness of annotations uses `facetRecords_finite` and `restrictionOps_finite`. -/
theorem endTemplates_finite (S : SubstSystem d) (P : Params S) :
    (honestEndGeometries S P).Finite := by
  sorry

/-- Q13, V4 §2.5, 1.19: one positive native radius works for all END geometries.
The entire parent-cone sector is covered by the complete owned star. -/
theorem endGeometry_coverage (S : SubstSystem d) (P : Params S) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ G ∈ honestEndGeometries S P,
      ((fun u => vertexPoint G.vertex + u) '' G.header.parentCone) ∩
          ball (vertexPoint G.vertex) r₀ ⊆
        ⋃ u ∈ G.tiles, u.carrier 0 := by
  sorry

/-- Q12/Q13, V4 §2.5: finite framed native configuration relative to its central tile.
END annotations are part of template identity, so different restriction operators
on the same positioned star give different annotated templates. -/
structure Template (P : Params S) where
  /-- Q12/Q13, V4 §2.5: the distinguished leaf type. -/
  central : LeafType P
  /-- Q12/Q13, V4 §2.5: positioned native tiles with arbitrary admissible leaf types. -/
  tiles : Finset (FramedNode S × LeafType P)
  /-- Q12/Q13, V4 §2.5: every leaf label matches the positioned prototype. -/
  types_match : ∀ z ∈ tiles, z.1.ty = z.2.prototype
  /-- Q12/Q13, V4 §2.5: all placed native interiors are pairwise disjoint. -/
  disjoint : (tiles : Set (FramedNode S × LeafType P)).PairwiseDisjoint
    (fun z => interior (z.1.carrier 0))
  /-- Q12/Q13, V4 §2.5: the central tile is present in its identity frame. -/
  central_mem : ((⟨central.prototype, AffineIsometryEquiv.refl ℝ (E d)⟩ : FramedNode S),
    central) ∈ tiles
  /-- Q13, V4 §2.5: complete geometry and restriction annotation, absent for CONT. -/
  annotation : Option (EndGeometry P)

/-- Q12, V4 §2.5 (CONT): a facet, a chain-active edge, and its terminal vertex
mapping to the relative interior of the provider flag edge. The side and serving
residue are read from the actual finite record, not supplied as unrelated labels. -/
structure ContSlot {P : Params S} (l : LeafType P) where
  /-- Q12, V4 §2.5: central native facet. -/
  facet : FacetName S l.prototype
  /-- Q12, V4 §2.5: its finite record. -/
  record : FacetRecord P
  /-- Q12, V4 §2.5: the record is read from this central leaf. -/
  record_eq : leafRecord l facet.val = some record
  /-- Q12, V4 §2.5: the record is in the central prototype. -/
  type_eq : record.ty = l.prototype
  /-- Q12, V4 §2.5: the record's facet is the keyed facet. -/
  facet_eq : record.facet.val = facet.val
  /-- Q12, V4 §2.5: a chain-active edge. -/
  edge : PrototypeEdge S record.ty
  /-- Q12, V4 §2.5: activity uses a full chain. -/
  active : record.ChainActive (edgeCell edge)
  /-- Q12, V4 §2.5: the terminal listed vertex in the oriented edge. -/
  vertex : VertexName S record.ty
  /-- Q12, V4 §2.5: the vertex is on the port facet. -/
  onFacet : vertex.val.carrier ⊆ record.facet.val.carrier
  /-- Q12, V4 §2.5: this physical vertex is the terminal endpoint of the edge. -/
  terminal : vertexPoint vertex = (record.endpoints edge).2
  /-- Q12, V4 §2.5: its provider stratum is exactly the open flag edge. -/
  tau_edge : record.tauAt vertex.val =
    some ((P.flag record.incidence).flag.cell edgeIndex).val
  /-- Q12, V4 §2.5: the packet attached to this finite facet. -/
  packet : Packet P
  /-- Q12, V4 §2.5: the packet is the central leaf's readout. -/
  packet_eq : leafPacket l facet.val = some packet

/-- Q13, V4 §2.5 (END): a listed vertex mapping to a provider vertex, with its header.
The packet is the one attached to the same finite central port. -/
structure EndSlot {P : Params S} (l : LeafType P) where
  /-- Q13, V4 §2.5: central facet. -/
  facet : FacetName S l.prototype
  /-- Q13, V4 §2.5: its finite record. -/
  record : FacetRecord P
  /-- Q13, V4 §2.5: the leaf's actual record. -/
  record_eq : leafRecord l facet.val = some record
  /-- Q13, V4 §2.5: the record has the central prototype. -/
  type_eq : record.ty = l.prototype
  /-- Q13, V4 §2.5: the record has the keyed facet. -/
  facet_eq : record.facet.val = facet.val
  /-- Q13, V4 §2.5: listed event vertex. -/
  vertex : VertexName S record.ty
  /-- Q13, V4 §2.5: the vertex lies on the facet. -/
  onFacet : vertex.val.carrier ⊆ record.facet.val.carrier
  /-- Q13, V4 §2.5: its provider vertex in the canonical complex. -/
  providerVertex : ProviderCell record.incidence.val
  /-- Q13, V4 §2.5: the exact provider-zero stratum readout. -/
  tau_vertex : record.tauAt vertex.val = some providerVertex.val.val
  /-- Q13, V4 §2.5: provider stratum has dimension zero. -/
  provider_zero : providerVertex.val.val.dim = 0
  /-- Q13, V4 §2.5: the provider-zero header. -/
  header : State.Header P
  /-- Q13, V4 §2.5: this is the recorded header of the same vertex and facet. -/
  header_eq : leafHeader l vertex.val facet.val = some header
  /-- Q13, V4 §2.5: central non-NULL packet. -/
  packet : Packet P
  /-- Q13, V4 §2.5: central packet readout. -/
  packet_eq : leafPacket l facet.val = some packet

/-- Q12, V4 §2.5 (CONT geometry): full positioned oriented chains agree.
Affine spans, induced edge orientations, successive sides, and the inward tile
sides are all compared in the central prototype frame. -/
def ChainsAligned {P : Params S} (r r' : FacetRecord P)
    (c : OrientedChain r.facet) (c' : OrientedChain r'.facet) (φ : Iso d) : Prop :=
  (∀ j, affineSpan ℝ (c.chain.val.cell j).val.carrier =
    affineSpan ℝ (φ '' (c'.chain.val.cell j).val.carrier)) ∧
  (∀ j, flagSide c.chain.val j = φ.linearIsometryEquiv '' flagSide c'.chain.val j) ∧
    0 < inner ℝ (chainVector c) (φ.linearIsometryEquiv (chainVector c')) ∧
    tangentCone (S.proto r.ty).carrier (cellAnchor r.facet.val) =
      φ.linearIsometryEquiv '' tangentCone (S.proto r'.ty).carrier (cellAnchor r'.facet.val)

/-- Q12, V4 §2.5: a positioned CONT template of one or two native tiles.
The continuation is a physical vertex shared by the two oriented edges, which form
a segment across it. Membership in active-chain tables is checked by the row.
The continuing tile may be the central tile itself: (H2) allows flat listed
vertices, where consecutive listed edges along the flag edge have one owner
(fix after audit A6, F1). `Template.disjoint` then forces equal leaf labels. -/
structure ContTemplate {P : Params S} {l : LeafType P} (slot : ContSlot l) where
  /-- Q12, V4 §2.5: the full positioned labelled configuration. -/
  configuration : Template P
  /-- Q12, V4 §2.5: its distinguished label is the slot's central leaf. -/
  central_eq : configuration.central = l
  /-- Q12, V4 §2.5: the other native tile and its actual frame. -/
  other : FramedNode S
  /-- Q12, V4 §2.5: arbitrary matching admissible leaf label for the other tile. -/
  label : LeafType P
  /-- Q12, V4 §2.5: the continuation tile is present. -/
  other_mem : (other, label) ∈ configuration.tiles
  /-- Q12, V4 §2.5: exactly the central tile and the continuing tile are listed;
  a singleton when the continuation lies in the central tile. -/
  tiles_eq : configuration.tiles =
    {((⟨l.prototype, AffineIsometryEquiv.refl ℝ (E d)⟩ : FramedNode S), l), (other, label)}
  /-- Q12, V4 §2.5: CONT has no END annotation. -/
  annotation_none : configuration.annotation = none
  /-- Q12, V4 §2.5: the finite record of the continuing port. -/
  record : FacetRecord P
  /-- Q12, V4 §2.5: the finite record is actually read from that leaf. -/
  record_eq : leafRecord label record.facet.val = some record
  /-- Q12, V4 §2.5: the record is in the other tile's prototype. -/
  type_eq : record.ty = other.ty
  /-- Q12, V4 §2.5: named full central chain selected by this positioned geometry. -/
  centralChain : OrientedChain slot.record.facet
  /-- Q12, V4 §2.5: the chain starts with the event edge. -/
  central_edge : (centralChain.chain.val.cell edgeIndex).val = slot.edge.val
  /-- Q12, V4 §2.5: named full continuing chain. -/
  otherChain : OrientedChain record.facet
  /-- Q12, V4 §2.5: named continuing edge. -/
  edge : PrototypeEdge S record.ty
  /-- Q12, V4 §2.5: the continuing chain starts with that edge. -/
  other_edge : (otherChain.chain.val.cell edgeIndex).val = edge.val
  /-- Q12, V4 §2.5: the other tile's listed vertex at the junction. -/
  vertex : VertexName S record.ty
  /-- Q12, V4 §2.5: its endpoint is initial in the common orientation. -/
  initial : vertexPoint vertex = (record.endpoints edge).1
  /-- Q12, V4 §2.5: the two names refer to the same physical vertex. -/
  vertex_eq : other.frame (vertexPoint vertex) = vertexPoint slot.vertex
  /-- Q12, V4 §2.5: both full chains lie in the same positioned oriented flag and side. -/
  aligned : ChainsAligned slot.record record centralChain otherChain other.frame
  /-- Q12, V4 §2.5: the two complete edges form one segment across the junction. -/
  segment_eq : slot.edge.val.carrier ∪ placedSet other.frame edge.val.carrier =
    segment ℝ (slot.record.endpoints slot.edge).1 (other.frame (record.endpoints edge).2)
  /-- Q12, V4 §2.5: the physical junction lies strictly between the outer endpoints. -/
  junction_interior : vertexPoint slot.vertex ∈ openSegment ℝ
    (slot.record.endpoints slot.edge).1 (other.frame (record.endpoints edge).2)

/-- Q12, V4 §2.5 (CONT row): equal incidence, side and serving residue; both full
chains recorded active with the induced orientations; counter jump is 0 or 1,
and is 1 exactly when the same physical junction is recorded as a site in both
profiles; the attached packets are equal. Addition avoids truncated subtraction. -/
def contRow {P : Params S} {l : LeafType P} {slot : ContSlot l}
    (T : ContTemplate slot) : Prop :=
  T.record.incidence = slot.record.incidence ∧ T.record.side = slot.record.side ∧
    T.record.beta = slot.record.beta ∧
    T.centralChain ∈ slot.record.chains ∧ T.otherChain ∈ T.record.chains ∧
    ChainsAligned slot.record T.record T.centralChain T.otherChain T.other.frame ∧
    (T.record.kappaMinus T.edge = slot.record.kappaPlus slot.edge ∨
      T.record.kappaMinus T.edge = slot.record.kappaPlus slot.edge + 1) ∧
    (T.record.kappaMinus T.edge = slot.record.kappaPlus slot.edge + 1 ↔
      slot.record.isSite slot.vertex = true ∧ T.record.isSite T.vertex = true) ∧
    leafPacket T.label T.record.facet.val = some slot.packet

/-- Q12, V4 §2.5: finitely many CONT positioned templates, with arbitrary matching
leaf labels. The full oriented flag and inward side fix each relative placement. -/
theorem contTemplates_finite (P : Params S) (l : LeafType P) (slot : ContSlot l) :
    (Set.range (fun T : ContTemplate slot => T.configuration)).Finite := by
  sorry

/-- Q13, V4 §2.5: an END template uses a whole honest positioned annotated star
with the central header, and arbitrary matching admissible leaf labels.
It does not require those labels to be jointly realized in an honest source. -/
structure EndTemplate {P : Params S} {l : LeafType P} (slot : EndSlot l) where
  /-- Q13, V4 §2.5: complete positioned annotated geometry. -/
  geometry : EndGeometry P
  /-- Q13, V4 §2.5: geometry is in the honest catalogue. -/
  honest_geometry : geometry ∈ honestEndGeometries S P
  /-- Q13, V4 §2.5: exactly the central prototype. -/
  type_eq : geometry.centralType = l.prototype
  /-- Q13, V4 §2.5: exactly the central named event vertex. -/
  vertex_eq : geometry.vertex.val = slot.vertex.val
  /-- Q13, V4 §2.5: exactly the central leaf's recorded header. -/
  header_eq : geometry.header = slot.header
  /-- Q13, V4 §2.5: arbitrary prototype-matching leaf assignments on this star. -/
  configuration : Template P
  /-- Q13, V4 §2.5: distinguished leaf type. -/
  central_eq : configuration.central = l
  /-- Q13, V4 §2.5: every geometric tile is assigned a label. -/
  tiles_eq : configuration.tiles.image Prod.fst = geometry.tiles
  /-- Q13, V4 §2.5: annotation remains part of the positioned template identity. -/
  annotation_eq : configuration.annotation = some geometry

/-- Q12/Q13, V4 §2.5: the two kinds of native event slot. -/
inductive EventSlot {P : Params S} (l : LeafType P)
  /-- Q12, V4 §2.5: a continuation slot. -/
  | cont : ContSlot l → EventSlot l
  /-- Q13, V4 §2.5: a provider-zero endpoint slot. -/
  | end_ : EndSlot l → EventSlot l

/-- Q13, V4 §2.5 (E2 alignment): a whole listed chain lies at the event point
in the realized flag planes, with its tangent cones inside the realized flag cones. -/
def ChainFitsTangent {P : Params S} (r : FacetRecord P) (φ : Iso d) (x : E d)
    (F : FlagChain r.facet) (G : State.FlagTangent (d := d)) : Prop :=
  ∀ j, x ∈ placedSet φ (F.val.cell j).val.carrier ∧
    affineSpan ℝ (placedSet φ (F.val.cell j).val.carrier) =
      affineSpan ℝ ((fun u => x + u) '' G.cones j) ∧
    tangentCone (placedSet φ (F.val.cell j).val.carrier) x ⊆ G.cones j

/-- Q13, V4 §2.5 (E2 alignment): the edge points in the flag orientation and
all successive coface sides match the header's realized flag sides. -/
def OrientationFitsTangent {P : Params S} (r : FacetRecord P) (φ : Iso d)
    (c : OrientedChain r.facet) (G : State.FlagTangent (d := d)) : Prop :=
  (if G.initial then φ.linearIsometryEquiv (chainVector c)
    else -φ.linearIsometryEquiv (chainVector c)) ∈ G.cones edgeIndex ∧
    ∀ j, φ.linearIsometryEquiv '' flagSide c.chain.val j = G.sides j

/-- Q13, V4 §2.5 (E1): every port has its geometry-dictated record.
A first-generation port has its dictated incidence and side, its provider-vertex
stratum, and the central serving residue. A boundary port carries the annotated
restriction of the head's record for F, or NULL if that head record is NULL.
Every tile lists the event vertex by the complete geometry of `EndTemplate`. -/
def endRow_E1 {P : Params S} {l : LeafType P} {slot : EndSlot l}
    (T : EndTemplate slot) : Prop :=
  (∀ a ∈ T.geometry.primitivePorts, ∀ u : LeafType P,
    (a.tile, u) ∈ T.configuration.tiles → ∃ r : FacetRecord P,
      leafRecord u a.facet.val = some r ∧ r.incidence = a.incidence ∧ r.side = a.side ∧
      r.tauAt a.vertex.val = some a.providerVertex.val.val ∧ r.beta = slot.record.beta) ∧
  ∀ a ∈ T.geometry.boundaryPorts, ∀ u : LeafType P,
    (a.tile, u) ∈ T.configuration.tiles →
      match stateRecordAt slot.packet.head a.parentFacet.val with
      | none => leafRecord u a.facet.val = none
      | some r => leafRecord u a.facet.val = some (a.restriction r)

/-- Q13, V4 §2.5 (E2): same first-generation facet, alignment and endpoint counters.
All ports on the same first-generation facet, on both sides, have equal packets.
At a flag endpoint every listed chain in the realized flag planes with tangent
cones inside the realized flag cones is recorded active with its induced orientation
and sides. Every chain-active edge at the event vertex along the realized flag ray
has initial germ 0 at an initial flag endpoint and terminal germ N at a terminal one. -/
def endRow_E2 {P : Params S} {l : LeafType P} {slot : EndSlot l}
    (T : EndTemplate slot) : Prop :=
  (∀ a ∈ T.geometry.primitivePorts, ∀ b ∈ T.geometry.primitivePorts,
    a.incidence = b.incidence → ∀ u v : LeafType P,
      (a.tile, u) ∈ T.configuration.tiles → (b.tile, v) ∈ T.configuration.tiles →
      leafPacket u a.facet.val = leafPacket v b.facet.val) ∧
  ∀ a ∈ T.geometry.primitivePorts, ∀ u : LeafType P,
    (a.tile, u) ∈ T.configuration.tiles → ∀ r : FacetRecord P,
      leafRecord u a.facet.val = some r → ∀ G : State.FlagTangent (d := d),
      T.geometry.header.flagTangent a.incidence = some G →
      (∀ F : FlagChain r.facet,
        ChainFitsTangent r a.tile.frame (vertexPoint T.geometry.vertex) F G →
        ∃ c ∈ r.chains, c.chain = F ∧ OrientationFitsTangent r a.tile.frame c G) ∧
      ∀ e : PrototypeEdge S r.ty, r.ChainActive (edgeCell e) →
        vertexPoint T.geometry.vertex ∈ placedSet a.tile.frame e.val.carrier →
        tangentCone (placedSet a.tile.frame e.val.carrier)
          (vertexPoint T.geometry.vertex) = G.cones edgeIndex →
        if G.initial then r.kappaMinus e = 0 else r.kappaPlus e = P.N

/-- Q13, V4 §2.5 (E3): equality of shifted PRESENT slots, with finite window bounds. -/
def ShiftedAgree {P : Params S} (q q' : Packet P) (δ : ℕ) : Prop :=
  ∀ (i j : Fin P.k) (s s' : State P), j.val = i.val + δ →
    decode q i = some s → decode q' j = some s' → s = s'

/-- Q13, V4 §2.5 (E3): head and GROUP.
The central head is a state of the birth-parent type. For each parent boundary
facet through p, a finite head record gives one common packet of its incidence,
with its own head-determined mask; if the age delta is uncapped, its slot s equals
the central packet's slot s+delta whenever both are PRESENT inside the window.
A NULL head record forces every port on that facet to carry NULL. -/
def endRow_E3 {P : Params S} {l : LeafType P} {slot : EndSlot l}
    (T : EndTemplate slot) : Prop :=
  slot.packet.head.ty = T.geometry.header.birthType ∧
  ∀ F : FacetName S T.geometry.header.birthType,
    (∃ G, T.geometry.header.boundaryCones F = some G) →
    match stateRecordAt slot.packet.head F.val with
    | none => ∀ a ∈ T.geometry.boundaryPorts, a.parentFacet.val = F.val →
        ∀ u : LeafType P, (a.tile, u) ∈ T.configuration.tiles →
          leafPacket u a.facet.val = none
    | some r => ∃ q : Packet P, q ∈ honestPackets S P ∧ q.incidence = r.incidence ∧
        (∀ j, q.mask j ↔ packetMask P r.incidence q.head j) ∧
        (∀ a ∈ T.geometry.boundaryPorts, a.parentFacet.val = F.val →
          ∀ u : LeafType P, (a.tile, u) ∈ T.configuration.tiles →
            leafPacket u a.facet.val = some q) ∧
        (r.age.val < P.C → ShiftedAgree q slot.packet r.age.val)

/-- Q13, V4 §2.5 (E4): equality at every common PRESENT index. -/
def AgreePresent {P : Params S} (q q' : Packet P) : Prop :=
  ∀ (j : Fin P.k) (s s' : State P), decode q j = some s → decode q' j = some s' → s = s'

/-- Q13, V4 §2.5 (E4): same parent.
For any first-generation facets through p, all their packets agree at every slot
PRESENT in both. In particular every first-generation packet head is the central head. -/
def endRow_E4 {P : Params S} {l : LeafType P} {slot : EndSlot l}
    (T : EndTemplate slot) : Prop :=
  ∀ a ∈ T.geometry.primitivePorts, ∀ u : LeafType P,
    (a.tile, u) ∈ T.configuration.tiles → ∃ q : Packet P,
      leafPacket u a.facet.val = some q ∧ q.head = slot.packet.head ∧
      ∀ b ∈ T.geometry.primitivePorts, ∀ v : LeafType P,
        (b.tile, v) ∈ T.configuration.tiles → ∀ q' : Packet P,
          leafPacket v b.facet.val = some q' → AgreePresent q q'

/-- Q13, V4 §2.5 (E5): E-related.
Packets on boundary ports of two parent facets through p are equal whenever the
central head records E(F,F'). NULL participates in equality as the persistent-fault symbol. -/
def endRow_E5 {P : Params S} {l : LeafType P} {slot : EndSlot l}
    (T : EndTemplate slot) : Prop :=
  ∀ a ∈ T.geometry.boundaryPorts, ∀ b ∈ T.geometry.boundaryPorts,
    stateEAt slot.packet.head a.parentFacet.val b.parentFacet.val →
    ∀ u v : LeafType P, (a.tile, u) ∈ T.configuration.tiles →
      (b.tile, v) ∈ T.configuration.tiles →
      leafPacket u a.facet.val = leafPacket v b.facet.val

/-- Q13, V4 §2.5 (E6): same facet.
All ports on the same boundary facet F of the parent carry equal packets,
including multiple ports of one tile on that facet and NULL fault packets. -/
def endRow_E6 {P : Params S} {l : LeafType P} {slot : EndSlot l}
    (T : EndTemplate slot) : Prop :=
  ∀ a ∈ T.geometry.boundaryPorts, ∀ b ∈ T.geometry.boundaryPorts,
    a.parentFacet.val = b.parentFacet.val → ∀ u v : LeafType P,
      (a.tile, u) ∈ T.configuration.tiles → (b.tile, v) ∈ T.configuration.tiles →
      leafPacket u a.facet.val = leafPacket v b.facet.val

/-- Q13, V4 §2.5 (E1)--(E6): the END row is precisely their conjunction. -/
def endRow {P : Params S} {l : LeafType P} {slot : EndSlot l}
    (T : EndTemplate slot) : Prop :=
  endRow_E1 T ∧ endRow_E2 T ∧ endRow_E3 T ∧ endRow_E4 T ∧ endRow_E5 T ∧ endRow_E6 T

/-- Q12/Q13, V4 §2.5: the full catalogue of positioned templates satisfying the row.
Geometry is honest; leaf assignments range freely over matching admissible leaf types.
No condition of joint honesty is added to these assignments. -/
def allowedTemplates {P : Params S} {l : LeafType P} (slot : EventSlot l) :
    Set (Template P) :=
  match slot with
  | .cont s => {θ | ∃ T : ContTemplate s, T.configuration = θ ∧ contRow T}
  | .end_ s => {θ | ∃ T : EndTemplate s, T.configuration = θ ∧ endRow T}

/-- Q13, V4 §2.5: the positioned END catalogue remains finite under all matching
leaf assignments, with the complete geometry and its annotation retained. -/
theorem endPositionedTemplates_finite (P : Params S) (l : LeafType P) (slot : EndSlot l) :
    (Set.range (fun T : EndTemplate slot => T.configuration)).Finite := by
  sorry

/-- Q12/Q13, V4 §2.5: every event slot has a finite allowed template catalogue. -/
theorem allowedTemplates_finite (P : Params S) (l : LeafType P) (slot : EventSlot l) :
    (allowedTemplates slot).Finite := by
  sorry

/-- Q12/Q13, V4 §2.5: a native leaf has only finitely many CONT and END slots.
The header and packet data are readouts fixed by the leaf type, not free choices. -/
theorem eventSlots_finite (P : Params S) (l : LeafType P) : Finite (EventSlot l) := by
  sorry

/-- Q14, V4 2.8: a positioned labelled configuration consists of actual native tiles
with their actual leaf types and exact relative frames. END completeness is retained
separately by `EndGeometryRealizes`, not inferred from this inclusion statement. -/
def IsActualTemplate (U : HonestSource S) (P : Params S) (t : U.Node) (ht : t.1 = 0)
    (θ : Template P) : Prop :=
  θ.central = leafTypeOf U P t ht ∧ ∀ z ∈ θ.tiles,
    ∃ (q : U.Node) (hq : q.1 = 0),
      z.1 = q.2.val.move t.2.val.frame.symm ∧ z.2 = leafTypeOf U P q hq

/-- Q14, V4 2.8 (CONT geometry): the actual next selected owner supplies a physical
continuation template. This existence lemma asserts geometry and actual labels only;
it does not assume or assert the CONT row. -/
theorem actualCont_exists (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : ContSlot (leafTypeOf U P t ht)) :
    ∃ T : ContTemplate slot, IsActualTemplate U P t ht T.configuration := by
  sorry

/-- Q14, V4 2.8 (END geometry): the actual complete P-owned star with its header,
restriction annotations and actual leaf labels. This does not assume the END row.
Nonemptiness is supplied by the given honest native tile and its END slot. -/
theorem actualEnd_exists (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : EndSlot (leafTypeOf U P t ht)) :
    ∃ T : EndTemplate slot, IsActualTemplate U P t ht T.configuration ∧
      ∃ (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
        (v : VertexName S t.2.val.ty),
        f.val = slot.facet.val ∧ v.val = slot.vertex.val ∧
          EndGeometryRealizes U P t f hf v T.geometry := by
  sorry

/-- Q14, V4 2.8: choose the actual positioned continuation, or the actual complete
endpoint star, using the geometry-only existence lemmas. Rows are not used in the choice. -/
def actualTemplate (U : HonestSource S) (P : Params S) (t : U.Node) (ht : t.1 = 0)
    (slot : EventSlot (leafTypeOf U P t ht)) : Template P :=
  match slot with
  | .cont s => (Classical.choose (actualCont_exists U P t ht s)).configuration
  | .end_ s => (Classical.choose (actualEnd_exists U P t ht s)).configuration

/-- Q14, V4 2.8: in every honest source, at every event slot of every native tile,
the actual positioned configuration belongs to the allowed catalogue.
CONT uses the physical-vertex jump rule; END asserts all six clauses simultaneously. -/
theorem honest_rows (U : HonestSource S) (P : Params S) :
    ∀ (t : U.Node) (ht : t.1 = 0) (slot : EventSlot (leafTypeOf U P t ht)),
      actualTemplate U P t ht slot ∈ allowedTemplates slot := by
  sorry

end Enforce
