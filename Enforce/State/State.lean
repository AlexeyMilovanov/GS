import Enforce.State.Parameters

/-!
# Honest finite source states

Q3--Q7, V4 §2.2, Remark 2.1 and Propositions 2.2--2.4.
`State` is an ordinary structure. Only its honest range is asserted finite.
The richer (S6) header is `State.Header`; the earlier `Enforce.Header` remains
the generic cone-tuple header of V4 1.17. The cone convention is documented in
`Parameters`: the inverse full prototype linear frame is used at positive height.

An oriented chain stores its listed cells and the orientation of its edge relative
to the fixed endpoints from `edge_endpoints_exist`. Its successive sides are
`flagSide` of those cells, so there is no global orientation convention.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- Q3, V4 §2.2 (S4): cells on a specified prototype facet. -/
abbrev CellsInFacet (A : S.ι) (f : FacetName S A) :=
  {e : CellName S A // e.val.carrier ⊆ f.val.carrier}

/-- Q3, V4 §2.2 (S6): a named listed vertex. -/
abbrev VertexName (S : SubstSystem d) (A : S.ι) :=
  {v // v ∈ (S.cx A).vertices}

/-- Q3, V4 §2.2 (S4d): a named prototype edge. -/
abbrev PrototypeEdge (S : SubstSystem d) (A : S.ι) :=
  {e // e ∈ (S.cx A).edges}

/-- Q3, V4 §2.2 (S4): a facet is a listed cell. -/
def facetCell {A : S.ι} (f : FacetName S A) : CellName S A :=
  ⟨f.val, (Finset.mem_filter.mp f.property).1⟩

/-- Q3, V4 §2.2 (S4d): an edge is a listed cell. -/
def edgeCell {A : S.ι} (e : PrototypeEdge S A) : CellName S A :=
  ⟨e.val, (Finset.mem_filter.mp e.property).1⟩

/-- Q3, V4 §2.2 (S6): a vertex is a listed cell. -/
def vertexCell {A : S.ι} (v : VertexName S A) : CellName S A :=
  ⟨v.val, (Finset.mem_filter.mp v.property).1⟩

/-- Q3, V4 §2.2 (S6): a listed zero-cell is exactly one point. -/
theorem vertexPoint_exists {A : S.ι} (v : VertexName S A) :
    ∃! p : E d, v.val.carrier = {p} := by
  sorry

/-- Q3, V4 §2.2 (S6): the actual point of a listed vertex. -/
def vertexPoint {A : S.ι} (v : VertexName S A) : E d :=
  Classical.choose (vertexPoint_exists v)

/-- Q3, V4 §2.2 (S6): the selected vertex point has its exact carrier. -/
theorem vertexPoint_spec {A : S.ι} (v : VertexName S A) :
    v.val.carrier = {vertexPoint v} :=
  (Classical.choose_spec (vertexPoint_exists v)).1

/-- Q3, V4 §2.2 (S4c): cells of the common provider complex, named on the
canonical side. Their positioned carriers also name the other side's cells. -/
abbrev ProviderCell (ι : PrimitiveIncidence S) :=
  CellsInFacet (S.child ι.ty ι.left).ty ι.leftFacet

/-- Q3, V4 §2.2 (S4e): a full flag whose top is the recorded facet. -/
abbrev FlagChain {A : S.ι} (f : FacetName S A) :=
  {F : FacetFlag S A // (F.cell facetIndex).val = f.val}

/-- Q3, V4 §2.2 (S4e): an active chain, with its induced edge orientation.
The listed cofaces determine all successive side choices by `flagSide`. -/
structure OrientedChain {A : S.ι} (f : FacetName S A) where
  /-- Q3, V4 §2.2 (S4e): the entire named full chain, not only its edge. -/
  chain : FlagChain f
  /-- Q3, V4 §2.2 (S4e): agreement with the chosen prototype edge orientation. -/
  forward : Bool

/-- Q3, V4 §2.2 (S4e): the chain alphabet is finite before honesty is imposed. -/
theorem orientedChains_finite {A : S.ι} (f : FacetName S A) :
    Finite (OrientedChain f) := by
  sorry

/-- Q3, V4 §2.2 (S4e): all oriented chains as a finite catalogue. -/
def allOrientedChains {A : S.ι} (f : FacetName S A) : Finset (OrientedChain f) := by
  classical
  letI := orientedChains_finite f
  letI := Fintype.ofFinite (OrientedChain f)
  exact Finset.univ

/-- Q3, V4 §2.2 (S4d): the mature branch of a counter profile.
Absent entries mean non-active edges or vertices that are not active endpoints. -/
structure ConstantProfile (P : Params S) (A : S.ι) where
  /-- Q3, V4 §2.2 (S4d): constants only on chain-active edges. -/
  value : CellName S A → Option (Fin (P.N + 1))
  /-- Q3, V4 §2.2 (S4d): site flags only at endpoints of chain-active edges. -/
  endpointSite : VertexName S A → Option Bool

/-- Q3, V4 §2.2 (S4d): the shallow branch retains the downward role word.
The bound is uniform; actual depth and type consistency hold in honest records. -/
structure ShortProfile (P : Params S) where
  /-- Q3, V4 §2.2 (S4d): roles from the serving child down to the recorded node. -/
  word : List S.Role
  /-- Q3, V4 §2.2 (S4d): a bounded finite word, including the empty word. -/
  length_lt : word.length < P.H_site

/-- Q3, V4 §2.2 (S4a)--(S4e): a finite-provider facet record.
NULL is represented by `Option` in `State`. Raw records are not assumed honest. -/
structure FacetRecord (P : Params S) where
  /-- Q3, V4 §2.2 (S4): prototype in whose frame the record is written. -/
  ty : S.ι
  /-- Q3, V4 §2.2 (S4): the facet receiving the record. -/
  facet : FacetName S ty
  /-- Q3, V4 §2.2 (S4a): side-independent incidence. -/
  incidence : P.Incidence
  /-- Q3, V4 §2.2 (S4a): index of one of the two canonical sides. -/
  sideIndex : Bool
  /-- Q3, V4 §2.2 (S4a): the serving side as an actual globally distinct role. -/
  side : S.Role
  /-- Q3, V4 §2.2 (S4a): the role is exactly the indexed side of this incidence. -/
  side_eq : side = incidence.val.sideRole sideIndex
  /-- Q3, V4 §2.2 (S4b): capped age. -/
  age : Fin (P.C + 1)
  /-- Q3, V4 §2.2 (S4b′): serving-child height modulo `L`. -/
  beta : Fin P.L
  /-- Q3, V4 §2.2 (S4c): stratum map on every listed cell contained in the facet. -/
  tau : CellsInFacet ty facet → ProviderCell incidence.val
  /-- Q3, V4 §2.2 (S4e): all active full chains, with induced orientations and sides. -/
  chains : Finset (OrientedChain facet)
  /-- Q3, V4 §2.2 (S4d): constants at mature depth, a bounded role word otherwise. -/
  counter : ConstantProfile P ty ⊕ ShortProfile P

namespace FacetRecord

variable {P : Params S} (r : FacetRecord P)

/-- Q3, V4 §2.2 (S4a): serving side as a globally distinct role. -/
def servingRole : S.Role := r.side

/-- Q3, V4 §2.2 (S4d): activity tests the full-chain table, not just `tau(e)=h`. -/
def ChainActive (e : CellName S r.ty) : Prop :=
  ∃ c ∈ r.chains, (c.chain.val.cell edgeIndex).val = e.val

/-- Q3, V4 §2.2 (S4d): the induced orientation read from the finite chain table. -/
def edgeForward (e : PrototypeEdge S r.ty) : Bool := by
  classical
  exact r.chains.toList.any (fun c =>
    decide ((c.chain.val.cell edgeIndex).val = e.val) && c.forward)

/-- Q3, V4 §2.2 (S4d): oriented endpoints in the recorded prototype. -/
def endpoints (e : PrototypeEdge S r.ty) : E d × E d :=
  let ab := Classical.choose (edge_endpoints_exist (⟨r.ty, e⟩ : EdgeName S))
  if r.edgeForward e then ab else (ab.2, ab.1)

end FacetRecord

/-- Q3/Q13, V4 2.3 (inherited case): one role's full prototype placement,
normalized in its unexpanded parent, with no isotropy assumption. -/
def rolePlacement (r : S.Role) : E d ≃ᵃ[ℝ] E d :=
  (S.child r.1 r.2).frame.toAffineEquiv.trans S.σ.symm.toAffineEquiv

/-- Q3/Q13, V4 2.3: full affine placement along a downward role list. -/
def wordPlacement : List S.Role → E d ≃ᵃ[ℝ] E d
  | [] => AffineEquiv.refl ℝ (E d)
  | r :: rs => (wordPlacement rs).trans (rolePlacement r)

namespace FacetRecord

variable {P : Params S} (r : FacetRecord P)

/-- Q3, V4 §2.2 (S4d): the common oriented edge direction in the serving prototype. -/
def servingDirection : E d :=
  (S.child r.incidence.val.ty (r.incidence.val.sideIndex r.sideIndex)).rotation.symm
    ((S.child r.incidence.val.ty r.incidence.val.left).rotation
      (P.flag r.incidence).direction)

/-- Q3, V4 §2.2 (S4d): the germ immediately after the initial endpoint.
For shallow words sites at that endpoint are counted; for mature profiles this
is the recorded constant. The return value is a natural number in `[0,N]`. -/
def kappaMinus (e : PrototypeEdge S r.ty) : ℕ := by
  classical
  exact match r.counter with
  | .inl c => ((c.value (edgeCell e)).getD 0).val
  | .inr w => (Finset.univ.filter (fun a : Fin P.N =>
      inner ℝ r.servingDirection
        (P.sites r.incidence r.sideIndex a - wordPlacement w.word (r.endpoints e).1) ≤ 0)).card

/-- Q3, V4 §2.2 (S4d): the germ immediately before the terminal endpoint.
For shallow words sites strictly before that endpoint are counted. -/
def kappaPlus (e : PrototypeEdge S r.ty) : ℕ := by
  classical
  exact match r.counter with
  | .inl c => ((c.value (edgeCell e)).getD 0).val
  | .inr w => (Finset.univ.filter (fun a : Fin P.N =>
      inner ℝ r.servingDirection
        (P.sites r.incidence r.sideIndex a - wordPlacement w.word (r.endpoints e).2) < 0)).card

/-- Q3, V4 §2.2 (S4d): site status at a listed active-edge endpoint.
Shallow status is decoded from the same role word and fixed site system. -/
def isSite (v : VertexName S r.ty) : Bool := by
  classical
  exact match r.counter with
  | .inl c => (c.endpointSite v).getD false
  | .inr w => (Finset.univ : Finset (Fin P.N)).toList.any (fun a : Fin P.N =>
      decide (P.sites r.incidence r.sideIndex a = wordPlacement w.word (vertexPoint v)))

end FacetRecord

namespace State

/-- Q3, V4 §2.2 (S6)(iii): flag tangent cones at an endpoint of its oriented edge.
The cones and side cones are all in the recording node's prototype frame. -/
structure FlagTangent where
  /-- Q3, V4 §2.2 (S6)(iii): all positive-dimensional flag-cell cones. -/
  cones : FlagIndex d → Set (E d)
  /-- Q3, V4 §2.2 (S6)(iii): true at the initial, false at the terminal endpoint. -/
  initial : Bool
  /-- Q3, V4 §2.2 (S6)(iii): successive side cones of the positioned flag. -/
  sides : FlagStep d → Set (E d)

/-- Q3, V4 §2.2 (S6): the provider-zero header with all (i)--(iii) data.
This extends the generic cone-tuple concept already called `Enforce.Header`.
Cones are literal sets of directions, not identifiers for cones. -/
structure Header (P : Params S) where
  /-- Q3, V4 §2.2 (S6): birth-parent type. -/
  birthType : S.ι
  /-- Q3, V4 §2.2 (S6)(i): tangent cone of the birth parent. -/
  parentCone : Set (E d)
  /-- Q3, V4 §2.2 (S6)(ii): cones of exactly the children containing the apex. -/
  childCones : S.I birthType → Option (Set (E d))
  /-- Q3, V4 §2.2 (S6)(ii): boundary facets through the apex with their cones. -/
  boundaryCones : FacetName S birthType → Option (Set (E d))
  /-- Q3, V4 §2.2 (S6)(ii): first-generation facets through the apex with their cones. -/
  primitiveCones : P.Incidence → Option (Set (E d))
  /-- Q3, V4 §2.2 (S6)(iii): endpoint flags and oriented tangent data. -/
  flagTangent : P.Incidence → Option (FlagTangent (d := d))

end State

/-- Q3, V4 §2.2 (S1)--(S6): an ordinary source-state data structure.
The ambient type may be infinite. Admissibility is membership in `honestStates`,
whose finiteness is Proposition 2.2, not a `Fintype` instance on `State`. -/
structure State (P : Params S) where
  /-- Q3, V4 §2.2 (S1): prototype type. -/
  ty : S.ι
  /-- Q3, V4 §2.2 (S2): bottom-up roles of the next `k` ancestors. -/
  address : Fin P.k → S.Role
  /-- Q3, V4 §2.2 (S2): first role has the recorded child type. -/
  address_start : (S.child (address ⟨0, P.k_pos⟩).1 (address ⟨0, P.k_pos⟩).2).ty = ty
  /-- Q3, V4 §2.2 (S2): each parent type is the next role's child type. -/
  address_consistent : ∀ j : ℕ, ∀ hj : j + 1 < P.k,
    (address ⟨j, by omega⟩).1 =
      (S.child (address ⟨j + 1, hj⟩).1 (address ⟨j + 1, hj⟩).2).ty
  /-- Q3, V4 §2.2 (S3): height modulo `L`. -/
  residue : Fin P.L
  /-- Q3, V4 §2.2 (S4): NULL precisely on honest persistent faults. -/
  facetRecord : FacetName S ty → Option (FacetRecord P)
  /-- Q3, V4 §2.2 (S4): records belong to their keyed prototype facets. -/
  facetRecord_valid : ∀ f r, facetRecord f = some r → r.ty = ty ∧ r.facet.val = f.val
  /-- Q3, V4 §2.2 (S5): equality of eventually coalescing boundary tracks. -/
  E : FacetName S ty → FacetName S ty → Prop
  /-- Q3, V4 §2.2 (S5): a decidable finite table. -/
  E_decidable : DecidableRel E
  /-- Q3, V4 §2.2 (S5): every track is related to itself. -/
  E_refl : ∀ f, E f f
  /-- Q3, V4 §2.2 (S6): provider-zero headers, keyed by vertex and facet. -/
  header : VertexName S ty → FacetName S ty → Option (State.Header P)

attribute [instance] State.E_decidable

namespace HonestSource

variable (U : HonestSource S)

/-- Q3, V4 §2.2: all actual hierarchy nodes, with their height and membership. -/
abbrev Node := U.hierarchy.Node

/-- Q3, V4 §2.2 (S2): the actual downward role list from the a-th ancestor. -/
def downRoles (q : U.Node) (a : ℕ) : List S.Role :=
  (List.ofFn (fun j : Fin a => U.hierarchy.nodeRole (U.hierarchy.ancestor q j.val))).reverse

/-- Q3, V4 §2.2 (S2): the actual address is type-consistent. -/
theorem address_data (P : Params S) (q : U.Node) :
    (S.child (U.hierarchy.nodeRole q).1 (U.hierarchy.nodeRole q).2).ty = q.2.val.ty ∧
      ∀ j : ℕ, j + 1 < P.k →
        (U.hierarchy.nodeRole (U.hierarchy.ancestor q j)).1 =
          (S.child (U.hierarchy.nodeRole (U.hierarchy.ancestor q (j + 1))).1
            (U.hierarchy.nodeRole (U.hierarchy.ancestor q (j + 1))).2).ty := by
  sorry

/-- Q3, V4 §2.2 (S4a): canonical side-independent provider incidence. -/
def recordIncidence (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) : P.Incidence :=
  P.canonical (U.hierarchy.providerIncidence q f hf)

/-- Q3, V4 §2.2 (S4a): the actual serving role selects exactly one canonical side. -/
theorem recordSide_exists (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) :
    ∃! b : Bool, (U.recordIncidence P q f hf).val.sideRole b =
      U.hierarchy.nodeRole (U.hierarchy.servingChild q f hf) := by
  sorry

/-- Q3, V4 §2.2 (S4a): the separate serving-side datum. -/
def recordSide (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) : Bool :=
  Classical.choose (U.recordSide_exists P q f hf)

/-- Q3, V4 §2.2 (S4): placement of the selected canonical flag in the actual source. -/
def providerPlacement (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) : E d ≃ᵃ[ℝ] E d :=
  P.incidencePlacement (U.hierarchy.birthParent q f hf).2.val
    (U.hierarchy.birthHeight q f hf) (U.recordIncidence P q f hf)

/-- Q3, V4 §2.2 (S4c): prototype containment transports to the placed facet. -/
theorem cellInFacet_placed (q : U.Node) (f : FacetName S q.2.val.ty)
    (e : CellsInFacet q.2.val.ty f) :
    q.2.val.cell q.1 e.val.val ⊆ q.2.val.cell q.1 f.val := by
  exact Set.image_mono e.property

/-- Q3, V4 §2.2 (S4c): unique canonical name of the actual provider stratum.
Existence is the stage-2 stratum map, transported between the paired side names. -/
theorem recordTau_exists (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (e : CellsInFacet q.2.val.ty f) :
    ∃! t : ProviderCell (U.recordIncidence P q f hf).val,
      U.providerPlacement P q f hf '' t.val.val.carrier =
        (U.hierarchy.servingChild q f hf).2.val.cell
          (U.hierarchy.servingChild q f hf).1
          (U.hierarchy.stratumMap q f hf e.val (U.cellInFacet_placed q f e)).val := by
  sorry

/-- Q3, V4 §2.2 (S4c): actual canonical stratum map. -/
def recordTau (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (e : CellsInFacet q.2.val.ty f) :
    ProviderCell (U.recordIncidence P q f hf).val :=
  Classical.choose (U.recordTau_exists P q f hf e)

/-- Q3, V4 §2.2 (S4e): full geometric chain activity with the induced orientation.
The stratum equality and affine-span equality are both explicit. -/
def ActiveChain (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (c : OrientedChain f) : Prop :=
  (∀ j, ∃ hs : q.2.val.cell q.1 (c.chain.val.cell j).val ⊆ q.2.val.cell q.1 f.val,
    (U.hierarchy.servingChild q f hf).2.val.cell
        (U.hierarchy.servingChild q f hf).1
        (U.hierarchy.stratumMap q f hf (c.chain.val.cell j) hs).val =
      U.providerPlacement P q f hf ''
        ((P.flag (U.recordIncidence P q f hf)).flag.cell j).val.carrier ∧
    affineSpan ℝ (q.2.val.cell q.1 (c.chain.val.cell j).val) =
      affineSpan ℝ (U.providerPlacement P q f hf ''
        ((P.flag (U.recordIncidence P q f hf)).flag.cell j).val.carrier)) ∧
  (c.forward = true ↔ inner ℝ
    ((U.providerPlacement P q f hf).linear (P.flag (U.recordIncidence P q f hf)).direction)
    ((q.2.val.prototypeFrame q.1).linear
      ((Classical.choose (edge_endpoints_exist
        ⟨q.2.val.ty, ⟨(c.chain.val.cell edgeIndex).val, by
          classical
          simp only [CellComplex.edges, Finset.mem_filter]
          exact ⟨(c.chain.val.cell edgeIndex).property,
            c.chain.val.dimension edgeIndex⟩⟩⟩)).2 -
       (Classical.choose (edge_endpoints_exist
        ⟨q.2.val.ty, ⟨(c.chain.val.cell edgeIndex).val, by
          classical
          simp only [CellComplex.edges, Finset.mem_filter]
          exact ⟨(c.chain.val.cell edgeIndex).property,
            c.chain.val.dimension edgeIndex⟩⟩⟩)).1)) > 0)

/-- Q3, V4 §2.2 (S4e): the exact finite table of active oriented chains. -/
def recordChains (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) : Finset (OrientedChain f) := by
  classical
  exact (allOrientedChains f).filter (U.ActiveChain P q f hf)

/-- Q3, V4 §2.2 (S4d): selected sites transported to the serving child in this source. -/
def sitePoint (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (a : Fin P.N) : E d :=
  U.providerPlacement P q f hf
    (P.canonicalSite (U.recordIncidence P q f hf) (U.recordSide P q f hf) a)

/-- Q3, V4 §2.2 (S4d): common direction of increasing counter in ambient coordinates. -/
def counterDirection (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) : E d :=
  (U.providerPlacement P q f hf).linear (P.flag (U.recordIncidence P q f hf)).direction

/-- Q3, V4 §2.2 (S4d): the number of sites strictly before an ambient point. -/
def sitesBefore (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (x : E d) : Fin (P.N + 1) := by
  classical
  let B := Finset.univ.filter (fun a : Fin P.N =>
    inner ℝ (U.counterDirection P q f hf) (U.sitePoint P q f hf a - x) < 0)
  have hB : B.card ≤ P.N := by
    exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
  exact ⟨B.card, by omega⟩

/-- Q3, V4 §2.2 (S4d): mature constants and endpoint flags, computed geometrically.
The finite-chain test ensures that non-active edges carry no counter data. -/
def constantProfile (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) : ConstantProfile P q.2.val.ty := by
  classical
  let chains := U.recordChains P q f hf
  exact {
    value := fun e => if ∃ c ∈ chains, (c.chain.val.cell edgeIndex).val = e.val then
      some (U.sitesBefore P q f hf (q.2.val.prototypeFrame q.1 (cellAnchor e.val)))
      else none
    endpointSite := fun v => if ∃ c ∈ chains,
        vertexPoint v ∈ (c.chain.val.cell edgeIndex).val.carrier then
      some ((Finset.univ : Finset (Fin P.N)).toList.any (fun a : Fin P.N => decide
        (U.sitePoint P q f hf a = q.2.val.prototypeFrame q.1 (vertexPoint v))))
      else none }

/-- Q3, V4 §2.2 (S4d): exact two-branch counter extraction from the source depth. -/
def counterProfile (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) : ConstantProfile P q.2.val.ty ⊕ ShortProfile P := by
  classical
  let a := (U.hierarchy.firstProvider q f hf).1
  let r := P.siteDepth (U.recordIncidence P q f hf) (U.recordSide P q f hf)
  exact if h : a < r then .inr {
    word := U.downRoles q a
    length_lt := by
      simp only [downRoles, List.length_reverse, List.length_ofFn]
      exact lt_trans h (P.siteDepth_lt _ _) }
    else .inl (U.constantProfile P q f hf)

/-- Q3, V4 §2.2 (S4): the actual finite-provider record, with every field computed
from the hierarchy, its unique provider, its canonical strata, and the chosen sites. -/
def recordOf (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) : FacetRecord P where
  ty := q.2.val.ty
  facet := f
  incidence := U.recordIncidence P q f hf
  sideIndex := U.recordSide P q f hf
  side := (U.recordIncidence P q f hf).val.sideRole (U.recordSide P q f hf)
  side_eq := rfl
  age := ⟨min (U.hierarchy.age q f hf) P.C, by omega⟩
  beta := ⟨(U.hierarchy.servingChild q f hf).1 % P.L, Nat.mod_lt _ P.L_pos⟩
  tau := U.recordTau P q f hf
  chains := U.recordChains P q f hf
  counter := U.counterProfile P q f hf

/-- Q3, V4 §2.2 (S4): the total facet record, NULL exactly on a persistent fault. -/
def facetRecordOf (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty) :
    Option (FacetRecord P) := by
  classical
  exact if hf : U.hierarchy.IsFault q f then none else some (U.recordOf P q f hf)

/-- Q3, V4 §2.2 (S4): extraction preserves the keyed facet and prototype. -/
theorem facetRecordOf_valid (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (r : FacetRecord P) (hr : U.facetRecordOf P q f = some r) :
    r.ty = q.2.val.ty ∧ r.facet.val = f.val := by
  classical
  unfold facetRecordOf at hr
  split at hr
  · contradiction
  · cases Option.some.inj hr
    exact ⟨rfl, rfl⟩

/-- Q3, V4 §2.2 (S5): literal coalescence of the two boundary tracks.
Both tracks must remain on the boundary up to the coalescence height. -/
def TracksCoalesce (q : U.Node) (f g : FacetName S q.2.val.ty) : Prop :=
  ∃ a : ℕ, (∀ j ≤ a, j ∈ U.hierarchy.boundaryOffsets q f ∧
    j ∈ U.hierarchy.boundaryOffsets q g) ∧
    ∃ F : FacetName S (U.hierarchy.ancestor q a).2.val.ty,
      q.2.val.cell q.1 f.val ⊆
        (U.hierarchy.ancestor q a).2.val.cell (U.hierarchy.ancestor q a).1 F.val ∧
      q.2.val.cell q.1 g.val ⊆
        (U.hierarchy.ancestor q a).2.val.cell (U.hierarchy.ancestor q a).1 F.val

/-- Q3, V4 §2.2 (S5): a track coalesces with itself at offset zero. -/
theorem tracksCoalesce_refl (q : U.Node) (f : FacetName S q.2.val.ty) :
    U.TracksCoalesce q f f := by
  sorry

/-- Q3, V4 §2.2 (S5): the finite coalescence table. -/
def coalescenceTable (q : U.Node) :
    Finset (FacetName S q.2.val.ty × FacetName S q.2.val.ty) := by
  classical
  exact Finset.univ.filter (fun z => U.TracksCoalesce q z.1 z.2)

/-- Q3, V4 §2.2 (S5): the finite table contains exactly the coalescing tracks. -/
theorem mem_coalescenceTable (q : U.Node) (f g : FacetName S q.2.val.ty) :
    (f, g) ∈ U.coalescenceTable q ↔ U.TracksCoalesce q f g := by
  classical
  simp only [coalescenceTable, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Q3, V4 §2.2 (S6): normalize a direction cone by the inverse full linear frame. -/
def normalizeCone (q : U.Node) (G : Set (E d)) : Set (E d) :=
  (q.2.val.prototypeFrame q.1).linear.symm '' G

/-- Q3, V4 §2.2 (S6): complete provider-zero header, extracted geometrically.
It is read only at a listed vertex whose provider stratum is zero-dimensional. -/
def headerOf (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (v : VertexName S q.2.val.ty) : State.Header P := by
  classical
  let B := U.hierarchy.birthParent q f hf
  let x := q.2.val.prototypeFrame q.1 (vertexPoint v)
  let pos := fun ι : P.Incidence => P.incidencePlacement B.2.val B.1 ι
  exact {
    birthType := B.2.val.ty
    parentCone := U.normalizeCone q (tangentCone (B.2.val.carrier B.1) x)
    childCones := fun i =>
      let C := B.2.val.child (B.1 - 1) i
      if x ∈ C.carrier (B.1 - 1) then
        some (U.normalizeCone q (tangentCone (C.carrier (B.1 - 1)) x)) else none
    boundaryCones := fun F => if x ∈ B.2.val.cell B.1 F.val then
      some (U.normalizeCone q (tangentCone (B.2.val.cell B.1 F.val) x)) else none
    primitiveCones := fun ι => if ι.val.ty = B.2.val.ty ∧
        x ∈ pos ι '' ι.val.leftFacet.val.carrier then
      some (U.normalizeCone q (tangentCone (pos ι '' ι.val.leftFacet.val.carrier) x))
      else none
    flagTangent := fun ι => if ι.val.ty = B.2.val.ty ∧
        (x = pos ι (P.flag ι).initial ∨ x = pos ι (P.flag ι).terminal) then
      some {
        cones := fun j => U.normalizeCone q
          (tangentCone (pos ι '' ((P.flag ι).flag.cell j).val.carrier) x)
        initial := decide (x = pos ι (P.flag ι).initial)
        sides := fun j => U.normalizeCone q ((pos ι).linear '' (P.flag ι).sides j) }
      else none }

/-- Q3, V4 §2.2 (S6): the header table is present exactly at provider-zero pairs. -/
def headerRecordOf (P : Params S) (q : U.Node) (v : VertexName S q.2.val.ty)
    (f : FacetName S q.2.val.ty) : Option (State.Header P) := by
  classical
  exact if hv : v.val.carrier ⊆ f.val.carrier then
    if hf : U.hierarchy.IsFault q f then none else
      if (U.recordTau P q f hf ⟨vertexCell v, hv⟩).val.val.dim = 0 then
        some (U.headerOf P q f hf v) else none
    else none

/-- Q3/Q6, V4 2.3: an actual child of any positive-height honest node. -/
def childNode (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) : U.Node :=
  ⟨q.1 - 1, ⟨q.2.val.child (q.1 - 1) i,
    U.hierarchy.children_mem (q.1 - 1) q.2.val
      (by simpa only [Nat.sub_add_cancel hq] using q.2.property) i⟩⟩

end HonestSource

/-- Q3, V4 §2.2 (S1)--(S6): the real state extraction from an honest hierarchy.
Only the unique geometric provider, side and stratum choices use existence lemmas.
A whole state is not postulated or chosen as an unspecified witness. -/
def stateOf (U : HonestSource S) (P : Params S) (q : U.Node) : State P := by
  classical
  exact {
    ty := q.2.val.ty
    address := fun j => U.hierarchy.nodeRole (U.hierarchy.ancestor q j.val)
    address_start := by simpa only [CoherentHierarchy.ancestor, Function.iterate_zero,
      id_eq] using (U.address_data P q).1
    address_consistent := (U.address_data P q).2
    residue := ⟨q.1 % P.L, Nat.mod_lt _ P.L_pos⟩
    facetRecord := U.facetRecordOf P q
    facetRecord_valid := U.facetRecordOf_valid P q
    E := fun f g => (f, g) ∈ U.coalescenceTable q
    E_decidable := fun _ _ => inferInstance
    E_refl := fun f => (U.mem_coalescenceTable q f f).mpr (U.tracksCoalesce_refl q f)
    header := U.headerRecordOf P q }

/-- Q5, V4 2.2: the honest range over all honest sources and all of their nodes.
It may be empty when the species is empty; every member has an actual realisation. -/
def honestStates (S : SubstSystem d) (P : Params S) : Set (State P) :=
  {s | ∃ (U : HonestSource S) (q : U.Node), stateOf U P q = s}

/-- Q5, V4 2.2: every honest state has a source witness, by definition. -/
theorem mem_honestStates (P : Params S) (s : State P) :
    s ∈ honestStates S P ↔ ∃ (U : HonestSource S) (q : U.Node), stateOf U P q = s :=
  Iff.rfl

/-- Q5, V4 2.2: extraction always belongs to the honest range. -/
theorem stateOf_mem (U : HonestSource S) (P : Params S) (q : U.Node) :
    stateOf U P q ∈ honestStates S P := ⟨U, q, rfl⟩

/-- Q5, V4 2.2: the full range, including the literal cone sets in headers, is finite.
The finite-header input is V4 1.17 in `CompatiblePatch.header_finiteness`.
This does not assert finiteness of the ambient structure `State`. -/
theorem states_finite (S : SubstSystem d) (P : Params S) :
    (honestStates S P).Finite := by
  sorry

/-- Q4, V4 Remark 2.1: each chain-active edge belongs to a selected owner of the
recursive coface trace, with its entire recorded chain (including the planar case).
The converse in `chain_active_owner_converse` retains all coface information. -/
theorem chain_active_owner (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (c : OrientedChain f) (hc : c ∈ U.recordChains P q f hf) :
    ∃ (F : FacetFlag S (U.hierarchy.servingChild q f hf).2.val.ty)
      (a : TracePiece (U.hierarchy.servingChild q f hf).2.val.ty F
        (U.hierarchy.firstProvider q f hf).1),
      (∀ j, (U.hierarchy.servingChild q f hf).2.val.cell
          (U.hierarchy.servingChild q f hf).1 (F.cell j).val =
        U.providerPlacement P q f hf ''
          ((P.flag (U.recordIncidence P q f hf)).flag.cell j).val.carrier) ∧
      placedTraceOwner (U.hierarchy.servingChild q f hf).2.val
        (U.hierarchy.servingChild q f hf).1 (U.hierarchy.firstProvider q f hf).1 F a =
        q.2.val ∧
      ∀ j : ChainIndex d (traceDimension d),
        (a.chain.cell j).val =
          (c.chain.val.cell ⟨j.val.val, j.property.2, j.val.isLt⟩).val := by
  sorry

/-- Q4, V4 Remark 2.1: top coface of a selected owner's recorded trace chain. -/
def traceTopIndex : ChainIndex d (traceDimension d) :=
  ⟨⟨d - 1, by have := (Fact.out : 2 ≤ d); omega⟩, by
    change traceDimension d ≤ d - 1
    unfold traceDimension
    have := (Fact.out : 2 ≤ d)
    omega, by
    change 1 ≤ d - 1
    have := (Fact.out : 2 ≤ d)
    omega⟩

/-- Q4, V4 Remark 2.1 (converse): the selected owner with its recorded coface
chain ending at f has all of its trace-boundary edges chain-active at that f.
The top-cell equality is needed when one tile has several facets in the provider. -/
theorem chain_active_owner_converse (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (F : FacetFlag S (U.hierarchy.servingChild q f hf).2.val.ty)
    (hF : ∀ j, (U.hierarchy.servingChild q f hf).2.val.cell
        (U.hierarchy.servingChild q f hf).1 (F.cell j).val =
      U.providerPlacement P q f hf ''
        ((P.flag (U.recordIncidence P q f hf)).flag.cell j).val.carrier)
    (a : TracePiece (U.hierarchy.servingChild q f hf).2.val.ty F
      (U.hierarchy.firstProvider q f hf).1)
    (ha : placedTraceOwner (U.hierarchy.servingChild q f hf).2.val
      (U.hierarchy.servingChild q f hf).1 (U.hierarchy.firstProvider q f hf).1 F a =
        q.2.val)
    (ha_top : (a.chain.cell traceTopIndex).val = f.val)
    (e : CellName S q.2.val.ty) (he : e.val.dim = 1)
    (heB : q.2.val.cell q.1 e.val ⊆
      placedTraceCarrier (U.hierarchy.servingChild q f hf).2.val
        (U.hierarchy.servingChild q f hf).1 (U.hierarchy.firstProvider q f hf).1 F a)
    (heh : q.2.val.cell q.1 e.val ⊆ U.providerPlacement P q f hf ''
      ((P.flag (U.recordIncidence P q f hf)).flag.cell edgeIndex).val.carrier) :
    (U.recordOf P q f hf).ChainActive e := by
  sorry

/-- Q6, V4 2.3: deterministic descent, totalized on raw states and invalid roles.
Only admissible pairs are constrained. Honest ground states are first raised by
`L` using exact scale transfer, so every admissible pair has an honest child witness. -/
theorem exists_childMap (S : SubstSystem d) (P : Params S) :
    ∃ D : State P → S.Role → State P,
      (∀ s ∈ honestStates S P, ∀ r : S.Role, r.1 = s.ty →
        D s r ∈ honestStates S P ∧ (D s r).ty = (S.child r.1 r.2).ty) ∧
      ∀ (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty),
        stateOf U P (U.childNode q hq i) = D (stateOf U P q) ⟨q.2.val.ty, i⟩ := by
  sorry

/-- Q6, V4 2.3: the deterministic child map, chosen from its complete specification.
Invalid pairs may return arbitrary raw states; they are not used in descent. -/
def childMap (P : Params S) : State P → S.Role → State P :=
  Classical.choose (exists_childMap S P)

/-- Q6, V4 2.3: honest closure and prescribed child type on every admissible pair. -/
theorem childMap_admissible (P : Params S) (s : State P)
    (hs : s ∈ honestStates S P) (r : S.Role) (hr : r.1 = s.ty) :
    childMap P s r ∈ honestStates S P ∧
      (childMap P s r).ty = (S.child r.1 r.2).ty :=
  (Classical.choose_spec (exists_childMap S P)).1 s hs r hr

/-- Q6, V4 2.3: the child map computes every actual honest child state. -/
theorem childMap_spec (U : HonestSource S) (P : Params S) (q : U.Node)
    (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) :
    stateOf U P (U.childNode q hq i) =
      childMap P (stateOf U P q) ⟨q.2.val.ty, i⟩ :=
  (Classical.choose_spec (exists_childMap S P)).2 U q hq i

/-- Q7, V4 2.4(a): internalness computed in the parent specified by the first address. -/
def State.InternalFacet {P : Params S} (s : State P) (f : FacetName S s.ty) : Prop :=
  let r := s.address ⟨0, P.k_pos⟩
  relint (placedSet (S.child r.1 r.2).frame f.val.carrier) ⊆
    interior (S.supertile 1 r.1)

/-- Q7, V4 2.4(a): the complete age-one record semantics, in paired-side coordinates.
Identity of `tau` is equality of positioned cells, avoiding a cast between sides. -/
def AgeOneRecord {P : Params S} (s : State P) (r : FacetRecord P) : Prop :=
  r.age.val = 1 ∧ r.servingRole = s.address ⟨0, P.k_pos⟩ ∧
    r.incidence.val.positioned =
      placedSet (S.child r.servingRole.1 r.servingRole.2).frame r.facet.val.carrier ∧
    r.beta = s.residue ∧
    (∀ e, placedSet (S.child r.incidence.val.ty r.incidence.val.left).frame
        (r.tau e).val.val.carrier =
      placedSet (S.child r.servingRole.1 r.servingRole.2).frame e.val.val.carrier) ∧
    ∃ w : ShortProfile P, r.counter = .inr w ∧ w.word = []

/-- Q7, V4 2.4(a): internal child facets have precisely the age-one data;
conversely age one determines the first address role and its unique paired sibling. -/
theorem state_semantics_a (P : Params S) (s : State P) (hs : s ∈ honestStates S P)
    (f : FacetName S s.ty) :
    (s.InternalFacet f ↔ ∃ r, s.facetRecord f = some r ∧ AgeOneRecord s r) ∧
      (∀ r, s.facetRecord f = some r → r.age.val = 1 →
        s.InternalFacet f ∧ AgeOneRecord s r) := by
  sorry

/-- Q7, V4 2.4(b): provider strata never decrease cell dimension. -/
theorem state_semantics_b (P : Params S) (s : State P) (hs : s ∈ honestStates S P)
    (f : FacetName S s.ty) (r : FacetRecord P) (hr : s.facetRecord f = some r)
    (e : CellsInFacet r.ty r.facet) : e.val.val.dim ≤ (r.tau e).val.val.dim := by
  sorry

/-- Q7, V4 2.4(c): an interior jump forces shallow depth and uncapped age.
The depth is the recorded word length, strictly below the chosen side's site depth. -/
theorem state_semantics_c (P : Params S) (s : State P) (hs : s ∈ honestStates S P)
    (f : FacetName S s.ty) (r : FacetRecord P) (hr : s.facetRecord f = some r)
    (e : PrototypeEdge S r.ty) (he : r.ChainActive (edgeCell e))
    (hjump : r.kappaPlus e ≠ r.kappaMinus e) :
    ∃ w : ShortProfile P, r.counter = .inr w ∧
      w.word.length < P.siteDepth r.incidence r.sideIndex ∧
      r.age.val = w.word.length + 1 ∧ r.age.val ≤ P.H_site ∧ r.age.val < P.C := by
  sorry

/-- Q7, V4 2.4(d): every active edge type is reachable from the serving flag edge.
The graph is the existing hereditary edge graph of V4 1.20. -/
theorem state_semantics_d (P : Params S) (s : State P) (hs : s ∈ honestStates S P)
    (f : FacetName S s.ty) (r : FacetRecord P) (hr : s.facetRecord f = some r)
    (e : PrototypeEdge S r.ty) (he : r.ChainActive (edgeCell e)) :
    ∃ h : PrototypeEdge S (r.incidence.val.sideType r.sideIndex),
      h.val = ((P.sideFlag r.incidence r.sideIndex).cell edgeIndex).val ∧
      Relation.ReflTransGen (edgeGraph S)
        ⟨r.incidence.val.sideType r.sideIndex, h⟩ ⟨r.ty, e⟩ := by
  sorry

/-- Q7, V4 2.4(e): uncapped ages give the serving-residue congruence. -/
theorem state_semantics_e (P : Params S) (s : State P) (hs : s ∈ honestStates S P)
    (f : FacetName S s.ty) (r : FacetRecord P) (hr : s.facetRecord f = some r)
    (huncapped : r.age.val < P.C) :
    r.beta.val = (s.residue.val + r.age.val - 1) % P.L := by
  sorry

/-- Q7, V4 2.4(e), all ages: serving residue is the honest serving-child height. -/
theorem state_semantics_e_realisation (U : HonestSource S) (P : Params S)
    (q : U.Node) (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f) :
    (U.recordOf P q f hf).beta.val =
      (U.hierarchy.servingChild q f hf).1 % P.L := rfl

/-- Q7, V4 2.4(f): residue is actual height modulo `L` in every realisation. -/
theorem state_semantics_f (U : HonestSource S) (P : Params S) (q : U.Node) :
    (stateOf U P q).residue.val = q.1 % P.L := rfl

/-- Q7, V4 2.4(f): every honest state has a height/residue realisation. -/
theorem state_semantics_f_exists (P : Params S) (s : State P)
    (hs : s ∈ honestStates S P) :
    ∃ (U : HonestSource S) (q : U.Node), stateOf U P q = s ∧
      s.residue.val = q.1 % P.L := by
  obtain ⟨U, q, rfl⟩ := hs
  exact ⟨U, q, rfl, rfl⟩

/-- Q3/Q7, V4 §2.2 (S4), 2.4: NULL has exactly the persistent-fault semantics. -/
theorem stateOf_null_iff (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) :
    (stateOf U P q).facetRecord f = none ↔ U.hierarchy.IsFault q f := by
  classical
  change U.facetRecordOf P q f = none ↔ _
  simp only [HonestSource.facetRecordOf]
  split <;> simp_all

/-- Q3, V4 §2.2 (S4d): honest germs are ordered and bounded by the site count. -/
theorem honest_counter_germs (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (e : PrototypeEdge S q.2.val.ty) (he : (U.recordOf P q f hf).ChainActive (edgeCell e)) :
    (U.recordOf P q f hf).kappaMinus e ≤ (U.recordOf P q f hf).kappaPlus e ∧
      (U.recordOf P q f hf).kappaPlus e ≤ P.N := by
  sorry

/-- Q3, V4 §2.2 (S4a): the side readout is the exact serving role. -/
theorem record_side_spec (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f) :
    (U.recordOf P q f hf).servingRole =
      U.hierarchy.nodeRole (U.hierarchy.servingChild q f hf) :=
  (Classical.choose_spec (U.recordSide_exists P q f hf)).1

/-- Q3, V4 §2.2 (S4c): each recorded canonical stratum is exactly the existing
stage-2 stratum, after placement in the actual provider. -/
theorem record_tau_spec (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (e : CellsInFacet q.2.val.ty f) :
    U.providerPlacement P q f hf '' ((U.recordOf P q f hf).tau e).val.val.carrier =
      (U.hierarchy.servingChild q f hf).2.val.cell
        (U.hierarchy.servingChild q f hf).1
        (U.hierarchy.stratumMap q f hf e.val (U.cellInFacet_placed q f e)).val := by
  exact (Classical.choose_spec (U.recordTau_exists P q f hf e)).1

/-- Q3, V4 §2.2 (S4): the canonical flag's top is the entire actual provider.
This identifies the side-independent state geometry with the ordered source API. -/
theorem record_provider_carrier (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f) :
    U.providerPlacement P q f hf '' (U.recordIncidence P q f hf).val.leftFacet.val.carrier =
      U.hierarchy.providerCarrier q f hf := by
  sorry

/-- Q3, V4 §2.2 (S4e): the finite chain table records exactly geometric activity
with induced orientation; it has no unrecorded active full chains. -/
theorem record_chains_spec (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (c : OrientedChain f) :
    c ∈ (U.recordOf P q f hf).chains ↔ U.ActiveChain P q f hf c := by
  sorry

/-- Q3/Q7, V4 §2.2 (S4d), 2.4(c): the shallow branch occurs precisely before
site maturity, and retains the actual complete serving-child role word. -/
theorem record_shallow_iff (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f) :
    (∃ w : ShortProfile P, (U.recordOf P q f hf).counter = .inr w ∧
      w.word = U.downRoles q (U.hierarchy.firstProvider q f hf).1) ↔
      (U.hierarchy.firstProvider q f hf).1 <
        P.siteDepth (U.recordIncidence P q f hf) (U.recordSide P q f hf) := by
  sorry

/-- Q3, V4 §2.2 (S4d): the mature branch is exactly the geometric constant table. -/
theorem record_mature_iff (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f) :
    (U.recordOf P q f hf).counter = .inl (U.constantProfile P q f hf) ↔
      P.siteDepth (U.recordIncidence P q f hf) (U.recordSide P q f hf) ≤
        (U.hierarchy.firstProvider q f hf).1 := by
  sorry

/-- Q3, V4 §2.2 (S4d): a mature counter exists at exactly the chain-active edges.
Its recorded value is the common value on the relative interior of that edge. -/
theorem mature_counter_spec (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (hmature : P.siteDepth (U.recordIncidence P q f hf) (U.recordSide P q f hf) ≤
      (U.hierarchy.firstProvider q f hf).1) (e : CellName S q.2.val.ty) :
    ((U.constantProfile P q f hf).value e).isSome = true ↔
      (U.recordOf P q f hf).ChainActive e := by
  sorry

/-- Q3, V4 §2.2 (S4d): the two one-sided germs differ by precisely the number
of chosen sites in the relative interior of the active edge, even before maturity. -/
theorem honest_counter_jump_count (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (e : PrototypeEdge S q.2.val.ty) (he : (U.recordOf P q f hf).ChainActive (edgeCell e)) :
    (U.recordOf P q f hf).kappaPlus e - (U.recordOf P q f hf).kappaMinus e =
      (by
        classical
        exact (Finset.univ.filter (fun a : Fin P.N =>
          U.sitePoint P q f hf a ∈ relint (q.2.val.cell q.1 e.val))).card) := by
  sorry

/-- Q3, V4 §2.2 (S4d): endpoint site flags refer to equality of physical points,
not to separate vertex names in different tiles. -/
theorem honest_counter_endpoint_site (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (e : PrototypeEdge S q.2.val.ty) (he : (U.recordOf P q f hf).ChainActive (edgeCell e))
    (v : VertexName S q.2.val.ty) (hv : vertexPoint v ∈ e.val.carrier) :
    (U.recordOf P q f hf).isSite v = true ↔
      ∃ a : Fin P.N, U.sitePoint P q f hf a = q.2.val.prototypeFrame q.1 (vertexPoint v) :=
  by sorry

/-- Q3, V4 §2.2 (S5): on finite tracks coalescence is equality of the exact
provider occurrence, retaining both the birth node and its positioned facet. -/
theorem honest_E_finite_providers (U : HonestSource S) (P : Params S) (q : U.Node)
    (f g : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (hg : ¬ U.hierarchy.IsFault q g) :
    (stateOf U P q).E f g ↔
      U.hierarchy.birthParent q f hf = U.hierarchy.birthParent q g hg ∧
        U.hierarchy.providerCarrier q f hf = U.hierarchy.providerCarrier q g hg := by
  sorry

/-- Q3/Q6, V4 1.13(c), 2.2--2.3: exact scale transfer with congruent height
shift preserves the entire state literally, including active orientations, counters,
coalescence and the full normalized header cones. This permits raising ground
realisations before using the child map. -/
theorem state_scaleTransfer {U V : HonestSource S} (P : Params S)
    {a b : ℕ} {J : Iso d} (e : ScaleTailEquiv U V a b J)
    (hab : a % P.L = b % P.L) (q : U.hierarchy.Tail a) :
    stateOf U P q.val = stateOf V P (e.toEquiv q).val := by
  sorry

/-- Q5, V4 2.2: an actual honest source contributes a state at every height.
This is the nonvacuity implication; existence of a source is not assumed globally. -/
theorem honestStates_nonempty (U : HonestSource S) (P : Params S) (n : ℕ) :
    ∃ q : U.Node, q.1 = n ∧ stateOf U P q ∈ honestStates S P := by
  obtain ⟨N, hN, _⟩ := U.hierarchy.cover n (0 : E d)
  exact ⟨⟨n, ⟨N, hN⟩⟩, rfl, stateOf_mem U P _⟩

end Enforce
