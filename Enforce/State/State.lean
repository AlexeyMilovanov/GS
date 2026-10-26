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

/-- Step 7 of the V4 proof of `exists_childMap` (V4 2.3): (S1)--(S6): "We describe S(C) from S(B) and i." Equality of all data fields gives equality of states; decidability witnesses are subsingletons. -/
private theorem exists_childMap_step7_state_ext {P : Params S} {s t : State P}
    (ht : s.ty = t.ty) (ha : s.address = t.address) (hr : s.residue = t.residue)
    (hf : HEq s.facetRecord t.facetRecord) (he : HEq s.E t.E)
    (hh : HEq s.header t.header) : s = t := by
  cases s
  cases t
  cases ht
  cases ha
  cases hr
  cases hf
  cases he
  cases hh
  congr
  exact Subsingleton.elim _ _

/-- Step 1 of the V4 proof of `exists_childMap` (V4 2.3): (S1): "A_i." The prescribed child is a depth-one descendant, with its actual frame. -/
private theorem exists_childMap_step1_descendant (N : FramedNode S) (n : ℕ) (i : S.I N.ty) :
    (N.child n i).IsDescendant n N (n+1) := by
  refine ⟨1, rfl, ⟨i, ()⟩, ?_⟩
  simp only [SubstSystem.descendantNode, FramedNode.move, FramedNode.child]
  rfl

/-- Step 1 of the V4 proof of `exists_childMap` (V4 2.3): (S6): "re-expressed in C's frame". The full child frame is the parent frame composed with the normalized role placement. -/
private theorem exists_childMap_step1_frame (N : FramedNode S) (n : ℕ) (i : S.I N.ty) :
    (N.child n i).prototypeFrame n =
      (rolePlacement ⟨N.ty, i⟩).trans (N.prototypeFrame (n+1)) := by
  apply AffineEquiv.ext
  intro x
  change N.frame (S.placeChild n i ((S.σ ^ n) x)) =
    N.frame ((S.σ ^ (n+1)) (S.σ.symm ((S.child N.ty i).frame x)))
  congr 1
  rw [S.placeChild_apply]
  simp [linearConj, Child.frame, rigidMotion, pow_succ, zpow_neg,
    LinearEquiv.mul_apply, ← map_add]

/-- Step 2 of the V4 proof of `exists_childMap` (V4 2.3): (S2): "i' = (A,i)". Disjoint nonempty child interiors make the child index unique. -/
private theorem exists_childMap_step2_role_injective (N : FramedNode S) (n : ℕ) :
    Function.Injective (N.child n) := by
  intro i j h
  have hty : (S.child N.ty i).ty = (S.child N.ty j).ty := congrArg FramedNode.ty h
  have he := congrArg (fun M : FramedNode S => M.prototypeFrame n) h
  dsimp only at he
  rw [exists_childMap_step1_frame, exists_childMap_step1_frame] at he
  have hframe : (S.child N.ty i).frame = (S.child N.ty j).frame := by
    apply AffineIsometryEquiv.ext
    intro x
    have hx := congrArg (fun e : E d ≃ᵃ[ℝ] E d => e x) he
    exact S.σ.symm.injective ((N.prototypeFrame (n+1)).injective hx)
  by_contra hij
  have hd := S.children_disjoint N.ty hij
  dsimp only at hd
  rw [hty, hframe] at hd
  have hn : (interior (placedSet (S.child N.ty j).frame
      (S.proto (S.child N.ty j).ty).carrier)).Nonempty := by
    change (interior ((S.child N.ty j).frame.toHomeomorph ''
      (S.proto (S.child N.ty j).ty).carrier)).Nonempty
    rw [← Homeomorph.image_interior]
    exact (S.proto (S.child N.ty j).ty).interior_nonempty.image _
  obtain ⟨x, hx⟩ := hn
  exact Set.disjoint_left.mp hd hx hx

/-- Step 2 of the V4 proof of `exists_childMap` (V4 2.3): (S2): "(i',r_1,...,r_{k-1})". The parent of a prescribed honest child is the original node. -/
private theorem exists_childMap_step2_parent (U : HonestSource S) (q : U.Node)
    (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) :
    U.hierarchy.parentNode (U.childNode q hq i) = q := by
  rcases q with ⟨n, N, hN⟩
  cases n with
  | zero =>
    change 1 ≤ 0 at hq
    omega
  | succ n =>
    apply Sigma.ext
    · simp [HonestSource.childNode, CoherentHierarchy.parentNode]
    · apply heq_of_eq
      apply Subtype.ext
      exact (U.hierarchy.parent_unique n _ N hN ⟨i, rfl⟩).symm

/-- Step 2 of the V4 proof of `exists_childMap` (V4 2.3): (S2): "i' = (A,i)". The hierarchy role of a prescribed child is its prescribed index. -/
private theorem exists_childMap_step2_role (U : HonestSource S) (q : U.Node)
    (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) :
    U.hierarchy.nodeRole (U.childNode q hq i) = ⟨q.2.val.ty, i⟩ := by
  rcases q with ⟨n, N, hN⟩
  cases n with
  | zero =>
    change 1 ≤ 0 at hq
    omega
  | succ n =>
    let c := U.childNode ⟨n+1, ⟨N, hN⟩⟩ hq i
    have hp : (U.hierarchy.parent n c.2).val = N :=
      (U.hierarchy.parent_unique n c.2 N hN ⟨i, rfl⟩).symm
    have hc := U.hierarchy.child_eq n c.2
    change c.2.val = _ at hc
    change (⟨(U.hierarchy.parent n c.2).val.ty, U.hierarchy.role n c.2⟩ : S.Role) = _
    have aux (M : FramedNode S) (j : S.I M.ty) (hM : M = N)
        (h : N.child n i = M.child n j) : (⟨M.ty, j⟩ : S.Role) = ⟨N.ty, i⟩ := by
      subst M
      exact congrArg (Sigma.mk N.ty) ((exists_childMap_step2_role_injective N n h).symm)
    exact aux _ _ hp hc

/-- Step 2 of the V4 proof of `exists_childMap` (V4 2.3): (S2): "(i',r_1,...,r_{k-1})". The first address role is prepended and the last parent role is discarded. -/
private theorem exists_childMap_step2_address (U : HonestSource S) (P : Params S) (q : U.Node)
    (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) (j : Fin P.k) :
    (stateOf U P (U.childNode q hq i)).address j =
      if hj : j.val = 0 then ⟨q.2.val.ty, i⟩ else
        (stateOf U P q).address ⟨j.val - 1, by omega⟩ := by
  change U.hierarchy.nodeRole (U.hierarchy.ancestor (U.childNode q hq i) j.val) = _
  by_cases hj : j.val = 0
  · simp only [hj, dif_pos, CoherentHierarchy.ancestor, Function.iterate_zero, id_eq]
    exact exists_childMap_step2_role U q hq i
  · rw [dif_neg hj]
    have hj' : j.val = (j.val - 1) + 1 := by omega
    conv_lhs => rw [hj']
    simp only [CoherentHierarchy.ancestor, Function.iterate_succ_apply,
      exists_childMap_step2_parent]
    rfl

/-- Step 3 of the V4 proof of `exists_childMap` (V4 2.3): (S3): "residue of B minus one". Positive heights with equal residues have predecessors with equal residues. -/
private theorem exists_childMap_step3_residue (P : Params S) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (h : n % P.L = m % P.L) :
    (n-1) % P.L = (m-1) % P.L := by
  exact Nat.ModEq.sub_right hn hm h

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3): (S4): "which case occurs, and f, depend only on (A,i,f')". Containment of placed cells is tested in the normalized one-step geometry. -/
private theorem exists_childMap_step4_containment (U : HonestSource S) (q : U.Node)
    (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) (f F : Cell d) :
    (U.childNode q hq i).2.val.cell (U.childNode q hq i).1 f ⊆ q.2.val.cell q.1 F ↔
      rolePlacement ⟨q.2.val.ty, i⟩ '' f.carrier ⊆ F.carrier := by
  change (q.2.val.child (q.1-1) i).prototypeFrame (q.1-1) '' f.carrier ⊆
    q.2.val.prototypeFrame q.1 '' F.carrier ↔ _
  rw [exists_childMap_step1_frame, Nat.sub_add_cancel hq]
  change (fun x => q.2.val.prototypeFrame q.1 (rolePlacement ⟨q.2.val.ty, i⟩ x)) ''
    f.carrier ⊆ _ ↔ _
  rw [← Set.image_image]
  exact Set.image_subset_image_iff (q.2.val.prototypeFrame q.1).injective

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3): (S4), inherited case: "If S(B) has NULL at f then NULL." A child facet is a fault precisely when it lies in a fault facet of the parent. -/
private theorem exists_childMap_step4_fault (U : HonestSource S) (q : U.Node)
    (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) :
    U.hierarchy.IsFault (U.childNode q hq i) f ↔
      ∃ F : FacetName S q.2.val.ty,
        rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier ∧
          U.hierarchy.IsFault q F := by
  have hinternal (c p : U.Node) (he : U.hierarchy.parentNode c = p)
      (f : FacetName S c.2.val.ty)
      (hint : relint (c.2.val.cell c.1 f.val) ⊆ interior (p.2.val.carrier p.1)) :
      ¬ U.hierarchy.IsFault c f := by
    subst p
    exact (U.hierarchy.restriction_det_internal c f hint).choose
  have hinherited (c p : U.Node) (he : U.hierarchy.parentNode c = p)
      (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
      (hF : c.2.val.cell c.1 f.val ⊆ p.2.val.cell p.1 F.val)
      (hf : U.hierarchy.IsFault p F) : U.hierarchy.IsFault c f := by
    subst p
    exact U.hierarchy.restriction_det_fault c F f hf hF
  have hp := exists_childMap_step2_parent U q hq i
  have hd : (U.childNode q hq i).2.val.IsDescendant (q.1-1) q.2.val q.1 := by
    convert exists_childMap_step1_descendant q.2.val (q.1-1) i using 1
    exact (Nat.sub_add_cancel hq).symm
  constructor
  · intro hf
    rcases facet_dichotomy q.2.val (U.childNode q hq i).2.val q.1 (q.1-1) hd f with
      ⟨F, hF, _⟩ | hint
    · refine ⟨F, (exists_childMap_step4_containment U q hq i f.val F.val).mp hF, ?_⟩
      by_contra hFfault
      obtain ⟨hcf, _⟩ := U.hierarchy.provider_inherited q (U.childNode q hq i) 1
        (by simpa only [CoherentHierarchy.ancestor, Function.iterate_one] using hp)
        F f hFfault hF
      exact hcf hf
    · exact False.elim (hinternal _ _ hp f hint hf)
  · rintro ⟨F, hF, hf⟩
    exact hinherited _ _ hp f F (exists_childMap_step4_containment U q hq i f.val F.val |>.mpr hF) hf

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"If S(B) has NULL at f then NULL." Extraction uses NULL exactly on faults. -/
private theorem exists_childMap_step4_null (U : HonestSource S) (P : Params S)
    (q : U.Node) (f : FacetName S q.2.val.ty) :
    U.facetRecordOf P q f = none ↔ U.hierarchy.IsFault q f := by
  classical
  unfold HonestSource.facetRecordOf
  split <;> simp_all

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"the provider of f' is f' itself with birth parent B, age 1". In particular,
the serving child of an internal facet is the child itself. -/
private theorem exists_childMap_step4_internal_provider (U : HonestSource S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hint : ¬ ∃ F : FacetName S q.2.val.ty,
      rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier) :
    U.hierarchy.servingChild (U.childNode q hq i) f hf = U.childNode q hq i ∧
      U.hierarchy.birthParent (U.childNode q hq i) f hf = q ∧
      U.hierarchy.age (U.childNode q hq i) f hf = 1 := by
  have haux (c p : U.Node) (hp : U.hierarchy.parentNode c = p)
      (f : FacetName S c.2.val.ty) (hf : ¬ U.hierarchy.IsFault c f)
      (hi : relint (c.2.val.cell c.1 f.val) ⊆ interior (p.2.val.carrier p.1)) :
      U.hierarchy.birthParent c f hf = p ∧ U.hierarchy.age c f hf = 1 := by
    subst p
    obtain ⟨_, _, hb, ha⟩ := U.hierarchy.restriction_det_internal c f hi
    exact ⟨hb, ha⟩
  have hd : (U.childNode q hq i).2.val.IsDescendant (q.1-1) q.2.val q.1 := by
    convert exists_childMap_step1_descendant q.2.val (q.1-1) i using 1
    exact (Nat.sub_add_cancel hq).symm
  obtain hF | hi := facet_dichotomy q.2.val (U.childNode q hq i).2.val q.1 (q.1-1) hd f
  · obtain ⟨F, hF, _⟩ := hF
    exact False.elim (hint ⟨F, (exists_childMap_step4_containment U q hq i f.val F.val).mp hF⟩)
  · obtain ⟨hb, ha⟩ := haux _ _ (exists_childMap_step2_parent U q hq i) f hf hi
    refine ⟨?_, hb, ha⟩
    have hoff := (U.hierarchy.birthHeight_age_spec (U.childNode q hq i) f hf).2.1
    have hz : (U.hierarchy.firstProvider (U.childNode q hq i) f hf).1 = 0 := by omega
    simp only [CoherentHierarchy.servingChild, hz, CoherentHierarchy.ancestor,
      Function.iterate_zero, id_eq]

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"same ... beta and provider; age min(age+1,C)". Before capping, restriction
adds one to the age and leaves the serving-child height unchanged. -/
private theorem exists_childMap_step4_inherited_numbers (U : HonestSource S)
    (c p : U.Node) (hp : U.hierarchy.parentNode c = p)
    (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f)
    (hsub : c.2.val.cell c.1 f.val ⊆ p.2.val.cell p.1 F.val) :
    ∃ hF : ¬ U.hierarchy.IsFault p F,
      U.hierarchy.age c f hf = U.hierarchy.age p F hF + 1 ∧
      (U.hierarchy.servingChild c f hf).1 = (U.hierarchy.servingChild p F hF).1 := by
  subst p
  have hF : ¬ U.hierarchy.IsFault (U.hierarchy.parentNode c) F := by
    intro hF
    exact hf (U.hierarchy.restriction_det_fault c F f hF hsub)
  obtain ⟨_, _, hb, ha, _⟩ := U.hierarchy.restriction_det_inherited c F f hF hsub
  refine ⟨hF, ha, ?_⟩
  have hh := congrArg (fun q : U.Node => q.1) hb
  change (U.hierarchy.servingChild c f hf).1 + 1 =
    (U.hierarchy.servingChild (U.hierarchy.parentNode c) F hF).1 + 1 at hh
  omega

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"same iota". The transversal gives the same canonical name to equal
parent types and positioned primitive facets. -/
private theorem exists_childMap_step4_canonical (P : Params S)
    (a b : PrimitiveIncidence S) (h : SameIncidence a b) :
    P.canonical a = P.canonical b := by
  apply P.canonical_unique
  exact ⟨h.1.trans (P.canonical_spec b).1, h.2.trans (P.canonical_spec b).2⟩

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"same iota, side ... and provider". Equality of the birth node and provider
carrier identifies the canonical incidence by cancelling the full birth frame. -/
private theorem exists_childMap_step4_provider_name (P : Params S) (U : HonestSource S)
    (c p : U.Node) (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f) (hF : ¬ U.hierarchy.IsFault p F)
    (hb : U.hierarchy.birthParent c f hf = U.hierarchy.birthParent p F hF)
    (hp : U.hierarchy.providerCarrier c f hf = U.hierarchy.providerCarrier p F hF) :
    U.recordIncidence P c f hf = U.recordIncidence P p F hF := by
  have hc := U.hierarchy.providerIncidence_spec c f hf
  have hpar := U.hierarchy.providerIncidence_spec p F hF
  apply exists_childMap_step4_canonical
  constructor
  · exact hc.1.trans ((congrArg (fun q : U.Node => q.2.val.ty) hb).trans hpar.1.symm)
  · have hplace := congrArg (fun B : U.Node => B.2.val.prototypeFrame B.1 ''
        (S.σ.symm '' (U.hierarchy.providerIncidence c f hf).positioned)) hb
    have heq := hplace.symm.trans (hc.2.2.2.symm.trans (hp.trans hpar.2.2.2))
    exact S.σ.symm.injective.image_injective
      (((U.hierarchy.birthParent p F hF).2.val.prototypeFrame
        (U.hierarchy.birthHeight p F hF)).injective.image_injective heq)

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"same ... side". Once the canonical incidence and serving role agree,
the uniquely selected Boolean side agrees too. -/
private theorem exists_childMap_step4_side (P : Params S) (U V : HonestSource S)
    (c : U.Node) (c' : V.Node) (f : FacetName S c.2.val.ty) (g : FacetName S c'.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f) (hg : ¬ V.hierarchy.IsFault c' g)
    (hi : U.recordIncidence P c f hf = V.recordIncidence P c' g hg)
    (hr : U.hierarchy.nodeRole (U.hierarchy.servingChild c f hf) =
      V.hierarchy.nodeRole (V.hierarchy.servingChild c' g hg)) :
    U.recordSide P c f hf = V.recordSide P c' g hg := by
  apply Eq.symm
  apply (Classical.choose_spec (U.recordSide_exists P c f hf)).2
  change (U.recordIncidence P c f hf).val.sideRole (V.recordSide P c' g hg) = _
  calc
    _ = (V.recordIncidence P c' g hg).val.sideRole (V.recordSide P c' g hg) :=
      congrArg (fun a : P.Incidence => a.val.sideRole (V.recordSide P c' g hg)) hi
    _ = V.hierarchy.nodeRole (V.hierarchy.servingChild c' g hg) :=
      (Classical.choose_spec (V.recordSide_exists P c' g hg)).1
    _ = _ := hr.symm

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"same iota, side ... and provider". Along an inherited facet the first
provider offset gains one, so the serving node, incidence and side are unchanged. -/
private theorem exists_childMap_step4_inherited_incidence (P : Params S) (U : HonestSource S)
    (c p : U.Node) (hp : U.hierarchy.parentNode c = p)
    (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f)
    (hsub : c.2.val.cell c.1 f.val ⊆ p.2.val.cell p.1 F.val) :
    ∃ hF : ¬ U.hierarchy.IsFault p F,
      U.recordIncidence P c f hf = U.recordIncidence P p F hF ∧
      U.recordSide P c f hf = U.recordSide P p F hF := by
  subst p
  have hF : ¬ U.hierarchy.IsFault (U.hierarchy.parentNode c) F := by
    intro hF
    exact hf (U.hierarchy.restriction_det_fault c F f hF hsub)
  obtain ⟨_, hprovider, hbirth, hage, _⟩ := U.hierarchy.restriction_det_inherited c F f hF hsub
  have hinc := exists_childMap_step4_provider_name P U c (U.hierarchy.parentNode c) f F hf hF hbirth hprovider
  have hserv : U.hierarchy.servingChild c f hf =
      U.hierarchy.servingChild (U.hierarchy.parentNode c) F hF := by
    have hc := (U.hierarchy.birthHeight_age_spec c f hf).2.1
    have hp := (U.hierarchy.birthHeight_age_spec (U.hierarchy.parentNode c) F hF).2.1
    have hoff : (U.hierarchy.firstProvider c f hf).1 =
        (U.hierarchy.firstProvider (U.hierarchy.parentNode c) F hF).1 + 1 := by omega
    simp only [CoherentHierarchy.servingChild, hoff, CoherentHierarchy.ancestor,
      Function.iterate_succ_apply]
  exact ⟨hF, hinc, exists_childMap_step4_side P U U _ _ f F hf hF hinc
    (congrArg U.hierarchy.nodeRole hserv)⟩

/-- Step 5 of the V4 proof of `exists_childMap` (V4 2.3): "the facets ... containing f',f'' are those containing f,tilde f". Relative interiors commute with every full affine frame, including anisotropic ones. -/
private theorem exists_childMap_step5_relint_image (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
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

/-- Step 5 of the V4 proof of `exists_childMap` (V4 2.3): "coalesce ... only if equal". Every placed listed cell has nonempty relative interior. -/
private theorem exists_childMap_step5_cell_nonempty (N : FramedNode S) (n : ℕ) (f : Cell d) :
    (relint (N.cell n f)).Nonempty := by
  rw [FramedNode.cell, exists_childMap_step5_relint_image]
  exact f.flat.relint_nonempty.image _

/-- Step 5 of the V4 proof of `exists_childMap` (V4 2.3): "the facets ... containing f',f''". A placed cell is the closure of its relative interior. -/
private theorem exists_childMap_step5_cell_closure (N : FramedNode S) (n : ℕ) (f : Cell d) :
    closure (relint (N.cell n f)) = N.cell n f := by
  rw [FramedNode.cell, exists_childMap_step5_relint_image]
  change closure ((N.prototypeFrame n).toHomeomorphOfFiniteDimensional '' relint f.carrier) = _
  rw [← Homeomorph.image_closure, f.flat.regularClosed]
  rfl

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"the unique cell". A cell's carrier determines its dimension and hence its name. -/
private theorem exists_childMap_step4_cell_eq {e f : Cell d}
    (h : e.carrier = f.carrier) : e = f := by
  rcases e with ⟨K, n, hn⟩
  rcases f with ⟨K', n', hn'⟩
  cases h
  have hd : n = n' := hn.dimension.symm.trans hn'.dimension
  cases hd
  rfl

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"t(s') is the unique cell of B with relint s' contained in relint t(s')".
This containment is a test in the fixed one-step substitution geometry. -/
private theorem exists_childMap_step4_relint_containment (U : HonestSource S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) (e t : Cell d) :
    relint ((U.childNode q hq i).2.val.cell (U.childNode q hq i).1 e) ⊆
        relint (q.2.val.cell q.1 t) ↔
      relint (rolePlacement ⟨q.2.val.ty, i⟩ '' e.carrier) ⊆ relint t.carrier := by
  change relint ((q.2.val.child (q.1-1) i).prototypeFrame (q.1-1) '' e.carrier) ⊆
    relint (q.2.val.prototypeFrame q.1 '' t.carrier) ↔ _
  rw [exists_childMap_step1_frame, Nat.sub_add_cancel hq]
  change relint ((fun x => q.2.val.prototypeFrame q.1 (rolePlacement ⟨q.2.val.ty, i⟩ x)) ''
    e.carrier) ⊆ _ ↔ _
  rw [← Set.image_image]
  simp only [exists_childMap_step5_relint_image]
  exact Set.image_subset_image_iff (q.2.val.prototypeFrame q.1).injective

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"tau_f'(s') = tau_f(t(s'))". For an inherited finite facet, the recorded
canonical child stratum equals the recorded stratum of its containing parent cell. -/
private theorem exists_childMap_step4_inherited_tau (P : Params S) (U : HonestSource S)
    (c p : U.Node) (hp : U.hierarchy.parentNode c = p)
    (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f) (hF : ¬ U.hierarchy.IsFault p F)
    (hsub : c.2.val.cell c.1 f.val ⊆ p.2.val.cell p.1 F.val)
    (e : CellsInFacet c.2.val.ty f) :
    ∃ t : CellsInFacet p.2.val.ty F,
      relint (c.2.val.cell c.1 e.val.val) ⊆ relint (p.2.val.cell p.1 t.val.val) ∧
      (U.recordTau P c f hf e).val.val = (U.recordTau P p F hF t).val.val := by
  subst p
  obtain ⟨_, hprov, hbirth, _, hstrata⟩ := U.hierarchy.restriction_det_inherited c F f hF hsub
  obtain ⟨t, ht, hrel, hstrat⟩ := hstrata e.val (U.cellInFacet_placed c f e)
  have htc : t.val.carrier ⊆ F.val.carrier :=
    (Set.image_subset_image_iff ((U.hierarchy.parentNode c).2.val.prototypeFrame
      (U.hierarchy.parentNode c).1).injective).mp ht
  let t' : CellsInFacet (U.hierarchy.parentNode c).2.val.ty F := ⟨t, htc⟩
  refine ⟨t', hrel, ?_⟩
  have hinc := exists_childMap_step4_provider_name P U c (U.hierarchy.parentNode c) f F hf hF hbirth hprov
  have hplace : U.providerPlacement P c f hf = U.providerPlacement P (U.hierarchy.parentNode c) F hF := by
    exact congrArg₂ (fun (B : U.Node) (a : P.Incidence) => P.incidencePlacement B.2.val B.1 a) hbirth hinc
  have hc := (Classical.choose_spec (U.recordTau_exists P c f hf e)).1
  have hp := (Classical.choose_spec (U.recordTau_exists P (U.hierarchy.parentNode c) F hF t')).1
  have heq : U.providerPlacement P c f hf '' (U.recordTau P c f hf e).val.val.carrier =
      U.providerPlacement P (U.hierarchy.parentNode c) F hF ''
        (U.recordTau P (U.hierarchy.parentNode c) F hF t').val.val.carrier :=
    hc.trans (hstrat.trans hp.symm)
  rw [hplace] at heq
  apply exists_childMap_step4_cell_eq
  exact (U.providerPlacement P (U.hierarchy.parentNode c) F hF).injective.image_injective heq

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"tau = id" in the internal case, expressed using the canonical provider-side
name. The two positioned cells agree in the normalized parent prototype. -/
private theorem exists_childMap_step4_internal_tau (P : Params S) (U : HonestSource S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hint : ¬ ∃ F : FacetName S q.2.val.ty,
      rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (e : CellsInFacet (U.childNode q hq i).2.val.ty f) :
    rolePlacement ⟨(U.recordIncidence P (U.childNode q hq i) f hf).val.ty,
        (U.recordIncidence P (U.childNode q hq i) f hf).val.left⟩ ''
        (U.recordTau P (U.childNode q hq i) f hf e).val.val.carrier =
      rolePlacement ⟨q.2.val.ty, i⟩ '' e.val.val.carrier := by
  obtain ⟨hserv, hbirth, hage⟩ := exists_childMap_step4_internal_provider U q hq i f hf hint
  let a := U.recordIncidence P (U.childNode q hq i) f hf
  have hplace : U.providerPlacement P (U.childNode q hq i) f hf =
      (rolePlacement ⟨a.val.ty, a.val.left⟩).trans (q.2.val.prototypeFrame q.1) := by
    calc
      _ = (rolePlacement ⟨a.val.ty, a.val.left⟩).trans
          ((U.hierarchy.birthParent (U.childNode q hq i) f hf).2.val.prototypeFrame
            (U.hierarchy.birthParent (U.childNode q hq i) f hf).1) := by
        apply AffineEquiv.ext
        intro x
        rfl
      _ = _ := congrArg (fun B : U.Node =>
          (rolePlacement ⟨a.val.ty, a.val.left⟩).trans (B.2.val.prototypeFrame B.1)) hbirth
  have hframe : (U.childNode q hq i).2.val.prototypeFrame (U.childNode q hq i).1 =
      (rolePlacement ⟨q.2.val.ty, i⟩).trans (q.2.val.prototypeFrame q.1) := by
    simpa only [Nat.sub_add_cancel hq] using exists_childMap_step1_frame q.2.val (q.1-1) i
  have hs := (Classical.choose_spec (U.recordTau_exists P (U.childNode q hq i) f hf e)).1
  have hstratum := U.hierarchy.stratumMap_age_one (U.childNode q hq i) f hf hage e.val
    (U.cellInFacet_placed (U.childNode q hq i) f e)
  change U.providerPlacement P (U.childNode q hq i) f hf ''
      (U.recordTau P (U.childNode q hq i) f hf e).val.val.carrier =
    (U.hierarchy.servingChild (U.childNode q hq i) f hf).2.val.cell
      (U.hierarchy.servingChild (U.childNode q hq i) f hf).1
      (U.hierarchy.stratumMap (U.childNode q hq i) f hf e.val
        (U.cellInFacet_placed (U.childNode q hq i) f e)).val at hs
  rw [hstratum] at hs
  have hservcell := congrArg (fun c : U.Node => c.2.val.cell c.1 e.val.val) hserv
  have heq := hs.trans hservcell
  apply (q.2.val.prototypeFrame q.1).injective.image_injective
  rw [Set.image_image, Set.image_image]
  change ((rolePlacement ⟨a.val.ty, a.val.left⟩).trans (q.2.val.prototypeFrame q.1)) '' _ =
    ((rolePlacement ⟨q.2.val.ty, i⟩).trans (q.2.val.prototypeFrame q.1)) '' _
  rw [← hplace, ← hframe]
  exact heq

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"tau_f(t(s'))" is read from the parent record at the uniquely named cell.
Equality of records preserves this readout despite their dependent domains. -/
private theorem exists_childMap_step4_read_tau {P : Params S} {r t : FacetRecord P}
    (h : r = t) (e : CellsInFacet r.ty r.facet) (e' : CellsInFacet t.ty t.facet)
    (he : e.val.val = e'.val.val) : (r.tau e).val.val = (t.tau e').val.val := by
  cases h
  have heq : e = e' := Subtype.ext (Subtype.ext he)
  cases heq
  rfl

section ChildComparison
variable (P : Params S) {U V : HonestSource S}
  (q : U.Node) (q' : V.Node) (hq : 1 ≤ q.1) (hq' : 1 ≤ q'.1)
  (i : S.I q.2.val.ty) (i' : S.I q'.2.val.ty)
  (hrole : (⟨q.2.val.ty, i⟩ : S.Role) = ⟨q'.2.val.ty, i'⟩)
  (hrecords : ∀ (F : FacetName S q.2.val.ty) (G : FacetName S q'.2.val.ty),
    F.val = G.val → U.facetRecordOf P q F = V.facetRecordOf P q' G)
  (f : FacetName S (U.childNode q hq i).2.val.ty)
  (g : FacetName S (V.childNode q' hq' i').2.val.ty) (hfg : f.val = g.val)

include hrole hrecords hfg

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"If S(B) has NULL at f then NULL." Matching parent tables give matching NULL
branches at corresponding child facets, including persistent faults. -/
private theorem exists_childMap_step4_fault_eq :
    U.hierarchy.IsFault (U.childNode q hq i) f ↔
      V.hierarchy.IsFault (V.childNode q' hq' i') g := by
  have hty : q.2.val.ty = q'.2.val.ty := congrArg Sigma.fst hrole
  rw [exists_childMap_step4_fault, exists_childMap_step4_fault]
  constructor
  · rintro ⟨F, hF, hf⟩
    let G : FacetName S q'.2.val.ty := ⟨F.val, hty ▸ F.property⟩
    refine ⟨G, ?_, ?_⟩
    · simpa only [← hrole, ← hfg] using hF
    · apply (exists_childMap_step4_null V P q' G).mp
      rw [← hrecords F G rfl]
      exact (exists_childMap_step4_null U P q F).mpr hf
  · rintro ⟨G, hG, hg⟩
    let F : FacetName S q.2.val.ty := ⟨G.val, hty.symm ▸ G.property⟩
    refine ⟨F, ?_, ?_⟩
    · simpa only [hrole, hfg] using hG
    · apply (exists_childMap_step4_null U P q F).mp
      rw [hrecords F G rfl]
      exact (exists_childMap_step4_null V P q' G).mpr hg

variable (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
  (hg : ¬ V.hierarchy.IsFault (V.childNode q' hq' i') g)

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
(S4a), internal case: "paired children i and the unique j"; inherited case:
"same iota, side". The canonical incidence and its side are determined by the
one-step geometry and the corresponding parent facet records. -/
private theorem exists_childMap_step4_incidence :
    (U.recordOf P (U.childNode q hq i) f hf).incidence =
        (V.recordOf P (V.childNode q' hq' i') g hg).incidence ∧
      (U.recordOf P (U.childNode q hq i) f hf).sideIndex =
        (V.recordOf P (V.childNode q' hq' i') g hg).sideIndex := by
  classical
  have hty : q.2.val.ty = q'.2.val.ty := congrArg Sigma.fst hrole
  by_cases hint : ∃ F : FacetName S q.2.val.ty,
      rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier
  · obtain ⟨F, hF⟩ := hint
    let G : FacetName S q'.2.val.ty := ⟨F.val, hty ▸ F.property⟩
    have hG : rolePlacement ⟨q'.2.val.ty, i'⟩ '' g.val.carrier ⊆ G.val.carrier := by
      simpa only [← hrole, ← hfg] using hF
    obtain ⟨hFfinite, hi, hs⟩ := exists_childMap_step4_inherited_incidence P U _ _
      (exists_childMap_step2_parent U q hq i) f F hf
      ((exists_childMap_step4_containment U q hq i f.val F.val).mpr hF)
    obtain ⟨hGfinite, hi', hs'⟩ := exists_childMap_step4_inherited_incidence P V _ _
      (exists_childMap_step2_parent V q' hq' i') g G hg
      ((exists_childMap_step4_containment V q' hq' i' g.val G.val).mpr hG)
    have hr := hrecords F G rfl
    simp only [HonestSource.facetRecordOf, dif_neg hFfinite, dif_neg hGfinite,
      Option.some.injEq] at hr
    exact ⟨hi.trans ((congrArg FacetRecord.incidence hr).trans hi'.symm),
      hs.trans ((congrArg FacetRecord.sideIndex hr).trans hs'.symm)⟩
  · have hint' : ¬ ∃ G : FacetName S q'.2.val.ty,
        rolePlacement ⟨q'.2.val.ty, i'⟩ '' g.val.carrier ⊆ G.val.carrier := by
      rintro ⟨G, hG⟩
      let F : FacetName S q.2.val.ty := ⟨G.val, hty.symm ▸ G.property⟩
      exact hint ⟨F, by simpa only [hrole, hfg] using hG⟩
    obtain ⟨hserv, _, ha⟩ := exists_childMap_step4_internal_provider U q hq i f hf hint
    obtain ⟨hserv', _, ha'⟩ := exists_childMap_step4_internal_provider V q' hq' i' g hg hint'
    have hfirst (W : HonestSource S) (c : W.Node) (F : FacetName S c.2.val.ty)
        (hF : ¬ W.hierarchy.IsFault c F) (hA : W.hierarchy.age c F hF = 1) :
        (W.hierarchy.firstProvider c F hF).2.val = F.val := by
      obtain ⟨hsub, ht⟩ := W.hierarchy.stratumMap_facet c F hF (facetCell F) rfl
      exact ht.symm.trans (W.hierarchy.stratumMap_age_one c F hF hA (facetCell F) hsub)
    let a := U.hierarchy.providerIncidence (U.childNode q hq i) f hf
    let b := V.hierarchy.providerIncidence (V.childNode q' hq' i') g hg
    have haspec := U.hierarchy.providerIncidence_spec (U.childNode q hq i) f hf
    have hbspec := V.hierarchy.providerIncidence_spec (V.childNode q' hq' i') g hg
    have harole : (⟨a.ty, a.left⟩ : S.Role) = ⟨q.2.val.ty, i⟩ :=
      haspec.2.1.trans ((congrArg U.hierarchy.nodeRole hserv).trans
        (exists_childMap_step2_role U q hq i))
    have hbrole : (⟨b.ty, b.left⟩ : S.Role) = ⟨q'.2.val.ty, i'⟩ :=
      hbspec.2.1.trans ((congrArg V.hierarchy.nodeRole hserv').trans
        (exists_childMap_step2_role V q' hq' i'))
    have hleft := harole.trans (hrole.trans hbrole.symm)
    have hafacet : a.leftFacet.val = f.val := haspec.2.2.1.trans (hfirst U _ f hf ha)
    have hbfacet : b.leftFacet.val = g.val := hbspec.2.2.1.trans (hfirst V _ g hg ha')
    have hsame : SameIncidence a b := by
      refine ⟨congrArg Sigma.fst hleft, ?_⟩
      change placedSet (S.child a.ty a.left).frame a.leftFacet.val.carrier =
        placedSet (S.child b.ty b.left).frame b.leftFacet.val.carrier
      rw [hafacet, hbfacet, hfg,
        congrArg (fun r : S.Role => (S.child r.1 r.2).frame) hleft]
    have hinc := exists_childMap_step4_canonical P a b hsame
    refine ⟨hinc, exists_childMap_step4_side P U V _ _ f g hf hg hinc ?_⟩
    exact (congrArg U.hierarchy.nodeRole hserv).trans
      ((exists_childMap_step2_role U q hq i).trans (hrole.trans
        ((exists_childMap_step2_role V q' hq' i').symm.trans
          (congrArg V.hierarchy.nodeRole hserv').symm)))

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
(S4b,b'), internal case: "age 1" and "beta = residue of C"; inherited case:
"same ... beta" and "age min(age+1,C)". These two numeric fields only need
the parent records and the parent's height residue. -/
private theorem exists_childMap_step4_age_residue
    (hresidue : q.1 % P.L = q'.1 % P.L) :
    (U.recordOf P (U.childNode q hq i) f hf).age =
        (V.recordOf P (V.childNode q' hq' i') g hg).age ∧
      (U.recordOf P (U.childNode q hq i) f hf).beta =
        (V.recordOf P (V.childNode q' hq' i') g hg).beta := by
  classical
  have hty : q.2.val.ty = q'.2.val.ty := congrArg Sigma.fst hrole
  by_cases hint : ∃ F : FacetName S q.2.val.ty,
      rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier
  · obtain ⟨F, hF⟩ := hint
    let G : FacetName S q'.2.val.ty := ⟨F.val, hty ▸ F.property⟩
    have hG : rolePlacement ⟨q'.2.val.ty, i'⟩ '' g.val.carrier ⊆ G.val.carrier := by
      simpa only [← hrole, ← hfg] using hF
    obtain ⟨hFfinite, ha, hb⟩ := exists_childMap_step4_inherited_numbers U _ _
      (exists_childMap_step2_parent U q hq i) f F hf
      ((exists_childMap_step4_containment U q hq i f.val F.val).mpr hF)
    obtain ⟨hGfinite, ha', hb'⟩ := exists_childMap_step4_inherited_numbers V _ _
      (exists_childMap_step2_parent V q' hq' i') g G hg
      ((exists_childMap_step4_containment V q' hq' i' g.val G.val).mpr hG)
    have hr := hrecords F G rfl
    simp only [HonestSource.facetRecordOf, dif_neg hFfinite, dif_neg hGfinite,
      Option.some.injEq] at hr
    have hage := congrArg (fun r : FacetRecord P => r.age.val) hr
    have hbeta := congrArg (fun r : FacetRecord P => r.beta.val) hr
    constructor
    · apply Fin.ext
      change min (U.hierarchy.age _ f hf) P.C = min (V.hierarchy.age _ g hg) P.C
      rw [ha, ha']
      change min (U.hierarchy.age q F hFfinite) P.C =
        min (V.hierarchy.age q' G hGfinite) P.C at hage
      omega
    · apply Fin.ext
      change (U.hierarchy.servingChild _ f hf).1 % P.L =
        (V.hierarchy.servingChild _ g hg).1 % P.L
      rw [hb, hb']
      exact hbeta
  · have hint' : ¬ ∃ G : FacetName S q'.2.val.ty,
        rolePlacement ⟨q'.2.val.ty, i'⟩ '' g.val.carrier ⊆ G.val.carrier := by
      rintro ⟨G, hG⟩
      let F : FacetName S q.2.val.ty := ⟨G.val, hty.symm ▸ G.property⟩
      exact hint ⟨F, by simpa only [hrole, hfg] using hG⟩
    obtain ⟨hserv, _, ha⟩ := exists_childMap_step4_internal_provider U q hq i f hf hint
    obtain ⟨hserv', _, ha'⟩ := exists_childMap_step4_internal_provider V q' hq' i' g hg hint'
    constructor
    · apply Fin.ext
      change min (U.hierarchy.age _ f hf) P.C = min (V.hierarchy.age _ g hg) P.C
      rw [ha, ha']
    · apply Fin.ext
      change (U.hierarchy.servingChild _ f hf).1 % P.L =
        (V.hierarchy.servingChild _ g hg).1 % P.L
      rw [hserv, hserv']
      exact exists_childMap_step3_residue P hq hq' hresidue

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
(S4c), internal case: "tau = id"; inherited case:
"tau_f'(s') = tau_f(t(s'))". Corresponding child stratum maps agree after
identifying their facet domains and canonical provider names. -/
private theorem exists_childMap_step4_strata :
    HEq (U.recordOf P (U.childNode q hq i) f hf).tau
      (V.recordOf P (V.childNode q' hq' i') g hg).tau := by
  classical
  have hty : q.2.val.ty = q'.2.val.ty := congrArg Sigma.fst hrole
  have hchild : (U.childNode q hq i).2.val.ty = (V.childNode q' hq' i').2.val.ty :=
    congrArg (fun r : S.Role => (S.child r.1 r.2).ty) hrole
  have hinc : U.recordIncidence P (U.childNode q hq i) f hf =
      V.recordIncidence P (V.childNode q' hq' i') g hg :=
    (exists_childMap_step4_incidence P q q' hq hq' i i' hrole hrecords f g hfg hf hg).1
  have hvalues (e : CellsInFacet (U.childNode q hq i).2.val.ty f)
      (e' : CellsInFacet (V.childNode q' hq' i').2.val.ty g) (he : e.val.val = e'.val.val) :
      (U.recordTau P (U.childNode q hq i) f hf e).val.val =
        (V.recordTau P (V.childNode q' hq' i') g hg e').val.val := by
    by_cases hint : ∃ F : FacetName S q.2.val.ty,
        rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier
    · obtain ⟨F, hF⟩ := hint
      let G : FacetName S q'.2.val.ty := ⟨F.val, hty ▸ F.property⟩
      have hG : rolePlacement ⟨q'.2.val.ty, i'⟩ '' g.val.carrier ⊆ G.val.carrier := by
        simpa only [← hrole, ← hfg] using hF
      have hFsub := (exists_childMap_step4_containment U q hq i f.val F.val).mpr hF
      have hGsub := (exists_childMap_step4_containment V q' hq' i' g.val G.val).mpr hG
      obtain ⟨hFfinite, _, _⟩ := exists_childMap_step4_inherited_incidence P U _ _
        (exists_childMap_step2_parent U q hq i) f F hf hFsub
      obtain ⟨hGfinite, _, _⟩ := exists_childMap_step4_inherited_incidence P V _ _
        (exists_childMap_step2_parent V q' hq' i') g G hg hGsub
      obtain ⟨t, ht, hτ⟩ := exists_childMap_step4_inherited_tau P U _ _
        (exists_childMap_step2_parent U q hq i) f F hf hFfinite hFsub e
      obtain ⟨t', ht', hτ'⟩ := exists_childMap_step4_inherited_tau P V _ _
        (exists_childMap_step2_parent V q' hq' i') g G hg hGfinite hGsub e'
      have ht0 := (exists_childMap_step4_relint_containment U q hq i e.val.val t.val.val).mp ht
      have ht0' := (exists_childMap_step4_relint_containment V q' hq' i' e'.val.val t'.val.val).mp ht'
      have ht1' : relint (rolePlacement ⟨q.2.val.ty, i⟩ '' e.val.val.carrier) ⊆
          relint t'.val.val.carrier := by simpa only [hrole, he] using ht0'
      have htt : t.val.val = t'.val.val := by
        by_contra hne
        have hmem : t'.val.val ∈ (S.cx q.2.val.ty).cells := hty.symm ▸ t'.val.property
        have hd := (S.cx q.2.val.ty).relint_disjoint _ t.val.property _ hmem hne
        have hn : (relint (rolePlacement ⟨q.2.val.ty, i⟩ '' e.val.val.carrier)).Nonempty := by
          rw [exists_childMap_step5_relint_image]
          exact e.val.val.flat.relint_nonempty.image _
        obtain ⟨x, hx⟩ := hn
        exact Set.disjoint_left.mp hd (ht0 hx) (ht1' hx)
      have hr := hrecords F G rfl
      simp only [HonestSource.facetRecordOf, dif_neg hFfinite, dif_neg hGfinite,
        Option.some.injEq] at hr
      exact hτ.trans ((exists_childMap_step4_read_tau hr t t' htt).trans hτ'.symm)
    · have hint' : ¬ ∃ G : FacetName S q'.2.val.ty,
          rolePlacement ⟨q'.2.val.ty, i'⟩ '' g.val.carrier ⊆ G.val.carrier := by
        rintro ⟨G, hG⟩
        let F : FacetName S q.2.val.ty := ⟨G.val, hty.symm ▸ G.property⟩
        exact hint ⟨F, by simpa only [hrole, hfg] using hG⟩
      have hτ := exists_childMap_step4_internal_tau P U q hq i f hf hint e
      have hτ' := exists_childMap_step4_internal_tau P V q' hq' i' g hg hint' e'
      have hn : rolePlacement ⟨q.2.val.ty, i⟩ '' e.val.val.carrier =
          rolePlacement ⟨q'.2.val.ty, i'⟩ '' e'.val.val.carrier := by rw [hrole, he]
      have heq := hτ.trans (hn.trans hτ'.symm)
      have hplace := congrArg (fun a : P.Incidence => rolePlacement ⟨a.val.ty, a.val.left⟩) hinc
      dsimp only at hplace
      rw [hplace] at heq
      apply exists_childMap_step4_cell_eq
      exact (rolePlacement ⟨(V.recordIncidence P (V.childNode q' hq' i') g hg).val.ty,
        (V.recordIncidence P (V.childNode q' hq' i') g hg).val.left⟩).injective.image_injective heq
  have hext {A B : S.ι} (hAB : A = B) {f : FacetName S A} {g : FacetName S B}
      (hfg : f.val = g.val) {a b : PrimitiveIncidence S} (hab : a = b)
      (t : CellsInFacet A f → ProviderCell a) (t' : CellsInFacet B g → ProviderCell b)
      (hv : ∀ e e', e.val.val = e'.val.val → (t e).val.val = (t' e').val.val) : HEq t t' := by
    cases hAB
    cases Subtype.ext hfg
    cases hab
    apply heq_of_eq
    funext e
    exact Subtype.ext (Subtype.ext (hv e e rfl))
  exact hext hchild hfg (congrArg Subtype.val hinc) _ _ hvalues

section ChainGeometry

omit hrole hrecords hfg

/-- Step 1 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"with inherited orientations". The edge of a full flag is a listed edge. -/
private def exists_childMap_step4_chains_step1_edge {A : S.ι}
    (c : FacetFlag S A) : EdgeName S :=
  ⟨A, ⟨(c.cell edgeIndex).val, by
    simp only [CellComplex.edges, Finset.mem_filter]
    exact ⟨(c.cell edgeIndex).property, c.dimension edgeIndex⟩⟩⟩

/-- Step 1 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"with inherited orientations". Read the signed vector from the orientation bit. -/
private def exists_childMap_step4_chains_step1_direction {A : S.ι}
    {f : FacetName S A} (c : OrientedChain f) : E d :=
  if c.forward then edgeVector (exists_childMap_step4_chains_step1_edge c.chain.val)
  else -edgeVector (exists_childMap_step4_chains_step1_edge c.chain.val)

/-- Step 1 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"a chain ... of C". Every cell of the chain is contained in its top facet. -/
private theorem exists_childMap_step4_chains_step1_subset {A : S.ι}
    {f : FacetName S A} (c : OrientedChain f) (j : FlagIndex d) :
    (c.chain.val.cell j).val.carrier ⊆ f.val.carrier := by
  have hj : j.val ≤ (facetIndex : FlagIndex d).val := by
    have := j.property
    change j.val ≤ d - 1
    omega
  simpa only [c.chain.property] using c.chain.val.nested j facetIndex hj

/-- Step 1 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"with inherited orientations". On a line, the inner-product test says exactly
that the oriented vectors are positive multiples of one another. -/
private theorem exists_childMap_step4_chains_step1_positive
    (u v : E d) (hu : u ≠ 0) (hv : v ≠ 0)
    (hline : u ∈ Submodule.span ℝ {v}) (b : Bool) :
    (b = true ↔ 0 < inner ℝ u v) ↔
      ∃ a : ℝ, 0 < a ∧ u = a • (if b then v else -v) := by
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hline
  have hk0 : k ≠ 0 := by
    intro h
    apply hu
    rw [← hk, h, zero_smul]
  have hpos : 0 < inner ℝ v v := real_inner_self_pos.mpr hv
  cases b with
  | false =>
    simp only [Bool.false_eq_true, false_iff, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro h
      have hnonpos : k ≤ 0 := by
        rw [← hk, real_inner_smul_left] at h
        have := le_of_not_gt h
        nlinarith
      refine ⟨-k, neg_pos.mpr (lt_of_le_of_ne hnonpos hk0), ?_⟩
      simpa only [neg_smul, smul_neg, neg_neg] using hk.symm
    · rintro ⟨a, ha, h⟩
      rw [h, real_inner_smul_left, inner_neg_left]
      exact not_lt.mpr (le_of_lt (mul_neg_of_pos_of_neg ha (neg_neg_of_pos hpos)))
  | true =>
    simp only [true_iff, ↓reduceIte]
    constructor
    · intro h
      rw [← hk, real_inner_smul_left] at h
      exact ⟨k, (mul_pos_iff_of_pos_right hpos).mp h, hk.symm⟩
    · rintro ⟨a, ha, h⟩
      rw [h, real_inner_smul_left]
      exact mul_pos ha hpos

/-- Step 1 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"equal affine spans". The direction of a placed segment is generated by
the placed difference of its endpoints. -/
private theorem exists_childMap_step4_chains_step1_segment_direction
    (T : E d ≃ᵃ[ℝ] E d) (x y : E d) :
    (affineSpan ℝ (T '' segment ℝ x y)).direction =
      Submodule.span ℝ {T.linear (y - x)} := by
  change (affineSpan ℝ (T.toAffineMap '' segment ℝ x y)).direction = _
  rw [← AffineSubspace.map_span T.toAffineMap,
    AffineSubspace.map_direction, direction_affineSpan, vectorSpan_segment,
    Submodule.map_span, Set.image_singleton]
  rfl

/-- Step 1 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"the full-chain test". Stratum names and affine spans are the unoriented test. -/
private def exists_childMap_step4_chains_step1_geometry (U : HonestSource S)
    (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (c : OrientedChain f) : Prop :=
  ∀ j : FlagIndex d,
    (U.recordTau P q f hf
      ⟨c.chain.val.cell j, exists_childMap_step4_chains_step1_subset c j⟩).val.val =
      ((P.flag (U.recordIncidence P q f hf)).flag.cell j).val ∧
    affineSpan ℝ (q.2.val.cell q.1 (c.chain.val.cell j).val) =
      affineSpan ℝ (U.providerPlacement P q f hf ''
        ((P.flag (U.recordIncidence P q f hf)).flag.cell j).val.carrier)

/-- Step 1 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"equal affine spans ... with its orientation". Rewrite the geometric definition
using canonical stratum names and a positive multiple of the signed edge vector. -/
private theorem exists_childMap_step4_chains_step1_test (U : HonestSource S)
    (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (c : OrientedChain f) :
    U.ActiveChain P q f hf c ↔
      exists_childMap_step4_chains_step1_geometry U P q f hf c ∧
      ∃ a : ℝ, 0 < a ∧ U.counterDirection P q f hf =
        a • (q.2.val.prototypeFrame q.1).linear
          (exists_childMap_step4_chains_step1_direction c) := by
  let e := exists_childMap_step4_chains_step1_edge c.chain.val
  let v := (q.2.val.prototypeFrame q.1).linear (edgeVector e)
  let u := U.counterDirection P q f hf
  have horient (H : exists_childMap_step4_chains_step1_geometry U P q f hf c) :
      (c.forward = true ↔ 0 < inner ℝ u v) ↔
        ∃ a : ℝ, 0 < a ∧ u = a • (q.2.val.prototypeFrame q.1).linear
          (exists_childMap_step4_chains_step1_direction c) := by
    have hv : v ≠ 0 := by
      exact fun h => (edgeVector_spec e).1
        ((q.2.val.prototypeFrame q.1).linear.injective (h.trans (map_zero _).symm))
    have hu : u ≠ 0 := by
      intro h
      have hzero := (U.providerPlacement P q f hf).linear.injective
        (h.trans (map_zero _).symm)
      exact (P.flag (U.recordIncidence P q f hf)).distinct
        (sub_eq_zero.mp hzero).symm
    have hspan := congrArg AffineSubspace.direction (H edgeIndex).2
    have he : (c.chain.val.cell edgeIndex).val.carrier =
        segment ℝ (Classical.choose (edge_endpoints_exist e)).1
          (Classical.choose (edge_endpoints_exist e)).2 :=
      (Classical.choose_spec (edge_endpoints_exist e)).2
    simp only [FramedNode.cell, he, (P.flag (U.recordIncidence P q f hf)).edge_eq,
      exists_childMap_step4_chains_step1_segment_direction] at hspan
    change Submodule.span ℝ {v} = Submodule.span ℝ {u} at hspan
    have hline : u ∈ Submodule.span ℝ {v} := by
      rw [hspan]
      exact Submodule.mem_span_singleton_self _
    have h := exists_childMap_step4_chains_step1_positive u v hu hv hline c.forward
    simpa only [exists_childMap_step4_chains_step1_direction, apply_ite, map_neg] using h
  constructor
  · intro hc
    have H : exists_childMap_step4_chains_step1_geometry U P q f hf c := by
      intro j
      obtain ⟨hs, ht, hspan⟩ := hc.1 j
      refine ⟨?_, hspan⟩
      have hτ := (Classical.choose_spec (U.recordTau_exists P q f hf
        ⟨c.chain.val.cell j, exists_childMap_step4_chains_step1_subset c j⟩)).1
      exact exists_childMap_step4_cell_eq
        ((U.providerPlacement P q f hf).injective.image_injective (hτ.trans ht))
    exact ⟨H, (horient H).mp hc.2⟩
  · rintro ⟨H, hdir⟩
    refine ⟨?_, (horient H).mpr hdir⟩
    intro j
    refine ⟨U.cellInFacet_placed q f
      ⟨c.chain.val.cell j, exists_childMap_step4_chains_step1_subset c j⟩, ?_, (H j).2⟩
    have hτ := (Classical.choose_spec (U.recordTau_exists P q f hf
      ⟨c.chain.val.cell j, exists_childMap_step4_chains_step1_subset c j⟩)).1
    exact hτ.symm.trans (congrArg
      (fun e : Cell d => U.providerPlacement P q f hf '' e.carrier) (H j).1)

/-- Step 2 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"computed in the fixed substitution geometry". A common full affine frame
can be cancelled from equality of affine spans. -/
private theorem exists_childMap_step4_chains_step2_span
    (T : E d ≃ᵃ[ℝ] E d) (K L : Set (E d)) :
    affineSpan ℝ (T '' K) = affineSpan ℝ (T '' L) ↔
      affineSpan ℝ K = affineSpan ℝ L := by
  change affineSpan ℝ (T.toAffineMap '' K) = affineSpan ℝ (T.toAffineMap '' L) ↔ _
  rw [← AffineSubspace.map_span, ← AffineSubspace.map_span]
  constructor
  · intro h
    apply SetLike.coe_injective
    apply T.injective.image_injective
    exact congrArg (fun A : AffineSubspace ℝ (E d) => (A : Set (E d))) h
  · exact congrArg (AffineSubspace.map T.toAffineMap)

/-- Step 2 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"the flag itself as cells of C, with its orientation". For an internal facet,
the complete activity test is expressed in the fixed one-step geometry. -/
private theorem exists_childMap_step4_chains_step2_internal (U : HonestSource S)
    (P : Params S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hint : ¬ ∃ F : FacetName S q.2.val.ty,
      rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (c : OrientedChain f) :
    U.ActiveChain P (U.childNode q hq i) f hf c ↔
      (∀ j : FlagIndex d,
        rolePlacement ⟨q.2.val.ty, i⟩ '' (c.chain.val.cell j).val.carrier =
          rolePlacement ⟨(U.recordIncidence P (U.childNode q hq i) f hf).val.ty,
            (U.recordIncidence P (U.childNode q hq i) f hf).val.left⟩ ''
            ((P.flag (U.recordIncidence P (U.childNode q hq i) f hf)).flag.cell j).val.carrier) ∧
      ∃ a : ℝ, 0 < a ∧
        (rolePlacement ⟨(U.recordIncidence P (U.childNode q hq i) f hf).val.ty,
          (U.recordIncidence P (U.childNode q hq i) f hf).val.left⟩).linear
            (P.flag (U.recordIncidence P (U.childNode q hq i) f hf)).direction =
          a • (rolePlacement ⟨q.2.val.ty, i⟩).linear
            (exists_childMap_step4_chains_step1_direction c) := by
  let C := U.childNode q hq i
  let a := U.recordIncidence P C f hf
  let R := rolePlacement ⟨q.2.val.ty, i⟩
  let Q := rolePlacement ⟨a.val.ty, a.val.left⟩
  let T := q.2.val.prototypeFrame q.1
  obtain ⟨_, hbirth, _⟩ := exists_childMap_step4_internal_provider U q hq i f hf hint
  have hplace : U.providerPlacement P C f hf = Q.trans T := by
    change (rolePlacement ⟨a.val.ty, a.val.left⟩).trans
      ((U.hierarchy.birthParent C f hf).2.val.prototypeFrame
        (U.hierarchy.birthParent C f hf).1) = _
    rw [hbirth]
  have hframe : C.2.val.prototypeFrame C.1 = R.trans T := by
    simpa only [Nat.sub_add_cancel hq] using exists_childMap_step1_frame q.2.val (q.1-1) i
  have htau (j : FlagIndex d) := exists_childMap_step4_internal_tau P U q hq i f hf hint
    ⟨c.chain.val.cell j, exists_childMap_step4_chains_step1_subset c j⟩
  rw [exists_childMap_step4_chains_step1_test]
  constructor
  · rintro ⟨H, b, hb, hdir⟩
    refine ⟨?_, b, hb, ?_⟩
    · intro j
      exact (htau j).symm.trans (congrArg (fun e : Cell d => Q '' e.carrier) (H j).1)
    · change U.counterDirection P C f hf = _ at hdir
      unfold HonestSource.counterDirection at hdir
      rw [hplace, hframe] at hdir
      apply T.linear.injective
      simpa only [map_smul] using hdir
  · rintro ⟨H, b, hb, hdir⟩
    refine ⟨?_, b, hb, ?_⟩
    · intro j
      refine ⟨?_, ?_⟩
      · exact exists_childMap_step4_cell_eq (Q.injective.image_injective
          ((htau j).trans (H j)))
      · apply congrArg (affineSpan ℝ)
        change C.2.val.prototypeFrame C.1 '' _ = U.providerPlacement P C f hf '' _
        rw [hframe, hplace]
        simpa only [Set.image_image] using congrArg (fun K : Set (E d) => T '' K) (H j)
    · change U.counterDirection P C f hf = _
      unfold HonestSource.counterDirection
      rw [hplace, hframe]
      simpa only [map_smul] using congrArg T.linear hdir

/-- Step 3 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"same ... provider". Inheritance preserves its full placement, including its
canonical flag and oriented direction. -/
private theorem exists_childMap_step4_chains_step3_placement (U : HonestSource S)
    (P : Params S) (c p : U.Node) (hp : U.hierarchy.parentNode c = p)
    (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f) (hF : ¬ U.hierarchy.IsFault p F)
    (hsub : c.2.val.cell c.1 f.val ⊆ p.2.val.cell p.1 F.val) :
    U.recordIncidence P c f hf = U.recordIncidence P p F hF ∧
      U.providerPlacement P c f hf = U.providerPlacement P p F hF ∧
      U.counterDirection P c f hf = U.counterDirection P p F hF := by
  subst p
  obtain ⟨_, hprov, hbirth, _, _⟩ := U.hierarchy.restriction_det_inherited c F f hF hsub
  have hi := exists_childMap_step4_provider_name P U c (U.hierarchy.parentNode c)
    f F hf hF hbirth hprov
  have hplace : U.providerPlacement P c f hf =
      U.providerPlacement P (U.hierarchy.parentNode c) F hF :=
    congrArg₂ (fun (B : U.Node) (a : P.Incidence) => P.incidencePlacement B.2.val B.1 a)
      hbirth hi
  refine ⟨hi, hplace, ?_⟩
  unfold HonestSource.counterDirection
  rw [hplace]
  exact congrArg (fun a : P.Incidence =>
    (U.providerPlacement P (U.hierarchy.parentNode c) F hF).linear (P.flag a).direction) hi

/-- Step 3 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"the chain ... of containing cells ... with inherited orientations".
This relation is tested entirely in the one-step prototype geometry. -/
private def exists_childMap_step4_chains_step3_restriction
    (r : S.Role) {A B : S.ι} {f : FacetName S A} {F : FacetName S B}
    (c : OrientedChain f) (t : OrientedChain F) : Prop :=
  (∀ j : FlagIndex d,
    relint (rolePlacement r '' (c.chain.val.cell j).val.carrier) ⊆
      relint (t.chain.val.cell j).val.carrier) ∧
  (∀ j : FlagIndex d,
    affineSpan ℝ (rolePlacement r '' (c.chain.val.cell j).val.carrier) =
      affineSpan ℝ (t.chain.val.cell j).val.carrier) ∧
  ∃ a : ℝ, 0 < a ∧
    (rolePlacement r).linear (exists_childMap_step4_chains_step1_direction c) =
      a • exists_childMap_step4_chains_step1_direction t

/-- Step 3 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"the unique cell ... with relint s' contained in relint t(s')". Nonempty
relative interiors distinguish the containing names in a proper complex. -/
private theorem exists_childMap_step4_chains_step3_unique {A : S.ι}
    (e t : CellName S A) (K : Set (E d)) (hK : K.Nonempty)
    (he : K ⊆ relint e.val.carrier) (ht : K ⊆ relint t.val.carrier) : e = t := by
  apply Subtype.ext
  by_contra hne
  obtain ⟨x, hx⟩ := hK
  exact Set.disjoint_left.mp
    ((S.cx A).relint_disjoint e.val e.property t.val t.property hne) (he hx) (ht hx)

/-- Step 4 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"If the chain of B is active ... the chain of C". A full chain with the
inherited strata, spans and orientation restricts to an active child chain. -/
private theorem exists_childMap_step4_chains_step4_restrict (U : HonestSource S)
    (P : Params S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) (F : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hsub : rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (c : OrientedChain f) (t : OrientedChain F)
    (ht : U.ActiveChain P q F hF t)
    (hct : exists_childMap_step4_chains_step3_restriction ⟨q.2.val.ty, i⟩ c t) :
    U.ActiveChain P (U.childNode q hq i) f hf c := by
  let C := U.childNode q hq i
  let R := rolePlacement ⟨q.2.val.ty, i⟩
  let T := q.2.val.prototypeFrame q.1
  have hsub' := (exists_childMap_step4_containment U q hq i f.val F.val).mpr hsub
  obtain ⟨hi, hplace, hdir⟩ := exists_childMap_step4_chains_step3_placement U P C q
    (exists_childMap_step2_parent U q hq i) f F hf hF hsub'
  have hframe : C.2.val.prototypeFrame C.1 = R.trans T := by
    simpa only [Nat.sub_add_cancel hq] using exists_childMap_step1_frame q.2.val (q.1-1) i
  obtain ⟨H, b, hb, htb⟩ := (exists_childMap_step4_chains_step1_test U P q F hF t).mp ht
  obtain ⟨hrel, hspan, a, ha, hca⟩ := hct
  apply (exists_childMap_step4_chains_step1_test U P C f hf c).mpr
  refine ⟨?_, b / a, div_pos hb ha, ?_⟩
  · intro j
    obtain ⟨e, he, hτ⟩ := exists_childMap_step4_inherited_tau P U C q
      (exists_childMap_step2_parent U q hq i) f F hf hF hsub'
      ⟨c.chain.val.cell j, exists_childMap_step4_chains_step1_subset c j⟩
    have he' := (exists_childMap_step4_relint_containment U q hq i
      (c.chain.val.cell j).val e.val.val).mp he
    have hn : (relint (R '' (c.chain.val.cell j).val.carrier)).Nonempty := by
      rw [exists_childMap_step5_relint_image]
      exact (c.chain.val.cell j).val.flat.relint_nonempty.image _
    have het : e.val = t.chain.val.cell j :=
      exists_childMap_step4_chains_step3_unique e.val (t.chain.val.cell j) _ hn he' (hrel j)
    have heq : e = ⟨t.chain.val.cell j, exists_childMap_step4_chains_step1_subset t j⟩ :=
      Subtype.ext het
    rw [heq] at hτ
    refine ⟨hτ.trans ((H j).1.trans ?_), ?_⟩
    · exact congrArg (fun a : P.Incidence => ((P.flag a).flag.cell j).val) hi.symm
    · have hspan' := (exists_childMap_step4_chains_step2_span T
        (R '' (c.chain.val.cell j).val.carrier) (t.chain.val.cell j).val.carrier).mpr (hspan j)
      have hspan'' : affineSpan ℝ (C.2.val.cell C.1 (c.chain.val.cell j).val) =
          affineSpan ℝ (q.2.val.cell q.1 (t.chain.val.cell j).val) := by
        change affineSpan ℝ (C.2.val.prototypeFrame C.1 '' _) = _
        rw [hframe]
        simpa only [Set.image_image] using hspan'
      refine hspan''.trans ((H j).2.trans ?_)
      rw [hplace]
      exact congrArg (fun a : P.Incidence => affineSpan ℝ
        (U.providerPlacement P q F hF '' ((P.flag a).flag.cell j).val.carrier)) hi.symm
  · rw [hdir, htb, hframe]
    change b • T.linear (exists_childMap_step4_chains_step1_direction t) =
      (b / a) • T.linear (R.linear (exists_childMap_step4_chains_step1_direction c))
    rw [hca, map_smul, smul_smul, div_mul_cancel₀ b (ne_of_gt ha)]

/-- Step 5 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"Conversely ... t(s'_j) is a j-cell". The hereditary full-flag lemma lifts
an active child chain, retaining its spans and its oriented edge. -/
private theorem exists_childMap_step4_chains_step5_lift (U : HonestSource S)
    (P : Params S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) (F : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hsub : rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (c : OrientedChain f) (hc : U.ActiveChain P (U.childNode q hq i) f hf c) :
    ∃ t : OrientedChain F, U.ActiveChain P q F hF t ∧
      exists_childMap_step4_chains_step3_restriction ⟨q.2.val.ty, i⟩ c t := by
  classical
  let C := U.childNode q hq i
  let R := rolePlacement ⟨q.2.val.ty, i⟩
  let T := q.2.val.prototypeFrame q.1
  have hsub' := (exists_childMap_step4_containment U q hq i f.val F.val).mpr hsub
  obtain ⟨hi, hplace, hdir⟩ := exists_childMap_step4_chains_step3_placement U P C q
    (exists_childMap_step2_parent U q hq i) f F hf hF hsub'
  have hframe : C.2.val.prototypeFrame C.1 = R.trans T := by
    simpa only [Nat.sub_add_cancel hq] using exists_childMap_step1_frame q.2.val (q.1-1) i
  have hflag (j : FlagIndex d) :
      U.providerPlacement P C f hf '' ((P.flag (U.recordIncidence P C f hf)).flag.cell j).val.carrier =
        U.providerPlacement P q F hF '' ((P.flag (U.recordIncidence P q F hF)).flag.cell j).val.carrier := by
    rw [hplace]
    exact congrArg (fun a : P.Incidence =>
      U.providerPlacement P q F hF '' ((P.flag a).flag.cell j).val.carrier) hi
  have hmem : c ∈ U.recordChains P C f hf := by
    simp only [HonestSource.recordChains, Finset.mem_filter]
    exact ⟨by simp [allOrientedChains], hc⟩
  obtain ⟨G, _, hG, _, _⟩ := chain_active_owner U P C f hf c hmem
  have ha : U.hierarchy.ActiveFlag C f hf c.chain.val G := by
    intro j
    obtain ⟨hs, hτ, _⟩ := hc.1 j
    refine ⟨hs, ?_⟩
    apply exists_childMap_step4_cell_eq
    exact ((U.hierarchy.servingChild C f hf).2.val.prototypeFrame
      (U.hierarchy.servingChild C f hf).1).injective.image_injective (hτ.trans (hG j).symm)
  have hp : U.hierarchy.ancestor C 1 = q := by
    simpa only [CoherentHierarchy.ancestor, Function.iterate_one] using
      exists_childMap_step2_parent U q hq i
  obtain ⟨t, ht⟩ := U.hierarchy.active_flags_hereditary q C 1 hp F f hF hf hsub'
    c.chain.val G ha
  have htop : (t.cell facetIndex).val = F.val := by
    let F' : FacetName S q.2.val.ty :=
      ⟨(t.cell facetIndex).val, Finset.mem_filter.mpr
        ⟨(t.cell facetIndex).property, t.dimension facetIndex⟩⟩
    have hFF : q.2.val.cell q.1 F'.val ⊆ q.2.val.cell q.1 F.val :=
      (ht facetIndex).2.choose
    have hd := U.hierarchy.ancestor_descendant q 0
    change q.2.val.IsDescendant q.1 q.2.val q.1 at hd
    rcases facet_dichotomy q.2.val q.2.val q.1 q.1 hd F' with ⟨K, _, hu⟩ | hint
    · exact congrArg Subtype.val ((hu F' Subset.rfl).trans (hu F hFF).symm)
    · obtain ⟨x, hx⟩ := exists_childMap_step5_cell_nonempty q.2.val q.1 F'.val
      exact False.elim (((U.hierarchy.boundaryOffsets_downward q F').1
        (intrinsicInterior_subset hx)).2 (hint hx))
  let tc : OrientedChain F :=
    ⟨⟨t, htop⟩, decide (0 < inner ℝ (U.counterDirection P q F hF)
      (T.linear (edgeVector (exists_childMap_step4_chains_step1_edge t))))⟩
  have htc : U.ActiveChain P q F hF tc := by
    constructor
    · intro j
      obtain ⟨hrel, htF, hstr⟩ := ht j
      have hstr' := hstr.trans ((hG j).trans (hflag j))
      refine ⟨htF, hstr', ?_⟩
      have hCsub : C.2.val.cell C.1 (c.chain.val.cell j).val ⊆
          q.2.val.cell q.1 (t.cell j).val := by
        simpa only [exists_childMap_step5_cell_closure] using closure_mono hrel
      have htstr : q.2.val.cell q.1 (t.cell j).val ⊆
          U.providerPlacement P q F hF ''
            ((P.flag (U.recordIncidence P q F hF)).flag.cell j).val.carrier := by
        have h := closure_mono (U.hierarchy.stratumMap_spec q F hF (t.cell j) htF).1
        simp only [exists_childMap_step5_cell_closure] at h
        exact h.trans_eq hstr'
      have hCspan := (hc.1 j).choose_spec.2.trans (congrArg (affineSpan ℝ) (hflag j))
      apply le_antisymm (affineSpan_mono ℝ htstr)
      exact hCspan.symm.trans_le (affineSpan_mono ℝ hCsub)
    · change (decide (0 < inner ℝ (U.counterDirection P q F hF)
        (T.linear (edgeVector (exists_childMap_step4_chains_step1_edge t)))) = true ↔ _)
      exact decide_eq_true_iff
  refine ⟨tc, htc, ?_, ?_, ?_⟩
  · intro j
    exact (exists_childMap_step4_relint_containment U q hq i
      (c.chain.val.cell j).val (t.cell j).val).mp (ht j).1
  · intro j
    have hCspan := (hc.1 j).choose_spec.2.trans
      ((congrArg (affineSpan ℝ) (hflag j)).trans (htc.1 j).choose_spec.2.symm)
    change affineSpan ℝ (C.2.val.prototypeFrame C.1 '' (c.chain.val.cell j).val.carrier) =
      affineSpan ℝ (T '' (t.cell j).val.carrier) at hCspan
    rw [hframe] at hCspan
    apply (exists_childMap_step4_chains_step2_span T
      (R '' (c.chain.val.cell j).val.carrier) (t.cell j).val.carrier).mp
    simpa only [Set.image_image] using hCspan
  · obtain ⟨_, b, hb, hcb⟩ := (exists_childMap_step4_chains_step1_test U P C f hf c).mp hc
    obtain ⟨_, a, ha, hta⟩ := (exists_childMap_step4_chains_step1_test U P q F hF tc).mp htc
    have heq : b • R.linear (exists_childMap_step4_chains_step1_direction c) =
        a • exists_childMap_step4_chains_step1_direction tc := by
      apply T.linear.injective
      have he := hcb.symm.trans (hdir.trans hta)
      rw [hframe] at he
      simpa only [map_smul] using he
    refine ⟨a / b, div_pos ha hb, ?_⟩
    calc
      _ = b⁻¹ • (b • R.linear (exists_childMap_step4_chains_step1_direction c)) := by
        rw [inv_smul_smul₀ (ne_of_gt hb)]
      _ = b⁻¹ • (a • exists_childMap_step4_chains_step1_direction tc) := congrArg (b⁻¹ • ·) heq
      _ = _ := by rw [smul_smul, ← div_eq_inv_mul]

/-- Step 6 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"the entire oriented chain table". Listed cells and the orientation bit
determine an oriented chain, independently of its proof fields. -/
private theorem exists_childMap_step4_chains_step6_equal {A : S.ι}
    {f : FacetName S A} (c t : OrientedChain f)
    (hcell : ∀ j, (c.chain.val.cell j).val = (t.chain.val.cell j).val)
    (hb : c.forward = t.forward) : c = t := by
  rcases c with ⟨⟨⟨cc, cd, cn⟩, ch⟩, cb⟩
  rcases t with ⟨⟨⟨tc, td, tn⟩, th⟩, tb⟩
  dsimp only at hcell hb
  have heq : cc = tc := funext (fun j => Subtype.ext (hcell j))
  cases heq
  cases hb
  rfl

/-- Step 6 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"depend only on (A,i,f')". Matching prototype and facet names transport
every listed chain and its orientation bit. -/
private theorem exists_childMap_step4_chains_step6_transport {A B : S.ι}
    (hAB : A = B) {f : FacetName S A} {g : FacetName S B} (hfg : f.val = g.val)
    (c : OrientedChain f) :
    ∃ c' : OrientedChain g,
      (∀ j, (c.chain.val.cell j).val = (c'.chain.val.cell j).val) ∧ c.forward = c'.forward := by
  cases hAB
  cases Subtype.ext hfg
  exact ⟨c, fun _ => rfl, rfl⟩

/-- Step 6 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"with inherited orientations". Matching names and bits give the same signed
prototype edge vector, including the chosen endpoint convention. -/
private theorem exists_childMap_step4_chains_step6_direction {A B : S.ι}
    (hAB : A = B) {f : FacetName S A} {g : FacetName S B} (hfg : f.val = g.val)
    (c : OrientedChain f) (c' : OrientedChain g)
    (hcell : ∀ j, (c.chain.val.cell j).val = (c'.chain.val.cell j).val)
    (hb : c.forward = c'.forward) :
    exists_childMap_step4_chains_step1_direction c =
      exists_childMap_step4_chains_step1_direction c' := by
  cases hAB
  cases Subtype.ext hfg
  rw [exists_childMap_step4_chains_step6_equal c c' hcell hb]

/-- Step 6 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"the entire oriented chain table". Its filter lists exactly the active chains. -/
private theorem exists_childMap_step4_chains_step6_mem (U : HonestSource S)
    (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (c : OrientedChain f) :
    c ∈ (U.recordOf P q f hf).chains ↔ U.ActiveChain P q f hf c := by
  classical
  simp [HonestSource.recordOf, HonestSource.recordChains, allOrientedChains]

/-- Step 6 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"the chain ... of B is active". Equality of parent records preserves this
readout at every matching full chain. -/
private theorem exists_childMap_step4_chains_step6_read {P : Params S}
    {r t : FacetRecord P} (h : r = t) (c : OrientedChain r.facet) (c' : OrientedChain t.facet)
    (hcell : ∀ j, (c.chain.val.cell j).val = (c'.chain.val.cell j).val)
    (hb : c.forward = c'.forward) : c ∈ r.chains ↔ c' ∈ t.chains := by
  cases h
  rw [exists_childMap_step4_chains_step6_equal c c' hcell hb]

end ChainGeometry

/-- Step 7 of the V4 proof of `exists_childMap_step4_chains` (V4 2.3):
"Internal chains are the fixed flag" and "the chain ... of B is active".
The fixed internal test and the inherited parent-table test preserve activity
between matching child chains. -/
private theorem exists_childMap_step4_chains_step7_activity
    (c : OrientedChain f) (c' : OrientedChain g)
    (hcell : ∀ j, (c.chain.val.cell j).val = (c'.chain.val.cell j).val)
    (hb : c.forward = c'.forward)
    (hc : U.ActiveChain P (U.childNode q hq i) f hf c) :
    V.ActiveChain P (V.childNode q' hq' i') g hg c' := by
  classical
  have hty : q.2.val.ty = q'.2.val.ty := congrArg Sigma.fst hrole
  have hchild : (U.childNode q hq i).2.val.ty = (V.childNode q' hq' i').2.val.ty :=
    congrArg (fun r : S.Role => (S.child r.1 r.2).ty) hrole
  have hcdir := exists_childMap_step4_chains_step6_direction hchild hfg c c' hcell hb
  by_cases hint : ∃ F : FacetName S q.2.val.ty,
      rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier
  · obtain ⟨F, hF⟩ := hint
    let G : FacetName S q'.2.val.ty := ⟨F.val, hty ▸ F.property⟩
    have hG : rolePlacement ⟨q'.2.val.ty, i'⟩ '' g.val.carrier ⊆ G.val.carrier := by
      simpa only [← hrole, ← hfg] using hF
    obtain ⟨hFfinite, _, _⟩ := exists_childMap_step4_inherited_incidence P U _ _
      (exists_childMap_step2_parent U q hq i) f F hf
      ((exists_childMap_step4_containment U q hq i f.val F.val).mpr hF)
    obtain ⟨hGfinite, _, _⟩ := exists_childMap_step4_inherited_incidence P V _ _
      (exists_childMap_step2_parent V q' hq' i') g G hg
      ((exists_childMap_step4_containment V q' hq' i' g.val G.val).mpr hG)
    have hr := hrecords F G rfl
    simp only [HonestSource.facetRecordOf, dif_neg hFfinite, dif_neg hGfinite,
      Option.some.injEq] at hr
    obtain ⟨t, ht, hct⟩ := exists_childMap_step4_chains_step5_lift U P q hq i f F hf
      hFfinite hF c hc
    obtain ⟨t', htcell, htb⟩ := exists_childMap_step4_chains_step6_transport hty
      (show F.val = G.val from rfl) t
    have htdir := exists_childMap_step4_chains_step6_direction hty
      (show F.val = G.val from rfl) t t' htcell htb
    have ht' : V.ActiveChain P q' G hGfinite t' :=
      (exists_childMap_step4_chains_step6_mem V P q' G hGfinite t').mp
        ((exists_childMap_step4_chains_step6_read hr t t' htcell htb).mp
          ((exists_childMap_step4_chains_step6_mem U P q F hFfinite t).mpr ht))
    apply exists_childMap_step4_chains_step4_restrict V P q' hq' i' g G hg hGfinite hG c' t' ht'
    dsimp only [exists_childMap_step4_chains_step3_restriction] at hct ⊢
    simpa only [hrole, hcell, htcell, hcdir, htdir] using hct
  · have hint' : ¬ ∃ G : FacetName S q'.2.val.ty,
        rolePlacement ⟨q'.2.val.ty, i'⟩ '' g.val.carrier ⊆ G.val.carrier := by
      rintro ⟨G, hG⟩
      let F : FacetName S q.2.val.ty := ⟨G.val, hty.symm ▸ G.property⟩
      exact hint ⟨F, by simpa only [hrole, hfg] using hG⟩
    have hi : U.recordIncidence P (U.childNode q hq i) f hf =
        V.recordIncidence P (V.childNode q' hq' i') g hg :=
      (exists_childMap_step4_incidence P q q' hq hq' i i' hrole hrecords f g hfg hf hg).1
    have htest := (exists_childMap_step4_chains_step2_internal U P q hq i f hf hint c).mp hc
    rw [hi] at htest
    apply (exists_childMap_step4_chains_step2_internal V P q' hq' i' g hg hint' c').mpr
    simpa only [hrole, hcell, hcdir] using htest

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
(S4e): "a chain ... of C is active iff the chain ... of containing cells of B
is active, with inherited orientations". Internal chains are the fixed flag;
the inherited full-chain test determines the entire oriented chain table. -/
private theorem exists_childMap_step4_chains :
    HEq (U.recordOf P (U.childNode q hq i) f hf).chains
      (V.recordOf P (V.childNode q' hq' i') g hg).chains := by
  have hchild : (U.childNode q hq i).2.val.ty = (V.childNode q' hq' i').2.val.ty :=
    congrArg (fun r : S.Role => (S.child r.1 r.2).ty) hrole
  have hext {A B : S.ι} (hAB : A = B) {f : FacetName S A} {g : FacetName S B}
      (hfg : f.val = g.val) (s : Finset (OrientedChain f)) (t : Finset (OrientedChain g))
      (hmem : ∀ c c', (∀ j, (c.chain.val.cell j).val = (c'.chain.val.cell j).val) →
        c.forward = c'.forward → (c ∈ s ↔ c' ∈ t)) : HEq s t := by
    cases hAB
    cases Subtype.ext hfg
    apply heq_of_eq
    apply Finset.ext
    intro c
    exact hmem c c (fun _ => rfl) rfl
  apply hext hchild hfg
  intro c c' hcell hb
  rw [exists_childMap_step4_chains_step6_mem, exists_childMap_step4_chains_step6_mem]
  constructor
  · exact exists_childMap_step4_chains_step7_activity P q q' hq hq' i i' hrole hrecords
      f g hfg hf hg c c' hcell hb
  · exact exists_childMap_step4_chains_step7_activity P q' q hq' hq i' i hrole.symm
      (fun G F h => (hrecords F G h.symm).symm) g f hfg.symm hg hf c' c
      (fun j => (hcell j).symm) hb.symm

section ProfileSteps
omit hrole hrecords hfg

/-- Step 1 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"append i to the role word". The downward list reverses the ancestor list,
so the immediate role is its last letter. -/
private theorem exists_childMap_step4_profile_step1_downRoles
    (U : HonestSource S) (c : U.Node) (a : ℕ) :
    U.downRoles c (a + 1) =
      U.downRoles (U.hierarchy.parentNode c) a ++ [U.hierarchy.nodeRole c] := by
  simp only [HonestSource.downRoles, List.ofFn_succ, List.reverse_cons,
    Fin.val_succ, Fin.val_zero, CoherentHierarchy.ancestor, Function.iterate_zero, id_eq,
    Function.iterate_succ_apply]

/-- Step 2 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"the depth of B below H" increases by one on an inherited facet. -/
private theorem exists_childMap_step4_profile_step2_depth
    (U : HonestSource S) (c p : U.Node) (hp : U.hierarchy.parentNode c = p)
    (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f) (hF : ¬ U.hierarchy.IsFault p F)
    (hsub : c.2.val.cell c.1 f.val ⊆ p.2.val.cell p.1 F.val) :
    (U.hierarchy.firstProvider c f hf).1 = (U.hierarchy.firstProvider p F hF).1 + 1 := by
  obtain ⟨_, ha, _⟩ := exists_childMap_step4_inherited_numbers U c p hp f F hf hsub
  have hc := (U.hierarchy.birthHeight_age_spec c f hf).2.1
  have hp := (U.hierarchy.birthHeight_age_spec p F hF).2.1
  omega

/-- Step 3 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"compute from the finite lookup". A downward word places the recorded node
in its ancestor's prototype, using the full affine frames. -/
private theorem exists_childMap_step4_profile_step3_word_frame
    (U : HonestSource S) (c : U.Node) (a : ℕ) :
    c.2.val.prototypeFrame c.1 =
      (wordPlacement (U.downRoles c a)).trans
        ((U.hierarchy.ancestor c a).2.val.prototypeFrame (U.hierarchy.ancestor c a).1) := by
  induction a generalizing c with
  | zero => simp [HonestSource.downRoles, wordPlacement, CoherentHierarchy.ancestor]
  | succ a ih =>
    have hw (v w : List S.Role) : wordPlacement (v ++ w) =
        (wordPlacement w).trans (wordPlacement v) := by
      induction v with
      | nil => simp [wordPlacement]
      | cons r v ih => simp [wordPlacement, ih, AffineEquiv.trans_assoc]
    have hc : c.2.val.prototypeFrame c.1 =
        (rolePlacement (U.hierarchy.nodeRole c)).trans
          ((U.hierarchy.parentNode c).2.val.prototypeFrame (U.hierarchy.parentNode c).1) := by
      have h := congrArg (fun N : FramedNode S => N.prototypeFrame c.1)
        (U.hierarchy.child_eq c.1 c.2)
      exact h.trans (exists_childMap_step1_frame _ _ _)
    rw [exists_childMap_step4_profile_step1_downRoles, hw]
    simp only [wordPlacement, AffineEquiv.refl_trans]
    rw [hc, ih (U.hierarchy.parentNode c), AffineEquiv.trans_assoc]
    rfl

/-- Step 4 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"same ... side" identifies the serving child's full affine frame. -/
private theorem exists_childMap_step4_profile_step4_serving_frame
    (P : Params S) (U : HonestSource S) (c : U.Node)
    (f : FacetName S c.2.val.ty) (hf : ¬ U.hierarchy.IsFault c f) :
    (U.hierarchy.servingChild c f hf).2.val.prototypeFrame
        (U.hierarchy.servingChild c f hf).1 =
      (rolePlacement ((U.recordIncidence P c f hf).val.sideRole (U.recordSide P c f hf))).trans
        ((U.hierarchy.birthParent c f hf).2.val.prototypeFrame (U.hierarchy.birthHeight c f hf)) := by
  let H := U.hierarchy.servingChild c f hf
  have hrole := (Classical.choose_spec (U.recordSide_exists P c f hf)).1
  change (U.recordIncidence P c f hf).val.sideRole (U.recordSide P c f hf) =
    U.hierarchy.nodeRole H at hrole
  have hframe : H.2.val.prototypeFrame H.1 =
      (rolePlacement (U.hierarchy.nodeRole H)).trans
        ((U.hierarchy.parentNode H).2.val.prototypeFrame (U.hierarchy.parentNode H).1) := by
    have h := congrArg (fun N : FramedNode S => N.prototypeFrame H.1)
      (U.hierarchy.child_eq H.1 H.2)
    exact h.trans (exists_childMap_step1_frame _ _ _)
  exact hframe.trans (congrArg (fun r : S.Role => (rolePlacement r).trans
    ((U.hierarchy.parentNode H).2.val.prototypeFrame (U.hierarchy.parentNode H).1)) hrole.symm)

/-- Step 4 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"the sites are named vertices ... of H". The ambient site is its fixed
side-specific coordinate placed by H's full frame. -/
private theorem exists_childMap_step4_profile_step4_site_placement
    (P : Params S) (U : HonestSource S) (c : U.Node)
    (f : FacetName S c.2.val.ty) (hf : ¬ U.hierarchy.IsFault c f) (a : Fin P.N) :
    U.sitePoint P c f hf a =
      (U.hierarchy.servingChild c f hf).2.val.prototypeFrame (U.hierarchy.servingChild c f hf).1
        (P.sites (U.recordIncidence P c f hf) (U.recordSide P c f hf) a) := by
  rw [exists_childMap_step4_profile_step4_serving_frame P U c f hf]
  simp [HonestSource.sitePoint, HonestSource.providerPlacement, Params.incidencePlacement,
    Params.canonicalSite, rolePlacement, PrimitiveIncidence.sideRole]

/-- Step 4 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"the sites are named vertices of the depth-r subdivision of H". Their
coordinates in H are exactly the fixed side-specific sites. -/
private theorem exists_childMap_step4_profile_step4_site_coordinates
    (P : Params S) (U : HonestSource S) (c : U.Node)
    (f : FacetName S c.2.val.ty) (hf : ¬ U.hierarchy.IsFault c f)
    (a : Fin P.N) (x : E d) :
    U.sitePoint P c f hf a = c.2.val.prototypeFrame c.1 x ↔
      P.sites (U.recordIncidence P c f hf) (U.recordSide P c f hf) a =
        wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) x := by
  rw [exists_childMap_step4_profile_step4_site_placement P U c f hf a,
    exists_childMap_step4_profile_step3_word_frame U c
    (U.hierarchy.firstProvider c f hf).1]
  exact ((U.hierarchy.servingChild c f hf).2.val.prototypeFrame
    (U.hierarchy.servingChild c f hf).1).injective.eq_iff

/-- Step 5 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3, S4d):
"the sites" lie on the selected provider edge, on either serving side. -/
private theorem exists_childMap_step4_profile_step5_site_in_flag
    (P : Params S) (U : HonestSource S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f) (a : Fin P.N) :
    U.sitePoint P q f hf a ∈ U.providerPlacement P q f hf ''
      ((P.flag (U.recordIncidence P q f hf)).flag.cell edgeIndex).val.carrier := by
  let ι := U.recordIncidence P q f hf
  let b := U.recordSide P q f hf
  have h := Set.mem_image_of_mem (S.child ι.val.ty (ι.val.sideIndex b)).frame
    (intrinsicInterior_subset (P.sites_relint ι b a))
  change (S.child ι.val.ty (ι.val.sideIndex b)).frame (P.sites ι b a) ∈
    placedSet (S.child ι.val.ty (ι.val.sideIndex b)).frame
      ((P.sideFlag ι b).cell edgeIndex).val.carrier at h
  rw [P.sideFlag_eq] at h
  obtain ⟨y, hy, hyeq⟩ := h
  have hy' : y = P.canonicalSite ι b a := by
    apply (S.child ι.val.ty ι.val.left).frame.injective
    simpa only [Params.canonicalSite, AffineIsometryEquiv.apply_symm_apply] using hyeq
  exact ⟨y, hy, congrArg (U.providerPlacement P q f hf) hy'⟩

/-- Step 5 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3, S4d):
the counter is read "along" the oriented flag edge. Differences of points on
its supporting line are scalar multiples of the transported direction. -/
private theorem exists_childMap_step4_profile_step5_flag_line
    {ι : PrimitiveIncidence S} (F : OrientedFullFlag ι) (φ : E d ≃ᵃ[ℝ] E d)
    (x y : E d)
    (hx : x ∈ affineSpan ℝ (φ '' (F.flag.cell edgeIndex).val.carrier))
    (hy : y ∈ affineSpan ℝ (φ '' (F.flag.cell edgeIndex).val.carrier)) :
    ∃ t : ℝ, t • φ.linear F.direction = x - y := by
  have hedge : φ '' (F.flag.cell edgeIndex).val.carrier =
      segment ℝ (φ F.initial) (φ F.terminal) := by
    rw [F.edge_eq]
    exact image_segment ℝ φ.toAffineMap _ _
  have hv := AffineSubspace.vsub_mem_direction hx hy
  rw [hedge, ← convexHull_pair, affineSpan_convexHull, direction_affineSpan] at hv
  obtain ⟨t, ht⟩ := mem_vectorSpan_pair_rev.mp hv
  refine ⟨t, ?_⟩
  have hdir : φ.linear F.direction = φ F.terminal - φ F.initial :=
    φ.toAffineMap.linearMap_vsub F.terminal F.initial
  rw [hdir]
  exact ht

/-- Step 5 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3, S4d):
the full-chain test puts an active edge in the flag edge's affine span.
Consequently its points and all sites share one counter direction. -/
private theorem exists_childMap_step4_profile_step5_site_line
    (P : Params S) (U : HonestSource S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (e : CellName S q.2.val.ty) (he : (U.recordOf P q f hf).ChainActive e)
    (a : Fin P.N) (x : E d) (hx : x ∈ affineSpan ℝ (q.2.val.cell q.1 e.val)) :
    ∃ t : ℝ, t • U.counterDirection P q f hf = U.sitePoint P q f hf a - x := by
  classical
  obtain ⟨z, hz, hze⟩ := he
  have hza : U.ActiveChain P q f hf z := (Finset.mem_filter.mp hz).2
  obtain ⟨_, _, hspan⟩ := hza.1 edgeIndex
  rw [hze] at hspan
  rw [hspan] at hx
  exact exists_childMap_step4_profile_step5_flag_line (P.flag (U.recordIncidence P q f hf))
    (U.providerPlacement P q f hf) _ x
    (mem_affineSpan ℝ (exists_childMap_step4_profile_step5_site_in_flag P U q f hf a)) hx

omit [Fact (2 ≤ d)] in
/-- Step 5 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"compute from the finite lookup" is invariant under a full affine frame.
An invertible linear map preserves the sign of the inner product of two
collinear vectors; no similarity or uniform scaling is assumed. -/
private theorem exists_childMap_step4_profile_step5_linear_order
    (L : E d ≃ₗ[ℝ] E d) (u v : E d) (hv : ∃ t : ℝ, t • u = v) :
    inner ℝ (L u) (L v) < 0 ↔ inner ℝ u v < 0 := by
  obtain ⟨t, rfl⟩ := hv
  by_cases hu : u = 0
  · simp [hu]
  · have hLu : L u ≠ 0 := by
      intro h
      exact hu (L.injective (h.trans (map_zero L).symm))
    rw [map_smul, real_inner_smul_right, real_inner_smul_right]
    have hp := real_inner_self_pos.mpr hu
    have hp' := real_inner_self_pos.mpr hLu
    simp only [mul_neg_iff, hp, hp', not_lt_of_ge hp.le, not_lt_of_ge hp'.le,
      and_true, and_false]

/-- Step 5 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"compute from the finite lookup the constants kappa(e')". On an active edge,
the order of its anchor and the sites can be tested in the serving prototype. -/
private theorem exists_childMap_step4_profile_step5_word_count
    (P : Params S) (U : HonestSource S) (c : U.Node)
    (f : FacetName S c.2.val.ty) (hf : ¬ U.hierarchy.IsFault c f)
    (e : CellName S c.2.val.ty) (he : (U.recordOf P c f hf).ChainActive e) :
    (U.sitesBefore P c f hf (c.2.val.prototypeFrame c.1 (cellAnchor e.val))).val =
      (Finset.univ.filter (fun a : Fin P.N =>
        inner ℝ (U.recordOf P c f hf).servingDirection
          (P.sites (U.recordIncidence P c f hf) (U.recordSide P c f hf) a -
            wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1)
              (cellAnchor e.val)) < 0)).card := by
  classical
  let ι := U.recordIncidence P c f hf
  let b := U.recordSide P c f hf
  let H := U.hierarchy.servingChild c f hf
  let ψ := H.2.val.prototypeFrame H.1
  let R := (S.child ι.val.ty ι.val.left).frame.toAffineEquiv.trans
    (S.child ι.val.ty (ι.val.sideIndex b)).frame.symm.toAffineEquiv
  have hframes : R.trans ψ = U.providerPlacement P c f hf := by
    dsimp only [ψ, H]
    rw [exists_childMap_step4_profile_step4_serving_frame P U c f hf]
    apply AffineEquiv.ext
    intro x
    simp [R, rolePlacement, PrimitiveIncidence.sideRole, HonestSource.providerPlacement,
      Params.incidencePlacement, ι, b]
  have hdir : ψ.linear (U.recordOf P c f hf).servingDirection = U.counterDirection P c f hf :=
    congrArg (fun φ : E d ≃ᵃ[ℝ] E d => φ.linear (P.flag ι).direction) hframes
  have hpoint := congrArg (fun φ : E d ≃ᵃ[ℝ] E d => φ (cellAnchor e.val))
    (exists_childMap_step4_profile_step3_word_frame U c (U.hierarchy.firstProvider c f hf).1)
  change c.2.val.prototypeFrame c.1 (cellAnchor e.val) =
    ψ (wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) (cellAnchor e.val)) at hpoint
  dsimp only [HonestSource.sitesBefore]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro a _
  have hsite := exists_childMap_step4_profile_step4_site_placement P U c f hf a
  have hdiff : ψ.linear (P.sites ι b a -
      wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) (cellAnchor e.val)) =
      U.sitePoint P c f hf a - c.2.val.prototypeFrame c.1 (cellAnchor e.val) := by
    calc
      _ = ψ (P.sites ι b a) - ψ
          (wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) (cellAnchor e.val)) :=
        ψ.toAffineMap.linearMap_vsub _ _
      _ = _ := by rw [← hsite, ← hpoint]
  obtain ⟨t, ht⟩ := exists_childMap_step4_profile_step5_site_line P U c f hf e he a _
    (mem_affineSpan ℝ (Set.mem_image_of_mem _ (intrinsicInterior_subset (cellAnchor_mem e.val))))
  have hscalar : t • (U.recordOf P c f hf).servingDirection =
      P.sites ι b a - wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1)
        (cellAnchor e.val) := by
    apply ψ.linear.injective
    rw [map_smul, hdir, hdiff]
    exact ht
  have h := exists_childMap_step4_profile_step5_linear_order ψ.linear
    (U.recordOf P c f hf).servingDirection _ ⟨t, hscalar⟩
  rwa [hdir, hdiff] at h

/-- Step 6 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"every chain-active edge of C lies in a chain-active edge of B".
The containing edge is specified by relative-interior containment in the fixed
one-step geometry, not by an isolated stratum test. -/
private theorem exists_childMap_step4_profile_step6_parent_edge
    (P : Params S) (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1)
    (i : S.I q.2.val.ty) (f : FacetName S (U.childNode q hq i).2.val.ty)
    (F : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hsub : rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (e : CellName S (U.childNode q hq i).2.val.ty)
    (he : (U.recordOf P (U.childNode q hq i) f hf).ChainActive e) :
    ∃ E : CellName S q.2.val.ty, (U.recordOf P q F hF).ChainActive E ∧
      relint (rolePlacement ⟨q.2.val.ty, i⟩ '' e.val.carrier) ⊆ relint E.val.carrier := by
  classical
  let c := U.childNode q hq i
  have hp : U.hierarchy.parentNode c = q := exists_childMap_step2_parent U q hq i
  have hancestor : U.hierarchy.ancestor c 1 = q := by
    simpa only [CoherentHierarchy.ancestor, Function.iterate_one] using hp
  have hsub' := (exists_childMap_step4_containment U q hq i f.val F.val).mpr hsub
  obtain ⟨z, hz, hze⟩ := he
  have hza : U.ActiveChain P c f hf z := (Finset.mem_filter.mp hz).2
  obtain ⟨F₀, _, hF₀, _, _⟩ := chain_active_owner U P c f hf z hz
  have hflag : U.hierarchy.ActiveFlag c f hf z.chain.val F₀ := by
    intro j
    obtain ⟨hsub, hτ, _⟩ := hza.1 j
    refine ⟨hsub, ?_⟩
    apply exists_childMap_step4_cell_eq
    exact ((U.hierarchy.servingChild c f hf).2.val.prototypeFrame
      (U.hierarchy.servingChild c f hf).1).injective.image_injective
        (hτ.trans (hF₀ j).symm)
  obtain ⟨t, ht⟩ := U.hierarchy.active_flags_hereditary q c 1 hancestor F f hF hf
    hsub' z.chain.val F₀ hflag
  have htop : (t.cell facetIndex).val = F.val := by
    let T : FacetName S q.2.val.ty := ⟨(t.cell facetIndex).val,
      Finset.mem_filter.mpr ⟨(t.cell facetIndex).property, t.dimension facetIndex⟩⟩
    have hct : c.2.val.cell c.1 f.val ⊆ q.2.val.cell q.1 T.val := by
      have h := closure_mono (ht facetIndex).1
      simpa only [exists_childMap_step5_cell_closure, z.chain.property] using h
    have hd : c.2.val.IsDescendant c.1 q.2.val q.1 :=
      by
        convert exists_childMap_step1_descendant q.2.val (q.1-1) i using 1
        exact (Nat.sub_add_cancel hq).symm
    obtain huniq | hi := facet_dichotomy q.2.val c.2.val q.1 c.1 hd f
    · obtain ⟨G, _, hu⟩ := huniq
      exact congrArg Subtype.val ((hu T hct).trans (hu F hsub').symm)
    · have hbd := hsub'.trans (U.hierarchy.boundaryOffsets_downward q F).1
      obtain ⟨x, hx⟩ := exists_childMap_step5_cell_nonempty c.2.val c.1 f.val
      exact False.elim ((hbd (intrinsicInterior_subset hx)).2 (hi hx))
  obtain ⟨_, _, hb⟩ := U.hierarchy.provider_inherited q c 1 hancestor F f hF hsub'
  obtain ⟨_, hi, _⟩ := exists_childMap_step4_inherited_incidence P U c q hp f F hf hsub'
  have hplace : U.providerPlacement P c f hf = U.providerPlacement P q F hF :=
    congrArg₂ (fun (B : U.Node) (a : P.Incidence) => P.incidencePlacement B.2.val B.1 a) hb hi
  have hdata (j : FlagIndex d) :
      U.providerPlacement P c f hf '' ((P.flag (U.recordIncidence P c f hf)).flag.cell j).val.carrier =
        U.providerPlacement P q F hF '' ((P.flag (U.recordIncidence P q F hF)).flag.cell j).val.carrier :=
    congrArg₂ (fun (φ : E d ≃ᵃ[ℝ] E d) (a : P.Incidence) =>
      φ '' ((P.flag a).flag.cell j).val.carrier) hplace hi
  have hgeom : ∀ j, ∃ hs : q.2.val.cell q.1 (t.cell j).val ⊆ q.2.val.cell q.1 F.val,
      (U.hierarchy.servingChild q F hF).2.val.cell (U.hierarchy.servingChild q F hF).1
          (U.hierarchy.stratumMap q F hF (t.cell j) hs).val =
        U.providerPlacement P q F hF '' ((P.flag (U.recordIncidence P q F hF)).flag.cell j).val.carrier ∧
      affineSpan ℝ (q.2.val.cell q.1 (t.cell j).val) =
        affineSpan ℝ (U.providerPlacement P q F hF ''
          ((P.flag (U.recordIncidence P q F hF)).flag.cell j).val.carrier) := by
    intro j
    obtain ⟨hrel, hs, hτ⟩ := ht j
    have hτ' := hτ.trans ((hF₀ j).trans (hdata j))
    refine ⟨hs, hτ', ?_⟩
    have hsubC : c.2.val.cell c.1 (z.chain.val.cell j).val ⊆
        q.2.val.cell q.1 (t.cell j).val := by
      simpa only [exists_childMap_step5_cell_closure] using closure_mono hrel
    have hstratum := (U.hierarchy.stratumMap_spec q F hF (t.cell j) hs).1
    rw [hτ] at hstratum
    have hsubP : q.2.val.cell q.1 (t.cell j).val ⊆
        U.providerPlacement P q F hF '' ((P.flag (U.recordIncidence P q F hF)).flag.cell j).val.carrier := by
      have h := closure_mono hstratum
      simp only [exists_childMap_step5_cell_closure] at h
      rwa [(hF₀ j).trans (hdata j)] at h
    apply le_antisymm (affineSpan_mono ℝ hsubP)
    obtain ⟨_, _, hspan⟩ := hza.1 j
    rw [hdata j] at hspan
    rw [← hspan]
    exact affineSpan_mono ℝ hsubC
  have horient : ∃ w : OrientedChain F, w.chain.val = t ∧ U.ActiveChain P q F hF w := by
    let T : FlagChain F := ⟨t, htop⟩
    by_cases h : U.ActiveChain P q F hF ⟨T, true⟩
    · exact ⟨⟨T, true⟩, rfl, h⟩
    · refine ⟨⟨T, false⟩, rfl, hgeom, ?_⟩
      simp only [Bool.false_eq_true, false_iff]
      intro hh
      apply h
      exact ⟨hgeom, by simpa using hh⟩
  obtain ⟨w, hw, hwa⟩ := horient
  refine ⟨t.cell edgeIndex, ⟨w, ?_, ?_⟩, ?_⟩
  · change w ∈ U.recordChains P q F hF
    simp only [HonestSource.recordChains, Finset.mem_filter]
    exact ⟨by simp [allOrientedChains], hwa⟩
  · exact congrArg (fun T : FacetFlag S q.2.val.ty => (T.cell edgeIndex).val) hw
  · apply (exists_childMap_step4_relint_containment U q hq i e.val (t.cell edgeIndex).val).mp
    simpa only [hze] using (ht edgeIndex).1

/-- Step 8 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3, 1.23(c)):
"sites on chain-active edges of B are vertices of B when a >= r".
The active-edge hypothesis retains the selected-owner condition of site persistence. -/
private theorem exists_childMap_step4_profile_step8_mature_site
    (P : Params S) (U : HonestSource S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (hm : P.siteDepth (U.recordIncidence P q f hf) (U.recordSide P q f hf) ≤
      (U.hierarchy.firstProvider q f hf).1)
    (e : CellName S q.2.val.ty) (he : (U.recordOf P q f hf).ChainActive e)
    (a : Fin P.N) (ha : U.sitePoint P q f hf a ∈ q.2.val.cell q.1 e.val) :
    ∃ v : VertexName S q.2.val.ty,
      U.sitePoint P q f hf a = q.2.val.prototypeFrame q.1 (vertexPoint v) := by
  let H := U.hierarchy.servingChild q f hf
  let b := (U.hierarchy.firstProvider q f hf).1
  let ι := U.recordIncidence P q f hf
  let s := U.recordSide P q f hf
  let r := P.siteDepth ι s
  have hheight : H.1 = q.1 + b := U.hierarchy.ancestor_height q b
  have hb : b ≤ H.1 := by omega
  have hdiff : H.1 - b = q.1 := by omega
  have hrn : r ≤ H.1 := by change r ≤ b at hm; omega
  obtain ⟨z, hz, hze⟩ := he
  obtain ⟨F, t, hF, ht, hcells⟩ := chain_active_owner U P q f hf z hz
  have hsidecells (j : FlagIndex d) :
      H.2.val.prototypeFrame H.1 '' ((P.sideFlag ι s).cell j).val.carrier =
        U.providerPlacement P q f hf '' ((P.flag ι).flag.cell j).val.carrier := by
    rw [exists_childMap_step4_profile_step4_serving_frame P U q f hf]
    have h := congrArg (fun K : Set (E d) =>
      (U.hierarchy.birthParent q f hf).2.val.prototypeFrame (U.hierarchy.birthHeight q f hf) ''
        (S.σ.symm '' K)) (P.sideFlag_eq ι s j)
    simpa only [placedSet, Set.image_image] using h
  have hcellsF (j : FlagIndex d) : (F.cell j).val = ((P.sideFlag ι s).cell j).val := by
    apply exists_childMap_step4_cell_eq
    exact (H.2.val.prototypeFrame H.1).injective.image_injective
      ((hF j).trans (hsidecells j).symm)
  have hrole := (Classical.choose_spec (U.recordSide_exists P q f hf)).1
  change ι.val.sideRole s = U.hierarchy.nodeRole H at hrole
  have hnode := congrArg FramedNode.ty (U.hierarchy.child_eq H.1 H.2)
  have htype : ι.val.sideType s = H.2.val.ty :=
    (congrArg (fun r : S.Role => (S.child r.1 r.2).ty) hrole).trans hnode.symm
  have transfer {A B : S.ι} (hAB : A = B) (F : FacetFlag S A) (G : FacetFlag S B)
      (hFG : ∀ j, (F.cell j).val = (G.cell j).val) (r : ℕ) (x : E d) :
      IsSite A F r x → IsSite B G r x := by
    cases hAB
    have heq : F = G := by
      cases F with | mk fc fd fn =>
        cases G with | mk gc gd gn =>
          have he : fc = gc := funext fun j => Subtype.ext (hFG j)
          cases he
          rfl
    cases heq
    exact id
  have hsite : IsSite H.2.val.ty F r ((S.σ ^ r) (P.sites ι s a)) :=
    transfer htype (P.sideFlag ι s) F (fun j => (hcellsF j).symm) r _ (P.sites_valid ι s a)
  have hesub : e.val.carrier ⊆ t.bottom.val.carrier := by
    rw [← hze]
    change _ ⊆ (t.chain.cell TracePiece.bottomIndex).val.carrier
    rw [hcells TracePiece.bottomIndex]
    exact z.chain.val.nested _ _ traceDimension_pos
  have htrace := placedTraceOwner_cells H.2.val H.1 b hb F t t.bottom.val
  rw [ht, hdiff] at htrace
  change q.2.val.cell q.1 t.bottom.val = placedTraceCarrier H.2.val H.1 b F t at htrace
  have hxtrace : U.sitePoint P q f hf a ∈ placedTraceCarrier H.2.val H.1 b F t := by
    rw [← htrace]
    exact Set.image_mono hesub ha
  have hposition : tracePlacement H.2.val H.1 r ((S.σ ^ r) (P.sites ι s a)) =
      U.sitePoint P q f hf a := by
    rw [exists_childMap_step4_profile_step4_site_placement P U q f hf a]
    change H.2.val.frame ((S.σ ^ (H.1-r)) ((S.σ ^ r) (P.sites ι s a))) =
      H.2.val.frame ((S.σ ^ H.1) (P.sites ι s a))
    rw [← LinearEquiv.mul_apply, ← pow_add, Nat.sub_add_cancel hrn]
  have hlisted := placed_site_listed H.2.val H.1 r b hm hb F _ hsite t
    (by rw [hposition]; exact hxtrace)
  rw [ht, hdiff] at hlisted
  obtain ⟨v, hv, hxv⟩ := hlisted
  refine ⟨⟨v, hv⟩, ?_⟩
  obtain ⟨y, hy, hyx⟩ := hxv
  rw [vertexPoint_spec (⟨v, hv⟩ : VertexName S q.2.val.ty)] at hy
  cases Set.mem_singleton_iff.mp hy
  simpa only [hposition] using hyx.symm

/-- Step 7 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3, S4d):
"kappa is constant on relint e" once the owner reaches its side's site depth.
Listed vertices cannot lie in the relative interior of a listed edge. Each
site's continuous signed coordinate therefore has a constant sign there. -/
private theorem exists_childMap_step4_profile_step7_mature_constant
    (P : Params S) (U : HonestSource S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (hm : P.siteDepth (U.recordIncidence P q f hf) (U.recordSide P q f hf) ≤
      (U.hierarchy.firstProvider q f hf).1)
    (e : CellName S q.2.val.ty) (he : (U.recordOf P q f hf).ChainActive e)
    (x y : E d) (hx : x ∈ relint (q.2.val.cell q.1 e.val))
    (hy : y ∈ relint (q.2.val.cell q.1 e.val)) :
    U.sitesBefore P q f hf x = U.sitesBefore P q f hf y := by
  classical
  have hdim : e.val.dim = 1 := by
    obtain ⟨z, _, hze⟩ := he
    rw [← hze]
    exact z.chain.val.dimension edgeIndex
  have hnosite (a : Fin P.N) : U.sitePoint P q f hf a ∉ relint (q.2.val.cell q.1 e.val) := by
    intro ha
    obtain ⟨v, hv⟩ := exists_childMap_step4_profile_step8_mature_site P U q f hf hm e he a
      (intrinsicInterior_subset ha)
    rw [hv, FramedNode.cell, exists_childMap_step5_relint_image] at ha
    have hvrel : vertexPoint v ∈ relint e.val.carrier :=
      (q.2.val.prototypeFrame q.1).injective.mem_set_image.mp ha
    have hvdim : v.val.dim = 0 := (Finset.mem_filter.mp v.property).2
    have hvne : v.val ≠ e.val := by intro h; rw [h, hdim] at hvdim; omega
    have hvself : vertexPoint v ∈ relint v.val.carrier := by
      rw [vertexPoint_spec]
      simp only [relint, intrinsicInterior_singleton, Set.mem_singleton_iff]
    exact Set.disjoint_left.mp ((S.cx q.2.val.ty).relint_disjoint v.val
      (Finset.mem_filter.mp v.property).1 e.val e.property hvne) hvself hvrel
  have hconn : IsPreconnected (relint (q.2.val.cell q.1 e.val)) := by
    rw [FramedNode.cell, exists_childMap_step5_relint_image]
    exact e.val.flat.relint_connected.isPreconnected.image _
      (q.2.val.prototypeFrame q.1).toHomeomorphOfFiniteDimensional.continuous.continuousOn
  by_cases hD : U.counterDirection P q f hf = 0
  · simp only [HonestSource.sitesBefore, hD, inner_zero_left]
  · have hpos := real_inner_self_pos.mpr hD
    have hnonzero (a : Fin P.N) (z : E d) (hz : z ∈ relint (q.2.val.cell q.1 e.val)) :
        inner ℝ (U.counterDirection P q f hf) (U.sitePoint P q f hf a - z) ≠ 0 := by
      obtain ⟨t, ht⟩ := exists_childMap_step4_profile_step5_site_line P U q f hf e he a z
        (mem_affineSpan ℝ (intrinsicInterior_subset hz))
      intro hzero
      rw [← ht, real_inner_smul_right] at hzero
      have ht0 : t = 0 := (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hpos)
      have heq : U.sitePoint P q f hf a = z := sub_eq_zero.mp (by rw [← ht, ht0, zero_smul])
      exact hnosite a (heq.symm ▸ hz)
    apply Fin.ext
    dsimp only [HonestSource.sitesBefore]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro a _
    have hcont : ContinuousOn
        (fun z : E d => inner ℝ (U.counterDirection P q f hf) (U.sitePoint P q f hf a - z))
        (relint (q.2.val.cell q.1 e.val)) :=
      (continuous_const.inner (continuous_const.sub continuous_id)).continuousOn
    exact ⟨fun h => hconn.gt_of_ne hcont (hnonzero a) ⟨x, hx, h⟩ hy,
      fun h => hconn.gt_of_ne hcont (hnonzero a) ⟨y, hy, h⟩ hx⟩

/-- Step 9 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"same ... provider" and "same ... side" preserve the ambient sites and their
counting function along an inherited facet. -/
private theorem exists_childMap_step4_profile_step9_inherited_sites
    (P : Params S) (U : HonestSource S) (c p : U.Node)
    (hp : U.hierarchy.parentNode c = p)
    (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f) (hF : ¬ U.hierarchy.IsFault p F)
    (hsub : c.2.val.cell c.1 f.val ⊆ p.2.val.cell p.1 F.val) :
    (∀ a, U.sitePoint P c f hf a = U.sitePoint P p F hF a) ∧
      ∀ x, U.sitesBefore P c f hf x = U.sitesBefore P p F hF x := by
  subst p
  obtain ⟨_, _, hb, _, _⟩ := U.hierarchy.restriction_det_inherited c F f hF hsub
  obtain ⟨_, hi, hs⟩ := exists_childMap_step4_inherited_incidence P U c
    (U.hierarchy.parentNode c) rfl f F hf hsub
  have hplace : U.providerPlacement P c f hf =
      U.providerPlacement P (U.hierarchy.parentNode c) F hF := by
    exact congrArg₂ (fun (b : U.Node) (j : P.Incidence) =>
      P.incidencePlacement b.2.val b.1 j) hb hi
  have hsite (a : Fin P.N) : U.sitePoint P c f hf a =
      U.sitePoint P (U.hierarchy.parentNode c) F hF a := by
    simp only [HonestSource.sitePoint, hplace, hi, hs]
  refine ⟨hsite, fun x => ?_⟩
  have hdir : U.counterDirection P c f hf =
      U.counterDirection P (U.hierarchy.parentNode c) F hF :=
    congrArg₂ (fun (p : E d ≃ᵃ[ℝ] E d) (j : P.Incidence) =>
      p.linear (P.flag j).direction) hplace hi
  simp only [HonestSource.sitesBefore, hdir, hsite]

/-- Step 10 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"activity being decided by the full-chain test". Equal chain tables give equal
edge support and endpoint support tests, including empty tables. -/
private theorem exists_childMap_step4_profile_step10_chain_tests
    {A B : S.ι} (hAB : A = B) {f : FacetName S A} {g : FacetName S B}
    (hfg : f.val = g.val) (C : Finset (OrientedChain f)) (D : Finset (OrientedChain g))
    (hCD : HEq C D) :
    (∀ (e : CellName S A) (e' : CellName S B), e.val = e'.val →
      ((∃ c ∈ C, (c.chain.val.cell edgeIndex).val = e.val) ↔
        ∃ c ∈ D, (c.chain.val.cell edgeIndex).val = e'.val)) ∧
    (∀ x : E d, (∃ c ∈ C, x ∈ (c.chain.val.cell edgeIndex).val.carrier) ↔
      ∃ c ∈ D, x ∈ (c.chain.val.cell edgeIndex).val.carrier) := by
  cases hAB
  cases Subtype.ext hfg
  cases eq_of_heq hCD
  refine ⟨?_, fun _ => Iff.rfl⟩
  intro e e' he
  cases Subtype.ext he
  rfl

/-- Step 11 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"the sites are named vertices". Equal vertex cells name the same point even
when their prototype indices differ. -/
private theorem exists_childMap_step4_profile_step11_vertex
    {A B : S.ι} (v : VertexName S A) (w : VertexName S B) (h : v.val = w.val) :
    vertexPoint v = vertexPoint w := by
  apply Set.singleton_injective
  exact (vertexPoint_spec v).symm.trans ((congrArg Cell.carrier h).trans (vertexPoint_spec w))

/-- Step 12 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"constants ... and the site statuses of their endpoints" are the two fields
of the mature profile. Pointwise agreement determines that profile. -/
private theorem exists_childMap_step4_profile_step12_constant_ext
    {P : Params S} {A B : S.ι} (hAB : A = B)
    (C : ConstantProfile P A) (D : ConstantProfile P B)
    (hv : ∀ e e', e.val = e'.val → C.value e = D.value e')
    (hs : ∀ v v', v.val = v'.val → C.endpointSite v = D.endpointSite v') : HEq C D := by
  cases hAB
  apply heq_of_eq
  cases C with | mk cv cs =>
    cases D with | mk dv ds =>
      have hv' : cv = dv := funext fun e => hv e e rfl
      have hs' : cs = ds := funext fun v => hs v v rfl
      cases hv'
      cases hs'
      rfl

/-- Step 13 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"append i and compute from the finite lookup". The full downward word, incidence,
side and chain table determine the constants, also at the transition depth. -/
private theorem exists_childMap_step4_profile_step13_word_constants
    (P : Params S) (U V : HonestSource S) (c : U.Node) (c' : V.Node)
    (f : FacetName S c.2.val.ty) (g : FacetName S c'.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f) (hg : ¬ V.hierarchy.IsFault c' g)
    (hty : c.2.val.ty = c'.2.val.ty) (hfg : f.val = g.val)
    (hi : U.recordIncidence P c f hf = V.recordIncidence P c' g hg)
    (hs : U.recordSide P c f hf = V.recordSide P c' g hg)
    (hc : HEq (U.recordChains P c f hf) (V.recordChains P c' g hg))
    (hw : U.downRoles c (U.hierarchy.firstProvider c f hf).1 =
      V.downRoles c' (V.hierarchy.firstProvider c' g hg).1) :
    HEq (U.constantProfile P c f hf) (V.constantProfile P c' g hg) := by
  classical
  obtain ⟨hedge, hend⟩ := exists_childMap_step4_profile_step10_chain_tests hty hfg _ _ hc
  have hdir : (U.recordOf P c f hf).servingDirection =
      (V.recordOf P c' g hg).servingDirection :=
    congrArg₂ (fun (j : P.Incidence) (b : Bool) =>
      (S.child j.val.ty (j.val.sideIndex b)).rotation.symm
        ((S.child j.val.ty j.val.left).rotation (P.flag j).direction)) hi hs
  apply exists_childMap_step4_profile_step12_constant_ext hty
  · intro e e' he
    have hae := hedge e e' he
    change (if _ then some _ else none) = (if _ then some _ else none)
    by_cases ha : ∃ z ∈ U.recordChains P c f hf, (z.chain.val.cell edgeIndex).val = e.val
    · rw [if_pos ha, if_pos (hae.mp ha)]
      congr 1
      apply Fin.ext
      rw [exists_childMap_step4_profile_step5_word_count P U c f hf e ha,
        exists_childMap_step4_profile_step5_word_count P V c' g hg e' (hae.mp ha)]
      simp only [hdir, hi, hs, hw, he]
    · rw [if_neg ha, if_neg (fun h => ha (hae.mpr h))]
  · intro v v' hv
    have hp := exists_childMap_step4_profile_step11_vertex v v' hv
    have hae := hend (vertexPoint v)
    rw [hp] at hae
    change (if _ then some _ else none) = (if _ then some _ else none)
    by_cases ha : ∃ z ∈ U.recordChains P c f hf,
        vertexPoint v ∈ (z.chain.val.cell edgeIndex).val.carrier
    · have ha' : ∃ z ∈ V.recordChains P c' g hg,
          vertexPoint v' ∈ (z.chain.val.cell edgeIndex).val.carrier := hae.mp (hp ▸ ha)
      rw [if_pos ha, if_pos ha']
      congr 1
      apply List.any_congr rfl
      intro a
      simp only [exists_childMap_step4_profile_step4_site_coordinates, hi, hs, hw, hp]
    · have ha' : ¬ ∃ z ∈ V.recordChains P c' g hg,
          vertexPoint v' ∈ (z.chain.val.cell edgeIndex).val.carrier := by
        intro h
        exact ha (hp.symm ▸ hae.mpr h)
      rw [if_neg ha, if_neg ha']

/-- Step 14 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"if a+1 < r ...; if a+1 >= r ...". Equal depths and words select the same
profile branch; at maturity the word lookup supplies its two fields. -/
private theorem exists_childMap_step4_profile_step14_word_profile
    (P : Params S) (U V : HonestSource S) (c : U.Node) (c' : V.Node)
    (f : FacetName S c.2.val.ty) (g : FacetName S c'.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f) (hg : ¬ V.hierarchy.IsFault c' g)
    (hty : c.2.val.ty = c'.2.val.ty) (hfg : f.val = g.val)
    (hi : U.recordIncidence P c f hf = V.recordIncidence P c' g hg)
    (hs : U.recordSide P c f hf = V.recordSide P c' g hg)
    (hc : HEq (U.recordChains P c f hf) (V.recordChains P c' g hg))
    (ha : (U.hierarchy.firstProvider c f hf).1 = (V.hierarchy.firstProvider c' g hg).1)
    (hw : U.downRoles c (U.hierarchy.firstProvider c f hf).1 =
      V.downRoles c' (V.hierarchy.firstProvider c' g hg).1) :
    HEq (U.counterProfile P c f hf) (V.counterProfile P c' g hg) := by
  classical
  have hshort : ((U.hierarchy.firstProvider c f hf).1 <
      P.siteDepth (U.recordIncidence P c f hf) (U.recordSide P c f hf)) ↔
      ((V.hierarchy.firstProvider c' g hg).1 <
        P.siteDepth (V.recordIncidence P c' g hg) (V.recordSide P c' g hg)) := by
    rw [ha, hi, hs]
  unfold HonestSource.counterProfile
  dsimp only
  by_cases h : (U.hierarchy.firstProvider c f hf).1 <
      P.siteDepth (U.recordIncidence P c f hf) (U.recordSide P c f hf)
  · rw [dif_pos h, dif_pos (hshort.mp h)]
    have aux {A B : S.ι} (hAB : A = B) (w w' : ShortProfile P)
        (hw : w.word = w'.word) :
        HEq (Sum.inr w : ConstantProfile P A ⊕ ShortProfile P)
          (Sum.inr w' : ConstantProfile P B ⊕ ShortProfile P) := by
      cases hAB
      cases w
      cases w'
      cases hw
      rfl
    exact aux hty _ _ hw
  · rw [dif_neg h, dif_neg (fun h' => h (hshort.mpr h'))]
    have hconst := exists_childMap_step4_profile_step13_word_constants P U V c c' f g
      hf hg hty hfg hi hs hc hw
    have aux {A B : S.ι} (hAB : A = B) (C : ConstantProfile P A)
        (D : ConstantProfile P B) (hCD : HEq C D) :
        HEq (Sum.inl C : ConstantProfile P A ⊕ ShortProfile P)
          (Sum.inl D : ConstantProfile P B ⊕ ShortProfile P) := by
      cases hAB
      cases eq_of_heq hCD
      rfl
    exact aux hty _ _ hconst

/-- Step 15 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"if the profile is a role word, let a be its length". Equal parent records
either expose equal depths and words or are both already mature. -/
private theorem exists_childMap_step4_profile_step15_parent_branch
    (P : Params S) (U V : HonestSource S) (q : U.Node) (q' : V.Node)
    (F : FacetName S q.2.val.ty) (G : FacetName S q'.2.val.ty)
    (hF : ¬ U.hierarchy.IsFault q F) (hG : ¬ V.hierarchy.IsFault q' G)
    (hr : U.recordOf P q F hF = V.recordOf P q' G hG) :
    ((U.hierarchy.firstProvider q F hF).1 = (V.hierarchy.firstProvider q' G hG).1 ∧
      U.downRoles q (U.hierarchy.firstProvider q F hF).1 =
        V.downRoles q' (V.hierarchy.firstProvider q' G hG).1) ∨
    (P.siteDepth (U.recordIncidence P q F hF) (U.recordSide P q F hF) ≤
        (U.hierarchy.firstProvider q F hF).1 ∧
      P.siteDepth (V.recordIncidence P q' G hG) (V.recordSide P q' G hG) ≤
        (V.hierarchy.firstProvider q' G hG).1) := by
  classical
  have htag := congrArg (fun r : FacetRecord P => r.counter.isLeft) hr
  by_cases h : (U.hierarchy.firstProvider q F hF).1 <
      P.siteDepth (U.recordIncidence P q F hF) (U.recordSide P q F hF)
  · have h' : (V.hierarchy.firstProvider q' G hG).1 <
        P.siteDepth (V.recordIncidence P q' G hG) (V.recordSide P q' G hG) := by
      by_contra hn
      simp [HonestSource.recordOf, HonestSource.counterProfile, h, hn] at htag
    have hw := congrArg (fun r : FacetRecord P =>
      match r.counter with | .inl _ => [] | .inr w => w.word) hr
    simp only [HonestSource.recordOf, HonestSource.counterProfile, dif_pos h, dif_pos h'] at hw
    have hl := congrArg List.length hw
    simp only [HonestSource.downRoles, List.length_reverse, List.length_ofFn] at hl
    exact Or.inl ⟨hl, hw⟩
  · right
    refine ⟨Nat.le_of_not_lt h, ?_⟩
    by_contra hn
    have h' := Nat.lt_of_not_ge hn
    simp [HonestSource.recordOf, HonestSource.counterProfile, h, h'] at htag

/-- Step 16 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"if the profile already consists of constants". Equality of mature parent
records preserves every named counter and endpoint entry. -/
private theorem exists_childMap_step4_profile_step16_parent_entries
    (P : Params S) (U V : HonestSource S) (q : U.Node) (q' : V.Node)
    (F : FacetName S q.2.val.ty) (G : FacetName S q'.2.val.ty)
    (hF : ¬ U.hierarchy.IsFault q F) (hG : ¬ V.hierarchy.IsFault q' G)
    (hr : U.recordOf P q F hF = V.recordOf P q' G hG)
    (hm : P.siteDepth (U.recordIncidence P q F hF) (U.recordSide P q F hF) ≤
      (U.hierarchy.firstProvider q F hF).1)
    (hm' : P.siteDepth (V.recordIncidence P q' G hG) (V.recordSide P q' G hG) ≤
      (V.hierarchy.firstProvider q' G hG).1) :
    (∀ e e', e.val = e'.val →
      (U.constantProfile P q F hF).value e = (V.constantProfile P q' G hG).value e') ∧
    (∀ v v', v.val = v'.val →
      (U.constantProfile P q F hF).endpointSite v =
        (V.constantProfile P q' G hG).endpointSite v') := by
  have aux {r t : FacetRecord P} (h : r = t)
      (C : ConstantProfile P r.ty) (D : ConstantProfile P t.ty)
      (hC : r.counter = .inl C) (hD : t.counter = .inl D) :
      (∀ e e', e.val = e'.val → C.value e = D.value e') ∧
      (∀ v v', v.val = v'.val → C.endpointSite v = D.endpointSite v') := by
    cases h
    cases Sum.inl.inj (hC.symm.trans hD)
    constructor
    · intro e e' he
      cases Subtype.ext he
      rfl
    · intro v v' hv
      cases Subtype.ext hv
      rfl
  exact aux hr _ _
    (by simp only [HonestSource.recordOf, HonestSource.counterProfile, dif_neg (not_lt.mpr hm)])
    (by simp only [HonestSource.recordOf, HonestSource.counterProfile, dif_neg (not_lt.mpr hm')])

/-- Step 17 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"inherits kappa(e') = kappa(e)". The child's anchor is inside its containing
parent edge, where the unchanged ambient counting function is constant. -/
private theorem exists_childMap_step4_profile_step17_inherited_value
    (P : Params S) (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1)
    (i : S.I q.2.val.ty) (f : FacetName S (U.childNode q hq i).2.val.ty)
    (F : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hsub : rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (hm : P.siteDepth (U.recordIncidence P q F hF) (U.recordSide P q F hF) ≤
      (U.hierarchy.firstProvider q F hF).1)
    (e : CellName S (U.childNode q hq i).2.val.ty) (E : CellName S q.2.val.ty)
    (he : (U.recordOf P (U.childNode q hq i) f hf).ChainActive e)
    (hE : (U.recordOf P q F hF).ChainActive E)
    (heE : relint (rolePlacement ⟨q.2.val.ty, i⟩ '' e.val.carrier) ⊆ relint E.val.carrier) :
    (U.constantProfile P (U.childNode q hq i) f hf).value e =
      (U.constantProfile P q F hF).value E := by
  classical
  change ∃ z ∈ U.recordChains P (U.childNode q hq i) f hf,
    (z.chain.val.cell edgeIndex).val = e.val at he
  change ∃ z ∈ U.recordChains P q F hF, (z.chain.val.cell edgeIndex).val = E.val at hE
  change (if _ then some _ else none) = (if _ then some _ else none)
  rw [if_pos he, if_pos hE]
  congr 1
  have hsub' := (exists_childMap_step4_containment U q hq i f.val F.val).mpr hsub
  rw [(exists_childMap_step4_profile_step9_inherited_sites P U _ _
    (exists_childMap_step2_parent U q hq i) f F hf hF hsub').2]
  apply exists_childMap_step4_profile_step7_mature_constant P U q F hF hm E hE
  · apply (exists_childMap_step4_relint_containment U q hq i e.val E.val).mpr heE
    rw [FramedNode.cell, exists_childMap_step5_relint_image]
    exact Set.mem_image_of_mem _ (cellAnchor_mem e.val)
  · rw [FramedNode.cell, exists_childMap_step5_relint_image]
    exact Set.mem_image_of_mem _ (cellAnchor_mem E.val)

/-- Step 18 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"the site status ... is inherited if v' is a vertex of B ... and is not a site
otherwise". On a mature active edge, a site is precisely a flagged parent vertex. -/
private theorem exists_childMap_step4_profile_step18_endpoint_lookup
    (P : Params S) (U : HonestSource S) (q : U.Node)
    (F : FacetName S q.2.val.ty) (hF : ¬ U.hierarchy.IsFault q F)
    (hm : P.siteDepth (U.recordIncidence P q F hF) (U.recordSide P q F hF) ≤
      (U.hierarchy.firstProvider q F hF).1)
    (E : CellName S q.2.val.ty) (hE : (U.recordOf P q F hF).ChainActive E)
    (x : Enforce.E d) (hx : x ∈ q.2.val.cell q.1 E.val) :
    (∃ a, U.sitePoint P q F hF a = x) ↔
      ∃ v : VertexName S q.2.val.ty, q.2.val.prototypeFrame q.1 (vertexPoint v) = x ∧
        (U.constantProfile P q F hF).endpointSite v = some true := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨v, hv⟩ := exists_childMap_step4_profile_step8_mature_site P U q F hF hm E hE a hx
    refine ⟨v, hv.symm, ?_⟩
    have hvE : vertexPoint v ∈ E.val.carrier := by
      rw [hv] at hx
      exact (q.2.val.prototypeFrame q.1).injective.mem_set_image.mp hx
    obtain ⟨z, hz, hze⟩ := hE
    have hendpoint : ∃ z ∈ U.recordChains P q F hF,
        vertexPoint v ∈ (z.chain.val.cell edgeIndex).val.carrier :=
      ⟨z, hz, by simpa only [hze] using hvE⟩
    simp only [HonestSource.constantProfile, if_pos hendpoint, Option.some.injEq,
      List.any_eq_true, Finset.mem_toList, Finset.mem_univ, true_and, decide_eq_true_eq]
    exact ⟨a, hv⟩
  · rintro ⟨v, hv, hflag⟩
    have ha : ∃ a, U.sitePoint P q F hF a = q.2.val.prototypeFrame q.1 (vertexPoint v) := by
      simp only [HonestSource.constantProfile] at hflag
      split_ifs at hflag with h
      simpa only [Option.some.injEq, List.any_eq_true, Finset.mem_toList,
        Finset.mem_univ, true_and, decide_eq_true_eq] using hflag
    obtain ⟨a, ha⟩ := ha
    exact ⟨a, ha.trans hv⟩

/-- Step 19 of the V4 proof of `exists_childMap_step4_profile` (V4 2.3):
"each chain-active edge ... inherits" and old endpoint flags inherit.
Apply the single-edge laws to the equal mature parent entries; the containing
edge and the old-vertex test use only the common substitution geometry. -/
private theorem exists_childMap_step4_profile_step19_mature_constants
    (P : Params S) (U V : HonestSource S) (q : U.Node) (q' : V.Node)
    (hq : 1 ≤ q.1) (hq' : 1 ≤ q'.1) (i : S.I q.2.val.ty) (i' : S.I q'.2.val.ty)
    (hrole : (⟨q.2.val.ty, i⟩ : S.Role) = ⟨q'.2.val.ty, i'⟩)
    (f : FacetName S (U.childNode q hq i).2.val.ty)
    (g : FacetName S (V.childNode q' hq' i').2.val.ty) (hfg : f.val = g.val)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hg : ¬ V.hierarchy.IsFault (V.childNode q' hq' i') g)
    (F : FacetName S q.2.val.ty) (G : FacetName S q'.2.val.ty)
    (hF : ¬ U.hierarchy.IsFault q F) (hG : ¬ V.hierarchy.IsFault q' G)
    (hsub : rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (hsub' : rolePlacement ⟨q'.2.val.ty, i'⟩ '' g.val.carrier ⊆ G.val.carrier)
    (hr : U.recordOf P q F hF = V.recordOf P q' G hG)
    (hm : P.siteDepth (U.recordIncidence P q F hF) (U.recordSide P q F hF) ≤
      (U.hierarchy.firstProvider q F hF).1)
    (hm' : P.siteDepth (V.recordIncidence P q' G hG) (V.recordSide P q' G hG) ≤
      (V.hierarchy.firstProvider q' G hG).1)
    (hc : HEq (U.recordChains P (U.childNode q hq i) f hf)
      (V.recordChains P (V.childNode q' hq' i') g hg)) :
    HEq (U.constantProfile P (U.childNode q hq i) f hf)
      (V.constantProfile P (V.childNode q' hq' i') g hg) := by
  classical
  have hty : q.2.val.ty = q'.2.val.ty := congrArg Sigma.fst hrole
  have hchild : (U.childNode q hq i).2.val.ty = (V.childNode q' hq' i').2.val.ty :=
    congrArg (fun r : S.Role => (S.child r.1 r.2).ty) hrole
  obtain ⟨hedge, hend⟩ := exists_childMap_step4_profile_step10_chain_tests hchild hfg _ _ hc
  obtain ⟨hvalues, hflags⟩ := exists_childMap_step4_profile_step16_parent_entries P U V
    q q' F G hF hG hr hm hm'
  have hactive (E : CellName S q.2.val.ty) (E' : CellName S q'.2.val.ty)
      (hEE : E.val = E'.val) :
      (U.recordOf P q F hF).ChainActive E ↔ (V.recordOf P q' G hG).ChainActive E' := by
    have aux {r t : FacetRecord P} (h : r = t) (e : CellName S r.ty)
        (e' : CellName S t.ty) (he : e.val = e'.val) : r.ChainActive e ↔ t.ChainActive e' := by
      cases h
      cases Subtype.ext he
      rfl
    exact aux hr E E' hEE
  have hframe (W : HonestSource S) (p : W.Node) (hp : 1 ≤ p.1)
      (j : S.I p.2.val.ty) (x : E d) :
      (W.childNode p hp j).2.val.prototypeFrame (W.childNode p hp j).1 x =
        p.2.val.prototypeFrame p.1 (rolePlacement ⟨p.2.val.ty, j⟩ x) := by
    change (p.2.val.child (p.1-1) j).prototypeFrame (p.1-1) x = _
    rw [exists_childMap_step1_frame, Nat.sub_add_cancel hp]
    rfl
  apply exists_childMap_step4_profile_step12_constant_ext hchild
  · intro e e' he
    have hae := hedge e e' he
    by_cases ha : ∃ z ∈ U.recordChains P (U.childNode q hq i) f hf,
        (z.chain.val.cell edgeIndex).val = e.val
    · obtain ⟨E, hE, heE⟩ := exists_childMap_step4_profile_step6_parent_edge P U q hq i
        f F hf hF hsub e ha
      let E' : CellName S q'.2.val.ty := ⟨E.val, hty ▸ E.property⟩
      have hE' := (hactive E E' rfl).mp hE
      have heE' : relint (rolePlacement ⟨q'.2.val.ty, i'⟩ '' e'.val.carrier) ⊆
          relint E'.val.carrier := by simpa only [← hrole, ← he] using heE
      exact (exists_childMap_step4_profile_step17_inherited_value P U q hq i f F hf hF
        hsub hm e E ha hE heE).trans ((hvalues E E' rfl).trans
          (exists_childMap_step4_profile_step17_inherited_value P V q' hq' i' g G hg hG
            hsub' hm' e' E' (hae.mp ha) hE' heE').symm)
    · simp only [HonestSource.constantProfile, if_neg ha, if_neg (fun h => ha (hae.mpr h))]
  · intro v v' hv
    have hp := exists_childMap_step4_profile_step11_vertex v v' hv
    have hae : (∃ z ∈ U.recordChains P (U.childNode q hq i) f hf,
        vertexPoint v ∈ (z.chain.val.cell edgeIndex).val.carrier) ↔
        ∃ z ∈ V.recordChains P (V.childNode q' hq' i') g hg,
          vertexPoint v' ∈ (z.chain.val.cell edgeIndex).val.carrier := by
      rw [hp]
      exact hend _
    by_cases ha : ∃ z ∈ U.recordChains P (U.childNode q hq i) f hf,
        vertexPoint v ∈ (z.chain.val.cell edgeIndex).val.carrier
    · change (if _ then some _ else none) = (if _ then some _ else none)
      rw [if_pos ha, if_pos (hae.mp ha)]
      apply congrArg some
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, Finset.mem_toList, Finset.mem_univ, true_and, decide_eq_true_eq]
      obtain ⟨z, hz, hvz⟩ := ha
      let e := z.chain.val.cell edgeIndex
      have he : (U.recordOf P (U.childNode q hq i) f hf).ChainActive e := ⟨z, hz, rfl⟩
      obtain ⟨E, hE, heE⟩ := exists_childMap_step4_profile_step6_parent_edge P U q hq i
        f F hf hF hsub e he
      let E' : CellName S q'.2.val.ty := ⟨E.val, hty ▸ E.property⟩
      have hE' := (hactive E E' rfl).mp hE
      have hclosed : rolePlacement ⟨q.2.val.ty, i⟩ '' e.val.carrier ⊆ E.val.carrier := by
        have h := closure_mono ((exists_childMap_step4_relint_containment U q hq i e.val E.val).mpr heE)
        rw [exists_childMap_step5_cell_closure, exists_childMap_step5_cell_closure] at h
        exact (exists_childMap_step4_containment U q hq i e.val E.val).mp h
      have hx : rolePlacement ⟨q.2.val.ty, i⟩ (vertexPoint v) ∈ E.val.carrier :=
        hclosed (Set.mem_image_of_mem _ hvz)
      have hx' : rolePlacement ⟨q'.2.val.ty, i'⟩ (vertexPoint v') ∈ E'.val.carrier := by
        simpa only [← hrole, ← hp] using hx
      have hxU : (U.childNode q hq i).2.val.prototypeFrame (U.childNode q hq i).1
          (vertexPoint v) ∈ q.2.val.cell q.1 E.val := by
        rw [hframe]
        exact Set.mem_image_of_mem _ hx
      have hxV : (V.childNode q' hq' i').2.val.prototypeFrame (V.childNode q' hq' i').1
          (vertexPoint v') ∈ q'.2.val.cell q'.1 E'.val := by
        rw [hframe]
        exact Set.mem_image_of_mem _ hx'
      have hsites := (exists_childMap_step4_profile_step9_inherited_sites P U _ _
        (exists_childMap_step2_parent U q hq i) f F hf hF
        ((exists_childMap_step4_containment U q hq i f.val F.val).mpr hsub)).1
      have hsites' := (exists_childMap_step4_profile_step9_inherited_sites P V _ _
        (exists_childMap_step2_parent V q' hq' i') g G hg hG
        ((exists_childMap_step4_containment V q' hq' i' g.val G.val).mpr hsub')).1
      simp only [hsites, hsites']
      rw [exists_childMap_step4_profile_step18_endpoint_lookup P U q F hF hm E hE _ hxU,
        exists_childMap_step4_profile_step18_endpoint_lookup P V q' G hG hm' E' hE' _ hxV]
      simp only [hframe, AffineEquiv.apply_eq_iff_eq]
      constructor
      · rintro ⟨w, hw, hs⟩
        let w' : VertexName S q'.2.val.ty := ⟨w.val, hty ▸ w.property⟩
        have hw' := exists_childMap_step4_profile_step11_vertex w w' rfl
        refine ⟨w', ?_, (hflags w w' rfl).symm.trans hs⟩
        simpa only [← hrole, ← hp, ← hw'] using hw
      · rintro ⟨w', hw, hs⟩
        let w : VertexName S q.2.val.ty := ⟨w'.val, hty.symm ▸ w'.property⟩
        have hw' := exists_childMap_step4_profile_step11_vertex w w' rfl
        refine ⟨w, ?_, (hflags w w' rfl).trans hs⟩
        simpa only [hrole, hp, hw'] using hw
    · simp only [HonestSource.constantProfile, if_neg ha, if_neg (fun h => ha (hae.mpr h))]

end ProfileSteps

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
(S4d): "append i to the role word"; after maturity each active edge
"inherits kappa(e') = kappa(e)", and a new endpoint is "not a site".
This determines the short-word or mature-constant profile, including the
transition at the chosen side's site depth. -/
private theorem exists_childMap_step4_profile :
    HEq (U.recordOf P (U.childNode q hq i) f hf).counter
      (V.recordOf P (V.childNode q' hq' i') g hg).counter := by
  classical
  have hty : q.2.val.ty = q'.2.val.ty := congrArg Sigma.fst hrole
  have hchild : (U.childNode q hq i).2.val.ty = (V.childNode q' hq' i').2.val.ty :=
    congrArg (fun r : S.Role => (S.child r.1 r.2).ty) hrole
  obtain ⟨hi, hs⟩ := exists_childMap_step4_incidence P q q' hq hq' i i' hrole hrecords f g hfg hf hg
  have hc := exists_childMap_step4_chains P q q' hq hq' i i' hrole hrecords f g hfg hf hg
  change U.recordIncidence P (U.childNode q hq i) f hf =
    V.recordIncidence P (V.childNode q' hq' i') g hg at hi
  change U.recordSide P (U.childNode q hq i) f hf =
    V.recordSide P (V.childNode q' hq' i') g hg at hs
  change HEq (U.recordChains P (U.childNode q hq i) f hf)
    (V.recordChains P (V.childNode q' hq' i') g hg) at hc
  change HEq (U.counterProfile P (U.childNode q hq i) f hf)
    (V.counterProfile P (V.childNode q' hq' i') g hg)
  by_cases hint : ∃ F : FacetName S q.2.val.ty,
      rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier
  · obtain ⟨F, hsub⟩ := hint
    let G : FacetName S q'.2.val.ty := ⟨F.val, hty ▸ F.property⟩
    have hsub' : rolePlacement ⟨q'.2.val.ty, i'⟩ '' g.val.carrier ⊆ G.val.carrier := by
      simpa only [← hrole, ← hfg] using hsub
    have hplaced := (exists_childMap_step4_containment U q hq i f.val F.val).mpr hsub
    have hplaced' := (exists_childMap_step4_containment V q' hq' i' g.val G.val).mpr hsub'
    obtain ⟨hF, hiF, hsF⟩ := exists_childMap_step4_inherited_incidence P U _ _
      (exists_childMap_step2_parent U q hq i) f F hf hplaced
    obtain ⟨hG, hiG, hsG⟩ := exists_childMap_step4_inherited_incidence P V _ _
      (exists_childMap_step2_parent V q' hq' i') g G hg hplaced'
    have hr := hrecords F G rfl
    simp only [HonestSource.facetRecordOf, dif_neg hF, dif_neg hG, Option.some.injEq] at hr
    have ha := exists_childMap_step4_profile_step2_depth U _ _
      (exists_childMap_step2_parent U q hq i) f F hf hF hplaced
    have ha' := exists_childMap_step4_profile_step2_depth V _ _
      (exists_childMap_step2_parent V q' hq' i') g G hg hG hplaced'
    obtain ⟨hdepth, hword⟩ | ⟨hm, hm'⟩ :=
      exists_childMap_step4_profile_step15_parent_branch P U V q q' F G hF hG hr
    · apply exists_childMap_step4_profile_step14_word_profile P U V _ _ f g hf hg hchild hfg hi hs hc
      · omega
      · rw [ha, ha', exists_childMap_step4_profile_step1_downRoles,
          exists_childMap_step4_profile_step1_downRoles,
          exists_childMap_step2_parent, exists_childMap_step2_parent,
          exists_childMap_step2_role, exists_childMap_step2_role, hword, hrole]
    · have hmC : ¬ (U.hierarchy.firstProvider (U.childNode q hq i) f hf).1 <
          P.siteDepth (U.recordIncidence P (U.childNode q hq i) f hf)
            (U.recordSide P (U.childNode q hq i) f hf) := by
        rw [ha, hiF, hsF]
        omega
      have hmC' : ¬ (V.hierarchy.firstProvider (V.childNode q' hq' i') g hg).1 <
          P.siteDepth (V.recordIncidence P (V.childNode q' hq' i') g hg)
            (V.recordSide P (V.childNode q' hq' i') g hg) := by
        rw [ha', hiG, hsG]
        omega
      simp only [HonestSource.counterProfile, dif_neg hmC, dif_neg hmC']
      have hconst := exists_childMap_step4_profile_step19_mature_constants P U V q q'
        hq hq' i i' hrole f g hfg hf hg F G hF hG hsub hsub' hr hm hm' hc
      have aux {A B : S.ι} (hAB : A = B) (C : ConstantProfile P A)
          (D : ConstantProfile P B) (hCD : HEq C D) :
          HEq (Sum.inl C : ConstantProfile P A ⊕ ShortProfile P)
            (Sum.inl D : ConstantProfile P B ⊕ ShortProfile P) := by
        cases hAB
        cases eq_of_heq hCD
        rfl
      exact aux hchild _ _ hconst
  · have hint' : ¬ ∃ G : FacetName S q'.2.val.ty,
        rolePlacement ⟨q'.2.val.ty, i'⟩ '' g.val.carrier ⊆ G.val.carrier := by
      rintro ⟨G, hG⟩
      let F : FacetName S q.2.val.ty := ⟨G.val, hty.symm ▸ G.property⟩
      exact hint ⟨F, by simpa only [hrole, hfg] using hG⟩
    obtain ⟨_, _, hage⟩ := exists_childMap_step4_internal_provider U q hq i f hf hint
    obtain ⟨_, _, hage'⟩ := exists_childMap_step4_internal_provider V q' hq' i' g hg hint'
    have hage0 := (U.hierarchy.birthHeight_age_spec (U.childNode q hq i) f hf).2.1
    have hage0' := (V.hierarchy.birthHeight_age_spec (V.childNode q' hq' i') g hg).2.1
    have hz : (U.hierarchy.firstProvider (U.childNode q hq i) f hf).1 = 0 := by omega
    have hz' : (V.hierarchy.firstProvider (V.childNode q' hq' i') g hg).1 = 0 := by omega
    apply exists_childMap_step4_profile_step14_word_profile P U V _ _ f g hf hg hchild hfg hi hs hc
    · omega
    · simp only [hz, hz', HonestSource.downRoles, List.ofFn_zero, List.reverse_nil]

end ChildComparison

/-- Step 5 of the V4 proof of `exists_childMap` (V4 2.3):
"boundary tracks" start in their own node's boundary. -/
private theorem exists_childMap_step5_facet_boundary (U : HonestSource S)
    (q : U.Node) (f : FacetName S q.2.val.ty) :
    q.2.val.cell q.1 f.val ⊆ frontier (q.2.val.carrier q.1) := by
  exact (U.hierarchy.boundaryOffsets_downward q f).1

/-- Step 5 of the V4 proof of `exists_childMap` (V4 2.3):
"the facets ... containing f',f'' are those containing f,tilde f".
An inherited facet has its relative interior in the relative interior of its
unique parent facet; equal facet dimensions exclude lower strata. -/
private theorem exists_childMap_step5_facet_relint (U : HonestSource S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) (F : FacetName S q.2.val.ty)
    (hF : (U.childNode q hq i).2.val.cell (U.childNode q hq i).1 f.val ⊆
      q.2.val.cell q.1 F.val) :
    relint ((U.childNode q hq i).2.val.cell (U.childNode q hq i).1 f.val) ⊆
      relint (q.2.val.cell q.1 F.val) := by
  classical
  have hd : (U.childNode q hq i).2.val.IsDescendant (q.1-1) q.2.val q.1 := by
    convert exists_childMap_step1_descendant q.2.val (q.1-1) i using 1
    exact (Nat.sub_add_cancel hq).symm
  have hbd := hF.trans (exists_childMap_step5_facet_boundary U q F)
  let T := ancestralStratum q.2.val (U.childNode q hq i).2.val q.1 (q.1-1) hd (facetCell f) hbd
  have ht := ancestralStratum_spec q.2.val (U.childNode q hq i).2.val q.1 (q.1-1) hd (facetCell f) hbd
  have hdimf : f.val.dim = d-1 := (Finset.mem_filter.mp f.property).2
  have hdimT : T.val.dim = d-1 := by
    have hle := ht.2
    have hlt := (S.cx q.2.val.ty).dim_lt T.val T.property
    change f.val.dim ≤ T.val.dim at hle
    omega
  let F' : FacetName S q.2.val.ty := ⟨T.val, Finset.mem_filter.mpr ⟨T.property, hdimT⟩⟩
  have hsub : (U.childNode q hq i).2.val.cell (U.childNode q hq i).1 f.val ⊆
      q.2.val.cell q.1 F'.val := by
    have hh := closure_mono ht.1
    simpa only [exists_childMap_step5_cell_closure] using hh
  rcases facet_dichotomy q.2.val (U.childNode q hq i).2.val q.1 (q.1-1) hd f with huniq | hi
  · obtain ⟨G, hG, hu⟩ := huniq
    have heq : F' = F := (hu F' hsub).trans (hu F hF).symm
    have htf : T.val = F.val := congrArg Subtype.val heq
    have htt : relint ((U.childNode q hq i).2.val.cell (U.childNode q hq i).1 f.val) ⊆
        relint (q.2.val.cell q.1 T.val) := ht.1
    rwa [htf] at htt
  · obtain ⟨x, hx⟩ := exists_childMap_step5_cell_nonempty (U.childNode q hq i).2.val (q.1-1) f.val
    exact False.elim ((hbd (intrinsicInterior_subset hx)).2 (hi hx))

/-- Step 5 of the V4 proof of `exists_childMap` (V4 2.3):
"the facets ... containing f',f'' are those containing f,tilde f".
Hereditary trace lifts containment of a child facet in a higher ancestor facet
to containment of its immediate parent facet. -/
private theorem exists_childMap_step5_lift (U : HonestSource S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) (F : FacetName S q.2.val.ty)
    (a : ℕ) (G : FacetName S (U.hierarchy.ancestor q a).2.val.ty)
    (hF : (U.childNode q hq i).2.val.cell (U.childNode q hq i).1 f.val ⊆
      q.2.val.cell q.1 F.val)
    (hG : (U.childNode q hq i).2.val.cell (U.childNode q hq i).1 f.val ⊆
      (U.hierarchy.ancestor q a).2.val.cell (U.hierarchy.ancestor q a).1 G.val) :
    q.2.val.cell q.1 F.val ⊆
      (U.hierarchy.ancestor q a).2.val.cell (U.hierarchy.ancestor q a).1 G.val := by
  obtain ⟨x, hx⟩ := exists_childMap_step5_cell_nonempty (U.childNode q hq i).2.val (q.1-1) f.val
  apply hereditary_trace (U.hierarchy.ancestor q a).2.val q.2.val
    (U.hierarchy.ancestor q a).1 q.1 (U.hierarchy.ancestor_descendant q a) G.val F.val
    (facetCell G).property (facetCell F).property
  exact ⟨x, exists_childMap_step5_facet_relint U q hq i f F hF hx,
    hG (intrinsicInterior_subset hx)⟩

/-- Step 5 of the V4 proof of `exists_childMap` (V4 2.3):
"coalesce ... only if equal" at offset zero. Distinct facet names of one
node cannot contain one another. -/
private theorem exists_childMap_step5_facet_eq (U : HonestSource S) (q : U.Node)
    (f F : FacetName S q.2.val.ty)
    (hF : q.2.val.cell q.1 f.val ⊆ q.2.val.cell q.1 F.val) : f = F := by
  have hd := U.hierarchy.ancestor_descendant q 0
  change q.2.val.IsDescendant q.1 q.2.val q.1 at hd
  rcases facet_dichotomy q.2.val q.2.val q.1 q.1 hd f with huniq | hi
  · obtain ⟨G, _, hu⟩ := huniq
    exact (hu f Subset.rfl).trans (hu F hF).symm
  · obtain ⟨x, hx⟩ := exists_childMap_step5_cell_nonempty q.2.val q.1 f.val
    exact False.elim ((exists_childMap_step5_facet_boundary U q f (intrinsicInterior_subset hx)).2 (hi hx))

/-- Step 5 of the V4 proof of `exists_childMap` (V4 2.3):
"for m>n the facets of B_m ...". Ancestors of the child beyond its first
parent step are exactly the ancestors of that parent. -/
private theorem exists_childMap_step5_ancestor (U : HonestSource S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) (a : ℕ) :
    U.hierarchy.ancestor (U.childNode q hq i) (a+1) = U.hierarchy.ancestor q a := by
  change (U.hierarchy.parentNode^[a+1]) (U.childNode q hq i) = (U.hierarchy.parentNode^[a]) q
  rw [Function.iterate_succ_apply, exists_childMap_step2_parent]

/-- Step 5 of the V4 proof of `exists_childMap` (V4 2.3):
"if f' [is] internal ... the tracks never both lie on the boundary" above
its parent. A track surviving the first step therefore has a parent facet. -/
private theorem exists_childMap_step5_surviving_facet (U : HonestSource S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty)
    (hb : 1 ∈ U.hierarchy.boundaryOffsets (U.childNode q hq i) f) :
    ∃ F : FacetName S q.2.val.ty,
      (U.childNode q hq i).2.val.cell (U.childNode q hq i).1 f.val ⊆ q.2.val.cell q.1 F.val := by
  have hd : (U.childNode q hq i).2.val.IsDescendant (q.1-1) q.2.val q.1 := by
    convert exists_childMap_step1_descendant q.2.val (q.1-1) i using 1
    exact (Nat.sub_add_cancel hq).symm
  rcases facet_dichotomy q.2.val (U.childNode q hq i).2.val q.1 (q.1-1) hd f with hF | hi
  · obtain ⟨F, hF, _⟩ := hF
    exact ⟨F, hF⟩
  · have hparent : U.hierarchy.ancestor (U.childNode q hq i) 1 = q :=
      exists_childMap_step5_ancestor U q hq i 0
    have he := congrArg (fun p : U.Node => frontier (p.2.val.carrier p.1)) hparent
    dsimp only at he
    have hb' : (U.childNode q hq i).2.val.cell (q.1-1) f.val ⊆ frontier (q.2.val.carrier q.1) := by
      rw [← he]
      exact hb
    obtain ⟨x, hx⟩ := exists_childMap_step5_cell_nonempty (U.childNode q hq i).2.val (q.1-1) f.val
    exact False.elim ((hb' (intrinsicInterior_subset hx)).2 (hi hx))

/-- Step 5 of the V4 proof of `exists_childMap` (V4 2.3):
"if both are internal ... iff f'=f''"; mixed pairs are false; inherited pairs
use equality of the parent facet or its E-table. Reflexivity of the parent
E-table includes the equal-parent-facet case in the second disjunct below. -/
private theorem exists_childMap_step5_tracks (U : HonestSource S) (q : U.Node)
    (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f g : FacetName S (U.childNode q hq i).2.val.ty) :
    U.TracksCoalesce (U.childNode q hq i) f g ↔
      f.val = g.val ∨ ∃ F G : FacetName S q.2.val.ty,
        rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier ∧
        rolePlacement ⟨q.2.val.ty, i⟩ '' g.val.carrier ⊆ G.val.carrier ∧
        U.TracksCoalesce q F G := by
  constructor
  · rintro ⟨a, hboundary, K, hfK, hgK⟩
    cases a with
    | zero =>
      have hf : f = K := exists_childMap_step5_facet_eq U (U.childNode q hq i) f K hfK
      have hg : g = K := exists_childMap_step5_facet_eq U (U.childNode q hq i) g K hgK
      exact Or.inl (congrArg Subtype.val (hf.trans hg.symm))
    | succ a =>
      obtain ⟨F, hF⟩ := exists_childMap_step5_surviving_facet U q hq i f (hboundary 1 (by omega)).1
      obtain ⟨G, hG⟩ := exists_childMap_step5_surviving_facet U q hq i g (hboundary 1 (by omega)).2
      have ha := exists_childMap_step5_ancestor U q hq i a
      let K' : FacetName S (U.hierarchy.ancestor q a).2.val.ty :=
        ⟨K.val, (congrArg (fun n : U.Node => n.2.val.ty) ha) ▸ K.property⟩
      have hkcell : (U.hierarchy.ancestor (U.childNode q hq i) (a+1)).2.val.cell
          (U.hierarchy.ancestor (U.childNode q hq i) (a+1)).1 K.val =
          (U.hierarchy.ancestor q a).2.val.cell (U.hierarchy.ancestor q a).1 K'.val :=
        congrArg (fun n : U.Node => n.2.val.cell n.1 K.val) ha
      have hfK' : (U.childNode q hq i).2.val.cell (q.1-1) f.val ⊆
          (U.hierarchy.ancestor q a).2.val.cell (U.hierarchy.ancestor q a).1 K'.val := by
        rw [← hkcell]
        exact hfK
      have hgK' : (U.childNode q hq i).2.val.cell (q.1-1) g.val ⊆
          (U.hierarchy.ancestor q a).2.val.cell (U.hierarchy.ancestor q a).1 K'.val := by
        rw [← hkcell]
        exact hgK
      have hFK := exists_childMap_step5_lift U q hq i f F a K' hF hfK'
      have hGK := exists_childMap_step5_lift U q hq i g G a K' hG hgK'
      have hbF : a ∈ U.hierarchy.boundaryOffsets q F :=
        hFK.trans (exists_childMap_step5_facet_boundary U (U.hierarchy.ancestor q a) K')
      have hbG : a ∈ U.hierarchy.boundaryOffsets q G :=
        hGK.trans (exists_childMap_step5_facet_boundary U (U.hierarchy.ancestor q a) K')
      refine Or.inr ⟨F, G, (exists_childMap_step4_containment U q hq i f.val F.val).mp hF,
        (exists_childMap_step4_containment U q hq i g.val G.val).mp hG, a, ?_, K', hFK, hGK⟩
      intro j hj
      exact ⟨(U.hierarchy.boundaryOffsets_downward q F).2 j a hj hbF,
        (U.hierarchy.boundaryOffsets_downward q G).2 j a hj hbG⟩
  · rintro (heq | ⟨F, G, hF, hG, a, hboundary, K, hFK, hGK⟩)
    · cases Subtype.ext heq
      exact U.tracksCoalesce_refl _ f
    · have hF' := (exists_childMap_step4_containment U q hq i f.val F.val).mpr hF
      have hG' := (exists_childMap_step4_containment U q hq i g.val G.val).mpr hG
      have ha := exists_childMap_step5_ancestor U q hq i a
      let K' : FacetName S (U.hierarchy.ancestor (U.childNode q hq i) (a+1)).2.val.ty :=
        ⟨K.val, (congrArg (fun n : U.Node => n.2.val.ty) ha.symm) ▸ K.property⟩
      have hkcell : (U.hierarchy.ancestor (U.childNode q hq i) (a+1)).2.val.cell
          (U.hierarchy.ancestor (U.childNode q hq i) (a+1)).1 K'.val =
          (U.hierarchy.ancestor q a).2.val.cell (U.hierarchy.ancestor q a).1 K.val :=
        congrArg (fun n : U.Node => n.2.val.cell n.1 K.val) ha
      refine ⟨a+1, ?_, K', ?_, ?_⟩
      · intro j hj
        cases j with
        | zero => exact ⟨(U.hierarchy.boundaryOffsets_downward _ f).1,
            (U.hierarchy.boundaryOffsets_downward _ g).1⟩
        | succ j =>
          have hb := hboundary j (by omega)
          have he := congrArg (fun n : U.Node => frontier (n.2.val.carrier n.1))
            (exists_childMap_step5_ancestor U q hq i j)
          dsimp only at he
          constructor
          · change (U.childNode q hq i).2.val.cell (q.1-1) f.val ⊆ _
            rw [he]
            exact hF'.trans hb.1
          · change (U.childNode q hq i).2.val.cell (q.1-1) g.val ⊆ _
            rw [he]
            exact hG'.trans hb.2
      · rw [hkcell]
        exact hF'.trans hFK
      · rw [hkcell]
        exact hG'.trans hGK

/-- Step 1 of the V4 proof of `exists_childMap_step6_internal_header` (V4 2.3):
"the same cones, re-expressed in C's frame". An affine change of frame sends
the positive-time radial tangent cone by its linear part. -/
private theorem exists_childMap_step6_internal_header_step1_tangent_image
    (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) (x : E d) :
    tangentCone (e '' K) (e x) = e.linear '' tangentCone K x := by
  have hmap (y u : E d) (t : ℝ) : e (y + t • u) = e y + t • e.linear u := by
    simpa only [vadd_eq_add, add_comm, map_smul] using e.map_vadd y (t • u)
  ext u
  constructor
  · rintro ⟨ε, hε, hu⟩
    refine ⟨e.linear.symm u, ⟨ε, hε, ?_⟩, e.linear.apply_symm_apply u⟩
    intro t ht htε
    apply e.injective.mem_set_image.mp
    simpa only [hmap, e.linear.apply_symm_apply] using hu t ht htε
  · rintro ⟨u, ⟨ε, hε, hu⟩, rfl⟩
    refine ⟨ε, hε, ?_⟩
    intro t ht htε
    rw [← hmap]
    exact Set.mem_image_of_mem e (hu t ht htε)

/-- Step 2 of the V4 proof of `exists_childMap_step6_internal_header` (V4 2.3):
"expressed in C's frame". Normalizing a parent-frame direction set by the
full child frame cancels the parent frame, leaving the inverse role map. -/
private theorem exists_childMap_step6_internal_header_step2_normalize_linear
    (e r : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
    (r.trans e).linear.symm '' (e.linear '' K) = r.linear.symm '' K := by
  rw [Set.image_image]
  congr 1
  funext x
  change r.linear.symm (e.linear.symm (e.linear x)) = r.linear.symm x
  rw [e.linear.symm_apply_apply]

/-- Step 3 of the V4 proof of `exists_childMap_step6_internal_header` (V4 2.3):
"the header of the immediate substitution ... (a fixed finite lookup)".
The lookup uses the unexpanded parent prototype and then the inverse role
linear map, including all incident child, boundary, primitive and flag data. -/
private def exists_childMap_step6_internal_header_step3_lookup
    (P : Params S) (r : S.Role) (x : E d) : State.Header P := by
  classical
  let y := rolePlacement r x
  let normalize := fun K : Set (E d) => (rolePlacement r).linear.symm '' K
  let pos := fun a : P.Incidence => rolePlacement ⟨a.val.ty, a.val.left⟩
  exact {
    birthType := r.1
    parentCone := normalize (tangentCone (S.proto r.1).carrier y)
    childCones := fun j =>
      let K := rolePlacement ⟨r.1, j⟩ '' (S.proto (S.child r.1 j).ty).carrier
      if y ∈ K then some (normalize (tangentCone K y)) else none
    boundaryCones := fun F => if y ∈ F.val.carrier then
      some (normalize (tangentCone F.val.carrier y)) else none
    primitiveCones := fun a => if a.val.ty = r.1 ∧
        y ∈ pos a '' a.val.leftFacet.val.carrier then
      some (normalize (tangentCone (pos a '' a.val.leftFacet.val.carrier) y))
      else none
    flagTangent := fun a => if a.val.ty = r.1 ∧
        (y = pos a (P.flag a).initial ∨ y = pos a (P.flag a).terminal) then
      some {
        cones := fun j => normalize
          (tangentCone (pos a '' ((P.flag a).flag.cell j).val.carrier) y)
        initial := decide (y = pos a (P.flag a).initial)
        sides := fun j => normalize ((pos a).linear '' (P.flag a).sides j) }
      else none }

/-- Step 4 of the V4 proof of `exists_childMap_step6_internal_header` (V4 2.3):
"the record is the header of the immediate substitution ... expressed in C's
frame". Once the birth parent is the immediate parent, each geometric header
field equals its fixed prototype lookup. -/
private theorem exists_childMap_step6_internal_header_step4_header_lookup
    (P : Params S) (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1)
    (i : S.I q.2.val.ty) (f : FacetName S (U.childNode q hq i).2.val.ty)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (v : VertexName S (U.childNode q hq i).2.val.ty)
    (hbirth : U.hierarchy.birthParent (U.childNode q hq i) f hf = q) :
    U.headerOf P (U.childNode q hq i) f hf v =
      exists_childMap_step6_internal_header_step3_lookup P ⟨q.2.val.ty, i⟩
        (vertexPoint v) := by
  classical
  have hframe : (U.childNode q hq i).2.val.prototypeFrame (U.childNode q hq i).1 =
      (rolePlacement ⟨q.2.val.ty, i⟩).trans (q.2.val.prototypeFrame q.1) := by
    simpa only [Nat.sub_add_cancel hq] using exists_childMap_step1_frame q.2.val (q.1-1) i
  have hcarrier (N : FramedNode S) (n : ℕ) :
      N.carrier n = N.prototypeFrame n '' (S.proto N.ty).carrier := by
    rw [FramedNode.carrier, placedSet, SubstSystem.supertile, Set.image_image]
    rfl
  have hchild (j : S.I q.2.val.ty) :
      (q.2.val.child (q.1-1) j).carrier (q.1-1) = q.2.val.prototypeFrame q.1 ''
        (rolePlacement ⟨q.2.val.ty, j⟩ '' (S.proto (S.child q.2.val.ty j).ty).carrier) := by
    rw [hcarrier, exists_childMap_step1_frame, Nat.sub_add_cancel hq, Set.image_image]
    rfl
  have hpos (a : P.Incidence) : P.incidencePlacement q.2.val q.1 a =
      (rolePlacement ⟨a.val.ty, a.val.left⟩).trans (q.2.val.prototypeFrame q.1) := rfl
  have hposimage (a : P.Incidence) (K : Set (E d)) :
      P.incidencePlacement q.2.val q.1 a '' K = q.2.val.prototypeFrame q.1 ''
        (rolePlacement ⟨a.val.ty, a.val.left⟩ '' K) := by
    rw [hpos, Set.image_image]
    rfl
  have hpospoint (a : P.Incidence) (x : E d) :
      P.incidencePlacement q.2.val q.1 a x = q.2.val.prototypeFrame q.1
        (rolePlacement ⟨a.val.ty, a.val.left⟩ x) := rfl
  have hposlinear (a : P.Incidence) (K : Set (E d)) :
      (P.incidencePlacement q.2.val q.1 a).linear '' K =
        (q.2.val.prototypeFrame q.1).linear ''
          ((rolePlacement ⟨a.val.ty, a.val.left⟩).linear '' K) := by
    rw [hpos, Set.image_image]
    rfl
  have hnorm (K : Set (E d)) :
      U.normalizeCone (U.childNode q hq i) ((q.2.val.prototypeFrame q.1).linear '' K) =
        (rolePlacement ⟨q.2.val.ty, i⟩).linear.symm '' K := by
    rw [HonestSource.normalizeCone, hframe]
    exact exists_childMap_step6_internal_header_step2_normalize_linear _ _ _
  have hpoint : (U.childNode q hq i).2.val.prototypeFrame (U.childNode q hq i).1
      (vertexPoint v) = q.2.val.prototypeFrame q.1
        (rolePlacement ⟨q.2.val.ty, i⟩ (vertexPoint v)) := by rw [hframe]; rfl
  unfold HonestSource.headerOf
  rw [hbirth]
  simp only [hpoint, hchild, hcarrier q.2.val q.1,
    FramedNode.cell, hposimage, exists_childMap_step6_internal_header_step1_tangent_image,
    hnorm, (q.2.val.prototypeFrame q.1).injective.mem_set_image,
    exists_childMap_step6_internal_header_step3_lookup]
  simp only [hpospoint, hposlinear, (q.2.val.prototypeFrame q.1).injective.eq_iff, hnorm]

/-- Step 5 of the V4 proof of `exists_childMap_step6_internal_header` (V4 2.3):
"tau = id" for an internal facet. A vertex on that facet has a singleton
canonical provider stratum, hence dimension zero. -/
private theorem exists_childMap_step6_internal_header_step5_zero_stratum
    (P : Params S) (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1)
    (i : S.I q.2.val.ty) (f : FacetName S (U.childNode q hq i).2.val.ty)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hint : ¬ ∃ F : FacetName S q.2.val.ty,
      rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (v : VertexName S (U.childNode q hq i).2.val.ty) (hv : v.val.carrier ⊆ f.val.carrier) :
    (U.recordTau P (U.childNode q hq i) f hf ⟨vertexCell v, hv⟩).val.val.dim = 0 := by
  let a := U.recordIncidence P (U.childNode q hq i) f hf
  let e := U.recordTau P (U.childNode q hq i) f hf ⟨vertexCell v, hv⟩
  let t := rolePlacement ⟨a.val.ty, a.val.left⟩
  have he := exists_childMap_step4_internal_tau P U q hq i f hf hint ⟨vertexCell v, hv⟩
  change t '' e.val.val.carrier = rolePlacement ⟨q.2.val.ty, i⟩ '' v.val.carrier at he
  rw [vertexPoint_spec, Set.image_singleton] at he
  have hsingleton : e.val.val.carrier = {t.symm (rolePlacement ⟨q.2.val.ty, i⟩ (vertexPoint v))} := by
    apply t.injective.image_injective
    simpa only [Set.image_singleton, t.apply_symm_apply] using he
  change e.val.val.dim = 0
  rw [← e.val.val.flat.dimension, hsingleton]
  simp [cellDirection, direction_affineSpan]

section HeaderComparison
variable (P : Params S) {U V : HonestSource S}
  (q : U.Node) (q' : V.Node) (hq : 1 ≤ q.1) (hq' : 1 ≤ q'.1)
  (i : S.I q.2.val.ty) (i' : S.I q'.2.val.ty)
  (hrole : (⟨q.2.val.ty, i⟩ : S.Role) = ⟨q'.2.val.ty, i'⟩)
  (v : VertexName S (U.childNode q hq i).2.val.ty)
  (v' : VertexName S (V.childNode q' hq' i').2.val.ty) (hvv' : v.val = v'.val)
  (f : FacetName S (U.childNode q hq i).2.val.ty)
  (g : FacetName S (V.childNode q' hq' i').2.val.ty) (hfg : f.val = g.val)

include hrole hvv' hfg

/-- Step 6 of the V4 proof of `exists_childMap` (V4 2.3):
"if f' is internal, the record is the header of the immediate substitution ...
(a fixed finite lookup) ... expressed in C's frame". A facet contained in no
parent facet is internal by Corollary 1.3. This lookup also determines absence
when the vertex is not a provider-zero pair. -/
private theorem exists_childMap_step6_internal_header
    (hint : ¬ ∃ F : FacetName S q.2.val.ty,
      rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier) :
    U.headerRecordOf P (U.childNode q hq i) v f =
      V.headerRecordOf P (V.childNode q' hq' i') v' g := by
  classical
  have hty : q.2.val.ty = q'.2.val.ty := congrArg Sigma.fst hrole
  have hint' : ¬ ∃ G : FacetName S q'.2.val.ty,
      rolePlacement ⟨q'.2.val.ty, i'⟩ '' g.val.carrier ⊆ G.val.carrier := by
    rintro ⟨G, hG⟩
    let F : FacetName S q.2.val.ty := ⟨G.val, hty.symm ▸ G.property⟩
    exact hint ⟨F, by simpa only [hrole, hfg] using hG⟩
  by_cases hv : v.val.carrier ⊆ f.val.carrier
  · have hv' : v'.val.carrier ⊆ g.val.carrier := by
      simpa only [← hvv', ← hfg] using hv
    have hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f := by
      intro h
      obtain ⟨F, hF, _⟩ := (exists_childMap_step4_fault U q hq i f).mp h
      exact hint ⟨F, hF⟩
    have hg : ¬ V.hierarchy.IsFault (V.childNode q' hq' i') g := by
      intro h
      obtain ⟨G, hG, _⟩ := (exists_childMap_step4_fault V q' hq' i' g).mp h
      exact hint' ⟨G, hG⟩
    have hz := exists_childMap_step6_internal_header_step5_zero_stratum P U q hq i f hf hint v hv
    have hz' := exists_childMap_step6_internal_header_step5_zero_stratum P V q' hq' i' g hg hint' v' hv'
    have hb := (exists_childMap_step4_internal_provider U q hq i f hf hint).2.1
    have hb' := (exists_childMap_step4_internal_provider V q' hq' i' g hg hint').2.1
    have hp : vertexPoint v = vertexPoint v' := by
      apply Set.singleton_injective
      exact (vertexPoint_spec v).symm.trans
        ((congrArg Cell.carrier hvv').trans (vertexPoint_spec v'))
    simp only [HonestSource.headerRecordOf, dif_pos hv, dif_pos hv', dif_neg hf,
      dif_neg hg, if_pos hz, if_pos hz', Option.some.injEq]
    rw [exists_childMap_step6_internal_header_step4_header_lookup P U q hq i f hf v hb,
      exists_childMap_step6_internal_header_step4_header_lookup P V q' hq' i' g hg v' hb']
    exact congrArg₂ (exists_childMap_step6_internal_header_step3_lookup P) hrole hp
  · have hv' : ¬ v'.val.carrier ⊆ g.val.carrier := by
      simpa only [← hvv', ← hfg] using hv
    simp only [HonestSource.headerRecordOf, dif_neg hv, dif_neg hv']

section InheritedHeaderGeometry

omit hrole hvv' hfg

/-- Step 1 of the V4 proof of `exists_childMap_step6_inherited_header` (V4 2.3):
"then ... has dimension 0". Full affine frames preserve cell dimension. -/
private theorem exists_childMap_step6_inherited_header_step1_dimension
    (T : E d ≃ᵃ[ℝ] E d) (e : Cell d) :
    Module.finrank ℝ (cellDirection (T '' e.carrier)) = e.dim := by
  change Module.finrank ℝ (affineSpan ℝ (T.toAffineMap '' e.carrier)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  exact (T.linear.finrank_map_eq (cellDirection e.carrier)).trans e.flat.dimension

/-- Step 1 of the V4 proof of `exists_childMap_step6_inherited_header` (V4 2.3):
"so dim t = 0 (Lemma 1.7(b))". The dimension bound also holds for the
canonical provider-side names used by the recorded stratum map. -/
private theorem exists_childMap_step6_inherited_header_step1_tau_dimension
    (P : Params S) (U : HonestSource S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (e : CellsInFacet q.2.val.ty f) :
    e.val.val.dim ≤ (U.recordTau P q f hf e).val.val.dim := by
  have h := (Classical.choose_spec (U.recordTau_exists P q f hf e)).1
  have hd := congrArg (fun K => Module.finrank ℝ (cellDirection K)) h
  change Module.finrank ℝ
      (cellDirection (U.providerPlacement P q f hf ''
        (U.recordTau P q f hf e).val.val.carrier)) =
    Module.finrank ℝ (cellDirection
      ((U.hierarchy.servingChild q f hf).2.val.prototypeFrame
        (U.hierarchy.servingChild q f hf).1 ''
        (U.hierarchy.stratumMap q f hf e.val (U.cellInFacet_placed q f e)).val.carrier)) at hd
  rw [exists_childMap_step6_inherited_header_step1_dimension,
    exists_childMap_step6_inherited_header_step1_dimension] at hd
  exact (U.hierarchy.stratumMap_spec q f hf e.val
    (U.cellInFacet_placed q f e)).2.1.trans_eq hd.symm

/-- Step 2 of the V4 proof of `exists_childMap_step6_inherited_header` (V4 2.3):
"if f' ... is inherited". Its provider is finite exactly when the parent
facet's provider is finite. -/
private theorem exists_childMap_step6_inherited_header_step2_fault
    (U : HonestSource S) (c p : U.Node) (hp : U.hierarchy.parentNode c = p)
    (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
    (hsub : c.2.val.cell c.1 f.val ⊆ p.2.val.cell p.1 F.val) :
    U.hierarchy.IsFault c f ↔ U.hierarchy.IsFault p F := by
  subst p
  constructor
  · intro hf
    by_contra hF
    exact (U.hierarchy.restriction_det_inherited c F f hF hsub).choose hf
  · intro hF
    exact U.hierarchy.restriction_det_fault c F f hF hsub

/-- Step 2 of the V4 proof of `exists_childMap_step6_inherited_header` (V4 2.3):
"v' is a vertex v of B ... and the record of (v,f) in S(B) exists".
A present inherited child header has a parent-vertex name at the same point. -/
private theorem exists_childMap_step6_inherited_header_step2_vertex
    (P : Params S) (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1)
    (i : S.I q.2.val.ty) (v : VertexName S (U.childNode q hq i).2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) (F : FacetName S q.2.val.ty)
    (hsub : rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (hh : U.headerRecordOf P (U.childNode q hq i) v f ≠ none) :
    ∃ w : VertexName S q.2.val.ty,
      rolePlacement ⟨q.2.val.ty, i⟩ '' v.val.carrier = w.val.carrier := by
  classical
  unfold HonestSource.headerRecordOf at hh
  split at hh
  next hv =>
    split at hh
    next hf => exact False.elim (hh rfl)
    next hf =>
      split at hh
      next hzero =>
        have hsub' := (exists_childMap_step4_containment U q hq i f.val F.val).mpr hsub
        have hF := mt (exists_childMap_step6_inherited_header_step2_fault U _ _
          (exists_childMap_step2_parent U q hq i) f F hsub').mpr hf
        obtain ⟨t, hrel, htau⟩ := exists_childMap_step4_inherited_tau P U _ _
          (exists_childMap_step2_parent U q hq i) f F hf hF hsub' ⟨vertexCell v, hv⟩
        have hdim := exists_childMap_step6_inherited_header_step1_tau_dimension P U q F hF t
        have htzero : t.val.val.dim = 0 := by
          rw [← htau, hzero] at hdim
          exact Nat.eq_zero_of_le_zero hdim
        let w : VertexName S q.2.val.ty :=
          ⟨t.val.val, Finset.mem_filter.mpr ⟨t.val.property, htzero⟩⟩
        refine ⟨w, ?_⟩
        have hrel' := (exists_childMap_step4_relint_containment U q hq i
          v.val t.val.val).mp hrel
        change relint (rolePlacement ⟨q.2.val.ty, i⟩ '' v.val.carrier) ⊆
          relint w.val.carrier at hrel'
        simpa only [vertexPoint_spec, Set.image_singleton, relint,
          intrinsicInterior_singleton, Set.singleton_subset_iff,
          Set.mem_singleton_iff, Set.singleton_eq_singleton_iff] using hrel'
      next hzero => exact False.elim (hh rfl)
  next hv => exact False.elim (hh rfl)

/-- Step 2 of the V4 proof of `exists_childMap_step6_inherited_header` (V4 2.3):
"tau_f(t) = tau_f'({v'})". When the child vertex names a parent vertex,
uniqueness of the parent cell identifies their recorded provider strata. -/
private theorem exists_childMap_step6_inherited_header_step2_tau
    (P : Params S) (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1)
    (i : S.I q.2.val.ty) (v : VertexName S (U.childNode q hq i).2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) (F : FacetName S q.2.val.ty)
    (hsub : rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (w : VertexName S q.2.val.ty)
    (hw : rolePlacement ⟨q.2.val.ty, i⟩ '' v.val.carrier = w.val.carrier)
    (hv : v.val.carrier ⊆ f.val.carrier) (hwF : w.val.carrier ⊆ F.val.carrier)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hF : ¬ U.hierarchy.IsFault q F) :
    (U.recordTau P (U.childNode q hq i) f hf ⟨vertexCell v, hv⟩).val.val =
      (U.recordTau P q F hF ⟨vertexCell w, hwF⟩).val.val := by
  obtain ⟨t, hrel, htau⟩ := exists_childMap_step4_inherited_tau P U _ _
    (exists_childMap_step2_parent U q hq i) f F hf hF
    ((exists_childMap_step4_containment U q hq i f.val F.val).mpr hsub)
    ⟨vertexCell v, hv⟩
  have hrel' := (exists_childMap_step4_relint_containment U q hq i
    v.val t.val.val).mp hrel
  rw [hw] at hrel'
  have he : t.val.val = w.val := by
    by_contra hne
    have hd := (S.cx q.2.val.ty).relint_disjoint _ t.val.property _
      (vertexCell w).property hne
    obtain ⟨x, hx⟩ := w.val.flat.relint_nonempty
    exact Set.disjoint_left.mp hd (hrel' hx) hx
  have ht : t = ⟨vertexCell w, hwF⟩ := Subtype.ext (Subtype.ext he)
  simpa only [ht] using htau

/-- Step 3 of the V4 proof of `exists_childMap_step6_inherited_header` (V4 2.3):
"the same cones, re-expressed in C's frame". Apply a linear change of frame
to every cone, retaining every presence test and the endpoint orientation. -/
private def exists_childMap_step6_inherited_header_step3_reframe
    {P : Params S} (L : E d ≃ₗ[ℝ] E d) (H : State.Header P) : State.Header P where
  birthType := H.birthType
  parentCone := L '' H.parentCone
  childCones := fun i => (H.childCones i).map (fun K => L '' K)
  boundaryCones := fun F => (H.boundaryCones F).map (fun K => L '' K)
  primitiveCones := fun a => (H.primitiveCones a).map (fun K => L '' K)
  flagTangent := fun a => (H.flagTangent a).map (fun T => {
    cones := fun j => L '' T.cones j
    initial := T.initial
    sides := fun j => L '' T.sides j })

/-- Step 3 of the V4 proof of `exists_childMap_step6_inherited_header` (V4 2.3):
"a vector u in B's frame becomes R_i^-1 sigma u in C's frame".
Inverse full linear frames compose with the inverse normalized role placement. -/
private theorem exists_childMap_step6_inherited_header_step3_cone
    (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (K : Set (E d)) :
    U.normalizeCone (U.childNode q hq i) K =
      (rolePlacement ⟨q.2.val.ty, i⟩).linear.symm '' U.normalizeCone q K := by
  have hframe : (U.childNode q hq i).2.val.prototypeFrame (U.childNode q hq i).1 =
      (rolePlacement ⟨q.2.val.ty, i⟩).trans (q.2.val.prototypeFrame q.1) := by
    simpa only [Nat.sub_add_cancel hq] using exists_childMap_step1_frame q.2.val (q.1-1) i
  unfold HonestSource.normalizeCone
  rw [hframe, Set.image_image]
  rfl

/-- Step 3 of the V4 proof of `exists_childMap_step6_inherited_header` (V4 2.3):
"the record of (v',f') is ... (record of (v,f))". With the same birth parent
and apex, the literal geometric header changes only its normalizing frame. -/
private theorem exists_childMap_step6_inherited_header_step3_header
    (P : Params S) (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1)
    (i : S.I q.2.val.ty) (v : VertexName S (U.childNode q hq i).2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) (F : FacetName S q.2.val.ty)
    (w : VertexName S q.2.val.ty)
    (hw : rolePlacement ⟨q.2.val.ty, i⟩ '' v.val.carrier = w.val.carrier)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hb : U.hierarchy.birthParent (U.childNode q hq i) f hf =
      U.hierarchy.birthParent q F hF) :
    U.headerOf P (U.childNode q hq i) f hf v =
      exists_childMap_step6_inherited_header_step3_reframe
        (rolePlacement ⟨q.2.val.ty, i⟩).linear.symm (U.headerOf P q F hF w) := by
  have hp : rolePlacement ⟨q.2.val.ty, i⟩ (vertexPoint v) = vertexPoint w := by
    simpa only [vertexPoint_spec, Set.image_singleton, Set.singleton_eq_singleton_iff] using hw
  have hframe : (U.childNode q hq i).2.val.prototypeFrame (U.childNode q hq i).1 =
      (rolePlacement ⟨q.2.val.ty, i⟩).trans (q.2.val.prototypeFrame q.1) := by
    simpa only [Nat.sub_add_cancel hq] using exists_childMap_step1_frame q.2.val (q.1-1) i
  have hx : (U.childNode q hq i).2.val.prototypeFrame (U.childNode q hq i).1 (vertexPoint v) =
      q.2.val.prototypeFrame q.1 (vertexPoint w) := by
    rw [hframe]
    exact congrArg (q.2.val.prototypeFrame q.1) hp
  unfold HonestSource.headerOf
  rw [hb, hx]
  unfold exists_childMap_step6_inherited_header_step3_reframe
  simp only [exists_childMap_step6_inherited_header_step3_cone,
    apply_ite, Option.map_some, Option.map_none]

/-- Step 4 of the V4 proof of `exists_childMap_step6_inherited_header` (V4 2.3):
"the record of (v,f) in S(B) exists; the record of (v',f') is ...".
At a shared vertex, the inherited header entry is the parent entry with all
cones re-expressed in the child frame, including the absent-entry cases. -/
private theorem exists_childMap_step6_inherited_header_step4_record
    (P : Params S) (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1)
    (i : S.I q.2.val.ty) (v : VertexName S (U.childNode q hq i).2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) (F : FacetName S q.2.val.ty)
    (hsub : rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (w : VertexName S q.2.val.ty)
    (hw : rolePlacement ⟨q.2.val.ty, i⟩ '' v.val.carrier = w.val.carrier)
    (hv : v.val.carrier ⊆ f.val.carrier) :
    U.headerRecordOf P (U.childNode q hq i) v f =
      (U.headerRecordOf P q w F).map
        (exists_childMap_step6_inherited_header_step3_reframe
          (rolePlacement ⟨q.2.val.ty, i⟩).linear.symm) := by
  classical
  have hwF : w.val.carrier ⊆ F.val.carrier := by
    rw [← hw]
    exact (Set.image_mono hv).trans hsub
  have hsub' := (exists_childMap_step4_containment U q hq i f.val F.val).mpr hsub
  have hfault := exists_childMap_step6_inherited_header_step2_fault U _ _
    (exists_childMap_step2_parent U q hq i) f F hsub'
  by_cases hF : U.hierarchy.IsFault q F
  · simp only [HonestSource.headerRecordOf, dif_pos hv, dif_pos hwF,
      dif_pos hF, dif_pos (hfault.mpr hF), Option.map_none]
  · have hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f := mt hfault.mp hF
    have hp : U.hierarchy.ancestor (U.childNode q hq i) 1 = q := by
      simpa only [CoherentHierarchy.ancestor, Function.iterate_one] using
        exists_childMap_step2_parent U q hq i
    obtain ⟨_, _, hb⟩ := U.hierarchy.provider_inherited q (U.childNode q hq i) 1 hp F f hF hsub'
    have htau := exists_childMap_step6_inherited_header_step2_tau P U q hq i v f F
      hsub w hw hv hwF hf hF
    simp only [HonestSource.headerRecordOf, dif_pos hv, dif_pos hwF, dif_neg hf,
      dif_neg hF, htau]
    by_cases hz : (U.recordTau P q F hF ⟨vertexCell w, hwF⟩).val.val.dim = 0
    · simp only [if_pos hz, Option.map_some]
      exact congrArg some
        (exists_childMap_step6_inherited_header_step3_header P U q hq i v f F w hw hf hF hb)
    · simp only [if_neg hz, Option.map_none]

end InheritedHeaderGeometry

/-- Step 6 of the V4 proof of `exists_childMap` (V4 2.3):
"if f' ... is inherited ... v' is a vertex v of B" and its record is
"the same cones, re-expressed in C's frame". Thus the parent header table on
the inherited facet determines both presence and every cone of the child
header; a child vertex with no parent-vertex name has no such header. -/
private theorem exists_childMap_step6_inherited_header
    (F : FacetName S q.2.val.ty) (G : FacetName S q'.2.val.ty) (hFG : F.val = G.val)
    (hsub : rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (hheaders : ∀ (w : VertexName S q.2.val.ty) (w' : VertexName S q'.2.val.ty),
      w.val = w'.val → U.headerRecordOf P q w F = V.headerRecordOf P q' w' G) :
    U.headerRecordOf P (U.childNode q hq i) v f =
      V.headerRecordOf P (V.childNode q' hq' i') v' g := by
  classical
  have hty : q.2.val.ty = q'.2.val.ty := congrArg Sigma.fst hrole
  have hsub' : rolePlacement ⟨q'.2.val.ty, i'⟩ '' g.val.carrier ⊆ G.val.carrier := by
    simpa only [← hrole, ← hfg, ← hFG] using hsub
  by_cases hv : v.val.carrier ⊆ f.val.carrier
  · have hv' : v'.val.carrier ⊆ g.val.carrier := by
      simpa only [← hvv', ← hfg] using hv
    by_cases hw : ∃ w : VertexName S q.2.val.ty,
        rolePlacement ⟨q.2.val.ty, i⟩ '' v.val.carrier = w.val.carrier
    · obtain ⟨w, hw⟩ := hw
      let w' : VertexName S q'.2.val.ty := ⟨w.val, hty ▸ w.property⟩
      have hw' : rolePlacement ⟨q'.2.val.ty, i'⟩ '' v'.val.carrier = w'.val.carrier := by
        simpa only [← hrole, ← hvv'] using hw
      rw [exists_childMap_step6_inherited_header_step4_record P U q hq i v f F hsub w hw hv,
        exists_childMap_step6_inherited_header_step4_record P V q' hq' i' v' g G hsub' w' hw' hv',
        hrole, hheaders w w' rfl]
    · have hnone : U.headerRecordOf P (U.childNode q hq i) v f = none := by
        by_contra hh
        exact hw (exists_childMap_step6_inherited_header_step2_vertex P U q hq i v f F hsub hh)
      have hnone' : V.headerRecordOf P (V.childNode q' hq' i') v' g = none := by
        by_contra hh
        obtain ⟨w', hw'⟩ := exists_childMap_step6_inherited_header_step2_vertex
          P V q' hq' i' v' g G hsub' hh
        let w : VertexName S q.2.val.ty := ⟨w'.val, hty.symm ▸ w'.property⟩
        apply hw
        refine ⟨w, ?_⟩
        simpa only [hrole, hvv'] using hw'
      exact hnone.trans hnone'.symm
  · have hv' : ¬ v'.val.carrier ⊆ g.val.carrier := by
      simpa only [← hvv', ← hfg] using hv
    simp only [HonestSource.headerRecordOf, dif_neg hv, dif_neg hv']

end HeaderComparison

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
"All these are finite computations". The incidence-side equality determines
the redundant serving role, and equality of the remaining data determines a record. -/
private theorem exists_childMap_step4_record_ext {P : Params S} {r t : FacetRecord P}
    (ht : r.ty = t.ty) (hf : r.facet.val = t.facet.val)
    (hi : r.incidence = t.incidence) (hs : r.sideIndex = t.sideIndex)
    (ha : r.age = t.age) (hb : r.beta = t.beta) (hτ : HEq r.tau t.tau)
    (hc : HEq r.chains t.chains) (hp : HEq r.counter t.counter) : r = t := by
  rcases r with ⟨A, f, ι, s, side, hside, age, beta, tau, chains, counter⟩
  rcases t with ⟨A', f', ι', s', side', hside', age', beta', tau', chains', counter'⟩
  cases ht
  cases Subtype.ext hf
  cases hi
  cases hs
  cases ha
  cases hb
  cases hτ
  cases hc
  cases hp
  simp_all

/-- Step 7 of the V4 proof of `exists_childMap` (V4 2.3):
"We describe S(C) from S(B) and i." Equal parent states have equal facet
entries at identical named facets, even before their type indices are identified. -/
private theorem exists_childMap_step7_parent_record {P : Params S} {s t : State P}
    (h : s = t) (f : FacetName S s.ty) (g : FacetName S t.ty) (hfg : f.val = g.val) :
    s.facetRecord f = t.facetRecord g := by
  cases h
  cases Subtype.ext hfg
  rfl

/-- Step 7 of the V4 proof of `exists_childMap` (V4 2.3):
"This matches Definition (S5)." Equal states have identical coalescence entries. -/
private theorem exists_childMap_step7_parent_tracks {P : Params S} {s t : State P}
    (h : s = t) (f g : FacetName S s.ty) (f' g' : FacetName S t.ty)
    (hf : f.val = f'.val) (hg : g.val = g'.val) : s.E f g ↔ t.E f' g' := by
  cases h
  cases Subtype.ext hf
  cases Subtype.ext hg
  rfl

/-- Step 7 of the V4 proof of `exists_childMap` (V4 2.3):
"the record of (v,f) in S(B) exists". Equal states have equal header entries
at identical named vertices and facets, including absent entries. -/
private theorem exists_childMap_step7_parent_header {P : Params S} {s t : State P}
    (h : s = t) (v : VertexName S s.ty) (v' : VertexName S t.ty)
    (f : FacetName S s.ty) (f' : FacetName S t.ty)
    (hv : v.val = v'.val) (hf : f.val = f'.val) : s.header v f = t.header v' f' := by
  cases h
  cases Subtype.ext hv
  cases Subtype.ext hf
  rfl

/-- Step 7 of the V4 proof of `exists_childMap` (V4 2.3):
"All these are finite computations from S(B) and i." Assemble the six field
computations to prove independence of a positive-height parent realisation. -/
private theorem exists_childMap_step7_determinacy (P : Params S)
    {U V : HonestSource S} (q : U.Node) (q' : V.Node) (hq : 1 ≤ q.1) (hq' : 1 ≤ q'.1)
    (i : S.I q.2.val.ty) (i' : S.I q'.2.val.ty)
    (hstate : stateOf U P q = stateOf V P q')
    (hrole : (⟨q.2.val.ty, i⟩ : S.Role) = ⟨q'.2.val.ty, i'⟩) :
    stateOf U P (U.childNode q hq i) = stateOf V P (V.childNode q' hq' i') := by
  classical
  have hty : q.2.val.ty = q'.2.val.ty := congrArg Sigma.fst hrole
  have hchild : (U.childNode q hq i).2.val.ty = (V.childNode q' hq' i').2.val.ty :=
    congrArg (fun r : S.Role => (S.child r.1 r.2).ty) hrole
  have hrecords := exists_childMap_step7_parent_record hstate
  have hresidue : q.1 % P.L = q'.1 % P.L := congrArg (fun s : State P => s.residue.val) hstate
  have hfacets (f : FacetName S (U.childNode q hq i).2.val.ty)
      (g : FacetName S (V.childNode q' hq' i').2.val.ty) (hfg : f.val = g.val) :
      U.facetRecordOf P (U.childNode q hq i) f = V.facetRecordOf P (V.childNode q' hq' i') g := by
    have hfault := exists_childMap_step4_fault_eq P q q' hq hq' i i' hrole hrecords f g hfg
    by_cases hf : U.hierarchy.IsFault (U.childNode q hq i) f
    · rw [(exists_childMap_step4_null U P _ f).mpr hf,
        (exists_childMap_step4_null V P _ g).mpr (hfault.mp hf)]
    · have hg := mt hfault.mpr hf
      simp only [HonestSource.facetRecordOf, dif_neg hf, dif_neg hg]
      apply congrArg some
      have hinc := exists_childMap_step4_incidence P q q' hq hq' i i' hrole hrecords f g hfg hf hg
      have hnum := exists_childMap_step4_age_residue P q q' hq hq' i i' hrole hrecords f g hfg hf hg hresidue
      exact exists_childMap_step4_record_ext hchild hfg hinc.1 hinc.2 hnum.1 hnum.2
        (exists_childMap_step4_strata P q q' hq hq' i i' hrole hrecords f g hfg hf hg)
        (exists_childMap_step4_chains P q q' hq hq' i i' hrole hrecords f g hfg hf hg)
        (exists_childMap_step4_profile P q q' hq hq' i i' hrole hrecords f g hfg hf hg)
  have htracks (f g : FacetName S (U.childNode q hq i).2.val.ty)
      (f' g' : FacetName S (V.childNode q' hq' i').2.val.ty)
      (hf : f.val = f'.val) (hg : g.val = g'.val) :
      U.TracksCoalesce (U.childNode q hq i) f g ↔ V.TracksCoalesce (V.childNode q' hq' i') f' g' := by
    rw [exists_childMap_step5_tracks, exists_childMap_step5_tracks]
    apply or_congr (by rw [hf, hg])
    constructor
    · rintro ⟨F, G, hF, hG, hE⟩
      let F' : FacetName S q'.2.val.ty := ⟨F.val, hty ▸ F.property⟩
      let G' : FacetName S q'.2.val.ty := ⟨G.val, hty ▸ G.property⟩
      refine ⟨F', G', ?_, ?_, ?_⟩
      · simpa only [← hrole, ← hf] using hF
      · simpa only [← hrole, ← hg] using hG
      · exact (V.mem_coalescenceTable q' F' G').mp
          ((exists_childMap_step7_parent_tracks hstate F G F' G' rfl rfl).mp
            ((U.mem_coalescenceTable q F G).mpr hE))
    · rintro ⟨F', G', hF, hG, hE⟩
      let F : FacetName S q.2.val.ty := ⟨F'.val, hty.symm ▸ F'.property⟩
      let G : FacetName S q.2.val.ty := ⟨G'.val, hty.symm ▸ G'.property⟩
      refine ⟨F, G, ?_, ?_, ?_⟩
      · simpa only [hrole, hf] using hF
      · simpa only [hrole, hg] using hG
      · exact (U.mem_coalescenceTable q F G).mp
          ((exists_childMap_step7_parent_tracks hstate F G F' G' rfl rfl).mpr
            ((V.mem_coalescenceTable q' F' G').mpr hE))
  have hheaders (v : VertexName S (U.childNode q hq i).2.val.ty)
      (v' : VertexName S (V.childNode q' hq' i').2.val.ty)
      (f : FacetName S (U.childNode q hq i).2.val.ty)
      (g : FacetName S (V.childNode q' hq' i').2.val.ty) (hv : v.val = v'.val) (hf : f.val = g.val) :
      U.headerRecordOf P (U.childNode q hq i) v f = V.headerRecordOf P (V.childNode q' hq' i') v' g := by
    by_cases hint : ∃ F : FacetName S q.2.val.ty,
        rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier
    · obtain ⟨F, hF⟩ := hint
      let G : FacetName S q'.2.val.ty := ⟨F.val, hty ▸ F.property⟩
      exact exists_childMap_step6_inherited_header P q q' hq hq' i i' hrole v v' hv f g hf F G rfl hF
        (fun w w' hw => exists_childMap_step7_parent_header hstate w w' F G hw rfl)
    · exact exists_childMap_step6_internal_header P q q' hq hq' i i' hrole v v' hv f g hf hint
  apply exists_childMap_step7_state_ext hchild
  · funext j
    rw [exists_childMap_step2_address, exists_childMap_step2_address]
    split
    · exact hrole
    · exact congrFun (congrArg State.address hstate) _
  · apply Fin.ext
    exact exists_childMap_step3_residue P hq hq' hresidue
  · have aux {A B : S.ι} (ht : A = B)
        (F : FacetName S A → Option (FacetRecord P)) (G : FacetName S B → Option (FacetRecord P))
        (h : ∀ f g, f.val = g.val → F f = G g) : HEq F G := by
      subst B
      exact heq_of_eq (funext (fun f => h f f rfl))
    exact aux hchild _ _ hfacets
  · have aux {A B : S.ι} (ht : A = B)
        (F : FacetName S A → FacetName S A → Prop) (G : FacetName S B → FacetName S B → Prop)
        (h : ∀ f g f' g', f.val = f'.val → g.val = g'.val → (F f g ↔ G f' g')) : HEq F G := by
      subst B
      exact heq_of_eq (funext (fun f => funext (fun g => propext (h f g f g rfl rfl))))
    apply aux hchild
    intro f g f' g' hf hg
    exact (U.mem_coalescenceTable _ f g).trans ((htracks f g f' g' hf hg).trans
      (V.mem_coalescenceTable _ f' g').symm)
  · have aux {A B : S.ι} (ht : A = B)
        (F : VertexName S A → FacetName S A → Option (State.Header P))
        (G : VertexName S B → FacetName S B → Option (State.Header P))
        (h : ∀ v v' f f', v.val = v'.val → f.val = f'.val → F v f = G v' f') : HEq F G := by
      subst B
      exact heq_of_eq (funext (fun v => funext (fun f => h v v f f rfl rfl)))
    exact aux hchild _ _ hheaders

/-- Step 8 of the V4 proof of `exists_childMap` (V4 1.13, 2.3):
"if that node has height 0, first raise it". For an admissible input with no
positive-height realisation selected, closure needs only an honest state of the
prescribed child type. Inflation supplies a positive-height node of the same
type, without requiring the later full-state scale-transfer theorem. -/
private theorem exists_childMap_step8_child_type (P : Params S) (s : State P)
    (hs : s ∈ honestStates S P) (r : S.Role) (hr : r.1 = s.ty) :
    ∃ t ∈ honestStates S P, t.ty = (S.child r.1 r.2).ty := by
  obtain ⟨U, q, rfl⟩ := hs
  obtain ⟨V, ⟨e⟩⟩ := inflate U
  let q' := e.toEquiv ⟨q, Nat.zero_le _⟩
  have hty : q'.val.2.val.ty = r.1 := (e.types _).trans hr.symm
  let i : S.I q'.val.2.val.ty := hty.symm ▸ r.2
  have hrole : (⟨q'.val.2.val.ty, i⟩ : S.Role) = r :=
    Sigma.ext hty (eqRec_heq hty.symm r.2)
  refine ⟨stateOf V P (V.childNode q'.val q'.property i), stateOf_mem V P _, ?_⟩
  exact congrArg (fun r : S.Role => (S.child r.1 r.2).ty) hrole

/-- Q6, V4 2.3: deterministic descent, totalized on raw states and invalid roles.
Only admissible pairs are constrained. Honest ground states are first raised by
`L` using exact scale transfer, so every admissible pair has an honest child witness. -/
theorem exists_childMap (S : SubstSystem d) (P : Params S) :
    ∃ D : State P → S.Role → State P,
      (∀ s ∈ honestStates S P, ∀ r : S.Role, r.1 = s.ty →
        D s r ∈ honestStates S P ∧ (D s r).ty = (S.child r.1 r.2).ty) ∧
      ∀ (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty),
        stateOf U P (U.childNode q hq i) = D (stateOf U P q) ⟨q.2.val.ty, i⟩ := by
  classical
  let R (s : State P) (r : S.Role) (t : State P) : Prop :=
    ∃ (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty),
      stateOf U P q = s ∧ (⟨q.2.val.ty, i⟩ : S.Role) = r ∧
        stateOf U P (U.childNode q hq i) = t
  have hsingle (s : State P) (r : S.Role) (t t' : State P)
      (ht : R s r t) (ht' : R s r t') : t = t' := by
    obtain ⟨U, q, hq, i, hs, hr, hc⟩ := ht
    obtain ⟨V, q', hq', i', hs', hr', hc'⟩ := ht'
    exact hc.symm.trans ((exists_childMap_step7_determinacy P q q' hq hq' i i'
      (hs.trans hs'.symm) (hr.trans hr'.symm)).trans hc')
  let D (s : State P) (r : S.Role) : State P :=
    if h : ∃ t, R s r t then Classical.choose h
    else if ha : s ∈ honestStates S P ∧ r.1 = s.ty then
      Classical.choose (exists_childMap_step8_child_type P s ha.1 r ha.2)
    else s
  refine ⟨D, ?_, ?_⟩
  · intro s hs r hr
    by_cases h : ∃ t, R s r t
    · dsimp only [D]
      rw [dif_pos h]
      obtain ⟨U, q, hq, i, _, hrole, hc⟩ := Classical.choose_spec h
      rw [← hc]
      exact ⟨stateOf_mem U P _, congrArg (fun r : S.Role => (S.child r.1 r.2).ty) hrole⟩
    · dsimp only [D]
      rw [dif_neg h, dif_pos ⟨hs, hr⟩]
      exact Classical.choose_spec (exists_childMap_step8_child_type P s hs r hr)
  · intro U q hq i
    have h : R (stateOf U P q) ⟨q.2.val.ty, i⟩ (stateOf U P (U.childNode q hq i)) :=
      ⟨U, q, hq, i, rfl, rfl, rfl⟩
    have hex : ∃ t, R (stateOf U P q) ⟨q.2.val.ty, i⟩ t := ⟨_, h⟩
    dsimp only [D]
    rw [dif_pos hex]
    exact hsingle _ _ _ _ h (Classical.choose_spec hex)

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
Its value is identified in `mature_counter_value` below. -/
theorem mature_counter_spec (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (hmature : P.siteDepth (U.recordIncidence P q f hf) (U.recordSide P q f hf) ≤
      (U.hierarchy.firstProvider q f hf).1) (e : CellName S q.2.val.ty) :
    ((U.constantProfile P q f hf).value e).isSome = true ↔
      (U.recordOf P q f hf).ChainActive e := by
  sorry

/-- Q3, V4 §2.2 (S4d): on a chain-active edge the stored mature constant is the
common counter value at every point of the relative interior of the placed edge;
the anchor used by `constantProfile` is one such point. Added after audit A6 (P2). -/
theorem mature_counter_value (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (hmature : P.siteDepth (U.recordIncidence P q f hf) (U.recordSide P q f hf) ≤
      (U.hierarchy.firstProvider q f hf).1) (e : CellName S q.2.val.ty)
    (he : (U.recordOf P q f hf).ChainActive e) (x : E d)
    (hx : x ∈ relint (q.2.val.cell q.1 e.val)) :
    (U.constantProfile P q f hf).value e = some (U.sitesBefore P q f hf x) := by
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
