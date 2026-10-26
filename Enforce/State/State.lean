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

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
(S4e): "a chain ... of C is active iff the chain ... of containing cells of B
is active, with inherited orientations". Internal chains are the fixed flag;
the inherited full-chain test determines the entire oriented chain table. -/
private theorem exists_childMap_step4_chains :
    HEq (U.recordOf P (U.childNode q hq i) f hf).chains
      (V.recordOf P (V.childNode q' hq' i') g hg).chains := by
  sorry

/-- Step 4 of the V4 proof of `exists_childMap` (V4 2.3):
(S4d): "append i to the role word"; after maturity each active edge
"inherits kappa(e') = kappa(e)", and a new endpoint is "not a site".
This determines the short-word or mature-constant profile, including the
transition at the chosen side's site depth. -/
private theorem exists_childMap_step4_profile :
    HEq (U.recordOf P (U.childNode q hq i) f hf).counter
      (V.recordOf P (V.childNode q' hq' i') g hg).counter := by
  sorry

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
  sorry

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
  sorry

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
