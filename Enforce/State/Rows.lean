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
  haveI := facetRecords_finite P
  haveI : Fintype (FacetRecord P) := Fintype.ofFinite (FacetRecord P)
  classical
  haveI : Fintype (FacetRecord P → FacetRecord P) := Pi.instFintype
  exact (Set.finite_univ : (Set.univ : Set (FacetRecord P → FacetRecord P)).Finite).subset
    (Set.subset_univ _)

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

/-- Step 1 of the V4 proof of `restrictionOp_source` (V4 2.3): (S6): "re-expressed in C's frame". The full child frame is the parent frame composed with the normalized role placement. -/
private theorem restrictionOp_source_step1_frame (N : FramedNode S) (n : ℕ) (i : S.I N.ty) :
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

/-- Step 2 of the V4 proof of `restrictionOp_source` (V4 2.3): (S2): "i' = (A,i)". Disjoint nonempty child interiors make the child index unique. -/
private theorem restrictionOp_source_step2_role_injective (N : FramedNode S) (n : ℕ) :
    Function.Injective (N.child n) := by
  intro i j h
  have hty : (S.child N.ty i).ty = (S.child N.ty j).ty := congrArg FramedNode.ty h
  have he := congrArg (fun M : FramedNode S => M.prototypeFrame n) h
  dsimp only at he
  rw [restrictionOp_source_step1_frame, restrictionOp_source_step1_frame] at he
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

/-- Step 2 of the V4 proof of `restrictionOp_source` (V4 2.3): (S2): "(i',r_1,...,r_{k-1})". The parent of a prescribed honest child is the original node. -/
private theorem restrictionOp_source_step2_parent (U : HonestSource S) (q : U.Node)
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

/-- Step 2 of the V4 proof of `restrictionOp_source` (V4 2.3): (S2): "i' = (A,i)". The hierarchy role of a prescribed child is its prescribed index. -/
private theorem restrictionOp_source_step2_role (U : HonestSource S) (q : U.Node)
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
      exact congrArg (Sigma.mk N.ty) ((restrictionOp_source_step2_role_injective N n h).symm)
    exact aux _ _ hp hc

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3): (S4): "which case occurs, and f, depend only on (A,i,f')". Containment of placed cells is tested in the normalized one-step geometry. -/
private theorem restrictionOp_source_step4_containment (U : HonestSource S) (q : U.Node)
    (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) (f F : Cell d) :
    (U.childNode q hq i).2.val.cell (U.childNode q hq i).1 f ⊆ q.2.val.cell q.1 F ↔
      rolePlacement ⟨q.2.val.ty, i⟩ '' f.carrier ⊆ F.carrier := by
  change (q.2.val.child (q.1-1) i).prototypeFrame (q.1-1) '' f.carrier ⊆
    q.2.val.prototypeFrame q.1 '' F.carrier ↔ _
  rw [restrictionOp_source_step1_frame, Nat.sub_add_cancel hq]
  change (fun x => q.2.val.prototypeFrame q.1 (rolePlacement ⟨q.2.val.ty, i⟩ x)) ''
    f.carrier ⊆ _ ↔ _
  rw [← Set.image_image]
  exact Set.image_subset_image_iff (q.2.val.prototypeFrame q.1).injective

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3):
"same ... beta and provider; age min(age+1,C)". Before capping, restriction
adds one to the age and leaves the serving-child height unchanged. -/
private theorem restrictionOp_source_step4_inherited_numbers (U : HonestSource S)
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

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3):
"same iota". The transversal gives the same canonical name to equal
parent types and positioned primitive facets. -/
private theorem restrictionOp_source_step4_canonical (P : Params S)
    (a b : PrimitiveIncidence S) (h : SameIncidence a b) :
    P.canonical a = P.canonical b := by
  apply P.canonical_unique
  exact ⟨h.1.trans (P.canonical_spec b).1, h.2.trans (P.canonical_spec b).2⟩

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3):
"same iota, side ... and provider". Equality of the birth node and provider
carrier identifies the canonical incidence by cancelling the full birth frame. -/
private theorem restrictionOp_source_step4_provider_name (P : Params S) (U : HonestSource S)
    (c p : U.Node) (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f) (hF : ¬ U.hierarchy.IsFault p F)
    (hb : U.hierarchy.birthParent c f hf = U.hierarchy.birthParent p F hF)
    (hp : U.hierarchy.providerCarrier c f hf = U.hierarchy.providerCarrier p F hF) :
    U.recordIncidence P c f hf = U.recordIncidence P p F hF := by
  have hc := U.hierarchy.providerIncidence_spec c f hf
  have hpar := U.hierarchy.providerIncidence_spec p F hF
  apply restrictionOp_source_step4_canonical
  constructor
  · exact hc.1.trans ((congrArg (fun q : U.Node => q.2.val.ty) hb).trans hpar.1.symm)
  · have hplace := congrArg (fun B : U.Node => B.2.val.prototypeFrame B.1 ''
        (S.σ.symm '' (U.hierarchy.providerIncidence c f hf).positioned)) hb
    have heq := hplace.symm.trans (hc.2.2.2.symm.trans (hp.trans hpar.2.2.2))
    exact S.σ.symm.injective.image_injective
      (((U.hierarchy.birthParent p F hF).2.val.prototypeFrame
        (U.hierarchy.birthHeight p F hF)).injective.image_injective heq)

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3):
"same ... side". Once the canonical incidence and serving role agree,
the uniquely selected Boolean side agrees too. -/
private theorem restrictionOp_source_step4_side (P : Params S) (U V : HonestSource S)
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

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3):
"same iota, side ... and provider". Along an inherited facet the first
provider offset gains one, so the serving node, incidence and side are unchanged. -/
private theorem restrictionOp_source_step4_inherited_incidence (P : Params S) (U : HonestSource S)
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
  have hinc := restrictionOp_source_step4_provider_name P U c (U.hierarchy.parentNode c) f F hf hF hbirth hprovider
  have hserv : U.hierarchy.servingChild c f hf =
      U.hierarchy.servingChild (U.hierarchy.parentNode c) F hF := by
    have hc := (U.hierarchy.birthHeight_age_spec c f hf).2.1
    have hp := (U.hierarchy.birthHeight_age_spec (U.hierarchy.parentNode c) F hF).2.1
    have hoff : (U.hierarchy.firstProvider c f hf).1 =
        (U.hierarchy.firstProvider (U.hierarchy.parentNode c) F hF).1 + 1 := by omega
    simp only [CoherentHierarchy.servingChild, hoff, CoherentHierarchy.ancestor,
      Function.iterate_succ_apply]
  exact ⟨hF, hinc, restrictionOp_source_step4_side P U U _ _ f F hf hF hinc
    (congrArg U.hierarchy.nodeRole hserv)⟩

/-- Step 5 of the V4 proof of `restrictionOp_source` (V4 2.3): "the facets ... containing f',f'' are those containing f,tilde f". Relative interiors commute with every full affine frame, including anisotropic ones. -/
private theorem restrictionOp_source_step5_relint_image (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
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

/-- Step 5 of the V4 proof of `restrictionOp_source` (V4 2.3): "coalesce ... only if equal". Every placed listed cell has nonempty relative interior. -/
private theorem restrictionOp_source_step5_cell_nonempty (N : FramedNode S) (n : ℕ) (f : Cell d) :
    (relint (N.cell n f)).Nonempty := by
  rw [FramedNode.cell, restrictionOp_source_step5_relint_image]
  exact f.flat.relint_nonempty.image _

/-- Step 5 of the V4 proof of `restrictionOp_source` (V4 2.3): "the facets ... containing f',f''". A placed cell is the closure of its relative interior. -/
private theorem restrictionOp_source_step5_cell_closure (N : FramedNode S) (n : ℕ) (f : Cell d) :
    closure (relint (N.cell n f)) = N.cell n f := by
  rw [FramedNode.cell, restrictionOp_source_step5_relint_image]
  change closure ((N.prototypeFrame n).toHomeomorphOfFiniteDimensional '' relint f.carrier) = _
  rw [← Homeomorph.image_closure, f.flat.regularClosed]
  rfl

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the unique cell". A cell's carrier determines its dimension and hence its name. -/
private theorem restrictionOp_source_step4_cell_eq {e f : Cell d}
    (h : e.carrier = f.carrier) : e = f := by
  rcases e with ⟨K, n, hn⟩
  rcases f with ⟨K', n', hn'⟩
  cases h
  have hd : n = n' := hn.dimension.symm.trans hn'.dimension
  cases hd
  rfl

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3):
"t(s') is the unique cell of B with relint s' contained in relint t(s')".
This containment is a test in the fixed one-step substitution geometry. -/
private theorem restrictionOp_source_step4_relint_containment (U : HonestSource S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) (e t : Cell d) :
    relint ((U.childNode q hq i).2.val.cell (U.childNode q hq i).1 e) ⊆
        relint (q.2.val.cell q.1 t) ↔
      relint (rolePlacement ⟨q.2.val.ty, i⟩ '' e.carrier) ⊆ relint t.carrier := by
  change relint ((q.2.val.child (q.1-1) i).prototypeFrame (q.1-1) '' e.carrier) ⊆
    relint (q.2.val.prototypeFrame q.1 '' t.carrier) ↔ _
  rw [restrictionOp_source_step1_frame, Nat.sub_add_cancel hq]
  change relint ((fun x => q.2.val.prototypeFrame q.1 (rolePlacement ⟨q.2.val.ty, i⟩ x)) ''
    e.carrier) ⊆ _ ↔ _
  rw [← Set.image_image]
  simp only [restrictionOp_source_step5_relint_image]
  exact Set.image_subset_image_iff (q.2.val.prototypeFrame q.1).injective

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3):
"tau_f'(s') = tau_f(t(s'))". For an inherited finite facet, the recorded
canonical child stratum equals the recorded stratum of its containing parent cell. -/
private theorem restrictionOp_source_step4_inherited_tau (P : Params S) (U : HonestSource S)
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
  have hinc := restrictionOp_source_step4_provider_name P U c (U.hierarchy.parentNode c) f F hf hF hbirth hprov
  have hplace : U.providerPlacement P c f hf = U.providerPlacement P (U.hierarchy.parentNode c) F hF := by
    exact congrArg₂ (fun (B : U.Node) (a : P.Incidence) => P.incidencePlacement B.2.val B.1 a) hbirth hinc
  have hc := (Classical.choose_spec (U.recordTau_exists P c f hf e)).1
  have hp := (Classical.choose_spec (U.recordTau_exists P (U.hierarchy.parentNode c) F hF t')).1
  have heq : U.providerPlacement P c f hf '' (U.recordTau P c f hf e).val.val.carrier =
      U.providerPlacement P (U.hierarchy.parentNode c) F hF ''
        (U.recordTau P (U.hierarchy.parentNode c) F hF t').val.val.carrier :=
    hc.trans (hstrat.trans hp.symm)
  rw [hplace] at heq
  apply restrictionOp_source_step4_cell_eq
  exact (U.providerPlacement P (U.hierarchy.parentNode c) F hF).injective.image_injective heq

/-- Step 1 of the V4 proof of `restrictionOp_source` (V4 2.3):
"with inherited orientations". The edge of a full flag is a listed edge. -/
private def restrictionOp_source_step4_chains_step1_edge {A : S.ι}
    (c : FacetFlag S A) : EdgeName S :=
  ⟨A, ⟨(c.cell edgeIndex).val, by
    simp only [CellComplex.edges, Finset.mem_filter]
    exact ⟨(c.cell edgeIndex).property, c.dimension edgeIndex⟩⟩⟩

/-- Step 1 of the V4 proof of `restrictionOp_source` (V4 2.3):
"with inherited orientations". Read the signed vector from the orientation bit. -/
private def restrictionOp_source_step4_chains_step1_direction {A : S.ι}
    {f : FacetName S A} (c : OrientedChain f) : E d :=
  if c.forward then edgeVector (restrictionOp_source_step4_chains_step1_edge c.chain.val)
  else -edgeVector (restrictionOp_source_step4_chains_step1_edge c.chain.val)

/-- Step 1 of the V4 proof of `restrictionOp_source` (V4 2.3):
"a chain ... of C". Every cell of the chain is contained in its top facet. -/
private theorem restrictionOp_source_step4_chains_step1_subset {A : S.ι}
    {f : FacetName S A} (c : OrientedChain f) (j : FlagIndex d) :
    (c.chain.val.cell j).val.carrier ⊆ f.val.carrier := by
  have hj : j.val ≤ (facetIndex : FlagIndex d).val := by
    have := j.property
    change j.val ≤ d - 1
    omega
  simpa only [c.chain.property] using c.chain.val.nested j facetIndex hj

/-- Step 1 of the V4 proof of `restrictionOp_source` (V4 2.3):
"with inherited orientations". On a line, the inner-product test says exactly
that the oriented vectors are positive multiples of one another. -/
private theorem restrictionOp_source_step4_chains_step1_positive
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

/-- Step 1 of the V4 proof of `restrictionOp_source` (V4 2.3):
"equal affine spans". The direction of a placed segment is generated by
the placed difference of its endpoints. -/
private theorem restrictionOp_source_step4_chains_step1_segment_direction
    (T : E d ≃ᵃ[ℝ] E d) (x y : E d) :
    (affineSpan ℝ (T '' segment ℝ x y)).direction =
      Submodule.span ℝ {T.linear (y - x)} := by
  change (affineSpan ℝ (T.toAffineMap '' segment ℝ x y)).direction = _
  rw [← AffineSubspace.map_span T.toAffineMap,
    AffineSubspace.map_direction, direction_affineSpan, vectorSpan_segment,
    Submodule.map_span, Set.image_singleton]
  rfl

/-- Step 1 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the full-chain test". Stratum names and affine spans are the unoriented test. -/
private def restrictionOp_source_step4_chains_step1_geometry (U : HonestSource S)
    (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (c : OrientedChain f) : Prop :=
  ∀ j : FlagIndex d,
    (U.recordTau P q f hf
      ⟨c.chain.val.cell j, restrictionOp_source_step4_chains_step1_subset c j⟩).val.val =
      ((P.flag (U.recordIncidence P q f hf)).flag.cell j).val ∧
    affineSpan ℝ (q.2.val.cell q.1 (c.chain.val.cell j).val) =
      affineSpan ℝ (U.providerPlacement P q f hf ''
        ((P.flag (U.recordIncidence P q f hf)).flag.cell j).val.carrier)

/-- Step 1 of the V4 proof of `restrictionOp_source` (V4 2.3):
"equal affine spans ... with its orientation". Rewrite the geometric definition
using canonical stratum names and a positive multiple of the signed edge vector. -/
private theorem restrictionOp_source_step4_chains_step1_test (U : HonestSource S)
    (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (c : OrientedChain f) :
    U.ActiveChain P q f hf c ↔
      restrictionOp_source_step4_chains_step1_geometry U P q f hf c ∧
      ∃ a : ℝ, 0 < a ∧ U.counterDirection P q f hf =
        a • (q.2.val.prototypeFrame q.1).linear
          (restrictionOp_source_step4_chains_step1_direction c) := by
  let e := restrictionOp_source_step4_chains_step1_edge c.chain.val
  let v := (q.2.val.prototypeFrame q.1).linear (edgeVector e)
  let u := U.counterDirection P q f hf
  have horient (H : restrictionOp_source_step4_chains_step1_geometry U P q f hf c) :
      (c.forward = true ↔ 0 < inner ℝ u v) ↔
        ∃ a : ℝ, 0 < a ∧ u = a • (q.2.val.prototypeFrame q.1).linear
          (restrictionOp_source_step4_chains_step1_direction c) := by
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
      restrictionOp_source_step4_chains_step1_segment_direction] at hspan
    change Submodule.span ℝ {v} = Submodule.span ℝ {u} at hspan
    have hline : u ∈ Submodule.span ℝ {v} := by
      rw [hspan]
      exact Submodule.mem_span_singleton_self _
    have h := restrictionOp_source_step4_chains_step1_positive u v hu hv hline c.forward
    simpa only [restrictionOp_source_step4_chains_step1_direction, apply_ite, map_neg] using h
  constructor
  · intro hc
    have H : restrictionOp_source_step4_chains_step1_geometry U P q f hf c := by
      intro j
      obtain ⟨hs, ht, hspan⟩ := hc.1 j
      refine ⟨?_, hspan⟩
      have hτ := (Classical.choose_spec (U.recordTau_exists P q f hf
        ⟨c.chain.val.cell j, restrictionOp_source_step4_chains_step1_subset c j⟩)).1
      exact restrictionOp_source_step4_cell_eq
        ((U.providerPlacement P q f hf).injective.image_injective (hτ.trans ht))
    exact ⟨H, (horient H).mp hc.2⟩
  · rintro ⟨H, hdir⟩
    refine ⟨?_, (horient H).mpr hdir⟩
    intro j
    refine ⟨U.cellInFacet_placed q f
      ⟨c.chain.val.cell j, restrictionOp_source_step4_chains_step1_subset c j⟩, ?_, (H j).2⟩
    have hτ := (Classical.choose_spec (U.recordTau_exists P q f hf
      ⟨c.chain.val.cell j, restrictionOp_source_step4_chains_step1_subset c j⟩)).1
    exact hτ.symm.trans (congrArg
      (fun e : Cell d => U.providerPlacement P q f hf '' e.carrier) (H j).1)

/-- Step 2 of the V4 proof of `restrictionOp_source` (V4 2.3):
"computed in the fixed substitution geometry". A common full affine frame
can be cancelled from equality of affine spans. -/
private theorem restrictionOp_source_step4_chains_step2_span
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

/-- Step 3 of the V4 proof of `restrictionOp_source` (V4 2.3):
"same ... provider". Inheritance preserves its full placement, including its
canonical flag and oriented direction. -/
private theorem restrictionOp_source_step4_chains_step3_placement (U : HonestSource S)
    (P : Params S) (c p : U.Node) (hp : U.hierarchy.parentNode c = p)
    (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f) (hF : ¬ U.hierarchy.IsFault p F)
    (hsub : c.2.val.cell c.1 f.val ⊆ p.2.val.cell p.1 F.val) :
    U.recordIncidence P c f hf = U.recordIncidence P p F hF ∧
      U.providerPlacement P c f hf = U.providerPlacement P p F hF ∧
      U.counterDirection P c f hf = U.counterDirection P p F hF := by
  subst p
  obtain ⟨_, hprov, hbirth, _, _⟩ := U.hierarchy.restriction_det_inherited c F f hF hsub
  have hi := restrictionOp_source_step4_provider_name P U c (U.hierarchy.parentNode c)
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

/-- Step 3 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the chain ... of containing cells ... with inherited orientations".
This relation is tested entirely in the one-step prototype geometry. -/
private def restrictionOp_source_step4_chains_step3_restriction
    (r : S.Role) {A B : S.ι} {f : FacetName S A} {F : FacetName S B}
    (c : OrientedChain f) (t : OrientedChain F) : Prop :=
  (∀ j : FlagIndex d,
    relint (rolePlacement r '' (c.chain.val.cell j).val.carrier) ⊆
      relint (t.chain.val.cell j).val.carrier) ∧
  (∀ j : FlagIndex d,
    affineSpan ℝ (rolePlacement r '' (c.chain.val.cell j).val.carrier) =
      affineSpan ℝ (t.chain.val.cell j).val.carrier) ∧
  ∃ a : ℝ, 0 < a ∧
    (rolePlacement r).linear (restrictionOp_source_step4_chains_step1_direction c) =
      a • restrictionOp_source_step4_chains_step1_direction t

/-- Step 3 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the unique cell ... with relint s' contained in relint t(s')". Nonempty
relative interiors distinguish the containing names in a proper complex. -/
private theorem restrictionOp_source_step4_chains_step3_unique {A : S.ι}
    (e t : CellName S A) (K : Set (E d)) (hK : K.Nonempty)
    (he : K ⊆ relint e.val.carrier) (ht : K ⊆ relint t.val.carrier) : e = t := by
  apply Subtype.ext
  by_contra hne
  obtain ⟨x, hx⟩ := hK
  exact Set.disjoint_left.mp
    ((S.cx A).relint_disjoint e.val e.property t.val t.property hne) (he hx) (ht hx)

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3):
"If the chain of B is active ... the chain of C". A full chain with the
inherited strata, spans and orientation restricts to an active child chain. -/
private theorem restrictionOp_source_step4_chains_step4_restrict (U : HonestSource S)
    (P : Params S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) (F : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hsub : rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (c : OrientedChain f) (t : OrientedChain F)
    (ht : U.ActiveChain P q F hF t)
    (hct : restrictionOp_source_step4_chains_step3_restriction ⟨q.2.val.ty, i⟩ c t) :
    U.ActiveChain P (U.childNode q hq i) f hf c := by
  let C := U.childNode q hq i
  let R := rolePlacement ⟨q.2.val.ty, i⟩
  let T := q.2.val.prototypeFrame q.1
  have hsub' := (restrictionOp_source_step4_containment U q hq i f.val F.val).mpr hsub
  obtain ⟨hi, hplace, hdir⟩ := restrictionOp_source_step4_chains_step3_placement U P C q
    (restrictionOp_source_step2_parent U q hq i) f F hf hF hsub'
  have hframe : C.2.val.prototypeFrame C.1 = R.trans T := by
    simpa only [Nat.sub_add_cancel hq] using restrictionOp_source_step1_frame q.2.val (q.1-1) i
  obtain ⟨H, b, hb, htb⟩ := (restrictionOp_source_step4_chains_step1_test U P q F hF t).mp ht
  obtain ⟨hrel, hspan, a, ha, hca⟩ := hct
  apply (restrictionOp_source_step4_chains_step1_test U P C f hf c).mpr
  refine ⟨?_, b / a, div_pos hb ha, ?_⟩
  · intro j
    obtain ⟨e, he, hτ⟩ := restrictionOp_source_step4_inherited_tau P U C q
      (restrictionOp_source_step2_parent U q hq i) f F hf hF hsub'
      ⟨c.chain.val.cell j, restrictionOp_source_step4_chains_step1_subset c j⟩
    have he' := (restrictionOp_source_step4_relint_containment U q hq i
      (c.chain.val.cell j).val e.val.val).mp he
    have hn : (relint (R '' (c.chain.val.cell j).val.carrier)).Nonempty := by
      rw [restrictionOp_source_step5_relint_image]
      exact (c.chain.val.cell j).val.flat.relint_nonempty.image _
    have het : e.val = t.chain.val.cell j :=
      restrictionOp_source_step4_chains_step3_unique e.val (t.chain.val.cell j) _ hn he' (hrel j)
    have heq : e = ⟨t.chain.val.cell j, restrictionOp_source_step4_chains_step1_subset t j⟩ :=
      Subtype.ext het
    rw [heq] at hτ
    refine ⟨hτ.trans ((H j).1.trans ?_), ?_⟩
    · exact congrArg (fun a : P.Incidence => ((P.flag a).flag.cell j).val) hi.symm
    · have hspan' := (restrictionOp_source_step4_chains_step2_span T
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
    change b • T.linear (restrictionOp_source_step4_chains_step1_direction t) =
      (b / a) • T.linear (R.linear (restrictionOp_source_step4_chains_step1_direction c))
    rw [hca, map_smul, smul_smul, div_mul_cancel₀ b (ne_of_gt ha)]

/-- Step 5 of the V4 proof of `restrictionOp_source` (V4 2.3):
"Conversely ... t(s'_j) is a j-cell". The hereditary full-flag lemma lifts
an active child chain, retaining its spans and its oriented edge. -/
private theorem restrictionOp_source_step4_chains_step5_lift (U : HonestSource S)
    (P : Params S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) (F : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hsub : rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier)
    (c : OrientedChain f) (hc : U.ActiveChain P (U.childNode q hq i) f hf c) :
    ∃ t : OrientedChain F, U.ActiveChain P q F hF t ∧
      restrictionOp_source_step4_chains_step3_restriction ⟨q.2.val.ty, i⟩ c t := by
  classical
  let C := U.childNode q hq i
  let R := rolePlacement ⟨q.2.val.ty, i⟩
  let T := q.2.val.prototypeFrame q.1
  have hsub' := (restrictionOp_source_step4_containment U q hq i f.val F.val).mpr hsub
  obtain ⟨hi, hplace, hdir⟩ := restrictionOp_source_step4_chains_step3_placement U P C q
    (restrictionOp_source_step2_parent U q hq i) f F hf hF hsub'
  have hframe : C.2.val.prototypeFrame C.1 = R.trans T := by
    simpa only [Nat.sub_add_cancel hq] using restrictionOp_source_step1_frame q.2.val (q.1-1) i
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
    apply restrictionOp_source_step4_cell_eq
    exact ((U.hierarchy.servingChild C f hf).2.val.prototypeFrame
      (U.hierarchy.servingChild C f hf).1).injective.image_injective (hτ.trans (hG j).symm)
  have hp : U.hierarchy.ancestor C 1 = q := by
    simpa only [CoherentHierarchy.ancestor, Function.iterate_one] using
      restrictionOp_source_step2_parent U q hq i
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
    · obtain ⟨x, hx⟩ := restrictionOp_source_step5_cell_nonempty q.2.val q.1 F'.val
      exact False.elim (((U.hierarchy.boundaryOffsets_downward q F').1
        (intrinsicInterior_subset hx)).2 (hint hx))
  let tc : OrientedChain F :=
    ⟨⟨t, htop⟩, decide (0 < inner ℝ (U.counterDirection P q F hF)
      (T.linear (edgeVector (restrictionOp_source_step4_chains_step1_edge t))))⟩
  have htc : U.ActiveChain P q F hF tc := by
    constructor
    · intro j
      obtain ⟨hrel, htF, hstr⟩ := ht j
      have hstr' := hstr.trans ((hG j).trans (hflag j))
      refine ⟨htF, hstr', ?_⟩
      have hCsub : C.2.val.cell C.1 (c.chain.val.cell j).val ⊆
          q.2.val.cell q.1 (t.cell j).val := by
        simpa only [restrictionOp_source_step5_cell_closure] using closure_mono hrel
      have htstr : q.2.val.cell q.1 (t.cell j).val ⊆
          U.providerPlacement P q F hF ''
            ((P.flag (U.recordIncidence P q F hF)).flag.cell j).val.carrier := by
        have h := closure_mono (U.hierarchy.stratumMap_spec q F hF (t.cell j) htF).1
        simp only [restrictionOp_source_step5_cell_closure] at h
        exact h.trans_eq hstr'
      have hCspan := (hc.1 j).choose_spec.2.trans (congrArg (affineSpan ℝ) (hflag j))
      apply le_antisymm (affineSpan_mono ℝ htstr)
      exact hCspan.symm.trans_le (affineSpan_mono ℝ hCsub)
    · change (decide (0 < inner ℝ (U.counterDirection P q F hF)
        (T.linear (edgeVector (restrictionOp_source_step4_chains_step1_edge t)))) = true ↔ _)
      exact decide_eq_true_iff
  refine ⟨tc, htc, ?_, ?_, ?_⟩
  · intro j
    exact (restrictionOp_source_step4_relint_containment U q hq i
      (c.chain.val.cell j).val (t.cell j).val).mp (ht j).1
  · intro j
    have hCspan := (hc.1 j).choose_spec.2.trans
      ((congrArg (affineSpan ℝ) (hflag j)).trans (htc.1 j).choose_spec.2.symm)
    change affineSpan ℝ (C.2.val.prototypeFrame C.1 '' (c.chain.val.cell j).val.carrier) =
      affineSpan ℝ (T '' (t.cell j).val.carrier) at hCspan
    rw [hframe] at hCspan
    apply (restrictionOp_source_step4_chains_step2_span T
      (R '' (c.chain.val.cell j).val.carrier) (t.cell j).val.carrier).mp
    simpa only [Set.image_image] using hCspan
  · obtain ⟨_, b, hb, hcb⟩ := (restrictionOp_source_step4_chains_step1_test U P C f hf c).mp hc
    obtain ⟨_, a, ha, hta⟩ := (restrictionOp_source_step4_chains_step1_test U P q F hF tc).mp htc
    have heq : b • R.linear (restrictionOp_source_step4_chains_step1_direction c) =
        a • restrictionOp_source_step4_chains_step1_direction tc := by
      apply T.linear.injective
      have he := hcb.symm.trans (hdir.trans hta)
      rw [hframe] at he
      simpa only [map_smul] using he
    refine ⟨a / b, div_pos ha hb, ?_⟩
    calc
      _ = b⁻¹ • (b • R.linear (restrictionOp_source_step4_chains_step1_direction c)) := by
        rw [inv_smul_smul₀ (ne_of_gt hb)]
      _ = b⁻¹ • (a • restrictionOp_source_step4_chains_step1_direction tc) := congrArg (b⁻¹ • ·) heq
      _ = _ := by rw [smul_smul, ← div_eq_inv_mul]

/-- Step 1 of the V4 proof of `restrictionOp_source` (V4 2.3):
"append i to the role word". The downward list reverses the ancestor list,
so the immediate role is its last letter. -/
private theorem restrictionOp_source_step4_profile_step1_downRoles
    (U : HonestSource S) (c : U.Node) (a : ℕ) :
    U.downRoles c (a + 1) =
      U.downRoles (U.hierarchy.parentNode c) a ++ [U.hierarchy.nodeRole c] := by
  simp only [HonestSource.downRoles, List.ofFn_succ, List.reverse_cons,
    Fin.val_succ, Fin.val_zero, CoherentHierarchy.ancestor, Function.iterate_zero, id_eq,
    Function.iterate_succ_apply]

/-- Step 2 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the depth of B below H" increases by one on an inherited facet. -/
private theorem restrictionOp_source_step4_profile_step2_depth
    (U : HonestSource S) (c p : U.Node) (hp : U.hierarchy.parentNode c = p)
    (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f) (hF : ¬ U.hierarchy.IsFault p F)
    (hsub : c.2.val.cell c.1 f.val ⊆ p.2.val.cell p.1 F.val) :
    (U.hierarchy.firstProvider c f hf).1 = (U.hierarchy.firstProvider p F hF).1 + 1 := by
  obtain ⟨_, ha, _⟩ := restrictionOp_source_step4_inherited_numbers U c p hp f F hf hsub
  have hc := (U.hierarchy.birthHeight_age_spec c f hf).2.1
  have hp := (U.hierarchy.birthHeight_age_spec p F hF).2.1
  omega

/-- Step 3 of the V4 proof of `restrictionOp_source` (V4 2.3):
"compute from the finite lookup". A downward word places the recorded node
in its ancestor's prototype, using the full affine frames. -/
private theorem restrictionOp_source_step4_profile_step3_word_frame
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
      exact h.trans (restrictionOp_source_step1_frame _ _ _)
    rw [restrictionOp_source_step4_profile_step1_downRoles, hw]
    simp only [wordPlacement, AffineEquiv.refl_trans]
    rw [hc, ih (U.hierarchy.parentNode c), AffineEquiv.trans_assoc]
    rfl

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3):
"same ... side" identifies the serving child's full affine frame. -/
private theorem restrictionOp_source_step4_profile_step4_serving_frame
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
    exact h.trans (restrictionOp_source_step1_frame _ _ _)
  exact hframe.trans (congrArg (fun r : S.Role => (rolePlacement r).trans
    ((U.hierarchy.parentNode H).2.val.prototypeFrame (U.hierarchy.parentNode H).1)) hrole.symm)

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the sites are named vertices ... of H". The ambient site is its fixed
side-specific coordinate placed by H's full frame. -/
private theorem restrictionOp_source_step4_profile_step4_site_placement
    (P : Params S) (U : HonestSource S) (c : U.Node)
    (f : FacetName S c.2.val.ty) (hf : ¬ U.hierarchy.IsFault c f) (a : Fin P.N) :
    U.sitePoint P c f hf a =
      (U.hierarchy.servingChild c f hf).2.val.prototypeFrame (U.hierarchy.servingChild c f hf).1
        (P.sites (U.recordIncidence P c f hf) (U.recordSide P c f hf) a) := by
  rw [restrictionOp_source_step4_profile_step4_serving_frame P U c f hf]
  simp [HonestSource.sitePoint, HonestSource.providerPlacement, Params.incidencePlacement,
    Params.canonicalSite, rolePlacement, PrimitiveIncidence.sideRole]

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the sites are named vertices of the depth-r subdivision of H". Their
coordinates in H are exactly the fixed side-specific sites. -/
private theorem restrictionOp_source_step4_profile_step4_site_coordinates
    (P : Params S) (U : HonestSource S) (c : U.Node)
    (f : FacetName S c.2.val.ty) (hf : ¬ U.hierarchy.IsFault c f)
    (a : Fin P.N) (x : E d) :
    U.sitePoint P c f hf a = c.2.val.prototypeFrame c.1 x ↔
      P.sites (U.recordIncidence P c f hf) (U.recordSide P c f hf) a =
        wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) x := by
  rw [restrictionOp_source_step4_profile_step4_site_placement P U c f hf a,
    restrictionOp_source_step4_profile_step3_word_frame U c
    (U.hierarchy.firstProvider c f hf).1]
  exact ((U.hierarchy.servingChild c f hf).2.val.prototypeFrame
    (U.hierarchy.servingChild c f hf).1).injective.eq_iff

/-- Step 5 of the V4 proof of `restrictionOp_source` (V4 2.3, S4d):
"the sites" lie on the selected provider edge, on either serving side. -/
private theorem restrictionOp_source_step4_profile_step5_site_in_flag
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

/-- Step 5 of the V4 proof of `restrictionOp_source` (V4 2.3, S4d):
the counter is read "along" the oriented flag edge. Differences of points on
its supporting line are scalar multiples of the transported direction. -/
private theorem restrictionOp_source_step4_profile_step5_flag_line
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

/-- Step 5 of the V4 proof of `restrictionOp_source` (V4 2.3, S4d):
the full-chain test puts an active edge in the flag edge's affine span.
Consequently its points and all sites share one counter direction. -/
private theorem restrictionOp_source_step4_profile_step5_site_line
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
  exact restrictionOp_source_step4_profile_step5_flag_line (P.flag (U.recordIncidence P q f hf))
    (U.providerPlacement P q f hf) _ x
    (mem_affineSpan ℝ (restrictionOp_source_step4_profile_step5_site_in_flag P U q f hf a)) hx

/-- Step 5 of the V4 proof of `restrictionOp_source` (V4 2.3):
"compute from the finite lookup" is invariant under a full affine frame.
An invertible linear map preserves the sign of the inner product of two
collinear vectors; no similarity or uniform scaling is assumed. -/
private theorem restrictionOp_source_step4_profile_step5_linear_order
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

/-- Step 5 of the V4 proof of `restrictionOp_source` (V4 2.3):
"compute from the finite lookup the constants kappa(e')". On an active edge,
the order of its anchor and the sites can be tested in the serving prototype. -/
private theorem restrictionOp_source_step4_profile_step5_word_count
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
    rw [restrictionOp_source_step4_profile_step4_serving_frame P U c f hf]
    apply AffineEquiv.ext
    intro x
    simp [R, rolePlacement, PrimitiveIncidence.sideRole, HonestSource.providerPlacement,
      Params.incidencePlacement, ι, b]
  have hdir : ψ.linear (U.recordOf P c f hf).servingDirection = U.counterDirection P c f hf :=
    congrArg (fun φ : E d ≃ᵃ[ℝ] E d => φ.linear (P.flag ι).direction) hframes
  have hpoint := congrArg (fun φ : E d ≃ᵃ[ℝ] E d => φ (cellAnchor e.val))
    (restrictionOp_source_step4_profile_step3_word_frame U c (U.hierarchy.firstProvider c f hf).1)
  change c.2.val.prototypeFrame c.1 (cellAnchor e.val) =
    ψ (wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) (cellAnchor e.val)) at hpoint
  dsimp only [HonestSource.sitesBefore]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro a _
  have hsite := restrictionOp_source_step4_profile_step4_site_placement P U c f hf a
  have hdiff : ψ.linear (P.sites ι b a -
      wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) (cellAnchor e.val)) =
      U.sitePoint P c f hf a - c.2.val.prototypeFrame c.1 (cellAnchor e.val) := by
    calc
      _ = ψ (P.sites ι b a) - ψ
          (wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) (cellAnchor e.val)) :=
        ψ.toAffineMap.linearMap_vsub _ _
      _ = _ := by rw [← hsite, ← hpoint]
  obtain ⟨t, ht⟩ := restrictionOp_source_step4_profile_step5_site_line P U c f hf e he a _
    (mem_affineSpan ℝ (Set.mem_image_of_mem _ (intrinsicInterior_subset (cellAnchor_mem e.val))))
  have hscalar : t • (U.recordOf P c f hf).servingDirection =
      P.sites ι b a - wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1)
        (cellAnchor e.val) := by
    apply ψ.linear.injective
    rw [map_smul, hdir, hdiff]
    exact ht
  have h := restrictionOp_source_step4_profile_step5_linear_order ψ.linear
    (U.recordOf P c f hf).servingDirection _ ⟨t, hscalar⟩
  rwa [hdir, hdiff] at h

/-- Step 8 of the V4 proof of `restrictionOp_source` (V4 2.3, 1.23(c)):
"sites on chain-active edges of B are vertices of B when a >= r".
The active-edge hypothesis retains the selected-owner condition of site persistence. -/
private theorem restrictionOp_source_step4_profile_step8_mature_site
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
    rw [restrictionOp_source_step4_profile_step4_serving_frame P U q f hf]
    have h := congrArg (fun K : Set (E d) =>
      (U.hierarchy.birthParent q f hf).2.val.prototypeFrame (U.hierarchy.birthHeight q f hf) ''
        (S.σ.symm '' K)) (P.sideFlag_eq ι s j)
    simpa only [placedSet, Set.image_image] using h
  have hcellsF (j : FlagIndex d) : (F.cell j).val = ((P.sideFlag ι s).cell j).val := by
    apply restrictionOp_source_step4_cell_eq
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
    rw [restrictionOp_source_step4_profile_step4_site_placement P U q f hf a]
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

/-- Step 7 of the V4 proof of `restrictionOp_source` (V4 2.3, S4d):
"kappa is constant on relint e" once the owner reaches its side's site depth.
Listed vertices cannot lie in the relative interior of a listed edge. Each
site's continuous signed coordinate therefore has a constant sign there. -/
private theorem restrictionOp_source_step4_profile_step7_mature_constant
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
    obtain ⟨v, hv⟩ := restrictionOp_source_step4_profile_step8_mature_site P U q f hf hm e he a
      (intrinsicInterior_subset ha)
    rw [hv, FramedNode.cell, restrictionOp_source_step5_relint_image] at ha
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
    rw [FramedNode.cell, restrictionOp_source_step5_relint_image]
    exact e.val.flat.relint_connected.isPreconnected.image _
      (q.2.val.prototypeFrame q.1).toHomeomorphOfFiniteDimensional.continuous.continuousOn
  by_cases hD : U.counterDirection P q f hf = 0
  · simp only [HonestSource.sitesBefore, hD, inner_zero_left]
  · have hpos := real_inner_self_pos.mpr hD
    have hnonzero (a : Fin P.N) (z : E d) (hz : z ∈ relint (q.2.val.cell q.1 e.val)) :
        inner ℝ (U.counterDirection P q f hf) (U.sitePoint P q f hf a - z) ≠ 0 := by
      obtain ⟨t, ht⟩ := restrictionOp_source_step4_profile_step5_site_line P U q f hf e he a z
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

/-- Step 9 of the V4 proof of `restrictionOp_source` (V4 2.3):
"same ... provider" and "same ... side" preserve the ambient sites and their
counting function along an inherited facet. -/
private theorem restrictionOp_source_step4_profile_step9_inherited_sites
    (P : Params S) (U : HonestSource S) (c p : U.Node)
    (hp : U.hierarchy.parentNode c = p)
    (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f) (hF : ¬ U.hierarchy.IsFault p F)
    (hsub : c.2.val.cell c.1 f.val ⊆ p.2.val.cell p.1 F.val) :
    (∀ a, U.sitePoint P c f hf a = U.sitePoint P p F hF a) ∧
      ∀ x, U.sitesBefore P c f hf x = U.sitesBefore P p F hF x := by
  subst p
  obtain ⟨_, _, hb, _, _⟩ := U.hierarchy.restriction_det_inherited c F f hF hsub
  obtain ⟨_, hi, hs⟩ := restrictionOp_source_step4_inherited_incidence P U c
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

/-- Step 17 of the V4 proof of `restrictionOp_source` (V4 2.3):
"inherits kappa(e') = kappa(e)". The child's anchor is inside its containing
parent edge, where the unchanged ambient counting function is constant. -/
private theorem restrictionOp_source_step4_profile_step17_inherited_value
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
  have hsub' := (restrictionOp_source_step4_containment U q hq i f.val F.val).mpr hsub
  rw [(restrictionOp_source_step4_profile_step9_inherited_sites P U _ _
    (restrictionOp_source_step2_parent U q hq i) f F hf hF hsub').2]
  apply restrictionOp_source_step4_profile_step7_mature_constant P U q F hF hm E hE
  · apply (restrictionOp_source_step4_relint_containment U q hq i e.val E.val).mpr heE
    rw [FramedNode.cell, restrictionOp_source_step5_relint_image]
    exact Set.mem_image_of_mem _ (cellAnchor_mem e.val)
  · rw [FramedNode.cell, restrictionOp_source_step5_relint_image]
    exact Set.mem_image_of_mem _ (cellAnchor_mem E.val)

/-- Step 18 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the site status ... is inherited if v' is a vertex of B ... and is not a site
otherwise". On a mature active edge, a site is precisely a flagged parent vertex. -/
private theorem restrictionOp_source_step4_profile_step18_endpoint_lookup
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
    obtain ⟨v, hv⟩ := restrictionOp_source_step4_profile_step8_mature_site P U q F hF hm E hE a hx
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

/-- Step 4 of the V4 proof of `restrictionOp_source` (V4 2.3):
"All these are finite computations". The incidence-side equality determines
the redundant serving role, and equality of the remaining data determines a record. -/
private theorem restrictionOp_source_step4_record_ext {P : Params S} {r t : FacetRecord P}
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

/-- Step 6 of the V4 proof of `restrictionOp_source` (V4 2.3):
"computed in the fixed substitution geometry". Normalize the inherited containment. -/
private theorem restrictionOp_source_step6_normalize {A : S.ι} (i : S.I A)
    (e F : Cell d) :
    placedSet (S.child A i).frame e.carrier ⊆ S.σ '' F.carrier ↔
      rolePlacement ⟨A, i⟩ '' e.carrier ⊆ F.carrier := by
  constructor
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, he⟩ := h ⟨y, hy, rfl⟩
    change S.σ.symm ((S.child A i).frame y) ∈ F.carrier
    rw [← he, S.σ.symm_apply_apply]
    exact hz
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨rolePlacement ⟨A, i⟩ y, h ⟨y, hy, rfl⟩, S.σ.apply_symm_apply _⟩

/-- Step 6 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the unique cell ... with relint s' contained in relint t(s')".
The containing-cell condition commutes with normalization by sigma. -/
private theorem restrictionOp_source_step6_normalize_relint {A : S.ι} (i : S.I A)
    (e F : Cell d) :
    relint (placedSet (S.child A i).frame e.carrier) ⊆ relint (S.σ '' F.carrier) ↔
      relint (rolePlacement ⟨A, i⟩ '' e.carrier) ⊆ relint F.carrier := by
  have he : placedSet (S.child A i).frame e.carrier =
      S.σ.toAffineEquiv '' (rolePlacement ⟨A, i⟩ '' e.carrier) := by
    simp [rolePlacement, placedSet, Set.image_image]
  rw [he]
  change relint (S.σ.toAffineEquiv '' _) ⊆ relint (S.σ.toAffineEquiv '' F.carrier) ↔ _
  rw [restrictionOp_source_step5_relint_image S.σ.toAffineEquiv,
    restrictionOp_source_step5_relint_image S.σ.toAffineEquiv]
  exact Set.image_subset_image_iff S.σ.injective

/-- Step 6 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the unique cell ... t(s')". The chosen finite lookup has its geometric specification. -/
private theorem restrictionOp_source_step6_cell_spec {P : Params S} (r : FacetRecord P)
    (i : S.I r.ty) (f : FacetName S (S.child r.ty i).ty)
    (h : placedSet (S.child r.ty i).frame f.val.carrier ⊆ S.σ '' r.facet.val.carrier)
    (e : CellsInFacet (S.child r.ty i).ty f) :
    relint (rolePlacement ⟨r.ty, i⟩ '' e.val.val.carrier) ⊆
      relint (inheritedCell r i f h e).val.val.carrier :=
  (restrictionOp_source_step6_normalize_relint i _ _).mp
    (Classical.choose_spec (inheritedCell_exists r i f h e)).1

/-- Step 6 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the unique cell ... t(s')". Its specification uniquely determines the lookup. -/
private theorem restrictionOp_source_step6_cell_unique {P : Params S} (r : FacetRecord P)
    (i : S.I r.ty) (f : FacetName S (S.child r.ty i).ty)
    (h : placedSet (S.child r.ty i).frame f.val.carrier ⊆ S.σ '' r.facet.val.carrier)
    (e : CellsInFacet (S.child r.ty i).ty f) (t : CellsInFacet r.ty r.facet)
    (ht : relint (rolePlacement ⟨r.ty, i⟩ '' e.val.val.carrier) ⊆ relint t.val.val.carrier) :
    inheritedCell r i f h e = t :=
  ((Classical.choose_spec (inheritedCell_exists r i f h e)).2 t
    ((restrictionOp_source_step6_normalize_relint i _ _).mpr ht)).symm

/-- Step 6 of the V4 proof of `restrictionOp_source` (V4 2.3):
"t(s'_j) is a j-cell with aff t(s'_j) = aff s'_j".
Containing cells of equal dimension have equal affine spans. -/
private theorem restrictionOp_source_step6_span (T : E d ≃ᵃ[ℝ] E d)
    (e t : Cell d) (hd : e.dim = t.dim)
    (h : relint (T '' e.carrier) ⊆ relint t.carrier) :
    affineSpan ℝ (T '' e.carrier) = affineSpan ℝ t.carrier := by
  have hcl : closure (relint (T '' e.carrier)) = T '' e.carrier := by
    rw [restrictionOp_source_step5_relint_image]
    change closure (T.toHomeomorphOfFiniteDimensional '' relint e.carrier) = _
    rw [← T.toHomeomorphOfFiniteDimensional.image_closure, e.flat.regularClosed]
    rfl
  have hsub : T '' e.carrier ⊆ t.carrier := by
    simpa only [hcl, t.flat.regularClosed] using closure_mono h
  have hle := affineSpan_mono ℝ hsub
  apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le _ _ hle
  · apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
    change Module.finrank ℝ (affineSpan ℝ (T.toAffineMap '' e.carrier)).direction = _
    rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
    change Module.finrank ℝ ((affineSpan ℝ e.carrier).direction.map
      (T.linear : E d →ₗ[ℝ] E d)) = _
    rw [LinearEquiv.finrank_map_eq]
    exact e.flat.dimension.trans (hd.trans t.flat.dimension.symm)
  · exact (e.flat.connected.nonempty.image T).mono (subset_affineSpan ℝ _)

/-- Step 6 of the V4 proof of `restrictionOp_source` (V4 2.3):
"with inherited orientations". The direction of an oriented chain spans its edge line. -/
private theorem restrictionOp_source_step6_chain_direction {A : S.ι}
    {f : FacetName S A} (c : OrientedChain f) (T : E d ≃ᵃ[ℝ] E d) :
    (affineSpan ℝ (T '' (c.chain.val.cell edgeIndex).val.carrier)).direction =
      Submodule.span ℝ {T.linear (chainVector c)} := by
  let e := restrictionOp_source_step4_chains_step1_edge c.chain.val
  have he : (c.chain.val.cell edgeIndex).val.carrier =
      segment ℝ (Classical.choose (edge_endpoints_exist e)).1
        (Classical.choose (edge_endpoints_exist e)).2 :=
    (Classical.choose_spec (edge_endpoints_exist e)).2
  rw [he, restrictionOp_source_step4_chains_step1_segment_direction]
  change Submodule.span ℝ {T.linear (edgeVector e)} = _
  change _ = Submodule.span ℝ {T.linear (if c.forward then edgeVector e else -edgeVector e)}
  cases c.forward <;> simp [← Set.neg_singleton, Submodule.span_neg]

/-- Step 6 of the V4 proof of `restrictionOp_source` (V4 2.3):
"re-expressed in C's frame". Normalization cancels the expansion in edge vectors. -/
private theorem restrictionOp_source_step6_role_linear {A : S.ι} (i : S.I A) (v : E d) :
    S.σ ((rolePlacement ⟨A, i⟩).linear v) = (S.child A i).rotation v := by
  change S.σ (S.σ.symm ((S.child A i).rotation v)) = _
  exact S.σ.apply_symm_apply _

set_option maxHeartbeats 800000 in
/-- Step 6 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the chain ... of containing cells ... with inherited orientations".
The lookup and inner-product test equal the geometric full-chain relation. -/
private theorem restrictionOp_source_step6_chain_lookup {P : Params S}
    (r : FacetRecord P) (i : S.I r.ty) (f : FacetName S (S.child r.ty i).ty)
    (h : placedSet (S.child r.ty i).frame f.val.carrier ⊆ S.σ '' r.facet.val.carrier)
    (c : OrientedChain f) (t : OrientedChain r.facet) :
    ((∀ j, ∃ hs : (c.chain.val.cell j).val.carrier ⊆ f.val.carrier,
      (inheritedCell r i f h ⟨c.chain.val.cell j, hs⟩).val.val =
        (t.chain.val.cell j).val) ∧
      0 < inner ℝ ((S.child r.ty i).rotation (chainVector c)) (S.σ (chainVector t))) ↔
      restrictionOp_source_step4_chains_step3_restriction ⟨r.ty, i⟩ c t := by
  let R := rolePlacement ⟨r.ty, i⟩
  have hmap (a : ℝ) (ha : R.linear (chainVector c) = a • chainVector t) :
      (S.child r.ty i).rotation (chainVector c) = a • S.σ (chainVector t) := by
    rw [← restrictionOp_source_step6_role_linear i]
    change S.σ (R.linear (chainVector c)) = _
    rw [ha, map_smul]
  constructor
  · rintro ⟨hcell, hpos⟩
    have hrel (j : FlagIndex d) :
        relint (R '' (c.chain.val.cell j).val.carrier) ⊆
          relint (t.chain.val.cell j).val.carrier := by
      obtain ⟨hs, he⟩ := hcell j
      simpa only [he] using restrictionOp_source_step6_cell_spec r i f h
        ⟨c.chain.val.cell j, hs⟩
    have hspan (j : FlagIndex d) :
        affineSpan ℝ (R '' (c.chain.val.cell j).val.carrier) =
          affineSpan ℝ (t.chain.val.cell j).val.carrier :=
      restrictionOp_source_step6_span R _ _
        ((c.chain.val.dimension j).trans (t.chain.val.dimension j).symm) (hrel j)
    have ht : (affineSpan ℝ (t.chain.val.cell edgeIndex).val.carrier).direction =
        Submodule.span ℝ {chainVector t} := by
      simpa using restrictionOp_source_step6_chain_direction t (AffineEquiv.refl ℝ (E d))
    have hdir := congrArg AffineSubspace.direction (hspan edgeIndex)
    rw [restrictionOp_source_step6_chain_direction, ht] at hdir
    have hline : R.linear (chainVector c) ∈ Submodule.span ℝ {chainVector t} := by
      rw [← hdir]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hline
    have hrot := hmap a ha.symm
    have hnonneg : 0 ≤ inner ℝ (S.σ (chainVector t)) (S.σ (chainVector t)) :=
      real_inner_self_nonneg
    rw [hrot, real_inner_smul_left] at hpos
    refine ⟨hrel, hspan, a, ?_, ha.symm⟩
    nlinarith
  · rintro ⟨hrel, _, a, ha, hca⟩
    refine ⟨?_, ?_⟩
    · intro j
      refine ⟨restrictionOp_source_step4_chains_step1_subset c j, ?_⟩
      exact congrArg (fun x : CellsInFacet r.ty r.facet => x.val.val)
        (restrictionOp_source_step6_cell_unique r i f h _
          ⟨t.chain.val.cell j, restrictionOp_source_step4_chains_step1_subset t j⟩ (hrel j))
    · have ht : chainVector t ≠ 0 := by
        change (if t.forward then edgeVector _ else -edgeVector _) ≠ 0
        split <;> simpa using (edgeVector_spec
          (restrictionOp_source_step4_chains_step1_edge t.chain.val)).1
      have hσt : S.σ (chainVector t) ≠ 0 :=
        fun he => ht (S.σ.injective (he.trans (map_zero _).symm))
      rw [hmap a hca, real_inner_smul_left]
      exact mul_pos ha (real_inner_self_pos.mpr hσt)

set_option maxHeartbeats 800000 in
/-- Step 7 of the V4 proof of `restrictionOp_source` (V4 2.3):
"a chain ... of C is active iff the chain ... of containing cells ... of B is active".
Consequently the restricted finite chain table is the actual child table. -/
private theorem restrictionOp_source_step7_chains (U : HonestSource S) (P : Params S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (F : FacetName S q.2.val.ty) (f : FacetName S (S.child q.2.val.ty i).ty)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (h : placedSet (S.child q.2.val.ty i).frame f.val.carrier ⊆ S.σ '' F.val.carrier) :
    restrictedChains (U.recordOf P q F hF) i f h =
      U.recordChains P (U.childNode q hq i) f hf := by
  classical
  have hsub := (restrictionOp_source_step6_normalize i f.val F.val).mp h
  ext c
  simp only [restrictedChains, HonestSource.recordChains, Finset.mem_filter,
    allOrientedChains, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, hct⟩
    exact restrictionOp_source_step4_chains_step4_restrict U P q hq i f F hf hF hsub
      c t (Finset.mem_filter.mp ht).2
      ((restrictionOp_source_step6_chain_lookup (U.recordOf P q F hF) i f h c t).mp hct)
  · intro hc
    obtain ⟨t, ht, hct⟩ := restrictionOp_source_step4_chains_step5_lift
      U P q hq i f F hf hF hsub c hc
    refine ⟨t, ?_, (restrictionOp_source_step6_chain_lookup (U.recordOf P q F hF) i f h c t).mpr hct⟩
    simp [HonestSource.recordOf, HonestSource.recordChains, allOrientedChains, ht]

/-- Step 7 of the V4 proof of `restrictionOp_source` (V4 2.3):
"tau_f'(s') = tau_f(t(s'))". Uniqueness identifies the finite lookup with the actual stratum. -/
private theorem restrictionOp_source_step7_tau (U : HonestSource S) (P : Params S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (F : FacetName S q.2.val.ty) (f : FacetName S (S.child q.2.val.ty i).ty)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (h : placedSet (S.child q.2.val.ty i).frame f.val.carrier ⊆ S.σ '' F.val.carrier) :
    HEq (fun e => (U.recordOf P q F hF).tau (inheritedCell (U.recordOf P q F hF) i f h e))
      (U.recordTau P (U.childNode q hq i) f hf) := by
  have hsub := (restrictionOp_source_step4_containment U q hq i f.val F.val).mpr
    ((restrictionOp_source_step6_normalize i f.val F.val).mp h)
  have hp := restrictionOp_source_step2_parent U q hq i
  obtain ⟨_, hi, _⟩ := restrictionOp_source_step4_inherited_incidence P U _ q hp f F hf hsub
  have hext {a b : P.Incidence} (hab : a = b)
      (τ : CellsInFacet (S.child q.2.val.ty i).ty f → ProviderCell a.val)
      (τ' : CellsInFacet (S.child q.2.val.ty i).ty f → ProviderCell b.val)
      (hv : ∀ e, (τ e).val.val = (τ' e).val.val) : HEq τ τ' := by
    cases hab
    apply heq_of_eq
    funext e
    exact Subtype.ext (Subtype.ext (hv e))
  apply hext hi.symm
  intro e
  obtain ⟨t, ht, hτ⟩ := restrictionOp_source_step4_inherited_tau P U _ q hp f F hf hF hsub e
  have het := restrictionOp_source_step6_cell_unique (U.recordOf P q F hF) i f h e t
    ((restrictionOp_source_step4_relint_containment U q hq i e.val.val t.val.val).mp ht)
  change (U.recordTau P q F hF _).val.val = _
  rw [het]
  exact hτ.symm

/-- Step 8 of the V4 proof of `restrictionOp_source` (V4 2.3):
"append i to the role word". The inherited provider depth and downward word increment together. -/
private theorem restrictionOp_source_step8_word (U : HonestSource S) (P : Params S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (F : FacetName S q.2.val.ty) (f : FacetName S (S.child q.2.val.ty i).ty)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (h : placedSet (S.child q.2.val.ty i).frame f.val.carrier ⊆ S.σ '' F.val.carrier) :
    U.downRoles (U.childNode q hq i) (U.hierarchy.firstProvider (U.childNode q hq i) f hf).1 =
      U.downRoles q (U.hierarchy.firstProvider q F hF).1 ++ [⟨q.2.val.ty, i⟩] := by
  have hsub := (restrictionOp_source_step4_containment U q hq i f.val F.val).mpr
    ((restrictionOp_source_step6_normalize i f.val F.val).mp h)
  rw [restrictionOp_source_step4_profile_step2_depth U _ q
    (restrictionOp_source_step2_parent U q hq i) f F hf hF hsub,
    restrictionOp_source_step4_profile_step1_downRoles,
    restrictionOp_source_step2_parent, restrictionOp_source_step2_role]

/-- Step 8 of the V4 proof of `restrictionOp_source` (V4 2.3):
"constants ... and the site statuses of their endpoints" determine a mature profile. -/
private theorem restrictionOp_source_step8_constant_ext {P : Params S} {A : S.ι}
    {C D : ConstantProfile P A} (hv : ∀ e, C.value e = D.value e)
    (hs : ∀ v, C.endpointSite v = D.endpointSite v) : C = D := by
  cases C
  cases D
  congr
  · exact funext hv
  · exact funext hs

set_option maxHeartbeats 800000 in
/-- Step 8 of the V4 proof of `restrictionOp_source` (V4 2.3):
"append i and compute from the finite lookup the constants ... and the site statuses".
The appended word computes the actual geometric constants. -/
private theorem restrictionOp_source_step8_wordConstants (U : HonestSource S) (P : Params S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (F : FacetName S q.2.val.ty) (f : FacetName S (S.child q.2.val.ty i).ty)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (h : placedSet (S.child q.2.val.ty i).frame f.val.carrier ⊆ S.σ '' F.val.carrier) :
    wordConstants (U.recordOf P q F hF) i f (restrictedChains (U.recordOf P q F hF) i f h)
      (U.downRoles q (U.hierarchy.firstProvider q F hF).1 ++ [⟨q.2.val.ty, i⟩]) =
      U.constantProfile P (U.childNode q hq i) f hf := by
  classical
  let c := U.childNode q hq i
  have hp := restrictionOp_source_step2_parent U q hq i
  have hsub := (restrictionOp_source_step4_containment U q hq i f.val F.val).mpr
    ((restrictionOp_source_step6_normalize i f.val F.val).mp h)
  obtain ⟨_, hi, hs⟩ := restrictionOp_source_step4_inherited_incidence P U c q hp f F hf hsub
  have hdir : (U.recordOf P c f hf).servingDirection = (U.recordOf P q F hF).servingDirection :=
    congrArg₂ (fun (j : P.Incidence) (b : Bool) =>
      (S.child j.val.ty (j.val.sideIndex b)).rotation.symm
        ((S.child j.val.ty j.val.left).rotation (P.flag j).direction)) hi hs
  dsimp only [c] at hi hs hdir
  have hw := restrictionOp_source_step8_word U P q hq i F f hF hf h
  rw [restrictionOp_source_step7_chains U P q hq i F f hF hf h]
  apply restrictionOp_source_step8_constant_ext
  · intro e
    change (if _ then some _ else none) = (if _ then some _ else none)
    by_cases he : ∃ z ∈ U.recordChains P c f hf, (z.chain.val.cell edgeIndex).val = e.val
    · rw [if_pos he, if_pos he]
      congr 1
      apply Fin.ext
      have hv := restrictionOp_source_step4_profile_step5_word_count P U c f hf e he
      simpa only [c, hi, hs, hdir, hw] using hv.symm
    · rw [if_neg he, if_neg he]
  · intro v
    change (if _ then some _ else none) = (if _ then some _ else none)
    by_cases hv : ∃ z ∈ U.recordChains P c f hf,
        vertexPoint v ∈ (z.chain.val.cell edgeIndex).val.carrier
    · rw [if_pos hv, if_pos hv]
      congr 1
      apply List.any_congr rfl
      intro a
      simp only [restrictionOp_source_step4_profile_step4_site_coordinates, hi, hs, hw]
      rfl
    · rw [if_neg hv, if_neg hv]

/-- Step 8 of the V4 proof of `restrictionOp_source` (V4 2.3):
"every chain-active edge of C lies in a chain-active edge of B".
Take the edge of the lifted full chain. -/
private theorem restrictionOp_source_step8_parent_edge (U : HonestSource S) (P : Params S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (F : FacetName S q.2.val.ty) (f : FacetName S (S.child q.2.val.ty i).ty)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (h : placedSet (S.child q.2.val.ty i).frame f.val.carrier ⊆ S.σ '' F.val.carrier)
    (e : CellName S (S.child q.2.val.ty i).ty)
    (he : (U.recordOf P (U.childNode q hq i) f hf).ChainActive e) :
    ∃ E : CellName S q.2.val.ty, (U.recordOf P q F hF).ChainActive E ∧
      relint (rolePlacement ⟨q.2.val.ty, i⟩ '' e.val.carrier) ⊆ relint E.val.carrier := by
  classical
  obtain ⟨z, hz, hze⟩ := he
  obtain ⟨t, ht, hct⟩ := restrictionOp_source_step4_chains_step5_lift U P q hq i f F hf hF
    ((restrictionOp_source_step6_normalize i f.val F.val).mp h) z (Finset.mem_filter.mp hz).2
  refine ⟨t.chain.val.cell edgeIndex, ⟨t, ?_, rfl⟩, ?_⟩
  · simp [HonestSource.recordOf, HonestSource.recordChains, allOrientedChains, ht]
  · simpa only [hze] using hct.1 edgeIndex

/-- Step 8 of the V4 proof of `restrictionOp_source` (V4 2.3):
"if v' is a vertex v of B". The geometric point uniquely identifies its listed vertex. -/
private theorem restrictionOp_source_step8_vertex_unique {A : S.ι} (v w : VertexName S A)
    (h : vertexPoint v = vertexPoint w) : v = w := by
  apply Subtype.ext
  apply restrictionOp_source_step4_cell_eq
  rw [vertexPoint_spec, vertexPoint_spec, h]

set_option maxHeartbeats 800000 in
/-- Step 8 of the V4 proof of `restrictionOp_source` (V4 2.3):
"each chain-active edge ... inherits kappa" and "the site status ... is inherited
if v' is a vertex of B ... and is not a site otherwise". These are exactly the
two fields of the mature lookup. -/
private theorem restrictionOp_source_step8_inheritedConstants (U : HonestSource S) (P : Params S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (F : FacetName S q.2.val.ty) (f : FacetName S (S.child q.2.val.ty i).ty)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (h : placedSet (S.child q.2.val.ty i).frame f.val.carrier ⊆ S.σ '' F.val.carrier)
    (hm : P.siteDepth (U.recordIncidence P q F hF) (U.recordSide P q F hF) ≤
      (U.hierarchy.firstProvider q F hF).1) :
    inheritedConstants (U.recordOf P q F hF) i f h (U.constantProfile P q F hF) =
      U.constantProfile P (U.childNode q hq i) f hf := by
  classical
  let c := U.childNode q hq i
  have hsub := (restrictionOp_source_step6_normalize i f.val F.val).mp h
  have hsub' := (restrictionOp_source_step4_containment U q hq i f.val F.val).mpr hsub
  have hchains := restrictionOp_source_step7_chains U P q hq i F f hF hf h
  have hframe : c.2.val.prototypeFrame c.1 =
      (rolePlacement ⟨q.2.val.ty, i⟩).trans (q.2.val.prototypeFrame q.1) := by
    change (q.2.val.child (q.1-1) i).prototypeFrame (q.1-1) = _
    rw [restrictionOp_source_step1_frame, Nat.sub_add_cancel hq]
  apply restrictionOp_source_step8_constant_ext
  · intro e
    change (if _ then (if hs : e.val.carrier ⊆ f.val.carrier then
      (U.constantProfile P q F hF).value (inheritedCell (U.recordOf P q F hF) i f h ⟨e, hs⟩).val
      else none) else none) = _
    rw [hchains]
    by_cases he : ∃ z ∈ U.recordChains P c f hf, (z.chain.val.cell edgeIndex).val = e.val
    · have hesub : e.val.carrier ⊆ f.val.carrier := by
        obtain ⟨z, _, hze⟩ := he
        rw [← hze]
        exact restrictionOp_source_step4_chains_step1_subset z edgeIndex
      obtain ⟨E, hE, heE⟩ := restrictionOp_source_step8_parent_edge U P q hq i F f hF hf h e he
      have hEsub : E.val.carrier ⊆ F.val.carrier := by
        obtain ⟨z, _, hzE⟩ := hE
        rw [← hzE]
        exact restrictionOp_source_step4_chains_step1_subset z edgeIndex
      have hlookup := congrArg Subtype.val
        (restrictionOp_source_step6_cell_unique (U.recordOf P q F hF) i f h
          ⟨e, hesub⟩ ⟨E, hEsub⟩ heE)
      rw [if_pos he, dif_pos hesub, hlookup]
      exact (restrictionOp_source_step4_profile_step17_inherited_value P U q hq i f F
        hf hF hsub hm e E he hE heE).symm
    · dsimp only [c] at he
      simp only [HonestSource.constantProfile, if_neg he]
  · intro v
    change (if _ then some (if hv : ∃ w : VertexName S q.2.val.ty,
        S.σ (vertexPoint w) = (S.child q.2.val.ty i).frame (vertexPoint v) then
        ((U.constantProfile P q F hF).endpointSite (Classical.choose hv)).getD false else false)
      else none) = _
    rw [hchains]
    change (if _ then some _ else none) = (if _ then some _ else none)
    by_cases hv : ∃ z ∈ U.recordChains P c f hf,
        vertexPoint v ∈ (z.chain.val.cell edgeIndex).val.carrier
    · rw [if_pos hv, if_pos hv]
      apply congrArg some
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, Finset.mem_toList, Finset.mem_univ, true_and, decide_eq_true_eq]
      obtain ⟨z, hz, hvz⟩ := hv
      let e := z.chain.val.cell edgeIndex
      have he : (U.recordOf P c f hf).ChainActive e := ⟨z, hz, rfl⟩
      obtain ⟨E, hE, heE⟩ := restrictionOp_source_step8_parent_edge U P q hq i F f hF hf h e he
      have hclosed : c.2.val.cell c.1 e.val ⊆ q.2.val.cell q.1 E.val := by
        have hc := closure_mono
          ((restrictionOp_source_step4_relint_containment U q hq i e.val E.val).mpr heE)
        simpa only [restrictionOp_source_step5_cell_closure] using hc
      have hx : c.2.val.prototypeFrame c.1 (vertexPoint v) ∈ q.2.val.cell q.1 E.val :=
        hclosed (Set.mem_image_of_mem _ hvz)
      have hsites := (restrictionOp_source_step4_profile_step9_inherited_sites P U c q
        (restrictionOp_source_step2_parent U q hq i) f F hf hF hsub').1
      change (if hv : ∃ w : VertexName S q.2.val.ty,
          S.σ (vertexPoint w) = (S.child q.2.val.ty i).frame (vertexPoint v) then
          ((U.constantProfile P q F hF).endpointSite (Classical.choose hv)).getD false else false) = true ↔
        ∃ a, U.sitePoint P c f hf a = c.2.val.prototypeFrame c.1 (vertexPoint v)
      simp only [hsites]
      rw [restrictionOp_source_step4_profile_step18_endpoint_lookup P U q F hF hm E hE _ hx]
      have hposition (w : VertexName S q.2.val.ty) :
          q.2.val.prototypeFrame q.1 (vertexPoint w) = c.2.val.prototypeFrame c.1 (vertexPoint v) ↔
            S.σ (vertexPoint w) = (S.child q.2.val.ty i).frame (vertexPoint v) := by
        rw [hframe]
        change q.2.val.prototypeFrame q.1 (vertexPoint w) =
          q.2.val.prototypeFrame q.1 (S.σ.symm ((S.child q.2.val.ty i).frame (vertexPoint v))) ↔ _
        rw [(q.2.val.prototypeFrame q.1).injective.eq_iff]
        constructor
        · intro he
          rw [he, S.σ.apply_symm_apply]
        · intro he
          exact S.σ.injective (he.trans (S.σ.apply_symm_apply _).symm)
      simp only [hposition]
      have hget (o : Option Bool) : o.getD false = true ↔ o = some true := by
        cases o <;> simp
      by_cases hw : ∃ w : VertexName S q.2.val.ty,
          S.σ (vertexPoint w) = (S.child q.2.val.ty i).frame (vertexPoint v)
      · rw [dif_pos hw, hget]
        constructor
        · intro hs
          exact ⟨Classical.choose hw, Classical.choose_spec hw, hs⟩
        · rintro ⟨w, hw', hs⟩
          have he : Classical.choose hw = w := restrictionOp_source_step8_vertex_unique _ _
            (S.σ.injective ((Classical.choose_spec hw).trans hw'.symm))
          simpa only [he] using hs
      · rw [dif_neg hw]
        simp only [Bool.false_eq_true, false_iff]
        rintro ⟨w, hw', _⟩
        exact hw ⟨w, hw'⟩
    · rw [if_neg hv, if_neg hv]

set_option maxHeartbeats 800000 in
/-- Step 9 of the V4 proof of `restrictionOp_source` (V4 2.3):
"if a+1 < r ...; if a+1 >= r ...; if the profile already consists of constants".
The depth test selects the actual child branch in all three cases. -/
private theorem restrictionOp_source_step9_counter (U : HonestSource S) (P : Params S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (F : FacetName S q.2.val.ty) (f : FacetName S (S.child q.2.val.ty i).ty)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (h : placedSet (S.child q.2.val.ty i).frame f.val.carrier ⊆ S.σ '' F.val.carrier) :
    restrictedCounter (U.recordOf P q F hF) i f h = U.counterProfile P (U.childNode q hq i) f hf := by
  classical
  have hp := restrictionOp_source_step2_parent U q hq i
  have hsub := (restrictionOp_source_step4_containment U q hq i f.val F.val).mpr
    ((restrictionOp_source_step6_normalize i f.val F.val).mp h)
  obtain ⟨_, hi, hs⟩ := restrictionOp_source_step4_inherited_incidence P U _ q hp f F hf hsub
  have hd := restrictionOp_source_step4_profile_step2_depth U _ q hp f F hf hF hsub
  have hw := restrictionOp_source_step8_word U P q hq i F f hF hf h
  have hlen : (U.downRoles q (U.hierarchy.firstProvider q F hF).1 ++ [(⟨q.2.val.ty, i⟩ : S.Role)]).length =
      (U.hierarchy.firstProvider q F hF).1 + 1 := by
    simp [HonestSource.downRoles]
  by_cases ha : (U.hierarchy.firstProvider q F hF).1 <
      P.siteDepth (U.recordIncidence P q F hF) (U.recordSide P q F hF)
  · simp only [restrictedCounter, HonestSource.recordOf, HonestSource.counterProfile,
      dif_pos ha, hi, hs, hd]
    by_cases hb : (U.hierarchy.firstProvider q F hF).1 + 1 <
        P.siteDepth (U.recordIncidence P q F hF) (U.recordSide P q F hF)
    · simp only [hlen, dif_pos hb]
      congr 1
      congr 1
      simpa only [hd] using hw.symm
    · simp only [hlen, dif_neg hb]
      congr 1
      exact restrictionOp_source_step8_wordConstants U P q hq i F f hF hf h
  · have hb : ¬ (U.hierarchy.firstProvider q F hF).1 + 1 <
        P.siteDepth (U.recordIncidence P q F hF) (U.recordSide P q F hF) := by omega
    simp only [restrictedCounter, HonestSource.recordOf, HonestSource.counterProfile,
      dif_neg ha, hi, hs, hd, dif_neg hb]
    congr 1
    exact restrictionOp_source_step8_inheritedConstants U P q hq i F f hF hf h (not_lt.mp ha)

/-- Step 10 of the V4 proof of `restrictionOp_source` (V4 2.3):
"same iota, side, beta and provider; age min(age+1,C); tau ...; active chains ...; profile".
The fieldwise inherited computations assemble into the actual child record. -/
private theorem restrictionOp_source_step10_record (U : HonestSource S) (P : Params S)
    (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (F : FacetName S q.2.val.ty) (f : FacetName S (S.child q.2.val.ty i).ty)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (h : placedSet (S.child q.2.val.ty i).frame f.val.carrier ⊆ S.σ '' F.val.carrier) :
    restrictOne (U.recordOf P q F hF) i f h = U.recordOf P (U.childNode q hq i) f hf := by
  have hp := restrictionOp_source_step2_parent U q hq i
  have hsub := (restrictionOp_source_step4_containment U q hq i f.val F.val).mpr
    ((restrictionOp_source_step6_normalize i f.val F.val).mp h)
  obtain ⟨_, hi, hs⟩ := restrictionOp_source_step4_inherited_incidence P U _ q hp f F hf hsub
  obtain ⟨_, ha, hb⟩ := restrictionOp_source_step4_inherited_numbers U _ q hp f F hf hsub
  apply restrictionOp_source_step4_record_ext
    (r := restrictOne (U.recordOf P q F hF) i f h)
    (t := U.recordOf P (U.childNode q hq i) f hf) rfl rfl hi.symm hs.symm
  · apply Fin.ext
    change min (min (U.hierarchy.age q F hF) P.C + 1) P.C =
      min (U.hierarchy.age (U.childNode q hq i) f hf) P.C
    rw [ha]
    omega
  · apply Fin.ext
    exact congrArg (· % P.L) hb.symm
  · exact restrictionOp_source_step7_tau U P q hq i F f hF hf h
  · exact heq_of_eq (restrictionOp_source_step7_chains U P q hq i F f hF hf h)
  · exact heq_of_eq (restrictionOp_source_step9_counter U P q hq i F f hF hf h)

/-- Step 11 of the V4 proof of `restrictionOp_source` (V4 2.3):
"which case occurs, and f, depend only on (A,i,f')". On matching named facets,
the totalized restriction chooses precisely the prescribed inherited step. -/
private theorem restrictionOp_source_step11_apply {P : Params S} (a : RestrictionStep S)
    (r : FacetRecord P) (i : S.I r.ty) (f : FacetName S (S.child r.ty i).ty)
    (h : placedSet (S.child r.ty i).frame f.val.carrier ⊆ S.σ '' r.facet.val.carrier)
    (hr : (⟨r.ty, i⟩ : S.Role) = a.role) (hs : r.facet.val = a.source.val)
    (ht : f.val = a.target.val) : a.apply r = restrictOne r i f h := by
  classical
  have hm : ∃ (j : S.I r.ty) (g : FacetName S (S.child r.ty j).ty),
      (⟨r.ty, j⟩ : S.Role) = a.role ∧ r.facet.val = a.source.val ∧
        g.val = a.target.val ∧
        placedSet (S.child r.ty j).frame g.val.carrier ⊆ S.σ '' r.facet.val.carrier :=
    ⟨i, f, hr, hs, ht, h⟩
  have hu (j : S.I r.ty) (g : FacetName S (S.child r.ty j).ty)
      (hj : (⟨r.ty, j⟩ : S.Role) = a.role) (hg : g.val = a.target.val)
      (hsub : placedSet (S.child r.ty j).frame g.val.carrier ⊆ S.σ '' r.facet.val.carrier) :
      restrictOne r j g hsub = restrictOne r i f h := by
    have hji : j = i := eq_of_heq (Sigma.mk.inj (hj.trans hr.symm)).2
    subst j
    have hgf : g = f := Subtype.ext (hg.trans ht.symm)
    subst g
    rfl
  rw [RestrictionStep.apply, dif_pos hm]
  exact hu _ _ (Classical.choose_spec (Classical.choose_spec hm)).1
    (Classical.choose_spec (Classical.choose_spec hm)).2.2.1 _

/-- Step 11 of the V4 proof of `restrictionOp_source` (V4 2.3):
"every child C of B of role i". The actual node is its parent's prescribed child. -/
private theorem restrictionOp_source_step11_actual_child (U : HonestSource S) (c : U.Node) :
    U.childNode (U.hierarchy.parentNode c) (by simp [CoherentHierarchy.parentNode])
      (U.hierarchy.role c.1 c.2) = c := by
  rcases c with ⟨n, N, hN⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact (U.hierarchy.child_eq n ⟨N, hN⟩).symm

/-- Step 11 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the facet f' of C". Equal nodes and facet names have the same fault status. -/
private theorem restrictionOp_source_step11_fault_congr (U : HonestSource S)
    (q t : U.Node) (hqt : q = t) (F : FacetName S q.2.val.ty)
    (f : FacetName S t.2.val.ty) (hFf : F.val = f.val) :
    U.hierarchy.IsFault q F ↔ U.hierarchy.IsFault t f := by
  cases hqt
  cases Subtype.ext hFf
  rfl

/-- Step 11 of the V4 proof of `restrictionOp_source` (V4 2.3):
"the facet f' of C". Equal nodes and facet names have the same computed record. -/
private theorem restrictionOp_source_step11_record_congr (U : HonestSource S) (P : Params S)
    (q t : U.Node) (hqt : q = t) (F : FacetName S q.2.val.ty)
    (f : FacetName S t.2.val.ty) (hFf : F.val = f.val)
    (hF : ¬ U.hierarchy.IsFault q F) (hf : ¬ U.hierarchy.IsFault t f) :
    U.recordOf P q F hF = U.recordOf P t f hf := by
  cases hqt
  cases Subtype.ext hFf
  rfl

set_option maxHeartbeats 800000 in
/-- Step 11 of the V4 proof of `restrictionOp_source` (V4 2.3):
"inherited case". A named actual role step pulls a finite child record back to
a finite parent facet, and its annotation gives that child record. -/
private theorem restrictionOp_source_step11_actual (U : HonestSource S) (P : Params S)
    (c : U.Node) (a : RestrictionStep S) (hr : a.role = U.hierarchy.nodeRole c)
    (F : FacetName S (U.hierarchy.parentNode c).2.val.ty) (f : FacetName S c.2.val.ty)
    (hs : F.val = a.source.val) (ht : f.val = a.target.val)
    (hf : ¬ U.hierarchy.IsFault c f) :
    ∃ hF : ¬ U.hierarchy.IsFault (U.hierarchy.parentNode c) F,
      a.apply (U.recordOf P (U.hierarchy.parentNode c) F hF) = U.recordOf P c f hf := by
  rcases a with ⟨role, source, target, inherited⟩
  change role = U.hierarchy.nodeRole c at hr
  subst role
  let q := U.hierarchy.parentNode c
  have hq : 1 ≤ q.1 := by simp [q, CoherentHierarchy.parentNode]
  let i : S.I q.2.val.ty := U.hierarchy.role c.1 c.2
  have hc : U.childNode q hq i = c := restrictionOp_source_step11_actual_child U c
  have hty : (S.child q.2.val.ty i).ty = c.2.val.ty := congrArg (fun x : U.Node => x.2.val.ty) hc
  let g : FacetName S (S.child q.2.val.ty i).ty := ⟨f.val, hty.symm ▸ f.property⟩
  have hg : ¬ U.hierarchy.IsFault (U.childNode q hq i) g :=
    fun hgf => hf ((restrictionOp_source_step11_fault_congr U _ c hc g f rfl).mp hgf)
  have h : placedSet (S.child q.2.val.ty i).frame g.val.carrier ⊆ S.σ '' F.val.carrier := by
    change placedSet (S.child q.2.val.ty i).frame f.val.carrier ⊆ S.σ '' F.val.carrier
    change F.val = source.val at hs
    change f.val = target.val at ht
    rw [hs, ht]
    exact inherited
  have hsub := (restrictionOp_source_step4_containment U q hq i g.val F.val).mpr
    ((restrictionOp_source_step6_normalize i g.val F.val).mp h)
  change (U.childNode q hq i).2.val.cell (U.childNode q hq i).1 f.val ⊆ q.2.val.cell q.1 F.val at hsub
  rw [hc] at hsub
  have hF : ¬ U.hierarchy.IsFault q F :=
    fun hfault => hf (U.hierarchy.restriction_det_fault c F f hfault hsub)
  refine ⟨hF, ?_⟩
  calc
    _ = restrictOne (U.recordOf P q F hF) i g h :=
      restrictionOp_source_step11_apply _ (U.recordOf P q F hF) i g h rfl hs ht
    _ = U.recordOf P (U.childNode q hq i) g hg :=
      restrictionOp_source_step10_record U P q hq i F g hF hg h
    _ = U.recordOf P c f hf := restrictionOp_source_step11_record_congr U P _ c hc g f rfl hg hf

set_option maxHeartbeats 800000 in
/-- Q13, V4 §2.5: annotation agrees with the actual inherited record whenever finite.
This is V4 2.3's inherited case iterated along the explicit source role path. -/
theorem restrictionOp_source (U : HonestSource S) (P : Params S) (B t : U.Node)
    (F : FacetName S B.2.val.ty) (f : FacetName S t.2.val.ty)
    (hF : ¬ U.hierarchy.IsFault B F) (hf : ¬ U.hierarchy.IsFault t f)
    (path : List (RestrictionStep S)) (hp : SourceRestrictionPath U B t F f path) :
    restrictionOp path (U.recordOf P B F hF) = U.recordOf P t f hf := by
  induction path using List.reverseRecOn generalizing B t with
  | nil =>
    have hh := hp.2.2.2.2.1
    simp at hh
  | append_singleton path a ih =>
    obtain ⟨hlt, hanc, hlen, hroles, hhead, hlast, hchain⟩ := hp
    have hn : B.1 - t.1 = path.length + 1 := by simpa using hlen.symm
    rw [hn] at hanc hroles
    simp only [List.map_append, List.map_cons, List.map_nil,
      restrictionOp_source_step4_profile_step1_downRoles] at hroles
    have hr : a.role = U.hierarchy.nodeRole t := by
      have hh := congrArg List.getLast? hroles
      simpa using hh
    have hprefix : path.map RestrictionStep.role = U.downRoles (U.hierarchy.parentNode t) path.length := by
      rw [hr] at hroles
      exact (List.append_left_inj _).mp hroles
    have hanc' : U.hierarchy.ancestor (U.hierarchy.parentNode t) path.length = B := by
      simpa only [CoherentHierarchy.ancestor, Function.iterate_succ_apply] using hanc
    have hty : a.role.1 = (U.hierarchy.parentNode t).2.val.ty := congrArg Sigma.fst hr
    let G : FacetName S (U.hierarchy.parentNode t).2.val.ty :=
      ⟨a.source.val, hty ▸ a.source.property⟩
    have ht : f.val = a.target.val := by
      simpa using hlast.symm
    obtain ⟨hG, hop⟩ := restrictionOp_source_step11_actual U P t a hr G f rfl ht hf
    by_cases hnil : path = []
    · subst path
      have hB : U.hierarchy.parentNode t = B := by
        simpa only [CoherentHierarchy.ancestor, Function.iterate_zero, id_eq] using hanc'
      have hFG : F.val = G.val := by simpa using hhead.symm
      have hrec := restrictionOp_source_step11_record_congr U P B (U.hierarchy.parentNode t)
        hB.symm F G hFG hF hG
      simpa only [List.nil_append, restrictionOp, hrec] using hop
    · have hpos : 0 < path.length := List.length_pos_iff.mpr hnil
      have hheight : (U.hierarchy.parentNode t).1 = t.1 + 1 := rfl
      have hlt' : (U.hierarchy.parentNode t).1 < B.1 := by omega
      have hlen' : path.length = B.1 - (U.hierarchy.parentNode t).1 := by omega
      have hlast' : path.getLast?.map (fun b => b.target.val) = some G.val := by
        rw [List.getLast?_eq_some_getLast hnil, Option.map_some]
        apply congrArg some
        exact ((List.isChain_append.mp hchain).2.2 (path.getLast hnil)
          (by simp [List.getLast?_eq_some_getLast hnil]) a (by simp)).2
      have hpath : SourceRestrictionPath U B (U.hierarchy.parentNode t) F G path := by
        refine ⟨hlt', ?_, hlen', ?_, ?_, hlast', (List.isChain_append.mp hchain).1⟩
        · simpa only [← hlen'] using hanc'
        · simpa only [← hlen'] using hprefix
        · simpa only [List.head?_append_of_ne_nil _ hnil] using hhead
      rw [restrictionOp_append, ih B (U.hierarchy.parentNode t) F G hF hG hpath]
      exact hop

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

/-- Step 1 of the V4 proof of `endGeometry_exists` (V4 1.6): "the ancestors `P_{b+j}`".
An ancestor after `r` parent steps has height increased by exactly `r`. -/
private theorem endGeometry_exists_step1_ancestor_height (U : HonestSource S) (q : U.Node)
    (r : ℕ) : (U.hierarchy.ancestor q r).1 = q.1 + r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [CoherentHierarchy.ancestor, Function.iterate_succ_apply']
    change (U.hierarchy.ancestor q r).1 + 1 = q.1 + (r + 1)
    omega

open private states_finite_step6_vertex_mem from Enforce.State.State in
/-- Step 1 of the V4 proof of `endGeometry_exists` (V4 §2.5, 1.6): "the complete P-owned star
at the event point". The distinguished tile itself is a native B-owned tile at that point. -/
private theorem endGeometry_exists_step1_central (U : HonestSource S) (t : U.Node)
    (ht : t.1 = 0) (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) :
    t ∈ ownedStarSet U (U.hierarchy.birthParent t f hf)
      (t.2.val.prototypeFrame t.1 (vertexPoint v)) := by
  have hB : U.hierarchy.birthParent t f hf =
      U.hierarchy.ancestor t ((U.hierarchy.firstProvider t f hf).1 + 1) := by
    simp only [CoherentHierarchy.birthParent, CoherentHierarchy.servingChild,
      CoherentHierarchy.ancestor, Function.iterate_succ_apply']
  have hh : (U.hierarchy.birthParent t f hf).1 = (U.hierarchy.firstProvider t f hf).1 + 1 := by
    rw [hB, endGeometry_exists_step1_ancestor_height, ht, zero_add]
  refine ⟨ht, ?_, ?_⟩
  · rw [hh]
    exact hB.symm
  · have hcar : t.2.val.carrier t.1 =
        t.2.val.prototypeFrame t.1 '' (S.proto t.2.val.ty).carrier := by
      rw [FramedNode.carrier, placedSet, SubstSystem.supertile, Set.image_image]
      rfl
    rw [hcar]
    exact Set.mem_image_of_mem _ (states_finite_step6_vertex_mem _ v)

/-- Step 2 of the V4 proof of `endGeometry_exists` (V4 1.5(b)--(c)):
"every child C of B". A node with parent `B` is a prescribed child of `B`. -/
private theorem endGeometry_exists_step2_child (U : HonestSource S) (C B : U.Node)
    (h : U.hierarchy.parentNode C = B) :
    B.1 = C.1 + 1 ∧ ∃ j : S.I B.2.val.ty, C.2.val = B.2.val.child C.1 j := by
  subst h
  exact ⟨rfl, U.hierarchy.role C.1 C.2, U.hierarchy.child_eq C.1 C.2⟩

/-- Step 2 of the V4 proof of `endGeometry_exists` (V4 2.2): "after rescaling by the frame
of P". Membership in a composed affine image is membership of the pulled-back point. -/
private theorem endGeometry_exists_step2_mem (g e : E d ≃ᵃ[ℝ] E d) (K : Set (E d))
    (y : E d) : y ∈ (g.trans e) '' K ↔ e.symm y ∈ g '' K := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, by simp⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨z, hz, by rw [AffineEquiv.trans_apply, hzy, AffineEquiv.apply_symm_apply]⟩

open private states_finite_step3_child states_finite_step5_birthFrame
  states_finite_step5_child_frame from Enforce.State.State in
/-- Step 2 of the V4 proof of `endGeometry_exists` (V4 2.2, 1.5(c)): "B is a native tile of
sigma^(b-1) Pi", in the birth frame. Listedness and carriers of the actual children of the
birth parent are those of the prototype first-generation patch, pulled back by the birth frame. -/
private theorem endGeometry_exists_step2_transfer (N : FramedNode S) (b m : ℕ)
    (hb : b = m + 1) (j : S.I N.ty) (y : E d) :
    ((N.child m j).Lists m y ↔ (states_finite_step3_child N.ty j).Lists 0
      ((states_finite_step5_birthFrame N b).symm y)) ∧
    (y ∈ (N.child m j).carrier m ↔ (states_finite_step5_birthFrame N b).symm y ∈
      (states_finite_step3_child N.ty j).carrier 0) := by
  subst hb
  have hpf : (N.child m j).prototypeFrame m =
      (S.child N.ty j).frame.toAffineEquiv.trans (states_finite_step5_birthFrame N (m + 1)) := by
    rw [states_finite_step5_child_frame]
    rfl
  have hpf0 : (states_finite_step3_child N.ty j).prototypeFrame 0 =
      (S.child N.ty j).frame.toAffineEquiv := by
    apply AffineEquiv.ext
    intro z
    change (S.child N.ty j).frame ((S.σ ^ 0) z) = (S.child N.ty j).frame z
    rw [pow_zero]
    rfl
  have hcar (M : FramedNode S) (n : ℕ) :
      M.carrier n = M.prototypeFrame n '' (S.proto M.ty).carrier := by
    rw [FramedNode.carrier, placedSet, SubstSystem.supertile, Set.image_image]
    rfl
  have hmem (K : Set (E d)) : y ∈ (N.child m j).prototypeFrame m '' K ↔
      (states_finite_step5_birthFrame N (m + 1)).symm y ∈
        (states_finite_step3_child N.ty j).prototypeFrame 0 '' K := by
    rw [hpf, hpf0]
    exact endGeometry_exists_step2_mem _ _ K y
  refine ⟨⟨fun ⟨c, hc, hy⟩ => ⟨c, hc, (hmem _).mp hy⟩,
    fun ⟨c, hc, hy⟩ => ⟨c, hc, (hmem _).mpr hy⟩⟩, ?_⟩
  rw [hcar, hcar]
  exact hmem _

open private states_finite_step6_provider_anchor states_finite_step3_patch
  states_finite_step3_child states_finite_step3_point states_finite_step5_birthFrame
  from Enforce.State.State in
open private birth_ascent_routing_step3_desc_subset from Enforce.Source.Routing in
/-- Step 2 of the V4 proof of `endGeometry_exists` (V4 1.5(b)--(c), 2.2): "p is common-listed".
The provider-zero vertex is common-listed in the immediate subdivision of the birth parent
(1.5(c)), and listedness passes to every containing descendant (1.5(b)); hence every tile
of the complete owned star lists the event point. -/
private theorem endGeometry_exists_step2_listed (U : HonestSource S) (P : Params S)
    (t : U.Node) (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (hv : v.val.carrier ⊆ f.val.carrier)
    (hz : (U.recordTau P t f hf ⟨vertexCell v, hv⟩).val.val.dim = 0) (q : U.Node)
    (hq : q ∈ ownedStarSet U (U.hierarchy.birthParent t f hf)
      (t.2.val.prototypeFrame t.1 (vertexPoint v))) :
    q.2.val.Lists q.1 (t.2.val.prototypeFrame t.1 (vertexPoint v)) := by
  classical
  have hb : 1 ≤ (U.hierarchy.birthParent t f hf).1 := by
    dsimp [CoherentHierarchy.birthParent, CoherentHierarchy.parentNode]
    omega
  obtain ⟨a, ha1, hap, hcl⟩ := states_finite_step6_provider_anchor P U t f hf v hv hz
  obtain ⟨_, hanc, hxq⟩ := hq
  rw [hap] at hcl
  generalize hBdef : U.hierarchy.birthParent t f hf = B at hb ha1 hcl hanc
  generalize hxdef : t.2.val.prototypeFrame t.1 (vertexPoint v) = x at hcl hxq ⊢
  rw [ha1] at hcl
  have hpar : U.hierarchy.parentNode (U.hierarchy.ancestor q (B.1 - 1)) = B := by
    have h1 : U.hierarchy.ancestor q (B.1 - 1 + 1) =
        U.hierarchy.parentNode (U.hierarchy.ancestor q (B.1 - 1)) :=
      Function.iterate_succ_apply' _ _ _
    rw [← h1, Nat.sub_add_cancel hb, hanc]
  have hdesc := U.hierarchy.ancestor_descendant q (B.1 - 1)
  generalize U.hierarchy.ancestor q (B.1 - 1) = C at hpar hdesc
  obtain ⟨hBC, j, hj⟩ := endGeometry_exists_step2_child U C B hpar
  rw [hj] at hdesc
  have hxC : x ∈ (B.2.val.child C.1 j).carrier C.1 :=
    birth_ascent_routing_step3_desc_subset _ _ _ _ hdesc hxq
  have htr := endGeometry_exists_step2_transfer B.2.val B.1 C.1 hBC j x
  have hl : (B.2.val.child C.1 j).Lists C.1 x :=
    htr.1.mpr (hcl _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩) (htr.2.mp hxC))
  exact commonListed_inherited _ _ _ _ hdesc x hl hxq

/-- Step 2 of the V4 proof of `endGeometry_exists` (V4 §2.5): "in the central frame".
Moving a height-zero tile listing the event point to the central frame lists its prototype point. -/
private theorem endGeometry_exists_step2_move_lists (q t : FramedNode S) (k m : ℕ)
    (hk : k = 0) (hm : m = 0) (vt : VertexName S t.ty)
    (h : q.Lists k (t.prototypeFrame m (vertexPoint vt))) :
    (q.move t.frame.symm).Lists 0 (vertexPoint vt) := by
  subst hk hm
  have h0 (z : E d) : (S.σ ^ 0) z = z := by rw [pow_zero]; rfl
  obtain ⟨c, hc, z, hz, hzx⟩ := h
  refine ⟨c, hc, z, hz, ?_⟩
  change t.frame.symm (q.frame ((S.σ ^ 0) z)) = vertexPoint vt
  change q.frame ((S.σ ^ 0) z) = t.frame ((S.σ ^ 0) (vertexPoint vt)) at hzx
  rw [hzx, h0]
  exact t.frame.symm_apply_apply _

/-- Step 4 of the V4 proof of `endGeometry_exists` (V4 2.2, (S6)): "the vertex p".
A listed vertex point depends only on the underlying cell. -/
private theorem endGeometry_exists_step4_vertexPoint_congr {A B : S.ι} (v : VertexName S A)
    (w : VertexName S B) (h : v.val = w.val) : vertexPoint v = vertexPoint w := by
  have h1 := vertexPoint_spec v
  have h2 := vertexPoint_spec w
  rw [h, h2] at h1
  exact (Set.singleton_eq_singleton_iff.mp h1).symm

/-- Step 4 of the V4 proof of `endGeometry_exists` (V4 §2.5): "anchored at the event point".
A port of a moved star tile at the same physical vertex is anchored at the central vertex. -/
private theorem endGeometry_exists_step4_anchor (q t N : FramedNode S) (k m : ℕ)
    (hk : k = 0) (hm : m = 0) (vt : VertexName S t.ty) (w : VertexName S q.ty)
    (w' : VertexName S N.ty) (hN : N = q.move t.frame.symm) (hw : w'.val = w.val)
    (hx : t.prototypeFrame m (vertexPoint vt) = q.prototypeFrame k (vertexPoint w)) :
    N.frame (vertexPoint w') = vertexPoint vt := by
  subst hk hm hN
  have h0 (z : E d) : (S.σ ^ 0) z = z := by rw [pow_zero]; rfl
  rw [endGeometry_exists_step4_vertexPoint_congr w' w hw]
  change t.frame ((S.σ ^ 0) (vertexPoint vt)) = q.frame ((S.σ ^ 0) (vertexPoint w)) at hx
  rw [h0, h0] at hx
  change t.frame.symm (q.frame (vertexPoint w)) = vertexPoint vt
  rw [← hx]
  exact t.frame.symm_apply_apply _

/-- Step 3 of the V4 proof of `endGeometry_exists` (V4 §2.5, 1.17--1.18): "finite".
Data over a finite set of base points, with finite fibres, form a finite set. -/
private theorem endGeometry_exists_step3_sigma_finite {α : Type*} {T : α → Type*}
    [∀ u, Finite (T u)] (s : Set α) (hs : s.Finite) :
    {z : Σ u, T u | z.1 ∈ s}.Finite := by
  have h : {z : Σ u, T u | z.1 ∈ s} = ⋃ u ∈ s, Set.range (Sigma.mk u) := by
    ext ⟨u, y⟩
    simp
  rw [h]
  exact hs.biUnion fun u _ => Set.finite_range _

/-- Q13, V4 §2.5, 1.17--1.18: every provider-zero occurrence has its complete
annotated positioned geometry. Nonemptiness is supplied by that actual occurrence. -/
theorem endGeometry_exists (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (hv : v.val.carrier ⊆ f.val.carrier)
    (hz : (U.recordTau P t f hf ⟨vertexCell v, hv⟩).val.val.dim = 0) :
    ∃ G : EndGeometry P, EndGeometryRealizes U P t f hf v G := by
  classical
  let B := U.hierarchy.birthParent t f hf
  let x := t.2.val.prototypeFrame t.1 (vertexPoint v)
  let hd := U.headerOf P t f hf v
  let tiles : Finset (FramedNode S) :=
    (ownedStar U B x).image (fun q => q.2.val.move t.2.val.frame.symm)
  have hstar (q : U.Node) (hq : q ∈ ownedStar U B x) : q ∈ ownedStarSet U B x := by
    simpa only [ownedStar, Set.Finite.mem_toFinset] using hq
  have hprim : {a : PrimitivePort P | IsSourcePrimitivePort U P t f hf v a}.Finite := by
    let φ : PrimitivePort P → Σ u : FramedNode S, FacetName S u.ty × VertexName S u.ty ×
        Σ ι : P.Incidence, Bool × ProviderCell ι.val :=
      fun a => ⟨a.tile, a.facet, a.vertex, a.incidence, a.sideIndex, a.providerVertex⟩
    have hinj : Function.Injective φ := by
      rintro ⟨t1, f1, v1, o1, i1, s1, d1, e1, p1, z1⟩
        ⟨t2, f2, v2, o2, i2, s2, d2, e2, p2, z2⟩ h
      simp only [φ, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h⟩ := h
      simp only [heq_eq_eq, Prod.mk.injEq, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, rfl, rfl, h⟩ := h
      simp only [heq_eq_eq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst e1
      subst e2
      rfl
    have hsub : φ '' {a | IsSourcePrimitivePort U P t f hf v a} ⊆
        {z | z.1 ∈ (tiles : Set (FramedNode S))} := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨q, hq, g, hg, w, hw, hx, hbirth, htile, -⟩ := ha
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨q, hq, htile.symm⟩)
    exact Set.Finite.of_finite_image
      ((endGeometry_exists_step3_sigma_finite _ tiles.finite_toSet).subset hsub) hinj.injOn
  have hbdry : {a : BoundaryPort P hd.birthType | IsSourceBoundaryPort U P t f hf v a}.Finite := by
    haveI := facetRecords_finite P
    let φ : BoundaryPort P hd.birthType → Σ u : FramedNode S, FacetName S u.ty ×
        VertexName S u.ty × FacetName S hd.birthType × (FacetRecord P → FacetRecord P) :=
      fun a => ⟨a.tile, a.facet, a.vertex, a.parentFacet, a.restriction⟩
    have hinj : Function.Injective φ := by
      rintro ⟨t1, f1, v1, o1, p1, r1⟩ ⟨t2, f2, v2, o2, p2, r2⟩ h
      simp only [φ, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h⟩ := h
      simp only [heq_eq_eq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rfl
    have hsub : φ '' {a | IsSourceBoundaryPort U P t f hf v a} ⊆
        {z | z.1 ∈ (tiles : Set (FramedNode S))} := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨q, hq, F, g, w, hw, hx, hsub, htile, -⟩ := ha
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨q, hq, htile.symm⟩)
    exact Set.Finite.of_finite_image
      ((endGeometry_exists_step3_sigma_finite _ tiles.finite_toSet).subset hsub) hinj.injOn
  have hcentral : t ∈ ownedStar U B x := by
    simpa only [ownedStar, Set.Finite.mem_toFinset] using
      endGeometry_exists_step1_central U t ht f hf v
  let G : EndGeometry P := {
    centralType := t.2.val.ty
    vertex := v
    header := hd
    tiles := tiles
    central_mem := Finset.mem_image.mpr
      ⟨t, hcentral, FramedNode.ext rfl (AffineIsometryEquiv.self_trans_symm _)⟩
    disjoint := by
      intro a ha b hb hne
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
      apply Set.disjoint_left.mpr
      intro z hza hzb
      have hmove (N : FramedNode S) :
          interior ((N.move t.2.val.frame.symm).carrier 0) =
            t.2.val.frame.symm '' interior (N.carrier 0) := by
        have hcarrier : (N.move t.2.val.frame.symm).carrier 0 =
            t.2.val.frame.symm '' N.carrier 0 := by
          simp [FramedNode.carrier, FramedNode.move, placedSet, Set.image_image]
        rw [hcarrier]
        exact (t.2.val.frame.symm.toHomeomorph.image_interior _).symm
      dsimp only at hza hzb
      rw [hmove] at hza hzb
      obtain ⟨zp, hzp, hzp'⟩ := hza
      obtain ⟨zr, hzr, hzr'⟩ := hzb
      have hzz : zp = zr := t.2.val.frame.symm.injective (hzp'.trans hzr'.symm)
      have hp0 := (hstar p hp).1
      have hr0 := (hstar r hr).1
      have hpr : p.2.val = r.2.val := U.hierarchy.same_height_disjoint 0 p.2.val r.2.val
        (hp0 ▸ p.2.property) (hr0 ▸ r.2.property) zp hzp (hzz.symm ▸ hzr)
      exact hne (congrArg (fun N : FramedNode S => N.move t.2.val.frame.symm) hpr)
    listed := by
      intro u hu
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
      exact endGeometry_exists_step2_move_lists q.2.val t.2.val q.1 t.1 (hstar q hq).1 ht v
        (endGeometry_exists_step2_listed U P t f hf v hv hz q (hstar q hq))
    primitivePorts := hprim.toFinset
    boundaryPorts := hbdry.toFinset
    primitive_tiles := by
      intro a ha
      obtain ⟨q, hq, g, hg, w, hw, hx, hbirth, htile, -⟩ := hprim.mem_toFinset.mp ha
      exact Finset.mem_image.mpr ⟨q, hq, htile.symm⟩
    boundary_tiles := by
      intro a ha
      obtain ⟨q, hq, F, g, w, hw, hx, hsub, htile, -⟩ := hbdry.mem_toFinset.mp ha
      exact Finset.mem_image.mpr ⟨q, hq, htile.symm⟩
    primitive_anchor := by
      intro a ha
      obtain ⟨q, hq, g, hg, w, hw, hx, hbirth, htile, hfac, hvert, -⟩ :=
        hprim.mem_toFinset.mp ha
      exact endGeometry_exists_step4_anchor q.2.val t.2.val a.tile q.1 t.1 (hstar q hq).1 ht
        v w a.vertex htile hvert hx
    boundary_anchor := by
      intro a ha
      obtain ⟨q, hq, F, g, w, hw, hx, hsub, htile, hfac, hvert, -⟩ :=
        hbdry.mem_toFinset.mp ha
      exact endGeometry_exists_step4_anchor q.2.val t.2.val a.tile q.1 t.1 (hstar q hq).1 ht
        v w a.vertex htile hvert hx }
  refine ⟨G, ?_⟩
  unfold EndGeometryRealizes
  refine ⟨rfl, rfl, rfl, rfl, fun a => hprim.mem_toFinset, fun a => hbdry.mem_toFinset⟩

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

open private header_finiteness_step4_flag_transporters from Enforce.Source.Headers in
/-- Step 1 of the V4 proof of `contTemplates_finite` (V4 §2.5): "the full oriented
flag ... fix[es] each relative placement". Isometries carrying the affine spans of
one complete named flag onto those of another, and one fixed point to another, form
a finite set: their linear parts transport a complete flag of directions (a coset of
the finite orthogonal flag stabilizer), and the image of one point fixes the
translation. -/
private theorem contTemplates_finite_step1_frames {A B : S.ι} (F : FacetFlag S A)
    (G : FacetFlag S B) (x₀ p : E d) :
    {φ : Iso d | (∀ j : FlagIndex d, affineSpan ℝ (F.cell j).val.carrier =
      affineSpan ℝ (φ '' (G.cell j).val.carrier)) ∧ φ x₀ = p}.Finite := by
  classical
  let V : ℕ → Submodule ℝ (E d) := fun i =>
    if h : 1 ≤ i ∧ i < d then cellDirection (G.cell ⟨i, h⟩).val.carrier
    else if i = 0 then ⊥ else ⊤
  let W : ℕ → Submodule ℝ (E d) := fun i =>
    if h : 1 ≤ i ∧ i < d then cellDirection (F.cell ⟨i, h⟩).val.carrier
    else if i = 0 then ⊥ else ⊤
  have hV0 : V 0 = ⊥ := by
    dsimp only [V]
    rw [dif_neg (by omega), if_pos rfl]
  have hW0 : W 0 = ⊥ := by
    dsimp only [W]
    rw [dif_neg (by omega), if_pos rfl]
  have hVd : V d = ⊤ := by
    have h2 : 2 ≤ d := Fact.out
    dsimp only [V]
    rw [dif_neg (by omega), if_neg (by omega)]
  have hWd : W d = ⊤ := by
    have h2 : 2 ≤ d := Fact.out
    dsimp only [W]
    rw [dif_neg (by omega), if_neg (by omega)]
  have hVm : ∀ (i : ℕ) (h : 1 ≤ i ∧ i < d),
      V i = cellDirection (G.cell ⟨i, h⟩).val.carrier := by
    intro i h
    dsimp only [V]
    rw [dif_pos h]
  have hWm : ∀ (i : ℕ) (h : 1 ≤ i ∧ i < d),
      W i = cellDirection (F.cell ⟨i, h⟩).val.carrier := by
    intro i h
    dsimp only [W]
    rw [dif_pos h]
  have hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i := by
    intro i hi
    by_cases h : 1 ≤ i ∧ i < d
    · rw [hVm i h, (G.cell ⟨i, h⟩).val.flat.dimension, G.dimension]
    · by_cases h0 : i = 0
      · subst h0
        rw [hV0, finrank_bot]
      · have hid : i = d := by omega
        subst hid
        rw [hVd, finrank_top, finrank_euclideanSpace_fin]
  have hmono : ∀ i < d, V i ≤ V (i + 1) := by
    intro i hi
    by_cases h0 : i = 0
    · subst h0
      rw [hV0]
      exact bot_le
    · by_cases h1 : i + 1 < d
      · rw [hVm i ⟨by omega, hi⟩, hVm (i + 1) ⟨by omega, h1⟩]
        exact AffineSubspace.direction_le (affineSpan_mono ℝ
          (G.nested ⟨i, by omega, hi⟩ ⟨i + 1, by omega, h1⟩ (by simp)))
      · have hid : i + 1 = d := by omega
        rw [hid, hVd]
        exact le_top
  have hT := header_finiteness_step4_flag_transporters V W hdim hmono
  have key : ∀ (φ : Iso d) (K : Set (E d)),
      (affineSpan ℝ (φ '' K)).direction =
        (affineSpan ℝ K).direction.map φ.linearIsometryEquiv.toLinearEquiv.toLinearMap := by
    intro φ K
    calc (affineSpan ℝ (φ '' K)).direction =
        ((affineSpan ℝ K).map φ.toAffineEquiv.toAffineMap).direction := by
          rw [AffineSubspace.map_span]
          rfl
      _ = _ := AffineSubspace.map_direction _ _
  apply Set.Finite.of_finite_image (f := fun φ : Iso d => φ.linearIsometryEquiv)
    (hT.subset ?_) ?_
  · rintro _ ⟨φ, ⟨hφ, -⟩, rfl⟩ i hi
    by_cases h : 1 ≤ i ∧ i < d
    · rw [hVm i h, hWm i h]
      change (affineSpan ℝ (G.cell ⟨i, h⟩).val.carrier).direction.map _ =
        (affineSpan ℝ (F.cell ⟨i, h⟩).val.carrier).direction
      rw [hφ ⟨i, h⟩, key]
    · by_cases h0 : i = 0
      · subst h0
        rw [hV0, hW0, Submodule.map_bot]
      · have hid : i = d := by omega
        subst hid
        rw [hVd, hWd, Submodule.map_top, LinearEquiv.range]
  · intro φ hφ ψ hψ heq
    have heq' : φ.linearIsometryEquiv = ψ.linearIsometryEquiv := heq
    ext x
    rw [← vsub_vadd x x₀, φ.map_vadd, ψ.map_vadd, heq', hφ.2, hψ.2]

/-- Step 2 of the V4 proof of `contTemplates_finite` (V4 §2.5): "finitely many CONT
positioned templates". The continuing tile's type is its record's type, its frame
aligns the two named full chains and sends the junction vertex to the slot vertex;
records, chains and vertices range over finite alphabets, so by Step 1 only finitely
many positioned continuing tiles occur. -/
private theorem contTemplates_finite_step2_others (P : Params S) (l : LeafType P)
    (slot : ContSlot l) :
    (Set.range (fun T : ContTemplate slot => T.other)).Finite := by
  classical
  haveI := facetRecords_finite P
  haveI : ∀ r : FacetRecord P, Finite (OrientedChain r.facet) :=
    fun r => orientedChains_finite _
  have hU : (⋃ (r : FacetRecord P) (c' : OrientedChain r.facet) (v : VertexName S r.ty)
      (c : OrientedChain slot.record.facet),
      (fun φ : Iso d => (⟨r.ty, φ⟩ : FramedNode S)) ''
        {φ : Iso d | (∀ j : FlagIndex d, affineSpan ℝ (c.chain.val.cell j).val.carrier =
          affineSpan ℝ (φ '' (c'.chain.val.cell j).val.carrier)) ∧
          φ (vertexPoint v) = vertexPoint slot.vertex}).Finite :=
    Set.finite_iUnion fun r => Set.finite_iUnion fun c' => Set.finite_iUnion fun v =>
      Set.finite_iUnion fun c =>
        (contTemplates_finite_step1_frames c.chain.val c'.chain.val _ _).image _
  apply hU.subset
  rintro _ ⟨T, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_image]
  refine ⟨T.record, T.otherChain, T.vertex, T.centralChain, T.other.frame,
    ⟨T.aligned.1, T.vertex_eq⟩, ?_⟩
  rw [T.type_eq]

/-- Q12, V4 §2.5: finitely many CONT positioned templates, with arbitrary matching
leaf labels. The full oriented flag and inward side fix each relative placement. -/
theorem contTemplates_finite (P : Params S) (l : LeafType P) (slot : ContSlot l) :
    (Set.range (fun T : ContTemplate slot => T.configuration)).Finite := by
  classical
  haveI := leafTypes_finite P
  have hF : (Set.range (fun T : ContTemplate slot => (T.other, T.label))).Finite :=
    ((contTemplates_finite_step2_others P l slot).prod
      (Set.finite_univ : (Set.univ : Set (LeafType P)).Finite)).subset
      (by rintro _ ⟨T, rfl⟩; exact ⟨⟨T, rfl⟩, trivial⟩)
  have hext : ∀ C C' : Template P, C.central = C'.central → C.tiles = C'.tiles →
      C.annotation = C'.annotation → C = C' := by
    rintro ⟨a, b, _, _, _, e⟩ ⟨a', b', _, _, _, e'⟩ h1 h2 h3
    dsimp only at h1 h2 h3
    subst h1 h2 h3
    rfl
  have hdet : ∀ T T' : ContTemplate slot, (T.other, T.label) = (T'.other, T'.label) →
      T.configuration = T'.configuration := by
    intro T T' h
    have h1 : T.other = T'.other := congrArg Prod.fst h
    have h2 : T.label = T'.label := congrArg Prod.snd h
    refine hext _ _ (T.central_eq.trans T'.central_eq.symm) ?_
      (T.annotation_none.trans T'.annotation_none.symm)
    rw [T.tiles_eq, T'.tiles_eq, h1, h2]
  haveI := hF.to_subtype
  apply (Set.finite_range (fun z : Set.range (fun T : ContTemplate slot => (T.other, T.label)) =>
    (Classical.choose z.2).configuration)).subset
  rintro _ ⟨T, rfl⟩
  refine ⟨⟨(T.other, T.label), T, rfl⟩, ?_⟩
  exact hdet _ _ (Classical.choose_spec
    (⟨T, rfl⟩ : (T.other, T.label) ∈ Set.range (fun T : ContTemplate slot => (T.other, T.label))))

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

/-- Step 1 of the V4 proof of `actualCont_exists` (V4 2.8):
"a native tile with a chain-active edge e of its facet f". Reading an actual
leaf recovers the facet record extracted from that same hierarchy node. -/
private theorem actualCont_exists_step1_readout (U : HonestSource S) (P : Params S)
    (t : U.Node) (ht : t.1 = 0) (f : FacetName S t.2.val.ty) :
    leafRecord (leafTypeOf U P t ht) f.val = U.facetRecordOf P t f := by
  unfold leafRecord
  rw [← prePattern_of_leafType U P t ht]
  simp only [prePatternOf, stateRecordAt, stateOf, dif_pos f.property]

/-- Step 1 of the V4 proof of `actualCont_exists` (V4 2.8):
"provider g, serving child H". A non-NULL readout of an actual leaf has an
actual nonfault facet, and its entire record is the geometric extraction. -/
private theorem actualCont_exists_step1_record (U : HonestSource S) (P : Params S)
    (t : U.Node) (ht : t.1 = 0) (k : Cell d) (r : FacetRecord P)
    (hr : leafRecord (leafTypeOf U P t ht) k = some r) :
    ∃ (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f),
      f.val = k ∧ U.recordOf P t f hf = r := by
  unfold leafRecord at hr
  rw [← prePattern_of_leafType U P t ht] at hr
  change stateRecordAt (stateOf U P t) k = some r at hr
  unfold stateRecordAt at hr
  split at hr
  · rename_i hk
    change U.facetRecordOf P t ⟨k, hk⟩ = some r at hr
    unfold HonestSource.facetRecordOf at hr
    split at hr
    · contradiction
    · rename_i hf
      exact ⟨⟨k, hk⟩, hf, rfl, Option.some.inj hr⟩
  · contradiction

/-- Step 2 of the V4 proof of `actualCont_exists` (V4 2.8):
"the terminal endpoint of e". Either orientation of a listed edge retains
its nondegenerate segment carrier. -/
private theorem actualCont_exists_step2_endpoints {P : Params S} (r : FacetRecord P)
    (e : PrototypeEdge S r.ty) :
    (r.endpoints e).1 ≠ (r.endpoints e).2 ∧
      e.val.carrier = segment ℝ (r.endpoints e).1 (r.endpoints e).2 := by
  have h := Classical.choose_spec (edge_endpoints_exist (⟨r.ty, e⟩ : EdgeName S))
  unfold FacetRecord.endpoints
  split
  · exact h
  · exact ⟨Ne.symm h.1, h.2.trans (segment_symm ℝ _ _)⟩

/-- Step 2 of the V4 proof of `actualCont_exists` (V4 2.8):
"after v in the orientation". All actual active chains on the same edge
give it the same orientation, which is the orientation read by `endpoints`. -/
private theorem actualCont_exists_step2_vector (U : HonestSource S) (P : Params S)
    (q : U.Node) (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (c : OrientedChain f) (hc : c ∈ U.recordChains P q f hf)
    (e : PrototypeEdge S q.2.val.ty)
    (he : (c.chain.val.cell edgeIndex).val = e.val) :
    ((U.recordOf P q f hf).endpoints e).2 -
      ((U.recordOf P q f hf).endpoints e).1 = chainVector c := by
  classical
  let r := U.recordOf P q f hf
  let edgeOf := fun z : OrientedChain f =>
    (restrictionOp_source_step4_chains_step1_edge z.chain.val).2
  have hec : edgeOf c = e := Subtype.ext he
  have horient (z : OrientedChain f) (hz : z ∈ r.chains) :
      z.forward = true ↔ 0 < inner ℝ (U.counterDirection P q f hf)
        ((q.2.val.prototypeFrame q.1).linear (edgeVector ⟨q.2.val.ty, edgeOf z⟩)) :=
    (Finset.mem_filter.mp hz).2.2
  have hsame (z : OrientedChain f) (hz : z ∈ r.chains)
      (hzedge : (z.chain.val.cell edgeIndex).val = e.val) : z.forward = c.forward := by
    have hez : edgeOf z = e := Subtype.ext hzedge
    have h := horient c hc
    have h' := horient z hz
    rw [hec] at h
    rw [hez] at h'
    have hiff := h'.trans h.symm
    cases hzbit : z.forward <;> cases hcbit : c.forward <;> simp_all
  have hforward : r.edgeForward e = c.forward := by
    unfold FacetRecord.edgeForward
    cases hcf : c.forward with
    | false =>
      apply Bool.eq_false_iff.mpr
      intro hh
      obtain ⟨z, hz, hze⟩ := List.any_eq_true.mp hh
      have hp : (z.chain.val.cell edgeIndex).val = e.val ∧ z.forward = true := by
        simpa using hze
      have heq := hsame z (Finset.mem_toList.mp hz) hp.1
      simp_all
    | true =>
      apply List.any_eq_true.mpr
      exact ⟨c, Finset.mem_toList.mpr hc, by simp [he, hcf]⟩
  change (r.endpoints e).2 - (r.endpoints e).1 = _
  unfold FacetRecord.endpoints
  rw [hforward]
  have hvector : chainVector c =
      if c.forward then edgeVector ⟨q.2.val.ty, e⟩ else -edgeVector ⟨q.2.val.ty, e⟩ := by
    change (if c.forward then edgeVector ⟨q.2.val.ty, edgeOf c⟩
      else -edgeVector ⟨q.2.val.ty, edgeOf c⟩) = _
    rw [hec]
  rw [hvector]
  cases c.forward <;> simp [edgeVector, neg_sub]

/-- Step 2 of the V4 proof of `actualCont_exists` (V4 2.8):
"v in relint h (transported)". The recorded stratum of a listed vertex
puts its actual physical point in the relative interior of that provider cell. -/
private theorem actualCont_exists_step2_vertex (U : HonestSource S) (P : Params S)
    (q : U.Node) (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (v : VertexName S q.2.val.ty) (hv : v.val.carrier ⊆ f.val.carrier)
    (hτ : (U.recordOf P q f hf).tauAt v.val =
      some ((P.flag (U.recordIncidence P q f hf)).flag.cell edgeIndex).val) :
    q.2.val.prototypeFrame q.1 (vertexPoint v) ∈ relint
      (U.providerPlacement P q f hf ''
        ((P.flag (U.recordIncidence P q f hf)).flag.cell edgeIndex).val.carrier) := by
  have hvc : v.val ∈ (S.cx q.2.val.ty).cells := (vertexCell v).property
  simp only [FacetRecord.tauAt, HonestSource.recordOf, dif_pos hvc, dif_pos hv,
    Option.some.injEq] at hτ
  have hpoint : q.2.val.prototypeFrame q.1 (vertexPoint v) ∈
      relint (q.2.val.cell q.1 v.val) := by
    simp only [FramedNode.cell, vertexPoint_spec, Set.image_singleton, relint,
      intrinsicInterior_singleton, Set.mem_singleton_iff]
  have h := (U.hierarchy.stratumMap_spec q f hf (vertexCell v)
    (U.cellInFacet_placed q f ⟨vertexCell v, hv⟩)).1 hpoint
  rw [← record_tau_spec U P q f hf ⟨vertexCell v, hv⟩] at h
  simpa only [HonestSource.recordOf, vertexCell, hτ] using h

/-- Step 1 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 2.8):
"the polygons ... adjacent to h tile a neighbourhood of v in h". A point of the
relative interior of a set can be pushed a little beyond itself along the
direction from any other point of the set, staying in the set. -/
private theorem actualCont_exists_step3_trace_successor_step1_ray (s : Set (E d))
    (p v : E d) (hp : p ∈ s) (hv : v ∈ relint s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 ≤ t → t < δ → v + t • (v - p) ∈ s := by
  unfold relint at hv
  obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.mp hv
  have hmem (t : ℝ) : (y : E d) + t • ((y : E d) - p) ∈ affineSpan ℝ s := by
    have h1 : (y : E d) ∈ affineSpan ℝ s := y.property
    have h2 : p ∈ affineSpan ℝ s := mem_affineSpan ℝ hp
    have h := AffineSubspace.smul_vsub_vadd_mem (affineSpan ℝ s) t h1 h2 h1
    simpa only [vsub_eq_sub, vadd_eq_add, add_comm] using h
  let g : ℝ → affineSpan ℝ s := fun t => ⟨(y : E d) + t • ((y : E d) - p), hmem t⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    fun_prop
  have hg0 : g 0 = y := by
    apply Subtype.ext
    simp [g]
  have hnhds : g ⁻¹' interior (((↑) : affineSpan ℝ s → E d) ⁻¹' s) ∈ nhds (0 : ℝ) := by
    apply hg.continuousAt.preimage_mem_nhds
    rw [hg0]
    exact isOpen_interior.mem_nhds hy
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ, hδ, fun t ht htδ => ?_⟩
  have htb : t ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht]
    exact htδ
  have h1 : g t ∈ ((↑) : affineSpan ℝ s → E d) ⁻¹' s := interior_subset (hball htb)
  exact h1

/-- Step 1 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 2.8):
"initial endpoint v". An endpoint of a nondegenerate segment is not in its
relative interior: pushing it beyond itself leaves the segment. -/
private theorem actualCont_exists_step3_trace_successor_step1_endpoint (x y : E d)
    (hxy : x ≠ y) : x ∉ relint (segment ℝ x y) := by
  intro hx
  obtain ⟨δ, hδ, hray⟩ := actualCont_exists_step3_trace_successor_step1_ray
    (segment ℝ x y) y x (right_mem_segment ℝ x y) hx
  obtain ⟨α, β, hα, hβ, hαβ, hh⟩ := hray (δ / 2) (by positivity) (by linarith)
  have hα' : α = 1 - β := by linarith
  rw [hα'] at hh
  have h0 : (β + δ / 2) • (y - x) = 0 := by
    calc (β + δ / 2) • (y - x) = ((1 - β) • x + β • y - x) - (δ / 2) • (x - y) := by module
      _ = 0 := by rw [hh]; module
  rcases smul_eq_zero.mp h0 with h | h
  · linarith
  · exact hxy (sub_eq_zero.mp h).symm

/-- Step 1 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 2.8):
"v in the relative interior of its edge". Every point of the open segment of a
nondegenerate segment lies in its relative interior (one-dimensional fact). -/
private theorem actualCont_exists_step3_trace_successor_step1_open_relint (x y : E d)
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

/-- Step 1 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 2.8):
"after v". A point strictly beyond the endpoint `v` of the segment `[p, v]`
is not in that segment. -/
private theorem actualCont_exists_step3_trace_successor_step1_beyond (p v : E d)
    (hne : p ≠ v) (t : ℝ) (ht : 0 < t) : v + t • (v - p) ∉ segment ℝ p v := by
  rintro ⟨α, β, hα, hβ, hαβ, hh⟩
  have hβ' : β = 1 - α := by linarith
  rw [hβ'] at hh
  have h0 : (α + t) • (p - v) = 0 := by
    calc (α + t) • (p - v) = (α • p + (1 - α) • v) - (v + t • (v - p)) := by module
      _ = 0 := by rw [hh]; module
  rcases smul_eq_zero.mp h0 with h | h
  · linarith
  · exact hne (sub_eq_zero.mp h)

/-- Step 2 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 1.1, 1.22(a)):
"edge heredity". Containment of placed cells bounds their dimensions;
invertible affine placement preserves the dimension of each affine span. -/
private theorem actualCont_exists_step3_trace_successor_step2_dim_le
    (φ ψ : E d ≃ᵃ[ℝ] E d) (e f : Cell d)
    (hsub : φ '' e.carrier ⊆ ψ '' f.carrier) : e.dim ≤ f.dim := by
  have hdim (φ : E d ≃ᵃ[ℝ] E d) (e : Cell d) :
      Module.finrank ℝ (affineSpan ℝ (φ '' e.carrier)).direction = e.dim := by
    change Module.finrank ℝ (affineSpan ℝ (φ.toAffineMap '' e.carrier)).direction = e.dim
    rw [← AffineSubspace.map_span φ.toAffineMap, AffineSubspace.map_direction]
    exact (φ.linear.finrank_map_eq _).trans e.flat.dimension
  have h := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hsub))
  simpa only [hdim] using h

/-- Step 2 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 1.22(a)):
"owner t'' of the polygon s_2''". The placed owner has the native owner's type. -/
private theorem actualCont_exists_step3_trace_successor_step2_owner_ty (N : FramedNode S)
    (n : ℕ) (F : FacetFlag S N.ty) (b : TracePiece N.ty F n) :
    (placedTraceOwner N n n F b).ty = b.tile.ty := by
  simp only [placedTraceOwner, FramedNode.move, Nat.sub_self, TracePiece.tile,
    SubstSystem.nativeTile]

/-- Step 2 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 1.22(a)):
"the polygon s_2'' of its owner". The placed trace piece is the placed bottom
cell of its own owner. -/
private theorem actualCont_exists_step3_trace_successor_step2_carrier (N : FramedNode S)
    (n : ℕ) (F : FacetFlag S N.ty) (b : TracePiece N.ty F n) :
    placedTraceCarrier N n n F b = (placedTraceOwner N n n F b).cell 0 b.bottom.val := by
  have h := placedTraceOwner_cells N n n le_rfl F b b.bottom.val
  rw [Nat.sub_self] at h
  exact h.symm

/-- Step 2 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 1.1, 1.22(a)):
"an edge e'' along h". Away from listed vertices of the owner, a point of a placed
trace piece on the flag edge lies on a listed edge of the owner, contained both
in the flag edge (Lemma 1.1) and in the trace piece. -/
private theorem actualCont_exists_step3_trace_successor_step2_trace_edge
    (N : FramedNode S) (n : ℕ) (F : FacetFlag S N.ty) (b : TracePiece N.ty F n) (z : E d)
    (hzb : z ∈ placedTraceCarrier N n n F b)
    (hzh : z ∈ N.cell n (F.cell edgeIndex).val)
    (hnv : ¬ (placedTraceOwner N n n F b).Lists 0 z) :
    ∃ e : PrototypeEdge S (placedTraceOwner N n n F b).ty,
      z ∈ (placedTraceOwner N n n F b).cell 0 e.val ∧
      (placedTraceOwner N n n F b).cell 0 e.val ⊆ N.cell n (F.cell edgeIndex).val ∧
      (placedTraceOwner N n n F b).cell 0 e.val ⊆ placedTraceCarrier N n n F b := by
  classical
  have hty := actualCont_exists_step3_trace_successor_step2_owner_ty N n F b
  have hcar := actualCont_exists_step3_trace_successor_step2_carrier N n F b
  have hdesc : (placedTraceOwner N n n F b).IsDescendant 0 N n :=
    ⟨n, (zero_add n).symm, b.owner, by simp only [placedTraceOwner, Nat.sub_self]⟩
  rw [hcar] at hzb ⊢
  generalize placedTraceOwner N n n F b = C at hty hdesc hnv hzb ⊢
  have hbot : b.bottom.val ∈ (S.cx C.ty).cells := by
    rw [hty]
    exact b.bottom.property
  obtain ⟨u, hu, rfl⟩ := hzb
  have hu' : u ∈ frontier (S.proto C.ty).carrier := by
    rw [← (S.cx C.ty).carriers_cover]
    exact mem_iUnion₂.mpr ⟨b.bottom.val, hbot, hu⟩
  let e := (S.cx C.ty).minimalCell u hu'
  have he := (S.cx C.ty).minimalCell_mem u hu'
  have hue := (S.cx C.ty).mem_relint_minimalCell u hu'
  have hbottom : e.carrier ⊆ b.bottom.val.carrier :=
    (S.cx C.ty).minimalCell_subset u hu' b.bottom.val hbot hu
  have hzrel : C.prototypeFrame 0 u ∈ relint (C.cell 0 e) := by
    change C.frame u ∈ intrinsicInterior ℝ (C.frame.toAffineIsometry '' e.carrier)
    rw [C.frame.toAffineIsometry.image_intrinsicInterior]
    exact Set.mem_image_of_mem _ hue
  have hze : C.prototypeFrame 0 u ∈ C.cell 0 e := intrinsicInterior_subset hzrel
  have hsub : C.cell 0 e ⊆ N.cell n (F.cell edgeIndex).val :=
    hereditary_trace N C n 0 hdesc (F.cell edgeIndex).val e (F.cell edgeIndex).property he
      ⟨C.prototypeFrame 0 u, hzrel, hzh⟩
  have hdim : e.dim ≤ 1 := by
    have hh := actualCont_exists_step3_trace_successor_step2_dim_le
      (C.prototypeFrame 0) (N.prototypeFrame n) e (F.cell edgeIndex).val hsub
    simpa only [F.dimension edgeIndex] using hh
  have hnonzero : e.dim ≠ 0 := by
    intro hz
    exact hnv ⟨e, Finset.mem_filter.mpr ⟨he, hz⟩, hze⟩
  exact ⟨⟨e, Finset.mem_filter.mpr ⟨he, by omega⟩⟩, hze, hsub, Set.image_mono hbottom⟩

/-- Step 3 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 2.8, 1.22(a)):
"there is a polygon s_2'' adjacent to h on the far side of v ... with an edge
e'' along h". Points just beyond `v` on the flag edge are covered by the finitely
many trace pieces; avoiding the finitely many listed vertices and the closed edges
missing `v`, one listed owner edge along `h` contains `v` and a point beyond it. -/
private theorem actualCont_exists_step3_trace_successor_step3_edge_germ (N : FramedNode S)
    (n : ℕ) (F : FacetFlag S N.ty) (p v : E d) (hne : p ≠ v)
    (hp : p ∈ N.cell n (F.cell edgeIndex).val)
    (hv : v ∈ relint (N.cell n (F.cell edgeIndex).val)) :
    ∃ (b : TracePiece N.ty F n) (e : PrototypeEdge S (placedTraceOwner N n n F b).ty)
      (t : ℝ), 0 < t ∧ v ∈ (placedTraceOwner N n n F b).cell 0 e.val ∧
      v + t • (v - p) ∈ (placedTraceOwner N n n F b).cell 0 e.val ∧
      (placedTraceOwner N n n F b).cell 0 e.val ⊆ N.cell n (F.cell edgeIndex).val ∧
      (placedTraceOwner N n n F b).cell 0 e.val ⊆ placedTraceCarrier N n n F b := by
  classical
  letI : Finite (TracePiece N.ty F n) := tracePieces_finite N.ty F n
  obtain ⟨δ, hδ, hray⟩ := actualCont_exists_step3_trace_successor_step1_ray
    (N.cell n (F.cell edgeIndex).val) p v hp hv
  let Good := {z : Σ b : TracePiece N.ty F n, PrototypeEdge S (placedTraceOwner N n n F b).ty //
    (placedTraceOwner N n n F z.1).cell 0 z.2.val ⊆ N.cell n (F.cell edgeIndex).val ∧
      (placedTraceOwner N n n F z.1).cell 0 z.2.val ⊆ placedTraceCarrier N n n F z.1}
  let Far := {z : Good // v ∉ (placedTraceOwner N n n F z.val.1).cell 0 z.val.2.val}
  let K : Set (E d) := ⋃ z : Far, (placedTraceOwner N n n F z.val.val.1).cell 0 z.val.val.2.val
  let V : Set (E d) := ⋃ b : TracePiece N.ty F n,
    ⋃ w : VertexName S (placedTraceOwner N n n F b).ty,
      {(placedTraceOwner N n n F b).prototypeFrame 0 (vertexPoint w)}
  have hK : IsClosed K := by
    apply isClosed_iUnion_of_finite
    intro z
    exact (z.val.val.2.val.flat.compact.image
      ((placedTraceOwner N n n F z.val.val.1).prototypeFrame 0).continuous_of_finiteDimensional
      ).isClosed
  have hvK : v ∉ K := by
    intro h
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp h
    exact z.property hz
  have hV : V.Finite := Set.finite_iUnion fun b =>
    Set.finite_iUnion fun w => Set.finite_singleton _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl v hvK
  let u := v - p
  have hu : u ≠ 0 := sub_ne_zero.mpr hne.symm
  let η := min δ (ε / (‖u‖ + 1))
  have hden : 0 < ‖u‖ + 1 := by positivity
  have hη : 0 < η := lt_min hδ (div_pos hε hden)
  let L : ℝ → E d := fun t => v + t • u
  have hL : Function.Injective L := by
    intro a b h
    exact smul_left_injective ℝ hu (add_left_cancel h)
  obtain ⟨t, ht, htv⟩ := (Set.Ioo_infinite hη).exists_notMem_finite (hV.preimage hL.injOn)
  have htδ : t < δ := lt_of_lt_of_le ht.2 (min_le_left _ _)
  have htε : t < ε / (‖u‖ + 1) := lt_of_lt_of_le ht.2 (min_le_right _ _)
  have hzh : L t ∈ N.cell n (F.cell edgeIndex).val := hray t ht.1.le htδ
  have hnear : L t ∈ ball v ε := by
    change dist (v + t • u) v < ε
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    have := (lt_div_iff₀ hden).mp htε
    nlinarith [norm_nonneg u]
  have hz2 : L t ∈ N.cell n
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val :=
    Set.image_mono (F.nested edgeIndex
      ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩ traceDimension_pos) hzh
  rw [← (placed_recursiveTrace_tiles N n n le_rfl F).1] at hz2
  obtain ⟨b, hzb⟩ := Set.mem_iUnion.mp hz2
  have hnv : ¬ (placedTraceOwner N n n F b).Lists 0 (L t) := by
    rintro ⟨w, hw, hzw⟩
    let w' : VertexName S (placedTraceOwner N n n F b).ty := ⟨w, hw⟩
    have hpoint : L t = (placedTraceOwner N n n F b).prototypeFrame 0 (vertexPoint w') := by
      change L t ∈ (placedTraceOwner N n n F b).cell 0 w'.val at hzw
      simpa only [FramedNode.cell, vertexPoint_spec w', Set.image_singleton,
        Set.mem_singleton_iff] using hzw
    exact htv (Set.mem_iUnion_of_mem b (Set.mem_iUnion_of_mem w' hpoint))
  obtain ⟨e, hze, heh, heb⟩ :=
    actualCont_exists_step3_trace_successor_step2_trace_edge N n F b (L t) hzb hzh hnv
  refine ⟨b, e, t, ht.1, ?_, hze, heh, heb⟩
  by_contra hve
  exact hball hnear (Set.mem_iUnion_of_mem (⟨⟨⟨b, e⟩, heh, heb⟩, hve⟩ : Far) hze)

/-- Step 4 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 2.8):
"after v in the orientation". A segment from `v` containing a point strictly
beyond `v` along `u` has its other endpoint on the positive ray of `u`. -/
private theorem actualCont_exists_step3_trace_successor_step4_direction (v w u : E d)
    (t : ℝ) (ht : 0 < t) (hu : u ≠ 0) (h : v + t • u ∈ segment ℝ v w) :
    ∃ k : ℝ, 0 < k ∧ w - v = k • u := by
  obtain ⟨α, β, hα, hβ, hαβ, hvw⟩ := h
  have hα' : α = 1 - β := by linarith
  have hβu : β • (w - v) = t • u := by
    have hh := congrArg (fun z : E d => z - v) hvw
    simp only [add_sub_cancel_left] at hh
    rw [← hh, hα']
    module
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hβu
    exact hu ((smul_eq_zero.mp hβu.symm).resolve_left ht.ne')
  have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
  refine ⟨t / β, div_pos ht hβpos, ?_⟩
  have hh := congrArg (fun z : E d => β⁻¹ • z) hβu
  simp only [smul_smul, inv_mul_cancel₀ hβ0, one_smul] at hh
  rw [hh, div_eq_inv_mul]

/-- Step 5 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 2.8, (H2)):
"v is a vertex of s_2''", same-owner case. If the next edge belonged to the
same owner as the edge `e` ending at `v`, a listed edge of that owner would
contain `v` in its relative interior together with a point beyond `v`, so the
two listed edges would share relative-interior points of `e` near `v`; by (H2)(i)
they would coincide, but `e` ends at `v`. -/
private theorem actualCont_exists_step3_trace_successor_step5_same_owner (C : FramedNode S)
    (e e' : PrototypeEdge S C.ty) (p v x y : E d) (t : ℝ) (ht : 0 < t) (hne : p ≠ v)
    (hseg : C.cell 0 e.val = segment ℝ p v) (hseg' : C.cell 0 e'.val = segment ℝ x y)
    (hv : v ∈ openSegment ℝ x y) (hfwd : v + t • (v - p) ∈ segment ℝ x y) : False := by
  have hxy : x ≠ y := by
    rintro rfl
    rw [openSegment_same, Set.mem_singleton_iff] at hv
    rw [segment_same, Set.mem_singleton_iff, hv] at hfwd
    have h0 : t • (x - p) = 0 := by
      have hh := congrArg (fun z : E d => z - x) hfwd
      simpa only [add_sub_cancel_left, sub_self] using hh
    rcases smul_eq_zero.mp h0 with h | h
    · exact ht.ne' h
    · exact hne (hv ▸ (sub_eq_zero.mp h).symm)
  have hvC : v ∈ intrinsicInterior ℝ (C.frame.toAffineIsometry '' e'.val.carrier) := by
    have h := actualCont_exists_step3_trace_successor_step1_open_relint x y hxy hv
    rw [← hseg'] at h
    exact h
  rw [C.frame.toAffineIsometry.image_intrinsicInterior] at hvC
  obtain ⟨v0, hv0, hv0v⟩ := hvC
  have hv0e : v0 ∈ e.val.carrier := by
    have h : v ∈ C.cell 0 e.val := hseg ▸ right_mem_segment ℝ p v
    obtain ⟨q, hq, hqv⟩ := h
    have hq' : q = v0 := C.frame.injective (hqv.trans hv0v.symm)
    exact hq' ▸ hq
  have hec : e.val ∈ (S.cx C.ty).cells := (Finset.mem_filter.mp e.property).1
  have he'c : e'.val ∈ (S.cx C.ty).cells := (Finset.mem_filter.mp e'.property).1
  have hfr : v0 ∈ frontier (S.proto C.ty).carrier := by
    rw [← (S.cx C.ty).carriers_cover]
    exact mem_iUnion₂.mpr ⟨e.val, hec, hv0e⟩
  have huniq := (S.cx C.ty).exists_unique_minimalCell v0 hfr
  have hm : (S.cx C.ty).minimalCell v0 hfr = e'.val := by
    have h := huniq.unique (Classical.choose_spec huniq).1
      (show v0 ∈ relint (⟨e'.val, he'c⟩ : {f // f ∈ (S.cx C.ty).cells}).val.carrier from hv0)
    exact congrArg Subtype.val h
  have hsub := (S.cx C.ty).minimalCell_subset v0 hfr e.val hec hv0e
  rw [hm] at hsub
  have hsub' : segment ℝ x y ⊆ segment ℝ p v := by
    rw [← hseg, ← hseg']
    exact Set.image_mono hsub
  exact actualCont_exists_step3_trace_successor_step1_beyond p v hne t ht (hsub' hfwd)

/-- Step 1 of the V4 proof of `actualCont_exists_step3_trace_successor_step6_fill`
(V4 1.22(a)): "the recorded chain s_2 ⊂ ⋯ lies in the fixed successive cofaces": the
placed trace polygon (edge for `d = 2`) lies in the placed bottom flag cell `F_2`. -/
private theorem actualCont_exists_step3_trace_successor_step6_fill_step1_subset
    (N : FramedNode S) (n : ℕ) (F : FacetFlag S N.ty) (a : TracePiece N.ty F n) :
    placedTraceCarrier N n n F a ⊆
      N.cell n (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val := by
  have h := a.chain.contained TracePiece.bottomIndex
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨q, hq, hqy⟩ := h hy
  refine ⟨q, hq, ?_⟩
  show N.frame ((S.σ ^ n) q) = N.frame ((S.σ ^ (n - n)) y)
  rw [Nat.sub_self, pow_zero, hqy]
  rfl

/-- Step 2 of the V4 proof of `actualCont_exists_step3_trace_successor_step6_fill`
(V4 1.0, (H2)): "s_2 has aff = aff F_2". Affine equivalences preserve the dimension of
the affine span. -/
private theorem actualCont_exists_step3_trace_successor_step6_fill_step2_finrank_image
    (g : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
    Module.finrank ℝ (affineSpan ℝ (g '' K)).direction =
      Module.finrank ℝ (affineSpan ℝ K).direction := by
  change Module.finrank ℝ (affineSpan ℝ (g.toAffineMap '' K)).direction = _
  rw [← AffineSubspace.map_span g.toAffineMap K, AffineSubspace.map_direction]
  exact LinearEquiv.finrank_map_eq g.linear _

/-- Step 2 of the V4 proof of `actualCont_exists_step3_trace_successor_step6_fill`
(V4 1.0, (H2)): a nonempty subset of no smaller affine dimension has the same span. -/
private theorem actualCont_exists_step3_trace_successor_step6_fill_step2_span_of_finrank
    {K L : Set (E d)} (hKL : K ⊆ L) (hK : K.Nonempty)
    (hdim : Module.finrank ℝ (affineSpan ℝ L).direction ≤
      Module.finrank ℝ (affineSpan ℝ K).direction) :
    affineSpan ℝ K = affineSpan ℝ L := by
  obtain ⟨z, hz⟩ := hK
  have hle := AffineSubspace.direction_le (affineSpan_mono ℝ hKL)
  have hdir := Submodule.eq_of_le_of_finrank_le hle hdim
  exact AffineSubspace.ext_of_direction_eq hdir
    ⟨z, subset_affineSpan ℝ _ hz, subset_affineSpan ℝ _ (hKL hz)⟩

/-- Step 2 of the V4 proof of `actualCont_exists_step3_trace_successor_step6_fill`
(V4 1.0, (H2)): relative interiors are monotone between sets with the same span. -/
private theorem actualCont_exists_step3_trace_successor_step6_fill_step2_relint_mono
    {K L : Set (E d)} (hKL : K ⊆ L) (hspan : affineSpan ℝ K = affineSpan ℝ L) :
    relint K ⊆ relint L := by
  unfold relint intrinsicInterior
  rw [← hspan]
  exact Set.image_mono (interior_mono (Set.preimage_mono hKL))

/-- Step 2 of the V4 proof of `actualCont_exists_step3_trace_successor_step6_fill`
(V4 1.22(a)): "aff s_2 = aff F_2": the placed trace piece and the placed bottom flag
cell have the same affine span (both have dimension `traceDimension d`). -/
private theorem actualCont_exists_step3_trace_successor_step6_fill_step2_span
    (N : FramedNode S) (n : ℕ) (F : FacetFlag S N.ty) (a : TracePiece N.ty F n) :
    affineSpan ℝ (placedTraceCarrier N n n F a) =
      affineSpan ℝ (N.cell n
        (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val) := by
  apply actualCont_exists_step3_trace_successor_step6_fill_step2_span_of_finrank
    (actualCont_exists_step3_trace_successor_step6_fill_step1_subset N n F a)
  · obtain ⟨w, hw⟩ := a.bottom.val.flat.relint_nonempty
    rw [actualCont_exists_step3_trace_successor_step2_carrier N n F a]
    exact ⟨_, Set.mem_image_of_mem ((placedTraceOwner N n n F a).prototypeFrame 0)
      (intrinsicInterior_subset hw)⟩
  · rw [actualCont_exists_step3_trace_successor_step2_carrier N n F a]
    unfold FramedNode.cell
    rw [actualCont_exists_step3_trace_successor_step6_fill_step2_finrank_image,
      actualCont_exists_step3_trace_successor_step6_fill_step2_finrank_image]
    have h1 := a.bottom.val.flat.dimension
    have h2 := (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.flat.dimension
    have hb : a.bottom.val.dim = traceDimension d := a.chain.dimension TracePiece.bottomIndex
    have hf : (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.dim =
      traceDimension d := F.dimension _
    unfold cellDirection at h1 h2
    omega

/-- Step 2 of the V4 proof of `actualCont_exists_step3_trace_successor_step6_fill`
(V4 1.1): "its edge along h": a listed owner edge inside the flag edge spans the
same line as the flag edge. -/
private theorem actualCont_exists_step3_trace_successor_step6_fill_step2_edge_span
    (N : FramedNode S) (n : ℕ) (F : FacetFlag S N.ty) (a : TracePiece N.ty F n)
    (e : PrototypeEdge S (placedTraceOwner N n n F a).ty)
    (hflag : (placedTraceOwner N n n F a).cell 0 e.val ⊆ N.cell n (F.cell edgeIndex).val) :
    affineSpan ℝ ((placedTraceOwner N n n F a).cell 0 e.val) =
      affineSpan ℝ (N.cell n (F.cell edgeIndex).val) := by
  apply actualCont_exists_step3_trace_successor_step6_fill_step2_span_of_finrank hflag
  · obtain ⟨w, hw⟩ := e.val.flat.relint_nonempty
    exact ⟨_, Set.mem_image_of_mem ((placedTraceOwner N n n F a).prototypeFrame 0)
      (intrinsicInterior_subset hw)⟩
  · unfold FramedNode.cell
    rw [actualCont_exists_step3_trace_successor_step6_fill_step2_finrank_image,
      actualCont_exists_step3_trace_successor_step6_fill_step2_finrank_image]
    have h1 := e.val.flat.dimension
    have h2 := (F.cell edgeIndex).val.flat.dimension
    have he1 : e.val.dim = 1 := (Finset.mem_filter.mp e.property).2
    have hf : (F.cell edgeIndex).val.dim = 1 := F.dimension edgeIndex
    unfold cellDirection at h1 h2
    omega

open private states_finite_step4_flag_halfspace_lem_relint
  states_finite_step4_flag_halfspace_lem_local_frontier from Enforce.State.State in
/-- Step 3 of the V4 proof of `actualCont_exists_step3_trace_successor_step6_fill`
(V4 2.8, (H2)(ii)): "a polygon containing v in the relative interior of its edge along
h": near a relative-interior point `z` of a listed owner edge `e` lying along the flag
edge `h` inside the trace polygon `s_2`, the relative boundary of `s_2` is the edge `e`
itself (the relative boundary is a union of listed cells, and the only listed cells
through `z` contain `e`); `e` lies in `h`, whose relative interior is disjoint from that
of `F_2`. Hence a point of `s_2` near `z` in the relative interior of `F_2` is in the
relative interior of `s_2`. (For `d = 2`, `s_2` is an edge containing `z` in its
relative interior.) -/
private theorem actualCont_exists_step3_trace_successor_step6_fill_step3_owner_frontier
    (N : FramedNode S) (n : ℕ) (F : FacetFlag S N.ty) (a : TracePiece N.ty F n)
    (e : PrototypeEdge S (placedTraceOwner N n n F a).ty) (z : E d)
    (hbot : (placedTraceOwner N n n F a).cell 0 e.val ⊆ placedTraceCarrier N n n F a)
    (hflag : (placedTraceOwner N n n F a).cell 0 e.val ⊆ N.cell n (F.cell edgeIndex).val)
    (hz : z ∈ relint ((placedTraceOwner N n n F a).cell 0 e.val)) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball z r, x ∈ placedTraceCarrier N n n F a →
      x ∈ relint (N.cell n
        (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val) →
      x ∈ relint (placedTraceCarrier N n n F a) := by
  classical
  have hX : placedTraceCarrier N n n F a = (placedTraceOwner N n n F a).cell 0 a.bottom.val :=
    actualCont_exists_step3_trace_successor_step2_carrier N n F a
  have hd2 : 2 ≤ d := Fact.out
  have hb : a.bottom.val.dim = traceDimension d := a.chain.dimension TracePiece.bottomIndex
  have he1 : e.val.dim = 1 := (Finset.mem_filter.mp e.property).2
  rcases Nat.lt_or_ge 2 d with hd | hd
  · have htd : traceDimension d = 2 := by unfold traceDimension; omega
    have hbC : a.bottom.val ∈ (S.cx (placedTraceOwner N n n F a).ty).cells := by
      rw [actualCont_exists_step3_trace_successor_step2_owner_ty N n F a]
      exact a.bottom.property
    have heC : e.val ∈ (S.cx (placedTraceOwner N n n F a).ty).cells :=
      (Finset.mem_filter.mp e.property).1
    have hdim : a.bottom.val.dim = e.val.dim + 1 := by omega
    have hhF : Disjoint (relint (N.cell n (F.cell edgeIndex).val))
        (relint (N.cell n
          (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val)) := by
      have hne : (F.cell edgeIndex).val ≠
          (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val := by
        intro heq
        have h1 : (F.cell edgeIndex).val.dim = 1 := F.dimension edgeIndex
        have h2 : (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.dim =
          traceDimension d := F.dimension _
        rw [heq] at h1
        omega
      have hdj := (S.cx N.ty).relint_disjoint _ (F.cell edgeIndex).property _
        (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).property hne
      rw [FramedNode.cell, FramedNode.cell, restrictionOp_source_step5_relint_image,
        restrictionOp_source_step5_relint_image]
      exact (Set.disjoint_image_iff (N.prototypeFrame n).injective).mpr hdj
    have hEH := actualCont_exists_step3_trace_successor_step6_fill_step2_relint_mono hflag
      (actualCont_exists_step3_trace_successor_step6_fill_step2_edge_span N n F a e hflag)
    have hz' := hz
    rw [FramedNode.cell, restrictionOp_source_step5_relint_image] at hz'
    obtain ⟨z0, hz0, rfl⟩ := hz'
    obtain ⟨r, hr, hloc⟩ :=
      states_finite_step4_flag_halfspace_lem_local_frontier (S.cx _) heC hbC hdim hz0
    obtain ⟨-, ρ, hρ, hρe⟩ := states_finite_step4_flag_halfspace_lem_relint.mp hz0
    refine ⟨min r (ρ / 2), lt_min hr (half_pos hρ), fun x hx hxX hxY => ?_⟩
    by_contra hxi
    rw [hX] at hxX hxi
    obtain ⟨x0, hx0, rfl⟩ := hxX
    have hd0 : dist x0 z0 < min r (ρ / 2) := by
      have h0 : dist ((placedTraceOwner N n n F a).frame x0)
          ((placedTraceOwner N n n F a).frame z0) < min r (ρ / 2) := hx
      rwa [(placedTraceOwner N n n F a).frame.dist_map] at h0
    have hx0i : x0 ∉ relint a.bottom.val.carrier := fun h => hxi (by
      rw [FramedNode.cell, restrictionOp_source_step5_relint_image]
      exact Set.mem_image_of_mem _ h)
    have hx0f : x0 ∈ relfrontier a.bottom.val.carrier := by
      change x0 ∈ intrinsicFrontier ℝ _
      rw [← closure_diff_intrinsicInterior, a.bottom.val.flat.compact.isClosed.closure_eq]
      exact ⟨hx0, hx0i⟩
    have hx0s := hloc x0 (lt_of_lt_of_le hd0 (min_le_left _ _)) hx0f
    have hx0r : x0 ∈ relint e.val.carrier := by
      refine states_finite_step4_flag_halfspace_lem_relint.mpr
        ⟨hρe x0 hx0s ?_, ρ / 2, half_pos hρ, fun y hy hyd => hρe y hy ?_⟩
      · linarith [min_le_right r (ρ / 2)]
      · linarith [dist_triangle y x0 z0, min_le_right r (ρ / 2)]
    have hxE : (placedTraceOwner N n n F a).prototypeFrame 0 x0 ∈
        relint ((placedTraceOwner N n n F a).cell 0 e.val) := by
      rw [FramedNode.cell, restrictionOp_source_step5_relint_image]
      exact Set.mem_image_of_mem _ hx0r
    exact Set.disjoint_left.mp hhF (hEH hxE) hxY
  · have htd : traceDimension d = 1 := by unfold traceDimension; omega
    have hspan : affineSpan ℝ ((placedTraceOwner N n n F a).cell 0 e.val) =
        affineSpan ℝ (placedTraceCarrier N n n F a) := by
      apply actualCont_exists_step3_trace_successor_step6_fill_step2_span_of_finrank hbot
        ⟨z, intrinsicInterior_subset hz⟩
      rw [hX]
      unfold FramedNode.cell
      rw [actualCont_exists_step3_trace_successor_step6_fill_step2_finrank_image,
        actualCont_exists_step3_trace_successor_step6_fill_step2_finrank_image]
      have h1 := a.bottom.val.flat.dimension
      have h2 := e.val.flat.dimension
      unfold cellDirection at h1 h2
      omega
    have hzX := actualCont_exists_step3_trace_successor_step6_fill_step2_relint_mono hbot hspan hz
    obtain ⟨-, ρ, hρ, hρX⟩ := states_finite_step4_flag_halfspace_lem_relint.mp hzX
    refine ⟨ρ / 2, half_pos hρ, fun x hx hxX _ => states_finite_step4_flag_halfspace_lem_relint.mpr
      ⟨hxX, ρ / 2, half_pos hρ, fun y hy hyd => hρX y hy ?_⟩⟩
    have := dist_triangle y x z
    rw [mem_ball] at hx
    linarith

open private states_finite_step4_flag_halfspace_lem_relint
  states_finite_step4_flag_halfspace_lem_local_frontier
  states_finite_step4_flag_halfspace_lem_functional
  states_finite_step4_flag_halfspace_lem_dichotomy
  states_finite_step4_flag_halfspace_lem_closure from Enforce.State.State in
/-- Step 4 of the V4 proof of `actualCont_exists_step3_trace_successor_step6_fill`
(V4 1.0(a), (H2)): "a half-disc", in prototype coordinates: near a relative-interior
point `a` of a listed codimension-one subcell `e` of a listed cell `C`, the relative
interior of `C` is exactly one open side of `aff e` in `aff C` (as in
`states_finite_step4_flag_halfspace_lem_cell`). -/
private theorem actualCont_exists_step3_trace_successor_step6_fill_step4_proto_side
    {A : PolyManifoldDomain d} (K : CellComplex A) {e C : Cell d}
    (he : e ∈ K.cells) (hC : C ∈ K.cells) (hsub : e.carrier ⊆ C.carrier)
    (hdim : C.dim = e.dim + 1) {a : E d} (ha : a ∈ relint e.carrier) :
    ∃ ℓ : E d →ₗ[ℝ] ℝ, ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball a r,
      (x ∈ relint C.carrier ↔ x ∈ affineSpan ℝ C.carrier ∧ ℓ a < ℓ x) := by
  have hWV : cellDirection e.carrier ≤ cellDirection C.carrier :=
    AffineSubspace.direction_le (affineSpan_mono ℝ hsub)
  have hfin : Module.finrank ℝ (cellDirection C.carrier) =
      Module.finrank ℝ (cellDirection e.carrier) + 1 := by
    rw [C.flat.dimension, e.flat.dimension, hdim]
  obtain ⟨ℓ, n, hnV, hℓn, hker⟩ := states_finite_step4_flag_halfspace_lem_functional hWV hfin
  have hcl : IsClosed C.carrier := C.flat.compact.isClosed
  have hae : a ∈ e.carrier := intrinsicInterior_subset ha
  have haC : a ∈ C.carrier := hsub hae
  have haeS : a ∈ affineSpan ℝ e.carrier := subset_affineSpan ℝ _ hae
  have haCS : a ∈ affineSpan ℝ C.carrier := subset_affineSpan ℝ _ haC
  have hne : e ≠ C := by
    intro h
    rw [h] at hdim
    omega
  have hdisj := K.relint_disjoint e he C hC hne
  have hnotint : a ∉ relint C.carrier := fun h => Set.disjoint_left.mp hdisj ha h
  obtain ⟨r, hr, hloc⟩ := states_finite_step4_flag_halfspace_lem_local_frontier K he hC hdim ha
  obtain ⟨-, ρ, hρ, hρe⟩ := states_finite_step4_flag_halfspace_lem_relint.mp ha
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
  have hline : ∀ x ∈ ball a (ρ / 2), x ∈ affineSpan ℝ C.carrier → ℓ x = ℓ a →
      x ∉ relint C.carrier := by
    intro x hx hxS hxl hxi
    have hxa : dist x a < ρ / 2 := hx
    have hW : x - a ∈ cellDirection e.carrier := by
      have h' : x - a ∈ {x | x ∈ cellDirection C.carrier ∧ ℓ x = 0} :=
        ⟨by simpa only [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hxS haCS,
          by rw [map_sub, hxl, sub_self]⟩
      rw [hker] at h'
      exact h'
    have hxe : x ∈ affineSpan ℝ e.carrier := by
      have := AffineSubspace.vadd_mem_of_mem_direction hW haeS
      simpa only [vadd_eq_add, sub_add_cancel] using this
    have hxr : x ∈ relint e.carrier := states_finite_step4_flag_halfspace_lem_relint.mpr
      ⟨hρe x hxe (by linarith), ρ / 2, half_pos hρ, fun y hy hyd =>
        hρe y hy (by linarith [dist_triangle y x a])⟩
    exact Set.disjoint_left.mp hdisj hxr hxi
  have hd1 := states_finite_step4_flag_halfspace_lem_dichotomy hcl ℓ a r
    (fun x hx hxS hxl hxC => hoff x hx hxS hxl.ne' hxC)
  have hd2 := states_finite_step4_flag_halfspace_lem_dichotomy hcl (-ℓ) a r
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
    refine states_finite_step4_flag_halfspace_lem_relint.mpr ⟨haC, r, hr, fun y hy hyd => ?_⟩
    rcases le_total (ℓ a) (ℓ y) with hle | hle
    · exact states_finite_step4_flag_halfspace_lem_closure hcl ℓ a n r hnS hℓn h1 hyd hy hle
    · exact states_finite_step4_flag_halfspace_lem_closure hcl (-ℓ) a (-n) r hnS' hℓn' h2
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
    obtain ⟨hzC, ρ, hρ, hzρ⟩ := states_finite_step4_flag_halfspace_lem_relint.mp hz
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
  have key : ∀ m : E d →ₗ[ℝ] ℝ, (∀ x, m x = m a ↔ ℓ x = ℓ a) →
      (∀ x ∈ ball a r, x ∈ affineSpan ℝ C.carrier → m a < m x → x ∈ C.carrier) →
      (∀ x ∈ ball a r, x ∈ affineSpan ℝ C.carrier → m x < m a → x ∉ C.carrier) →
      ∃ ℓ : E d →ₗ[ℝ] ℝ, ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball a r,
        (x ∈ relint C.carrier ↔ x ∈ affineSpan ℝ C.carrier ∧ ℓ a < ℓ x) := by
    intro m hm hpos hneg
    refine ⟨m, min r (ρ / 2), lt_min hr (half_pos hρ), fun x hx => ⟨fun hxi => ?_, ?_⟩⟩
    · have hxC := intrinsicInterior_subset hxi
      have hxS : x ∈ affineSpan ℝ C.carrier := subset_affineSpan ℝ _ hxC
      refine ⟨hxS, ?_⟩
      rcases lt_trichotomy (m a) (m x) with h | h | h
      · exact h
      · exact absurd hxi (hline x (ball_subset_ball (min_le_right _ _) hx) hxS
          ((hm x).mp h.symm))
      · exact absurd hxC (hneg x (ball_subset_ball (min_le_left _ _) hx) hxS h)
    · rintro ⟨hxS, hxl⟩
      have hxb := ball_subset_ball (min_le_left _ _) hx
      exact hoff x hxb hxS (fun h => hxl.ne' ((hm x).mpr h)) (hpos x hxb hxS hxl)
  rcases hd1 with h1 | h1
  · rcases hd2 with h2 | h2
    · exact (hnotboth ⟨h1, h2⟩).elim
    · exact key ℓ (fun x => Iff.rfl) h1 (fun x hx hxS hxl => h2 x hx hxS (by simpa using hxl))
  · rcases hd2 with h2 | h2
    · exact key (-ℓ) (fun x => by simp) h2 (fun x hx hxS hxl => h1 x hx hxS (by simpa using hxl))
    · exact (hnotnone ⟨h1, h2⟩).elim

/-- Step 4 of the V4 proof of `actualCont_exists_step3_trace_successor_step6_fill`
(V4 1.0(a), (H2)): "a half-disc of F_2 at v", case `d ≥ 3` (`F_2` is a polygon): at a
relative-interior point `z` of the flag edge `h`, the polygon `F_2` is locally a closed
half-disc of its plane bounded by the line of `h` (the relative boundary of `F_2` near
`z` is `h`, and each of the two open half-discs is inside or outside `F_2`, as in
`states_finite_step4_flag_halfspace_lem_cell`; not both, since `relint h` is disjoint
from `relint F_2`, and not neither, since `F_2` is the closure of its relative
interior). Hence `relint F_2` meets small balls at `z` in a convex (affine image of an
open half-disc) and so connected set. -/
private theorem actualCont_exists_step3_trace_successor_step6_fill_step4_polygon_halfdisc
    (N : FramedNode S) (n : ℕ) (F : FacetFlag S N.ty) (z : E d) (hd : 2 < d)
    (hzh : z ∈ relint (N.cell n (F.cell edgeIndex).val)) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
      IsPreconnected (relint (N.cell n
        (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val) ∩ ball z r) := by
  classical
  have hd2 : 2 ≤ d := Fact.out
  have htd : traceDimension d = 2 := by unfold traceDimension; omega
  have hhC : (F.cell edgeIndex).val ∈ (S.cx N.ty).cells := (F.cell edgeIndex).property
  have hPC := (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).property
  have hsub : (F.cell edgeIndex).val.carrier ⊆
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.carrier :=
    F.nested _ _ traceDimension_pos
  have hdim : (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.dim =
      (F.cell edgeIndex).val.dim + 1 := by
    have h1 : (F.cell edgeIndex).val.dim = 1 := F.dimension edgeIndex
    have h2 : (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.dim =
      traceDimension d := F.dimension _
    omega
  have hz' := hzh
  rw [FramedNode.cell, restrictionOp_source_step5_relint_image] at hz'
  obtain ⟨z0, hz0, rfl⟩ := hz'
  obtain ⟨ℓ, r, hr, hloc⟩ :=
    actualCont_exists_step3_trace_successor_step6_fill_step4_proto_side (S.cx N.ty) hhC hPC
      hsub hdim hz0
  have hcont : Continuous (N.prototypeFrame n).symm :=
    (N.prototypeFrame n).symm.toHomeomorphOfFiniteDimensional.continuous
  obtain ⟨δ, hδ, hδr⟩ := Metric.continuous_iff.mp hcont (N.prototypeFrame n z0) r hr
  have hback : ∀ x : E d, dist (N.prototypeFrame n x) (N.prototypeFrame n z0) < δ →
      x ∈ ball z0 r := by
    intro x hx
    have := hδr (N.prototypeFrame n x) hx
    simpa using this
  refine ⟨δ, hδ, fun s hs hsδ => ?_⟩
  have heq : relint (N.cell n
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val) ∩
        ball (N.prototypeFrame n z0) s =
      (N.prototypeFrame n).toAffineMap ''
        ({x | x ∈ affineSpan ℝ
          (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.carrier ∧
            ℓ z0 < ℓ x} ∩
          (N.prototypeFrame n).toAffineMap ⁻¹' ball (N.prototypeFrame n z0) s) := by
    rw [FramedNode.cell, restrictionOp_source_step5_relint_image]
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hyb⟩
      have hxb := hback x (lt_of_lt_of_le hyb hsδ)
      exact ⟨x, ⟨(hloc x hxb).mp hx, hyb⟩, rfl⟩
    · rintro ⟨x, ⟨hxA, hxb⟩, rfl⟩
      have hxb' := hback x (lt_of_lt_of_le hxb hsδ)
      exact ⟨⟨x, (hloc x hxb').mpr hxA, rfl⟩, hxb⟩
  rw [heq]
  apply Convex.isPreconnected
  apply Convex.affine_image
  exact ((affineSpan ℝ _).convex.inter (convex_halfSpace_gt ℓ.isLinear _)).inter
    ((convex_ball _ _).affine_preimage _)

open private states_finite_step4_flag_halfspace_lem_relint from Enforce.State.State in
/-- Step 4 of the V4 proof of `actualCont_exists_step3_trace_successor_step6_fill`
(V4 1.0(a), (H2)): "a half-disc of F_2 at v": at a relative-interior point of the flag
edge `h`, the bottom flag cell `F_2` is locally a closed half-disc of its plane bounded
by the line of `h` (by the dichotomy of the two open half-discs, as for
`states_finite_step4_flag_halfspace`), so its relative interior meets small balls in
an open half-disc, which is connected. (For `d = 2`, `F_2 = h` and the intersection
is an open segment.) -/
private theorem actualCont_exists_step3_trace_successor_step6_fill_step4_flag_halfdisc
    (N : FramedNode S) (n : ℕ) (F : FacetFlag S N.ty) (z : E d)
    (hzh : z ∈ relint (N.cell n (F.cell edgeIndex).val)) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
      IsPreconnected (relint (N.cell n
        (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val) ∩ ball z r) := by
  have hd2 : 2 ≤ d := Fact.out
  rcases Nat.lt_or_ge 2 d with hd | hd
  · exact actualCont_exists_step3_trace_successor_step6_fill_step4_polygon_halfdisc N n F z hd hzh
  · have hidx : (⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩ : FlagIndex d) =
        edgeIndex := Subtype.ext (show traceDimension d = 1 by unfold traceDimension; omega)
    rw [hidx]
    obtain ⟨-, ρ, hρ, hρY⟩ := states_finite_step4_flag_halfspace_lem_relint.mp hzh
    refine ⟨ρ / 2, half_pos hρ, fun r hr hrρ => ?_⟩
    have heq : relint (N.cell n (F.cell edgeIndex).val) ∩ ball z r =
        (affineSpan ℝ (N.cell n (F.cell edgeIndex).val) : Set (E d)) ∩ ball z r := by
      apply Set.Subset.antisymm
      · exact fun x hx => ⟨subset_affineSpan ℝ _ (intrinsicInterior_subset hx.1), hx.2⟩
      · rintro x ⟨hxs, hxb⟩
        have hxb' : dist x z < r := hxb
        refine ⟨states_finite_step4_flag_halfspace_lem_relint.mpr ⟨hρY x hxs (by linarith),
          ρ / 2, half_pos hρ, fun y hy hyd => hρY y hy ?_⟩, hxb⟩
        linarith [dist_triangle y x z]
    rw [heq]
    exact ((affineSpan ℝ _).convex.inter (convex_ball z r)).isPreconnected

open private states_finite_step4_flag_halfspace_lem_relint from Enforce.State.State in
/-- Step 5 of the V4 proof of `actualCont_exists_step3_trace_successor_step6_fill`
(V4 2.8): "would fill a half-disc of F_2 at v": if a closed piece `X ⊆ Y` of the same
span has no relative boundary inside `relint Y` near `z`, meets every ball at `z` in
its relative interior, and `relint Y` is connected near `z`, then the two relative
interiors coincide near `z` (a clopen argument). -/
private theorem actualCont_exists_step3_trace_successor_step6_fill_step5_clopen
    {X Y : Set (E d)} {z : E d} {r : ℝ}
    (hsub : X ⊆ Y) (hspan : affineSpan ℝ X = affineSpan ℝ Y) (hcl : IsClosed X)
    (hX : ∀ x ∈ ball z r, x ∈ X → x ∈ relint Y → x ∈ relint X)
    (hconn : IsPreconnected (relint Y ∩ ball z r))
    (hdense : ∃ w ∈ relint X, dist w z < r) :
    relint X ∩ ball z r = relint Y ∩ ball z r := by
  have hrel : relint X ⊆ relint Y :=
    actualCont_exists_step3_trace_successor_step6_fill_step2_relint_mono hsub hspan
  refine Set.Subset.antisymm (fun x hx => ⟨hrel hx.1, hx.2⟩) ?_
  let U : Set (E d) := {x | ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ affineSpan ℝ X, dist y x < ρ → y ∈ X}
  have hU : IsOpen U := by
    rw [Metric.isOpen_iff]
    rintro x ⟨ρ, hρ, hx⟩
    refine ⟨ρ / 2, half_pos hρ, fun q hq => ⟨ρ / 2, half_pos hρ, fun y hy hyq => hx y hy ?_⟩⟩
    have := dist_triangle y q x
    rw [mem_ball] at hq
    linarith
  have hspanY : ∀ x ∈ relint Y, x ∈ affineSpan ℝ X := by
    intro x hx
    rw [hspan]
    exact subset_affineSpan ℝ _ (intrinsicInterior_subset hx)
  obtain ⟨w, hw, hwz⟩ := hdense
  have hcover : relint Y ∩ ball z r ⊆ U ∪ Xᶜ := by
    rintro x ⟨hxY, hxb⟩
    by_cases hxX : x ∈ X
    · exact Or.inl (states_finite_step4_flag_halfspace_lem_relint.mp (hX x hxb hxX hxY)).2
    · exact Or.inr hxX
  have hdisj : relint Y ∩ ball z r ∩ (U ∩ Xᶜ) = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro x ⟨⟨hxY, _⟩, ⟨ρ, hρ, hρx⟩, hxX⟩
    exact hxX (hρx x (hspanY x hxY) (by simpa using hρ))
  rcases (isPreconnected_iff_subset_of_disjoint.mp hconn) U Xᶜ hU hcl.isOpen_compl hcover
      hdisj with h | h
  · rintro x ⟨hxY, hxb⟩
    obtain ⟨ρ, hρ, hρx⟩ := h ⟨hxY, hxb⟩
    exact ⟨hX x hxb (hρx x (hspanY x hxY) (by simpa using hρ)) hxY, hxb⟩
  · exact absurd (intrinsicInterior_subset hw) (h ⟨hrel hw, by rwa [mem_ball]⟩)


/-- Step 6 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 2.8, 1.0(a)):
"a polygon containing v in the relative interior of its edge along h would fill a
half-disc of F_2 at v". If a point lies in the relative interior of a listed owner
edge which lies along the flag edge and in the trace piece, then near that point the
relative interior of the trace piece coincides with the relative interior of the
bottom flag cell `F_2` (for `d = 2`: of the flag edge `h` itself). -/
private theorem actualCont_exists_step3_trace_successor_step6_fill (N : FramedNode S)
    (n : ℕ) (F : FacetFlag S N.ty) (a : TracePiece N.ty F n)
    (e : PrototypeEdge S (placedTraceOwner N n n F a).ty) (z : E d)
    (hbot : (placedTraceOwner N n n F a).cell 0 e.val ⊆ placedTraceCarrier N n n F a)
    (hflag : (placedTraceOwner N n n F a).cell 0 e.val ⊆ N.cell n (F.cell edgeIndex).val)
    (hz : z ∈ relint ((placedTraceOwner N n n F a).cell 0 e.val)) :
    ∃ r : ℝ, 0 < r ∧ relint (placedTraceCarrier N n n F a) ∩ ball z r =
      relint (N.cell n
        (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val) ∩ ball z r := by
  classical
  have hzh : z ∈ relint (N.cell n (F.cell edgeIndex).val) := by
    have hspanE := actualCont_exists_step3_trace_successor_step6_fill_step2_edge_span N n F a e
      hflag
    exact actualCont_exists_step3_trace_successor_step6_fill_step2_relint_mono hflag hspanE hz
  have hzX : z ∈ placedTraceCarrier N n n F a := hbot (intrinsicInterior_subset hz)
  have hcl : IsClosed (placedTraceCarrier N n n F a) := by
    rw [actualCont_exists_step3_trace_successor_step2_carrier N n F a]
    change IsClosed ((placedTraceOwner N n n F a).frame '' a.bottom.val.carrier)
    exact (a.bottom.val.flat.compact.image (placedTraceOwner N n n F a).frame.continuous).isClosed
  have hdense : ∀ ε : ℝ, 0 < ε →
      ∃ w ∈ relint (placedTraceCarrier N n n F a), dist w z < ε := by
    intro ε hε
    have hzC := hzX
    rw [actualCont_exists_step3_trace_successor_step2_carrier N n F a] at hzC ⊢
    obtain ⟨z0, hz0, hz0e⟩ := hzC
    have hK := a.bottom.val.flat.regularClosed
    rw [← hK] at hz0
    obtain ⟨w0, hw0, hdist⟩ := Metric.mem_closure_iff.mp hz0 ε hε
    let C := placedTraceOwner N n n F a
    refine ⟨C.frame w0, ?_, ?_⟩
    · change C.frame w0 ∈ intrinsicInterior ℝ (C.frame.toAffineIsometry '' a.bottom.val.carrier)
      rw [C.frame.toAffineIsometry.image_intrinsicInterior]
      exact Set.mem_image_of_mem _ hw0
    · rw [← hz0e]
      change dist (C.frame w0) (C.frame z0) < ε
      rw [C.frame.dist_map, dist_comm]
      exact hdist
  obtain ⟨r1, hr1, hX⟩ :=
    actualCont_exists_step3_trace_successor_step6_fill_step3_owner_frontier N n F a e z
      hbot hflag hz
  obtain ⟨r0, hr0, hconn⟩ :=
    actualCont_exists_step3_trace_successor_step6_fill_step4_flag_halfdisc N n F z hzh
  have hr : 0 < min r0 r1 := lt_min hr0 hr1
  refine ⟨min r0 r1, hr, ?_⟩
  exact actualCont_exists_step3_trace_successor_step6_fill_step5_clopen
    (actualCont_exists_step3_trace_successor_step6_fill_step1_subset N n F a)
    (actualCont_exists_step3_trace_successor_step6_fill_step2_span N n F a) hcl
    (fun x hx => hX x (ball_subset_ball (min_le_right _ _) hx))
    (hconn _ hr (min_le_left _ _)) (hdense _ hr)

/-- Step 7 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 2.8, 1.22(a)):
"v is a vertex of s_2'': a polygon containing v in the relative interior of its
edge along h would fill a half-disc of F_2 at v, overlapping s_2". Two distinct
trace pieces cannot have listed edges along the flag edge, one ending at `v` and
the other containing `v` in its relative interior: near `v` both pieces would
contain the same half-disc (for `d = 2`, the same half-neighbourhood in `h`),
contradicting the disjoint relative interiors of the trace. -/
private theorem actualCont_exists_step3_trace_successor_step7_distinct_owner
    (N : FramedNode S) (n : ℕ) (F : FacetFlag S N.ty) (a b : TracePiece N.ty F n)
    (hab : a ≠ b) (e : PrototypeEdge S (placedTraceOwner N n n F a).ty)
    (e' : PrototypeEdge S (placedTraceOwner N n n F b).ty) (p v x y : E d) (hne : p ≠ v)
    (hseg : (placedTraceOwner N n n F a).cell 0 e.val = segment ℝ p v)
    (hseg' : (placedTraceOwner N n n F b).cell 0 e'.val = segment ℝ x y)
    (hbot : (placedTraceOwner N n n F a).cell 0 e.val ⊆ placedTraceCarrier N n n F a)
    (hbot' : (placedTraceOwner N n n F b).cell 0 e'.val ⊆ placedTraceCarrier N n n F b)
    (hflag : (placedTraceOwner N n n F a).cell 0 e.val ⊆ N.cell n (F.cell edgeIndex).val)
    (hflag' : (placedTraceOwner N n n F b).cell 0 e'.val ⊆ N.cell n (F.cell edgeIndex).val)
    (hxy : x ≠ y) (hv : v ∈ openSegment ℝ x y) : False := by
  obtain ⟨rb, hrb, hfb⟩ := actualCont_exists_step3_trace_successor_step6_fill N n F b e' v
    hbot' hflag' (hseg' ▸ actualCont_exists_step3_trace_successor_step1_open_relint x y hxy hv)
  have hpv : 0 < ‖v - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  let s : ℝ := min (1 / 2) (rb / (2 * (‖v - p‖ + 1)))
  have hden : 0 < 2 * (‖v - p‖ + 1) := by positivity
  have hs0 : 0 < s := lt_min (by norm_num) (div_pos hrb hden)
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hsr : s * ‖v - p‖ < rb / 2 := by
    have h1 : s ≤ rb / (2 * (‖v - p‖ + 1)) := min_le_right _ _
    have h2 : s * (2 * (‖v - p‖ + 1)) ≤ rb := (le_div_iff₀ hden).mp h1
    nlinarith
  let zs : E d := v - s • (v - p)
  have hzs_open : zs ∈ openSegment ℝ p v :=
    ⟨s, 1 - s, hs0, by linarith, by ring, by simp only [zs]; module⟩
  have hzs_rel : zs ∈ relint ((placedTraceOwner N n n F a).cell 0 e.val) :=
    hseg ▸ actualCont_exists_step3_trace_successor_step1_open_relint p v hne hzs_open
  have hzs_v : dist zs v < rb / 2 := by
    change dist (v - s • (v - p)) v < rb / 2
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs0]
    exact hsr
  obtain ⟨ra, hra, hfa⟩ := actualCont_exists_step3_trace_successor_step6_fill N n F a e zs
    hbot hflag hzs_rel
  have hzsC : zs ∈ placedTraceCarrier N n n F a := hbot (intrinsicInterior_subset hzs_rel)
  rw [actualCont_exists_step3_trace_successor_step2_carrier N n F a] at hzsC
  obtain ⟨z0, hz0, hz0e⟩ := hzsC
  have hK := a.bottom.val.flat.regularClosed
  rw [← hK] at hz0
  obtain ⟨w0, hw0, hdist⟩ := Metric.mem_closure_iff.mp hz0 (min ra (rb / 2))
    (lt_min hra (by linarith))
  let C := placedTraceOwner N n n F a
  have hwrel : C.frame w0 ∈ relint (placedTraceCarrier N n n F a) := by
    rw [actualCont_exists_step3_trace_successor_step2_carrier N n F a]
    change C.frame w0 ∈ intrinsicInterior ℝ (C.frame.toAffineIsometry '' a.bottom.val.carrier)
    rw [C.frame.toAffineIsometry.image_intrinsicInterior]
    exact Set.mem_image_of_mem _ hw0
  have hdw : dist (C.frame w0) zs < min ra (rb / 2) := by
    rw [← hz0e]
    change dist (C.frame w0) (C.frame z0) < _
    rw [C.frame.dist_map, dist_comm]
    exact hdist
  have hwX : C.frame w0 ∈ relint (N.cell n
      (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val) ∩ ball zs ra := by
    rw [← hfa]
    exact ⟨hwrel, lt_of_lt_of_le hdw (min_le_left _ _)⟩
  have hwv : C.frame w0 ∈ ball v rb := by
    have h1 := lt_of_lt_of_le hdw (min_le_right _ _)
    change dist (C.frame w0) v < rb
    linarith [dist_triangle (C.frame w0) zs v]
  have hwb : C.frame w0 ∈ relint (placedTraceCarrier N n n F b) ∩ ball v rb := by
    rw [hfb]
    exact ⟨hwX.1, hwv⟩
  exact Set.disjoint_left.mp ((placed_recursiveTrace_tiles N n n le_rfl F).2 hab) hwrel hwb.1

/-- Step 8 of the V4 proof of `actualCont_exists_step3_trace_successor` (V4 2.8, (H2)(ii)):
"t'' is a native tile with v as a listed vertex (vertex of a cell)". An endpoint
of a listed edge is a listed vertex: the relative boundary of the edge is its two
endpoints and is a union of listed cells, which must be zero-cells. -/
private theorem actualCont_exists_step3_trace_successor_step8_endpoint_vertex {A : S.ι}
    (e : PrototypeEdge S A) (x y : E d) (hxy : x ≠ y)
    (h : e.val.carrier = segment ℝ x y) : ∃ w : VertexName S A, vertexPoint w = x := by
  classical
  have hec : e.val ∈ (S.cx A).cells := (Finset.mem_filter.mp e.property).1
  obtain ⟨bs, hbs, hunion⟩ := (S.cx A).boundary_union e.val hec
  have hclosed : IsClosed (segment ℝ x y) := h ▸ e.val.flat.compact.isClosed
  have hxf : x ∈ relfrontier (segment ℝ x y) := by
    unfold relfrontier
    rw [← intrinsicClosure_diff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure (left_mem_segment ℝ x y),
      actualCont_exists_step3_trace_successor_step1_endpoint x y hxy⟩
  have hfront : relfrontier (segment ℝ x y) ⊆ {x, y} := by
    intro z hz
    have hz' := hz
    unfold relfrontier at hz'
    rw [← intrinsicClosure_diff_intrinsicInterior] at hz'
    have hzs : z ∈ segment ℝ x y := intrinsicFrontier_subset hclosed hz
    by_contra hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    exact hz'.2 (actualCont_exists_step3_trace_successor_step1_open_relint x y hxy
      (mem_openSegment_of_ne_left_right (Ne.symm hne.1) (Ne.symm hne.2) hzs))
  rw [← h] at hxf hfront
  rw [hunion] at hxf hfront
  obtain ⟨f, hf, hxf'⟩ := mem_iUnion₂.mp hxf
  have hfsub : f.carrier ⊆ {x, y} := fun z hz => hfront (mem_iUnion₂.mpr ⟨f, hf, hz⟩)
  have hfx : f.carrier = {x} := by
    apply Set.Subset.antisymm _ (Set.singleton_subset_iff.mpr hxf')
    intro z hz
    rcases hfsub hz with hzx | hzy
    · exact hzx
    · exfalso
      subst hzy
      have hcon : IsPreconnected ((fun q : E d => dist q x) '' f.carrier) :=
        f.flat.connected.isPreconnected.image _ (continuous_id.dist continuous_const).continuousOn
      have hsub := hcon.Icc_subset (Set.mem_image_of_mem _ hxf') (Set.mem_image_of_mem _ hz)
      have hpos : 0 < dist z x := dist_pos.mpr hxy.symm
      have hmid : dist z x / 2 ∈ Set.Icc (dist x x) (dist z x) := by
        rw [dist_self]
        constructor <;> linarith
      obtain ⟨q, hq, hqd⟩ := hsub hmid
      rcases hfsub hq with rfl | rfl
      · simp only [dist_self] at hqd
        linarith
      · simp only at hqd
        linarith
  have hdim : f.dim = 0 := by
    have hd := f.flat.dimension
    have h0 : Module.finrank ℝ (affineSpan ℝ ({x} : Set (E d))).direction = 0 := by
      rw [direction_affineSpan, vectorSpan_singleton, finrank_bot]
    rw [hfx] at hd
    unfold cellDirection at hd
    exact hd.symm.trans h0
  let w : VertexName S A := ⟨f, Finset.mem_filter.mpr ⟨hbs hf, hdim⟩⟩
  refine ⟨w, ?_⟩
  have hw := vertexPoint_spec w
  change f.carrier = {vertexPoint w} at hw
  rw [hfx] at hw
  exact (Set.singleton_eq_singleton_iff.mp hw).symm

/-- Step 3 of the V4 proof of `actualCont_exists` (V4 2.8):
"there is a polygon ... on the far side of v ... with an edge ... with initial
endpoint v". In the recursive trace, a boundary edge ending inside the flag
edge has a next listed edge, possibly in the same owner. This is solely the
local trace geometry; it makes no assertion about records or template labels. -/
private theorem actualCont_exists_step3_trace_successor (N : FramedNode S) (n : ℕ)
    (F : FacetFlag S N.ty) (a : TracePiece N.ty F n) (e : Cell d)
    (he : e ∈ (S.cx (placedTraceOwner N n n F a).ty).edges) (p v : E d)
    (hne : p ≠ v) (hseg : (placedTraceOwner N n n F a).cell 0 e = segment ℝ p v)
    (hbottom : (placedTraceOwner N n n F a).cell 0 e ⊆
      placedTraceCarrier N n n F a)
    (hflag : (placedTraceOwner N n n F a).cell 0 e ⊆
      N.cell n (F.cell edgeIndex).val)
    (hv : v ∈ relint (N.cell n (F.cell edgeIndex).val)) :
    ∃ (b : TracePiece N.ty F n)
      (e' : PrototypeEdge S (placedTraceOwner N n n F b).ty)
      (v' : VertexName S (placedTraceOwner N n n F b).ty) (w : E d),
      (placedTraceOwner N n n F b).frame (vertexPoint v') = v ∧
      (placedTraceOwner N n n F b).cell 0 e'.val = segment ℝ v w ∧
      v ≠ w ∧ (∃ k : ℝ, 0 < k ∧ w - v = k • (v - p)) ∧
      (placedTraceOwner N n n F b).cell 0 e'.val ⊆
        placedTraceCarrier N n n F b ∧
      (placedTraceOwner N n n F b).cell 0 e'.val ⊆
        N.cell n (F.cell edgeIndex).val := by
  classical
  obtain ⟨b, e', t, ht, hve, hte, hflag', hbot'⟩ :=
    actualCont_exists_step3_trace_successor_step3_edge_germ N n F p v hne
      (hflag (hseg ▸ left_mem_segment ℝ p v)) hv
  obtain ⟨⟨x0, y0⟩, hxy0, hseg0⟩ :=
    edge_endpoints_exist (⟨(placedTraceOwner N n n F b).ty, e'⟩ : EdgeName S)
  have hcell : (placedTraceOwner N n n F b).cell 0 e'.val =
      segment ℝ ((placedTraceOwner N n n F b).prototypeFrame 0 x0)
        ((placedTraceOwner N n n F b).prototypeFrame 0 y0) := by
    change (placedTraceOwner N n n F b).prototypeFrame 0 '' e'.val.carrier = _
    rw [hseg0]
    exact image_segment ℝ ((placedTraceOwner N n n F b).prototypeFrame 0).toAffineMap x0 y0
  have hframe (z : E d) : (placedTraceOwner N n n F b).prototypeFrame 0 z =
      (placedTraceOwner N n n F b).frame z := rfl
  rw [hframe, hframe] at hcell
  have hnotopen : v ∉ openSegment ℝ ((placedTraceOwner N n n F b).frame x0)
      ((placedTraceOwner N n n F b).frame y0) := by
    intro hvo
    by_cases hab : a = b
    · subst hab
      exact actualCont_exists_step3_trace_successor_step5_same_owner
        (placedTraceOwner N n n F a) ⟨e, he⟩ e' p v _ _ t ht hne hseg hcell hvo
        (hcell ▸ hte)
    · exact actualCont_exists_step3_trace_successor_step7_distinct_owner N n F a b hab
        ⟨e, he⟩ e' p v _ _ hne hseg hcell hbottom hbot' hflag hflag'
        (fun h => hxy0 ((placedTraceOwner N n n F b).frame.injective h)) hvo
  have hvseg := hcell ▸ hve
  have hend : v = (placedTraceOwner N n n F b).frame x0 ∨
      v = (placedTraceOwner N n n F b).frame y0 := by
    by_contra hh
    push_neg at hh
    exact hnotopen (mem_openSegment_of_ne_left_right (Ne.symm hh.1) (Ne.symm hh.2) hvseg)
  have hu : v - p ≠ 0 := sub_ne_zero.mpr hne.symm
  rcases hend with hx | hy
  · obtain ⟨w', hw'⟩ := actualCont_exists_step3_trace_successor_step8_endpoint_vertex
      e' x0 y0 hxy0 hseg0
    have hseg1 : (placedTraceOwner N n n F b).cell 0 e'.val =
        segment ℝ v ((placedTraceOwner N n n F b).frame y0) := by rw [hcell, hx]
    obtain ⟨k, hk, hkw⟩ := actualCont_exists_step3_trace_successor_step4_direction v _ (v - p)
      t ht hu (hseg1 ▸ hte)
    refine ⟨b, e', w', (placedTraceOwner N n n F b).frame y0, by rw [hw', hx], hseg1, ?_,
      ⟨k, hk, hkw⟩, hbot', hflag'⟩
    rw [hx]
    exact fun h => hxy0 ((placedTraceOwner N n n F b).frame.injective h)
  · obtain ⟨w', hw'⟩ := actualCont_exists_step3_trace_successor_step8_endpoint_vertex
      e' y0 x0 (Ne.symm hxy0) (hseg0.trans (segment_symm ℝ x0 y0))
    have hseg1 : (placedTraceOwner N n n F b).cell 0 e'.val =
        segment ℝ v ((placedTraceOwner N n n F b).frame x0) := by
      rw [hcell, hy, segment_symm]
    obtain ⟨k, hk, hkw⟩ := actualCont_exists_step3_trace_successor_step4_direction v _ (v - p)
      t ht hu (hseg1 ▸ hte)
    refine ⟨b, e', w', (placedTraceOwner N n n F b).frame x0, by rw [hw', hy], hseg1, ?_,
      ⟨k, hk, hkw⟩, hbot', hflag'⟩
    rw [hy]
    exact fun h => hxy0 ((placedTraceOwner N n n F b).frame.injective h).symm

/-- Step 4 of the V4 proof of `actualCont_exists` (V4 2.8):
"same ... serving child H". Reindexing the known height retains the exact
hierarchy node; membership proofs do not change its identity. -/
private theorem actualCont_exists_step4_reindex (U : HonestSource S) (H : U.Node)
    (n : ℕ) (hn : H.1 = n) (hN : H.2.val ∈ U.hierarchy.nodes n) :
    (⟨n, ⟨H.2.val, hN⟩⟩ : U.Node) = H := by
  rcases H with ⟨m, M⟩
  dsimp only at hn hN ⊢
  subst n
  rfl

/-- Step 4 of the V4 proof of `actualCont_exists` (V4 2.8):
"with owner t''". An exact native descendant address identifies the
ancestor in the fixed hierarchy, including its frame and its height. -/
private theorem actualCont_exists_step4_ancestor (U : HonestSource S)
    (q : U.Node) (hq : q.1 = 0) (n : ℕ) (N : FramedNode S)
    (hN : N ∈ U.hierarchy.nodes n) (w : S.RoleWord N.ty n)
    (hw : q.2.val = (S.nativeTile N.ty n w).move N.frame) :
    U.hierarchy.ancestor q n = ⟨n, ⟨N, hN⟩⟩ := by
  induction n generalizing N with
  | zero =>
    have hqN : q.2.val = N := by
      simpa [SubstSystem.nativeTile, SubstSystem.descendantNode, FramedNode.move] using hw
    change q = _
    rcases q with ⟨m, Q, hQ⟩
    dsimp only at hq hqN
    subst m
    cases hqN
    rfl
  | succ n ih =>
    let C := N.child n w.1
    have hC : C ∈ U.hierarchy.nodes n := U.hierarchy.children_mem n N hN w.1
    have hqC : q.2.val = (S.nativeTile C.ty n w.2).move C.frame := by
      rw [hw]
      apply FramedNode.ext
      · rfl
      · ext x
        simp [SubstSystem.nativeTile, SubstSystem.descendantNode, C,
          FramedNode.move, FramedNode.child]
    have ha := ih C hC w.2 hqC
    have hp : U.hierarchy.parentNode ⟨n, ⟨C, hC⟩⟩ = ⟨n+1, ⟨N, hN⟩⟩ := by
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Subtype.ext
        exact (U.hierarchy.parent_unique n ⟨C, hC⟩ N hN ⟨w.1, rfl⟩).symm
    change U.hierarchy.parentNode^[n+1] q = _
    rw [Function.iterate_succ_apply']
    change U.hierarchy.parentNode (U.hierarchy.ancestor q n) = _
    rw [ha]
    exact hp

/-- Step 4 of the V4 proof of `actualCont_exists` (V4 2.8):
"same provider g, same serving child H". Every descendant facet contained
in the serving facet inherits its provider, birth parent, and serving node. -/
private theorem actualCont_exists_step4_provider (U : HonestSource S) (P : Params S)
    (t q : U.Node) (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (g : FacetName S q.2.val.ty) (r : ℕ)
    (ha : U.hierarchy.ancestor q r = U.hierarchy.servingChild t f hf)
    (hsub : q.2.val.cell q.1 g.val ⊆ U.hierarchy.providerCarrier t f hf) :
    ∃ hg : ¬ U.hierarchy.IsFault q g,
      U.hierarchy.servingChild q g hg = U.hierarchy.servingChild t f hf ∧
      U.recordIncidence P q g hg = U.recordIncidence P t f hf ∧
      U.providerPlacement P q g hg = U.providerPlacement P t f hf := by
  let H := U.hierarchy.servingChild t f hf
  let F : FacetName S H.2.val.ty := (U.hierarchy.firstProvider t f hf).2
  have hint : relint (H.2.val.cell H.1 F.val) ⊆
      interior ((U.hierarchy.parentNode H).2.val.carrier (U.hierarchy.parentNode H).1) := by
    have h := (U.hierarchy.firstProvider_spec t f hf).2.2
    have hp : U.hierarchy.ancestor t ((U.hierarchy.firstProvider t f hf).1 + 1) =
        U.hierarchy.parentNode H := by
      simp only [H, CoherentHierarchy.servingChild, CoherentHierarchy.ancestor,
        Function.iterate_succ_apply']
    have heq := congrArg (fun B : U.Node => B.2.val.carrier B.1) hp
    exact h.trans_eq (congrArg interior heq)
  obtain ⟨hF, hcarrier, hbirth, _⟩ := U.hierarchy.restriction_det_internal H F hint
  obtain ⟨hg, hprovider, hbirth'⟩ := U.hierarchy.provider_inherited H q r ha F g hF hsub
  have hb : U.hierarchy.birthParent q g hg = U.hierarchy.birthParent t f hf :=
    hbirth'.trans hbirth
  have hc : U.hierarchy.providerCarrier q g hg = U.hierarchy.providerCarrier t f hf :=
    hprovider.trans hcarrier
  have hserv : U.hierarchy.servingChild q g hg = H := by
    have hheight := congrArg (fun B : U.Node => B.1) hb
    change (U.hierarchy.servingChild q g hg).1 + 1 = H.1 + 1 at hheight
    have hh := U.hierarchy.ancestor_height q (U.hierarchy.firstProvider q g hg).1
    have hh' := U.hierarchy.ancestor_height q r
    rw [ha] at hh'
    have hoff : (U.hierarchy.firstProvider q g hg).1 = r := by
      change H.1 = q.1 + r at hh'
      change (U.hierarchy.servingChild q g hg).1 =
        q.1 + (U.hierarchy.firstProvider q g hg).1 at hh
      omega
    simpa only [CoherentHierarchy.servingChild, hoff] using ha
  have hi := restrictionOp_source_step4_provider_name P U q t g f hg hf hb hc
  refine ⟨hg, hserv, hi, ?_⟩
  unfold HonestSource.providerPlacement CoherentHierarchy.birthHeight
  rw [hb, hi]

/-- Step 4 of the V4 proof of `actualCont_exists` (V4 2.8):
"by Remark 2.1 (converse part)". Reindex the selected trace by its owner's
actual serving node and depth, retaining the required top-facet equality. -/
private theorem actualCont_exists_step4_active (U : HonestSource S) (P : Params S)
    (q H : U.Node) (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g)
    (r : ℕ) (hH : U.hierarchy.servingChild q g hg = H)
    (hr : (U.hierarchy.firstProvider q g hg).1 = r)
    (F : FacetFlag S H.2.val.ty) (a : TracePiece H.2.val.ty F r)
    (hF : ∀ j, H.2.val.cell H.1 (F.cell j).val = U.providerPlacement P q g hg ''
      ((P.flag (U.recordIncidence P q g hg)).flag.cell j).val.carrier)
    (ha : placedTraceOwner H.2.val H.1 r F a = q.2.val)
    (htop : (a.chain.cell traceTopIndex).val = g.val)
    (e : PrototypeEdge S q.2.val.ty)
    (heB : q.2.val.cell q.1 e.val ⊆ placedTraceCarrier H.2.val H.1 r F a)
    (heh : q.2.val.cell q.1 e.val ⊆ U.providerPlacement P q g hg ''
      ((P.flag (U.recordIncidence P q g hg)).flag.cell edgeIndex).val.carrier) :
    (U.recordOf P q g hg).ChainActive (edgeCell e) := by
  subst H
  subst r
  exact chain_active_owner_converse U P q g hg F hF a ha htop (edgeCell e)
    (Finset.mem_filter.mp e.property).2 heB heh

open private solidAngle_constant_on_cell_step2_fill solidAngle_constant_on_cell_step4_common_ball
  from Enforce.Geometry.CellComplex in
/-- Step 1 of the V4 proof of `actualCont_exists_step5_coface_side` (V4 1.0(b)):
"the local structure is constant by (a) applied to the cell complex". Induction
through the finite boundary complex proves both incidence and local translation
invariance of a listed carrier in the directions of the cell containing the base point. -/
private lemma actualCont_exists_step5_coface_side_step1_cell_invariance
    {A : PolyManifoldDomain d} (K : CellComplex A) (e : Cell d) (he : e ∈ K.cells)
    (p : E d) (hp : p ∈ relint e.carrier) (f : Cell d) (hf : f ∈ K.cells) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
      y - x ∈ cellDirection e.carrier → (x ∈ f.carrier ↔ y ∈ f.carrier) := by
  classical
  let N (f : Cell d) := (K.cells.filter fun g => g.carrier ⊆ f.carrier).card
  have main : ∀ n : ℕ, ∀ f : Cell d, f ∈ K.cells → N f = n →
      (p ∈ f.carrier → e.carrier ⊆ f.carrier) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
        y - x ∈ cellDirection e.carrier → (x ∈ f.carrier ↔ y ∈ f.carrier) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf hN
      by_cases hpf : p ∈ f.carrier
      · obtain ⟨b, hb, hboundary⟩ := K.boundary_union f hf
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
        have hef : e.carrier ⊆ f.carrier := by
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
            exact ((ih (N g) (by simpa only [hN] using hsmall g hg)
              g (hb hg) rfl).1 hpg).trans (hgf g hg)
        have hV : cellDirection e.carrier ≤ (affineSpan ℝ f.carrier).direction :=
          AffineSubspace.direction_le (affineSpan_mono ℝ hef)
        obtain ⟨r, hr, hc⟩ :=
          solidAngle_constant_on_cell_step4_common_ball b
            Cell.carrier (cellDirection e.carrier) p (fun g hg =>
              (ih (N g) (by simpa only [hN] using hsmall g hg) g (hb hg) rfl).2)
        refine ⟨fun _ => hef, r, hr,
          solidAngle_constant_on_cell_step2_fill
            f.flat.compact.isClosed (cellDirection e.carrier) hV p r ?_⟩
        intro x hx y hy hv
        rw [hboundary]
        simp only [mem_iUnion, exists_prop]
        constructor
        · rintro ⟨g, hg, hxg⟩
          exact ⟨g, hg, (hc g hg x hx y hy hv).mp hxg⟩
        · rintro ⟨g, hg, hyg⟩
          exact ⟨g, hg, (hc g hg x hx y hy hv).mpr hyg⟩
      · obtain ⟨r, hr, hball⟩ :=
          Metric.isOpen_iff.mp f.flat.compact.isClosed.isOpen_compl p hpf
        exact ⟨fun h => (hpf h).elim, r, hr,
          fun x hx y hy _ => iff_of_false (hball hx) (hball hy)⟩
  exact (main (N f) f hf rfl).2

open private solidAngle_constant_on_cell_step8_tangent_germ
  from Enforce.Geometry.CellComplex in
/-- Step 2 of the V4 proof of `actualCont_exists_step5_coface_side` (V4 1.0(b), 3.6(F1)):
"near a point of the relative interior of a codimension-one face, a polyhedral
manifold cell is a half-space on the recorded side". The tangent of a coface is
constant along the relative interior of its listed face, so the anchor of
`flagSide` is immaterial. -/
private theorem actualCont_exists_step5_coface_side_step2_coface
    {A : S.ι} (F : FacetFlag S A) (k : FlagStep d) (x : E d)
    (hx : x ∈ relint (F.cell ⟨k.val, k.property.1, by omega⟩).val.carrier) :
    tangentCone (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier x =
      flagSide F k := by
  let e := (F.cell ⟨k.val, k.property.1, by omega⟩).val
  let f := (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val
  have he : e ∈ (S.cx A).cells := (F.cell _).property
  have hf : f ∈ (S.cx A).cells := (F.cell _).property
  have hloc : IsLocallyConstant (fun p : relint e.carrier => tangentCone f.carrier p) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro p
    obtain ⟨r, hr, hball⟩ :=
      actualCont_exists_step5_coface_side_step1_cell_invariance
        (S.cx A) e he p p.property f hf
    have hnear : ∀ᶠ q : relint e.carrier in nhds p, (q : E d) ∈ ball (p : E d) r :=
      continuous_subtype_val.continuousAt.eventually
        (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hnear] with q hq
    apply (solidAngle_constant_on_cell_step8_tangent_germ
      f.carrier (cellDirection e.carrier) p q r hr hq ?_ hball).symm
    exact AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ e.carrier (intrinsicInterior_subset q.property))
      (subset_affineSpan ℝ e.carrier (intrinsicInterior_subset p.property))
  have hconn : IsPreconnected (univ : Set (relint e.carrier)) :=
    (Subtype.preconnectedSpace e.flat.relint_connected.isPreconnected).isPreconnected_univ
  exact hloc.apply_eq_of_isPreconnected hconn
    (x := ⟨x, hx⟩) (y := ⟨cellAnchor e, cellAnchor_mem e⟩) (mem_univ _) (mem_univ _)

/-- Step 3 of the V4 proof of `actualCont_exists_step5_coface_side` (V4 2.8):
"both chains lie in the positioned flag". Affine transport of a radial
tangent cone uses exactly the linear part of the affine frame. -/
private theorem actualCont_exists_step5_coface_side_step3_tangent_image
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

open private states_finite_step4_flag_halfspace_lem_cell from Enforce.State.State in
/-- Step 4 of the V4 proof of `actualCont_exists_step5_coface_side` (V4 3.6(F1)):
"a polyhedral manifold cell is a half-space on the recorded side". The local
side of a flag pair is a closed half-space of the upper direction space, cut
by a functional that does not vanish on that direction space. -/
private theorem actualCont_exists_step5_coface_side_step4_halfspace
    {A : S.ι} (F : FacetFlag S A) (k : FlagStep d) :
    ∃ ℓ : E d →ₗ[ℝ] ℝ,
      flagSide F k = {v | v ∈ cellDirection
        (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier ∧ 0 ≤ ℓ v} ∧
      ∃ u ∈ cellDirection (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier,
        ℓ u ≠ 0 := by
  let e := F.cell ⟨k.val, k.property.1, by omega⟩
  let C := F.cell ⟨k.val + 1, by omega, k.property.2⟩
  have hsub : e.val.carrier ⊆ C.val.carrier := F.nested _ _ (Nat.le_succ k.val)
  have hdim : C.val.dim = e.val.dim + 1 := by
    rw [F.dimension, F.dimension]
  obtain ⟨ℓ, hker, htan⟩ := states_finite_step4_flag_halfspace_lem_cell (S.cx A)
    e.property C.property hsub hdim (cellAnchor_mem e.val)
  refine ⟨ℓ, htan, ?_⟩
  by_contra hno
  push_neg at hno
  have hle : cellDirection C.val.carrier ≤ cellDirection e.val.carrier := by
    intro u hu
    have hmem : u ∈ {x | x ∈ cellDirection C.val.carrier ∧ ℓ x = 0} := ⟨hu, hno u hu⟩
    rw [hker] at hmem
    exact hmem
  have hfin := Submodule.finrank_mono hle
  rw [C.val.flat.dimension, e.val.flat.dimension, hdim] at hfin
  omega

/-- Step 4 of the V4 proof of `actualCont_exists_step5_coface_side` (V4 3.6(F1)):
"a half-space on the recorded side". A linear placement maps a half-space
of a subspace to the half-space of the image subspace. -/
private theorem actualCont_exists_step5_coface_side_step4_image
    (L : E d ≃ₗ[ℝ] E d) (D : Submodule ℝ (E d)) (ℓ : E d →ₗ[ℝ] ℝ) :
    L '' {v | v ∈ D ∧ 0 ≤ ℓ v} =
      {w | w ∈ D.map L.toLinearMap ∧ 0 ≤ (ℓ.comp L.symm.toLinearMap) w} := by
  ext y
  constructor
  · rintro ⟨v, ⟨hv, hl⟩, rfl⟩
    exact ⟨Submodule.mem_map_of_mem hv, by simpa using hl⟩
  · rintro ⟨⟨v, hv, rfl⟩, hl⟩
    exact ⟨v, ⟨hv, by simpa using hl⟩, rfl⟩

/-- Step 5 of the V4 proof of `actualCont_exists_step5_coface_side` (V4 3.6, Step 2):
"same affine spans, orientation and sides". Inclusion of two proper linear
half-spaces in one subspace forces equality: their defining functionals are
positive scalar multiples on that subspace. -/
private theorem actualCont_exists_step5_coface_side_step5_inclusion
    (V : Submodule ℝ (E d)) (ℓ m : E d →ₗ[ℝ] ℝ)
    (hℓ : ∃ u ∈ V, ℓ u ≠ 0) (hm : ∃ u ∈ V, m u ≠ 0)
    (hsub : {u | u ∈ V ∧ 0 ≤ ℓ u} ⊆ {u | u ∈ V ∧ 0 ≤ m u}) :
    {u | u ∈ V ∧ 0 ≤ ℓ u} = {u | u ∈ V ∧ 0 ≤ m u} := by
  obtain ⟨v, hv, hvℓ⟩ := hℓ
  let w := (ℓ v)⁻¹ • v
  have hwV : w ∈ V := V.smul_mem _ hv
  have hw : ℓ w = 1 := by simp [w, hvℓ]
  have hmw : 0 ≤ m w := (hsub ⟨hwV, by simp [hw]⟩).2
  have hscale (u : E d) (hu : u ∈ V) : m u = ℓ u * m w := by
    have hz : ℓ (u - ℓ u • w) = 0 := by simp [hw]
    have hV : u - ℓ u • w ∈ V := V.sub_mem hu (V.smul_mem _ hwV)
    have h₁ := (hsub ⟨hV, by simp [hz]⟩).2
    have h₂ := (hsub ⟨V.neg_mem hV, by rw [map_neg, hz]; simp⟩).2
    simp only [map_sub, map_smul, map_neg, smul_eq_mul] at h₁ h₂
    linarith
  have hmwpos : 0 < m w := by
    apply lt_of_le_of_ne hmw
    intro hz
    obtain ⟨u, hu, hmu⟩ := hm
    exact hmu (by rw [hscale u hu, ← hz, mul_zero])
  apply Set.Subset.antisymm hsub
  rintro u ⟨hu, hmu⟩
  refine ⟨hu, ?_⟩
  rw [hscale u hu] at hmu
  exact (mul_nonneg_iff_of_pos_right hmwpos).mp hmu

/-- Step 5 of the V4 proof of `actualCont_exists` (V4 2.8):
"both chains lie in the positioned flag". Refinement of a consecutive pair
of flag cells, with the same affine spans, preserves the local coface side. -/
private theorem actualCont_exists_step5_coface_side {A B : S.ι}
    (F : FacetFlag S A) (G : FacetFlag S B) (φ ψ : E d ≃ᵃ[ℝ] E d) (k : FlagStep d)
    (hlow : relint (φ '' (F.cell ⟨k.val, k.property.1, by omega⟩).val.carrier) ⊆
      relint (ψ '' (G.cell ⟨k.val, k.property.1, by omega⟩).val.carrier))
    (hhigh : relint (φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier) ⊆
      relint (ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier))
    (hspanlow : affineSpan ℝ (φ '' (F.cell ⟨k.val, k.property.1, by omega⟩).val.carrier) =
      affineSpan ℝ (ψ '' (G.cell ⟨k.val, k.property.1, by omega⟩).val.carrier))
    (hspanhigh : affineSpan ℝ
        (φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier) =
      affineSpan ℝ (ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier)) :
    φ.linear '' flagSide F k = ψ.linear '' flagSide G k := by
  classical
  let low : FlagIndex d := ⟨k.val, k.property.1, by omega⟩
  let high : FlagIndex d := ⟨k.val + 1, by omega, k.property.2⟩
  let x := φ (cellAnchor (F.cell low).val)
  have hx : x ∈ relint (ψ '' (G.cell low).val.carrier) := by
    apply hlow
    rw [restrictionOp_source_step5_relint_image]
    exact Set.mem_image_of_mem φ (cellAnchor_mem _)
  have hclosed (χ : E d ≃ᵃ[ℝ] E d) (e : Cell d) :
      closure (relint (χ '' e.carrier)) = χ '' e.carrier := by
    rw [restrictionOp_source_step5_relint_image]
    change closure (χ.toHomeomorphOfFiniteDimensional '' relint e.carrier) =
      χ.toHomeomorphOfFiniteDimensional '' e.carrier
    rw [← Homeomorph.image_closure, e.flat.regularClosed]
  have hsub : φ '' (F.cell high).val.carrier ⊆ ψ '' (G.cell high).val.carrier := by
    simpa only [hclosed] using closure_mono hhigh
  have hF : tangentCone (φ '' (F.cell high).val.carrier) x =
      φ.linear '' flagSide F k := by
    rw [actualCont_exists_step5_coface_side_step3_tangent_image]
    rfl
  have hG : tangentCone (ψ '' (G.cell high).val.carrier) x =
      ψ.linear '' flagSide G k := by
    rw [restrictionOp_source_step5_relint_image] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [← hxy, actualCont_exists_step5_coface_side_step3_tangent_image]
    exact congrArg (fun K : Set (E d) => ψ.linear '' K)
      (actualCont_exists_step5_coface_side_step2_coface G k y hy)
  have hmono : tangentCone (φ '' (F.cell high).val.carrier) x ⊆
      tangentCone (ψ '' (G.cell high).val.carrier) x := by
    rintro u ⟨ε, hε, hu⟩
    exact ⟨ε, hε, fun t ht htε => hsub (hu t ht htε)⟩
  rw [hF, hG] at hmono
  have hdirχ (χ : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
      (affineSpan ℝ (χ '' K)).direction =
        (cellDirection K).map χ.linear.toLinearMap := by
    change (affineSpan ℝ (χ.toAffineMap '' K)).direction = _
    rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
    rfl
  have hV := congrArg AffineSubspace.direction hspanhigh
  rw [hdirχ, hdirχ] at hV
  obtain ⟨ℓ, hℓ, u, hu, hℓu⟩ := actualCont_exists_step5_coface_side_step4_halfspace F k
  obtain ⟨m, hm, v, hv, hmv⟩ := actualCont_exists_step5_coface_side_step4_halfspace G k
  rw [hℓ, actualCont_exists_step5_coface_side_step4_image] at hmono ⊢
  rw [hm, actualCont_exists_step5_coface_side_step4_image] at hmono ⊢
  rw [← hV] at hmono ⊢
  apply actualCont_exists_step5_coface_side_step5_inclusion _ _ _ ?_ ?_ hmono
  · exact ⟨φ.linear u, Submodule.mem_map_of_mem hu, by simpa using hℓu⟩
  · rw [hV]
    exact ⟨ψ.linear v, Submodule.mem_map_of_mem hv, by simpa using hmv⟩

/-- Step 5 of the V4 proof of `actualCont_exists` (V4 2.8):
"with owner t''". Every listed cell of an owner lies in its closed tile. -/
private theorem actualCont_exists_step5_cell_subset (A : S.ι) (e : Cell d)
    (he : e ∈ (S.cx A).cells) : e.carrier ⊆ (S.proto A).carrier := by
  have hrel : relint e.carrier ⊆ frontier (S.proto A).carrier := by
    rw [← (S.cx A).cover]
    exact Set.subset_iUnion_of_subset e
      (Set.subset_iUnion_of_subset he Subset.rfl)
  calc
    e.carrier = closure (relint e.carrier) := e.flat.regularClosed.symm
    _ ⊆ closure (frontier (S.proto A).carrier) := closure_mono hrel
    _ = frontier (S.proto A).carrier := isClosed_frontier.closure_eq
    _ ⊆ (S.proto A).carrier := (S.proto A).compact.isClosed.frontier_subset

/-- Step 5 of the V4 proof of `actualCont_exists` (V4 2.8):
"both chains lie in the positioned flag". Affine transport of a radial
tangent cone uses exactly the linear part of the affine frame. -/
private theorem actualCont_exists_step5_tangent_image
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

/-- Step 5 of the V4 proof of `actualCont_exists` (V4 2.8):
"same ... side". Containment preserves radial tangent directions at a
common point. -/
private theorem actualCont_exists_step5_tangent_mono
    {K L : Set (E d)} (h : K ⊆ L) (x : E d) :
    tangentCone K x ⊆ tangentCone L x := by
  rintro u ⟨ε, hε, hu⟩
  exact ⟨ε, hε, fun t ht htε => h (hu t ht htε)⟩

/-- Step 5 of the V4 proof of `actualCont_exists` (V4 2.8):
"same ... side". The local half-ball description of a facet gives its
closed inward tangent half-space. -/
private theorem actualCont_exists_step5_halfball
    (K : Set (E d)) (p v : E d) (r : ℝ) (hr : 0 < r)
    (hlocal : K ∩ ball p r = {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p r) :
    tangentCone K p = {u | 0 ≤ inner ℝ v u} := by
  ext u
  let δ := r / (‖u‖ + 1)
  have hden : 0 < ‖u‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hr hden
  have hnear (t : ℝ) (ht : 0 < t) (htδ : t < δ) : p + t • u ∈ ball p r := by
    change dist (p + t • u) p < r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have := (lt_div_iff₀ hden).mp htδ
    nlinarith [norm_nonneg u]
  constructor
  · rintro ⟨ε, hε, hmem⟩
    let t := min ε δ / 2
    have ht : 0 < t := div_pos (lt_min hε hδ) (by norm_num)
    have htε : t < ε := lt_of_lt_of_le (by dsimp [t]; linarith [lt_min hε hδ])
      (min_le_left ε δ)
    have htδ : t < δ := lt_of_lt_of_le (by dsimp [t]; linarith [lt_min hε hδ])
      (min_le_right ε δ)
    have hm : p + t • u ∈ {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p r :=
      hlocal ▸ ⟨hmem t ht htε, hnear t ht htδ⟩
    have hnonneg := hm.1
    change 0 ≤ inner ℝ v (p + t • u - p) at hnonneg
    rw [add_sub_cancel_left, inner_smul_right] at hnonneg
    exact nonneg_of_mul_nonneg_right hnonneg ht
  · intro hu
    refine ⟨δ, hδ, fun t ht htδ => ?_⟩
    have hm : p + t • u ∈ K ∩ ball p r := by
      rw [hlocal]
      refine ⟨?_, hnear t ht htδ⟩
      change 0 ≤ inner ℝ v (p + t • u - p)
      rw [add_sub_cancel_left, inner_smul_right]
      exact mul_nonneg ht.le hu
    exact hm.1

/-- Step 5 of the V4 proof of `actualCont_exists` (V4 2.8):
"same ... side". Containment of nontrivial closed linear half-spaces
forces their equality. -/
private theorem actualCont_exists_step5_halfspace
    (f g : E d →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (hsub : {x | 0 ≤ f x} ⊆ {x | 0 ≤ g x}) :
    {x | 0 ≤ f x} = {x | 0 ≤ g x} ∨ g = 0 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    apply hf
    ext v
    simpa using not_exists.mp h v
  let w := (f v)⁻¹ • v
  have hw : f w = 1 := by simp [w, hv]
  have hg : 0 ≤ g w := hsub (by simp [hw])
  have heq (x : E d) : g x = f x * g w := by
    have hz : f (x - f x • w) = 0 := by simp [hw]
    have h₁ := hsub (a := x - f x • w) (by simp [hz])
    have h₂ := hsub (a := -(x - f x • w)) (by change 0 ≤ f (-(x - f x • w)); rw [map_neg, hz]; simp)
    simp only [Set.mem_setOf_eq, map_sub, map_smul, map_neg, smul_eq_mul] at h₁ h₂
    linarith
  by_cases hgw : g w = 0
  · right
    ext x
    simp [heq x, hgw]
  · left
    ext x
    simp only [Set.mem_setOf_eq, heq x]
    exact (mul_nonneg_iff_of_pos_right (lt_of_le_of_ne hg (Ne.symm hgw))).symm

/-- Step 5 of the V4 proof of `actualCont_exists` (V4 2.8):
"both chains lie in the positioned flag". Every affine-span direction
is tangent at a relative-interior point of a cell. -/
private theorem actualCont_exists_step5_relint_directions
    (K : Set (E d)) (p : E d) (hp : p ∈ relint K) :
    (cellDirection K : Set (E d)) ⊆ tangentCone K p := by
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hq)
  intro u hu
  let δ := r / (‖u‖ + 1)
  have hden : 0 < ‖u‖ + 1 := by positivity
  refine ⟨δ, div_pos hr hden, fun t ht htδ => ?_⟩
  have hmem : q.val + t • u ∈ affineSpan ℝ K := by
    simpa only [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction ((cellDirection K).smul_mem t hu) q.property
  apply hball (a := ⟨q.val + t • u, hmem⟩)
  change dist (q.val + t • u) q.val < r
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have := (lt_div_iff₀ hden).mp htδ
  nlinarith [norm_nonneg u]

/-- Step 5 of the V4 proof of `actualCont_exists` (V4 2.8):
"same ... side". The inward tangent cone is constant along the connected
relative interior of a listed facet. -/
private theorem actualCont_exists_step5_facet_cone
    (A : S.ι) (f : FacetName S A) (p q : E d)
    (hp : p ∈ relint f.val.carrier) (hq : q ∈ relint f.val.carrier) :
    tangentCone (S.proto A).carrier p = tangentCone (S.proto A).carrier q := by
  let R := relint f.val.carrier
  let cone : R → Set (E d) := fun x => tangentCone (S.proto A).carrier x.val
  have hsub : f.val.carrier ⊆ (S.proto A).carrier :=
    actualCont_exists_step5_cell_subset A f.val (Finset.mem_filter.mp f.property).1
  have hloc : IsLocallyConstant cone := by
    apply (IsLocallyConstant.iff_exists_open cone).mpr
    intro x
    obtain ⟨r, hr, v, _, _, _, hlocal⟩ :=
      facet_halfball (S.proto A) (S.cx A) f.val f.property x.val x.property
    have hc := actualCont_exists_step5_halfball _ _ v r hr hlocal
    have hnormal (u : E d) (hu : u ∈ cellDirection f.val.carrier) : inner ℝ v u = 0 := by
      have hnonneg (w : E d) (hw : w ∈ cellDirection f.val.carrier) : 0 ≤ inner ℝ v w := by
        have h := actualCont_exists_step5_tangent_mono hsub x.val
          (actualCont_exists_step5_relint_directions _ _ x.property hw)
        simpa only [hc, Set.mem_setOf_eq] using h
      have h₁ := hnonneg u hu
      have h₂ := hnonneg (-u) ((cellDirection f.val.carrier).neg_mem hu)
      rw [inner_neg_right] at h₂
      linarith
    refine ⟨Subtype.val ⁻¹' ball x.val r, isOpen_ball.preimage continuous_subtype_val,
      by simpa only [Set.mem_preimage, mem_ball, dist_self] using hr, ?_⟩
    intro y hy
    have hyx : inner ℝ v (y.val - x.val) = 0 := hnormal _
      (AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ _ (intrinsicInterior_subset y.property))
        (subset_affineSpan ℝ _ (intrinsicInterior_subset x.property)))
    have hδ : 0 < r - dist y.val x.val := sub_pos.mpr hy
    have hball : ball y.val (r - dist y.val x.val) ⊆ ball x.val r := by
      intro z hz
      change dist z x.val < r
      have ht := dist_triangle z y.val x.val
      change dist z y.val < r - dist y.val x.val at hz
      linarith
    have htranslate (z : E d) : inner ℝ v (z - x.val) = inner ℝ v (z - y.val) := by
      have he : z - x.val = (z - y.val) + (y.val - x.val) := by module
      rw [he, inner_add_right, hyx, add_zero]
    have hlocal' : (S.proto A).carrier ∩ ball y.val (r - dist y.val x.val) =
        {z | 0 ≤ inner ℝ v (z - y.val)} ∩ ball y.val (r - dist y.val x.val) := by
      ext z
      constructor
      · rintro ⟨hz, hzball⟩
        have hm : z ∈ {z | 0 ≤ inner ℝ v (z - x.val)} ∩ ball x.val r :=
          hlocal ▸ ⟨hz, hball hzball⟩
        exact ⟨by simpa only [Set.mem_setOf_eq, htranslate z] using hm.1, hzball⟩
      · rintro ⟨hz, hzball⟩
        have hm : z ∈ (S.proto A).carrier ∩ ball x.val r := by
          rw [hlocal]
          exact ⟨by simpa only [Set.mem_setOf_eq, htranslate z] using hz, hball hzball⟩
        exact ⟨hm.1, hzball⟩
    exact (actualCont_exists_step5_halfball _ _ v _ hδ hlocal').trans hc.symm
  letI : PreconnectedSpace R := isPreconnected_iff_preconnectedSpace.mp
    f.val.flat.relint_connected.isPreconnected
  exact hloc.apply_eq_of_preconnectedSpace ⟨p, hp⟩ ⟨q, hq⟩

/-- Step 5 of the V4 proof of `actualCont_exists` (V4 2.8):
"same ... side (same provider g, same serving child H)". A contained
tile and its ancestor have the same inward half-space along an inherited facet. -/
private theorem actualCont_exists_step5_inward {A B : S.ι}
    (f : FacetName S A) (F : FacetName S B) (φ ψ : E d ≃ᵃ[ℝ] E d)
    (hsub : φ '' (S.proto A).carrier ⊆ ψ '' (S.proto B).carrier)
    (hrel : relint (φ '' f.val.carrier) ⊆ relint (ψ '' F.val.carrier)) :
    φ.linear '' tangentCone (S.proto A).carrier (cellAnchor f.val) =
      ψ.linear '' tangentCone (S.proto B).carrier (cellAnchor F.val) := by
  let p := cellAnchor f.val
  let q := ψ.symm (φ p)
  have hp : p ∈ relint f.val.carrier := cellAnchor_mem _
  have hq : q ∈ relint F.val.carrier := by
    have h := hrel (by rw [restrictionOp_source_step5_relint_image]; exact ⟨p, hp, rfl⟩)
    rw [restrictionOp_source_step5_relint_image] at h
    obtain ⟨z, hz, he⟩ := h
    simpa only [q, ← he, AffineEquiv.symm_apply_apply] using hz
  have hpq : ψ q = φ p := ψ.apply_symm_apply _
  obtain ⟨r, hr, v, hv, _, _, hlocal⟩ :=
    facet_halfball (S.proto A) (S.cx A) f.val f.property p hp
  obtain ⟨s, hs, w, hw, _, _, hlocal'⟩ :=
    facet_halfball (S.proto B) (S.cx B) F.val F.property q hq
  have hcp := actualCont_exists_step5_halfball _ _ v r hr hlocal
  have hcq := actualCont_exists_step5_halfball _ _ w s hs hlocal'
  let l : E d →ₗ[ℝ] ℝ := (innerₛₗ ℝ v).comp φ.linear.symm.toLinearMap
  let m : E d →ₗ[ℝ] ℝ := (innerₛₗ ℝ w).comp ψ.linear.symm.toLinearMap
  have himage (L : E d ≃ₗ[ℝ] E d) (v : E d) :
      L '' {z | 0 ≤ inner ℝ v z} = {z | 0 ≤ inner ℝ v (L.symm z)} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [Set.mem_setOf_eq, LinearEquiv.symm_apply_apply] using hy
    · intro hz
      exact ⟨L.symm z, hz, L.apply_symm_apply z⟩
  have hl : φ.linear '' tangentCone (S.proto A).carrier p = {z | 0 ≤ l z} := by
    rw [hcp, himage]
    rfl
  have hm : ψ.linear '' tangentCone (S.proto B).carrier q = {z | 0 ≤ m z} := by
    rw [hcq, himage]
    rfl
  have hlne : l ≠ 0 := by
    intro h
    have he := congrArg (fun k : E d →ₗ[ℝ] ℝ => k (φ.linear v)) h
    change inner ℝ v (φ.linear.symm (φ.linear v)) = 0 at he
    rw [LinearEquiv.symm_apply_apply, real_inner_self_eq_norm_sq, hv] at he
    norm_num at he
  have hmne : m ≠ 0 := by
    intro h
    have he := congrArg (fun k : E d →ₗ[ℝ] ℝ => k (ψ.linear w)) h
    change inner ℝ w (ψ.linear.symm (ψ.linear w)) = 0 at he
    rw [LinearEquiv.symm_apply_apply, real_inner_self_eq_norm_sq, hw] at he
    norm_num at he
  have hcones : {z | 0 ≤ l z} ⊆ {z | 0 ≤ m z} := by
    rw [← hl, ← hm,
      ← actualCont_exists_step5_tangent_image,
      ← actualCont_exists_step5_tangent_image, hpq]
    exact actualCont_exists_step5_tangent_mono hsub _
  have heq := (actualCont_exists_step5_halfspace l m hlne hcones).resolve_right hmne
  have hconst := actualCont_exists_step5_facet_cone B F q
    (cellAnchor F.val) hq (cellAnchor_mem _)
  exact hl.trans (heq.trans (hm.symm.trans (congrArg (ψ.linear '' ·) hconst)))

/-- Step 5 of the V4 proof of `actualCont_exists` (V4 2.8):
"selected owners ... of H". A native descendant is contained in the
positioned ancestor, as follows from the prescribed native subdivision. -/
private theorem actualCont_exists_step5_subset (N Q : FramedNode S) (n : ℕ)
    (hQ : Q.IsDescendant 0 N n) : Q.carrier 0 ⊆ N.carrier n := by
  obtain ⟨r, hr, w, rfl⟩ := hQ
  simp only [zero_add] at hr
  subst r
  have hnative : (S.nativeTile N.ty n w).carrier 0 ⊆ S.supertile n N.ty := by
    rw [← S.native_cover N.ty n]
    exact Set.subset_iUnion_of_subset w Subset.rfl
  have h := Set.image_mono (f := N.frame) hnative
  simpa only [FramedNode.carrier, FramedNode.move, placedSet, Set.image_image,
    AffineIsometryEquiv.coe_trans, Function.comp_apply, SubstSystem.nativeTile] using h

/-- Step 5 of the V4 proof of `actualCont_exists` (V4 2.8):
"both chains lie in the positioned flag ... with its orientations".
Active chains with the same placed provider and serving child agree in all
the affine spans, successive sides, edge orientation, and inward tile side. -/
private theorem actualCont_exists_step5_aligned (U : HonestSource S) (P : Params S)
    (t q : U.Node) (ht : t.1 = 0) (hq : q.1 = 0)
    (f : FacetName S t.2.val.ty) (g : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault t f) (hg : ¬ U.hierarchy.IsFault q g)
    (c : OrientedChain f) (c' : OrientedChain g)
    (hc : c ∈ U.recordChains P t f hf) (hc' : c' ∈ U.recordChains P q g hg)
    (hserv : U.hierarchy.servingChild q g hg = U.hierarchy.servingChild t f hf)
    (hi : U.recordIncidence P q g hg = U.recordIncidence P t f hf)
    (hp : U.providerPlacement P q g hg = U.providerPlacement P t f hf) :
    ChainsAligned (U.recordOf P t f hf) (U.recordOf P q g hg) c c'
      (q.2.val.frame.trans t.2.val.frame.symm) := by
  classical
  have hct : U.ActiveChain P t f hf c := (Finset.mem_filter.mp hc).2
  have hcq : U.ActiveChain P q g hg c' := (Finset.mem_filter.mp hc').2
  have fit (x : U.Node) (fx : FacetName S x.2.val.ty)
      (hfx : ¬ U.hierarchy.IsFault x fx) (cx : OrientedChain fx)
      (hcx : U.ActiveChain P x fx hfx cx) (j : FlagIndex d) :
      relint (x.2.val.cell x.1 (cx.chain.val.cell j).val) ⊆
          relint (U.providerPlacement P x fx hfx ''
            ((P.flag (U.recordIncidence P x fx hfx)).flag.cell j).val.carrier) ∧
        affineSpan ℝ (x.2.val.cell x.1 (cx.chain.val.cell j).val) =
          affineSpan ℝ (U.providerPlacement P x fx hfx ''
            ((P.flag (U.recordIncidence P x fx hfx)).flag.cell j).val.carrier) := by
    obtain ⟨hs, hτ, hspan⟩ := hcx.1 j
    exact ⟨by simpa only [hτ] using
      (U.hierarchy.stratumMap_spec x fx hfx (cx.chain.val.cell j) hs).1, hspan⟩
  have side (x : U.Node) (hx : x.1 = 0) (fx : FacetName S x.2.val.ty)
      (hfx : ¬ U.hierarchy.IsFault x fx) (cx : OrientedChain fx)
      (hcx : U.ActiveChain P x fx hfx cx) (k : FlagStep d) :
      x.2.val.frame.linearIsometryEquiv '' flagSide cx.chain.val k =
        (U.providerPlacement P x fx hfx).linear ''
          flagSide (P.flag (U.recordIncidence P x fx hfx)).flag k := by
    have h := actualCont_exists_step5_coface_side cx.chain.val
      (P.flag (U.recordIncidence P x fx hfx)).flag (x.2.val.prototypeFrame x.1)
      (U.providerPlacement P x fx hfx) k (fit x fx hfx cx hcx _).1
      (fit x fx hfx cx hcx _).1 (fit x fx hfx cx hcx _).2
      (fit x fx hfx cx hcx _).2
    simpa [FramedNode.prototypeFrame, hx] using h
  let H := U.hierarchy.servingChild t f hf
  let F : FacetName S H.2.val.ty := (U.hierarchy.firstProvider t f hf).2
  have inward (x : U.Node) (hx : x.1 = 0) (fx : FacetName S x.2.val.ty)
      (hfx : ¬ U.hierarchy.IsFault x fx) (cx : OrientedChain fx)
      (hcx : U.ActiveChain P x fx hfx cx)
      (hH : U.hierarchy.servingChild x fx hfx = H)
      (hcarrier : U.hierarchy.providerCarrier x fx hfx = H.2.val.cell H.1 F.val) :
      x.2.val.frame.linearIsometryEquiv ''
        tangentCone (S.proto x.2.val.ty).carrier (cellAnchor fx.val) =
      (H.2.val.prototypeFrame H.1).linear ''
        tangentCone (S.proto H.2.val.ty).carrier (cellAnchor F.val) := by
    have hd := U.hierarchy.ancestor_descendant x (U.hierarchy.firstProvider x fx hfx).1
    change x.2.val.IsDescendant x.1
      (U.hierarchy.servingChild x fx hfx).2.val
      (U.hierarchy.servingChild x fx hfx).1 at hd
    have hd' : x.2.val.IsDescendant 0 H.2.val H.1 := by
      have hn := congrArg (fun B : U.Node => B.2.val) hH
      have hh := congrArg (fun B : U.Node => B.1) hH
      simpa only [hx, hn, hh] using hd
    have hsub := actualCont_exists_step5_subset H.2.val x.2.val H.1 hd'
    have hrel := (fit x fx hfx cx hcx facetIndex).1
    rw [cx.chain.property, (P.flag (U.recordIncidence P x fx hfx)).top,
      record_provider_carrier, hcarrier] at hrel
    have h := actualCont_exists_step5_inward fx F (x.2.val.prototypeFrame 0)
      (H.2.val.prototypeFrame H.1)
      (by simpa [FramedNode.carrier, FramedNode.prototypeFrame, placedSet,
        SubstSystem.supertile, Set.image_image] using hsub)
      (by simpa only [hx] using hrel)
    simpa [FramedNode.prototypeFrame] using h
  have hcarrier : U.hierarchy.providerCarrier q g hg = H.2.val.cell H.1 F.val := by
    rw [← record_provider_carrier U P q g hg, hp, hi, record_provider_carrier]
    rfl
  have htin := inward t ht f hf c hct rfl rfl
  have hqin := inward q hq g hg c' hcq hserv hcarrier
  have hlin (x : E d) : t.2.val.frame.linearIsometryEquiv
      ((q.2.val.frame.trans t.2.val.frame.symm).linearIsometryEquiv x) =
        q.2.val.frame.linearIsometryEquiv x := by
    change t.2.val.frame.linearIsometryEquiv
      (t.2.val.frame.linearIsometryEquiv.symm (q.2.val.frame.linearIsometryEquiv x)) = _
    exact t.2.val.frame.linearIsometryEquiv.apply_symm_apply _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    have hs := (fit t f hf c hct j).2
    have hs' := (fit q g hg c' hcq j).2
    rw [hp, hi] at hs'
    have heq := hs.trans hs'.symm
    apply (restrictionOp_source_step4_chains_step2_span t.2.val.frame.toAffineEquiv
      (c.chain.val.cell j).val.carrier
      ((q.2.val.frame.trans t.2.val.frame.symm) '' (c'.chain.val.cell j).val.carrier)).mp
    simpa [FramedNode.cell, FramedNode.prototypeFrame, ht, hq, Set.image_image] using heq
  · intro k
    have hs := side t ht f hf c hct k
    have hs' := side q hq g hg c' hcq k
    rw [hp, hi] at hs'
    apply t.2.val.frame.linearIsometryEquiv.injective.image_injective
    simpa only [Set.image_image, hlin] using hs.trans hs'.symm
  · obtain ⟨a, ha, hca⟩ :=
      ((restrictionOp_source_step4_chains_step1_test U P t f hf c).mp hct).2
    obtain ⟨b, hb, hcb⟩ :=
      ((restrictionOp_source_step4_chains_step1_test U P q g hg c').mp hcq).2
    change U.counterDirection P t f hf =
      a • (t.2.val.prototypeFrame t.1).linear (chainVector c) at hca
    change U.counterDirection P q g hg =
      b • (q.2.val.prototypeFrame q.1).linear (chainVector c') at hcb
    have hcbn : U.counterDirection P q g hg =
        b • q.2.val.frame.linearIsometryEquiv (chainVector c') := by
      simpa [FramedNode.prototypeFrame, hq] using hcb
    have hdir : U.counterDirection P q g hg = U.counterDirection P t f hf := by
      unfold HonestSource.counterDirection
      rw [hp, hi]
    rw [hdir, hca] at hcb
    have hcb' : a • t.2.val.frame.linearIsometryEquiv (chainVector c) =
        b • q.2.val.frame.linearIsometryEquiv (chainVector c') := by
      simpa [FramedNode.prototypeFrame, ht, hq] using hcb
    have hvec : t.2.val.frame.linearIsometryEquiv (chainVector c) =
        (b / a) • q.2.val.frame.linearIsometryEquiv (chainVector c') := by
      calc
        _ = a⁻¹ • (a • t.2.val.frame.linearIsometryEquiv (chainVector c)) :=
          (inv_smul_smul₀ (ne_of_gt ha) _).symm
        _ = _ := by rw [hcb', smul_smul, ← div_eq_inv_mul]
    have hne : q.2.val.frame.linearIsometryEquiv (chainVector c') ≠ 0 := by
      have hnonzero : U.counterDirection P q g hg ≠ 0 := by
        intro hzero
        have hz := (U.providerPlacement P q g hg).linear.injective
          (hzero.trans (map_zero _).symm)
        exact (P.flag (U.recordIncidence P q g hg)).distinct (sub_eq_zero.mp hz).symm
      intro hz
      apply hnonzero
      rw [hcbn, hz, smul_zero]
    have hpos : 0 < inner ℝ (t.2.val.frame.linearIsometryEquiv (chainVector c))
        (q.2.val.frame.linearIsometryEquiv (chainVector c')) := by
      rw [hvec, real_inner_smul_left]
      exact mul_pos (div_pos hb ha) (real_inner_self_pos.mpr hne)
    simpa only [LinearIsometryEquiv.inner_map_eq_flip] using hpos
  · apply t.2.val.frame.linearIsometryEquiv.injective.image_injective
    simpa only [Set.image_image, hlin, HonestSource.recordOf] using htin.trans hqin.symm

/-- Step 6 of the V4 proof of `actualCont_exists` (V4 2.8):
"initial endpoint v". The order of the endpoints of a nondegenerate segment
is determined by a positive inner product of the two directed edge vectors. -/
private theorem actualCont_exists_step6_order (a b v w : E d)
    (hseg : segment ℝ a b = segment ℝ v w)
    (hpos : 0 < inner ℝ (b - a) (w - v)) : a = v ∧ b = w := by
  have first (a b v w : E d) (hs : segment ℝ a b = segment ℝ v w)
      (hp : 0 < inner ℝ (b - a) (w - v)) : a = v := by
    have ha : a ∈ segment ℝ v w := hs ▸ left_mem_segment ℝ a b
    have hv : v ∈ segment ℝ a b := hs.symm ▸ left_mem_segment ℝ v w
    rw [segment_eq_image'] at ha hv
    obtain ⟨s, hs, hsa⟩ := ha
    obtain ⟨t, ht, htv⟩ := hv
    have heq : s • (w - v) + t • (b - a) = 0 := by
      have hs' : s • (w - v) = a - v := by rw [← hsa]; module
      have ht' : t • (b - a) = v - a := by rw [← htv]; module
      rw [hs', ht']
      module
    have h := congrArg (inner ℝ (b - a)) heq
    simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at h
    have hn : 0 ≤ inner ℝ (b - a) (b - a) := real_inner_self_nonneg
    have hs0 : s = 0 := by nlinarith [mul_nonneg ht.1 hn, hs.1]
    simpa only [hs0, zero_smul, add_zero] using hsa.symm
  refine ⟨first a b v w hseg hpos, first b a w v ?_ ?_⟩
  · simpa only [segment_symm ℝ b a, segment_symm ℝ w v] using hseg
  · simpa only [← neg_sub a b, ← neg_sub v w, inner_neg_left, inner_neg_right,
      neg_neg] using hpos

/-- Step 6 of the V4 proof of `actualCont_exists` (V4 2.8):
"on the far side of v (after v in the orientation)". Two consecutive
positively directed intervals form their full segment, with the junction inside. -/
private theorem actualCont_exists_step6_join (p v w : E d)
    (hnext : ∃ k : ℝ, 0 < k ∧ w - v = k • (v - p)) :
    segment ℝ p v ∪ segment ℝ v w = segment ℝ p w ∧
      v ∈ openSegment ℝ p w := by
  obtain ⟨k, hk, hw⟩ := hnext
  have hk1 : 0 < 1 + k := by linarith
  have hwp : w - p = (1 + k) • (v - p) := by
    calc
      _ = (w - v) + (v - p) := by module
      _ = _ := by rw [hw, add_smul, one_smul]; module
  have hv : v ∈ openSegment ℝ p w := by
    rw [openSegment_eq_image']
    refine ⟨(1 + k)⁻¹, ⟨inv_pos.mpr hk1, ?_⟩, ?_⟩
    · exact (inv_lt_one₀ hk1).mpr (by linarith)
    · change p + (1 + k)⁻¹ • (w - p) = v
      rw [hwp, inv_smul_smul₀ (ne_of_gt hk1)]
      module
  refine ⟨?_, hv⟩
  have hvseg := openSegment_subset_segment ℝ p w hv
  have hconv := convex_segment p w (𝕜 := ℝ)
  apply Set.Subset.antisymm
  · exact union_subset
      (hconv.segment_subset (left_mem_segment ℝ p w) hvseg)
      (hconv.segment_subset hvseg (right_mem_segment ℝ p w))
  · intro x hx
    have hvrange : v ∈ Set.range (AffineMap.lineMap p w : ℝ → E d) := by
      rw [openSegment_eq_image_lineMap] at hv
      obtain ⟨s, _, hs⟩ := hv
      exact ⟨s, hs⟩
    rw [← insert_endpoints_openSegment] at hx
    simp only [Set.mem_insert_iff] at hx
    rcases hx with hxp | hxw | hx
    · subst x
      exact Or.inl (left_mem_segment ℝ p v)
    · subst x
      exact Or.inr (right_mem_segment ℝ v w)
    · have hm := openSegment_subset_union p w hvrange hx
      simp only [Set.mem_insert_iff, Set.mem_union] at hm
      rcases hm with hxv | hm | hm
      · subst x
        exact Or.inl (right_mem_segment ℝ p v)
      · exact Or.inl (openSegment_subset_segment ℝ p v hm)
      · exact Or.inr (openSegment_subset_segment ℝ v w hm)

/-- Step 6 of the V4 proof of `actualCont_exists` (V4 2.8):
"(t,t'') ... realised by actual tiles". Two actual native nodes, including
the case of equal nodes, give a finite configuration with their actual labels. -/
private theorem actualCont_exists_step6_configuration (U : HonestSource S) (P : Params S)
    (t q : U.Node) (ht : t.1 = 0) (hq : q.1 = 0) :
    ∃ θ : Template P,
      θ.central = leafTypeOf U P t ht ∧
      θ.tiles =
        {((⟨(leafTypeOf U P t ht).prototype, AffineIsometryEquiv.refl ℝ (E d)⟩ :
          FramedNode S), leafTypeOf U P t ht),
          (q.2.val.move t.2.val.frame.symm, leafTypeOf U P q hq)} ∧
      θ.annotation = none ∧ IsActualTemplate U P t ht θ := by
  classical
  let zt := (t.2.val.move t.2.val.frame.symm, leafTypeOf U P t ht)
  let zq := (q.2.val.move t.2.val.frame.symm, leafTypeOf U P q hq)
  have hcentral : t.2.val.move t.2.val.frame.symm =
      (⟨(leafTypeOf U P t ht).prototype, AffineIsometryEquiv.refl ℝ (E d)⟩ :
        FramedNode S) := by
    apply FramedNode.ext
    · exact (leafTypeOf_type U P t ht).symm
    · exact AffineIsometryEquiv.self_trans_symm _
  have hdis : zt ≠ zq → Disjoint (interior (zt.1.carrier 0))
      (interior (zq.1.carrier 0)) := by
    intro hne
    have hnode : t.2.val ≠ q.2.val := by
      intro heq
      have htq : t = q := by
        rcases t with ⟨m, T, hT⟩
        rcases q with ⟨n, Q, hQ⟩
        dsimp only at ht hq heq
        subst m
        subst n
        cases heq
        rfl
      cases htq
      exact hne rfl
    have hd := U.hierarchy.disjoint 0 (by simpa only [ht] using t.2.property)
      (by simpa only [hq] using q.2.property) hnode
    have himage (N : FramedNode S) :
        interior ((N.move t.2.val.frame.symm).carrier 0) =
          t.2.val.frame.symm '' interior (N.carrier 0) := by
      have hc : (N.move t.2.val.frame.symm).carrier 0 =
          t.2.val.frame.symm.toHomeomorph '' N.carrier 0 := by
        simp only [FramedNode.carrier, FramedNode.move, placedSet, Set.image_image]
        rfl
      rw [hc, ← Homeomorph.image_interior]
      rfl
    change Disjoint (interior ((t.2.val.move t.2.val.frame.symm).carrier 0))
      (interior ((q.2.val.move t.2.val.frame.symm).carrier 0))
    rw [himage, himage]
    exact (Set.disjoint_image_iff t.2.val.frame.symm.injective).mpr hd
  let θ : Template P := {
    central := leafTypeOf U P t ht
    tiles := {zt, zq}
    types_match := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (leafTypeOf_type U P t ht).symm
      · exact (leafTypeOf_type U P q hq).symm
    disjoint := by
      intro z hz w hw hne
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz hw
      rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
      · exact (hne rfl).elim
      · exact hdis hne
      · exact (hdis (Ne.symm hne)).symm
      · exact (hne rfl).elim
    central_mem := by
      change _ ∈ ({zt, zq} : Finset (FramedNode S × LeafType P))
      rw [← hcentral]
      exact Finset.mem_insert_self _ _
    annotation := none }
  refine ⟨θ, rfl, ?_, rfl, rfl, ?_⟩
  · change ({zt, zq} : Finset (FramedNode S × LeafType P)) = _
    simp only [zt, hcentral]
    rfl
  · intro z hz
    change z ∈ ({zt, zq} : Finset (FramedNode S × LeafType P)) at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨t, ht, rfl, rfl⟩
    · exact ⟨q, hq, rfl, rfl⟩

/-- Q14, V4 2.8 (CONT geometry): the actual next selected owner supplies a physical
continuation template. This existence lemma asserts geometry and actual labels only;
it does not assume or assert the CONT row. -/
theorem actualCont_exists (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : ContSlot (leafTypeOf U P t ht)) :
    ∃ T : ContTemplate slot, IsActualTemplate U P t ht T.configuration := by
  classical
  rcases slot with ⟨facet, r, hread, htype, hfacet, e, hactive, v, hvf, hterminal,
    htau, packet, hpacket⟩
  obtain ⟨f, hf, _, hr⟩ := actualCont_exists_step1_record U P t ht facet.val r hread
  subst r
  obtain ⟨c, hc, he⟩ := hactive
  change (c.chain.val.cell edgeIndex).val = e.val at he
  have hct : U.ActiveChain P t f hf c := (Finset.mem_filter.mp hc).2
  let H := U.hierarchy.servingChild t f hf
  let n := (U.hierarchy.firstProvider t f hf).1
  have hHheight : H.1 = n := by
    simpa only [ht, zero_add] using U.hierarchy.ancestor_height t n
  obtain ⟨F, a, hF, ha, hcells⟩ := chain_active_owner U P t f hf c hc
  have hF' (j : FlagIndex d) : H.2.val.cell n (F.cell j).val =
      U.providerPlacement P t f hf ''
        ((P.flag (U.recordIncidence P t f hf)).flag.cell j).val.carrier := by
    have h := hF j
    change H.2.val.cell H.1 (F.cell j).val = _ at h
    simpa only [hHheight] using h
  have ha' : placedTraceOwner H.2.val n n F a = t.2.val := by
    change placedTraceOwner H.2.val H.1 n F a = t.2.val at ha
    simpa only [hHheight] using ha
  have hebottom : e.val.carrier ⊆ a.bottom.val.carrier := by
    rw [← he]
    change _ ⊆ (a.chain.cell TracePiece.bottomIndex).val.carrier
    rw [hcells TracePiece.bottomIndex]
    exact c.chain.val.nested _ _ traceDimension_pos
  have hbottom : t.2.val.cell 0 e.val ⊆ placedTraceCarrier H.2.val n n F a := by
    have h := placedTraceOwner_cells H.2.val n n le_rfl F a a.bottom.val
    rw [ha', Nat.sub_self] at h
    exact (Set.image_mono hebottom).trans_eq h
  have hedge : t.2.val.cell 0 e.val ⊆ H.2.val.cell n (F.cell edgeIndex).val := by
    obtain ⟨hs, hτ, _⟩ := hct.1 edgeIndex
    have h := closure_mono (U.hierarchy.stratumMap_spec t f hf
      (c.chain.val.cell edgeIndex) hs).1
    simp only [restrictionOp_source_step5_cell_closure] at h
    rw [hτ, ← hF' edgeIndex, he] at h
    simpa only [ht] using h
  let p := t.2.val.frame ((U.recordOf P t f hf).endpoints e).1
  let x := t.2.val.frame (vertexPoint v)
  have hx : x ∈ relint (H.2.val.cell n (F.cell edgeIndex).val) := by
    rw [hF' edgeIndex]
    simpa [x, FramedNode.prototypeFrame, ht] using
      actualCont_exists_step2_vertex U P t f hf v hvf htau
  have hseg : t.2.val.cell 0 e.val = segment ℝ p x := by
    have h := image_segment ℝ t.2.val.frame.toAffineEquiv.toAffineMap
      ((U.recordOf P t f hf).endpoints e).1 ((U.recordOf P t f hf).endpoints e).2
    rw [← (actualCont_exists_step2_endpoints (U.recordOf P t f hf) e).2] at h
    simpa [FramedNode.cell, FramedNode.prototypeFrame, p, x, hterminal] using h
  have hpx : p ≠ x := by
    intro h
    apply (actualCont_exists_step2_endpoints (U.recordOf P t f hf) e).1
    exact (t.2.val.frame.injective h).trans hterminal
  obtain ⟨b, e', v', w, hv', hseg', hxw, hnext, hbottom', hedge'⟩ :=
    actualCont_exists_step3_trace_successor H.2.val n F a e.val
      (by rw [ha']; exact e.property) p x hpx (by rw [ha']; exact hseg)
      (by rw [ha']; exact hbottom) (by rw [ha']; exact hedge) hx
  let Q := placedTraceOwner H.2.val n n F b
  have hHmem : H.2.val ∈ U.hierarchy.nodes n := by
    simpa only [hHheight] using H.2.property
  have hQ : Q ∈ U.hierarchy.nodes 0 := by
    simpa only [Nat.sub_self] using
      U.hierarchy.placedTraceOwner_mem H.2.val n n hHmem le_rfl F b
  let q : U.Node := ⟨0, ⟨Q, hQ⟩⟩
  have hqty : q.2.val.ty = b.tile.ty := by
    simp only [q, Q, placedTraceOwner, FramedNode.move, Nat.sub_self,
      TracePiece.tile, SubstSystem.nativeTile]
  let g : FacetName S q.2.val.ty := ⟨(b.chain.cell traceTopIndex).val, by
    rw [hqty]
    exact Finset.mem_filter.mpr
      ⟨(b.chain.cell traceTopIndex).property, b.chain.dimension traceTopIndex⟩⟩
  have hsub : q.2.val.cell q.1 g.val ⊆ U.hierarchy.providerCarrier t f hf := by
    calc
      _ = tracePlacement H.2.val n n '' (b.tile.cell 0 (b.chain.cell traceTopIndex).val) := by
        simpa only [Nat.sub_self] using
          placedTraceOwner_cells H.2.val n n le_rfl F b (b.chain.cell traceTopIndex).val
      _ ⊆ tracePlacement H.2.val n n ''
          ((S.σ ^ n) '' (F.cell facetIndex).val.carrier) :=
        Set.image_mono (b.chain.contained traceTopIndex)
      _ = H.2.val.cell n (F.cell facetIndex).val := by
        simp [tracePlacement, FramedNode.cell, FramedNode.prototypeFrame, Set.image_image]
      _ = U.hierarchy.providerCarrier t f hf := by
        rw [hF' facetIndex, (P.flag (U.recordIncidence P t f hf)).top,
          record_provider_carrier]
  have hroot : (⟨n, ⟨H.2.val, hHmem⟩⟩ : U.Node) = H := by
    exact actualCont_exists_step4_reindex U H n hHheight hHmem
  have hanc : U.hierarchy.ancestor q n = H := by
    apply Eq.trans _ hroot
    exact actualCont_exists_step4_ancestor U q rfl n H.2.val hHmem b.owner
      (by simp only [q, Q, placedTraceOwner, Nat.sub_self, SubstSystem.nativeTile])
  obtain ⟨hg, hserv, hi, hp⟩ := actualCont_exists_step4_provider U P t q f hf g n hanc hsub
  have hdepth : (U.hierarchy.firstProvider q g hg).1 = n := by
    have h := U.hierarchy.ancestor_height q (U.hierarchy.firstProvider q g hg).1
    have hs := congrArg (fun B : U.Node => B.1) hserv
    change (U.hierarchy.servingChild q g hg).1 = 0 +
      (U.hierarchy.firstProvider q g hg).1 at h
    change (U.hierarchy.servingChild q g hg).1 = H.1 at hs
    omega
  have hactive' : (U.recordOf P q g hg).ChainActive (edgeCell e') := by
    apply actualCont_exists_step4_active U P q H g hg n hserv hdepth F b
      (fun j => by rw [hp, hi]; exact hF j)
      (congrArg (fun k => placedTraceOwner H.2.val k n F b) hHheight) rfl e'
    · simpa only [hHheight] using hbottom'
    · rw [hp, hi, ← hF' edgeIndex]
      exact hedge'
  obtain ⟨c', hc', he'⟩ := hactive'
  have halign := actualCont_exists_step5_aligned U P t q ht rfl f g hf hg c c'
    hc hc' hserv hi hp
  have hvec := actualCont_exists_step2_vector U P t f hf c hc e he
  have hvec' := actualCont_exists_step2_vector U P q g hg c' hc' e' he'
  let a' := q.2.val.frame ((U.recordOf P q g hg).endpoints e').1
  let b' := q.2.val.frame ((U.recordOf P q g hg).endpoints e').2
  have hsegorder : segment ℝ a' b' = segment ℝ x w := by
    have h := image_segment ℝ q.2.val.frame.toAffineEquiv.toAffineMap
      ((U.recordOf P q g hg).endpoints e').1 ((U.recordOf P q g hg).endpoints e').2
    rw [← (actualCont_exists_step2_endpoints (U.recordOf P q g hg) e').2] at h
    have h' : q.2.val.cell 0 e'.val = segment ℝ a' b' := by
      simpa [FramedNode.cell, FramedNode.prototypeFrame, a', b'] using h
    exact h'.symm.trans hseg'
  have hdir : 0 < inner ℝ (x - p) (b' - a') := by
    have h := halign.2.2.1
    have hcvec : x - p = t.2.val.frame.linearIsometryEquiv (chainVector c) := by
      rw [← hvec]
      simpa only [p, x, hterminal] using
        (t.2.val.frame.map_vsub ((U.recordOf P t f hf).endpoints e).2
          ((U.recordOf P t f hf).endpoints e).1).symm
    have hcvec' : b' - a' = q.2.val.frame.linearIsometryEquiv (chainVector c') := by
      rw [← hvec']
      exact (q.2.val.frame.map_vsub _ _).symm
    rw [hcvec, hcvec', LinearIsometryEquiv.inner_map_eq_flip]
    exact h
  have horder : a' = x ∧ b' = w := by
    apply actualCont_exists_step6_order a' b' x w hsegorder
    obtain ⟨k, hk, hkw⟩ := hnext
    rw [hkw, real_inner_smul_right]
    exact mul_pos hk (by simpa only [real_inner_comm] using hdir)
  have hinitial : vertexPoint v' = ((U.recordOf P q g hg).endpoints e').1 :=
    q.2.val.frame.injective (hv'.trans horder.1.symm)
  have hvertex : (q.2.val.frame.trans t.2.val.frame.symm) (vertexPoint v') =
      vertexPoint v := by
    change t.2.val.frame.symm (q.2.val.frame (vertexPoint v')) = _
    rw [hv']
    exact t.2.val.frame.symm_apply_apply _
  have hj := actualCont_exists_step6_join p x w hnext
  have houter : t.2.val.frame.symm w =
      (q.2.val.frame.trans t.2.val.frame.symm) ((U.recordOf P q g hg).endpoints e').2 := by
    exact congrArg t.2.val.frame.symm horder.2.symm
  have hsegment : e.val.carrier ∪
      placedSet (q.2.val.frame.trans t.2.val.frame.symm) e'.val.carrier =
      segment ℝ ((U.recordOf P t f hf).endpoints e).1
        ((q.2.val.frame.trans t.2.val.frame.symm)
          ((U.recordOf P q g hg).endpoints e').2) := by
    have h := congrArg (fun K : Set (E d) =>
      t.2.val.frame.symm.toAffineEquiv.toAffineMap '' K) hj.1
    dsimp only at h
    rw [Set.image_union, image_segment, image_segment, image_segment] at h
    simp only [AffineEquiv.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineEquiv,
      p, x, AffineIsometryEquiv.symm_apply_apply, houter] at h
    have heq : placedSet (q.2.val.frame.trans t.2.val.frame.symm) e'.val.carrier =
        segment ℝ (vertexPoint v) (t.2.val.frame.symm w) := by
      have h' := congrArg (fun K : Set (E d) =>
        t.2.val.frame.symm.toAffineEquiv.toAffineMap '' K) hseg'
      dsimp only at h'
      rw [image_segment] at h'
      simpa [q, Q, FramedNode.cell, FramedNode.prototypeFrame, placedSet,
        Set.image_image, x] using h'
    rw [(actualCont_exists_step2_endpoints (U.recordOf P t f hf) e).2,
      ← hterminal, heq, houter]
    exact h
  have hjunction : vertexPoint v ∈ openSegment ℝ
      ((U.recordOf P t f hf).endpoints e).1
      ((q.2.val.frame.trans t.2.val.frame.symm)
        ((U.recordOf P q g hg).endpoints e').2) := by
    have h := Set.mem_image_of_mem t.2.val.frame.symm hj.2
    change t.2.val.frame.symm x ∈
      t.2.val.frame.symm.toAffineEquiv.toAffineMap '' openSegment ℝ p w at h
    rw [image_openSegment] at h
    simpa only [AffineEquiv.coe_toAffineMap, AffineIsometryEquiv.coe_toAffineEquiv,
      p, x, AffineIsometryEquiv.symm_apply_apply, houter] using h
  obtain ⟨θ, hcentral, htiles, hnone, hactual⟩ :=
    actualCont_exists_step6_configuration U P t q ht rfl
  refine ⟨{
    configuration := θ
    central_eq := hcentral
    other := q.2.val.move t.2.val.frame.symm
    label := leafTypeOf U P q rfl
    other_mem := by rw [htiles]; simp
    tiles_eq := htiles
    annotation_none := hnone
    record := U.recordOf P q g hg
    record_eq := ?_
    type_eq := rfl
    centralChain := c
    central_edge := he
    otherChain := c'
    edge := e'
    other_edge := he'
    vertex := v'
    initial := hinitial
    vertex_eq := hvertex
    aligned := halign
    segment_eq := hsegment
    junction_interior := hjunction }, hactual⟩
  change leafRecord (leafTypeOf U P q rfl) g.val = some (U.recordOf P q g hg)
  rw [actualCont_exists_step1_readout U P q rfl g]
  simp only [HonestSource.facetRecordOf, dif_neg hg]

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

/-- Step 1 of the V4 proof of `honest_rows_step1_cont_geometry` (V4 2.8):
"let t be a native tile ... of its facet f (provider g)". A non-NULL leaf
readout is the actual record of a nonfault facet of that native tile. -/
private theorem honest_rows_step1_cont_geometry_step1_record
    (U : HonestSource S) (P : Params S) (t : U.Node) (ht : t.1 = 0)
    (r : FacetRecord P)
    (hr : leafRecord (leafTypeOf U P t ht) r.facet.val = some r) :
    ∃ (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f),
      r = U.recordOf P t f hf := by
  unfold leafRecord at hr
  rw [← prePattern_of_leafType] at hr
  change stateRecordAt (stateOf U P t) r.facet.val = some r at hr
  unfold stateRecordAt at hr
  split at hr
  next h =>
    change U.facetRecordOf P t ⟨r.facet.val, h⟩ = some r at hr
    unfold HonestSource.facetRecordOf at hr
    split at hr
    next hf => contradiction
    next hf => exact ⟨_, hf, (Option.some.inj hr).symm⟩
  next h => contradiction

/-- Step 1 of the V4 proof of `honest_rows_step1_cont_geometry` (V4 2.8):
"with owner t'' ... whose record". The label on an actual native tile reads
the record of each of its nonfault facets. -/
private theorem honest_rows_step1_cont_geometry_step1_read
    (U : HonestSource S) (P : Params S) (t : U.Node) (ht : t.1 = 0)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f) :
    leafRecord (leafTypeOf U P t ht) f.val = some (U.recordOf P t f hf) := by
  unfold leafRecord
  rw [← prePattern_of_leafType]
  change stateRecordAt (stateOf U P t) f.val = _
  simp [stateRecordAt, stateOf, HonestSource.facetRecordOf, f.property, hf]

/-- Step 1 of the V4 proof of `honest_rows_step1_cont_geometry` (V4 Remark 2.1):
"a j-cell inside the j-cell F_j has its relative interior inside relint F_j".
Containment of placed cells of equal dimension also identifies their affine spans. -/
private theorem honest_rows_step1_cont_geometry_step1_spans
    (g h : E d ≃ᵃ[ℝ] E d) (e f : Cell d) (hd : e.dim = f.dim)
    (hsub : g '' e.carrier ⊆ h '' f.carrier) :
    affineSpan ℝ (g '' e.carrier) = affineSpan ℝ (h '' f.carrier) ∧
      relint (g '' e.carrier) ⊆ relint (h '' f.carrier) := by
  have hdim (T : E d ≃ᵃ[ℝ] E d) (c : Cell d) :
      Module.finrank ℝ (affineSpan ℝ (T '' c.carrier)).direction = c.dim := by
    change Module.finrank ℝ (affineSpan ℝ (T.toAffineMap '' c.carrier)).direction = _
    rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
    exact (LinearEquiv.finrank_map_eq T.linear _).trans c.flat.dimension
  have hle := affineSpan_mono ℝ hsub
  have hs : affineSpan ℝ (g '' e.carrier) = affineSpan ℝ (h '' f.carrier) :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
      (Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
        ((hdim g e).trans (hd.trans (hdim h f).symm)))
      ((e.flat.connected.nonempty.image g).mono (subset_affineSpan ℝ _)) hle
  refine ⟨hs, ?_⟩
  unfold relint intrinsicInterior
  rw [hs]
  exact Set.image_mono (interior_mono (Set.preimage_mono hsub))

/-- Step 1 of the V4 proof of `honest_rows_step1_cont_geometry_step2_successor`
(V4 Remark 2.1): "restricting recursively along the chain, s₂ is a polygon of
the recursive trace ... with owner B and recorded chain". Normalize an exact
native descendant and retain the given cofaces as a trace occurrence. -/
private theorem honest_rows_step1_cont_geometry_step2_successor_step1_trace
    (N C : FramedNode S) (n : ℕ) (F : FacetFlag S N.ty) (c : FacetFlag S C.ty)
    (hC : C.IsDescendant 0 N n)
    (hc : ∀ j, C.cell 0 (c.cell j).val ⊆ N.cell n (F.cell j).val) :
    ∃ a : TracePiece N.ty F n, placedTraceOwner N n n F a = C ∧
      ∀ i : ChainIndex d (traceDimension d),
        (a.chain.cell i).val = (c.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val := by
  obtain ⟨r, hr, w, hC⟩ := hC
  simp only [zero_add] at hr
  subst r
  change C = (S.nativeTile N.ty n w).move N.frame at hC
  subst C
  let a : TracePiece N.ty F n := {
    owner := w
    chain := {
      cell := fun i => c.cell ⟨i.val.val, i.property.2, i.val.isLt⟩
      dimension := fun i => c.dimension ⟨i.val.val, i.property.2, i.val.isLt⟩
      nested := fun i j hij => c.nested _ _ hij
      contained := by
        intro i
        apply (Set.image_subset_image_iff N.frame.injective).mp
        simpa [FramedNode.cell, FramedNode.prototypeFrame, FramedNode.move,
          Set.image_image] using hc ⟨i.val.val, i.property.2, i.val.isLt⟩ } }
  refine ⟨a, ?_, fun _ => rfl⟩
  simp only [a, placedTraceOwner, Nat.sub_self, SubstSystem.nativeTile]

/-- Step 2 of the V4 proof of `honest_rows_step1_cont_geometry_step2_successor`
(V4 Remark 2.1): "every selected owner of the trace with its recorded chain ...
has the 1-cells of G₂ along h as chain-active edges". Append the given boundary
edge to the recorded cofaces, retaining containment in every ancestral flag cell.
The same construction includes the one-dimensional trace when d = 2. -/
private theorem honest_rows_step1_cont_geometry_step2_successor_step2_flag
    (N : FramedNode S) (n : ℕ) (F : FacetFlag S N.ty) (a : TracePiece N.ty F n)
    (e : PrototypeEdge S a.tile.ty)
    (heB : (placedTraceOwner N n n F a).cell 0 e.val ⊆
      placedTraceCarrier N n n F a)
    (heF : (placedTraceOwner N n n F a).cell 0 e.val ⊆
      N.cell n (F.cell edgeIndex).val) :
    ∃ c : FacetFlag S a.tile.ty, (c.cell edgeIndex).val = e.val ∧
      ∀ j, (placedTraceOwner N n n F a).cell 0 (c.cell j).val ⊆
        N.cell n (F.cell j).val := by
  have hcell (f : Cell d) : (placedTraceOwner N n n F a).cell 0 f =
      tracePlacement N n n '' (a.tile.cell 0 f) := by
    simpa only [Nat.sub_self] using placedTraceOwner_cells N n n le_rfl F a f
  have hsub : e.val.carrier ⊆ a.bottom.val.carrier := by
    rw [hcell] at heB
    exact (Set.image_subset_image_iff (a.tile.prototypeFrame 0).injective).mp
      ((Set.image_subset_image_iff (tracePlacement N n n).injective).mp heB)
  have hdim : traceDimension d ≤ 2 := min_le_left _ _
  let idx (j : FlagIndex d) (hj : j.val ≠ 1) : ChainIndex d (traceDimension d) :=
    ⟨⟨j.val, j.property.2⟩,
      by change traceDimension d ≤ j.val; have := j.property.1; omega, j.property.1⟩
  let c : FacetFlag S a.tile.ty := {
    cell := fun j => if hj : j.val = 1 then edgeCell e else a.chain.cell (idx j hj)
    dimension := by
      intro j
      split_ifs with hj
      · exact (Finset.mem_filter.mp e.property).2.trans hj.symm
      · exact a.chain.dimension (idx j hj)
    nested := by
      intro i j hij
      split_ifs with hi hj hj
      · exact Subset.rfl
      · exact hsub.trans (a.chain.nested TracePiece.bottomIndex (idx j hj)
          (by have := j.property.1; change traceDimension d ≤ j.val; omega))
      · have := i.property.1
        omega
      · exact a.chain.nested (idx i hi) (idx j hj) hij }
  refine ⟨c, by simp [c, edgeIndex, edgeCell], ?_⟩
  intro j
  by_cases hj : j.val = 1
  · have hj' : j = edgeIndex := Subtype.ext hj
    subst j
    simpa only [c, edgeIndex, dif_pos rfl, edgeCell] using heF
  · change (placedTraceOwner N n n F a).cell 0
      (if hj : j.val = 1 then edgeCell e else a.chain.cell (idx j hj)).val ⊆ _
    rw [dif_neg hj, hcell]
    refine (Set.image_mono (a.chain.contained (idx j hj))).trans_eq ?_
    simp [tracePlacement, FramedNode.cell, FramedNode.prototypeFrame, Set.image_image, idx]

/-- Step 2 of the V4 proof of `honest_rows_step1_cont_geometry` (V4 2.8):
"the polygons ... adjacent to h tile a neighbourhood of v in h ... so there
is a polygon ... on the far side of v ... with ... an edge ... with initial
endpoint v". This is only the subdivision geometry: both full chains lie
in the given ancestor flag. No record, orientation bit or template is involved.
The owners may coincide at a flat listed vertex; the positive scalar excludes
a degenerate continuing edge. -/
private theorem honest_rows_step1_cont_geometry_step2_successor
    (U : HonestSource S) (B t : U.Node) (ht : t.1 = 0)
    (hBt : U.hierarchy.ancestor t B.1 = B)
    (F : FacetFlag S B.2.val.ty) (c : FacetFlag S t.2.val.ty)
    (hc : ∀ j, t.2.val.cell t.1 (c.cell j).val ⊆ B.2.val.cell B.1 (F.cell j).val)
    (v : VertexName S t.2.val.ty) (a : E d)
    (he : t.2.val.cell t.1 (c.cell edgeIndex).val =
      segment ℝ a (t.2.val.prototypeFrame t.1 (vertexPoint v)))
    (hne : a ≠ t.2.val.prototypeFrame t.1 (vertexPoint v))
    (hv : t.2.val.prototypeFrame t.1 (vertexPoint v) ∈
      relint (B.2.val.cell B.1 (F.cell edgeIndex).val)) :
    ∃ (q : U.Node) (hq : q.1 = 0) (c' : FacetFlag S q.2.val.ty)
      (v' : VertexName S q.2.val.ty) (z : E d) (b : ℝ),
      U.hierarchy.ancestor q B.1 = B ∧
      (∀ j, q.2.val.cell q.1 (c'.cell j).val ⊆ B.2.val.cell B.1 (F.cell j).val) ∧
      q.2.val.prototypeFrame q.1 (vertexPoint v') =
        t.2.val.prototypeFrame t.1 (vertexPoint v) ∧
      q.2.val.cell q.1 (c'.cell edgeIndex).val =
        segment ℝ (t.2.val.prototypeFrame t.1 (vertexPoint v)) z ∧
      0 < b ∧ z - t.2.val.prototypeFrame t.1 (vertexPoint v) =
        b • (t.2.val.prototypeFrame t.1 (vertexPoint v) - a) := by
  have htB : t.2.val.IsDescendant 0 B.2.val B.1 := by
    have h := U.hierarchy.ancestor_descendant t B.1
    rw [hBt] at h
    simpa only [ht] using h
  obtain ⟨s, hs, hsc⟩ := honest_rows_step1_cont_geometry_step2_successor_step1_trace
    B.2.val t.2.val B.1 F c htB (by simpa only [ht] using hc)
  have hbottom : t.2.val.cell 0 (c.cell edgeIndex).val ⊆
      placedTraceCarrier B.2.val B.1 B.1 F s := by
    have h := placedTraceOwner_cells B.2.val B.1 B.1 le_rfl F s s.bottom.val
    rw [hs, Nat.sub_self] at h
    refine (Set.image_mono ?_).trans_eq h
    change (c.cell edgeIndex).val.carrier ⊆ (s.chain.cell TracePiece.bottomIndex).val.carrier
    rw [hsc]
    exact c.nested _ _ traceDimension_pos
  obtain ⟨s', e', v', z, hv', he', _, ⟨b, hb, hz⟩, heB, heF⟩ :=
    actualCont_exists_step3_trace_successor B.2.val B.1 F s (c.cell edgeIndex).val
      (by rw [hs]; exact Finset.mem_filter.mpr ⟨(c.cell edgeIndex).property,
        c.dimension edgeIndex⟩) a (t.2.val.prototypeFrame t.1 (vertexPoint v)) hne
      (by rw [hs]; simpa only [ht] using he)
      (by rw [hs]; exact hbottom)
      (by rw [hs]; simpa only [ht] using hc edgeIndex) hv
  let Q := placedTraceOwner B.2.val B.1 B.1 F s'
  have hQ : Q ∈ U.hierarchy.nodes 0 := by
    simpa only [Nat.sub_self] using
      U.hierarchy.placedTraceOwner_mem B.2.val B.1 B.1 B.2.property le_rfl F s'
  let q : U.Node := ⟨0, ⟨Q, hQ⟩⟩
  have hqty : q.2.val.ty = s'.tile.ty := by
    simp only [q, Q, placedTraceOwner, FramedNode.move, Nat.sub_self,
      TracePiece.tile, SubstSystem.nativeTile]
  let en : PrototypeEdge S s'.tile.ty := ⟨e'.val, by rw [← hqty]; exact e'.property⟩
  obtain ⟨G, hGe, hG⟩ := honest_rows_step1_cont_geometry_step2_successor_step2_flag
    B.2.val B.1 F s' en heB heF
  let c' : FacetFlag S q.2.val.ty := {
    cell := fun j => ⟨(G.cell j).val, by rw [hqty]; exact (G.cell j).property⟩
    dimension := G.dimension
    nested := G.nested }
  refine ⟨q, rfl, c', v', z, b, ?_, hG, ?_, ?_, hb, hz⟩
  · exact (actualCont_exists_step4_ancestor U q rfl B.1 B.2.val B.2.property s'.owner
      (by simp only [q, Q, placedTraceOwner, Nat.sub_self, SubstSystem.nativeTile])).trans
      (actualCont_exists_step4_reindex U B B.1 rfl B.2.property)
  · simpa [q, FramedNode.prototypeFrame] using hv'
  · change Q.cell 0 (G.cell edgeIndex).val = _
    rw [hGe]
    exact he'

/-- Step 3 of the V4 proof of `honest_rows_step1_cont_geometry` (V4 2.8):
"same provider g, same serving child H". A native descendant facet contained
in the provider inherits its carrier and birth parent, hence its serving node. -/
private theorem honest_rows_step1_cont_geometry_step3_provider
    (U : HonestSource S) (t q : U.Node) (hq : q.1 = 0)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (g : FacetName S q.2.val.ty)
    (hanc : U.hierarchy.ancestor q (U.hierarchy.servingChild t f hf).1 =
      U.hierarchy.servingChild t f hf)
    (hsub : q.2.val.cell q.1 g.val ⊆ U.hierarchy.providerCarrier t f hf) :
    ∃ hg : ¬ U.hierarchy.IsFault q g,
      U.hierarchy.birthParent q g hg = U.hierarchy.birthParent t f hf ∧
      U.hierarchy.providerCarrier q g hg = U.hierarchy.providerCarrier t f hf ∧
      U.hierarchy.servingChild q g hg = U.hierarchy.servingChild t f hf := by
  let B := U.hierarchy.servingChild t f hf
  let G : FacetName S B.2.val.ty := (U.hierarchy.firstProvider t f hf).2
  have hpar : U.hierarchy.ancestor t ((U.hierarchy.firstProvider t f hf).1 + 1) =
      U.hierarchy.parentNode B := by
    change (U.hierarchy.parentNode^[((U.hierarchy.firstProvider t f hf).1 + 1)]) t = _
    rw [Function.iterate_succ_apply']
    rfl
  have hint := (U.hierarchy.firstProvider_spec t f hf).2.2
  rw [hpar] at hint
  obtain ⟨hG, hcar, hbirth, _⟩ := U.hierarchy.restriction_det_internal B G hint
  obtain ⟨hg, hcar', hbirth'⟩ :=
    U.hierarchy.provider_inherited B q B.1 hanc G g hG hsub
  have hb : U.hierarchy.birthParent q g hg = U.hierarchy.birthParent t f hf :=
    hbirth'.trans hbirth
  refine ⟨hg, hb, hcar'.trans hcar, ?_⟩
  have hh := congrArg (fun x : U.Node => x.1) hb
  change (U.hierarchy.servingChild q g hg).1 + 1 = B.1 + 1 at hh
  have hh' := U.hierarchy.ancestor_height q (U.hierarchy.firstProvider q g hg).1
  have hoff : (U.hierarchy.firstProvider q g hg).1 = B.1 := by
    change (U.hierarchy.servingChild q g hg).1 = _ at hh'
    omega
  change U.hierarchy.ancestor q (U.hierarchy.firstProvider q g hg).1 = B
  rwa [hoff]

/-- Step 3 of the V4 proof of `honest_rows_step1_cont_geometry` (V4 Remark 2.1):
"its recorded chain ... has aff = aff F_j ... [so it] is a chain-active edge".
A full chain contained in the serving flag has exactly its provider strata;
choose the induced orientation and enter it in the actual chain table. -/
private theorem honest_rows_step1_cont_geometry_step3_activity
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (B : U.Node) (hB : U.hierarchy.servingChild q f hf = B)
    (F : FacetFlag S B.2.val.ty)
    (hF : ∀ j, B.2.val.cell B.1 (F.cell j).val = U.providerPlacement P q f hf ''
      ((P.flag (U.recordIncidence P q f hf)).flag.cell j).val.carrier)
    (c : FacetFlag S q.2.val.ty) (hc : (c.cell facetIndex).val = f.val)
    (hsub : ∀ j, q.2.val.cell q.1 (c.cell j).val ⊆ B.2.val.cell B.1 (F.cell j).val) :
    ∃ z : OrientedChain f, z.chain.val = c ∧ z ∈ U.recordChains P q f hf := by
  classical
  subst B
  let z : OrientedChain f := ⟨⟨c, hc⟩, decide (0 < inner ℝ
    (U.counterDirection P q f hf) ((q.2.val.prototypeFrame q.1).linear
      (edgeVector (restrictionOp_source_step4_chains_step1_edge c))))⟩
  refine ⟨z, rfl, Finset.mem_filter.mpr ⟨by simp [allOrientedChains], ?_⟩⟩
  constructor
  · intro j
    have hs := U.cellInFacet_placed q f
      ⟨c.cell j, restrictionOp_source_step4_chains_step1_subset z j⟩
    obtain ⟨hspan, hrel⟩ := honest_rows_step1_cont_geometry_step1_spans
      (q.2.val.prototypeFrame q.1)
      ((U.hierarchy.servingChild q f hf).2.val.prototypeFrame
        (U.hierarchy.servingChild q f hf).1)
      (c.cell j).val (F.cell j).val ((c.dimension j).trans (F.dimension j).symm) (hsub j)
    have hstr : U.hierarchy.stratumMap q f hf (c.cell j) hs = F.cell j :=
      ((Classical.choose_spec (U.hierarchy.stratum_exists_unique q f hf
        (c.cell j) hs)).2 (F.cell j) hrel).symm
    refine ⟨hs, ?_, hspan.trans (congrArg (affineSpan ℝ) (hF j))⟩
    change (U.hierarchy.servingChild q f hf).2.val.cell
      (U.hierarchy.servingChild q f hf).1
      (U.hierarchy.stratumMap q f hf (c.cell j) hs).val = _
    rw [hstr]
    exact hF j
  · exact decide_eq_true_iff

open private birth_ascent_routing_step3_desc_subset from Enforce.Source.Routing in

/-- Step 4 of the V4 proof of `honest_rows_step1_cont_geometry` (V4 2.8):
"both chains lie in the positioned flag ... with its orientations".
The successive coface sides and the inward tile side of a descendant full
flag contained in an ancestor flag are the ancestor's sides in ambient coordinates. -/
private theorem honest_rows_step1_cont_geometry_step4_sides
    (U : HonestSource S) (B t : U.Node)
    (hBt : U.hierarchy.ancestor t (B.1 - t.1) = B)
    (F : FacetFlag S B.2.val.ty) (c : FacetFlag S t.2.val.ty)
    (hc : ∀ j, t.2.val.cell t.1 (c.cell j).val ⊆ B.2.val.cell B.1 (F.cell j).val) :
    (∀ j, (t.2.val.prototypeFrame t.1).linear '' flagSide c j =
      (B.2.val.prototypeFrame B.1).linear '' flagSide F j) ∧
    (t.2.val.prototypeFrame t.1).linear ''
        tangentCone (S.proto t.2.val.ty).carrier (cellAnchor (c.cell facetIndex).val) =
      (B.2.val.prototypeFrame B.1).linear ''
        tangentCone (S.proto B.2.val.ty).carrier (cellAnchor (F.cell facetIndex).val) := by
  have hfit (j : FlagIndex d) := honest_rows_step1_cont_geometry_step1_spans
    (t.2.val.prototypeFrame t.1) (B.2.val.prototypeFrame B.1)
    (c.cell j).val (F.cell j).val ((c.dimension j).trans (F.dimension j).symm) (hc j)
  constructor
  · intro j
    exact actualCont_exists_step5_coface_side c F
      (t.2.val.prototypeFrame t.1) (B.2.val.prototypeFrame B.1) j
      (hfit _).2 (hfit _).2 (hfit _).1 (hfit _).1
  · let f : FacetName S t.2.val.ty := ⟨(c.cell facetIndex).val,
      Finset.mem_filter.mpr ⟨(c.cell facetIndex).property, c.dimension facetIndex⟩⟩
    let g : FacetName S B.2.val.ty := ⟨(F.cell facetIndex).val,
      Finset.mem_filter.mpr ⟨(F.cell facetIndex).property, F.dimension facetIndex⟩⟩
    have hd := U.hierarchy.ancestor_descendant t (B.1 - t.1)
    rw [hBt] at hd
    have hsub := birth_ascent_routing_step3_desc_subset t.2.val B.2.val t.1 B.1 hd
    apply actualCont_exists_step5_inward f g
      (t.2.val.prototypeFrame t.1) (B.2.val.prototypeFrame B.1)
    · simpa only [FramedNode.carrier, FramedNode.prototypeFrame, placedSet,
        SubstSystem.supertile, Set.image_image, AffineEquiv.coe_trans,
        LinearEquiv.coe_toAffineEquiv, AffineIsometryEquiv.coe_toAffineEquiv] using hsub
    · exact (hfit facetIndex).2

/-- Step 4 of the V4 proof of `honest_rows_step1_cont_geometry` (V4 2.8):
"both chains lie in the positioned flag ... with its orientations".
Cancel the central isometric frame from agreement of the ambient flags and sides. -/
private theorem honest_rows_step1_cont_geometry_step4_alignment
    {P : Params S} (r r' : FacetRecord P)
    (c : OrientedChain r.facet) (c' : OrientedChain r'.facet) (T Q : Iso d)
    (hspan : ∀ j, affineSpan ℝ (T '' (c.chain.val.cell j).val.carrier) =
      affineSpan ℝ (Q '' (c'.chain.val.cell j).val.carrier))
    (hside : ∀ j, T.linearIsometryEquiv '' flagSide c.chain.val j =
      Q.linearIsometryEquiv '' flagSide c'.chain.val j)
    (hdir : 0 < inner ℝ (T.linearIsometryEquiv (chainVector c))
      (Q.linearIsometryEquiv (chainVector c')))
    (hcone : T.linearIsometryEquiv ''
        tangentCone (S.proto r.ty).carrier (cellAnchor r.facet.val) =
      Q.linearIsometryEquiv ''
        tangentCone (S.proto r'.ty).carrier (cellAnchor r'.facet.val)) :
    ChainsAligned r r' c c' (Q.trans T.symm) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    apply (restrictionOp_source_step4_chains_step2_span T.toAffineEquiv _ _).mp
    change affineSpan ℝ (T '' (c.chain.val.cell j).val.carrier) =
      affineSpan ℝ (T '' ((Q.trans T.symm) '' (c'.chain.val.cell j).val.carrier))
    simpa only [Set.image_image, AffineIsometryEquiv.coe_trans, Function.comp_apply,
      AffineIsometryEquiv.apply_symm_apply] using hspan j
  · intro j
    apply T.linearIsometryEquiv.injective.image_injective
    change T.linearIsometryEquiv '' flagSide c.chain.val j =
      T.linearIsometryEquiv ''
        ((fun x => T.linearIsometryEquiv.symm (Q.linearIsometryEquiv x)) ''
          flagSide c'.chain.val j)
    simpa only [Set.image_image, LinearIsometryEquiv.apply_symm_apply] using hside j
  · change 0 < inner ℝ (chainVector c)
      (T.linearIsometryEquiv.symm (Q.linearIsometryEquiv (chainVector c')))
    rw [← T.linearIsometryEquiv.inner_map_map]
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hdir
  · apply T.linearIsometryEquiv.injective.image_injective
    change T.linearIsometryEquiv ''
        tangentCone (S.proto r.ty).carrier (cellAnchor r.facet.val) =
      T.linearIsometryEquiv ''
        ((fun x => T.linearIsometryEquiv.symm (Q.linearIsometryEquiv x)) ''
          tangentCone (S.proto r'.ty).carrier (cellAnchor r'.facet.val))
    simpa only [Set.image_image, LinearIsometryEquiv.apply_symm_apply] using hcone

/-- Step 5 of the V4 proof of `honest_rows_step1_cont_geometry` (V4 2.8):
"with its orientations". Every active chain on the same edge has the same
orientation bit; the record's endpoints therefore agree with its signed vector. -/
private theorem honest_rows_step1_cont_geometry_step5_endpoints
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (c : OrientedChain f) (hc : c ∈ U.recordChains P q f hf)
    (e : PrototypeEdge S q.2.val.ty)
    (he : (c.chain.val.cell edgeIndex).val = e.val) :
    e.val.carrier = segment ℝ ((U.recordOf P q f hf).endpoints e).1
        ((U.recordOf P q f hf).endpoints e).2 ∧
      ((U.recordOf P q f hf).endpoints e).1 ≠ ((U.recordOf P q f hf).endpoints e).2 ∧
      chainVector c = ((U.recordOf P q f hf).endpoints e).2 -
        ((U.recordOf P q f hf).endpoints e).1 := by
  classical
  have hedge (z : OrientedChain f) (hz : (z.chain.val.cell edgeIndex).val = e.val) :
      restrictionOp_source_step4_chains_step1_edge z.chain.val =
        (⟨q.2.val.ty, e⟩ : EdgeName S) := by
    exact congrArg (fun e : PrototypeEdge S q.2.val.ty =>
      (⟨q.2.val.ty, e⟩ : EdgeName S)) (Subtype.ext hz)
  have horient (z : OrientedChain f) (hz : z ∈ U.recordChains P q f hf)
      (hze : (z.chain.val.cell edgeIndex).val = e.val) :
      z.forward = true ↔ 0 < inner ℝ (U.counterDirection P q f hf)
        ((q.2.val.prototypeFrame q.1).linear (edgeVector ⟨q.2.val.ty, e⟩)) := by
    have ha := (Finset.mem_filter.mp hz).2.2
    change z.forward = true ↔ 0 < inner ℝ (U.counterDirection P q f hf)
      ((q.2.val.prototypeFrame q.1).linear
        (edgeVector (restrictionOp_source_step4_chains_step1_edge z.chain.val))) at ha
    rwa [hedge z hze] at ha
  have hforward : (U.recordOf P q f hf).edgeForward e = c.forward := by
    apply Bool.eq_iff_iff.mpr
    simp only [FacetRecord.edgeForward, List.any_eq_true, Finset.mem_toList,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨z, hz, hze, hztrue⟩
      exact (horient c hc he).mpr ((horient z hz hze).mp hztrue)
    · intro h
      exact ⟨c, hc, he, h⟩
  have hvec : chainVector c = if c.forward then edgeVector ⟨q.2.val.ty, e⟩
      else -edgeVector ⟨q.2.val.ty, e⟩ := by
    change (if c.forward then
      edgeVector (restrictionOp_source_step4_chains_step1_edge c.chain.val)
      else -edgeVector (restrictionOp_source_step4_chains_step1_edge c.chain.val)) = _
    rw [hedge c he]
  have hab := Classical.choose_spec (edge_endpoints_exist (⟨q.2.val.ty, e⟩ : EdgeName S))
  rw [hvec]
  simp only [FacetRecord.endpoints, hforward]
  cases c.forward <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact ⟨hab.2.trans (segment_symm _ _ _), Ne.symm hab.1, neg_sub _ _⟩
  · exact ⟨hab.2, hab.1, rfl⟩

/-- Step 5 of the V4 proof of `honest_rows_step1_cont_geometry` (V4 2.8):
"after v in the orientation". The oriented coordinate distinguishes all
points of a nondegenerate segment. -/
private theorem honest_rows_step1_cont_geometry_step5_projection
    (p q : E d) (hpq : p ≠ q) :
    Set.InjOn (fun x => inner ℝ (q - p) x) (segment ℝ p q) := by
  intro x hx y hy hxy
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  have hpos : 0 < inner ℝ (q - p) (q - p) :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr hpq.symm)
  have hst : s = t := by
    simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub,
      inner_add_right, inner_smul_right] at hxy
    nlinarith
  rw [hst]

/-- Step 5 of the V4 proof of `honest_rows_step1_cont_geometry` (V4 2.8):
"an edge ... with initial endpoint v". Equal segments with agreeing
nonzero orientations have equal ordered endpoints. -/
private theorem honest_rows_step1_cont_geometry_step5_ordered_endpoints
    (a b x y : E d) (hs : segment ℝ a b = segment ℝ x y)
    (hp : 0 < inner ℝ (b - a) (y - x)) : a = x ∧ b = y := by
  have hxy : x ≠ y := by rintro rfl; simpa using hp
  have hbound (p q z w : E d) (hz : z ∈ segment ℝ p q)
      (hpq : inner ℝ w p ≤ inner ℝ w q) :
      inner ℝ w p ≤ inner ℝ w z ∧ inner ℝ w z ≤ inner ℝ w q := by
    obtain ⟨u, v, hu, hv, huv, rfl⟩ := hz
    simp only [inner_add_right, inner_smul_right]
    have hu' := mul_nonneg hu (sub_nonneg.mpr hpq)
    have hv' := mul_nonneg hv (sub_nonneg.mpr hpq)
    have hp' := congrArg (fun k : ℝ => k * inner ℝ w p) huv
    have hq' := congrArg (fun k : ℝ => k * inner ℝ w q) huv
    constructor <;> nlinarith
  have hab : inner ℝ (y - x) a ≤ inner ℝ (y - x) b := by
    rw [real_inner_comm, inner_sub_right] at hp
    linarith
  have hxy' : inner ℝ (y - x) x ≤ inner ℝ (y - x) y := by
    have h : 0 ≤ inner ℝ (y - x) (y - x) := real_inner_self_nonneg
    rw [inner_sub_right] at h
    linarith
  have ha : a ∈ segment ℝ x y := hs ▸ left_mem_segment ℝ a b
  have hb : b ∈ segment ℝ x y := hs ▸ right_mem_segment ℝ a b
  have hx : x ∈ segment ℝ a b := hs.symm ▸ left_mem_segment ℝ x y
  have hy : y ∈ segment ℝ a b := hs.symm ▸ right_mem_segment ℝ x y
  have hinj := honest_rows_step1_cont_geometry_step5_projection x y hxy
  exact ⟨hinj ha (left_mem_segment ℝ x y)
    (le_antisymm (hbound a b x _ hx hab).1 (hbound x y a _ ha hxy').1),
    hinj hb (right_mem_segment ℝ x y)
      (le_antisymm (hbound x y b _ hb hxy').2 (hbound a b y _ hy hab).2)⟩

/-- Step 5 of the V4 proof of `honest_rows_step1_cont_geometry` (V4 2.8):
"on the far side of v (after v in the orientation)". Two consecutive
positively oriented collinear segments form one segment across their junction. -/
private theorem honest_rows_step1_cont_geometry_step5_join
    (a x z : E d) (b : ℝ) (hb : 0 < b) (hz : z - x = b • (x - a)) :
    segment ℝ a x ∪ segment ℝ x z = segment ℝ a z ∧ x ∈ openSegment ℝ a z := by
  let L : ℝ →ᵃ[ℝ] E d := AffineMap.lineMap a x
  have h0 : L 0 = a := AffineMap.lineMap_apply_zero _ _
  have h1 : L 1 = x := AffineMap.lineMap_apply_one _ _
  have hz' : L (1 + b) = z := by
    rw [sub_eq_iff_eq_add] at hz
    rw [hz]
    simp only [L, AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
    module
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have h1b : (1 : ℝ) ≤ 1 + b := by linarith
  have h0b : (0 : ℝ) < 1 + b := by linarith
  have hseg (u v : ℝ) (huv : u ≤ v) :
      segment ℝ (L u) (L v) = L '' Icc u v := by
    rw [← image_segment, segment_eq_Icc huv]
  constructor
  · rw [← h0, ← h1, ← hz', hseg 0 1 h01, hseg 1 (1 + b) h1b,
      hseg 0 (1 + b) h0b.le, ← Set.image_union, Set.Icc_union_Icc_eq_Icc h01 h1b]
  · rw [← h0, ← hz', ← image_openSegment, openSegment_eq_Ioo h0b]
    exact ⟨1, ⟨by norm_num, by linarith⟩, h1⟩

/-- Step 6 of the V4 proof of `honest_rows_step1_cont_geometry` (V4 2.8):
"a template realised by actual tiles". Two actual native tiles, with their
actual leaf labels and relative frames, form an actual configuration. Equal
owners give a singleton, so no distinct-owner assumption is needed. -/
private theorem honest_rows_step1_cont_geometry_step6_configuration
    (U : HonestSource S) (P : Params S) (t q : U.Node) (ht : t.1 = 0) (hq : q.1 = 0) :
    ∃ θ : Template P, IsActualTemplate U P t ht θ ∧
      θ.central = leafTypeOf U P t ht ∧
      θ.tiles =
        {((⟨(leafTypeOf U P t ht).prototype, AffineIsometryEquiv.refl ℝ (E d)⟩ :
            FramedNode S), leafTypeOf U P t ht),
          (q.2.val.move t.2.val.frame.symm, leafTypeOf U P q hq)} ∧
      θ.annotation = none := by
  classical
  let l := leafTypeOf U P t ht
  let l' := leafTypeOf U P q hq
  let z : FramedNode S × LeafType P :=
    (⟨l.prototype, AffineIsometryEquiv.refl ℝ (E d)⟩, l)
  let w : FramedNode S × LeafType P := (q.2.val.move t.2.val.frame.symm, l')
  have hz : z.1 = t.2.val.move t.2.val.frame.symm := by
    simp [z, l, leafTypeOf_type, FramedNode.move]
  have hreal (a : FramedNode S × LeafType P) (ha : a ∈ ({z, w} : Finset _)) :
      ∃ (p : U.Node) (hp : p.1 = 0),
        a.1 = p.2.val.move t.2.val.frame.symm ∧ a.2 = leafTypeOf U P p hp := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨t, ht, hz, rfl⟩
    · rcases Finset.mem_singleton.mp ha with rfl
      exact ⟨q, hq, rfl, rfl⟩
  have hdis : (({z, w} : Finset _) : Set (FramedNode S × LeafType P)).PairwiseDisjoint
      (fun a => interior (a.1.carrier 0)) := by
    intro a ha b hb hne
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    obtain ⟨p, hp, hpa, hla⟩ := hreal a ha
    obtain ⟨r, hr, hrb, hlb⟩ := hreal b hb
    have hmove (N : FramedNode S) :
        interior ((N.move t.2.val.frame.symm).carrier 0) =
          t.2.val.frame.symm '' interior (N.carrier 0) := by
      have hcarrier : (N.move t.2.val.frame.symm).carrier 0 =
          t.2.val.frame.symm '' N.carrier 0 := by
        simp [FramedNode.carrier, FramedNode.move, placedSet, Set.image_image]
      rw [hcarrier]
      exact (t.2.val.frame.symm.toHomeomorph.image_interior _).symm
    dsimp only at hxa hxb
    rw [hpa, hmove] at hxa
    rw [hrb, hmove] at hxb
    obtain ⟨xp, hxp, hxp'⟩ := hxa
    obtain ⟨xr, hxr, hxr'⟩ := hxb
    have hxx : xp = xr := t.2.val.frame.symm.injective (hxp'.trans hxr'.symm)
    have hpr : p.2.val = r.2.val := U.hierarchy.same_height_disjoint 0 p.2.val r.2.val
      (hp ▸ p.2.property) (hr ▸ r.2.property) xp hxp (hxx.symm ▸ hxr)
    have hnode : p = r := by
      rcases p with ⟨n, p, hpm⟩
      rcases r with ⟨m, r, hrm⟩
      dsimp only at hp hr hpr
      subst n
      subst m
      cases hpr
      rfl
    subst r
    exact hne (Prod.ext (hpa.trans hrb.symm) (hla.trans hlb.symm))
  let θ : Template P := {
    central := l
    tiles := {z, w}
    types_match := by
      intro a ha
      obtain ⟨p, hp, hp', hl⟩ := hreal a ha
      rw [hp', hl, leafTypeOf_type]
      rfl
    disjoint := hdis
    central_mem := Finset.mem_insert_self _ _
    annotation := none }
  exact ⟨θ, ⟨rfl, hreal⟩, rfl, rfl, rfl⟩

/-- Step 1 of the V4 proof of `honest_rows` (V4 2.8): "CONT: ... By Remark 2.1, $t$ is a
selected owner of the recursive trace $\mathcal P_2$ of $H$ ... so there is a polygon $s_2''$
adjacent to $h$ on the far side of $v$ ... with owner $t''$ and an edge $e''$ along $h$ with
initial endpoint $v$ ... its recorded chain $s_2''\subset\cdots\subset s_{d-1}''$ has
$\operatorname{aff}=\operatorname{aff}F_j$, so by Remark 2.1 (converse part) $e''$ is a
chain-active edge". The actual continuation geometry follows the recorded active chains. -/
private theorem honest_rows_step1_cont_geometry (U : HonestSource S) (P : Params S)
    (t : U.Node) (ht : t.1 = 0) (slot : ContSlot (leafTypeOf U P t ht)) :
    ∃ T : ContTemplate slot, IsActualTemplate U P t ht T.configuration ∧
      T.centralChain ∈ slot.record.chains ∧ T.otherChain ∈ T.record.chains := by
  classical
  rcases slot with ⟨key, r, hr, hty, hfacet, e, he, v, hvf, hterm, htau, packet, hpacket⟩
  have hread : leafRecord (leafTypeOf U P t ht) r.facet.val = some r := by
    rw [hfacet]
    exact hr
  obtain ⟨f, hf, rfl⟩ := honest_rows_step1_cont_geometry_step1_record U P t ht r hread
  let slot : ContSlot (leafTypeOf U P t ht) :=
    ⟨key, U.recordOf P t f hf, hr, hty, hfacet, e, he, v, hvf, hterm, htau,
      packet, hpacket⟩
  change ∃ T : ContTemplate slot, IsActualTemplate U P t ht T.configuration ∧
    T.centralChain ∈ (U.recordOf P t f hf).chains ∧ T.otherChain ∈ T.record.chains
  obtain ⟨c, hc, hce⟩ := he
  change (c.chain.val.cell edgeIndex).val = e.val at hce
  have hca : U.ActiveChain P t f hf c := (Finset.mem_filter.mp hc).2
  let B := U.hierarchy.servingChild t f hf
  obtain ⟨F, aTrace, hF, _, _⟩ := chain_active_owner U P t f hf c hc
  have hBt : U.hierarchy.ancestor t B.1 = B := by
    have hh : B.1 = (U.hierarchy.firstProvider t f hf).1 := by
      dsimp only [B, CoherentHierarchy.servingChild]
      rw [U.hierarchy.ancestor_height, ht, zero_add]
    rw [hh]
    rfl
  have hsub (j : FlagIndex d) :
      t.2.val.cell t.1 (c.chain.val.cell j).val ⊆ B.2.val.cell B.1 (F.cell j).val := by
    obtain ⟨hs, hstr, _⟩ := hca.1 j
    have h := closure_mono (U.hierarchy.stratumMap_spec t f hf (c.chain.val.cell j) hs).1
    simp only [restrictionOp_source_step5_cell_closure] at h
    rw [hstr, ← hF j] at h
    exact h
  have hvtau : (U.recordTau P t f hf ⟨vertexCell v, hvf⟩).val.val =
      ((P.flag (U.recordIncidence P t f hf)).flag.cell edgeIndex).val := by
    have hvlist : v.val ∈ (S.cx t.2.val.ty).cells := (Finset.mem_filter.mp v.property).1
    unfold FacetRecord.tauAt at htau
    split at htau
    next h => exact Option.some.inj htau
    next h => exact (h hvlist).elim
  have hvrel : t.2.val.prototypeFrame t.1 (vertexPoint v) ∈
      relint (B.2.val.cell B.1 (F.cell edgeIndex).val) := by
    have hτ := record_tau_spec U P t f hf ⟨vertexCell v, hvf⟩
    change U.providerPlacement P t f hf ''
      (U.recordTau P t f hf ⟨vertexCell v, hvf⟩).val.val.carrier = _ at hτ
    rw [hvtau, ← hF edgeIndex] at hτ
    rw [hτ]
    apply (U.hierarchy.stratumMap_spec t f hf (vertexCell v)
      (U.cellInFacet_placed t f ⟨vertexCell v, hvf⟩)).1
    change t.2.val.prototypeFrame t.1 (vertexPoint v) ∈
      relint (t.2.val.prototypeFrame t.1 '' v.val.carrier)
    rw [vertexPoint_spec, Set.image_singleton]
    simp [relint]
  obtain ⟨heseg, hene, hevec⟩ :=
    honest_rows_step1_cont_geometry_step5_endpoints U P t f hf c hc e hce
  let a := t.2.val.prototypeFrame t.1 ((U.recordOf P t f hf).endpoints e).1
  let x := t.2.val.prototypeFrame t.1 (vertexPoint v)
  have het : t.2.val.cell t.1 (c.chain.val.cell edgeIndex).val = segment ℝ a x := by
    change t.2.val.prototypeFrame t.1 '' (c.chain.val.cell edgeIndex).val.carrier = _
    rw [hce, heseg]
    simpa only [a, x, hterm] using
      image_segment ℝ (t.2.val.prototypeFrame t.1).toAffineMap
        ((U.recordOf P t f hf).endpoints e).1 ((U.recordOf P t f hf).endpoints e).2
  have hax : a ≠ x := by
    apply (t.2.val.prototypeFrame t.1).injective.ne
    simpa only [hterm] using hene
  obtain ⟨q, hq, G, v', z, b, hBq, hsubq, hv', heq, hb, hzx⟩ :=
    honest_rows_step1_cont_geometry_step2_successor U B t ht hBt F c.chain.val
      hsub v a het hax hvrel
  let g : FacetName S q.2.val.ty := ⟨(G.cell facetIndex).val,
    Finset.mem_filter.mpr ⟨(G.cell facetIndex).property, G.dimension facetIndex⟩⟩
  have hgsub : q.2.val.cell q.1 g.val ⊆ U.hierarchy.providerCarrier t f hf := by
    have h := hsubq facetIndex
    rw [hF facetIndex, (P.flag (U.recordIncidence P t f hf)).top,
      record_provider_carrier] at h
    exact h
  obtain ⟨hg, hbirth, hcarrier, hserv⟩ :=
    honest_rows_step1_cont_geometry_step3_provider U t q hq f hf g hBq hgsub
  have hi := restrictionOp_source_step4_provider_name P U q t g f hg hf hbirth hcarrier
  have hplace : U.providerPlacement P q g hg = U.providerPlacement P t f hf :=
    congrArg₂ (fun (D : U.Node) (i : P.Incidence) =>
      P.incidencePlacement D.2.val D.1 i) hbirth hi
  have hdir : U.counterDirection P q g hg = U.counterDirection P t f hf := by
    unfold HonestSource.counterDirection
    rw [hplace, hi]
  have hFq (j : FlagIndex d) : B.2.val.cell B.1 (F.cell j).val =
      U.providerPlacement P q g hg ''
        ((P.flag (U.recordIncidence P q g hg)).flag.cell j).val.carrier := by
    rw [hplace, hi]
    exact hF j
  obtain ⟨c', hc'G, hc'⟩ := honest_rows_step1_cont_geometry_step3_activity
    U P q g hg B hserv F hFq G rfl hsubq
  let e' : PrototypeEdge S q.2.val.ty := ⟨(G.cell edgeIndex).val,
    Finset.mem_filter.mpr ⟨(G.cell edgeIndex).property, G.dimension edgeIndex⟩⟩
  have hc'e : (c'.chain.val.cell edgeIndex).val = e'.val := by rw [hc'G]
  obtain ⟨he'seg, he'ne, he'vec⟩ :=
    honest_rows_step1_cont_geometry_step5_endpoints U P q g hg c' hc' e' hc'e
  let p := q.2.val.prototypeFrame q.1 ((U.recordOf P q g hg).endpoints e').1
  let w := q.2.val.prototypeFrame q.1 ((U.recordOf P q g hg).endpoints e').2
  have hpw : p ≠ w := (q.2.val.prototypeFrame q.1).injective.ne he'ne
  have hsegq : segment ℝ p w = segment ℝ x z := by
    have hh : q.2.val.cell q.1 e'.val = segment ℝ p w := by
      change q.2.val.prototypeFrame q.1 '' e'.val.carrier = _
      rw [he'seg]
      exact image_segment ℝ (q.2.val.prototypeFrame q.1).toAffineMap _ _
    exact hh.symm.trans heq
  obtain ⟨_, α, hα, hcdir⟩ :=
    (restrictionOp_source_step4_chains_step1_test U P t f hf c).mp hca
  have hc'a : U.ActiveChain P q g hg c' := (Finset.mem_filter.mp hc').2
  obtain ⟨_, β, hβ, hc'dir⟩ :=
    (restrictionOp_source_step4_chains_step1_test U P q g hg c').mp hc'a
  change U.counterDirection P t f hf =
    α • (t.2.val.prototypeFrame t.1).linear (chainVector c) at hcdir
  change U.counterDirection P q g hg =
    β • (q.2.val.prototypeFrame q.1).linear (chainVector c') at hc'dir
  have hlinear (T : E d ≃ᵃ[ℝ] E d) (u v : E d) :
      T.linear (u - v) = T u - T v := T.toAffineMap.linearMap_vsub u v
  have hcdiff : (t.2.val.prototypeFrame t.1).linear (chainVector c) = x - a := by
    rw [hevec, hlinear]
    dsimp only [x, a]
    rw [hterm]
  have hc'diff : (q.2.val.prototypeFrame q.1).linear (chainVector c') = w - p := by
    rw [he'vec, hlinear]
  have hcommon : β • (w - p) = α • (x - a) := by
    rw [← hc'diff, ← hc'dir, hdir, hcdir, hcdiff]
  have hpositive : 0 < inner ℝ (w - p) (x - a) := by
    have hinner := congrArg (fun u => inner ℝ (w - p) u) hcommon
    simp only [inner_smul_right] at hinner
    have hnorm := real_inner_self_pos.mpr (sub_ne_zero.mpr hpw.symm)
    nlinarith
  have hpositive' : 0 < inner ℝ (w - p) (z - x) := by
    rw [hzx, inner_smul_right]
    exact mul_pos hb hpositive
  obtain ⟨hpx, hwz⟩ :=
    honest_rows_step1_cont_geometry_step5_ordered_endpoints p w x z hsegq hpositive'
  have hvinit : vertexPoint v' = ((U.recordOf P q g hg).endpoints e').1 :=
    (q.2.val.prototypeFrame q.1).injective (hv'.trans hpx.symm)
  have htf : t.2.val.prototypeFrame t.1 = t.2.val.frame.toAffineEquiv := by
    ext u
    simp [FramedNode.prototypeFrame, ht]
  have hqf : q.2.val.prototypeFrame q.1 = q.2.val.frame.toAffineEquiv := by
    ext u
    simp [FramedNode.prototypeFrame, hq]
  have hsubq' (j : FlagIndex d) : q.2.val.cell q.1 (c'.chain.val.cell j).val ⊆
      B.2.val.cell B.1 (F.cell j).val := by rw [hc'G]; exact hsubq j
  obtain ⟨hst, hct⟩ := honest_rows_step1_cont_geometry_step4_sides U B t
    (by simpa only [ht, Nat.sub_zero] using hBt) F c.chain.val hsub
  obtain ⟨hsq, hcq⟩ := honest_rows_step1_cont_geometry_step4_sides U B q
    (by simpa only [hq, Nat.sub_zero] using hBq) F c'.chain.val hsubq'
  have halign : ChainsAligned (U.recordOf P t f hf) (U.recordOf P q g hg)
      c c' (q.2.val.move t.2.val.frame.symm).frame := by
    apply honest_rows_step1_cont_geometry_step4_alignment
      (U.recordOf P t f hf) (U.recordOf P q g hg) c c'
      t.2.val.frame q.2.val.frame
    · intro j
      have hst' := (hca.1 j).choose_spec.2
      have hsq' := (hc'a.1 j).choose_spec.2
      rw [hplace, hi] at hsq'
      simpa only [FramedNode.cell, htf, hqf] using hst'.trans hsq'.symm
    · intro j
      simpa only [htf, hqf] using (hst j).trans (hsq j).symm
    · have hpos : 0 < inner ℝ
          ((t.2.val.prototypeFrame t.1).linear (chainVector c))
          ((q.2.val.prototypeFrame q.1).linear (chainVector c')) := by
        rw [hcdiff, hc'diff, real_inner_comm]
        exact hpositive
      simpa only [htf, hqf] using hpos
    · simpa only [htf, hqf, c.chain.property, c'.chain.property] using hct.trans hcq.symm
  let other := q.2.val.move t.2.val.frame.symm
  have hrelative (u : E d) : t.2.val.prototypeFrame t.1 (other.frame u) =
      q.2.val.prototypeFrame q.1 u := by
    rw [htf, hqf]
    simp [other, FramedNode.move]
  have hver : other.frame (vertexPoint v') = vertexPoint v := by
    apply (t.2.val.prototypeFrame t.1).injective
    rw [hrelative]
    exact hv'
  have hjoin := honest_rows_step1_cont_geometry_step5_join a x z b hb hzx
  have hsegment : e.val.carrier ∪ placedSet other.frame e'.val.carrier =
      segment ℝ ((U.recordOf P t f hf).endpoints e).1
        (other.frame ((U.recordOf P q g hg).endpoints e').2) := by
    apply (t.2.val.prototypeFrame t.1).injective.image_injective
    rw [Set.image_union]
    have hleft : t.2.val.prototypeFrame t.1 '' e.val.carrier = segment ℝ a x := by
      simpa only [FramedNode.cell, hce] using het
    have hright : t.2.val.prototypeFrame t.1 '' placedSet other.frame e'.val.carrier =
        segment ℝ x z := by
      change t.2.val.prototypeFrame t.1 '' (other.frame '' e'.val.carrier) = _
      rw [Set.image_image]
      simpa only [hrelative, FramedNode.cell] using heq
    rw [hleft, hright]
    change _ = (t.2.val.prototypeFrame t.1).toAffineMap '' segment ℝ _ _
    rw [image_segment]
    change _ = segment ℝ a (t.2.val.prototypeFrame t.1
      (other.frame ((U.recordOf P q g hg).endpoints e').2))
    rw [hrelative]
    change _ = segment ℝ a w
    rw [hwz]
    exact hjoin.1
  have hjunction : vertexPoint v ∈ openSegment ℝ ((U.recordOf P t f hf).endpoints e).1
      (other.frame ((U.recordOf P q g hg).endpoints e').2) := by
    apply (t.2.val.prototypeFrame t.1).injective.mem_set_image.mp
    change x ∈ (t.2.val.prototypeFrame t.1).toAffineMap '' openSegment ℝ _ _
    rw [image_openSegment]
    change x ∈ openSegment ℝ a (t.2.val.prototypeFrame t.1
      (other.frame ((U.recordOf P q g hg).endpoints e').2))
    rw [hrelative]
    change x ∈ openSegment ℝ a w
    rw [hwz]
    exact hjoin.2
  obtain ⟨θ, hθ, hcentral, htiles, hannotation⟩ :=
    honest_rows_step1_cont_geometry_step6_configuration U P t q ht hq
  refine ⟨{
    configuration := θ
    central_eq := hcentral
    other := other
    label := leafTypeOf U P q hq
    other_mem := by rw [htiles]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    tiles_eq := htiles
    annotation_none := hannotation
    record := U.recordOf P q g hg
    record_eq := honest_rows_step1_cont_geometry_step1_read U P q hq g hg
    type_eq := rfl
    centralChain := c
    central_edge := hce
    otherChain := c'
    edge := e'
    other_edge := hc'e
    vertex := v'
    initial := hvinit
    vertex_eq := hver
    aligned := halign
    segment_eq := hsegment
    junction_interior := hjunction }, hθ, hc, hc'⟩

/-- Step 1 of the V4 proof of `honest_rows_step2_cont_labels` (V4 2.8):
"whose record". Read a finite facet record from the actual native pre-pattern. -/
private theorem honest_rows_step2_cont_labels_step1_read_record
    (U : HonestSource S) (P : Params S) (q : U.Node) (hq : q.1 = 0)
    (e : Cell d) (r : FacetRecord P)
    (hr : leafRecord (leafTypeOf U P q hq) e = some r) :
    ∃ (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f),
      f.val = e ∧ r = U.recordOf P q f hf := by
  unfold leafRecord at hr
  rw [← prePattern_of_leafType U P q hq] at hr
  change stateRecordAt (stateOf U P q) e = some r at hr
  unfold stateRecordAt at hr
  split at hr
  next he =>
    change e ∈ (S.cx q.2.val.ty).facets at he
    change U.facetRecordOf P q ⟨e, he⟩ = some r at hr
    unfold HonestSource.facetRecordOf at hr
    split at hr
    · contradiction
    next hf => exact ⟨⟨e, he⟩, hf, rfl, (Option.some.inj hr).symm⟩
  · contradiction

/-- Step 2 of the V4 proof of `honest_rows_step2_cont_labels` (V4 2.1):
"active with induced orientations". Nested cells with equal affine spans inherit
the successive local sides; containment of their owners also fixes the inward side. -/
private theorem honest_rows_step2_cont_labels_step2_nested_sides
    (A B : S.ι) (a : FacetFlag S A) (b : FacetFlag S B)
    (φ ψ : E d ≃ᵃ[ℝ] E d)
    (hcell : ∀ j, φ '' (a.cell j).val.carrier ⊆ ψ '' (b.cell j).val.carrier)
    (hspan : ∀ j, affineSpan ℝ (φ '' (a.cell j).val.carrier) =
      affineSpan ℝ (ψ '' (b.cell j).val.carrier))
    (howner : φ '' (S.proto A).carrier ⊆ ψ '' (S.proto B).carrier) :
    (∀ j, φ.linear '' flagSide a j = ψ.linear '' flagSide b j) ∧
      φ.linear '' tangentCone (S.proto A).carrier (cellAnchor (a.cell facetIndex).val) =
        ψ.linear '' tangentCone (S.proto B).carrier (cellAnchor (b.cell facetIndex).val) := by
  classical
  have hrel (j : FlagIndex d) :
      relint (φ '' (a.cell j).val.carrier) ⊆ relint (ψ '' (b.cell j).val.carrier) := by
    unfold relint intrinsicInterior
    rw [hspan j]
    exact Set.image_mono (interior_mono (Set.preimage_mono (hcell j)))
  constructor
  · intro j
    exact actualCont_exists_step5_coface_side a b φ ψ j
      (hrel _) (hrel _) (hspan _) (hspan _)
  · let f : FacetName S A := ⟨(a.cell facetIndex).val,
      Finset.mem_filter.mpr ⟨(a.cell facetIndex).property, a.dimension facetIndex⟩⟩
    let g : FacetName S B := ⟨(b.cell facetIndex).val,
      Finset.mem_filter.mpr ⟨(b.cell facetIndex).property, b.dimension facetIndex⟩⟩
    exact actualCont_exists_step5_inward f g φ ψ howner (hrel facetIndex)

/-- Step 1 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"A is a polyhedron". A simplex, including a lower-dimensional one, is cut out by
finitely many affine inequalities, using coordinates of an extended affine basis. -/
private lemma honest_rows_step3_flag_overlap_aux_step1_simplex
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

/-- Step 1 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"A is a polyhedron". Carathéodory's theorem gives a finite union of simplices,
and hence a finite union of intersections of affine closed half-spaces. -/
private lemma honest_rows_step3_flag_overlap_aux_step1_halfspaces
    {K : Set (E d)} (hK : Polyhedron K) :
    ∃ S : Finset (Finset (E d →ᵃ[ℝ] ℝ)),
      K = ⋃ q ∈ S, {x | ∀ f ∈ q, 0 ≤ f x} := by
  classical
  obtain ⟨s, rfl⟩ := hK
  have hrep (t : Finset (E d)) : ∃ q : Finset (E d →ᵃ[ℝ] ℝ),
      AffineIndependent ℝ ((↑) : t → E d) →
        convexHull ℝ (t : Set (E d)) = {x | ∀ f ∈ q, 0 ≤ f x} := by
    by_cases ht : AffineIndependent ℝ ((↑) : t → E d)
    · obtain ⟨q, hq⟩ := honest_rows_step3_flag_overlap_aux_step1_simplex t ht
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
/-- Step 1 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"its tangent cone at any point is a polyhedral cone". Near the base point,
inactive inequalities keep their sign and active inequalities become homogeneous. -/
private lemma honest_rows_step3_flag_overlap_aux_step1_local_cone
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

/-- Step 1 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"polyhedral cone". Homogeneous half-space inequalities are invariant under
multiplication by a positive scalar, as is a finite union of their intersections. -/
private lemma honest_rows_step3_flag_overlap_aux_step1_scaling
    {C : Set (E d)} (hC : IsPolyhedralCone C) {r : ℝ} (hr : 0 < r) (v : E d) :
    r • v ∈ C ↔ v ∈ C := by
  obtain ⟨S, rfl⟩ := hC
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, map_smul, smul_eq_mul,
    mul_nonneg_iff_of_pos_left hr]

open scoped Topology in
/-- Step 1 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"its tangent cone at any point is a polyhedral cone". A local conical model
equals the positive-time radial germ in the definition of `tangentCone`. -/
private lemma honest_rows_step3_flag_overlap_aux_step1_radial
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
    exact (honest_rows_step3_flag_overlap_aux_step1_scaling hC ht v).mp
      ((hδloc hnear).mp (hv t ht htε))
  · intro hv
    refine ⟨δ, hδ, fun t ht htδ => ?_⟩
    have hnear : dist t 0 < δ := by simpa [Real.dist_eq, abs_of_pos ht] using htδ
    exact (hδloc hnear).mpr
      ((honest_rows_step3_flag_overlap_aux_step1_scaling hC ht v).mpr hv)

/-- Step 2 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(a)):
"each component is inside or outside A". On a connected set on which boundary
membership is constant, membership in a closed set is constant as well. -/
private lemma honest_rows_step3_flag_overlap_aux_step2_membership
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

/-- Step 2 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"the local structure is constant by (a) applied to the cell complex". Translation
invariance of the relative boundary of a closed set extends to the set itself,
provided the translations are parallel to its affine span. -/
private lemma honest_rows_step3_flag_overlap_aux_step2_fill
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
    have heq := honest_rows_step3_flag_overlap_aux_step2_membership
      (hS.preimage continuous_subtype_val)
      (isPreconnected_Icc.image γ hγcont.continuousOn) hinv
      (mem_image_of_mem γ (left_mem_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)))
      (mem_image_of_mem γ (right_mem_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)))
    simpa [γ] using heq.mp (by simpa [γ] using hxs)
  intro x hx y hy hyx
  exact ⟨hforward x hx y hy hyx,
    hforward y hy x hx (by simpa only [neg_sub] using V.neg_mem hyx)⟩

/-- Step 2 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(a)):
"if p ∈ e ... then mc_A(p) ⊆ e". A listed cell meeting the relative interior
of another listed cell contains the whole latter cell. -/
private lemma honest_rows_step3_flag_overlap_aux_step2_incidence
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

/-- Step 2 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(a)):
"Cells are closed and finitely many, so some ball U ...". Finitely many local
translation invariances hold on a common ball, including for an empty family. -/
private lemma honest_rows_step3_flag_overlap_aux_step2_common_ball
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

/-- Step 2 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"the local structure is constant by (a) applied to the cell complex". Induction
through relative boundaries makes every listed carrier locally invariant in the
directions of the cell containing the base point in its relative interior. -/
private lemma honest_rows_step3_flag_overlap_aux_step2_invariance
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
      · have hef := honest_rows_step3_flag_overlap_aux_step2_incidence K he hf hp hpf
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
        obtain ⟨r, hr, hc⟩ := honest_rows_step3_flag_overlap_aux_step2_common_ball b
          Cell.carrier (cellDirection e.carrier) p (fun g hg =>
            ih (N g) (by simpa only [hN] using hsmall g hg) g (hb hg) rfl)
        refine ⟨r, hr, honest_rows_step3_flag_overlap_aux_step2_fill f.flat.compact.isClosed
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

open scoped Topology in
/-- Step 2 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"the local structure is constant". Equal translated germs give equal radial
tangent cones; only sufficiently short positive portions of each ray matter. -/
private lemma honest_rows_step3_flag_overlap_aux_step2_tangent_germ
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

open scoped Topology in
/-- Step 1 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"A is a polyhedron". Its radial tangent cone determines its entire local germ. -/
private theorem honest_rows_step3_flag_overlap_aux_step1_germ
    {K : Set (E d)} (hK : Polyhedron K) (p : E d) :
    ∀ᶠ x in 𝓝 p, x ∈ K ↔ x - p ∈ tangentCone K p := by
  obtain ⟨s, hs⟩ := honest_rows_step3_flag_overlap_aux_step1_halfspaces hK
  obtain ⟨C, hC, hlocal⟩ := honest_rows_step3_flag_overlap_aux_step1_local_cone s p
  rw [← hs] at hlocal
  rwa [honest_rows_step3_flag_overlap_aux_step1_radial p hC hlocal]

/-- Step 1 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"the local structure" is transported by the full affine placement. -/
private theorem honest_rows_step3_flag_overlap_aux_step1_placed_germ
    {K : Set (E d)} (hK : Polyhedron K) (φ : E d ≃ᵃ[ℝ] E d) (p : E d) :
    ∃ V : Set (E d), IsOpen V ∧ φ p ∈ V ∧ ∀ x ∈ V,
      x ∈ φ '' K ↔ x - φ p ∈ φ.linear '' tangentCone K p := by
  obtain ⟨r, hr, hlocal⟩ := Metric.eventually_nhds_iff.mp
    (honest_rows_step3_flag_overlap_aux_step1_germ hK p)
  refine ⟨φ '' ball p r, φ.toHomeomorphOfFiniteDimensional.isOpenMap _ isOpen_ball,
    ⟨p, mem_ball_self hr, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hdiff : φ.linear (x - p) = φ x - φ p := φ.toAffineMap.linearMap_vsub x p
  rw [φ.injective.mem_set_image, ← hdiff,
    φ.linear.injective.mem_set_image]
  exact hlocal hx

/-- Step 1 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"closure of its relative interior" is preserved by an affine placement. -/
private theorem honest_rows_step3_flag_overlap_aux_step1_cell_closure
    (e : Cell d) (φ : E d ≃ᵃ[ℝ] E d) :
    closure (relint (φ '' e.carrier)) = φ '' e.carrier := by
  rw [restrictionOp_source_step5_relint_image]
  change closure (φ.toHomeomorphOfFiniteDimensional '' relint e.carrier) = _
  rw [← Homeomorph.image_closure, e.flat.regularClosed]
  rfl

/-- Step 2 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"the local structure is constant" on the connected relative interior of a listed cell. -/
private theorem honest_rows_step3_flag_overlap_aux_step2_cell_cone
    {A : PolyManifoldDomain d} (K : CellComplex A) (e f : Cell d)
    (he : e ∈ K.cells) (hf : f ∈ K.cells) (p q : E d)
    (hp : p ∈ relint e.carrier) (hq : q ∈ relint e.carrier) :
    tangentCone f.carrier p = tangentCone f.carrier q := by
  let cone : relint e.carrier → Set (E d) := fun x => tangentCone f.carrier x.val
  have hloc : IsLocallyConstant cone := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    obtain ⟨r, hr, hball⟩ :=
      honest_rows_step3_flag_overlap_aux_step2_invariance K e he x x.property f hf
    have hnear : ∀ᶠ y : relint e.carrier in nhds x, (y : E d) ∈ ball (x : E d) r :=
      continuous_subtype_val.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hnear] with y hy
    apply (honest_rows_step3_flag_overlap_aux_step2_tangent_germ f.carrier
      (cellDirection e.carrier) x y r hr hy ?_ hball).symm
    exact AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ e.carrier (intrinsicInterior_subset y.property))
      (subset_affineSpan ℝ e.carrier (intrinsicInterior_subset x.property))
  letI : PreconnectedSpace (relint e.carrier) :=
    isPreconnected_iff_preconnectedSpace.mp e.flat.relint_connected.isPreconnected
  exact hloc.apply_eq_of_preconnectedSpace ⟨p, hp⟩ ⟨q, hq⟩

/-- Step 3 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 2.8):
"v in relint h" supplies a neighbourhood inside the supporting affine span. -/
private theorem honest_rows_step3_flag_overlap_aux_step3_relint_ball
    {K : Set (E d)} {p : E d} (hp : p ∈ relint K) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball p r,
      x ∈ affineSpan ℝ K → x ∈ relint K := by
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp isOpen_interior q hq
  refine ⟨r, hr, ?_⟩
  intro x hx hxaff
  exact ⟨⟨x, hxaff⟩, hb hx, rfl⟩

/-- Step 3 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 2.8):
"adjacent to h on the far side of v". A closed edge through an interior
point of another edge has overlapping relative interiors in their common line. -/
private theorem honest_rows_step3_flag_overlap_aux_step3_relint_overlap
    {K L : Set (E d)} (hspan : affineSpan ℝ K = affineSpan ℝ L)
    (hreg : closure (relint K) = K) {p : E d} (hpK : p ∈ K) (hpL : p ∈ relint L) :
    (relint K ∩ relint L).Nonempty := by
  obtain ⟨r, hr, hball⟩ := honest_rows_step3_flag_overlap_aux_step3_relint_ball hpL
  have hp : p ∈ closure (relint K) := hreg.symm ▸ hpK
  obtain ⟨x, hx, hxp⟩ := Metric.mem_closure_iff.mp hp r hr
  refine ⟨x, hx, hball x (by simpa only [mem_ball, dist_comm] using hxp) ?_⟩
  rw [← hspan]
  exact mem_affineSpan ℝ (intrinsicInterior_subset hx)

/-- Step 3 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"the local structure" determines relative interior in a fixed affine span. -/
private theorem honest_rows_step3_flag_overlap_aux_step3_relint_transfer
    {K L V : Set (E d)} (hspan : affineSpan ℝ K = affineSpan ℝ L)
    (hV : IsOpen V) (heq : K ∩ V = L ∩ V) {p : E d}
    (hp : p ∈ relint K) (hpV : p ∈ V) : p ∈ relint L := by
  obtain ⟨q, hq, rfl⟩ := hp
  have hpre : ((↑) ⁻¹' K : Set (affineSpan ℝ K)) ∩ (↑) ⁻¹' V =
      ((↑) ⁻¹' L : Set (affineSpan ℝ K)) ∩ (↑) ⁻¹' V :=
    congrArg (fun X : Set (E d) => (fun x : affineSpan ℝ K => x.val) ⁻¹' X) heq
  have hi := congrArg interior hpre
  rw [interior_inter, interior_inter,
    (hV.preimage continuous_subtype_val).interior_eq] at hi
  have hh : q ∈ interior ((↑) ⁻¹' L : Set (affineSpan ℝ K)) ∩ (↑) ⁻¹' V :=
    hi ▸ ⟨hq, hpV⟩
  rw [relint, intrinsicInterior, ← hspan]
  exact ⟨q, hh.1, rfl⟩

/-- Step 3 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 1.0(b)):
"the local structure is constant". Equal local germs of regular closed
cells in one affine span give an overlap of relative interiors. -/
private theorem honest_rows_step3_flag_overlap_aux_step3_local_overlap
    {K L V : Set (E d)} (hspan : affineSpan ℝ K = affineSpan ℝ L)
    (hreg : closure (relint K) = K) (hV : IsOpen V) (heq : K ∩ V = L ∩ V)
    {p : E d} (hpK : p ∈ K) (hpV : p ∈ V) :
    (relint K ∩ relint L).Nonempty := by
  have hp : (closure (relint K) ∩ V).Nonempty := ⟨p, hreg.symm ▸ hpK, hpV⟩
  obtain ⟨x, hx, hxV⟩ := (closure_inter_open_nonempty_iff hV).mp hp
  exact ⟨x, hx, honest_rows_step3_flag_overlap_aux_step3_relint_transfer hspan hV heq hx hxV⟩

/-- Step 3 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 2.8):
"both chains lie in the positioned flag ... with its orientations".
At one consecutive pair of dimensions, equal coface sides extend a relative-interior
intersection of the lower cells to one of the upper cells. -/
private theorem honest_rows_step3_flag_overlap_aux_step3_coface_overlap
    {A B : S.ι} (F : FacetFlag S A) (G : FacetFlag S B)
    (φ ψ : E d ≃ᵃ[ℝ] E d) (k : FlagStep d)
    (hlow : (relint (φ '' (F.cell ⟨k.val, k.property.1, by omega⟩).val.carrier) ∩
      relint (ψ '' (G.cell ⟨k.val, k.property.1, by omega⟩).val.carrier)).Nonempty)
    (hspan : affineSpan ℝ
        (φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier) =
      affineSpan ℝ (ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier))
    (hside : φ.linear '' flagSide F k = ψ.linear '' flagSide G k) :
    (relint (φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier) ∩
      relint (ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier)).Nonempty := by
  let i : FlagIndex d := ⟨k.val, k.property.1, by have := k.property.2; omega⟩
  let j : FlagIndex d := ⟨k.val + 1, by omega, k.property.2⟩
  obtain ⟨p, hp, hq⟩ := hlow
  rw [restrictionOp_source_step5_relint_image] at hp hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, hba⟩ := hq
  have hF := honest_rows_step3_flag_overlap_aux_step2_cell_cone (S.cx A)
    (F.cell i).val (F.cell j).val (F.cell i).property (F.cell j).property
    a (cellAnchor (F.cell i).val) ha (cellAnchor_mem _)
  have hG := honest_rows_step3_flag_overlap_aux_step2_cell_cone (S.cx B)
    (G.cell i).val (G.cell j).val (G.cell i).property (G.cell j).property
    b (cellAnchor (G.cell i).val) hb (cellAnchor_mem _)
  obtain ⟨V, hV, hpV, hVeq⟩ := honest_rows_step3_flag_overlap_aux_step1_placed_germ
    (F.cell j).val.flat.polyhedral φ a
  obtain ⟨W, hW, hpW, hWeq⟩ := honest_rows_step3_flag_overlap_aux_step1_placed_germ
    (G.cell j).val.flat.polyhedral ψ b
  rw [hF] at hVeq
  rw [hG] at hWeq
  change φ.linear '' tangentCone (F.cell j).val.carrier (cellAnchor (F.cell i).val) =
    ψ.linear '' tangentCone (G.cell j).val.carrier (cellAnchor (G.cell i).val) at hside
  have heq : (φ '' (F.cell j).val.carrier) ∩ (V ∩ W) =
      (ψ '' (G.cell j).val.carrier) ∩ (V ∩ W) := by
    ext x
    constructor
    · rintro ⟨hx, hxV, hxW⟩
      refine ⟨(hWeq x hxW).mpr ?_, hxV, hxW⟩
      rw [hba, ← hside]
      exact (hVeq x hxV).mp hx
    · rintro ⟨hx, hxV, hxW⟩
      refine ⟨(hVeq x hxV).mpr ?_, hxV, hxW⟩
      rw [hside, ← hba]
      exact (hWeq x hxW).mp hx
  exact honest_rows_step3_flag_overlap_aux_step3_local_overlap hspan
    (honest_rows_step3_flag_overlap_aux_step1_cell_closure _ φ) (hV.inter hW) heq
    ⟨a, F.nested i j (by dsimp [i, j]; omega) (intrinsicInterior_subset ha), rfl⟩
    ⟨hpV, hba ▸ hpW⟩

/-- Step 3 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 2.8):
"both chains lie in the positioned flag ... with its orientations".
Induction through the consecutive cofaces carries the edge intersection to the facets. -/
private theorem honest_rows_step3_flag_overlap_aux_step3_flag_overlap
    {A B : S.ι} (F : FacetFlag S A) (G : FacetFlag S B)
    (φ ψ : E d ≃ᵃ[ℝ] E d)
    (hspan : ∀ j, affineSpan ℝ (φ '' (F.cell j).val.carrier) =
      affineSpan ℝ (ψ '' (G.cell j).val.carrier))
    (hside : ∀ k, φ.linear '' flagSide F k = ψ.linear '' flagSide G k)
    (p : E d) (hpF : p ∈ φ '' (F.cell edgeIndex).val.carrier)
    (hpG : p ∈ relint (ψ '' (G.cell edgeIndex).val.carrier)) :
    (relint (φ '' (F.cell facetIndex).val.carrier) ∩
      relint (ψ '' (G.cell facetIndex).val.carrier)).Nonempty := by
  have hbase := honest_rows_step3_flag_overlap_aux_step3_relint_overlap (hspan edgeIndex)
    (honest_rows_step3_flag_overlap_aux_step1_cell_closure _ φ) hpF hpG
  have hall : ∀ (n : ℕ) (hn : 1 ≤ n) (hnd : n < d),
      (relint (φ '' (F.cell ⟨n, hn, hnd⟩).val.carrier) ∩
        relint (ψ '' (G.cell ⟨n, hn, hnd⟩).val.carrier)).Nonempty := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro hnd; exact hbase
    | succ n hn ih =>
      intro hnd
      exact honest_rows_step3_flag_overlap_aux_step3_coface_overlap F G φ ψ ⟨n, hn, hnd⟩
        (ih (by omega)) (hspan _) (hside _)
  exact hall (d - 1) facetIndex.property.1 facetIndex.property.2

/-- Step 4 of the V4 proof of `honest_rows_step2_cont_labels_step3_flag_overlap` (V4 2.8):
"same ... side". Overlapping facet interiors and equal inward cones force
an overlap of the interiors of the two placed domains. -/
private theorem honest_rows_step3_flag_overlap_aux_step4_inward_overlap
    {A B : S.ι} (f : FacetName S A) (g : FacetName S B)
    (φ ψ : E d ≃ᵃ[ℝ] E d)
    (hmeet : (relint (φ '' f.val.carrier) ∩ relint (ψ '' g.val.carrier)).Nonempty)
    (hside : φ.linear '' tangentCone (S.proto A).carrier (cellAnchor f.val) =
      ψ.linear '' tangentCone (S.proto B).carrier (cellAnchor g.val)) :
    (interior (φ '' (S.proto A).carrier) ∩
      interior (ψ '' (S.proto B).carrier)).Nonempty := by
  obtain ⟨p, hp, hq⟩ := hmeet
  rw [restrictionOp_source_step5_relint_image] at hp hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, hba⟩ := hq
  have hF := actualCont_exists_step5_facet_cone A f a (cellAnchor f.val)
    ha (cellAnchor_mem _)
  have hG := actualCont_exists_step5_facet_cone B g b (cellAnchor g.val)
    hb (cellAnchor_mem _)
  obtain ⟨V, hV, hpV, hVeq⟩ := honest_rows_step3_flag_overlap_aux_step1_placed_germ
    (S.proto A).polyhedral φ a
  obtain ⟨W, hW, hpW, hWeq⟩ := honest_rows_step3_flag_overlap_aux_step1_placed_germ
    (S.proto B).polyhedral ψ b
  rw [hF] at hVeq
  rw [hG] at hWeq
  have hsub : interior (φ '' (S.proto A).carrier) ∩ (V ∩ W) ⊆
      ψ '' (S.proto B).carrier := by
    rintro x ⟨hx, hxV, hxW⟩
    apply (hWeq x hxW).mpr
    rw [hba, ← hside]
    exact (hVeq x hxV).mp (interior_subset hx)
  have hreg : closure (interior (φ '' (S.proto A).carrier)) =
      φ '' (S.proto A).carrier := by
    change closure (interior (φ.toHomeomorphOfFiniteDimensional ''
      (S.proto A).carrier)) = _
    rw [← Homeomorph.image_interior, ← Homeomorph.image_closure,
      (S.proto A).regularClosed]
    rfl
  have hpK : φ a ∈ closure (interior (φ '' (S.proto A).carrier)) := by
    rw [hreg]
    exact ⟨a, actualCont_exists_step5_cell_subset A f.val
      (Finset.mem_filter.mp f.property).1 (intrinsicInterior_subset ha), rfl⟩
  obtain ⟨x, hx, hxV⟩ := (closure_inter_open_nonempty_iff (hV.inter hW)).mp
    ⟨φ a, hpK, hpV, hba ▸ hpW⟩
  exact ⟨x, hx, ((isOpen_interior.inter (hV.inter hW)).subset_interior_iff.mpr hsub)
    ⟨hx, hxV⟩⟩


/-- Step 3 of the V4 proof of `honest_rows_step2_cont_labels` (V4 2.8):
"both chains lie in the positioned flag ... with its orientations". A common open
edge portion and matching successive sides give overlapping coface interiors,
then overlapping owner interiors when their inward sides also match. -/
private theorem honest_rows_step2_cont_labels_step3_flag_overlap
    (A B : S.ι) (a : FacetFlag S A) (b : FacetFlag S B)
    (φ ψ : E d ≃ᵃ[ℝ] E d)
    (hspan : ∀ j, affineSpan ℝ (φ '' (a.cell j).val.carrier) =
      affineSpan ℝ (ψ '' (b.cell j).val.carrier))
    (hside : ∀ j, φ.linear '' flagSide a j = ψ.linear '' flagSide b j)
    (hinward :
      φ.linear '' tangentCone (S.proto A).carrier (cellAnchor (a.cell facetIndex).val) =
        ψ.linear '' tangentCone (S.proto B).carrier (cellAnchor (b.cell facetIndex).val))
    (hedge : (relint (φ '' (a.cell edgeIndex).val.carrier) ∩
      relint (ψ '' (b.cell edgeIndex).val.carrier)).Nonempty) :
    (relint (φ '' (a.cell facetIndex).val.carrier) ∩
      relint (ψ '' (b.cell facetIndex).val.carrier)).Nonempty ∧
    (interior (φ '' (S.proto A).carrier) ∩ interior (ψ '' (S.proto B).carrier)).Nonempty := by
  -- Starting at a common relative-interior edge point, pass up one coface at a time.
  -- Equal side cones give a common relative-interior point in the next cofaces.
  -- At the top facet, the matching inward sides give a point in both owner interiors.
  obtain ⟨p, hpF, hpG⟩ := hedge
  have hfacet := honest_rows_step3_flag_overlap_aux_step3_flag_overlap a b φ ψ hspan hside p
    (intrinsicInterior_subset hpF) hpG
  refine ⟨hfacet, ?_⟩
  let f : FacetName S A := ⟨(a.cell facetIndex).val,
    Finset.mem_filter.mpr ⟨(a.cell facetIndex).property, a.dimension facetIndex⟩⟩
  let g : FacetName S B := ⟨(b.cell facetIndex).val,
    Finset.mem_filter.mpr ⟨(b.cell facetIndex).property, b.dimension facetIndex⟩⟩
  exact honest_rows_step3_flag_overlap_aux_step4_inward_overlap f g φ ψ hfacet hinward

/-- Step 4 of the V4 proof of `honest_rows_step2_cont_labels` (V4 2.8):
"v in relint h". A cell accumulating at an interior point of a cell in the same
affine span shares a relative-interior point with it. -/
private theorem honest_rows_step2_cont_labels_step4_relint_overlap
    (K L : Set (E d)) (x : E d) (hx : x ∈ closure (relint K))
    (hL : x ∈ relint L) (hspan : affineSpan ℝ K = affineSpan ℝ L) :
    (relint K ∩ relint L).Nonempty := by
  obtain ⟨p, hp, hpx⟩ := hL
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  obtain ⟨y, hy, hyx⟩ := Metric.mem_closure_iff.mp hx ε hε
  have hyspan : y ∈ affineSpan ℝ L := by
    rw [← hspan]
    exact subset_affineSpan ℝ K (intrinsicInterior_subset hy)
  refine ⟨y, hy, ⟨⟨y, hyspan⟩, hb ?_, rfl⟩⟩
  simpa only [mem_ball, Subtype.dist_eq, hpx, dist_comm] using hyx

/-- Step 5 of the V4 proof of `honest_rows_step2_cont_labels` (V4 1.22(a)):
"owner ... inside H". A native descendant's support lies in its ancestor. -/
private theorem honest_rows_step2_cont_labels_step5_native_subset
    (C N : FramedNode S) (n : ℕ) (h : C.IsDescendant 0 N n) :
    C.carrier 0 ⊆ N.carrier n := by
  obtain ⟨r, hr, w, rfl⟩ := h
  simp only [Nat.zero_add] at hr
  subst n
  have hsub : (S.nativeTile N.ty r w).carrier 0 ⊆ S.supertile r N.ty := by
    rw [← S.native_cover]
    exact Set.subset_iUnion (fun w : S.RoleWord N.ty r => (S.nativeTile N.ty r w).carrier 0) w
  simpa only [FramedNode.move, FramedNode.carrier, placedSet, Set.image_image,
    AffineIsometryEquiv.coe_trans, Function.comp_apply] using Set.image_mono (f := N.frame) hsub

/-- Step 6 of the V4 proof of `honest_rows_step2_cont_labels` (V4 1.22(a), 2.8):
"same serving child H". An interior point shared with a hierarchy node identifies
the native tile's ancestor at that height, by disjointness at one level. -/
private theorem honest_rows_step2_cont_labels_step6_ancestor
    (U : HonestSource S) (q H : U.Node) (hq : q.1 = 0)
    (hmeet : (interior (q.2.val.carrier q.1) ∩
      interior (H.2.val.carrier H.1)).Nonempty) :
    U.hierarchy.ancestor q H.1 = H := by
  let Q := U.hierarchy.ancestor q H.1
  have hheight : Q.1 = H.1 := by
    simp only [Q, U.hierarchy.ancestor_height, hq, Nat.zero_add]
  have hsub : q.2.val.carrier q.1 ⊆ Q.2.val.carrier Q.1 := by
    have hd : q.2.val.IsDescendant 0 Q.2.val Q.1 :=
      (congrArg (fun n => q.2.val.IsDescendant n Q.2.val Q.1) hq).mp
        (U.hierarchy.ancestor_descendant q H.1)
    exact (congrArg (fun n => q.2.val.carrier n) hq).subset.trans
      (honest_rows_step2_cont_labels_step5_native_subset q.2.val Q.2.val Q.1 hd)
  obtain ⟨x, hxq, hxH⟩ := hmeet
  have hval : Q.2.val = H.2.val := by
    apply U.hierarchy.same_height_disjoint H.1 Q.2.val H.2.val
      (hheight ▸ Q.2.property) H.2.property x _ hxH
    exact hheight ▸ interior_mono hsub hxq
  exact Sigma.ext hheight ((Subtype.heq_iff_coe_eq (by
    intro N
    rw [hheight])).mpr hval)

/-- Step 7 of the V4 proof of `honest_rows_step2_cont_labels` (V4 1.1, 1.7(a), 2.8):
"the facet f'' ... inside g". An inherited facet meeting the provider in its
relative interior is contained in it and has the same provider and serving node. -/
private theorem honest_rows_step2_cont_labels_step7_provider
    (U : HonestSource S) (t q : U.Node) (hq : q.1 = 0)
    (f : FacetName S t.2.val.ty) (g : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault t f) (hg : ¬ U.hierarchy.IsFault q g)
    (hanc : U.hierarchy.ancestor q (U.hierarchy.servingChild t f hf).1 =
      U.hierarchy.servingChild t f hf)
    (hmeet : (relint (q.2.val.cell q.1 g.val) ∩
      U.hierarchy.providerCarrier t f hf).Nonempty) :
    U.hierarchy.providerCarrier q g hg = U.hierarchy.providerCarrier t f hf ∧
      U.hierarchy.servingChild q g hg = U.hierarchy.servingChild t f hf := by
  let H := U.hierarchy.servingChild t f hf
  let F : FacetName S H.2.val.ty := (U.hierarchy.firstProvider t f hf).2
  have hd : q.2.val.IsDescendant q.1 H.2.val H.1 := by
    exact (congrArg (fun B : U.Node => q.2.val.IsDescendant q.1 B.2.val B.1) hanc).mp
      (U.hierarchy.ancestor_descendant q H.1)
  have hsub : q.2.val.cell q.1 g.val ⊆ H.2.val.cell H.1 F.val :=
    hereditary_trace H.2.val q.2.val H.1 q.1 hd F.val g.val
      (Finset.mem_filter.mp F.property).1 (Finset.mem_filter.mp g.property).1 hmeet
  have hint : relint (H.2.val.cell H.1 F.val) ⊆
      interior ((U.hierarchy.parentNode H).2.val.carrier (U.hierarchy.parentNode H).1) := by
    have he : U.hierarchy.ancestor t ((U.hierarchy.firstProvider t f hf).1 + 1) =
        U.hierarchy.parentNode H := by
      simp only [H, CoherentHierarchy.servingChild, CoherentHierarchy.ancestor,
        Function.iterate_succ_apply']
    exact (congrArg (fun B : U.Node => relint (H.2.val.cell H.1 F.val) ⊆
      interior (B.2.val.carrier B.1)) he).mp (U.hierarchy.firstProvider_spec t f hf).2.2
  obtain ⟨hF, hprovider, hbirth, _⟩ := U.hierarchy.restriction_det_internal H F hint
  obtain ⟨hg', hprovider', hbirth'⟩ :=
    U.hierarchy.provider_inherited H q H.1 hanc F g hF hsub
  have hb : U.hierarchy.birthParent q g hg = U.hierarchy.parentNode H :=
    hbirth'.trans hbirth
  refine ⟨hprovider'.trans hprovider, ?_⟩
  have hh := congrArg (fun N : U.Node => N.1) hb
  change (U.hierarchy.servingChild q g hg).1 + 1 = H.1 + 1 at hh
  have ha := U.hierarchy.ancestor_height q (U.hierarchy.firstProvider q g hg).1
  have hoff : (U.hierarchy.firstProvider q g hg).1 = H.1 := by
    change (U.hierarchy.servingChild q g hg).1 = _ at ha
    omega
  simpa only [CoherentHierarchy.servingChild, hoff] using hanc

/-- Step 8 of the V4 proof of `honest_rows_step2_cont_labels` (V4 2.8):
"same provider g, same serving child H". Apply the flag geometry to actual
records, identify the provider, and read its incidence, role and height residue. -/
private theorem honest_rows_step2_cont_labels_step8_source_labels
    (U : HonestSource S) (P : Params S) (t q : U.Node) (ht : t.1 = 0) (hq : q.1 = 0)
    (f : FacetName S t.2.val.ty) (g : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault t f) (hg : ¬ U.hierarchy.IsFault q g)
    (r s : FacetRecord P) (hr : r = U.recordOf P t f hf) (hs : s = U.recordOf P q g hg)
    (c : OrientedChain r.facet) (c' : OrientedChain s.facet) (hc : c ∈ r.chains)
    (φ : Iso d) (hφ : φ = q.2.val.frame.trans t.2.val.frame.symm)
    (halign : ChainsAligned r s c c' φ)
    (v : VertexName S r.ty) (hv : v.val.carrier ⊆ r.facet.val.carrier)
    (htau : r.tauAt v.val = some ((P.flag r.incidence).flag.cell edgeIndex).val)
    (hx : vertexPoint v ∈ φ '' (c'.chain.val.cell edgeIndex).val.carrier) :
    s.incidence = r.incidence ∧ s.side = r.side ∧ s.beta = r.beta := by
  classical
  subst r
  subst s
  let H := U.hierarchy.servingChild t f hf
  let τ := t.2.val.prototypeFrame t.1
  let χ := q.2.val.prototypeFrame q.1
  have hframe : φ.toAffineEquiv.trans τ = χ := by
    ext x
    simp [τ, χ, FramedNode.prototypeFrame, ht, hq, hφ]
  have himage (K : Set (E d)) : τ '' (φ '' K) = χ '' K := by
    rw [Set.image_image]
    change (φ.toAffineEquiv.trans τ) '' K = _
    rw [hframe]
  have hlinear (K : Set (E d)) : τ.linear '' (φ.linearIsometryEquiv '' K) =
      χ.linear '' K := by
    rw [Set.image_image]
    change (φ.toAffineEquiv.trans τ).linear '' K = _
    rw [hframe]
  have hactive : U.ActiveChain P t f hf c := (Finset.mem_filter.mp hc).2
  obtain ⟨F, _, hF, _, _⟩ := chain_active_owner U P t f hf c hc
  have hcells (j : FlagIndex d) :
      τ '' (c.chain.val.cell j).val.carrier ⊆ H.2.val.cell H.1 (F.cell j).val := by
    obtain ⟨he, hstr, _⟩ := hactive.1 j
    have hh := (U.hierarchy.stratumMap_spec t f hf (c.chain.val.cell j) he).1
    have hsame := hstr.trans (hF j).symm
    rw [hsame] at hh
    exact (by simpa only [restrictionOp_source_step5_cell_closure] using closure_mono hh)
  have hspans (j : FlagIndex d) :
      affineSpan ℝ (τ '' (c.chain.val.cell j).val.carrier) =
        affineSpan ℝ (H.2.val.cell H.1 (F.cell j).val) :=
    (hactive.1 j).choose_spec.2.trans (congrArg (affineSpan ℝ) (hF j).symm)
  have howner : τ '' (S.proto t.2.val.ty).carrier ⊆
      H.2.val.prototypeFrame H.1 '' (S.proto H.2.val.ty).carrier := by
    have hd : t.2.val.IsDescendant 0 H.2.val H.1 :=
      (congrArg (fun n => t.2.val.IsDescendant n H.2.val H.1) ht).mp
        (U.hierarchy.ancestor_descendant t (U.hierarchy.firstProvider t f hf).1)
    have hh := honest_rows_step2_cont_labels_step5_native_subset t.2.val H.2.val H.1 hd
    simpa only [τ, FramedNode.prototypeFrame, FramedNode.carrier, placedSet,
      SubstSystem.supertile, Set.image_image, ht] using hh
  obtain ⟨hsideH, hinwardH⟩ := honest_rows_step2_cont_labels_step2_nested_sides
    t.2.val.ty H.2.val.ty c.chain.val F τ (H.2.val.prototypeFrame H.1)
    hcells hspans howner
  have hspanQ (j : FlagIndex d) :
      affineSpan ℝ (τ '' (c.chain.val.cell j).val.carrier) =
        affineSpan ℝ (χ '' (c'.chain.val.cell j).val.carrier) := by
    have hh := congrArg (AffineSubspace.map τ.toAffineMap) (halign.1 j)
    simp only [AffineSubspace.map_span] at hh
    change affineSpan ℝ (τ '' (c.chain.val.cell j).val.carrier) =
      affineSpan ℝ (τ '' (φ '' (c'.chain.val.cell j).val.carrier)) at hh
    rwa [himage] at hh
  have hsideQ (j : FlagStep d) :
      τ.linear '' flagSide c.chain.val j = χ.linear '' flagSide c'.chain.val j := by
    simpa only [hlinear] using congrArg (fun K => τ.linear '' K) (halign.2.1 j)
  have hinwardQ :
      τ.linear '' tangentCone (S.proto t.2.val.ty).carrier
          (cellAnchor (c.chain.val.cell facetIndex).val) =
        χ.linear '' tangentCone (S.proto q.2.val.ty).carrier
          (cellAnchor (c'.chain.val.cell facetIndex).val) := by
    simpa only [c.chain.property, c'.chain.property, hlinear] using
      congrArg (fun K => τ.linear '' K) halign.2.2.2
  have hvcell : v.val ∈ (S.cx t.2.val.ty).cells := (Finset.mem_filter.mp v.property).1
  have hτ : (U.recordTau P t f hf ⟨vertexCell v, hv⟩).val.val =
      ((P.flag (U.recordIncidence P t f hf)).flag.cell edgeIndex).val := by
    unfold FacetRecord.tauAt at htau
    split at htau
    · exact Option.some.inj htau
    next hn => exact (hn hvcell).elim
  have hvertex : τ (vertexPoint v) ∈ relint (t.2.val.cell t.1 v.val) := by
    rw [FramedNode.cell, vertexPoint_spec, Set.image_singleton]
    simp only [relint, intrinsicInterior_singleton, Set.mem_singleton_iff]
    rfl
  have hxH : τ (vertexPoint v) ∈ relint (H.2.val.cell H.1 (F.cell edgeIndex).val) := by
    have hh := (U.hierarchy.stratumMap_spec t f hf (vertexCell v)
      (U.cellInFacet_placed t f ⟨vertexCell v, hv⟩)).1 hvertex
    have hsame := (record_tau_spec U P t f hf ⟨vertexCell v, hv⟩).symm
    change H.2.val.cell H.1 _ = U.providerPlacement P t f hf ''
      (U.recordTau P t f hf ⟨vertexCell v, hv⟩).val.val.carrier at hsame
    rw [hτ, ← hF edgeIndex] at hsame
    exact hsame ▸ hh
  have hxQ : τ (vertexPoint v) ∈ χ '' (c'.chain.val.cell edgeIndex).val.carrier := by
    rw [← himage]
    exact Set.mem_image_of_mem τ hx
  have hedge : (relint (χ '' (c'.chain.val.cell edgeIndex).val.carrier) ∩
      relint (H.2.val.cell H.1 (F.cell edgeIndex).val)).Nonempty := by
    apply honest_rows_step2_cont_labels_step4_relint_overlap _ _ (τ (vertexPoint v))
      _ hxH ((hspanQ edgeIndex).symm.trans (hspans edgeIndex))
    change τ (vertexPoint v) ∈ closure (relint (q.2.val.cell q.1 _))
    rw [restrictionOp_source_step5_cell_closure]
    exact hxQ
  obtain ⟨hfacet, htiles⟩ := honest_rows_step2_cont_labels_step3_flag_overlap
    q.2.val.ty H.2.val.ty c'.chain.val F χ (H.2.val.prototypeFrame H.1)
    (fun j => (hspanQ j).symm.trans (hspans j))
    (fun j => (hsideQ j).symm.trans (hsideH j)) (hinwardQ.symm.trans hinwardH) hedge
  have hanc : U.hierarchy.ancestor q H.1 = H := by
    apply honest_rows_step2_cont_labels_step6_ancestor U q H hq
    simpa only [χ, FramedNode.prototypeFrame, FramedNode.carrier, placedSet,
      SubstSystem.supertile, Set.image_image] using htiles
  have htop : H.2.val.cell H.1 (F.cell facetIndex).val =
      U.hierarchy.providerCarrier t f hf := by
    rw [hF facetIndex, (P.flag (U.recordIncidence P t f hf)).top]
    exact record_provider_carrier U P t f hf
  have hmeet : (relint (q.2.val.cell q.1 g.val) ∩
      U.hierarchy.providerCarrier t f hf).Nonempty := by
    obtain ⟨y, hyq, hyH⟩ := hfacet
    refine ⟨y, ?_, htop ▸ intrinsicInterior_subset hyH⟩
    simpa only [c'.chain.property] using hyq
  obtain ⟨hprovider, hserving⟩ :=
    honest_rows_step2_cont_labels_step7_provider U t q hq f g hf hg hanc hmeet
  refine ⟨restrictionOp_source_step4_provider_name P U q t g f hg hf
    (congrArg U.hierarchy.parentNode hserving) hprovider, ?_, ?_⟩
  · exact (record_side_spec U P q g hg).trans
      ((congrArg U.hierarchy.nodeRole hserving).trans (record_side_spec U P t f hf).symm)
  · apply Fin.ext
    exact congrArg (fun N : U.Node => N.1 % P.L) hserving

/-- Step 2 of the V4 proof of `honest_rows` (V4 2.8): "by Remark 2.1 (converse part) $e''$ is
a chain-active edge of the facet $f''$ of $t''$ inside $g$, whose record has the same $\iota$,
side and $\beta$ (same provider $g$, same serving child $H$)". -/
private theorem honest_rows_step2_cont_labels (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : ContSlot (leafTypeOf U P t ht)) (T : ContTemplate slot)
    (hT : IsActualTemplate U P t ht T.configuration)
    (hc : T.centralChain ∈ slot.record.chains) (ho : T.otherChain ∈ T.record.chains) :
    T.record.incidence = slot.record.incidence ∧ T.record.side = slot.record.side ∧
      T.record.beta = slot.record.beta := by
  obtain ⟨q, hq, hother, hlabel⟩ := hT.2 _ T.other_mem
  obtain ⟨f, hf, _, hr⟩ := honest_rows_step2_cont_labels_step1_read_record
    U P t ht slot.facet.val slot.record slot.record_eq
  have hread : leafRecord (leafTypeOf U P q hq) T.record.facet.val = some T.record := by
    exact (congrArg (fun l => leafRecord l T.record.facet.val) hlabel).symm.trans T.record_eq
  obtain ⟨g, hg, _, hs⟩ := honest_rows_step2_cont_labels_step1_read_record
    U P q hq T.record.facet.val T.record hread
  apply honest_rows_step2_cont_labels_step8_source_labels U P t q ht hq f g hf hg
    slot.record T.record hr hs T.centralChain T.otherChain hc T.other.frame
    (congrArg FramedNode.frame hother) T.aligned slot.vertex slot.onFacet slot.tau_edge
  refine ⟨vertexPoint T.vertex, ?_, T.vertex_eq⟩
  rw [T.other_edge, T.initial]
  have he := (Classical.choose_spec (edge_endpoints_exist ⟨T.record.ty, T.edge⟩)).2
  rw [he]
  dsimp only [FacetRecord.endpoints]
  split_ifs
  · exact left_mem_segment ℝ _ _
  · exact right_mem_segment ℝ _ _

/-- Step 1 of the V4 proof of `honest_rows_step3_cont_counters` (V4 2.8):
"both profiles are restrictions of the same site system". A finite readout of an
actual leaf is the record computed at that source node. -/
private theorem honest_rows_step3_cont_counters_step1_readout
    (U : HonestSource S) (P : Params S) (q : U.Node) (hq : q.1 = 0)
    (F : Cell d) (r : FacetRecord P)
    (hr : leafRecord (leafTypeOf U P q hq) F = some r) :
    ∃ (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f),
      r = U.recordOf P q f hf := by
  classical
  unfold leafRecord at hr
  rw [← prePattern_of_leafType U P q hq] at hr
  change stateRecordAt (stateOf U P q) F = some r at hr
  unfold stateRecordAt at hr
  split at hr
  · change U.facetRecordOf P q _ = some r at hr
    unfold HonestSource.facetRecordOf at hr
    split at hr
    · contradiction
    · exact ⟨_, _, (Option.some.inj hr).symm⟩
  · contradiction

/-- Step 2 of the V4 proof of `honest_rows_step3_cont_counters` (V4 2.8):
"there is a polygon s2'' adjacent to h on the far side of v ... with owner
t''". The aligned actual continuation belongs to the same serving child and
its top facet is contained in that child's provider facet. -/
private theorem honest_rows_step3_cont_counters_step2_containment
    (U : HonestSource S) (P : Params S) (t : U.Node) (ht : t.1 = 0)
    (slot : ContSlot (leafTypeOf U P t ht)) (T : ContTemplate slot)
    (q : U.Node) (hq : q.1 = 0)
    (hother : T.other = q.2.val.move t.2.val.frame.symm)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g)
    (hr : slot.record = U.recordOf P t f hf) (hr' : T.record = U.recordOf P q g hg)
    (hc : T.centralChain ∈ slot.record.chains) (ho : T.otherChain ∈ T.record.chains) :
    U.hierarchy.ancestor q (U.hierarchy.firstProvider t f hf).1 =
        U.hierarchy.servingChild t f hf ∧
      q.2.val.cell q.1 g.val ⊆ U.hierarchy.providerCarrier t f hf := by
  classical
  rcases slot with ⟨facet, r, hread, htype, hfacet, e, hactive, v, hvf, hterminal,
    htau, packet, hpacket⟩
  dsimp only at hr
  subst r
  rcases T with ⟨θ, hcentral, Q, l, hmem, htiles, hnone, r', hread', htype', c, he,
    c', e', he', v', hinitial, hvertex, halign, hsegment, hjunction⟩
  dsimp only at hother hr' hc ho
  subst Q
  subst r'
  let H := U.hierarchy.servingChild t f hf
  let τ := t.2.val.prototypeFrame t.1
  let χ := q.2.val.prototypeFrame q.1
  let φ := q.2.val.frame.trans t.2.val.frame.symm
  change ChainsAligned (U.recordOf P t f hf) (U.recordOf P q g hg) c c' φ at halign
  have hframe : φ.toAffineEquiv.trans τ = χ := by
    ext x
    simp [τ, χ, φ, FramedNode.prototypeFrame, ht, hq]
  have himage (K : Set (E d)) : τ '' (φ '' K) = χ '' K := by
    rw [Set.image_image]
    change (φ.toAffineEquiv.trans τ) '' K = _
    rw [hframe]
  have hlinear (K : Set (E d)) : τ.linear '' (φ.linearIsometryEquiv '' K) =
      χ.linear '' K := by
    rw [Set.image_image]
    change (φ.toAffineEquiv.trans τ).linear '' K = _
    rw [hframe]
  have hchain : U.ActiveChain P t f hf c := (Finset.mem_filter.mp hc).2
  obtain ⟨F, _, hF, _, _⟩ := chain_active_owner U P t f hf c hc
  have hcells (j : FlagIndex d) :
      τ '' (c.chain.val.cell j).val.carrier ⊆ H.2.val.cell H.1 (F.cell j).val := by
    obtain ⟨he, hstr, _⟩ := hchain.1 j
    have hh := (U.hierarchy.stratumMap_spec t f hf (c.chain.val.cell j) he).1
    have hsame := hstr.trans (hF j).symm
    rw [hsame] at hh
    exact (by simpa only [restrictionOp_source_step5_cell_closure] using closure_mono hh)
  have hspans (j : FlagIndex d) :
      affineSpan ℝ (τ '' (c.chain.val.cell j).val.carrier) =
        affineSpan ℝ (H.2.val.cell H.1 (F.cell j).val) :=
    (hchain.1 j).choose_spec.2.trans (congrArg (affineSpan ℝ) (hF j).symm)
  have howner : τ '' (S.proto t.2.val.ty).carrier ⊆
      H.2.val.prototypeFrame H.1 '' (S.proto H.2.val.ty).carrier := by
    have hd : t.2.val.IsDescendant 0 H.2.val H.1 :=
      (congrArg (fun n => t.2.val.IsDescendant n H.2.val H.1) ht).mp
        (U.hierarchy.ancestor_descendant t (U.hierarchy.firstProvider t f hf).1)
    have hh := honest_rows_step2_cont_labels_step5_native_subset t.2.val H.2.val H.1 hd
    simpa only [τ, FramedNode.prototypeFrame, FramedNode.carrier, placedSet,
      SubstSystem.supertile, Set.image_image, ht] using hh
  obtain ⟨hsideH, hinwardH⟩ := honest_rows_step2_cont_labels_step2_nested_sides
    t.2.val.ty H.2.val.ty c.chain.val F τ (H.2.val.prototypeFrame H.1)
    hcells hspans howner
  have hspanQ (j : FlagIndex d) :
      affineSpan ℝ (τ '' (c.chain.val.cell j).val.carrier) =
        affineSpan ℝ (χ '' (c'.chain.val.cell j).val.carrier) := by
    have hh := congrArg (AffineSubspace.map τ.toAffineMap) (halign.1 j)
    simp only [AffineSubspace.map_span] at hh
    change affineSpan ℝ (τ '' (c.chain.val.cell j).val.carrier) =
      affineSpan ℝ (τ '' (φ '' (c'.chain.val.cell j).val.carrier)) at hh
    rwa [himage] at hh
  have hsideQ (j : FlagStep d) :
      τ.linear '' flagSide c.chain.val j = χ.linear '' flagSide c'.chain.val j := by
    simpa only [hlinear] using congrArg (fun K => τ.linear '' K) (halign.2.1 j)
  have hinwardQ :
      τ.linear '' tangentCone (S.proto t.2.val.ty).carrier
          (cellAnchor (c.chain.val.cell facetIndex).val) =
        χ.linear '' tangentCone (S.proto q.2.val.ty).carrier
          (cellAnchor (c'.chain.val.cell facetIndex).val) := by
    simpa only [c.chain.property, c'.chain.property, hlinear] using
      congrArg (fun K => τ.linear '' K) halign.2.2.2
  -- The tau readout places the junction in the open serving flag edge.
  have hxH : τ (vertexPoint v) ∈ relint (H.2.val.cell H.1 (F.cell edgeIndex).val) := by
    rw [hF edgeIndex]
    exact actualCont_exists_step2_vertex U P t f hf v hvf htau
  have hxQ : τ (vertexPoint v) ∈ χ '' (c'.chain.val.cell edgeIndex).val.carrier := by
    rw [← himage]
    apply Set.mem_image_of_mem τ
    refine ⟨vertexPoint v', ?_, hvertex⟩
    rw [he', hinitial, (actualCont_exists_step2_endpoints (U.recordOf P q g hg) e').2]
    exact left_mem_segment ℝ _ _
  have hedge : (relint (χ '' (c'.chain.val.cell edgeIndex).val.carrier) ∩
      relint (H.2.val.cell H.1 (F.cell edgeIndex).val)).Nonempty := by
    apply honest_rows_step2_cont_labels_step4_relint_overlap _ _ (τ (vertexPoint v))
      _ hxH ((hspanQ edgeIndex).symm.trans (hspans edgeIndex))
    change τ (vertexPoint v) ∈ closure (relint (q.2.val.cell q.1 _))
    rw [restrictionOp_source_step5_cell_closure]
    exact hxQ
  -- Matching successive sides lift the edge overlap through the facets and into the owners.
  obtain ⟨hfacet, htiles⟩ := honest_rows_step2_cont_labels_step3_flag_overlap
    q.2.val.ty H.2.val.ty c'.chain.val F χ (H.2.val.prototypeFrame H.1)
    (fun j => (hspanQ j).symm.trans (hspans j))
    (fun j => (hsideQ j).symm.trans (hsideH j)) (hinwardQ.symm.trans hinwardH) hedge
  have hanc : U.hierarchy.ancestor q H.1 = H := by
    apply honest_rows_step2_cont_labels_step6_ancestor U q H hq
    simpa only [χ, FramedNode.prototypeFrame, FramedNode.carrier, placedSet,
      SubstSystem.supertile, Set.image_image] using htiles
  have hheight : H.1 = (U.hierarchy.firstProvider t f hf).1 := by
    simpa only [ht, Nat.zero_add] using
      U.hierarchy.ancestor_height t (U.hierarchy.firstProvider t f hf).1
  refine ⟨hheight ▸ hanc, ?_⟩
  have htop : H.2.val.cell H.1 (F.cell facetIndex).val =
      U.hierarchy.providerCarrier t f hf := by
    rw [hF facetIndex, (P.flag (U.recordIncidence P t f hf)).top]
    exact record_provider_carrier U P t f hf
  have hmeet : (relint (q.2.val.cell q.1 g.val) ∩
      U.hierarchy.providerCarrier t f hf).Nonempty := by
    obtain ⟨y, hyq, hyH⟩ := hfacet
    refine ⟨y, ?_, htop ▸ intrinsicInterior_subset hyH⟩
    simpa only [c'.chain.property] using hyq
  have hd : q.2.val.IsDescendant q.1 H.2.val H.1 := by
    have hh := U.hierarchy.ancestor_descendant q H.1
    rw [hanc] at hh
    exact hh
  let G : FacetName S H.2.val.ty := (U.hierarchy.firstProvider t f hf).2
  exact hereditary_trace H.2.val q.2.val H.1 q.1 hd G.val g.val
    (Finset.mem_filter.mp G.property).1 (Finset.mem_filter.mp g.property).1 hmeet

/-- Step 2 of the V4 proof of `honest_rows_step3_cont_counters` (V4 2.8):
"same provider g, same serving child H". The actual continuation of the active
positioned flag has the same birth parent as the central finite facet. -/
private theorem honest_rows_step3_cont_counters_step2_common_birth
    (U : HonestSource S) (P : Params S) (t : U.Node) (ht : t.1 = 0)
    (slot : ContSlot (leafTypeOf U P t ht)) (T : ContTemplate slot)
    (q : U.Node) (hq : q.1 = 0)
    (hother : T.other = q.2.val.move t.2.val.frame.symm)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g)
    (hr : slot.record = U.recordOf P t f hf) (hr' : T.record = U.recordOf P q g hg)
    (hc : T.centralChain ∈ slot.record.chains) (ho : T.otherChain ∈ T.record.chains) :
    U.hierarchy.birthParent t f hf = U.hierarchy.birthParent q g hg := by
  obtain ⟨hanc, hsub⟩ := honest_rows_step3_cont_counters_step2_containment U P t ht
    slot T q hq hother f hf g hg hr hr' hc ho
  let H := U.hierarchy.servingChild t f hf
  let a := (U.hierarchy.firstProvider t f hf).1
  let F : FacetName S H.2.val.ty := (U.hierarchy.firstProvider t f hf).2
  have hnext : U.hierarchy.ancestor t (a + 1) = U.hierarchy.parentNode H :=
    Function.iterate_succ_apply' _ _ _
  have hint : relint (H.2.val.cell H.1 F.val) ⊆
      interior ((U.hierarchy.parentNode H).2.val.carrier
        (U.hierarchy.parentNode H).1) := by
    have h := (U.hierarchy.firstProvider_spec t f hf).2.2
    change relint (H.2.val.cell H.1 F.val) ⊆
      interior ((U.hierarchy.ancestor t (a + 1)).2.val.carrier
        (U.hierarchy.ancestor t (a + 1)).1) at h
    rwa [hnext] at h
  obtain ⟨hF, _, hbirth, _⟩ := U.hierarchy.restriction_det_internal H F hint
  obtain ⟨_, _, hbirth'⟩ := U.hierarchy.provider_inherited H q a hanc F g hF hsub
  exact (hbirth'.trans hbirth).symm

/-- Step 3 of the V4 proof of `honest_rows_step3_cont_counters` (V4 2.8):
"just before v" and "just after v" refer to the endpoints of the actual edge.
Reversing its stored orientation exchanges the two distinct endpoints. -/
private theorem honest_rows_step3_cont_counters_step3_endpoints
    {P : Params S} (r : FacetRecord P) (e : PrototypeEdge S r.ty) :
    (r.endpoints e).1 ≠ (r.endpoints e).2 ∧
      e.val.carrier = segment ℝ (r.endpoints e).1 (r.endpoints e).2 := by
  have h := Classical.choose_spec (edge_endpoints_exist (⟨r.ty, e⟩ : EdgeName S))
  unfold FacetRecord.endpoints
  split
  · exact h
  · exact ⟨h.1.symm, h.2.trans (segment_symm ℝ _ _)⟩

/-- Step 4 of the V4 proof of `honest_rows_step3_cont_counters` (V4 2.8):
"the value of kappa" is independent of the frame used for its finite lookup.
On the active line, a full affine frame preserves both endpoint order tests. -/
private theorem honest_rows_step3_cont_counters_step4_word_order
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (e : PrototypeEdge S q.2.val.ty)
    (he : (U.recordOf P q f hf).ChainActive (edgeCell e))
    (x : E d) (hx : x ∈ e.val.carrier) (a : Fin P.N) :
    (inner ℝ (U.counterDirection P q f hf)
        (U.sitePoint P q f hf a - q.2.val.prototypeFrame q.1 x) ≤ 0 ↔
      inner ℝ (U.recordOf P q f hf).servingDirection
        (P.sites (U.recordIncidence P q f hf) (U.recordSide P q f hf) a -
          wordPlacement (U.downRoles q (U.hierarchy.firstProvider q f hf).1) x) ≤ 0) ∧
    (inner ℝ (U.counterDirection P q f hf)
        (U.sitePoint P q f hf a - q.2.val.prototypeFrame q.1 x) < 0 ↔
      inner ℝ (U.recordOf P q f hf).servingDirection
        (P.sites (U.recordIncidence P q f hf) (U.recordSide P q f hf) a -
          wordPlacement (U.downRoles q (U.hierarchy.firstProvider q f hf).1) x) < 0) := by
  let ι := U.recordIncidence P q f hf
  let b := U.recordSide P q f hf
  let H := U.hierarchy.servingChild q f hf
  let ψ := H.2.val.prototypeFrame H.1
  let R := (S.child ι.val.ty ι.val.left).frame.toAffineEquiv.trans
    (S.child ι.val.ty (ι.val.sideIndex b)).frame.symm.toAffineEquiv
  have hframes : R.trans ψ = U.providerPlacement P q f hf := by
    dsimp only [ψ, H]
    rw [restrictionOp_source_step4_profile_step4_serving_frame P U q f hf]
    apply AffineEquiv.ext
    intro y
    simp [R, rolePlacement, PrimitiveIncidence.sideRole, HonestSource.providerPlacement,
      Params.incidencePlacement, ι, b]
  have hdir : ψ.linear (U.recordOf P q f hf).servingDirection =
      U.counterDirection P q f hf :=
    congrArg (fun φ : E d ≃ᵃ[ℝ] E d => φ.linear (P.flag ι).direction) hframes
  have hpoint := congrArg (fun φ : E d ≃ᵃ[ℝ] E d => φ x)
    (restrictionOp_source_step4_profile_step3_word_frame U q
      (U.hierarchy.firstProvider q f hf).1)
  change q.2.val.prototypeFrame q.1 x =
    ψ (wordPlacement (U.downRoles q (U.hierarchy.firstProvider q f hf).1) x) at hpoint
  let v := P.sites ι b a -
    wordPlacement (U.downRoles q (U.hierarchy.firstProvider q f hf).1) x
  have hdiff : ψ.linear v = U.sitePoint P q f hf a - q.2.val.prototypeFrame q.1 x := by
    calc
      _ = ψ (P.sites ι b a) -
          ψ (wordPlacement (U.downRoles q (U.hierarchy.firstProvider q f hf).1) x) :=
        ψ.toAffineMap.linearMap_vsub _ _
      _ = _ := by
        rw [← restrictionOp_source_step4_profile_step4_site_placement P U q f hf a,
          ← hpoint]
  obtain ⟨z, hz⟩ := restrictionOp_source_step4_profile_step5_site_line P U q f hf
    (edgeCell e) he a _ (mem_affineSpan ℝ (Set.mem_image_of_mem _ hx))
  have hscalar : z • (U.recordOf P q f hf).servingDirection = v := by
    apply ψ.linear.injective
    rw [map_smul, hdir, hdiff]
    exact hz
  have hlt := restrictionOp_source_step4_profile_step5_linear_order ψ.linear
    (U.recordOf P q f hf).servingDirection v ⟨z, hscalar⟩
  have hneg := restrictionOp_source_step4_profile_step5_linear_order ψ.linear
    (U.recordOf P q f hf).servingDirection (-v)
    ⟨-z, by rw [neg_smul, hscalar]⟩
  have hle := not_congr hneg
  simp only [map_neg, inner_neg_right, neg_lt_zero, not_lt] at hle
  rw [hdir, hdiff] at hlt hle
  exact ⟨hle, hlt⟩

/-- Step 4 of the V4 proof of `honest_rows_step3_cont_counters` (V4 2.8):
"just before" and "just after" use the induced orientation. The active
chain table gives the same orientation to every occurrence of one edge. -/
private theorem honest_rows_step3_cont_counters_step4_orientation
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (e : PrototypeEdge S q.2.val.ty)
    (he : (U.recordOf P q f hf).ChainActive (edgeCell e)) :
    0 < inner ℝ (U.counterDirection P q f hf)
      (q.2.val.prototypeFrame q.1 ((U.recordOf P q f hf).endpoints e).2 -
        q.2.val.prototypeFrame q.1 ((U.recordOf P q f hf).endpoints e).1) := by
  classical
  obtain ⟨c, hc, hce⟩ := he
  have heq : e = (restrictionOp_source_step4_chains_step1_edge c.chain.val).2 :=
    Subtype.ext hce.symm
  subst e
  let r := U.recordOf P q f hf
  let e := (restrictionOp_source_step4_chains_step1_edge c.chain.val).2
  have horient (c' : OrientedChain f) (hc' : c' ∈ r.chains) :
      c'.forward = true ↔ 0 < inner ℝ (U.counterDirection P q f hf)
        ((q.2.val.prototypeFrame q.1).linear
          (edgeVector (restrictionOp_source_step4_chains_step1_edge c'.chain.val))) :=
    ((record_chains_spec U P q f hf c').mp hc').2
  have hsame (c' : OrientedChain f) (hc' : c' ∈ r.chains)
      (he' : (c'.chain.val.cell edgeIndex).val = e.val) : c'.forward = c.forward := by
    have he'' : restrictionOp_source_step4_chains_step1_edge c'.chain.val =
        restrictionOp_source_step4_chains_step1_edge c.chain.val := by
      exact congrArg (fun z : PrototypeEdge S q.2.val.ty =>
        (⟨q.2.val.ty, z⟩ : EdgeName S)) (Subtype.ext he')
    have ho := horient c hc
    have ho' := horient c' hc'
    rw [he''] at ho'
    have hb := ho'.trans ho.symm
    cases h1 : c'.forward <;> cases h2 : c.forward <;> simp_all
  have hforward : r.edgeForward e = c.forward := by
    unfold FacetRecord.edgeForward
    cases hcf : c.forward with
    | false =>
      apply Bool.eq_false_iff.mpr
      intro hh
      obtain ⟨c', hc', he'⟩ := List.any_eq_true.mp hh
      have hp : (c'.chain.val.cell edgeIndex).val = e.val ∧ c'.forward = true := by
        simpa using he'
      have hh := hsame c' (Finset.mem_toList.mp hc') hp.1
      simp_all
    | true =>
      apply List.any_eq_true.mpr
      refine ⟨c, Finset.mem_toList.mpr hc, ?_⟩
      simp [e, restrictionOp_source_step4_chains_step1_edge, hcf]
  have hvector : (r.endpoints e).2 - (r.endpoints e).1 =
      restrictionOp_source_step4_chains_step1_direction c := by
    unfold FacetRecord.endpoints
    rw [hforward]
    unfold restrictionOp_source_step4_chains_step1_direction
    cases c.forward <;> simp [e, edgeVector, neg_sub]
  obtain ⟨a, ha, hdir⟩ := ((restrictionOp_source_step4_chains_step1_test U P q f hf c).mp
    ((record_chains_spec U P q f hf c).mp hc)).2
  rw [← hvector] at hdir
  have hv : (q.2.val.prototypeFrame q.1).linear
      ((r.endpoints e).2 - (r.endpoints e).1) ≠ 0 := by
    intro h
    have hz := (q.2.val.prototypeFrame q.1).linear.injective
      (h.trans (map_zero _).symm)
    exact (honest_rows_step3_cont_counters_step3_endpoints r e).1
      (sub_eq_zero.mp hz).symm
  have hpos : 0 < inner ℝ (U.counterDirection P q f hf)
      ((q.2.val.prototypeFrame q.1).linear ((r.endpoints e).2 - (r.endpoints e).1)) := by
    rw [hdir, real_inner_smul_left]
    exact mul_pos ha (real_inner_self_pos.mpr hv)
  have hmap : (q.2.val.prototypeFrame q.1).linear
      ((r.endpoints e).2 - (r.endpoints e).1) =
      q.2.val.prototypeFrame q.1 (r.endpoints e).2 -
        q.2.val.prototypeFrame q.1 (r.endpoints e).1 :=
    (q.2.val.prototypeFrame q.1).toAffineMap.linearMap_vsub _ _
  rwa [hmap] at hpos

/-- Step 4 of the V4 proof of `honest_rows_step3_cont_counters` (V4 2.8):
"just before" and "just after" are limits through the open edge. A
nondegenerate segment's relative interior has interpolation parameter in (0,1). -/
private theorem honest_rows_step3_cont_counters_step4_segment_relint
    (p q : E d) (hpq : p ≠ q) :
    relint (segment ℝ p q) = AffineMap.lineMap p q '' Ioo (0 : ℝ) 1 := by
  let L := ‖q - p‖
  have hL : 0 < L := norm_pos_iff.mpr (sub_ne_zero.mpr hpq.symm)
  let u := L⁻¹ • (q - p)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    exact inv_mul_cancel₀ hL.ne'
  let φ : ℝ →ᵃⁱ[ℝ] E d := {
    toAffineMap := {
      toFun := fun t => t • u + p
      linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight u
      map_vadd' := by
        intro t s
        change (s + t) • u + p = s • u + (t • u + p)
        rw [add_smul, add_assoc] }
    norm_map := by
      intro t
      change ‖t • u‖ = ‖t‖
      rw [norm_smul, hu, mul_one] }
  have hφ0 : φ 0 = p := by change (0 : ℝ) • u + p = p; simp
  have hφL : φ L = q := by
    change L • (L⁻¹ • (q - p)) + p = q
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul, sub_add_cancel]
  have hseg : segment ℝ p q = φ '' Icc 0 L := by
    simpa only [AffineIsometry.coe_toAffineMap, hφ0, hφL, segment_eq_Icc hL.le] using
      (image_segment ℝ φ.toAffineMap 0 L).symm
  have hir : intrinsicInterior ℝ (Icc (0 : ℝ) L) = Ioo 0 L := by
    have hspan : affineSpan ℝ (Icc (0 : ℝ) L) = ⊤ :=
      (convex_Icc 0 L).interior_nonempty_iff_affineSpan_eq_top.mp
        (by rw [interior_Icc]; exact nonempty_Ioo.mpr hL)
    rw [intrinsicInterior, hspan]
    change (Homeomorph.Set.univ ℝ) ''
      interior ((Homeomorph.Set.univ ℝ) ⁻¹' Icc 0 L) = Ioo 0 L
    rw [(Homeomorph.Set.univ ℝ).image_interior]
    simp
  rw [hseg, relint, φ.image_intrinsicInterior, hir]
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t / L, ⟨div_pos ht.1 hL, (div_lt_one hL).mpr ht.2⟩, ?_⟩
    have he := φ.toAffineMap.apply_lineMap (0 : ℝ) L (t / L)
    simpa [AffineMap.lineMap_apply_ring, hφ0, hφL, hL.ne'] using he.symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * L, ⟨mul_pos ht.1 hL, by nlinarith [ht.2]⟩, ?_⟩
    have he := φ.toAffineMap.apply_lineMap (0 : ℝ) L t
    simpa [AffineMap.lineMap_apply_ring, hφ0, hφL] using he

/-- Step 4 of the V4 proof of `honest_rows_step3_cont_counters` (V4 2.8):
"the value of kappa just before v". When no site is in the open edge,
counting at any interior point gives both one-sided endpoint counts. -/
private theorem honest_rows_step3_cont_counters_step4_interval
    (p q u s x : E d) (hpos : 0 < inner ℝ u (q - p))
    (hs : s ∈ affineSpan ℝ (segment ℝ p q)) (hn : s ∉ relint (segment ℝ p q))
    (hx : x ∈ relint (segment ℝ p q)) :
    (inner ℝ u (s - p) ≤ 0 ↔ inner ℝ u (s - x) < 0) ∧
      (inner ℝ u (s - q) < 0 ↔ inner ℝ u (s - x) < 0) := by
  have hpq : p ≠ q := by intro h; simp [h] at hpos
  rw [← convexHull_pair, affineSpan_convexHull] at hs
  obtain ⟨a, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hs
  rw [honest_rows_step3_cont_counters_step4_segment_relint p q hpq] at hn hx
  obtain ⟨b, hb, rfl⟩ := hx
  have ha : ¬ (0 < a ∧ a < 1) := fun h => hn ⟨a, h, rfl⟩
  have hlinear (c e : ℝ) :
      inner ℝ u (AffineMap.lineMap p q c - AffineMap.lineMap p q e) =
        (c - e) * inner ℝ u (q - p) := by
    have hv : AffineMap.lineMap p q c - AffineMap.lineMap p q e = (c - e) • (q - p) := by
      simp only [AffineMap.lineMap_apply_module]
      module
    rw [hv, real_inner_smul_right]
  have hzero := hlinear a 0
  have hone := hlinear a 1
  simp only [AffineMap.lineMap_apply_zero, sub_zero] at hzero
  simp only [AffineMap.lineMap_apply_one] at hone
  rw [hzero, hone, hlinear]
  by_cases ha0 : a ≤ 0
  · have h0 := mul_nonpos_of_nonpos_of_nonneg ha0 hpos.le
    have h1 := mul_neg_of_neg_of_pos (show a - 1 < 0 by linarith) hpos
    have hb' := mul_neg_of_neg_of_pos (show a - b < 0 by linarith [hb.1]) hpos
    simp only [h0, h1, hb', iff_self, and_self]
  · have ha1 : 1 ≤ a := by push_neg at ha; exact ha (lt_of_not_ge ha0)
    have h0 := mul_pos (lt_of_not_ge ha0) hpos
    have h1 := mul_nonneg (sub_nonneg.mpr ha1) hpos.le
    have hb' := mul_pos (show 0 < a - b by linarith [hb.2]) hpos
    simp only [not_le.mpr h0, not_lt.mpr h1, not_lt.mpr hb'.le, iff_self, and_self]

/-- Step 4 of the V4 proof of `honest_rows_step3_cont_counters` (V4 2.8):
"kappa+(e) is the value of kappa just before v and kappa-(e'') the value just
after v". In either profile branch these are the strict and non-strict counts
of physical sites at the oriented endpoints of one honest active edge. -/
private theorem honest_rows_step3_cont_counters_step4_germs
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (r : FacetRecord P) (hr : r = U.recordOf P q f hf)
    (e : PrototypeEdge S r.ty) (he : r.ChainActive (edgeCell e)) :
    r.kappaMinus e = (Finset.univ.filter (fun a : Fin P.N =>
      inner ℝ (U.counterDirection P q f hf) (U.sitePoint P q f hf a -
        q.2.val.prototypeFrame q.1 (r.endpoints e).1) ≤ 0)).card ∧
    r.kappaPlus e = (Finset.univ.filter (fun a : Fin P.N =>
      inner ℝ (U.counterDirection P q f hf) (U.sitePoint P q f hf a -
        q.2.val.prototypeFrame q.1 (r.endpoints e).2) < 0)).card := by
  classical
  subst r
  let r := U.recordOf P q f hf
  have hegeom := honest_rows_step3_cont_counters_step3_endpoints r e
  have hends : (r.endpoints e).1 ∈ e.val.carrier ∧
      (r.endpoints e).2 ∈ e.val.carrier := by
    rw [hegeom.2]
    exact ⟨left_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩
  by_cases hm : P.siteDepth (U.recordIncidence P q f hf) (U.recordSide P q f hf) ≤
      (U.hierarchy.firstProvider q f hf).1
  · have hw := (record_mature_iff U P q f hf).mpr hm
    have hzero : (Finset.univ.filter (fun a : Fin P.N =>
        U.sitePoint P q f hf a ∈ relint (q.2.val.cell q.1 e.val))).card = 0 := by
      simpa only [FacetRecord.kappaMinus, FacetRecord.kappaPlus, hw, Nat.sub_self] using
        (honest_counter_jump_count U P q f hf e he).symm
    have hnone (a : Fin P.N) :
        U.sitePoint P q f hf a ∉ relint (q.2.val.cell q.1 e.val) := by
      intro ha
      have hmem : a ∈ Finset.univ.filter (fun a : Fin P.N =>
          U.sitePoint P q f hf a ∈ relint (q.2.val.cell q.1 e.val)) := by simp [ha]
      rw [Finset.card_eq_zero.mp hzero] at hmem
      simp at hmem
    let x := q.2.val.prototypeFrame q.1 (cellAnchor e.val)
    have hx : x ∈ relint (q.2.val.cell q.1 e.val) := by
      rw [FramedNode.cell, restrictionOp_source_step5_relint_image]
      exact Set.mem_image_of_mem _ (cellAnchor_mem e.val)
    have hvalue := mature_counter_value U P q f hf hm (edgeCell e) he x hx
    have hminus : r.kappaMinus e = (U.sitesBefore P q f hf x).val := by
      simp only [r, FacetRecord.kappaMinus, hw, hvalue, Option.getD_some]
    have hplus : r.kappaPlus e = (U.sitesBefore P q f hf x).val := by
      simp only [r, FacetRecord.kappaPlus, hw, hvalue, Option.getD_some]
    let p₀ := q.2.val.prototypeFrame q.1 (r.endpoints e).1
    let p₁ := q.2.val.prototypeFrame q.1 (r.endpoints e).2
    have hseg : q.2.val.cell q.1 e.val = segment ℝ p₀ p₁ := by
      rw [FramedNode.cell, hegeom.2]
      exact image_segment ℝ (q.2.val.prototypeFrame q.1).toAffineMap _ _
    have hspan : affineSpan ℝ (q.2.val.cell q.1 e.val) =
        affineSpan ℝ (U.providerPlacement P q f hf ''
          ((P.flag (U.recordIncidence P q f hf)).flag.cell edgeIndex).val.carrier) := by
      obtain ⟨c, hc, hce⟩ := he
      obtain ⟨_, _, h⟩ := ((record_chains_spec U P q f hf c).mp hc).1 edgeIndex
      simpa only [hce] using h
    have hcounts (a : Fin P.N) :
        (inner ℝ (U.counterDirection P q f hf) (U.sitePoint P q f hf a - p₀) ≤ 0 ↔
          inner ℝ (U.counterDirection P q f hf) (U.sitePoint P q f hf a - x) < 0) ∧
        (inner ℝ (U.counterDirection P q f hf) (U.sitePoint P q f hf a - p₁) < 0 ↔
          inner ℝ (U.counterDirection P q f hf) (U.sitePoint P q f hf a - x) < 0) := by
      apply honest_rows_step3_cont_counters_step4_interval
      · exact honest_rows_step3_cont_counters_step4_orientation U P q f hf e he
      · rw [← hseg, hspan]
        exact mem_affineSpan ℝ
          (restrictionOp_source_step4_profile_step5_site_in_flag P U q f hf a)
      · simpa only [← hseg] using hnone a
      · simpa only [← hseg] using hx
    constructor
    · rw [hminus]
      change (Finset.univ.filter (fun a : Fin P.N =>
        inner ℝ (U.counterDirection P q f hf) (U.sitePoint P q f hf a - x) < 0)).card = _
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro a _
      exact (hcounts a).1.symm
    · rw [hplus]
      change (Finset.univ.filter (fun a : Fin P.N =>
        inner ℝ (U.counterDirection P q f hf) (U.sitePoint P q f hf a - x) < 0)).card = _
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro a _
      exact (hcounts a).2.symm
  · obtain ⟨w, hw, hword⟩ := (record_shallow_iff U P q f hf).mpr (lt_of_not_ge hm)
    constructor
    · rw [FacetRecord.kappaMinus, hw]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro a _
      simpa only [hword] using
        (honest_rows_step3_cont_counters_step4_word_order U P q f hf e he
          (r.endpoints e).1 hends.1 a).1.symm
    · rw [FacetRecord.kappaPlus, hw]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro a _
      simpa only [hword] using
        (honest_rows_step3_cont_counters_step4_word_order U P q f hf e he
          (r.endpoints e).2 hends.2 a).2.symm

/-- Step 5 of the V4 proof of `honest_rows_step3_cont_counters` (V4 2.8):
"v is a site iff it is recorded as a site in the profiles". Transport the
existing physical endpoint-site specification through a record readout. -/
private theorem honest_rows_step3_cont_counters_step5_site_readout
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (r : FacetRecord P) (hr : r = U.recordOf P q f hf)
    (e : PrototypeEdge S r.ty) (he : r.ChainActive (edgeCell e))
    (v : VertexName S r.ty) (hv : vertexPoint v ∈ e.val.carrier) :
    r.isSite v = true ↔
      ∃ a : Fin P.N, U.sitePoint P q f hf a = q.2.val.prototypeFrame q.1 (vertexPoint v) := by
  subst r
  exact honest_counter_endpoint_site U P q f hf e he v hv

/-- Step 6 of the V4 proof of `honest_rows_step3_cont_counters` (V4 2.8):
"kappa jumps by 1 exactly at sites". All sites and an active-edge endpoint
lie on the same line, whose counter direction is nonzero. -/
private theorem honest_rows_step3_cont_counters_step6_site_line
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (r : FacetRecord P) (hr : r = U.recordOf P q f hf)
    (e : PrototypeEdge S r.ty) (he : r.ChainActive (edgeCell e))
    (x : E d) (hx : x ∈ e.val.carrier) :
    U.counterDirection P q f hf ≠ 0 ∧
      ∀ a : Fin P.N, ∃ b : ℝ, b • U.counterDirection P q f hf =
        U.sitePoint P q f hf a - q.2.val.prototypeFrame q.1 x := by
  subst r
  constructor
  · intro h
    have hz := (U.providerPlacement P q f hf).linear.injective
      (h.trans (map_zero _).symm)
    exact (P.flag (U.recordIncidence P q f hf)).distinct (sub_eq_zero.mp hz).symm
  · intro a
    exact restrictionOp_source_step4_profile_step5_site_line P U q f hf (edgeCell e) he a
      _ (mem_affineSpan ℝ (Set.mem_image_of_mem _ hx))

/-- Step 7 of the V4 proof of `honest_rows_step3_cont_counters` (V4 2.8):
"kappa jumps by 1 exactly at sites". The ordered sites remain distinct under
the serving child's invertible affine placement. -/
private theorem honest_rows_step3_cont_counters_step7_sites_injective
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f) :
    Function.Injective (U.sitePoint P q f hf) := by
  intro a b h
  simp only [restrictionOp_source_step4_profile_step4_site_placement] at h
  exact P.sites_injective _ _ (((U.hierarchy.servingChild q f hf).2.val.prototypeFrame
    (U.hierarchy.servingChild q f hf).1).injective h)

/-- Step 8 of the V4 proof of `honest_rows_step3_cont_counters` (V4 2.8):
"kappa jumps by 1 exactly at sites". Passing from a strict count to a
non-strict count adds the unique site at the point, if there is one. -/
private theorem honest_rows_step3_cont_counters_step8_count
    {n : ℕ} (p : Fin n → E d) (hp : Function.Injective p) (u x : E d) (hu : u ≠ 0)
    (hline : ∀ a, ∃ b : ℝ, b • u = p a - x) :
    let lo := (Finset.univ.filter (fun a => inner ℝ u (p a - x) < 0)).card
    let hi := (Finset.univ.filter (fun a => inner ℝ u (p a - x) ≤ 0)).card
    (hi = lo ∨ hi = lo + 1) ∧ (hi = lo + 1 ↔ ∃ a, p a = x) := by
  classical
  let A := Finset.univ.filter (fun a => inner ℝ u (p a - x) < 0)
  let B := Finset.univ.filter (fun a => inner ℝ u (p a - x) ≤ 0)
  let Z := Finset.univ.filter (fun a => inner ℝ u (p a - x) = 0)
  have hz (a : Fin n) : inner ℝ u (p a - x) = 0 ↔ p a = x := by
    constructor
    · intro h
      obtain ⟨b, hb⟩ := hline a
      rw [← hb, real_inner_smul_right] at h
      have hb0 : b = 0 := (mul_eq_zero.mp h).resolve_right
        (ne_of_gt (real_inner_self_pos.mpr hu))
      exact sub_eq_zero.mp (by rw [← hb, hb0, zero_smul])
    · intro h
      simp [h]
  have hB : B = A ∪ Z := by
    ext a
    simp only [A, B, Z, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact le_iff_lt_or_eq
  have hd : Disjoint A Z := by
    apply Finset.disjoint_left.mpr
    intro a ha hz'
    exact (ne_of_lt (Finset.mem_filter.mp ha).2) (Finset.mem_filter.mp hz').2
  have hcard : B.card = A.card + Z.card := by rw [hB, Finset.card_union_of_disjoint hd]
  have hsmall : Z.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hp (((hz a).mp (Finset.mem_filter.mp ha).2).trans
      ((hz b).mp (Finset.mem_filter.mp hb).2).symm)
  have hex : (∃ a, p a = x) ↔ 0 < Z.card := by
    rw [Finset.card_pos]
    simp only [Finset.Nonempty, Z, Finset.mem_filter, Finset.mem_univ, true_and, hz]
  change (B.card = A.card ∨ B.card = A.card + 1) ∧
    (B.card = A.card + 1 ↔ ∃ a, p a = x)
  rw [hex]
  omega

/-- Step 3 of the V4 proof of `honest_rows` (V4 2.8): "Counters: $\kappa^+(e)$ is the value
of $\kappa$ just before $v$ and $\kappa^-(e'')$ the value just after $v$; $\kappa$ jumps by
$1$ exactly at sites, so the difference is $1$ iff $v$ is a site, and $v$ is a site iff it is
recorded as a site in the profiles of both tiles". -/
private theorem honest_rows_step3_cont_counters (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : ContSlot (leafTypeOf U P t ht)) (T : ContTemplate slot)
    (hT : IsActualTemplate U P t ht T.configuration)
    (hc : T.centralChain ∈ slot.record.chains) (ho : T.otherChain ∈ T.record.chains) :
    (T.record.kappaMinus T.edge = slot.record.kappaPlus slot.edge ∨
      T.record.kappaMinus T.edge = slot.record.kappaPlus slot.edge + 1) ∧
    (T.record.kappaMinus T.edge = slot.record.kappaPlus slot.edge + 1 ↔
      slot.record.isSite slot.vertex = true ∧ T.record.isSite T.vertex = true) := by
  classical
  obtain ⟨q, hq, hother, hlabel⟩ := hT.2 _ T.other_mem
  dsimp only at hother hlabel
  obtain ⟨f, hf, hr⟩ := honest_rows_step3_cont_counters_step1_readout U P t ht
    slot.facet.val slot.record slot.record_eq
  have hread := T.record_eq
  rw [hlabel] at hread
  obtain ⟨g, hg, hr'⟩ := honest_rows_step3_cont_counters_step1_readout U P q hq
    T.record.facet.val T.record hread
  have hbirth := honest_rows_step3_cont_counters_step2_common_birth U P t ht slot T
    q hq hother f hf g hg hr hr' hc ho
  obtain ⟨hi, hs, _⟩ := honest_rows_step2_cont_labels U P t ht slot T hT hc ho
  have hside : T.record.sideIndex = slot.record.sideIndex := by
    have hroles : slot.record.incidence.val.sideRole T.record.sideIndex =
        slot.record.incidence.val.sideRole slot.record.sideIndex := by
      simpa only [hi] using T.record.side_eq.symm.trans (hs.trans slot.record.side_eq)
    have hd := slot.record.incidence.val.distinct
    cases hb : T.record.sideIndex <;> cases hb' : slot.record.sideIndex <;>
      simp_all [PrimitiveIncidence.sideRole, PrimitiveIncidence.sideIndex]
  have hinc : U.recordIncidence P q g hg = U.recordIncidence P t f hf := by
    simpa only [hr, hr', HonestSource.recordOf] using hi
  have hside' : U.recordSide P q g hg = U.recordSide P t f hf := by
    simpa only [hr, hr', HonestSource.recordOf] using hside
  have hplace : U.providerPlacement P q g hg = U.providerPlacement P t f hf := by
    unfold HonestSource.providerPlacement CoherentHierarchy.birthHeight
    rw [← hbirth, hinc]
  have hsites (a : Fin P.N) : U.sitePoint P q g hg a = U.sitePoint P t f hf a := by
    simp only [HonestSource.sitePoint, hplace, hinc, hside']
  have hdir : U.counterDirection P q g hg = U.counterDirection P t f hf := by
    unfold HonestSource.counterDirection
    rw [hplace, hinc]
  have hpoint : q.2.val.prototypeFrame q.1 (vertexPoint T.vertex) =
      t.2.val.prototypeFrame t.1 (vertexPoint slot.vertex) := by
    have hv := T.vertex_eq
    rw [hother] at hv
    have h := congrArg t.2.val.frame hv
    change t.2.val.frame (t.2.val.frame.symm (q.2.val.frame (vertexPoint T.vertex))) =
      t.2.val.frame (vertexPoint slot.vertex) at h
    rw [t.2.val.frame.apply_symm_apply] at h
    simpa [FramedNode.prototypeFrame, ht, hq] using h
  have he : T.record.ChainActive (edgeCell T.edge) := ⟨T.otherChain, ho, T.other_edge⟩
  have hv : vertexPoint slot.vertex ∈ slot.edge.val.carrier := by
    rw [slot.terminal, (honest_rows_step3_cont_counters_step3_endpoints
      slot.record slot.edge).2]
    exact right_mem_segment ℝ _ _
  have hv' : vertexPoint T.vertex ∈ T.edge.val.carrier := by
    rw [T.initial, (honest_rows_step3_cont_counters_step3_endpoints T.record T.edge).2]
    exact left_mem_segment ℝ _ _
  have hk := (honest_rows_step3_cont_counters_step4_germs U P t f hf
    slot.record hr slot.edge slot.active).2
  have hk' := (honest_rows_step3_cont_counters_step4_germs U P q g hg
    T.record hr' T.edge he).1
  rw [← slot.terminal] at hk
  rw [← T.initial, hpoint, hdir] at hk'
  simp only [hsites] at hk'
  have hvsite := honest_rows_step3_cont_counters_step5_site_readout U P t f hf
    slot.record hr slot.edge slot.active slot.vertex hv
  have hvsite' := honest_rows_step3_cont_counters_step5_site_readout U P q g hg
    T.record hr' T.edge he T.vertex hv'
  simp only [hsites, hpoint] at hvsite'
  obtain ⟨hu, hline⟩ := honest_rows_step3_cont_counters_step6_site_line U P t f hf
    slot.record hr slot.edge slot.active (vertexPoint slot.vertex) hv
  have hcount := honest_rows_step3_cont_counters_step8_count (U.sitePoint P t f hf)
    (honest_rows_step3_cont_counters_step7_sites_injective U P t f hf)
    (U.counterDirection P t f hf) (t.2.val.prototypeFrame t.1 (vertexPoint slot.vertex))
    hu hline
  dsimp only at hcount
  rw [← hk, ← hk'] at hcount
  refine ⟨hcount.1, hcount.2.trans ?_⟩
  exact ⟨fun h => ⟨hvsite.mpr h, hvsite'.mpr h⟩, fun h => hvsite.mp h.1⟩

/-- Step 1 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"A is a polyhedron". A simplex, including a lower-dimensional one, is cut out by
finitely many affine inequalities, using coordinates of an extended affine basis. -/
private lemma honest_rows_step4_cont_packet_step1_simplex
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

/-- Step 1 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"A is a polyhedron". Carathéodory's theorem gives a finite union of simplices,
and hence a finite union of intersections of affine closed half-spaces. -/
private lemma honest_rows_step4_cont_packet_step1_halfspaces
    {K : Set (E d)} (hK : Polyhedron K) :
    ∃ S : Finset (Finset (E d →ᵃ[ℝ] ℝ)),
      K = ⋃ q ∈ S, {x | ∀ f ∈ q, 0 ≤ f x} := by
  classical
  obtain ⟨s, rfl⟩ := hK
  have hrep (t : Finset (E d)) : ∃ q : Finset (E d →ᵃ[ℝ] ℝ),
      AffineIndependent ℝ ((↑) : t → E d) →
        convexHull ℝ (t : Set (E d)) = {x | ∀ f ∈ q, 0 ≤ f x} := by
    by_cases ht : AffineIndependent ℝ ((↑) : t → E d)
    · obtain ⟨q, hq⟩ := honest_rows_step4_cont_packet_step1_simplex t ht
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
/-- Step 1 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"its tangent cone at any point is a polyhedral cone". Near the base point,
inactive inequalities keep their sign and active inequalities become homogeneous. -/
private lemma honest_rows_step4_cont_packet_step1_local_cone
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

/-- Step 1 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"polyhedral cone". Homogeneous half-space inequalities are invariant under
multiplication by a positive scalar, as is a finite union of their intersections. -/
private lemma honest_rows_step4_cont_packet_step1_scaling
    {C : Set (E d)} (hC : IsPolyhedralCone C) {r : ℝ} (hr : 0 < r) (v : E d) :
    r • v ∈ C ↔ v ∈ C := by
  obtain ⟨S, rfl⟩ := hC
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, map_smul, smul_eq_mul,
    mul_nonneg_iff_of_pos_left hr]

open scoped Topology in
/-- Step 1 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"its tangent cone at any point is a polyhedral cone". A local conical model
equals the positive-time radial germ in the definition of `tangentCone`. -/
private lemma honest_rows_step4_cont_packet_step1_radial
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
    exact (honest_rows_step4_cont_packet_step1_scaling hC ht v).mp
      ((hδloc hnear).mp (hv t ht htε))
  · intro hv
    refine ⟨δ, hδ, fun t ht htδ => ?_⟩
    have hnear : dist t 0 < δ := by simpa [Real.dist_eq, abs_of_pos ht] using htδ
    exact (hδloc hnear).mpr
      ((honest_rows_step4_cont_packet_step1_scaling hC ht v).mpr hv)

/-- Step 2 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(a)):
"each component is inside or outside A". On a connected set on which boundary
membership is constant, membership in a closed set is constant as well. -/
private lemma honest_rows_step4_cont_packet_step2_membership
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

/-- Step 2 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"the local structure is constant by (a) applied to the cell complex". Translation
invariance of the relative boundary of a closed set extends to the set itself,
provided the translations are parallel to its affine span. -/
private lemma honest_rows_step4_cont_packet_step2_fill
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
    have heq := honest_rows_step4_cont_packet_step2_membership
      (hS.preimage continuous_subtype_val)
      (isPreconnected_Icc.image γ hγcont.continuousOn) hinv
      (mem_image_of_mem γ (left_mem_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)))
      (mem_image_of_mem γ (right_mem_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)))
    simpa [γ] using heq.mp (by simpa [γ] using hxs)
  intro x hx y hy hyx
  exact ⟨hforward x hx y hy hyx,
    hforward y hy x hx (by simpa only [neg_sub] using V.neg_mem hyx)⟩

/-- Step 2 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(a)):
"if p ∈ e ... then mc_A(p) ⊆ e". A listed cell meeting the relative interior
of another listed cell contains the whole latter cell. -/
private lemma honest_rows_step4_cont_packet_step2_incidence
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

/-- Step 2 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(a)):
"Cells are closed and finitely many, so some ball U ...". Finitely many local
translation invariances hold on a common ball, including for an empty family. -/
private lemma honest_rows_step4_cont_packet_step2_common_ball
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

/-- Step 2 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"the local structure is constant by (a) applied to the cell complex". Induction
through relative boundaries makes every listed carrier locally invariant in the
directions of the cell containing the base point in its relative interior. -/
private lemma honest_rows_step4_cont_packet_step2_invariance
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
      · have hef := honest_rows_step4_cont_packet_step2_incidence K he hf hp hpf
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
        obtain ⟨r, hr, hc⟩ := honest_rows_step4_cont_packet_step2_common_ball b
          Cell.carrier (cellDirection e.carrier) p (fun g hg =>
            ih (N g) (by simpa only [hN] using hsmall g hg) g (hb hg) rfl)
        refine ⟨r, hr, honest_rows_step4_cont_packet_step2_fill f.flat.compact.isClosed
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

open scoped Topology in
/-- Step 2 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"the local structure is constant". Equal translated germs give equal radial
tangent cones; only sufficiently short positive portions of each ray matter. -/
private lemma honest_rows_step4_cont_packet_step2_tangent_germ
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

open scoped Topology in
/-- Step 1 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"A is a polyhedron". Its radial tangent cone determines its entire local germ. -/
private theorem honest_rows_step4_cont_packet_step1_germ
    {K : Set (E d)} (hK : Polyhedron K) (p : E d) :
    ∀ᶠ x in 𝓝 p, x ∈ K ↔ x - p ∈ tangentCone K p := by
  obtain ⟨s, hs⟩ := honest_rows_step4_cont_packet_step1_halfspaces hK
  obtain ⟨C, hC, hlocal⟩ := honest_rows_step4_cont_packet_step1_local_cone s p
  rw [← hs] at hlocal
  rwa [honest_rows_step4_cont_packet_step1_radial p hC hlocal]

/-- Step 1 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"the local structure" is transported by the full affine placement. -/
private theorem honest_rows_step4_cont_packet_step1_placed_germ
    {K : Set (E d)} (hK : Polyhedron K) (φ : E d ≃ᵃ[ℝ] E d) (p : E d) :
    ∃ V : Set (E d), IsOpen V ∧ φ p ∈ V ∧ ∀ x ∈ V,
      x ∈ φ '' K ↔ x - φ p ∈ φ.linear '' tangentCone K p := by
  obtain ⟨r, hr, hlocal⟩ := Metric.eventually_nhds_iff.mp
    (honest_rows_step4_cont_packet_step1_germ hK p)
  refine ⟨φ '' ball p r, φ.toHomeomorphOfFiniteDimensional.isOpenMap _ isOpen_ball,
    ⟨p, mem_ball_self hr, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hdiff : φ.linear (x - p) = φ x - φ p := φ.toAffineMap.linearMap_vsub x p
  rw [φ.injective.mem_set_image, ← hdiff,
    φ.linear.injective.mem_set_image]
  exact hlocal hx

/-- Step 1 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"closure of its relative interior" is preserved by an affine placement. -/
private theorem honest_rows_step4_cont_packet_step1_cell_closure
    (e : Cell d) (φ : E d ≃ᵃ[ℝ] E d) :
    closure (relint (φ '' e.carrier)) = φ '' e.carrier := by
  rw [restrictionOp_source_step5_relint_image]
  change closure (φ.toHomeomorphOfFiniteDimensional '' relint e.carrier) = _
  rw [← Homeomorph.image_closure, e.flat.regularClosed]
  rfl

/-- Step 2 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"the local structure is constant" on the connected relative interior of a listed cell. -/
private theorem honest_rows_step4_cont_packet_step2_cell_cone
    {A : PolyManifoldDomain d} (K : CellComplex A) (e f : Cell d)
    (he : e ∈ K.cells) (hf : f ∈ K.cells) (p q : E d)
    (hp : p ∈ relint e.carrier) (hq : q ∈ relint e.carrier) :
    tangentCone f.carrier p = tangentCone f.carrier q := by
  let cone : relint e.carrier → Set (E d) := fun x => tangentCone f.carrier x.val
  have hloc : IsLocallyConstant cone := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    obtain ⟨r, hr, hball⟩ :=
      honest_rows_step4_cont_packet_step2_invariance K e he x x.property f hf
    have hnear : ∀ᶠ y : relint e.carrier in nhds x, (y : E d) ∈ ball (x : E d) r :=
      continuous_subtype_val.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hnear] with y hy
    apply (honest_rows_step4_cont_packet_step2_tangent_germ f.carrier
      (cellDirection e.carrier) x y r hr hy ?_ hball).symm
    exact AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ e.carrier (intrinsicInterior_subset y.property))
      (subset_affineSpan ℝ e.carrier (intrinsicInterior_subset x.property))
  letI : PreconnectedSpace (relint e.carrier) :=
    isPreconnected_iff_preconnectedSpace.mp e.flat.relint_connected.isPreconnected
  exact hloc.apply_eq_of_preconnectedSpace ⟨p, hp⟩ ⟨q, hq⟩

/-- Step 3 of the V4 proof of `honest_rows_step4_cont_packet` (V4 2.8):
"v in relint h" supplies a neighbourhood inside the supporting affine span. -/
private theorem honest_rows_step4_cont_packet_step3_relint_ball
    {K : Set (E d)} {p : E d} (hp : p ∈ relint K) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball p r,
      x ∈ affineSpan ℝ K → x ∈ relint K := by
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp isOpen_interior q hq
  refine ⟨r, hr, ?_⟩
  intro x hx hxaff
  exact ⟨⟨x, hxaff⟩, hb hx, rfl⟩

/-- Step 3 of the V4 proof of `honest_rows_step4_cont_packet` (V4 2.8):
"adjacent to h on the far side of v". A closed edge through an interior
point of another edge has overlapping relative interiors in their common line. -/
private theorem honest_rows_step4_cont_packet_step3_relint_overlap
    {K L : Set (E d)} (hspan : affineSpan ℝ K = affineSpan ℝ L)
    (hreg : closure (relint K) = K) {p : E d} (hpK : p ∈ K) (hpL : p ∈ relint L) :
    (relint K ∩ relint L).Nonempty := by
  obtain ⟨r, hr, hball⟩ := honest_rows_step4_cont_packet_step3_relint_ball hpL
  have hp : p ∈ closure (relint K) := hreg.symm ▸ hpK
  obtain ⟨x, hx, hxp⟩ := Metric.mem_closure_iff.mp hp r hr
  refine ⟨x, hx, hball x (by simpa only [mem_ball, dist_comm] using hxp) ?_⟩
  rw [← hspan]
  exact mem_affineSpan ℝ (intrinsicInterior_subset hx)

/-- Step 3 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"the local structure" determines relative interior in a fixed affine span. -/
private theorem honest_rows_step4_cont_packet_step3_relint_transfer
    {K L V : Set (E d)} (hspan : affineSpan ℝ K = affineSpan ℝ L)
    (hV : IsOpen V) (heq : K ∩ V = L ∩ V) {p : E d}
    (hp : p ∈ relint K) (hpV : p ∈ V) : p ∈ relint L := by
  obtain ⟨q, hq, rfl⟩ := hp
  have hpre : ((↑) ⁻¹' K : Set (affineSpan ℝ K)) ∩ (↑) ⁻¹' V =
      ((↑) ⁻¹' L : Set (affineSpan ℝ K)) ∩ (↑) ⁻¹' V :=
    congrArg (fun X : Set (E d) => (fun x : affineSpan ℝ K => x.val) ⁻¹' X) heq
  have hi := congrArg interior hpre
  rw [interior_inter, interior_inter,
    (hV.preimage continuous_subtype_val).interior_eq] at hi
  have hh : q ∈ interior ((↑) ⁻¹' L : Set (affineSpan ℝ K)) ∩ (↑) ⁻¹' V :=
    hi ▸ ⟨hq, hpV⟩
  rw [relint, intrinsicInterior, ← hspan]
  exact ⟨q, hh.1, rfl⟩

/-- Step 3 of the V4 proof of `honest_rows_step4_cont_packet` (V4 1.0(b)):
"the local structure is constant". Equal local germs of regular closed
cells in one affine span give an overlap of relative interiors. -/
private theorem honest_rows_step4_cont_packet_step3_local_overlap
    {K L V : Set (E d)} (hspan : affineSpan ℝ K = affineSpan ℝ L)
    (hreg : closure (relint K) = K) (hV : IsOpen V) (heq : K ∩ V = L ∩ V)
    {p : E d} (hpK : p ∈ K) (hpV : p ∈ V) :
    (relint K ∩ relint L).Nonempty := by
  have hp : (closure (relint K) ∩ V).Nonempty := ⟨p, hreg.symm ▸ hpK, hpV⟩
  obtain ⟨x, hx, hxV⟩ := (closure_inter_open_nonempty_iff hV).mp hp
  exact ⟨x, hx, honest_rows_step4_cont_packet_step3_relint_transfer hspan hV heq hx hxV⟩

/-- Step 3 of the V4 proof of `honest_rows_step4_cont_packet` (V4 2.8):
"both chains lie in the positioned flag ... with its orientations".
At one consecutive pair of dimensions, equal coface sides extend a relative-interior
intersection of the lower cells to one of the upper cells. -/
private theorem honest_rows_step4_cont_packet_step3_coface_overlap
    {A B : S.ι} (F : FacetFlag S A) (G : FacetFlag S B)
    (φ ψ : E d ≃ᵃ[ℝ] E d) (k : FlagStep d)
    (hlow : (relint (φ '' (F.cell ⟨k.val, k.property.1, by omega⟩).val.carrier) ∩
      relint (ψ '' (G.cell ⟨k.val, k.property.1, by omega⟩).val.carrier)).Nonempty)
    (hspan : affineSpan ℝ
        (φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier) =
      affineSpan ℝ (ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier))
    (hside : φ.linear '' flagSide F k = ψ.linear '' flagSide G k) :
    (relint (φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier) ∩
      relint (ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier)).Nonempty := by
  let i : FlagIndex d := ⟨k.val, k.property.1, by have := k.property.2; omega⟩
  let j : FlagIndex d := ⟨k.val + 1, by omega, k.property.2⟩
  obtain ⟨p, hp, hq⟩ := hlow
  rw [restrictionOp_source_step5_relint_image] at hp hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, hba⟩ := hq
  have hF := honest_rows_step4_cont_packet_step2_cell_cone (S.cx A)
    (F.cell i).val (F.cell j).val (F.cell i).property (F.cell j).property
    a (cellAnchor (F.cell i).val) ha (cellAnchor_mem _)
  have hG := honest_rows_step4_cont_packet_step2_cell_cone (S.cx B)
    (G.cell i).val (G.cell j).val (G.cell i).property (G.cell j).property
    b (cellAnchor (G.cell i).val) hb (cellAnchor_mem _)
  obtain ⟨V, hV, hpV, hVeq⟩ := honest_rows_step4_cont_packet_step1_placed_germ
    (F.cell j).val.flat.polyhedral φ a
  obtain ⟨W, hW, hpW, hWeq⟩ := honest_rows_step4_cont_packet_step1_placed_germ
    (G.cell j).val.flat.polyhedral ψ b
  rw [hF] at hVeq
  rw [hG] at hWeq
  change φ.linear '' tangentCone (F.cell j).val.carrier (cellAnchor (F.cell i).val) =
    ψ.linear '' tangentCone (G.cell j).val.carrier (cellAnchor (G.cell i).val) at hside
  have heq : (φ '' (F.cell j).val.carrier) ∩ (V ∩ W) =
      (ψ '' (G.cell j).val.carrier) ∩ (V ∩ W) := by
    ext x
    constructor
    · rintro ⟨hx, hxV, hxW⟩
      refine ⟨(hWeq x hxW).mpr ?_, hxV, hxW⟩
      rw [hba, ← hside]
      exact (hVeq x hxV).mp hx
    · rintro ⟨hx, hxV, hxW⟩
      refine ⟨(hVeq x hxV).mpr ?_, hxV, hxW⟩
      rw [hside, ← hba]
      exact (hWeq x hxW).mp hx
  exact honest_rows_step4_cont_packet_step3_local_overlap hspan
    (honest_rows_step4_cont_packet_step1_cell_closure _ φ) (hV.inter hW) heq
    ⟨a, F.nested i j (by dsimp [i, j]; omega) (intrinsicInterior_subset ha), rfl⟩
    ⟨hpV, hba ▸ hpW⟩

/-- Step 3 of the V4 proof of `honest_rows_step4_cont_packet` (V4 2.8):
"both chains lie in the positioned flag ... with its orientations".
Induction through the consecutive cofaces carries the edge intersection to the facets. -/
private theorem honest_rows_step4_cont_packet_step3_flag_overlap
    {A B : S.ι} (F : FacetFlag S A) (G : FacetFlag S B)
    (φ ψ : E d ≃ᵃ[ℝ] E d)
    (hspan : ∀ j, affineSpan ℝ (φ '' (F.cell j).val.carrier) =
      affineSpan ℝ (ψ '' (G.cell j).val.carrier))
    (hside : ∀ k, φ.linear '' flagSide F k = ψ.linear '' flagSide G k)
    (p : E d) (hpF : p ∈ φ '' (F.cell edgeIndex).val.carrier)
    (hpG : p ∈ relint (ψ '' (G.cell edgeIndex).val.carrier)) :
    (relint (φ '' (F.cell facetIndex).val.carrier) ∩
      relint (ψ '' (G.cell facetIndex).val.carrier)).Nonempty := by
  have hbase := honest_rows_step4_cont_packet_step3_relint_overlap (hspan edgeIndex)
    (honest_rows_step4_cont_packet_step1_cell_closure _ φ) hpF hpG
  have hall : ∀ (n : ℕ) (hn : 1 ≤ n) (hnd : n < d),
      (relint (φ '' (F.cell ⟨n, hn, hnd⟩).val.carrier) ∩
        relint (ψ '' (G.cell ⟨n, hn, hnd⟩).val.carrier)).Nonempty := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro hnd; exact hbase
    | succ n hn ih =>
      intro hnd
      exact honest_rows_step4_cont_packet_step3_coface_overlap F G φ ψ ⟨n, hn, hnd⟩
        (ih (by omega)) (hspan _) (hside _)
  exact hall (d - 1) facetIndex.property.1 facetIndex.property.2

/-- Step 4 of the V4 proof of `honest_rows_step4_cont_packet` (V4 2.8):
"same ... side". Overlapping facet interiors and equal inward cones force
an overlap of the interiors of the two placed domains. -/
private theorem honest_rows_step4_cont_packet_step4_inward_overlap
    {A B : S.ι} (f : FacetName S A) (g : FacetName S B)
    (φ ψ : E d ≃ᵃ[ℝ] E d)
    (hmeet : (relint (φ '' f.val.carrier) ∩ relint (ψ '' g.val.carrier)).Nonempty)
    (hside : φ.linear '' tangentCone (S.proto A).carrier (cellAnchor f.val) =
      ψ.linear '' tangentCone (S.proto B).carrier (cellAnchor g.val)) :
    (interior (φ '' (S.proto A).carrier) ∩
      interior (ψ '' (S.proto B).carrier)).Nonempty := by
  obtain ⟨p, hp, hq⟩ := hmeet
  rw [restrictionOp_source_step5_relint_image] at hp hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, hba⟩ := hq
  have hF := actualCont_exists_step5_facet_cone A f a (cellAnchor f.val)
    ha (cellAnchor_mem _)
  have hG := actualCont_exists_step5_facet_cone B g b (cellAnchor g.val)
    hb (cellAnchor_mem _)
  obtain ⟨V, hV, hpV, hVeq⟩ := honest_rows_step4_cont_packet_step1_placed_germ
    (S.proto A).polyhedral φ a
  obtain ⟨W, hW, hpW, hWeq⟩ := honest_rows_step4_cont_packet_step1_placed_germ
    (S.proto B).polyhedral ψ b
  rw [hF] at hVeq
  rw [hG] at hWeq
  have hsub : interior (φ '' (S.proto A).carrier) ∩ (V ∩ W) ⊆
      ψ '' (S.proto B).carrier := by
    rintro x ⟨hx, hxV, hxW⟩
    apply (hWeq x hxW).mpr
    rw [hba, ← hside]
    exact (hVeq x hxV).mp (interior_subset hx)
  have hreg : closure (interior (φ '' (S.proto A).carrier)) =
      φ '' (S.proto A).carrier := by
    change closure (interior (φ.toHomeomorphOfFiniteDimensional ''
      (S.proto A).carrier)) = _
    rw [← Homeomorph.image_interior, ← Homeomorph.image_closure,
      (S.proto A).regularClosed]
    rfl
  have hpK : φ a ∈ closure (interior (φ '' (S.proto A).carrier)) := by
    rw [hreg]
    exact ⟨a, actualCont_exists_step5_cell_subset A f.val
      (Finset.mem_filter.mp f.property).1 (intrinsicInterior_subset ha), rfl⟩
  obtain ⟨x, hx, hxV⟩ := (closure_inter_open_nonempty_iff (hV.inter hW)).mp
    ⟨φ a, hpK, hpV, hba ▸ hpW⟩
  exact ⟨x, hx, ((isOpen_interior.inter (hV.inter hW)).subset_interior_iff.mpr hsub)
    ⟨hx, hxV⟩⟩

/-- Step 5 of the V4 proof of `honest_rows_step4_cont_packet` (V4 2.8):
"same serving child H". A native tile whose interior meets a hierarchy node's
interior has that node as its ancestor at the indicated height. -/
private theorem honest_rows_step4_cont_packet_step5_ancestor
    (U : HonestSource S) (q H : U.Node) (hq : q.1 = 0)
    (hmeet : (interior (q.2.val.carrier 0) ∩
      interior (H.2.val.carrier H.1)).Nonempty) :
    U.hierarchy.ancestor q H.1 = H := by
  let A := U.hierarchy.ancestor q H.1
  have hheight : A.1 = H.1 := by
    simpa only [hq, zero_add] using U.hierarchy.ancestor_height q H.1
  have hmem : A.2.val ∈ U.hierarchy.nodes H.1 := by
    simpa only [hheight] using A.2.property
  have hd : q.2.val.IsDescendant 0 A.2.val H.1 := by
    have h := U.hierarchy.ancestor_descendant q H.1
    change q.2.val.IsDescendant q.1 A.2.val A.1 at h
    simpa only [hq, hheight] using h
  have hsub := actualCont_exists_step5_subset A.2.val q.2.val H.1 hd
  obtain ⟨x, hx, hy⟩ := hmeet
  have hframes := U.hierarchy.same_height_disjoint H.1 A.2.val H.2.val
    hmem H.2.property x (interior_mono hsub hx) hy
  have hnodes : (⟨H.1, ⟨A.2.val, hmem⟩⟩ : U.Node) = H := by
    have h : (⟨A.2.val, hmem⟩ : {N // N ∈ U.hierarchy.nodes H.1}) = H.2 :=
      Subtype.ext hframes
    exact congrArg (fun v => (⟨H.1, v⟩ : U.Node)) h
  exact (actualCont_exists_step4_reindex U A H.1 hheight hmem).symm.trans hnodes

/-- Step 5 of the V4 proof of `honest_rows_step4_cont_packet` (V4 2.8):
"the facet f'' of t'' inside g". The aligned flag gives a facet-interior
intersection with the serving facet; its inward side identifies the ancestor,
and hereditary trace then gives containment of the whole continuing facet. -/
private theorem honest_rows_step4_cont_packet_step5_containment
    (U : HonestSource S) (P : Params S) (t q : U.Node) (ht : t.1 = 0) (hq : q.1 = 0)
    (f : FacetName S t.2.val.ty) (g : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault t f) (hg : ¬ U.hierarchy.IsFault q g)
    (c : OrientedChain f) (c' : OrientedChain g)
    (hc : c ∈ U.recordChains P t f hf)
    (halign : ChainsAligned (U.recordOf P t f hf) (U.recordOf P q g hg) c c'
      (q.2.val.frame.trans t.2.val.frame.symm))
    (x : E d) (hxq : x ∈ q.2.val.cell q.1 (c'.chain.val.cell edgeIndex).val)
    (hxt : x ∈ relint (U.providerPlacement P t f hf ''
      ((P.flag (U.recordIncidence P t f hf)).flag.cell edgeIndex).val.carrier)) :
    q.2.val.cell q.1 g.val ⊆ U.hierarchy.providerCarrier t f hf := by
  classical
  let H := U.hierarchy.servingChild t f hf
  obtain ⟨F, a, hF, _, _⟩ := chain_active_owner U P t f hf c hc
  have hct : U.ActiveChain P t f hf c := (Finset.mem_filter.mp hc).2
  have fit (j : FlagIndex d) :
      relint (t.2.val.cell t.1 (c.chain.val.cell j).val) ⊆
        relint (H.2.val.cell H.1 (F.cell j).val) ∧
      affineSpan ℝ (t.2.val.cell t.1 (c.chain.val.cell j).val) =
        affineSpan ℝ (H.2.val.cell H.1 (F.cell j).val) := by
    obtain ⟨hs, hτ, hspan⟩ := hct.1 j
    have hr := (U.hierarchy.stratumMap_spec t f hf (c.chain.val.cell j) hs).1
    rw [hτ, ← hF j] at hr
    rw [← hF j] at hspan
    exact ⟨hr, hspan⟩
  have hlin (y : E d) : t.2.val.frame.linearIsometryEquiv
      ((q.2.val.frame.trans t.2.val.frame.symm).linearIsometryEquiv y) =
        q.2.val.frame.linearIsometryEquiv y := by
    exact t.2.val.frame.linearIsometryEquiv.apply_symm_apply _
  have hspan (j : FlagIndex d) :
      affineSpan ℝ (q.2.val.cell q.1 (c'.chain.val.cell j).val) =
        affineSpan ℝ (H.2.val.cell H.1 (F.cell j).val) := by
    have h := (restrictionOp_source_step4_chains_step2_span t.2.val.frame.toAffineEquiv
      (c.chain.val.cell j).val.carrier
      ((q.2.val.frame.trans t.2.val.frame.symm) ''
        (c'.chain.val.cell j).val.carrier)).mpr (halign.1 j)
    have heq : affineSpan ℝ (q.2.val.cell q.1 (c'.chain.val.cell j).val) =
        affineSpan ℝ (t.2.val.cell t.1 (c.chain.val.cell j).val) := by
      simpa [FramedNode.cell, FramedNode.prototypeFrame, ht, hq, Set.image_image] using h.symm
    exact heq.trans (fit j).2
  have hside (k : FlagStep d) :
      (q.2.val.prototypeFrame q.1).linear '' flagSide c'.chain.val k =
        (H.2.val.prototypeFrame H.1).linear '' flagSide F k := by
    have h := congrArg (t.2.val.frame.linearIsometryEquiv '' ·) (halign.2.1 k)
    have heq : (q.2.val.prototypeFrame q.1).linear '' flagSide c'.chain.val k =
        (t.2.val.prototypeFrame t.1).linear '' flagSide c.chain.val k := by
      simpa [FramedNode.prototypeFrame, ht, hq, Set.image_image, hlin] using h.symm
    exact heq.trans (actualCont_exists_step5_coface_side c.chain.val F
      (t.2.val.prototypeFrame t.1) (H.2.val.prototypeFrame H.1) k
      (fit _).1 (fit _).1 (fit _).2 (fit _).2)
  have hxH : x ∈ relint (H.2.val.cell H.1 (F.cell edgeIndex).val) := by
    rw [hF edgeIndex]
    exact hxt
  have hmeet := honest_rows_step4_cont_packet_step3_flag_overlap c'.chain.val F
    (q.2.val.prototypeFrame q.1) (H.2.val.prototypeFrame H.1) hspan hside x hxq hxH
  let G : FacetName S H.2.val.ty := ⟨(F.cell facetIndex).val,
    Finset.mem_filter.mpr ⟨(F.cell facetIndex).property, F.dimension facetIndex⟩⟩
  have hmeet' : (relint (q.2.val.cell q.1 g.val) ∩
      relint (H.2.val.cell H.1 G.val)).Nonempty := by
    simpa only [c'.chain.property] using hmeet
  have htd : t.2.val.IsDescendant 0 H.2.val H.1 := by
    have h := U.hierarchy.ancestor_descendant t (U.hierarchy.firstProvider t f hf).1
    simpa only [ht] using h
  have hsub := actualCont_exists_step5_subset H.2.val t.2.val H.1 htd
  have hrel : relint (t.2.val.cell t.1 f.val) ⊆ relint (H.2.val.cell H.1 G.val) := by
    simpa only [c.chain.property] using (fit facetIndex).1
  have hin := actualCont_exists_step5_inward f G
    (t.2.val.prototypeFrame t.1) (H.2.val.prototypeFrame H.1)
    (by simpa [FramedNode.carrier, FramedNode.prototypeFrame, placedSet,
      SubstSystem.supertile, Set.image_image, ht] using hsub) hrel
  have hqside : (q.2.val.prototypeFrame q.1).linear ''
      tangentCone (S.proto q.2.val.ty).carrier (cellAnchor g.val) =
        (H.2.val.prototypeFrame H.1).linear ''
          tangentCone (S.proto H.2.val.ty).carrier (cellAnchor G.val) := by
    have h := congrArg (t.2.val.frame.linearIsometryEquiv '' ·) halign.2.2.2
    have heq : (q.2.val.prototypeFrame q.1).linear ''
        tangentCone (S.proto q.2.val.ty).carrier (cellAnchor g.val) =
      (t.2.val.prototypeFrame t.1).linear ''
        tangentCone (S.proto t.2.val.ty).carrier (cellAnchor f.val) := by
      simpa [FramedNode.prototypeFrame, ht, hq, Set.image_image, hlin,
        HonestSource.recordOf] using h.symm
    exact heq.trans hin
  have hinter := honest_rows_step4_cont_packet_step4_inward_overlap g G
    (q.2.val.prototypeFrame q.1) (H.2.val.prototypeFrame H.1) hmeet' hqside
  have ha := honest_rows_step4_cont_packet_step5_ancestor U q H hq
    (by simpa [FramedNode.carrier, FramedNode.prototypeFrame, placedSet,
      SubstSystem.supertile, Set.image_image, hq] using hinter)
  have hd : q.2.val.IsDescendant q.1 H.2.val H.1 := by
    have h := U.hierarchy.ancestor_descendant q H.1
    rw [ha] at h
    exact h
  have hcontained := hereditary_trace H.2.val q.2.val H.1 q.1 hd G.val g.val
    (Finset.mem_filter.mp G.property).1 (Finset.mem_filter.mp g.property).1
    (hmeet'.mono (fun _ h => ⟨h.1, intrinsicInterior_subset h.2⟩))
  have hG : H.2.val.cell H.1 G.val = U.hierarchy.providerCarrier t f hf := by
    change H.2.val.cell H.1 (F.cell facetIndex).val = _
    rw [hF facetIndex, (P.flag (U.recordIncidence P t f hf)).top, record_provider_carrier]
  exact hcontained.trans_eq hG

/-- Step 6 of the V4 proof of `honest_rows_step4_cont_packet` (V4 2.8):
"the packets attached to f,f''" are the facet packets of their actual native tiles. -/
private theorem honest_rows_step4_cont_packet_step6_readout
    (U : HonestSource S) (P : Params S) (t : U.Node) (ht : t.1 = 0)
    (f : FacetName S t.2.val.ty) :
    leafPacket (leafTypeOf U P t ht) f.val = U.facetPacket P t f := by
  unfold leafPacket
  rw [← prePattern_of_leafType U P t ht]
  simp only [prePatternOf, dif_pos f.property]

/-- Step 4 of the V4 proof of `honest_rows` (V4 2.8): "the packets attached to $f,f''$ are
both $\mathcal P(g)$". -/
private theorem honest_rows_step4_cont_packet (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : ContSlot (leafTypeOf U P t ht)) (T : ContTemplate slot)
    (hT : IsActualTemplate U P t ht T.configuration)
    (hc : T.centralChain ∈ slot.record.chains) (ho : T.otherChain ∈ T.record.chains) :
    leafPacket T.label T.record.facet.val = some slot.packet := by
  classical
  rcases slot with ⟨facet, r, hread, htype, hfacet, e, hactive, v, hvf, hterminal,
    htau, packet, hpacket⟩
  obtain ⟨f, hf, hfname, hr⟩ := actualCont_exists_step1_record U P t ht facet.val r hread
  subst r
  rcases T with ⟨θ, hcentral, Q, l, hmem, htiles, hnone, r', hread', htype', c, he,
    c', e', he', v', hinitial, hvertex, halign, hsegment, hjunction⟩
  obtain ⟨q, hq, hQ, hl⟩ := hT.2 (Q, l) hmem
  dsimp only at hQ hl
  subst Q
  subst l
  obtain ⟨g, hg, _, hr'⟩ := actualCont_exists_step1_record U P q hq
    r'.facet.val r' hread'
  subst r'
  have hx := actualCont_exists_step2_vertex U P t f hf v hvf htau
  have hv'e : vertexPoint v' ∈ e'.val.carrier := by
    rw [hinitial, (actualCont_exists_step2_endpoints (U.recordOf P q g hg) e').2]
    exact left_mem_segment ℝ _ _
  have hv : q.2.val.frame (vertexPoint v') = t.2.val.frame (vertexPoint v) := by
    have h := congrArg t.2.val.frame hvertex
    simpa only [FramedNode.move, AffineIsometryEquiv.coe_trans, Function.comp_apply,
      AffineIsometryEquiv.apply_symm_apply] using h
  have hxq : t.2.val.prototypeFrame t.1 (vertexPoint v) ∈
      q.2.val.cell q.1 (c'.chain.val.cell edgeIndex).val := by
    rw [he']
    have h := Set.mem_image_of_mem q.2.val.frame hv'e
    rw [hv] at h
    simpa [FramedNode.cell, FramedNode.prototypeFrame, ht, hq] using h
  have hsub := honest_rows_step4_cont_packet_step5_containment U P t q ht hq
    f g hf hg c c' hc halign _ hxq hx
  have hcarrier : q.2.val.cell q.1 g.val ⊆ (U.providerOccurrence P t f hf).carrier := by
    change q.2.val.cell q.1 g.val ⊆ U.providerPlacement P t f hf ''
      (U.recordIncidence P t f hf).val.leftFacet.val.carrier
    rw [record_provider_carrier]
    exact hsub
  have hattached := (packet_attached U P (U.providerOccurrence P t f hf) q hq g
    hcarrier).2
  rw [← hfname, honest_rows_step4_cont_packet_step6_readout] at hpacket
  simp only [HonestSource.facetPacket, dif_neg hf] at hpacket
  change leafPacket (leafTypeOf U P q hq) g.val = some packet
  rw [honest_rows_step4_cont_packet_step6_readout]
  exact hattached.trans hpacket

/-- Step 1 of the V4 proof of `honest_rows_step5_end_E1` (V4 2.8):
"the actual configuration". The relative frame identifies a native source node,
so an actual configuration assigns that node its own leaf type. -/
private theorem honest_rows_step5_end_E1_step1_label (U : HonestSource S) (P : Params S)
    (t : U.Node) (ht : t.1 = 0) (θ : Template P)
    (hθ : IsActualTemplate U P t ht θ) (q : U.Node) (hq : q.1 = 0)
    (u : LeafType P) (hu : (q.2.val.move t.2.val.frame.symm, u) ∈ θ.tiles) :
    u = leafTypeOf U P q hq := by
  obtain ⟨q', hq', hframe, hlabel⟩ := hθ.2 _ hu
  have hnode : q.2.val = q'.2.val := by
    apply FramedNode.ext
    · have hty := congrArg FramedNode.ty hframe
      exact hty
    · ext x : 1
      have hx := congrArg (fun N : FramedNode S => N.frame x) hframe
      exact t.2.val.frame.symm.injective hx
  have heq : q = q' := by
    rcases q with ⟨n, N, hN⟩
    rcases q' with ⟨m, M, hM⟩
    dsimp only at hq hq' hnode
    subst n
    subst m
    cases hnode
    rfl
  subst q'
  exact hlabel

/-- Step 2 of the V4 proof of `honest_rows_step5_end_E1` (V4 2.8):
"ports on boundary facets of P carry the restrictions of P's records".
The central facet's actual packet has the state of its birth parent as its head. -/
private theorem honest_rows_step5_end_E1_step2_head (U : HonestSource S) (P : Params S)
    (t : U.Node) (ht : t.1 = 0) (slot : EndSlot (leafTypeOf U P t ht))
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (hfv : f.val = slot.facet.val) :
    slot.packet.head = stateOf U P (U.hierarchy.birthParent t f hf) := by
  have hp := slot.packet_eq
  rw [← hfv] at hp
  unfold leafPacket at hp
  rw [← prePattern_of_leafType U P t ht] at hp
  simp only [prePatternOf, dif_pos f.property, HonestSource.facetPacket, dif_neg hf] at hp
  rw [← Option.some.inj hp]
  exact packet_head U P (U.providerOccurrence P t f hf)

/-- Step 3 of the V4 proof of `honest_rows_step5_end_E1` (V4 1.7(c)):
"ports on boundary facets of P carry the restrictions of P's records ...
NULL if P's record is NULL". A contained descendant facet follows its named
restriction path, including the persistent-fault case. -/
private theorem honest_rows_step5_end_E1_step3_boundary (U : HonestSource S)
    (P : Params S) (B q : U.Node) (F : FacetName S B.2.val.ty)
    (g : FacetName S q.2.val.ty) (path : List (RestrictionStep S))
    (hp : SourceRestrictionPath U B q F g path)
    (hsub : q.2.val.cell q.1 g.val ⊆ B.2.val.cell B.1 F.val) :
    match U.facetRecordOf P B F with
    | none => U.facetRecordOf P q g = none
    | some r => U.facetRecordOf P q g = some (restrictionOp path r) := by
  classical
  by_cases hF : U.hierarchy.IsFault B F
  · have hg : U.hierarchy.IsFault q g := by
      intro k
      apply (U.hierarchy.boundaryOffsets_downward q g).2 k (B.1 - q.1 + k) (by omega)
      change q.2.val.cell q.1 g.val ⊆
        frontier ((U.hierarchy.ancestor q (B.1 - q.1 + k)).2.val.carrier
          (U.hierarchy.ancestor q (B.1 - q.1 + k)).1)
      rw [← U.hierarchy.ancestor_add, hp.2.1]
      exact hsub.trans (hF k)
    simp only [HonestSource.facetRecordOf, dif_pos hF, dif_pos hg]
  · obtain ⟨hg, _, _⟩ :=
      U.hierarchy.provider_inherited B q (B.1 - q.1) hp.2.1 F g hF hsub
    simp only [HonestSource.facetRecordOf, dif_neg hF, dif_neg hg]
    exact congrArg some (restrictionOp_source U P B q F g hF hg path hp).symm

/-- Step 5 of the V4 proof of `honest_rows` (V4 2.8): "(E1): the ports on first-generation
facets of $P$ have finite records with the incidence of their facet and the dictated side
(Lemma 1.5(b), Lemma 1.7), $\tau(\{v\})=\{p\}$ ... and $\beta=(b-1)\bmod L$ for all of
them; ports on boundary facets of $P$ carry the restrictions of $P$'s records (Lemma 1.7(c)),
NULL if $P$'s record is NULL." -/
private theorem honest_rows_step5_end_E1 (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : EndSlot (leafTypeOf U P t ht)) (T : EndTemplate slot)
    (hT : IsActualTemplate U P t ht T.configuration)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (hfv : f.val = slot.facet.val)
    (hvv : v.val = slot.vertex.val)
    (hreal : EndGeometryRealizes U P t f hf v T.geometry) :
    endRow_E1 T := by
  have hrecord : U.recordOf P t f hf = slot.record := by
    have hr := slot.record_eq
    rw [← hfv, actualCont_exists_step1_readout U P t ht f] at hr
    simpa only [HonestSource.facetRecordOf, dif_neg hf, Option.some.injEq] using hr
  constructor
  · intro a ha u hu
    obtain ⟨q, hq, g, hg, w, hw, _, hbirth, htile, hfacet, hvertex, hi, hs, hτ⟩ :=
      (hreal.2.2.2.2.1 a).mp ha
    have howned : q ∈ ownedStarSet U (U.hierarchy.birthParent t f hf)
        (t.2.val.prototypeFrame t.1 (vertexPoint v)) := by
      simpa only [ownedStar, Set.Finite.mem_toFinset] using hq
    have hlabel : u = leafTypeOf U P q howned.1 :=
      honest_rows_step5_end_E1_step1_label U P t ht T.configuration hT q howned.1 u
        (by simpa only [htile] using hu)
    refine ⟨U.recordOf P q g hg, ?_, hi.symm, ?_, ?_, ?_⟩
    · rw [hlabel, hfacet, actualCont_exists_step1_readout U P q howned.1 g]
      simp only [HonestSource.facetRecordOf, dif_neg hg]
    · rw [a.side_eq, hi, hs]
      rfl
    · rw [hvertex]
      have hvc : w.val ∈ (S.cx q.2.val.ty).cells := (vertexCell w).property
      simp only [FacetRecord.tauAt, HonestSource.recordOf, dif_pos hvc, dif_pos hw]
      exact congrArg some hτ.symm
    · rw [← hrecord]
      apply Fin.ext
      change (U.hierarchy.servingChild q g hg).1 % P.L =
        (U.hierarchy.servingChild t f hf).1 % P.L
      have hh := congrArg (fun B : U.Node => B.1) hbirth
      change (U.hierarchy.servingChild q g hg).1 + 1 =
        (U.hierarchy.servingChild t f hf).1 + 1 at hh
      exact congrArg (· % P.L) (Nat.add_right_cancel hh)
  · intro a ha u hu
    obtain ⟨q, hq, F, g, w, _, _, hsub, htile, hfacet, _, hparent, path, hp, hop⟩ :=
      (hreal.2.2.2.2.2 a).mp ha
    have howned : q ∈ ownedStarSet U (U.hierarchy.birthParent t f hf)
        (t.2.val.prototypeFrame t.1 (vertexPoint v)) := by
      simpa only [ownedStar, Set.Finite.mem_toFinset] using hq
    have hlabel : u = leafTypeOf U P q howned.1 :=
      honest_rows_step5_end_E1_step1_label U P t ht T.configuration hT q howned.1 u
        (by simpa only [htile] using hu)
    rw [honest_rows_step5_end_E1_step2_head U P t ht slot f hf hfv,
      hparent, hlabel, hfacet, actualCont_exists_step1_readout U P q howned.1 g, hop]
    simpa only [stateRecordAt, stateOf, dif_pos F.property] using
      honest_rows_step5_end_E1_step3_boundary U P (U.hierarchy.birthParent t f hf)
        q F g path hp hsub

/-- Step 1 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"the actual star". A positioned native node has a unique actual leaf label. -/
private theorem honest_rows_step6_end_E2_step1_label (U : HonestSource S) (P : Params S)
    (t : U.Node) (ht : t.1 = 0) (θ : Template P) (hθ : IsActualTemplate U P t ht θ)
    (q : U.Node) (hq : q.1 = 0) (u : LeafType P)
    (hu : (q.2.val.move t.2.val.frame.symm, u) ∈ θ.tiles) :
    u = leafTypeOf U P q hq := by
  obtain ⟨q', hq', hframe, hlabel⟩ := hθ.2 _ hu
  have hnode : q.2.val = q'.2.val := by
    apply FramedNode.ext
    · simpa only [FramedNode.move] using
        congrArg (fun N : FramedNode S => N.ty) hframe
    · ext x : 1
      exact t.2.val.frame.symm.injective
        (congrArg (fun N : FramedNode S => N.frame x) hframe)
  have heq : q = q' := by
    rcases q with ⟨n, Q, hQ⟩
    rcases q' with ⟨n', Q', hQ'⟩
    dsimp only at hq hq' hnode
    subst n
    subst n'
    cases hnode
    rfl
  subst q'
  exact hlabel

/-- Step 1 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.6(c)):
"we attach P(g) to f_t". The packet readout of an actual leaf is its source packet. -/
private theorem honest_rows_step6_end_E2_step1_packet_readout
    (U : HonestSource S) (P : Params S) (q : U.Node) (hq : q.1 = 0)
    (g : FacetName S q.2.val.ty) :
    leafPacket (leafTypeOf U P q hq) g.val = U.facetPacket P q g := by
  unfold leafPacket
  rw [← prePattern_of_leafType U P q hq]
  simp only [prePatternOf, dif_pos g.property]

/-- Step 1 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"the actual star is the complete P-owned star". A labelled primitive port
recovers its native source node, its actual record, and its birth parent. -/
private theorem honest_rows_step6_end_E2_step1_source (U : HonestSource S) (P : Params S)
    (t : U.Node) (ht : t.1 = 0) (θ : Template P) (hθ : IsActualTemplate U P t ht θ)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (Z : EndGeometry P)
    (hZ : EndGeometryRealizes U P t f hf v Z)
    (a : PrimitivePort P) (ha : a ∈ Z.primitivePorts)
    (u : LeafType P) (hu : (a.tile, u) ∈ θ.tiles) :
    ∃ (q : U.Node) (hq : q.1 = 0) (g : FacetName S q.2.val.ty)
      (hg : ¬ U.hierarchy.IsFault q g),
      a.tile = q.2.val.move t.2.val.frame.symm ∧ a.facet.val = g.val ∧
      u = leafTypeOf U P q hq ∧ a.incidence = U.recordIncidence P q g hg ∧
      U.hierarchy.birthParent q g hg = U.hierarchy.birthParent t f hf := by
  obtain ⟨q, hq, g, hg, w, hw, hx, hb, hatile, haf, hav, hai, has, haτ⟩ :=
    (hZ.2.2.2.2.1 a).mp ha
  have hqset : q ∈ ownedStarSet U (U.hierarchy.birthParent t f hf)
      (t.2.val.prototypeFrame t.1 (vertexPoint v)) := by
    simpa only [ownedStar, Set.Finite.mem_toFinset] using hq
  refine ⟨q, hqset.1, g, hg, hatile, haf, ?_, hai, hb⟩
  apply honest_rows_step6_end_E2_step1_label U P t ht θ hθ q hqset.1 u
  simpa only [← hatile] using hu

/-- Step 2 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.6(c)):
"all ports on one first-generation facet carry its unique packet".
Equal birth nodes and canonical incidences identify the entire provider occurrence. -/
private theorem honest_rows_step6_end_E2_step2_packet (U : HonestSource S) (P : Params S)
    (q q' : U.Node) (g : FacetName S q.2.val.ty) (g' : FacetName S q'.2.val.ty)
    (hg : ¬ U.hierarchy.IsFault q g) (hg' : ¬ U.hierarchy.IsFault q' g')
    (hb : U.hierarchy.birthParent q g hg = U.hierarchy.birthParent q' g' hg')
    (hi : U.recordIncidence P q g hg = U.recordIncidence P q' g' hg') :
    U.facetPacket P q g = U.facetPacket P q' g' := by
  have hp : U.providerOccurrence P q g hg = U.providerOccurrence P q' g' hg' := by
    have ext_occ (a b : PrimitiveOccurrence U P) (hb : a.birth = b.birth)
        (hi : a.incidence = b.incidence) : a = b := by
      cases a
      cases b
      dsimp only at hb hi
      subst_vars
      rfl
    exact ext_occ _ _ hb hi
  simp only [HonestSource.facetPacket, dif_neg hg, dif_neg hg', hp]

open private tangentCone_polyhedral_step2_halfspace_presentation
  tangentCone_polyhedral_step3_local_cone tangentCone_polyhedral_step5_radial_germ
  from Enforce.Geometry.Polyhedral in
open scoped Topology in

/-- Step 3 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"the tangent cones". A finite polyhedron agrees locally with its radial cone. -/
private theorem honest_rows_step6_end_E2_step3_local_cone
    {K : Set (E d)} (hK : Polyhedron K) (x : E d) :
    ∀ᶠ y in 𝓝 x, y ∈ K ↔ y - x ∈ tangentCone K x := by
  obtain ⟨s, hs⟩ := tangentCone_polyhedral_step2_halfspace_presentation hK
  obtain ⟨C, hC, hloc⟩ := tangentCone_polyhedral_step3_local_cone s x
  rw [← hs] at hloc
  rwa [tangentCone_polyhedral_step5_radial_germ x hC hloc]

/-- Step 3 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"aff s_j = aff F_j". At a point of a regular closed polyhedron,
its translated tangent cone has the same affine span. -/
private theorem honest_rows_step6_end_E2_step3_cone_span
    {K : Set (E d)} (hK : Polyhedron K) (hreg : closure (relint K) = K)
    (x : E d) (hx : x ∈ K) :
    affineSpan ℝ ((fun u => x + u) '' tangentCone K x) = affineSpan ℝ K := by
  let A := affineSpan ℝ K
  let T := (fun u => x + u) '' tangentCone K x
  have hxA : x ∈ A := subset_affineSpan ℝ K hx
  have hle : affineSpan ℝ T ≤ A := by
    apply affineSpan_le.mpr
    rintro z ⟨u, ⟨ε, hε, hu⟩, rfl⟩
    let t := ε / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have hz : x + t • u ∈ A := subset_affineSpan ℝ K
      (hu t ht (by dsimp [t]; linarith))
    have hh := A.smul_vsub_vadd_mem t⁻¹ hz hxA hxA
    have he : t⁻¹ • ((x + t • u) - x) + x = x + u := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      module
    change x + u ∈ A
    rw [← he]
    exact hh
  obtain ⟨r, hr, hlocal⟩ := Metric.eventually_nhds_iff.mp
    (honest_rows_step6_end_E2_step3_local_cone hK x)
  have hxcl : x ∈ closure (relint K) := hreg.symm ▸ hx
  obtain ⟨y, hyr, hy⟩ := mem_closure_iff.mp hxcl (ball x r) isOpen_ball (by simp [hr])
  letI : Nonempty A := ⟨⟨x, hxA⟩⟩
  let V : Set A := interior ((↑) ⁻¹' K : Set A) ∩ ((↑) ⁻¹' ball x r)
  have hV : IsOpen V := isOpen_interior.inter (isOpen_ball.preimage continuous_subtype_val)
  have hVne : V.Nonempty := by
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hz, hyr⟩
  have hVT : A.subtype '' V ⊆ T := by
    rintro z ⟨w, hw, rfl⟩
    have hm : (w : E d) ∈ K :=
      interior_subset (s := ((↑) ⁻¹' K : Set A)) hw.1
    exact ⟨w.val - x, (hlocal hw.2).mp hm, by simp⟩
  have hfull : affineSpan ℝ (A.subtype '' V) = A := by
    rw [← AffineSubspace.map_span, hV.affineSpan_eq_top hVne]
    ext z
    constructor
    · rintro ⟨w, _, rfl⟩
      exact w.property
    · intro hz
      exact ⟨⟨z, hz⟩, by trivial, rfl⟩
  apply le_antisymm hle
  rw [← hfull]
  exact affineSpan_mono ℝ hVT

open scoped Topology in
/-- Step 3 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"has points of relint s_j near v inside relint F_j".
Equal spans and inclusion of polyhedral tangent cones give an interior intersection. -/
private theorem honest_rows_step6_end_E2_step3_overlap
    {K L : Set (E d)} (hK : Polyhedron K) (hL : Polyhedron L)
    (hreg : closure (relint K) = K) (x : E d) (hx : x ∈ K)
    (hspan : affineSpan ℝ K = affineSpan ℝ L)
    (hcone : tangentCone K x ⊆ tangentCone L x) :
    (relint K ∩ relint L).Nonempty := by
  have hlocal : ∀ᶠ y in 𝓝 x, y ∈ K → y ∈ L := by
    filter_upwards [honest_rows_step6_end_E2_step3_local_cone hK x,
      honest_rows_step6_end_E2_step3_local_cone hL x] with y hyK hyL hy
    exact hyL.mpr (hcone (hyK.mp hy))
  obtain ⟨r, hr, hlocal⟩ := Metric.eventually_nhds_iff.mp hlocal
  have hxcl : x ∈ closure (relint K) := hreg.symm ▸ hx
  obtain ⟨y, hyr, hy⟩ := mem_closure_iff.mp hxcl (ball x r) isOpen_ball (by simp [hr])
  refine ⟨y, hy, ?_⟩
  obtain ⟨z, hz, rfl⟩ := hy
  unfold relint intrinsicInterior
  rw [← hspan]
  refine ⟨z, mem_interior_iff_mem_nhds.mpr ?_, rfl⟩
  have hball : ((↑) ⁻¹' ball x r : Set (affineSpan ℝ K)) ∈ 𝓝 z :=
    (isOpen_ball.preimage continuous_subtype_val).mem_nhds hyr
  apply Filter.mem_of_superset (Filter.inter_mem (mem_interior_iff_mem_nhds.mp hz) hball)
  rintro w ⟨hw, hwr⟩
  exact hlocal hwr hw

open private states_finite_step4_polyhedron_image from Enforce.State.State in
/-- Step 3 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"a chain of cells". Placed cells retain polyhedrality and regular closedness. -/
private theorem honest_rows_step6_end_E2_step3_placed_cell
    (φ : E d ≃ᵃ[ℝ] E d) (e : Cell d) :
    Polyhedron (φ '' e.carrier) ∧
      closure (relint (φ '' e.carrier)) = φ '' e.carrier := by
  refine ⟨states_finite_step4_polyhedron_image φ e.flat.polyhedral, ?_⟩
  rw [restrictionOp_source_step5_relint_image]
  change closure (φ.toHomeomorphOfFiniteDimensional '' relint e.carrier) = _
  rw [← Homeomorph.image_closure, e.flat.regularClosed]
  rfl

/-- Step 3 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"tau(s_j) = F_j with equal affine spans". The tangent test for one listed
cell identifies its canonical provider stratum, in any common affine frame. -/
private theorem honest_rows_step6_end_E2_step3_stratum
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g)
    (e : CellsInFacet q.2.val.ty g)
    (F : ProviderCell (U.recordIncidence P q g hg).val)
    (φ : E d ≃ᵃ[ℝ] E d) (x : E d)
    (hx : x ∈ φ '' q.2.val.cell q.1 e.val.val)
    (hF : x ∈ φ '' (U.providerPlacement P q g hg '' F.val.val.carrier))
    (hspan : affineSpan ℝ (φ '' q.2.val.cell q.1 e.val.val) =
      affineSpan ℝ ((fun u => x + u) ''
        tangentCone (φ '' (U.providerPlacement P q g hg '' F.val.val.carrier)) x))
    (hcone : tangentCone (φ '' q.2.val.cell q.1 e.val.val) x ⊆
      tangentCone (φ '' (U.providerPlacement P q g hg '' F.val.val.carrier)) x) :
    (U.recordTau P q g hg e).val.val = F.val.val ∧
      affineSpan ℝ (φ '' q.2.val.cell q.1 e.val.val) =
        affineSpan ℝ (φ '' (U.providerPlacement P q g hg '' F.val.val.carrier)) := by
  let ψ := (U.providerPlacement P q g hg).trans φ
  have hK : Polyhedron (φ '' q.2.val.cell q.1 e.val.val) ∧
    closure (relint (φ '' q.2.val.cell q.1 e.val.val)) =
      φ '' q.2.val.cell q.1 e.val.val := by
    simpa only [FramedNode.cell, Set.image_image, AffineEquiv.coe_trans] using
      honest_rows_step6_end_E2_step3_placed_cell
        ((q.2.val.prototypeFrame q.1).trans φ) e.val.val
  have hL : Polyhedron (φ '' (U.providerPlacement P q g hg '' F.val.val.carrier)) ∧
      closure (relint (φ '' (U.providerPlacement P q g hg '' F.val.val.carrier))) =
        φ '' (U.providerPlacement P q g hg '' F.val.val.carrier) := by
    simpa only [Set.image_image, AffineEquiv.coe_trans] using
      honest_rows_step6_end_E2_step3_placed_cell ψ F.val.val
  have hspan' := hspan.trans
    (honest_rows_step6_end_E2_step3_cone_span hL.1 hL.2 x hF)
  refine ⟨?_, hspan'⟩
  obtain ⟨y, hy, hyF⟩ := honest_rows_step6_end_E2_step3_overlap
    hK.1 hL.1 hK.2 x hx hspan' hcone
  have hrel := (U.hierarchy.stratumMap_spec q g hg e.val
    (U.cellInFacet_placed q g e)).1
  rw [← record_tau_spec U P q g hg e] at hrel
  have hyτ : y ∈ relint (ψ '' (U.recordTau P q g hg e).val.val.carrier) := by
    rw [restrictionOp_source_step5_relint_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hz' := hrel hz
    rw [restrictionOp_source_step5_relint_image] at hz'
    obtain ⟨w, hw, rfl⟩ := hz'
    rw [restrictionOp_source_step5_relint_image]
    exact ⟨w, hw, rfl⟩
  by_contra hne
  have hdis := (S.cx (S.child (U.recordIncidence P q g hg).val.ty
    (U.recordIncidence P q g hg).val.left).ty).relint_disjoint
    _ (U.recordTau P q g hg e).val.property _ F.val.property hne
  have hdis' := (Set.disjoint_image_iff ψ.injective).mpr hdis
  rw [restrictionOp_source_step5_relint_image] at hyτ
  have hyF' : y ∈ relint (ψ '' F.val.val.carrier) := by
    simpa only [ψ, Set.image_image, AffineEquiv.coe_trans] using hyF
  rw [restrictionOp_source_step5_relint_image] at hyF'
  exact Set.disjoint_left.mp hdis' hyτ hyF'

/-- Step 4 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"the orientations transported from the flag". A present header entry gives
the actual flag cones, sides and endpoint in the central native frame. -/
private theorem honest_rows_step6_end_E2_step4_header (U : HonestSource S) (P : Params S)
    (t : U.Node) (ht : t.1 = 0) (f : FacetName S t.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault t f) (v : VertexName S t.2.val.ty)
    (q : U.Node) (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g)
    (hb : U.hierarchy.birthParent q g hg = U.hierarchy.birthParent t f hf)
    (G : State.FlagTangent (d := d))
    (hG : (U.headerOf P t f hf v).flagTangent (U.recordIncidence P q g hg) = some G) :
    let F := P.flag (U.recordIncidence P q g hg)
    let ψ := (U.providerPlacement P q g hg).trans t.2.val.frame.symm.toAffineEquiv
    (vertexPoint v = ψ F.initial ∨ vertexPoint v = ψ F.terminal) ∧
      G.initial = decide (vertexPoint v = ψ F.initial) ∧
      (∀ j, G.cones j = tangentCone (ψ '' (F.flag.cell j).val.carrier) (vertexPoint v)) ∧
      ∀ j, G.sides j = ψ.linear '' flagSide F.flag j := by
  have hplace : P.incidencePlacement (U.hierarchy.birthParent t f hf).2.val
      (U.hierarchy.birthParent t f hf).1 (U.recordIncidence P q g hg) =
        U.providerPlacement P q g hg := by
    change _ = P.incidencePlacement (U.hierarchy.birthParent q g hg).2.val
      (U.hierarchy.birthParent q g hg).1 (U.recordIncidence P q g hg)
    rw [hb]
  have hx : t.2.val.prototypeFrame t.1 (vertexPoint v) =
      t.2.val.frame (vertexPoint v) := by simp [FramedNode.prototypeFrame, ht]
  have hnorm (K : Set (E d)) : U.normalizeCone t K =
      t.2.val.frame.linearIsometryEquiv.symm '' K := by
    simp [HonestSource.normalizeCone, FramedNode.prototypeFrame, ht]
    rfl
  dsimp only [HonestSource.headerOf] at hG
  rw [hplace, hx] at hG
  simp only [hnorm] at hG
  split at hG
  · rename_i hend
    cases Option.some.inj hG
    have he (y : E d) : t.2.val.frame (vertexPoint v) = y ↔
        vertexPoint v = t.2.val.frame.symm y := by
      constructor
      · intro h
        rw [← h]
        simp
      · intro h
        rw [h]
        simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hend.2.imp ((he _).mp) ((he _).mp)
    · simp only [he]
      rfl
    · intro j
      have h := actualCont_exists_step5_tangent_image t.2.val.frame.symm.toAffineEquiv
        (U.providerPlacement P q g hg ''
          ((P.flag (U.recordIncidence P q g hg)).flag.cell j).val.carrier)
        (t.2.val.frame (vertexPoint v))
      simpa [Set.image_image, AffineEquiv.coe_trans] using h.symm
    · intro j
      simp only [OrientedFullFlag.sides_eq, Set.image_image]
      rfl
  · contradiction

/-- Step 4 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"with the orientations transported". A positive multiple of a segment's
direction belongs to its initial tangent ray. -/
private theorem honest_rows_step6_end_E2_step4_ray (p q u : E d) (a : ℝ)
    (ha : 0 < a) (hu : q - p = a • u) : u ∈ tangentCone (segment ℝ p q) p := by
  refine ⟨a, ha, fun t ht hta => ?_⟩
  rw [segment_eq_image']
  refine ⟨t / a, ⟨(div_pos ht ha).le, ((div_lt_one ha).mpr hta).le⟩, ?_⟩
  change p + (t / a) • (q - p) = p + t • u
  rw [hu, smul_smul, div_mul_cancel₀ _ ha.ne']

/-- Step 4 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"the chain is active, with the orientations transported from the flag".
The individual tangent tests identify every stratum; the source table records
the resulting full chain with the unique induced edge orientation. -/
private theorem honest_rows_step6_end_E2_step4_alignment
    (U : HonestSource S) (P : Params S) (q : U.Node) (hq : q.1 = 0)
    (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g)
    (φ : Iso d) (x : E d) (G : State.FlagTangent (d := d))
    (hend : x = φ (U.providerPlacement P q g hg
        (P.flag (U.recordIncidence P q g hg)).initial) ∨
      x = φ (U.providerPlacement P q g hg
        (P.flag (U.recordIncidence P q g hg)).terminal))
    (hinit : G.initial = decide (x = φ (U.providerPlacement P q g hg
      (P.flag (U.recordIncidence P q g hg)).initial)))
    (hcones : ∀ j, G.cones j = tangentCone
      (((U.providerPlacement P q g hg).trans φ.toAffineEquiv) ''
        ((P.flag (U.recordIncidence P q g hg)).flag.cell j).val.carrier) x)
    (hsides : ∀ j, G.sides j =
      ((U.providerPlacement P q g hg).trans φ.toAffineEquiv).linear ''
        flagSide (P.flag (U.recordIncidence P q g hg)).flag j)
    (F : FlagChain g)
    (hfit : ChainFitsTangent (U.recordOf P q g hg) (q.2.val.move φ).frame x F G) :
    ∃ c ∈ (U.recordOf P q g hg).chains, c.chain = F ∧
      OrientationFitsTangent (U.recordOf P q g hg) (q.2.val.move φ).frame c G := by
  classical
  let ι := U.recordIncidence P q g hg
  let H := P.flag ι
  let ψ := (U.providerPlacement P q g hg).trans φ.toAffineEquiv
  have hcell (e : Cell d) : placedSet (q.2.val.move φ).frame e.carrier =
      φ '' q.2.val.cell q.1 e := by
    simp [FramedNode.move, FramedNode.cell, FramedNode.prototypeFrame, hq,
      placedSet, Set.image_image]
  have hpoint (j : FlagIndex d) : x ∈ ψ '' (H.flag.cell j).val.carrier := by
    have hsub := H.flag.nested edgeIndex j j.property.1
    rcases hend with hx | hx
    · refine ⟨H.initial, hsub ?_, hx.symm⟩
      rw [H.edge_eq]
      exact left_mem_segment ℝ _ _
    · refine ⟨H.terminal, hsub ?_, hx.symm⟩
      rw [H.edge_eq]
      exact right_mem_segment ℝ _ _
  have hgeom (j : FlagIndex d) :
      (U.recordTau P q g hg ⟨F.val.cell j,
        FacetRecord.chain_cell_subset (U.recordOf P q g hg) ⟨F, false⟩ j⟩).val.val =
          (H.flag.cell j).val ∧
      affineSpan ℝ (q.2.val.cell q.1 (F.val.cell j).val) =
        affineSpan ℝ (U.providerPlacement P q g hg '' (H.flag.cell j).val.carrier) := by
    let e : CellsInFacet q.2.val.ty g :=
      ⟨F.val.cell j, FacetRecord.chain_cell_subset (U.recordOf P q g hg) ⟨F, false⟩ j⟩
    let Fj : ProviderCell ι.val := ⟨H.flag.cell j, by
      have h := H.flag.nested j facetIndex (by
        change j.val ≤ d - 1
        have := j.property.2
        omega)
      simpa only [H.top] using h⟩
    have hfits := hfit j
    rw [hcell, hcones j] at hfits
    have hp : x ∈ φ.toAffineEquiv ''
        (U.providerPlacement P q g hg '' Fj.val.val.carrier) := by
      simpa only [ψ, Set.image_image, AffineEquiv.coe_trans] using hpoint j
    have hh := honest_rows_step6_end_E2_step3_stratum U P q g hg e Fj
      φ.toAffineEquiv x hfits.1 hp
      (by simpa only [ψ, Set.image_image, AffineEquiv.coe_trans] using hfits.2.1)
      (by simpa only [ψ, Set.image_image, AffineEquiv.coe_trans] using hfits.2.2)
    exact ⟨hh.1, (restrictionOp_source_step4_chains_step2_span φ.toAffineEquiv _ _).mp
      hh.2⟩
  let c : OrientedChain g := ⟨F, decide (0 < inner ℝ (U.counterDirection P q g hg)
    ((q.2.val.prototypeFrame q.1).linear
      (edgeVector (restrictionOp_source_step4_chains_step1_edge F.val))))⟩
  have hactive : U.ActiveChain P q g hg c := by
    refine ⟨?_, ?_⟩
    · intro j
      let e : CellsInFacet q.2.val.ty g :=
        ⟨F.val.cell j, FacetRecord.chain_cell_subset (U.recordOf P q g hg) c j⟩
      refine ⟨U.cellInFacet_placed q g e, ?_, (hgeom j).2⟩
      have hτ := record_tau_spec U P q g hg e
      change U.providerPlacement P q g hg '' (U.recordTau P q g hg e).val.val.carrier = _
        at hτ
      rw [(hgeom j).1] at hτ
      exact hτ.symm
    · exact decide_eq_true_iff
  have hc : c ∈ (U.recordOf P q g hg).chains := by
    exact Finset.mem_filter.mpr ⟨by simp [allOrientedChains], hactive⟩
  refine ⟨c, hc, rfl, ?_, ?_⟩
  · obtain ⟨a, ha, hdir⟩ :=
      ((restrictionOp_source_step4_chains_step1_test U P q g hg c).mp hactive).2
    have hdir' : ψ H.terminal - ψ H.initial =
        a • (q.2.val.move φ).frame.linearIsometryEquiv (chainVector c) := by
      have hh := congrArg φ.linearIsometryEquiv hdir
      have hψ := ψ.toAffineMap.linearMap_vsub H.terminal H.initial
      change ψ.linear H.direction = ψ H.terminal - ψ H.initial at hψ
      rw [← hψ]
      simpa [ψ, H, ι, HonestSource.counterDirection, FramedNode.prototypeFrame,
        hq, FramedNode.move] using hh
    have hseg : ψ '' (H.flag.cell edgeIndex).val.carrier =
        segment ℝ (ψ H.initial) (ψ H.terminal) := by
      rw [H.edge_eq]
      exact image_segment ℝ ψ.toAffineMap _ _
    rw [hcones edgeIndex]
    change (if G.initial then (q.2.val.move φ).frame.linearIsometryEquiv (chainVector c)
      else -(q.2.val.move φ).frame.linearIsometryEquiv (chainVector c)) ∈
        tangentCone (ψ '' (H.flag.cell edgeIndex).val.carrier) x
    rw [hseg]
    change G.initial = decide (x = ψ H.initial) at hinit
    by_cases hx : x = ψ H.initial
    · have hi : G.initial = true := by simpa only [hx, decide_true] using hinit
      simp only [hi, ite_true]
      rw [hx]
      exact honest_rows_step6_end_E2_step4_ray _ _ _ a ha hdir'
    · have hi : G.initial = false := by
        change G.initial = decide (x = ψ H.initial) at hinit
        simpa only [hx, decide_false] using hinit
      have hx' : x = ψ H.terminal := hend.resolve_left hx
      simp only [hi, Bool.false_eq_true, ite_false]
      rw [hx', segment_symm]
      apply honest_rows_step6_end_E2_step4_ray _ _ _ a ha
      rw [← neg_sub, hdir', smul_neg]
  · intro j
    have fit (k : FlagIndex d) :
        relint (q.2.val.cell q.1 (F.val.cell k).val) ⊆
          relint (U.providerPlacement P q g hg '' (H.flag.cell k).val.carrier) := by
      obtain ⟨hs, hτ, _⟩ := hactive.1 k
      change (U.hierarchy.servingChild q g hg).2.val.cell
        (U.hierarchy.servingChild q g hg).1
        (U.hierarchy.stratumMap q g hg (F.val.cell k) hs).val =
          U.providerPlacement P q g hg '' (H.flag.cell k).val.carrier at hτ
      simpa only [hτ] using (U.hierarchy.stratumMap_spec q g hg (F.val.cell k) hs).1
    have hh := actualCont_exists_step5_coface_side F.val H.flag
      (q.2.val.prototypeFrame q.1) (U.providerPlacement P q g hg) j
      (fit _) (fit _) (hgeom _).2 (hgeom _).2
    rw [hsides j]
    have hh' := congrArg (fun K : Set (E d) => φ.linearIsometryEquiv '' K) hh
    simpa [FramedNode.move, FramedNode.prototypeFrame, hq, Set.image_image] using hh'

/-- Step 5 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"all sites lie in relint h". A nondegenerate segment has precisely its
open affine interpolations as its relative interior. -/
private theorem honest_rows_step6_end_E2_step5_segment_relint
    {d : ℕ} (p q : E d) (hpq : p ≠ q) :
    relint (segment ℝ p q) = AffineMap.lineMap p q '' Ioo (0 : ℝ) 1 := by
  let L := ‖q - p‖
  have hL : 0 < L := norm_pos_iff.mpr (sub_ne_zero.mpr hpq.symm)
  let u := L⁻¹ • (q - p)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    exact inv_mul_cancel₀ hL.ne'
  let φ : ℝ →ᵃⁱ[ℝ] E d := {
    toAffineMap := {
      toFun := fun t => t • u + p
      linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight u
      map_vadd' := by
        intro t s
        change (s + t) • u + p = s • u + (t • u + p)
        rw [add_smul, add_assoc] }
    norm_map := by
      intro t
      change ‖t • u‖ = ‖t‖
      rw [norm_smul, hu, mul_one] }
  have hφ0 : φ 0 = p := by change (0 : ℝ) • u + p = p; simp
  have hφL : φ L = q := by
    change L • (L⁻¹ • (q - p)) + p = q
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul, sub_add_cancel]
  have hseg : segment ℝ p q = φ '' Icc 0 L := by
    simpa only [AffineIsometry.coe_toAffineMap, hφ0, hφL, segment_eq_Icc hL.le] using
      (image_segment ℝ φ.toAffineMap 0 L).symm
  have hir : intrinsicInterior ℝ (Icc (0 : ℝ) L) = Ioo 0 L := by
    have hspan : affineSpan ℝ (Icc (0 : ℝ) L) = ⊤ :=
      (convex_Icc 0 L).interior_nonempty_iff_affineSpan_eq_top.mp
        (by rw [interior_Icc]; exact nonempty_Ioo.mpr hL)
    rw [intrinsicInterior, hspan]
    change (Homeomorph.Set.univ ℝ) ''
      interior ((Homeomorph.Set.univ ℝ) ⁻¹' Icc 0 L) = Ioo 0 L
    rw [(Homeomorph.Set.univ ℝ).image_interior]
    simp
  rw [hseg, relint, φ.image_intrinsicInterior, hir]
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t / L, ⟨div_pos ht.1 hL, (div_lt_one hL).mpr ht.2⟩, ?_⟩
    have he := φ.toAffineMap.apply_lineMap (0 : ℝ) L (t / L)
    simpa [AffineMap.lineMap_apply_ring, hφ0, hφL, hL.ne'] using he.symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * L, ⟨mul_pos ht.1 hL, by nlinarith [ht.2]⟩, ?_⟩
    have he := φ.toAffineMap.apply_lineMap (0 : ℝ) L t
    simpa [AffineMap.lineMap_apply_ring, hφ0, hφL] using he

/-- Step 5 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"all sites lie in relint h". This remains true after naming the serving
side in canonical coordinates and placing the provider in the source. -/
private theorem honest_rows_step6_end_E2_step5_sites_relint
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g) (a : Fin P.N) :
    U.sitePoint P q g hg a ∈ relint (U.providerPlacement P q g hg ''
      ((P.flag (U.recordIncidence P q g hg)).flag.cell edgeIndex).val.carrier) := by
  let ι := U.recordIncidence P q g hg
  let b := U.recordSide P q g hg
  have hh := Set.mem_image_of_mem (S.child ι.val.ty (ι.val.sideIndex b)).frame
    (P.sites_relint ι b a)
  change (S.child ι.val.ty (ι.val.sideIndex b)).frame.toAffineEquiv (P.sites ι b a) ∈
    (S.child ι.val.ty (ι.val.sideIndex b)).frame.toAffineEquiv ''
      relint ((P.sideFlag ι b).cell edgeIndex).val.carrier at hh
  rw [← restrictionOp_source_step5_relint_image
    (S.child ι.val.ty (ι.val.sideIndex b)).frame.toAffineEquiv] at hh
  change (S.child ι.val.ty (ι.val.sideIndex b)).frame (P.sites ι b a) ∈
    relint (placedSet (S.child ι.val.ty (ι.val.sideIndex b)).frame
      ((P.sideFlag ι b).cell edgeIndex).val.carrier) at hh
  rw [P.sideFlag_eq] at hh
  rw [show placedSet (S.child ι.val.ty ι.val.left).frame
      ((P.flag ι).flag.cell edgeIndex).val.carrier =
      (S.child ι.val.ty ι.val.left).frame.toAffineEquiv ''
        ((P.flag ι).flag.cell edgeIndex).val.carrier from rfl,
    restrictionOp_source_step5_relint_image] at hh
  obtain ⟨y, hy, hyeq⟩ := hh
  have hy' : y = P.canonicalSite ι b a := by
    apply (S.child ι.val.ty ι.val.left).frame.injective
    simpa only [Params.canonicalSite, AffineIsometryEquiv.apply_symm_apply] using hyeq
  rw [restrictionOp_source_step5_relint_image]
  exact ⟨y, hy, congrArg (U.providerPlacement P q g hg) hy'⟩

/-- Step 5 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"immediately after the initial endpoint ... immediately before the terminal
endpoint". Every site is strictly after the first and strictly before the second. -/
private theorem honest_rows_step6_end_E2_step5_site_signs
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g) (a : Fin P.N) :
    0 < inner ℝ (U.counterDirection P q g hg)
      (U.sitePoint P q g hg a - U.providerPlacement P q g hg
        (P.flag (U.recordIncidence P q g hg)).initial) ∧
    inner ℝ (U.counterDirection P q g hg)
      (U.sitePoint P q g hg a - U.providerPlacement P q g hg
        (P.flag (U.recordIncidence P q g hg)).terminal) < 0 := by
  let F := P.flag (U.recordIncidence P q g hg)
  let ψ := U.providerPlacement P q g hg
  let p := ψ F.initial
  let r := ψ F.terminal
  have hpr : p ≠ r := fun h => F.distinct (ψ.injective h)
  have hdir : U.counterDirection P q g hg = r - p :=
    ψ.toAffineMap.linearMap_vsub F.terminal F.initial
  have hsite := honest_rows_step6_end_E2_step5_sites_relint U P q g hg a
  have hseg : ψ '' (F.flag.cell edgeIndex).val.carrier = segment ℝ p r := by
    rw [F.edge_eq]
    exact image_segment ℝ ψ.toAffineMap _ _
  rw [hseg, honest_rows_step6_end_E2_step5_segment_relint p r hpr] at hsite
  obtain ⟨s, hs, he⟩ := hsite
  have hv : 0 < inner ℝ (r - p) (r - p) :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr hpr.symm)
  have hfirst : U.sitePoint P q g hg a - p = s • (r - p) := by
    rw [← he, AffineMap.lineMap_apply_module']
    module
  have hlast : U.sitePoint P q g hg a - r = (s - 1) • (r - p) := by
    rw [← he, AffineMap.lineMap_apply_module']
    module
  change 0 < inner ℝ (U.counterDirection P q g hg) (_ - p) ∧
    inner ℝ (U.counterDirection P q g hg) (_ - r) < 0
  rw [hdir, hfirst, hlast, real_inner_smul_right, real_inner_smul_right]
  exact ⟨mul_pos hs.1 hv, mul_neg_of_neg_of_pos (sub_neg.mpr hs.2) hv⟩

/-- Step 5 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"the value of kappa". On an active edge, the shallow word and the physical
source coordinates give the same strict and weak order comparisons. -/
private theorem honest_rows_step6_end_E2_step5_word_order
    (P : Params S) (U : HonestSource S) (c : U.Node)
    (f : FacetName S c.2.val.ty) (hf : ¬ U.hierarchy.IsFault c f)
    (e : CellName S c.2.val.ty) (he : (U.recordOf P c f hf).ChainActive e)
    (a : Fin P.N) (x : E d)
    (hx : c.2.val.prototypeFrame c.1 x ∈ affineSpan ℝ (c.2.val.cell c.1 e.val)) :
    (inner ℝ (U.counterDirection P c f hf)
        (U.sitePoint P c f hf a - c.2.val.prototypeFrame c.1 x) < 0 ↔
      inner ℝ (U.recordOf P c f hf).servingDirection
        (P.sites (U.recordIncidence P c f hf) (U.recordSide P c f hf) a -
          wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) x) < 0) ∧
    (inner ℝ (U.counterDirection P c f hf)
        (U.sitePoint P c f hf a - c.2.val.prototypeFrame c.1 x) ≤ 0 ↔
      inner ℝ (U.recordOf P c f hf).servingDirection
        (P.sites (U.recordIncidence P c f hf) (U.recordSide P c f hf) a -
          wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) x) ≤ 0) := by
  classical
  let ι := U.recordIncidence P c f hf
  let b := U.recordSide P c f hf
  let H := U.hierarchy.servingChild c f hf
  let ψ := H.2.val.prototypeFrame H.1
  let R := (S.child ι.val.ty ι.val.left).frame.toAffineEquiv.trans
    (S.child ι.val.ty (ι.val.sideIndex b)).frame.symm.toAffineEquiv
  have hframes : R.trans ψ = U.providerPlacement P c f hf := by
    dsimp only [ψ, H]
    rw [restrictionOp_source_step4_profile_step4_serving_frame P U c f hf]
    apply AffineEquiv.ext
    intro x
    simp [R, rolePlacement, PrimitiveIncidence.sideRole, HonestSource.providerPlacement,
      Params.incidencePlacement, ι, b]
  have hdir : ψ.linear (U.recordOf P c f hf).servingDirection = U.counterDirection P c f hf :=
    congrArg (fun φ : E d ≃ᵃ[ℝ] E d => φ.linear (P.flag ι).direction) hframes
  have hpoint := congrArg (fun φ : E d ≃ᵃ[ℝ] E d => φ x)
    (restrictionOp_source_step4_profile_step3_word_frame U c (U.hierarchy.firstProvider c f hf).1)
  change c.2.val.prototypeFrame c.1 x =
    ψ (wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) x) at hpoint
  have hsite := restrictionOp_source_step4_profile_step4_site_placement P U c f hf a
  have hdiff : ψ.linear (P.sites ι b a -
      wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) x) =
      U.sitePoint P c f hf a - c.2.val.prototypeFrame c.1 x := by
    calc
      _ = ψ (P.sites ι b a) - ψ
          (wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) x) :=
        ψ.toAffineMap.linearMap_vsub _ _
      _ = _ := by rw [← hsite, ← hpoint]
  obtain ⟨t, ht⟩ := restrictionOp_source_step4_profile_step5_site_line P U c f hf e he a _
    hx
  have hscalar : t • (U.recordOf P c f hf).servingDirection =
      P.sites ι b a - wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1)
        x := by
    apply ψ.linear.injective
    rw [map_smul, hdir, hdiff]
    exact ht
  have hlt := restrictionOp_source_step4_profile_step5_linear_order ψ.linear
    (U.recordOf P c f hf).servingDirection _ ⟨t, hscalar⟩
  have hle : inner ℝ (ψ.linear (U.recordOf P c f hf).servingDirection)
      (ψ.linear (P.sites ι b a -
        wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) x)) ≤ 0 ↔
      inner ℝ (U.recordOf P c f hf).servingDirection
        (P.sites ι b a -
          wordPlacement (U.downRoles c (U.hierarchy.firstProvider c f hf).1) x) ≤ 0 := by
    rw [← hscalar, map_smul, real_inner_smul_right, real_inner_smul_right]
    by_cases hu : (U.recordOf P c f hf).servingDirection = 0
    · simp [hu]
    · have hu' : ψ.linear (U.recordOf P c f hf).servingDirection ≠ 0 :=
        ψ.linear.map_ne_zero_iff.mpr hu
      have hp := real_inner_self_pos.mpr hu
      have hp' := real_inner_self_pos.mpr hu'
      constructor
      · intro hh
        exact mul_nonpos_of_nonpos_of_nonneg (nonpos_of_mul_nonpos_left hh hp') hp.le
      · intro hh
        exact mul_nonpos_of_nonpos_of_nonneg (nonpos_of_mul_nonpos_left hh hp) hp'.le
  rw [hdir, hdiff] at hlt hle
  exact ⟨hlt, hle⟩

/-- Step 5 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"which is what kappa-minus and kappa-plus say". Shallow readouts count
physical sites weakly before the first endpoint and strictly before the last. -/
private theorem honest_rows_step6_end_E2_step5_shallow_germs
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g)
    (e : PrototypeEdge S q.2.val.ty)
    (he : (U.recordOf P q g hg).ChainActive (edgeCell e))
    (w : ShortProfile P) (hw : (U.recordOf P q g hg).counter = .inr w) :
    (U.recordOf P q g hg).kappaMinus e =
      (Finset.univ.filter (fun a : Fin P.N => inner ℝ (U.counterDirection P q g hg)
        (U.sitePoint P q g hg a - q.2.val.prototypeFrame q.1
          ((U.recordOf P q g hg).endpoints e).1) ≤ 0)).card ∧
    (U.recordOf P q g hg).kappaPlus e =
      (Finset.univ.filter (fun a : Fin P.N => inner ℝ (U.counterDirection P q g hg)
        (U.sitePoint P q g hg a - q.2.val.prototypeFrame q.1
          ((U.recordOf P q g hg).endpoints e).2) < 0)).card := by
  classical
  have hword : w.word = U.downRoles q (U.hierarchy.firstProvider q g hg).1 := by
    change U.counterProfile P q g hg = .inr w at hw
    unfold HonestSource.counterProfile at hw
    dsimp only at hw
    split at hw
    · cases Sum.inr.inj hw
      rfl
    · contradiction
  have hends := actualCont_exists_step2_endpoints (U.recordOf P q g hg) e
  have horder (a : Fin P.N) (x : E d) (hx : x ∈ e.val.carrier) :=
    honest_rows_step6_end_E2_step5_word_order P U q g hg (edgeCell e) he a x
      (mem_affineSpan ℝ (Set.mem_image_of_mem _ hx))
  constructor
  · rw [FacetRecord.kappaMinus, hw]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro a _
    simpa only [hword] using (horder a _
      (hends.2.symm ▸ left_mem_segment ℝ _ _)).2.symm
  · rw [FacetRecord.kappaPlus, hw]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro a _
    simpa only [hword] using (horder a _
      (hends.2.symm ▸ right_mem_segment ℝ _ _)).1.symm

open scoped Topology in
/-- Step 5 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"immediately after ... immediately before". At maturity the constant on
an active edge equals the count near any incident point away from all sites. -/
private theorem honest_rows_step6_end_E2_step5_mature_endpoint
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g)
    (e : PrototypeEdge S q.2.val.ty)
    (he : (U.recordOf P q g hg).ChainActive (edgeCell e))
    (hm : P.siteDepth (U.recordIncidence P q g hg) (U.recordSide P q g hg) ≤
      (U.hierarchy.firstProvider q g hg).1)
    (x : E d) (hx : x ∈ q.2.val.cell q.1 e.val) (initial : Bool)
    (hsite : ∀ a : Fin P.N, if initial then
      0 < inner ℝ (U.counterDirection P q g hg) (U.sitePoint P q g hg a - x) else
      inner ℝ (U.counterDirection P q g hg) (U.sitePoint P q g hg a - x) < 0) :
    (U.recordOf P q g hg).kappaMinus e = (if initial then 0 else P.N) ∧
      (U.recordOf P q g hg).kappaPlus e = (if initial then 0 else P.N) := by
  classical
  have hnear : ∀ᶠ y in 𝓝 x, ∀ a : Fin P.N, if initial then
      0 < inner ℝ (U.counterDirection P q g hg) (U.sitePoint P q g hg a - y) else
      inner ℝ (U.counterDirection P q g hg) (U.sitePoint P q g hg a - y) < 0 := by
    apply Filter.eventually_all.mpr
    intro a
    have hc : Continuous (fun y : E d => inner ℝ (U.counterDirection P q g hg)
        (U.sitePoint P q g hg a - y)) := by fun_prop
    cases initial with
    | false => exact hc.continuousAt.eventually_lt_const (hsite a)
    | true => exact hc.continuousAt.eventually_const_lt (hsite a)
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
  have hxcl : x ∈ closure (relint (q.2.val.cell q.1 e.val)) := by
    rw [restrictionOp_source_step5_cell_closure]
    exact hx
  obtain ⟨y, hyr, hy⟩ := mem_closure_iff.mp hxcl (ball x r) isOpen_ball (by simp [hr])
  have hsign := hnear hyr
  have hcount : (U.sitesBefore P q g hg y).val = (if initial then 0 else P.N) := by
    cases initial with
    | false =>
      have hfilter : Finset.univ.filter (fun a : Fin P.N =>
          inner ℝ (U.counterDirection P q g hg) (U.sitePoint P q g hg a - y) < 0) =
          Finset.univ := Finset.filter_eq_self.mpr (fun a _ => hsign a)
      simp only [HonestSource.sitesBefore, hfilter, Finset.card_univ, Fintype.card_fin]
      rfl
    | true =>
      have hfilter : Finset.univ.filter (fun a : Fin P.N =>
          inner ℝ (U.counterDirection P q g hg) (U.sitePoint P q g hg a - y) < 0) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro a _
        exact not_lt_of_ge (hsign a).le
      simp only [HonestSource.sitesBefore, hfilter, Finset.card_empty]
      rfl
  have hv := mature_counter_value U P q g hg hm (edgeCell e) he y hy
  have hcounter := (record_mature_iff U P q g hg).mpr hm
  constructor
  · simpa [FacetRecord.kappaMinus, hcounter, hv] using hcount
  · simpa [FacetRecord.kappaPlus, hcounter, hv] using hcount

/-- Step 5 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"kappa-minus(e) = 0, respectively kappa-plus(e) = N". An active edge
beginning or ending at the corresponding flag endpoint has the required germ. -/
private theorem honest_rows_step6_end_E2_step5_endpoint_counts
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g)
    (e : PrototypeEdge S q.2.val.ty)
    (he : (U.recordOf P q g hg).ChainActive (edgeCell e)) :
    (q.2.val.prototypeFrame q.1 ((U.recordOf P q g hg).endpoints e).1 =
        U.providerPlacement P q g hg (P.flag (U.recordIncidence P q g hg)).initial →
      (U.recordOf P q g hg).kappaMinus e = 0) ∧
    (q.2.val.prototypeFrame q.1 ((U.recordOf P q g hg).endpoints e).2 =
        U.providerPlacement P q g hg (P.flag (U.recordIncidence P q g hg)).terminal →
      (U.recordOf P q g hg).kappaPlus e = P.N) := by
  classical
  have hends := actualCont_exists_step2_endpoints (U.recordOf P q g hg) e
  by_cases hm : P.siteDepth (U.recordIncidence P q g hg) (U.recordSide P q g hg) ≤
      (U.hierarchy.firstProvider q g hg).1
  · constructor
    · intro hstart
      apply (honest_rows_step6_end_E2_step5_mature_endpoint U P q g hg e he hm
        _ (Set.mem_image_of_mem _ (hends.2.symm ▸ left_mem_segment ℝ _ _)) true ?_).1
      intro a
      simpa only [hstart] using (honest_rows_step6_end_E2_step5_site_signs U P q g hg a).1
    · intro hend
      apply (honest_rows_step6_end_E2_step5_mature_endpoint U P q g hg e he hm
        _ (Set.mem_image_of_mem _ (hends.2.symm ▸ right_mem_segment ℝ _ _)) false ?_).2
      intro a
      simpa only [hend] using (honest_rows_step6_end_E2_step5_site_signs U P q g hg a).2
  · obtain ⟨w, hw, _⟩ := (record_shallow_iff U P q g hg).mpr (lt_of_not_ge hm)
    have hread := honest_rows_step6_end_E2_step5_shallow_germs U P q g hg e he w hw
    constructor
    · intro hstart
      rw [hread.1]
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro a _
      rw [hstart]
      exact not_le_of_gt (honest_rows_step6_end_E2_step5_site_signs U P q g hg a).1
    · intro hend
      rw [hread.2]
      have hfilter : Finset.univ.filter (fun a : Fin P.N =>
          inner ℝ (U.counterDirection P q g hg) (U.sitePoint P q g hg a -
            q.2.val.prototypeFrame q.1 ((U.recordOf P q g hg).endpoints e).2) < 0) =
          Finset.univ := by
        apply Finset.filter_eq_self.mpr
        intro a _
        rw [hend]
        exact (honest_rows_step6_end_E2_step5_site_signs U P q g hg a).2
      rw [hfilter, Finset.card_univ, Fintype.card_fin]

/-- Step 6 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"a chain-active edge at the endpoint". Positive orientation identifies
the first endpoint of a subsegment that contains the first endpoint of its parent. -/
private theorem honest_rows_step6_end_E2_step6_first_endpoint
    (p q a b : E d) (ha : a ∈ segment ℝ p q) (hp : p ∈ segment ℝ a b)
    (hpos : 0 < inner ℝ (q - p) (b - a)) : a = p := by
  rw [segment_eq_image'] at ha hp
  obtain ⟨r, hr, he⟩ := ha
  obtain ⟨s, hs, hp⟩ := hp
  have hn : 0 ≤ inner ℝ (q - p) (a - p) := by
    rw [← he]
    simp only [add_sub_cancel_left, real_inner_smul_right]
    exact mul_nonneg hr.1 real_inner_self_nonneg
  have hdiff : a - p = (-s) • (b - a) := by
    rw [← hp]
    module
  rw [hdiff, real_inner_smul_right] at hn
  have hs0 : s = 0 := by
    have hle : s * inner ℝ (q - p) (b - a) ≤ 0 := by nlinarith
    exact le_antisymm (nonpos_of_mul_nonpos_left hle hpos) hs.1
  simpa only [hs0, zero_smul, add_zero] using hp

/-- Step 6 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"a chain-active edge at the endpoint". An actual active edge lies in its
provider edge and its recorded endpoints point in the provider's orientation. -/
private theorem honest_rows_step6_end_E2_step6_active_edge
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g)
    (e : PrototypeEdge S q.2.val.ty)
    (he : (U.recordOf P q g hg).ChainActive (edgeCell e)) :
    q.2.val.cell q.1 e.val ⊆ U.providerPlacement P q g hg ''
      ((P.flag (U.recordIncidence P q g hg)).flag.cell edgeIndex).val.carrier ∧
    ∃ a : ℝ, 0 < a ∧ U.counterDirection P q g hg = a •
      (q.2.val.prototypeFrame q.1 ((U.recordOf P q g hg).endpoints e).2 -
        q.2.val.prototypeFrame q.1 ((U.recordOf P q g hg).endpoints e).1) := by
  classical
  obtain ⟨c, hc, hce⟩ := he
  have hactive : U.ActiveChain P q g hg c := (Finset.mem_filter.mp hc).2
  constructor
  · obtain ⟨hs, hτ, _⟩ := hactive.1 edgeIndex
    have hrel := (U.hierarchy.stratumMap_spec q g hg (c.chain.val.cell edgeIndex) hs).1
    rw [hτ, hce] at hrel
    have hh := closure_mono hrel
    rw [restrictionOp_source_step5_cell_closure,
      (honest_rows_step6_end_E2_step3_placed_cell (U.providerPlacement P q g hg)
        ((P.flag (U.recordIncidence P q g hg)).flag.cell edgeIndex).val).2] at hh
    exact hh
  · obtain ⟨a, ha, hdir⟩ :=
      ((restrictionOp_source_step4_chains_step1_test U P q g hg c).mp hactive).2
    have hvec := actualCont_exists_step2_vector U P q g hg c hc e hce
    have hmap := (q.2.val.prototypeFrame q.1).toAffineMap.linearMap_vsub
      ((U.recordOf P q g hg).endpoints e).2 ((U.recordOf P q g hg).endpoints e).1
    change (q.2.val.prototypeFrame q.1).linear
      (((U.recordOf P q g hg).endpoints e).2 - ((U.recordOf P q g hg).endpoints e).1) = _
      at hmap
    rw [hvec] at hmap
    exact ⟨a, ha, hdir.trans (congrArg (fun v : E d => a • v) hmap)⟩

/-- Step 6 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"at the endpoint". Incidence with a flag endpoint identifies the matching
recorded endpoint of an active edge, on either serving side. -/
private theorem honest_rows_step6_end_E2_step6_endpoints
    (U : HonestSource S) (P : Params S) (q : U.Node)
    (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g)
    (e : PrototypeEdge S q.2.val.ty)
    (he : (U.recordOf P q g hg).ChainActive (edgeCell e)) :
    (U.providerPlacement P q g hg (P.flag (U.recordIncidence P q g hg)).initial ∈
        q.2.val.cell q.1 e.val →
      q.2.val.prototypeFrame q.1 ((U.recordOf P q g hg).endpoints e).1 =
        U.providerPlacement P q g hg (P.flag (U.recordIncidence P q g hg)).initial) ∧
    (U.providerPlacement P q g hg (P.flag (U.recordIncidence P q g hg)).terminal ∈
        q.2.val.cell q.1 e.val →
      q.2.val.prototypeFrame q.1 ((U.recordOf P q g hg).endpoints e).2 =
        U.providerPlacement P q g hg (P.flag (U.recordIncidence P q g hg)).terminal) := by
  let ψ := U.providerPlacement P q g hg
  let F := P.flag (U.recordIncidence P q g hg)
  let p := ψ F.initial
  let r := ψ F.terminal
  let a := q.2.val.prototypeFrame q.1 ((U.recordOf P q g hg).endpoints e).1
  let b := q.2.val.prototypeFrame q.1 ((U.recordOf P q g hg).endpoints e).2
  have hends := actualCont_exists_step2_endpoints (U.recordOf P q g hg) e
  have hab : a ≠ b := fun h => hends.1 ((q.2.val.prototypeFrame q.1).injective h)
  have hseg : q.2.val.cell q.1 e.val = segment ℝ a b := by
    rw [FramedNode.cell, hends.2]
    exact image_segment ℝ (q.2.val.prototypeFrame q.1).toAffineMap _ _
  have hflag : ψ '' (F.flag.cell edgeIndex).val.carrier = segment ℝ p r := by
    rw [F.edge_eq]
    exact image_segment ℝ ψ.toAffineMap _ _
  obtain ⟨hsub, k, hk, hdir⟩ := honest_rows_step6_end_E2_step6_active_edge U P q g hg e he
  rw [hseg, hflag] at hsub
  have hdir' : r - p = k • (b - a) :=
    (ψ.toAffineMap.linearMap_vsub F.terminal F.initial).symm.trans hdir
  have hpos : 0 < inner ℝ (r - p) (b - a) := by
    rw [hdir', real_inner_smul_left]
    exact mul_pos hk (real_inner_self_pos.mpr (sub_ne_zero.mpr hab.symm))
  constructor
  · intro hp
    rw [hseg] at hp
    exact honest_rows_step6_end_E2_step6_first_endpoint p r a b
      (hsub (left_mem_segment ℝ a b)) hp hpos
  · intro hr
    rw [hseg] at hr
    apply honest_rows_step6_end_E2_step6_first_endpoint r p b a
    · rw [segment_symm]
      exact hsub (right_mem_segment ℝ a b)
    · rwa [segment_symm]
    · simpa only [← neg_sub p r, ← neg_sub a b, inner_neg_left,
        inner_neg_right, neg_neg] using hpos

/-- Step 6 of the V4 proof of `honest_rows_step6_end_E2` (V4 2.8):
"kappa = 0 ... kappa = N". The source endpoint counts can be read in any
native isometric frame used by the positioned star. -/
private theorem honest_rows_step6_end_E2_step6_counter
    (U : HonestSource S) (P : Params S) (q : U.Node) (hq : q.1 = 0)
    (g : FacetName S q.2.val.ty) (hg : ¬ U.hierarchy.IsFault q g)
    (φ : Iso d) (x : E d) (initial : Bool)
    (hend : x = φ (U.providerPlacement P q g hg
        (P.flag (U.recordIncidence P q g hg)).initial) ∨
      x = φ (U.providerPlacement P q g hg
        (P.flag (U.recordIncidence P q g hg)).terminal))
    (hinit : initial = decide (x = φ (U.providerPlacement P q g hg
      (P.flag (U.recordIncidence P q g hg)).initial)))
    (e : PrototypeEdge S q.2.val.ty)
    (he : (U.recordOf P q g hg).ChainActive (edgeCell e))
    (hx : x ∈ placedSet (q.2.val.move φ).frame e.val.carrier) :
    if initial then (U.recordOf P q g hg).kappaMinus e = 0
      else (U.recordOf P q g hg).kappaPlus e = P.N := by
  classical
  have hcell : placedSet (q.2.val.move φ).frame e.val.carrier =
      φ '' q.2.val.cell q.1 e.val := by
    simp [FramedNode.move, FramedNode.cell, FramedNode.prototypeFrame, hq,
      placedSet, Set.image_image]
  rw [hcell] at hx
  by_cases hi : x = φ (U.providerPlacement P q g hg
      (P.flag (U.recordIncidence P q g hg)).initial)
  · have hib : initial = true := by simpa only [hi, decide_true] using hinit
    simp only [hib, ite_true]
    apply (honest_rows_step6_end_E2_step5_endpoint_counts U P q g hg e he).1
    apply (honest_rows_step6_end_E2_step6_endpoints U P q g hg e he).1
    rw [hi] at hx
    exact φ.injective.mem_set_image.mp hx
  · have hib : initial = false := by simpa only [hi, decide_false] using hinit
    simp only [hib, Bool.false_eq_true, ite_false]
    apply (honest_rows_step6_end_E2_step5_endpoint_counts U P q g hg e he).2
    apply (honest_rows_step6_end_E2_step6_endpoints U P q g hg e he).2
    rw [hend.resolve_left hi] at hx
    exact φ.injective.mem_set_image.mp hx

/-- Step 6 of the V4 proof of `honest_rows` (V4 2.8): "(E2): all ports on one
first-generation facet carry its unique packet (Lemma 2.6(c)); alignment: ... the chain is
active, with the orientations transported from $\mathcal F_\iota$ ...; counters: all sites
lie in $\operatorname{relint}h$, so $\kappa=0$ ... immediately after the initial endpoint
and $\kappa=N$ immediately before the terminal endpoint". -/
private theorem honest_rows_step6_end_E2 (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : EndSlot (leafTypeOf U P t ht)) (T : EndTemplate slot)
    (hT : IsActualTemplate U P t ht T.configuration)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (hfv : f.val = slot.facet.val)
    (hvv : v.val = slot.vertex.val)
    (hreal : EndGeometryRealizes U P t f hf v T.geometry) :
    endRow_E2 T := by
  classical
  constructor
  · intro a ha b hb hab u u' hu hu'
    obtain ⟨q, hq, g, hg, hatile, haf, hulabel, hai, hbirth⟩ :=
      honest_rows_step6_end_E2_step1_source U P t ht T.configuration hT f hf v
        T.geometry hreal a ha u hu
    obtain ⟨q', hq', g', hg', hbtile, hbf, hu'label, hbi, hbirth'⟩ :=
      honest_rows_step6_end_E2_step1_source U P t ht T.configuration hT f hf v
        T.geometry hreal b hb u' hu'
    rw [hulabel, hu'label, haf, hbf,
      honest_rows_step6_end_E2_step1_packet_readout U P q hq g,
      honest_rows_step6_end_E2_step1_packet_readout U P q' hq' g']
    exact honest_rows_step6_end_E2_step2_packet U P q q' g g' hg hg'
      (hbirth.trans hbirth'.symm) (hai.symm.trans (hab.trans hbi))
  · intro a ha u hu r hr G hG
    obtain ⟨q, hq, g, hg, hatile, haf, hulabel, hai, hbirth⟩ :=
      honest_rows_step6_end_E2_step1_source U P t ht T.configuration hT f hf v
        T.geometry hreal a ha u hu
    have hr' : U.recordOf P q g hg = r := by
      rw [hulabel, haf, actualCont_exists_step1_readout U P q hq g] at hr
      simpa only [HonestSource.facetRecordOf, dif_neg hg, Option.some.injEq] using hr
    subst r
    have hvpoint : vertexPoint T.geometry.vertex = vertexPoint v := by
      apply Set.singleton_injective
      rw [← vertexPoint_spec T.geometry.vertex, ← vertexPoint_spec v, hreal.2.1]
    have hG' : (U.headerOf P t f hf v).flagTangent (U.recordIncidence P q g hg) =
        some G := by
      simpa only [hreal.2.2.1, hai] using hG
    obtain ⟨hend, hinit, hcones, hsides⟩ :=
      honest_rows_step6_end_E2_step4_header U P t ht f hf v q g hg hbirth G hG'
    constructor
    · intro F hfit
      rw [hatile, hvpoint] at hfit
      rw [hatile]
      exact honest_rows_step6_end_E2_step4_alignment U P q hq g hg
        t.2.val.frame.symm (vertexPoint v) G hend hinit hcones hsides F hfit
    · intro e he hx _hray
      rw [hatile, hvpoint] at hx
      exact honest_rows_step6_end_E2_step6_counter U P q hq g hg t.2.val.frame.symm
        (vertexPoint v) G.initial hend hinit e he hx

/-- Step 1 of the V4 proof of `honest_rows_step7_end_E3` (V4 2.8):
"the record of F in S(P) gives the provider g_F". A native leaf's packet readout
is the packet extracted from that same hierarchy node. -/
private theorem honest_rows_step7_end_E3_step1_readout (U : HonestSource S)
    (P : Params S) (t : U.Node) (ht : t.1 = 0) (f : FacetName S t.2.val.ty) :
    leafPacket (leafTypeOf U P t ht) f.val = U.facetPacket P t f := by
  unfold leafPacket
  rw [← prePattern_of_leafType U P t ht]
  simp only [prePatternOf, dif_pos f.property]

/-- Step 2 of the V4 proof of `honest_rows_step7_end_E3` (V4 2.8):
"the actual star is the complete P-owned star". An actual configuration's label
at a specified native node is that node's own leaf type. -/
private theorem honest_rows_step7_end_E3_step2_label (U : HonestSource S)
    (P : Params S) (t : U.Node) (ht : t.1 = 0) (θ : Template P)
    (hθ : IsActualTemplate U P t ht θ) (q : U.Node) (hq : q.1 = 0)
    (u : LeafType P) (hu : (q.2.val.move t.2.val.frame.symm, u) ∈ θ.tiles) :
    u = leafTypeOf U P q hq := by
  obtain ⟨q', hq', hnode, hlabel⟩ := hθ.2 _ hu
  have heq : q.2.val = q'.2.val := by
    apply FramedNode.ext
    · have hty := congrArg (fun N : FramedNode S => N.ty) hnode
      exact hty
    · ext x : 1
      exact t.2.val.frame.symm.injective
        (congrArg (fun N : FramedNode S => N.frame x) hnode)
  have hqq' : q = q' := by
    rcases q with ⟨n, Q, hQ⟩
    rcases q' with ⟨n', Q', hQ'⟩
    dsimp only at hq hq' heq
    subst n
    subst n'
    cases heq
    rfl
  cases hqq'
  exact hlabel

/-- Step 3 of the V4 proof of `honest_rows_step7_end_E3` (V4 2.8, 2.6(d)):
"if F is a FAULT of P, all ports on F are NULL". Every actual boundary port
inherits its parent facet's packet, including the NULL case. -/
private theorem honest_rows_step7_end_E3_step3_boundary_packet (U : HonestSource S)
    (P : Params S) (t : U.Node) (ht : t.1 = 0)
    (slot : EndSlot (leafTypeOf U P t ht)) (T : EndTemplate slot)
    (hT : IsActualTemplate U P t ht T.configuration)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty)
    (hreal : EndGeometryRealizes U P t f hf v T.geometry)
    (F : FacetName S (U.hierarchy.birthParent t f hf).2.val.ty)
    (a : BoundaryPort P T.geometry.header.birthType)
    (ha : a ∈ T.geometry.boundaryPorts) (haF : a.parentFacet.val = F.val)
    (u : LeafType P) (hu : (a.tile, u) ∈ T.configuration.tiles) :
    leafPacket u a.facet.val = U.facetPacket P (U.hierarchy.birthParent t f hf) F := by
  classical
  obtain ⟨q, hq, F', g, w, hw, hx, hsub, htile, hfacet, hvertex, hparent,
    path, hpath, hop⟩ := (hreal.2.2.2.2.2 a).mp ha
  have hq0 : q.1 = 0 := by
    have hmem : q ∈ ownedStarSet U (U.hierarchy.birthParent t f hf)
        (t.2.val.prototypeFrame t.1 (vertexPoint v)) := by
      simpa only [ownedStar, Set.Finite.mem_toFinset] using hq
    exact hmem.1
  have hFF : F' = F := Subtype.ext (hparent.symm.trans haF)
  subst F'
  have hlu := honest_rows_step7_end_E3_step2_label U P t ht T.configuration hT q hq0 u
    (by simpa only [htile] using hu)
  rw [hlu, hfacet, honest_rows_step7_end_E3_step1_readout U P q hq0 g]
  exact packet_inherited U P (U.hierarchy.birthParent t f hf) q _ hpath.2.1 F g hsub

/-- Step 4 of the V4 proof of `honest_rows_step7_end_E3` (V4 2.8):
"when delta_F < C the recorded age is the actual age". The provider's birth
parent is the ancestor at the uncapped recorded age. -/
private theorem honest_rows_step7_end_E3_step4_uncapped_birth (U : HonestSource S)
    (P : Params S) (B : U.Node) (F : FacetName S B.2.val.ty)
    (hF : ¬ U.hierarchy.IsFault B F) (hage : (U.recordOf P B F hF).age.val < P.C) :
    U.hierarchy.birthParent B F hF =
      U.hierarchy.ancestor B (U.recordOf P B F hF).age.val := by
  have hbirth : U.hierarchy.birthParent B F hF =
      U.hierarchy.ancestor B ((U.hierarchy.firstProvider B F hF).1 + 1) := by
    simp only [CoherentHierarchy.birthParent, CoherentHierarchy.servingChild,
      CoherentHierarchy.ancestor, Function.iterate_succ_apply']
  have hactual : U.hierarchy.age B F hF =
      (U.hierarchy.firstProvider B F hF).1 + 1 := by
    unfold CoherentHierarchy.age CoherentHierarchy.birthHeight
    rw [hbirth, U.hierarchy.ancestor_height]
    omega
  have hrecorded : (U.recordOf P B F hF).age.val =
      (U.hierarchy.firstProvider B F hF).1 + 1 := by
    change min (U.hierarchy.age B F hF) P.C = _
    change min (U.hierarchy.age B F hF) P.C < P.C at hage
    omega
  rw [hrecorded]
  exact hbirth

/-- Step 5 of the V4 proof of `honest_rows_step7_end_E3` (V4 2.8):
"the slots of P(g_F) are the states of the ancestors ... shifted by delta_F".
Packets whose birth nodes differ by delta agree at every pair of PRESENT slots
whose indices differ by delta. -/
private theorem honest_rows_step7_end_E3_step5_shift (U : HonestSource S)
    (P : Params S) (g g' : PrimitiveOccurrence U P) (δ : ℕ)
    (hbirth : g.birth = U.hierarchy.ancestor g'.birth δ) :
    ShiftedAgree (packetOf U P g) (packetOf U P g') δ := by
  classical
  intro i j s s' hji hi hj
  rw [decode_spec] at hi hj
  split_ifs at hi with hmi
  split_ifs at hj with hmj
  have hsi := Option.some.inj hi
  have hsj := Option.some.inj hj
  rw [← hsi, ← hsj, hbirth, U.hierarchy.ancestor_add]
  congr 2
  omega

/-- Step 7 of the V4 proof of `honest_rows` (V4 2.8): "(E3): when $\delta_F<C$ the recorded
age is the actual age, so the record of $F$ in $S(P)$ gives the provider $g_F$ born in
$P_{b+\delta_F}$ and the slots of $\mathcal P(g_F)$ are the states of the ancestors of
$P_{b+\delta_F}$ ...; if $F$ is a FAULT of $P$, all ports on $F$ are NULL." -/
private theorem honest_rows_step7_end_E3 (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : EndSlot (leafTypeOf U P t ht)) (T : EndTemplate slot)
    (hT : IsActualTemplate U P t ht T.configuration)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (hfv : f.val = slot.facet.val)
    (hvv : v.val = slot.vertex.val)
    (hreal : EndGeometryRealizes U P t f hf v T.geometry) :
    endRow_E3 T := by
  classical
  let B := U.hierarchy.birthParent t f hf
  let g := U.providerOccurrence P t f hf
  have hpacket : slot.packet = packetOf U P g := by
    have h := slot.packet_eq
    rw [← hfv, honest_rows_step7_end_E3_step1_readout U P t ht f,
      HonestSource.facetPacket, dif_neg hf] at h
    exact (Option.some.inj h).symm
  have hhead : slot.packet.head = stateOf U P B := by
    rw [hpacket, packet_head]
    rfl
  have htype : T.geometry.header.birthType = B.2.val.ty :=
    congrArg State.Header.birthType hreal.2.2.1
  refine ⟨?_, ?_⟩
  · rw [hhead]
    exact htype.symm
  · intro F hthrough
    let F' : FacetName S B.2.val.ty := ⟨F.val, by rw [← htype]; exact F.property⟩
    have hrecord : stateRecordAt slot.packet.head F.val = U.facetRecordOf P B F' := by
      rw [hhead]
      change stateRecordAt (stateOf U P B) F'.val = U.facetRecordOf P B F'
      simp only [stateRecordAt, stateOf, dif_pos F'.property]
    rw [hrecord]
    by_cases hF : U.hierarchy.IsFault B F'
    · simp only [HonestSource.facetRecordOf, dif_pos hF]
      intro a ha haF u hu
      rw [honest_rows_step7_end_E3_step3_boundary_packet U P t ht slot T hT f hf v
        hreal F' a ha haF u hu]
      exact dif_pos hF
    · simp only [HonestSource.facetRecordOf, dif_neg hF]
      let gF := U.providerOccurrence P B F' hF
      refine ⟨packetOf U P gF, ⟨U, gF, rfl⟩, rfl, fun _ => Iff.rfl, ?_, ?_⟩
      · intro a ha haF u hu
        rw [honest_rows_step7_end_E3_step3_boundary_packet U P t ht slot T hT f hf v
          hreal F' a ha haF u hu]
        exact dif_neg hF
      · intro hage
        rw [hpacket]
        exact honest_rows_step7_end_E3_step5_shift U P gF g _
          (honest_rows_step7_end_E3_step4_uncapped_birth U P B F' hF hage)

/-- Step 1 of the V4 proof of `honest_rows_step8_end_E4` (V4 2.8):
"the heads of first-generation facets of P are S(P)". The packet read from an
actual native leaf is the packet of its facet's provider occurrence. -/
private theorem honest_rows_step8_end_E4_step1_packet (U : HonestSource S) (P : Params S)
    (q : U.Node) (hq : q.1 = 0) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) :
    leafPacket (leafTypeOf U P q hq) f.val =
      some (packetOf U P (U.providerOccurrence P q f hf)) := by
  unfold leafPacket
  rw [← prePattern_of_leafType U P q hq]
  simp only [prePatternOf, dif_pos f.property, HonestSource.facetPacket, dif_neg hf]

/-- Step 2 of the V4 proof of `honest_rows_step8_end_E4` (V4 2.8):
"the slots are the ancestors' states". Two primitive occurrences with the same
birth parent decode to the same state at every common PRESENT index. -/
private theorem honest_rows_step8_end_E4_step2_present (U : HonestSource S) (P : Params S)
    (g g' : PrimitiveOccurrence U P) (hb : g.birth = g'.birth) :
    AgreePresent (packetOf U P g) (packetOf U P g') := by
  intro j s s' hs hs'
  rw [decode_spec] at hs hs'
  split at hs
  · split at hs'
    · have h := Option.some.inj hs
      rw [hb] at h
      exact h.symm.trans (Option.some.inj hs')
    · contradiction
  · contradiction

/-- Step 8 of the V4 proof of `honest_rows` (V4 2.8): "(E4): the heads of first-generation
facets of $P$ are $S(P)$ and the slots are the ancestors' states." -/
private theorem honest_rows_step8_end_E4 (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : EndSlot (leafTypeOf U P t ht)) (T : EndTemplate slot)
    (hT : IsActualTemplate U P t ht T.configuration)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (hfv : f.val = slot.facet.val)
    (hvv : v.val = slot.vertex.val)
    (hreal : EndGeometryRealizes U P t f hf v T.geometry) :
    endRow_E4 T := by
  have hports : ∀ a ∈ T.geometry.primitivePorts, ∀ u : LeafType P,
      (a.tile, u) ∈ T.configuration.tiles → ∃ g : PrimitiveOccurrence U P,
        g.birth = U.hierarchy.birthParent t f hf ∧
          leafPacket u a.facet.val = some (packetOf U P g) := by
    intro a ha u hu
    obtain ⟨q, hq, g, hg, w, hw, _, hbirth, htile, hfacet, _⟩ :=
      (hreal.2.2.2.2.1 a).mp ha
    have howned : q ∈ ownedStarSet U (U.hierarchy.birthParent t f hf)
        (t.2.val.prototypeFrame t.1 (vertexPoint v)) := by
      simpa only [ownedStar, Set.Finite.mem_toFinset] using hq
    have hlabel : u = leafTypeOf U P q howned.1 :=
      honest_rows_step5_end_E1_step1_label U P t ht T.configuration hT q howned.1 u
        (by simpa only [htile] using hu)
    refine ⟨U.providerOccurrence P q g hg, hbirth, ?_⟩
    rw [hlabel, hfacet]
    exact honest_rows_step8_end_E4_step1_packet U P q howned.1 g hg
  intro a ha u hu
  obtain ⟨g, hg, hpacket⟩ := hports a ha u hu
  refine ⟨packetOf U P g, hpacket, ?_, ?_⟩
  · rw [packet_head, hg, honest_rows_step5_end_E1_step2_head U P t ht slot f hf hfv]
  · intro b hb u' hu' q' hq'
    obtain ⟨g', hg', hpacket'⟩ := hports b hb u' hu'
    have hq : q' = packetOf U P g' := Option.some.inj (hq'.symm.trans hpacket')
    rw [hq]
    exact honest_rows_step8_end_E4_step2_present U P g g' (hg.trans hg'.symm)

/-- Step 1 of the V4 proof of `honest_rows_step9_end_E5` (V4 2.8):
"coalescence of the tracks, hence the same provider occurrence and the same packet,
or both NULL". Both tracks inherit the packet of their common ancestor facet. -/
private theorem honest_rows_step9_end_E5_step1_coalescence (U : HonestSource S)
    (P : Params S) (q : U.Node) (f g : FacetName S q.2.val.ty)
    (hE : stateEAt (stateOf U P q) f.val g.val) :
    U.facetPacket P q f = U.facetPacket P q g := by
  obtain ⟨_, _, hE⟩ := hE
  obtain ⟨a, _, F, hf, hg⟩ := (U.mem_coalescenceTable q f g).mp hE
  exact (packet_inherited U P (U.hierarchy.ancestor q a) q a rfl F f hf).trans
    (packet_inherited U P (U.hierarchy.ancestor q a) q a rfl F g hg).symm

/-- Step 9 of the V4 proof of `honest_rows` (V4 2.8): "(E5): $E_P(F,F')$ means coalescence
of the tracks, hence the same provider occurrence and the same packet, or both NULL." -/
private theorem honest_rows_step9_end_E5 (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : EndSlot (leafTypeOf U P t ht)) (T : EndTemplate slot)
    (hT : IsActualTemplate U P t ht T.configuration)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (hfv : f.val = slot.facet.val)
    (hvv : v.val = slot.vertex.val)
    (hreal : EndGeometryRealizes U P t f hf v T.geometry) :
    endRow_E5 T := by
  intro a ha b hb hE u u' hu hu'
  obtain ⟨q, hq, F, g, w, _, _, hsub, htile, hfacet, _, hparent, path, hp, _⟩ :=
    (hreal.2.2.2.2.2 a).mp ha
  obtain ⟨q', hq', F', g', w', _, _, hsub', htile', hfacet', _, hparent',
      path', hp', _⟩ := (hreal.2.2.2.2.2 b).mp hb
  have howned : q ∈ ownedStarSet U (U.hierarchy.birthParent t f hf)
      (t.2.val.prototypeFrame t.1 (vertexPoint v)) := by
    simpa only [ownedStar, Set.Finite.mem_toFinset] using hq
  have howned' : q' ∈ ownedStarSet U (U.hierarchy.birthParent t f hf)
      (t.2.val.prototypeFrame t.1 (vertexPoint v)) := by
    simpa only [ownedStar, Set.Finite.mem_toFinset] using hq'
  have hlabel : u = leafTypeOf U P q howned.1 :=
    honest_rows_step5_end_E1_step1_label U P t ht T.configuration hT q howned.1 u
      (by simpa only [htile] using hu)
  have hlabel' : u' = leafTypeOf U P q' howned'.1 :=
    honest_rows_step5_end_E1_step1_label U P t ht T.configuration hT q' howned'.1 u'
      (by simpa only [htile'] using hu')
  rw [honest_rows_step5_end_E1_step2_head U P t ht slot f hf hfv,
    hparent, hparent'] at hE
  calc
    leafPacket u a.facet.val = U.facetPacket P q g := by
      rw [hlabel, hfacet, honest_rows_step4_cont_packet_step6_readout]
    _ = U.facetPacket P (U.hierarchy.birthParent t f hf) F :=
      packet_inherited U P _ q _ hp.2.1 F g hsub
    _ = U.facetPacket P (U.hierarchy.birthParent t f hf) F' :=
      honest_rows_step9_end_E5_step1_coalescence U P _ F F' hE
    _ = U.facetPacket P q' g' :=
      (packet_inherited U P _ q' _ hp'.2.1 F' g' hsub').symm
    _ = leafPacket u' b.facet.val := by
      rw [hlabel', hfacet', honest_rows_step4_cont_packet_step6_readout]

/-- Step 10 of the V4 proof of `honest_rows` (V4 2.8): "(E6): all ports on one facet carry
its unique packet or are all NULL." -/
private theorem honest_rows_step10_end_E6 (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : EndSlot (leafTypeOf U P t ht)) (T : EndTemplate slot)
    (hT : IsActualTemplate U P t ht T.configuration)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (v : VertexName S t.2.val.ty) (hfv : f.val = slot.facet.val)
    (hvv : v.val = slot.vertex.val)
    (hreal : EndGeometryRealizes U P t f hf v T.geometry) :
    endRow_E6 T := by
  intro a ha b hb hab u w hu hw
  have htype : T.geometry.header.birthType =
      (U.hierarchy.birthParent t f hf).2.val.ty :=
    congrArg State.Header.birthType hreal.2.2.1
  let F : FacetName S (U.hierarchy.birthParent t f hf).2.val.ty :=
    ⟨a.parentFacet.val, by rw [← htype]; exact a.parentFacet.property⟩
  exact (honest_rows_step7_end_E3_step3_boundary_packet U P t ht slot T hT f hf v
    hreal F a ha rfl u hu).trans
    (honest_rows_step7_end_E3_step3_boundary_packet U P t ht slot T hT f hf v
      hreal F b hb hab.symm w hw).symm

/-- Q14, V4 2.8: in every honest source, at every event slot of every native tile,
there is an actual positioned configuration belonging to the allowed catalogue.
CONT uses the physical-vertex jump rule; END asserts all six clauses simultaneously.
(repaired after a false-claim verdict 2026-10-27: assert existence of an actual allowed
configuration because the geometry-only choice need not follow the recorded active chain) -/
theorem honest_rows (U : HonestSource S) (P : Params S) :
    ∀ (t : U.Node) (ht : t.1 = 0) (slot : EventSlot (leafTypeOf U P t ht)),
      ∃ θ : Template P, IsActualTemplate U P t ht θ ∧ θ ∈ allowedTemplates slot := by
  intro t ht slot
  cases slot with
  | cont s =>
    obtain ⟨T, hT, hc, ho⟩ := honest_rows_step1_cont_geometry U P t ht s
    obtain ⟨hi, hs, hb⟩ := honest_rows_step2_cont_labels U P t ht s T hT hc ho
    obtain ⟨hk1, hk2⟩ := honest_rows_step3_cont_counters U P t ht s T hT hc ho
    have hp := honest_rows_step4_cont_packet U P t ht s T hT hc ho
    have hrow : contRow T := by
      unfold contRow
      exact ⟨hi, hs, hb, hc, ho, T.aligned, hk1, hk2, hp⟩
    refine ⟨T.configuration, hT, ?_⟩
    show ∃ T' : ContTemplate s, T'.configuration = T.configuration ∧ contRow T'
    exact ⟨T, rfl, hrow⟩
  | end_ s =>
    obtain ⟨T, hT, f, hf, v, hfv, hvv, hreal⟩ := actualEnd_exists U P t ht s
    have hrow : endRow T := by
      unfold endRow
      exact ⟨honest_rows_step5_end_E1 U P t ht s T hT f hf v hfv hvv hreal,
        honest_rows_step6_end_E2 U P t ht s T hT f hf v hfv hvv hreal,
        honest_rows_step7_end_E3 U P t ht s T hT f hf v hfv hvv hreal,
        honest_rows_step8_end_E4 U P t ht s T hT f hf v hfv hvv hreal,
        honest_rows_step9_end_E5 U P t ht s T hT f hf v hfv hvv hreal,
        honest_rows_step10_end_E6 U P t ht s T hT f hf v hfv hvv hreal⟩
    refine ⟨T.configuration, hT, ?_⟩
    show ∃ T' : EndTemplate s, T'.configuration = T.configuration ∧ endRow T'
    exact ⟨T, rfl, hrow⟩

end Enforce
