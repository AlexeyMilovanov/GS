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
  sorry

/-- Step 2 of the V4 proof of `honest_rows` (V4 2.8): "by Remark 2.1 (converse part) $e''$ is
a chain-active edge of the facet $f''$ of $t''$ inside $g$, whose record has the same $\iota$,
side and $\beta$ (same provider $g$, same serving child $H$)". -/
private theorem honest_rows_step2_cont_labels (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : ContSlot (leafTypeOf U P t ht)) (T : ContTemplate slot)
    (hT : IsActualTemplate U P t ht T.configuration)
    (hc : T.centralChain ∈ slot.record.chains) (ho : T.otherChain ∈ T.record.chains) :
    T.record.incidence = slot.record.incidence ∧ T.record.side = slot.record.side ∧
      T.record.beta = slot.record.beta := by
  sorry

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
  sorry

/-- Step 4 of the V4 proof of `honest_rows` (V4 2.8): "the packets attached to $f,f''$ are
both $\mathcal P(g)$". -/
private theorem honest_rows_step4_cont_packet (U : HonestSource S) (P : Params S) (t : U.Node)
    (ht : t.1 = 0) (slot : ContSlot (leafTypeOf U P t ht)) (T : ContTemplate slot)
    (hT : IsActualTemplate U P t ht T.configuration)
    (hc : T.centralChain ∈ slot.record.chains) (ho : T.otherChain ∈ T.record.chains) :
    leafPacket T.label T.record.facet.val = some slot.packet := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
