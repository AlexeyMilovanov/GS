import Enforce.Compiler.Clusters
import Enforce.Combinatorics

/-!
# The C1 compiler, honest lifts, and forced configurations

M3--M8, V4 2.11--2.17. CORE markings are glued using the fixed native frames
inside the certificate. EVENT markings use exactly the positioned template frames.
All point functions are real definitions. Existence and geometric assertions are
separate theorem declarations, including those used to build bundled objects.

The typed-carrier convention D1 is retained: augmented colours recover a unique
leaf type and full frame from each placed marked carrier. Blocks retain their
certificate and frame, with proof-irrelevant subdivision witnesses.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d} {P : Params S}

attribute [local instance] Classical.decEq

namespace Compiler

/-- M3, V4 2.11: all augmented leaves, with their original physical carriers. -/
def physicalCatalogue (C : ClusterData S P) : Finset (MarkedPrototile d (Colour S P)) :=
  Finset.univ.image (augmentedLeaf C)

/-- M3, V4 2.11: the finite index of an EVENT rule, with its allowed annotation. -/
structure EventIndex (S : SubstSystem d) (P : Params S) where
  /-- M3, V4 2.11: central leaf type. -/
  leaf : LeafType P
  /-- M3, V4 2.11: central event slot. -/
  slot : EventSlot leaf
  /-- M3, V4 2.11: complete positioned labelled configuration. -/
  template : Template P
  /-- M3, V4 2.11: the configuration satisfies the slot's row. -/
  allowed : template ∈ allowedTemplates slot

private def EventIndex.equiv (S : SubstSystem d) (P : Params S) : EventIndex S P ≃
    Σ l : LeafType P, Σ slot : EventSlot l, (allowedTemplates slot : Set (Template P)) where
  toFun e := ⟨e.leaf, e.slot, ⟨e.template, e.allowed⟩⟩
  invFun s := { leaf := s.1, slot := s.2.1, template := s.2.2.1, allowed := s.2.2.2 }
  left_inv e := by cases e; rfl
  right_inv s := by rcases s with ⟨leaf, slot, template, allowed⟩; rfl

/-- M3, V4 2.11: the indexed allowed template family is finite. -/
theorem eventIndices_finite (S : SubstSystem d) (P : Params S) :
    Finite (EventIndex S P) := by
  have inst1 : Finite (LeafType P) := Finite.of_fintype _
  have inst2 (l : LeafType P) : Finite (EventSlot l) := Finite.of_fintype _
  have inst3 (l : LeafType P) (slot : EventSlot l) :
    Finite (allowedTemplates slot : Set (Template P)) := allowedTemplates_finite P l slot
  exact Finite.of_equiv _ (EventIndex.equiv S P).symm

/-- M3, V4 2.11: enumeration of EVENT rule indices. -/
instance eventIndexFintype (S : SubstSystem d) (P : Params S) :
    Fintype (EventIndex S P) := by
  letI := eventIndices_finite S P
  exact Fintype.ofFinite _

/-- M3, V4 2.11: every allowed template has the prescribed central label. -/
theorem allowedTemplate_central (l : LeafType P) (j : EventSlot l) (θ : Template P)
    (hθ : θ ∈ allowedTemplates j) : θ.central = l := by
  cases j with
  | cont s =>
    rcases hθ with ⟨T, hT_eq, _⟩
    rw [← hT_eq]
    exact T.central_eq
  | end_ s =>
    rcases hθ with ⟨T, hT_eq, _⟩
    rw [← hT_eq]
    exact T.central_eq

/-- M3, V4 2.11: the distinguished positioned labelled tile. -/
def centralPair (l : LeafType P) : FramedNode S × LeafType P :=
  (⟨l.prototype, AffineIsometryEquiv.refl ℝ (E d)⟩, l)

/-- M3, V4 2.11: every non-central tile contributes exactly its closed RO ball. -/
def eventReadouts (e : EventIndex S P) : Finset (FramedNode S × LeafType P) :=
  e.template.tiles.filter (fun z => z ≠ centralPair e.leaf)

/-- M3, V4 2.11: a template tile's closed readout ball in the central frame. -/
def readoutRegion (C : ClusterData S P) (z : FramedNode S × LeafType P) : Set (E d) :=
  placedSet z.1.frame (C.enclosing z.2 .readout)

/-- M3, V4 2.11: CORE carrier, with every open trigger ball removed.
The position is `S.nativeTile D.ty K w`, so no arbitrary leaf placement is chosen. -/
def coreCarrier (C : ClusterData S P) (D : CertificateSymbol S P) : Set (E d) :=
  S.supertile P.K D.val.ty \
    (⋃ w : S.RoleWord D.val.ty P.K, ⋃ j : EventSlot (⟨D, w⟩ : LeafType P),
      placedSet (LeafType.position (⟨D, w⟩ : LeafType P))
        (C.openTrigger (⟨D, w⟩ : LeafType P) j))

/-- M3, V4 2.11: the certificate's total ambient marking, extended by @ outside.
A covering native leaf supplies a value; shared leaf boundaries all have colour @.
The independence lemma below states that every covering leaf gives the same value. -/
def certificateColour (C : ClusterData S P) (D : CertificateSymbol S P)
    (x : E d) : Colour S P := by
  classical
  exact if h : ∃ w : S.RoleWord D.val.ty P.K,
      x ∈ placedSet (LeafType.position (⟨D, w⟩ : LeafType P))
        (S.proto (LeafType.prototype (⟨D, w⟩ : LeafType P))).carrier then
    let l : LeafType P := ⟨D, Classical.choose h⟩
    augmentedColour C l (l.position.symm x)
    else .boundary

/-- Step 1 of the V4 proof of `certificateColour_leaf` (V4 2.11):
"compatible on shared boundaries: all @". Distinct native leaves meet on their frontiers. -/
private theorem certificateColour_leaf_step1_frontier (D : CertificateSymbol S P)
    (v w : S.RoleWord D.val.ty P.K) (hvw : v ≠ w) (x : E d)
    (hxv : x ∈ placedSet (LeafType.position (⟨D, v⟩ : LeafType P))
      (S.proto (LeafType.prototype (⟨D, v⟩ : LeafType P))).carrier)
    (hxw : x ∈ placedSet (LeafType.position (⟨D, w⟩ : LeafType P))
      (S.proto (LeafType.prototype (⟨D, w⟩ : LeafType P))).carrier) :
    (LeafType.position (⟨D, v⟩ : LeafType P)).symm x ∈
      frontier (S.proto (LeafType.prototype (⟨D, v⟩ : LeafType P))).carrier := by
  let l : LeafType P := ⟨D, v⟩
  let u : LeafType P := ⟨D, w⟩
  have hd : Disjoint (interior (placedSet l.position (S.proto l.prototype).carrier))
      (interior (placedSet u.position (S.proto u.prototype).carrier)) := by
    simpa [l, u, LeafType.position, LeafType.prototype, FramedNode.carrier,
      SubstSystem.supertile] using S.native_disjoint D.val.ty P.K hvw
  have hu : closure (interior (placedSet u.position (S.proto u.prototype).carrier)) =
      placedSet u.position (S.proto u.prototype).carrier := by
    change closure (interior (u.position.toHomeomorph '' _)) = u.position.toHomeomorph '' _
    rw [← u.position.toHomeomorph.image_interior,
      ← u.position.toHomeomorph.image_closure, (S.proto u.prototype).regularClosed]
  have hd' := hd.closure_right isOpen_interior
  rw [hu] at hd'
  have hfront : x ∈ frontier (placedSet l.position (S.proto l.prototype).carrier) :=
    ⟨subset_closure hxv, fun hi => Set.disjoint_left.mp hd' hi hxw⟩
  change x ∈ frontier (l.position.toHomeomorph '' (S.proto l.prototype).carrier) at hfront
  rw [← l.position.toHomeomorph.image_frontier] at hfront
  obtain ⟨y, hy, hxy⟩ := hfront
  change l.position y = x at hxy
  change l.position.symm x ∈ frontier (S.proto l.prototype).carrier
  rw [← hxy, AffineIsometryEquiv.symm_apply_apply]
  exact hy

/-- M3, V4 2.11: gluing agrees with each native leaf at every shared point. -/
theorem certificateColour_leaf (C : ClusterData S P) (D : CertificateSymbol S P)
    (w : S.RoleWord D.val.ty P.K) (x : E d)
    (hx : x ∈ placedSet (LeafType.position (⟨D, w⟩ : LeafType P))
      (S.proto (LeafType.prototype (⟨D, w⟩ : LeafType P))).carrier) :
    certificateColour C D x = augmentedColour C (⟨D, w⟩ : LeafType P)
      ((LeafType.position (⟨D, w⟩ : LeafType P)).symm x) := by
  classical
  have h : ∃ v : S.RoleWord D.val.ty P.K,
      x ∈ placedSet (LeafType.position (⟨D, v⟩ : LeafType P))
        (S.proto (LeafType.prototype (⟨D, v⟩ : LeafType P))).carrier := ⟨w, hx⟩
  unfold certificateColour
  rw [dif_pos h]
  by_cases hw : Classical.choose h = w
  · simp only [hw]
  · have hv := Classical.choose_spec h
    rw [augmentedMarking_boundary C _ _
      (certificateColour_leaf_step1_frontier D _ _ hw x hv hx),
      augmentedMarking_boundary C _ _
        (certificateColour_leaf_step1_frontier D _ _ (Ne.symm hw) x hx hv)]

/-- M3, V4 2.11: CORE supports are compact, as closed subsets of supertiles. -/
theorem coreCarrier_compact (C : ClusterData S P) (D : CertificateSymbol S P) :
    IsCompact (coreCarrier C D) := by
  dsimp [Compiler.coreCarrier, SubstSystem.supertile]
  apply IsCompact.diff
  · apply IsCompact.image (S.proto D.val.ty).compact
    exact ContinuousLinearEquiv.continuous (S.σ ^ P.K).toContinuousLinearEquiv
  · apply isOpen_iUnion
    intro w
    apply isOpen_iUnion
    intro j
    have hl : IsOpen (C.openTrigger ⟨D, w⟩ j) := by
      dsimp [ClusterData.openTrigger]
      exact Metric.isOpen_ball
    dsimp [placedSet]
    rw [← Homeomorph.isOpen_image (LeafType.position (⟨D, w⟩ : LeafType P)).toHomeomorph] at hl
    exact hl

/-- M3, V4 2.11: the compact certificate rule CORE_D. -/
def coreRule (C : ClusterData S P) (D : CertificateSymbol S P) :
    CompactRule d (Colour S P) where
  carrier := coreCarrier C D
  mark x := certificateColour C D x
  compact := coreCarrier_compact C D

/-- M3, V4 2.11: EVENT support, central closed trigger plus other closed RO balls. -/
def eventCarrier (C : ClusterData S P) (e : EventIndex S P) : Set (E d) :=
  C.enclosing e.leaf (.trigger e.slot) ∪
    ⋃ z ∈ eventReadouts e, readoutRegion C z

/-- M3, V4 2.11: EVENT marking in its central prototype frame.
The central trigger is read first; all other points are read from a positioned
RO ball. On the defined carrier one of these cases always applies. -/
def eventColour (C : ClusterData S P) (e : EventIndex S P) (x : E d) : Colour S P := by
  classical
  exact if x ∈ C.enclosing e.leaf (.trigger e.slot) then augmentedColour C e.leaf x
    else if h : ∃ z ∈ eventReadouts e, x ∈ readoutRegion C z then
      let z := Classical.choose h
      augmentedColour C z.2 (z.1.frame.symm x)
    else .boundary

/-- M3, V4 2.11: all EVENT supports are finite unions of compact closed balls. -/
theorem eventCarrier_compact (C : ClusterData S P) (e : EventIndex S P) :
    IsCompact (eventCarrier C e) := by
  dsimp [eventCarrier]
  apply IsCompact.union
  · exact isCompact_closedBall (C.enclosingCentre e.leaf (.trigger e.slot)) (C.enclosingRadius e.leaf (.trigger e.slot))
  · apply Finset.isCompact_biUnion
    intro z _
    dsimp [readoutRegion, placedSet]
    apply IsCompact.image (isCompact_closedBall _ _)
    exact z.1.frame.continuous

/-- M3, V4 2.11: agreement with the central trigger marking, including its sphere. -/
theorem eventColour_trigger (C : ClusterData S P) (e : EventIndex S P) (x : E d)
    (hx : x ∈ C.enclosing e.leaf (.trigger e.slot)) :
    eventColour C e x = augmentedColour C e.leaf x := by
  classical
  simp only [eventColour, if_pos hx]

/-- Step 1 of the V4 proof of `eventColour_readout` (V4 2.11): trigger disjointness. -/
private theorem eventColour_readout_step1_trigger_disjoint (C : ClusterData S P) (e : EventIndex S P)
    (z : FramedNode S × LeafType P) (hz : z ∈ eventReadouts e) (x : E d)
    (hx : x ∈ readoutRegion C z) :
    x ∉ C.enclosing e.leaf (.trigger e.slot) := by
  intro h_contra
  have hz_neq : z ≠ centralPair e.leaf := (Finset.mem_filter.mp hz).2
  dsimp [readoutRegion, placedSet] at hx
  rcases hx with ⟨y, hy, hxy⟩
  
  have hz_mem_tiles : z ∈ e.template.tiles := (Finset.mem_filter.mp hz).1
  have hc_mem_tiles : centralPair e.leaf ∈ e.template.tiles := by
    have h1 := e.template.central_mem
    have h2 : e.template.central = e.leaf := allowedTemplate_central e.leaf e.slot e.template e.allowed
    dsimp [centralPair]
    rwa [←h2]
  have h_disj := e.template.disjoint hz_mem_tiles hc_mem_tiles hz_neq
  
  have hz_inside : y ∈ interior (S.proto z.2.prototype).carrier := by
    have h_sub := C.enclosing_inside z.2 .readout
    exact h_sub hy
  have hc_inside : x ∈ interior (S.proto e.leaf.prototype).carrier := by
    have h_sub := C.enclosing_inside e.leaf (.trigger e.slot)
    exact h_sub h_contra
    
  have hz_carrier : x ∈ interior (z.1.carrier 0) := by
    rw [←hxy]
    have hz_type_match := e.template.types_match z hz_mem_tiles
    dsimp [FramedNode.carrier, SubstSystem.supertile, placedSet]
    have eq1 : interior (⇑z.1.frame '' (⇑(S.σ ^ 0) '' (S.proto z.1.ty).carrier)) =
        z.1.frame '' interior (⇑(S.σ ^ 0) '' (S.proto z.1.ty).carrier) := by
      have h3 := Homeomorph.image_interior z.1.frame.toHomeomorph (⇑(S.σ ^ 0) '' (S.proto z.1.ty).carrier)
      exact h3.symm
    rw [eq1]
    apply Set.mem_image_of_mem
    have eq2 : interior (⇑(S.σ ^ 0) '' (S.proto z.1.ty).carrier) = ⇑(S.σ ^ 0) '' interior (S.proto z.1.ty).carrier := by
      have h3 := Homeomorph.image_interior (S.σ ^ 0).toContinuousLinearEquiv.toHomeomorph (S.proto z.1.ty).carrier
      exact h3.symm
    rw [eq2]
    apply Set.mem_image_of_mem
    rwa [hz_type_match]
  
  have hc_carrier : x ∈ interior ((centralPair e.leaf).1.carrier 0) := by
    dsimp [centralPair, FramedNode.carrier, SubstSystem.supertile, placedSet]
    have eq2 : interior (⇑(S.σ ^ 0) '' (S.proto e.leaf.prototype).carrier) = ⇑(S.σ ^ 0) '' interior (S.proto e.leaf.prototype).carrier := by
      have h3 := Homeomorph.image_interior (S.σ ^ 0).toContinuousLinearEquiv.toHomeomorph (S.proto e.leaf.prototype).carrier
      exact h3.symm
    have eq3 : interior (id '' (⇑(S.σ ^ 0) '' (S.proto e.leaf.prototype).carrier)) =
        id '' interior (⇑(S.σ ^ 0) '' (S.proto e.leaf.prototype).carrier) := by
      have h3 := Homeomorph.image_interior (Homeomorph.refl (E d)) (⇑(S.σ ^ 0) '' (S.proto e.leaf.prototype).carrier)
      exact h3.symm
    rw [eq3, eq2]
    apply Set.mem_image_of_mem
    apply Set.mem_image_of_mem
    exact hc_inside

  have h_disj_inter := Set.disjoint_iff_inter_eq_empty.mp h_disj
  have hx_in_inter : x ∈ interior (z.1.carrier 0) ∩ interior ((centralPair e.leaf).1.carrier 0) := ⟨hz_carrier, hc_carrier⟩
  rw [h_disj_inter] at hx_in_inter
  exact Set.mem_empty_iff_false x |>.mp hx_in_inter

/-- Step 2 of the V4 proof of `eventColour_readout` (V4 2.11): readout disjointness. -/
private theorem eventColour_readout_step2_readout_disjoint (C : ClusterData S P) (e : EventIndex S P)
    (z1 z2 : FramedNode S × LeafType P) (hz1 : z1 ∈ eventReadouts e) (hz2 : z2 ∈ eventReadouts e)
    (x : E d) (hx1 : x ∈ readoutRegion C z1) (hx2 : x ∈ readoutRegion C z2) :
    z1 = z2 := by
  sorry

/-- M3, V4 2.11: agreement with every other tile's whole closed readout ball. -/
theorem eventColour_readout (C : ClusterData S P) (e : EventIndex S P)
    (z : FramedNode S × LeafType P) (hz : z ∈ eventReadouts e) (x : E d)
    (hx : x ∈ readoutRegion C z) :
    eventColour C e x = augmentedColour C z.2 (z.1.frame.symm x) := by
  classical
  unfold eventColour
  have h_not_trigger := eventColour_readout_step1_trigger_disjoint C e z hz x hx
  rw [if_neg h_not_trigger]
  have h_exists : ∃ z' ∈ eventReadouts e, x ∈ readoutRegion C z' := ⟨z, hz, hx⟩
  rw [dif_pos h_exists]
  have h_choose := eventColour_readout_step2_readout_disjoint C e (Classical.choose h_exists) z (Classical.choose_spec h_exists).1 hz x (Classical.choose_spec h_exists).2 hx
  rw [h_choose]

/-- M3, V4 2.11: the compact event rule EV_(leaf,slot,template). -/
def eventRule (C : ClusterData S P) (e : EventIndex S P) :
    CompactRule d (Colour S P) where
  carrier := eventCarrier C e
  mark x := eventColour C e x
  compact := eventCarrier_compact C e

/-- M3, V4 2.11: exactly the union of the finite CORE and EVENT families. -/
def ruleCatalogue (C : ClusterData S P) : Finset (CompactRule d (Colour S P)) :=
  (Finset.univ.image (coreRule C)) ∪ (Finset.univ.image (eventRule C))

end Compiler

/-- M3, V4 2.11: the actual finite C1 system, with precisely the native carriers.
All geometry and point markings are given by definitions above; no arbitrary C1
system is selected from an existence theorem. -/
def systemM (S : SubstSystem d) (P : Params S) (C : ClusterData S P) :
    C1System d (Colour S P) where
  colors_finite := colourFintype S P
  physical := Compiler.physicalCatalogue C
  rules := Compiler.ruleCatalogue C

namespace Compiler

/-- M3, V4 2.11: membership in the physical catalogue supplies an actual leaf. -/
theorem physicalLeaf_exists (C : ClusterData S P)
    (Q : {Q // Q ∈ (systemM S P C).physical}) :
    ∃ l : LeafType P, augmentedLeaf C l = Q.val := by
  simpa only [systemM, physicalCatalogue, Finset.mem_image, Finset.mem_univ,
    true_and] using Q.property

/-- M3, V4 2.11: decode a physical prototype's leaf label from catalogue membership. -/
def physicalLeaf (C : ClusterData S P)
    (Q : {Q // Q ∈ (systemM S P C).physical}) : LeafType P :=
  Classical.choose (physicalLeaf_exists C Q)

/-- M3, V4 2.11: the decoded label realizes the complete marked prototype. -/
theorem physicalLeaf_spec (C : ClusterData S P)
    (Q : {Q // Q ∈ (systemM S P C).physical}) :
    augmentedLeaf C (physicalLeaf C Q) = Q.val :=
  Classical.choose_spec (physicalLeaf_exists C Q)

/-- M3, V4 2.11: decoding preserves the literal prototype carrier. -/
theorem decoration_carrier (C : ClusterData S P)
    (Q : {Q // Q ∈ (systemM S P C).physical}) :
    Q.val.carrier = (S.proto (physicalLeaf C Q).prototype).carrier := by
  rw [← physicalLeaf_spec C Q]
  rfl

/-- M3, V4 2.11: every catalogue member projects to its type on its interior. -/
theorem decoration_interior (C : ClusterData S P)
    (Q : {Q // Q ∈ (systemM S P C).physical}) (x : Q.val.carrier)
    (hx : x.val ∈ interior Q.val.carrier) :
    π S P (Q.val.mark x) = some (physicalLeaf C Q).prototype := by
  obtain ⟨Q_val, hQ⟩ := Q
  generalize hl : physicalLeaf C ⟨Q_val, hQ⟩ = l
  have hs : Q_val = augmentedLeaf C l := by
    rw [← hl]
    exact (physicalLeaf_spec C ⟨Q_val, hQ⟩).symm
  subst hs
  exact augmentedMarking_projection C l x.val hx

/-- M3, V4 2.11: every catalogue member projects to @ on its entire frontier. -/
theorem decoration_frontier (C : ClusterData S P)
    (Q : {Q // Q ∈ (systemM S P C).physical}) (x : Q.val.carrier)
    (hx : x.val ∈ frontier Q.val.carrier) : π S P (Q.val.mark x) = none := by
  have h_spec := physicalLeaf_spec C Q
  revert x hx
  rw [← h_spec]
  intro x hx
  have h_bound := augmentedMarking_boundary C (physicalLeaf C Q) x.val hx
  change π S P (augmentedColour C (physicalLeaf C Q) x.val) = none
  rw [h_bound]
  rfl

end Compiler

/-- M3, V4 2.11: exact native decoration and the specified projection π. -/
def nativeDecoration (S : SubstSystem d) (P : Params S) (C : ClusterData S P) :
    NativeDecoration S (systemM S P C) (π S P) where
  ty Q := (Compiler.physicalLeaf C Q).prototype
  carrier_eq := Compiler.decoration_carrier C
  interior_projection := Compiler.decoration_interior C
  frontier_projection := Compiler.decoration_frontier C

namespace Compiler

/-- M3/M5, V4 2.11, 2.13: an isometric augmented leaf is a physical realization.
This helper supplies only catalogue membership and transported marking, with no
rigidity or properness assumption. -/
theorem placedLeaf_realization (C : ClusterData S P) (l : LeafType P) (φ : Iso d) :
    ∃ Q ∈ (systemM S P C).physical, ∃ ψ : Iso d,
      ((augmentedLeaf C l).toMarkedSet.move φ).carrier = placedSet ψ Q.carrier ∧
        ∀ (x : Q.carrier)
          (hx : ψ x ∈ ((augmentedLeaf C l).toMarkedSet.move φ).carrier),
          ((augmentedLeaf C l).toMarkedSet.move φ).mark ⟨ψ x, hx⟩ = Q.mark x := by
  have H : augmentedLeaf C l ∈ (systemM S P C).physical := by
    simp only [systemM, Compiler.physicalCatalogue, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨l, rfl⟩
  refine ⟨augmentedLeaf C l, H, φ, rfl, ?_⟩
  intro x hx
  change (augmentedLeaf C l).toMarkedSet.mark ⟨φ.symm (φ x.val), _⟩ = _
  simp only [φ.symm_apply_apply]

end Compiler

/-- M3/M5, V4 2.11, 2.13: place an actual augmented leaf in its exact frame. -/
def placedLeaf (C : ClusterData S P) (l : LeafType P) (φ : Iso d) :
    PlacedMarkedTile (systemM S P C) where
  toMarkedSet := (augmentedLeaf C l).toMarkedSet.move φ
  realization := Compiler.placedLeaf_realization C l φ

/-- M3/M5, V4 2.11, 2.13: leaf label read from the realizing physical prototype. -/
def compilerLeaf (C : ClusterData S P) (t : PlacedMarkedTile (systemM S P C)) :
    LeafType P := Compiler.physicalLeaf C t.prototype

/-- M3/M5, V4 2.11, 2.13: full Euclidean frame of an augmented physical tile.
Rigidity below proves independence of the catalogue realization used in this choice. -/
def compilerFrame (C : ClusterData S P) (t : PlacedMarkedTile (systemM S P C)) : Iso d :=
  t.placement

/-- M3/M5, V4 2.11, 2.13: decoding realizes the entire placed marked carrier. -/
theorem placedLeaf_decode (C : ClusterData S P)
    (t : PlacedMarkedTile (systemM S P C)) :
    placedLeaf C (compilerLeaf C t) (compilerFrame C t) = t := by
  sorry

/-- M3/M5, V4 2.11, 2.13: augmented physical placements determine label and frame. -/
theorem placedLeaf_injective (C : ClusterData S P) (l u : LeafType P) (φ ψ : Iso d)
    (h : placedLeaf C l φ = placedLeaf C u ψ) : l = u ∧ φ = ψ := by
  exact augmentedLeaf_rigid C l u φ ψ (congrArg PlacedMarkedTile.toMarkedSet h)

/-- M3/M5, V4 2.11, 2.13: the decoded pair is unique, not a representative ambiguity. -/
theorem compiler_decode_unique (C : ClusterData S P) (l : LeafType P) (φ : Iso d) :
    compilerLeaf C (placedLeaf C l φ) = l ∧
      compilerFrame C (placedLeaf C l φ) = φ :=
  placedLeaf_injective C _ _ _ _ (placedLeaf_decode C _)

/-- M4, V4 2.12(i): no CORE microball colour occurs in any EVENT rule. -/
theorem colour_disjointness_i (C : ClusterData S P) (e : Compiler.EventIndex S P)
    (l : LeafType P) (a : Fin (d + 1)) (x : (Compiler.eventRule C e).carrier) :
    (Compiler.eventRule C e).mark x ≠ Colour.core l a := by
  change Compiler.eventColour C e x.val ≠ Colour.core l a
  dsimp [Compiler.eventColour]
  split_ifs with h1 h2
  · intro h
    have h_micro := (augmentedColour_micro_iff C l e.leaf .core a x.val).mp (by exact h)
    have heq : e.leaf = l := h_micro.1
    have h_in_micro := h_micro.2
    have h_in_cluster : x.val ∈ C.cluster e.leaf .core := by
      exact Set.subset_iUnion (fun a => C.microball e.leaf .core a) a (heq ▸ h_in_micro)
    have h_disj := C.cluster_disjoint_enclosing e.leaf .core (.trigger e.slot) (by intro H; cases H)
    exact Set.disjoint_left.mp h_disj h_in_cluster h1
  · intro h
    let z := Classical.choose h2
    have hz_prop := Classical.choose_spec h2
    have h_micro := (augmentedColour_micro_iff C l z.2 .core a (z.1.frame.symm x.val)).mp (by exact h)
    have heq : z.2 = l := h_micro.1
    have h_in_micro := h_micro.2
    have h_in_cluster : z.1.frame.symm x.val ∈ C.cluster z.2 .core := by
      exact Set.subset_iUnion (fun a => C.microball z.2 .core a) a (heq ▸ h_in_micro)
    have h_disj := C.cluster_disjoint_enclosing z.2 .core .readout (by intro H; cases H)
    have h_in_encl : z.1.frame.symm x.val ∈ C.enclosing z.2 .readout := by
      dsimp [Compiler.readoutRegion, placedSet] at hz_prop
      obtain ⟨y, hy1, hy2⟩ := hz_prop.2
      have heq2 : y = z.1.frame.symm x.val := by
        calc y = z.1.frame.symm (z.1.frame y) := by rw [AffineIsometryEquiv.symm_apply_apply]
             _ = z.1.frame.symm x.val := by rw [hy2]
      rwa [← heq2]
    exact Set.disjoint_left.mp h_disj h_in_cluster h_in_encl
  · intro h
    contradiction

/-- M4, V4 2.12(ii): TRIG colours occur in no CORE rule or EVENT readout ball,
and an EVENT occurrence identifies exactly its central leaf and slot.
Heterogeneous slot equality retains the dependent leaf index without a cast. -/
theorem colour_disjointness_ii (C : ClusterData S P) :
    (∀ (D : CertificateSymbol S P) (l : LeafType P) (j : EventSlot l)
      (a : Fin (d + 1)) (x : (Compiler.coreRule C D).carrier),
      (Compiler.coreRule C D).mark x ≠ Colour.trigger l j a) ∧
    (∀ (e : Compiler.EventIndex S P) (z : FramedNode S × LeafType P),
      z ∈ Compiler.eventReadouts e → ∀ (l : LeafType P) (j : EventSlot l)
        (a : Fin (d + 1)) (x : E d), x ∈ Compiler.readoutRegion C z →
        augmentedColour C z.2 (z.1.frame.symm x) ≠ Colour.trigger l j a) ∧
    ∀ (e : Compiler.EventIndex S P) (l : LeafType P) (j : EventSlot l)
      (a : Fin (d + 1)) (x : (Compiler.eventRule C e).carrier),
      (Compiler.eventRule C e).mark x = Colour.trigger l j a →
        e.leaf = l ∧ HEq e.slot j ∧ x.val ∈ C.enclosing e.leaf (.trigger e.slot) := by
  sorry

/-- M4, V4 2.12(iii): a microcolour's locus is precisely one radius-rho ball
in each tile of that leaf type. Distinct tiles' corresponding centres are at
least 2 delta apart. Properness is not needed for this geometric assertion. -/
theorem colour_disjointness_iii (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) (l : LeafType P) (κ : ClusterKind l)
    (a : Fin (d + 1)) :
    {x | Y.marking x = microColour l κ a} =
      ⋃ t : {t : PlacedMarkedTile (systemM S P C) //
        t ∈ Y.tiles ∧ compilerLeaf C t = l},
        closedBall (compilerFrame C t.val (C.centre l κ a)) C.ρ ∧
    ∀ t ∈ Y.tiles, ∀ u ∈ Y.tiles,
      compilerLeaf C t = l → compilerLeaf C u = l → t ≠ u →
      2 * C.δ ≤ dist (compilerFrame C t (C.centre l κ a))
        (compilerFrame C u (C.centre l κ a)) := by
  sorry

/-- Step 1 of the V4 proof of `cluster_rigidity` (V4 2.13): Each source microball ψ(B̄(c_a, ρ))
is connected and coloured (κ,D,i,a) throughout, so it lies in the set of points of Y with that colour. -/
private lemma cluster_rigidity_step1_microball_contained (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) (l : LeafType P) (κ : ClusterKind l) (ψ : Iso d)
    (h : ∀ x ∈ C.cluster l κ, Y.marking (ψ x) = augmentedColour C l x) (a : Fin (d + 1)) :
    ψ '' (C.microball l κ a) ⊆ {x | Y.marking x = microColour l κ a} := by
  sorry

/-- Step 2 of the V4 proof of `cluster_rigidity` (V4 2.13): a connected set lies in one of the
pairwise disjoint closed balls of radius ρ. A closed ball of radius ρ contained in a closed ball of
radius ρ coincides with it. So ψ(c_a) = c'_a, the centre of the a-th microball of the κ-cluster
of some tile t_a of type l. -/
private lemma cluster_rigidity_step2_microball_eq (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) (l : LeafType P) (κ : ClusterKind l) (ψ : Iso d)
    (a : Fin (d + 1)) (hsub : ψ '' (C.microball l κ a) ⊆ {x | Y.marking x = microColour l κ a}) :
    ∃ t ∈ Y.tiles, compilerLeaf C t = l ∧
      ψ (C.centre l κ a) = compilerFrame C t (C.centre l κ a) := by
  sorry

/-- Step 3 of the V4 proof of `cluster_rigidity` (V4 2.13): The d+1 points ψ(c_a) are within
ε < 2δ of each other, while centres in distinct tiles are ≥ 2δ apart; so all t_a equal one tile t.
Within t the cluster of kind κ is unique, so ψ(c_a) = φ_t(c_a) for a = 0, ..., d. -/
private lemma cluster_rigidity_step3_same_tile (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) (l : LeafType P) (κ : ClusterKind l) (ψ : Iso d)
    (h_centers : ∀ a, ∃ t ∈ Y.tiles, compilerLeaf C t = l ∧
      ψ (C.centre l κ a) = compilerFrame C t (C.centre l κ a)) :
    ∃ t ∈ Y.tiles, compilerLeaf C t = l ∧
      ∀ a, ψ (C.centre l κ a) = compilerFrame C t (C.centre l κ a) := by
  sorry

/-- Step 4 of the V4 proof of `cluster_rigidity` (V4 2.13): An isometry is determined by its values
on d+1 affinely independent points, so ψ = φ_t. -/
private lemma cluster_rigidity_step4_affine_span (C : ClusterData S P)
    (l : LeafType P) (κ : ClusterKind l) (ψ φ : Iso d)
    (h_centers : ∀ a, ψ (C.centre l κ a) = φ (C.centre l κ a)) :
    ψ = φ := by
  sorry

/-- M5, V4 2.13: agreement on an entire cluster forces one actual tile of the
exact leaf type in the exact source frame. This applies to every marked tiling,
without properness, and equality is of full isometries, including reflections. -/
theorem cluster_rigidity (C : ClusterData S P) (Y : MarkedTiling (systemM S P C))
    (l : LeafType P) (κ : ClusterKind l) (ψ : Iso d)
    (h : ∀ x ∈ C.cluster l κ, Y.marking (ψ x) = augmentedColour C l x) :
    ∃ t ∈ Y.tiles, compilerLeaf C t = l ∧ ψ = compilerFrame C t := by
  have h1 : ∀ a, ψ '' (C.microball l κ a) ⊆ {x | Y.marking x = microColour l κ a} :=
    fun a => cluster_rigidity_step1_microball_contained C Y l κ ψ h a
  have h2 : ∀ a, ∃ t ∈ Y.tiles, compilerLeaf C t = l ∧
      ψ (C.centre l κ a) = compilerFrame C t (C.centre l κ a) :=
    fun a => cluster_rigidity_step2_microball_eq C Y l κ ψ a (h1 a)
  obtain ⟨t, ht_tiles, ht_leaf, ht_centers⟩ := cluster_rigidity_step3_same_tile C Y l κ ψ h2
  exact ⟨t, ht_tiles, ht_leaf, cluster_rigidity_step4_affine_span C l κ ψ (compilerFrame C t) ht_centers⟩

section MarkedMotion

variable {X : Type} {M : C1System d X}
omit [Fact (2 ≤ d)]

/-- M6, V4 2.14(d): isometric transport of a physical marked tile is realizable. -/
theorem PlacedMarkedTile.move_realization (t : PlacedMarkedTile M) (g : Iso d) :
    ∃ Q ∈ M.physical, ∃ φ : Iso d,
      (t.toMarkedSet.move g).carrier = placedSet φ Q.carrier ∧
        ∀ (x : Q.carrier) (hx : φ x ∈ (t.toMarkedSet.move g).carrier),
          (t.toMarkedSet.move g).mark ⟨φ x, hx⟩ = Q.mark x := by
  obtain ⟨P, hP, φ, hc, hm⟩ := t.realization
  use P, hP, g * φ
  constructor
  · dsimp [MarkedSet.move, placedSet]
    rw [hc]
    exact Set.image_image g φ P.carrier
  · intro x hx
    dsimp [MarkedSet.move]
    have ht_mem : φ x ∈ t.toMarkedSet.carrier := by
      have h1 : g.symm ((g * φ) x) = φ x := g.symm_apply_apply (φ x)
      have h2 : (g * φ) x ∈ (t.toMarkedSet.move g).carrier := hx
      dsimp [MarkedSet.move] at h2
      obtain ⟨y, hy, h_eq⟩ := h2
      have h_eq2 : (g * φ) x = g y := h_eq.symm
      have h_symm : g.symm ((g * φ) x) = y := by rw [h_eq2, g.symm_apply_apply]
      rw [h1] at h_symm
      rw [h_symm]
      exact hy
    have hm_x := hm x ht_mem
    have heq2 : (⟨g.symm (g (φ x)), (by
      obtain ⟨y, hy, he⟩ := hx
      have h_subst : g y = g (φ x) := he
      rw [← h_subst, g.symm_apply_apply]
      exact hy)⟩ : t.toMarkedSet.carrier) = ⟨φ x, ht_mem⟩ := Subtype.ext (g.symm_apply_apply (φ x))
    rw [heq2]
    exact hm_x

/-- M6, V4 2.14(d): actual isometric motion of a marked carrier. -/
def PlacedMarkedTile.move (t : PlacedMarkedTile M) (g : Iso d) : PlacedMarkedTile M where
  toMarkedSet := t.toMarkedSet.move g
  realization := t.move_realization g

/-- M6, V4 2.14(d): moving a marked tiling preserves coverage. -/
theorem MarkedTiling.move_cover (Y : MarkedTiling M) (g : Iso d) (x : E d) :
    ∃ t ∈ (fun t : PlacedMarkedTile M => t.move g) '' Y.tiles, x ∈ t.carrier := by
  obtain ⟨u, hu_tiles, hx_in_u⟩ := Y.cover (g.symm x)
  use u.move g
  refine ⟨Set.mem_image_of_mem _ hu_tiles, ?_⟩
  dsimp [PlacedMarkedTile.move, MarkedSet.move]
  use g.symm x
  exact ⟨hx_in_u, g.apply_symm_apply x⟩

/-- M6, V4 2.14(d): moving a marked tiling preserves interior disjointness. -/
theorem MarkedTiling.move_disjoint (Y : MarkedTiling M) (g : Iso d) :
    ((fun t : PlacedMarkedTile M => t.move g) '' Y.tiles).PairwiseDisjoint
      (fun t => interior t.carrier) := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hneq
  have h_disj := Y.disjoint hu hv (by intro h_eq; apply hneq; rw [h_eq])
  dsimp [Function.onFun] at *
  have hu_c : (u.move g).carrier = g.toHomeomorph '' u.carrier := rfl
  have hv_c : (v.move g).carrier = g.toHomeomorph '' v.carrier := rfl
  rw [hu_c, hv_c]
  rw [← g.toHomeomorph.image_interior, ← g.toHomeomorph.image_interior]
  exact Set.disjoint_image_of_injective g.injective h_disj

/-- M6, V4 2.14(d): moving a marked tiling preserves agreement at every shared point. -/
theorem MarkedTiling.move_agree (Y : MarkedTiling M) (g : Iso d) :
    ∀ t ∈ (fun t : PlacedMarkedTile M => t.move g) '' Y.tiles,
      ∀ u ∈ (fun t : PlacedMarkedTile M => t.move g) '' Y.tiles,
        ∀ x (ht : x ∈ t.carrier) (hu : x ∈ u.carrier), t.mark ⟨x, ht⟩ = u.mark ⟨x, hu⟩ := by
  rintro _ ⟨t, ht, rfl⟩ _ ⟨u, hu, rfl⟩ x hx_t hx_u
  have hxt_orig : g.symm x ∈ t.carrier := by
    obtain ⟨y, hy, heq⟩ := hx_t
    rw [← heq, g.symm_apply_apply]
    exact hy
  have hxu_orig : g.symm x ∈ u.carrier := by
    obtain ⟨y, hy, heq⟩ := hx_u
    rw [← heq, g.symm_apply_apply]
    exact hy
  have h_agree := Y.agreement t ht u hu (g.symm x) hxt_orig hxu_orig
  change t.mark ⟨g.symm x, hxt_orig⟩ = u.mark ⟨g.symm x, hxu_orig⟩
  exact h_agree

/-- M6, V4 2.14(d): the full isometry action on pointwise marked tilings. -/
def MarkedTiling.move (Y : MarkedTiling M) (g : Iso d) : MarkedTiling M where
  tiles := (fun t : PlacedMarkedTile M => t.move g) '' Y.tiles
  cover := Y.move_cover g
  disjoint := Y.move_disjoint g
  agreement := Y.move_agree g

/-- M6, V4 2.14(d): the transported global function has the expected pointwise value. -/
theorem MarkedTiling.move_marking (Y : MarkedTiling M) (g : Iso d) (x : E d) :
    (Y.move g).marking (g x) = Y.marking x := by
  have Hcov := (Y.move g).cover (g x)
  obtain ⟨t, ht, hxt⟩ := Hcov
  rw [MarkedTiling.marking_eq_tile (Y.move g) t ht (g x) hxt]
  dsimp [MarkedTiling.move] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  have hxu : x ∈ u.carrier := by
    dsimp [PlacedMarkedTile.move, MarkedSet.move] at hxt
    obtain ⟨y, hy, heq⟩ := hxt
    have h1 : g y = g x := heq
    have h2 : y = x := g.injective h1
    rwa [h2] at hy
  rw [MarkedTiling.marking_eq_tile Y u hu x hxu]
  dsimp [PlacedMarkedTile.move, MarkedSet.move]
  congr 1
  ext
  simp

/-- M6, V4 2.14(d): properness is invariant under every Euclidean isometry. -/
theorem MProper.move (Y : MarkedTiling M) (hY : MProper Y) (g : Iso d) :
    MProper (Y.move g) := by
  intro x
  obtain ⟨R, hR, ψ, h_mem, h_eq⟩ := hY (g.symm x)
  use R, hR, ψ.trans g
  constructor
  · rw [placedSet] at h_mem ⊢
    obtain ⟨p, hp, hp_eq⟩ := h_mem
    use p, hp
    show g (ψ p) = x
    rw [hp_eq]
    exact AffineIsometryEquiv.apply_symm_apply g x
  · intro p
    have h1 := h_eq p
    have h2 := MarkedTiling.move_marking Y g (ψ p)
    show (Y.move g).marking (g (ψ p)) = R.mark p
    rw [h2]
    exact h1

end MarkedMotion

/-- M6, V4 2.14(d), 1.11: exact isometric transport of an honest source.
The coset is rotated by the orthogonal part of g; parents and globally distinct
roles are retained. These fields generalize the existing `TranslatedSource`. -/
structure MovedSource (U V : HonestSource S) (g : Iso d) : Prop where
  /-- M6, V4 2.14(d): transported physical tiling, with the original partition. -/
  tiling : V.tiling = U.tiling.move g
  /-- M6, V4 2.14(d): transported framed nodes at every height. -/
  nodes : ∀ n, V.hierarchy.nodes n =
    (fun N : FramedNode S => N.move g) '' U.hierarchy.nodes n
  /-- M6, V4 2.14(d): the correctly rotated common frame coset. -/
  coset : V.coset = g.linearIsometryEquiv * U.coset
  /-- M6, V4 2.14(d): exact parent preservation. -/
  parents : ∀ n (N : {N // N ∈ U.hierarchy.nodes n})
    (hN : N.val.move g ∈ V.hierarchy.nodes n),
    (V.hierarchy.parent n ⟨N.val.move g, hN⟩).val =
      (U.hierarchy.parent n N).val.move g
  /-- M6, V4 2.14(d): exact role preservation. -/
  roles : ∀ n (N : {N // N ∈ U.hierarchy.nodes n})
    (hN : N.val.move g ∈ V.hierarchy.nodes n),
    V.hierarchy.nodeRole ⟨n, ⟨N.val.move g, hN⟩⟩ = U.hierarchy.nodeRole ⟨n, N⟩

/-- Step 1 of the V4 proof of `honest_move_exists` (V4 1.11, 2.14(d)): the moved tiling belongs to the species. -/
private lemma honest_move_exists_step1_species (U : HonestSource S) (g : Iso d) :
    U.tiling.move g ∈ S.Species :=
  sorry

/-- Step 2 of the V4 proof of `honest_move_exists` (V4 1.11, 2.14(d)): moving the entire coherent hierarchy preserves coherence. -/
private lemma honest_move_exists_step2_hierarchy (U : HonestSource S) (g : Iso d) :
    ∃ H : CoherentHierarchy S (U.tiling.move g),
      (∀ n, H.nodes n = (fun N : FramedNode S => N.move g) '' U.hierarchy.nodes n) ∧
      (∀ n (N : {N // N ∈ U.hierarchy.nodes n}) (hN : N.val.move g ∈ H.nodes n),
        (H.parent n ⟨N.val.move g, hN⟩).val = (U.hierarchy.parent n N).val.move g) ∧
      (∀ n (N : {N // N ∈ U.hierarchy.nodes n}) (hN : N.val.move g ∈ H.nodes n),
        H.nodeRole ⟨n, ⟨N.val.move g, hN⟩⟩ = U.hierarchy.nodeRole ⟨n, N⟩) :=
  sorry

/-- Step 3 of the V4 proof of `honest_move_exists` (V4 1.11, 2.14(d)): moving a legal context yields a legal context for the moved finite node set. -/
private lemma honest_move_exists_step3_contexts (U : HonestSource S) (g : Iso d)
    (H : CoherentHierarchy S (U.tiling.move g))
    (hNodes : ∀ n, H.nodes n = (fun N : FramedNode S => N.move g) '' U.hierarchy.nodes n)
    (hParents : ∀ n (N : {N // N ∈ U.hierarchy.nodes n}) (hN : N.val.move g ∈ H.nodes n),
        (H.parent n ⟨N.val.move g, hN⟩).val = (U.hierarchy.parent n N).val.move g)
    (hRoles : ∀ n (N : {N // N ∈ U.hierarchy.nodes n}) (hN : N.val.move g ∈ H.nodes n),
        H.nodeRole ⟨n, ⟨N.val.move g, hN⟩⟩ = U.hierarchy.nodeRole ⟨n, N⟩) :
    ∀ F : Finset H.Node, Nonempty (LegalContext H F) :=
  sorry

/-- Step 4 of the V4 proof of `honest_move_exists` (V4 1.11, 2.14(d)): frames of the moved hierarchy lie in the rotated common coset. -/
private lemma honest_move_exists_step4_coset (U : HonestSource S) (g : Iso d)
    (H : CoherentHierarchy S (U.tiling.move g))
    (hNodes : ∀ n, H.nodes n = (fun N : FramedNode S => N.move g) '' U.hierarchy.nodes n)
    (n : ℕ) (N : FramedNode S) (hN : N ∈ H.nodes n) :
    ∃ R ∈ S.rotGroup, N.frame.linearIsometryEquiv =
      (g.linearIsometryEquiv * U.coset) * R :=
  sorry

/-- M6, V4 2.14(d), 1.11: moving every frame and every legal context gives
an honest source. The input source supplies nonemptiness of the transport problem. -/
theorem honest_move_exists (U : HonestSource S) (g : Iso d) :
    ∃ V : HonestSource S, MovedSource U V g := by
  obtain ⟨H, hNodes, hParents, hRoles⟩ := honest_move_exists_step2_hierarchy U g
  let V : HonestSource S := {
    tiling := U.tiling.move g
    mem_species := honest_move_exists_step1_species U g
    hierarchy := H
    contexts := honest_move_exists_step3_contexts U g H hNodes hParents hRoles
    coset := g.linearIsometryEquiv * U.coset
    frames_in_coset := honest_move_exists_step4_coset U g H hNodes
  }
  exact ⟨V, rfl, hNodes, rfl, hParents, hRoles⟩

/-- M6, V4 2.14(d): move an honest source using the exact transport specification.
Only the existing, geometrically specified transported source is selected. -/
def HonestSource.move (U : HonestSource S) (g : Iso d) : HonestSource S :=
  Classical.choose (honest_move_exists U g)

/-- M6, V4 2.14(d): the chosen transport has all prescribed geometric and tree data. -/
theorem HonestSource.move_spec (U : HonestSource S) (g : Iso d) :
    MovedSource U (U.move g) g := Classical.choose_spec (honest_move_exists U g)

/-- M6, V4 2.14(d): exact transport specifies a unique honest source. -/
theorem MovedSource.unique {U V W : HonestSource S} {g : Iso d}
    (hV : MovedSource U V g) (hW : MovedSource U W g) : V = W := by
  sorry

/-- M6, V4 2.14(d): the actual transported hierarchy node, retaining its height. -/
def HonestSource.movedNode (U : HonestSource S) (g : Iso d) (q : U.Node) :
    (U.move g).Node :=
  ⟨q.1, ⟨q.2.val.move g, by
    rw [(U.move_spec g).nodes q.1]
    exact ⟨q.2.val, q.2.property, rfl⟩⟩⟩

/-- M6, V4 2.14(d): general source motion extends the established translation action. -/
theorem HonestSource.move_translation (U : HonestSource S) (v : E d) :
    U.move (translation v) = U.translate v := by
  have h_move : MovedSource U (U.move (translation v)) (translation v) := U.move_spec (translation v)
  have h_trans : TranslatedSource U (U.translate v) v := U.translate_spec v
  apply MovedSource.unique h_move
  constructor
  · exact h_trans.tiling
  · exact h_trans.nodes
  · have h_lin : (translation v).linearIsometryEquiv = 1 := rfl
    rw [h_lin, one_mul]
    exact h_trans.coset
  · exact h_trans.parents
  · exact h_trans.roles


/-- Step 1 of the V4 proof of `move_refl` (V4 2.14(d)): tiling equality -/
private lemma move_refl_step1_tiling (U : HonestSource S) :
    U.tiling = U.tiling.move (AffineIsometryEquiv.refl ℝ (E d)) := by
  have H : ∀ (t : PlacedTile S), t.move (AffineIsometryEquiv.refl ℝ (E d)) = t := by
    intro t
    dsimp [PlacedTile.move]
    have h : AffineIsometryEquiv.trans t.frame (AffineIsometryEquiv.refl ℝ (E d)) = t.frame := by
      ext p
      rfl
    rw [h]
    apply PlacedTile.ext
    · rfl
    · dsimp [PlacedTile.ofFrame]
      rw [t.frame_carrier]
  rcases U.tiling with ⟨T, hT1, hT2⟩
  dsimp [Tiling.move]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · intro h
    use x, h
    exact H x
  · rintro ⟨y, hy, rfl⟩
    rw [H y]
    exact hy

/-- Step 2 of the V4 proof of `move_refl` (V4 2.14(d)): nodes equality -/
private lemma move_refl_step2_nodes (U : HonestSource S) (n : ℕ) :
    U.hierarchy.nodes n = (fun N : FramedNode S => N.move (AffineIsometryEquiv.refl ℝ (E d))) '' U.hierarchy.nodes n := by
  have h_move : ∀ N : FramedNode S, N.move (AffineIsometryEquiv.refl ℝ (E d)) = N := by
    intro N
    ext
    · rfl
    · simp [FramedNode.move]
  rw [show (fun N : FramedNode S => N.move (AffineIsometryEquiv.refl ℝ (E d))) = id from funext h_move, Set.image_id]

/-- Step 3 of the V4 proof of `move_refl` (V4 2.14(d)): coset equality -/
private lemma move_refl_step3_coset (U : HonestSource S) :
    U.coset = (AffineIsometryEquiv.refl ℝ (E d)).linearIsometryEquiv * U.coset := by
  have h_refl : (AffineIsometryEquiv.refl ℝ (E d)).linearIsometryEquiv = 1 := rfl
  rw [h_refl]
  exact one_mul U.coset

/-- Step 4 of the V4 proof of `move_refl` (V4 2.14(d)): parents equality -/
private lemma move_refl_step4_parents (U : HonestSource S) (n : ℕ) (N : {N // N ∈ U.hierarchy.nodes n})
    (hN : N.val.move (AffineIsometryEquiv.refl ℝ (E d)) ∈ U.hierarchy.nodes n) :
    (U.hierarchy.parent n ⟨N.val.move (AffineIsometryEquiv.refl ℝ (E d)), hN⟩).val =
      (U.hierarchy.parent n N).val.move (AffineIsometryEquiv.refl ℝ (E d)) := by
  have key : N.val.move (AffineIsometryEquiv.refl ℝ (E d)) = N.val := by
    dsimp [FramedNode.move]
    ext
    · rfl
    · simp
  have key2 : (⟨N.val.move (AffineIsometryEquiv.refl ℝ (E d)), hN⟩ : {N // N ∈ U.hierarchy.nodes n}) = N := by
    apply Subtype.ext
    exact key
  rw [key2]
  have key3 : (U.hierarchy.parent n N).val.move (AffineIsometryEquiv.refl ℝ (E d)) = (U.hierarchy.parent n N).val := by
    dsimp [FramedNode.move]
    ext
    · rfl
    · simp
  rw [key3]

/-- Step 5 of the V4 proof of `move_refl` (V4 2.14(d)): roles equality -/
private lemma move_refl_step5_roles (U : HonestSource S) (n : ℕ) (N : {N // N ∈ U.hierarchy.nodes n})
    (hN : N.val.move (AffineIsometryEquiv.refl ℝ (E d)) ∈ U.hierarchy.nodes n) :
    U.hierarchy.nodeRole ⟨n, ⟨N.val.move (AffineIsometryEquiv.refl ℝ (E d)), hN⟩⟩ = U.hierarchy.nodeRole ⟨n, N⟩ := by
  have H : N.val.move (AffineIsometryEquiv.refl ℝ (E d)) = N.val := by
    dsimp [FramedNode.move]
    ext
    · rfl
    · simp
  revert hN
  rw [H]
  intro hN
  rfl

/-- Step 6 of the V4 proof of `move_refl` (V4 2.14(d)): moved source equality -/
private lemma move_refl_step6_movedSource (U : HonestSource S) :
    MovedSource U U (AffineIsometryEquiv.refl ℝ (E d)) := by
  constructor
  · exact (move_refl_step1_tiling U)
  · exact (move_refl_step2_nodes U)
  · exact (move_refl_step3_coset U)
  · intro n N hN
    exact (move_refl_step4_parents U n N hN)
  · intro n N hN
    exact (move_refl_step5_roles U n N hN)

/-- M6, V4 2.14(d): identity motion preserves the entire honest hierarchy. -/
theorem HonestSource.move_refl (U : HonestSource S) :
    U.move (AffineIsometryEquiv.refl ℝ (E d)) = U :=
  MovedSource.unique (U.move_spec (AffineIsometryEquiv.refl ℝ (E d))) (move_refl_step6_movedSource U)

open private Tiling.move_move from Enforce.Combinatorics in
/-- Step 1 of the V4 proof of `move_trans` (V4 2.14(d)): transported physical tiling. -/
private lemma move_trans_step1_tiling (U : HonestSource S) (g h : Iso d) :
    ((U.move g).move h).tiling = U.tiling.move (g.trans h) := by
  have H1 := (U.move g).move_spec h
  have H2 := U.move_spec g
  rw [H1.tiling, H2.tiling]
  exact Tiling.move_move U.tiling g h

/-- Step 2 of the V4 proof of `move_trans` (V4 2.14(d)): transported framed nodes. -/
private lemma move_trans_step2_nodes (U : HonestSource S) (g h : Iso d) :
    ∀ n, ((U.move g).move h).hierarchy.nodes n =
      (fun N : FramedNode S => N.move (g.trans h)) '' U.hierarchy.nodes n := by
  intro n
  have key (N : FramedNode S) :
      (N.move g).move h = N.move (g.trans h) := by
    apply FramedNode.ext
    · rfl
    · change (N.frame.trans g).trans h = N.frame.trans (g.trans h)
      exact (AffineIsometryEquiv.trans_assoc N.frame g h).symm
  calc
    ((U.move g).move h).hierarchy.nodes n =
        (fun N : FramedNode S => N.move h) ''
          (U.move g).hierarchy.nodes n :=
      ((U.move g).move_spec h).nodes n
    _ = (fun N : FramedNode S => N.move h) ''
        ((fun N : FramedNode S => N.move g) '' U.hierarchy.nodes n) :=
      congrArg (fun A : Set (FramedNode S) =>
        (fun N : FramedNode S => N.move h) '' A)
        ((U.move_spec g).nodes n)
    _ = (fun N : FramedNode S => (N.move g).move h) ''
        U.hierarchy.nodes n := Set.image_image _ _ _
    _ = (fun N : FramedNode S => N.move (g.trans h)) ''
        U.hierarchy.nodes n :=
      congrArg (fun f : FramedNode S → FramedNode S => f '' U.hierarchy.nodes n) (funext key)

/-- Step 3 of the V4 proof of `move_trans` (V4 2.14(d)): correctly rotated common frame coset. -/
private lemma move_trans_step3_coset (U : HonestSource S) (g h : Iso d) :
    ((U.move g).move h).coset = (g.trans h).linearIsometryEquiv * U.coset := by
  have H1 := (U.move_spec g).coset
  have H2 := ((U.move g).move_spec h).coset
  rw [H2, H1]
  change _ = (h.linearIsometryEquiv * g.linearIsometryEquiv) * U.coset
  rw [mul_assoc]

/-- Step 4 of the V4 proof of `move_trans` (V4 2.14(d)): exact parent preservation. -/
private lemma move_trans_step4_parents (U : HonestSource S) (g h : Iso d) :
    ∀ n (N : {N // N ∈ U.hierarchy.nodes n})
      (hN : N.val.move (g.trans h) ∈ ((U.move g).move h).hierarchy.nodes n),
      (((U.move g).move h).hierarchy.parent n ⟨N.val.move (g.trans h), hN⟩).val =
        (U.hierarchy.parent n N).val.move (g.trans h) := by
  intro n N hN
  have H1 := U.move_spec g
  have H2 := (U.move g).move_spec h
  have h_move : N.val.move (g.trans h) = (N.val.move g).move h := by
    dsimp [FramedNode.move]
    ext x
    · rfl
    · rfl
  have hN_g_nodes : N.val.move g ∈ (U.move g).hierarchy.nodes n := by
    rw [H1.nodes n]
    exact Set.mem_image_of_mem (fun N : FramedNode S => N.move g) N.property
  have hN_h_nodes : (N.val.move g).move h ∈ ((U.move g).move h).hierarchy.nodes n := by
    rw [← h_move]
    exact hN
  have h_parent_move : (((U.hierarchy.parent n N).val).move g).move h = (U.hierarchy.parent n N).val.move (g.trans h) := by
    dsimp [FramedNode.move]
    ext x
    · rfl
    · rfl
  have H2_parent := H2.parents n ⟨N.val.move g, hN_g_nodes⟩ hN_h_nodes
  rw [H1.parents n N hN_g_nodes] at H2_parent
  revert hN
  rw [h_move]
  intro hN
  have hN_eq : hN = hN_h_nodes := rfl
  rw [hN_eq, H2_parent, h_parent_move]


/-- Step 5 of the V4 proof of `move_trans` (V4 2.14(d)): exact role preservation. -/
private lemma move_trans_step5_roles (U : HonestSource S) (g h : Iso d) :
    ∀ n (N : {N // N ∈ U.hierarchy.nodes n})
      (hN : N.val.move (g.trans h) ∈ ((U.move g).move h).hierarchy.nodes n),
      ((U.move g).move h).hierarchy.nodeRole ⟨n, ⟨N.val.move (g.trans h), hN⟩⟩ =
        U.hierarchy.nodeRole ⟨n, N⟩ := by
  intro n N hN
  have H : N.val.move (g.trans h) = (N.val.move g).move h := by
    dsimp [FramedNode.move]
    ext
    · rfl
    · rfl
  
  have step1 := (U.move_spec g).roles n N
  have hNg : N.val.move g ∈ (U.move g).hierarchy.nodes n := by
    have hn := (U.move_spec g).nodes n
    rw [hn]
    exact ⟨N.val, N.property, rfl⟩
  
  have step2 := ((U.move g).move_spec h).roles n ⟨N.val.move g, hNg⟩
  
  revert hN
  rw [H]
  intro hN
  
  have step2_applied := step2 hN
  rw [step2_applied]
  exact step1 hNg

/-- Step 6 of the V4 proof of `move_trans` (V4 2.14(d)): bundled moved source. -/
private lemma move_trans_step6_movedSource (U : HonestSource S) (g h : Iso d) :
    MovedSource U ((U.move g).move h) (g.trans h) :=
  ⟨move_trans_step1_tiling U g h, move_trans_step2_nodes U g h,
   move_trans_step3_coset U g h, move_trans_step4_parents U g h,
   move_trans_step5_roles U g h⟩

/-- M6, V4 2.14(d): successive motions compose on full honest sources. -/
theorem HonestSource.move_trans (U : HonestSource S) (g h : Iso d) :
    (U.move g).move h = U.move (g.trans h) := by
  exact MovedSource.unique (move_trans_step6_movedSource U g h) (U.move_spec (g.trans h))

/-- Step 1 of the V4 proof of `leafTypeOf_move` (V4 2.14(d), 1.11): moving a framed node
by `g` and then by `g⁻¹` returns it. -/
private theorem leafTypeOf_move_step1_move_symm (N : FramedNode S) (g : Iso d) :
    (N.move g).move g.symm = N :=
  FramedNode.ext rfl (by ext x; simp [FramedNode.move])

/-- Step 1 of the V4 proof of `leafTypeOf_move` (V4 2.14(d), 1.11): moving by `g⁻¹` and
then by `g` returns the node. -/
private theorem leafTypeOf_move_step1_symm_move (N : FramedNode S) (g : Iso d) :
    (N.move g.symm).move g = N :=
  FramedNode.ext rfl (by ext x; simp [FramedNode.move])

/-- Step 1 of the V4 proof of `leafTypeOf_move` (V4 2.14(d), 1.11): every node of the
moved source is the motion of a node of the original source. -/
private theorem leafTypeOf_move_step1_inv_mem (U : HonestSource S) (g : Iso d) (n : ℕ)
    (N : FramedNode S) (hN : N ∈ (U.move g).hierarchy.nodes n) :
    N.move g.symm ∈ U.hierarchy.nodes n := by
  rw [(U.move_spec g).nodes n] at hN
  obtain ⟨M, hM, rfl⟩ := hN
  rwa [leafTypeOf_move_step1_move_symm]

/-- Step 1 of the V4 proof of `leafTypeOf_move` (V4 2.14(d), 1.11: "parents ... are
retained"): the parent of a moved node is the moved parent. -/
private theorem leafTypeOf_move_step1_parent (U : HonestSource S) (g : Iso d)
    (q : U.Node) :
    (U.move g).hierarchy.parentNode (U.movedNode g q) =
      U.movedNode g (U.hierarchy.parentNode q) :=
  Sigma.ext rfl (heq_of_eq (Subtype.ext ((U.move_spec g).parents q.1 q.2 _)))

/-- Step 1 of the V4 proof of `leafTypeOf_move` (V4 2.14(d)): the ancestors of a moved
node, in particular its K-ancestor, are the moved ancestors. -/
private theorem leafTypeOf_move_step1_ancestor (U : HonestSource S) (g : Iso d)
    (q : U.Node) (j : ℕ) :
    (U.move g).hierarchy.ancestor (U.movedNode g q) j =
      U.movedNode g (U.hierarchy.ancestor q j) := by
  unfold CoherentHierarchy.ancestor
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      leafTypeOf_move_step1_parent]

/-- Step 1 of the V4 proof of `leafTypeOf_move` (V4 2.14(d), 1.11: "roles are
retained"): a moved node keeps its role. -/
private theorem leafTypeOf_move_step1_role (U : HonestSource S) (g : Iso d) (q : U.Node) :
    (U.move g).hierarchy.nodeRole (U.movedNode g q) = U.hierarchy.nodeRole q :=
  (U.move_spec g).roles q.1 q.2 _

/-- Step 1 of the V4 proof of `leafTypeOf_move` (V4 2.14(d)): the motion is a bijection
of all hierarchy nodes, preserving heights. -/
private def leafTypeOf_move_step1_equiv (U : HonestSource S) (g : Iso d) :
    U.hierarchy.Tail 0 ≃ (U.move g).hierarchy.Tail 0 where
  toFun q := ⟨U.movedNode g q.val, Nat.zero_le _⟩
  invFun q := ⟨⟨q.val.1, ⟨q.val.2.val.move g.symm,
    leafTypeOf_move_step1_inv_mem U g q.val.1 q.val.2.val q.val.2.property⟩⟩, Nat.zero_le _⟩
  left_inv q := Subtype.ext (Sigma.ext rfl (heq_of_eq (Subtype.ext
    (leafTypeOf_move_step1_move_symm q.val.2.val g))))
  right_inv q := Subtype.ext (Sigma.ext rfl (heq_of_eq (Subtype.ext
    (leafTypeOf_move_step1_symm_move q.val.2.val g))))

/-- Step 1 of the V4 proof of `leafTypeOf_move` (V4 2.14(d), with V4 1.13(c) at zero
cutoff): an isometric motion of an honest source is an exact scale transfer with
`a = b = 0` and `J = g`. -/
private def leafTypeOf_move_step1_scale (U : HonestSource S) (g : Iso d) :
    ScaleTailEquiv U (U.move g) 0 0 g where
  toEquiv := leafTypeOf_move_step1_equiv U g
  heights _ := rfl
  types _ := rfl
  frames q := by
    ext x
    simp [leafTypeOf_move_step1_equiv, HonestSource.movedNode, FramedNode.prototypeFrame,
      FramedNode.move]
  parents q := Subtype.ext (leafTypeOf_move_step1_parent U g q.val).symm
  roles q := leafTypeOf_move_step1_role U g q.val
  prototype_sets q K := by
    ext x
    simp [leafTypeOf_move_step1_equiv, HonestSource.movedNode, FramedNode.prototypeFrame,
      FramedNode.move, Set.mem_image]

/-- Step 2 of the V4 proof of `leafTypeOf_move` (V4 2.14(d): "the leaf type of `t` is
intrinsic to the hierarchy"; V4 1.13(c)): states are invariant under motion. -/
private theorem leafTypeOf_move_step2_state (U : HonestSource S) (g : Iso d) (q : U.Node) :
    stateOf (U.move g) P (U.movedNode g q) = stateOf U P q :=
  (state_scaleTransfer P (leafTypeOf_move_step1_scale U g) rfl ⟨q, Nat.zero_le _⟩).symm

/-- Step 3 of the V4 proof of `leafTypeOf_move` (V4 8.1): packets are determined by
incidence, top slot, top state and role word. -/
private theorem leafTypeOf_move_step3_packet_ext {p p' : Packet P}
    (hi : p.incidence = p'.incidence) (hj : p.jstar = p'.jstar) (hs : p.sstar = p'.sstar)
    (hr : ∀ (i : ℕ) (h : i < p.jstar.val) (h' : i < p'.jstar.val),
      p.roles ⟨i, h⟩ = p'.roles ⟨i, h'⟩) : p = p' := by
  obtain ⟨i, j, s, r⟩ := p
  obtain ⟨i', j', s', r'⟩ := p'
  dsimp only at hi hj hs hr
  subst hi hj hs
  congr
  funext ⟨k, hk⟩
  exact hr k hk hk

/-- Step 3 of the V4 proof of `leafTypeOf_move` (V4 2.5, 2.6(a), 8.1): a primitive
occurrence with moved birth node and the same incidence has the same packet. -/
private theorem leafTypeOf_move_step3_packetOf (U : HonestSource S) (g : Iso d)
    (γ : PrimitiveOccurrence U P) (γ' : PrimitiveOccurrence (U.move g) P)
    (hb : γ'.birth = U.movedNode g γ.birth) (hi : γ'.incidence = γ.incidence) :
    packetOf (U.move g) P γ' = packetOf U P γ := by
  have hmask : ∀ j, mask (U.move g) P γ' j ↔ mask U P γ j := fun j => by
    rw [packet_mask_fn, packet_mask_fn, hb, hi, leafTypeOf_move_step2_state]
  have hpres : presentSlots (U.move g) P γ' = presentSlots U P γ := by
    unfold presentSlots
    classical
    exact Finset.filter_congr (fun j _ => hmask j)
  have htop : topSlot (U.move g) P γ' = topSlot U P γ := by
    unfold topSlot
    simp only [hpres]
  have hanc : ∀ j, (U.move g).hierarchy.ancestor γ'.birth j =
      U.movedNode g (U.hierarchy.ancestor γ.birth j) := fun j => by
    rw [hb, leafTypeOf_move_step1_ancestor]
  apply leafTypeOf_move_step3_packet_ext
  · exact hi
  · exact htop
  · show stateOf (U.move g) P ((U.move g).hierarchy.ancestor γ'.birth
        (topSlot (U.move g) P γ').val) =
      stateOf U P (U.hierarchy.ancestor γ.birth (topSlot U P γ).val)
    rw [htop, hanc, leafTypeOf_move_step2_state]
  · intro i _ _
    show (U.move g).hierarchy.nodeRole ((U.move g).hierarchy.ancestor γ'.birth i) =
      U.hierarchy.nodeRole (U.hierarchy.ancestor γ.birth i)
    rw [hanc, leafTypeOf_move_step1_role]

/-- Step 3 of the V4 proof of `leafTypeOf_move` (V4 2.6, 1.13(c)): faults, provider
incidences and birth parents move with the source, hence so do facet packets. -/
private theorem leafTypeOf_move_step3_facetPacket (U : HonestSource S) (g : Iso d)
    (t : U.Node) (f : FacetName S t.2.val.ty) :
    (U.move g).facetPacket P (U.movedNode g t) f = U.facetPacket P t f := by
  let e := leafTypeOf_move_step1_scale U g
  let q : U.hierarchy.Tail 0 := ⟨t, Nat.zero_le _⟩
  unfold HonestSource.facetPacket
  by_cases hf : U.hierarchy.IsFault t f
  · have hg : (U.move g).hierarchy.IsFault (U.movedNode g t) f :=
      (e.faults q f f rfl).mp hf
    rw [dif_pos hf, dif_pos hg]
  · have hg : ¬ (U.move g).hierarchy.IsFault (U.movedNode g t) f :=
      fun h => hf ((e.faults q f f rfl).mpr h)
    rw [dif_neg hf, dif_neg hg]
    congr 1
    have hprov := e.providers q f f rfl hf hg
    have hinc : (U.move g).recordIncidence P (U.movedNode g t) f hg =
        U.recordIncidence P t f hf := by
      have hι : (U.move g).hierarchy.providerIncidence (U.movedNode g t) f hg =
          U.hierarchy.providerIncidence t f hf := hprov.2.2.1.symm
      unfold HonestSource.recordIncidence
      rw [hι]
    have hb : (U.move g).hierarchy.birthParent (U.movedNode g t) f hg =
        U.movedNode g (U.hierarchy.birthParent t f hf) := by
      have hk : ((U.move g).hierarchy.firstProvider (U.movedNode g t) f hg).1 =
          (U.hierarchy.firstProvider t f hf).1 := hprov.1.symm
      unfold CoherentHierarchy.birthParent CoherentHierarchy.servingChild
      rw [hk, leafTypeOf_move_step1_ancestor, leafTypeOf_move_step1_parent]
    exact leafTypeOf_move_step3_packetOf U g _ _ hb hinc

/-- Step 3 of the V4 proof of `leafTypeOf_move` (V4 §2.4): pre-patterns are determined
by type, state and packets. -/
private theorem leafTypeOf_move_step3_prePattern_ext {w w' : PrePattern P}
    (hty : w.ty = w'.ty) (hs : w.state = w'.state) (hp : HEq w.packets w'.packets) :
    w = w' := by
  obtain ⟨ty, fm, hfm, st, hst, pk⟩ := w
  obtain ⟨ty', fm', hfm', st', hst', pk'⟩ := w'
  dsimp only at hty hs hp
  subst hty hfm hfm' hs
  cases hp
  rfl

/-- Step 3 of the V4 proof of `leafTypeOf_move` (V4 §2.4, 2.14(d)): the pre-pattern of
a moved native tile is the same pre-pattern. -/
private theorem leafTypeOf_move_step3_prePattern (U : HonestSource S) (g : Iso d)
    (t : U.Node) (ht : t.1 = 0) (t' : (U.move g).Node) (ht' : t'.1 = 0)
    (h : t' = U.movedNode g t) :
    prePatternOf (U.move g) P t' ht' = prePatternOf U P t ht := by
  subst h
  exact leafTypeOf_move_step3_prePattern_ext rfl (leafTypeOf_move_step2_state U g t)
    (heq_of_eq (funext fun f => leafTypeOf_move_step3_facetPacket U g t f))

/-- Step 4 of the V4 proof of `leafTypeOf_move` (V4 2.7): standard descendants of a moved
node are the moved descendants. -/
private theorem leafTypeOf_move_step4_descendant (U : HonestSource S) (g : Iso d)
    (q : U.Node) (a : ℕ) (ha : a ≤ q.1) (w : S.RoleWord q.2.val.ty a) :
    (U.move g).descendant (U.movedNode g q) a ha w = U.movedNode g (U.descendant q a ha w) :=
  Sigma.ext rfl (heq_of_eq (Subtype.ext (FramedNode.ext rfl (by
    ext x
    simp [HonestSource.descendant, HonestSource.movedNode, FramedNode.move]))))

/-- Step 4 of the V4 proof of `leafTypeOf_move` (V4 2.7): certificates are determined by
their type, leaf pre-patterns and state table. -/
private theorem leafTypeOf_move_step4_cert_ext {D D' : Certificate P}
    (hty : D.ty = D'.ty) (hl : HEq D.leaves D'.leaves) (ht : HEq D.table D'.table) :
    D = D' := by
  obtain ⟨ty, l, lt, t, tt⟩ := D
  obtain ⟨ty', l', lt', t', tt'⟩ := D'
  dsimp only at hty hl ht
  subst hty
  cases hl
  cases ht
  rfl

/-- Step 4 of the V4 proof of `leafTypeOf_move` (V4 2.7, 2.14(d): "the leaf type of `t`
is intrinsic to the hierarchy"): the joint certificate of a moved K-node is unchanged. -/
private theorem leafTypeOf_move_step4_cert (U : HonestSource S) (g : Iso d)
    (B : FramedNode S) (hB : B ∈ U.hierarchy.nodes P.K) (B' : FramedNode S)
    (hB' : B' ∈ (U.move g).hierarchy.nodes P.K) (hBB : B' = B.move g) :
    certOf (U.move g) P B' hB' = certOf U P B hB := by
  subst hBB
  refine leafTypeOf_move_step4_cert_ext (D := certOf (U.move g) P (B.move g) hB')
    (D' := certOf U P B hB) rfl ?_ ?_
  · refine heq_of_eq (funext fun w => ?_)
    exact leafTypeOf_move_step3_prePattern U g _ (Nat.sub_self P.K) _ (Nat.sub_self P.K)
      (leafTypeOf_move_step4_descendant U g ⟨P.K, ⟨B, hB⟩⟩ P.K le_rfl w)
  · refine heq_of_eq (funext fun a => funext fun ha => funext fun w => ?_)
    show stateOf (U.move g) P ((U.move g).descendant ⟨P.K, ⟨B.move g, hB'⟩⟩ a ha w) =
      stateOf U P (U.descendant ⟨P.K, ⟨B, hB⟩⟩ a ha w)
    exact (congrArg (stateOf (U.move g) P)
      (leafTypeOf_move_step4_descendant U g ⟨P.K, ⟨B, hB⟩⟩ a ha w)).trans
        (leafTypeOf_move_step2_state U g _)

/-- Step 5 of the V4 proof of `leafTypeOf_move` (V4 2.7, 2.14(d): "the exact leaf
address"): the unique role word placing the moved tile below the moved K-node is the
original role word. -/
private theorem leafTypeOf_move_step5_leafIndex (g : Iso d) (X Y t : FramedNode S)
    (hXY : X = Y.move g) (w' : S.RoleWord X.ty P.K) (w : S.RoleWord Y.ty P.K)
    (h' : (S.nativeTile X.ty P.K w').move X.frame = t.move g)
    (huniq : ∀ v : S.RoleWord Y.ty P.K, (S.nativeTile Y.ty P.K v).move Y.frame = t → v = w) :
    HEq w' w := by
  subst hXY
  refine heq_of_eq (huniq w' ?_)
  have e1 : ((S.nativeTile Y.ty P.K w').move Y.frame).move g = t.move g := by
    rw [← h']
    exact FramedNode.ext rfl (by ext x; simp [FramedNode.move])
  calc (S.nativeTile Y.ty P.K w').move Y.frame
      = (((S.nativeTile Y.ty P.K w').move Y.frame).move g).move g.symm :=
        (leafTypeOf_move_step1_move_symm _ g).symm
    _ = (t.move g).move g.symm := by rw [e1]
    _ = t := leafTypeOf_move_step1_move_symm t g

/-- M6, V4 2.14(d): leaf types are intrinsic to the hierarchy under all isometries.
The equality includes the whole joint certificate and the exact leaf address. -/
theorem leafTypeOf_move (U : HonestSource S) (g : Iso d) (q : U.Node) (hq : q.1 = 0) :
    leafTypeOf (U.move g) P (U.movedNode g q) hq = leafTypeOf U P q hq := by
  have hanc := leafTypeOf_move_step1_ancestor U g q P.K
  have hX : ((U.move g).hierarchy.ancestor (U.movedNode g q) P.K).2.val =
      (U.hierarchy.ancestor q P.K).2.val.move g := by rw [hanc]; rfl
  unfold leafTypeOf
  apply Sigma.ext
  · apply Subtype.ext
    exact leafTypeOf_move_step4_cert U g _ (U.certificateAncestor_mem P q hq) _ _ hX
  · exact leafTypeOf_move_step5_leafIndex g _ _ q.2.val hX _ _
      (Classical.choose_spec ((U.move g).leafIndex_exists P (U.movedNode g q) hq)).1
      (Classical.choose_spec (U.leafIndex_exists P q hq)).2

namespace Compiler

/-- M6, V4 2.14: native hierarchy nodes with their specified ground frames. -/
abbrev GroundNode (U : HonestSource S) := {t // t ∈ U.hierarchy.nodes 0}

/-- M6, V4 2.14: mark an actual native source tile as its actual augmented leaf. -/
def honestTile (C : ClusterData S P) (U : HonestSource S) (t : GroundNode U) :
    PlacedMarkedTile (systemM S P C) :=
  placedLeaf C (leafTypeOf U P ⟨0, t⟩ rfl) t.val.frame

/-- M6, V4 2.14: exactly the native tiles of the source, with their augmented markings. -/
def honestLiftTiles (C : ClusterData S P) (U : HonestSource S) :
    Set (PlacedMarkedTile (systemM S P C)) := Set.range (honestTile C U)

/-- M6, V4 2.14: each lifted tile has exactly its source tile's carrier. -/
theorem honestTile_carrier (C : ClusterData S P) (U : HonestSource S) (t : GroundNode U) :
    (honestTile C U t).carrier = t.val.toTile.carrier := by
  dsimp [honestTile, placedLeaf, augmentedLeaf, FramedNode.toTile]
  show (MarkedSet.move _ t.val.frame).carrier = (PlacedTile.ofFrame _ _).carrier
  dsimp [MarkedSet.move, PlacedTile.ofFrame, placedSet]
  congr 3
  exact leafTypeOf_type U P ⟨0, t.val, t.property⟩ rfl

open private exists_honest_step7_zero_carrier from Enforce.Tiling in
/-- M6, V4 2.14: the proposed lift covers the whole space by source ground coverage. -/
theorem honestLift_cover (C : ClusterData S P) (U : HonestSource S) (x : E d) :
    ∃ t ∈ honestLiftTiles C U, x ∈ t.carrier := by
  obtain ⟨N, hN, hx⟩ := U.hierarchy.cover 0 x
  let t : GroundNode U := ⟨N, hN⟩
  use honestTile C U t
  constructor
  · exact Set.mem_range_self t
  · rw [honestTile_carrier C U t]
    rw [← exists_honest_step7_zero_carrier]
    exact hx

open private exists_honest_step7_zero_carrier from Enforce.Tiling in
/-- M6, V4 2.14: the proposed lifted physical tiles have disjoint interiors. -/
theorem honestLift_disjoint (C : ClusterData S P) (U : HonestSource S) :
    (honestLiftTiles C U).PairwiseDisjoint (fun t => interior t.carrier) := by
  rintro _ ⟨t1, rfl⟩ _ ⟨t2, rfl⟩ hne
  have ht1_c : (honestTile C U t1).carrier = t1.val.toTile.carrier :=
    honestTile_carrier C U t1
  have ht2_c : (honestTile C U t2).carrier = t2.val.toTile.carrier :=
    honestTile_carrier C U t2
  dsimp only [Function.onFun]
  rw [ht1_c, ht2_c]
  have hne_val : t1.val ≠ t2.val := by
    intro h
    apply hne
    congr 1
    apply Subtype.ext
    exact h
  have ht_c1 : t1.val.toTile.carrier = t1.val.carrier 0 := (exists_honest_step7_zero_carrier t1.val).symm
  have ht_c2 : t2.val.toTile.carrier = t2.val.carrier 0 := (exists_honest_step7_zero_carrier t2.val).symm
  rw [ht_c1, ht_c2]
  exact U.hierarchy.disjoint 0 t1.property t2.property hne_val

end Compiler

/-- M6, V4 2.14(a): all shared points in the proposed lift have agreeing markings.
In particular tile boundaries carry @. This theorem precedes `honestLift`, so
no proof hole is hidden in that definition's agreement field. -/
theorem honestLift_agree (C : ClusterData S P) (U : HonestSource S) :
    ∀ t ∈ Compiler.honestLiftTiles C U, ∀ u ∈ Compiler.honestLiftTiles C U,
      ∀ x (ht : x ∈ t.carrier) (hu : x ∈ u.carrier), t.mark ⟨x, ht⟩ = u.mark ⟨x, hu⟩ := by
  sorry

/-- M6, V4 2.14: the actual marked tiling on the native partition of an honest source.
The tile set is defined before its cover, disjointness and agreement theorems. -/
def honestLift (C : ClusterData S P) (U : HonestSource S) :
    MarkedTiling (systemM S P C) where
  tiles := Compiler.honestLiftTiles C U
  cover := Compiler.honestLift_cover C U
  disjoint := Compiler.honestLift_disjoint C U
  agreement := honestLift_agree C U

/-- M6, V4 2.14(a): every source tile appears with its exact hierarchy label and frame. -/
theorem honestLift_tile (C : ClusterData S P) (U : HonestSource S)
    (t : Compiler.GroundNode U) :
    Compiler.honestTile C U t ∈ (honestLift C U).tiles := ⟨t, rfl⟩

/-- M6, V4 2.14(a): ground label and frame readouts of the honest lift are exact. -/
theorem honestLift_tile_data (C : ClusterData S P) (U : HonestSource S)
    (t : Compiler.GroundNode U) :
    compilerLeaf C (Compiler.honestTile C U t) = leafTypeOf U P ⟨0, t⟩ rfl ∧
      compilerFrame C (Compiler.honestTile C U t) = t.val.frame :=
  compiler_decode_unique C _ _

/-- M6, V4 2.14(a),(c): forgetting augmented markings preserves the exact typed tiling. -/
theorem honestLift_tiles (C : ClusterData S P) (U : HonestSource S) :
    (honestLift C U).project (nativeDecoration S P C) = U.tiling := by
  have key : ∀ T1 T2 : Tiling S, T1.tiles = T2.tiles → T1 = T2 := by
    rintro ⟨a, ca, da⟩ ⟨b, cb, db⟩ h
    cases h
    rfl
  have h_tiles : ((honestLift C U).project (nativeDecoration S P C)).tiles = U.tiling.tiles := by
    dsimp [MarkedTiling.project]
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      dsimp [honestLift, Compiler.honestLiftTiles] at hv
      obtain ⟨t, rfl⟩ := hv
      have ht : PlacedMarkedTile.native (nativeDecoration S P C) (Compiler.honestTile C U t) = t.val.toTile := by
        apply PlacedTile.ext
        · have h1 : (PlacedMarkedTile.native (nativeDecoration S P C) (Compiler.honestTile C U t)).ty = (compilerLeaf C (Compiler.honestTile C U t)).prototype := rfl
          have h2 := (honestLift_tile_data C U t).1
          have hl := leafTypeOf_type U P ⟨0, t.val, t.property⟩ rfl
          rw [h1, h2, hl]
          rfl
        · rw [PlacedMarkedTile.native_carrier (nativeDecoration S P C) (Compiler.honestTile C U t)]
          exact Compiler.honestTile_carrier C U t
      show PlacedMarkedTile.native (nativeDecoration S P C) (Compiler.honestTile C U t) ∈ U.tiling.tiles
      rw [ht]
      have hground := U.hierarchy.ground
      rw [← hground]
      exact ⟨t.val, t.property, rfl⟩
    · intro hu
      have hu' : u ∈ {t | ∃ N ∈ U.hierarchy.nodes 0, N.toTile = t} := by
        have hground := U.hierarchy.ground
        rw [hground]
        exact hu
      obtain ⟨N, hN, rfl⟩ := hu'
      let t : Compiler.GroundNode U := ⟨N, hN⟩
      refine ⟨Compiler.honestTile C U t, ?_, ?_⟩
      · exact ⟨t, rfl⟩
      · show PlacedMarkedTile.native (nativeDecoration S P C) (Compiler.honestTile C U t) = N.toTile
        apply PlacedTile.ext
        · have h1 : (PlacedMarkedTile.native (nativeDecoration S P C) (Compiler.honestTile C U t)).ty = (compilerLeaf C (Compiler.honestTile C U t)).prototype := rfl
          have h2 := (honestLift_tile_data C U t).1
          have hl := leafTypeOf_type U P ⟨0, t.val, t.property⟩ rfl
          rw [h1, h2, hl]
          rfl
        · rw [PlacedMarkedTile.native_carrier (nativeDecoration S P C) (Compiler.honestTile C U t)]
          exact Compiler.honestTile_carrier C U t
  exact key _ _ h_tiles

/-- M6, V4 2.14(b): the honest lift is proper, by CORE coverage and honest event rows. -/
theorem honestLift_proper (C : ClusterData S P) (U : HonestSource S) :
    MProper (honestLift C U) := by
  sorry

/-- M6, V4 2.14(c): exact old marking at every point, including the boundary skeleton. -/
theorem honestLift_projection (C : ClusterData S P) (U : HonestSource S) (x : E d) :
    π S P ((honestLift C U).marking x) = oldMarking U.tiling x := by
  rw [← honestLift_tiles C U]
  exact (honestLift C U).project_marking (nativeDecoration S P C) x

/-- M6, V4 2.14(c): pointwise projection also as equality of total functions. -/
theorem honestLift_projection_eq (C : ClusterData S P) (U : HonestSource S) :
    π S P ∘ (honestLift C U).marking = oldMarking U.tiling :=
  funext (honestLift_projection C U)

/-- M6, V4 2.14(d): covariance as equality of full physical marked tilings.
The motion uses all Euclidean isometries, including reflections. -/
theorem honestLift_covariant (C : ClusterData S P) (U : HonestSource S) (g : Iso d) :
    honestLift C (U.move g) = (honestLift C U).move g := by
  sorry

/-- M6, V4 2.14(d): the compiler marking meets the existing section lemma's
translation-covariance hypothesis on the whole honest class. -/
theorem honestLift_translationCovariant (C : ClusterData S P) :
    TranslationCovariant (fun U : HonestSource S => (honestLift C U).marking) := by
  intro U v x
  have hx : x + v = translation v x := rfl
  have h1 : honestLift C (U.translate v) = (honestLift C U).move (translation v) := by
    rw [← HonestSource.move_translation U v]
    exact honestLift_covariant C U (translation v)
  change (honestLift C (U.translate v)).marking (x + v) = (honestLift C U).marking x
  rw [h1, hx]
  exact MarkedTiling.move_marking (honestLift C U) (translation v) x

/-- M7, V4 2.15: complete closed normalized patterns over all honest sources.
DEVIATION: the same definition includes height zero, for the all-height requests
in V4 1.27. At every positive height this is exactly Definition 2.15. -/
def sourceLanguage (C : ClusterData S P) (n : ℕ) (A : S.ι) :
    Set (Pattern S (Colour S P) n A) :=
  {q | ∃ (U : HonestSource S) (φ : Iso d),
    (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n ∧
      q = normalisedPattern (honestLift C U) n A φ}

/-- M7, V4 2.15: the compiler's language is the existing honest-language interface. -/
theorem sourceLanguage_eq_honestLanguage (C : ClusterData S P) (n : ℕ) (A : S.ι) :
    sourceLanguage C n A =
      honestLanguage (fun U : HonestSource S => (honestLift C U).marking) n A := rfl

/-- M7, V4 2.15: an actual source node witnesses language membership.
This records nonvacuity whenever the specified source node exists. -/
theorem normalisedPattern_mem_sourceLanguage (C : ClusterData S P) (U : HonestSource S)
    (n : ℕ) (A : S.ι) (φ : Iso d)
    (hN : (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n) :
    normalisedPattern (honestLift C U) n A φ ∈ sourceLanguage C n A :=
  ⟨U, φ, hN, rfl⟩

/-- M7, V4 2.16: leaf-type tuple in the fixed depth-n native role-word order.
The definition uses actual descendants of the chosen framed source node. -/
def sourceLeafTypes (U : HonestSource S) (P : Params S) (n : ℕ) (A : S.ι) (φ : Iso d)
    (hN : (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n) :
    S.RoleWord A n → LeafType P :=
  fun w => leafTypeOf U P (U.descendant ⟨n, ⟨⟨A, φ⟩, hN⟩⟩ n le_rfl w) (Nat.sub_self n)

/-- M7, V4 2.16: leaf tuples have the prototype prescribed at each native address. -/
theorem sourceLeafTypes_type (U : HonestSource S) (P : Params S)
    (n : ℕ) (A : S.ι) (φ : Iso d)
    (hN : (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n) (w : S.RoleWord A n) :
    (sourceLeafTypes U P n A φ hN w).prototype = (S.nativeTile A n w).ty := by
  dsimp [sourceLeafTypes]
  rw [leafTypeOf_type]
  exact HonestSource.descendant_type U ⟨n, ⟨⟨A, φ⟩, hN⟩⟩ n le_rfl w

/-- M7, V4 2.16: render an arbitrary finite leaf tuple in the fixed native positions.
Actual source tuples have the required prototype at each address. The total ambient
extension of each augmented marking makes this a function even on other tuples;
only actual source tuples are identified with source patterns below. -/
def renderLeafTuple (C : ClusterData S P) (n : ℕ) (A : S.ι)
    (labels : S.RoleWord A n → LeafType P) : Pattern S (Colour S P) n A := by
  classical
  exact fun x => if h : ∃ w : S.RoleWord A n,
      x.val ∈ placedSet (S.nativeTile A n w).frame
        (S.proto (S.nativeTile A n w).ty).carrier then
    let w := Classical.choose h
    augmentedColour C (labels w) ((S.nativeTile A n w).frame.symm x.val)
    else .boundary

/-- M7, V4 2.16: the complete source pattern is the rendering of its leaf tuple.
This is equality on the entire closed supertile, so boundary values are retained. -/
theorem renderLeafTuple_source (C : ClusterData S P) (U : HonestSource S)
    (n : ℕ) (A : S.ι) (φ : Iso d)
    (hN : (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n) :
    normalisedPattern (honestLift C U) n A φ =
      renderLeafTuple C n A (sourceLeafTypes U P n A φ hN) := by
  sorry

/-- M7, V4 2.16: the source language lies in the image of one finite tuple space. -/
theorem sourceLanguage_subset_render (C : ClusterData S P) (n : ℕ) (A : S.ι) :
    sourceLanguage C n A ⊆ Set.range (renderLeafTuple C n A) := by
  rintro q ⟨U, φ, hN, rfl⟩
  exact ⟨sourceLeafTypes U P n A φ hN, (renderLeafTuple_source C U n A φ hN).symm⟩

/-- M7, V4 2.16: equal role-indexed leaf-type tuples determine equal complete
patterns, even across distinct honest sources, nodes, and ambient frames. -/
theorem pattern_determined_by_leafTypes (C : ClusterData S P) (U V : HonestSource S)
    (n : ℕ) (A : S.ι) (φ ψ : Iso d)
    (hN : (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n)
    (hM : (⟨A, ψ⟩ : FramedNode S) ∈ V.hierarchy.nodes n)
    (h : sourceLeafTypes U P n A φ hN = sourceLeafTypes V P n A ψ hM) :
    normalisedPattern (honestLift C U) n A φ =
      normalisedPattern (honestLift C V) n A ψ := by
  rw [renderLeafTuple_source C U n A φ hN, renderLeafTuple_source C V n A ψ hM, h]

/-- M7, V4 2.16: finitely many complete normalized patterns at each height and type.
The statement also holds at height zero under the extension documented at 2.15. -/
theorem sourceLanguage_finite (C : ClusterData S P) (n : ℕ) (A : S.ι) :
    (sourceLanguage C n A).Finite :=
  (Set.finite_range (renderLeafTuple C n A)).subset (sourceLanguage_subset_render C n A)

/-- M7, V4 2.15, Theorem F(2): emptiness is exactly absence of an honest node.
No global existence of a tiling is presumed. -/
theorem sourceLanguage_eq_empty_iff (C : ClusterData S P) (n : ℕ) (A : S.ι) :
    sourceLanguage C n A = ∅ ↔ ¬ ∃ (U : HonestSource S) (φ : Iso d),
      (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n := by
  rw [sourceLanguage_eq_honestLanguage]
  exact honestLanguage_eq_empty_iff (fun U => (honestLift C U).marking) n A


/-- M8, V4 2.17(a): a placed whole certificate with every prescribed leaf actual.
The certificate belongs to the joint honest catalogue. Its entire S-table is thus
retained. Identity includes certificate and frame; subdivision proofs are irrelevant.
The definition requires no pre-existing hierarchy on the output. -/
@[ext]
structure KBlock {C : ClusterData S P} (Y : MarkedTiling (systemM S P C)) where
  /-- M8, V4 2.17(a): the full honest certificate, including its S-table. -/
  certificate : CertificateSymbol S P
  /-- M8, V4 2.17(a): the isometric frame on the standard height-K supertile. -/
  frame : Iso d
  /-- M8, V4 2.17(a): all leaf labels and frames occur as actual physical marked tiles. -/
  leaves_actual : ∀ w : S.RoleWord certificate.val.ty P.K,
    placedLeaf C (⟨certificate, w⟩ : LeafType P)
      ((LeafType.position (⟨certificate, w⟩ : LeafType P)).trans frame) ∈ Y.tiles

namespace KBlock

variable {C : ClusterData S P} {Y : MarkedTiling (systemM S P C)} (B : KBlock Y)

/-- M8, V4 2.17(a): the root type and frame as an ordinary height-K node. -/
def node : FramedNode S := ⟨B.certificate.val.ty, B.frame⟩

/-- M8, V4 2.17(a): the placed closed height-K carrier. -/
def carrier : Set (E d) := B.node.carrier P.K

/-- M8, V4 2.17(a): a prescribed actual leaf at its exact native address. -/
def leaf (w : S.RoleWord B.certificate.val.ty P.K) :
    PlacedMarkedTile (systemM S P C) :=
  placedLeaf C (⟨B.certificate, w⟩ : LeafType P)
    ((LeafType.position (⟨B.certificate, w⟩ : LeafType P)).trans B.frame)

/-- M8, V4 2.17(a): each prescribed leaf is a tile of the fixed output. -/
theorem leaf_mem (w : S.RoleWord B.certificate.val.ty P.K) : B.leaf w ∈ Y.tiles :=
  B.leaves_actual w

/-- M8, V4 2.17(a): union of all native leaf carriers is exactly the whole block. -/
theorem union_leaves :
    (⋃ w : S.RoleWord B.certificate.val.ty P.K, (B.leaf w).carrier) = B.carrier := by
  have key : ∀ w : S.RoleWord B.certificate.val.ty P.K, (B.leaf w).carrier =
      placedSet B.frame ((S.nativeTile B.certificate.val.ty P.K w).carrier 0) := by
    intro w
    show placedSet ((LeafType.position (⟨B.certificate, w⟩ : LeafType P)).trans B.frame)
      (S.proto (LeafType.prototype (⟨B.certificate, w⟩ : LeafType P))).carrier = _
    simp only [FramedNode.carrier, placedSet, SubstSystem.supertile, pow_zero,
      LinearEquiv.coe_one, Set.image_id, LeafType.position, LeafType.prototype,
      AffineIsometryEquiv.coe_trans, Set.image_comp]
  simp_rw [key]
  show (⋃ w, placedSet B.frame _) = placedSet B.frame (S.supertile P.K B.certificate.val.ty)
  rw [← S.native_cover]
  simp only [placedSet, Set.image_iUnion]

/-- M8, V4 2.17(a): actual tiles contained in a block are exactly its native leaves. -/
theorem tiles_exact :
    {t | t ∈ Y.tiles ∧ t.carrier ⊆ B.carrier} = Set.range B.leaf := by
  sorry

/-- M8, V4 2.17(a): every inner node, positioned by the fixed standard subdivision. -/
def innerNode (a : ℕ) (_ha : a ≤ P.K) (w : S.RoleWord B.certificate.val.ty a) :
    FramedNode S :=
  (S.descendantNode B.certificate.val.ty (P.K - a) a w).move B.frame

/-- M8, V4 2.17(a): the honest S-table of the certificate, with all depths retained. -/
def table (a : ℕ) (ha : a ≤ P.K) (w : S.RoleWord B.certificate.val.ty a) : State P :=
  B.certificate.val.table a ha w

/-- M8, V4 2.17(a): the entire joint table and leaf data have an honest source witness. -/
theorem honest_table :
    ∃ (U : HonestSource S) (N : FramedNode S) (hN : N ∈ U.hierarchy.nodes P.K),
      certOf U P N hN = B.certificate.val := B.certificate.property

/-- M8, V4 2.17(a): all decoded inner states lie in the honest state alphabet. -/
theorem table_mem (a : ℕ) (ha : a ≤ P.K) (w : S.RoleWord B.certificate.val.ty a) :
    B.table a ha w ∈ honestStates S P :=
  (certificate_components_honest P B.certificate.val B.certificate.property).2 a ha w

/-- M8, V4 2.17(a): each child equation of the retained S-table, with exact roles. -/
theorem table_child (a : ℕ) (ha : a + 1 ≤ P.K)
    (w : S.RoleWord B.certificate.val.ty a)
    (i : S.I (S.nativeTile B.certificate.val.ty a w).ty) :
    ∃ w' : S.RoleWord B.certificate.val.ty (a + 1),
      prototypeDescendantFrame B.certificate.val.ty (a + 1) w' =
        (rolePlacement (⟨(S.nativeTile B.certificate.val.ty a w).ty, i⟩ : S.Role)).trans
          (prototypeDescendantFrame B.certificate.val.ty a w) ∧
      B.table (a + 1) ha w' = childMap P (B.table a (by omega) w)
        ⟨(S.nativeTile B.certificate.val.ty a w).ty, i⟩ :=
  certificate_child_equations P B.certificate.val B.certificate.property a ha w i

end KBlock

/-- Step 1 of the V4 proof of `compiler_certificates` (V4 2.17(a), using 2.12(i)): "Let x be
the centre of the CORE microball a=0 of t; λ_Y(x)=(CORE,D,i,0). Some rule copy ψ(Λ,m) covers x
with m=λ_Y∘ψ on Λ. By Lemma 2.12(i) it is a CORE rule, CORE_{D'}, whose marking takes the value
(CORE,D,i,0) at ψ⁻¹(x); CORE colours in CORE_{D'} are (CORE,D',i',a), so D'=D", and that colour
occurs in CORE_D only on the microball 0 of leaf i. So some copy of CORE_D agrees with Y and
ψ⁻¹(x) lies in the native image of the CORE microball 0 of leaf i. -/
private lemma compiler_certificates_step1_core_rule (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles) :
    ∃ ψ : Iso d,
      (∀ p : (Compiler.coreRule C (compilerLeaf C t).1).carrier,
        Y.marking (ψ p) = (Compiler.coreRule C (compilerLeaf C t).1).mark p) ∧
      ψ.symm (compilerFrame C t (C.centre (compilerLeaf C t) .core 0)) ∈
        placedSet (compilerLeaf C t).position (C.microball (compilerLeaf C t) .core 0) := by
  set l := compilerLeaf C t with hl_def
  set x := compilerFrame C t (C.centre l .core 0) with hx_def
  have hxm : Y.marking x = Colour.core l 0 := by
    have hmem : x ∈ {x | Y.marking x = microColour l .core 0} := by
      rw [(colour_disjointness_iii C Y l .core 0).1]
      exact Set.mem_iUnion.mpr ⟨⟨t, ht, rfl⟩, Metric.mem_closedBall_self C.ρ_pos.le⟩
    exact hmem
  obtain ⟨R, hR, ψ, hxR, hcons⟩ := hY x
  obtain ⟨q, hq, hqx⟩ := hxR
  have hR' : R ∈ Compiler.ruleCatalogue C := hR
  simp only [Compiler.ruleCatalogue, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and] at hR'
  rcases hR' with ⟨D', rfl⟩ | ⟨e, rfl⟩
  · have hc : Y.marking (ψ q) = _ := hcons ⟨q, hq⟩
    rw [hqx, hxm] at hc
    have hc' : Compiler.certificateColour C D' q = Colour.core l 0 := hc.symm
    unfold Compiler.certificateColour at hc'
    split_ifs at hc' with hex
    · have hmi := (augmentedColour_micro_iff C l _ .core 0 _).1 hc'
      obtain ⟨hl, hqm⟩ := hmi
      have hD : D' = l.1 := congrArg Sigma.fst hl
      subst hD
      refine ⟨ψ, hcons, ?_⟩
      have hpos : LeafType.position (⟨l.1, Classical.choose hex⟩ : LeafType P) =
          l.position := by rw [hl]
      rw [hpos] at hqm
      rw [← hqx, AffineIsometryEquiv.symm_apply_apply]
      exact ⟨_, hqm, AffineIsometryEquiv.apply_symm_apply _ _⟩
  · exfalso
    have hc := hcons ⟨q, hq⟩
    rw [hqx, hxm] at hc
    exact colour_disjointness_i C e l 0 ⟨q, hq⟩ hc.symm

/-- Step 2 of the V4 proof of `compiler_certificates` (V4 2.17(a)): "The carrier Λ_D contains
the entire CORE cluster of leaf i (CORE balls are disjoint from trigger balls)". -/
private lemma compiler_certificates_step2_core_cluster_inside (C : ClusterData S P)
    (D : CertificateSymbol S P) (w : S.RoleWord D.val.ty P.K) :
    placedSet (LeafType.position (⟨D, w⟩ : LeafType P))
      (C.cluster (⟨D, w⟩ : LeafType P) .core) ⊆ Compiler.coreCarrier C D := by
  have hsup0 : ∀ A : S.ι, S.supertile 0 A = (S.proto A).carrier := by
    intro A; simp [SubstSystem.supertile]
  have hint : ∀ (v : S.RoleWord D.val.ty P.K) (y : E d),
      y ∈ interior (S.proto (S.nativeTile D.val.ty P.K v).ty).carrier →
      (S.nativeTile D.val.ty P.K v).frame y ∈
        interior ((S.nativeTile D.val.ty P.K v).carrier 0) := by
    intro v y hy
    have hc : (S.nativeTile D.val.ty P.K v).carrier 0 = (S.nativeTile D.val.ty P.K v).frame ''
        (S.proto (S.nativeTile D.val.ty P.K v).ty).carrier := by
      show placedSet _ (S.supertile 0 _) = _
      rw [hsup0]; rfl
    rw [hc]
    have := (S.nativeTile D.val.ty P.K v).frame.toHomeomorph.image_interior
      (S.proto (S.nativeTile D.val.ty P.K v).ty).carrier
    simp only [AffineIsometryEquiv.coe_toHomeomorph] at this
    rw [← this]
    exact Set.mem_image_of_mem _ hy
  rintro _ ⟨x, hx, rfl⟩
  have hxi : x ∈ interior (S.proto (S.nativeTile D.val.ty P.K w).ty).carrier :=
    C.cluster_inside (⟨D, w⟩ : LeafType P) .core hx
  refine ⟨?_, ?_⟩
  · rw [← S.native_cover]
    exact Set.mem_iUnion.mpr ⟨w, interior_subset (hint w x hxi)⟩
  · intro hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨w', j, z, hz, hzx⟩ := hmem
    have hzc : z ∈ closedBall (C.enclosingCentre (⟨D, w'⟩ : LeafType P) (.trigger j))
        (C.enclosingRadius (⟨D, w'⟩ : LeafType P) (.trigger j)) := Metric.ball_subset_closedBall hz
    by_cases hw : w' = w
    · subst hw
      have hzx' : z = x := (LeafType.position (⟨D, w'⟩ : LeafType P)).injective hzx
      subst hzx'
      have hxe := C.cluster_subset_enclosing (⟨D, w'⟩ : LeafType P) .core hx
      exact Set.disjoint_left.mp (C.enclosing_disjoint (⟨D, w'⟩ : LeafType P)
        (show (ClusterKind.core : ClusterKind (⟨D, w'⟩ : LeafType P)) ≠ .trigger j from
          by intro h; cases h)) hxe hzc
    · have hz' := hint w' z (C.enclosing_inside (⟨D, w'⟩ : LeafType P) (.trigger j) hzc)
      have hx' := hint w x hxi
      have hzx'' : (S.nativeTile D.val.ty P.K w').frame z =
          (S.nativeTile D.val.ty P.K w).frame x := hzx
      rw [hzx''] at hz'
      exact Set.disjoint_left.mp (S.native_disjoint D.val.ty P.K hw) hz' hx'

/-- Step 3 of the V4 proof of `compiler_certificates` (V4 2.17(a)): "on [the CORE cluster of
leaf i] λ_Y∘ψ equals the augmented marking of (D,i) transported by φ_(D,i)" — the CORE_D
marking restricted to a native CORE cluster is the augmented leaf marking. -/
private lemma compiler_certificates_step3_core_marks (C : ClusterData S P)
    (D : CertificateSymbol S P) (w : S.RoleWord D.val.ty P.K) (x : E d)
    (hx : x ∈ C.cluster (⟨D, w⟩ : LeafType P) .core) :
    Compiler.certificateColour C D ((LeafType.position (⟨D, w⟩ : LeafType P)) x) =
      augmentedColour C (⟨D, w⟩ : LeafType P) x := by
  have hc : x ∈ (S.proto (LeafType.prototype (⟨D, w⟩ : LeafType P))).carrier :=
    interior_subset (C.cluster_inside _ _ hx)
  have h := Compiler.certificateColour_leaf C D w
    ((LeafType.position (⟨D, w⟩ : LeafType P)) x) (Set.mem_image_of_mem _ hc)
  rwa [AffineIsometryEquiv.symm_apply_apply] at h

/-- Step 4 of the V4 proof of `compiler_certificates` (V4 2.17(a), using 2.13): "For every
leaf i' of D, Λ_D contains its entire CORE cluster, so Lemma 2.13 gives a tile t_{i'} of type
(D,i') with frame ψ∘φ_(D,i')" — for any copy ψ of CORE_D agreeing with Y. -/
private lemma compiler_certificates_step4_leaf_pinned (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) (D : CertificateSymbol S P) (ψ : Iso d)
    (hψ : ∀ p : (Compiler.coreRule C D).carrier,
      Y.marking (ψ p) = (Compiler.coreRule C D).mark p)
    (w : S.RoleWord D.val.ty P.K) :
    ∃ t' ∈ Y.tiles, compilerLeaf C t' = (⟨D, w⟩ : LeafType P) ∧
      (LeafType.position (⟨D, w⟩ : LeafType P)).trans ψ = compilerFrame C t' := by
  refine cluster_rigidity C Y (⟨D, w⟩ : LeafType P) .core _ ?_
  intro x hx
  have hc := compiler_certificates_step2_core_cluster_inside C D w (Set.mem_image_of_mem _ hx)
  have h := hψ ⟨_, hc⟩
  rw [AffineIsometryEquiv.coe_trans, Function.comp_apply, h]
  exact compiler_certificates_step3_core_marks C D w x hx

/-- Interior points of a prototype go to interior points of each actual tile. -/
private lemma compiler_certificates_frame_interior (C : ClusterData S P)
    (u : PlacedMarkedTile (systemM S P C)) (y : E d)
    (hy : y ∈ interior (S.proto (compilerLeaf C u).prototype).carrier) :
    compilerFrame C u y ∈ interior u.carrier := by
  have hu := placedLeaf_decode C u
  have hcar : u.carrier = compilerFrame C u ''
      (S.proto (compilerLeaf C u).prototype).carrier :=
    calc u.carrier = (placedLeaf C (compilerLeaf C u) (compilerFrame C u)).carrier := by rw [hu]
      _ = _ := rfl
  rw [hcar]
  have := (compilerFrame C u).toHomeomorph.image_interior
    (S.proto (compilerLeaf C u).prototype).carrier
  simp only [AffineIsometryEquiv.coe_toHomeomorph] at this
  rw [← this]
  exact Set.mem_image_of_mem _ hy

/-- Step 5 of the V4 proof of `compiler_certificates` (V4 2.17(a), using 2.13): "there is a
tile t' of type (D,i) with ψ∘φ_(D,i)=φ_{t'}; the point x lies in the image under ψ of this CORE
microball, which by Lemma 2.13 is a microball of t' and lies in int t'; since also x ∈ int t and
distinct tiles have disjoint interiors, t'=t ... Hence ψ=φ_t∘φ_(D,i)⁻¹ is determined by t." -/
private lemma compiler_certificates_step5_frame (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles) :
    ∀ p : (Compiler.coreRule C (compilerLeaf C t).1).carrier,
      Y.marking (((compilerLeaf C t).position.symm.trans (compilerFrame C t)) p) =
        (Compiler.coreRule C (compilerLeaf C t).1).mark p := by
  obtain ⟨ψ, hψ, hx⟩ := compiler_certificates_step1_core_rule C Y hY t ht
  obtain ⟨t', ht', hl, hf⟩ := compiler_certificates_step4_leaf_pinned C Y
    (compilerLeaf C t).1 ψ hψ (compilerLeaf C t).2
  obtain ⟨m, hm, hpm⟩ := hx
  have hmi : m ∈ C.cluster (compilerLeaf C t) .core := Set.mem_iUnion_of_mem 0 hm
  have hx' : compilerFrame C t (C.centre (compilerLeaf C t) .core 0) =
      compilerFrame C t' m := by
    rw [← hf, AffineIsometryEquiv.coe_trans, Function.comp_apply, hpm,
      AffineIsometryEquiv.apply_symm_apply]
  have hint_t : compilerFrame C t (C.centre (compilerLeaf C t) .core 0) ∈ interior t.carrier :=
    compiler_certificates_frame_interior C t _
      (C.cluster_inside _ _ (Set.mem_iUnion_of_mem 0 (Metric.mem_closedBall_self C.ρ_pos.le)))
  have hint_t' : compilerFrame C t' m ∈ interior t'.carrier := by
    refine compiler_certificates_frame_interior C t' m ?_
    rw [hl]
    exact C.cluster_inside _ _ hmi
  have htt : t = t' := by
    by_contra hne
    exact Set.disjoint_left.mp (Y.disjoint ht ht' hne) hint_t (hx' ▸ hint_t')
  subst htt
  have hψ' : ψ = (compilerLeaf C t).position.symm.trans (compilerFrame C t) := by
    rw [← hf]; ext y; simp
  rw [← hψ']
  exact hψ

/-- An open set inside a finite union of closed sets meets the interior of one of them. -/
private lemma compiler_certificates_open_meets_interior {ι : Type} [Finite ι]
    (f : ι → Set (E d)) (hc : ∀ i, IsClosed (f i)) (O : Set (E d)) (hO : IsOpen O)
    (hne : O.Nonempty) (hsub : O ⊆ ⋃ i, f i) : ∃ i, (O ∩ interior (f i)).Nonempty := by
  let g : Option ι → Set (E d) := fun o => o.elim Oᶜ f
  have hgc : ∀ o, IsClosed (g o) := by
    intro o; cases o with
    | none => exact hO.isClosed_compl
    | some i => exact hc i
  have hgU : ⋃ o, g o = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    by_cases hy : y ∈ O
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hsub hy)
      exact Set.mem_iUnion.mpr ⟨some i, hi⟩
    · exact Set.mem_iUnion.mpr ⟨none, hy⟩
  have hd := dense_iUnion_interior_of_closed hgc hgU
  obtain ⟨y, hyO, hy⟩ := hd.inter_open_nonempty O hO hne
  obtain ⟨o, ho⟩ := Set.mem_iUnion.mp hy
  cases o with
  | none => exact absurd hyO (interior_subset ho)
  | some i => exact ⟨i, y, hyO, ho⟩

/-- Leaf carriers of a block are closed. -/
private lemma compiler_certificates_leaf_closed {C : ClusterData S P}
    {Y : MarkedTiling (systemM S P C)} (B : KBlock Y)
    (w : S.RoleWord B.certificate.val.ty P.K) : IsClosed (B.leaf w).carrier :=
  ((augmentedLeaf C (⟨B.certificate, w⟩ : LeafType P)).compact.image
    (AffineIsometryEquiv.continuous _)).isClosed

/-- Step 6 of the V4 proof of `compiler_certificates` (V4 2.17(a)): "If two such K-blocks β,β'
have a common interior point, pick one outside the (nowhere dense) union of all tile
boundaries: it lies in int u ∩ int u' for leaves u of β and u' of β'; so u=u', and the block
determined by u is unique, so β=β'." -/
private lemma compiler_certificates_step6_disjoint (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) :
    Pairwise (fun B D : KBlock Y => Disjoint (interior B.carrier) (interior D.carrier)) := by
  intro B D hBD
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hne
  have hO : (interior B.carrier ∩ interior D.carrier).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hne
  have hOo : IsOpen (interior B.carrier ∩ interior D.carrier) :=
    isOpen_interior.inter isOpen_interior
  obtain ⟨w, hw⟩ := compiler_certificates_open_meets_interior (fun w => (B.leaf w).carrier)
    (compiler_certificates_leaf_closed B) _ hOo hO
    (by rw [KBlock.union_leaves]; exact fun y hy => interior_subset hy.1)
  obtain ⟨w', hw'⟩ := compiler_certificates_open_meets_interior (fun w => (D.leaf w).carrier)
    (compiler_certificates_leaf_closed D) _ (hOo.inter isOpen_interior) hw
    (by rw [KBlock.union_leaves]; exact fun y hy => interior_subset hy.1.2)
  obtain ⟨y, ⟨⟨_, hyB⟩, hyD⟩⟩ := hw'
  have hleaf : B.leaf w = D.leaf w' := by
    by_contra hne'
    exact Set.disjoint_left.mp (Y.disjoint (B.leaf_mem w) (D.leaf_mem w') hne') hyB hyD
  obtain ⟨hl, hφ⟩ := placedLeaf_injective C _ _ _ _ hleaf
  apply hBD
  have hc : B.certificate = D.certificate := congrArg Sigma.fst hl
  have hpos : LeafType.position (⟨B.certificate, w⟩ : LeafType P) =
      LeafType.position (⟨D.certificate, w'⟩ : LeafType P) := by rw [hl]
  rw [hpos] at hφ
  refine KBlock.ext hc (AffineIsometryEquiv.ext fun y => ?_)
  have := congrArg (fun φ : Iso d => φ
    ((LeafType.position (⟨D.certificate, w'⟩ : LeafType P)).symm y)) hφ
  simpa using this


/-- M8, V4 2.17(a): complete certificates are forced in a proper output.
Every tile determines its certificate and the block frame φ_t ∘ φ_(D,i)⁻¹.
All resulting blocks, with repetitions identified, cover space and have disjoint
interiors; each retains a jointly honest table and pre-patterns. -/
theorem compiler_certificates (C : ClusterData S P) (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) :
    (∀ t ∈ Y.tiles, ∃ B : KBlock Y,
      B.certificate = (compilerLeaf C t).1 ∧
      B.frame = (compilerLeaf C t).position.symm.trans (compilerFrame C t) ∧
      t = placedLeaf C (compilerLeaf C t) ((compilerLeaf C t).position.trans B.frame) ∧
      t.carrier ⊆ B.carrier) ∧
    Pairwise (fun B D : KBlock Y => Disjoint (interior B.carrier) (interior D.carrier)) ∧
    (∀ x : E d, ∃ B : KBlock Y, x ∈ B.carrier) ∧
    ∀ B : KBlock Y, ∃ (U : HonestSource S) (N : FramedNode S)
      (hN : N ∈ U.hierarchy.nodes P.K), certOf U P N hN = B.certificate.val := by
  have h1 : ∀ t ∈ Y.tiles, ∃ B : KBlock Y,
      B.certificate = (compilerLeaf C t).1 ∧
      B.frame = (compilerLeaf C t).position.symm.trans (compilerFrame C t) ∧
      t = placedLeaf C (compilerLeaf C t) ((compilerLeaf C t).position.trans B.frame) ∧
      t.carrier ⊆ B.carrier := by
    intro t ht
    have hψ := compiler_certificates_step5_frame C Y hY t ht
    let B : KBlock Y :=
      { certificate := (compilerLeaf C t).1
        frame := (compilerLeaf C t).position.symm.trans (compilerFrame C t)
        leaves_actual := fun w => by
          obtain ⟨t', ht', hl, hf⟩ := compiler_certificates_step4_leaf_pinned C Y
            (compilerLeaf C t).1 _ hψ w
          have hd := placedLeaf_decode C t'
          rw [hl] at hd
          rw [hf, hd]
          exact ht' }
    have he : (compilerLeaf C t).position.trans B.frame = compilerFrame C t := by
      ext y; simp [B]
    have hteq : t = B.leaf (compilerLeaf C t).2 := by
      change t = placedLeaf C (compilerLeaf C t) ((compilerLeaf C t).position.trans B.frame)
      rw [he, placedLeaf_decode]
    refine ⟨B, rfl, rfl, ?_, ?_⟩
    · rw [he, placedLeaf_decode]
    · calc t.carrier = (B.leaf (compilerLeaf C t).2).carrier := congrArg (·.carrier) hteq
        _ ⊆ B.carrier := by
          rw [← KBlock.union_leaves]
          exact Set.subset_iUnion (fun w => (B.leaf w).carrier) _
  refine ⟨h1, compiler_certificates_step6_disjoint C Y, ?_, fun B => B.certificate.property⟩
  intro x
  obtain ⟨t, ht, hx⟩ := Y.cover x
  obtain ⟨B, -, -, -, hsub⟩ := h1 t ht
  exact ⟨B, hsub hx⟩

/-- M8, V4 2.17(a): a tile lies in a unique whole certificate block with its address.
Existence comes from properness; uniqueness is of certificate and frame, not support alone. -/
theorem compilerBlock_exists_unique (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles) :
    ∃! B : KBlock Y, ∃ w : S.RoleWord B.certificate.val.ty P.K, B.leaf w = t := by
  obtain ⟨H, _, _, _⟩ := compiler_certificates C Y hY
  obtain ⟨B, hcert, hframe, heq, _⟩ := H t ht
  use B
  dsimp
  constructor
  · have h1 : (compilerLeaf C t).1 = B.certificate := hcert.symm
    use h1 ▸ (compilerLeaf C t).2
    dsimp [KBlock.leaf]
    have hw : (⟨B.certificate, h1 ▸ (compilerLeaf C t).2⟩ : LeafType P) = compilerLeaf C t := by
      exact Sigma.ext hcert (by simp)
    have ht_eq : placedLeaf C (compilerLeaf C t) ((compilerLeaf C t).position.trans B.frame) = t := heq.symm
    rw [hw]
    exact ht_eq
  · rintro D ⟨wD, hwD⟩
    have h1 : (compilerLeaf C t).1 = B.certificate := hcert.symm
    let w : S.RoleWord B.certificate.val.ty P.K := h1 ▸ (compilerLeaf C t).2
    have ht_eq : B.leaf w = t := by
      dsimp [KBlock.leaf]
      have hw : (⟨B.certificate, h1 ▸ (compilerLeaf C t).2⟩ : LeafType P) = compilerLeaf C t := by
        exact Sigma.ext hcert (by simp)
      rw [hw]
      exact heq.symm
    have hwD_eq : D.leaf wD = B.leaf w := by
      rw [hwD, ht_eq]
      
    dsimp [KBlock.leaf] at hwD_eq
    have h_inj := placedLeaf_injective C _ _ _ _ hwD_eq
    have h_cert_eq : D.certificate = B.certificate := congrArg Sigma.fst h_inj.1
    have h_frame_eq : D.frame = B.frame := by
      have h_leaf_eq : (⟨D.certificate, wD⟩ : LeafType P) = ⟨B.certificate, w⟩ := h_inj.1
      have hφ := h_inj.2
      have h_pos_eq : LeafType.position (⟨D.certificate, wD⟩ : LeafType P) = LeafType.position (⟨B.certificate, w⟩ : LeafType P) := by
        rw [h_leaf_eq]
      rw [h_pos_eq] at hφ
      ext x
      have h_apply := congrArg (fun (f : Iso d) => f ((LeafType.position (⟨B.certificate, w⟩ : LeafType P)).symm x)) hφ
      dsimp at h_apply
      have h_symm : (LeafType.position (⟨B.certificate, w⟩ : LeafType P)) ((LeafType.position (⟨B.certificate, w⟩ : LeafType P)).symm x) = x := by
        exact (LeafType.position (⟨B.certificate, w⟩ : LeafType P)).apply_symm_apply x
      rw [h_symm] at h_apply
      rw [h_apply]
    obtain ⟨cD, fD, lD⟩ := D
    obtain ⟨cB, fB, lB⟩ := B
    dsimp at h_cert_eq h_frame_eq ⊢
    subst h_cert_eq
    subst h_frame_eq
    rfl

/-- M8, V4 2.17(b): every listed template tile occurs in the output with exactly
its listed label and the composite frame φ_central ∘ φ_template. -/
def TemplateOccurs (C : ClusterData S P) (Y : MarkedTiling (systemM S P C))
    (φ : Iso d) (θ : Template P) : Prop :=
  ∀ z ∈ θ.tiles, placedLeaf C z.2 (z.1.frame.trans φ) ∈ Y.tiles

/-- M8, V4 2.17(b): every output event contains an allowed positioned configuration.
Catalogue membership includes the CONT row or all six END rows on these actual labels. -/
theorem compiler_events (C : ClusterData S P) (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (j : EventSlot (compilerLeaf C t)) :
    ∃ θ ∈ allowedTemplates j, θ.central = compilerLeaf C t ∧
      TemplateOccurs C Y (compilerFrame C t) θ := by
  sorry

namespace Compiler

/-- M8, V4 1.19, 2.17(c): the uniform native-scale cone radius of the END catalogue.
The stage-3 coverage existence lemma is a direct consequence of Corollary 1.19. -/
def coneRadius (S : SubstSystem d) (P : Params S) : ℝ :=
  Classical.choose (endGeometry_coverage S P)

/-- M8, V4 1.19, 2.17(c): the selected radius is positive and covers every honest star. -/
theorem coneRadius_spec (S : SubstSystem d) (P : Params S) :
    0 < coneRadius S P ∧ ∀ G ∈ honestEndGeometries S P,
      ((fun u => vertexPoint G.vertex + u) '' G.header.parentCone) ∩
          ball (vertexPoint G.vertex) (coneRadius S P) ⊆
        ⋃ u ∈ G.tiles, u.carrier 0 := Classical.choose_spec (endGeometry_coverage S P)

/-- M8, V4 2.17(c): the END event vertex in the actual central tile's frame. -/
def endVertex {l : LeafType P} (φ : Iso d) (j : EndSlot l) : E d :=
  φ (vertexPoint j.vertex)

/-- M8, V4 2.17(c): v + Q_t G with G a direction cone in the central prototype.
Only the orthogonal part acts on directions; the apex is translated separately. -/
def endSector {l : LeafType P} (φ : Iso d) (j : EndSlot l) : Set (E d) :=
  (fun u => endVertex φ j + φ.linearIsometryEquiv u) '' j.header.parentCone

/-- M8, V4 2.17(c): the union of the whole positioned template tiles. -/
def templateSupport (C : ClusterData S P) (φ : Iso d) (θ : Template P) : Set (E d) :=
  ⋃ z ∈ θ.tiles, (placedLeaf C z.2 (z.1.frame.trans φ)).carrier

/-- M8, V4 2.17(c): every allowed END template has the recorded local cone coverage.
This is a property of the honest geometric catalogue, independent of proper outputs. -/
theorem allowedEnd_coverage (C : ClusterData S P) (l : LeafType P) (j : EndSlot l)
    (θ : Template P) (hθ : θ ∈ allowedTemplates (.end_ j)) (φ : Iso d) :
    endSector φ j ∩ ball (endVertex φ j) (coneRadius S P) ⊆
      templateSupport C φ θ := by
  sorry

end Compiler

/-- M8, V4 2.17(c): in every actual allowed END configuration the template tiles
cover the recorded cone sector near v, and contain every output tile whose interior
meets the open sector there. The radius is the uniform Corollary 1.19 radius.
The statement applies to every allowed template occurring as in part (b). -/
theorem compiler_coverage (C : ClusterData S P) (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (j : EndSlot (compilerLeaf C t)) (θ : Template P)
    (hθ : θ ∈ allowedTemplates (.end_ j))
    (hactual : TemplateOccurs C Y (compilerFrame C t) θ) :
    Compiler.endSector (compilerFrame C t) j ∩
        ball (Compiler.endVertex (compilerFrame C t) j) (Compiler.coneRadius S P) ⊆
      Compiler.templateSupport C (compilerFrame C t) θ ∧
    ∀ u ∈ Y.tiles,
      (interior u.carrier ∩ interior (Compiler.endSector (compilerFrame C t) j) ∩
        ball (Compiler.endVertex (compilerFrame C t) j) (Compiler.coneRadius S P)).Nonempty →
      ∃ z ∈ θ.tiles, u = placedLeaf C z.2 (z.1.frame.trans (compilerFrame C t)) := by
  sorry

/-- M3, V4 2.11: exact physical-catalogue membership, with no additional tiles. -/
theorem systemM_physical_iff (C : ClusterData S P) (Q : MarkedPrototile d (Colour S P)) :
    Q ∈ (systemM S P C).physical ↔ ∃ l : LeafType P, augmentedLeaf C l = Q := by
  simp only [systemM, Compiler.physicalCatalogue, Finset.mem_image, Finset.mem_univ,
    true_and]

/-- M3, V4 2.11: exact rule-catalogue membership in the two printed families. -/
theorem systemM_rules_iff (C : ClusterData S P) (R : CompactRule d (Colour S P)) :
    R ∈ (systemM S P C).rules ↔
      (∃ D : CertificateSymbol S P, Compiler.coreRule C D = R) ∨
      ∃ e : Compiler.EventIndex S P, Compiler.eventRule C e = R := by
  simp only [systemM, Compiler.ruleCatalogue, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]

/-- M3/M5, V4 2.11, 2.13: physical and pointwise native type decodings coincide. -/
theorem compilerLeaf_native_type (C : ClusterData S P)
    (t : PlacedMarkedTile (systemM S P C)) :
    (t.native (nativeDecoration S P C)).ty = (compilerLeaf C t).prototype := rfl

/-- M3/M5, V4 2.11, 2.13: the decoded frame realizes the physical carrier exactly. -/
theorem compilerFrame_carrier (C : ClusterData S P)
    (t : PlacedMarkedTile (systemM S P C)) :
    t.carrier = placedSet (compilerFrame C t) (S.proto (compilerLeaf C t).prototype).carrier :=
  by
  rw [← placedLeaf_decode C t]
  obtain ⟨hl, hφ⟩ := compiler_decode_unique C (compilerLeaf C t) (compilerFrame C t)
  rw [hl, hφ]
  rfl

/-- M3/M5, V4 2.11, 2.13: every point of a physical tile reads its augmented marking. -/
theorem compilerFrame_marking (C : ClusterData S P)
    (t : PlacedMarkedTile (systemM S P C)) (x : t.carrier) :
    t.mark x = augmentedColour C (compilerLeaf C t) ((compilerFrame C t).symm x.val) := by
  sorry

/-- M4, V4 2.12(iii): every tile boundary in any compiler tiling has colour @. -/
theorem compiler_boundary (C : ClusterData S P) (Y : MarkedTiling (systemM S P C))
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles) (x : E d)
    (hx : x ∈ frontier t.carrier) : Y.marking x = Colour.boundary := by
  have H1 : x ∈ t.carrier := by
    obtain ⟨Q, _, φ, hQ2, _⟩ := t.realization
    have H2 : IsCompact Q.carrier := Q.compact
    have H4 : IsCompact t.carrier := by
      rw [hQ2]
      exact H2.image φ.continuous
    have H5 : IsClosed t.carrier := H4.isClosed
    exact H5.closure_eq ▸ frontier_subset_closure hx
  have H2 := Y.marking_eq_tile t ht x H1
  rw [H2]
  have H3 := compilerFrame_marking C t ⟨x, H1⟩
  rw [H3]
  apply augmentedMarking_boundary C (compilerLeaf C t)
  have h_frame := compilerFrame_carrier C t
  have H4 : x ∈ frontier (placedSet (compilerFrame C t) (S.proto (compilerLeaf C t).prototype).carrier) := by
    rw [← h_frame]
    exact hx
  let f := (compilerFrame C t).toHomeomorph
  change x ∈ frontier (f '' (S.proto (compilerLeaf C t).prototype).carrier) at H4
  rw [← f.image_frontier] at H4
  obtain ⟨y, hy1, hy2⟩ := (Set.mem_image f _ _).mp H4
  have H5 : y = (compilerFrame C t).symm x := by
    calc y = (compilerFrame C t).symm ((compilerFrame C t) y) := by simp
    _ = (compilerFrame C t).symm (f y) := rfl
    _ = (compilerFrame C t).symm x := by rw [hy2]
  rw [← H5]
  exact hy1

/-- M4, V4 2.12(iii): separation works for arbitrary cluster labels in distinct
tiles, even different microball indices or kinds. This is the separation used
when the d+1 source balls are first pinned to potentially different target tiles. -/
theorem compiler_microcentres_separated (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C))
    (t u : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles) (hu : u ∈ Y.tiles)
    (hne : t ≠ u) (κ : ClusterKind (compilerLeaf C t))
    (η : ClusterKind (compilerLeaf C u)) (a b : Fin (d + 1)) :
    2 * C.δ ≤ dist (compilerFrame C t (C.centre (compilerLeaf C t) κ a))
      (compilerFrame C u (C.centre (compilerLeaf C u) η b)) := by
  have h_int_t : Metric.ball (compilerFrame C t (C.centre (compilerLeaf C t) κ a)) C.δ ⊆ interior t.carrier := by
    rw [compilerFrame_carrier C t]
    have h_clear := C.centre_ball_inside (compilerLeaf C t) κ a
    change Metric.ball ((compilerFrame C t) (C.centre (compilerLeaf C t) κ a)) C.δ ⊆ interior (⇑(compilerFrame C t).toHomeomorph '' _)
    rw [← (compilerFrame C t).toHomeomorph.image_interior]
    intro x hx
    have h1 : (compilerFrame C t).symm x ∈ Metric.ball (C.centre (compilerLeaf C t) κ a) C.δ := by
      rw [Metric.mem_ball, ← (compilerFrame C t).isometry.dist_eq (compilerFrame C t |>.symm x) (C.centre (compilerLeaf C t) κ a)]
      rw [AffineIsometryEquiv.apply_symm_apply]
      exact hx
    use (compilerFrame C t).symm x
    exact ⟨h_clear h1, AffineIsometryEquiv.apply_symm_apply _ _⟩
  have h_int_u : Metric.ball (compilerFrame C u (C.centre (compilerLeaf C u) η b)) C.δ ⊆ interior u.carrier := by
    rw [compilerFrame_carrier C u]
    have h_clear := C.centre_ball_inside (compilerLeaf C u) η b
    change Metric.ball ((compilerFrame C u) (C.centre (compilerLeaf C u) η b)) C.δ ⊆ interior (⇑(compilerFrame C u).toHomeomorph '' _)
    rw [← (compilerFrame C u).toHomeomorph.image_interior]
    intro x hx
    have h1 : (compilerFrame C u).symm x ∈ Metric.ball (C.centre (compilerLeaf C u) η b) C.δ := by
      rw [Metric.mem_ball, ← (compilerFrame C u).isometry.dist_eq (compilerFrame C u |>.symm x) (C.centre (compilerLeaf C u) η b)]
      rw [AffineIsometryEquiv.apply_symm_apply]
      exact hx
    use (compilerFrame C u).symm x
    exact ⟨h_clear h1, AffineIsometryEquiv.apply_symm_apply _ _⟩
  have h_disj : Disjoint (interior t.carrier) (interior u.carrier) := Y.disjoint ht hu hne
  have h_disj_balls : Disjoint (Metric.ball (compilerFrame C t (C.centre (compilerLeaf C t) κ a)) C.δ) (Metric.ball (compilerFrame C u (C.centre (compilerLeaf C u) η b)) C.δ) := h_disj.mono h_int_t h_int_u
  have hdist := (disjoint_ball_ball_iff C.δ_pos C.δ_pos).mp h_disj_balls
  linarith

/-- M4, V4 2.12(iii): the placed physical family is locally finite, including
its closed carriers; every bounded set meets only finitely many tiles. -/
theorem compiler_tiles_locallyFinite (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) :
    LocallyFinite (fun t : {t // t ∈ Y.tiles} => t.val.carrier) ∧
      ∀ B : Set (E d), Bornology.IsBounded B →
        {t : PlacedMarkedTile (systemM S P C) |
          t ∈ Y.tiles ∧ (B ∩ t.carrier).Nonempty}.Finite := by
classical
  have hc : ∀ t : PlacedMarkedTile (systemM S P C),
      placedSet (compilerFrame C t) (S.proto (compilerLeaf C t).prototype).carrier = t.carrier :=
    fun t => (compilerFrame_carrier C t).symm
  have hd : Pairwise (fun t u : {t // t ∈ Y.tiles} => Disjoint
      (interior (placedSet (compilerFrame C t.val)
        (S.proto (compilerLeaf C t.val).prototype).carrier))
      (interior (placedSet (compilerFrame C u.val)
        (S.proto (compilerLeaf C u.val).prototype).carrier))) := by
    intro t u htu
    rw [hc, hc]
    exact Y.disjoint t.property u.property (fun h => htu (Subtype.ext h))
  have h := locallyFinite_disjointInteriors S.proto
    (fun t : {t // t ∈ Y.tiles} => (compilerLeaf C t.val).prototype)
    (fun t : {t // t ∈ Y.tiles} => compilerFrame C t.val) hd
  have e : (fun t : {t // t ∈ Y.tiles} =>
      placedSet (compilerFrame C t.val) (S.proto (compilerLeaf C t.val).prototype).carrier)
      = fun t => t.val.carrier := funext fun t => hc t.val
  refine ⟨?_, ?_⟩
  · have := h.1
    rwa [e] at this
  · intro B hB
    have := h.2 B hB
    have h_eq : {a : {t // t ∈ Y.tiles} | (B ∩ placedSet (compilerFrame C a.val) (S.proto (compilerLeaf C a.val).prototype).carrier).Nonempty} = {a : {t // t ∈ Y.tiles} | (B ∩ a.val.carrier).Nonempty} := by
      ext a
      change (B ∩ placedSet (compilerFrame C a.val) (S.proto (compilerLeaf C a.val).prototype).carrier).Nonempty ↔ (B ∩ a.val.carrier).Nonempty
      have hc2 : placedSet (compilerFrame C a.val) (S.proto (compilerLeaf C a.val).prototype).carrier = a.val.carrier := (compilerFrame_carrier C a.val).symm
      rw [hc2]
    rw [h_eq] at this
    exact this.image Subtype.val |>.subset (by
      intro t ht; exact ⟨⟨t, ht.1⟩, ht.2, rfl⟩)

namespace Compiler

/-- M3/M5, V4 2.11, 2.13: all CORE clusters survive all removed open trigger balls. -/
theorem core_contains_core_clusters (C : ClusterData S P) (D : CertificateSymbol S P)
    (w : S.RoleWord D.val.ty P.K) :
    placedSet (LeafType.position (⟨D, w⟩ : LeafType P))
      (C.cluster (⟨D, w⟩ : LeafType P) .core) ⊆ coreCarrier C D := by
  have hsup0 : ∀ A : S.ι, S.supertile 0 A = (S.proto A).carrier := by
    intro A; simp [SubstSystem.supertile]
  have hint : ∀ (v : S.RoleWord D.val.ty P.K) (y : E d),
      y ∈ interior (S.proto (S.nativeTile D.val.ty P.K v).ty).carrier →
      (S.nativeTile D.val.ty P.K v).frame y ∈
        interior ((S.nativeTile D.val.ty P.K v).carrier 0) := by
    intro v y hy
    have hc : (S.nativeTile D.val.ty P.K v).carrier 0 = (S.nativeTile D.val.ty P.K v).frame ''
        (S.proto (S.nativeTile D.val.ty P.K v).ty).carrier := by
      show placedSet _ (S.supertile 0 _) = _
      rw [hsup0]; rfl
    rw [hc]
    have := (S.nativeTile D.val.ty P.K v).frame.toHomeomorph.image_interior
      (S.proto (S.nativeTile D.val.ty P.K v).ty).carrier
    simp only [AffineIsometryEquiv.coe_toHomeomorph] at this
    rw [← this]
    exact Set.mem_image_of_mem _ hy
  rintro _ ⟨x, hx, rfl⟩
  have hxi : x ∈ interior (S.proto (S.nativeTile D.val.ty P.K w).ty).carrier :=
    C.cluster_inside (⟨D, w⟩ : LeafType P) .core hx
  refine ⟨?_, ?_⟩
  · rw [← S.native_cover]
    exact Set.mem_iUnion.mpr ⟨w, interior_subset (hint w x hxi)⟩
  · intro hmem
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨w', j, z, hz, hzx⟩ := hmem
    have hzc : z ∈ closedBall (C.enclosingCentre (⟨D, w'⟩ : LeafType P) (.trigger j))
        (C.enclosingRadius (⟨D, w'⟩ : LeafType P) (.trigger j)) := Metric.ball_subset_closedBall hz
    by_cases hw : w' = w
    · subst hw
      have hzx' : z = x := (LeafType.position (⟨D, w'⟩ : LeafType P)).injective hzx
      subst hzx'
      have hxe := C.cluster_subset_enclosing (⟨D, w'⟩ : LeafType P) .core hx
      exact Set.disjoint_left.mp (C.enclosing_disjoint (⟨D, w'⟩ : LeafType P)
        (show (ClusterKind.core : ClusterKind (⟨D, w'⟩ : LeafType P)) ≠ .trigger j from
          by intro h; cases h)) hxe hzc
    · have hz' := hint w' z (C.enclosing_inside (⟨D, w'⟩ : LeafType P) (.trigger j) hzc)
      have hx' := hint w x hxi
      have hzx'' : (S.nativeTile D.val.ty P.K w').frame z =
          (S.nativeTile D.val.ty P.K w).frame x := hzx
      rw [hzx''] at hz'
      exact Set.disjoint_left.mp (S.native_disjoint D.val.ty P.K hw) hz' hx'

/-- M3/M5, V4 2.11, 2.13: on every surviving CORE cluster the rule is the leaf marking. -/
theorem core_marks_core_cluster (C : ClusterData S P) (D : CertificateSymbol S P)
    (w : S.RoleWord D.val.ty P.K) (x : E d)
    (hx : x ∈ C.cluster (⟨D, w⟩ : LeafType P) .core) :
    certificateColour C D ((LeafType.position (⟨D, w⟩ : LeafType P)) x) =
      augmentedColour C (⟨D, w⟩ : LeafType P) x := by
  have h_leaf := certificateColour_leaf C D w ((LeafType.position (⟨D, w⟩ : LeafType P)) x)
  have hc : x ∈ (S.proto (LeafType.prototype (⟨D, w⟩ : LeafType P))).carrier := by
    have h1 : C.cluster (⟨D, w⟩ : LeafType P) .core ⊆ (S.proto (LeafType.prototype (⟨D, w⟩ : LeafType P))).carrier := by
      calc C.cluster (⟨D, w⟩ : LeafType P) .core ⊆ C.enclosing (⟨D, w⟩ : LeafType P) .core := C.cluster_subset_enclosing (⟨D, w⟩ : LeafType P) .core
      _ = Metric.closedBall (C.enclosingCentre (⟨D, w⟩ : LeafType P) .core) (C.enclosingRadius (⟨D, w⟩ : LeafType P) .core) := rfl
      _ ⊆ interior (S.proto (LeafType.prototype (⟨D, w⟩ : LeafType P))).carrier := C.enclosing_inside (⟨D, w⟩ : LeafType P) .core
      _ ⊆ (S.proto (LeafType.prototype (⟨D, w⟩ : LeafType P))).carrier := interior_subset
    exact h1 hx
  have hp : ((LeafType.position (⟨D, w⟩ : LeafType P)) x) ∈ placedSet (LeafType.position (⟨D, w⟩ : LeafType P)) (S.proto (LeafType.prototype (⟨D, w⟩ : LeafType P))).carrier := by
    exact Set.mem_image_of_mem _ hc
  have h_eq : certificateColour C D ((LeafType.position (⟨D, w⟩ : LeafType P)) x) = augmentedColour C (⟨D, w⟩ : LeafType P) ((LeafType.position (⟨D, w⟩ : LeafType P)).symm ((LeafType.position (⟨D, w⟩ : LeafType P)) x)) := h_leaf hp
  have h_symm : (LeafType.position (⟨D, w⟩ : LeafType P)).symm ((LeafType.position (⟨D, w⟩ : LeafType P)) x) = x := by
    exact Equiv.symm_apply_apply _ x
  rwa [h_symm] at h_eq

/-- M3/M5, V4 2.11, 2.13: an EVENT support contains the entire central TRIG cluster. -/
theorem event_contains_trigger_cluster (C : ClusterData S P) (e : EventIndex S P) :
    C.cluster e.leaf (.trigger e.slot) ⊆ eventCarrier C e := by
  exact (C.cluster_subset_enclosing e.leaf (.trigger e.slot)).trans Set.subset_union_left

/-- M3/M5, V4 2.11, 2.13: an EVENT support contains every other tile's whole RO cluster. -/
theorem event_contains_readout_cluster (C : ClusterData S P) (e : EventIndex S P)
    (z : FramedNode S × LeafType P) (hz : z ∈ eventReadouts e) :
    placedSet z.1.frame (C.cluster z.2 .readout) ⊆ eventCarrier C e := by
  have h1 : C.cluster z.2 .readout ⊆ C.enclosing z.2 .readout := C.cluster_subset_enclosing z.2 .readout
  have h2 : placedSet z.1.frame (C.cluster z.2 .readout) ⊆ placedSet z.1.frame (C.enclosing z.2 .readout) :=
    Set.image_mono h1
  have h3 : placedSet z.1.frame (C.enclosing z.2 .readout) = readoutRegion C z := rfl
  have h4 : readoutRegion C z ⊆ eventCarrier C e := by
    unfold eventCarrier
    apply Set.subset_union_of_subset_right
    apply Set.subset_biUnion_of_mem hz
  exact h2.trans (by rw [h3]; exact h4)

/-- M3/M5, V4 2.11, 2.13: central TRIG pinning reads the entire correct cluster. -/
theorem event_marks_trigger_cluster (C : ClusterData S P) (e : EventIndex S P)
    (x : E d) (hx : x ∈ C.cluster e.leaf (.trigger e.slot)) :
    eventColour C e x = augmentedColour C e.leaf x :=
  eventColour_trigger C e x (C.cluster_subset_enclosing e.leaf (.trigger e.slot) hx)

/-- M3/M5, V4 2.11, 2.13: RO pinning reads the entire correct transported cluster. -/
theorem event_marks_readout_cluster (C : ClusterData S P) (e : EventIndex S P)
    (z : FramedNode S × LeafType P) (hz : z ∈ eventReadouts e) (x : E d)
    (hx : x ∈ C.cluster z.2 .readout) :
    eventColour C e (z.1.frame x) = augmentedColour C z.2 x := by
  have h_encl : x ∈ C.enclosing z.2 .readout := C.cluster_subset_enclosing z.2 .readout hx
  have h_reg : z.1.frame x ∈ readoutRegion C z := by
    dsimp [readoutRegion, placedSet]
    exact Set.mem_image_of_mem _ h_encl
  rw [eventColour_readout C e z hz (z.1.frame x) h_reg]
  simp

/-- M6, V4 2.14(b): the actual event index of a native source slot.
Choose an actual allowed configuration supplied by `honest_rows`, retaining both
its actual-label specification and its membership in the allowed catalogue. -/
def honestEventIndex (U : HonestSource S) (t : U.Node) (ht : t.1 = 0)
    (j : EventSlot (leafTypeOf U P t ht)) : EventIndex S P where
  leaf := leafTypeOf U P t ht
  slot := j
  template := Classical.choose (honest_rows U P t ht j)
  allowed := (Classical.choose_spec (honest_rows U P t ht j)).2

/-- M6, V4 2.14(b): the CORE copy in an actual height-K source node agrees everywhere. -/
theorem honestLift_core_agree (C : ClusterData S P) (U : HonestSource S)
    (B : FramedNode S) (hB : B ∈ U.hierarchy.nodes P.K)
    (x : (coreRule C (⟨certOf U P B hB, ⟨U, B, hB, rfl⟩⟩ :
      CertificateSymbol S P)).carrier) :
    (honestLift C U).marking (B.frame x) =
      (coreRule C (⟨certOf U P B hB, ⟨U, B, hB, rfl⟩⟩ :
        CertificateSymbol S P)).mark x := by
  sorry

/-- M6, V4 2.14(b): the actual allowed EVENT copy agrees on its entire compact support. -/
theorem honestLift_event_agree (C : ClusterData S P) (U : HonestSource S)
    (t : U.Node) (ht : t.1 = 0) (j : EventSlot (leafTypeOf U P t ht))
    (x : (eventRule C (honestEventIndex U t ht j)).carrier) :
    (honestLift C U).marking (t.2.val.frame x) =
      (eventRule C (honestEventIndex U t ht j)).mark x := by
  sorry

end Compiler

/-- M6, V4 2.14: a source supplies an actual proper output on its exact native tiling.
This explicit nonvacuity implication imposes no existence assumption on the species. -/
theorem compiler_nonempty_proper (C : ClusterData S P) (U : HonestSource S) :
    ∃ Y : MarkedTiling (systemM S P C), MProper Y ∧
      Y.project (nativeDecoration S P C) = U.tiling :=
  ⟨honestLift C U, honestLift_proper C U, honestLift_tiles C U⟩

/-- M7, V4 2.15--2.16: any actual source contributes some language at every height. -/
theorem sourceLanguage_nonempty (C : ClusterData S P) (U : HonestSource S) (n : ℕ) :
    ∃ A : S.ι, (sourceLanguage C n A).Nonempty := by
  obtain ⟨N, hN, _⟩ := U.hierarchy.cover n (0 : E d)
  exact ⟨N.ty, normalisedPattern (honestLift C U) n N.ty N.frame,
    U, N.frame, hN, rfl⟩

/-- M7, V4 2.16: the number of source patterns is bounded by the finite tuple space.
This estimate counts all leaf assignments, so no joint-honesty assumption is used. -/
theorem sourceLanguage_card_le (C : ClusterData S P) (n : ℕ) (A : S.ι) :
    (sourceLanguage C n A).ncard ≤
      Fintype.card (LeafType P) ^ Fintype.card (S.RoleWord A n) := by
  letI : Fintype (LeafType P) := leafTypeFintype P
  letI : Fintype (S.RoleWord A n) := SubstSystem.roleWordFintype S A n
  classical
  letI : Fintype (S.RoleWord A n → LeafType P) := Pi.instFintype
  have h1 := sourceLanguage_subset_render C n A
  have h2 : (Set.range (renderLeafTuple C n A)).ncard ≤ Fintype.card (S.RoleWord A n → LeafType P) := by
    have h_fin : (Set.univ : Set (S.RoleWord A n → LeafType P)).Finite := Set.finite_univ
    have h_eq : Set.range (renderLeafTuple C n A) = renderLeafTuple C n A '' Set.univ := by ext; simp
    rw [h_eq]
    have h_le : (renderLeafTuple C n A '' Set.univ).ncard ≤ Set.univ.ncard := Set.ncard_image_le h_fin
    rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h_le
    exact h_le
  have h3 : Fintype.card (S.RoleWord A n → LeafType P) = Fintype.card (LeafType P) ^ Fintype.card (S.RoleWord A n) := Fintype.card_fun
  rw [← h3]
  have h4 := Set.ncard_le_ncard h1 (Set.finite_range (renderLeafTuple C n A))
  exact le_trans h4 h2


/-- M8, V4 2.17(a): an honest certificate's leaf state is its depth-K table entry. -/
theorem certificate_leaf_state (D : CertificateSymbol S P)
    (w : S.RoleWord D.val.ty P.K) :
    D.val.table P.K le_rfl w = (D.val.leaves w).state := by
  obtain ⟨val, ⟨U, B, hB, rfl⟩⟩ := D
  rfl

namespace KBlock

variable {C : ClusterData S P} {Y : MarkedTiling (systemM S P C)} (B : KBlock Y)

/-- M8, V4 2.17(a): each actual leaf decodes to its prescribed label and exact frame. -/
theorem leaf_data (w : S.RoleWord B.certificate.val.ty P.K) :
    compilerLeaf C (B.leaf w) = (⟨B.certificate, w⟩ : LeafType P) ∧
      compilerFrame C (B.leaf w) =
        (LeafType.position (⟨B.certificate, w⟩ : LeafType P)).trans B.frame :=
  compiler_decode_unique C _ _

/-- M8, V4 2.17(a): decoded leaf state agrees with the block's retained table. -/
theorem leaf_state (w : S.RoleWord B.certificate.val.ty P.K) :
    (compilerLeaf C (B.leaf w)).prePattern.state = B.table P.K le_rfl w := by
  rw [(B.leaf_data w).1]
  exact (certificate_leaf_state B.certificate w).symm

/-- M8, V4 2.17(a): no address occurs twice in the actual block subdivision. -/
theorem leaf_injective : Function.Injective B.leaf := by
  intro v w h
  have h_inj := placedLeaf_injective C _ _ _ _ h
  have h_eq := h_inj.1
  cases h_eq
  rfl

/-- M8, V4 2.17(a): the standard native leaf interiors form a disjoint subdivision. -/
theorem leaves_disjoint : Pairwise (fun v w : S.RoleWord B.certificate.val.ty P.K =>
    Disjoint (interior (B.leaf v).carrier) (interior (B.leaf w).carrier)) := by
  intro v w hvw
  exact Y.disjoint (B.leaf_mem v) (B.leaf_mem w) (B.leaf_injective.ne hvw)

/-- M8, V4 2.17(a): the full closed block carrier is compact and regular closed. -/
theorem carrier_regular : IsCompact B.carrier ∧ IsRegularClosed B.carrier := by
  have hcar : B.carrier = B.node.prototypeFrame P.K '' (S.proto B.node.ty).carrier := by
    simp only [carrier, FramedNode.carrier, FramedNode.prototypeFrame, SubstSystem.supertile,
      placedSet, Set.image_image]
    rfl
  let e := (B.node.prototypeFrame P.K).toHomeomorphOfFiniteDimensional
  have hcar' : B.carrier = e '' (S.proto B.node.ty).carrier := hcar
  rw [hcar']
  refine ⟨(S.proto B.node.ty).compact.image e.continuous, ?_⟩
  change closure (interior (e '' (S.proto B.node.ty).carrier)) = _
  rw [← e.image_interior, ← e.image_closure, (S.proto B.node.ty).regularClosed]

/-- M8, V4 2.17(a): the block has genuine full-dimensional connected interior. -/
theorem carrier_interior : IsConnected (interior B.carrier) ∧
    (interior B.carrier).Nonempty := by
  dsimp [carrier, node, FramedNode.carrier, placedSet, SubstSystem.supertile]
  have h1 : (S.σ ^ P.K) '' (S.proto B.certificate.val.ty).carrier =
    ((S.σ ^ P.K).toContinuousLinearEquiv).toHomeomorph '' (S.proto B.certificate.val.ty).carrier := rfl
  rw [h1]
  have h2 : B.frame '' (((S.σ ^ P.K).toContinuousLinearEquiv).toHomeomorph '' (S.proto B.certificate.val.ty).carrier) =
    B.frame.toHomeomorph '' (((S.σ ^ P.K).toContinuousLinearEquiv).toHomeomorph '' (S.proto B.certificate.val.ty).carrier) := rfl
  rw [h2]
  rw [← Homeomorph.image_interior B.frame.toHomeomorph]
  rw [← Homeomorph.image_interior ((S.σ ^ P.K).toContinuousLinearEquiv).toHomeomorph]
  constructor
  · apply IsConnected.image
    · apply IsConnected.image
      · exact (S.proto B.certificate.val.ty).interior_connected
      · exact ((S.σ ^ P.K).toContinuousLinearEquiv).continuous.continuousOn
    · exact B.frame.continuous.continuousOn
  · apply Nonempty.image
    apply Nonempty.image
    exact (S.proto B.certificate.val.ty).interior_nonempty

/-- M8, V4 2.17(a): a common actual leaf identifies the entire certificate block.
The prescribed label identifies D and i; its full frame identifies the block frame. -/
theorem unique_at_leaf (D : KBlock Y)
    (v : S.RoleWord B.certificate.val.ty P.K) (w : S.RoleWord D.certificate.val.ty P.K)
    (h : B.leaf v = D.leaf w) : B = D := by
  have h_inj := placedLeaf_injective C _ _ _ _ h
  obtain ⟨h_cert_w, h_frame⟩ := h_inj
  have h_cert : B.certificate = D.certificate := congrArg (fun x => x.1) h_cert_w
  cases B with | mk cB fB hB =>
  cases D with | mk cD fD hD =>
  dsimp at h_cert h_cert_w h_frame
  subst h_cert
  have h_w : HEq v w := by
    cases h_cert_w
    rfl
  have h_w_eq : v = w := eq_of_heq h_w
  subst h_w_eq
  have h_frame_eq : fB = fD := by
    calc fB
      _ = (AffineIsometryEquiv.refl ℝ (E d)).trans fB := by rw [AffineIsometryEquiv.refl_trans]
      _ = ((LeafType.position ⟨cB, v⟩).symm.trans (LeafType.position ⟨cB, v⟩)).trans fB := by rw [AffineIsometryEquiv.symm_trans_self]
      _ = (LeafType.position ⟨cB, v⟩).symm.trans ((LeafType.position ⟨cB, v⟩).trans fB) := by rw [AffineIsometryEquiv.trans_assoc]
      _ = (LeafType.position ⟨cB, v⟩).symm.trans ((LeafType.position ⟨cB, v⟩).trans fD) := by rw [h_frame]
      _ = ((LeafType.position ⟨cB, v⟩).symm.trans (LeafType.position ⟨cB, v⟩)).trans fD := by rw [AffineIsometryEquiv.trans_assoc]
      _ = (AffineIsometryEquiv.refl ℝ (E d)).trans fD := by rw [AffineIsometryEquiv.symm_trans_self]
      _ = fD := by rw [AffineIsometryEquiv.refl_trans]
  subst h_frame_eq
  rfl

/-- M8, V4 2.17(a): actual whole certificate blocks with intersecting interiors coincide.
This uses only the actual-leaf subdivision witnesses and the physical tiling. -/
theorem eq_of_interior_meet (D : KBlock Y)
    (h : (interior B.carrier ∩ interior D.carrier).Nonempty) : B = D := by
  sorry

end KBlock

/-- M8, V4 2.17(b): occurrence identifies all decoded labels and composite frames. -/
theorem TemplateOccurs.tile_data (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) (φ : Iso d) (θ : Template P)
    (h : TemplateOccurs C Y φ θ) (z : FramedNode S × LeafType P) (hz : z ∈ θ.tiles) :
    ∃ t ∈ Y.tiles, compilerLeaf C t = z.2 ∧ compilerFrame C t = z.1.frame.trans φ := by
  exact ⟨placedLeaf C z.2 (z.1.frame.trans φ), h z hz, (compiler_decode_unique C _ _).1,
    (compiler_decode_unique C _ _).2⟩

/-- M8, V4 2.17(b): an occurring configuration's entire support consists of actual tiles. -/
theorem TemplateOccurs.support_subset (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) (φ : Iso d) (θ : Template P)
    (h : TemplateOccurs C Y φ θ) :
    Compiler.templateSupport C φ θ ⊆ ⋃ t ∈ Y.tiles, t.carrier := by
  intro x hx
  simp only [Compiler.templateSupport, Set.mem_iUnion] at hx
  obtain ⟨z, hz, hx⟩ := hx
  exact Set.mem_iUnion.mpr ⟨placedLeaf C z.2 (z.1.frame.trans φ),
    Set.mem_iUnion.mpr ⟨h z hz, hx⟩⟩

namespace KBlock

variable {C : ClusterData S P} {Y : MarkedTiling (systemM S P C)} (B : KBlock Y)

/-- M8, V4 2.17(a): the placed CORE carrier lies in its whole certificate block. -/
theorem core_support_subset : placedSet B.frame (Compiler.coreCarrier C B.certificate) ⊆
    B.carrier := by
  exact Set.image_mono Set.diff_subset

/-- M8, V4 2.17(a): every actual whole certificate carries the prescribed CORE rule.
This uses the actual standard leaves and their shared @ boundaries, independently
of an already constructed hierarchy on the output. -/
theorem core_rule_agree (x : (Compiler.coreRule C B.certificate).carrier) :
    Y.marking (B.frame x) = (Compiler.coreRule C B.certificate).mark x := by
  have hx := x.property
  have ht_x : ↑x ∈ Compiler.coreCarrier C B.certificate := hx
  have hx_cov : ↑x ∈ S.supertile P.K B.certificate.val.ty := by
    exact Set.diff_subset hx
  rw [← SubstSystem.native_cover] at hx_cov
  simp only [Set.mem_iUnion] at hx_cov
  obtain ⟨w, hw⟩ := hx_cov
  have hw2 : ↑x ∈ placedSet (LeafType.position (⟨B.certificate, w⟩ : LeafType P))
        (S.proto (LeafType.prototype (⟨B.certificate, w⟩ : LeafType P))).carrier := by
    change ↑x ∈ (S.nativeTile B.certificate.val.ty P.K w).carrier 0 at hw
    dsimp [FramedNode.carrier, placedSet] at hw
    have h_c_0 : S.supertile 0 (S.nativeTile B.certificate.val.ty P.K w).ty = (S.proto (S.nativeTile B.certificate.val.ty P.K w).ty).carrier := by
      ext y
      dsimp [SubstSystem.supertile]
      simp
    change ↑x ∈ placedSet (S.nativeTile B.certificate.val.ty P.K w).frame (S.proto (S.nativeTile B.certificate.val.ty P.K w).ty).carrier
    rw [← h_c_0]
    exact hw
  have ht := B.leaf_mem w
  have hx_t : B.frame ↑x ∈ (B.leaf w).carrier := by
    change B.frame ↑x ∈ placedSet ((LeafType.position ⟨B.certificate, w⟩).trans B.frame) (S.proto (LeafType.prototype ⟨B.certificate, w⟩)).carrier
    dsimp [placedSet]
    dsimp [placedSet] at hw2
    obtain ⟨y, hy, hy_eq⟩ := hw2
    exact ⟨y, hy, by change B.frame ((LeafType.position ⟨B.certificate, w⟩) y) = B.frame ↑x; rw [hy_eq]⟩
  have h_eq1 : Y.marking (B.frame ↑x) = (B.leaf w).mark ⟨B.frame ↑x, hx_t⟩ := Y.marking_eq_tile (B.leaf w) ht (B.frame ↑x) hx_t
  rw [h_eq1]
  change _ = Compiler.certificateColour C B.certificate x
  have h_eq2 : Compiler.certificateColour C B.certificate x = augmentedColour C (⟨B.certificate, w⟩ : LeafType P) ((LeafType.position (⟨B.certificate, w⟩ : LeafType P)).symm ↑x) := by
    exact Compiler.certificateColour_leaf C B.certificate w ↑x hw2
  rw [h_eq2]
  have h_eq3 : (B.leaf w).mark ⟨B.frame ↑x, hx_t⟩ = augmentedColour C (⟨B.certificate, w⟩ : LeafType P) ((LeafType.position (⟨B.certificate, w⟩ : LeafType P)).symm ↑x) := by
    change (placedLeaf C ⟨B.certificate, w⟩ ((LeafType.position ⟨B.certificate, w⟩).trans B.frame)).mark ⟨B.frame ↑x, hx_t⟩ = _
    change augmentedColour C ⟨B.certificate, w⟩ ((AffineIsometryEquiv.trans (LeafType.position ⟨B.certificate, w⟩) B.frame).symm (B.frame ↑x)) = _
    have h_symm : (AffineIsometryEquiv.trans (LeafType.position ⟨B.certificate, w⟩) B.frame).symm (B.frame ↑x) = ((LeafType.position ⟨B.certificate, w⟩).symm ↑x) := by
      show (LeafType.position ⟨B.certificate, w⟩).symm (B.frame.symm (B.frame ↑x)) = _
      rw [AffineIsometryEquiv.symm_apply_apply]
    rw [h_symm]
  exact h_eq3

/-- M8, V4 2.17(a): every leaf's certificate-frame formula recovers the block frame. -/
theorem frame_from_leaf (w : S.RoleWord B.certificate.val.ty P.K) :
    (compilerLeaf C (B.leaf w)).position.symm.trans (compilerFrame C (B.leaf w)) =
      B.frame := by
  have hw : B.leaf w = placedLeaf C ⟨B.certificate, w⟩
    ((LeafType.position (⟨B.certificate, w⟩ : LeafType P)).trans B.frame) := rfl
  have h2 := placedLeaf_decode C (B.leaf w)
  rw [hw] at h2
  have ⟨hl, hφ⟩ := placedLeaf_injective C _ _ _ _ h2
  rw [hw, hl, hφ]
  ext
  simp

end KBlock

/-- M8, V4 2.17(b): an actual allowed template carries the corresponding whole
EVENT rule, including the closed trigger sphere and every closed readout ball. -/
theorem TemplateOccurs.event_rule_agree (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) (φ : Iso d) (e : Compiler.EventIndex S P)
    (h : TemplateOccurs C Y φ e.template) (x : (Compiler.eventRule C e).carrier) :
    Y.marking (φ x) = (Compiler.eventRule C e).mark x := by
  sorry

/-- M8, V4 2.17(b)--(c): the END event needed by the parser, with the actual
allowed template, cone coverage and all meeting tiles in one existence statement.
An actual central tile supplies the nonempty configuration through properness. -/
theorem compiler_end_event (C : ClusterData S P) (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (j : EndSlot (compilerLeaf C t)) :
    ∃ θ ∈ allowedTemplates (.end_ j),
      TemplateOccurs C Y (compilerFrame C t) θ ∧
      Compiler.endSector (compilerFrame C t) j ∩
          ball (Compiler.endVertex (compilerFrame C t) j) (Compiler.coneRadius S P) ⊆
        Compiler.templateSupport C (compilerFrame C t) θ ∧
      ∀ u ∈ Y.tiles,
        (interior u.carrier ∩ interior (Compiler.endSector (compilerFrame C t) j) ∩
          ball (Compiler.endVertex (compilerFrame C t) j)
            (Compiler.coneRadius S P)).Nonempty →
        ∃ z ∈ θ.tiles, u = placedLeaf C z.2 (z.1.frame.trans (compilerFrame C t)) := by
  obtain ⟨θ, hθ, _, hactual⟩ := compiler_events C Y hY t ht (.end_ j)
  exact ⟨θ, hθ, hactual, compiler_coverage C Y hY t ht j θ hθ hactual⟩

/-- M3/M6, V4 2.11, 2.14(c): every output projects to its exact native old marking.
This does not assert that the projected output belongs to the source species. -/
theorem compiler_projection (C : ClusterData S P) (Y : MarkedTiling (systemM S P C))
    (x : E d) :
    π S P (Y.marking x) = oldMarking (Y.project (nativeDecoration S P C)) x :=
  Y.project_marking (nativeDecoration S P C) x

/-- M6, V4 2.14(a): the lift has the single colour @ on every physical tile boundary. -/
theorem honestLift_boundary (C : ClusterData S P) (U : HonestSource S)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ (honestLift C U).tiles)
    (x : E d) (hx : x ∈ frontier t.carrier) :
    (honestLift C U).marking x = Colour.boundary :=
  compiler_boundary C (honestLift C U) t ht x hx

end Enforce
