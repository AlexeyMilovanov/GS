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

/-- M3, V4 2.11: the indexed allowed template family is finite. -/
theorem eventIndices_finite (S : SubstSystem d) (P : Params S) :
    Finite (EventIndex S P) := by
  sorry

/-- M3, V4 2.11: enumeration of EVENT rule indices. -/
instance eventIndexFintype (S : SubstSystem d) (P : Params S) :
    Fintype (EventIndex S P) := by
  letI := eventIndices_finite S P
  exact Fintype.ofFinite _

/-- M3, V4 2.11: every allowed template has the prescribed central label. -/
theorem allowedTemplate_central (l : LeafType P) (j : EventSlot l) (θ : Template P)
    (hθ : θ ∈ allowedTemplates j) : θ.central = l := by
  sorry

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

/-- M3, V4 2.11: gluing agrees with each native leaf at every shared point. -/
theorem certificateColour_leaf (C : ClusterData S P) (D : CertificateSymbol S P)
    (w : S.RoleWord D.val.ty P.K) (x : E d)
    (hx : x ∈ placedSet (LeafType.position (⟨D, w⟩ : LeafType P))
      (S.proto (LeafType.prototype (⟨D, w⟩ : LeafType P))).carrier) :
    certificateColour C D x = augmentedColour C (⟨D, w⟩ : LeafType P)
      ((LeafType.position (⟨D, w⟩ : LeafType P)).symm x) := by
  sorry

/-- M3, V4 2.11: CORE supports are compact, as closed subsets of supertiles. -/
theorem coreCarrier_compact (C : ClusterData S P) (D : CertificateSymbol S P) :
    IsCompact (coreCarrier C D) := by
  sorry

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
  sorry

/-- M3, V4 2.11: agreement with the central trigger marking, including its sphere. -/
theorem eventColour_trigger (C : ClusterData S P) (e : EventIndex S P) (x : E d)
    (hx : x ∈ C.enclosing e.leaf (.trigger e.slot)) :
    eventColour C e x = augmentedColour C e.leaf x := by
  classical
  simp only [eventColour, if_pos hx]

/-- M3, V4 2.11: agreement with every other tile's whole closed readout ball. -/
theorem eventColour_readout (C : ClusterData S P) (e : EventIndex S P)
    (z : FramedNode S × LeafType P) (hz : z ∈ eventReadouts e) (x : E d)
    (hx : x ∈ readoutRegion C z) :
    eventColour C e x = augmentedColour C z.2 (z.1.frame.symm x) := by
  sorry

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
  sorry

/-- M3, V4 2.11: every catalogue member projects to @ on its entire frontier. -/
theorem decoration_frontier (C : ClusterData S P)
    (Q : {Q // Q ∈ (systemM S P C).physical}) (x : Q.val.carrier)
    (hx : x.val ∈ frontier Q.val.carrier) : π S P (Q.val.mark x) = none := by
  sorry

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
  sorry

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
  sorry

/-- M3/M5, V4 2.11, 2.13: the decoded pair is unique, not a representative ambiguity. -/
theorem compiler_decode_unique (C : ClusterData S P) (l : LeafType P) (φ : Iso d) :
    compilerLeaf C (placedLeaf C l φ) = l ∧
      compilerFrame C (placedLeaf C l φ) = φ :=
  placedLeaf_injective C _ _ _ _ (placedLeaf_decode C _)

/-- M4, V4 2.12(i): no CORE microball colour occurs in any EVENT rule. -/
theorem colour_disjointness_i (C : ClusterData S P) (e : Compiler.EventIndex S P)
    (l : LeafType P) (a : Fin (d + 1)) (x : (Compiler.eventRule C e).carrier) :
    (Compiler.eventRule C e).mark x ≠ Colour.core l a := by
  sorry

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

/-- M5, V4 2.13: agreement on an entire cluster forces one actual tile of the
exact leaf type in the exact source frame. This applies to every marked tiling,
without properness, and equality is of full isometries, including reflections. -/
theorem cluster_rigidity (C : ClusterData S P) (Y : MarkedTiling (systemM S P C))
    (l : LeafType P) (κ : ClusterKind l) (ψ : Iso d)
    (h : ∀ x ∈ C.cluster l κ, Y.marking (ψ x) = augmentedColour C l x) :
    ∃ t ∈ Y.tiles, compilerLeaf C t = l ∧ ψ = compilerFrame C t := by
  sorry

section MarkedMotion

variable {X : Type} {M : C1System d X}
omit [Fact (2 ≤ d)]

/-- M6, V4 2.14(d): isometric transport of a physical marked tile is realizable. -/
theorem PlacedMarkedTile.move_realization (t : PlacedMarkedTile M) (g : Iso d) :
    ∃ Q ∈ M.physical, ∃ φ : Iso d,
      (t.toMarkedSet.move g).carrier = placedSet φ Q.carrier ∧
        ∀ (x : Q.carrier) (hx : φ x ∈ (t.toMarkedSet.move g).carrier),
          (t.toMarkedSet.move g).mark ⟨φ x, hx⟩ = Q.mark x := by
  sorry

/-- M6, V4 2.14(d): actual isometric motion of a marked carrier. -/
def PlacedMarkedTile.move (t : PlacedMarkedTile M) (g : Iso d) : PlacedMarkedTile M where
  toMarkedSet := t.toMarkedSet.move g
  realization := t.move_realization g

/-- M6, V4 2.14(d): moving a marked tiling preserves coverage. -/
theorem MarkedTiling.move_cover (Y : MarkedTiling M) (g : Iso d) (x : E d) :
    ∃ t ∈ (fun t : PlacedMarkedTile M => t.move g) '' Y.tiles, x ∈ t.carrier := by
  sorry

/-- M6, V4 2.14(d): moving a marked tiling preserves interior disjointness. -/
theorem MarkedTiling.move_disjoint (Y : MarkedTiling M) (g : Iso d) :
    ((fun t : PlacedMarkedTile M => t.move g) '' Y.tiles).PairwiseDisjoint
      (fun t => interior t.carrier) := by
  sorry

/-- M6, V4 2.14(d): moving a marked tiling preserves agreement at every shared point. -/
theorem MarkedTiling.move_agree (Y : MarkedTiling M) (g : Iso d) :
    ∀ t ∈ (fun t : PlacedMarkedTile M => t.move g) '' Y.tiles,
      ∀ u ∈ (fun t : PlacedMarkedTile M => t.move g) '' Y.tiles,
        ∀ x (ht : x ∈ t.carrier) (hu : x ∈ u.carrier), t.mark ⟨x, ht⟩ = u.mark ⟨x, hu⟩ := by
  sorry

/-- M6, V4 2.14(d): the full isometry action on pointwise marked tilings. -/
def MarkedTiling.move (Y : MarkedTiling M) (g : Iso d) : MarkedTiling M where
  tiles := (fun t : PlacedMarkedTile M => t.move g) '' Y.tiles
  cover := Y.move_cover g
  disjoint := Y.move_disjoint g
  agreement := Y.move_agree g

/-- M6, V4 2.14(d): the transported global function has the expected pointwise value. -/
theorem MarkedTiling.move_marking (Y : MarkedTiling M) (g : Iso d) (x : E d) :
    (Y.move g).marking (g x) = Y.marking x := by
  sorry

/-- M6, V4 2.14(d): properness is invariant under every Euclidean isometry. -/
theorem MProper.move (Y : MarkedTiling M) (hY : MProper Y) (g : Iso d) :
    MProper (Y.move g) := by
  sorry

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

/-- M6, V4 2.14(d), 1.11: moving every frame and every legal context gives
an honest source. The input source supplies nonemptiness of the transport problem. -/
theorem honest_move_exists (U : HonestSource S) (g : Iso d) :
    ∃ V : HonestSource S, MovedSource U V g := by
  sorry

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
  sorry

/-- M6, V4 2.14(d): identity motion preserves the entire honest hierarchy. -/
theorem HonestSource.move_refl (U : HonestSource S) :
    U.move (AffineIsometryEquiv.refl ℝ (E d)) = U := by
  sorry

/-- M6, V4 2.14(d): successive motions compose on full honest sources. -/
theorem HonestSource.move_trans (U : HonestSource S) (g h : Iso d) :
    (U.move g).move h = U.move (g.trans h) := by
  sorry

/-- M6, V4 2.14(d): leaf types are intrinsic to the hierarchy under all isometries.
The equality includes the whole joint certificate and the exact leaf address. -/
theorem leafTypeOf_move (U : HonestSource S) (g : Iso d) (q : U.Node) (hq : q.1 = 0) :
    leafTypeOf (U.move g) P (U.movedNode g q) hq = leafTypeOf U P q hq := by
  sorry

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
  sorry

/-- M6, V4 2.14: the proposed lift covers the whole space by source ground coverage. -/
theorem honestLift_cover (C : ClusterData S P) (U : HonestSource S) (x : E d) :
    ∃ t ∈ honestLiftTiles C U, x ∈ t.carrier := by
  sorry

/-- M6, V4 2.14: the proposed lifted physical tiles have disjoint interiors. -/
theorem honestLift_disjoint (C : ClusterData S P) (U : HonestSource S) :
    (honestLiftTiles C U).PairwiseDisjoint (fun t => interior t.carrier) := by
  sorry

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
  sorry

/-- M6, V4 2.14(b): the honest lift is proper, by CORE coverage and honest event rows. -/
theorem honestLift_proper (C : ClusterData S P) (U : HonestSource S) :
    MProper (honestLift C U) := by
  sorry

/-- M6, V4 2.14(c): exact old marking at every point, including the boundary skeleton. -/
theorem honestLift_projection (C : ClusterData S P) (U : HonestSource S) (x : E d) :
    π S P ((honestLift C U).marking x) = oldMarking U.tiling x := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- M8, V4 2.17(a): a tile lies in a unique whole certificate block with its address.
Existence comes from properness; uniqueness is of certificate and frame, not support alone. -/
theorem compilerBlock_exists_unique (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles) :
    ∃! B : KBlock Y, ∃ w : S.RoleWord B.certificate.val.ty P.K, B.leaf w = t := by
  sorry

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
  sorry

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
  sorry

/-- M4, V4 2.12(iii): the placed physical family is locally finite, including
its closed carriers; every bounded set meets only finitely many tiles. -/
theorem compiler_tiles_locallyFinite (C : ClusterData S P)
    (Y : MarkedTiling (systemM S P C)) :
    LocallyFinite (fun t : {t // t ∈ Y.tiles} => t.val.carrier) ∧
      ∀ B : Set (E d), Bornology.IsBounded B →
        {t : PlacedMarkedTile (systemM S P C) |
          t ∈ Y.tiles ∧ (B ∩ t.carrier).Nonempty}.Finite := by
  sorry

namespace Compiler

/-- M3/M5, V4 2.11, 2.13: all CORE clusters survive all removed open trigger balls. -/
theorem core_contains_core_clusters (C : ClusterData S P) (D : CertificateSymbol S P)
    (w : S.RoleWord D.val.ty P.K) :
    placedSet (LeafType.position (⟨D, w⟩ : LeafType P))
      (C.cluster (⟨D, w⟩ : LeafType P) .core) ⊆ coreCarrier C D := by
  sorry

/-- M3/M5, V4 2.11, 2.13: on every surviving CORE cluster the rule is the leaf marking. -/
theorem core_marks_core_cluster (C : ClusterData S P) (D : CertificateSymbol S P)
    (w : S.RoleWord D.val.ty P.K) (x : E d)
    (hx : x ∈ C.cluster (⟨D, w⟩ : LeafType P) .core) :
    certificateColour C D ((LeafType.position (⟨D, w⟩ : LeafType P)) x) =
      augmentedColour C (⟨D, w⟩ : LeafType P) x := by
  sorry

/-- M3/M5, V4 2.11, 2.13: an EVENT support contains the entire central TRIG cluster. -/
theorem event_contains_trigger_cluster (C : ClusterData S P) (e : EventIndex S P) :
    C.cluster e.leaf (.trigger e.slot) ⊆ eventCarrier C e := by
  exact (C.cluster_subset_enclosing e.leaf (.trigger e.slot)).trans Set.subset_union_left

/-- M3/M5, V4 2.11, 2.13: an EVENT support contains every other tile's whole RO cluster. -/
theorem event_contains_readout_cluster (C : ClusterData S P) (e : EventIndex S P)
    (z : FramedNode S × LeafType P) (hz : z ∈ eventReadouts e) :
    placedSet z.1.frame (C.cluster z.2 .readout) ⊆ eventCarrier C e := by
  sorry

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
  sorry

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
  sorry

/-- M8, V4 2.17(a): an honest certificate's leaf state is its depth-K table entry. -/
theorem certificate_leaf_state (D : CertificateSymbol S P)
    (w : S.RoleWord D.val.ty P.K) :
    D.val.table P.K le_rfl w = (D.val.leaves w).state := by
  sorry

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
  sorry

/-- M8, V4 2.17(a): the standard native leaf interiors form a disjoint subdivision. -/
theorem leaves_disjoint : Pairwise (fun v w : S.RoleWord B.certificate.val.ty P.K =>
    Disjoint (interior (B.leaf v).carrier) (interior (B.leaf w).carrier)) := by
  sorry

/-- M8, V4 2.17(a): the full closed block carrier is compact and regular closed. -/
theorem carrier_regular : IsCompact B.carrier ∧ IsRegularClosed B.carrier := by
  sorry

/-- M8, V4 2.17(a): the block has genuine full-dimensional connected interior. -/
theorem carrier_interior : IsConnected (interior B.carrier) ∧
    (interior B.carrier).Nonempty := by
  sorry

/-- M8, V4 2.17(a): a common actual leaf identifies the entire certificate block.
The prescribed label identifies D and i; its full frame identifies the block frame. -/
theorem unique_at_leaf (D : KBlock Y)
    (v : S.RoleWord B.certificate.val.ty P.K) (w : S.RoleWord D.certificate.val.ty P.K)
    (h : B.leaf v = D.leaf w) : B = D := by
  sorry

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
  sorry

/-- M8, V4 2.17(a): every leaf's certificate-frame formula recovers the block frame. -/
theorem frame_from_leaf (w : S.RoleWord B.certificate.val.ty P.K) :
    (compilerLeaf C (B.leaf w)).position.symm.trans (compilerFrame C (B.leaf w)) =
      B.frame := by
  sorry

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
