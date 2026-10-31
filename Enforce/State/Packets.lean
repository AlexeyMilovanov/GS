import Enforce.State.State

/-!
# One-state packets, pre-patterns, and certificates

Q8--Q11, V4 2.5--2.7 and V4 8.1. A packet has just one highest state and the
intervening role word. Its honest alphabet is an image, not the ambient tuple type.
Decoding reconstructs all intermediate states, then tests the head-determined mask.
FAULT packets are `none`, separate from every non-NULL packet.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- Q8, V4 2.5: an actual primitive occurrence, with its birth parent and incidence.
The parent has positive height, so both paired serving children actually exist. -/
structure PrimitiveOccurrence (U : HonestSource S) (P : Params S) where
  /-- Q8, V4 2.5: the birth node in the fixed honest hierarchy. -/
  birth : U.Node
  /-- Q8, V4 2.5: the birth node has children. -/
  positive : 1 ≤ birth.1
  /-- Q8, V4 2.5: canonical side-independent first-generation incidence. -/
  incidence : P.Incidence
  /-- Q8, V4 2.5: this incidence belongs to this birth-parent type. -/
  parent_type : incidence.val.ty = birth.2.val.ty

/-- Q8, V4 2.5: the positioned primitive facet, in actual ambient coordinates. -/
def PrimitiveOccurrence.carrier {U : HonestSource S} {P : Params S}
    (g : PrimitiveOccurrence U P) : Set (E d) :=
  P.incidencePlacement g.birth.2.val g.birth.1 g.incidence ''
    g.incidence.val.leftFacet.val.carrier

/-- Q8, V4 2.5: geometric mask, with slots indexed from the birth parent. -/
def mask (U : HonestSource S) (P : Params S) (g : PrimitiveOccurrence U P)
    (j : Fin P.k) : Prop :=
  P.InPrincipal (U.hierarchy.ancestor g.birth j.val).2.val
    (U.hierarchy.ancestor g.birth j.val).1 g.carrier

/-- Q8, V4 2.5: slot zero is PRESENT because all first-generation facets are required. -/
theorem mask_zero (U : HonestSource S) (P : Params S) (g : PrimitiveOccurrence U P) :
    mask U P g ⟨0, P.k_pos⟩ := by
  sorry

/-- Q8, V4 2.5, 8.1: the actual finite set of PRESENT slots. -/
def presentSlots (U : HonestSource S) (P : Params S) (g : PrimitiveOccurrence U P) :
    Finset (Fin P.k) := by
  classical
  exact Finset.univ.filter (mask U P g)

/-- Q8, V4 8.1: the PRESENT-slot set is nonempty, so its maximum exists. -/
theorem presentSlots_nonempty (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) : (presentSlots U P g).Nonempty := by
  classical
  exact ⟨⟨0, P.k_pos⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, mask_zero U P g⟩⟩

/-- Q8, V4 8.1: highest PRESENT ancestor slot. -/
def topSlot (U : HonestSource S) (P : Params S) (g : PrimitiveOccurrence U P) :
    Fin P.k := (presentSlots U P g).max' (presentSlots_nonempty U P g)

/-- Q8, V4 8.1: the compressed non-NULL packet tuple.
Only `honestPackets` is the admissible packet alphabet. No consistency of arbitrary
ambient tuples is asserted; NULL remains an outer `Option`. -/
structure Packet (P : Params S) where
  /-- Q8, V4 8.1: side-independent incidence. -/
  incidence : P.Incidence
  /-- Q8, V4 8.1: largest PRESENT index. -/
  jstar : Fin P.k
  /-- Q8, V4 8.1: the state at that index. -/
  sstar : State P
  /-- Q8, V4 8.1: bottom-up roles between the head and the highest state. -/
  roles : Fin jstar.val → S.Role

/-- Q8, V4 8.1: actual compressed packet of a positioned primitive facet. -/
def packetOf (U : HonestSource S) (P : Params S) (g : PrimitiveOccurrence U P) :
    Packet P where
  incidence := g.incidence
  jstar := topSlot U P g
  sstar := stateOf U P (U.hierarchy.ancestor g.birth (topSlot U P g).val)
  roles := fun j => U.hierarchy.nodeRole (U.hierarchy.ancestor g.birth j.val)

/-- Q9, V4 2.6(a): prototype type of a slot, read from a head's upward address. -/
def slotType {P : Params S} (s : State P) (j : Fin P.k) : S.ι := by
  classical
  exact if hj : j.val = 0 then s.ty else
    (s.address ⟨j.val - 1, by omega⟩).1

/-- Q9, V4 2.6(a): the downward role list from slot `j` to the head. -/
def slotRoles {P : Params S} (s : State P) (j : Fin P.k) : List S.Role :=
  (List.ofFn (fun a : Fin j.val => s.address ⟨a.val, lt_trans a.isLt j.isLt⟩)).reverse

/-- Q9, V4 2.6(a): mask lookup using only incidence and head state.
The normalized positioned primitive carrier is compared with the finite `E_A` table. -/
def packetMask (P : Params S) (ι : P.Incidence) (s : State P) (j : Fin P.k) : Prop :=
  ∃ f ∈ P.E_A (slotType s j),
    f.carrier = wordPlacement (slotRoles s j) '' (S.σ.symm '' ι.val.positioned)

namespace Packet

variable {P : Params S}

/-- Q8/Q9, V4 8.1: descend a specified number of steps from the highest state.
The role at bottom-up index `jstar-1-a` is used in the next downward step. -/
def descend (q : Packet P) : ℕ → State P
  | 0 => q.sstar
  | a + 1 => if ha : a < q.jstar.val then
      childMap P (q.descend a) (q.roles ⟨q.jstar.val - 1 - a, by omega⟩)
    else q.descend a

/-- Q8, V4 8.1: reconstructed state at any slot below the highest slot.
For raw tuples, indices above the highest slot are ignored by `decode`. -/
def reconstructed (q : Packet P) (j : Fin P.k) : State P :=
  q.descend (q.jstar.val - j.val)

/-- Q8/Q9, V4 8.1: reconstructed head, including the `jstar = 0` case. -/
def head (q : Packet P) : State P := q.reconstructed ⟨0, P.k_pos⟩

/-- Q8/Q9, V4 8.1: the full mask reconstructed from incidence and head. -/
def mask (q : Packet P) (j : Fin P.k) : Prop := packetMask P q.incidence q.head j

end Packet

/-- Q8/Q9, V4 8.1: recover exactly the PRESENT states by child-map descent.
The extra bound is automatic on the honest alphabet, where `jstar` is its maximum. -/
def decode {P : Params S} (q : Packet P) (j : Fin P.k) : Option (State P) := by
  classical
  exact if j.val ≤ q.jstar.val ∧ q.mask j then some (q.reconstructed j) else none

/-- Q9, V4 2.6(a): the geometric mask is a function of incidence and birth state. -/
theorem packet_mask_fn (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (j : Fin P.k) :
    mask U P g j ↔ packetMask P g.incidence (stateOf U P g.birth) j := by
  sorry

/-- Q8/Q9, V4 8.1: descent reconstructs even the intermediate ABSENT states. -/
theorem reconstructed_spec (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (j : Fin P.k) (hj : j ≤ topSlot U P g) :
    (packetOf U P g).reconstructed j = stateOf U P (U.hierarchy.ancestor g.birth j.val) :=
  by sorry

/-- Q8/Q9, V4 8.1: lossless decoding, with precisely the geometric mask.
This replaces a separate D-path invariant: it identifies every retained slot state. -/
theorem decode_spec (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (j : Fin P.k) :
    decode (packetOf U P g) j = (by
      classical
      exact if mask U P g j then
        some (stateOf U P (U.hierarchy.ancestor g.birth j.val)) else none) := by
  sorry

/-- Q8, V4 8.1: the packet head is exactly the state of its birth parent. -/
theorem packet_head (U : HonestSource S) (P : Params S) (g : PrimitiveOccurrence U P) :
    (packetOf U P g).head = stateOf U P g.birth := by
  have hk : NeZero P.k := ⟨ne_of_gt P.k_pos⟩
  have h := reconstructed_spec U P g ⟨0, P.k_pos⟩ (Fin.zero_le _)
  have h2 : U.hierarchy.ancestor g.birth 0 = g.birth := rfl
  rw [h2] at h
  exact h

/-- Q8, V4 2.5, 8.1: admissible packets are exactly the honest compressed image. -/
def honestPackets (S : SubstSystem d) (P : Params S) : Set (Packet P) :=
  {q | ∃ (U : HonestSource S) (g : PrimitiveOccurrence U P), packetOf U P g = q}

/-- Q8, V4 2.5: the honest packet alphabet is finite. -/
theorem packets_finite (S : SubstSystem d) (P : Params S) :
    (honestPackets S P).Finite := by
  sorry

namespace HonestSource

variable (U : HonestSource S)

/-- Q8/Q9, V4 2.5--2.6: a finite provider determines an actual primitive occurrence.
These properties follow from the existing provider incidence and birth-height API. -/
theorem providerOccurrence_data (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f) :
    1 ≤ (U.hierarchy.birthParent q f hf).1 ∧
      (U.recordIncidence P q f hf).val.ty = (U.hierarchy.birthParent q f hf).2.val.ty :=
  by sorry

/-- Q8/Q9, V4 2.5--2.6: the canonical primitive occurrence of a finite provider. -/
def providerOccurrence (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) : PrimitiveOccurrence U P where
  birth := U.hierarchy.birthParent q f hf
  positive := (U.providerOccurrence_data P q f hf).1
  incidence := U.recordIncidence P q f hf
  parent_type := (U.providerOccurrence_data P q f hf).2

/-- Q8/Q9, V4 2.5--2.6: attach the provider's packet; faults receive NULL.
This applies to all node facets and restricts to pre-patterns at native height. -/
def facetPacket (P : Params S) (q : U.Node) (f : FacetName S q.2.val.ty) :
    Option (Packet P) := by
  classical
  exact if hf : U.hierarchy.IsFault q f then none else
    some (packetOf U P (U.providerOccurrence P q f hf))

end HonestSource

/-- Q9, V4 2.6(c): every native facet piece on either side of a primitive facet
has its canonical incidence and carries that primitive facet's single packet. -/
theorem packet_attached (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (t : U.Node) (ht : t.1 = 0)
    (f : FacetName S t.2.val.ty) (hfg : t.2.val.cell t.1 f.val ⊆ g.carrier) :
    (∃ hf : ¬ U.hierarchy.IsFault t f,
      (U.recordOf P t f hf).incidence = g.incidence) ∧
      U.facetPacket P t f = some (packetOf U P g) := by
  sorry

/-- Q9, V4 2.6(d): packets restrict unchanged along inherited facet tracks. -/
theorem packet_inherited (U : HonestSource S) (P : Params S) (q c : U.Node)
    (a : ℕ) (hca : U.hierarchy.ancestor c a = q)
    (f : FacetName S q.2.val.ty) (g : FacetName S c.2.val.ty)
    (hgf : c.2.val.cell c.1 g.val ⊆ q.2.val.cell q.1 f.val) :
    U.facetPacket P c g = U.facetPacket P q f := by
  sorry

/-- Q8/Q9, V4 2.5, 8.1: every honest non-NULL packet has a PRESENT head and
its top index is exactly the maximum reconstructed mask index. -/
theorem honest_packet_admissible (P : Params S) (q : Packet P)
    (hq : q ∈ honestPackets S P) :
    decode q ⟨0, P.k_pos⟩ = some q.head ∧ q.head.ty = q.incidence.val.ty ∧
      q.mask q.jstar ∧ (∀ j, q.mask j → j ≤ q.jstar) ∧
      ∀ j s, decode q j = some s → s ∈ honestStates S P := by
  sorry

/-- Q10, V4 §2.4: the pre-pattern symbol, before marker clusters are added.
Its marker is the fixed marker of its prototype; the state and packets may be raw.
The admissible alphabet is the actual range `honestPrePatterns`. -/
structure PrePattern (P : Params S) where
  /-- Q10, V4 §2.4: native prototype. -/
  ty : S.ι
  /-- Q10, V4 §2.4: the labelled frame-marker balls. -/
  frameMarker : MarkerData S ty
  /-- Q10, V4 §2.4: marker data are fixed once and for all. -/
  frameMarker_eq : frameMarker = P.marker ty
  /-- Q10, V4 §2.4: full state of the native node. -/
  state : State P
  /-- Q10, V4 §2.4: the state belongs to the prototype. -/
  state_type : state.ty = ty
  /-- Q10, V4 §2.4: provider packets or NULL at every prototype facet. -/
  packets : FacetName S ty → Option (Packet P)

/-- Q10, V4 §2.4: the actual pre-pattern of a native tile, in its exact frame. -/
def prePatternOf (U : HonestSource S) (P : Params S) (t : U.Node) (_ht : t.1 = 0) :
    PrePattern P where
  ty := t.2.val.ty
  frameMarker := P.marker t.2.val.ty
  frameMarker_eq := rfl
  state := stateOf U P t
  state_type := rfl
  packets := U.facetPacket P t

/-- Q10, V4 §2.4: all honest native pre-patterns, including their marker data. -/
def honestPrePatterns (S : SubstSystem d) (P : Params S) : Set (PrePattern P) :=
  {w | ∃ (U : HonestSource S) (t : U.Node) (ht : t.1 = 0), prePatternOf U P t ht = w}

/-- Q10, V4 §2.4: the pre-pattern alphabet is finite. -/
theorem prePatterns_finite (S : SubstSystem d) (P : Params S) :
    (honestPrePatterns S P).Finite := by
  sorry

namespace HonestSource

variable (U : HonestSource S)

/-- Q11, V4 2.7: a standard descendant is an actual member of the honest hierarchy. -/
theorem descendant_mem (q : U.Node) (a : ℕ) (ha : a ≤ q.1) (w : S.RoleWord q.2.val.ty a) :
    (S.descendantNode q.2.val.ty (q.1 - a) a w).move q.2.val.frame ∈
      U.hierarchy.nodes (q.1 - a) := by
  sorry

/-- Q11, V4 2.7: the actual source node at an exact downward address. -/
def descendant (q : U.Node) (a : ℕ) (ha : a ≤ q.1) (w : S.RoleWord q.2.val.ty a) :
    U.Node :=
  ⟨q.1 - a, ⟨(S.descendantNode q.2.val.ty (q.1 - a) a w).move q.2.val.frame,
    U.descendant_mem q a ha w⟩⟩

/-- Q11, V4 2.7: descendant type is independent of its remaining height. -/
theorem descendant_type (q : U.Node) (a : ℕ) (ha : a ≤ q.1)
    (w : S.RoleWord q.2.val.ty a) :
    (U.descendant q a ha w).2.val.ty = (S.nativeTile q.2.val.ty a w).ty := by
  sorry

end HonestSource

/-- Q11, V4 2.7: a full height-K certificate, with role-word indexed data.
The state table includes the root, all inner nodes, and the native leaves. -/
structure Certificate (P : Params S) where
  /-- Q11, V4 2.7: type of the height-K root. -/
  ty : S.ι
  /-- Q11, V4 2.7: pre-patterns of all depth-K leaves. -/
  leaves : S.RoleWord ty P.K → PrePattern P
  /-- Q11, V4 2.7: leaf prototype types follow the fixed substitution geometry. -/
  leaf_type : ∀ w, (leaves w).ty = (S.nativeTile ty P.K w).ty
  /-- Q11, V4 2.7: states at every downward depth at most K. -/
  table : ∀ a : ℕ, a ≤ P.K → S.RoleWord ty a → State P
  /-- Q11, V4 2.7: every table entry has its prescribed prototype. -/
  table_type : ∀ a ha w, (table a ha w).ty = (S.nativeTile ty a w).ty

/-- Q11, V4 2.7: the actual certificate of a height-K source node. -/
def certOf (U : HonestSource S) (P : Params S) (B : FramedNode S)
    (hB : B ∈ U.hierarchy.nodes P.K) : Certificate P := by
  let q : U.Node := ⟨P.K, ⟨B, hB⟩⟩
  exact {
    ty := B.ty
    leaves := fun w => prePatternOf U P (U.descendant q P.K le_rfl w) (Nat.sub_self P.K)
    leaf_type := fun w => U.descendant_type q P.K le_rfl w
    table := fun a ha w => stateOf U P (U.descendant q a ha w)
    table_type := fun a ha w => U.descendant_type q a ha w }

/-- Q11, V4 2.7: certificates are the joint honest image, retaining all correlations. -/
def honestCerts (S : SubstSystem d) (P : Params S) : Set (Certificate P) :=
  {D | ∃ (U : HonestSource S) (B : FramedNode S) (hB : B ∈ U.hierarchy.nodes P.K),
    certOf U P B hB = D}

/-- Q11, V4 2.7: the finite certificate catalogue. -/
theorem certs_finite (S : SubstSystem d) (P : Params S) :
    (honestCerts S P).Finite := by
  sorry

/-- Q11, V4 2.7: a certificate with one of its exact depth-K leaf addresses. -/
abbrev LeafType (P : Params S) :=
  Σ D : {D // D ∈ honestCerts S P}, S.RoleWord D.val.ty P.K

namespace LeafType

variable {P : Params S}

/-- Q11, V4 2.7: prototype of a leaf type, fixed by its role word. -/
def prototype (l : LeafType P) : S.ι := (S.nativeTile l.1.val.ty P.K l.2).ty

/-- Q11, V4 2.7: the native leaf's relative frame inside its certificate block. -/
def position (l : LeafType P) : Iso d := (S.nativeTile l.1.val.ty P.K l.2).frame

/-- Q11, V4 2.7: pre-pattern read from the certificate's indicated component. -/
def prePattern (l : LeafType P) : PrePattern P := l.1.val.leaves l.2

/-- Q11, V4 2.7: the component has exactly the leaf prototype type. -/
theorem prePattern_type (l : LeafType P) : l.prePattern.ty = l.prototype :=
  l.1.val.leaf_type l.2

end LeafType

/-- Q11, V4 2.7: finitely many leaf types, even though the ambient state type is infinite. -/
theorem leafTypes_finite (P : Params S) : Finite (LeafType P) := by
  sorry

namespace HonestSource

variable (U : HonestSource S)

/-- Q11, V4 2.7: the K-ancestor of a native tile really has height K. -/
theorem certificateAncestor_mem (P : Params S) (t : U.Node) (ht : t.1 = 0) :
    (U.hierarchy.ancestor t P.K).2.val ∈ U.hierarchy.nodes P.K := by
  have h := (U.hierarchy.ancestor t P.K).2.property
  have hh : (U.hierarchy.ancestor t P.K).1 = P.K := by
    rw [U.hierarchy.ancestor_height, ht, zero_add]
  simpa only [hh] using h

/-- Q11, V4 2.7: the native tile has one exact role-word address below its K-ancestor.
Frames, rather than just carriers, are identified by the coherent hierarchy. -/
theorem leafIndex_exists (P : Params S) (t : U.Node) (ht : t.1 = 0) :
    ∃! w : S.RoleWord (U.hierarchy.ancestor t P.K).2.val.ty P.K,
      (S.nativeTile (U.hierarchy.ancestor t P.K).2.val.ty P.K w).move
        (U.hierarchy.ancestor t P.K).2.val.frame = t.2.val := by
  sorry

/-- Q11, V4 2.7: the actual role-word address of a native leaf. -/
def leafIndex (P : Params S) (t : U.Node) (ht : t.1 = 0) :
    S.RoleWord (U.hierarchy.ancestor t P.K).2.val.ty P.K :=
  Classical.choose (U.leafIndex_exists P t ht)

end HonestSource

/-- Q11, V4 2.7: the actual leaf type determined by the native tile's K-ancestor. -/
def leafTypeOf (U : HonestSource S) (P : Params S) (t : U.Node) (ht : t.1 = 0) :
    LeafType P :=
  ⟨⟨certOf U P (U.hierarchy.ancestor t P.K).2.val (U.certificateAncestor_mem P t ht),
    ⟨U, (U.hierarchy.ancestor t P.K).2.val, U.certificateAncestor_mem P t ht, rfl⟩⟩,
    U.leafIndex P t ht⟩

/-- Q11, V4 2.7: a tile's pre-pattern is exactly its certificate's indicated component. -/
theorem prePattern_of_leafType (U : HonestSource S) (P : Params S)
    (t : U.Node) (ht : t.1 = 0) :
    prePatternOf U P t ht = (leafTypeOf U P t ht).prePattern := by
  sorry

/-- Q11, V4 2.7: the actual leaf type retains its native prototype. -/
theorem leafTypeOf_type (U : HonestSource S) (P : Params S)
    (t : U.Node) (ht : t.1 = 0) : (leafTypeOf U P t ht).prototype = t.2.val.ty := by
  dsimp [leafTypeOf, LeafType.prototype]
  have h := Classical.choose_spec (U.leafIndex_exists P t ht)
  have h1 := h.1
  dsimp [HonestSource.leafIndex]
  have eq := congrArg FramedNode.ty h1
  dsimp [FramedNode.move] at eq
  exact eq

/-- Q11, V4 2.7 (S-table): every honest table obeys the deterministic child equation.
The role-word constructors are the original typed `S.RoleWord` constructors. -/
theorem certificate_child_equations (P : Params S) (D : Certificate P)
    (hD : D ∈ honestCerts S P) (a : ℕ) (ha : a + 1 ≤ P.K)
    (w : S.RoleWord D.ty a) (i : S.I (S.nativeTile D.ty a w).ty) :
    ∃ w' : S.RoleWord D.ty (a + 1),
      prototypeDescendantFrame D.ty (a + 1) w' =
        (rolePlacement (⟨(S.nativeTile D.ty a w).ty, i⟩ : S.Role)).trans
          (prototypeDescendantFrame D.ty a w) ∧
      D.table (a + 1) ha w' =
        childMap P (D.table a (by omega) w) ⟨(S.nativeTile D.ty a w).ty, i⟩ := by
  sorry

/-- Q8/Q9, V4 8.1: the downward word is recoverable from the reconstructed head's
upward address on the honest packet alphabet. It is not free auxiliary ancestry. -/
theorem packet_roles_from_head (P : Params S) (q : Packet P)
    (hq : q ∈ honestPackets S P) (j : Fin q.jstar.val) :
    q.roles j = q.head.address ⟨j.val, lt_trans j.isLt q.jstar.isLt⟩ := by
  sorry

/-- Q8, V4 8.1: the highest state is retained, and every higher slot is ABSENT. -/
theorem packet_top_spec (P : Params S) (q : Packet P) (hq : q ∈ honestPackets S P) :
    decode q q.jstar = some q.sstar ∧
      ∀ j : Fin P.k, q.jstar < j → decode q j = none := by
  sorry

/-- Q8/Q9, V4 8.1: decoding is injective on the honest compressed alphabet.
Together with `decode_spec` this is the lossless equivalence with Definition 2.5;
arbitrary raw tuples are not declared admissible. -/
theorem packet_encoding_injective (P : Params S) (q q' : Packet P)
    (hq : q ∈ honestPackets S P) (hq' : q' ∈ honestPackets S P)
    (hι : q.incidence = q'.incidence) (hslots : ∀ j, decode q j = decode q' j) : q = q' := by
  sorry

/-- Q10, V4 §2.4: every honest pre-pattern has an honest state and honest non-NULL
packets. The range is joint: this does not assert that arbitrary marginal choices occur. -/
theorem prePattern_components_honest (P : Params S) (w : PrePattern P)
    (hw : w ∈ honestPrePatterns S P) :
    w.state ∈ honestStates S P ∧
      ∀ f q, w.packets f = some q → q ∈ honestPackets S P := by
  sorry

/-- Q11, V4 2.7: each honest certificate component has its actual source meaning.
The certificate itself, not independent component membership, records their joint witness. -/
theorem certificate_components_honest (P : Params S) (D : Certificate P)
    (hD : D ∈ honestCerts S P) :
    (∀ w, D.leaves w ∈ honestPrePatterns S P) ∧
      ∀ a ha w, D.table a ha w ∈ honestStates S P := by
  sorry

/-- Q10, V4 §2.4 (frame marker): preserving every labelled marker ball fixes the
entire Euclidean frame, including its orientation. Reflections are allowed in the
isometry group; affine independence rules out every nonidentity stabilizer. -/
theorem frameMarker_rigid (P : Params S) (A : S.ι) (φ : Iso d)
    (hφ : ∀ a : Fin (d + 1),
      φ '' closedBall ((P.marker A).centre a) (P.marker A).radius =
        closedBall ((P.marker A).centre a) (P.marker A).radius) :
    φ = AffineIsometryEquiv.refl ℝ (E d) := by
  sorry

/-- Q11, V4 2.7: an actual source supplies certificates at the fixed certificate
height. No global nonemptiness of the species is imposed. -/
theorem honestCerts_nonempty (U : HonestSource S) (P : Params S) :
    (honestCerts S P).Nonempty := by
  obtain ⟨B, hB, _⟩ := U.hierarchy.cover P.K (0 : E d)
  exact ⟨certOf U P B hB, U, B, hB, rfl⟩

end Enforce
