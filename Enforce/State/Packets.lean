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

private def depthZeroFacet {A : S.ι} (ι : PrimitiveIncidence S) (h : ι.ty = A) :
    PrimitiveFacet S A := by
  subst h
  exact
    { depth := 0
      word := ()
      localCarrier := placedSet (S.child ι.ty ι.left).frame ι.leftFacet.val.carrier
      realization := ⟨ι.left, ι.leftFacet, rfl, ι.internal⟩ }

private lemma depthZeroFacet_depth {A : S.ι} (ι : PrimitiveIncidence S) (h : ι.ty = A) :
    (depthZeroFacet ι h).depth = 0 := by
  subst h; rfl

private theorem depthZeroFacet_image {A : S.ι} (P : Params S) (ι : P.Incidence)
    (h : ι.val.ty = A) (B : FramedNode S) (n : ℕ) :
    (B.prototypeFrame n) '' (depthZeroFacet ι.val h).carrier =
      P.incidencePlacement B n ι '' ι.val.leftFacet.val.carrier := by
  subst h
  dsimp [PrimitiveFacet.carrier, depthZeroFacet]
  dsimp [PrimitiveFacet.birthFrame, prototypeDescendantFrame, placedSet]
  simp only [Set.image_image]
  rfl

/-- Q8, V4 2.5: slot zero is PRESENT because all first-generation facets are required. -/
theorem mask_zero (U : HonestSource S) (P : Params S) (g : PrimitiveOccurrence U P) :
    mask U P g ⟨0, P.k_pos⟩ := by
  show P.InPrincipal g.birth.2.val g.birth.1 g.carrier
  let f := depthZeroFacet g.incidence.val g.parent_type
  have hreq : f ∈ P.required g.birth.2.val.ty := by
    rw [P.required_eq, mem_required_list]
    exact Or.inl (depthZeroFacet_depth _ _)
  exact ⟨f, P.required_mem _ f hreq, depthZeroFacet_image P g.incidence g.parent_type _ _⟩

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

open private honest_counter_jump_count_step3_word_frame from Enforce.State.State in
/-- Step 2 of the V4 proof of `packet_mask_fn` (V4 2.6(a)):
"the role word from each down to P_b" transports the normalized
birth carrier into the ancestor prototype. -/
private theorem packet_mask_fn_step2_geometry
    (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (j : Fin P.k)
    (K : Set (E d)) :
    (U.hierarchy.ancestor g.birth j.val).2.val.prototypeFrame
        (U.hierarchy.ancestor g.birth j.val).1 '' K = g.carrier ↔
      K = wordPlacement (slotRoles (stateOf U P g.birth) j) ''
        (S.σ.symm '' g.incidence.val.positioned) := by
  let A := (U.hierarchy.ancestor g.birth j.val).2.val.prototypeFrame
    (U.hierarchy.ancestor g.birth j.val).1
  let W := wordPlacement (slotRoles (stateOf U P g.birth) j)
  let T := ⇑W '' (⇑S.σ.symm '' g.incidence.val.positioned)
  have hw : slotRoles (stateOf U P g.birth) j =
      U.downRoles g.birth j.val := rfl
  have hf : g.birth.2.val.prototypeFrame g.birth.1 = W.trans A := by
    simpa only [← hw] using
      honest_counter_jump_count_step3_word_frame U g.birth j.val
  have hc : g.carrier = ⇑A '' T := by
    calc
      g.carrier = ⇑(g.birth.2.val.prototypeFrame g.birth.1) ''
          (⇑S.σ.symm '' g.incidence.val.positioned) := by
        ext y
        simp [PrimitiveOccurrence.carrier, Params.incidencePlacement,
          PrimitiveIncidence.positioned, placedSet]
      _ = ⇑A '' T := by
        rw [hf]
        simp only [T, Set.image_image, AffineEquiv.trans_apply]
  change ⇑A '' K = g.carrier ↔ K = T
  rw [hc]
  exact Set.image_eq_image A.injective

/-- Q9, V4 2.6(a): the geometric mask is a function of incidence and birth state. -/
theorem packet_mask_fn (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (j : Fin P.k) :
    mask U P g j ↔ packetMask P g.incidence (stateOf U P g.birth) j := by
  dsimp [mask, Params.InPrincipal, packetMask]
  have h_type : (U.hierarchy.ancestor g.birth j.val).2.val.ty = slotType (stateOf U P g.birth) j := by
    dsimp [slotType]
    split_ifs with hj
    · rw [hj]
      dsimp [stateOf]
      rfl
    · dsimp [stateOf, CoherentHierarchy.nodeRole]
      have h_anc : U.hierarchy.ancestor g.birth j.val = U.hierarchy.parentNode (U.hierarchy.ancestor g.birth (j.val - 1)) := by
        change (U.hierarchy.parentNode^[j.val]) g.birth = U.hierarchy.parentNode ((U.hierarchy.parentNode^[j.val - 1]) g.birth)
        have hj_pos : 0 < j.val := by omega
        have e : j.val = j.val - 1 + 1 := by omega
        nth_rw 1 [e]
        rw [Function.iterate_succ_apply']
      rw [h_anc]
      rfl
  revert h_type
  generalize hA1 : (U.hierarchy.ancestor g.birth j.val).2.val.ty = A1
  generalize hA2 : slotType (stateOf U P g.birth) j = A2
  intro h_type
  subst h_type
  have h_geom := packet_mask_fn_step2_geometry U P g j
  apply exists_congr
  intro f
  apply and_congr Iff.rfl
  exact h_geom f.carrier

private lemma childNode_parentNode (U : HonestSource S) (N : U.Node)
    (hq : 1 ≤ (U.hierarchy.parentNode N).1) :
    U.childNode (U.hierarchy.parentNode N) hq (U.hierarchy.role N.1 N.2) = N := by
  obtain ⟨n, N, hN⟩ := N
  exact Sigma.subtype_ext rfl (U.hierarchy.child_eq n ⟨N, hN⟩).symm

private lemma stateOf_childMap_step (U : HonestSource S) (P : Params S) (N : U.Node)
    (hq : 1 ≤ (U.hierarchy.parentNode N).1) :
    stateOf U P N = childMap P (stateOf U P (U.hierarchy.parentNode N))
      (U.hierarchy.nodeRole N) := by
  have hc := childMap_spec U P (U.hierarchy.parentNode N) hq (U.hierarchy.role N.1 N.2)
  exact (congrArg (stateOf U P) (childNode_parentNode U N hq)).symm.trans hc

private lemma descend_eq (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (a : ℕ) (ha : a ≤ (topSlot U P g).val) :
    (packetOf U P g).descend a =
      stateOf U P (U.hierarchy.ancestor g.birth ((topSlot U P g).val - a)) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    set J := (topSlot U P g).val
    have hlt : a < J := by omega
    have h_dif : a < (packetOf U P g).jstar.val := hlt
    rw [Packet.descend, dif_pos h_dif, ih (by omega)]
    set N := U.hierarchy.ancestor g.birth (J - (a + 1))
    have hidx : J - 1 - a = J - (a + 1) := by omega
    have hp : U.hierarchy.parentNode N = U.hierarchy.ancestor g.birth (J - a) := by
      have e : J - (a + 1) + 1 = J - a := by omega
      have hc : U.hierarchy.ancestor g.birth (J - a) = U.hierarchy.parentNode (U.hierarchy.ancestor g.birth (J - (a + 1))) := by
        rw [← e]
        change (U.hierarchy.parentNode^[J - (a + 1) + 1]) g.birth = _
        rw [Function.iterate_succ_apply']
        rfl
      exact hc.symm
    have hq : 1 ≤ (U.hierarchy.parentNode N).1 := Nat.le_add_left 1 N.1
    have hstep := stateOf_childMap_step U P N hq
    rw [hp] at hstep
    have hroles : (packetOf U P g).roles ⟨(packetOf U P g).jstar.val - 1 - a, by omega⟩ = U.hierarchy.nodeRole N := by
      dsimp [packetOf]
      have this : U.hierarchy.ancestor g.birth (J - 1 - a) = U.hierarchy.ancestor g.birth (J - (a + 1)) := by
        have h_idx_eq : J - 1 - a = J - (a + 1) := hidx
        rw [h_idx_eq]
      rw [this]
    rw [hroles]
    exact hstep.symm

/-- Q8/Q9, V4 8.1: descent reconstructs even the intermediate ABSENT states. -/
theorem reconstructed_spec (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (j : Fin P.k) (hj : j ≤ topSlot U P g) :
    (packetOf U P g).reconstructed j = stateOf U P (U.hierarchy.ancestor g.birth j.val) := by
  show (packetOf U P g).descend ((packetOf U P g).jstar.val - j.val) = _
  have hjstar : (packetOf U P g).jstar.val = (topSlot U P g).val := rfl
  rw [hjstar]
  have h := descend_eq U P g ((topSlot U P g).val - j.val) (Nat.sub_le _ _)
  have hj' : j.val ≤ (topSlot U P g).val := hj
  have e : (topSlot U P g).val - ((topSlot U P g).val - j.val) = j.val :=
    Nat.sub_sub_self hj'
  rw [e] at h
  exact h

/-- Q8/Q9, V4 8.1: lossless decoding, with precisely the geometric mask.
This replaces a separate D-path invariant: it identifies every retained slot state. -/
theorem decode_spec (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (j : Fin P.k) :
    decode (packetOf U P g) j = (by
      classical
      exact if mask U P g j then
        some (stateOf U P (U.hierarchy.ancestor g.birth j.val)) else none) := by
  have hk : NeZero P.k := ⟨ne_of_gt P.k_pos⟩
  have h_packet_head : (packetOf U P g).head = stateOf U P g.birth := by
    have hh := reconstructed_spec U P g ⟨0, P.k_pos⟩ (Fin.zero_le _)
    have h2 : U.hierarchy.ancestor g.birth 0 = g.birth := rfl
    rw [h2] at hh
    exact hh
  have hm : Packet.mask (packetOf U P g) j ↔ mask U P g j := by
    dsimp [Packet.mask]
    rw [h_packet_head]
    exact (packet_mask_fn U P g j).symm
  have hj : mask U P g j → j ≤ topSlot U P g := by
    classical
    intro h
    have hmem : j ∈ presentSlots U P g := Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
    exact Finset.le_max' (presentSlots U P g) j hmem
  by_cases hm2 : mask U P g j
  · have h1 : j.val ≤ (packetOf U P g).jstar.val := hj hm2
    have h2 : (packetOf U P g).mask j := hm.mpr hm2
    change (by classical exact if h : j.val ≤ (packetOf U P g).jstar.val ∧ (packetOf U P g).mask j then some ((packetOf U P g).reconstructed j) else none) = _
    have h_decide : j.val ≤ (packetOf U P g).jstar.val ∧ (packetOf U P g).mask j := ⟨h1, h2⟩
    rw [dif_pos h_decide]
    change _ = (by classical exact if h : mask U P g j then some (stateOf U P (U.hierarchy.ancestor g.birth j.val)) else none)
    rw [dif_pos hm2]
    congr 1
    exact reconstructed_spec U P g j h1
  · have h_not_decide : ¬ (j.val ≤ (packetOf U P g).jstar.val ∧ (packetOf U P g).mask j) := by
      intro h
      apply hm2
      exact hm.mp h.2
    change (by classical exact if h : j.val ≤ (packetOf U P g).jstar.val ∧ (packetOf U P g).mask j then some ((packetOf U P g).reconstructed j) else none) = _
    rw [dif_neg h_not_decide]
    change none = (by classical exact if h : mask U P g j then some (stateOf U P (U.hierarchy.ancestor g.birth j.val)) else none)
    rw [dif_neg hm2]

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
private theorem packets_finite_step1_subset (S : SubstSystem d) (P : Params S) :
    honestPackets S P ⊆ ⋃ (g : P.Incidence), ⋃ (jstar : Fin P.k), ⋃ (sstar : State P) (_ : sstar ∈ honestStates S P), ⋃ (roles : Fin jstar.val → S.Role), {Packet.mk g jstar sstar roles} := by
  rintro q ⟨U, g, rfl⟩
  simp only [mem_iUnion, mem_singleton_iff]
  exact ⟨g.incidence, topSlot U P g, stateOf U P (U.hierarchy.ancestor g.birth (topSlot U P g).val), ⟨U, U.hierarchy.ancestor g.birth (topSlot U P g).val, rfl⟩, fun j => U.hierarchy.nodeRole (U.hierarchy.ancestor g.birth j.val), rfl⟩

theorem packets_finite (S : SubstSystem d) (P : Params S) :
    (honestPackets S P).Finite := by
  apply (Set.Finite.subset (s := ⋃ (g : P.Incidence), ⋃ (jstar : Fin P.k), ⋃ (sstar : State P) (_ : sstar ∈ honestStates S P), ⋃ (roles : Fin jstar.val → S.Role), {Packet.mk g jstar sstar roles}) ?_ (packets_finite_step1_subset S P))
  apply finite_iUnion; intro g
  apply finite_iUnion; intro jstar
  apply (states_finite S P).biUnion; intro sstar _
  apply finite_iUnion; intro roles
  exact finite_singleton _

namespace HonestSource

variable (U : HonestSource S)

/-- Q8/Q9, V4 2.5--2.6: a finite provider determines an actual primitive occurrence.
These properties follow from the existing provider incidence and birth-height API. -/
theorem providerOccurrence_data (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f) :
    1 ≤ (U.hierarchy.birthParent q f hf).1 ∧
      (U.recordIncidence P q f hf).val.ty = (U.hierarchy.birthParent q f hf).2.val.ty := by
  constructor
  · dsimp [CoherentHierarchy.birthParent, CoherentHierarchy.parentNode]
    omega
  · have h1 : (U.recordIncidence P q f hf).val.ty = (U.hierarchy.providerIncidence q f hf).ty :=
      (P.canonical_spec (U.hierarchy.providerIncidence q f hf)).1.symm
    have h2 : (U.hierarchy.providerIncidence q f hf).ty = (U.hierarchy.birthParent q f hf).2.val.ty :=
      (U.hierarchy.providerIncidence_spec q f hf).1
    exact Eq.trans h1 h2

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

open private exists_honest_step7_child_subset exists_honest_step7_tile_regular exists_honest_step7_zero_carrier from Enforce.Tiling in
private theorem packet_attached_step1_owner_step1_anc_subset (U : HonestSource S) (q : U.Node) (r : ℕ) : 
  q.2.val.carrier q.1 ⊆ (U.hierarchy.ancestor q r).2.val.carrier (U.hierarchy.ancestor q r).1 := by
  induction' r with r ih generalizing q
  · exact Subset.rfl
  · have ih' := ih (U.hierarchy.parentNode q)
    change q.2.val.carrier q.1 ⊆ (U.hierarchy.parentNode^[r] (U.hierarchy.parentNode q)).2.val.carrier _
    have h1 : q.2.val.carrier q.1 ⊆ (U.hierarchy.parentNode q).2.val.carrier (q.1 + 1) := by
      let P := U.hierarchy.parentNode q
      have H_child := U.hierarchy.child_eq q.1 q.2
      have h_q_eq : q.2.val = (P.2.val.child q.1 (U.hierarchy.role q.1 q.2)) := H_child
      rw [h_q_eq]
      exact exists_honest_step7_child_subset P.2.val q.1 _
    have h2 : (U.hierarchy.parentNode q).2.val.carrier (U.hierarchy.parentNode q).1 ⊆ (U.hierarchy.ancestor (U.hierarchy.parentNode q) r).2.val.carrier (U.hierarchy.ancestor (U.hierarchy.parentNode q) r).1 := by
      exact ih (U.hierarchy.parentNode q)
    have hp_height : (U.hierarchy.parentNode q).1 = q.1 + 1 := rfl
    have h2_rw : (U.hierarchy.parentNode q).2.val.carrier (q.1 + 1) ⊆ (U.hierarchy.ancestor (U.hierarchy.parentNode q) r).2.val.carrier (U.hierarchy.ancestor (U.hierarchy.parentNode q) r).1 := by
      exact hp_height ▸ h2
    exact h1.trans h2_rw

omit [Fact (2 ≤ d)] in
/-- Step 4 of the V4 proof of `packet_attached` (V4 1.6, used in 2.6(c)): relative
interiors commute with invertible affine maps. -/
private theorem packet_attached_step1_owner_hint_step1_relint_image
    (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
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

/-- Step 4 of the V4 proof of `packet_attached` (V4 1.6): the positioned primitive
facet is the placed side-independent positioned facet of its incidence. -/
private theorem packet_attached_step1_owner_hint_step2_carrier_eq (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) :
    g.carrier = g.birth.2.val.prototypeFrame g.birth.1 ''
      (S.σ.symm '' g.incidence.val.positioned) := by
  ext y
  simp [PrimitiveOccurrence.carrier, Params.incidencePlacement,
    PrimitiveIncidence.positioned, placedSet]

private theorem packet_attached_step1_owner_hint (U : HonestSource S) (P : Params S) (g : PrimitiveOccurrence U P) : relint g.carrier ⊆ interior (g.birth.2.val.carrier g.birth.1) := by
  let G : E d ≃ᵃ[ℝ] E d :=
    S.σ.symm.toAffineEquiv.trans (g.birth.2.val.prototypeFrame g.birth.1)
  have hg : g.carrier = G '' g.incidence.val.positioned := by
    rw [packet_attached_step1_owner_hint_step2_carrier_eq U P g, Set.image_image]
    rfl
  have hB : g.birth.2.val.carrier g.birth.1 = G '' S.supertile 1 g.incidence.val.ty := by
    rw [g.parent_type]
    ext y
    simp [G, FramedNode.carrier, FramedNode.prototypeFrame, placedSet,
      SubstSystem.supertile]
  rw [hg, hB, packet_attached_step1_owner_hint_step1_relint_image]
  let H := G.toHomeomorphOfFiniteDimensional
  change H '' relint _ ⊆ interior (H '' _)
  rw [← H.image_interior]
  exact Set.image_mono g.incidence.val.internal

omit [Fact (2 ≤ d)] in
/-- Step 1 of the V4 proof of `packet_attached_step1_owner_hxc` (V4 1.0 (H2), used in
2.6(c)): invertible affine maps preserve the dimension of the affine hull. -/
private theorem packet_attached_step1_owner_hxc_step1_finrank_image
    (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
    Module.finrank ℝ (affineSpan ℝ (e '' K)).direction =
      Module.finrank ℝ (affineSpan ℝ K).direction := by
  have h' : affineSpan ℝ (e '' K) = (affineSpan ℝ K).map e.toAffineMap :=
    (AffineSubspace.map_span e.toAffineMap K).symm
  rw [h', AffineSubspace.map_direction]
  exact LinearEquiv.finrank_map_eq e.linear _

omit [Fact (2 ≤ d)] in
/-- Step 2 of the V4 proof of `packet_attached_step1_owner_hxc` (V4 1.0 (H2), used in
2.6(c)): a placed cell inside a placed cell of the same dimension has the same affine
hull, so its (nonempty) relative interior lies in the relative interior of the larger. -/
private theorem packet_attached_step1_owner_hxc_step2_meets
    (e₁ e₂ : E d ≃ᵃ[ℝ] E d) (c₁ c₂ : Cell d)
    (hdim : c₁.dim = c₂.dim) (hsub : e₁ '' c₁.carrier ⊆ e₂ '' c₂.carrier) :
    ∃ x ∈ e₁ '' c₁.carrier, x ∈ relint (e₂ '' c₂.carrier) := by
  obtain ⟨y, hy⟩ := c₁.flat.relint_nonempty
  have hyK : y ∈ c₁.carrier := intrinsicInterior_subset hy
  have hle : affineSpan ℝ (e₁ '' c₁.carrier) ≤ affineSpan ℝ (e₂ '' c₂.carrier) :=
    affineSpan_mono ℝ hsub
  have hfin : Module.finrank ℝ (affineSpan ℝ (e₁ '' c₁.carrier)).direction =
      Module.finrank ℝ (affineSpan ℝ (e₂ '' c₂.carrier)).direction := by
    rw [packet_attached_step1_owner_hxc_step1_finrank_image,
      packet_attached_step1_owner_hxc_step1_finrank_image]
    have h1 := c₁.flat.dimension
    have h2 := c₂.flat.dimension
    simp only [cellDirection] at h1 h2
    rw [h1, h2, hdim]
  have hdir : (affineSpan ℝ (e₁ '' c₁.carrier)).direction =
      (affineSpan ℝ (e₂ '' c₂.carrier)).direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) hfin
  have hspan : affineSpan ℝ (e₁ '' c₁.carrier) = affineSpan ℝ (e₂ '' c₂.carrier) := by
    apply AffineSubspace.ext_of_direction_eq hdir
    exact ⟨e₁ y, subset_affineSpan ℝ _ ⟨y, hyK, rfl⟩,
      subset_affineSpan ℝ _ (hsub ⟨y, hyK, rfl⟩)⟩
  have key : ∀ (V W : AffineSubspace ℝ (E d)), V = W → ∀ A B : Set (E d), A ⊆ B →
      (((↑) : V → E d) '' interior ((↑) ⁻¹' A : Set V) : Set (E d)) ⊆
        ((↑) : W → E d) '' interior ((↑) ⁻¹' B : Set W) := by
    rintro V W rfl A B hAB
    exact Set.image_mono (interior_mono (Set.preimage_mono hAB))
  have hrel : relint (e₁ '' c₁.carrier) ⊆ relint (e₂ '' c₂.carrier) :=
    key _ _ hspan _ _ hsub
  refine ⟨e₁ y, ⟨y, hyK, rfl⟩, hrel ?_⟩
  rw [packet_attached_step1_owner_hint_step1_relint_image]
  exact ⟨y, hy, rfl⟩

private theorem packet_attached_step1_owner_hxc (U : HonestSource S) (P : Params S) (g : PrimitiveOccurrence U P) (t : U.Node) (f : FacetName S t.2.val.ty) (hfg : t.2.val.cell t.1 f.val ⊆ g.carrier) : ∃ x ∈ t.2.val.cell t.1 f.val, x ∈ relint g.carrier := by
  have hfdim : f.val.dim = d - 1 := (Finset.mem_filter.mp f.2).2
  have hgdim : g.incidence.val.leftFacet.val.dim = d - 1 :=
    (Finset.mem_filter.mp g.incidence.val.leftFacet.2).2
  exact packet_attached_step1_owner_hxc_step2_meets (t.2.val.prototypeFrame t.1)
    (P.incidencePlacement g.birth.2.val g.birth.1 g.incidence) f.val
    g.incidence.val.leftFacet.val (hfdim.trans hgdim.symm) hfg
open private hereditary_trace_step1_cell_frontier from Enforce.Source.Trace in
private theorem packet_attached_step1_owner_hfront (U : HonestSource S) (t : U.Node) (f : FacetName S t.2.val.ty) : ∀ x ∈ t.2.val.cell t.1 f.val, x ∈ frontier (t.2.val.carrier t.1) := by
  intro x hx
  have he : f.val ∈ (S.cx t.2.val.ty).cells := by
    have hf := f.property
    exact (Finset.mem_filter.mp hf).1
  exact hereditary_trace_step1_cell_frontier t.2.val t.1 f.val he hx


/-- Step 1 of the V4 proof of `packet_attached` (V4 2.6(c), via 1.0 native ownership):
"every native tile `t` with a facet piece `f_t ⊆ g`" lies in the birth parent of `g`:
since `relint g` is interior to the birth parent, the tile meets that interior and
is one of its native tiles, so its ancestor at the birth height is the birth parent. -/
private theorem packet_attached_step1_owner (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (t : U.Node) (ht : t.1 = 0)
    (f : FacetName S t.2.val.ty) (hfg : t.2.val.cell t.1 f.val ⊆ g.carrier) :
    U.hierarchy.ancestor t g.birth.1 = g.birth := by
  let a := U.hierarchy.ancestor t g.birth.1
  have ha : a.1 = g.birth.1 := by
    dsimp only [a]
    rw [U.hierarchy.ancestor_height, ht, Nat.zero_add]
  have hsub : t.2.val.carrier t.1 ⊆ a.2.val.carrier a.1 := by
    exact packet_attached_step1_owner_step1_anc_subset U t g.birth.1
  
  have hint := packet_attached_step1_owner_hint U P g
  have hxc := packet_attached_step1_owner_hxc U P g t f hfg
  have hxt_front := packet_attached_step1_owner_hfront U t f

  obtain ⟨x, hxc_x, hxg_x⟩ := hxc
  have hxt_front_x : x ∈ frontier (t.2.val.carrier t.1) := hxt_front x hxc_x
  
  have ht_closed : IsClosed (t.2.val.carrier t.1) := by
    have h_c_eq : t.2.val.carrier t.1 = (t.2.val.prototypeFrame t.1) '' (S.proto t.2.val.ty).carrier := by
      simp [FramedNode.carrier, FramedNode.prototypeFrame, placedSet, SubstSystem.supertile, Set.image_image]
    rw [h_c_eq]
    have h_c := (S.proto t.2.val.ty).compact
    exact (h_c.image ((t.2.val.prototypeFrame t.1).toHomeomorphOfFiniteDimensional).continuous).isClosed
  have hxt : x ∈ t.2.val.carrier t.1 := by
    have h_closure : x ∈ closure (t.2.val.carrier t.1) := frontier_subset_closure hxt_front_x
    rwa [IsClosed.closure_eq ht_closed] at h_closure

  have hx_interior_birth : x ∈ interior (g.birth.2.val.carrier g.birth.1) := hint hxg_x

  have ht_reg : closure (interior (t.2.val.carrier t.1)) = t.2.val.carrier t.1 := by
    have h_c_eq : t.2.val.carrier t.1 = (t.2.val.prototypeFrame t.1) '' (S.proto t.2.val.ty).carrier := by
      simp [FramedNode.carrier, FramedNode.prototypeFrame, placedSet, SubstSystem.supertile, Set.image_image]
    rw [h_c_eq]
    have h_r := (S.proto t.2.val.ty).regularClosed
    let f' := (t.2.val.prototypeFrame t.1).toHomeomorphOfFiniteDimensional
    change closure (interior (f' '' _)) = f' '' _
    rw [← f'.image_interior, ← f'.image_closure, h_r]
  
  have hx_closure_int_t : x ∈ closure (interior (t.2.val.carrier t.1)) := by
    rwa [ht_reg]
  
  have hz : (interior (g.birth.2.val.carrier g.birth.1) ∩ interior (t.2.val.carrier t.1)).Nonempty := 
    mem_closure_iff.mp hx_closure_int_t (interior (g.birth.2.val.carrier g.birth.1)) isOpen_interior hx_interior_birth

  obtain ⟨y, hy_birth, hy_t⟩ := hz
  have hya : y ∈ interior (a.2.val.carrier a.1) := interior_mono hsub hy_t
  
  have H_eq : ∀ n : ℕ, ∀ A B : FramedNode S, A ∈ U.hierarchy.nodes n → B ∈ U.hierarchy.nodes n → 
    (interior (A.carrier n) ∩ interior (B.carrier n)).Nonempty → A = B := by
    intro n A B hA hB ⟨z, hzA, hzB⟩
    exact U.hierarchy.same_height_disjoint n A B hA hB z hzA hzB
    
  have H_nodes_a : a.2.val ∈ U.hierarchy.nodes a.1 := a.2.property
  have hb_prop := g.birth.2.property
  have H_nodes_b : g.birth.2.val ∈ U.hierarchy.nodes a.1 := by
    rw [ha]
    exact hb_prop
  
  have ha_eq_b : a.2.val = g.birth.2.val := by
    have h_hy_birth_a : y ∈ interior (g.birth.2.val.carrier a.1) := by rwa [ha]
    exact H_eq a.1 a.2.val g.birth.2.val H_nodes_a H_nodes_b ⟨y, hya, h_hy_birth_a⟩
  
  have key : ∀ a b : U.Node, a.1 = b.1 → a.2.val = b.2.val → a = b := by
    rintro ⟨n, A, hA⟩ ⟨m, B, hB⟩ h1 h2
    dsimp only at h1 h2
    subst h1
    subst h2
    rfl
  exact key a g.birth ha ha_eq_b

open private hereditary_trace_step3_child_cell from Enforce.Source.Trace in
/-- Step 1 of the V4 proof of `packet_attached_step2_serving_facet` (V4 1.6):
the left facet named by an incidence is a whole facet of its placed child. -/
private theorem packet_attached_step2_serving_facet_step1_incidence_cell
    (B : FramedNode S) (n : ℕ) (ι : PrimitiveIncidence S) (hι : ι.ty = B.ty) :
    ∃ (i : S.I B.ty) (e : FacetName S (B.child n i).ty),
      (B.child n i).cell n e.val =
        B.prototypeFrame (n + 1) '' (S.σ.symm '' ι.positioned) := by
  obtain ⟨A, φ⟩ := B
  dsimp only at hι
  subst A
  refine ⟨ι.left, ι.leftFacet, ?_⟩
  rw [hereditary_trace_step3_child_cell]
  simp only [PrimitiveIncidence.positioned, Set.image_image]
  apply Set.image_congr
  intro y hy
  change φ ((S.σ ^ n) y) = φ ((S.σ ^ (n + 1)) (S.σ.symm y))
  rw [pow_succ, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]

open private hereditary_trace_step1_cell_subset hereditary_trace_step1_frontier_relint
  sibling_intersection_cells_step1_reg sibling_intersection_cells_step1_disjoint
  sibling_facet_eq_step0_finrank_image from Enforce.Source.Trace in
/-- Step 2 of the V4 proof of `packet_attached_step2_serving_facet` (V4 1.4(a)):
at a relative-interior point of a sibling facet, the containing child's minimal
cell is the same whole cell, and hence is itself a facet. -/
private theorem packet_attached_step2_serving_facet_step2_sibling_cell
    (B : FramedNode S) (n : ℕ) (i j : S.I B.ty)
    (f : FacetName S (B.child n i).ty) (x : E d)
    (hxf : x ∈ relint ((B.child n i).cell n f.val))
    (hxj : x ∈ (B.child n j).carrier n) :
    ∃ e : FacetName S (B.child n j).ty,
      (B.child n j).cell n e.val = (B.child n i).cell n f.val := by
  by_cases hji : j = i
  · subst j
    exact ⟨f, rfl⟩
  have hfc := (Finset.mem_filter.mp f.property).1
  have hfd := (Finset.mem_filter.mp f.property).2
  have hxi : x ∈ (B.child n i).carrier n :=
    hereditary_trace_step1_cell_subset (B.child n i) n f.val hfc
      (intrinsicInterior_subset hxf)
  obtain ⟨-, hri⟩ := sibling_intersection_cells_step1_reg (B.child n i) n
  obtain ⟨hcj, -⟩ := sibling_intersection_cells_step1_reg (B.child n j) n
  have hfront : x ∈ frontier ((B.child n j).carrier n) := by
    rw [hcj.frontier_eq]
    refine ⟨hxj, fun hxint => ?_⟩
    have hd := (sibling_intersection_cells_step1_disjoint B n j i hji).closure_right
      isOpen_interior
    rw [hri] at hd
    exact Set.disjoint_left.mp hd hxint hxi
  obtain ⟨e, he, hxe⟩ := hereditary_trace_step1_frontier_relint (B.child n j) n x hfront
  have heq : (B.child n i).cell n f.val = (B.child n j).cell n e :=
    sibling_minimalCell_eq B n i j (Ne.symm hji) x ⟨f.val, hfc⟩ ⟨e, he⟩ hxf hxe
  have hdim : f.val.dim = e.dim := by
    rw [← f.val.flat.dimension, ← e.flat.dimension,
      ← sibling_facet_eq_step0_finrank_image ((B.child n i).prototypeFrame n) f.val.carrier,
      ← sibling_facet_eq_step0_finrank_image ((B.child n j).prototypeFrame n) e.carrier]
    change Module.finrank ℝ (cellDirection ((B.child n i).cell n f.val)) =
      Module.finrank ℝ (cellDirection ((B.child n j).cell n e))
    rw [heq]
  exact ⟨⟨e, Finset.mem_filter.mpr ⟨he, by rw [← hdim, hfd]⟩⟩, heq.symm⟩

open private hereditary_trace_step1_cell_subset from Enforce.Source.Trace in
/-- Step 2 of the V4 proof of `packet_attached` (V4 2.6(c), sibling pairing of 1.6):
"on either side": the child of the birth parent containing the native tile is one of
the two paired children of the incidence, and the primitive facet `g` is a whole listed
facet of that child (its left facet name, or the paired right facet name). -/
private theorem packet_attached_step2_serving_facet (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (t : U.Node) (ht : t.1 = 0)
    (f : FacetName S t.2.val.ty) (hfg : t.2.val.cell t.1 f.val ⊆ g.carrier) :
    ∃ e : FacetName S (U.hierarchy.ancestor t (g.birth.1 - 1)).2.val.ty,
      (U.hierarchy.ancestor t (g.birth.1 - 1)).2.val.cell
        (U.hierarchy.ancestor t (g.birth.1 - 1)).1 e.val = g.carrier := by
  let n := g.birth.1 - 1
  let a := U.hierarchy.ancestor t n
  have hn : n + 1 = g.birth.1 := Nat.sub_add_cancel g.positive
  have ha : a.1 = n := by
    dsimp only [a]
    rw [U.hierarchy.ancestor_height, ht, Nat.zero_add]
  have hp : U.hierarchy.parentNode a = g.birth := by
    have hanc : U.hierarchy.ancestor t (n + 1) = U.hierarchy.parentNode a :=
      Function.iterate_succ_apply' _ _ _
    rw [← hanc, hn]
    exact packet_attached_step1_owner U P g t ht f hfg
  have hchild : ∃ j : S.I (U.hierarchy.parentNode a).2.val.ty,
      a.2.val = (U.hierarchy.parentNode a).2.val.child a.1 j :=
    ⟨U.hierarchy.role a.1 a.2, U.hierarchy.child_eq a.1 a.2⟩
  rw [hp] at hchild
  simp only [ha] at hchild
  obtain ⟨j, hj⟩ := hchild
  obtain ⟨i, e, he⟩ := packet_attached_step2_serving_facet_step1_incidence_cell
    g.birth.2.val n g.incidence.val g.parent_type
  have heg : (g.birth.2.val.child n i).cell n e.val = g.carrier := by
    rw [he, hn]
    exact (packet_attached_step1_owner_hint_step2_carrier_eq U P g).symm
  obtain ⟨x, hxf, hxg⟩ := packet_attached_step1_owner_hxc U P g t f hfg
  have hxa : x ∈ a.2.val.carrier a.1 :=
    packet_attached_step1_owner_step1_anc_subset U t n
      (hereditary_trace_step1_cell_subset t.2.val t.1 f.val
        (Finset.mem_filter.mp f.property).1 hxf)
  have hxj : x ∈ (g.birth.2.val.child n j).carrier n := by
    simpa only [ha, hj] using hxa
  have hxe : x ∈ relint ((g.birth.2.val.child n i).cell n e.val) := by
    rwa [heg]
  obtain ⟨e', he'⟩ := packet_attached_step2_serving_facet_step2_sibling_cell
    g.birth.2.val n i j e x hxe hxj
  change ∃ e : FacetName S a.2.val.ty, a.2.val.cell a.1 e.val = g.carrier
  have hfacet : ∃ e : FacetName S a.2.val.ty, a.2.val.cell n e.val = g.carrier := by
    rw [hj]
    exact ⟨e', he'.trans heg⟩
  simpa only [ha] using hfacet

omit [Fact (2 ≤ d)] in
/-- Step 4 of the V4 proof of `packet_attached` (V4 1.6, used in 2.6(c)): relative
interiors commute with invertible affine maps. -/
private theorem packet_attached_step4_relint_image
    (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
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

/-- Step 4 of the V4 proof of `packet_attached` (V4 1.6): the positioned primitive
facet is the placed side-independent positioned facet of its incidence. -/
private theorem packet_attached_step4_carrier_eq (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) :
    g.carrier = g.birth.2.val.prototypeFrame g.birth.1 ''
      (S.σ.symm '' g.incidence.val.positioned) := by
  ext y
  simp [PrimitiveOccurrence.carrier, Params.incidencePlacement,
    PrimitiveIncidence.positioned, placedSet]

/-- Step 4 of the V4 proof of `packet_attached` (V4 1.6, internality of the
primitive incidence): `relint g` lies in the interior of its birth parent. -/
private theorem packet_attached_step4_internal (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) :
    relint g.carrier ⊆ interior (g.birth.2.val.carrier g.birth.1) := by
  let G : E d ≃ᵃ[ℝ] E d :=
    S.σ.symm.toAffineEquiv.trans (g.birth.2.val.prototypeFrame g.birth.1)
  have hg : g.carrier = G '' g.incidence.val.positioned := by
    rw [packet_attached_step4_carrier_eq U P g, Set.image_image]
    rfl
  have hB : g.birth.2.val.carrier g.birth.1 = G '' S.supertile 1 g.incidence.val.ty := by
    rw [g.parent_type]
    ext y
    simp [G, FramedNode.carrier, FramedNode.prototypeFrame, placedSet,
      SubstSystem.supertile]
  rw [hg, hB, packet_attached_step4_relint_image]
  let H := G.toHomeomorphOfFiniteDimensional
  change H '' relint _ ⊆ interior (H '' _)
  rw [← H.image_interior]
  exact Set.image_mono g.incidence.val.internal

/-- Step 5 of the V4 proof of `packet_attached` (V4 1.1, (H2)): a listed facet of a
placed node lies on the frontier of that node. -/
private theorem packet_attached_step5_cell_frontier (N : FramedNode S) (n : ℕ)
    (e : Cell d) (he : e ∈ (S.cx N.ty).cells) : N.cell n e ⊆ frontier (N.carrier n) := by
  have hsub : e.carrier ⊆ frontier (S.proto N.ty).carrier := by
    rw [← (S.cx N.ty).carriers_cover]
    exact Set.subset_iUnion₂_of_subset e he (Set.Subset.refl _)
  have hcarrier : N.carrier n = N.prototypeFrame n '' (S.proto N.ty).carrier := by
    simp [FramedNode.carrier, FramedNode.prototypeFrame, placedSet,
      SubstSystem.supertile, Set.image_image]
  rw [hcarrier]
  let H := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional
  change H '' e.carrier ⊆ frontier (H '' (S.proto N.ty).carrier)
  rw [← H.image_frontier]
  exact Set.image_mono hsub

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `packet_attached` (V4 1.6): affine images keep the
dimension of the affine span. -/
private theorem packet_attached_step3_finrank_image (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
    Module.finrank ℝ (affineSpan ℝ (e '' K)).direction =
      Module.finrank ℝ (affineSpan ℝ K).direction := by
  have h' : affineSpan ℝ (e '' K) = (affineSpan ℝ K).map e.toAffineMap :=
    (AffineSubspace.map_span e.toAffineMap K).symm
  rw [h', AffineSubspace.map_direction]
  exact LinearEquiv.finrank_map_eq e.linear _

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `packet_attached` (V4 2.6(c)): a placed cell inside a
placed cell of the same dimension meets the relative interior of the larger one. -/
private theorem packet_attached_step3_meets_geom (e₁ e₂ : E d ≃ᵃ[ℝ] E d) (c₁ c₂ : Cell d)
    (hdim : c₁.dim = c₂.dim) (hsub : e₁ '' c₁.carrier ⊆ e₂ '' c₂.carrier) :
    ∃ x ∈ e₁ '' c₁.carrier, x ∈ relint (e₂ '' c₂.carrier) := by
  obtain ⟨y, hy⟩ := c₁.flat.relint_nonempty
  have hyK : y ∈ c₁.carrier := intrinsicInterior_subset hy
  have hle : affineSpan ℝ (e₁ '' c₁.carrier) ≤ affineSpan ℝ (e₂ '' c₂.carrier) :=
    affineSpan_mono ℝ hsub
  have hfin : Module.finrank ℝ (affineSpan ℝ (e₁ '' c₁.carrier)).direction =
      Module.finrank ℝ (affineSpan ℝ (e₂ '' c₂.carrier)).direction := by
    rw [packet_attached_step3_finrank_image, packet_attached_step3_finrank_image]
    have h1 := c₁.flat.dimension
    have h2 := c₂.flat.dimension
    simp only [cellDirection] at h1 h2
    rw [h1, h2, hdim]
  have hdir : (affineSpan ℝ (e₁ '' c₁.carrier)).direction =
      (affineSpan ℝ (e₂ '' c₂.carrier)).direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle) hfin
  have hspan : affineSpan ℝ (e₁ '' c₁.carrier) = affineSpan ℝ (e₂ '' c₂.carrier) := by
    apply AffineSubspace.ext_of_direction_eq hdir
    refine ⟨e₁ y, subset_affineSpan ℝ _ ⟨y, hyK, rfl⟩,
      subset_affineSpan ℝ _ (hsub ⟨y, hyK, rfl⟩)⟩
  have key : ∀ (V W : AffineSubspace ℝ (E d)), V = W → ∀ A B : Set (E d), A ⊆ B →
      (((↑) : V → E d) '' interior ((↑) ⁻¹' A : Set V) : Set (E d)) ⊆
        ((↑) : W → E d) '' interior ((↑) ⁻¹' B : Set W) := by
    rintro V W rfl A B hAB
    exact Set.image_mono (interior_mono (Set.preimage_mono hAB))
  have hrel : relint (e₁ '' c₁.carrier) ⊆ relint (e₂ '' c₂.carrier) :=
    key _ _ hspan _ _ hsub
  refine ⟨e₁ y, ⟨y, hyK, rfl⟩, hrel ?_⟩
  rw [packet_attached_step4_relint_image]
  exact ⟨y, hy, rfl⟩

/-- Step 3 of the V4 proof of `packet_attached` (V4 2.6(c)): "a native facet piece
`f_t ⊆ g`" is a full-dimensional piece of the flat facet `g`, so it meets `relint g`. -/
private theorem packet_attached_step3_meets_relint (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (t : U.Node)
    (f : FacetName S t.2.val.ty) (hfg : t.2.val.cell t.1 f.val ⊆ g.carrier) :
    ∃ x ∈ t.2.val.cell t.1 f.val, x ∈ relint g.carrier := by
  have hfdim : f.val.dim = d - 1 := (Finset.mem_filter.mp f.2).2
  have hgdim : g.incidence.val.leftFacet.val.dim = d - 1 :=
    (Finset.mem_filter.mp g.incidence.val.leftFacet.2).2
  exact packet_attached_step3_meets_geom (t.2.val.prototypeFrame t.1)
    (P.incidencePlacement g.birth.2.val g.birth.1 g.incidence) f.val
    g.incidence.val.leftFacet.val (hfdim.trans hgdim.symm) hfg

/-- Step 6 of the V4 proof of `packet_attached` (V4 2.6(c), side-independent
incidence): once the provider has the birth parent and the carrier of `g`, its
canonical incidence is the incidence of `g`. -/
private theorem packet_attached_step6_record_incidence (U : HonestSource S)
    (P : Params S) (g : PrimitiveOccurrence U P) (t : U.Node)
    (f : FacetName S t.2.val.ty) (hf : ¬ U.hierarchy.IsFault t f)
    (hbirth : U.hierarchy.birthParent t f hf = g.birth)
    (hcarrier : U.hierarchy.providerCarrier t f hf = g.carrier) :
    U.recordIncidence P t f hf = g.incidence := by
  obtain ⟨hty, -, -, hpc⟩ := U.hierarchy.providerIncidence_spec t f hf
  apply P.canonical_unique
  refine ⟨?_, ?_⟩
  · rw [hty, hbirth]
    exact g.parent_type.symm
  · unfold CoherentHierarchy.birthHeight at hpc
    rw [hbirth, hcarrier, packet_attached_step4_carrier_eq U P g] at hpc
    have h1 := (g.birth.2.val.prototypeFrame g.birth.1).injective.image_injective hpc
    have h2 := S.σ.symm.injective.image_injective h1
    exact h2.symm

/-- Step 7 of the V4 proof of `packet_attached` (V4 2.5): a primitive occurrence is
determined by its birth node and its incidence. -/
private theorem packet_attached_step7_occurrence_ext (U : HonestSource S) (P : Params S)
    (g₁ g₂ : PrimitiveOccurrence U P) (h1 : g₁.birth = g₂.birth)
    (h2 : g₁.incidence = g₂.incidence) : g₁ = g₂ := by
  obtain ⟨b₁, p₁, i₁, t₁⟩ := g₁
  obtain ⟨b₂, p₂, i₂, t₂⟩ := g₂
  dsimp only at h1 h2
  subst h1
  subst h2
  rfl

/-- Q9, V4 2.6(c): every native facet piece on either side of a primitive facet
has its canonical incidence and carries that primitive facet's single packet. -/
theorem packet_attached (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (t : U.Node) (ht : t.1 = 0)
    (f : FacetName S t.2.val.ty) (hfg : t.2.val.cell t.1 f.val ⊆ g.carrier) :
    (∃ hf : ¬ U.hierarchy.IsFault t f,
      (U.recordOf P t f hf).incidence = g.incidence) ∧
      U.facetPacket P t f = some (packetOf U P g) := by
  classical
  have hpos := g.positive
  have hown := packet_attached_step1_owner U P g t ht f hfg
  obtain ⟨e, he⟩ := packet_attached_step2_serving_facet U P g t ht f hfg
  have hint := packet_attached_step4_internal U P g
  obtain ⟨x, hxc, hxg⟩ := packet_attached_step3_meets_relint U P g t f hfg
  have hsucc : g.birth.1 - 1 + 1 = g.birth.1 := Nat.sub_add_cancel hpos
  have hnot : g.birth.1 ∉ U.hierarchy.boundaryOffsets t f := by
    intro hmem
    have hmem' : t.2.val.cell t.1 f.val ⊆
        frontier ((U.hierarchy.ancestor t g.birth.1).2.val.carrier
          (U.hierarchy.ancestor t g.birth.1).1) := hmem
    rw [hown] at hmem'
    exact (hmem' hxc).2 (hint hxg)
  have hf : ¬ U.hierarchy.IsFault t f := fun hfault => hnot (hfault _)
  have hprev : g.birth.1 - 1 ∈ U.hierarchy.boundaryOffsets t f := by
    have hfr := packet_attached_step5_cell_frontier
      (U.hierarchy.ancestor t (g.birth.1 - 1)).2.val
      (U.hierarchy.ancestor t (g.birth.1 - 1)).1 e.val
      (Finset.mem_filter.mp e.2).1
    rw [he] at hfr
    exact hfg.trans hfr
  have hoff : U.hierarchy.boundaryOffsets t f = {r | r < g.birth.1 - 1 + 1} := by
    rcases U.hierarchy.boundaryOffsets_initial t f with ⟨b, _, hb⟩ | hfault
    · rw [hb] at hnot hprev
      simp only [Set.mem_setOf_eq, not_lt] at hnot hprev
      have hbh : b = g.birth.1 - 1 + 1 := by omega
      rw [hb, hbh]
    · exact absurd hfault hf
  have hprov : U.hierarchy.IsProvider t f ⟨g.birth.1 - 1, e⟩ := by
    refine ⟨hoff, ?_, ?_⟩
    · show t.2.val.cell t.1 f.val ⊆ (U.hierarchy.ancestor t (g.birth.1 - 1)).2.val.cell
        (U.hierarchy.ancestor t (g.birth.1 - 1)).1 e.val
      rw [he]
      exact hfg
    · show relint ((U.hierarchy.ancestor t (g.birth.1 - 1)).2.val.cell
          (U.hierarchy.ancestor t (g.birth.1 - 1)).1 e.val) ⊆
        interior ((U.hierarchy.ancestor t (g.birth.1 - 1 + 1)).2.val.carrier
          (U.hierarchy.ancestor t (g.birth.1 - 1 + 1)).1)
      rw [he, hsucc, hown]
      exact hint
  have hfirst : U.hierarchy.firstProvider t f hf = ⟨g.birth.1 - 1, e⟩ :=
    U.hierarchy.provider_unique t f _ _ (U.hierarchy.firstProvider_spec t f hf) hprov
  have hanc : U.hierarchy.ancestor t (g.birth.1 - 1 + 1) =
      U.hierarchy.parentNode (U.hierarchy.ancestor t (g.birth.1 - 1)) :=
    Function.iterate_succ_apply' _ _ _
  have hbirth : U.hierarchy.birthParent t f hf = g.birth := by
    unfold CoherentHierarchy.birthParent CoherentHierarchy.servingChild
    rw [hfirst]
    show U.hierarchy.parentNode (U.hierarchy.ancestor t (g.birth.1 - 1)) = g.birth
    rw [← hanc, hsucc, hown]
  have hcarrier : U.hierarchy.providerCarrier t f hf = g.carrier := by
    unfold CoherentHierarchy.providerCarrier CoherentHierarchy.servingChild
    rw [hfirst]
    exact he
  have hinc := packet_attached_step6_record_incidence U P g t f hf hbirth hcarrier
  have hocc : U.providerOccurrence P t f hf = g :=
    packet_attached_step7_occurrence_ext U P _ _ hbirth hinc
  refine ⟨⟨hf, hinc⟩, ?_⟩
  unfold HonestSource.facetPacket
  rw [dif_neg hf, hocc]


/-- Step 1 of the V4 proof of `packet_inherited` (V4 2.6(d)): faults restrict to faults and non-faults to non-faults along inherited facet tracks. -/
private theorem packet_inherited_step1_fault (U : HonestSource S) (P : Params S) (q c : U.Node)
    (a : ℕ) (hca : U.hierarchy.ancestor c a = q)
    (f : FacetName S q.2.val.ty) (g : FacetName S c.2.val.ty)
    (hgf : c.2.val.cell c.1 g.val ⊆ q.2.val.cell q.1 f.val) :
    U.hierarchy.IsFault q f ↔ U.hierarchy.IsFault c g := by
  have hanc (s : ℕ) : U.hierarchy.ancestor c (a + s) = U.hierarchy.ancestor q s := by
    rw [← hca]
    dsimp [CoherentHierarchy.ancestor]
    rw [← Function.iterate_add_apply, Nat.add_comm s a]
  constructor
  · intro hq
    have hshift (s : ℕ) : a + s ∈ U.hierarchy.boundaryOffsets c g := by
      change c.2.val.cell c.1 g.val ⊆ frontier
        ((U.hierarchy.ancestor c (a + s)).2.val.carrier (U.hierarchy.ancestor c (a + s)).1)
      rw [hanc]
      exact hgf.trans (hq s)
    rcases U.hierarchy.boundaryOffsets_initial c g with ⟨b, _, hb⟩ | hc
    · have hmem := hshift b
      rw [hb] at hmem
      exact absurd hmem (by simp)
    · exact hc
  · intro hc
    by_contra hq
    obtain ⟨hg, -⟩ := U.hierarchy.provider_inherited q c a hca f g hq hgf
    exact hg hc

/-- Step 1 of the V4 proof of `packet_inherited_step2_occurrence`: by induction on a, the
provider carrier and birth parent of the inherited facet match those of the original facet. -/
private theorem packet_inherited_step2_occurrence_step1_induction (U : HonestSource S) (P : Params S) (q c : U.Node)
    (a : ℕ) (hca : U.hierarchy.ancestor c a = q)
    (f : FacetName S q.2.val.ty) (g : FacetName S c.2.val.ty)
    (hgf : c.2.val.cell c.1 g.val ⊆ q.2.val.cell q.1 f.val)
    (hq : ¬ U.hierarchy.IsFault q f) (hc : ¬ U.hierarchy.IsFault c g) :
    U.hierarchy.providerCarrier c g hc = U.hierarchy.providerCarrier q f hq ∧
    U.hierarchy.birthParent c g hc = U.hierarchy.birthParent q f hq := by
  obtain ⟨_, h1, h2⟩ := U.hierarchy.provider_inherited q c a hca f g hq hgf
  exact ⟨h1, h2⟩

/-- Step 2 of the V4 proof of `packet_inherited_step2_occurrence`: the carrier of the constructed
provider occurrence is equal to the hierarchy's provider carrier. -/
private theorem packet_inherited_step2_occurrence_step2_carrier (U : HonestSource S) (P : Params S) (q : U.Node)
    (f : FacetName S q.2.val.ty) (hq : ¬ U.hierarchy.IsFault q f) :
    (U.providerOccurrence P q f hq).carrier = U.hierarchy.providerCarrier q f hq := by
  dsimp [PrimitiveOccurrence.carrier]
  dsimp [HonestSource.providerOccurrence, Params.incidencePlacement]
  dsimp [HonestSource.recordIncidence]
  have hc := U.hierarchy.providerIncidence_spec q f hq
  have h1 : SameIncidence (U.hierarchy.providerIncidence q f hq) (P.canonical (U.hierarchy.providerIncidence q f hq)).val :=
    (P.canonical_spec (U.hierarchy.providerIncidence q f hq))
  have h2 := hc.2.2.2
  dsimp [SameIncidence] at h1
  have h3 : (P.canonical (U.hierarchy.providerIncidence q f hq)).val.positioned =
      (U.hierarchy.providerIncidence q f hq).positioned := h1.2.symm
  rw [h2]
  have h_b_eq : U.hierarchy.birthHeight q f hq = (U.hierarchy.birthParent q f hq).1 := rfl
  rw [h_b_eq]
  dsimp [PrimitiveIncidence.positioned, placedSet] at h3
  rw [Set.image_comp, Set.image_comp]
  congr 2

/-- Step 2 of the V4 proof of `packet_inherited` (V4 2.6(d)): the provider occurrence is unchanged along inherited facet tracks. -/
private theorem packet_inherited_step2_occurrence (U : HonestSource S) (P : Params S) (q c : U.Node)
    (a : ℕ) (hca : U.hierarchy.ancestor c a = q)
    (f : FacetName S q.2.val.ty) (g : FacetName S c.2.val.ty)
    (hgf : c.2.val.cell c.1 g.val ⊆ q.2.val.cell q.1 f.val)
    (hq : ¬ U.hierarchy.IsFault q f) (hc : ¬ U.hierarchy.IsFault c g) :
    U.providerOccurrence P c g hc = U.providerOccurrence P q f hq := by
  let G := U.providerOccurrence P q f hq
  obtain ⟨hcar, hbp⟩ := packet_inherited_step2_occurrence_step1_induction U P q c a hca f g hgf hq hc
  have hcar' : U.hierarchy.providerCarrier c g hc = G.carrier := by
    rw [hcar]
    exact (packet_inherited_step2_occurrence_step2_carrier U P q f hq).symm
  have hinc := packet_attached_step6_record_incidence U P G c g hc hbp hcar'
  exact packet_attached_step7_occurrence_ext U P _ _ hbp hinc
/-- Q9, V4 2.6(d): packets restrict unchanged along inherited facet tracks. -/
theorem packet_inherited (U : HonestSource S) (P : Params S) (q c : U.Node)
    (a : ℕ) (hca : U.hierarchy.ancestor c a = q)
    (f : FacetName S q.2.val.ty) (g : FacetName S c.2.val.ty)
    (hgf : c.2.val.cell c.1 g.val ⊆ q.2.val.cell q.1 f.val) :
    U.facetPacket P c g = U.facetPacket P q f := by
  unfold HonestSource.facetPacket
  by_cases hq : U.hierarchy.IsFault q f
  · have hc : U.hierarchy.IsFault c g := (packet_inherited_step1_fault U P q c a hca f g hgf).mp hq
    rw [dif_pos hq, dif_pos hc]
  · have hc : ¬ U.hierarchy.IsFault c g := mt (packet_inherited_step1_fault U P q c a hca f g hgf).mpr hq
    rw [dif_neg hq, dif_neg hc]
    congr 2
    exact packet_inherited_step2_occurrence U P q c a hca f g hgf hq hc

/-- Q8/Q9, V4 2.5, 8.1: every honest non-NULL packet has a PRESENT head and
its top index is exactly the maximum reconstructed mask index. -/
theorem honest_packet_admissible (P : Params S) (q : Packet P)
    (hq : q ∈ honestPackets S P) :
    decode q ⟨0, P.k_pos⟩ = some q.head ∧ q.head.ty = q.incidence.val.ty ∧
      q.mask q.jstar ∧ (∀ j, q.mask j → j ≤ q.jstar) ∧
      ∀ j s, decode q j = some s → s ∈ honestStates S P := by
  obtain ⟨U, g, rfl⟩ := hq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · classical
    have h_mask := mask_zero U P g
    have h_dec := decode_spec U P g ⟨0, P.k_pos⟩
    have h_head := packet_head U P g
    have h_pos : (if mask U P g ⟨0, P.k_pos⟩ then
        some (stateOf U P (U.hierarchy.ancestor g.birth 0)) else none) =
        some (stateOf U P g.birth) := by
      rw [if_pos h_mask]
      rfl
    rw [h_pos] at h_dec
    rw [h_dec, h_head]
  · have h_head := packet_head U P g
    rw [h_head]
    dsimp [stateOf]
    have h_pt := g.parent_type
    exact h_pt.symm
  · classical
    have hm : mask U P g (topSlot U P g) := by
      have h_max := Finset.max'_mem _ (presentSlots_nonempty U P g)
      exact (Finset.mem_filter.mp h_max).2
    change packetMask P g.incidence (packetOf U P g).head (topSlot U P g)
    rw [packet_head U P g]
    rw [← packet_mask_fn U P g (topSlot U P g)]
    exact hm
  · classical
    intro j hj
    have hm : mask U P g j := by
      rw [packet_mask_fn U P g j]
      change packetMask P g.incidence (packetOf U P g).head j at hj
      rw [packet_head U P g] at hj
      exact hj
    have h_mem : j ∈ presentSlots U P g := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
    exact Finset.le_max' _ _ h_mem
  · intro j s hs
    have h_dec := decode_spec U P g j
    revert hs
    split at h_dec
    · rw [h_dec]
      intro hs
      injection hs with hs'
      rw [← hs']
      exact ⟨U, _, rfl⟩
    · rw [h_dec]
      intro hs
      contradiction

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
private def prePattern_inj (S : SubstSystem d) (P : Params S) (w : PrePattern P) :
    Sigma (fun ty : S.ι => State P × (FacetName S ty → Option (Packet P))) :=
  ⟨w.ty, w.state, w.packets⟩

private theorem prePattern_inj_injective (S : SubstSystem d) (P : Params S) :
    Function.Injective (prePattern_inj S P) := by
  rintro ⟨ty1, fm1, fmeq1, state1, state_type1, pkts1⟩ ⟨ty2, fm2, fmeq2, state2, state_type2, pkts2⟩ h
  dsimp [prePattern_inj] at h
  have hty : ty1 = ty2 := congrArg Sigma.fst h
  subst hty
  have hrest : (state1, pkts1) = (state2, pkts2) := by
    exact eq_of_heq (Sigma.mk.inj h).2
  have hstate : state1 = state2 := congrArg Prod.fst hrest
  subst hstate
  have hpkts : pkts1 = pkts2 := congrArg Prod.snd hrest
  subst hpkts
  cases fmeq1
  cases fmeq2
  rfl

private theorem prePattern_state_mem (S : SubstSystem d) (P : Params S)
    {w : PrePattern P} (hw : w ∈ honestPrePatterns S P) :
    w.state ∈ honestStates S P := by
  obtain ⟨U, t, ht, rfl⟩ := hw
  exact stateOf_mem U P t

private theorem prePattern_packets_mem (S : SubstSystem d) (P : Params S)
    {w : PrePattern P} (hw : w ∈ honestPrePatterns S P) (f : FacetName S w.ty)
    (q : Packet P) (h : w.packets f = some q) :
    q ∈ honestPackets S P := by
  obtain ⟨U, t, ht, rfl⟩ := hw
  dsimp [prePatternOf, HonestSource.facetPacket] at h
  revert h
  split_ifs with hf
  · intro hc; cases hc
  · intro hc
    injection hc with hc
    subst hc
    exact ⟨U, _, rfl⟩

theorem prePatterns_finite (S : SubstSystem d) (P : Params S) :
    (honestPrePatterns S P).Finite := by
  classical
  have hst : (honestStates S P).Finite := states_finite S P
  have hpk : (honestPackets S P).Finite := packets_finite S P
  refine Set.Finite.of_finite_image (f := prePattern_inj S P) ?_ (prePattern_inj_injective S P).injOn
  have hB : (insert (none : Option (Packet P)) (some '' honestPackets S P)).Finite := (hpk.image _).insert _
  haveI : Fintype S.ι := S.types_finite
  refine Set.Finite.subset (Set.finite_iUnion (fun ty : S.ι => ((hst.prod (Set.Finite.pi (t := fun _ : FacetName S ty => _) (fun _ => hB))).image (Sigma.mk ty)))) ?_
  rintro _ ⟨w, hw, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_prod, Set.mem_pi, Set.mem_insert_iff]
  refine ⟨w.ty, ⟨w.state, w.packets⟩, ⟨prePattern_state_mem S P hw, ?_⟩, rfl⟩
  intro f _
  have h_eq : w.packets f = w.packets f := rfl
  rcases h : w.packets f with _ | q
  · left
    exact h
  · right
    refine ⟨q, prePattern_packets_mem S P hw f q h, ?_⟩
    exact h.symm

namespace HonestSource

variable (U : HonestSource S)

/-- Q11, V4 2.7: a standard descendant is an actual member of the honest hierarchy. -/
theorem descendant_mem (q : U.Node) (a : ℕ) (ha : a ≤ q.1) (w : S.RoleWord q.2.val.ty a) :
    (S.descendantNode q.2.val.ty (q.1 - a) a w).move q.2.val.frame ∈
      U.hierarchy.nodes (q.1 - a) := by
  induction' a with a ih generalizing q
  · have h0 : q.1 - 0 = q.1 := rfl
    have h1 : S.descendantNode q.2.val.ty (q.1 - 0) 0 w = ⟨q.2.val.ty, AffineIsometryEquiv.refl ℝ (E d)⟩ := rfl
    rw [h1]
    have h2 : (FramedNode.mk q.2.val.ty (AffineIsometryEquiv.refl ℝ (E d))).move q.2.val.frame = q.2.val := by
      rcases q.2.val with ⟨qty, qframe⟩
      rfl
    rw [h2, h0]
    exact q.2.property
  · have h_desc : S.descendantNode q.2.val.ty (q.1 - (a + 1)) (a + 1) w = (S.descendantNode (S.child q.2.val.ty w.1).ty (q.1 - (a + 1)) a w.2).move (S.placeChild (q.1 - (a + 1) + a) w.1) := rfl
    rw [h_desc]
    have h_move : ((S.descendantNode (S.child q.2.val.ty w.1).ty (q.1 - (a + 1)) a w.2).move (S.placeChild (q.1 - (a + 1) + a) w.1)).move q.2.val.frame = (S.descendantNode (S.child q.2.val.ty w.1).ty (q.1 - (a + 1)) a w.2).move ((S.placeChild (q.1 - (a + 1) + a) w.1).trans q.2.val.frame) := by
      rfl
    rw [h_move]
    have h_child_height : q.1 - (a + 1) + a = q.1 - 1 := by omega
    have h_frame : (S.placeChild (q.1 - (a + 1) + a) w.1).trans q.2.val.frame = (q.2.val.child (q.1 - 1) w.1).frame := by
      rw [h_child_height]
      rfl
    rw [h_frame]
    have h_child_ty : (S.child q.2.val.ty w.1).ty = (q.2.val.child (q.1 - 1) w.1).ty := rfl
    have h_q_mem : q.2.val ∈ U.hierarchy.nodes (q.1 - 1 + 1) := by
      have hh : q.1 - 1 + 1 = q.1 := by omega
      rw [hh]
      exact q.2.property
    have h_mem := U.hierarchy.children_mem (q.1 - 1) q.2.val h_q_mem w.1
    let q_child : U.Node := ⟨q.1 - 1, ⟨q.2.val.child (q.1 - 1) w.1, h_mem⟩⟩
    have h_q_child_height : q_child.1 = q.1 - 1 := rfl
    have h_child_ha : a ≤ q_child.1 := by
      rw [h_q_child_height]
      omega
    have h_height : q.1 - (a + 1) = q_child.1 - a := by
      rw [h_q_child_height]
      omega
    have ih_app := ih q_child h_child_ha (by rw [← h_child_ty]; exact w.2)
    have h_rw : (S.descendantNode (S.child q.2.val.ty w.1).ty (q.1 - (a + 1)) a w.2).move (q.2.val.child (q.1 - 1) w.1).frame = (S.descendantNode q_child.2.val.ty (q_child.1 - a) a (by rw [← h_child_ty]; exact w.2)).move q_child.2.val.frame := by
      dsimp [q_child]
      rw [h_height]
      congr
    rw [h_rw]
    rw [h_height]
    exact ih_app

/-- Q11, V4 2.7: the actual source node at an exact downward address. -/
def descendant (q : U.Node) (a : ℕ) (ha : a ≤ q.1) (w : S.RoleWord q.2.val.ty a) :
    U.Node :=
  ⟨q.1 - a, ⟨(S.descendantNode q.2.val.ty (q.1 - a) a w).move q.2.val.frame,
    U.descendant_mem q a ha w⟩⟩

/-- Q11, V4 2.7: descendant type is independent of its remaining height. -/
theorem descendant_type (q : U.Node) (a : ℕ) (ha : a ≤ q.1)
    (w : S.RoleWord q.2.val.ty a) :
    (U.descendant q a ha w).2.val.ty = (S.nativeTile q.2.val.ty a w).ty := by
  dsimp [HonestSource.descendant, FramedNode.move]
  have H : ∀ (A : S.ι) (rem : ℕ) (a : ℕ) (w : S.RoleWord A a), (S.descendantNode A rem a w).ty = (S.nativeTile A a w).ty := by
    intro A rem a
    induction' a with a ih generalizing A
    · intro _
      rfl
    · intro w
      dsimp [SubstSystem.RoleWord] at w
      dsimp [SubstSystem.descendantNode, SubstSystem.nativeTile]
      apply ih
  apply H

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


private def CertEncoding (P : Params S) :=
  Σ ty : S.ι,
    (S.RoleWord ty P.K → {w // w ∈ honestPrePatterns S P}) ×
    ((a : Fin (P.K + 1)) → (w : S.RoleWord ty a.val) → {s // s ∈ honestStates S P})

private def toCertEncoding (P : Params S)
    (C : Certificate P)
    (h_leaf : ∀ w, C.leaves w ∈ honestPrePatterns S P)
    (h_table : ∀ a ha w, C.table a ha w ∈ honestStates S P) : CertEncoding P :=
  ⟨C.ty, (fun w => ⟨C.leaves w, h_leaf w⟩), (fun a w => ⟨C.table a.val (Nat.le_of_lt_succ a.isLt) w, h_table a.val (Nat.le_of_lt_succ a.isLt) w⟩)⟩

private theorem toCertEncoding_injective (P : Params S) :
    ∀ C₁ C₂ (h_leaf₁ h_table₁ h_leaf₂ h_table₂),
      toCertEncoding P C₁ h_leaf₁ h_table₁ = toCertEncoding P C₂ h_leaf₂ h_table₂ → C₁ = C₂ := by
  rintro ⟨ty₁, leaves₁, ht1, table₁, htt1⟩ ⟨ty₂, leaves₂, ht2, table₂, htt2⟩ h_leaf₁ h_table₁ h_leaf₂ h_table₂ h
  injection h with h_ty h_rest
  subst h_ty
  have h_rest2 := eq_of_heq h_rest
  injection h_rest2 with h_leaves h_table
  congr 1
  · ext w
    apply congrArg Subtype.val (congrFun h_leaves w)
  · ext a ha w
    apply congrArg Subtype.val (congrFun (congrFun h_table ⟨a, by omega⟩) w)

/-- Q11, V4 2.7: the finite certificate catalogue. -/
theorem certs_finite (S : SubstSystem d) (P : Params S) :
    (honestCerts S P).Finite := by
  haveI h1 : Finite {w // w ∈ honestPrePatterns S P} := (prePatterns_finite S P).to_subtype
  haveI h2 : Finite {s // s ∈ honestStates S P} := (states_finite S P).to_subtype
  haveI : Fintype {w // w ∈ honestPrePatterns S P} := Fintype.ofFinite _
  haveI : Fintype {s // s ∈ honestStates S P} := Fintype.ofFinite _
  haveI (ty : S.ι) (a : Fin (P.K + 1)) : Fintype (S.RoleWord ty a.val) := S.roleWordFintype ty a.val
  haveI (ty : S.ι) : Fintype (S.RoleWord ty P.K) := S.roleWordFintype ty P.K
  haveI : Fintype S.ι := inferInstance
  haveI (ty : S.ι) (a : Fin (P.K + 1)) : DecidableEq (S.RoleWord ty a.val) := Classical.decEq _
  haveI (ty : S.ι) : DecidableEq (S.RoleWord ty P.K) := Classical.decEq _
  haveI (ty : S.ι) (a : Fin (P.K + 1)) : Fintype ((w : S.RoleWord ty a.val) → {s // s ∈ honestStates S P}) := Pi.instFintype
  haveI (ty : S.ι) : Fintype ((a : Fin (P.K + 1)) → (w : S.RoleWord ty a.val) → {s // s ∈ honestStates S P}) := Pi.instFintype
  haveI (ty : S.ι) : Fintype (S.RoleWord ty P.K → {w // w ∈ honestPrePatterns S P}) := Pi.instFintype
  haveI (ty : S.ι) : Fintype ((S.RoleWord ty P.K → {w // w ∈ honestPrePatterns S P}) × ((a : Fin (P.K + 1)) → (w : S.RoleWord ty a.val) → {s // s ∈ honestStates S P})) := inferInstance
  haveI : Fintype (CertEncoding P) := Sigma.instFintype
  apply Finite.of_injective (fun (⟨C, hC⟩ : {C // C ∈ honestCerts S P}) => toCertEncoding P C (by rintro w; obtain ⟨U, B, hB, rfl⟩ := hC; exact ⟨U, U.descendant ⟨P.K, ⟨B, hB⟩⟩ P.K le_rfl w, Nat.sub_self P.K, rfl⟩) (by rintro a ha w; obtain ⟨U, B, hB, rfl⟩ := hC; exact ⟨U, U.descendant ⟨P.K, ⟨B, hB⟩⟩ a ha w, rfl⟩))
  intro ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h
  exact Subtype.ext (toCertEncoding_injective P C₁ C₂ _ _ _ _ h)

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
  haveI : Finite {D // D ∈ honestCerts S P} := (certs_finite S P).to_subtype
  haveI (D : {D // D ∈ honestCerts S P}) : Finite (S.RoleWord D.val.ty P.K) :=
    S.roleWord_finite D.val.ty P.K
  infer_instance

namespace HonestSource

variable (U : HonestSource S)

/-- Q11, V4 2.7: the K-ancestor of a native tile really has height K. -/
theorem certificateAncestor_mem (P : Params S) (t : U.Node) (ht : t.1 = 0) :
    (U.hierarchy.ancestor t P.K).2.val ∈ U.hierarchy.nodes P.K := by
  have h := (U.hierarchy.ancestor t P.K).2.property
  have hh : (U.hierarchy.ancestor t P.K).1 = P.K := by
    rw [U.hierarchy.ancestor_height, ht, zero_add]
  simpa only [hh] using h

open private birth_ascent_routing_step2_descendant_injective from Enforce.Source.Routing in
/-- Q11, V4 2.7: the native tile has one exact role-word address below its K-ancestor.
Frames, rather than just carriers, are identified by the coherent hierarchy. -/
theorem leafIndex_exists (P : Params S) (t : U.Node) (ht : t.1 = 0) :
    ∃! w : S.RoleWord (U.hierarchy.ancestor t P.K).2.val.ty P.K,
      (S.nativeTile (U.hierarchy.ancestor t P.K).2.val.ty P.K w).move
        (U.hierarchy.ancestor t P.K).2.val.frame = t.2.val := by
  obtain ⟨r, hr, w, hw⟩ := U.hierarchy.ancestor_descendant t P.K
  have hK : r = P.K := by
    have hah := U.hierarchy.ancestor_height t P.K
    omega
  subst hK
  have hnat : S.descendantNode (U.hierarchy.ancestor t P.K).2.val.ty t.1 P.K w =
      S.nativeTile (U.hierarchy.ancestor t P.K).2.val.ty P.K w := by
    rw [ht]; rfl
  rw [hnat] at hw
  refine ⟨w, hw.symm, ?_⟩
  intro v hv
  have hmove : S.nativeTile (U.hierarchy.ancestor t P.K).2.val.ty P.K v =
      S.nativeTile (U.hierarchy.ancestor t P.K).2.val.ty P.K w := by
    have h := hv.trans hw
    have hty := congrArg FramedNode.ty h
    have hf := congrArg FramedNode.frame h
    apply FramedNode.ext
    · exact hty
    · refine AffineIsometryEquiv.ext fun x => ?_
      have hx := congrArg (fun φ : Iso d => φ x) hf
      exact (U.hierarchy.ancestor t P.K).2.val.frame.injective hx
  exact birth_ascent_routing_step2_descendant_injective _ 0 P.K hmove

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
  have node_ext : ∀ a b : U.Node, a.1 = b.1 → a.2.val = b.2.val → a = b := by
    rintro ⟨n, x, hx⟩ ⟨m, y, hy⟩ h1 h2
    dsimp only at h1 h2
    subst h1; subst h2; rfl
  have cong : ∀ (a b : U.Node) (hab : a = b) (ha : a.1 = 0) (hb : b.1 = 0),
      prePatternOf U P a ha = prePatternOf U P b hb := by
    intro a b hab ha hb; subst hab; rfl
  have h := (Classical.choose_spec (U.leafIndex_exists P t ht)).1
  show prePatternOf U P t ht =
    prePatternOf U P (U.descendant ⟨P.K, ⟨(U.hierarchy.ancestor t P.K).2.val,
      U.certificateAncestor_mem P t ht⟩⟩ P.K le_rfl (U.leafIndex P t ht)) (Nat.sub_self P.K)
  refine cong _ _ ?_ _ _
  symm
  apply node_ext
  · show P.K - P.K = t.1
    rw [ht]; exact Nat.sub_self P.K
  · change (S.descendantNode _ (P.K - P.K) P.K _).move _ = t.2.val
    have h_rw : (S.descendantNode _ (P.K - P.K) P.K (U.leafIndex P t ht)).move (U.hierarchy.ancestor t P.K).2.val.frame = (S.nativeTile _ P.K (U.leafIndex P t ht)).move (U.hierarchy.ancestor t P.K).2.val.frame := by
      have hh : ∀ m, m = 0 → ∀ A n (w : S.RoleWord A n), S.descendantNode A m n w = S.nativeTile A n w := by
        rintro m rfl A n w; rfl
      exact congrArg (fun (x : FramedNode S) => x.move (U.hierarchy.ancestor t P.K).2.val.frame) (hh (P.K - P.K) (Nat.sub_self P.K) (U.hierarchy.ancestor t P.K).2.val.ty P.K (U.leafIndex P t ht))
    dsimp only [HonestSource.leafIndex] at h_rw
    change (S.nativeTile _ P.K (Classical.choose (U.leafIndex_exists P t ht))).move _ = _ at h
    exact h_rw.trans h

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

/-- Q11, V4 2.7: append one child role to a typed role word. -/
private def certificate_child_equations_snoc : (A : S.ι) → (n : ℕ) → (w : S.RoleWord A n) →
    S.I (S.nativeTile A n w).ty → S.RoleWord A (n + 1)
  | _, 0, _, i => ⟨i, ()⟩
  | A, n + 1, w, i => ⟨w.1, certificate_child_equations_snoc (S.child A w.1).ty n w.2 i⟩

/-- Q11, V4 2.7: a child placed at height `n` conjugates its prescribed frame by `σ^n`. -/
private theorem certificate_child_equations_place_scaled (n : ℕ) {A : S.ι}
    (i : S.I A) (x : E d) :
    S.placeChild n i ((S.σ ^ n) x) = (S.σ ^ n) ((S.child A i).frame x) := by
  rw [S.placeChild_apply]
  simp [linearConj, Child.frame, rigidMotion, zpow_neg, LinearEquiv.mul_apply, map_add]

/-- Q11, V4 2.7: raising the base height by `h` conjugates the placement by `σ^h`. -/
private theorem certificate_child_equations_place_shift (h k : ℕ) {A : S.ι}
    (i : S.I A) (x : E d) :
    S.placeChild (h + k) i ((S.σ ^ h) x) = (S.σ ^ h) (S.placeChild k i x) := by
  have h₁ := certificate_child_equations_place_scaled (S := S) (h + k) i ((S.σ ^ k).symm x)
  have h₂ := certificate_child_equations_place_scaled (S := S) k i ((S.σ ^ k).symm x)
  simp only [pow_add, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply] at h₁ h₂
  rw [← h₂] at h₁
  exact h₁

/-- Q11, V4 2.7: a descendant at base height `h` is the native tile conjugated by `σ^h`. -/
private theorem certificate_child_equations_desc_scaled (A : S.ι) (h k : ℕ)
    (w : S.RoleWord A k) (x : E d) :
    (S.descendantNode A h k w).frame ((S.σ ^ h) x) =
      (S.σ ^ h) ((S.nativeTile A k w).frame x) := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih =>
    change S.placeChild (h + k) w.1
      ((S.descendantNode (S.child A w.1).ty h k w.2).frame ((S.σ ^ h) x)) =
      (S.σ ^ h) (S.placeChild (0 + k) w.1
        ((S.nativeTile (S.child A w.1).ty k w.2).frame x))
    rw [ih, certificate_child_equations_place_shift, Nat.zero_add]

/-- Q11, V4 2.7: the terminal type of a role word does not depend on the base height. -/
private theorem certificate_child_equations_desc_type (A : S.ι) (h k : ℕ)
    (w : S.RoleWord A k) : (S.descendantNode A h k w).ty = (S.nativeTile A k w).ty := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih => exact ih (S.child A w.1).ty w.2

/-- Q11, V4 2.7: moving a node commutes with taking a child. -/
private theorem certificate_child_equations_move_child (N : FramedNode S) (g : Iso d) (h : ℕ)
    (j : S.I N.ty) : (N.child h j).move g = (N.move g).child h j := by
  apply FramedNode.ext
  · rfl
  · apply AffineIsometryEquiv.ext
    intro x
    rfl

/-- Q11, V4 2.7: the appended word names the actual child of the descendant. -/
private theorem certificate_child_equations_desc_snoc (A : S.ι) (h n : ℕ)
    (w : S.RoleWord A n) (i : S.I (S.nativeTile A n w).ty) (h' : ℕ) (hh : h' = h + 1)
    (j : S.I (S.descendantNode A h' n w).ty) (hij : HEq i j) :
    S.descendantNode A h (n + 1) (certificate_child_equations_snoc A n w i) =
      (S.descendantNode A h' n w).child h j := by
  subst hh
  induction n generalizing A with
  | zero =>
    have hj : i = j := eq_of_heq hij
    subst hj
    apply FramedNode.ext
    · rfl
    · apply AffineIsometryEquiv.ext
      intro x
      rfl
  | succ n ih =>
    change (S.descendantNode (S.child A w.1).ty h (n + 1)
        (certificate_child_equations_snoc (S.child A w.1).ty n w.2 i)).move
          (S.placeChild (h + (n + 1)) w.1) =
      ((S.descendantNode (S.child A w.1).ty (h + 1) n w.2).move
        (S.placeChild (h + 1 + n) w.1)).child h j
    rw [ih (S.child A w.1).ty w.2 i j hij, certificate_child_equations_move_child,
      show h + (n + 1) = h + 1 + n by omega]

/-- Q11, V4 2.7: the normalized frame of the appended word is the role placement
followed by the parent's normalized frame. -/
private theorem certificate_child_equations_frame (A : S.ι) (a : ℕ) (w : S.RoleWord A a)
    (i : S.I (S.nativeTile A a w).ty) :
    prototypeDescendantFrame A (a + 1) (certificate_child_equations_snoc A a w i) =
      (rolePlacement (⟨(S.nativeTile A a w).ty, i⟩ : S.Role)).trans
        (prototypeDescendantFrame A a w) := by
  have hT := certificate_child_equations_desc_type A 1 a w
  let j : S.I (S.descendantNode A 1 a w).ty := cast (congrArg S.I hT.symm) i
  have hij : HEq i j := (cast_heq _ _).symm
  have hN : S.nativeTile A (a + 1) (certificate_child_equations_snoc A a w i) =
      (S.descendantNode A 1 a w).child 0 j :=
    certificate_child_equations_desc_snoc A 0 a w i 1 rfl j hij
  have hchild : ∀ (T' : S.ι) (hT' : T' = (S.nativeTile A a w).ty) (j' : S.I T'), HEq i j' →
      (S.child T' j').frame = (S.child (S.nativeTile A a w).ty i).frame := by
    rintro _ rfl j' h
    rw [eq_of_heq h]
  apply AffineEquiv.ext
  intro x
  show (S.σ ^ (a + 1)).symm
      ((S.nativeTile A (a + 1) (certificate_child_equations_snoc A a w i)).frame x) =
    (S.σ ^ a).symm ((S.nativeTile A a w).frame
      (S.σ.symm ((S.child (S.nativeTile A a w).ty i).frame x)))
  rw [hN]
  show (S.σ ^ (a + 1)).symm ((S.descendantNode A 1 a w).frame (S.placeChild 0 j x)) = _
  have h0 : S.placeChild 0 j x = (S.child (S.nativeTile A a w).ty i).frame x := by
    have := certificate_child_equations_place_scaled (S := S) 0 j x
    simp only [pow_zero, LinearEquiv.coe_one, id_eq] at this
    rw [this, hchild _ hT j hij]
  rw [h0]
  set y := (S.child (S.nativeTile A a w).ty i).frame x
  have h1 := certificate_child_equations_desc_scaled A 1 a w (S.σ.symm y)
  rw [pow_one, LinearEquiv.apply_symm_apply] at h1
  rw [h1, LinearEquiv.symm_apply_eq, pow_succ', LinearEquiv.mul_apply,
    LinearEquiv.apply_symm_apply]

/-- Q11, V4 2.7: equality of hierarchy nodes from heights and framed nodes. -/
private theorem certificate_child_equations_node_ext (U : HonestSource S) (n m : ℕ)
    (x : {N // N ∈ U.hierarchy.nodes n}) (y : {N // N ∈ U.hierarchy.nodes m})
    (hnm : n = m) (hxy : x.val = y.val) : (⟨n, x⟩ : U.Node) = ⟨m, y⟩ := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  subst hnm
  dsimp only at hxy
  subst hxy
  rfl

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
  obtain ⟨U, B, hB, rfl⟩ := hD
  refine ⟨certificate_child_equations_snoc _ a w i,
    certificate_child_equations_frame _ a w i, ?_⟩
  let q : U.Node := ⟨P.K, ⟨B, hB⟩⟩
  let N := U.descendant q a (by show a ≤ P.K; omega) w
  have hN : 1 ≤ N.1 := by show 1 ≤ P.K - a; omega
  have hty : N.2.val.ty = (S.nativeTile B.ty a w).ty := U.descendant_type q a _ w
  let j : S.I N.2.val.ty := cast (congrArg S.I hty.symm) i
  have hij : HEq i j := (cast_heq _ _).symm
  have hrole : (⟨N.2.val.ty, j⟩ : S.Role) = ⟨(S.nativeTile B.ty a w).ty, i⟩ :=
    Sigma.ext hty hij.symm
  have hchild : U.descendant q (a + 1) ha (certificate_child_equations_snoc B.ty a w i) =
      U.childNode N hN j := by
    apply certificate_child_equations_node_ext
    · show P.K - (a + 1) = P.K - a - 1
      omega
    · show (S.descendantNode B.ty (P.K - (a + 1)) (a + 1)
          (certificate_child_equations_snoc B.ty a w i)).move B.frame =
        ((S.descendantNode B.ty (P.K - a) a w).move B.frame).child (P.K - a - 1) j
      rw [certificate_child_equations_desc_snoc B.ty (P.K - (a + 1)) a w i (P.K - a)
          (by omega) j hij,
        certificate_child_equations_move_child, show P.K - (a + 1) = P.K - a - 1 by omega]
  show stateOf U P (U.descendant q (a + 1) ha (certificate_child_equations_snoc B.ty a w i)) =
    childMap P (stateOf U P N) ⟨(S.nativeTile B.ty a w).ty, i⟩
  rw [← hrole, ← childMap_spec U P N hN j, hchild]

/-- Q8/Q9, V4 8.1: the downward word is recoverable from the reconstructed head's
upward address on the honest packet alphabet. It is not free auxiliary ancestry. -/
theorem packet_roles_from_head (P : Params S) (q : Packet P)
    (hq : q ∈ honestPackets S P) (j : Fin q.jstar.val) :
    q.roles j = q.head.address ⟨j.val, lt_trans j.isLt q.jstar.isLt⟩ := by
  obtain ⟨U, g, rfl⟩ := hq
  rw [packet_head]
  rfl

/-- Q8, V4 8.1: the highest state is retained, and every higher slot is ABSENT. -/
theorem packet_top_spec (P : Params S) (q : Packet P) (hq : q ∈ honestPackets S P) :
    decode q q.jstar = some q.sstar ∧
      ∀ j : Fin P.k, q.jstar < j → decode q j = none := by
  obtain ⟨U, g, rfl⟩ := hq
  constructor
  · unfold decode
    split_ifs with h
    · congr
      change (packetOf U P g).descend (↑(topSlot U P g) - ↑(topSlot U P g)) = _
      have : (topSlot U P g).val - (topSlot U P g).val = 0 := Nat.sub_self _
      rw [this]
      rfl
    · exfalso
      have h1 : ¬ (↑(packetOf U P g).jstar ≤ ↑(packetOf U P g).jstar ∧ (packetOf U P g).mask (packetOf U P g).jstar) := h
      simp only [le_refl, true_and] at h1
      have h2 : (packetOf U P g).mask (packetOf U P g).jstar := by
        change packetMask P g.incidence (packetOf U P g).head (topSlot U P g)
        have h_head : (packetOf U P g).head = stateOf U P (U.hierarchy.ancestor g.birth 0) := by
          dsimp [Packet.head]
          have h0 : (⟨0, P.k_pos⟩ : Fin P.k) ≤ topSlot U P g := by
            have : NeZero P.k := ⟨P.k_pos.ne'⟩
            exact Fin.zero_le _
          exact reconstructed_spec U P g ⟨0, P.k_pos⟩ h0
        rw [h_head]
        have h_birth : U.hierarchy.ancestor g.birth 0 = g.birth := rfl
        rw [h_birth]
        rw [← packet_mask_fn]
        dsimp [topSlot]
        have h3 : (presentSlots U P g).max' (presentSlots_nonempty U P g) ∈ presentSlots U P g :=
          Finset.max'_mem (presentSlots U P g) (presentSlots_nonempty U P g)
        have h4 : mask U P g ((presentSlots U P g).max' (presentSlots_nonempty U P g)) := by
          classical
          exact (Finset.mem_filter.mp h3).2
        exact h4
      exact h1 h2
  · intro j hj
    unfold decode
    split_ifs with h
    · exfalso
      have h1 : j.val ≤ (packetOf U P g).jstar.val := h.1
      omega
    · rfl

/-- Q8/Q9, V4 8.1: decoding is injective on the honest compressed alphabet.
Together with `decode_spec` this is the lossless equivalence with Definition 2.5;
arbitrary raw tuples are not declared admissible. -/
private theorem packet_eq_of_fields {P : Params S} (q q' : Packet P)
    (hι : q.incidence = q'.incidence) (hj : q.jstar = q'.jstar)
    (hs : q.sstar = q'.sstar)
    (hr : ∀ (a : ℕ) (h : a < q.jstar.val) (h' : a < q'.jstar.val),
      q.roles ⟨a, h⟩ = q'.roles ⟨a, h'⟩) : q = q' := by
  obtain ⟨ι, j, s, r⟩ := q
  obtain ⟨ι', j', s', r'⟩ := q'
  dsimp only at hι hj hs hr
  subst hι hj hs
  have : r = r' := by
    funext a
    exact hr a.1 a.2 a.2
  subst this
  rfl

theorem packet_encoding_injective (P : Params S) (q q' : Packet P)
    (hq : q ∈ honestPackets S P) (hq' : q' ∈ honestPackets S P)
    (hι : q.incidence = q'.incidence) (hslots : ∀ j, decode q j = decode q' j) : q = q' := by
  have hhead : q.head = q'.head := by
    have h := hslots ⟨0, P.k_pos⟩
    rw [(honest_packet_admissible P q hq).1,
      (honest_packet_admissible P q' hq').1] at h
    exact Option.some.inj h
  have hmask : ∀ j, q.mask j ↔ q'.mask j := by
    intro j
    show packetMask P q.incidence q.head j ↔ packetMask P q'.incidence q'.head j
    rw [hι, hhead]
  have hjs : q.jstar = q'.jstar := by
    have a1 := (honest_packet_admissible P q hq).2.2.1
    have a2 := (honest_packet_admissible P q' hq').2.2.1
    exact le_antisymm
      ((honest_packet_admissible P q' hq').2.2.2.1 _ ((hmask _).1 a1))
      ((honest_packet_admissible P q hq).2.2.2.1 _ ((hmask _).2 a2))
  have hss : q.sstar = q'.sstar := by
    have e := hslots q.jstar
    rw [(packet_top_spec P q hq).1] at e
    have e' := (packet_top_spec P q' hq').1
    rw [← hjs] at e'
    exact Option.some.inj (e.trans e')
  have hr : ∀ (a : ℕ) (h : a < q.jstar.val) (h' : a < q'.jstar.val),
      q.roles ⟨a, h⟩ = q'.roles ⟨a, h'⟩ := by
    intro a h h'
    rw [packet_roles_from_head P q hq ⟨a, h⟩, packet_roles_from_head P q' hq' ⟨a, h'⟩, hhead]
  exact packet_eq_of_fields q q' hι hjs hss hr

/-- Q10, V4 §2.4: every honest pre-pattern has an honest state and honest non-NULL
packets. The range is joint: this does not assert that arbitrary marginal choices occur. -/
theorem prePattern_components_honest (P : Params S) (w : PrePattern P)
    (hw : w ∈ honestPrePatterns S P) :
    w.state ∈ honestStates S P ∧
      ∀ f q, w.packets f = some q → q ∈ honestPackets S P := by
  obtain ⟨U, t, ht, rfl⟩ := hw
  constructor
  · exact stateOf_mem U P t
  · intro f q hfq
    change (by classical exact if hf : U.hierarchy.IsFault t f then none else some (packetOf U P (U.providerOccurrence P t f hf))) = some q at hfq
    by_cases hf : U.hierarchy.IsFault t f
    · rw [dif_pos hf] at hfq
      contradiction
    · rw [dif_neg hf] at hfq
      exact ⟨U, U.providerOccurrence P t f hf, Option.some.inj hfq⟩

/-- Q11, V4 2.7: each honest certificate component has its actual source meaning.
The certificate itself, not independent component membership, records their joint witness. -/
theorem certificate_components_honest (P : Params S) (D : Certificate P)
    (hD : D ∈ honestCerts S P) :
    (∀ w, D.leaves w ∈ honestPrePatterns S P) ∧
      ∀ a ha w, D.table a ha w ∈ honestStates S P := by
  obtain ⟨U, B, hB, rfl⟩ := hD
  constructor
  · intro w
    exact ⟨U, U.descendant ⟨P.K, B, hB⟩ P.K le_rfl w, Nat.sub_self P.K, rfl⟩
  · intro a ha w
    exact ⟨U, U.descendant ⟨P.K, B, hB⟩ a ha w, rfl⟩

private lemma frameMarker_rigid_step1_center_aux (φ : Iso d) (c : E d) (r : ℝ) (hr : 0 < r)
    (hφ : φ '' Metric.closedBall c r = Metric.closedBall c r) : φ c = c := by
  have hballs : Metric.closedBall (φ c) r = Metric.closedBall c r :=
    (φ.toIsometryEquiv.image_closedBall c r).symm.trans hφ
  by_contra hne
  have hpos : 0 < ‖φ c - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hscale : 0 ≤ r / ‖φ c - c‖ := (div_pos hr hpos).le
  have hv : ‖(r / ‖φ c - c‖) • (φ c - c)‖ = r := by
    rw [norm_smul_of_nonneg hscale, div_mul_cancel₀ r hpos.ne']
  -- Extend the segment from c to φ c by one radius beyond φ c.
  have hx : φ c + (r / ‖φ c - c‖) • (φ c - c) ∈ Metric.closedBall (φ c) r := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hv]
  rw [hballs, Metric.mem_closedBall, dist_eq_norm] at hx
  have heq : φ c + (r / ‖φ c - c‖) • (φ c - c) - c =
      (1 + r / ‖φ c - c‖) • (φ c - c) := by
    rw [add_smul, one_smul]
    abel
  rw [heq, norm_smul_of_nonneg (by linarith : 0 ≤ 1 + r / ‖φ c - c‖),
    add_mul, one_mul, div_mul_cancel₀ r hpos.ne'] at hx
  linarith

private lemma frameMarker_rigid_step1_center (P : Params S) (A : S.ι) (φ : Iso d)
    (hφ : ∀ a : Fin (d + 1),
      φ '' Metric.closedBall ((P.marker A).centre a) (P.marker A).radius =
        Metric.closedBall ((P.marker A).centre a) (P.marker A).radius) :
    ∀ a : Fin (d + 1), φ ((P.marker A).centre a) = (P.marker A).centre a := by
  intro a
  let c := ((P.marker A).centre a)
  let r := (P.marker A).radius
  have hr : 0 < r := (P.marker A).radius_pos
  have eq1 : φ '' Metric.closedBall c r = Metric.closedBall c r := hφ a
  exact frameMarker_rigid_step1_center_aux φ c r hr eq1

private lemma frameMarker_rigid_step2_span (P : Params S) (A : S.ι) :
    affineSpan ℝ (Set.range (P.marker A).centre) = ⊤ := by
  have hindep := (P.marker A).independent
  have H : affineSpan ℝ (Set.range (P.marker A).centre) = ⊤ ↔ Fintype.card (Fin (d + 1)) = Module.finrank ℝ (E d) + 1 := by
    exact AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one hindep
  have H2 : Fintype.card (Fin (d + 1)) = d + 1 := Fintype.card_fin (d + 1)
  have H3 : Module.finrank ℝ (E d) = d := finrank_euclideanSpace_fin
  rw [H2, H3] at H
  exact H.mpr rfl

omit [Fact (2 ≤ d)] in
private lemma frameMarker_rigid_step3_ext (φ : Iso d) (c : Fin (d+1) → E d)
    (hspan : affineSpan ℝ (Set.range c) = ⊤) (hfix : ∀ a, φ (c a) = c a) :
    φ = AffineIsometryEquiv.refl ℝ (E d) := by
  have h : φ.toAffineEquiv = (AffineIsometryEquiv.refl ℝ (E d)).toAffineEquiv :=
    AffineEquiv.ext_on hspan _ _ (by
      rintro _ ⟨a, rfl⟩
      simpa using hfix a)
  exact AffineIsometryEquiv.toAffineEquiv_injective h

/-- Q10, V4 §2.4 (frame marker): preserving every labelled marker ball fixes the
entire Euclidean frame, including its orientation. Reflections are allowed in the
isometry group; affine independence rules out every nonidentity stabilizer. -/
theorem frameMarker_rigid (P : Params S) (A : S.ι) (φ : Iso d)
    (hφ : ∀ a : Fin (d + 1),
      φ '' closedBall ((P.marker A).centre a) (P.marker A).radius =
        closedBall ((P.marker A).centre a) (P.marker A).radius) :
    φ = AffineIsometryEquiv.refl ℝ (E d) := by
  have h1 := frameMarker_rigid_step1_center P A φ (fun a => hφ a)
  have h2 := frameMarker_rigid_step2_span P A
  exact frameMarker_rigid_step3_ext φ (P.marker A).centre h2 h1

/-- Q11, V4 2.7: an actual source supplies certificates at the fixed certificate
height. No global nonemptiness of the species is imposed. -/
theorem honestCerts_nonempty (U : HonestSource S) (P : Params S) :
    (honestCerts S P).Nonempty := by
  obtain ⟨B, hB, _⟩ := U.hierarchy.cover P.K (0 : E d)
  exact ⟨certOf U P B hB, U, B, hB, rfl⟩

end Enforce
