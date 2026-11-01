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
  sorry

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

/-- Step 1 of the V4 proof of `packet_attached` (V4 2.6(c), via 1.0 native ownership):
"every native tile `t` with a facet piece `f_t ⊆ g`" lies in the birth parent of `g`:
since `relint g` is interior to the birth parent, the tile meets that interior and
is one of its native tiles, so its ancestor at the birth height is the birth parent. -/
private theorem packet_attached_step1_owner (U : HonestSource S) (P : Params S)
    (g : PrimitiveOccurrence U P) (t : U.Node) (ht : t.1 = 0)
    (f : FacetName S t.2.val.ty) (hfg : t.2.val.cell t.1 f.val ⊆ g.carrier) :
    U.hierarchy.ancestor t g.birth.1 = g.birth := by
  sorry

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
  sorry

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
