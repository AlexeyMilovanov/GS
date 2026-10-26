import Enforce.Parser.Host

/-!
# Assembly, forward states, the all-height hierarchy, and W4

R7--R13, V4 3.7--3.13 and 3.1, with the Req′ proof of V4 8.3.
A new parent first has geometry and old child states. Its state is then the
parent slot of a readable facet in the first child's first branching descendant.
Routing and the child equations are conclusions, never assumptions on that state.

The all-height theorem produces a single nested sequence of decoded levels,
and a coherent hierarchy on the exact native projection of Y. Its low levels
are exactly the inner nodes of the certificate base. Choices of levels, hierarchy
and states are made from that one theorem, preserving all correlations.

DEVIATION: the unnamed first child C₁ of Definition 3.9 is selected using
Classical.choice, since substitution roles are finite types without an order.
The readable facet is selected from Lemma 3.8. Lemma 3.10 states independence
of these choices by equality on every PRESENT parent slot in E_P.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d} {P : Params S}
variable {C : ClusterData S P}

namespace Parser

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ}

/-- R7, V4 3.7: the set of proposed parents, identifying repeated framed copies. -/
def proposedParents (D : DecodedLevel Y n) : Set (FramedNode S) :=
  {N | ∃ B : Block Y n, ∃ hB : B ∈ D.geometry.blocks, proposedParent D B hB = N}

/-- R7, V4 3.7: the complete geometric assembly assertion for a new level.
Its roots are exactly the proposed parents; all prescribed children have their
old decoded frames and first letters, so every child proposes that same parent. -/
structure AssemblyGeometry (D : DecodedLevel Y n) (G : GeometricLevel Y (n + 1)) : Prop where
  /-- R7, V4 3.7: no proposed parent is omitted and no extra root is introduced. -/
  roots_eq : G.roots = proposedParents D
  /-- R7, V4 3.7: every root has all prescribed children with the old first letters. -/
  children : ∀ N ∈ G.roots, Nonempty (AssembledParent D N)
  /-- R7, V4 3.7: every old root is a prescribed child of its proposed parent. -/
  old_child : ∀ (B : Block Y n) (hB : B ∈ D.geometry.blocks),
    ∃ i : S.I (proposedParent D B hB).ty,
      B.node = (proposedParent D B hB).child n i

end Parser

/-- R7, V4 3.7: all proposed parents form a genuine geometric level n+1,
with disjoint interiors and whole-space coverage. Each parent is the union of
its actual level-n children, in their prescribed frames, and PP(C) = PP(B).
The one-child case is included; no branching hypothesis is added. -/
theorem assembly (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D) :
    ∃ G : GeometricLevel Y (n + 1), Parser.AssemblyGeometry D G := by
  sorry

namespace Parser

/-- R7, V4 3.7: the assembled geometry selected from the complete assembly theorem.
An actual proper output and its decoded old level supply the existence witness. -/
def assembledGeometry (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D) :
    GeometricLevel Y (n + 1) := Classical.choose (assembly Y hY n hn D hD)

/-- R7, V4 3.7: the selected geometry has exactly the proposed roots and child data. -/
theorem assembledGeometry_spec (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D) :
    AssemblyGeometry D (assembledGeometry Y hY n hn D hD) :=
  Classical.choose_spec (assembly Y hY n hn D hD)

/-- R7, V4 3.7: choose the already assembled child family at a new root.
This chooses only old geometric blocks and their proven first letters. -/
def assembledParent (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (hN : N ∈ (assembledGeometry Y hY n hn D hD).roots) :
    AssembledParent D N :=
  Classical.choice ((assembledGeometry_spec Y hY n hn D hD).children N hN)

/-- R7, V4 3.7: every strict descendant of an assembled parent already had a state.
The strict inequality excludes only the newly assembled root itself. -/
theorem assembled_inner_mem {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (N : FramedNode S) (A : AssembledParent D N)
    (m : ℕ) (M : FramedNode S) (hm : m < n + 1)
    (hM : M.IsDescendant m N (n + 1)) : M ∈ D.geometry.nodes m := by
  sorry

/-- R8, V4 3.8, replacement V4 8.3: a readable facet for one assembled child.
It belongs to F(A_C), has a positive birth inside C, belongs to both E_C and
E_P, and its honest attached packet has both indicated slots PRESENT.
No field assumes a state of the new parent or a routing conclusion. -/
structure ReadableFacet {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (N : FramedNode S) (A : AssembledParent D N)
    (i : S.I N.ty) where
  /-- R8, V4 3.8, 8.3: the positioned primitive facet in child prototype coordinates. -/
  facet : PrimitiveFacet S (A.children i).val.node.ty
  /-- R8, V4 3.8, 8.3: the facet is in the first branching descendant's F(A_C). -/
  first_branching : facet ∈ firstBranchingFacets (A.children i).val.node.ty
  /-- R8, V4 3.8, 8.3: the birth remains strictly above native tiles. -/
  depth_lt : facet.depth < n
  /-- R8, V4 3.8, 8.3: the same primitive occurrence in ambient framed coordinates. -/
  birthFacet : BornFacet P
  /-- R8, V4 3.8, 8.3: exact absolute birth height. -/
  height_eq : birthFacet.height = n - facet.depth
  /-- R8, V4 3.8, 8.3: exact birth node and frame in the child subdivision. -/
  birth_eq : birthFacet.birth = (facet.birthNode n).move (A.children i).val.node.frame
  /-- R8, V4 3.8, 8.3: the two coordinate descriptions have the same primitive support. -/
  carrier_eq : birthFacet.carrier = (A.children i).val.node.prototypeFrame n '' facet.carrier
  /-- R8, V4 3.8, 8.3: the birth is inside this actual child, with its prescribed frame. -/
  inside_child : birthFacet.birth.IsDescendant birthFacet.height (A.children i).val.node n
  /-- R8, V4 3.8, 8.3: membership in the child's principal set. -/
  child_principal : P.InPrincipal (A.children i).val.node n birthFacet.carrier
  /-- R8, V4 3.8, 8.3: membership in the parent's principal set by the iF(A_i) list. -/
  parent_principal : P.InPrincipal N (n + 1) birthFacet.carrier
  /-- R8, V4 3.8: the child's slot in the finite packet window. -/
  childSlot : Fin P.k
  /-- R8, V4 3.8: slots count upward from the positive birth height. -/
  childSlot_eq : childSlot.val = n - birthFacet.height
  /-- R8, V4 3.8: the immediately following parent slot. -/
  parentSlot : Fin P.k
  /-- R8, V4 3.8: the parent's exact upward slot index. -/
  parentSlot_eq : parentSlot.val = n + 1 - birthFacet.height
  /-- R8, V4 3.8: the packet is read from the actual left-side native pieces. -/
  constancy : BoundaryPackets Y (birthFacet.height - 1) birthFacet.leftNode
  /-- R8, V4 3.8: the non-NULL attached packet. -/
  packet : Packet P
  /-- R8, V4 3.8: attachment is the actual output marking's pre-pattern readout. -/
  attached : birthFacet.packet constancy = some packet
  /-- R8, V4 3.8: the packet belongs to the original finite honest alphabet. -/
  honest : packet ∈ honestPackets S P
  /-- R8, V4 3.8: the old child slot equals the child's existing assigned state. -/
  child_decode : decode packet childSlot =
    some (D.blockState (A.children i).val (A.children i).property)
  /-- R8/R9, V4 3.8--3.9: the value of the PRESENT parent slot, before naming S(P). -/
  parentState : State P
  /-- R8/R9, V4 3.8--3.9: presence of the parent slot with this exact value. -/
  parent_decode : decode packet parentSlot = some parentState

end Parser

/-- R8, V4 3.8, replacement V4 8.3: every assembled child has a readable facet
in F(A_C) ∩ E_C ∩ E_P, born inside C, with both slots PRESENT.
The child supplies a first branching descendant even for a placeholder type;
n ≥ K and the parameter inequalities make its birth positive. -/
theorem readable_facet (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N) (i : S.I N.ty) :
    Nonempty (Parser.ReadableFacet D N A i) := by
  sorry

namespace Parser

/-- R9, V4 3.9: select C₁ from the nonempty prescribed child list.
DEVIATION: roles have no preferred enumeration; Classical.choice supplies the
paper's unnamed first child. Routing will give the same state from every child. -/
def firstChild (A : S.ι) : S.I A := Classical.choice (roles_nonempty A)

/-- R8/R9, V4 3.8--3.9: choose a readable facet with its actual packet slots.
The existence comes from the geometric first branching descendant, not an
assumed state or child equation for the new parent. -/
def readableFacet (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : AssembledParent D N) (i : S.I N.ty) :
    ReadableFacet D N A i := Classical.choice (readable_facet Y hY n hn D hD N A i)

end Parser

/-- R9, V4 3.9: S(P) is the PRESENT parent slot of the chosen readable facet
of C₁. It is read from the actual attached packet, not chosen as a free honest
state. DEVIATION: the unordered role type's first child is `Parser.firstChild`;
V4 3.10 will assert that every principal primitive facet gives this same value. -/
def newState (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N) : State P :=
  (Parser.readableFacet Y hY n hn D hD N A (Parser.firstChild N.ty)).parentState

section Forward

variable (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
variable (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
variable (N : FramedNode S) (A : Parser.AssembledParent D N)

include hY hn hD A

/-- R9, V4 3.9: the defining parent slot is PRESENT and literally equals newState. -/
theorem newState_readout :
    let r := Parser.readableFacet Y hY n hn D hD N A (Parser.firstChild N.ty)
    decode r.packet r.parentSlot = some (newState Y hY n hn D hD N A) :=
  (Parser.readableFacet Y hY n hn D hD N A (Parser.firstChild N.ty)).parent_decode

section RoutingConstant

omit hY hn hD A

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"Every primitive facet f in E_P" is an actual positioned birth. This relation
retains its birth depth, full birth frame, and carrier, in the normalized
coordinates used by Lemma 1.25. -/
private def routing_constant_step1_realizes (N : FramedNode S) (m : ℕ)
    (f : PrimitiveFacet S N.ty) (g : Parser.BornFacet P) : Prop :=
  g.height + f.depth = m ∧
    g.birth = (f.birthNode m).move N.frame ∧
    g.carrier = N.prototypeFrame m '' f.carrier

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"born strictly below P" refers to the prescribed subdivision. A normalized
birth realization gives the actual framed descendant relation. -/
private theorem routing_constant_step1_descendant (N : FramedNode S) (m : ℕ)
    (f : PrimitiveFacet S N.ty) (g : Parser.BornFacet P)
    (h : routing_constant_step1_realizes N m f g) :
    g.birth.IsDescendant g.height N m := by
  refine ⟨f.depth, h.1.symm, f.word, ?_⟩
  have hsum := h.1
  have hh : m - f.depth = g.height := by omega
  simpa only [PrimitiveFacet.birthNode, hh] using h.2.1

/-- Step 1 of the V4 proof of `routing_constant` (V4 3.10):
"applied inside P". Transport the normalized birth frame to the assembled
parent, retaining the full anisotropic prototype frame. -/
private theorem routing_constant_step1_frame (N : FramedNode S) (m : ℕ)
    (f : PrimitiveFacet S N.ty) (hf : f.depth ≤ m) :
    ((f.birthNode m).move N.frame).prototypeFrame (m - f.depth) =
      f.birthFrame.trans (N.prototypeFrame m) := by
  have h := (f.birthFrame_spec m hf).2
  apply AffineEquiv.ext
  intro x
  have hx := congrArg (fun e : E d ≃ᵃ[ℝ] E d => e x) h
  change (S.σ ^ m).symm ((f.birthNode m).prototypeFrame (m - f.depth)
    x) = f.birthFrame x at hx
  have hx' := congrArg (fun z => N.frame ((S.σ ^ m) z)) hx
  simpa only [LinearEquiv.apply_symm_apply] using hx'

/-- Step 1 of the V4 proof of `routing_constant` (V4 3.10):
"For b = n+1 the facet is first-generation in P". A descendant at the same
height is exactly the root, including its frame. -/
private theorem routing_constant_step1_equal_height (N M : FramedNode S) (m : ℕ)
    (h : M.IsDescendant m N m) : M = N := by
  obtain ⟨r, hr, w, hw⟩ := h
  have : r = 0 := by omega
  subst r
  simpa only [SubstSystem.descendantNode, FramedNode.move,
    AffineIsometryEquiv.refl_trans] using hw

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"its address gives the actual path up to P". The type at the end of a fixed
role word is independent of the absolute height. -/
private theorem routing_constant_step1_descendant_type (T : S.ι) (h r : ℕ)
    (w : S.RoleWord T r) :
    (S.descendantNode T h r w).ty = (S.nativeTile T r w).ty := by
  induction r generalizing T with
  | zero => rfl
  | succ r ih => exact ih (S.child T w.1).ty w.2

/-- Step 1 of the V4 proof of `routing_constant` (V4 3.10):
"born in a node P_b inside P". Express a born facet using the normalized
incidence and the prototype frame of that birth node. -/
private theorem routing_constant_step1_carrier (g : Parser.BornFacet P) :
    g.carrier = g.birth.prototypeFrame g.height ''
      (S.σ.symm '' g.incidence.val.positioned) := by
  simp only [Parser.BornFacet.carrier, Params.incidencePlacement,
    PrimitiveIncidence.positioned, placedSet, Set.image_image]
  rfl

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"Every primitive facet f in E_P". Normalize an actual principal birth by
its own descendant address; principal membership follows from the carrier
and depth, without assuming uniqueness of primitive addresses. -/
private theorem routing_constant_step1_normalize (N : FramedNode S) (m : ℕ)
    (g : Parser.BornFacet P) (hbirth : g.birth.IsDescendant g.height N m)
    (hdepth : m - g.height < P.k) (hprincipal : P.InPrincipal N m g.carrier) :
    ∃ f ∈ P.E_A N.ty, routing_constant_step1_realizes N m f g := by
  obtain ⟨r, hr, w, hw⟩ := hbirth
  have ht : (S.nativeTile N.ty r w).ty = g.incidence.val.ty :=
    ((congrArg FramedNode.ty hw).trans
      (routing_constant_step1_descendant_type N.ty g.height r w)).symm.trans
        g.parent_type.symm
  let f : PrimitiveFacet S N.ty := {
    depth := r
    word := w
    localCarrier := g.incidence.val.positioned
    realization := by
      rw [ht]
      exact ⟨g.incidence.val.left, g.incidence.val.leftFacet, rfl,
        g.incidence.val.internal⟩ }
  have hd : f.depth < P.k := by change r < P.k; omega
  have hm : f.depth ≤ m := by change r ≤ m; omega
  have hh : m - f.depth = g.height := by change m - r = g.height; omega
  have hb : g.birth = (f.birthNode m).move N.frame := by
    simpa only [PrimitiveFacet.birthNode, hh] using hw
  have hframe : g.birth.prototypeFrame g.height =
      f.birthFrame.trans (N.prototypeFrame m) := by
    rw [hb, ← hh]
    exact routing_constant_step1_frame N m f hm
  have hcarrier : g.carrier = N.prototypeFrame m '' f.carrier := by
    rw [routing_constant_step1_carrier, hframe]
    simp only [PrimitiveFacet.carrier, Set.image_image]
    rfl
  refine ⟨f, ?_, hr.symm, hb, hcarrier⟩
  obtain ⟨e, he, hec⟩ := hprincipal
  have he' : e ∈ principalFacets S N.ty P.k (P.component N.ty) := by
    rw [← P.E_A_eq N.ty]
    exact he
  have hfe : f.carrier = e.carrier :=
    (N.prototypeFrame m).injective.image_injective (hcarrier.symm.trans hec.symm)
  change f ∈ (P.E_A N.ty : Set (PrimitiveFacet S N.ty))
  rw [P.E_A_eq]
  exact ⟨hd, hfe.symm ▸ he'.2⟩

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"first-generation facets". At native height the conjugated child placement
is the original prescribed isometry. -/
private theorem routing_constant_step1_ground_child (T : S.ι) (i : S.I T)
    (e : Cell d) :
    ((⟨T, AffineIsometryEquiv.refl ℝ (E d)⟩ : FramedNode S).child 0 i).cell 0 e =
      placedSet (S.child T i).frame e.carrier := by
  have hp : S.placeChild 0 i = (S.child T i).frame := by
    ext x
    simp [SubstSystem.placeChild_apply, linearConj, Child.frame, rigidMotion]
  simp [FramedNode.cell, FramedNode.prototypeFrame, FramedNode.child, hp, placedSet]

/-- Step 1 of the V4 proof of `routing_constant` (V4 3.10):
"the record with incidence iota(g)". Whole-facet pairing and the canonical
transversal assign the normalized facet its side-independent incidence. -/
private theorem routing_constant_step1_incidence {T : S.ι}
    (f : PrimitiveFacet S T) :
    ∃ a : P.Incidence, a.val.ty = f.birthType ∧ a.val.positioned = f.localCarrier := by
  obtain ⟨i, e, he, hint⟩ := f.realization
  let B : FramedNode S := ⟨f.birthType, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hc : B.carrier (0 + 1) = S.supertile 1 f.birthType := by
    simp [B, FramedNode.carrier, placedSet]
  have hne : (relint (placedSet (S.child f.birthType i).frame e.val.carrier)).Nonempty := by
    change (intrinsicInterior ℝ
      ((S.child f.birthType i).frame.toAffineIsometry '' e.val.carrier)).Nonempty
    rw [AffineIsometry.image_intrinsicInterior]
    exact e.val.flat.relint_nonempty.image _
  have hpair := internal_facet_pairing B 0 i e (by
    rw [routing_constant_step1_ground_child, hc]
    rw [he] at hint
    exact hne.mono (fun _ hx => ⟨hx, hint hx⟩))
  obtain ⟨j, ⟨hji, e', he', _⟩, _⟩ := hpair.2
  let a : PrimitiveIncidence S := {
    ty := f.birthType
    left := i
    right := j
    distinct := Ne.symm hji
    leftFacet := e
    rightFacet := e'
    paired := by
      rw [routing_constant_step1_ground_child, routing_constant_step1_ground_child] at he'
      exact he'.symm
    internal := by rw [he] at hint; exact hint }
  refine ⟨P.canonical a, (P.canonical_spec a).1.symm, ?_⟩
  exact (P.canonical_spec a).2.symm.trans he.symm

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"Every primitive facet f in E_P has a well-defined attached packet".
First realize each normalized facet as a positive-height framed birth. -/
private theorem routing_constant_step1_realize (N : FramedNode S) (m : ℕ)
    (f : PrimitiveFacet S N.ty) (hf : f.depth < m) :
    ∃ g : Parser.BornFacet P, routing_constant_step1_realizes N m f g := by
  obtain ⟨a, hat, hac⟩ := routing_constant_step1_incidence (P := P) f
  let g : Parser.BornFacet P := {
    height := m - f.depth
    positive := by omega
    birth := (f.birthNode m).move N.frame
    incidence := a
    parent_type := hat.trans (f.birthFrame_spec m (Nat.le_of_lt hf)).1.symm }
  refine ⟨g, ?_, rfl, ?_⟩
  · change m - f.depth + f.depth = m
    omega
  · rw [routing_constant_step1_carrier]
    change ((f.birthNode m).move N.frame).prototypeFrame (m - f.depth) ''
      (S.σ.symm '' a.val.positioned) = N.prototypeFrame m '' f.carrier
    rw [routing_constant_step1_frame N m f (Nat.le_of_lt hf), hac]
    simp only [PrimitiveFacet.carrier, Set.image_image]
    rfl

/-- Step 1 of the V4 proof of `routing_constant` (V4 8.3):
"the attached packet". A fixed normalized facet has a unique born-facet
representation: its height and frame are fixed, and the incidence catalogue
has one representative of each positioned provider. -/
private theorem routing_constant_step1_unique (N : FramedNode S) (m : ℕ)
    (f : PrimitiveFacet S N.ty) (g g' : Parser.BornFacet P)
    (hg : routing_constant_step1_realizes N m f g)
    (hg' : routing_constant_step1_realizes N m f g') : g = g' := by
  have hh : g.height = g'.height := by have := hg.1; have := hg'.1; omega
  have hb : g.birth = g'.birth := hg.2.1.trans hg'.2.1.symm
  have hc : g.carrier = g'.carrier := hg.2.2.trans hg'.2.2.symm
  rw [routing_constant_step1_carrier, routing_constant_step1_carrier, hb, hh] at hc
  have hp : g.incidence.val.positioned = g'.incidence.val.positioned :=
    S.σ.symm.injective.image_injective
      ((g'.birth.prototypeFrame g'.height).injective.image_injective hc)
  have hi : g.incidence = g'.incidence := by
    have h := P.canonical_unique g.incidence.val g'.incidence
      ⟨g.parent_type.trans ((congrArg FramedNode.ty hb).trans g'.parent_type.symm), hp⟩
    simpa only [P.canonical_idempotent] using h
  cases g
  cases g'
  cases hh
  cases hb
  cases hi
  rfl

/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"For a facet born strictly below P, this follows from (I5) and Lemma 3.4
inside a child; for a first-generation facet of P, it follows from the second
assertion of Lemma 3.4". Both cases supply an actual honest packet. -/
private theorem routing_constant_step2_attachment
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (g : Parser.BornFacet P) (hbirth : g.birth.IsDescendant g.height N (n + 1)) :
    ∃ hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode,
      ∃ q : Packet P, g.packet hl = some q ∧ q ∈ honestPackets S P := by
  have hle := Parser.descendant_height_le _ _ _ _ hbirth
  by_cases hlt : g.height < n + 1
  · have hg := Parser.assembled_inner_mem D N A g.height g.birth hlt hbirth
    obtain ⟨hl, _, _, q, hq, _, hread, _⟩ := two_sided_constancy Y hY n hn D hD g hg
    exact ⟨hl, q, hread, hq⟩
  · have hh : g.height = n + 1 := by omega
    have hb : g.birth = N := routing_constant_step1_equal_height N g.birth (n + 1)
      (by simpa only [hh] using hbirth)
    obtain ⟨hl, _, _, q, hq, _, hread⟩ :=
      two_sided_constancy_assembled Y hY n hn D hD N A g hh hb
    exact ⟨hl, q, hread, hq⟩

/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"the head is the state of its birth node". The old two-sided theorem also
identifies the incidence, independently of the supplied constancy proof. -/
private theorem routing_constant_step2_old_readout
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (g : Parser.BornFacet P) (hg : g.birth ∈ D.geometry.nodes g.height)
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (q : Packet P) (hq : g.packet hl = some q) :
    q.incidence = g.incidence ∧ q.head = D.stateAt g.height g.birth hg := by
  obtain ⟨hl', _, _, q', _, hi, ha, _, hh⟩ := two_sided_constancy Y hY n hn D hD g hg
  have he : q = q' := Option.some.inj (hq.symm.trans ha)
  simpa only [he] using And.intro hi hh

/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"its address gives the actual path up to P". To read the address, realize
one honest old state at its actual height and frame, using the congruent
scale transfer of V4 1.13(c). No joint realization of the new parent is assumed. -/
private theorem routing_constant_step2_source_realization
    (s : State P) (hs : s ∈ honestStates S P) (N : FramedNode S) (n : ℕ)
    (hty : s.ty = N.ty) (hres : s.residue.val = n % P.L) :
    ∃ (U : HonestSource S) (hN : N ∈ U.hierarchy.nodes n),
      stateOf U P ⟨n, ⟨N, hN⟩⟩ = s := by
  obtain ⟨U, q, rfl⟩ := hs
  have hmod : q.1 % P.L = n % P.L := hres
  have hshift : (q.1 - n) % P.L = (n - q.1) % P.L := by
    rcases le_total q.1 n with h | h
    · rw [Nat.sub_eq_zero_of_le h, Nat.zero_mod]
      exact (Nat.dvd_iff_mod_eq_zero.mp ((Nat.modEq_iff_dvd' h).mp hmod)).symm
    · rw [Nat.sub_eq_zero_of_le h, Nat.zero_mod]
      exact Nat.dvd_iff_mod_eq_zero.mp ((Nat.modEq_iff_dvd' h).mp hmod.symm)
  obtain ⟨V, e, N', he⟩ := exactScaleTransfer U q.1 q.2.val q.2.property n
    (AffineIsometryEquiv.refl ℝ (E d))
  have hs' : stateOf V P ⟨n, N'⟩ = stateOf U P q := by
    have h := state_scaleTransfer P e hshift ⟨q, Nat.sub_le _ _⟩
    rw [he] at h
    exact h.symm
  have hty' : N'.val.ty = N.ty := by
    have h := e.types ⟨q, Nat.sub_le _ _⟩
    rw [he] at h
    exact h.trans hty
  let J := N'.val.frame.symm.trans N.frame
  obtain ⟨W, f, N'', hf⟩ := exactScaleTransfer V n N'.val N'.property n J
  have hs'' : stateOf W P ⟨n, N''⟩ = stateOf V P ⟨n, N'⟩ := by
    have h := state_scaleTransfer P f rfl ⟨⟨n, N'⟩, Nat.sub_le _ _⟩
    rw [hf] at h
    exact h.symm
  have hnode : N''.val = N := by
    apply FramedNode.ext
    · have h := f.types ⟨⟨n, N'⟩, Nat.sub_le _ _⟩
      rw [hf] at h
      exact h.trans hty'
    · have h := f.frames ⟨⟨n, N'⟩, Nat.sub_le _ _⟩
      rw [hf] at h
      apply AffineIsometryEquiv.ext
      intro x
      have hx := congrArg (fun g : E d ≃ᵃ[ℝ] E d => g ((S.σ ^ n).symm x)) h
      simpa [FramedNode.prototypeFrame, J] using hx
  obtain ⟨N'', hN''⟩ := N''
  dsimp only at hnode
  subst N''
  exact ⟨W, hN'', hs''.trans hs'⟩


/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"by (I2) and the children's first letters". Inside one old child, (I2)
identifies every descendant state and its ancestor in a fixed honest
realization of that child's state. -/
private theorem routing_constant_step2_source_descent
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) (hD : Inv D)
    (U : HonestSource S) (h r : ℕ) (N : FramedNode S)
    (hN : N ∈ D.geometry.nodes (h + r)) (hU : N ∈ U.hierarchy.nodes (h + r))
    (hs : stateOf U P ⟨h + r, ⟨N, hU⟩⟩ = D.stateAt (h + r) N hN)
    (w : S.RoleWord N.ty r) :
    let M := (S.descendantNode N.ty h r w).move N.frame
    ∃ (hM : M ∈ D.geometry.nodes h) (hMU : M ∈ U.hierarchy.nodes h),
      stateOf U P ⟨h, ⟨M, hMU⟩⟩ = D.stateAt h M hM ∧
        U.hierarchy.ancestor ⟨h, ⟨M, hMU⟩⟩ r = ⟨h + r, ⟨N, hU⟩⟩ := by
  induction r generalizing N with
  | zero =>
    have hnode : (S.descendantNode N.ty h 0 w).move N.frame = N := by
      cases N
      simp [SubstSystem.descendantNode, FramedNode.move]
    simp only [hnode]
    exact ⟨hN, hU, hs, rfl⟩
  | succ r ih =>
    let i := w.1
    let N' := N.child (h + r) i
    have hN' : N' ∈ D.geometry.nodes (h + r) := D.geometry.child_mem _ N hN i
    have hU' : N' ∈ U.hierarchy.nodes (h + r) := U.hierarchy.children_mem _ N hU i
    have hs' : stateOf U P ⟨h + r, ⟨N', hU'⟩⟩ = D.stateAt (h + r) N' hN' := by
      rw [hD.I2.1 (h + r) N hN i]
      simp only [Nat.add_assoc]
      rw [← hs]
      have hc := childMap_spec U P ⟨h + r + 1, ⟨N, hU⟩⟩
        (by change 1 ≤ h + r + 1; omega) i
      simpa [HonestSource.childNode, N'] using hc
    obtain ⟨hM, hMU, hstate, hanc⟩ := ih N' hN' hU' hs' w.2
    have hnode : (S.descendantNode N.ty h (r + 1) w).move N.frame =
        (S.descendantNode N'.ty h r w.2).move N'.frame := by
      simp [SubstSystem.descendantNode, FramedNode.move, FramedNode.child, N', i,
        AffineIsometryEquiv.trans_assoc]
    simp only [hnode]
    refine ⟨hM, hMU, hstate, ?_⟩
    rw [CoherentHierarchy.ancestor, Function.iterate_succ_apply']
    change U.hierarchy.parentNode (U.hierarchy.ancestor _ r) = _
    rw [hanc]
    apply Sigma.ext
    · simp [CoherentHierarchy.parentNode, Nat.add_assoc]
    · apply heq_of_eq
      apply Subtype.ext
      exact (U.hierarchy.parent_unique (h + r) ⟨N', hU'⟩ N hU ⟨i, rfl⟩).symm


/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"the children's first letters". A prescribed child and its globally distinct
role determine the parent type and full frame. -/
private theorem routing_constant_step2_parent_from_child
    (M N : FramedNode S) (m : ℕ) (j : S.I M.ty) (i : S.I N.ty)
    (hr : (⟨M.ty, j⟩ : S.Role) = ⟨N.ty, i⟩) (hc : M.child m j = N.child m i) : M = N := by
  rcases M with ⟨T, φ⟩
  rcases N with ⟨T', ψ⟩
  obtain ⟨ht, hj⟩ := Sigma.mk.inj_iff.mp hr
  dsimp only at ht hj
  subst T'
  have hi : j = i := eq_of_heq hj
  subst i
  congr 1
  have hf := congrArg FramedNode.frame hc
  apply AffineIsometryEquiv.ext
  intro x
  have hx := congrArg (fun e : Iso d => e ((S.placeChild m j).symm x)) hf
  simpa only [FramedNode.child, AffineIsometryEquiv.coe_trans, Function.comp_apply,
    AffineIsometryEquiv.apply_symm_apply] using hx

/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"Its P-slot is consequently PRESENT by Lemma 2.6(a)". Realize the containing
old child, descend to the birth using (I2), and identify the next source
parent by that child's first letter. Then apply the geometric mask theorem. -/
private theorem routing_constant_step2_address_mask
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (hD : Inv D) (N : FramedNode S)
    (A : Parser.AssembledParent D N) (g : Parser.BornFacet P)
    (hg : g.birth ∈ D.geometry.nodes g.height)
    (hbirth : g.birth.IsDescendant g.height N (n + 1))
    (hdepth : n + 1 - g.height < P.k) (hprincipal : P.InPrincipal N (n + 1) g.carrier) :
    packetMask P g.incidence (D.stateAt g.height g.birth hg)
      ⟨n + 1 - g.height, hdepth⟩ := by
  have hle := D.geometry.nodes_height _ _ hg
  obtain ⟨r, hr, w, hw⟩ := hbirth
  have hrpos : 0 < r := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
  have hn : n = g.height + r := by omega
  subst n
  let B := N.child (g.height + r) w.1
  have hB : B ∈ D.geometry.nodes (g.height + r) := by
    change N.child (g.height + r) w.1 ∈ D.geometry.nodes (g.height + r)
    rw [← A.child_eq w.1]
    exact D.geometry.root_mem (A.children w.1).val (A.children w.1).property
  obtain ⟨U, hU, hs⟩ := routing_constant_step2_source_realization
    (D.stateAt (g.height + r) B hB) (D.state_honest _ _)
    B (g.height + r) (hD.node_type_residue _ _ hB).1 (hD.node_type_residue _ _ hB).2
  have hnode : (S.descendantNode B.ty g.height r w.2).move B.frame = g.birth := by
    rw [hw]
    simp [B, SubstSystem.descendantNode, FramedNode.move, FramedNode.child,
      AffineIsometryEquiv.trans_assoc]
  have hdown := routing_constant_step2_source_descent D hD U g.height r B hB hU hs w.2
  dsimp only at hdown
  rw [hnode] at hdown
  obtain ⟨_, hGU, hstate, hanc⟩ := hdown
  let c : U.Node := ⟨g.height + r, ⟨B, hU⟩⟩
  have hrole : U.hierarchy.nodeRole c = ⟨N.ty, w.1⟩ := by
    change (stateOf U P c).address ⟨0, P.k_pos⟩ = _
    rw [hs]
    have h := A.first_letters w.1
    simpa only [firstRole, DecodedLevel.blockState, A.child_eq] using h
  have hparent : (U.hierarchy.parentNode c).2.val = N := by
    have hc := U.hierarchy.child_eq (g.height + r) c.2
    exact routing_constant_step2_parent_from_child (U.hierarchy.parentNode c).2.val N
      (g.height + r) (U.hierarchy.role (g.height + r) c.2) w.1 hrole hc.symm
  let occ : PrimitiveOccurrence U P := {
    birth := ⟨g.height, ⟨g.birth, hGU⟩⟩
    positive := g.positive
    incidence := g.incidence
    parent_type := g.parent_type }
  have hanc' : U.hierarchy.ancestor occ.birth (r + 1) = U.hierarchy.parentNode c := by
    rw [CoherentHierarchy.ancestor, Function.iterate_succ_apply']
    change U.hierarchy.parentNode (U.hierarchy.ancestor occ.birth r) = _
    rw [hanc]
  have hm : mask U P occ ⟨g.height + r + 1 - g.height, hdepth⟩ := by
    change P.InPrincipal (U.hierarchy.ancestor occ.birth _).2.val
      (U.hierarchy.ancestor occ.birth _).1 g.carrier
    dsimp only [Fin.val_mk]
    have he : g.height + r + 1 - g.height = r + 1 := by omega
    rw [he, hanc', hparent]
    exact hprincipal
  have hmask := (packet_mask_fn U P occ ⟨g.height + r + 1 - g.height, hdepth⟩).mp hm
  change packetMask P g.incidence (stateOf U P ⟨g.height, ⟨g.birth, hGU⟩⟩) _ at hmask
  simpa only [hstate] using hmask

/-- Step 2 of the V4 proof of `routing_constant` (V4 8.3):
"If b = n+1, the P-slot is its head, always PRESENT". Below the new parent,
the address mask and honesty give presence; at the new parent use slot zero. -/
private theorem routing_constant_step2_present
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (g : Parser.BornFacet P) (hbirth : g.birth.IsDescendant g.height N (n + 1))
    (hdepth : n + 1 - g.height < P.k) (hprincipal : P.InPrincipal N (n + 1) g.carrier)
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (q : Packet P) (hq : g.packet hl = some q) (hhon : q ∈ honestPackets S P) :
    ∃ s, decode q ⟨n + 1 - g.height, hdepth⟩ = some s := by
  have hle := Parser.descendant_height_le _ _ _ _ hbirth
  by_cases hlt : g.height < n + 1
  · have hg := Parser.assembled_inner_mem D N A g.height g.birth hlt hbirth
    obtain ⟨hi, hh⟩ := routing_constant_step2_old_readout Y hY n hn D hD g hg hl q hq
    have hm : q.mask ⟨n + 1 - g.height, hdepth⟩ := by
      change packetMask P q.incidence q.head _
      rw [hi, hh]
      exact routing_constant_step2_address_mask D hD N A g hg hbirth hdepth hprincipal
    have hj := (honest_packet_admissible P q hhon).2.2.2.1 _ hm
    refine ⟨q.reconstructed ⟨n + 1 - g.height, hdepth⟩, ?_⟩
    unfold decode
    exact if_pos ⟨hj, hm⟩
  · have he : (⟨n + 1 - g.height, hdepth⟩ : Fin P.k) = ⟨0, P.k_pos⟩ := by
      apply Fin.ext
      change n + 1 - g.height = 0
      omega
    exact ⟨q.head, he ▸ (honest_packet_admissible P q hhon).1⟩

/-- Step 3 of the V4 proof of `routing_constant` (V4 8.3):
"Theorem 2.17 and Lemma 3.3 put the ports of both facets into the endpoint
template." For a same-parent link, construct one actual END template and
primitive ports reading the two attached packets. This includes a birth at
the new parent: its children's age-one records come from their first letters.
No equality of packet slots is part of this geometric obligation. -/
private theorem routing_constant_step3_same_parent_ports
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (f f' : PrimitiveFacet S N.ty) (g g' : Parser.BornFacet P)
    (hg : routing_constant_step1_realizes N (n + 1) f g)
    (hg' : routing_constant_step1_realizes N (n + 1) f' g')
    (hlink : SameParentLink f f')
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (hl' : Parser.BoundaryPackets Y (g'.height - 1) g'.leftNode)
    (q q' : Packet P) (hq : g.packet hl = some q) (hq' : g'.packet hl' = some q') :
    ∃ t ∈ Y.tiles, ∃ (slot : EndSlot (compilerLeaf C t)) (T : EndTemplate slot),
      TemplateOccurs C Y (compilerFrame C t) T.configuration ∧ endRow T ∧
        ∃ (a b : PrimitivePort P) (u v : LeafType P),
          a ∈ T.geometry.primitivePorts ∧ b ∈ T.geometry.primitivePorts ∧
          (a.tile, u) ∈ T.configuration.tiles ∧ (b.tile, v) ∈ T.configuration.tiles ∧
          leafPacket u a.facet.val = some q ∧ leafPacket v b.facet.val = some q' := by
  sorry

/-- Step 3 of the V4 proof of `routing_constant` (V4 8.3):
"Row (E4) equates their slots". Once both primitive ports are identified,
E4 gives equality at every common PRESENT index. -/
private theorem routing_constant_step3_same_parent_agree
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (f f' : PrimitiveFacet S N.ty) (g g' : Parser.BornFacet P)
    (hg : routing_constant_step1_realizes N (n + 1) f g)
    (hg' : routing_constant_step1_realizes N (n + 1) f' g')
    (hlink : SameParentLink f f')
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (hl' : Parser.BoundaryPackets Y (g'.height - 1) g'.leftNode)
    (q q' : Packet P) (hq : g.packet hl = some q) (hq' : g'.packet hl' = some q') :
    AgreePresent q q' := by
  obtain ⟨t, ht, slot, T, _, hrow, a, b, u, v, ha, hb, hu, hv, hqu, hqv⟩ :=
    routing_constant_step3_same_parent_ports Y hY n hn D hD N A f f' g g'
      hg hg' hlink hl hl' q q' hq hq'
  obtain ⟨p, hp, _, hagree⟩ := hrow.2.2.2.1 a ha u hu
  have he : p = q := Option.some.inj (hp.symm.trans hqu)
  exact he ▸ hagree b hb v hv q' hqv

/-- Step 4 of the V4 proof of `routing_constant` (V4 8.3):
"start with the age-one record in the child of Q' and restrict down to Q
using (I2) and Proposition 2.3". The actual descendant boundary facet has
the higher birth's incidence and exact age. The strict age-cap hypothesis
excludes saturation, and the strict height inequality excludes age zero.
The higher birth may be the newly assembled parent. -/
private theorem routing_constant_step4_inherited_record
    {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (hD : Inv D) (N : FramedNode S)
    (A : Parser.AssembledParent D N) (b : ℕ) (M : FramedNode S)
    (hM : M ∈ D.geometry.nodes b) (g : Parser.BornFacet P)
    (hbirth : g.birth.IsDescendant g.height N (n + 1))
    (hdesc : M.IsDescendant b g.birth g.height) (hb : b < g.height)
    (e : FacetName S M.ty) (he : M.cell b e.val ⊆ g.carrier)
    (huncapped : g.height - b < P.C) :
    ∃ r : FacetRecord P, stateRecordAt (D.stateAt b M hM) e.val = some r ∧
      r.incidence = g.incidence ∧ r.age.val = g.height - b := by
  sorry

/-- Step 4 of the V4 proof of `routing_constant` (V4 8.3):
"The common-listed vertex and the e-facing port given by Lemma 1.25 belong
to an END template with cone T_q Q". Transport the ascent to the actual
frames and identify a boundary port reading the higher facet's packet in
an END event whose central packet is the lower facet's packet. The named
boundary facet and its recorded cone are retained for applying E3. -/
private theorem routing_constant_step4_ascent_ports
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (f f' : PrimitiveFacet S N.ty) (hf : f.depth < P.k) (hf' : f'.depth < P.k)
    (g g' : Parser.BornFacet P)
    (hg : routing_constant_step1_realizes N (n + 1) f g)
    (hg' : routing_constant_step1_realizes N (n + 1) f' g')
    (hlink : AscentLink P.k f f')
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (hl' : Parser.BoundaryPackets Y (g'.height - 1) g'.leftNode)
    (q q' : Packet P) (hq : g.packet hl = some q) (hq' : g'.packet hl' = some q') :
    g.birth.IsDescendant g.height g'.birth g'.height ∧
      ∃ e : FacetName S g.birth.ty, g.birth.cell g.height e.val ⊆ g'.carrier ∧
        ∃ t ∈ Y.tiles, ∃ (slot : EndSlot (compilerLeaf C t)) (T : EndTemplate slot),
          TemplateOccurs C Y (compilerFrame C t) T.configuration ∧ endRow T ∧
            slot.packet = q ∧
            ∃ (a : BoundaryPort P T.geometry.header.birthType) (u : LeafType P),
              a ∈ T.geometry.boundaryPorts ∧ (a.tile, u) ∈ T.configuration.tiles ∧
              a.parentFacet.val = e.val ∧
              (∃ G, T.geometry.header.boundaryCones a.parentFacet = some G) ∧
              leafPacket u a.facet.val = some q' := by
  sorry

/-- Step 4 of the V4 proof of `routing_constant` (V4 8.3):
"Row (E3) gives P(g)[s] = P(f)[s+delta]". The lower birth is old, so its
packet head is its assigned state. The uncapped record and actual boundary
port identify the GROUP packet, giving the exact height shift. -/
private theorem routing_constant_step4_ascent_agree
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N)
    (f f' : PrimitiveFacet S N.ty) (hf : f.depth < P.k) (hf' : f'.depth < P.k)
    (g g' : Parser.BornFacet P)
    (hg : routing_constant_step1_realizes N (n + 1) f g)
    (hg' : routing_constant_step1_realizes N (n + 1) f' g')
    (hlink : AscentLink P.k f f')
    (hl : Parser.BoundaryPackets Y (g.height - 1) g.leftNode)
    (hl' : Parser.BoundaryPackets Y (g'.height - 1) g'.leftNode)
    (q q' : Packet P) (hq : g.packet hl = some q) (hq' : g'.packet hl' = some q') :
    ShiftedAgree q' q (g'.height - g.height) := by
  have hsum := hg.1
  have hsum' := hg'.1
  have hdepth := hlink.1
  have hh : g.height < g'.height := by omega
  have hold : g.height < n + 1 := by omega
  have huncapped : g'.height - g.height < P.C := by rw [P.C_eq]; omega
  have hbirth := routing_constant_step1_descendant N (n + 1) f g hg
  have hbirth' := routing_constant_step1_descendant N (n + 1) f' g' hg'
  have hM := Parser.assembled_inner_mem D N A g.height g.birth hold hbirth
  obtain ⟨hdesc, e, he, t, ht, slot, T, _, hrow, hslot, a, u, ha, hu, heq, hcone, hport⟩ :=
    routing_constant_step4_ascent_ports Y hY n hn D hD N A f f' hf hf' g g'
      hg hg' hlink hl hl' q q' hq hq'
  obtain ⟨r, hr, _, hage⟩ := routing_constant_step4_inherited_record D hD N A
    g.height g.birth hM g' hbirth' hdesc hh e he huncapped
  have hhead := (routing_constant_step2_old_readout Y hY n hn D hD g hM hl q hq).2
  have hread : stateRecordAt slot.packet.head a.parentFacet.val = some r := by
    rw [hslot, hhead, heq]
    exact hr
  have hgroup := hrow.2.2.1.2 a.parentFacet hcone
  rw [hread] at hgroup
  obtain ⟨p, _, _, _, hports, hshift⟩ := hgroup
  have hp : p = q' := Option.some.inj ((hports a ha rfl u hu).symm.trans hport)
  have hshift' := hshift (by simpa only [hage] using huncapped)
  simpa only [hp, hslot, hage] using hshift'

/-- Step 5 of the V4 proof of `routing_constant` (V4 8.3):
"this finite union of closed sets". Every primitive carrier is a nonempty
compact affine image of its realizing facet cell. -/
private theorem routing_constant_step5_facet_compact {T : S.ι}
    (f : PrimitiveFacet S T) : IsCompact f.carrier ∧ f.carrier.Nonempty := by
  obtain ⟨i, e, he, _⟩ := f.realization
  have hc : IsCompact f.localCarrier := by
    rw [he]
    exact e.val.flat.compact.image (S.child _ i).frame.continuous
  have hn : f.localCarrier.Nonempty := by
    rw [he]
    exact e.val.flat.connected.nonempty.image _
  exact ⟨(hc.image (LinearMap.continuous_of_finiteDimensional
    (S.σ.symm : E d →ₗ[ℝ] E d))).image
      f.birthFrame.toAffineMap.continuous_of_finiteDimensional,
    (hn.image _).image _⟩

/-- Step 5 of the V4 proof of `routing_constant` (V4 8.3):
"a disconnected intersection graph would split this finite union of closed
sets into two disjoint nonempty closed subsets". Values agreeing on
intersections are constant on a preconnected finite union. Nonemptiness of
each member is explicit, so empty members cannot carry arbitrary values. -/
private theorem routing_constant_step5_finite_closed_values
    {X ι V : Type*} [TopologicalSpace X] [Finite ι]
    (K : ι → Set X) (v : ι → V)
    (hc : ∀ i, IsClosed (K i)) (hne : ∀ i, (K i).Nonempty)
    (hconn : IsPreconnected (⋃ i, K i))
    (hlocal : ∀ i j, (K i ∩ K j).Nonempty → v i = v j) (i j : ι) :
    v i = v j := by
  classical
  by_contra hij
  let U : Set X := ⋃ a ∈ {a | v a = v i}, K a
  let W : Set X := ⋃ a ∈ {a | v a ≠ v i}, K a
  have hU : IsClosed U := (Set.toFinite _).isClosed_biUnion (fun a _ => hc a)
  have hW : IsClosed W := (Set.toFinite _).isClosed_biUnion (fun a _ => hc a)
  have hcover : (⋃ a, K a) ⊆ U ∪ W := by
    intro x hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    by_cases hv : v a = v i
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨a, hv, ha⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨a, hv, ha⟩)
  obtain ⟨x, hx⟩ := hne i
  obtain ⟨y, hy⟩ := hne j
  have hi : ((⋃ a, K a) ∩ U).Nonempty :=
    ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩, Set.mem_iUnion₂.mpr ⟨i, rfl, hx⟩⟩
  have hj : ((⋃ a, K a) ∩ W).Nonempty :=
    ⟨y, Set.mem_iUnion.mpr ⟨j, hy⟩,
      Set.mem_iUnion₂.mpr ⟨j, Ne.symm hij, hy⟩⟩
  obtain ⟨z, _, hzU, hzW⟩ :=
    (isPreconnected_closed_iff.mp hconn) U W hU hW hcover hi hj
  obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp hzU
  obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.mp hzW
  exact hb ((hlocal a b ⟨z, hza, hzb⟩).symm.trans ha)

/-- Step 5 of the V4 proof of `routing_constant` (V4 8.3):
"At an intersection point, Lemma 1.25 connects the facets by same-parent
and ascent links." Apply that route at each intersection, then use the
finite closed cover of the selected connected component. -/
private theorem routing_constant_step5_connected_values (T : S.ι) {V : Type*}
    (v : {f : PrimitiveFacet S T // f ∈ P.E_A T} → V)
    (hlink : ∀ f g, RoutingLink P.k f.val g.val → v f = v g)
    (f g : {f : PrimitiveFacet S T // f ∈ P.E_A T}) : v f = v g := by
  classical
  have hmem : ∀ a : PrimitiveFacet S T,
      a ∈ P.E_A T ↔ a ∈ principalFacets S T P.k (P.component T) := by
    intro a
    exact Set.ext_iff.mp (P.E_A_eq T) a
  have hconn : IsPreconnected (P.component T) := by
    obtain ⟨x, hx, he⟩ := P.component_valid T
    rw [he]
    exact isPreconnected_connectedComponentIn
  have hunion : (⋃ a : {f : PrimitiveFacet S T // f ∈ P.E_A T}, a.val.carrier) =
      P.component T := by
    rw [(principalFacets_spec T P.k (P.component T) (P.component_valid T)).2.2]
    ext x
    simp only [Set.mem_iUnion, exists_prop, Subtype.exists]
    exact exists_congr (fun a => and_congr_left (fun _ => hmem a))
  apply routing_constant_step5_finite_closed_values (fun a => a.val.carrier) v
    (fun a => (routing_constant_step5_facet_compact a.val).1.isClosed)
    (fun a => (routing_constant_step5_facet_compact a.val).2)
    (hunion.symm ▸ hconn) ?_ f g
  intro a b hab
  obtain ⟨x, hxa, hxb⟩ := hab
  have route := birth_ascent_routing T P.k (P.component T) (P.component_valid T)
    x a.val b.val ((hmem a.val).mp a.property) ((hmem b.val).mp b.property) hxa hxb
  have H : ∀ c, Relation.ReflTransGen
      (ThroughLink (principalFacets S T P.k (P.component T)) x (RoutingLink P.k))
      a.val c → ∀ hc : c ∈ P.E_A T, v a = v ⟨c, hc⟩ := by
    intro c route
    induction route with
    | refl => intro _; rfl
    | @tail c e _ hce ih =>
      intro he
      have hc := (hmem c).mpr hce.1
      exact (ih hc).trans (hlink ⟨c, hc⟩ ⟨e, he⟩ hce.2.2.2.2)
  exact H b.val route b.property

end RoutingConstant

/-- R9, V4 3.10, replacement V4 8.3: every primitive facet of E_P born
inside P within depth k-1 has its P-slot PRESENT and equal to newState.
The attached packet is honest. First-generation births of P are included,
using R5's second clause without assuming any state of P beforehand. -/
theorem routing_constant (g : Parser.BornFacet P)
    (hbirth : g.birth.IsDescendant g.height N (n + 1))
    (hdepth : n + 1 - g.height < P.k) (hprincipal : P.InPrincipal N (n + 1) g.carrier) :
    ∃ hleft : Parser.BoundaryPackets Y (g.height - 1) g.leftNode,
      ∃ q : Packet P, g.packet hleft = some q ∧ q ∈ honestPackets S P ∧
        decode q ⟨n + 1 - g.height, hdepth⟩ = some (newState Y hY n hn D hD N A) := by
  classical
  let F := {f : PrimitiveFacet S N.ty // f ∈ P.E_A N.ty}
  have hex (f : F) : ∃ (G : Parser.BornFacet P)
      (hl : Parser.BoundaryPackets Y (G.height - 1) G.leftNode)
      (q : Packet P) (s : State P),
      routing_constant_step1_realizes N (n + 1) f.val G ∧
      G.packet hl = some q ∧ q ∈ honestPackets S P ∧
      decode q ⟨f.val.depth, P.principal_depth _ _ f.property⟩ = some s := by
    have hf := P.principal_depth _ _ f.property
    obtain ⟨G, hG⟩ := routing_constant_step1_realize (P := P) N (n + 1) f.val
      (by have := P.K_address; omega)
    have hb := routing_constant_step1_descendant N (n + 1) f.val G hG
    have hd : n + 1 - G.height = f.val.depth := by have := hG.1; omega
    have hdp : n + 1 - G.height < P.k := by omega
    have hp : P.InPrincipal N (n + 1) G.carrier := ⟨f.val, f.property, hG.2.2.symm⟩
    obtain ⟨hl, q, hq, hhon⟩ := routing_constant_step2_attachment Y hY n hn D hD N A G hb
    obtain ⟨s, hs⟩ := routing_constant_step2_present Y hY n hn D hD N A G hb hdp hp hl q hq hhon
    exact ⟨G, hl, q, s, hG, hq, hhon, by simpa only [hd] using hs⟩
  choose G HL Q V HG HQ HH HV using hex
  have hlinks : ∀ (f f' : F), RoutingLink P.k f.val f'.val → V f = V f' := by
    intro f f' hlink
    rcases hlink with hs | ha | ha
    · have h := routing_constant_step3_same_parent_agree Y hY n hn D hD N A
        f.val f'.val (G f) (G f') (HG f) (HG f') hs (HL f) (HL f') (Q f) (Q f')
        (HQ f) (HQ f')
      have hd : f.val.depth = f'.val.depth := congrArg Sigma.fst hs.1
      exact h _ _ _ (HV f) (by simpa only [hd] using HV f')
    · have h := routing_constant_step4_ascent_agree Y hY n hn D hD N A
        f.val f'.val (P.principal_depth _ _ f.property) (P.principal_depth _ _ f'.property)
        (G f) (G f') (HG f) (HG f') ha (HL f) (HL f') (Q f) (Q f') (HQ f) (HQ f')
      have he : f.val.depth = f'.val.depth + ((G f').height - (G f).height) := by
        have := (HG f).1; have := (HG f').1; have := ha.1; omega
      exact (h _ _ _ _ he (HV f') (HV f)).symm
    · have h := routing_constant_step4_ascent_agree Y hY n hn D hD N A
        f'.val f.val (P.principal_depth _ _ f'.property) (P.principal_depth _ _ f.property)
        (G f') (G f) (HG f') (HG f) ha (HL f') (HL f) (Q f') (Q f) (HQ f') (HQ f)
      have he : f'.val.depth = f.val.depth + ((G f).height - (G f').height) := by
        have := (HG f).1; have := (HG f').1; have := ha.1; omega
      exact h _ _ _ _ he (HV f) (HV f')
  let r := Parser.readableFacet Y hY n hn D hD N A (Parser.firstChild N.ty)
  have hrbirth : r.birthFacet.birth.IsDescendant r.birthFacet.height N (n + 1) :=
    Parser.descendant_trans _ _ _ _ _ _ r.inside_child (by
      rw [A.child_eq]
      exact Parser.child_descendant N n _)
  have hrdepth : n + 1 - r.birthFacet.height < P.k := by
    rw [← r.parentSlot_eq]
    exact r.parentSlot.isLt
  obtain ⟨f₀, hf₀, hr⟩ := routing_constant_step1_normalize N (n + 1) r.birthFacet
    hrbirth hrdepth r.parent_principal
  let a₀ : F := ⟨f₀, hf₀⟩
  have hG₀ : G a₀ = r.birthFacet :=
    routing_constant_step1_unique N (n + 1) f₀ (G a₀) r.birthFacet (HG a₀) hr
  have hQ₀ : Q a₀ = r.packet := by
    have hread : r.birthFacet.packet r.constancy = some (Q a₀) := by
      simpa only [hG₀] using HQ a₀
    exact Option.some.inj (hread.symm.trans r.attached)
  have hj₀ : (⟨f₀.depth, P.principal_depth _ _ hf₀⟩ : Fin P.k) = r.parentSlot := by
    apply Fin.ext
    have := hr.1
    have := r.parentSlot_eq
    dsimp only
    omega
  have hV₀ : V a₀ = newState Y hY n hn D hD N A := by
    have h := HV a₀
    change decode (Q a₀) ⟨f₀.depth, _⟩ = some (V a₀) at h
    rw [hQ₀, hj₀] at h
    exact Option.some.inj (h.symm.trans r.parent_decode)
  obtain ⟨f, hf, hg⟩ := routing_constant_step1_normalize N (n + 1) g hbirth hdepth hprincipal
  let a : F := ⟨f, hf⟩
  have hG : G a = g := routing_constant_step1_unique N (n + 1) f (G a) g (HG a) hg
  have hV : V a = newState Y hY n hn D hD N A :=
    (routing_constant_step5_connected_values N.ty V hlinks a a₀).trans hV₀
  subst g
  refine ⟨HL a, Q a, HQ a, HH a, ?_⟩
  have hd : n + 1 - (G a).height = f.depth := by
    have hsum : (G a).height + f.depth = n + 1 := (HG a).1
    omega
  simpa only [hd] using (HV a).trans (congrArg some hV)

/-- R9, V4 3.10: in particular every first-generation primitive facet of P
has head S(P), the entire compressed packet's reconstructed bottom state. -/
theorem first_generation_head (g : Parser.BornFacet P)
    (hheight : g.height = n + 1) (hbirth : g.birth = N)
    (hleft : Parser.BoundaryPackets Y (g.height - 1) g.leftNode) :
    ∃ q : Packet P, g.packet hleft = some q ∧ q ∈ honestPackets S P ∧
      q.head = newState Y hY n hn D hD N A := by
  sorry

/-- R9, V4 3.10: the new parent state belongs to the honest state alphabet. -/
theorem newState_honest : newState Y hY n hn D hD N A ∈ honestStates S P := by
  sorry

/-- R9, V4 3.10: the new state has the assembled parent's actual prototype. -/
theorem newState_type : (newState Y hY n hn D hD N A).ty = N.ty := by
  sorry

/-- R10, V4 3.11: every actual child's old state is the deterministic child
of S(P) at the prescribed globally distinct role (A_P,i). -/
theorem child_equations (i : S.I N.ty) :
    D.blockState (A.children i).val (A.children i).property =
      childMap P (newState Y hY n hn D hD N A) ⟨N.ty, i⟩ := by
  sorry

/-- R9/R10, V4 3.10--3.11, 3.1 (I1): child descent fixes the new height residue. -/
theorem newState_residue :
    (newState Y hY n hn D hD N A).residue.val = (n + 1) % P.L := by
  sorry

/-- R11, V4 3.12(a): every boundary facet of the new parent has one constant
actual native-packet readout. NULL is retained, so this also covers faults. -/
theorem packet_constancy : Parser.BoundaryPackets Y (n + 1) N := by
  sorry

/-- R11, V4 3.12(b): meeting facets related by E in the newly decoded parent
state have equal attached packets. Attachment uses R11(a), and its value is
independent of which proof of constancy was supplied. -/
theorem packet_E_equality (F F' : FacetName S N.ty)
    (hE : stateEAt (newState Y hY n hn D hD N A) F.val F'.val)
    (hmeet : (N.cell (n + 1) F.val ∩ N.cell (n + 1) F'.val).Nonempty)
    (hconst : Parser.BoundaryPackets Y (n + 1) N) :
    attachedPacket hconst F = attachedPacket hconst F' := by
  sorry

/-- R9, V4 3.10: every readable child yields the same parent slot value,
including every choice of facet in its first branching descendant. -/
theorem readable_parent_state (i : S.I N.ty) (r : Parser.ReadableFacet D N A i) :
    r.parentState = newState Y hY n hn D hD N A := by
  sorry

end Forward

namespace Parser

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ}

/-- R12, V4 3.1, induction step: exact nesting of consecutive decoded levels.
Every new root has exactly its prescribed old children; every old root has
one such parent, and all states already assigned below agree literally. -/
structure NestedLevels (D : DecodedLevel Y n) (D' : DecodedLevel Y (n + 1)) : Prop where
  /-- R12, V4 3.1, 3.7: all new roots are unions of their actual prescribed old children. -/
  children : ∀ B' ∈ D'.geometry.blocks, ∀ i : S.I B'.node.ty,
    ∃ B ∈ D.geometry.blocks, B.node = B'.node.child n i
  /-- R12, V4 3.1, 3.7: every old root has exactly one new root as a parent. -/
  parents : ∀ B ∈ D.geometry.blocks, ∃! B' : {B' // B' ∈ D'.geometry.blocks},
    ∃ i : S.I B'.val.node.ty, B.node = B'.val.node.child n i
  /-- R12, V4 3.1: all inner old nodes remain nodes inside the new blocks. -/
  nodes : ∀ m : ℕ, D.geometry.nodes m ⊆ D'.geometry.nodes m
  /-- R12, V4 3.1: all retained states agree, including native leaves and inner nodes. -/
  states : ∀ (m : ℕ) (M : FramedNode S) (hM : M ∈ D.geometry.nodes m)
    (hM' : M ∈ D'.geometry.nodes m), D.stateAt m M hM = D'.stateAt m M hM'

end Parser

/-- R12, V4 3.1 (forward induction step), 3.7--3.12: the proposed geometry
with states defined by 3.9 extends the old decoded level and satisfies all four
invariants. This packages the forward step without imposing its conclusions
as hypotheses on an assembled parent. -/
theorem forward_level (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D) :
    ∃ D' : DecodedLevel Y (n + 1), Inv D' ∧ Parser.NestedLevels D D' ∧
      D'.geometry.roots = Parser.proposedParents D ∧
      ∀ (B' : Block Y (n + 1)) (hB' : B' ∈ D'.geometry.blocks),
        ∃ A : Parser.AssembledParent D B'.node,
          D'.blockState B' hB' = newState Y hY n hn D hD B'.node A := by
  sorry

namespace DecodedLevel

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)

/-- R12, V4 3.1: read the assigned state of a framed root without choosing
a representative block; the geometric top-node equality supplies membership. -/
def rootState (N : FramedNode S) (hN : N ∈ D.geometry.roots) : State P :=
  D.stateAt n N (by rw [D.geometry.nodes_top]; exact hN)

/-- R12, V4 3.1: root-state readout is the original block-state readout. -/
theorem rootState_block (B : Block Y n) (hB : B ∈ D.geometry.blocks) :
    D.rootState B.node ⟨B, hB, rfl⟩ = D.blockState B hB := rfl

end DecodedLevel

namespace Parser

variable (Y : MarkedTiling (systemM S P C))

/-- R12, V4 3.1: realization of one nested sequence as a coherent hierarchy.
The full decoded levels also expose low-height states; their roots are exactly
the hierarchy nodes, and every inner state agrees with the corresponding root
state. Below K the hierarchy is explicitly the certificate subdivision. -/
structure HierarchyRealizes (levels : ∀ n : ℕ, P.K ≤ n → DecodedLevel Y n)
    (H : CoherentHierarchy S (Y.project (nativeDecoration S P C))) where
  /-- R12, V4 3.1: every level in the induction sequence has Inv(n). -/
  invariant : ∀ n hn, Inv (levels n hn)
  /-- R12, V4 3.1: the one-step nesting retains all previously assigned states. -/
  nested : ∀ n hn, NestedLevels (levels n hn)
    (levels (n + 1) (Nat.le_trans hn (Nat.le_succ n)))
  /-- R12, V4 3.1, 3.2: the initial level is the actual forced certificate base. -/
  base : CertificateBase (levels P.K le_rfl)
  /-- R12, V4 3.1: decoded families at every height, including heights less than K. -/
  fullLevels : ∀ n : ℕ, DecodedLevel Y n
  /-- R12, V4 3.1: the four invariant clauses hold at every height. -/
  full_invariant : ∀ n : ℕ, Inv (fullLevels n)
  /-- R12, V4 3.1: the high full levels are the very same induction sequence. -/
  upper_eq : ∀ n hn, fullLevels n = levels n hn
  /-- R12, V4 3.1: roots, including their frames, are exactly the hierarchy nodes. -/
  roots : ∀ n, (fullLevels n).geometry.roots = H.nodes n
  /-- R12, V4 3.1: every lower full level is exactly the inner subdivision of a higher one. -/
  inner_nodes : ∀ n m : ℕ, m ≤ n → (fullLevels n).geometry.nodes m = H.nodes m
  /-- R12, V4 3.1: low levels are the nodes inside the actual K-certificate blocks. -/
  below_K : ∀ n : ℕ, n < P.K → H.nodes n = (levels P.K le_rfl).geometry.nodes n
  /-- R12, V4 3.1: state assignments agree at every shared inner node. -/
  states : ∀ (n m : ℕ) (N : FramedNode S)
    (hn : N ∈ (fullLevels n).geometry.nodes m)
    (hm : N ∈ (fullLevels m).geometry.nodes m),
      (fullLevels n).stateAt m N hn = (fullLevels m).stateAt m N hm
  /-- R12, V4 3.1, §3.2: parents at and above K are exactly the proposed parents. -/
  parents : ∀ (n : ℕ) (hn : P.K ≤ n) (B : Block Y n)
    (hB : B ∈ (levels n hn).geometry.blocks) (hN : B.node ∈ H.nodes n),
      (H.parent n ⟨B.node, hN⟩).val = proposedParent (levels n hn) B hB
  /-- R12, V4 3.1 (I2): each root's first address letter is its actual hierarchy role. -/
  roles : ∀ q : H.Node,
    ((fullLevels q.1).rootState q.2.val (by rw [roots]; exact q.2.property)).address
      ⟨0, P.k_pos⟩ = H.nodeRole q

namespace HierarchyRealizes

variable {Y} {levels : ∀ n : ℕ, P.K ≤ n → DecodedLevel Y n}
variable {H : CoherentHierarchy S (Y.project (nativeDecoration S P C))}
variable (R : HierarchyRealizes Y levels H)

/-- R12, V4 3.1: the single state assigned to each actual hierarchy node,
read from its full decoded level and using the exact root correspondence. -/
def state (q : H.Node) : State P :=
  (R.fullLevels q.1).rootState q.2.val (by rw [R.roots]; exact q.2.property)

/-- R12, V4 3.1: every assigned hierarchy state is honest. -/
theorem state_honest (q : H.Node) : R.state q ∈ honestStates S P :=
  (R.fullLevels q.1).state_honest q.1 _

/-- R12, V4 3.1: every assigned hierarchy state has the node type and height residue. -/
theorem state_type_residue (q : H.Node) :
    (R.state q).ty = q.2.val.ty ∧ (R.state q).residue.val = q.1 % P.L := by
  sorry

/-- R12, V4 3.1: the hierarchy state is the existing inner state in every
decoded level containing that framed node, not an independent marginal choice. -/
theorem state_agrees (n m : ℕ) (N : FramedNode S)
    (hN : N ∈ (R.fullLevels n).geometry.nodes m) (hm : N ∈ H.nodes m) :
    (R.fullLevels n).stateAt m N hN = R.state ⟨m, ⟨N, hm⟩⟩ := by
  sorry

/-- R12, V4 3.1: the global state assignment obeys every actual child equation. -/
theorem state_child (q : H.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (hc : q.2.val.child (q.1 - 1) i ∈ H.nodes (q.1 - 1)) :
    R.state ⟨q.1 - 1, ⟨q.2.val.child (q.1 - 1) i, hc⟩⟩ =
      childMap P (R.state q) ⟨q.2.val.ty, i⟩ := by
  sorry

/-- R12, V4 3.1: ground hierarchy states are the actual output leaf states. -/
theorem state_ground (q : H.Node) (hq : q.1 = 0)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (heq : tileNode t = q.2.val) : R.state q = (compilerLeaf C t).prePattern.state := by
  sorry

/-- R12, V4 3.1: the assigned state's first role is the actual parent role. -/
theorem state_role (q : H.Node) : (R.state q).address ⟨0, P.k_pos⟩ = H.nodeRole q :=
  R.roles q

/-- R12, V4 3.1 (I5): every hierarchy node, at every height, has constant
side packets and E-equality on meeting boundary facets. -/
theorem boundary_invariant (q : H.Node) :
    ∃ h : BoundaryPackets Y q.1 q.2.val, ∀ F F' : FacetName S q.2.val.ty,
      stateEAt (R.state q) F.val F'.val →
      (q.2.val.cell q.1 F.val ∩ q.2.val.cell q.1 F'.val).Nonempty →
        attachedPacket h F = attachedPacket h F' := by
  sorry

/-- R12, V4 3.1 (I4): the global assignment satisfies the principal PRESENT-slot
invariant at every height, including all certificate-subdivision nodes below K. -/
theorem principal_invariant (q : H.Node) (g : BornFacet P)
    (hbirth : g.birth.IsDescendant g.height q.2.val q.1)
    (hdepth : q.1 - g.height < P.k) (hprincipal : P.InPrincipal q.2.val q.1 g.carrier) :
    ∃ hleft : BoundaryPackets Y (g.height - 1) g.leftNode, ∃ p : Packet P,
      g.packet hleft = some p ∧
        decode p ⟨q.1 - g.height, hdepth⟩ = some (R.state q) := by
  sorry

end HierarchyRealizes

end Parser

/-- R12, V4 3.1: one nested sequence of decoded levels exists for all n ≥ K,
with Inv(n) and agreeing inner states, and realizes a coherent hierarchy on the
exact native projection of the arbitrary proper output Y. At heights below K,
the nodes and their states come from the forced honest K-certificates.
The existential witnesses are correlated through HierarchyRealizes; they do not
assert independent existence at each height or source-species membership of Y.
An actual M-proper Y supplies the base, so no species nonemptiness is assumed. -/
theorem all_height_hierarchy (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    ∃ levels : ∀ n : ℕ, P.K ≤ n → DecodedLevel Y n,
      ∃ H : CoherentHierarchy S (Y.project (nativeDecoration S P C)),
        Nonempty (Parser.HierarchyRealizes Y levels H) := by
  sorry

/-- R12, V4 3.1: the chosen correlated induction sequence, from the single
all-height existence theorem. Definitions contain no proof holes. -/
def parsedLevels (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    ∀ n : ℕ, P.K ≤ n → DecodedLevel Y n :=
  Classical.choose (all_height_hierarchy Y hY)

/-- R12, V4 3.1: the parsed coherent hierarchy, chosen from all_height_hierarchy
after fixing that theorem's one sequence of decoded levels. Its low levels are
the actual K-block inner nodes, by parsedHierarchy_below_K. -/
def parsedHierarchy (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    CoherentHierarchy S (Y.project (nativeDecoration S P C)) :=
  Classical.choose (Classical.choose_spec (all_height_hierarchy Y hY))

/-- R12, V4 3.1: the realization data for those very same levels and hierarchy.
The final nonempty witness retains all state assignments and their agreements. -/
def parsedRealization (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    Parser.HierarchyRealizes Y (parsedLevels Y hY) (parsedHierarchy Y hY) :=
  Classical.choice (Classical.choose_spec
    (Classical.choose_spec (all_height_hierarchy Y hY)))

/-- R12, V4 3.1: the decoded level at any height in the chosen realization,
including heights below K. Its state table is part of the one parsed hierarchy. -/
def parsedDecodedLevel (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) : DecodedLevel Y n := (parsedRealization Y hY).fullLevels n

/-- R12, V4 3.1: the assigned state of an actual node of the parsed hierarchy. -/
def parsedState (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) : State P := (parsedRealization Y hY).state q

/-- R12, V4 3.1: every chosen high decoded level satisfies Inv(n). -/
theorem parsedLevels_invariant (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) : Inv (parsedLevels Y hY n hn) :=
  (parsedRealization Y hY).invariant n hn

/-- R12, V4 3.1: consecutive chosen levels are nested and their states agree. -/
theorem parsedLevels_nested (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) :
    Parser.NestedLevels (parsedLevels Y hY n hn)
      (parsedLevels Y hY (n + 1) (Nat.le_trans hn (Nat.le_succ n))) :=
  (parsedRealization Y hY).nested n hn

/-- R12, V4 3.1: all four invariants hold for decoded levels at every height. -/
theorem parsedHierarchy_invariant (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) : Inv (parsedDecodedLevel Y hY n) :=
  (parsedRealization Y hY).full_invariant n

/-- R12, V4 3.1: high decoded levels are literally the induction witnesses. -/
theorem parsedDecodedLevel_upper (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) : parsedDecodedLevel Y hY n = parsedLevels Y hY n hn :=
  (parsedRealization Y hY).upper_eq n hn

/-- R12, V4 3.1: the full decoded roots are exactly the parsed framed nodes. -/
theorem parsedHierarchy_nodes (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) : (parsedDecodedLevel Y hY n).geometry.roots = (parsedHierarchy Y hY).nodes n :=
  (parsedRealization Y hY).roots n

/-- R12, V4 3.1: at n < K, the parsed nodes are exactly the inner nodes of
the K-certificate base; no fresh low-height subdivision is chosen. -/
theorem parsedHierarchy_below_K (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : n < P.K) :
    (parsedHierarchy Y hY).nodes n = (parsedLevels Y hY P.K le_rfl).geometry.nodes n :=
  (parsedRealization Y hY).below_K n hn

/-- R12, V4 3.1, 3.2: the chosen base is precisely the compiler certificate family,
and its entire table agrees with every certificate's honest inner-node table. -/
theorem parsedHierarchy_base (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    Parser.CertificateBase (parsedLevels Y hY P.K le_rfl) :=
  (parsedRealization Y hY).base

/-- R12, V4 3.1: every actual parsed state is honest with the correct type and residue. -/
theorem parsedState_type_residue (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) :
    parsedState Y hY q ∈ honestStates S P ∧ (parsedState Y hY q).ty = q.2.val.ty ∧
      (parsedState Y hY q).residue.val = q.1 % P.L :=
  ⟨(parsedRealization Y hY).state_honest q, (parsedRealization Y hY).state_type_residue q⟩

/-- R12, V4 3.1: the parsed state's first role agrees with the actual parent. -/
theorem parsedState_role (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) :
    (parsedState Y hY q).address ⟨0, P.k_pos⟩ = (parsedHierarchy Y hY).nodeRole q :=
  (parsedRealization Y hY).state_role q

/-- R12, V4 3.1: all actual parent-child state equations hold in the parsed hierarchy. -/
theorem parsedState_child (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (hc : q.2.val.child (q.1 - 1) i ∈ (parsedHierarchy Y hY).nodes (q.1 - 1)) :
    parsedState Y hY ⟨q.1 - 1, ⟨q.2.val.child (q.1 - 1) i, hc⟩⟩ =
      childMap P (parsedState Y hY q) ⟨q.2.val.ty, i⟩ :=
  (parsedRealization Y hY).state_child q hq i hc

/-- R12, V4 3.1 (I5): parsed hierarchy boundary attachment is available at
every height, with equality on meeting E-related facets and NULL retained. -/
theorem parsedState_boundary (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) :
    ∃ h : Parser.BoundaryPackets Y q.1 q.2.val, ∀ F F' : FacetName S q.2.val.ty,
      stateEAt (parsedState Y hY q) F.val F'.val →
      (q.2.val.cell q.1 F.val ∩ q.2.val.cell q.1 F'.val).Nonempty →
        attachedPacket h F = attachedPacket h F' :=
  (parsedRealization Y hY).boundary_invariant q

/-- R12, V4 3.1: all inner nodes of a chosen higher level give exactly the
corresponding lower hierarchy level, including the actual framed ground tiles. -/
theorem parsedHierarchy_inner_nodes (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n m : ℕ) (hmn : m ≤ n) :
    (parsedDecodedLevel Y hY n).geometry.nodes m = (parsedHierarchy Y hY).nodes m :=
  (parsedRealization Y hY).inner_nodes n m hmn

/-- R12, V4 3.1: the global state agrees with every containing decoded table.
Thus passing to a higher block never reassigns an earlier inner node's state. -/
theorem parsedState_agrees (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n m : ℕ) (N : FramedNode S)
    (hN : N ∈ (parsedDecodedLevel Y hY n).geometry.nodes m)
    (hm : N ∈ (parsedHierarchy Y hY).nodes m) :
    (parsedDecodedLevel Y hY n).stateAt m N hN = parsedState Y hY ⟨m, ⟨N, hm⟩⟩ :=
  (parsedRealization Y hY).state_agrees n m N hN hm

/-- R12, V4 3.1 (I2): parsed height-zero states are the physical tiles'
pre-pattern states, with the leaf type and frame decoded from the actual marking. -/
theorem parsedState_ground (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : q.1 = 0)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (heq : tileNode t = q.2.val) : parsedState Y hY q = (compilerLeaf C t).prePattern.state :=
  (parsedRealization Y hY).state_ground q hq t ht heq

/-- R12, V4 3.1 (I4): every principal primitive facet born inside a parsed
node has that node's actual state in its PRESENT slot, at every height. -/
theorem parsedState_principal (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (g : Parser.BornFacet P)
    (hbirth : g.birth.IsDescendant g.height q.2.val q.1)
    (hdepth : q.1 - g.height < P.k) (hprincipal : P.InPrincipal q.2.val q.1 g.carrier) :
    ∃ hleft : Parser.BoundaryPackets Y (g.height - 1) g.leftNode, ∃ p : Packet P,
      g.packet hleft = some p ∧
        decode p ⟨q.1 - g.height, hdepth⟩ = some (parsedState Y hY q) :=
  (parsedRealization Y hY).principal_invariant q g hbirth hdepth hprincipal

/-- R12/R13, V4 3.1, 3.13: every letter in the assigned upward address is
the actual globally distinct role of the indicated hierarchy ancestor. -/
theorem parsedState_address (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (j : Fin P.k) :
    (parsedState Y hY q).address j =
      (parsedHierarchy Y hY).nodeRole ((parsedHierarchy Y hY).ancestor q j.val) := by
  sorry

/-- R12, V4 3.1, §3.2: the actual high-level parent is the proposed parent
computed from the old block's first address letter, with the exact full frame. -/
theorem parsedLevels_parent (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (B : Block Y n)
    (hB : B ∈ (parsedLevels Y hY n hn).geometry.blocks)
    (hN : B.node ∈ (parsedHierarchy Y hY).nodes n) :
    ((parsedHierarchy Y hY).parent n ⟨B.node, hN⟩).val =
      proposedParent (parsedLevels Y hY n hn) B hB :=
  (parsedRealization Y hY).parents n hn B hB hN

/-- R12, V4 3.1 (I5): the constancy proof supplied by the single parsed state
assignment. This selects a proof, not a packet or an additional source witness. -/
def parsedBoundaryPackets (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) : Parser.BoundaryPackets Y q.1 q.2.val :=
  (parsedState_boundary Y hY q).choose

/-- R12, V4 3.1 (I5): the packet attached to a boundary facet from one parsed
node, read from the actual tile pre-patterns. Its value may be NULL or a packet;
persistent faults are subject only to constancy and E-equality. -/
def parsedFacetPacket (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (F : FacetName S q.2.val.ty) : Option (Packet P) :=
  attachedPacket (parsedBoundaryPackets Y hY q) F

/-- R12, V4 3.1 (I5): parsed attachment has the defining actual leaf-readout property. -/
theorem parsedFacetPacket_spec (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (F : FacetName S q.2.val.ty) :
    Parser.ConstantPacket Y q.1 q.2.val F (parsedFacetPacket Y hY q F) :=
  attachedPacket_spec (parsedBoundaryPackets Y hY q) F

/-- R12, V4 3.1 (I5): meeting E-related parsed facets carry exactly equal packets. -/
theorem parsedFacetPacket_E (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (F F' : FacetName S q.2.val.ty)
    (hE : stateEAt (parsedState Y hY q) F.val F'.val)
    (hmeet : (q.2.val.cell q.1 F.val ∩ q.2.val.cell q.1 F'.val).Nonempty) :
    parsedFacetPacket Y hY q F = parsedFacetPacket Y hY q F' :=
  (parsedState_boundary Y hY q).choose_spec F F' hE hmeet

/-- R12, V4 3.1 (I5): every non-NULL parsed boundary packet belongs to the
honest packet alphabet, even when its facet is a persistent fault of Y. This
asserts admissibility of the readout, not actuality of its claimed provider. -/
theorem parsedFacetPacket_honest (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (F : FacetName S q.2.val.ty) (p : Packet P)
    (hp : parsedFacetPacket Y hY q F = some p) : p ∈ honestPackets S P := by
  sorry

/-- R12, V4 3.1 (I5): a boundary track retains the same attached packet in
every descendant facet piece. The assertion includes NULL and phantom packets. -/
theorem parsedFacetPacket_inherited (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q c : (parsedHierarchy Y hY).Node)
    (hdesc : c.2.val.IsDescendant c.1 q.2.val q.1)
    (F : FacetName S q.2.val.ty) (f : FacetName S c.2.val.ty)
    (hsub : c.2.val.cell c.1 f.val ⊆ q.2.val.cell q.1 F.val) :
    parsedFacetPacket Y hY q F = parsedFacetPacket Y hY c f := by
  sorry

namespace Parser.BornFacet

/-- R13, V4 3.13: the actual birth node of a primitive facet in a specified
coherent hierarchy. Membership is explicit; no source hierarchy is assumed. -/
def hierarchyBirth {Y : MarkedTiling (systemM S P C)}
    (H : CoherentHierarchy S (Y.project (nativeDecoration S P C)))
    (g : Parser.BornFacet P) (hg : g.birth ∈ H.nodes g.height) : H.Node :=
  ⟨g.height, ⟨g.birth, hg⟩⟩

end Parser.BornFacet

/-- R13, V4 3.13: the primitive packet in the parsed output, initially read
from the canonical left child. Its two-sided and non-NULL calibration is W4.
This definition uses (I5) on the actual left hierarchy node and makes no new
choice of a state, source occurrence or provider. -/
def parsedPrimitivePacket (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Parser.BornFacet P) (hg : g.birth ∈ (parsedHierarchy Y hY).nodes g.height) :
    Option (Packet P) :=
  parsedFacetPacket Y hY ⟨g.height - 1, ⟨g.leftNode, g.left_mem (parsedHierarchy Y hY) hg⟩⟩
    g.incidence.val.leftFacet

/-- R13, V4 3.13 (W4): for every actual finite primitive birth in the parsed
hierarchy, the attached packet is two-sided, honest and has that birth's state
as head. At each index 0 ≤ j ≤ k-1 its mask is PRESENT exactly when its carrier
belongs to the actual ancestor's E-set, and every PRESENT slot is the state
assigned to that ancestor by Theorem 3.1. Persistent faults are not finite births
and receive no additional provider or NULL assertion here (Remark 3.14). -/
theorem calibration_W4 (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Parser.BornFacet P) (hg : g.birth ∈ (parsedHierarchy Y hY).nodes g.height) :
    ∃ hleft : Parser.BoundaryPackets Y (g.height - 1) g.leftNode,
      ∃ hright : Parser.BoundaryPackets Y (g.height - 1) g.rightNode,
        attachedPacket hleft g.incidence.val.leftFacet =
          attachedPacket hright g.incidence.val.rightFacet ∧
        ∃ q : Packet P, g.packet hleft = some q ∧ q ∈ honestPackets S P ∧
          q.incidence = g.incidence ∧
          q.head = parsedState Y hY (g.hierarchyBirth (parsedHierarchy Y hY) hg) ∧
          ∀ j : Fin P.k,
            let ancestor := (parsedHierarchy Y hY).ancestor
              (g.hierarchyBirth (parsedHierarchy Y hY) hg) j.val
            (q.mask j ↔ P.InPrincipal ancestor.2.val ancestor.1 g.carrier) ∧
              (q.mask j → decode q j = some (parsedState Y hY ancestor)) := by
  sorry

/-- R13, V4 3.13: every finite primitive birth has a non-NULL honest attached
packet of its actual incidence, and the canonical left/right readouts are equal. -/
theorem parsedPrimitivePacket_spec (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Parser.BornFacet P) (hg : g.birth ∈ (parsedHierarchy Y hY).nodes g.height) :
    parsedPrimitivePacket Y hY g hg =
      parsedFacetPacket Y hY
        ⟨g.height - 1, ⟨g.rightNode, g.right_mem (parsedHierarchy Y hY) hg⟩⟩
        g.incidence.val.rightFacet ∧
      ∃ p : Packet P, parsedPrimitivePacket Y hY g hg = some p ∧
        p ∈ honestPackets S P ∧ p.incidence = g.incidence := by
  sorry

/-- R13, V4 3.13: W4 for a specified actual packet readout. Its complete mask
and every PRESENT slot refer to the actual ancestors and their assigned states. -/
theorem calibration_W4_readout (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Parser.BornFacet P) (hg : g.birth ∈ (parsedHierarchy Y hY).nodes g.height)
    (p : Packet P) (hp : parsedPrimitivePacket Y hY g hg = some p) (j : Fin P.k) :
    let ancestor := (parsedHierarchy Y hY).ancestor
      (g.hierarchyBirth (parsedHierarchy Y hY) hg) j.val
    (p.mask j ↔ P.InPrincipal ancestor.2.val ancestor.1 g.carrier) ∧
      (p.mask j → decode p j = some (parsedState Y hY ancestor)) := by
  sorry

/-- R13, V4 3.13: slots outside the actual principal set are ABSENT, as
required by the one-state packet decoder; this is the other direction of W4. -/
theorem calibration_W4_absent (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Parser.BornFacet P) (hg : g.birth ∈ (parsedHierarchy Y hY).nodes g.height)
    (p : Packet P) (hp : parsedPrimitivePacket Y hY g hg = some p) (j : Fin P.k)
    (habsent : ¬ P.InPrincipal
      ((parsedHierarchy Y hY).ancestor (g.hierarchyBirth (parsedHierarchy Y hY) hg) j.val).2.val
      ((parsedHierarchy Y hY).ancestor (g.hierarchyBirth (parsedHierarchy Y hY) hg) j.val).1
      g.carrier) : decode p j = none := by
  sorry

end Enforce
