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
  sorry

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
