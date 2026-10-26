import Enforce.Parser.Invariant

/-!
# END coverage, two-sided packets, and the reverse host step

R4--R6, V4 3.3, 3.4 and 3.6. The output Y is arbitrary and M-proper.
The full counter strand remains part of the general anisotropic host theorem.
The N = M choice from V4 8.3 is already part of Params.

Primitive attachments are the original leaf pre-pattern packets. The second
two-sided statement applies before a new parent has any assigned state.
The open opposite half-ball uses the negative interior tangent cone of the
known block at a relative-interior facet point; this is the geometric j-side
by V4 1.0(a), without choosing a global normal or an orientation.

The explicit scalar/equal-edge predicates at the end record the extra geometric
hypotheses of the optional R6s milestone. A reduced counter-free compiler is not
identified with the existing full compiler; see the S5 report's not-done entry.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d} {P : Params S}
variable {C : ClusterData S P}

namespace Parser

/-- R4, V4 3.3: a tile has interior points of the recorded open sector
arbitrarily close to its apex. The event point itself need not be interior. -/
def ApproachesSector (t : PlacedMarkedTile (systemM S P C))
    (v : E d) (G : Set (E d)) : Prop :=
  ∀ ε : ℝ, 0 < ε → (interior t.carrier ∩ interior G ∩ ball v ε).Nonempty

end Parser

/-- R4, V4 3.3: every tile approaching an END sector belongs to the actual
allowed template, lists its event vertex, and carries the template's END row.
The template is the one supplied by Theorem 2.17(b), with its exact leaf labels
and frames; its geometry fixes the position in which the row is read. -/
theorem trigger_coverage (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (j : EndSlot (compilerLeaf C t)) (θ : Template P)
    (hθ : θ ∈ allowedTemplates (.end_ j))
    (hactual : TemplateOccurs C Y (compilerFrame C t) θ)
    (u : PlacedMarkedTile (systemM S P C)) (hu : u ∈ Y.tiles)
    (hnear : Parser.ApproachesSector u (Compiler.endVertex (compilerFrame C t) j)
      (Compiler.endSector (compilerFrame C t) j)) :
    (∃ z ∈ θ.tiles, u = placedLeaf C z.2 (z.1.frame.trans (compilerFrame C t))) ∧
      (tileNode u).Lists 0 (Compiler.endVertex (compilerFrame C t) j) ∧
      ∃ T : EndTemplate j, T.configuration = θ ∧ endRow T := by
  sorry

/-- R5, V4 3.4 (first clause): at a primitive birth inside any decoded block,
the two child-side constant packets coincide. They are non-NULL, honest, have
the prescribed incidence, and their head slot is the birth node's assigned state.
The inclusion premise covers every inner birth, including heights below K. -/
theorem two_sided_constancy (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (g : Parser.BornFacet P) (hg : g.birth ∈ D.geometry.nodes g.height) :
    ∃ hleft : Parser.BoundaryPackets Y (g.height - 1) g.leftNode,
      ∃ hright : Parser.BoundaryPackets Y (g.height - 1) g.rightNode,
        attachedPacket hleft g.incidence.val.leftFacet =
          attachedPacket hright g.incidence.val.rightFacet ∧
        ∃ q : Packet P, q ∈ honestPackets S P ∧ q.incidence = g.incidence ∧
          g.packet hleft = some q ∧
          decode q ⟨0, P.k_pos⟩ = some (D.stateAt g.height g.birth hg) ∧
          q.head = D.stateAt g.height g.birth hg := by
  sorry

/-- R5, V4 3.4 (second clause): the same equality holds for a placed parent
whose prescribed children are level-n blocks with the correct first address
letters. No state, honesty assumption on a parent state, or new invariant for
that parent is required. An actual assembled subdivision supplies both sides. -/
theorem two_sided_constancy_assembled (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (N : FramedNode S) (A : Parser.AssembledParent D N) (g : Parser.BornFacet P)
    (hheight : g.height = n + 1) (hbirth : g.birth = N) :
    ∃ hleft : Parser.BoundaryPackets Y (g.height - 1) g.leftNode,
      ∃ hright : Parser.BoundaryPackets Y (g.height - 1) g.rightNode,
        attachedPacket hleft g.incidence.val.leftFacet =
          attachedPacket hright g.incidence.val.rightFacet ∧
        ∃ q : Packet P, q ∈ honestPackets S P ∧ q.incidence = g.incidence ∧
          g.packet hleft = some q := by
  sorry

namespace Parser

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ}

/-- R5, V4 3.4: once the birth belongs to the old decoded family, the packet
is independent of which proof of side constancy is used. -/
theorem primitive_packet_honest (hY : MProper Y) (hn : P.K ≤ n)
    (D : DecodedLevel Y n) (hD : Inv D) (g : BornFacet P)
    (hg : g.birth ∈ D.geometry.nodes g.height)
    (hleft : BoundaryPackets Y (g.height - 1) g.leftNode) :
    ∃ q : Packet P, g.packet hleft = some q ∧
      q ∈ honestPackets S P ∧ q.incidence = g.incidence := by
  sorry

/-- R6, V4 3.6: the open half-ball opposite the known block at x.
At a relative-interior facet point, tangentCone is the closed inward half-space;
negating its interior gives precisely the open j-side. No normal is chosen. -/
def oppositeHalfBall (B : FramedNode S) (n : ℕ) (x : E d) (r : ℝ) : Set (E d) :=
  ball x r ∩ {y | -(y - x) ∈ interior (tangentCone (B.carrier n) x)}

/-- R6, V4 3.6, 1.0(a): opposite half-balls at relative-interior facet points
are genuine nonempty open half-balls with the facet as wall, at sufficiently
small radii. This provides a nonvacuous meaning of the j-side tile assertion. -/
theorem oppositeHalfBall_geometry (B : FramedNode S) (n : ℕ)
    (f : FacetName S B.ty) (x : E d) (hx : x ∈ relint (B.cell n f.val)) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : E d, ‖v‖ = 1 ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ r →
        oppositeHalfBall B n x ε = ball x ε ∩ {y | inner ℝ v (y - x) < 0}) ∧
      B.carrier n ∩ ball x r = ball x r ∩ {y | 0 ≤ inner ℝ v (y - x)} := by
  sorry

/-- R6, V4 3.6: all actual j-side tiles near every point of the relative-open
facet belong to one specified block. The half-balls themselves are inside its
interior, and every meeting actual tile is contained in its closed support. -/
def HostsAcross (B : Block Y n) (f : FacetName S B.node.ty) (B' : Block Y n) : Prop :=
  ∀ x ∈ relint (B.node.cell n f.val), ∃ r : ℝ, 0 < r ∧
    oppositeHalfBall B.node n x r ⊆ interior B'.carrier ∧
    ∀ t ∈ Y.tiles,
      (interior t.carrier ∩ oppositeHalfBall B.node n x r).Nonempty →
        t.carrier ⊆ B'.carrier

/-- R6, V4 3.6: the complete host conclusion, including the exact framed
sibling, first address letter, age-one incidence, named opposite facet and side.
The existential is a block of the chosen level, not a fresh geometric candidate. -/
def HostConclusion (D : DecodedLevel Y n) (B : Block Y n)
    (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : AgeOneFacet D B hB f) : Prop :=
  ∃ B' : Block Y n, ∃ hB' : B' ∈ D.geometry.blocks,
    B'.node = proposedSibling D B hB f a ∧
    firstRole D B' hB' = a.record.incidence.val.sideRole (!a.record.sideIndex) ∧
    (∃ r' : FacetRecord P,
      stateRecordAt (D.blockState B' hB')
        (a.record.incidence.val.sideFacet (!a.record.sideIndex)).val = some r' ∧
      AgeOneRecord (D.blockState B' hB') r' ∧
      r'.incidence = a.record.incidence ∧
      r'.side = a.record.incidence.val.sideRole (!a.record.sideIndex)) ∧
    HostsAcross B f B'

end Parser

/-- R6, V4 3.6: the general reverse host step, retaining the counter strand.
All j-side tiles sufficiently near relint f belong to one existing level-n block,
which is the proposed sibling with its prescribed type and full frame. Its
first address role and opposite-facet record are exactly the age-one data.
No scalar expansion or equal-edge hypothesis is imposed. -/
theorem host_step (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) : Parser.HostConclusion D B hB f a := by
  sorry

namespace Parser

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ}

/-- R6, V4 3.6: two chosen blocks realizing the proposed framed sibling coincide.
This records uniqueness in the chosen family, including type and frame. -/
theorem host_unique (D : DecodedLevel Y n) (B : Block Y n)
    (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : AgeOneFacet D B hB f) (B' B'' : Block Y n)
    (h' : B'.node = proposedSibling D B hB f a)
    (h'' : B''.node = proposedSibling D B hB f a) : B' = B'' := by
  apply Block.ext
  exact h'.trans h''.symm

/-- R6/R7, V4 3.6--3.7: the hosted sibling proposes the same framed parent.
This is the frame-coherence input for the connected dual-graph assembly. -/
theorem host_parent_eq (hY : MProper Y) (hn : P.K ≤ n) (D : DecodedLevel Y n)
    (hD : Inv D) (B : Block Y n) (hB : B ∈ D.geometry.blocks)
    (f : FacetName S B.node.ty) (a : AgeOneFacet D B hB f)
    (B' : Block Y n) (hB' : B' ∈ D.geometry.blocks)
    (hsibling : B'.node = proposedSibling D B hB f a)
    (hrole : firstRole D B' hB' = a.record.incidence.val.sideRole (!a.record.sideIndex)) :
    proposedParent D B' hB' = proposedParent D B hB := by
  sorry

end Parser

/-- R6s, V4 8.4, OPTIONAL MILESTONE: the explicit scalar expansion hypothesis.
The quantifier is over the actual linear map; s must be strictly greater than one. -/
def ScalarExpansion (S : SubstSystem d) : Prop :=
  ∃ s : ℝ, 1 < s ∧ ∀ x : E d, S.σ x = s • x

/-- R6s, V4 8.4, OPTIONAL MILESTONE: every listed one-cell in every prototype
has one common positive length. This concerns the specified complexes, including
flat subdivided edges, rather than only the maximal geometric edges. -/
def EqualListedEdgeLengths (S : SubstSystem d) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ e : EdgeName S, diam e.2.val.carrier = a

end Enforce
