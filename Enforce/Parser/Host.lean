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

open scoped BigOperators

/-- The record and the full oriented chain of one strand port or root edge. -/
private def host_step_Chain (P : Params S) :=
  Σ r : FacetRecord P, OrientedChain r.facet

/-- The listed edge at the bottom of a full chain. -/
private def host_step_edge (z : host_step_Chain P) : PrototypeEdge S z.1.ty :=
  ⟨(z.2.chain.val.cell edgeIndex).val, by
    classical
    simp only [CellComplex.edges, Finset.mem_filter]
    exact ⟨(z.2.chain.val.cell edgeIndex).property, z.2.chain.val.dimension edgeIndex⟩⟩

/-- A native strand port retains its physical tile and its full chain.
Different ports are allowed to have the same physical tile. -/
private def host_step_Port (C : ClusterData S P) :=
  PlacedMarkedTile (systemM S P C) × host_step_Chain P

/-- A root port retains membership in the chosen decoded level. -/
private def host_step_Root {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) :=
  {B : Block Y n // B ∈ D.geometry.blocks} × host_step_Chain P

/-- The canonical left flag, expressed in a placed copy of the selected child. -/
private def host_step_flagFrame (H : FramedNode S) (n : ℕ)
    (ι : P.Incidence) (b : Bool) : E d ≃ᵃ[ℝ] E d :=
  (S.child ι.val.ty ι.val.left).frame.toAffineEquiv.trans
    ((S.child ι.val.ty (ι.val.sideIndex b)).frame.symm.toAffineEquiv.trans
      (H.prototypeFrame n))

/-- The reference flag edge in ambient coordinates. -/
private def host_step_flagEdge (H : FramedNode S) (n : ℕ)
    (ι : P.Incidence) (b : Bool) : Set (E d) :=
  H.cell n ((P.sideFlag ι b).cell edgeIndex).val

/-- Full positioned flag alignment: affine spans, successive sides, edge
orientation, and the inward side. All linear maps include the expansion power. -/
private def host_step_aligned (H : FramedNode S) (n : ℕ)
    (ι : P.Incidence) (b : Bool) (N : FramedNode S) (m : ℕ)
    (z : host_step_Chain P) : Prop :=
  (∀ j, affineSpan ℝ (N.cell m (z.2.chain.val.cell j).val) =
    affineSpan ℝ (H.cell n ((P.sideFlag ι b).cell j).val)) ∧
  (∀ j, (N.prototypeFrame m).linear '' flagSide z.2.chain.val j =
    (H.prototypeFrame n).linear '' flagSide (P.sideFlag ι b) j) ∧
  0 < inner ℝ ((host_step_flagFrame H n ι b).linear (P.flag ι).direction)
    ((N.prototypeFrame m).linear (chainVector z.2)) ∧
  (N.prototypeFrame m).linear ''
      tangentCone (S.proto N.ty).carrier (cellAnchor z.1.facet.val) =
    (H.prototypeFrame n).linear ''
      tangentCone (S.proto H.ty).carrier (cellAnchor (ι.val.sideFacet b).val)

/-- The actual readout, activity and alignment required of a strand port. -/
private def host_step_portValid (Y : MarkedTiling (systemM S P C)) (n : ℕ)
    (H : FramedNode S) (ι : P.Incidence) (b : Bool)
    (u : host_step_Port C) : Prop :=
  u.1 ∈ Y.tiles ∧
  leafRecord (compilerLeaf C u.1) u.2.1.facet.val = some u.2.1 ∧
  u.2.1.ty = (tileNode u.1).ty ∧ u.2.2 ∈ u.2.1.chains ∧
  u.2.1.incidence = ι ∧ u.2.1.sideIndex = b ∧ u.2.1.beta.val = n % P.L ∧
  host_step_aligned H n ι b (tileNode u.1) 0 u.2 ∧
  ∃ q : Packet P, leafPacket (compilerLeaf C u.1) u.2.1.facet.val = some q

/-- The two physical endpoints, in the orientation read from the record. -/
private def host_step_portEnds (u : host_step_Port C) : E d × E d :=
  let e := u.2.1.endpoints (host_step_edge u.2)
  ((compilerFrame C u.1) e.1, (compilerFrame C u.1) e.2)

/-- The actual native edge of a strand port. -/
private def host_step_portEdge (u : host_step_Port C) : Set (E d) :=
  (tileNode u.1).cell 0 (host_step_edge u.2).val

/-- An END event based on an actual piece of the known block's facet.
Its realized sector is the cone of the proposed parent at the indicated endpoint. -/
private def host_step_endEvent (Y : MarkedTiling (systemM S P C)) (n : ℕ)
    (B : Block Y n) (f : FacetName S B.node.ty) (Q : FramedNode S)
    (p : E d) : Prop :=
  ∃ t ∈ Y.tiles, ∃ j : EndSlot (compilerLeaf C t), ∃ θ : Template P,
    Parser.IsFacetPiece Y n B.node f t j.facet ∧
    Compiler.endVertex (compilerFrame C t) j = p ∧
    Compiler.endSector (compilerFrame C t) j =
      (fun v => p + v) '' tangentCone (Q.carrier (n + 1)) p ∧
    θ ∈ allowedTemplates (.end_ j) ∧ TemplateOccurs C Y (compilerFrame C t) θ

/-- A finite oriented counter strand from the initial to the terminal flag
endpoint. It records CONT germ equations and distinct internal junctions, without
requiring different tiles at successive ports. -/
private def host_step_strand (Y : MarkedTiling (systemM S P C)) (n : ℕ)
    (H : FramedNode S) (ι : P.Incidence) (b : Bool)
    (m : ℕ) (u : Fin (m + 1) → host_step_Port C) : Prop :=
  (∀ i, host_step_portValid Y n H ι b (u i)) ∧
  (host_step_portEnds (u 0)).1 = host_step_flagFrame H n ι b (P.flag ι).initial ∧
  (host_step_portEnds (u (Fin.last m))).2 =
    host_step_flagFrame H n ι b (P.flag ι).terminal ∧
  (u 0).2.1.kappaMinus (host_step_edge (u 0).2) = 0 ∧
  (u (Fin.last m)).2.1.kappaPlus (host_step_edge (u (Fin.last m)).2) = P.N ∧
  (∀ i : Fin m,
    (host_step_portEnds (u i.castSucc)).2 = (host_step_portEnds (u i.succ)).1 ∧
    ((u i.succ).2.1.kappaMinus (host_step_edge (u i.succ).2) =
        (u i.castSucc).2.1.kappaPlus (host_step_edge (u i.castSucc).2) ∨
      (u i.succ).2.1.kappaMinus (host_step_edge (u i.succ).2) =
        (u i.castSucc).2.1.kappaPlus (host_step_edge (u i.castSucc).2) + 1)) ∧
  (∀ i, host_step_portEdge (u i) ⊆ host_step_flagEdge H n ι b) ∧
  Pairwise (fun i j => Disjoint (relint (host_step_portEdge (u i)))
    (relint (host_step_portEdge (u j)))) ∧
  (⋃ i, host_step_portEdge (u i)) = host_step_flagEdge H n ι b ∧
  Function.Injective (fun i : Fin m => (host_step_portEnds (u i.castSucc)).2) ∧
  (∀ i : Fin m, (host_step_portEnds (u i.castSucc)).2 ∈
    relint (host_step_flagEdge H n ι b)) ∧
  (∀ i : Fin m, ∀ j, (host_step_portEnds (u i.castSucc)).2 ∉
    relint (host_step_portEdge (u j))) ∧
  ∀ i, relint (host_step_portEdge (u i)) ⊆ relint (host_step_flagEdge H n ι b)

/-- A selected site strictly inside one native port edge, decoded from its
shallow word and then transported by the actual native frame. -/
private def host_step_localJump (u : host_step_Port C) (x : E d) : Prop :=
  ∃ w : ShortProfile P, u.2.1.counter = .inr w ∧ ∃ k : Fin P.N,
    x = compilerFrame C u.1 ((wordPlacement w.word).symm
      (P.sites u.2.1.incidence u.2.1.sideIndex k)) ∧
    x ∈ relint (host_step_portEdge u)

/-- A jump is either a selected site in an open strand edge or a unit CONT
jump at its junction. The shallow word places the site in the actual tile frame. -/
private def host_step_jump {m : ℕ} (u : Fin (m + 1) → host_step_Port C)
    (x : E d) : Prop :=
  (∃ i, host_step_localJump (u i) x) ∨
  ∃ i : Fin m, x = (host_step_portEnds (u i.castSucc)).2 ∧
    (u i.succ).2.1.kappaMinus (host_step_edge (u i.succ).2) =
      (u i.castSucc).2.1.kappaPlus (host_step_edge (u i.castSucc).2) + 1

/-- Readout and full alignment of an opposite root edge at the decoded height. -/
private def host_step_rootValid {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (H : FramedNode S) (ι : P.Incidence) (b : Bool)
    (R : host_step_Root D) : Prop :=
  stateRecordAt (D.blockState R.1.val R.1.property) R.2.1.facet.val = some R.2.1 ∧
  R.2.1.ty = R.1.val.node.ty ∧ R.2.2 ∈ R.2.1.chains ∧
  R.2.1.incidence = ι ∧ R.2.1.sideIndex = b ∧ R.2.1.beta.val = n % P.L ∧
  host_step_aligned H n ι b R.1.val.node n R.2

/-- The actual root edge, retaining the level's expansion power. -/
private def host_step_rootEdge {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    {D : DecodedLevel Y n} (R : host_step_Root D) : Set (E d) :=
  R.1.val.node.cell n (host_step_edge R.2).val

/-- The opposite roots partition the flag edge and lift every strand chain
through an actual descendant relation. These are geometric root data, without
any assertion of age one or of equality with the proposed sibling. -/
private def host_step_rootCover {Y : MarkedTiling (systemM S P C)} {n : ℕ}
    (D : DecodedLevel Y n) (H : FramedNode S) (ι : P.Incidence) (b : Bool)
    {m q : ℕ} (u : Fin (m + 1) → host_step_Port C)
    (R : Fin q → host_step_Root D) (owner : Fin (m + 1) → Fin q) : Prop :=
  (∀ j, host_step_rootValid D H ι b (R j)) ∧
  (∀ j, host_step_rootEdge (R j) ⊆ host_step_flagEdge H n ι b) ∧
  Pairwise (fun i j => Disjoint (relint (host_step_rootEdge (R i)))
    (relint (host_step_rootEdge (R j)))) ∧
  (⋃ j, host_step_rootEdge (R j)) = host_step_flagEdge H n ι b ∧
  ∀ i, (tileNode (u i).1).IsDescendant 0 (R (owner i)).1.val.node n ∧
    ∀ k, (tileNode (u i).1).cell 0 ((u i).2.2.chain.val.cell k).val ⊆
      (R (owner i)).1.val.node.cell n ((R (owner i)).2.2.chain.val.cell k).val

/-- Step 1 of the V4 proof of `host_step_step1_seed` (V4 3.6):
"the actual header of P at p₀: the cone G_p₀, the children's cones, and
the flag tangent data". This is that geometric header, expressed in a native
tile's frame, without asserting that the proposed parent is an actual block. -/
private def host_step_step1_seed_step1_header (Q : FramedNode S) (n : ℕ)
    (φ : Iso d) (p : E d) : State.Header P := by
  classical
  let normalize := fun K : Set (E d) => φ.linearIsometryEquiv.symm '' K
  let pos := fun ι : P.Incidence => P.incidencePlacement Q (n + 1) ι
  exact {
    birthType := Q.ty
    parentCone := normalize (tangentCone (Q.carrier (n + 1)) p)
    childCones := fun i =>
      let N := Q.child n i
      if p ∈ N.carrier n then some (normalize (tangentCone (N.carrier n) p)) else none
    boundaryCones := fun F => if p ∈ Q.cell (n + 1) F.val then
      some (normalize (tangentCone (Q.cell (n + 1) F.val) p)) else none
    primitiveCones := fun ι => if ι.val.ty = Q.ty ∧
        p ∈ pos ι '' ι.val.leftFacet.val.carrier then
      some (normalize (tangentCone (pos ι '' ι.val.leftFacet.val.carrier) p)) else none
    flagTangent := fun ι => if ι.val.ty = Q.ty ∧
        (p = pos ι (P.flag ι).initial ∨ p = pos ι (P.flag ι).terminal) then
      some {
        cones := fun j => normalize
          (tangentCone (pos ι '' ((P.flag ι).flag.cell j).val.carrier) p)
        initial := decide (p = pos ι (P.flag ι).initial)
        sides := fun j => normalize ((pos ι).linear '' (P.flag ι).sides j) }
      else none }

/-- Step 1 of the V4 proof of `host_step_step1_seed` (V4 3.6):
"the oriented flag ... transported to P". The sibling-coordinate formula
is the canonical incidence placement in the proposed parent, also for a
general anisotropic expansion. -/
private theorem host_step_step1_seed_step1_flag_frame (Q : FramedNode S) (n : ℕ)
    (ι : P.Incidence) (b : Bool) :
    host_step_flagFrame
        ((⟨ι.val.ty, Q.frame⟩ : FramedNode S).child n (ι.val.sideIndex b)) n ι b =
      P.incidencePlacement Q (n + 1) ι := by
  have hplace (x : E d) : S.placeChild n (ι.val.sideIndex b) ((S.σ ^ n) x) =
      (S.σ ^ n) ((S.child ι.val.ty (ι.val.sideIndex b)).frame x) := by
    change linearConj S.σ (n : ℤ)
        (S.child ι.val.ty (ι.val.sideIndex b)).rotation.toLinearEquiv ((S.σ ^ n) x) +
        (S.σ ^ n) (S.child ι.val.ty (ι.val.sideIndex b)).offset =
      (S.σ ^ n) ((S.child ι.val.ty (ι.val.sideIndex b)).rotation x +
        (S.child ι.val.ty (ι.val.sideIndex b)).offset)
    simp [linearConj, zpow_neg, LinearEquiv.mul_apply]
  apply AffineEquiv.ext
  intro x
  change Q.frame (S.placeChild n (ι.val.sideIndex b) ((S.σ ^ n)
      ((S.child ι.val.ty (ι.val.sideIndex b)).frame.symm
        ((S.child ι.val.ty ι.val.left).frame x)))) =
    Q.frame ((S.σ ^ (n + 1)) (S.σ.symm ((S.child ι.val.ty ι.val.left).frame x)))
  rw [hplace]
  simp only [AffineIsometryEquiv.apply_symm_apply, pow_succ, LinearEquiv.mul_apply,
    LinearEquiv.apply_symm_apply]

/-- Step 2 of the V4 proof of `host_step_step1_seed` (V4 3.6):
"Tiles t ⊆ B with a facet piece on f". A listed closed cell lies in the
prototype support, including at its boundary. -/
private theorem host_step_step1_seed_step2_cell_subset (A : S.ι) (e : Cell d) (he : e ∈ (S.cx A).cells) :
    e.carrier ⊆ (S.proto A).carrier := by
  intro x hx
  apply (S.proto A).compact.isClosed.frontier_subset
  rw [← (S.cx A).carriers_cover]
  exact mem_iUnion₂.mpr ⟨e, he, hx⟩

/-- Step 2 of the V4 proof of `host_step_step1_seed` (V4 3.6, 1.5, 1.8):
"Tiles t ⊆ B with a facet piece on f containing p₀ exist". Iterated
heredity covers the entire closed facet; listedness then passes to the
chosen actual native descendant, even at a boundary point of the piece. -/
private theorem host_step_step1_seed_step2_facet_at_vertex
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (B : Block Y n)
    (f : FacetName S B.node.ty) (p : E d) (hp : B.node.Lists n p)
    (hpf : p ∈ B.node.cell n f.val) :
    ∃ (t : PlacedMarkedTile (systemM S P C)) (g : FacetName S (tileNode t).ty)
      (v : VertexName S (tileNode t).ty),
      Parser.IsFacetPiece Y n B.node f t g ∧ v.val.carrier ⊆ g.val.carrier ∧
        compilerFrame C t (vertexPoint v) = p := by
  classical
  obtain ⟨parts, hparts⟩ := S.heredity_iter B.node.ty n f.val
    (Finset.mem_filter.mp f.property).1
  obtain ⟨x, hxf, hxp⟩ := hpf
  have hσx : (S.σ ^ n) x ∈ (S.σ ^ n) '' f.val.carrier := ⟨x, hxf, rfl⟩
  rw [hparts] at hσx
  obtain ⟨q, hq, y, hy, hxy⟩ := mem_iUnion₂.mp hσx
  obtain ⟨t, ht, hnode⟩ := B.actual q.1
  let g : FacetName S (tileNode t).ty := ⟨q.2.val, by
    rw [hnode]
    exact Finset.mem_filter.mpr ⟨q.2.property.1,
      q.2.property.2.trans (Finset.mem_filter.mp f.property).2⟩⟩
  have hdesc : (tileNode t).IsDescendant 0 B.node n := ⟨n, by omega, q.1, hnode⟩
  have hsub : (tileNode t).cell 0 g.val ⊆ B.node.cell n f.val := by
    rintro z ⟨w, hw, rfl⟩
    have hmem : (S.nativeTile B.node.ty n q.1).frame w ∈ (S.σ ^ n) '' f.val.carrier := by
      rw [hparts]
      exact mem_iUnion₂.mpr ⟨q, hq, w, hw, rfl⟩
    obtain ⟨z, hz, he⟩ := hmem
    refine ⟨z, hz, ?_⟩
    rw [hnode]
    change B.node.frame ((S.σ ^ n) z) = B.node.frame ((S.nativeTile B.node.ty n q.1).frame w)
    exact congrArg B.node.frame he
  have hpoint : (tileNode t).prototypeFrame 0 y = p := by
    rw [hnode]
    change B.node.frame ((S.nativeTile B.node.ty n q.1).frame y) = p
    rw [hxy]
    exact hxp
  have hmem : p ∈ (tileNode t).carrier 0 := by
    rw [← hpoint, hnode]
    refine ⟨(S.σ ^ 0) y, ⟨y, ?_, rfl⟩, rfl⟩
    exact host_step_step1_seed_step2_cell_subset _ q.2.val q.2.property.1 hy
  obtain ⟨v, hv, hvp⟩ := commonListed_inherited B.node (tileNode t) n 0 hdesc p hp hmem
  let v' : VertexName S (tileNode t).ty := ⟨v, hv⟩
  have hvpoint : compilerFrame C t (vertexPoint v') = p := by
    obtain ⟨z, hz, hzp⟩ := hvp
    change z ∈ v'.val.carrier at hz
    have hzv : z = vertexPoint v' := by simpa only [vertexPoint_spec v', mem_singleton_iff] using hz
    subst z
    exact hzp
  have hvg : v.carrier ⊆ g.val.carrier := by
    rw [vertexPoint_spec v']
    apply singleton_subset_iff.mpr
    have hyv : y = vertexPoint v' := by
      apply (compilerFrame C t).injective
      exact hpoint.trans hvpoint.symm
    simpa only [← hyv] using hy
  exact ⟨t, g, v', ⟨ht, hdesc, hsub⟩, hvg, hvpoint⟩

/-- Step 2 of the V4 proof of `host_step_step1_seed` (V4 3.6, 1.4(a)):
"p₀, p_N the initial and terminal vertices of h". Both endpoints are
listed vertices on both incidence sides. Sibling conformity transfers the
canonical singleton cell to the other side without identifying prototypes. -/
private theorem host_step_step1_seed_step2_side_vertex (ι : P.Incidence) (b : Bool) (p : E d)
    (hp : p = (P.flag ι).initial ∨ p = (P.flag ι).terminal) :
    ∃ v ∈ (S.cx (ι.val.sideType b)).vertices,
      v.carrier = {(S.child ι.val.ty (ι.val.sideIndex b)).frame.symm
        ((S.child ι.val.ty ι.val.left).frame p)} ∧
      v.carrier ⊆ (ι.val.sideFacet b).val.carrier := by
  classical
  have hpedge : p ∈ ((P.flag ι).flag.cell edgeIndex).val.carrier := by
    rw [(P.flag ι).edge_eq]
    rcases hp with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  have hpf : p ∈ ι.val.leftFacet.val.carrier := by
    have hsub := (P.flag ι).flag.nested edgeIndex facetIndex (by
      change 1 ≤ d - 1
      have := (Fact.out : 2 ≤ d)
      omega)
    rw [(P.flag ι).top] at hsub
    exact hsub hpedge
  obtain ⟨v, hv, hvc⟩ : ∃ v ∈ (S.cx (S.child ι.val.ty ι.val.left).ty).vertices,
      v.carrier = {p} := by
    rcases hp with rfl | rfl
    · exact (P.flag ι).initial_listed
    · exact (P.flag ι).terminal_listed
  cases b with
  | false =>
    refine ⟨v, hv, ?_, ?_⟩
    · simpa only [PrimitiveIncidence.sideIndex, Bool.false_eq_true, ↓reduceIte,
        AffineIsometryEquiv.symm_apply_apply] using hvc
    · simpa only [hvc, singleton_subset_iff] using hpf
  | true =>
    have hleft : (S.child ι.val.ty ι.val.left).frame p ∈
        placedSet (S.child ι.val.ty ι.val.left).frame
          (S.proto (S.child ι.val.ty ι.val.left).ty).carrier := by
      exact ⟨p, host_step_step1_seed_step2_cell_subset _ _ (Finset.mem_filter.mp ι.val.leftFacet.property).1 hpf, rfl⟩
    have hrightfacet : (S.child ι.val.ty ι.val.left).frame p ∈
        placedSet (S.child ι.val.ty ι.val.right).frame ι.val.rightFacet.val.carrier := by
      rw [← ι.val.paired]
      exact ⟨p, hpf, rfl⟩
    have hright : (S.child ι.val.ty ι.val.left).frame p ∈
        placedSet (S.child ι.val.ty ι.val.right).frame
          (S.proto (S.child ι.val.ty ι.val.right).ty).carrier := by
      exact Set.image_mono
        (host_step_step1_seed_step2_cell_subset _ _ (Finset.mem_filter.mp ι.val.rightFacet.property).1) hrightfacet
    obtain ⟨w, hw, hplace⟩ := S.sibling_conformity ι.val.ty ι.val.left ι.val.right
      ι.val.distinct ((S.child ι.val.ty ι.val.left).frame p) hleft hright v
      (Finset.mem_filter.mp hv).1
      (by simp only [AffineIsometryEquiv.symm_apply_apply, hvc, relint,
        intrinsicInterior_singleton, mem_singleton_iff])
      (by have hd := (Finset.mem_filter.mp hv).2; omega)
    let p' := (S.child ι.val.ty ι.val.right).frame.symm
      ((S.child ι.val.ty ι.val.left).frame p)
    have hwc : w.carrier = {p'} := by
      apply (Set.image_injective.mpr (S.child ι.val.ty ι.val.right).frame.injective)
      change placedSet (S.child ι.val.ty ι.val.right).frame w.carrier = _
      rw [← hplace, hvc]
      simp only [placedSet, image_singleton, p', AffineIsometryEquiv.apply_symm_apply]
    have hdim : w.dim = 0 := by
      rw [← w.flat.dimension, cellDirection, hwc]
      simp [direction_affineSpan]
    refine ⟨w, Finset.mem_filter.mpr ⟨hw, hdim⟩, hwc, ?_⟩
    rw [hwc]
    apply singleton_subset_iff.mpr
    obtain ⟨z, hz, he⟩ := hrightfacet
    have hz' : z = p' := (S.child ι.val.ty ι.val.right).frame.injective
      (he.trans ((S.child ι.val.ty ι.val.right).frame.apply_symm_apply _).symm)
    simpa only [← hz'] using hz

/-- Step 2 of the V4 proof of `host_step_step1_seed` (V4 3.6):
"the oriented flag ... transported to P". The two endpoint singleton cells
remain listed, and lie on the named facet, in every placed incidence child. -/
private theorem host_step_step1_seed_step2_child_endpoint
    (Q : FramedNode S) (n : ℕ) (ι : P.Incidence) (b : Bool) (p : E d)
    (hp : p = (P.flag ι).initial ∨ p = (P.flag ι).terminal) :
    let H := (⟨ι.val.ty, Q.frame⟩ : FramedNode S).child n (ι.val.sideIndex b)
    H.Lists n (P.incidencePlacement Q (n + 1) ι p) ∧
      P.incidencePlacement Q (n + 1) ι p ∈ H.cell n (ι.val.sideFacet b).val := by
  obtain ⟨v, hv, hvc, hsub⟩ := host_step_step1_seed_step2_side_vertex ι b p hp
  let x := (S.child ι.val.ty (ι.val.sideIndex b)).frame.symm
    ((S.child ι.val.ty ι.val.left).frame p)
  have hx : x ∈ v.carrier := by rw [hvc]; exact mem_singleton _
  dsimp only
  rw [← host_step_step1_seed_step1_flag_frame Q n ι b]
  exact ⟨⟨v, hv, x, hx, rfl⟩, ⟨x, hsub hx, rfl⟩⟩

/-- Step 2 of the V4 proof of `host_step_step1_seed` (V4 3.6, 1.5, 1.8):
"Tiles t ⊆ B with a facet piece on f containing p₀ exist".
Hereditary subdivision supplies an actual native facet piece and a listed
vertex on it at either flag endpoint; this asserts no event or leaf readout. -/
private theorem host_step_step1_seed_step2_endpoint_piece
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) (p : E d)
    (hp : p = host_step_flagFrame (proposedSibling D B hB f a) n a.record.incidence
        (!a.record.sideIndex) (P.flag a.record.incidence).initial ∨
      p = host_step_flagFrame (proposedSibling D B hB f a) n a.record.incidence
        (!a.record.sideIndex) (P.flag a.record.incidence).terminal) :
    B.node.Lists n p ∧
      ∃ (t : PlacedMarkedTile (systemM S P C)) (g : FacetName S (tileNode t).ty)
        (v : VertexName S (tileNode t).ty),
        Parser.IsFacetPiece Y n B.node f t g ∧ v.val.carrier ⊆ g.val.carrier ∧
          compilerFrame C t (vertexPoint v) = p := by
  let Q := proposedParent D B hB
  let ι := a.record.incidence
  have hs := Parser.ageOneFacet_semantics D hD B hB f a
  have hrole : firstRole D B hB = ι.val.sideRole a.record.sideIndex :=
    hs.2.2.1.symm.trans a.record.side_eq
  have hBnode : B.node =
      (⟨ι.val.ty, Q.frame⟩ : FramedNode S).child n (ι.val.sideIndex a.record.sideIndex) := by
    have hc := Parser.proposedParent_child D hD B hB
    exact hc.symm.trans (congrArg
      (fun r : S.Role => (⟨r.1, Q.frame⟩ : FramedNode S).child n r.2) hrole)
  have hflag : host_step_flagFrame (proposedSibling D B hB f a) n ι
      (!a.record.sideIndex) = P.incidencePlacement Q (n + 1) ι :=
    host_step_step1_seed_step1_flag_frame Q n ι (!a.record.sideIndex)
  have hgeom : ∀ x, x = (P.flag ι).initial ∨ x = (P.flag ι).terminal →
      B.node.Lists n (P.incidencePlacement Q (n + 1) ι x) ∧
        P.incidencePlacement Q (n + 1) ι x ∈ B.node.cell n f.val := by
    intro x hx
    have hown := host_step_step1_seed_step2_child_endpoint Q n ι a.record.sideIndex x hx
    have hopp := host_step_step1_seed_step2_child_endpoint Q n ι (!a.record.sideIndex) x hx
    refine ⟨by simpa only [← hBnode] using hown.1, ?_⟩
    rw [← hs.2.2.2]
    exact hopp.2
  have hp' : p = P.incidencePlacement Q (n + 1) ι (P.flag ι).initial ∨
      p = P.incidencePlacement Q (n + 1) ι (P.flag ι).terminal := by
    dsimp only [ι] at hflag
    simpa only [hflag] using hp
  have hlisted : B.node.Lists n p ∧ p ∈ B.node.cell n f.val := by
    rcases hp' with rfl | rfl
    · exact hgeom _ (Or.inl rfl)
    · exact hgeom _ (Or.inr rfl)
  exact ⟨hlisted.1, host_step_step1_seed_step2_facet_at_vertex Y n B f p hlisted.1 hlisted.2⟩

/-- Step 3 of the V4 proof of `host_step_step1_seed` (V4 3.6, 2.3):
"by (I2) their record on that piece is the restriction of the age-1 record"
and "their (S6) record is the header ... in t's frame".
This is only the iterated restriction/readout assertion for an already given
native facet piece and listed block vertex. No template is asserted. -/
private theorem host_step_step1_seed_step3_restricted_header
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) (p : E d) (hp : B.node.Lists n p)
    (t : PlacedMarkedTile (systemM S P C)) (g : FacetName S (tileNode t).ty)
    (v : VertexName S (tileNode t).ty) (hpiece : Parser.IsFacetPiece Y n B.node f t g)
    (hv : v.val.carrier ⊆ g.val.carrier) (hvp : compilerFrame C t (vertexPoint v) = p) :
    ∃ j : EndSlot (compilerLeaf C t), j.facet = g ∧
      Compiler.endVertex (compilerFrame C t) j = p ∧
      j.record.incidence = a.record.incidence ∧ j.record.beta.val = n % P.L ∧
      j.header = host_step_step1_seed_step1_header (proposedParent D B hB) n
        (compilerFrame C t) p := by
  -- Realize the root state at height n, using exact scale transfer if needed,
  -- then iterate I2 along the native address supplied by hpiece. Provider
  -- inheritance preserves incidence and beta; the listed block vertex has
  -- a zero-dimensional provider stratum. Unfolding headerOf gives the header.
  sorry

/-- Step 4 of the V4 proof of `host_step_step1_seed` (V4 3.6):
"Theorem 2.17(b) yields a template ... realised by actual tiles".
Once an actual facet piece carries the geometric header, compilation supplies
the required END event; the sector equality is just change of frame. -/
private theorem host_step_step1_seed_step4_event
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) (n : ℕ)
    (B : Block Y n) (f : FacetName S B.node.ty) (Q : FramedNode S) (p : E d)
    (t : PlacedMarkedTile (systemM S P C)) (j : EndSlot (compilerLeaf C t))
    (hpiece : Parser.IsFacetPiece Y n B.node f t j.facet)
    (hp : Compiler.endVertex (compilerFrame C t) j = p)
    (hheader : j.header = host_step_step1_seed_step1_header Q n (compilerFrame C t) p) :
    ∃ T : EndTemplate j, endRow T ∧
      TemplateOccurs C Y (compilerFrame C t) T.configuration ∧
      host_step_endEvent Y n B f Q p := by
  obtain ⟨θ, hθ, _, hactual⟩ := compiler_events C Y hY t hpiece.1 (.end_ j)
  obtain ⟨T, rfl, hrow⟩ := hθ
  refine ⟨T, hrow, hactual, t, hpiece.1, j, T.configuration,
    hpiece, hp, ?_, ⟨T, rfl, hrow⟩, hactual⟩
  simp only [Compiler.endSector, hp, hheader, host_step_step1_seed_step1_header,
    Set.image_image, LinearIsometryEquiv.apply_symm_apply]

/-- Step 5 of the V4 proof of `host_step_step1_seed` (V4 3.6, 1.22):
"consider the recursive trace ... and the selected owner ... adjacent to h′
at its initial endpoint". An honest END geometry supplies a port on either
child side and an unlabelled full chain fitting its recorded flag tangent.
The edge has the exact endpoint ray. This involves no output tiling, record
activity, counter, or chosen scale. -/
private theorem host_step_step1_seed_step5_trace
    (Z : EndGeometry P) (hZ : Z ∈ honestEndGeometries S P)
    (ι : P.Incidence) (b : Bool) (G : State.FlagTangent (d := d))
    (hG : Z.header.flagTangent ι = some G) :
    ∃ a ∈ Z.primitivePorts, a.incidence = ι ∧ a.sideIndex = b ∧
      ∃ F : FlagChain a.facet,
        (∀ k, vertexPoint Z.vertex ∈ placedSet a.tile.frame (F.val.cell k).val.carrier ∧
          affineSpan ℝ (placedSet a.tile.frame (F.val.cell k).val.carrier) =
            affineSpan ℝ ((fun v => vertexPoint Z.vertex + v) '' G.cones k) ∧
          tangentCone (placedSet a.tile.frame (F.val.cell k).val.carrier)
            (vertexPoint Z.vertex) ⊆ G.cones k) ∧
        tangentCone (placedSet a.tile.frame (F.val.cell edgeIndex).val.carrier)
          (vertexPoint Z.vertex) = G.cones edgeIndex := by
  -- Unpack the honest source witnessing hZ. Use the recursive trace in the
  -- selected child, and edge heredity in its endpoint trace piece. The full
  -- chain belongs to a native owner in the complete owned star. The primitive
  -- port biconditional in EndGeometryRealizes places this port in Z.
  sorry

/-- Step 6 of the V4 proof of `host_step_step1_seed` (V4 3.6):
"Row (E1) gives u₀'s record on its port". A cell-keyed record has the
prototype and facet of the leaf from which it was read. -/
private theorem host_step_step1_seed_step6_readout (l : LeafType P) (f : Cell d)
    (r : FacetRecord P) (hr : leafRecord l f = some r) :
    r.ty = l.prototype ∧ r.facet.val = f := by
  classical
  unfold leafRecord stateRecordAt at hr
  split at hr
  · obtain ⟨hty, hf⟩ := l.prePattern.state.facetRecord_valid _ r hr
    exact ⟨hty.trans (l.prePattern.state_type.trans l.prePattern_type), hf⟩
  · contradiction

/-- Step 6 of the V4 proof of `host_step_step1_seed` (V4 3.6, 2.6(c)):
"its packet equals 𝒫_B(f)". In particular a finite port has a non-NULL
packet: the record and packet come from the same honest leaf pre-pattern. -/
private theorem host_step_step1_seed_step6_packet (l : LeafType P) (f : Cell d)
    (r : FacetRecord P) (hr : leafRecord l f = some r) :
    ∃ q : Packet P, leafPacket l f = some q := by
  classical
  obtain ⟨U, t, ht, hw⟩ := (certificate_components_honest P l.1.val l.1.property).1 l.2
  change prePatternOf U P t ht = l.prePattern at hw
  unfold leafRecord at hr
  rw [← hw] at hr
  change stateRecordAt (stateOf U P t) f = some r at hr
  unfold stateRecordAt at hr
  split at hr
  next hf =>
    change f ∈ (S.cx t.2.val.ty).facets at hf
    change U.facetRecordOf P t ⟨f, hf⟩ = some r at hr
    unfold HonestSource.facetRecordOf at hr
    split at hr
    · contradiction
    next hn =>
      refine ⟨packetOf U P (U.providerOccurrence P t ⟨f, hf⟩ hn), ?_⟩
      unfold leafPacket
      rw [← hw]
      simp only [prePatternOf, dif_pos hf, HonestSource.facetPacket, dif_neg hn]
  · contradiction

/-- Step 6 of the V4 proof of `host_step_step1_seed` (V4 3.6):
"incidence ι, side (A_P,j)". Globally distinct child roles determine the
Boolean side index; no distinct-prototype assumption is needed. -/
private theorem host_step_step1_seed_step6_side (r : FacetRecord P)
    (ι : P.Incidence) (b : Bool) (hi : r.incidence = ι)
    (hs : r.side = ι.val.sideRole b) : r.sideIndex = b := by
  have hroles : ι.val.sideRole r.sideIndex = ι.val.sideRole b := by
    simpa only [hi] using r.side_eq.symm.trans hs
  have hd := ι.val.distinct
  cases hr : r.sideIndex <;> cases b <;>
    simp_all [PrimitiveIncidence.sideRole, PrimitiveIncidence.sideIndex]

/-- Step 7 of the V4 proof of `host_step_step1_seed` (V4 3.6):
"cells are determined by type and frame". Re-keying a geometric chain by
the finite record preserves its cells, tangent fit, and bottom-edge ray. -/
private theorem host_step_step1_seed_step7_chain
    (a : PrimitivePort P) (r : FacetRecord P) (ht : r.ty = a.tile.ty)
    (hf : r.facet.val = a.facet.val) (F : FlagChain a.facet)
    (x : E d) (G : State.FlagTangent (d := d))
    (hfit : ∀ k, x ∈ placedSet a.tile.frame (F.val.cell k).val.carrier ∧
      affineSpan ℝ (placedSet a.tile.frame (F.val.cell k).val.carrier) =
        affineSpan ℝ ((fun v => x + v) '' G.cones k) ∧
      tangentCone (placedSet a.tile.frame (F.val.cell k).val.carrier) x ⊆ G.cones k)
    (hray : tangentCone (placedSet a.tile.frame (F.val.cell edgeIndex).val.carrier) x =
      G.cones edgeIndex) :
    ∃ F' : FlagChain r.facet, ChainFitsTangent r a.tile.frame x F' G ∧
      tangentCone (placedSet a.tile.frame (F'.val.cell edgeIndex).val.carrier) x =
        G.cones edgeIndex := by
  let F' : FacetFlag S r.ty := {
    cell := fun k => ⟨(F.val.cell k).val, by rw [ht]; exact (F.val.cell k).property⟩
    dimension := F.val.dimension
    nested := F.val.nested }
  have htop : (F'.cell facetIndex).val = r.facet.val := F.property.trans hf.symm
  exact ⟨⟨F', htop⟩, hfit, hray⟩

/-- Step 8 of the V4 proof of `host_step_step1_seed` (V4 3.6):
"the realised flag tangent cones ... equal the actual T_p₀ F_j" and
"u₀ lies on the j-side". Transporting an already active, oriented chain
in a primitive port of an honest star gives its affine flag, inward side,
and initial endpoint in the ambient frame. There is no existence assertion
for a port or active chain here, and no counter assertion. -/
private theorem host_step_step1_seed_step8_transport
    (Q : FramedNode S) (n : ℕ) (ι : P.Incidence) (b : Bool) (hι : ι.val.ty = Q.ty)
    (φ : Iso d) (l : LeafType P) (j : EndSlot l)
    (hp : Compiler.endVertex φ j = P.incidencePlacement Q (n + 1) ι (P.flag ι).initial)
    (hh : j.header = host_step_step1_seed_step1_header Q n φ
      (P.incidencePlacement Q (n + 1) ι (P.flag ι).initial))
    (T : EndTemplate j) (a : PrimitivePort P) (ha : a ∈ T.geometry.primitivePorts)
    (hai : a.incidence = ι) (hab : a.sideIndex = b)
    (u : LeafType P) (hu : (a.tile, u) ∈ T.configuration.tiles)
    (r : FacetRecord P) (hr : leafRecord u a.facet.val = some r)
    (c : OrientedChain r.facet) (hc : c ∈ r.chains)
    (G : State.FlagTangent (d := d))
    (hG : T.geometry.header.flagTangent ι = some G) (hi : G.initial = true)
    (hfit : ChainFitsTangent r a.tile.frame (vertexPoint T.geometry.vertex) c.chain G)
    (ho : OrientationFitsTangent r a.tile.frame c G)
    (hray : tangentCone (placedSet a.tile.frame (host_step_edge ⟨r, c⟩).val.carrier)
      (vertexPoint T.geometry.vertex) = G.cones edgeIndex) :
    host_step_aligned
        ((⟨ι.val.ty, Q.frame⟩ : FramedNode S).child n (ι.val.sideIndex b)) n ι b
        ⟨u.prototype, a.tile.frame.trans φ⟩ 0 ⟨r, c⟩ ∧
      (a.tile.frame.trans φ) (r.endpoints (host_step_edge ⟨r, c⟩)).1 =
        P.incidencePlacement Q (n + 1) ι (P.flag ι).initial := by
  -- The full header equality identifies flag cones, coface sides, and the
  -- selected child's cone. The primitive-port geometry fixes the inward
  -- half-space. Honest activity makes the record's edge orientation agree
  -- with c; the initial flag ray therefore starts at the event vertex.
  sorry

/-- Step 9 of the V4 proof of `host_step_step1_seed` (V4 3.6):
"by alignment, the chain ... is recorded active" and "by the endpoint
counters, κ⁻(e₀)=0". These are the two clauses of row (E2), applied to the
selected geometric chain and its exact initial flag ray. -/
private theorem host_step_step1_seed_step9_counter {l : LeafType P}
    {j : EndSlot l} (T : EndTemplate j) (hrow : endRow T)
    (a : PrimitivePort P) (ha : a ∈ T.geometry.primitivePorts)
    (u : LeafType P) (hu : (a.tile, u) ∈ T.configuration.tiles)
    (r : FacetRecord P) (hr : leafRecord u a.facet.val = some r)
    (G : State.FlagTangent (d := d))
    (hG : T.geometry.header.flagTangent a.incidence = some G) (hi : G.initial = true)
    (F : FlagChain r.facet)
    (hfit : ChainFitsTangent r a.tile.frame (vertexPoint T.geometry.vertex) F G)
    (hray : tangentCone (placedSet a.tile.frame (F.val.cell edgeIndex).val.carrier)
      (vertexPoint T.geometry.vertex) = G.cones edgeIndex) :
    ∃ c ∈ r.chains, c.chain = F ∧ OrientationFitsTangent r a.tile.frame c G ∧
      r.kappaMinus (host_step_edge ⟨r, c⟩) = 0 := by
  have he2 := hrow.2.1.2 a ha u hu r hr G hG
  obtain ⟨c, hc, hF, ho⟩ := he2.1 F hfit
  have hx : vertexPoint T.geometry.vertex ∈
      placedSet a.tile.frame (host_step_edge ⟨r, c⟩).val.carrier := by
    simpa only [host_step_edge, hF] using (hfit edgeIndex).1
  have hcone : tangentCone
      (placedSet a.tile.frame (host_step_edge ⟨r, c⟩).val.carrier)
        (vertexPoint T.geometry.vertex) = G.cones edgeIndex := by
    simpa only [host_step_edge, hF] using hray
  have hz := he2.2 (host_step_edge ⟨r, c⟩) ⟨c, hc, rfl⟩ hx hcone
  exact ⟨c, hc, hF, ho, by simpa only [hi, Bool.true_eq, ite_true] using hz⟩

/-- Step 1 of the V4 proof of `host_step` (V4 3.6): "the endpoint events
and the first strand tile"; "by the endpoint counters, κ⁻(e₀)=0".
The seed records the full flag and the opposite inward side, and the two END
events are based on actual facet pieces of B. -/
private theorem host_step_step1_seed (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) :
    let H := proposedSibling D B hB f a
    let ι := a.record.incidence
    let b := !a.record.sideIndex
    host_step_endEvent Y n B f (proposedParent D B hB)
        (host_step_flagFrame H n ι b (P.flag ι).initial) ∧
    host_step_endEvent Y n B f (proposedParent D B hB)
        (host_step_flagFrame H n ι b (P.flag ι).terminal) ∧
    ∃ u : host_step_Port C, host_step_portValid Y n H ι b u ∧
      (host_step_portEnds u).1 = host_step_flagFrame H n ι b (P.flag ι).initial ∧
      u.2.1.kappaMinus (host_step_edge u.2) = 0 := by
  classical
  let Q := proposedParent D B hB
  let H := proposedSibling D B hB f a
  let ι := a.record.incidence
  let b := !a.record.sideIndex
  let p₀ := host_step_flagFrame H n ι b (P.flag ι).initial
  let pN := host_step_flagFrame H n ι b (P.flag ι).terminal
  have hframe : host_step_flagFrame H n ι b = P.incidencePlacement Q (n + 1) ι :=
    host_step_step1_seed_step1_flag_frame Q n ι b
  have hι : ι.val.ty = Q.ty := (Parser.ageOneFacet_semantics D hD B hB f a).2.1
  obtain ⟨hlisted₀, t₀, g₀, v₀, hpiece₀, hv₀, hpv₀⟩ :=
    host_step_step1_seed_step2_endpoint_piece Y n D hD B hB f a p₀ (Or.inl rfl)
  obtain ⟨j₀, hjfacet₀, hjp₀, _, hbeta₀, hheader₀⟩ :=
    host_step_step1_seed_step3_restricted_header Y n D hD B hB f a p₀ hlisted₀
      t₀ g₀ v₀ hpiece₀ hv₀ hpv₀
  have hpiece₀' : Parser.IsFacetPiece Y n B.node f t₀ j₀.facet := by
    simpa only [hjfacet₀] using hpiece₀
  obtain ⟨T, hrow, hactual, he₀⟩ :=
    host_step_step1_seed_step4_event Y hY n B f Q p₀ t₀ j₀ hpiece₀' hjp₀ hheader₀
  obtain ⟨hlistedN, tN, gN, vN, hpieceN, hvN, hpvN⟩ :=
    host_step_step1_seed_step2_endpoint_piece Y n D hD B hB f a pN (Or.inr rfl)
  obtain ⟨jN, hjfacetN, hjpN, _, _, hheaderN⟩ :=
    host_step_step1_seed_step3_restricted_header Y n D hD B hB f a pN hlistedN
      tN gN vN hpieceN hvN hpvN
  have hpieceN' : Parser.IsFacetPiece Y n B.node f tN jN.facet := by
    simpa only [hjfacetN] using hpieceN
  obtain ⟨_, _, _, heN⟩ :=
    host_step_step1_seed_step4_event Y hY n B f Q pN tN jN hpieceN' hjpN hheaderN
  refine ⟨he₀, heN, ?_⟩
  obtain ⟨G, hG, hinitial⟩ : ∃ G : State.FlagTangent (d := d),
      T.geometry.header.flagTangent ι = some G ∧ G.initial = true := by
    rw [T.header_eq, hheader₀]
    simp [host_step_step1_seed_step1_header, p₀, hframe, hι, Q]
  obtain ⟨port, hport, hportι, hportb, F, hfit, hray⟩ :=
    host_step_step1_seed_step5_trace T.geometry T.honest_geometry ι b G hG
  have htile : port.tile ∈ T.configuration.tiles.image Prod.fst := by
    rw [T.tiles_eq]
    exact T.geometry.primitive_tiles port hport
  obtain ⟨⟨N, l⟩, hl, hN⟩ := Finset.mem_image.mp htile
  change N = port.tile at hN
  subst N
  obtain ⟨r, hr, hrι, hrs, _, hrβ⟩ := hrow.1.1 port hport l hl
  obtain ⟨hty, hfacet⟩ := host_step_step1_seed_step6_readout l port.facet.val r hr
  have hrb : r.sideIndex = b := host_step_step1_seed_step6_side r ι b
    (hrι.trans hportι) (by simpa only [hportι, hportb] using hrs.trans port.side_eq)
  obtain ⟨q, hq⟩ := host_step_step1_seed_step6_packet l port.facet.val r hr
  obtain ⟨F', hfit', hray'⟩ := host_step_step1_seed_step7_chain port r
    (hty.trans (T.configuration.types_match _ hl).symm) hfacet F
    (vertexPoint T.geometry.vertex) G hfit hray
  obtain ⟨c, hc, hcF, ho, hz⟩ := host_step_step1_seed_step9_counter T hrow port hport l hl
    r hr G (by simpa only [hportι] using hG) hinitial F' hfit' hray'
  have hfitc : ChainFitsTangent r port.tile.frame (vertexPoint T.geometry.vertex) c.chain G := by
    simpa only [hcF] using hfit'
  have hrayc : tangentCone
      (placedSet port.tile.frame (host_step_edge ⟨r, c⟩).val.carrier)
        (vertexPoint T.geometry.vertex) = G.cones edgeIndex := by
    simpa only [host_step_edge, hcF] using hray'
  obtain ⟨halign, hstart⟩ := host_step_step1_seed_step8_transport Q n ι b hι
    (compilerFrame C t₀) (compilerLeaf C t₀) j₀
    (by simpa only [p₀, hframe] using hjp₀)
    (by simpa only [p₀, hframe] using hheader₀)
    T port hport hportι hportb l hl r hr c hc G hG hinitial hfitc ho hrayc
  obtain ⟨t, ht, hleaf, hφ⟩ := TemplateOccurs.tile_data C Y (compilerFrame C t₀)
    T.configuration hactual (port.tile, l) hl
  have hnode : tileNode t = ⟨l.prototype, port.tile.frame.trans (compilerFrame C t₀)⟩ := by
    simp only [tileNode, hleaf, hφ]
  refine ⟨(t, ⟨r, c⟩), ?_, ?_, hz⟩
  · refine ⟨ht, ?_, ?_, hc, hrι.trans hportι, hrb, ?_, ?_, q, ?_⟩
    · simpa only [hleaf, hfacet] using hr
    · simpa only [hnode] using hty
    · exact (congrArg Fin.val hrβ).trans hbeta₀
    · simpa only [hnode] using halign
    · simpa only [hleaf, hfacet] using hq
  · change compilerFrame C t (r.endpoints (host_step_edge ⟨r, c⟩)).1 = p₀
    simpa only [hφ, p₀, hframe] using hstart

/-- Step 2 of the V4 proof of `host_step` (V4 3.6): "The strand never
passes p_N" and "No false interior endpoint". CONT extends the seed, the
terminal END event bounds the strand, and the restriction of B's age-one
strata rules out stopping in the open flag edge. -/
private theorem host_step_step2_strand (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f)
    (hends : host_step_endEvent Y n B f (proposedParent D B hB)
        (host_step_flagFrame (proposedSibling D B hB f a) n a.record.incidence
          (!a.record.sideIndex) (P.flag a.record.incidence).initial) ∧
      host_step_endEvent Y n B f (proposedParent D B hB)
        (host_step_flagFrame (proposedSibling D B hB f a) n a.record.incidence
          (!a.record.sideIndex) (P.flag a.record.incidence).terminal))
    (u₀ : host_step_Port C)
    (hu₀ : host_step_portValid Y n (proposedSibling D B hB f a)
      a.record.incidence (!a.record.sideIndex) u₀)
    (hstart : (host_step_portEnds u₀).1 =
      host_step_flagFrame (proposedSibling D B hB f a) n a.record.incidence
        (!a.record.sideIndex) (P.flag a.record.incidence).initial)
    (hzero : u₀.2.1.kappaMinus (host_step_edge u₀.2) = 0) :
    ∃ m : ℕ, ∃ u : Fin (m + 1) → host_step_Port C, u 0 = u₀ ∧
      host_step_strand Y n (proposedSibling D B hB f a)
        a.record.incidence (!a.record.sideIndex) m u := by
  sorry

/-- Step 1 of the V4 proof of `host_step_step2_port_sites` (V4 2.3):
"re-expressed in C's frame". A child frame factors through its normalized role. -/
private theorem host_step_step2_port_sites_step1_child_frame
    (N : FramedNode S) (n : ℕ) (i : S.I N.ty) :
    (N.child n i).prototypeFrame n =
      (rolePlacement ⟨N.ty, i⟩).trans (N.prototypeFrame (n + 1)) := by
  apply AffineEquiv.ext
  intro x
  change N.frame (S.placeChild n i ((S.σ ^ n) x)) =
    N.frame ((S.σ ^ (n + 1)) (S.σ.symm ((S.child N.ty i).frame x)))
  congr 1
  rw [S.placeChild_apply]
  simp [linearConj, Child.frame, rigidMotion, pow_succ, zpow_neg,
    LinearEquiv.mul_apply, ← map_add]

/-- Step 1 of the V4 proof of `host_step_step2_port_sites` (V4 2.3):
"re-expressed in C's frame". The honest parent relation has that same factorization. -/
private theorem host_step_step2_port_sites_step1_parent_frame
    (U : HonestSource S) (q : U.Node) :
    q.2.val.prototypeFrame q.1 =
      (rolePlacement (U.hierarchy.nodeRole q)).trans
        ((U.hierarchy.parentNode q).2.val.prototypeFrame
          (U.hierarchy.parentNode q).1) := by
  conv_lhs => rw [U.hierarchy.child_eq q.1 q.2]
  exact host_step_step2_port_sites_step1_child_frame _ _ _

/-- Step 1 of the V4 proof of `host_step_step2_port_sites` (V4 2.3):
"re-expressed in C's frame". Iterating the role placements gives the full ancestor frame. -/
private theorem host_step_step2_port_sites_step1_word_frame
    (U : HonestSource S) (q : U.Node) (a : ℕ) :
    q.2.val.prototypeFrame q.1 =
      (wordPlacement (U.downRoles q a)).trans
        ((U.hierarchy.ancestor q a).2.val.prototypeFrame
          (U.hierarchy.ancestor q a).1) := by
  induction a with
  | zero =>
    simp [HonestSource.downRoles, CoherentHierarchy.ancestor, wordPlacement]
  | succ a ih =>
    have hroles : U.downRoles q (a + 1) =
        U.hierarchy.nodeRole (U.hierarchy.ancestor q a) :: U.downRoles q a := by
      unfold HonestSource.downRoles
      rw [List.ofFn_succ']
      simp only [List.concat_eq_append, List.reverse_append, List.reverse_singleton,
        List.singleton_append, Fin.val_last, Fin.val_castSucc]
    have ha : U.hierarchy.ancestor q (a + 1) =
        U.hierarchy.parentNode (U.hierarchy.ancestor q a) := by
      exact Function.iterate_succ_apply' _ _ _
    rw [hroles, wordPlacement, ha, AffineEquiv.trans_assoc,
      ← host_step_step2_port_sites_step1_parent_frame]
    exact ih

/-- Step 1 of the V4 proof of `host_step_step2_port_sites` (V4 3.6(2c)):
"a site ... recorded in u_m's profile". The canonical site is placed by the
serving child's full frame, on its recorded side. -/
private theorem host_step_step2_port_sites_step1_site_frame
    (U : HonestSource S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (a : Fin P.N) :
    U.sitePoint P q f hf a =
      (U.hierarchy.servingChild q f hf).2.val.prototypeFrame
        (U.hierarchy.servingChild q f hf).1
        (P.sites (U.recordIncidence P q f hf) (U.recordSide P q f hf) a) := by
  have hr : (U.recordIncidence P q f hf).val.sideRole (U.recordSide P q f hf) =
      U.hierarchy.nodeRole (U.hierarchy.servingChild q f hf) :=
    (Classical.choose_spec (U.recordSide_exists P q f hf)).1
  rw [host_step_step2_port_sites_step1_parent_frame]
  change _ = (U.hierarchy.birthParent q f hf).2.val.prototypeFrame
    (U.hierarchy.birthHeight q f hf)
    (rolePlacement (U.hierarchy.nodeRole (U.hierarchy.servingChild q f hf))
      (P.sites (U.recordIncidence P q f hf) (U.recordSide P q f hf) a))
  rw [← hr]
  simp [HonestSource.sitePoint, HonestSource.providerPlacement, Params.incidencePlacement,
    Params.canonicalSite, rolePlacement, PrimitiveIncidence.sideRole]

/-- Step 1 of the V4 proof of `host_step_step2_port_sites` (V4 3.6(2c)):
"a site ... recorded in u_m's profile". The shallow word pulls the actual
source site back to the recording node's prototype. -/
private theorem host_step_step2_port_sites_step1_shallow_site
    (U : HonestSource S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (w : ShortProfile P)
    (hw : (U.recordOf P q f hf).counter = .inr w) (a : Fin P.N) :
    U.sitePoint P q f hf a = q.2.val.prototypeFrame q.1
      ((wordPlacement w.word).symm
        (P.sites (U.recordOf P q f hf).incidence (U.recordOf P q f hf).sideIndex a)) := by
  have hword : w.word = U.downRoles q (U.hierarchy.firstProvider q f hf).1 := by
    change U.counterProfile P q f hf = .inr w at hw
    unfold HonestSource.counterProfile at hw
    dsimp only at hw
    split at hw
    · cases Sum.inr.inj hw
      rfl
    · contradiction
  rw [hword, host_step_step2_port_sites_step1_word_frame U q
    (U.hierarchy.firstProvider q f hf).1]
  simpa only [AffineEquiv.trans_apply, AffineEquiv.apply_symm_apply] using
    host_step_step2_port_sites_step1_site_frame U q f hf a

omit [Fact (2 ≤ d)] in
/-- Step 2 of the V4 proof of `host_step_step2_port_sites` (V4 3.6(2c)):
"q a site in relint e_m". Relative interiors commute with the full affine
frames, including the anisotropic source frames. -/
private theorem host_step_step2_port_sites_step2_relint_image
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

/-- Step 2 of the V4 proof of `host_step_step2_port_sites` (V4 3.6(2c)):
"there are exactly κ⁺(e_m)-κ⁻(e_m) of them". Transport the honest source
count to the recording prototype using its shallow word. -/
private theorem host_step_step2_port_sites_step2_source_count
    (U : HonestSource S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (e : PrototypeEdge S q.2.val.ty)
    (he : (U.recordOf P q f hf).ChainActive (edgeCell e)) (w : ShortProfile P)
    (hw : (U.recordOf P q f hf).counter = .inr w) :
    (U.recordOf P q f hf).kappaPlus e = (U.recordOf P q f hf).kappaMinus e +
      (by classical exact (Finset.univ.filter (fun a : Fin P.N =>
        (wordPlacement w.word).symm
          (P.sites (U.recordOf P q f hf).incidence (U.recordOf P q f hf).sideIndex a)
            ∈ relint e.val.carrier)).card) := by
  classical
  have hcount := honest_counter_jump_count U P q f hf e he
  have hle := (honest_counter_germs U P q f hf e he).1
  have hfilter : (Finset.univ.filter (fun a : Fin P.N =>
      U.sitePoint P q f hf a ∈ relint (q.2.val.cell q.1 e.val))) =
      Finset.univ.filter (fun a : Fin P.N =>
        (wordPlacement w.word).symm
          (P.sites (U.recordOf P q f hf).incidence (U.recordOf P q f hf).sideIndex a)
            ∈ relint e.val.carrier) := by
    apply Finset.filter_congr
    intro a _
    rw [host_step_step2_port_sites_step1_shallow_site U q f hf w hw,
      FramedNode.cell, host_step_step2_port_sites_step2_relint_image]
    exact (q.2.val.prototypeFrame q.1).injective.mem_set_image
  rw [hfilter] at hcount
  omega

/-- Step 2 of the V4 proof of `host_step_step2_port_sites` (V4 3.6(2c)):
"there are exactly κ⁺(e_m)-κ⁻(e_m) of them". An honest state readout has
the source count, independently of the chosen realization. -/
private theorem host_step_step2_port_sites_step2_readout_count
    (s : State P) (hs : s ∈ honestStates S P) (F : Cell d)
    (r : FacetRecord P) (hr : stateRecordAt s F = some r)
    (e : PrototypeEdge S r.ty) (he : r.ChainActive (edgeCell e))
    (w : ShortProfile P) (hw : r.counter = .inr w) :
    r.kappaPlus e = r.kappaMinus e +
      (by classical exact (Finset.univ.filter (fun a : Fin P.N =>
        (wordPlacement w.word).symm (P.sites r.incidence r.sideIndex a)
          ∈ relint e.val.carrier)).card) := by
  classical
  obtain ⟨U, q, rfl⟩ := hs
  unfold stateRecordAt at hr
  split at hr
  · change U.facetRecordOf P q _ = some r at hr
    unfold HonestSource.facetRecordOf at hr
    split at hr
    · contradiction
    · cases Option.some.inj hr
      exact host_step_step2_port_sites_step2_source_count U q _ _ e he w hw
  · contradiction

/-- Step 3 of the V4 proof of `host_step_step2_port_sites` (V4 3.6(2c)):
"there are exactly κ⁺(e_m)-κ⁻(e_m) of them". Strictly ordered sites
are distinct, so taking their image does not lose any events. -/
private theorem host_step_step2_port_sites_step3_sites_injective
    (ι : P.Incidence) (b : Bool) : Function.Injective (P.sites ι b) := by
  intro i j hij
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have ho := P.sites_order ι b i j hlt
    rw [hij, sub_self, inner_zero_right] at ho
    exact lt_irrefl _ ho
  · have ho := P.sites_order ι b j i hlt
    rw [hij, sub_self, inner_zero_right] at ho
    exact lt_irrefl _ ho

/-- Step 2 of the V4 proof of `host_step` (V4 3.6(2c)): "there are exactly
κ⁺(e_m)-κ⁻(e_m) of them". This is the honest single-port counter jump count,
expressed in the native tile's frame; mature profiles contribute no interior site. -/
private theorem host_step_step2_port_sites
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (H : FramedNode S)
    (ι : P.Incidence) (b : Bool) (u : host_step_Port C)
    (hu : host_step_portValid Y n H ι b u) :
    ∃ J : Finset (E d),
      u.2.1.kappaPlus (host_step_edge u.2) =
        u.2.1.kappaMinus (host_step_edge u.2) + J.card ∧
      ∀ x ∈ J, host_step_localJump u x := by
  classical
  cases hcounter : u.2.1.counter with
  | inl c =>
    refine ⟨∅, ?_, ?_⟩
    · simp [FacetRecord.kappaPlus, FacetRecord.kappaMinus, hcounter]
    · simp
  | inr w =>
    let A := Finset.univ.filter (fun a : Fin P.N =>
      (wordPlacement w.word).symm (P.sites u.2.1.incidence u.2.1.sideIndex a)
        ∈ relint (host_step_edge u.2).val.carrier)
    let point := fun a : Fin P.N => compilerFrame C u.1
      ((wordPlacement w.word).symm (P.sites u.2.1.incidence u.2.1.sideIndex a))
    have hs : (compilerLeaf C u.1).prePattern.state ∈ honestStates S P :=
      (prePattern_components_honest P _
        ((certificate_components_honest P (compilerLeaf C u.1).1.val
          (compilerLeaf C u.1).1.property).1 (compilerLeaf C u.1).2)).1
    have hcount := host_step_step2_port_sites_step2_readout_count _ hs
      u.2.1.facet.val u.2.1 hu.2.1 (host_step_edge u.2)
      ⟨u.2.2, hu.2.2.2.1, rfl⟩ w hcounter
    have hinj : Function.Injective point :=
      (compilerFrame C u.1).injective.comp ((wordPlacement w.word).symm.injective.comp
        (host_step_step2_port_sites_step3_sites_injective u.2.1.incidence u.2.1.sideIndex))
    refine ⟨A.image point, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj]
      exact hcount
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      refine ⟨w, hcounter, a, rfl, ?_⟩
      have hframe : (tileNode u.1).prototypeFrame 0 =
          (compilerFrame C u.1).toAffineEquiv := by
        ext z
        simp [FramedNode.prototypeFrame, tileNode]
      change point a ∈ relint ((tileNode u.1).prototypeFrame 0 ''
        (host_step_edge u.2).val.carrier)
      rw [hframe, host_step_step2_port_sites_step2_relint_image]
      exact ⟨_, (Finset.mem_filter.mp ha).2, rfl⟩

/-- Step 2 of the V4 proof of `host_step` (V4 3.6(2c), sharpened in 8.3):
"the strand gives N distinct jump locations". Interior sites are in disjoint
open strand edges; unit CONT jumps are at distinct internal junctions. -/
private theorem host_step_step2_distinct_jumps
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (H : FramedNode S)
    (ι : P.Incidence) (b : Bool) (m : ℕ) (u : Fin (m + 1) → host_step_Port C)
    (hu : host_step_strand Y n H ι b m u) :
    ∃ J : Finset (E d), P.N ≤ J.card ∧
      ∀ x ∈ J, x ∈ relint (host_step_flagEdge H n ι b) ∧ host_step_jump u x := by
  classical
  rcases hu with ⟨hvalid, _, _, hzero, hlast, hcont, _, hdisj, _,
    hinj, hvertices, havoid, hinside⟩
  choose sites hcount hsites using
    fun i => host_step_step2_port_sites Y n H ι b (u i) (hvalid i)
  let lo := fun i => (u i).2.1.kappaMinus (host_step_edge (u i).2)
  let hi := fun i => (u i).2.1.kappaPlus (host_step_edge (u i).2)
  let vertex := fun i : Fin m => (host_step_portEnds (u i.castSucc)).2
  let jump := fun i : Fin m => lo i.succ = hi i.castSucc + 1
  let V : Finset (Fin m) := Finset.univ.filter jump
  let A := Finset.univ.biUnion sites
  let E := V.image vertex
  have hlocal : ∀ i x, x ∈ sites i → x ∈ relint (host_step_portEdge (u i)) := by
    intro i x hx
    obtain ⟨w, hw, k, hk, hx⟩ := hsites i x hx
    exact hx
  have hpair : ((Finset.univ : Finset (Fin (m + 1))) : Set (Fin (m + 1))).PairwiseDisjoint
      sites := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp (hdisj hij) (hlocal i x hxi) (hlocal j x hxj)
  have hAE : Disjoint A E := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxE
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hxA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hxE
    exact havoid j i (hlocal i (vertex j) hxi)
  have hsum : (∑ i, hi i) = (∑ i, lo i) + ∑ i, (sites i).card := by
    simp_rw [show ∀ i, hi i = lo i + (sites i).card from hcount]
    exact Finset.sum_add_distrib
  have hjump : ∀ i : Fin m, lo i.succ = hi i.castSucc + if jump i then 1 else 0 := by
    intro i
    obtain h | h := (hcont i).2
    · have hj : ¬ jump i := by dsimp [jump, lo, hi]; omega
      simp only [hj, ↓reduceIte, add_zero]
      exact h
    · have hj : jump i := h
      simp only [hj, ↓reduceIte]
      exact h
  have hsumCont : (∑ i : Fin m, lo i.succ) =
      (∑ i : Fin m, hi i.castSucc) + V.card := by
    simp_rw [hjump]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter]
    simp [V]
  have htel : (∑ i, (sites i).card) + V.card = P.N := by
    rw [Fin.sum_univ_castSucc] at hsum
    rw [Fin.sum_univ_succ] at hsum
    change lo 0 = 0 at hzero
    change hi (Fin.last m) = P.N at hlast
    omega
  have hcard : (A ∪ E).card = P.N := by
    rw [Finset.card_union_of_disjoint hAE, Finset.card_biUnion hpair,
      Finset.card_image_of_injective V hinj]
    exact htel
  refine ⟨A ∪ E, hcard.ge, ?_⟩
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    exact ⟨hinside i (hlocal i x hxi), Or.inl ⟨i, hsites i x hxi⟩⟩
  · obtain ⟨i, hiV, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hvertices i, Or.inr ⟨i, rfl, (Finset.mem_filter.mp hiV).2⟩⟩

/-- Step 3 of the V4 proof of `host_step` (V4 3.6): "the opposite root
edges"; "they have disjoint relative interiors, lie in h, and cover h".
This lifts the entire chain of each strand port to its chosen level-n block.
Endpoint END rows exclude a root edge extending beyond either end of h. -/
private theorem host_step_step3_roots (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) (m : ℕ)
    (u : Fin (m + 1) → host_step_Port C)
    (hu : host_step_strand Y n (proposedSibling D B hB f a)
      a.record.incidence (!a.record.sideIndex) m u) :
    ∃ q : ℕ, ∃ R : Fin q → host_step_Root D, ∃ owner : Fin (m + 1) → Fin q,
      host_step_rootCover D (proposedSibling D B hB f a)
        a.record.incidence (!a.record.sideIndex) u R owner := by
  sorry

/-- Step 3 of the V4 proof of `host_step` (V4 3.6): "that record is finite".
A successful cell-keyed readout supplies a genuine facet of the state. -/
private theorem host_step_step3_readout (s : State P) (F : Cell d)
    (r : FacetRecord P) (hr : stateRecordAt s F = some r) :
    ∃ f : FacetName S s.ty, f.val = F ∧ s.facetRecord f = some r := by
  classical
  unfold stateRecordAt at hr
  split at hr
  · exact ⟨_, rfl, hr⟩
  · contradiction

/-- Step 3 of the V4 proof of `host_step` (V4 3.6): "by Corollary 1.21
... q ≤ M". Reachability comes from the actual root record's active chain. -/
private theorem host_step_step3_root_bound
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) (hD : Inv D)
    (H : FramedNode S) (ι : P.Incidence) (b : Bool) (hH : H.ty = ι.val.sideType b)
    {m q : ℕ} (u : Fin (m + 1) → host_step_Port C)
    (R : Fin q → host_step_Root D) (owner : Fin (m + 1) → Fin q)
    (hR : host_step_rootCover D H ι b u R owner) : q ≤ P.M := by
  classical
  let e : PrototypeEdge S H.ty := ⟨((P.sideFlag ι b).cell edgeIndex).val, by
    rw [hH]
    simp only [CellComplex.edges, Finset.mem_filter]
    exact ⟨((P.sideFlag ι b).cell edgeIndex).property,
      (P.sideFlag ι b).dimension edgeIndex⟩⟩
  let es : ∀ j : Fin q, PrototypeEdge S (R j).1.val.node.ty := fun j =>
    ⟨(host_step_edge (R j).2).val, by
      rw [← (hR.1 j).2.1]
      exact (host_step_edge (R j).2).property⟩
  have edge_eq : ∀ e f : EdgeName S, e.1 = f.1 → e.2.val = f.2.val → e = f := by
    rintro ⟨A, e⟩ ⟨A', f⟩ hty he
    cases hty
    congr
    exact Subtype.ext he
  have hreach : ∀ j, Relation.ReflTransGen (edgeGraph S)
      ⟨H.ty, e⟩ ⟨(R j).1.val.node.ty, es j⟩ := by
    intro j
    have hv := hR.1 j
    obtain ⟨f, _, hf⟩ := host_step_step3_readout _ _ _ hv.1
    have he : (R j).2.1.ChainActive (edgeCell (host_step_edge (R j).2)) :=
      ⟨(R j).2.2, hv.2.2.1, rfl⟩
    obtain ⟨e', he', hreach⟩ := state_semantics_d P _
      (hD.I1 (R j).1.val (R j).1.property).1 f _ hf (host_step_edge (R j).2) he
    have hsource : (⟨(R j).2.1.incidence.val.sideType (R j).2.1.sideIndex, e'⟩ :
        EdgeName S) = ⟨H.ty, e⟩ := by
      apply edge_eq
      · change (R j).2.1.incidence.val.sideType (R j).2.1.sideIndex = H.ty
        rw [hv.2.2.2.1, hv.2.2.2.2.1, hH]
      · change e'.val = ((P.sideFlag ι b).cell edgeIndex).val
        exact he'.trans (by rw [hv.2.2.2.1, hv.2.2.2.2.1])
    have htarget : (⟨(R j).2.1.ty, host_step_edge (R j).2⟩ : EdgeName S) =
        ⟨(R j).1.val.node.ty, es j⟩ := edge_eq _ _ hv.2.1 rfl
    rw [hsource, htarget] at hreach
    exact hreach
  have hbound := opposite_root_edges_bound P.edgeBounds n H e
    (fun j => (R j).1.val.node) es hR.2.1 hR.2.2.1 hreach
  simpa only [Fintype.card_fin, ← P.M_eq] using hbound

/-- Step 4 of the V4 proof of `host_step` (V4 3.6): "relint c".
In real interval coordinates the relative interior is the open interval. -/
private theorem host_step_step4_intrinsic_interval (a b : ℝ) (hab : a < b) :
    intrinsicInterior ℝ (Icc a b) = Ioo a b := by
  have hspan : affineSpan ℝ (Icc a b) = ⊤ :=
    (convex_Icc a b).interior_nonempty_iff_affineSpan_eq_top.mp
      (by rw [interior_Icc]; exact nonempty_Ioo.mpr hab)
  rw [intrinsicInterior, hspan]
  change (Homeomorph.Set.univ ℝ) ''
    interior ((Homeomorph.Set.univ ℝ) ⁻¹' Icc a b) = Ioo a b
  rw [(Homeomorph.Set.univ ℝ).image_interior]
  simp

/-- Step 4 of the V4 proof of `host_step` (V4 3.6): "h ... into ... intervals".
A nondegenerate placed segment has an isometric real interval coordinate,
including its relative interior. -/
private theorem host_step_step4_segment_chart (p q : E d) (hpq : p ≠ q) :
    ∃ (φ : ℝ →ᵃⁱ[ℝ] E d) (L : ℝ), 0 < L ∧
      segment ℝ p q = φ '' Icc 0 L ∧ relint (segment ℝ p q) = φ '' Ioo 0 L := by
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
  refine ⟨φ, L, hL, hseg, ?_⟩
  rw [hseg, relint, φ.image_intrinsicInterior, host_step_step4_intrinsic_interval 0 L hL]

/-- Step 4 of the V4 proof of `host_step` (V4 3.6): "at most q-1 ...
points of relint h are endpoints of these intervals". For a finite interval
cover, right endpoints other than the final endpoint suffice as exceptions.
This even allows overlapping covering intervals. -/
private theorem host_step_step4_interval_cover (q : ℕ) (L : ℝ) (hL : 0 < L)
    (lo hi : Fin q → ℝ) (hbound : ∀ i, 0 ≤ lo i ∧ hi i ≤ L)
    (hcover : ∀ x ∈ Icc 0 L, ∃ i, x ∈ Icc (lo i) (hi i)) :
    ∃ E : Finset ℝ, E.card < q ∧
      ∀ x ∈ Ioo 0 L, x ∉ E → ∃ i, x ∈ Ioo (lo i) (hi i) := by
  classical
  let F := Finset.univ.filter (fun i => hi i < L)
  let E := F.image hi
  obtain ⟨j, hj⟩ := hcover L ⟨hL.le, le_rfl⟩
  have hjL : hi j = L := (hbound j).2.antisymm hj.2
  have hjnot : j ∉ F := by simp [F, hjL]
  have hss : F ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    exact hjnot (heq.symm ▸ Finset.mem_univ j)
  have hcard : E.card < q := by
    have hc := (Finset.card_image_le (s := F) (f := hi)).trans_lt (Finset.card_lt_card hss)
    simpa only [Finset.card_univ, Fintype.card_fin] using hc
  refine ⟨E, hcard, ?_⟩
  intro x hx hxE
  let G := Finset.univ.filter (fun i => lo i < x)
  let U := ⋃ i ∈ G, Icc (lo i) (hi i)
  have hclosed : IsClosed U := isClosed_biUnion_finset (fun _ _ => isClosed_Icc)
  have hsub : Ioo 0 x ⊆ U := by
    intro y hy
    obtain ⟨i, hi⟩ := hcover y ⟨hy.1.le, (hy.2.trans hx.2).le⟩
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.1.trans_lt hy.2⟩, hi⟩⟩
  have hxcl : x ∈ closure (Ioo 0 x) := by
    rw [closure_Ioo hx.1.ne]
    exact ⟨hx.1.le, le_rfl⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (closure_minimal hsub hclosed hxcl)
  obtain ⟨hiG, hxi⟩ := Set.mem_iUnion.mp hxi
  have hlo : lo i < x := (Finset.mem_filter.mp hiG).2
  have hhi : x < hi i := by
    by_contra h
    have heq : x = hi i := le_antisymm hxi.2 (le_of_not_gt h)
    apply hxE
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, heq ▸ hx.2⟩, heq.symm⟩
  exact ⟨i, hlo, hhi⟩

/-- Step 4 of the V4 proof of `host_step` (V4 3.6): "at most q-1 ...
points of relint h are endpoints of these intervals". This is only the
one-dimensional partition assertion; no counter or age assertion is included. -/
private theorem host_step_step4_partition_endpoints
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)
    (H : FramedNode S) (ι : P.Incidence) (b : Bool)
    {m q : ℕ} (u : Fin (m + 1) → host_step_Port C)
    (R : Fin q → host_step_Root D) (owner : Fin (m + 1) → Fin q)
    (hR : host_step_rootCover D H ι b u R owner) :
    ∃ E : Finset (E d), E.card < q ∧
      ∀ x ∈ relint (host_step_flagEdge H n ι b), x ∉ E →
        ∃ j, x ∈ relint (host_step_rootEdge (R j)) := by
  classical
  let e : PrototypeEdge S (ι.val.sideType b) :=
    ⟨((P.sideFlag ι b).cell edgeIndex).val, by
      simp only [CellComplex.edges, Finset.mem_filter]
      exact ⟨((P.sideFlag ι b).cell edgeIndex).property,
        (P.sideFlag ι b).dimension edgeIndex⟩⟩
  obtain ⟨ab, hab, he⟩ := edge_endpoints_exist (⟨ι.val.sideType b, e⟩ : EdgeName S)
  have hseg : host_step_flagEdge H n ι b =
      segment ℝ (H.prototypeFrame n ab.1) (H.prototypeFrame n ab.2) := by
    change H.prototypeFrame n '' e.val.carrier = _
    rw [he]
    exact image_segment ℝ (H.prototypeFrame n).toAffineMap _ _
  obtain ⟨φ, L, hL, hchart, hrel⟩ := host_step_step4_segment_chart
    (H.prototypeFrame n ab.1) (H.prototypeFrame n ab.2)
    (fun h => hab ((H.prototypeFrame n).injective h))
  have hedge : host_step_flagEdge H n ι b = φ '' Icc 0 L := hseg.trans hchart
  have hrel' : relint (host_step_flagEdge H n ι b) = φ '' Ioo 0 L := by
    rw [hseg, hrel]
  have intervals : ∀ i : Fin q, ∃ lo hi : ℝ, lo < hi ∧ 0 ≤ lo ∧ hi ≤ L ∧
      host_step_rootEdge (R i) = φ '' Icc lo hi := by
    intro i
    obtain ⟨cd, hcd, he⟩ := edge_endpoints_exist
      (⟨(R i).2.1.ty, host_step_edge (R i).2⟩ : EdgeName S)
    let Ψ := (R i).1.val.node.prototypeFrame n
    have hroot : host_step_rootEdge (R i) = segment ℝ (Ψ cd.1) (Ψ cd.2) := by
      change Ψ '' (host_step_edge (R i).2).val.carrier = _
      rw [he]
      exact image_segment ℝ Ψ.toAffineMap _ _
    have hleft : Ψ cd.1 ∈ φ '' Icc 0 L := by
      rw [← hedge]
      apply hR.2.1 i
      rw [hroot]
      exact left_mem_segment ℝ _ _
    have hright : Ψ cd.2 ∈ φ '' Icc 0 L := by
      rw [← hedge]
      apply hR.2.1 i
      rw [hroot]
      exact right_mem_segment ℝ _ _
    obtain ⟨a, ha, hea⟩ := hleft
    obtain ⟨b, hb, heb⟩ := hright
    have hab : a ≠ b := by
      intro h
      apply hcd
      apply Ψ.injective
      rw [← hea, ← heb, h]
    refine ⟨min a b, max a b, min_lt_max.mpr hab, le_min ha.1 hb.1,
      max_le ha.2 hb.2, ?_⟩
    rw [hroot, ← hea, ← heb]
    simpa only [AffineIsometry.coe_toAffineMap, segment_eq_Icc'] using
      (image_segment ℝ φ.toAffineMap a b).symm
  choose lo hi hlt hlo hhi heq using intervals
  have hcover : ∀ x ∈ Icc 0 L, ∃ i, x ∈ Icc (lo i) (hi i) := by
    intro x hx
    have hmem : φ x ∈ host_step_flagEdge H n ι b := hedge.symm ▸ ⟨x, hx, rfl⟩
    rw [← hR.2.2.2.1] at hmem
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
    rw [heq i] at hi
    obtain ⟨y, hy, hxy⟩ := hi
    exact ⟨i, φ.injective hxy ▸ hy⟩
  obtain ⟨E, hE, hcover⟩ := host_step_step4_interval_cover q L hL lo hi
    (fun i => ⟨hlo i, hhi i⟩) hcover
  refine ⟨E.image φ, (Finset.card_image_le).trans_lt hE, ?_⟩
  intro x hx hxE
  rw [hrel'] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨i, hi⟩ := hcover t ht (fun h => hxE (Finset.mem_image_of_mem φ h))
  refine ⟨i, ?_⟩
  rw [heq i, relint, φ.image_intrinsicInterior,
    host_step_step4_intrinsic_interval _ _ (hlt i)]
  exact ⟨t, hi, rfl⟩

/-- Step 4 of the V4 proof of `host_step` (V4 3.6, 8.3): "N=M still
forces a jump inside one root edge". The strict inequality also covers q=1. -/
private theorem host_step_step4_pigeonhole (J E : Finset (E d)) (q : ℕ)
    (hJ : P.N ≤ J.card) (hE : E.card < q) (hq : q ≤ P.M) :
    ∃ x ∈ J, x ∉ E := by
  classical
  by_contra h
  have hsub : J ⊆ E := by
    intro x hx
    by_contra hxE
    exact h ⟨x, hx, hxE⟩
  have := Finset.card_le_card hsub
  have := P.N_eq
  omega

/-- Step 4 of the V4 proof of `host_step` (V4 3.6): "the germs ... are
restrictions of the profile of c". An interior site or an interior unit CONT
jump makes the containing root profile nonconstant, by I2 and site persistence. -/
private theorem host_step_step4_lift_jump
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) (hD : Inv D)
    (H : FramedNode S) (ι : P.Incidence) (b : Bool)
    {m q : ℕ} (u : Fin (m + 1) → host_step_Port C)
    (hu : host_step_strand Y n H ι b m u)
    (R : Fin q → host_step_Root D) (owner : Fin (m + 1) → Fin q)
    (hR : host_step_rootCover D H ι b u R owner)
    (x : E d) (hx : host_step_jump u x) (j : Fin q)
    (hj : x ∈ relint (host_step_rootEdge (R j))) :
    (R j).2.1.kappaPlus (host_step_edge (R j).2) ≠
      (R j).2.1.kappaMinus (host_step_edge (R j).2) := by
  sorry

/-- Step 4 of the V4 proof of `host_step` (V4 3.6): "a ≡ 0 mod L ...
a=0". A nonconstant honest root profile with β equal to the root residue has
uncapped age one, hence the full age-one record semantics. -/
private theorem host_step_step4_age_one (s : State P) (hs : s ∈ honestStates S P)
    (z : host_step_Chain P) (hr : stateRecordAt s z.1.facet.val = some z.1)
    (hc : z.2 ∈ z.1.chains) (hbeta : z.1.beta = s.residue)
    (hjump : z.1.kappaPlus (host_step_edge z) ≠ z.1.kappaMinus (host_step_edge z)) :
    AgeOneRecord s z.1 := by
  obtain ⟨f, _, hf⟩ := host_step_step3_readout s z.1.facet.val z.1 hr
  have he : z.1.ChainActive (edgeCell (host_step_edge z)) := ⟨z.2, hc, rfl⟩
  obtain ⟨w, _, _, hage, _, hcap⟩ :=
    state_semantics_c P s hs f z.1 hf (host_step_edge z) he hjump
  have hmod := state_semantics_e P s hs f z.1 hf hcap
  have hcong : Nat.ModEq P.L (s.residue.val + w.word.length) (s.residue.val + 0) := by
    rw [hbeta, hage] at hmod
    simpa [Nat.ModEq, Nat.add_assoc, Nat.mod_eq_of_lt s.residue.isLt] using hmod.symm
  have hlen : w.word.length < P.L := by
    have := w.length_lt
    rw [P.L_eq]
    omega
  have hw : w.word.length = 0 :=
    (Nat.ModEq.add_left_cancel' s.residue.val hcong).eq_of_lt_of_lt hlen P.L_pos
  exact ((state_semantics_a P s hs f).2 z.1 hf (by omega)).2

omit [Fact (2 ≤ d)] in
/-- Step 1 of the V4 proof of `host_step_step4_age_one_flag` (V4 3.6):
"the flag cells themselves" have unique cell names once their carriers agree. -/
private theorem host_step_step4_age_one_flag_step1_cell_ext {e f : Cell d}
    (h : e.carrier = f.carrier) : e = f := by
  rcases e with ⟨K, n, hn⟩
  rcases f with ⟨K', n', hn'⟩
  cases h
  have hd : n = n' := hn.dimension.symm.trans hn'.dimension
  cases hd
  rfl

/-- Step 2 of the V4 proof of `host_step_step4_age_one_flag` (V4 2.3):
"the active chains of an age-one record are the flag cells themselves".
The active stratum and the age-one identity determine each positioned cell. -/
private theorem host_step_step4_age_one_flag_step2_cells (U : HonestSource S)
    (q : U.Node) (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (c : OrientedChain f) (hc : U.ActiveChain P q f hf c)
    (ha : AgeOneRecord (stateOf U P q) (U.recordOf P q f hf)) (j : FlagIndex d) :
    (c.chain.val.cell j).val =
      ((P.sideFlag (U.recordIncidence P q f hf) (U.recordSide P q f hf)).cell j).val := by
  let r := U.recordOf P q f hf
  let e : CellsInFacet q.2.val.ty f := ⟨c.chain.val.cell j, r.chain_cell_subset c j⟩
  obtain ⟨hs, hstratum, _⟩ := hc.1 j
  have htau : (r.tau e).val.val.carrier =
      ((P.flag r.incidence).flag.cell j).val.carrier := by
    apply (U.providerPlacement P q f hf).injective.image_injective
    exact (record_tau_spec U P q f hf e).trans hstratum
  have hplaced := ha.2.2.2.2.1 e
  change placedSet (S.child r.incidence.val.ty r.incidence.val.left).frame
      (r.tau e).val.val.carrier =
    placedSet (S.child r.side.1 r.side.2).frame (c.chain.val.cell j).val.carrier at hplaced
  rw [htau, r.side_eq] at hplaced
  apply host_step_step4_age_one_flag_step1_cell_ext
  apply (S.child r.incidence.val.ty (r.incidence.val.sideIndex r.sideIndex)).frame.injective.image_injective
  exact hplaced.symm.trans (P.sideFlag_eq r.incidence r.sideIndex j).symm

/-- Step 3 of the V4 proof of `host_step_step4_age_one_flag` (V4 2.3):
"internal case": the provider is born in the immediate parent. Its canonical
placement is the side change followed by the node's full prototype frame. -/
private theorem host_step_step4_age_one_flag_step3_frame (U : HonestSource S)
    (q : U.Node) (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (ha : AgeOneRecord (stateOf U P q) (U.recordOf P q f hf)) :
    U.providerPlacement P q f hf =
      ((S.child (U.recordIncidence P q f hf).val.ty
          (U.recordIncidence P q f hf).val.left).frame.toAffineEquiv.trans
        (S.child (U.recordIncidence P q f hf).val.ty
          ((U.recordIncidence P q f hf).val.sideIndex
            (U.recordSide P q f hf))).frame.symm.toAffineEquiv).trans
        (q.2.val.prototypeFrame q.1) := by
  let r := U.recordOf P q f hf
  have hage : U.hierarchy.age q f hf = 1 := by
    have h := ha.1
    change min (U.hierarchy.age q f hf) P.C = 1 at h
    have := P.C_gt_one
    omega
  have hoff : (U.hierarchy.firstProvider q f hf).1 = 0 := by
    have := (U.hierarchy.birthHeight_age_spec q f hf).2.1
    omega
  have hserv : U.hierarchy.servingChild q f hf = q := by
    simp only [CoherentHierarchy.servingChild, hoff, CoherentHierarchy.ancestor,
      Function.iterate_zero, id_eq]
  have hbirth : U.hierarchy.birthParent q f hf = U.hierarchy.parentNode q :=
    congrArg U.hierarchy.parentNode hserv
  have hrole : r.incidence.val.sideRole r.sideIndex = U.hierarchy.nodeRole q := by
    exact ha.2.1
  have hframe : q.2.val.prototypeFrame q.1 =
      (rolePlacement (U.hierarchy.nodeRole q)).trans
        ((U.hierarchy.parentNode q).2.val.prototypeFrame (q.1 + 1)) := by
    rw [U.hierarchy.child_eq q.1 q.2]
    apply AffineEquiv.ext
    intro x
    change (U.hierarchy.parent q.1 q.2).val.frame
        (S.placeChild q.1 (U.hierarchy.role q.1 q.2) ((S.σ ^ q.1) x)) =
      (U.hierarchy.parent q.1 q.2).val.frame
        ((S.σ ^ (q.1 + 1)) (S.σ.symm
          ((S.child (U.hierarchy.nodeRole q).1 (U.hierarchy.nodeRole q).2).frame x)))
    congr 1
    rw [S.placeChild_apply]
    simp [linearConj, Child.frame, rigidMotion, pow_succ, zpow_neg,
      LinearEquiv.mul_apply, ← map_add, CoherentHierarchy.nodeRole]
  calc
    _ = (rolePlacement ⟨r.incidence.val.ty, r.incidence.val.left⟩).trans
        ((U.hierarchy.birthParent q f hf).2.val.prototypeFrame
          (U.hierarchy.birthParent q f hf).1) := by
      apply AffineEquiv.ext
      intro x
      rfl
    _ = (rolePlacement ⟨r.incidence.val.ty, r.incidence.val.left⟩).trans
        ((U.hierarchy.parentNode q).2.val.prototypeFrame (q.1 + 1)) := by rw [hbirth]; rfl
    _ = _ := by
      rw [hframe, ← hrole]
      apply AffineEquiv.ext
      intro x
      change (U.hierarchy.parentNode q).2.val.prototypeFrame (q.1 + 1)
          (S.σ.symm ((S.child r.incidence.val.ty r.incidence.val.left).frame x)) =
        (U.hierarchy.parentNode q).2.val.prototypeFrame (q.1 + 1)
          (S.σ.symm ((S.child r.incidence.val.ty (r.incidence.val.sideIndex r.sideIndex)).frame
            ((S.child r.incidence.val.ty (r.incidence.val.sideIndex r.sideIndex)).frame.symm
              ((S.child r.incidence.val.ty r.incidence.val.left).frame x))))
      rw [AffineIsometryEquiv.apply_symm_apply]

omit [Fact (2 ≤ d)] in
/-- Step 4 of the V4 proof of `host_step_step4_age_one_flag` (V4 3.6):
"the flag edge" has only its two endpoint orderings. -/
private theorem host_step_step4_age_one_flag_step4_endpoints (p q a b : E d)
    (hpq : p ≠ q) (h : segment ℝ a b = segment ℝ p q) :
    (a = p ∧ b = q) ∨ (a = q ∧ b = p) := by
  let φ : ℝ →ᵃ[ℝ] E d := AffineMap.lineMap p q
  have hφ : Function.Injective φ := AffineMap.lineMap_injective ℝ hpq
  have hseg : segment ℝ p q = φ '' Icc 0 1 := segment_eq_image_lineMap ℝ p q
  obtain ⟨u, hu, heu⟩ := hseg ▸ h ▸ left_mem_segment ℝ a b
  obtain ⟨v, hv, hev⟩ := hseg ▸ h ▸ right_mem_segment ℝ a b
  have hab : segment ℝ a b = φ '' Icc (min u v) (max u v) := by
    rw [← heu, ← hev]
    simpa only [segment_eq_Icc'] using (image_segment ℝ φ u v).symm
  have hi : Icc (min u v) (max u v) = Icc (0 : ℝ) 1 :=
    hφ.image_injective (hab.symm.trans (h.trans hseg))
  have hlo : min u v = 0 := by
    have hleft := hi ▸ (left_mem_Icc.mpr (show min u v ≤ max u v from min_le_max))
    have hzero := hi.symm ▸ (left_mem_Icc.mpr (show (0 : ℝ) ≤ 1 by norm_num))
    exact le_antisymm hzero.1 hleft.1
  have hhi : max u v = 1 := by
    have hright := hi ▸ (right_mem_Icc.mpr (show min u v ≤ max u v from min_le_max))
    have hone := hi.symm ▸ (right_mem_Icc.mpr (show (0 : ℝ) ≤ 1 by norm_num))
    exact le_antisymm hright.2 hone.2
  rcases le_total u v with huv | hvu
  · have hu0 : u = 0 := by simpa only [min_eq_left huv] using hlo
    have hv1 : v = 1 := by simpa only [max_eq_right huv] using hhi
    left
    simpa only [hu0, hv1, φ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
      using And.intro heu.symm hev.symm
  · have hv0 : v = 0 := by simpa only [min_eq_right hvu] using hlo
    have hu1 : u = 1 := by simpa only [max_eq_left hvu] using hhi
    right
    simpa only [hu1, hv0, φ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
      using And.intro heu.symm hev.symm

/-- Step 5 of the V4 proof of `host_step_step4_age_one_flag` (V4 2.3):
"with inherited orientations". The active-chain sign selects the ordering
of the two flag endpoints in the full placed frame. -/
private theorem host_step_step4_age_one_flag_step5_orientation (U : HonestSource S)
    (q : U.Node) (f : FacetName S q.2.val.ty) (hf : ¬ U.hierarchy.IsFault q f)
    (c : OrientedChain f) (hc : U.ActiveChain P q f hf c)
    (ha : AgeOneRecord (stateOf U P q) (U.recordOf P q f hf))
    (he : (c.chain.val.cell edgeIndex).val =
      ((P.sideFlag (U.recordIncidence P q f hf) (U.recordSide P q f hf)).cell edgeIndex).val) :
    chainVector c = (U.recordOf P q f hf).servingDirection := by
  let r := U.recordOf P q f hf
  let ψ : Iso d := (S.child r.incidence.val.ty r.incidence.val.left).frame.trans
    (S.child r.incidence.val.ty (r.incidence.val.sideIndex r.sideIndex)).frame.symm
  let a := ψ (P.flag r.incidence).initial
  let b := ψ (P.flag r.incidence).terminal
  have hab : a ≠ b := ψ.injective.ne (P.flag r.incidence).distinct
  have hdir : b - a = r.servingDirection := by
    change ψ (P.flag r.incidence).terminal - ψ (P.flag r.incidence).initial =
      ψ.linearIsometryEquiv ((P.flag r.incidence).terminal - (P.flag r.incidence).initial)
    exact (ψ.map_vsub _ _).symm
  have hcarrier : (c.chain.val.cell edgeIndex).val.carrier =
      ψ '' ((P.flag r.incidence).flag.cell edgeIndex).val.carrier := by
    apply (S.child r.incidence.val.ty (r.incidence.val.sideIndex r.sideIndex)).frame.injective.image_injective
    calc
      _ = (S.child r.incidence.val.ty r.incidence.val.left).frame ''
          ((P.flag r.incidence).flag.cell edgeIndex).val.carrier := by
        rw [he]
        exact P.sideFlag_eq r.incidence r.sideIndex edgeIndex
      _ = _ := by
        rw [Set.image_image]
        apply congrArg (fun φ : E d → E d =>
          φ '' ((P.flag r.incidence).flag.cell edgeIndex).val.carrier)
        funext x
        change (S.child r.incidence.val.ty r.incidence.val.left).frame x =
          (S.child r.incidence.val.ty (r.incidence.val.sideIndex r.sideIndex)).frame
            ((S.child r.incidence.val.ty (r.incidence.val.sideIndex r.sideIndex)).frame.symm
              ((S.child r.incidence.val.ty r.incidence.val.left).frame x))
        rw [AffineIsometryEquiv.apply_symm_apply]
  have hseg : (c.chain.val.cell edgeIndex).val.carrier = segment ℝ a b := by
    rw [hcarrier, (P.flag r.incidence).edge_eq]
    exact image_segment ℝ ψ.toAffineMap _ _
  let e : EdgeName S := ⟨q.2.val.ty, ⟨(c.chain.val.cell edgeIndex).val, by
    classical
    simp only [CellComplex.edges, Finset.mem_filter]
    exact ⟨(c.chain.val.cell edgeIndex).property, c.chain.val.dimension edgeIndex⟩⟩⟩
  let ab := Classical.choose (edge_endpoints_exist e)
  have habspec : e.2.val.carrier = segment ℝ ab.1 ab.2 :=
    (Classical.choose_spec (edge_endpoints_exist e)).2
  have hraw : edgeVector e = r.servingDirection ∨ edgeVector e = -r.servingDirection := by
    rcases host_step_step4_age_one_flag_step4_endpoints a b ab.1 ab.2 hab
      (habspec.symm.trans hseg) with ⟨hfirst, hlast⟩ | ⟨hfirst, hlast⟩
    · left
      change ab.2 - ab.1 = _
      rw [hfirst, hlast]
      exact hdir
    · right
      change ab.2 - ab.1 = _
      rw [hfirst, hlast, ← hdir]
      exact (neg_sub b a).symm
  have hframe : (U.providerPlacement P q f hf).linear (P.flag r.incidence).direction =
      (q.2.val.prototypeFrame q.1).linear r.servingDirection :=
    congrArg (fun φ : E d ≃ᵃ[ℝ] E d => φ.linear (P.flag r.incidence).direction)
      (host_step_step4_age_one_flag_step3_frame U q f hf ha)
  have hsign : c.forward = true ↔ 0 < inner ℝ
      ((q.2.val.prototypeFrame q.1).linear r.servingDirection)
      ((q.2.val.prototypeFrame q.1).linear (edgeVector e)) := by
    have h := hc.2
    change c.forward = true ↔ 0 < inner ℝ
      ((U.providerPlacement P q f hf).linear (P.flag r.incidence).direction)
      ((q.2.val.prototypeFrame q.1).linear (edgeVector e)) at h
    rwa [hframe] at h
  have hn : r.servingDirection ≠ 0 := by
    rw [← hdir]
    exact sub_ne_zero.mpr hab.symm
  have hpos : 0 < inner ℝ ((q.2.val.prototypeFrame q.1).linear r.servingDirection)
      ((q.2.val.prototypeFrame q.1).linear r.servingDirection) := by
    apply real_inner_self_pos.mpr
    simpa only [map_zero] using (q.2.val.prototypeFrame q.1).linear.injective.ne hn
  change (if c.forward then edgeVector e else -edgeVector e) = r.servingDirection
  rcases hraw with hraw | hraw
  · have hforward : c.forward = true := hsign.mpr (by rw [hraw]; exact hpos)
    simp [hforward, hraw]
  · have hforward : c.forward ≠ true := by
      intro h
      have hbad := hsign.mp h
      rw [hraw, map_neg, inner_neg_right] at hbad
      linarith
    simp [hforward, hraw]

/-- Step 6 of the V4 proof of `host_step_step4_age_one_flag` (V4 3.6):
"f is the cell g_j of A_j". The top of the side flag is its paired facet. -/
private theorem host_step_step4_age_one_flag_step6_top (ι : P.Incidence) (b : Bool) :
    ((P.sideFlag ι b).cell facetIndex).val = (ι.val.sideFacet b).val := by
  apply host_step_step4_age_one_flag_step1_cell_ext
  apply (S.child ι.val.ty (ι.val.sideIndex b)).frame.injective.image_injective
  change placedSet (S.child ι.val.ty (ι.val.sideIndex b)).frame _ = placedSet _ _
  rw [P.sideFlag_eq, (P.flag ι).top]
  cases b
  · rfl
  · exact ι.val.paired

/-- Step 4 of the V4 proof of `host_step` (V4 3.6): "the active chains
of an age-one record are the flag cells themselves". This is a statement about
one honest state in prototype coordinates, including the induced orientation. -/
private theorem host_step_step4_age_one_flag (s : State P)
    (hs : s ∈ honestStates S P) (z : host_step_Chain P)
    (hr : stateRecordAt s z.1.facet.val = some z.1) (hc : z.2 ∈ z.1.chains)
    (ha : AgeOneRecord s z.1) :
    z.1.ty = z.1.incidence.val.sideType z.1.sideIndex ∧
    z.1.facet.val = (z.1.incidence.val.sideFacet z.1.sideIndex).val ∧
    (∀ k, (z.2.chain.val.cell k).val =
      ((P.sideFlag z.1.incidence z.1.sideIndex).cell k).val) ∧
    chainVector z.2 = z.1.servingDirection := by
  classical
  obtain ⟨U, q, rfl⟩ := hs
  rcases z with ⟨r, c⟩
  obtain ⟨f, _, hrec⟩ :=
    host_step_step3_readout (stateOf U P q) r.facet.val r hr
  change U.facetRecordOf P q f = some r at hrec
  unfold HonestSource.facetRecordOf at hrec
  split at hrec
  · contradiction
  · rename_i hf
    cases Option.some.inj hrec
    have hactive : U.ActiveChain P q f hf c := (Finset.mem_filter.mp hc).2
    have hcells := host_step_step4_age_one_flag_step2_cells U q f hf c hactive ha
    have htype : (U.recordOf P q f hf).ty =
        (U.recordOf P q f hf).incidence.val.sideType (U.recordOf P q f hf).sideIndex := by
      have hrole := ha.2.1.symm.trans (U.recordOf P q f hf).side_eq
      exact (stateOf U P q).address_start.symm.trans
        (congrArg (fun r : S.Role => (S.child r.1 r.2).ty) hrole)
    refine ⟨htype, ?_, hcells, ?_⟩
    · exact c.chain.property.symm.trans ((hcells facetIndex).trans
        (host_step_step4_age_one_flag_step6_top _ _))
    · exact host_step_step4_age_one_flag_step5_orientation U q f hf c hactive ha
        (hcells edgeIndex)

/-- Step 4 of the V4 proof of `host_step` (V4 3.6): "c ⊆ h and |c|=|h|,
c=h". This metric assertion also allows a degenerate candidate subsegment;
equality of diameters with the nondegenerate containing segment excludes it. -/
private theorem host_step_step4_subsegment_eq (p q a b : E d) (hpq : p ≠ q)
    (hsub : segment ℝ a b ⊆ segment ℝ p q)
    (hdiam : diam (segment ℝ a b) = diam (segment ℝ p q)) :
    segment ℝ a b = segment ℝ p q := by
  obtain ⟨φ, L, hL, hchart, _⟩ := host_step_step4_segment_chart p q hpq
  obtain ⟨u, hu, heu⟩ := hchart ▸ hsub (left_mem_segment ℝ a b)
  obtain ⟨v, hv, hev⟩ := hchart ▸ hsub (right_mem_segment ℝ a b)
  have hab : segment ℝ a b = φ '' Icc (min u v) (max u v) := by
    rw [← heu, ← hev]
    simpa only [AffineIsometry.coe_toAffineMap, segment_eq_Icc'] using
      (image_segment ℝ φ.toAffineMap u v).symm
  rw [hab, hchart, φ.diam_image, φ.diam_image,
    Real.diam_Icc min_le_max, Real.diam_Icc hL.le, sub_zero] at hdiam
  have hlo : 0 ≤ min u v := le_min hu.1 hv.1
  have hhi : max u v ≤ L := max_le hu.2 hv.2
  have hmin : min u v = 0 := by linarith
  have hmax : max u v = L := by linarith
  rw [hab, hmin, hmax, hchart]

/-- Step 4 of the V4 proof of `host_step` (V4 3.6): "the active chains
of an age-one record are the flag cells themselves" and "c=h".
Containment of the root edge and equality of its same-height length exhaust h;
the record's keyed facet is the prescribed opposite facet. -/
private theorem host_step_step4_full_edge
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) (hD : Inv D)
    (H : FramedNode S) (ι : P.Incidence) (b : Bool) (hH : H.ty = ι.val.sideType b)
    (R : host_step_Root D) (hR : host_step_rootValid D H ι b R)
    (ha : AgeOneRecord (D.blockState R.1.val R.1.property) R.2.1)
    (hsub : host_step_rootEdge R ⊆ host_step_flagEdge H n ι b) :
    R.1.val.node.ty = H.ty ∧ R.2.1.facet.val = (ι.val.sideFacet b).val ∧
      (∀ k, (R.2.2.chain.val.cell k).val = ((P.sideFlag ι b).cell k).val) ∧
      0 < inner ℝ ((host_step_flagFrame H n ι b).linear (P.flag ι).direction)
        ((H.prototypeFrame n).linear (chainVector R.2.2)) ∧
      host_step_rootEdge R = host_step_flagEdge H n ι b := by
  have hs := hD.I1 R.1.val R.1.property
  obtain ⟨htype, hfacet, hchain, hvector⟩ :=
    host_step_step4_age_one_flag _ hs.1 R.2 hR.1 hR.2.2.1 ha
  have htype' : R.2.1.ty = H.ty := by
    simpa only [hR.2.2.2.1, hR.2.2.2.2.1, ← hH] using htype
  have hfacet' : R.2.1.facet.val = (ι.val.sideFacet b).val := by
    exact hfacet.trans (by rw [hR.2.2.2.1, hR.2.2.2.2.1])
  have hchain' : ∀ k, (R.2.2.chain.val.cell k).val = ((P.sideFlag ι b).cell k).val := by
    intro k
    exact (hchain k).trans (by rw [hR.2.2.2.1, hR.2.2.2.2.1])
  have hdir : (host_step_flagFrame H n ι b).linear (P.flag ι).direction =
      (H.prototypeFrame n).linear (chainVector R.2.2) := by
    rw [hvector]
    unfold FacetRecord.servingDirection
    rw [hR.2.2.2.1, hR.2.2.2.2.1]
    rfl
  have hnz : (host_step_flagFrame H n ι b).linear (P.flag ι).direction ≠ 0 := by
    have h := (host_step_flagFrame H n ι b).linear.injective.ne
      (sub_ne_zero.mpr (P.flag ι).distinct.symm)
    simpa only [map_zero, OrientedFullFlag.direction] using h
  refine ⟨hR.2.1.symm.trans htype', hfacet', hchain', ?_, ?_⟩
  · rw [← hdir]
    exact real_inner_self_pos.mpr hnz
  · have hbottom : (host_step_edge R.2).val = ((P.sideFlag ι b).cell edgeIndex).val :=
      hchain' edgeIndex
    have cell_image (N : FramedNode S) (e : Cell d) :
        N.cell n e = N.frame '' ((S.σ ^ n) '' e.carrier) := by
      rw [Set.image_image]
      rfl
    have hdiam : diam (host_step_rootEdge R) = diam (host_step_flagEdge H n ι b) := by
      unfold host_step_rootEdge host_step_flagEdge
      rw [cell_image, cell_image, hbottom, R.1.val.node.frame.diam_image, H.frame.diam_image]
    obtain ⟨ab, hab, he⟩ := edge_endpoints_exist
      (⟨R.2.1.ty, host_step_edge R.2⟩ : EdgeName S)
    have hroot : host_step_rootEdge R = segment ℝ
        (R.1.val.node.prototypeFrame n ab.1) (R.1.val.node.prototypeFrame n ab.2) := by
      change R.1.val.node.prototypeFrame n '' (host_step_edge R.2).val.carrier = _
      rw [he]
      exact image_segment ℝ (R.1.val.node.prototypeFrame n).toAffineMap _ _
    have href : host_step_flagEdge H n ι b =
        segment ℝ (H.prototypeFrame n ab.1) (H.prototypeFrame n ab.2) := by
      change H.prototypeFrame n '' ((P.sideFlag ι b).cell edgeIndex).val.carrier = _
      rw [← hbottom, he]
      exact image_segment ℝ (H.prototypeFrame n).toAffineMap _ _
    rw [hroot, href] at hsub hdiam ⊢
    exact host_step_step4_subsegment_eq _ _ _ _
      (fun h => hab ((H.prototypeFrame n).injective h)) hsub hdiam

/-- Step 5 of the V4 proof of `host_step` (V4 3.6): "the positioned
oriented flag together with the side determines the frame". Equal edge carriers
fix translation; all flag spans, orientations and sides fix the orthogonal part. -/
private theorem host_step_step5_frame (H N : FramedNode S) (n : ℕ)
    (ι : P.Incidence) (b : Bool) (z : host_step_Chain P)
    (hH : H.ty = ι.val.sideType b) (hty : N.ty = H.ty)
    (hf : z.1.facet.val = (ι.val.sideFacet b).val)
    (hchain : ∀ k, (z.2.chain.val.cell k).val = ((P.sideFlag ι b).cell k).val)
    (horient : 0 < inner ℝ ((host_step_flagFrame H n ι b).linear (P.flag ι).direction)
      ((H.prototypeFrame n).linear (chainVector z.2)))
    (halign : host_step_aligned H n ι b N n z)
    (hedge : N.cell n (host_step_edge z).val = host_step_flagEdge H n ι b) :
    N = H := by
  sorry

/-- Step 5 of the V4 proof of `host_step` (V4 3.6): "these open
half-balls lie in int B'". The common facet and the disjoint interiors of the
two chosen blocks force their local half-spaces to have opposite normals. -/
private theorem host_step_step5_halfballs
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) (B' : Block Y n)
    (hB' : B' ∈ D.geometry.blocks) (hnode : B'.node = proposedSibling D B hB f a)
    (hne : B ≠ B') :
    ∀ x ∈ relint (B.node.cell n f.val), ∃ r : ℝ, 0 < r ∧
      Parser.oppositeHalfBall B.node n x r ⊆ interior B'.carrier := by
  intro x hx
  let g : FacetName S B'.node.ty :=
    ⟨(a.record.incidence.val.sideFacet (!a.record.sideIndex)).val, by
      rw [hnode]
      exact (a.record.incidence.val.sideFacet (!a.record.sideIndex)).property⟩
  have hfacet : B'.node.cell n g.val = B.node.cell n f.val := by
    change B'.node.cell n (a.record.incidence.val.sideFacet (!a.record.sideIndex)).val = _
    rw [hnode]
    exact (Parser.ageOneFacet_semantics D hD B hB f a).2.2.2
  obtain ⟨r₀, hr₀, v, hv, hopp, h₀⟩ := Parser.oppositeHalfBall_geometry B.node n f x hx
  obtain ⟨r₁, hr₁, w, hw, _, h₁⟩ :=
    Parser.oppositeHalfBall_geometry B'.node n g x (hfacet.symm ▸ hx)
  have hopen : ∀ (K : Set (E d)) (r : ℝ) (v : E d),
      K ∩ ball x r = ball x r ∩ {y | 0 ≤ inner ℝ v (y - x)} →
      ball x r ∩ {y | 0 < inner ℝ v (y - x)} ⊆ interior K := by
    intro K r v hK
    apply interior_maximal
    · intro y hy
      have hmem : y ∈ K ∩ ball x r := by
        rw [hK]
        exact ⟨hy.1, (show 0 ≤ inner ℝ v (y - x) from le_of_lt hy.2)⟩
      exact hmem.1
    · exact isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
  let r := min r₀ r₁
  have hr : 0 < r := lt_min hr₀ hr₁
  have hsum : v + w = 0 := by
    by_contra hsum
    have hnorm : 0 < ‖v + w‖ := norm_pos_iff.mpr hsum
    have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
    have hww : inner ℝ w w = 1 := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
    have hpos := real_inner_self_pos.mpr hsum
    rw [inner_add_left, inner_add_right, inner_add_right, hvv, hww,
      real_inner_comm w v] at hpos
    have hvpos : 0 < inner ℝ v (v + w) := by
      rw [inner_add_right, hvv, real_inner_comm w v]
      linarith
    have hwpos : 0 < inner ℝ w (v + w) := by
      rw [inner_add_right, hww]
      linarith
    let ε := r / (2 * ‖v + w‖)
    have hε : 0 < ε := div_pos hr (mul_pos (by norm_num) hnorm)
    let y := x + ε • (v + w)
    have hy : dist y x < r := by
      dsimp [y]
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      have heq : ε * ‖v + w‖ = r / 2 := by
        dsimp [ε]
        field_simp
      rw [heq]
      linarith
    have hy₀ : y ∈ interior B.carrier := by
      apply hopen _ r₀ v h₀
      refine ⟨lt_of_lt_of_le hy (min_le_left _ _), ?_⟩
      change 0 < inner ℝ v (x + ε • (v + w) - x)
      rw [add_sub_cancel_left, inner_smul_right]
      exact mul_pos hε hvpos
    have hy₁ : y ∈ interior B'.carrier := by
      apply hopen _ r₁ w h₁
      refine ⟨lt_of_lt_of_le hy (min_le_right _ _), ?_⟩
      change 0 < inner ℝ w (x + ε • (v + w) - x)
      rw [add_sub_cancel_left, inner_smul_right]
      exact mul_pos hε hwpos
    exact Set.disjoint_left.mp (D.geometry.disjoint hB hB' hne) hy₀ hy₁
  have hwv : w = -v := eq_neg_of_add_eq_zero_right hsum
  refine ⟨r, hr, ?_⟩
  rw [hopp r hr (min_le_left _ _)]
  intro y hy
  apply hopen _ r₁ w h₁
  refine ⟨(show dist y x < r₁ from lt_of_lt_of_le hy.1 (min_le_right _ _)), ?_⟩
  change 0 < inner ℝ w (y - x)
  rw [hwv, inner_neg_left]
  exact neg_pos.mpr hy.2

/-- Step 5 of the V4 proof of `host_step` (V4 3.6): "every tile whose
interior meets ... lies in B'". An actual block is a union of actual native
tiles, and distinct physical tiles have disjoint interiors. -/
private theorem host_step_step5_tile_containment
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (B : Block Y n)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (hmeet : (interior t.carrier ∩ interior B.carrier).Nonempty) :
    t.carrier ⊆ B.carrier := by
  classical
  obtain ⟨x, hxt, hxB⟩ := hmeet
  have hx : x ∈ B.carrier := interior_subset hxB
  rw [B.union_tiles] at hx
  obtain ⟨v, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hv, hxv⟩ := Set.mem_iUnion.mp hx
  by_cases htv : t = v
  · subst v
    exact hv.2
  have hreg : closure (interior v.carrier) = v.carrier := by
    obtain ⟨A, _, φ, hcarrier, _⟩ := v.realization
    rw [hcarrier]
    change closure (interior (φ.toHomeomorph '' A.carrier)) =
      φ.toHomeomorph '' A.carrier
    rw [← φ.toHomeomorph.image_interior, ← φ.toHomeomorph.image_closure,
      A.regularClosed]
  have hd := (Y.disjoint ht hv.1 htv).closure_right isOpen_interior
  rw [hreg] at hd
  exact False.elim (Set.disjoint_left.mp hd hxt hxv)

/-- R6, V4 3.6: the general reverse host step, retaining the counter strand.
All j-side tiles sufficiently near relint f belong to one existing level-n block,
which is the proposed sibling with its prescribed type and full frame. Its
first address role and opposite-facet record are exactly the age-one data.
No scalar expansion or equal-edge hypothesis is imposed. -/
theorem host_step (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) : Parser.HostConclusion D B hB f a := by
  classical
  let H := proposedSibling D B hB f a
  let ι := a.record.incidence
  let b := !a.record.sideIndex
  have hH : H.ty = ι.val.sideType b := rfl
  obtain ⟨he₀, heN, u₀, hu₀, hs₀, hk₀⟩ :=
    host_step_step1_seed Y hY n hn D hD B hB f a
  obtain ⟨m, u, _, hu⟩ :=
    host_step_step2_strand Y hY n hn D hD B hB f a ⟨he₀, heN⟩ u₀ hu₀ hs₀ hk₀
  obtain ⟨J, hJ, hjumps⟩ := host_step_step2_distinct_jumps Y n H ι b m u hu
  obtain ⟨q, R, owner, hR⟩ := host_step_step3_roots Y hY n hn D hD B hB f a m u hu
  have hq := host_step_step3_root_bound D hD H ι b hH u R owner hR
  obtain ⟨E, hE, hcover⟩ := host_step_step4_partition_endpoints D H ι b u R owner hR
  obtain ⟨x, hxJ, hxE⟩ := host_step_step4_pigeonhole J E q hJ hE hq
  obtain ⟨j, hj⟩ := hcover x (hjumps x hxJ).1 hxE
  have hjump := host_step_step4_lift_jump D hD H ι b u hu R owner hR
    x (hjumps x hxJ).2 j hj
  have hv := hR.1 j
  have hstate := hD.I1 (R j).1.val (R j).1.property
  have hbeta : (R j).2.1.beta = (D.blockState (R j).1.val (R j).1.property).residue :=
    Fin.ext (hv.2.2.2.2.2.1.trans hstate.2.2.symm)
  have ha := host_step_step4_age_one _ hstate.1 (R j).2 hv.1 hv.2.2.1 hbeta hjump
  obtain ⟨hty, hf, hchain, horient, hedge⟩ :=
    host_step_step4_full_edge D hD H ι b hH (R j) hv ha (hR.2.1 j)
  have hnode := host_step_step5_frame H (R j).1.val.node n ι b (R j).2
    hH hty hf hchain horient hv.2.2.2.2.2.2 hedge
  have hrole : firstRole D (R j).1.val (R j).1.property = ι.val.sideRole b := by
    exact ha.2.1.symm.trans
      ((R j).2.1.side_eq.trans (by rw [hv.2.2.2.1, hv.2.2.2.2.1]))
  have hne : B ≠ (R j).1.val := by
    intro heq
    have hroles : firstRole D B hB = firstRole D (R j).1.val (R j).1.property := by
      subst B
      rfl
    have hown : firstRole D B hB = ι.val.sideRole a.record.sideIndex :=
      (Parser.ageOneFacet_semantics D hD B hB f a).2.2.1.symm.trans a.record.side_eq
    have hcontra := hown.symm.trans (hroles.trans hrole)
    have hd := ι.val.distinct
    cases hb : a.record.sideIndex <;>
      simp [b, hb, PrimitiveIncidence.sideRole, PrimitiveIncidence.sideIndex,
        hd, Ne.symm hd] at hcontra
  refine ⟨(R j).1.val, (R j).1.property, hnode, hrole, ?_, ?_⟩
  · refine ⟨(R j).2.1, ?_, ha, hv.2.2.2.1, ?_⟩
    · simpa only [hf] using hv.1
    · exact (R j).2.1.side_eq.trans (by rw [hv.2.2.2.1, hv.2.2.2.2.1])
  · intro y hy
    obtain ⟨r, hr, hball'⟩ := host_step_step5_halfballs D hD B hB f a
      (R j).1.val (R j).1.property hnode hne y hy
    refine ⟨r, hr, hball', ?_⟩
    intro t ht hmeet
    apply host_step_step5_tile_containment (R j).1.val t ht
    exact hmeet.mono (Set.inter_subset_inter_right _ hball')

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
