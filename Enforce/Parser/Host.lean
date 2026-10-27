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

/-- Step 1 of the V4 proof of `host_step_step1_seed_step3_restricted_header` (V4 3.6, 1.13(c)):
"by (I2) their record ... is the restriction of the age-1 record".
Realize the honest root state at its prescribed height and frame before descent. -/
private theorem host_step_step1_seed_step3_restricted_header_step1_realise
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

/-- Step 2 of the V4 proof of `host_step_step1_seed_step3_restricted_header` (V4 3.6, 2.3):
"by (I2) their record on that piece is the restriction". The child equations
identify every native descendant state and its ancestor in the fixed source. -/
private theorem host_step_step1_seed_step3_restricted_header_step2_descent
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

/-- Step 3 of the V4 proof of `host_step_step1_seed_step3_restricted_header` (V4 2.3):
"same iota, side, beta and provider". Equal birth nodes and provider carriers
have equal canonical incidence names. -/
private theorem host_step_step1_seed_step3_restricted_header_step3_incidence
    (P : Params S) (U : HonestSource S)
    (c p : U.Node) (f : FacetName S c.2.val.ty) (F : FacetName S p.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f) (hF : ¬ U.hierarchy.IsFault p F)
    (hb : U.hierarchy.birthParent c f hf = U.hierarchy.birthParent p F hF)
    (hp : U.hierarchy.providerCarrier c f hf = U.hierarchy.providerCarrier p F hF) :
    U.recordIncidence P c f hf = U.recordIncidence P p F hF := by
  have hc := U.hierarchy.providerIncidence_spec c f hf
  have hpar := U.hierarchy.providerIncidence_spec p F hF
  apply P.canonical_unique
  constructor
  · exact hc.1.trans ((congrArg (fun q : U.Node => q.2.val.ty) hb).trans
      (hpar.1.symm.trans (P.canonical_spec _).1))
  · have hplace := congrArg (fun B : U.Node => B.2.val.prototypeFrame B.1 ''
        (S.σ.symm '' (U.hierarchy.providerIncidence c f hf).positioned)) hb
    have heq := hplace.symm.trans (hc.2.2.2.symm.trans (hp.trans hpar.2.2.2))
    exact S.σ.symm.injective.image_injective
      (((U.hierarchy.birthParent p F hF).2.val.prototypeFrame
        (U.hierarchy.birthHeight p F hF)).injective.image_injective heq) |>.trans
          (P.canonical_spec _).2

/-- Step 4 of the V4 proof of `host_step_step1_seed_step3_restricted_header` (V4 3.6):
"P := PP(B)". The first source role reconstructs the exact source parent frame. -/
private theorem host_step_step1_seed_step3_restricted_header_step4_parent
    (U : HonestSource S) (q : U.Node) :
    (U.hierarchy.parentNode q).2.val =
      ⟨(U.hierarchy.nodeRole q).1,
        (S.placeChild q.1 (U.hierarchy.nodeRole q).2).symm.trans q.2.val.frame⟩ := by
  apply FramedNode.ext
  · rfl
  · have hf := congrArg FramedNode.frame (U.hierarchy.child_eq q.1 q.2)
    change q.2.val.frame = (S.placeChild q.1 (U.hierarchy.nodeRole q).2).trans
      (U.hierarchy.parentNode q).2.val.frame at hf
    rw [hf]
    ext x
    simp

/-- Step 5 of the V4 proof of `host_step_step1_seed_step3_restricted_header` (V4 3.6, 2.3):
"tau({p₀}) = {p₀} is a vertex of g". A listed vertex of the serving node
has a zero-dimensional canonical provider stratum. -/
private theorem host_step_step1_seed_step3_restricted_header_step5_zero
    (U : HonestSource S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (v : VertexName S q.2.val.ty)
    (hv : v.val.carrier ⊆ f.val.carrier)
    (hp : (U.hierarchy.servingChild q f hf).2.val.Lists
      (U.hierarchy.servingChild q f hf).1
      (q.2.val.prototypeFrame q.1 (vertexPoint v))) :
    (U.recordTau P q f hf ⟨vertexCell v, hv⟩).val.val.dim = 0 := by
  obtain ⟨w, hw, hpw⟩ := hp
  let w' : VertexName S (U.hierarchy.servingChild q f hf).2.val.ty := ⟨w, hw⟩
  have hpoint : q.2.val.prototypeFrame q.1 (vertexPoint v) =
      (U.hierarchy.servingChild q f hf).2.val.prototypeFrame
        (U.hierarchy.servingChild q f hf).1 (vertexPoint w') := by
    change _ ∈ (U.hierarchy.servingChild q f hf).2.val.cell
      (U.hierarchy.servingChild q f hf).1 w'.val at hpw
    simpa only [FramedNode.cell, vertexPoint_spec w', Set.image_singleton,
      Set.mem_singleton_iff] using hpw
  have hcell : q.2.val.cell q.1 (vertexCell v).val =
      (U.hierarchy.servingChild q f hf).2.val.cell
        (U.hierarchy.servingChild q f hf).1 (vertexCell w').val := by
    simp only [FramedNode.cell, vertexCell, vertexPoint_spec, Set.image_singleton, hpoint]
  have hstratum : U.hierarchy.stratumMap q f hf (vertexCell v)
      (U.cellInFacet_placed q f ⟨vertexCell v, hv⟩) = vertexCell w' := by
    exact ((Classical.choose_spec (U.hierarchy.stratum_exists_unique q f hf
      (vertexCell v) (U.cellInFacet_placed q f ⟨vertexCell v, hv⟩))).2
        (vertexCell w') (by rw [hcell])).symm
  have htau := record_tau_spec U P q f hf ⟨vertexCell v, hv⟩
  rw [hstratum] at htau
  change U.providerPlacement P q f hf ''
      (U.recordTau P q f hf ⟨vertexCell v, hv⟩).val.val.carrier =
    (U.hierarchy.servingChild q f hf).2.val.prototypeFrame
      (U.hierarchy.servingChild q f hf).1 '' w'.val.carrier at htau
  rw [vertexPoint_spec, Set.image_singleton] at htau
  let e := U.recordTau P q f hf ⟨vertexCell v, hv⟩
  have hsingleton : e.val.val.carrier =
      {(U.providerPlacement P q f hf).symm
        ((U.hierarchy.servingChild q f hf).2.val.prototypeFrame
          (U.hierarchy.servingChild q f hf).1 (vertexPoint w'))} := by
    apply (U.providerPlacement P q f hf).injective.image_injective
    simpa only [Set.image_singleton, AffineEquiv.apply_symm_apply] using htau
  change e.val.val.dim = 0
  rw [← e.val.val.flat.dimension, hsingleton]
  simp [cellDirection, direction_affineSpan]

/-- Step 6 of the V4 proof of `host_step_step1_seed_step3_restricted_header` (V4 3.6, 2.6(c)):
"each such t has an END slot". A finite record in an honest leaf pre-pattern
has a non-NULL packet on that same facet. -/
private theorem host_step_step1_seed_step3_restricted_header_step6_packet
    (l : LeafType P) (f : Cell d)
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
  classical
  obtain ⟨U, hU, hs⟩ := host_step_step1_seed_step3_restricted_header_step1_realise
    (D.blockState B hB) (hD.I1 B hB).1 B.node n
    (hD.I1 B hB).2.1 (hD.I1 B hB).2.2
  let q : U.Node := ⟨n, ⟨B.node, hU⟩⟩
  have hread : U.facetRecordOf P q f = some a.record := by
    have h := a.readout
    rw [← hs] at h
    simpa only [stateRecordAt, stateOf, dif_pos f.property] using h
  have hf : ¬ U.hierarchy.IsFault q f := by
    intro hf
    simp only [HonestSource.facetRecordOf, dif_pos hf] at hread
    contradiction
  have hrecord : U.recordOf P q f hf = a.record := by
    simpa only [HonestSource.facetRecordOf, dif_neg hf, Option.some.injEq] using hread
  have hoff : (U.hierarchy.firstProvider q f hf).1 = 0 := by
    have ha := a.age_one
    rw [← hrecord] at ha
    change min (U.hierarchy.age q f hf) P.C = 1 at ha
    have := P.C_gt_one
    have := (U.hierarchy.birthHeight_age_spec q f hf).2.1
    omega
  have hserv : U.hierarchy.servingChild q f hf = q := by
    simp only [CoherentHierarchy.servingChild, hoff, CoherentHierarchy.ancestor,
      Function.iterate_zero, id_eq]
  have hrole : U.hierarchy.nodeRole q = firstRole D B hB := by
    have h := congrArg (fun s : State P => s.address ⟨0, P.k_pos⟩) hs
    simpa only [stateOf, CoherentHierarchy.ancestor, Function.iterate_zero, id_eq,
      firstRole] using h
  have hparent : (U.hierarchy.parentNode q).2.val = proposedParent D B hB := by
    rw [host_step_step1_seed_step3_restricted_header_step4_parent, hrole]
    rfl
  obtain ⟨r, hr, w, htile⟩ := hpiece.2.1
  have hrn : r = n := by omega
  subst r
  have hreal {k : ℕ} (hk : k = n) (hN : B.node ∈ D.geometry.nodes k)
      (hU' : B.node ∈ U.hierarchy.nodes k) :
      stateOf U P ⟨k, ⟨B.node, hU'⟩⟩ = D.stateAt k B.node hN := by
    subst k
    exact hs
  have hnode {k : ℕ} (hk : k = n) (hU' : B.node ∈ U.hierarchy.nodes k) :
      (⟨k, ⟨B.node, hU'⟩⟩ : U.Node) = q := by
    subst k
    rfl
  have hdesc : ∃ (htD : tileNode t ∈ D.geometry.nodes 0)
      (htU : tileNode t ∈ U.hierarchy.nodes 0),
      stateOf U P ⟨0, ⟨tileNode t, htU⟩⟩ = D.stateAt 0 (tileNode t) htD ∧
        U.hierarchy.ancestor ⟨0, ⟨tileNode t, htU⟩⟩ n = q := by
    obtain ⟨htD, htU, htstate, hanc⟩ :=
      host_step_step1_seed_step3_restricted_header_step2_descent D hD U 0 n B.node
        (by simpa only [Nat.zero_add] using D.geometry.root_mem B hB)
        (by simpa only [Nat.zero_add] using hU)
        (hreal (Nat.zero_add n) _ _) w
    rw [htile]
    exact ⟨htD, htU, htstate, hanc.trans (hnode (Nat.zero_add n) _)⟩
  obtain ⟨htD, htU, htstate, hanc⟩ := hdesc
  let c : U.Node := ⟨0, ⟨tileNode t, htU⟩⟩
  have hleaf : stateOf U P c = (compilerLeaf C t).prePattern.state :=
    htstate.trans (hD.I2.2 (tileNode t) htD t hpiece.1 rfl)
  obtain ⟨hg, hprovider, hbirth⟩ := U.hierarchy.provider_inherited q c n hanc f g hf hpiece.2.2
  have hbirth' : U.hierarchy.birthParent c g hg = U.hierarchy.parentNode q := by
    rw [hbirth, CoherentHierarchy.birthParent, hserv]
  have hcserv : U.hierarchy.servingChild c g hg = q := by
    have hh := congrArg (fun z : U.Node => z.1) hbirth'
    have hoff' := (U.hierarchy.birthHeight_age_spec c g hg).1
    have he : (U.hierarchy.firstProvider c g hg).1 = n := by
      change U.hierarchy.birthHeight c g hg = n + 1 at hh
      change U.hierarchy.birthHeight c g hg = 0 + _ + 1 at hoff'
      omega
    simpa only [CoherentHierarchy.servingChild, he] using hanc
  have hι : U.recordIncidence P c g hg = a.record.incidence :=
    (host_step_step1_seed_step3_restricted_header_step3_incidence P U c q g f hg hf
      hbirth hprovider).trans (congrArg FacetRecord.incidence hrecord)
  have hframe : c.2.val.prototypeFrame c.1 = (compilerFrame C t).toAffineEquiv := by
    ext x
    rfl
  have hpoint : c.2.val.prototypeFrame c.1 (vertexPoint v) = p := by
    rw [hframe]
    exact hvp
  have hzero := host_step_step1_seed_step3_restricted_header_step5_zero (P := P)
    U c g hg v hv (by rw [hcserv, hpoint]; exact hp)
  have hrleaf : leafRecord (compilerLeaf C t) g.val = some (U.recordOf P c g hg) := by
    unfold leafRecord
    rw [← hleaf]
    simp only [stateRecordAt, stateOf, c, dif_pos g.property,
      HonestSource.facetRecordOf, dif_neg hg]
  have hheader : leafHeader (compilerLeaf C t) v.val g.val =
      some (U.headerOf P c g hg v) := by
    unfold leafHeader
    rw [← hleaf]
    simp only [stateOf, c, dif_pos v.property, dif_pos g.property,
      HonestSource.headerRecordOf, dif_pos hv, dif_neg hg, hzero, if_pos True.intro]
  obtain ⟨packet, hpacket⟩ := host_step_step1_seed_step3_restricted_header_step6_packet
    (compilerLeaf C t) g.val (U.recordOf P c g hg) hrleaf
  have hvc : v.val ∈ (S.cx (tileNode t).ty).cells := (vertexCell v).property
  let j : EndSlot (compilerLeaf C t) := {
    facet := g
    record := U.recordOf P c g hg
    record_eq := hrleaf
    type_eq := rfl
    facet_eq := rfl
    vertex := v
    onFacet := hv
    providerVertex := U.recordTau P c g hg ⟨vertexCell v, hv⟩
    tau_vertex := by
      simp only [FacetRecord.tauAt, HonestSource.recordOf, c,
        dif_pos hvc, dif_pos hv]
      rfl
    provider_zero := hzero
    header := U.headerOf P c g hg v
    header_eq := hheader
    packet := packet
    packet_eq := hpacket }
  refine ⟨j, rfl, hvp, hι, ?_, ?_⟩
  · change (U.hierarchy.servingChild c g hg).1 % P.L = n % P.L
    rw [hcserv]
  · change U.headerOf P c g hg v = _
    have hnorm (K : Set (E d)) : U.normalizeCone c K =
        (compilerFrame C t).linearIsometryEquiv.symm '' K := by
      rw [HonestSource.normalizeCone, hframe]
      rfl
    rw [← hparent]
    unfold HonestSource.headerOf
    rw [hbirth']
    simp only [show (U.hierarchy.parentNode q).1 = n + 1 from rfl,
      hpoint, Nat.add_sub_cancel, hnorm, host_step_step1_seed_step1_header]

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

/-- Step 1 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6):
"the realised flag tangent cones ... equal the actual tangent cones".
Radial tangent cones commute with an invertible affine change of coordinates. -/
private theorem host_step_step1_seed_step5_trace_step1_tangent_image
    (φ : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) (x : E d) :
    tangentCone (φ '' K) (φ x) = φ.linear '' tangentCone K x := by
  have hmap (t : ℝ) (u : E d) : φ (x + t • u) = φ x + t • φ.linear u := by
    simpa only [vadd_eq_add, map_smul, add_comm] using φ.map_vadd x (t • u)
  ext u
  constructor
  · rintro ⟨ε, hε, hmem⟩
    refine ⟨φ.linear.symm u, ⟨ε, hε, ?_⟩, φ.linear.apply_symm_apply u⟩
    intro t ht htε
    have hm := hmem t ht htε
    rw [← φ.linear.apply_symm_apply u, ← hmap] at hm
    exact φ.injective.mem_set_image.mp hm
  · rintro ⟨u, ⟨ε, hε, hmem⟩, rfl⟩
    exact ⟨ε, hε, fun t ht htε => hmap t u ▸
      Set.mem_image_of_mem φ (hmem t ht htε)⟩

/-- Step 1 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6):
"T_p s_j is contained in T_p F_j". Containment of cells implies containment
of their radial tangent cones, with the same apex. -/
private theorem host_step_step1_seed_step5_trace_step1_tangent_mono
    {K L : Set (E d)} (h : K ⊆ L) (x : E d) :
    tangentCone K x ⊆ tangentCone L x := by
  rintro u ⟨ε, hε, hu⟩
  exact ⟨ε, hε, fun t ht htε => h (hu t ht htε)⟩

/-- Step 1 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6):
"aff s_j = aff F_j". A flat polyhedral cell and its tangent cone at a point
of the cell have the same affine span after translating the cone to that point. -/
private theorem host_step_step1_seed_step5_trace_step1_cone_span
    (e : Cell d) (x : E d) (hx : x ∈ e.carrier) :
    affineSpan ℝ ((fun u => x + u) '' tangentCone e.carrier x) =
      affineSpan ℝ e.carrier := by
  classical
  let A := affineSpan ℝ e.carrier
  let T := (fun u => x + u) '' tangentCone e.carrier x
  have hxA : x ∈ A := subset_affineSpan ℝ e.carrier hx
  have hle : affineSpan ℝ T ≤ A := by
    apply affineSpan_le.mpr
    rintro z ⟨u, ⟨ε, hε, hu⟩, rfl⟩
    let t := ε / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have hz : x + t • u ∈ A := subset_affineSpan ℝ e.carrier
      (hu t ht (by dsimp [t]; linarith))
    have hh := A.smul_vsub_vadd_mem t⁻¹ hz hxA hxA
    have he : t⁻¹ • ((x + t • u) - x) + x = x + u := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      module
    change x + u ∈ A
    rw [← he]
    exact hh
  obtain ⟨s, hs⟩ := e.flat.polyhedral
  let bad : Finset (Finset (E d)) :=
    s.filter (fun p : Finset (E d) => x ∉ convexHull ℝ (p : Set (E d)))
  let O : Set (E d) := (⋃ p : Finset (E d), ⋃ (_ : p ∈ bad),
    convexHull ℝ (p : Set (E d)))ᶜ
  have hO : IsOpen O := by
    exact (isClosed_biUnion_finset (s := bad)
      (fun p _ => p.finite_toSet.isCompact_convexHull.isClosed)).isOpen_compl
  have hxO : x ∈ O := by
    intro hh
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hh
    exact (Finset.mem_filter.mp hp).2 hxp
  have hlocal : e.carrier ∩ O ⊆ T := by
    rintro y ⟨hy, hyO⟩
    rw [hs] at hy
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hy
    have hxp : x ∈ convexHull ℝ (p : Set (E d)) := by
      by_contra h
      exact hyO (mem_iUnion₂.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, h⟩, hyp⟩)
    refine ⟨y - x, ⟨1, zero_lt_one, fun t ht ht1 => ?_⟩, by module⟩
    rw [hs]
    refine mem_iUnion₂.mpr ⟨p, hp, ?_⟩
    have hm := (convex_convexHull ℝ (p : Set (E d))) hxp hyp
      (by linarith : 0 ≤ 1 - t) ht.le (by ring : (1 - t) + t = 1)
    convert hm using 1 <;> module
  have hxcl : x ∈ closure (relint e.carrier) := by
    rw [e.flat.regularClosed]
    exact hx
  obtain ⟨y, hyO, hy⟩ := mem_closure_iff.mp hxcl O hO hxO
  letI : Nonempty A := ⟨⟨x, hxA⟩⟩
  let V : Set A := interior ((↑) ⁻¹' e.carrier : Set A) ∩ ((↑) ⁻¹' O)
  have hV : IsOpen V := isOpen_interior.inter (hO.preimage continuous_subtype_val)
  have hVne : V.Nonempty := by
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hz, hyO⟩
  have hVT : A.subtype '' V ⊆ T := by
    rintro z ⟨w, hw, rfl⟩
    have hm : (w : E d) ∈ e.carrier :=
      interior_subset (s := ((↑) ⁻¹' e.carrier : Set A)) hw.1
    exact hlocal ⟨hm, hw.2⟩
  have hfull : affineSpan ℝ (A.subtype '' V) = A := by
    rw [← AffineSubspace.map_span, hV.affineSpan_eq_top hVne]
    ext z
    constructor
    · rintro ⟨w, _, rfl⟩
      exact w.property
    · intro hz
      exact ⟨⟨z, hz⟩, by trivial, rfl⟩
  apply le_antisymm hle
  rw [← hfull]
  exact affineSpan_mono ℝ hVT

/-- Step 2 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 1.1, 1.22(a)):
"edge heredity". Containment of placed cells bounds their dimensions;
invertible affine placement preserves the dimension of each affine span. -/
private theorem host_step_step1_seed_step5_trace_step2_dim_le
    (φ ψ : E d ≃ᵃ[ℝ] E d) (e f : Cell d)
    (hsub : φ '' e.carrier ⊆ ψ '' f.carrier) : e.dim ≤ f.dim := by
  have hdim (φ : E d ≃ᵃ[ℝ] E d) (e : Cell d) :
      Module.finrank ℝ (affineSpan ℝ (φ '' e.carrier)).direction = e.dim := by
    change Module.finrank ℝ (affineSpan ℝ (φ.toAffineMap '' e.carrier)).direction = e.dim
    rw [← AffineSubspace.map_span φ.toAffineMap, AffineSubspace.map_direction]
    exact (φ.linear.finrank_map_eq _).trans e.flat.dimension
  have h := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hsub))
  simpa only [hdim] using h

/-- Step 2 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 1.22(a), 3.6):
"adjacent to h at its initial endpoint". Finitely many vertices cannot
leave an endpoint uncovered by a closed family that covers the remaining segment. -/
private theorem host_step_step1_seed_step5_trace_step2_closed_cover
    (K V : Set (E d)) (hK : IsClosed K) (hV : V.Finite)
    (x y : E d) (hxy : x ≠ y) (hcover : segment ℝ x y ⊆ K ∪ V) : x ∈ K := by
  by_contra hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl x hx
  let δ := min 1 (ε / (‖y - x‖ + 1))
  have hden : 0 < ‖y - x‖ + 1 := by positivity
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε hden)
  let L : ℝ → E d := fun t => x + t • (y - x)
  have hL : Function.Injective L := by
    intro a b h
    exact smul_left_injective ℝ (sub_ne_zero.mpr hxy.symm) (add_left_cancel h)
  obtain ⟨t, ht, htv⟩ := (Set.Ioo_infinite hδ).exists_notMem_finite
    (hV.preimage hL.injOn)
  have ht1 : t < 1 := lt_of_lt_of_le ht.2 (min_le_left _ _)
  have htε : t < ε / (‖y - x‖ + 1) := lt_of_lt_of_le ht.2 (min_le_right _ _)
  have hseg : L t ∈ segment ℝ x y := by
    refine ⟨1 - t, t, by linarith [ht.1], ht.1.le, by ring, ?_⟩
    dsimp [L]
    module
  have hnear : L t ∈ ball x ε := by
    change dist (x + t • (y - x)) x < ε
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    have := (lt_div_iff₀ hden).mp htε
    nlinarith [norm_nonneg (y - x)]
  rcases hcover hseg with h | h
  · exact hball hnear h
  · exact htv h

/-- Step 2 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 1.1, 1.22(a)):
"edge heredity in its endpoint trace piece". Away from listed vertices,
the minimal cell of a trace owner on the ancestral edge is a listed edge,
and it lies in both the trace polygon and the ancestral edge. -/
private theorem host_step_step1_seed_step5_trace_step2_trace_edge
    (A : S.ι) (F : FacetFlag S A) (n : ℕ) (a : TracePiece A F n) (z : E d)
    (hza : z ∈ a.carrier)
    (hzh : z ∈ (S.σ ^ n) '' (F.cell edgeIndex).val.carrier)
    (hnv : ¬ a.tile.Lists 0 z) :
    ∃ e : PrototypeEdge S a.tile.ty,
      z ∈ a.tile.cell 0 e.val ∧
      a.tile.cell 0 e.val ⊆ (S.σ ^ n) '' (F.cell edgeIndex).val.carrier ∧
      e.val.carrier ⊆ a.bottom.val.carrier := by
  obtain ⟨u, hu, rfl⟩ := hza
  have hu' : u ∈ frontier (S.proto a.tile.ty).carrier := by
    rw [← (S.cx a.tile.ty).carriers_cover]
    exact mem_iUnion₂.mpr ⟨a.bottom.val, a.bottom.property, hu⟩
  let e := (S.cx a.tile.ty).minimalCell u hu'
  have he := (S.cx a.tile.ty).minimalCell_mem u hu'
  have hue := (S.cx a.tile.ty).mem_relint_minimalCell u hu'
  have hbottom : e.carrier ⊆ a.bottom.val.carrier :=
    (S.cx a.tile.ty).minimalCell_subset u hu' a.bottom.val a.bottom.property hu
  have hzrel : a.tile.prototypeFrame 0 u ∈ relint (a.tile.cell 0 e) := by
    change a.tile.frame u ∈ intrinsicInterior ℝ (a.tile.frame.toAffineIsometry '' e.carrier)
    rw [a.tile.frame.toAffineIsometry.image_intrinsicInterior]
    exact Set.mem_image_of_mem _ hue
  have hze : a.tile.prototypeFrame 0 u ∈ a.tile.cell 0 e :=
    intrinsicInterior_subset hzrel
  let R : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hdesc : a.tile.IsDescendant 0 R n := by
    refine ⟨n, by omega, a.owner, ?_⟩
    simp [TracePiece.tile, R, FramedNode.move]
    rfl
  have hsub : a.tile.cell 0 e ⊆ (S.σ ^ n) '' (F.cell edgeIndex).val.carrier := by
    have hh := hereditary_trace R a.tile n 0 hdesc (F.cell edgeIndex).val e
      (F.cell edgeIndex).property he ⟨a.tile.prototypeFrame 0 u, hzrel, hzh⟩
    exact hh
  have hdim : e.dim ≤ 1 := by
    have hh := host_step_step1_seed_step5_trace_step2_dim_le
      (a.tile.prototypeFrame 0) (S.σ ^ n).toAffineEquiv e (F.cell edgeIndex).val hsub
    simpa only [F.dimension edgeIndex] using hh
  have hnonzero : e.dim ≠ 0 := by
    intro hz
    exact hnv ⟨e, Finset.mem_filter.mpr ⟨he, hz⟩, hze⟩
  exact ⟨⟨e, Finset.mem_filter.mpr ⟨he, by omega⟩⟩, hze, hsub, hbottom⟩
/-- Step 2 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 1.22(a), 3.6):
"the selected owner ... adjacent to h at its initial endpoint".
In the recursive trace, one selected polygon has a listed edge lying in the
flag edge and containing its endpoint. This also covers the segment trace in
dimension two and subdivision depth zero. -/
private theorem host_step_step1_seed_step5_trace_step2_endpoint_piece
    (A : S.ι) (F : FacetFlag S A) (n : ℕ) (x y : E d)
    (hxy : x ≠ y) (hedge : (F.cell edgeIndex).val.carrier = segment ℝ x y) :
    ∃ a : TracePiece A F n, ∃ e : PrototypeEdge S a.tile.ty,
      (S.σ ^ n) x ∈ a.tile.cell 0 e.val ∧
      a.tile.cell 0 e.val ⊆ (S.σ ^ n) '' (F.cell edgeIndex).val.carrier ∧
      e.val.carrier ⊆ a.bottom.val.carrier := by
  classical
  letI : Finite (TracePiece A F n) := tracePieces_finite A F n
  let Good := {z : Σ a : TracePiece A F n, PrototypeEdge S a.tile.ty //
    z.1.tile.cell 0 z.2.val ⊆ (S.σ ^ n) '' (F.cell edgeIndex).val.carrier ∧
      z.2.val.carrier ⊆ z.1.bottom.val.carrier}
  let K : Set (E d) := ⋃ z : Good, z.val.1.tile.cell 0 z.val.2.val
  let V : Set (E d) := ⋃ a : TracePiece A F n, ⋃ v : VertexName S a.tile.ty,
    {a.tile.prototypeFrame 0 (vertexPoint v)}
  have hK : IsClosed K := by
    apply isClosed_iUnion_of_finite
    intro z
    exact (z.val.2.val.flat.compact.image
      (z.val.1.tile.prototypeFrame 0).continuous_of_finiteDimensional).isClosed
  have hV : V.Finite := Set.finite_iUnion fun a =>
    Set.finite_iUnion fun v => Set.finite_singleton _
  have hcover : (S.σ ^ n) '' (F.cell edgeIndex).val.carrier ⊆ K ∪ V := by
    intro z hz
    by_cases hzV : z ∈ V
    · exact Or.inr hzV
    apply Or.inl
    have hzb : z ∈ (S.σ ^ n) ''
        (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val.carrier :=
      Set.image_mono (F.nested edgeIndex
        ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩ traceDimension_pos) hz
    rw [← (recursiveTrace_tiles A F n).1] at hzb
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hzb
    have hnv : ¬ a.tile.Lists 0 z := by
      rintro ⟨v, hv, hzv⟩
      let v' : VertexName S a.tile.ty := ⟨v, hv⟩
      have hpoint : z = a.tile.prototypeFrame 0 (vertexPoint v') := by
        change z ∈ a.tile.cell 0 v'.val at hzv
        simpa only [FramedNode.cell, vertexPoint_spec v', Set.image_singleton,
          Set.mem_singleton_iff] using hzv
      exact hzV (Set.mem_iUnion_of_mem a (Set.mem_iUnion_of_mem v' hpoint))
    obtain ⟨e, hze, heh, heb⟩ :=
      host_step_step1_seed_step5_trace_step2_trace_edge A F n a z hza hz hnv
    exact Set.mem_iUnion_of_mem (⟨⟨a, e⟩, heh, heb⟩ : Good) hze
  have hedge' : (S.σ ^ n) '' (F.cell edgeIndex).val.carrier =
      segment ℝ ((S.σ ^ n) x) ((S.σ ^ n) y) := by
    rw [hedge]
    exact image_segment ℝ (S.σ ^ n).toAffineEquiv.toAffineMap x y
  have hxK := host_step_step1_seed_step5_trace_step2_closed_cover K V hK hV
    ((S.σ ^ n) x) ((S.σ ^ n) y) (fun h => hxy ((S.σ ^ n).injective h))
    (hedge' ▸ hcover)
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hxK
  exact ⟨z.val.1, z.val.2, hz, z.property.1, z.property.2⟩

/-- Step 2 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6):
"a segment from p along the ray of h". The radial tangent cone at the first
endpoint of a closed segment is its nonnegative direction ray. -/
private theorem host_step_step1_seed_step5_trace_step2_segment_cone
    (x y : E d) :
    tangentCone (segment ℝ x y) x = {u | ∃ c : ℝ, 0 ≤ c ∧ u = c • (y - x)} := by
  ext u
  constructor
  · rintro ⟨ε, hε, hmem⟩
    let t := ε / 2
    have ht : 0 < t := by dsimp [t]; positivity
    obtain ⟨a, b, ha, hb, hab, he⟩ := hmem t ht (by dsimp [t]; linarith)
    have ha' : a = 1 - b := by linarith
    have he' : t • u = b • (y - x) := by
      have hh := congrArg (fun z : E d => z - x) he
      dsimp only at hh
      rw [add_sub_cancel_left] at hh
      rw [← hh, ha']
      module
    refine ⟨b / t, div_nonneg hb ht.le, ?_⟩
    have hh := congrArg (fun z : E d => t⁻¹ • z) he'
    simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul, div_eq_mul_inv,
      mul_comm] using hh
  · rintro ⟨c, hc, rfl⟩
    have hden : 0 < c + 1 := by linarith
    refine ⟨1 / (c + 1), div_pos zero_lt_one hden, fun t ht htε => ?_⟩
    have htc : t * c < 1 := by
      have := (lt_div_iff₀ hden).mp htε
      nlinarith
    refine ⟨1 - t * c, t * c, by linarith, mul_nonneg ht.le hc, by ring, ?_⟩
    module

/-- Step 2 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6):
"T_p e = T_p h". Any nontrivial convex subsegment containing an endpoint
has the same endpoint ray and affine span as the whole segment. -/
private theorem host_step_step1_seed_step5_trace_step2_subsegment
    (K : Set (E d)) (x y z : E d) (hK : Convex ℝ K)
    (hx : x ∈ K) (hz : z ∈ K) (hzx : z ≠ x) (hsub : K ⊆ segment ℝ x y) :
    affineSpan ℝ K = affineSpan ℝ (segment ℝ x y) ∧
      tangentCone K x = tangentCone (segment ℝ x y) x := by
  obtain ⟨a, b, ha, hb, hab, he⟩ := hsub hz
  have ha' : a = 1 - b := by linarith
  have hz' : z = x + b • (y - x) := by rw [← he, ha']; module
  have hbpos : 0 < b := by
    apply lt_of_le_of_ne hb
    intro h
    apply hzx
    simp only [← h, zero_smul, add_zero] at hz'
    exact hz'
  constructor
  · apply le_antisymm (affineSpan_mono ℝ hsub)
    apply affineSpan_le.mpr
    have hxs := mem_affineSpan ℝ hx
    have hzs := mem_affineSpan ℝ hz
    have hy : y ∈ affineSpan ℝ K := by
      have hh := (affineSpan ℝ K).smul_vsub_vadd_mem b⁻¹ hzs hxs hxs
      have heq : b⁻¹ • (z - x) + x = y := by
        rw [hz', add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hbpos.ne', one_smul]
        module
      exact heq ▸ hh
    exact (affineSpan ℝ K).convex.segment_subset hxs hy
  · apply Set.Subset.antisymm
      (host_step_step1_seed_step5_trace_step1_tangent_mono hsub x)
    rw [host_step_step1_seed_step5_trace_step2_segment_cone]
    rintro u ⟨c, hc, rfl⟩
    have hden : 0 < c + 1 := by linarith
    refine ⟨b / (c + 1), div_pos hbpos hden, fun t ht htε => ?_⟩
    have htc : t * c < b := by
      have := (lt_div_iff₀ hden).mp htε
      nlinarith
    have hs : 0 ≤ t * c / b := div_nonneg (mul_nonneg ht.le hc) hbpos.le
    have hs' : t * c / b ≤ 1 := (div_le_one hbpos).mpr htc.le
    have hm := hK hx hz (by linarith : 0 ≤ 1 - t * c / b) hs
      (by ring : (1 - t * c / b) + t * c / b = 1)
    have heq : (1 - t * c / b) • x + (t * c / b) • z =
        x + t • (c • (y - x)) := by
      rw [hz']
      have hc' : t * c / b * b = t * c := div_mul_cancel₀ _ hbpos.ne'
      simp only [smul_add, smul_smul, hc']
      module
    exact heq ▸ hm

/-- Step 2 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 1.22(a), 3.6):
"with chain cells s_1 contained in ... contained in s_(d-1)".
Adjoin the endpoint edge to the trace piece's recorded cofaces. The trace
theorem supplies the higher affine spans; the subsegment supplies the edge ray. -/
private theorem host_step_step1_seed_step5_trace_step2_full_chain
    (A : S.ι) (F : FacetFlag S A) (n : ℕ) (x y : E d)
    (hxy : x ≠ y) (hedge : (F.cell edgeIndex).val.carrier = segment ℝ x y) :
    ∃ (a : TracePiece A F n) (F' : FacetFlag S a.tile.ty),
      (∀ k, (S.σ ^ n) x ∈ a.tile.cell 0 (F'.cell k).val ∧
        a.tile.cell 0 (F'.cell k).val ⊆ (S.σ ^ n) '' (F.cell k).val.carrier ∧
        affineSpan ℝ (a.tile.cell 0 (F'.cell k).val) =
          affineSpan ℝ ((S.σ ^ n) '' (F.cell k).val.carrier)) ∧
      tangentCone (a.tile.cell 0 (F'.cell edgeIndex).val) ((S.σ ^ n) x) =
        tangentCone ((S.σ ^ n) '' (F.cell edgeIndex).val.carrier) ((S.σ ^ n) x) := by
  classical
  obtain ⟨a, e, hx, hsub, hbottom⟩ :=
    host_step_step1_seed_step5_trace_step2_endpoint_piece A F n x y hxy hedge
  have hindex (k : FlagIndex d) (hk : k ≠ edgeIndex) : traceDimension d ≤ k.val := by
    have hne : k.val ≠ 1 := by
      intro h
      apply hk
      exact Subtype.ext h
    have hpos := k.property.1
    unfold traceDimension
    omega
  let index (k : FlagIndex d) (hk : k ≠ edgeIndex) : ChainIndex d (traceDimension d) :=
    ⟨⟨k.val, k.property.2⟩, hindex k hk, k.property.1⟩
  let F' : FacetFlag S a.tile.ty := {
    cell := fun k => if hk : k = edgeIndex then edgeCell e else a.chain.cell (index k hk)
    dimension := by
      intro k
      split
      · next hk => subst k; exact (Finset.mem_filter.mp e.property).2
      · exact a.chain.dimension _
    nested := by
      intro i j hij
      split <;> split
      · exact Subset.rfl
      · exact hbottom.trans (a.chain.nested _ _ (hindex j ‹_›))
      · next hi hj =>
          have hne : i.val ≠ 1 := fun h => hi (Subtype.ext h)
          have hipos := i.property.1
          subst j
          change i.val ≤ 1 at hij
          omega
      · exact a.chain.nested _ _ hij }
  have hcell : (F'.cell edgeIndex).val = e.val := by simp [F', edgeCell]
  obtain ⟨⟨u, v⟩, huv, huvset⟩ := edge_endpoints_exist (⟨a.tile.ty, e⟩ : EdgeName S)
  have hK : a.tile.cell 0 e.val = segment ℝ (a.tile.frame u) (a.tile.frame v) := by
    change a.tile.prototypeFrame 0 '' e.val.carrier = _
    rw [huvset]
    exact image_segment ℝ (a.tile.prototypeFrame 0).toAffineMap u v
  have hF : (S.σ ^ n) '' (F.cell edgeIndex).val.carrier =
      segment ℝ ((S.σ ^ n) x) ((S.σ ^ n) y) := by
    rw [hedge]
    exact image_segment ℝ (S.σ ^ n).toAffineEquiv.toAffineMap x y
  obtain ⟨z, hz, hzx⟩ : ∃ z ∈ a.tile.cell 0 e.val, z ≠ (S.σ ^ n) x := by
    by_cases hu : a.tile.frame u = (S.σ ^ n) x
    · exact ⟨a.tile.frame v, hK.symm ▸ right_mem_segment ℝ _ _, fun hv =>
        huv (a.tile.frame.injective (hu.trans hv.symm))⟩
    · exact ⟨a.tile.frame u, hK.symm ▸ left_mem_segment ℝ _ _, hu⟩
  have hgeom := host_step_step1_seed_step5_trace_step2_subsegment
    (a.tile.cell 0 e.val) ((S.σ ^ n) x) ((S.σ ^ n) y) z
    (hK.symm ▸ convex_segment _ _) hx hz hzx (hF ▸ hsub)
  refine ⟨a, F', ?_, ?_⟩
  · intro k
    have hcontained : a.tile.cell 0 (F'.cell k).val ⊆
        (S.σ ^ n) '' (F.cell k).val.carrier := by
      by_cases hk : k = edgeIndex
      · subst k; simpa only [hcell] using hsub
      · simpa only [F', dif_neg hk] using a.chain.contained (index k hk)
    refine ⟨?_, hcontained, ?_⟩
    · have hh := Set.image_mono (f := a.tile.prototypeFrame 0)
        (F'.nested edgeIndex k k.property.1)
      exact hh (hcell.symm ▸ hx)
    · by_cases hk : k = edgeIndex
      · subst k; simpa only [hcell, hF] using hgeom.1
      · simpa only [F', dif_neg hk] using
          (recursiveTrace_tiles A F n).2.2 a (index k hk)
  · simpa only [hcell, hF] using hgeom.2

/-- Step 3 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 1.22(a), 3.6):
"a native descendant of P". The recursive address of a selected owner
recovers its actual ancestor in the fixed coherent hierarchy. -/
private theorem host_step_step1_seed_step5_trace_step3_ancestor
    (U : HonestSource S) (h r : ℕ) (N : FramedNode S)
    (hN : N ∈ U.hierarchy.nodes (h + r)) (w : S.RoleWord N.ty r)
    (hc : (S.descendantNode N.ty h r w).move N.frame ∈ U.hierarchy.nodes h) :
    U.hierarchy.ancestor ⟨h, ⟨(S.descendantNode N.ty h r w).move N.frame, hc⟩⟩ r =
      ⟨h + r, ⟨N, hN⟩⟩ := by
  induction r generalizing N with
  | zero =>
    simp [CoherentHierarchy.ancestor, SubstSystem.descendantNode, FramedNode.move]
  | succ r ih =>
    have hchild := U.hierarchy.children_mem (h + r) N
      (by simpa only [Nat.add_assoc] using hN) w.1
    have hc' : (S.descendantNode (N.child (h + r) w.1).ty h r w.2).move
        (N.child (h + r) w.1).frame ∈ U.hierarchy.nodes h := hc
    have hi := ih (N.child (h + r) w.1) hchild w.2 hc'
    rw [← U.hierarchy.ancestor_add]
    change U.hierarchy.parentNode (U.hierarchy.ancestor _ r) = _
    have he : (⟨h, ⟨(S.descendantNode N.ty h (r + 1) w).move N.frame, hc⟩⟩ : U.Node) =
        ⟨h, ⟨(S.descendantNode (N.child (h + r) w.1).ty h r w.2).move
          (N.child (h + r) w.1).frame, hc'⟩⟩ := rfl
    rw [he, hi]
    apply Sigma.ext
    · simp only [CoherentHierarchy.parentNode, Nat.add_assoc]
    · apply heq_of_eq
      apply Subtype.ext
      exact (U.hierarchy.parent_unique (h + r) _ N hN ⟨w.1, rfl⟩).symm

/-- Step 3 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 1.22(a), 3.6):
"a native descendant ... with chain cells". Place the selected trace and
its complete chain in an arbitrary honest source node, preserving its owner. -/
private theorem host_step_step1_seed_step5_trace_step3_source_chain
    (U : HonestSource S) (N : U.Node) (F : FacetFlag S N.2.val.ty) (x y : E d)
    (hxy : x ≠ y) (hedge : (F.cell edgeIndex).val.carrier = segment ℝ x y) :
    ∃ q : U.Node, q.1 = 0 ∧ U.hierarchy.ancestor q N.1 = N ∧
      ∃ F' : FacetFlag S q.2.val.ty,
        (∀ k, N.2.val.prototypeFrame N.1 x ∈ q.2.val.cell q.1 (F'.cell k).val ∧
          q.2.val.cell q.1 (F'.cell k).val ⊆ N.2.val.cell N.1 (F.cell k).val ∧
          affineSpan ℝ (q.2.val.cell q.1 (F'.cell k).val) =
            affineSpan ℝ (N.2.val.cell N.1 (F.cell k).val)) ∧
        tangentCone (q.2.val.cell q.1 (F'.cell edgeIndex).val)
            (N.2.val.prototypeFrame N.1 x) =
          tangentCone (N.2.val.cell N.1 (F.cell edgeIndex).val)
            (N.2.val.prototypeFrame N.1 x) := by
  obtain ⟨a, F', hfit, hray⟩ :=
    host_step_step1_seed_step5_trace_step2_full_chain N.2.val.ty F N.1 x y hxy hedge
  have hm : a.tile.move N.2.val.frame ∈ U.hierarchy.nodes 0 := by
    simpa only [Nat.sub_self] using U.descendant_mem N N.1 le_rfl a.owner
  let q : U.Node := ⟨0, ⟨a.tile.move N.2.val.frame, hm⟩⟩
  have hqcell (e : Cell d) : q.2.val.cell q.1 e = N.2.val.frame '' a.tile.cell 0 e := by
    simp only [q, FramedNode.cell, FramedNode.prototypeFrame, FramedNode.move,
      Set.image_image]
    rfl
  have hNcell (e : Cell d) : N.2.val.cell N.1 e = N.2.val.frame '' ((S.σ ^ N.1) '' e.carrier) := by
    simp only [FramedNode.cell, FramedNode.prototypeFrame, Set.image_image]
    rfl
  refine ⟨q, rfl, ?_, F', ?_, ?_⟩
  · have hh := host_step_step1_seed_step5_trace_step3_ancestor U 0 N.1 N.2.val
        (by simpa only [Nat.zero_add] using N.2.property) a.owner hm
    rcases N with ⟨n, N, hN⟩
    refine hh.trans (Sigma.ext (Nat.zero_add n) ?_)
    exact (Subtype.heq_iff_coe_eq (by
      intro M
      change M ∈ U.hierarchy.nodes (0 + n) ↔ M ∈ U.hierarchy.nodes n
      rw [Nat.zero_add])).mpr rfl
  · intro k
    rw [hqcell, hNcell]
    refine ⟨Set.mem_image_of_mem N.2.val.frame (hfit k).1,
      Set.image_mono (hfit k).2.1, ?_⟩
    simpa only [AffineSubspace.map_span] using congrArg
      (AffineSubspace.map N.2.val.frame.toAffineEquiv.toAffineMap) (hfit k).2.2
  · rw [hqcell, hNcell]
    change tangentCone (N.2.val.frame.toAffineEquiv '' _)
        (N.2.val.frame.toAffineEquiv ((S.σ ^ N.1) x)) =
      tangentCone (N.2.val.frame.toAffineEquiv '' _)
        (N.2.val.frame.toAffineEquiv ((S.σ ^ N.1) x))
    rw [host_step_step1_seed_step5_trace_step1_tangent_image N.2.val.frame.toAffineEquiv,
      host_step_step1_seed_step5_trace_step1_tangent_image N.2.val.frame.toAffineEquiv,
      hray]

/-- Step 4 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 1.7(a), 3.6):
"the selected owner ... a member of the star". A descendant facet of an
internal child facet retains its birth parent, canonical incidence and child side.
All three geometric identifications of the child facet are explicit hypotheses. -/
private theorem host_step_step1_seed_step5_trace_step4_provider
    (U : HonestSource S) (c q : U.Node) (f : FacetName S c.2.val.ty)
    (g : FacetName S q.2.val.ty) (r : ℕ) (hanc : U.hierarchy.ancestor q r = c)
    (hsub : q.2.val.cell q.1 g.val ⊆ c.2.val.cell c.1 f.val)
    (hint : relint (c.2.val.cell c.1 f.val) ⊆
      interior ((U.hierarchy.parentNode c).2.val.carrier (U.hierarchy.parentNode c).1))
    (ι : P.Incidence) (b : Bool)
    (hrole : U.hierarchy.nodeRole c = ι.val.sideRole b)
    (hpos : c.2.val.cell c.1 f.val =
      P.incidencePlacement (U.hierarchy.parentNode c).2.val
        (U.hierarchy.parentNode c).1 ι '' ι.val.leftFacet.val.carrier) :
    ∃ hg : ¬ U.hierarchy.IsFault q g,
      U.hierarchy.birthParent q g hg = U.hierarchy.parentNode c ∧
      U.hierarchy.servingChild q g hg = c ∧
      U.recordIncidence P q g hg = ι ∧ U.recordSide P q g hg = b := by
  obtain ⟨hf, hfc, hfb, _⟩ := U.hierarchy.restriction_det_internal c f hint
  obtain ⟨hg, hgc, hgb⟩ := U.hierarchy.provider_inherited c q r hanc f g hf hsub
  have hbirth : U.hierarchy.birthParent q g hg = U.hierarchy.parentNode c := hgb.trans hfb
  have hserv : U.hierarchy.servingChild q g hg = c := by
    have hh := congrArg (fun n : U.Node => n.1) hbirth
    change (U.hierarchy.servingChild q g hg).1 + 1 = c.1 + 1 at hh
    have hs := U.hierarchy.ancestor_height q (U.hierarchy.firstProvider q g hg).1
    have ha := U.hierarchy.ancestor_height q r
    rw [hanc] at ha
    have hoff : (U.hierarchy.firstProvider q g hg).1 = r := by
      change (U.hierarchy.servingChild q g hg).1 = _ at hs
      omega
    simpa only [CoherentHierarchy.servingChild, hoff] using hanc
  have hinc : U.recordIncidence P q g hg = ι := by
    have hs := U.hierarchy.providerIncidence_spec q g hg
    apply P.canonical_unique
    constructor
    · exact hs.1.trans ((congrArg (fun N : U.Node => N.2.val.ty) hbirth).trans
        (congrArg Sigma.fst hrole))
    · have hcarrier := hgc.trans (hfc.trans hpos)
      rw [hs.2.2.2] at hcarrier
      change (U.hierarchy.birthParent q g hg).2.val.prototypeFrame
          (U.hierarchy.birthParent q g hg).1 ''
          (S.σ.symm '' (U.hierarchy.providerIncidence q g hg).positioned) = _ at hcarrier
      rw [hbirth] at hcarrier
      have hright : P.incidencePlacement (U.hierarchy.parentNode c).2.val
          (U.hierarchy.parentNode c).1 ι '' ι.val.leftFacet.val.carrier =
          (U.hierarchy.parentNode c).2.val.prototypeFrame (U.hierarchy.parentNode c).1 ''
            (S.σ.symm '' ι.val.positioned) := by
        simp only [Params.incidencePlacement, PrimitiveIncidence.positioned, placedSet,
          Set.image_image]
        rfl
      rw [hright] at hcarrier
      exact S.σ.symm.injective.image_injective
        (((U.hierarchy.parentNode c).2.val.prototypeFrame
          (U.hierarchy.parentNode c).1).injective.image_injective hcarrier)
  refine ⟨hg, hbirth, hserv, hinc, ?_⟩
  apply Eq.symm
  apply (Classical.choose_spec (U.recordSide_exists P q g hg)).2
  rw [hinc, hserv, hrole]

/-- Step 3 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6):
"the flag ... transported to P". Relative interiors commute with the full
invertible affine prototype frames, including anisotropic expansion. -/
private theorem host_step_step1_seed_step5_trace_step3_relint_image
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

/-- Step 3 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6):
"the child on the j-side". Distinct prescribed child roles give distinct
framed children, by disjointness and nonempty prototype interiors. -/
private theorem host_step_step1_seed_step5_trace_step3_child_injective
    (N : FramedNode S) (n : ℕ) : Function.Injective (N.child n) := by
  intro i j h
  have hty := congrArg FramedNode.ty h
  have hframe : (S.child N.ty i).frame = (S.child N.ty j).frame := by
    apply AffineIsometryEquiv.ext
    intro x
    have he := congrArg (fun M : FramedNode S => M.prototypeFrame n x) h
    change N.frame (S.placeChild n i ((S.σ ^ n) x)) =
      N.frame (S.placeChild n j ((S.σ ^ n) x)) at he
    have hi (k : S.I N.ty) : S.placeChild n k ((S.σ ^ n) x) =
        (S.σ ^ n) ((S.child N.ty k).frame x) := by
      rw [S.placeChild_apply]
      simp [linearConj, Child.frame, rigidMotion, zpow_neg, LinearEquiv.mul_apply,
        ← map_add]
    rw [hi, hi] at he
    exact (S.σ ^ n).injective (N.frame.injective he)
  by_contra hij
  have hd := S.children_disjoint N.ty hij
  change (S.child N.ty i).ty = (S.child N.ty j).ty at hty
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

/-- Step 3 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6):
"the child on the j-side". The actual hierarchy parent and role of a
prescribed child agree with its prescribed parent and child index. -/
private theorem host_step_step1_seed_step5_trace_step3_child_role
    (U : HonestSource S) (N : FramedNode S) (n : ℕ)
    (hN : N ∈ U.hierarchy.nodes (n + 1)) (i : S.I N.ty)
    (hc : N.child n i ∈ U.hierarchy.nodes n) :
    U.hierarchy.parentNode ⟨n, ⟨N.child n i, hc⟩⟩ = ⟨n + 1, ⟨N, hN⟩⟩ ∧
      U.hierarchy.nodeRole ⟨n, ⟨N.child n i, hc⟩⟩ = ⟨N.ty, i⟩ := by
  let c : U.Node := ⟨n, ⟨N.child n i, hc⟩⟩
  have hp : (U.hierarchy.parent n c.2).val = N :=
    (U.hierarchy.parent_unique n c.2 N hN ⟨i, rfl⟩).symm
  refine ⟨Sigma.ext rfl (heq_of_eq (Subtype.ext hp)), ?_⟩
  have he := U.hierarchy.child_eq n c.2
  change (⟨(U.hierarchy.parent n c.2).val.ty, U.hierarchy.role n c.2⟩ : S.Role) = _
  have aux (M : FramedNode S) (j : S.I M.ty) (hM : M = N)
      (h : N.child n i = M.child n j) : (⟨M.ty, j⟩ : S.Role) = ⟨N.ty, i⟩ := by
    subst M
    exact congrArg (Sigma.mk N.ty)
      ((host_step_step1_seed_step5_trace_step3_child_injective N n h).symm)
  exact aux _ _ hp he

/-- Step 3 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6):
"with respect to the flag of the incidence". Both side flags end at the
named incidence facet, since their positioned cell carriers agree. -/
private theorem host_step_step1_seed_step5_trace_step3_flag_top
    (ι : P.Incidence) (b : Bool) :
    ((P.sideFlag ι b).cell facetIndex).val = (ι.val.sideFacet b).val := by
  have h := P.sideFlag_eq ι b facetIndex
  rw [(P.flag ι).top] at h
  have hcarrier : ((P.sideFlag ι b).cell facetIndex).val.carrier =
      (ι.val.sideFacet b).val.carrier := by
    apply (S.child ι.val.ty (ι.val.sideIndex b)).frame.injective.image_injective
    change placedSet (S.child ι.val.ty (ι.val.sideIndex b)).frame _ = _
    rw [h]
    cases b
    · rfl
    · exact ι.val.paired
  have cell_eq (e f : Cell d) (h : e.carrier = f.carrier) : e = f := by
    rcases e with ⟨K, j, hj⟩
    rcases f with ⟨L, k, hk⟩
    cases h
    have hjk : j = k := hj.dimension.symm.trans hk.dimension
    cases hjk
    rfl
  exact cell_eq _ _ hcarrier

/-- Step 3 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6):
"the flag ... transported to P". Either child-side flag has exactly the
canonical positioned cells, with the full expansion in its prototype frame. -/
private theorem host_step_step1_seed_step5_trace_step3_side_cells
    (Q : FramedNode S) (n : ℕ) (ι : P.Incidence) (b : Bool) (k : FlagIndex d) :
    ((⟨ι.val.ty, Q.frame⟩ : FramedNode S).child n (ι.val.sideIndex b)).cell n
        ((P.sideFlag ι b).cell k).val =
      P.incidencePlacement Q (n + 1) ι '' ((P.flag ι).flag.cell k).val.carrier := by
  rw [← host_step_step1_seed_step1_flag_frame Q n ι b]
  have h := congrArg (fun K : Set (E d) =>
      ((⟨ι.val.ty, Q.frame⟩ : FramedNode S).child n (ι.val.sideIndex b)).prototypeFrame n ''
        ((S.child ι.val.ty (ι.val.sideIndex b)).frame.symm '' K)) (P.sideFlag_eq ι b k)
  simpa only [FramedNode.cell, host_step_flagFrame, placedSet, Set.image_image,
    AffineIsometryEquiv.symm_apply_apply] using h

/-- Step 3 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6, 1.4(c)):
"the child on the j-side with respect to the flag of the incidence".
The prescribed child has the canonical positioned flag, the listed endpoint,
and an internal top facet. This constructs no descendant or port. -/
private theorem host_step_step1_seed_step5_trace_step3_side_child
    (U : HonestSource S) (B : U.Node) (hB : 1 ≤ B.1)
    (ι : P.Incidence) (hι : ι.val.ty = B.2.val.ty) (b : Bool)
    (p : E d) (hp : p = (P.flag ι).initial ∨ p = (P.flag ι).terminal) :
    ∃ (c : U.Node) (f : FacetName S c.2.val.ty) (F : FlagChain f) (x y : E d),
      U.hierarchy.parentNode c = B ∧ U.hierarchy.nodeRole c = ι.val.sideRole b ∧
      x ≠ y ∧ (F.val.cell edgeIndex).val.carrier = segment ℝ x y ∧
      c.2.val.prototypeFrame c.1 x = P.incidencePlacement B.2.val B.1 ι p ∧
      c.2.val.Lists c.1 (c.2.val.prototypeFrame c.1 x) ∧
      (∀ k, c.2.val.cell c.1 (F.val.cell k).val =
        P.incidencePlacement B.2.val B.1 ι '' ((P.flag ι).flag.cell k).val.carrier) ∧
      relint (c.2.val.cell c.1 f.val) ⊆ interior (B.2.val.carrier B.1) := by
  classical
  rcases B with ⟨m, ⟨⟨A, φ⟩, hN⟩⟩
  cases m with
  | zero => change 1 ≤ 0 at hB; omega
  | succ n =>
    dsimp only at hι
    subst A
    let Q : FramedNode S := ⟨ι.val.ty, φ⟩
    have hc := U.hierarchy.children_mem n Q hN (ι.val.sideIndex b)
    let c : U.Node := ⟨n, ⟨Q.child n (ι.val.sideIndex b), hc⟩⟩
    have hcr := host_step_step1_seed_step5_trace_step3_child_role U Q n hN
      (ι.val.sideIndex b) hc
    let J : E d ≃ᵃ[ℝ] E d := (S.child ι.val.ty ι.val.left).frame.toAffineEquiv.trans
      (S.child ι.val.ty (ι.val.sideIndex b)).frame.symm.toAffineEquiv
    obtain ⟨p', hpp', hedge⟩ : ∃ p' : E d, p ≠ p' ∧
        ((P.flag ι).flag.cell edgeIndex).val.carrier = segment ℝ p p' := by
      rcases hp with rfl | rfl
      · exact ⟨_, (P.flag ι).distinct, (P.flag ι).edge_eq⟩
      · exact ⟨_, (P.flag ι).distinct.symm,
          (P.flag ι).edge_eq.trans (segment_symm ℝ _ _)⟩
    have hseg : ((P.sideFlag ι b).cell edgeIndex).val.carrier =
        segment ℝ (J p) (J p') := by
      apply (S.child ι.val.ty (ι.val.sideIndex b)).frame.injective.image_injective
      change placedSet (S.child ι.val.ty (ι.val.sideIndex b)).frame _ = _
      rw [P.sideFlag_eq, hedge]
      change (S.child ι.val.ty ι.val.left).frame.toAffineEquiv.toAffineMap '' segment ℝ p p' =
        (S.child ι.val.ty (ι.val.sideIndex b)).frame.toAffineEquiv.toAffineMap ''
          segment ℝ (J p) (J p')
      rw [image_segment ℝ (S.child ι.val.ty ι.val.left).frame.toAffineEquiv.toAffineMap,
        image_segment ℝ (S.child ι.val.ty (ι.val.sideIndex b)).frame.toAffineEquiv.toAffineMap]
      simp only [J, AffineEquiv.trans_apply,
        AffineIsometryEquiv.coe_toAffineEquiv, AffineEquiv.coe_toAffineMap,
        AffineIsometryEquiv.apply_symm_apply]
    have hpoint : c.2.val.prototypeFrame c.1 (J p) =
        P.incidencePlacement Q (n + 1) ι p := by
      exact congrArg (fun e : E d ≃ᵃ[ℝ] E d => e p)
        (host_step_step1_seed_step1_flag_frame Q n ι b)
    have hcells (k : FlagIndex d) : c.2.val.cell c.1 ((P.sideFlag ι b).cell k).val =
        P.incidencePlacement Q (n + 1) ι '' ((P.flag ι).flag.cell k).val.carrier :=
      host_step_step1_seed_step5_trace_step3_side_cells Q n ι b k
    refine ⟨c, ι.val.sideFacet b,
      ⟨P.sideFlag ι b, host_step_step1_seed_step5_trace_step3_flag_top ι b⟩,
      J p, J p', hcr.1, hcr.2, fun he => hpp' (J.injective he), hseg, hpoint, ?_, hcells, ?_⟩
    · rw [hpoint]
      exact (host_step_step1_seed_step2_child_endpoint Q n ι b p hp).1
    · have hfacet := hcells facetIndex
      rw [host_step_step1_seed_step5_trace_step3_flag_top, (P.flag ι).top] at hfacet
      rw [hfacet]
      let H : E d ≃ᵃ[ℝ] E d := (S.σ ^ n).toAffineEquiv.trans φ.toAffineEquiv
      have hpos : P.incidencePlacement Q (n + 1) ι '' ι.val.leftFacet.val.carrier =
          H '' ι.val.positioned := by
        simp only [Params.incidencePlacement, FramedNode.prototypeFrame,
          PrimitiveIncidence.positioned, placedSet, Set.image_image]
        congr 1
        funext z
        change φ ((S.σ ^ (n + 1)) (S.σ.symm ((S.child ι.val.ty ι.val.left).frame z))) =
          φ ((S.σ ^ n) ((S.child ι.val.ty ι.val.left).frame z))
        simp only [pow_succ, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
      have hcarrier : Q.carrier (n + 1) = H '' S.supertile 1 ι.val.ty := by
        simp only [FramedNode.carrier, SubstSystem.supertile, H, placedSet, pow_succ,
          pow_zero, one_mul, Set.image_image]
        rfl
      change relint _ ⊆ interior (Q.carrier (n + 1))
      rw [hpos, hcarrier, host_step_step1_seed_step5_trace_step3_relint_image]
      change H.toHomeomorphOfFiniteDimensional '' relint ι.val.positioned ⊆
        interior (H.toHomeomorphOfFiniteDimensional '' S.supertile 1 ι.val.ty)
      rw [← Homeomorph.image_interior]
      exact Set.image_mono ι.val.internal

/-- Step 5 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6):
"realised ... in the tile's frame". Translating a direction cone to its
apex commutes with the affine change of frame. -/
private theorem host_step_step1_seed_step5_trace_step5_span_image
    (φ : E d ≃ᵃ[ℝ] E d) (x : E d) (K : Set (E d)) :
    affineSpan ℝ ((fun u => φ x + u) '' (φ.linear '' K)) =
      (affineSpan ℝ ((fun u => x + u) '' K)).map φ.toAffineMap := by
  rw [AffineSubspace.map_span]
  congr 1
  simp only [Set.image_image]
  congr 1
  funext u
  simpa only [vadd_eq_add, add_comm] using (φ.map_vadd x u).symm

/-- Step 5 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6):
"aff s_j = aff F_j" in the recording frame. The affine span of a placed
cell is also the affine span of its translated tangent cone. -/
private theorem host_step_step1_seed_step5_trace_step5_placed_span
    (φ : E d ≃ᵃ[ℝ] E d) (e : Cell d) (x : E d) (hx : x ∈ φ '' e.carrier) :
    affineSpan ℝ ((fun u => x + u) '' tangentCone (φ '' e.carrier) x) =
      affineSpan ℝ (φ '' e.carrier) := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [host_step_step1_seed_step5_trace_step1_tangent_image,
    host_step_step1_seed_step5_trace_step5_span_image,
    host_step_step1_seed_step5_trace_step1_cone_span e y hy,
    AffineSubspace.map_span]
  rfl

/-- Step 5 of the V4 proof of `host_step_step1_seed_step5_trace` (V4 3.6):
"aff s_j = aff F_j and T_p s_j is contained in T_p F_j".
A contained cell with the correct affine span fits the flag tangent after
normalization in the central tile's frame. -/
private theorem host_step_step1_seed_step5_trace_step5_fit
    (φ ψ : E d ≃ᵃ[ℝ] E d) (e : Cell d) (K : Set (E d)) (x : E d)
    (hx : x ∈ K) (hsub : K ⊆ ψ '' e.carrier)
    (hspan : affineSpan ℝ K = affineSpan ℝ (ψ '' e.carrier)) :
    φ x ∈ φ '' K ∧
      affineSpan ℝ (φ '' K) = affineSpan ℝ ((fun u => φ x + u) ''
        (φ.linear '' tangentCone (ψ '' e.carrier) x)) ∧
      tangentCone (φ '' K) (φ x) ⊆ φ.linear '' tangentCone (ψ '' e.carrier) x := by
  refine ⟨Set.mem_image_of_mem φ hx, ?_, ?_⟩
  · rw [host_step_step1_seed_step5_trace_step5_span_image,
      host_step_step1_seed_step5_trace_step5_placed_span ψ e x (hsub hx),
      ← hspan, AffineSubspace.map_span]
    rfl
  · rw [host_step_step1_seed_step5_trace_step1_tangent_image]
    exact Set.image_mono (host_step_step1_seed_step5_trace_step1_tangent_mono hsub x)

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
  classical
  obtain ⟨U, t, ht, f, hf, v, hv, hz, hreal⟩ := hZ
  obtain ⟨htype, hvertex, hheader, htiles, hports, hboundary⟩ := hreal
  let B := U.hierarchy.birthParent t f hf
  let x := t.2.val.prototypeFrame t.1 (vertexPoint v)
  let pos := P.incidencePlacement B.2.val B.1 ι
  have hdata : ι.val.ty = B.2.val.ty ∧
      (x = pos (P.flag ι).initial ∨ x = pos (P.flag ι).terminal) ∧
      ∀ k, G.cones k = U.normalizeCone t
        (tangentCone (pos '' ((P.flag ι).flag.cell k).val.carrier) x) := by
    have hh : (U.headerOf P t f hf v).flagTangent ι = some G := by
      rw [← hheader]
      exact hG
    unfold HonestSource.headerOf at hh
    dsimp only at hh
    split at hh
    · next h =>
      refine ⟨h.1, h.2, ?_⟩
      intro k
      exact congrArg (fun T : State.FlagTangent (d := d) => T.cones k)
        (Option.some.inj hh).symm
    · contradiction
  have hB : 1 ≤ B.1 := by
    have h := (U.hierarchy.birthHeight_age_spec t f hf).1
    change B.1 = t.1 + (U.hierarchy.firstProvider t f hf).1 + 1 at h
    omega
  obtain ⟨p, hp, hpx⟩ : ∃ p : E d,
      (p = (P.flag ι).initial ∨ p = (P.flag ι).terminal) ∧ pos p = x := by
    rcases hdata.2.1 with h | h
    · exact ⟨_, Or.inl rfl, h.symm⟩
    · exact ⟨_, Or.inr rfl, h.symm⟩
  obtain ⟨c, f₀, F₀, p₀, p₁, hparent, hrole, hpne, hedge, hpoint, hlisted,
      hcells, hint⟩ :=
    host_step_step1_seed_step5_trace_step3_side_child U B hB ι hdata.1 b p hp
  have hcpoint : c.2.val.prototypeFrame c.1 p₀ = x := hpoint.trans hpx
  obtain ⟨q, hq, hanc, F, hfit, hray⟩ :=
    host_step_step1_seed_step5_trace_step3_source_chain U c F₀.val p₀ p₁ hpne hedge
  rw [hcpoint] at hfit hray hlisted
  let g : FacetName S q.2.val.ty := ⟨(F.cell facetIndex).val,
    Finset.mem_filter.mpr ⟨(F.cell facetIndex).property, F.dimension facetIndex⟩⟩
  have htop : q.2.val.cell q.1 g.val ⊆ c.2.val.cell c.1 f₀.val := by
    simpa only [F₀.property] using (hfit facetIndex).2.1
  have hpos : c.2.val.cell c.1 f₀.val =
      P.incidencePlacement (U.hierarchy.parentNode c).2.val
        (U.hierarchy.parentNode c).1 ι '' ι.val.leftFacet.val.carrier := by
    rw [hparent]
    simpa only [F₀.property, (P.flag ι).top] using hcells facetIndex
  obtain ⟨hg, hbirth, hserv, hinc, hside⟩ :=
    host_step_step1_seed_step5_trace_step4_provider U c q f₀ g c.1 hanc htop
      (by rw [hparent]; exact hint) ι b hrole hpos
  have hbirth' : U.hierarchy.birthParent q g hg = B := hbirth.trans hparent
  have hqmem : x ∈ q.2.val.carrier q.1 := by
    obtain ⟨z, hz, he⟩ := (hfit edgeIndex).1
    exact ⟨(S.σ ^ q.1) z,
      ⟨z, host_step_step1_seed_step2_cell_subset _ _ (F.cell edgeIndex).property hz, rfl⟩, he⟩
  have hdesc := U.hierarchy.ancestor_descendant q c.1
  rw [hanc] at hdesc
  obtain ⟨w, hw, hxw⟩ := commonListed_inherited c.2.val q.2.val c.1 q.1 hdesc x hlisted hqmem
  let w' : VertexName S q.2.val.ty := ⟨w, hw⟩
  have hwpoint : q.2.val.prototypeFrame q.1 (vertexPoint w') = x := by
    change x ∈ q.2.val.cell q.1 w'.val at hxw
    simpa only [FramedNode.cell, vertexPoint_spec w', Set.image_singleton,
      Set.mem_singleton_iff, eq_comm] using hxw
  have hwfacet : w'.val.carrier ⊆ g.val.carrier := by
    rw [vertexPoint_spec w']
    apply singleton_subset_iff.mpr
    have hh := (hfit facetIndex).1
    change x ∈ q.2.val.prototypeFrame q.1 '' g.val.carrier at hh
    rw [← hwpoint] at hh
    exact (q.2.val.prototypeFrame q.1).injective.mem_set_image.mp hh
  have hzero := host_step_step1_seed_step3_restricted_header_step5_zero (P := P)
    U q g hg w' hwfacet (by rw [hserv, hwpoint]; exact hlisted)
  have hstar : q ∈ ownedStar U B x := by
    change q ∈ (ownedStarSet_finite U B x).toFinset
    rw [Set.Finite.mem_toFinset]
    refine ⟨hq, ?_, hqmem⟩
    have hh := congrArg (fun N : U.Node => N.1) hparent
    change c.1 + 1 = B.1 at hh
    rw [← hh, ← U.hierarchy.ancestor_add, hanc]
    exact hparent
  let a : PrimitivePort P := {
    tile := q.2.val.move t.2.val.frame.symm
    facet := g
    vertex := w'
    onFacet := hwfacet
    incidence := U.recordIncidence P q g hg
    sideIndex := U.recordSide P q g hg
    side := (U.recordIncidence P q g hg).val.sideRole (U.recordSide P q g hg)
    side_eq := rfl
    providerVertex := U.recordTau P q g hg ⟨vertexCell w', hwfacet⟩
    provider_zero := hzero }
  have ha : a ∈ Z.primitivePorts := by
    apply (hports a).mpr
    exact ⟨q, hstar, g, hg, w', hwfacet, hwpoint.symm, hbirth',
      rfl, rfl, rfl, rfl, rfl, rfl⟩
  let φ : E d ≃ᵃ[ℝ] E d := t.2.val.frame.symm.toAffineEquiv
  have hvpoint : vertexPoint Z.vertex = vertexPoint v := by
    have hh := congrArg Cell.carrier hvertex
    rw [vertexPoint_spec Z.vertex, vertexPoint_spec v] at hh
    exact Set.singleton_injective hh
  have htframe : t.2.val.prototypeFrame t.1 = t.2.val.frame.toAffineEquiv := by
    exact (congrArg (fun n => t.2.val.prototypeFrame n) ht).trans rfl
  have hφx : φ x = vertexPoint Z.vertex := by
    change t.2.val.frame.symm (t.2.val.prototypeFrame t.1 (vertexPoint v)) = _
    rw [htframe]
    change t.2.val.frame.symm (t.2.val.frame (vertexPoint v)) = _
    rw [AffineIsometryEquiv.symm_apply_apply]
    exact hvpoint.symm
  have hnorm (K : Set (E d)) : U.normalizeCone t K = φ.linear '' K := by
    unfold HonestSource.normalizeCone
    rw [htframe]
    rfl
  have hcones (k : FlagIndex d) : G.cones k = φ.linear ''
      tangentCone (pos '' ((P.flag ι).flag.cell k).val.carrier) x := by
    rw [hdata.2.2 k, hnorm]
  have hplaced (e : Cell d) : placedSet a.tile.frame e.carrier = φ '' q.2.val.cell q.1 e := by
    rw [congrArg (fun n => q.2.val.cell n e) hq]
    simp only [a, φ, FramedNode.move, FramedNode.cell, FramedNode.prototypeFrame,
      placedSet, Set.image_image]
    rfl
  refine ⟨a, ha, hinc, hside, ⟨F, rfl⟩, ?_, ?_⟩
  · intro k
    rw [hplaced, ← hφx, hcones]
    apply host_step_step1_seed_step5_trace_step5_fit φ pos
      ((P.flag ι).flag.cell k).val (q.2.val.cell q.1 (F.cell k).val) x (hfit k).1
    · exact (hfit k).2.1.trans_eq (hcells k)
    · exact (hfit k).2.2.trans (congrArg (affineSpan ℝ) (hcells k))
  · rw [hplaced, ← hφx, hcones,
      host_step_step1_seed_step5_trace_step1_tangent_image, hray, hcells edgeIndex]


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

/-- Step 1 of the V4 proof of `host_step_step1_seed_step8_transport` (V4 3.6):
"the realised flag tangent cones ... equal the actual T_p₀ F_j".
Affine transport sends a radial tangent cone by the linear part of the frame. -/
private theorem host_step_step1_seed_step8_transport_step1_tangent_image
    (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) (x : E d) :
    tangentCone (e '' K) (e x) = e.linear '' tangentCone K x := by
  have hmap (y u : E d) (t : ℝ) : e (y + t • u) = e y + t • e.linear u := by
    simpa only [vadd_eq_add, add_comm, map_smul] using e.map_vadd y (t • u)
  ext u
  constructor
  · rintro ⟨ε, hε, hu⟩
    refine ⟨e.linear.symm u, ⟨ε, hε, ?_⟩, e.linear.apply_symm_apply u⟩
    intro t ht htε
    apply e.injective.mem_set_image.mp
    simpa only [hmap, e.linear.apply_symm_apply] using hu t ht htε
  · rintro ⟨u, ⟨ε, hε, hu⟩, rfl⟩
    refine ⟨ε, hε, ?_⟩
    intro t ht htε
    rw [← hmap]
    exact Set.mem_image_of_mem e (hu t ht htε)

/-- Step 1 of the V4 proof of `host_step_step1_seed_step8_transport` (V4 3.6):
"we have aff s_j = aff F_j". Translating a radial tangent direction back
to its base point stays in the affine span of the original set. -/
private theorem host_step_step1_seed_step8_transport_step1_tangent_span
    (K : Set (E d)) (x : E d) (hx : x ∈ K) :
    (fun v => x + v) '' tangentCone K x ⊆ affineSpan ℝ K := by
  rintro _ ⟨v, ⟨ε, hε, hv⟩, rfl⟩
  have ht : 0 < ε / 2 := by positivity
  have hm := mem_affineSpan ℝ (hv (ε / 2) ht (by linarith))
  have hdir : (ε / 2) • v ∈ (affineSpan ℝ K).direction := by
    simpa only [vsub_eq_sub, add_sub_cancel_left] using
      AffineSubspace.vsub_mem_direction hm (mem_affineSpan ℝ hx)
  have hvdir : v ∈ (affineSpan ℝ K).direction :=
    (Submodule.smul_mem_iff _ ht.ne').mp hdir
  simpa only [vadd_eq_add, add_comm] using
    AffineSubspace.vadd_mem_of_mem_direction hvdir (mem_affineSpan ℝ hx)

/-- Step 2 of the V4 proof of `host_step_step1_seed_step8_transport` (V4 3.6):
"we have aff s_j = aff F_j". A tangent fit gives inclusion of affine
spans; the two cells' equal dimensions turn that inclusion into equality. -/
private theorem host_step_step1_seed_step8_transport_step2_span
    (e f : Cell d) (ψ χ : E d ≃ᵃ[ℝ] E d) (hd : e.dim = f.dim)
    (x : E d) (hx : x ∈ χ '' f.carrier)
    (hfit : affineSpan ℝ (ψ '' e.carrier) =
      affineSpan ℝ ((fun v => x + v) '' tangentCone (χ '' f.carrier) x)) :
    affineSpan ℝ (ψ '' e.carrier) = affineSpan ℝ (χ '' f.carrier) := by
  have hle : affineSpan ℝ (ψ '' e.carrier) ≤ affineSpan ℝ (χ '' f.carrier) := by
    rw [hfit]
    exact affineSpan_le.mpr
      (host_step_step1_seed_step8_transport_step1_tangent_span _ x hx)
  apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le _ _ hle
  · apply Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
    change Module.finrank ℝ (affineSpan ℝ (ψ.toAffineMap '' e.carrier)).direction =
      Module.finrank ℝ (affineSpan ℝ (χ.toAffineMap '' f.carrier)).direction
    rw [← AffineSubspace.map_span, ← AffineSubspace.map_span,
      AffineSubspace.map_direction, AffineSubspace.map_direction]
    change Module.finrank ℝ ((affineSpan ℝ e.carrier).direction.map
        (ψ.linear : E d →ₗ[ℝ] E d)) =
      Module.finrank ℝ ((affineSpan ℝ f.carrier).direction.map
        (χ.linear : E d →ₗ[ℝ] E d))
    rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]
    exact e.flat.dimension.trans (hd.trans f.flat.dimension.symm)
  · exact (e.flat.connected.nonempty.image ψ).mono (subset_affineSpan ℝ _)

/-- Step 3 of the V4 proof of `host_step_step1_seed_step8_transport` (V4 3.6):
"the oriented flag ... transported to P". The two incidence-side names
give the same positioned cell at every dimension of the flag. -/
private theorem host_step_step1_seed_step8_transport_step3_cells
    (H : FramedNode S) (n : ℕ) (ι : P.Incidence) (b : Bool) (k : FlagIndex d) :
    H.cell n ((P.sideFlag ι b).cell k).val =
      host_step_flagFrame H n ι b '' ((P.flag ι).flag.cell k).val.carrier := by
  change H.prototypeFrame n '' ((P.sideFlag ι b).cell k).val.carrier = _
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hm : (S.child ι.val.ty (ι.val.sideIndex b)).frame y ∈
        placedSet (S.child ι.val.ty ι.val.left).frame
          ((P.flag ι).flag.cell k).val.carrier := by
      rw [← P.sideFlag_eq ι b k]
      exact ⟨y, hy, rfl⟩
    obtain ⟨z, hz, heq⟩ := hm
    refine ⟨z, hz, ?_⟩
    change H.prototypeFrame n
      ((S.child ι.val.ty (ι.val.sideIndex b)).frame.symm
        ((S.child ι.val.ty ι.val.left).frame z)) = H.prototypeFrame n y
    rw [heq, AffineIsometryEquiv.symm_apply_apply]
  · rintro ⟨z, hz, rfl⟩
    have hm : (S.child ι.val.ty ι.val.left).frame z ∈
        placedSet (S.child ι.val.ty (ι.val.sideIndex b)).frame
          ((P.sideFlag ι b).cell k).val.carrier := by
      rw [P.sideFlag_eq ι b k]
      exact ⟨z, hz, rfl⟩
    obtain ⟨y, hy, heq⟩ := hm
    refine ⟨y, hy, ?_⟩
    change H.prototypeFrame n y = H.prototypeFrame n
      ((S.child ι.val.ty (ι.val.sideIndex b)).frame.symm
        ((S.child ι.val.ty ι.val.left).frame z))
    rw [← heq, AffineIsometryEquiv.symm_apply_apply]

/-- Step 1 of the V4 proof of `host_step_step1_seed_step8_transport_step4_coface` (V4 1.0(a)):
"each component is inside or outside A". On a connected set on which boundary
membership is constant, membership in a closed set is constant as well. -/
private lemma host_step_step1_seed_step8_transport_step4_coface_step1_connected_membership
    {X : Type*} [TopologicalSpace X] {S T : Set X}
    (hS : IsClosed S) (hT : IsPreconnected T)
    (hb : ∀ x ∈ T, ∀ y ∈ T, x ∈ frontier S ↔ y ∈ frontier S)
    {x y : X} (hx : x ∈ T) (hy : y ∈ T) : x ∈ S ↔ y ∈ S := by
  by_cases hxb : x ∈ frontier S
  · exact iff_of_true (hS.frontier_subset hxb) (hS.frontier_subset ((hb x hx y hy).mp hxb))
  have havoid : ∀ z ∈ T, z ∉ frontier S := by
    intro z hz hzb
    exact hxb ((hb x hx z hz).mpr hzb)
  have hcover : T ⊆ interior S ∪ Sᶜ := by
    intro z hz
    by_cases hzs : z ∈ S
    · left
      by_contra hzi
      exact havoid z hz (by rw [hS.frontier_eq]; exact ⟨hzs, hzi⟩)
    · exact Or.inr hzs
  have hdis : Disjoint (interior S) Sᶜ :=
    Set.disjoint_left.mpr fun _ hi hc => hc (interior_subset hi)
  rcases hT.subset_or_subset isOpen_interior hS.isOpen_compl hdis hcover with h | h
  · exact iff_of_true (interior_subset (h hx)) (interior_subset (h hy))
  · exact iff_of_false (h hx) (h hy)

/-- Step 2 of the V4 proof of `host_step_step1_seed_step8_transport_step4_coface` (V4 1.0(b)):
"the local structure is constant by (a) applied to the cell complex". Translation
invariance of the relative boundary of a closed set extends to the set itself,
provided the translations are parallel to its affine span. -/
private lemma host_step_step1_seed_step8_transport_step4_coface_step2_fill
    {S : Set (E d)} (hS : IsClosed S) (V : Submodule ℝ (E d))
    (hV : V ≤ (affineSpan ℝ S).direction) (p : E d) (r : ℝ)
    (hb : ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V →
      (x ∈ relfrontier S ↔ y ∈ relfrontier S)) :
    ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V → (x ∈ S ↔ y ∈ S) := by
  have hforward : ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V → x ∈ S → y ∈ S := by
    intro x hx y hy hyx hxs
    have hxaff : x ∈ affineSpan ℝ S := subset_affineSpan ℝ S hxs
    let γ : ℝ → affineSpan ℝ S := fun t =>
      ⟨t • (y - x) + x,
        AffineSubspace.vadd_mem_of_mem_direction
          ((affineSpan ℝ S).direction.smul_mem t (hV hyx)) hxaff⟩
    have hγcont : Continuous γ := by
      apply Continuous.subtype_mk
      fun_prop
    have hγball : ∀ t ∈ Icc (0 : ℝ) 1, (γ t : E d) ∈ ball p r := by
      intro t ht
      have hseg : (γ t : E d) ∈ segment ℝ x y := by
        rw [segment_eq_image_lineMap]
        exact ⟨t, ht, rfl⟩
      exact (convex_ball p r).segment_subset hx hy hseg
    have hfront (z : affineSpan ℝ S) :
        z ∈ frontier ((↑) ⁻¹' S : Set (affineSpan ℝ S)) ↔ (z : E d) ∈ relfrontier S := by
      change _ ↔ (z : E d) ∈ Subtype.val '' frontier _
      exact (Subtype.val_injective.mem_set_image).symm
    have hinv : ∀ a ∈ γ '' Icc (0 : ℝ) 1, ∀ b ∈ γ '' Icc (0 : ℝ) 1,
        a ∈ frontier ((↑) ⁻¹' S : Set (affineSpan ℝ S)) ↔
        b ∈ frontier ((↑) ⁻¹' S : Set (affineSpan ℝ S)) := by
      rintro a ⟨s, hs, rfl⟩ b ⟨t, ht, rfl⟩
      rw [hfront, hfront]
      apply hb _ (hγball s hs) _ (hγball t ht)
      change (t • (y - x) + x) - (s • (y - x) + x) ∈ V
      simpa only [add_sub_add_right_eq_sub] using
        V.sub_mem (V.smul_mem t hyx) (V.smul_mem s hyx)
    have heq := host_step_step1_seed_step8_transport_step4_coface_step1_connected_membership
      (hS.preimage continuous_subtype_val)
      (isPreconnected_Icc.image γ hγcont.continuousOn) hinv
      (mem_image_of_mem γ (left_mem_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)))
      (mem_image_of_mem γ (right_mem_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)))
    simpa [γ] using heq.mp (by simpa [γ] using hxs)
  intro x hx y hy hyx
  exact ⟨hforward x hx y hy hyx,
    hforward y hy x hx (by simpa only [neg_sub] using V.neg_mem hyx)⟩

/-- Step 3 of the V4 proof of `host_step_step1_seed_step8_transport_step4_coface` (V4 1.0(a)):
"Cells are closed and finitely many, so some ball U ...". Finitely many local
translation invariances hold on a common ball, including for an empty family. -/
private lemma host_step_step1_seed_step8_transport_step4_coface_step3_common_ball
    {ι : Type*} (s : Finset ι) (C : ι → Set (E d))
    (V : Submodule ℝ (E d)) (p : E d)
    (h : ∀ i ∈ s, ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V → (x ∈ C i ↔ y ∈ C i)) :
    ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s,
      ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V → (x ∈ C i ↔ y ∈ C i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨ra, hra, hca⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨rs, hrs, hcs⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨min ra rs, lt_min hra hrs, ?_⟩
    intro i hi x hx y hy hv
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hca x (ball_subset_ball (min_le_left _ _) hx)
        y (ball_subset_ball (min_le_left _ _) hy) hv
    · exact hcs i hi x (ball_subset_ball (min_le_right _ _) hx)
        y (ball_subset_ball (min_le_right _ _) hy) hv

/-- Step 4 of the V4 proof of `host_step_step1_seed_step8_transport_step4_coface` (V4 1.0(b)):
"the local structure is constant by (a) applied to the cell complex". Induction
through the finite boundary complex proves both incidence and local translation
invariance in the directions of the cell containing the base point. -/
private lemma host_step_step1_seed_step8_transport_step4_coface_step4_cell_invariance
    {A : PolyManifoldDomain d} (K : CellComplex A) (e : Cell d) (he : e ∈ K.cells)
    (p : E d) (hp : p ∈ relint e.carrier) (f : Cell d) (hf : f ∈ K.cells) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
      y - x ∈ cellDirection e.carrier → (x ∈ f.carrier ↔ y ∈ f.carrier) := by
  classical
  let N (f : Cell d) := (K.cells.filter fun g => g.carrier ⊆ f.carrier).card
  have main : ∀ n : ℕ, ∀ f : Cell d, f ∈ K.cells → N f = n →
      (p ∈ f.carrier → e.carrier ⊆ f.carrier) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball p r, ∀ y ∈ ball p r,
        y - x ∈ cellDirection e.carrier → (x ∈ f.carrier ↔ y ∈ f.carrier) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf hN
      by_cases hpf : p ∈ f.carrier
      · obtain ⟨b, hb, hboundary⟩ := K.boundary_union f hf
        have hgb (g : Cell d) (hg : g ∈ b) : g.carrier ⊆ relfrontier f.carrier := by
          intro z hz
          rw [hboundary]
          exact mem_iUnion.mpr ⟨g, mem_iUnion.mpr ⟨hg, hz⟩⟩
        have hgf (g : Cell d) (hg : g ∈ b) : g.carrier ⊆ f.carrier :=
          (hgb g hg).trans (intrinsicFrontier_subset f.flat.compact.isClosed)
        have hsmall : ∀ g ∈ b, N g < N f := by
          intro g hg
          have hnfg : ¬ f.carrier ⊆ g.carrier := by
            intro hfg
            obtain ⟨z, hz⟩ := f.flat.relint_nonempty
            have hzb := hgb g hg (hfg (intrinsicInterior_subset hz))
            change z ∈ intrinsicFrontier ℝ f.carrier at hzb
            rw [← closure_diff_intrinsicInterior] at hzb
            exact hzb.2 hz
          apply Finset.card_lt_card
          apply (Finset.ssubset_iff_of_subset ?_).mpr
          · refine ⟨f, Finset.mem_filter.mpr ⟨hf, Subset.rfl⟩, ?_⟩
            intro hfg
            exact hnfg (Finset.mem_filter.mp hfg).2
          · intro g' hg'
            obtain ⟨hg'K, hg'g⟩ := Finset.mem_filter.mp hg'
            exact Finset.mem_filter.mpr ⟨hg'K, hg'g.trans (hgf g hg)⟩
        have hef : e.carrier ⊆ f.carrier := by
          by_cases hpi : p ∈ relint f.carrier
          · have hef : e = f := by
              by_contra hne
              exact Set.disjoint_left.mp (K.relint_disjoint e he f hf hne) hp hpi
            exact hef ▸ Subset.rfl
          · have hpb : p ∈ relfrontier f.carrier := by
              change p ∈ intrinsicFrontier ℝ f.carrier
              rw [← closure_diff_intrinsicInterior, f.flat.compact.isClosed.closure_eq]
              exact ⟨hpf, hpi⟩
            rw [hboundary] at hpb
            obtain ⟨g, hpg⟩ := mem_iUnion.mp hpb
            obtain ⟨hg, hpg⟩ := mem_iUnion.mp hpg
            exact ((ih (N g) (by simpa only [hN] using hsmall g hg)
              g (hb hg) rfl).1 hpg).trans (hgf g hg)
        have hV : cellDirection e.carrier ≤ (affineSpan ℝ f.carrier).direction :=
          AffineSubspace.direction_le (affineSpan_mono ℝ hef)
        obtain ⟨r, hr, hc⟩ :=
          host_step_step1_seed_step8_transport_step4_coface_step3_common_ball b
            Cell.carrier (cellDirection e.carrier) p (fun g hg =>
              (ih (N g) (by simpa only [hN] using hsmall g hg) g (hb hg) rfl).2)
        refine ⟨fun _ => hef, r, hr,
          host_step_step1_seed_step8_transport_step4_coface_step2_fill
            f.flat.compact.isClosed (cellDirection e.carrier) hV p r ?_⟩
        intro x hx y hy hv
        rw [hboundary]
        simp only [mem_iUnion, exists_prop]
        constructor
        · rintro ⟨g, hg, hxg⟩
          exact ⟨g, hg, (hc g hg x hx y hy hv).mp hxg⟩
        · rintro ⟨g, hg, hyg⟩
          exact ⟨g, hg, (hc g hg x hx y hy hv).mpr hyg⟩
      · obtain ⟨r, hr, hball⟩ :=
          Metric.isOpen_iff.mp f.flat.compact.isClosed.isOpen_compl p hpf
        exact ⟨fun h => (hpf h).elim, r, hr,
          fun x hx y hy _ => iff_of_false (hball hx) (hball hy)⟩
  exact (main (N f) f hf rfl).2

open scoped Topology in
/-- Step 5 of the V4 proof of `host_step_step1_seed_step8_transport_step4_coface` (V4 1.0(b)):
"the local structure is constant". Equal translated germs give equal radial
tangent cones; only sufficiently short positive portions of each ray matter. -/
private lemma host_step_step1_seed_step8_transport_step4_coface_step5_tangent_germ
    (S : Set (E d)) (V : Submodule ℝ (E d)) (p q : E d)
    (r : ℝ) (hr : 0 < r) (hq : q ∈ ball p r) (hv : q - p ∈ V)
    (hloc : ∀ x ∈ ball p r, ∀ y ∈ ball p r, y - x ∈ V → (x ∈ S ↔ y ∈ S)) :
    tangentCone S p = tangentCone S q := by
  ext v
  have hnear (a : E d) (ha : a ∈ ball p r) :
      ∀ᶠ t : ℝ in 𝓝 0, a + t • v ∈ ball p r := by
    have hc : Continuous (fun t : ℝ => a + t • v) := by fun_prop
    have ht : Filter.Tendsto (fun t : ℝ => a + t • v) (𝓝 0) (𝓝 a) := by
      simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
    exact ht.eventually (isOpen_ball.mem_nhds ha)
  obtain ⟨δ, hδ, hδnear⟩ := Metric.eventually_nhds_iff.mp
    ((hnear p (mem_ball_self hr)).and (hnear q hq))
  have heq (t : ℝ) (ht : 0 < t) (htδ : t < δ) :
      p + t • v ∈ S ↔ q + t • v ∈ S := by
    have hdist : dist t 0 < δ := by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using htδ
    have hpair := hδnear hdist
    apply hloc _ hpair.1 _ hpair.2
    simpa only [add_sub_add_right_eq_sub] using hv
  constructor
  · rintro ⟨ε, hε, hεray⟩
    refine ⟨min ε δ, lt_min hε hδ, fun t ht htεδ => ?_⟩
    exact (heq t ht (lt_of_lt_of_le htεδ (min_le_right _ _))).mp
      (hεray t ht (lt_of_lt_of_le htεδ (min_le_left _ _)))
  · rintro ⟨ε, hε, hεray⟩
    refine ⟨min ε δ, lt_min hε hδ, fun t ht htεδ => ?_⟩
    exact (heq t ht (lt_of_lt_of_le htεδ (min_le_right _ _))).mpr
      (hεray t ht (lt_of_lt_of_le htεδ (min_le_left _ _)))

/-- Step 4 of the V4 proof of `host_step_step1_seed_step8_transport` (V4 3.6, F1):
"near a point of the relative interior of a codimension-one face,
a polyhedral manifold cell is a half-space on the recorded side".
The tangent of a coface is constant along the relative interior of its
listed codimension-one face; the anchor used by `flagSide` is immaterial. -/
private theorem host_step_step1_seed_step8_transport_step4_coface
    {A : S.ι} (F : FacetFlag S A) (k : FlagStep d) (x : E d)
    (hx : x ∈ relint (F.cell ⟨k.val, k.property.1, by omega⟩).val.carrier) :
    tangentCone (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier x =
      flagSide F k := by
  let e := (F.cell ⟨k.val, k.property.1, by omega⟩).val
  let f := (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val
  have he : e ∈ (S.cx A).cells := (F.cell _).property
  have hf : f ∈ (S.cx A).cells := (F.cell _).property
  have hloc : IsLocallyConstant (fun p : relint e.carrier => tangentCone f.carrier p) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro p
    obtain ⟨r, hr, hball⟩ :=
      host_step_step1_seed_step8_transport_step4_coface_step4_cell_invariance
        (S.cx A) e he p p.property f hf
    have hnear : ∀ᶠ q : relint e.carrier in nhds p, (q : E d) ∈ ball (p : E d) r :=
      continuous_subtype_val.continuousAt.eventually
        (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hnear] with q hq
    apply (host_step_step1_seed_step8_transport_step4_coface_step5_tangent_germ
      f.carrier (cellDirection e.carrier) p q r hr hq ?_ hball).symm
    exact AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ e.carrier (intrinsicInterior_subset q.property))
      (subset_affineSpan ℝ e.carrier (intrinsicInterior_subset p.property))
  have hconn : IsPreconnected (univ : Set (relint e.carrier)) :=
    (Subtype.preconnectedSpace e.flat.relint_connected.isPreconnected).isPreconnected_univ
  exact hloc.apply_eq_of_isPreconnected hconn
    (x := ⟨x, hx⟩) (y := ⟨cellAnchor e, cellAnchor_mem e⟩) (mem_univ _) (mem_univ _)

/-- Step 4 of the V4 proof of `host_step_step1_seed_step8_transport` (V4 3.6, F1):
"with the recorded sides". The common positioned cofaces give identical
local side cones, even though their relative-interior anchors may differ. -/
private theorem host_step_step1_seed_step8_transport_step4_sides
    (ι : P.Incidence) (b : Bool) (k : FlagStep d) :
    (S.child ι.val.ty (ι.val.sideIndex b)).frame.linearIsometryEquiv ''
        flagSide (P.sideFlag ι b) k =
      (S.child ι.val.ty ι.val.left).frame.linearIsometryEquiv '' (P.flag ι).sides k := by
  let τ := (S.child ι.val.ty (ι.val.sideIndex b)).frame.trans
    (S.child ι.val.ty ι.val.left).frame.symm
  have hcells (j : FlagIndex d) : τ '' ((P.sideFlag ι b).cell j).val.carrier =
      ((P.flag ι).flag.cell j).val.carrier := by
    calc
      τ '' ((P.sideFlag ι b).cell j).val.carrier =
          (S.child ι.val.ty ι.val.left).frame.symm ''
            placedSet (S.child ι.val.ty (ι.val.sideIndex b)).frame
              ((P.sideFlag ι b).cell j).val.carrier := by
        rw [placedSet, Set.image_image]
        rfl
      _ = (S.child ι.val.ty ι.val.left).frame.symm ''
          placedSet (S.child ι.val.ty ι.val.left).frame
            ((P.flag ι).flag.cell j).val.carrier := by rw [P.sideFlag_eq]
      _ = _ := by
        simp only [placedSet, Set.image_image, AffineIsometryEquiv.symm_apply_apply,
          Set.image_id']
  let low : FlagIndex d := ⟨k.val, k.property.1, by omega⟩
  let high : FlagIndex d := ⟨k.val + 1, by omega, k.property.2⟩
  have hx : τ (cellAnchor ((P.sideFlag ι b).cell low).val) ∈
      relint ((P.flag ι).flag.cell low).val.carrier := by
    rw [← hcells low]
    change τ (cellAnchor ((P.sideFlag ι b).cell low).val) ∈
      intrinsicInterior ℝ (τ.toAffineIsometry '' ((P.sideFlag ι b).cell low).val.carrier)
    rw [τ.toAffineIsometry.image_intrinsicInterior]
    exact Set.mem_image_of_mem τ (cellAnchor_mem _)
  have hc := host_step_step1_seed_step8_transport_step4_coface (P.flag ι).flag k _ hx
  change tangentCone ((P.flag ι).flag.cell high).val.carrier
    (τ (cellAnchor ((P.sideFlag ι b).cell low).val)) = flagSide (P.flag ι).flag k at hc
  rw [← hcells high] at hc
  change tangentCone (τ.toAffineEquiv '' ((P.sideFlag ι b).cell high).val.carrier)
    (τ.toAffineEquiv (cellAnchor ((P.sideFlag ι b).cell low).val)) = _ at hc
  rw [host_step_step1_seed_step8_transport_step1_tangent_image] at hc
  have h := congrArg (fun K : Set (E d) =>
    (S.child ι.val.ty ι.val.left).frame.linearIsometryEquiv '' K) hc
  rw [(P.flag ι).sides_eq]
  dsimp only at h
  rw [Set.image_image] at h
  change (fun v => (S.child ι.val.ty ι.val.left).frame.linearIsometryEquiv
      ((S.child ι.val.ty ι.val.left).frame.linearIsometryEquiv.symm
        ((S.child ι.val.ty (ι.val.sideIndex b)).frame.linearIsometryEquiv v))) ''
      flagSide (P.sideFlag ι b) k = _ at h
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

/-- Step 5 of the V4 proof of `host_step_step1_seed_step8_transport` (V4 3.6):
"e₀ is a segment from p₀ along the ray of h". Every direction of the
radial tangent cone at a segment's initial endpoint is a nonnegative multiple
of its oriented vector, including the zero direction. -/
private theorem host_step_step1_seed_step8_transport_step5_ray
    (p q v : E d) (hv : v ∈ tangentCone (segment ℝ p q) p) :
    ∃ a : ℝ, 0 ≤ a ∧ v = a • (q - p) := by
  obtain ⟨ε, hε, hv⟩ := hv
  have ht : 0 < ε / 2 := by positivity
  have hm := hv (ε / 2) ht (by linarith)
  rw [segment_eq_image'] at hm
  obtain ⟨a, ha, he⟩ := hm
  have he' : a • (q - p) = (ε / 2) • v := add_left_cancel he
  refine ⟨a / (ε / 2), div_nonneg ha.1 ht.le, ?_⟩
  calc
    v = (ε / 2)⁻¹ • ((ε / 2) • v) := by
      rw [inv_smul_smul₀ ht.ne']
    _ = (a / (ε / 2)) • (q - p) := by
      rw [← he', smul_smul]
      congr 1
      ring

/-- Step 5 of the V4 proof of `host_step_step1_seed_step8_transport` (V4 3.6):
"the recorded orientation ... those of P's actual flag". A nonzero
direction in the initial flag ray has strictly positive oriented inner product. -/
private theorem host_step_step1_seed_step8_transport_step5_positive
    (p q v : E d) (hv : v ∈ tangentCone (segment ℝ p q) p) (hn : v ≠ 0) :
    0 < inner ℝ (q - p) v := by
  obtain ⟨a, ha, rfl⟩ := host_step_step1_seed_step8_transport_step5_ray p q v hv
  have ha' : a ≠ 0 := by intro h; exact hn (by simp [h])
  have hpq : q - p ≠ 0 := by intro h; exact hn (by simp [h])
  rw [inner_smul_right]
  exact mul_pos (lt_of_le_of_ne ha (Ne.symm ha')) (real_inner_self_pos.mpr hpq)

/-- Step 5 of the V4 proof of `host_step_step1_seed_step8_transport` (V4 3.6):
"e₀ is a segment from p₀ along the ray of h". If a segment has the
initial flag ray at a point of itself and is oriented forward along that ray,
the point is its initial endpoint. -/
private theorem host_step_step1_seed_step8_transport_step5_initial
    (p q a b : E d) (hp : p ∈ segment ℝ a b)
    (hray : tangentCone (segment ℝ a b) p ⊆ tangentCone (segment ℝ p q) p)
    (hpos : 0 < inner ℝ (q - p) (b - a)) : a = p := by
  have hback : a - p ∈ tangentCone (segment ℝ a b) p := by
    refine ⟨1, zero_lt_one, fun t ht ht1 => ?_⟩
    have hm := (convex_segment a b) hp (left_mem_segment ℝ a b)
      (sub_nonneg.mpr ht1.le) ht.le (sub_add_cancel 1 t)
    convert hm using 1
    module
  obtain ⟨s, hs, hdir⟩ := host_step_step1_seed_step8_transport_step5_ray p q (a - p)
    (hray hback)
  have hnonneg : 0 ≤ inner ℝ (q - p) (a - p) := by
    rw [hdir, inner_smul_right]
    exact mul_nonneg hs (real_inner_self_nonneg)
  rw [segment_eq_image'] at hp
  obtain ⟨t, ht, he⟩ := hp
  have hsub : a - p = -t • (b - a) := by rw [← he]; module
  rw [hsub, inner_smul_right] at hnonneg
  have ht0 : t = 0 := by nlinarith [ht.1]
  simpa only [ht0, zero_smul, add_zero] using he

/-- Step 6 of the V4 proof of `host_step_step1_seed_step8_transport` (V4 3.6):
"with the recorded orientation". All honest active chains with the same
bottom edge agree in orientation, so the endpoint readout equals the chain vector. -/
private theorem host_step_step1_seed_step8_transport_step6_endpoint_vector
    (s : State P) (hs : s ∈ honestStates S P) (F : Cell d)
    (r : FacetRecord P) (hr : stateRecordAt s F = some r)
    (c : OrientedChain r.facet) (hc : c ∈ r.chains) :
    (r.endpoints (host_step_edge ⟨r, c⟩)).2 -
      (r.endpoints (host_step_edge ⟨r, c⟩)).1 = chainVector c := by
  classical
  obtain ⟨U, q, rfl⟩ := hs
  unfold stateRecordAt at hr
  split at hr
  · rename_i hF
    change U.facetRecordOf P q ⟨F, hF⟩ = some r at hr
    unfold HonestSource.facetRecordOf at hr
    split at hr
    · contradiction
    · rename_i hf
      have hr' := Option.some.inj hr
      subst r
      let r := U.recordOf P q ⟨F, hF⟩ hf
      let e := host_step_edge (⟨r, c⟩ : host_step_Chain P)
      have horient (c' : OrientedChain r.facet) (hc' : c' ∈ r.chains) :
          c'.forward = true ↔ 0 < inner ℝ
            ((U.providerPlacement P q ⟨F, hF⟩ hf).linear
              (P.flag (U.recordIncidence P q ⟨F, hF⟩ hf)).direction)
            ((q.2.val.prototypeFrame q.1).linear
              (edgeVector ⟨r.ty, host_step_edge ⟨r, c'⟩⟩)) :=
        (record_chains_spec U P q ⟨F, hF⟩ hf c').mp hc' |>.2
      have hsame (c' : OrientedChain r.facet) (hc' : c' ∈ r.chains)
          (he : (c'.chain.val.cell edgeIndex).val = e.val) :
          c'.forward = c.forward := by
        have he' : host_step_edge (⟨r, c'⟩ : host_step_Chain P) = e := Subtype.ext he
        have ho := horient c hc
        have ho' := horient c' hc'
        rw [he'] at ho'
        have heq : (c'.forward = true) ↔ c.forward = true := ho'.trans ho.symm
        cases h1 : c'.forward <;> cases h2 : c.forward <;> simp_all
      have hforward : r.edgeForward e = c.forward := by
        unfold FacetRecord.edgeForward
        cases hcf : c.forward with
        | false =>
            apply Bool.eq_false_iff.mpr
            intro hh
            obtain ⟨c', hc', he'⟩ := List.any_eq_true.mp hh
            have hp : (c'.chain.val.cell edgeIndex).val = e.val ∧ c'.forward = true := by
              simpa using he'
            have heq := hsame c' (Finset.mem_toList.mp hc') hp.1
            simp_all
        | true =>
            apply List.any_eq_true.mpr
            refine ⟨c, Finset.mem_toList.mpr hc, ?_⟩
            simp [e, host_step_edge, hcf]
      change (r.endpoints e).2 - (r.endpoints e).1 = chainVector c
      unfold FacetRecord.endpoints
      rw [hforward]
      unfold chainVector
      cases c.forward <;> simp [e, edgeVector, neg_sub]
  · contradiction

/-- Step 6 of the V4 proof of `host_step_step1_seed_step8_transport` (V4 3.6):
"the recorded orientation". The record's two endpoints always describe
the full nondegenerate bottom edge, in one of its two possible orders. -/
private theorem host_step_step1_seed_step8_transport_step6_segment
    (r : FacetRecord P) (c : OrientedChain r.facet) :
    (r.endpoints (host_step_edge ⟨r, c⟩)).1 ≠
        (r.endpoints (host_step_edge ⟨r, c⟩)).2 ∧
      (host_step_edge ⟨r, c⟩).val.carrier = segment ℝ
        (r.endpoints (host_step_edge ⟨r, c⟩)).1
        (r.endpoints (host_step_edge ⟨r, c⟩)).2 := by
  have h := Classical.choose_spec
    (edge_endpoints_exist (⟨r.ty, host_step_edge ⟨r, c⟩⟩ : EdgeName S))
  unfold FacetRecord.endpoints
  split
  · exact h
  · exact ⟨h.1.symm, h.2.trans (segment_symm ℝ _ _)⟩

/-- Step 7 of the V4 proof of `host_step_step1_seed_step8_transport` (V4 3.6):
"u₀ lies on the j-side of aff g (its position in the template is inside
the j-side child's cone)". Matching full headers identify the selected
child's cone and primitive facet cone. A geometric primitive port therefore
has that child's inward half-space after the ambient isometry. This concerns
only the honest star's geometry, independently of its leaf records or chains. -/
private theorem host_step_step1_seed_step8_transport_step7_inward
    (Q : FramedNode S) (n : ℕ) (ι : P.Incidence) (b : Bool) (hι : ι.val.ty = Q.ty)
    (φ : Iso d) (l : LeafType P) (j : EndSlot l)
    (hp : Compiler.endVertex φ j = P.incidencePlacement Q (n + 1) ι (P.flag ι).initial)
    (hh : j.header = host_step_step1_seed_step1_header Q n φ
      (P.incidencePlacement Q (n + 1) ι (P.flag ι).initial))
    (T : EndTemplate j) (a : PrimitivePort P) (ha : a ∈ T.geometry.primitivePorts)
    (hai : a.incidence = ι) (hab : a.sideIndex = b) :
    φ.linearIsometryEquiv '' (a.tile.frame.linearIsometryEquiv ''
        tangentCone (S.proto a.tile.ty).carrier (cellAnchor a.facet.val)) =
      (((⟨ι.val.ty, Q.frame⟩ : FramedNode S).child n
          (ι.val.sideIndex b)).prototypeFrame n).linear ''
        tangentCone (S.proto (ι.val.sideType b)).carrier
          (cellAnchor (ι.val.sideFacet b).val) := by
  -- Unpack T.honest_geometry and its IsSourcePrimitivePort witness. The
  -- native facet is a piece of the b-side serving child's provider facet.
  -- In the common header, both the selected child cone and the primitive
  -- facet cone agree with those of Q. Their local half-spaces at relative
  -- interior facet directions determine the same inward side by V4 1.0(a).
  sorry

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
  classical
  let H := (⟨ι.val.ty, Q.frame⟩ : FramedNode S).child n (ι.val.sideIndex b)
  let pos := P.incidencePlacement Q (n + 1) ι
  let p := pos (P.flag ι).initial
  let q := pos (P.flag ι).terminal
  let x := vertexPoint T.geometry.vertex
  let ψ := a.tile.frame.trans φ
  let N : FramedNode S := ⟨u.prototype, ψ⟩
  have hframe : host_step_flagFrame H n ι b = pos :=
    host_step_step1_seed_step1_flag_frame Q n ι b
  have hNframe : N.prototypeFrame 0 = ψ.toAffineEquiv := by
    ext y
    simp [N, FramedNode.prototypeFrame]
  have hx : φ x = p := by
    have hv := congrArg Cell.carrier T.vertex_eq
    rw [vertexPoint_spec, vertexPoint_spec] at hv
    have hvertex := Set.singleton_injective hv
    change φ (vertexPoint T.geometry.vertex) = p
    rw [hvertex]
    exact hp
  have hdata : G = {
      cones := fun k => φ.linearIsometryEquiv.symm ''
        tangentCone (pos '' ((P.flag ι).flag.cell k).val.carrier) p
      initial := true
      sides := fun k => φ.linearIsometryEquiv.symm '' (pos.linear '' (P.flag ι).sides k) } := by
    apply Option.some.inj
    calc
      some G = T.geometry.header.flagTangent ι := hG.symm
      _ = _ := by
        rw [T.header_eq, hh]
        simp [host_step_step1_seed_step1_header, hι, p, pos]
  have hcones (k : FlagIndex d) : φ.linearIsometryEquiv '' G.cones k =
      tangentCone (pos '' ((P.flag ι).flag.cell k).val.carrier) p := by
    rw [hdata]
    simp only [Set.image_image, LinearIsometryEquiv.apply_symm_apply, Set.image_id']
  have hsides (k : FlagStep d) : φ.linearIsometryEquiv '' G.sides k =
      pos.linear '' (P.flag ι).sides k := by
    rw [hdata]
    simp only [Set.image_image, LinearIsometryEquiv.apply_symm_apply]
  have hcomp (K : Set (E d)) : φ '' placedSet a.tile.frame K = ψ '' K := by
    rw [placedSet, Set.image_image]
    rfl
  have hspans (k : FlagIndex d) : affineSpan ℝ (N.cell 0 (c.chain.val.cell k).val) =
      affineSpan ℝ (H.cell n ((P.sideFlag ι b).cell k).val) := by
    rw [host_step_step1_seed_step8_transport_step3_cells, hframe]
    change affineSpan ℝ (N.prototypeFrame 0 '' (c.chain.val.cell k).val.carrier) = _
    rw [hNframe]
    have hpF : p ∈ pos '' ((P.flag ι).flag.cell k).val.carrier := by
      refine ⟨(P.flag ι).initial, ?_, rfl⟩
      apply (P.flag ι).flag.nested edgeIndex k (by exact k.property.1)
      rw [(P.flag ι).edge_eq]
      exact left_mem_segment ℝ _ _
    apply host_step_step1_seed_step8_transport_step2_span _ _ ψ.toAffineEquiv pos
      ((c.chain.val.dimension k).trans ((P.flag ι).flag.dimension k).symm) p hpF
    have ht := congrArg (fun A : AffineSubspace ℝ (E d) => A.map φ.toAffineMap)
      (hfit k).2.1
    dsimp only at ht
    rw [AffineSubspace.map_span, AffineSubspace.map_span] at ht
    change affineSpan ℝ (φ '' placedSet a.tile.frame (c.chain.val.cell k).val.carrier) =
      affineSpan ℝ (φ '' ((fun v => x + v) '' G.cones k)) at ht
    rw [hcomp] at ht
    have htranslate : φ '' ((fun v => x + v) '' G.cones k) =
        (fun v => p + v) '' tangentCone (pos '' ((P.flag ι).flag.cell k).val.carrier) p := by
      rw [← hcones k, Set.image_image, Set.image_image]
      congr 1
      funext v
      change φ (x + v) = p + φ.linearIsometryEquiv v
      rw [← hx]
      simpa only [vadd_eq_add, add_comm] using φ.map_vadd x v
    rwa [htranslate] at ht
  have hside (k : FlagStep d) : (N.prototypeFrame 0).linear '' flagSide c.chain.val k =
      (H.prototypeFrame n).linear '' flagSide (P.sideFlag ι b) k := by
    have href : (H.prototypeFrame n).linear '' flagSide (P.sideFlag ι b) k =
        pos.linear '' (P.flag ι).sides k := by
      have hhside := congrArg (fun K : Set (E d) =>
        (H.prototypeFrame n).linear ''
          ((S.child ι.val.ty (ι.val.sideIndex b)).frame.linearIsometryEquiv.symm '' K))
        (host_step_step1_seed_step8_transport_step4_sides ι b k)
      rw [← hframe]
      simpa only [Set.image_image, LinearIsometryEquiv.symm_apply_apply] using hhside
    rw [href, hNframe]
    calc
      ψ.toAffineEquiv.linear '' flagSide c.chain.val k =
          φ.linearIsometryEquiv '' (a.tile.frame.linearIsometryEquiv '' flagSide c.chain.val k) := by
        rw [Set.image_image]
        rfl
      _ = φ.linearIsometryEquiv '' G.sides k := by rw [ho.2 k]
      _ = _ := hsides k
  let e := host_step_edge (⟨r, c⟩ : host_step_Chain P)
  let a₀ := (r.endpoints e).1
  let a₁ := (r.endpoints e).2
  have hsegment := host_step_step1_seed_step8_transport_step6_segment r c
  have hsegment' : ψ '' e.val.carrier = segment ℝ (ψ a₀) (ψ a₁) := by
    rw [hsegment.2]
    exact image_segment ℝ ψ.toAffineMap _ _
  have hstate : u.prePattern.state ∈ honestStates S P :=
    (prePattern_components_honest P u.prePattern
      ((certificate_components_honest P u.1.val u.1.property).1 u.2)).1
  have hvector := host_step_step1_seed_step8_transport_step6_endpoint_vector
    u.prePattern.state hstate a.facet.val r hr c hc
  have hv : ψ.linearIsometryEquiv (chainVector c) = ψ a₁ - ψ a₀ := by
    rw [← hvector]
    exact ψ.map_vsub a₁ a₀
  have hn : ψ.linearIsometryEquiv (chainVector c) ≠ 0 := by
    rw [hv]
    exact sub_ne_zero.mpr (ψ.injective.ne hsegment.1.symm)
  have hflagseg : pos '' ((P.flag ι).flag.cell edgeIndex).val.carrier =
      segment ℝ p q := by
    rw [(P.flag ι).edge_eq]
    exact image_segment ℝ pos.toAffineMap _ _
  have horient : ψ.linearIsometryEquiv (chainVector c) ∈
      tangentCone (segment ℝ p q) p := by
    rw [← hflagseg, ← hcones edgeIndex]
    refine ⟨a.tile.frame.linearIsometryEquiv (chainVector c), ?_, rfl⟩
    simpa only [hi, Bool.true_eq, ite_true] using ho.1
  have hpos := host_step_step1_seed_step8_transport_step5_positive p q _ horient hn
  have hcone : tangentCone (ψ '' e.val.carrier) p =
      tangentCone (segment ℝ p q) p := by
    calc
      tangentCone (ψ '' e.val.carrier) p =
          φ.linearIsometryEquiv '' tangentCone (placedSet a.tile.frame e.val.carrier) x := by
        rw [← hcomp, ← hx]
        exact host_step_step1_seed_step8_transport_step1_tangent_image φ.toAffineEquiv _ x
      _ = φ.linearIsometryEquiv '' G.cones edgeIndex := by rw [hray]
      _ = _ := by rw [hcones, hflagseg]
  have hstart : ψ a₀ = p := by
    apply host_step_step1_seed_step8_transport_step5_initial p q (ψ a₀) (ψ a₁)
    · rw [← hsegment', ← hcomp, ← hx]
      exact Set.mem_image_of_mem φ (hfit edgeIndex).1
    · rw [← hsegment']
      exact hcone.subset
    · rwa [← hv]
  have hinward := host_step_step1_seed_step8_transport_step7_inward
    Q n ι b hι φ l j hp hh T a ha hai hab
  obtain ⟨_, hfacet⟩ := host_step_step1_seed_step6_readout u a.facet.val r hr
  have htype := T.configuration.types_match (a.tile, u) hu
  change host_step_aligned H n ι b N 0 ⟨r, c⟩ ∧ ψ a₀ = p
  refine ⟨⟨hspans, hside, ?_, ?_⟩, hstart⟩
  · rw [hframe, hNframe]
    have href : pos.linear (P.flag ι).direction = q - p :=
      pos.toAffineMap.linearMap_vsub (P.flag ι).terminal (P.flag ι).initial
    rw [href]
    exact hpos
  · change (N.prototypeFrame 0).linear ''
        tangentCone (S.proto u.prototype).carrier (cellAnchor r.facet.val) = _
    rw [hNframe, ← htype, hfacet]
    rw [Set.image_image] at hinward
    exact hinward

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

/-- Step 1 of the V4 proof of `host_step_step2_strand` (V4 3.6):
"the initial and terminal vertices of h". The two side names of the flag
give the same oriented segment after placement. -/
private theorem host_step_step2_strand_step1_flag_segment
    (H : FramedNode S) (n : ℕ) (ι : P.Incidence) (b : Bool) :
    host_step_flagEdge H n ι b = segment ℝ
      (host_step_flagFrame H n ι b (P.flag ι).initial)
      (host_step_flagFrame H n ι b (P.flag ι).terminal) := by
  have he : host_step_flagEdge H n ι b =
      host_step_flagFrame H n ι b '' ((P.flag ι).flag.cell edgeIndex).val.carrier := by
    change H.prototypeFrame n '' ((P.sideFlag ι b).cell edgeIndex).val.carrier = _
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hm : (S.child ι.val.ty (ι.val.sideIndex b)).frame y ∈
          placedSet (S.child ι.val.ty ι.val.left).frame
            ((P.flag ι).flag.cell edgeIndex).val.carrier := by
        rw [← P.sideFlag_eq ι b edgeIndex]
        exact ⟨y, hy, rfl⟩
      obtain ⟨z, hz, heq⟩ := hm
      refine ⟨z, hz, ?_⟩
      change H.prototypeFrame n
        ((S.child ι.val.ty (ι.val.sideIndex b)).frame.symm
          ((S.child ι.val.ty ι.val.left).frame z)) = H.prototypeFrame n y
      rw [heq, AffineIsometryEquiv.symm_apply_apply]
    · rintro ⟨z, hz, rfl⟩
      have hm : (S.child ι.val.ty ι.val.left).frame z ∈
          placedSet (S.child ι.val.ty (ι.val.sideIndex b)).frame
            ((P.sideFlag ι b).cell edgeIndex).val.carrier := by
        rw [P.sideFlag_eq ι b edgeIndex]
        exact ⟨z, hz, rfl⟩
      obtain ⟨y, hy, heq⟩ := hm
      refine ⟨y, hy, ?_⟩
      change H.prototypeFrame n y = H.prototypeFrame n
        ((S.child ι.val.ty (ι.val.sideIndex b)).frame.symm
          ((S.child ι.val.ty ι.val.left).frame z))
      rw [← heq, AffineIsometryEquiv.symm_apply_apply]
  rw [he, (P.flag ι).edge_eq]
  exact image_segment ℝ (host_step_flagFrame H n ι b).toAffineMap _ _

/-- Step 1 of the V4 proof of `host_step_step2_strand` (V4 3.6):
"in the orientation of h". On a nondegenerate real interval the relative
interior is exactly the open interval. -/
private theorem host_step_step2_strand_step1_interval_relint (a b : ℝ) (hab : a < b) :
    intrinsicInterior ℝ (Icc a b) = Ioo a b := by
  have hspan : affineSpan ℝ (Icc a b) = ⊤ :=
    (convex_Icc a b).interior_nonempty_iff_affineSpan_eq_top.mp
      (by rw [interior_Icc]; exact nonempty_Ioo.mpr hab)
  rw [intrinsicInterior, hspan]
  change (Homeomorph.Set.univ ℝ) ''
    interior ((Homeomorph.Set.univ ℝ) ⁻¹' Icc a b) = Ioo a b
  rw [(Homeomorph.Set.univ ℝ).image_interior]
  simp

/-- Step 1 of the V4 proof of `host_step_step2_strand` (V4 3.6):
"in the orientation of h". Use an isometric coordinate increasing from
the initial endpoint to the terminal endpoint. -/
private theorem host_step_step2_strand_step1_chart
    (H : FramedNode S) (n : ℕ) (ι : P.Incidence) (b : Bool) :
    ∃ (φ : ℝ →ᵃⁱ[ℝ] E d) (L : ℝ), 0 < L ∧
      φ 0 = host_step_flagFrame H n ι b (P.flag ι).initial ∧
      φ L = host_step_flagFrame H n ι b (P.flag ι).terminal ∧
      host_step_flagEdge H n ι b = φ '' Icc 0 L ∧
      relint (host_step_flagEdge H n ι b) = φ '' Ioo 0 L := by
  let p := host_step_flagFrame H n ι b (P.flag ι).initial
  let q := host_step_flagFrame H n ι b (P.flag ι).terminal
  have hpq : p ≠ q := (host_step_flagFrame H n ι b).injective.ne (P.flag ι).distinct
  let L := ‖q - p‖
  have hL : 0 < L := norm_pos_iff.mpr (sub_ne_zero.mpr hpq.symm)
  let v := L⁻¹ • (q - p)
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    exact inv_mul_cancel₀ hL.ne'
  let φ : ℝ →ᵃⁱ[ℝ] E d := {
    toAffineMap := {
      toFun := fun t => t • v + p
      linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight v
      map_vadd' := by
        intro t s
        change (s + t) • v + p = s • v + (t • v + p)
        rw [add_smul, add_assoc] }
    norm_map := by
      intro t
      change ‖t • v‖ = ‖t‖
      rw [norm_smul, hv, mul_one] }
  have hφ0 : φ 0 = p := by change (0 : ℝ) • v + p = p; simp
  have hφL : φ L = q := by
    change L • (L⁻¹ • (q - p)) + p = q
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul, sub_add_cancel]
  have hseg : host_step_flagEdge H n ι b = φ '' Icc 0 L := by
    rw [host_step_step2_strand_step1_flag_segment]
    simpa only [AffineIsometry.coe_toAffineMap, hφ0, hφL, segment_eq_Icc hL.le] using
      (image_segment ℝ φ.toAffineMap 0 L).symm
  refine ⟨φ, L, hL, hφ0, hφL, hseg, ?_⟩
  rw [hseg, relint, φ.image_intrinsicInterior,
    host_step_step2_strand_step1_interval_relint 0 L hL]

/-- Step 1 of the V4 proof of `host_step_step2_strand` (V4 3.6(2a)):
"edges of length at least the minimal native edge length". The bound
uses only the finite native edge catalogue, and also covers an empty catalogue. -/
private theorem host_step_step2_strand_step1_native_length :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : host_step_Port C,
      ε ≤ dist (host_step_portEnds u).1 (host_step_portEnds u).2 := by
  classical
  letI := edgeNames_finite S
  have hlength (u : host_step_Port C) :
      dist (host_step_portEnds u).1 (host_step_portEnds u).2 =
        ‖edgeVector (⟨u.2.1.ty, host_step_edge u.2⟩ : EdgeName S)‖ := by
    change dist (compilerFrame C u.1 (u.2.1.endpoints (host_step_edge u.2)).1)
      (compilerFrame C u.1 (u.2.1.endpoints (host_step_edge u.2)).2) = _
    rw [(compilerFrame C u.1).dist_map]
    unfold FacetRecord.endpoints
    split <;> simp only [edgeVector, dist_eq_norm]
    exact norm_sub_rev _ _
  by_cases hn : Nonempty (EdgeName S)
  · obtain ⟨e, _, he⟩ := Set.exists_min_image (Set.univ : Set (EdgeName S))
      (fun e => ‖edgeVector e‖) Set.finite_univ ⟨Classical.choice hn, Set.mem_univ _⟩
    refine ⟨‖edgeVector e‖, norm_pos_iff.mpr (edgeVector_spec e).1, ?_⟩
    intro u
    rw [hlength]
    exact he _ (Set.mem_univ _)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro u
    exact (hn ⟨⟨u.2.1.ty, host_step_edge u.2⟩⟩).elim

/-- Step 1 of the V4 proof of `host_step_step2_strand` (V4 3.6):
"with the recorded orientation". All honest active chains with the
same bottom edge give that edge the same orientation, so the endpoint
readout and the chain vector agree. -/
private theorem host_step_step2_strand_step1_endpoint_vector
    (s : State P) (hs : s ∈ honestStates S P) (F : Cell d)
    (r : FacetRecord P) (hr : stateRecordAt s F = some r)
    (c : OrientedChain r.facet) (hc : c ∈ r.chains) :
    (r.endpoints (host_step_edge ⟨r, c⟩)).2 -
      (r.endpoints (host_step_edge ⟨r, c⟩)).1 = chainVector c := by
  classical
  obtain ⟨U, q, rfl⟩ := hs
  unfold stateRecordAt at hr
  split at hr
  · rename_i hF
    change U.facetRecordOf P q ⟨F, hF⟩ = some r at hr
    unfold HonestSource.facetRecordOf at hr
    split at hr
    · contradiction
    · rename_i hf
      have hr' := Option.some.inj hr
      subst r
      let r := U.recordOf P q ⟨F, hF⟩ hf
      let e := host_step_edge (⟨r, c⟩ : host_step_Chain P)
      have horient (c' : OrientedChain r.facet) (hc' : c' ∈ r.chains) :
          c'.forward = true ↔ 0 < inner ℝ
            ((U.providerPlacement P q ⟨F, hF⟩ hf).linear
              (P.flag (U.recordIncidence P q ⟨F, hF⟩ hf)).direction)
            ((q.2.val.prototypeFrame q.1).linear
              (edgeVector ⟨r.ty, host_step_edge ⟨r, c'⟩⟩)) :=
        (record_chains_spec U P q ⟨F, hF⟩ hf c').mp hc' |>.2
      have hsame (c' : OrientedChain r.facet) (hc' : c' ∈ r.chains)
          (he : (c'.chain.val.cell edgeIndex).val = e.val) :
          c'.forward = c.forward := by
        have he' : host_step_edge (⟨r, c'⟩ : host_step_Chain P) = e := Subtype.ext he
        have ho := horient c hc
        have ho' := horient c' hc'
        rw [he'] at ho'
        have heq : (c'.forward = true) ↔ c.forward = true := ho'.trans ho.symm
        cases h1 : c'.forward <;> cases h2 : c.forward <;> simp_all
      have hforward : r.edgeForward e = c.forward := by
        unfold FacetRecord.edgeForward
        cases hcf : c.forward with
        | false =>
            apply Bool.eq_false_iff.mpr
            intro hh
            obtain ⟨c', hc', he'⟩ := List.any_eq_true.mp hh
            have hp : (c'.chain.val.cell edgeIndex).val = e.val ∧ c'.forward = true := by
              simpa using he'
            have heq := hsame c' (Finset.mem_toList.mp hc') hp.1
            simp_all
        | true =>
            apply List.any_eq_true.mpr
            refine ⟨c, Finset.mem_toList.mpr hc, ?_⟩
            simp [e, host_step_edge, hcf]
      change (r.endpoints e).2 - (r.endpoints e).1 = chainVector c
      unfold FacetRecord.endpoints
      rw [hforward]
      unfold chainVector
      cases c.forward <;> simp [e, edgeVector, neg_sub]
  · contradiction

/-- Step 1 of the V4 proof of `host_step_step2_strand` (V4 3.6):
"chain-active edges". The native edge is precisely the closed segment
between its two recorded physical endpoints. -/
private theorem host_step_step2_strand_step1_port_segment (u : host_step_Port C) :
    host_step_portEdge u = segment ℝ (host_step_portEnds u).1 (host_step_portEnds u).2 := by
  have he := (Classical.choose_spec
    (edge_endpoints_exist (⟨u.2.1.ty, host_step_edge u.2⟩ : EdgeName S))).2
  have hframe : (tileNode u.1).prototypeFrame 0 = (compilerFrame C u.1).toAffineEquiv := by
    ext x
    simp [FramedNode.prototypeFrame, tileNode]
  unfold host_step_portEdge FramedNode.cell
  rw [hframe, he]
  let ab := Classical.choose
    (edge_endpoints_exist (⟨u.2.1.ty, host_step_edge u.2⟩ : EdgeName S))
  trans segment ℝ (compilerFrame C u.1 ab.1) (compilerFrame C u.1 ab.2)
  · exact image_segment ℝ (compilerFrame C u.1).toAffineEquiv.toAffineMap _ _
  · unfold host_step_portEnds FacetRecord.endpoints
    split
    · rfl
    · exact segment_symm _ _ _

/-- Step 1 of the V4 proof of `host_step_step2_strand` (V4 3.6):
"chain-active edges ... along the oriented line". Honesty identifies the
record's endpoint order with its active chain orientation; alignment places
both endpoints on the reference line. This concerns one port only. -/
private theorem host_step_step2_strand_step1_port_coordinates
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (H : FramedNode S)
    (ι : P.Incidence) (b : Bool) (u : host_step_Port C)
    (hu : host_step_portValid Y n H ι b u)
    (φ : ℝ →ᵃⁱ[ℝ] E d) (L : ℝ) (hL : 0 < L)
    (hφ0 : φ 0 = host_step_flagFrame H n ι b (P.flag ι).initial)
    (hφL : φ L = host_step_flagFrame H n ι b (P.flag ι).terminal) :
    ∃ x y : ℝ, x < y ∧
      (host_step_portEnds u).1 = φ x ∧ (host_step_portEnds u).2 = φ y ∧
      host_step_portEdge u = φ '' Icc x y ∧
      relint (host_step_portEdge u) = φ '' Ioo x y := by
  classical
  rcases hu with ⟨ht, hread, hty, hchain, hι, hb, hβ, halign, hpacket⟩
  let l := compilerLeaf C u.1
  have hs : l.prePattern.state ∈ honestStates S P :=
    (prePattern_components_honest P l.prePattern
      ((certificate_components_honest P l.1.val l.1.property).1 l.2)).1
  have hvec := host_step_step2_strand_step1_endpoint_vector l.prePattern.state hs
    u.2.1.facet.val u.2.1 hread u.2.2 hchain
  change (u.2.1.endpoints (host_step_edge u.2)).2 -
    (u.2.1.endpoints (host_step_edge u.2)).1 = chainVector u.2.2 at hvec
  have hnative : ((tileNode u.1).prototypeFrame 0).linear (chainVector u.2.2) =
      (host_step_portEnds u).2 - (host_step_portEnds u).1 := by
    have hv := (compilerFrame C u.1).map_vsub
      (u.2.1.endpoints (host_step_edge u.2)).2
      (u.2.1.endpoints (host_step_edge u.2)).1
    change (compilerFrame C u.1).linearIsometryEquiv
      ((u.2.1.endpoints (host_step_edge u.2)).2 -
        (u.2.1.endpoints (host_step_edge u.2)).1) =
      (host_step_portEnds u).2 - (host_step_portEnds u).1 at hv
    rw [hvec] at hv
    simpa [FramedNode.prototypeFrame, tileNode] using hv
  have hdir : (host_step_flagFrame H n ι b).linear (P.flag ι).direction = φ L - φ 0 := by
    rw [hφL, hφ0]
    exact (host_step_flagFrame H n ι b).toAffineMap.linearMap_vsub _ _
  have hpos : 0 < inner ℝ (φ L - φ 0)
      ((host_step_portEnds u).2 - (host_step_portEnds u).1) := by
    rw [← hdir, ← hnative]
    exact halign.2.2.1
  have hflag : host_step_flagEdge H n ι b = φ '' Icc 0 L := by
    rw [host_step_step2_strand_step1_flag_segment, ← hφ0, ← hφL]
    simpa only [AffineIsometry.coe_toAffineMap, segment_eq_Icc hL.le] using
      (image_segment ℝ φ.toAffineMap 0 L).symm
  have hspan : affineSpan ℝ (host_step_portEdge u) =
      affineSpan ℝ (host_step_flagEdge H n ι b) := halign.1 edgeIndex
  have hrange : affineSpan ℝ (host_step_flagEdge H n ι b) ≤
      (⊤ : AffineSubspace ℝ ℝ).map φ.toAffineMap := by
    apply affineSpan_le.mpr
    rw [hflag]
    rintro x ⟨t, ht, rfl⟩
    exact ⟨t, Set.mem_univ _, rfl⟩
  have hpoint (x : E d) (hx : x ∈ host_step_portEdge u) :
      x ∈ (⊤ : AffineSubspace ℝ ℝ).map φ.toAffineMap := by
    apply hrange
    rw [← hspan]
    exact mem_affineSpan ℝ hx
  obtain ⟨x, _, hx⟩ := hpoint (host_step_portEnds u).1
    (by rw [host_step_step2_strand_step1_port_segment]; exact left_mem_segment ℝ _ _)
  obtain ⟨y, _, hy⟩ := hpoint (host_step_portEnds u).2
    (by rw [host_step_step2_strand_step1_port_segment]; exact right_mem_segment ℝ _ _)
  have hxy : x < y := by
    rw [← hx, ← hy] at hpos
    change 0 < inner ℝ (φ L -ᵥ φ 0) (φ y -ᵥ φ x) at hpos
    rw [← φ.map_vsub, ← φ.map_vsub, φ.linearIsometry.inner_map_map] at hpos
    change 0 < (y - x) * (L - 0) at hpos
    nlinarith
  have he : host_step_portEdge u = φ '' Icc x y := by
    rw [host_step_step2_strand_step1_port_segment, ← hx, ← hy]
    simpa only [AffineIsometry.coe_toAffineMap, segment_eq_Icc hxy.le] using
      (image_segment ℝ φ.toAffineMap x y).symm
  refine ⟨x, y, hxy, hx.symm, hy.symm, he, ?_⟩
  rw [he, relint, φ.image_intrinsicInterior,
    host_step_step2_strand_step1_interval_relint x y hxy]

open private honest_rows_step4_cont_packet_step3_relint_transfer
  from Enforce.State.Rows in
/-- Step 1 of the V4 proof of `host_step_step2_strand_step2_terminal_bound_step1_flag_overlap`
(V4 3.6(F1)): "the half-space structure ... near points of relint F_{j-1}".
Equal local germs in a common affine span give common relative-interior
points arbitrarily close to any point of the regular closed first set. -/
private theorem host_step_step2_strand_step2_terminal_bound_step1_flag_overlap_step1_local_overlap
    {K L V : Set (E d)} (hspan : affineSpan ℝ K = affineSpan ℝ L)
    (hreg : closure (relint K) = K) (hV : IsOpen V) (heq : K ∩ V = L ∩ V)
    {p : E d} (hpK : p ∈ K) (hpV : p ∈ V) :
    p ∈ closure (relint K ∩ relint L) := by
  have hsub : relint K ∩ V ⊆ relint K ∩ relint L := by
    rintro x ⟨hx, hxV⟩
    exact ⟨hx, honest_rows_step4_cont_packet_step3_relint_transfer hspan hV heq hx hxV⟩
  exact closure_mono hsub (hV.closure_inter ⟨hreg.symm ▸ hpK, hpV⟩)

open private honest_rows_step4_cont_packet_step2_cell_cone
  honest_rows_step4_cont_packet_step1_placed_germ
  honest_rows_step4_cont_packet_step1_cell_closure
  restrictionOp_source_step5_relint_image
  from Enforce.State.Rows in
/-- Step 2 of the V4 proof of `host_step_step2_strand_step2_terminal_bound_step1_flag_overlap`
(V4 3.6(F1)): "then by a much smaller displacement into relint F_2 on the
recorded side ... then into relint F_3". For a single consecutive pair,
equal recorded sides give equal upper-cell germs at a common lower
relative-interior point, and hence arbitrarily nearby common upper interiors. -/
private theorem host_step_step2_strand_step2_terminal_bound_step1_flag_overlap_step2_coface
    {A B : S.ι} (F : FacetFlag S A) (G : FacetFlag S B)
    (φ ψ : E d ≃ᵃ[ℝ] E d) (k : FlagStep d)
    (hspan : affineSpan ℝ
        (φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier) =
      affineSpan ℝ (ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier))
    (hside : φ.linear '' flagSide F k = ψ.linear '' flagSide G k)
    (p : E d)
    (hp : p ∈ relint (φ '' (F.cell ⟨k.val, k.property.1, by omega⟩).val.carrier) ∩
      relint (ψ '' (G.cell ⟨k.val, k.property.1, by omega⟩).val.carrier)) :
    p ∈ closure
      (relint (φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier) ∩
        relint (ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier)) := by
  let i : FlagIndex d := ⟨k.val, k.property.1, by have := k.property.2; omega⟩
  let j : FlagIndex d := ⟨k.val + 1, by omega, k.property.2⟩
  rcases hp with ⟨hp, hq⟩
  rw [restrictionOp_source_step5_relint_image] at hp hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, hba⟩ := hq
  have hF := honest_rows_step4_cont_packet_step2_cell_cone (S.cx A)
    (F.cell i).val (F.cell j).val (F.cell i).property (F.cell j).property
    a (cellAnchor (F.cell i).val) ha (cellAnchor_mem _)
  have hG := honest_rows_step4_cont_packet_step2_cell_cone (S.cx B)
    (G.cell i).val (G.cell j).val (G.cell i).property (G.cell j).property
    b (cellAnchor (G.cell i).val) hb (cellAnchor_mem _)
  obtain ⟨V, hV, hpV, hVeq⟩ := honest_rows_step4_cont_packet_step1_placed_germ
    (F.cell j).val.flat.polyhedral φ a
  obtain ⟨W, hW, hpW, hWeq⟩ := honest_rows_step4_cont_packet_step1_placed_germ
    (G.cell j).val.flat.polyhedral ψ b
  rw [hF] at hVeq
  rw [hG] at hWeq
  change φ.linear '' tangentCone (F.cell j).val.carrier (cellAnchor (F.cell i).val) =
    ψ.linear '' tangentCone (G.cell j).val.carrier (cellAnchor (G.cell i).val) at hside
  have heq : (φ '' (F.cell j).val.carrier) ∩ (V ∩ W) =
      (ψ '' (G.cell j).val.carrier) ∩ (V ∩ W) := by
    ext x
    constructor
    · rintro ⟨hx, hxV, hxW⟩
      refine ⟨(hWeq x hxW).mpr ?_, hxV, hxW⟩
      rw [hba, ← hside]
      exact (hVeq x hxV).mp hx
    · rintro ⟨hx, hxV, hxW⟩
      refine ⟨(hVeq x hxV).mpr ?_, hxV, hxW⟩
      rw [hside, ← hba]
      exact (hWeq x hxW).mp hx
  exact host_step_step2_strand_step2_terminal_bound_step1_flag_overlap_step1_local_overlap
    hspan (honest_rows_step4_cont_packet_step1_cell_closure _ φ) (hV.inter hW) heq
    ⟨a, F.nested i j (by dsimp [i, j]; omega) (intrinsicInterior_subset ha), rfl⟩
    ⟨hpV, hba ▸ hpW⟩

open private actualCont_exists_step5_facet_cone actualCont_exists_step5_cell_subset
  honest_rows_step4_cont_packet_step1_placed_germ restrictionOp_source_step5_relint_image
  from Enforce.State.Rows in
/-- Step 3 of the V4 proof of `host_step_step2_strand_step2_terminal_bound_step1_flag_overlap`
(V4 3.6(F1)): "finally by a still smaller displacement off aff g".
At a common relative-interior facet point, equal inward cones give equal
domain germs. Regular closedness then supplies common ambient interior
points in every neighbourhood of that point. -/
private theorem host_step_step2_strand_step2_terminal_bound_step1_flag_overlap_step3_inward
    {A B : S.ι} (f : FacetName S A) (g : FacetName S B)
    (φ ψ : E d ≃ᵃ[ℝ] E d)
    (hside : φ.linear '' tangentCone (S.proto A).carrier (cellAnchor f.val) =
      ψ.linear '' tangentCone (S.proto B).carrier (cellAnchor g.val))
    (p : E d) (hp : p ∈ relint (φ '' f.val.carrier) ∩ relint (ψ '' g.val.carrier)) :
    p ∈ closure (interior (φ '' (S.proto A).carrier) ∩
      interior (ψ '' (S.proto B).carrier)) := by
  rcases hp with ⟨hp, hq⟩
  rw [restrictionOp_source_step5_relint_image] at hp hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, hba⟩ := hq
  have hF := actualCont_exists_step5_facet_cone A f a (cellAnchor f.val)
    ha (cellAnchor_mem _)
  have hG := actualCont_exists_step5_facet_cone B g b (cellAnchor g.val)
    hb (cellAnchor_mem _)
  obtain ⟨V, hV, hpV, hVeq⟩ := honest_rows_step4_cont_packet_step1_placed_germ
    (S.proto A).polyhedral φ a
  obtain ⟨W, hW, hpW, hWeq⟩ := honest_rows_step4_cont_packet_step1_placed_germ
    (S.proto B).polyhedral ψ b
  rw [hF] at hVeq
  rw [hG] at hWeq
  have hsub : interior (φ '' (S.proto A).carrier) ∩ (V ∩ W) ⊆
      ψ '' (S.proto B).carrier := by
    rintro x ⟨hx, hxV, hxW⟩
    apply (hWeq x hxW).mpr
    rw [hba, ← hside]
    exact (hVeq x hxV).mp (interior_subset hx)
  have hreg : closure (interior (φ '' (S.proto A).carrier)) =
      φ '' (S.proto A).carrier := by
    change closure (interior (φ.toHomeomorphOfFiniteDimensional ''
      (S.proto A).carrier)) = _
    rw [← Homeomorph.image_interior, ← Homeomorph.image_closure,
      (S.proto A).regularClosed]
    rfl
  have hpK : φ a ∈ closure (interior (φ '' (S.proto A).carrier)) := by
    rw [hreg]
    exact ⟨a, actualCont_exists_step5_cell_subset A f.val
      (Finset.mem_filter.mp f.property).1 (intrinsicInterior_subset ha), rfl⟩
  have hinside : interior (φ '' (S.proto A).carrier) ∩ (V ∩ W) ⊆
      interior (φ '' (S.proto A).carrier) ∩ interior (ψ '' (S.proto B).carrier) := by
    intro x hx
    exact ⟨hx.1, interior_maximal hsub (isOpen_interior.inter (hV.inter hW)) hx⟩
  exact closure_mono hinside ((hV.inter hW).closure_inter ⟨hpK, hpV, hba ▸ hpW⟩)

/-- Step 1 of the V4 proof of `host_step_step2_strand_step2_terminal_bound` (V4 3.6(F1)):
"the same holds ... for any tile ... having a chain of cells ... with the
recorded sides". Common relative-interior edge points can be displaced into
both interiors, successively through the common flag spans and sides, in
every neighbourhood of the chosen relative-interior point.
This is purely local geometry; neither node is assumed to occur in a tiling. -/
private theorem host_step_step2_strand_step2_terminal_bound_step1_flag_overlap
    (N H : FramedNode S) (m n : ℕ) {A A' : S.ι}
    (F : FacetFlag S A) (G : FacetFlag S A') (hN : N.ty = A) (hH : H.ty = A')
    (hspans : ∀ k, affineSpan ℝ (N.cell m (F.cell k).val) =
      affineSpan ℝ (H.cell n (G.cell k).val))
    (hsides : ∀ k, (N.prototypeFrame m).linear '' flagSide F k =
      (H.prototypeFrame n).linear '' flagSide G k)
    (hinward : (N.prototypeFrame m).linear ''
        tangentCone (S.proto N.ty).carrier (cellAnchor (F.cell facetIndex).val) =
      (H.prototypeFrame n).linear ''
        tangentCone (S.proto H.ty).carrier (cellAnchor (G.cell facetIndex).val))
    (p : E d) (hp : p ∈ relint (N.cell m (F.cell edgeIndex).val) ∩
      relint (H.cell n (G.cell edgeIndex).val)) :
    p ∈ closure (interior (N.carrier m) ∩ interior (H.carrier n)) := by
  have hfaces : ∀ (j : ℕ) (hj : 1 ≤ j) (hjd : j < d),
      p ∈ closure (relint (N.cell m (F.cell ⟨j, hj, hjd⟩).val) ∩
        relint (H.cell n (G.cell ⟨j, hj, hjd⟩).val)) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
        intro hjd
        exact subset_closure hp
    | succ j hj ih =>
        intro hjd
        apply closure_minimal ?_ isClosed_closure (ih (by omega))
        intro x hx
        exact host_step_step2_strand_step2_terminal_bound_step1_flag_overlap_step2_coface
          F G (N.prototypeFrame m) (H.prototypeFrame n) ⟨j, hj, hjd⟩
          (hspans _) (hsides _) x hx
  have htop := hfaces (d - 1) facetIndex.property.1 facetIndex.property.2
  apply closure_minimal ?_ isClosed_closure htop
  intro x hx
  let f : FacetName S A := ⟨(F.cell facetIndex).val,
    Finset.mem_filter.mpr ⟨(F.cell facetIndex).property, F.dimension facetIndex⟩⟩
  let g : FacetName S A' := ⟨(G.cell facetIndex).val,
    Finset.mem_filter.mpr ⟨(G.cell facetIndex).property, G.dimension facetIndex⟩⟩
  have hside : (N.prototypeFrame m).linear ''
      tangentCone (S.proto A).carrier (cellAnchor f.val) =
      (H.prototypeFrame n).linear '' tangentCone (S.proto A').carrier (cellAnchor g.val) := by
    simpa only [hN, hH] using hinward
  have h := host_step_step2_strand_step2_terminal_bound_step1_flag_overlap_step3_inward
    f g (N.prototypeFrame m) (H.prototypeFrame n) hside x hx
  simpa only [FramedNode.carrier, SubstSystem.supertile, placedSet,
    FramedNode.prototypeFrame, AffineEquiv.coe_trans, LinearEquiv.coe_toAffineEquiv,
    AffineIsometryEquiv.coe_toAffineEquiv, image_image, hN, hH] using h

/-- Step 2 of the V4 proof of `host_step_step2_strand_step2_terminal_bound` (V4 3.6(F1), 1.19):
"these ... are interior directions of T_x P". At a listed point of a
placed child, a neighbourhood of that child's support lies in the translated
tangent cone of any containing set. The native cone radius is transported
by the full affine prototype frame, so no scalar expansion is required. -/
private theorem host_step_step2_strand_step2_terminal_bound_step2_local_sector
    (H : FramedNode S) (n : ℕ) (K : Set (E d)) (p : E d)
    (hp : H.Lists n p) (hHK : H.carrier n ⊆ K) :
    ∃ U : Set (E d), IsOpen U ∧ p ∈ U ∧
      H.carrier n ∩ U ⊆ (fun v => p + v) '' tangentCone K p := by
  let e := H.prototypeFrame n
  let x := e.symm p
  let H₀ : FramedNode S := ⟨H.ty, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hcarrier : H.carrier n = e '' (S.proto H.ty).carrier := by
    simp only [FramedNode.carrier, SubstSystem.supertile, placedSet, image_image]
    rfl
  have hzero : H₀.carrier 0 = (S.proto H.ty).carrier := by
    simp [H₀, FramedNode.carrier, SubstSystem.supertile, placedSet]
  have hx : H₀.Lists 0 x := by
    obtain ⟨v, hv, y, hy, hyp⟩ := hp
    refine ⟨v, hv, x, ?_, ?_⟩
    · have he : y = x := e.injective (hyp.trans (e.apply_symm_apply p).symm)
      exact he ▸ hy
    · simp [H₀, FramedNode.prototypeFrame]
  obtain ⟨r, hr, hcone⟩ := uniform_prototype_cone_radius S
  have hlocal := hcone H₀ x hx
  rw [hzero] at hlocal
  let U := e '' ball x r
  have hU : IsOpen U := e.toHomeomorphOfFiniteDimensional.isOpenMap _ isOpen_ball
  have hpU : p ∈ U := ⟨x, mem_ball_self hr, e.apply_symm_apply p⟩
  refine ⟨U, hU, hpU, ?_⟩
  rintro y ⟨hyH, z, hz, rfl⟩
  have hzH : z ∈ (S.proto H.ty).carrier := by
    rw [hcarrier] at hyH
    exact e.injective.mem_set_image.mp hyH
  have hzcone : z ∈ (fun v => x + v) '' tangentCone (S.proto H.ty).carrier x :=
    (hlocal ▸ (show z ∈ (S.proto H.ty).carrier ∩ ball x r from ⟨hzH, hz⟩)).1
  obtain ⟨v, ⟨δ, hδ, hv⟩, rfl⟩ := hzcone
  have hmap (t : ℝ) : e (x + t • v) = p + t • e.linear v := by
    have h := e.map_vadd x (t • v)
    simpa only [vadd_eq_add, map_smul, add_comm, x, e.apply_symm_apply] using h
  refine ⟨e.linear v, ⟨δ, hδ, ?_⟩, ?_⟩
  · intro t ht htδ
    apply hHK
    rw [hcarrier, ← hmap]
    exact ⟨x + t • v, hv t ht htδ, rfl⟩
  · simpa only [one_smul] using (hmap 1).symm

/-- Step 3 of the V4 proof of `host_step_step2_strand_step2_terminal_bound` (V4 3.6(F1)):
"the honest geometry of P ... and B is its child". Each prescribed
child, including the proposed sibling, is contained in its placed parent. -/
private theorem host_step_step2_strand_step2_terminal_bound_step3_child_subset
    (Q : FramedNode S) (n : ℕ) (i : S.I Q.ty) :
    (Q.child n i).carrier n ⊆ Q.carrier (n + 1) := by
  rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hmem : (S.child Q.ty i).frame x ∈ S.σ '' (S.proto Q.ty).carrier := by
    rw [S.children_cover]
    exact mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩
  obtain ⟨y, hy, he⟩ := hmem
  refine ⟨(S.σ ^ (n + 1)) y, ⟨y, hy, rfl⟩, ?_⟩
  change Q.frame ((S.σ ^ (n + 1)) y) = Q.frame (S.placeChild n i ((S.σ ^ n) x))
  have hplace : S.placeChild n i ((S.σ ^ n) x) =
      (S.σ ^ n) ((S.child Q.ty i).frame x) := by
    change linearConj S.σ (n : ℤ) (S.child Q.ty i).rotation.toLinearEquiv
        ((S.σ ^ n) x) + (S.σ ^ n) (S.child Q.ty i).offset =
      (S.σ ^ n) ((S.child Q.ty i).rotation x + (S.child Q.ty i).offset)
    simp [linearConj, zpow_neg, LinearEquiv.mul_apply]
  rw [hplace, ← he, pow_succ]
  rfl

/-- Step 4 of the V4 proof of `host_step_step2_strand_step2_terminal_bound` (V4 3.6(F1)):
"into relint g, and finally ... to either side". The top cell of either
side's flag is the named incidence facet, with equality of cell names. -/
private theorem host_step_step2_strand_step2_terminal_bound_step4_flag_top
    (ι : P.Incidence) (b : Bool) :
    ((P.sideFlag ι b).cell facetIndex).val = (ι.val.sideFacet b).val := by
  have h := P.sideFlag_eq ι b facetIndex
  rw [(P.flag ι).top] at h
  have hcarrier : ((P.sideFlag ι b).cell facetIndex).val.carrier =
      (ι.val.sideFacet b).val.carrier := by
    apply Set.image_injective.mpr (S.child ι.val.ty (ι.val.sideIndex b)).frame.injective
    change placedSet (S.child ι.val.ty (ι.val.sideIndex b)).frame _ = _
    rw [h]
    cases b
    · rfl
    · exact ι.val.paired
  have cell_eq (e f : Cell d) (h : e.carrier = f.carrier) : e = f := by
    rcases e with ⟨K, j, hj⟩
    rcases f with ⟨L, k, hk⟩
    cases h
    have hjk : j = k := hj.dimension.symm.trans hk.dimension
    cases hjk
    rfl
  exact cell_eq _ _ hcarrier

/-- Step 5 of the V4 proof of `host_step_step2_strand_step2_terminal_bound` (V4 3.6(2a)):
"relative interiors of distinct cells are disjoint". A listed vertex
of a native node cannot lie in the relative interior of one of its edges. -/
private theorem host_step_step2_strand_step2_terminal_bound_step5_vertex_exclusion
    (N : FramedNode S) (e : PrototypeEdge S N.ty) (p : E d)
    (hp : N.Lists 0 p) : p ∉ relint (N.cell 0 e.val) := by
  classical
  obtain ⟨v, hv, x, hx, rfl⟩ := hp
  have hcell (c : Cell d) : N.cell 0 c = N.frame '' c.carrier := by
    rfl
  have hrel : relint (N.cell 0 e.val) = N.frame '' relint e.val.carrier := by
    rw [hcell]
    exact N.frame.toAffineIsometry.image_intrinsicInterior _
  intro hmem
  rw [hrel] at hmem
  have hxe : x ∈ relint e.val.carrier := N.frame.injective.mem_set_image.mp hmem
  have hxv : x ∈ relint v.carrier := by
    rw [vertexPoint_spec (⟨v, hv⟩ : VertexName S N.ty)] at hx ⊢
    simpa only [relint, intrinsicInterior_singleton] using hx
  have hne : v ≠ e.val := by
    intro h
    have hvdim := (Finset.mem_filter.mp hv).2
    have hedim := (Finset.mem_filter.mp e.property).2
    rw [h] at hvdim
    omega
  exact Set.disjoint_left.mp
    ((S.cx N.ty).relint_disjoint v (Finset.mem_filter.mp hv).1
      e.val (Finset.mem_filter.mp e.property).1 hne) hxv hxe

/-- Step 2 of the V4 proof of `host_step_step2_strand` (V4 3.6(2a)):
"The strand never passes p_N". A single aligned port starting in h
strictly before p_N cannot cross p_N: its backward flag displacements
enter the terminal END sector, whose template lists p_N as a vertex. -/
private theorem host_step_step2_strand_step2_terminal_bound
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f)
    (hend : host_step_endEvent Y n B f (proposedParent D B hB)
      (host_step_flagFrame (proposedSibling D B hB f a) n a.record.incidence
        (!a.record.sideIndex) (P.flag a.record.incidence).terminal))
    (u : host_step_Port C)
    (hu : host_step_portValid Y n (proposedSibling D B hB f a)
      a.record.incidence (!a.record.sideIndex) u)
    (hstart : (host_step_portEnds u).1 ∈
      host_step_flagEdge (proposedSibling D B hB f a) n
        a.record.incidence (!a.record.sideIndex))
    (hbefore : (host_step_portEnds u).1 ≠
      host_step_flagFrame (proposedSibling D B hB f a) n a.record.incidence
        (!a.record.sideIndex) (P.flag a.record.incidence).terminal) :
    host_step_portEdge u ⊆ host_step_flagEdge (proposedSibling D B hB f a) n
      a.record.incidence (!a.record.sideIndex) := by
  let H := proposedSibling D B hB f a
  let Q := proposedParent D B hB
  let ι := a.record.incidence
  let b := !a.record.sideIndex
  let p := host_step_flagFrame H n ι b (P.flag ι).terminal
  obtain ⟨φ, L, hL, hφ0, hφL, hflag, _⟩ :=
    host_step_step2_strand_step1_chart H n ι b
  obtain ⟨x, y, hxy, hx, hy, hedge, hopen⟩ :=
    host_step_step2_strand_step1_port_coordinates Y n H ι b u hu φ L hL hφ0 hφL
  have hxL : x ∈ Icc 0 L := by
    rw [hx, hflag] at hstart
    exact φ.injective.mem_set_image.mp hstart
  have hxlt : x < L := lt_of_le_of_ne hxL.2 (fun he =>
    hbefore (hx.trans ((congrArg φ he).trans hφL)))
  have hyL : y ≤ L := by
    by_contra h
    have hLy : L < y := lt_of_not_ge h
    have hcross : p ∈ relint (host_step_portEdge u) := by
      rw [hopen]
      exact ⟨L, ⟨hxlt, hLy⟩, hφL⟩
    have hnearEdge : p ∈ closure (relint (host_step_portEdge u) ∩
        relint (host_step_flagEdge H n ι b)) := by
      have hsub : φ '' Ioo x L ⊆ relint (host_step_portEdge u) ∩
          relint (host_step_flagEdge H n ι b) := by
        rintro z ⟨t, ht, rfl⟩
        rw [hopen]
        refine ⟨⟨t, ⟨ht.1, ht.2.trans hLy⟩, rfl⟩, ?_⟩
        rw [hflag, relint, φ.image_intrinsicInterior,
          host_step_step2_strand_step1_interval_relint 0 L hL]
        exact ⟨t, ⟨hxL.1.trans_lt ht.1, ht.2⟩, rfl⟩
      apply closure_mono hsub
      apply image_closure_subset_closure_image φ.continuous
      refine ⟨L, ?_, hφL⟩
      rw [closure_Ioo hxlt.ne]
      exact ⟨hxlt.le, le_rfl⟩
    have halign := hu.2.2.2.2.2.2.2.1
    have hnear : p ∈ closure (interior ((tileNode u.1).carrier 0) ∩
        interior (H.carrier n)) := by
      apply closure_minimal ?_ isClosed_closure hnearEdge
      intro z hz
      apply host_step_step2_strand_step2_terminal_bound_step1_flag_overlap
        (tileNode u.1) H 0 n u.2.2.chain.val (P.sideFlag ι b)
        hu.2.2.1.symm rfl halign.1 halign.2.1
      · simpa only [u.2.2.chain.property,
          host_step_step2_strand_step2_terminal_bound_step4_flag_top] using halign.2.2.2
      · exact hz
    have hlistedH : H.Lists n p := by
      have hv := host_step_step1_seed_step2_child_endpoint Q n ι b
        (P.flag ι).terminal (Or.inr rfl)
      rw [← host_step_step1_seed_step1_flag_frame Q n ι b] at hv
      exact hv.1
    have hsub : H.carrier n ⊆ Q.carrier (n + 1) := by
      have hty := (Parser.ageOneFacet_semantics D hD B hB f a).2.1
      have h := host_step_step2_strand_step2_terminal_bound_step3_child_subset
        (⟨ι.val.ty, Q.frame⟩ : FramedNode S) n (ι.val.sideIndex b)
      have hQ : (⟨ι.val.ty, Q.frame⟩ : FramedNode S) = Q := by
        apply FramedNode.ext
        · exact hty
        · rfl
      change H.carrier n ⊆ (⟨ι.val.ty, Q.frame⟩ : FramedNode S).carrier (n + 1) at h
      simpa only [hQ] using h
    obtain ⟨U, hU, hpU, hUsub⟩ :=
      host_step_step2_strand_step2_terminal_bound_step2_local_sector
        H n (Q.carrier (n + 1)) p hlistedH hsub
    have happroach : Parser.ApproachesSector u.1 p
        ((fun v => p + v) '' tangentCone (Q.carrier (n + 1)) p) := by
      intro ε hε
      obtain ⟨z, ⟨hzU, hzball⟩, hzt, hzH⟩ := mem_closure_iff_nhds.mp hnear
        (U ∩ ball p ε) ((hU.inter isOpen_ball).mem_nhds ⟨hpU, mem_ball_self hε⟩)
      have hzt' : z ∈ interior u.1.carrier := by
        have hc : (tileNode u.1).carrier 0 = u.1.carrier := by
          rw [compilerFrame_carrier C u.1]
          simp [tileNode, FramedNode.carrier, SubstSystem.supertile, placedSet]
        simpa only [hc] using hzt
      refine ⟨z, ⟨hzt', ?_⟩, hzball⟩
      apply interior_mono hUsub
      rw [interior_inter, hU.interior_eq]
      exact ⟨hzH, hzU⟩
    obtain ⟨t, ht, j, θ, hpiece, hpj, hsector, hθ, hactual⟩ := hend
    have happroach' : Parser.ApproachesSector u.1
        (Compiler.endVertex (compilerFrame C t) j)
        (Compiler.endSector (compilerFrame C t) j) := by
      rw [hpj, hsector]
      exact happroach
    have hlisted := (trigger_coverage Y hY t ht j θ hθ hactual u.1 hu.1 happroach').2.1
    rw [hpj] at hlisted
    let e : PrototypeEdge S (tileNode u.1).ty := ⟨(host_step_edge u.2).val, by
      rw [← hu.2.2.1]
      exact (host_step_edge u.2).property⟩
    exact host_step_step2_strand_step2_terminal_bound_step5_vertex_exclusion
      (tileNode u.1) e p hlisted hcross
  rw [hedge, hflag]
  exact Set.image_mono (fun _ ht => ⟨hxL.1.trans ht.1, ht.2.trans hyL⟩)

/-- Step 1 of the V4 proof of `host_step_step2_strand_step2_terminal_counter` (V4 3.6, Step 1):
"their (S6) record is the header of σ A_P ... in t's frame".
The restriction theorem identifies the header of any END slot on the actual
facet piece, not just the particular slot chosen when constructing the event. -/
private theorem host_step_step2_strand_step2_terminal_counter_step1_header
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) (p : E d) (hp : B.node.Lists n p)
    (t : PlacedMarkedTile (systemM S P C)) (j : EndSlot (compilerLeaf C t))
    (hpiece : Parser.IsFacetPiece Y n B.node f t j.facet)
    (hj : Compiler.endVertex (compilerFrame C t) j = p) :
    j.header = host_step_step1_seed_step1_header (proposedParent D B hB) n
      (compilerFrame C t) p := by
  have cell_ext (e e' : Cell d) (h : e.carrier = e'.carrier) : e = e' := by
    rcases e with ⟨K, k, hk⟩
    rcases e' with ⟨K', k', hk'⟩
    cases h
    have hd : k = k' := hk.dimension.symm.trans hk'.dimension
    cases hd
    rfl
  let v : VertexName S (tileNode t).ty :=
    ⟨j.vertex.val, by change _ ∈ (S.cx (compilerLeaf C t).prototype).vertices
                      rw [← j.type_eq]; exact j.vertex.property⟩
  have hv : v.val.carrier ⊆ j.facet.val.carrier := by
    simpa only [v, j.facet_eq] using j.onFacet
  have hvp : vertexPoint v = vertexPoint j.vertex := by
    apply Set.singleton_injective
    exact (vertexPoint_spec v).symm.trans (vertexPoint_spec j.vertex)
  obtain ⟨j', hfacet, hpoint, _, _, hheader⟩ :=
    host_step_step1_seed_step3_restricted_header Y n D hD B hB f a p hp
      t j.facet v hpiece hv (by simpa only [hvp] using hj)
  have hvertex : j'.vertex.val = j.vertex.val := by
    apply cell_ext
    rw [vertexPoint_spec, vertexPoint_spec]
    exact congrArg (fun x : E d => ({x} : Set (E d)))
      ((compilerFrame C t).injective (hpoint.trans hj.symm))
  have hread := j'.header_eq
  rw [hvertex, hfacet] at hread
  exact (Option.some.inj (j.header_eq.symm.trans hread)).trans hheader

/-- Step 2 of the V4 proof of `host_step_step2_strand_step2_terminal_counter` (V4 3.6, F1 and 2a):
"u_m has interior points in int(p_N + G_p_N) ... arbitrarily close to p_N".
This is only the flag-displacement assertion for a native geometric tile.
It assumes neither an output tiling nor an END template or counter row. -/
private theorem host_step_step2_strand_step2_terminal_counter_step2_sector
    (Q : FramedNode S) (n : ℕ) (ι : P.Incidence) (b : Bool) (hι : ι.val.ty = Q.ty)
    (N : FramedNode S) (z : host_step_Chain P) (hty : z.1.ty = N.ty)
    (halign : host_step_aligned
      ((⟨ι.val.ty, Q.frame⟩ : FramedNode S).child n (ι.val.sideIndex b)) n ι b N 0 z)
    (hsub : N.cell 0 (host_step_edge z).val ⊆ host_step_flagEdge
      ((⟨ι.val.ty, Q.frame⟩ : FramedNode S).child n (ι.val.sideIndex b)) n ι b)
    (hterminal : N.prototypeFrame 0 (z.1.endpoints (host_step_edge z)).2 =
      P.incidencePlacement Q (n + 1) ι (P.flag ι).terminal) :
    let p := P.incidencePlacement Q (n + 1) ι (P.flag ι).terminal
    ∀ ε : ℝ, 0 < ε →
      (interior (N.carrier 0) ∩
        interior ((fun v => p + v) '' tangentCone (Q.carrier (n + 1)) p) ∩
        ball p ε).Nonempty := by
  -- Move backwards along the nondegenerate terminal edge, then into the
  -- successive flag cells on their common recorded sides, and finally into
  -- the selected child side. The same displacements enter N and Q. At the
  -- endpoint, their directions are interior directions of the parent cone.
  sorry

/-- Step 3 of the V4 proof of `host_step_step2_strand_step2_terminal_counter` (V4 3.6, 2a):
"u_m is a port on g at p_N". In a complete honest annotated star, a listed
tile with the aligned facet germ is one of the primitive ports on that
incidence. This identifies geometry only; no leaf label or END row is assumed. -/
private theorem host_step_step2_strand_step2_terminal_counter_step3_primitive_port
    (Q : FramedNode S) (n : ℕ) (ι : P.Incidence) (b : Bool) (hι : ι.val.ty = Q.ty)
    (φ : Iso d) (Z : EndGeometry P) (hZ : Z ∈ honestEndGeometries S P)
    (hheader : Z.header = host_step_step1_seed_step1_header Q n φ
      (P.incidencePlacement Q (n + 1) ι (P.flag ι).terminal))
    (hapex : φ (vertexPoint Z.vertex) =
      P.incidencePlacement Q (n + 1) ι (P.flag ι).terminal)
    (N : FramedNode S) (hN : N ∈ Z.tiles)
    (z : host_step_Chain P) (hty : z.1.ty = N.ty)
    (halign : host_step_aligned
      ((⟨ι.val.ty, Q.frame⟩ : FramedNode S).child n (ι.val.sideIndex b)) n ι b
      (N.move φ) 0 z)
    (hsub : (N.move φ).cell 0 (host_step_edge z).val ⊆ host_step_flagEdge
      ((⟨ι.val.ty, Q.frame⟩ : FramedNode S).child n (ι.val.sideIndex b)) n ι b)
    (hterminal : (N.frame.trans φ) (z.1.endpoints (host_step_edge z)).2 =
      P.incidencePlacement Q (n + 1) ι (P.flag ι).terminal) :
    ∃ port ∈ Z.primitivePorts,
      port.tile = N ∧ port.facet.val = z.1.facet.val ∧ port.incidence = ι := by
  -- In the honest realization of Z, the header identifies the primitive
  -- facet germ. Flag displacements put the tile's facet on that germ;
  -- hereditary facet dichotomy identifies its first-generation provider.
  -- The primitive-port biconditional in EndGeometryRealizes then lists it.
  sorry

/-- Step 4 of the V4 proof of `host_step_step2_strand_step2_terminal_counter` (V4 3.6, F2):
"realised at v by u's frame". Radial tangent cones commute with an
invertible affine change of frame, using its linear part on directions. -/
private theorem host_step_step2_strand_step2_terminal_counter_step4_tangent_image
    (e : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) (x : E d) :
    tangentCone (e '' K) (e x) = e.linear '' tangentCone K x := by
  have hmap (y u : E d) (t : ℝ) : e (y + t • u) = e y + t • e.linear u := by
    simpa only [vadd_eq_add, add_comm, map_smul] using e.map_vadd y (t • u)
  ext u
  constructor
  · rintro ⟨ε, hε, hu⟩
    refine ⟨e.linear.symm u, ⟨ε, hε, ?_⟩, e.linear.apply_symm_apply u⟩
    intro t ht htε
    apply e.injective.mem_set_image.mp
    simpa only [hmap, e.linear.apply_symm_apply] using hu t ht htε
  · rintro ⟨u, ⟨ε, hε, hu⟩, rfl⟩
    refine ⟨ε, hε, ?_⟩
    intro t ht htε
    rw [← hmap]
    exact Set.mem_image_of_mem e (hu t ht htε)

/-- Step 4 of the V4 proof of `host_step_step2_strand_step2_terminal_counter` (V4 3.6, 2c):
"e_s is a chain-active edge at p_N along h". A nondegenerate subsegment
ending at the same endpoint has exactly the same radial tangent ray there. -/
private theorem host_step_step2_strand_step2_terminal_counter_step4_terminal_germ
    (p₀ p q : E d) (hq : q ∈ segment ℝ p₀ p) (hne : q ≠ p) :
    tangentCone (segment ℝ q p) p = tangentCone (segment ℝ p₀ p) p := by
  have hsubset : segment ℝ q p ⊆ segment ℝ p₀ p :=
    (convex_segment p₀ p).segment_subset hq (right_mem_segment ℝ p₀ p)
  rw [segment_symm, segment_eq_image'] at hq
  obtain ⟨a, ha, heq⟩ := hq
  have hapos : 0 < a := by
    apply lt_of_le_of_ne ha.1
    intro he
    apply hne
    simpa only [← he, zero_smul, add_zero] using heq.symm
  have hcontract (x : E d) (hx : x ∈ segment ℝ p₀ p) :
      p + a • (x - p) ∈ segment ℝ q p := by
    rw [segment_symm, segment_eq_image'] at hx ⊢
    obtain ⟨b, hb, rfl⟩ := hx
    refine ⟨b, hb, ?_⟩
    rw [← heq]
    simp only [add_sub_cancel_left, smul_smul, mul_comm]
  apply Set.Subset.antisymm
  · rintro v ⟨ε, hε, hv⟩
    exact ⟨ε, hε, fun t ht htε => hsubset (hv t ht htε)⟩
  · rintro v ⟨ε, hε, hv⟩
    refine ⟨a * ε, mul_pos hapos hε, ?_⟩
    intro t ht htε
    have hm := hcontract _ (hv (t / a) (div_pos ht hapos)
      ((div_lt_iff₀ hapos).mpr (by simpa only [mul_comm] using htε)))
    simpa only [add_sub_cancel_left, smul_smul, mul_div_cancel₀ _ hapos.ne'] using hm

/-- Step 5 of the V4 proof of `host_step_step2_strand_step2_terminal_counter` (V4 3.6, 2c; 2.5 E2):
"(E2) at θ_N gives κ⁺(e_s)=N". Once the primitive port and its terminal
flag ray are identified, the conclusion is exactly the endpoint-counter row. -/
private theorem host_step_step2_strand_step2_terminal_counter_step5_row
    {l : LeafType P} {j : EndSlot l} (T : EndTemplate j) (hrow : endRow T)
    (port : PrimitivePort P) (hport : port ∈ T.geometry.primitivePorts)
    (l' : LeafType P) (hl' : (port.tile, l') ∈ T.configuration.tiles)
    (z : host_step_Chain P) (hr : leafRecord l' port.facet.val = some z.1)
    (hc : z.2 ∈ z.1.chains) (G : State.FlagTangent (d := d))
    (hG : T.geometry.header.flagTangent port.incidence = some G)
    (hi : G.initial = false)
    (hx : vertexPoint T.geometry.vertex ∈
      placedSet port.tile.frame (host_step_edge z).val.carrier)
    (hray : tangentCone (placedSet port.tile.frame (host_step_edge z).val.carrier)
      (vertexPoint T.geometry.vertex) = G.cones edgeIndex) :
    z.1.kappaPlus (host_step_edge z) = P.N := by
  have h := (hrow.2.1.2 port hport l' hl' z.1 hr G hG).2
    (host_step_edge z) ⟨z.2, hc, rfl⟩ hx hray
  simpa only [hi, Bool.false_eq_true, ite_false] using h

/-- Step 2 of the V4 proof of `host_step_step2_strand` (V4 3.6(2c)):
"(E2) at θ_N gives κ⁺(e_s)=N". This is the terminal END row for
one aligned port ending at p_N, independently of how the port was reached. -/
private theorem host_step_step2_strand_step2_terminal_counter
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f)
    (hend : host_step_endEvent Y n B f (proposedParent D B hB)
      (host_step_flagFrame (proposedSibling D B hB f a) n a.record.incidence
        (!a.record.sideIndex) (P.flag a.record.incidence).terminal))
    (u : host_step_Port C)
    (hu : host_step_portValid Y n (proposedSibling D B hB f a)
      a.record.incidence (!a.record.sideIndex) u)
    (hsub : host_step_portEdge u ⊆ host_step_flagEdge (proposedSibling D B hB f a) n
      a.record.incidence (!a.record.sideIndex))
    (hterminal : (host_step_portEnds u).2 =
      host_step_flagFrame (proposedSibling D B hB f a) n a.record.incidence
        (!a.record.sideIndex) (P.flag a.record.incidence).terminal) :
    u.2.1.kappaPlus (host_step_edge u.2) = P.N := by
  classical
  let Q := proposedParent D B hB
  let H := proposedSibling D B hB f a
  let ι := a.record.incidence
  let b := !a.record.sideIndex
  let p := P.incidencePlacement Q (n + 1) ι (P.flag ι).terminal
  have hframe : host_step_flagFrame H n ι b = P.incidencePlacement Q (n + 1) ι :=
    host_step_step1_seed_step1_flag_frame Q n ι b
  have hι : ι.val.ty = Q.ty := (Parser.ageOneFacet_semantics D hD B hB f a).2.1
  change (host_step_portEnds u).2 = host_step_flagFrame H n ι b (P.flag ι).terminal
    at hterminal
  have hterminal' : (host_step_portEnds u).2 = p := by
    exact hterminal.trans (congrArg (fun e : E d ≃ᵃ[ℝ] E d => e (P.flag ι).terminal) hframe)
  obtain ⟨t, ht, j, θ, hpiece, hj, hsector, hθ, hactual⟩ := hend
  change Compiler.endVertex (compilerFrame C t) j =
    host_step_flagFrame H n ι b (P.flag ι).terminal at hj
  have hj' : Compiler.endVertex (compilerFrame C t) j = p := by
    simpa only [hframe] using hj
  have hpflag : p = host_step_flagFrame H n ι b (P.flag ι).terminal := by
    rw [hframe]
  have hp : B.node.Lists n p :=
    (host_step_step1_seed_step2_endpoint_piece Y n D hD B hB f a p (Or.inr hpflag)).1
  have hh := host_step_step2_strand_step2_terminal_counter_step1_header
    Y n D hD B hB f a p hp t j hpiece hj'
  change j.header = host_step_step1_seed_step1_header Q n (compilerFrame C t) p at hh
  obtain ⟨T, rfl, hrow⟩ := hθ
  rcases hu with ⟨hut, hread, hty, hc, hinc, hside, hβ, halign, hpacket⟩
  have hnear := host_step_step2_strand_step2_terminal_counter_step2_sector
    Q n ι b hι (tileNode u.1) u.2 hty halign hsub
    (by simpa [FramedNode.prototypeFrame, tileNode, host_step_portEnds] using hterminal')
  have hcarrier : (tileNode u.1).carrier 0 = u.1.carrier := by
    rw [compilerFrame_carrier C u.1]
    simp [tileNode, FramedNode.carrier, SubstSystem.supertile, placedSet]
  change Compiler.endSector (compilerFrame C t) j =
    (fun v => host_step_flagFrame H n ι b (P.flag ι).terminal + v) ''
      tangentCone (Q.carrier (n + 1)) (host_step_flagFrame H n ι b (P.flag ι).terminal)
    at hsector
  rw [hframe] at hsector
  have hnear' : Parser.ApproachesSector u.1 (Compiler.endVertex (compilerFrame C t) j)
      (Compiler.endSector (compilerFrame C t) j) := by
    intro ε hε
    rw [hj', hsector]
    simpa only [hframe, hcarrier] using hnear ε hε
  obtain ⟨⟨⟨N, l'⟩, hNl, hplaced⟩, _, _⟩ :=
    trigger_coverage Y hY t ht j T.configuration ⟨T, rfl, hrow⟩ hactual u.1 hut hnear'
  have hleaf : compilerLeaf C u.1 = l' := by
    rw [hplaced]
    exact (compiler_decode_unique C _ _).1
  have hφ : compilerFrame C u.1 = N.frame.trans (compilerFrame C t) := by
    rw [hplaced]
    exact (compiler_decode_unique C _ _).2
  have hnode : tileNode u.1 = N.move (compilerFrame C t) := by
    apply FramedNode.ext
    · change (compilerLeaf C u.1).prototype = N.ty
      rw [hleaf]
      exact (T.configuration.types_match _ hNl).symm
    · exact hφ
  have hN : N ∈ T.geometry.tiles := by
    rw [← T.tiles_eq]
    exact Finset.mem_image.mpr ⟨(N, l'), hNl, rfl⟩
  have hvertex : vertexPoint T.geometry.vertex = vertexPoint j.vertex := by
    apply Set.singleton_injective
    exact (vertexPoint_spec T.geometry.vertex).symm.trans
      ((congrArg Cell.carrier T.vertex_eq).trans (vertexPoint_spec j.vertex))
  have hapex : compilerFrame C t (vertexPoint T.geometry.vertex) = p := by
    rw [hvertex]
    exact hj'
  obtain ⟨port, hport, hportN, hfacet, hportι⟩ :=
    host_step_step2_strand_step2_terminal_counter_step3_primitive_port
      Q n ι b hι (compilerFrame C t) T.geometry T.honest_geometry
      (T.header_eq.trans hh) hapex N hN u.2
      (by simpa only [hnode, FramedNode.move] using hty)
      (by simpa only [hnode] using halign)
      (by simpa only [host_step_portEdge, hnode] using hsub)
      (by simpa only [host_step_portEnds, hφ] using hterminal')
  have hstart : (host_step_portEnds u).1 ∈ host_step_flagEdge H n ι b :=
    hsub (by rw [host_step_step2_strand_step1_port_segment]; exact left_mem_segment ℝ _ _)
  have hne : (host_step_portEnds u).1 ≠ p := by
    obtain ⟨ε, hε, hlength⟩ := host_step_step2_strand_step1_native_length (C := C)
    intro heq
    have hlen := hlength u
    rw [hterminal', heq, dist_self] at hlen
    exact (not_le_of_gt hε) hlen
  have hray : tangentCone (host_step_portEdge u) p =
      tangentCone (host_step_flagEdge H n ι b) p := by
    rw [host_step_step2_strand_step1_port_segment, hterminal',
      host_step_step2_strand_step1_flag_segment, hframe]
    apply host_step_step2_strand_step2_terminal_counter_step4_terminal_germ _ p _ _ hne
    simpa only [host_step_step2_strand_step1_flag_segment, hframe] using hstart
  have hflag : host_step_flagEdge H n ι b =
      P.incidencePlacement Q (n + 1) ι '' ((P.flag ι).flag.cell edgeIndex).val.carrier := by
    rw [host_step_step2_strand_step1_flag_segment, hframe, (P.flag ι).edge_eq]
    exact (image_segment ℝ (P.incidencePlacement Q (n + 1) ι).toAffineMap _ _).symm
  let G : State.FlagTangent (d := d) := {
    cones := fun k => (compilerFrame C t).linearIsometryEquiv.symm ''
      tangentCone (P.incidencePlacement Q (n + 1) ι '' ((P.flag ι).flag.cell k).val.carrier) p
    initial := false
    sides := fun k => (compilerFrame C t).linearIsometryEquiv.symm ''
      ((P.incidencePlacement Q (n + 1) ι).linear '' (P.flag ι).sides k) }
  have hpne : P.incidencePlacement Q (n + 1) ι (P.flag ι).terminal ≠
      P.incidencePlacement Q (n + 1) ι (P.flag ι).initial :=
    (P.incidencePlacement Q (n + 1) ι).injective.ne (P.flag ι).distinct.symm
  have hG : T.geometry.header.flagTangent ι = some G := by
    rw [T.header_eq, hh]
    simp [host_step_step1_seed_step1_header, G, p, hι, hpne]
  have hGcone : G.cones edgeIndex = (compilerFrame C t).linearIsometryEquiv.symm ''
      tangentCone (host_step_flagEdge H n ι b) p := by
    rw [hflag]
  let K := placedSet port.tile.frame (host_step_edge u.2).val.carrier
  have hphysical : compilerFrame C t '' K = host_step_portEdge u := by
    rw [host_step_portEdge, hnode]
    simp [K, hportN, placedSet, FramedNode.cell, FramedNode.prototypeFrame,
      FramedNode.move, Set.image_image]
  have hx : vertexPoint T.geometry.vertex ∈ K := by
    apply (compilerFrame C t).injective.mem_set_image.mp
    rw [hapex, hphysical, ← hterminal', host_step_step2_strand_step1_port_segment]
    exact right_mem_segment ℝ _ _
  have htransport : tangentCone (host_step_portEdge u) p =
      (compilerFrame C t).linearIsometryEquiv ''
        tangentCone K (vertexPoint T.geometry.vertex) := by
    have he := host_step_step2_strand_step2_terminal_counter_step4_tangent_image
      (compilerFrame C t).toAffineEquiv K (vertexPoint T.geometry.vertex)
    change tangentCone (compilerFrame C t '' K)
      (compilerFrame C t (vertexPoint T.geometry.vertex)) =
        (compilerFrame C t).linearIsometryEquiv ''
          tangentCone K (vertexPoint T.geometry.vertex) at he
    rwa [hphysical, hapex] at he
  have hlocalray : tangentCone K (vertexPoint T.geometry.vertex) = G.cones edgeIndex := by
    rw [hGcone, ← hray, htransport]
    simp only [Set.image_image, LinearIsometryEquiv.symm_apply_apply, Set.image_id']
  apply host_step_step2_strand_step2_terminal_counter_step5_row T hrow port hport l'
    (by simpa only [hportN] using hNl) u.2
    (by simpa only [hfacet, hleaf] using hread) hc G
    (by simpa only [hportι] using hG) rfl hx hlocalray

/-- Step 1 of the V4 proof of `host_step_step2_strand_step3_no_false_endpoint` (V4 3.6, Step 2):
"the terminal vertex". A nondegenerate segment has interval coordinates,
with its two endpoints as its entire relative boundary. -/
private theorem host_step_step2_strand_step3_no_false_endpoint_step1_segment
    (p q : E d) (hpq : p ≠ q) :
    ∃ (φ : ℝ →ᵃⁱ[ℝ] E d) (L : ℝ), 0 < L ∧ φ 0 = p ∧ φ L = q ∧
      segment ℝ p q = φ '' Icc 0 L ∧
      relint (segment ℝ p q) = φ '' Ioo 0 L ∧
      relfrontier (segment ℝ p q) = {p, q} := by
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
  have hrel : relint (segment ℝ p q) = φ '' Ioo 0 L := by
    rw [hseg, relint, φ.image_intrinsicInterior,
      host_step_step2_strand_step1_interval_relint 0 L hL]
  refine ⟨φ, L, hL, hφ0, hφL, hseg, hrel, ?_⟩
  have hclosed : IsClosed (segment ℝ p q) := by
    rw [hseg]
    exact (isCompact_Icc.image φ.continuous).isClosed
  rw [relfrontier, ← closure_diff_intrinsicInterior, hclosed.closure_eq]
  change segment ℝ p q \ relint (segment ℝ p q) = _
  rw [hrel, hseg, ← Set.image_diff φ.injective]
  have hd : Icc (0 : ℝ) L \ Ioo 0 L = {0, L} := by
    ext x
    simp only [mem_diff, mem_Icc, mem_Ioo, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hn⟩
      by_cases h : x = 0
      · exact Or.inl h
      · exact Or.inr (by push_neg at hn; have := hn (lt_of_le_of_ne hx.1 (Ne.symm h)); linarith)
    · rintro (rfl | rfl)
      · exact ⟨⟨le_rfl, hL.le⟩, by simp⟩
      · exact ⟨⟨hL.le, le_rfl⟩, by simp⟩
  rw [hd, Set.image_pair, hφ0, hφL]

/-- Step 1 of the V4 proof of `host_step_step2_strand_step3_no_false_endpoint` (V4 3.6, Step 2):
"given ... terminal vertex". Both endpoints of a listed edge are listed
vertices, including flat subdivisions of the boundary complex. -/
private theorem host_step_step2_strand_step3_no_false_endpoint_step1_vertex
    (A : S.ι) (e : PrototypeEdge S A) (p q : E d) (hpq : p ≠ q)
    (he : e.val.carrier = segment ℝ p q) :
    ∃ v : VertexName S A, v.val.carrier = {q} := by
  classical
  obtain ⟨φ, L, hL, hφ0, hφL, hseg, hrel, hfront⟩ :=
    host_step_step2_strand_step3_no_false_endpoint_step1_segment p q hpq
  obtain ⟨cs, hcs, hcover⟩ := (S.cx A).boundary_union e.val
    (Finset.mem_filter.mp e.property).1
  have hq : q ∈ ⋃ c ∈ cs, c.carrier := by
    rw [← hcover, he, hfront]
    simp
  obtain ⟨c, hc, hqc⟩ := mem_iUnion₂.mp hq
  have hsub : c.carrier ⊆ {p, q} := by
    intro x hx
    rw [← hfront, ← he, hcover]
    exact mem_iUnion₂.mpr ⟨c, hc, hx⟩
  have hfinite : c.carrier.Finite := (Set.toFinite {p, q}).subset hsub
  have hsingle : c.carrier.Subsingleton := by
    by_contra h
    exact (c.flat.connected.isPreconnected.infinite_of_nontrivial
      (Set.not_subsingleton_iff.mp h)) hfinite
  have hcq : c.carrier = {q} := Set.Subset.antisymm
    (fun x hx => mem_singleton_iff.mpr (hsingle hx hqc)) (singleton_subset_iff.mpr hqc)
  have hz : c.dim = 0 := by
    rw [← c.flat.dimension, cellDirection, hcq]
    simp [direction_affineSpan]
  exact ⟨⟨c, Finset.mem_filter.mpr ⟨hcs hc, hz⟩⟩, hcq⟩

/-- Step 1 of the V4 proof of `host_step_step2_strand_step3_no_false_endpoint` (V4 3.6, Step 2):
"the stratum ... is h or {p₀} or {p_N}". A listed cell contained in a
listed edge is that edge or is zero-dimensional. -/
private theorem host_step_step2_strand_step3_no_false_endpoint_step1_subcell
    (A : S.ι) (e : PrototypeEdge S A) (c : CellName S A)
    (hce : c.val.carrier ⊆ e.val.carrier) : c.val = e.val ∨ c.val.dim = 0 := by
  classical
  obtain ⟨⟨p, q⟩, hpq, he⟩ := edge_endpoints_exist (⟨A, e⟩ : EdgeName S)
  obtain ⟨φ, L, hL, hφ0, hφL, hseg, hrel, hfront⟩ :=
    host_step_step2_strand_step3_no_false_endpoint_step1_segment p q hpq
  obtain ⟨x, hx⟩ := c.val.flat.relint_nonempty
  have hxe : x ∈ e.val.carrier := hce (intrinsicInterior_subset hx)
  by_cases h : c.val = e.val
  · exact Or.inl h
  right
  have hnot : x ∉ relint e.val.carrier :=
    Set.disjoint_left.mp ((S.cx A).relint_disjoint c.val c.property e.val
      (Finset.mem_filter.mp e.property).1 h) hx
  have hbound : x ∈ relfrontier e.val.carrier := by
    rw [relfrontier, ← closure_diff_intrinsicInterior, e.val.flat.compact.isClosed.closure_eq]
    exact ⟨hxe, hnot⟩
  rw [he, hfront] at hbound
  have endpoint (y z : E d) (hyz : y ≠ z)
      (he' : e.val.carrier = segment ℝ y z) (hxz : x = z) : c.val.dim = 0 := by
    obtain ⟨v, hv⟩ := host_step_step2_strand_step3_no_false_endpoint_step1_vertex A e y z hyz he'
    have hxv : x ∈ relint v.val.carrier := by
      rw [hv, relint, intrinsicInterior_singleton]
      exact mem_singleton_iff.mpr hxz
    have hcv : c.val = v.val := by
      by_contra hh
      exact Set.disjoint_left.mp ((S.cx A).relint_disjoint c.val c.property v.val
        (Finset.mem_filter.mp v.property).1 hh) hx hxv
    rw [hcv]
    exact (Finset.mem_filter.mp v.property).2
  rcases hbound with hxp | hxq
  · exact endpoint q p hpq.symm (he.trans (segment_symm ℝ p q)) hxp
  · exact endpoint p q hpq he hxq

/-- Step 1 of the V4 proof of `host_step_step2_strand_step3_no_false_endpoint` (V4 3.6, Step 2):
"the stratum ... is a cell of g contained in h (as τ(e_m)=h)".
Incidence preservation of the honest stratum map gives the endpoint dichotomy. -/
private theorem host_step_step2_strand_step3_no_false_endpoint_step1_stratum
    (s : State P) (hs : s ∈ honestStates S P) (F : Cell d)
    (r : FacetRecord P) (hr : stateRecordAt s F = some r)
    (c : OrientedChain r.facet) (hc : c ∈ r.chains)
    (v : VertexName S r.ty)
    (hv : v.val.carrier ⊆ (host_step_edge ⟨r, c⟩).val.carrier) :
    ∃ z : ProviderCell r.incidence.val, r.tauAt v.val = some z.val.val ∧
      (z.val.val = ((P.flag r.incidence).flag.cell edgeIndex).val ∨ z.val.val.dim = 0) := by
  classical
  obtain ⟨U, q, rfl⟩ := hs
  unfold stateRecordAt at hr
  split at hr
  · rename_i hF
    change U.facetRecordOf P q ⟨F, hF⟩ = some r at hr
    unfold HonestSource.facetRecordOf at hr
    split at hr
    · contradiction
    · rename_i hf
      have hr' := Option.some.inj hr
      subst r
      let r := U.recordOf P q ⟨F, hF⟩ hf
      have hvf : v.val.carrier ⊆ F.carrier := hv.trans (r.chain_cell_subset c edgeIndex)
      let z := U.recordTau P q ⟨F, hF⟩ hf ⟨vertexCell v, hvf⟩
      have hvτ := record_tau_spec U P q ⟨F, hF⟩ hf ⟨vertexCell v, hvf⟩
      change U.providerPlacement P q ⟨F, hF⟩ hf '' z.val.val.carrier = _ at hvτ
      obtain ⟨heF, heτ, _⟩ := ((record_chains_spec U P q ⟨F, hF⟩ hf c).mp hc).1 edgeIndex
      have hmono := U.hierarchy.stratumMap_mono q ⟨F, hF⟩ hf (vertexCell v)
        (c.chain.val.cell edgeIndex) (U.cellInFacet_placed q ⟨F, hF⟩ ⟨vertexCell v, hvf⟩)
        heF hv
      have hsub : z.val.val.carrier ⊆ ((P.flag r.incidence).flag.cell edgeIndex).val.carrier := by
        intro x hx
        apply (U.providerPlacement P q ⟨F, hF⟩ hf).injective.mem_set_image.mp
        have hx' : U.providerPlacement P q ⟨F, hF⟩ hf x ∈
            U.providerPlacement P q ⟨F, hF⟩ hf '' z.val.val.carrier := ⟨x, hx, rfl⟩
        rw [hvτ] at hx'
        change U.providerPlacement P q ⟨F, hF⟩ hf x ∈
          U.providerPlacement P q ⟨F, hF⟩ hf ''
            ((P.flag (U.recordIncidence P q ⟨F, hF⟩ hf)).flag.cell edgeIndex).val.carrier
        rw [← heτ]
        exact Set.image_mono hmono hx'
      let e : PrototypeEdge S (S.child r.incidence.val.ty r.incidence.val.left).ty :=
        ⟨((P.flag r.incidence).flag.cell edgeIndex).val,
          Finset.mem_filter.mpr ⟨((P.flag r.incidence).flag.cell edgeIndex).property,
            (P.flag r.incidence).flag.dimension edgeIndex⟩⟩
      refine ⟨z, ?_, host_step_step2_strand_step3_no_false_endpoint_step1_subcell _ e z.val hsub⟩
      have hvc : v.val ∈ (S.cx q.2.val.ty).cells := (vertexCell v).property
      simp only [FacetRecord.tauAt, HonestSource.recordOf, dif_pos hvc, dif_pos hvf]
      rfl
  · contradiction

/-- Step 1 of the V4 proof of `host_step_step2_strand_step3_no_false_endpoint` (V4 3.6(F2), S6):
"u_s has an END slot ... with recorded header G′". A zero-dimensional
provider stratum in an honest leaf has its S6 header on the same vertex and facet. -/
private theorem host_step_step2_strand_step3_no_false_endpoint_step1_header
    (l : LeafType P) (F : Cell d) (r : FacetRecord P)
    (hr : leafRecord l F = some r) (v : VertexName S r.ty)
    (hv : v.val.carrier ⊆ r.facet.val.carrier)
    (z : ProviderCell r.incidence.val) (hz : r.tauAt v.val = some z.val.val)
    (hzero : z.val.val.dim = 0) :
    ∃ G : State.Header P, leafHeader l v.val r.facet.val = some G := by
  classical
  have hs : l.prePattern.state ∈ honestStates S P :=
    (prePattern_components_honest P l.prePattern
      ((certificate_components_honest P l.1.val l.1.property).1 l.2)).1
  obtain ⟨U, q, hs⟩ := hs
  have hr' : stateRecordAt (stateOf U P q) F = some r := by rw [hs]; exact hr
  unfold stateRecordAt at hr'
  split at hr'
  · rename_i hF
    change U.facetRecordOf P q ⟨F, hF⟩ = some r at hr'
    unfold HonestSource.facetRecordOf at hr'
    split at hr'
    · contradiction
    · rename_i hf
      have hrec := Option.some.inj hr'
      subst r
      have hvc : v.val ∈ (S.cx q.2.val.ty).cells := (vertexCell v).property
      have hvv : v.val ∈ (S.cx q.2.val.ty).vertices := v.property
      change v.val.carrier ⊆ F.carrier at hv
      change F ∈ (S.cx q.2.val.ty).facets at hF
      have hτ : (U.recordTau P q ⟨F, hF⟩ hf ⟨vertexCell v, hv⟩).val.val = z.val.val := by
        simpa only [FacetRecord.tauAt, HonestSource.recordOf, dif_pos hvc, dif_pos hv,
          Option.some.injEq] using hz
      refine ⟨U.headerOf P q ⟨F, hF⟩ hf v, ?_⟩
      unfold leafHeader
      rw [← hs]
      change (if hv' : v.val ∈ (S.cx q.2.val.ty).vertices then
        if hf' : F ∈ (S.cx q.2.val.ty).facets then
          U.headerRecordOf P q ⟨v.val, hv'⟩ ⟨F, hf'⟩ else none else none) = _
      simp only [dif_pos hvv, dif_pos hF, HonestSource.headerRecordOf,
        dif_pos hv, dif_neg hf]
      change (if (U.recordTau P q ⟨F, hF⟩ hf ⟨vertexCell v, hv⟩).val.val.dim = 0 then
        some (U.headerOf P q ⟨F, hF⟩ hf v) else none) = _
      rw [hτ, hzero, if_pos rfl]
  · contradiction

/-- Step 1 of the V4 proof of `host_step_step2_strand_step3_no_false_endpoint` (V4 3.6, Step 2):
"If it is h, u_m has a CONT slot ... If it is a vertex ... the sequence stops."
This is the local slot alternative for one honest active port, before using
any information about a decoded block or the position of the endpoint. -/
private theorem host_step_step2_strand_step3_no_false_endpoint_step1_slots
    (l : LeafType P) (F : Cell d) (r : FacetRecord P)
    (hr : leafRecord l F = some r) (c : OrientedChain r.facet) (hc : c ∈ r.chains) :
    (∃ j : ContSlot l, j.record = r ∧ j.edge.val = (host_step_edge ⟨r, c⟩).val) ∨
      ∃ j : EndSlot l, j.record = r ∧
        vertexPoint j.vertex = (r.endpoints (host_step_edge ⟨r, c⟩)).2 := by
  classical
  let e := host_step_edge (⟨r, c⟩ : host_step_Chain P)
  have hends : (r.endpoints e).1 ≠ (r.endpoints e).2 ∧
      e.val.carrier = segment ℝ (r.endpoints e).1 (r.endpoints e).2 := by
    have he := Classical.choose_spec (edge_endpoints_exist (⟨r.ty, e⟩ : EdgeName S))
    unfold FacetRecord.endpoints
    split
    · exact he
    · exact ⟨he.1.symm, he.2.trans (segment_symm ℝ _ _)⟩
  obtain ⟨v, hv⟩ := host_step_step2_strand_step3_no_false_endpoint_step1_vertex
    r.ty e (r.endpoints e).1 (r.endpoints e).2 hends.1 hends.2
  have hvpoint : vertexPoint v = (r.endpoints e).2 := by
    have h : vertexPoint v ∈ v.val.carrier := by rw [vertexPoint_spec]; simp
    simpa only [hv, mem_singleton_iff] using h
  have hve : v.val.carrier ⊆ e.val.carrier := by
    rw [hv, hends.2]
    exact singleton_subset_iff.mpr (right_mem_segment ℝ _ _)
  have hvf : v.val.carrier ⊆ r.facet.val.carrier := hve.trans (r.chain_cell_subset c edgeIndex)
  obtain ⟨hty, hf⟩ := host_step_step1_seed_step6_readout l F r hr
  let f : FacetName S l.prototype := ⟨r.facet.val, hty ▸ r.facet.property⟩
  have hrf : leafRecord l f.val = some r := by rw [show f.val = F from hf]; exact hr
  obtain ⟨packet, hpacket⟩ := host_step_step1_seed_step6_packet l f.val r hrf
  have hs : l.prePattern.state ∈ honestStates S P :=
    (prePattern_components_honest P l.prePattern
      ((certificate_components_honest P l.1.val l.1.property).1 l.2)).1
  obtain ⟨z, hz, hez | hzero⟩ :=
    host_step_step2_strand_step3_no_false_endpoint_step1_stratum
      l.prePattern.state hs F r hr c hc v hve
  · let j : ContSlot l := {
      facet := f
      record := r
      record_eq := hrf
      type_eq := hty
      facet_eq := rfl
      edge := e
      active := ⟨c, hc, rfl⟩
      vertex := v
      onFacet := hvf
      terminal := hvpoint
      tau_edge := hz.trans (congrArg some hez)
      packet := packet
      packet_eq := hpacket }
    exact Or.inl ⟨j, rfl, rfl⟩
  · obtain ⟨G, hG⟩ := host_step_step2_strand_step3_no_false_endpoint_step1_header
      l F r hr v hvf z hz hzero
    let j : EndSlot l := {
      facet := f
      record := r
      record_eq := hrf
      type_eq := hty
      facet_eq := rfl
      vertex := v
      onFacet := hvf
      providerVertex := z
      tau_vertex := hz
      provider_zero := hzero
      header := G
      header_eq := hG
      packet := packet
      packet_eq := hpacket }
    exact Or.inr ⟨j, rfl, hvpoint⟩

/-- Step 2 of the V4 proof of `host_step_step2_strand_step3_no_false_endpoint` (V4 3.6(F2), S6):
"its recorded header G′ ... is realised by an honest configuration".
The header records the tangent cone of this very record's primitive facet. -/
private theorem host_step_step2_strand_step3_no_false_endpoint_step2_header_cone
    (l : LeafType P) (F : Cell d) (r : FacetRecord P)
    (hr : leafRecord l F = some r) (v : VertexName S r.ty)
    (hv : v.val.carrier ⊆ r.facet.val.carrier) (H : State.Header P)
    (hH : leafHeader l v.val F = some H) :
    ∃ G : Set (E d), H.primitiveCones r.incidence = some G := by
  classical
  have hs : l.prePattern.state ∈ honestStates S P :=
    (prePattern_components_honest P l.prePattern
      ((certificate_components_honest P l.1.val l.1.property).1 l.2)).1
  obtain ⟨U, q, hs⟩ := hs
  have hr' : stateRecordAt (stateOf U P q) F = some r := by rw [hs]; exact hr
  unfold stateRecordAt at hr'
  split at hr'
  · rename_i hF
    change U.facetRecordOf P q ⟨F, hF⟩ = some r at hr'
    unfold HonestSource.facetRecordOf at hr'
    split at hr'
    · contradiction
    · rename_i hf
      have hrec := Option.some.inj hr'
      subst r
      have hvv : v.val ∈ (S.cx q.2.val.ty).vertices := v.property
      change v.val.carrier ⊆ F.carrier at hv
      change F ∈ (S.cx q.2.val.ty).facets at hF
      unfold leafHeader at hH
      rw [← hs] at hH
      change (if hv' : v.val ∈ (S.cx q.2.val.ty).vertices then
        if hf' : F ∈ (S.cx q.2.val.ty).facets then
          U.headerRecordOf P q ⟨v.val, hv'⟩ ⟨F, hf'⟩ else none else none) = some H at hH
      simp only [dif_pos hvv, dif_pos hF, HonestSource.headerRecordOf,
        dif_pos hv, dif_neg hf] at hH
      split at hH
      · have hheader : U.headerOf P q ⟨F, hF⟩ hf v = H := Option.some.inj hH
        subst H
        let ι := U.recordIncidence P q ⟨F, hF⟩ hf
        have hty : ι.val.ty = (U.hierarchy.birthParent q ⟨F, hF⟩ hf).2.val.ty :=
          (P.canonical_spec (U.hierarchy.providerIncidence q ⟨F, hF⟩ hf)).1.symm.trans
            (U.hierarchy.providerIncidence_spec q ⟨F, hF⟩ hf).1
        have hp : q.2.val.prototypeFrame q.1 (vertexPoint v) ∈
            relint (q.2.val.cell q.1 (vertexCell v).val) := by
          simp only [FramedNode.cell, vertexCell, vertexPoint_spec, Set.image_singleton,
            relint, intrinsicInterior_singleton, mem_singleton_iff]
        have hstratum := U.hierarchy.stratumMap_spec q ⟨F, hF⟩ hf (vertexCell v)
          (U.cellInFacet_placed q ⟨F, hF⟩ ⟨vertexCell v, hv⟩)
        have hprovider := hstratum.2.2 (intrinsicInterior_subset (hstratum.1 hp))
        rw [← record_provider_carrier U P q ⟨F, hF⟩ hf] at hprovider
        change ∃ G, (U.headerOf P q ⟨F, hF⟩ hf v).primitiveCones ι = some G
        unfold HonestSource.headerOf
        dsimp only
        rw [if_pos ⟨hty, hprovider⟩]
        exact ⟨_, rfl⟩
      · contradiction
  · contradiction

/-- Step 2 of the V4 proof of `host_step_step2_strand_step3_no_false_endpoint` (V4 3.6(F1), 3.6(F2)):
"the composite displacements from v backwards along e_s, then into relint s₂, ..."
enter the recorded parent cone. Their intermediate facet points accumulate
at v in both the known facet and the recorded primitive-facet cone. This is
only the local geometric overlap; it asserts no actual template or leaf readout. -/
private theorem host_step_step2_strand_step3_no_false_endpoint_step2_sector_patch
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) (u : host_step_Port C)
    (hu : host_step_portValid Y n (proposedSibling D B hB f a)
      a.record.incidence (!a.record.sideIndex) u)
    (hsub : host_step_portEdge u ⊆ host_step_flagEdge (proposedSibling D B hB f a) n
      a.record.incidence (!a.record.sideIndex))
    (hterminal : (host_step_portEnds u).2 ∈
      relint (host_step_flagEdge (proposedSibling D B hB f a) n
        a.record.incidence (!a.record.sideIndex)))
    (j : EndSlot (compilerLeaf C u.1)) (hrecord : j.record = u.2.1)
    (hpoint : Compiler.endVertex (compilerFrame C u.1) j = (host_step_portEnds u).2) :
    ∃ G : Set (E d), j.header.primitiveCones a.record.incidence = some G ∧
      affineSpan ℝ (B.node.cell n f.val) =
        affineSpan ℝ ((fun w => (host_step_portEnds u).2 +
          (compilerFrame C u.1).linearIsometryEquiv w) '' G) ∧
      (host_step_portEnds u).2 ∈ closure
        (relint (B.node.cell n f.val) ∩
          relint ((fun w => (host_step_portEnds u).2 +
            (compilerFrame C u.1).linearIsometryEquiv w) '' G) ∩
          interior (Compiler.endSector (compilerFrame C u.1) j)) := by
  obtain ⟨G, hG⟩ := host_step_step2_strand_step3_no_false_endpoint_step2_header_cone
    (compilerLeaf C u.1) j.facet.val j.record j.record_eq j.vertex j.onFacet j.header j.header_eq
  have hι : j.record.incidence = a.record.incidence :=
    (congrArg FacetRecord.incidence hrecord).trans hu.2.2.2.2.1
  refine ⟨G, by simpa only [hι] using hG, ?_⟩
  -- Realize this header and the active chain in the same honest leaf source.
  -- The backward edge displacement and the successive recorded coface sides
  -- enter both facets, and their common facet patch lies inside the parent cone.
  sorry

/-- Step 3 of the V4 proof of `host_step_step2_strand_step3_no_false_endpoint` (V4 3.6(2b), 3.3, 1.8):
"among them is a tile t_B ... with a facet piece in f whose closure contains v";
"the template geometry identifies t_B as a port". Hereditary facet coverage
and finiteness select one piece from an accumulating primitive-facet patch.
The conclusion identifies its exact geometric port and label, without applying (E1). -/
private theorem host_step_step2_strand_step3_no_false_endpoint_step3_facet_port
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (B : Block Y n)
    (f : FacetName S B.node.ty) (l : LeafType P) (j : EndSlot l)
    (φ : Iso d) (T : EndTemplate j) (hactual : TemplateOccurs C Y φ T.configuration)
    (ι : P.Incidence) (G : Set (E d)) (hG : j.header.primitiveCones ι = some G)
    (hspan : affineSpan ℝ (B.node.cell n f.val) =
      affineSpan ℝ ((fun w => Compiler.endVertex φ j + φ.linearIsometryEquiv w) '' G))
    (hnear : Compiler.endVertex φ j ∈ closure
      (relint (B.node.cell n f.val) ∩
        relint ((fun w => Compiler.endVertex φ j + φ.linearIsometryEquiv w) '' G) ∩
        interior (Compiler.endSector φ j))) :
    ∃ (t : PlacedMarkedTile (systemM S P C)) (g : FacetName S (tileNode t).ty)
      (v : VertexName S (tileNode t).ty),
      Parser.IsFacetPiece Y n B.node f t g ∧ v.val.carrier ⊆ g.val.carrier ∧
        compilerFrame C t (vertexPoint v) = Compiler.endVertex φ j ∧
        ∃ b ∈ T.geometry.primitivePorts,
          (b.tile, compilerLeaf C t) ∈ T.configuration.tiles ∧
          b.facet.val = g.val ∧ b.vertex.val = v.val ∧
          compilerFrame C t = b.tile.frame.trans φ := by
  -- In the source realizing T.geometry, a small neighbourhood of the apex
  -- identifies G with the first-generation facet. In the common affine span,
  -- the intersection is relatively open. Apply finite hereditary facet covers
  -- on both sides and actual-tile uniqueness, then select a pair accumulating
  -- at the apex. Its common native facet is the required primitive port.
  sorry

/-- Step 3 of the V4 proof of `host_step_step2_strand_step3_no_false_endpoint` (V4 3.6(2b), E1):
"Row (E1) requires τ_{t_B}({v}) = {p′}, a vertex." The exact port-label
identification transfers the END row to the actual native facet piece. -/
private theorem host_step_step2_strand_step3_no_false_endpoint_step3_vertex_readout
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (B : Block Y n)
    (f : FacetName S B.node.ty) (l : LeafType P) (j : EndSlot l)
    (φ : Iso d) (T : EndTemplate j) (hrow : endRow T)
    (hactual : TemplateOccurs C Y φ T.configuration)
    (ι : P.Incidence) (G : Set (E d)) (hG : j.header.primitiveCones ι = some G)
    (hspan : affineSpan ℝ (B.node.cell n f.val) =
      affineSpan ℝ ((fun w => Compiler.endVertex φ j + φ.linearIsometryEquiv w) '' G))
    (hnear : Compiler.endVertex φ j ∈ closure
      (relint (B.node.cell n f.val) ∩
        relint ((fun w => Compiler.endVertex φ j + φ.linearIsometryEquiv w) '' G) ∩
        interior (Compiler.endSector φ j))) :
    ∃ (t : PlacedMarkedTile (systemM S P C)) (g : FacetName S (tileNode t).ty)
      (v : VertexName S (tileNode t).ty),
      Parser.IsFacetPiece Y n B.node f t g ∧ v.val.carrier ⊆ g.val.carrier ∧
        compilerFrame C t (vertexPoint v) = Compiler.endVertex φ j ∧
        ∃ r : FacetRecord P, leafRecord (compilerLeaf C t) g.val = some r ∧
          ∃ z : Cell d, r.tauAt v.val = some z ∧ z.dim = 0 := by
  obtain ⟨t, g, v, hpiece, hv, hvp, b, hb, hlabel, hfacet, hvertex, _⟩ :=
    host_step_step2_strand_step3_no_false_endpoint_step3_facet_port
      Y n B f l j φ T hactual ι G hG hspan hnear
  obtain ⟨r, hr, _, _, hτ, _⟩ := hrow.1.1 b hb (compilerLeaf C t) hlabel
  exact ⟨t, g, v, hpiece, hv, hvp, r, hfacet ▸ hr,
    b.providerVertex.val.val, hvertex ▸ hτ, b.provider_zero⟩

/-- Step 4 of the V4 proof of `host_step_step2_strand_step3_no_false_endpoint` (V4 3.6(2b)):
"the cell ... containing v in its relative interior". Relative interiors
commute with the full affine frames used in the restriction rule. -/
private theorem host_step_step2_strand_step3_no_false_endpoint_step4_relint_image
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

/-- Step 4 of the V4 proof of `host_step_step2_strand_step3_no_false_endpoint` (V4 3.6(2b), 2.3):
"by (I2) ... τ_{t_B}({v}) = τ_f(h) = h". On an actual native facet
piece of the known block, a listed vertex in the open age-one flag edge has
a one-dimensional provider stratum. This concerns only restriction on B's side. -/
private theorem host_step_step2_strand_step3_no_false_endpoint_step4_restriction
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) (p : E d)
    (hp : p ∈ relint (host_step_flagEdge (proposedSibling D B hB f a) n
      a.record.incidence (!a.record.sideIndex)))
    (t : PlacedMarkedTile (systemM S P C)) (g : FacetName S (tileNode t).ty)
    (v : VertexName S (tileNode t).ty) (hpiece : Parser.IsFacetPiece Y n B.node f t g)
    (hv : v.val.carrier ⊆ g.val.carrier) (hvp : compilerFrame C t (vertexPoint v) = p) :
    ∃ r : FacetRecord P, leafRecord (compilerLeaf C t) g.val = some r ∧
      ∃ z : Cell d, r.tauAt v.val = some z ∧ z.dim = 1 := by
  classical
  obtain ⟨U, hU, hs⟩ := host_step_step1_seed_step3_restricted_header_step1_realise
    (D.blockState B hB) (hD.I1 B hB).1 B.node n
    (hD.I1 B hB).2.1 (hD.I1 B hB).2.2
  let q : U.Node := ⟨n, ⟨B.node, hU⟩⟩
  have hread : U.facetRecordOf P q f = some a.record := by
    have h := a.readout
    rw [← hs] at h
    simpa only [stateRecordAt, stateOf, dif_pos f.property] using h
  have hf : ¬ U.hierarchy.IsFault q f := by
    intro hf
    simp only [HonestSource.facetRecordOf, dif_pos hf] at hread
    contradiction
  have hrecord : U.recordOf P q f hf = a.record := by
    simpa only [HonestSource.facetRecordOf, dif_neg hf, Option.some.injEq] using hread
  have hoff : (U.hierarchy.firstProvider q f hf).1 = 0 := by
    have ha := a.age_one
    rw [← hrecord] at ha
    change min (U.hierarchy.age q f hf) P.C = 1 at ha
    have := P.C_gt_one
    have := (U.hierarchy.birthHeight_age_spec q f hf).2.1
    omega
  have hserv : U.hierarchy.servingChild q f hf = q := by
    simp only [CoherentHierarchy.servingChild, hoff, CoherentHierarchy.ancestor,
      Function.iterate_zero, id_eq]
  have hrole : U.hierarchy.nodeRole q = firstRole D B hB := by
    have h := congrArg (fun s : State P => s.address ⟨0, P.k_pos⟩) hs
    simpa only [stateOf, CoherentHierarchy.ancestor, Function.iterate_zero,
      id_eq, firstRole] using h
  have hparent : (U.hierarchy.parentNode q).2.val = proposedParent D B hB := by
    rw [host_step_step1_seed_step3_restricted_header_step4_parent, hrole]
    rfl
  obtain ⟨r, hr, w, htile⟩ := hpiece.2.1
  have hrn : r = n := by omega
  subst r
  have hreal {k : ℕ} (hk : k = n) (hN : B.node ∈ D.geometry.nodes k)
      (hU' : B.node ∈ U.hierarchy.nodes k) :
      stateOf U P ⟨k, ⟨B.node, hU'⟩⟩ = D.stateAt k B.node hN := by
    subst k
    exact hs
  have hnode {k : ℕ} (hk : k = n) (hU' : B.node ∈ U.hierarchy.nodes k) :
      (⟨k, ⟨B.node, hU'⟩⟩ : U.Node) = q := by
    subst k
    rfl
  have hdesc : ∃ (htD : tileNode t ∈ D.geometry.nodes 0)
      (htU : tileNode t ∈ U.hierarchy.nodes 0),
      stateOf U P ⟨0, ⟨tileNode t, htU⟩⟩ = D.stateAt 0 (tileNode t) htD ∧
        U.hierarchy.ancestor ⟨0, ⟨tileNode t, htU⟩⟩ n = q := by
    obtain ⟨htD, htU, htstate, hanc⟩ :=
      host_step_step1_seed_step3_restricted_header_step2_descent D hD U 0 n B.node
        (by simpa only [Nat.zero_add] using D.geometry.root_mem B hB)
        (by simpa only [Nat.zero_add] using hU)
        (hreal (Nat.zero_add n) _ _) w
    rw [htile]
    exact ⟨htD, htU, htstate, hanc.trans (hnode (Nat.zero_add n) _)⟩
  obtain ⟨htD, htU, htstate, hanc⟩ := hdesc
  let c : U.Node := ⟨0, ⟨tileNode t, htU⟩⟩
  have hleaf : stateOf U P c = (compilerLeaf C t).prePattern.state :=
    htstate.trans (hD.I2.2 (tileNode t) htD t hpiece.1 rfl)
  obtain ⟨hg, hprovider, hbirth⟩ := U.hierarchy.provider_inherited q c n hanc f g hf hpiece.2.2
  have hbirth' : U.hierarchy.birthParent c g hg = U.hierarchy.parentNode q := by
    rw [hbirth, CoherentHierarchy.birthParent, hserv]
  have hheight : U.hierarchy.birthHeight c g hg = n + 1 :=
    congrArg (fun z : U.Node => z.1) hbirth'
  have hι : U.recordIncidence P c g hg = a.record.incidence :=
    (host_step_step1_seed_step3_restricted_header_step3_incidence P U c q g f hg hf
      hbirth hprovider).trans (congrArg FacetRecord.incidence hrecord)
  have hframe : U.providerPlacement P c g hg =
      host_step_flagFrame (proposedSibling D B hB f a) n a.record.incidence
        (!a.record.sideIndex) := by
    rw [HonestSource.providerPlacement, hheight, hbirth', hparent, hι]
    exact (host_step_step1_seed_step1_flag_frame (proposedParent D B hB) n
      a.record.incidence (!a.record.sideIndex)).symm
  have hflag : host_step_flagEdge (proposedSibling D B hB f a) n
      a.record.incidence (!a.record.sideIndex) =
      U.providerPlacement P c g hg ''
        ((P.flag (U.recordIncidence P c g hg)).flag.cell edgeIndex).val.carrier := by
    rw [hframe, hι, (P.flag a.record.incidence).edge_eq,
      host_step_step2_strand_step1_flag_segment]
    exact (image_segment ℝ
      (host_step_flagFrame (proposedSibling D B hB f a) n a.record.incidence
        (!a.record.sideIndex)).toAffineMap _ _).symm
  let z := U.recordTau P c g hg ⟨vertexCell v, hv⟩
  have hpoint : c.2.val.prototypeFrame c.1 (vertexPoint v) = p := hvp
  have hpv : p ∈ relint (c.2.val.cell c.1 (vertexCell v).val) := by
    simp only [FramedNode.cell, vertexCell, vertexPoint_spec, Set.image_singleton,
      relint, intrinsicInterior_singleton, hpoint, mem_singleton_iff]
  have hpz := (U.hierarchy.stratumMap_spec c g hg (vertexCell v)
    (U.cellInFacet_placed c g ⟨vertexCell v, hv⟩)).1 hpv
  have hτ := record_tau_spec U P c g hg ⟨vertexCell v, hv⟩
  change U.providerPlacement P c g hg '' z.val.val.carrier = _ at hτ
  rw [← hτ, host_step_step2_strand_step3_no_false_endpoint_step4_relint_image] at hpz
  rw [hflag, host_step_step2_strand_step3_no_false_endpoint_step4_relint_image] at hp
  obtain ⟨x, hx, hxp⟩ := hpz
  have hxe : x ∈ relint ((P.flag (U.recordIncidence P c g hg)).flag.cell edgeIndex).val.carrier := by
    rw [← hxp] at hp
    exact (U.providerPlacement P c g hg).injective.mem_set_image.mp hp
  have hze : z.val.val = ((P.flag (U.recordIncidence P c g hg)).flag.cell edgeIndex).val := by
    by_contra hne
    exact Set.disjoint_left.mp ((S.cx _).relint_disjoint z.val.val z.val.property
      _ ((P.flag (U.recordIncidence P c g hg)).flag.cell edgeIndex).property hne) hx hxe
  refine ⟨U.recordOf P c g hg, ?_, z.val.val, ?_, ?_⟩
  · unfold leafRecord
    rw [← hleaf]
    simp only [stateRecordAt, stateOf, c, dif_pos g.property,
      HonestSource.facetRecordOf, dif_neg hg]
  · have hvc : v.val ∈ (S.cx (tileNode t).ty).cells := (vertexCell v).property
    simp only [FacetRecord.tauAt, HonestSource.recordOf, c, dif_pos hvc, dif_pos hv]
    rfl
  · rw [hze]
    exact (P.flag (U.recordIncidence P c g hg)).flag.dimension edgeIndex

/-- Step 3 of the V4 proof of `host_step_step2_strand` (V4 3.6(2b)):
"No false interior endpoint". An END record at an interior point would
force a B-side tile's stratum to be a vertex by (E1), while (I2) restricts
B's age-one stratum there to h. Thus the terminal vertex has a CONT slot
with exactly this port's record and edge. -/
private theorem host_step_step2_strand_step3_no_false_endpoint
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f)
    (u : host_step_Port C)
    (hu : host_step_portValid Y n (proposedSibling D B hB f a)
      a.record.incidence (!a.record.sideIndex) u)
    (hsub : host_step_portEdge u ⊆ host_step_flagEdge (proposedSibling D B hB f a) n
      a.record.incidence (!a.record.sideIndex))
    (hterminal : (host_step_portEnds u).2 ∈
      relint (host_step_flagEdge (proposedSibling D B hB f a) n
        a.record.incidence (!a.record.sideIndex))) :
    ∃ j : ContSlot (compilerLeaf C u.1),
      j.record = u.2.1 ∧ j.edge.val = (host_step_edge u.2).val := by
  classical
  rcases host_step_step2_strand_step3_no_false_endpoint_step1_slots
      (compilerLeaf C u.1) u.2.1.facet.val u.2.1 hu.2.1 u.2.2 hu.2.2.2.1 with
      hcont | ⟨j, hjrecord, hjpoint⟩
  · exact hcont
  have hpoint : Compiler.endVertex (compilerFrame C u.1) j = (host_step_portEnds u).2 :=
    congrArg (compilerFrame C u.1) hjpoint
  obtain ⟨G, hG, hspan, hnear⟩ :=
    host_step_step2_strand_step3_no_false_endpoint_step2_sector_patch
      Y n D hD B hB f a u hu hsub hterminal j hjrecord hpoint
  obtain ⟨θ, hθ, _, hactual⟩ := compiler_events C Y hY u.1 hu.1 (.end_ j)
  obtain ⟨T, rfl, hrow⟩ := hθ
  obtain ⟨t, g, v, hpiece, hv, hvp, r, hr, z, hz, hzero⟩ :=
    host_step_step2_strand_step3_no_false_endpoint_step3_vertex_readout
      Y n B f (compilerLeaf C u.1) j (compilerFrame C u.1) T hrow hactual
      a.record.incidence G hG (by simpa only [hpoint] using hspan)
      (by simpa only [hpoint] using hnear)
  obtain ⟨r', hr', z', hz', hone⟩ :=
    host_step_step2_strand_step3_no_false_endpoint_step4_restriction
      Y n D hD B hB f a (host_step_portEnds u).2 hterminal
      t g v hpiece hv (hvp.trans hpoint)
  have hrr : r = r' := Option.some.inj (hr.symm.trans hr')
  subst r'
  have hzz : z = z' := Option.some.inj (hz.symm.trans hz')
  rw [← hzz, hzero] at hone
  contradiction

/-- Step 1 of the V4 proof of `host_step_step2_strand_step4_continue` (V4 3.6, Step 2):
"same affine spans, orientation and sides". For one consecutive pair of
flag cells, refinement preserves its local side: both cells have the provider
cells' affine spans and their relative interiors lie in the respective provider
relative interiors. The codimension-one half-space structure in V4 3.6(F1)
then identifies the tangent sides, after the full affine placements. -/
private theorem host_step_step2_strand_step4_continue_step1_coface_side
    {A A' : S.ι} (F : FacetFlag S A) (G : FacetFlag S A')
    (φ ψ : E d ≃ᵃ[ℝ] E d) (k : FlagStep d)
    (hlow : relint (φ '' (F.cell ⟨k.val, k.property.1, by omega⟩).val.carrier) ⊆
      relint (ψ '' (G.cell ⟨k.val, k.property.1, by omega⟩).val.carrier))
    (hhigh : relint (φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier) ⊆
      relint (ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier))
    (hspanlow : affineSpan ℝ (φ '' (F.cell ⟨k.val, k.property.1, by omega⟩).val.carrier) =
      affineSpan ℝ (ψ '' (G.cell ⟨k.val, k.property.1, by omega⟩).val.carrier))
    (hspanhigh : affineSpan ℝ (φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier) =
      affineSpan ℝ (ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier)) :
    φ.linear '' flagSide F k = ψ.linear '' flagSide G k := by
  let low : FlagIndex d := ⟨k.val, k.property.1, by omega⟩
  let high : FlagIndex d := ⟨k.val + 1, by omega, k.property.2⟩
  let x := φ (cellAnchor (F.cell low).val)
  have hx : x ∈ relint (ψ '' (G.cell low).val.carrier) := by
    apply hlow
    rw [host_step_step1_seed_step5_trace_step3_relint_image]
    exact Set.mem_image_of_mem φ (cellAnchor_mem _)
  have hclosed (χ : E d ≃ᵃ[ℝ] E d) (e : Cell d) :
      closure (relint (χ '' e.carrier)) = χ '' e.carrier := by
    rw [host_step_step1_seed_step5_trace_step3_relint_image]
    change closure (χ.toHomeomorphOfFiniteDimensional '' relint e.carrier) =
      χ.toHomeomorphOfFiniteDimensional '' e.carrier
    rw [← Homeomorph.image_closure, e.flat.regularClosed]
  have hsub : φ '' (F.cell high).val.carrier ⊆ ψ '' (G.cell high).val.carrier := by
    simpa only [hclosed] using closure_mono hhigh
  have hF : tangentCone (φ '' (F.cell high).val.carrier) x =
      φ.linear '' flagSide F k := by
    rw [host_step_step1_seed_step8_transport_step1_tangent_image]
    rfl
  have hG : tangentCone (ψ '' (G.cell high).val.carrier) x =
      ψ.linear '' flagSide G k := by
    rw [host_step_step1_seed_step5_trace_step3_relint_image] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [← hxy, host_step_step1_seed_step8_transport_step1_tangent_image]
    exact congrArg (fun K : Set (E d) => ψ.linear '' K)
      (host_step_step1_seed_step8_transport_step4_coface G k y hy)
  rw [← hF, ← hG]
  apply Set.Subset.antisymm
  · exact host_step_step1_seed_step5_trace_step1_tangent_mono hsub x
  · -- Both cones are nontrivial closed half-spaces in the common upper
    -- direction space, with the common lower direction space as wall.
    -- The forward inclusion therefore forces their inward sides to agree.
    sorry

/-- Step 1 of the V4 proof of `host_step_step2_strand_step4_continue` (V4 3.6, Step 2):
"active chain in the same positioned flag (same affine spans, orientation and sides)".
Every active chain of an honest record has the provider's successive coface
sides. Cancelling the common source frame compares any two such chains. -/
private theorem host_step_step2_strand_step4_continue_step1_sides
    (s : State P) (hs : s ∈ honestStates S P) (F : Cell d)
    (r : FacetRecord P) (hr : stateRecordAt s F = some r)
    (c c' : OrientedChain r.facet) (hc : c ∈ r.chains) (hc' : c' ∈ r.chains) :
    ∀ k, flagSide c.chain.val k = flagSide c'.chain.val k := by
  classical
  obtain ⟨U, q, rfl⟩ := hs
  unfold stateRecordAt at hr
  split at hr
  · rename_i hF
    change U.facetRecordOf P q ⟨F, hF⟩ = some r at hr
    unfold HonestSource.facetRecordOf at hr
    split at hr
    · contradiction
    · rename_i hf
      have hr' := Option.some.inj hr
      subst r
      let φ := q.2.val.prototypeFrame q.1
      let ψ := U.providerPlacement P q ⟨F, hF⟩ hf
      let G := (P.flag (U.recordIncidence P q ⟨F, hF⟩ hf)).flag
      have hside (a : OrientedChain (⟨F, hF⟩ : FacetName S q.2.val.ty))
          (ha : a ∈ (U.recordOf P q ⟨F, hF⟩ hf).chains) (k : FlagStep d) :
          φ.linear '' flagSide a.chain.val k = ψ.linear '' flagSide G k := by
        have hactive := (record_chains_spec U P q ⟨F, hF⟩ hf a).mp ha
        have hfit (i : FlagIndex d) :
            relint (φ '' (a.chain.val.cell i).val.carrier) ⊆
                relint (ψ '' (G.cell i).val.carrier) ∧
              affineSpan ℝ (φ '' (a.chain.val.cell i).val.carrier) =
                affineSpan ℝ (ψ '' (G.cell i).val.carrier) := by
          obtain ⟨hsub, hstratum, hspan⟩ := hactive.1 i
          refine ⟨?_, hspan⟩
          have h := (U.hierarchy.stratumMap_spec q ⟨F, hF⟩ hf
            (a.chain.val.cell i) hsub).1
          simpa only [hstratum] using h
        exact host_step_step2_strand_step4_continue_step1_coface_side a.chain.val G φ ψ k
          (hfit _).1 (hfit _).1 (hfit _).2 (hfit _).2
      intro k
      exact φ.linear.injective.image_injective ((hside c hc k).trans (hside c' hc' k).symm)
  · contradiction

/-- Step 2 of the V4 proof of `host_step_step2_strand_step4_continue` (V4 3.6, Step 2):
"same affine spans, orientation and sides". The stratum test in an honest
record gives every active chain the provider's affine spans; on a common
edge the endpoint readout fixes the oriented vector as well. -/
private theorem host_step_step2_strand_step4_continue_step2_chains
    (s : State P) (hs : s ∈ honestStates S P) (F : Cell d)
    (r : FacetRecord P) (hr : stateRecordAt s F = some r)
    (c c' : OrientedChain r.facet) (hc : c ∈ r.chains) (hc' : c' ∈ r.chains)
    (he : (c.chain.val.cell edgeIndex).val = (c'.chain.val.cell edgeIndex).val) :
    (∀ k, affineSpan ℝ (c.chain.val.cell k).val.carrier =
      affineSpan ℝ (c'.chain.val.cell k).val.carrier) ∧
    (∀ k, flagSide c.chain.val k = flagSide c'.chain.val k) ∧
    chainVector c = chainVector c' := by
  refine ⟨?_, host_step_step2_strand_step4_continue_step1_sides s hs F r hr c c' hc hc',
    ?_⟩
  · classical
    obtain ⟨U, q, rfl⟩ := hs
    unfold stateRecordAt at hr
    split at hr
    · rename_i hF
      change U.facetRecordOf P q ⟨F, hF⟩ = some r at hr
      unfold HonestSource.facetRecordOf at hr
      split at hr
      · contradiction
      · rename_i hf
        have hr' := Option.some.inj hr
        subst r
        intro k
        have h := ((record_chains_spec U P q ⟨F, hF⟩ hf c).mp hc).1 k
        have h' := ((record_chains_spec U P q ⟨F, hF⟩ hf c').mp hc').1 k
        obtain ⟨_, _, hspan⟩ := h
        obtain ⟨_, _, hspan'⟩ := h'
        have hsame := hspan.trans hspan'.symm
        change affineSpan ℝ (q.2.val.prototypeFrame q.1 '' _) =
          affineSpan ℝ (q.2.val.prototypeFrame q.1 '' _) at hsame
        have hpull := congrArg
          (fun A : AffineSubspace ℝ (E d) =>
            A.map (q.2.val.prototypeFrame q.1).symm.toAffineMap) hsame
        dsimp only at hpull
        rw [AffineSubspace.map_span, AffineSubspace.map_span] at hpull
        simpa only [AffineEquiv.coe_toAffineMap, Set.image_image,
          AffineEquiv.symm_apply_apply, Set.image_id'] using hpull
    · contradiction
  · have he' : host_step_edge (⟨r, c⟩ : host_step_Chain P) = host_step_edge ⟨r, c'⟩ :=
      Subtype.ext he
    rw [← host_step_step2_strand_step1_endpoint_vector s hs F r hr c hc,
      ← host_step_step2_strand_step1_endpoint_vector s hs F r hr c' hc', he']

/-- Step 3 of the V4 proof of `host_step_step2_strand_step4_continue` (V4 3.6, Step 2):
"continuing ... along the oriented line". The direction of a chain's
bottom edge is generated by its signed edge vector, after any affine placement. -/
private theorem host_step_step2_strand_step4_continue_step3_direction
    (r : FacetRecord P) (c : OrientedChain r.facet) (φ : E d ≃ᵃ[ℝ] E d) :
    (affineSpan ℝ (φ '' (c.chain.val.cell edgeIndex).val.carrier)).direction =
      Submodule.span ℝ {φ.linear (chainVector c)} := by
  let e : EdgeName S := ⟨r.ty, host_step_edge ⟨r, c⟩⟩
  have he := (Classical.choose_spec (edge_endpoints_exist e)).2
  change (c.chain.val.cell edgeIndex).val.carrier = _ at he
  rw [he]
  change (affineSpan ℝ (φ.toAffineMap '' segment ℝ _ _)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction,
    direction_affineSpan, vectorSpan_segment, Submodule.map_span, Set.image_singleton]
  change Submodule.span ℝ {φ.linear (edgeVector e)} =
    Submodule.span ℝ {φ.linear (if c.forward then edgeVector e else -edgeVector e)}
  cases c.forward
  · simp only [Bool.false_eq_true, ↓reduceIte, map_neg]
    simpa only [Set.neg_singleton] using
      (Submodule.span_neg (R := ℝ) {φ.linear (edgeVector e)}).symm
  · rfl

/-- Step 4 of the V4 proof of `host_step_step2_strand_step4_continue` (V4 3.6, Step 2):
"same affine spans, orientation and sides ... on the same side of aff g".
Composing the two native frames transports the relative CONT alignment.
Positivity of orientation is transitive because the edge vectors lie on one line. -/
private theorem host_step_step2_strand_step4_continue_step4_transport
    (H : FramedNode S) (n : ℕ) (ι : P.Incidence) (b : Bool)
    (N N' : FramedNode S) (r r' : FacetRecord P)
    (c : OrientedChain r.facet) (c' : OrientedChain r'.facet)
    (hN : r.ty = N.ty) (hN' : r'.ty = N'.ty) (φ : Iso d)
    (hframe : N'.frame = φ.trans N.frame)
    (hrelative : ChainsAligned r r' c c' φ)
    (hcentral : host_step_aligned H n ι b N 0 ⟨r, c⟩) :
    host_step_aligned H n ι b N' 0 ⟨r', c'⟩ := by
  have hzero (M : FramedNode S) : M.prototypeFrame 0 = M.frame.toAffineEquiv := by
    ext x
    simp [FramedNode.prototypeFrame]
  have hlinear (x : E d) : (N'.prototypeFrame 0).linear x =
      (N.prototypeFrame 0).linear (φ.linearIsometryEquiv x) := by
    rw [hzero, hzero, hframe]
    rfl
  have himage (K : Set (E d)) : (N'.prototypeFrame 0).linear '' K =
      (N.prototypeFrame 0).linear '' (φ.linearIsometryEquiv '' K) := by
    simp only [Set.image_image, hlinear]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    have h := congrArg (fun A : AffineSubspace ℝ (E d) => A.map N.frame.toAffineMap)
      (hrelative.1 k)
    dsimp only at h
    rw [AffineSubspace.map_span, AffineSubspace.map_span] at h
    change affineSpan ℝ (N.frame '' (c.chain.val.cell k).val.carrier) =
      affineSpan ℝ (N.frame '' (φ '' (c'.chain.val.cell k).val.carrier)) at h
    have hcell : N'.cell 0 (c'.chain.val.cell k).val =
        N.frame '' (φ '' (c'.chain.val.cell k).val.carrier) := by
      simp only [FramedNode.cell, hzero, hframe, Set.image_image]
      rfl
    change affineSpan ℝ (N'.cell 0 (c'.chain.val.cell k).val) = _
    rw [hcell, ← h]
    exact hcentral.1 k
  · intro k
    rw [himage, ← hrelative.2.1 k]
    exact hcentral.2.1 k
  · have hspan := congrArg AffineSubspace.direction (hrelative.1 edgeIndex)
    have hid := host_step_step2_strand_step4_continue_step3_direction r c
      (AffineEquiv.refl ℝ (E d))
    change (affineSpan ℝ ((fun x : E d => x) ''
      (c.chain.val.cell edgeIndex).val.carrier)).direction =
      Submodule.span ℝ {chainVector c} at hid
    simp only [Set.image_id'] at hid
    change (affineSpan ℝ (c.chain.val.cell edgeIndex).val.carrier).direction =
      (affineSpan ℝ (φ.toAffineEquiv '' (c'.chain.val.cell edgeIndex).val.carrier)).direction
      at hspan
    rw [hid, host_step_step2_strand_step4_continue_step3_direction r' c'
      φ.toAffineEquiv] at hspan
    have hmem : φ.linearIsometryEquiv (chainVector c') ∈ Submodule.span ℝ {chainVector c} := by
      rw [hspan]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have hpos := hrelative.2.2.1
    rw [← ha, inner_smul_right] at hpos
    have ha0 : 0 < a := by
      by_contra h
      have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h)
        (real_inner_self_nonneg (x := chainVector c))
      linarith
    rw [hlinear, ← ha, map_smul, inner_smul_right]
    exact mul_pos ha0 hcentral.2.2.1
  · rw [himage]
    have h := congrArg (fun K : Set (E d) => (N.prototypeFrame 0).linear '' K)
      hrelative.2.2.2
    simp only [hN, hN'] at h
    exact h.symm.trans hcentral.2.2.2

/-- Step 4 of the V4 proof of `host_step_step2_strand` (V4 3.6, Step 2):
"Theorem 2.17(b) gives a template: a tile u_{m+1} ... continuing e_m".
This extracts a single actual successor from a CONT slot, retaining full
flag alignment and the row's zero-or-one counter increment. -/
private theorem host_step_step2_strand_step4_continue
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) (n : ℕ)
    (H : FramedNode S) (ι : P.Incidence) (b : Bool) (u : host_step_Port C)
    (hu : host_step_portValid Y n H ι b u)
    (j : ContSlot (compilerLeaf C u.1))
    (hrecord : j.record = u.2.1) (hedge : j.edge.val = (host_step_edge u.2).val) :
    ∃ v : host_step_Port C, host_step_portValid Y n H ι b v ∧
      (host_step_portEnds u).2 = (host_step_portEnds v).1 ∧
      (v.2.1.kappaMinus (host_step_edge v.2) = u.2.1.kappaPlus (host_step_edge u.2) ∨
        v.2.1.kappaMinus (host_step_edge v.2) = u.2.1.kappaPlus (host_step_edge u.2) + 1) := by
  classical
  rcases u with ⟨t, r, c⟩
  dsimp only at j hrecord hedge hu ⊢
  subst r
  rcases hu with ⟨ht, hread, htype, hc, hι, hb, hβ, halign, hpacket⟩
  have he : j.edge = host_step_edge (⟨j.record, c⟩ : host_step_Chain P) :=
    Subtype.ext hedge
  obtain ⟨θ, hθ, _, hactual⟩ := compiler_events C Y hY t ht (.cont j)
  obtain ⟨T, rfl, hrow⟩ := hθ
  rcases hrow with ⟨hι', hside, hβ', hc₀, hc', hrelative, hcounter, _, hpacket'⟩
  have hs : (compilerLeaf C t).prePattern.state ∈ honestStates S P :=
    (prePattern_components_honest P _
      ((certificate_components_honest P (compilerLeaf C t).1.val
        (compilerLeaf C t).1.property).1 (compilerLeaf C t).2)).1
  obtain ⟨hspans, hsides, hvector⟩ :=
    host_step_step2_strand_step4_continue_step2_chains _ hs _ j.record hread
      c T.centralChain hc hc₀ (hedge.symm.trans T.central_edge.symm)
  have halign₀ : host_step_aligned H n ι b (tileNode t) 0 ⟨j.record, T.centralChain⟩ := by
    refine ⟨?_, ?_, ?_, halign.2.2.2⟩
    · intro k
      have h := congrArg (fun A : AffineSubspace ℝ (E d) =>
        A.map ((tileNode t).prototypeFrame 0).toAffineMap) (hspans k)
      dsimp only at h
      rw [AffineSubspace.map_span, AffineSubspace.map_span] at h
      exact h.symm.trans (halign.1 k)
    · intro k
      rw [← hsides k]
      exact halign.2.1 k
    · rw [← hvector]
      exact halign.2.2.1
  obtain ⟨t', ht', hleaf, hφ⟩ := TemplateOccurs.tile_data C Y (compilerFrame C t)
    T.configuration hactual (T.other, T.label) T.other_mem
  have htype' : T.record.ty = (tileNode t').ty := by
    change T.record.ty = (compilerLeaf C t').prototype
    rw [hleaf]
    exact T.type_eq.trans (T.configuration.types_match _ T.other_mem)
  have hframe : (tileNode t').frame = T.other.frame.trans (tileNode t).frame := hφ
  have halign' := host_step_step2_strand_step4_continue_step4_transport H n ι b
    (tileNode t) (tileNode t') j.record T.record T.centralChain T.otherChain
    htype htype' T.other.frame hframe hrelative halign₀
  have hb' : T.record.sideIndex = b :=
    (host_step_step1_seed_step6_side T.record j.record.incidence j.record.sideIndex
      hι' (hside.trans j.record.side_eq)).trans hb
  have he' : host_step_edge (⟨T.record, T.otherChain⟩ : host_step_Chain P) = T.edge :=
    Subtype.ext T.other_edge
  refine ⟨(t', ⟨T.record, T.otherChain⟩), ?_, ?_, ?_⟩
  · refine ⟨ht', ?_, htype', hc', hι'.trans hι, hb', (congrArg Fin.val hβ').trans hβ,
      halign', j.packet, ?_⟩
    · simpa only [hleaf] using T.record_eq
    · simpa only [hleaf] using hpacket'
  · change compilerFrame C t (j.record.endpoints (host_step_edge ⟨j.record, c⟩)).2 =
      compilerFrame C t' (T.record.endpoints (host_step_edge ⟨T.record, T.otherChain⟩)).1
    rw [he', hφ]
    change compilerFrame C t (j.record.endpoints (host_step_edge ⟨j.record, c⟩)).2 =
      compilerFrame C t (T.other.frame (T.record.endpoints T.edge).1)
    rw [← T.initial, T.vertex_eq, j.terminal, he]
  · simpa only [he', he] using hcounter

/-- Step 5 of the V4 proof of `host_step_step2_strand` (V4 3.6(2a)):
"The sequence, having edges of length at least the minimal native edge length,
is finite." This is the bounded-progress argument, with the continuation rule
supplied separately. -/
private theorem host_step_step2_strand_step5_finite_walk
    {α : Type*} (good : α → Prop) (lo hi : α → ℝ) (R : α → α → Prop)
    (L ε : ℝ) (hε : 0 < ε)
    (hbound : ∀ u, good u → lo u + ε ≤ hi u ∧ hi u ≤ L)
    (hnext : ∀ u, good u → hi u < L →
      ∃ v, good v ∧ lo v = hi u ∧ R u v)
    (u₀ : α) (hu₀ : good u₀) :
    ∃ m : ℕ, ∃ u : Fin (m + 1) → α,
      u 0 = u₀ ∧ (∀ i, good (u i)) ∧ hi (u (Fin.last m)) = L ∧
      ∀ i : Fin m, lo (u i.succ) = hi (u i.castSucc) ∧ R (u i.castSucc) (u i.succ) := by
  have aux : ∀ k : ℕ, ∀ v, good v → L - lo v < (k : ℝ) * ε →
      ∃ m : ℕ, ∃ u : Fin (m + 1) → α,
        u 0 = v ∧ (∀ i, good (u i)) ∧ hi (u (Fin.last m)) = L ∧
        ∀ i : Fin m, lo (u i.succ) = hi (u i.castSucc) ∧ R (u i.castSucc) (u i.succ) := by
    intro k
    induction k with
    | zero =>
        intro v hv hk
        have hb := hbound v hv
        norm_num at hk
        linarith
    | succ k ih =>
        intro v hv hk
        by_cases hend : hi v = L
        · refine ⟨0, fun _ => v, rfl, fun _ => hv, hend, ?_⟩
          exact Fin.elim0
        · obtain ⟨w, hw, hwlo, hR⟩ := hnext v hv (lt_of_le_of_ne (hbound v hv).2 hend)
          have hwk : L - lo w < (k : ℝ) * ε := by
            have hb := (hbound v hv).1
            rw [hwlo]
            push_cast at hk
            nlinarith
          obtain ⟨m, u, hu, hg, he, hc⟩ := ih w hw hwk
          refine ⟨m + 1, Fin.cons v u, rfl, ?_, ?_, ?_⟩
          · intro i
            refine Fin.cases hv (fun j => ?_) i
            exact hg j
          · exact he
          · intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa [hu] using And.intro hwlo hR
            · simpa only [Fin.succ_castSucc, Fin.cons_succ] using hc j
  obtain ⟨k, hk⟩ := exists_nat_gt ((L - lo u₀) / ε)
  exact aux k u₀ hu₀ ((div_lt_iff₀ hε).mp hk)
/-- Step 6 of the V4 proof of `host_step_step2_strand` (V4 3.6(2a)):
"all e_m ⊆ h". Consecutive increasing intervals cover the interval
between their extreme endpoints. -/
private theorem host_step_step2_strand_step6_interval_cover
    (m : ℕ) (lo hi : Fin (m + 1) → ℝ)
    (hinc : ∀ i, lo i < hi i)
    (hnext : ∀ i : Fin m, hi i.castSucc = lo i.succ) :
    (⋃ i, Icc (lo i) (hi i)) = Icc (lo 0) (hi (Fin.last m)) := by
  induction m with
  | zero =>
      have h : ∀ i : Fin 1, i = 0 := fun i => Subsingleton.elim _ _
      simp only [h, iUnion_const]
  | succ m ih =>
      have ht := ih (fun i => lo i.succ) (fun i => hi i.succ)
        (fun i => hinc i.succ) (fun i => hnext i.succ)
      have hsplit : (⋃ i, Icc (lo i) (hi i)) =
          Icc (lo 0) (hi 0) ∪ ⋃ i : Fin (m + 1), Icc (lo i.succ) (hi i.succ) := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_union, Fin.exists_fin_succ]
      rw [hsplit, ht]
      dsimp only
      have hj := hnext 0
      simp only [Fin.castSucc_zero] at hj
      rw [← hj]
      exact Set.Icc_union_Icc_eq_Icc (hinc 0).le
        ((Fin.strictMono_iff_lt_succ.mpr
          (fun i => (hnext i).trans_lt (hinc i.succ))).monotone (Fin.zero_le _))/-- Step 6 of the V4 proof of `host_step_step2_strand` (V4 3.6(2a)):
"e_0,e_1,... follow one another in the orientation of h". Ordered
consecutive intervals have disjoint interiors and distinct interior junctions;
no junction lies in the interior of one of the intervals. -/
private theorem host_step_step2_strand_step6_ordered_intervals
    (m : ℕ) (lo hi : Fin (m + 1) → ℝ) (L : ℝ)
    (hinc : ∀ i, lo i < hi i) (hfirst : lo 0 = 0) (hlast : hi (Fin.last m) = L)
    (hnext : ∀ i : Fin m, hi i.castSucc = lo i.succ) :
    (∀ i, 0 ≤ lo i ∧ hi i ≤ L) ∧
    Pairwise (fun i j => Disjoint (Ioo (lo i) (hi i)) (Ioo (lo j) (hi j))) ∧
    (⋃ i, Icc (lo i) (hi i)) = Icc 0 L ∧
    Function.Injective (fun i : Fin m => hi i.castSucc) ∧
    (∀ i : Fin m, hi i.castSucc ∈ Ioo 0 L) ∧
    (∀ i : Fin m, ∀ j, hi i.castSucc ∉ Ioo (lo j) (hi j)) ∧
    ∀ i, Ioo (lo i) (hi i) ⊆ Ioo 0 L := by
  have hlo : StrictMono lo := Fin.strictMono_iff_lt_succ.mpr
    (fun i => (hinc i.castSucc).trans_eq (hnext i))
  have hhi : StrictMono hi := Fin.strictMono_iff_lt_succ.mpr
    (fun i => (hnext i).trans_lt (hinc i.succ))
  have hb : ∀ i, 0 ≤ lo i ∧ hi i ≤ L := by
    intro i
    exact ⟨hfirst ▸ hlo.monotone (Fin.zero_le i),
      hlast ▸ hhi.monotone (Fin.le_last i)⟩
  have hsep : ∀ i j, i < j → hi i ≤ lo j := by
    intro i j hij
    let k : Fin m := ⟨i.val, by have := j.isLt; exact Nat.lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)⟩
    have he : k.castSucc = i := Fin.ext rfl
    have hkj : k.succ ≤ j := by change i.val + 1 ≤ j.val; exact hij
    rw [← he, hnext k]
    exact hlo.monotone hkj
  refine ⟨hb, ?_, ?_, hhi.injective.comp (Fin.castSucc_injective m), ?_, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact (not_lt_of_ge (hsep i j hij)) (hy.1.trans hx.2)
    · exact (not_lt_of_ge (hsep j i hji)) (hx.1.trans hy.2)
  · rw [host_step_step2_strand_step6_interval_cover m lo hi hinc hnext, hfirst, hlast]
  · intro i
    refine ⟨(hb i.castSucc).1.trans_lt (hinc i.castSucc), ?_⟩
    rw [hnext i]
    exact (hinc i.succ).trans_le (hb i.succ).2
  · intro i j hx
    by_cases hji : j ≤ i.castSucc
    · exact (not_lt_of_ge (hhi.monotone hji)) hx.2
    · exact (not_lt_of_ge (hsep i.castSucc j (lt_of_not_ge hji))) hx.1
  · intro i x hx
    exact ⟨(hb i).1.trans_lt hx.1, hx.2.trans_le (hb i).2⟩
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
  classical
  let H := proposedSibling D B hB f a
  let ι := a.record.incidence
  let b := !a.record.sideIndex
  obtain ⟨φ, L, hL, hφ0, hφL, hflag, hflagopen⟩ :=
    host_step_step2_strand_step1_chart H n ι b
  let A := {u : host_step_Port C // host_step_portValid Y n H ι b u}
  choose lo hi hlt hleft hright hedge hopen using
    (fun u : A => host_step_step2_strand_step1_port_coordinates
      Y n H ι b u.val u.property φ L hL hφ0 hφL)
  obtain ⟨ε, hε, hlength⟩ := host_step_step2_strand_step1_native_length (C := C)
  let good : A → Prop := fun u => 0 ≤ lo u ∧ lo u < L
  let R : A → A → Prop := fun u v =>
    v.val.2.1.kappaMinus (host_step_edge v.val.2) =
      u.val.2.1.kappaPlus (host_step_edge u.val.2) ∨
    v.val.2.1.kappaMinus (host_step_edge v.val.2) =
      u.val.2.1.kappaPlus (host_step_edge u.val.2) + 1
  have hsub : ∀ u : A, good u → host_step_portEdge u.val ⊆ host_step_flagEdge H n ι b := by
    intro u hu
    apply host_step_step2_strand_step2_terminal_bound Y hY n hn D hD B hB f a
      hends.2 u.val u.property
    · rw [hleft u, hflag]
      exact ⟨lo u, ⟨hu.1, hu.2.le⟩, rfl⟩
    · rw [hleft u, ← hφL]
      intro heq
      exact hu.2.ne (φ.injective heq)
  have hbound : ∀ u : A, good u → lo u + ε ≤ hi u ∧ hi u ≤ L := by
    intro u hu
    have hlen := hlength u.val
    rw [hleft u, hright u, φ.dist_map, Real.dist_eq,
      abs_of_neg (sub_neg.mpr (hlt u))] at hlen
    refine ⟨by linarith, ?_⟩
    have hm : φ (hi u) ∈ host_step_flagEdge H n ι b :=
      hsub u hu (by rw [hedge u]; exact ⟨hi u, ⟨(hlt u).le, le_rfl⟩, rfl⟩)
    rw [hflag] at hm
    obtain ⟨x, hx, heq⟩ := hm
    exact (φ.injective heq) ▸ hx.2
  have hnext : ∀ u : A, good u → hi u < L →
      ∃ v : A, good v ∧ lo v = hi u ∧ R u v := by
    intro u hu hbefore
    have hterminal : (host_step_portEnds u.val).2 ∈ relint (host_step_flagEdge H n ι b) := by
      rw [hright u, hflagopen]
      exact ⟨hi u, ⟨hu.1.trans_lt (hlt u), hbefore⟩, rfl⟩
    obtain ⟨j, hjr, hje⟩ := host_step_step2_strand_step3_no_false_endpoint
      Y hY n hn D hD B hB f a u.val u.property (hsub u hu) hterminal
    obtain ⟨v, hv, hvpoint, hvcounter⟩ := host_step_step2_strand_step4_continue
      Y hY n H ι b u.val u.property j hjr hje
    let v' : A := ⟨v, hv⟩
    have heq : lo v' = hi u := φ.injective
      ((hleft v').symm.trans (hvpoint.symm.trans (hright u)))
    refine ⟨v', ?_, heq, hvcounter⟩
    change 0 ≤ lo v' ∧ lo v' < L
    rw [heq]
    exact ⟨(hu.1.trans_lt (hlt u)).le, hbefore⟩
  let seed : A := ⟨u₀, hu₀⟩
  have hlo0 : lo seed = 0 :=
    φ.injective ((hleft seed).symm.trans (hstart.trans hφ0.symm))
  have hseed : good seed := by
    change 0 ≤ lo seed ∧ lo seed < L
    rw [hlo0]
    exact ⟨le_rfl, hL⟩
  obtain ⟨m, w, hw0, hwgood, hwlast, hwcont⟩ :=
    host_step_step2_strand_step5_finite_walk good lo hi R L ε hε hbound hnext seed hseed
  have hwfirst : lo (w 0) = 0 := by rw [hw0, hlo0]
  have hwadj : ∀ i : Fin m, hi (w i.castSucc) = lo (w i.succ) :=
    fun i => (hwcont i).1.symm
  obtain ⟨hbounds, hdisj, hcover, hinj, hjunction, havoid, hinside⟩ :=
    host_step_step2_strand_step6_ordered_intervals m (fun i => lo (w i))
      (fun i => hi (w i)) L (fun i => hlt (w i)) hwfirst hwlast hwadj
  let u : Fin (m + 1) → host_step_Port C := fun i => (w i).val
  have hu0 : u 0 = u₀ := congrArg Subtype.val hw0
  have hterminal : (host_step_portEnds (u (Fin.last m))).2 =
      host_step_flagFrame H n ι b (P.flag ι).terminal := by
    rw [hright, hwlast, hφL]
  have hcontained : ∀ i, host_step_portEdge (u i) ⊆ host_step_flagEdge H n ι b :=
    fun i => hsub (w i) (hwgood i)
  refine ⟨m, u, hu0, ?_⟩
  refine ⟨fun i => (w i).property, hu0 ▸ hstart, hterminal, hu0 ▸ hzero, ?_, ?_,
    hcontained, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact host_step_step2_strand_step2_terminal_counter Y hY n hn D hD B hB f a
      hends.2 _ (w (Fin.last m)).property (hcontained _) hterminal
  · intro i
    refine ⟨?_, (hwcont i).2⟩
    change (host_step_portEnds (w i.castSucc).val).2 =
      (host_step_portEnds (w i.succ).val).1
    rw [hright, hleft, hwadj]
  · intro i j hij
    rw [hopen (w i), hopen (w j)]
    exact (Set.disjoint_image_iff φ.injective).mpr (hdisj hij)
  · change (⋃ i, host_step_portEdge (w i).val) = _
    simp_rw [hedge]
    rw [← Set.image_iUnion, hcover, hflag]
  · intro i j heq
    apply hinj
    apply φ.injective
    exact (hright (w i.castSucc)).symm.trans (heq.trans (hright (w j.castSucc)))
  · intro i
    rw [hright (w i.castSucc), hflagopen]
    exact ⟨_, hjunction i, rfl⟩
  · intro i j hmem
    rw [hopen (w j)] at hmem
    obtain ⟨x, hx, heq⟩ := hmem
    have hxi : x = hi (w i.castSucc) :=
      φ.injective (heq.trans (hright (w i.castSucc)))
    exact havoid i j (hxi ▸ hx)
  · intro i
    rw [hopen (w i), hflagopen]
    exact Set.image_mono (hinside i)

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

/-- Step 1 of the V4 proof of `host_step_step3_roots` (V4 3.6):
"Each u_m lies in a unique block B_m of the level." Existence follows by
covering an interior point of the tile and using the actual leaves of that block. -/
private theorem host_step_step3_roots_step1_owner
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (G : GeometricLevel Y n)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles) :
    ∃ B ∈ G.blocks, t.carrier ⊆ B.carrier ∧
      (tileNode t).IsDescendant 0 B.node n := by
  classical
  have hnonempty : (interior t.carrier).Nonempty := by
    rw [compilerFrame_carrier C t]
    change (interior ((compilerFrame C t).toHomeomorph ''
      (S.proto (compilerLeaf C t).prototype).carrier)).Nonempty
    rw [← Homeomorph.image_interior]
    exact (S.proto (compilerLeaf C t).prototype).interior_nonempty.image _
  obtain ⟨x, hxt⟩ := hnonempty
  obtain ⟨B, hB, hxB⟩ := G.cover x
  rw [B.union_tiles] at hxB
  obtain ⟨v, hxv⟩ := Set.mem_iUnion.mp hxB
  obtain ⟨hv, hxv⟩ := Set.mem_iUnion.mp hxv
  have htv : t = v := by
    by_contra hne
    have hreg : closure (interior v.carrier) = v.carrier := by
      obtain ⟨A, _, φ, hcarrier, _⟩ := v.realization
      rw [hcarrier]
      change closure (interior (φ.toHomeomorph '' A.carrier)) =
        φ.toHomeomorph '' A.carrier
      rw [← φ.toHomeomorph.image_interior, ← φ.toHomeomorph.image_closure,
        A.regularClosed]
    have hd := (Y.disjoint ht hv.1 hne).closure_right isOpen_interior
    rw [hreg] at hd
    exact Set.disjoint_left.mp hd hxt hxv
  subst v
  have hexact : t ∈ {t | t ∈ Y.tiles ∧ ∃ w : S.RoleWord B.node.ty n,
      tileNode t = (S.nativeTile B.node.ty n w).move B.node.frame} := by
    rw [← B.tiles_exact]
    exact ⟨ht, hv.2⟩
  obtain ⟨w, hw⟩ := hexact.2
  exact ⟨B, hB, hv.2, n, by omega, w, hw⟩

/-- Step 2 of the V4 proof of `host_step_step3_roots` (V4 3.6, F1):
"the same affine spans". Relative interiors commute with the full affine
prototype frames, including the anisotropic expansion. -/
private theorem host_step_step3_roots_step2_relint_image
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

/-- Step 1 of the V4 proof of `host_step_step3_roots_step2_flag_overlap` (V4 3.6, F1):
"Moving from x ... by a much smaller displacement". A finite polyhedron is
locally star-shaped at each of its points: discard the convex pieces missing x. -/
private theorem host_step_step3_roots_step2_flag_overlap_step1_local_segments
    (K : Set (E d)) (hK : Polyhedron K) (x : E d) :
    ∃ U : Set (E d), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ K ∩ U, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → x + t • (y - x) ∈ K := by
  classical
  obtain ⟨s, hs⟩ := hK
  let bad := s.filter (fun p : Finset (E d) => x ∉ convexHull ℝ (p : Set (E d)))
  let U : Set (E d) := (⋃ p ∈ bad, convexHull ℝ (p : Set (E d)))ᶜ
  have hU : IsOpen U :=
    (isClosed_biUnion_finset (s := bad)
      (fun p _ => p.finite_toSet.isCompact_convexHull.isClosed)).isOpen_compl
  have hxU : x ∈ U := by
    intro hh
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hh
    exact (Finset.mem_filter.mp hp).2 hxp
  refine ⟨U, hU, hxU, ?_⟩
  rintro y ⟨hy, hyU⟩ t ht ht1
  rw [hs] at hy ⊢
  obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hy
  have hxp : x ∈ convexHull ℝ (p : Set (E d)) := by
    by_contra h
    exact hyU (mem_iUnion₂.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, h⟩, hyp⟩)
  refine mem_iUnion₂.mpr ⟨p, hp, ?_⟩
  have hm := (convex_convexHull ℝ (p : Set (E d))) hxp hyp
    (sub_nonneg.mpr ht1) ht (by ring : (1 - t) + t = 1)
  convert hm using 1 <;> module

set_option maxHeartbeats 800000 in
/-- Step 2 of the V4 proof of `host_step_step3_roots_step2_flag_overlap` (V4 3.6, F1):
"the same composite displacement from x gives a point". A common radial tangent
cone lets a regular closed polyhedral cell enter a closed set of the same affine
span. Baire's theorem supplies a relatively open set of common displacements. -/
private theorem host_step_step3_roots_step2_flag_overlap_step2_tangent_overlap
    (K L : Set (E d)) (hK : Polyhedron K) (hreg : closure (relint K) = K)
    (hL : IsClosed L) (hspan : affineSpan ℝ K = affineSpan ℝ L)
    (x : E d) (hx : x ∈ K) (hcone : tangentCone K x ⊆ tangentCone L x) :
    (relint K ∩ relint L).Nonempty := by
  obtain ⟨O, hO, hxO, hseg⟩ :=
    host_step_step3_roots_step2_flag_overlap_step1_local_segments K hK x
  let A := affineSpan ℝ K
  have hxA : x ∈ A := mem_affineSpan ℝ hx
  letI : Nonempty A := ⟨⟨x, hxA⟩⟩
  let U : Set A := interior ((↑) ⁻¹' K : Set A) ∩ ((↑) ⁻¹' O)
  have hU : IsOpen U := isOpen_interior.inter (hO.preimage continuous_subtype_val)
  have hUne : U.Nonempty := by
    have hxcl : x ∈ closure (relint K) := hreg.symm ▸ hx
    obtain ⟨y, hyO, z, hz, rfl⟩ := mem_closure_iff.mp hxcl O hO hxO
    exact ⟨z, hz, hyO⟩
  let c (j : ℕ) : ℝ := 1 / (j + 1 : ℝ)
  have hc (j : ℕ) : 0 < c j ∧ c j ≤ 1 := by
    dsimp [c]
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
  let g (j : ℕ) : A →ᵃ[ℝ] A := AffineMap.homothety ⟨x, hxA⟩ (c j)
  have hg (j : ℕ) (y : A) : (g j y).val = x + c j • (y.val - x) := by
    simp only [g, AffineMap.homothety_apply, AffineSubspace.coe_vadd,
      Submodule.coe_smul, AffineSubspace.coe_vsub, vsub_eq_sub, vadd_eq_add]
    exact add_comm _ _
  let T (j : ℕ) : Set A := (g j) ⁻¹' ((↑) ⁻¹' L : Set A)
  have hT (j : ℕ) : IsClosed (T j) :=
    (hL.preimage continuous_subtype_val).preimage (AffineMap.homothety_continuous _ _)
  have hcover : ∀ y : U, ∃ j, y.val ∈ T j := by
    intro y
    have hyK : y.val.val ∈ K :=
      interior_subset (s := ((↑) ⁻¹' K : Set A)) y.property.1
    have hycone : y.val.val - x ∈ tangentCone K x :=
      ⟨1, zero_lt_one, fun t ht ht1 => hseg _ ⟨hyK, y.property.2⟩ t ht.le ht1.le⟩
    obtain ⟨ε, hε, hyL⟩ := hcone hycone
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    refine ⟨j, ?_⟩
    change (g j y.val).val ∈ L
    rw [hg]
    exact hyL (c j) (hc j).1 hj
  letI : Nonempty U := hUne.to_subtype
  letI : IsClosed (A : Set (E d)) := A.closed_of_finiteDimensional
  letI : CompleteSpace A := IsClosed.completeSpace_coe
  letI : BaireSpace U := hU.baireSpace
  obtain ⟨j, y, hy⟩ := nonempty_interior_of_iUnion_of_closed
    (fun j => (hT j).preimage continuous_subtype_val)
    (show (⋃ j, ((↑) ⁻¹' T j : Set U)) = univ by
      apply eq_univ_of_forall
      intro y
      obtain ⟨j, hj⟩ := hcover y
      exact mem_iUnion.mpr ⟨j, hj⟩)
  have hyT : y.val ∈ interior (T j) :=
    hU.isOpenMap_subtype_val.interior_preimage_subset_preimage_interior hy
  let W := U ∩ interior (T j)
  have hW : IsOpen W := hU.inter isOpen_interior
  have hgw : IsOpen (g j '' W) :=
    AffineMap.homothety_isOpenMap _ _ (hc j).1.ne' W hW
  have hsub : g j '' W ⊆ ((↑) ⁻¹' K : Set A) ∩ ((↑) ⁻¹' L : Set A) := by
    rintro _ ⟨z, hz, rfl⟩
    constructor
    · change (g j z).val ∈ K
      rw [hg]
      have hzU : z ∈ U := hz.1
      have hzK : z.val ∈ K := interior_subset (s := ((↑) ⁻¹' K : Set A)) hzU.1
      have hzO : z.val ∈ O := hzU.2
      exact hseg z.val ⟨hzK, hzO⟩ (c j) (hc j).1.le (hc j).2
    · exact interior_subset (s := T j) hz.2
  have hmem : g j y.val ∈ interior (((↑) ⁻¹' K : Set A) ∩ ((↑) ⁻¹' L : Set A)) :=
    interior_maximal hsub hgw ⟨y.val, ⟨y.property, hyT⟩, rfl⟩
  rw [interior_inter] at hmem
  refine ⟨(g j y.val).val, ⟨g j y.val, hmem.1, rfl⟩, ?_⟩
  change (g j y.val).val ∈ intrinsicInterior ℝ L
  rw [intrinsicInterior, ← hspan]
  exact ⟨g j y.val, hmem.2, rfl⟩

/-- Step 3 of the V4 proof of `host_step_step3_roots_step2_flag_overlap` (V4 3.6, F1):
"the same holds ... for any tile ... or block". Affine placement preserves a
finite polyhedral presentation, including an anisotropic expansion. -/
private theorem host_step_step3_roots_step2_flag_overlap_step3_polyhedron_image
    (K : Set (E d)) (hK : Polyhedron K) (φ : E d ≃ᵃ[ℝ] E d) :
    Polyhedron (φ '' K) := by
  classical
  obtain ⟨s, hs⟩ := hK
  have hmap (p : Finset (E d)) : φ '' convexHull ℝ (p : Set (E d)) =
      convexHull ℝ (φ '' (p : Set (E d))) := φ.toAffineMap.image_convexHull _
  refine ⟨s.image (fun p => p.image φ), ?_⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hs] at hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp hz
    refine mem_iUnion₂.mpr ⟨p.image φ, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    rw [Finset.coe_image, ← hmap]
    exact mem_image_of_mem φ hzp
  · intro hy
    obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    rw [Finset.coe_image, ← hmap] at hyq
    obtain ⟨z, hz, rfl⟩ := hyq
    refine ⟨z, ?_, rfl⟩
    rw [hs]
    exact mem_iUnion₂.mpr ⟨p, hp, hz⟩


/-- Step 4 of the V4 proof of `host_step_step3_roots_step2_flag_overlap` (V4 3.6, F1):
"then by a much smaller displacement into relint F₂ on the recorded side".
For one consecutive pair of flag cells, a common lower relative-interior point
has the same upper tangent cone in both placements, and hence the upper
relative interiors meet. -/
private theorem host_step_step3_roots_step2_flag_overlap_step4_coface
    {A A' : S.ι} (F : FacetFlag S A) (G : FacetFlag S A')
    (φ ψ : E d ≃ᵃ[ℝ] E d) (k : FlagStep d)
    (hspan : affineSpan ℝ (φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier) =
      affineSpan ℝ (ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier))
    (hside : φ.linear '' flagSide F k = ψ.linear '' flagSide G k)
    (hmeet : (relint (φ '' (F.cell ⟨k.val, k.property.1, by omega⟩).val.carrier) ∩
      relint (ψ '' (G.cell ⟨k.val, k.property.1, by omega⟩).val.carrier)).Nonempty) :
    (relint (φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier) ∩
      relint (ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier)).Nonempty := by
  obtain ⟨x, hxF, hxG⟩ := hmeet
  let lo : FlagIndex d := ⟨k.val, k.property.1, by omega⟩
  let hi : FlagIndex d := ⟨k.val + 1, by omega, k.property.2⟩
  have htransport {B : S.ι} (H : FacetFlag S B) (χ : E d ≃ᵃ[ℝ] E d)
      (hx : x ∈ relint (χ '' (H.cell lo).val.carrier)) :
      tangentCone (χ '' (H.cell hi).val.carrier) x = χ.linear '' flagSide H k := by
    rw [host_step_step3_roots_step2_relint_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [host_step_step1_seed_step8_transport_step1_tangent_image,
      host_step_step1_seed_step8_transport_step4_coface H k p hp]
  have hreg : closure (relint (φ '' (F.cell hi).val.carrier)) =
      φ '' (F.cell hi).val.carrier := by
    rw [host_step_step3_roots_step2_relint_image]
    change closure (φ.toHomeomorphOfFiniteDimensional '' relint (F.cell hi).val.carrier) =
      φ.toHomeomorphOfFiniteDimensional '' (F.cell hi).val.carrier
    rw [← φ.toHomeomorphOfFiniteDimensional.image_closure, (F.cell hi).val.flat.regularClosed]
  have hxK : x ∈ φ '' (F.cell hi).val.carrier := by
    obtain ⟨p, hp, rfl⟩ := intrinsicInterior_subset (𝕜 := ℝ) hxF
    exact ⟨p, F.nested lo hi (by dsimp [lo, hi]; omega) hp, rfl⟩
  apply host_step_step3_roots_step2_flag_overlap_step2_tangent_overlap
    (φ '' (F.cell hi).val.carrier) (ψ '' (G.cell hi).val.carrier)
    (host_step_step3_roots_step2_flag_overlap_step3_polyhedron_image _
      (F.cell hi).val.flat.polyhedral φ) hreg
    ((G.cell hi).val.flat.compact.image ψ.toHomeomorphOfFiniteDimensional.continuous).isClosed
    hspan x hxK
  rw [htransport F φ hxF, htransport G ψ hxG, hside]

/-- Step 2 of the V4 proof of `host_step_step3_roots` (V4 3.6, F1):
"the same composite displacement from x gives a point" in both interiors.
Two full flags with the same spans, successive sides and inward side have
overlapping relative interiors at every coface whenever their open edges meet. -/
private theorem host_step_step3_roots_step2_flag_overlap
    (N M : FramedNode S) (n m : ℕ) {A A' : S.ι}
    (F : FacetFlag S A) (G : FacetFlag S A') (hN : N.ty = A) (hM : M.ty = A')
    (hspans : ∀ k, affineSpan ℝ (N.cell n (F.cell k).val) =
      affineSpan ℝ (M.cell m (G.cell k).val))
    (hsides : ∀ k, (N.prototypeFrame n).linear '' flagSide F k =
      (M.prototypeFrame m).linear '' flagSide G k)
    (hinward : (N.prototypeFrame n).linear ''
        tangentCone (S.proto N.ty).carrier (cellAnchor (F.cell facetIndex).val) =
      (M.prototypeFrame m).linear ''
        tangentCone (S.proto M.ty).carrier (cellAnchor (G.cell facetIndex).val))
    (hmeet : (relint (N.cell n (F.cell edgeIndex).val) ∩
      relint (M.cell m (G.cell edgeIndex).val)).Nonempty) :
    (∀ k, (relint (N.cell n (F.cell k).val) ∩
      relint (M.cell m (G.cell k).val)).Nonempty) ∧
    (interior (N.carrier n) ∩ interior (M.carrier m)).Nonempty := by
  have hfaces : ∀ (j : ℕ) (hj : 1 ≤ j) (hjd : j < d),
      (relint (N.cell n (F.cell ⟨j, hj, hjd⟩).val) ∩
        relint (M.cell m (G.cell ⟨j, hj, hjd⟩).val)).Nonempty := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
        intro hjd
        exact hmeet
    | succ j hj ih =>
        intro hjd
        exact host_step_step3_roots_step2_flag_overlap_step4_coface F G
          (N.prototypeFrame n) (M.prototypeFrame m) ⟨j, hj, hjd⟩
          (hspans _) (hsides _) (ih (by omega))
  refine ⟨fun k => hfaces k.val k.property.1 k.property.2, ?_⟩
  obtain ⟨x, hx⟩ := hmeet
  apply Set.Nonempty.of_closure
  exact ⟨x, host_step_step2_strand_step2_terminal_bound_step1_flag_overlap
    N M n m F G hN hM hspans hsides hinward x hx⟩

/-- Step 2 of the V4 proof of `host_step_step3_roots` (V4 3.6, F1):
"the cells ... of the actual flag". The top of either named side flag is
exactly the incidence's facet, as follows from equality of positioned carriers. -/
private theorem host_step_step3_roots_step2_flag_top (ι : P.Incidence) (b : Bool) :
    ((P.sideFlag ι b).cell facetIndex).val = (ι.val.sideFacet b).val := by
  have h := P.sideFlag_eq ι b facetIndex
  rw [(P.flag ι).top] at h
  have hcarrier : ((P.sideFlag ι b).cell facetIndex).val.carrier =
      (ι.val.sideFacet b).val.carrier := by
    apply Set.image_injective.mpr (S.child ι.val.ty (ι.val.sideIndex b)).frame.injective
    change placedSet (S.child ι.val.ty (ι.val.sideIndex b)).frame _ = _
    rw [h]
    cases b
    · rfl
    · exact ι.val.paired
  have cell_eq (e f : Cell d) (h : e.carrier = f.carrier) : e = f := by
    rcases e with ⟨K, j, hj⟩
    rcases f with ⟨L, k, hk⟩
    cases h
    have hjk : j = k := hj.dimension.symm.trans hk.dimension
    cases hjk
    rfl
  exact cell_eq _ _ hcarrier

/-- Step 2 of the V4 proof of `host_step_step3_roots` (V4 3.6, F1):
"the i-side points ... lie in int B" and the j-side points in its sibling.
Distinct prescribed children have disjoint interiors at every height. -/
private theorem host_step_step3_roots_step2_children_disjoint
    (Q : FramedNode S) (n : ℕ) (i j : S.I Q.ty) (hij : i ≠ j) :
    Disjoint (interior ((Q.child n i).carrier n))
      (interior ((Q.child n j).carrier n)) := by
  let e := ((S.σ ^ n).toContinuousLinearEquiv.toHomeomorph).trans Q.frame.toHomeomorph
  have hcarrier (i : S.I Q.ty) : (Q.child n i).carrier n =
      e '' placedSet (S.child Q.ty i).frame (S.proto (S.child Q.ty i).ty).carrier := by
    simp only [FramedNode.carrier, FramedNode.child, SubstSystem.supertile,
      placedSet, Set.image_image]
    congr 1
    funext x
    change Q.frame (S.placeChild n i ((S.σ ^ n) x)) =
      Q.frame ((S.σ ^ n) ((S.child Q.ty i).frame x))
    congr 1
    rw [S.placeChild_apply]
    simp [linearConj, Child.frame, rigidMotion, zpow_neg,
      LinearEquiv.mul_apply, ← map_add]
  rw [hcarrier i, hcarrier j, ← e.image_interior, ← e.image_interior]
  exact Set.disjoint_image_of_injective e.injective (S.children_disjoint Q.ty hij)

/-- Step 2 of the V4 proof of `host_step_step3_roots` (V4 3.6):
"otherwise B_m would contain interior points on both sides ... overlapping
int B". The port facet is therefore contained in a facet of its owning block. -/
private theorem host_step_step3_roots_step2_boundary
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) (u : host_step_Port C)
    (hu : host_step_portValid Y n (proposedSibling D B hB f a)
      a.record.incidence (!a.record.sideIndex) u)
    (hinside : relint (host_step_portEdge u) ⊆
      relint (host_step_flagEdge (proposedSibling D B hB f a) n
        a.record.incidence (!a.record.sideIndex)))
    (B' : Block Y n) (hB' : B' ∈ D.geometry.blocks)
    (hsub : u.1.carrier ⊆ B'.carrier)
    (hdesc : (tileNode u.1).IsDescendant 0 B'.node n) :
    ∃ F : FacetName S B'.node.ty,
      (tileNode u.1).cell 0 u.2.1.facet.val ⊆ B'.node.cell n F.val := by
  classical
  let H := proposedSibling D B hB f a
  let ι := a.record.incidence
  let b := !a.record.sideIndex
  rcases hu with ⟨ht, hrec, hty, hactive, hinc, hs, hβ, halign, hpacket⟩
  have he : (relint (host_step_portEdge u)).Nonempty := by
    change (relint ((tileNode u.1).prototypeFrame 0 ''
      (host_step_edge u.2).val.carrier)).Nonempty
    rw [host_step_step3_roots_step2_relint_image]
    exact (host_step_edge u.2).val.flat.relint_nonempty.image _
  obtain ⟨x, hx⟩ := he
  obtain ⟨hfaces, hinter⟩ := host_step_step3_roots_step2_flag_overlap
    (tileNode u.1) H 0 n u.2.2.chain.val (P.sideFlag ι b) hty.symm rfl
    halign.1 halign.2.1
    (by simpa only [u.2.2.chain.property, host_step_step3_roots_step2_flag_top]
      using halign.2.2.2) ⟨x, hx, hinside hx⟩
  let g : FacetName S (tileNode u.1).ty :=
    ⟨u.2.1.facet.val, by rw [← hty]; exact u.2.1.facet.property⟩
  rcases facet_dichotomy B'.node (tileNode u.1) n 0 hdesc g with hboundary | hint
  · obtain ⟨F, hF, _⟩ := hboundary
    exact ⟨F, hF⟩
  have hsem := Parser.ageOneFacet_semantics D hD B hB f a
  have hrole : firstRole D B hB = ι.val.sideRole a.record.sideIndex :=
    hsem.2.2.1.symm.trans a.record.side_eq
  have hBH : Disjoint (interior B.carrier) (interior (H.carrier n)) := by
    let Q : FramedNode S := ⟨ι.val.ty, (proposedParent D B hB).frame⟩
    have hnode : Q.child n (ι.val.sideIndex a.record.sideIndex) = B.node := by
      have hc := Parser.proposedParent_child D hD B hB
      change (⟨(S.child (firstRole D B hB).1 (firstRole D B hB).2).ty,
        (S.placeChild n (firstRole D B hB).2).trans (proposedParent D B hB).frame⟩ :
        FramedNode S) = B.node at hc
      rw [hrole] at hc
      exact hc
    have hne : ι.val.sideIndex a.record.sideIndex ≠ ι.val.sideIndex b := by
      cases hb : a.record.sideIndex <;>
        simp [b, hb, PrimitiveIncidence.sideIndex, ι.val.distinct, Ne.symm ι.val.distinct]
    have hd := host_step_step3_roots_step2_children_disjoint Q n _ _ hne
    change Disjoint (interior ((Q.child n (ι.val.sideIndex a.record.sideIndex)).carrier n))
      (interior (H.carrier n)) at hd
    rwa [hnode] at hd
  obtain ⟨y, hy, hyf⟩ := hfaces facetIndex
  rw [u.2.2.chain.property] at hy
  rw [host_step_step3_roots_step2_flag_top] at hyf
  change y ∈ relint ((proposedSibling D B hB f a).cell n
    (a.record.incidence.val.sideFacet (!a.record.sideIndex)).val) at hyf
  rw [hsem.2.2.2] at hyf
  have hyB : y ∈ B.carrier := by
    obtain ⟨z, hz, rfl⟩ := (intrinsicInterior_subset (𝕜 := ℝ) hyf)
    have hzB : z ∈ (S.proto B.node.ty).carrier := by
      have hzfront : z ∈ frontier (S.proto B.node.ty).carrier := by
        rw [← (S.cx B.node.ty).carriers_cover]
        exact Set.mem_iUnion.mpr ⟨f.val, Set.mem_iUnion.mpr
          ⟨(facetCell f).property, hz⟩⟩
      exact (S.proto B.node.ty).compact.isClosed.frontier_subset hzfront
    exact ⟨(S.σ ^ n) z, ⟨z, hzB, rfl⟩, rfl⟩
  have heq : B = B' := by
    by_contra hne
    have hd := (D.geometry.disjoint hB hB' hne).closure_left isOpen_interior
    rw [B.carrier_regular.2.1] at hd
    exact Set.disjoint_left.mp hd hyB (hint hy)
  obtain ⟨z, hzt, hzH⟩ := hinter
  have hcarrier : (tileNode u.1).carrier 0 = u.1.carrier := by
    rw [compilerFrame_carrier C u.1]
    simp [tileNode, FramedNode.carrier, SubstSystem.supertile, placedSet]
  rw [hcarrier] at hzt
  have hzB' := interior_mono hsub hzt
  rw [← heq] at hzB'
  exact False.elim (Set.disjoint_left.mp hBH hzB' hzH)

/-- Step 1 of the V4 proof of `host_step_step3_roots_step3_lift` (V4 2.3):
"same iota, side, beta and provider". A finite descendant boundary record
forces a finite ancestor record and preserves its provider data. -/
private theorem host_step_step3_roots_step3_lift_step1_provider
    (U : HonestSource S) (q c : U.Node) (r : ℕ)
    (hc : U.hierarchy.ancestor c r = q)
    (F : FacetName S q.2.val.ty) (f : FacetName S c.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault c f)
    (hsub : c.2.val.cell c.1 f.val ⊆ q.2.val.cell q.1 F.val) :
    ∃ hF : ¬ U.hierarchy.IsFault q F,
      U.recordIncidence P c f hf = U.recordIncidence P q F hF ∧
      U.recordSide P c f hf = U.recordSide P q F hF ∧
      (U.recordOf P c f hf).beta = (U.recordOf P q F hF).beta ∧
      U.providerPlacement P c f hf = U.providerPlacement P q F hF := by
  have hF : ¬ U.hierarchy.IsFault q F := by
    intro h
    apply hf
    intro k
    apply (U.hierarchy.boundaryOffsets_downward c f).2 k (r + k) (by omega)
    change c.2.val.cell c.1 f.val ⊆
      frontier ((U.hierarchy.ancestor c (r + k)).2.val.carrier
        (U.hierarchy.ancestor c (r + k)).1)
    rw [← U.hierarchy.ancestor_add, hc]
    exact hsub.trans (h k)
  obtain ⟨_, hprovider, hbirth⟩ := U.hierarchy.provider_inherited q c r hc F f hF hsub
  have hi := host_step_step1_seed_step3_restricted_header_step3_incidence P U c q f F
    hf hF hbirth hprovider
  have hserv : U.hierarchy.servingChild c f hf = U.hierarchy.servingChild q F hF := by
    have hb := congrArg (fun z : U.Node => z.1) hbirth
    change (U.hierarchy.servingChild c f hf).1 + 1 =
      (U.hierarchy.servingChild q F hF).1 + 1 at hb
    have h₁ := U.hierarchy.ancestor_height c (U.hierarchy.firstProvider c f hf).1
    have h₂ := U.hierarchy.ancestor_height q (U.hierarchy.firstProvider q F hF).1
    have h₃ := U.hierarchy.ancestor_height c r
    rw [hc] at h₃
    have hoff : (U.hierarchy.firstProvider c f hf).1 =
        r + (U.hierarchy.firstProvider q F hF).1 := by
      change (U.hierarchy.servingChild c f hf).1 = _ at h₁
      change (U.hierarchy.servingChild q F hF).1 = _ at h₂
      omega
    simp only [CoherentHierarchy.servingChild, hoff, ← U.hierarchy.ancestor_add, hc]
  refine ⟨hF, hi, ?_, ?_, ?_⟩
  · apply (Classical.choose_spec (U.recordSide_exists P q F hF)).2
    rw [← hi, ← hserv]
    exact (Classical.choose_spec (U.recordSide_exists P c f hf)).1
  · apply Fin.ext
    change (U.hierarchy.servingChild c f hf).1 % P.L =
      (U.hierarchy.servingChild q F hF).1 % P.L
    rw [hserv]
  · unfold HonestSource.providerPlacement CoherentHierarchy.birthHeight
    rw [hbirth, hi]

/-- Step 2 of the V4 proof of `host_step_step3_roots_step3_lift` (V4 2.3):
"with inherited orientations". On a common line, the orientation test is
exactly a positive multiple of the signed edge vector. -/
private theorem host_step_step3_roots_step3_lift_step2_positive
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
    simp only [Bool.false_eq_true, false_iff, ↓reduceIte]
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

/-- Step 2 of the V4 proof of `host_step_step3_roots_step3_lift` (V4 2.3):
"equal affine spans". The direction space of a placed edge is generated
by the placed difference of its endpoints. -/
private theorem host_step_step3_roots_step3_lift_step2_segment_direction
    (T : E d ≃ᵃ[ℝ] E d) (x y : E d) :
    (affineSpan ℝ (T '' segment ℝ x y)).direction =
      Submodule.span ℝ {T.linear (y - x)} := by
  change (affineSpan ℝ (T.toAffineMap '' segment ℝ x y)).direction = _
  rw [← AffineSubspace.map_span T.toAffineMap,
    AffineSubspace.map_direction, direction_affineSpan, vectorSpan_segment,
    Submodule.map_span, Set.image_singleton]
  rfl

/-- Step 2 of the V4 proof of `host_step_step3_roots_step3_lift` (V4 2.3):
"with inherited orientations". An active chain's signed edge vector is
positively proportional to its provider's oriented flag direction. -/
private theorem host_step_step3_roots_step3_lift_step2_direction
    (U : HonestSource S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (c : OrientedChain f)
    (hc : U.ActiveChain P q f hf c) :
    ∃ a : ℝ, 0 < a ∧ U.counterDirection P q f hf =
      a • (q.2.val.prototypeFrame q.1).linear (chainVector c) := by
  let e : EdgeName S := ⟨q.2.val.ty, ⟨(c.chain.val.cell edgeIndex).val, by
    simp only [CellComplex.edges, Finset.mem_filter]
    exact ⟨(c.chain.val.cell edgeIndex).property, c.chain.val.dimension edgeIndex⟩⟩⟩
  let v := (q.2.val.prototypeFrame q.1).linear (edgeVector e)
  let u := U.counterDirection P q f hf
  have hv : v ≠ 0 := by
    exact fun h => (edgeVector_spec e).1
      ((q.2.val.prototypeFrame q.1).linear.injective (h.trans (map_zero _).symm))
  have hu : u ≠ 0 := by
    intro h
    have hzero := (U.providerPlacement P q f hf).linear.injective
      (h.trans (map_zero _).symm)
    exact (P.flag (U.recordIncidence P q f hf)).distinct
      (sub_eq_zero.mp hzero).symm
  have hspan := congrArg AffineSubspace.direction (hc.1 edgeIndex).choose_spec.2
  have he : (c.chain.val.cell edgeIndex).val.carrier =
      segment ℝ (Classical.choose (edge_endpoints_exist e)).1
        (Classical.choose (edge_endpoints_exist e)).2 :=
    (Classical.choose_spec (edge_endpoints_exist e)).2
  simp only [FramedNode.cell, he, (P.flag (U.recordIncidence P q f hf)).edge_eq,
    host_step_step3_roots_step3_lift_step2_segment_direction] at hspan
  change Submodule.span ℝ {v} = Submodule.span ℝ {u} at hspan
  have hline : u ∈ Submodule.span ℝ {v} := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self _
  have h := (host_step_step3_roots_step3_lift_step2_positive u v hu hv hline c.forward).mp hc.2
  simpa only [chainVector, apply_ite, map_neg] using h

/-- Step 3 of the V4 proof of `host_step_step3_roots_step3_lift` (V4 2.3):
"the chain ... of containing cells ... is active". Lift the geometric flag
through the honest hierarchy and retain its spans and signed edge direction. -/
private theorem host_step_step3_roots_step3_lift_step3_flag
    (U : HonestSource S) (q c : U.Node) (r : ℕ)
    (hc : U.hierarchy.ancestor c r = q)
    (F : FacetName S q.2.val.ty) (f : FacetName S c.2.val.ty)
    (hF : ¬ U.hierarchy.IsFault q F) (hf : ¬ U.hierarchy.IsFault c f)
    (hi : U.recordIncidence P c f hf = U.recordIncidence P q F hF)
    (hplace : U.providerPlacement P c f hf = U.providerPlacement P q F hF)
    (hsub : c.2.val.cell c.1 f.val ⊆ q.2.val.cell q.1 F.val)
    (s : OrientedChain f) (hs : U.ActiveChain P c f hf s) :
    ∃ t : OrientedChain F, U.ActiveChain P q F hF t ∧
      (∀ j, relint (c.2.val.cell c.1 (s.chain.val.cell j).val) ⊆
        relint (q.2.val.cell q.1 (t.chain.val.cell j).val)) ∧
      (∀ j, c.2.val.cell c.1 (s.chain.val.cell j).val ⊆
        q.2.val.cell q.1 (t.chain.val.cell j).val) ∧
      (∀ j, affineSpan ℝ (c.2.val.cell c.1 (s.chain.val.cell j).val) =
        affineSpan ℝ (q.2.val.cell q.1 (t.chain.val.cell j).val)) ∧
      ∃ a : ℝ, 0 < a ∧ (c.2.val.prototypeFrame c.1).linear (chainVector s) =
        a • (q.2.val.prototypeFrame q.1).linear (chainVector t) := by
  classical
  have cell_closure (N : FramedNode S) (n : ℕ) (e : Cell d) :
      closure (relint (N.cell n e)) = N.cell n e := by
    rw [FramedNode.cell, host_step_step3_roots_step2_relint_image]
    change closure ((N.prototypeFrame n).toHomeomorphOfFiniteDimensional ''
      relint e.carrier) = _
    rw [← Homeomorph.image_closure, e.flat.regularClosed]
    rfl
  have hflag (j : FlagIndex d) :
      U.providerPlacement P c f hf '' ((P.flag (U.recordIncidence P c f hf)).flag.cell j).val.carrier =
        U.providerPlacement P q F hF '' ((P.flag (U.recordIncidence P q F hF)).flag.cell j).val.carrier := by
    rw [hplace, hi]
  have hmem : s ∈ U.recordChains P c f hf := by
    simp only [HonestSource.recordChains, Finset.mem_filter]
    exact ⟨by simp [allOrientedChains], hs⟩
  obtain ⟨G, _, hG, _, _⟩ := chain_active_owner U P c f hf s hmem
  have ha : U.hierarchy.ActiveFlag c f hf s.chain.val G := by
    intro j
    obtain ⟨hs', hτ, _⟩ := hs.1 j
    refine ⟨hs', ?_⟩
    have cell_ext {e f : Cell d} (h : e.carrier = f.carrier) : e = f := by
      rcases e with ⟨K, k, hk⟩
      rcases f with ⟨L, l, hl⟩
      cases h
      have hd : k = l := hk.dimension.symm.trans hl.dimension
      cases hd
      rfl
    apply cell_ext
    exact ((U.hierarchy.servingChild c f hf).2.val.prototypeFrame
      (U.hierarchy.servingChild c f hf).1).injective.image_injective
        (hτ.trans (hG j).symm)
  obtain ⟨t, ht⟩ := U.hierarchy.active_flags_hereditary q c r hc F f hF hf hsub
    s.chain.val G ha
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
    · obtain ⟨x, hx⟩ := F'.val.flat.relint_nonempty.image (q.2.val.prototypeFrame q.1)
      have hx' : x ∈ relint (q.2.val.cell q.1 F'.val) := by
        rwa [FramedNode.cell, host_step_step3_roots_step2_relint_image]
      exact False.elim (((U.hierarchy.boundaryOffsets_downward q F').1
        (intrinsicInterior_subset hx')).2 (hint hx'))
  let tc : OrientedChain F := ⟨⟨t, htop⟩, decide (0 < inner ℝ (U.counterDirection P q F hF)
    ((q.2.val.prototypeFrame q.1).linear (edgeVector
      ⟨q.2.val.ty, ⟨(t.cell edgeIndex).val, by
        simp only [CellComplex.edges, Finset.mem_filter]
        exact ⟨(t.cell edgeIndex).property, t.dimension edgeIndex⟩⟩⟩)))⟩
  have hcontained (j : FlagIndex d) : c.2.val.cell c.1 (s.chain.val.cell j).val ⊆
      q.2.val.cell q.1 (t.cell j).val := by
    simpa only [cell_closure] using closure_mono (ht j).1
  have htc : U.ActiveChain P q F hF tc := by
    constructor
    · intro j
      obtain ⟨hrel, htF, hstr⟩ := ht j
      have hstr' := hstr.trans ((hG j).trans (hflag j))
      refine ⟨htF, hstr', ?_⟩
      have htstr : q.2.val.cell q.1 (t.cell j).val ⊆
          U.providerPlacement P q F hF ''
            ((P.flag (U.recordIncidence P q F hF)).flag.cell j).val.carrier := by
        have h := closure_mono (U.hierarchy.stratumMap_spec q F hF (t.cell j) htF).1
        simp only [cell_closure] at h
        exact h.trans_eq hstr'
      have hCspan := (hs.1 j).choose_spec.2.trans (congrArg (affineSpan ℝ) (hflag j))
      apply le_antisymm (affineSpan_mono ℝ htstr)
      exact hCspan.symm.trans_le (affineSpan_mono ℝ (hcontained j))
    · exact decide_eq_true_iff
  refine ⟨tc, htc, fun j => (ht j).1, hcontained, ?_, ?_⟩
  · intro j
    exact (hs.1 j).choose_spec.2.trans
      ((congrArg (affineSpan ℝ) (hflag j)).trans (htc.1 j).choose_spec.2.symm)
  · obtain ⟨a, ha, hsa⟩ := host_step_step3_roots_step3_lift_step2_direction U c f hf s hs
    obtain ⟨b, hb, htb⟩ := host_step_step3_roots_step3_lift_step2_direction U q F hF tc htc
    have hdir : U.counterDirection P c f hf = U.counterDirection P q F hF := by
      unfold HonestSource.counterDirection
      rw [hplace, hi]
    refine ⟨b / a, div_pos hb ha, ?_⟩
    have heq := hsa.symm.trans (hdir.trans htb)
    calc
      _ = a⁻¹ • (a • (c.2.val.prototypeFrame c.1).linear (chainVector s)) := by
        rw [inv_smul_smul₀ (ne_of_gt ha)]
      _ = a⁻¹ • (b • (q.2.val.prototypeFrame q.1).linear (chainVector tc)) :=
        congrArg (a⁻¹ • ·) heq
      _ = _ := by rw [smul_smul, ← div_eq_inv_mul]

/-- Step 4 of the V4 proof of `host_step_step3_roots_step3_lift` (V4 3.6, F1; V4 2.3):
"with the same affine spans, orientation and sides". For one consecutive
pair of listed flag cells, inherited relative interiors preserve the local
side in their common upper affine span. -/
private theorem host_step_step3_roots_step3_lift_step4_coface_side
    {A B : S.ι} (F : FacetFlag S A) (G : FacetFlag S B)
    (φ ψ : E d ≃ᵃ[ℝ] E d) (k : FlagStep d)
    (hlow : relint (φ '' (F.cell ⟨k.val, k.property.1, by omega⟩).val.carrier) ⊆
      relint (ψ '' (G.cell ⟨k.val, k.property.1, by omega⟩).val.carrier))
    (hhigh : φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier ⊆
      ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier)
    (hspan : affineSpan ℝ (φ '' (F.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier) =
      affineSpan ℝ (ψ '' (G.cell ⟨k.val + 1, by omega, k.property.2⟩).val.carrier)) :
    φ.linear '' flagSide F k = ψ.linear '' flagSide G k := by
  sorry

/-- Step 5 of the V4 proof of `host_step_step3_roots_step3_lift` (V4 3.6; V4 1.0(a)):
"lies on the j-side ... as u_m contained in B_m does". A local half-ball
has the corresponding closed half-space as its radial tangent cone. -/
private theorem host_step_step3_roots_step3_lift_step5_halfball
    (K : Set (E d)) (p v : E d) (r : ℝ) (hr : 0 < r)
    (hlocal : K ∩ ball p r = {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p r) :
    tangentCone K p = {u | 0 ≤ inner ℝ v u} := by
  ext u
  let δ := r / (‖u‖ + 1)
  have hden : 0 < ‖u‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hr hden
  have hnear (t : ℝ) (ht : 0 < t) (htδ : t < δ) : p + t • u ∈ ball p r := by
    change dist (p + t • u) p < r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have := (lt_div_iff₀ hden).mp htδ
    nlinarith [norm_nonneg u]
  constructor
  · rintro ⟨ε, hε, hmem⟩
    let t := min ε δ / 2
    have ht : 0 < t := div_pos (lt_min hε hδ) (by norm_num)
    have htε : t < ε := lt_of_lt_of_le (by dsimp [t]; linarith [lt_min hε hδ])
      (min_le_left ε δ)
    have htδ : t < δ := lt_of_lt_of_le (by dsimp [t]; linarith [lt_min hε hδ])
      (min_le_right ε δ)
    have hm : p + t • u ∈ {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p r :=
      hlocal ▸ ⟨hmem t ht htε, hnear t ht htδ⟩
    have hnonneg := hm.1
    change 0 ≤ inner ℝ v (p + t • u - p) at hnonneg
    rw [add_sub_cancel_left, inner_smul_right] at hnonneg
    exact nonneg_of_mul_nonneg_right hnonneg ht
  · intro hu
    refine ⟨δ, hδ, fun t ht htδ => ?_⟩
    have hm : p + t • u ∈ K ∩ ball p r := by
      rw [hlocal]
      refine ⟨?_, hnear t ht htδ⟩
      change 0 ≤ inner ℝ v (p + t • u - p)
      rw [add_sub_cancel_left, inner_smul_right]
      exact mul_nonneg ht.le hu
    exact hm.1

/-- Step 5 of the V4 proof of `host_step_step3_roots_step3_lift` (V4 3.6; V4 1.0(a)):
"the same ... side". Inclusion between two nontrivial closed linear
half-spaces forces equality. -/
private theorem host_step_step3_roots_step3_lift_step5_halfspace
    (f g : E d →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (hsub : {x | 0 ≤ f x} ⊆ {x | 0 ≤ g x}) :
    {x | 0 ≤ f x} = {x | 0 ≤ g x} ∨ g = 0 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    apply hf
    ext v
    simpa using not_exists.mp h v
  let w := (f v)⁻¹ • v
  have hw : f w = 1 := by simp [w, hv]
  have hg : 0 ≤ g w := hsub (by simp [hw])
  have heq (x : E d) : g x = f x * g w := by
    have hz : f (x - f x • w) = 0 := by simp [hw]
    have h₁ := hsub (a := x - f x • w) (by simp [hz])
    have h₂ := hsub (a := -(x - f x • w)) (by change 0 ≤ f (-(x - f x • w)); rw [map_neg, hz]; simp)
    simp only [Set.mem_setOf_eq, map_sub, map_smul, map_neg, smul_eq_mul] at h₁ h₂
    linarith
  by_cases hgw : g w = 0
  · right
    ext x
    simp [heq x, hgw]
  · left
    ext x
    simp only [Set.mem_setOf_eq, heq x]
    exact (mul_nonneg_iff_of_pos_right (lt_of_le_of_ne hg (Ne.symm hgw))).symm

/-- Step 5 of the V4 proof of `host_step_step3_roots_step3_lift` (V4 3.6; V4 1.0(a)):
"near a point of the relative interior". Every direction of a cell's
affine span is available in its radial tangent cone at such a point. -/
private theorem host_step_step3_roots_step3_lift_step5_relint_directions
    (K : Set (E d)) (p : E d) (hp : p ∈ relint K) :
    (cellDirection K : Set (E d)) ⊆ tangentCone K p := by
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hq)
  intro u hu
  let δ := r / (‖u‖ + 1)
  have hden : 0 < ‖u‖ + 1 := by positivity
  refine ⟨δ, div_pos hr hden, fun t ht htδ => ?_⟩
  have hmem : q.val + t • u ∈ affineSpan ℝ K := by
    simpa only [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction ((cellDirection K).smul_mem t hu) q.property
  apply hball (a := ⟨q.val + t • u, hmem⟩)
  change dist (q.val + t • u) q.val < r
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have := (lt_div_iff₀ hden).mp htδ
  nlinarith [norm_nonneg u]

/-- Step 5 of the V4 proof of `host_step_step3_roots_step3_lift` (V4 3.6; V4 1.0(a)):
"the recorded side". The inward half-space is constant along the connected
relative interior of one listed facet. -/
private theorem host_step_step3_roots_step3_lift_step5_facet_cone
    (A : S.ι) (f : FacetName S A) (p q : E d)
    (hp : p ∈ relint f.val.carrier) (hq : q ∈ relint f.val.carrier) :
    tangentCone (S.proto A).carrier p = tangentCone (S.proto A).carrier q := by
  let R := relint f.val.carrier
  let cone : R → Set (E d) := fun x => tangentCone (S.proto A).carrier x.val
  have hsub : f.val.carrier ⊆ (S.proto A).carrier :=
    host_step_step1_seed_step2_cell_subset A f.val (Finset.mem_filter.mp f.property).1
  have hloc : IsLocallyConstant cone := by
    apply (IsLocallyConstant.iff_exists_open cone).mpr
    intro x
    obtain ⟨r, hr, v, _, _, _, hlocal⟩ :=
      facet_halfball (S.proto A) (S.cx A) f.val f.property x.val x.property
    have hc := host_step_step3_roots_step3_lift_step5_halfball _ _ v r hr hlocal
    have hnormal (u : E d) (hu : u ∈ cellDirection f.val.carrier) : inner ℝ v u = 0 := by
      have hnonneg (w : E d) (hw : w ∈ cellDirection f.val.carrier) : 0 ≤ inner ℝ v w := by
        have h := host_step_step1_seed_step5_trace_step1_tangent_mono hsub x.val
          (host_step_step3_roots_step3_lift_step5_relint_directions _ _ x.property hw)
        simpa only [hc, Set.mem_setOf_eq] using h
      have h₁ := hnonneg u hu
      have h₂ := hnonneg (-u) ((cellDirection f.val.carrier).neg_mem hu)
      rw [inner_neg_right] at h₂
      linarith
    refine ⟨Subtype.val ⁻¹' ball x.val r, isOpen_ball.preimage continuous_subtype_val,
      by simpa only [Set.mem_preimage, mem_ball, dist_self] using hr, ?_⟩
    intro y hy
    have hyx : inner ℝ v (y.val - x.val) = 0 := hnormal _
      (AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ _ (intrinsicInterior_subset y.property))
        (subset_affineSpan ℝ _ (intrinsicInterior_subset x.property)))
    have hδ : 0 < r - dist y.val x.val := sub_pos.mpr hy
    have hball : ball y.val (r - dist y.val x.val) ⊆ ball x.val r := by
      intro z hz
      change dist z x.val < r
      have ht := dist_triangle z y.val x.val
      change dist z y.val < r - dist y.val x.val at hz
      linarith
    have htranslate (z : E d) : inner ℝ v (z - x.val) = inner ℝ v (z - y.val) := by
      have he : z - x.val = (z - y.val) + (y.val - x.val) := by module
      rw [he, inner_add_right, hyx, add_zero]
    have hlocal' : (S.proto A).carrier ∩ ball y.val (r - dist y.val x.val) =
        {z | 0 ≤ inner ℝ v (z - y.val)} ∩ ball y.val (r - dist y.val x.val) := by
      ext z
      constructor
      · rintro ⟨hz, hzball⟩
        have hm : z ∈ {z | 0 ≤ inner ℝ v (z - x.val)} ∩ ball x.val r :=
          hlocal ▸ ⟨hz, hball hzball⟩
        exact ⟨by simpa only [Set.mem_setOf_eq, htranslate z] using hm.1, hzball⟩
      · rintro ⟨hz, hzball⟩
        have hm : z ∈ (S.proto A).carrier ∩ ball x.val r := by
          rw [hlocal]
          exact ⟨by simpa only [Set.mem_setOf_eq, htranslate z] using hz, hball hzball⟩
        exact ⟨hm.1, hzball⟩
    exact (host_step_step3_roots_step3_lift_step5_halfball _ _ v _ hδ hlocal').trans hc.symm
  letI : PreconnectedSpace R := isPreconnected_iff_preconnectedSpace.mp
    f.val.flat.relint_connected.isPreconnected
  exact hloc.apply_eq_of_preconnectedSpace ⟨p, hp⟩ ⟨q, hq⟩

/-- Step 5 of the V4 proof of `host_step_step3_roots_step3_lift` (V4 3.6; V4 1.0(a)):
"B_m lies on the j-side ... as u_m contained in B_m does". Contained
placed domains with an inherited facet have the same inward tangent side. -/
private theorem host_step_step3_roots_step3_lift_step5_inward
    (A B : S.ι) (f : FacetName S A) (F : FacetName S B)
    (φ ψ : E d ≃ᵃ[ℝ] E d)
    (hsub : φ '' (S.proto A).carrier ⊆ ψ '' (S.proto B).carrier)
    (hrel : relint (φ '' f.val.carrier) ⊆ relint (ψ '' F.val.carrier)) :
    φ.linear '' tangentCone (S.proto A).carrier (cellAnchor f.val) =
      ψ.linear '' tangentCone (S.proto B).carrier (cellAnchor F.val) := by
  let p := cellAnchor f.val
  let q := ψ.symm (φ p)
  have hp : p ∈ relint f.val.carrier := cellAnchor_mem _
  have hq : q ∈ relint F.val.carrier := by
    have h := hrel (by rw [host_step_step3_roots_step2_relint_image]; exact ⟨p, hp, rfl⟩)
    rw [host_step_step3_roots_step2_relint_image] at h
    obtain ⟨z, hz, he⟩ := h
    simpa only [q, ← he, AffineEquiv.symm_apply_apply] using hz
  have hpq : ψ q = φ p := ψ.apply_symm_apply _
  obtain ⟨r, hr, v, hv, _, _, hlocal⟩ :=
    facet_halfball (S.proto A) (S.cx A) f.val f.property p hp
  obtain ⟨s, hs, w, hw, _, _, hlocal'⟩ :=
    facet_halfball (S.proto B) (S.cx B) F.val F.property q hq
  have hcp := host_step_step3_roots_step3_lift_step5_halfball _ _ v r hr hlocal
  have hcq := host_step_step3_roots_step3_lift_step5_halfball _ _ w s hs hlocal'
  let l : E d →ₗ[ℝ] ℝ := (innerₛₗ ℝ v).comp φ.linear.symm.toLinearMap
  let m : E d →ₗ[ℝ] ℝ := (innerₛₗ ℝ w).comp ψ.linear.symm.toLinearMap
  have himage (L : E d ≃ₗ[ℝ] E d) (v : E d) :
      L '' {z | 0 ≤ inner ℝ v z} = {z | 0 ≤ inner ℝ v (L.symm z)} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [Set.mem_setOf_eq, LinearEquiv.symm_apply_apply] using hy
    · intro hz
      exact ⟨L.symm z, hz, L.apply_symm_apply z⟩
  have hl : φ.linear '' tangentCone (S.proto A).carrier p = {z | 0 ≤ l z} := by
    rw [hcp, himage]
    rfl
  have hm : ψ.linear '' tangentCone (S.proto B).carrier q = {z | 0 ≤ m z} := by
    rw [hcq, himage]
    rfl
  have hlne : l ≠ 0 := by
    intro h
    have he := congrArg (fun k : E d →ₗ[ℝ] ℝ => k (φ.linear v)) h
    change inner ℝ v (φ.linear.symm (φ.linear v)) = 0 at he
    rw [LinearEquiv.symm_apply_apply, real_inner_self_eq_norm_sq, hv] at he
    norm_num at he
  have hmne : m ≠ 0 := by
    intro h
    have he := congrArg (fun k : E d →ₗ[ℝ] ℝ => k (ψ.linear w)) h
    change inner ℝ w (ψ.linear.symm (ψ.linear w)) = 0 at he
    rw [LinearEquiv.symm_apply_apply, real_inner_self_eq_norm_sq, hw] at he
    norm_num at he
  have hcones : {z | 0 ≤ l z} ⊆ {z | 0 ≤ m z} := by
    rw [← hl, ← hm,
      ← host_step_step1_seed_step8_transport_step1_tangent_image,
      ← host_step_step1_seed_step8_transport_step1_tangent_image, hpq]
    exact host_step_step1_seed_step5_trace_step1_tangent_mono hsub _
  have heq := (host_step_step3_roots_step3_lift_step5_halfspace l m hlne hcones).resolve_right hmne
  have hconst := host_step_step3_roots_step3_lift_step5_facet_cone B F q
    (cellAnchor F.val) hq (cellAnchor_mem _)
  exact hl.trans (heq.trans (hm.symm.trans (congrArg (ψ.linear '' ·) hconst)))

/-- Step 6 of the V4 proof of `host_step_step3_roots_step3_lift` (V4 2.3):
"that record is finite". A successful cell-keyed state readout supplies
its actual listed facet. -/
private theorem host_step_step3_roots_step3_lift_step6_readout
    (s : State P) (F : Cell d) (r : FacetRecord P)
    (hr : stateRecordAt s F = some r) :
    ∃ f : FacetName S s.ty, f.val = F ∧ s.facetRecord f = some r := by
  classical
  unfold stateRecordAt at hr
  split at hr
  · exact ⟨_, rfl, hr⟩
  · contradiction

/-- Step 3 of the V4 proof of `host_step_step3_roots` (V4 3.6; V4 2.3):
"a chain of u_m is active iff the chain of containing cells of B_m is active".
On one inherited boundary facet, (I2) lifts the finite record and the full active
chain, preserving incidence, side, beta, affine spans and all orientations. -/
private theorem host_step_step3_roots_step3_lift
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) (hD : Inv D)
    (H : FramedNode S) (ι : P.Incidence) (b : Bool) (u : host_step_Port C)
    (hu : host_step_portValid Y n H ι b u)
    (B' : Block Y n) (hB' : B' ∈ D.geometry.blocks)
    (hdesc : (tileNode u.1).IsDescendant 0 B'.node n)
    (F : FacetName S B'.node.ty)
    (hfacet : (tileNode u.1).cell 0 u.2.1.facet.val ⊆ B'.node.cell n F.val) :
    ∃ z : host_step_Chain P,
      z.1.facet.val = F.val ∧ host_step_rootValid D H ι b (⟨B', hB'⟩, z) ∧
      ∀ k, (tileNode u.1).cell 0 (u.2.2.chain.val.cell k).val ⊆
        B'.node.cell n (z.2.chain.val.cell k).val := by
  classical
  rcases u with ⟨v, r, c⟩
  rcases hu with ⟨hv, hrec, hty, hactive, hinc, hside, hbeta, halign, _⟩
  obtain ⟨U, hU, hs⟩ := host_step_step1_seed_step3_restricted_header_step1_realise
    (D.blockState B' hB') (hD.I1 B' hB').1 B'.node n
    (hD.I1 B' hB').2.1 (hD.I1 B' hB').2.2
  let q : U.Node := ⟨n, ⟨B'.node, hU⟩⟩
  obtain ⟨a, ha, w, htile⟩ := hdesc
  have han : a = n := by omega
  subst a
  have hcarrier : (tileNode v).carrier 0 ⊆ B'.node.carrier n := by
    rw [htile]
    have h := Set.subset_iUnion (fun w : S.RoleWord B'.node.ty n =>
      (S.nativeTile B'.node.ty n w).carrier 0) w
    rw [S.native_cover B'.node.ty n] at h
    have h' : (S.nativeTile B'.node.ty n w).frame ''
        (S.proto (S.nativeTile B'.node.ty n w).ty).carrier ⊆ S.supertile n B'.node.ty := by
      simpa [FramedNode.carrier, SubstSystem.supertile, placedSet] using h
    simpa [FramedNode.carrier, FramedNode.move, SubstSystem.supertile,
      placedSet, SubstSystem.nativeTile, Set.image_image] using
        (Set.image_mono (f := B'.node.frame) h')
  have hreal {k : ℕ} (hk : k = n) (hN : B'.node ∈ D.geometry.nodes k)
      (hU' : B'.node ∈ U.hierarchy.nodes k) :
      stateOf U P ⟨k, ⟨B'.node, hU'⟩⟩ = D.stateAt k B'.node hN := by
    subst k
    exact hs
  have hnode {k : ℕ} (hk : k = n) (hU' : B'.node ∈ U.hierarchy.nodes k) :
      (⟨k, ⟨B'.node, hU'⟩⟩ : U.Node) = q := by
    subst k
    rfl
  have hdescent : ∃ (hvD : tileNode v ∈ D.geometry.nodes 0)
      (hvU : tileNode v ∈ U.hierarchy.nodes 0),
      stateOf U P ⟨0, ⟨tileNode v, hvU⟩⟩ = D.stateAt 0 (tileNode v) hvD ∧
        U.hierarchy.ancestor ⟨0, ⟨tileNode v, hvU⟩⟩ n = q := by
    obtain ⟨hvD, hvU, hvstate, hanc⟩ :=
      host_step_step1_seed_step3_restricted_header_step2_descent D hD U 0 n B'.node
        (by simpa only [Nat.zero_add] using D.geometry.root_mem B' hB')
        (by simpa only [Nat.zero_add] using hU)
        (hreal (Nat.zero_add n) _ _) w
    rw [htile]
    exact ⟨hvD, hvU, hvstate, hanc.trans (hnode (Nat.zero_add n) _)⟩
  obtain ⟨hvD, hvU, hvstate, hanc⟩ := hdescent
  let t : U.Node := ⟨0, ⟨tileNode v, hvU⟩⟩
  have hleaf : stateOf U P t = (compilerLeaf C v).prePattern.state :=
    hvstate.trans (hD.I2.2 (tileNode v) hvD v hv rfl)
  have hr : stateRecordAt (stateOf U P t) r.facet.val = some r := by
    rw [hleaf]
    exact hrec
  obtain ⟨f, _, hr⟩ := host_step_step3_roots_step3_lift_step6_readout _ _ _ hr
  change U.facetRecordOf P t f = some r at hr
  unfold HonestSource.facetRecordOf at hr
  split at hr
  · contradiction
  · rename_i hf
    cases Option.some.inj hr
    obtain ⟨hF, hi, hb, hβ, hp⟩ := host_step_step3_roots_step3_lift_step1_provider
      U q t n hanc F f hf hfacet
    have hc := (record_chains_spec U P t f hf c).mp hactive
    obtain ⟨c', hc', hrel, hsub, hspans, a, ha, hvector⟩ :=
      host_step_step3_roots_step3_lift_step3_flag U q t n hanc F f hF hf hi hp hfacet c hc
    let z : host_step_Chain P := ⟨U.recordOf P q F hF, c'⟩
    refine ⟨z, rfl, ?_, hsub⟩
    refine ⟨?_, rfl, (record_chains_spec U P q F hF c').mpr hc',
      hi.symm.trans hinc, hb.symm.trans hside, ?_, ?_⟩
    · change stateRecordAt (D.blockState B' hB') F.val = some (U.recordOf P q F hF)
      rw [← hs]
      simp only [stateRecordAt, stateOf, dif_pos F.property]
      change U.facetRecordOf P q F = some (U.recordOf P q F hF)
      simp only [HonestSource.facetRecordOf, dif_neg hF]
    · exact (congrArg Fin.val hβ).symm.trans hbeta
    · refine ⟨fun j => (hspans j).symm.trans (halign.1 j), ?_, ?_, ?_⟩
      · intro j
        have h := host_step_step3_roots_step3_lift_step4_coface_side
          c.chain.val c'.chain.val (t.2.val.prototypeFrame t.1)
          (q.2.val.prototypeFrame q.1) j (hrel _) (hsub _) (hspans _)
        exact h.symm.trans (halign.2.1 j)
      · have h := halign.2.2.1
        change 0 < inner ℝ ((host_step_flagFrame H n ι b).linear (P.flag ι).direction)
          ((t.2.val.prototypeFrame t.1).linear (chainVector c)) at h
        rw [hvector, inner_smul_right] at h
        exact (mul_pos_iff_of_pos_left ha).mp h
      · have hcar : t.2.val.prototypeFrame t.1 '' (S.proto t.2.val.ty).carrier ⊆
            q.2.val.prototypeFrame q.1 '' (S.proto q.2.val.ty).carrier := by
          simpa only [FramedNode.carrier, FramedNode.prototypeFrame, SubstSystem.supertile,
            placedSet, Set.image_image] using hcarrier
        have hrelF : relint (t.2.val.prototypeFrame t.1 '' f.val.carrier) ⊆
            relint (q.2.val.prototypeFrame q.1 '' F.val.carrier) := by
          simpa only [c.chain.property, c'.chain.property] using hrel facetIndex
        have h := host_step_step3_roots_step3_lift_step5_inward _ _ f F
          (t.2.val.prototypeFrame t.1) (q.2.val.prototypeFrame q.1) hcar hrelF
        exact h.symm.trans halign.2.2.2

set_option maxHeartbeats 800000 in
/-- Step 3 of the V4 proof of `host_step_step3_roots_step4_endpoint` (V4 3.6, Containment; 1.7):
"the cell of B_m containing p_N in its relative interior is c_m".
In one honest source, a descendant vertex in an active root edge has that
edge's one-dimensional provider stratum. Uniqueness of relative-interior
strata is applied after identifying the inherited provider placement. -/
private theorem host_step_step3_roots_step4_endpoint_step3_source_stratum
    (U : HonestSource S) (q c : U.Node) (r : ℕ) (hc : U.hierarchy.ancestor c r = q)
    (F : FacetName S q.2.val.ty) (g : FacetName S c.2.val.ty)
    (hF : ¬ U.hierarchy.IsFault q F)
    (hsub : c.2.val.cell c.1 g.val ⊆ q.2.val.cell q.1 F.val)
    (z : OrientedChain F) (hz : U.ActiveChain P q F hF z)
    (v : VertexName S c.2.val.ty) (hv : v.val.carrier ⊆ g.val.carrier)
    (hp : c.2.val.prototypeFrame c.1 (vertexPoint v) ∈
      relint (q.2.val.cell q.1 (z.chain.val.cell edgeIndex).val)) :
    ∃ hg : ¬ U.hierarchy.IsFault c g,
      (U.recordTau P c g hg ⟨vertexCell v, hv⟩).val.val.dim = 1 := by
  classical
  obtain ⟨hg, hprovider, hbirth⟩ := U.hierarchy.provider_inherited q c r hc F g hF hsub
  have hinc := host_step_step1_seed_step3_restricted_header_step3_incidence P U
    c q g F hg hF hbirth hprovider
  have hplace : U.providerPlacement P c g hg = U.providerPlacement P q F hF := by
    exact congrArg₂ (fun (B : U.Node) (a : P.Incidence) =>
      P.incidencePlacement B.2.val B.1 a) hbirth hinc
  let e := U.recordTau P c g hg ⟨vertexCell v, hv⟩
  let E := ((P.flag (U.recordIncidence P q F hF)).flag.cell edgeIndex).val
  let x := c.2.val.prototypeFrame c.1 (vertexPoint v)
  obtain ⟨hs, hflag, _⟩ := hz.1 edgeIndex
  have hxE : x ∈ relint (U.providerPlacement P q F hF '' E.carrier) := by
    rw [← hflag]
    exact (U.hierarchy.stratumMap_spec q F hF _ hs).1 hp
  have hxv : x ∈ relint (c.2.val.cell c.1 (vertexCell v).val) := by
    change x ∈ relint (c.2.val.prototypeFrame c.1 '' v.val.carrier)
    rw [vertexPoint_spec, Set.image_singleton]
    simpa only [relint, intrinsicInterior_singleton] using (mem_singleton x)
  have hxe : x ∈ relint (U.providerPlacement P c g hg '' e.val.val.carrier) := by
    have he : U.providerPlacement P c g hg '' e.val.val.carrier =
        (U.hierarchy.servingChild c g hg).2.val.cell
          (U.hierarchy.servingChild c g hg).1
          (U.hierarchy.stratumMap c g hg (vertexCell v)
            (U.cellInFacet_placed c g ⟨vertexCell v, hv⟩)).val :=
      (Classical.choose_spec (U.recordTau_exists P c g hg ⟨vertexCell v, hv⟩)).1
    rw [he]
    exact (U.hierarchy.stratumMap_spec c g hg (vertexCell v)
      (U.cellInFacet_placed c g ⟨vertexCell v, hv⟩)).1 hxv
  rw [hplace, host_step_step3_roots_step2_relint_image] at hxe
  rw [host_step_step3_roots_step2_relint_image] at hxE
  obtain ⟨y, hy, hyx⟩ := hxE
  have hye : y ∈ relint e.val.val.carrier := by
    rw [← hyx] at hxe
    exact (U.providerPlacement P q F hF).injective.mem_set_image.mp hxe
  have hecell : e.val.val ∈ (S.cx (S.child (U.recordIncidence P q F hF).val.ty
      (U.recordIncidence P q F hF).val.left).ty).cells := by
    have ht := congrArg (fun a : P.Incidence => (S.child a.val.ty a.val.left).ty) hinc
    exact Eq.mp (congrArg (fun A => e.val.val ∈ (S.cx A).cells) ht) e.val.property
  have heE : e.val.val = E := by
    by_contra hne
    exact Set.disjoint_left.mp ((S.cx _).relint_disjoint _ hecell _
      ((P.flag (U.recordIncidence P q F hF)).flag.cell edgeIndex).property hne) hye hy
  refine ⟨hg, ?_⟩
  change e.val.val.dim = 1
  rw [heE]
  exact (P.flag (U.recordIncidence P q F hF)).flag.dimension edgeIndex

/-- Step 4 of the V4 proof of `host_step_step3_roots_step4_endpoint` (V4 3.6, Containment; 2.3):
"by (I2) and the restriction rule, tau_{u'}({p_N}) = tau_{f_m}(c_m) = h".
Realize a root state and descend by the deterministic child equations. Any
listed vertex of a native facet piece lying in the active root edge's relative
interior therefore reads a one-dimensional stratum. No endpoint event is used. -/
private theorem host_step_step3_roots_step4_endpoint_step4_restricted_stratum
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) (hD : Inv D)
    (B' : Block Y n) (hB' : B' ∈ D.geometry.blocks) (F : FacetName S B'.node.ty)
    (z : host_step_Chain P)
    (hr : stateRecordAt (D.blockState B' hB') F.val = some z.1)
    (hz : z.2 ∈ z.1.chains)
    (u : PlacedMarkedTile (systemM S P C)) (g : FacetName S (tileNode u).ty)
    (v : VertexName S (tileNode u).ty) (hpiece : Parser.IsFacetPiece Y n B'.node F u g)
    (hv : v.val.carrier ⊆ g.val.carrier)
    (hp : compilerFrame C u (vertexPoint v) ∈
      relint (B'.node.cell n (host_step_edge z).val)) :
    ∃ (s : FacetRecord P) (e : Cell d), leafRecord (compilerLeaf C u) g.val = some s ∧
      s.tauAt v.val = some e ∧ e.dim = 1 := by
  classical
  obtain ⟨U, hU, hs⟩ := host_step_step1_seed_step3_restricted_header_step1_realise
    (D.blockState B' hB') (hD.I1 B' hB').1 B'.node n
    (hD.I1 B' hB').2.1 (hD.I1 B' hB').2.2
  let q : U.Node := ⟨n, ⟨B'.node, hU⟩⟩
  rcases z with ⟨s, z⟩
  have hread : U.facetRecordOf P q F = some s := by
    rw [← hs] at hr
    simpa only [stateRecordAt, stateOf, dif_pos F.property] using hr
  have hF : ¬ U.hierarchy.IsFault q F := by
    intro hF
    simp only [HonestSource.facetRecordOf, dif_pos hF] at hread
    contradiction
  have hrecord : U.recordOf P q F hF = s := by
    simpa only [HonestSource.facetRecordOf, dif_neg hF, Option.some.injEq] using hread
  subst s
  have hactive : U.ActiveChain P q F hF z := (Finset.mem_filter.mp hz).2
  obtain ⟨r, hr, w, htile⟩ := hpiece.2.1
  have hrn : r = n := by omega
  subst r
  have hreal {k : ℕ} (hk : k = n) (hN : B'.node ∈ D.geometry.nodes k)
      (hU' : B'.node ∈ U.hierarchy.nodes k) :
      stateOf U P ⟨k, ⟨B'.node, hU'⟩⟩ = D.stateAt k B'.node hN := by
    subst k
    exact hs
  have hnode {k : ℕ} (hk : k = n) (hU' : B'.node ∈ U.hierarchy.nodes k) :
      (⟨k, ⟨B'.node, hU'⟩⟩ : U.Node) = q := by
    subst k
    rfl
  have hdesc : ∃ (huD : tileNode u ∈ D.geometry.nodes 0)
      (huU : tileNode u ∈ U.hierarchy.nodes 0),
      stateOf U P ⟨0, ⟨tileNode u, huU⟩⟩ = D.stateAt 0 (tileNode u) huD ∧
        U.hierarchy.ancestor ⟨0, ⟨tileNode u, huU⟩⟩ n = q := by
    obtain ⟨huD, huU, hstate, hanc⟩ :=
      host_step_step1_seed_step3_restricted_header_step2_descent D hD U 0 n B'.node
        (by simpa only [Nat.zero_add] using D.geometry.root_mem B' hB')
        (by simpa only [Nat.zero_add] using hU)
        (hreal (Nat.zero_add n) _ _) w
    rw [htile]
    exact ⟨huD, huU, hstate, hanc.trans (hnode (Nat.zero_add n) _)⟩
  obtain ⟨huD, huU, hstate, hanc⟩ := hdesc
  let c : U.Node := ⟨0, ⟨tileNode u, huU⟩⟩
  have hleaf : stateOf U P c = (compilerLeaf C u).prePattern.state :=
    hstate.trans (hD.I2.2 (tileNode u) huD u hpiece.1 rfl)
  obtain ⟨hg, hdim⟩ := host_step_step3_roots_step4_endpoint_step3_source_stratum
    U q c n hanc F g hF hpiece.2.2 z hactive v hv hp
  refine ⟨U.recordOf P c g hg, (U.recordTau P c g hg ⟨vertexCell v, hv⟩).val.val,
    ?_, ?_, hdim⟩
  · unfold leafRecord
    rw [← hleaf]
    simp only [stateRecordAt, stateOf, c, dif_pos g.property,
      HonestSource.facetRecordOf, dif_neg hg]
  · have hvc : v.val ∈ (S.cx (tileNode u).ty).cells := (vertexCell v).property
    simp only [FacetRecord.tauAt, HonestSource.recordOf, c,
      dif_pos hvc, dif_pos hv]
    rfl

/-- Step 5 of the V4 proof of `host_step_step3_roots_step4_endpoint` (V4 3.6, Containment; 2.5 E1):
"Row (E1) gives tau_{u'}({p_N}) = {p_N}". On a labelled primitive port,
the END row gives a zero-dimensional stratum at its listed apex vertex. -/
private theorem host_step_step3_roots_step4_endpoint_step5_row
    {l : LeafType P} {j : EndSlot l} (T : EndTemplate j) (hrow : endRow T)
    (port : PrimitivePort P) (hport : port ∈ T.geometry.primitivePorts)
    (l' : LeafType P) (hl' : (port.tile, l') ∈ T.configuration.tiles) :
    ∃ (s : FacetRecord P) (e : Cell d), leafRecord l' port.facet.val = some s ∧
      s.tauAt port.vertex.val = some e ∧ e.dim = 0 := by
  obtain ⟨s, hs, _, _, htau, _⟩ := hrow.1.1 port hport l' hl'
  exact ⟨s, port.providerVertex.val.val, hs, htau, port.provider_zero⟩

/-- Step 2 of the V4 proof of `host_step_step3_roots_step4_endpoint` (V4 3.6, F1):
"p_N lies in relint c_m". A point in the relative interior of one set
and the relative-interior closure of another gives overlapping relative
interiors when their affine spans agree. -/
private theorem host_step_step3_roots_step4_endpoint_step2_edge_overlap
    (K L : Set (E d)) (hspan : affineSpan ℝ K = affineSpan ℝ L)
    (p : E d) (hpK : p ∈ relint K) (hpL : p ∈ closure (relint L)) :
    (relint K ∩ relint L).Nonempty := by
  obtain ⟨x, hx, rfl⟩ := hpK
  have hind : Topology.IsInducing (Subtype.val : (affineSpan ℝ K) → E d) :=
    Topology.IsInducing.subtypeVal
  obtain ⟨O, hO, hpre⟩ :=
    hind.isOpen_iff.mp
      (isOpen_interior : IsOpen (interior ((↑) ⁻¹' K : Set (affineSpan ℝ K))))
  have hxO : x.val ∈ O := by
    change x ∈ (Subtype.val : (affineSpan ℝ K) → E d) ⁻¹' O
    rwa [hpre]
  obtain ⟨y, hyO, hyL⟩ := mem_closure_iff.mp hpL O hO hxO
  have hyspan : y ∈ affineSpan ℝ K := by
    rw [hspan]
    exact mem_affineSpan ℝ (intrinsicInterior_subset (𝕜 := ℝ) hyL)
  refine ⟨y, ⟨⟨y, hyspan⟩, ?_, rfl⟩, hyL⟩
  rw [← hpre]
  exact hyO

/-- Step 2 of the V4 proof of `host_step_step3_roots_step4_endpoint` (V4 3.6, F1; 1.1):
"the tiles of B_m with facet pieces in f_m". An aligned native port
through an interior point of the root edge overlaps the root's interior.
Disjointness of decoded blocks fixes its owner, and hereditary trace places
its facet in the named root facet. -/
private theorem host_step_step3_roots_step4_endpoint_step2_root_piece
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)
    (H : FramedNode S) (ι : P.Incidence) (b : Bool)
    (R : host_step_Root D) (hR : host_step_rootValid D H ι b R)
    (u : host_step_Port C) (hu : host_step_portValid Y n H ι b u)
    (p : E d) (hpR : p ∈ relint (host_step_rootEdge R))
    (hpu : p ∈ host_step_portEdge u) :
    ∃ (F : FacetName S R.1.val.node.ty) (g : FacetName S (tileNode u.1).ty),
      F.val = R.2.1.facet.val ∧ g.val = u.2.1.facet.val ∧
      Parser.IsFacetPiece Y n R.1.val.node F u.1 g := by
  classical
  have hRty := hR.2.1
  have huty := hu.2.2.1
  have hRa := hR.2.2.2.2.2.2
  have hua := hu.2.2.2.2.2.2.2.1
  have hspan : affineSpan ℝ (host_step_rootEdge R) =
      affineSpan ℝ (host_step_portEdge u) :=
    (hRa.1 edgeIndex).trans (hua.1 edgeIndex).symm
  have hcl : closure (relint (host_step_portEdge u)) = host_step_portEdge u := by
    change closure (relint ((tileNode u.1).prototypeFrame 0 ''
      (host_step_edge u.2).val.carrier)) = _
    rw [host_step_step3_roots_step2_relint_image]
    change closure (((tileNode u.1).prototypeFrame 0).toHomeomorphOfFiniteDimensional ''
      relint (host_step_edge u.2).val.carrier) = _
    rw [← Homeomorph.image_closure, (host_step_edge u.2).val.flat.regularClosed]
    rfl
  have hmeet := host_step_step3_roots_step4_endpoint_step2_edge_overlap
    (host_step_rootEdge R) (host_step_portEdge u) hspan p hpR (hcl.symm ▸ hpu)
  obtain ⟨hfaces, hinteriors⟩ := host_step_step3_roots_step2_flag_overlap
    R.1.val.node (tileNode u.1) n 0 R.2.2.chain.val u.2.2.chain.val
    hRty.symm huty.symm
    (fun k => (hRa.1 k).trans (hua.1 k).symm)
    (fun k => (hRa.2.1 k).trans (hua.2.1 k).symm)
    (by simpa only [R.2.2.chain.property, u.2.2.chain.property] using
      hRa.2.2.2.trans hua.2.2.2.symm) hmeet
  obtain ⟨B', hB', hsub, hdesc⟩ := host_step_step3_roots_step1_owner D.geometry u.1 hu.1
  have hcarrier : (tileNode u.1).carrier 0 = u.1.carrier := by
    rw [compilerFrame_carrier C u.1]
    simp [tileNode, FramedNode.carrier, SubstSystem.supertile, placedSet]
  have howner : B' = R.1.val := by
    by_contra hne
    obtain ⟨x, hxR, hxu⟩ := hinteriors
    rw [hcarrier] at hxu
    exact Set.disjoint_left.mp (D.geometry.disjoint hB' R.1.property hne)
      (interior_mono hsub hxu) hxR
  subst B'
  let F : FacetName S R.1.val.node.ty := ⟨R.2.1.facet.val, by
    rw [← hRty]; exact R.2.1.facet.property⟩
  let g : FacetName S (tileNode u.1).ty := ⟨u.2.1.facet.val, by
    rw [← huty]; exact u.2.1.facet.property⟩
  refine ⟨F, g, rfl, rfl, hu.1, hdesc, ?_⟩
  apply hereditary_trace R.1.val.node (tileNode u.1) n 0 hdesc F.val g.val
    (Finset.mem_filter.mp F.property).1 (Finset.mem_filter.mp g.property).1
  obtain ⟨x, hxR, hxu⟩ := hfaces facetIndex
  rw [R.2.2.chain.property] at hxR
  rw [u.2.2.chain.property] at hxu
  exact ⟨x, hxu, intrinsicInterior_subset (𝕜 := ℝ) hxR⟩

/-- Step 1 of the V4 proof of `host_step_step3_roots_step4_endpoint` (V4 3.6, Step 1):
"Row (E1) gives ... tau({p_0}) = {p_0}". Retain the provider-vertex
readout of the initial opposite port supplied by the honest endpoint trace,
together with its full positioned flag alignment. -/
private theorem host_step_step3_roots_step4_endpoint_step1_initial_port
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) :
    let H := proposedSibling D B hB f a
    let ι := a.record.incidence
    let b := !a.record.sideIndex
    let p := host_step_flagFrame H n ι b (P.flag ι).initial
    ∃ u : host_step_Port C, host_step_portValid Y n H ι b u ∧
      (host_step_portEnds u).1 = p ∧
      ∃ (v : VertexName S (tileNode u.1).ty) (e : Cell d),
        v.val.carrier ⊆ u.2.1.facet.val.carrier ∧
        compilerFrame C u.1 (vertexPoint v) = p ∧
        u.2.1.tauAt v.val = some e ∧ e.dim = 0 := by
  classical
  let Q := proposedParent D B hB
  let H := proposedSibling D B hB f a
  let ι := a.record.incidence
  let b := !a.record.sideIndex
  let p₀ := host_step_flagFrame H n ι b (P.flag ι).initial
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
  obtain ⟨r, hr, hrι, hrs, hrτ, hrβ⟩ := hrow.1.1 port hport l hl
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
  refine ⟨(t, ⟨r, c⟩), ?_, ?_, ?_⟩
  · refine ⟨ht, ?_, ?_, hc, hrι.trans hportι, hrb, ?_, ?_, q, ?_⟩
    · simpa only [hleaf, hfacet] using hr
    · simpa only [hnode] using hty
    · exact (congrArg Fin.val hrβ).trans hbeta₀
    · simpa only [hnode] using halign
    · simpa only [hleaf, hfacet] using hq
  · change compilerFrame C t (r.endpoints (host_step_edge ⟨r, c⟩)).1 = p₀
    simpa only [hφ, p₀, hframe] using hstart

  · let v : VertexName S (tileNode t).ty := ⟨port.vertex.val, by
      rw [hnode]
      change port.vertex.val ∈ (S.cx l.prototype).vertices
      rw [← T.configuration.types_match (port.tile, l) hl]
      exact port.vertex.property⟩
    have hvpoint : vertexPoint v = vertexPoint port.vertex := by
      apply Set.singleton_injective
      exact (vertexPoint_spec v).symm.trans (vertexPoint_spec port.vertex)
    have hv : v.val.carrier ⊆ r.facet.val.carrier := by
      rw [hfacet]
      exact port.onFacet
    have hvp : compilerFrame C t (vertexPoint v) = p₀ := by
      rw [hφ, hvpoint]
      change compilerFrame C t₀ (port.tile.frame (vertexPoint port.vertex)) = p₀
      rw [T.geometry.primitive_anchor port hport]
      have he := congrArg Cell.carrier T.vertex_eq
      rw [vertexPoint_spec, vertexPoint_spec] at he
      rw [Set.singleton_injective he]
      exact hjp₀
    exact ⟨v, port.providerVertex.val.val, hv, hvp, hrτ, port.provider_zero⟩

/-- Step 1 of the V4 proof of `host_step_step3_roots_step4_endpoint` (V4 3.6, 2a and Containment):
"u_m is a port on g at p_N" and "Row (E1) gives tau({p_N})={p_N}".
Retain the zero-dimensional stratum of an aligned native edge ending at the
terminal endpoint; this is the same template port used for its terminal counter. -/
private theorem host_step_step3_roots_step4_endpoint_step1_terminal_port
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f)
    (hend : host_step_endEvent Y n B f (proposedParent D B hB)
      (host_step_flagFrame (proposedSibling D B hB f a) n a.record.incidence
        (!a.record.sideIndex) (P.flag a.record.incidence).terminal))
    (u : host_step_Port C)
    (hu : host_step_portValid Y n (proposedSibling D B hB f a)
      a.record.incidence (!a.record.sideIndex) u)
    (hsub : host_step_portEdge u ⊆ host_step_flagEdge (proposedSibling D B hB f a) n
      a.record.incidence (!a.record.sideIndex))
    (hterminal : (host_step_portEnds u).2 =
      host_step_flagFrame (proposedSibling D B hB f a) n a.record.incidence
        (!a.record.sideIndex) (P.flag a.record.incidence).terminal) :
    ∃ (v : VertexName S (tileNode u.1).ty) (e : Cell d),
      v.val.carrier ⊆ u.2.1.facet.val.carrier ∧
      compilerFrame C u.1 (vertexPoint v) = (host_step_portEnds u).2 ∧
      u.2.1.tauAt v.val = some e ∧ e.dim = 0 := by
  classical
  let Q := proposedParent D B hB
  let H := proposedSibling D B hB f a
  let ι := a.record.incidence
  let b := !a.record.sideIndex
  let p := P.incidencePlacement Q (n + 1) ι (P.flag ι).terminal
  have hframe : host_step_flagFrame H n ι b = P.incidencePlacement Q (n + 1) ι :=
    host_step_step1_seed_step1_flag_frame Q n ι b
  have hι : ι.val.ty = Q.ty := (Parser.ageOneFacet_semantics D hD B hB f a).2.1
  change (host_step_portEnds u).2 = host_step_flagFrame H n ι b (P.flag ι).terminal
    at hterminal
  have hterminal' : (host_step_portEnds u).2 = p := by
    exact hterminal.trans (congrArg (fun e : E d ≃ᵃ[ℝ] E d => e (P.flag ι).terminal) hframe)
  obtain ⟨t, ht, j, θ, hpiece, hj, hsector, hθ, hactual⟩ := hend
  change Compiler.endVertex (compilerFrame C t) j =
    host_step_flagFrame H n ι b (P.flag ι).terminal at hj
  have hj' : Compiler.endVertex (compilerFrame C t) j = p := by
    simpa only [hframe] using hj
  have hpflag : p = host_step_flagFrame H n ι b (P.flag ι).terminal := by
    rw [hframe]
  have hp : B.node.Lists n p :=
    (host_step_step1_seed_step2_endpoint_piece Y n D hD B hB f a p (Or.inr hpflag)).1
  have hh := host_step_step2_strand_step2_terminal_counter_step1_header
    Y n D hD B hB f a p hp t j hpiece hj'
  change j.header = host_step_step1_seed_step1_header Q n (compilerFrame C t) p at hh
  obtain ⟨T, rfl, hrow⟩ := hθ
  rcases hu with ⟨hut, hread, hty, hc, hinc, hside, hβ, halign, hpacket⟩
  have hnear := host_step_step2_strand_step2_terminal_counter_step2_sector
    Q n ι b hι (tileNode u.1) u.2 hty halign hsub
    (by simpa [FramedNode.prototypeFrame, tileNode, host_step_portEnds] using hterminal')
  have hcarrier : (tileNode u.1).carrier 0 = u.1.carrier := by
    rw [compilerFrame_carrier C u.1]
    simp [tileNode, FramedNode.carrier, SubstSystem.supertile, placedSet]
  change Compiler.endSector (compilerFrame C t) j =
    (fun v => host_step_flagFrame H n ι b (P.flag ι).terminal + v) ''
      tangentCone (Q.carrier (n + 1)) (host_step_flagFrame H n ι b (P.flag ι).terminal)
    at hsector
  rw [hframe] at hsector
  have hnear' : Parser.ApproachesSector u.1 (Compiler.endVertex (compilerFrame C t) j)
      (Compiler.endSector (compilerFrame C t) j) := by
    intro ε hε
    rw [hj', hsector]
    simpa only [hframe, hcarrier] using hnear ε hε
  obtain ⟨⟨⟨N, l'⟩, hNl, hplaced⟩, _, _⟩ :=
    trigger_coverage Y hY t ht j T.configuration ⟨T, rfl, hrow⟩ hactual u.1 hut hnear'
  have hleaf : compilerLeaf C u.1 = l' := by
    rw [hplaced]
    exact (compiler_decode_unique C _ _).1
  have hφ : compilerFrame C u.1 = N.frame.trans (compilerFrame C t) := by
    rw [hplaced]
    exact (compiler_decode_unique C _ _).2
  have hnode : tileNode u.1 = N.move (compilerFrame C t) := by
    apply FramedNode.ext
    · change (compilerLeaf C u.1).prototype = N.ty
      rw [hleaf]
      exact (T.configuration.types_match _ hNl).symm
    · exact hφ
  have hN : N ∈ T.geometry.tiles := by
    rw [← T.tiles_eq]
    exact Finset.mem_image.mpr ⟨(N, l'), hNl, rfl⟩
  have hvertex : vertexPoint T.geometry.vertex = vertexPoint j.vertex := by
    apply Set.singleton_injective
    exact (vertexPoint_spec T.geometry.vertex).symm.trans
      ((congrArg Cell.carrier T.vertex_eq).trans (vertexPoint_spec j.vertex))
  have hapex : compilerFrame C t (vertexPoint T.geometry.vertex) = p := by
    rw [hvertex]
    exact hj'
  obtain ⟨port, hport, hportN, hfacet, hportι⟩ :=
    host_step_step2_strand_step2_terminal_counter_step3_primitive_port
      Q n ι b hι (compilerFrame C t) T.geometry T.honest_geometry
      (T.header_eq.trans hh) hapex N hN u.2
      (by simpa only [hnode, FramedNode.move] using hty)
      (by simpa only [hnode] using halign)
      (by simpa only [host_step_portEdge, hnode] using hsub)
      (by simpa only [host_step_portEnds, hφ] using hterminal')
  obtain ⟨r, e, hr, htau, hdim⟩ :=
    host_step_step3_roots_step4_endpoint_step5_row T hrow port hport l'
    (by simpa only [hportN] using hNl)
  have hrecord : r = u.2.1 := Option.some.inj (hr.symm.trans (by
    simpa only [hfacet, hleaf] using hread))
  subst r
  let v : VertexName S (tileNode u.1).ty := ⟨port.vertex.val, by
    have huN : (tileNode u.1).ty = N.ty := by
      have he := congrArg FramedNode.ty hnode
      exact he
    have he : port.tile.ty = (tileNode u.1).ty :=
      (congrArg FramedNode.ty hportN).trans huN.symm
    exact Eq.mp (congrArg (fun A => port.vertex.val ∈ (S.cx A).vertices) he)
      port.vertex.property⟩
  have hvpoint : vertexPoint v = vertexPoint port.vertex := by
    apply Set.singleton_injective
    exact (vertexPoint_spec v).symm.trans (vertexPoint_spec port.vertex)
  have hv : v.val.carrier ⊆ u.2.1.facet.val.carrier := by
    rw [← hfacet]
    exact port.onFacet
  have hvp : compilerFrame C u.1 (vertexPoint v) = p := by
    rw [hφ, hvpoint, ← hportN]
    change compilerFrame C t (port.tile.frame (vertexPoint port.vertex)) = p
    rw [T.geometry.primitive_anchor port hport]
    exact hapex
  exact ⟨v, e, hv, hvp.trans hterminal'.symm, htau, hdim⟩

/-- Step 4 of the V4 proof of `host_step_step3_roots` (V4 3.6, Containment):
"Row (E1) gives tau({p_N})={p_N}" but "by (I2) ... tau(c_m)=h".
An endpoint END event excludes that endpoint from the relative interior of
any aligned active opposite root edge. The initial endpoint uses the same argument. -/
private theorem host_step_step3_roots_step4_endpoint
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : P.K ≤ n) (D : DecodedLevel Y n) (hD : Inv D)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) (p : E d)
    (hp : p = host_step_flagFrame (proposedSibling D B hB f a) n
        a.record.incidence (!a.record.sideIndex) (P.flag a.record.incidence).initial ∨
      p = host_step_flagFrame (proposedSibling D B hB f a) n
        a.record.incidence (!a.record.sideIndex) (P.flag a.record.incidence).terminal)
    (hend : host_step_endEvent Y n B f (proposedParent D B hB) p)
    (R : host_step_Root D)
    (hR : host_step_rootValid D (proposedSibling D B hB f a)
      a.record.incidence (!a.record.sideIndex) R) :
    p ∉ relint (host_step_rootEdge R) := by
  classical
  intro hinterior
  let H := proposedSibling D B hB f a
  let ι := a.record.incidence
  let b := !a.record.sideIndex
  have hex : ∃ u : host_step_Port C, host_step_portValid Y n H ι b u ∧
      p ∈ host_step_portEdge u ∧
      ∃ (v : VertexName S (tileNode u.1).ty) (e : Cell d),
        v.val.carrier ⊆ u.2.1.facet.val.carrier ∧
        compilerFrame C u.1 (vertexPoint v) = p ∧
        u.2.1.tauAt v.val = some e ∧ e.dim = 0 := by
    rcases hp with rfl | rfl
    · obtain ⟨u, hu, hstart, v, e, hv, hvp, htau, hdim⟩ :=
        host_step_step3_roots_step4_endpoint_step1_initial_port Y hY n D hD B hB f a
      refine ⟨u, hu, ?_, v, e, hv, hvp, htau, hdim⟩
      rw [← hstart, host_step_step2_strand_step1_port_segment]
      exact left_mem_segment ℝ _ _
    · obtain ⟨he₀, heN, u₀, hu₀, hstart, hzero⟩ :=
        host_step_step1_seed Y hY n hn D hD B hB f a
      obtain ⟨m, u, _, hstrand⟩ := host_step_step2_strand Y hY n hn D hD B hB f a
        ⟨he₀, heN⟩ u₀ hu₀ hstart hzero
      rcases hstrand with ⟨hvalid, _, hterminal, _, _, _, hcontained, _⟩
      obtain ⟨v, e, hv, hvp, htau, hdim⟩ :=
        host_step_step3_roots_step4_endpoint_step1_terminal_port Y hY n D hD B hB f a
          hend (u (Fin.last m)) (hvalid _) (hcontained _) hterminal
      refine ⟨u (Fin.last m), hvalid _, ?_, v, e, hv, hvp.trans hterminal, htau, hdim⟩
      rw [← hterminal, host_step_step2_strand_step1_port_segment]
      exact right_mem_segment ℝ _ _
  obtain ⟨u, hu, hpu, v, e, hv, hvp, htau, hzero⟩ := hex
  obtain ⟨F, g, hF, hg, hpiece⟩ :=
    host_step_step3_roots_step4_endpoint_step2_root_piece D H ι b R hR u hu p hinterior hpu
  obtain ⟨s, e', hs, htau', hone⟩ :=
    host_step_step3_roots_step4_endpoint_step4_restricted_stratum D hD R.1.val R.1.property
      F R.2 (by simpa only [hF] using hR.1) hR.2.2.1 u.1 g v hpiece
      (by simpa only [hg] using hv) (by simpa only [hvp] using hinterior)
  have hrecord : s = u.2.1 := Option.some.inj (hs.symm.trans (by
    simpa only [hg] using hu.2.1))
  have he : e' = e := Option.some.inj (htau'.symm.trans (by
    simpa only [hrecord] using htau))
  rw [he, hzero] at hone
  omega

/-- Step 5 of the V4 proof of `host_step_step3_roots` (V4 3.6, Containment):
"a segment of aff h". A nondegenerate oriented segment admits an isometric
real coordinate with its endpoints at zero and a positive number. -/
private theorem host_step_step3_roots_step5_coordinate (p q : E d) (hpq : p ≠ q) :
    ∃ (φ : ℝ →ᵃⁱ[ℝ] E d) (L : ℝ), 0 < L ∧ φ 0 = p ∧ φ L = q := by
  let L := ‖q - p‖
  have hL : 0 < L := norm_pos_iff.mpr (sub_ne_zero.mpr hpq.symm)
  let v := L⁻¹ • (q - p)
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    exact inv_mul_cancel₀ hL.ne'
  let φ : ℝ →ᵃⁱ[ℝ] E d := {
    toAffineMap := {
      toFun := fun t => t • v + p
      linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight v
      map_vadd' := by
        intro t s
        change (s + t) • v + p = s • v + (t • v + p)
        rw [add_smul, add_assoc] }
    norm_map := by
      intro t
      change ‖t • v‖ = ‖t‖
      rw [norm_smul, hv, mul_one] }
  refine ⟨φ, L, hL, ?_, ?_⟩
  · change (0 : ℝ) • v + p = p
    simp
  · change L • (L⁻¹ • (q - p)) + p = q
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul, sub_add_cancel]

/-- Step 5 of the V4 proof of `host_step_step3_roots` (V4 3.6, Containment):
"one of p_0,p_N lies in relint c_m". In real coordinates relative interiors
of nondegenerate closed intervals are their open intervals. -/
private theorem host_step_step3_roots_step5_interval (a b : ℝ) (hab : a < b) :
    intrinsicInterior ℝ (Icc a b) = Ioo a b := by
  have hspan : affineSpan ℝ (Icc a b) = ⊤ :=
    (convex_Icc a b).interior_nonempty_iff_affineSpan_eq_top.mp
      (by rw [interior_Icc]; exact nonempty_Ioo.mpr hab)
  rw [intrinsicInterior, hspan]
  change (Homeomorph.Set.univ ℝ) ''
    interior ((Homeomorph.Set.univ ℝ) ⁻¹' Icc a b) = Ioo a b
  rw [(Homeomorph.Set.univ ℝ).image_interior]
  simp

/-- Step 5 of the V4 proof of `host_step_step3_roots` (V4 3.6, Containment):
"Otherwise ... one of p_0,p_N lies in relint c_m." A segment on the same
line, meeting the open reference segment and avoiding its endpoints in its
own relative interior, is contained in the reference segment. -/
private theorem host_step_step3_roots_step5_segment_trap
    (p q a b : E d) (hpq : p ≠ q) (hab : a ≠ b)
    (hspan : affineSpan ℝ (segment ℝ a b) = affineSpan ℝ (segment ℝ p q))
    (hp : p ∉ relint (segment ℝ a b)) (hq : q ∉ relint (segment ℝ a b))
    (hmeet : (segment ℝ a b ∩ relint (segment ℝ p q)).Nonempty) :
    segment ℝ a b ⊆ segment ℝ p q := by
  obtain ⟨φ, L, hL, hφ0, hφL⟩ := host_step_step3_roots_step5_coordinate p q hpq
  have href : segment ℝ p q = φ '' Icc 0 L := by
    simpa only [AffineIsometry.coe_toAffineMap, hφ0, hφL, segment_eq_Icc hL.le] using
      (image_segment ℝ φ.toAffineMap 0 L).symm
  have hrange : (affineSpan ℝ (segment ℝ p q) : Set (E d)) = Set.range φ := by
    have hfull : affineSpan ℝ (Icc 0 L) = ⊤ :=
      (convex_Icc 0 L).interior_nonempty_iff_affineSpan_eq_top.mp
        (by rw [interior_Icc]; exact nonempty_Ioo.mpr hL)
    rw [href, ← AffineIsometry.coe_toAffineMap, ← AffineSubspace.map_span, hfull]
    change φ '' (Set.univ : Set ℝ) = Set.range φ
    exact Set.image_univ
  have ha : a ∈ Set.range φ := by
    rw [← hrange, ← hspan]
    exact subset_affineSpan ℝ _ (left_mem_segment ℝ a b)
  have hb : b ∈ Set.range φ := by
    rw [← hrange, ← hspan]
    exact subset_affineSpan ℝ _ (right_mem_segment ℝ a b)
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  have hst : s ≠ t := fun h => hab (congrArg φ h)
  have hroot : segment ℝ (φ s) (φ t) = φ '' Icc (min s t) (max s t) := by
    simpa only [AffineIsometry.coe_toAffineMap, segment_eq_Icc'] using
      (image_segment ℝ φ.toAffineMap s t).symm
  have hrelroot : relint (segment ℝ (φ s) (φ t)) =
      φ '' Ioo (min s t) (max s t) := by
    rw [hroot, relint, φ.image_intrinsicInterior,
      host_step_step3_roots_step5_interval _ _ (min_lt_max.mpr hst)]
  have hrelref : relint (segment ℝ p q) = φ '' Ioo 0 L := by
    rw [href, relint, φ.image_intrinsicInterior,
      host_step_step3_roots_step5_interval _ _ hL]
  obtain ⟨x, hxroot, hxref⟩ := hmeet
  rw [hroot] at hxroot
  rw [hrelref] at hxref
  obtain ⟨v, hv, rfl⟩ := hxroot
  obtain ⟨w, hw, hwv⟩ := hxref
  have hwv' : w = v := φ.injective hwv
  subst w
  have hlo : 0 ≤ min s t := by
    by_contra h
    apply hp
    rw [hrelroot]
    exact ⟨0, ⟨lt_of_not_ge h, hw.1.trans_le hv.2⟩, hφ0⟩
  have hhi : max s t ≤ L := by
    by_contra h
    apply hq
    rw [hrelroot]
    exact ⟨L, ⟨hv.1.trans_lt hw.2, lt_of_not_ge h⟩, hφL⟩
  rw [hroot, href]
  exact Set.image_mono (fun _ hx => ⟨hlo.trans hx.1, hx.2.trans hhi⟩)

/-- Step 5 of the V4 proof of `host_step_step3_roots` (V4 3.6, Containment):
"p_0,p_N the initial and terminal vertices of h". Both side names give
the same transported oriented flag segment. -/
private theorem host_step_step3_roots_step5_flag_segment
    (H : FramedNode S) (n : ℕ) (ι : P.Incidence) (b : Bool) :
    host_step_flagEdge H n ι b =
      segment ℝ (host_step_flagFrame H n ι b (P.flag ι).initial)
        (host_step_flagFrame H n ι b (P.flag ι).terminal) := by
  have hcell := congrArg
    (fun K : Set (E d) => (S.child ι.val.ty (ι.val.sideIndex b)).frame.symm '' K)
    (P.sideFlag_eq ι b edgeIndex)
  change (S.child ι.val.ty (ι.val.sideIndex b)).frame.symm ''
      ((S.child ι.val.ty (ι.val.sideIndex b)).frame '' _) = _ at hcell
  rw [Set.image_image] at hcell
  simp only [AffineIsometryEquiv.symm_apply_apply,
    Set.image_id'] at hcell
  have hedge : host_step_flagEdge H n ι b =
      host_step_flagFrame H n ι b '' ((P.flag ι).flag.cell edgeIndex).val.carrier := by
    change H.prototypeFrame n '' _ = _
    rw [hcell]
    simp only [placedSet, Set.image_image]
    rfl
  rw [hedge, (P.flag ι).edge_eq]
  exact image_segment ℝ (host_step_flagFrame H n ι b).toAffineMap _ _

/-- Step 5 of the V4 proof of `host_step_step3_roots` (V4 3.6, Containment):
"Hence every root edge lies in h." The END exclusions and the common
line turn one point on the open flag edge into containment of the whole root. -/
private theorem host_step_step3_roots_step5_contained
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)
    (H : FramedNode S) (ι : P.Incidence) (b : Bool) (R : host_step_Root D)
    (hR : host_step_rootValid D H ι b R)
    (hp : host_step_flagFrame H n ι b (P.flag ι).initial ∉
      relint (host_step_rootEdge R))
    (hq : host_step_flagFrame H n ι b (P.flag ι).terminal ∉
      relint (host_step_rootEdge R))
    (hmeet : (host_step_rootEdge R ∩ relint (host_step_flagEdge H n ι b)).Nonempty) :
    host_step_rootEdge R ⊆ host_step_flagEdge H n ι b := by
  obtain ⟨ab, hab, he⟩ := edge_endpoints_exist
    (⟨R.2.1.ty, host_step_edge R.2⟩ : EdgeName S)
  let ψ := R.1.val.node.prototypeFrame n
  have hroot : host_step_rootEdge R = segment ℝ (ψ ab.1) (ψ ab.2) := by
    change ψ '' (host_step_edge R.2).val.carrier = _
    rw [he]
    exact image_segment ℝ ψ.toAffineMap _ _
  have hspan := hR.2.2.2.2.2.2.1 edgeIndex
  change affineSpan ℝ (host_step_rootEdge R) =
    affineSpan ℝ (host_step_flagEdge H n ι b) at hspan
  rw [hroot, host_step_step3_roots_step5_flag_segment] at hspan hmeet ⊢
  rw [hroot] at hp hq
  exact host_step_step3_roots_step5_segment_trap _ _ _ _
    (fun h => (P.flag ι).distinct ((host_step_flagFrame H n ι b).injective h))
    (fun h => hab (ψ.injective h)) hspan hp hq hmeet

/-- Step 6 of the V4 proof of `host_step_step3_roots` (V4 3.6, Disjointness):
"B_m=B_m'" and "cells of one complex with overlapping relative interiors".
Overlapping open root edges force the same block and the same positioned cell
at every level of their aligned chains. -/
private theorem host_step_step3_roots_step6_overlap
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)
    (H : FramedNode S) (ι : P.Incidence) (b : Bool) (R T : host_step_Root D)
    (hR : host_step_rootValid D H ι b R) (hT : host_step_rootValid D H ι b T)
    (hmeet : (relint (host_step_rootEdge R) ∩ relint (host_step_rootEdge T)).Nonempty) :
    R.1.val = T.1.val ∧ ∀ k,
      R.1.val.node.cell n (R.2.2.chain.val.cell k).val =
        T.1.val.node.cell n (T.2.2.chain.val.cell k).val := by
  classical
  have hRA := hR.2.2.2.2.2.2
  have hTA := hT.2.2.2.2.2.2
  obtain ⟨hfaces, hinter⟩ := host_step_step3_roots_step2_flag_overlap
    R.1.val.node T.1.val.node n n R.2.2.chain.val T.2.2.chain.val
    hR.2.1.symm hT.2.1.symm
    (fun k => (hRA.1 k).trans (hTA.1 k).symm)
    (fun k => (hRA.2.1 k).trans (hTA.2.1 k).symm)
    (by simpa only [R.2.2.chain.property, T.2.2.chain.property] using
      hRA.2.2.2.trans hTA.2.2.2.symm) hmeet
  have hblock : R.1.val = T.1.val := by
    by_contra hne
    obtain ⟨x, hx, hy⟩ := hinter
    exact Set.disjoint_left.mp (D.geometry.disjoint R.1.property T.1.property hne) hx hy
  refine ⟨hblock, ?_⟩
  have hnode := congrArg Block.node hblock
  intro k
  have hmemR : (R.2.2.chain.val.cell k).val ∈ (S.cx R.1.val.node.ty).cells := by
    rw [← hR.2.1]
    exact (R.2.2.chain.val.cell k).property
  have hmemT : (T.2.2.chain.val.cell k).val ∈ (S.cx R.1.val.node.ty).cells := by
    rw [hnode, ← hT.2.1]
    exact (T.2.2.chain.val.cell k).property
  have hcells : (R.2.2.chain.val.cell k).val = (T.2.2.chain.val.cell k).val := by
    by_contra hne
    have hd := (S.cx R.1.val.node.ty).relint_disjoint _ hmemR _ hmemT hne
    have hd' := Set.disjoint_image_of_injective (R.1.val.node.prototypeFrame n).injective hd
    have hh := hfaces k
    rw [← hnode] at hh
    simp only [FramedNode.cell, host_step_step3_roots_step2_relint_image] at hh
    obtain ⟨x, hx, hy⟩ := hh
    exact Set.disjoint_left.mp hd' hx hy
  rw [hnode, hcells]

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
  classical
  let H := proposedSibling D B hB f a
  let ι := a.record.incidence
  let b := !a.record.sideIndex
  rcases hu with ⟨hvalid, _, _, _, _, _, _, _, hcover, _, _, _, hinside⟩
  have lifts : ∀ i, ∃ V : host_step_Root D, host_step_rootValid D H ι b V ∧
      (tileNode (u i).1).IsDescendant 0 V.1.val.node n ∧
      ∀ k, (tileNode (u i).1).cell 0 ((u i).2.2.chain.val.cell k).val ⊆
        V.1.val.node.cell n (V.2.2.chain.val.cell k).val := by
    intro i
    obtain ⟨B', hB', hsub, hdesc⟩ :=
      host_step_step3_roots_step1_owner D.geometry (u i).1 (hvalid i).1
    obtain ⟨F, hF⟩ := host_step_step3_roots_step2_boundary D hD B hB f a
      (u i) (hvalid i) (hinside i) B' hB' hsub hdesc
    obtain ⟨z, _, hz, hchain⟩ := host_step_step3_roots_step3_lift D hD H ι b
      (u i) (hvalid i) B' hB' hdesc F hF
    exact ⟨(⟨B', hB'⟩, z), hz, hdesc, hchain⟩
  choose V hV hdesc hchain using lifts
  obtain ⟨he₀, heN, _⟩ := host_step_step1_seed Y hY n hn D hD B hB f a
  have hcontained : ∀ i, host_step_rootEdge (V i) ⊆ host_step_flagEdge H n ι b := by
    intro i
    apply host_step_step3_roots_step5_contained D H ι b (V i) (hV i)
    · exact host_step_step3_roots_step4_endpoint Y hY n hn D hD B hB f a _
        (Or.inl rfl) he₀ (V i) (hV i)
    · exact host_step_step3_roots_step4_endpoint Y hY n hn D hD B hB f a _
        (Or.inr rfl) heN (V i) (hV i)
    · have hne : (relint (host_step_portEdge (u i))).Nonempty := by
        change (relint ((tileNode (u i).1).prototypeFrame 0 ''
          (host_step_edge (u i).2).val.carrier)).Nonempty
        rw [host_step_step3_roots_step2_relint_image]
        exact (host_step_edge (u i).2).val.flat.relint_nonempty.image _
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hchain i edgeIndex (intrinsicInterior_subset (𝕜 := ℝ) hx), hinside i hx⟩
  let edges : Finset (Set (E d)) := Finset.univ.image (fun i => host_step_rootEdge (V i))
  let J := {K // K ∈ edges}
  have representatives : ∀ K : J, ∃ i, host_step_rootEdge (V i) = K.val := by
    intro K
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp K.property
    exact ⟨i, hi⟩
  choose rep hrep using representatives
  let e := (Fintype.equivFin J).symm
  let R : Fin (Fintype.card J) → host_step_Root D := fun j => V (rep (e j))
  let owner : Fin (m + 1) → Fin (Fintype.card J) := fun i =>
    e.symm ⟨host_step_rootEdge (V i), Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have howner : ∀ i, host_step_rootEdge (R (owner i)) = host_step_rootEdge (V i) := by
    intro i
    have h := hrep (e (owner i))
    simpa only [R, owner, Equiv.apply_symm_apply] using h
  refine ⟨Fintype.card J, R, owner, ?_⟩
  refine ⟨(fun j => hV (rep (e j))), (fun j => hcontained (rep (e j))), ?_, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hh := host_step_step3_roots_step6_overlap D H ι b (R i) (R j)
      (hV (rep (e i))) (hV (rep (e j))) ⟨x, hxi, hxj⟩
    have hedge : host_step_rootEdge (R i) = host_step_rootEdge (R j) := hh.2 edgeIndex
    apply hij
    apply e.injective
    apply Subtype.ext
    exact (hrep (e i)).symm.trans (hedge.trans (hrep (e j)))
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun j => hcontained (rep (e j)))
    · intro x hx
      rw [← hcover] at hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      apply Set.mem_iUnion.mpr
      refine ⟨owner i, ?_⟩
      rw [howner i]
      exact hchain i edgeIndex hxi
  · intro i
    have hne : (relint (host_step_rootEdge (V i))).Nonempty := by
      change (relint ((V i).1.val.node.prototypeFrame n ''
        (host_step_edge (V i).2).val.carrier)).Nonempty
      rw [host_step_step3_roots_step2_relint_image]
      exact (host_step_edge (V i).2).val.flat.relint_nonempty.image _
    obtain ⟨x, hx⟩ := hne
    have hh := host_step_step3_roots_step6_overlap D H ι b (V i) (R (owner i))
      (hV i) (hV (rep (e (owner i)))) ⟨x, hx, by rwa [howner i]⟩
    refine ⟨?_, ?_⟩
    · rw [← hh.1]
      exact hdesc i
    · intro k
      rw [← hh.2 k]
      exact hchain i k

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

/-- Step 1 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6):
"the root edges ... have disjoint relative interiors". In a common affine
span, the closure of one relative interior still misses the other one. -/
private theorem host_step_step4_lift_jump_step1_separation
    (A B : Set (E d)) (hspan : affineSpan ℝ A = affineSpan ℝ B)
    (hclosure : closure (relint A) = A)
    (hdis : Disjoint (relint A) (relint B)) : Disjoint A (relint B) := by
  let F := affineSpan ℝ A
  let a : Set F := (Subtype.val : F → E d) ⁻¹' A
  let b : Set F := (Subtype.val : F → E d) ⁻¹' B
  have ha : relint A = (Subtype.val : F → E d) '' interior a := rfl
  have hb : relint B = (Subtype.val : F → E d) '' interior b := by
    unfold relint intrinsicInterior
    rw [← hspan]
  have hd : Disjoint (interior a) (interior b) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hy
    rw [ha, hb] at hdis
    exact Set.disjoint_left.mp hdis ⟨x, hx, rfl⟩ ⟨x, hy, rfl⟩
  have hc : closure (interior a) = a := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
      ← ha, hclosure]
  have hd' : Disjoint a (interior b) := hc ▸ hd.closure_left isOpen_interior
  refine Set.disjoint_left.mpr ?_
  intro x hx hy
  rw [hb] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  exact Set.disjoint_left.mp hd' hx hy

/-- Step 2 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6):
"their edges lie in c ... by disjointness". A port touching the relative
interior of a root is owned by that root, even at a port endpoint. -/
private theorem host_step_step4_lift_jump_step2_owner
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)
    (H : FramedNode S) (ι : P.Incidence) (b : Bool)
    {m q : ℕ} (u : Fin (m + 1) → host_step_Port C)
    (R : Fin q → host_step_Root D) (owner : Fin (m + 1) → Fin q)
    (hR : host_step_rootCover D H ι b u R owner)
    (i : Fin (m + 1)) (j : Fin q) (x : E d)
    (hi : x ∈ host_step_portEdge (u i))
    (hj : x ∈ relint (host_step_rootEdge (R j))) : owner i = j := by
  by_contra hne
  have hsub : host_step_portEdge (u i) ⊆ host_step_rootEdge (R (owner i)) :=
    (hR.2.2.2.2 i).2 edgeIndex
  have hspan : affineSpan ℝ (host_step_rootEdge (R (owner i))) =
      affineSpan ℝ (host_step_rootEdge (R j)) :=
    ((hR.1 (owner i)).2.2.2.2.2.2.1 edgeIndex).trans
      ((hR.1 j).2.2.2.2.2.2.1 edgeIndex).symm
  have hclosure : closure (relint (host_step_rootEdge (R (owner i)))) =
      host_step_rootEdge (R (owner i)) := by
    rw [host_step_rootEdge, FramedNode.cell,
      host_step_step2_port_sites_step2_relint_image]
    change closure (((R (owner i)).1.val.node.prototypeFrame n).toHomeomorphOfFiniteDimensional
      '' relint (host_step_edge (R (owner i)).2).val.carrier) = _
    rw [← Homeomorph.image_closure, (host_step_edge (R (owner i)).2).val.flat.regularClosed]
    rfl
  exact Set.disjoint_left.mp
    (host_step_step4_lift_jump_step1_separation _ _ hspan hclosure
      (hR.2.2.1 hne)) (hsub hi) hj

/-- Step 3 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6, 1.13(c)):
"the restriction of S(B)'s profile". An honest root state with the correct
residue has a source realization at the root's actual height and full frame. -/
private theorem host_step_step4_lift_jump_step3_realise
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

/-- Step 3 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6, 2.3):
"by (I2)". Deterministic child equations identify every descendant state with
that of the same descendant in one fixed honest realization of the root. -/
private theorem host_step_step4_lift_jump_step3_descent
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

/-- Step 3 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6):
"the germs ... of the profile". Finite threshold counts on an interval
attain both endpoint germs and stay between them. The ordered-count premise
also handles a constant or decreasing affine coordinate. -/
private theorem host_step_step4_lift_jump_step3_interval_counts
    {N : ℕ} (p : Fin N → ℝ) (a b : ℝ)
    (hcounter : (Finset.univ.filter (fun i => p i ≤ a)).card ≤
      (Finset.univ.filter (fun i => p i < b)).card) :
    let lo := (Finset.univ.filter (fun i => p i ≤ a)).card
    let hi := (Finset.univ.filter (fun i => p i < b)).card
    let count := fun t : ℝ => (Finset.univ.filter (fun i =>
      p i < (1 - t) * a + t * b)).card
    (∀ t ∈ Ioo (0 : ℝ) 1, lo ≤ count t ∧ count t ≤ hi) ∧
      (∃ t ∈ Ioo (0 : ℝ) 1, count t = lo) ∧
      (∃ t ∈ Ioo (0 : ℝ) 1, count t = hi) := by
  classical
  dsimp only
  by_cases hab : a < b
  · have hbounds (x : ℝ) (hx : x ∈ Ioo a b) :
        (Finset.univ.filter (fun i => p i ≤ a)).card ≤
          (Finset.univ.filter (fun i => p i < x)).card ∧
        (Finset.univ.filter (fun i => p i < x)).card ≤
          (Finset.univ.filter (fun i => p i < b)).card := by
      constructor <;> apply Finset.card_le_card <;> intro i hi
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hi).2.trans_lt hx.1⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hi).2.trans hx.2⟩
    have hparam (x : ℝ) (hx : x ∈ Ioo a b) :
        ∃ t ∈ Ioo (0 : ℝ) 1, (1 - t) * a + t * b = x := by
      refine ⟨(x - a) / (b - a), ?_, ?_⟩
      · exact ⟨div_pos (sub_pos.mpr hx.1) (sub_pos.mpr hab),
          (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [hx.2])⟩
      · field_simp [sub_ne_zero.mpr hab.ne']
        ring
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      apply hbounds
      constructor <;> nlinarith [ht.1, ht.2]
    · let F := insert b ((Finset.univ.filter (fun i => a < p i)).image p)
      have hF : F.Nonempty := ⟨b, Finset.mem_insert_self _ _⟩
      have ham : a < F.min' hF := by
        apply (Finset.lt_min'_iff _ _).mpr
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hab
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          exact (Finset.mem_filter.mp hi).2
      obtain ⟨x, hax, hxm⟩ := exists_between ham
      have hxb : x < b := hxm.trans_le (Finset.min'_le F b (Finset.mem_insert_self _ _))
      have hfilter : Finset.univ.filter (fun i => p i < x) =
          Finset.univ.filter (fun i => p i ≤ a) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hi
          by_contra ha
          have hm : F.min' hF ≤ p i := Finset.min'_le F (p i)
            (Finset.mem_insert_of_mem (Finset.mem_image.mpr
              ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge ha⟩, rfl⟩))
          linarith
        · exact fun hi => hi.trans_lt hax
      obtain ⟨t, ht, heq⟩ := hparam x ⟨hax, hxb⟩
      exact ⟨t, ht, by rw [heq, hfilter]⟩
    · let F := insert a ((Finset.univ.filter (fun i => p i < b)).image p)
      have hF : F.Nonempty := ⟨a, Finset.mem_insert_self _ _⟩
      have hmb : F.max' hF < b := by
        apply (Finset.max'_lt_iff _ _).mpr
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hab
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          exact (Finset.mem_filter.mp hi).2
      obtain ⟨x, hmx, hxb⟩ := exists_between hmb
      have hax : a < x := (Finset.le_max' F a (Finset.mem_insert_self _ _)).trans_lt hmx
      have hfilter : Finset.univ.filter (fun i => p i < x) =
          Finset.univ.filter (fun i => p i < b) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun hi => hi.trans hxb
        · intro hi
          have hm : p i ≤ F.max' hF := Finset.le_max' F (p i)
            (Finset.mem_insert_of_mem (Finset.mem_image.mpr
              ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩))
          exact hm.trans_lt hmx
      obtain ⟨t, ht, heq⟩ := hparam x ⟨hax, hxb⟩
      exact ⟨t, ht, by rw [heq, hfilter]⟩
  · have hba : b ≤ a := le_of_not_gt hab
    have heq : (Finset.univ.filter (fun i => p i ≤ a)).card =
        (Finset.univ.filter (fun i => p i < b)).card := by
      apply le_antisymm hcounter
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((Finset.mem_filter.mp hi).2.trans_le hba).le⟩
    have hc (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
        (Finset.univ.filter (fun i => p i < (1 - t) * a + t * b)).card =
          (Finset.univ.filter (fun i => p i ≤ a)).card := by
      have hlo : b ≤ (1 - t) * a + t * b := by nlinarith [ht.1, ht.2]
      have hhi : (1 - t) * a + t * b ≤ a := by nlinarith [ht.1, ht.2]
      apply le_antisymm
      · apply Finset.card_le_card
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ((Finset.mem_filter.mp hi).2.trans_le hhi).le⟩
      · rw [heq]
        apply Finset.card_le_card
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hi).2.trans_le hlo⟩
    refine ⟨fun t ht => ?_, ⟨1 / 2, by norm_num, hc _ (by norm_num)⟩,
      ⟨1 / 2, by norm_num, (hc _ (by norm_num)).trans heq⟩⟩
    rw [hc t ht, heq]
    exact ⟨le_rfl, le_rfl⟩

/-- Step 3 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6):
"restrictions of the profile of c". An invertible affine frame preserves
order along a line when its direction is transported by the linear part. -/
private theorem host_step_step4_lift_jump_step3_line_order
    {d : ℕ} (φ : E d ≃ᵃ[ℝ] E d) (p q : E d) (hpq : p ≠ q)
    (x y : E d) (hx : x ∈ affineSpan ℝ ({p, q} : Set (E d)))
    (hy : y ∈ affineSpan ℝ ({p, q} : Set (E d))) :
    (inner ℝ (φ.linear (q - p)) (φ x - φ y) ≤ 0 ↔ inner ℝ (q - p) (x - y) ≤ 0) ∧
    (inner ℝ (φ.linear (q - p)) (φ x - φ y) < 0 ↔ inner ℝ (q - p) (x - y) < 0) := by
  obtain ⟨a, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
  obtain ⟨b, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy
  have hsub : AffineMap.lineMap p q a - AffineMap.lineMap p q b = (a - b) • (q - p) := by
    simp only [AffineMap.lineMap_apply_module']
    module
  have hmap : φ (AffineMap.lineMap p q a) - φ (AffineMap.lineMap p q b) =
      (a - b) • φ.linear (q - p) := by
    have hm := φ.toAffineMap.linearMap_vsub (AffineMap.lineMap p q a) (AffineMap.lineMap p q b)
    change φ.linear (AffineMap.lineMap p q a - AffineMap.lineMap p q b) = _ at hm
    rw [hsub, map_smul] at hm
    exact hm.symm
  have hv : 0 < inner ℝ (q - p) (q - p) := real_inner_self_pos.mpr (sub_ne_zero.mpr hpq.symm)
  have hw : 0 < inner ℝ (φ.linear (q - p)) (φ.linear (q - p)) :=
    real_inner_self_pos.mpr (φ.linear.map_ne_zero_iff.mpr (sub_ne_zero.mpr hpq.symm))
  rw [hmap, hsub, real_inner_smul_right, real_inner_smul_right]
  constructor <;> constructor <;> intro hh
  · have hc : a - b ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hc hv.le
  · have hc : a - b ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hc hw.le
  · have hc : a - b < 0 := by nlinarith
    exact mul_neg_of_neg_of_pos hc hv
  · have hc : a - b < 0 := by nlinarith
    exact mul_neg_of_neg_of_pos hc hw

/-- Step 3 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6):
"in relint c". The open affine interpolation parameterizes precisely the
relative interior of a nondegenerate edge. -/
private theorem host_step_step4_lift_jump_step3_segment_relint
    {d : ℕ} (p q : E d) (hpq : p ≠ q) :
    relint (segment ℝ p q) = AffineMap.lineMap p q '' Ioo (0 : ℝ) 1 := by
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
  have hir : intrinsicInterior ℝ (Icc (0 : ℝ) L) = Ioo 0 L := by
    have hspan : affineSpan ℝ (Icc (0 : ℝ) L) = ⊤ :=
      (convex_Icc 0 L).interior_nonempty_iff_affineSpan_eq_top.mp
        (by rw [interior_Icc]; exact nonempty_Ioo.mpr hL)
    rw [intrinsicInterior, hspan]
    change (Homeomorph.Set.univ ℝ) ''
      interior ((Homeomorph.Set.univ ℝ) ⁻¹' Icc 0 L) = Ioo 0 L
    rw [(Homeomorph.Set.univ ℝ).image_interior]
    simp
  rw [hseg, relint, φ.image_intrinsicInterior, hir]
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t / L, ⟨div_pos ht.1 hL, (div_lt_one hL).mpr ht.2⟩, ?_⟩
    have he := φ.toAffineMap.apply_lineMap (0 : ℝ) L (t / L)
    simpa [AffineMap.lineMap_apply_ring, hφ0, hφL, hL.ne'] using he.symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * L, ⟨mul_pos ht.1 hL, by nlinarith [ht.2]⟩, ?_⟩
    have he := φ.toAffineMap.apply_lineMap (0 : ℝ) L t
    simpa [AffineMap.lineMap_apply_ring, hφ0, hφL] using he

/-- Step 3 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6, 2.3):
"the restriction of S(B)'s profile". The serving child's full frame factors
through its side's isometry to the canonical provider coordinates. -/
private theorem host_step_step4_lift_jump_step3_serving_frame
    (U : HonestSource S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) :
    (U.hierarchy.servingChild q f hf).2.val.prototypeFrame
        (U.hierarchy.servingChild q f hf).1 =
      (S.child (U.recordIncidence P q f hf).val.ty
        ((U.recordIncidence P q f hf).val.sideIndex (U.recordSide P q f hf))).frame.toAffineEquiv.trans
      ((S.child (U.recordIncidence P q f hf).val.ty
        (U.recordIncidence P q f hf).val.left).frame.symm.toAffineEquiv.trans
        (U.providerPlacement P q f hf)) := by
  have hr := (Classical.choose_spec (U.recordSide_exists P q f hf)).1
  rw [host_step_step2_port_sites_step1_parent_frame]
  change (rolePlacement (U.hierarchy.nodeRole (U.hierarchy.servingChild q f hf))).trans
    ((U.hierarchy.birthParent q f hf).2.val.prototypeFrame (U.hierarchy.birthHeight q f hf)) = _
  rw [← hr]
  ext x
  simp [rolePlacement, HonestSource.providerPlacement, Params.incidencePlacement,
    PrimitiveIncidence.sideRole, HonestSource.recordSide]

set_option maxHeartbeats 800000 in
/-- Step 3 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6, §2.2(S4d)):
"the germs ... are restrictions of the profile of c". The shallow word's
endpoint counts equal the counts of physical source sites. Active-chain
alignment puts all compared points on the same line, so arbitrary invertible
expansion preserves the signs used by both counters. -/
private theorem host_step_step4_lift_jump_step3_shallow_germs
    (U : HonestSource S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (e : PrototypeEdge S q.2.val.ty)
    (he : (U.recordOf P q f hf).ChainActive (edgeCell e))
    (w : ShortProfile P) (hw : (U.recordOf P q f hf).counter = .inr w) :
    (U.recordOf P q f hf).kappaMinus e =
      (Finset.univ.filter (fun a : Fin P.N => inner ℝ (U.counterDirection P q f hf)
        (U.sitePoint P q f hf a -
          q.2.val.prototypeFrame q.1 ((U.recordOf P q f hf).endpoints e).1) ≤ 0)).card ∧
    (U.recordOf P q f hf).kappaPlus e =
      (Finset.univ.filter (fun a : Fin P.N => inner ℝ (U.counterDirection P q f hf)
        (U.sitePoint P q f hf a -
          q.2.val.prototypeFrame q.1 ((U.recordOf P q f hf).endpoints e).2) < 0)).card := by
  classical
  let ι := U.recordIncidence P q f hf
  let b := U.recordSide P q f hf
  let F := P.flag ι
  let K : Iso d := (S.child ι.val.ty (ι.val.sideIndex b)).frame.trans
    (S.child ι.val.ty ι.val.left).frame.symm
  let p₀ := K.symm F.initial
  let p₁ := K.symm F.terminal
  let Ψ := K.toAffineEquiv.trans (U.providerPlacement P q f hf)
  have hp : p₀ ≠ p₁ := fun h => F.distinct (K.symm.injective h)
  have hdir : p₁ - p₀ = (U.recordOf P q f hf).servingDirection := by
    have hh := K.symm.toAffineEquiv.toAffineMap.linearMap_vsub F.terminal F.initial
    change K.symm.linearIsometryEquiv (F.terminal - F.initial) = p₁ - p₀ at hh
    exact hh.symm
  have hdir' : Ψ.linear (p₁ - p₀) = U.counterDirection P q f hf := by
    change (U.providerPlacement P q f hf).linear (K.linearIsometryEquiv (p₁ - p₀)) = _
    have hh := K.toAffineEquiv.toAffineMap.linearMap_vsub p₁ p₀
    change K.linearIsometryEquiv (p₁ - p₀) = K p₁ - K p₀ at hh
    rw [hh]
    simp [p₀, p₁, HonestSource.counterDirection, F, ι, OrientedFullFlag.direction]
  have hserv : (U.hierarchy.servingChild q f hf).2.val.prototypeFrame
      (U.hierarchy.servingChild q f hf).1 = Ψ := by
    apply AffineEquiv.ext
    intro x
    exact congrArg (fun g : E d ≃ᵃ[ℝ] E d => g x)
      (host_step_step4_lift_jump_step3_serving_frame (P := P) U q f hf)
  have hword : w.word = U.downRoles q (U.hierarchy.firstProvider q f hf).1 := by
    change U.counterProfile P q f hf = .inr w at hw
    unfold HonestSource.counterProfile at hw
    dsimp only at hw
    split at hw
    · cases Sum.inr.inj hw
      rfl
    · contradiction
  have hframe : q.2.val.prototypeFrame q.1 = (wordPlacement w.word).trans Ψ := by
    rw [hword, host_step_step2_port_sites_step1_word_frame]
    exact congrArg (fun g => (wordPlacement (U.downRoles q
      (U.hierarchy.firstProvider q f hf).1)).trans g) hserv
  have hsite (a : Fin P.N) : U.sitePoint P q f hf a = Ψ (P.sites ι b a) := by
    rw [host_step_step2_port_sites_step1_site_frame, hserv]
  have hside : ((P.sideFlag ι b).cell edgeIndex).val.carrier = segment ℝ p₀ p₁ := by
    have hh := congrArg (fun A : Set (E d) =>
      (S.child ι.val.ty ι.val.left).frame.symm '' A) (P.sideFlag_eq ι b edgeIndex)
    have hK : K '' ((P.sideFlag ι b).cell edgeIndex).val.carrier =
        (F.flag.cell edgeIndex).val.carrier := by
      simpa [placedSet, Set.image_image, K, F] using hh
    have hh := congrArg (fun A : Set (E d) => K.symm '' A) hK
    simp only [Set.image_image, K.symm_apply_apply, Set.image_id'] at hh
    rw [F.edge_eq] at hh
    exact hh.trans (image_segment ℝ K.symm.toAffineEquiv.toAffineMap F.initial F.terminal)
  have hs (a : Fin P.N) : P.sites ι b a ∈ affineSpan ℝ ({p₀, p₁} : Set (E d)) := by
    have hh := intrinsicInterior_subset (P.sites_relint ι b a)
    rw [hside] at hh
    simpa only [← convexHull_pair, affineSpan_convexHull] using
      (subset_affineSpan ℝ (segment ℝ p₀ p₁) hh)
  obtain ⟨c, hc, hce⟩ := he
  have hspan : affineSpan ℝ (q.2.val.cell q.1 e.val) =
      affineSpan ℝ (Ψ '' segment ℝ p₀ p₁) := by
    obtain ⟨_, _, hh⟩ := ((record_chains_spec U P q f hf c).mp hc).1 edgeIndex
    rw [hce] at hh
    have hfedge : U.providerPlacement P q f hf '' (F.flag.cell edgeIndex).val.carrier =
        Ψ '' segment ℝ p₀ p₁ := by
      rw [F.edge_eq]
      change (U.providerPlacement P q f hf).toAffineMap '' segment ℝ F.initial F.terminal =
        Ψ.toAffineMap '' segment ℝ p₀ p₁
      rw [image_segment, image_segment]
      simp [Ψ, p₀, p₁]
    exact hh.trans (congrArg (affineSpan ℝ) hfedge)
  have hmem (y : E d) (hy : y ∈ e.val.carrier) :
      wordPlacement w.word y ∈ affineSpan ℝ ({p₀, p₁} : Set (E d)) := by
    have hh := subset_affineSpan ℝ (q.2.val.cell q.1 e.val) (Set.mem_image_of_mem _ hy)
    rw [hspan] at hh
    change q.2.val.prototypeFrame q.1 y ∈
      affineSpan ℝ (Ψ.toAffineMap '' segment ℝ p₀ p₁) at hh
    rw [← AffineSubspace.map_span] at hh
    change q.2.val.prototypeFrame q.1 y ∈ Ψ ''
      (affineSpan ℝ (segment ℝ p₀ p₁) : Set (E d)) at hh
    rw [hframe] at hh
    have hh := Ψ.injective.mem_set_image.mp hh
    simpa only [← convexHull_pair, affineSpan_convexHull] using hh
  have hends : ((U.recordOf P q f hf).endpoints e).1 ∈ e.val.carrier ∧
      ((U.recordOf P q f hf).endpoints e).2 ∈ e.val.carrier := by
    have hh := (Classical.choose_spec (edge_endpoints_exist (⟨q.2.val.ty, e⟩ : EdgeName S))).2
    rw [hh]
    unfold FacetRecord.endpoints
    split
    · exact ⟨left_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩
    · exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  have horder (a : Fin P.N) (y : E d) (hy : y ∈ e.val.carrier) :
      (inner ℝ (U.counterDirection P q f hf)
          (U.sitePoint P q f hf a - q.2.val.prototypeFrame q.1 y) ≤ 0 ↔
        inner ℝ (U.recordOf P q f hf).servingDirection
          (P.sites ι b a - wordPlacement w.word y) ≤ 0) ∧
      (inner ℝ (U.counterDirection P q f hf)
          (U.sitePoint P q f hf a - q.2.val.prototypeFrame q.1 y) < 0 ↔
        inner ℝ (U.recordOf P q f hf).servingDirection
          (P.sites ι b a - wordPlacement w.word y) < 0) := by
    have hh := host_step_step4_lift_jump_step3_line_order Ψ p₀ p₁ hp
      (P.sites ι b a) (wordPlacement w.word y) (hs a) (hmem y hy)
    rw [hdir', hdir] at hh
    simpa only [hsite, hframe, AffineEquiv.trans_apply] using hh
  constructor
  · rw [FacetRecord.kappaMinus, hw]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro a _
    exact (horder a _ hends.1).1.symm
  · rw [FacetRecord.kappaPlus, hw]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro a _
    exact (horder a _ hends.2).2.symm

/-- Step 3 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6, §2.2(S4d)):
"the germs ... of the profile of c". On one honest active edge, every
interior counter value lies between the endpoint germs, and both endpoint
germs occur at interior points sufficiently close to their endpoints. -/
private theorem host_step_step4_lift_jump_step3_source_range
    (U : HonestSource S) (q : U.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ U.hierarchy.IsFault q f) (e : PrototypeEdge S q.2.val.ty)
    (he : (U.recordOf P q f hf).ChainActive (edgeCell e)) :
    (∀ x ∈ relint (q.2.val.cell q.1 e.val),
      (U.recordOf P q f hf).kappaMinus e ≤ (U.sitesBefore P q f hf x).val ∧
        (U.sitesBefore P q f hf x).val ≤ (U.recordOf P q f hf).kappaPlus e) ∧
    (∃ x ∈ relint (q.2.val.cell q.1 e.val),
      (U.sitesBefore P q f hf x).val = (U.recordOf P q f hf).kappaMinus e) ∧
    (∃ x ∈ relint (q.2.val.cell q.1 e.val),
      (U.sitesBefore P q f hf x).val = (U.recordOf P q f hf).kappaPlus e) := by
  classical
  by_cases hm : P.siteDepth (U.recordIncidence P q f hf) (U.recordSide P q f hf) ≤
      (U.hierarchy.firstProvider q f hf).1
  · have hc := (record_mature_iff U P q f hf).mpr hm
    have hval (x : E d) (hx : x ∈ relint (q.2.val.cell q.1 e.val)) :
        (U.recordOf P q f hf).kappaMinus e = (U.sitesBefore P q f hf x).val ∧
        (U.recordOf P q f hf).kappaPlus e = (U.sitesBefore P q f hf x).val := by
      have hv := mature_counter_value U P q f hf hm (edgeCell e) he x hx
      simp [FacetRecord.kappaMinus, FacetRecord.kappaPlus, hc, hv]
    obtain ⟨x, hx⟩ : (relint (q.2.val.cell q.1 e.val)).Nonempty := by
      rw [FramedNode.cell, host_step_step2_port_sites_step2_relint_image]
      exact e.val.flat.relint_nonempty.image _
    refine ⟨fun y hy => ?_, ⟨x, hx, (hval x hx).1.symm⟩,
      ⟨x, hx, (hval x hx).2.symm⟩⟩
    exact ⟨(hval y hy).1.le, (hval y hy).2.ge⟩
  · obtain ⟨w, hw, _⟩ := (record_shallow_iff U P q f hf).mpr (lt_of_not_ge hm)
    have hgerms := host_step_step4_lift_jump_step3_shallow_germs U q f hf e he w hw
    let p₀ := q.2.val.prototypeFrame q.1 ((U.recordOf P q f hf).endpoints e).1
    let p₁ := q.2.val.prototypeFrame q.1 ((U.recordOf P q f hf).endpoints e).2
    let v := U.counterDirection P q f hf
    let sites := fun a : Fin P.N => inner ℝ v (U.sitePoint P q f hf a)
    let a := inner ℝ v p₀
    let b := inner ℝ v p₁
    have hlo : (U.recordOf P q f hf).kappaMinus e =
        (Finset.univ.filter (fun i => sites i ≤ a)).card := by
      rw [hgerms.1]
      simp only [inner_sub_right, sub_nonpos]
      rfl
    have hhi : (U.recordOf P q f hf).kappaPlus e =
        (Finset.univ.filter (fun i => sites i < b)).card := by
      rw [hgerms.2]
      simp only [inner_sub_right, sub_lt_zero]
      rfl
    have hord : (Finset.univ.filter (fun i => sites i ≤ a)).card ≤
        (Finset.univ.filter (fun i => sites i < b)).card := by
      rw [← hlo, ← hhi]
      exact (honest_counter_germs U P q f hf e he).1
    have hcounts := host_step_step4_lift_jump_step3_interval_counts sites a b hord
    have hegeom : ((U.recordOf P q f hf).endpoints e).1 ≠
          ((U.recordOf P q f hf).endpoints e).2 ∧
        e.val.carrier = segment ℝ ((U.recordOf P q f hf).endpoints e).1
          ((U.recordOf P q f hf).endpoints e).2 := by
      have hh := Classical.choose_spec (edge_endpoints_exist (⟨q.2.val.ty, e⟩ : EdgeName S))
      unfold FacetRecord.endpoints
      split
      · exact hh
      · exact ⟨hh.1.symm, hh.2.trans (segment_symm ℝ _ _)⟩
    have hp : p₀ ≠ p₁ := fun h => hegeom.1 ((q.2.val.prototypeFrame q.1).injective h)
    have hseg : q.2.val.cell q.1 e.val = segment ℝ p₀ p₁ := by
      rw [FramedNode.cell, hegeom.2]
      exact image_segment ℝ (q.2.val.prototypeFrame q.1).toAffineMap _ _
    have hrel : relint (q.2.val.cell q.1 e.val) =
        AffineMap.lineMap p₀ p₁ '' Ioo (0 : ℝ) 1 := by
      rw [hseg, host_step_step4_lift_jump_step3_segment_relint p₀ p₁ hp]
    have hcount (t : ℝ) :
        (U.sitesBefore P q f hf (AffineMap.lineMap p₀ p₁ t)).val =
          (Finset.univ.filter (fun i => sites i < (1 - t) * a + t * b)).card := by
      change (Finset.univ.filter (fun i : Fin P.N =>
        inner ℝ v (U.sitePoint P q f hf i - AffineMap.lineMap p₀ p₁ t) < 0)).card = _
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro i _
      simp only [inner_sub_right, sub_lt_zero, AffineMap.lineMap_apply_module,
        inner_add_right, real_inner_smul_right]
      rfl
    rw [hlo, hhi]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [hrel] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      rw [hcount]
      exact hcounts.1 t ht
    · obtain ⟨t, ht, hc⟩ := hcounts.2.1
      exact ⟨_, hrel.symm ▸ Set.mem_image_of_mem _ ht, (hcount t).trans hc⟩
    · obtain ⟨t, ht, hc⟩ := hcounts.2.2
      exact ⟨_, hrel.symm ▸ Set.mem_image_of_mem _ ht, (hcount t).trans hc⟩

/-- Step 3 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6, 2.3):
"the germs ... are restrictions of the profile of c". For two active chains
in one honest source, with the smaller chain on the larger one's boundary
track, each smaller-edge germ is bounded by the larger-edge germs. -/
private theorem host_step_step4_lift_jump_step3_source_bounds
    (U : HonestSource S) (B t : U.Node) (a : ℕ)
    (hanc : U.hierarchy.ancestor t a = B)
    (v z : host_step_Chain P)
    (hv : stateRecordAt (stateOf U P B) v.1.facet.val = some v.1)
    (hz : stateRecordAt (stateOf U P t) z.1.facet.val = some z.1)
    (hvc : v.2 ∈ v.1.chains) (hzc : z.2 ∈ z.1.chains)
    (hι : z.1.incidence = v.1.incidence) (hb : z.1.sideIndex = v.1.sideIndex)
    (hchain : ∀ k, t.2.val.cell t.1 (z.2.chain.val.cell k).val ⊆
      B.2.val.cell B.1 (v.2.chain.val.cell k).val) :
    v.1.kappaMinus (host_step_edge v) ≤ z.1.kappaMinus (host_step_edge z) ∧
      z.1.kappaPlus (host_step_edge z) ≤ v.1.kappaPlus (host_step_edge v) := by
  classical
  rcases v with ⟨rv, cv⟩
  rcases z with ⟨rz, cz⟩
  obtain ⟨F, _, hv⟩ := host_step_step3_readout _ _ _ hv
  obtain ⟨f, _, hz⟩ := host_step_step3_readout _ _ _ hz
  change U.facetRecordOf P B F = some rv at hv
  change U.facetRecordOf P t f = some rz at hz
  unfold HonestSource.facetRecordOf at hv hz
  split at hv
  · contradiction
  · rename_i hF
    cases Option.some.inj hv
    split at hz
    · contradiction
    · rename_i hf
      cases Option.some.inj hz
      have hsub : t.2.val.cell t.1 f.val ⊆ B.2.val.cell B.1 F.val := by
        simpa only [cv.chain.property, cz.chain.property] using hchain facetIndex
      obtain ⟨_, _, hbirth⟩ := U.hierarchy.provider_inherited B t a hanc F f hF hsub
      change U.recordIncidence P t f hf = U.recordIncidence P B F hF at hι
      change U.recordSide P t f hf = U.recordSide P B F hF at hb
      have hpos : U.providerPlacement P t f hf = U.providerPlacement P B F hF := by
        unfold HonestSource.providerPlacement CoherentHierarchy.birthHeight
        rw [hbirth, hι]
      have hcount (x : E d) : U.sitesBefore P t f hf x = U.sitesBefore P B F hF x := by
        apply Fin.ext
        change (Finset.univ.filter (fun a : Fin P.N =>
          inner ℝ (U.counterDirection P t f hf) (U.sitePoint P t f hf a - x) < 0)).card =
          (Finset.univ.filter (fun a : Fin P.N =>
          inner ℝ (U.counterDirection P B F hF) (U.sitePoint P B F hF a - x) < 0)).card
        unfold HonestSource.sitePoint HonestSource.counterDirection
        rw [hpos, hι, hb]
      let ev := host_step_edge ⟨U.recordOf P B F hF, cv⟩
      let ez := host_step_edge ⟨U.recordOf P t f hf, cz⟩
      have hspan : affineSpan ℝ (t.2.val.cell t.1 ez.val) =
          affineSpan ℝ (B.2.val.cell B.1 ev.val) := by
        obtain ⟨_, _, hvspan⟩ := ((record_chains_spec U P B F hF cv).mp hvc).1 edgeIndex
        obtain ⟨_, _, hzspan⟩ := ((record_chains_spec U P t f hf cz).mp hzc).1 edgeIndex
        change affineSpan ℝ (t.2.val.cell t.1 ez.val) = _ at hzspan
        change affineSpan ℝ (B.2.val.cell B.1 ev.val) = _ at hvspan
        rw [hpos, hι] at hzspan
        exact hzspan.trans hvspan.symm
      have hinside : relint (t.2.val.cell t.1 ez.val) ⊆
          relint (B.2.val.cell B.1 ev.val) := by
        unfold relint intrinsicInterior
        rw [hspan]
        exact Set.image_mono (interior_mono (Set.preimage_mono (hchain edgeIndex)))
      have hvbounds := host_step_step4_lift_jump_step3_source_range U B F hF ev ⟨cv, hvc, rfl⟩
      have hzbounds := host_step_step4_lift_jump_step3_source_range U t f hf ez ⟨cz, hzc, rfl⟩
      obtain ⟨x, hx, hlo⟩ := hzbounds.2.1
      obtain ⟨y, hy, hhi⟩ := hzbounds.2.2
      have hl := (hvbounds.1 x (hinside hx)).1
      have hh := (hvbounds.1 y (hinside hy)).2
      rw [← hcount x, hlo] at hl
      rw [← hcount y, hhi] at hh
      exact ⟨hl, hh⟩

/-- Step 3 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6):
"the germs ... are restrictions of the profile of c". I2 along one native
descendant chain bounds its endpoint germs by the containing root's germs.
This is the monotonicity part of the inherited profile rule of V4 2.3. -/
private theorem host_step_step4_lift_jump_step3_germ_bounds
    {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) (hD : Inv D)
    (H : FramedNode S) (ι : P.Incidence) (b : Bool)
    (u : host_step_Port C) (hu : host_step_portValid Y n H ι b u)
    (R : host_step_Root D) (hR : host_step_rootValid D H ι b R)
    (hdesc : (tileNode u.1).IsDescendant 0 R.1.val.node n)
    (hchain : ∀ k, (tileNode u.1).cell 0 (u.2.2.chain.val.cell k).val ⊆
      R.1.val.node.cell n (R.2.2.chain.val.cell k).val) :
    R.2.1.kappaMinus (host_step_edge R.2) ≤ u.2.1.kappaMinus (host_step_edge u.2) ∧
      u.2.1.kappaPlus (host_step_edge u.2) ≤ R.2.1.kappaPlus (host_step_edge R.2) := by
  obtain ⟨U, hU, hs⟩ := host_step_step4_lift_jump_step3_realise
    (D.blockState R.1.val R.1.property) (hD.I1 R.1.val R.1.property).1
    R.1.val.node n (hD.I1 R.1.val R.1.property).2.1
    (hD.I1 R.1.val R.1.property).2.2
  obtain ⟨r, hr, w, htile⟩ := hdesc
  have hrn : r = n := by omega
  subst r
  have hreal {k : ℕ} (hk : k = n) (hN : R.1.val.node ∈ D.geometry.nodes k)
      (hU' : R.1.val.node ∈ U.hierarchy.nodes k) :
      stateOf U P ⟨k, ⟨R.1.val.node, hU'⟩⟩ = D.stateAt k R.1.val.node hN := by
    subst k
    exact hs
  have hnode {k : ℕ} (hk : k = n) (hU' : R.1.val.node ∈ U.hierarchy.nodes k) :
      (⟨k, ⟨R.1.val.node, hU'⟩⟩ : U.Node) = ⟨n, ⟨R.1.val.node, hU⟩⟩ := by
    subst k
    rfl
  have hdesc : ∃ (htD : tileNode u.1 ∈ D.geometry.nodes 0)
      (htU : tileNode u.1 ∈ U.hierarchy.nodes 0),
      stateOf U P ⟨0, ⟨tileNode u.1, htU⟩⟩ = D.stateAt 0 (tileNode u.1) htD ∧
        U.hierarchy.ancestor ⟨0, ⟨tileNode u.1, htU⟩⟩ n = ⟨n, ⟨R.1.val.node, hU⟩⟩ := by
    obtain ⟨htD, htU, htstate, hanc⟩ :=
      host_step_step4_lift_jump_step3_descent D hD U 0 n R.1.val.node
        (by simpa only [Nat.zero_add] using D.geometry.root_mem R.1.val R.1.property)
        (by simpa only [Nat.zero_add] using hU)
        (hreal (Nat.zero_add n) _ _) w
    rw [htile]
    exact ⟨htD, htU, htstate, hanc.trans (hnode (Nat.zero_add n) _)⟩
  obtain ⟨htD, htU, htstate, hanc⟩ := hdesc
  apply host_step_step4_lift_jump_step3_source_bounds U
    ⟨n, ⟨R.1.val.node, hU⟩⟩ ⟨0, ⟨tileNode u.1, htU⟩⟩ n hanc R.2 u.2
  · rw [hs]
    exact hR.1
  · rw [htstate, hD.I2.2 (tileNode u.1) htD u.1 hu.1 rfl]
    exact hu.2.1
  · exact hR.2.2.1
  · exact hu.2.2.2.1
  · exact hu.2.2.2.2.1.trans hR.2.2.2.1.symm
  · exact hu.2.2.2.2.2.1.trans hR.2.2.2.2.1.symm
  · exact hchain

/-- Step 4 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6):
"a site ... in relint e_m ... is nonconstant". The honest count includes
the specified local site, so the port's two germs are strictly ordered. -/
private theorem host_step_step4_lift_jump_step4_site_strict
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (H : FramedNode S)
    (ι : P.Incidence) (b : Bool) (u : host_step_Port C)
    (hu : host_step_portValid Y n H ι b u) (x : E d)
    (hx : host_step_localJump u x) :
    u.2.1.kappaMinus (host_step_edge u.2) < u.2.1.kappaPlus (host_step_edge u.2) := by
  classical
  obtain ⟨w, hw, k, rfl, hx⟩ := hx
  have hs : (compilerLeaf C u.1).prePattern.state ∈ honestStates S P :=
    (prePattern_components_honest P _
      ((certificate_components_honest P (compilerLeaf C u.1).1.val
        (compilerLeaf C u.1).1.property).1 (compilerLeaf C u.1).2)).1
  have hc := host_step_step2_port_sites_step2_readout_count _ hs
    u.2.1.facet.val u.2.1 hu.2.1 (host_step_edge u.2)
    ⟨u.2.2, hu.2.2.2.1, rfl⟩ w hw
  have hframe : (tileNode u.1).prototypeFrame 0 =
      (compilerFrame C u.1).toAffineEquiv := by
    ext z
    simp [FramedNode.prototypeFrame, tileNode]
  change _ ∈ relint ((tileNode u.1).prototypeFrame 0 ''
    (host_step_edge u.2).val.carrier) at hx
  rw [hframe, host_step_step2_port_sites_step2_relint_image] at hx
  have hk : (wordPlacement w.word).symm (P.sites u.2.1.incidence u.2.1.sideIndex k)
      ∈ relint (host_step_edge u.2).val.carrier :=
    (compilerFrame C u.1).injective.mem_set_image.mp hx
  have hpos : 0 < (Finset.univ.filter (fun a : Fin P.N =>
      (wordPlacement w.word).symm (P.sites u.2.1.incidence u.2.1.sideIndex a)
        ∈ relint (host_step_edge u.2).val.carrier)).card :=
    Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  omega

/-- Step 5 of the V4 proof of `host_step_step4_lift_jump` (V4 3.6):
"a strand vertex v_(m+1)". Both recorded endpoints belong to the actual
port edge, including when its chosen orientation reverses the endpoint pair. -/
private theorem host_step_step4_lift_jump_step5_endpoints (u : host_step_Port C) :
    (host_step_portEnds u).1 ∈ host_step_portEdge u ∧
      (host_step_portEnds u).2 ∈ host_step_portEdge u := by
  have he := (Classical.choose_spec
    (edge_endpoints_exist (⟨u.2.1.ty, host_step_edge u.2⟩ : EdgeName S))).2
  have hends : (u.2.1.endpoints (host_step_edge u.2)).1 ∈
      (host_step_edge u.2).val.carrier ∧
      (u.2.1.endpoints (host_step_edge u.2)).2 ∈
        (host_step_edge u.2).val.carrier := by
    rw [he]
    unfold FacetRecord.endpoints
    split
    · exact ⟨left_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩
    · exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  constructor
  · refine ⟨_, hends.1, ?_⟩
    simp [FramedNode.prototypeFrame, tileNode, host_step_portEnds]
  · refine ⟨_, hends.2, ?_⟩
    simp [FramedNode.prototypeFrame, tileNode, host_step_portEnds]

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
  have hbounds (i : Fin (m + 1)) (hi : x ∈ host_step_portEdge (u i)) :
      (R j).2.1.kappaMinus (host_step_edge (R j).2) ≤
          (u i).2.1.kappaMinus (host_step_edge (u i).2) ∧
        (u i).2.1.kappaMinus (host_step_edge (u i).2) ≤
          (u i).2.1.kappaPlus (host_step_edge (u i).2) ∧
        (u i).2.1.kappaPlus (host_step_edge (u i).2) ≤
          (R j).2.1.kappaPlus (host_step_edge (R j).2) := by
    have ho := host_step_step4_lift_jump_step2_owner D H ι b u R owner hR i j x hi hj
    have hb := host_step_step4_lift_jump_step3_germ_bounds D hD H ι b
      (u i) (hu.1 i) (R (owner i)) (hR.1 (owner i))
      (hR.2.2.2.2 i).1 (hR.2.2.2.2 i).2
    rw [ho] at hb
    obtain ⟨J, hcount, _⟩ := host_step_step2_port_sites Y n H ι b (u i) (hu.1 i)
    exact ⟨hb.1, by omega, hb.2⟩
  rcases hx with ⟨i, hi⟩ | ⟨i, hxi, hunit⟩
  · have hstrict := host_step_step4_lift_jump_step4_site_strict Y n H ι b (u i) (hu.1 i) x hi
    have hmem := hi.choose_spec.2.choose_spec.2
    have hb := hbounds i (intrinsicInterior_subset hmem)
    omega
  · have hleft : x ∈ host_step_portEdge (u i.castSucc) :=
      hxi ▸ (host_step_step4_lift_jump_step5_endpoints (u i.castSucc)).2
    have hright : x ∈ host_step_portEdge (u i.succ) := by
      rw [hxi, (hu.2.2.2.2.2.1 i).1]
      exact (host_step_step4_lift_jump_step5_endpoints (u i.succ)).1
    have hl := hbounds i.castSucc hleft
    have hr := hbounds i.succ hright
    omega

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

/-- Step 1 of the V4 proof of `host_step_step5_frame` (V4 3.6):
"with the orientation of h". The chain vector orders the two actual endpoints. -/
private theorem host_step_step5_frame_step1_chain_segment (z : host_step_Chain P) :
    ∃ p q : E d, p ≠ q ∧ (host_step_edge z).val.carrier = segment ℝ p q ∧
      chainVector z.2 = q - p := by
  let e : EdgeName S := ⟨z.1.ty, host_step_edge z⟩
  let ab := Classical.choose (edge_endpoints_exist e)
  have hab : ab.1 ≠ ab.2 := (Classical.choose_spec (edge_endpoints_exist e)).1
  have he : (host_step_edge z).val.carrier = segment ℝ ab.1 ab.2 :=
    (Classical.choose_spec (edge_endpoints_exist e)).2
  cases hforward : z.2.forward
  · refine ⟨ab.2, ab.1, hab.symm, he.trans (segment_symm ℝ _ _), ?_⟩
    change (if z.2.forward then edgeVector e else -edgeVector e) = _
    simp only [hforward, Bool.false_eq_true, ↓reduceIte]
    change -(ab.2 - ab.1) = ab.1 - ab.2
    exact neg_sub _ _
  · refine ⟨ab.1, ab.2, hab, he, ?_⟩
    change (if z.2.forward then edgeVector e else -edgeVector e) = _
    simp only [hforward, ↓reduceIte]
    rfl

/-- Step 1 of the V4 proof of `host_step_step5_frame` (V4 3.6):
"its flag edge is h ... with the orientation of h". Equal segments have
only two endpoint orderings, and the two positive inner products exclude reversal. -/
private theorem host_step_step5_frame_step1_oriented_endpoints
    (φ ψ : E d ≃ᵃ[ℝ] E d) (p q v : E d) (hpq : p ≠ q)
    (hedge : ψ '' segment ℝ p q = φ '' segment ℝ p q)
    (hφ : 0 < inner ℝ v (φ.linear (q - p)))
    (hψ : 0 < inner ℝ v (ψ.linear (q - p))) :
    ψ p = φ p ∧ ψ q = φ q := by
  have hψseg : ψ '' segment ℝ p q = segment ℝ (ψ p) (ψ q) :=
    image_segment ℝ ψ.toAffineMap _ _
  have hφseg : φ '' segment ℝ p q = segment ℝ (φ p) (φ q) :=
    image_segment ℝ φ.toAffineMap _ _
  rw [hψseg, hφseg] at hedge
  rcases host_step_step4_age_one_flag_step4_endpoints (φ p) (φ q) (ψ p) (ψ q)
      (φ.injective.ne hpq) hedge with h | ⟨hfirst, hlast⟩
  · exact h
  · have hφ' : φ.linear (q - p) = φ q - φ p := φ.toAffineMap.linearMap_vsub q p
    have hψ' : ψ.linear (q - p) = ψ q - ψ p := ψ.toAffineMap.linearMap_vsub q p
    rw [hψ', hfirst, hlast, ← neg_sub (φ q) (φ p), inner_neg_right, ← hφ'] at hψ
    linarith

/-- Step 2 of the V4 proof of `host_step_step5_frame` (V4 3.6):
"with the orientation of h and the sides of 𝓕". An orthogonal map fixing the wall
pointwise and preserving one closed side fixes the whole containing space. -/
private theorem host_step_step5_frame_step2_fix_side
    (R : Ortho d) (W V : Submodule ℝ (E d)) (ℓ : E d →ₗ[ℝ] ℝ)
    (hWV : W ≤ V) (hker : ∀ x ∈ V, ℓ x = 0 ↔ x ∈ W)
    (hfix : ∀ x ∈ W, R x = x)
    (hside : R '' {x | x ∈ V ∧ 0 ≤ ℓ x} = {x | x ∈ V ∧ 0 ≤ ℓ x}) :
    ∀ x ∈ V, R x = x := by
  have hmap (x : E d) (hx : x ∈ V) : R x ∈ V := by
    rcases le_total 0 (ℓ x) with hpos | hneg
    · exact (show R x ∈ {x | x ∈ V ∧ 0 ≤ ℓ x} from
          hside ▸ mem_image_of_mem R ⟨hx, hpos⟩).1
    · have hm : R (-x) ∈ V :=
        (show R (-x) ∈ {x | x ∈ V ∧ 0 ≤ ℓ x} from
          hside ▸ mem_image_of_mem R ⟨V.neg_mem hx, by simpa using hneg⟩).1
      simpa only [map_neg, neg_mem_iff] using hm
  intro x hx
  let p := W.starProjection x
  let u := x - p
  have hp : p ∈ W := W.starProjection_apply_mem x
  have huV : u ∈ V := V.sub_mem hx (hWV hp)
  have huO : u ∈ Wᗮ := W.sub_starProjection_mem_orthogonal x
  by_cases hu : u = 0
  · have hxp : x = p := sub_eq_zero.mp hu
    rw [hxp]
    exact hfix p hp
  have hℓ : ℓ u ≠ 0 := by
    intro hz
    have huW := (hker u huV).mp hz
    have hzero : u ∈ (⊥ : Submodule ℝ (E d)) := by
      rw [← W.orthogonal_disjoint.eq_bot]
      exact ⟨huW, huO⟩
    exact hu hzero
  have hRuO : R u ∈ Wᗮ := by
    intro w hw
    rw [← hfix w hw, R.inner_map_map]
    exact huO w hw
  let a := ℓ (R u) / ℓ u
  have heq : R u = a • u := by
    have hzV : R u - a • u ∈ V := V.sub_mem (hmap u huV) (V.smul_mem a huV)
    have hzW : R u - a • u ∈ W := (hker _ hzV).mp (by
      simp only [map_sub, map_smul, smul_eq_mul, a, div_mul_cancel₀ _ hℓ, sub_self])
    have hzO : R u - a • u ∈ Wᗮ := Wᗮ.sub_mem hRuO (Wᗮ.smul_mem a huO)
    have hz : R u - a • u = 0 := by
      have hm : R u - a • u ∈ W ⊓ Wᗮ := ⟨hzW, hzO⟩
      simpa only [W.orthogonal_disjoint.eq_bot, Submodule.mem_bot] using hm
    exact sub_eq_zero.mp hz
  have ha : |a| = 1 := by
    have hn := R.norm_map u
    rw [heq, norm_smul, Real.norm_eq_abs] at hn
    exact (mul_eq_right₀ (norm_ne_zero_iff.mpr hu)).mp hn
  have ha1 : a = 1 := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp ha with h | h
    · exact h
    · have hflip : R u = -u := by simpa only [h, neg_one_smul] using heq
      rcases lt_or_gt_of_ne hℓ with hneg | hpos
      · have hm : R (-u) ∈ {x | x ∈ V ∧ 0 ≤ ℓ x} :=
          hside ▸ mem_image_of_mem R ⟨V.neg_mem huV, by simpa using hneg.le⟩
        have := hm.2
        simp only [map_neg, hflip, neg_neg] at this
        linarith
      · have hm : R u ∈ {x | x ∈ V ∧ 0 ≤ ℓ x} :=
          hside ▸ mem_image_of_mem R ⟨huV, hpos.le⟩
        have := hm.2
        simp only [hflip, map_neg] at this
        linarith
  have hRu : R u = u := by simpa only [ha1, one_smul] using heq
  have hxp : x = p + u := by dsimp [u]; abel
  rw [hxp, map_add, hfix p hp, hRu]


/-- Step 2 of the V4 proof of `host_step_step5_frame` (V4 3.6):
"with the same positioned oriented flag and the same inward side". The one-side rigidity argument survives an arbitrary
invertible linear placement, including the anisotropic expansion. -/
private theorem host_step_step5_frame_step2_transport_side
    (R : Ortho d) (L : E d ≃ₗ[ℝ] E d) (W V : Submodule ℝ (E d)) (K : Set (E d))
    (hgeom : ∃ ℓ : E d →ₗ[ℝ] ℝ,
      (∀ x, x ∈ W ↔ x ∈ V ∧ ℓ x = 0) ∧ K = {x | x ∈ V ∧ 0 ≤ ℓ x})
    (hfix : ∀ x ∈ W, R (L x) = L x)
    (hside : R '' (L '' K) = L '' K) :
    ∀ x ∈ V, R (L x) = L x := by
  obtain ⟨ℓ, hwall, hK⟩ := hgeom
  let W' := W.map L.toLinearMap
  let V' := V.map L.toLinearMap
  let ℓ' : E d →ₗ[ℝ] ℝ := ℓ.comp L.symm.toLinearMap
  have heval (x : E d) : ℓ' (L x) = ℓ x := by
    simp only [ℓ', LinearMap.comp_apply, LinearEquiv.coe_coe, L.symm_apply_apply]
  have hhalf : L '' K = {y | y ∈ V' ∧ 0 ≤ ℓ' y} := by
    rw [hK]
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hpos⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by simpa only [heval] using hpos⟩
    · rintro ⟨⟨x, hx, rfl⟩, hpos⟩
      change 0 ≤ ℓ' (L x) at hpos
      exact ⟨x, ⟨hx, by simpa only [heval] using hpos⟩, rfl⟩
  have hWV : W' ≤ V' := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, ((hwall x).mp hx).1, rfl⟩
  have hker : ∀ y ∈ V', ℓ' y = 0 ↔ y ∈ W' := by
    rintro y ⟨x, hx, rfl⟩
    change ℓ' (L x) = 0 ↔ L x ∈ W'
    rw [heval]
    constructor
    · intro hz
      exact ⟨x, (hwall x).mpr ⟨hx, hz⟩, rfl⟩
    · rintro ⟨w, hw, he⟩
      have he' : w = x := L.injective he
      exact ((hwall x).mp (he' ▸ hw)).2
  have hfix' : ∀ y ∈ W', R y = y := by
    rintro y ⟨x, hx, rfl⟩
    exact hfix x hx
  rw [hhalf] at hside
  intro x hx
  exact host_step_step5_frame_step2_fix_side R W' V' ℓ' hWV hker hfix' hside
    (L x) ⟨x, hx, rfl⟩


/-- Step 3 of the V4 proof of `host_step_step5_frame` (V4 3.6, 1.0(a)):
"near a point of the relative interior ... a half-space".
The tangent cone reads exactly the half-space in a local half-ball. -/
private theorem host_step_step5_frame_step3_tangent_halfball
    (K : Set (E d)) (p v : E d) (r : ℝ) (hr : 0 < r)
    (hlocal : K ∩ ball p r = {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p r) :
    tangentCone K p = {u | 0 ≤ inner ℝ v u} := by
  ext u
  let δ := r / (‖u‖ + 1)
  have hden : 0 < ‖u‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hr hden
  have hnear (t : ℝ) (ht : 0 < t) (htδ : t < δ) : p + t • u ∈ ball p r := by
    change dist (p + t • u) p < r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have := (lt_div_iff₀ hden).mp htδ
    nlinarith [norm_nonneg u]
  constructor
  · rintro ⟨ε, hε, hmem⟩
    let t := min ε δ / 2
    have ht : 0 < t := div_pos (lt_min hε hδ) (by norm_num)
    have htε : t < ε := lt_of_lt_of_le (by dsimp [t]; linarith [lt_min hε hδ])
      (min_le_left ε δ)
    have htδ : t < δ := lt_of_lt_of_le (by dsimp [t]; linarith [lt_min hε hδ])
      (min_le_right ε δ)
    have hm : p + t • u ∈ {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p r :=
      hlocal ▸ ⟨hmem t ht htε, hnear t ht htδ⟩
    have hnonneg := hm.1
    change 0 ≤ inner ℝ v (p + t • u - p) at hnonneg
    rw [add_sub_cancel_left, inner_smul_right] at hnonneg
    exact nonneg_of_mul_nonneg_right hnonneg ht
  · intro hu
    refine ⟨δ, hδ, fun t ht htδ => ?_⟩
    have hm : p + t • u ∈ K ∩ ball p r := by
      rw [hlocal]
      refine ⟨?_, hnear t ht htδ⟩
      change 0 ≤ inner ℝ v (p + t • u - p)
      rw [add_sub_cancel_left, inner_smul_right]
      exact mul_nonneg ht.le hu
    exact hm.1

/-- Step 3 of the V4 proof of `host_step_step5_frame` (V4 3.6, F1):
"moving ... into relint". Every direction of an affine span is locally
available at a relative-interior point. -/
private theorem host_step_step5_frame_step3_relint_directions
    (K : Set (E d)) (p : E d) (hp : p ∈ relint K) :
    (cellDirection K : Set (E d)) ⊆ tangentCone K p := by
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hq)
  intro u hu
  let δ := r / (‖u‖ + 1)
  have hden : 0 < ‖u‖ + 1 := by positivity
  refine ⟨δ, div_pos hr hden, fun t ht htδ => ?_⟩
  have hmem : q.val + t • u ∈ affineSpan ℝ K := by
    simpa only [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction ((cellDirection K).smul_mem t hu) q.property
  apply hball (a := ⟨q.val + t • u, hmem⟩)
  change dist (q.val + t • u) q.val < r
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have := (lt_div_iff₀ hden).mp htδ
  nlinarith [norm_nonneg u]


/-- Step 3 of the V4 proof of `host_step_step5_frame` (V4 3.6, 1.0(a)):
"its inward side at g_j". The inward tangent cone is a closed half-space
whose wall is precisely the direction of the listed facet. -/
private theorem host_step_step5_frame_step3_inward_side
    (A : S.ι) (f : FacetName S A) :
    ∃ ℓ : E d →ₗ[ℝ] ℝ,
      (∀ x, x ∈ cellDirection f.val.carrier ↔ x ∈ (⊤ : Submodule ℝ (E d)) ∧ ℓ x = 0) ∧
      tangentCone (S.proto A).carrier (cellAnchor f.val) =
        {x | x ∈ (⊤ : Submodule ℝ (E d)) ∧ 0 ≤ ℓ x} := by
  obtain ⟨r, hr, v, hv, _, _, hlocal⟩ :=
    facet_halfball (S.proto A) (S.cx A) f.val f.property _ (cellAnchor_mem f.val)
  have hcone := host_step_step5_frame_step3_tangent_halfball _ _ v r hr hlocal
  let ℓ : E d →ₗ[ℝ] ℝ := innerₛₗ ℝ v
  have hsub : f.val.carrier ⊆ (S.proto A).carrier := by
    have hm := (Finset.mem_filter.mp f.property).1
    have hfront : relint f.val.carrier ⊆ frontier (S.proto A).carrier := by
      intro x hx
      rw [← (S.cx A).cover]
      exact mem_iUnion.mpr ⟨f.val, mem_iUnion.mpr ⟨hm, hx⟩⟩
    rw [← f.val.flat.regularClosed]
    exact closure_minimal (hfront.trans frontier_subset_closure)
      (isClosed_closure) |>.trans_eq (S.proto A).compact.isClosed.closure_eq
  have hle : cellDirection f.val.carrier ≤ ℓ.ker := by
    intro u hu
    have hpos (w : E d) (hw : w ∈ cellDirection f.val.carrier) : 0 ≤ ℓ w := by
      have ht := host_step_step5_frame_step3_relint_directions _ _ (cellAnchor_mem f.val) hw
      have ht' : w ∈ tangentCone (S.proto A).carrier (cellAnchor f.val) := by
        obtain ⟨ε, hε, hmem⟩ := ht
        exact ⟨ε, hε, fun t ht htε => hsub (hmem t ht htε)⟩
      simpa only [hcone] using ht'
    have h₁ := hpos u hu
    have h₂ := hpos (-u) ((cellDirection f.val.carrier).neg_mem hu)
    change ℓ u = 0
    rw [map_neg] at h₂
    linarith
  have hvv : ℓ v ≠ 0 := by
    change inner ℝ v v ≠ 0
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have hproper : ℓ.ker ≠ ⊤ := by
    intro he
    exact hvv (show v ∈ ℓ.ker from he ▸ Submodule.mem_top)
  have hdim := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hproper)
  have hfdim : Module.finrank ℝ (cellDirection f.val.carrier) = d - 1 :=
    f.val.flat.dimension.trans (Finset.mem_filter.mp f.property).2
  have heq : cellDirection f.val.carrier = ℓ.ker := by
    apply Submodule.eq_of_le_of_finrank_le hle
    simp only [finrank_top, finrank_euclideanSpace_fin] at hdim
    omega
  refine ⟨ℓ, ?_, ?_⟩
  · intro x
    simp only [heq, LinearMap.mem_ker, Submodule.mem_top, true_and]
  · simpa only [Submodule.mem_top, true_and] using hcone


/-- Step 1 of the V4 proof of `host_step_step5_frame_step3_flag_side` (V4 1.0(a)):
"a (d-1)-cell inside e ... forces e = F". Strict containment of listed cells
strictly increases dimension, since their relative interiors are disjoint. -/
private theorem host_step_step5_frame_step3_flag_side_step1_dimension
    {A : PolyManifoldDomain d} (K : CellComplex A) (e f : Cell d)
    (he : e ∈ K.cells) (hf : f ∈ K.cells) (hsub : e.carrier ⊆ f.carrier)
    (hne : e ≠ f) : e.dim < f.dim := by
  have hspan := affineSpan_mono ℝ hsub
  have hdir := AffineSubspace.direction_le hspan
  have hdim : e.dim ≤ f.dim := by
    rw [← e.flat.dimension, ← f.flat.dimension]
    exact Submodule.finrank_mono hdir
  by_contra hlt
  have heqdim : e.dim = f.dim := by omega
  have heq : affineSpan ℝ e.carrier = affineSpan ℝ f.carrier := by
    apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le _ _ hspan
    · apply Submodule.eq_of_le_of_finrank_eq hdir
      exact e.flat.dimension.trans (heqdim.trans f.flat.dimension.symm)
    · exact e.flat.connected.nonempty.mono (subset_affineSpan ℝ _)
  have hrel : relint e.carrier ⊆ relint f.carrier := by
    unfold relint intrinsicInterior
    rw [heq]
    exact image_mono (interior_mono (preimage_mono hsub))
  obtain ⟨x, hx⟩ := e.flat.relint_nonempty
  exact Set.disjoint_left.mp (K.relint_disjoint e he f hf hne) hx (hrel hx)

/-- Step 2 of the V4 proof of `host_step_step5_frame_step3_flag_side` (V4 1.0(a)):
"Cells are closed and finitely many, so some ball U around p meets no other cell".
In the upper cell's relative boundary, a point of the lower relative interior
meets only that codimension-one cell; locally the boundary is its affine span. -/
private theorem host_step_step5_frame_step3_flag_side_step2_boundary_patch
    {A : PolyManifoldDomain d} (K : CellComplex A) (e f : Cell d)
    (he : e ∈ K.cells) (hf : f ∈ K.cells) (hsub : e.carrier ⊆ f.carrier)
    (hdim : f.dim = e.dim + 1) (p : E d) (hp : p ∈ relint e.carrier) :
    ∃ r : ℝ, 0 < r ∧ relfrontier f.carrier ∩ ball p r =
      (affineSpan ℝ e.carrier : Set (E d)) ∩ ball p r := by
  classical
  have hne : e ≠ f := by
    intro h
    have := congrArg Cell.dim h
    omega
  have hpf : p ∈ relfrontier f.carrier := by
    rw [relfrontier, ← closure_diff_intrinsicInterior (𝕜 := ℝ), f.flat.compact.isClosed.closure_eq]
    exact ⟨hsub (intrinsicInterior_subset (𝕜 := ℝ) hp), fun h =>
      Set.disjoint_left.mp (K.relint_disjoint e he f hf hne) hp h⟩
  have hpA : p ∈ frontier A.carrier := by
    rw [← K.cover]
    exact mem_iUnion₂.mpr ⟨e, he, hp⟩
  have hmin : K.minimalCell p hpA = e := by
    by_contra h
    exact Set.disjoint_left.mp
      (K.relint_disjoint _ (K.minimalCell_mem p hpA) e he h)
      (K.mem_relint_minimalCell p hpA) hp
  obtain ⟨b, hb, hboundary⟩ := K.boundary_union f hf
  have hgb (g : Cell d) (hg : g ∈ b) : g.carrier ⊆ relfrontier f.carrier := by
    intro x hx
    rw [hboundary]
    exact mem_iUnion₂.mpr ⟨g, hg, hx⟩
  have hgf (g : Cell d) (hg : g ∈ b) : g.carrier ⊆ f.carrier :=
    (hgb g hg).trans (intrinsicFrontier_subset (𝕜 := ℝ) f.flat.compact.isClosed)
  have honly (g : Cell d) (hg : g ∈ b) (hpg : p ∈ g.carrier) : g = e := by
    have heg : e.carrier ⊆ g.carrier := hmin ▸ K.minimalCell_subset p hpA g (hb hg) hpg
    have hgfne : g ≠ f := by
      intro h
      obtain ⟨x, hx⟩ := f.flat.relint_nonempty
      have hx' := hgb g hg (h.symm ▸ intrinsicInterior_subset (𝕜 := ℝ) hx)
      rw [relfrontier, ← closure_diff_intrinsicInterior (𝕜 := ℝ)] at hx'
      exact hx'.2 hx
    have hgd := host_step_step5_frame_step3_flag_side_step1_dimension
      K g f (hb hg) hf (hgf g hg) hgfne
    by_contra hge
    have hed := host_step_step5_frame_step3_flag_side_step1_dimension
      K e g he (hb hg) heg (Ne.symm hge)
    omega
  let U : Set (E d) := (⋃ g ∈ b.filter (fun g => g ≠ e), g.carrier)ᶜ
  have hU : IsOpen U :=
    (isClosed_biUnion_finset (s := b.filter (fun g => g ≠ e))
      (fun g _ => g.flat.compact.isClosed)).isOpen_compl
  have hpU : p ∈ U := by
    intro h
    obtain ⟨g, hg, hpg⟩ := mem_iUnion₂.mp h
    exact (Finset.mem_filter.mp hg).2 (honly g (Finset.mem_filter.mp hg).1 hpg)
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hpU)
  obtain ⟨q, hq, hqp⟩ := hp
  obtain ⟨r₂, hr₂, hball₂⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hq)
  have hflat : ∀ x ∈ affineSpan ℝ e.carrier, x ∈ ball p r₂ → x ∈ e.carrier := by
    intro x hx hnear
    apply hball₂ (a := ⟨x, hx⟩)
    simpa only [mem_ball, Subtype.dist_eq, hqp] using hnear
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hnear⟩
    rw [hboundary] at hx
    obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp hx
    have hge : g = e := by
      by_contra h
      exact (hball₁ ((ball_subset_ball (min_le_left r₁ r₂)) hnear))
        (mem_iUnion₂.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, h⟩, hxg⟩)
    exact ⟨mem_affineSpan ℝ (hge ▸ hxg), hnear⟩
  · rintro ⟨hx, hnear⟩
    have hxe := hflat x hx ((ball_subset_ball (min_le_right r₁ r₂)) hnear)
    have heB : e ∈ b := by
      rw [hboundary] at hpf
      obtain ⟨g, hg, hpg⟩ := mem_iUnion₂.mp hpf
      exact honly g hg hpg ▸ hg
    exact ⟨hgb e heB hxe, hnear⟩

/-- Step 3 of the V4 proof of `host_step_step5_frame_step3_flag_side` (V4 3.6, F1):
"a codimension-one face". A codimension-one inclusion of direction spaces
is the kernel of a real linear functional restricted to the upper space. -/
private theorem host_step_step5_frame_step3_flag_side_step3_wall
    (W V : Submodule ℝ (E d)) (hWV : W ≤ V)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ W + 1) :
    ∃ ℓ : E d →ₗ[ℝ] ℝ, ∀ x, x ∈ W ↔ x ∈ V ∧ ℓ x = 0 := by
  have hlt : W < V := lt_of_le_of_ne hWV (by
    intro h
    rw [h] at hdim
    omega)
  obtain ⟨v, hv, hvW⟩ := SetLike.exists_of_lt hlt
  obtain ⟨ℓ, hvℓ, hWℓ⟩ := Submodule.exists_le_ker_of_notMem hvW
  have hle : W ≤ V ⊓ ℓ.ker := le_inf hWV hWℓ
  have hproper : V ⊓ ℓ.ker < V := lt_of_le_of_ne inf_le_left (by
    intro h
    have hm : v ∈ V ⊓ ℓ.ker := h.symm ▸ hv
    exact hvℓ hm.2)
  have hsmall := Submodule.finrank_lt_finrank_of_lt hproper
  have heq : W = V ⊓ ℓ.ker := Submodule.eq_of_le_of_finrank_le hle (by omega)
  refine ⟨ℓ, fun x => ?_⟩
  simp only [heq, Submodule.mem_inf, LinearMap.mem_ker]

/-- Step 4 of the V4 proof of `host_step_step5_frame_step3_flag_side` (V4 1.0(a)):
"U \ aff F has two components ... each component is inside or outside A".
A closed set with a flat boundary patch and an interior point in the ball
occupies exactly one of its two open half-balls. -/
private theorem host_step_step5_frame_step3_flag_side_step4_halfball
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : Set V) (hD : IsClosed D) (r : ℝ) (hr : 0 < r) (ℓ : V →ₗ[ℝ] ℝ)
    (hwall : frontier D ∩ ball 0 r = {x | ℓ x = 0} ∩ ball 0 r)
    (hint : (interior D ∩ ball 0 r).Nonempty) :
    D ∩ ball 0 r = {x | 0 ≤ ℓ x} ∩ ball 0 r ∨
      D ∩ ball 0 r = {x | ℓ x ≤ 0} ∩ ball 0 r := by
  let U : Set V := {x | 0 < ℓ x} ∩ ball 0 r
  let L : Set V := {x | ℓ x < 0} ∩ ball 0 r
  have hzero (x : V) (hx : x ∈ ball 0 r) : x ∈ frontier D ↔ ℓ x = 0 := by
    constructor
    · intro h
      exact (show x ∈ {x | ℓ x = 0} ∩ ball 0 r from hwall ▸ ⟨h, hx⟩).1
    · intro h
      exact (show x ∈ frontier D ∩ ball 0 r from hwall.symm ▸ ⟨h, hx⟩).1
  have hclass (T : Set V) (hT : IsPreconnected T) (hball : T ⊆ ball 0 r)
      (hne : ∀ x ∈ T, ℓ x ≠ 0) : T ⊆ interior D ∨ T ⊆ Dᶜ := by
    apply hT.subset_or_subset isOpen_interior hD.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset)
    intro x hx
    by_cases hxD : x ∈ D
    · left
      by_contra hi
      have hf : x ∈ frontier D := by
        rw [hD.frontier_eq]
        exact ⟨hxD, hi⟩
      exact hne x hx ((hzero x (hball hx)).mp hf)
    · exact Or.inr hxD
  have hU := hclass U
    ((convex_halfSpace_gt ℓ.isLinear 0).inter (convex_ball (0 : V) r)).isPreconnected
    inter_subset_right (fun x hx => ne_of_gt hx.1)
  have hL := hclass L
    ((convex_halfSpace_lt ℓ.isLinear 0).inter (convex_ball (0 : V) r)).isPreconnected
    inter_subset_right (fun x hx => ne_of_lt hx.1)
  have hnotboth (hu : U ⊆ interior D) (hl : L ⊆ interior D) : False := by
    have hb : ball (0 : V) r ⊆ D := by
      intro x hx
      rcases lt_trichotomy (ℓ x) 0 with hn | hz | hp
      · exact interior_subset (hl ⟨hn, hx⟩)
      · exact hD.frontier_subset ((hzero x hx).mpr hz)
      · exact interior_subset (hu ⟨hp, hx⟩)
    have hi : (0 : V) ∈ interior D :=
      interior_maximal hb isOpen_ball (mem_ball_self hr)
    exact Set.disjoint_left.mp disjoint_interior_frontier hi
      ((hzero 0 (mem_ball_self hr)).mpr (map_zero ℓ))
  have hnotneither (hu : U ⊆ Dᶜ) (hl : L ⊆ Dᶜ) : False := by
    obtain ⟨x, hi, hx⟩ := hint
    rcases lt_trichotomy (ℓ x) 0 with hn | hz | hp
    · exact hl ⟨hn, hx⟩ (interior_subset hi)
    · exact Set.disjoint_left.mp disjoint_interior_frontier hi ((hzero x hx).mpr hz)
    · exact hu ⟨hp, hx⟩ (interior_subset hi)
  rcases hU with hu | hu <;> rcases hL with hl | hl
  · exact (hnotboth hu hl).elim
  · left
    ext x
    constructor
    · rintro ⟨hxD, hx⟩
      refine ⟨?_, hx⟩
      change 0 ≤ ℓ x
      exact le_of_not_gt (fun hn => hl ⟨hn, hx⟩ hxD)
    · rintro ⟨hpos, hx⟩
      change 0 ≤ ℓ x at hpos
      rcases hpos.eq_or_lt with hz | hp
      · exact ⟨hD.frontier_subset ((hzero x hx).mpr hz.symm), hx⟩
      · exact ⟨interior_subset (hu ⟨hp, hx⟩), hx⟩
  · right
    ext x
    constructor
    · rintro ⟨hxD, hx⟩
      refine ⟨?_, hx⟩
      change ℓ x ≤ 0
      exact le_of_not_gt (fun hp => hu ⟨hp, hx⟩ hxD)
    · rintro ⟨hneg, hx⟩
      change ℓ x ≤ 0 at hneg
      rcases hneg.eq_or_lt with hz | hn
      · exact ⟨hD.frontier_subset ((hzero x hx).mpr hz), hx⟩
      · exact ⟨interior_subset (hl ⟨hn, hx⟩), hx⟩
  · exact (hnotneither hu hl).elim

/-- Step 5 of the V4 proof of `host_step_step5_frame_step3_flag_side` (V4 3.6, F1):
"in the affine span of the upper cell". Translate the flat boundary patch to
its direction space, apply the two-component argument, and return to ambient
coordinates. Reversing the functional selects the occupied side. -/
private theorem host_step_step5_frame_step3_flag_side_step5_relative_halfball
    (e f : Cell d) (hsub : e.carrier ⊆ f.carrier) (p : E d)
    (hp : p ∈ relint e.carrier) (r : ℝ) (hr : 0 < r)
    (hboundary : relfrontier f.carrier ∩ ball p r =
      (affineSpan ℝ e.carrier : Set (E d)) ∩ ball p r)
    (ℓ : E d →ₗ[ℝ] ℝ)
    (hker : ∀ x, x ∈ cellDirection e.carrier ↔
      x ∈ cellDirection f.carrier ∧ ℓ x = 0) :
    ∃ m : E d →ₗ[ℝ] ℝ, (∀ x, m x = 0 ↔ ℓ x = 0) ∧
      f.carrier ∩ ball p r =
        {x | x - p ∈ cellDirection f.carrier ∧ 0 ≤ m (x - p)} ∩ ball p r := by
  let B := affineSpan ℝ f.carrier
  let V := cellDirection f.carrier
  have hpe : p ∈ e.carrier := intrinsicInterior_subset (𝕜 := ℝ) hp
  have hpB : p ∈ B := mem_affineSpan ℝ (hsub hpe)
  have hpE : p ∈ affineSpan ℝ e.carrier := mem_affineSpan ℝ hpe
  letI : Nonempty B := ⟨⟨p, hpB⟩⟩
  let i : V ≃ᵃⁱ[ℝ] B := AffineIsometryEquiv.vaddConst ℝ ⟨p, hpB⟩
  let D : Set V := i ⁻¹' ((↑) ⁻¹' f.carrier : Set B)
  have hi (u : V) : (i u).val = p + u.val := by
    change u.val + p = p + u.val
    exact add_comm _ _
  have hiB (u : V) : u ∈ ball 0 r ↔ (i u).val ∈ ball p r := by
    simp only [mem_ball, hi, dist_eq_norm, sub_zero, add_sub_cancel_left,
      Submodule.coe_norm]
  have hD : IsClosed D :=
    (f.flat.compact.isClosed.preimage continuous_subtype_val).preimage i.continuous
  have hfront (u : V) : u ∈ frontier D ↔ (i u).val ∈ relfrontier f.carrier := by
    change u ∈ frontier (i.toHomeomorph ⁻¹' ((↑) ⁻¹' f.carrier : Set B)) ↔ _
    rw [← i.toHomeomorph.preimage_frontier]
    constructor
    · intro hu
      exact ⟨i u, hu, rfl⟩
    · rintro ⟨a, ha, heq⟩
      have heq' : a = i u := Subtype.ext heq
      simpa only [heq'] using ha
  have hlow (u : V) : (i u).val ∈ affineSpan ℝ e.carrier ↔ ℓ u.val = 0 := by
    rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hpE]
    change (i u).val - p ∈ cellDirection e.carrier ↔ _
    rw [hi, add_sub_cancel_left, hker]
    exact and_iff_right u.property
  let ℓV : V →ₗ[ℝ] ℝ := ℓ.comp V.subtype
  have hwall : frontier D ∩ ball 0 r = {u | ℓV u = 0} ∩ ball 0 r := by
    ext u
    constructor
    · rintro ⟨hu, hnear⟩
      have hm : (i u).val ∈ (affineSpan ℝ e.carrier : Set (E d)) ∩ ball p r :=
        hboundary ▸ ⟨(hfront u).mp hu, (hiB u).mp hnear⟩
      exact ⟨(hlow u).mp hm.1, hnear⟩
    · rintro ⟨hu, hnear⟩
      have hm : (i u).val ∈ relfrontier f.carrier ∩ ball p r :=
        hboundary.symm ▸ ⟨(hlow u).mpr hu, (hiB u).mp hnear⟩
      exact ⟨(hfront u).mpr hm.1, hnear⟩
  have hint : (interior D ∩ ball 0 r).Nonempty := by
    have hpcl : p ∈ closure (relint f.carrier) := f.flat.regularClosed.symm ▸ hsub hpe
    obtain ⟨y, hyball, a, ha, rfl⟩ :=
      mem_closure_iff.mp hpcl (ball p r) isOpen_ball (mem_ball_self hr)
    refine ⟨i.symm a, ?_, ?_⟩
    · change i.symm a ∈ interior (i.toHomeomorph ⁻¹' ((↑) ⁻¹' f.carrier : Set B))
      rw [← i.toHomeomorph.preimage_interior]
      change i (i.symm a) ∈ interior ((↑) ⁻¹' f.carrier : Set B)
      simpa only [i.apply_symm_apply] using ha
    · apply (hiB _).mpr
      simpa only [i.apply_symm_apply] using hyball
  have htranslate (m : E d →ₗ[ℝ] ℝ)
      (hm : D ∩ ball 0 r = {u | 0 ≤ m u.val} ∩ ball 0 r) :
      f.carrier ∩ ball p r =
        {x | x - p ∈ V ∧ 0 ≤ m (x - p)} ∩ ball p r := by
    have heval (x : E d) (hx : x - p ∈ V) : (i ⟨x - p, hx⟩).val = x := by
      rw [hi]
      exact add_sub_cancel _ _
    ext x
    constructor
    · rintro ⟨hxf, hnear⟩
      have hxV : x - p ∈ V := AffineSubspace.vsub_mem_direction
        (mem_affineSpan ℝ hxf) hpB
      have hu : (⟨x - p, hxV⟩ : V) ∈ D ∩ ball 0 r := by
        constructor
        · change (i ⟨x - p, hxV⟩).val ∈ f.carrier
          rwa [heval]
        · apply (hiB _).mpr
          rwa [heval]
      have hpos := (show (⟨x - p, hxV⟩ : V) ∈ {u | 0 ≤ m u.val} ∩ ball 0 r from hm ▸ hu).1
      exact ⟨⟨hxV, hpos⟩, hnear⟩
    · rintro ⟨⟨hxV, hpos⟩, hnear⟩
      have hu : (⟨x - p, hxV⟩ : V) ∈ D ∩ ball 0 r := by
        rw [hm]
        refine ⟨hpos, (hiB _).mpr ?_⟩
        rwa [heval]
      refine ⟨?_, hnear⟩
      have huD := hu.1
      change (i ⟨x - p, hxV⟩).val ∈ f.carrier at huD
      rwa [heval] at huD
  rcases host_step_step5_frame_step3_flag_side_step4_halfball D hD r hr ℓV hwall hint
    with hpos | hneg
  · exact ⟨ℓ, fun _ => Iff.rfl, htranslate ℓ hpos⟩
  · refine ⟨-ℓ, ?_, htranslate (-ℓ) ?_⟩
    · intro x
      simp only [LinearMap.neg_apply, neg_eq_zero]
    · simpa only [LinearMap.neg_apply, neg_nonneg] using hneg

/-- Step 6 of the V4 proof of `host_step_step5_frame_step3_flag_side` (V4 3.6, F1):
"a half-space on the recorded side". A local relative half-ball has exactly
its homogeneous half-space as its radial tangent cone. -/
private theorem host_step_step5_frame_step3_flag_side_step6_tangent
    (K : Set (E d)) (p : E d) (V : Submodule ℝ (E d))
    (ℓ : E d →ₗ[ℝ] ℝ) (r : ℝ) (hr : 0 < r)
    (hlocal : K ∩ ball p r = {x | x - p ∈ V ∧ 0 ≤ ℓ (x - p)} ∩ ball p r) :
    tangentCone K p = {u | u ∈ V ∧ 0 ≤ ℓ u} := by
  ext u
  let δ := r / (‖u‖ + 1)
  have hden : 0 < ‖u‖ + 1 := by positivity
  have hδ : 0 < δ := div_pos hr hden
  have hnear (t : ℝ) (ht : 0 < t) (htδ : t < δ) : p + t • u ∈ ball p r := by
    change dist (p + t • u) p < r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have := (lt_div_iff₀ hden).mp htδ
    nlinarith [norm_nonneg u]
  constructor
  · rintro ⟨ε, hε, hmem⟩
    let t := min ε δ / 2
    have ht : 0 < t := div_pos (lt_min hε hδ) (by norm_num)
    have htε : t < ε := lt_of_lt_of_le (by dsimp [t]; linarith [lt_min hε hδ])
      (min_le_left ε δ)
    have htδ : t < δ := lt_of_lt_of_le (by dsimp [t]; linarith [lt_min hε hδ])
      (min_le_right ε δ)
    have hm : p + t • u ∈ {x | x - p ∈ V ∧ 0 ≤ ℓ (x - p)} ∩ ball p r :=
      hlocal ▸ ⟨hmem t ht htε, hnear t ht htδ⟩
    have hV := hm.1.1
    have hℓ := hm.1.2
    change p + t • u - p ∈ V at hV
    rw [add_sub_cancel_left] at hV
    change 0 ≤ ℓ (p + t • u - p) at hℓ
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at hℓ
    exact ⟨(Submodule.smul_mem_iff V ht.ne').mp hV, nonneg_of_mul_nonneg_right hℓ ht⟩
  · rintro ⟨huV, huℓ⟩
    refine ⟨δ, hδ, fun t ht htδ => ?_⟩
    have hm : p + t • u ∈ K ∩ ball p r := by
      rw [hlocal]
      refine ⟨?_, hnear t ht htδ⟩
      change p + t • u - p ∈ V ∧ 0 ≤ ℓ (p + t • u - p)
      rw [add_sub_cancel_left, map_smul, smul_eq_mul]
      exact ⟨V.smul_mem t huV, mul_nonneg ht.le huℓ⟩
    exact hm.1

/-- Step 3 of the V4 proof of `host_step_step5_frame` (V4 3.6, F1):
"near a point of the relative interior of a codimension-one face,
a polyhedral manifold cell is a half-space on the recorded side".
For a single consecutive pair of listed flag cells, the local side is a
half-space in the upper cell's direction space, with the lower cell as wall. -/
private theorem host_step_step5_frame_step3_flag_side
    {A : S.ι} (F : FacetFlag S A) (j : FlagStep d) :
    ∃ ℓ : E d →ₗ[ℝ] ℝ,
      (∀ x, x ∈ cellDirection (F.cell ⟨j.val, j.property.1, by omega⟩).val.carrier ↔
        x ∈ cellDirection (F.cell ⟨j.val + 1, by omega, j.property.2⟩).val.carrier ∧
          ℓ x = 0) ∧
      flagSide F j =
        {x | x ∈ cellDirection (F.cell ⟨j.val + 1, by omega, j.property.2⟩).val.carrier ∧
          0 ≤ ℓ x} := by
  let lo : FlagIndex d := ⟨j.val, j.property.1, by omega⟩
  let hi : FlagIndex d := ⟨j.val + 1, by omega, j.property.2⟩
  let e := (F.cell lo).val
  let f := (F.cell hi).val
  let p := cellAnchor e
  have hp : p ∈ relint e.carrier := cellAnchor_mem e
  have hsub : e.carrier ⊆ f.carrier := F.nested lo hi (by dsimp [lo, hi]; omega)
  have hdim : f.dim = e.dim + 1 := by
    dsimp [e, f]
    rw [F.dimension, F.dimension]
  obtain ⟨r, hr, hboundary⟩ := host_step_step5_frame_step3_flag_side_step2_boundary_patch
    (S.cx A) e f (F.cell lo).property (F.cell hi).property hsub hdim p hp
  obtain ⟨ℓ, hker⟩ := host_step_step5_frame_step3_flag_side_step3_wall
    (cellDirection e.carrier) (cellDirection f.carrier)
    (AffineSubspace.direction_le (affineSpan_mono ℝ hsub))
    (by rw [e.flat.dimension, f.flat.dimension]; exact hdim)
  obtain ⟨m, hm, hlocal⟩ := host_step_step5_frame_step3_flag_side_step5_relative_halfball
    e f hsub p hp r hr hboundary ℓ hker
  refine ⟨m, ?_, ?_⟩
  · intro x
    change x ∈ cellDirection e.carrier ↔ x ∈ cellDirection f.carrier ∧ m x = 0
    rw [hm]
    exact hker x
  · exact host_step_step5_frame_step3_flag_side_step6_tangent
      f.carrier p (cellDirection f.carrier) m r hr hlocal

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
  obtain ⟨p, q, hpq, hseg, hvec⟩ := host_step_step5_frame_step1_chain_segment z
  obtain ⟨_, hsides, hNorient, hinward⟩ := halign
  have heq : N.prototypeFrame n '' segment ℝ p q =
      H.prototypeFrame n '' segment ℝ p q := by
    change N.prototypeFrame n '' (host_step_edge z).val.carrier =
      H.prototypeFrame n '' ((P.sideFlag ι b).cell edgeIndex).val.carrier at hedge
    rw [← hchain edgeIndex] at hedge
    change N.prototypeFrame n '' (host_step_edge z).val.carrier =
      H.prototypeFrame n '' (host_step_edge z).val.carrier at hedge
    rwa [hseg] at hedge
  rw [hvec] at horient hNorient
  obtain ⟨hp, hq⟩ := host_step_step5_frame_step1_oriented_endpoints
    (H.prototypeFrame n) (N.prototypeFrame n) p q
    ((host_step_flagFrame H n ι b).linear (P.flag ι).direction) hpq heq horient hNorient
  let L := (H.prototypeFrame n).linear
  let R : Ortho d := H.frame.linearIsometryEquiv.symm.trans N.frame.linearIsometryEquiv
  have hR (x : E d) : R (L x) = (N.prototypeFrame n).linear x := by
    change N.frame.linearIsometryEquiv
      (H.frame.linearIsometryEquiv.symm (H.frame.linearIsometryEquiv ((S.σ ^ n) x))) =
        N.frame.linearIsometryEquiv ((S.σ ^ n) x)
    rw [LinearIsometryEquiv.symm_apply_apply]
  have hdir : R (L (q - p)) = L (q - p) := by
    rw [hR]
    change (N.prototypeFrame n).linear (q - p) = (H.prototypeFrame n).linear (q - p)
    change (N.prototypeFrame n).toAffineMap.linear (q -ᵥ p) =
      (H.prototypeFrame n).toAffineMap.linear (q -ᵥ p)
    rw [AffineMap.linearMap_vsub, AffineMap.linearMap_vsub]
    change N.prototypeFrame n q - N.prototypeFrame n p =
      H.prototypeFrame n q - H.prototypeFrame n p
    rw [hp, hq]
  have hfixedge : ∀ x ∈ cellDirection ((P.sideFlag ι b).cell edgeIndex).val.carrier,
      R (L x) = L x := by
    rw [← hchain edgeIndex]
    change ∀ x ∈ cellDirection (host_step_edge z).val.carrier, R (L x) = L x
    rw [hseg, cellDirection, direction_affineSpan, vectorSpan_segment]
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [vsub_eq_sub, map_smul, hdir]
  have hside (j : FlagStep d) : R '' (L '' flagSide (P.sideFlag ι b) j) =
      L '' flagSide (P.sideFlag ι b) j := by
    have hc : flagSide z.2.chain.val j = flagSide (P.sideFlag ι b) j := by
      unfold flagSide
      rw [hchain, hchain]
    calc
      _ = (N.prototypeFrame n).linear '' flagSide (P.sideFlag ι b) j := by
        rw [image_image]
        congr 1
        funext x
        exact hR x
      _ = _ := by simpa only [hc] using hsides j
  have hfixflag : ∀ (j : ℕ) (hj : 1 ≤ j ∧ j < d),
      ∀ x ∈ cellDirection ((P.sideFlag ι b).cell ⟨j, hj⟩).val.carrier,
        R (L x) = L x := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      by_cases hj1 : j = 1
      · subst j
        exact hfixedge
      · let k : FlagStep d := ⟨j - 1, by omega, by omega⟩
        have hlow := ih (j - 1) (by omega) (show 1 ≤ j - 1 ∧ j - 1 < d by omega)
        have hstep := host_step_step5_frame_step2_transport_side R L _ _ _
          (host_step_step5_frame_step3_flag_side (P.sideFlag ι b) k) hlow (hside k)
        simpa only [k, Nat.sub_add_cancel hj.1] using hstep
  let f : FacetName S H.ty := ⟨(ι.val.sideFacet b).val, by
    rw [hH]
    exact (ι.val.sideFacet b).property⟩
  have hfixfacet : ∀ x ∈ cellDirection f.val.carrier, R (L x) = L x := by
    have ht := hfixflag facetIndex.val facetIndex.property
    rwa [host_step_step4_age_one_flag_step6_top ι b] at ht
  have hinside : R '' (L '' tangentCone (S.proto H.ty).carrier (cellAnchor f.val)) =
      L '' tangentCone (S.proto H.ty).carrier (cellAnchor f.val) := by
    calc
      _ = (N.prototypeFrame n).linear ''
          tangentCone (S.proto H.ty).carrier (cellAnchor f.val) := by
        rw [image_image]
        congr 1
        funext x
        exact hR x
      _ = _ := by simpa only [hty, hf] using hinward
  have hall := host_step_step5_frame_step2_transport_side R L _ _ _
    (host_step_step5_frame_step3_inward_side H.ty f) hfixfacet hinside
  have hlin (x : E d) : (N.prototypeFrame n).linear x = (H.prototypeFrame n).linear x :=
    (hR x).symm.trans (hall x Submodule.mem_top)
  have hproto : N.prototypeFrame n = H.prototypeFrame n := by
    apply AffineEquiv.ext
    intro x
    have hx := hlin (x - p)
    change (N.prototypeFrame n).toAffineMap.linear (x -ᵥ p) =
      (H.prototypeFrame n).toAffineMap.linear (x -ᵥ p) at hx
    rw [AffineMap.linearMap_vsub, AffineMap.linearMap_vsub] at hx
    change N.prototypeFrame n x - N.prototypeFrame n p =
      H.prototypeFrame n x - H.prototypeFrame n p at hx
    rw [hp] at hx
    exact sub_left_injective hx
  apply FramedNode.ext hty
  apply AffineIsometryEquiv.ext
  intro x
  have hx := congrArg (fun φ : E d ≃ᵃ[ℝ] E d => φ ((S.σ ^ n).symm x)) hproto
  change N.frame ((S.σ ^ n) ((S.σ ^ n).symm x)) =
    H.frame ((S.σ ^ n) ((S.σ ^ n).symm x)) at hx
  simpa only [LinearEquiv.apply_symm_apply] using hx

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
