import Enforce.Compiler

/-!
# Blocks, decoded levels, and the four parser invariants

R1--R3, V4 §3.0, 3.2 and §3.2. Physical tiles are decoded through the
stage-4 `compilerLeaf` and `compilerFrame`; states and packets are the original
stage-3 objects. Nodes retain their full Euclidean frames.

DEVIATION: `Block` is defined at every natural height, rather than only above K.
This makes the nodes inside certificate blocks actual blocks of the same type.
The induction theorems still require n ≥ K. Boundary attachment is chosen from
the unique constant leaf readout in (I5); primitive attachment initially uses
the canonical left child. R5 will prove equality with the right child's readout.
No provider interpretation is imposed on packets along persistent faults.

Inner node sets retain the exact frames, so overlapping descriptions of a node
index the same state. The later nesting predicate requires literal agreement
of these state assignments; membership and constancy proofs are irrelevant.
-/

open Set Metric

noncomputable section

open private incidentForest_step1_placeChild_pow from Enforce.Source.Headers

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d} {P : Params S}
variable {C : ClusterData S P}

/-- R1, V4 §3.0: the framed native node decoded from an augmented physical tile. -/
def tileNode (t : PlacedMarkedTile (systemM S P C)) : FramedNode S :=
  ⟨(compilerLeaf C t).prototype, compilerFrame C t⟩

/-- R1, V4 §3.0: exact native subdivision in the actual tiling, with both
prototype type and full frame prescribed at every depth-n leaf. -/
def IsBlock (Y : MarkedTiling (systemM S P C)) (n : ℕ) (N : FramedNode S) : Prop :=
  ∀ w : S.RoleWord N.ty n, ∃ t ∈ Y.tiles,
    tileNode t = (S.nativeTile N.ty n w).move N.frame

/-- R1, V4 §3.0: a framed block with all prescribed leaves actual in Y.
DEVIATION: heights below K are allowed to represent inner nodes uniformly;
all assertions about the induction's decoded levels retain their n ≥ K premise. -/
@[ext]
structure Block (Y : MarkedTiling (systemM S P C)) (n : ℕ) where
  /-- R1, V4 §3.0: the prototype and full isometric frame. -/
  node : FramedNode S
  /-- R1, V4 §3.0: actual tiles at every standard native address. -/
  actual : IsBlock Y n node

namespace Parser

/-- R1, V4 §3.0: the root itself is a depth-zero descendant. -/
theorem descendant_refl (N : FramedNode S) (n : ℕ) : N.IsDescendant n N n := by
  refine ⟨0, rfl, (), ?_⟩
  cases N with
  | mk ty frame =>
    show (⟨ty, frame⟩ : FramedNode S) = ⟨ty, (AffineIsometryEquiv.refl ℝ (E d)).trans frame⟩
    rw [AffineIsometryEquiv.refl_trans]

open private birth_ascent_routing_step3_desc_trans from Enforce.Source.Routing in
/-- R1, V4 §3.0: descendant inclusion composes with exact frames and heights. -/
theorem descendant_trans (A B D : FramedNode S) (a b e : ℕ)
    (hAB : A.IsDescendant a B b) (hBD : B.IsDescendant b D e) :
    A.IsDescendant a D e := by
  exact birth_ascent_routing_step3_desc_trans A B D a b e hAB hBD

/-- R1, V4 §3.0: a descendant has no greater height than its root. -/
theorem descendant_height_le (A B : FramedNode S) (a b : ℕ)
    (h : A.IsDescendant a B b) : a ≤ b := by
  obtain ⟨r, hr, _⟩ := h
  omega

/-- R1, V4 §3.0: an immediate prescribed child is a descendant. -/
theorem child_descendant (N : FramedNode S) (n : ℕ) (i : S.I N.ty) :
    (N.child n i).IsDescendant n N (n + 1) := by
  use 1
  constructor
  · rfl
  · use ⟨i, ()⟩
    rfl

/-- R3, V4 §3.2: every actual prototype has at least one child.
The nonempty prototype interior and substitution cover supply this nonemptiness. -/
theorem roles_nonempty (A : S.ι) : Nonempty (S.I A) := by
  have h := (S.proto A).interior_nonempty
  have hc := S.children_cover A
  by_contra h_empty
  have _ : IsEmpty (S.I A) := ⟨not_nonempty_iff_imp_false.mp h_empty⟩
  have h_union : (⋃ i : S.I A, placedSet (S.child A i).frame (S.proto (S.child A i).ty).carrier) = ∅ := by
    exact Set.iUnion_of_empty _
  rw [h_union] at hc
  have h_nonempty : ((S.proto A).carrier).Nonempty := h.mono interior_subset
  have h_image_nonempty : (S.σ '' (S.proto A).carrier).Nonempty := h_nonempty.image S.σ
  rw [hc] at h_image_nonempty
  exact Set.not_nonempty_empty h_image_nonempty

/-- R1/R12, V4 §3.0, 3.1: exact descendants of an actual hierarchy node
belong to that hierarchy, without requiring an honest source or species membership. -/
theorem hierarchy_descendant_mem {T : Tiling S} (H : CoherentHierarchy S T)
    (n m : ℕ) (N M : FramedNode S) (hN : N ∈ H.nodes n)
    (hM : M.IsDescendant m N n) : M ∈ H.nodes m := by
  obtain ⟨r, rfl, w, rfl⟩ := hM
  induction' r with r ih generalizing N
  · cases N
    dsimp [SubstSystem.descendantNode, FramedNode.move]
    exact hN
  · have hc := H.children_mem (m + r) N hN w.1
    have hi := ih (N.child (m + r) w.1) hc w.2
    exact hi

end Parser

namespace Block

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ} (B : Block Y n)

/-- R1, V4 §3.0: the closed carrier of the framed block. -/
def carrier : Set (E d) := B.node.carrier n

/-- R1, V4 §3.0: nodes inside a block are its sub-blocks, with exact frames. -/
def Contains (m : ℕ) (N : FramedNode S) : Prop := N.IsDescendant m B.node n

/-- R1, V4 §3.0: every inner node has its prescribed actual native subdivision. -/
theorem inner_actual (m : ℕ) (N : FramedNode S) (hN : B.Contains m N) :
    IsBlock Y m N := by
  intro w
  have hw : ((S.nativeTile N.ty m w).move N.frame).IsDescendant 0 N m :=
    ⟨m, (Nat.zero_add m).symm, w, rfl⟩
  obtain ⟨r, hr, v, hv⟩ :=
    Parser.descendant_trans _ N B.node 0 m n hw hN
  have hrn : r = n := by omega
  subst r
  obtain ⟨t, ht, htile⟩ := B.actual v
  exact ⟨t, ht, htile.trans hv.symm⟩

/-- R1, V4 §3.0: a node inside a block, regarded as a block at its own height. -/
def innerBlock (m : ℕ) (N : FramedNode S) (hN : B.Contains m N) : Block Y m :=
  ⟨N, B.inner_actual m N hN⟩

/-- Step 1 of the V4 proof of `tiles_exact` (V4 §3.0): a physical tile is the
height-zero carrier of its decoded framed native node. Only the realizing catalogue
member is used; no rigidity of decoding is needed. -/
private theorem tiles_exact_step1_tile_carrier (t : PlacedMarkedTile (systemM S P C)) :
    t.carrier = (tileNode t).carrier 0 := by
  have hc : t.carrier = placedSet t.placement t.prototype.val.carrier :=
    (Classical.choose_spec (Classical.choose_spec t.realization).2).1
  rw [hc, Compiler.decoration_carrier C t.prototype]
  simp [tileNode, FramedNode.carrier, SubstSystem.supertile, compilerLeaf, compilerFrame]

/-- Step 2 of the V4 proof of `tiles_exact` (V4 §3.0): the placed native leaves
cover the block. -/
private theorem tiles_exact_step2_leaves_cover :
    (⋃ w : S.RoleWord B.node.ty n,
      ((S.nativeTile B.node.ty n w).move B.node.frame).carrier 0) = B.carrier := by
  have key : ∀ w : S.RoleWord B.node.ty n,
      ((S.nativeTile B.node.ty n w).move B.node.frame).carrier 0 =
        placedSet B.node.frame ((S.nativeTile B.node.ty n w).carrier 0) := by
    intro w
    simp only [FramedNode.carrier, FramedNode.move, placedSet, AffineIsometryEquiv.coe_trans,
      Set.image_comp]
  simp_rw [key]
  show (⋃ w, placedSet B.node.frame _) = placedSet B.node.frame (S.supertile n B.node.ty)
  rw [← S.native_cover]
  simp only [placedSet, Set.image_iUnion]

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `tiles_exact` (V4 §3.0): "pick one outside the
(nowhere dense) union of all tile boundaries". A nonempty open set covered by finitely
many closed carriers meets the interior of one of them. -/
private theorem tiles_exact_step3_open_meets_interior {ι : Type} [Finite ι]
    (f : ι → Set (E d)) (hc : ∀ i, IsClosed (f i)) (O : Set (E d)) (hO : IsOpen O)
    (hne : O.Nonempty) (hsub : O ⊆ ⋃ i, f i) : ∃ i, (O ∩ interior (f i)).Nonempty := by
  let g : Option ι → Set (E d) := fun o => o.elim Oᶜ f
  have hgc : ∀ o, IsClosed (g o) := by
    intro o
    cases o with
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

/-- R1, V4 §3.0: the actual tiles in a block are exactly its framed native leaves. -/
theorem tiles_exact :
    {t | t ∈ Y.tiles ∧ t.carrier ⊆ B.carrier} =
      {t | t ∈ Y.tiles ∧ ∃ w : S.RoleWord B.node.ty n,
        tileNode t = (S.nativeTile B.node.ty n w).move B.node.frame} := by
  classical
  apply Set.Subset.antisymm
  · rintro t ⟨ht, hsub⟩
    have hcar : t.carrier = compilerFrame C t ''
        (S.proto (compilerLeaf C t).prototype).carrier := by
      rw [tiles_exact_step1_tile_carrier t]
      simp [tileNode, FramedNode.carrier, SubstSystem.supertile, placedSet]
    have hn : (interior t.carrier).Nonempty := by
      rw [hcar]
      change (interior ((compilerFrame C t).toHomeomorph ''
        (S.proto (compilerLeaf C t).prototype).carrier)).Nonempty
      rw [← (compilerFrame C t).toHomeomorph.image_interior]
      exact (S.proto (compilerLeaf C t).prototype).interior_nonempty.image _
    have hc : ∀ w : S.RoleWord B.node.ty n,
        IsClosed (((S.nativeTile B.node.ty n w).move B.node.frame).carrier 0) := by
      intro w
      have hcpt : IsCompact (S.supertile 0 ((S.nativeTile B.node.ty n w).move B.node.frame).ty) :=
        (S.proto _).compact.image (S.σ ^ 0).toContinuousLinearEquiv.continuous
      exact (hcpt.image (AffineIsometryEquiv.continuous _)).isClosed
    obtain ⟨w, x, hxt, hxw⟩ := tiles_exact_step3_open_meets_interior
      (fun w => ((S.nativeTile B.node.ty n w).move B.node.frame).carrier 0) hc
      (interior t.carrier) isOpen_interior hn
      (by
        rw [tiles_exact_step2_leaves_cover B]
        exact fun y hy => hsub (interior_subset hy))
    obtain ⟨t', ht', htile⟩ := B.actual w
    have hcar' : t'.carrier = ((S.nativeTile B.node.ty n w).move B.node.frame).carrier 0 := by
      rw [tiles_exact_step1_tile_carrier t', htile]
    have heq : t = t' := by
      by_contra hne
      rw [← hcar'] at hxw
      exact Set.disjoint_left.mp (Y.disjoint ht ht' hne) hxt hxw
    subst heq
    exact ⟨ht, w, htile⟩
  · rintro t ⟨ht, w, htile⟩
    refine ⟨ht, ?_⟩
    rw [tiles_exact_step1_tile_carrier t, htile, ← tiles_exact_step2_leaves_cover B]
    exact Set.subset_iUnion
      (fun w => ((S.nativeTile B.node.ty n w).move B.node.frame).carrier 0) w

/-- R1, V4 §3.0: the union of its actual native tiles is the whole block. -/
theorem union_tiles : B.carrier =
    ⋃ t ∈ {t | t ∈ Y.tiles ∧ t.carrier ⊆ B.carrier}, t.carrier := by
  sorry

/-- R1, V4 §3.0: a block has compact, regular closed support and nonempty interior. -/
theorem carrier_regular : IsCompact B.carrier ∧ IsRegularClosed B.carrier ∧
    (interior B.carrier).Nonempty := by
  simp only [Block.carrier, FramedNode.carrier, placedSet, SubstSystem.supertile, Set.image_image]
  let e1 := (S.σ ^ n).toContinuousLinearEquiv.toHomeomorph
  let e2 := B.node.frame.toHomeomorph
  let e := e1.trans e2
  have heq : (fun (x : E d) => B.node.frame ((S.σ ^ n) x)) '' (S.proto B.node.ty).carrier =
             e '' (S.proto B.node.ty).carrier := rfl
  rw [heq]
  have Hc : IsCompact (e '' (S.proto B.node.ty).carrier) :=
    (S.proto B.node.ty).compact.image e.continuous
  have Hr : IsRegularClosed (e '' (S.proto B.node.ty).carrier) := by
    change closure (interior (e '' _)) = e '' _
    rw [← Homeomorph.image_interior, ← Homeomorph.image_closure]
    rw [(S.proto _).regularClosed]
  have Hn : (interior (e '' (S.proto B.node.ty).carrier)).Nonempty := by
    rw [← Homeomorph.image_interior]
    exact (S.proto _).interior_nonempty.image e
  exact ⟨Hc, Hr, Hn⟩

end Block

/-- R1/R7, V4 §3.0, 3.7: a geometric level, before assigning its new root states.
The family is a set of genuine blocks, with pairwise disjoint interiors and coverage. -/
structure GeometricLevel (Y : MarkedTiling (systemM S P C)) (n : ℕ) where
  /-- R1, V4 §3.0: the chosen height-n blocks. -/
  blocks : Set (Block Y n)
  /-- R1, V4 §3.0: distinct members have disjoint interiors. -/
  disjoint : blocks.PairwiseDisjoint (fun B => interior B.carrier)
  /-- R1, V4 §3.0: closed blocks cover the whole ambient Euclidean space. -/
  cover : ∀ x : E d, ∃ B ∈ blocks, x ∈ B.carrier

namespace GeometricLevel

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ} (G : GeometricLevel Y n)

/-- R1, V4 §3.0: the set of framed roots of the chosen blocks. -/
def roots : Set (FramedNode S) := (fun B => B.node) '' G.blocks

/-- R1, V4 §3.0: all sub-blocks at their own heights, including the roots. -/
def nodes (m : ℕ) : Set (FramedNode S) :=
  {N | ∃ B ∈ G.blocks, B.Contains m N}

/-- R1, V4 §3.0: the chosen family has no nodes above its root height. -/
theorem nodes_height (m : ℕ) (N : FramedNode S) (hN : N ∈ G.nodes m) : m ≤ n := by
  obtain ⟨B, _, h⟩ := hN
  exact Parser.descendant_height_le N B.node m n h

/-- R1, V4 §3.0: each chosen root is one of the nodes carrying a state. -/
theorem root_mem (B : Block Y n) (hB : B ∈ G.blocks) : B.node ∈ G.nodes n :=
  ⟨B, hB, Parser.descendant_refl B.node n⟩

/-- R1, V4 §3.0: all states at height n belong exactly to the chosen roots. -/
theorem nodes_top : G.nodes n = G.roots := by
  ext N
  constructor
  · intro h
    obtain ⟨B, hB, hBN⟩ := h
    have hBN' : N = B.node := by
      obtain ⟨r, hr, w, eq⟩ := hBN
      have : r = 0 := by omega
      subst r
      have h1 : S.descendantNode B.node.ty n 0 w = ⟨B.node.ty, 1⟩ := rfl
      rw [h1] at eq
      have h2 : (⟨B.node.ty, 1⟩ : FramedNode S).move B.node.frame = B.node := by
        cases B.node
        rfl
      rw [h2] at eq
      exact eq
    rw [hBN']
    exact ⟨B, hB, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    exact G.root_mem B hB

/-- R1, V4 §3.0: every node in the level is itself a genuine block. -/
theorem node_actual (m : ℕ) (N : FramedNode S) (hN : N ∈ G.nodes m) : IsBlock Y m N := by
  obtain ⟨B, _, h⟩ := hN
  exact B.inner_actual m N h

/-- R1, V4 §3.0: sub-block closure of the node family, with exact descendant frames. -/
theorem descendant_mem (m a : ℕ) (N D : FramedNode S) (hN : N ∈ G.nodes m)
    (hD : D.IsDescendant a N m) : D ∈ G.nodes a := by
  obtain ⟨B, hB, h⟩ := hN
  exact ⟨B, hB, Parser.descendant_trans D N B.node a m n hD h⟩

/-- R1, V4 §3.0: immediate children of all positive-height inner nodes are inner nodes. -/
theorem child_mem (m : ℕ) (N : FramedNode S) (hN : N ∈ G.nodes (m + 1))
    (i : S.I N.ty) : N.child m i ∈ G.nodes m :=
  G.descendant_mem (m + 1) m N (N.child m i) hN (Parser.child_descendant N m i)

/-- At a fixed height, the expanded prototypes are again polyhedral manifold
domains, as used in V4 1.0(d): "placed copies of the finitely many σ^n A". -/
private def locallyFinite_supertileDomain (n : ℕ) (A : S.ι) : PolyManifoldDomain d := by
  classical
  let e := (S.σ ^ n).toContinuousLinearEquiv.toHomeomorph
  refine {
    carrier := S.supertile n A
    polyhedral := ?_
    compact := (S.proto A).compact.image e.continuous
    regularClosed := ?_
    interior_connected := ?_
    interior_nonempty := ?_
    frontier_manifold := ?_
  }
  · obtain ⟨s, hs⟩ := (S.proto A).polyhedral
    refine ⟨s.image (fun p => p.image (S.σ ^ n)), ?_⟩
    have himage (p : Finset (E d)) :
        (S.σ ^ n) '' convexHull ℝ (p : Set (E d)) =
          convexHull ℝ (p.image (S.σ ^ n) : Set (E d)) := by
      rw [Finset.coe_image]
      exact (S.σ ^ n).toLinearMap.image_convexHull _
    change (S.σ ^ n) '' (S.proto A).carrier = _
    rw [hs]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨p, hp, hyp⟩ := Set.mem_iUnion₂.mp hy
      refine Set.mem_iUnion₂.mpr
        ⟨p.image (S.σ ^ n), Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
      rw [← himage]
      exact Set.mem_image_of_mem _ hyp
    · intro hx
      obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      rw [← himage] at hxq
      obtain ⟨y, hy, rfl⟩ := hxq
      exact ⟨y, Set.mem_iUnion₂.mpr ⟨p, hp, hy⟩, rfl⟩
  · change closure (interior (e '' (S.proto A).carrier)) = e '' (S.proto A).carrier
    rw [← e.image_interior, ← e.image_closure, (S.proto A).regularClosed]
  · change IsConnected (interior (e '' (S.proto A).carrier))
    rw [← e.image_interior]
    exact (S.proto A).interior_connected.image e e.continuous.continuousOn
  · change (interior (e '' (S.proto A).carrier)).Nonempty
    rw [← e.image_interior]
    exact (S.proto A).interior_nonempty.image e
  · change IsLocallyEuclidean (d - 1) (frontier (e '' (S.proto A).carrier))
    rw [← e.image_frontier]
    intro p
    let f := e.image (frontier (S.proto A).carrier)
    obtain ⟨U, hU, hpU, V, hV, ⟨φ⟩⟩ := (S.proto A).frontier_manifold (f.symm p)
    exact ⟨f '' U, f.isOpenMap U hU, ⟨f.symm p, hpU, f.apply_symm_apply p⟩,
      V, hV, ⟨(f.image U).symm.trans φ⟩⟩

/-- R1, V4 §3.0, 1.0(d): each fixed geometric level is locally finite. -/
theorem locallyFinite :
    LocallyFinite (fun B : {B // B ∈ G.blocks} => B.val.carrier) ∧
      ∀ Q : Set (E d), Bornology.IsBounded Q →
        {B : Block Y n | B ∈ G.blocks ∧ (Q ∩ B.carrier).Nonempty}.Finite := by
  have hd : Pairwise (fun B D : {B // B ∈ G.blocks} => Disjoint
      (interior B.val.carrier) (interior D.val.carrier)) := by
    intro B D hBD
    exact G.disjoint B.property D.property (fun h => hBD (Subtype.ext h))
  have h := locallyFinite_disjointInteriors (locallyFinite_supertileDomain (S := S) n)
    (fun B : {B // B ∈ G.blocks} => B.val.node.ty)
    (fun B : {B // B ∈ G.blocks} => B.val.node.frame) hd
  refine ⟨h.1, fun Q hQ => ?_⟩
  exact ((h.2 Q hQ).image Subtype.val).subset (by
    intro B hB
    exact ⟨⟨B, hB.1⟩, hB.2, rfl⟩)

end GeometricLevel

/-- R1, V4 §3.0: decoded geometry and an honest state on every inner node.
The four invariant predicates are separate, so an induction step can first
construct the geometry and state data and then establish exactly (I1),(I2),(I4),(I5). -/
structure DecodedLevel (Y : MarkedTiling (systemM S P C)) (n : ℕ) where
  /-- R1, V4 §3.0: the chosen geometric level. -/
  geometry : GeometricLevel Y n
  /-- R1, V4 §3.0: states of every node inside the chosen blocks. -/
  state : ∀ m : ℕ, {N // N ∈ geometry.nodes m} → State P
  /-- R1, V4 §3.0: the assignment takes values in the honest alphabet 𝒮. -/
  state_honest : ∀ m N, state m N ∈ honestStates S P

namespace DecodedLevel

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)

/-- R1, V4 §3.0: read a state at a framed inner node with its membership proof. -/
def stateAt (m : ℕ) (N : FramedNode S) (hN : N ∈ D.geometry.nodes m) : State P :=
  D.state m ⟨N, hN⟩

/-- R1/R3, V4 §3.0, §3.2: the state of a chosen root block. -/
def blockState (B : Block Y n) (hB : B ∈ D.geometry.blocks) : State P :=
  D.stateAt n B.node (D.geometry.root_mem B hB)

end DecodedLevel

namespace Parser

variable (Y : MarkedTiling (systemM S P C))

/-- R1, V4 §3.0 (I5): an actual native facet piece of a node.
Ownership uses the standard framed subdivision, not just set-theoretic intersection. -/
def IsFacetPiece (m : ℕ) (N : FramedNode S) (F : FacetName S N.ty)
    (t : PlacedMarkedTile (systemM S P C)) (f : FacetName S (tileNode t).ty) : Prop :=
  t ∈ Y.tiles ∧ (tileNode t).IsDescendant 0 N m ∧
    (tileNode t).cell 0 f.val ⊆ N.cell m F.val

/-- R1, V4 §3.0 (I5): every actual native piece on the facet reads the same
packet, including NULL. Readouts come from the tiles' honest leaf pre-patterns. -/
def ConstantPacket (m : ℕ) (N : FramedNode S) (F : FacetName S N.ty)
    (q : Option (Packet P)) : Prop :=
  ∀ (t : PlacedMarkedTile (systemM S P C)) (f : FacetName S (tileNode t).ty),
    IsFacetPiece Y m N F t f → leafPacket (compilerLeaf C t) f.val = q

/-- R1, V4 §3.0 (I5): a boundary packet exists uniquely at every named facet.
Existence is constancy; uniqueness follows because heredity supplies a native piece. -/
def BoundaryPackets (m : ℕ) (N : FramedNode S) : Prop :=
  ∀ F : FacetName S N.ty, ∃! q : Option (Packet P), ConstantPacket Y m N F q

/-- R1, V4 §3.0 (I5): a block has an actual native piece on each boundary facet.
Nonemptiness comes from the facet and the hereditary native subdivision. -/
theorem facet_piece_exists (m : ℕ) (N : FramedNode S) (hN : IsBlock Y m N)
    (F : FacetName S N.ty) :
    ∃ (t : PlacedMarkedTile (systemM S P C)) (f : FacetName S (tileNode t).ty),
    IsFacetPiece Y m N F t f := by
  classical
  obtain ⟨parts, hparts⟩ := S.heredity_iter N.ty m F.val (Finset.mem_filter.mp F.property).1
  have hF : (F.val.carrier : Set (E d)).Nonempty := F.val.flat.relint_nonempty.mono intrinsicInterior_subset
  obtain ⟨x, hxf⟩ := hF
  have hσx : (S.σ ^ m) x ∈ (S.σ ^ m) '' F.val.carrier := ⟨x, hxf, rfl⟩
  rw [hparts] at hσx
  obtain ⟨q, hq, y, hy, hxy⟩ := Set.mem_iUnion₂.mp hσx
  obtain ⟨t, ht, hnode⟩ := hN q.1
  let g : FacetName S (tileNode t).ty := ⟨q.2.val, by
    rw [hnode]
    exact Finset.mem_filter.mpr ⟨q.2.property.1,
      q.2.property.2.trans (Finset.mem_filter.mp F.property).2⟩⟩
  have hdesc : (tileNode t).IsDescendant 0 N m := ⟨m, by omega, q.1, hnode⟩
  have hsub : (tileNode t).cell 0 g.val ⊆ N.cell m F.val := by
    rintro z ⟨w, hw, rfl⟩
    have hmem : (S.nativeTile N.ty m q.1).frame w ∈ (S.σ ^ m) '' F.val.carrier := by
      rw [hparts]
      exact Set.mem_iUnion₂.mpr ⟨q, hq, w, hw, rfl⟩
    obtain ⟨z, hz, he⟩ := hmem
    refine ⟨z, hz, ?_⟩
    rw [hnode]
    change N.frame ((S.σ ^ m) z) = N.frame ((S.nativeTile N.ty m q.1).frame w)
    exact congrArg N.frame he
  exact ⟨t, g, ht, hdesc, hsub⟩


/-- R1, V4 §3.0 (I5): one genuine facet piece identifies a constant packet.
The piece is supplied by heredity, so equality does not follow from an empty
universal quantifier over nonexistent boundary tiles. -/
theorem constantPacket_unique (m : ℕ) (N : FramedNode S) (hN : IsBlock Y m N)
    (F : FacetName S N.ty) (q q' : Option (Packet P))
    (hq : ConstantPacket Y m N F q) (hq' : ConstantPacket Y m N F q') : q = q' := by
  obtain ⟨t, f, h⟩ := facet_piece_exists Y m N hN F
  exact (hq t f h).symm.trans (hq' t f h)

/-- R1, V4 §3.0 (I5): boundary attachment is inherited along an actual
descendant facet track. This concerns the packet readout, including NULL;
it asserts no provider interpretation of a persistent-fault packet. -/
theorem boundaryPacket_inherited (n m : ℕ) (N M : FramedNode S)
    (hM : IsBlock Y m M) (hdesc : M.IsDescendant m N n)
    (F : FacetName S N.ty) (f : FacetName S M.ty)
    (hsub : M.cell m f.val ⊆ N.cell n F.val)
    (hNpacket : BoundaryPackets Y n N) (hMpacket : BoundaryPackets Y m M) :
    Classical.choose (hNpacket F) = Classical.choose (hMpacket f) := by
  obtain ⟨t, f', h_piece⟩ := facet_piece_exists Y m M hM f
  have h_piece_N : IsFacetPiece Y n N F t f' := ⟨
    h_piece.1,
    descendant_trans (tileNode t) M N 0 m n h_piece.2.1 hdesc,
    h_piece.2.2.trans hsub
  ⟩
  have h1 := (Classical.choose_spec (hMpacket f)).1 t f' h_piece
  have h2 := (Classical.choose_spec (hNpacket F)).1 t f' h_piece_N
  exact h2.symm.trans h1

end Parser

/-- R1, V4 §3.0 (I5): the packet attached to F from N in the actual output Y.
It is chosen from the unique constant leaf readout asserted by (I5); no source
provider, invented state or arbitrary packet is selected. -/
def attachedPacket {Y : MarkedTiling (systemM S P C)} {m : ℕ} {N : FramedNode S}
    (h : Parser.BoundaryPackets Y m N) (F : FacetName S N.ty) : Option (Packet P) :=
  Classical.choose (h F)

/-- R1, V4 §3.0 (I5): attachment agrees with every actual tile piece on that side. -/
theorem attachedPacket_spec {Y : MarkedTiling (systemM S P C)} {m : ℕ}
    {N : FramedNode S} (h : Parser.BoundaryPackets Y m N) (F : FacetName S N.ty) :
    Parser.ConstantPacket Y m N F (attachedPacket h F) :=
  (Classical.choose_spec (h F)).1

/-- R1, V4 §3.0 (I5): a different proof of constancy gives the identical packet. -/
theorem attachedPacket_proof_independent {Y : MarkedTiling (systemM S P C)} {m : ℕ}
    {N : FramedNode S} (h h' : Parser.BoundaryPackets Y m N) (F : FacetName S N.ty) :
    attachedPacket h F = attachedPacket h' F := rfl

/-- R1, V4 §3.0 (I5): read attachment directly on any named actual leaf piece. -/
theorem attachedPacket_eq_leaf {Y : MarkedTiling (systemM S P C)} {m : ℕ}
    {N : FramedNode S} (h : Parser.BoundaryPackets Y m N) (F : FacetName S N.ty)
    (t : PlacedMarkedTile (systemM S P C)) (f : FacetName S (tileNode t).ty)
    (hpiece : Parser.IsFacetPiece Y m N F t f) :
    attachedPacket h F = leafPacket (compilerLeaf C t) f.val :=
  (attachedPacket_spec h F t f hpiece).symm

namespace Parser

/-- R1/R5, V4 §3.0, 3.4: a primitive facet in an arbitrary output subdivision.
This is the geometric analogue of a source `PrimitiveOccurrence`; it requires
no honest hierarchy on Y. The canonical incidence fixes its two owning children. -/
structure BornFacet (P : Params S) where
  /-- R1, V4 §3.0: positive birth height. -/
  height : ℕ
  /-- R1, V4 §3.0: a birth has immediate children. -/
  positive : 1 ≤ height
  /-- R1, V4 §3.0: the full framed birth node. -/
  birth : FramedNode S
  /-- R1, V4 §3.0: the canonical side-independent primitive incidence. -/
  incidence : P.Incidence
  /-- R1, V4 §3.0: the incidence belongs to this birth-parent prototype. -/
  parent_type : incidence.val.ty = birth.ty

namespace BornFacet

variable (g : BornFacet P)

/-- R1/R5, V4 §3.0, 3.4: the actual primitive carrier in ambient coordinates. -/
def carrier : Set (E d) :=
  P.incidencePlacement g.birth g.height g.incidence '' g.incidence.val.leftFacet.val.carrier

/-- R1/R5, V4 §3.0, 3.4: the canonical left child with its exact substitution frame.
Using the incidence's equal parent type avoids transporting its dependent role. -/
def leftNode : FramedNode S :=
  (⟨g.incidence.val.ty, g.birth.frame⟩ : FramedNode S).child (g.height - 1)
    g.incidence.val.left

/-- R1/R5, V4 §3.0, 3.4: the canonical right child in the same framed parent. -/
def rightNode : FramedNode S :=
  (⟨g.incidence.val.ty, g.birth.frame⟩ : FramedNode S).child (g.height - 1)
    g.incidence.val.right

/-- R1/R5, V4 §3.0, 3.4: the two child-facet names give exactly the same carrier. -/
theorem sides_carrier :
    g.leftNode.cell (g.height - 1) g.incidence.val.leftFacet.val = g.carrier ∧
      g.rightNode.cell (g.height - 1) g.incidence.val.rightFacet.val = g.carrier := by
  have H_paired := g.incidence.val.paired
  dsimp [placedSet] at H_paired
  constructor
  · have h_leftNode : g.leftNode.prototypeFrame (g.height - 1) = P.incidencePlacement g.birth g.height g.incidence := by
      ext1 x
      dsimp [BornFacet.leftNode, Params.incidencePlacement, FramedNode.prototypeFrame, FramedNode.child]
      have h_pow : g.height - 1 + 1 = g.height := Nat.sub_add_cancel g.positive
      change g.birth.frame (S.placeChild (g.height - 1) g.incidence.val.left ((S.σ ^ (g.height - 1)) x)) =
        g.birth.frame ((S.σ ^ g.height) (S.σ.symm ((S.child g.incidence.val.ty g.incidence.val.left).frame x)))
      congr 1
      rw [incidentForest_step1_placeChild_pow]
      have H_symm := S.σ.apply_symm_apply ((S.child g.incidence.val.ty g.incidence.val.left).frame x)
      nth_rw 2 [← h_pow]
      rw [pow_add, pow_one]
      change (S.σ ^ (g.height - 1)) ((S.child g.incidence.val.ty g.incidence.val.left).frame x) =
        (S.σ ^ (g.height - 1)) (S.σ (S.σ.symm ((S.child g.incidence.val.ty g.incidence.val.left).frame x)))
      rw [H_symm]
    have h_leftNode' : ⇑(g.leftNode.prototypeFrame (g.height - 1)) = ⇑(P.incidencePlacement g.birth g.height g.incidence) := by
      rw [h_leftNode]
    rw [BornFacet.carrier, FramedNode.cell, h_leftNode']
  · dsimp [BornFacet.carrier, FramedNode.cell, Params.incidencePlacement]
    have H_paired2 : ⇑(S.child g.incidence.val.ty g.incidence.val.right).frame '' g.incidence.val.rightFacet.val.carrier =
      ⇑(S.child g.incidence.val.ty g.incidence.val.left).frame '' g.incidence.val.leftFacet.val.carrier := H_paired.symm
    have h_rightNode : ⇑(g.rightNode.prototypeFrame (g.height - 1)) = (⇑(g.birth.prototypeFrame g.height) ∘ ⇑S.σ.symm) ∘ ⇑(S.child g.incidence.val.ty g.incidence.val.right).frame := by
      ext1 x
      dsimp [BornFacet.rightNode, FramedNode.prototypeFrame, FramedNode.child]
      have h_pow : g.height - 1 + 1 = g.height := Nat.sub_add_cancel g.positive
      change g.birth.frame (S.placeChild (g.height - 1) g.incidence.val.right ((S.σ ^ (g.height - 1)) x)) =
        g.birth.frame ((S.σ ^ g.height) (S.σ.symm ((S.child g.incidence.val.ty g.incidence.val.right).frame x)))
      congr 1
      rw [incidentForest_step1_placeChild_pow]
      have H_symm := S.σ.apply_symm_apply ((S.child g.incidence.val.ty g.incidence.val.right).frame x)
      nth_rw 2 [← h_pow]
      rw [pow_add, pow_one]
      change (S.σ ^ (g.height - 1)) ((S.child g.incidence.val.ty g.incidence.val.right).frame x) =
        (S.σ ^ (g.height - 1)) (S.σ (S.σ.symm ((S.child g.incidence.val.ty g.incidence.val.right).frame x)))
      rw [H_symm]
    rw [h_rightNode]
    have h_image : (⇑(g.birth.prototypeFrame g.height) ∘ ⇑S.σ.symm) ∘ ⇑(S.child g.incidence.val.ty g.incidence.val.right).frame '' g.incidence.val.rightFacet.val.carrier =
      (⇑(g.birth.prototypeFrame g.height) ∘ ⇑S.σ.symm) '' (⇑(S.child g.incidence.val.ty g.incidence.val.right).frame '' g.incidence.val.rightFacet.val.carrier) := Set.image_comp _ _ _
    rw [h_image]
    have h_image2 : (⇑(g.birth.prototypeFrame g.height) ∘ ⇑S.σ.symm) ∘ ⇑(S.child g.incidence.val.ty g.incidence.val.left).frame '' g.incidence.val.leftFacet.val.carrier =
      (⇑(g.birth.prototypeFrame g.height) ∘ ⇑S.σ.symm) '' (⇑(S.child g.incidence.val.ty g.incidence.val.left).frame '' g.incidence.val.leftFacet.val.carrier) := Set.image_comp _ _ _
    rw [h_image2]
    rw [H_paired2]

/-- R1/R5, V4 §3.0, 3.4: both owning children are actual descendants of the birth. -/
theorem sides_descendant :
    g.leftNode.IsDescendant (g.height - 1) g.birth g.height ∧
      g.rightNode.IsDescendant (g.height - 1) g.birth g.height := by
  dsimp [leftNode, rightNode]
  have hpos : g.height = g.height - 1 + 1 := (Nat.sub_add_cancel g.positive).symm
  have heq : (⟨g.incidence.val.ty, g.birth.frame⟩ : FramedNode S) = g.birth := by
    ext
    · exact g.parent_type
    · rfl
  exact ⟨heq ▸ hpos ▸ child_descendant ⟨g.incidence.val.ty, g.birth.frame⟩ (g.height - 1) g.incidence.val.left,
    heq ▸ hpos ▸ child_descendant ⟨g.incidence.val.ty, g.birth.frame⟩ (g.height - 1) g.incidence.val.right⟩

/-- R1/R5/R12, V4 §3.0, 3.4, 3.1: the left owner of an actual hierarchy
birth is an actual hierarchy node, with its prescribed frame. -/
theorem left_mem {T : Tiling S} (H : CoherentHierarchy S T)
    (hg : g.birth ∈ H.nodes g.height) : g.leftNode ∈ H.nodes (g.height - 1) :=
  hierarchy_descendant_mem H g.height (g.height - 1) g.birth g.leftNode hg
    g.sides_descendant.1

/-- R1/R5/R12, V4 §3.0, 3.4, 3.1: the right owner of an actual hierarchy
birth is an actual hierarchy node in the same subdivision. -/
theorem right_mem {T : Tiling S} (H : CoherentHierarchy S T)
    (hg : g.birth ∈ H.nodes g.height) : g.rightNode ∈ H.nodes (g.height - 1) :=
  hierarchy_descendant_mem H g.height (g.height - 1) g.birth g.rightNode hg
    g.sides_descendant.2

/-- R1/R5, V4 §3.0, 3.4: primitive attachment, initially from the canonical left side.
Lemma 3.4 establishes equality with the right-side value, including the full packet. -/
def packet {Y : MarkedTiling (systemM S P C)}
    (h : BoundaryPackets Y (g.height - 1) g.leftNode) : Option (Packet P) :=
  attachedPacket h g.incidence.val.leftFacet

end BornFacet

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)

/-- R1, V4 §3.0 (I1): root states are honest, have the geometric prototype,
and have residue n modulo the fixed positive L. -/
def I1 : Prop :=
  ∀ (B : Block Y n) (hB : B ∈ D.geometry.blocks),
    D.blockState B hB ∈ honestStates S P ∧
      (D.blockState B hB).ty = B.node.ty ∧
      (D.blockState B hB).residue.val = n % P.L

/-- R1, V4 §3.0 (I2): deterministic child equations on all inner nodes,
and equality with the actual leaf pre-pattern state at height zero. -/
def I2 : Prop :=
  (∀ (m : ℕ) (N : FramedNode S) (hN : N ∈ D.geometry.nodes (m + 1))
    (i : S.I N.ty),
    D.stateAt m (N.child m i) (D.geometry.child_mem m N hN i) =
      childMap P (D.stateAt (m + 1) N hN) ⟨N.ty, i⟩) ∧
  ∀ (N : FramedNode S) (hN : N ∈ D.geometry.nodes 0)
    (t : PlacedMarkedTile (systemM S P C)), t ∈ Y.tiles → tileNode t = N →
      D.stateAt 0 N hN = (compilerLeaf C t).prePattern.state

/-- R1, V4 §3.0 (I4): every principal primitive facet born inside a node
at depth at most k-1 has that node's slot PRESENT and equal to its assigned state.
The packet is the real constant leaf readout from the left child, whose existence
is included. R5 identifies it with the right readout. Persistent faults are excluded
by the positive finite birth, exactly as in Remark 3.14. -/
def I4 : Prop :=
  ∀ (m : ℕ) (N : FramedNode S) (hN : N ∈ D.geometry.nodes m) (g : BornFacet P),
    g.birth.IsDescendant g.height N m →
    ∀ hdepth : m - g.height < P.k, P.InPrincipal N m g.carrier →
      ∃ h : BoundaryPackets Y (g.height - 1) g.leftNode, ∃ q : Packet P,
        g.packet h = some q ∧
          decode q ⟨m - g.height, hdepth⟩ = some (D.stateAt m N hN)

/-- R1, V4 §3.0 (I5): one constant packet on every side of every node facet,
and equality on meeting facets whose tracks are E-related in the node's state.
NULL participates in both assertions. The finite table is read by `stateEAt`
to avoid transporting facet names along a later proved state-type equality. -/
def I5 : Prop :=
  ∀ (m : ℕ) (N : FramedNode S) (hN : N ∈ D.geometry.nodes m),
    ∃ h : BoundaryPackets Y m N, ∀ F F' : FacetName S N.ty,
      stateEAt (D.stateAt m N hN) F.val F'.val →
      (N.cell m F.val ∩ N.cell m F'.val).Nonempty →
        attachedPacket h F = attachedPacket h F'

end Parser

/-- R1, V4 §3.0: precisely the four named invariant propositions.
I3 is contained in I2 because facet records are state fields, as the paper explains. -/
structure Inv {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n) : Prop where
  /-- R1, V4 §3.0 (I1): root type, honesty and height residue. -/
  I1 : Parser.I1 D
  /-- R1, V4 §3.0 (I2): all child equations and actual ground pre-pattern states. -/
  I2 : Parser.I2 D
  /-- R1, V4 §3.0 (I4): principal PRESENT slots at all inner nodes. -/
  I4 : Parser.I4 D
  /-- R1, V4 §3.0 (I5): boundary constancy and equality for meeting E-related facets. -/
  I5 : Parser.I5 D

namespace Inv

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ} {D : DecodedLevel Y n} (h : Inv D)

include h

/-- R1, V4 §3.0 (I5): the invariant supplies the constancy proof for attachment. -/
theorem boundaryPackets (m : ℕ) (N : FramedNode S) (hN : N ∈ D.geometry.nodes m) :
    Parser.BoundaryPackets Y m N := (h.I5 m N hN).choose


private lemma node_type_residue_step2_predecessor_exists (m : ℕ) (N : FramedNode S)
    (hN : N ∈ D.geometry.nodes m) (hm : m < n) :
    ∃ (M : FramedNode S) (hM : M ∈ D.geometry.nodes (m + 1)) (i : S.I M.ty), N = M.child m i := by
  have predecessor : ∀ (X R : FramedNode S) (a b : ℕ),
      a < b → X.IsDescendant a R b →
      ∃ M : FramedNode S, M.IsDescendant (a + 1) R b ∧
        ∃ i : S.I M.ty, X = M.child a i := by
    intro X R a b hab hXR
    obtain ⟨r, rfl, w, rfl⟩ := hXR
    induction r generalizing R with
    | zero => omega
    | succ r ih =>
      cases r with
      | zero =>
        refine ⟨R, Parser.descendant_refl R (a + 1), w.1, ?_⟩
        rfl
      | succ r =>
        obtain ⟨M, hM, i, hi⟩ :=
          ih (R.child (a + (r + 1)) w.1) (by omega) w.2
        exact ⟨M, Parser.descendant_trans M _ R (a + 1)
          (a + (r + 1)) (a + (r + 1 + 1)) hM
          (Parser.child_descendant R _ w.1), i, hi⟩
  obtain ⟨B, hB, hNB⟩ := hN
  change N.IsDescendant m B.node n at hNB
  obtain ⟨M, hM, i, hi⟩ := predecessor N B.node m n hm hNB
  exact ⟨M, ⟨B, hB, hM⟩, i, hi⟩

private lemma node_type_residue_step1_childMap_residue (m : ℕ) (M : FramedNode S)
    (i : S.I M.ty) (s : State P) (hs : s ∈ honestStates S P)
    (hty : s.ty = M.ty) (hres : s.residue.val = (m + 1) % P.L) :
    (childMap P s ⟨M.ty, i⟩).ty = (M.child m i).ty ∧
      (childMap P s ⟨M.ty, i⟩).residue.val = m % P.L := by
  refine ⟨(childMap_admissible P s hs ⟨M.ty, i⟩ hty.symm).2, ?_⟩
  obtain ⟨U, q, rfl⟩ := hs
  have hmod : q.1 % P.L = (m + 1) % P.L := hres
  have hshift : (q.1 - (m + 1)) % P.L = (m + 1 - q.1) % P.L := by
    rcases le_total q.1 (m + 1) with hle | hle
    · rw [Nat.sub_eq_zero_of_le hle, Nat.zero_mod]
      exact (Nat.dvd_iff_mod_eq_zero.mp ((Nat.modEq_iff_dvd' hle).mp hmod)).symm
    · rw [Nat.sub_eq_zero_of_le hle, Nat.zero_mod]
      exact Nat.dvd_iff_mod_eq_zero.mp ((Nat.modEq_iff_dvd' hle).mp hmod.symm)
  obtain ⟨V, e, N', he⟩ := exactScaleTransfer U q.1 q.2.val q.2.property (m + 1)
    (AffineIsometryEquiv.refl ℝ (E d))
  have hs' : stateOf U P q = stateOf V P ⟨m + 1, N'⟩ := by
    have hst := state_scaleTransfer P e hshift ⟨q, Nat.sub_le _ _⟩
    rw [he] at hst
    exact hst
  rw [hs'] at hty ⊢
  have key : ∀ r : S.Role, r.1 = N'.val.ty →
      (childMap P (stateOf V P ⟨m + 1, N'⟩) r).residue.val = m % P.L := by
    rintro ⟨A, j⟩ hA
    dsimp only at hA
    subst hA
    rw [← childMap_spec V P ⟨m + 1, N'⟩ (Nat.le_add_left 1 m) j]
    show (m + 1 - 1) % P.L = m % P.L
    rw [Nat.add_sub_cancel]
  exact key ⟨M.ty, i⟩ hty.symm

/-- R1, V4 §3.0 (I1)--(I2): type and residue propagate to every inner node. -/
theorem node_type_residue (m : ℕ) (N : FramedNode S) (hN : N ∈ D.geometry.nodes m) :
    (D.stateAt m N hN).ty = N.ty ∧
      (D.stateAt m N hN).residue.val = m % P.L := by
  have key : ∀ (r m : ℕ) (N : FramedNode S) (hN : N ∈ D.geometry.nodes m), m + r = n →
      (D.stateAt m N hN).ty = N.ty ∧ (D.stateAt m N hN).residue.val = m % P.L := by
    intro r
    induction r with
    | zero =>
      intro m N hN hmn
      obtain rfl : m = n := by omega
      have hN' : N ∈ D.geometry.roots := D.geometry.nodes_top ▸ hN
      obtain ⟨B, hB, rfl⟩ := hN'
      obtain ⟨_, h1, h2⟩ := h.I1 B hB
      exact ⟨h1, h2⟩
    | succ r ih =>
      intro m N hN hmn
      obtain ⟨M, hM, i, rfl⟩ := node_type_residue_step2_predecessor_exists (h := h) m N hN (by omega)
      obtain ⟨hty, hres⟩ := ih (m + 1) M hM (by omega)
      have e := h.I2.1 m M hM i
      obtain ⟨hty', hres'⟩ := node_type_residue_step1_childMap_residue (h := h) m M i
        (D.stateAt (m + 1) M hM) (D.state_honest _ ⟨M, hM⟩) hty hres
      rw [e]
      exact ⟨hty', hres'⟩
  exact key (n - m) m N hN (by have := D.geometry.nodes_height m N hN; omega)


end Inv

namespace Parser

variable {Y : MarkedTiling (systemM S P C)}

/-- R2, V4 3.2: the base family and every inner state are exactly the actual
K-certificates and their jointly honest S-tables from Theorem 2.17(a). -/
def CertificateBase (D : DecodedLevel Y P.K) : Prop :=
  D.geometry.roots = Set.range (fun B : KBlock Y => B.node) ∧
    ∀ (B : KBlock Y) (a : ℕ) (ha : a ≤ P.K) (w : S.RoleWord B.certificate.val.ty a),
      ∃ hN : B.innerNode a ha w ∈ D.geometry.nodes (P.K - a),
        D.stateAt (P.K - a) (B.innerNode a ha w) hN = B.table a ha w

end Parser

/-- Step 0 of the V4 proof of `base_level_step1_decoded` (V4 2.17(a)): "each is a placed
σ^K A whose standard subdivision consists of actual tiles"; a whole certificate is an
actual height-K parser block. -/
private lemma base_level_step1_decoded_step0_isBlock {Y : MarkedTiling (systemM S P C)}
    (B : KBlock Y) : IsBlock Y P.K B.node := by
  intro w
  refine ⟨B.leaf w, B.leaf_mem w, ?_⟩
  apply FramedNode.ext
  · change (compilerLeaf C (B.leaf w)).prototype = _
    rw [(B.leaf_data w).1]
    rfl
  · exact (B.leaf_data w).2

/-- Step 0 of the V4 proof of `base_level_step1_decoded` (V4 2.17(a)): a whole certificate
regarded as an ordinary parser block. -/
private def base_level_step1_decoded_step0_toBlock {Y : MarkedTiling (systemM S P C)}
    (B : KBlock Y) : Block Y P.K :=
  ⟨B.node, base_level_step1_decoded_step0_isBlock B⟩

/-- Step 1 of the V4 proof of `base_level_step1_decoded` (V4 3.2, 2.17(a)): "each is a
placed σ^K A whose standard subdivision consists of actual tiles". For a level whose
blocks are the K-blocks, the nodes at height m are exactly the inner nodes of the
certificates at depth K - m. -/
private lemma base_level_step1_decoded_step1_mem_iff {Y : MarkedTiling (systemM S P C)}
    (G : GeometricLevel Y P.K) (hG : G.blocks = Set.range base_level_step1_decoded_step0_toBlock)
    (m : ℕ) (N : FramedNode S) :
    N ∈ G.nodes m ↔ ∃ (B : KBlock Y) (a : ℕ) (ha : a ≤ P.K)
      (w : S.RoleWord B.certificate.val.ty a), P.K - a = m ∧ B.innerNode a ha w = N := by
  constructor
  · rintro ⟨Bk, hBk, r, hr, w, hw⟩
    rw [hG] at hBk
    obtain ⟨B, rfl⟩ := hBk
    have hm : P.K - r = m := by omega
    refine ⟨B, r, by omega, w, hm, ?_⟩
    rw [hw]
    change (S.descendantNode B.certificate.val.ty (P.K - r) r w).move B.frame = _
    rw [hm]
    rfl
  · rintro ⟨B, a, ha, w, hm, rfl⟩
    refine ⟨(base_level_step1_decoded_step0_toBlock B), hG ▸ ⟨B, rfl⟩, a, by omega, w, ?_⟩
    change (S.descendantNode B.certificate.val.ty (P.K - a) a w).move B.frame = _
    rw [hm]
    rfl

/-- Step 2 of the V4 proof of `base_level_step1_decoded` (V4 §1.0, H3): a prescribed child
lies in its closed parent (the substitution cover `σ(A) = ⋃ children`). -/
private lemma base_level_step1_decoded_step2_child_subset (N : FramedNode S) (n : ℕ)
    (i : S.I N.ty) : (N.child n i).carrier n ⊆ N.carrier (n + 1) := by
  have hplace (x : E d) : S.placeChild n i ((S.σ ^ n) x) =
      (S.σ ^ n) ((S.child N.ty i).frame x) := by
    change linearConj S.σ (n : ℤ) (S.child N.ty i).rotation.toLinearEquiv
        ((S.σ ^ n) x) + (S.σ ^ n) (S.child N.ty i).offset =
      (S.σ ^ n) ((S.child N.ty i).rotation x + (S.child N.ty i).offset)
    simp [linearConj, zpow_neg, LinearEquiv.mul_apply]
  rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hmem : (S.child N.ty i).frame x ∈ S.σ '' (S.proto N.ty).carrier := by
    rw [S.children_cover]
    exact mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩
  obtain ⟨y, hy, he⟩ := hmem
  refine ⟨(S.σ ^ (n + 1)) y, ⟨y, hy, rfl⟩, ?_⟩
  change N.frame ((S.σ ^ (n + 1)) y) = N.frame (S.placeChild n i ((S.σ ^ n) x))
  rw [hplace, ← he, pow_succ]
  rfl

/-- Step 2 of the V4 proof of `base_level_step1_decoded` (V4 §1.0, H3): a descendant node
lies in the closed carrier of its root. -/
private lemma base_level_step1_decoded_step2_descendant_subset (D N : FramedNode S)
    (m n : ℕ) (h : D.IsDescendant m N n) : D.carrier m ⊆ N.carrier n := by
  obtain ⟨r, rfl, w, rfl⟩ := h
  induction r generalizing N with
  | zero => simp [SubstSystem.descendantNode, FramedNode.move]
  | succ r ih =>
    have he : (S.descendantNode N.ty m (r + 1) w).move N.frame =
        (S.descendantNode (N.child (m + r) w.1).ty m r w.2).move
          (N.child (m + r) w.1).frame := rfl
    rw [he]
    exact (ih (N.child (m + r) w.1) w.2).trans
      (base_level_step1_decoded_step2_child_subset N (m + r) w.1)

/-- Step 2 of the V4 proof of `base_level_step1_decoded` (V4 2.17(a)): "the K-blocks of Y
(one per tile, with repetitions identified) have pairwise disjoint interiors". Two
K-blocks sharing an inner node at the same height coincide. -/
private lemma base_level_step1_decoded_step2_block_unique {Y : MarkedTiling (systemM S P C)}
    (B B' : KBlock Y) (a a' : ℕ) (ha : a ≤ P.K) (ha' : a' ≤ P.K)
    (w : S.RoleWord B.certificate.val.ty a) (w' : S.RoleWord B'.certificate.val.ty a')
    (hm : P.K - a = P.K - a') (h : B.innerNode a ha w = B'.innerNode a' ha' w') :
    B = B' := by
  have hd : (B.innerNode a ha w).IsDescendant (P.K - a) (base_level_step1_decoded_step0_toBlock B).node P.K :=
    ⟨a, by omega, w, rfl⟩
  have hd' : (B.innerNode a ha w).IsDescendant (P.K - a) B'.node P.K := by
    rw [h, hm]
    exact ⟨a', by omega, w', rfl⟩
  obtain ⟨x, hx⟩ := ((base_level_step1_decoded_step0_toBlock B).innerBlock (P.K - a) _ hd).carrier_regular.2.2
  apply B.eq_of_interior_meet B'
  refine ⟨x, interior_mono ?_ hx, interior_mono ?_ hx⟩
  · exact base_level_step1_decoded_step2_descendant_subset _ _ _ _ hd
  · exact base_level_step1_decoded_step2_descendant_subset _ _ _ _ hd'

/-- Step 3 of the V4 proof of `base_level_step1_decoded` (V4 §1.0, H3): a placed child
carrier is the image of the placed child prototype under the parent's prototype frame. -/
private lemma base_level_step1_decoded_step3_child_carrier (N : FramedNode S) (n : ℕ)
    (i : S.I N.ty) : (N.child n i).carrier n = N.prototypeFrame n ''
      placedSet (S.child N.ty i).frame (S.proto (S.child N.ty i).ty).carrier := by
  have hi (x : E d) : S.placeChild n i ((S.σ ^ n) x) =
      (S.σ ^ n) ((S.child N.ty i).frame x) := by
    rw [S.placeChild_apply]
    simp [linearConj, Child.frame, rigidMotion, zpow_neg, LinearEquiv.mul_apply,
      ← map_add]
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    change N.frame ((S.σ ^ n) ((S.child N.ty i).frame x)) =
      N.frame (S.placeChild n i ((S.σ ^ n) x))
    rw [hi]
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    change N.frame (S.placeChild n i ((S.σ ^ n) x)) =
      N.frame ((S.σ ^ n) ((S.child N.ty i).frame x))
    rw [hi]

/-- Step 3 of the V4 proof of `base_level_step1_decoded` (V4 §1.0): every framed node
has a carrier with nonempty interior (nonempty prototype interiors). -/
private lemma base_level_step1_decoded_step3_interior_nonempty (D : FramedNode S) (h : ℕ) :
    (interior (D.carrier h)).Nonempty := by
  have hc : D.carrier h = D.prototypeFrame h '' (S.proto D.ty).carrier := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hi : interior (D.prototypeFrame h '' (S.proto D.ty).carrier) =
      D.prototypeFrame h '' interior (S.proto D.ty).carrier :=
    ((D.prototypeFrame h).toHomeomorphOfFiniteDimensional.image_interior _).symm
  rw [hc, hi]
  exact (S.proto D.ty).interior_nonempty.image _

/-- Step 3 of the V4 proof of `base_level_step1_decoded` (V4 §1.0, H3): distinct
children of a framed node have disjoint interiors. -/
private lemma base_level_step1_decoded_step3_children_disjoint (N : FramedNode S) (n : ℕ)
    (i j : S.I N.ty) (hij : i ≠ j) :
    Disjoint (interior ((N.child n i).carrier n)) (interior ((N.child n j).carrier n)) := by
  have hi (k : S.I N.ty) : interior ((N.child n k).carrier n) = N.prototypeFrame n ''
      interior (placedSet (S.child N.ty k).frame (S.proto (S.child N.ty k).ty).carrier) := by
    rw [base_level_step1_decoded_step3_child_carrier]
    exact ((N.prototypeFrame n).toHomeomorphOfFiniteDimensional.image_interior _).symm
  rw [hi, hi]
  exact (Set.disjoint_image_iff (N.prototypeFrame n).injective).mpr
    (S.children_disjoint N.ty hij)

/-- Step 3 of the V4 proof of `base_level_step1_decoded` (V4 §1.0, H3--H4): distinct role
words of one depth name distinct framed descendants of a node. -/
private lemma base_level_step1_decoded_step3_descendant_injective (h a : ℕ) :
    ∀ (N : FramedNode S) (w w' : S.RoleWord N.ty a),
      (S.descendantNode N.ty h a w).move N.frame =
        (S.descendantNode N.ty h a w').move N.frame → w = w' := by
  induction a with
  | zero =>
    intro N w w' _
    exact Subsingleton.elim (α := Unit) w w'
  | succ a ih =>
    intro N w w' hw
    obtain ⟨i, u⟩ := w
    obtain ⟨j, u'⟩ := w'
    have he : ∀ (k : S.I N.ty) (v : S.RoleWord (S.child N.ty k).ty a),
        (S.descendantNode N.ty h (a + 1) ⟨k, v⟩).move N.frame =
          (S.descendantNode (N.child (h + a) k).ty h a v).move
            (N.child (h + a) k).frame := fun _ _ => rfl
    rw [he, he] at hw
    by_cases hij : i = j
    · subst hij
      rw [ih (N.child (h + a) i) u u' hw]
    · exfalso
      have h1 := base_level_step1_decoded_step2_descendant_subset _
        (N.child (h + a) i) h (h + a) ⟨a, rfl, u, rfl⟩
      have h2 := base_level_step1_decoded_step2_descendant_subset _
        (N.child (h + a) j) h (h + a) ⟨a, rfl, u', hw⟩
      obtain ⟨x, hx⟩ := base_level_step1_decoded_step3_interior_nonempty
        ((S.descendantNode (N.child (h + a) i).ty h a u).move (N.child (h + a) i).frame) h
      exact Set.disjoint_left.mp
        (base_level_step1_decoded_step3_children_disjoint N (h + a) i j hij)
        (interior_mono h1 hx) (interior_mono h2 hx)

/-- Step 3 of the V4 proof of `base_level_step1_decoded` (V4 §1.0, H3--H4): in the standard
subdivision of one K-block, distinct role words of the same depth name distinct
framed inner nodes (children of a node have disjoint interiors). -/
private lemma base_level_step1_decoded_step3_word_unique {Y : MarkedTiling (systemM S P C)}
    (B : KBlock Y) (a : ℕ) (ha : a ≤ P.K) (w w' : S.RoleWord B.certificate.val.ty a)
    (h : B.innerNode a ha w = B.innerNode a ha w') : w = w' :=
  base_level_step1_decoded_step3_descendant_injective (P.K - a) a B.node w w' h

/-- Step 4 of the V4 proof of `base_level_step1_decoded` (V4 3.2): the honest S-table
state of an inner node does not depend on the certificate presenting it. -/
private lemma base_level_step1_decoded_step4_table_eq {Y : MarkedTiling (systemM S P C)}
    (B B' : KBlock Y) (a a' : ℕ) (ha : a ≤ P.K) (ha' : a' ≤ P.K)
    (w : S.RoleWord B.certificate.val.ty a) (w' : S.RoleWord B'.certificate.val.ty a')
    (hm : P.K - a = P.K - a') (h : B.innerNode a ha w = B'.innerNode a' ha' w') :
    B.table a ha w = B'.table a' ha' w' := by
  have hB := base_level_step1_decoded_step2_block_unique B B' a a' ha ha' w w' hm h
  subst hB
  have haa : a = a' := by omega
  subst haa
  have hw := base_level_step1_decoded_step3_word_unique B a ha w w' h
  subst hw
  rfl

/-- Step 1 of the V4 proof of `base_level` (V4 3.2): The K-blocks of Theorem 2.17(a), with the states given by the honest S-tables of their certificates, form a decoded level K. -/
private lemma base_level_step1_decoded (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    ∃ D : DecodedLevel Y P.K, Parser.CertificateBase D := by
  obtain ⟨-, hdisj, hcov, -⟩ := compiler_certificates C Y hY
  let G : GeometricLevel Y P.K :=
    { blocks := Set.range base_level_step1_decoded_step0_toBlock
      disjoint := by
        rintro _ ⟨B₁, rfl⟩ _ ⟨B₂, rfl⟩ hne
        exact hdisj (fun h => hne (h ▸ rfl))
      cover := fun x => by
        obtain ⟨B, hB⟩ := hcov x
        exact ⟨(base_level_step1_decoded_step0_toBlock B), ⟨B, rfl⟩, hB⟩ }
  have hG : G.blocks = Set.range base_level_step1_decoded_step0_toBlock := rfl
  have hex : ∀ (m : ℕ) (N : {N // N ∈ G.nodes m}), ∃ s : State P,
      ∃ (B : KBlock Y) (a : ℕ) (ha : a ≤ P.K) (w : S.RoleWord B.certificate.val.ty a),
        P.K - a = m ∧ B.innerNode a ha w = N.1 ∧ s = B.table a ha w := by
    intro m N
    obtain ⟨B, a, ha, w, hm, hN⟩ :=
      (base_level_step1_decoded_step1_mem_iff G hG m N.1).1 N.2
    exact ⟨_, B, a, ha, w, hm, hN, rfl⟩
  refine ⟨⟨G, fun m N => (hex m N).choose, fun m N => ?_⟩, ?_, ?_⟩
  · obtain ⟨B, a, ha, w, -, -, hs⟩ := (hex m N).choose_spec
    show (hex m N).choose ∈ honestStates S P
    rw [hs]
    exact B.table_mem a ha w
  · ext N
    constructor
    · rintro ⟨_, ⟨B, rfl⟩, rfl⟩
      exact ⟨B, rfl⟩
    · rintro ⟨B, rfl⟩
      exact ⟨(base_level_step1_decoded_step0_toBlock B), ⟨B, rfl⟩, rfl⟩
  · intro B a ha w
    have hN : B.innerNode a ha w ∈ G.nodes (P.K - a) :=
      (base_level_step1_decoded_step1_mem_iff G hG _ _).2 ⟨B, a, ha, w, rfl, rfl⟩
    refine ⟨hN, ?_⟩
    obtain ⟨B', a', ha', w', hm, hn, hs⟩ := (hex (P.K - a) ⟨_, hN⟩).choose_spec
    change (hex (P.K - a) ⟨_, hN⟩).choose = _
    rw [hs]
    exact base_level_step1_decoded_step4_table_eq B' B a' a ha' ha w' w hm hn

/-- Step 2 of the V4 proof of `base_level` (V4 3.2): (I1): the table's state of the root has the block's type, and its residue is K mod L because the certificate is the S-table of an honest node of height exactly K. -/
private lemma base_level_step2_I1 (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (D : DecodedLevel Y P.K) (hbase : Parser.CertificateBase D) : Parser.I1 D := by
  intro B hB
  have hroot : B.node ∈ D.geometry.roots := ⟨B, hB, rfl⟩
  rw [hbase.1] at hroot
  obtain ⟨B', hB'⟩ := hroot
  obtain ⟨hN, hs⟩ := hbase.2 B' 0 (Nat.zero_le _) ()
  have hinner : B'.innerNode 0 (Nat.zero_le _) () = B'.node := by
    rfl
  have hstate : D.blockState B hB = B'.table 0 (Nat.zero_le _) () := by
    simpa only [Nat.sub_zero, hinner, hB', DecodedLevel.blockState] using hs
  refine ⟨D.state_honest P.K ⟨B.node, D.geometry.root_mem B hB⟩, ?_, ?_⟩
  · rw [hstate]
    calc
      (B'.table 0 (Nat.zero_le _) ()).ty = B'.node.ty :=
        B'.certificate.val.table_type 0 (Nat.zero_le _) ()
      _ = B.node.ty := congrArg FramedNode.ty hB'
  · rw [hstate]
    have hres : ∀ (c : Certificate P), c ∈ honestCerts S P →
        (c.table 0 (Nat.zero_le _) ()).residue.val = P.K % P.L := by
      rintro c ⟨U, N, hN, rfl⟩
      rfl
    exact hres B'.certificate.val B'.certificate.property

/-- Step 1 of the V4 proof of `base_level_step3_I2` (V4 3.2): "the K-blocks ...
form a decoded level K". Every inner node of a level with the forced roots has
an exact role-word address in a certificate. -/
private lemma base_level_step3_I2_step1_certificate_node
    {Y : MarkedTiling (systemM S P C)}
    (G : GeometricLevel Y P.K)
    (hroots : G.roots = Set.range (fun B : KBlock Y => B.node))
    (m : ℕ) (N : FramedNode S) (hN : N ∈ G.nodes m) :
    ∃ (B : KBlock Y) (a : ℕ) (ha : a ≤ P.K)
      (w : S.RoleWord B.certificate.val.ty a),
      P.K - a = m ∧ B.innerNode a ha w = N := by
  obtain ⟨Bk, hBk, hdesc⟩ := hN
  have hroot : Bk.node ∈ G.roots :=
    G.nodes_top ▸ G.root_mem Bk hBk
  rw [hroots] at hroot
  obtain ⟨B, hB⟩ := hroot
  change N.IsDescendant m Bk.node P.K at hdesc
  rw [← hB] at hdesc
  obtain ⟨a, ha, w, hw⟩ := hdesc
  have hm : P.K - a = m := by omega
  refine ⟨B, a, by omega, w, hm, ?_⟩
  rw [hw]
  change (S.descendantNode B.certificate.val.ty (P.K - a) a w).move B.frame = _
  rw [hm]
  rfl

/-- Step 2 of the V4 proof of `base_level_step3_I2` (V4 3.2, 2.3): "the table
is the S-table of an honest node ... so Proposition 2.3 gives the child equations".
The honest source identifies both the child's exact address and its table state. -/
private lemma base_level_step3_I2_step2_certificate_child
    (D : Certificate P) (hD : D ∈ honestCerts S P)
    (a m : ℕ) (ham : m + 1 + a = P.K) (w : S.RoleWord D.ty a)
    (i : S.I (S.descendantNode D.ty (m + 1) a w).ty) :
    ∃ w' : S.RoleWord D.ty (a + 1),
      S.descendantNode D.ty m (a + 1) w' =
        (S.descendantNode D.ty (m + 1) a w).child m i ∧
      D.table (a + 1) (by omega) w' =
        childMap P (D.table a (by omega) w)
          ⟨(S.descendantNode D.ty (m + 1) a w).ty, i⟩ := by
  obtain ⟨U, R, hR, rfl⟩ := hD
  let Q := (S.descendantNode R.ty (m + 1) a w).move R.frame
  have hQ : Q.IsDescendant (m + 1) R P.K := ⟨a, ham.symm, w, rfl⟩
  have hchild := Parser.descendant_trans (Q.child m i) Q R m (m + 1) P.K
    (Parser.child_descendant Q m i) hQ
  obtain ⟨r, hr, v, hv⟩ := hchild
  have hr' : r = a + 1 := by omega
  subst r
  have hrel : S.descendantNode R.ty m (a + 1) v =
      (S.descendantNode R.ty (m + 1) a w).child m i := by
    apply FramedNode.ext
    · exact (congrArg FramedNode.ty hv).symm
    · apply AffineIsometryEquiv.ext
      intro x
      apply R.frame.injective
      exact congrArg (fun N : FramedNode S => N.frame x) hv.symm
  refine ⟨v, hrel, ?_⟩
  let q : U.Node := ⟨m + 1, ⟨Q,
    Parser.hierarchy_descendant_mem U.hierarchy P.K (m + 1) R Q hR hQ⟩⟩
  have hparent : U.descendant ⟨P.K, ⟨R, hR⟩⟩ a (by change a ≤ P.K; omega) w = q := by
    apply Sigma.subtype_ext
    · change P.K - a = m + 1
      omega
    · change (S.descendantNode R.ty (P.K - a) a w).move R.frame = Q
      rw [show P.K - a = m + 1 by omega]
  have hstate := childMap_spec U P q (by change 1 ≤ m + 1; omega) i
  have heq : U.descendant ⟨P.K, ⟨R, hR⟩⟩ (a + 1) (by change a + 1 ≤ P.K; omega) v =
      U.childNode q (by change 1 ≤ m + 1; omega) i := by
    apply Sigma.subtype_ext
    · change P.K - (a + 1) = (m + 1) - 1
      omega
    · change (S.descendantNode R.ty (P.K - (a + 1)) (a + 1) v).move R.frame =
        Q.child ((m + 1) - 1) i
      rw [show P.K - (a + 1) = m by omega, show (m + 1) - 1 = m by omega]
      exact hv.symm
  change stateOf U P (U.descendant ⟨P.K, ⟨R, hR⟩⟩ (a + 1) _ v) =
    childMap P (stateOf U P (U.descendant ⟨P.K, ⟨R, hR⟩⟩ a _ w)) ⟨_, i⟩
  rw [heq, hparent]
  exact hstate

/-- Step 3 of the V4 proof of `base_level_step3_I2` (V4 3.2): "the leaf
pre-patterns are those of the honest leaves". Disjoint tile interiors identify
an actual tile with the prescribed certificate leaf at its framed node. -/
private lemma base_level_step3_I2_step3_tile_unique
    {Y : MarkedTiling (systemM S P C)}
    (t u : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles) (hu : u ∈ Y.tiles)
    (h : tileNode t = tileNode u) : t = u := by
  have hc (v : PlacedMarkedTile (systemM S P C)) :
      v.carrier = (tileNode v).carrier 0 := by
    rw [compilerFrame_carrier C v]
    simp [tileNode, FramedNode.carrier, SubstSystem.supertile, placedSet]
  have hcar : t.carrier = u.carrier := by rw [hc t, hc u, h]
  have hn : (interior t.carrier).Nonempty := by
    rw [compilerFrame_carrier C t]
    change (interior ((compilerFrame C t).toHomeomorph ''
      (S.proto (compilerLeaf C t).prototype).carrier)).Nonempty
    rw [← (compilerFrame C t).toHomeomorph.image_interior]
    exact (S.proto _).interior_nonempty.image _
  obtain ⟨x, hx⟩ := hn
  by_contra hne
  have hxu : x ∈ interior u.carrier := by
    rw [← hcar]
    exact hx
  exact Set.disjoint_left.mp (Y.disjoint ht hu hne) hx hxu

/-- Step 3 of the V4 proof of `base_level` (V4 3.2): (I2): the table is the S-table of an honest node, so Proposition 2.3 gives the child equations, and the leaf pre-patterns are those of the honest leaves. -/
private lemma base_level_step3_I2 (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (D : DecodedLevel Y P.K) (hbase : Parser.CertificateBase D) : Parser.I2 D := by
  have state_eq (B : KBlock Y) (a : ℕ) (ha : a ≤ P.K)
      (w : S.RoleWord B.certificate.val.ty a)
      (m : ℕ) (N : FramedNode S) (hN : N ∈ D.geometry.nodes m)
      (hm : P.K - a = m) (hnode : B.innerNode a ha w = N) :
      D.stateAt m N hN = B.table a ha w := by
    obtain ⟨hcert, heq⟩ := hbase.2 B a ha w
    subst m
    subst N
    exact heq
  constructor
  · intro m N hN i
    obtain ⟨B, a, ha, w, hm, hnode⟩ :=
      base_level_step3_I2_step1_certificate_node D.geometry hbase.1 (m + 1) N hN
    have hparent := state_eq B a ha w (m + 1) N hN hm hnode
    have ham : m + 1 + a = P.K := by omega
    have hn : (S.descendantNode B.certificate.val.ty (m + 1) a w).move B.frame = N := by
      simpa only [KBlock.innerNode, hm] using hnode
    cases hn
    obtain ⟨w', hw', htable⟩ := base_level_step3_I2_step2_certificate_child B.certificate.val
      B.certificate.property a m ham w i
    have hchild : B.innerNode (a + 1) (by omega) w' =
        ((S.descendantNode B.certificate.val.ty (m + 1) a w).move B.frame).child m i := by
      have he := congrArg (fun M : FramedNode S => M.move B.frame) hw'
      change (S.descendantNode B.certificate.val.ty (P.K - (a + 1)) (a + 1) w').move
        B.frame = _
      rw [show P.K - (a + 1) = m by omega]
      simpa only [FramedNode.move, FramedNode.child, AffineIsometryEquiv.trans_assoc] using he
    rw [state_eq B (a + 1) (by omega) w' m _
      (D.geometry.child_mem m _ hN i) (by omega) hchild, hparent]
    exact htable
  · intro N hN t ht htN
    obtain ⟨B, a, ha, w, hm, hnode⟩ :=
      base_level_step3_I2_step1_certificate_node D.geometry hbase.1 0 N hN
    have haK : a = P.K := by omega
    subst a
    have hleaf : tileNode (B.leaf w) = B.innerNode P.K le_rfl w := by
      apply FramedNode.ext
      · change (compilerLeaf C (B.leaf w)).prototype = _
        rw [(B.leaf_data w).1]
        simp only [KBlock.innerNode, Nat.sub_self]
        rfl
      · change compilerFrame C (B.leaf w) = _
        rw [(B.leaf_data w).2]
        simp only [KBlock.innerNode, Nat.sub_self]
        rfl
    have htleaf : t = B.leaf w :=
      base_level_step3_I2_step3_tile_unique t (B.leaf w) ht (B.leaf_mem w)
        (htN.trans (hleaf.trans hnode).symm)
    rw [state_eq B P.K le_rfl w 0 N hN (Nat.sub_self _) hnode, htleaf]
    exact (B.leaf_state w).symm

open private leafTypeOf_move_step4_cert from Enforce.Compiler.System in
/-- Step 1 of the V4 proof of `base_level_step4_I4` (V4 3.2, 2.7):
"the certificate is the S-table of an honest node". Move its honest witness
to the actual certificate frame; its joint certificate is unchanged. -/
private lemma base_level_step4_I4_step1_source
    {Y : MarkedTiling (systemM S P C)} (B : KBlock Y) :
    ∃ (U : HonestSource S) (hB : B.node ∈ U.hierarchy.nodes P.K),
      certOf U P B.node hB = B.certificate.val := by
  obtain ⟨U, N, hN, hcert⟩ := B.honest_table
  let γ := N.frame.symm.trans B.frame
  have hmove : N.move γ = B.node := by
    apply FramedNode.ext
    · exact congrArg Certificate.ty hcert
    · apply AffineIsometryEquiv.ext
      intro x
      exact congrArg B.frame (N.frame.symm_apply_apply x)
  have hB : B.node ∈ (U.move γ).hierarchy.nodes P.K := by
    rw [(U.move_spec γ).nodes]
    exact ⟨N, hN, hmove⟩
  exact ⟨U.move γ, hB,
    (leafTypeOf_move_step4_cert U γ N hN B.node hB hmove.symm).trans hcert⟩

/-- Step 2 of the V4 proof of `base_level_step4_I4` (V4 3.2, 2.5):
"the slot of N" is the ancestor at its exact birth-to-node distance.
An exact standard descendant address in a coherent hierarchy inverts ancestry. -/
private lemma base_level_step4_I4_step2_ancestor
    {T : Tiling S} (H : CoherentHierarchy S T) (m r : ℕ)
    (N : FramedNode S) (hN : N ∈ H.nodes (m + r))
    (w : S.RoleWord N.ty r)
    (hc : (S.descendantNode N.ty m r w).move N.frame ∈ H.nodes m) :
    H.ancestor ⟨m, ⟨(S.descendantNode N.ty m r w).move N.frame, hc⟩⟩ r =
      ⟨m + r, ⟨N, hN⟩⟩ := by
  induction r generalizing N with
  | zero =>
    simp [CoherentHierarchy.ancestor, SubstSystem.descendantNode, FramedNode.move]
  | succ r ih =>
    have hchild := H.children_mem (m + r) N (by simpa [Nat.add_assoc] using hN) w.1
    have hc' : (S.descendantNode (N.child (m + r) w.1).ty m r w.2).move
        (N.child (m + r) w.1).frame ∈ H.nodes m := hc
    have hi := ih (N.child (m + r) w.1) hchild w.2 hc'
    rw [← H.ancestor_add]
    change H.parentNode (H.ancestor _ r) = _
    have he : (⟨m, ⟨(S.descendantNode N.ty m (r + 1) w).move N.frame, hc⟩⟩ :
        H.Node) = ⟨m, ⟨(S.descendantNode (N.child (m + r) w.1).ty m r w.2).move
          (N.child (m + r) w.1).frame, hc'⟩⟩ := rfl
    rw [he, hi]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact (H.parent_unique (m + r) ⟨N.child (m + r) w.1, hchild⟩ N
        (by simpa [Nat.add_assoc] using hN) ⟨w.1, rfl⟩).symm

/-- Step 2 of the V4 proof of `base_level_step4_I4` (V4 3.2, 2.5):
"the slot of N". Reindex exact descendant ancestry by the difference
of the two node heights. -/
private lemma base_level_step4_I4_step2_ancestor_node
    {T : Tiling S} (H : CoherentHierarchy S T) (q N : H.Node)
    (h : q.2.val.IsDescendant q.1 N.2.val N.1) :
    H.ancestor q (N.1 - q.1) = N := by
  rcases q with ⟨m, M, hM⟩
  rcases N with ⟨n, N, hN⟩
  obtain ⟨r, hr, w, hw⟩ := h
  dsimp only at hr hw ⊢
  subst n
  rw [show m + r - m = r by omega]
  cases hw
  exact base_level_step4_I4_step2_ancestor H m r N hN w hM

/-- Step 3 of the V4 proof of `base_level_step4_I4` (V4 3.2, 2.7):
"with slot value S(N)". The certificate table is the state of the
same-address descendant of its honest source witness. -/
private lemma base_level_step4_I4_step3_table
    {Y : MarkedTiling (systemM S P C)} (B : KBlock Y)
    (U : HonestSource S) (hB : B.node ∈ U.hierarchy.nodes P.K)
    (hcert : certOf U P B.node hB = B.certificate.val)
    (a : ℕ) (ha : a ≤ P.K) (w : S.RoleWord B.certificate.val.ty a) :
    B.table a ha w =
      stateOf U P (U.descendant ⟨P.K, ⟨B.node, hB⟩⟩ a ha w) := by
  have aux : ∀ X Z : Certificate P, X = Z → ∀ (h : X.ty = Z.ty)
      (a : ℕ) (ha : a ≤ P.K) (w : S.RoleWord X.ty a),
      X.table a ha w = Z.table a ha (h ▸ w) := by
    intro X Z he h a ha w
    subst he
    rfl
  exact (aux _ _ hcert rfl a ha w).symm

/-- Step 4 of the V4 proof of `base_level_step4_I4` (V4 3.2, 2.7):
"these packets are the ones in the leaves' pre-patterns inside D".
An actual ground descendant of a certificate has exactly the facet readout
of the same framed ground node in its honest source, including NULL. -/
private lemma base_level_step4_I4_step4_leaf
    {Y : MarkedTiling (systemM S P C)} (B : KBlock Y)
    (U : HonestSource S) (hB : B.node ∈ U.hierarchy.nodes P.K)
    (hcert : certOf U P B.node hB = B.certificate.val)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (htd : (tileNode t).IsDescendant 0 B.node P.K)
    (f : FacetName S (tileNode t).ty)
    (htU : tileNode t ∈ U.hierarchy.nodes 0) :
    leafPacket (compilerLeaf C t) f.val =
      U.facetPacket P ⟨0, ⟨tileNode t, htU⟩⟩ f := by
  obtain ⟨r, hr, v, hv⟩ := htd
  have hrK : r = P.K := by omega
  subst r
  have hleaf : tileNode (B.leaf v) =
      (S.nativeTile B.certificate.val.ty P.K v).move B.frame := by
    apply FramedNode.ext
    · change (compilerLeaf C (B.leaf v)).prototype = _
      rw [(B.leaf_data v).1]
      rfl
    · exact (B.leaf_data v).2
  have htleaf : t = B.leaf v :=
    base_level_step3_I2_step3_tile_unique t (B.leaf v) ht (B.leaf_mem v)
      (hv.trans hleaf.symm)
  subst t
  have aux : ∀ X Z : Certificate P, X = Z → ∀ (h : X.ty = Z.ty)
      (v : S.RoleWord X.ty P.K), X.leaves v = Z.leaves (h ▸ v) := by
    intro X Z he h v
    subst he
    rfl
  have hpre : B.certificate.val.leaves v =
      prePatternOf U P (U.descendant ⟨P.K, ⟨B.node, hB⟩⟩ P.K le_rfl v)
        (Nat.sub_self P.K) := (aux _ _ hcert rfl v).symm
  have he : U.descendant ⟨P.K, ⟨B.node, hB⟩⟩ P.K le_rfl v =
      ⟨0, ⟨tileNode (B.leaf v), htU⟩⟩ := by
    apply Sigma.subtype_ext
    · exact Nat.sub_self P.K
    · change (S.descendantNode B.certificate.val.ty (P.K - P.K) P.K v).move
        B.frame = tileNode (B.leaf v)
      simpa only [Nat.sub_self] using hleaf.symm
  rw [(B.leaf_data v).1]
  unfold leafPacket LeafType.prePattern
  rw [hpre]
  simp only [prePatternOf]
  have hfacet : f.val ∈ (S.cx
      (U.descendant ⟨P.K, ⟨B.node, hB⟩⟩ P.K le_rfl v).2.val.ty).facets := by
    rw [he]
    exact f.property
  rw [dif_pos hfacet]
  have hcongr : ∀ (q q' : U.Node) (h : q = q')
      (F : FacetName S q.2.val.ty) (F' : FacetName S q'.2.val.ty),
      F.val = F'.val → U.facetPacket P q F = U.facetPacket P q' F' := by
    intro q q' h F F' hF
    subst q'
    exact congrArg (U.facetPacket P q) (Subtype.ext hF)
  exact hcongr _ _ he _ f rfl

/-- Step 5 of the V4 proof of `base_level_step4_I4` (V4 3.2, 2.6(d)):
"these packets are the ones in the leaves' pre-patterns inside D".
Honest inherited facet packets give the constant readout on every side of
an inner certificate node. -/
private lemma base_level_step4_I4_step5_boundary
    {Y : MarkedTiling (systemM S P C)} (B : KBlock Y)
    (U : HonestSource S) (hB : B.node ∈ U.hierarchy.nodes P.K)
    (hcert : certOf U P B.node hB = B.certificate.val)
    (m : ℕ) (N : FramedNode S) (hdesc : N.IsDescendant m B.node P.K) :
    Parser.BoundaryPackets Y m N := by
  have hNU := Parser.hierarchy_descendant_mem U.hierarchy P.K m B.node N hB hdesc
  have hactual : IsBlock Y m N :=
    (base_level_step1_decoded_step0_toBlock B).inner_actual m N hdesc
  intro F
  let q := U.facetPacket P ⟨m, ⟨N, hNU⟩⟩ F
  have hq : Parser.ConstantPacket Y m N F q := by
    intro t f ht
    have htB := Parser.descendant_trans (tileNode t) N B.node 0 m P.K ht.2.1 hdesc
    have htU := Parser.hierarchy_descendant_mem U.hierarchy P.K 0 B.node (tileNode t) hB htB
    rw [base_level_step4_I4_step4_leaf B U hB hcert t ht.1 htB f htU]
    have hanc := base_level_step4_I4_step2_ancestor_node U.hierarchy
      ⟨0, ⟨tileNode t, htU⟩⟩ ⟨m, ⟨N, hNU⟩⟩ ht.2.1
    exact packet_inherited U P ⟨m, ⟨N, hNU⟩⟩ ⟨0, ⟨tileNode t, htU⟩⟩ m
      hanc F f ht.2.2
  exact ⟨q, hq, fun q' hq' => Parser.constantPacket_unique Y m N hactual F q' q hq' hq⟩

/-- Step 6 of the V4 proof of `base_level_step4_I4` (V4 3.2, 2.5):
"in the honest source mu_{slot of N} = PRESENT with slot value S(N)".
This is solely the honest-source slot semantics; it involves no output tiles
or certificate readout. -/
private lemma base_level_step4_I4_step6_slot
    (U : HonestSource S) (N : U.Node) (g : PrimitiveOccurrence U P)
    (hg : g.birth.2.val.IsDescendant g.birth.1 N.2.val N.1)
    (hd : N.1 - g.birth.1 < P.k)
    (hp : P.InPrincipal N.2.val N.1 g.carrier) :
    decode (packetOf U P g) ⟨N.1 - g.birth.1, hd⟩ = some (stateOf U P N) := by
  classical
  have hanc := base_level_step4_I4_step2_ancestor_node U.hierarchy g.birth N hg
  have hm : mask U P g ⟨N.1 - g.birth.1, hd⟩ := by
    unfold mask
    rw [hanc]
    exact hp
  simpa only [if_pos hm, hanc] using
    decode_spec U P g ⟨N.1 - g.birth.1, hd⟩

/-- Step 4 of the V4 proof of `base_level` (V4 3.2): (I4): for every node N inside the certificate and f in E_N born inside N, in the honest source mu_{slot of N} = PRESENT with slot value S(N), and these packets are the ones in the leaves' pre-patterns inside D. -/
private lemma base_level_step4_I4 (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (D : DecodedLevel Y P.K) (hbase : Parser.CertificateBase D) : Parser.I4 D := by
  intro m N hN g hg hd hp
  obtain ⟨B, a, ha, w, hm, hnode⟩ :=
    base_level_step3_I2_step1_certificate_node D.geometry hbase.1 m N hN
  obtain ⟨U, hB, hcert⟩ := base_level_step4_I4_step1_source B
  have hNB : N.IsDescendant m B.node P.K := by
    rw [← hnode, ← hm]
    exact ⟨a, by omega, w, rfl⟩
  have hNU := Parser.hierarchy_descendant_mem U.hierarchy P.K m B.node N hB hNB
  have hbirthB := Parser.descendant_trans g.birth N B.node g.height m P.K hg hNB
  have hbirthU := Parser.hierarchy_descendant_mem U.hierarchy P.K g.height B.node
    g.birth hB hbirthB
  let gU : PrimitiveOccurrence U P :=
    ⟨⟨g.height, ⟨g.birth, hbirthU⟩⟩, g.positive, g.incidence, g.parent_type⟩
  have hleftB := Parser.descendant_trans g.leftNode g.birth B.node (g.height - 1)
    g.height P.K g.sides_descendant.1 hbirthB
  have hboundary := base_level_step4_I4_step5_boundary B U hB hcert
    (g.height - 1) g.leftNode hleftB
  refine ⟨hboundary, packetOf U P gU, ?_, ?_⟩
  · have hactual : IsBlock Y (g.height - 1) g.leftNode :=
      (base_level_step1_decoded_step0_toBlock B).inner_actual _ _ hleftB
    obtain ⟨t, f, ht⟩ := Parser.facet_piece_exists Y (g.height - 1) g.leftNode hactual
      g.incidence.val.leftFacet
    have htB := Parser.descendant_trans (tileNode t) g.leftNode B.node 0
      (g.height - 1) P.K ht.2.1 hleftB
    have htU := Parser.hierarchy_descendant_mem U.hierarchy P.K 0 B.node (tileNode t) hB htB
    change attachedPacket hboundary g.incidence.val.leftFacet = _
    rw [attachedPacket_eq_leaf hboundary g.incidence.val.leftFacet t f ht,
      base_level_step4_I4_step4_leaf B U hB hcert t ht.1 htB f htU]
    apply (packet_attached U P gU ⟨0, ⟨tileNode t, htU⟩⟩ rfl f ?_).2
    change (tileNode t).cell 0 f.val ⊆ g.carrier
    rw [← g.sides_carrier.1]
    exact ht.2.2
  · have hstate : D.stateAt m N hN = stateOf U P ⟨m, ⟨N, hNU⟩⟩ := by
      subst m
      subst N
      exact (hbase.2 B a ha w).choose_spec.trans
        (base_level_step4_I4_step3_table B U hB hcert a ha w)
    rw [hstate]
    exact base_level_step4_I4_step6_slot U ⟨m, ⟨N, hNU⟩⟩ gU hg hd hp

/-- Step 2 of the V4 proof of `base_level_step5_I5_step1_boundary` (V4 3.2): unpack node membership to identify its root with a K-certificate. -/
private lemma base_level_step5_I5_step1_boundary_step2_certificate
    (Y : MarkedTiling (systemM S P C))
    (D : DecodedLevel Y P.K) (hbase : Parser.CertificateBase D)
    (m : ℕ) (N : FramedNode S) (hN : N ∈ D.geometry.nodes m) :
    ∃ (B : KBlock Y) (a : ℕ) (ha : a ≤ P.K)
      (w : S.RoleWord B.certificate.val.ty a),
      P.K - a = m ∧ B.innerNode a ha w = N := by
  exact base_level_step3_I2_step1_certificate_node D.geometry hbase.1 m N hN

/-- Step 3 of the V4 proof of `base_level_step5_I5_step1_boundary` (V4 2.17(a)): actual tiles inside the block are prescribed leaves. -/
private lemma base_level_step5_I5_step1_boundary_step3_leaf
    (Y : MarkedTiling (systemM S P C)) (B : KBlock Y)
    (a : ℕ) (ha : a ≤ P.K)
    (w : S.RoleWord B.certificate.val.ty a)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (hdesc : (tileNode t).IsDescendant 0
      (B.innerNode a ha w) (P.K - a)) :
    ∃ v : S.RoleWord B.certificate.val.ty P.K, B.leaf v = t := by
  have hin : (B.innerNode a ha w).IsDescendant (P.K - a)
      B.node P.K :=
    ⟨a, by omega, w, rfl⟩
  have hroot : (tileNode t).IsDescendant 0 B.node P.K :=
    Parser.descendant_trans (tileNode t) (B.innerNode a ha w)
      B.node 0 (P.K - a) P.K hdesc hin
  have hcar : t.carrier = (tileNode t).carrier 0 := by
    rw [compilerFrame_carrier C t]
    simp [tileNode, FramedNode.carrier, SubstSystem.supertile, placedSet]
  have hsub : t.carrier ⊆ B.carrier := by
    rw [hcar]
    exact base_level_step1_decoded_step2_descendant_subset
      (tileNode t) B.node 0 P.K hroot
  have hmem : t ∈ Set.range B.leaf := by
    rw [← B.tiles_exact]
    exact ⟨ht, hsub⟩
  exact hmem

private lemma cert_leaves_of_eq {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d} {P : Params S} {D₁ D₂ : Certificate P} (h : D₁ = D₂) (hty : D₁.ty = D₂.ty) (w : S.RoleWord D₂.ty P.K) : D₁.leaves (hty.symm ▸ w) = D₂.leaves w := by
  subst h
  cases hty
  rfl

/-- Step 1 of the V4 proof of `base_level_step5_I5_step1_boundary_step4_honest` (V4 2.6(c)): the leaf packet equals the honest source facet packet. -/
private lemma base_level_step5_I5_step1_boundary_step4_honest_step1_leafPacket
    (Y : MarkedTiling (systemM S P C)) (B : KBlock Y)
    (U : HonestSource S) (N_honest : FramedNode S) (hN_honest : N_honest ∈ U.hierarchy.nodes P.K)
    (h_cert : certOf U P N_honest hN_honest = B.certificate.val)
    (h_ty_eq : (⟨P.K, N_honest, hN_honest⟩ : U.Node).2.val.ty = B.certificate.val.ty)
    (v : S.RoleWord B.certificate.val.ty P.K)
    (f : FacetName S (tileNode (B.leaf v)).ty)
    (h_ty : (U.descendant ⟨P.K, N_honest, hN_honest⟩ P.K le_rfl (h_ty_eq.symm ▸ v)).2.val.ty = (tileNode (B.leaf v)).ty) :
    leafPacket (compilerLeaf C (B.leaf v)) f.val =
      U.facetPacket P (U.descendant ⟨P.K, N_honest, hN_honest⟩ P.K le_rfl (h_ty_eq.symm ▸ v)) (h_ty.symm ▸ f) := by
  have hl : prePatternOf U P (U.descendant ⟨P.K, ⟨N_honest, hN_honest⟩⟩ P.K le_rfl (h_ty_eq.symm ▸ v)) (Nat.sub_self P.K) = B.certificate.val.leaves v := cert_leaves_of_eq h_cert h_ty_eq v
  rw [(B.leaf_data v).1]
  unfold leafPacket
  classical
  show (if hf : f.val ∈ (S.cx (B.certificate.val.leaves v).ty).facets then (B.certificate.val.leaves v).packets ⟨f.val, hf⟩ else none) = _
  rw [← hl]
  change (if hf : f.val ∈ (S.cx (U.descendant ⟨P.K, ⟨N_honest, hN_honest⟩⟩ P.K le_rfl (h_ty_eq.symm ▸ v)).2.val.ty).facets then U.facetPacket P (U.descendant ⟨P.K, ⟨N_honest, hN_honest⟩⟩ P.K le_rfl (h_ty_eq.symm ▸ v)) ⟨f.val, hf⟩ else none) = U.facetPacket P (U.descendant ⟨P.K, ⟨N_honest, hN_honest⟩⟩ P.K le_rfl (h_ty_eq.symm ▸ v)) (h_ty.symm ▸ f)
  generalize hq' : U.descendant ⟨P.K, ⟨N_honest, hN_honest⟩⟩ P.K le_rfl (h_ty_eq.symm ▸ v) = q' at h_ty ⊢
  have key : ∀ (T : S.ι) (hT : q'.2.val.ty = T) (g : FacetName S T), (if hf : g.val ∈ (S.cx q'.2.val.ty).facets then U.facetPacket P q' ⟨g.val, hf⟩ else none) = U.facetPacket P q' (hT.symm ▸ g) := by
    intro T hT g
    cases hT
    rw [dif_pos g.2]
  exact key ((tileNode (B.leaf v)).ty) h_ty f

/-- Step 1 of the V4 proof of `base_level_step5_I5_step1_boundary_step4_honest_step2_inherited` (V4 2.6(d)): honest source hierarchy ancestor relation. -/
private lemma base_level_step5_I5_step1_boundary_step4_honest_step2_inherited_step1_anc_desc
    (U : HonestSource S) (h r : ℕ) (N : FramedNode S)
    (hN : N ∈ U.hierarchy.nodes (h + r)) (w : S.RoleWord N.ty r)
    (hc : (S.descendantNode N.ty h r w).move N.frame ∈ U.hierarchy.nodes h) :
    U.hierarchy.ancestor ⟨h, ⟨(S.descendantNode N.ty h r w).move N.frame, hc⟩⟩ r
      = ⟨h + r, ⟨N, hN⟩⟩ := by
  exact base_level_step4_I4_step2_ancestor U.hierarchy h r N hN w hc

/-- Step 2 of the V4 proof of `base_level_step5_I5_step1_boundary_step4_honest_step2_inherited` (V4 2.6(d)): word extension. -/
private lemma base_level_step5_I5_step1_boundary_step4_honest_step2_inherited_step2_leaf_extends_inner
    (Y : MarkedTiling (systemM S P C)) (B : KBlock Y) (a : ℕ) (ha : a ≤ P.K)
    (w : S.RoleWord B.certificate.val.ty a) (v : S.RoleWord B.certificate.val.ty P.K)
    (h : (tileNode (B.leaf v)).IsDescendant 0 (B.innerNode a ha w) (P.K - a)) :
    ∃ x : S.RoleWord (B.innerNode a ha w).ty (P.K - a),
      S.descendantNode B.certificate.val.ty 0 P.K v =
        (S.descendantNode (B.innerNode a ha w).ty 0 (P.K - a) x).move
          (S.descendantNode B.certificate.val.ty (P.K - a) a w).frame := by
  obtain ⟨r, hr, x, hx⟩ := h
  have hr' : r = P.K - a := by omega
  subst hr'
  use x
  have hleaf : tileNode (B.leaf v) =
      (S.descendantNode B.certificate.val.ty 0 P.K v).move B.frame := by
    apply FramedNode.ext
    · change (compilerLeaf C (B.leaf v)).prototype = _
      rw [(B.leaf_data v).1]
      rfl
    · change compilerFrame C (B.leaf v) = _
      rw [(B.leaf_data v).2]
      rfl
  rw [hleaf] at hx
  have hx2 : (S.descendantNode B.certificate.val.ty 0 P.K v).move B.frame =
      (S.descendantNode (B.innerNode a ha w).ty 0 (P.K - a) x).move
        ((S.descendantNode B.certificate.val.ty (P.K - a) a w).frame.trans B.frame) := hx
  apply FramedNode.ext
  · have ht := congrArg FramedNode.ty hx2
    exact ht
  · ext y : 1
    have hf := congrArg (fun N : FramedNode S => N.frame y) hx2
    exact B.frame.injective hf

/-- Step 3 of the V4 proof of `base_level_step5_I5_step1_boundary_step4_honest_step2_inherited` (V4 2.6(d)): split cast transport auxiliary. -/
private lemma base_level_step5_I5_step1_boundary_step4_honest_step2_inherited_step3_split_cast_aux
    {T T' T1 : S.ι} (e : T' = T) (n m k : ℕ)
    (w : S.RoleWord T' n) (v : S.RoleWord T' m) (x : S.RoleWord T1 k)
    (h : S.descendantNode T' 0 m v =
        (S.descendantNode T1 0 k x).move (S.descendantNode T' k n w).frame)
    (A_ty : S.ι) (hA : A_ty = T1) :
    ∃ x' : S.RoleWord A_ty k,
      S.descendantNode T 0 m (e.symm ▸ v) =
        (S.descendantNode A_ty 0 k x').move (S.descendantNode T k n (e.symm ▸ w)).frame := by
  subst e
  subst hA
  exact ⟨x, h⟩

/-- Step 3 of the V4 proof of `base_level_step5_I5_step1_boundary_step4_honest_step2_inherited` (V4 2.6(d)): descendant splitting cast. -/
private lemma base_level_step5_I5_step1_boundary_step4_honest_step2_inherited_step3_split_cast
    (Y : MarkedTiling (systemM S P C)) (B : KBlock Y)
    (a : ℕ) (ha : a ≤ P.K)
    (w : S.RoleWord B.certificate.val.ty a)
    (v : S.RoleWord B.certificate.val.ty P.K)
    (x : S.RoleWord (B.innerNode a ha w).ty (P.K - a))
    (h_split : S.descendantNode B.certificate.val.ty 0 P.K v =
        (S.descendantNode (B.innerNode a ha w).ty 0 (P.K - a) x).move
          (S.descendantNode B.certificate.val.ty (P.K - a) a w).frame)
    (U : HonestSource S) (N_honest : FramedNode S) (hN_honest : N_honest ∈ U.hierarchy.nodes P.K)
    (h_ty_eq : (⟨P.K, N_honest, hN_honest⟩ : U.Node).2.val.ty = B.certificate.val.ty)
    (A : U.Node) (hA : A = U.descendant ⟨P.K, N_honest, hN_honest⟩ a ha (h_ty_eq.symm ▸ w))
    (h_ty_A : A.2.val.ty = (B.innerNode a ha w).ty) :
    ∃ x' : S.RoleWord A.2.val.ty (P.K - a),
      S.descendantNode (⟨P.K, N_honest, hN_honest⟩ : U.Node).2.val.ty 0 P.K (h_ty_eq.symm ▸ v) =
        (S.descendantNode A.2.val.ty 0 (P.K - a) x').move
          (S.descendantNode (⟨P.K, N_honest, hN_honest⟩ : U.Node).2.val.ty (P.K - a) a (h_ty_eq.symm ▸ w)).frame := by
  exact base_level_step5_I5_step1_boundary_step4_honest_step2_inherited_step3_split_cast_aux h_ty_eq.symm a P.K (P.K - a) w v x h_split A.2.val.ty h_ty_A

/-- Step 4 of the V4 proof of `base_level_step5_I5_step1_boundary_step4_honest_step2_inherited` (V4 2.6(d)): descendant node ancestor. -/
private lemma base_level_step5_I5_step1_boundary_step4_honest_step2_inherited_step4_ancestor
    (U : HonestSource S) (P : Params S) (q : U.Node) (a : ℕ) (ha : a ≤ q.fst)
    (w : S.RoleWord q.2.val.ty a) (v : S.RoleWord q.2.val.ty q.fst)
    (A L : U.Node) (hA : A = U.descendant q a ha w) (hL : L = U.descendant q q.fst le_rfl v)
    (x : S.RoleWord A.2.val.ty (q.fst - a))
    (h_split : S.descendantNode q.2.val.ty 0 q.fst v =
        (S.descendantNode A.2.val.ty 0 (q.fst - a) x).move
          (S.descendantNode q.2.val.ty (q.fst - a) a w).frame) :
    U.hierarchy.ancestor L (q.fst - a) = A := by
  subst hA hL
  have hd : (U.descendant q q.fst le_rfl v).2.val.IsDescendant
      (U.descendant q q.fst le_rfl v).1
      (U.descendant q a ha w).2.val (U.descendant q a ha w).1 := by
    refine ⟨q.fst - a, ?_, x, ?_⟩
    · show q.fst - a = q.fst - q.fst + (q.fst - a)
      omega
    · show (S.descendantNode q.2.val.ty (q.fst - q.fst) q.fst v).move q.2.val.frame =
        (S.descendantNode (U.descendant q a ha w).2.val.ty (q.fst - q.fst) (q.fst - a) x).move
          ((S.descendantNode q.2.val.ty (q.fst - a) a w).frame.trans q.2.val.frame)
      rw [Nat.sub_self, h_split]
      rfl
  have h := base_level_step4_I4_step2_ancestor_node U.hierarchy _ _ hd
  have he : (U.descendant q a ha w).1 - (U.descendant q q.fst le_rfl v).1 = q.fst - a := by
    show q.fst - a - (q.fst - q.fst) = q.fst - a
    omega
  rw [he] at h
  exact h

/-- Step 5 of the V4 proof of `base_level_step5_I5_step1_boundary_step4_honest_step2_inherited` (V4 2.6(d)): descendant cell inclusion. -/
private lemma base_level_step5_I5_step1_boundary_step4_honest_step2_inherited_step5_cell
    (Y : MarkedTiling (systemM S P C)) (B : KBlock Y)
    (a : ℕ) (ha : a ≤ P.K)
    (w : S.RoleWord B.certificate.val.ty a)
    (F : FacetName S (B.innerNode a ha w).ty)
    (U : HonestSource S) (N_honest : FramedNode S) (hN_honest : N_honest ∈ U.hierarchy.nodes P.K)
    (h_cert : certOf U P N_honest hN_honest = B.certificate.val)
    (h_ty_eq : (⟨P.K, N_honest, hN_honest⟩ : U.Node).2.val.ty = B.certificate.val.ty)
    (v : S.RoleWord B.certificate.val.ty P.K)
    (f : FacetName S (tileNode (B.leaf v)).ty)
    (h_piece : Parser.IsFacetPiece Y (P.K - a) (B.innerNode a ha w) F (B.leaf v) f)
    (h_ty_A : (U.descendant ⟨P.K, N_honest, hN_honest⟩ a ha (h_ty_eq.symm ▸ w)).2.val.ty = (B.innerNode a ha w).ty)
    (h_ty_L : (U.descendant ⟨P.K, N_honest, hN_honest⟩ P.K le_rfl (h_ty_eq.symm ▸ v)).2.val.ty = (tileNode (B.leaf v)).ty) :
    (U.descendant ⟨P.K, N_honest, hN_honest⟩ P.K le_rfl (h_ty_eq.symm ▸ v)).2.val.cell
        (U.descendant ⟨P.K, N_honest, hN_honest⟩ P.K le_rfl (h_ty_eq.symm ▸ v)).1
        (h_ty_L.symm ▸ f).val ⊆
      (U.descendant ⟨P.K, N_honest, hN_honest⟩ a ha (h_ty_eq.symm ▸ w)).2.val.cell
        (U.descendant ⟨P.K, N_honest, hN_honest⟩ a ha (h_ty_eq.symm ▸ w)).1
        (h_ty_A.symm ▸ F).val := by
  sorry

/-- Step 2 of the V4 proof of `base_level_step5_I5_step1_boundary_step4_honest` (V4 2.6(d)): packets are inherited unchanged along the tracks. -/
private lemma base_level_step5_I5_step1_boundary_step4_honest_step2_inherited
    (Y : MarkedTiling (systemM S P C)) (B : KBlock Y)
    (a : ℕ) (ha : a ≤ P.K)
    (w : S.RoleWord B.certificate.val.ty a)
    (F : FacetName S (B.innerNode a ha w).ty)
    (U : HonestSource S) (N_honest : FramedNode S) (hN_honest : N_honest ∈ U.hierarchy.nodes P.K)
    (h_cert : certOf U P N_honest hN_honest = B.certificate.val)
    (h_ty_eq : (⟨P.K, N_honest, hN_honest⟩ : U.Node).2.val.ty = B.certificate.val.ty)
    (v : S.RoleWord B.certificate.val.ty P.K)
    (f : FacetName S (tileNode (B.leaf v)).ty)
    (h_piece : Parser.IsFacetPiece Y (P.K - a) (B.innerNode a ha w) F (B.leaf v) f)
    (h_ty_A : (U.descendant ⟨P.K, N_honest, hN_honest⟩ a ha (h_ty_eq.symm ▸ w)).2.val.ty = (B.innerNode a ha w).ty)
    (h_ty_L : (U.descendant ⟨P.K, N_honest, hN_honest⟩ P.K le_rfl (h_ty_eq.symm ▸ v)).2.val.ty = (tileNode (B.leaf v)).ty) :
    U.facetPacket P (U.descendant ⟨P.K, N_honest, hN_honest⟩ P.K le_rfl (h_ty_eq.symm ▸ v)) (h_ty_L.symm ▸ f) =
    U.facetPacket P (U.descendant ⟨P.K, N_honest, hN_honest⟩ a ha (h_ty_eq.symm ▸ w)) (h_ty_A.symm ▸ F) := by
  obtain ⟨x, hx⟩ := base_level_step5_I5_step1_boundary_step4_honest_step2_inherited_step2_leaf_extends_inner Y B a ha w v h_piece.2.1
  obtain ⟨x', hx'⟩ := base_level_step5_I5_step1_boundary_step4_honest_step2_inherited_step3_split_cast Y B a ha w v x hx U N_honest hN_honest h_ty_eq _ rfl h_ty_A
  have hca : U.hierarchy.ancestor (U.descendant ⟨P.K,N_honest,hN_honest⟩ P.K le_rfl (h_ty_eq.symm ▸ v)) (P.K - a)
      = U.descendant ⟨P.K,N_honest,hN_honest⟩ a ha (h_ty_eq.symm ▸ w) :=
    base_level_step5_I5_step1_boundary_step4_honest_step2_inherited_step4_ancestor U P ⟨P.K,N_honest,hN_honest⟩ a ha (h_ty_eq.symm ▸ w) (h_ty_eq.symm ▸ v) _ _ rfl rfl x' hx'
  have hgf := base_level_step5_I5_step1_boundary_step4_honest_step2_inherited_step5_cell Y B a ha w F U N_honest hN_honest h_cert h_ty_eq v f h_piece h_ty_A h_ty_L
  exact packet_inherited U P _ _ (P.K - a) hca (h_ty_A.symm ▸ F) (h_ty_L.symm ▸ f) hgf

open private exists_honest_step7_descendant_type from Enforce.Tiling in
/-- Step 4 of the V4 proof of `base_level_step5_I5_step1_boundary` (V4 2.6(c),(d)): honest packet constancy for prescribed leaves. -/
private lemma base_level_step5_I5_step1_boundary_step4_honest
    (Y : MarkedTiling (systemM S P C)) (B : KBlock Y)
    (a : ℕ) (ha : a ≤ P.K)
    (w : S.RoleWord B.certificate.val.ty a)
    (F : FacetName S (B.innerNode a ha w).ty) :
    ∃ q : Option (Packet P),
      ∀ (v : S.RoleWord B.certificate.val.ty P.K)
        (f : FacetName S (tileNode (B.leaf v)).ty),
        Parser.IsFacetPiece Y (P.K - a) (B.innerNode a ha w)
          F (B.leaf v) f →
        leafPacket (compilerLeaf C (B.leaf v)) f.val = q := by
  obtain ⟨U, N_honest, hN_honest, h_cert⟩ := KBlock.honest_table B
  have h_ty_eq : (⟨P.K, N_honest, hN_honest⟩ : U.Node).2.val.ty = B.certificate.val.ty := by
    change (certOf U P N_honest hN_honest).ty = _
    rw [h_cert]
  have native_cast : ∀ (T T' : S.ι) (e : T = T')
      (n : ℕ) (z : S.RoleWord T' n),
      (S.nativeTile T n (e.symm ▸ z)).ty =
        (S.nativeTile T' n z).ty := by
    intro T T' e n z
    cases e
    rfl
  let A := U.descendant ⟨P.K, N_honest, hN_honest⟩ a ha (h_ty_eq.symm ▸ w)
  have h_ty_A : A.2.val.ty = (B.innerNode a ha w).ty := by
    calc
      A.2.val.ty =
          (S.nativeTile N_honest.ty a (h_ty_eq.symm ▸ w)).ty :=
        U.descendant_type ⟨P.K, N_honest, hN_honest⟩
          a ha (h_ty_eq.symm ▸ w)
      _ = (S.nativeTile B.certificate.val.ty a w).ty :=
        native_cast _ _ h_ty_eq a w
      _ = (B.innerNode a ha w).ty :=
        (exists_honest_step7_descendant_type
          B.certificate.val.ty (P.K - a) a w).symm
  use U.facetPacket P A (h_ty_A.symm ▸ F)
  intro v f hf
  let L := U.descendant ⟨P.K, N_honest, hN_honest⟩ P.K le_rfl (h_ty_eq.symm ▸ v)
  have h_ty_L : L.2.val.ty = (tileNode (B.leaf v)).ty := by
    calc
      L.2.val.ty =
          (S.nativeTile N_honest.ty P.K (h_ty_eq.symm ▸ v)).ty :=
        U.descendant_type ⟨P.K, N_honest, hN_honest⟩
          P.K le_rfl (h_ty_eq.symm ▸ v)
      _ = (S.nativeTile B.certificate.val.ty P.K v).ty :=
        native_cast _ _ h_ty_eq P.K v
      _ = (tileNode (B.leaf v)).ty := by
        change _ = (compilerLeaf C (B.leaf v)).prototype
        rw [(B.leaf_data v).1]
        rfl
  have h1 : leafPacket (compilerLeaf C (B.leaf v)) f.val = U.facetPacket P L (h_ty_L.symm ▸ f) :=
    base_level_step5_I5_step1_boundary_step4_honest_step1_leafPacket Y B U N_honest hN_honest h_cert h_ty_eq v f h_ty_L
  have h2 : U.facetPacket P L (h_ty_L.symm ▸ f) = U.facetPacket P A (h_ty_A.symm ▸ F) :=
    base_level_step5_I5_step1_boundary_step4_honest_step2_inherited Y B a ha w F U N_honest hN_honest h_cert h_ty_eq v f hf h_ty_A h_ty_L
  rw [h1, h2]

/-- Step 1 of the V4 proof of `base_level_step5_I5_step1_boundary` (V4 3.2): a specific packet q exists and is constant along the facet F. -/
private lemma base_level_step5_I5_step1_boundary_step1_packet (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (D : DecodedLevel Y P.K) (hbase : Parser.CertificateBase D) (m : ℕ) (N : FramedNode S) (hN : N ∈ D.geometry.nodes m)
    (F : FacetName S N.ty) : ∃ q : Option (Packet P), Parser.ConstantPacket Y m N F q := by
  obtain ⟨B, a, ha, w, hm, rfl⟩ := base_level_step5_I5_step1_boundary_step2_certificate Y D hbase m N hN
  obtain ⟨q, hq⟩ := base_level_step5_I5_step1_boundary_step4_honest Y B a ha w F
  use q
  intro t f hpiece
  obtain ⟨ht, hdesc, hsub⟩ := hpiece
  have hdesc' : (tileNode t).IsDescendant 0 (B.innerNode a ha w) (P.K - a) := hm ▸ hdesc
  obtain ⟨v, rfl⟩ := base_level_step5_I5_step1_boundary_step3_leaf Y B a ha w t ht hdesc'
  have hpiece' : Parser.IsFacetPiece Y (P.K - a) (B.innerNode a ha w) F (B.leaf v) f := ⟨ht, hm ▸ hdesc, hm ▸ hsub⟩
  exact hq v f hpiece'

/-- Step 1 of the V4 proof of `base_level_step5_I5` (V4 3.2): constant packets existence for boundary packets. -/
private lemma base_level_step5_I5_step1_boundary (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (D : DecodedLevel Y P.K) (hbase : Parser.CertificateBase D) (m : ℕ) (N : FramedNode S) (hN : N ∈ D.geometry.nodes m) :
    ∃ h : Parser.BoundaryPackets Y m N, True := by
  have h_block : IsBlock Y m N := by
    obtain ⟨B, _, hdesc⟩ := hN
    exact B.inner_actual m N hdesc
  have h_pack : Parser.BoundaryPackets Y m N := fun F =>
    let ⟨q, hq⟩ := base_level_step5_I5_step1_boundary_step1_packet Y hY D hbase m N hN F
    ⟨q, hq, fun q' hq' => Parser.constantPacket_unique Y m N h_block F q' q hq' hq⟩
  exact ⟨h_pack, trivial⟩

/-- Step 2 of the V4 proof of `base_level_step5_I5` (V4 3.2): equality of packets for E-related facets. -/
private lemma base_level_step5_I5_step2_equality (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (D : DecodedLevel Y P.K) (hbase : Parser.CertificateBase D) (m : ℕ) (N : FramedNode S) (hN : N ∈ D.geometry.nodes m)
    (h : Parser.BoundaryPackets Y m N) (F F' : FacetName S N.ty) (he : stateEAt (D.stateAt m N hN) F.val F'.val)
    (hne : (N.cell m F.val ∩ N.cell m F'.val).Nonempty) : attachedPacket h F = attachedPacket h F' := by
  obtain ⟨B, a, ha, w, hm, hnode⟩ :=
    base_level_step3_I2_step1_certificate_node D.geometry hbase.1 m N hN
  obtain ⟨U, hB, hcert⟩ := base_level_step4_I4_step1_source B
  have hNB : N.IsDescendant m B.node P.K := by
    rw [← hnode, ← hm]
    exact ⟨a, by omega, w, rfl⟩
  have hNU := Parser.hierarchy_descendant_mem U.hierarchy P.K m B.node N hB hNB
  have hstate : D.stateAt m N hN = stateOf U P ⟨m, ⟨N, hNU⟩⟩ := by
    subst m
    subst N
    exact (hbase.2 B a ha w).choose_spec.trans
      (base_level_step4_I4_step3_table B U hB hcert a ha w)
  have hread : ∀ G : FacetName S N.ty,
      attachedPacket h G = U.facetPacket P ⟨m, ⟨N, hNU⟩⟩ G := by
    intro G
    obtain ⟨t, f, ht⟩ := Parser.facet_piece_exists Y m N
      (D.geometry.node_actual m N hN) G
    have htB := Parser.descendant_trans (tileNode t) N B.node 0 m P.K ht.2.1 hNB
    have htU := Parser.hierarchy_descendant_mem U.hierarchy P.K 0 B.node (tileNode t) hB htB
    rw [attachedPacket_eq_leaf h G t f ht,
      base_level_step4_I4_step4_leaf B U hB hcert t ht.1 htB f htU]
    exact packet_inherited U P ⟨m, ⟨N, hNU⟩⟩ ⟨0, ⟨tileNode t, htU⟩⟩ m
      (base_level_step4_I4_step2_ancestor_node U.hierarchy
        ⟨0, ⟨tileNode t, htU⟩⟩ ⟨m, ⟨N, hNU⟩⟩ ht.2.1) G f ht.2.2
  rw [hstate] at he
  obtain ⟨_, _, hE⟩ := he
  obtain ⟨r, _, G, hF, hF'⟩ := (U.mem_coalescenceTable ⟨m, ⟨N, hNU⟩⟩ F F').mp hE
  rw [hread F, hread F']
  exact (packet_inherited U P (U.hierarchy.ancestor ⟨m, ⟨N, hNU⟩⟩ r)
    ⟨m, ⟨N, hNU⟩⟩ r rfl G F hF).trans
      (packet_inherited U P (U.hierarchy.ancestor ⟨m, ⟨N, hNU⟩⟩ r)
        ⟨m, ⟨N, hNU⟩⟩ r rfl G F' hF').symm

/-- Step 5 of the V4 proof of `base_level` (V4 3.2): (I5): for a node N inside the certificate and a facet F of N, the tiles inside N with pieces in F are leaves of D carrying the honest packets, which are constant along F and equal for E-related facets. -/
private lemma base_level_step5_I5 (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (D : DecodedLevel Y P.K) (hbase : Parser.CertificateBase D) : Parser.I5 D := by
  intro m N hN
  obtain ⟨h, _⟩ := base_level_step5_I5_step1_boundary Y hY D hbase m N hN
  exact ⟨h, base_level_step5_I5_step2_equality Y hY D hbase m N hN h⟩

/-- R2, V4 3.2: the forced K-blocks with their honest tables form the base
decoded level. An arbitrary proper Y supplies the actual certificates, so no
nonempty-species assumption or pre-existing hierarchy is used. -/
theorem base_level (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    ∃ D : DecodedLevel Y P.K, Inv D ∧ Parser.CertificateBase D := by
  obtain ⟨D, hD⟩ := base_level_step1_decoded Y hY
  exact ⟨D, ⟨base_level_step2_I1 Y hY D hD, base_level_step3_I2 Y hY D hD,
    base_level_step4_I4 Y hY D hD, base_level_step5_I5 Y hY D hD⟩, hD⟩

/-- R2, V4 3.2: the certificate base level selected from the base existence
theorem. Properness supplies the actual certificates and their joint tables. -/
def baseLevel (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) : DecodedLevel Y P.K :=
  Classical.choose (base_level Y hY)

/-- R2, V4 3.2: the selected base satisfies the four exact invariants. -/
theorem baseLevel_invariant (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    Inv (baseLevel Y hY) := (Classical.choose_spec (base_level Y hY)).1

/-- R2, V4 3.2: the selected base has precisely the forced roots and S-tables. -/
theorem baseLevel_certificates (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    Parser.CertificateBase (baseLevel Y hY) := (Classical.choose_spec (base_level Y hY)).2

namespace KBlock

variable {Y : MarkedTiling (systemM S P C)} (B : KBlock Y)

/-- R1/R2, V4 §3.0, 3.2: a whole forced certificate is an actual height-K
block in the parser's sense. Every leaf has its prescribed prototype and frame. -/
theorem isBlock : IsBlock Y P.K B.node := by
  intro w
  refine ⟨B.leaf w, B.leaf_mem w, ?_⟩
  apply FramedNode.ext
  · change (compilerLeaf C (B.leaf w)).prototype = _
    rw [(B.leaf_data w).1]
    rfl
  · exact (B.leaf_data w).2

/-- R1/R2, V4 §3.0, 3.2: forget only the certificate label, retaining the
forced root and its actual native subdivision as an ordinary parser block. -/
def toBlock : Block Y P.K := ⟨B.node, B.isBlock⟩

/-- R1/R2, V4 §3.0, 3.2: certificate-to-block transport preserves the full root frame. -/
theorem toBlock_node : B.toBlock.node = B.node := rfl

end KBlock

/-- R3, V4 §3.2: the first address letter of a decoded root state. -/
def firstRole {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) : S.Role :=
  (D.blockState B hB).address ⟨0, P.k_pos⟩

/-- R3, V4 §3.2: PP(B), the proposed parent specified by the first address letter.
Its frame is φ_B composed with the inverse height-n placed-child isometry.
The conjugated `placeChild` retains the general anisotropic expansion. -/
def proposedParent {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) : FramedNode S :=
  let r := firstRole D B hB
  ⟨r.1, (S.placeChild n r.2).symm.trans B.node.frame⟩

namespace Parser

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)

/-- R3, V4 §3.2: the finite age-one record read from a specified root facet. -/
structure AgeOneFacet (B : Block Y n) (hB : B ∈ D.geometry.blocks)
    (f : FacetName S B.node.ty) where
  /-- R3, V4 §3.2: the actual finite facet record. -/
  record : FacetRecord P
  /-- R3, V4 §3.2: the record belongs to the decoded state at this named facet. -/
  readout : stateRecordAt (D.blockState B hB) f.val = some record
  /-- R3, V4 §3.2: the recorded age is exactly one, not a capped larger age. -/
  age_one : record.age.val = 1

end Parser

/-- R3, V4 §3.2: PS_f(B), the opposite child of PP(B) named by the age-one
incidence and its serving side. Exact matching of the parent type is a consequence
of honest state semantics; the formula already specifies its full frame. -/
def proposedSibling {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)
    (B : Block Y n) (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : Parser.AgeOneFacet D B hB f) : FramedNode S :=
  let ι := a.record.incidence.val
  let j := ι.sideIndex (!a.record.sideIndex)
  ⟨(S.child ι.ty j).ty, (S.placeChild n j).trans (proposedParent D B hB).frame⟩

namespace Parser

variable {Y : MarkedTiling (systemM S P C)} {n : ℕ} (D : DecodedLevel Y n)

/-- R3, V4 §3.2: the proposed parent has B as its prescribed child, with equal frame. -/
theorem proposedParent_child (h : Inv D) (B : Block Y n) (hB : B ∈ D.geometry.blocks) :
    (proposedParent D B hB).child n (firstRole D B hB).2 = B.node := by
  ext
  · dsimp [proposedParent, FramedNode.child]
    have H := h.node_type_residue n B.node (D.geometry.root_mem B hB)
    have H2 := (D.blockState B hB).address_start
    dsimp [firstRole, DecodedLevel.blockState] at *
    rw [H2, H.1]
  · change (((S.placeChild n (firstRole D B hB).2).trans ((S.placeChild n (firstRole D B hB).2).symm.trans B.node.frame)) _ : E d).ofLp _ = _
    rw [AffineIsometryEquiv.trans_assoc, AffineIsometryEquiv.self_trans_symm, AffineIsometryEquiv.refl_trans]

/-- R3, V4 §3.2, 2.4(a): age-one incidence, serving role, and geometry agree
with the first address and the named block facet. -/
private lemma ageOneFacet_semantics_step2_internal (h : Inv D) (B : Block Y n)
    (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : AgeOneFacet D B hB f) :
    AgeOneRecord (D.blockState B hB) a.record := by
  have hs := (h.I1 B hB).1
  have hty := (h.I1 B hB).2.1
  have hf2 : f.val ∈ (S.cx (D.blockState B hB).ty).facets := by
    have h1 := f.property
    rwa [hty]
  let f' : FacetName S (D.blockState B hB).ty := ⟨f.val, hf2⟩
  have hr : (D.blockState B hB).facetRecord f' = some a.record := by
    have hr' := a.readout
    change stateRecordAt (D.blockState B hB) f.val = some a.record at hr'
    unfold stateRecordAt at hr'
    split_ifs at hr'
    · convert hr'
  exact (state_semantics_a P (D.blockState B hB) hs f').2 a.record hr a.age_one |>.2

private lemma ageOneFacet_semantics_step3_types (h : Inv D) (B : Block Y n)
    (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : AgeOneFacet D B hB f) :
    a.record.incidence.val.ty = (proposedParent D B hB).ty ∧
    a.record.servingRole = firstRole D B hB := by
  have hA := ageOneFacet_semantics_step2_internal D h B hB f a
  have h3 : a.record.servingRole = firstRole D B hB := hA.2.1
  have h2 : a.record.incidence.val.ty = (proposedParent D B hB).ty := by
    have h_side := a.record.side_eq
    have h_ty : a.record.servingRole.1 = a.record.incidence.val.ty := by
      change a.record.side.1 = a.record.incidence.val.ty
      have H := (congrArg Sigma.fst h_side).symm
      change _ = a.record.side.1 at H
      exact H.symm
    rw [← h_ty, h3]
    rfl
  exact ⟨h2, h3⟩

open private incidentForest_step1_placeChild_pow from Enforce.Source.Headers in
/-- Step 4 of the V4 proof of `ageOneFacet_semantics` (V4 3.2): the paired facet is correctly placed as a child cell. -/
private lemma ageOneFacet_semantics_step4_cell (h : Inv D) (B : Block Y n)
    (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : AgeOneFacet D B hB f) :
    (proposedSibling D B hB f a).cell n (a.record.incidence.val.sideFacet (!a.record.sideIndex)).val =
      B.node.cell n f.val := by
  classical
  let N := proposedParent D B hB
  let T : E d → E d := fun x => N.frame ((S.σ ^ n) x)
  have hA := ageOneFacet_semantics_step2_internal D h B hB f a
  have hfacet : a.record.facet.val = f.val := by
    have hr := a.readout
    unfold stateRecordAt at hr
    split at hr
    next hf =>
      exact ((D.blockState B hB).facetRecord_valid
        ⟨f.val, hf⟩ a.record hr).2
    next hf => contradiction
  have hrole : a.record.servingRole = firstRole D B hB := hA.2.1
  have hgeo := hA.2.2.1
  rw [hrole, hfacet] at hgeo
  have hc (A : S.ι) (i : S.I A) (e : Cell d) :
      (⟨(S.child A i).ty, (S.placeChild n i).trans N.frame⟩ :
        FramedNode S).cell n e =
      T '' placedSet (S.child A i).frame e.carrier := by
    change (fun x : E d =>
      N.frame (S.placeChild n i ((S.σ ^ n) x))) '' e.carrier =
      T '' ((S.child A i).frame '' e.carrier)
    rw [Set.image_image]
    congr 1
    funext x
    exact congrArg N.frame
      (incidentForest_step1_placeChild_pow i n x)
  have hp (b : Bool) :
      placedSet
        (S.child a.record.incidence.val.ty
          (a.record.incidence.val.sideIndex b)).frame
        (a.record.incidence.val.sideFacet b).val.carrier =
      a.record.incidence.val.positioned := by
    cases b with
    | false => rfl
    | true => exact a.record.incidence.val.paired.symm
  calc (proposedSibling D B hB f a).cell n ((a.record.incidence.val.sideFacet (!a.record.sideIndex)).val)
    _ = T '' placedSet (S.child a.record.incidence.val.ty (a.record.incidence.val.sideIndex (!a.record.sideIndex))).frame (a.record.incidence.val.sideFacet (!a.record.sideIndex)).val.carrier := hc _ _ _
    _ = T '' a.record.incidence.val.positioned := congrArg (fun K : Set (E d) => T '' K) (hp _)
    _ = T '' placedSet (S.child (firstRole D B hB).1 (firstRole D B hB).2).frame f.val.carrier := congrArg (fun K : Set (E d) => T '' K) hgeo
    _ = (⟨(S.child (firstRole D B hB).1 (firstRole D B hB).2).ty, (S.placeChild n (firstRole D B hB).2).trans N.frame⟩ : FramedNode S).cell n f.val := (hc _ _ _).symm
    _ = (N.child n (firstRole D B hB).2).cell n f.val := rfl
    _ = B.node.cell n f.val := congrArg (fun M : FramedNode S => M.cell n f.val) (proposedParent_child D h B hB)

theorem ageOneFacet_semantics (h : Inv D) (B : Block Y n)
    (hB : B ∈ D.geometry.blocks) (f : FacetName S B.node.ty)
    (a : AgeOneFacet D B hB f) :
    AgeOneRecord (D.blockState B hB) a.record ∧
      a.record.incidence.val.ty = (proposedParent D B hB).ty ∧
      a.record.servingRole = firstRole D B hB ∧
      (proposedSibling D B hB f a).cell n
        (a.record.incidence.val.sideFacet (!a.record.sideIndex)).val =
          B.node.cell n f.val := by
  exact ⟨ageOneFacet_semantics_step2_internal D h B hB f a,
         (ageOneFacet_semantics_step3_types D h B hB f a).1,
         (ageOneFacet_semantics_step3_types D h B hB f a).2,
         ageOneFacet_semantics_step4_cell D h B hB f a⟩

/-- R5/R7, V4 3.4 (second clause), 3.7: an assembled parent before its state
is defined. Every prescribed child is a level-n block and has the correct first
address letter. This is geometry and old state data, not a new parent invariant. -/
structure AssembledParent (N : FramedNode S) where
  /-- R5/R7, V4 3.4, 3.7: each prescribed child as an actual chosen block. -/
  children : S.I N.ty → {B : Block Y n // B ∈ D.geometry.blocks}
  /-- R5/R7, V4 3.4, 3.7: exact child types and frames. -/
  child_eq : ∀ i, (children i).val.node = N.child n i
  /-- R5/R7, V4 3.4, 3.7: the old child state proposes precisely this role. -/
  first_letters : ∀ i, firstRole D (children i).val (children i).property = ⟨N.ty, i⟩

namespace AssembledParent

variable {D} {N : FramedNode S} (A : AssembledParent D N)

include A

/-- R7, V4 3.7: all actual child subdivisions combine to the parent's native subdivision. -/
theorem actual : IsBlock Y (n + 1) N := by
  intro w
  rcases w with ⟨i, w_child⟩
  have h_child_eq := A.child_eq i
  have h1 : (S.nativeTile N.ty (n + 1) ⟨i, w_child⟩).move N.frame = (S.nativeTile (S.child N.ty i).ty n w_child).move (N.child n i).frame := by
    apply FramedNode.ext
    · rfl
    · ext x : 1
      dsimp [SubstSystem.nativeTile, SubstSystem.descendantNode, FramedNode.child, FramedNode.move]
      rw [Nat.zero_add]
  have h_actual := (A.children i).val.actual
  revert h_actual
  generalize h_node : (A.children i).val.node = node
  rw [h_node] at h_child_eq
  subst h_child_eq
  intro h_actual
  have h_actual_inst := h_actual w_child
  rcases h_actual_inst with ⟨t, ht, ht_eq⟩
  use t, ht
  rw [h1]
  exact ht_eq

/-- R7, V4 3.7: the assembled framed parent, regarded as a genuine height-(n+1) block. -/
def block : Block Y (n + 1) := ⟨N, A.actual⟩

/-- R7, V4 3.7: every chosen child proposes this same parent, including its frame. -/
theorem parent_eq (i : S.I N.ty) :
    proposedParent D (A.children i).val (A.children i).property = N := by
  have hl := A.first_letters i
  have hc := A.child_eq i
  dsimp [proposedParent]
  dsimp [FramedNode.child] at hc
  rw [hl]
  dsimp
  have h_frame := congrArg FramedNode.frame hc
  dsimp at h_frame
  apply FramedNode.ext
  · rfl
  · rw [h_frame]
    dsimp
    rw [AffineIsometryEquiv.trans_assoc]
    rw [AffineIsometryEquiv.symm_trans_self]
    rw [AffineIsometryEquiv.refl_trans]


/-- R7, V4 3.7: the parent is the union of its chosen children. -/
theorem union_children :
    N.carrier (n + 1) = ⋃ i : S.I N.ty, (A.children i).val.carrier := by
  have hc : ∀ i, (A.children i).val.carrier = (N.child n i).carrier n := by
    intro i
    change (A.children i).val.node.carrier n = _
    rw [A.child_eq i]
  have hpar : N.carrier (n+1) = N.prototypeFrame n '' S.supertile 1 N.ty := by
    simp only [FramedNode.carrier, FramedNode.prototypeFrame, SubstSystem.supertile,
      placedSet, Set.image_image, pow_one]
    congr 1
  have hfr : ∀ i, (N.child n i).prototypeFrame n =
      (S.child N.ty i).frame.toAffineEquiv.trans (N.prototypeFrame n) := by
    intro i
    apply AffineEquiv.ext; intro x
    change N.frame (S.placeChild n i ((S.σ ^ n) x)) =
      N.frame ((S.σ ^ n) ((S.child N.ty i).frame x))
    congr 1
    rw [S.placeChild_apply]
    simp [linearConj, Child.frame, rigidMotion, zpow_neg,
      LinearEquiv.mul_apply, ← map_add]
  have hci : ∀ M : FramedNode S, M.carrier n = M.prototypeFrame n '' (S.proto M.ty).carrier := by
    intro M
    simp only [FramedNode.carrier, FramedNode.prototypeFrame, SubstSystem.supertile,
      placedSet, Set.image_image]
    rfl
  have hch : ∀ i, (N.child n i).carrier n = N.prototypeFrame n ''
      placedSet (S.child N.ty i).frame (S.proto (S.child N.ty i).ty).carrier := by
    intro i
    rw [hci, hfr]
    simp only [placedSet, Set.image_image]
    rfl
  rw [hpar]
  simp_rw [hc]
  change N.prototypeFrame n '' (S.σ '' (S.proto N.ty).carrier) = _
  rw [S.children_cover, Set.image_iUnion]
  exact Set.iUnion_congr (fun i => (hch i).symm)

end AssembledParent

end Parser

end Enforce
