import Enforce.Substitution

/-!
# Tile-faithful tilings, species, honest hierarchies and scale transfer

DEVIATION: placed tiles store their type and geometric carrier, with an existence
proof of an isometric frame. Frames are separate data on hierarchy nodes. This is
the typed-carrier quotient of pairs `(A, φ)` by equality of placed carriers, as in
V4's tile-faithful convention. It avoids imposing arbitrary choices of symmetric
tile frames on legality or on the ground level of a hierarchy.

Scale transfer is expressed by an equivalence of the entire surviving tails of
two hierarchies. Exact frame, type, role and parent equalities preserve all data
expressed in prototype coordinates; the coordinate equality holds for every set.
-/

open Set

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)]

/-- T1, V4 §1.0 (H7): a typed placed carrier.
DEVIATION: the isometric frame is existential rather than part of tile identity;
different frames of the same typed carrier represent the same physical tile. -/
@[ext]
structure PlacedTile (S : SubstSystem d) where
  /-- T1, V4 §1.0 (H7): the type remains part of the tile, even for congruent types. -/
  ty : S.ι
  /-- T1, V4 §1.0 (H7): the actual closed tile in Euclidean space. -/
  carrier : Set (E d)
  /-- T1, V4 §1.0 (H7): the tile is an isometric copy of its prototype. -/
  isometric : ∃ φ : Iso d, carrier = placedSet φ (S.proto ty).carrier

namespace PlacedTile

variable {S : SubstSystem d}

/-- T1, V4 §1.0 (H7): forget the frame of a typed isometric placement. -/
def ofFrame (A : S.ι) (φ : Iso d) : PlacedTile S :=
  ⟨A, placedSet φ (S.proto A).carrier, ⟨φ, rfl⟩⟩

/-- T1, V4 §1.0, Frames: choose a representative frame when needed.
The frame exists by the tile's defining field; it is never used as tile identity. -/
def frame (t : PlacedTile S) : Iso d := Classical.choose t.isometric

/-- T1, V4 §1.0, Frames: the representative frame realizes the carrier. -/
theorem frame_carrier (t : PlacedTile S) :
    t.carrier = placedSet t.frame (S.proto t.ty).carrier :=
  Classical.choose_spec t.isometric

/-- T1, V4 §1.0 (H7): apply a common Euclidean isometry to a tile. -/
def move (t : PlacedTile S) (g : Iso d) : PlacedTile S :=
  ofFrame t.ty (t.frame.trans g)

/-- T1, V4 §1.0 (H7): moving a tile acts geometrically on its carrier. -/
theorem move_carrier (t : PlacedTile S) (g : Iso d) :
    (t.move g).carrier = g '' t.carrier := by
  sorry

end PlacedTile

/-- T1/S2, V4 §1.0 (H3), (H7): forget the frame of a ground-level node. -/
def FramedNode.toTile {S : SubstSystem d} (N : FramedNode S) : PlacedTile S :=
  PlacedTile.ofFrame N.ty N.frame

/-- T1, V4 §1.0 (H7): a whole-space tiling, retaining its typed partition.
No local finiteness, side-to-side condition or finite local complexity is assumed. -/
structure Tiling (S : SubstSystem d) where
  /-- T1, V4 §1.0 (H7): the set of physical tiles. -/
  tiles : Set (PlacedTile S)
  /-- T1, V4 §1.0 (H7): every point is covered. -/
  cover : ∀ x : E d, ∃ t ∈ tiles, x ∈ t.carrier
  /-- T1, V4 §1.0 (H7): distinct tiles have disjoint interiors. -/
  disjoint : tiles.PairwiseDisjoint (fun t => interior t.carrier)

namespace Tiling

variable {S : SubstSystem d} (T : Tiling S) (g : Iso d)

/-- T1, V4 §1.0 (H7): isometrically moved physical tiles still cover space. -/
theorem move_cover : ∀ x : E d,
    ∃ t ∈ (fun t : PlacedTile S => t.move g) '' T.tiles, x ∈ t.carrier := by
  sorry

/-- T1, V4 §1.0 (H7): isometric motion preserves disjoint tile interiors. -/
theorem move_disjoint :
    ((fun t : PlacedTile S => t.move g) '' T.tiles).PairwiseDisjoint
      (fun t => interior t.carrier) := by
  sorry

/-- T1, V4 §1.0 (H7): the action of all Euclidean isometries on physical tilings. -/
def move : Tiling S where
  tiles := (fun t : PlacedTile S => t.move g) '' T.tiles
  cover := T.move_cover g
  disjoint := T.move_disjoint g

end Tiling

/-- T1, V4 §1.0 (H7): a finite patch of nonoverlapping typed tiles. -/
structure Patch (S : SubstSystem d) where
  /-- T1, V4 §1.0 (H7): the finite collection of tiles. -/
  tiles : Finset (PlacedTile S)
  /-- T1, V4 §1.0 (H7): the interiors are pairwise disjoint. -/
  disjoint : (tiles : Set (PlacedTile S)).PairwiseDisjoint (fun t => interior t.carrier)

namespace Patch

variable {S : SubstSystem d}

/-- T1, V4 §1.0 (H7): the union of a patch's closed carriers. -/
def support (P : Patch S) : Set (E d) := ⋃ t ∈ P.tiles, t.carrier

/-- T1, V4 §1.0 (H7): a finite patch of a specified whole-space tiling. -/
def IsPatchOf (P : Patch S) (T : Tiling S) : Prop :=
  (P.tiles : Set (PlacedTile S)) ⊆ T.tiles

end Patch

/-- T2, V4 §1.0 (H7): legality by occurrence among the native tiles of some
standard supertile. Occurrence compares physical typed carriers, not frame choices. -/
def IsLegal {S : SubstSystem d} (P : Patch S) : Prop :=
  ∃ (n : ℕ) (A : S.ι) (ψ : Iso d), ∀ t ∈ P.tiles,
    ∃ w : S.RoleWord A n, t.move ψ = (S.nativeTile A n w).toTile

/-- T2, V4 §1.0 (H7): native occurrence strictly inside a standard supertile.
The containment concerns the union of the closed tiles, including their boundaries. -/
def InteriorLegal {S : SubstSystem d} (P : Patch S) : Prop :=
  ∃ (n : ℕ) (A : S.ι) (ψ : Iso d),
    (∀ t ∈ P.tiles, ∃ w : S.RoleWord A n, t.move ψ = (S.nativeTile A n w).toTile) ∧
      ψ '' P.support ⊆ interior (S.supertile n A)

/-- T2, V4 §1.0 (H7): the species is defined, rather than supplied as an
extra hypothesis. Its members are exactly the tilings with interior-legal patches. -/
def SubstSystem.Species (S : SubstSystem d) : Set (Tiling S) :=
  {T | ∀ P : Patch S, P.IsPatchOf T → InteriorLegal P}

/-- T3, V4 7.4: ordinary legality and interior legality give exactly the
same whole-space species. The equivalence is asserted for all finite patches of
a tiling, rather than incorrectly for an isolated finite patch. -/
theorem species_eq_legal {S : SubstSystem d} (T : Tiling S) :
    T ∈ S.Species ↔ ∀ P : Patch S, P.IsPatchOf T → IsLegal P := by
  sorry

/-- T2, V4 §1.0 (H7): the defined species is invariant under every Euclidean
isometry, including reflections. This does not impose covariance on a chosen lift. -/
theorem species_move_iff {S : SubstSystem d} (T : Tiling S) (g : Iso d) :
    T.move g ∈ S.Species ↔ T ∈ S.Species := by
  sorry

/-- T4, V4 §1.0 (H7): a point is in the interior of a physical tile. -/
def Tiling.IsTileInterior {S : SubstSystem d} (T : Tiling S) (x : E d) : Prop :=
  ∃ t ∈ T.tiles, x ∈ interior t.carrier

/-- T4, V4 §1.0 (H7): type on tile interiors and the single value `none = @`
on the entire boundary skeleton. Interior disjointness makes the choice independent. -/
def oldMarking {S : SubstSystem d} (T : Tiling S) (x : E d) : Option S.ι := by
  classical
  exact if h : ∃ t ∈ T.tiles, x ∈ interior t.carrier then
    some (Classical.choose h).ty else none

/-- T4, V4 §1.0 (H7): the old marking on each tile interior. -/
theorem oldMarking_interior {S : SubstSystem d} (T : Tiling S)
    (t : PlacedTile S) (ht : t ∈ T.tiles) (x : E d) (hx : x ∈ interior t.carrier) :
    oldMarking T x = some t.ty := by
  sorry

/-- T4, V4 §1.0 (H7): a point on any tile boundary receives `@`. -/
theorem oldMarking_frontier {S : SubstSystem d} (T : Tiling S)
    (t : PlacedTile S) (ht : t ∈ T.tiles) (x : E d) (hx : x ∈ frontier t.carrier) :
    oldMarking T x = none := by
  sorry

/-- T5, V4 §1.0, Hierarchies and Frames: a coherent hierarchy on a whole-space
tiling. The definition deliberately does not require membership in the source
species: proper outputs also carry hierarchies and need not belong to the species. -/
structure CoherentHierarchy (S : SubstSystem d) (T : Tiling S) where
  /-- T5, V4 §1.0: the framed nodes at every height. -/
  nodes : ℕ → Set (FramedNode S)
  /-- T5, V4 §1.0: height zero is exactly the given physical tiling. -/
  ground : {t | ∃ N ∈ nodes 0, N.toTile = t} = T.tiles
  /-- T5, V4 §1.0: each level covers Euclidean space. -/
  cover : ∀ n x, ∃ N ∈ nodes n, x ∈ N.carrier n
  /-- T5, V4 §1.0: different framed nodes of the same height have disjoint interiors. -/
  disjoint : ∀ n, (nodes n).PairwiseDisjoint (fun N => interior (N.carrier n))
  /-- T5, V4 §1.0: a parent for every node, at the next height. -/
  parent : ∀ n, {N // N ∈ nodes n} → {P // P ∈ nodes (n + 1)}
  /-- T5, V4 §1.0: the actual child role in that parent's substitution. -/
  role : ∀ n N, S.I (parent n N).val.ty
  /-- T5, V4 §1.0, Frames: exact frame and type compatibility. -/
  child_eq : ∀ n N, N.val = (parent n N).val.child n (role n N)
  /-- T5, V4 §1.0: all prescribed children of a parent occur at the lower level. -/
  children_mem : ∀ n P, P ∈ nodes (n + 1) →
    ∀ i : S.I P.ty, P.child n i ∈ nodes n
  /-- T5, V4 §1.0: a node belongs to only one parent. -/
  parent_unique : ∀ n N P, P ∈ nodes (n + 1) →
    (∃ i : S.I P.ty, N.val = P.child n i) → P = (parent n N).val
  /-- T5, V4 §1.0: physical tiles contained in a node are exactly its native tiles. -/
  native_tiles : ∀ n N, N ∈ nodes n →
    {t | t ∈ T.tiles ∧ t.carrier ⊆ N.carrier n} =
      {t | ∃ w : S.RoleWord N.ty n, ((S.nativeTile N.ty n w).move N.frame).toTile = t}

namespace CoherentHierarchy

variable {S : SubstSystem d} {T : Tiling S} (H : CoherentHierarchy S T)

/-- T5, V4 §1.0: nodes at arbitrary heights, retaining their membership proof. -/
abbrev Node := Σ n : ℕ, {N // N ∈ H.nodes n}

/-- T5, V4 §1.0: the parent map on the union of all levels. -/
def parentNode (q : H.Node) : H.Node := ⟨q.1 + 1, H.parent q.1 q.2⟩

/-- T5, V4 §1.0 (H3): a node's role, including its parent's type. -/
def nodeRole (q : H.Node) : S.Role :=
  ⟨(H.parent q.1 q.2).val.ty, H.role q.1 q.2⟩

/-- T6, V4 1.0(d): every fixed level is locally finite and meets bounded
sets in finitely many nodes. Closed supports, rather than interiors, are counted. -/
theorem nodes_locallyFinite (n : ℕ) :
    LocallyFinite (fun N : {N // N ∈ H.nodes n} => N.val.carrier n) ∧
      ∀ B : Set (E d), Bornology.IsBounded B →
        {N : {N // N ∈ H.nodes n} | (B ∩ N.val.carrier n).Nonempty}.Finite := by
  sorry

/-- T6, V4 1.0(d): a node is the union of the physical tiles it contains. -/
theorem node_union_tiles (n : ℕ) (N : FramedNode S) (hN : N ∈ H.nodes n) :
    N.carrier n = ⋃ t ∈ {t | t ∈ T.tiles ∧ t.carrier ⊆ N.carrier n}, t.carrier := by
  sorry

/-- T6, V4 §1.0, Hierarchies: same-height nodes sharing an interior point
coincide as framed nodes, including their type and isometric frame. -/
theorem same_height_disjoint (n : ℕ) (N P : FramedNode S)
    (hN : N ∈ H.nodes n) (hP : P ∈ H.nodes n) (x : E d)
    (hxN : x ∈ interior (N.carrier n)) (hxP : x ∈ interior (P.carrier n)) :
    N = P := by
  sorry

end CoherentHierarchy

namespace SubstSystem

variable (S : SubstSystem d)

/-- T7/S2, V4 1.11(i): a framed node of height `h` in the standard hierarchy
of `σ^n A`. The address and complete isometric frame are retained. -/
def IsStandardNode (A : S.ι) (n h : ℕ) (N : FramedNode S) : Prop :=
  ∃ depth : ℕ, n = h + depth ∧
    ∃ w : S.RoleWord A depth, N = S.descendantNode A h depth w

end SubstSystem

/-- T7, V4 1.11(i): an interior legal context for a finite set of nodes,
possibly of different heights. Matching the full framed standard nodes and their
child equations preserves roles and parents wherever both endpoints are selected. -/
structure LegalContext {S : SubstSystem d} {T : Tiling S}
    (H : CoherentHierarchy S T) (F : Finset H.Node) where
  /-- T7, V4 1.11(i): height of the containing standard supertile. -/
  height : ℕ
  /-- T7, V4 1.11(i): its type. -/
  ty : S.ι
  /-- T7, V4 1.11(i): a single isometry for the entire finite configuration. -/
  placement : Iso d
  /-- T7, V4 1.11(i): exact framed occurrence in the standard hierarchy. -/
  standard : ∀ q ∈ F,
    S.IsStandardNode ty height q.1 (q.2.val.move placement)
  /-- T7, V4 1.11(i): closed supports lie strictly inside the context. -/
  interior : ∀ q ∈ F,
    placement '' q.2.val.carrier q.1 ⊆ _root_.interior (S.supertile height ty)
  /-- T7, V4 1.11(i): child equations, with the original roles and parents. -/
  edges : ∀ q ∈ F, H.parentNode q ∈ F →
    q.2.val.move placement =
      ((H.parent q.1 q.2).val.move placement).child q.1 (H.role q.1 q.2)

/-- T7, V4 1.11: an honest source, including the common frame coset.
No nonemptiness of the species is postulated. Lemma `exists_honest` supplies
an honest source over each actual member of the species. -/
structure HonestSource (S : SubstSystem d) where
  /-- T7, V4 1.11: the underlying physical source tiling. -/
  tiling : Tiling S
  /-- T7, V4 1.11: source legality. -/
  mem_species : tiling ∈ S.Species
  /-- T7, V4 1.11: the chosen coherent hierarchy. -/
  hierarchy : CoherentHierarchy S tiling
  /-- T7, V4 1.11(i): every finite node set has a legal framed context. -/
  contexts : ∀ F : Finset hierarchy.Node, Nonempty (LegalContext hierarchy F)
  /-- T7, V4 1.11(ii): one common coset representative. -/
  coset : Ortho d
  /-- T7, V4 1.11(ii): all orthogonal node frames lie in that coset. -/
  frames_in_coset : ∀ n N, N ∈ hierarchy.nodes n →
    ∃ R ∈ S.rotGroup, N.frame.linearIsometryEquiv = coset * R

/-- T8, V4 1.12: every member of the species has an honest hierarchy.
Existence is conditional only on actual membership in the defined species;
the underlying tiling is preserved exactly, with its typed physical tiles. -/
theorem exists_honest {S : SubstSystem d} (T : Tiling S) (hT : T ∈ S.Species) :
    ∃ U : HonestSource S, U.tiling = T := by
  sorry

namespace HonestSource

variable {S : SubstSystem d} (U : HonestSource S)

/-- T9, V4 1.13: the ambient expansion `Λ = Q σ Q⁻¹` for this frame coset. -/
def expansion : E d ≃ₗ[ℝ] E d :=
  U.coset.toLinearEquiv * S.σ * U.coset.symm.toLinearEquiv

end HonestSource

namespace CoherentHierarchy

variable {S : SubstSystem d} {T : Tiling S} (H : CoherentHierarchy S T)

/-- T9, V4 1.13: all nodes at or above a retained level. -/
abbrev Tail (a : ℕ) := {q : H.Node // a ≤ q.1}

/-- T9, V4 1.13: the parent remains in the retained tail. -/
def tailParent (a : ℕ) (q : H.Tail a) : H.Tail a :=
  ⟨H.parentNode q.val, Nat.le_trans q.property (Nat.le_succ _)⟩

end CoherentHierarchy

/-- T9, V4 1.13(a)--(c): exact correspondence of the surviving hierarchy tails.
Levels `a+r` and `b+r` correspond under `J ∘ Λ^(b-a)`. The separate fields give
literal equalities for types, frames, roles and parents. Pullback equality for
every ambient set also preserves cells, cones, strata and provider geometry in
prototype coordinates; provider ages follow from the parent and height equalities.
DEVIATION: the catch-all data clause is encoded by these explicit equalities,
rather than by fields naming providers and strata before those objects are defined.
The universal prototype-set equality and the full tail bijection retain its content. -/
structure ScaleTailEquiv {S : SubstSystem d} (U V : HonestSource S)
    (a b : ℕ) (J : Iso d) where
  /-- T9, V4 1.13: a bijection of all surviving nodes, not just one branch. -/
  toEquiv : U.hierarchy.Tail a ≃ V.hierarchy.Tail b
  /-- T9, V4 1.13: all heights shift by exactly `b-a`. -/
  heights : ∀ q, (toEquiv q).val.1 + a = q.val.1 + b
  /-- T9, V4 1.13(c): corresponding types are equal. -/
  types : ∀ q, (toEquiv q).val.2.val.ty = q.val.2.val.ty
  /-- T9, V4 1.13(c): equality of the full affine prototype frames. -/
  frames : ∀ q,
    (toEquiv q).val.2.val.prototypeFrame (toEquiv q).val.1 =
      (q.val.2.val.prototypeFrame q.val.1).trans
        (((U.expansion ^ ((b : ℤ) - (a : ℤ))).toAffineEquiv).trans J.toAffineEquiv)
  /-- T9, V4 1.13(c): corresponding parent nodes are equal under the bijection. -/
  parents : ∀ q,
    toEquiv (U.hierarchy.tailParent a q) = V.hierarchy.tailParent b (toEquiv q)
  /-- T9, V4 1.13(c): roles agree, including their parent type. -/
  roles : ∀ q, V.hierarchy.nodeRole (toEquiv q).val = U.hierarchy.nodeRole q.val
  /-- T9, V4 1.13(c): literal preservation of every set in prototype coordinates. -/
  prototype_sets : ∀ q (K : Set (E d)),
    ((toEquiv q).val.2.val.prototypeFrame (toEquiv q).val.1).symm ''
        (J '' ((U.expansion ^ ((b : ℤ) - (a : ℤ))) '' K)) =
      (q.val.2.val.prototypeFrame q.val.1).symm '' K

/-- T9, V4 1.13(a): inflation by `Λ`, with new native ground tiles, remains
honest. Every old node becomes a node one level higher, with exact framed data.
The target's coherent native-tile condition prescribes the ground subdivision. -/
theorem inflate {S : SubstSystem d} (U : HonestSource S) :
    ∃ V : HonestSource S,
      Nonempty (ScaleTailEquiv U V 0 1 (AffineIsometryEquiv.refl ℝ (E d))) := by
  sorry

/-- T9, V4 1.13(b): for every positive `j`, coarsening the height-`j` nodes
by `Λ⁻ʲ` gives an honest source and exactly its inherited hierarchy. -/
theorem coarsen {S : SubstSystem d} (U : HonestSource S) (j : ℕ) (hj : 1 ≤ j) :
    ∃ V : HonestSource S,
      Nonempty (ScaleTailEquiv U V j 0 (AffineIsometryEquiv.refl ℝ (E d))) := by
  sorry

/-- T9, V4 1.13(c): transfer any node to any specified nonnegative height,
preserving the entire surviving hierarchy and all prototype-frame data.
An arbitrary common isometry `J` is included, so any congruent final placement
is available. Nonemptiness is supplied by the original honest source. -/
theorem exactScaleTransfer {S : SubstSystem d} (U : HonestSource S)
    (m : ℕ) (N : FramedNode S) (hN : N ∈ U.hierarchy.nodes m) (n : ℕ) (J : Iso d) :
    ∃ V : HonestSource S,
      ∃ e : ScaleTailEquiv U V (m - n) (n - m) J,
        ∃ N' : {N // N ∈ V.hierarchy.nodes n},
          e.toEquiv ⟨⟨m, ⟨N, hN⟩⟩, Nat.sub_le m n⟩ =
            ⟨⟨n, N'⟩, Nat.sub_le n m⟩ := by
  sorry

/-- T9, V4 1.13(c): congruent height shifts preserve all height residues.
The same statement applies to every pair of corresponding nodes of a transfer. -/
theorem ScaleTailEquiv.residues {S : SubstSystem d} {U V : HonestSource S}
    {a b : ℕ} {J : Iso d} (e : ScaleTailEquiv U V a b J)
    (L : ℕ) (hL : 0 < L) (hab : a % L = b % L) (q : U.hierarchy.Tail a) :
    (e.toEquiv q).val.1 % L = q.val.1 % L := by
  sorry

end Enforce
