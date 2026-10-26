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

/-- Step 1 of the V4 proof of `exists_honest` (V4 1.12):
"a prototile has finitely many frames onto a given placed copy". -/
private theorem exists_honest_step1_frames_finite
    (A : PolyManifoldDomain d) (K : Set (E d)) :
    {φ : Iso d | placedSet φ A.carrier = K}.Finite := by
  classical
  by_cases h : ∃ φ : Iso d, placedSet φ A.carrier = K
  · obtain ⟨φ₀, hφ₀⟩ := h
    have hfin := (polyhedron_symmetries_finite A.carrier A.polyhedral
      A.interior_nonempty).image (fun s : Iso d => s.trans φ₀)
    apply hfin.subset
    intro φ hφ
    refine ⟨φ.trans φ₀.symm, ?_, ?_⟩
    · change (φ₀.symm ∘ φ) '' A.carrier = A.carrier
      rw [Set.image_comp, show φ '' A.carrier = K from hφ, ← hφ₀]
      change φ₀.symm '' (φ₀ '' A.carrier) = A.carrier
      rw [← Set.image_comp]
      convert Set.image_id A.carrier using 1
      congr 1
      funext x
      exact φ₀.symm_apply_apply x
    · apply AffineIsometryEquiv.ext
      intro x
      exact φ₀.apply_symm_apply (φ x)
  · have he : {φ : Iso d | placedSet φ A.carrier = K} = ∅ := by
      ext φ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hφ => h ⟨φ, hφ⟩
    rw [he]
    exact Set.finite_empty

/-- A possible height-`n` ancestor of the physical tile `t`, including its frame. -/
private def exists_honest_candidates {S : SubstSystem d}
    (t : PlacedTile S) (n : ℕ) : Set (FramedNode S) :=
  {N | ∃ w : S.RoleWord N.ty n,
    ((S.nativeTile N.ty n w).move N.frame).toTile = t}

/-- Step 2 of the V4 proof of `exists_honest` (V4 1.12):
"a candidate is determined by a role word of length m ... and a frame of t". -/
private theorem exists_honest_step2_candidates_finite {S : SubstSystem d}
    (t : PlacedTile S) (n : ℕ) : (exists_honest_candidates t n).Finite := by
  classical
  let f : (a : Σ A : S.ι, S.RoleWord A n) → Iso d → FramedNode S :=
    fun a φ => ⟨a.1, (S.nativeTile a.1 n a.2).frame.symm.trans φ⟩
  have hfin : (⋃ a : Σ A : S.ι, S.RoleWord A n,
      f a '' {φ : Iso d |
        placedSet φ (S.proto (S.nativeTile a.1 n a.2).ty).carrier = t.carrier}).Finite :=
    Set.finite_iUnion fun a =>
      (exists_honest_step1_frames_finite
        (S.proto (S.nativeTile a.1 n a.2).ty) t.carrier).image (f a)
  apply hfin.subset
  rintro N ⟨w, hw⟩
  apply Set.mem_iUnion.mpr
  refine ⟨⟨N.ty, w⟩, ?_⟩
  refine ⟨(S.nativeTile N.ty n w).frame.trans N.frame, ?_, ?_⟩
  · exact congrArg PlacedTile.carrier hw
  · simp [f, AffineIsometryEquiv.trans_assoc]

/-- Step 3 of the V4 proof of `exists_honest` (V4 1.12):
"Each variable has finitely many values and every finite subfamily of constraints
is satisfiable; by the compactness ... principle ... there is a global assignment".
Here a constraint indexed by `F` depends only on the coordinates in `F`. -/
private theorem exists_honest_step3_compactness
    {ι : Type*} {α : ι → Type*} [∀ i, Finite (α i)]
    (C : Finset ι → (∀ i, α i) → Prop)
    (hdep : ∀ F, DependsOn (C F) (F : Set ι))
    (hmono : ∀ F G, F ⊆ G → ∀ a, C G a → C F a)
    (hfin : ∀ F, ∃ a, C F a) :
    ∃ a, ∀ F, C F a := by
  classical
  letI : ∀ i, TopologicalSpace (α i) := fun _ => ⊥
  letI : ∀ i, DiscreteTopology (α i) := fun _ => ⟨rfl⟩
  have hclosed : ∀ F, IsClosed {a : ∀ i, α i | C F a} := by
    intro F
    obtain ⟨g, hg⟩ := dependsOn_iff_exists_comp.mp (hdep F)
    rw [hg]
    exact (isClosed_discrete {a | g a}).preimage (Pi.continuous_restrict _)
  obtain ⟨a, ha⟩ := CompactSpace.iInter_nonempty hclosed (fun Fs => by
    obtain ⟨a, ha⟩ := hfin (Fs.biUnion id)
    refine ⟨a, Set.mem_iInter.mpr fun F => Set.mem_iInter.mpr fun hF => ?_⟩
    exact hmono F (Fs.biUnion id) (Finset.subset_biUnion_of_mem id hF) a ha)
  exact ⟨a, fun F => Set.mem_iInter.mp ha F⟩

/-- Step 4 of the V4 proof of `exists_honest` (V4 1.12):
"the positioned m-ancestor of t ... [has] the role word ... down to t".
A native leaf is contained in the carrier of its ancestor. -/
private theorem exists_honest_step4_native_subset {S : SubstSystem d}
    (N : FramedNode S) (n : ℕ) (w : S.RoleWord N.ty n) :
    ((S.nativeTile N.ty n w).move N.frame).toTile.carrier ⊆ N.carrier n := by
  have h := Set.subset_iUnion (fun v : S.RoleWord N.ty n =>
    (S.nativeTile N.ty n v).carrier 0) w
  rw [S.native_cover N.ty n] at h
  have h' : placedSet (S.nativeTile N.ty n w).frame
      (S.proto (S.nativeTile N.ty n w).ty).carrier ⊆ S.supertile n N.ty := by
    simpa [FramedNode.carrier, SubstSystem.supertile, placedSet] using h
  change (N.frame ∘ (S.nativeTile N.ty n w).frame) ''
    (S.proto (S.nativeTile N.ty n w).ty).carrier ⊆ N.frame '' S.supertile n N.ty
  rw [Set.image_comp]
  exact Set.image_mono h'

/-- Step 5 of the V4 proof of `exists_honest` (V4 1.12):
"children of a recorded node are recorded nodes (the recorded ancestors of the
tiles it contains)". Each prescribed child contains a native physical tile. -/
private theorem exists_honest_step5_child_tile {S : SubstSystem d}
    (T : Tiling S) (n : ℕ) (N : FramedNode S)
    (hnative : {t | t ∈ T.tiles ∧ t.carrier ⊆ N.carrier (n + 1)} =
      {t | ∃ w : S.RoleWord N.ty (n + 1),
        ((S.nativeTile N.ty (n + 1) w).move N.frame).toTile = t})
    (i : S.I N.ty) :
    ∃ t : T.tiles, t.val.carrier ⊆ (N.child n i).carrier n := by
  have hne : (S.supertile n (S.child N.ty i).ty).Nonempty :=
    ((S.proto (S.child N.ty i).ty).interior_nonempty.mono interior_subset).image (S.σ ^ n)
  rw [← S.native_cover (S.child N.ty i).ty n, Set.nonempty_iUnion] at hne
  obtain ⟨w, _⟩ := hne
  let t := ((S.nativeTile (S.child N.ty i).ty n w).move (N.child n i).frame).toTile
  have ht : ((S.nativeTile N.ty (n + 1) ⟨i, w⟩).move N.frame).toTile = t := by
    simp [t, SubstSystem.nativeTile, SubstSystem.descendantNode, FramedNode.move,
      FramedNode.child, ← AffineIsometryEquiv.trans_assoc]
  have hmem : t ∈ T.tiles := by
    have : t ∈ {t | ∃ w : S.RoleWord N.ty (n + 1),
        ((S.nativeTile N.ty (n + 1) w).move N.frame).toTile = t} := ⟨⟨i, w⟩, ht⟩
    rw [← hnative] at this
    exact this.1
  exact ⟨⟨t, hmem⟩, exists_honest_step4_native_subset (N.child n i) n w⟩

/-- The finite constraints C1--C3 of V4 1.12. All occurrences of `a` are at
indices in `F`; in particular, no conditions on unselected tiles are imposed.
The child-containment clause makes the fullness of the subdivision explicit. -/
private def exists_honest_constraints {S : SubstSystem d} (T : Tiling S)
    (t₀ : T.tiles) (F : Finset (T.tiles × ℕ))
    (a : T.tiles × ℕ → FramedNode S) : Prop :=
  (∀ x ∈ F,
    {t | t ∈ T.tiles ∧ t.carrier ⊆ (a x).carrier x.2} =
      {t | ∃ w : S.RoleWord (a x).ty x.2,
        ((S.nativeTile (a x).ty x.2 w).move (a x).frame).toTile = t}) ∧
  (∀ x ∈ F, ∀ y ∈ F, x.2 = y.2 → a x ≠ a y →
    Disjoint (interior ((a x).carrier x.2)) (interior ((a y).carrier y.2))) ∧
  (∀ t n, (t, n) ∈ F → (t, n + 1) ∈ F →
    ∃ i : S.I (a (t, n + 1)).ty, a (t, n) = (a (t, n + 1)).child n i) ∧
  (∀ t u n, (t, n) ∈ F → (t, n + 1) ∈ F → (u, n + 1) ∈ F →
    (∃ i : S.I (a (u, n + 1)).ty, a (t, n) = (a (u, n + 1)).child n i) →
      a (u, n + 1) = a (t, n + 1)) ∧
  (∀ t u n, (t, n + 1) ∈ F → (u, n) ∈ F →
    ∀ i : S.I (a (t, n + 1)).ty,
      u.val.carrier ⊆ ((a (t, n + 1)).child n i).carrier n →
        a (u, n) = (a (t, n + 1)).child n i) ∧
  (∃ (height : ℕ) (A : S.ι) (ψ : Iso d), ∀ x ∈ F,
    S.IsStandardNode A height x.2 ((a x).move ψ) ∧
      ψ '' (a x).carrier x.2 ⊆ interior (S.supertile height A)) ∧
  ((t₀, 0) ∈ F → ∀ x ∈ F, ∃ R ∈ S.rotGroup,
    (a x).frame.linearIsometryEquiv = (a (t₀, 0)).frame.linearIsometryEquiv * R)

/-- Step 6 of the V4 proof of `exists_honest` (V4 1.12):
"it involves finitely many tiles ... and a maximal height".
The constraints really depend only on the displayed finite set of coordinates. -/
private theorem exists_honest_step6_constraints_local {S : SubstSystem d}
    (T : Tiling S) (t₀ : T.tiles) (F : Finset (T.tiles × ℕ)) :
    DependsOn (exists_honest_constraints T t₀ F) (F : Set (T.tiles × ℕ)) := by
  have transfer (a b : T.tiles × ℕ → FramedNode S)
      (hab : ∀ x ∈ F, a x = b x) :
      exists_honest_constraints T t₀ F a → exists_honest_constraints T t₀ F b := by
    rintro ⟨hn, hd, hp, hu, hc, hl, hf⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [← hab x hx]
      exact hn x hx
    · intro x hx y hy
      rw [← hab x hx, ← hab y hy]
      exact hd x hx y hy
    · intro t n ht ht'
      rw [← hab (t, n) ht, ← hab (t, n + 1) ht']
      exact hp t n ht ht'
    · intro t u n ht ht' hu'
      rw [← hab (t, n) ht, ← hab (t, n + 1) ht', ← hab (u, n + 1) hu']
      exact hu t u n ht ht' hu'
    · intro t u n ht hu'
      rw [← hab (t, n + 1) ht, ← hab (u, n) hu']
      exact hc t u n ht hu'
    · obtain ⟨height, A, ψ, hl⟩ := hl
      refine ⟨height, A, ψ, ?_⟩
      intro x hx
      rw [← hab x hx]
      exact hl x hx
    · intro ht₀ x hx
      rw [← hab x hx, ← hab (t₀, 0) ht₀]
      exact hf ht₀ x hx
  intro a b hab
  exact propext ⟨transfer a b hab, transfer b a (fun x hx => (hab x hx).symm)⟩

/-- Step 6 of the V4 proof of `exists_honest` (V4 1.12):
"Every finite subfamily of constraints is satisfiable".
Restricting the selected variables discards constraints. -/
private theorem exists_honest_step6_constraints_mono {S : SubstSystem d}
    (T : Tiling S) (t₀ : T.tiles) (F G : Finset (T.tiles × ℕ)) (hFG : F ⊆ G)
    (a : T.tiles × ℕ → FramedNode S) :
    exists_honest_constraints T t₀ G a → exists_honest_constraints T t₀ F a := by
  rintro ⟨hn, hd, hp, hu, hc, ⟨height, A, ψ, hl⟩, hf⟩
  exact ⟨fun x hx => hn x (hFG hx),
    fun x hx y hy => hd x (hFG hx) y (hFG hy),
    fun t n ht ht' => hp t n (hFG ht) (hFG ht'),
    fun t u n ht ht' hu' => hu t u n (hFG ht) (hFG ht') (hFG hu'),
    fun t u n ht hu' => hc t u n (hFG ht) (hFG hu'),
    ⟨height, A, ψ, fun x hx => hl x (hFG hx)⟩,
    fun ht₀ x hx => hf (hFG ht₀) x (hFG hx)⟩

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"a collar large enough that any node ... consists of tiles of Π₀".
Every placed physical tile has compact support. -/
private theorem exists_honest_step7_tile_compact {S : SubstSystem d}
    (t : PlacedTile S) : IsCompact t.carrier := by
  rw [t.frame_carrier]
  exact (S.proto t.ty).compact.image t.frame.continuous

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"a collar large enough that any node ... consists of tiles of Π₀".
Every candidate ancestor has compact support. -/
private theorem exists_honest_step7_node_compact {S : SubstSystem d}
    (N : FramedNode S) (n : ℕ) : IsCompact (N.carrier n) := by
  exact ((S.proto N.ty).compact.image
    (S.σ ^ n).toLinearMap.continuous_of_finiteDimensional).image N.frame.continuous

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"enlarging Π₀ (and hence n) we may assume n ≥ m".
A whole-space tiling has arbitrarily many distinct physical tiles. -/
private theorem exists_honest_step7_tiles_infinite {S : SubstSystem d}
    (T : Tiling S) : T.tiles.Infinite := by
  classical
  have hd : 2 ≤ d := Fact.out
  letI : NeZero d := ⟨by omega⟩
  intro hfin
  have hc : IsCompact (⋃ t ∈ T.tiles, t.carrier) :=
    hfin.isCompact_biUnion fun t _ => exists_honest_step7_tile_compact t
  have heq : (⋃ t ∈ T.tiles, t.carrier) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    simpa only [exists_prop] using T.cover x
  rw [heq] at hc
  exact noncompact_univ (E d) hc

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"Π₀ ... (finite, Lemma 1.0(c))". Only finitely many tiles meet a compact set. -/
private theorem exists_honest_step7_tiles_meeting {S : SubstSystem d}
    (T : Tiling S) (K : Set (E d)) (hK : IsCompact K) :
    {t : T.tiles | (K ∩ t.val.carrier).Nonempty}.Finite := by
  have hd : Pairwise (fun t u : T.tiles => Disjoint
      (interior (placedSet t.val.frame (S.proto t.val.ty).carrier))
      (interior (placedSet u.val.frame (S.proto u.val.ty).carrier))) := by
    intro t u htu
    rw [← t.val.frame_carrier, ← u.val.frame_carrier]
    exact T.disjoint t.property u.property (fun h => htu (Subtype.ext h))
  have h := (locallyFinite_disjointInteriors S.proto
    (fun t : T.tiles => t.val.ty) (fun t : T.tiles => t.val.frame) hd).2 K hK.isBounded
  simpa only [← PlacedTile.frame_carrier] using h

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"pull back by ψ⁻¹". Motion of a physical tile acts on its carrier. -/
private theorem exists_honest_step7_tile_move_carrier {S : SubstSystem d}
    (t : PlacedTile S) (ψ : Iso d) : (t.move ψ).carrier = ψ '' t.carrier := by
  change (ψ ∘ t.frame) '' (S.proto t.ty).carrier = ψ '' t.carrier
  rw [Set.image_comp]
  change ψ '' placedSet t.frame (S.proto t.ty).carrier = ψ '' t.carrier
  rw [← t.frame_carrier]

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"Π₀ occurs ... as native tiles". A common motion preserves physical tile identity. -/
private theorem exists_honest_step7_move_injective {S : SubstSystem d}
    (ψ : Iso d) : Function.Injective (fun t : PlacedTile S => t.move ψ) := by
  intro t u h
  apply PlacedTile.ext
  · simpa only [PlacedTile.move, PlacedTile.ofFrame] using congrArg PlacedTile.ty h
  · apply ψ.injective.image_injective
    simpa only [exists_honest_step7_tile_move_carrier] using congrArg PlacedTile.carrier h

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"enlarging Π₀ (and hence n) we may assume n ≥ m".
The number of distinct tiles in a native occurrence is bounded by its role words. -/
private theorem exists_honest_step7_occurrence_card {S : SubstSystem d}
    (P : Patch S) (n : ℕ) (A : S.ι) (ψ : Iso d)
    (hocc : ∀ t ∈ P.tiles, ∃ w : S.RoleWord A n,
      t.move ψ = (S.nativeTile A n w).toTile) :
    P.tiles.card ≤ Fintype.card (S.RoleWord A n) := by
  classical
  let f (t : P.tiles) : S.RoleWord A n := (hocc t.val t.property).choose
  have hf (t : P.tiles) : t.val.move ψ = (S.nativeTile A n (f t)).toTile :=
    (hocc t.val t.property).choose_spec
  have hinj : Function.Injective f := by
    intro t u htu
    apply Subtype.ext
    apply exists_honest_step7_move_injective ψ
    change t.val.move ψ = u.val.move ψ
    rw [hf t, hf u, htu]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"Let Π₀ be the patch of all tiles ... a collar large enough that any node of
height ≤ m containing one of the tᵢ consists of tiles of Π₀".
Taking the union of the finitely many candidate supports gives such a collar;
an additional large finite patch forces the legal occurrence to have enough height. -/
private theorem exists_honest_step7_collar {S : SubstSystem d}
    (T : Tiling S) (hT : T ∈ S.Species) (t₀ : T.tiles)
    (F : Finset (T.tiles × ℕ)) :
    ∃ (P : Patch S) (height : ℕ) (A : S.ι) (ψ : Iso d),
      P.IsPatchOf T ∧ t₀.val ∈ P.tiles ∧
      (∀ x ∈ F, x.1.val ∈ P.tiles ∧ x.2 ≤ height) ∧
      (∀ x ∈ F, ∀ N ∈ exists_honest_candidates x.1.val x.2,
        N.carrier x.2 ⊆ P.support) ∧
      (∀ x ∈ F, ∀ N ∈ exists_honest_candidates x.1.val x.2,
        ∀ t ∈ T.tiles, (t.carrier ∩ N.carrier x.2).Nonempty → t ∈ P.tiles) ∧
      (∀ t ∈ P.tiles, ∃ w : S.RoleWord A height,
        t.move ψ = (S.nativeTile A height w).toTile) ∧
      ψ '' P.support ⊆ interior (S.supertile height A) := by
  classical
  let m := F.sup Prod.snd
  let W := Σ (k : Fin m) (A : S.ι), S.RoleWord A k.val
  obtain ⟨Q, hQT, hQcard⟩ := (exists_honest_step7_tiles_infinite T).exists_subset_card_eq
    (Fintype.card W + 1)
  let K : Set (E d) := ⋃ x ∈ F, ⋃ N ∈ exists_honest_candidates x.1.val x.2, N.carrier x.2
  have hK : IsCompact K := F.isCompact_biUnion fun x _ =>
    (exists_honest_step2_candidates_finite x.1.val x.2).isCompact_biUnion
      (fun N _ => exists_honest_step7_node_compact N x.2)
  have hB := exists_honest_step7_tiles_meeting T K hK
  let B := hB.toFinset.image Subtype.val
  let tiles := insert t₀.val ((F.image (fun x => x.1.val)) ∪ B ∪ Q)
  have hsub : (tiles : Set (PlacedTile S)) ⊆ T.tiles := by
    intro t ht
    simp only [tiles, Finset.mem_coe, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at ht
    rcases ht with rfl | ((⟨x, _, rfl⟩ | ht) | ht)
    · exact t₀.property
    · exact x.1.property
    · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ht
      exact u.property
    · exact hQT ht
  let P : Patch S := ⟨tiles, by
    intro t ht u hu hne
    exact T.disjoint (hsub ht) (hsub hu) hne⟩
  have hP : P.IsPatchOf T := hsub
  obtain ⟨height, A, ψ, hocc, hinterior⟩ := hT P hP
  have hheight : m ≤ height := by
    by_contra hm
    have hlt : height < m := Nat.lt_of_not_ge hm
    let f : S.RoleWord A height → W := fun w => ⟨⟨height, hlt⟩, A, w⟩
    have hf : Function.Injective f := by
      intro v w hvw
      cases hvw
      rfl
    have hbound := (exists_honest_step7_occurrence_card P height A ψ hocc).trans
      (Fintype.card_le_of_injective f hf)
    have hQP : Q ⊆ P.tiles := by
      intro t ht
      simp only [P, tiles, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inr ht)
    have hlarge := Finset.card_le_card hQP
    rw [hQcard] at hlarge
    omega
  have hBK (t : T.tiles) (ht : (K ∩ t.val.carrier).Nonempty) : t.val ∈ P.tiles := by
    have hb : t.val ∈ B := Finset.mem_image.mpr ⟨t, hB.mem_toFinset.mpr ht, rfl⟩
    simp only [P, tiles, Finset.mem_insert, Finset.mem_union]
    exact Or.inr (Or.inl (Or.inr hb))
  have hNK (x : T.tiles × ℕ) (hx : x ∈ F)
      (N : FramedNode S) (hN : N ∈ exists_honest_candidates x.1.val x.2) :
      N.carrier x.2 ⊆ K := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx,
      Set.mem_iUnion.mpr ⟨N, Set.mem_iUnion.mpr ⟨hN, hy⟩⟩⟩⟩
  refine ⟨P, height, A, ψ, hP, ?_, ?_, ?_, ?_, hocc, hinterior⟩
  · exact Finset.mem_insert_self _ _
  · intro x hx
    constructor
    · simp only [P, tiles, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inl (Or.inl (Finset.mem_image_of_mem _ hx)))
    · exact (Finset.le_sup (f := Prod.snd) hx).trans hheight
  · intro x hx N hN y hy
    obtain ⟨t, ht, hyt⟩ := T.cover y
    have hmem := hBK ⟨t, ht⟩ ⟨y, hNK x hx N hN hy, hyt⟩
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨hmem, hyt⟩⟩
  · intro x hx N hN t ht ⟨y, hyt, hyN⟩
    exact hBK ⟨t, ht⟩ ⟨y, hNK x hx N hN hyN, hyt⟩

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
The height-n child map is the conjugate of its ground placement. -/
private theorem exists_honest_step7_place_scaled {S : SubstSystem d} (n : ℕ) {A : S.ι}
    (i : S.I A) (x : E d) :
    S.placeChild n i ((S.σ ^ n) x) = (S.σ ^ n) ((S.child A i).frame x) := by
  rw [S.placeChild_apply]
  simp [linearConj, Child.frame, rigidMotion, LinearEquiv.mul_apply,
    zpow_natCast, zpow_neg, AffineIsometryEquiv.coe_trans]

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Changing the base height conjugates the child placement by the expansion. -/
private theorem exists_honest_step7_place_shift {S : SubstSystem d} (h k : ℕ) {A : S.ι}
    (i : S.I A) (x : E d) :
    S.placeChild (h + k) i ((S.σ ^ h) x) = (S.σ ^ h) (S.placeChild k i x) := by
  have h₁ := exists_honest_step7_place_scaled (h + k) i ((S.σ ^ k).symm x)
  have h₂ := exists_honest_step7_place_scaled k i ((S.σ ^ k).symm x)
  simp only [pow_add, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply] at h₁ h₂
  rw [← h₂] at h₁
  exact h₁

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
The same conjugacy holds for every descendant frame. -/
private theorem exists_honest_step7_descendant_scaled {S : SubstSystem d} (A : S.ι) (h k : ℕ)
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
    rw [ih, exists_honest_step7_place_shift, Nat.zero_add]

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
The type at the end of a role word is independent of its base height. -/
private theorem exists_honest_step7_descendant_type {S : SubstSystem d} (A : S.ι) (h k : ℕ)
    (w : S.RoleWord A k) : (S.descendantNode A h k w).ty = (S.nativeTile A k w).ty := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih => exact ih (S.child A w.1).ty w.2

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
A height-h level is the linear image of the corresponding native partition. -/
private theorem exists_honest_step7_descendant_carrier {S : SubstSystem d} (A : S.ι) (h k : ℕ)
    (w : S.RoleWord A k) :
    (S.descendantNode A h k w).carrier h = (S.σ ^ h) '' (S.nativeTile A k w).carrier 0 := by
  have hz : (S.nativeTile A k w).carrier 0 =
      (S.nativeTile A k w).frame '' (S.proto (S.nativeTile A k w).ty).carrier := by
    simp [FramedNode.carrier, SubstSystem.supertile, placedSet]
  rw [hz]
  simp only [FramedNode.carrier, SubstSystem.supertile, placedSet, exists_honest_step7_descendant_type]
  rw [Set.image_image, Set.image_image]
  congr 1
  funext x
  exact exists_honest_step7_descendant_scaled A h k w x

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Different framed standard nodes at one height have disjoint interiors. -/
private theorem exists_honest_step7_standard_disjoint {S : SubstSystem d} (A : S.ι) (height n : ℕ)
    (N P : FramedNode S) (hN : S.IsStandardNode A height n N)
    (hP : S.IsStandardNode A height n P) (hne : N ≠ P) :
    Disjoint (interior (N.carrier n)) (interior (P.carrier n)) := by
  obtain ⟨k, hk, u, rfl⟩ := hN
  obtain ⟨l, hl, v, rfl⟩ := hP
  have hkl : k = l := by omega
  subst l
  have huv : u ≠ v := fun h => hne (h ▸ rfl)
  rw [exists_honest_step7_descendant_carrier, exists_honest_step7_descendant_carrier]
  let e := (S.σ ^ n).toContinuousLinearEquiv.toHomeomorph
  change Disjoint (interior (e '' _)) (interior (e '' _))
  rw [← e.image_interior, ← e.image_interior]
  exact Set.disjoint_image_of_injective e.injective (S.native_disjoint A k huv)

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Split a role word into the path to an ancestor and the remaining descendant path. -/
private theorem exists_honest_step7_split_word {S : SubstSystem d} (A : S.ι) (h m k : ℕ)
    (w : S.RoleWord A (m + k)) :
    ∃ u : S.RoleWord A k,
      ∃ v : S.RoleWord (S.descendantNode A (h + m) k u).ty m,
        S.descendantNode A h (m + k) w =
          (S.descendantNode (S.descendantNode A (h + m) k u).ty h m v).move
            (S.descendantNode A (h + m) k u).frame := by
  induction k generalizing A with
  | zero =>
    refine ⟨(), w, ?_⟩
    simp [SubstSystem.descendantNode, FramedNode.move]
  | succ k ih =>
    obtain ⟨u, v, hv⟩ := ih (S.child A w.1).ty w.2
    refine ⟨⟨w.1, u⟩, v, ?_⟩
    change (S.descendantNode (S.child A w.1).ty h (m + k) w.2).move
      (S.placeChild (h + (m + k)) w.1) = _
    rw [hv]
    simp [SubstSystem.descendantNode, FramedNode.move, Nat.add_assoc,
      ← AffineIsometryEquiv.trans_assoc]

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Concatenate the path to an ancestor with a path inside that ancestor. -/
private theorem exists_honest_step7_join_words {S : SubstSystem d} (A : S.ι) (h m k : ℕ)
    (u : S.RoleWord A k)
    (v : S.RoleWord (S.descendantNode A (h + m) k u).ty m) :
    ∃ w : S.RoleWord A (m + k),
      S.descendantNode A h (m + k) w =
        (S.descendantNode (S.descendantNode A (h + m) k u).ty h m v).move
          (S.descendantNode A (h + m) k u).frame := by
  induction k generalizing A with
  | zero =>
    refine ⟨v, ?_⟩
    simp [SubstSystem.descendantNode, FramedNode.move]
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih (S.child A u.1).ty u.2 v
    refine ⟨⟨u.1, w⟩, ?_⟩
    change (S.descendantNode (S.child A u.1).ty h (m + k) w).move
      (S.placeChild (h + (m + k)) u.1) = _
    rw [hw]
    simp [SubstSystem.descendantNode, FramedNode.move, Nat.add_assoc,
      ← AffineIsometryEquiv.trans_assoc]

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
A standard height-zero node is exactly a native framed tile. -/
private theorem exists_honest_step7_standard_ground {S : SubstSystem d} (A : S.ι) (height : ℕ)
    (N : FramedNode S) (hN : S.IsStandardNode A height 0 N) :
    ∃ w : S.RoleWord A height, N = S.nativeTile A height w := by
  obtain ⟨k, hk, w, rfl⟩ := hN
  simp only [Nat.zero_add] at hk
  subst height
  exact ⟨w, rfl⟩

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Every prescribed child of a standard node is standard. -/
private theorem exists_honest_step7_standard_child {S : SubstSystem d} (A : S.ι) (height n : ℕ)
    (N : FramedNode S) (hN : S.IsStandardNode A height (n + 1) N) (i : S.I N.ty) :
    S.IsStandardNode A height n (N.child n i) := by
  obtain ⟨k, hk, u, rfl⟩ := hN
  obtain ⟨w, hw⟩ := exists_honest_step7_join_words A n 1 k u ⟨i, ()⟩
  refine ⟨1 + k, by omega, w, ?_⟩
  simpa [SubstSystem.descendantNode, FramedNode.move, FramedNode.child] using hw.symm

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Every standard node below the root has a standard parent with an exact child role. -/
private theorem exists_honest_step7_standard_parent {S : SubstSystem d} (A : S.ι) (height n : ℕ)
    (N : FramedNode S) (hN : S.IsStandardNode A height n N) (hn : n < height) :
    ∃ P : FramedNode S, S.IsStandardNode A height (n + 1) P ∧
      ∃ i : S.I P.ty, N = P.child n i := by
  obtain ⟨l, hl, w, rfl⟩ := hN
  have hlpos : 1 ≤ l := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlpos
  obtain ⟨u, v, hv⟩ := exists_honest_step7_split_word A n 1 k w
  refine ⟨S.descendantNode A (n + 1) k u, ⟨k, by omega, u, rfl⟩, v.1, ?_⟩
  simpa [SubstSystem.descendantNode, FramedNode.move, FramedNode.child] using hv

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Every native leaf of a standard node is a native leaf of the context. -/
private theorem exists_honest_step7_standard_native {S : SubstSystem d} (A : S.ι) (height n : ℕ)
    (N : FramedNode S) (hN : S.IsStandardNode A height n N)
    (v : S.RoleWord N.ty n) :
    S.IsStandardNode A height 0 ((S.nativeTile N.ty n v).move N.frame) := by
  obtain ⟨k, hk, u, rfl⟩ := hN
  subst height
  have h := exists_honest_step7_join_words A 0 n k u
  rw [Nat.zero_add] at h
  obtain ⟨w, hw⟩ := h v
  exact ⟨n + k, by omega, w, hw.symm⟩

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
A standard ground tile has an ancestor at every height up to the root. -/
private theorem exists_honest_step7_standard_ancestor {S : SubstSystem d} (A : S.ι) (height n : ℕ)
    (L : FramedNode S) (hL : S.IsStandardNode A height 0 L) (hn : n ≤ height) :
    ∃ N : FramedNode S, S.IsStandardNode A height n N ∧
      ∃ v : S.RoleWord N.ty n, (S.nativeTile N.ty n v).move N.frame = L := by
  obtain ⟨w, rfl⟩ := exists_honest_step7_standard_ground A height L hL
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := exists_honest_step7_split_word A 0 n k w
  rw [Nat.zero_add] at h
  obtain ⟨u, v, hv⟩ := h
  exact ⟨S.descendantNode A n k u, ⟨k, rfl, u, rfl⟩, v, hv.symm⟩

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Physical tiles have nonempty interior. -/
private theorem exists_honest_step7_tile_interior {S : SubstSystem d} (t : PlacedTile S) :
    (interior t.carrier).Nonempty := by
  rw [t.frame_carrier]
  exact t.frame.toHomeomorph.image_interior _ ▸
    (S.proto t.ty).interior_nonempty.image t.frame

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Physical tiles are the closures of their interiors. -/
private theorem exists_honest_step7_tile_regular {S : SubstSystem d} (t : PlacedTile S) :
    closure (interior t.carrier) = t.carrier := by
  rw [t.frame_carrier]
  change closure (interior (t.frame.toHomeomorph '' _)) = t.frame.toHomeomorph '' _
  rw [← t.frame.toHomeomorph.image_interior, ← t.frame.toHomeomorph.image_closure,
    (S.proto t.ty).regularClosed]

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
A tile contained in a finite union from the same disjoint-interior family belongs to that union. -/
private theorem exists_honest_step7_saturation {S : SubstSystem d} (s : Finset (PlacedTile S))
    (Q : Set (PlacedTile S)) (hQ : Q.PairwiseDisjoint (fun t => interior t.carrier))
    (hs : (s : Set (PlacedTile S)) ⊆ Q) (t : PlacedTile S) (ht : t ∈ Q)
    (hsub : t.carrier ⊆ ⋃ u ∈ s, u.carrier) : t ∈ s := by
  classical
  let U := ⋃ u ∈ s, interior u.carrier
  have hclosure : (⋃ u ∈ s, u.carrier) ⊆ closure U := by
    intro x hx
    obtain ⟨u, hxu⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hu, hxu⟩ := Set.mem_iUnion.mp hxu
    rw [← exists_honest_step7_tile_regular u] at hxu
    exact closure_mono (fun y hy => Set.mem_iUnion.mpr
      ⟨u, Set.mem_iUnion.mpr ⟨hu, hy⟩⟩) hxu
  obtain ⟨x, hx⟩ := exists_honest_step7_tile_interior t
  have hxU := hclosure (hsub (interior_subset hx))
  obtain ⟨y, hyt, hyU⟩ := mem_closure_iff.mp hxU (interior t.carrier) isOpen_interior hx
  obtain ⟨u, hyu⟩ := Set.mem_iUnion.mp hyU
  obtain ⟨hu, hyu⟩ := Set.mem_iUnion.mp hyu
  have htu : t = u := by
    by_contra hne
    exact Set.disjoint_left.mp (hQ ht (hs hu) hne) hyt hyu
  exact htu ▸ hu

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Moving a framed node applies the same isometry to its carrier. -/
private theorem exists_honest_step7_node_move_carrier {S : SubstSystem d} (N : FramedNode S)
    (ψ : Iso d) (n : ℕ) : (N.move ψ).carrier n = ψ '' N.carrier n := by
  exact Set.image_comp ψ N.frame (S.supertile n N.ty)

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Forgetting a frame commutes with physical motion. -/
private theorem exists_honest_step7_move_toTile {S : SubstSystem d} (N : FramedNode S)
    (ψ : Iso d) : (N.move ψ).toTile = N.toTile.move ψ := by
  apply PlacedTile.ext
  · rfl
  · rw [exists_honest_step7_tile_move_carrier]
    exact Set.image_comp ψ N.frame (S.proto N.ty).carrier

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Moving a pulled-back node into its context recovers the original framed node. -/
private theorem exists_honest_step7_pullback_cancel {S : SubstSystem d} (N : FramedNode S) (ψ : Iso d) :
    (N.move ψ.symm).move ψ = N := by
  simp [FramedNode.move, ← AffineIsometryEquiv.trans_assoc]

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Motion preserves the child equation, including its prescribed role. -/
private theorem exists_honest_step7_move_child {S : SubstSystem d} (N : FramedNode S) (ψ : Iso d)
    (n : ℕ) (i : S.I N.ty) : (N.child n i).move ψ = (N.move ψ).child n i := rfl

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Each prescribed child carrier is contained in its parent carrier. -/
private theorem exists_honest_step7_child_subset {S : SubstSystem d} (N : FramedNode S) (n : ℕ)
    (i : S.I N.ty) : (N.child n i).carrier n ⊆ N.carrier (n + 1) := by
  have hc := Set.subset_iUnion (fun i : S.I N.ty =>
    placedSet (S.child N.ty i).frame (S.proto (S.child N.ty i).ty).carrier) i
  rw [← S.children_cover N.ty] at hc
  rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
  change N.frame (S.placeChild n i ((S.σ ^ n) x)) ∈ N.frame '' S.supertile (n + 1) N.ty
  rw [exists_honest_step7_place_scaled]
  obtain ⟨p, hp, heq⟩ := hc ⟨x, hx, rfl⟩
  refine ⟨(S.σ ^ n) ((S.child N.ty i).frame x), ⟨p, hp, ?_⟩, rfl⟩
  rw [pow_succ, LinearEquiv.mul_apply, heq]

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Disjointness of standard nodes pulls back to the finite configuration. -/
private theorem exists_honest_step7_context_disjoint {S : SubstSystem d} (A : S.ι) (height n : ℕ)
    (ψ : Iso d) (N P : FramedNode S)
    (hN : S.IsStandardNode A height n (N.move ψ))
    (hP : S.IsStandardNode A height n (P.move ψ)) (hne : N ≠ P) :
    Disjoint (interior (N.carrier n)) (interior (P.carrier n)) := by
  have hm : N.move ψ ≠ P.move ψ := by
    intro h
    apply hne
    have := congrArg (fun M : FramedNode S => M.move ψ.symm) h
    simpa only [FramedNode.move, ← AffineIsometryEquiv.trans_assoc,
      AffineIsometryEquiv.self_trans_symm, AffineIsometryEquiv.trans_refl] using this
  have hdis := exists_honest_step7_standard_disjoint A height n (N.move ψ) (P.move ψ) hN hP hm
  rw [exists_honest_step7_node_move_carrier, exists_honest_step7_node_move_carrier] at hdis
  change Disjoint (interior (ψ.toHomeomorph '' N.carrier n))
    (interior (ψ.toHomeomorph '' P.carrier n)) at hdis
  have hn := ψ.toHomeomorph.image_interior (N.carrier n)
  have hp := ψ.toHomeomorph.image_interior (P.carrier n)
  rw [← hn, ← hp] at hdis
  exact hdis.of_image

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Two same-height context nodes containing one physical tile coincide as framed nodes. -/
private theorem exists_honest_step7_context_unique {S : SubstSystem d} (A : S.ι) (height n : ℕ)
    (ψ : Iso d) (N P : FramedNode S)
    (hN : S.IsStandardNode A height n (N.move ψ))
    (hP : S.IsStandardNode A height n (P.move ψ))
    (t : PlacedTile S) (htN : t.carrier ⊆ N.carrier n) (htP : t.carrier ⊆ P.carrier n) :
    N = P := by
  by_contra hne
  obtain ⟨x, hx⟩ := exists_honest_step7_tile_interior t
  exact Set.disjoint_left.mp (exists_honest_step7_context_disjoint A height n ψ N P hN hP hne)
    (interior_mono htN hx) (interior_mono htP hx)

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Ancestor candidacy is invariant under a common isometry. -/
private theorem exists_honest_step7_candidate_move {S : SubstSystem d} (t : PlacedTile S)
    (n : ℕ) (N : FramedNode S) (ψ : Iso d) :
    N.move ψ ∈ exists_honest_candidates (t.move ψ) n ↔
      N ∈ exists_honest_candidates t n := by
  have he (w : S.RoleWord N.ty n) :
      ((S.nativeTile (N.move ψ).ty n w).move (N.move ψ).frame).toTile =
        ((S.nativeTile N.ty n w).move N.frame).toTile.move ψ :=
    exists_honest_step7_move_toTile ((S.nativeTile N.ty n w).move N.frame) ψ
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, exists_honest_step7_move_injective ψ ?_⟩
    change ((S.nativeTile N.ty n w).move N.frame).toTile.move ψ = t.move ψ
    rw [← he w]
    exact hw
  · rintro ⟨w, hw⟩
    exact ⟨w, (he w).trans (congrArg (fun t : PlacedTile S => t.move ψ) hw)⟩

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
A candidate ancestor contains its recorded physical tile. -/
private theorem exists_honest_step7_candidate_subset {S : SubstSystem d} (t : PlacedTile S)
    (n : ℕ) (N : FramedNode S) (hN : N ∈ exists_honest_candidates t n) :
    t.carrier ⊆ N.carrier n := by
  obtain ⟨w, hw⟩ := hN
  rw [← hw]
  exact exists_honest_step4_native_subset N n w

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Forgetting a height-zero frame preserves its carrier. -/
private theorem exists_honest_step7_zero_carrier {S : SubstSystem d} (N : FramedNode S) :
    N.carrier 0 = N.toTile.carrier := by
  simp [FramedNode.carrier, FramedNode.toTile, PlacedTile.ofFrame,
    SubstSystem.supertile, placedSet]

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
The native physical tiles cover the entire node carrier. -/
private theorem exists_honest_step7_native_union {S : SubstSystem d} (N : FramedNode S) (n : ℕ) :
    N.carrier n = ⋃ w : S.RoleWord N.ty n,
      ((S.nativeTile N.ty n w).move N.frame).toTile.carrier := by
  change N.frame '' S.supertile n N.ty = _
  rw [← S.native_cover N.ty n, Set.image_iUnion]
  congr 1
  funext w
  rw [← exists_honest_step7_node_move_carrier, exists_honest_step7_zero_carrier]

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
The collar recovers exactly all native physical tiles, with their original types. -/
private theorem exists_honest_step7_native_exact {S : SubstSystem d} (T : Tiling S) (P : Patch S)
    (hP : P.IsPatchOf T) (height : ℕ) (A : S.ι) (ψ : Iso d)
    (hocc : ∀ t ∈ P.tiles, ∃ w : S.RoleWord A height,
      t.move ψ = (S.nativeTile A height w).toTile)
    (n : ℕ) (N : FramedNode S) (hN : S.IsStandardNode A height n (N.move ψ))
    (hNP : N.carrier n ⊆ P.support) :
    {t | t ∈ T.tiles ∧ t.carrier ⊆ N.carrier n} =
      {t | ∃ w : S.RoleWord N.ty n,
        ((S.nativeTile N.ty n w).move N.frame).toTile = t} := by
  classical
  let Q : Set (PlacedTile S) := {t | ∃ L : FramedNode S,
    S.IsStandardNode A height 0 (L.move ψ) ∧ L.toTile = t}
  have hQ : Q.PairwiseDisjoint (fun t => interior t.carrier) := by
    rintro t ⟨L, hL, rfl⟩ u ⟨M, hM, rfl⟩ hne
    change Disjoint (interior L.toTile.carrier) (interior M.toTile.carrier)
    rw [← exists_honest_step7_zero_carrier, ← exists_honest_step7_zero_carrier]
    exact exists_honest_step7_context_disjoint A height 0 ψ L M hL hM
      (fun h => hne (congrArg FramedNode.toTile h))
  have hPQ : (P.tiles : Set (PlacedTile S)) ⊆ Q := by
    intro t ht
    obtain ⟨w, hw⟩ := hocc t ht
    refine ⟨(S.nativeTile A height w).move ψ.symm, ?_, ?_⟩
    · rw [exists_honest_step7_pullback_cancel]
      exact ⟨height, by omega, w, rfl⟩
    · apply exists_honest_step7_move_injective ψ
      change ((S.nativeTile A height w).move ψ.symm).toTile.move ψ = t.move ψ
      rw [← exists_honest_step7_move_toTile, exists_honest_step7_pullback_cancel, hw]
  have hleaves (w : S.RoleWord N.ty n) :
      ((S.nativeTile N.ty n w).move N.frame).toTile ∈ T.tiles := by
    let L := (S.nativeTile N.ty n w).move N.frame
    have hL : L.toTile ∈ Q := ⟨L, exists_honest_step7_standard_native A height n (N.move ψ) hN w, rfl⟩
    exact hP (exists_honest_step7_saturation P.tiles Q hQ hPQ L.toTile hL
      ((exists_honest_step4_native_subset N n w).trans hNP))
  ext t
  constructor
  · rintro ⟨ht, hsub⟩
    let s := Finset.univ.image (fun w : S.RoleWord N.ty n =>
      ((S.nativeTile N.ty n w).move N.frame).toTile)
    have hs : (s : Set (PlacedTile S)) ⊆ T.tiles := by
      rintro u hu
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hu
      exact hleaves w
    have hsupp : t.carrier ⊆ ⋃ u ∈ s, u.carrier := by
      intro x hx
      have hxN := hsub hx
      rw [exists_honest_step7_native_union] at hxN
      obtain ⟨w, hxw⟩ := Set.mem_iUnion.mp hxN
      exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr
        ⟨Finset.mem_image_of_mem _ (Finset.mem_univ w), hxw⟩⟩
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp (exists_honest_step7_saturation s T.tiles T.disjoint hs t ht hsupp)
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨hleaves w, exists_honest_step4_native_subset N n w⟩

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Pulling a moved node back recovers its complete frame. -/
private theorem exists_honest_step7_move_cancel {S : SubstSystem d} (N : FramedNode S) (ψ : Iso d) :
    (N.move ψ).move ψ.symm = N := by
  simpa only [AffineIsometryEquiv.symm_symm] using exists_honest_step7_pullback_cancel N ψ.symm

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
Choose standard ancestors for the finitely many recorded tiles and heights. -/
private theorem exists_honest_step7_choose_ancestors {S : SubstSystem d} (T : Tiling S) (t₀ : T.tiles)
    (F : Finset (T.tiles × ℕ)) (P : Patch S) (height : ℕ) (A : S.ι) (ψ : Iso d)
    (hbase : ∀ x ∈ F, x.1.val ∈ P.tiles ∧ x.2 ≤ height)
    (hocc : ∀ t ∈ P.tiles, ∃ w : S.RoleWord A height,
      t.move ψ = (S.nativeTile A height w).toTile) :
    ∃ a : T.tiles × ℕ → FramedNode S,
      (∀ x ∈ F, a x ∈ exists_honest_candidates x.1.val x.2) ∧
      ∀ x ∈ F, S.IsStandardNode A height x.2 ((a x).move ψ) := by
  classical
  have hc (x : T.tiles × ℕ) (hx : x ∈ F) :
      ∃ N : FramedNode S, N ∈ exists_honest_candidates x.1.val x.2 ∧
        S.IsStandardNode A height x.2 (N.move ψ) := by
    obtain ⟨w, hw⟩ := hocc x.1.val (hbase x hx).1
    have hL : S.IsStandardNode A height 0 (S.nativeTile A height w) :=
      ⟨height, by omega, w, rfl⟩
    obtain ⟨M, hM, v, hv⟩ := exists_honest_step7_standard_ancestor A height x.2
      (S.nativeTile A height w) hL (hbase x hx).2
    refine ⟨M.move ψ.symm, ?_, ?_⟩
    · apply (exists_honest_step7_candidate_move x.1.val x.2 (M.move ψ.symm) ψ).mp
      rw [exists_honest_step7_pullback_cancel]
      exact ⟨v, (congrArg FramedNode.toTile hv).trans hw.symm⟩
    · simpa only [exists_honest_step7_pullback_cancel] using hM
  choose f hf hstd using hc
  let a (x : T.tiles × ℕ) : FramedNode S :=
    if hx : x ∈ F then f x hx else ⟨t₀.val.ty, t₀.val.frame⟩
  refine ⟨a, ?_, ?_⟩
  · intro x hx
    simpa only [a, dif_pos hx] using hf x hx
  · intro x hx
    simpa only [a, dif_pos hx] using hstd x hx

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"The standard hierarchy ... gives each tile ... its ancestors ...; pull back by ψ⁻¹".
All pulled-back standard frames lie in the root frame coset, by V4 1.10(b). -/
private theorem exists_honest_step7_context_coset {S : SubstSystem d} (A : S.ι) (height n : ℕ)
    (ψ : Iso d) (N : FramedNode S)
    (hN : S.IsStandardNode A height n (N.move ψ)) :
    ∃ R ∈ S.rotGroup, N.frame.linearIsometryEquiv = ψ.symm.linearIsometryEquiv * R := by
  obtain ⟨k, _, w, hw⟩ := hN
  have heq : N = (S.descendantNode A n k w).move ψ.symm := by
    simpa only [exists_honest_step7_move_cancel] using
      congrArg (fun M : FramedNode S => M.move ψ.symm) hw
  rw [heq]
  exact S.descendant_frames A n k w ψ.symm

/-- Step 7 of the V4 proof of `exists_honest` (V4 1.12):
"By (H7) Π₀ occurs inside ... as native tiles. The standard hierarchy ... gives
each tile ... its ancestors ...; pull back by ψ⁻¹. This satisfies (C1) and (C2)";
the anchor's pulled-back frame gives (C3) by V4 1.10(b).
Only the finitely many indices in `F` are constrained; the values elsewhere are
arbitrary. The collar includes the entire native subdivisions of these nodes. -/
private theorem exists_honest_step7_finite_realization {S : SubstSystem d}
    (T : Tiling S) (hT : T ∈ S.Species) (t₀ : T.tiles)
    (F : Finset (T.tiles × ℕ)) :
    ∃ a : T.tiles × ℕ → FramedNode S,
      (∀ x ∈ F, a x ∈ exists_honest_candidates x.1.val x.2) ∧
        exists_honest_constraints T t₀ F a := by
  classical
  obtain ⟨P, height, A, ψ, hP, _, hbase, hcover, _, hocc, hinterior⟩ :=
    exists_honest_step7_collar T hT t₀ F
  obtain ⟨a, ha, hstd⟩ := exists_honest_step7_choose_ancestors T t₀ F P height A ψ hbase hocc
  have hcontains (x : T.tiles × ℕ) (hx : x ∈ F) :
      x.1.val.carrier ⊆ (a x).carrier x.2 :=
    exists_honest_step7_candidate_subset x.1.val x.2 (a x) (ha x hx)
  refine ⟨a, ha, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact exists_honest_step7_native_exact T P hP height A ψ hocc x.2 (a x) (hstd x hx)
      (hcover x hx (a x) (ha x hx))
  · intro x hx y hy hxy hne
    have hN := hstd x hx
    have hP := hstd y hy
    rw [← hxy] at hP
    simpa only [hxy] using exists_honest_step7_context_disjoint A height x.2 ψ (a x) (a y) hN hP hne
  · intro t n ht ht'
    have hn : n < height := lt_of_lt_of_le (Nat.lt_succ_self n) (hbase (t, n + 1) ht').2
    obtain ⟨M, hM, i, hchild⟩ := exists_honest_step7_standard_parent A height n
      ((a (t, n)).move ψ) (hstd (t, n) ht) hn
    let P := M.move ψ.symm
    have hPstd : S.IsStandardNode A height (n + 1) (P.move ψ) := by
      simpa only [P, exists_honest_step7_pullback_cancel] using hM
    have he : a (t, n) = P.child n i := by
      simpa only [exists_honest_step7_move_cancel, exists_honest_step7_move_child] using
        congrArg (fun N : FramedNode S => N.move ψ.symm) hchild
    have htP : t.val.carrier ⊆ P.carrier (n + 1) :=
      (hcontains (t, n) ht).trans (he ▸ exists_honest_step7_child_subset P n i)
    have hPeq := exists_honest_step7_context_unique A height (n + 1) ψ P (a (t, n + 1))
      hPstd (hstd (t, n + 1) ht') t.val htP (hcontains (t, n + 1) ht')
    rw [← hPeq]
    exact ⟨i, he⟩
  · intro t u n ht ht' hu hchild
    obtain ⟨i, hi⟩ := hchild
    apply exists_honest_step7_context_unique A height (n + 1) ψ (a (u, n + 1)) (a (t, n + 1))
      (hstd (u, n + 1) hu) (hstd (t, n + 1) ht') t.val
    · exact (hcontains (t, n) ht).trans (hi ▸ exists_honest_step7_child_subset (a (u, n + 1)) n i)
    · exact hcontains (t, n + 1) ht'
  · intro t u n ht hu i hsub
    apply exists_honest_step7_context_unique A height n ψ (a (u, n)) ((a (t, n + 1)).child n i)
      (hstd (u, n) hu) _ u.val (hcontains (u, n) hu) hsub
    rw [exists_honest_step7_move_child]
    exact exists_honest_step7_standard_child A height n ((a (t, n + 1)).move ψ) (hstd (t, n + 1) ht) i
  · refine ⟨height, A, ψ, ?_⟩
    intro x hx
    exact ⟨hstd x hx, (Set.image_mono (hcover x hx (a x) (ha x hx))).trans hinterior⟩
  · intro ht₀ x hx
    obtain ⟨R₀, hR₀, he₀⟩ := exists_honest_step7_context_coset A height 0 ψ (a (t₀, 0)) (hstd _ ht₀)
    obtain ⟨R, hR, he⟩ := exists_honest_step7_context_coset A height x.2 ψ (a x) (hstd x hx)
    refine ⟨R₀⁻¹ * R, S.rotGroup.mul_mem (S.rotGroup.inv_mem hR₀) hR, ?_⟩
    rw [he, he₀]
    group

/-- Step 8 of the V4 proof of `exists_honest` (V4 1.12):
"there is a global assignment satisfying all constraints".
The height-zero anchor is itself a finite-valued frame variable, so the resulting
coset is common to all levels, without fixing arbitrary physical tile frames. -/
private theorem exists_honest_step8_assignment {S : SubstSystem d}
    (T : Tiling S) (hT : T ∈ S.Species) (t₀ : T.tiles) :
    ∃ a : T.tiles × ℕ → FramedNode S,
      (∀ x, a x ∈ exists_honest_candidates x.1.val x.2) ∧
        ∀ F, exists_honest_constraints T t₀ F a := by
  classical
  let C (x : T.tiles × ℕ) := exists_honest_candidates x.1.val x.2
  have hne : ∀ x, (C x).Nonempty := by
    intro x
    obtain ⟨a, ha, _⟩ := exists_honest_step7_finite_realization T hT t₀ {x}
    exact ⟨a x, ha x (Finset.mem_singleton_self x)⟩
  letI : ∀ x, Finite (C x) := fun x =>
    (exists_honest_step2_candidates_finite x.1.val x.2).to_subtype
  let P (F : Finset (T.tiles × ℕ)) (a : ∀ x, C x) :=
    exists_honest_constraints T t₀ F (fun x => (a x).val)
  have hfin : ∀ F, ∃ a, P F a := by
    intro F
    obtain ⟨a, ha, hgood⟩ := exists_honest_step7_finite_realization T hT t₀ F
    let b (x : T.tiles × ℕ) : C x :=
      if hx : x ∈ F then ⟨a x, ha x hx⟩ else ⟨(hne x).choose, (hne x).choose_spec⟩
    refine ⟨b, ?_⟩
    have hab : ∀ x ∈ F, a x = (b x).val := by
      intro x hx
      simp [b, hx]
    change exists_honest_constraints T t₀ F (fun x => (b x).val)
    exact (exists_honest_step6_constraints_local T t₀ F hab) ▸ hgood
  obtain ⟨a, ha⟩ := exists_honest_step3_compactness P
    (fun F a b hab => exists_honest_step6_constraints_local T t₀ F
      (fun x hx => congrArg Subtype.val (hab x hx)))
    (fun F G hFG a => exists_honest_step6_constraints_mono T t₀ F G hFG
      (fun x => (a x).val)) hfin
  exact ⟨fun x => (a x).val, fun x => (a x).property, ha⟩

/-- Step 9 of the V4 proof of `exists_honest` (V4 1.12):
"Define Nₘ as the set of recorded m-ancestors. (C1) makes them a coherent
hierarchy". This constructs all fields, including complete native subdivisions
and the unique parent map, from the already compatible assignment. -/
private theorem exists_honest_step9_hierarchy {S : SubstSystem d}
    (T : Tiling S) (t₀ : T.tiles) (a : T.tiles × ℕ → FramedNode S)
    (ha : ∀ x, a x ∈ exists_honest_candidates x.1.val x.2)
    (hgood : ∀ F, exists_honest_constraints T t₀ F a) :
    ∃ H : CoherentHierarchy S T,
      ∀ n, H.nodes n = Set.range (fun t : T.tiles => a (t, n)) := by
  classical
  have hnative (t : T.tiles) (n : ℕ) :
      {u | u ∈ T.tiles ∧ u.carrier ⊆ (a (t, n)).carrier n} =
        {u | ∃ w : S.RoleWord (a (t, n)).ty n,
          ((S.nativeTile (a (t, n)).ty n w).move (a (t, n)).frame).toTile = u} :=
    (hgood {(t, n)}).1 (t, n) (by simp)
  have hdisjoint (t u : T.tiles) (n : ℕ) (hne : a (t, n) ≠ a (u, n)) :
      Disjoint (interior ((a (t, n)).carrier n))
        (interior ((a (u, n)).carrier n)) :=
    (hgood {(t, n), (u, n)}).2.1 (t, n) (by simp) (u, n) (by simp) rfl hne
  have hparent (t : T.tiles) (n : ℕ) :
      ∃ i : S.I (a (t, n + 1)).ty, a (t, n) = (a (t, n + 1)).child n i :=
    (hgood {(t, n), (t, n + 1)}).2.2.1 t n (by simp) (by simp)
  have hunique (t u : T.tiles) (n : ℕ) :
      (∃ i : S.I (a (u, n + 1)).ty, a (t, n) = (a (u, n + 1)).child n i) →
        a (u, n + 1) = a (t, n + 1) :=
    (hgood {(t, n), (t, n + 1), (u, n + 1)}).2.2.2.1 t u n
      (by simp) (by simp) (by simp)
  have hchild (t u : T.tiles) (n : ℕ) (i : S.I (a (t, n + 1)).ty) :
      u.val.carrier ⊆ ((a (t, n + 1)).child n i).carrier n →
        a (u, n) = (a (t, n + 1)).child n i :=
    (hgood {(t, n + 1), (u, n)}).2.2.2.2.1 t u n (by simp) (by simp) i
  have hzero (t : T.tiles) : (a (t, 0)).toTile = t.val := by
    obtain ⟨w, hw⟩ := ha (t, 0)
    simpa [SubstSystem.nativeTile, SubstSystem.descendantNode, FramedNode.move] using hw
  let nodes (n : ℕ) := Set.range (fun t : T.tiles => a (t, n))
  have representatives (n : ℕ) (N : {N // N ∈ nodes n}) :
      ∃ t : T.tiles, a (t, n) = N.val := N.property
  choose rep hrep using representatives
  let parent (n : ℕ) (N : {N // N ∈ nodes n}) : {P // P ∈ nodes (n + 1)} :=
    ⟨a (rep n N, n + 1), ⟨rep n N, rfl⟩⟩
  let role (n : ℕ) (N : {N // N ∈ nodes n}) : S.I (parent n N).val.ty :=
    (hparent (rep n N) n).choose
  refine ⟨{
    nodes := nodes
    ground := ?_
    cover := ?_
    disjoint := ?_
    parent := parent
    role := role
    child_eq := ?_
    children_mem := ?_
    parent_unique := ?_
    native_tiles := ?_
  }, fun _ => rfl⟩
  · ext t
    constructor
    · rintro ⟨N, ⟨u, rfl⟩, hNt⟩
      rw [hzero] at hNt
      exact hNt ▸ u.property
    · intro ht
      exact ⟨a (⟨t, ht⟩, 0), ⟨⟨t, ht⟩, rfl⟩, hzero ⟨t, ht⟩⟩
  · intro n x
    obtain ⟨t, ht, hxt⟩ := T.cover x
    let u : T.tiles := ⟨t, ht⟩
    refine ⟨a (u, n), ⟨u, rfl⟩, ?_⟩
    obtain ⟨w, hw⟩ := ha (u, n)
    apply exists_honest_step4_native_subset (a (u, n)) n w
    simpa only [hw] using hxt
  · intro n N hN P hP hNP
    obtain ⟨t, rfl⟩ := hN
    obtain ⟨u, rfl⟩ := hP
    exact hdisjoint t u n hNP
  · intro n N
    exact (hrep n N).symm.trans (hparent (rep n N) n).choose_spec
  · intro n P hP i
    obtain ⟨t, rfl⟩ := hP
    obtain ⟨u, hu⟩ := exists_honest_step5_child_tile T n (a (t, n + 1)) (hnative t _) i
    exact ⟨u, hchild t u n i hu⟩
  · intro n N P hP hNP
    obtain ⟨u, rfl⟩ := hP
    apply hunique (rep n N) u n
    simpa only [hrep n N] using hNP
  · intro n N hN
    obtain ⟨t, rfl⟩ := hN
    exact hnative t n

/-- Step 10 of the V4 proof of `exists_honest` (V4 1.12):
"(C2), (C3) give S-membership". A finite node set has a finite set of recorded
representatives, and its context preserves the hierarchy's actual child equations. -/
private theorem exists_honest_step10_contexts {S : SubstSystem d}
    (T : Tiling S) (t₀ : T.tiles) (a : T.tiles × ℕ → FramedNode S)
    (hgood : ∀ F, exists_honest_constraints T t₀ F a)
    (H : CoherentHierarchy S T)
    (hnodes : ∀ n, H.nodes n = Set.range (fun t : T.tiles => a (t, n))) :
    ∀ F : Finset H.Node, Nonempty (LegalContext H F) := by
  classical
  have representatives (q : H.Node) : ∃ t : T.tiles, a (t, q.1) = q.2.val := by
    simpa only [hnodes q.1] using q.2.property
  choose rep hrep using representatives
  intro F
  let G := F.image (fun q => (rep q, q.1))
  obtain ⟨height, A, ψ, hcontext⟩ := (hgood G).2.2.2.2.2.1
  have hG (q : H.Node) (hq : q ∈ F) : (rep q, q.1) ∈ G :=
    Finset.mem_image_of_mem _ hq
  refine ⟨{
    height := height
    ty := A
    placement := ψ
    standard := ?_
    interior := ?_
    edges := ?_
  }⟩
  · intro q hq
    simpa only [hrep q] using (hcontext (rep q, q.1) (hG q hq)).1
  · intro q hq
    simpa only [hrep q] using (hcontext (rep q, q.1) (hG q hq)).2
  · intro q _ _
    simpa [FramedNode.move, FramedNode.child, AffineIsometryEquiv.trans_assoc] using
      congrArg (fun N : FramedNode S => N.move ψ) (H.child_eq q.1 q.2)

/-- Step 11 of the V4 proof of `exists_honest` (V4 1.12):
"the frame of t₀ obtained this way is φ₀ ∘ s ... gH = Q₀sH".
The chosen anchor variable supplies one coset for every recorded node. -/
private theorem exists_honest_step11_coset {S : SubstSystem d}
    (T : Tiling S) (t₀ : T.tiles) (a : T.tiles × ℕ → FramedNode S)
    (hgood : ∀ F, exists_honest_constraints T t₀ F a)
    (H : CoherentHierarchy S T)
    (hnodes : ∀ n, H.nodes n = Set.range (fun t : T.tiles => a (t, n))) :
    ∀ n N, N ∈ H.nodes n → ∃ R ∈ S.rotGroup,
      N.frame.linearIsometryEquiv = (a (t₀, 0)).frame.linearIsometryEquiv * R := by
  classical
  intro n N hN
  rw [hnodes n] at hN
  obtain ⟨t, rfl⟩ := hN
  exact (hgood {(t₀, 0), (t, n)}).2.2.2.2.2.2 (by simp) (t, n) (by simp)

/-- T8, V4 1.12: every member of the species has an honest hierarchy.
Existence is conditional only on actual membership in the defined species;
the underlying tiling is preserved exactly, with its typed physical tiles. -/
theorem exists_honest {S : SubstSystem d} (T : Tiling S) (hT : T ∈ S.Species) :
    ∃ U : HonestSource S, U.tiling = T := by
  obtain ⟨t, ht, _⟩ := T.cover 0
  let t₀ : T.tiles := ⟨t, ht⟩
  obtain ⟨a, ha, hgood⟩ := exists_honest_step8_assignment T hT t₀
  obtain ⟨H, hnodes⟩ := exists_honest_step9_hierarchy T t₀ a ha hgood
  exact ⟨{
    tiling := T
    mem_species := hT
    hierarchy := H
    contexts := exists_honest_step10_contexts T t₀ a hgood H hnodes
    coset := (a (t₀, 0)).frame.linearIsometryEquiv
    frames_in_coset := exists_honest_step11_coset T t₀ a hgood H hnodes
  }, rfl⟩

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
