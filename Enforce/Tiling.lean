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
  dsimp [move, ofFrame]
  rw [frame_carrier]
  dsimp [placedSet]
  rw [Set.image_image]
  rfl

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
  intro x
  have h := T.cover (g.symm x)
  rcases h with ⟨t, ht_in, hx_in_t⟩
  use t.move g
  constructor
  · exact Set.mem_image_of_mem (fun t => t.move g) ht_in
  · rw [PlacedTile.move_carrier]
    exact ⟨g.symm x, hx_in_t, by simp⟩

/-- T1, V4 §1.0 (H7): isometric motion preserves disjoint tile interiors. -/
theorem move_disjoint :
    ((fun t : PlacedTile S => t.move g) '' T.tiles).PairwiseDisjoint
      (fun t => interior t.carrier) := by
  rintro _ ⟨t, ht, rfl⟩ _ ⟨u, hu, rfl⟩ h_neq
  dsimp [Function.onFun]
  have ht_neq_u : t ≠ u := by
    intro h
    apply h_neq
    rw [h]
  have h_disj := T.disjoint ht hu ht_neq_u
  dsimp [Function.onFun] at h_disj
  rw [PlacedTile.move_carrier, PlacedTile.move_carrier]
  let e := g.toHomeomorph
  change Disjoint (interior (e '' t.carrier)) (interior (e '' u.carrier))
  rw [← e.image_interior, ← e.image_interior]
  exact Set.disjoint_image_of_injective e.injective h_disj

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


/-- Step 1 of the V4 proof of `species_eq_legal` (V4 7.4): a finite patch can be extended to cover the epsilon-thickening of its support. -/
private theorem species_eq_legal_step1_collar {S : SubstSystem d} (T : Tiling S)
    (P : Patch S) (hP : P.IsPatchOf T) {ε : ℝ} (_ : 0 < ε) :
    ∃ P' : Patch S, P'.IsPatchOf T ∧ P.tiles ⊆ P'.tiles ∧
      Metric.cthickening ε P.support ⊆ P'.support := by
  sorry

/-- Step 3 of the V4 proof of `species_eq_legal` (V4 7.4): legality of a larger patch implies legality of a subpatch. -/
private theorem species_eq_legal_step3_subset {S : SubstSystem d} {P P' : Patch S}
    (h : P.tiles ⊆ P'.tiles) (hl : IsLegal P') : IsLegal P := by
  rcases hl with ⟨n, A, ψ, h1⟩
  use n, A, ψ
  intro t ht
  exact h1 t (h ht)

/-- Step 4 of the V4 proof of `species_eq_legal` (V4 7.4): interior legality follows from legality of a patch covering an epsilon-thickening. -/
private theorem species_eq_legal_step4_interior {S : SubstSystem d} {P P' : Patch S}
    {ε : ℝ} (hε : 0 < ε) (hsub : P.tiles ⊆ P'.tiles)
    (hcov : Metric.cthickening ε P.support ⊆ P'.support) (hl : IsLegal P') :
    InteriorLegal P := by
  sorry

/-- T3, V4 7.4: ordinary legality and interior legality give exactly the
same whole-space species. The equivalence is asserted for all finite patches of
a tiling, rather than incorrectly for an isolated finite patch. -/
theorem species_eq_legal {S : SubstSystem d} (T : Tiling S) :
    T ∈ S.Species ↔ ∀ P : Patch S, P.IsPatchOf T → IsLegal P := by
  constructor
  · intro hT P hP
    have hInt : InteriorLegal P := hT P hP
    rcases hInt with ⟨n, A, ψ, h1, h2⟩
    exact ⟨n, A, ψ, h1⟩
  · intro hLeg P hP
    have he : (0:ℝ) < 1 := zero_lt_one
    obtain ⟨P', hP', hsub, hcov⟩ := species_eq_legal_step1_collar T P hP he
    have hl : IsLegal P' := hLeg P' hP'
    exact species_eq_legal_step4_interior he hsub hcov hl

/-- T2, V4 §1.0 (H7): the defined species is invariant under every Euclidean
isometry, including reflections. This does not impose covariance on a chosen lift. -/

private theorem pt_move_move {S : SubstSystem d} (t : PlacedTile S) (g h : Iso d) :
    (t.move g).move h = t.move (g.trans h) := by
  ext
  · simp [PlacedTile.move, PlacedTile.ofFrame]
  · rw [PlacedTile.move_carrier, PlacedTile.move_carrier, PlacedTile.move_carrier, Set.image_image]
    rfl

private theorem pt_move_refl {S : SubstSystem d} (t : PlacedTile S) :
    t.move (AffineIsometryEquiv.refl ℝ (E d)) = t := by
  ext
  · simp [PlacedTile.move, PlacedTile.ofFrame]
  · rw [PlacedTile.move_carrier]
    simp

private noncomputable def moveEquiv {S : SubstSystem d} (g : Iso d) : PlacedTile S ≃ PlacedTile S :=
  ⟨(·.move g), (·.move g.symm),
   fun t => by
     change (t.move g).move g.symm = t
     rw [pt_move_move]
     have h : g.trans g.symm = AffineIsometryEquiv.refl ℝ (E d) := by
       ext x
       simp
     rw [h, pt_move_refl],
   fun t => by
     change (t.move g.symm).move g = t
     rw [pt_move_move]
     have h : g.symm.trans g = AffineIsometryEquiv.refl ℝ (E d) := by
       ext x
       simp
     rw [h, pt_move_refl]⟩

private theorem move_interior_disjoint {S : SubstSystem d} (t s : PlacedTile S) (g : Iso d) :
  Disjoint (interior (t.move g).carrier) (interior (s.move g).carrier) ↔
  Disjoint (interior t.carrier) (interior s.carrier) := by
  rw [PlacedTile.move_carrier, PlacedTile.move_carrier]
  have h1 : interior (⇑g '' t.carrier) = ⇑g.toHomeomorph '' interior t.carrier := by
    exact (Homeomorph.image_interior g.toHomeomorph t.carrier).symm
  have h2 : interior (⇑g '' s.carrier) = ⇑g.toHomeomorph '' interior s.carrier := by
    exact (Homeomorph.image_interior g.toHomeomorph s.carrier).symm
  rw [h1, h2]
  exact Set.disjoint_image_iff g.toHomeomorph.injective

private noncomputable def movePatch {S : SubstSystem d} (P : Patch S) (g : Iso d) : Patch S where
  tiles := P.tiles.map (moveEquiv g).toEmbedding
  disjoint := by
    intro a ha b hb hab
    simp only [Finset.coe_map, Set.mem_image, Equiv.coe_toEmbedding, Finset.mem_coe] at ha hb
    obtain ⟨t, ht, rfl⟩ := ha
    obtain ⟨s, hs, rfl⟩ := hb
    have hneq : t ≠ s := fun h => hab (by rw [h])
    change Disjoint (interior (t.move g).carrier) (interior (s.move g).carrier)
    rw [move_interior_disjoint]
    exact P.disjoint ht hs hneq

private theorem movePatch_mem {S : SubstSystem d} (P : Patch S) (g : Iso d) (t : PlacedTile S) :
  t ∈ (movePatch P g).tiles ↔ ∃ t' ∈ P.tiles, t'.move g = t := by
  change t ∈ P.tiles.map (moveEquiv g).toEmbedding ↔ _
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨t', ht', rfl⟩
    exact ⟨t', ht', rfl⟩
  · rintro ⟨t', ht', rfl⟩
    exact ⟨t', ht', rfl⟩

private theorem movePatch_support {S : SubstSystem d} (P : Patch S) (g : Iso d) :
  (movePatch P g).support = g '' P.support := by
  dsimp [Patch.support, movePatch]
  ext x
  constructor
  · intro hx
    have ⟨t_moved, ht_moved, hx2⟩ := Set.mem_iUnion₂.mp hx
    simp only [Finset.mem_map, Equiv.coe_toEmbedding] at ht_moved
    obtain ⟨t, ht, rfl⟩ := ht_moved
    change x ∈ (t.move g).carrier at hx2
    rw [PlacedTile.move_carrier] at hx2
    obtain ⟨y, hy, rfl⟩ := hx2
    exact ⟨y, Set.mem_iUnion₂.mpr ⟨t, ht, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have ⟨t, ht, hy2⟩ := Set.mem_iUnion₂.mp hy
    apply Set.mem_iUnion₂.mpr
    use t.move g
    have hmem : t.move g ∈ P.tiles.map (moveEquiv g).toEmbedding := by
      rw [Finset.mem_map]
      exact ⟨t, ht, rfl⟩
    exact ⟨hmem, by rw [PlacedTile.move_carrier]; exact ⟨y, hy2, rfl⟩⟩

private theorem movePatch_mem_symm {S : SubstSystem d} (P : Patch S) (g : Iso d) (t : PlacedTile S) :
  t ∈ (movePatch P g).tiles ↔ t.move g.symm ∈ P.tiles := by
  rw [movePatch_mem]
  constructor
  · rintro ⟨t', ht', rfl⟩
    have h : (t'.move g).move g.symm = t' := by
      rw [pt_move_move]
      have h2 : g.trans g.symm = AffineIsometryEquiv.refl ℝ (E d) := by
        ext x
        simp
      rw [h2, pt_move_refl]
    rw [h]
    exact ht'
  · intro ht
    use t.move g.symm
    refine ⟨ht, ?_⟩
    change (t.move g.symm).move g = t
    rw [pt_move_move]
    have h : g.symm.trans g = AffineIsometryEquiv.refl ℝ (E d) := by
      ext x
      simp
    rw [h, pt_move_refl]

private theorem movePatch_isPatchOf {S : SubstSystem d} (P : Patch S) (T : Tiling S) (g : Iso d) :
  P.IsPatchOf T → (movePatch P g).IsPatchOf (T.move g) := by
  intro hP
  dsimp [Patch.IsPatchOf]
  intro t ht
  have hmem : t ∈ (movePatch P g).tiles := ht
  rw [movePatch_mem] at hmem
  obtain ⟨t', ht', rfl⟩ := hmem
  have hmem_T : t' ∈ T.tiles := hP ht'
  change t'.move g ∈ (T.move g).tiles
  dsimp [Tiling.move]
  exact Set.mem_image_of_mem _ hmem_T

private theorem movePatch_movePatch {S : SubstSystem d} (P : Patch S) (g : Iso d) :
  movePatch (movePatch P g) g.symm = P := by
  have heq : (movePatch (movePatch P g) g.symm).tiles = P.tiles := by
    ext t
    rw [movePatch_mem_symm]
    rw [movePatch_mem_symm]
    have h0 : g.symm.symm = g := by
      ext x
      simp
    have h1 : t.move g.symm.symm = t.move g := by
      rw [h0]
    rw [h1]
    have h2 : (t.move g).move g.symm = t := by
      rw [pt_move_move]
      have h3 : g.trans g.symm = AffineIsometryEquiv.refl ℝ (E d) := by
        ext x
        simp
      rw [h3, pt_move_refl]
    rw [h2]
  cases P
  dsimp at heq
  dsimp [movePatch]
  congr

private theorem interiorLegal_move {S : SubstSystem d} (P : Patch S) (g : Iso d) :
    InteriorLegal P → InteriorLegal (movePatch P g) := by
  rintro ⟨n, A, ψ, h1, h2⟩
  use n, A, g.symm.trans ψ
  constructor
  · intro t ht
    have hmem : t ∈ (movePatch P g).tiles := ht
    rw [movePatch_mem] at hmem
    obtain ⟨t', ht', rfl⟩ := hmem
    obtain ⟨w, hw⟩ := h1 t' ht'
    use w
    rw [← hw]
    rw [pt_move_move]
    have h : g.trans (g.symm.trans ψ) = ψ := by
      ext x
      simp
    rw [h]
  · rw [movePatch_support]
    change (g.symm.trans ψ) '' (g '' P.support) ⊆ interior (S.supertile n A)
    have h : (g.symm.trans ψ) '' (g '' P.support) = ψ '' P.support := by
      rw [← Set.image_comp]
      have h_eq : ⇑((AffineIsometryEquiv.symm g).trans ψ) ∘ ⇑g = ⇑ψ := by
        ext x
        simp
      rw [h_eq]
    rw [h]
    exact h2

private theorem species_move_mp {S : SubstSystem d} (T : Tiling S) (g : Iso d) (h : T ∈ S.Species) : T.move g ∈ S.Species := by
  dsimp [SubstSystem.Species]
  intro P hP
  let Q := movePatch P g.symm
  have hQ : Q.IsPatchOf T := by
    dsimp [Patch.IsPatchOf]
    intro t ht
    have hmem : t ∈ Q.tiles := ht
    change t ∈ (movePatch P g.symm).tiles at hmem
    rw [movePatch_mem] at hmem
    obtain ⟨t', ht', rfl⟩ := hmem
    have ht'_in_T_move : t' ∈ (T.move g).tiles := hP ht'
    dsimp [Tiling.move] at ht'_in_T_move
    obtain ⟨t0, ht0, ht0_eq⟩ := ht'_in_T_move
    have h_eq : t0.move g = t' := ht0_eq
    rw [← h_eq]
    have h_move : (t0.move g).move g.symm = t0 := by
      rw [pt_move_move]
      have hh : g.trans g.symm = AffineIsometryEquiv.refl ℝ (E d) := by
        ext x
        simp
      rw [hh, pt_move_refl]
    rw [h_move]
    exact ht0
  have h_legal_Q := h Q hQ
  have h_legal_Q_moved := interiorLegal_move Q g h_legal_Q
  have h_Q_moved_eq : movePatch Q g = P := by
    change movePatch (movePatch P g.symm) g = P
    have h_symm : g.symm.symm = g := by
      ext x
      simp
    have eq := movePatch_movePatch P g.symm
    rw [h_symm] at eq
    exact eq
  rw [h_Q_moved_eq] at h_legal_Q_moved
  exact h_legal_Q_moved

theorem species_move_iff {S : SubstSystem d} (T : Tiling S) (g : Iso d) :
    T.move g ∈ S.Species ↔ T ∈ S.Species := by
  constructor
  · intro h
    have h1 := species_move_mp (T.move g) g.symm h
    have heq : (T.move g).move g.symm = T := by
      cases T
      dsimp [Tiling.move]
      congr 1
      ext t
      simp only [Set.mem_image]
      constructor
      · rintro ⟨t', ⟨t0, ht0, rfl⟩, rfl⟩
        have h_move : (t0.move g).move g.symm = t0 := by
          rw [pt_move_move]
          have hh : g.trans g.symm = AffineIsometryEquiv.refl ℝ (E d) := by
            ext x
            simp
          rw [hh, pt_move_refl]
        rw [h_move]
        exact ht0
      · rintro ht
        use t.move g
        constructor
        · exact ⟨t, ht, rfl⟩
        · rw [pt_move_move]
          have hh : g.trans g.symm = AffineIsometryEquiv.refl ℝ (E d) := by
            ext x
            simp
          rw [hh, pt_move_refl]
    rw [heq] at h1
    exact h1
  · intro h
    exact species_move_mp T g h

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
  have H : ∃ t ∈ T.tiles, x ∈ interior t.carrier := ⟨t, ht, hx⟩
  dsimp [oldMarking]
  rw [dif_pos H]
  have h2 := Classical.choose_spec H
  obtain ⟨h_in, h_mem⟩ := h2
  have h_eq : Classical.choose H = t := by
    by_contra hc
    have h_disj := T.disjoint h_in ht hc
    have h_mem_inter : x ∈ interior (Classical.choose H).carrier ∩ interior t.carrier := ⟨h_mem, hx⟩
    exact Set.disjoint_iff.mp h_disj h_mem_inter
  rw [h_eq]

private theorem oldMarking_frontier_tile_regular {S : SubstSystem d} (t : PlacedTile S) :
    closure (interior t.carrier) = t.carrier := by
  rw [t.frame_carrier]
  change closure (interior (t.frame.toHomeomorph '' _)) = t.frame.toHomeomorph '' _
  rw [← t.frame.toHomeomorph.image_interior, ← t.frame.toHomeomorph.image_closure,
    (S.proto t.ty).regularClosed]

/-- T4, V4 §1.0 (H7): a point on any tile boundary receives `@`. -/
theorem oldMarking_frontier {S : SubstSystem d} (T : Tiling S)
    (t : PlacedTile S) (ht : t ∈ T.tiles) (x : E d) (hx : x ∈ frontier t.carrier) :
    oldMarking T x = none := by
  dsimp [oldMarking]
  split_ifs with H
  · obtain ⟨u, hu, hxu⟩ := H
    have h_ne : t ≠ u := by
      rintro rfl
      have h1 : x ∈ interior t.carrier := hxu
      have h_closed : IsClosed t.carrier := by
        rw [← oldMarking_frontier_tile_regular t]
        exact isClosed_closure
      have h2 : x ∉ interior t.carrier := fun h => (h_closed.frontier_eq ▸ hx).2 h
      exact h2 h1
    have hd : Disjoint (interior t.carrier) (interior u.carrier) := T.disjoint ht hu h_ne
    have h_front2 : x ∈ closure (interior t.carrier) := by
      have h_closed : IsClosed t.carrier := by
        rw [← oldMarking_frontier_tile_regular t]
        exact isClosed_closure
      have H_x_c : x ∈ t.carrier := h_closed.frontier_subset hx
      rwa [oldMarking_frontier_tile_regular t]
    have h_open_u : IsOpen (interior u.carrier) := isOpen_interior
    have h_mem_cl := mem_closure_iff.mp h_front2 (interior u.carrier) h_open_u hxu
    have h_empty : interior t.carrier ∩ interior u.carrier = ∅ := Set.eq_empty_of_subset_empty (Set.disjoint_iff.mp hd)
    rw [Set.inter_comm, h_empty] at h_mem_cl
    exact Set.not_nonempty_empty h_mem_cl
  · rfl

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

/-- At a fixed height, the expanded prototypes are again polyhedral manifold
domains, as used in V4 1.0(d): "placed copies of the finitely many σ^n A". -/
private def nodes_locallyFinite_step1_supertileDomain (n : ℕ) (A : S.ι) : PolyManifoldDomain d := by
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

/-- T6, V4 1.0(d): every fixed level is locally finite and meets bounded
sets in finitely many nodes. Closed supports, rather than interiors, are counted. -/
theorem nodes_locallyFinite (n : ℕ) :
    LocallyFinite (fun N : {N // N ∈ H.nodes n} => N.val.carrier n) ∧
      ∀ B : Set (E d), Bornology.IsBounded B →
        {N : {N // N ∈ H.nodes n} | (B ∩ N.val.carrier n).Nonempty}.Finite := by
  have hd : Pairwise (fun N M : {N // N ∈ H.nodes n} => Disjoint
      (interior (placedSet N.val.frame (nodes_locallyFinite_step1_supertileDomain n N.val.ty).carrier))
      (interior (placedSet M.val.frame (nodes_locallyFinite_step1_supertileDomain n M.val.ty).carrier))) := by
    intro N M hNM
    exact H.disjoint n N.property M.property (fun h => hNM (Subtype.ext h))
  exact locallyFinite_disjointInteriors (nodes_locallyFinite_step1_supertileDomain (S := S) n)
    (fun N : {N // N ∈ H.nodes n} => N.val.ty)
    (fun N : {N // N ∈ H.nodes n} => N.val.frame) hd

/-- T6, V4 1.0(d): a node is the union of the physical tiles it contains. -/
theorem node_union_tiles (n : ℕ) (N : FramedNode S) (hN : N ∈ H.nodes n) :
    N.carrier n = ⋃ t ∈ {t | t ∈ T.tiles ∧ t.carrier ⊆ N.carrier n}, t.carrier := by
  rw [H.native_tiles n N hN]
  have h1 : N.carrier n = ⋃ w : S.RoleWord N.ty n, ((S.nativeTile N.ty n w).move N.frame).toTile.carrier := by
    change N.frame '' S.supertile n N.ty = _
    rw [← S.native_cover N.ty n, Set.image_iUnion]
    congr 1
    ext w x
    simp only [Set.mem_image]
    dsimp [FramedNode.move, FramedNode.toTile, PlacedTile.ofFrame, placedSet]
    change x ∈ N.frame '' (S.nativeTile N.ty n w).carrier 0 ↔ x ∈ ((S.nativeTile N.ty n w).frame.trans N.frame) '' (S.proto (S.nativeTile N.ty n w).ty).carrier
    dsimp [FramedNode.carrier, placedSet, SubstSystem.supertile]
    constructor
    · rintro ⟨y, ⟨z, ⟨z0, hz0, rfl⟩, rfl⟩, rfl⟩
      exact ⟨z0, hz0, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(S.nativeTile N.ty n w).frame z, ⟨z, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
  rw [h1]
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨((S.nativeTile N.ty n w).move N.frame).toTile, ⟨w, rfl⟩, hw⟩
  · rintro ⟨t, ⟨w, rfl⟩, hw⟩
    exact ⟨w, hw⟩

/-- T6, V4 §1.0, Hierarchies: same-height nodes sharing an interior point
coincide as framed nodes, including their type and isometric frame. -/
theorem same_height_disjoint (n : ℕ) (N P : FramedNode S)
    (hN : N ∈ H.nodes n) (hP : P ∈ H.nodes n) (x : E d)
    (hxN : x ∈ interior (N.carrier n)) (hxP : x ∈ interior (P.carrier n)) :
    N = P := by
  by_contra h
  have hd := H.disjoint n hN hP h
  exact Set.disjoint_left.mp hd hxN hxP

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

/-- Step 1 of the V4 proof of `inflate` (V4 1.13(a)): "a tile `t = QRA' + τ` is mapped
to `Λt`". An affine isometry is its linear part plus its value at the origin. -/
private theorem inflate_step1_iso_apply (f : Iso d) (x : E d) :
    f x = f.linearIsometryEquiv x + f 0 := by
  have h := f.map_vadd 0 x
  simpa [vadd_eq_add] using h

/-- Step 1 of the V4 proof of `inflate` (V4 1.13(a)): "`σRσ⁻¹` ... Lemma 1.10(a)".
Conjugation by `σ` keeps elements of the compatible group orthogonal and in the group. -/
private theorem inflate_step1_conj {S : SubstSystem d} (R : Ortho d) (hR : R ∈ S.rotGroup) :
    ∃ R' ∈ S.rotGroup, ∀ x, R' x = S.σ (R (S.σ.symm x)) := by
  have hmem : linearConj S.σ 1 R.toLinearEquiv ∈
      (fun R : Ortho d => R.toLinearEquiv) '' (S.rotGroup : Set (Ortho d)) := by
    rw [← S.rotGroup_conj]
    exact ⟨R, hR, rfl⟩
  obtain ⟨R', hR', heq⟩ := hmem
  refine ⟨R', hR', fun x => ?_⟩
  have h := congrArg (fun e : E d ≃ₗ[ℝ] E d => e x) heq
  simp only [linearConj, zpow_neg, zpow_one] at h
  exact h

/-- Step 1 of the V4 proof of `inflate` (V4 1.13(a)): the linear part `Λ O σ⁻¹` of an
inflated frame. -/
private def inflate_step1_lin {S : SubstSystem d} (U : HonestSource S) (φ : Iso d) :
    E d ≃ₗ[ℝ] E d :=
  S.σ.symm.trans (φ.linearIsometryEquiv.toLinearEquiv.trans U.expansion)

/-- Step 1 of the V4 proof of `inflate` (V4 1.13(a)): the inflated frame
`x ↦ Λ (φ (σ⁻¹ x))`, which is an isometry whenever `φ` has orthogonal part in `Q H`. -/
private def inflate_step1_frame {S : SubstSystem d} (U : HonestSource S) (φ : Iso d) :
    Iso d := by
  classical
  exact if h : ∀ x, ‖inflate_step1_lin U φ x‖ = ‖x‖ then
    rigidMotion { inflate_step1_lin U φ with norm_map' := h } (U.expansion (φ 0)) else φ

/-- Step 1 of the V4 proof of `inflate` (V4 1.13(a)): "with orthogonal part
`Q σ R σ⁻¹ ∈ Q H`". The linear part of the inflated frame. -/
private theorem inflate_step1_lin_apply {S : SubstSystem d} (U : HonestSource S) (φ : Iso d)
    (R R' : Ortho d) (he : φ.linearIsometryEquiv = U.coset * R)
    (hR' : ∀ x, R' x = S.σ (R (S.σ.symm x))) (y : E d) :
    inflate_step1_lin U φ y = U.coset (R' y) := by
  rw [hR']
  change U.expansion (φ.linearIsometryEquiv (S.σ.symm y)) = _
  rw [he]
  change U.coset (S.σ (U.coset.symm (U.coset (R (S.σ.symm y))))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- Step 1 of the V4 proof of `inflate` (V4 1.13(a)): "`Λt = ... + Λτ`, here
`Λτ = QσQ⁻¹τ`". The inflated frame is `Λ ∘ φ ∘ σ⁻¹`. -/
private theorem inflate_step1_frame_apply {S : SubstSystem d} (U : HonestSource S) (φ : Iso d)
    (hφ : ∃ R ∈ S.rotGroup, φ.linearIsometryEquiv = U.coset * R) (x : E d) :
    inflate_step1_frame U φ x = U.expansion (φ (S.σ.symm x)) := by
  obtain ⟨R, hR, he⟩ := hφ
  obtain ⟨R', _, hR'x⟩ := inflate_step1_conj (S := S) R hR
  have h : ∀ y, ‖inflate_step1_lin U φ y‖ = ‖y‖ := by
    intro y
    rw [inflate_step1_lin_apply U φ R R' he hR'x]
    simp
  unfold inflate_step1_frame
  rw [dif_pos h]
  change inflate_step1_lin U φ x + U.expansion (φ 0) = _
  rw [inflate_step1_iso_apply φ (S.σ.symm x), map_add]
  rfl

/-- Step 1 of the V4 proof of `inflate` (V4 1.13(a)): "a placed copy of `σA'` with
orthogonal part `QσRσ⁻¹ ∈ QH`". Inflated frames stay in the common coset. -/
private theorem inflate_step1_frame_coset {S : SubstSystem d} (U : HonestSource S) (φ : Iso d)
    (hφ : ∃ R ∈ S.rotGroup, φ.linearIsometryEquiv = U.coset * R) :
    ∃ R ∈ S.rotGroup, (inflate_step1_frame U φ).linearIsometryEquiv = U.coset * R := by
  obtain ⟨R, hR, he⟩ := hφ
  obtain ⟨R', hR', hR'x⟩ := inflate_step1_conj (S := S) R hR
  refine ⟨R', hR', ?_⟩
  apply LinearIsometryEquiv.ext
  intro y
  have h1 := inflate_step1_iso_apply (inflate_step1_frame U φ) y
  rw [inflate_step1_frame_apply U φ ⟨R, hR, he⟩, inflate_step1_frame_apply U φ ⟨R, hR, he⟩,
    map_zero, inflate_step1_iso_apply φ (S.σ.symm y), map_add] at h1
  have h2 := add_right_cancel h1
  rw [← h2]
  change inflate_step1_lin U φ y = _
  rw [inflate_step1_lin_apply U φ R R' he hR'x]
  rfl

/-- Step 1 of the V4 proof of `inflate` (V4 1.13(a)): an old node with its inflated frame. -/
private def inflate_step1_node {S : SubstSystem d} (U : HonestSource S) (N : FramedNode S) :
    FramedNode S :=
  ⟨N.ty, inflate_step1_frame U N.frame⟩

/-- Step 1 of the V4 proof of `inflate` (V4 1.13(a)): "the old height-`n` nodes become
height-`(n+1)` nodes": `Λ(N)` as a node of one more height. -/
private theorem inflate_step1_carrier {S : SubstSystem d} (U : HonestSource S) (N : FramedNode S)
    (hN : ∃ R ∈ S.rotGroup, N.frame.linearIsometryEquiv = U.coset * R) (n : ℕ) :
    (inflate_step1_node U N).carrier (n + 1) = U.expansion '' N.carrier n := by
  change inflate_step1_frame U N.frame '' ((S.σ ^ (n + 1)) '' (S.proto N.ty).carrier) =
    U.expansion '' (N.frame '' ((S.σ ^ n) '' (S.proto N.ty).carrier))
  rw [Set.image_image, Set.image_image, Set.image_image]
  apply Set.image_congr
  intro x _
  rw [inflate_step1_frame_apply U N.frame hN, pow_succ', LinearEquiv.mul_apply,
    LinearEquiv.symm_apply_apply]

/-- Step 1 of the V4 proof of `inflate` (V4 1.13(a)): "(conjugated) frames": the
prototype frame of the inflated node is `Λ` after the old prototype frame. -/
private theorem inflate_step1_prototypeFrame {S : SubstSystem d} (U : HonestSource S)
    (N : FramedNode S) (hN : ∃ R ∈ S.rotGroup, N.frame.linearIsometryEquiv = U.coset * R)
    (n : ℕ) :
    (inflate_step1_node U N).prototypeFrame (n + 1) =
      (N.prototypeFrame n).trans U.expansion.toAffineEquiv := by
  apply AffineEquiv.ext
  intro x
  change inflate_step1_frame U N.frame ((S.σ ^ (n + 1)) x) = U.expansion (N.frame ((S.σ ^ n) x))
  rw [inflate_step1_frame_apply U N.frame hN, pow_succ', LinearEquiv.mul_apply,
    LinearEquiv.symm_apply_apply]

/-- Step 2 of the V4 proof of `inflate` (V4 1.13(a)): the placed child at height zero is
the prescribed child frame. -/
private theorem inflate_step2_placeChild_zero {S : SubstSystem d} {A : S.ι} (i : S.I A)
    (x : E d) : S.placeChild 0 i x = (S.child A i).frame x := by
  have h := exists_honest_step7_place_scaled (S := S) 0 i x
  simpa using h

/-- Step 2 of the V4 proof of `inflate` (V4 1.13(a)): "subdividing it by the
substitution gives native tiles with frames in `QH` (1.10(b))". -/
private theorem inflate_step2_child_coset {S : SubstSystem d} (U : HonestSource S)
    (N : FramedNode S) (hN : ∃ R ∈ S.rotGroup, N.frame.linearIsometryEquiv = U.coset * R)
    (n : ℕ) (i : S.I N.ty) :
    ∃ R ∈ S.rotGroup, (N.child n i).frame.linearIsometryEquiv = U.coset * R := by
  obtain ⟨R, hR, he⟩ := hN
  refine ⟨R * S.childRotation n i, S.rotGroup.mul_mem hR (S.rotGroup_spec.1 ⟨n, N.ty, i, rfl⟩), ?_⟩
  have h : (N.child n i).frame.linearIsometryEquiv =
      N.frame.linearIsometryEquiv * S.childRotation n i := by
    ext y
    rfl
  rw [h, he, mul_assoc]

/-- Step 2 of the V4 proof of `inflate` (V4 1.13(a)): "the old height-`n` nodes become
height-`(n+1)` nodes with the same roles, parents": inflation commutes with children. -/
private theorem inflate_step2_child_succ {S : SubstSystem d} (U : HonestSource S)
    (P : FramedNode S) (hP : ∃ R ∈ S.rotGroup, P.frame.linearIsometryEquiv = U.coset * R)
    (n : ℕ) (i : S.I P.ty) :
    (inflate_step1_node U P).child (n + 1) i = inflate_step1_node U (P.child n i) := by
  refine FramedNode.ext ?_ ?_
  · rfl
  apply AffineIsometryEquiv.ext
  intro x
  change inflate_step1_frame U P.frame (S.placeChild (n + 1) i x) =
    inflate_step1_frame U (P.child n i).frame x
  rw [inflate_step1_frame_apply U P.frame hP,
    inflate_step1_frame_apply U _ (inflate_step2_child_coset U P hP n i)]
  have h := exists_honest_step7_place_shift (S := S) 1 n i (S.σ.symm x)
  rw [Nat.add_comm 1 n, pow_one, LinearEquiv.apply_symm_apply] at h
  rw [h, LinearEquiv.symm_apply_apply]
  try rfl

/-- Step 2 of the V4 proof of `inflate` (V4 1.13(a)): "`Λ` is invertible": inflation
is injective on frames in the common coset. -/
private theorem inflate_step2_injective {S : SubstSystem d} (U : HonestSource S)
    (M N : FramedNode S) (hM : ∃ R ∈ S.rotGroup, M.frame.linearIsometryEquiv = U.coset * R)
    (hN : ∃ R ∈ S.rotGroup, N.frame.linearIsometryEquiv = U.coset * R)
    (h : inflate_step1_node U M = inflate_step1_node U N) : M = N := by
  have hty : M.ty = N.ty := by
    have h' := congrArg FramedNode.ty h
    exact h'
  have hfr := congrArg FramedNode.frame h
  refine FramedNode.ext hty ?_
  apply AffineIsometryEquiv.ext
  intro x
  have hx := congrArg (fun f : Iso d => f (S.σ x)) hfr
  change inflate_step1_frame U M.frame (S.σ x) = inflate_step1_frame U N.frame (S.σ x) at hx
  rw [inflate_step1_frame_apply U M.frame hM, inflate_step1_frame_apply U N.frame hN] at hx
  simp only [LinearEquiv.symm_apply_apply] at hx
  exact U.expansion.injective hx

/-- Step 2 of the V4 proof of `inflate` (V4 1.13(a)): "disjoint interiors are
preserved by the invertible linear map `Λ`". -/
private theorem inflate_step2_image_disjoint {S : SubstSystem d} (U : HonestSource S)
    (K L : Set (E d)) (h : Disjoint (interior K) (interior L)) :
    Disjoint (interior (U.expansion '' K)) (interior (U.expansion '' L)) := by
  let e := U.expansion.toContinuousLinearEquiv.toHomeomorph
  change Disjoint (interior (e '' K)) (interior (e '' L))
  rw [← e.image_interior, ← e.image_interior]
  exact Set.disjoint_image_of_injective e.injective h

/-- Step 2 of the V4 proof of `inflate` (V4 1.13(a)): a height-zero child carrier is the
placed prototype of the prescribed child. -/
private theorem inflate_step2_child_zero_carrier {S : SubstSystem d} (N : FramedNode S)
    (i : S.I N.ty) :
    (N.child 0 i).carrier 0 =
      N.frame '' placedSet (S.child N.ty i).frame (S.proto (S.child N.ty i).ty).carrier := by
  change ((S.placeChild 0 i).trans N.frame) '' (⇑(S.σ ^ 0) '' (S.proto (S.child N.ty i).ty).carrier) =
    N.frame '' ((S.child N.ty i).frame '' (S.proto (S.child N.ty i).ty).carrier)
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro x _
  change N.frame (S.placeChild 0 i ((S.σ ^ 0) x)) = N.frame ((S.child N.ty i).frame x)
  rw [pow_zero]
  exact congrArg N.frame (inflate_step2_placeChild_zero i x)

/-- Step 2 of the V4 proof of `inflate` (V4 1.13(a)): "each node subdivided by the
substitution": a height-one node is covered by its height-zero children. -/
private theorem inflate_step2_carrier_one {S : SubstSystem d} (N : FramedNode S) :
    N.carrier 1 ⊆ ⋃ i : S.I N.ty, (N.child 0 i).carrier 0 := by
  rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
  have hc : S.σ x ∈ S.σ '' (S.proto N.ty).carrier := ⟨x, hx, rfl⟩
  rw [S.children_cover N.ty] at hc
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hc
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  rw [inflate_step2_child_zero_carrier]
  refine ⟨S.σ x, hi, ?_⟩
  rw [pow_one]

/-- Step 3 of the V4 proof of `inflate` (V4 1.13(a)): the hierarchy `Λ(𝒩_n)` at heights
`n+1` and the new native ground tiles at height zero. -/
private def inflate_step3_nodes {S : SubstSystem d} (U : HonestSource S) :
    ℕ → Set (FramedNode S)
  | 0 => {M | ∃ P : {P // P ∈ U.hierarchy.nodes 0}, ∃ i : S.I P.val.ty,
      M = (inflate_step1_node U P.val).child 0 i}
  | n + 1 => {M | ∃ P : {P // P ∈ U.hierarchy.nodes n}, M = inflate_step1_node U P.val}

private theorem inflate_step3_mem_zero {S : SubstSystem d} (U : HonestSource S)
    {M : FramedNode S} (h : M ∈ inflate_step3_nodes U 0) :
    ∃ P : {P // P ∈ U.hierarchy.nodes 0}, ∃ i : S.I P.val.ty,
      M = (inflate_step1_node U P.val).child 0 i := h

private theorem inflate_step3_mem_succ {S : SubstSystem d} (U : HonestSource S) {n : ℕ}
    {M : FramedNode S} (h : M ∈ inflate_step3_nodes U (n + 1)) :
    ∃ P : {P // P ∈ U.hierarchy.nodes n}, M = inflate_step1_node U P.val := h

private theorem inflate_step3_mem_zero_intro {S : SubstSystem d} (U : HonestSource S)
    (P : {P // P ∈ U.hierarchy.nodes 0}) (i : S.I P.val.ty) :
    (inflate_step1_node U P.val).child 0 i ∈ inflate_step3_nodes U 0 := by
  show ∃ P' : {P // P ∈ U.hierarchy.nodes 0}, ∃ i' : S.I P'.val.ty,
    (inflate_step1_node U P.val).child 0 i = (inflate_step1_node U P'.val).child 0 i'
  exact ⟨P, i, rfl⟩

private theorem inflate_step3_mem_succ_intro {S : SubstSystem d} (U : HonestSource S) {n : ℕ}
    (P : {P // P ∈ U.hierarchy.nodes n}) :
    inflate_step1_node U P.val ∈ inflate_step3_nodes U (n + 1) := by
  show ∃ P' : {P // P ∈ U.hierarchy.nodes n},
    inflate_step1_node U P.val = inflate_step1_node U P'.val
  exact ⟨P, rfl⟩

/-- Step 3 of the V4 proof of `inflate` (V4 1.13(a)): "The frame coset is `QH` again". -/
private theorem inflate_step3_coset {S : SubstSystem d} (U : HonestSource S) :
    ∀ n N, N ∈ inflate_step3_nodes U n →
      ∃ R ∈ S.rotGroup, N.frame.linearIsometryEquiv = U.coset * R := by
  intro n N hN
  cases n with
  | zero =>
    obtain ⟨P, i, rfl⟩ := inflate_step3_mem_zero U hN
    exact inflate_step2_child_coset U (inflate_step1_node U P.val)
      (inflate_step1_frame_coset U _ (U.frames_in_coset 0 P.val P.property)) 0 i
  | succ n =>
    obtain ⟨P, rfl⟩ := inflate_step3_mem_succ U hN
    exact inflate_step1_frame_coset U _ (U.frames_in_coset n P.val P.property)

/-- Step 3 of the V4 proof of `inflate` (V4 1.13(a)): "Coverage ... preserved by the
invertible linear map `Λ`", including the new native subdivision. -/
private theorem inflate_step3_cover {S : SubstSystem d} (U : HonestSource S) :
    ∀ n x, ∃ N ∈ inflate_step3_nodes U n, x ∈ N.carrier n := by
  intro n x
  cases n with
  | zero =>
    obtain ⟨P, hP, hx⟩ := U.hierarchy.cover 0 (U.expansion.symm x)
    have hPc := U.frames_in_coset 0 P hP
    have hx1 : x ∈ (inflate_step1_node U P).carrier 1 := by
      rw [inflate_step1_carrier U P hPc 0]
      exact ⟨_, hx, LinearEquiv.apply_symm_apply _ _⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (inflate_step2_carrier_one _ hx1)
    exact ⟨_, inflate_step3_mem_zero_intro U ⟨P, hP⟩ i, hi⟩
  | succ n =>
    obtain ⟨P, hP, hx⟩ := U.hierarchy.cover n (U.expansion.symm x)
    refine ⟨inflate_step1_node U P, inflate_step3_mem_succ_intro U ⟨P, hP⟩, ?_⟩
    rw [inflate_step1_carrier U P (U.frames_in_coset n P hP) n]
    exact ⟨_, hx, LinearEquiv.apply_symm_apply _ _⟩

/-- Step 3 of the V4 proof of `inflate` (V4 1.13(a)): a new ground tile lies in the
inflation of its old parent tile. -/
private theorem inflate_step3_zero_subset {S : SubstSystem d} (U : HonestSource S)
    (P : FramedNode S) (hP : ∃ R ∈ S.rotGroup, P.frame.linearIsometryEquiv = U.coset * R)
    (i : S.I P.ty) :
    ((inflate_step1_node U P).child 0 i).carrier 0 ⊆ U.expansion '' P.carrier 0 := by
  rw [← inflate_step1_carrier U P hP 0]
  exact exists_honest_step7_child_subset (inflate_step1_node U P) 0 i

/-- Step 3 of the V4 proof of `inflate` (V4 1.13(a)): "disjoint interiors are preserved
by the invertible linear map `Λ`", also for the new native subdivision. -/
private theorem inflate_step3_disjoint {S : SubstSystem d} (U : HonestSource S) :
    ∀ n, (inflate_step3_nodes U n).PairwiseDisjoint (fun N => interior (N.carrier n)) := by
  intro n
  cases n with
  | zero =>
    intro M hM M' hM' hne
    obtain ⟨P, i, rfl⟩ := inflate_step3_mem_zero U hM
    obtain ⟨P', i', rfl⟩ := inflate_step3_mem_zero U hM'
    show Disjoint (interior (((inflate_step1_node U P.val).child 0 i).carrier 0))
      (interior (((inflate_step1_node U P'.val).child 0 i').carrier 0))
    by_cases hPP : P = P'
    · subst hPP
      have hii : i ≠ i' := fun h => hne (h ▸ rfl)
      rw [inflate_step2_child_zero_carrier, inflate_step2_child_zero_carrier]
      let e := (inflate_step1_node U P.val).frame.toHomeomorph
      change Disjoint (interior (e '' _)) (interior (e '' _))
      rw [← e.image_interior, ← e.image_interior]
      exact Set.disjoint_image_of_injective e.injective
        (S.children_disjoint (inflate_step1_node U P.val).ty hii)
    · have hPv : P.val ≠ P'.val := fun h => hPP (Subtype.ext h)
      have hd := inflate_step2_image_disjoint U _ _
        (U.hierarchy.disjoint 0 P.property P'.property hPv)
      exact hd.mono
        (interior_mono (inflate_step3_zero_subset U P.val
          (U.frames_in_coset 0 P.val P.property) i))
        (interior_mono (inflate_step3_zero_subset U P'.val
          (U.frames_in_coset 0 P'.val P'.property) i'))
  | succ n =>
    intro M hM M' hM' hne
    obtain ⟨P, rfl⟩ := inflate_step3_mem_succ U hM
    obtain ⟨P', rfl⟩ := inflate_step3_mem_succ U hM'
    have hPv : P.val ≠ P'.val := fun h => hne (h ▸ rfl)
    show Disjoint (interior ((inflate_step1_node U P.val).carrier (n + 1)))
      (interior ((inflate_step1_node U P'.val).carrier (n + 1)))
    rw [inflate_step1_carrier U P.val (U.frames_in_coset n P.val P.property),
      inflate_step1_carrier U P'.val (U.frames_in_coset n P'.val P'.property)]
    exact inflate_step2_image_disjoint U _ _ (U.hierarchy.disjoint n P.property P'.property hPv)

/-- Step 4 of the V4 proof of `inflate` (V4 1.13(a)): the new tiling `Λ(T)` with the
new native ground tiles. -/
private def inflate_step4_tiling {S : SubstSystem d} (U : HonestSource S) : Tiling S where
  tiles := {t | ∃ N ∈ inflate_step3_nodes U 0, N.toTile = t}
  cover := by
    intro x
    obtain ⟨N, hN, hx⟩ := inflate_step3_cover U 0 x
    refine ⟨N.toTile, ⟨N, hN, rfl⟩, ?_⟩
    rw [← exists_honest_step7_zero_carrier]
    exact hx
  disjoint := by
    rintro t ⟨N, hN, rfl⟩ u ⟨M, hM, rfl⟩ hne
    have hNM : N ≠ M := fun h => hne (h ▸ rfl)
    show Disjoint (interior N.toTile.carrier) (interior M.toTile.carrier)
    rw [← exists_honest_step7_zero_carrier, ← exists_honest_step7_zero_carrier]
    exact inflate_step3_disjoint U 0 hN hM hNM

/-- Step 5 of the V4 proof of `inflate` (V4 1.13(a)): "their parents in the new
indexing, plus the new tiles' parents". -/
private def inflate_step5_parent {S : SubstSystem d} (U : HonestSource S) :
    ∀ n, {N // N ∈ inflate_step3_nodes U n} → {P // P ∈ inflate_step3_nodes U (n + 1)}
  | 0, N => ⟨inflate_step1_node U (Classical.choose (inflate_step3_mem_zero U N.2)).val,
      inflate_step3_mem_succ_intro U (Classical.choose (inflate_step3_mem_zero U N.2))⟩
  | n + 1, N => ⟨inflate_step1_node U
        (U.hierarchy.parent n (Classical.choose (inflate_step3_mem_succ U N.2))).val,
      inflate_step3_mem_succ_intro U
        (U.hierarchy.parent n (Classical.choose (inflate_step3_mem_succ U N.2)))⟩

/-- Step 5 of the V4 proof of `inflate` (V4 1.13(a)): "the same roles". -/
private def inflate_step5_role {S : SubstSystem d} (U : HonestSource S) :
    ∀ n N, S.I (inflate_step5_parent U n N).val.ty
  | 0, N => Classical.choose (Classical.choose_spec (inflate_step3_mem_zero U N.2))
  | n + 1, N => U.hierarchy.role n (Classical.choose (inflate_step3_mem_succ U N.2))

/-- Step 5 of the V4 proof of `inflate` (V4 1.13(a)): the chosen preimage of an inflated
node is the node itself. -/
private theorem inflate_step5_choose_succ {S : SubstSystem d} (U : HonestSource S) {n : ℕ}
    (N₀ : {P // P ∈ U.hierarchy.nodes n})
    (h : inflate_step1_node U N₀.val ∈ inflate_step3_nodes U (n + 1)) :
    Classical.choose (inflate_step3_mem_succ U h) = N₀ := by
  have hs := Classical.choose_spec (inflate_step3_mem_succ U h)
  apply Subtype.ext
  exact (inflate_step2_injective U _ _ (U.frames_in_coset n N₀.val N₀.property)
    (U.frames_in_coset n _ (Classical.choose (inflate_step3_mem_succ U h)).property) hs).symm

/-- Step 5 of the V4 proof of `inflate` (V4 1.13(a)): "with the same ... parents". -/
private theorem inflate_step5_parent_succ {S : SubstSystem d} (U : HonestSource S) {n : ℕ}
    (N₀ : {P // P ∈ U.hierarchy.nodes n})
    (h : inflate_step1_node U N₀.val ∈ inflate_step3_nodes U (n + 1)) :
    inflate_step5_parent U (n + 1) ⟨_, h⟩ =
      ⟨inflate_step1_node U (U.hierarchy.parent n N₀).val,
        inflate_step3_mem_succ_intro U (U.hierarchy.parent n N₀)⟩ := by
  apply Subtype.ext
  show inflate_step1_node U
    (U.hierarchy.parent n (Classical.choose (inflate_step3_mem_succ U h))).val = _
  rw [inflate_step5_choose_succ U N₀ h]

/-- Step 5 of the V4 proof of `inflate` (V4 1.13(a)): "with the same roles". -/
private theorem inflate_step5_role_succ {S : SubstSystem d} (U : HonestSource S) {n : ℕ}
    (N₀ : {P // P ∈ U.hierarchy.nodes n})
    (h : inflate_step1_node U N₀.val ∈ inflate_step3_nodes U (n + 1)) :
    (⟨(inflate_step5_parent U (n + 1) ⟨_, h⟩).val.ty,
        inflate_step5_role U (n + 1) ⟨_, h⟩⟩ : S.Role) =
      ⟨(U.hierarchy.parent n N₀).val.ty, U.hierarchy.role n N₀⟩ := by
  show (⟨(U.hierarchy.parent n (Classical.choose (inflate_step3_mem_succ U h))).val.ty,
      U.hierarchy.role n (Classical.choose (inflate_step3_mem_succ U h))⟩ : S.Role) = _
  rw [inflate_step5_choose_succ U N₀ h]

/-- Step 5 of the V4 proof of `inflate` (V4 1.13(a)): exact child equations. -/
private theorem inflate_step5_child_eq {S : SubstSystem d} (U : HonestSource S) :
    ∀ n N, N.val = (inflate_step5_parent U n N).val.child n (inflate_step5_role U n N) := by
  intro n N
  cases n with
  | zero =>
    exact Classical.choose_spec (Classical.choose_spec (inflate_step3_mem_zero U N.2))
  | succ n =>
    let N₁ := Classical.choose (inflate_step3_mem_succ U N.2)
    have hN₁ : N.val = inflate_step1_node U N₁.val :=
      Classical.choose_spec (inflate_step3_mem_succ U N.2)
    show N.val = (inflate_step1_node U (U.hierarchy.parent n N₁).val).child (n + 1)
      (U.hierarchy.role n N₁)
    rw [inflate_step2_child_succ U _ (U.frames_in_coset (n + 1) _
      (U.hierarchy.parent n N₁).property), ← U.hierarchy.child_eq n N₁]
    exact hN₁

/-- Step 5 of the V4 proof of `inflate` (V4 1.13(a)): all prescribed children occur. -/
private theorem inflate_step5_children_mem {S : SubstSystem d} (U : HonestSource S) :
    ∀ n P, P ∈ inflate_step3_nodes U (n + 1) →
      ∀ i : S.I P.ty, P.child n i ∈ inflate_step3_nodes U n := by
  intro n P hP i
  obtain ⟨P₀, rfl⟩ := inflate_step3_mem_succ U hP
  cases n with
  | zero => exact inflate_step3_mem_zero_intro U P₀ i
  | succ n =>
    rw [inflate_step2_child_succ U _ (U.frames_in_coset (n + 1) P₀.val P₀.property)]
    exact inflate_step3_mem_succ_intro U
      ⟨P₀.val.child n i, U.hierarchy.children_mem n P₀.val P₀.property i⟩

/-- Step 5 of the V4 proof of `inflate` (V4 1.13(a)): a node belongs to only one parent. -/
private theorem inflate_step5_parent_unique {S : SubstSystem d} (U : HonestSource S) :
    ∀ n N P, P ∈ inflate_step3_nodes U (n + 1) →
      (∃ i : S.I P.ty, N.val = P.child n i) → P = (inflate_step5_parent U n N).val := by
  intro n N P hP hNP
  obtain ⟨i, hi⟩ := hNP
  obtain ⟨P₀, rfl⟩ := inflate_step3_mem_succ U hP
  cases n with
  | zero =>
    let P₁ := Classical.choose (inflate_step3_mem_zero U N.2)
    obtain ⟨i₁, hi₁⟩ := Classical.choose_spec (inflate_step3_mem_zero U N.2)
    show inflate_step1_node U P₀.val = inflate_step1_node U P₁.val
    by_contra hne
    have hPv : P₀.val ≠ P₁.val := fun h => hne (h ▸ rfl)
    have hd := inflate_step2_image_disjoint U _ _
      (U.hierarchy.disjoint 0 P₀.property P₁.property hPv)
    obtain ⟨x, hx⟩ := exists_honest_step7_tile_interior N.val.toTile
    rw [← exists_honest_step7_zero_carrier] at hx
    have hx₀ : x ∈ interior (U.expansion '' P₀.val.carrier 0) := by
      apply interior_mono (inflate_step3_zero_subset U P₀.val
        (U.frames_in_coset 0 P₀.val P₀.property) i)
      rw [← hi]
      exact hx
    have hx₁ : x ∈ interior (U.expansion '' P₁.val.carrier 0) := by
      apply interior_mono (inflate_step3_zero_subset U P₁.val
        (U.frames_in_coset 0 P₁.val P₁.property) i₁)
      rw [← hi₁]
      exact hx
    exact Set.disjoint_left.mp hd hx₀ hx₁
  | succ n =>
    let N₁ := Classical.choose (inflate_step3_mem_succ U N.2)
    have hN₁ : N.val = inflate_step1_node U N₁.val :=
      Classical.choose_spec (inflate_step3_mem_succ U N.2)
    show inflate_step1_node U P₀.val = inflate_step1_node U (U.hierarchy.parent n N₁).val
    rw [inflate_step2_child_succ U _ (U.frames_in_coset (n + 1) P₀.val P₀.property), hN₁] at hi
    have hc := U.hierarchy.children_mem n P₀.val P₀.property i
    have heq := inflate_step2_injective U _ _ (U.frames_in_coset n N₁.val N₁.property)
      (U.frames_in_coset n _ hc) hi
    rw [U.hierarchy.parent_unique n N₁ P₀.val P₀.property ⟨i, heq⟩]

/-- Step 6 of the V4 proof of `inflate` (V4 1.13(a)): "each node subdivided by the
substitution": every native framed tile of a node is a ground node. -/
private theorem inflate_step6_native_mem {S : SubstSystem d} (nodes : ℕ → Set (FramedNode S))
    (hc : ∀ n P, P ∈ nodes (n + 1) → ∀ i : S.I P.ty, P.child n i ∈ nodes n) :
    ∀ (k h : ℕ) (N : FramedNode S), N ∈ nodes (h + k) → ∀ w : S.RoleWord N.ty k,
      (S.descendantNode N.ty h k w).move N.frame ∈ nodes h := by
  intro k
  induction k with
  | zero =>
    intro h N hN w
    have heq : (S.descendantNode N.ty h 0 w).move N.frame = N := by
      refine FramedNode.ext ?_ ?_
      · rfl
      apply AffineIsometryEquiv.ext
      intro x
      rfl
    rw [heq]
    exact hN
  | succ k ih =>
    intro h N hN w
    have heq : (S.descendantNode N.ty h (k + 1) w).move N.frame =
        (S.descendantNode (N.child (h + k) w.1).ty h k w.2).move
          (N.child (h + k) w.1).frame := by
      refine FramedNode.ext ?_ ?_
      · rfl
      apply AffineIsometryEquiv.ext
      intro x
      rfl
    rw [heq]
    exact ih h (N.child (h + k) w.1) (hc (h + k) N hN w.1) w.2

/-- Step 6 of the V4 proof of `inflate` (V4 1.13(a)): "The target's coherent native-tile
condition prescribes the ground subdivision": the tiles inside a node are its native tiles. -/
private theorem inflate_step6_native_tiles {S : SubstSystem d} (T : Tiling S)
    (nodes : ℕ → Set (FramedNode S))
    (hground : ∀ N ∈ nodes 0, N.toTile ∈ T.tiles)
    (hc : ∀ n P, P ∈ nodes (n + 1) → ∀ i : S.I P.ty, P.child n i ∈ nodes n)
    (n : ℕ) (N : FramedNode S) (hN : N ∈ nodes n) :
    {t | t ∈ T.tiles ∧ t.carrier ⊆ N.carrier n} =
      {t | ∃ w : S.RoleWord N.ty n, ((S.nativeTile N.ty n w).move N.frame).toTile = t} := by
  classical
  have hleaves (w : S.RoleWord N.ty n) :
      ((S.nativeTile N.ty n w).move N.frame).toTile ∈ T.tiles :=
    hground _ (inflate_step6_native_mem nodes hc n 0 N (by simpa using hN) w)
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
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp
      (exists_honest_step7_saturation s T.tiles T.disjoint hs t ht hsupp)
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨hleaves w, exists_honest_step4_native_subset N n w⟩

/-- Step 6 of the V4 proof of `inflate` (V4 1.13(a)): the inflated coherent hierarchy. -/
private def inflate_step6_hierarchy {S : SubstSystem d} (U : HonestSource S) :
    CoherentHierarchy S (inflate_step4_tiling U) where
  nodes := inflate_step3_nodes U
  ground := rfl
  cover := inflate_step3_cover U
  disjoint := inflate_step3_disjoint U
  parent := inflate_step5_parent U
  role := inflate_step5_role U
  child_eq := inflate_step5_child_eq U
  children_mem := inflate_step5_children_mem U
  parent_unique := inflate_step5_parent_unique U
  native_tiles := inflate_step6_native_tiles (inflate_step4_tiling U) (inflate_step3_nodes U)
    (fun N hN => show ∃ M ∈ inflate_step3_nodes U 0, M.toTile = N.toTile from ⟨N, hN, rfl⟩)
    (inflate_step5_children_mem U)

/-- Step 7 of the V4 proof of `inflate` (V4 1.13(a)): "a finite set of new nodes lies in
the inflation of a finite set of old nodes (their parents in the new indexing, plus the
new tiles' parents)". -/
private theorem inflate_step7_pre {S : SubstSystem d} (U : HonestSource S)
    (q : Σ n : ℕ, {N // N ∈ inflate_step3_nodes U n}) :
    ∃ p : U.hierarchy.Node,
      (q.1 = 0 ∧ p.1 = 0 ∧ ∃ i : S.I p.2.val.ty,
        q.2.val = (inflate_step1_node U p.2.val).child 0 i) ∨
      (q.1 = p.1 + 1 ∧ q.2.val = inflate_step1_node U p.2.val) := by
  rcases q with ⟨_ | n, N⟩
  · obtain ⟨P, i, hi⟩ := inflate_step3_mem_zero U N.2
    exact ⟨⟨0, P⟩, Or.inl ⟨rfl, rfl, i, hi⟩⟩
  · obtain ⟨P, hP⟩ := inflate_step3_mem_succ U N.2
    exact ⟨⟨n, P⟩, Or.inr ⟨rfl, hP⟩⟩

/-- Step 7 of the V4 proof of `inflate` (V4 1.13(a)): one height up, descendant frames
are conjugated by `σ`. -/
private theorem inflate_step7_desc_shift {S : SubstSystem d} (A : S.ι) (n k : ℕ)
    (w : S.RoleWord A k) (z : E d) :
    (S.descendantNode A (n + 1) k w).frame (S.σ z) =
      S.σ ((S.descendantNode A n k w).frame z) := by
  have h1 := exists_honest_step7_descendant_scaled A (n + 1) k w ((S.σ ^ n).symm z)
  have h2 := exists_honest_step7_descendant_scaled A n k w ((S.σ ^ n).symm z)
  rw [LinearEquiv.apply_symm_apply] at h2
  rw [pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    LinearEquiv.apply_symm_apply] at h1
  rw [h1, h2]

/-- Step 7 of the V4 proof of `inflate` (V4 1.13(a)): "`σ^{n+1}A`" is `σ` of `σ^n A`. -/
private theorem inflate_step7_supertile_succ {S : SubstSystem d} (h : ℕ) (A : S.ι) :
    S.supertile (h + 1) A = S.σ '' S.supertile h A := by
  unfold SubstSystem.supertile
  rw [Set.image_image]
  apply Set.image_congr
  intro x _
  rw [pow_succ', LinearEquiv.mul_apply]

/-- Step 7 of the V4 proof of `inflate` (V4 1.13(a)): "the legal context for the inflated
patch is `σ^{n+1}A` with the isometry `ψ' = σψΛ⁻¹`". -/
private theorem inflate_step7_inflated {S : SubstSystem d} (U : HonestSource S)
    (A : S.ι) (height n : ℕ) (ψ ψ' : Iso d)
    (hψ' : ∀ y, ψ' (U.expansion y) = S.σ (ψ y)) (N : FramedNode S)
    (hN : ∃ R ∈ S.rotGroup, N.frame.linearIsometryEquiv = U.coset * R)
    (hstd : S.IsStandardNode A height n (N.move ψ))
    (hint : ψ '' N.carrier n ⊆ interior (S.supertile height A)) :
    S.IsStandardNode A (height + 1) (n + 1) ((inflate_step1_node U N).move ψ') ∧
      ψ' '' (inflate_step1_node U N).carrier (n + 1) ⊆
        interior (S.supertile (height + 1) A) := by
  constructor
  · obtain ⟨k, hk, w, hw⟩ := hstd
    refine ⟨k, by omega, w, ?_⟩
    apply FramedNode.ext
    · have hty := congrArg FramedNode.ty hw
      rw [exists_honest_step7_descendant_type] at hty ⊢
      exact hty
    · apply AffineIsometryEquiv.ext
      intro x
      have hfr := congrArg FramedNode.frame hw
      change ψ' (inflate_step1_frame U N.frame x) = _
      rw [inflate_step1_frame_apply U N.frame hN, hψ']
      rw [show x = S.σ (S.σ.symm x) from (LinearEquiv.apply_symm_apply _ _).symm,
        inflate_step7_desc_shift, LinearEquiv.symm_apply_apply, ← hfr]
      rfl
  · rw [inflate_step1_carrier U N hN n, Set.image_image]
    have hf : (fun y => ψ' (U.expansion y)) = fun y => S.σ (ψ y) := funext hψ'
    rw [hf, ← Set.image_image (fun y => S.σ y) ψ, inflate_step7_supertile_succ]
    let e := S.σ.toContinuousLinearEquiv.toHomeomorph
    change e '' (ψ '' N.carrier n) ⊆ interior (e '' S.supertile height A)
    rw [← e.image_interior]
    exact Set.image_mono hint

/-- Step 7 of the V4 proof of `inflate` (V4 1.13(a)): "Interior legality: ... conjugating"
gives a legal context for every finite set of new nodes. -/
private theorem inflate_step7_contexts {S : SubstSystem d} (U : HonestSource S) :
    ∀ F : Finset (inflate_step6_hierarchy U).Node,
      Nonempty (LegalContext (inflate_step6_hierarchy U) F) := by
  classical
  intro F
  choose pre hpre using inflate_step7_pre U
  obtain ⟨B, hB, -⟩ := U.hierarchy.cover 0 0
  have hBc := U.frames_in_coset 0 B hB
  let b : U.hierarchy.Node := ⟨0, ⟨B, hB⟩⟩
  let G : Finset U.hierarchy.Node := insert b (F.image pre)
  obtain ⟨C⟩ := U.contexts G
  obtain ⟨k, -, w, hw⟩ := C.standard b (Finset.mem_insert_self _ _)
  let ψ' : Iso d :=
    (inflate_step1_frame U B.frame).symm.trans (S.descendantNode C.ty 1 k w).frame
  have hψ' : ∀ y, ψ' (U.expansion y) = S.σ (C.placement y) := by
    intro y
    have h1 : (inflate_step1_frame U B.frame).symm (U.expansion y) = S.σ (B.frame.symm y) := by
      apply (inflate_step1_frame U B.frame).injective
      rw [AffineIsometryEquiv.apply_symm_apply, inflate_step1_frame_apply U B.frame hBc,
        LinearEquiv.symm_apply_apply, AffineIsometryEquiv.apply_symm_apply]
    have h2 : (S.descendantNode C.ty 0 k w).frame (B.frame.symm y) = C.placement y := by
      change (S.descendantNode C.ty 0 k w).frame (B.frame.symm y) = _
      rw [← hw]
      change C.placement (B.frame (B.frame.symm y)) = _
      rw [AffineIsometryEquiv.apply_symm_apply]
    change (S.descendantNode C.ty 1 k w).frame
      ((inflate_step1_frame U B.frame).symm (U.expansion y)) = _
    rw [h1, inflate_step7_desc_shift C.ty 0 k w, h2]
  have key : ∀ q ∈ F,
      S.IsStandardNode C.ty (C.height + 1) q.1 (q.2.val.move ψ') ∧
        ψ' '' q.2.val.carrier q.1 ⊆ interior (S.supertile (C.height + 1) C.ty) := by
    rintro ⟨n, N⟩ hq
    have hc := hpre ⟨n, N⟩
    have hmem : pre ⟨n, N⟩ ∈ G := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hq)
    generalize pre ⟨n, N⟩ = p at hc hmem
    rcases p with ⟨m, P⟩
    rcases hc with ⟨hn, hm, i, hi⟩ | ⟨hn, hi⟩
    · simp only at hn hm hi
      subst hn
      subst hm
      have hinf := inflate_step7_inflated U C.ty C.height 0 C.placement ψ' hψ' P.val
        (U.frames_in_coset 0 P.val P.property) (C.standard ⟨0, P⟩ hmem)
        (C.interior ⟨0, P⟩ hmem)
      show S.IsStandardNode C.ty (C.height + 1) 0 (N.val.move ψ') ∧
        ψ' '' N.val.carrier 0 ⊆ interior (S.supertile (C.height + 1) C.ty)
      rw [hi]
      refine ⟨?_, ?_⟩
      · rw [exists_honest_step7_move_child]
        exact exists_honest_step7_standard_child _ _ 0 _ hinf.1 i
      · exact (Set.image_mono (exists_honest_step7_child_subset
          (inflate_step1_node U P.val) 0 i)).trans hinf.2
    · simp only at hn hi
      subst hn
      have hinf := inflate_step7_inflated U C.ty C.height m C.placement ψ' hψ' P.val
        (U.frames_in_coset m P.val P.property) (C.standard ⟨m, P⟩ hmem)
        (C.interior ⟨m, P⟩ hmem)
      show S.IsStandardNode C.ty (C.height + 1) (m + 1) (N.val.move ψ') ∧
        ψ' '' N.val.carrier (m + 1) ⊆ interior (S.supertile (C.height + 1) C.ty)
      rw [hi]
      exact hinf
  exact ⟨{
    height := C.height + 1
    ty := C.ty
    placement := ψ'
    standard := fun q hq => (key q hq).1
    interior := fun q hq => (key q hq).2
    edges := fun q _ _ => congrArg (fun N : FramedNode S => N.move ψ')
      ((inflate_step6_hierarchy U).child_eq q.1 q.2) }⟩

/-- Step 8 of the V4 proof of `inflate` (V4 1.13(a)): "Interior legality" of every finite
patch follows from the legal contexts of its ground nodes. -/
private theorem inflate_step8_species {S : SubstSystem d} {T : Tiling S}
    (H : CoherentHierarchy S T) (hctx : ∀ F : Finset H.Node, Nonempty (LegalContext H F)) :
    T ∈ S.Species := by
  classical
  intro P hP
  have hnode : ∀ t ∈ P.tiles, ∃ N : {N // N ∈ H.nodes 0}, N.val.toTile = t := by
    intro t ht
    have h : t ∈ T.tiles := hP ht
    rw [← H.ground] at h
    obtain ⟨N, hN, rfl⟩ := h
    exact ⟨⟨N, hN⟩, rfl⟩
  choose f hf using hnode
  let F : Finset H.Node := P.tiles.attach.image (fun t => ⟨0, f t.val t.property⟩)
  obtain ⟨C⟩ := hctx F
  have hq (t : PlacedTile S) (ht : t ∈ P.tiles) : (⟨0, f t ht⟩ : H.Node) ∈ F :=
    Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩
  refine ⟨C.height, C.ty, C.placement, ?_, ?_⟩
  · intro t ht
    obtain ⟨w, hw⟩ := exists_honest_step7_standard_ground C.ty C.height _
      (C.standard _ (hq t ht))
    refine ⟨w, ?_⟩
    rw [← hf t ht, ← exists_honest_step7_move_toTile]
    exact congrArg FramedNode.toTile hw
  · rintro y ⟨x, hx, rfl⟩
    simp only [Patch.support, Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    apply C.interior _ (hq t ht)
    refine ⟨x, ?_, rfl⟩
    show x ∈ (f t ht).val.carrier 0
    rw [exists_honest_step7_zero_carrier, hf t ht]
    exact hxt

/-- Step 8 of the V4 proof of `inflate` (V4 1.13(a)): the inflated honest source. -/
private def inflate_step8_source {S : SubstSystem d} (U : HonestSource S) : HonestSource S where
  tiling := inflate_step4_tiling U
  mem_species := inflate_step8_species (inflate_step6_hierarchy U) (inflate_step7_contexts U)
  hierarchy := inflate_step6_hierarchy U
  contexts := inflate_step7_contexts U
  coset := U.coset
  frames_in_coset := inflate_step3_coset U

/-- Step 9 of the V4 proof of `inflate` (V4 1.13(a)): "the old height-`n` nodes become
height-`(n+1)` nodes". -/
private def inflate_step9_fwd {S : SubstSystem d} (U : HonestSource S)
    (q : U.hierarchy.Tail 0) : (inflate_step8_source U).hierarchy.Tail 1 :=
  ⟨⟨q.val.1 + 1, ⟨inflate_step1_node U q.val.2.val, inflate_step3_mem_succ_intro U q.val.2⟩⟩,
    Nat.le_add_left 1 _⟩

/-- Step 9 of the V4 proof of `inflate` (V4 1.13(a)): the correspondence of all surviving
nodes is a bijection. -/
private theorem inflate_step9_bij {S : SubstSystem d} (U : HonestSource S) :
    Function.Bijective (inflate_step9_fwd U) := by
  constructor
  · rintro ⟨⟨n, N⟩, hn⟩ ⟨⟨m, M⟩, hm⟩ h
    have h1 := congrArg Subtype.val h
    obtain ⟨hnm, hNM⟩ := Sigma.mk.inj h1
    have hnm' : n = m := Nat.succ_injective hnm
    subst hnm'
    have hv := congrArg Subtype.val (eq_of_heq hNM)
    have hNM' : N = M := Subtype.ext (inflate_step2_injective U N.val M.val
      (U.frames_in_coset n N.val N.property) (U.frames_in_coset n M.val M.property) hv)
    subst hNM'
    rfl
  · rintro ⟨⟨m, M⟩, hm⟩
    cases m with
    | zero => exact (Nat.not_succ_le_zero 0 hm).elim
    | succ n =>
      obtain ⟨N₀, hN₀⟩ := inflate_step3_mem_succ U M.2
      refine ⟨⟨⟨n, N₀⟩, Nat.zero_le _⟩, ?_⟩
      apply Subtype.ext
      refine Sigma.ext ?_ ?_
      · rfl
      apply heq_of_eq
      apply Subtype.ext
      exact hN₀.symm

/-- Step 9 of the V4 proof of `inflate` (V4 1.13(a)): "with the same roles, parents and
(conjugated) frames": the full tail correspondence. -/
private theorem inflate_step9_tail {S : SubstSystem d} (U : HonestSource S) :
    Nonempty (ScaleTailEquiv U (inflate_step8_source U) 0 1
      (AffineIsometryEquiv.refl ℝ (E d))) := by
  have hpf : ∀ q : U.hierarchy.Tail 0,
      (inflate_step9_fwd U q).val.2.val.prototypeFrame (inflate_step9_fwd U q).val.1 =
        (q.val.2.val.prototypeFrame q.val.1).trans U.expansion.toAffineEquiv := fun q =>
    inflate_step1_prototypeFrame U _ (U.frames_in_coset _ _ q.val.2.property) q.val.1
  have hexp : U.expansion ^ (((1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) = U.expansion := by
    simp
  refine ⟨{
    toEquiv := Equiv.ofBijective (inflate_step9_fwd U) (inflate_step9_bij U)
    heights := fun q => rfl
    types := fun q => rfl
    frames := ?_
    parents := ?_
    roles := ?_
    prototype_sets := ?_ }⟩
  · intro q
    rw [Equiv.ofBijective_apply, hpf q, hexp]
    ext x
    rfl
  · intro q
    rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply]
    apply Subtype.ext
    refine Sigma.ext ?_ ?_
    · rfl
    apply heq_of_eq
    exact (inflate_step5_parent_succ U q.val.2 _).symm
  · intro q
    rw [Equiv.ofBijective_apply]
    exact inflate_step5_role_succ U q.val.2 _
  · intro q K
    rw [Equiv.ofBijective_apply, hpf q, hexp]
    rw [AffineIsometryEquiv.coe_refl, Set.image_id, Set.image_image]
    apply Set.image_congr
    intro x _
    dsimp only
    refine ((q.val.2.val.prototypeFrame q.val.1).trans U.expansion.toAffineEquiv).injective ?_
    rw [AffineEquiv.apply_symm_apply, AffineEquiv.trans_apply, AffineEquiv.apply_symm_apply]
    try rfl

/-- T9, V4 1.13(a): inflation by `Λ`, with new native ground tiles, remains
honest. Every old node becomes a node one level higher, with exact framed data.
The target's coherent native-tile condition prescribes the ground subdivision. -/
theorem inflate {S : SubstSystem d} (U : HonestSource S) :
    ∃ V : HonestSource S,
      Nonempty (ScaleTailEquiv U V 0 1 (AffineIsometryEquiv.refl ℝ (E d))) :=
  ⟨inflate_step8_source U, inflate_step9_tail U⟩

/-! Private construction for `coarsen` (V4 1.13(b)). -/

/-- V4 1.13(b): the frame `φ` has orthogonal part in the coset `Q H`. -/
private abbrev coarsen_InC {S : SubstSystem d} (U : HonestSource S) (φ : Iso d) : Prop :=
  ∃ R ∈ S.rotGroup, φ.linearIsometryEquiv = U.coset * R

private theorem coarsen_lin_apply (φ : Iso d) (v : E d) :
    φ v = φ.linearIsometryEquiv v + φ 0 := by
  have h := φ.map_vadd (0 : E d) v
  simpa [vadd_eq_add] using h

private theorem coarsen_rigid_apply (R : Ortho d) (t x : E d) :
    rigidMotion R t x = R x + t := rfl

/-- V4 1.13: `Λ^z = Q σ^z Q⁻¹`. -/
private theorem coarsen_expansion_zpow {S : SubstSystem d} (U : HonestSource S) (z : ℤ)
    (x : E d) : (U.expansion ^ z) x = U.coset ((S.σ ^ z) (U.coset.symm x)) := by
  have h : U.expansion = MulAut.conj U.coset.toLinearEquiv S.σ := rfl
  rw [h, ← map_zpow, MulAut.conj_apply]
  rfl

/-- V4 1.13(b): `Λ^{-j} ∘ φ ∘ σ^j` is an isometry with frame in `Q H`, by V4 1.10(a). -/
private theorem coarsen_frame_exists {S : SubstSystem d} (U : HonestSource S) (j : ℕ)
    (φ : Iso d) (hφ : coarsen_InC U φ) :
    ∃ ψ : Iso d, (∀ x, ψ x = (U.expansion ^ (-(j : ℤ))) (φ ((S.σ ^ j) x))) ∧
      coarsen_InC U ψ := by
  obtain ⟨R, hR, hφR⟩ := hφ
  obtain ⟨Q, hQ, hQeq⟩ := S.rotGroup_conj_zpow (-(j : ℤ)) R hR
  have hQx : ∀ x, Q x = (S.σ ^ (-(j : ℤ))) (R ((S.σ ^ j) x)) := by
    intro x
    have := congrArg (fun e : E d ≃ₗ[ℝ] E d => e x) hQeq
    simp only [linearConj, LinearEquiv.mul_apply, neg_neg, zpow_natCast,
      LinearIsometryEquiv.coe_toLinearEquiv] at this
    exact this
  refine ⟨rigidMotion (U.coset * Q) ((U.expansion ^ (-(j : ℤ))) (φ 0)), ?_, Q, hQ, ?_⟩
  · intro x
    rw [coarsen_rigid_apply, coarsen_lin_apply φ ((S.σ ^ j) x), map_add]
    congr 1
    rw [hφR, coarsen_expansion_zpow, LinearIsometryEquiv.coe_mul, LinearIsometryEquiv.coe_mul,
      Function.comp_apply, Function.comp_apply, LinearIsometryEquiv.symm_apply_apply, hQx]
  · apply LinearIsometryEquiv.ext
    intro v
    have h := coarsen_lin_apply (rigidMotion (U.coset * Q) ((U.expansion ^ (-(j : ℤ))) (φ 0))) v
    have h1 : rigidMotion (U.coset * Q) ((U.expansion ^ (-(j : ℤ))) (φ 0)) v =
        (U.coset * Q) v + (U.expansion ^ (-(j : ℤ))) (φ 0) := rfl
    have h2 : rigidMotion (U.coset * Q) ((U.expansion ^ (-(j : ℤ))) (φ 0)) 0 =
        (U.expansion ^ (-(j : ℤ))) (φ 0) := by
      show (U.coset * Q) 0 + (U.expansion ^ (-(j : ℤ))) (φ 0) = _
      rw [map_zero (U.coset * Q), zero_add]
    rw [h1, h2] at h
    exact (add_right_cancel h).symm

open Classical in
/-- V4 1.13(b): the coarsened framed node `Λ^{-j} N` (frame `Λ^{-j} ∘ φ_N ∘ σ^j`). -/
private def coarsen_node {S : SubstSystem d} (U : HonestSource S) (j : ℕ)
    (N : FramedNode S) : FramedNode S :=
  ⟨N.ty, if h : ∃ ψ : Iso d, ∀ x, ψ x = (U.expansion ^ (-(j : ℤ))) (N.frame ((S.σ ^ j) x))
    then Classical.choose h else N.frame⟩

private theorem coarsen_node_apply {S : SubstSystem d} (U : HonestSource S) (j : ℕ)
    (N : FramedNode S) (hN : coarsen_InC U N.frame) (x : E d) :
    (coarsen_node U j N).frame x = (U.expansion ^ (-(j : ℤ))) (N.frame ((S.σ ^ j) x)) := by
  obtain ⟨ψ, hψ, -⟩ := coarsen_frame_exists U j N.frame hN
  have h : ∃ ψ : Iso d, ∀ x, ψ x = (U.expansion ^ (-(j : ℤ))) (N.frame ((S.σ ^ j) x)) :=
    ⟨ψ, hψ⟩
  simp only [coarsen_node, dif_pos h]
  exact Classical.choose_spec h x

private theorem coarsen_node_InC {S : SubstSystem d} (U : HonestSource S) (j : ℕ)
    (N : FramedNode S) (hN : coarsen_InC U N.frame) :
    coarsen_InC U (coarsen_node U j N).frame := by
  obtain ⟨ψ, hψ, hψC⟩ := coarsen_frame_exists U j N.frame hN
  have : (coarsen_node U j N).frame = ψ := by
    apply AffineIsometryEquiv.ext
    intro x
    rw [coarsen_node_apply U j N hN, hψ]
  rw [this]
  exact hψC

private theorem coarsen_node_inj {S : SubstSystem d} (U : HonestSource S) (j : ℕ)
    {N M : FramedNode S} (hN : coarsen_InC U N.frame) (hM : coarsen_InC U M.frame)
    (h : coarsen_node U j N = coarsen_node U j M) : N = M := by
  apply FramedNode.ext
  · have h' := congrArg FramedNode.ty h
    exact h'
  · apply AffineIsometryEquiv.ext
    intro y
    have := congrArg (fun P : FramedNode S => P.frame ((S.σ ^ j).symm y)) h
    simp only [coarsen_node_apply U j N hN, coarsen_node_apply U j M hM,
      LinearEquiv.apply_symm_apply] at this
    exact (U.expansion ^ (-(j : ℤ))).injective this

private theorem coarsen_interior_image (L : E d ≃ₗ[ℝ] E d) (X : Set (E d)) :
    interior (L '' X) = L '' interior X :=
  (L.toContinuousLinearEquiv.toHomeomorph.image_interior X).symm

/-- V4 1.13(b): the support of `Λ^{-j} N` is `Λ^{-j}` of the support of `N`. -/
private theorem coarsen_carrier {S : SubstSystem d} (U : HonestSource S) (j n : ℕ)
    (N : FramedNode S) (hN : coarsen_InC U N.frame) :
    (coarsen_node U j N).carrier n = (U.expansion ^ (-(j : ℤ))) '' N.carrier (j + n) := by
  change (coarsen_node U j N).frame '' ((S.σ ^ n) '' (S.proto N.ty).carrier) =
    (U.expansion ^ (-(j : ℤ))) '' (N.frame '' ((S.σ ^ (j + n)) '' (S.proto N.ty).carrier))
  simp only [Set.image_image]
  congr 1
  funext x
  rw [coarsen_node_apply U j N hN, pow_add, LinearEquiv.mul_apply]

/-- V4 1.13(b): coarsening commutes with taking prescribed children. -/
private theorem coarsen_child {S : SubstSystem d} (U : HonestSource S) (j n : ℕ)
    (P : FramedNode S) (i : S.I P.ty)
    (hP : coarsen_InC U P.frame) (hc : coarsen_InC U (P.child (j + n) i).frame) :
    coarsen_node U j (P.child (j + n) i) = (coarsen_node U j P).child n i := by
  apply FramedNode.ext
  · rfl
  · apply AffineIsometryEquiv.ext
    intro x
    rw [coarsen_node_apply U j _ hc]
    show (U.expansion ^ (-(j : ℤ))) (P.frame (S.placeChild (j + n) i ((S.σ ^ j) x))) =
      (coarsen_node U j P).frame (S.placeChild n i x)
    rw [coarsen_node_apply U j P hP, exists_honest_step7_place_shift]

/-- V4 1.13(b): coarsening a height-`j` descendant gives a native tile. -/
private theorem coarsen_desc {S : SubstSystem d} (U : HonestSource S) (j n : ℕ)
    (N : FramedNode S) (w : S.RoleWord N.ty n)
    (hN : coarsen_InC U N.frame)
    (hM : coarsen_InC U ((S.descendantNode N.ty j n w).move N.frame).frame) :
    (S.nativeTile N.ty n w).move (coarsen_node U j N).frame =
      coarsen_node U j ((S.descendantNode N.ty j n w).move N.frame) := by
  apply FramedNode.ext
  · exact (exists_honest_step7_descendant_type N.ty j n w).symm
  · apply AffineIsometryEquiv.ext
    intro x
    rw [coarsen_node_apply U j _ hM]
    show (coarsen_node U j N).frame ((S.nativeTile N.ty n w).frame x) = _
    rw [coarsen_node_apply U j N hN]
    show _ = (U.expansion ^ (-(j : ℤ)))
      (N.frame ((S.descendantNode N.ty j n w).frame ((S.σ ^ j) x)))
    rw [exists_honest_step7_descendant_scaled]

private theorem coarsen_desc_shift {S : SubstSystem d} (A : S.ι) (h n k : ℕ)
    (w : S.RoleWord A k) (x : E d) :
    (S.descendantNode A (h + n) k w).frame ((S.σ ^ h) x) =
      (S.σ ^ h) ((S.descendantNode A n k w).frame x) := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih =>
    change S.placeChild (h + n + k) w.1
      ((S.descendantNode (S.child A w.1).ty (h + n) k w.2).frame ((S.σ ^ h) x)) =
      (S.σ ^ h) (S.placeChild (n + k) w.1
        ((S.descendantNode (S.child A w.1).ty n k w.2).frame x))
    rw [ih, Nat.add_assoc, exists_honest_step7_place_shift]

private theorem coarsen_desc_succ {S : SubstSystem d} (j k : ℕ) (N : FramedNode S)
    (w : S.RoleWord N.ty (k + 1)) :
    (S.descendantNode N.ty j (k + 1) w).move N.frame =
      (S.descendantNode (N.child (j + k) w.1).ty j k w.2).move (N.child (j + k) w.1).frame := by
  simp [SubstSystem.descendantNode, FramedNode.move, FramedNode.child,
    AffineIsometryEquiv.trans_assoc]

private theorem coarsen_desc_zero {S : SubstSystem d} (j : ℕ) (N : FramedNode S)
    (w : S.RoleWord N.ty 0) : (S.descendantNode N.ty j 0 w).move N.frame = N := by
  apply FramedNode.ext
  · rfl
  · apply AffineIsometryEquiv.ext
    intro x
    rfl

private theorem coarsen_desc_mem {S : SubstSystem d} {T : Tiling S}
    (H : CoherentHierarchy S T) (j : ℕ) :
    ∀ (k : ℕ) (N : FramedNode S), N ∈ H.nodes (j + k) → ∀ w : S.RoleWord N.ty k,
      (S.descendantNode N.ty j k w).move N.frame ∈ H.nodes j := by
  intro k
  induction k with
  | zero =>
    intro N hN w
    rw [coarsen_desc_zero]
    exact hN
  | succ k ih =>
    intro N hN w
    rw [coarsen_desc_succ]
    exact ih (N.child (j + k) w.1) (H.children_mem (j + k) N hN w.1) w.2

private theorem coarsen_desc_subset {S : SubstSystem d} (j : ℕ) :
    ∀ (k : ℕ) (N : FramedNode S) (w : S.RoleWord N.ty k),
      ((S.descendantNode N.ty j k w).move N.frame).carrier j ⊆ N.carrier (j + k) := by
  intro k
  induction k with
  | zero =>
    intro N w
    rw [coarsen_desc_zero]
    exact le_rfl
  | succ k ih =>
    intro N w
    rw [coarsen_desc_succ]
    exact (ih (N.child (j + k) w.1) w.2).trans
      (exists_honest_step7_child_subset N (j + k) w.1)

private theorem coarsen_desc_exists {S : SubstSystem d} {T : Tiling S}
    (H : CoherentHierarchy S T) (j : ℕ) :
    ∀ (k : ℕ) (M : FramedNode S), M ∈ H.nodes j → ∃ P ∈ H.nodes (j + k),
      ∃ w : S.RoleWord P.ty k, M = (S.descendantNode P.ty j k w).move P.frame := by
  intro k
  induction k with
  | zero =>
    intro M hM
    exact ⟨M, hM, (), (coarsen_desc_zero j M ()).symm⟩
  | succ k ih =>
    intro M hM
    obtain ⟨P, hP, w, rfl⟩ := ih M hM
    have key : ∃ Q ∈ H.nodes (j + k + 1), ∃ i : S.I Q.ty, P = Q.child (j + k) i :=
      ⟨_, (H.parent (j + k) ⟨P, hP⟩).2, H.role (j + k) ⟨P, hP⟩, H.child_eq (j + k) ⟨P, hP⟩⟩
    obtain ⟨Q, hQ, i, rfl⟩ := key
    exact ⟨Q, hQ, ⟨i, w⟩, (coarsen_desc_succ j k Q ⟨i, w⟩).symm⟩

private theorem coarsen_node_interior {S : SubstSystem d} (N : FramedNode S) (n : ℕ) :
    (interior (N.carrier n)).Nonempty := by
  have h1 : (interior (S.supertile n N.ty)).Nonempty := by
    change (interior ((S.σ ^ n) '' (S.proto N.ty).carrier)).Nonempty
    rw [coarsen_interior_image]
    exact (S.proto N.ty).interior_nonempty.image _
  change (interior (N.frame.toHomeomorph '' S.supertile n N.ty)).Nonempty
  rw [← N.frame.toHomeomorph.image_interior]
  exact h1.image _

/-- V4 1.13(b): the height-`n` nodes of the coarsened hierarchy, `Λ^{-j} 𝒩_{j+n}`. -/
private abbrev coarsen_nodes {S : SubstSystem d} (U : HonestSource S) (j n : ℕ) :
    Set (FramedNode S) :=
  coarsen_node U j '' U.hierarchy.nodes (j + n)

private def coarsen_rep {S : SubstSystem d} (U : HonestSource S) (j n : ℕ)
    (N' : {N' // N' ∈ coarsen_nodes U j n}) : FramedNode S :=
  Classical.choose N'.2

private theorem coarsen_rep_mem {S : SubstSystem d} (U : HonestSource S) (j n : ℕ)
    (N' : {N' // N' ∈ coarsen_nodes U j n}) :
    coarsen_rep U j n N' ∈ U.hierarchy.nodes (j + n) :=
  (Classical.choose_spec N'.2).1

private theorem coarsen_rep_eq {S : SubstSystem d} (U : HonestSource S) (j n : ℕ)
    (N' : {N' // N' ∈ coarsen_nodes U j n}) :
    coarsen_node U j (coarsen_rep U j n N') = N'.val :=
  (Classical.choose_spec N'.2).2

private theorem coarsen_inC_of_mem {S : SubstSystem d} (U : HonestSource S) {m : ℕ}
    {N : FramedNode S} (hN : N ∈ U.hierarchy.nodes m) : coarsen_InC U N.frame :=
  U.frames_in_coset m N hN

private theorem coarsen_zpow_cancel {S : SubstSystem d} (U : HonestSource S) (j : ℕ)
    (x : E d) : (U.expansion ^ (-(j : ℤ))) ((U.expansion ^ (j : ℤ)) x) = x := by
  rw [← LinearEquiv.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero]
  rfl

private theorem coarsen_cover {S : SubstSystem d} (U : HonestSource S) (j n : ℕ) (x : E d) :
    ∃ N ∈ coarsen_nodes U j n, x ∈ N.carrier n := by
  obtain ⟨N, hN, hx⟩ := U.hierarchy.cover (j + n) ((U.expansion ^ (j : ℤ)) x)
  refine ⟨coarsen_node U j N, Set.mem_image_of_mem _ hN, ?_⟩
  rw [coarsen_carrier U j n N (coarsen_inC_of_mem U hN)]
  exact ⟨_, hx, coarsen_zpow_cancel U j x⟩

private theorem coarsen_disjoint {S : SubstSystem d} (U : HonestSource S) (j n : ℕ) :
    (coarsen_nodes U j n).PairwiseDisjoint (fun N => interior (N.carrier n)) := by
  rintro _ ⟨N₁, h₁, rfl⟩ _ ⟨N₂, h₂, rfl⟩ hne
  have hne' : N₁ ≠ N₂ := fun h => hne (h ▸ rfl)
  have hd : Disjoint (interior (N₁.carrier (j + n))) (interior (N₂.carrier (j + n))) :=
    U.hierarchy.disjoint (j + n) h₁ h₂ hne'
  change Disjoint (interior ((coarsen_node U j N₁).carrier n))
    (interior ((coarsen_node U j N₂).carrier n))
  rw [coarsen_carrier U j n N₁ (coarsen_inC_of_mem U h₁),
    coarsen_carrier U j n N₂ (coarsen_inC_of_mem U h₂),
    coarsen_interior_image, coarsen_interior_image]
  exact Set.disjoint_image_of_injective (U.expansion ^ (-(j : ℤ))).injective hd

/-- V4 1.13(b): `Λ^{-j}(𝒩_j)` as a tiling. -/
private def coarsen_tiling {S : SubstSystem d} (U : HonestSource S) (j : ℕ) : Tiling S where
  tiles := {t | ∃ N ∈ coarsen_nodes U j 0, N.toTile = t}
  cover := by
    intro x
    obtain ⟨N, hN, hx⟩ := coarsen_cover U j 0 x
    exact ⟨N.toTile, ⟨N, hN, rfl⟩, by rwa [← exists_honest_step7_zero_carrier]⟩
  disjoint := by
    rintro _ ⟨N₁, h₁, rfl⟩ _ ⟨N₂, h₂, rfl⟩ hne
    have hne' : N₁ ≠ N₂ := fun h => hne (h ▸ rfl)
    have hd : Disjoint (interior (N₁.carrier 0)) (interior (N₂.carrier 0)) :=
      coarsen_disjoint U j 0 h₁ h₂ hne'
    rw [exists_honest_step7_zero_carrier, exists_honest_step7_zero_carrier] at hd
    exact hd

/-- V4 1.13(b): native tiles of a coarsened node are the coarsened height-`j`
descendants of the original node. -/
private theorem coarsen_native {S : SubstSystem d} (U : HonestSource S) (j n : ℕ)
    (N : FramedNode S) (hN : N ∈ U.hierarchy.nodes (j + n)) :
    {t | t ∈ (coarsen_tiling U j).tiles ∧ t.carrier ⊆ (coarsen_node U j N).carrier n} =
      {t | ∃ w : S.RoleWord (coarsen_node U j N).ty n,
        ((S.nativeTile (coarsen_node U j N).ty n w).move
          (coarsen_node U j N).frame).toTile = t} := by
  have hNC := coarsen_inC_of_mem U hN
  ext t
  constructor
  · rintro ⟨⟨_, ⟨M, hM, rfl⟩, rfl⟩, hsub⟩
    have hM' : M ∈ U.hierarchy.nodes j := hM
    have hMC := coarsen_inC_of_mem U hM'
    rw [← exists_honest_step7_zero_carrier, coarsen_carrier U j 0 M hMC,
      coarsen_carrier U j n N hNC] at hsub
    have hsub' : M.carrier (j + 0) ⊆ N.carrier (j + n) :=
      (Set.image_subset_image_iff (U.expansion ^ (-(j : ℤ))).injective).mp hsub
    obtain ⟨P, hP, w, rfl⟩ := coarsen_desc_exists U.hierarchy j n M hM'
    have hPN : P = N := by
      obtain ⟨x, hx⟩ := coarsen_node_interior ((S.descendantNode P.ty j n w).move P.frame) j
      by_contra hne
      exact Set.disjoint_left.mp (U.hierarchy.disjoint (j + n) hP hN hne)
        (interior_mono (coarsen_desc_subset j n P w) hx) (interior_mono hsub' hx)
    subst hPN
    exact ⟨w, congrArg FramedNode.toTile (coarsen_desc U j n _ w hNC hMC)⟩
  · rintro ⟨w, rfl⟩
    have hM := coarsen_desc_mem U.hierarchy j n N hN w
    have hMC := coarsen_inC_of_mem U hM
    have heq := coarsen_desc U j n N w hNC hMC
    refine ⟨(show ∃ N' ∈ coarsen_nodes U j 0, N'.toTile = _ from
      ⟨_, Set.mem_image_of_mem _ hM, (congrArg FramedNode.toTile heq).symm⟩), ?_⟩
    · rw [← exists_honest_step7_zero_carrier]
      change ((S.nativeTile N.ty n w).move (coarsen_node U j N).frame).carrier 0 ⊆ _
      rw [heq, coarsen_carrier U j 0 _ hMC, coarsen_carrier U j n N hNC]
      exact Set.image_mono (coarsen_desc_subset j n N w)

/-- V4 1.13(b): the inherited hierarchy `(Λ^{-j} 𝒩_{j+n})_n`. -/
private def coarsen_hier {S : SubstSystem d} (U : HonestSource S) (j : ℕ) :
    CoherentHierarchy S (coarsen_tiling U j) where
  nodes := coarsen_nodes U j
  ground := rfl
  cover := coarsen_cover U j
  disjoint := coarsen_disjoint U j
  parent n N' := ⟨coarsen_node U j
      (U.hierarchy.parent (j + n) ⟨coarsen_rep U j n N', coarsen_rep_mem U j n N'⟩).val,
    Set.mem_image_of_mem _ (U.hierarchy.parent (j + n)
      ⟨coarsen_rep U j n N', coarsen_rep_mem U j n N'⟩).2⟩
  role n N' := U.hierarchy.role (j + n) ⟨coarsen_rep U j n N', coarsen_rep_mem U j n N'⟩
  child_eq := by
    intro n N'
    have h1 := U.hierarchy.child_eq (j + n) ⟨coarsen_rep U j n N', coarsen_rep_mem U j n N'⟩
    refine (coarsen_rep_eq U j n N').symm.trans ?_
    refine (congrArg (coarsen_node U j) h1).trans ?_
    apply coarsen_child
    · exact coarsen_inC_of_mem U (U.hierarchy.parent (j + n) _).2
    · rw [← h1]
      exact coarsen_inC_of_mem U (coarsen_rep_mem U j n N')
  children_mem := by
    rintro n _ ⟨P, hP, rfl⟩ i
    have hc := U.hierarchy.children_mem (j + n) P hP i
    refine ⟨P.child (j + n) i, hc, ?_⟩
    exact coarsen_child U j n P i (coarsen_inC_of_mem U hP) (coarsen_inC_of_mem U hc)
  parent_unique := by
    rintro n N' _ ⟨P, hP, rfl⟩ ⟨i, hi⟩
    have hc := U.hierarchy.children_mem (j + n) P hP i
    have h2 : coarsen_node U j (coarsen_rep U j n N') =
        coarsen_node U j (P.child (j + n) i) := by
      rw [coarsen_rep_eq, hi,
        coarsen_child U j n P i (coarsen_inC_of_mem U hP) (coarsen_inC_of_mem U hc)]
    have h3 : coarsen_rep U j n N' = P.child (j + n) i :=
      coarsen_node_inj U j (coarsen_inC_of_mem U (coarsen_rep_mem U j n N'))
        (coarsen_inC_of_mem U hc) h2
    have h4 := U.hierarchy.parent_unique (j + n)
      ⟨coarsen_rep U j n N', coarsen_rep_mem U j n N'⟩ P hP ⟨i, h3⟩
    exact congrArg (coarsen_node U j) h4
  native_tiles := by
    rintro n _ ⟨N, hN, rfl⟩
    exact coarsen_native U j n N hN

private theorem coarsen_supertile_shift {S : SubstSystem d} (j k : ℕ) (A : S.ι) :
    (S.σ ^ j).symm '' S.supertile (j + k) A = S.supertile k A := by
  simp only [SubstSystem.supertile, Set.image_image, pow_add, LinearEquiv.mul_apply,
    LinearEquiv.symm_apply_apply]

/-- V4 1.13(b): every finite set of coarsened nodes has a legal context
`σ^{-j} ψ Λ^j` in `σ^{n-j} A`, from the context `ψ` of the original nodes. -/
private theorem coarsen_contexts {S : SubstSystem d} (U : HonestSource S) (j : ℕ)
    (F' : Finset (coarsen_hier U j).Node) : Nonempty (LegalContext (coarsen_hier U j) F') := by
  classical
  obtain ⟨M₀, hM₀, -⟩ := U.hierarchy.cover j 0
  let back : (coarsen_hier U j).Node → U.hierarchy.Node := fun r =>
    ⟨j + r.1, ⟨coarsen_rep U j r.1 r.2, coarsen_rep_mem U j r.1 r.2⟩⟩
  let F : Finset U.hierarchy.Node := insert ⟨j, ⟨M₀, hM₀⟩⟩ (F'.image back)
  obtain ⟨ctx⟩ := U.contexts F
  have h0 : (⟨j, ⟨M₀, hM₀⟩⟩ : U.hierarchy.Node) ∈ F := Finset.mem_insert_self _ _
  obtain ⟨depth₀, hd₀, w₀, hw₀⟩ := ctx.standard _ h0
  have hw₀' : M₀.move ctx.placement = S.descendantNode ctx.ty j depth₀ w₀ := hw₀
  have hd₀' : ctx.height = j + depth₀ := hd₀
  let ψ' : Iso d := (coarsen_node U j M₀).frame.symm.trans (S.nativeTile ctx.ty depth₀ w₀).frame
  have hψ' : ∀ x, ψ' ((U.expansion ^ (-(j : ℤ))) x) = (S.σ ^ j).symm (ctx.placement x) := by
    intro x
    obtain ⟨z, hz⟩ : ∃ z, (coarsen_node U j M₀).frame z = (U.expansion ^ (-(j : ℤ))) x :=
      ⟨_, AffineIsometryEquiv.apply_symm_apply _ _⟩
    have hz' : M₀.frame ((S.σ ^ j) z) = x := by
      rw [coarsen_node_apply U j M₀ (coarsen_inC_of_mem U hM₀)] at hz
      exact (U.expansion ^ (-(j : ℤ))).injective hz
    have hstep : ψ' ((U.expansion ^ (-(j : ℤ))) x) = (S.nativeTile ctx.ty depth₀ w₀).frame z := by
      rw [← hz]
      show (S.nativeTile ctx.ty depth₀ w₀).frame
        ((coarsen_node U j M₀).frame.symm ((coarsen_node U j M₀).frame z)) = _
      rw [AffineIsometryEquiv.symm_apply_apply]
    have h2 : ctx.placement (M₀.frame ((S.σ ^ j) z)) =
        (S.descendantNode ctx.ty j depth₀ w₀).frame ((S.σ ^ j) z) :=
      congrArg (fun N : FramedNode S => N.frame ((S.σ ^ j) z)) hw₀'

    rw [hstep, ← hz', h2, exists_honest_step7_descendant_scaled, LinearEquiv.symm_apply_apply]
  have hback : ∀ r ∈ F', back r ∈ F := fun r hr =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hr)
  refine ⟨{
    height := ctx.height - j
    ty := ctx.ty
    placement := ψ'
    standard := ?_
    interior := ?_
    edges := ?_ }⟩
  · intro r hr
    obtain ⟨depth, hd, w, hw⟩ := ctx.standard _ (hback r hr)
    have hd' : ctx.height = j + r.1 + depth := hd
    have hw' : (coarsen_rep U j r.1 r.2).move ctx.placement =
        S.descendantNode ctx.ty (j + r.1) depth w := hw
    refine ⟨depth, by omega, w, ?_⟩
    rw [← coarsen_rep_eq U j r.1 r.2]
    apply FramedNode.ext
    · have := congrArg FramedNode.ty hw'
      change (coarsen_rep U j r.1 r.2).ty = _
      rw [show (coarsen_rep U j r.1 r.2).ty = (S.descendantNode ctx.ty (j + r.1) depth w).ty
        from this, exists_honest_step7_descendant_type, exists_honest_step7_descendant_type]
    · apply AffineIsometryEquiv.ext
      intro x
      show ψ' ((coarsen_node U j (coarsen_rep U j r.1 r.2)).frame x) = _
      rw [coarsen_node_apply U j _ (coarsen_inC_of_mem U (coarsen_rep_mem U j r.1 r.2)), hψ']
      have h3 : ctx.placement ((coarsen_rep U j r.1 r.2).frame ((S.σ ^ j) x)) =
          (S.descendantNode ctx.ty (j + r.1) depth w).frame ((S.σ ^ j) x) :=
        congrArg (fun N : FramedNode S => N.frame ((S.σ ^ j) x)) hw'

      rw [h3, coarsen_desc_shift, LinearEquiv.symm_apply_apply]
  · intro r hr
    have hsub := ctx.interior _ (hback r hr)
    change ctx.placement '' (coarsen_rep U j r.1 r.2).carrier (j + r.1) ⊆ _ at hsub
    rw [hd₀'] at hsub
    rw [hd₀', Nat.add_sub_cancel_left, ← coarsen_rep_eq U j r.1 r.2,
      coarsen_carrier U j r.1 _ (coarsen_inC_of_mem U (coarsen_rep_mem U j r.1 r.2)),
      Set.image_image]
    calc (fun x => ψ' ((U.expansion ^ (-(j : ℤ))) x)) ''
          (coarsen_rep U j r.1 r.2).carrier (j + r.1)
        = (S.σ ^ j).symm '' (ctx.placement '' (coarsen_rep U j r.1 r.2).carrier (j + r.1)) := by
          rw [Set.image_image]
          congr 1
          funext x
          exact hψ' x
      _ ⊆ (S.σ ^ j).symm '' interior (S.supertile (j + depth₀) ctx.ty) := Set.image_mono hsub
      _ = interior (S.supertile depth₀ ctx.ty) := by
          rw [← coarsen_interior_image, coarsen_supertile_shift]
  · intro r _ _
    exact congrArg (fun N : FramedNode S => N.move ψ') ((coarsen_hier U j).child_eq r.1 r.2)

/-- Generic: a tiling carrying a hierarchy with legal contexts is in the species. -/
private theorem coarsen_species_of_contexts {S : SubstSystem d} {T : Tiling S}
    (H : CoherentHierarchy S T)
    (hctx : ∀ F : Finset H.Node, Nonempty (LegalContext H F)) : T ∈ S.Species := by
  classical
  intro P hP
  have hrep : ∀ t : P.tiles, ∃ N, N ∈ H.nodes 0 ∧ N.toTile = t.val := by
    intro t
    have : t.val ∈ {t | ∃ N ∈ H.nodes 0, N.toTile = t} := by
      rw [H.ground]
      exact hP t.property
    obtain ⟨N, hN, h⟩ := this
    exact ⟨N, hN, h⟩
  choose rep hrepmem hrepeq using hrep
  let F : Finset H.Node :=
    Finset.univ.image (fun t : P.tiles => (⟨0, ⟨rep t, hrepmem t⟩⟩ : H.Node))
  have hF : ∀ t : P.tiles, (⟨0, ⟨rep t, hrepmem t⟩⟩ : H.Node) ∈ F := fun t =>
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  obtain ⟨ctx⟩ := hctx F
  refine ⟨ctx.height, ctx.ty, ctx.placement, ?_, ?_⟩
  · intro t ht
    obtain ⟨w, hw⟩ := exists_honest_step7_standard_ground _ _ _ (ctx.standard _ (hF ⟨t, ht⟩))
    refine ⟨w, ?_⟩
    have h1 := hrepeq ⟨t, ht⟩
    calc t.move ctx.placement = (rep ⟨t, ht⟩).toTile.move ctx.placement := by rw [h1]
      _ = ((rep ⟨t, ht⟩).move ctx.placement).toTile :=
          (exists_honest_step7_move_toTile _ _).symm
      _ = _ := congrArg FramedNode.toTile hw
  · rintro _ ⟨x, hx, rfl⟩
    simp only [Patch.support, Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    refine ctx.interior _ (hF ⟨t, ht⟩) ⟨x, ?_, rfl⟩
    change x ∈ (rep ⟨t, ht⟩).carrier 0
    rw [exists_honest_step7_zero_carrier, hrepeq]
    exact hxt

/-- V4 1.13(b): the coarsened honest source. -/
private def coarsen_source {S : SubstSystem d} (U : HonestSource S) (j : ℕ) :
    HonestSource S where
  tiling := coarsen_tiling U j
  mem_species := coarsen_species_of_contexts (coarsen_hier U j) (coarsen_contexts U j)
  hierarchy := coarsen_hier U j
  contexts := coarsen_contexts U j
  coset := U.coset
  frames_in_coset := by
    rintro n _ ⟨N, hN, rfl⟩
    exact coarsen_node_InC U j N (coarsen_inC_of_mem U hN)

private theorem coarsen_back_eq {S : SubstSystem d} (U : HonestSource S) (j m : ℕ)
    (N : FramedNode S) (hN : N ∈ U.hierarchy.nodes m) (hm : j ≤ m)
    (h' : coarsen_node U j N ∈ coarsen_nodes U j (m - j)) :
    (⟨j + (m - j), ⟨coarsen_rep U j (m - j) ⟨coarsen_node U j N, h'⟩,
      coarsen_rep_mem U j (m - j) _⟩⟩ : U.hierarchy.Node) = ⟨m, ⟨N, hN⟩⟩ := by
  apply Sigma.subtype_ext
  · exact Nat.add_sub_cancel' hm
  · exact coarsen_node_inj U j (coarsen_inC_of_mem U (coarsen_rep_mem U j (m - j) _))
      (coarsen_inC_of_mem U hN) (coarsen_rep_eq U j (m - j) _)

private theorem coarsen_mem_shift {S : SubstSystem d} (U : HonestSource S) (j m : ℕ)
    (N : FramedNode S) (hN : N ∈ U.hierarchy.nodes m) (hm : j ≤ m) :
    coarsen_node U j N ∈ coarsen_nodes U j (m - j) := by
  refine ⟨N, ?_, rfl⟩
  rwa [Nat.add_sub_cancel' hm]

/-- V4 1.13(b): the bijection of the surviving tails. -/
private def coarsen_equiv {S : SubstSystem d} (U : HonestSource S) (j : ℕ) :
    U.hierarchy.Tail j ≃ (coarsen_source U j).hierarchy.Tail 0 where
  toFun q := ⟨⟨q.val.1 - j, ⟨coarsen_node U j q.val.2.val,
    coarsen_mem_shift U j q.val.1 q.val.2.val q.val.2.property q.property⟩⟩, Nat.zero_le _⟩
  invFun r := ⟨⟨j + r.val.1, ⟨coarsen_rep U j r.val.1 r.val.2,
    coarsen_rep_mem U j r.val.1 r.val.2⟩⟩, Nat.le_add_right _ _⟩
  left_inv q := Subtype.ext (coarsen_back_eq U j q.val.1 q.val.2.val q.val.2.property
    q.property _)
  right_inv r := Subtype.ext (Sigma.subtype_ext (Nat.add_sub_cancel_left j r.val.1)
    (coarsen_rep_eq U j r.val.1 r.val.2))

private theorem coarsen_frames {S : SubstSystem d} (U : HonestSource S) (j m : ℕ)
    (N : FramedNode S) (hN : N ∈ U.hierarchy.nodes m) (hm : j ≤ m) :
    (coarsen_node U j N).prototypeFrame (m - j) =
      (N.prototypeFrame m).trans
        (((U.expansion ^ (((0 : ℕ) : ℤ) - (j : ℤ))).toAffineEquiv).trans
          (AffineIsometryEquiv.refl ℝ (E d)).toAffineEquiv) := by
  have hz : ((0 : ℕ) : ℤ) - (j : ℤ) = -(j : ℤ) := by simp
  rw [hz]
  apply AffineEquiv.ext
  intro x
  change (coarsen_node U j N).frame ((S.σ ^ (m - j)) x) =
    (U.expansion ^ (-(j : ℤ))) (N.frame ((S.σ ^ m) x))
  rw [coarsen_node_apply U j N (coarsen_inC_of_mem U hN), ← LinearEquiv.mul_apply, ← pow_add,
    Nat.add_sub_cancel' hm]

private theorem coarsen_pullback (P P' : E d ≃ᵃ[ℝ] E d) (g₁ g₂ : E d → E d)
    (h : ∀ x, P' x = g₁ (g₂ (P x))) (K : Set (E d)) :
    P'.symm '' (g₁ '' (g₂ '' K)) = P.symm '' K := by
  rw [Set.image_image g₁ g₂, Set.image_image]
  congr 1
  funext k
  show P'.symm (g₁ (g₂ k)) = P.symm k
  apply P'.injective
  rw [AffineEquiv.apply_symm_apply, h, AffineEquiv.apply_symm_apply]

/-- V4 1.13(b): exact correspondence of the tails under `Λ^{-j}`. -/
private def coarsen_tail {S : SubstSystem d} (U : HonestSource S) (j : ℕ) :
    ScaleTailEquiv U (coarsen_source U j) j 0 (AffineIsometryEquiv.refl ℝ (E d)) where
  toEquiv := coarsen_equiv U j
  heights q := by
    show q.val.1 - j + j = q.val.1 + 0
    have := q.property
    omega
  types q := rfl
  frames q := coarsen_frames U j q.val.1 q.val.2.val q.val.2.property q.property
  parents q := by
    apply Subtype.ext
    apply Sigma.subtype_ext
    · show q.val.1 + 1 - j = q.val.1 - j + 1
      have := q.property
      omega
    · show coarsen_node U j (U.hierarchy.parentNode q.val).2.val =
        coarsen_node U j (U.hierarchy.parentNode ⟨j + (q.val.1 - j), ⟨coarsen_rep U j (q.val.1 - j)
          ⟨coarsen_node U j q.val.2.val, coarsen_mem_shift U j q.val.1 q.val.2.val
            q.val.2.property q.property⟩, coarsen_rep_mem U j _ _⟩⟩).2.val
      rw [coarsen_back_eq U j q.val.1 q.val.2.val q.val.2.property q.property]
  roles q := by
    show U.hierarchy.nodeRole ⟨j + (q.val.1 - j), ⟨coarsen_rep U j (q.val.1 - j)
          ⟨coarsen_node U j q.val.2.val, coarsen_mem_shift U j q.val.1 q.val.2.val
            q.val.2.property q.property⟩, coarsen_rep_mem U j _ _⟩⟩ = _
    rw [coarsen_back_eq U j q.val.1 q.val.2.val q.val.2.property q.property]
  prototype_sets q K := by
    refine coarsen_pullback _ _ _ _ (fun x => ?_) K
    exact congrArg (fun f : E d ≃ᵃ[ℝ] E d => f x)
      (coarsen_frames U j q.val.1 q.val.2.val q.val.2.property q.property)

/-- T9, V4 1.13(b): for every positive `j`, coarsening the height-`j` nodes
by `Λ⁻ʲ` gives an honest source and exactly its inherited hierarchy. -/
theorem coarsen {S : SubstSystem d} (U : HonestSource S) (j : ℕ) (hj : 1 ≤ j) :
    ∃ V : HonestSource S,
      Nonempty (ScaleTailEquiv U V j 0 (AffineIsometryEquiv.refl ℝ (E d))) := by
  exact ⟨coarsen_source U j, ⟨coarsen_tail U j⟩⟩

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
  have h := e.heights q
  have h_mod : ((e.toEquiv q).val.1 + a) % L = (q.val.1 + b) % L := by rw [h]
  have h2a : ((e.toEquiv q).val.1 + a) % L = ((e.toEquiv q).val.1 % L + a % L) % L := Nat.add_mod _ _ _
  have h1b : (q.val.1 + b) % L = (q.val.1 % L + b % L) % L := Nat.add_mod _ _ _
  rw [h2a, h1b, ← hab] at h_mod
  have h_mod_eq : (e.toEquiv q).val.1 % L + a % L ≡ q.val.1 % L + a % L [MOD L] := h_mod
  have h_xy : (e.toEquiv q).val.1 % L ≡ q.val.1 % L [MOD L] := Nat.ModEq.add_right_cancel' (a % L) h_mod_eq
  exact Nat.ModEq.eq_of_lt_of_lt h_xy (Nat.mod_lt _ hL) (Nat.mod_lt _ hL)

end Enforce
