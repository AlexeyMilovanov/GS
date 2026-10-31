import Enforce.Tiling

/-!
# C1 rule systems and pointwise marked tilings

Markings are functions on the closed carriers, with no continuity assumption.
Agreement is imposed at every shared point, including tile boundaries. Physical
tiles retain their marked carriers; symmetries preserve both their partition and
their markings. The canonical global marking is chosen from a covering tile.
-/

open Set

noncomputable section

namespace Enforce

variable {d : ℕ} {X : Type}

/-- M1, V4 2.9: a set with an arbitrary pointwise marking on its carrier. -/
structure MarkedSet (d : ℕ) (X : Type) where
  /-- M1, V4 2.9: the support of the partial marking. -/
  carrier : Set (E d)
  /-- M1, V4 2.9: the marking is defined at every point of the support. -/
  mark : carrier → X

/-- M1, V4 2.9: apply an isometry to a marked set, transporting its marking. -/
def MarkedSet.move (P : MarkedSet d X) (g : Iso d) : MarkedSet d X where
  carrier := g '' P.carrier
  mark x := P.mark ⟨g.symm x.val, by
    obtain ⟨y, hy, he⟩ := x.property
    rw [← he, g.symm_apply_apply]
    exact hy⟩

/-- M1, V4 2.9: a physical marked prototile in a C1 catalogue. -/
structure MarkedPrototile (d : ℕ) (X : Type) extends MarkedSet d X where
  /-- M1, V4 2.9: the physical carrier is compact. -/
  compact : IsCompact carrier
  /-- M1, V4 2.9: the physical carrier is regular closed. -/
  regularClosed : IsRegularClosed carrier

/-- M1, V4 2.9: a compact rule, which need not be a full physical tile. -/
structure CompactRule (d : ℕ) (X : Type) extends MarkedSet d X where
  /-- M1, V4 2.9: compact support, with no interior or continuity requirement. -/
  compact : IsCompact carrier

/-- M1, V4 2.9: a finite colour set, finite physical catalogue and finite
catalogue of compact rules. Properness is the pointwise covering rule below. -/
structure C1System (d : ℕ) (X : Type) where
  /-- M1, V4 2.9: colours are finite. -/
  [colors_finite : Fintype X]
  /-- M1, V4 2.9: finitely many marked physical prototiles. -/
  physical : Finset (MarkedPrototile d X)
  /-- M1, V4 2.9: finitely many compact rules. -/
  rules : Finset (CompactRule d X)

/-- M1, V4 2.9: a physical placed marked tile, identified by its marked carrier.
DEVIATION: as for `PlacedTile`, representing isometries are existential witnesses,
so a symmetry of a marked prototype does not create a second physical tile. -/
structure PlacedMarkedTile (M : C1System d X) extends MarkedSet d X where
  /-- M1, V4 2.9: realization by a member of the physical catalogue. -/
  realization : ∃ P ∈ M.physical, ∃ φ : Iso d,
    carrier = placedSet φ P.carrier ∧
      ∀ (x : P.carrier) (hx : φ x ∈ carrier), mark ⟨φ x, hx⟩ = P.mark x

/-- M1, V4 2.9: a marked tiling by the finite physical catalogue, with
agreement on all shared points. No properness is included in this definition. -/
structure MarkedTiling (M : C1System d X) where
  /-- M1, V4 2.9: the set of physical placed marked tiles. -/
  tiles : Set (PlacedMarkedTile M)
  /-- M1, V4 2.9: every point belongs to a tile. -/
  cover : ∀ x : E d, ∃ t ∈ tiles, x ∈ t.carrier
  /-- M1, V4 2.9: interiors of distinct physical tiles are disjoint. -/
  disjoint : tiles.PairwiseDisjoint (fun t => interior t.carrier)
  /-- M1, V4 2.9: the markings agree, also on lower-dimensional intersections. -/
  agreement : ∀ t ∈ tiles, ∀ u ∈ tiles, ∀ x (ht : x ∈ t.carrier) (hu : x ∈ u.carrier),
    t.mark ⟨x, ht⟩ = u.mark ⟨x, hu⟩

namespace MarkedTiling

variable {M : C1System d X} (Y : MarkedTiling M)

/-- M1, V4 2.9: the global function `λ_Y`, chosen from a tile covering `x`.
The covering field supplies the existence and agreement makes the result canonical. -/
def marking (x : E d) : X :=
  (Classical.choose (Y.cover x)).mark ⟨x, (Classical.choose_spec (Y.cover x)).2⟩

/-- M1, V4 2.9: independence of the tile used to read a shared point. -/
theorem marking_independent (t u : PlacedMarkedTile M) (ht : t ∈ Y.tiles)
    (hu : u ∈ Y.tiles) (x : E d) (hxt : x ∈ t.carrier) (hxu : x ∈ u.carrier) :
    t.mark ⟨x, hxt⟩ = u.mark ⟨x, hxu⟩ :=
  Y.agreement t ht u hu x hxt hxu

/-- M1, V4 2.9: the global marking equals the marking of any covering tile. -/
theorem marking_eq_tile (t : PlacedMarkedTile M) (ht : t ∈ Y.tiles)
    (x : E d) (hx : x ∈ t.carrier) : Y.marking x = t.mark ⟨x, hx⟩ := by
  exact Y.agreement _ (Classical.choose_spec (Y.cover x)).1 t ht x _ hx

/-- M1, V4 2.9: a point in the interior of any physical tile of `Y`. -/
def IsTileInterior (x : E d) : Prop := ∃ t ∈ Y.tiles, x ∈ interior t.carrier

/-- M1/F, V4 2.9, 5.7: the set of placed marked carriers, retaining the partition. -/
def markedCarriers : Set (MarkedSet d X) := (fun t => t.toMarkedSet) '' Y.tiles

/-- M1/F, V4 5.7: a Euclidean symmetry preserves both tiles and markings. -/
def IsSymmetry (g : Iso d) : Prop :=
  (fun P : MarkedSet d X => P.move g) '' Y.markedCarriers = Y.markedCarriers

/-- M1/F, V4 5.7: all Euclidean symmetries, including reflections. -/
def symmetries : Set (Iso d) := {g | Y.IsSymmetry g}

/-- M1/F, V4 5.7: tile-and-marking symmetries satisfy the subgroup laws.
The action is on placed marked carriers, so it retains the physical partition. -/
theorem symmetry_group_laws : Y.IsSymmetry 1 ∧
    (∀ g h : Iso d, Y.IsSymmetry g → Y.IsSymmetry h → Y.IsSymmetry (g * h)) ∧
      (∀ g : Iso d, Y.IsSymmetry g → Y.IsSymmetry g⁻¹) := by
  sorry

/-- M1/F, V4 5.7: the full Euclidean symmetry group of the marked tiling. -/
def symmetryGroup : Subgroup (Iso d) where
  carrier := Y.symmetries
  one_mem' := Y.symmetry_group_laws.1
  mul_mem' := Y.symmetry_group_laws.2.1 _ _
  inv_mem' := Y.symmetry_group_laws.2.2 _

/-- M1/F, V4 5.7: the subgroup has exactly the intended tile-and-marking symmetries. -/
theorem mem_symmetryGroup (g : Iso d) : g ∈ Y.symmetryGroup ↔ Y.IsSymmetry g :=
  Iff.rfl

end MarkedTiling

/-- M1, V4 2.9: every point is covered by a placed compact rule that agrees
with the global marking throughout the whole rule support. -/
def MProper {M : C1System d X} (Y : MarkedTiling M) : Prop :=
  ∀ x : E d, ∃ R ∈ M.rules, ∃ ψ : Iso d,
    x ∈ placedSet ψ R.carrier ∧ ∀ p : R.carrier, Y.marking (ψ p) = R.mark p

variable [Fact (2 ≤ d)]

/-- M1/F, V4 2.9, Theorem F §F.2: the physical catalogue is a decoration of
the original prototypes, and `π` recovers type on interiors and `@` on frontiers.
No condition on the rules is hidden in this structure. -/
structure NativeDecoration (S : SubstSystem d) (M : C1System d X) (π : X → Option S.ι)
    where
  /-- M1/F, V4 §F.2: the prototype type of each physical marked prototype. -/
  ty : {P // P ∈ M.physical} → S.ι
  /-- M1/F, V4 §F.2: equality in prototype coordinates, not just congruence. -/
  carrier_eq : ∀ P : {P // P ∈ M.physical}, P.val.carrier = (S.proto (ty P)).carrier
  /-- M1/F, V4 §F.2: type on the prototype interior. -/
  interior_projection : ∀ (P : {P // P ∈ M.physical}) (x : P.val.carrier),
    x.val ∈ interior P.val.carrier → π (P.val.mark x) = some (ty P)
  /-- M1/F, V4 §F.2: the common boundary value `none = @`. -/
  frontier_projection : ∀ (P : {P // P ∈ M.physical}) (x : P.val.carrier),
    x.val ∈ frontier P.val.carrier → π (P.val.mark x) = none

namespace PlacedMarkedTile

variable {M : C1System d X}

/-- M1, V4 2.9: a representing marked prototype, chosen from a genuine realization. -/
def prototype (t : PlacedMarkedTile M) : {P // P ∈ M.physical} :=
  ⟨Classical.choose t.realization, (Classical.choose_spec t.realization).1⟩

/-- M1, V4 2.9: an isometry realizing the chosen marked prototype. -/
def placement (t : PlacedMarkedTile M) : Iso d :=
  Classical.choose (Classical.choose_spec t.realization).2

/-- M1/F, V4 §F.2: forget the extra marking, retaining the typed native carrier. -/
def native {S : SubstSystem d} {π : X → Option S.ι} (D : NativeDecoration S M π)
    (t : PlacedMarkedTile M) : PlacedTile S :=
  PlacedTile.ofFrame (D.ty t.prototype) t.placement

/-- M1/F, V4 §F.2: forgetting the marking preserves the closed physical carrier. -/
theorem native_carrier {S : SubstSystem d} {π : X → Option S.ι}
    (D : NativeDecoration S M π) (t : PlacedMarkedTile M) :
    (t.native D).carrier = t.carrier := by
  dsimp [native, PlacedTile.ofFrame]
  have h_eq := D.carrier_eq t.prototype
  have h2 := Classical.choose_spec t.realization
  have h3 := Classical.choose_spec h2.2
  have h_carrier := h3.1
  dsimp [prototype, placement] at h_eq ⊢
  rw [← h_eq]
  exact h_carrier.symm

end PlacedMarkedTile

namespace MarkedTiling

variable {S : SubstSystem d} {M : C1System d X} {π : X → Option S.ι}
    (Y : MarkedTiling M) (D : NativeDecoration S M π)

/-- M1/F, V4 §F.2: the projected native tiles cover space. -/
theorem project_cover (x : E d) :
    ∃ t ∈ (fun u => u.native D) '' Y.tiles, x ∈ t.carrier := by
  obtain ⟨u, hu, hx⟩ := Y.cover x
  use u.native D
  constructor
  · exact Set.mem_image_of_mem _ hu
  · rw [PlacedMarkedTile.native_carrier D u]
    exact hx

/-- M1/F, V4 §F.2: projection preserves disjointness of tile interiors. -/
theorem project_disjoint :
    ((fun u => u.native D) '' Y.tiles).PairwiseDisjoint (fun t => interior t.carrier) := by
  sorry

/-- M1/F, V4 §F.2: the tile-faithful native projection of a marked output.
It is a tiling; it is deliberately not required to be a member of `S.Species`. -/
def project : Tiling S where
  tiles := (fun u => u.native D) '' Y.tiles
  cover := Y.project_cover D
  disjoint := Y.project_disjoint D

/-- M1/F, V4 §F.2: pointwise projection recovers the old native marking. -/
theorem project_marking (x : E d) :
    π (Y.marking x) = oldMarking (Y.project D) x := by
  sorry

/-- M1/F, V4 §F.2: projected and physical tiles have exactly the same carriers. -/
theorem project_carriers :
    (fun t : PlacedTile S => t.carrier) '' (Y.project D).tiles =
      (fun t : PlacedMarkedTile M => t.carrier) '' Y.tiles := by
  show (fun t : PlacedTile S => t.carrier) '' ((fun u => u.native D) '' Y.tiles) = _
  rw [Set.image_image]
  exact Set.image_congr (fun t _ => PlacedMarkedTile.native_carrier D t)

end MarkedTiling

/-- M1, V4 2.9, 2.15: a complete pattern on a closed standard supertile. -/
abbrev Pattern (S : SubstSystem d) (X : Type) (n : ℕ) (A : S.ι) :=
  S.supertile n A → X

/-- M1, V4 2.9, 2.15: transport the entire marking into an isometric frame,
including all points on the supertile boundary. -/
def normalisedPattern {S : SubstSystem d} {M : C1System d X}
    (Y : MarkedTiling M) (n : ℕ) (A : S.ι) (ψ : Iso d) : Pattern S X n A :=
  fun x => Y.marking (ψ x)

/-- M1/F, V4 4.7--4.9: a framed copy is well formed exactly when its complete
normalised pattern belongs to the specified height/type language. -/
def IsWFConfig {S : SubstSystem d} {M : C1System d X}
    (L : ∀ n A, Set (Pattern S X n A)) (Y : MarkedTiling M)
    (n : ℕ) (N : FramedNode S) : Prop :=
  normalisedPattern Y n N.ty N.frame ∈ L n N.ty

end Enforce
