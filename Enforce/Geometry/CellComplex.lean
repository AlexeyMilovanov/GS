import Enforce.Geometry.Polyhedral

/-!
# Proper boundary complexes and Lemma 1.0

Cells need not be maximal geometric faces. Flat subdivisions and listed vertices
are allowed. Relative interiors, rather than carriers, partition the boundary.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ}

/-- G3, V4 §1.0 (H2): a finite proper boundary complex on a prototile. -/
structure CellComplex (A : PolyManifoldDomain d) where
  /-- G3, V4 §1.0 (H2): the finite list of closed flat cells. -/
  cells : Finset (Cell d)
  /-- G3, V4 §1.0 (H2): all cells have boundary dimensions. -/
  dim_lt : ∀ e ∈ cells, e.dim < d
  /-- G3, V4 §1.0 (H2)(i): distinct relative interiors are disjoint. -/
  relint_disjoint : ∀ e ∈ cells, ∀ f ∈ cells, e ≠ f →
    Disjoint (relint e.carrier) (relint f.carrier)
  /-- G3, V4 §1.0 (H2)(i): the relative interiors partition the entire frontier. -/
  cover : (⋃ e ∈ cells, relint e.carrier) = frontier A.carrier
  /-- G3, V4 §1.0 (H2)(ii): each relative boundary is a union of listed cells.
  Condition (iii) is `Cell.flat.regularClosed`. -/
  boundary_union : ∀ e ∈ cells, ∃ b : Finset (Cell d), b ⊆ cells ∧
    relfrontier e.carrier = ⋃ f ∈ b, f.carrier

namespace CellComplex

variable {A : PolyManifoldDomain d} (K : CellComplex A)

/-- G3, V4 §1.0 (H2): the `(d-1)`-cells, including flat subdivided facets. -/
def facets : Finset (Cell d) := by
  classical
  exact K.cells.filter (fun e => e.dim = d - 1)

/-- G3, V4 §1.0 (H2): the listed one-dimensional edges. -/
def edges : Finset (Cell d) := by
  classical
  exact K.cells.filter (fun e => e.dim = 1)

/-- G3, V4 §1.0 (H2): the listed vertices, including flat listed vertices. -/
def vertices : Finset (Cell d) := by
  classical
  exact K.cells.filter (fun e => e.dim = 0)

/-- G3, V4 §1.0 (H2): every frontier point belongs to exactly one relative
interior. The existence is used to define `minimalCell`, without partial choices. -/
theorem exists_unique_minimalCell (p : E d) (hp : p ∈ frontier A.carrier) :
    ∃! e : {e // e ∈ K.cells}, p ∈ relint e.val.carrier := by
  sorry

/-- G3, V4 §1.0 (H2): the unique cell whose relative interior contains `p`.
It is defined only on the frontier; the existence theorem supplies the choice. -/
def minimalCell (p : E d) (hp : p ∈ frontier A.carrier) : Cell d :=
  (Classical.choose (K.exists_unique_minimalCell p hp)).val

/-- G3, V4 §1.0 (H2): the chosen minimal cell is listed. -/
theorem minimalCell_mem (p : E d) (hp : p ∈ frontier A.carrier) :
    K.minimalCell p hp ∈ K.cells :=
  (Classical.choose (K.exists_unique_minimalCell p hp)).property

/-- G3, V4 §1.0 (H2): the defining relative-interior property. -/
theorem mem_relint_minimalCell (p : E d) (hp : p ∈ frontier A.carrier) :
    p ∈ relint (K.minimalCell p hp).carrier :=
  (Classical.choose_spec (K.exists_unique_minimalCell p hp)).1

/-- G4, V4 §1.0 (H2): descend through relative boundaries to the minimal cell. -/
theorem minimalCell_subset (p : E d) (hp : p ∈ frontier A.carrier)
    (e : Cell d) (he : e ∈ K.cells) (hpe : p ∈ e.carrier) :
    (K.minimalCell p hp).carrier ⊆ e.carrier := by
  sorry

/-- G3, V4 §1.0 (H2): the closed cell carriers also cover the frontier. -/
theorem carriers_cover : (⋃ e ∈ K.cells, e.carrier) = frontier A.carrier := by
  sorry

end CellComplex

/-- G3, V4 §1.0 (H2), 1.15: a complete nested flag of listed boundary cells.
Index zero is a vertex and index `d-1` is a facet. -/
structure CellFlag {A : PolyManifoldDomain d} (K : CellComplex A) where
  /-- G3, V4 1.15: cell at each dimension. -/
  cell : Fin d → Cell d
  /-- G3, V4 1.15: all cells are listed. -/
  mem : ∀ j, cell j ∈ K.cells
  /-- G3, V4 1.15: dimensions are exact. -/
  dimension : ∀ j, (cell j).dim = j.val
  /-- G3, V4 1.15: cells in increasing order are nested. -/
  nested : ∀ i j, i ≤ j → (cell i).carrier ⊆ (cell j).carrier

/-- G6, V4 1.0(a): near a relative-interior facet point, the frontier and the
facet agree with their affine hyperplane, and the domain is a closed half-ball.
The normal may point to either side, so no orientation is imposed. -/
theorem facet_halfball [Fact (2 ≤ d)] (A : PolyManifoldDomain d) (K : CellComplex A)
    (F : Cell d) (hF : F ∈ K.facets) (p : E d) (hp : p ∈ relint F.carrier) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : E d, ‖v‖ = 1 ∧
      frontier A.carrier ∩ ball p r =
        (affineSpan ℝ F.carrier : Set (E d)) ∩ ball p r ∧
      F.carrier ∩ ball p r = (affineSpan ℝ F.carrier : Set (E d)) ∩ ball p r ∧
      A.carrier ∩ ball p r = {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p r := by
  sorry

/-- G7, V4 1.0(b): the solid angle depends only on the minimal cell. -/
theorem solidAngle_constant_on_cell [Fact (2 ≤ d)] (A : PolyManifoldDomain d)
    (K : CellComplex A) (e : Cell d) (he : e ∈ K.cells) (p q : E d)
    (hp : p ∈ relint e.carrier) (hq : q ∈ relint e.carrier) :
    solidAngle (tangentCone A.carrier p) = solidAngle (tangentCone A.carrier q) := by
  sorry

/-- G7, V4 1.0(b): the catalogue of boundary solid angles, indexed geometrically
by relative interiors of listed cells. It is a set of real numbers, not a choice
of representative points or an enumeration with repetitions. -/
def boundaryAngles {ι : Type*} (proto : ι → PolyManifoldDomain d)
    (cx : ∀ A, CellComplex (proto A)) : Set ℝ :=
  {θ | ∃ (A : ι) (e : Cell d), e ∈ (cx A).cells ∧
    ∃ p ∈ relint e.carrier, θ = solidAngle (tangentCone (proto A).carrier p)}

/-- G7, V4 1.0(b): finitely many boundary angles, all strictly positive. -/
theorem boundaryAngles_finite [Fact (2 ≤ d)] {ι : Type*} [Fintype ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) :
    (boundaryAngles proto cx).Finite ∧
      ∀ θ ∈ boundaryAngles proto cx, 0 < θ := by
  sorry

/-- G7, V4 1.0(b): the paper's `β` is the positive minimum of the finite
angle catalogue. The nonempty type catalogue supplies an actual boundary cell;
the separate uniform-bound theorem also handles an empty catalogue. -/
theorem minimum_solidAngle [Fact (2 ≤ d)] {ι : Type*} [Fintype ι] [Nonempty ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) :
    ∃ β : ℝ, IsLeast (boundaryAngles proto cx) β ∧ 0 < β := by
  sorry

/-- G7, V4 1.0(b): the actual minimum `β` of the finite boundary-angle catalogue.
The preceding existence lemma supplies the choice; the definition has no proof hole. -/
def minimumAngle [Fact (2 ≤ d)] {ι : Type*} [Fintype ι] [Nonempty ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) : ℝ :=
  Classical.choose (minimum_solidAngle proto cx)

/-- G7, V4 1.0(b): the chosen angle is the least catalogue element and is positive. -/
theorem minimumAngle_spec [Fact (2 ≤ d)] {ι : Type*} [Fintype ι] [Nonempty ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) :
    IsLeast (boundaryAngles proto cx) (minimumAngle proto cx) ∧
      0 < minimumAngle proto cx :=
  Classical.choose_spec (minimum_solidAngle proto cx)

/-- G7, V4 1.0(b): the paper's exact numerical bound `M₀ = floor (ω_d / β)`. -/
def multiplicityBound [Fact (2 ≤ d)] {ι : Type*} [Fintype ι] [Nonempty ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) : ℕ :=
  ⌊fullSolidAngle d / minimumAngle proto cx⌋₊

/-- G7, V4 1.0(b): the common-point bound using precisely the minimum-angle
constant, rather than an arbitrary positive lower estimate for the angles. -/
theorem point_count_le [Fact (2 ≤ d)] {ι : Type*} [Fintype ι] [Nonempty ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A))
    {α : Type*} (ty : α → ι) (φ : α → Iso d)
    (hdisjoint : Pairwise (fun a b => Disjoint
      (interior (placedSet (φ a) (proto (ty a)).carrier))
      (interior (placedSet (φ b) (proto (ty b)).carrier)))) (p : E d) :
    {a | p ∈ placedSet (φ a) (proto (ty a)).carrier}.Finite ∧
      Set.ncard {a | p ∈ placedSet (φ a) (proto (ty a)).carrier} ≤
        multiplicityBound proto cx := by
  sorry

/-- G7, V4 1.0(b): a uniform positive lower bound for angles at boundary cells.
The conclusion also covers an empty prototile catalogue (any positive bound works). -/
theorem uniform_solidAngle [Fact (2 ≤ d)] {ι : Type*} [Fintype ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) :
    ∃ β : ℝ, 0 < β ∧ β ≤ fullSolidAngle d ∧
      ∀ A e, e ∈ (cx A).cells → ∀ p ∈ relint e.carrier,
        β ≤ solidAngle (tangentCone (proto A).carrier p) := by
  sorry

/-- G7, V4 1.0(b): at most `floor (ω_d / β)` disjoint placed prototiles
contain any one point. This includes points in the interiors of prototiles. -/
theorem point_multiplicity_bound [Fact (2 ≤ d)] {ι : Type*} [Fintype ι]
    (proto : ι → PolyManifoldDomain d) (cx : ∀ A, CellComplex (proto A)) :
    ∃ β : ℝ, 0 < β ∧ β ≤ fullSolidAngle d ∧
      (∀ A e, e ∈ (cx A).cells → ∀ p ∈ relint e.carrier,
        β ≤ solidAngle (tangentCone (proto A).carrier p)) ∧
      ∀ (α : Type) (ty : α → ι) (φ : α → Iso d),
        Pairwise (fun a b => Disjoint
          (interior (placedSet (φ a) (proto (ty a)).carrier))
          (interior (placedSet (φ b) (proto (ty b)).carrier))) →
        ∀ p : E d, {a | p ∈ placedSet (φ a) (proto (ty a)).carrier}.Finite ∧
          Set.ncard {a | p ∈ placedSet (φ a) (proto (ty a)).carrier} ≤
            ⌊fullSolidAngle d / β⌋₊ := by
  sorry

/-- G8, V4 1.0(c): a family of placed prototiles with pairwise disjoint
interiors is locally finite, and every bounded set meets only finitely many. -/
theorem locallyFinite_disjointInteriors {ι : Type*} [Fintype ι]
    (proto : ι → PolyManifoldDomain d) {α : Type*} (ty : α → ι) (φ : α → Iso d)
    (hdisjoint : Pairwise (fun a b => Disjoint
      (interior (placedSet (φ a) (proto (ty a)).carrier))
      (interior (placedSet (φ b) (proto (ty b)).carrier)))) :
    LocallyFinite (fun a => placedSet (φ a) (proto (ty a)).carrier) ∧
      ∀ B : Set (E d), Bornology.IsBounded B →
        {a | (B ∩ placedSet (φ a) (proto (ty a)).carrier).Nonempty}.Finite := by
  sorry

/-- G9, V4 1.16(b): one closed side of a codimension-one pair `W ≤ V`.
The kernel condition determines the wall inside `V`, not in all of `E`. -/
def IsClosedSide (dirs : Set (Submodule ℝ (E d))) (K : Set (E d)) : Prop :=
  ∃ V W : Submodule ℝ (E d), (V ∈ dirs ∨ V = ⊤) ∧ (W ∈ dirs ∨ W = ⊤) ∧
    W ≤ V ∧ Module.finrank ℝ V = Module.finrank ℝ W + 1 ∧
    ∃ ℓ : E d →ₗ[ℝ] ℝ, {x | x ∈ V ∧ ℓ x = 0} = (W : Set (E d)) ∧
      K = {x | x ∈ V ∧ 0 ≤ ℓ x}

/-- G9, V4 1.16(b): finite unions of finite intersections of allowed subspaces
and closed sides. Supply `Π = HΠ` from the substitution rotation group. -/
def HPiCone (dirs : Set (Submodule ℝ (E d))) (K : Set (E d)) : Prop :=
  ∃ s : Finset (Finset (Set (E d))), K = (⋃ p ∈ s, ⋂ C ∈ p, C) ∧
    ∀ p ∈ s, ∀ C ∈ p,
      (∃ V : Submodule ℝ (E d), (V ∈ dirs ∨ V = ⊤) ∧ C = (V : Set (E d))) ∨
        IsClosedSide dirs C

end Enforce
