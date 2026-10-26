import Enforce.Rules

/-!
# Theorem F, statement stage

This is the bounded-configuration rule-system theorem in F-STATEMENT.md §F.2.
It includes all five conclusions, for arbitrary expanding linear substitutions
in all dimensions at least two. Compilation to geometric fitting is Stage 2.
The languages below are definitions from one chosen hierarchy and lift per source;
they are neither extra witnesses nor the language of arbitrary geometric crops.
-/

open Set

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)]

/-- F, V4 Main Theorem (2), 4.10: the language of the chosen source family.
A pattern occurs exactly at a height-`n`, type-`A` node of a chosen hierarchy,
with that node's full isometric frame. No raw geometric occurrences are added. -/
def chosenLanguage {S : SubstSystem d} {X : Type} {M : C1System d X}
    (lift : ∀ Z ∈ S.Species, MarkedTiling M)
    (hier : ∀ Z ∈ S.Species, CoherentHierarchy S Z)
    (n : ℕ) (A : S.ι) : Set (Pattern S X n A) :=
  {q | ∃ (Z : Tiling S) (hZ : Z ∈ S.Species) (φ : Iso d),
    (⟨A, φ⟩ : FramedNode S) ∈ (hier Z hZ).nodes n ∧
      q = normalisedPattern (lift Z hZ) n A φ}

/-- F, V4 3.1, 4.7, 4.8, 5.5: an intrinsic hierarchy on a proper output.
It is a hierarchy on the exact native partition. All positive-height nodes,
including their frames, are exactly the well-formed configurations. The final
two fields state the resulting determination by the marking and equivariance. -/
structure IntrinsicHierarchy {S : SubstSystem d} {X : Type} {M : C1System d X}
    {π : X → Option S.ι} (D : NativeDecoration S M π)
    (L : ∀ n A, Set (Pattern S X n A)) (Y : MarkedTiling M) where
  /-- F(4), V4 3.1: a coherent hierarchy on the native physical tiling. -/
  hierarchy : CoherentHierarchy S (Y.project D)
  /-- F(4), V4 4.7, 4.8: every node is WF and every framed WF copy is a node. -/
  nodes_iff : ∀ n, 1 ≤ n → ∀ N : FramedNode S,
    N ∈ hierarchy.nodes n ↔ IsWFConfig L Y n N
  /-- F(4), V4 4.7, 4.8, §5.5: equal global markings determine the same nodes
  at every height, even when comparing distinct physical marked tilings. -/
  marking_determines : ∀ (Y' : MarkedTiling M)
      (H' : CoherentHierarchy S (Y'.project D)),
    (∀ n, 1 ≤ n → ∀ N : FramedNode S,
      N ∈ H'.nodes n ↔ IsWFConfig L Y' n N) →
    Y'.marking = Y.marking → ∀ n, H'.nodes n = hierarchy.nodes n
  /-- F(4), V4 §5.5: symmetries preserve all nodes with their transported frames. -/
  equivariant : ∀ g : Iso d, Y.IsSymmetry g → ∀ n,
    (fun N : FramedNode S => N.move g) '' hierarchy.nodes n = hierarchy.nodes n

/-- F, V4 Main Theorem, formalization edition §F.2: the complete enforcement
data with its five conclusions. The preamble fields require proper source lifts
and exact equality of native typed tiles, not merely equality of point markings.
If the species is nonempty, these fields provide a proper marked tiling; the
theorem does not assume nonemptiness, primitivity, FLC or side-to-side incidence. -/
structure EnforcementData (S : SubstSystem d) where
  /-- F, V4 §F.2: the finite colour alphabet. -/
  X : Type
  /-- F, V4 §F.2: finiteness of the alphabet. -/
  [colors_finite : Fintype X]
  /-- F, V4 §F.2: projection to native types plus the boundary symbol. -/
  π : X → Option S.ι
  /-- F, V4 2.9, §F.2: the C1 bounded-configuration system. -/
  M : C1System d X
  /-- F, V4 §F.2: physical marked prototiles have exactly the native carriers
  and the specified old projection on interiors and frontiers. -/
  decoration : NativeDecoration S M π
  /-- F, V4 4.10, §F.2: one marked lift for every source tiling. -/
  lift : ∀ Z ∈ S.Species, MarkedTiling M
  /-- F, V4 1.12, 4.10: one chosen coherent hierarchy for every source tiling. -/
  hier : ∀ Z ∈ S.Species, CoherentHierarchy S Z
  /-- F, V4 2.14, 4.10, §F.2 preamble: all source lifts are proper. -/
  lift_proper : ∀ Z hZ, MProper (lift Z hZ)
  /-- F, V4 2.14, 4.10, §F.2 preamble: lifts have precisely the source's
  typed physical tiles; no coarsening or change of partition is permitted. -/
  lift_tiles : ∀ Z hZ, (lift Z hZ).project decoration = Z
  /-- F(1), V4 Main Theorem (1), 4.10(1): pointwise recovery of the old marking. -/
  lift_projection : ∀ Z hZ x, π ((lift Z hZ).marking x) = oldMarking Z x
  /-- F(2), V4 Main Theorem (2), 4.10(2): finite languages, empty exactly
  when no chosen source hierarchy has a node of that height and type. -/
  finite_languages : ∀ n, 1 ≤ n → ∀ A,
    (chosenLanguage lift hier n A).Finite ∧
      (chosenLanguage lift hier n A = ∅ ↔
        ¬ ∃ (Z : Tiling S) (hZ : Z ∈ S.Species) (φ : Iso d),
          (⟨A, φ⟩ : FramedNode S) ∈ (hier Z hZ).nodes n)
  /-- F(3), V4 Main Theorem (4), 4.9: exactly one pair `(A, ψ)` through
  each tile-interior point. Membership of the point uses the closed supertile,
  and uniqueness includes the entire isometric frame, not just the support. -/
  point_uniqueness : ∀ Y : MarkedTiling M, MProper Y →
    ∀ n, 1 ≤ n → ∀ x : E d, Y.IsTileInterior x →
      ∃! N : FramedNode S,
        x ∈ N.carrier n ∧ IsWFConfig (chosenLanguage lift hier) Y n N
  /-- F(4), V4 Main Theorem (5), 3.1, 4.7, 4.8: every proper output has
  exactly the intrinsic WF hierarchy, determined by its marking and equivariant
  under every Euclidean symmetry of its tiles and markings. -/
  intrinsic_hierarchy : ∀ Y : MarkedTiling M, MProper Y →
    Nonempty (IntrinsicHierarchy decoration (chosenLanguage lift hier) Y)
  /-- F(5), V4 Main Theorem (5), 5.7: the full group of tile-and-marking
  symmetries of each proper output is finite, including reflections. -/
  finite_symmetry : ∀ Y : MarkedTiling M, MProper Y → Y.symmetries.Finite

namespace EnforcementData

variable {S : SubstSystem d} (D : EnforcementData S)

/-- F(2), V4 Main Theorem (2), 4.10: the language is derived from the data. -/
def language (n : ℕ) (A : S.ι) : Set (Pattern S D.X n A) :=
  chosenLanguage D.lift D.hier n A

/-- F, V4 §F.2 nonemptiness: every actual source has a proper lift.
This makes the nonvacuity implication explicit without assuming a source exists. -/
theorem nonempty_proper (Z : Tiling S) (hZ : Z ∈ S.Species) :
    ∃ Y : MarkedTiling D.M, MProper Y ∧ Y.project D.decoration = Z :=
  ⟨D.lift Z hZ, D.lift_proper Z hZ, D.lift_tiles Z hZ⟩

/-- F(1), V4 Main Theorem (1), 4.10(1): pointwise lift as a function equality. -/
theorem lift_oldMarking (Z : Tiling S) (hZ : Z ∈ S.Species) :
    D.π ∘ (D.lift Z hZ).marking = oldMarking Z :=
  funext (D.lift_projection Z hZ)

/-- F(5), V4 5.7: in particular, no proper output has an infinite-order
Euclidean symmetry. This is a proved group-theoretic consequence of finiteness. -/
theorem symmetry_finiteOrder (Y : MarkedTiling D.M) (hY : MProper Y)
    (g : Iso d) (hg : Y.IsSymmetry g) : IsOfFinOrder g := by
  letI : Fintype Y.symmetryGroup := (D.finite_symmetry Y hY).fintype
  exact Y.symmetryGroup.subtype.isOfFinOrder
    (isOfFinOrder_of_finite (⟨g, hg⟩ : Y.symmetryGroup))

end EnforcementData

/-- F, V4 Main Theorem (§5.5), formalization edition F-STATEMENT.md §F.2:
every system satisfying (H1)--(H6), with species defined by (H7), admits finite
bounded-configuration matching rules satisfying exactly conclusions F(1)--F(5).
When the species has a member, `EnforcementData.nonempty_proper` supplies a proper
output above that member. All Euclidean isometries and general expanding `σ`
are allowed. This statement does not assert equality of all projections with the
species, and does not include the Stage 2 geometric fitting compiler. -/
theorem enforce (S : SubstSystem d) : Nonempty (EnforcementData S) := by
  sorry

end Enforce
