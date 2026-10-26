import Enforce.Basic

/-!
# Polyhedral domains and their local geometry

The frontier manifold condition uses relative open neighbourhoods and homeomorphisms
to open subsets of Euclidean space. This is the chosen chart formulation of (H1).
The solid angle is measured in steradians, by `d` times the volume of a unit-ball sector.
-/

open Set Metric MeasureTheory

noncomputable section

namespace Enforce

variable {d : ℕ}

/-- G1, V4 §1.0 (H1): a finite union of convex hulls of finite sets of vertices.
Empty polyhedra are allowed here; domains and cells separately require nonemptiness. -/
def Polyhedron (K : Set (E d)) : Prop :=
  ∃ s : Finset (Finset (E d)), K = ⋃ p ∈ s, convexHull ℝ (p : Set (E d))

/-- G1, V4 §1.0 (H1): local Euclidean charts on a subset, in its subspace topology.
At every point there is a relative open neighbourhood homeomorphic to an open subset
of `E n`. In particular the condition on an empty frontier is harmless. -/
def IsLocallyEuclidean (n : ℕ) (K : Set (E d)) : Prop :=
  ∀ p : K, ∃ U : Set K, IsOpen U ∧ p ∈ U ∧
    ∃ V : Set (E n), IsOpen V ∧ Nonempty (U ≃ₜ V)

/-- G1, V4 §1.0 (H1): a full-dimensional polyhedral manifold domain.
Nonconvexity, cavities, handles and arbitrary Euclidean placements are permitted.
The explicit nonempty interior excludes degenerate or empty prototiles. -/
structure PolyManifoldDomain (d : ℕ) where
  /-- G1, V4 §1.0 (H1): the closed region. -/
  carrier : Set (E d)
  /-- G1, V4 §1.0 (H1): finite polyhedral presentation. -/
  polyhedral : Polyhedron carrier
  /-- G1, V4 §1.0 (H1): compactness, redundant with the finite presentation. -/
  compact : IsCompact carrier
  /-- G1, V4 §1.0 (H1): ambient regular closedness. -/
  regularClosed : IsRegularClosed carrier
  /-- G1, V4 §1.0 (H1): connected interior. -/
  interior_connected : IsConnected (interior carrier)
  /-- G1, V4 §1.0 (H1): full dimensionality. -/
  interior_nonempty : (interior carrier).Nonempty
  /-- G1, V4 §1.0 (H1): the boundary is a topological `(d-1)`-manifold. -/
  frontier_manifold : IsLocallyEuclidean (d - 1) (frontier carrier)

/-- G2, V4 §1.0 (H2): the relative interior in the affine span, as an ambient set. -/
def relint (K : Set (E d)) : Set (E d) := intrinsicInterior ℝ K

/-- G2, V4 §1.0 (H2): relative boundary in the affine span, as an ambient set. -/
def relfrontier (K : Set (E d)) : Set (E d) := intrinsicFrontier ℝ K

/-- G2, V4 §1.0 (H2): the direction space of the affine hull. -/
def cellDirection (K : Set (E d)) : Submodule ℝ (E d) :=
  (affineSpan ℝ K).direction

/-- G2, V4 §1.0 (H2): a flat `j`-cell, regular closed in its own affine span.
The relative boundary charts express that the cell is a polyhedral manifold domain
in that span. A zero-dimensional cell has empty relative boundary. -/
structure IsFlatCell (j : ℕ) (K : Set (E d)) : Prop where
  /-- G2, V4 §1.0 (H2): finite polyhedral carrier. -/
  polyhedral : Polyhedron K
  /-- G2, V4 §1.0 (H2): affine dimension is the listed dimension. -/
  dimension : Module.finrank ℝ (cellDirection K) = j
  /-- G2, V4 §1.0 (H2): compactness. -/
  compact : IsCompact K
  /-- G2, V4 §1.0 (H2): connectedness of the cell. -/
  connected : IsConnected K
  /-- G2, V4 §1.0 (H2)(iii): closure of the relative interior. -/
  regularClosed : closure (relint K) = K
  /-- G2, V4 §1.0 (H2): connected relative interior. -/
  relint_connected : IsConnected (relint K)
  /-- G2, V4 §1.0 (H2): nonempty relative interior. -/
  relint_nonempty : (relint K).Nonempty
  /-- G2, V4 §1.0 (H2): relative boundary manifold condition. -/
  boundary_manifold : IsLocallyEuclidean (j - 1) (relfrontier K)

/-- G2, V4 §1.0 (H2): a flat compact cell with its dimension as data. -/
structure Cell (d : ℕ) where
  /-- G2, V4 §1.0 (H2): closed carrier. -/
  carrier : Set (E d)
  /-- G2, V4 §1.0 (H2): dimension, including zero. -/
  dim : ℕ
  /-- G2, V4 §1.0 (H2): all geometric cell conditions. -/
  flat : IsFlatCell dim carrier

/-- G5, V4 1.0(b): the local radial tangent cone, translated to the origin.
The positive-time germ, rather than a limiting or convexified cone, is used. -/
def tangentCone (K : Set (E d)) (p : E d) : Set (E d) :=
  {v | ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → p + t • v ∈ K}

/-- G5, V4 1.0(b): a finite union of closed convex polyhedral cones.
Each convex piece is a finite intersection of homogeneous closed half-spaces. -/
def IsPolyhedralCone (K : Set (E d)) : Prop :=
  ∃ s : Finset (Finset (E d →ₗ[ℝ] ℝ)),
    K = ⋃ p ∈ s, {v | ∀ ℓ ∈ p, 0 ≤ ℓ v}

/-- G5, V4 1.0(b): solid angle, using radial volume in the Euclidean unit ball.
This equals the usual spherical area for measurable cones. -/
def solidAngle (K : Set (E d)) : ℝ :=
  (d : ℝ) * (volume (K ∩ ball 0 1)).toReal

/-- G5, V4 1.0(b): the full solid angle `ω_d`, in the same normalization. -/
def fullSolidAngle (d : ℕ) : ℝ :=
  (d : ℝ) * (volume (ball (0 : E d) 1)).toReal

/-- G7, V4 1.0(b): local polyhedrality and solidity of the tangent cone. -/
theorem tangentCone_polyhedral (A : PolyManifoldDomain d) (p : E d)
    (hp : p ∈ frontier A.carrier) :
    IsPolyhedralCone (tangentCone A.carrier p) ∧
      (interior (tangentCone A.carrier p)).Nonempty := by
  sorry

/-- G1, V4 §1.0 (H1): the finite-convex-hull definition implies compactness. -/
theorem Polyhedron.isCompact {K : Set (E d)} (hK : Polyhedron K) : IsCompact K := by
  sorry

/-- Sym1, V4 5.6: the full group of Euclidean symmetries of a full-dimensional
polyhedron is finite. No boundary manifold condition or orientation restriction
is needed, and the nonempty interior rules out lower-dimensional stabilizers. -/
theorem polyhedron_symmetries_finite (K : Set (E d)) (hK : Polyhedron K)
    (hfull : (interior K).Nonempty) :
    {g : Iso d | g '' K = K}.Finite := by
  sorry

end Enforce
