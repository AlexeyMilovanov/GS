import Mathlib

/-!
# Shared conventions for the formalization edition of V4

All Euclidean isometries, including reflections, are allowed. The dimension bound
is imposed on substitution systems, rather than on the ambient geometric definitions.
-/

noncomputable section

namespace Enforce

/-- G1, V4 §1.0 (H1): Euclidean space of dimension `d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- T1, V4 §1.0 (H7): all affine Euclidean isometries, including reflections. -/
abbrev Iso (d : ℕ) := E d ≃ᵃⁱ[ℝ] E d

/-- S1, V4 §1.0 (H3): the full orthogonal group, without an orientation restriction. -/
abbrev Ortho (d : ℕ) := E d ≃ₗᵢ[ℝ] E d

/-- G1, V4 §1.0 (H1): regular closedness in the ambient Euclidean space. -/
def IsRegularClosed {d : ℕ} (K : Set (E d)) : Prop :=
  closure (interior K) = K

/-- T1, V4 §1.0 (H7): the carrier placed by an isometric frame. -/
def placedSet {d : ℕ} (φ : Iso d) (K : Set (E d)) : Set (E d) := φ '' K

/-- S1, V4 §1.0 (H3): the rigid motion `x ↦ R x + t`. -/
def rigidMotion {d : ℕ} (R : Ortho d) (t : E d) : Iso d :=
  R.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ t)

/-- S2, V4 §1.0 (H3): conjugation by an integral power of the expansion. -/
def linearConj {d : ℕ} (σ : E d ≃ₗ[ℝ] E d) (m : ℤ)
    (R : E d ≃ₗ[ℝ] E d) : E d ≃ₗ[ℝ] E d :=
  (σ ^ m) * R * (σ ^ (-m))

end Enforce
