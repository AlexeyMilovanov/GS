import Tilings.Basic
import Tilings.Hierarchy

/-!
# The five principal theorems (statements only)

Theorem 1(a,b,c) and Theorem 2(a,b) of arXiv:2606.25005v2 in the corrected
form of the blueprint (revision of 12 October 2026).  Every statement is
about plane tilings.  All proofs are `sorry`: these are the final goals of
the formalization and must not be marked proved before the geometric
certificate is instantiated.
-/

namespace Tilings

open Substitution

variable {P : Protoset} (τ : Substitution P)

/-- Theorem 1(a) (`thm:sts-substitution`): under STS the substitution plane
tilings are side-to-side sofic on the original listed sides. -/
theorem sts_substitution_sofic (h : τ.STS) :
    IsSideToSideSofic {T | τ.IsSubstitutionTiling T} := by
  sorry

/-- Theorem 1(b) (`thm:sts-stshierarchy`): under STS the side-to-side
hierarchical plane tilings are side-to-side sofic. -/
theorem sts_side_to_side_hierarchy_sofic (h : τ.STS) :
    IsSideToSideSofic {T | τ.IsSideToSideHierarchical T} := by
  sorry

/-- Theorem 2(a) (`thm:flc-substitution`): under FLC the substitution plane
tilings are sofic. -/
theorem flc_substitution_sofic (h : τ.FLC) :
    IsSofic {T | τ.IsSubstitutionTiling T} := by
  sorry

/-- Theorem 2(b) (`thm:flc-hierarchy`): under FLC the hierarchical plane
tilings are sofic. -/
theorem flc_hierarchy_sofic (h : τ.FLC) :
    IsSofic {T | τ.IsHierarchical T} := by
  sorry

/-- `lem:sts-flc`: STS implies FLC. -/
theorem STS.flc (h : τ.STS) : τ.FLC :=
  STS.finite_crowns τ h

/-- Theorem 1(c) (`thm:sts-hierarchy`): under STS the hierarchical plane
tilings are sofic. -/
theorem sts_hierarchy_sofic (h : τ.STS) :
    IsSofic {T | τ.IsHierarchical T} := by
  exact flc_hierarchy_sofic τ (STS.flc τ h)

/-- Theorem 1(c) follows from Theorem 2(b) and `STS.flc`; recorded as the
intended dependency. -/
theorem sts_hierarchy_sofic_of_flc (h : τ.STS) : IsSofic {T | τ.IsHierarchical T} :=
  flc_hierarchy_sofic τ (STS.flc τ h)

end Tilings
