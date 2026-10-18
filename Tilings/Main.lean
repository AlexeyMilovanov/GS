import Tilings.StrictPresentation
import Tilings.Basic
import Tilings.FLC.Clones
import Tilings.Hierarchy
import Tilings.LocalRules

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
  obtain ⟨Sys, hsingle, hSTS, hcomp, hcompl⟩ := Alignment.exists_strict_schedule_system τ h
  have H : IsSideToSideSofic {T : PlaneTiling Sys.GS.G.P' |
      ∃ T' : PlaneTiling Sys.dec.P', Sys.dec.Proper T' ∧ Sys.dec.project T' = T} := by
    use Sys.dec
    intro T
    rfl
  have H2 := Decoration.dissection_preserves_sts_sofic Sys.GS.G H
  convert H2 using 1
  ext S
  simp only [Set.mem_setOf_eq, Geometry.GroupedFamily.scatterFamily]
  constructor
  · intro hS
    obtain ⟨T, hProper, hEq⟩ :=
      Alignment.exists_strict_proper_of_sts_hierarchical h Sys hsingle hcompl hS
    use Sys.dec.project T
    refine ⟨⟨T, hProper, rfl⟩, ?_⟩
    cases S
    dsimp at hEq ⊢
    congr
  · rintro ⟨T', ⟨T, hProper, rfl⟩, hEq⟩
    have hEq' : S.tiles = Sys.GS.G.scatter (Sys.dec.project T).tiles := by
      rw [hEq]
    exact Alignment.sts_hierarchical_of_strict_proper h Sys hSTS hcomp hProper hEq'


/-- Theorem 2(a) (`thm:flc-substitution`): under FLC the substitution plane
tilings are sofic. -/
theorem flc_substitution_sofic (h : τ.FLC) :
    IsSofic {T | τ.IsSubstitutionTiling T} := by
  sorry

/-- Theorem 2(b) (`thm:flc-hierarchy`): under FLC the hierarchical plane
tilings are sofic. -/
theorem flc_hierarchy_sofic (h : τ.FLC) :
    IsSofic {T | τ.IsHierarchical T} := by
  have hsts := FLC.refinedSubstitution_sts τ h
  have hher := FLC.refinedSubstitution_hereditary τ h
  have hsofic := Core.hereditary_sts_hierarchy_sofic _ hsts hher
  have hlift : {T | τ.IsHierarchical T} =
      (FLC.cloneDecoration τ h).project ''
        {T | (FLC.refinedSubstitution τ h).IsHierarchical T} := by
    ext T
    simp only [FLC.hierarchy_clone_lift_iff τ h T, Set.mem_setOf_eq, Set.mem_image]
    tauto
  rw [hlift]
  exact FLC.forget_vertices_preserves_sofic (FLC.cloneDecoration τ h)
    {T | (FLC.refinedSubstitution τ h).IsHierarchical T} (Or.inl hsofic)

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
