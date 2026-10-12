import Tilings.Alignment

/-!
# Local-rule transfers and the hereditary STS core (statements only)

Skeleton for `main.tex`: finite collar conversion (`lem:collar-conversion`),
dissection and glue colours (`lem:glues`), the compatible grouped hierarchy
lift (`lem:grouping-lift`) and the hereditary STS core theorems
(`thm:hereditary-substitution`, `thm:hereditary-hierarchy`).

The five principal theorems themselves are stated in `Tilings/Main.lean`.
All proofs are `sorry`.
-/

open Set Pointwise

noncomputable section

namespace Tilings

open Geometry

variable {P : Protoset}

/-! ## Finite collar conversion (`lem:collar-conversion`) -/

/-- `lem:collar-conversion`: a sofic family consisting entirely of
side-to-side plane tilings is side-to-side sofic on the original listed
sides. -/
theorem LocalRule.side_presentation_of_sts_sofic {F : Set (PlaneTiling P)} (hF : IsSofic F)
    (hsts : ∀ T ∈ F, T.SideToSide) : IsSideToSideSofic F := by
  sorry

/-! ## Dissection and glue colours (`lem:glues`) -/

/-- The family of scatterings of a family of grouped plane tilings. -/
def Geometry.GroupedFamily.scatterFamily (G : GroupedFamily P) (F' : Set (PlaneTiling G.P')) :
    Set (PlaneTiling P) :=
  {T | ∃ T' ∈ F', G.scatter T'.tiles = T.tiles}

/-- `lem:glues` (generic presentations): the grouped forms are finite
connected unions of original tiles with connected dual graphs (fields of
`GroupedFamily`).  A sofic presentation of a family of grouped plane tilings
transfers, via unique glue colours on internal constituent sides and inert
decorations for surjectivity, to a sofic presentation of its scattering. -/
theorem Decoration.dissection_preserves_sofic (G : GroupedFamily P)
    {F' : Set (PlaneTiling G.P')} (h : IsSofic F') : IsSofic (G.scatterFamily F') := by
  sorry

/-- `lem:glues` (strict presentations): the same transfer for side-to-side
sofic presentations; grouped sides are complete original sides, so exposed
colours stay on whole original sides. -/
theorem Decoration.dissection_preserves_sts_sofic (G : GroupedFamily P)
    {F' : Set (PlaneTiling G.P')} (h : IsSideToSideSofic F') :
    IsSideToSideSofic (G.scatterFamily F') := by
  sorry

/-! ## Compatible grouped hierarchy lift (`lem:grouping-lift`) -/

/-- `T` is the bottom of a `τ^k`-hierarchy of plane tilings. -/
def Grouping.IsPowerHierarchy (τ : Substitution P) (k : ℕ) (T : PlaneTiling P) : Prop :=
  ∃ seq : ℕ → PlaneTiling P, seq 0 = T ∧ ∀ n, τ.decomposeIter k (seq (n + 1)).tiles = (seq n).tiles

/-- `lem:grouping-lift`: when every original form is available as a
singleton group, original `τ^k`-hierarchies are exactly the scatterings of
grouped `σ`-hierarchies. -/
theorem Grouping.hierarchy_lift_iff (τ : Substitution P) (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩}) (T : PlaneTiling P) :
    Grouping.IsPowerHierarchy τ GS.k T ↔
      ∃ seq' : ℕ → PlaneTiling GS.G.P', (∀ n, GS.σ.IsComposition (seq' (n + 1)) (seq' n)) ∧
        GS.G.scatter (seq' 0).tiles = T.tiles := by
  sorry

/-- `lem:grouping-lift` (STS levels): a `τ^k`-hierarchy all of whose levels
are STS lifts to a grouped `σ`-hierarchy scattering level by level onto it,
all of whose levels are STS. -/
theorem Grouping.hierarchy_lift_sts (τ : Substitution P) (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P) (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (hsts : ∀ n, (seq n).SideToSide) :
    ∃ seq' : ℕ → PlaneTiling GS.G.P', (∀ n, GS.σ.IsComposition (seq' (n + 1)) (seq' n)) ∧
      (∀ n, GS.G.scatter (seq' n).tiles = (seq n).tiles) ∧ ∀ n, (seq' n).SideToSide := by
  sorry

/-! ## The hereditary STS core -/

/-- `thm:hereditary-substitution`: an STS substitution with hereditary
listed sides has a side-to-side sofic substitution family. -/
theorem Core.hereditary_sts_substitution_sofic (τ : Substitution P) (hsts : τ.STS)
    (hher : τ.HereditarySides) : IsSideToSideSofic {T | τ.IsSubstitutionTiling T} := by
  sorry

/-- `thm:hereditary-hierarchy`: an STS substitution with hereditary listed
sides has a sofic family of hierarchical plane tilings. -/
theorem Core.hereditary_sts_hierarchy_sofic (τ : Substitution P) (hsts : τ.STS)
    (hher : τ.HereditarySides) : IsSofic {T | τ.IsHierarchical T} := by
  sorry

end Tilings

end
