import Tilings.Alignment
import Tilings.LocalRules

/-!
# Strict presentation of an STS substitution (`thm:sts-stshierarchy`)

Bridge statements between the strict schedule system of `Tilings.Alignment`
and Theorem 1(b): existence of the strict presentation together with its
composition and completeness properties, and the two halves (soundness and
completeness) of the proof of `thm:sts-stshierarchy`.

Added by hand on 12 October 2026: codex reported that the skeleton had no
statement constructing a strict schedule system from the certificate of
`lem:certificate-exists`, nor the existence half of `lem:schedule-compose`
(`strict_schedule_composition` states only the STS half), so Theorem 1(b)
could not be assembled.  The flexible control chapter needs hereditary listed
sides, which STS does not provide; the strict variant with endpoint schedules
replaces that hypothesis.
-/

noncomputable section

namespace Tilings

open Substitution Geometry

namespace Alignment

variable {P : Protoset}

/-- Existence half of `lem:schedule-compose`: every proper strict coloured
plane tiling has an exact proper coloured composition. -/
def StrictScheduleSystem.HasCompositions {τ : Substitution P} (Sys : StrictScheduleSystem τ) :
    Prop :=
  ∀ T : PlaneTiling Sys.dec.P', Sys.dec.Proper T →
    ∃ T'' : PlaneTiling Sys.dec.P', Sys.dec.Proper T'' ∧ Sys.σc.IsComposition T'' T

/-- Completeness of the strict presentation (`thm:sts-stshierarchy`, "origin
chains give legal tiles"): every grouped `σ'`-hierarchy whose levels and whose
scattered intermediate original levels are all side-to-side is the projection
of a proper strict coloured plane tiling. -/
def StrictScheduleSystem.Complete {τ : Substitution P} (Sys : StrictScheduleSystem τ) : Prop :=
  ∀ seq' : ℕ → PlaneTiling Sys.GS.G.P',
    (∀ n, Sys.GS.σ.IsComposition (seq' (n + 1)) (seq' n)) →
    (∀ n, (seq' n).SideToSide) →
    (∀ n, ∀ j ≤ Sys.GS.k, SideToSideSet (τ.decomposeIter j (Sys.GS.G.scatter (seq' n).tiles))) →
    ∃ T : PlaneTiling Sys.dec.P', Sys.dec.Proper T ∧ Sys.dec.toDecoration.project T = seq' 0

/-- `lem:strict-projection`: the projection of a coloured composition is a
grouped composition (`rule_proj` and `θ_eq` of the strict schedule system). -/
theorem StrictScheduleSystem.isComposition_project {τ : Substitution P}
    (Sys : StrictScheduleSystem τ) {T'' T : PlaneTiling Sys.dec.P'}
    (h : Sys.σc.IsComposition T'' T) :
    Sys.GS.σ.IsComposition (Sys.dec.toDecoration.project T'')
      (Sys.dec.toDecoration.project T) := by
  sorry

/-- `lem:strict-presentation`: for every STS substitution there is a strict
schedule system (the strict typed decoration of the certificate of
`lem:certificate-exists`, with second component zero, endpoint schedules and
whole-side ports) whose grouped family contains every original form as a
singleton group, whose dissections stay side-to-side under all
decompositions, and which has exact proper compositions (the existence half
of `lem:schedule-compose`) and is complete. -/
theorem exists_strict_schedule_system (τ : Substitution P) (hτ : τ.STS) :
    ∃ Sys : StrictScheduleSystem τ,
      (∀ p : P.Form, ∃ α, (Sys.GS.G.dissect α).tiles = {⟨p, 0⟩}) ∧
      (∀ α j, SideToSideSet (τ.decomposeIter j (Sys.GS.G.dissect α).tiles)) ∧
      Sys.HasCompositions ∧ Sys.Complete := by
  sorry

/-- Step 1 of the blueprint proof of `sts_hierarchical_of_strict_proper`: repeatedly
apply strict schedule composition to obtain an infinite sequence of proper compositions. -/
private lemma sts_hierarchical_of_strict_proper_step1_seq {P : Protoset} {τ : Substitution P}
    (Sys : StrictScheduleSystem τ) (hcomp : Sys.HasCompositions) {T : PlaneTiling Sys.dec.P'}
    (hT : Sys.dec.Proper T) :
    ∃ seq : ℕ → PlaneTiling Sys.dec.P', seq 0 = T ∧ ∀ n, Sys.dec.Proper (seq n) ∧
      Sys.σc.IsComposition (seq (n + 1)) (seq n) := by
  sorry

/-- Step 2 of the blueprint proof of `sts_hierarchical_of_strict_proper`: at each step
insert the original levels, which are STS by schedule alignment, yielding an infinite original
STS hierarchy. -/
private lemma sts_hierarchical_of_strict_proper_step2_sts {P : Protoset} {τ : Substitution P}
    (hτ : τ.STS) (Sys : StrictScheduleSystem τ)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (Sys.GS.G.dissect α).tiles))
    (seq : ℕ → PlaneTiling Sys.dec.P') (h_proper : ∀ n, Sys.dec.Proper (seq n))
    (h_comp : ∀ n, Sys.σc.IsComposition (seq (n + 1)) (seq n)) {S : PlaneTiling P}
    (hS : S.tiles = Sys.GS.G.scatter (Sys.dec.toDecoration.project (seq 0)).tiles) :
    τ.IsSideToSideHierarchical S := by
  sorry

/-- `lem:strict-sound` (soundness half of `thm:sts-stshierarchy`): the
scattering of the projection of a proper strict coloured plane tiling is a
side-to-side `τ`-hierarchical plane tiling (iterate `lem:schedule-compose`
and insert the side-to-side intermediate original levels). -/
theorem sts_hierarchical_of_strict_proper {τ : Substitution P} (hτ : τ.STS)
    (Sys : StrictScheduleSystem τ)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (Sys.GS.G.dissect α).tiles))
    (hcomp : Sys.HasCompositions) {T : PlaneTiling Sys.dec.P'} (hT : Sys.dec.Proper T)
    {S : PlaneTiling P}
    (hS : S.tiles = Sys.GS.G.scatter (Sys.dec.toDecoration.project T).tiles) :
    τ.IsSideToSideHierarchical S := by
  obtain ⟨seq, hseq0, hseq⟩ := sts_hierarchical_of_strict_proper_step1_seq Sys hcomp hT
  have hproper : ∀ n, Sys.dec.Proper (seq n) := fun n => (hseq n).1
  have hcomp_seq : ∀ n, Sys.σc.IsComposition (seq (n + 1)) (seq n) := fun n => (hseq n).2
  apply sts_hierarchical_of_strict_proper_step2_sts hτ Sys hΔ seq hproper hcomp_seq
  rwa [hseq0]

/-- `lem:strict-complete` (completeness half of `thm:sts-stshierarchy`): every
side-to-side `τ`-hierarchical plane tiling is the scattering of the projection
of a proper strict coloured plane tiling (lift by `lem:grouping-lift`, then
`Complete`). -/
theorem exists_strict_proper_of_sts_hierarchical {τ : Substitution P} (hτ : τ.STS)
    (Sys : StrictScheduleSystem τ)
    (hsingle : ∀ p : P.Form, ∃ α, (Sys.GS.G.dissect α).tiles = {⟨p, 0⟩})
    (hcompl : Sys.Complete) {S : PlaneTiling P} (hS : τ.IsSideToSideHierarchical S) :
    ∃ T : PlaneTiling Sys.dec.P', Sys.dec.Proper T ∧
      Sys.GS.G.scatter (Sys.dec.toDecoration.project T).tiles = S.tiles := by
  sorry

end Alignment

end Tilings

end
