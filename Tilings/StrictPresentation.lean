import Tilings.Alignment
import Tilings.LocalRules
import Tilings.Control.Strict

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

/-- `lem:strict-projection`: the projection of a coloured composition is a
grouped composition (`rule_proj` and `θ_eq` of the strict schedule system). -/
theorem StrictScheduleSystem.isComposition_project {τ : Substitution P}
    (Sys : StrictScheduleSystem τ) {T'' T : PlaneTiling Sys.dec.P'}
    (h : Sys.σc.IsComposition T'' T) :
    Sys.GS.σ.IsComposition (Sys.dec.toDecoration.project T'')
      (Sys.dec.toDecoration.project T) := by
  have htile (A : PlacedTile Sys.dec.P') :
      Sys.GS.σ.decomposeTile (Sys.dec.toDecoration.projTile A) =
        Sys.dec.toDecoration.projTile '' Sys.σc.decomposeTile A := by
    have hrule := Sys.rule_proj A.form
    dsimp [Substitution.decomposeTile, translateSet]
    ext B
    simp only [Set.mem_image]
    constructor
    · rintro ⟨C, hC, rfl⟩
      change C ∈ (Sys.GS.σ.rule (Sys.dec.proj A.form)).tiles at hC
      rw [← hrule] at hC
      rcases hC with ⟨D, hD, rfl⟩
      refine ⟨D.translate (Sys.σc.θ • A.anchor), ⟨D, hD, rfl⟩, ?_⟩
      rcases D with ⟨fD, aD⟩
      rcases A with ⟨fA, aA⟩
      dsimp [Decoration.projTile, PlacedTile.translate]
      rw [Sys.θ_eq]
    · rintro ⟨C, ⟨D, hD, rfl⟩, rfl⟩
      refine ⟨Sys.dec.toDecoration.projTile D, ?_, ?_⟩
      · change Sys.dec.toDecoration.projTile D ∈
          (Sys.GS.σ.rule (Sys.dec.proj A.form)).tiles
        rw [← hrule]
        exact ⟨D, hD, rfl⟩
      · rcases D with ⟨fD, aD⟩
        rcases A with ⟨fA, aA⟩
        dsimp [Decoration.projTile, PlacedTile.translate]
        rw [Sys.θ_eq]
  dsimp [Substitution.IsComposition] at h ⊢
  change Sys.GS.σ.decompose (Sys.dec.toDecoration.projTile '' T''.tiles) =
    Sys.dec.toDecoration.projTile '' T.tiles
  rw [← h]
  dsimp [Substitution.decompose]
  have hleft :
      (⋃ A ∈ Sys.dec.toDecoration.projTile '' T''.tiles, Sys.GS.σ.decomposeTile A) =
        ⋃ A ∈ T''.tiles, Sys.GS.σ.decomposeTile (Sys.dec.toDecoration.projTile A) := by
    ext B
    simp
  rw [hleft]
  simp_rw [htile]
  rw [Set.image_iUnion₂]

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
  obtain ⟨C, m, hC⟩ := existsMacroCertificate τ hτ
  exact Planned.Strict.exists_strict_schedule_system_of_certificate τ hτ C m hC

/-- Step 1 of the blueprint proof of `sts_hierarchical_of_strict_proper`: repeatedly
apply strict schedule composition to obtain an infinite sequence of proper compositions. -/
private lemma sts_hierarchical_of_strict_proper_step1_seq {P : Protoset} {τ : Substitution P}
    (Sys : StrictScheduleSystem τ) (hcomp : Sys.HasCompositions) {T : PlaneTiling Sys.dec.P'}
    (hT : Sys.dec.Proper T) :
    ∃ seq : ℕ → PlaneTiling Sys.dec.P', seq 0 = T ∧ ∀ n, Sys.dec.Proper (seq n) ∧
      Sys.σc.IsComposition (seq (n + 1)) (seq n) := by
  let seq_type := { T' : PlaneTiling Sys.dec.P' // Sys.dec.Proper T' }
  let next (T' : seq_type) : seq_type :=
    ⟨Classical.choose (hcomp T'.val T'.property), (Classical.choose_spec (hcomp T'.val T'.property)).1⟩
  let seq_f : ℕ → seq_type := fun n => Nat.recOn n ⟨T, hT⟩ (fun _ T' => next T')
  use fun n => (seq_f n).val
  refine ⟨rfl, fun n => ?_⟩
  exact ⟨(seq_f n).property, (Classical.choose_spec (hcomp (seq_f n).val (seq_f n).property)).2⟩

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
