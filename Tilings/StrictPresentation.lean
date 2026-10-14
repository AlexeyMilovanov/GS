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

/-- Step 1 of the blueprint proof of `sts_hierarchical_of_strict_proper_step2_sts_step1_macro`:
isolate one step of schedule composition. -/
private lemma sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair
    {P : Protoset} {τ : Substitution P} (hτ : τ.STS)
    (Sys : StrictScheduleSystem τ)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (Sys.GS.G.dissect α).tiles))
    (T T' : PlaneTiling Sys.dec.P') (hT : Sys.dec.Proper T)
    (hcomp : Sys.σc.IsComposition T' T) :
    ∃ U : PlaneTiling P,
      U.tiles = Sys.GS.G.scatter (Sys.dec.toDecoration.project T).tiles ∧
      U.SideToSide ∧
      τ.decomposeIter Sys.GS.k
          (Sys.GS.G.scatter (Sys.dec.toDecoration.project T').tiles) = U.tiles ∧
      (∀ j, j ≤ Sys.GS.k →
        SideToSideSet (τ.decomposeIter j
          (Sys.GS.G.scatter (Sys.dec.toDecoration.project T').tiles))) := by
  sorry

/-- Step 2 of the blueprint proof of `sts_hierarchical_of_strict_proper`: at each step
insert the original levels, which are STS by schedule alignment, yielding an infinite original
STS hierarchy. -/
private lemma sts_hierarchical_of_strict_proper_step2_sts_step1_macro
    {P : Protoset} {τ : Substitution P} (hτ : τ.STS)
    (Sys : StrictScheduleSystem τ)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (Sys.GS.G.dissect α).tiles))
    (seq : ℕ → PlaneTiling Sys.dec.P')
    (hproper : ∀ n, Sys.dec.Proper (seq n))
    (h_comp : ∀ n, Sys.σc.IsComposition (seq (n + 1)) (seq n)) :
    ∃ O : ℕ → PlaneTiling P,
      (∀ n, (O n).tiles = Sys.GS.G.scatter (Sys.dec.toDecoration.project (seq n)).tiles) ∧
      (∀ n, τ.decomposeIter Sys.GS.k (O (n + 1)).tiles = (O n).tiles) ∧
      (∀ n, (O n).SideToSide) ∧
      (∀ n j, j ≤ Sys.GS.k → SideToSideSet (τ.decomposeIter j (O (n + 1)).tiles)) := by
  have H : ∀ n, ∃ U : PlaneTiling P,
      U.tiles = Sys.GS.G.scatter (Sys.dec.toDecoration.project (seq n)).tiles ∧
      U.SideToSide ∧
      τ.decomposeIter Sys.GS.k
          (Sys.GS.G.scatter (Sys.dec.toDecoration.project (seq (n + 1))).tiles) = U.tiles ∧
      (∀ j, j ≤ Sys.GS.k →
        SideToSideSet (τ.decomposeIter j
          (Sys.GS.G.scatter (Sys.dec.toDecoration.project (seq (n + 1))).tiles))) := by
    intro n
    exact sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair hτ Sys hΔ (seq n) (seq (n + 1)) (hproper n) (h_comp n)
  let O : ℕ → PlaneTiling P := fun n => Classical.choose (H n)
  have Hspec := fun n => Classical.choose_spec (H n)
  have heq : ∀ n, Sys.GS.G.scatter (Sys.dec.toDecoration.project (seq (n + 1))).tiles = (O (n + 1)).tiles := by
    intro n
    exact (Hspec (n + 1)).1.symm
  refine ⟨O, fun n => (Hspec n).1, fun n => ?_, fun n => (Hspec n).2.1, fun n j hj => ?_⟩
  · have h1 := (Hspec n).2.2.1
    have h2 : Sys.GS.G.scatter (Sys.dec.toDecoration.project (seq (n + 1))).tiles = (O (n + 1)).tiles := heq n
    have h3 : (O n).tiles = τ.decomposeIter Sys.GS.k (Sys.GS.G.scatter (Sys.dec.toDecoration.project (seq (n + 1))).tiles) := h1.symm
    rw [h2] at h3
    exact h3.symm
  · have h1 := (Hspec n).2.2.2 j hj
    have h2 : Sys.GS.G.scatter (Sys.dec.toDecoration.project (seq (n + 1))).tiles = (O (n + 1)).tiles := heq n
    have h3 : SideToSideSet (τ.decomposeIter j (Sys.GS.G.scatter (Sys.dec.toDecoration.project (seq (n + 1))).tiles)) := h1
    rw [h2] at h3
    exact h3

private lemma sts_hierarchical_of_strict_proper_step2_sts_step2_interleave
    {P : Protoset} {τ : Substitution P} {k : ℕ} (hk : 0 < k)
    (O : ℕ → PlaneTiling P)
    (hcomp : ∀ n, τ.decomposeIter k (O (n + 1)).tiles = (O n).tiles)
    (hint : ∀ n j, j ≤ k → SideToSideSet
      (τ.decomposeIter j (O (n + 1)).tiles)) {S : PlaneTiling P}
    (hS : S.tiles = (O 0).tiles) :
    τ.IsSideToSideHierarchical S := by
  sorry

private lemma sts_hierarchical_of_strict_proper_step2_sts {P : Protoset} {τ : Substitution P}
    (hτ : τ.STS) (Sys : StrictScheduleSystem τ)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (Sys.GS.G.dissect α).tiles))
    (seq : ℕ → PlaneTiling Sys.dec.P') (h_proper : ∀ n, Sys.dec.Proper (seq n))
    (h_comp : ∀ n, Sys.σc.IsComposition (seq (n + 1)) (seq n)) {S : PlaneTiling P}
    (hS : S.tiles = Sys.GS.G.scatter (Sys.dec.toDecoration.project (seq 0)).tiles) :
    τ.IsSideToSideHierarchical S := by
  obtain ⟨O, hO_eq, hcomp, hsts, hint⟩ :=
    sts_hierarchical_of_strict_proper_step2_sts_step1_macro hτ Sys hΔ seq h_proper h_comp
  have hS_eq : S.tiles = (O 0).tiles := by
    rw [hS, hO_eq 0]
  exact sts_hierarchical_of_strict_proper_step2_sts_step2_interleave Sys.GS.k_pos O hcomp hint hS_eq

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

private lemma exists_strict_proper_of_sts_hierarchical_step1_seq_power_chain
    (τ : Substitution P) (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.IsComposition (seq (n + 1)) (seq n)) (k n : ℕ) :
    τ.decomposeIter k (seq (n + k)).tiles = (seq n).tiles := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    change τ.decompose (τ.decomposeIter k (seq (n + (k + 1))).tiles) = _
    rw [show n + (k + 1) = (n + 1) + k by omega, ih]
    exact hseq n

/-- Step 1 of the blueprint proof of `exists_strict_proper_of_sts_hierarchical`:
construct the subsequence of k-spaced original levels, which is sts and whose
intermediate scattered levels are also original levels. -/
private lemma exists_strict_proper_of_sts_hierarchical_step1_seq
    {P : Protoset} {τ : Substitution P} (Sys : StrictScheduleSystem τ)
    {S : PlaneTiling P} (hS : τ.IsSideToSideHierarchical S) :
    ∃ seq : ℕ → PlaneTiling P,
      seq 0 = S ∧
      (∀ n, τ.decomposeIter Sys.GS.k (seq (n + 1)).tiles = (seq n).tiles) ∧
      (∀ n, (seq n).SideToSide) ∧
      (∀ (n j : ℕ), j ≤ Sys.GS.k → SideToSideSet (τ.decomposeIter j (seq (n + 1)).tiles)) := by
  obtain ⟨seq, h0, hcomp, hsts⟩ := hS
  use fun n => seq (n * Sys.GS.k)
  constructor
  · rw [Nat.zero_mul]
    exact h0
  constructor
  · intro n
    have h := exists_strict_proper_of_sts_hierarchical_step1_seq_power_chain
      τ seq hcomp Sys.GS.k (n * Sys.GS.k)
    have hrw : n * Sys.GS.k + Sys.GS.k = (n + 1) * Sys.GS.k := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [← hrw]
    exact h
  constructor
  · intro n
    exact hsts (n * Sys.GS.k)
  · intro n j hj
    have h1 := exists_strict_proper_of_sts_hierarchical_step1_seq_power_chain
      τ seq hcomp j (n * Sys.GS.k + Sys.GS.k - j)
    have h_eq : n * Sys.GS.k + Sys.GS.k - j + j = (n + 1) * Sys.GS.k := by
      have hmul : n * Sys.GS.k + Sys.GS.k = (n + 1) * Sys.GS.k := by
        rw [Nat.add_mul, Nat.one_mul]
      rw [← hmul]
      exact Nat.sub_add_cancel (by omega)
    rw [h_eq] at h1
    have h_sts : (seq (n * Sys.GS.k + Sys.GS.k - j)).SideToSide :=
      hsts (n * Sys.GS.k + Sys.GS.k - j)
    have h2 : SideToSideSet (seq (n * Sys.GS.k + Sys.GS.k - j)).tiles := h_sts
    rw [← h1] at h2
    exact h2

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
  have _ := hτ
  obtain ⟨seq, hseq0, hseq_decomp, hseq_sts, hseq_inter⟩ :=
    exists_strict_proper_of_sts_hierarchical_step1_seq Sys hS
  obtain ⟨seq', hseq'_comp, hseq'_scat, hseq'_sts⟩ :=
    Grouping.hierarchy_lift_sts τ Sys.GS hsingle seq hseq_decomp hseq_sts
  have h_inter : ∀ (n j : ℕ), j ≤ Sys.GS.k →
      SideToSideSet (τ.decomposeIter j (Sys.GS.G.scatter (seq' (n + 1)).tiles)) := by
    intro n j hj
    rw [hseq'_scat]
    exact hseq_inter n j hj
  obtain ⟨T, hT_proper, hT_proj⟩ := hcompl seq' hseq'_comp hseq'_sts h_inter
  use T, hT_proper
  have h0 := hseq'_scat 0
  rw [hseq0] at h0
  change Sys.GS.G.scatter (Sys.dec.toDecoration.project T).tiles = S.tiles
  have h_proj2 : Sys.dec.project T = seq' 0 := hT_proj
  change Sys.GS.G.scatter (Sys.dec.project T).tiles = S.tiles
  rw [h_proj2]
  exact h0

end Alignment

end Tilings

end
