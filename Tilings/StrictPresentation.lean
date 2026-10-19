import Tilings.Alignment
import Tilings.LocalRules
import Tilings.Control.Strict

/-!
# Strict presentation of an STS substitution (`thm:sts-stshierarchy`)

Bridge theorems between the strict schedule system of `Tilings.Alignment`
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
open Set Pointwise

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

private lemma
sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_supp_trans
    {P : Protoset} (v : Pt) (S : Set (PlacedTile P)) :
    support (translateSet v S) = v +ᵥ support S := by
  have hc : ∀ A : PlacedTile P, (A.translate v).carrier = v +ᵥ A.carrier := by
    intro A
    show (v +ᵥ A.anchor) +ᵥ _ = v +ᵥ (A.anchor +ᵥ _)
    rw [vadd_vadd]
    rfl
  simp only [support, translateSet, Set.biUnion_image, hc, Set.vadd_set_iUnion₂]

private lemma
sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_tile_supp
    {P : Protoset} (G : GroupedFamily P) (A : PlacedTile G.P') :
    support (G.scatterTile A) = A.carrier := by
  rw [GroupedFamily.scatterTile,
    sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_supp_trans,
    G.support_eq A.form]
  rfl

private lemma
sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_scat_supp
    {P : Protoset} (G : GroupedFamily P) (S : Set (PlacedTile G.P')) :
    support (G.scatter S) = support S := by
  ext x
  simp only [GroupedFamily.scatter, support, Set.mem_iUnion]
  constructor
  · rintro ⟨B, ⟨A, hAS, hBA⟩, hxB⟩
    refine ⟨A, hAS, ?_⟩
    rw [←
      sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_tile_supp
        G A]
    simp only [support, Set.mem_iUnion]
    exact ⟨B, hBA, hxB⟩
  · rintro ⟨A, hAS, hxA⟩
    rw [←
      sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_tile_supp
        G A] at hxA
    simp only [support, Set.mem_iUnion] at hxA
    rcases hxA with ⟨B, hBA, hxB⟩
    exact ⟨B, ⟨A, hAS, hBA⟩, hxB⟩

private lemma
sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_car_trans
    {P : Protoset} (A : PlacedTile P) (v : Pt) :
    (A.translate v).carrier = v +ᵥ A.carrier := by
  simp only [PlacedTile.translate, PlacedTile.carrier, Set.ext_iff,
    Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  intro y
  constructor <;> intro hy
  · convert hy using 1
    all_goals abel
  · convert hy using 1
    all_goals abel

private lemma
sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_scat_disj
    {P : Protoset} (G : GroupedFamily P) (T : PlaneTiling G.P') :
    DisjointInteriors (G.scatter T.tiles) := by
  intro B hB C hC hBC
  simp only [GroupedFamily.scatter, Set.mem_iUnion] at hB hC
  obtain ⟨A, hAT, hBA⟩ := hB
  obtain ⟨D, hDT, hCD⟩ := hC
  by_cases hAD : A = D
  · subst D
    simp only [GroupedFamily.scatterTile, translateSet, Set.mem_image] at hBA hCD
    obtain ⟨B₀, hB₀, rfl⟩ := hBA
    obtain ⟨C₀, hC₀, hCeq⟩ := hCD
    subst C
    have hB₀C₀ : B₀ ≠ C₀ := by
      intro h
      apply hBC
      rw [h]
    have hd := (G.dissect A.form).disjoint hB₀ hC₀ hB₀C₀
    dsimp [Function.onFun] at hd ⊢
    rw [
      sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_car_trans,
      sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_car_trans,
      interior_vadd, interior_vadd]
    exact disjoint_image_of_injective (add_right_injective A.anchor) hd
  · have hBsub : interior B.carrier ⊆ interior A.carrier := by
      apply interior_maximal
      · apply interior_subset.trans
        rw [←
          sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_tile_supp
            G A]
        intro x hx
        simp only [support, Set.mem_iUnion]
        exact ⟨B, hBA, hx⟩
      · exact isOpen_interior
    have hCsub : interior C.carrier ⊆ interior D.carrier := by
      apply interior_maximal
      · apply interior_subset.trans
        rw [←
          sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_tile_supp
            G D]
        intro x hx
        simp only [support, Set.mem_iUnion]
        exact ⟨C, hCD, hx⟩
      · exact isOpen_interior
    exact (T.disjoint hAT hDT hAD).mono hBsub hCsub

private noncomputable def
sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_scat_tiling
    {P : Protoset} (G : GroupedFamily P) (T : PlaneTiling G.P') : PlaneTiling P where
  tiles := G.scatter T.tiles
  cover := by
    rw [
      sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_scat_supp,
      T.cover]
  disjoint :=
    sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_scat_disj G T

private lemma
sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_scat_trans
    {P : Protoset} (G : GroupedFamily P) (v : Pt)
    (S : Set (PlacedTile G.P')) :
    G.scatter (translateSet v S) = translateSet v (G.scatter S) := by
  ext B
  simp only [GroupedFamily.scatter, GroupedFamily.scatterTile, translateSet,
    Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨A, ⟨A₀, hA₀, rfl⟩, C, hC, rfl⟩
    refine ⟨C.translate A₀.anchor, ⟨A₀, hA₀, C, hC, rfl⟩, ?_⟩
    simp [PlacedTile.translate, add_assoc]
  · rintro ⟨B₀, ⟨A, hAS, C, hC, rfl⟩, rfl⟩
    refine ⟨A.translate v, ⟨A, hAS, rfl⟩, C, hC, ?_⟩
    simp [PlacedTile.translate, add_assoc]

private lemma
sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_dec_trans
    {P : Protoset} (τ : Substitution P) (v : Pt) (S : Set (PlacedTile P)) :
    τ.decompose (translateSet v S) =
      translateSet (τ.θ • v) (τ.decompose S) := by
  ext C
  simp only [Substitution.decompose, Substitution.decomposeTile, translateSet,
    Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨A, ⟨A₀, hA₀, rfl⟩, B, hB, rfl⟩
    refine ⟨B.translate (τ.θ • A₀.anchor), ⟨A₀, hA₀, B, hB, rfl⟩, ?_⟩
    apply PlacedTile.ext
    · rfl
    · simp only [PlacedTile.translate, vadd_eq_add, smul_add]
      abel
  · rintro ⟨C₀, ⟨A, hAS, B, hB, rfl⟩, rfl⟩
    refine ⟨A.translate v, ⟨A, hAS, rfl⟩, B, hB, ?_⟩
    apply PlacedTile.ext
    · rfl
    · simp only [PlacedTile.translate, vadd_eq_add, smul_add]
      abel

private lemma
sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_iter_trans
    {P : Protoset} (τ : Substitution P) (n : ℕ) (v : Pt)
    (S : Set (PlacedTile P)) :
    τ.decomposeIter n (translateSet v S) =
      translateSet (τ.θ ^ n • v) (τ.decomposeIter n S) := by
  induction n with
  | zero => simp [Substitution.decomposeIter]
  | succ n ih =>
      change τ.decompose (τ.decomposeIter n (translateSet v S)) = _
      rw [ih,
        sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_dec_trans]
      rw [pow_succ', mul_smul]
      rfl

private lemma
sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_iter_union
    {P : Protoset} (τ : Substitution P) {ι : Type*} (n : ℕ) (s : Set ι)
    (f : ι → Set (PlacedTile P)) :
    τ.decomposeIter n (⋃ i ∈ s, f i) = ⋃ i ∈ s, τ.decomposeIter n (f i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change τ.decompose (τ.decomposeIter n (⋃ i ∈ s, f i)) = _
      rw [ih]
      ext C
      simp only [Substitution.decompose, Set.mem_iUnion]
      constructor
      · rintro ⟨B, ⟨i, hi, hB⟩, hCB⟩
        refine ⟨i, hi, ?_⟩
        change C ∈ τ.decompose (τ.decomposeIter n (f i))
        simp only [Substitution.decompose, Set.mem_iUnion]
        exact ⟨B, hB, hCB⟩
      · rintro ⟨i, hi, hC⟩
        change C ∈ τ.decompose (τ.decomposeIter n (f i)) at hC
        simp only [Substitution.decompose, Set.mem_iUnion] at hC
        rcases hC with ⟨B, hB, hCB⟩
        exact ⟨B, ⟨i, hi, hB⟩, hCB⟩

private lemma
sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_dec_tile
    {P : Protoset} (τ : Substitution P) (GS : GroupedSubstitution τ)
    (A : PlacedTile GS.G.P') :
    GS.G.scatter (GS.σ.decomposeTile A) =
      τ.decomposeIter GS.k (GS.G.scatterTile A) := by
  rw [Substitution.decomposeTile,
    sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_scat_trans,
    GS.θ_eq, GS.compat, GroupedFamily.scatterTile,
    sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_iter_trans]

private lemma
sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_dec_scat
    {P : Protoset} (τ : Substitution P) (GS : GroupedSubstitution τ)
    (S : Set (PlacedTile GS.G.P')) :
    GS.G.scatter (GS.σ.decompose S) =
      τ.decomposeIter GS.k (GS.G.scatter S) := by
  change GS.G.scatter (GS.σ.decompose S) =
    τ.decomposeIter GS.k (⋃ A ∈ S, GS.G.scatterTile A)
  rw [sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_iter_union]
  ext B
  simp only [Substitution.decompose, GroupedFamily.scatter, Set.mem_iUnion]
  constructor
  · rintro ⟨C, ⟨A, hAS, hCA⟩, hBC⟩
    refine ⟨A, hAS, ?_⟩
    rw [←
      sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_dec_tile
        τ GS A]
    simp only [GroupedFamily.scatter, Set.mem_iUnion]
    exact ⟨C, hCA, hBC⟩
  · rintro ⟨A, hAS, hBA⟩
    rw [←
      sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_dec_tile
        τ GS A] at hBA
    simp only [GroupedFamily.scatter, Set.mem_iUnion] at hBA
    rcases hBA with ⟨C, hC, hBC⟩
    exact ⟨C, ⟨A, hAS, hC⟩, hBC⟩

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
  let U :=
    sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_scat_tiling
      Sys.GS.G (Sys.dec.toDecoration.project T)
  have hproject := Sys.isComposition_project hcomp
  have hreduce :
      τ.decomposeIter Sys.GS.k
          (Sys.GS.G.scatter (Sys.dec.toDecoration.project T').tiles) = U.tiles := by
    change τ.decomposeIter Sys.GS.k
      (Sys.GS.G.scatter (Sys.dec.toDecoration.project T').tiles) =
        Sys.GS.G.scatter (Sys.dec.toDecoration.project T).tiles
    rw [←
      sts_hierarchical_of_strict_proper_step2_sts_step1_macro_step1_pair_dec_scat
        τ Sys.GS]
    rw [hproject]
  have hsts := Alignment.strict_schedule_composition (τ := τ) hτ Sys hΔ T T' hT hcomp
  refine ⟨U, rfl, ?_, hreduce, ?_⟩
  · change SideToSideSet U.tiles
    rw [← hreduce]
    exact hsts.2 Sys.GS.k le_rfl
  · exact hsts.2

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

private lemma sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_support_translate
    {P : Protoset} (v : Pt) (S : Set (PlacedTile P)) :
    support (translateSet v S) = v +ᵥ support S := by
  ext x
  simp only [support, translateSet, PlacedTile.translate, PlacedTile.carrier,
    Set.mem_iUnion, Set.mem_image, Set.mem_vadd_set_iff_neg_vadd_mem]
  constructor
  · rintro ⟨A, ⟨B, hB, rfl⟩, hx⟩
    exact ⟨B, hB, by simpa [← add_assoc] using hx⟩
  · rintro ⟨A, hA, hx⟩
    refine ⟨⟨A.form, v +ᵥ A.anchor⟩, ⟨A, hA, rfl⟩, ?_⟩
    simpa [← add_assoc] using hx

private lemma sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_support_tile
    {P : Protoset} (τ : Substitution P) (A : PlacedTile P) :
    support (τ.decomposeTile A) = τ.θ • A.carrier := by
  dsimp [Substitution.decomposeTile]
  rw [sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_support_translate,
    τ.support_eq, PlacedTile.carrier]
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, hx⟩
    refine ⟨A.anchor + y, ?_, ?_⟩
    · simpa
    · rw [smul_add]
      calc
        τ.θ • A.anchor + τ.θ • y =
            τ.θ • A.anchor + (-(τ.θ • A.anchor) + x) := by congr 1
        _ = x := by abel
  · rintro ⟨y, hy, rfl⟩
    refine ⟨-A.anchor + y, ?_, ?_⟩
    · simpa
    · simp [smul_add]

private lemma sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_support
    {P : Protoset} (τ : Substitution P) (S : Set (PlacedTile P)) :
    support (τ.decompose S) = τ.θ • support S := by
  dsimp [Substitution.decompose, support]
  rw [Set.smul_set_iUnion₂]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨A, ⟨B, hB, hA⟩, hx⟩
    refine ⟨B, hB, ?_⟩
    have h : x ∈ support (τ.decomposeTile B) := by
      simp only [support, Set.mem_iUnion]
      exact ⟨A, hA, hx⟩
    rwa [sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_support_tile] at h
  · rintro ⟨A, hA, hx⟩
    have h : x ∈ support (τ.decomposeTile A) := by
      rwa [sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_support_tile]
    simp only [support, Set.mem_iUnion] at h
    rcases h with ⟨B, hB, hxB⟩
    exact ⟨B, ⟨A, hA, hB⟩, hxB⟩

private lemma sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_disjoint
    {P : Protoset} (τ : Substitution P) (S : Set (PlacedTile P))
    (hS : DisjointInteriors S) : DisjointInteriors (τ.decompose S) := by
  intro A hA B hB hAB
  simp only [Substitution.decompose, Set.mem_iUnion] at hA hB
  rcases hA with ⟨X, hX, hAX⟩
  rcases hB with ⟨Y, hY, hBY⟩
  simp only [Substitution.decomposeTile, translateSet, Set.mem_image] at hAX hBY
  rcases hAX with ⟨C, hC, rfl⟩
  rcases hBY with ⟨D, hD, rfl⟩
  by_cases hXY : X = Y
  · subst Y
    have hCD : C ≠ D := by
      intro h
      subst D
      exact hAB rfl
    have hdisj := (τ.rule X.form).disjoint hC hD hCD
    have hcarrier (E : PlacedTile P) (v : Pt) :
        (E.translate v).carrier = v +ᵥ E.carrier := by
      dsimp [PlacedTile.carrier, PlacedTile.translate]
      rw [← vadd_assoc, vadd_eq_add]
    dsimp [Function.onFun] at hdisj ⊢
    rw [hcarrier, hcarrier, interior_vadd, interior_vadd]
    rw [Set.disjoint_left] at hdisj ⊢
    intro z hzC hzD
    apply hdisj
    · rwa [Set.mem_vadd_set_iff_neg_vadd_mem] at hzC
    · rwa [Set.mem_vadd_set_iff_neg_vadd_mem] at hzD
  · have hθ : τ.θ ≠ 0 := by linarith [τ.one_lt]
    have hCX : interior (C.translate (τ.θ • X.anchor)).carrier ⊆
        interior (τ.θ • X.carrier) := by
      apply interior_maximal
      · intro z hz
        have hz' : z ∈ support (τ.decomposeTile X) := by
          simp only [support, Set.mem_iUnion]
          refine ⟨C.translate (τ.θ • X.anchor), ?_, interior_subset hz⟩
          simp only [Substitution.decomposeTile, translateSet, Set.mem_image]
          exact ⟨C, hC, rfl⟩
        rwa [sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_support_tile] at hz'
      · exact isOpen_interior
    have hDY : interior (D.translate (τ.θ • Y.anchor)).carrier ⊆
        interior (τ.θ • Y.carrier) := by
      apply interior_maximal
      · intro z hz
        have hz' : z ∈ support (τ.decomposeTile Y) := by
          simp only [support, Set.mem_iUnion]
          refine ⟨D.translate (τ.θ • Y.anchor), ?_, interior_subset hz⟩
          simp only [Substitution.decomposeTile, translateSet, Set.mem_image]
          exact ⟨D, hD, rfl⟩
        rwa [sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_support_tile] at hz'
      · exact isOpen_interior
    have hparents := hS hX hY hXY
    dsimp [Function.onFun] at hparents
    have hscaled : Disjoint (interior (τ.θ • X.carrier))
        (interior (τ.θ • Y.carrier)) := by
      rw [interior_smul₀ hθ, interior_smul₀ hθ]
      rw [Set.disjoint_left] at hparents ⊢
      intro z hzX hzY
      apply hparents
      · exact (Set.mem_smul_set_iff_inv_smul_mem₀ hθ _ _).mp hzX
      · exact (Set.mem_smul_set_iff_inv_smul_mem₀ hθ _ _).mp hzY
    exact hscaled.mono hCX hDY

private noncomputable def
    sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_decompose_tiling
    {P : Protoset} (τ : Substitution P) (T : PlaneTiling P) : PlaneTiling P where
  tiles := τ.decompose T.tiles
  cover := by
    rw [sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_support, T.cover]
    exact Set.smul_set_univ₀ (by linarith [τ.one_lt])
  disjoint :=
    sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_disjoint
      τ T.tiles T.disjoint

private def sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_iter_tiling
    {P : Protoset} (τ : Substitution P) : ℕ → PlaneTiling P → PlaneTiling P
  | 0, T => T
  | n + 1, T =>
      sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_decompose_tiling
        τ (sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_iter_tiling τ n T)

private lemma sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_iter_tiles
    {P : Protoset} (τ : Substitution P) (n : ℕ) (T : PlaneTiling P) :
    (sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_iter_tiling τ n T).tiles =
      τ.decomposeIter n T.tiles := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change τ.decompose
        (sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_iter_tiling τ n T).tiles = _
      rw [ih]
      rfl

private lemma sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_tiling_ext
    {P : Protoset} {T₁ T₂ : PlaneTiling P} (h : T₁.tiles = T₂.tiles) : T₁ = T₂ := by
  cases T₁
  cases T₂
  cases h
  rfl

private lemma sts_hierarchical_of_strict_proper_step2_sts_step2_interleave
    {P : Protoset} {τ : Substitution P} {k : ℕ} (hk : 0 < k)
    (O : ℕ → PlaneTiling P)
    (hcomp : ∀ n, τ.decomposeIter k (O (n + 1)).tiles = (O n).tiles)
    (hint : ∀ n j, j ≤ k → SideToSideSet
      (τ.decomposeIter j (O (n + 1)).tiles)) {S : PlaneTiling P}
    (hS : S.tiles = (O 0).tiles) :
    τ.IsSideToSideHierarchical S := by
  let fine : ℕ → PlaneTiling P := fun n =>
    sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_iter_tiling τ
      (k - n % k) (O (n / k + 1))
  refine ⟨fine, ?_, ?_, ?_⟩
  · apply sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_tiling_ext
    dsimp [fine]
    rw [sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_iter_tiles]
    change τ.decomposeIter (k - 0 % k) (O (0 / k + 1)).tiles = S.tiles
    rw [Nat.zero_mod, Nat.zero_div, Nat.zero_add, Nat.sub_zero, hcomp 0]
    exact hS.symm
  · intro n
    change τ.decompose (fine (n + 1)).tiles = (fine n).tiles
    rw [show (fine (n + 1)).tiles =
        τ.decomposeIter (k - (n + 1) % k) (O ((n + 1) / k + 1)).tiles by
      exact sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_iter_tiles τ _ _]
    rw [show (fine n).tiles =
        τ.decomposeIter (k - n % k) (O (n / k + 1)).tiles by
      exact sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_iter_tiles τ _ _]
    by_cases hdvd : k ∣ n + 1
    · have hdiv : (n + 1) / k = n / k + 1 := Nat.succ_div_of_dvd hdvd
      have hmod : (n + 1) % k = 0 := Nat.mod_eq_zero_of_dvd hdvd
      have hn := Nat.mod_add_div n k
      have hn1 := Nat.mod_add_div (n + 1) k
      rw [hmod, hdiv] at hn1
      simp only [zero_add, mul_add, mul_one] at hn1
      have hr : n % k + 1 = k := by omega
      rw [hmod, hdiv]
      change τ.decompose (τ.decomposeIter k (O (n / k + 1 + 1)).tiles) = _
      rw [hcomp (n / k + 1)]
      have hexp : k - n % k = 1 := by omega
      rw [hexp]
      rfl
    · have hk_ne_one : k ≠ 1 := by
        intro h
        subst k
        exact hdvd (one_dvd _)
      have hk_one : 1 < k := by omega
      have hr_lt : n % k + 1 < k := by
        have hr := Nat.mod_lt n hk
        by_contra hlt
        have heq : n % k + 1 = k := by omega
        apply hdvd
        rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
        rw [Nat.mod_eq_of_lt hk_one, heq, Nat.mod_self]
      have hmod : (n + 1) % k = n % k + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt hk_one, Nat.mod_eq_of_lt hr_lt]
      have hdiv : (n + 1) / k = n / k := Nat.succ_div_of_not_dvd hdvd
      rw [hmod, hdiv]
      have hr := Nat.mod_lt n hk
      have hexp : k - (n % k + 1) + 1 = k - n % k := by omega
      change τ.decomposeIter (k - (n % k + 1) + 1)
        (O (n / k + 1)).tiles = _
      rw [hexp]
  · intro n
    change SideToSideSet (fine n).tiles
    rw [show (fine n).tiles =
        τ.decomposeIter (k - n % k) (O (n / k + 1)).tiles by
      exact sts_hierarchical_of_strict_proper_step2_sts_step2_interleave_iter_tiles τ _ _]
    apply hint (n / k) (k - n % k)
    omega

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
