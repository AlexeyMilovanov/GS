import Tilings.Geometry.Grouping.Foundation

/-!
# The geometric macrocertificate construction

The geometric, grouping and routing foundation is compiled separately. This file
contains the certificate construction and retains the original theorem names.
-/

open Set Pointwise

noncomputable section

namespace Tilings

namespace Geometry

variable {P : Protoset}

/-! ### Helpers for `existsMacroCertificate` -/

/-- The first, purely geometric, choice package in the construction of
`lem:certificate-exists`.  It records the noncircular order of the choices and the labelled
catalogue obtained from the quantitative annular groupings. -/
private structure existsMacroCertificate_GroupingSeed (τ : Substitution P) where
  M : MeshConstants P
  Csep : ℝ
  Cloc : ℝ
  Clen : ℝ
  Cerr : ℝ
  C : ℝ
  constants_pos : 0 < Csep ∧ 0 < Cloc ∧ 0 < Clen ∧ 0 ≤ Cerr ∧ 0 < C
  Csep_eq : Csep = 1000
  Cloc_eq : Cloc = 20
  Clen_eq : Clen = 2
  Cerr_eq : Cerr = 0
  C_eq : C = 7
  R : ℝ
  R_separates : Csep * M.D ≤ R
  R_routes : 10000 * ((M.K0 : ℝ) + 3) * M.D ≤ R
  private_edges : (M.K0 : ℝ) + 2 ≤ (⌊R / (Clen * M.D)⌋₊ : ℝ) - Cerr
  Qmax : ℕ
  Qmax_eq : Qmax = M.K0 * ⌈4 * C ^ 2 * R ^ 2 / M.a⌉₊
  N : ℕ
  N_two : 2 ≤ N
  N_dominates : 3 * Qmax < 4 * N
  k : ℕ
  k_pos : 0 < k
  centre : P.Form → Pt
  square_margin : ∀ p, square (centre p) ((N : ℝ) * R / 2 + R) + Binf (10 * M.D) ⊆
    interior ((τ.θ ^ k) • (P.disk p).carrier)
  annular : ∀ p, AnnularGrouping M (τ.supertile k p) (centre p) N R
  annular_quantitative : ∀ p,
    (∀ j : Fin (4 * N), ((annular p).spokes.piece j).carrier ⊆
      Metric.cthickening (Cloc * M.D) (idealTrapezoid (centre p) N R M.D (j : ℕ))) ∧
    (∀ j : Fin (4 * N),
      (⌊R / (Clen * M.D)⌋₊ : ℝ) - Cerr ≤ ((privateOuterEdges (annular p) j).ncard : ℝ)) ∧
    (∀ j : Fin (4 * N), Metric.diam ((annular p).spokes.piece j).carrier ≤ C * R) ∧
    ∀ j : Fin (4 * N),
      ((annular p).spokes.piece j).disk.n ≤ M.K0 * ⌈4 * C ^ 2 * R ^ 2 / M.a⌉₊
  annular_windows : ∀ p, ∃ e : Fin (4 * N) → Fin 4 → Set Pt,
    (∀ j i, e j i ∈ privateOuterEdges (annular p) j) ∧
      ∀ j i j' i', (j, i) ≠ (j', i') →
        ∀ x ∈ e j i, ∀ y ∈ e j' i', R / 10 ≤ dist x y
  GS : GroupedSubstitution τ
  grouped_power : GS.k = k
  ccw : ∀ α, pdCCW (GS.G.P'.disk α)
  large : P.Form → GS.G.P'.Form
  /-- the large forms of distinct original forms are distinct (the catalogue has one large form per original form) -/
  large_injective : Function.Injective large
  small : P.Form → Fin (4 * N) → GS.G.P'.Form
  original : P.Form → GS.G.P'.Form
  large_dissect : ∀ p, (GS.G.dissect (large p)).tiles = (annular p).L.faces
  small_dissect : ∀ p j, (GS.G.dissect (small p j)).tiles = ((annular p).spokes.piece j).faces
  original_dissect : ∀ p, (GS.G.dissect (original p)).tiles = {⟨p, 0⟩}
  catalogue : ∀ α,
    (∃ p v, (GS.G.dissect α).tiles = translateSet v (annular p).L.faces) ∨
    (∃ p j v, (GS.G.dissect α).tiles = translateSet v ((annular p).spokes.piece j).faces) ∨
    ∃ p v, (GS.G.dissect α).tiles = {⟨p, v⟩}
  /-- The construction uses exactly the three labelled catalogue constructors.  In
  particular there are no additional translated large forms on which the marking
  definition would incorrectly mark every listed side. -/
  catalogue_exact : ∀ α, (∃ p, α = large p) ∨
    (∃ p j, α = small p j) ∨ ∃ p, α = original p
  /-- Labels in the three summands remain distinct, including between different
  annular catalogues.  The concrete seed uses the sum constructors themselves. -/
  catalogue_labels_injective : Function.Injective
    (fun x : P.Form ⊕ ((P.Form × Fin (4 * N)) ⊕ P.Form) =>
      match x with
      | Sum.inl p => large p
      | Sum.inr (Sum.inl (p, j)) => small p j
      | Sum.inr (Sum.inr p) => original p)
  inside_supertile : ∀ α, ∃ n p v, translateSet v (GS.G.dissect α).tiles ⊆ τ.supertile n p
  hereditary : τ.HereditarySides → GS.σ.HereditarySides
  grouped_disks_distinct : ∀ α β, (GS.G.dissect α).tiles.Nontrivial →
    (GS.G.dissect β).tiles.Nontrivial → GS.G.P'.disk α = GS.G.P'.disk β → α = β

/-! ### Helpers for `existsMacroCertificate_seed1_grouping` -/

/-- An open nonempty set covered by finitely many tile carriers meets the interior of one. -/
private lemma emcg_open_meets_interior {U : Set Pt} (hU : IsOpen U) (hne : U.Nonempty)
    {F : Set (PlacedTile P)} (hF : F.Finite) (hcov : U ⊆ ⋃ A ∈ F, A.carrier) :
    ∃ A ∈ F, (U ∩ interior A.carrier).Nonempty := by
  induction F, hF using Set.Finite.induction_on generalizing U with
  | empty => obtain ⟨x, hx⟩ := hne; simpa using hcov hx
  | @insert A0 F _ _ ih =>
    by_cases h : (U \ A0.carrier).Nonempty
    · have hclosed : IsClosed A0.carrier := by
        have : IsCompact A0.carrier := by
          simpa [PlacedTile.carrier] using (P.disk A0.form).compact.vadd A0.anchor
        exact this.isClosed
      obtain ⟨A, hA, hx⟩ := ih (hU.sdiff hclosed) h (by
        intro x hx
        have := hcov hx.1
        simp only [mem_insert_iff, iUnion_iUnion_eq_or_left, mem_union] at this
        rcases this with h1 | h1
        · exact absurd h1 hx.2
        · exact h1)
      exact ⟨A, mem_insert_of_mem _ hA, hx.mono (inter_subset_inter_left _ diff_subset)⟩
    · have hsub : U ⊆ A0.carrier := by
        intro x hx; by_contra hc; exact h ⟨x, hx, hc⟩
      refine ⟨A0, mem_insert _ _, ?_⟩
      rw [inter_eq_left.mpr (interior_maximal hsub hU)]
      exact hne

/-- Supports of two disjoint finite families of tiles of a set with disjoint interiors have
disjoint interiors. -/
private lemma emcg_disjoint_interior_support {S F₁ F₂ : Set (PlacedTile P)}
    (hS : DisjointInteriors S) (h₁ : F₁ ⊆ S) (h₂ : F₂ ⊆ S) (hf₁ : F₁.Finite) (hf₂ : F₂.Finite)
    (hd : Disjoint F₁ F₂) : Disjoint (interior (support F₁)) (interior (support F₂)) := by
  rw [Set.disjoint_iff]
  rintro x ⟨hx1, hx2⟩
  obtain ⟨A, hA, hUA⟩ := emcg_open_meets_interior (isOpen_interior.inter isOpen_interior)
    ⟨x, hx1, hx2⟩ hf₁ ((inter_subset_left).trans (interior_subset (s := support F₁)))
  obtain ⟨B, hB, hUB⟩ := emcg_open_meets_interior
    ((isOpen_interior.inter isOpen_interior).inter isOpen_interior) hUA hf₂
    ((inter_subset_left.trans inter_subset_right).trans (interior_subset (s := support F₂)))
  have hAB : A ≠ B := fun hAB => Set.disjoint_left.mp hd hA (hAB ▸ hB)
  obtain ⟨y, ⟨⟨_, hyA⟩, hyB⟩⟩ := hUB
  exact Set.disjoint_left.mp (hS (h₁ hA) (h₂ hB) hAB) hyA hyB

/-- The interior of the carrier of a placed tile is nonempty. -/
private lemma emcg_interior_carrier_nonempty (A : PlacedTile P) :
    (interior A.carrier).Nonempty := by
  rw [PlacedTile.carrier, interior_vadd]
  obtain ⟨x, hx⟩ := (P.disk A.form).interior_nonempty
  exact ⟨A.anchor +ᵥ x, Set.vadd_mem_vadd_set hx⟩

/-- Two disjoint finite families of tiles of a set with disjoint interiors, the first nonempty,
have different supports. -/
private lemma emcg_support_ne {S F₁ F₂ : Set (PlacedTile P)}
    (hS : DisjointInteriors S) (h₁ : F₁ ⊆ S) (h₂ : F₂ ⊆ S) (hf₁ : F₁.Finite) (hf₂ : F₂.Finite)
    (hd : Disjoint F₁ F₂) (hne : F₁.Nonempty) : support F₁ ≠ support F₂ := by
  intro heq
  have h := emcg_disjoint_interior_support hS h₁ h₂ hf₁ hf₂ hd
  obtain ⟨A, hA⟩ := hne
  obtain ⟨y, hy⟩ := emcg_interior_carrier_nonempty A
  have hsub : A.carrier ⊆ support F₁ := fun z hz => by
    simp only [support, mem_iUnion]
    exact ⟨A, hA, hz⟩
  have h1 : y ∈ interior (support F₁) := interior_mono hsub hy
  have h2 : y ∈ interior (support F₂) := heq ▸ h1
  exact Set.disjoint_left.mp h h1 h2

private lemma emcg_translateSet_zero (S : Set (PlacedTile P)) : translateSet 0 S = S := by
  ext A
  simp [translateSet, PlacedTile.translate]

private lemma emcg_mem_translateSet {v : Pt} {S : Set (PlacedTile P)} {A : PlacedTile P} :
    A ∈ translateSet v S ↔ ∃ B ∈ S, A = B.translate v := by
  simp only [translateSet, mem_image]
  exact ⟨fun ⟨B, hB, h⟩ => ⟨B, hB, h.symm⟩, fun ⟨B, hB, h⟩ => ⟨B, hB, h.symm⟩⟩

private lemma emcg_translate_carrier (A : PlacedTile P) (v : Pt) :
    (A.translate v).carrier = v +ᵥ A.carrier := by
  simp only [PlacedTile.carrier, PlacedTile.translate, vadd_vadd]
  rfl

private lemma emcg_translate_side (A : PlacedTile P) (v : Pt) (i : Fin (P.disk A.form).n) :
    (A.translate v).side i = v +ᵥ A.side i := by
  simp only [PlacedTile.side, PlacedTile.translate, vadd_vadd]
  rfl

private lemma emcg_translate_vertex (A : PlacedTile P) (v : Pt) (i : Fin (P.disk A.form).n) :
    (A.translate v).vertex i = v + A.vertex i := by
  simp only [PlacedTile.vertex, PlacedTile.translate, vadd_eq_add, add_assoc]

private lemma emcg_support_translateSet (v : Pt) (S : Set (PlacedTile P)) :
    support (translateSet v S) = v +ᵥ support S := by
  ext x
  simp only [support, translateSet, mem_iUnion, mem_image, exists_prop]
  constructor
  · rintro ⟨A, ⟨B, hB, rfl⟩, hx⟩
    rw [emcg_translate_carrier] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, by simp only [mem_iUnion, exists_prop]; exact ⟨B, hB, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    simp only [mem_iUnion, exists_prop] at hy
    obtain ⟨B, hB, hy⟩ := hy
    exact ⟨B.translate v, ⟨B, hB, rfl⟩, by rw [emcg_translate_carrier]; exact ⟨y, hy, rfl⟩⟩

private lemma emcg_decompose_translate (τ : Substitution P) (v : Pt)
    (S : Set (PlacedTile P)) :
    τ.decompose (translateSet v S) = translateSet (τ.θ • v) (τ.decompose S) := by
  ext A
  simp only [Substitution.decompose, Substitution.decomposeTile, translateSet,
    PlacedTile.translate, mem_iUnion, mem_image]
  constructor
  · rintro ⟨B, ⟨C, hC, rfl⟩, D, hD, rfl⟩
    refine ⟨D.translate (τ.θ • C.anchor), ⟨C, hC, D, hD, ?_⟩, ?_⟩
    · apply PlacedTile.ext
      · rfl
      · simp [PlacedTile.translate]
    · apply PlacedTile.ext
      · rfl
      · change τ.θ • v + (τ.θ • C.anchor + D.anchor) =
          τ.θ • (v + C.anchor) + D.anchor
        rw [smul_add]
        abel
  · rintro ⟨B, ⟨C, hC, D, hD, rfl⟩, rfl⟩
    refine ⟨C.translate v, ⟨C, hC, rfl⟩, D, hD, ?_⟩
    apply PlacedTile.ext
    · rfl
    · change τ.θ • (v + C.anchor) + D.anchor =
        τ.θ • v + (τ.θ • C.anchor + D.anchor)
      rw [smul_add]
      abel

private lemma emcg_decompose_iUnion (τ : Substitution P)
    {ι : Sort*} (S : ι → Set (PlacedTile P)) :
    τ.decompose (⋃ i, S i) = ⋃ i, τ.decompose (S i) := by
  ext A
  simp only [Substitution.decompose, mem_iUnion]
  constructor
  · rintro ⟨B, ⟨i, hB⟩, hA⟩
    exact ⟨i, B, hB, hA⟩
  · rintro ⟨i, B, hB, hA⟩
    exact ⟨B, ⟨i, hB⟩, hA⟩

private lemma emcg_iter_iUnion (τ : Substitution P) (n : ℕ)
    {ι : Sort*} (S : ι → Set (PlacedTile P)) :
    τ.decomposeIter n (⋃ i, S i) = ⋃ i, τ.decomposeIter n (S i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change τ.decompose (τ.decomposeIter n (⋃ i, S i)) = _
      rw [ih, emcg_decompose_iUnion]
      rfl

private lemma emcg_iter_translate (τ : Substitution P) (n : ℕ)
    (v : Pt) (S : Set (PlacedTile P)) :
    τ.decomposeIter n (translateSet v S) =
      translateSet ((τ.θ ^ n) • v) (τ.decomposeIter n S) := by
  induction n with
  | zero => simp [Substitution.decomposeIter]
  | succ n ih =>
      change τ.decompose (τ.decomposeIter n (translateSet v S)) = _
      rw [ih, emcg_decompose_translate]
      congr 1
      rw [pow_succ', mul_smul]

private lemma emcg_iter_biUnion (τ : Substitution P) (n : ℕ) (S : Set (PlacedTile P)) :
    τ.decomposeIter n S = ⋃ T ∈ S, τ.decomposeIter n {T} := by
  conv_lhs => rw [show S = ⋃ T ∈ S, ({T} : Set (PlacedTile P)) by ext; simp]
  rw [emcg_iter_iUnion]
  apply iUnion_congr
  intro T
  rw [emcg_iter_iUnion]

private lemma emcg_iter_singleton (τ : Substitution P) (n : ℕ) (T : PlacedTile P) :
    τ.decomposeIter n {T} = translateSet ((τ.θ ^ n) • T.anchor) (τ.supertile n T.form) := by
  rw [show ({T} : Set (PlacedTile P)) = translateSet T.anchor {⟨T.form, 0⟩} by
    ext B; simp [translateSet, PlacedTile.translate, PlacedTile.ext_iff]]
  rw [emcg_iter_translate]
  rfl

private lemma emcg_iter_mono (τ : Substitution P) (n : ℕ) {S S' : Set (PlacedTile P)}
    (h : S ⊆ S') : τ.decomposeIter n S ⊆ τ.decomposeIter n S' := by
  rw [emcg_iter_biUnion τ n S, emcg_iter_biUnion τ n S']
  exact biUnion_subset_biUnion_left h

private lemma emcg_iter_add (τ : Substitution P) (m n : ℕ) (S : Set (PlacedTile P)) :
    τ.decomposeIter n (τ.decomposeIter m S) = τ.decomposeIter (m + n) S := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change τ.decompose (τ.decomposeIter n (τ.decomposeIter m S)) =
        τ.decompose (τ.decomposeIter (m + n) S)
      rw [ih]

private lemma emcg_smul_vadd_set (c : ℝ) (a : Pt) (s : Set Pt) :
    c • (a +ᵥ s) = (c • a) +ᵥ c • s := by
  ext x
  simp only [mem_smul_set, mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨c • z, ⟨z, hz, rfl⟩, by rw [smul_add]⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨a + z, ⟨z, hz, rfl⟩, by rw [smul_add]⟩

/-- One step of hereditary sides for a placed tile. -/
private lemma emcg_hered_side_one (τ : Substitution P) (hH : τ.HereditarySides)
    (T : PlacedTile P) (i : Fin (P.disk T.form).n) {x : Pt} (hx : x ∈ τ.θ • T.side i) :
    ∃ F ∈ τ.decomposeTile T, ∃ j, F.side j ⊆ τ.θ • T.side i ∧ x ∈ F.side j := by
  have h2 := hH.2 T.form i
  have hside : τ.θ • T.side i = (τ.θ • T.anchor) +ᵥ τ.θ • (P.disk T.form).side i := by
    rw [PlacedTile.side, emcg_smul_vadd_set]
  rw [hside] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  rw [h2] at hy
  simp only [mem_iUnion, exists_prop] at hy
  obtain ⟨A, hA, j, hj, hyj⟩ := hy
  refine ⟨A.translate (τ.θ • T.anchor), ⟨A, hA, rfl⟩, j, ?_, ?_⟩
  · rw [emcg_translate_side]
    exact vadd_set_mono hj
  · rw [emcg_translate_side]
    exact vadd_mem_vadd_set hyj

/-- Hereditary sides for the `n`-th decomposition of a placed tile. -/
private lemma emcg_hered_side_iter (τ : Substitution P) (hH : τ.HereditarySides) (n : ℕ)
    (T : PlacedTile P) (i : Fin (P.disk T.form).n) {x : Pt} (hx : x ∈ (τ.θ ^ n) • T.side i) :
    ∃ F ∈ τ.decomposeIter n {T}, ∃ j, F.side j ⊆ (τ.θ ^ n) • T.side i ∧ x ∈ F.side j := by
  induction n generalizing x with
  | zero =>
    refine ⟨T, rfl, i, by simp, by simpa using hx⟩
  | succ n ih =>
    rw [pow_succ', mul_smul] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨F, hF, j, hj, hyj⟩ := ih hy
    obtain ⟨F', hF', j', hj', hxj'⟩ := emcg_hered_side_one τ hH F j (smul_mem_smul_set hyj)
    refine ⟨F', ?_, j', hj'.trans (smul_set_mono hj), hxj'⟩
    change F' ∈ τ.decompose (τ.decomposeIter n {T})
    simp only [Substitution.decompose, mem_iUnion]
    exact ⟨F, hF, hF'⟩

/-- One step of hereditary vertices for a placed tile. -/
private lemma emcg_hered_vertex_one (τ : Substitution P) (hH : τ.HereditarySides)
    (T : PlacedTile P) (i : Fin (P.disk T.form).n) :
    ∃ F ∈ τ.decomposeTile T, τ.θ • T.vertex i ∈ F.vertexSet := by
  obtain ⟨A, hA, j, hj⟩ := hH.1 T.form i
  refine ⟨A.translate (τ.θ • T.anchor), ⟨A, hA, rfl⟩, j, ?_⟩
  rw [emcg_translate_vertex, hj, PlacedTile.vertex, vadd_eq_add, smul_add]

/-- Hereditary vertices for the `n`-th decomposition of a placed tile. -/
private lemma emcg_hered_vertex_iter (τ : Substitution P) (hH : τ.HereditarySides) (n : ℕ)
    (T : PlacedTile P) (i : Fin (P.disk T.form).n) :
    ∃ F ∈ τ.decomposeIter n {T}, (τ.θ ^ n) • T.vertex i ∈ F.vertexSet := by
  induction n with
  | zero => exact ⟨T, rfl, i, by simp⟩
  | succ n ih =>
    obtain ⟨F, hF, j, hj⟩ := ih
    obtain ⟨F', hF', hv⟩ := emcg_hered_vertex_one τ hH F j
    refine ⟨F', ?_, ?_⟩
    · change F' ∈ τ.decompose (τ.decomposeIter n {T})
      simp only [Substitution.decompose, mem_iUnion]
      exact ⟨F, hF, hF'⟩
    · rw [pow_succ', mul_smul, ← hj]
      exact hv

private lemma emcg_b_iterate_support_decomposeTile (τ : Substitution P) (A : PlacedTile P) :
    support (τ.decomposeTile A) = τ.θ • A.carrier := by
  dsimp [Substitution.decomposeTile]
  rw [emcg_support_translateSet, τ.support_eq, PlacedTile.carrier]
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, hx⟩
    refine ⟨A.anchor + y, ?_, ?_⟩
    · simpa
    · rw [smul_add]
      calc τ.θ • A.anchor + τ.θ • y = τ.θ • A.anchor + (-(τ.θ • A.anchor) + x) := by congr 1
        _ = x := by abel
  · rintro ⟨y, hy, rfl⟩
    refine ⟨-A.anchor + y, ?_, ?_⟩
    · simpa
    · simp [smul_add]

private lemma emcg_b_iterate_support_decompose (τ : Substitution P) (S : Set (PlacedTile P)) :
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
    rw [emcg_b_iterate_support_decomposeTile τ] at h
    exact h
  · rintro ⟨A, hA, hx⟩
    have h : x ∈ support (τ.decomposeTile A) := by
      rw [emcg_b_iterate_support_decomposeTile τ]
      exact hx
    simp only [support, Set.mem_iUnion] at h
    rcases h with ⟨B, hB, hx'⟩
    exact ⟨B, ⟨A, hA, hB⟩, hx'⟩

private lemma emcg_b_disjoint_translate {v : Pt} {S : Set (PlacedTile P)}
    (h : DisjointInteriors S) : DisjointInteriors (translateSet v S) := by
  intro A hA B hB hne
  dsimp [translateSet] at hA hB
  rcases hA with ⟨A', hA', rfl⟩
  rcases hB with ⟨B', hB', rfl⟩
  have hne' : A' ≠ B' := by
    intro hc
    apply hne
    rw [hc]
  have hd := h hA' hB' hne'
  have heq1 : (A'.translate v).carrier = v +ᵥ A'.carrier := by
    ext x
    simp only [PlacedTile.carrier, PlacedTile.translate, mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_rev]
    rw [← add_assoc]
  have heq2 : (B'.translate v).carrier = v +ᵥ B'.carrier := by
    ext x
    simp only [PlacedTile.carrier, PlacedTile.translate, mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_rev]
    rw [← add_assoc]
  dsimp [Function.onFun] at hd ⊢
  rw [heq1, heq2, interior_vadd, interior_vadd]
  exact (disjoint_image_iff (add_right_injective v)).mpr hd

private lemma emcg_b_disjoint_decompose (τ : Substitution P) (S : Set (PlacedTile P))
    (hS : DisjointInteriors S) : DisjointInteriors (τ.decompose S) := by
  have hθ : τ.θ ≠ 0 := (zero_lt_one.trans τ.one_lt).ne'
  have key : ∀ {X X' : PlacedTile P}, X ∈ τ.decomposeTile X' →
      interior X.carrier ⊆ τ.θ • interior X'.carrier := by
    intro X X' hX
    rw [← interior_smul₀ hθ]
    refine interior_mono ?_
    rw [← emcg_b_iterate_support_decomposeTile τ]
    exact Set.subset_biUnion_of_mem hX
  intro A hA B hB hne
  simp only [Substitution.decompose, Set.mem_iUnion, exists_prop] at hA hB
  obtain ⟨A', hA', hAmem⟩ := hA
  obtain ⟨B', hB', hBmem⟩ := hB
  dsimp [Function.onFun]
  by_cases hAB : A' = B'
  · subst hAB
    have h_rule_disj := (τ.rule A'.form).disjoint
    have h_trans_disj := emcg_b_disjoint_translate h_rule_disj
      (v := τ.θ • A'.anchor)
    change DisjointInteriors (τ.decomposeTile A') at h_trans_disj
    exact h_trans_disj hAmem hBmem hne
  · have hd : Disjoint (interior A'.carrier) (interior B'.carrier) :=
      hS hA' hB' hAB
    have hd' : Disjoint (τ.θ • interior A'.carrier) (τ.θ • interior B'.carrier) :=
      (disjoint_image_iff (smul_right_injective _ hθ)).mpr hd
    exact hd'.mono (key hAmem) (key hBmem)


private lemma emcg_iter_support (τ : Substitution P) (n : ℕ) (S : Set (PlacedTile P)) :
    support (τ.decomposeIter n S) = (τ.θ ^ n) • support S := by
  induction n with
  | zero => simp [Substitution.decomposeIter]
  | succ n ih =>
    change support (τ.decompose (τ.decomposeIter n S)) = _
    rw [emcg_b_iterate_support_decompose, ih, smul_smul, pow_succ']

private lemma emcg_iter_disjoint (τ : Substitution P) (n : ℕ) {S : Set (PlacedTile P)}
    (hS : DisjointInteriors S) : DisjointInteriors (τ.decomposeIter n S) := by
  induction n with
  | zero => exact hS
  | succ n ih => exact emcg_b_disjoint_decompose τ _ ih

private lemma emcg_segment_infinite {a b : Pt} (hab : a ≠ b) : (segment ℝ a b).Infinite := by
  rw [segment_eq_image_lineMap]
  refine Set.Infinite.image ?_ (Set.Icc_infinite zero_lt_one)
  exact (AffineMap.lineMap_injective ℝ hab).injOn

private lemma emcg_inter_subsingleton {s e : Set Pt} (hs : Convex ℝ s) (he : Convex ℝ e)
    (h : ¬ OverlapPos s e) : (s ∩ e).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  exact h ⟨x, y, hxy, (hs.inter he).segment_subset hx hy⟩

private lemma emcg_exists_overlap {ι : Type*} [Finite ι] (s : ι → Set Pt)
    (hs : ∀ i, Convex ℝ (s i)) {a b : Pt} (hab : a ≠ b) (hcov : segment ℝ a b ⊆ ⋃ i, s i) :
    ∃ i, OverlapPos (s i) (segment ℝ a b) := by
  by_contra hno
  push_neg at hno
  have hfin : (segment ℝ a b).Finite := by
    have : segment ℝ a b ⊆ ⋃ i, (s i ∩ segment ℝ a b) := by
      intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
      exact mem_iUnion.mpr ⟨i, hi, hx⟩
    refine Set.Finite.subset (Set.finite_iUnion fun i => ?_) this
    exact (emcg_inter_subsingleton (hs i) (convex_segment a b) (hno i)).finite
  exact emcg_segment_infinite hab hfin

private lemma emcg_finRotate_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have h1 : (1 : Fin (m + 1)) = 0 := by
    have := congrArg (fun x => x - i) h
    simpa using this
  have : NeZero (m + 1) := ⟨by omega⟩
  rw [Fin.one_eq_zero_iff] at h1
  omega

private lemma emcg_side_eq_segment (A : PlacedTile P) (i : Fin (P.disk A.form).n) :
    A.side i = segment ℝ (A.vertex i) (A.vertex (finRotate _ i)) := by
  simp only [PlacedTile.side, PlacedTile.vertex, PolygonalDisk.side]
  exact vadd_segment ℝ _ _ _

private lemma emcg_vertex_ne (A : PlacedTile P) (i : Fin (P.disk A.form).n) :
    A.vertex i ≠ A.vertex (finRotate _ i) := by
  intro h
  simp only [PlacedTile.vertex, vadd_eq_add, add_right_inj] at h
  exact emcg_finRotate_ne (by have := (P.disk A.form).three_le; omega) i
    ((P.disk A.form).vertex_injective h).symm

private lemma emcg_segment_endpoints {a b c d : Pt} (h : segment ℝ a b = segment ℝ c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases hab : a = b
  · subst hab
    rw [segment_same] at h
    have hc : c ∈ ({a} : Set Pt) := h ▸ left_mem_segment ℝ c d
    have hd : d ∈ ({a} : Set Pt) := h ▸ right_mem_segment ℝ c d
    rw [Set.mem_singleton_iff] at hc hd
    exact Or.inl ⟨hc.symm, hd.symm⟩
  · have hc : c ∈ segment ℝ a b := h ▸ left_mem_segment ℝ c d
    have hd : d ∈ segment ℝ a b := h ▸ right_mem_segment ℝ c d
    have ha : a ∈ segment ℝ c d := h ▸ left_mem_segment ℝ a b
    have hb : b ∈ segment ℝ c d := h ▸ right_mem_segment ℝ a b
    rw [segment_eq_image'] at hc hd ha hb
    obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hc
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hd
    obtain ⟨u, ⟨hu0, hu1⟩, hu⟩ := ha
    obtain ⟨w, ⟨hw0, hw1⟩, hw⟩ := hb
    simp only at hu hw
    have hv : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    have e1 : (s + u * (t - s)) • (b - a) = 0 := by
      have h' : a + s • (b - a) + u • (a + t • (b - a) -
          (a + s • (b - a))) - a = (s + u * (t - s)) • (b - a) := by
        module
      rw [← h', hu, sub_self]
    have e2 : (s + w * (t - s) - 1) • (b - a) = 0 := by
      have h' : a + s • (b - a) + w • (a + t • (b - a) -
          (a + s • (b - a))) - b = (s + w * (t - s) - 1) • (b - a) := by
        module
      rw [← h', hw, sub_self]
    have f1 := (smul_eq_zero.1 e1).resolve_right hv
    have f2 := (smul_eq_zero.1 e2).resolve_right hv
    rcases lt_trichotomy s t with hst | hst | hst
    · have hs : s = 0 := by nlinarith
      subst hs
      have ht : t = 1 := by nlinarith
      subst ht
      left; constructor <;> simp
    · subst hst; simp at f1 f2; linarith
    · have ht : t = 0 := by nlinarith
      subst ht
      have hs : s = 1 := by nlinarith
      subst hs
      right; constructor <;> simp

private lemma emcg_tile_closed {Q : Protoset} (A : PlacedTile Q) : IsClosed A.carrier := by
  have : IsCompact A.carrier := by
    simpa [PlacedTile.carrier] using (Q.disk A.form).compact.vadd A.anchor
  exact this.isClosed

private lemma emcg_disk_side_subset_frontier (D : PolygonalDisk) (i : Fin D.n) :
    D.side i ⊆ frontier D.carrier := by
  rw [D.frontier_eq]
  exact subset_iUnion (fun i => segment ℝ (D.vertex i) (D.vertex (finRotate D.n i))) i

private lemma emcg_carrier_subset_support {Q : Protoset} {S : Set (PlacedTile Q)}
    {A : PlacedTile Q} (hA : A ∈ S) : A.carrier ⊆ support S := fun z hz => by
  simp only [support, mem_iUnion]
  exact ⟨A, hA, hz⟩

private lemma emcg_side_subset_carrier {Q : Protoset} (A : PlacedTile Q)
    (i : Fin (Q.disk A.form).n) : A.side i ⊆ A.carrier := by
  simp only [PlacedTile.side, PlacedTile.carrier]
  refine vadd_set_mono ?_
  refine (emcg_disk_side_subset_frontier _ i).trans ?_
  rw [((Q.disk A.form).compact.isClosed).frontier_eq]
  exact diff_subset

private lemma emcg_grouped_carrier (G : GroupedFamily P) (X : PlacedTile G.P') :
    X.carrier = support (G.scatterTile X) := by
  rw [GroupedFamily.scatterTile, emcg_support_translateSet, G.support_eq]
  rfl

/-- A point of a scaled side of a grouped form lying in a child of the grouped substitution lies
on the frontier of that child. -/
private lemma emcg_not_mem_interior_child {τ : Substitution P} (GS : GroupedSubstitution τ)
    (α : GS.G.P'.Form) (i : Fin (GS.G.P'.disk α).n) {X : PlacedTile GS.G.P'}
    (hX : X ∈ (GS.σ.rule α).tiles) {y : Pt} (hy : y ∈ (τ.θ ^ GS.k) • (GS.G.P'.disk α).side i) :
    y ∉ interior X.carrier := by
  intro hint
  have hθ : τ.θ ^ GS.k ≠ 0 := (pow_pos (zero_lt_one.trans τ.one_lt) _).ne'
  have hsub : X.carrier ⊆ (τ.θ ^ GS.k) • (GS.G.P'.disk α).carrier := by
    rw [← GS.θ_eq, ← GS.σ.support_eq α]
    exact emcg_carrier_subset_support hX
  have h1 := interior_mono hsub hint
  rw [interior_smul₀ hθ] at h1
  obtain ⟨z, hz, rfl⟩ := hy
  rw [smul_mem_smul_set_iff₀ hθ] at h1
  have hzf := emcg_disk_side_subset_frontier _ i hz
  rw [((GS.G.P'.disk α).compact.isClosed).frontier_eq] at hzf
  exact hzf.2 h1

/-- Fine tiles of the decomposition of a grouped form are constituents of children. -/
private lemma emcg_fine_tile_in_child {τ : Substitution P} (GS : GroupedSubstitution τ)
    (α : GS.G.P'.Form) {F : PlacedTile P}
    (hF : F ∈ τ.decomposeIter GS.k (GS.G.dissect α).tiles) :
    ∃ X ∈ (GS.σ.rule α).tiles, F ∈ GS.G.scatterTile X := by
  rw [← GS.compat α] at hF
  simp only [GroupedFamily.scatter, mem_iUnion] at hF
  obtain ⟨X, hX, hF⟩ := hF
  exact ⟨X, hX, hF⟩

private lemma emcg_scatterTile_subset {τ : Substitution P} (GS : GroupedSubstitution τ)
    (α : GS.G.P'.Form) {X : PlacedTile GS.G.P'} (hX : X ∈ (GS.σ.rule α).tiles) :
    GS.G.scatterTile X ⊆ τ.decomposeIter GS.k (GS.G.dissect α).tiles := by
  rw [← GS.compat α]
  intro F hF
  simp only [GroupedFamily.scatter, mem_iUnion]
  exact ⟨X, hX, hF⟩

/-- A point on the frontier of a placed tile lies on one of its listed sides. -/
private lemma emcg_mem_side_of_not_interior {Q : Protoset} (X : PlacedTile Q) {y : Pt}
    (hy : y ∈ X.carrier) (hyi : y ∉ interior X.carrier) :
    ∃ l, y ∈ X.side l := by
  simp only [PlacedTile.carrier, PlacedTile.side] at hy hyi ⊢
  rw [interior_vadd] at hyi
  obtain ⟨z, hz, rfl⟩ := hy
  have hzi : z ∉ interior (Q.disk X.form).carrier := fun h => hyi (vadd_mem_vadd_set h)
  have hzf : z ∈ frontier (Q.disk X.form).carrier := by
    rw [((Q.disk X.form).compact.isClosed).frontier_eq]
    exact ⟨hz, hzi⟩
  rw [(Q.disk X.form).frontier_eq] at hzf
  obtain ⟨l, hl⟩ := mem_iUnion.mp hzf
  exact ⟨l, vadd_mem_vadd_set hl⟩

/-- `lem:certificate-exists`, heredity: a grouped substitution whose decompositions are STS
inherits hereditary listed sides from `τ`. -/
private lemma emcg_grouped_hereditary {τ : Substitution P} (GS : GroupedSubstitution τ)
    (hH : τ.HereditarySides)
    (hsts : ∀ α, SideToSideSet (τ.decomposeIter GS.k (GS.G.dissect α).tiles)) :
    GS.σ.HereditarySides := by
  constructor
  · intro α i
    rw [GS.θ_eq]
    obtain ⟨T, hT, j, hj⟩ := GS.G.side_whole α i
    have hT' : τ.decomposeIter GS.k {T} ⊆ τ.decomposeIter GS.k (GS.G.dissect α).tiles :=
      emcg_iter_mono τ _ (singleton_subset_iff.mpr hT)
    have hv : ∃ j', T.vertex j' = (GS.G.P'.disk α).vertex i := by
      have h := hj
      rw [emcg_side_eq_segment, PolygonalDisk.side] at h
      rcases emcg_segment_endpoints h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact ⟨j, h1⟩
      · exact ⟨_, h2⟩
    obtain ⟨j', hj'⟩ := hv
    obtain ⟨F, hF, m, hm⟩ := emcg_hered_vertex_iter τ hH GS.k T j'
    obtain ⟨X, hX, hFX⟩ := emcg_fine_tile_in_child GS α (hT' hF)
    rw [GroupedFamily.scatterTile, emcg_mem_translateSet] at hFX
    obtain ⟨F0, hF0, rfl⟩ := hFX
    rw [hj'] at hm
    have hyX : (τ.θ ^ GS.k) • (GS.G.P'.disk α).vertex i ∈ X.carrier := by
      rw [emcg_grouped_carrier]
      refine emcg_carrier_subset_support (A := F0.translate X.anchor) ?_ ?_
      · rw [GroupedFamily.scatterTile, emcg_mem_translateSet]; exact ⟨F0, hF0, rfl⟩
      · rw [← hm]
        exact emcg_side_subset_carrier _ m (by
          rw [emcg_side_eq_segment]; exact left_mem_segment ℝ _ _)
    have hyi := emcg_not_mem_interior_child GS α i hX (y := (τ.θ ^ GS.k) •
      (GS.G.P'.disk α).vertex i) (smul_mem_smul_set (by
        rw [PolygonalDisk.side]; exact left_mem_segment ℝ _ _))
    -- the vertex lies on the frontier of the grouped disk of `X`
    have hfr : F0.vertex m ∈ frontier (GS.G.P'.disk X.form).carrier := by
      rw [((GS.G.P'.disk X.form).compact.isClosed).frontier_eq]
      have hm' : (τ.θ ^ GS.k) • (GS.G.P'.disk α).vertex i = X.anchor +ᵥ F0.vertex m := by
        rw [← hm, emcg_translate_vertex]; rfl
      rw [hm'] at hyX hyi
      simp only [PlacedTile.carrier] at hyX hyi
      rw [interior_vadd] at hyi
      exact ⟨(vadd_mem_vadd_set_iff).mp hyX, fun h => hyi (vadd_mem_vadd_set h)⟩
    obtain ⟨m', hm'⟩ := GS.G.vertex_retained X.form (F0.vertex m) ⟨F0, hF0, m, rfl⟩ hfr
    refine ⟨X, hX, m', ?_⟩
    rw [PlacedTile.vertex, hm', ← hm, emcg_translate_vertex]
    rfl
  · intro α i
    rw [GS.θ_eq]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨T, hT, j, hj⟩ := GS.G.side_whole α i
      have hT' : τ.decomposeIter GS.k {T} ⊆ τ.decomposeIter GS.k (GS.G.dissect α).tiles :=
        emcg_iter_mono τ _ (singleton_subset_iff.mpr hT)
      rw [← hj] at hx
      obtain ⟨F, hF, m, hmsub, hxm⟩ := emcg_hered_side_iter τ hH GS.k T j hx
      rw [hj] at hmsub
      obtain ⟨X, hX, hFX⟩ := emcg_fine_tile_in_child GS α (hT' hF)
      have hFX' := hFX
      rw [GroupedFamily.scatterTile, emcg_mem_translateSet] at hFX'
      obtain ⟨F0, hF0, hFeq⟩ := hFX'
      -- the fine side lies on the frontier of `X`
      have hcov : F.side m ⊆ ⋃ l, X.side l := by
        intro y hy
        have hyX : y ∈ X.carrier := by
          rw [emcg_grouped_carrier]
          exact emcg_carrier_subset_support hFX (emcg_side_subset_carrier F m hy)
        have hyi := emcg_not_mem_interior_child GS α i hX (hmsub hy)
        obtain ⟨l, hl⟩ := emcg_mem_side_of_not_interior X hyX hyi
        exact mem_iUnion.mpr ⟨l, hl⟩
      rw [emcg_side_eq_segment] at hcov
      obtain ⟨l, hl⟩ := emcg_exists_overlap (fun l => X.side l)
        (fun l => by show Convex ℝ (X.side l); rw [emcg_side_eq_segment]; exact convex_segment _ _)
        (emcg_vertex_ne F m) hcov
      rw [← emcg_side_eq_segment] at hl
      obtain ⟨B0, hB0, q, hq⟩ := GS.G.side_whole X.form l
      have hB : B0.translate X.anchor ∈ τ.decomposeIter GS.k (GS.G.dissect α).tiles :=
        emcg_scatterTile_subset GS α hX (by
          rw [GroupedFamily.scatterTile, emcg_mem_translateSet]; exact ⟨B0, hB0, rfl⟩)
      have hBside : (B0.translate X.anchor).side q = X.side l := by
        rw [emcg_translate_side, hq]; rfl
      have heq := hsts α _ hB _ (hT' hF) q m (by rw [hBside]; exact hl)
      rw [hBside] at heq
      simp only [mem_iUnion, exists_prop]
      exact ⟨X, hX, l, heq ▸ hmsub, heq ▸ hxm⟩
    · simp only [iUnion_subset_iff]
      intro X _ l hl
      exact hl

section GroupingConstruction

variable (τ : Substitution P) (k : ℕ) {M : MeshConstants P} {N : ℕ} {R : ℝ}
  {c : P.Form → Pt} (A : ∀ p, AnnularGrouping M (τ.supertile k p) (c p) N R)

private lemma emcg_disjoint_of_subset {S T : Set (PlacedTile P)} (hS : DisjointInteriors S)
    (h : T ⊆ S) : DisjointInteriors T := Set.PairwiseDisjoint.subset hS h

private lemma emcg_iter_finite (n : ℕ) {S : Set (PlacedTile P)} (hS : S.Finite) :
    (τ.decomposeIter n S).Finite := by
  induction n with
  | zero => exact hS
  | succ n ih =>
    change (τ.decompose (τ.decomposeIter n S)).Finite
    exact ih.biUnion fun T _ => (τ.rule T.form).finite.image _

private lemma emcg_supertile_disjoint (q : P.Form) : DisjointInteriors (τ.supertile k q) := by
  refine emcg_iter_disjoint τ k ?_
  intro X hX Y hY hXY
  rw [mem_singleton_iff] at hX hY
  exact absurd (hX.trans hY.symm) hXY

private lemma emcg_supertile_finite (q : P.Form) : (τ.supertile k q).Finite :=
  emcg_iter_finite τ k (finite_singleton _)

/-- The grouped protoset. -/
private def emcgP' : Protoset where
  Form := P.Form ⊕ (P.Form × Fin (4 * N)) ⊕ P.Form
  disk := Sum.elim (fun p => pdOrientCCW (A p).L.disk)
    (Sum.elim (fun pj => pdOrientCCW ((A pj.1).spokes.piece pj.2).disk)
      (fun p => pdOrientCCW (P.disk p)))

/-- The scattering patches. -/
private def emcgDissect : (emcgP' τ k A).Form → Patch P :=
  Sum.elim (fun p => ⟨(A p).L.faces, (A p).L.finite,
      emcg_disjoint_of_subset (emcg_supertile_disjoint τ k p) (A p).L.faces_sub⟩)
    (Sum.elim (fun pj => ⟨((A pj.1).spokes.piece pj.2).faces, ((A pj.1).spokes.piece pj.2).finite,
      emcg_disjoint_of_subset (emcg_supertile_disjoint τ k pj.1)
        ((A pj.1).spokes.piece pj.2).faces_sub⟩)
      (fun p => ⟨{⟨p, 0⟩}, finite_singleton _, by
        intro X hX Y hY hXY
        rw [mem_singleton_iff] at hX hY
        exact absurd (hX.trans hY.symm) hXY⟩))

private lemma emcg_sts_subset {S T : Set (PlacedTile P)} (hS : SideToSideSet S) (h : T ⊆ S) :
    SideToSideSet T := fun A hA B hB => hS A (h hA) B (h hB)

private lemma emcg_isVertexOf_mono {S T : Set (PlacedTile P)} (h : T ⊆ S) {v : Pt}
    (hv : Substitution.IsVertexOf T v) : Substitution.IsVertexOf S v := by
  obtain ⟨B, hB, hv⟩ := hv
  exact ⟨B, h hB, hv⟩

private lemma emcg_support_singleton_zero (p : P.Form) :
    support ({⟨p, 0⟩} : Set (PlacedTile P)) = (P.disk p).carrier := by
  simp [support, PlacedTile.carrier]

/-- The grouped family: the large groups, the annular pieces and the original singletons. -/
private def emcgG (h : τ.STS) : GroupedFamily P where
  P' := emcgP' τ k A
  dissect := emcgDissect τ k A
  support_eq := by
    rintro (p | ⟨p, j⟩ | p)
    · change support (A p).L.faces = (pdOrientCCW (A p).L.disk).carrier
      rw [pdOrientCCW_carrier]
      exact (A p).L.carrier_eq.symm
    · change support ((A p).spokes.piece j).faces =
        (pdOrientCCW ((A p).spokes.piece j).disk).carrier
      rw [pdOrientCCW_carrier]
      exact ((A p).spokes.piece j).carrier_eq.symm
    · change support ({⟨p, 0⟩} : Set (PlacedTile P)) = (pdOrientCCW (P.disk p)).carrier
      rw [pdOrientCCW_carrier]
      exact emcg_support_singleton_zero p
  sts := by
    rintro (p | ⟨p, j⟩ | p)
    · exact emcg_sts_subset (h k p) (A p).L.faces_sub
    · exact emcg_sts_subset (h k p) ((A p).spokes.piece j).faces_sub
    · exact h 0 p
  dualConnected := by
    rintro (p | ⟨p, j⟩ | p)
    · exact (A p).L.dualConnected
    · exact ((A p).spokes.piece j).dualConnected
    · intro X hX Y hY
      change X ∈ ({⟨p, 0⟩} : Set (PlacedTile P)) at hX
      change Y ∈ ({⟨p, 0⟩} : Set (PlacedTile P)) at hY
      rw [mem_singleton_iff] at hX hY
      rw [hX, hY]
  side_whole := by
    rintro (p | ⟨p, j⟩ | p) i
    · obtain ⟨i', hi'⟩ := pdOrientCCW_side (A p).L.disk i
      obtain ⟨B, hB, k, hk⟩ := (A p).L.side_whole i'
      exact ⟨B, hB, k, hk.trans hi'.symm⟩
    · obtain ⟨i', hi'⟩ := pdOrientCCW_side ((A p).spokes.piece j).disk i
      obtain ⟨B, hB, k, hk⟩ := ((A p).spokes.piece j).side_whole i'
      exact ⟨B, hB, k, hk.trans hi'.symm⟩
    · obtain ⟨i', hi'⟩ := pdOrientCCW_side (P.disk p) i
      exact ⟨⟨p, 0⟩, mem_singleton _, i', by simpa [PlacedTile.side] using hi'.symm⟩
  vertex_retained := by
    rintro (p | ⟨p, j⟩ | p) v hv hfr
    · change v ∈ frontier (pdOrientCCW (A p).L.disk).carrier at hfr
      change v ∈ (pdOrientCCW (A p).L.disk).vertexSet
      rw [pdOrientCCW_vertexSet]
      exact (A p).L.vertex_retained v (emcg_isVertexOf_mono (A p).L.faces_sub hv)
        (by simpa [pdOrientCCW_carrier] using hfr)
    · change v ∈ frontier (pdOrientCCW ((A p).spokes.piece j).disk).carrier at hfr
      change v ∈ (pdOrientCCW ((A p).spokes.piece j).disk).vertexSet
      rw [pdOrientCCW_vertexSet]
      exact ((A p).spokes.piece j).vertex_retained v
        (emcg_isVertexOf_mono ((A p).spokes.piece j).faces_sub hv)
        (by simpa [pdOrientCCW_carrier] using hfr)
    · obtain ⟨B, hB, l, hl⟩ := hv
      change B ∈ ({⟨p, 0⟩} : Set (PlacedTile P)) at hB
      rw [mem_singleton_iff] at hB
      subst hB
      change v ∈ (pdOrientCCW (P.disk p)).vertexSet
      rw [pdOrientCCW_vertexSet]
      exact ⟨l, by rw [← hl]; simp [PlacedTile.vertex]⟩

end GroupingConstruction

private lemma emcg_translateSet_translateSet {Q : Protoset} (v w : Pt) (S : Set (PlacedTile Q)) :
    translateSet v (translateSet w S) = translateSet (v + w) S := by
  ext X
  simp only [translateSet, mem_image]
  constructor
  · rintro ⟨Y, ⟨Z, hZ, rfl⟩, rfl⟩
    exact ⟨Z, hZ, by simp [PlacedTile.translate, add_assoc]⟩
  · rintro ⟨Z, hZ, rfl⟩
    exact ⟨Z.translate w, ⟨Z, hZ, rfl⟩, by simp [PlacedTile.translate, add_assoc]⟩

private lemma emcg_translateSet_iUnion {Q : Protoset} (v : Pt) {ι : Sort*}
    (S : ι → Set (PlacedTile Q)) : translateSet v (⋃ i, S i) = ⋃ i, translateSet v (S i) := by
  simp only [translateSet, image_iUnion]

private lemma emcg_translate_injective {Q : Protoset} (v : Pt) :
    Function.Injective (fun X : PlacedTile Q => X.translate v) := by
  intro X Y h
  simp only [PlacedTile.translate, PlacedTile.mk.injEq] at h
  exact PlacedTile.ext h.1 (by simpa using h.2)

private lemma emcg_translateSet_disjoint {Q : Protoset} (v : Pt) {S T : Set (PlacedTile Q)}
    (h : Disjoint S T) : Disjoint (translateSet v S) (translateSet v T) :=
  (disjoint_image_iff (emcg_translate_injective v)).mpr h

private lemma emcg_scatterTile_translate (G : GroupedFamily P) (X : PlacedTile G.P') (v : Pt) :
    G.scatterTile (X.translate v) = translateSet v (G.scatterTile X) := by
  simp only [GroupedFamily.scatterTile, emcg_translateSet_translateSet]
  rfl

private lemma emcg_scatter_translateSet (G : GroupedFamily P) (v : Pt)
    (S : Set (PlacedTile G.P')) : G.scatter (translateSet v S) = translateSet v (G.scatter S) := by
  simp only [GroupedFamily.scatter, translateSet, biUnion_image, image_iUnion]
  apply iUnion_congr; intro X; apply iUnion_congr; intro _
  exact emcg_scatterTile_translate G X v

private lemma emcg_support_biUnion {Q : Protoset} {ι : Type*} (s : Set ι)
    (f : ι → Set (PlacedTile Q)) : support (⋃ i ∈ s, f i) = ⋃ i ∈ s, support (f i) := by
  ext x
  simp only [support, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨A, ⟨i, hi, hA⟩, hx⟩; exact ⟨i, hi, A, hA, hx⟩
  · rintro ⟨i, hi, A, hA, hx⟩; exact ⟨A, ⟨i, hi, hA⟩, hx⟩

private lemma emcg_support_scatter (G : GroupedFamily P) (S : Set (PlacedTile G.P')) :
    support (G.scatter S) = support S := by
  rw [GroupedFamily.scatter, emcg_support_biUnion]
  simp only [support]
  apply iUnion_congr; intro X; apply iUnion_congr; intro _
  rw [emcg_grouped_carrier G X]
  rfl

private lemma emcg_iter_singleton_disjoint (τ : Substitution P) (n : ℕ) {S : Set (PlacedTile P)}
    (hS : DisjointInteriors S) {T T' : PlacedTile P} (hT : T ∈ S) (hT' : T' ∈ S) (hne : T ≠ T') :
    Disjoint (τ.decomposeIter n {T}) (τ.decomposeIter n {T'}) := by
  rw [Set.disjoint_left]
  intro F hF hF'
  have hθ : τ.θ ^ n ≠ 0 := (pow_pos (zero_lt_one.trans τ.one_lt) _).ne'
  have key : ∀ {T : PlacedTile P}, F ∈ τ.decomposeIter n {T} →
      interior F.carrier ⊆ (τ.θ ^ n) • interior T.carrier := by
    intro T hFT
    rw [← interior_smul₀ hθ]
    refine interior_mono ((emcg_carrier_subset_support hFT).trans ?_)
    rw [emcg_iter_support]
    simp [support]
  obtain ⟨y, hy⟩ := emcg_interior_carrier_nonempty F
  obtain ⟨a, ha, rfl⟩ := key hF hy
  obtain ⟨b, hb, hab⟩ := key hF' hy
  rw [smul_right_injective Pt hθ hab] at hb
  exact Set.disjoint_left.mp (hS hT hT' hne) ha hb

section GroupingConstruction2

variable (τ : Substitution P) (k : ℕ) {M : MeshConstants P} {N : ℕ} {R : ℝ}
  {c : P.Form → Pt} (A : ∀ p, AnnularGrouping M (τ.supertile k p) (c p) N R)

/-- The original tiles of `τ^k q` outside the large group and the annular pieces. -/
private def emcgRest (q : P.Form) : Set (PlacedTile P) :=
  τ.supertile k q \ ((A q).L.faces ∪ ⋃ j, ((A q).spokes.piece j).faces)

/-- The grouped version of the supertile `τ^k q`. -/
private def emcgGT (q : P.Form) : Set (PlacedTile (emcgP' τ k A)) :=
  {(⟨Sum.inl q, 0⟩ : PlacedTile (emcgP' τ k A))} ∪
    range (fun j : Fin (4 * N) => (⟨Sum.inr (Sum.inl (q, j)), 0⟩ : PlacedTile (emcgP' τ k A))) ∪
    (fun B : PlacedTile P => (⟨Sum.inr (Sum.inr B.form), B.anchor⟩ : PlacedTile (emcgP' τ k A))) ''
      emcgRest τ k A q

private lemma emcg_mem_GT {q : P.Form} {Y : PlacedTile (emcgP' τ k A)} :
    Y ∈ emcgGT τ k A q ↔ Y = ⟨Sum.inl q, 0⟩ ∨ (∃ j, Y = ⟨Sum.inr (Sum.inl (q, j)), 0⟩) ∨
      ∃ B ∈ emcgRest τ k A q, Y = ⟨Sum.inr (Sum.inr B.form), B.anchor⟩ := by
  simp only [emcgGT, mem_union, mem_singleton_iff, mem_range, mem_image]
  constructor
  · rintro ((h | ⟨j, rfl⟩) | ⟨B, hB, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨j, rfl⟩)
    · exact Or.inr (Or.inr ⟨B, hB, rfl⟩)
  · rintro (h | ⟨j, rfl⟩ | ⟨B, hB, rfl⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨j, rfl⟩)
    · exact Or.inr ⟨B, hB, rfl⟩

private lemma emcg_GT_finite (q : P.Form) : (emcgGT τ k A q).Finite :=
  ((finite_singleton _).union (finite_range _)).union
    (((emcg_supertile_finite τ k q).subset diff_subset).image _)

variable (h : τ.STS)

private lemma emcg_scatter_large (q : P.Form) (v : Pt) :
    (emcgG τ k A h).scatterTile ⟨Sum.inl q, v⟩ = translateSet v (A q).L.faces := rfl

private lemma emcg_scatter_small (q : P.Form) (j : Fin (4 * N)) (v : Pt) :
    (emcgG τ k A h).scatterTile ⟨Sum.inr (Sum.inl (q, j)), v⟩ =
      translateSet v ((A q).spokes.piece j).faces := rfl

private lemma emcg_scatter_orig (r : P.Form) (v : Pt) :
    (emcgG τ k A h).scatterTile ⟨Sum.inr (Sum.inr r), v⟩ = {⟨r, v⟩} := by
  change translateSet v {⟨r, 0⟩} = _
  ext X
  simp [translateSet, PlacedTile.translate]

private lemma emcg_scatter_GT (q : P.Form) :
    (emcgG τ k A h).scatter (emcgGT τ k A q) = τ.supertile k q := by
  apply Subset.antisymm
  · simp only [GroupedFamily.scatter, iUnion_subset_iff]
    intro Y hY
    rcases (emcg_mem_GT τ k A).mp hY with rfl | ⟨j, rfl⟩ | ⟨B, hB, rfl⟩
    · rw [emcg_scatter_large, emcg_translateSet_zero]; exact (A q).L.faces_sub
    · rw [emcg_scatter_small, emcg_translateSet_zero]; exact ((A q).spokes.piece j).faces_sub
    · rw [emcg_scatter_orig, singleton_subset_iff]; exact hB.1
  · intro B hB
    simp only [GroupedFamily.scatter, mem_iUnion, exists_prop]
    by_cases hL : B ∈ (A q).L.faces
    · refine ⟨_, (emcg_mem_GT τ k A).mpr (Or.inl rfl), ?_⟩
      rw [emcg_scatter_large, emcg_translateSet_zero]; exact hL
    by_cases hP : ∃ j, B ∈ ((A q).spokes.piece j).faces
    · obtain ⟨j, hj⟩ := hP
      refine ⟨_, (emcg_mem_GT τ k A).mpr (Or.inr (Or.inl ⟨j, rfl⟩)), ?_⟩
      rw [emcg_scatter_small, emcg_translateSet_zero]; exact hj
    · refine ⟨_, (emcg_mem_GT τ k A).mpr (Or.inr (Or.inr ⟨B, ⟨hB, ?_⟩, rfl⟩)), ?_⟩
      · simp only [mem_union, mem_iUnion, not_or]
        exact ⟨hL, fun ⟨j, hj⟩ => hP ⟨j, hj⟩⟩
      · rw [emcg_scatter_orig]; rfl

private lemma emcg_piece_disjoint_L (q : P.Form) (j : Fin (4 * N)) :
    Disjoint ((A q).spokes.piece j).faces (A q).L.faces := by
  rw [Set.disjoint_left]
  intro B hB hBL
  exact ((A q).spokes.piece_sub j hB).2 hBL

private lemma emcg_piece_disjoint_piece (q : P.Form) {j j' : Fin (4 * N)} (hjj : j ≠ j') :
    Disjoint ((A q).spokes.piece j).faces ((A q).spokes.piece j').faces := by
  rw [Set.disjoint_left]
  intro B hB hB'
  have hS := ((A q).spokes.piece j).faces_sub hB
  obtain ⟨i, -, huniq⟩ := ((A q).spokes.piece_partition B hS).mp ((A q).spokes.piece_sub j hB)
  exact hjj ((huniq j hB).trans (huniq j' hB').symm)

private lemma emcg_GT_scatter_disjoint (q : P.Form) {Y₀ Y₁ : PlacedTile (emcgP' τ k A)}
    (h₀ : Y₀ ∈ emcgGT τ k A q) (h₁ : Y₁ ∈ emcgGT τ k A q) (hne : Y₀ ≠ Y₁) :
    Disjoint ((emcgG τ k A h).scatterTile Y₀) ((emcgG τ k A h).scatterTile Y₁) := by
  rcases (emcg_mem_GT τ k A).mp h₀ with rfl | ⟨j, rfl⟩ | ⟨B, hB, rfl⟩ <;>
    rcases (emcg_mem_GT τ k A).mp h₁ with rfl | ⟨j', rfl⟩ | ⟨B', hB', rfl⟩ <;>
    simp only [emcg_scatter_large, emcg_scatter_small, emcg_scatter_orig, emcg_translateSet_zero,
      disjoint_singleton_left, disjoint_singleton_right]
  · exact absurd rfl hne
  · exact (emcg_piece_disjoint_L τ k A q j').symm
  · exact fun h' => hB'.2 (Or.inl h')
  · exact emcg_piece_disjoint_L τ k A q j
  · exact emcg_piece_disjoint_piece τ k A q (fun hjj => hne (by rw [hjj]))
  · exact fun h' => hB'.2 (Or.inr (mem_iUnion.mpr ⟨j, h'⟩))
  · exact fun h' => hB.2 (Or.inl h')
  · exact fun h' => hB.2 (Or.inr (mem_iUnion.mpr ⟨j', h'⟩))
  · intro hBB
    apply hne
    have : B = B' := PlacedTile.ext (PlacedTile.mk.inj hBB).1.symm (PlacedTile.mk.inj hBB).2.symm
    rw [this]

end GroupingConstruction2

section GroupingConstruction3

variable (τ : Substitution P) (k : ℕ) {M : MeshConstants P} {N : ℕ} {R : ℝ}
  {c : P.Form → Pt} (A : ∀ p, AnnularGrouping M (τ.supertile k p) (c p) N R)

/-- The children of the grouped substitution: every constituent `T` of a grouped form is replaced
by the grouped version of `τ^k T`. -/
private def emcgRuleSet (α : (emcgP' τ k A).Form) : Set (PlacedTile (emcgP' τ k A)) :=
  ⋃ T ∈ (emcgDissect τ k A α).tiles, translateSet ((τ.θ ^ k) • T.anchor) (emcgGT τ k A T.form)

variable (h : τ.STS)

private lemma emcg_scatter_biUnion (G : GroupedFamily P) {ι : Type*} (s : Set ι)
    (f : ι → Set (PlacedTile G.P')) : G.scatter (⋃ i ∈ s, f i) = ⋃ i ∈ s, G.scatter (f i) := by
  ext F
  simp only [GroupedFamily.scatter, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨X, ⟨i, hi, hX⟩, hF⟩; exact ⟨i, hi, X, hX, hF⟩
  · rintro ⟨i, hi, X, hX, hF⟩; exact ⟨X, ⟨i, hi, hX⟩, hF⟩

private lemma emcg_scatter_rule (α : (emcgP' τ k A).Form) :
    (emcgG τ k A h).scatter (emcgRuleSet τ k A α) =
      τ.decomposeIter k (emcgDissect τ k A α).tiles := by
  rw [emcgRuleSet, emcg_scatter_biUnion, emcg_iter_biUnion]
  apply iUnion_congr; intro T; apply iUnion_congr; intro _
  rw [emcg_scatter_translateSet, emcg_scatter_GT, emcg_iter_singleton]

private lemma emcg_rule_finite (α : (emcgP' τ k A).Form) : (emcgRuleSet τ k A α).Finite :=
  (emcgDissect τ k A α).finite.biUnion fun T _ => (emcg_GT_finite τ k A T.form).image _

include h in
private lemma emcg_rule_disjoint (α : (emcgP' τ k A).Form) :
    DisjointInteriors (emcgRuleSet τ k A α) := by
  intro X hX Y hY hXY
  have hsub : ∀ {Z}, Z ∈ emcgRuleSet τ k A α →
      (emcgG τ k A h).scatterTile Z ⊆ τ.decomposeIter k (emcgDissect τ k A α).tiles := by
    intro Z hZ F hF
    rw [← emcg_scatter_rule τ k A h α]
    simp only [GroupedFamily.scatter, mem_iUnion, exists_prop]
    exact ⟨Z, hZ, hF⟩
  have hfin : ∀ Z : PlacedTile (emcgP' τ k A), ((emcgG τ k A h).scatterTile Z).Finite :=
    fun Z => ((emcgG τ k A h).dissect Z.form).finite.image _
  have hdisj : Disjoint ((emcgG τ k A h).scatterTile X) ((emcgG τ k A h).scatterTile Y) := by
    have hX' := hX
    have hY' := hY
    simp only [emcgRuleSet, mem_iUnion, exists_prop] at hX' hY'
    obtain ⟨T, hT, hXT⟩ := hX'
    obtain ⟨T', hT', hYT⟩ := hY'
    rw [emcg_mem_translateSet] at hXT hYT
    obtain ⟨X0, hX0, rfl⟩ := hXT
    obtain ⟨Y0, hY0, rfl⟩ := hYT
    by_cases hTT : T = T'
    · subst hTT
      rw [emcg_scatterTile_translate, emcg_scatterTile_translate]
      refine emcg_translateSet_disjoint _ (emcg_GT_scatter_disjoint τ k A h T.form hX0 hY0 ?_)
      rintro rfl; exact hXY rfl
    · refine (emcg_iter_singleton_disjoint τ k (emcgDissect τ k A α).disjoint hT hT' hTT).mono
        ?_ ?_
      · rw [emcg_scatterTile_translate, emcg_iter_singleton]
        refine image_mono ?_
        rw [← emcg_scatter_GT τ k A h T.form]
        intro F hF
        simp only [GroupedFamily.scatter, mem_iUnion, exists_prop]
        exact ⟨X0, hX0, hF⟩
      · rw [emcg_scatterTile_translate, emcg_iter_singleton]
        refine image_mono ?_
        rw [← emcg_scatter_GT τ k A h T'.form]
        intro F hF
        simp only [GroupedFamily.scatter, mem_iUnion, exists_prop]
        exact ⟨Y0, hY0, hF⟩
  change Disjoint (interior X.carrier) (interior Y.carrier)
  rw [emcg_grouped_carrier (emcgG τ k A h) X, emcg_grouped_carrier (emcgG τ k A h) Y]
  exact emcg_disjoint_interior_support (emcg_iter_disjoint τ k (emcgDissect τ k A α).disjoint)
    (hsub hX) (hsub hY) (hfin X) (hfin Y) hdisj

variable {k} (hk : 0 < k)

/-- The grouped substitution on the labelled catalogue. -/
private def emcgσ : Substitution (emcgP' τ k A) where
  θ := τ.θ ^ k
  one_lt := one_lt_pow₀ τ.one_lt hk.ne'
  rule α := ⟨emcgRuleSet τ k A α, emcg_rule_finite τ k A α, emcg_rule_disjoint τ k A h α⟩
  support_eq α := by
    change support (emcgRuleSet τ k A α) = _
    rw [← emcg_support_scatter (emcgG τ k A h), emcg_scatter_rule τ k A h, emcg_iter_support]
    exact congrArg _ ((emcgG τ k A h).support_eq α)

/-- The grouped substitution for `τ^k` on the labelled catalogue. -/
private def emcgGS : GroupedSubstitution τ where
  G := emcgG τ k A h
  k := k
  k_pos := hk
  σ := emcgσ τ A h hk
  θ_eq := rfl
  compat := emcg_scatter_rule τ k A h

end GroupingConstruction3

section GroupingConstruction4

variable (τ : Substitution P) (k : ℕ) {M : MeshConstants P} {N : ℕ} {R : ℝ}
  {c : P.Form → Pt} (A : ∀ p, AnnularGrouping M (τ.supertile k p) (c p) N R)

private lemma emcg_dissect_sub (α : (emcgP' τ k A).Form) :
    ∃ n p, (emcgDissect τ k A α).tiles ⊆ τ.supertile n p ∧ (n = 0 ∨ n = k) := by
  rcases α with p | ⟨p, j⟩ | p
  · exact ⟨k, p, (A p).L.faces_sub, Or.inr rfl⟩
  · exact ⟨k, p, ((A p).spokes.piece j).faces_sub, Or.inr rfl⟩
  · exact ⟨0, p, subset_rfl, Or.inl rfl⟩

private lemma emcg_iter_sts (h : τ.STS) (α : (emcgP' τ k A).Form) :
    SideToSideSet (τ.decomposeIter k (emcgDissect τ k A α).tiles) := by
  obtain ⟨n, p, hsub, -⟩ := emcg_dissect_sub τ k A α
  refine emcg_sts_subset (h (n + k) p) ?_
  rw [Substitution.supertile, ← emcg_iter_add]
  exact emcg_iter_mono τ k hsub

private lemma emcg_square_add_Binf (c : Pt) (a b : ℝ) : square c a + Binf b ⊆ square c (a + b) := by
  rintro x ⟨y, hy, z, hz, rfl⟩
  simp only [square, Binf, mem_setOf_eq] at hy hz ⊢
  simp only [PiLp.add_apply]
  constructor
  · calc |y 0 + z 0 - c 0| = |(y 0 - c 0) + z 0| := by ring_nf
      _ ≤ |y 0 - c 0| + |z 0| := abs_add_le _ _
      _ ≤ a + b := add_le_add hy.1 hz.1
  · calc |y 1 + z 1 - c 1| = |(y 1 - c 1) + z 1| := by ring_nf
      _ ≤ |y 1 - c 1| + |z 1| := abs_add_le _ _
      _ ≤ a + b := add_le_add hy.2 hz.2

private lemma emcg_square_mono (c : Pt) {a b : ℝ} (hab : a ≤ b) : square c a ⊆ square c b :=
  fun _ hx => ⟨hx.1.trans hab, hx.2.trans hab⟩

private lemma emcg_L_support_square (hR : 0 ≤ R) (p : P.Form) :
    support (A p).L.faces ⊆ square (c p) ((N : ℝ) * R / 2 + R + 3 * M.D) := by
  rw [← (A p).L.carrier_eq]
  refine (A p).L_upper.trans ((emcg_square_add_Binf _ _ _).trans (emcg_square_mono _ ?_))
  linarith [M.D_pos]

private lemma emcg_piece_support_square (p : P.Form) (j : Fin (4 * N)) :
    support ((A p).spokes.piece j).faces ⊆ square (c p) ((N : ℝ) * R / 2 + R + 3 * M.D) := by
  have hsub : support ((A p).spokes.piece j).faces ⊆ (A p).H.carrier := by
    rw [FaceGroup.carrier, (A p).H.carrier_eq]
    intro x hx
    simp only [support, mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨B, hB, hx⟩ := hx
    exact ⟨B, ((A p).spokes.piece_sub j hB).1, hx⟩
  exact hsub.trans ((A p).H_upper.trans (emcg_square_add_Binf _ _ _))

private lemma emcg_support_nonempty {S : Set (PlacedTile P)} (hS : S.Nonempty) :
    (support S).Nonempty := by
  obtain ⟨B, hB⟩ := hS
  obtain ⟨y, hy⟩ := emcg_interior_carrier_nonempty B
  exact ⟨y, emcg_carrier_subset_support hB (interior_subset hy)⟩

private lemma emcg_grouped_disks_distinct (h : τ.STS) (hR : 0 ≤ R)
    (hsep : ∀ p q, p ≠ q → Disjoint (square (c p) ((N : ℝ) * R / 2 + R + 3 * M.D))
      (square (c q) ((N : ℝ) * R / 2 + R + 3 * M.D)))
    (α β : (emcgP' τ k A).Form) (hα : (emcgDissect τ k A α).tiles.Nontrivial)
    (hβ : (emcgDissect τ k A β).tiles.Nontrivial)
    (hdisk : (emcgP' τ k A).disk α = (emcgP' τ k A).disk β) : α = β := by
  have hsupp : support (emcgDissect τ k A α).tiles = support (emcgDissect τ k A β).tiles := by
    have h1 : support (emcgDissect τ k A α).tiles = ((emcgP' τ k A).disk α).carrier :=
      (emcgG τ k A h).support_eq α
    have h2 : support (emcgDissect τ k A β).tiles = ((emcgP' τ k A).disk β).carrier :=
      (emcgG τ k A h).support_eq β
    rw [h1, h2, hdisk]
  have hsame : ∀ p q, support (emcgDissect τ k A α).tiles ⊆
      square (c p) ((N : ℝ) * R / 2 + R + 3 * M.D) →
      support (emcgDissect τ k A β).tiles ⊆ square (c q) ((N : ℝ) * R / 2 + R + 3 * M.D) →
      p = q := by
    intro p q hp hq
    by_contra hpq
    obtain ⟨y, hy⟩ := emcg_support_nonempty hα.nonempty
    exact Set.disjoint_left.mp (hsep p q hpq) (hp hy) (hq (hsupp ▸ hy))
  rcases α with p | ⟨p, j⟩ | p <;> rcases β with q | ⟨q, j'⟩ | q
  · obtain rfl := hsame p q (emcg_L_support_square τ k A hR p) (emcg_L_support_square τ k A hR q)
    rfl
  · obtain rfl := hsame p q (emcg_L_support_square τ k A hR p) (emcg_piece_support_square τ k A q j')
    exact absurd hsupp (emcg_support_ne (emcg_supertile_disjoint τ k p) (A p).L.faces_sub
      ((A p).spokes.piece j').faces_sub (A p).L.finite ((A p).spokes.piece j').finite
      (emcg_piece_disjoint_L τ k A p j').symm hα.nonempty)
  · exact absurd hβ (not_nontrivial_singleton (x := (⟨q, 0⟩ : PlacedTile P)))
  · obtain rfl := hsame p q (emcg_piece_support_square τ k A p j) (emcg_L_support_square τ k A hR q)
    exact absurd hsupp (emcg_support_ne (emcg_supertile_disjoint τ k p)
      ((A p).spokes.piece j).faces_sub (A p).L.faces_sub ((A p).spokes.piece j).finite
      (A p).L.finite (emcg_piece_disjoint_L τ k A p j) hα.nonempty)
  · obtain rfl := hsame p q (emcg_piece_support_square τ k A p j)
      (emcg_piece_support_square τ k A q j')
    by_cases hjj : j = j'
    · rw [hjj]
    · exact absurd hsupp (emcg_support_ne (emcg_supertile_disjoint τ k p)
        ((A p).spokes.piece j).faces_sub ((A p).spokes.piece j').faces_sub
        ((A p).spokes.piece j).finite ((A p).spokes.piece j').finite
        (emcg_piece_disjoint_piece τ k A p hjj) hα.nonempty)
  · exact absurd hβ (not_nontrivial_singleton (x := (⟨q, 0⟩ : PlacedTile P)))
  all_goals exact absurd hα (not_nontrivial_singleton (x := (⟨p, 0⟩ : PlacedTile P)))

end GroupingConstruction4

private lemma emcg_norm_le_abs_add (v : Pt) : ‖v‖ ≤ |v 0| + |v 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), sq_abs (v 0), sq_abs (v 1)]

private lemma emcg_norm_sub_le_of_square {c y : Pt} {W : ℝ} (hy : y ∈ square c W) :
    ‖y - c‖ ≤ 2 * W := by
  refine (emcg_norm_le_abs_add _).trans ?_
  simp only [PiLp.sub_apply]
  linarith [hy.1, hy.2]

/-- Choice of the substitution power and of well-separated centres: for every half side `W` there
are `k > 0` and centres whose squares lie in the interiors of the scaled forms and are pairwise
disjoint. -/
private lemma emcg_centres (τ : Substitution P) {W : ℝ} (hW : 0 < W) :
    ∃ k, 0 < k ∧ ∃ c : P.Form → Pt,
      (∀ p, square (c p) W ⊆ interior ((τ.θ ^ k) • (P.disk p).carrier)) ∧
      ∀ p q, p ≠ q → Disjoint (square (c p) W) (square (c q) W) := by
  have hex : ∀ p : P.Form, ∃ x : Pt, ∃ ε > 0, Metric.ball x ε ⊆ interior (P.disk p).carrier := by
    intro p
    obtain ⟨x, hx⟩ := (P.disk p).interior_nonempty
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    exact ⟨x, ε, hε, hball⟩
  choose x ε hε hball using hex
  set n : ℕ := Fintype.card P.Form
  let e := Fintype.equivFin P.Form
  let off : P.Form → Pt := fun p => EuclideanSpace.single 0 (3 * W * ((e p : ℕ) : ℝ))
  have hoff : ∀ p, ‖off p‖ ≤ 3 * W * n := by
    intro p
    simp only [off, EuclideanSpace.norm_single, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have : ((e p : ℕ) : ℝ) ≤ n := by exact_mod_cast (e p).isLt.le
    nlinarith
  have hθ : Filter.Tendsto (fun k : ℕ => τ.θ ^ k) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt τ.one_lt
  have hev : ∀ᶠ k : ℕ in Filter.atTop, 0 < k ∧
      (∀ p, 2 * W + 3 * W * n < τ.θ ^ k * ε p) ∧
      ∀ pq : P.Form × P.Form, x pq.1 ≠ x pq.2 →
        4 * W + 6 * W * n < τ.θ ^ k * ‖x pq.1 - x pq.2‖ := by
    refine (Filter.eventually_gt_atTop 0).and ((Filter.eventually_all.mpr fun p => ?_).and
      (Filter.eventually_all.mpr fun pq => ?_))
    · exact (hθ.atTop_mul_const (hε p)).eventually_gt_atTop _
    · by_cases hpq : x pq.1 = x pq.2
      · exact Filter.Eventually.of_forall fun _ h => absurd hpq h
      · exact ((hθ.atTop_mul_const (norm_pos_iff.mpr (sub_ne_zero.mpr hpq))).eventually_gt_atTop
          _).mono fun _ h _ => h
  obtain ⟨k, hk0, hka, hkb⟩ := hev.exists
  have hθk : 0 < τ.θ ^ k := pow_pos (zero_lt_one.trans τ.one_lt) _
  refine ⟨k, hk0, fun p => (τ.θ ^ k) • x p + off p, ?_, ?_⟩
  · intro p y hy
    rw [interior_smul₀ hθk.ne']
    refine smul_set_mono (hball p) ?_
    rw [smul_ball hθk.ne', Real.norm_eq_abs, abs_of_pos hθk, Metric.mem_ball, dist_eq_norm]
    have h1 := emcg_norm_sub_le_of_square hy
    calc ‖y - (τ.θ ^ k) • x p‖ = ‖(y - ((τ.θ ^ k) • x p + off p)) + off p‖ := by
          congr 1; abel
      _ ≤ ‖y - ((τ.θ ^ k) • x p + off p)‖ + ‖off p‖ := norm_add_le _ _
      _ < τ.θ ^ k * ε p := by linarith [hoff p, hka p]
  · intro p q hpq
    rw [Set.disjoint_left]
    intro y hyp hyq
    have hp0 : |y 0 - ((τ.θ ^ k) • x p + off p) 0| ≤ W := hyp.1
    have hp1 : |y 1 - ((τ.θ ^ k) • x p + off p) 1| ≤ W := hyp.2
    have hq0 : |y 0 - ((τ.θ ^ k) • x q + off q) 0| ≤ W := hyq.1
    have hq1 : |y 1 - ((τ.θ ^ k) • x q + off q) 1| ≤ W := hyq.2
    have h0 : |((τ.θ ^ k) • x p + off p) 0 - ((τ.θ ^ k) • x q + off q) 0| ≤ 2 * W := by
      have := abs_sub_le (((τ.θ ^ k) • x p + off p) 0) (y 0) (((τ.θ ^ k) • x q + off q) 0)
      linarith [abs_sub_comm (y 0) (((τ.θ ^ k) • x p + off p) 0)]
    have h1 : |((τ.θ ^ k) • x p + off p) 1 - ((τ.θ ^ k) • x q + off q) 1| ≤ 2 * W := by
      have := abs_sub_le (((τ.θ ^ k) • x p + off p) 1) (y 1) (((τ.θ ^ k) • x q + off q) 1)
      linarith [abs_sub_comm (y 1) (((τ.θ ^ k) • x p + off p) 1)]
    by_cases hx : x p = x q
    · have hne : ((e p : ℕ) : ℝ) ≠ ((e q : ℕ) : ℝ) := by
        intro h'
        exact hpq (e.injective (Fin.ext (by exact_mod_cast h')))
      have hge : 1 ≤ |((e p : ℕ) : ℝ) - ((e q : ℕ) : ℝ)| := by
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have : ((e p : ℕ) : ℝ) + 1 ≤ ((e q : ℕ) : ℝ) := by
            exact_mod_cast (show (e p : ℕ) + 1 ≤ (e q : ℕ) by exact_mod_cast hlt)
          rw [abs_of_neg (by linarith)]; linarith
        · have : ((e q : ℕ) : ℝ) + 1 ≤ ((e p : ℕ) : ℝ) := by
            exact_mod_cast (show (e q : ℕ) + 1 ≤ (e p : ℕ) by exact_mod_cast hlt)
          rw [abs_of_pos (by linarith)]; linarith
      rw [hx] at h0
      simp only [PiLp.add_apply, add_sub_add_left_eq_sub, off, EuclideanSpace.single_apply,
        if_true] at h0
      rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 * W)] at h0
      nlinarith
    · have hb := hkb (p, q) hx
      have hsum : ‖((τ.θ ^ k) • x p + off p) - ((τ.θ ^ k) • x q + off q)‖ ≤ 4 * W := by
        refine (emcg_norm_le_abs_add _).trans ?_
        simp only [PiLp.sub_apply]
        linarith
      have hrw : (τ.θ ^ k) • (x p - x q) =
          (((τ.θ ^ k) • x p + off p) - ((τ.θ ^ k) • x q + off q)) - off p + off q := by
        rw [smul_sub]; abel
      have hn1 := norm_add_le
        ((((τ.θ ^ k) • x p + off p) - ((τ.θ ^ k) • x q + off q)) - off p) (off q)
      have hn2 := norm_sub_le (((τ.θ ^ k) • x p + off p) - ((τ.θ ^ k) • x q + off q)) (off p)
      have hn3 : ‖(τ.θ ^ k) • (x p - x q)‖ = τ.θ ^ k * ‖x p - x q‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθk]
      rw [← hn3, hrw] at hb
      linarith [hoff p, hoff q]

private lemma emcg_smul_segment (θ : ℝ) (a b : Pt) :
    θ • segment ℝ a b = segment ℝ (θ • a) (θ • b) := by
  rw [← Set.image_smul]
  exact image_segment ℝ ((θ • LinearMap.id : Pt →ₗ[ℝ] Pt).toAffineMap) a b

/-- A polygonal disk scaled by a nonzero factor. -/
private def emcgScaleDisk (D : PolygonalDisk) (θ : ℝ) (hθ : θ ≠ 0) : PolygonalDisk where
  carrier := θ • D.carrier
  n := D.n
  three_le := D.three_le
  vertex i := θ • D.vertex i
  vertex_injective i j hij := D.vertex_injective (smul_right_injective Pt hθ hij)
  compact := D.compact.smul θ
  interior_nonempty := by
    rw [interior_smul₀ hθ]
    obtain ⟨x, hx⟩ := D.interior_nonempty
    exact ⟨θ • x, smul_mem_smul_set hx⟩
  regular_closed := by rw [interior_smul₀ hθ, closure_smul₀, D.regular_closed]
  interior_pathConnected := by
    rw [interior_smul₀ hθ, ← Set.image_smul]
    exact D.interior_pathConnected.image (continuous_const_smul θ)
  frontier_eq := by
    rw [frontier, closure_smul₀, interior_smul₀ hθ, ← Set.smul_set_sdiff₀ hθ, ← frontier,
      D.frontier_eq, Set.smul_set_iUnion]
    simp only [emcg_smul_segment]
  simple i j hij := by
    have h := Set.smul_set_mono (a := θ) (D.simple i j hij)
    rw [Set.smul_set_inter₀ hθ, Set.smul_set_inter₀ hθ, emcg_smul_segment, emcg_smul_segment,
      Set.smul_set_insert, Set.smul_set_insert, Set.smul_set_singleton,
      Set.smul_set_singleton] at h
    exact h

private lemma emcg_window_far (v w z q : Pt) (μ A R : ℝ) (hA : 0 < A) (hμ : 0 ≤ μ)
    (hR : 0 ≤ R) (hv : v 0 ^ 2 + v 1 ^ 2 ≤ 2 * A ^ 2)
    (hw : w 0 ^ 2 + w 1 ^ 2 ≤ 2 * A ^ 2)
    (h1 : 3 * A * R / 16 ≤ jcr v z) (h2 : 3 * A * R / 16 ≤ jcr z w)
    (hq : jcr v q ≤ 0 ∨ jcr q w ≤ 0) :
    R ^ 2 / 64 ≤ (z 0 - μ * q 0) ^ 2 + (z 1 - μ * q 1) ^ 2 := by
  unfold jcr at *
  set d0 := z 0 - μ * q 0
  set d1 := z 1 - μ * q 1
  have key : ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 2 * A ^ 2 →
      3 * A * R / 16 ≤ a * d1 - b * d0 → R ^ 2 / 64 ≤ d0 ^ 2 + d1 ^ 2 := by
    intro a b hab hc
    have hl : (a * d1 - b * d0) ^ 2 ≤ (a ^ 2 + b ^ 2) * (d0 ^ 2 + d1 ^ 2) := by
      nlinarith [sq_nonneg (a * d0 + b * d1)]
    have hpos : 0 ≤ 3 * A * R / 16 := by positivity
    have h3 : (3 * A * R / 16) ^ 2 ≤ 2 * A ^ 2 * (d0 ^ 2 + d1 ^ 2) := by
      calc
        (3 * A * R / 16) ^ 2 ≤ (a * d1 - b * d0) ^ 2 := pow_le_pow_left₀ hpos hc 2
        _ ≤ _ := hl
        _ ≤ _ := mul_le_mul_of_nonneg_right hab (by positivity)
    have hA2 : 0 < A ^ 2 := by positivity
    nlinarith
  rcases hq with hq | hq
  · exact key (v 0) (v 1) hv (by simp only [d0, d1]; nlinarith)
  · exact key (-w 0) (-w 1) (by nlinarith) (by simp only [d0, d1]; nlinarith)

private lemma emcg_window_farFromOthers {c : Pt} {N : ℕ} {R D : ℝ} (hN : 2 ≤ N)
    (hD : 0 < D) (hR : 1000 * D ≤ R) (j : Fin (4 * N)) (k : ℕ) (hk : k < 4)
    (hu1 : 2 * k * ((N : ℝ) * R / 2) ≤ ((j : ℕ) : ℝ) * R)
    (hu2 : ((j : ℕ) : ℝ) * R + R ≤ 2 * (k + 1) * ((N : ℝ) * R / 2))
    (p : Pt)
    (h1 : 3 * ((N : ℝ) * R / 2) * R / 16 ≤
      jcr (squarePerimeterPoint ((N : ℝ) * R / 2) (((j : ℕ) : ℝ) * R)) (p - c))
    (h2 : 3 * ((N : ℝ) * R / 2) * R / 16 ≤
      jcr (p - c) (squarePerimeterPoint ((N : ℝ) * R / 2) (((j : ℕ) : ℝ) * R + R)))
    (t : Fin (4 * N)) (ht : t ≠ j) (q : Pt)
    (hq : q ∈ idealTrapezoid c N R D (t : ℕ)) : R / 8 ≤ dist p q := by
  obtain ⟨τ, ⟨hτ1, hτ2⟩, μ, ⟨hμ1, -⟩, rfl⟩ := hq
  have hRpos : 0 < R := by linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  have htN : ((t : ℕ) : ℝ) + 1 ≤ 4 * N := by
    exact_mod_cast (show (t : ℕ) + 1 ≤ 4 * N by omega)
  have hjN : ((j : ℕ) : ℝ) + 1 ≤ 4 * N := by
    exact_mod_cast (show (j : ℕ) + 1 ≤ 4 * N by omega)
  have hτ0 : 0 ≤ τ := le_trans (by positivity) hτ1
  have hτ8 : τ ≤ 8 * ((N : ℝ) * R / 2) := by nlinarith
  have hτ : τ ≤ ((j : ℕ) : ℝ) * R ∨ ((j : ℕ) : ℝ) * R + R ≤ τ := by
    have hne : (t : ℕ) ≠ (j : ℕ) := fun h => ht (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · left
      have : ((t : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast h
      nlinarith
    · right
      have : ((j : ℕ) : ℝ) + 1 ≤ (t : ℕ) := by exact_mod_cast h
      nlinarith
  have hsign := step5_sign _ _ _ _ k hk hA hRpos hu1 hu2 hτ0 hτ8 hτ
  have hv := step5_spp_bound (A := (N : ℝ) * R / 2) (t := ((j : ℕ) : ℝ) * R)
    (by positivity) (by nlinarith)
  have hw := step5_spp_bound (A := (N : ℝ) * R / 2)
    (t := ((j : ℕ) : ℝ) * R + R) (by positivity) (by nlinarith)
  have key := emcg_window_far _ _ (p - c) _ μ _ R hA (by linarith) hRpos.le hv hw h1 h2 hsign
  have hd : dist p (c + μ • squarePerimeterPoint ((N : ℝ) * R / 2) τ) ^ 2 =
      ((p - c) 0 - μ * squarePerimeterPoint ((N : ℝ) * R / 2) τ 0) ^ 2 +
        ((p - c) 1 - μ * squarePerimeterPoint ((N : ℝ) * R / 2) τ 1) ^ 2 := by
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp [Real.dist_eq, sq_abs]
    ring
  have hdn := dist_nonneg (x := p)
    (y := c + μ • squarePerimeterPoint ((N : ℝ) * R / 2) τ)
  nlinarith [key]

private lemma emcg_window_core {M : MeshConstants P} {S : Set (PlacedTile P)} {c : Pt}
    {N : ℕ} {R : ℝ} (hR : 1000 * M.D ≤ R) (G : AnnularGrouping M S c N R)
    (hloc : ∀ j : Fin (4 * N), (G.spokes.piece j).carrier ⊆
      Metric.cthickening (20 * M.D) (idealTrapezoid c N R M.D (j : ℕ)))
    (j : Fin (4 * N)) (f : Pt → ℝ) (s : ℝ) (γ : ℝ → Pt) (hγ : Continuous γ)
    {x0 x1 : ℝ} (hx : x0 ≤ x1) (h0 : γ x0 ∈ G.H.carrier) (h1 : γ x1 ∉ G.H.carrier)
    (hfs : ∀ x ∈ Icc x0 x1, f (γ x) = s) (hL : ∀ x ∈ Icc x0 x1, γ x ∉ G.L.carrier)
    (hfar : ∀ x ∈ Icc x0 x1, ∀ t : Fin (4 * N), t ≠ j →
      ∀ q ∈ idealTrapezoid c N R M.D (t : ℕ), R / 8 ≤ dist (γ x) q) :
    ∃ e ∈ privateOuterEdges G j, ∃ p ∈ e, f p = s ∧
      ∀ t : Fin (4 * N), t ≠ j →
        ∀ q ∈ idealTrapezoid c N R M.D (t : ℕ), R / 8 ≤ dist p q := by
  obtain ⟨x, hxI, hxf⟩ := step5_frontier_hit hγ hx h0 h1
  have hfr : frontier G.H.carrier = ⋃ i, G.H.disk.side i := G.H.disk.frontier_eq
  have hxf' := hxf
  rw [hfr, mem_iUnion] at hxf'
  obtain ⟨i, hi⟩ := hxf'
  obtain ⟨A, hAH, iA, hA⟩ := G.H.side_whole i
  obtain ⟨F, hFS, hFH, ⟨iF, hF⟩, -⟩ := G.H_anchor i
  have hpA : γ x ∈ A.carrier := tile_side_subset A iA (hA ▸ hi)
  have hpF : γ x ∈ F.carrier := tile_side_subset F iF (hF ▸ hi)
  have hfarE : ∀ t : Fin (4 * N), t ≠ j → ∀ y, dist y (γ x) ≤ M.D →
      y ∉ (G.spokes.piece t).carrier := by
    intro t ht y hy hyt
    have hlocy := hloc t hyt
    rw [Metric.mem_cthickening_iff] at hlocy
    have h2 : ENNReal.ofReal (22 * M.D) ≤
        Metric.infEDist (γ x) (idealTrapezoid c N R M.D (t : ℕ)) := by
      rw [Metric.le_infEDist]
      intro q hq
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      exact (show 22 * M.D ≤ R / 8 by linarith [M.D_pos]).trans (hfar x hxI t ht q hq)
    have h3 := Metric.infEDist_le_infEDist_add_edist (x := γ x) (y := y)
      (s := idealTrapezoid c N R M.D (t : ℕ))
    rw [edist_dist, dist_comm] at h3
    have h4 : ENNReal.ofReal (22 * M.D) ≤
        ENNReal.ofReal (20 * M.D) + ENNReal.ofReal M.D :=
      h2.trans (h3.trans (add_le_add hlocy (ENNReal.ofReal_le_ofReal hy)))
    rw [← ENNReal.ofReal_add (by linarith [M.D_pos]) M.D_pos.le] at h4
    have := (ENNReal.ofReal_le_ofReal_iff (by linarith [M.D_pos])).1 h4
    linarith [M.D_pos]
  have hAj : A ∈ (G.spokes.piece j).faces := by
    have hAL : A ∉ G.L.faces := by
      intro hAL
      apply hL x hxI
      show γ x ∈ G.L.disk.carrier
      rw [G.L.carrier_eq]
      exact carrier_subset_support hAL hpA
    obtain ⟨t, ht, -⟩ := (G.spokes.piece_partition A (G.H.faces_sub hAH)).1 ⟨hAH, hAL⟩
    by_cases htj : t = j
    · exact htj ▸ ht
    · exfalso
      apply hfarE t htj (γ x) (by simp [M.D_pos.le])
      show γ x ∈ (G.spokes.piece t).disk.carrier
      rw [(G.spokes.piece t).carrier_eq]
      exact carrier_subset_support ht hpA
  refine ⟨G.H.disk.side i, ⟨⟨A, hAj, iA, hA⟩, ?_, F, hFS, hFH, ⟨iF, hF⟩, ?_⟩,
    γ x, hi, hfs x hxI, ?_⟩
  · rw [hfr]
    exact subset_iUnion (fun i => G.H.disk.side i) i
  · intro t ht
    rw [Set.disjoint_left]
    intro y hyF hyt
    exact hfarE t ht y (step5_tile_dist_le M F hyF hpF) hyt
  · exact hfar x hxI

private lemma emcg_window_reduced {A R D y x s δ : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hR : 1000 * D ≤ R) (hRA : R ≤ A) (hy1 : -A ≤ y) (hy2 : y ≤ A - R)
    (hx1 : A + R + 2 * D ≤ x) (hx2 : x ≤ A + R + 4 * D)
    (hδ1 : R / 16 ≤ δ) (hδ2 : δ ≤ 7 * R / 16)
    (hs : s = y * (A + R + 2 * D) / A + R / 8 + 2 * D + δ) :
    3 * A * R / 16 ≤ A * s - y * x ∧
      3 * A * R / 16 ≤ x * (y + R) - s * A ∧ |s| ≤ A + R + 2 * D := by
  have e : y * (A + R + 2 * D) / A * A = y * (A + R + 2 * D) := by field_simp
  have hs' : A * s = y * (A + R + 2 * D) + A * (R / 8 + 2 * D + δ) := by
    rw [hs]
    nlinarith
  refine ⟨?_, ?_, abs_le.2 ⟨?_, ?_⟩⟩ <;> nlinarith

private lemma emcg_window_side {M : MeshConstants P} {S : Set (PlacedTile P)} {c : Pt}
    {N : ℕ} {R : ℝ} (hN : 2 ≤ N) (hR : 1000 * M.D ≤ R)
    (G : AnnularGrouping M S c N R)
    (hloc : ∀ j : Fin (4 * N), (G.spokes.piece j).carrier ⊆
      Metric.cthickening (20 * M.D) (idealTrapezoid c N R M.D (j : ℕ)))
    (j : Fin (4 * N)) (k : ℕ) (hk : k < 4)
    (hu1 : 2 * k * ((N : ℝ) * R / 2) ≤ ((j : ℕ) : ℝ) * R)
    (hu2 : ((j : ℕ) : ℝ) * R + R ≤ 2 * (k + 1) * ((N : ℝ) * R / 2))
    (y : ℝ) (hy1 : -((N : ℝ) * R / 2) ≤ y)
    (hy2 : y ≤ (N : ℝ) * R / 2 - R) (f : Pt → ℝ) (g : ℝ → ℝ)
    (s δ : ℝ) (hδ1 : R / 16 ≤ δ) (hδ2 : δ ≤ 7 * R / 16)
    (Z : ℝ → ℝ → Pt) (hZc : ∀ u, Continuous (Z u)) (hfZ : ∀ u x, f (Z u x) = u)
    (hg : g s = y * ((N : ℝ) * R / 2 + R + 2 * M.D) / ((N : ℝ) * R / 2) +
      R / 8 + 2 * M.D + δ) (hgabs : ∀ u, |g u| = |u|)
    (hZsq : ∀ u x, (|Z u x 0 - c 0| = |x| ∧ |Z u x 1 - c 1| = |u|) ∨
      (|Z u x 0 - c 0| = |u| ∧ |Z u x 1 - c 1| = |x|))
    (hcr1 : ∀ u x, jcr (squarePerimeterPoint ((N : ℝ) * R / 2)
      (((j : ℕ) : ℝ) * R)) (Z u x - c) = (N : ℝ) * R / 2 * g u - y * x)
    (hcr2 : ∀ u x, jcr (Z u x - c) (squarePerimeterPoint ((N : ℝ) * R / 2)
      (((j : ℕ) : ℝ) * R + R)) = x * (y + R) - g u * ((N : ℝ) * R / 2)) :
    ∃ e ∈ privateOuterEdges G j, ∃ p ∈ e, f p = s ∧
      ∀ t : Fin (4 * N), t ≠ j →
        ∀ q ∈ idealTrapezoid c N R M.D (t : ℕ), R / 8 ≤ dist p q := by
  have hD := M.D_pos
  have hRpos : 0 < R := by linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  have hRA : R ≤ (N : ℝ) * R / 2 := by nlinarith
  have red : ∀ x ∈ Icc ((N : ℝ) * R / 2 + R + 2 * M.D)
      ((N : ℝ) * R / 2 + R + 4 * M.D),
      3 * ((N : ℝ) * R / 2) * R / 16 ≤ (N : ℝ) * R / 2 * g s - y * x ∧
      3 * ((N : ℝ) * R / 2) * R / 16 ≤ x * (y + R) - g s * ((N : ℝ) * R / 2) ∧
      |g s| ≤ (N : ℝ) * R / 2 + R + 2 * M.D := by
    intro x hx
    exact emcg_window_reduced hA hD hR hRA hy1 hy2 hx.1 hx.2 hδ1 hδ2 hg
  have hsabs : |s| ≤ (N : ℝ) * R / 2 + R + 2 * M.D := by
    rw [← hgabs s]
    exact (red _ ⟨le_rfl, by linarith⟩).2.2
  refine emcg_window_core hR G hloc j f s (Z s) (hZc s)
    (x0 := (N : ℝ) * R / 2 + R + 2 * M.D)
    (x1 := (N : ℝ) * R / 2 + R + 4 * M.D) (by linarith) ?_ ?_
    (fun x _ => hfZ s x) ?_ ?_
  · apply G.H_lower
    apply rg_square_add (by positivity) (by positivity)
    have hx0 : |(N : ℝ) * R / 2 + R + 2 * M.D| =
        (N : ℝ) * R / 2 + R + 2 * M.D := abs_of_pos (by positivity)
    rcases hZsq s ((N : ℝ) * R / 2 + R + 2 * M.D) with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ⟨h0.trans_le hx0.le, h1.trans_le hsabs⟩
    · exact ⟨h0.trans_le hsabs, h1.trans_le hx0.le⟩
  · intro hmem
    have hsq := step5_square_add_subset (G.H_upper hmem)
    have hx1 : |(N : ℝ) * R / 2 + R + 4 * M.D| =
        (N : ℝ) * R / 2 + R + 4 * M.D := abs_of_pos (by positivity)
    rcases hZsq s ((N : ℝ) * R / 2 + R + 4 * M.D) with ⟨h0, -⟩ | ⟨-, h1⟩
    · have := hsq.1
      rw [h0, hx1] at this
      linarith
    · have := hsq.2
      rw [h1, hx1] at this
      linarith
  · intro x hx hmem
    have hsq := step5_square_add_subset (G.L_upper hmem)
    have hxa : |x| = x := abs_of_pos (by linarith [hx.1])
    rcases hZsq s x with ⟨h0, -⟩ | ⟨-, h1⟩
    · have := hsq.1
      rw [h0, hxa] at this
      linarith [hx.1]
    · have := hsq.2
      rw [h1, hxa] at this
      linarith [hx.1]
  · intro x hx t ht q hq
    exact emcg_window_farFromOthers hN hD hR j k hk hu1 hu2 (Z s x)
      (by rw [hcr1]; exact (red x hx).1) (by rw [hcr2]; exact (red x hx).2.1) t ht q hq

private lemma emcg_window_pick {M : MeshConstants P} {S : Set (PlacedTile P)} (c : Pt)
    {N : ℕ} {R : ℝ} (hN : 2 ≤ N) (hR : 1000 * M.D ≤ R)
    (G : AnnularGrouping M S c N R)
    (hloc : ∀ j : Fin (4 * N), (G.spokes.piece j).carrier ⊆
      Metric.cthickening (20 * M.D) (idealTrapezoid c N R M.D (j : ℕ)))
    (j : Fin (4 * N)) :
    ∃ f : Pt → ℝ, LipschitzWith 1 f ∧ ∃ a : ℝ,
      ∃ (e : Fin 4 → Set Pt) (p : Fin 4 → Pt),
      ∀ i, e i ∈ privateOuterEdges G j ∧ p i ∈ e i ∧
        f (p i) = a + (2 * (i : ℕ) + 1) * R / 16 ∧
        ∀ t : Fin (4 * N), t ≠ j →
          ∀ q ∈ idealTrapezoid c N R M.D (t : ℕ), R / 8 ≤ dist (p i) q := by
  have hD := M.D_pos
  have hRpos : 0 < R := by linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  obtain ⟨k, hk, hk1, hk2⟩ :
      ∃ k, k < 4 ∧ k * N ≤ (j : ℕ) ∧ (j : ℕ) + 1 ≤ (k + 1) * N := by
    refine ⟨(j : ℕ) / N, (Nat.div_lt_iff_lt_mul (by omega)).2 j.isLt,
      Nat.div_mul_le_self _ _, ?_⟩
    have h1 := Nat.div_add_mod (j : ℕ) N
    have h2 := Nat.mod_lt (j : ℕ) (show N > 0 by omega)
    nlinarith
  have hk1' : (k : ℝ) * N ≤ (j : ℕ) := by exact_mod_cast hk1
  have hk2' : ((j : ℕ) : ℝ) + 1 ≤ ((k : ℝ) + 1) * N := by exact_mod_cast hk2
  have hu1 : 2 * k * ((N : ℝ) * R / 2) ≤ ((j : ℕ) : ℝ) * R := by nlinarith
  have hu2 : ((j : ℕ) : ℝ) * R + R ≤ 2 * (k + 1) * ((N : ℝ) * R / 2) := by nlinarith
  set A := (N : ℝ) * R / 2 with hAdef
  set u := ((j : ℕ) : ℝ) * R with hudef
  have finish (f : Pt → ℝ) (hf : LipschitzWith 1 f) (a : ℝ)
      (H : ∀ i : Fin 4, ∃ e ∈ privateOuterEdges G j, ∃ p ∈ e,
        f p = a + (2 * (i : ℕ) + 1) * R / 16 ∧
          ∀ t : Fin (4 * N), t ≠ j →
            ∀ q ∈ idealTrapezoid c N R M.D (t : ℕ), R / 8 ≤ dist p q) :
      ∃ f : Pt → ℝ, LipschitzWith 1 f ∧ ∃ a : ℝ,
        ∃ (e : Fin 4 → Set Pt) (p : Fin 4 → Pt),
        ∀ i, e i ∈ privateOuterEdges G j ∧ p i ∈ e i ∧
          f (p i) = a + (2 * (i : ℕ) + 1) * R / 16 ∧
          ∀ t : Fin (4 * N), t ≠ j →
            ∀ q ∈ idealTrapezoid c N R M.D (t : ℕ), R / 8 ≤ dist (p i) q := by
    choose e he p hp hfp hfar using H
    exact ⟨f, hf, a, e, p, fun i => ⟨he i, hp i, hfp i, hfar i⟩⟩
  interval_cases k <;> norm_num at hu1 hu2
  · let a := (-A + u) * (A + R + 2 * M.D) / A + R / 8 + 2 * M.D
    apply finish (fun p => p 1 - c 1) (step5_coord_lipschitz c 1) a
    intro i
    let δ := (2 * (i : ℕ) + 1) * R / 16
    have hδ1 : R / 16 ≤ δ := by fin_cases i <;> simp [δ] <;> linarith
    have hδ2 : δ ≤ 7 * R / 16 := by fin_cases i <;> simp [δ] <;> linarith
    apply emcg_window_side hN hR G hloc j 0 (by norm_num) (by push_cast; linarith)
      (by push_cast; linarith) (-A + u) (by linarith) (by linarith)
      (fun p => p 1 - c 1) id (a + δ) δ hδ1 hδ2 (fun s x => c + mkPt x s)
      (fun _ => continuous_const.add (step5_mkPt_continuous continuous_id continuous_const))
      (fun s x => by simp [mkPt]) (by simp [a, δ, A]) (fun s => rfl)
      (fun s x => Or.inl (by simp [mkPt]))
    · intro s x
      rw [step5_spp0 (t := u) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1, id]
      ring
    · intro s x
      rw [step5_spp0 (t := u + R) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1, id]
      ring
  · let b := (u - 3 * A) * (A + R + 2 * M.D) / A + R / 8 + 2 * M.D
    let a := -b - R / 2
    apply finish (fun p => p 0 - c 0) (step5_coord_lipschitz c 0) a
    intro i
    let d := (2 * (i : ℕ) + 1) * R / 16
    let δ := R / 2 - d
    have hδ1 : R / 16 ≤ δ := by fin_cases i <;> simp [δ, d] <;> linarith
    have hδ2 : δ ≤ 7 * R / 16 := by fin_cases i <;> simp [δ, d] <;> linarith
    apply emcg_window_side hN hR G hloc j 1 (by norm_num) (by push_cast; linarith)
      (by push_cast; linarith) (u - 3 * A) (by linarith) (by linarith)
      (fun p => p 0 - c 0) (fun s => -s) (a + d) δ hδ1 hδ2
      (fun s x => c + mkPt s x)
      (fun _ => continuous_const.add (step5_mkPt_continuous continuous_const continuous_id))
      (fun s x => by simp [mkPt]) (by simp [a, b, δ, d]; ring) (fun s => abs_neg s)
      (fun s x => Or.inr (by simp [mkPt]))
    · intro s x
      rw [step5_spp1 (t := u) (by linarith) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1]
      ring
    · intro s x
      rw [step5_spp1 (t := u + R) (by linarith) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1]
      ring
  · let b := (u - 5 * A) * (A + R + 2 * M.D) / A + R / 8 + 2 * M.D
    let a := -b - R / 2
    apply finish (fun p => p 1 - c 1) (step5_coord_lipschitz c 1) a
    intro i
    let d := (2 * (i : ℕ) + 1) * R / 16
    let δ := R / 2 - d
    have hδ1 : R / 16 ≤ δ := by fin_cases i <;> simp [δ, d] <;> linarith
    have hδ2 : δ ≤ 7 * R / 16 := by fin_cases i <;> simp [δ, d] <;> linarith
    apply emcg_window_side hN hR G hloc j 2 (by norm_num) (by push_cast; linarith)
      (by push_cast; linarith) (u - 5 * A) (by linarith) (by linarith)
      (fun p => p 1 - c 1) (fun s => -s) (a + d) δ hδ1 hδ2
      (fun s x => c + mkPt (-x) s)
      (fun _ => continuous_const.add (step5_mkPt_continuous continuous_neg continuous_const))
      (fun s x => by simp [mkPt]) (by simp [a, b, δ, d]; ring) (fun s => abs_neg s)
      (fun s x => Or.inl (by simp [mkPt]))
    · intro s x
      rw [step5_spp2 hA.le (t := u) (by linarith) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1]
      ring
    · intro s x
      rw [step5_spp2 hA.le (t := u + R) (by linarith) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1]
      ring
  · let a := (u - 7 * A) * (A + R + 2 * M.D) / A + R / 8 + 2 * M.D
    apply finish (fun p => p 0 - c 0) (step5_coord_lipschitz c 0) a
    intro i
    let δ := (2 * (i : ℕ) + 1) * R / 16
    have hδ1 : R / 16 ≤ δ := by fin_cases i <;> simp [δ] <;> linarith
    have hδ2 : δ ≤ 7 * R / 16 := by fin_cases i <;> simp [δ] <;> linarith
    apply emcg_window_side hN hR G hloc j 3 (by norm_num) (by push_cast; linarith)
      (by push_cast; linarith) (u - 7 * A) (by linarith) (by linarith)
      (fun p => p 0 - c 0) id (a + δ) δ hδ1 hδ2 (fun s x => c + mkPt s (-x))
      (fun _ => continuous_const.add (step5_mkPt_continuous continuous_const continuous_neg))
      (fun s x => by simp [mkPt]) (by simp [a, δ, A]) (fun s => rfl)
      (fun s x => Or.inr (by simp [mkPt]))
    · intro s x
      rw [step5_spp3 hA.le (t := u) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1, id]
      ring
    · intro s x
      rw [step5_spp3 hA.le (t := u + R) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1, id]
      ring

/-- the four middle windows of every annular piece contain private outer edges pairwise
separated by R/10, by localization within 20D and R ≥ 10000(K₀+3)D. -/
private lemma existsMacroCertificate_seed1_grouping_step1_windows (M : MeshConstants P)
    {S : Set (PlacedTile P)} (c : Pt) (N : ℕ) (R : ℝ) (G : AnnularGrouping M S c N R)
    (hN : 2 ≤ N) (hR : 10000 * ((M.K0 : ℝ) + 3) * M.D ≤ R)
    (hloc : ∀ j : Fin (4 * N), (G.spokes.piece j).carrier ⊆
      Metric.cthickening (20 * M.D) (idealTrapezoid c N R M.D (j : ℕ))) :
    ∃ e : Fin (4 * N) → Fin 4 → Set Pt,
      (∀ j i, e j i ∈ privateOuterEdges G j) ∧
        ∀ j i j' i', (j, i) ≠ (j', i') →
          ∀ x ∈ e j i, ∀ y ∈ e j' i', R / 10 ≤ dist x y := by
  classical
  have hD := M.D_pos
  have hK : (0 : ℝ) ≤ M.K0 := Nat.cast_nonneg _
  have hR1000 : 1000 * M.D ≤ R := by nlinarith
  have hRpos : 0 < R := by linarith
  have H := fun j => emcg_window_pick c hN hR1000 G hloc j
  choose f hf a e p he hp hfp hfar using H
  refine ⟨e, he, ?_⟩
  intro j i j' i' hne x hx y hy
  have edge_dist {j : Fin (4 * N)} {e : Set Pt} (he : e ∈ privateOuterEdges G j)
      {x y : Pt} (hx : x ∈ e) (hy : y ∈ e) : dist x y ≤ M.D := by
    rcases he.1 with ⟨A, -, k, hk⟩
    exact step5_tile_dist_le M A (tile_side_subset A k (hk ▸ hx))
      (tile_side_subset A k (hk ▸ hy))
  have hpx : dist (p j i) x ≤ M.D := edge_dist (he j i) (hp j i) hx
  have hyp : dist y (p j' i') ≤ M.D := edge_dist (he j' i') hy (hp j' i')
  by_cases hj : j = j'
  · subst j'
    have hii : i ≠ i' := by
      intro h
      exact hne (Prod.ext rfl h)
    have htargets : R / 8 ≤ dist (f j (p j i)) (f j (p j i')) := by
      rw [hfp j i, hfp j i', Real.dist_eq]
      let d := a j + (2 * (i : ℕ) + 1) * R / 16 -
        (a j + (2 * (i' : ℕ) + 1) * R / 16)
      have hdpos : d ≤ |d| := le_abs_self d
      have hdneg : -d ≤ |d| := neg_le_abs d
      fin_cases i
      all_goals fin_cases i'
      all_goals norm_num at hii
      all_goals norm_num [d] at hdpos hdneg ⊢
      all_goals linarith
    have hfx : dist (f j (p j i)) (f j x) ≤ M.D := by
      have h := (hf j).dist_le_mul (p j i) x
      simpa using h.trans (by simpa using hpx)
    have hfy : dist (f j y) (f j (p j i')) ≤ M.D := by
      have h := (hf j).dist_le_mul y (p j i')
      simpa using h.trans (by simpa using hyp)
    have hxy : dist (f j x) (f j y) ≤ dist x y := by
      simpa using (hf j).dist_le_mul x y
    have htri1 := dist_triangle (f j (p j i)) (f j x) (f j (p j i'))
    have htri2 := dist_triangle (f j x) (f j y) (f j (p j i'))
    nlinarith
  · have hyc : y ∈ (G.spokes.piece j').carrier := by
      rcases (he j' i').1 with ⟨A, hA, k, hk⟩
      show y ∈ (G.spokes.piece j').disk.carrier
      rw [(G.spokes.piece j').carrier_eq]
      exact carrier_subset_support hA (tile_side_subset A k (hk ▸ hy))
    have hyT := hloc j' hyc
    rw [Metric.mem_cthickening_iff] at hyT
    have hfarE : ENNReal.ofReal (R / 8) ≤
        Metric.infEDist (p j i) (idealTrapezoid c N R M.D (j' : ℕ)) := by
      rw [Metric.le_infEDist]
      intro q hq
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hfar j i j' (Ne.symm hj) q hq)
    have htri := Metric.infEDist_le_infEDist_add_edist (x := p j i) (y := y)
      (s := idealTrapezoid c N R M.D (j' : ℕ))
    rw [edist_dist] at htri
    have hsum : ENNReal.ofReal (R / 8) ≤
        ENNReal.ofReal (20 * M.D) + ENNReal.ofReal (dist (p j i) y) :=
      hfarE.trans (htri.trans (add_le_add hyT le_rfl))
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 20 * M.D) dist_nonneg] at hsum
    have hpy : R / 8 ≤ 20 * M.D + dist (p j i) y :=
      (ENNReal.ofReal_le_ofReal_iff
        (by positivity : 0 ≤ 20 * M.D + dist (p j i) y)).1 hsum
    have htri' := dist_triangle_left (p j i) y x
    have hxp : dist x (p j i) ≤ M.D := by simpa [dist_comm] using hpx
    nlinarith [hR1000]

/-- Step 1--2 of `lem:certificate-exists`: choose the mesh constants, then `R,Q,N,k`, and
form the finite labelled catalogue consisting of `L`, its `4N` annular pieces, and the remaining
singletons, with scattering/regrouping equal to the `k`-th substitution power. -/
private lemma existsMacroCertificate_seed1_grouping (τ : Substitution P) (h : τ.STS) :
    Nonempty (existsMacroCertificate_GroupingSeed τ) := by
  classical
  let M : MeshConstants P := Classical.choice (MeshConstants.nonempty P)
  obtain ⟨Csep, Cloc, Clen, Cerr, C, hCsep_eq, hCloc_eq, hClen_eq, hCerr_eq, hC_eq,
    hCsep, hCloc, hClen, hCerr, hC, hquant⟩ :=
    quantitativeAnnularGrouping M
  have hD := M.D_pos
  -- the scale `R`
  let R : ℝ := max (max (Csep * M.D) (10000 * ((M.K0 : ℝ) + 3) * M.D))
    (((M.K0 : ℝ) + 3 + Cerr) * Clen * M.D)
  have hR1 : Csep * M.D ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hR2 : 10000 * ((M.K0 : ℝ) + 3) * M.D ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hR3 : ((M.K0 : ℝ) + 3 + Cerr) * Clen * M.D ≤ R := le_max_right _ _
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR2
  have hpriv : (M.K0 : ℝ) + 2 ≤ (⌊R / (Clen * M.D)⌋₊ : ℝ) - Cerr := by
    have hCD : 0 < Clen * M.D := mul_pos hClen hD
    have h1 : (M.K0 : ℝ) + 3 + Cerr ≤ R / (Clen * M.D) := by
      rw [le_div_iff₀ hCD]; linarith
    have h2 := Nat.lt_floor_add_one (R / (Clen * M.D))
    linarith
  -- the bound `Q` and the number `N`
  let Qmax : ℕ := M.K0 * ⌈4 * C ^ 2 * R ^ 2 / M.a⌉₊
  let N : ℕ := Qmax + 2
  -- the power `k` and the centres
  have hW : 0 < (N : ℝ) * R / 2 + R + 10 * M.D := by positivity
  obtain ⟨k, hk, c, hcin, hcsep⟩ := emcg_centres τ hW
  have hθk : τ.θ ^ k ≠ 0 := (pow_pos (zero_lt_one.trans τ.one_lt) _).ne'
  have hmargin : ∀ p, square (c p) ((N : ℝ) * R / 2 + R) + Binf (10 * M.D) ⊆
      interior ((τ.θ ^ k) • (P.disk p).carrier) := fun p =>
    (emcg_square_add_Binf _ _ _).trans (hcin p)
  -- the annular groupings
  have hex : ∀ p, ∃ G : AnnularGrouping M (τ.supertile k p) (c p) N R,
      (∀ j : Fin (4 * N), (G.spokes.piece j).carrier ⊆
          Metric.cthickening (Cloc * M.D) (idealTrapezoid (c p) N R M.D (j : ℕ))) ∧
      (∀ j : Fin (4 * N),
          (⌊R / (Clen * M.D)⌋₊ : ℝ) - Cerr ≤ ((privateOuterEdges G j).ncard : ℝ)) ∧
      (∀ j : Fin (4 * N), Metric.diam (G.spokes.piece j).carrier ≤ C * R) ∧
      (∀ j : Fin (4 * N), (G.spokes.piece j).disk.n ≤ M.K0 * ⌈4 * C ^ 2 * R ^ 2 / M.a⌉₊) :=
    fun p => hquant ((τ.pow k hk).rule p) (emcgScaleDisk (P.disk p) (τ.θ ^ k) hθk)
      ((τ.pow k hk).support_eq p) (h k p) (c p) N R (by omega) hR1 (hmargin p)
  choose Ag hAg using hex
  have hwin : ∀ p, ∃ e : Fin (4 * N) → Fin 4 → Set Pt,
      (∀ j i, e j i ∈ privateOuterEdges (Ag p) j) ∧
        ∀ j i j' i', (j, i) ≠ (j', i') →
          ∀ x ∈ e j i, ∀ y ∈ e j' i', R / 10 ≤ dist x y := by
    intro p
    apply existsMacroCertificate_seed1_grouping_step1_windows M (c p) N R (Ag p)
      (by omega) hR2
    simpa [hCloc_eq] using (hAg p).1
  have hsep : ∀ p q, p ≠ q → Disjoint (square (c p) ((N : ℝ) * R / 2 + R + 3 * M.D))
      (square (c q) ((N : ℝ) * R / 2 + R + 3 * M.D)) := fun p q hpq =>
    (hcsep p q hpq).mono (emcg_square_mono _ (by linarith)) (emcg_square_mono _ (by linarith))
  exact ⟨{
    M := M
    Csep := Csep
    Cloc := Cloc
    Clen := Clen
    Cerr := Cerr
    C := C
    constants_pos := ⟨hCsep, hCloc, hClen, hCerr, hC⟩
    Csep_eq := hCsep_eq
    Cloc_eq := hCloc_eq
    Clen_eq := hClen_eq
    Cerr_eq := hCerr_eq
    C_eq := hC_eq
    R := R
    R_separates := hR1
    R_routes := hR2
    private_edges := hpriv
    Qmax := Qmax
    Qmax_eq := rfl
    N := N
    N_two := by omega
    N_dominates := by omega
    k := k
    k_pos := hk
    centre := c
    square_margin := hmargin
    annular := Ag
    annular_quantitative := hAg
    annular_windows := hwin
    GS := emcgGS τ Ag h hk
    grouped_power := rfl
    ccw := by
      rintro (p | ⟨p, j⟩ | p)
      · exact pdOrientCCW_ccw (Ag p).L.disk
      · exact pdOrientCCW_ccw ((Ag p).spokes.piece j).disk
      · exact pdOrientCCW_ccw (P.disk p)
    large := fun p => Sum.inl p
    large_injective := Sum.inl_injective
    small := fun p j => Sum.inr (Sum.inl (p, j))
    original := fun p => Sum.inr (Sum.inr p)
    large_dissect := fun _ => rfl
    small_dissect := fun _ _ => rfl
    original_dissect := fun _ => rfl
    catalogue := by
      rintro (p | ⟨p, j⟩ | p)
      · exact Or.inl ⟨p, 0, (emcg_translateSet_zero _).symm⟩
      · exact Or.inr (Or.inl ⟨p, j, 0, (emcg_translateSet_zero _).symm⟩)
      · exact Or.inr (Or.inr ⟨p, 0, rfl⟩)
    catalogue_exact := by
      rintro (p | ⟨p, j⟩ | p)
      · exact Or.inl ⟨p, rfl⟩
      · exact Or.inr (Or.inl ⟨p, j, rfl⟩)
      · exact Or.inr (Or.inr ⟨p, rfl⟩)
    catalogue_labels_injective := by
      rintro (p | ⟨p, j⟩ | p) (q | ⟨q, i⟩ | q) h <;> exact h
    inside_supertile := by
      intro α
      obtain ⟨n, p, hsub, -⟩ := emcg_dissect_sub τ k Ag α
      exact ⟨n, p, 0, by rw [emcg_translateSet_zero]; exact hsub⟩
    hereditary := fun hH => emcg_grouped_hereditary (emcgGS τ Ag h hk) hH (emcg_iter_sts τ k Ag h)
    grouped_disks_distinct := emcg_grouped_disks_distinct τ k Ag h hR0.le hsep }⟩

/-- The second choice package in the construction.  Besides the routing power and retained
templates, its equations identify every field of the final certificate with the corresponding
labelled group, retained child, print slot, globally oriented outer list, or routed side list. -/
private structure existsMacroCertificate_RoutingSeed (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) where
  setup : RoutingSetup τ g.M
  setup_grouped : setup.GS = g.GS
  l : ℕ
  l_pos : 0 < l
  central_idempotent : setup.c^[2 * l] = setup.c^[l]
  routing : ∀ α, RoutingData (setup.retained l α) (setup.GS.G.P'.disk α)
    (τ.θ ^ (setup.GS.k * l)) (setup.central l α) (setup.markedSides α)
    ((setup.markedSides (setup.c^[l] α)).map Fin.valEmbedding)
  C : MacroCertificate P
  m : ℕ
  m_eq : m = g.k * l
  represents : C.Represents τ m
  baseForm : C.Q.Form → setup.GS.G.P'.Form
  catalogueTile : C.Q.Form → PlacedTile setup.GS.G.mixed
  disk_carrier : ∀ α, (C.Q.disk α).carrier =
    (pdTranslate (setup.GS.G.mixed.disk (catalogueTile α).form)
      (catalogueTile α).anchor).carrier
  disk_vertexSet : ∀ α, (C.Q.disk α).vertexSet =
    (pdTranslate (setup.GS.G.mixed.disk (catalogueTile α).form)
      (catalogueTile α).anchor).vertexSet
  disk_ccw : ∀ α, pdCCW (C.Q.disk α)
  scatter_eq : ∀ α, (C.Δ α).tiles = setup.GS.G.mixedScatterTile (catalogueTile α)
  originalForm : P.Form → C.Q.Form
  original_tile : ∀ p, catalogueTile (originalForm p) = ⟨Sum.inr p, 0⟩
  original_scatter : ∀ p, (C.Δ (originalForm p)).tiles = {⟨p, 0⟩}
  catalogue_injective : Function.Injective catalogueTile
  grouped_disks_distinct : ∀ α β, C.kind α ≠ .original → C.kind β ≠ .original →
    C.Q.disk α = C.Q.disk β → α = β
  kind_original : ∀ α, C.kind α = .original ↔ ∃ p, (catalogueTile α).form = Sum.inr p
  kind_large : ∀ α, C.kind α = .large ↔
    ∃ β, (catalogueTile α).form = Sum.inl (setup.c^[l] β)
  kind_small : ∀ α, C.kind α = .small ↔
    ∃ β γ X, X ∈ (setup.retained l β).children.tiles ∧ X ≠ setup.central l β ∧
      X.form = Sum.inl γ ∧ (catalogueTile α).form = Sum.inl γ
  templateChild : C.Typ → PlacedTile setup.GS.G.mixed
  child_bijective : ∀ α, Set.BijOn templateChild {t | C.owner t = α}
    (setup.retained l (baseForm α)).children.tiles
  child_carrier : ∀ t, (C.childTile t).carrier = (templateChild t).carrier
  central_child : ∀ α, templateChild (C.central α) = setup.central l (baseForm α)
  central_form : ∀ α, (templateChild (C.central α)).form =
    Sum.inl (setup.c^[l] (baseForm α))
  parentSide : ∀ α, Fin (C.Q.disk α).n → Fin (setup.GS.G.P'.disk (baseForm α)).n
  parentSide_injective : ∀ α, Function.Injective (parentSide α)
  parent_side_geometry : ∀ α d, C.macroSide α d =
    (τ.θ ^ (setup.GS.k * l)) • (setup.GS.G.P'.disk (baseForm α)).side (parentSide α d)
  marked_from_setup : ∀ α d, C.marked α d ↔ parentSide α d ∈ setup.markedSides (baseForm α)
  marked_rule_nonlarge : ∀ o : C.SideOcc,
    C.kind (C.form o.1) ≠ .large ∨ C.IsPrint o → C.IsMarked o
  marked_rule_large : ∀ o : C.SideOcc, C.kind (C.owner o.1) = .large →
    C.kind (C.form o.1) = .large → C.IsMarked o → C.IsPrint o
  positive_eq : C.IsPositive = LexPositive
  outerList_global : ∀ α d, (C.outerList α d).Nodup ∧
    (C.outerList α d).Pairwise fun o o' =>
      ∃ r : ℝ, 0 < r ∧ C.occMid o' - C.occMid o = r • C.macroSideDir α d
  print_from_routing : ∀ α d, C.occSide (C.printOcc α d) =
    (setup.central l (baseForm α)).side ((routing (baseForm α)).printIdx (parentSide α d))
  special_contact : ∀ o : C.SideOcc, C.special o →
    C.IsInner o ∧ (C.partner o).1 = C.central (C.owner o.1)
  path_from_routing : ∀ α d (i : Fin 4), C.marked α d →
    @List.destutter (Set Pt) (· ≠ ·) (Classical.decRel _)
      ((C.path α d i.castSucc).map C.occSide) =
      (routing (baseForm α)).pathSides (parentSide α d) i
  fifth_path : ∀ α d, C.path α d (4 : Fin 5) = (C.port α d (4 : Fin 5)).toList
  N_eq : C.N = g.N
  Qmax_eq : C.Qmax = g.Qmax
  rankBound_is_max : ∀ b, (∀ α d, (C.outerList α d).length ≤ b) → C.rankBound ≤ b

/-- The grouped-family, substitution-compatibility and representation output of Step 1 of
`lem:certificate-exists`: "Keep the finite labelled groups in `P'` ... Scattering a group and
applying the grouped substitution ... gives `Δσ = τ^kΔ`." -/
private structure existsMacroCertificate_RepresentationData (τ : Substitution P) (m : ℕ)
    (D : MacroData P) : Prop where
  m_pos : 0 < m
  θ_eq : D.σ.θ = τ.θ ^ m
  compat : ∀ _α, (⋃ A ∈ (D.σ.rule _α).tiles, translateSet A.anchor (D.Δ A.form).tiles) =
    τ.decomposeIter m (D.Δ _α).tiles
  scatter_support : ∀ _α, support (D.Δ _α).tiles = (D.Q.disk _α).carrier
  sts : ∀ _α, SideToSideSet (D.Δ _α).tiles
  dualConnected : ∀ _α, DualConnected (D.Δ _α).tiles
  side_whole : ∀ _α (_i : Fin (D.Q.disk _α).n),
    ∃ _A ∈ (D.Δ _α).tiles, HasEdge _A ((D.Q.disk _α).side _i)
  vertex_retained : ∀ _α _v, Substitution.IsVertexOf (D.Δ _α).tiles _v →
    _v ∈ frontier (D.Q.disk _α).carrier → _v ∈ (D.Q.disk _α).vertexSet
  singleton : ∀ _p : P.Form, ∃ _α, (D.Δ _α).tiles = {⟨_p, 0⟩}
  inside_supertile : ∀ _α, ∃ (_n : ℕ) (_p : P.Form) (_v : Pt),
    translateSet _v (D.Δ _α).tiles ⊆ τ.supertile _n _p
  hereditary : τ.HereditarySides → D.Hereditary

/-- The template preamble of the blueprint construction, separated from (G1): the positioned
types are exactly the children of the retained/scattered rule and every such template is STS. -/
private structure existsMacroCertificate_TemplateData (D : MacroData P) : Prop where
  rule_eq : ∀ _α, (D.σ.rule _α).tiles =
    (fun _t => (⟨D.form _t, D.anchor _t⟩ : PlacedTile D.Q)) '' {_t | D.owner _t = _α}
  type_injective : ∀ _t _t', D.owner _t = D.owner _t' → D.form _t = D.form _t' →
    D.anchor _t = D.anchor _t' → _t = _t'
  template_sts : ∀ _α, SideToSideSet (D.σ.rule _α).tiles

/-- The (G1) output of Step 3 of `lem:certificate-exists`: disk cellulations with the retained
centre and ring have connected inner-side dual graphs, at least three children, and the usual
unique two-owner interface data. -/
private structure existsMacroCertificate_G1Data (D : MacroData P) : Prop where
  connected : ∀ _α, (D.innerGraph _α).Connected
  three_le : ∀ _α, 3 ≤ Nat.card {_t : D.Typ // D.owner _t = _α}
  inner_side : ∀ _t, ∃ _i, D.IsInner (D.occ _t _i)
  partner : ∀ _o : D.SideOcc, D.IsInner _o →
    (D.partner _o).1 ≠ _o.1 ∧ D.owner (D.partner _o).1 = D.owner _o.1 ∧
      D.occSide (D.partner _o) = D.occSide _o
  partner_partner : ∀ _o : D.SideOcc, D.IsInner _o → D.partner (D.partner _o) = _o
  side_unique : ∀ _o _o' : D.SideOcc, D.IsInner _o → D.owner _o'.1 = D.owner _o.1 →
    _o'.1 ≠ _o.1 → D.occSide _o' = D.occSide _o → _o' = D.partner _o
  edge_partner : ∀ _o : D.SideOcc, D.IsInner _o → D.edge (D.partner _o) = D.edge _o
  edge_unique : ∀ _o _o' : D.SideOcc, D.IsInner _o → D.IsInner _o' →
    D.edge _o = D.edge _o' → _o' = _o ∨ _o' = D.partner _o
  edgeTypes : ∀ _o : D.SideOcc, D.IsInner _o →
    D.edgeTypes (D.edge _o) = (_o.1, (D.partner _o).1) ∨
      D.edgeTypes (D.edge _o) = ((D.partner _o).1, _o.1)

/-- The (G2) output of Step 4 of `lem:certificate-exists`: the boundary fan argument connects
the belt, gives every belt type a boundary side, and the retained centre is strictly interior. -/
private structure existsMacroCertificate_G2Data (D : MacroData P) : Prop where
  belt_connected : ∀ _α, (D.beltGraph _α).Connected
  belt_edge : ∀ _t, D.IsBeltType (D.owner _t) _t → ∃ _i, D.IsBoundary (D.occ _t _i)
  central : ∀ _α _i, ¬ D.IsOuter (D.occ (D.central _α) _i) ∧
    ¬ D.IsBoundary (D.occ (D.central _α) _i)

/-- The (G3) output of Step 5 of `lem:certificate-exists`: the finite boundary intersections
give globally oriented, sorted, bounded outer-side lists with at most two endpoint crossings and
five whole sides available for ports. -/
private structure existsMacroCertificate_G3Data (D : MacroData P) : Prop where
  pos_iff : ∀ _v : Pt, _v ≠ 0 → (D.IsPositive _v ↔ ¬ D.IsPositive (-_v))
  pos_smul : ∀ (_v : Pt) (_r : ℝ), 0 < _r → D.IsPositive _v → D.IsPositive (_r • _v)
  outerList_mem : ∀ _α (_d : Fin (D.Q.disk _α).n) (_o : D.SideOcc),
    _o ∈ D.outerList _α _d ↔ D.owner _o.1 = _α ∧ D.IsOuter _o ∧
      D.occSide _o ⊆ D.macroSide _α _d
  outerList_nodup : ∀ _α _d, (D.outerList _α _d).Nodup
  outerList_sorted : ∀ _α _d, (D.outerList _α _d).Pairwise fun _o _o' =>
    ∃ _r : ℝ, 0 < _r ∧ D.occMid _o' - D.occMid _o = _r • D.macroSideDir _α _d
  crossing_le_two : ∀ _α (_d : Fin (D.Q.disk _α).n),
    Set.ncard {_o : D.SideOcc | D.owner _o.1 = _α ∧ D.IsOuter _o ∧
      OverlapPos (D.occSide _o) (D.macroSide _α _d) ∧
      ¬ D.occSide _o ⊆ D.macroSide _α _d} ≤ 2
  five_le : ∀ _α _d, 5 ≤ (D.outerList _α _d).length
  length_le : ∀ _α _d, (D.outerList _α _d).length ≤ D.rankBound

/-- The (G4) output of Step 6 of `lem:certificate-exists`: `lem:routing` is converted from
geometric side paths to side occurrences, including both occurrences of crossed inner sides,
the small-owner terminal print, and the global no-sharing clauses. -/
private structure existsMacroCertificate_G4Data (D : MacroData P) : Prop where
  print_injective : ∀ _α (_d _d' : Fin (D.Q.disk _α).n), D.marked _α _d → D.marked _α _d' →
    D.print _α _d = D.print _α _d' → _d = _d'
  print_cyclic : ∀ _α (_a _b _e : Fin (D.Q.disk _α).n), D.marked _α _a → D.marked _α _b →
    D.marked _α _e → CycLt3 _a _b _e → CycLt3 (D.print _α _a) (D.print _α _b) (D.print _α _e)
  print_inner : ∀ _α _d, D.marked _α _d → D.IsInner (D.printOcc _α _d)
  print_small : ∀ _α _d, D.marked _α _d →
    D.kind (D.form (D.partner (D.printOcc _α _d)).1) = .small
  print_special : ∀ _α _d, D.marked _α _d → D.special (D.partner (D.printOcc _α _d))
  path_head : ∀ _α _d _i, D.IsGenuinePath _α _d _i →
    (D.path _α _d _i).head? = D.port _α _d _i
  path_last : ∀ _α _d _i, D.IsGenuinePath _α _d _i →
    (D.path _α _d _i).getLast? = some (D.partner (D.printOcc _α _d))
  path_chain : ∀ _α _d _i (_n : ℕ) (_o _o' : D.SideOcc),
    (D.path _α _d _i)[_n]? = some _o → (D.path _α _d _i)[_n + 1]? = some _o' →
      _o.1 = _o'.1 ∨ (D.IsInner _o ∧ _o' = D.partner _o)
  path_owner : ∀ _α _d _i (_o : D.SideOcc), _o ∈ D.path _α _d _i → D.owner _o.1 = _α
  path_inner : ∀ _α _d _i, D.IsGenuinePath _α _d _i →
    ∀ (_n : ℕ) (_o : D.SideOcc), (D.path _α _d _i)[_n + 1]? = some _o → D.IsInner _o
  path_partner : ∀ _α _d _i, D.IsGenuinePath _α _d _i →
    ∀ _o ∈ D.path _α _d _i, D.IsInner _o → ¬ D.IsPrint _o → D.partner _o ∈ D.path _α _d _i
  path_marked : ∀ _α _d _i, D.IsGenuinePath _α _d _i →
    ∀ _o ∈ D.path _α _d _i, D.IsMarked _o
  path_not_central : ∀ _α _d _i, D.IsGenuinePath _α _d _i →
    ∀ _o ∈ D.path _α _d _i, _o.1 ≠ D.central _α
  path_penultimate : ∀ _α _d _i, D.IsGenuinePath _α _d _i →
    ∀ _o : D.SideOcc, (D.path _α _d _i)[(D.path _α _d _i).length - 2]? = some _o →
      _o.1 = (D.partner (D.printOcc _α _d)).1 ∧ D.IsOrdinary _o
  path_trivial : ∀ _α _d _i, ¬ D.IsGenuinePath _α _d _i →
    D.path _α _d _i = (D.port _α _d _i).toList
  path_nodup : ∀ _α _d _i, (D.path _α _d _i).Nodup
  path_disjoint : ∀ _α (_d _d' : Fin (D.Q.disk _α).n) (_i _i' : Fin 5),
    (_d, _i) ≠ (_d', _i') → ∀ _o, _o ∈ D.path _α _d _i → _o ∈ D.path _α _d' _i' →
      _d = _d' ∧ (_o = D.printOcc _α _d ∨ _o = D.partner (D.printOcc _α _d))

/-- The (G5) output of Step 7 of `lem:certificate-exists`: idempotence fixes retained large
central forms; the annular ring has `4N` marked sides and dominates the noncentral bound. -/
private structure existsMacroCertificate_G5Data (D : MacroData P) : Prop where
  central_owner : ∀ _α, D.owner (D.central _α) = _α
  large_iff : ∀ _t, D.kind (D.form _t) = .large ↔ _t = D.central (D.owner _t)
  central_fixes_large : ∀ _α, D.kind _α = .large → D.form (D.central _α) = _α
  print_id_large : ∀ _α _d, D.kind _α = .large → D.marked _α _d →
    (D.print _α _d).val = _d.val
  card_marked_large : ∀ _α, D.kind _α = .large →
    Nat.card {_d // D.marked _α _d} = 4 * D.N
  card_marked_small : ∀ _α, D.kind _α ≠ .large →
    Nat.card {_d // D.marked _α _d} ≤ D.Qmax
  three_Q_lt : 3 * D.Qmax < 4 * D.N
  original_marked : ∀ _t, D.kind (D.form _t) = .original →
    ∃ _i, D.IsInner (D.occ _t _i) ∧ D.IsMarked (D.occ _t _i)

/-- The (G6) output of Step 8 of `lem:certificate-exists`: prints are the unique inner special
sides of small types, and the private-neighbour estimate feeds `fingerprintSeparation`. -/
private structure existsMacroCertificate_G6Data (D : MacroData P) : Prop where
  special_small : ∀ _o : D.SideOcc, D.special _o → D.kind (D.form _o.1) = .small
  special_unique : ∀ _t, D.kind (D.form _t) = .small → ∃! _i, D.special (D.occ _t _i)
  special_inner : ∀ _o : D.SideOcc, D.special _o → D.IsInner _o
  fingerprint : ∀ _t _t', _t ≠ _t' → ¬ D.IsCentral _t → ¬ D.IsCentral _t' →
    Disjoint (D.possibleFingerprints _t) (D.possibleFingerprints _t')

/-- The (G7) output of Step 9 of `lem:certificate-exists`: "every side not belonging to the
large central group, plus the prints" is marked, hence all outer, boundary, print and genuine
path occurrences satisfy the marking discipline. -/
private structure existsMacroCertificate_G7Data (D : MacroData P) : Prop where
  marking : ∀ _o : D.SideOcc,
    (D.IsOuter _o ∨ D.IsBoundary _o ∨ D.IsPrint _o ∨ D.OnGenuinePath _o) → D.IsMarked _o

/-! ### Decomposition of `existsMacroCertificate_seed2_routing` (hand decomposition, 16 October 2026)

The routing seed is assembled from three construction stages, mirroring Steps 3--9 of
`lem:certificate-exists`: the routing setup over the grouping seed (`SetupSeed`, Step 3), the
idempotent routed power (`existsRoutingAfterPower`), and the finite certificate data with its
definitional equations (`CertData`, Step 4), from which the seven properties (G1)--(G7) are proved
one by one (Steps 5--11).  Every structure pins its objects to the previous stage, so that each
existence lemma is a statement about the blueprint's construction and not about arbitrary data. -/

/-- Step 3 of `lem:certificate-exists`: the `RoutingSetup` of the blueprint over the grouping
seed `g`.  Its fields are pinned to the catalogue of `g`: `N` and `R` are the chosen constants,
the central-form map `c` takes values in the large catalogue forms `L_p`, the retained annulus of
every template at every power is a translate of one catalogue annulus `(g.annular p)` (the central
child scatters to the translated `L_p`, the `j`-th retained piece to the translated `j`-th
annular piece), every side of an annular piece and of a singleton group is marked, and a large form `L_p` has exactly `4N`
marked sides, each the side it shares with one annular piece, distinct pieces for distinct marked
sides.  The quantitative fields of the setup (clearance, windows, print slots) are those of
`RoutingSetup`; they follow from `g.square_margin`, `g.annular_windows` and the cyclic order of the
marked sides and of the pieces. -/
private structure existsMacroCertificate_SetupSeed (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) where
  setup : RoutingSetup τ g.M
  setup_grouped : setup.GS = g.GS
  N_eq : ∀ α, setup.N α = g.N
  R_eq : ∀ α, setup.R α = g.R
  /-- the central-form map takes values in the large catalogue forms -/
  central_large : ∀ α, ∃ p : P.Form, (setup.GS.G.dissect (setup.c α)).tiles = (g.annular p).L.faces
  /-- the retained annulus of every template is a translate of one catalogue annulus -/
  annulus_catalogue : ∀ l α (hl : 0 < l), ∃ (p : P.Form) (v : Pt),
    setup.GS.G.mixedScatterTile (setup.central l α) = translateSet v (g.annular p).L.faces ∧
    ∀ j : Fin (4 * setup.N α), ∃ j' : Fin (4 * g.N), (j : ℕ) = j' ∧
      ((setup.annulus l α hl).spokes.piece j).faces =
        translateSet v ((g.annular p).spokes.piece j').faces
  /-- every side of the form of a non-central grouped child of a retained template (an annular
  piece) and of a singleton group is marked.  (Repair of 17 October 2026 after Aristotle: the earlier
  clause marked every side of every form that is not a central image, which `GroupingSeed.catalogue`
  allows to be a translated copy of a large group with more than `4N` sides, so that no print slots
  could exist for it; forms that never occur as children are left unconstrained.) -/
  marked_child : ∀ l α (_hl : 0 < l), ∀ X ∈ (setup.retained l α).children.tiles,
    X ≠ setup.central l α → ∀ γ, X.form = Sum.inl γ → setup.markedSides γ = Finset.univ
  marked_singleton : ∀ α (p : P.Form), (setup.GS.G.dissect α).tiles = {⟨p, 0⟩} →
    setup.markedSides α = Finset.univ
  /-- a large form (a central image) has exactly `4N` marked sides -/
  marked_large_card : ∀ β, (setup.markedSides (setup.c β)).card = 4 * g.N
  /-- the marked sides of a large form `L_p` are sides shared with distinct annular pieces -/
  marked_large_contact : ∀ β, ∃ (p : P.Form)
      (piece : Fin (setup.GS.G.P'.disk (setup.c β)).n → Fin (4 * g.N)),
    (setup.GS.G.dissect (setup.c β)).tiles = (g.annular p).L.faces ∧
    Set.InjOn piece (setup.markedSides (setup.c β) : Set _) ∧
    ∀ a ∈ setup.markedSides (setup.c β),
      (setup.GS.G.P'.disk (setup.c β)).side a ⊆ support ((g.annular p).spokes.piece (piece a)).faces
  /-- a non-central child of a retained template never has a central-image form (it is an annular
  piece or an original tile) -/
  noncentral_not_large : ∀ l α (_hl : 0 < l), ∀ X ∈ (setup.retained l α).children.tiles,
    X ≠ setup.central l α → ∀ β, X.form ≠ Sum.inl (setup.c β)
  /-- the form of a non-central grouped child of a retained template (an annular piece) has at
  most `Q` listed sides (`lem:quantitative-sector`); a singleton group has at most `K₀ ≤ Q`.
  (Repair of 17 October 2026 after Aristotle: the earlier clause quantified over every form that is
  not a central image, which `GroupingSeed.catalogue` allows to be a translated copy of a large
  group.) -/
  sides_le_Qmax_child : ∀ l α (_hl : 0 < l), ∀ X ∈ (setup.retained l α).children.tiles,
    X ≠ setup.central l α → ∀ γ, X.form = Sum.inl γ → (setup.GS.G.P'.disk γ).n ≤ g.Qmax
  sides_le_Qmax_singleton : ∀ α (p : P.Form), (setup.GS.G.dissect α).tiles = {⟨p, 0⟩} →
    (setup.GS.G.P'.disk α).n ≤ g.Qmax

/-- Step 3 of `lem:certificate-exists`: "Inside any `σ`-template, fix a constituent original tile
`q₀` of the parent and let the central child be the retained large group `L_{q₀}` of `τ^k(q₀)`."
Every grouped form has a nonempty dissection into original tiles, and iterating the choice of a
constituent tile and its large group defines the central-form map `c`, the central child anchors,
and the inclusion of each central supertile in the iterated decomposition of the parent. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub1_central_chain
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ) :
    ∃ (q₀ : g.GS.G.P'.Form → PlacedTile P) (anchor : ℕ → g.GS.G.P'.Form → Pt),
      (∀ α, q₀ α ∈ (g.GS.G.dissect α).tiles) ∧
      (∀ α, anchor 0 α = 0) ∧
      (∀ m α, anchor (m + 1) α =
        (τ.θ ^ g.k) • (anchor m α + (q₀ ((fun β => g.large (q₀ β).form)^[m] α)).anchor)) ∧
      (∀ l α, translateSet (anchor l α)
        (g.GS.G.dissect ((fun β => g.large (q₀ β).form)^[l] α)).tiles ⊆
        τ.decomposeIter (g.GS.k * l) (g.GS.G.dissect α).tiles) ∧
      ∀ m α, translateSet (anchor (m + 1) α)
        (τ.supertile g.k (q₀ ((fun β => g.large (q₀ β).form)^[m] α)).form) ⊆
        τ.decomposeIter (g.GS.k * (m + 1)) (g.GS.G.dissect α).tiles := by
  classical
  have hnonempty : ∀ α, (g.GS.G.dissect α).tiles.Nonempty := by
    intro α
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hsupp : support (g.GS.G.dissect α).tiles = ∅ := by
      ext x
      simp [support, hne]
    have hcar : (g.GS.G.P'.disk α).carrier = ∅ := by
      rw [← g.GS.G.support_eq α, hsupp]
    obtain ⟨x, hx⟩ := (g.GS.G.P'.disk α).interior_nonempty
    have hx' : x ∈ (g.GS.G.P'.disk α).carrier := interior_subset hx
    rw [hcar] at hx'
    exact hx'
  let q₀ : g.GS.G.P'.Form → PlacedTile P :=
    fun α => Classical.choose (hnonempty α)
  have hq₀ : ∀ α, q₀ α ∈ (g.GS.G.dissect α).tiles := by
    intro α
    exact Classical.choose_spec (hnonempty α)
  let c : g.GS.G.P'.Form → g.GS.G.P'.Form :=
    fun β => g.large (q₀ β).form
  let anchor : ℕ → g.GS.G.P'.Form → Pt :=
    fun m => Nat.rec (motive := fun _ => g.GS.G.P'.Form → Pt)
      (fun _ => 0)
      (fun m ih α =>
        (τ.θ ^ g.k) • (ih α + (q₀ (c^[m] α)).anchor)) m
  have hlarge : ∀ q : PlacedTile P,
      translateSet ((τ.θ ^ g.k) • q.anchor)
          (g.GS.G.dissect (g.large q.form)).tiles ⊆
        τ.decomposeIter g.k {q} := by
    intro q
    rw [g.large_dissect, emcg_iter_singleton]
    exact image_mono (g.annular q.form).L.faces_sub
  have hchain : ∀ l α, translateSet (anchor l α)
      (g.GS.G.dissect (c^[l] α)).tiles ⊆
        τ.decomposeIter (g.k * l) (g.GS.G.dissect α).tiles := by
    intro l
    induction l with
    | zero =>
        intro α
        simp [anchor, Substitution.decomposeIter, emcg_translateSet_zero]
    | succ m ih =>
        intro α
        let β := c^[m] α
        let q := q₀ β
        have hq : q ∈ (g.GS.G.dissect β).tiles := hq₀ β
        have hanchor : anchor (m + 1) α =
            (τ.θ ^ g.k) • (anchor m α + q.anchor) := by
          dsimp [anchor, q, β]
        have hc : c^[m + 1] α = c β := by
          simp [Function.iterate_succ_apply', β]
        have hmid : translateSet ((τ.θ ^ g.k) • anchor m α)
            (τ.decomposeIter g.k {q}) ⊆
              τ.decomposeIter g.k
                (translateSet (anchor m α) (g.GS.G.dissect β).tiles) := by
          rw [emcg_iter_translate]
          exact image_mono (emcg_iter_mono τ g.k (singleton_subset_iff.mpr hq))
        have hnext : translateSet (anchor (m + 1) α)
            (g.GS.G.dissect (c^[m + 1] α)).tiles ⊆
              translateSet ((τ.θ ^ g.k) • anchor m α)
                (τ.decomposeIter g.k {q}) := by
          rw [hanchor, hc, smul_add]
          rw [← emcg_translateSet_translateSet]
          exact image_mono (hlarge q)
        calc
          translateSet (anchor (m + 1) α)
              (g.GS.G.dissect (c^[m + 1] α)).tiles ⊆
              τ.decomposeIter g.k
                (translateSet (anchor m α) (g.GS.G.dissect β).tiles) :=
            hnext.trans hmid
          _ ⊆ τ.decomposeIter g.k
                (τ.decomposeIter (g.k * m) (g.GS.G.dissect α).tiles) :=
            emcg_iter_mono τ g.k (ih α)
          _ = τ.decomposeIter (g.k * (m + 1))
                (g.GS.G.dissect α).tiles := by
            rw [emcg_iter_add, Nat.mul_succ]
  refine ⟨q₀, anchor, hq₀, ?_, ?_, ?_, ?_⟩
  · intro α
    dsimp [anchor]
  · intro m α
    dsimp [anchor, c]
  · intro l α
    simpa [c, g.grouped_power] using hchain l α
  · intro m α
    let β := c^[m] α
    let q := q₀ β
    have hanchor : anchor (m + 1) α =
        (τ.θ ^ g.k) • (anchor m α + q.anchor) := by
      dsimp [anchor, q, β]
    have hmid : translateSet ((τ.θ ^ g.k) • anchor m α)
        (τ.decomposeIter g.k {q}) ⊆
          τ.decomposeIter g.k
            (translateSet (anchor m α) (g.GS.G.dissect β).tiles) := by
      rw [emcg_iter_translate]
      exact image_mono (emcg_iter_mono τ g.k
        (singleton_subset_iff.mpr (hq₀ β)))
    have hnext : translateSet (anchor (m + 1) α)
        (τ.supertile g.k q.form) ⊆
          translateSet ((τ.θ ^ g.k) • anchor m α)
            (τ.decomposeIter g.k {q}) := by
      rw [hanchor, smul_add]
      rw [← emcg_translateSet_translateSet, emcg_iter_singleton]
    calc
      translateSet (anchor (m + 1) α)
          (τ.supertile g.k q.form) ⊆
          τ.decomposeIter g.k
            (translateSet (anchor m α) (g.GS.G.dissect β).tiles) :=
        hnext.trans hmid
      _ ⊆ τ.decomposeIter g.k
            (τ.decomposeIter (g.k * m) (g.GS.G.dissect α).tiles) :=
        emcg_iter_mono τ g.k (hchain m α)
      _ = τ.decomposeIter (g.GS.k * (m + 1))
            (g.GS.G.dissect α).tiles := by
        rw [emcg_iter_add, g.grouped_power, Nat.mul_succ]

private noncomputable def emcsCentralTile (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) : g.GS.G.P'.Form → PlacedTile P :=
  (existsMacroCertificate_seed2_routing_step1_setup_sub1_central_chain τ g).choose

private noncomputable def emcsCentralAnchor (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) : ℕ → g.GS.G.P'.Form → Pt :=
  (existsMacroCertificate_seed2_routing_step1_setup_sub1_central_chain τ g).choose_spec.choose

private noncomputable def emcsCentralForm (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (α : g.GS.G.P'.Form) : g.GS.G.P'.Form :=
  g.large (emcsCentralTile τ g α).form

private noncomputable def emcsCentralPlaced (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (l : ℕ) (α : g.GS.G.P'.Form) :
    PlacedTile g.GS.G.mixed :=
  ⟨Sum.inl ((emcsCentralForm τ g)^[l] α), emcsCentralAnchor τ g l α⟩

private noncomputable def emcsCentre (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) : ℕ → g.GS.G.P'.Form → Pt
  | 0, _ => 0
  | m + 1, α =>
    emcsCentralAnchor τ g (m + 1) α +
      g.centre (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form

/-- The retained template and its annulus are chosen together.  The final equation
  records the actual central-chain constituent and translation, so later contact-slot
  choices refer to the same labelled annular pieces. -/
private def emcsAnnulusSpec (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ)
    (retained : ℕ → g.GS.G.P'.Form → Template g.GS.G.mixed)
    (annulus : ∀ l α, 0 < l →
        AnnularGrouping g.M (g.GS.G.mixedScatter (retained l α).children.tiles)
          (emcsCentre τ g l α) g.N g.R) : Prop :=
  ((∀ l α (_hl : 0 < l),
        square (emcsCentre τ g l α) ((g.N : ℝ) * g.R / 2 + g.R) + Binf (10 * g.M.D) ⊆
          interior (retained l α).region) ∧
      (∀ l α (hl : 0 < l),
        g.GS.G.mixedScatterTile (emcsCentralPlaced τ g l α) = (annulus l α hl).L.faces) ∧
      (∀ l α (hl : 0 < l), ∀ X ∈ (retained l α).children.tiles,
        X ≠ emcsCentralPlaced τ g l α → (∃ β, X.form = Sum.inl β) →
          ∃ j : Fin (4 * g.N),
            g.GS.G.mixedScatterTile X = ((annulus l α hl).spokes.piece j).faces) ∧
      (∀ l α (hl : 0 < l) (j : Fin (4 * g.N)),
        ∃ X ∈ (retained l α).children.tiles, X ≠ emcsCentralPlaced τ g l α ∧
          g.GS.G.mixedScatterTile X = ((annulus l α hl).spokes.piece j).faces) ∧
      (∀ l α (hl : 0 < l) (j : Fin (4 * g.N)),
        ((annulus l α hl).spokes.piece j).carrier ⊆
          Metric.cthickening (20 * g.M.D)
            (idealTrapezoid (emcsCentre τ g l α) g.N g.R g.M.D (j : ℕ))) ∧
      (∀ l α (hl : 0 < l), ∃ e : Fin (4 * g.N) → Fin 4 → Set Pt,
        (∀ j i, e j i ∈ privateOuterEdges (annulus l α hl) j) ∧
          ∀ j i j' i', (j, i) ≠ (j', i') →
            ∀ x ∈ e j i, ∀ y ∈ e j' i', g.R / 10 ≤ dist x y) ∧
      ∀ l α (hl : 0 < l), ∃ (p : P.Form) (v : Pt),
        g.GS.G.mixedScatterTile (emcsCentralPlaced τ g l α) =
          translateSet v (g.annular p).L.faces ∧
        ∀ j : Fin (4 * g.N), ∃ j' : Fin (4 * g.N), (j : ℕ) = j' ∧
          ((annulus l α hl).spokes.piece j).faces =
            translateSet v ((g.annular p).spokes.piece j').faces) ∧
  ∀ m α (j : Fin (4 * g.N)),
    ((annulus (m + 1) α (Nat.succ_pos m)).spokes.piece j).faces =
      translateSet (emcsCentralAnchor τ g (m + 1) α)
        ((g.annular
          (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form).spokes.piece j).faces


/-! ### Helpers for `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates` -/

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"Its annulus is a translate of the catalogue annulus of one original supertile" -- squares
translate. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_square_vadd (v c : Pt) (r : ℝ) : v +ᵥ square c r = square (v + c) r := by
  ext x
  simp only [mem_vadd_set, square, mem_setOf_eq, vadd_eq_add]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [PiLp.add_apply, add_sub_add_left_eq_sub] using hy
  · intro hx
    refine ⟨x - v, ?_, by abel⟩
    simpa [PiLp.sub_apply, sub_sub, add_comm] using hx

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"Its annulus is a translate of the catalogue annulus" -- translation commutes with Minkowski
sums. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_vadd_add (v : Pt) (X Y : Set Pt) : (v +ᵥ X) + Y = v +ᵥ (X + Y) := by
  ext x
  simp only [mem_add, mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by abel⟩
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨v + a, ⟨a, ha, rfl⟩, b, hb, by abel⟩

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
the sides of a translated polygonal disk are the translated sides. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_pd_side (B : PolygonalDisk) (v : Pt) (i : Fin B.n) :
    (pdTranslate B v).side i = v +ᵥ B.side i := by
  simp only [PolygonalDisk.side, pdTranslate, vadd_segment]

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
listed sides of placed tiles translate. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_hasEdge_translate {Q : Protoset} {A : PlacedTile Q} {e : Set Pt} (v : Pt)
    (h : HasEdge A e) : HasEdge (A.translate v) (v +ᵥ e) := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨i, emcg_translate_side A v i⟩

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
listed sides of placed tiles translate back. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_hasEdge_translate_iff {Q : Protoset} {A : PlacedTile Q} {e : Set
    Pt} (v : Pt) :
    HasEdge (A.translate v) (v +ᵥ e) ↔ HasEdge A e := by
  refine ⟨fun ⟨i, hi⟩ => ⟨i, ?_⟩, existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_hasEdge_translate v⟩
  rw [emcg_translate_side] at hi
  exact (vadd_left_cancel_iff v).1 hi

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
shared sides translate. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_sharesSide_translate {Q : Protoset} {A B : PlacedTile Q} (v : Pt)
    (h : SharesSide A B) : SharesSide (A.translate v) (B.translate v) := by
  obtain ⟨hne, e, hA, hB⟩ := h
  exact ⟨fun h' => hne (emcg_translate_injective v h'), v +ᵥ e, existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_hasEdge_translate v hA,
    existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_hasEdge_translate v hB⟩

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
vertices of a translated tile. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_vertexSet_translate {Q : Protoset} (A : PlacedTile Q) (v : Pt) :
    (A.translate v).vertexSet = v +ᵥ A.vertexSet := by
  ext x
  simp only [PlacedTile.vertexSet, mem_range, mem_vadd_set]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨A.vertex i, ⟨i, rfl⟩, by rw [emcg_translate_vertex]; rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by rw [emcg_translate_vertex]; rfl⟩

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"Its annulus is a translate of the catalogue annulus of one original supertile" -- a face group of
`S` translates to a face group of any `S'` containing the translate of `S`, provided the vertices of
`S'` on the translated region are vertices of the translate of `S`. -/
private def existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_faceGroup {S S' : Set (PlacedTile P)} (F : FaceGroup S) (v : Pt)
    (hsub : translateSet v S ⊆ S')
    (hV : ∀ w, Substitution.IsVertexOf S' w → w ∈ v +ᵥ F.carrier →
      Substitution.IsVertexOf (translateSet v S) w) : FaceGroup S' where
  faces := translateSet v F.faces
  faces_sub := (image_mono F.faces_sub).trans hsub
  finite := F.finite.image _
  disk := pdTranslate F.disk v
  carrier_eq := by
    show v +ᵥ F.disk.carrier = _
    rw [F.carrier_eq, emcg_support_translateSet]
  side_whole := by
    intro i
    obtain ⟨A, hA, he⟩ := F.side_whole i
    refine ⟨A.translate v, ⟨A, hA, rfl⟩, ?_⟩
    rw [existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_pd_side]
    exact existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_hasEdge_translate v he
  vertex_retained := by
    intro w hw hfr
    have hcl : IsClosed (pdTranslate F.disk v).carrier := (pdTranslate F.disk v).compact.isClosed
    have hwc : w ∈ v +ᵥ F.carrier := hcl.frontier_subset hfr
    obtain ⟨B, hB, hwB⟩ := hV w hw hwc
    obtain ⟨A, hA, rfl⟩ := hB
    rw [existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_vertexSet_translate] at hwB
    obtain ⟨u, hu, rfl⟩ := hwB
    have hfr' : u ∈ frontier F.disk.carrier := by
      have : frontier (pdTranslate F.disk v).carrier = v +ᵥ frontier F.disk.carrier := by
        show frontier (v +ᵥ F.disk.carrier) = _
        rw [frontier, closure_vadd, interior_vadd, ← Set.vadd_set_sdiff]; rfl
      rw [this] at hfr
      obtain ⟨u', hu', he⟩ := hfr
      rwa [← (vadd_left_cancel_iff v).1 he]
    have := F.vertex_retained u ⟨A, hA, hu⟩ hfr'
    obtain ⟨i, hi⟩ := this
    exact ⟨i, by simp only [pdTranslate]; rw [hi]⟩
  dualConnected := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    refine Relation.ReflTransGen.lift (fun X => X.translate v) ?_ (F.dualConnected A hA B hB)
    rintro X Y ⟨hX, hY, hXY⟩
    exact ⟨⟨X, hX, rfl⟩, ⟨Y, hY, rfl⟩, existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_sharesSide_translate v hXY⟩

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"Its annulus is a translate of the catalogue annulus" -- the translate of a polygonal arc. -/
private def existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc (a : PolyArc) (v : Pt) : PolyArc := ⟨a.n, fun i => v +ᵥ a.pt i⟩

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
segments of a translated arc. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc_seg (a : PolyArc) (v : Pt) (i : Fin (a.n + 1)) :
    (existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc a v).seg i = v +ᵥ a.seg i := by
  simp only [PolyArc.seg, existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc, vadd_segment]

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
the carrier of a translated arc. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc_carrier (a : PolyArc) (v : Pt) :
    (existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc a v).carrier = v +ᵥ a.carrier := by
  simp only [PolyArc.carrier, Set.vadd_set_iUnion]
  exact iUnion_congr fun i => existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc_seg a v i

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
loop parametrizations translate. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_loop (K : Set Pt) (γ : ℝ → Pt) (v : Pt) (h : IsLoopParam K γ) :
    IsLoopParam (v +ᵥ K) (fun t => v +ᵥ γ t) := by
  obtain ⟨hc, hp, hi, hK⟩ := h
  refine ⟨continuous_const.add hc, fun t => by simp [hp t], ?_, ?_⟩
  · intro s hs t ht hst
    exact hi hs ht ((vadd_left_cancel_iff v).1 hst)
  · rw [← hK, ← Set.image_vadd, Set.image_image]

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
the matching cyclic order of the spokes is preserved by translation. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_matching (U Ko Ki : Set Pt) {k : ℕ} (x y : Fin k → Pt) (v : Pt)
    (h : MatchingCyclicOrder U Ko Ki x y) :
    MatchingCyclicOrder (v +ᵥ U) (v +ᵥ Ko) (v +ᵥ Ki) (fun j => v +ᵥ x j) (fun j => v +ᵥ y j) := by
  obtain ⟨γo, γi, ho, hi, ⟨F, hF, hper, h0, h1, hU⟩, ⟨t0, hto, hto1, hto2⟩, ⟨ti, hti, hti1, hti2⟩⟩ :=
    h
  refine ⟨fun t => v +ᵥ γo t, fun t => v +ᵥ γi t, existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_loop _ _ v ho,
      existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_loop _ _ v hi,
    ⟨fun st => v +ᵥ F st, continuous_const.add hF, fun s t => by simp [hper s t],
      fun t => by simp [h0 t], fun t => by simp [h1 t],
      fun s hs t => Set.vadd_mem_vadd_set (hU s hs t)⟩,
    ⟨t0, hto, hto1, fun i => by simp [hto2 i]⟩, ⟨ti, hti, hti1, fun i => by simp [hti2 i]⟩⟩

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
the carrier of a group is contained in the carrier of any group containing its faces. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_carrier_mono {S : Set (PlacedTile P)} (F F' : FaceGroup S) (h :
    F.faces ⊆ F'.faces) :
    F.carrier ⊆ F'.carrier := by
  show F.disk.carrier ⊆ F'.disk.carrier
  rw [F.carrier_eq, F'.carrier_eq]
  intro x hx
  simp only [support, mem_iUnion] at hx ⊢
  obtain ⟨A, hA, hx⟩ := hx
  exact ⟨A, h hA, hx⟩

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"Its annulus is a translate of the catalogue annulus of one original supertile, so the quantitative
data (`N`, `R`, the four separated windows of every piece, the private-edge count) are those of the
grouping step."  An annular grouping of `S` translates to an annular grouping of any `S'` containing
the translate of `S` whose vertices on the translated annulus are vertices of the translate of
`S`. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_annulus {M : MeshConstants P} {S S' : Set (PlacedTile P)} {c :
    Pt} {N : ℕ} {R : ℝ}
    (G : AnnularGrouping M S c N R) (v : Pt) (hsub : translateSet v S ⊆ S')
    (hV : ∀ w, Substitution.IsVertexOf S' w → w ∈ v +ᵥ (G.L.carrier ∪ G.H.carrier) →
      Substitution.IsVertexOf (translateSet v S) w) :
    ∃ G' : AnnularGrouping M S' (v + c) N R,
      G'.L.faces = translateSet v G.L.faces ∧
      G'.H.carrier = v +ᵥ G.H.carrier ∧
      (∀ j, (G'.spokes.piece j).faces = translateSet v (G.spokes.piece j).faces) ∧
      (∀ j, (G'.spokes.piece j).carrier = v +ᵥ (G.spokes.piece j).carrier) ∧
      (∀ j e, e ∈ privateOuterEdges G j → v +ᵥ e ∈ privateOuterEdges G' j) := by
  have hVL : ∀ w, Substitution.IsVertexOf S' w → w ∈ v +ᵥ G.L.carrier →
      Substitution.IsVertexOf (translateSet v S) w :=
    fun w hw hw' => hV w hw (Set.vadd_set_mono subset_union_left hw')
  have hVH : ∀ w, Substitution.IsVertexOf S' w → w ∈ v +ᵥ G.H.carrier →
      Substitution.IsVertexOf (translateSet v S) w :=
    fun w hw hw' => hV w hw (Set.vadd_set_mono subset_union_right hw')
  have hVP : ∀ j, ∀ w, Substitution.IsVertexOf S' w → w ∈ v +ᵥ (G.spokes.piece j).carrier →
      Substitution.IsVertexOf (translateSet v S) w := by
    intro j w hw hw'
    refine hVH w hw (Set.vadd_set_mono (existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_carrier_mono _ _ ?_) hw')
    exact (G.spokes.piece_sub j).trans diff_subset
  let L' : FaceGroup S' := existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_faceGroup G.L v hsub hVL
  let H' : FaceGroup S' := existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_faceGroup G.H v hsub hVH
  let pc : Fin (4 * N) → FaceGroup S' := fun j => existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_faceGroup (G.spokes.piece j)
      v hsub (hVP j)
  have hLc : L'.carrier = v +ᵥ G.L.carrier := rfl
  have hHc : H'.carrier = v +ᵥ G.H.carrier := rfl
  have hpc : ∀ j, (pc j).carrier = v +ᵥ (G.spokes.piece j).carrier := fun j => rfl
  have hmemT : ∀ {X : Set (PlacedTile P)} {B : PlacedTile P}, B.translate v ∈ translateSet v X ↔ B ∈ X :=
    fun {X B} => (emcg_translate_injective v).mem_set_image
  have hint : ∀ X : Set Pt, interior (v +ᵥ X) = v +ᵥ interior X := fun X => interior_vadd v X
  have hfr : ∀ X : Set Pt, frontier (v +ᵥ X) = v +ᵥ frontier X := fun X => by
    rw [frontier, closure_vadd, interior_vadd, ← Set.vadd_set_sdiff]; rfl
  have hannU : H'.carrier \ interior L'.carrier = v +ᵥ (G.H.carrier \ interior G.L.carrier) := by
    rw [hHc, hLc, hint, Set.vadd_set_sdiff]
  let sp : SpokeSystem S' L' H' N :=
    { spoke := fun j => existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc (G.spokes.spoke j) v
      simple := by
        intro j
        obtain ⟨hinj, hseg⟩ := G.spokes.simple j
        refine ⟨fun a b hab => hinj ((vadd_left_cancel_iff v).1 hab), ?_⟩
        intro a b hab
        have h := Set.vadd_set_mono (a := v) (hseg a b hab)
        rw [Set.vadd_set_inter, Set.vadd_set_inter, ← existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc_seg, ←
            existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc_seg] at h
        simpa [existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc, Set.vadd_set_insert, Set.vadd_set_singleton] using h
      skeletal := by
        intro j i
        obtain ⟨A, hA, he⟩ := G.spokes.skeletal j i
        exact ⟨A.translate v, hsub ⟨A, hA, rfl⟩, by rw [existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc_seg]; exact
            existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_hasEdge_translate v he⟩
      in_annulus := by
        intro j
        rw [existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc_carrier, hannU]
        exact Set.vadd_set_mono (G.spokes.in_annulus j)
      meets_L := by
        intro j
        rw [existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc_carrier, hLc, hfr, ← Set.vadd_set_inter, G.spokes.meets_L j,
          Set.vadd_set_singleton]
        rfl
      meets_H := by
        intro j
        rw [existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc_carrier, hHc, hfr, ← Set.vadd_set_inter, G.spokes.meets_H j,
          Set.vadd_set_singleton]
        rfl
      disjoint := by
        intro i j hij
        rw [existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc_carrier,
            existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc_carrier]
        exact (Set.disjoint_vadd_set).2 (G.spokes.disjoint i j hij)
      order := by
        rw [hannU, hHc, hLc, hfr, hfr]
        exact existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_matching _ _ _ _ _ v G.spokes.order
      piece := pc
      piece_partition := by
        intro A hA
        by_cases hT : ∃ B ∈ S, A = B.translate v
        · obtain ⟨B, hB, rfl⟩ := hT
          have := G.spokes.piece_partition B hB
          simp only [L', H', pc, existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_faceGroup]
          rw [hmemT, hmemT]
          simp only [hmemT]
          exact this
        · have hHS : ∀ X : Set (PlacedTile P), X ⊆ S → A ∉ translateSet v X := by
            rintro X hX ⟨B, hB, rfl⟩
            exact hT ⟨B, hX hB, rfl⟩
          constructor
          · rintro ⟨hH, -⟩
            exact absurd hH (hHS _ G.H.faces_sub)
          · rintro ⟨j, hj, -⟩
            exact absurd hj (hHS _ (G.spokes.piece j).faces_sub)
      piece_sub := by
        intro j
        show translateSet v _ ⊆ translateSet v _ \ translateSet v _
        rw [translateSet, translateSet, translateSet, ← Set.image_diff (emcg_translate_injective v)]
        exact image_mono (G.spokes.piece_sub j)
      piece_between := by
        intro j
        rw [existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc_carrier,
            existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_arc_carrier, hpc]
        exact ⟨Set.vadd_set_mono (G.spokes.piece_between j).1,
          Set.vadd_set_mono (G.spokes.piece_between j).2⟩
      contact_connected := by
        intro j
        rw [hpc, hLc, ← Set.vadd_set_inter, ← Set.image_vadd]
        exact (G.spokes.contact_connected j).image _ (continuous_const_vadd v).continuousOn
      contact_nondegenerate := by
        intro j
        rw [hpc, hLc, ← Set.vadd_set_inter, ← Set.image_vadd]
        exact (G.spokes.contact_nondegenerate j).image (fun a b h => (vadd_left_cancel_iff v).1 h) }
  have hK : ∀ (r : ℝ) (B : Set Pt), square (v + c) r + B = v +ᵥ (square c r + B) := fun r B => by
    rw [← existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_square_vadd,
        existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_vadd_add]
  have hcarT : ∀ F : PlacedTile P, interior (F.translate v).carrier = v +ᵥ interior F.carrier :=
    fun F => by rw [emcg_translate_carrier, hint]
  refine ⟨AnnularGrouping.mk L' H' ?_ ?_ ?_ ?_ ?_ ?_ sp, rfl, rfl, fun j => rfl, fun j => rfl, ?_⟩
  · rw [hLc, ← existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_square_vadd]; exact Set.vadd_set_mono G.L_lower
  · rw [hLc, hK]; exact Set.vadd_set_mono G.L_upper
  · intro i
    obtain ⟨F, hF, he, hne⟩ := G.L_anchor i
    refine ⟨F.translate v, ⟨F, hF, rfl⟩, ?_, ?_⟩
    · show HasEdge _ ((pdTranslate G.L.disk v).side i)
      rw [existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_pd_side]; exact
          existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_hasEdge_translate v he
    · rw [hcarT, ← existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_square_vadd, hint, ← Set.vadd_set_inter]
      exact hne.vadd_set
  · rw [hHc, hK]; exact Set.vadd_set_mono G.H_lower
  · rw [hHc, hK]; exact Set.vadd_set_mono G.H_upper
  · intro i
    obtain ⟨F, hF, hnot, he, hne⟩ := G.H_anchor i
    refine ⟨F.translate v, hsub ⟨F, hF, rfl⟩, fun h => hnot (hmemT.1 h), ?_, ?_⟩
    · show HasEdge _ ((pdTranslate G.H.disk v).side i)
      rw [existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_pd_side]; exact
          existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_hasEdge_translate v he
    · rw [hcarT, hK, ← Set.vadd_set_compl, ← Set.vadd_set_inter]
      exact hne.vadd_set
  · rintro j e ⟨⟨A, hA, heA⟩, hfrH, F, hF, hnot, heF, hdisj⟩
    refine ⟨⟨A.translate v, ⟨A, hA, rfl⟩, existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_hasEdge_translate v heA⟩, ?_,
      F.translate v, hsub ⟨F, hF, rfl⟩, fun h => hnot (hmemT.1 h),
          existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_hasEdge_translate v heF, ?_⟩
    · show v +ᵥ e ⊆ frontier H'.carrier
      rw [hHc, hfr]; exact Set.vadd_set_mono hfrH
    · intro t ht
      show Disjoint _ (pc t).carrier
      rw [hpc, emcg_translate_carrier]
      exact (Set.disjoint_vadd_set).2 (hdisj t ht)

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"Its annulus is a translate of the catalogue annulus of one original supertile" -- a vertex of a
patch with disjoint interiors lying in the interior of the support of a finite subpatch is a vertex
of the subpatch. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_vertex_local {S0 S' : Set (PlacedTile P)} (hsub : S0 ⊆ S') (hfin
    : S0.Finite)
    (hdisj : DisjointInteriors S') {w : Pt} (hw : w ∈ interior (support S0))
    (hv : Substitution.IsVertexOf S' w) : Substitution.IsVertexOf S0 w := by
  obtain ⟨B, hB, hwB⟩ := hv
  have hwc : w ∈ B.carrier := by
    obtain ⟨i, rfl⟩ := hwB
    refine emcg_side_subset_carrier B i ?_
    rw [emcg_side_eq_segment]
    exact left_mem_segment ℝ _ _
  have hreg : closure (interior B.carrier) = B.carrier := by
    rw [PlacedTile.carrier, interior_vadd, closure_vadd, (P.disk B.form).regular_closed]
  rw [← hreg] at hwc
  obtain ⟨y, hyU, hyB⟩ := mem_closure_iff.1 hwc _ isOpen_interior hw
  obtain ⟨A, hA, hAne⟩ := emcg_open_meets_interior (isOpen_interior.inter isOpen_interior)
    ⟨y, hyU, hyB⟩ hfin (fun z hz => interior_subset hz.1)
  by_cases hAB : A = B
  · subst hAB
    exact ⟨A, hA, hwB⟩
  · exfalso
    obtain ⟨z, ⟨-, hzB⟩, hzA⟩ := hAne
    exact Set.disjoint_left.mp (hdisj (hsub hA) hB hAB) hzA hzB

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
a single placed tile is side-to-side (distinct listed sides of a simple polygon meet in at most
their common endpoints). -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_sts_single {Q : Protoset} (A : PlacedTile Q) : SideToSideSet ({A}
    : Set _) := by
  rintro X rfl Y rfl i j hov
  by_cases hij : i = j
  · rw [hij]
  exfalso
  obtain ⟨x, y, hxy, hseg⟩ := hov
  have h := (Q.disk Y.form).simple i j hij
  have hsub : Y.side i ∩ Y.side j ⊆
      Y.anchor +ᵥ ({(Q.disk Y.form).vertex i, (Q.disk Y.form).vertex (finRotate _ i)} : Set Pt) := by
    simp only [PlacedTile.side]
    rw [← Set.vadd_set_inter]
    exact Set.vadd_set_mono (h.trans inter_subset_left)
  have hfin : (Y.anchor +ᵥ ({(Q.disk Y.form).vertex i, (Q.disk Y.form).vertex (finRotate _ i)} :
      Set Pt)).Finite := by
    rw [← Set.image_vadd]
    exact (Set.toFinite _).image _
  exact emcg_segment_infinite hxy (hfin.subset (hseg.trans hsub))

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
for the power `l = 0` the retained template is the parent group itself: its only child is the
central child `c⁰(α) = α` placed at the origin. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_template_zero (τ : Substitution P) (g :
    existsMacroCertificate_GroupingSeed τ)
    (α : g.GS.G.P'.Form) :
    ∃ T : Template g.GS.G.mixed,
      T.region = (τ.θ ^ (g.GS.k * 0)) • (g.GS.G.P'.disk α).carrier ∧
      g.GS.G.mixedScatter T.children.tiles = τ.decomposeIter (g.GS.k * 0) (g.GS.G.dissect α).tiles ∧
      T.children.tiles = {emcsCentralPlaced τ g 0 α} := by
  have hc : emcsCentralAnchor τ g 0 α = 0 :=
    (existsMacroCertificate_seed2_routing_step1_setup_sub1_central_chain τ g).choose_spec.choose_spec.2.1 α
  have hA : emcsCentralPlaced τ g 0 α = ⟨Sum.inl α, 0⟩ := by
    simp only [emcsCentralPlaced, hc, Function.iterate_zero, id]
  refine ⟨⟨⟨{⟨Sum.inl α, 0⟩}, finite_singleton _, pairwiseDisjoint_singleton _ _⟩,
    (g.GS.G.P'.disk α).carrier, ?_, existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_sts_single _⟩, by rw [mul_zero, pow_zero,
        one_smul], ?_, by rw [hA]⟩
  · simp only [support, mem_singleton_iff, iUnion_iUnion_eq_left, PlacedTile.carrier, zero_vadd]
    rfl
  · rw [mul_zero]
    simp only [GroupedFamily.mixedScatter, mem_singleton_iff, iUnion_iUnion_eq_left,
      GroupedFamily.mixedScatterTile, Sum.elim_inl, emcg_translateSet_zero]
    rfl

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
distinct listed sides of a polygonal disk are distinct sets. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_side_injective (B : PolygonalDisk) : Function.Injective B.side := by
  intro i j h
  by_contra hij
  have hab : B.vertex i ≠ B.vertex (finRotate B.n i) := fun he =>
    emcg_finRotate_ne (by have := B.three_le; omega) i (B.vertex_injective he).symm
  have hm : midpoint ℝ (B.vertex i) (B.vertex (finRotate B.n i)) ∈ B.side i :=
    midpoint_mem_segment _ _
  have hmj : midpoint ℝ (B.vertex i) (B.vertex (finRotate B.n i)) ∈ B.side j := h ▸ hm
  rcases (B.simple i j hij ⟨hm, hmj⟩).1 with h1 | h1
  · exact hab ((midpoint_eq_left_iff ℝ).mp h1)
  · exact hab ((midpoint_eq_right_iff ℝ).mp h1)

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
every listed side of a group is a whole side of one of its constituent tiles, so a group has at most
`K₀` listed sides per constituent. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_grouped_sides (M : MeshConstants P) (G : GroupedFamily P) (α : G.P'.Form) :
    (G.P'.disk α).n ≤ M.K0 * (G.dissect α).tiles.ncard := by
  classical
  choose A hA k hk using G.side_whole α
  let f : Fin (G.P'.disk α).n → PlacedTile P × Fin M.K0 := fun i =>
    (A i, ⟨k i, lt_of_lt_of_le (k i).isLt (M.sides_le _)⟩)
  have hinj : Function.Injective f := by
    intro i j hij
    simp only [f, Prod.mk.injEq, Fin.mk.injEq] at hij
    apply existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_side_injective
    rw [← hk i, ← hk j]
    obtain ⟨h1, h2⟩ := hij
    have : ∀ {X Y : PlacedTile P} (a : Fin (P.disk X.form).n) (b : Fin (P.disk Y.form).n),
        X = Y → (a : ℕ) = b → X.side a = Y.side b := by
      intro X Y a b hXY hab
      subst hXY
      rw [Fin.ext hab]
    exact this _ _ h1 h2
  have hfin := (G.dissect α).finite
  have hcard := Finset.card_le_card_of_injOn f (s := Finset.univ)
    (t := hfin.toFinset ×ˢ (Finset.univ : Finset (Fin M.K0)))
    (fun i _ => by simp [f, hA i]) hinj.injOn
  rw [Finset.card_univ, Fintype.card_fin, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    ← Set.ncard_eq_toFinset_card _ hfin] at hcard
  linarith [hcard, mul_comm M.K0 (G.dissect α).tiles.ncard]

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
`Q ≥ K₀`, i.e. `K₀ ≤ K₀ ⌈4C²R²/a⌉`. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_K0_le_Qmax (τ : Substitution P) (g :
    existsMacroCertificate_GroupingSeed τ) :
    g.M.K0 ≤ g.Qmax := by
  rw [g.Qmax_eq]
  have hR : 0 < g.R := by
    have := g.R_separates; rw [g.Csep_eq] at this; nlinarith [g.M.D_pos]
  have hpos : 0 < 4 * g.C ^ 2 * g.R ^ 2 / g.M.a := by
    rw [g.C_eq]; have := g.M.a_pos; positivity
  have : 1 ≤ ⌈4 * g.C ^ 2 * g.R ^ 2 / g.M.a⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; exact hpos)
  nlinarith

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"an original tile has at most `K₀ ≤ Q` sides" -- a singleton group has at most `Qmax` listed sides. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_singleton_sides (τ : Substitution P) (g :
    existsMacroCertificate_GroupingSeed τ)
    (α : g.GS.G.P'.Form) (p : P.Form) (hα : (g.GS.G.dissect α).tiles = {⟨p, 0⟩}) :
    (g.GS.G.P'.disk α).n ≤ g.Qmax := by
  have h := existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_grouped_sides g.M g.GS.G α
  rw [hα, Set.ncard_singleton, mul_one] at h
  exact h.trans (existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_K0_le_Qmax τ g)

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
segments are null sets. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_volume_segment (x y : Pt) : MeasureTheory.volume (segment ℝ x y) = 0 := by
  have hsub : segment ℝ x y ⊆ (affineSpan ℝ ({x, y} : Set Pt) : Set Pt) := by
    rw [segment_eq_image_lineMap]
    rintro _ ⟨t, -, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair t x y
  refine MeasureTheory.measure_mono_null hsub ?_
  refine MeasureTheory.Measure.addHaar_affineSubspace _ _ ?_
  intro htop
  have h1 := (collinear_iff_finrank_le_one (k := ℝ) (s := ({x, y} : Set Pt))).1 (collinear_pair ℝ x y)
  rw [← direction_affineSpan, htop, AffineSubspace.direction_top, finrank_top, finrank_euclideanSpace,
    Fintype.card_fin] at h1
  omega

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
the interior of a polygonal disk has full measure. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_volume_interior (B : PolygonalDisk) :
    MeasureTheory.volume (interior B.carrier) = MeasureTheory.volume B.carrier := by
  refine le_antisymm (MeasureTheory.measure_mono interior_subset) ?_
  have hfr : MeasureTheory.volume (frontier B.carrier) = 0 := by
    rw [B.frontier_eq]
    exact MeasureTheory.measure_iUnion_null fun i => existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_volume_segment _ _
  calc MeasureTheory.volume B.carrier ≤
        MeasureTheory.volume (interior B.carrier ∪ frontier B.carrier) := by
        refine MeasureTheory.measure_mono fun z hz => ?_
        by_cases h : z ∈ interior B.carrier
        · exact Or.inl h
        · exact Or.inr ⟨subset_closure hz, h⟩
    _ ≤ _ := MeasureTheory.measure_union_le _ _
    _ = _ := by rw [hfr, add_zero]

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
(`lem:quantitative-sector`) a finite family of tiles with disjoint interiors inside a ball of radius
`d` has at most `⌈4d²/a⌉` members. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_faces_le (M : MeshConstants P) {F : Set (PlacedTile P)} (hF : F.Finite)
    (hdisj : DisjointInteriors F) {x : Pt} {d : ℝ} (hd0 : 0 ≤ d)
    (hball : support F ⊆ Metric.closedBall x d) : F.ncard ≤ ⌈4 * d ^ 2 / M.a⌉₊ := by
  classical
  open MeasureTheory in
  set t := hF.toFinset with ht
  have hdisj' : (↑t : Set (PlacedTile P)).PairwiseDisjoint (fun A => interior A.carrier) := by
    rw [ht, Set.Finite.coe_toFinset]; exact hdisj
  have hmeas := measure_biUnion_finset (μ := volume) hdisj' (fun A _ => isOpen_interior.measurableSet)
  have hvolA : ∀ A ∈ t, ENNReal.ofReal M.a ≤ volume (interior A.carrier) := by
    intro A _
    rw [PlacedTile.carrier, interior_vadd, measure_vadd, existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_volume_interior]
    exact M.area_ge A.form
  have hle : volume (⋃ A ∈ t, interior A.carrier) ≤ volume (Metric.closedBall x d) := by
    apply measure_mono
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨A, hA, hzA⟩ := hz
    refine hball ?_
    exact emcg_carrier_subset_support (by simpa [ht] using hA) (interior_subset hzA)
  rw [hmeas, EuclideanSpace.volume_closedBall_fin_two] at hle
  have hsum : (t.card : ENNReal) * ENNReal.ofReal M.a ≤ ENNReal.ofReal (d ^ 2 * Real.pi) := by
    calc (t.card : ENNReal) * ENNReal.ofReal M.a = ∑ A ∈ t, ENNReal.ofReal M.a := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hvolA
      _ ≤ _ := hle
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hd0]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hsum
  have hcard : F.ncard = t.card := Set.ncard_eq_toFinset_card _ hF
  rw [hcard]
  have ha := M.a_pos
  have : (t.card : ℝ) ≤ 4 * d ^ 2 / M.a := by
    rw [le_div_iff₀ ha]
    nlinarith [Real.pi_lt_four, sq_nonneg d]
  exact_mod_cast this.trans (Nat.le_ceil _)

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"an annular piece has at most `Q` sides (`lem:quantitative-sector`)" -- the small catalogue forms
have at most `Qmax` listed sides. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_small_sides (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ)
    (p : P.Form) (j : Fin (4 * g.N)) : (g.GS.G.P'.disk (g.small p j)).n ≤ g.Qmax := by
  have h := existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_grouped_sides g.M g.GS.G (g.small p j)
  have hR : 0 < g.R := by
    have := g.R_separates; rw [g.Csep_eq] at this; nlinarith [g.M.D_pos]
  have hC : 0 < g.C := by rw [g.C_eq]; norm_num
  have hsupp : support (g.GS.G.dissect (g.small p j)).tiles = ((g.annular p).spokes.piece j).carrier := by
    rw [g.small_dissect]; exact ((g.annular p).spokes.piece j).carrier_eq.symm
  obtain ⟨x, hx⟩ := ((g.annular p).spokes.piece j).disk.interior_nonempty
  have hxc : x ∈ ((g.annular p).spokes.piece j).carrier := interior_subset hx
  have hdiam := (g.annular_quantitative p).2.2.1 j
  have hball : support (g.GS.G.dissect (g.small p j)).tiles ⊆ Metric.closedBall x (g.C * g.R) := by
    rw [hsupp]
    intro y hy
    exact Metric.mem_closedBall.2 ((Metric.dist_le_diam_of_mem
      ((g.annular p).spokes.piece j).disk.compact.isBounded hy hxc).trans hdiam)
  have hf := existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_faces_le g.M (g.GS.G.dissect (g.small p j)).finite (g.GS.G.dissect
      (g.small p j)).disjoint
    (by positivity) hball
  rw [g.Qmax_eq]
  calc _ ≤ g.M.K0 * (g.GS.G.dissect (g.small p j)).tiles.ncard := h
    _ ≤ g.M.K0 * ⌈4 * (g.C * g.R) ^ 2 / g.M.a⌉₊ := Nat.mul_le_mul_left _ hf
    _ = _ := by rw [mul_pow, ← mul_assoc]

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
the translated central supertile `τ^k q` of the central chain lies in the iterated decomposition of
the parent (`sub1_central_chain`). -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_supertile_sub (τ : Substitution P) (g :
    existsMacroCertificate_GroupingSeed τ)
    (m : ℕ) (α : g.GS.G.P'.Form) :
    translateSet (emcsCentralAnchor τ g (m + 1) α)
        (τ.supertile g.k (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form) ⊆
      τ.decomposeIter (g.GS.k * (m + 1)) (g.GS.G.dissect α).tiles :=
  (existsMacroCertificate_seed2_routing_step1_setup_sub1_central_chain τ g).choose_spec.choose_spec.2.2.2.2 m α

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
the support of a supertile is the scaled disk. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_support_supertile (τ : Substitution P) (n : ℕ) (p : P.Form) :
    support (τ.supertile n p) = (τ.θ ^ n) • (P.disk p).carrier := by
  rw [Substitution.supertile, emcg_iter_support, emcg_support_singleton_zero]

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
supports are monotone. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_support_mono {Q : Protoset} {X Y : Set (PlacedTile Q)} (h : X ⊆ Y) :
    support X ⊆ support Y :=
  biUnion_subset_biUnion_left h

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"at each step the chosen centre lies in the square of Lemma `lem:quantitative-sector` with its margin,
strictly inside the scaled parent" -- the margin square of the retained centre lies in the interior
of the retained region. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_margin (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ)
    (m : ℕ) (α : g.GS.G.P'.Form) :
    square (emcsCentre τ g (m + 1) α) ((g.N : ℝ) * g.R / 2 + g.R) + Binf (10 * g.M.D) ⊆
      interior ((τ.θ ^ (g.GS.k * (m + 1))) • (g.GS.G.P'.disk α).carrier) := by
  set v := emcsCentralAnchor τ g (m + 1) α
  set p := (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form
  have hc : emcsCentre τ g (m + 1) α = v + g.centre p := rfl
  rw [hc, ← existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_square_vadd,
      existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_vadd_add]
  refine (Set.vadd_set_mono (g.square_margin p)).trans ?_
  rw [← interior_vadd, ← existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_support_supertile, ← emcg_support_translateSet,
    ← g.GS.G.support_eq, ← emcg_iter_support]
  exact interior_mono (existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_support_mono
      (existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_supertile_sub τ g m α))

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"Its annulus is a translate of the catalogue annulus of one original supertile" -- the annulus of the
retained template at the power `m + 1`. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_annulus_succ (τ : Substitution P) (g :
    existsMacroCertificate_GroupingSeed τ)
    (m : ℕ) (α : g.GS.G.P'.Form) (S' : Set (PlacedTile P))
    (hS' : S' = τ.decomposeIter (g.GS.k * (m + 1)) (g.GS.G.dissect α).tiles) :
    ∃ G' : AnnularGrouping g.M S' (emcsCentre τ g (m + 1) α) g.N g.R,
      G'.L.faces = translateSet (emcsCentralAnchor τ g (m + 1) α)
        (g.annular (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form).L.faces ∧
      (∀ j, (G'.spokes.piece j).faces = translateSet (emcsCentralAnchor τ g (m + 1) α)
        ((g.annular (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form).spokes.piece j).faces) ∧
      (∀ j, (G'.spokes.piece j).carrier = emcsCentralAnchor τ g (m + 1) α +ᵥ
        ((g.annular (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form).spokes.piece j).carrier) ∧
      (∀ j e, e ∈ privateOuterEdges (g.annular (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form) j →
        emcsCentralAnchor τ g (m + 1) α +ᵥ e ∈ privateOuterEdges G' j) := by
  set v := emcsCentralAnchor τ g (m + 1) α
  set p := (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form
  have hsub : translateSet v (τ.supertile g.k p) ⊆ S' := hS' ▸ existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_supertile_sub τ g m α
  have hdisj : DisjointInteriors S' := hS' ▸ emcg_iter_disjoint τ _ (g.GS.G.dissect α).disjoint
  have hR : 0 ≤ g.R := by
    have := g.R_separates; rw [g.Csep_eq] at this; nlinarith [g.M.D_pos]
  have hD := g.M.D_pos
  have hBinf : ∀ {r s : ℝ}, r ≤ s → Binf r ⊆ Binf s := fun h x hx => ⟨hx.1.trans h, hx.2.trans h⟩
  have hLH : (g.annular p).L.carrier ∪ (g.annular p).H.carrier ⊆
      interior ((τ.θ ^ g.k) • (P.disk p).carrier) := by
    refine union_subset ?_ ?_
    · refine (g.annular p).L_upper.trans (Set.Subset.trans ?_ (g.square_margin p))
      exact Set.add_subset_add (emcg_square_mono _ (by linarith)) (hBinf (by linarith))
    · refine (g.annular p).H_upper.trans (Set.Subset.trans ?_ (g.square_margin p))
      exact Set.add_subset_add_left (hBinf (by linarith))
  have hV : ∀ w, Substitution.IsVertexOf S' w →
      w ∈ v +ᵥ ((g.annular p).L.carrier ∪ (g.annular p).H.carrier) →
      Substitution.IsVertexOf (translateSet v (τ.supertile g.k p)) w := by
    intro w hw hw'
    refine existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_vertex_local hsub ((emcg_supertile_finite τ g.k p).image _) hdisj ?_ hw
    rw [emcg_support_translateSet, existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_support_supertile, interior_vadd]
    exact Set.vadd_set_mono hLH hw'
  obtain ⟨G', h1, -, h3, h4, h5⟩ := existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_annulus (g.annular p) v hsub hV
  exact ⟨G', h1, h3, h4, h5⟩

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
ideal trapezoids translate with their centre. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_trapezoid (v c : Pt) (N : ℕ) (R D : ℝ) (j : ℕ) (r : ℝ) :
    v +ᵥ Metric.cthickening r (idealTrapezoid c N R D j) =
      Metric.cthickening r (idealTrapezoid (v + c) N R D j) := by
  have ht : idealTrapezoid (v + c) N R D j = v +ᵥ idealTrapezoid c N R D j := by
    ext x
    simp only [idealTrapezoid, mem_setOf_eq, mem_vadd_set, vadd_eq_add]
    constructor
    · rintro ⟨t, ht, μ, hμ, rfl⟩
      exact ⟨c + μ • squarePerimeterPoint ((N : ℝ) * R / 2) t, ⟨t, ht, μ, hμ, rfl⟩, by abel⟩
    · rintro ⟨_, ⟨t, ht, μ, hμ, rfl⟩, rfl⟩
      exact ⟨t, ht, μ, hμ, by abel⟩
  rw [ht]
  ext x
  simp only [Metric.cthickening_eq_preimage_infEDist, mem_preimage, mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← vadd_eq_add, Metric.infEDist_vadd]
    exact hy
  · intro hx
    refine ⟨x - v, ?_, by abel⟩
    have : x = v +ᵥ (x - v) := by rw [vadd_eq_add]; abel
    rw [this, Metric.infEDist_vadd] at hx
    exact hx

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
the carrier of a mixed tile is the support of its scattering. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_carrier_scatter (G : GroupedFamily P) (X : PlacedTile G.mixed) :
    X.carrier = support (G.mixedScatterTile X) := by
  obtain ⟨f, w⟩ := X
  cases f with
  | inl β =>
    show w +ᵥ (G.P'.disk β).carrier = support (translateSet w (G.dissect β).tiles)
    rw [emcg_support_translateSet, G.support_eq]
  | inr q =>
    show w +ᵥ (P.disk q).carrier = support ({⟨q, w⟩} : Set (PlacedTile P))
    simp [support, PlacedTile.carrier]

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"these are whole sides ... by the whole-side property of groups" -- every listed side of a mixed tile
is a whole side of one of its scattered constituents. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_child_side (G : GroupedFamily P) (X : PlacedTile G.mixed)
    (i : Fin (G.mixed.disk X.form).n) : ∃ A ∈ G.mixedScatterTile X, HasEdge A (X.side i) := by
  obtain ⟨f, w⟩ := X
  cases f with
  | inl β =>
    obtain ⟨A, hA, he⟩ := G.side_whole β i
    exact ⟨A.translate w, ⟨A, hA, rfl⟩, existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_hasEdge_translate w he⟩
  | inr q =>
    exact ⟨⟨q, w⟩, mem_singleton _, i, rfl⟩

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
side-to-side sets stay side-to-side after untranslating. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_sts_untranslate {S : Set (PlacedTile P)} (u : Pt)
    (h : SideToSideSet (translateSet u S)) : SideToSideSet S := by
  intro A hA B hB i j hov
  obtain ⟨x, y, hxy, hseg⟩ := hov
  have hov' : OverlapPos ((A.translate u).side i) ((B.translate u).side j) := by
    refine ⟨u +ᵥ x, u +ᵥ y, fun he => hxy ((vadd_left_cancel_iff u).1 he), ?_⟩
    rw [emcg_translate_side, emcg_translate_side, ← Set.vadd_set_inter, ← vadd_segment]
    exact Set.vadd_set_mono hseg
  have := h _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ i j hov'
  rw [emcg_translate_side, emcg_translate_side] at this
  exact (vadd_left_cancel_iff u).1 this

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
the iterated decomposition of a group is side-to-side (it lies in a translated supertile, STS). -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_sts_iter (τ : Substitution P) (h : τ.STS) (g :
    existsMacroCertificate_GroupingSeed τ)
    (n : ℕ) (α : g.GS.G.P'.Form) : SideToSideSet (τ.decomposeIter n (g.GS.G.dissect α).tiles) := by
  obtain ⟨n0, p0, w, hw⟩ := g.inside_supertile α
  refine existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_sts_untranslate ((τ.θ ^ n) • w) (emcg_sts_subset (h (n0 + n) p0) ?_)
  rw [← emcg_iter_translate, Substitution.supertile, ← emcg_iter_add]
  exact emcg_iter_mono τ n hw

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"The retained templates are side-to-side because scattering a group of a side-to-side patch along
whole sides preserves the side-to-side property." -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_sts_mixed (G : GroupedFamily P) {C : Set (PlacedTile G.mixed)}
    {S : Set (PlacedTile P)} (hS : SideToSideSet S) (hC : G.mixedScatter C ⊆ S) : SideToSideSet C := by
  intro X hX Y hY i j hov
  obtain ⟨A, hA, a, ha⟩ := existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_child_side G X i
  obtain ⟨B, hB, b, hb⟩ := existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_child_side G Y j
  have hA' : A ∈ S := hC (mem_biUnion hX hA)
  have hB' : B ∈ S := hC (mem_biUnion hY hB)
  rw [← ha, ← hb] at hov ⊢
  exact hS A hA' B hB' a b hov

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
children whose scatterings are disjoint families of a patch with disjoint interiors have disjoint
interiors. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_disjoint_mixed (G : GroupedFamily P) {C : Set (PlacedTile G.mixed)}
    {S : Set (PlacedTile P)} (hS : DisjointInteriors S) (hC : G.mixedScatter C ⊆ S)
    (huniq : ∀ X ∈ C, ∀ Y ∈ C, ∀ A, A ∈ G.mixedScatterTile X → A ∈ G.mixedScatterTile Y → X = Y) :
    DisjointInteriors C := by
  intro X hX Y hY hXY
  have hfin : ∀ Z : PlacedTile G.mixed, (G.mixedScatterTile Z).Finite := by
    rintro ⟨f, w⟩
    cases f with
    | inl β => exact (G.dissect β).finite.image _
    | inr q => exact finite_singleton _
  show Disjoint (interior X.carrier) (interior Y.carrier)
  rw [existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_carrier_scatter,
      existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_carrier_scatter]
  refine emcg_disjoint_interior_support hS (fun A hA => hC (mem_biUnion hX hA))
    (fun A hA => hC (mem_biUnion hY hA)) (hfin X) (hfin Y) ?_
  rw [Set.disjoint_left]
  intro A h1 h2
  exact hXY (huniq X hX Y hY A h1 h2)

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"a large form `L_p` has exactly `4N` marked sides, the side it shares with each of the `4N` annular
pieces (one per piece; these are whole sides of `L_p` by the whole-side property of groups)" -- every
small catalogue group shares a whole listed side with the large catalogue group of the same
supertile. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_contact (τ : Substitution P) (h : τ.STS) (g :
    existsMacroCertificate_GroupingSeed τ)
    (p : P.Form) (j : Fin (4 * g.N)) :
    SharesSide (⟨Sum.inl (g.small p j), 0⟩ : PlacedTile g.GS.G.mixed) ⟨Sum.inl (g.large p), 0⟩ := by
  classical
  set G := g.GS.G
  set L := (g.annular p).L
  set Pc := (g.annular p).spokes.piece j
  set D1 := G.P'.disk (g.large p)
  set D2 := G.P'.disk (g.small p j)
  have hD1 : D1.carrier = support L.faces := by
    rw [← G.support_eq, g.large_dissect]
  have hD2 : D2.carrier = support Pc.faces := by
    rw [← G.support_eq, g.small_dissect]
  have hdisjF : Disjoint L.faces Pc.faces :=
    Set.disjoint_left.2 fun A hA hA' => ((g.annular p).spokes.piece_sub j hA').2 hA
  have hint : Disjoint (interior D1.carrier) (interior D2.carrier) := by
    rw [hD1, hD2]
    exact emcg_disjoint_interior_support (emcg_supertile_disjoint τ g.k p) L.faces_sub Pc.faces_sub
      L.finite Pc.finite hdisjF
  set K := D2.carrier ∩ D1.carrier with hKdef
  have hK : K = Pc.carrier ∩ L.carrier := by
    rw [hKdef, hD1, hD2]
    show support Pc.faces ∩ support L.faces = Pc.disk.carrier ∩ L.disk.carrier
    rw [Pc.carrier_eq, L.carrier_eq]
  have hKconn : IsPreconnected K := by
    rw [hK]; exact ((g.annular p).spokes.contact_connected j).isPreconnected
  have hKnt : K.Nontrivial := by
    rw [hK]; exact (g.annular p).spokes.contact_nondegenerate j
  have hfr : ∀ (E F : PolygonalDisk), Disjoint (interior E.carrier) (interior F.carrier) →
      F.carrier ∩ E.carrier ⊆ frontier E.carrier := by
    intro E F hEF x ⟨hxF, hxE⟩
    refine ⟨subset_closure hxE, fun hxi => ?_⟩
    rw [← F.regular_closed] at hxF
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hxF _ isOpen_interior hxi
    exact Set.disjoint_left.mp hEF hy1 hy2
  have hK1 : K ⊆ ⋃ i, D1.side i := by
    have := hfr D1 D2 hint
    rw [D1.frontier_eq] at this
    exact this
  have hK2 : K ⊆ ⋃ a, D2.side a := by
    have := hfr D2 D1 hint.symm
    rw [D2.frontier_eq, inter_comm] at this
    exact this
  have hinf : K.Infinite := hKconn.infinite_of_nontrivial hKnt
  obtain ⟨i, a, hia⟩ : ∃ i a, (K ∩ (D1.side i ∩ D2.side a)).Infinite := by
    by_contra hno
    push_neg at hno
    refine hinf ((Set.finite_iUnion fun i => Set.finite_iUnion fun a =>
      hno i a).subset ?_)
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hK1 hx)
    obtain ⟨a, ha⟩ := mem_iUnion.1 (hK2 hx)
    exact mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨a, hx, hi, ha⟩⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hia.nontrivial
  have hov : OverlapPos (D1.side i) (D2.side a) := by
    refine ⟨x, y, hxy, ?_⟩
    exact ((convex_segment _ _).inter (convex_segment _ _)).segment_subset hx.2 hy.2
  obtain ⟨A, hA, ia, hAi⟩ := G.side_whole (g.large p) i
  obtain ⟨B, hB, ib, hBi⟩ := G.side_whole (g.small p j) a
  rw [g.large_dissect] at hA
  rw [g.small_dissect] at hB
  have heq : D1.side i = D2.side a := by
    rw [← hAi, ← hBi] at hov ⊢
    exact h g.k p A (L.faces_sub hA) B (Pc.faces_sub hB) ia ib hov
  refine ⟨fun hne => ?_, (0 : Pt) +ᵥ D2.side a, ⟨a, rfl⟩, ⟨i, ?_⟩⟩
  · simp only [PlacedTile.mk.injEq, Sum.inl.injEq] at hne
    have := g.catalogue_labels_injective (a₁ := Sum.inr (Sum.inl (p, j))) (a₂ := Sum.inl p) hne.1
    exact Sum.inr_ne_inl this
  · show (0 : Pt) +ᵥ D1.side i = (0 : Pt) +ᵥ D2.side a
    rw [heq]

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub2_templates`:
"For a power `l` the retained template of `α` keeps, inside `σ^l α`, only the central chain `c^l(α)`
... and its `4N` annular neighbours, and scatters every other group into original tiles."  At the
power `m + 1` the retained template has the central child, the `4N` translated small catalogue
groups of the central supertile, and otherwise only original tiles. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_template_succ (τ : Substitution P) (h : τ.STS)
    (g : existsMacroCertificate_GroupingSeed τ) (m : ℕ) (α : g.GS.G.P'.Form) :
    ∃ T : Template g.GS.G.mixed,
      T.region = (τ.θ ^ (g.GS.k * (m + 1))) • (g.GS.G.P'.disk α).carrier ∧
      g.GS.G.mixedScatter T.children.tiles =
        τ.decomposeIter (g.GS.k * (m + 1)) (g.GS.G.dissect α).tiles ∧
      emcsCentralPlaced τ g (m + 1) α ∈ T.children.tiles ∧
      (∀ j, (⟨Sum.inl (g.small (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form j),
          emcsCentralAnchor τ g (m + 1) α⟩ : PlacedTile g.GS.G.mixed) ∈ T.children.tiles) ∧
      ∀ X ∈ T.children.tiles, X = emcsCentralPlaced τ g (m + 1) α ∨
        (∃ j, X = ⟨Sum.inl (g.small (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form j),
          emcsCentralAnchor τ g (m + 1) α⟩) ∨ ∃ q, X.form = Sum.inr q := by
  classical
  set n := g.GS.k * (m + 1) with hn
  set S' := τ.decomposeIter n (g.GS.G.dissect α).tiles with hS'
  set v := emcsCentralAnchor τ g (m + 1) α with hv
  set p := (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form with hp
  have hcent : emcsCentralPlaced τ g (m + 1) α = ⟨Sum.inl (g.large p), v⟩ := by
    simp only [emcsCentralPlaced, Function.iterate_succ_apply']
    rfl
  have hsupT : translateSet v (τ.supertile g.k p) ⊆ S' := existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_supertile_sub τ g m α
  have hLf : translateSet v (g.annular p).L.faces ⊆ S' :=
    (image_mono (g.annular p).L.faces_sub).trans hsupT
  have hPf : ∀ j, translateSet v ((g.annular p).spokes.piece j).faces ⊆ S' := fun j =>
    (image_mono ((g.annular p).spokes.piece j).faces_sub).trans hsupT
  have hS'fin : S'.Finite := emcg_iter_finite τ n (g.GS.G.dissect α).finite
  let sm : Fin (4 * g.N) → PlacedTile g.GS.G.mixed := fun j => ⟨Sum.inl (g.small p j), v⟩
  let Rest : Set (PlacedTile P) := S' \ (translateSet v (g.annular p).L.faces ∪
    ⋃ j, translateSet v ((g.annular p).spokes.piece j).faces)
  let orig : PlacedTile P → PlacedTile g.GS.G.mixed := fun B => ⟨Sum.inr B.form, B.anchor⟩
  let C : Set (PlacedTile g.GS.G.mixed) := insert ⟨Sum.inl (g.large p), v⟩ (range sm ∪ orig '' Rest)
  have hsc_c : g.GS.G.mixedScatterTile ⟨Sum.inl (g.large p), v⟩ =
      translateSet v (g.annular p).L.faces := by
    show translateSet v (g.GS.G.dissect (g.large p)).tiles = _
    rw [g.large_dissect]
  have hsc_s : ∀ j, g.GS.G.mixedScatterTile (sm j) =
      translateSet v ((g.annular p).spokes.piece j).faces := by
    intro j
    show translateSet v (g.GS.G.dissect (g.small p j)).tiles = _
    rw [g.small_dissect]
  have hsc_o : ∀ B, g.GS.G.mixedScatterTile (orig B) = {B} := fun B => rfl
  have hscat : g.GS.G.mixedScatter C = S' := by
    ext A
    simp only [GroupedFamily.mixedScatter, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨X, hX, hA⟩
      rcases hX with rfl | ⟨j, rfl⟩ | ⟨B, hB, rfl⟩
      · rw [hsc_c] at hA; exact hLf hA
      · rw [hsc_s] at hA; exact hPf j hA
      · rw [hsc_o, mem_singleton_iff] at hA; subst hA; exact hB.1
    · intro hA
      by_cases h1 : A ∈ translateSet v (g.annular p).L.faces
      · exact ⟨_, mem_insert _ _, by rw [hsc_c]; exact h1⟩
      by_cases h2 : ∃ j, A ∈ translateSet v ((g.annular p).spokes.piece j).faces
      · obtain ⟨j, hj⟩ := h2
        exact ⟨sm j, Or.inr (Or.inl ⟨j, rfl⟩), by rw [hsc_s]; exact hj⟩
      · refine ⟨orig A, Or.inr (Or.inr ⟨A, ⟨hA, ?_⟩, rfl⟩), by rw [hsc_o]; exact mem_singleton _⟩
        rintro (h | h)
        · exact h1 h
        · exact h2 (mem_iUnion.1 h)
  have hLP : ∀ j A, A ∈ translateSet v (g.annular p).L.faces →
      A ∈ translateSet v ((g.annular p).spokes.piece j).faces → False := by
    rintro j _ ⟨B, hB, rfl⟩ hB'
    have hB'' := (emcg_translate_injective v).mem_set_image.1 hB'
    exact ((g.annular p).spokes.piece_sub j hB'').2 hB
  have hPP : ∀ j j' A, A ∈ translateSet v ((g.annular p).spokes.piece j).faces →
      A ∈ translateSet v ((g.annular p).spokes.piece j').faces → j = j' := by
    rintro j j' _ ⟨B, hB, rfl⟩ hB'
    have hB'' := (emcg_translate_injective v).mem_set_image.1 hB'
    have hBS := ((g.annular p).spokes.piece j).faces_sub hB
    have hex := ((g.annular p).spokes.piece_partition B hBS).1
      ⟨((g.annular p).spokes.piece_sub j hB).1, ((g.annular p).spokes.piece_sub j hB).2⟩
    exact hex.unique hB hB''
  have hRest : ∀ B ∈ Rest, ∀ X, (X = (⟨Sum.inl (g.large p), v⟩ : PlacedTile g.GS.G.mixed) ∨
      ∃ j, X = sm j) → B ∈ g.GS.G.mixedScatterTile X → False := by
    rintro B ⟨-, hB⟩ X hX hBX
    rcases hX with rfl | ⟨j, rfl⟩
    · rw [hsc_c] at hBX; exact hB (Or.inl hBX)
    · rw [hsc_s] at hBX; exact hB (Or.inr (mem_iUnion.2 ⟨j, hBX⟩))
  have huniq : ∀ X ∈ C, ∀ Y ∈ C, ∀ A, A ∈ g.GS.G.mixedScatterTile X →
      A ∈ g.GS.G.mixedScatterTile Y → X = Y := by
    intro X hX Y hY A hAX hAY
    rcases hX with rfl | ⟨j, rfl⟩ | ⟨B, hB, rfl⟩ <;> rcases hY with rfl | ⟨j', rfl⟩ | ⟨B', hB', rfl⟩
    · rfl
    · rw [hsc_c] at hAX; rw [hsc_s] at hAY; exact (hLP j' A hAX hAY).elim
    · rw [hsc_o, mem_singleton_iff] at hAY; subst hAY
      exact (hRest A hB' _ (Or.inl rfl) hAX).elim
    · rw [hsc_s] at hAX; rw [hsc_c] at hAY; exact (hLP j A hAY hAX).elim
    · rw [hsc_s] at hAX hAY; rw [hPP j j' A hAX hAY]
    · rw [hsc_o, mem_singleton_iff] at hAY; subst hAY
      exact (hRest A hB' _ (Or.inr ⟨j, rfl⟩) hAX).elim
    · rw [hsc_o, mem_singleton_iff] at hAX; subst hAX
      exact (hRest A hB _ (Or.inl rfl) hAY).elim
    · rw [hsc_o, mem_singleton_iff] at hAX; subst hAX
      exact (hRest A hB _ (Or.inr ⟨j', rfl⟩) hAY).elim
    · rw [hsc_o, mem_singleton_iff] at hAX hAY; rw [← hAX, ← hAY]
  have hCfin : C.Finite :=
    ((finite_range sm).union ((hS'fin.subset diff_subset).image orig)).insert _
  have hsupp : support C = support (g.GS.G.mixedScatter C) := by
    simp only [GroupedFamily.mixedScatter]
    rw [emcg_support_biUnion]
    simp only [support]
    exact iUnion₂_congr fun X _ => existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_carrier_scatter g.GS.G X
  refine ⟨⟨⟨C, hCfin, existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_disjoint_mixed g.GS.G (emcg_iter_disjoint τ n
      (g.GS.G.dissect α).disjoint)
      hscat.le huniq⟩, (τ.θ ^ n) • (g.GS.G.P'.disk α).carrier, ?_,
      existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_sts_mixed g.GS.G
          (existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_sts_iter τ h g n α) hscat.le⟩, rfl, hscat, ?_, ?_, ?_⟩
  · show support C = _
    rw [hsupp, hscat, hS', emcg_iter_support, g.GS.G.support_eq]
  · show _ ∈ C
    rw [hcent]; exact mem_insert _ _
  · intro j
    exact Or.inr (Or.inl ⟨j, rfl⟩)
  · intro X hX
    rcases hX with rfl | ⟨j, rfl⟩ | ⟨B, hB, rfl⟩
    · exact Or.inl hcent.symm
    · exact Or.inr (Or.inl ⟨j, rfl⟩)
    · exact Or.inr (Or.inr ⟨B.form, rfl⟩)

/-- Step 3 of `lem:certificate-exists`: "Scattering a group and applying the grouped substitution
to each constituent defines `σ` on `P'` ... In each `σ^l`-template of a group keep only the
central large child and the `4N` small annular groups directly adjacent to it, and scatter every
other group in the template back to its original `P`-tiles."  The non-central grouped children of
every retained template are the `4N` translated small catalogue groups, which are never large
central images and have at most `Qmax` listed sides (`lem:quantitative-sector`). -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub2_templates
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ) :
    ∃ retained : ℕ → g.GS.G.P'.Form → Template g.GS.G.mixed,
      (∀ l α, (retained l α).region = (τ.θ ^ (g.GS.k * l)) • (g.GS.G.P'.disk α).carrier) ∧
      (∀ l α, g.GS.G.mixedScatter (retained l α).children.tiles =
        τ.decomposeIter (g.GS.k * l) (g.GS.G.dissect α).tiles) ∧
      (∀ l α, emcsCentralPlaced τ g l α ∈ (retained l α).children.tiles) ∧
      (∀ l α, ∀ X ∈ (retained l α).children.tiles, X ≠ emcsCentralPlaced τ g l α →
        (∃ p, X.form = Sum.inr p) ∨ SharesSide X (emcsCentralPlaced τ g l α)) ∧
      (∀ l α (_hl : 0 < l), ∀ X ∈ (retained l α).children.tiles,
        X ≠ emcsCentralPlaced τ g l α → ∀ β, X.form ≠ Sum.inl (emcsCentralForm τ g β)) ∧
      (∀ l α (_hl : 0 < l), ∀ X ∈ (retained l α).children.tiles,
        X ≠ emcsCentralPlaced τ g l α → ∀ γ, X.form = Sum.inl γ →
          (g.GS.G.P'.disk γ).n ≤ g.Qmax) ∧
      (∀ α (p : P.Form), (g.GS.G.dissect α).tiles = {⟨p, 0⟩} →
        (g.GS.G.P'.disk α).n ≤ g.Qmax) ∧
      ∃ annulus : ∀ l α, 0 < l →
        AnnularGrouping g.M (g.GS.G.mixedScatter (retained l α).children.tiles)
          (emcsCentre τ g l α) g.N g.R, emcsAnnulusSpec τ g retained annulus := by
  classical
  choose T0 hT0r hT0s hT0c using existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_template_zero τ g
  choose T1 hT1r hT1s hT1c hT1small hT1cases using existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_template_succ τ h g
  choose Ga hGaL hGaP hGaC hGaE using fun m α => existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_annulus_succ τ g m α _ (hT1s m α)
  let retained : ℕ → g.GS.G.P'.Form → Template g.GS.G.mixed := fun l α =>
    Nat.casesOn (motive := fun _ => Template g.GS.G.mixed) l (T0 α) (fun m => T1 m α)
  let annulus : ∀ l α, 0 < l → AnnularGrouping g.M
      (g.GS.G.mixedScatter (retained l α).children.tiles) (emcsCentre τ g l α) g.N g.R :=
    fun l α hl => match l, hl with
      | 0, hl => absurd hl (lt_irrefl 0)
      | m + 1, _ => Ga m α
  -- the central form of the successor step is the large form of the central tile
  have hiter : ∀ m α, (emcsCentralForm τ g)^[m + 1] α =
      g.large (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form := by
    intro m α
    rw [Function.iterate_succ_apply']
    rfl
  have hcent : ∀ m α, emcsCentralPlaced τ g (m + 1) α =
      ⟨Sum.inl (g.large (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form),
        emcsCentralAnchor τ g (m + 1) α⟩ := by
    intro m α
    simp only [emcsCentralPlaced, hiter]
  have hsl : ∀ p j q, g.small p j ≠ g.large q := by
    intro p j q hpq
    have := g.catalogue_labels_injective (a₁ := Sum.inr (Sum.inl (p, j))) (a₂ := Sum.inl q) hpq
    exact Sum.inr_ne_inl this
  have hsmall_ne : ∀ m α j,
      (⟨Sum.inl (g.small (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form j),
        emcsCentralAnchor τ g (m + 1) α⟩ : PlacedTile g.GS.G.mixed) ≠ emcsCentralPlaced τ g (m + 1) α := by
    intro m α j hX
    rw [hcent] at hX
    simp only [PlacedTile.mk.injEq, Sum.inl.injEq] at hX
    exact hsl _ _ _ hX.1
  refine ⟨retained, ?_, ?_, ?_, ?_, ?_, ?_, fun α p hα => existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_singleton_sides τ g α
      p hα, annulus,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro l α
    cases l with
    | zero => exact hT0r α
    | succ m => exact hT1r m α
  · intro l α
    cases l with
    | zero => exact hT0s α
    | succ m => exact hT1s m α
  · intro l α
    cases l with
    | zero => show _ ∈ (T0 α).children.tiles; rw [hT0c α]; exact mem_singleton _
    | succ m => exact hT1c m α
  · intro l α X hX hne
    cases l with
    | zero =>
      have hX' : X ∈ (T0 α).children.tiles := hX
      rw [hT0c α] at hX'
      exact absurd hX' hne
    | succ m =>
      rcases hT1cases m α X hX with h1 | ⟨j, rfl⟩ | h3
      · exact absurd h1 hne
      · right
        have := existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_sharesSide_translate (emcsCentralAnchor τ g (m + 1) α)
            (existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_contact τ h g
          (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form j)
        simp only [PlacedTile.translate, vadd_eq_add, add_zero] at this
        rw [hcent]
        exact this
      · exact Or.inl h3
  · intro l α hl X hX hne β
    cases l with
    | zero => exact absurd hl (lt_irrefl 0)
    | succ m =>
      rcases hT1cases m α X hX with h1 | ⟨j, rfl⟩ | ⟨q, hq⟩
      · exact absurd h1 hne
      · intro hf
        simp only [Sum.inl.injEq] at hf
        exact hsl _ _ _ hf
      · rw [hq]; exact Sum.inr_ne_inl
  · intro l α hl X hX hne γ hγ
    cases l with
    | zero => exact absurd hl (lt_irrefl 0)
    | succ m =>
      rcases hT1cases m α X hX with h1 | ⟨j, rfl⟩ | ⟨q, hq⟩
      · exact absurd h1 hne
      · simp only [Sum.inl.injEq] at hγ
        rw [← hγ]
        exact existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_small_sides τ g _ j
      · rw [hq] at hγ; exact absurd hγ Sum.inr_ne_inl
  · intro l α hl
    cases l with
    | zero => exact absurd hl (lt_irrefl 0)
    | succ m =>
      show _ ⊆ interior (T1 m α).region
      rw [hT1r]
      exact existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_margin τ g m α
  · intro l α hl
    cases l with
    | zero => exact absurd hl (lt_irrefl 0)
    | succ m =>
      show _ = (Ga m α).L.faces
      rw [hGaL, hcent, ← g.large_dissect]
      rfl
  · intro l α hl X hX hne _
    cases l with
    | zero => exact absurd hl (lt_irrefl 0)
    | succ m =>
      rcases hT1cases m α X hX with h1 | ⟨j, rfl⟩ | ⟨q, hq⟩
      · exact absurd h1 hne
      · refine ⟨j, ?_⟩
        show _ = ((Ga m α).spokes.piece j).faces
        rw [hGaP, ← g.small_dissect]
        rfl
      · rename_i hβ
        obtain ⟨β, hβ⟩ := hβ
        rw [hq] at hβ; exact absurd hβ Sum.inr_ne_inl
  · intro l α hl j
    cases l with
    | zero => exact absurd hl (lt_irrefl 0)
    | succ m =>
      refine ⟨_, hT1small m α j, hsmall_ne m α j, ?_⟩
      show _ = ((Ga m α).spokes.piece j).faces
      rw [hGaP, ← g.small_dissect]
      rfl
  · intro l α hl j
    cases l with
    | zero => exact absurd hl (lt_irrefl 0)
    | succ m =>
      show ((Ga m α).spokes.piece j).carrier ⊆ _
      rw [hGaC]
      have h1 := (g.annular_quantitative (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form).1 j
      rw [g.Cloc_eq] at h1
      refine (Set.vadd_set_mono h1).trans ?_
      rw [existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_trapezoid]
      rfl
  · intro l α hl
    cases l with
    | zero => exact absurd hl (lt_irrefl 0)
    | succ m =>
      obtain ⟨e, he, hsep⟩ := g.annular_windows (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form
      refine ⟨fun j i => emcsCentralAnchor τ g (m + 1) α +ᵥ e j i, fun j i => hGaE m α j _ (he j i), ?_⟩
      rintro j i j' i' hji _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [dist_vadd_cancel_left]
      exact hsep j i j' i' hji x hx y hy
  · intro l α hl
    cases l with
    | zero => exact absurd hl (lt_irrefl 0)
    | succ m =>
      refine ⟨(emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form, emcsCentralAnchor τ g (m + 1) α,
        ?_, fun j => ⟨j, rfl, hGaP m α j⟩⟩
      rw [hcent, ← g.large_dissect]
      rfl
  · intro m α j
    exact hGaP m α j

private noncomputable def emcsRetained (τ : Substitution P) (h : τ.STS)
    (g : existsMacroCertificate_GroupingSeed τ) : ℕ → g.GS.G.P'.Form → Template g.GS.G.mixed :=
  (existsMacroCertificate_seed2_routing_step1_setup_sub2_templates τ h g).choose

/-- The annulus selected jointly with the retained children. -/
private noncomputable def emcsAnnulus (τ : Substitution P) (h : τ.STS)
    (g : existsMacroCertificate_GroupingSeed τ) : ∀ l α, 0 < l →
        AnnularGrouping g.M (g.GS.G.mixedScatter (emcsRetained τ h g l α).children.tiles)
          (emcsCentre τ g l α) g.N g.R :=
  ((existsMacroCertificate_seed2_routing_step1_setup_sub2_templates τ h g).choose_spec.2.2.2.2.2.2.2).choose

/-- The selected annulus keeps the exact central-chain labels and translation. -/
private lemma emcsAnnulus_canonical (τ : Substitution P) (h : τ.STS)
    (g : existsMacroCertificate_GroupingSeed τ) :
  ∀ m α (j : Fin (4 * g.N)),
    ((emcsAnnulus τ h g (m + 1) α (Nat.succ_pos m)).spokes.piece j).faces =
      translateSet (emcsCentralAnchor τ g (m + 1) α)
        ((g.annular
          (emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α)).form).spokes.piece j).faces :=
  ((existsMacroCertificate_seed2_routing_step1_setup_sub2_templates τ h g).choose_spec.2.2.2.2.2.2.2).choose_spec.2

/-- Step 3 of `lem:certificate-exists` and `lem:quantitative-sector`: translating the catalogue
annular grouping `g.annular p` of the central constituent `p` by `emcsCentralAnchor τ g l α` into
the scattered patch of `emcsRetained τ h g l α` yields the template's `AnnularGrouping` at
`emcsCentre τ g l α`, together with its interior square margin (`g.square_margin`), central and
small piece scatter equations, sector localization (`g.annular_quantitative`), separated private
outer windows (`g.annular_windows`), and the `annulus_catalogue` translation witness. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub3_annulus
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ) :
  (∀ l α (_hl : 0 < l),
        square (emcsCentre τ g l α) ((g.N : ℝ) * g.R / 2 + g.R) + Binf (10 * g.M.D) ⊆
          interior (emcsRetained τ h g l α).region) ∧
      (∀ l α (hl : 0 < l),
        g.GS.G.mixedScatterTile (emcsCentralPlaced τ g l α) = (emcsAnnulus τ h g l α hl).L.faces) ∧
      (∀ l α (hl : 0 < l), ∀ X ∈ (emcsRetained τ h g l α).children.tiles,
        X ≠ emcsCentralPlaced τ g l α → (∃ β, X.form = Sum.inl β) →
          ∃ j : Fin (4 * g.N),
            g.GS.G.mixedScatterTile X = ((emcsAnnulus τ h g l α hl).spokes.piece j).faces) ∧
      (∀ l α (hl : 0 < l) (j : Fin (4 * g.N)),
        ∃ X ∈ (emcsRetained τ h g l α).children.tiles, X ≠ emcsCentralPlaced τ g l α ∧
          g.GS.G.mixedScatterTile X = ((emcsAnnulus τ h g l α hl).spokes.piece j).faces) ∧
      (∀ l α (hl : 0 < l) (j : Fin (4 * g.N)),
        ((emcsAnnulus τ h g l α hl).spokes.piece j).carrier ⊆
          Metric.cthickening (20 * g.M.D)
            (idealTrapezoid (emcsCentre τ g l α) g.N g.R g.M.D (j : ℕ))) ∧
      (∀ l α (hl : 0 < l), ∃ e : Fin (4 * g.N) → Fin 4 → Set Pt,
        (∀ j i, e j i ∈ privateOuterEdges (emcsAnnulus τ h g l α hl) j) ∧
          ∀ j i j' i', (j, i) ≠ (j', i') →
            ∀ x ∈ e j i, ∀ y ∈ e j' i', g.R / 10 ≤ dist x y) ∧
      ∀ l α (hl : 0 < l), ∃ (p : P.Form) (v : Pt),
        g.GS.G.mixedScatterTile (emcsCentralPlaced τ g l α) =
          translateSet v (g.annular p).L.faces ∧
        ∀ j : Fin (4 * g.N), ∃ j' : Fin (4 * g.N), (j : ℕ) = j' ∧
          ((emcsAnnulus τ h g l α hl).spokes.piece j).faces =
            translateSet v ((g.annular p).spokes.piece j').faces := by
  exact ((existsMacroCertificate_seed2_routing_step1_setup_sub2_templates τ h g).choose_spec.2.2.2.2.2.2.2).choose_spec.1

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance`: "at higher powers
`(emcsCentralPlaced τ g (m + 1) α).carrier` lies inside the scaled carrier of the previous central child" (the chosen
centre lies strictly inside the scaled parent). -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance_step3_central_nested
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ) (m : ℕ) (α : g.GS.G.P'.Form) :
    (emcsCentralPlaced τ g (m + 1) α).carrier ⊆
      (τ.θ ^ g.GS.k) • (emcsCentralPlaced τ g m α).carrier := by
  obtain ⟨hq₀, -, hsucc, -, -⟩ :=
    (existsMacroCertificate_seed2_routing_step1_setup_sub1_central_chain τ g).choose_spec.choose_spec
  set q := emcsCentralTile τ g ((emcsCentralForm τ g)^[m] α) with hq
  have hdisk : (g.GS.G.P'.disk (g.large q.form)).carrier ⊆
      (τ.θ ^ g.GS.k) • (P.disk q.form).carrier := by
    rw [← g.GS.G.support_eq, g.large_dissect, g.grouped_power]
    have hsub : support (g.annular q.form).L.faces ⊆ support (τ.supertile g.k q.form) := by
      intro z hz
      simp only [support, Set.mem_iUnion] at hz ⊢
      obtain ⟨A, hA, hz⟩ := hz
      exact ⟨A, (g.annular q.form).L.faces_sub hA, hz⟩
    have hsup : support (τ.supertile g.k q.form) = τ.θ ^ g.k • (P.disk q.form).carrier :=
      (τ.pow g.k g.k_pos).support_eq q.form
    exact hsup ▸ hsub
  have hform : (emcsCentralForm τ g)^[m + 1] α = g.large q.form := by
    rw [Function.iterate_succ_apply']
    rfl
  have hanchor : emcsCentralAnchor τ g (m + 1) α =
      (τ.θ ^ g.GS.k) • (emcsCentralAnchor τ g m α + q.anchor) := by
    rw [g.grouped_power]
    exact hsucc m α
  have hqmem : q.carrier ⊆ (g.GS.G.P'.disk ((emcsCentralForm τ g)^[m] α)).carrier := by
    rw [← g.GS.G.support_eq]
    intro z hz
    simp only [support, Set.mem_iUnion]
    exact ⟨q, hq₀ _, hz⟩
  intro x hx
  simp only [emcsCentralPlaced, PlacedTile.carrier] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.mp hx
  change y ∈ (g.GS.G.P'.disk ((emcsCentralForm τ g)^[m + 1] α)).carrier at hy
  rw [hform] at hy
  obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp (hdisk hy)
  refine Set.mem_smul_set.mpr ⟨emcsCentralAnchor τ g m α + (q.anchor + z), ?_, ?_⟩
  · refine Set.mem_vadd_set.mpr ⟨q.anchor + z, hqmem ?_, rfl⟩
    exact Set.mem_vadd_set.mpr ⟨z, hz, rfl⟩
  · rw [hanchor, vadd_eq_add, ← smul_add, add_assoc]

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance`: "the retained
template of a power `l + 1` is the scaled retained template of the power `l`": its region is
`θ^k • (retained l α).region`. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance_step3_region_succ
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ) (m : ℕ)
    (α : g.GS.G.P'.Form) :
    (emcsRetained τ h g (m + 1) α).region = (τ.θ ^ g.GS.k) • (emcsRetained τ h g m α).region := by
  have hreg := (existsMacroCertificate_seed2_routing_step1_setup_sub2_templates τ h g).choose_spec.1
  unfold emcsRetained
  rw [hreg, hreg, smul_smul, ← pow_add, Nat.mul_succ, add_comm]

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance`: "after
normalization by `θ^{kl}`": scaling by a positive factor `c` multiplies the distance to the (scaled) frontier by `c`
(at least). -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance_step3_infDist_smul
    {c : ℝ} (hc : 0 < c) (y : Pt) (S : Set Pt) :
    c * Metric.infDist y (frontier S) ≤ Metric.infDist (c • y) (frontier (c • S)) := by
  rw [existsRoutingAfterPower_step2_ports_step1_intra_step2_clearance_frontier_smul hc.ne']
  rcases (frontier S).eq_empty_or_nonempty with hF | hF
  · simp [hF]
  · rw [Metric.le_infDist hF.smul_set]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.mp hz
    rw [dist_smul₀, Real.norm_of_nonneg hc.le]
    exact mul_le_mul_of_nonneg_left (Metric.infDist_le_dist_of_mem hw) hc.le

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance`: "at `l = 1`
the central child `L_{q₀}` lies inside `square (centre p) (N R / 2 + R)` which has clearance `R` from the frontier of
`(retained 1 α).region` by `g.square_margin`" (here for every power `l > 0`, from the annulus of the retained
template). -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance_step3_base
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ) (l : ℕ) (hl : 0 < l)
    (α : g.GS.G.P'.Form) :
    ∀ x ∈ (emcsCentralPlaced τ g l α).carrier,
      g.R ≤ Metric.infDist x (frontier (emcsRetained τ h g l α).region) := by
  obtain ⟨hsq, hL, -⟩ := existsMacroCertificate_seed2_routing_step1_setup_sub3_annulus τ h g
  have hD := g.M.D_pos
  have hR : 0 ≤ g.R := le_trans (mul_nonneg g.constants_pos.1.le hD.le) g.R_separates
  have hcar : (emcsCentralPlaced τ g l α).carrier = (emcsAnnulus τ h g l α hl).L.carrier := by
    rw [FaceGroup.carrier, (emcsAnnulus τ h g l α hl).L.carrier_eq, ← hL l α hl]
    simp only [emcsCentralPlaced, GroupedFamily.mixedScatterTile, Sum.elim_inl, PlacedTile.carrier]
    rw [emcg_support_translateSet, g.GS.G.support_eq]
  have hup := (emcsAnnulus τ h g l α hl).L_upper
  have hin := hsq l α hl
  set e := emcsCentre τ g l α
  set Ω := (emcsRetained τ h g l α).region
  have hcpt : IsCompact Ω := by
    have hreg := (existsMacroCertificate_seed2_routing_step1_setup_sub2_templates τ h g).choose_spec.1
    change IsCompact ((existsMacroCertificate_seed2_routing_step1_setup_sub2_templates τ h g).choose l α).region
    rw [hreg]
    exact (g.GS.G.P'.disk α).compact.smul _
  have heΩ : e ∈ Ω := by
    refine interior_subset (hin ⟨e, ?_, 0, ?_, add_zero e⟩)
    · have hN : (0 : ℝ) ≤ (g.N : ℝ) * g.R / 2 + g.R := by positivity
      exact ⟨by simpa using hN, by simpa using hN⟩
    · have h10 : (0 : ℝ) ≤ 10 * g.M.D := by positivity
      exact ⟨by simpa using h10, by simpa using h10⟩
  have hF : (frontier Ω).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hfe
    rcases isClopen_iff.mp (isClopen_iff_frontier_eq_empty.mpr hfe) with h0 | h1
    · exact (Set.eq_empty_iff_forall_notMem.mp h0) e heΩ
    · exact noncompact_univ Pt (h1 ▸ hcpt)
  intro x hx
  rw [hcar] at hx
  obtain ⟨u, hu, v, hv, rfl⟩ := hup hx
  rw [Metric.le_infDist hF]
  intro y hy
  by_contra hlt
  push_neg at hlt
  have hc : ∀ i : Fin 2, |y i - (u + v) i| ≤ g.R := by
    intro i
    have h1 := PiLp.norm_apply_le (y - (u + v)) i
    rw [dist_comm, dist_eq_norm] at hlt
    simp only [Real.norm_eq_abs] at h1
    exact le_trans h1 hlt.le
  have hyin : y ∈ interior Ω := by
    refine hin ⟨u + (y - (u + v)), ?_, v, ?_, by abel_nf⟩
    · constructor
      · have := hc 0
        have := hu.1
        simp only [PiLp.add_apply, PiLp.sub_apply] at *
        calc |u 0 + (y 0 - (u 0 + v 0)) - e 0| = |(u 0 - e 0) + (y 0 - (u 0 + v 0))| := by ring_nf
          _ ≤ |u 0 - e 0| + |y 0 - (u 0 + v 0)| := abs_add_le _ _
          _ ≤ _ := by linarith
      · have := hc 1
        have := hu.2
        simp only [PiLp.add_apply, PiLp.sub_apply] at *
        calc |u 1 + (y 1 - (u 1 + v 1)) - e 1| = |(u 1 - e 1) + (y 1 - (u 1 + v 1))| := by ring_nf
          _ ≤ |u 1 - e 1| + |y 1 - (u 1 + v 1)| := abs_add_le _ _
          _ ≤ _ := by linarith
    · exact ⟨le_trans hv.1 (by linarith), le_trans hv.2 (by linarith)⟩
  exact hy.2 hyin

/-- Step 3 of `lem:certificate-exists`: "The retained centre is strictly interior": because at
`l = 1` the central child `L_{q₀}` lies inside `square (centre p) (N R / 2 + R)` which has
`L∞`-clearance `R` from the frontier of `(retained 1 α).region` by `g.square_margin`, and at
higher powers `(emcsCentralPlaced τ g (m + 1) α).carrier` lies inside the scaled carrier of the
previous central child, the central child has uniform normalized clearance `ρ = g.R / τ.θ ^ g.GS.k`
for all `l ≥ 1`. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ l α, 0 < l → ∀ x ∈ (emcsCentralPlaced τ g l α).carrier,
      ρ * τ.θ ^ (g.GS.k * l) ≤
        Metric.infDist x (frontier (emcsRetained τ h g l α).region) := by
  have hθ : 0 < τ.θ ^ g.GS.k := pow_pos (by linarith [τ.one_lt]) _
  have hR : 0 < g.R :=
    lt_of_lt_of_le (mul_pos g.constants_pos.1 g.M.D_pos) g.R_separates
  refine ⟨g.R / τ.θ ^ g.GS.k, div_pos hR hθ, ?_⟩
  intro l α hl
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  clear hl
  induction m generalizing α with
  | zero =>
    intro x hx
    rw [zero_add, mul_one, div_mul_cancel₀ _ hθ.ne']
    exact existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance_step3_base τ h g 1 one_pos α x hx
  | succ m ih =>
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp
      (existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance_step3_central_nested τ g (m + 1) α hx)
    rw [existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance_step3_region_succ τ h g (m + 1) α]
    refine le_trans ?_ (existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance_step3_infDist_smul hθ y _)
    calc g.R / τ.θ ^ g.GS.k * τ.θ ^ (g.GS.k * (m + 1 + 1))
        = τ.θ ^ g.GS.k * (g.R / τ.θ ^ g.GS.k * τ.θ ^ (g.GS.k * (m + 1))) := by
          rw [Nat.mul_succ, pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (ih α y hy) hθ.le

/-- Step 1 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots`:
"the ray from the centre through the middle of the sector `T_{j_k}`" -- the cross products of the
middle point `v(jR + R/2)` of the `j`-th length-`R` window of `∂Q₀` with the window endpoints are
`A R / 2`, the middle point lies on `∂Q₀` (one coordinate of sup-norm exactly `A`). -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step1_mid_window
    (A R u : ℝ) (k : ℕ) (hk : k < 4) (hA : 0 < A) (hR : 0 < R)
    (hu1 : 2 * k * A ≤ u) (hu2 : u + R ≤ 2 * (k + 1) * A) :
    jcr (squarePerimeterPoint A u) (squarePerimeterPoint A (u + R / 2)) = A * R / 2 ∧
    jcr (squarePerimeterPoint A (u + R / 2)) (squarePerimeterPoint A (u + R)) = A * R / 2 ∧
    (|squarePerimeterPoint A (u + R / 2) 0| ≤ A ∧ |squarePerimeterPoint A (u + R / 2) 1| ≤ A) ∧
    (|squarePerimeterPoint A (u + R / 2) 0| = A ∨ |squarePerimeterPoint A (u + R / 2) 1| = A) := by
  interval_cases k <;> norm_num at hu1 hu2
  · rw [step5_spp0 (t := u) (by linarith), step5_spp0 (t := u + R / 2) (by linarith),
      step5_spp0 (t := u + R) (by linarith)]
    simp only [jcr, rg_mkPt0, rg_mkPt1]
    refine ⟨by ring, by ring, ⟨by rw [abs_of_pos hA], abs_le.2 ⟨by linarith, by linarith⟩⟩,
      Or.inl (abs_of_pos hA)⟩
  · rw [step5_spp1 (t := u) (by linarith) (by linarith),
      step5_spp1 (t := u + R / 2) (by linarith) (by linarith),
      step5_spp1 (t := u + R) (by linarith) (by linarith)]
    simp only [jcr, rg_mkPt0, rg_mkPt1]
    refine ⟨by ring, by ring, ⟨abs_le.2 ⟨by linarith, by linarith⟩, by rw [abs_of_pos hA]⟩,
      Or.inr (abs_of_pos hA)⟩
  · rw [step5_spp2 hA.le (t := u) (by linarith) (by linarith),
      step5_spp2 hA.le (t := u + R / 2) (by linarith) (by linarith),
      step5_spp2 hA.le (t := u + R) (by linarith) (by linarith)]
    simp only [jcr, rg_mkPt0, rg_mkPt1]
    refine ⟨by ring, by ring, ⟨by rw [abs_neg, abs_of_pos hA], abs_le.2 ⟨by linarith, by linarith⟩⟩,
      Or.inl (by rw [abs_neg, abs_of_pos hA])⟩
  · rw [step5_spp3 hA.le (t := u) (by linarith), step5_spp3 hA.le (t := u + R / 2) (by linarith),
      step5_spp3 hA.le (t := u + R) (by linarith)]
    simp only [jcr, rg_mkPt0, rg_mkPt1]
    refine ⟨by ring, by ring, ⟨abs_le.2 ⟨by linarith, by linarith⟩, by rw [abs_neg, abs_of_pos hA]⟩,
      Or.inr (by rw [abs_neg, abs_of_pos hA])⟩

/-- Step 1 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots`:
"for each `j_k` the contact side of the central child met by the ray from the centre through the
middle of the sector `T_{j_k}`" -- the ray from `c` through the middle point of the `j`-th window
of `∂Q₀` leaves the inside-anchored group `L` (which lies between `Q₀` and `Q₀ + B∞(D)`) at a
point of `∂L` lying in the ideal sector `T_j` and `50 D`-far from every other ideal sector. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step1_ray_exit
    {M : MeshConstants P} {S : Set (PlacedTile P)} {c : Pt} {N : ℕ} {R : ℝ} (hN : 2 ≤ N)
    (hR : 1000 * M.D ≤ R) (G : AnnularGrouping M S c N R) (j : Fin (4 * N)) :
    ∃ y ∈ frontier G.L.carrier, y ∈ idealTrapezoid c N R M.D (j : ℕ) ∧
      ∀ t : Fin (4 * N), t ≠ j →
        ∀ q ∈ idealTrapezoid c N R M.D (t : ℕ), 50 * M.D ≤ dist y q := by
  have hD := M.D_pos
  have hRpos : 0 < R := by linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  obtain ⟨k, hk, hk1, hk2⟩ :
      ∃ k, k < 4 ∧ k * N ≤ (j : ℕ) ∧ (j : ℕ) + 1 ≤ (k + 1) * N := by
    refine ⟨(j : ℕ) / N, (Nat.div_lt_iff_lt_mul (by omega)).2 j.isLt,
      Nat.div_mul_le_self _ _, ?_⟩
    have h1 := Nat.div_add_mod (j : ℕ) N
    have h2 := Nat.mod_lt (j : ℕ) (show N > 0 by omega)
    nlinarith
  have hk1' : (k : ℝ) * N ≤ (j : ℕ) := by exact_mod_cast hk1
  have hk2' : ((j : ℕ) : ℝ) + 1 ≤ ((k : ℝ) + 1) * N := by exact_mod_cast hk2
  have hu1 : 2 * k * ((N : ℝ) * R / 2) ≤ ((j : ℕ) : ℝ) * R := by nlinarith
  have hu2 : ((j : ℕ) : ℝ) * R + R ≤ 2 * (k + 1) * ((N : ℝ) * R / 2) := by nlinarith
  obtain ⟨hj1, hj2, ⟨hb0, hb1⟩, hside⟩ :=
    existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step1_mid_window
      _ _ _ k hk hA hRpos hu1 hu2
  set A := (N : ℝ) * R / 2 with hAdef
  set u := ((j : ℕ) : ℝ) * R with hudef
  set s := squarePerimeterPoint A (u + R / 2) with hsdef
  let γ : ℝ → Pt := fun μ => c + μ • s
  have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hγc : ∀ μ, γ μ - c = μ • s := fun μ => by simp [γ]
  have hγi : ∀ μ i, γ μ i - c i = μ * s i := fun μ i => by simp [γ]
  have h0 : γ 1 ∈ G.L.carrier := by
    apply G.L_lower
    refine ⟨?_, ?_⟩
    · rw [hγi, one_mul]; exact hb0
    · rw [hγi, one_mul]; exact hb1
  have hpos : (0 : ℝ) ≤ 3 * M.D / A := by positivity
  have hmul : (1 + 3 * M.D / A) * A = A + 3 * M.D := by field_simp
  have h1 : γ (1 + 3 * M.D / A) ∉ G.L.carrier := by
    intro hmem
    have hsq := step5_square_add_subset (G.L_upper hmem)
    obtain ⟨hs0, hs1⟩ := hsq
    rw [hγi, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + 3 * M.D / A)] at hs0 hs1
    rcases hside with h | h
    · rw [h, hmul] at hs0; linarith
    · rw [h, hmul] at hs1; linarith
  obtain ⟨μ, ⟨hμ1, hμ2⟩, hy⟩ := step5_frontier_hit hγ (by linarith) h0 h1
  refine ⟨γ μ, hy, ⟨u + R / 2, ⟨by linarith, by linarith⟩, μ, ⟨hμ1, ?_⟩, rfl⟩, ?_⟩
  · rw [le_div_iff₀ hA]
    nlinarith
  · intro t ht q hq
    have hjs : ∀ a b : Pt, jcr a (μ • b) = μ * jcr a b ∧ jcr (μ • b) a = μ * jcr b a := by
      intro a b
      simp only [jcr, PiLp.smul_apply, smul_eq_mul]
      constructor <;> ring
    have hAR : 0 < A * R := by positivity
    have hc1 : 3 * A * R / 16 ≤ jcr (squarePerimeterPoint A u) (γ μ - c) := by
      rw [hγc, (hjs _ _).1, hj1]
      nlinarith
    have hc2 : 3 * A * R / 16 ≤ jcr (γ μ - c) (squarePerimeterPoint A (u + R)) := by
      rw [hγc, (hjs _ _).2, hj2]
      nlinarith
    have := emcg_window_farFromOthers hN hD hR j k hk hu1 hu2 (γ μ) hc1 hc2 t ht q hq
    linarith

/-- Step 2 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots`:
"the contact side of the central child met by the ray" -- the grouped disk of `g.large p` has the
carrier of `(g.annular p).L`, so every point of `∂L` lies on one of its listed sides. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step2_side_through
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ) (p : P.Form) {y : Pt}
    (hy : y ∈ frontier (g.annular p).L.carrier) :
    ∃ i : Fin (g.GS.G.P'.disk (g.large p)).n, y ∈ (g.GS.G.P'.disk (g.large p)).side i := by
  have hcar : (g.GS.G.P'.disk (g.large p)).carrier = (g.annular p).L.carrier := by
    rw [← g.GS.G.support_eq, g.large_dissect]
    exact (g.annular p).L.carrier_eq.symm
  rw [← hcar, (g.GS.G.P'.disk (g.large p)).frontier_eq, mem_iUnion] at hy
  exact hy

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots`:
"by the sector localization the face across that side lies in the piece `j_k`" -- a listed side of
the grouped disk of `g.large p` passing through a point `50 D`-far from every ideal sector other
than `T_j` is contained in the support of the `j`-th annular piece: every point of the side is a
limit of points outside `L`, which lie in faces of `H` not in `L`, hence (sector localization) in
faces of the `j`-th piece. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step3_contact_support
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ) (p : P.Form)
    (j : Fin (4 * g.N)) (i : Fin (g.GS.G.P'.disk (g.large p)).n) (y : Pt)
    (hyi : y ∈ (g.GS.G.P'.disk (g.large p)).side i)
    (hfar : ∀ t : Fin (4 * g.N), t ≠ j →
      ∀ q ∈ idealTrapezoid (g.centre p) g.N g.R g.M.D (t : ℕ), 50 * g.M.D ≤ dist y q) :
    (g.GS.G.P'.disk (g.large p)).side i ⊆ support ((g.annular p).spokes.piece j).faces := by
  have hD := g.M.D_pos
  have hR : 1000 * g.M.D ≤ g.R := by
    have := g.R_separates
    rw [g.Csep_eq] at this
    exact this
  have hNr : (2 : ℝ) ≤ g.N := by exact_mod_cast g.N_two
  have hA : 0 < (g.N : ℝ) * g.R / 2 := by
    have : 0 < g.R := by linarith
    positivity
  have hloc := (g.annular_quantitative p).1
  rw [g.Cloc_eq] at hloc
  have hcar : (g.GS.G.P'.disk (g.large p)).carrier = (g.annular p).L.carrier := by
    rw [← g.GS.G.support_eq, g.large_dissect]
    exact (g.annular p).L.carrier_eq.symm
  obtain ⟨A, hA', iA, hAe⟩ := g.GS.G.side_whole (g.large p) i
  intro x hx
  have hxy : dist x y ≤ g.M.D :=
    step5_tile_dist_le g.M A (tile_side_subset A iA (by rw [hAe]; exact hx))
      (tile_side_subset A iA (by rw [hAe]; exact hyi))
  have hxfr : x ∈ frontier (g.annular p).L.carrier := by
    rw [← hcar]
    exact pd_segment_subset_frontier _ i hx
  have hxL : x ∈ (g.annular p).L.carrier := by
    rw [← hcar]
    exact pd_frontier_subset_carrier _ (by rw [hcar]; exact hxfr)
  have hpclosed : IsClosed (support ((g.annular p).spokes.piece j).faces) := by
    rw [← ((g.annular p).spokes.piece j).carrier_eq]
    exact ((g.annular p).spokes.piece j).disk.compact.isClosed
  apply hpclosed.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hxcl : x ∈ closure ((g.annular p).L.carrier)ᶜ :=
    (frontier_eq_closure_inter_closure.subset hxfr).2
  obtain ⟨z, hzL, hxz⟩ := Metric.mem_closure_iff.1 hxcl (min ε g.M.D) (lt_min hε hD)
  refine ⟨z, ?_, lt_of_lt_of_le hxz (min_le_left _ _)⟩
  have hxz' : dist x z ≤ g.M.D := le_trans hxz.le (min_le_right _ _)
  have hxsq := step5_square_add_subset ((g.annular p).L_upper hxL)
  have hcoord : ∀ k : Fin 2, |z k - g.centre p k| ≤ (g.N : ℝ) * g.R / 2 + g.R + 2 * g.M.D := by
    intro k
    have h1 : |z k - x k| ≤ g.M.D := by
      have := (step5_coord_lipschitz x k).dist_le_mul z x
      rw [Real.dist_eq, sub_self, sub_zero, NNReal.coe_one, one_mul, dist_comm] at this
      linarith
    have h2 : |x k - g.centre p k| ≤ (g.N : ℝ) * g.R / 2 + g.M.D := by
      fin_cases k
      · exact hxsq.1
      · exact hxsq.2
    calc |z k - g.centre p k| = |(z k - x k) + (x k - g.centre p k)| := by ring_nf
      _ ≤ |z k - x k| + |x k - g.centre p k| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hzH : z ∈ (g.annular p).H.carrier :=
    (g.annular p).H_lower (rg_square_add (by linarith) (by linarith) ⟨hcoord 0, hcoord 1⟩)
  have hzH' : z ∈ support (g.annular p).H.faces := by
    rw [← (g.annular p).H.carrier_eq]
    exact hzH
  obtain ⟨F, hFH, hzF⟩ := mem_support_iff'.1 hzH'
  have hFL : F ∉ (g.annular p).L.faces := by
    intro hFL
    apply hzL
    show z ∈ (g.annular p).L.disk.carrier
    rw [(g.annular p).L.carrier_eq]
    exact carrier_subset_support hFL hzF
  obtain ⟨t, ht, -⟩ :=
    ((g.annular p).spokes.piece_partition F ((g.annular p).H.faces_sub hFH)).1 ⟨hFH, hFL⟩
  by_cases htj : t = j
  · subst htj
    exact carrier_subset_support ht hzF
  · exfalso
    have hzt := hloc t (show z ∈ ((g.annular p).spokes.piece t).disk.carrier by
      rw [((g.annular p).spokes.piece t).carrier_eq]
      exact carrier_subset_support ht hzF)
    rw [Metric.mem_cthickening_iff] at hzt
    have h2 : ENNReal.ofReal (22 * g.M.D) ≤
        Metric.infEDist z (idealTrapezoid (g.centre p) g.N g.R g.M.D (t : ℕ)) := by
      rw [Metric.le_infEDist]
      intro q hq
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      have h3 := hfar t htj q hq
      have h4 := dist_triangle y x q
      have h5 := dist_triangle x z q
      rw [dist_comm] at hxy
      linarith
    have h6 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h2.trans hzt)
    linarith

private lemma emcg_contact_segment_scalar {r s u v : ℝ}
    (h0 : segment ℝ (0 : ℝ) 1 ⊆ segment ℝ r s ∩ segment ℝ u v)
    (heq : ({r, s} : Set ℝ) ∩ segment ℝ u v = {u, v} ∩ segment ℝ r s) :
    segment ℝ r s = segment ℝ u v := by
  have hrs_set : ({r, s} : Set ℝ) = {min r s, max r s} := by
    rcases le_total r s with hrs | hrs
    · simp [min_eq_left hrs, max_eq_right hrs]
    · simp [min_eq_right hrs, max_eq_left hrs, Set.pair_comm]
  have huv_set : ({u, v} : Set ℝ) = {min u v, max u v} := by
    rcases le_total u v with huv | huv
    · simp [min_eq_left huv, max_eq_right huv]
    · simp [min_eq_right huv, max_eq_left huv, Set.pair_comm]
  simp only [segment_eq_Icc'] at h0 ⊢
  norm_num at h0
  rw [hrs_set, huv_set] at heq
  simp only [segment_eq_Icc'] at heq
  let l := min r s
  let R := max r s
  let p := min u v
  let q := max u v
  change Icc l R = Icc p q
  change ({l, R} : Set ℝ) ∩ Icc p q = {p, q} ∩ Icc l R at heq
  have h0' : Icc 0 1 ⊆ Icc l R ∩ Icc p q := by
    intro z hz
    exact ⟨h0.1 hz, h0.2 hz⟩
  have hl0 : l ≤ 0 := (h0' (by simp)).1.1
  have hp0 : p ≤ 0 := (h0' (by simp)).2.1
  have h1R : 1 ≤ R := (h0' (by simp)).1.2
  have h1q : 1 ≤ q := (h0' (by simp)).2.2
  have hlp : l = p := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hp_mem : p ∈ Icc l R := ⟨by linarith, by linarith⟩
      have hp' : p ∈ ({l, R} : Set ℝ) ∩ Icc p q := by
        rw [heq]
        exact ⟨by simp, hp_mem⟩
      rcases (by simpa using hp'.1 : p = l ∨ p = R) with h | h <;> linarith
    · have hl_mem : l ∈ Icc p q := ⟨by linarith, by linarith⟩
      have hl' : l ∈ ({p, q} : Set ℝ) ∩ Icc l R := by
        rw [← heq]
        exact ⟨by simp, hl_mem⟩
      rcases (by simpa using hl'.1 : l = p ∨ l = q) with h | h <;> linarith
  have hRq : R = q := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hR_mem : R ∈ Icc p q := ⟨by linarith, by linarith⟩
      have hR' : R ∈ ({p, q} : Set ℝ) ∩ Icc l R := by
        rw [← heq]
        exact ⟨by simp, hR_mem⟩
      rcases (by simpa using hR'.1 : R = p ∨ R = q) with h | h <;> linarith
    · have hq_mem : q ∈ Icc l R := ⟨by linarith, by linarith⟩
      have hq' : q ∈ ({l, R} : Set ℝ) ∩ Icc p q := by
        rw [heq]
        exact ⟨by simp, hq_mem⟩
      rcases (by simpa using hq'.1 : q = l ∨ q = R) with h | h <;> linarith
  simp [hlp, hRq]

private lemma emcg_contact_segment_eq {a b c d : Pt}
    (hov : OverlapPos (segment ℝ a b) (segment ℝ c d))
    (hend : ({a, b} : Set Pt) ∩ segment ℝ c d = {c, d} ∩ segment ℝ a b) :
    segment ℝ a b = segment ℝ c d := by
  rcases hov with ⟨x, y, hxy, hsub⟩
  have hxa := (hsub (left_mem_segment ℝ x y)).1
  have hya := (hsub (right_mem_segment ℝ x y)).1
  have hxc := (hsub (left_mem_segment ℝ x y)).2
  have hyc := (hsub (right_mem_segment ℝ x y)).2
  have hline : line[ℝ, x, y] = line[ℝ, a, b] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne
      (mem_segment_iff_wbtw.mp hxa).mem_affineSpan
      (mem_segment_iff_wbtw.mp hya).mem_affineSpan hxy
  have hline' : line[ℝ, x, y] = line[ℝ, c, d] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne
      (mem_segment_iff_wbtw.mp hxc).mem_affineSpan
      (mem_segment_iff_wbtw.mp hyc).mem_affineSpan hxy
  let f : ℝ →ᵃ[ℝ] Pt := AffineMap.lineMap x y
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hxy
  have ha : a ∈ line[ℝ, x, y] := hline ▸ left_mem_affineSpan_pair ℝ a b
  have hb : b ∈ line[ℝ, x, y] := hline ▸ right_mem_affineSpan_pair ℝ a b
  have hc : c ∈ line[ℝ, x, y] := hline' ▸ left_mem_affineSpan_pair ℝ c d
  have hd : d ∈ line[ℝ, x, y] := hline' ▸ right_mem_affineSpan_pair ℝ c d
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp ha
  obtain ⟨s, hs⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hb
  obtain ⟨u, hu⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hc
  obtain ⟨v, hv⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hd
  have hfrs : f '' segment ℝ r s = segment ℝ a b := by
    rw [← hr, ← hs, image_segment]
  have hfuv : f '' segment ℝ u v = segment ℝ c d := by
    rw [← hu, ← hv, image_segment]
  have hab (t : ℝ) : f t ∈ segment ℝ a b ↔ t ∈ segment ℝ r s := by
    rw [← hfrs]
    exact ⟨fun ⟨z, hz, he⟩ => hf he ▸ hz, fun ht => ⟨t, ht, rfl⟩⟩
  have hcd (t : ℝ) : f t ∈ segment ℝ c d ↔ t ∈ segment ℝ u v := by
    rw [← hfuv]
    exact ⟨fun ⟨z, hz, he⟩ => hf he ▸ hz, fun ht => ⟨t, ht, rfl⟩⟩
  have hea (t : ℝ) : f t ∈ ({a, b} : Set Pt) ↔ t ∈ ({r, s} : Set ℝ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (ht | ht)
      · left; exact hf (ht.trans hr.symm)
      · right; exact hf (ht.trans hs.symm)
    · rintro (ht | ht)
      · left; exact (congrArg f ht).trans hr
      · right; exact (congrArg f ht).trans hs
  have hec (t : ℝ) : f t ∈ ({c, d} : Set Pt) ↔ t ∈ ({u, v} : Set ℝ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (ht | ht)
      · left; exact hf (ht.trans hu.symm)
      · right; exact hf (ht.trans hv.symm)
    · rintro (ht | ht)
      · left; exact (congrArg f ht).trans hu
      · right; exact (congrArg f ht).trans hv
  have h0 : segment ℝ (0 : ℝ) 1 ⊆ segment ℝ r s ∩ segment ℝ u v := by
    intro t ht
    rw [segment_eq_Icc (by norm_num)] at ht
    have hft : f t ∈ segment ℝ x y := by
      rw [segment_eq_image_lineMap]
      exact ⟨t, ht, rfl⟩
    exact ⟨(hab t).mp (hsub hft).1, (hcd t).mp (hsub hft).2⟩
  have heq : ({r, s} : Set ℝ) ∩ segment ℝ u v = {u, v} ∩ segment ℝ r s := by
    ext t
    constructor
    · intro ht
      have hft : f t ∈ ({a, b} : Set Pt) ∩ segment ℝ c d :=
        ⟨(hea t).mpr ht.1, (hcd t).mpr ht.2⟩
      rw [hend] at hft
      exact ⟨(hec t).mp hft.1, (hab t).mp hft.2⟩
    · intro ht
      have hft : f t ∈ ({c, d} : Set Pt) ∩ segment ℝ a b :=
        ⟨(hec t).mpr ht.1, (hab t).mpr ht.2⟩
      rw [← hend] at hft
      exact ⟨(hea t).mp hft.1, (hcd t).mp hft.2⟩
  have hsides := emcg_contact_segment_scalar h0 heq
  calc
    segment ℝ a b = f '' segment ℝ r s := hfrs.symm
    _ = f '' segment ℝ u v := congrArg (fun z => f '' z) hsides
    _ = segment ℝ c d := hfuv

private lemma emcg_disk_vertex_on_side_endpoint (D : PolygonalDisk)
    (k i : Fin D.n) (h : D.vertex k ∈ D.side i) :
    D.vertex k = D.vertex i ∨ D.vertex k = D.vertex (finRotate D.n i) := by
  by_cases hki : k = i
  · exact Or.inl (congrArg D.vertex hki)
  have hk : D.vertex k ∈ D.side k := by
    rw [PolygonalDisk.side]
    exact left_mem_segment ℝ _ _
  exact (D.simple i k (Ne.symm hki) ⟨h, hk⟩).1

private lemma emcg_disk_side_of_vertex_segment (D : PolygonalDisk) (a b : Fin D.n)
    (hab : D.vertex a ≠ D.vertex b)
    (hfr : segment ℝ (D.vertex a) (D.vertex b) ⊆ frontier D.carrier)
    (hopen : ∀ k, D.vertex k ∉ openSegment ℝ (D.vertex a) (D.vertex b)) :
    ∃ i, D.side i = segment ℝ (D.vertex a) (D.vertex b) := by
  rw [D.frontier_eq] at hfr
  obtain ⟨i, hov⟩ := emcg_exists_overlap (fun i => D.side i)
    (fun i => convex_segment _ _) hab hfr
  refine ⟨i, ?_⟩
  rw [PolygonalDisk.side]
  apply emcg_contact_segment_eq hov
  ext x
  constructor
  · rintro ⟨hx, hxi⟩
    rcases hx with hx | hx
    · subst x
      have he : D.vertex i = D.vertex a ∨ D.vertex i = D.vertex b := by
        by_cases hia : D.vertex i = D.vertex a
        · exact Or.inl hia
        by_cases hib : D.vertex i = D.vertex b
        · exact Or.inr hib
        exact False.elim
          (hopen i (mem_openSegment_of_ne_left_right (fun h => hia h.symm)
            (fun h => hib h.symm) hxi))
      exact ⟨he, left_mem_segment ℝ _ _⟩
    · subst x
      have he : D.vertex (finRotate D.n i) = D.vertex a ∨
          D.vertex (finRotate D.n i) = D.vertex b := by
        by_cases hia : D.vertex (finRotate D.n i) = D.vertex a
        · exact Or.inl hia
        by_cases hib : D.vertex (finRotate D.n i) = D.vertex b
        · exact Or.inr hib
        exact False.elim
          (hopen _ (mem_openSegment_of_ne_left_right (fun h => hia h.symm)
            (fun h => hib h.symm) hxi))
      exact ⟨he, right_mem_segment ℝ _ _⟩
  · rintro ⟨hx, hxab⟩
    rcases hx with hx | hx
    · subst x
      exact ⟨emcg_disk_vertex_on_side_endpoint D a i hxab, left_mem_segment ℝ _ _⟩
    · subst x
      exact ⟨emcg_disk_vertex_on_side_endpoint D b i hxab, right_mem_segment ℝ _ _⟩

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots`:
"the contact side of the central child" is "a whole side" shared with the piece -- a listed side of
the grouped disk of `g.large p` contained in the support of the `j`-th annular piece is a complete
listed side of one of the faces of that piece (the piece and `L` are face groups: their listed
sides are whole original sides and they retain every original vertex on their boundary, so the
piece side running along this side of `L` has the same endpoints). -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step4_contact_edge
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ) (p : P.Form)
    (j : Fin (4 * g.N)) (i : Fin (g.GS.G.P'.disk (g.large p)).n)
    (hsub : (g.GS.G.P'.disk (g.large p)).side i ⊆ support ((g.annular p).spokes.piece j).faces) :
    ∃ B ∈ ((g.annular p).spokes.piece j).faces,
      HasEdge B ((g.GS.G.P'.disk (g.large p)).side i) := by
  classical
  let D := g.GS.G.P'.disk (g.large p)
  let L := (g.annular p).L
  let K := (g.annular p).spokes.piece j
  change Fin D.n at i
  have hDL : D.carrier = L.carrier := by
    dsimp [D, L, FaceGroup.carrier]
    rw [← g.GS.G.support_eq, g.large_dissect]
    exact L.carrier_eq.symm
  obtain ⟨A, hAL, ia, hAe⟩ := g.GS.G.side_whole (g.large p) i
  have hAL' : A ∈ L.faces := by simpa [L] using g.large_dissect p ▸ hAL
  have hdisjFaces : Disjoint L.faces K.faces := by
    rw [Set.disjoint_left]
    intro X hXL hXK
    exact ((g.annular p).spokes.piece_sub j hXK).2 hXL
  have hdisjSupport : Disjoint (interior (support L.faces)) (interior (support K.faces)) :=
    emcg_disjoint_interior_support (emcg_supertile_disjoint τ g.k p) L.faces_sub K.faces_sub
      L.finite K.finite hdisjFaces
  have heFrontier : D.side i ⊆ frontier K.carrier := by
    intro x hx
    apply (mem_frontier_iff_of_closed K.disk.compact.isClosed).2
    constructor
    · change x ∈ K.disk.carrier
      rw [K.carrier_eq]
      exact hsub hx
    · intro hxKi
      have hxD : x ∈ D.carrier := pd_frontier_subset_carrier D
        (emcg_disk_side_subset_frontier D i hx)
      have hxLcl : x ∈ closure (interior (support L.faces)) := by
        rw [← L.carrier_eq, L.disk.regular_closed]
        have hDL' : D.carrier = L.disk.carrier := hDL
        exact hDL' ▸ hxD
      obtain ⟨y, hyK, hyL⟩ := mem_closure_iff.1 hxLcl (interior (support K.faces))
        isOpen_interior (by simpa [FaceGroup.carrier, K.carrier_eq] using hxKi)
      exact Set.disjoint_left.mp hdisjSupport hyL hyK
  have hseg : segment ℝ (A.vertex ia) (A.vertex (finRotate _ ia)) =
      segment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) := by
    simpa [emcg_side_eq_segment, PolygonalDisk.side] using hAe
  have hends := emcg_segment_endpoints hseg
  have hendVertex : ∀ x ∈ ({D.vertex i, D.vertex (finRotate D.n i)} : Set Pt),
      Substitution.IsVertexOf (τ.supertile g.k p) x := by
    intro x hx
    rcases hends with hends | hends
    · rcases hx with rfl | rfl
      · exact ⟨A, L.faces_sub hAL', ia, hends.1⟩
      · exact ⟨A, L.faces_sub hAL', finRotate _ ia, hends.2⟩
    · rcases hx with rfl | rfl
      · exact ⟨A, L.faces_sub hAL', finRotate _ ia, hends.2⟩
      · exact ⟨A, L.faces_sub hAL', ia, hends.1⟩
  have hendK : ∀ x ∈ ({D.vertex i, D.vertex (finRotate D.n i)} : Set Pt),
      x ∈ K.disk.vertexSet := by
    intro x hx
    apply K.vertex_retained x (hendVertex x hx)
    exact heFrontier (by
      rw [PolygonalDisk.side]
      rcases hx with rfl | rfl
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _)
  obtain ⟨a, ha⟩ := hendK (D.vertex i) (by simp)
  obtain ⟨b, hb⟩ := hendK (D.vertex (finRotate D.n i)) (by simp)
  have hab : K.disk.vertex a ≠ K.disk.vertex b := by
    rw [ha, hb]
    intro h
    exact emcg_finRotate_ne (n := D.n) (by have := D.three_le; omega) i
      (D.vertex_injective h).symm
  have hopen : ∀ k, K.disk.vertex k ∉
      openSegment ℝ (K.disk.vertex a) (K.disk.vertex b) := by
    intro k hk
    have hk' : K.disk.vertex k ∈ openSegment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) := by
      simpa [ha, hb] using hk
    obtain ⟨B, hBK, ib, hBside⟩ := K.side_whole k
    have hvS : Substitution.IsVertexOf (τ.supertile g.k p) (K.disk.vertex k) := by
      have hbe := emcg_segment_endpoints (by
        simpa [emcg_side_eq_segment, PolygonalDisk.side] using hBside)
      rcases hbe with hbe | hbe
      · exact ⟨B, K.faces_sub hBK, ib, hbe.1⟩
      · exact ⟨B, K.faces_sub hBK, finRotate _ ib, hbe.2⟩
    have hvLf : K.disk.vertex k ∈ frontier L.disk.carrier := by
      change K.disk.vertex k ∈ frontier L.carrier
      rw [← hDL]
      exact emcg_disk_side_subset_frontier D i (openSegment_subset_segment ℝ _ _ hk')
    obtain ⟨l, hl⟩ := L.vertex_retained _ hvS hvLf
    obtain ⟨C, hCL, ic, hCside⟩ := L.side_whole l
    have hvLarge : Substitution.IsVertexOf (g.GS.G.dissect (g.large p)).tiles
        (K.disk.vertex k) := by
      rw [g.large_dissect]
      have hce := emcg_segment_endpoints (by
        simpa [emcg_side_eq_segment, PolygonalDisk.side] using hCside)
      rcases hce with hce | hce
      · exact ⟨C, hCL, ic, hce.1.trans hl⟩
      · exact ⟨C, hCL, finRotate _ ic, hce.2.trans hl⟩
    obtain ⟨m, hm⟩ := g.GS.G.vertex_retained (g.large p) _ hvLarge (by
      exact emcg_disk_side_subset_frontier D i
        (openSegment_subset_segment ℝ _ _ hk'))
    have := emcg_disk_vertex_on_side_endpoint D m i
      (by rw [hm, PolygonalDisk.side]; exact openSegment_subset_segment ℝ _ _ hk')
    have hdne : D.vertex i ≠ D.vertex (finRotate D.n i) := by
      intro h
      exact emcg_finRotate_ne (n := D.n) (by have := D.three_le; omega) i
        (D.vertex_injective h).symm
    rcases this with hm0 | hm1
    · have hbad : D.vertex i ∈ openSegment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) := by
        exact (hm.symm.trans hm0) ▸ hk'
      exact hdne (left_mem_openSegment_iff.mp hbad)
    · have hbad : D.vertex (finRotate D.n i) ∈
          openSegment ℝ (D.vertex i) (D.vertex (finRotate D.n i)) := by
        exact (hm.symm.trans hm1) ▸ hk'
      exact hdne (right_mem_openSegment_iff.mp hbad)
  obtain ⟨k, hk⟩ := emcg_disk_side_of_vertex_segment K.disk a b hab
    (by simpa [ha, hb, FaceGroup.carrier] using heFrontier) hopen
  obtain ⟨B, hBK, hB⟩ := K.side_whole k
  refine ⟨B, hBK, ?_⟩
  obtain ⟨ib, hib⟩ := hB
  refine ⟨ib, ?_⟩
  rw [hib, hk, ha, hb]
  rfl

/-- Step 1 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order`:
"these sides" are sides of the central child
`L`: the carrier of the grouped disk of `g.large p` is the carrier of the inside-anchored group `L`. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step1_carrier
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ) (p : P.Form) :
    (g.GS.G.P'.disk (g.large p)).carrier = (g.annular p).L.carrier := by
  rw [← g.GS.G.support_eq, g.large_dissect]
  exact (g.annular p).L.carrier_eq.symm

/-- Step 1 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order`:
"these sides" lie on the boundary of the
central child -- a point of a listed side of the grouped disk of `g.large p` lies on the frontier of
`L`. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step1_frontier
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ) (p : P.Form)
    (i : Fin (g.GS.G.P'.disk (g.large p)).n) {y : Pt} (hy : y ∈ (g.GS.G.P'.disk (g.large p)).side i) :
    y ∈ frontier (g.annular p).L.carrier := by
  rw [← existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step1_carrier τ g p]
  exact pd_segment_subset_frontier _ i hy

/-- Step 2 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order`:
the sides are "whole sides" of original
tiles, so two points of one listed side of the grouped disk of `g.large p` are at distance at most
`D`. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step2_side_short
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ) (p : P.Form)
    (i : Fin (g.GS.G.P'.disk (g.large p)).n) {x z : Pt} (hx : x ∈ (g.GS.G.P'.disk (g.large p)).side i)
    (hz : z ∈ (g.GS.G.P'.disk (g.large p)).side i) : dist x z ≤ g.M.D := by
  obtain ⟨A, -, iA, hAe⟩ := g.GS.G.side_whole (g.large p) i
  exact step5_tile_dist_le g.M A (tile_side_subset A iA (by rw [hAe]; exact hx))
    (tile_side_subset A iA (by rw [hAe]; exact hz))

/-- Step 2 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order`:
points selected in distinct sectors are far
apart -- a point within `20 D` of `T_t` and a point `50 D`-far from `T_t` are more than `25 D`
apart. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step2_sep {c ya yb : Pt} {N : ℕ} {R D : ℝ}
    (hD : 0 < D) {t : ℕ} (hya : ya ∈ Metric.cthickening (20 * D) (idealTrapezoid c N R D t))
    (hyb : ∀ q ∈ idealTrapezoid c N R D t, 50 * D ≤ dist yb q) : 25 * D < dist ya yb := by
  have h := Metric.cthickening_subset_thickening' (by linarith : (0 : ℝ) < 25 * D)
    (by linarith : 20 * D < 25 * D) _ hya
  obtain ⟨q, hq, hdq⟩ := Metric.mem_thickening_iff.1 h
  have h1 := hyb q hq
  have h2 := dist_triangle yb ya q
  rw [dist_comm yb ya] at h2
  linarith

open private pgLoop pgL finRotate_val_eq_mod pd_vertex_ne_next from Tilings.Geometry.Grouping.Foundation in
/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order`:
"these sides occur counterclockwise" along
the boundary parametrization -- at parameter `t` the counterclockwise boundary loop of a polygonal
disk lies on the listed side with index `⌊n · fract t⌋`, and any other listed side through that
point is the preceding one. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step3_loop_side (B : PolygonalDisk) (t : ℝ) :
    ∃ h : ⌊(B.n : ℝ) * Int.fract t⌋₊ < B.n, pgLoop (pgL B) t ∈ B.side ⟨_, h⟩ ∧
      ∀ s : Fin B.n, pgLoop (pgL B) t ∈ B.side s →
        (s : ℕ) = ⌊(B.n : ℝ) * Int.fract t⌋₊ ∨ (s : ℕ) + 1 = ⌊(B.n : ℝ) * Int.fract t⌋₊ ∨
          (⌊(B.n : ℝ) * Int.fract t⌋₊ = 0 ∧ (s : ℕ) + 1 = B.n) := by
  have hn : 0 < B.n := by have := B.three_le; omega
  set τ := Int.fract t with hτdef
  have hτ0 : 0 ≤ τ := Int.fract_nonneg t
  have hτ1 : τ < 1 := Int.fract_lt_one t
  have hu0 : 0 ≤ (B.n : ℝ) * τ := mul_nonneg (by positivity) hτ0
  set i := ⌊(B.n : ℝ) * τ⌋₊ with hidef
  have hi1 : (i : ℝ) ≤ B.n * τ := Nat.floor_le hu0
  have hi2 : (B.n : ℝ) * τ < i + 1 := Nat.lt_floor_add_one _
  have hil : i < B.n := by
    have : (B.n : ℝ) * τ < B.n := by
      have := mul_lt_mul_of_pos_left hτ1 (show (0:ℝ) < B.n by exact_mod_cast hn)
      linarith
    have : (i : ℝ) < B.n := lt_of_le_of_lt hi1 this
    exact_mod_cast this
  refine ⟨hil, ?_⟩
  set iF : Fin B.n := ⟨i, hil⟩
  have hlen : (pgL B).length = B.n := by simp [pgL]
  have hget : ∀ k (hk : k < B.n), (pgL B).getD k 0 = B.vertex ⟨k, hk⟩ := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hk)]
    simp [pgL]
  have hnext : (pgL B).getD ((i + 1) % B.n) 0 = B.vertex (finRotate B.n iF) := by
    rw [hget _ (Nat.mod_lt _ hn)]
    congr 1
    ext
    rw [finRotate_val_eq_mod]
  set θ := (B.n : ℝ) * τ - i with hθ
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ < 1 := by linarith
  have hloop : pgLoop (pgL B) t = AffineMap.lineMap (B.vertex iF) (B.vertex (finRotate B.n iF)) θ := by
    simp only [pgLoop, hlen]
    rw [← hτdef, ← hidef, Nat.mod_eq_of_lt hil, hget _ hil, hnext]
  have hmem : pgLoop (pgL B) t ∈ B.side iF := by
    rw [hloop, PolygonalDisk.side, segment_eq_image_lineMap]
    exact ⟨θ, ⟨hθ0, hθ1.le⟩, rfl⟩
  refine ⟨hmem, fun s hs => ?_⟩
  by_cases hsi : s = iF
  · left; rw [hsi]
  have hsub := B.simple iF s (Ne.symm hsi) ⟨hmem, hs⟩
  obtain ⟨h1, h2⟩ := hsub
  have hne : pgLoop (pgL B) t ≠ B.vertex (finRotate B.n iF) := by
    rw [hloop]
    intro h
    have h' : AffineMap.lineMap (B.vertex iF) (B.vertex (finRotate B.n iF)) θ =
        AffineMap.lineMap (B.vertex iF) (B.vertex (finRotate B.n iF)) (1 : ℝ) := by
      rw [h, AffineMap.lineMap_apply_one]
    have := (AffineMap.lineMap_injective ℝ (pd_vertex_ne_next B iF)) h'
    linarith
  have hx : pgLoop (pgL B) t = B.vertex iF := by
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd h1 hne
  rcases h2 with h2 | h2
  · exact absurd (B.vertex_injective (hx.symm.trans h2)) (Ne.symm hsi)
  · have := B.vertex_injective (hx.symm.trans h2)
    have hv := congrArg Fin.val this
    rw [finRotate_val_eq_mod] at hv
    simp only [iF] at hv
    have := s.isLt
    rcases Nat.lt_or_ge (s.val + 1) B.n with h | h
    · rw [Nat.mod_eq_of_lt h] at hv; right; left; omega
    · have : s.val + 1 = B.n := by omega
      rw [this, Nat.mod_self] at hv; right; right; omega

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order`:
"occur counterclockwise in the order" --
three loop parameters in cyclic order within one period give cyclically ordered (distinct) side
indices `⌊n · fract t⌋`. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step3_fract_order {n : ℕ} (hn : 0 < n) {t0 t1 t2 : ℝ}
    (h01 : t0 < t1) (h12 : t1 < t2) (h20 : t2 < t0 + 1)
    (h01' : ⌊(n : ℝ) * Int.fract t0⌋₊ ≠ ⌊(n : ℝ) * Int.fract t1⌋₊)
    (h02' : ⌊(n : ℝ) * Int.fract t0⌋₊ ≠ ⌊(n : ℝ) * Int.fract t2⌋₊)
    (h12' : ⌊(n : ℝ) * Int.fract t1⌋₊ ≠ ⌊(n : ℝ) * Int.fract t2⌋₊) :
    CycLt3 ⌊(n : ℝ) * Int.fract t0⌋₊ ⌊(n : ℝ) * Int.fract t1⌋₊ ⌊(n : ℝ) * Int.fract t2⌋₊ := by
  have hmono : ∀ u v : ℝ, Int.fract u ≤ Int.fract v →
      ⌊(n : ℝ) * Int.fract u⌋₊ ≤ ⌊(n : ℝ) * Int.fract v⌋₊ := fun u v h =>
    Nat.floor_le_floor (mul_le_mul_of_nonneg_left h (by positivity))
  have f0 := Int.floor_le t0
  have f0' := Int.lt_floor_add_one t0
  have g1 := Int.floor_le t1
  have g1' := Int.lt_floor_add_one t1
  have g2 := Int.floor_le t2
  have g2' := Int.lt_floor_add_one t2
  have e1 : ⌊t1⌋ = ⌊t0⌋ ∨ ⌊t1⌋ = ⌊t0⌋ + 1 := by
    have a : ⌊t0⌋ ≤ ⌊t1⌋ := Int.floor_le_floor h01.le
    have b : ⌊t1⌋ ≤ ⌊t0⌋ + 1 := by
      rw [← Int.floor_add_one]; exact Int.floor_le_floor (by linarith)
    omega
  have e2 : ⌊t2⌋ = ⌊t0⌋ ∨ ⌊t2⌋ = ⌊t0⌋ + 1 := by
    have a : ⌊t0⌋ ≤ ⌊t2⌋ := Int.floor_le_floor (by linarith)
    have b : ⌊t2⌋ ≤ ⌊t0⌋ + 1 := by
      rw [← Int.floor_add_one]; exact Int.floor_le_floor (by linarith)
    omega
  have e12 : ⌊t1⌋ ≤ ⌊t2⌋ := Int.floor_le_floor h12.le
  unfold CycLt3
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  · have a := hmono t0 t1 (by simp only [Int.fract, e1]; linarith)
    have b := hmono t1 t2 (by simp only [Int.fract, e1, e2]; linarith)
    omega
  · have a := hmono t0 t1 (by simp only [Int.fract, e1]; linarith)
    have b := hmono t2 t0 (by simp only [Int.fract, e2]; push_cast; linarith)
    omega
  · rw [e1, e2] at e12; omega
  · have a := hmono t1 t2 (by simp only [Int.fract, e1, e2]; linarith)
    have b := hmono t2 t0 (by simp only [Int.fract, e2]; push_cast; linarith)
    omega

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order`:
"in the order of the sectors" survives the
vertex ambiguity -- replacing cyclically ordered indices by themselves or their cyclic predecessors,
without hitting the other indices, keeps the cyclic order. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step3_index_shift {n i0 i1 i2 s0 s1 s2 : ℕ}
    (hi0 : i0 < n) (hi1 : i1 < n) (hi2 : i2 < n) (hc : CycLt3 i0 i1 i2)
    (h0 : s0 = i0 ∨ s0 + 1 = i0 ∨ (i0 = 0 ∧ s0 + 1 = n))
    (h1 : s1 = i1 ∨ s1 + 1 = i1 ∨ (i1 = 0 ∧ s1 + 1 = n))
    (h2 : s2 = i2 ∨ s2 + 1 = i2 ∨ (i2 = 0 ∧ s2 + 1 = n))
    (h01 : s0 ≠ i1) (h02 : s0 ≠ i2) (h10 : s1 ≠ i0) (h12 : s1 ≠ i2) (h20 : s2 ≠ i0) (h21 : s2 ≠ i1) :
    CycLt3 s0 s1 s2 := by
  unfold CycLt3 at *
  omega

open private pgLoop pgL from Tilings.Geometry.Grouping.Foundation in
/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order`:
"these sides occur counterclockwise in the
order" of the points -- if three points appear in this order along the counterclockwise boundary
loop of a polygonal disk, lie on listed sides `s 0, s 1, s 2`, and no listed side contains two of
them, then the side indices are in cyclic order. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step3_side_order (B : PolygonalDisk) (x : Fin 3 → Pt)
    (hord : PointsInOrder (pgLoop (pgL B)) x) (s : Fin 3 → Fin B.n)
    (hx : ∀ k, x k ∈ B.side (s k))
    (hsep : ∀ k l, k ≠ l → ∀ i, x k ∈ B.side i → x l ∉ B.side i) :
    CycLt3 (s 0) (s 1) (s 2) := by
  obtain ⟨t, htm, ht1, htx⟩ := hord
  have hn : 0 < B.n := by have := B.three_le; omega
  have L := fun k => existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step3_loop_side B (t k)
  choose hlt hmem hrel using L
  simp only [htx] at hmem hrel
  have hd : ∀ k l, k ≠ l → ⌊(B.n : ℝ) * Int.fract (t k)⌋₊ ≠ ⌊(B.n : ℝ) * Int.fract (t l)⌋₊ := by
    intro k l hkl he
    apply hsep k l hkl _ (hmem k)
    have := hmem l
    simp only [← he] at this
    exact this
  have hne : ∀ k l, k ≠ l → (s k : ℕ) ≠ ⌊(B.n : ℝ) * Int.fract (t l)⌋₊ := by
    intro k l hkl he
    apply hsep k l hkl _ (hx k)
    have := hmem l
    have e : s k = ⟨_, hlt l⟩ := Fin.ext he
    rw [e]; exact this
  have hc := existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step3_fract_order hn (htm (show (0 : Fin 3) < 1 by decide))
    (htm (show (1 : Fin 3) < 2 by decide))
    (ht1 0 2) (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide))
  exact existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step3_index_shift
    (hlt 0) (hlt 1) (hlt 2) hc (hrel 0 _ (hx 0)) (hrel 1 _ (hx 1)) (hrel 2 _ (hx 2))
    (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 0 (by decide)) (hne 1 2 (by decide))
    (hne 2 0 (by decide)) (hne 2 1 (by decide))

open private quantitativeAnnularGrouping_innerOrder from Tilings.Geometry.Grouping.Foundation in
/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order`:
"by Lemma `inner-sector-order` these sides
occur counterclockwise in the order of the sectors" -- for sectors `a < b < c` the selected sides
are in cyclic order. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step4_sorted
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ) (p : P.Form)
    (side : Fin (4 * g.N) → Fin (g.GS.G.P'.disk (g.large p)).n) (y : Fin (4 * g.N) → Pt)
    (hy : ∀ j, y j ∈ (g.GS.G.P'.disk (g.large p)).side (side j))
    (hloc : ∀ j : Fin (4 * g.N), y j ∈ Metric.cthickening (20 * g.M.D)
      (idealTrapezoid (g.centre p) g.N g.R g.M.D (j : ℕ)))
    (hfar : ∀ j : Fin (4 * g.N), ∀ t : Fin (4 * g.N), t ≠ j →
      ∀ q ∈ idealTrapezoid (g.centre p) g.N g.R g.M.D (t : ℕ), 50 * g.M.D ≤ dist (y j) q)
    (a b c : Fin (4 * g.N)) (hab : a < b) (hbc : b < c) :
    CycLt3 (side a) (side b) (side c) := by
  have hD := g.M.D_pos
  have hR : 1000 * g.M.D ≤ g.R := by
    have := g.R_separates
    rw [g.Csep_eq] at this
    exact this
  set jj : Fin 3 → Fin (4 * g.N) := ![a, b, c] with hjj
  have hmono : StrictMono jj := by
    rw [hjj, Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · exact hab
    · exact hbc
  have hinj : Function.Injective jj := hmono.injective
  have hord := quantitativeAnnularGrouping_innerOrder (g.centre p) g.N_two hR (g.annular p)
    (g.GS.G.P'.disk (g.large p)) (existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step1_carrier τ g p)
    (g.ccw (g.large p)) jj hmono
    (fun k => y (jj k)) (fun k => existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step1_frontier τ g p _ (hy (jj k)))
    (fun k => hloc (jj k)) (fun k => hfar (jj k))
  have hsep : ∀ k l, k ≠ l → ∀ i, y (jj k) ∈ (g.GS.G.P'.disk (g.large p)).side i →
      y (jj l) ∉ (g.GS.G.P'.disk (g.large p)).side i := by
    intro k l hkl i hk hl
    have h1 := existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step2_side_short τ g p i hk hl
    have h2 := existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step2_sep hD (hloc (jj k))
      (hfar (jj l) (jj k) (fun h => hkl (hinj h)))
    linarith
  exact existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step3_side_order _ (fun k => y (jj k)) hord (fun k => side (jj k))
    (fun k => hy (jj k)) hsep

/-- Step 5 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots`:
"by Lemma `inner-sector-order` these sides occur counterclockwise in the order of the sectors, so the
print map preserves cyclic order" -- if each sector `j` selects a listed side `side j` of the
counterclockwise grouped disk of `g.large p` through a point `y j` within `20 D` of the ideal
sector `T_j` and `50 D`-far from every other ideal sector, then `side` preserves `CycLt3`. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ) (p : P.Form)
    (side : Fin (4 * g.N) → Fin (g.GS.G.P'.disk (g.large p)).n) (y : Fin (4 * g.N) → Pt)
    (hy : ∀ j, y j ∈ (g.GS.G.P'.disk (g.large p)).side (side j))
    (hloc : ∀ j : Fin (4 * g.N), y j ∈ Metric.cthickening (20 * g.M.D)
      (idealTrapezoid (g.centre p) g.N g.R g.M.D (j : ℕ)))
    (hfar : ∀ j : Fin (4 * g.N), ∀ t : Fin (4 * g.N), t ≠ j →
      ∀ q ∈ idealTrapezoid (g.centre p) g.N g.R g.M.D (t : ℕ), 50 * g.M.D ≤ dist (y j) q) :
    ∀ j₁ j₂ j₃ : Fin (4 * g.N), CycLt3 j₁ j₂ j₃ → CycLt3 (side j₁) (side j₂) (side j₃) := by
  intro j₁ j₂ j₃ h
  have hs := existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order_step4_sorted τ g p side y hy hloc hfar
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hs j₁ j₂ j₃ (Fin.lt_def.2 h1) (Fin.lt_def.2 h2)
  · have := hs j₂ j₃ j₁ (Fin.lt_def.2 h1) (Fin.lt_def.2 h2)
    unfold CycLt3 at this ⊢
    omega
  · have := hs j₃ j₁ j₂ (Fin.lt_def.2 h1) (Fin.lt_def.2 h2)
    unfold CycLt3 at this ⊢
    omega

/-- Step 6 of the blueprint proof of `existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots`:
"an order-preserving injection between two cyclically ordered boundary families" -- a map between
finite index sets with at least three elements which preserves the cyclic order `CycLt3` is
injective. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step6_injective
    {n m : ℕ} (hn : 3 ≤ n) (f : Fin n → Fin m)
    (h : ∀ a b c : Fin n, CycLt3 a b c → CycLt3 (f a) (f b) (f c)) : Function.Injective f := by
  intro a b hab
  by_contra hne
  obtain ⟨c, hca, hcb⟩ : ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
    by_contra hc
    push_neg at hc
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b} := fun x _ => by
      by_cases hx : x = a
      · simp [hx]
      · simp [hc x hx]
    have h1 := Finset.card_le_card hsub
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    have h2 := Finset.card_le_two (a := a) (b := b)
    omega
  have hval : (a : ℕ) ≠ b := fun h' => hne (Fin.ext h')
  have hca' : (c : ℕ) ≠ a := fun h' => hca (Fin.ext h')
  have hcb' : (c : ℕ) ≠ b := fun h' => hcb (Fin.ext h')
  have key : CycLt3 a b c ∨ CycLt3 b a c := by
    unfold CycLt3; omega
  rcases key with k | k
  · have := h a b c k
    rw [hab] at this
    unfold CycLt3 at this
    omega
  · have := h b a c k
    rw [hab] at this
    unfold CycLt3 at this
    omega

/-- Step 3 of `lem:certificate-exists` and `lem:inner-sector-order`
(`quantitativeAnnularGrouping_innerOrder`): for each original form `p`, the ray from `g.centre p`
through the midpoint of sector `T_j` (perimeter parameter `(j + 1/2) R`) exits `(g.annular p).L`
at a point `50 D`-far from all other sectors, selecting a side `slotSide p j` of `g.large p` shared
with `((g.annular p).spokes.piece j).faces` so that `slotSide p` is injective and preserves
`CycLt3` in the counterclockwise listing `g.ccw (g.large p)`. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ) :
    ∃ slotSide : ∀ p : P.Form, Fin (4 * g.N) → Fin (g.GS.G.P'.disk (g.large p)).n,
      (∀ p, Function.Injective (slotSide p)) ∧
      (∀ p (j₁ j₂ j₃ : Fin (4 * g.N)), CycLt3 j₁ j₂ j₃ →
        CycLt3 (slotSide p j₁) (slotSide p j₂) (slotSide p j₃)) ∧
      ∀ p (j : Fin (4 * g.N)),
        (g.GS.G.P'.disk (g.large p)).side (slotSide p j) ⊆
          support ((g.annular p).spokes.piece j).faces ∧
        ∃ B ∈ ((g.annular p).spokes.piece j).faces,
          HasEdge B ((g.GS.G.P'.disk (g.large p)).side (slotSide p j)) := by
  have hR : 1000 * g.M.D ≤ g.R := by
    have := g.R_separates
    rw [g.Csep_eq] at this
    exact this
  have hray := fun p j =>
    existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step1_ray_exit
      g.N_two hR (g.annular p) j
  choose y hyfr hytr hyfar using hray
  have hside := fun p j =>
    existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step2_side_through
      τ g p (hyfr p j)
  choose side hside using hside
  have hcyc : ∀ p (j₁ j₂ j₃ : Fin (4 * g.N)), CycLt3 j₁ j₂ j₃ →
      CycLt3 (side p j₁) (side p j₂) (side p j₃) := fun p =>
    existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step5_order τ g p
      (side p) (y p) (hside p) (fun j : Fin (4 * g.N) => Metric.self_subset_cthickening _ (hytr p j)) (hyfar p)
  refine ⟨side, fun p => ?_, hcyc, fun p j => ?_⟩
  · exact existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step6_injective
      (by have := g.N_two; omega) (side p) (hcyc p)
  · have hsub :=
      existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step3_contact_support τ g p j
        (side p j) (y p j) (hside p j) (hyfar p j)
    exact ⟨hsub,
      existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots_step4_contact_edge τ g p j
        (side p j) hsub⟩

private noncomputable def emcsSlotSide (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) :
    ∀ p : P.Form, Fin (4 * g.N) → Fin (g.GS.G.P'.disk (g.large p)).n :=
  (existsMacroCertificate_seed2_routing_step1_setup_sub5_contact_slots τ g).choose

/-- Step 3 of `lem:certificate-exists`: the marked sides of a grouped form `α`: on a large
catalogue form `g.large p`, the `4N` designated contact sides `emcsSlotSide τ g p` shared with
the `4N` annular pieces; on every other grouped form (including all small annular pieces and
singleton groups), all listed sides (`Finset.univ`). -/
private noncomputable def emcsMarkedSides (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (α : g.GS.G.P'.Form) :
    Finset (Fin (g.GS.G.P'.disk α).n) := by
  classical
  exact if hα : ∃ p : P.Form, g.large p = α then
    Finset.univ.image (fun j : Fin (4 * g.N) =>
      Fin.cast (by rw [hα.choose_spec]) (emcsSlotSide τ g hα.choose j))
  else
    Finset.univ

/-- Step 3 of `lem:certificate-exists`: under injectivity of `g.large` (implied by the disjoint
centre squares of `existsMacroCertificate_seed1_grouping`), `emcsMarkedSides` marks every side of
every non-central grouped child and of every singleton group, marks `4N` contact sides on every
central image `emcsCentralForm τ g β`, and provides the cyclically ordered print slots `f`,
print neighbours `g'`, and annular piece indices `printPiece` satisfying `PhysicalPrintOrder`
and equal to the identity when the central child has the parent's disk. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup_sub6_marking_and_prints
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (hlarge_inj : Function.Injective g.large) :
    (∀ l α (_hl : 0 < l), ∀ X ∈ (emcsRetained τ h g l α).children.tiles,
      X ≠ emcsCentralPlaced τ g l α → ∀ γ, X.form = Sum.inl γ →
        emcsMarkedSides τ g γ = Finset.univ) ∧
    (∀ α (p : P.Form), (g.GS.G.dissect α).tiles = {⟨p, 0⟩} →
      emcsMarkedSides τ g α = Finset.univ) ∧
    (∀ β, (emcsMarkedSides τ g (emcsCentralForm τ g β)).card = 4 * g.N) ∧
    (∀ β, ∃ (p : P.Form)
        (piece : Fin (g.GS.G.P'.disk (emcsCentralForm τ g β)).n → Fin (4 * g.N)),
      (g.GS.G.dissect (emcsCentralForm τ g β)).tiles = (g.annular p).L.faces ∧
      Set.InjOn piece (emcsMarkedSides τ g (emcsCentralForm τ g β) : Set _) ∧
      ∀ a ∈ emcsMarkedSides τ g (emcsCentralForm τ g β),
        (g.GS.G.P'.disk (emcsCentralForm τ g β)).side a ⊆
          support ((g.annular p).spokes.piece (piece a)).faces) ∧
    ∀ l α (hl : 0 < l),
      ∃ (f : Fin (g.GS.G.P'.disk α).n →
          Fin (g.GS.G.mixed.disk (emcsCentralPlaced τ g l α).form).n)
        (g' : Fin (g.GS.G.P'.disk α).n → PlacedTile g.GS.G.mixed)
        (printPiece : Fin (g.GS.G.P'.disk α).n → Fin (4 * g.N)),
      Set.InjOn f (emcsMarkedSides τ g α : Set _) ∧
      Set.InjOn g' (emcsMarkedSides τ g α : Set _) ∧
      CyclicOrderPreservingOn (emcsMarkedSides τ g α) f ∧
      Set.InjOn printPiece (emcsMarkedSides τ g α : Set _) ∧
      CyclicOrderPreservingOn (emcsMarkedSides τ g α) printPiece ∧
      (∀ a ∈ emcsMarkedSides τ g α,
        g.GS.G.mixedScatterTile (g' a) =
          ((emcsAnnulus τ h g l α hl).spokes.piece (printPiece a)).faces) ∧
      (∀ a ∈ emcsMarkedSides τ g α,
        (f a : ℕ) ∈ (emcsMarkedSides τ g ((emcsCentralForm τ g)^[l] α)).map Fin.valEmbedding) ∧
      PhysicalPrintOrder (emcsRetained τ h g l α).region (g.GS.G.P'.disk α)
        (τ.θ ^ (g.GS.k * l)) (emcsCentralPlaced τ g l α) (emcsMarkedSides τ g α) f ∧
      (g.GS.G.mixed.disk (emcsCentralPlaced τ g l α).form = g.GS.G.P'.disk α →
        ∀ a ∈ emcsMarkedSides τ g α, (f a : ℕ) = a) ∧
      ∀ a ∈ emcsMarkedSides τ g α,
        g' a ∈ (emcsRetained τ h g l α).children.tiles ∧
        g' a ≠ emcsCentralPlaced τ g l α ∧
        HasEdge (g' a) ((emcsCentralPlaced τ g l α).side (f a)) := by
  sorry

/-- Step 3 of `lem:certificate-exists`: "Scattering a group and applying the grouped substitution
to each constituent defines `σ`"; the central child of a template is the inside-anchored group
`L` of the supertile of the constituent nearest the centre, the retained ring its `4N` annular
groups; `N`, `R`, the windows (`g.annular_windows`) and the quantitative clearance (from
`g.square_margin`, iterated along the central chain) are those of the grouping seed, and the print
slots are an order-preserving injection of the marked sides of the parent into the contact sides
of `L` with the pieces (identity on a large parent).  See the blueprint for the detailed proof.

The two new setup clauses are obtained as follows.  `piece_localized` comes from the first conjunct
of `g.annular_quantitative`, translated with the catalogue annulus.  For `printPiece`, list the
marked sides as `a₁ < … < aₘ` in index order and choose distinct pieces `j₁ < … < jₘ` (for a large
parent all `4N` pieces in order; for a non-large parent any increasing selection), then choose for
each `jₖ` a contact side of the central child in the middle of the sector `T_{jₖ}`: a side of `L`
containing the exit point from `L` of the ray from `c` at perimeter parameter `(jₖ + 1/2) R`.
By `piece_localized`, the face across that side belongs to piece `jₖ`.  Thus `printPiece` preserves
cyclic order by construction, as a strictly increasing map on index order, while `f` (the index of
that side in the counterclockwise listing of the central child) preserves cyclic order by
`quantitativeAnnularGrouping_innerOrder`; its `50 D` separation holds because the chosen points
are `R/2 - O(D)` from the other sectors.  Together with `PhysicalPrintOrder` (both disks
counterclockwise), this gives `print_slots`. -/
private lemma existsMacroCertificate_seed2_routing_step1_setup (τ : Substitution P) (h : τ.STS)
    (g : existsMacroCertificate_GroupingSeed τ) :
    Nonempty (existsMacroCertificate_SetupSeed τ g) := by
  obtain ⟨hreg, hscat, hcmem, hothers, hnotlarge, hQchild, hQsing, _⟩ :=
    (existsMacroCertificate_seed2_routing_step1_setup_sub2_templates τ h g).choose_spec
  obtain ⟨hann_in, hc_scat, hs_scat, hp_child, hp_loc, hwin, hann_cat⟩ :=
    existsMacroCertificate_seed2_routing_step1_setup_sub3_annulus τ h g
  have hclear := existsMacroCertificate_seed2_routing_step1_setup_sub4_clearance τ h g
  obtain ⟨hm_child, hm_sing, hm_card, hm_contact, hprints⟩ :=
    existsMacroCertificate_seed2_routing_step1_setup_sub6_marking_and_prints τ h g g.large_injective
  exact ⟨{
    setup := {
      GS := g.GS
      parent_ccw := g.ccw
      c := emcsCentralForm τ g
      markedSides := emcsMarkedSides τ g
      retained := emcsRetained τ h g
      central := emcsCentralPlaced τ g
      region_eq := hreg
      scatter_eq := hscat
      central_mem := hcmem
      central_form := fun _ _ => rfl
      others := hothers
      clearance := hclear
      N := fun _ => g.N
      R := fun _ => g.R
      centre := emcsCentre τ g
      N_two := fun _ => g.N_two
      R_large := fun _ => g.R_routes
      annulus := emcsAnnulus τ h g
      annulus_inside := hann_in
      central_scatter := hc_scat
      small_scatter := hs_scat
      piece_child := hp_child
      piece_localized := hp_loc
      windows := hwin
      print_slots := hprints }
    setup_grouped := rfl
    N_eq := fun _ => rfl
    R_eq := fun _ => rfl
    central_large := fun α => ⟨(emcsCentralTile τ g α).form, g.large_dissect _⟩
    annulus_catalogue := hann_cat
    marked_child := hm_child
    marked_singleton := hm_sing
    marked_large_card := hm_card
    marked_large_contact := hm_contact
    noncentral_not_large := hnotlarge
    sides_le_Qmax_child := hQchild
    sides_le_Qmax_singleton := hQsing }⟩

/-- The routed idempotent power of `lem:routing` (`existsRoutingAfterPower` at `n₀ = 1`):
`l > 0` with `c^[2l] = c^[l]` and routing data for every retained template. -/
private lemma existsMacroCertificate_seed2_routing_step2_power (τ : Substitution P) (h : τ.STS)
    (M : MeshConstants P) (Rs : RoutingSetup τ M) :
    ∃ l : ℕ, 0 < l ∧ Rs.c^[2 * l] = Rs.c^[l] ∧
      ∀ α, Nonempty (RoutingData (Rs.retained l α) (Rs.GS.G.P'.disk α) (τ.θ ^ (Rs.GS.k * l))
        (Rs.central l α) (Rs.markedSides α)
        ((Rs.markedSides (Rs.c^[l] α)).map Fin.valEmbedding)) := by
  obtain ⟨l, -, hl, hidem, hr⟩ := existsRoutingAfterPower τ h M Rs 1
  exact ⟨l, hl, hidem, hr⟩

/-- Step 4 of `lem:certificate-exists`: the finite certificate data `D` built from the retained
templates at the routed power `l`, with the definitional equations that pin every datum to the
construction: the forms are the retained catalogue tiles (translated disks relisted
counterclockwise), the types are the positioned children of the retained templates, kinds are
large / small / original as in the grouping, marking follows the setup, the partner of an inner
side is the other occurrence of the same geometric side in the template and interface identifiers
are injective on edges, the special side of a small type is its designated contact side with the
centre (the print, when it receives one), prints come from the routing's print slots, the outer
lists are the whole outer fine sides in `LexPositive` order, the genuine paths are the occurrence
chains of the routed side lists (both occurrences of every crossed inner side, the print in its
small owner, with the occurrence-level invariants the chains inherit from the routing data), the
fifth and the unmarked paths are singleton ports, `N` and `Qmax` are the chosen constants and
`rankBound` is the largest list length.  (Repair of 16 October 2026 after codex: the destuttered
side projection alone did not pin the chains - adjacent duplicate occurrences were allowed - and
the ownership of the centre, the catalogue form of a type's child and the bijectivity of the side
relabelling were missing; the chain invariants, `central_owner`, `child_form`, `base_form`,
`catalogue_form_injective`, `parentSide_bijective`, `parentSide_cyclic` and `child_sideSet` are now
part of the data; the last two were found missing by Aristotle on (G3)/(G4): without the side
correspondence the five routing ports need not be entries of the outer lists.)  The properties
(G1)--(G7) of `D` are proved from these equations in the following seven lemmas; (G4) is a pure
projection. -/
private structure existsMacroCertificate_CertData (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) where
  l_pos : 0 < l
  central_idempotent : s.setup.c^[2 * l] = s.setup.c^[l]
  D : MacroData P
  rep : existsMacroCertificate_RepresentationData τ (g.k * l) D
  tmpl : existsMacroCertificate_TemplateData D
  -- the catalogue of forms
  baseForm : D.Q.Form → s.setup.GS.G.P'.Form
  catalogueTile : D.Q.Form → PlacedTile s.setup.GS.G.mixed
  disk_carrier : ∀ α, (D.Q.disk α).carrier =
    (pdTranslate (s.setup.GS.G.mixed.disk (catalogueTile α).form)
      (catalogueTile α).anchor).carrier
  disk_vertexSet : ∀ α, (D.Q.disk α).vertexSet =
    (pdTranslate (s.setup.GS.G.mixed.disk (catalogueTile α).form)
      (catalogueTile α).anchor).vertexSet
  disk_ccw : ∀ α, pdCCW (D.Q.disk α)
  scatter_eq : ∀ α, (D.Δ α).tiles = s.setup.GS.G.mixedScatterTile (catalogueTile α)
  originalForm : P.Form → D.Q.Form
  original_tile : ∀ p, catalogueTile (originalForm p) = ⟨Sum.inr p, 0⟩
  original_scatter : ∀ p, (D.Δ (originalForm p)).tiles = {⟨p, 0⟩}
  catalogue_injective : Function.Injective catalogueTile
  grouped_disks_distinct : ∀ α β, D.kind α ≠ .original → D.kind β ≠ .original →
    D.Q.disk α = D.Q.disk β → α = β
  kind_original : ∀ α, D.kind α = .original ↔ ∃ p, (catalogueTile α).form = Sum.inr p
  kind_large : ∀ α, D.kind α = .large ↔
    ∃ β, (catalogueTile α).form = Sum.inl (s.setup.c^[l] β)
  kind_small : ∀ α, D.kind α = .small ↔
    ∃ β γ X, X ∈ (s.setup.retained l β).children.tiles ∧ X ≠ s.setup.central l β ∧
      X.form = Sum.inl γ ∧ (catalogueTile α).form = Sum.inl γ
  -- the positioned types
  templateChild : D.Typ → PlacedTile s.setup.GS.G.mixed
  child_bijective : ∀ α, Set.BijOn templateChild {t | D.owner t = α}
    (s.setup.retained l (baseForm α)).children.tiles
  child_carrier : ∀ t, (D.childTile t).carrier = (templateChild t).carrier
  /-- the listed sides of a type and of its template child are the same segments (the two
  listings of one polygon have the same vertex set) -/
  child_sideSet : ∀ t, Set.range (fun i : D.Side t => D.occSide ⟨t, i⟩) =
    Set.range (fun j => (templateChild t).side j)
  central_child : ∀ α, templateChild (D.central α) = s.setup.central l (baseForm α)
  central_form : ∀ α, (templateChild (D.central α)).form =
    Sum.inl (s.setup.c^[l] (baseForm α))
  central_owner : ∀ α, D.owner (D.central α) = α
  /-- the mixed form of a type's template child is the catalogue form of its own form -/
  child_form : ∀ t, (templateChild t).form = (catalogueTile (D.form t)).form
  /-- the base form of a grouped catalogue form is that grouped form; of an original singleton
  the grouped singleton form -/
  base_form : ∀ α β, (catalogueTile α).form = Sum.inl β → baseForm α = β
  base_original : ∀ p, (s.setup.GS.G.dissect (baseForm (originalForm p))).tiles = {⟨p, 0⟩}
  /-- one catalogue entry per mixed form -/
  catalogue_form_injective : ∀ α β, (catalogueTile α).form = (catalogueTile β).form → α = β
  -- parent sides and marking
  parentSide : ∀ α, Fin (D.Q.disk α).n → Fin (s.setup.GS.G.P'.disk (baseForm α)).n
  parentSide_injective : ∀ α, Function.Injective (parentSide α)
  /-- the relabelling between the two listings of the same disk is a bijection -/
  parentSide_bijective : ∀ α, Function.Bijective (parentSide α)
  /-- both listings are counterclockwise, so the relabelling is a cyclic shift -/
  parentSide_cyclic : ∀ α (a b e : Fin (D.Q.disk α).n), CycLt3 a b e →
    CycLt3 (parentSide α a) (parentSide α b) (parentSide α e)
  parent_side_geometry : ∀ α d, D.macroSide α d =
    (τ.θ ^ (s.setup.GS.k * l)) • (s.setup.GS.G.P'.disk (baseForm α)).side (parentSide α d)
  marked_from_setup : ∀ α d, D.marked α d ↔ parentSide α d ∈ s.setup.markedSides (baseForm α)
  marked_rule_nonlarge : ∀ o : D.SideOcc,
    D.kind (D.form o.1) ≠ .large ∨ D.IsPrint o → D.IsMarked o
  marked_rule_large : ∀ o : D.SideOcc, D.kind (D.owner o.1) = .large →
    D.kind (D.form o.1) = .large → D.IsMarked o → D.IsPrint o
  -- interfaces: the partner of an inner side is the other occurrence of its geometric side
  partner_spec : ∀ o : D.SideOcc, D.IsInner o →
    (D.partner o).1 ≠ o.1 ∧ D.owner (D.partner o).1 = D.owner o.1 ∧
      D.occSide (D.partner o) = D.occSide o
  edge_spec : ∀ o o' : D.SideOcc, D.IsInner o → D.IsInner o' →
    (D.edge o = D.edge o' ↔ o' = o ∨ o' = D.partner o)
  edgeTypes_spec : ∀ o : D.SideOcc, D.IsInner o →
    D.edgeTypes (D.edge o) = (o.1, (D.partner o).1) ∨
      D.edgeTypes (D.edge o) = ((D.partner o).1, o.1)
  -- orientation, outer lists and ranks
  positive_eq : D.IsPositive = LexPositive
  outerList_mem : ∀ α (d : Fin (D.Q.disk α).n) (o : D.SideOcc),
    o ∈ D.outerList α d ↔ D.owner o.1 = α ∧ D.IsOuter o ∧ D.occSide o ⊆ D.macroSide α d
  outerList_nodup : ∀ α d, (D.outerList α d).Nodup
  outerList_sorted : ∀ α d, (D.outerList α d).Pairwise fun o o' =>
    ∃ r : ℝ, 0 < r ∧ D.occMid o' - D.occMid o = r • D.macroSideDir α d
  N_eq : D.N = g.N
  Qmax_eq : D.Qmax = g.Qmax
  rankBound_ge : ∀ α d, (D.outerList α d).length ≤ D.rankBound
  rankBound_is_max : ∀ b, (∀ α d, (D.outerList α d).length ≤ b) → D.rankBound ≤ b
  -- prints and special sides
  /-- Prints use the routing slots, which `RoutingData.print_marked` records as designated marked
  sides of the central form. -/
  print_from_routing : ∀ α d, D.occSide (D.printOcc α d) =
    (s.setup.central l (baseForm α)).side ((routing (baseForm α)).printIdx (parentSide α d))
  print_injective : ∀ α (d d' : Fin (D.Q.disk α).n), D.marked α d → D.marked α d' →
    D.print α d = D.print α d' → d = d'
  print_cyclic : ∀ α (a b e : Fin (D.Q.disk α).n), D.marked α a → D.marked α b →
    D.marked α e → CycLt3 a b e → CycLt3 (D.print α a) (D.print α b) (D.print α e)
  print_inner : ∀ α d, D.marked α d → D.IsInner (D.printOcc α d)
  print_small : ∀ α d, D.marked α d → D.kind (D.form (D.partner (D.printOcc α d)).1) = .small
  special_small : ∀ o : D.SideOcc, D.special o → D.kind (D.form o.1) = .small
  special_unique : ∀ t, D.kind (D.form t) = .small → ∃! i, D.special (D.occ t i)
  special_contact : ∀ o : D.SideOcc, D.special o →
    D.IsInner o ∧ (D.partner o).1 = D.central (D.owner o.1)
  special_print : ∀ α d, D.marked α d → D.special (D.partner (D.printOcc α d))
  -- paths: the occurrence chains of the routed side lists
  path_from_routing : ∀ α d (i : Fin 4), D.marked α d →
    @List.destutter (Set Pt) (· ≠ ·) (Classical.decRel _)
      ((D.path α d i.castSucc).map D.occSide) =
      (routing (baseForm α)).pathSides (parentSide α d) i
  path_head : ∀ α d i, D.IsGenuinePath α d i → (D.path α d i).head? = D.port α d i
  path_last : ∀ α d i, D.IsGenuinePath α d i →
    (D.path α d i).getLast? = some (D.partner (D.printOcc α d))
  path_chain : ∀ α d i (n : ℕ) (o o' : D.SideOcc),
    (D.path α d i)[n]? = some o → (D.path α d i)[n + 1]? = some o' →
      o.1 = o'.1 ∨ (D.IsInner o ∧ o' = D.partner o)
  path_owner : ∀ α d i (o : D.SideOcc), o ∈ D.path α d i → D.owner o.1 = α
  path_partner : ∀ α d i, D.IsGenuinePath α d i →
    ∀ o ∈ D.path α d i, D.IsInner o → ¬ D.IsPrint o → D.partner o ∈ D.path α d i
  path_trivial : ∀ α d i, ¬ D.IsGenuinePath α d i → D.path α d i = (D.port α d i).toList
  fifth_path : ∀ α d, D.path α d (4 : Fin 5) = (D.port α d (4 : Fin 5)).toList
  -- the occurrence-level invariants inherited by the chains from the routing data
  path_inner : ∀ α d i, D.IsGenuinePath α d i →
    ∀ (n : ℕ) (o : D.SideOcc), (D.path α d i)[n + 1]? = some o → D.IsInner o
  path_marked : ∀ α d i, D.IsGenuinePath α d i → ∀ o ∈ D.path α d i, D.IsMarked o
  path_not_central : ∀ α d i, D.IsGenuinePath α d i → ∀ o ∈ D.path α d i, o.1 ≠ D.central α
  path_penultimate : ∀ α d i, D.IsGenuinePath α d i →
    ∀ o : D.SideOcc, (D.path α d i)[(D.path α d i).length - 2]? = some o →
      o.1 = (D.partner (D.printOcc α d)).1 ∧ D.IsOrdinary o
  path_nodup : ∀ α d i, (D.path α d i).Nodup
  path_disjoint : ∀ α (d d' : Fin (D.Q.disk α).n) (i i' : Fin 5), (d, i) ≠ (d', i') →
    ∀ o, o ∈ D.path α d i → o ∈ D.path α d' i' →
      d = d' ∧ (o = D.printOcc α d ∨ o = D.partner (D.printOcc α d))

/-- Step 4 of `lem:certificate-exists`: the mixed forms retained in the finite certificate
catalogue `Q`: the original forms `Sum.inr p`, the retained central large forms
`Sum.inl (s.setup.c^[l] β)`, and the non-central grouped children `Sum.inl γ` of the retained
templates at the routed power `l`. -/
private def emcdIsRetainedForm {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (μ : s.setup.GS.G.mixed.Form) : Prop :=
  (∃ p : P.Form, μ = Sum.inr p) ∨
  (∃ β : s.setup.GS.G.P'.Form, μ = Sum.inl (s.setup.c^[l] β)) ∨
  ∃ (β γ : s.setup.GS.G.P'.Form) (X : PlacedTile s.setup.GS.G.mixed),
    X ∈ (s.setup.retained l β).children.tiles ∧ X ≠ s.setup.central l β ∧
      X.form = Sum.inl γ ∧ μ = Sum.inl γ

private abbrev emcdForm {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) : Type :=
  { μ : s.setup.GS.G.mixed.Form // emcdIsRetainedForm g s l μ }

/-- Step 4 of `lem:certificate-exists`: the grouped base form in `s.setup.GS.G.P'.Form`
associated to each retained catalogue form: `γ` on a grouped form `Sum.inl γ`, and the
singleton grouped form `g.original p` (transported along `s.setup_grouped`) on `Sum.inr p`. -/
private def emcdBaseForm {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (α : emcdForm g s l) : s.setup.GS.G.P'.Form :=
  match α.1 with
  | Sum.inl γ => γ
  | Sum.inr p => s.setup_grouped.symm ▸ g.original p

/-- Step 4 of `lem:certificate-exists`: the retained protoset `Q` of the macrocertificate,
equipping each retained form `α` with the counterclockwise disk of `emcdBaseForm g s l α`. -/
private noncomputable def emcdQ {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) : Protoset where
  Form := emcdForm g s l
  fintype := @Subtype.fintype _ _ (Classical.decPred _) inferInstance
  decEq := Classical.decEq _
  disk α := s.setup.GS.G.P'.disk (emcdBaseForm g s l α)

/-- Step 4 of `lem:certificate-exists`: the catalogue tile of a retained form `α`, anchored at
the origin with mixed form `α.1`. -/
private def emcdCatalogueTile {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (α : emcdForm g s l) : PlacedTile s.setup.GS.G.mixed :=
  ⟨α.1, 0⟩

/-- Step 4 of `lem:certificate-exists`: the embedding of original forms `p : P.Form` into the
retained catalogue `emcdQ g s l`. -/
private def emcdOriginalForm {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (p : P.Form) : emcdForm g s l :=
  ⟨Sum.inr p, Or.inl ⟨p, rfl⟩⟩

/-- Step 4 of `lem:certificate-exists`: the kind (`.original`, `.large`, or `.small`) of a
retained catalogue form. -/
private noncomputable def emcdKind {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (α : emcdForm g s l) : FormKind :=
  open Classical in
  if ∃ p : P.Form, α.1 = Sum.inr p then .original
  else if ∃ β : s.setup.GS.G.P'.Form, α.1 = Sum.inl (s.setup.c^[l] β) then .large
  else .small

/-- Step 4 of `lem:certificate-exists`: the scattering patch `Δ α` of a retained form `α`. -/
private def emcdDelta {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (α : emcdForm g s l) : Patch P :=
  s.setup.GS.G.dissect (emcdBaseForm g s l α)

/-- Step 4 of `lem:certificate-exists`: the positioned child types `Typ`, indexed by an owner
retained form `α` and a child `X` of the retained template
`s.setup.retained l (emcdBaseForm g s l α)`. -/
private def emcdTyp {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) : Type :=
  Σ α : emcdForm g s l,
    { X : PlacedTile s.setup.GS.G.mixed //
      X ∈ (s.setup.retained l (emcdBaseForm g s l α)).children.tiles }

private def emcdTemplateChild {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (t : emcdTyp g s l) : PlacedTile s.setup.GS.G.mixed :=
  t.2.1

private def emcdOwner {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (t : emcdTyp g s l) : emcdForm g s l :=
  t.1

private def emcdAnchor {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (t : emcdTyp g s l) : Pt :=
  t.2.1.anchor

private def emcdCentral {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (α : emcdForm g s l) : emcdTyp g s l :=
  ⟨α, ⟨s.setup.central l (emcdBaseForm g s l α), s.setup.central_mem l (emcdBaseForm g s l α)⟩⟩

private noncomputable def emcdChildForm {τ : Substitution P}
    (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (t : emcdTyp g s l) : emcdForm g s l :=
  ⟨t.2.1.form, show emcdIsRetainedForm g s l t.2.1.form by
    classical
    by_cases hX : t.2.1 = s.setup.central l (emcdBaseForm g s l t.1)
    · exact Or.inr (Or.inl ⟨emcdBaseForm g s l t.1,
        by rw [hX, s.setup.central_form]⟩)
    · rcases hform : t.2.1.form with γ | p
      · exact Or.inr (Or.inr ⟨emcdBaseForm g s l t.1, γ, t.2.1, t.2.2, hX, hform, rfl⟩)
      · exact Or.inl ⟨p, rfl⟩⟩

private def emcdParentSide {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (α : emcdForm g s l) :
    Fin ((emcdQ g s l).disk α).n → Fin (s.setup.GS.G.P'.disk (emcdBaseForm g s l α)).n :=
  id

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub1_macroData`:
"each with its disk relisted counterclockwise and translated to the origin": the disk of a
retained catalogue form has the same carrier as the mixed disk of its mixed form (for an original
singleton because the singleton group has the original tile as its scattering). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub1_macroData_step4_carrier
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (μ : s.setup.GS.G.mixed.Form)
    (hμ : emcdIsRetainedForm g s l μ) :
    ((emcdQ g s l).disk ⟨μ, hμ⟩).carrier = (s.setup.GS.G.mixed.disk μ).carrier := by
  rcases μ with γ | p
  · rfl
  · show (s.setup.GS.G.P'.disk (s.setup_grouped.symm ▸ g.original p)).carrier = (P.disk p).carrier
    have key : ∀ (GS : GroupedSubstitution τ) (e : GS = g.GS),
        (GS.G.P'.disk (e.symm ▸ g.original p)).carrier = (P.disk p).carrier := by
      intro GS e
      subst e
      rw [← g.GS.G.support_eq, g.original_dissect]
      simp [support, PlacedTile.carrier]
    exact key _ s.setup_grouped

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub1_macroData`:
"The types are the positioned children of the retained templates; the owner of a type is its
template and its anchor is its position": the relabelled child of a type has the carrier of the
template child. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub1_macroData_step4_childCarrier
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (t : emcdTyp g s l) :
    (⟨emcdChildForm g s l t, emcdAnchor g s l t⟩ : PlacedTile (emcdQ g s l)).carrier =
      t.2.1.carrier := by
  simp only [PlacedTile.carrier, emcdAnchor, emcdChildForm]
  rw [existsMacroCertificate_seed2_routing_step3_data_sub1_macroData_step4_carrier]

/-- Relabel the retained template as a substitution on the retained catalogue.  This
choice specifies only the substitution; all finite certificate maps are constructed below. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub1_macroData
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    ∃ σ : Substitution (emcdQ g s l),
      σ.θ = τ.θ ^ (g.k * l) ∧
      ∀ α, (σ.rule α).tiles =
        (fun t => (⟨emcdChildForm g s l t, emcdAnchor g s l t⟩ : PlacedTile (emcdQ g s l))) ''
          {t | emcdOwner g s l t = α} := by
  have hk : s.setup.GS.k = g.k := by rw [s.setup_grouped, g.grouped_power]
  let F : emcdTyp g s l → PlacedTile (emcdQ g s l) :=
    fun t => ⟨emcdChildForm g s l t, emcdAnchor g s l t⟩
  have hF := existsMacroCertificate_seed2_routing_step3_data_sub1_macroData_step4_childCarrier g s l
  have hown : ∀ α : emcdForm g s l, {t | emcdOwner g s l t = α} =
      (fun X => (⟨α, X⟩ : emcdTyp g s l)) '' Set.univ := by
    intro α
    ext ⟨β, X⟩
    simp only [Set.mem_setOf_eq, emcdOwner, Set.image_univ, Set.mem_range]
    constructor
    · rintro rfl; exact ⟨X, rfl⟩
    · rintro ⟨Y, hY⟩; cases hY; rfl
  refine ⟨⟨τ.θ ^ (g.k * l), one_lt_pow₀ τ.one_lt (Nat.mul_ne_zero g.k_pos.ne' hl.ne'),
    fun α => ⟨F '' {t | emcdOwner g s l t = α}, ?_, ?_⟩, ?_⟩, rfl, fun α => rfl⟩
  · rw [hown]
    have : Finite {X : PlacedTile s.setup.GS.G.mixed //
        X ∈ (s.setup.retained l (emcdBaseForm g s l α)).children.tiles} :=
      (s.setup.retained l (emcdBaseForm g s l α)).children.finite.to_subtype
    exact (Set.finite_univ.image _).image _
  · rw [hown]
    rintro _ ⟨_, ⟨X, -, rfl⟩, rfl⟩ _ ⟨_, ⟨Y, -, rfl⟩, rfl⟩ hne
    have hXY : X.1 ≠ Y.1 := by
      intro e
      apply hne
      have : X = Y := Subtype.ext e
      subst this
      rfl
    show Disjoint (interior (F ⟨α, X⟩).carrier) (interior (F ⟨α, Y⟩).carrier)
    rw [hF, hF]
    exact (s.setup.retained l (emcdBaseForm g s l α)).children.disjoint X.2 Y.2 hXY
  · intro α
    show support (F '' {t | emcdOwner g s l t = α}) = _
    rw [hown, ← hk]
    have hreg := (s.setup.retained l (emcdBaseForm g s l α)).support_eq
    rw [s.setup.region_eq] at hreg
    show _ = (τ.θ ^ (s.setup.GS.k * l)) • (s.setup.GS.G.P'.disk (emcdBaseForm g s l α)).carrier
    rw [← hreg]
    ext x
    simp only [support, Set.mem_iUnion, Set.image_univ, Set.mem_image, Set.mem_range,
      exists_prop]
    constructor
    · rintro ⟨_, ⟨_, ⟨X, rfl⟩, rfl⟩, hx⟩
      exact ⟨X.1, X.2, by rw [hF ⟨α, X⟩] at hx; exact hx⟩
    · rintro ⟨X, hX, hx⟩
      exact ⟨F ⟨α, ⟨X, hX⟩⟩, ⟨_, ⟨⟨X, hX⟩, rfl⟩, rfl⟩, by rw [hF ⟨α, ⟨X, hX⟩⟩]; exact hx⟩

/-- The other occurrence of the same geometric side in the same template.  The
fallback is used only when there is no opposite occurrence (in particular on outer sides).
For inner sides, side-to-side disjointness gives existence and uniqueness. -/
private noncomputable def emcdGeometricPartner (D : MacroData P) (o : D.SideOcc) :
    D.SideOcc :=
  open Classical in
  if hex : ∃ o' : D.SideOcc, o'.1 ≠ o.1 ∧ D.owner o'.1 = D.owner o.1 ∧
      D.occSide o' = D.occSide o then hex.choose else o

/-- An interface is represented by the lesser of its two occurrences in a fixed
finite enumeration.  Unlike an unconstrained edge map, this identifies exactly the pair. -/
private noncomputable def emcdGeometricEdge (D : MacroData P) (o : D.SideOcc) :
    D.SideOcc :=
  let index := Fintype.equivFin D.SideOcc
  if index o ≤ index (emcdGeometricPartner D o) then o else emcdGeometricPartner D o

/-- List all whole boundary occurrences, ordered by their midpoint coordinate along
the globally positive parent-side direction. -/
private noncomputable def emcdGeometricOuterList (D : MacroData P)
    (α : D.Q.Form) (d : Fin (D.Q.disk α).n) : List D.SideOcc := by
  classical
  let outer := Finset.univ.filter fun o : D.SideOcc =>
    D.owner o.1 = α ∧ D.IsOuter o ∧ D.occSide o ⊆ D.macroSide α d
  let coordinate := fun o : D.SideOcc =>
    (D.occMid o) 0 * (D.macroSideDir α d) 0 +
      (D.occMid o) 1 * (D.macroSideDir α d) 1
  exact outer.toList.mergeSort fun o o' => decide (coordinate o ≤ coordinate o')

/-- The exact maximum over the finite family of parent-side lists; an empty family
has maximum zero. -/
private noncomputable def emcdGeometricRankBound (D : MacroData P) : ℕ := by
  classical
  exact Finset.univ.sup fun a : Σ α : D.Q.Form, Fin (D.Q.disk α).n =>
    (D.outerList a.1 a.2).length

/-- Choose a special contact on each small type, preferring a print partner whenever
there is one.  Distinct print slots have distinct partner children, so this preference
is consistent.  All other small types have a contact by `RoutingSetup.others`. -/
private noncomputable def emcdGeometricSpecial (D : MacroData P) (o : D.SideOcc) : Prop :=
  open Classical in
  let isPrintPartner := fun i : D.Side o.1 =>
    ∃ d : Fin (D.Q.disk (D.owner o.1)).n, D.marked (D.owner o.1) d ∧
      D.partner (D.printOcc (D.owner o.1) d) = D.occ o.1 i
  let isContact := fun i : D.Side o.1 =>
    D.IsInner (D.occ o.1 i) ∧
      (D.partner (D.occ o.1 i)).1 = D.central (D.owner o.1)
  D.kind (D.form o.1) = .small ∧
    if hp : ∃ i, isPrintPartner i then o.2 = hp.choose
    else if hc : ∃ i, isContact i then o.2 = hc.choose
    else False

/-- Lift a geometric side in a specified routed child to its unique occurrence.
The empty fallback makes this definition total; the routing step equations ensure
that it is never used on an entry or exit of a genuine path. -/
private noncomputable def emcdLiftOccurrence {Q : Protoset} (D : MacroData P)
    (templateChild : D.Typ → PlacedTile Q) (α : D.Q.Form)
    (X : PlacedTile Q) (e : Set Pt) : List D.SideOcc :=
  open Classical in
  if hex : ∃ o : D.SideOcc, D.owner o.1 = α ∧ templateChild o.1 = X ∧
      D.occSide o = e then [hex.choose] else []

/-- Each crossed tile contributes its entry and exit occurrence.  At a crossed
interface the exit of one tile is followed by its partner in the next tile; the
terminal occurrence belongs to the small child, not to the centre. -/
private noncomputable def emcdLiftPath {Q : Protoset} (D : MacroData P)
    (templateChild : D.Typ → PlacedTile Q) (α : D.Q.Form)
    (tiles : List (PlacedTile Q)) (sides : List (Set Pt)) : List D.SideOcc :=
  (tiles.zip (sides.zip sides.tail)).flatMap fun entry =>
    emcdLiftOccurrence D templateChild α entry.1 entry.2.1 ++
      emcdLiftOccurrence D templateChild α entry.1 entry.2.2

/-- The retained catalogue and substitution, before the geometric maps are installed.
This intermediate record is used only for its geometric projections; its placeholder
maps are all overwritten in `emcdMacroData`. -/
private noncomputable def emcdGeometryData (τ : Substitution P) (h : τ.STS)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g)
    (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) : MacroData P :=
  let H := existsMacroCertificate_seed2_routing_step3_data_sub1_macroData τ h g s l hl routing
  let typFin : Fintype (emcdTyp g s l) :=
    @Sigma.instFintype (emcdForm g s l)
      (fun α => { X : PlacedTile s.setup.GS.G.mixed //
        X ∈ (s.setup.retained l (emcdBaseForm g s l α)).children.tiles })
      (fun α => ((s.setup.retained l (emcdBaseForm g s l α)).children.finite).fintype)
      (emcdQ g s l).fintype
  let edgeFin : Fintype
      (Σ t : emcdTyp g s l, Fin ((emcdQ g s l).disk (emcdChildForm g s l t)).n) :=
    @Sigma.instFintype (emcdTyp g s l)
      (fun t => Fin ((emcdQ g s l).disk (emcdChildForm g s l t)).n)
      (fun _ => inferInstance) typFin
  { Q := emcdQ g s l
    Δ := emcdDelta g s l
    σ := H.choose
    kind := emcdKind g s l
    Typ := emcdTyp g s l
    typFintype := typFin
    typDecEq := Classical.decEq _
    form := emcdChildForm g s l
    owner := emcdOwner g s l
    anchor := emcdAnchor g s l
    central := emcdCentral g s l
    EdgeId := Σ t : emcdTyp g s l, Fin ((emcdQ g s l).disk (emcdChildForm g s l t)).n
    edgeFintype := edgeFin
    edgeDecEq := Classical.decEq _
    edge := id
    partner := id
    edgeTypes := fun o => (o.1, o.1)
    marked := fun α d => emcdParentSide g s l α d ∈ s.setup.markedSides (emcdBaseForm g s l α)
    special := fun _ => False
    print := fun α _ => ⟨0, lt_of_lt_of_le (by decide : 0 < 3)
      ((emcdQ g s l).disk (emcdChildForm g s l (emcdCentral g s l α))).three_le⟩
    IsPositive := LexPositive
    outerList := fun _ _ => []
    path := fun _ _ _ => []
    N := g.N
    Qmax := g.Qmax
    rankBound := 0 }

/-- Step 4 of `lem:certificate-exists`: install the geometric interface maps,
transport the routing prints by equality of side segments, sort the boundary lists,
and lift the routed tile/side lists.  Every operational field now has a construction
equation, independent of the proofs of its certificate properties. -/
private noncomputable def emcdMacroData (τ : Substitution P) (h : τ.STS)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g)
    (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) : MacroData P := by
  classical
  let B := emcdGeometryData τ h g s l hl routing
  let print : ∀ α : B.Q.Form, Fin (B.Q.disk α).n → B.Side (B.central α) := fun α d =>
    if hp : ∃ i : B.Side (B.central α), B.occSide ⟨B.central α, i⟩ =
        (s.setup.central l (emcdBaseForm g s l α)).side
          ((routing (emcdBaseForm g s l α)).printIdx (emcdParentSide g s l α d))
    then hp.choose else B.print α d
  let I : MacroData P := { B with
    partner := emcdGeometricPartner B
    edge := emcdGeometricEdge B
    edgeTypes := fun o => (o.1, (emcdGeometricPartner B o).1)
    print := print
    outerList := emcdGeometricOuterList B }
  let S : MacroData P := { I with special := emcdGeometricSpecial I }
  exact { S with
    path := fun α d i =>
      if hi : S.IsGenuinePath α d i then
        emcdLiftPath S (emcdTemplateChild g s l) α
          ((routing (emcdBaseForm g s l α)).pathTiles (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
          ((routing (emcdBaseForm g s l α)).pathSides (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
      else (S.port α d i).toList
    rankBound := emcdGeometricRankBound S }


/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue`:
"every original form is a singleton": a grouped form scattering to the single tile `⟨p, 0⟩` has the
carrier of the original form `p`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_singleton_carrier
    (G : GroupedFamily P) (x : G.P'.Form) (p : P.Form) (hx : (G.dissect x).tiles = {⟨p, 0⟩}) :
    (G.P'.disk x).carrier = (P.disk p).carrier := by
  rw [← G.support_eq x, hx, emcg_support_singleton_zero]

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue`:
"every original form is a singleton": a grouped form scattering to the single tile `⟨p, 0⟩` has the
listed vertex set of the original form `p` (its sides are whole sides of `p`, and it retains every
vertex of `p`). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_singleton_vertexSet
    (G : GroupedFamily P) (x : G.P'.Form) (p : P.Form) (hx : (G.dissect x).tiles = {⟨p, 0⟩}) :
    (G.P'.disk x).vertexSet = (P.disk p).vertexSet := by
  have hcar :=
    existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_singleton_carrier G x p hx
  apply Set.Subset.antisymm
  · rintro _ ⟨j, rfl⟩
    obtain ⟨A, hA, i, hi⟩ := G.side_whole x j
    rw [hx, Set.mem_singleton_iff] at hA
    subst hA
    have hseg : segment ℝ ((P.disk p).vertex i) ((P.disk p).vertex (finRotate _ i)) =
        segment ℝ ((G.P'.disk x).vertex j) ((G.P'.disk x).vertex (finRotate _ j)) := by
      simpa [PlacedTile.side, PolygonalDisk.side] using hi
    rcases emcg_segment_endpoints hseg with ⟨h1, _⟩ | ⟨_, h1⟩
    · exact ⟨i, h1⟩
    · exact ⟨_, h1⟩
  · rintro _ ⟨i, rfl⟩
    apply G.vertex_retained x
    · rw [hx]
      exact ⟨⟨p, 0⟩, rfl, i, by simp [PlacedTile.vertex]⟩
    · rw [hcar, (P.disk p).frontier_eq]
      exact Set.mem_iUnion.2 ⟨i, left_mem_segment ℝ _ _⟩

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue`:
"every original form is a singleton": the base grouped form of the catalogue entry of an original
form `p` scatters to the single tile `⟨p, 0⟩` (transport of `g.original_dissect`). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_original
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (p : P.Form) :
    (s.setup.GS.G.dissect (emcdBaseForm g s l (emcdOriginalForm g s l p))).tiles = {⟨p, 0⟩} := by
  have key : ∀ (GS1 GS2 : GroupedSubstitution τ) (e : GS1 = GS2) (x : GS2.G.P'.Form),
      (GS1.G.dissect (e.symm ▸ x)).tiles = (GS2.G.dissect x).tiles := by
    rintro _ _ rfl x
    rfl
  have h := key _ _ s.setup_grouped (g.original p)
  rw [g.original_dissect] at h
  exact h

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue`:
a set of tiles whose support contains two points further apart than the mesh diameter `D` has at
least two tiles. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_nontrivial_of_far
    (M : MeshConstants P) {S : Set (PlacedTile P)} {x y : Pt}
    (hx : x ∈ support S) (hy : y ∈ support S) (hxy : M.D < dist x y) : S.Nontrivial := by
  simp only [support, Set.mem_iUnion, exists_prop] at hx hy
  obtain ⟨A, hA, hxA⟩ := hx
  obtain ⟨B, hB, hyB⟩ := hy
  refine ⟨A, hA, B, hB, ?_⟩
  rintro rfl
  obtain ⟨x', hx', rfl⟩ := hxA
  obtain ⟨y', hy', rfl⟩ := hyB
  have h1 : dist x' y' ≤ M.D :=
    (Metric.dist_le_diam_of_mem (P.disk A.form).compact.isBounded hx' hy').trans (M.diam_le _)
  simp only [vadd_eq_add, dist_add_left] at hxy
  linarith

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue`:
the inside-anchored group `L` of an annular grouping contains the square `Q₀` of half side
`NR/2 ≥ R > D`, so it has at least two faces. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_L_nontrivial
    {M : MeshConstants P} {S : Set (PlacedTile P)} {c : Pt} {N : ℕ} {R : ℝ}
    (G : AnnularGrouping M S c N R) (hN : 2 ≤ N) (hR : M.D < R) : G.L.faces.Nontrivial := by
  have hD := M.D_pos
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hR0 : 0 ≤ R := by linarith
  have hpos : 0 ≤ (N : ℝ) * R / 2 := by positivity
  apply existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_nontrivial_of_far M
    (x := c) (y := c + mkPt ((N : ℝ) * R / 2) 0)
  · rw [← G.L.carrier_eq]
    exact G.L_lower ⟨by simpa using hpos, by simpa using hpos⟩
  · rw [← G.L.carrier_eq]
    exact G.L_lower ⟨by simp [mkPt, abs_of_nonneg hpos], by simp [mkPt]; positivity⟩
  · rw [dist_self_add_right]
    have : ‖mkPt ((N : ℝ) * R / 2) 0‖ = (N : ℝ) * R / 2 := by
      rw [EuclideanSpace.norm_eq]
      simp [mkPt, Real.sqrt_sq_eq_abs, abs_of_nonneg hpos]
    rw [this]
    nlinarith

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue`:
an annular piece with more than `K₀` private outer edges has at least two faces (a single face has
at most `K₀` sides). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_piece_nontrivial
    {M : MeshConstants P} {S : Set (PlacedTile P)} {c : Pt} {N : ℕ} {R : ℝ}
    (G : AnnularGrouping M S c N R) (j : Fin (4 * N))
    (hcount : (M.K0 : ℝ) + 1 ≤ ((privateOuterEdges G j).ncard : ℝ)) :
    (G.spokes.piece j).faces.Nontrivial := by
  by_contra hnt
  rw [Set.not_nontrivial_iff] at hnt
  have hcount' : M.K0 + 1 ≤ (privateOuterEdges G j).ncard := by exact_mod_cast hcount
  obtain ⟨e0, he0⟩ : (privateOuterEdges G j).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [h, Set.ncard_empty] at hcount'
    omega
  obtain ⟨A, hA, -⟩ := he0.1
  have hsub : privateOuterEdges G j ⊆ Set.range A.side := by
    intro e he
    obtain ⟨B, hB, i, hi⟩ := he.1
    obtain rfl := hnt hB hA
    exact ⟨i, hi⟩
  have h1 := Set.ncard_le_ncard hsub (Set.finite_range _)
  have h2 : (Set.range A.side).ncard ≤ (P.disk A.form).n := by
    rw [← Set.image_univ]
    refine (Set.ncard_image_le (Set.finite_univ)).trans ?_
    simp
  have h3 := M.sides_le A.form
  omega

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue`:
a retained central large form `c^l β` (`l > 0`) is a large catalogue group `L_p`, which is not a
singleton. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_large_nontrivial
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l) (β : s.setup.GS.G.P'.Form) :
    (s.setup.GS.G.dissect (s.setup.c^[l] β)).tiles.Nontrivial := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  obtain ⟨p, hp⟩ := s.central_large (s.setup.c^[m] β)
  rw [hp]
  have hD := g.M.D_pos
  have hK : (0 : ℝ) ≤ g.M.K0 := Nat.cast_nonneg _
  have hR := g.R_routes
  exact existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_L_nontrivial
    (g.annular p) g.N_two (by nlinarith)

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue`:
the form of a non-central grouped child of a retained template (`l > 0`) scatters to a translate of
an annular piece of the catalogue, which has at least `K₀ + 2` private outer edges and hence is
not a singleton. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_small_nontrivial
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l) (β γ : s.setup.GS.G.P'.Form)
    (X : PlacedTile s.setup.GS.G.mixed) (hX : X ∈ (s.setup.retained l β).children.tiles)
    (hXc : X ≠ s.setup.central l β) (hXf : X.form = Sum.inl γ) :
    (s.setup.GS.G.dissect γ).tiles.Nontrivial := by
  obtain ⟨j, hj⟩ := s.setup.small_scatter l β hl X hX hXc ⟨γ, hXf⟩
  obtain ⟨p, v, -, hpiece⟩ := s.annulus_catalogue l β hl
  obtain ⟨j', -, hj'⟩ := hpiece j
  have hsc : s.setup.GS.G.mixedScatterTile X =
      translateSet X.anchor (s.setup.GS.G.dissect γ).tiles := by
    simp [GroupedFamily.mixedScatterTile, hXf]
  have hnt : ((g.annular p).spokes.piece j').faces.Nontrivial := by
    apply existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_piece_nontrivial
    have h1 := (g.annular_quantitative p).2.1 j'
    have h2 := g.private_edges
    linarith
  have ht : (translateSet X.anchor (s.setup.GS.G.dissect γ).tiles).Nontrivial := by
    rw [← hsc, hj, hj']
    exact hnt.image (emcg_translate_injective v)
  exact Set.nontrivial_of_image _ _ ht

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue`:
distinct non-singleton grouped forms of the routing setup have distinct disks
(`g.grouped_disks_distinct`, transported along `s.setup_grouped`). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_disks_distinct
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (α β : s.setup.GS.G.P'.Form)
    (hα : (s.setup.GS.G.dissect α).tiles.Nontrivial) (hβ : (s.setup.GS.G.dissect β).tiles.Nontrivial)
    (hd : s.setup.GS.G.P'.disk α = s.setup.GS.G.P'.disk β) : α = β := by
  have key := g.grouped_disks_distinct
  rw [← s.setup_grouped] at key
  exact key α β hα hβ hd

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue`:
"a type is large, small or original according as its form is a central image, an annular piece or
an original singleton": a retained form which is not original is a grouped form `Sum.inl γ` whose
group is not a singleton. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_nonoriginal
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l) (α : emcdForm g s l)
    (hα : emcdKind g s l α ≠ .original) :
    ∃ γ, α.1 = Sum.inl γ ∧ (s.setup.GS.G.dissect γ).tiles.Nontrivial := by
  obtain ⟨μ, hμ⟩ := α
  rcases hμ with ⟨p, rfl⟩ | ⟨β, rfl⟩ | ⟨β, γ, X, hX, hXc, hXf, rfl⟩
  · exact absurd (by unfold emcdKind; rw [if_pos ⟨p, rfl⟩]) hα
  · exact ⟨_, rfl,
      existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_large_nontrivial g s l hl β⟩
  · exact ⟨γ, rfl, existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_small_nontrivial
      g s l hl β γ X hX hXc hXf⟩

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue`:
the base form of a grouped catalogue form `Sum.inl β` is `β`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_inl
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (α : emcdForm g s l)
    (β : s.setup.GS.G.P'.Form) (h : α.1 = Sum.inl β) : emcdBaseForm g s l α = β := by
  obtain ⟨μ, hμ⟩ := α
  subst h
  rfl

/-- Step 4 of `lem:certificate-exists`: the catalogue, disk, dissection, and kind equations for
`emcdMacroData`: each retained form has the carrier and vertex set of its catalogue tile,
counterclockwise orientation (`s.setup.parent_ccw`), scattering patch equal to `mixedScatterTile`,
injective catalogue embedding (`catalogue_injective`, `catalogue_form_injective`,
`grouped_disks_distinct`), and disjoint `.original` / `.large` / `.small` classification
(`s.noncentral_not_large`). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α, (D.Q.disk α).carrier =
      (pdTranslate (s.setup.GS.G.mixed.disk (emcdCatalogueTile g s l α).form)
        (emcdCatalogueTile g s l α).anchor).carrier) ∧
    (∀ α, (D.Q.disk α).vertexSet =
      (pdTranslate (s.setup.GS.G.mixed.disk (emcdCatalogueTile g s l α).form)
        (emcdCatalogueTile g s l α).anchor).vertexSet) ∧
    (∀ α, pdCCW (D.Q.disk α)) ∧
    (∀ α, (D.Δ α).tiles = s.setup.GS.G.mixedScatterTile (emcdCatalogueTile g s l α)) ∧
    (∀ p, emcdCatalogueTile g s l (emcdOriginalForm g s l p) = ⟨Sum.inr p, 0⟩) ∧
    (∀ p, (D.Δ (emcdOriginalForm g s l p)).tiles = {⟨p, 0⟩}) ∧
    Function.Injective (emcdCatalogueTile g s l) ∧
    (∀ α β, D.kind α ≠ .original → D.kind β ≠ .original →
      D.Q.disk α = D.Q.disk β → α = β) ∧
    (∀ α, D.kind α = .original ↔ ∃ p, (emcdCatalogueTile g s l α).form = Sum.inr p) ∧
    (∀ α, D.kind α = .large ↔
      ∃ β, (emcdCatalogueTile g s l α).form = Sum.inl (s.setup.c^[l] β)) ∧
    (∀ α, D.kind α = .small ↔
      ∃ β γ X, X ∈ (s.setup.retained l β).children.tiles ∧ X ≠ s.setup.central l β ∧
        X.form = Sum.inl γ ∧ (emcdCatalogueTile g s l α).form = Sum.inl γ) ∧
    (∀ α β, (emcdCatalogueTile g s l α).form = Sum.inl β → emcdBaseForm g s l α = β) ∧
    (∀ p, (s.setup.GS.G.dissect (emcdBaseForm g s l (emcdOriginalForm g s l p))).tiles =
      {⟨p, 0⟩}) ∧
    ∀ α β, (emcdCatalogueTile g s l α).form = (emcdCatalogueTile g s l β).form → α = β := by
  intro D
  have hbase := existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_original g s l
  have hkind_o : ∀ α : emcdForm g s l, emcdKind g s l α = .original ↔ ∃ p, α.1 = Sum.inr p := by
    intro α
    unfold emcdKind
    split_ifs with h1 h2 <;> simp_all
  have hkind_l : ∀ α : emcdForm g s l, emcdKind g s l α = .large ↔
      ∃ β, α.1 = Sum.inl (s.setup.c^[l] β) := by
    intro α
    unfold emcdKind
    split_ifs with h1 h2
    · obtain ⟨p, hp⟩ := h1
      simp [hp]
    · simpa using h2
    · simpa using h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨μ | p, hμ⟩
    · show (s.setup.GS.G.P'.disk μ).carrier = (0 : Pt) +ᵥ (s.setup.GS.G.P'.disk μ).carrier
      rw [zero_vadd]
    · show (s.setup.GS.G.P'.disk (emcdBaseForm g s l (emcdOriginalForm g s l p))).carrier =
        (0 : Pt) +ᵥ (P.disk p).carrier
      rw [zero_vadd]
      exact existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_singleton_carrier
        _ _ p (hbase p)
  · rintro ⟨μ | p, hμ⟩
    · show (s.setup.GS.G.P'.disk μ).vertexSet = (pdTranslate (s.setup.GS.G.P'.disk μ) 0).vertexSet
      simp [pdTranslate, PolygonalDisk.vertexSet]
    · show (s.setup.GS.G.P'.disk (emcdBaseForm g s l (emcdOriginalForm g s l p))).vertexSet =
        (pdTranslate (P.disk p) 0).vertexSet
      rw [existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_singleton_vertexSet
        _ _ p (hbase p)]
      simp [pdTranslate, PolygonalDisk.vertexSet]
  · intro α
    exact s.setup.parent_ccw _
  · rintro ⟨μ | p, hμ⟩
    · show (s.setup.GS.G.dissect μ).tiles = translateSet 0 (s.setup.GS.G.dissect μ).tiles
      rw [emcg_translateSet_zero]
    · exact hbase p
  · intro p
    rfl
  · exact hbase
  · rintro ⟨μ, hμ⟩ ⟨ν, hν⟩ h
    simp only [emcdCatalogueTile, PlacedTile.mk.injEq, and_true] at h
    exact Subtype.ext h
  · intro α β hα hβ hd
    obtain ⟨γ, hγ, hγn⟩ :=
      existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_nonoriginal g s l hl α hα
    obtain ⟨γ', hγ', hγn'⟩ :=
      existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_nonoriginal g s l hl β hβ
    have hd' : s.setup.GS.G.P'.disk γ = s.setup.GS.G.P'.disk γ' := by
      rw [← existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_inl g s l α γ hγ,
        ← existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_inl g s l β γ' hγ']
      exact hd
    have := existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_disks_distinct g s
      γ γ' hγn hγn' hd'
    exact Subtype.ext (hγ.trans (this ▸ hγ'.symm))
  · exact hkind_o
  · exact hkind_l
  · intro α
    have hs : D.kind α = .small ↔ emcdKind g s l α ≠ .original ∧ emcdKind g s l α ≠ .large := by
      show emcdKind g s l α = .small ↔ _
      cases emcdKind g s l α <;> simp
    rw [hs, Ne, Ne, hkind_o, hkind_l]
    show _ ↔ ∃ β γ X, X ∈ (s.setup.retained l β).children.tiles ∧ X ≠ s.setup.central l β ∧
      X.form = Sum.inl γ ∧ α.1 = Sum.inl γ
    obtain ⟨μ, hμ⟩ := α
    constructor
    · rintro ⟨h1, h2⟩
      rcases hμ with ⟨p, rfl⟩ | ⟨β, rfl⟩ | h
      · exact absurd ⟨p, rfl⟩ h1
      · exact absurd ⟨β, rfl⟩ h2
      · exact h
    · rintro ⟨β, γ, X, hX, hXc, hXf, rfl⟩
      refine ⟨fun ⟨p, hp⟩ => (by cases hp), fun ⟨β', hβ'⟩ => ?_⟩
      have hγ : γ = s.setup.c^[l] β' := Sum.inl_injective hβ'
      obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
      rw [Function.iterate_succ_apply'] at hγ
      exact s.noncentral_not_large (m + 1) β hl X hX hXc _ (hXf.trans (congrArg Sum.inl hγ))
  · exact existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_inl g s l
  · exact hbase
  · rintro ⟨μ, hμ⟩ ⟨ν, hν⟩ h
    exact Subtype.ext h

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step1_templateData`:
"each with its disk relisted counterclockwise and translated to the origin": every listed side of
the relabelled child of a type is a listed side of the template child (for an original singleton
because the sides of the singleton group are whole sides of the original tile). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step1_templateData_step4_childSide
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (t : emcdTyp g s l)
    (i : Fin ((emcdQ g s l).disk (emcdChildForm g s l t)).n) :
    ∃ j : Fin (s.setup.GS.G.mixed.disk t.2.1.form).n,
      (⟨emcdChildForm g s l t, emcdAnchor g s l t⟩ : PlacedTile (emcdQ g s l)).side i =
        t.2.1.side j := by
  obtain ⟨α, ⟨μ, an⟩, hX⟩ := t
  simp only [PlacedTile.side, emcdAnchor]
  rcases μ with γ | p
  · exact ⟨i, rfl⟩
  · have hx := existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_original g s l p
    obtain ⟨A, hA, j, hj⟩ := s.setup.GS.G.side_whole (emcdBaseForm g s l (emcdOriginalForm g s l p)) i
    rw [hx, Set.mem_singleton_iff] at hA
    subst hA
    refine ⟨j, ?_⟩
    have hj' : (P.disk p).side j = (s.setup.GS.G.P'.disk (emcdBaseForm g s l (emcdOriginalForm g s l p))).side i := by
      simpa [PlacedTile.side] using hj
    exact congrArg (an +ᵥ ·) hj'.symm

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates`: `D.σ` satisfies
`existsMacroCertificate_TemplateData D`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step1_templateData
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (hidem : s.setup.c^[2 * l] = s.setup.c^[l])
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    existsMacroCertificate_TemplateData D := by
  intro D
  have hσ := (existsMacroCertificate_seed2_routing_step3_data_sub1_macroData τ h g s l hl routing).choose_spec
  have hrule : ∀ α, (D.σ.rule α).tiles =
      (fun t => (⟨emcdChildForm g s l t, emcdAnchor g s l t⟩ : PlacedTile (emcdQ g s l))) ''
        {t | emcdOwner g s l t = α} := hσ.2
  refine ⟨hrule, ?_, ?_⟩
  · rintro ⟨α, X, hX⟩ ⟨α', X', hX'⟩ ho hf ha
    change α = α' at ho
    subst ho
    have hf' : X.form = X'.form := congrArg Subtype.val hf
    have ha' : X.anchor = X'.anchor := ha
    have hXX : X = X' := PlacedTile.ext hf' ha'
    subst hXX
    rfl
  · intro α
    rw [hrule α]
    rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩ i j hov
    obtain ⟨i', hi'⟩ := existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step1_templateData_step4_childSide g s l t i
    obtain ⟨j', hj'⟩ := existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step1_templateData_step4_childSide g s l t' j
    rw [hi', hj'] at hov ⊢
    obtain ⟨β, X, hX⟩ := t
    obtain ⟨β', X', hX'⟩ := t'
    change β = α at ht
    change β' = α at ht'
    subst ht ht'
    exact (s.setup.retained l _).sts X hX X' hX' i' j' hov

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates`:
`emcdTemplateChild` bijects `{t | D.owner t = α}` onto the children of
`s.setup.retained l (emcdBaseForm g s l α)` preserving carriers and side sets. -/
private lemma
    existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step2_children_aux1
    (G : GroupedFamily P) (α : G.P'.Form) (p : P.Form)
    (hsingle : (G.dissect α).tiles = {⟨p, 0⟩}) :
    Set.range (G.P'.disk α).side = Set.range (P.disk p).side := by
  classical
  have hforward : ∀ i, ∃ j, (G.P'.disk α).side i = (P.disk p).side j := by
    intro i
    obtain ⟨A, hA, j, hj⟩ := G.side_whole α i
    have hAeq : A = (⟨p, 0⟩ : PlacedTile P) := by
      rw [hsingle] at hA
      simpa using hA
    subst A
    exact ⟨j, by simpa [PlacedTile.side] using hj.symm⟩
  choose f hf using hforward
  have hfinj : Function.Injective f := by
    intro i j hij
    apply existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_side_injective
    rw [hf i, hf j, hij]
  have hvertices : ∀ i, ∃ j, (G.P'.disk α).vertex j = (P.disk p).vertex i := by
    intro i
    apply G.vertex_retained α
    · refine ⟨⟨p, 0⟩, ?_, ?_⟩
      · rw [hsingle]
        simp
      · exact ⟨i, by simp [PlacedTile.vertex]⟩
    · rw [← G.support_eq α, hsingle, emcg_support_singleton_zero]
      rw [(P.disk p).frontier_eq]
      exact Set.mem_iUnion.2 ⟨i, left_mem_segment ℝ _ _⟩
  choose v hv using hvertices
  have hvinj : Function.Injective v := by
    intro i j hij
    apply (P.disk p).vertex_injective
    rw [← hv i, ← hv j, hij]
  have hcard : (G.P'.disk α).n = (P.disk p).n := by
    apply Nat.le_antisymm
    · simpa using Fintype.card_le_of_injective f hfinj
    · simpa using Fintype.card_le_of_injective v hvinj
  have hfsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).2
      ⟨hfinj, by simp [hcard]⟩).2
  ext e
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨f i, (hf i).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, rfl⟩ := hfsurj j
    exact ⟨i, hf i⟩

private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step2_children
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (hidem : s.setup.c^[2 * l] = s.setup.c^[l])
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α, Set.BijOn (emcdTemplateChild g s l) {t | D.owner t = α}
      (s.setup.retained l (emcdBaseForm g s l α)).children.tiles) ∧
    (∀ t, (D.childTile t).carrier = (emcdTemplateChild g s l t).carrier) ∧
    (∀ t, Set.range (fun i : D.Side t => D.occSide ⟨t, i⟩) =
      Set.range (fun j => (emcdTemplateChild g s l t).side j)) := by
  intro D
  have _ := hidem
  have hsingleton :=
    existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step2_children_aux1
      (P := P)
  have hbase : ∀ p, (s.setup.GS.G.dissect
      (emcdBaseForm g s l (emcdOriginalForm g s l p))).tiles = {⟨p, 0⟩} :=
    existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_original
      g s l
  have hchild : ∀ t : D.Typ,
      (D.childTile t).carrier = (emcdTemplateChild g s l t).carrier := by
    intro t
    exact existsMacroCertificate_seed2_routing_step3_data_sub1_macroData_step4_childCarrier
      g s l t
  have hside : ∀ t : D.Typ,
      Set.range (fun i : D.Side t => D.occSide ⟨t, i⟩) =
        Set.range (fun j => (emcdTemplateChild g s l t).side j) := by
    rintro ⟨α, ⟨⟨form, v⟩, hX⟩⟩
    cases form with
    | inl γ =>
        rfl
    | inr p =>
        let β := emcdBaseForm g s l
          (emcdChildForm g s l ⟨α, ⟨⟨Sum.inr p, v⟩, hX⟩⟩)
        have hsides :=
          hsingleton s.setup.GS.G β p
            (by simpa [β, emcdChildForm, emcdOriginalForm] using hbase p)
        ext e
        constructor
        · rintro ⟨i, rfl⟩
          have hi : (s.setup.GS.G.P'.disk β).side i ∈
              Set.range (s.setup.GS.G.P'.disk β).side := ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := Set.mem_range.1 (hsides ▸ hi)
          refine ⟨j, ?_⟩
          change v +ᵥ (P.disk p).side j =
            v +ᵥ (s.setup.GS.G.P'.disk β).side i
          have heq : (s.setup.GS.G.P'.disk β).side i = (P.disk p).side j :=
            hj.symm
          exact (Set.vadd_set_mono heq.symm.subset).antisymm
            (Set.vadd_set_mono heq.subset)
        · rintro ⟨j, rfl⟩
          have hj : (P.disk p).side j ∈ Set.range (P.disk p).side := ⟨j, rfl⟩
          obtain ⟨i, hi⟩ := Set.mem_range.1 (hsides.symm ▸ hj)
          refine ⟨i, ?_⟩
          change v +ᵥ (s.setup.GS.G.P'.disk β).side i =
            v +ᵥ (P.disk p).side j
          have heq : (s.setup.GS.G.P'.disk β).side i = (P.disk p).side j := hi
          exact (Set.vadd_set_mono heq.subset).antisymm
            (Set.vadd_set_mono heq.symm.subset)
  refine ⟨?_, ?_, ?_⟩
  · intro α
    refine Set.BijOn.mk ?_ ?_ ?_
    · rintro ⟨β, X⟩ hβ
      change β = α at hβ
      subst β
      exact X.2
    · rintro ⟨β, X⟩ hβ ⟨γ, Y⟩ hγ hXY
      change β = α at hβ
      change γ = α at hγ
      subst β
      subst γ
      change X.1 = Y.1 at hXY
      have hXY' : X = Y := Subtype.ext hXY
      subst Y
      rfl
    · intro X hX
      exact ⟨⟨α, ⟨X, hX⟩⟩, by rfl, rfl⟩
  · intro t
    exact hchild t
  · intro t
    exact hside t

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates`: properties of the central child. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step3_central
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (hidem : s.setup.c^[2 * l] = s.setup.c^[l])
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α, emcdTemplateChild g s l (D.central α) = s.setup.central l (emcdBaseForm g s l α)) ∧
    (∀ α, (emcdTemplateChild g s l (D.central α)).form =
      Sum.inl (s.setup.c^[l] (emcdBaseForm g s l α))) ∧
    (∀ α, D.owner (D.central α) = α) ∧
    (∀ t, (emcdTemplateChild g s l t).form = (emcdCatalogueTile g s l (D.form t)).form) := by
  exact ⟨fun _ => rfl, fun α => s.setup.central_form l _, fun _ => rfl, fun _ => rfl⟩

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates`: `emcdParentSide`
is the identity relabelling and has the required parent-side properties. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step4_parentSide
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (hidem : s.setup.c^[2 * l] = s.setup.c^[l])
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α, Function.Injective (emcdParentSide g s l α)) ∧
    (∀ α, Function.Bijective (emcdParentSide g s l α)) ∧
    (∀ α (a b e : Fin (D.Q.disk α).n), CycLt3 a b e →
      CycLt3 (emcdParentSide g s l α a) (emcdParentSide g s l α b) (emcdParentSide g s l α e)) ∧
    (∀ α d, D.macroSide α d =
      (τ.θ ^ (s.setup.GS.k * l)) •
        (s.setup.GS.G.P'.disk (emcdBaseForm g s l α)).side (emcdParentSide g s l α d)) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α
    exact Function.injective_id
  · intro α
    exact Function.bijective_id
  · intro α a b e hab
    exact hab
  · intro α d
    let H := existsMacroCertificate_seed2_routing_step3_data_sub1_macroData τ h g s l hl routing
    have hθ : H.choose.θ = τ.θ ^ (g.k * l) := H.choose_spec.1
    have hk : s.setup.GS.k = g.k := by
      calc
        s.setup.GS.k = g.GS.k := congrArg (fun x => x.k) s.setup_grouped
        _ = g.k := g.grouped_power
    change H.choose.θ •
        (s.setup.GS.G.P'.disk (emcdBaseForm g s l α)).side d =
      (τ.θ ^ (s.setup.GS.k * l)) •
        (s.setup.GS.G.P'.disk (emcdBaseForm g s l α)).side d
    rw [hθ, hk]

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking`: "the
relabelling between the counterclockwise listing of a certificate disk and the listing of its grouped
disk is a bijection of side indices": distinct listed sides of a polygonal disk are distinct
segments. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_side_injective (B : PolygonalDisk) :
    Function.Injective B.side := by
  intro i j hij
  rcases emcg_segment_endpoints hij with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact B.vertex_injective h1
  · exfalso
    have e1 := B.vertex_injective h1
    have e2 := B.vertex_injective h2
    have h3 := B.three_le
    subst e1
    have key : ∀ (n : ℕ), 3 ≤ n → ∀ j : Fin n, finRotate n (finRotate n j) ≠ j := by
      intro n hn j hj
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      rw [finRotate_succ_apply, finRotate_succ_apply, add_assoc, add_eq_left] at hj
      have := congrArg Fin.val hj
      rw [Fin.val_add, Fin.val_zero, Fin.val_one, Nat.mod_eq_of_lt (by omega)] at this
      omega
    exact key _ h3 j e2

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking`:
"Marking follows the marking rule of Step 3 through the parent sides": membership in the marked
sides transports along an equality of grouped forms and of side indices. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_mem_transport {τ : Substitution P}
    {g : existsMacroCertificate_GroupingSeed τ} (s : existsMacroCertificate_SetupSeed τ g)
    {x y : s.setup.GS.G.P'.Form} (hxy : x = y)
    (i : Fin (s.setup.GS.G.P'.disk x).n) (j : Fin (s.setup.GS.G.P'.disk y).n) (hij : (i : ℕ) = j)
    (hi : i ∈ s.setup.markedSides x) : j ∈ s.setup.markedSides y := by
  subst hxy
  have : i = j := Fin.ext hij
  rwa [← this]

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking`:
"every original form is a singleton": the base form of a catalogue form `Sum.inr p` is the base
form of the original catalogue entry of `p`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_base_inr {τ : Substitution P}
    (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (α : emcdForm g s l) (p : P.Form)
    (h : α.1 = Sum.inr p) : emcdBaseForm g s l α = emcdBaseForm g s l (emcdOriginalForm g s l p) := by
  obtain ⟨μ, hμ⟩ := α
  subst h
  rfl

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking`:
"every side of a form that is not a central image is marked": every side of a non-central child
type (an annular piece or an original singleton) is marked, by `s.marked_child` and
`s.marked_singleton`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_noncentral_marked
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ t : D.Typ, t ≠ D.central (D.owner t) → ∀ i, D.marked (D.form t) i := by
  intro D t ht i
  obtain ⟨α, X, hX⟩ := t
  have hXc : X ≠ s.setup.central l (emcdBaseForm g s l α) := by
    rintro rfl
    exact ht rfl
  show emcdParentSide g s l (emcdChildForm g s l ⟨α, X, hX⟩) i ∈
    s.setup.markedSides (emcdBaseForm g s l (emcdChildForm g s l ⟨α, X, hX⟩))
  suffices hu : s.setup.markedSides (emcdBaseForm g s l (emcdChildForm g s l ⟨α, X, hX⟩)) =
      Finset.univ by
    rw [hu]
    exact Finset.mem_univ _
  rcases hf : X.form with γ | p
  · rw [existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_inl g s l _ γ hf]
    exact s.marked_child l _ hl X hX hXc γ hf
  · rw [existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_base_inr g s l _ p hf]
    exact s.marked_singleton _ p
      (existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_original g s l p)

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking`:
"A type is large ... according as its form is a central image": the central type of every
template is large. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_central_large
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α, D.kind (D.form (D.central α)) = .large := by
  intro D α
  have h1 : (emcdChildForm g s l (emcdCentral g s l α)).1 =
      Sum.inl (s.setup.c^[l] (emcdBaseForm g s l α)) := s.setup.central_form l _
  have hn : ¬ ∃ p : P.Form, (emcdChildForm g s l (emcdCentral g s l α)).1 = Sum.inr p := by
    rintro ⟨p, hp⟩
    rw [h1] at hp
    cases hp
  have hy : ∃ β, (emcdChildForm g s l (emcdCentral g s l α)).1 = Sum.inl (s.setup.c^[l] β) :=
    ⟨_, h1⟩
  show emcdKind g s l (emcdChildForm g s l (emcdCentral g s l α)) = .large
  unfold emcdKind
  rw [if_neg hn, if_pos hy]

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking`:
"A type is large ... according as its form is a central image": by
`s.noncentral_not_large`, a type with a large form is the central type of its template. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_large_central
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ t : D.Typ, D.kind (D.form t) = .large → t = D.central (D.owner t) := by
  intro D t hk
  by_contra ht
  obtain ⟨α, X, hX⟩ := t
  have hXc : X ≠ s.setup.central l (emcdBaseForm g s l α) := by
    rintro rfl
    exact ht rfl
  change emcdKind g s l (emcdChildForm g s l ⟨α, X, hX⟩) = .large at hk
  unfold emcdKind at hk
  split_ifs at hk with h1 h2
  obtain ⟨β, hβ⟩ := h2
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  apply s.noncentral_not_large (m + 1) _ hl X hX hXc (s.setup.c^[m] β)
  rw [← Function.iterate_succ_apply' s.setup.c m β]
  exact hβ

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking`:
"The print of a marked parent side is the routing's print slot": the index of the print of `d`
is the routing print index of `d`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_print_val
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α d, (D.print α d : ℕ) =
      ((routing (emcdBaseForm g s l α)).printIdx (emcdParentSide g s l α d) : ℕ) := by
  intro D α d
  let B := emcdGeometryData τ h g s l hl routing
  have hdisk : (emcdQ g s l).disk (emcdChildForm g s l (emcdCentral g s l α)) =
      s.setup.GS.G.mixed.disk (s.setup.central l (emcdBaseForm g s l α)).form := by
    show s.setup.GS.G.P'.disk (emcdBaseForm g s l (emcdChildForm g s l (emcdCentral g s l α))) =
      Sum.elim s.setup.GS.G.P'.disk P.disk (s.setup.central l (emcdBaseForm g s l α)).form
    rw [existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_inl g s l _ _
      (s.setup.central_form l _), s.setup.central_form]
    rfl
  have hwit : ∀ (D1 D2 : PolygonalDisk) (_e : D1 = D2) (j : Fin D2.n), ∃ i : Fin D1.n,
      D1.side i = D2.side j := by
    rintro D1 _ rfl j
    exact ⟨j, rfl⟩
  have key : ∀ (D1 D2 : PolygonalDisk) (_e : D1 = D2) (v : Pt) (i : Fin D1.n) (j : Fin D2.n),
      v +ᵥ D1.side i = v +ᵥ D2.side j → (i : ℕ) = j := by
    rintro D1 _ rfl v i j hij
    have := congrArg ((-v) +ᵥ ·) hij
    simp only [neg_vadd_vadd] at this
    exact congrArg Fin.val (existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_side_injective D1 this)
  have hp : ∃ i : B.Side (B.central α), B.occSide ⟨B.central α, i⟩ =
      (s.setup.central l (emcdBaseForm g s l α)).side
        ((routing (emcdBaseForm g s l α)).printIdx (emcdParentSide g s l α d)) := by
    obtain ⟨i, hi⟩ := hwit _ _ hdisk ((routing (emcdBaseForm g s l α)).printIdx (emcdParentSide g s l α d))
    exact ⟨i, congrArg ((s.setup.central l (emcdBaseForm g s l α)).anchor +ᵥ ·) hi⟩
  have hprint : D.print α d = hp.choose := dif_pos hp
  rw [hprint]
  exact key _ _ hdisk (s.setup.central l (emcdBaseForm g s l α)).anchor _ _ hp.choose_spec

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking`:
"prints are marked" (`RoutingData.print_marked`): the print occurrence of a marked parent side,
in the central child, is marked. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_print_marked
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α d, D.marked α d → D.IsMarked (D.printOcc α d) := by
  intro D α d hd
  have hm := (routing (emcdBaseForm g s l α)).print_marked (emcdParentSide g s l α d) hd
  obtain ⟨a, ha, hav⟩ := Finset.mem_map.1 hm
  have hv := existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_print_val τ h g s l hl routing α d
  exact existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_mem_transport s
    (existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_inl g s l _ _
      (s.setup.central_form l _)).symm a (D.print α d) (by rw [hv]; exact hav) ha

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking`:
"the print in its small owner": the partner occurrence of the print of a marked parent side is
marked (it lies in a non-central child, or is the print itself). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_partner_marked
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α d, D.marked α d → D.IsMarked (D.partner (D.printOcc α d)) := by
  intro D α d hd
  show D.IsMarked (emcdGeometricPartner (emcdGeometryData τ h g s l hl routing) (D.printOcc α d))
  unfold emcdGeometricPartner
  split_ifs with hex
  · have hs := hex.choose_spec
    apply existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_noncentral_marked τ h g s l hl routing
    intro heq
    exact hs.1 (heq.trans (congrArg D.central hs.2.1))
  · exact existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_print_marked τ h g s l hl routing α d hd

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates`: the marking
discipline (`marked_rule_nonlarge`, `marked_rule_large`) follows from `s.marked_child`,
`s.marked_singleton`, `RoutingData.print_marked`, `RoutingData.print_id`, and `hidem`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (hidem : s.setup.c^[2 * l] = s.setup.c^[l])
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d, D.marked α d ↔
      emcdParentSide g s l α d ∈ s.setup.markedSides (emcdBaseForm g s l α)) ∧
    (∀ o : D.SideOcc, D.kind (D.form o.1) ≠ .large ∨ D.IsPrint o → D.IsMarked o) ∧
    ∀ o : D.SideOcc, D.kind (D.owner o.1) = .large →
      D.kind (D.form o.1) = .large → D.IsMarked o → D.IsPrint o := by
  intro D
  have hcl : ∀ β, s.setup.c^[l] (s.setup.c^[l] β) = s.setup.c^[l] β := fun β => by
    rw [← Function.iterate_add_apply, ← two_mul, hidem]
  refine ⟨fun α d => Iff.rfl, ?_, ?_⟩
  · intro o ho
    rcases ho with hk | ⟨d, hd, heq | heq⟩
    · by_cases hc : o.1 = D.central (D.owner o.1)
      · rw [hc] at hk
        exact absurd (existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_central_large τ h g s l hl routing _) hk
      · exact existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_noncentral_marked τ h g s l hl routing o.1 hc
          o.2
    · rw [heq]
      exact existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_print_marked τ h g s l hl routing _ d hd
    · rw [heq]
      exact existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_partner_marked τ h g s l hl routing _ d hd
  · intro o hown hform hmk
    have hc := existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_large_central τ h g s l hl routing o.1 hform
    obtain ⟨⟨α, X, hX⟩, i⟩ := o
    have hXe : X = s.setup.central l (emcdBaseForm g s l α) :=
      congrArg (fun t : emcdTyp g s l => t.2.1) hc
    subst hXe
    change emcdKind g s l α = .large at hown
    unfold emcdKind at hown
    split_ifs at hown with h1 h2
    obtain ⟨β, hβ⟩ := h2
    have hb : emcdBaseForm g s l α = s.setup.c^[l] β :=
      existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_inl g s l α _ hβ
    have hbc : emcdBaseForm g s l (D.form ⟨α, s.setup.central l (emcdBaseForm g s l α), hX⟩) =
        emcdBaseForm g s l α := by
      rw [existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_inl g s l _ _
        (s.setup.central_form l _), hb, hcl]
    have hn : (D.Q.disk (D.form ⟨α, s.setup.central l (emcdBaseForm g s l α), hX⟩)).n =
        (D.Q.disk α).n := by
      show (s.setup.GS.G.P'.disk (emcdBaseForm g s l
        (D.form ⟨α, s.setup.central l (emcdBaseForm g s l α), hX⟩))).n =
        (s.setup.GS.G.P'.disk (emcdBaseForm g s l α)).n
      rw [hbc]
    let d : Fin (D.Q.disk α).n := Fin.cast hn i
    have hd : D.marked α d := existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_mem_transport s hbc i d rfl hmk
    refine ⟨d, hd, Or.inl ?_⟩
    have hdisk : s.setup.GS.G.mixed.disk (s.setup.central l (emcdBaseForm g s l α)).form =
        s.setup.GS.G.P'.disk (emcdBaseForm g s l α) := by
      rw [s.setup.central_form]
      show s.setup.GS.G.P'.disk (s.setup.c^[l] (emcdBaseForm g s l α)) = _
      rw [hb, hcl]
    show (⟨D.central α, i⟩ : D.SideOcc) = ⟨D.central α, D.print α d⟩
    congr 1
    apply Fin.ext
    rw [existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking_step4_print_val τ h g s l hl routing α d,
      (routing _).print_id hdisk (emcdParentSide g s l α d) hd]
    rfl

/-- Step 4 of `lem:certificate-exists`: the positioned-child, template, parent-side, and marking
clauses for `emcdMacroData`: `emcdTemplateChild` bijects `{t | D.owner t = α}` onto the children
of `s.setup.retained l (emcdBaseForm g s l α)` preserving carriers and side sets, `D.σ` satisfies
`existsMacroCertificate_TemplateData D`, `emcdParentSide` is the identity relabelling, and the
marking discipline (`marked_rule_nonlarge`, `marked_rule_large`) follows from `s.marked_child`,
`s.marked_singleton`, `RoutingData.print_marked`, `RoutingData.print_id`, and `hidem`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (hidem : s.setup.c^[2 * l] = s.setup.c^[l])
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    existsMacroCertificate_TemplateData D ∧
    (∀ α, Set.BijOn (emcdTemplateChild g s l) {t | D.owner t = α}
      (s.setup.retained l (emcdBaseForm g s l α)).children.tiles) ∧
    (∀ t, (D.childTile t).carrier = (emcdTemplateChild g s l t).carrier) ∧
    (∀ t, Set.range (fun i : D.Side t => D.occSide ⟨t, i⟩) =
      Set.range (fun j => (emcdTemplateChild g s l t).side j)) ∧
    (∀ α, emcdTemplateChild g s l (D.central α) = s.setup.central l (emcdBaseForm g s l α)) ∧
    (∀ α, (emcdTemplateChild g s l (D.central α)).form =
      Sum.inl (s.setup.c^[l] (emcdBaseForm g s l α))) ∧
    (∀ α, D.owner (D.central α) = α) ∧
    (∀ t, (emcdTemplateChild g s l t).form = (emcdCatalogueTile g s l (D.form t)).form) ∧
    (∀ α, Function.Injective (emcdParentSide g s l α)) ∧
    (∀ α, Function.Bijective (emcdParentSide g s l α)) ∧
    (∀ α (a b e : Fin (D.Q.disk α).n), CycLt3 a b e →
      CycLt3 (emcdParentSide g s l α a) (emcdParentSide g s l α b) (emcdParentSide g s l α e)) ∧
    (∀ α d, D.macroSide α d =
      (τ.θ ^ (s.setup.GS.k * l)) •
        (s.setup.GS.G.P'.disk (emcdBaseForm g s l α)).side (emcdParentSide g s l α d)) ∧
    (∀ α d, D.marked α d ↔
      emcdParentSide g s l α d ∈ s.setup.markedSides (emcdBaseForm g s l α)) ∧
    (∀ o : D.SideOcc, D.kind (D.form o.1) ≠ .large ∨ D.IsPrint o → D.IsMarked o) ∧
    ∀ o : D.SideOcc, D.kind (D.owner o.1) = .large →
      D.kind (D.form o.1) = .large → D.IsMarked o → D.IsPrint o := by
  have h1 := existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step1_templateData τ h g s l hl hidem routing
  have h2 := existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step2_children τ h g s l hl hidem routing
  have h3 := existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step3_central τ h g s l hl hidem routing
  have h4 := existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step4_parentSide τ h g s l hl hidem routing
  have h5 := existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates_step5_marking τ h g s l hl hidem routing
  exact ⟨h1, h2.1, h2.2.1, h2.2.2, h3.1, h3.2.1, h3.2.2.1, h3.2.2.2, h4.1, h4.2.1, h4.2.2.1, h4.2.2.2, h5.1, h5.2.1, h5.2.2⟩

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub4_representation`:
"Put `m = kl`": the grouped power of the routing setup is the power `k` of the grouping seed. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_power
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) : s.setup.GS.k = g.k := by
  rw [s.setup_grouped]; exact g.grouped_power

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub4_representation`:
"every original form is a singleton": the base form of `emcdOriginalForm p` dissects into the
single tile `⟨p, 0⟩`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_original
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (p : P.Form) :
    (s.setup.GS.G.dissect (emcdBaseForm g s l (emcdOriginalForm g s l p))).tiles = {⟨p, 0⟩} := by
  have key : ∀ (GS : GroupedSubstitution τ) (e : GS = g.GS),
      (GS.G.dissect (e.symm ▸ g.original p)).tiles = {⟨p, 0⟩} := by
    rintro GS rfl; exact g.original_dissect p
  exact key _ s.setup_grouped

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub4_representation`:
"every group lies in a supertile", transported from `g.inside_supertile` to the grouped family of
the routing setup. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_inside
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (α : s.setup.GS.G.P'.Form) :
    ∃ (n : ℕ) (p : P.Form) (v : Pt), translateSet v (s.setup.GS.G.dissect α).tiles ⊆ τ.supertile n p := by
  have key : ∀ (GS : GroupedSubstitution τ) (_ : GS = g.GS) (α : GS.G.P'.Form),
      ∃ (n : ℕ) (p : P.Form) (v : Pt), translateSet v (GS.G.dissect α).tiles ⊆ τ.supertile n p := by
    rintro GS rfl α; exact g.inside_supertile α
  exact key _ s.setup_grouped α

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub4_representation`:
"scattering commutes with the retained/scattered rule": scattering a retained catalogue child
through the dissection of its base form is the mixed scattering of the child. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_scatterTile
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (X : PlacedTile s.setup.GS.G.mixed)
    (hX : emcdIsRetainedForm g s l X.form) :
    translateSet X.anchor (s.setup.GS.G.dissect (emcdBaseForm g s l ⟨X.form, hX⟩)).tiles =
      s.setup.GS.G.mixedScatterTile X := by
  rcases X with ⟨f, v⟩
  cases f with
  | inl γ => rfl
  | inr p =>
    have h0 := existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_original
      g s l p
    simp only [emcdOriginalForm] at h0
    change translateSet v (s.setup.GS.G.dissect (emcdBaseForm g s l ⟨Sum.inr p, hX⟩)).tiles = {⟨p, v⟩}
    rw [h0]
    simp [translateSet, PlacedTile.translate]

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub4_representation`:
"the dissections are side-to-side": the side-to-side property descends from a translate. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_sts_of_translate
    {S : Set (PlacedTile P)} (v : Pt) (hS : SideToSideSet (translateSet v S)) : SideToSideSet S := by
  intro A hA B hB i j ⟨x, y, hxy, hseg⟩
  have key := hS (A.translate v) ⟨A, hA, rfl⟩ (B.translate v) ⟨B, hB, rfl⟩ i j ⟨v + x, v + y,
    fun hc => hxy (add_left_cancel hc), by
      intro z hz
      rw [← segment_translate_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rw [emcg_translate_side, emcg_translate_side]
      exact ⟨vadd_mem_vadd_set (hseg hw).1, vadd_mem_vadd_set (hseg hw).2⟩⟩
  rw [emcg_translate_side, emcg_translate_side] at key
  have := congrArg (fun t : Set Pt => (-v) +ᵥ t) key
  simpa [neg_vadd_vadd] using this

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub4_representation`:
"every group lies in a supertile", so by STS every iterated decomposition of a group is
side-to-side. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_iter_sts
    {τ : Substitution P} (h : τ.STS) {S : Set (PlacedTile P)} (m : ℕ)
    (hS : ∃ (n : ℕ) (p : P.Form) (v : Pt), translateSet v S ⊆ τ.supertile n p) :
    SideToSideSet (τ.decomposeIter m S) := by
  obtain ⟨n, p, v, hsub⟩ := hS
  apply existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_sts_of_translate
    ((τ.θ ^ m) • v)
  rw [← emcg_iter_translate]
  refine emcg_sts_subset (h (n + m) p) ?_
  rw [Substitution.supertile, ← emcg_iter_add]
  exact emcg_iter_mono τ m hsub

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub4_representation`:
"heredity transfers": macro data satisfying the representation equations of a grouped
substitution for `τ^m` (whose decompositions are side-to-side) inherits hereditary listed sides
from `τ`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_hereditary
    {τ : Substitution P} (D : MacroData P) (m : ℕ) (hm : 0 < m) (hθ : D.σ.θ = τ.θ ^ m)
    (hcompat : ∀ α, (⋃ A ∈ (D.σ.rule α).tiles, translateSet A.anchor (D.Δ A.form).tiles) =
      τ.decomposeIter m (D.Δ α).tiles)
    (hsupp : ∀ α, support (D.Δ α).tiles = (D.Q.disk α).carrier)
    (hsts : ∀ α, SideToSideSet (D.Δ α).tiles)
    (hdual : ∀ α, DualConnected (D.Δ α).tiles)
    (hside : ∀ α (i : Fin (D.Q.disk α).n), ∃ A ∈ (D.Δ α).tiles, HasEdge A ((D.Q.disk α).side i))
    (hvert : ∀ α v, Substitution.IsVertexOf (D.Δ α).tiles v →
      v ∈ frontier (D.Q.disk α).carrier → v ∈ (D.Q.disk α).vertexSet)
    (hiter : ∀ α, SideToSideSet (τ.decomposeIter m (D.Δ α).tiles))
    (hτ : τ.HereditarySides) : D.Hereditary := by
  let G : GroupedFamily P :=
    { P' := D.Q, dissect := D.Δ, support_eq := hsupp, sts := hsts, dualConnected := hdual
      side_whole := hside, vertex_retained := hvert }
  let GS : GroupedSubstitution τ :=
    { G := G, k := m, k_pos := hm, σ := D.σ, θ_eq := hθ, compat := hcompat }
  exact emcg_grouped_hereditary GS hτ hiter

/-- Step 4 of `lem:certificate-exists`: the representation package
`existsMacroCertificate_RepresentationData τ (g.k * l) D`: scattering the children of `D.σ.rule α`
equals `s.setup.GS.G.mixedScatter (s.setup.retained l (emcdBaseForm g s l α)).children.tiles =
τ.decomposeIter (g.k * l) (D.Δ α).tiles` (`s.setup.scatter_eq`), the dissections `D.Δ α` inherit
`support_eq`, `sts`, `dualConnected`, `side_whole`, and `vertex_retained` from `s.setup.GS.G`,
`emcdOriginalForm` gives the singleton originals, and `g.inside_supertile` and `g.hereditary`
transfer to `D`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub4_representation
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    existsMacroCertificate_RepresentationData τ (g.k * l)
      (emcdMacroData τ h g s l hl routing) := by
  have H := existsMacroCertificate_seed2_routing_step3_data_sub1_macroData τ h g s l hl routing
  have hσ : (emcdMacroData τ h g s l hl routing).σ = H.choose := rfl
  have hΔ : ∀ α, (emcdMacroData τ h g s l hl routing).Δ α = s.setup.GS.G.dissect (emcdBaseForm g s l α) :=
    fun _ => rfl
  have hQ : ∀ α, ((emcdMacroData τ h g s l hl routing).Q.disk α) =
      s.setup.GS.G.P'.disk (emcdBaseForm g s l α) := fun _ => rfl
  have hθ : (emcdMacroData τ h g s l hl routing).σ.θ = τ.θ ^ (g.k * l) := by
    rw [hσ]; exact H.choose_spec.1
  have hcompat : ∀ α, (⋃ A ∈ ((emcdMacroData τ h g s l hl routing).σ.rule α).tiles,
      translateSet A.anchor ((emcdMacroData τ h g s l hl routing).Δ A.form).tiles) =
      τ.decomposeIter (g.k * l) ((emcdMacroData τ h g s l hl routing).Δ α).tiles := by
    intro α
    rw [hΔ α, ← existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_power g s,
      ← s.setup.scatter_eq l (emcdBaseForm g s l α), hσ, H.choose_spec.2 α]
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, GroupedFamily.mixedScatter, exists_prop]
    constructor
    · rintro ⟨A, ⟨t, rfl, rfl⟩, hx⟩
      refine ⟨t.2.1, t.2.2, ?_⟩
      rw [← existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_scatterTile g s l
        t.2.1 (emcdChildForm g s l t).2]
      exact hx
    · rintro ⟨X, hX, hx⟩
      refine ⟨_, ⟨⟨α, ⟨X, hX⟩⟩, rfl, rfl⟩, ?_⟩
      rw [← existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_scatterTile g s l
        X (emcdChildForm g s l ⟨α, ⟨X, hX⟩⟩).2] at hx
      exact hx
  have hsupp : ∀ α, support ((emcdMacroData τ h g s l hl routing).Δ α).tiles =
      ((emcdMacroData τ h g s l hl routing).Q.disk α).carrier := by
    intro α; rw [hΔ, hQ]; exact s.setup.GS.G.support_eq _
  have hsts : ∀ α, SideToSideSet ((emcdMacroData τ h g s l hl routing).Δ α).tiles := by
    intro α; rw [hΔ]; exact s.setup.GS.G.sts _
  have hdual : ∀ α, DualConnected ((emcdMacroData τ h g s l hl routing).Δ α).tiles := by
    intro α; rw [hΔ]; exact s.setup.GS.G.dualConnected _
  have hside : ∀ α (i : Fin ((emcdMacroData τ h g s l hl routing).Q.disk α).n),
      ∃ A ∈ ((emcdMacroData τ h g s l hl routing).Δ α).tiles,
        HasEdge A (((emcdMacroData τ h g s l hl routing).Q.disk α).side i) := by
    intro α i; rw [hΔ]; exact s.setup.GS.G.side_whole _ i
  have hvert : ∀ α v, Substitution.IsVertexOf ((emcdMacroData τ h g s l hl routing).Δ α).tiles v →
      v ∈ frontier ((emcdMacroData τ h g s l hl routing).Q.disk α).carrier →
        v ∈ ((emcdMacroData τ h g s l hl routing).Q.disk α).vertexSet := by
    intro α v hv hfr; rw [hΔ] at hv; rw [hQ] at hfr ⊢; exact s.setup.GS.G.vertex_retained _ v hv hfr
  have hinside : ∀ α, ∃ (n : ℕ) (p : P.Form) (v : Pt),
      translateSet v ((emcdMacroData τ h g s l hl routing).Δ α).tiles ⊆ τ.supertile n p := by
    intro α; rw [hΔ]
    exact existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_inside g s _
  have hm : 0 < g.k * l := Nat.mul_pos g.k_pos hl
  refine ⟨hm, hθ, hcompat, hsupp, hsts, hdual, hside, hvert, ?_, hinside, ?_⟩
  · intro p; exact ⟨emcdOriginalForm g s l p,
      existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_original g s l p⟩
  · exact existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_hereditary _ _ hm hθ
      hcompat hsupp hsts hdual hside hvert (fun α =>
        existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_iter_sts h _ (hinside α))

/-- Step 5 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces`:
"an inner side has exactly two owners, because the
template is side-to-side" (existence): in a finite side-to-side cellulation, a side of a cell
which is not contained in the frontier of the support is a whole side of a second cell. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step5_partner_exists
    {Q : Protoset} {S : Set (PlacedTile Q)} (hfin : S.Finite)
    (hdisj : DisjointInteriors S) (hsts : SideToSideSet S) {A : PlacedTile Q} (hA : A ∈ S)
    (i : Fin (Q.disk A.form).n) (hnot : ¬ A.side i ⊆ frontier (support S)) :
    ∃ B ∈ S, B ≠ A ∧ ∃ j, B.side j = A.side i := by
  classical
  obtain ⟨p, hpA, hpf⟩ := Set.not_subset.1 hnot
  have hpS : p ∈ support S := carrier_subset_support hA (tile_side_subset A i hpA)
  have hpint : p ∈ interior (support S) := by
    by_contra h
    exact hpf ((mem_frontier_iff_of_closed (support_isClosed hfin)).2 ⟨hpS, h⟩)
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.1 isOpen_interior p hpint
  have hab : A.vertex i ≠ A.vertex (finRotate _ i) := tile_vertex_ne_next A i
  rw [tile_side_eq, segment_eq_image_lineMap] at hpA
  obtain ⟨t0, ht0, rfl⟩ := hpA
  have hcont : Continuous (AffineMap.lineMap (A.vertex i) (A.vertex (finRotate _ i)) : ℝ → Pt) :=
    AffineMap.lineMap_continuous
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.1 hcont t0 ε hε
  have hlt : max 0 (t0 - δ) < min 1 (t0 + δ) := by
    rcases ht0 with ⟨h0, h1⟩
    exact max_lt (lt_min (by norm_num) (by linarith)) (lt_min (by linarith) (by linarith))
  have hIinf : (Ioo (max 0 (t0 - δ)) (min 1 (t0 + δ))).Infinite := Set.Ioo_infinite hlt
  have hV : (⋃ B ∈ S, B.vertexSet).Finite := hfin.biUnion fun B _ => Set.finite_range _
  have hinj : Function.Injective
      (AffineMap.lineMap (A.vertex i) (A.vertex (finRotate _ i)) : ℝ → Pt) :=
    AffineMap.lineMap_injective ℝ hab
  obtain ⟨q, ⟨t, htI, rfl⟩, hqV⟩ := ((hIinf.image hinj.injOn).diff hV).nonempty
  have htI' := htI
  rcases htI' with ⟨h1, h2⟩
  have hqo : AffineMap.lineMap (A.vertex i) (A.vertex (finRotate _ i)) t ∈
      openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)) := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨t, ⟨lt_of_le_of_lt (le_max_left _ _) h1, lt_of_lt_of_le h2 (min_le_left _ _)⟩, rfl⟩
  set q := AffineMap.lineMap (A.vertex i) (A.vertex (finRotate _ i)) t with hqdef
  have hqp : dist q (AffineMap.lineMap (A.vertex i) (A.vertex (finRotate _ i)) t0) < ε := by
    apply hδε
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [le_max_right 0 (t0 - δ)]
    · linarith [min_le_right 1 (t0 + δ)]
  set ε' := ε - dist q (AffineMap.lineMap (A.vertex i) (A.vertex (finRotate _ i)) t0)
  have hε' : 0 < ε' := by simp only [ε']; linarith
  have hball : Metric.ball q ε' ⊆ interior (support S) := by
    intro x hx
    apply hεS
    rw [Metric.mem_ball] at hx ⊢
    have := dist_triangle x q (AffineMap.lineMap (A.vertex i) (A.vertex (finRotate _ i)) t0)
    simp only [ε'] at hx
    linarith
  have hqB : ∃ B ∈ S, B ≠ A ∧ q ∈ B.carrier := by
    by_contra hno
    push_neg at hno
    have hKc : IsClosed (⋃ B ∈ S \ {A}, B.carrier) :=
      (hfin.diff).isClosed_biUnion fun B _ => tile_isClosed B
    have hqK : q ∉ ⋃ B ∈ S \ {A}, B.carrier := by
      simp only [mem_iUnion]
      rintro ⟨B, ⟨hB, hBA⟩, hqB⟩
      exact hno B hB hBA hqB
    obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl q hqK
    have hqfr : q ∈ frontier A.carrier := by
      rw [tile_frontier_eq]
      exact mem_iUnion.2 ⟨i, by rw [tile_side_eq]; exact openSegment_subset_segment ℝ _ _ hqo⟩
    rw [frontier_eq_closure_inter_closure] at hqfr
    obtain ⟨x, hxA, hxq⟩ := Metric.mem_closure_iff.1 hqfr.2 (min ρ ε') (lt_min hρ hε')
    have hxb : x ∈ Metric.ball q ε' := by
      rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hxq (min_le_right _ _)
    have hxρ : x ∈ Metric.ball q ρ := by
      rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hxq (min_le_left _ _)
    obtain ⟨B, hB, hxB⟩ := mem_support_iff'.1 (interior_subset (hball hxb))
    apply hρK hxρ
    simp only [mem_iUnion]
    refine ⟨B, ⟨hB, ?_⟩, hxB⟩
    rintro rfl
    exact hxA hxB
  obtain ⟨B, hB, hBA, hqB⟩ := hqB
  obtain ⟨j, hj⟩ := tile_partner hdisj hsts hA hB (Ne.symm hBA) i hqo hqB
    (fun hv => hqV (mem_biUnion hB hv))
  exact ⟨B, hB, hBA, j, hj⟩

/-- Step 5 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces`:
"three polygons with disjoint interiors cannot share a
whole segment": two cells sharing a whole side with a given cell coincide. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step5_two_owners
    {Q : Protoset} {S : Set (PlacedTile Q)} (hdisj : DisjointInteriors S)
    {A B C : PlacedTile Q} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S) (hBA : B ≠ A) (hCA : C ≠ A)
    (i : Fin (Q.disk A.form).n) (j : Fin (Q.disk B.form).n) (k : Fin (Q.disk C.form).n)
    (hj : B.side j = A.side i) (hk : C.side k = A.side i) : B = C := by
  by_contra hBC
  set a := A.vertex i with ha
  set b := A.vertex (finRotate _ i) with hb
  have hab : a ≠ b := tile_vertex_ne_next A i
  set q := midpoint ℝ a b with hq
  have hqo : q ∈ openSegment ℝ a b := by
    apply mem_openSegment_of_ne_left_right
    · intro h
      exact hab (by rw [eq_comm, midpoint_eq_left_iff] at h; exact h)
    · intro h
      exact hab (by rw [eq_comm, midpoint_eq_right_iff] at h; exact h)
    · exact midpoint_mem_segment _ _
  obtain ⟨r, hr, σ, hσ, h1⟩ := two_sides hdisj hA hB hBA.symm i j hj hqo
  obtain ⟨r', hr', σ', hσ', h2⟩ := two_sides hdisj hA hC hCA.symm i k hk hqo
  set d := b - a with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 hab.symm
  set N := d 0 * d 0 + d 1 * d 1 with hN
  have hNpos : 0 < N := by
    rcases (show d 0 ≠ 0 ∨ d 1 ≠ 0 by
      by_contra hc
      push_neg at hc
      apply hd0
      ext m
      fin_cases m <;> simp [hc.1, hc.2]) with h | h
    · have := mul_self_pos.2 h; nlinarith [mul_self_nonneg (d 1)]
    · have := mul_self_pos.2 h; nlinarith [mul_self_nonneg (d 0)]
  set n : Pt := mkPt (-d 1) (d 0) with hn
  set m := min r r' with hm
  have hmpos : 0 < m := lt_min hr hr'
  set s := m / (2 * (‖n‖ + 1)) with hs
  have hspos : 0 < s := by positivity
  have hsn : ‖s • n‖ < m := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos, hs]
    have hn0 : 0 ≤ ‖n‖ := norm_nonneg _
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hjq : jcr d (q - a) = 0 := by
    have : q - a = (1 / 2 : ℝ) • d := by
      rw [hq, hd, midpoint_eq_smul_add, invOf_eq_inv]; module
    rw [this, jcr, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]; ring
  have hJ : ∀ c : ℝ, jcr d (q + c • n - a) = c * N := by
    intro c
    have : q + c • n - a = (q - a) + c • n := by abel
    rw [this]
    have e : jcr d ((q - a) + c • n) = jcr d (q - a) + c * jcr d n := by
      simp only [jcr, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e, hjq, zero_add]
    simp only [jcr, hn, rg_mkPt0, rg_mkPt1, hN]; ring
  have hmem : ∀ c : ℝ, |c| ≤ s → q + c • n ∈ Metric.ball q r ∧ q + c • n ∈ Metric.ball q r' := by
    intro c hc
    have hlt : dist (q + c • n) q < m := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |c| * ‖n‖ ≤ s * ‖n‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        _ = ‖s • n‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
        _ < m := hsn
    exact ⟨Metric.mem_ball.2 (lt_of_lt_of_le hlt (min_le_left _ _)),
      Metric.mem_ball.2 (lt_of_lt_of_le hlt (min_le_right _ _))⟩
  have hp := hmem s (by rw [abs_of_pos hspos])
  have hm' := hmem (-s) (by rw [abs_neg, abs_of_pos hspos])
  have hJp := hJ s
  have hJm := hJ (-s)
  have hsN : 0 < s * N := mul_pos hspos hNpos
  rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl
  · have hyB := (h1 _ hm'.1).2.1 (by rw [hJm]; linarith)
    have hyC := (h2 _ hm'.2).2.1 (by rw [hJm]; linarith)
    exact interior_not_mem_other hdisj hB hC hBC hyB (interior_subset hyC)
  · have hyA := (h1 _ hp.1).1 (by rw [hJp]; linarith)
    have hyC := (h2 _ hp.2).2.1 (by rw [hJp]; linarith)
    exact interior_not_mem_other hdisj hA hC hCA.symm hyA (interior_subset hyC)
  · have hyA := (h1 _ hm'.1).1 (by rw [hJm]; linarith)
    have hyC := (h2 _ hm'.2).2.1 (by rw [hJm]; linarith)
    exact interior_not_mem_other hdisj hA hC hCA.symm hyA (interior_subset hyC)
  · have hyB := (h1 _ hp.1).2.1 (by rw [hJp]; linarith)
    have hyC := (h2 _ hp.2).2.1 (by rw [hJp]; linarith)
    exact interior_not_mem_other hdisj hB hC hBC hyB (interior_subset hyC)

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces`:
"the types are the positioned children of the retained
templates": every listed side of a type is a listed side of its template child. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_child_side
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ t i, ∃ j, D.occSide ⟨t, i⟩ = (emcdTemplateChild g s l t).side j := by
  classical
  dsimp only
  rintro ⟨α, ⟨⟨β | p, v⟩, hX⟩⟩ i
  · exact ⟨i, rfl⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hbase_original, _⟩ :=
      existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue τ h g s l hl routing
    have hdis :
        (s.setup.GS.G.dissect (emcdBaseForm g s l (emcdChildForm g s l
          ⟨α, ⟨⟨Sum.inr p, v⟩, hX⟩⟩))).tiles = {⟨p, 0⟩} := by
      simpa [emcdChildForm, emcdOriginalForm] using hbase_original p
    obtain ⟨A, hA, j, hj⟩ :=
      s.setup.GS.G.side_whole (emcdBaseForm g s l (emcdChildForm g s l
        ⟨α, ⟨⟨Sum.inr p, v⟩, hX⟩⟩)) i
    rw [hdis, Set.mem_singleton_iff] at hA
    subst A
    refine ⟨j, ?_⟩
    have hsides :
        (s.setup.GS.G.P'.disk (emcdBaseForm g s l (emcdChildForm g s l
          ⟨α, ⟨⟨Sum.inr p, v⟩, hX⟩⟩))).side i = (P.disk p).side j := by
      simpa [PlacedTile.side] using hj.symm
    change v +ᵥ
        (s.setup.GS.G.P'.disk (emcdBaseForm g s l (emcdChildForm g s l
          ⟨α, ⟨⟨Sum.inr p, v⟩, hX⟩⟩))).side i = v +ᵥ (P.disk p).side j
    rw [hsides]

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces`:
"the relabelling between the listing of a
certificate disk and the listing of its grouped disk is a bijection of side indices": the listed
sides of a polygonal disk are pairwise distinct. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_side_injective
    (B : PolygonalDisk) : Function.Injective B.side := by
  intro i j hij
  apply cyc_seg_inj B.three_le B.vertex_injective
  simpa only [PolygonalDisk.side] using hij

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces`:
"the relabelling between the counterclockwise listing
of a certificate disk and the listing of its grouped disk is a bijection of side indices":
every listed side of a template child is a listed side of its type. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_side_child
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ t j, ∃ i, D.occSide ⟨t, i⟩ = (emcdTemplateChild g s l t).side j := by
  classical
  dsimp only
  rintro ⟨α, ⟨⟨β | p, v⟩, hX⟩⟩ k
  · exact ⟨k, rfl⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hbase_original, _⟩ :=
      existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue τ h g s l hl routing
    set x := emcdBaseForm g s l (emcdChildForm g s l ⟨α, ⟨⟨Sum.inr p, v⟩, hX⟩⟩) with hxdef
    have hdis : (s.setup.GS.G.dissect x).tiles = {⟨p, 0⟩} := by
      simpa [x, emcdChildForm, emcdOriginalForm] using hbase_original p
    have hf : ∀ i, ∃ j, (s.setup.GS.G.P'.disk x).side i = (P.disk p).side j := by
      intro i
      obtain ⟨A, hA, j, hj⟩ := s.setup.GS.G.side_whole x i
      rw [hdis, Set.mem_singleton_iff] at hA
      subst A
      exact ⟨j, by simpa [PlacedTile.side] using hj.symm⟩
    choose f hf using hf
    have hfinj : Function.Injective f := by
      intro i i' hii'
      apply existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_side_injective
      rw [hf i, hf i', hii']
    have hvs := existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_singleton_vertexSet
      s.setup.GS.G x p hdis
    have hn : (s.setup.GS.G.P'.disk x).n = (P.disk p).n := by
      have h1 := Set.ncard_range_of_injective (s.setup.GS.G.P'.disk x).vertex_injective
      have h2 := Set.ncard_range_of_injective (P.disk p).vertex_injective
      simp only [PolygonalDisk.vertexSet] at hvs
      rw [hvs, h2] at h1
      simpa using h1.symm
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, by simp [hn]⟩
    obtain ⟨i, hi⟩ := hbij.2 k
    refine ⟨i, ?_⟩
    change v +ᵥ (s.setup.GS.G.P'.disk x).side i = v +ᵥ (P.disk p).side k
    rw [hf i, hi]

/-- Step 5 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces`:
the scaled parent region of a certificate form is
the region of its retained template. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step5_region
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α, D.macroRegion α = (s.setup.retained l (emcdBaseForm g s l α)).region := by
  dsimp only
  intro α
  have htheta :=
    (existsMacroCertificate_seed2_routing_step3_data_sub4_representation
      τ h g s l hl routing).θ_eq
  have hk : s.setup.GS.k = g.k := by
    calc
      s.setup.GS.k = g.GS.k := congrArg GroupedSubstitution.k s.setup_grouped
      _ = g.k := g.grouped_power
  rw [s.setup.region_eq]
  unfold MacroData.macroRegion
  rw [htheta, ← hk]
  rfl

/-- Step 5 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces`:
"an inner side has exactly two owners, because the
template is side-to-side" (existence of the second owner): every inner side occurrence has a
second occurrence of the same segment, in a different child of the same template. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step5_twin_exists
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ o : D.SideOcc, D.IsInner o →
      ∃ o' : D.SideOcc, o'.1 ≠ o.1 ∧ D.owner o'.1 = D.owner o.1 ∧ D.occSide o' = D.occSide o := by
  classical
  intro D
  rintro ⟨⟨α, X⟩, i⟩ hin
  obtain ⟨j, hj⟩ := existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_child_side τ h g s l hl routing ⟨α, X⟩ i
  let T := s.setup.retained l (emcdBaseForm g s l α)
  have hnot : ¬ X.1.side j ⊆ frontier (support T.children.tiles) := by
    intro hsub
    apply hin
    change D.occSide ⟨⟨α, X⟩, i⟩ ⊆ frontier (D.macroRegion α)
    rw [existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step5_region τ h g s l hl routing α, ← T.support_eq]
    exact hj ▸ hsub
  obtain ⟨Y, hY, hYX, k, hk⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step5_partner_exists
      T.children.finite T.children.disjoint
    T.sts X.2 j hnot
  obtain ⟨i', hi'⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_side_child
      τ h g s l hl routing ⟨α, ⟨Y, hY⟩⟩ k
  refine ⟨⟨⟨α, ⟨Y, hY⟩⟩, i'⟩, ?_, rfl, ?_⟩
  · intro he
    exact hYX (congrArg (emcdTemplateChild g s l) he)
  · exact hi'.trans (hk.trans hj.symm)

/-- Step 5 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces`:
"three polygons with disjoint interiors cannot share a
whole segment" (uniqueness of the second owner): two occurrences of the segment of a side
occurrence, in children different from its own child of the same template, coincide. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step5_twin_unique
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ o o₁ o₂ : D.SideOcc,
      (o₁.1 ≠ o.1 ∧ D.owner o₁.1 = D.owner o.1 ∧ D.occSide o₁ = D.occSide o) →
      (o₂.1 ≠ o.1 ∧ D.owner o₂.1 = D.owner o.1 ∧ D.occSide o₂ = D.occSide o) → o₁ = o₂ := by
  classical
  intro D
  rintro ⟨⟨α, X⟩, i⟩ ⟨⟨α₁, X₁⟩, i₁⟩ ⟨⟨α₂, X₂⟩, i₂⟩ ⟨hne₁, how₁, hs₁⟩ ⟨hne₂, how₂, hs₂⟩
  change α₁ = α at how₁
  change α₂ = α at how₂
  subst α₁
  subst α₂
  obtain ⟨j, hj⟩ := existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_child_side τ h g s l hl routing ⟨α, X⟩ i
  obtain ⟨j₁, hj₁⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_child_side
      τ h g s l hl routing ⟨α, X₁⟩ i₁
  obtain ⟨j₂, hj₂⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_child_side
      τ h g s l hl routing ⟨α, X₂⟩ i₂
  have hX₁ : X₁.1 ≠ X.1 := fun he => hne₁ (by
    have e : X₁ = X := Subtype.ext he
    subst e
    rfl)
  have hX₂ : X₂.1 ≠ X.1 := fun he => hne₂ (by
    have e : X₂ = X := Subtype.ext he
    subst e
    rfl)
  by_cases h12 : X₁.1 = X₂.1
  · have h12' : X₁ = X₂ := Subtype.ext h12
    subst h12'
    have hii : i₁ = i₂ := by
      apply existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_side_injective
      have hs : D.occSide ⟨⟨α, X₁⟩, i₁⟩ = D.occSide ⟨⟨α, X₁⟩, i₂⟩ := hs₁.trans hs₂.symm
      exact AddAction.injective (D.anchor ⟨α, X₁⟩) hs
    subst hii
    rfl
  · exfalso
    let T := s.setup.retained l (emcdBaseForm g s l α)
    exact h12 (existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step5_two_owners
        T.children.disjoint X.2 X₁.2 X₂.2 hX₁ hX₂ j j₁ j₂
      (hj₁.symm.trans (hs₁.trans hj)) (hj₂.symm.trans (hs₂.trans hj)))

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces`:
"the partner of an inner side occurrence is the other
occurrence of the same geometric side in the same template; the interface identifier of an inner
side is its unordered pair of occurrences, with the two type tags recorded in a fixed order":
given existence and uniqueness of the second occurrence (Step 5), the geometric partner,
interface and type-tag maps satisfy the interface specifications. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_partner_edge
    (B : MacroData P)
    (hE : ∀ o : B.SideOcc, B.IsInner o →
      ∃ o' : B.SideOcc, o'.1 ≠ o.1 ∧ B.owner o'.1 = B.owner o.1 ∧ B.occSide o' = B.occSide o)
    (hU : ∀ o o₁ o₂ : B.SideOcc,
      (o₁.1 ≠ o.1 ∧ B.owner o₁.1 = B.owner o.1 ∧ B.occSide o₁ = B.occSide o) →
      (o₂.1 ≠ o.1 ∧ B.owner o₂.1 = B.owner o.1 ∧ B.occSide o₂ = B.occSide o) → o₁ = o₂)
    (T : B.SideOcc → B.Typ × B.Typ) (hT : ∀ e, T e = (e.1, (emcdGeometricPartner B e).1)) :
    (∀ o : B.SideOcc, B.IsInner o →
      (emcdGeometricPartner B o).1 ≠ o.1 ∧ B.owner (emcdGeometricPartner B o).1 = B.owner o.1 ∧
        B.occSide (emcdGeometricPartner B o) = B.occSide o) ∧
    (∀ o o' : B.SideOcc, B.IsInner o → B.IsInner o' →
      (emcdGeometricEdge B o = emcdGeometricEdge B o' ↔ o' = o ∨ o' = emcdGeometricPartner B o)) ∧
    (∀ o : B.SideOcc, B.IsInner o →
      T (emcdGeometricEdge B o) = (o.1, (emcdGeometricPartner B o).1) ∨
        T (emcdGeometricEdge B o) = ((emcdGeometricPartner B o).1, o.1)) := by
  classical
  have hP : ∀ o, B.IsInner o → (emcdGeometricPartner B o).1 ≠ o.1 ∧
      B.owner (emcdGeometricPartner B o).1 = B.owner o.1 ∧
        B.occSide (emcdGeometricPartner B o) = B.occSide o := by
    intro o ho
    have hex := hE o ho
    unfold emcdGeometricPartner
    rw [dif_pos hex]
    exact hex.choose_spec
  have hIn : ∀ o o' : B.SideOcc, B.owner o'.1 = B.owner o.1 → B.occSide o' = B.occSide o →
      B.IsInner o → B.IsInner o' := by
    intro o o' h1 h2 ho
    unfold MacroData.IsInner MacroData.IsOuter at ho ⊢
    rw [h1, h2]
    exact ho
  have hPin : ∀ o, B.IsInner o → B.IsInner (emcdGeometricPartner B o) := fun o ho =>
    hIn o _ (hP o ho).2.1 (hP o ho).2.2 ho
  have hPP : ∀ o, B.IsInner o → emcdGeometricPartner B (emcdGeometricPartner B o) = o := by
    intro o ho
    obtain ⟨h1, h2, h3⟩ := hP o ho
    exact hU _ _ _ (hP _ (hPin o ho)) ⟨h1.symm, h2.symm, h3.symm⟩
  have hEd : ∀ o, emcdGeometricEdge B o = o ∨ emcdGeometricEdge B o = emcdGeometricPartner B o := by
    intro o
    unfold emcdGeometricEdge
    dsimp only
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hEs : ∀ o, B.IsInner o →
      emcdGeometricEdge B (emcdGeometricPartner B o) = emcdGeometricEdge B o := by
    intro o ho
    unfold emcdGeometricEdge
    dsimp only
    rw [hPP o ho]
    split_ifs with h1 h2 h2
    · exact (Fintype.equivFin B.SideOcc).injective (le_antisymm h1 h2)
    · rfl
    · rfl
    · exact absurd (le_of_not_ge h1) h2
  refine ⟨hP, ?_, ?_⟩
  · intro o o' ho ho'
    constructor
    · intro he
      rcases hEd o with e1 | e1 <;> rcases hEd o' with e2 | e2 <;> rw [e1, e2] at he
      · exact Or.inl he.symm
      · right
        rw [← hPP o' ho', ← he]
      · exact Or.inr he.symm
      · left
        obtain ⟨h1, h2, h3⟩ := hP o ho
        obtain ⟨h1', h2', h3'⟩ := hP o' ho'
        refine hU (emcdGeometricPartner B o) o' o ⟨?_, ?_, ?_⟩ ⟨h1.symm, h2.symm, h3.symm⟩
        · rw [he]; exact h1'.symm
        · rw [he]; exact h2'.symm
        · rw [he]; exact h3'.symm
    · rintro (rfl | rfl)
      · rfl
      · exact (hEs o ho).symm
  · intro o ho
    rw [hT]
    rcases hEd o with e | e
    · left
      rw [e]
    · right
      rw [e, hPP o ho]

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces`:
"the partner of an inner side occurrence is the other occurrence of the same geometric side in
the same template": construction equation of the partner map. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_partner_eq
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    ∀ o : (emcdMacroData τ h g s l hl routing).SideOcc,
      (emcdMacroData τ h g s l hl routing).partner o =
        emcdGeometricPartner (emcdGeometryData τ h g s l hl routing) o :=
  fun _ => rfl

/-- Step 4 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces`:
"the interface identifier of an inner side is its unordered pair of occurrences": construction
equation of the interface map. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_edge_eq
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    ∀ o : (emcdMacroData τ h g s l hl routing).SideOcc,
      (emcdMacroData τ h g s l hl routing).edge o =
        emcdGeometricEdge (emcdGeometryData τ h g s l hl routing) o :=
  fun _ => rfl

/-- Step 1 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer`: the internal
interface specifications (`partner_spec`, `edge_spec`, `edgeTypes_spec` from the two-owner
property of inner sides in the STS template). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ o : D.SideOcc, D.IsInner o →
      (D.partner o).1 ≠ o.1 ∧ D.owner (D.partner o).1 = D.owner o.1 ∧
        D.occSide (D.partner o) = D.occSide o) ∧
    (∀ o o' : D.SideOcc, D.IsInner o → D.IsInner o' →
      (D.edge o = D.edge o' ↔ o' = o ∨ o' = D.partner o)) ∧
    (∀ o : D.SideOcc, D.IsInner o →
      D.edgeTypes (D.edge o) = (o.1, (D.partner o).1) ∨
        D.edgeTypes (D.edge o) = ((D.partner o).1, o.1)) := by
  intro D
  have key := existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_partner_edge
    (emcdGeometryData τ h g s l hl routing)
    (existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step5_twin_exists τ h g s l hl routing)
    (existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step5_twin_unique τ h g s l hl routing)
    D.edgeTypes (fun _ => rfl)
  have hP := existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_partner_eq τ h g s l hl routing
  have hE := existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces_step4_edge_eq τ h g s l hl routing
  refine ⟨fun o ho => ?_, fun o o' ho ho' => ?_, fun o ho => ?_⟩
  · rw [hP]
    exact key.1 o ho
  · rw [hE, hE, hP]
    exact key.2.1 o o' ho ho'
  · rw [hE, hP]
    exact key.2.2 o ho

private lemma
    emcd_outer_step2_child_side
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ t i, ∃ j, D.occSide ⟨t, i⟩ = (emcdTemplateChild g s l t).side j := by
  classical
  dsimp only
  rintro ⟨α, ⟨⟨β | p, v⟩, hX⟩⟩ i
  · exact ⟨i, rfl⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hbase_original, _⟩ :=
      existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue τ h g s l hl routing
    have hdis :
        (s.setup.GS.G.dissect (emcdBaseForm g s l (emcdChildForm g s l
          ⟨α, ⟨⟨Sum.inr p, v⟩, hX⟩⟩))).tiles = {⟨p, 0⟩} := by
      simpa [emcdChildForm, emcdOriginalForm] using hbase_original p
    obtain ⟨A, hA, j, hj⟩ :=
      s.setup.GS.G.side_whole (emcdBaseForm g s l (emcdChildForm g s l
        ⟨α, ⟨⟨Sum.inr p, v⟩, hX⟩⟩)) i
    rw [hdis, Set.mem_singleton_iff] at hA
    subst A
    refine ⟨j, ?_⟩
    have hsides :
        (s.setup.GS.G.P'.disk (emcdBaseForm g s l (emcdChildForm g s l
          ⟨α, ⟨⟨Sum.inr p, v⟩, hX⟩⟩))).side i = (P.disk p).side j := by
      simpa [PlacedTile.side] using hj.symm
    change v +ᵥ
        (s.setup.GS.G.P'.disk (emcdBaseForm g s l (emcdChildForm g s l
          ⟨α, ⟨⟨Sum.inr p, v⟩, hX⟩⟩))).side i = v +ᵥ (P.disk p).side j
    exact Set.vadd_set_mono hsides.subset |>.antisymm
      (Set.vadd_set_mono hsides.symm.subset)

private lemma
    emcd_outer_step2_region
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α, D.macroRegion α =
      (s.setup.retained l (emcdBaseForm g s l α)).region := by
  dsimp only
  intro α
  have htheta :=
    (existsMacroCertificate_seed2_routing_step3_data_sub4_representation
      τ h g s l hl routing).θ_eq
  have hk : s.setup.GS.k = g.k := by
    calc
      s.setup.GS.k = g.GS.k := congrArg GroupedSubstitution.k s.setup_grouped
      _ = g.k := g.grouped_power
  rw [s.setup.region_eq]
  unfold MacroData.macroRegion
  rw [htheta, ← hk]
  rfl

private lemma
    emcd_outer_step2_side_injective
    (B : PolygonalDisk) : Function.Injective B.side := by
  intro i j hij
  apply cyc_seg_inj B.three_le B.vertex_injective
  simpa only [PolygonalDisk.side] using hij

private lemma
    emcd_outer_step2_occ_injective
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ {o o' : D.SideOcc}, D.owner o.1 = D.owner o'.1 → D.IsOuter o →
      D.IsOuter o' → D.occSide o = D.occSide o' → o = o' := by
  classical
  dsimp only
  let D := emcdMacroData τ h g s l hl routing
  change ∀ {o o' : D.SideOcc}, D.owner o.1 = D.owner o'.1 → D.IsOuter o →
    D.IsOuter o' → D.occSide o = D.occSide o' → o = o'
  rintro ⟨⟨α, X⟩, i⟩ ⟨⟨β, Y⟩, i'⟩ howner hout hout' heq
  change α = β at howner
  subst β
  obtain ⟨j, hj⟩ :=
    emcd_outer_step2_child_side
      τ h g s l hl routing ⟨α, X⟩ i
  obtain ⟨k, hk⟩ :=
    emcd_outer_step2_child_side
      τ h g s l hl routing ⟨α, Y⟩ i'
  have hside : X.1.side j = Y.1.side k := hj.symm.trans (heq.trans hk)
  by_cases hXY : X.1 = Y.1
  · have hXY' : X = Y := Subtype.ext hXY
    subst Y
    have hii : i = i' := by
      apply
      emcd_outer_step2_side_injective
      apply Set.Subset.antisymm
      · apply (Set.vadd_set_subset_vadd_set_iff
          (a := D.anchor ⟨α, X⟩)).1
        change D.occSide ⟨⟨α, X⟩, i⟩ ⊆ D.occSide ⟨⟨α, X⟩, i'⟩
        exact heq.subset
      · apply (Set.vadd_set_subset_vadd_set_iff
          (a := D.anchor ⟨α, X⟩)).1
        change D.occSide ⟨⟨α, X⟩, i'⟩ ⊆ D.occSide ⟨⟨α, X⟩, i⟩
        exact heq.symm.subset
    subst i'
    rfl
  · let T := s.setup.retained l (emcdBaseForm g s l α)
    have hXmem : X.1 ∈ T.children.tiles := X.2
    have hYmem : Y.1 ∈ T.children.tiles := Y.2
    let q := midpoint ℝ (X.1.vertex j) (X.1.vertex (finRotate _ j))
    have hqopen : q ∈ openSegment ℝ (X.1.vertex j)
        (X.1.vertex (finRotate _ j)) := by
      apply mem_openSegment_of_ne_left_right
      · intro hq
        exact tile_vertex_ne_next X.1 j (by
          dsimp [q] at hq
          rw [eq_comm, midpoint_eq_left_iff] at hq
          exact hq)
      · intro hq
        exact tile_vertex_ne_next X.1 j (by
          dsimp [q] at hq
          rw [eq_comm, midpoint_eq_right_iff] at hq
          exact hq)
      · exact midpoint_mem_segment _ _
    obtain ⟨r, hr, σ, _, hlocal⟩ :=
      two_sides T.children.disjoint hXmem hYmem hXY j k hside.symm hqopen
    have hqint : q ∈ interior (support T.children.tiles) := by
      rw [mem_interior_iff_mem_nhds]
      apply Filter.mem_of_superset (Metric.ball_mem_nhds q hr)
      intro x hx
      by_cases hnonneg : 0 ≤ σ * jcr (X.1.vertex (finRotate _ j) - X.1.vertex j)
          (x - X.1.vertex j)
      · exact carrier_subset_support hXmem ((hlocal x hx).2.2 hnonneg)
      · exact carrier_subset_support hYmem
          (interior_subset ((hlocal x hx).2.1 (lt_of_not_ge hnonneg)))
    have hqfront : q ∈ D.macroBoundary α := by
      apply hout
      rw [hj, tile_side_eq]
      exact openSegment_subset_segment ℝ _ _ hqopen
    unfold MacroData.macroBoundary at hqfront
    rw [emcd_outer_step2_region
      τ h g s l hl routing] at hqfront
    rw [T.support_eq] at hqint
    exact False.elim (hqfront.2 hqint)

private lemma
    emcd_outer_step2_mid_mem
    (D : MacroData P) (o : D.SideOcc) : D.occMid o ∈ D.occSide o := by
  rw [MacroData.occSide, tile_side_eq]
  exact midpoint_mem_segment _ _

private lemma
    emcd_outer_step2_parallel
    (D : MacroData P) (α : D.Q.Form) (d : Fin (D.Q.disk α).n) {x y : Pt}
    (hx : x ∈ D.macroSide α d) (hy : y ∈ D.macroSide α d) :
    ∃ r : ℝ, y - x = r • D.macroSideDir α d := by
  classical
  let p := D.σ.θ • (D.Q.disk α).vertex d
  let q := D.σ.θ • (D.Q.disk α).vertex (finRotate _ d)
  have hside : D.macroSide α d = segment ℝ p q := by
    simp only [MacroData.macroSide, PolygonalDisk.side, emcg_smul_segment, p, q]
  rw [hside] at hx hy
  obtain ⟨a, _, _, ha⟩ := mem_segment_iff'.mp hx
  obtain ⟨b, _, _, hb⟩ := mem_segment_iff'.mp hy
  unfold MacroData.macroSideDir MacroData.posDir
  change ∃ r : ℝ, y - x = r • (if D.IsPositive (q - p) then q - p else p - q)
  by_cases hpos : D.IsPositive (q - p)
  · refine ⟨b - a, ?_⟩
    rw [if_pos hpos, ha, hb]
    module
  · refine ⟨a - b, ?_⟩
    rw [if_neg hpos, ha, hb]
    module

private lemma
    emcd_outer_step2_dir_pos
    (D : MacroData P) (hpositive : D.IsPositive = LexPositive) :
    ∀ α d, LexPositive (D.macroSideDir α d) := by
  classical
  intro α d
  let v := D.σ.θ • (D.Q.disk α).vertex (finRotate _ d) -
    D.σ.θ • (D.Q.disk α).vertex d
  have hv : v ≠ 0 := by
    dsimp only [v]
    rw [← smul_sub]
    apply smul_ne_zero (ne_of_gt (zero_lt_one.trans D.σ.one_lt))
    apply sub_ne_zero.mpr
    intro heq
    exact emcg_finRotate_ne
      (le_trans (by decide : 2 ≤ 3) (D.Q.disk α).three_le) d
      ((D.Q.disk α).vertex_injective heq)
  unfold MacroData.macroSideDir MacroData.posDir
  rw [hpositive]
  change LexPositive (if LexPositive v then v else
    D.σ.θ • (D.Q.disk α).vertex d -
      D.σ.θ • (D.Q.disk α).vertex (finRotate _ d))
  by_cases hpos : LexPositive v
  · simp [hpos]
  · rw [if_neg hpos]
    have hneg :
        D.σ.θ • (D.Q.disk α).vertex d -
          D.σ.θ • (D.Q.disk α).vertex (finRotate _ d) = -v := by
      dsimp only [v]
      module
    rw [hneg]
    exact
      (existsRoutingAfterPower_step2_ports_step1_intra_step2_clearance_lex_neg hv).resolve_left
        hpos

private lemma
    emcd_outer_step2_lex_smul
    {v : Pt} (hv : LexPositive v) {r : ℝ} (hr : LexPositive (r • v)) : 0 < r := by
  rcases hv with hv | ⟨hv0, hv1⟩
  · rcases hr with hr | ⟨hr0, hr1⟩
    · simp only [PiLp.smul_apply, smul_eq_mul] at hr
      nlinarith
    · simp only [PiLp.smul_apply, smul_eq_mul] at hr0 hr1
      have : r = 0 := (mul_eq_zero.mp hr0).resolve_right hv.ne'
      subst r
      simp at hr1
  · rcases hr with hr | ⟨_, hr1⟩
    · simp only [PiLp.smul_apply, smul_eq_mul, hv0, mul_zero] at hr
      exact (lt_irrefl 0 hr).elim
    · simp only [PiLp.smul_apply, smul_eq_mul] at hr1
      nlinarith

private lemma
    emcd_outer_step2_mid_ne
    (D : MacroData P) {o o' : D.SideOcc}
    (hrel : ∀ x ∈ D.occSide o, ∀ y ∈ D.occSide o',
      x = y ∨ LexPositive (y - x)) : D.occMid o ≠ D.occMid o' := by
  let a := D.occStart o
  let b := D.occEnd o
  have hab : a ≠ b := tile_vertex_ne_next (D.childTile o.1) o.2
  have ha : a ∈ D.occSide o := by
    rw [MacroData.occSide, tile_side_eq]
    exact left_mem_segment ℝ _ _
  have hb : b ∈ D.occSide o := by
    rw [MacroData.occSide, tile_side_eq]
    exact right_mem_segment ℝ _ _
  have hm :=
    emcd_outer_step2_mid_mem
      D o'
  intro heq
  have ham : a ≠ D.occMid o' := by
    intro haeq
    apply hab
    rw [← heq, MacroData.occMid] at haeq
    exact (midpoint_eq_left_iff ℝ).mp haeq.symm
  have hbm : b ≠ D.occMid o' := by
    intro hbeq
    apply hab
    rw [← heq, MacroData.occMid] at hbeq
    exact (midpoint_eq_right_iff ℝ).mp hbeq.symm
  have hlexa := (hrel a ha (D.occMid o') hm).resolve_left ham
  have hlexb := (hrel b hb (D.occMid o') hm).resolve_left hbm
  have hneg : D.occMid o' - b = -(D.occMid o' - a) := by
    rw [← heq]
    change midpoint ℝ a b - b = -(midpoint ℝ a b - a)
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    module
  rw [hneg] at hlexb
  simp only [LexPositive, PiLp.neg_apply] at hlexa hlexb
  rcases hlexa with h0 | ⟨h0, h1⟩ <;>
    rcases hlexb with h0' | ⟨h0', h1'⟩ <;> simp_all <;> linarith

private lemma
    emcd_outer_step2_pairwise
    {A : Type*} {R : A → A → Prop} {L : List A} (hp : L.Pairwise R)
    {a b : A} (ha : a ∈ L) (hb : b ∈ L) (hne : a ≠ b) : R a b ∨ R b a := by
  induction L with
  | nil => simp at ha
  | cons x L ih =>
      rw [List.pairwise_cons] at hp
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact (hne rfl).elim
      · exact Or.inl (hp.1 _ hb)
      · exact Or.inr (hp.1 _ ha)
      · exact ih hp.2 ha hb

/-- Step 2 of the blueprint proof of
`existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer`: the global
orientation `LexPositive` and the sorted outer-side lists `outerList`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step2_orientation_outer
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    D.IsPositive = LexPositive ∧
    (∀ α (d : Fin (D.Q.disk α).n) (o : D.SideOcc),
      o ∈ D.outerList α d ↔ D.owner o.1 = α ∧ D.IsOuter o ∧ D.occSide o ⊆ D.macroSide α d) ∧
    (∀ α d, (D.outerList α d).Nodup) ∧
    (∀ α d, (D.outerList α d).Pairwise fun o o' =>
      ∃ r : ℝ, 0 < r ∧ D.occMid o' - D.occMid o = r • D.macroSideDir α d) := by
  classical
  dsimp only
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro α d o
    change o ∈ emcdGeometricOuterList (emcdGeometryData τ h g s l hl routing) α d ↔
      (emcdGeometryData τ h g s l hl routing).owner o.1 = α ∧
        (emcdGeometryData τ h g s l hl routing).IsOuter o ∧
        (emcdGeometryData τ h g s l hl routing).occSide o ⊆
          (emcdGeometryData τ h g s l hl routing).macroSide α d
    simp [emcdGeometricOuterList]
  · intro α d
    change (emcdGeometricOuterList
      (emcdGeometryData τ h g s l hl routing) α d).Nodup
    rw [emcdGeometricOuterList, List.nodup_mergeSort]
    exact Finset.nodup_toList _
  · intro α d
    let B := emcdGeometryData τ h g s l hl routing
    let outer := Finset.univ.filter fun o : B.SideOcc =>
      B.owner o.1 = α ∧ B.IsOuter o ∧ B.occSide o ⊆ B.macroSide α d
    let coordinate := fun o : B.SideOcc =>
      (B.occMid o) 0 * (B.macroSideDir α d) 0 +
        (B.occMid o) 1 * (B.macroSideDir α d) 1
    letI : IsTrans B.SideOcc
        (fun o o' => coordinate o ≤ coordinate o') :=
      ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
    letI : Std.Total (fun o o' : B.SideOcc => coordinate o ≤ coordinate o') :=
      ⟨fun o o' => le_total (coordinate o) (coordinate o')⟩
    change (outer.toList.mergeSort fun o o' => decide (coordinate o ≤ coordinate o')).Pairwise
      fun o o' => ∃ r : ℝ, 0 < r ∧
        B.occMid o' - B.occMid o = r • B.macroSideDir α d
    have hsorted :
        (outer.toList.mergeSort fun o o' => decide (coordinate o ≤ coordinate o')).Pairwise
          (fun o o' => coordinate o ≤ coordinate o') := by
      exact List.pairwise_mergeSort' (fun o o' => coordinate o ≤ coordinate o') _
    have hnodup :
        (outer.toList.mergeSort fun o o' => decide (coordinate o ≤ coordinate o')).Nodup := by
      rw [List.nodup_mergeSort]
      exact Finset.nodup_toList _
    let base := emcdBaseForm g s l α
    let T := s.setup.retained l base
    obtain ⟨L, hLmem, _, hLpair, _⟩ :=
      (routing base).port_quantile (emcdParentSide g s l α d)
    have hregion : B.macroRegion α = T.region := by
      exact
        emcd_outer_step2_region
          τ h g s l hl routing α
    have htheta :=
      (existsMacroCertificate_seed2_routing_step3_data_sub4_representation
        τ h g s l hl routing).θ_eq
    change B.σ.θ = τ.θ ^ (g.k * l) at htheta
    have hpower : s.setup.GS.k = g.k := by
      calc
        s.setup.GS.k = g.GS.k := congrArg GroupedSubstitution.k s.setup_grouped
        _ = g.k := g.grouped_power
    have hmacro : B.macroSide α d =
        (τ.θ ^ (s.setup.GS.k * l)) •
          (s.setup.GS.G.P'.disk base).side (emcdParentSide g s l α d) := by
      unfold MacroData.macroSide
      rw [htheta, ← hpower]
      rfl
    have hdir : LexPositive (B.macroSideDir α d) := by
      exact
        emcd_outer_step2_dir_pos
          B rfl α d
    apply List.Pairwise.imp_of_mem _ (List.pairwise_and_iff.mpr ⟨hsorted, hnodup⟩)
    intro o o' ho ho' hle
    have homem : B.owner o.1 = α ∧ B.IsOuter o ∧
        B.occSide o ⊆ B.macroSide α d := by
      have hm := (List.mergeSort_perm outer.toList _).mem_iff.mp ho
      simpa [outer] using hm
    have ho'mem : B.owner o'.1 = α ∧ B.IsOuter o' ∧
        B.occSide o' ⊆ B.macroSide α d := by
      have hm := (List.mergeSort_perm outer.toList _).mem_iff.mp ho'
      simpa [outer] using hm
    have htemplate : ∀ {z : B.SideOcc}, B.owner z.1 = α → B.IsOuter z →
        T.IsOuter (B.occSide z) := by
      rintro ⟨⟨β, X⟩, i⟩ hzowner hzouter
      change β = α at hzowner
      subst β
      obtain ⟨j, hj⟩ :=
        emcd_outer_step2_child_side
          τ h g s l hl routing ⟨α, X⟩ i
      constructor
      · exact ⟨emcdTemplateChild g s l ⟨α, X⟩, X.2, j, hj.symm⟩
      · change B.occSide ⟨⟨α, X⟩, i⟩ ⊆ frontier T.region
        rw [← hregion]
        exact hzouter
    have hoL : B.occSide o ∈ L := (hLmem _).2 ⟨htemplate homem.1 homem.2.1, by
      rw [← hmacro]
      exact homem.2.2⟩
    have ho'L : B.occSide o' ∈ L := (hLmem _).2
      ⟨htemplate ho'mem.1 ho'mem.2.1, by rw [← hmacro]; exact ho'mem.2.2⟩
    have hsides : B.occSide o ≠ B.occSide o' := by
      intro hs
      apply hle.2
      exact
        emcd_outer_step2_occ_injective
          τ h g s l hl routing (o := o) (o' := o')
            (homem.1.trans ho'mem.1.symm) homem.2.1 ho'mem.2.1 hs
    have horient :=
      emcd_outer_step2_pairwise
        hLpair hoL ho'L hsides
    have hmid :=
      emcd_outer_step2_mid_mem
        B
    obtain ⟨r, hr⟩ :=
      emcd_outer_step2_parallel
        B α d (homem.2.2 (hmid o)) (ho'mem.2.2 (hmid o'))
    rcases horient with horient | horient
    · have hmn :=
        emcd_outer_step2_mid_ne
          B horient
      have hlex := (horient (B.occMid o) (hmid o) (B.occMid o') (hmid o')).resolve_left hmn
      rw [hr] at hlex
      exact ⟨r,
        emcd_outer_step2_lex_smul
          hdir hlex, hr⟩
    · have hmn :=
        emcd_outer_step2_mid_ne
          B horient
      have hlex := (horient (B.occMid o') (hmid o') (B.occMid o) (hmid o)).resolve_left hmn
      have hneg : B.occMid o - B.occMid o' = (-r) • B.macroSideDir α d := by
        rw [← neg_sub, hr]
        module
      rw [hneg] at hlex
      have hrneg :=
        emcd_outer_step2_lex_smul
          hdir hlex
      have hr0 := congrArg (fun z : Pt => z 0) hr
      have hr1 := congrArg (fun z : Pt => z 1) hr
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hr0 hr1
      dsimp only [coordinate] at hle
      have hnorm : 0 < (B.macroSideDir α d 0) ^ 2 +
          (B.macroSideDir α d 1) ^ 2 := by
        rcases hdir with hdir | ⟨hdir0, hdir1⟩
        · nlinarith [sq_nonneg (B.macroSideDir α d 1)]
        · nlinarith [sq_nonneg (B.macroSideDir α d 0)]
      have hcoord :
          ((B.occMid o') 0 * (B.macroSideDir α d) 0 +
              (B.occMid o') 1 * (B.macroSideDir α d) 1) -
            ((B.occMid o) 0 * (B.macroSideDir α d) 0 +
              (B.occMid o) 1 * (B.macroSideDir α d) 1) =
            r * ((B.macroSideDir α d 0) ^ 2 +
              (B.macroSideDir α d 1) ^ 2) := by
        calc
          _ = ((B.occMid o') 0 - (B.occMid o) 0) *
                (B.macroSideDir α d) 0 +
              ((B.occMid o') 1 - (B.occMid o) 1) *
                (B.macroSideDir α d) 1 := by ring
          _ = (r * (B.macroSideDir α d) 0) *
                (B.macroSideDir α d) 0 +
              (r * (B.macroSideDir α d) 1) *
                (B.macroSideDir α d) 1 := by rw [hr0, hr1]
          _ = _ := by ring
      have hprod : r * ((B.macroSideDir α d 0) ^ 2 +
          (B.macroSideDir α d 1) ^ 2) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) hnorm
      linarith [hle.1, hcoord, hprod]

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer`: constants N and Qmax. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step3_constants
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    D.N = g.N ∧ D.Qmax = g.Qmax := by
  exact ⟨rfl, rfl⟩

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer`: the sharp rank bound `rankBound`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step4_rankBound
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d, (D.outerList α d).length ≤ D.rankBound) ∧
    ∀ b, (∀ α d, (D.outerList α d).length ≤ b) → D.rankBound ≤ b := by
  let D := emcdMacroData τ h g s l hl routing
  change (∀ α d, (D.outerList α d).length ≤ D.rankBound) ∧
    ∀ b, (∀ α d, (D.outerList α d).length ≤ b) → D.rankBound ≤ b
  constructor
  · intro α d
    let a : Σ α : D.Q.Form, Fin (D.Q.disk α).n := ⟨α, d⟩
    exact Finset.le_sup
      (f := fun x : Σ α : D.Q.Form, Fin (D.Q.disk α).n =>
        (D.outerList x.1 x.2).length)
      (Finset.mem_univ a)
  · intro b hb
    exact Finset.sup_le
      (f := fun a : Σ α : D.Q.Form, Fin (D.Q.disk α).n =>
        (D.outerList a.1 a.2).length)
      (fun a _ => hb a.1 a.2)

/-- Step 4 of `lem:certificate-exists`: the internal interface specifications (`partner_spec`,
`edge_spec`, `edgeTypes_spec` from the two-owner property of inner sides in the STS template
`s.setup.retained l (emcdBaseForm g s l α)`), the global orientation `LexPositive`, the sorted
outer-side lists `outerList`, and the sharp rank bound `rankBound`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ o : D.SideOcc, D.IsInner o →
      (D.partner o).1 ≠ o.1 ∧ D.owner (D.partner o).1 = D.owner o.1 ∧
        D.occSide (D.partner o) = D.occSide o) ∧
    (∀ o o' : D.SideOcc, D.IsInner o → D.IsInner o' →
      (D.edge o = D.edge o' ↔ o' = o ∨ o' = D.partner o)) ∧
    (∀ o : D.SideOcc, D.IsInner o →
      D.edgeTypes (D.edge o) = (o.1, (D.partner o).1) ∨
        D.edgeTypes (D.edge o) = ((D.partner o).1, o.1)) ∧
    D.IsPositive = LexPositive ∧
    (∀ α (d : Fin (D.Q.disk α).n) (o : D.SideOcc),
      o ∈ D.outerList α d ↔ D.owner o.1 = α ∧ D.IsOuter o ∧ D.occSide o ⊆ D.macroSide α d) ∧
    (∀ α d, (D.outerList α d).Nodup) ∧
    (∀ α d, (D.outerList α d).Pairwise fun o o' =>
      ∃ r : ℝ, 0 < r ∧ D.occMid o' - D.occMid o = r • D.macroSideDir α d) ∧
    D.N = g.N ∧
    D.Qmax = g.Qmax ∧
    (∀ α d, (D.outerList α d).length ≤ D.rankBound) ∧
    ∀ b, (∀ α d, (D.outerList α d).length ≤ b) → D.rankBound ≤ b := by
  dsimp only
  obtain ⟨hpart, hedge, hedge_t⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces
      τ h g s l hl routing
  obtain ⟨hpos, hout_mem, hout_nodup, hout_sort⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step2_orientation_outer
      τ h g s l hl routing
  obtain ⟨hN, hQmax⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step3_constants
      τ h g s l hl routing
  obtain ⟨hrank_ge, hrank_max⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step4_rankBound
      τ h g s l hl routing
  exact ⟨hpart, hedge, hedge_t, hpos, hout_mem, hout_nodup, hout_sort,
    hN, hQmax, hrank_ge, hrank_max⟩

private lemma emcd_scatter_covers_child (G : GroupedFamily P) (C : PlacedTile G.mixed) :
    C.carrier ⊆ support (G.mixedScatterTile C) := by
  rcases C with ⟨f, a⟩
  rcases f with β | q
  · intro x hx
    simp only [PlacedTile.carrier] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change y ∈ (G.P'.disk β).carrier at hy
    rw [← G.support_eq β] at hy
    obtain ⟨T, hT, hyT⟩ := mem_support_iff'.1 hy
    refine mem_support_iff'.2 ⟨T.translate a, ?_, ?_⟩
    · simp only [GroupedFamily.mixedScatterTile, Sum.elim_inl, translateSet]
      exact ⟨T, hT, rfl⟩
    · simp only [PlacedTile.carrier, PlacedTile.translate] at hyT ⊢
      obtain ⟨w, hw, rfl⟩ := hyT
      exact ⟨w, hw, by simp [vadd_eq_add, add_assoc]⟩
  · intro x hx
    refine mem_support_iff'.2 ⟨⟨q, a⟩, ?_, hx⟩
    simp [GroupedFamily.mixedScatterTile]

private lemma emcd_scatter_tile_carrier (G : GroupedFamily P) (C : PlacedTile G.mixed)
    {A : PlacedTile P} (hA : A ∈ G.mixedScatterTile C) : A.carrier ⊆ C.carrier := by
  rcases C with ⟨f, a⟩
  rcases f with β | q
  · simp only [GroupedFamily.mixedScatterTile, Sum.elim_inl, translateSet,
      Set.mem_image] at hA
    obtain ⟨T, hT, rfl⟩ := hA
    have hsub : T.carrier ⊆ (G.P'.disk β).carrier := by
      rw [← G.support_eq β]
      exact carrier_subset_support hT
    intro x hx
    simp only [PlacedTile.carrier, PlacedTile.translate] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨T.anchor +ᵥ y, hsub ⟨y, hy, rfl⟩, ?_⟩
    simp [vadd_eq_add, add_assoc]
  · simp only [GroupedFamily.mixedScatterTile, Sum.elim_inr,
      Set.mem_singleton_iff] at hA
    subst hA
    intro x hx
    exact hx

private lemma emcd_tile_coord (M : MeshConstants P) (A : PlacedTile P)
    {x y : Pt} (hx : x ∈ A.carrier) (hy : y ∈ A.carrier) (i : Fin 2) :
    |x i - y i| ≤ M.D := by
  have hcoord : |x i - y i| ≤ dist x y := by
    have hi := PiLp.norm_apply_le (x - y) i
    rw [Real.norm_eq_abs, PiLp.sub_apply] at hi
    rwa [dist_eq_norm]
  refine hcoord.trans
    ((Metric.dist_le_diam_of_mem (tileDisk A).compact.isBounded hx hy).trans ?_)
  have hdiam : Metric.diam A.carrier = Metric.diam (P.disk A.form).carrier := by
    rw [PlacedTile.carrier]
    exact diam_vadd _ _
  show Metric.diam A.carrier ≤ M.D
  rw [hdiam]
  exact M.diam_le _

private lemma emcd_original_child_annular_member
    (τ : Substitution P) (M : MeshConstants P) (Rs : RoutingSetup τ M) (l : ℕ)
    (hl : 0 < l) (α : Rs.GS.G.P'.Form) {p : P.Form} {X : PlacedTile Rs.GS.G.mixed}
    (hX : X ∈ (Rs.retained l α).children.tiles) (hXc : X ≠ Rs.central l α)
    {k : Fin (Rs.GS.G.mixed.disk (Rs.central l α).form).n}
    (hk : HasEdge X ((Rs.central l α).side k)) (hXp : X.form = Sum.inr p) :
    ∃ j : Fin (4 * Rs.N α),
      (⟨p, X.anchor⟩ : PlacedTile P) ∈ ((Rs.annulus l α hl).spokes.piece j).faces := by
  set A : PlacedTile P := ⟨p, X.anchor⟩
  have hdisj := (Rs.retained l α).children.disjoint
  have hAX : A.carrier = X.carrier := by simp [A, PlacedTile.carrier, hXp]
  have hscX : Rs.GS.G.mixedScatterTile X = {A} := by
    simp [GroupedFamily.mixedScatterTile, hXp, A]
  have hAS : A ∈ Rs.GS.G.mixedScatter (Rs.retained l α).children.tiles :=
    Set.mem_biUnion hX (by rw [hscX]; rfl)
  obtain ⟨z, hz⟩ : (interior X.carrier).Nonempty := by
    rw [PlacedTile.carrier, interior_vadd]
    exact (Rs.GS.G.mixed.disk X.form).interior_nonempty.vadd_set
  have hAL : A ∉ (Rs.annulus l α hl).L.faces := by
    intro hA
    rw [← Rs.central_scatter l α hl] at hA
    have hsub := emcd_scatter_tile_carrier Rs.GS.G _ hA
    rw [hAX] at hsub
    exact interior_not_mem_other hdisj hX (Rs.central_mem l α) hXc hz
      (hsub (interior_subset hz))
  have hR : 0 ≤ Rs.R α := by
    have h1 := Rs.R_large α
    have h2 := M.D_pos
    have h3 : 0 ≤ 10000 * ((M.K0 : ℝ) + 3) * M.D := by positivity
    linarith
  have hXH : X.carrier ⊆ (Rs.annulus l α hl).H.carrier := by
    obtain ⟨i, hi⟩ := hk
    set y := (Rs.central l α).vertex k
    have hyside : y ∈ (Rs.central l α).side k := by
      rw [tile_side_eq]
      exact left_mem_segment ℝ _ _
    have hyX : y ∈ X.carrier := tile_side_subset X i (hi ▸ hyside)
    have hyL : y ∈ (Rs.annulus l α hl).L.carrier := by
      have h1 := emcd_scatter_covers_child Rs.GS.G (Rs.central l α)
        (tile_side_subset _ k hyside)
      rw [Rs.central_scatter l α hl, ← (Rs.annulus l α hl).L.carrier_eq] at h1
      exact h1
    obtain ⟨u, hu, v, hv, huv⟩ := (Rs.annulus l α hl).L_upper hyL
    intro x hx
    apply (Rs.annulus l α hl).H_lower
    have hcoord : ∀ i : Fin 2, |x i - y i| ≤ M.D := fun i =>
      emcd_tile_coord M A (hAX ▸ hx) (hAX ▸ hyX) i
    refine ⟨u, ⟨?_, ?_⟩, x - u, ⟨?_, ?_⟩, add_sub_cancel u x⟩
    · exact hu.1.trans (by linarith)
    · exact hu.2.trans (by linarith)
    · have hc := hcoord 0
      have hv0 := hv.1
      rw [← huv] at hc
      simp only [PiLp.sub_apply, PiLp.add_apply] at hc ⊢
      calc
        |x 0 - u 0| = |(x 0 - (u 0 + v 0)) + v 0| := by ring_nf
        _ ≤ |x 0 - (u 0 + v 0)| + |v 0| := abs_add_le _ _
        _ ≤ 2 * M.D := by linarith
    · have hc := hcoord 1
      have hv1 := hv.2
      rw [← huv] at hc
      simp only [PiLp.sub_apply, PiLp.add_apply] at hc ⊢
      calc
        |x 1 - u 1| = |(x 1 - (u 1 + v 1)) + v 1| := by ring_nf
        _ ≤ |x 1 - (u 1 + v 1)| + |v 1| := abs_add_le _ _
        _ ≤ 2 * M.D := by linarith
  have hAH : A ∈ (Rs.annulus l α hl).H.faces := by
    have hzH : z ∈ (Rs.annulus l α hl).H.carrier := hXH (interior_subset hz)
    change z ∈ (Rs.annulus l α hl).H.disk.carrier at hzH
    rw [(Rs.annulus l α hl).H.carrier_eq] at hzH
    obtain ⟨F, hF, hzF⟩ := mem_support_iff'.1 hzH
    have hFS := (Rs.annulus l α hl).H.faces_sub hF
    simp only [GroupedFamily.mixedScatter, Set.mem_iUnion] at hFS
    obtain ⟨Y, hY, hFY⟩ := hFS
    have hFYc := emcd_scatter_tile_carrier Rs.GS.G Y hFY
    by_cases hYX : Y = X
    · subst hYX
      rw [hscX] at hFY
      rw [Set.mem_singleton_iff] at hFY
      exact hFY ▸ hF
    · exact absurd (hFYc hzF)
        (interior_not_mem_other hdisj hX hY (Ne.symm hYX) hz)
  obtain ⟨j, hj, -⟩ := ((Rs.annulus l α hl).spokes.piece_partition A hAS).1 ⟨hAH, hAL⟩
  exact ⟨j, hj⟩

private lemma emcd_annular_child_collision
    (τ : Substitution P) (M : MeshConstants P) (Rs : RoutingSetup τ M) (l : ℕ)
    (hl : 0 < l) (α : Rs.GS.G.P'.Form) {p : P.Form}
    {X Y : PlacedTile Rs.GS.G.mixed} {j : Fin (4 * Rs.N α)}
    (hX : X ∈ (Rs.retained l α).children.tiles) (hXc : X ≠ Rs.central l α)
    (hXp : X.form = Sum.inr p) (hY : Y ∈ (Rs.retained l α).children.tiles)
    (hYc : Y ≠ Rs.central l α)
    (hYj : Rs.GS.G.mixedScatterTile Y = ((Rs.annulus l α hl).spokes.piece j).faces)
    (hXj : (⟨p, X.anchor⟩ : PlacedTile P) ∈
      ((Rs.annulus l α hl).spokes.piece j).faces) : Y = X := by
  have _ := hXc
  have _ := hYc
  have hmem : (⟨p, X.anchor⟩ : PlacedTile P) ∈ Rs.GS.G.mixedScatterTile Y := by
    rw [hYj]
    exact hXj
  have hsub : (⟨p, X.anchor⟩ : PlacedTile P).carrier ⊆ Y.carrier :=
    emcd_scatter_tile_carrier Rs.GS.G Y hmem
  have hXsub : X.carrier ⊆ Y.carrier := by
    intro x hx
    apply hsub
    simpa [PlacedTile.carrier, hXp] using hx
  by_contra hYX
  have hXY : X ≠ Y := fun h => hYX h.symm
  have hdisj := (Rs.retained l α).children.disjoint hX hY hXY
  have hnonempty : (interior X.carrier).Nonempty := by
    rw [PlacedTile.carrier, interior_vadd]
    exact (Rs.GS.G.mixed.disk X.form).interior_nonempty.vadd_set
  obtain ⟨x, hx⟩ := hnonempty
  exact Set.disjoint_left.1 hdisj hx (interior_mono hXsub hx)

private lemma emcd_annular_piece_two_faces
    (τ : Substitution P) (M : MeshConstants P) (Rs : RoutingSetup τ M) (l : ℕ)
    (hl : 0 < l) (α : Rs.GS.G.P'.Form) :
    ∀ j : Fin (4 * Rs.N α), ∃ A B : PlacedTile P,
      A ∈ ((Rs.annulus l α hl).spokes.piece j).faces ∧
      B ∈ ((Rs.annulus l α hl).spokes.piece j).faces ∧ A ≠ B := by
  intro j
  obtain ⟨e, he, hsep⟩ := Rs.windows l α hl
  obtain ⟨⟨A, hA, i, hAi⟩, -⟩ := he j 0
  obtain ⟨⟨B, hB, k, hBk⟩, -⟩ := he j 1
  refine ⟨A, B, hA, hB, ?_⟩
  rintro rfl
  have hxs : A.vertex i ∈ A.side i :=
    ⟨(P.disk A.form).vertex i, left_mem_segment ℝ _ _, rfl⟩
  have hys : A.vertex k ∈ A.side k :=
    ⟨(P.disk A.form).vertex k, left_mem_segment ℝ _ _, rfl⟩
  have hx : A.vertex i ∈ e j 0 := hAi ▸ hxs
  have hy : A.vertex k ∈ e j 1 := hBk ▸ hys
  have h1 := hsep j 0 j 1 (by simp) _ hx _ hy
  have h2 := step5_tile_dist_le M A (tile_side_subset A i hxs) (tile_side_subset A k hys)
  have h3 := Rs.R_large α
  have hD := M.D_pos
  have hK : (0 : ℝ) ≤ M.K0 := Nat.cast_nonneg _
  nlinarith

private lemma emcd_noncentral_edge_grouped
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (α : s.setup.GS.G.P'.Form) {X : PlacedTile s.setup.GS.G.mixed}
    (hX : X ∈ (s.setup.retained l α).children.tiles)
    (hXc : X ≠ s.setup.central l α)
    {k : Fin (s.setup.GS.G.mixed.disk (s.setup.central l α).form).n}
    (hk : HasEdge X ((s.setup.central l α).side k)) :
    ∃ β, X.form = Sum.inl β := by
  cases hform : X.form with
  | inl β => exact ⟨β, rfl⟩
  | inr p =>
    exfalso
    obtain ⟨j, hXj⟩ := emcd_original_child_annular_member
      τ g.M s.setup l hl α hX hXc hk hform
    obtain ⟨Y, hY, hYc, hYj⟩ := s.setup.piece_child l α hl j
    have hYX := emcd_annular_child_collision
      τ g.M s.setup l hl α hX hXc hform hY hYc hYj hXj
    rw [hYX] at hYj
    have hscatter : s.setup.GS.G.mixedScatterTile X =
        ({⟨p, X.anchor⟩} : Set (PlacedTile P)) := by
      simp [GroupedFamily.mixedScatterTile, hform]
    rw [hscatter] at hYj
    obtain ⟨A, B, hA, hB, hAB⟩ :=
      emcd_annular_piece_two_faces τ g.M s.setup l hl α j
    have hA' : A ∈ ({⟨p, X.anchor⟩} : Set (PlacedTile P)) := hYj.symm ▸ hA
    have hB' : B ∈ ({⟨p, X.anchor⟩} : Set (PlacedTile P)) := hYj.symm ▸ hB
    have hAe : A = ⟨p, X.anchor⟩ := by simpa using hA'
    have hBe : B = ⟨p, X.anchor⟩ := by simpa using hB'
    exact hAB (hAe.trans hBe.symm)

private lemma emcd_prints_grouped_side
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (X : PlacedTile s.setup.GS.G.mixed) (γ : s.setup.GS.G.P'.Form)
    (hX : X.form = Sum.inl γ) (hμ : emcdIsRetainedForm g s l X.form)
    (j : Fin (s.setup.GS.G.mixed.disk X.form).n) :
    ∃ i, (⟨⟨X.form, hμ⟩, X.anchor⟩ : PlacedTile (emcdQ g s l)).side i = X.side j := by
  obtain ⟨f, a⟩ := X
  simp only at hX
  subst hX
  exact ⟨j, rfl⟩

private lemma emcd_prints_grouped_side_val
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (X : PlacedTile s.setup.GS.G.mixed) (γ : s.setup.GS.G.P'.Form)
    (hX : X.form = Sum.inl γ) (hμ : emcdIsRetainedForm g s l X.form)
    (j : Fin (s.setup.GS.G.mixed.disk X.form).n) :
    ∃ i, i.val = j.val ∧
      (⟨⟨X.form, hμ⟩, X.anchor⟩ : PlacedTile (emcdQ g s l)).side i = X.side j := by
  obtain ⟨f, a⟩ := X
  simp only at hX
  subst hX
  exact ⟨j, rfl, rfl⟩

private lemma emcd_prints_grouped_occ_side
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ (t : D.Typ) (γ : s.setup.GS.G.P'.Form),
      (emcdTemplateChild g s l t).form = Sum.inl γ → ∀ i : D.Side t,
        ∃ j : Fin (s.setup.GS.G.mixed.disk (emcdTemplateChild g s l t).form).n,
          j.val = i.val ∧ D.occSide (D.occ t i) = (emcdTemplateChild g s l t).side j := by
  intro D t γ ht i
  rcases t with ⟨α, ⟨⟨f, a⟩, hf⟩⟩
  simp only at ht
  subst ht
  exact ⟨i, rfl, rfl⟩

private lemma emcd_prints_occ_eq_of_type_eq
    (D : MacroData P) (o o' : D.SideOcc) (ht : o.1 = o'.1)
    (hs : D.occSide o = D.occSide o') : o = o' := by
  cases o with
  | mk t i =>
      cases o' with
      | mk t' i' =>
          simp only at ht
          subst t'
          have hii : i = i' := by
            apply emcd_outer_step2_side_injective
            apply Set.Subset.antisymm
            · apply (Set.vadd_set_subset_vadd_set_iff (a := D.anchor t)).1
              exact hs.subset
            · apply (Set.vadd_set_subset_vadd_set_iff (a := D.anchor t)).1
              exact hs.symm.subset
          subst i'
          rfl

private lemma emcd_print_occ_transport (D : MacroData P) {alpha beta : D.Q.Form}
    (hab : alpha = beta) (d : Fin (D.Q.disk alpha).n) :
    D.printOcc alpha d = D.printOcc beta (hab ▸ d) := by
  subst beta
  rfl

private lemma emcd_marked_transport (D : MacroData P) {alpha beta : D.Q.Form}
    (hab : alpha = beta) (d : Fin (D.Q.disk alpha).n) (hd : D.marked alpha d) :
    D.marked beta (hab ▸ d) := by
  subst beta
  exact hd

set_option maxHeartbeats 3000000 in
private lemma emcd_prints_other_is_partner
    (tau : Substitution P) (h : tau.STS) (g : existsMacroCertificate_GroupingSeed tau)
    (s : existsMacroCertificate_SetupSeed tau g) (l : Nat) (hl : 0 < l)
    (routing : ∀ alpha, RoutingData (s.setup.retained l alpha) (s.setup.GS.G.P'.disk alpha)
      (tau.θ ^ (s.setup.GS.k * l)) (s.setup.central l alpha) (s.setup.markedSides alpha)
      ((s.setup.markedSides (s.setup.c^[l] alpha)).map Fin.valEmbedding)) :
    let D := emcdMacroData tau h g s l hl routing
    ∀ o o' : D.SideOcc, D.owner o'.1 = D.owner o.1 → o'.1 ≠ o.1 →
      D.occSide o' = D.occSide o → D.IsInner o ∧ o' = D.partner o := by
  intro D o o' howner hne hside
  have hinner : D.IsInner o := by
    intro hout
    have hout' : D.IsOuter o' := by
      simpa only [MacroData.IsOuter, howner, hside] using hout
    have heq := emcd_outer_step2_occ_injective tau h g s l hl routing
      howner.symm hout hout' hside.symm
    exact hne (congrArg Sigma.fst heq).symm
  refine ⟨hinner, ?_⟩
  let B := emcdGeometryData tau h g s l hl routing
  have hex : ∃ z : B.SideOcc, z.1 ≠ o.1 ∧ B.owner z.1 = B.owner o.1 ∧
      B.occSide z = B.occSide o := ⟨o', hne, howner, hside⟩
  have hpartner_eq : D.partner o = hex.choose := by
    change emcdGeometricPartner B o = hex.choose
    unfold emcdGeometricPartner
    rw [dif_pos hex]
  have hp_ne : (D.partner o).1 ≠ o.1 := by
    rw [hpartner_eq]
    exact hex.choose_spec.1
  have hp_owner : D.owner (D.partner o).1 = D.owner o.1 := by
    rw [hpartner_eq]
    exact hex.choose_spec.2.1
  have hp_side : D.occSide (D.partner o) = D.occSide o := by
    rw [hpartner_eq]
    exact hex.choose_spec.2.2
  have htype : ∀ t u : D.Typ, D.owner t = D.owner u →
      emcdTemplateChild g s l t = emcdTemplateChild g s l u → t = u := by
    rintro ⟨alpha, X⟩ ⟨beta, Y⟩ hab hXY
    change alpha = beta at hab
    subst beta
    change X.1 = Y.1 at hXY
    have : X = Y := Subtype.ext hXY
    subst Y
    rfl
  let T := s.setup.retained l (emcdBaseForm g s l (D.owner o.1))
  have hmem : ∀ t : D.Typ, emcdTemplateChild g s l t ∈
      (s.setup.retained l (emcdBaseForm g s l (D.owner t))).children.tiles := by
    rintro ⟨alpha, X⟩
    exact X.2
  have hom : emcdTemplateChild g s l o.1 ∈ T.children.tiles := hmem o.1
  have hpm : emcdTemplateChild g s l (D.partner o).1 ∈ T.children.tiles := by
    have hm := hmem (D.partner o).1
    rw [hp_owner] at hm
    exact hm
  have ho'm : emcdTemplateChild g s l o'.1 ∈ T.children.tiles := by
    have hm := hmem o'.1
    rw [howner] at hm
    exact hm
  obtain ⟨io, hio⟩ := emcd_outer_step2_child_side tau h g s l hl routing o.1 o.2
  obtain ⟨ip, hip⟩ :=
    emcd_outer_step2_child_side tau h g s l hl routing (D.partner o).1 (D.partner o).2
  obtain ⟨io', hio'⟩ := emcd_outer_step2_child_side tau h g s l hl routing o'.1 o'.2
  have hop_ne : emcdTemplateChild g s l o.1 ≠
      emcdTemplateChild g s l (D.partner o).1 := by
    intro heq
    exact hp_ne (htype o.1 (D.partner o).1 hp_owner.symm heq).symm
  have hoo'_ne : emcdTemplateChild g s l o.1 ≠ emcdTemplateChild g s l o'.1 := by
    intro heq
    exact hne (htype o'.1 o.1 howner heq.symm)
  have hchildren : emcdTemplateChild g s l (D.partner o).1 =
      emcdTemplateChild g s l o'.1 := by
    apply side_partner_unique T.children.disjoint hom hpm ho'm hop_ne hoo'_ne io ip io'
    · exact hip.symm.trans (hp_side.trans hio)
    · exact hio'.symm.trans (hside.trans hio)
  have htypes : o'.1 = (D.partner o).1 :=
    htype o'.1 (D.partner o).1 (howner.trans hp_owner.symm) hchildren.symm
  exact emcd_prints_occ_eq_of_type_eq D o' (D.partner o) htypes
    (hside.trans hp_side.symm)

set_option maxHeartbeats 3000000 in
/-- Step 4 of `lem:certificate-exists`: the print and special-side clauses for `emcdMacroData`:
prints use `(routing (emcdBaseForm g s l α)).printIdx`, inheriting injectivity, cyclic order, and
innerness from `RoutingData` (`print_injOn`, `print_cyclic`, `print_inner`), their opposite partner
lies on a small annular child (`RoutingData.path_last`, `RoutingData.path_step`,
`RoutingData.path_last_tile`), and under distinctness of print partner children (`hpartner_inj`),
every small child type has a unique special contact side with the central child, equal to the print
partner when the small child receives a print. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub6_prints_and_special
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (hpartner_inj : ∀ β : s.setup.GS.G.P'.Form,
      ∀ a ∈ s.setup.markedSides β, ∀ b ∈ s.setup.markedSides β,
        ∀ X ∈ (s.setup.retained l β).children.tiles, X ≠ s.setup.central l β →
          HasEdge X ((s.setup.central l β).side ((routing β).printIdx a)) →
          HasEdge X ((s.setup.central l β).side ((routing β).printIdx b)) → a = b) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d, D.occSide (D.printOcc α d) =
      (s.setup.central l (emcdBaseForm g s l α)).side
        ((routing (emcdBaseForm g s l α)).printIdx (emcdParentSide g s l α d))) ∧
    (∀ α (d d' : Fin (D.Q.disk α).n), D.marked α d → D.marked α d' →
      D.print α d = D.print α d' → d = d') ∧
    (∀ α (a b e : Fin (D.Q.disk α).n), D.marked α a → D.marked α b →
      D.marked α e → CycLt3 a b e → CycLt3 (D.print α a) (D.print α b) (D.print α e)) ∧
    (∀ α d, D.marked α d → D.IsInner (D.printOcc α d)) ∧
    (∀ α d, D.marked α d → D.kind (D.form (D.partner (D.printOcc α d)).1) = .small) ∧
    (∀ o : D.SideOcc, D.special o → D.kind (D.form o.1) = .small) ∧
    (∀ t, D.kind (D.form t) = .small → ∃! i, D.special (D.occ t i)) ∧
    (∀ o : D.SideOcc, D.special o →
      D.IsInner o ∧ (D.partner o).1 = D.central (D.owner o.1)) ∧
    ∀ α d, D.marked α d → D.special (D.partner (D.printOcc α d)) := by
  classical
  intro D
  have htype : ∀ t u : D.Typ, D.owner t = D.owner u →
      emcdTemplateChild g s l t = emcdTemplateChild g s l u → t = u := by
    rintro ⟨α, X⟩ ⟨β, Y⟩ hab hXY
    change α = β at hab
    subst β
    change X.1 = Y.1 at hXY
    have : X = Y := Subtype.ext hXY
    subst Y
    rfl
  have hcentralChild : ∀ α,
      emcdTemplateChild g s l (D.central α) =
        s.setup.central l (emcdBaseForm g s l α) := by
    intro α
    rfl
  have hcentralOwner : ∀ α, D.owner (D.central α) = α := by
    intro α
    rfl
  have hcentralOcc : ∀ α
      (j : Fin (s.setup.GS.G.mixed.disk
        (s.setup.central l (emcdBaseForm g s l α)).form).n),
      ∃ i, i.val = j.val ∧ D.occSide ⟨D.central α, i⟩ =
        (s.setup.central l (emcdBaseForm g s l α)).side j := by
    intro α j
    exact emcd_prints_grouped_side_val g s l
      (s.setup.central l (emcdBaseForm g s l α)) _
      (s.setup.central_form l (emcdBaseForm g s l α)) _ j
  have hprintRoute : ∀ α d, D.occSide (D.printOcc α d) =
      (s.setup.central l (emcdBaseForm g s l α)).side
        ((routing (emcdBaseForm g s l α)).printIdx
          (emcdParentSide g s l α d)) := by
    intro α d
    obtain ⟨i, _, hi⟩ := hcentralOcc α
      ((routing (emcdBaseForm g s l α)).printIdx (emcdParentSide g s l α d))
    have hp : ∃ i : D.Side (D.central α), D.occSide ⟨D.central α, i⟩ =
        (s.setup.central l (emcdBaseForm g s l α)).side
          ((routing (emcdBaseForm g s l α)).printIdx
            (emcdParentSide g s l α d)) := ⟨i, hi⟩
    have hprintEq : D.print α d = hp.choose := by
      show (if hp : _ then _ else _) = _
      split
      · rfl
      · rename_i hn
        exact absurd hp hn
    show D.occSide ⟨D.central α, D.print α d⟩ = _
    rw [hprintEq]
    exact hp.choose_spec
  have hprintVal : ∀ α d, (D.print α d).val =
      ((routing (emcdBaseForm g s l α)).printIdx
        (emcdParentSide g s l α d)).val := by
    intro α d
    let r := (routing (emcdBaseForm g s l α)).printIdx
      (emcdParentSide g s l α d)
    obtain ⟨i, hival, hi⟩ := hcentralOcc α r
    have hoi : D.printOcc α d = D.occ (D.central α) i :=
      emcd_prints_occ_eq_of_type_eq D _ _ rfl ((hprintRoute α d).trans hi.symm)
    exact (congrArg (fun z : D.SideOcc => z.2.val) hoi).trans hival
  have hmarked : ∀ α d, D.marked α d →
      emcdParentSide g s l α d ∈ s.setup.markedSides (emcdBaseForm g s l α) := by
    intro α d hd
    exact hd
  have hprintData : ∀ α d, D.marked α d →
      D.IsInner (D.printOcc α d) ∧
        (D.partner (D.printOcc α d)).1 ≠ (D.printOcc α d).1 ∧
        D.owner (D.partner (D.printOcc α d)).1 = D.owner (D.printOcc α d).1 ∧
        D.occSide (D.partner (D.printOcc α d)) = D.occSide (D.printOcc α d) := by
    intro α d hd
    let β := emcdBaseForm g s l α
    let a := emcdParentSide g s l α d
    have hr := (routing β).print_inner a (hmarked α d hd)
    obtain ⟨A, hA, B, hB, hAB, hAe, hBe⟩ := hr
    have hc : HasEdge (s.setup.central l β)
        ((s.setup.central l β).side ((routing β).printIdx a)) :=
      ⟨(routing β).printIdx a, rfl⟩
    obtain ⟨X, hX, hXc, hXe⟩ : ∃ X,
        X ∈ (s.setup.retained l β).children.tiles ∧ X ≠ s.setup.central l β ∧
          HasEdge X ((s.setup.central l β).side ((routing β).printIdx a)) := by
      by_cases hAc : A = s.setup.central l β
      · exact ⟨B, hB, fun hBc => hAB (hAc.trans hBc.symm), hBe⟩
      · exact ⟨A, hA, hAc, hAe⟩
    obtain ⟨γ, hXf⟩ := emcd_noncentral_edge_grouped τ g s l hl β hX hXc hXe
    obtain ⟨j, hj⟩ := hXe
    let t : D.Typ := ⟨α, ⟨X, hX⟩⟩
    obtain ⟨i, hi⟩ := emcd_prints_grouped_side g s l X γ hXf
      (show emcdIsRetainedForm g s l X.form by
        change emcdIsRetainedForm g s l (emcdTemplateChild g s l t).form
        exact (D.form t).2) j
    let o : D.SideOcc := ⟨t, i⟩
    have howner : D.owner o.1 = α := rfl
    have hside : D.occSide o = D.occSide (D.printOcc α d) := by
      exact hi.trans (hj.trans (hprintRoute α d).symm)
    have hne : o.1 ≠ (D.printOcc α d).1 := by
      intro heq
      apply hXc
      have hchild := congrArg (emcdTemplateChild g s l) heq
      simpa [o, MacroData.printOcc] using hchild
    have hc := emcd_prints_other_is_partner τ h g s l hl routing
      (D.printOcc α d) o (by simpa using howner.trans (hcentralOwner α).symm)
      hne hside
    refine ⟨hc.1, ?_⟩
    rw [← hc.2]
    exact ⟨hne, howner.trans (hcentralOwner α).symm, hside⟩
  have hprintInner : ∀ α d, D.marked α d → D.IsInner (D.printOcc α d) := by
    intro α d hd
    exact (hprintData α d hd).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hkindSmall, _, _, _⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue τ h g s l hl routing
  have hprintSmall : ∀ α d, D.marked α d →
      D.kind (D.form (D.partner (D.printOcc α d)).1) = .small := by
    intro α d hd
    have hp := (hprintData α d hd).2
    let t := (D.partner (D.printOcc α d)).1
    let X := emcdTemplateChild g s l t
    have hXmem : X ∈ (s.setup.retained l
        (emcdBaseForm g s l (D.owner t))).children.tiles := by
      rcases t with ⟨β, Y⟩
      exact Y.2
    have hown : D.owner t = α := hp.2.1.trans (hcentralOwner α)
    have hXc : X ≠ s.setup.central l (emcdBaseForm g s l (D.owner t)) := by
      intro heq
      have htcent : t = D.central (D.owner t) :=
        htype t (D.central (D.owner t)) rfl (heq.trans (hcentralChild _).symm)
      apply hp.1
      change t = (D.printOcc α d).1
      exact htcent.trans ((congrArg D.central hown).trans rfl)
    obtain ⟨j, hj⟩ := emcd_outer_step2_child_side τ h g s l hl routing t
      (D.partner (D.printOcc α d)).2
    have hroute : D.occSide (D.partner (D.printOcc α d)) =
        (s.setup.central l (emcdBaseForm g s l α)).side
          ((routing (emcdBaseForm g s l α)).printIdx
            (emcdParentSide g s l α d)) := hp.2.2.trans (hprintRoute α d)
    have hXmem' : X ∈ (s.setup.retained l
        (emcdBaseForm g s l α)).children.tiles := by
      simpa only [hown] using hXmem
    have hXc' : X ≠ s.setup.central l (emcdBaseForm g s l α) := by
      simpa only [hown] using hXc
    have hXe : HasEdge X ((s.setup.central l
        (emcdBaseForm g s l α)).side
          ((routing (emcdBaseForm g s l α)).printIdx
            (emcdParentSide g s l α d))) :=
      ⟨j, hj.symm.trans hroute⟩
    obtain ⟨γ, hXf⟩ := emcd_noncentral_edge_grouped τ g s l hl
      (emcdBaseForm g s l α) hXmem' hXc' hXe
    apply (hkindSmall (D.form t)).2
    refine ⟨emcdBaseForm g s l α, γ, X, hXmem', hXc', hXf, ?_⟩
    change (emcdTemplateChild g s l t).form = Sum.inl γ
    exact hXf
  have hspecialSmall : ∀ o : D.SideOcc, D.special o →
      D.kind (D.form o.1) = .small := by
    intro o ho
    exact ho.1
  have hspecialDef : ∀ o : D.SideOcc, D.special o ↔
      D.kind (D.form o.1) = .small ∧
        (if hp : ∃ i : D.Side o.1,
            ∃ d : Fin (D.Q.disk (D.owner o.1)).n, D.marked (D.owner o.1) d ∧
              D.partner (D.printOcc (D.owner o.1) d) = D.occ o.1 i
          then o.2 = hp.choose
          else if hc : ∃ i : D.Side o.1,
            D.IsInner (D.occ o.1 i) ∧
              (D.partner (D.occ o.1 i)).1 = D.central (D.owner o.1)
          then o.2 = hc.choose
          else False) := by
    intro o
    rfl
  have hsmallContact : ∀ t, D.kind (D.form t) = .small →
      ∃ i, D.IsInner (D.occ t i) ∧
        (D.partner (D.occ t i)).1 = D.central (D.owner t) := by
    intro t ht
    obtain ⟨β, γ, Y, hY, hYc, hYf, hcat⟩ := (hkindSmall (D.form t)).1 ht
    let X := emcdTemplateChild g s l t
    have hXmem : X ∈ (s.setup.retained l
        (emcdBaseForm g s l (D.owner t))).children.tiles := by
      rcases t with ⟨α, Z⟩
      exact Z.2
    have hXf : X.form = Sum.inl γ := by
      change (emcdCatalogueTile g s l (D.form t)).form = Sum.inl γ
      exact hcat
    have hXc : X ≠ s.setup.central l (emcdBaseForm g s l (D.owner t)) := by
      intro hxc
      have hcf := congrArg PlacedTile.form hxc
      rw [s.setup.central_form] at hcf
      have hgamma : γ = s.setup.c^[l] (emcdBaseForm g s l (D.owner t)) :=
        Sum.inl_injective (hXf.symm.trans hcf)
      obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
      rw [Function.iterate_succ_apply'] at hgamma
      exact s.noncentral_not_large (m + 1) β hl Y hY hYc _
        (hYf.trans (congrArg Sum.inl hgamma))
    rcases s.setup.others l (emcdBaseForm g s l (D.owner t)) X hXmem hXc with
      horig | hshare
    · obtain ⟨p, hp⟩ := horig
      rw [hXf] at hp
      contradiction
    · obtain ⟨_, e, ⟨i, hi⟩, ⟨j, hj⟩⟩ := hshare
      obtain ⟨ii, hii⟩ := emcd_prints_grouped_side g s l X γ hXf
        (show emcdIsRetainedForm g s l X.form by
          change emcdIsRetainedForm g s l (emcdTemplateChild g s l t).form
          exact (D.form t).2) i
      let oi : D.SideOcc := D.occ t ii
      obtain ⟨k, _, hk⟩ := hcentralOcc (D.owner t) j
      let oc : D.SideOcc := D.occ (D.central (D.owner t)) k
      have hside : D.occSide oc = D.occSide oi := by
        exact hk.trans (hj.trans (hi.symm.trans hii.symm))
      have hne : oc.1 ≠ oi.1 := by
        intro heq
        apply hXc
        have hchild := congrArg (emcdTemplateChild g s l) heq
        simpa [oi, oc] using hchild.symm.trans (hcentralChild (D.owner t))
      have hc := emcd_prints_other_is_partner τ h g s l hl routing oi oc
        (by simpa [oi, oc] using hcentralOwner (D.owner t)) hne hside
      exact ⟨ii, hc.1, congrArg Sigma.fst hc.2 ▸ rfl⟩
  have hprintPartnerContact : ∀ α d, D.marked α d →
      D.IsInner (D.partner (D.printOcc α d)) ∧
        (D.partner (D.partner (D.printOcc α d))).1 = D.central α := by
    intro α d hd
    have hp := (hprintData α d hd).2
    have hc := emcd_prints_other_is_partner τ h g s l hl routing
      (D.partner (D.printOcc α d)) (D.printOcc α d)
      (by exact (hcentralOwner α).trans hp.2.1.symm) hp.1.symm hp.2.2.symm
    exact ⟨hc.1, (congrArg Sigma.fst hc.2).symm⟩
  refine ⟨hprintRoute, ?_, ?_, hprintInner, hprintSmall, hspecialSmall, ?_, ?_, ?_⟩
  · intro α d d' hd hd' heq
    have ha := hmarked α d hd
    have ha' := hmarked α d' hd'
    have hroute : (routing (emcdBaseForm g s l α)).printIdx
        (emcdParentSide g s l α d) =
        (routing (emcdBaseForm g s l α)).printIdx
          (emcdParentSide g s l α d') := by
      apply Fin.ext
      rw [← hprintVal α d, ← hprintVal α d']
      exact congrArg Fin.val heq
    have hp := (routing (emcdBaseForm g s l α)).print_injOn ha ha' hroute
    exact hp
  · intro α a b e ha hb he hcyc
    have hr := (routing (emcdBaseForm g s l α)).print_cyclic
      (emcdParentSide g s l α a) (hmarked α a ha)
      (emcdParentSide g s l α b) (hmarked α b hb)
      (emcdParentSide g s l α e) (hmarked α e he) hcyc
    unfold CycLt3 at hr ⊢
    simpa only [hprintVal α a, hprintVal α b, hprintVal α e] using hr
  · intro t ht
    have hc : ∃ i : D.Side t, D.IsInner (D.occ t i) ∧
        (D.partner (D.occ t i)).1 = D.central (D.owner t) := hsmallContact t ht
    by_cases hp : ∃ i : D.Side t,
        ∃ d : Fin (D.Q.disk (D.owner t)).n, D.marked (D.owner t) d ∧
          D.partner (D.printOcc (D.owner t) d) = D.occ t i
    · refine ⟨hp.choose, ?_, ?_⟩
      · change D.special (D.occ t hp.choose)
        rw [hspecialDef]
        exact ⟨ht, by simp only [dif_pos hp]⟩
      · intro y hy
        change D.special (D.occ t y) at hy
        rw [hspecialDef] at hy
        simpa only [dif_pos hp] using hy.2
    · refine ⟨hc.choose, ?_, ?_⟩
      · change D.special (D.occ t hc.choose)
        rw [hspecialDef]
        exact ⟨ht, by simp only [dif_neg hp, dif_pos hc]⟩
      · intro y hy
        change D.special (D.occ t y) at hy
        rw [hspecialDef] at hy
        simpa only [dif_neg hp, dif_pos hc] using hy.2
  · rintro ⟨t, i⟩ ho
    rw [hspecialDef] at ho
    change D.kind (D.form t) = .small ∧
      (if hp : ∃ j : D.Side t,
          ∃ d : Fin (D.Q.disk (D.owner t)).n, D.marked (D.owner t) d ∧
            D.partner (D.printOcc (D.owner t) d) = D.occ t j
        then i = hp.choose
        else if hc : ∃ j : D.Side t, D.IsInner (D.occ t j) ∧
            (D.partner (D.occ t j)).1 = D.central (D.owner t)
          then i = hc.choose
          else False) at ho
    by_cases hp : ∃ j : D.Side t,
        ∃ d : Fin (D.Q.disk (D.owner t)).n, D.marked (D.owner t) d ∧
          D.partner (D.printOcc (D.owner t) d) = D.occ t j
    · have hi : i = hp.choose := by simpa only [dif_pos hp] using ho.2
      obtain ⟨d, hd, heq⟩ := hp.choose_spec
      subst i
      change D.IsInner (D.occ t hp.choose) ∧
        (D.partner (D.occ t hp.choose)).1 = D.central (D.owner t)
      rw [← heq]
      exact hprintPartnerContact (D.owner t) d hd
    · have hc : ∃ j : D.Side t, D.IsInner (D.occ t j) ∧
          (D.partner (D.occ t j)).1 = D.central (D.owner t) := by
        by_contra hn
        simpa only [dif_neg hp, dif_neg hn] using ho.2
      have hi : i = hc.choose := by simpa only [dif_neg hp, dif_pos hc] using ho.2
      subst i
      exact hc.choose_spec
  · intro α d hd
    let o := D.partner (D.printOcc α d)
    have hps := (hprintData α d hd).2
    have hown : D.owner o.1 = α := hps.2.1.trans (hcentralOwner α)
    have hsmall : D.kind (D.form o.1) = .small := hprintSmall α d hd
    rw [hspecialDef]
    refine ⟨hsmall, ?_⟩
    let d0 : Fin (D.Q.disk (D.owner o.1)).n := hown.symm ▸ d
    have hd0 : D.marked (D.owner o.1) d0 :=
      emcd_marked_transport D hown.symm d hd
    have hpo : D.printOcc α d = D.printOcc (D.owner o.1) d0 :=
      emcd_print_occ_transport D hown.symm d
    have hoPartner : D.partner (D.printOcc (D.owner o.1) d0) = o := by
      rw [← hpo]
    have hp : ∃ i : D.Side o.1,
        ∃ e : Fin (D.Q.disk (D.owner o.1)).n, D.marked (D.owner o.1) e ∧
          D.partner (D.printOcc (D.owner o.1) e) = D.occ o.1 i := by
      exact ⟨o.2, d0, hd0, by simpa [o] using hoPartner⟩
    rw [dif_pos hp]
    obtain ⟨d', hd', heq'⟩ := hp.choose_spec
    have hXmem : emcdTemplateChild g s l o.1 ∈
        (s.setup.retained l (emcdBaseForm g s l (D.owner o.1))).children.tiles := by
      rcases o.1 with ⟨β, X⟩
      exact X.2
    have hXc : emcdTemplateChild g s l o.1 ≠
        s.setup.central l (emcdBaseForm g s l (D.owner o.1)) := by
      intro heq
      have hot : o.1 = D.central (D.owner o.1) :=
        htype o.1 (D.central (D.owner o.1)) rfl (heq.trans (hcentralChild _).symm)
      apply hps.1
      calc
        o.1 = D.central (D.owner o.1) := hot
        _ = D.central α := congrArg D.central hown
        _ = (D.printOcc α d).1 := rfl
    obtain ⟨j, hj⟩ := emcd_outer_step2_child_side τ h g s l hl routing o.1 o.2
    have hps0 := (hprintData (D.owner o.1) d0 hd0).2
    have hroute0 : D.occSide o =
        (s.setup.central l (emcdBaseForm g s l (D.owner o.1))).side
          ((routing (emcdBaseForm g s l (D.owner o.1))).printIdx
            (emcdParentSide g s l (D.owner o.1) d0)) := by
      exact (congrArg D.occSide hoPartner).symm.trans
        (hps0.2.2.trans (hprintRoute (D.owner o.1) d0))
    have hedge : HasEdge (emcdTemplateChild g s l o.1)
        ((s.setup.central l (emcdBaseForm g s l (D.owner o.1))).side
          ((routing (emcdBaseForm g s l (D.owner o.1))).printIdx
            (emcdParentSide g s l (D.owner o.1) d0))) :=
      ⟨j, hj.symm.trans hroute0⟩
    obtain ⟨j', hj'⟩ := emcd_outer_step2_child_side τ h g s l hl routing o.1 hp.choose
    have hps' := (hprintData (D.owner o.1) d' hd').2
    have hedge' : HasEdge (emcdTemplateChild g s l o.1)
        ((s.setup.central l (emcdBaseForm g s l (D.owner o.1))).side
          ((routing (emcdBaseForm g s l (D.owner o.1))).printIdx
            (emcdParentSide g s l (D.owner o.1) d'))) := by
      refine ⟨j', ?_⟩
      exact hj'.symm.trans ((congrArg D.occSide heq').symm.trans
        (hps'.2.2.trans (hprintRoute (D.owner o.1) d')))
    have hdd := hpartner_inj (emcdBaseForm g s l (D.owner o.1))
      (emcdParentSide g s l (D.owner o.1) d0)
      (hmarked _ _ hd0)
      (emcdParentSide g s l (D.owner o.1) d') (hmarked _ _ hd')
      (emcdTemplateChild g s l o.1) hXmem hXc hedge hedge'
    have hdeq : d0 = d' := hdd
    have hocc : D.occ o.1 o.2 = D.occ o.1 hp.choose := by
      have hoOcc : D.occ o.1 o.2 = D.partner (D.printOcc (D.owner o.1) d0) := by
        simpa [o] using hoPartner.symm
      exact hoOcc.trans
        ((congrArg D.partner (congrArg (D.printOcc (D.owner o.1)) hdeq)).trans heq')
    apply Fin.ext
    exact congrArg (fun z : D.SideOcc => z.2.val) hocc

private lemma
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step1_from_routing_aux1
    (G : GroupedFamily P) (α : G.P'.Form) (p : P.Form)
    (hsingle : (G.dissect α).tiles = {⟨p, 0⟩}) :
    Set.range (G.P'.disk α).side = Set.range (P.disk p).side := by
  classical
  have hforward : ∀ i, ∃ j, (G.P'.disk α).side i = (P.disk p).side j := by
    intro i
    obtain ⟨A, hA, j, hj⟩ := G.side_whole α i
    have hAeq : A = (⟨p, 0⟩ : PlacedTile P) := by
      rw [hsingle] at hA
      simpa using hA
    subst A
    exact ⟨j, by simpa [PlacedTile.side] using hj.symm⟩
  choose f hf using hforward
  have hfinj : Function.Injective f := by
    intro i j hij
    apply
      existsMacroCertificate_seed2_routing_step1_setup_sub2_templates_step3_side_injective
    rw [hf i, hf j, hij]
  have hvertices : ∀ i, ∃ j, (G.P'.disk α).vertex j = (P.disk p).vertex i := by
    intro i
    apply G.vertex_retained α
    · refine ⟨⟨p, 0⟩, ?_, ?_⟩
      · rw [hsingle]
        simp
      · exact ⟨i, by simp [PlacedTile.vertex]⟩
    · rw [← G.support_eq α, hsingle, emcg_support_singleton_zero]
      rw [(P.disk p).frontier_eq]
      exact Set.mem_iUnion.2 ⟨i, left_mem_segment ℝ _ _⟩
  choose v hv using hvertices
  have hvinj : Function.Injective v := by
    intro i j hij
    apply (P.disk p).vertex_injective
    rw [← hv i, ← hv j, hij]
  have hcard : (G.P'.disk α).n = (P.disk p).n := by
    apply Nat.le_antisymm
    · simpa using Fintype.card_le_of_injective f hfinj
    · simpa using Fintype.card_le_of_injective v hvinj
  have hfsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).2
      ⟨hfinj, by simp [hcard]⟩).2
  ext e
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨f i, (hf i).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, rfl⟩ := hfsurj j
    exact ⟨i, hf i⟩

/-- Step 1 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: from_routing -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step1_from_routing
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d (i : Fin 4), D.marked α d →
      @List.destutter (Set Pt) (· ≠ ·) (Classical.decRel _)
        ((D.path α d i.castSucc).map D.occSide) =
        (routing (emcdBaseForm g s l α)).pathSides (emcdParentSide g s l α d) i) := by
  classical
  intro D α d i hd
  have hgen : D.IsGenuinePath α d i.castSucc := ⟨hd, by simp⟩
  have hidx : (⟨i.castSucc.val, hgen.2⟩ : Fin 4) = i := Fin.ext rfl
  have hzip : ∀ xs : List (Set Pt), 2 ≤ xs.length → xs.IsChain (· ≠ ·) →
      ((xs.zip xs.tail).flatMap fun p => [p.1, p.2]).destutter (· ≠ ·) = xs := by
    intro xs hlen hchain
    induction xs with
    | nil => contradiction
    | cons x xs ih =>
      cases xs with
      | nil => contradiction
      | cons y ys =>
        cases ys with
        | nil =>
          change List.destutter (· ≠ ·) [x, y] = [x, y]
          have hxy : x ≠ y := by
            cases hchain with
            | cons_cons h _ => exact h
          rw [List.destutter_cons_cons, if_pos hxy]
          rfl
        | cons z zs =>
          have hxy : x ≠ y := by
            cases hchain with
            | cons_cons h _ => exact h
          have hrest : 2 ≤ (y :: z :: zs).length := by simp
          have hrest_chain : (y :: z :: zs).IsChain (· ≠ ·) := by
            cases hchain with
            | cons_cons _ h => exact h
          have ih_res := ih hrest hrest_chain
          change List.destutter (· ≠ ·)
            (x :: y :: y :: z ::
              ((z :: zs).zip zs).flatMap fun p => [p.1, p.2]) = _
          rw [List.destutter_cons_cons, if_pos hxy]
          have hd1 :
              List.destutter' (· ≠ ·) y
                (y :: z :: ((z :: zs).zip zs).flatMap fun p => [p.1, p.2]) =
              List.destutter' (· ≠ ·) y
                (z :: ((z :: zs).zip zs).flatMap fun p => [p.1, p.2]) := by
            have heq :
                List.destutter' (· ≠ ·) y
                    (y :: z :: ((z :: zs).zip zs).flatMap fun p => [p.1, p.2]) =
                  if y ≠ y then
                    y :: List.destutter' (· ≠ ·) y
                      (z :: ((z :: zs).zip zs).flatMap fun p => [p.1, p.2])
                  else List.destutter' (· ≠ ·) y
                    (z :: ((z :: zs).zip zs).flatMap fun p => [p.1, p.2]) := rfl
            rw [heq, if_neg (not_not.mpr rfl)]
          rw [hd1]
          change List.destutter (· ≠ ·)
            (y :: z :: ((z :: zs).zip zs).flatMap fun p => [p.1, p.2]) =
              y :: z :: zs at ih_res
          have hyz : y ≠ z := by
            cases hrest_chain with
            | cons_cons h _ => exact h
          rw [List.destutter_cons_cons, if_pos hyz] at ih_res
          have hd2 :
              List.destutter' (· ≠ ·) z
                (((z :: zs).zip zs).flatMap fun p => [p.1, p.2]) = z :: zs := by
            injection ih_res
          have hd3 :
              List.destutter' (· ≠ ·) y
                  (z :: ((z :: zs).zip zs).flatMap fun p => [p.1, p.2]) =
                y :: List.destutter' (· ≠ ·) z
                  (((z :: zs).zip zs).flatMap fun p => [p.1, p.2]) := by
            have heq :
                List.destutter' (· ≠ ·) y
                    (z :: ((z :: zs).zip zs).flatMap fun p => [p.1, p.2]) =
                  if y ≠ z then
                    y :: List.destutter' (· ≠ ·) z
                      (((z :: zs).zip zs).flatMap fun p => [p.1, p.2])
                  else List.destutter' (· ≠ ·) y
                    (((z :: zs).zip zs).flatMap fun p => [p.1, p.2]) := rfl
            rw [heq, if_pos hyz]
          rw [hd3, hd2]
  let β := emcdBaseForm g s l α
  let par := emcdParentSide g s l α d
  let xs := (routing β).pathSides par i
  have htiles_len : ((routing β).pathTiles par i).length + 1 = xs.length :=
    (routing β).path_length par (by assumption) i
  have hlen : 2 ≤ xs.length := by
    by_contra hnot
    have hlt : xs.length < 2 := not_le.mp hnot
    have htiles_lt : ((routing β).pathTiles par i).length + 1 < 2 := by omega
    have htiles_zero : ((routing β).pathTiles par i).length = 0 := by omega
    have hxs_one : xs.length = 1 := by omega
    have hhead := (routing β).path_head par (by assumption) i
    have hlast := (routing β).path_last par (by assumption) i
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hxs_one
    change xs.head? = some ((routing β).port par i.castSucc) at hhead
    change xs.getLast? =
      some ((s.setup.central l β).side ((routing β).printIdx par)) at hlast
    rw [hx] at hhead hlast
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
    have heq := hhead.symm.trans hlast
    have houter := (routing β).port_outer par i.castSucc
    have hinner := (routing β).print_inner par (by assumption)
    rw [heq] at houter
    obtain ⟨A, hA, B, hB, hAB, ⟨j, hj⟩, ⟨k, hk⟩⟩ := hinner
    let q := A.vertex j + (1 / 2 : ℝ) • (A.vertex (finRotate _ j) - A.vertex j)
    have hqopen : q ∈ openSegment ℝ (A.vertex j) (A.vertex (finRotate _ j)) := by
      have hqline : q = AffineMap.lineMap (A.vertex j)
          (A.vertex (finRotate _ j)) (1 / 2 : ℝ) := by
        simp only [q, AffineMap.lineMap_apply_module']
        module
      rw [hqline]
      exact lineMap_mem_openSegment (𝕜 := ℝ) _ _ (by norm_num)
    obtain ⟨r, hr, σ, _, hsides⟩ :=
      two_sides (s.setup.retained l β).children.disjoint hA hB hAB j k
        (hk.trans hj.symm) hqopen
    have hqint : q ∈ interior (support (s.setup.retained l β).children.tiles) := by
      rw [mem_interior_iff_mem_nhds]
      apply Filter.mem_of_superset (Metric.ball_mem_nhds q hr)
      intro z hz
      by_cases hside : 0 ≤ σ * jcr
          (A.vertex (finRotate _ j) - A.vertex j) (z - A.vertex j)
      · exact carrier_subset_support hA ((hsides z hz).2.2 hside)
      · exact carrier_subset_support hB
          (interior_subset ((hsides z hz).2.1 (lt_of_not_ge hside)))
    have hqint_region : q ∈ interior (s.setup.retained l β).region := by
      rw [← (s.setup.retained l β).support_eq]
      exact hqint
    have hqedge : q ∈ (s.setup.central l β).side ((routing β).printIdx par) := by
      rw [← hj, tile_side_eq]
      exact openSegment_subset_segment ℝ _ _ hqopen
    exact Set.disjoint_left.1 disjoint_interior_frontier hqint_region (houter.1.2 hqedge)
  have hchain : xs.IsChain (· ≠ ·) := by
    have hnonempty : xs ≠ [] := by
      intro hempty
      rw [hempty] at hlen
      contradiction
    have happend : xs = xs.dropLast ++ [xs.getLast hnonempty] :=
      (List.dropLast_append_getLast hnonempty).symm
    have hnodup : xs.dropLast.Nodup :=
      (routing β).path_nodup par (by assumption) i
    have hdrop_chain : xs.dropLast.IsChain (· ≠ ·) := by
      apply List.Pairwise.isChain
      exact List.Nodup.pairwise_of_forall_ne hnodup (fun _ _ _ _ hne => hne)
    have happend_chain :
        (xs.dropLast ++ [xs.getLast hnonempty]).IsChain (· ≠ ·) := by
      apply List.IsChain.append hdrop_chain (List.isChain_singleton _)
      intro x hx y hy
      have hdrop_nonempty : xs.dropLast ≠ [] := by
        intro hempty
        have hdrop_zero : xs.dropLast.length = 0 := by rw [hempty]; rfl
        rw [List.length_dropLast] at hdrop_zero
        omega
      obtain ⟨hlast, hxlast⟩ := List.mem_getLast?_eq_getLast hx
      have hxmem : x ∈ xs.dropLast := hxlast ▸ List.getLast_mem hlast
      have hyeq : y = xs.getLast hnonempty := by
        change y ∈ [xs.getLast hnonempty].head? at hy
        simp at hy
        exact hy.symm
      subst y
      have hnot_central : ¬ HasEdge (s.setup.central l β) x :=
        (routing β).path_central par (by assumption) i x hxmem
      have hcentral : HasEdge (s.setup.central l β) (xs.getLast hnonempty) := by
        have hroute_last := (routing β).path_last par (by assumption) i
        have hlast_get : xs.getLast? = some (xs.getLast hnonempty) :=
          List.getLast?_eq_getLast_of_ne_nil hnonempty
        rw [hlast_get] at hroute_last
        injection hroute_last with heq
        rw [heq]
        exact ⟨(routing β).printIdx par, rfl⟩
      intro heq
      apply hnot_central
      rw [heq]
      exact hcentral
    rw [← happend] at happend_chain
    exact happend_chain
  have hcalc : (D.path α d i.castSucc).map D.occSide =
      (xs.zip xs.tail).flatMap fun p => [p.1, p.2] := by
    have hpath : D.path α d i.castSucc =
        if hi : D.IsGenuinePath α d i.castSucc then
          emcdLiftPath D (emcdTemplateChild g s l) α
            ((routing (emcdBaseForm g s l α)).pathTiles
              (emcdParentSide g s l α d) ⟨i.castSucc.val, hi.2⟩)
            ((routing (emcdBaseForm g s l α)).pathSides
              (emcdParentSide g s l α d) ⟨i.castSucc.val, hi.2⟩)
        else (D.port α d i.castSucc).toList := rfl
    rw [hpath, dif_pos hgen]
    simp only [hidx]
    have hmap :
        (emcdLiftPath D (emcdTemplateChild g s l) α
          ((routing β).pathTiles par i) xs).map D.occSide =
        (((routing β).pathTiles par i).zip
          (xs.zip xs.tail)).flatMap fun entry =>
            (emcdLiftOccurrence D (emcdTemplateChild g s l) α entry.1
                entry.2.1).map D.occSide ++
              (emcdLiftOccurrence D (emcdTemplateChild g s l) α entry.1
                entry.2.2).map D.occSide := by
      rw [emcdLiftPath, List.map_flatMap]
      congr
      ext entry
      rw [List.map_append]
    rw [hmap]
    have hocc : ∀ entry : PlacedTile s.setup.GS.G.mixed × Set Pt × Set Pt,
        entry ∈ ((routing β).pathTiles par i).zip (xs.zip xs.tail) →
          (emcdLiftOccurrence D (emcdTemplateChild g s l) α entry.1
              entry.2.1).map D.occSide ++
            (emcdLiftOccurrence D (emcdTemplateChild g s l) α entry.1
              entry.2.2).map D.occSide = [entry.2.1, entry.2.2] := by
      intro entry hentry
      rcases entry with ⟨⟨form, a⟩, e1, e2⟩
      let entry : PlacedTile s.setup.GS.G.mixed × Set Pt × Set Pt :=
        (⟨form, a⟩, e1, e2)
      obtain ⟨k, hk⟩ : ∃ k : ℕ,
          (((routing β).pathTiles par i).zip (xs.zip xs.tail))[k]? =
            some (⟨form, a⟩, e1, e2) :=
        List.mem_iff_getElem?.mp hentry
      have hkzip := List.getElem?_zip_eq_some.mp hk
      have hktile : ((routing β).pathTiles par i)[k]? = some entry.1 := hkzip.1
      have hksides : (xs.zip xs.tail)[k]? = some entry.2 := hkzip.2
      have hksidezip := List.getElem?_zip_eq_some.mp hksides
      have hkside1 : xs[k]? = some entry.2.1 := hksidezip.1
      have hkside2 : xs.tail[k]? = some entry.2.2 := hksidezip.2
      have hkside2' : xs[k + 1]? = some entry.2.2 := by simpa using hkside2
      have hstep := (routing β).path_step par (by assumption) i k entry.1
        entry.2.1 entry.2.2 hktile hkside1 hkside2'
      have hmem := hstep.1
      have hedge1 := hstep.2.1
      have hedge2 := hstep.2.2
      let t : D.Typ := ⟨α, ⟨entry.1, hmem⟩⟩
      have hoccurrence : ∀ e, HasEdge entry.1 e →
          ∃ j : D.Side t, D.occSide ⟨t, j⟩ = e := by
        intro e hedge
        obtain ⟨j, hj⟩ := hedge
        rcases form with γ | p
        · exact ⟨j, hj⟩
        · have hrange :
              Set.range
                  (s.setup.GS.G.P'.disk
                    (s.setup_grouped.symm ▸ g.original p)).side =
                Set.range (P.disk p).side := by
            have key : ∀ (GS : GroupedSubstitution τ) (heq : GS = g.GS),
                Set.range (GS.G.P'.disk (heq.symm ▸ g.original p)).side =
                  Set.range (P.disk p).side := by
              intro GS heq
              subst heq
              exact
                existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step1_from_routing_aux1
                  g.GS.G (g.original p) p (g.original_dissect p)
            exact key _ s.setup_grouped
          have hjmem : (P.disk p).side j ∈
              Set.range
                (s.setup.GS.G.P'.disk
                  (s.setup_grouped.symm ▸ g.original p)).side := by
            rw [hrange]
            exact ⟨j, rfl⟩
          obtain ⟨k, hk⟩ := hjmem
          refine ⟨k, ?_⟩
          change a +ᵥ
              (s.setup.GS.G.P'.disk
                (s.setup_grouped.symm ▸ g.original p)).side k = e
          rw [hk]
          exact hj
      have hlift : ∀ e, HasEdge entry.1 e →
          (emcdLiftOccurrence D (emcdTemplateChild g s l) α entry.1
            e).map D.occSide = [e] := by
        intro e hedge
        unfold emcdLiftOccurrence
        obtain ⟨j, hj⟩ := hoccurrence e hedge
        have hex : ∃ o : D.SideOcc,
            D.owner o.1 = α ∧ emcdTemplateChild g s l o.1 = entry.1 ∧
              D.occSide o = e := by
          refine ⟨⟨t, j⟩, rfl, rfl, ?_⟩
          exact hj
        rw [dif_pos hex]
        simp
        exact hex.choose_spec.2.2
      rw [hlift entry.2.1 hedge1, hlift entry.2.2 hedge2]
      rfl
    have hlen_zip : ((routing β).pathTiles par i).length =
        (xs.zip xs.tail).length := by
      simp only [List.length_zip, List.length_tail]
      omega
    have hsnd :
        (((routing β).pathTiles par i).zip (xs.zip xs.tail)).map Prod.snd =
          xs.zip xs.tail := List.map_snd_zip hlen_zip.ge
    calc
      _ = (((routing β).pathTiles par i).zip (xs.zip xs.tail)).flatMap
          (fun entry => [entry.2.1, entry.2.2]) := List.flatMap_congr hocc
      _ = ((((routing β).pathTiles par i).zip
          (xs.zip xs.tail)).map Prod.snd).flatMap (fun p => [p.1, p.2]) := by
            rw [List.flatMap_map]
      _ = _ := by rw [hsnd]
  change @List.destutter (Set Pt) (· ≠ ·) (Classical.decRel _) _ = xs
  rw [hcalc]
  have hdec :
      @List.destutter (Set Pt) (· ≠ ·) (Classical.decRel _)
        ((xs.zip xs.tail).flatMap fun p => [p.1, p.2]) =
      List.destutter (· ≠ ·) ((xs.zip xs.tail).flatMap fun p => [p.1, p.2]) := by
    congr
  rw [hdec]
  exact hzip xs hlen hchain

private lemma emcd_paths_step3_getLast_flatMap
    {A B : Type} (f : A → List B) (xs : List A) (a : A)
    (hxs : xs.getLast? = some a) (ha : f a ≠ []) :
    (xs.flatMap f).getLast? = (f a).getLast? := by
  induction xs with
  | nil => simp at hxs
  | cons b bs ih =>
      cases bs with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hxs
          subst a
          simp
      | cons c cs =>
          have htail : (c :: cs).getLast? = some a := by
            simpa only [List.getLast?_cons_cons] using hxs
          have hflat_ne : ((c :: cs).flatMap f) ≠ [] := by
            intro hempty
            have heq := ih htail
            rw [hempty] at heq
            cases hfa : f a with
            | nil => exact ha hfa
            | cons z zs =>
                have hsome : (z :: zs).getLast? ≠ none := by
                  cases zs <;> simp
                rw [hfa] at heq
                exact hsome heq.symm
          rw [List.flatMap_cons, List.getLast?_append_of_ne_nil _ hflat_ne]
          exact ih htail

private lemma emcd_paths_step3_occ_eq_of_type_eq
    (D : MacroData P) (o o' : D.SideOcc) (ht : o.1 = o'.1)
    (hs : D.occSide o = D.occSide o') : o = o' := by
  cases o with
  | mk t i =>
      cases o' with
      | mk t' i' =>
          simp only at ht
          subst t'
          have hii : i = i' := by
            apply emcd_outer_step2_side_injective
            apply Set.Subset.antisymm
            · apply (Set.vadd_set_subset_vadd_set_iff (a := D.anchor t)).1
              exact hs.subset
            · apply (Set.vadd_set_subset_vadd_set_iff (a := D.anchor t)).1
              exact hs.symm.subset
          subst i'
          rfl

private lemma emcd_paths_step3_other_is_partner
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ o o' : D.SideOcc, D.IsInner o → D.owner o'.1 = D.owner o.1 → o'.1 ≠ o.1 →
      D.occSide o' = D.occSide o → o' = D.partner o := by
  intro D o o' hinner howner hne hside
  classical
  have hspec :=
    (existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces
      τ h g s l hl routing).1 o hinner
  have hp_ne : (D.partner o).1 ≠ o.1 := hspec.1
  have hp_owner : D.owner (D.partner o).1 = D.owner o.1 := hspec.2.1
  have hp_side : D.occSide (D.partner o) = D.occSide o := hspec.2.2
  have htype : ∀ t u : D.Typ, D.owner t = D.owner u →
      emcdTemplateChild g s l t = emcdTemplateChild g s l u → t = u := by
    rintro ⟨α, X⟩ ⟨β, Y⟩ hab hXY
    change α = β at hab
    subst β
    change X.1 = Y.1 at hXY
    have : X = Y := Subtype.ext hXY
    subst Y
    rfl
  let T := s.setup.retained l (emcdBaseForm g s l (D.owner o.1))
  have hmem : ∀ t : D.Typ,
      emcdTemplateChild g s l t ∈
        (s.setup.retained l (emcdBaseForm g s l (D.owner t))).children.tiles := by
    rintro ⟨α, X⟩
    exact X.2
  have hom : emcdTemplateChild g s l o.1 ∈ T.children.tiles := hmem o.1
  have hpm : emcdTemplateChild g s l (D.partner o).1 ∈ T.children.tiles := by
    have hm := hmem (D.partner o).1
    rw [hp_owner] at hm
    exact hm
  have ho'm : emcdTemplateChild g s l o'.1 ∈ T.children.tiles := by
    have hm := hmem o'.1
    rw [howner] at hm
    exact hm
  obtain ⟨io, hio⟩ := emcd_outer_step2_child_side τ h g s l hl routing o.1 o.2
  obtain ⟨ip, hip⟩ :=
    emcd_outer_step2_child_side τ h g s l hl routing (D.partner o).1 (D.partner o).2
  obtain ⟨io', hio'⟩ := emcd_outer_step2_child_side τ h g s l hl routing o'.1 o'.2
  have hop_ne : emcdTemplateChild g s l o.1 ≠ emcdTemplateChild g s l (D.partner o).1 := by
    intro heq
    exact hp_ne (htype o.1 (D.partner o).1 hp_owner.symm heq).symm
  have hoo'_ne : emcdTemplateChild g s l o.1 ≠ emcdTemplateChild g s l o'.1 := by
    intro heq
    exact hne (htype o'.1 o.1 howner heq.symm)
  have hchildren : emcdTemplateChild g s l (D.partner o).1 =
      emcdTemplateChild g s l o'.1 := by
    apply side_partner_unique T.children.disjoint hom hpm ho'm hop_ne hoo'_ne io ip io'
    · exact hip.symm.trans (hp_side.trans hio)
    · exact hio'.symm.trans (hside.trans hio)
  have htypes : o'.1 = (D.partner o).1 :=
    htype o'.1 (D.partner o).1 (howner.trans hp_owner.symm) hchildren.symm
  apply emcd_paths_step3_occ_eq_of_type_eq D o' (D.partner o) htypes
  exact hside.trans hp_side.symm

private lemma emcd_paths_step3_lift_occurrence
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ (α : D.Q.Form) (X : PlacedTile s.setup.GS.G.mixed),
      X ∈ (s.setup.retained l (emcdBaseForm g s l α)).children.tiles →
      ∀ e, HasEdge X e → ∃ o : D.SideOcc,
        emcdLiftOccurrence D (emcdTemplateChild g s l) α X e = [o] ∧
          D.owner o.1 = α ∧ emcdTemplateChild g s l o.1 = X ∧ D.occSide o = e := by
  classical
  intro D α X hX e hedge
  let t : D.Typ := ⟨α, ⟨X, hX⟩⟩
  have hoccurrence : ∃ j : D.Side t, D.occSide ⟨t, j⟩ = e := by
    obtain ⟨j, hj⟩ := hedge
    rcases X with ⟨form, a⟩
    cases form with
    | inl γ => exact ⟨j, hj⟩
    | inr p =>
        have hrange :
            Set.range
                (s.setup.GS.G.P'.disk
                  (s.setup_grouped.symm ▸ g.original p)).side =
              Set.range (P.disk p).side := by
          have key : ∀ (GS : GroupedSubstitution τ) (heq : GS = g.GS),
              Set.range (GS.G.P'.disk (heq.symm ▸ g.original p)).side =
                Set.range (P.disk p).side := by
            intro GS heq
            subst heq
            exact existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step1_from_routing_aux1
              g.GS.G (g.original p) p (g.original_dissect p)
          exact key _ s.setup_grouped
        have hjmem : (P.disk p).side j ∈
            Set.range
              (s.setup.GS.G.P'.disk
                (s.setup_grouped.symm ▸ g.original p)).side := by
          rw [hrange]
          exact ⟨j, rfl⟩
        obtain ⟨k, hk⟩ := hjmem
        refine ⟨k, ?_⟩
        change a +ᵥ
            (s.setup.GS.G.P'.disk
              (s.setup_grouped.symm ▸ g.original p)).side k = e
        rw [hk]
        exact hj
  obtain ⟨j, hj⟩ := hoccurrence
  have hex : ∃ o : D.SideOcc,
      D.owner o.1 = α ∧ emcdTemplateChild g s l o.1 = X ∧ D.occSide o = e := by
    exact ⟨⟨t, j⟩, rfl, rfl, hj⟩
  unfold emcdLiftOccurrence
  rw [dif_pos hex]
  exact ⟨hex.choose, rfl, hex.choose_spec⟩

set_option maxHeartbeats 4000000 in
/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: last -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step3_last
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d i, D.IsGenuinePath α d i →
      (D.path α d i).getLast? = some (D.partner (D.printOcc α d))) := by
  classical
  intro D α d i hi
  let β := emcdBaseForm g s l α
  let a := emcdParentSide g s l α d
  let j : Fin 4 := ⟨i.val, hi.2⟩
  let tiles := (routing β).pathTiles a j
  let sides := (routing β).pathSides a j
  have ha : a ∈ s.setup.markedSides β := hi.1
  have hlen : tiles.length + 1 = sides.length := (routing β).path_length a ha j
  have hlast : sides.getLast? =
      some ((s.setup.central l β).side ((routing β).printIdx a)) :=
    (routing β).path_last a ha j
  have htiles_ne : tiles ≠ [] := by
    intro hnil
    have hsides_one : sides.length = 1 := by simp [tiles, hnil] at hlen ⊢; omega
    obtain ⟨e, hsides⟩ := List.length_eq_one_iff.mp hsides_one
    have hhead := (routing β).path_head a ha j
    have houter := (routing β).port_outer a j.castSucc
    have hinner := (routing β).print_inner a ha
    change sides.head? = some ((routing β).port a j.castSucc) at hhead
    rw [hsides] at hhead hlast
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
    have heq := hhead.symm.trans hlast
    rw [heq] at houter
    obtain ⟨A, hA, B, hB, hAB, ⟨k, hk⟩, ⟨m, hm⟩⟩ := hinner
    let q := A.vertex k + (1 / 2 : ℝ) • (A.vertex (finRotate _ k) - A.vertex k)
    have hqopen : q ∈ openSegment ℝ (A.vertex k) (A.vertex (finRotate _ k)) := by
      have hqline : q = AffineMap.lineMap (A.vertex k)
          (A.vertex (finRotate _ k)) (1 / 2 : ℝ) := by
        simp only [q, AffineMap.lineMap_apply_module']
        module
      rw [hqline]
      exact lineMap_mem_openSegment (𝕜 := ℝ) _ _ (by norm_num)
    obtain ⟨r, hr, σ, _, hlocal⟩ :=
      two_sides (s.setup.retained l β).children.disjoint hA hB hAB k m
        (hm.trans hk.symm) hqopen
    have hqint : q ∈ interior (support (s.setup.retained l β).children.tiles) := by
      rw [mem_interior_iff_mem_nhds]
      apply Filter.mem_of_superset (Metric.ball_mem_nhds q hr)
      intro z hz
      by_cases hside : 0 ≤ σ * jcr
          (A.vertex (finRotate _ k) - A.vertex k) (z - A.vertex k)
      · exact carrier_subset_support hA ((hlocal z hz).2.2 hside)
      · exact carrier_subset_support hB
          (interior_subset ((hlocal z hz).2.1 (lt_of_not_ge hside)))
    have hqint_region : q ∈ interior (s.setup.retained l β).region := by
      rw [← (s.setup.retained l β).support_eq]
      exact hqint
    have hqedge : q ∈ (s.setup.central l β).side ((routing β).printIdx a) := by
      rw [← hk, tile_side_eq]
      exact openSegment_subset_segment ℝ _ _ hqopen
    exact Set.disjoint_left.1 disjoint_interior_frontier hqint_region (houter.1.2 hqedge)
  let X := tiles.getLast htiles_ne
  have hXlast : tiles.getLast? = some X := List.getLast?_eq_getLast_of_ne_nil htiles_ne
  have hk : tiles.length - 1 < tiles.length := by
    have : 0 < tiles.length := List.length_pos_of_ne_nil htiles_ne
    omega
  have hind : tiles.length - 1 + 1 = tiles.length := by
    have : 0 < tiles.length := List.length_pos_of_ne_nil htiles_ne
    omega
  have hXidx : tiles[tiles.length - 1]? = some X := by
    rw [← hXlast, List.getLast?_eq_getElem?]
  have hlast' := hlast
  rw [List.getLast?_eq_getElem?] at hlast'
  have hidx : sides.length - 1 = tiles.length := by omega
  have hfinal : sides[tiles.length]? =
      some ((s.setup.central l β).side ((routing β).printIdx a)) := by
    simpa [hidx] using hlast'
  let eprev := sides[tiles.length - 1]'(by omega)
  let eprint := (s.setup.central l β).side ((routing β).printIdx a)
  have hprev : sides[tiles.length - 1]? = some eprev := List.getElem?_eq_getElem _
  have hentry : (tiles.zip (sides.zip sides.tail)).getLast? =
      some (X, (eprev, eprint)) := by
    have hpairs_len : (tiles.zip (sides.zip sides.tail)).length = tiles.length := by
      simp only [List.length_zip, List.length_tail]
      omega
    rw [List.getLast?_eq_getElem?, hpairs_len]
    refine (List.getElem?_zip_eq_some).2 ⟨?_, ?_⟩
    · simpa using hXidx
    · refine (List.getElem?_zip_eq_some).2 ⟨?_, ?_⟩
      · simpa using hprev
      · rw [List.getElem?_tail, hind]
        simpa [eprint] using hfinal
  have hfinal_step : sides[(tiles.length - 1) + 1]? = some eprint := by
    rw [hind]
    simpa [eprint] using hfinal
  have hstep := (routing β).path_step a ha j (tiles.length - 1) X eprev eprint
    hXidx hprev hfinal_step
  obtain ⟨o, ho_lift, ho_owner, ho_child, ho_side⟩ :=
    emcd_paths_step3_lift_occurrence τ h g s l hl routing α X hstep.1 eprint hstep.2.2
  have hX_ne : X ≠ s.setup.central l β := (routing β).path_last_tile a ha j X hXlast
  have ho_ne : o.1 ≠ (D.printOcc α d).1 := by
    intro heq
    apply hX_ne
    rw [← ho_child, heq]
    rfl
  obtain ⟨hprint, -, -, hprint_inner, -⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub6_prints_and_special
      τ h g s l hl routing (fun γ => (routing γ).print_partner_injOn)
  have ho_partner : o = D.partner (D.printOcc α d) := by
    apply emcd_paths_step3_other_is_partner τ h g s l hl routing
    · exact hprint_inner α d hi.1
    · exact ho_owner
    · exact ho_ne
    · exact ho_side.trans (hprint α d).symm
  have hchunk :
      (emcdLiftOccurrence D (emcdTemplateChild g s l) α X eprev ++
        emcdLiftOccurrence D (emcdTemplateChild g s l) α X eprint) ≠ [] := by
    rw [ho_lift]
    simp
  have hflat := emcd_paths_step3_getLast_flatMap
    (fun entry =>
      emcdLiftOccurrence D (emcdTemplateChild g s l) α entry.1 entry.2.1 ++
        emcdLiftOccurrence D (emcdTemplateChild g s l) α entry.1 entry.2.2)
    (tiles.zip (sides.zip sides.tail)) (X, (eprev, eprint)) hentry hchunk
  change (if hgen : D.IsGenuinePath α d i then
      emcdLiftPath D (emcdTemplateChild g s l) α
        ((routing β).pathTiles a ⟨i.val, hgen.2⟩)
        ((routing β).pathSides a ⟨i.val, hgen.2⟩)
    else (D.port α d i).toList).getLast? = _
  rw [dif_pos hi]
  change (emcdLiftPath D (emcdTemplateChild g s l) α tiles sides).getLast? = _
  unfold emcdLiftPath
  rw [hflat]
  change (emcdLiftOccurrence D (emcdTemplateChild g s l) α X eprev ++
    emcdLiftOccurrence D (emcdTemplateChild g s l) α X eprint).getLast? = _
  rw [ho_lift, List.getLast?_append_of_ne_nil _ (by simp)]
  simpa [ho_partner]


set_option maxHeartbeats 800000 in
private lemma emcd_paths_step4_occ_eq_of_type_eq
    (D : MacroData P) (o o' : D.SideOcc) (ht : o.1 = o'.1)
    (hs : D.occSide o = D.occSide o') : o = o' := by
  cases o with
  | mk t i =>
      cases o' with
      | mk t' i' =>
          simp only at ht
          subst t'
          have hii : i = i' := by
            apply emcd_outer_step2_side_injective
            apply Set.Subset.antisymm
            · apply (Set.vadd_set_subset_vadd_set_iff (a := D.anchor t)).1
              exact hs.subset
            · apply (Set.vadd_set_subset_vadd_set_iff (a := D.anchor t)).1
              exact hs.symm.subset
          subst i'
          rfl

set_option maxHeartbeats 800000 in
private lemma emcd_paths_step4_other_is_partner
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ o o' : D.SideOcc, D.owner o'.1 = D.owner o.1 → o'.1 ≠ o.1 →
      D.occSide o' = D.occSide o → D.IsInner o ∧ o' = D.partner o := by
  intro D o o' howner hne hside
  have hinner : D.IsInner o := by
    intro hout
    have hout' : D.IsOuter o' := by
      simpa only [MacroData.IsOuter, howner, hside] using hout
    have heq := emcd_outer_step2_occ_injective τ h g s l hl routing
      howner.symm hout hout' hside.symm
    exact hne (congrArg Sigma.fst heq).symm
  refine ⟨hinner, ?_⟩
  let B := emcdGeometryData τ h g s l hl routing
  have hex : ∃ z : B.SideOcc, z.1 ≠ o.1 ∧ B.owner z.1 = B.owner o.1 ∧
      B.occSide z = B.occSide o := ⟨o', hne, howner, hside⟩
  have hpartner_eq : D.partner o = hex.choose := by
    change emcdGeometricPartner B o = hex.choose
    unfold emcdGeometricPartner
    rw [dif_pos hex]
  have hp_ne : (D.partner o).1 ≠ o.1 := by
    rw [hpartner_eq]
    exact hex.choose_spec.1
  have hp_owner : D.owner (D.partner o).1 = D.owner o.1 := by
    rw [hpartner_eq]
    exact hex.choose_spec.2.1
  have hp_side : D.occSide (D.partner o) = D.occSide o := by
    rw [hpartner_eq]
    exact hex.choose_spec.2.2
  have htype : ∀ t u : D.Typ, D.owner t = D.owner u →
      emcdTemplateChild g s l t = emcdTemplateChild g s l u → t = u := by
    rintro ⟨α, X⟩ ⟨β, Y⟩ hab hXY
    change α = β at hab
    subst β
    change X.1 = Y.1 at hXY
    have : X = Y := Subtype.ext hXY
    subst Y
    rfl
  let T := s.setup.retained l (emcdBaseForm g s l (D.owner o.1))
  have hmem : ∀ t : D.Typ,
      emcdTemplateChild g s l t ∈
        (s.setup.retained l (emcdBaseForm g s l (D.owner t))).children.tiles := by
    rintro ⟨α, X⟩
    exact X.2
  have hom : emcdTemplateChild g s l o.1 ∈ T.children.tiles := hmem o.1
  have hpm : emcdTemplateChild g s l (D.partner o).1 ∈ T.children.tiles := by
    have hm := hmem (D.partner o).1
    rw [hp_owner] at hm
    exact hm
  have ho'm : emcdTemplateChild g s l o'.1 ∈ T.children.tiles := by
    have hm := hmem o'.1
    rw [howner] at hm
    exact hm
  obtain ⟨io, hio⟩ := emcd_outer_step2_child_side τ h g s l hl routing o.1 o.2
  obtain ⟨ip, hip⟩ :=
    emcd_outer_step2_child_side τ h g s l hl routing (D.partner o).1 (D.partner o).2
  obtain ⟨io', hio'⟩ := emcd_outer_step2_child_side τ h g s l hl routing o'.1 o'.2
  have hop_ne : emcdTemplateChild g s l o.1 ≠ emcdTemplateChild g s l (D.partner o).1 := by
    intro heq
    exact hp_ne (htype o.1 (D.partner o).1 hp_owner.symm heq).symm
  have hoo'_ne : emcdTemplateChild g s l o.1 ≠ emcdTemplateChild g s l o'.1 := by
    intro heq
    exact hne (htype o'.1 o.1 howner heq.symm)
  have hchildren : emcdTemplateChild g s l (D.partner o).1 =
      emcdTemplateChild g s l o'.1 := by
    apply side_partner_unique T.children.disjoint hom hpm ho'm hop_ne hoo'_ne io ip io'
    · exact hip.symm.trans (hp_side.trans hio)
    · exact hio'.symm.trans (hside.trans hio)
  have htypes : o'.1 = (D.partner o).1 :=
    htype o'.1 (D.partner o).1 (howner.trans hp_owner.symm) hchildren.symm
  apply emcd_paths_step4_occ_eq_of_type_eq D o' (D.partner o) htypes
  exact hside.trans hp_side.symm

private lemma emcd_paths_step4_flatMap_chain
    {ι κ : Type} {R : κ → κ → Prop} {S : ι → ι → Prop}
    (F : ι → List κ) (xs : List ι) (hxs : xs.IsChain S)
    (hchunk : ∀ x ∈ xs, ∃ a b, F x = [a, b] ∧ R a b)
    (hcross : ∀ x ∈ xs, ∀ y ∈ xs, S x y →
      ∀ a b c d, F x = [a, b] → F y = [c, d] → R b c) :
    (xs.flatMap F).IsChain R := by
  induction xs with
  | nil => exact List.isChain_nil
  | cons x xs ih =>
      cases xs with
      | nil =>
          obtain ⟨a, b, hab, hr⟩ := hchunk x (by simp)
          simp only [List.flatMap_cons, hab, List.flatMap_nil, List.append_nil]
          exact List.isChain_pair.2 hr
      | cons y ys =>
          cases hxs with
          | cons_cons hxy htail =>
              obtain ⟨a, b, hab, hr⟩ := hchunk x (by simp)
              have hrest : ((y :: ys).flatMap F).IsChain R := by
                apply ih htail
                · intro z hz
                  exact hchunk z (by simp only [List.mem_cons] at hz ⊢; exact Or.inr hz)
                · intro z hz w hw hzw c d e f hcd hef
                  exact hcross z (by simp only [List.mem_cons] at hz ⊢; exact Or.inr hz)
                    w (by simp only [List.mem_cons] at hw ⊢; exact Or.inr hw) hzw c d e f hcd hef
              obtain ⟨c, d, hcd, -⟩ := hchunk y (by simp)
              have hbc : R b c := hcross x (by simp) y (by simp) hxy a b c d hab hcd
              simp only [List.flatMap_cons, hab, List.cons_append, List.nil_append]
              rw [List.isChain_cons_cons]
              refine ⟨hr, ?_⟩
              simp only [List.flatMap_cons] at hrest
              rw [hcd] at hrest
              simp only [List.cons_append, List.nil_append] at hrest
              rw [hcd]
              simp only [List.cons_append, List.nil_append]
              rw [List.isChain_cons_cons]
              exact ⟨hbc, hrest⟩

set_option maxHeartbeats 800000 in
private lemma emcd_paths_step4_lift_occurrence
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ (α : D.Q.Form) (X : PlacedTile s.setup.GS.G.mixed),
      X ∈ (s.setup.retained l (emcdBaseForm g s l α)).children.tiles →
      ∀ e, HasEdge X e → ∃ o : D.SideOcc,
        emcdLiftOccurrence D (emcdTemplateChild g s l) α X e = [o] ∧
          D.owner o.1 = α ∧ emcdTemplateChild g s l o.1 = X ∧ D.occSide o = e := by
  classical
  intro D α X hX e hedge
  let t : D.Typ := ⟨α, ⟨X, hX⟩⟩
  have hoccurrence : ∃ j : D.Side t, D.occSide ⟨t, j⟩ = e := by
    obtain ⟨j, hj⟩ := hedge
    rcases X with ⟨form, a⟩
    cases form with
    | inl γ => exact ⟨j, hj⟩
    | inr p =>
        have hrange :
            Set.range
                (s.setup.GS.G.P'.disk
                  (s.setup_grouped.symm ▸ g.original p)).side =
              Set.range (P.disk p).side := by
          have key : ∀ (GS : GroupedSubstitution τ) (heq : GS = g.GS),
              Set.range (GS.G.P'.disk (heq.symm ▸ g.original p)).side =
                Set.range (P.disk p).side := by
            intro GS heq
            subst heq
            exact existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step1_from_routing_aux1
              g.GS.G (g.original p) p (g.original_dissect p)
          exact key _ s.setup_grouped
        have hjmem : (P.disk p).side j ∈
            Set.range
              (s.setup.GS.G.P'.disk
                (s.setup_grouped.symm ▸ g.original p)).side := by
          rw [hrange]
          exact ⟨j, rfl⟩
        obtain ⟨k, hk⟩ := hjmem
        refine ⟨k, ?_⟩
        change a +ᵥ
            (s.setup.GS.G.P'.disk
              (s.setup_grouped.symm ▸ g.original p)).side k = e
        rw [hk]
        exact hj
  obtain ⟨j, hj⟩ := hoccurrence
  have hex : ∃ o : D.SideOcc,
      D.owner o.1 = α ∧ emcdTemplateChild g s l o.1 = X ∧ D.occSide o = e := by
    exact ⟨⟨t, j⟩, rfl, rfl, hj⟩
  unfold emcdLiftOccurrence
  rw [dif_pos hex]
  exact ⟨hex.choose, rfl, hex.choose_spec⟩

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: chain -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step4_chain
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d i (n : ℕ) (o o' : D.SideOcc),
      (D.path α d i)[n]? = some o → (D.path α d i)[n + 1]? = some o' →
        o.1 = o'.1 ∨ (D.IsInner o ∧ o' = D.partner o)) := by
  classical
  intro D α d i n o o' ho ho'
  have hpath : D.path α d i =
      if hi : D.IsGenuinePath α d i then
        emcdLiftPath D (emcdTemplateChild g s l) α
          ((routing (emcdBaseForm g s l α)).pathTiles
            (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
          ((routing (emcdBaseForm g s l α)).pathSides
            (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
      else (D.port α d i).toList := rfl
  by_cases hgen : D.IsGenuinePath α d i
  · let β := emcdBaseForm g s l α
    let a := emcdParentSide g s l α d
    let j : Fin 4 := ⟨i.val, hgen.2⟩
    let tiles := (routing β).pathTiles a j
    let sides := (routing β).pathSides a j
    let entries := tiles.zip (sides.zip sides.tail)
    let F := fun entry : PlacedTile s.setup.GS.G.mixed × Set Pt × Set Pt =>
      emcdLiftOccurrence D (emcdTemplateChild g s l) α entry.1 entry.2.1 ++
        emcdLiftOccurrence D (emcdTemplateChild g s l) α entry.1 entry.2.2
    have ha : a ∈ s.setup.markedSides β := hgen.1
    have hlen : tiles.length + 1 = sides.length := (routing β).path_length a ha j
    have hentries_len : entries.length = tiles.length := by
      simp only [entries, List.length_zip, List.length_tail]
      omega
    have hentry_step : ∀ entry ∈ entries,
        entry.1 ∈ (s.setup.retained l β).children.tiles ∧
          HasEdge entry.1 entry.2.1 ∧ HasEdge entry.1 entry.2.2 := by
      intro entry hentry
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hentry
      rw [List.getElem?_zip_eq_some] at hk
      have hksides := hk.2
      rw [List.getElem?_zip_eq_some] at hksides
      have hnext : sides[k + 1]? = some entry.2.2 := by
        simpa only [List.getElem?_tail] using hksides.2
      exact (routing β).path_step a ha j k entry.1 entry.2.1 entry.2.2
        hk.1 hksides.1 hnext
    have hentries : entries.IsChain
        (fun x y => x.1 ≠ y.1 ∧ x.2.2 = y.2.1) := by
      rw [List.isChain_iff_getElem]
      intro k hk
      have hk0 : entries[k]? = some entries[k] := List.getElem?_eq_getElem (by omega)
      have hk1 : entries[k + 1]? = some entries[k + 1] := List.getElem?_eq_getElem hk
      have hz0 := List.getElem?_zip_eq_some.mp hk0
      have hz1 := List.getElem?_zip_eq_some.mp hk1
      have hs0 := List.getElem?_zip_eq_some.mp hz0.2
      have hs1 := List.getElem?_zip_eq_some.mp hz1.2
      constructor
      · exact (routing β).path_cross a ha j k entries[k].1 entries[k + 1].1 hz0.1 hz1.1
      · have hs0' : sides[k + 1]? = some entries[k].2.2 := by
          simpa only [List.getElem?_tail] using hs0.2
        rw [hs1.1] at hs0'
        exact (Option.some.inj hs0').symm
    have htype : ∀ t u : D.Typ, D.owner t = D.owner u →
        emcdTemplateChild g s l t = emcdTemplateChild g s l u → t = u := by
      rintro ⟨γ, X⟩ ⟨δ, Y⟩ hγδ hXY
      change γ = δ at hγδ
      subst δ
      change X.1 = Y.1 at hXY
      have : X = Y := Subtype.ext hXY
      subst Y
      rfl
    have hchunk : ∀ entry ∈ entries, ∃ u v, F entry = [u, v] ∧
        (u.1 = v.1 ∨ (D.IsInner u ∧ v = D.partner u)) := by
      intro entry hentry
      obtain ⟨hmem, he1, he2⟩ := hentry_step entry hentry
      obtain ⟨u, hu, hu_owner, hu_child, hu_side⟩ :=
        emcd_paths_step4_lift_occurrence τ h g s l hl routing α entry.1 hmem entry.2.1 he1
      obtain ⟨v, hv, hv_owner, hv_child, hv_side⟩ :=
        emcd_paths_step4_lift_occurrence τ h g s l hl routing α entry.1 hmem entry.2.2 he2
      change emcdLiftOccurrence D (emcdTemplateChild g s l) α entry.1 entry.2.1 = [u] at hu
      change emcdLiftOccurrence D (emcdTemplateChild g s l) α entry.1 entry.2.2 = [v] at hv
      refine ⟨u, v, ?_, Or.inl ?_⟩
      · dsimp only [F]
        rw [hu, hv]
        rfl
      · exact htype u.1 v.1 (hu_owner.trans hv_owner.symm) (hu_child.trans hv_child.symm)
    have hcross : ∀ x ∈ entries, ∀ y ∈ entries,
        x.1 ≠ y.1 ∧ x.2.2 = y.2.1 →
        ∀ u v u' v', F x = [u, v] → F y = [u', v'] →
          v.1 = u'.1 ∨ (D.IsInner v ∧ u' = D.partner v) := by
      intro x hx y hy hxy u v u' v' hxpair hypair
      obtain ⟨hxmem, hxe1, hxe2⟩ := hentry_step x hx
      obtain ⟨hymem, hye1, hye2⟩ := hentry_step y hy
      obtain ⟨xu, hxu, -, -, -⟩ :=
        emcd_paths_step4_lift_occurrence τ h g s l hl routing α x.1 hxmem x.2.1 hxe1
      obtain ⟨xv, hxv, hxv_owner, hxv_child, hxv_side⟩ :=
        emcd_paths_step4_lift_occurrence τ h g s l hl routing α x.1 hxmem x.2.2 hxe2
      obtain ⟨yu, hyu, hyu_owner, hyu_child, hyu_side⟩ :=
        emcd_paths_step4_lift_occurrence τ h g s l hl routing α y.1 hymem y.2.1 hye1
      obtain ⟨yv, hyv, -, -, -⟩ :=
        emcd_paths_step4_lift_occurrence τ h g s l hl routing α y.1 hymem y.2.2 hye2
      change emcdLiftOccurrence D (emcdTemplateChild g s l) α x.1 x.2.1 = [xu] at hxu
      change emcdLiftOccurrence D (emcdTemplateChild g s l) α x.1 x.2.2 = [xv] at hxv
      change emcdLiftOccurrence D (emcdTemplateChild g s l) α y.1 y.2.1 = [yu] at hyu
      change emcdLiftOccurrence D (emcdTemplateChild g s l) α y.1 y.2.2 = [yv] at hyv
      have hxpair' : [xu, xv] = [u, v] := by
        dsimp only [F] at hxpair
        rw [hxu, hxv] at hxpair
        exact hxpair
      have hypair' : [yu, yv] = [u', v'] := by
        dsimp only [F] at hypair
        rw [hyu, hyv] at hypair
        exact hypair
      have hv : v = xv := by simpa using (congrArg List.getLast? hxpair').symm
      have hu' : u' = yu := by simpa using (congrArg List.head? hypair').symm
      subst v
      subst u'
      have hne : yu.1 ≠ xv.1 := by
        intro heq
        apply hxy.1
        calc
          x.1 = emcdTemplateChild g s l xv.1 := hxv_child.symm
          _ = emcdTemplateChild g s l yu.1 := congrArg _ heq.symm
          _ = y.1 := hyu_child
      have hside : D.occSide yu = D.occSide xv := by
        exact hyu_side.trans (hxy.2.symm.trans hxv_side.symm)
      exact Or.inr (emcd_paths_step4_other_is_partner τ h g s l hl routing
        xv yu (hyu_owner.trans hxv_owner.symm) hne hside)
    have hchain : (D.path α d i).IsChain
        (fun x y => x.1 = y.1 ∨ (D.IsInner x ∧ y = D.partner x)) := by
      rw [hpath, dif_pos hgen]
      change (entries.flatMap F).IsChain _
      exact emcd_paths_step4_flatMap_chain F entries hentries hchunk hcross
    have hn := List.getElem?_eq_some_iff.mp ho
    have hn' := List.getElem?_eq_some_iff.mp ho'
    have hr := hchain.getElem n hn'.1
    simpa only [hn.2, hn'.2] using hr
  · rw [hpath, dif_neg hgen] at ho'
    have hb := (List.getElem?_eq_some_iff.mp ho').1
    cases hp : D.port α d i <;> simp [hp] at hb

private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step5_owner_aux1
    {α : Type} {l : List α} {i : ℕ} {a : α} (h : l[i]? = some a) : a ∈ l := by
  revert i h
  induction l with
  | nil => intro i h; contradiction
  | cons head tail ih =>
    intro i h
    cases i with
    | zero => 
      injection h with h2
      subst h2
      exact List.Mem.head _
    | succ i =>
      exact List.Mem.tail _ (ih h)

/-- Step 5 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: owner -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step5_owner
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d i (o : D.SideOcc), o ∈ D.path α d i → D.owner o.1 = α) := by
  intro D α d i o ho
  classical
  have hpath : D.path α d i =
      if hi : D.IsGenuinePath α d i then
        emcdLiftPath D (emcdTemplateChild g s l) α
          ((routing (emcdBaseForm g s l α)).pathTiles
            (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
          ((routing (emcdBaseForm g s l α)).pathSides
            (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
      else (D.port α d i).toList := rfl
  rw [hpath] at ho
  split_ifs at ho with hgen
  · unfold emcdLiftPath at ho
    simp only [List.mem_flatMap, List.mem_append] at ho
    rcases ho with ⟨⟨X, ⟨e1, e2⟩⟩, _, ho⟩
    cases ho with
    | inl h1 =>
      unfold emcdLiftOccurrence at h1
      split_ifs at h1 with hex
      · simp only [List.mem_singleton] at h1
        subst o
        exact hex.choose_spec.1
      · simp only [List.not_mem_nil] at h1
    | inr h2 =>
      unfold emcdLiftOccurrence at h2
      split_ifs at h2 with hex
      · simp only [List.mem_singleton] at h2
        subst o
        exact hex.choose_spec.1
      · simp only [List.not_mem_nil] at h2
  · have ho_eq := Option.mem_toList.mp ho
    have H1 := existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step5_owner_aux1 ho_eq
    have h_outer : D.outerList α d =
        emcdGeometricOuterList (emcdGeometryData τ h g s l hl routing) α d := by
      rfl
    rw [h_outer] at H1
    unfold emcdGeometricOuterList at H1
    simp only [List.mem_mergeSort, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and] at H1
    exact H1.1

private lemma emcd_polygonalDisk_side_injective (B : PolygonalDisk) : Function.Injective B.side := by
  intro i j hij
  by_contra hne
  have hab : B.vertex i ≠ B.vertex (finRotate B.n i) := fun heq =>
    emcg_finRotate_ne (by have := B.three_le; omega) i (B.vertex_injective heq).symm
  have hm : midpoint ℝ (B.vertex i) (B.vertex (finRotate B.n i)) ∈ B.side i :=
    midpoint_mem_segment _ _
  have hmj : midpoint ℝ (B.vertex i) (B.vertex (finRotate B.n i)) ∈ B.side j := hij ▸ hm
  rcases (B.simple i j hne ⟨hm, hmj⟩).1 with hmid | hmid
  · exact hab ((midpoint_eq_left_iff ℝ).mp hmid)
  · exact hab ((midpoint_eq_right_iff ℝ).mp hmid)

private lemma emcd_grouped_singleton_side (G : GroupedFamily P) (α : G.P'.Form) (p : P.Form)
    (hsing : (G.dissect α).tiles = {⟨p, 0⟩}) (j : Fin (P.disk p).n) :
    ∃ i : Fin (G.P'.disk α).n, (G.P'.disk α).side i = (P.disk p).side j := by
  classical
  have hedge : ∀ i : Fin (G.P'.disk α).n,
      ∃ k : Fin (P.disk p).n, (P.disk p).side k = (G.P'.disk α).side i := by
    intro i
    obtain ⟨A, hA, k, hk⟩ := G.side_whole α i
    rw [hsing] at hA
    have hAeq : A = (⟨p, 0⟩ : PlacedTile P) := Set.mem_singleton_iff.mp hA
    subst A
    exact ⟨k, by simpa only [PlacedTile.side, zero_vadd] using hk⟩
  choose f hside using hedge
  have hfinj : Function.Injective f := by
    intro i k hik
    apply emcd_polygonalDisk_side_injective
    rw [← hside i, ← hside k, hik]
  have hcard_le : (G.P'.disk α).n ≤ (P.disk p).n := by
    simpa using Fintype.card_le_of_injective f hfinj
  have hcarrier : (G.P'.disk α).carrier = (P.disk p).carrier := by
    rw [← G.support_eq α, hsing]
    simp [support, PlacedTile.carrier]
  have hvertices : (P.disk p).vertexSet ⊆ (G.P'.disk α).vertexSet := by
    rintro v ⟨k, rfl⟩
    apply G.vertex_retained α
    · exact ⟨⟨p, 0⟩, by simp [hsing], by
        simp only [PlacedTile.vertexSet]
        exact ⟨k, by simp [PlacedTile.vertex]⟩⟩
    · rw [hcarrier]
      exact pd_segment_subset_frontier (P.disk p) k (left_mem_segment ℝ _ _)
  have hcard_ge : (P.disk p).n ≤ (G.P'.disk α).n := by
    have hn := Set.ncard_le_ncard hvertices (Set.finite_range (G.P'.disk α).vertex)
    simpa only [PolygonalDisk.vertexSet, Set.ncard_range_of_injective,
      PolygonalDisk.vertex_injective, Nat.card_fin] using hn
  have hcard : Fintype.card (Fin (G.P'.disk α).n) = Fintype.card (Fin (P.disk p).n) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨i, hi⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, hcard⟩).2 j
  exact ⟨i, (hside i).symm.trans (congrArg (P.disk p).side hi)⟩

set_option maxHeartbeats 800000 in
private lemma emcd_path_side_unique
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ o o' : D.SideOcc, D.IsInner o → D.owner o'.1 = D.owner o.1 →
      o'.1 ≠ o.1 → D.occSide o' = D.occSide o → o' = D.partner o := by
  intro D o o' hinner howner hne hside
  classical
  let H := existsMacroCertificate_seed2_routing_step3_data_sub1_macroData τ h g s l hl routing
  have hrule : ∀ α, (D.σ.rule α).tiles =
      (fun t => (⟨emcdChildForm g s l t, emcdAnchor g s l t⟩ :
        PlacedTile (emcdQ g s l))) '' {t | emcdOwner g s l t = α} := by
    intro α
    exact H.choose_spec.2 α
  have hinjective : ∀ t u : D.Typ, D.owner t = D.owner u →
      D.childTile t = D.childTile u → t = u := by
    rintro ⟨α, X⟩ ⟨β, Y⟩ hown htile
    change α = β at hown
    subst β
    have hXY : X.1 = Y.1 := by
      have hform := congrArg (fun A : PlacedTile D.Q => A.form) htile
      have hanchor := congrArg (fun A : PlacedTile D.Q => A.anchor) htile
      change D.form ⟨α, X⟩ = D.form ⟨α, Y⟩ at hform
      change D.anchor ⟨α, X⟩ = D.anchor ⟨α, Y⟩ at hanchor
      change emcdChildForm g s l ⟨α, X⟩ = emcdChildForm g s l ⟨α, Y⟩ at hform
      change emcdAnchor g s l ⟨α, X⟩ = emcdAnchor g s l ⟨α, Y⟩ at hanchor
      have hform := congrArg Subtype.val hform
      change X.1.form = Y.1.form at hform
      change X.1.anchor = Y.1.anchor at hanchor
      apply PlacedTile.ext
      · exact hform
      · exact hanchor
    have : X = Y := Subtype.ext hXY
    subst Y
    rfl
  obtain ⟨hpartner_ne, hpartner_owner, hpartner_side⟩ :=
    (existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step1_interfaces
      τ h g s l hl routing).1 o hinner
  let α := D.owner o.1
  have homem : D.childTile o.1 ∈ (D.σ.rule α).tiles := by
    rw [hrule]
    exact ⟨o.1, rfl, rfl⟩
  have hopmem : D.childTile (D.partner o).1 ∈ (D.σ.rule α).tiles := by
    rw [hrule]
    exact ⟨(D.partner o).1, hpartner_owner, rfl⟩
  have ho'mem : D.childTile o'.1 ∈ (D.σ.rule α).tiles := by
    rw [hrule]
    exact ⟨o'.1, howner, rfl⟩
  have hop_ne : D.childTile o.1 ≠ D.childTile (D.partner o).1 := by
    intro heq
    exact hpartner_ne (hinjective o.1 (D.partner o).1 hpartner_owner.symm heq).symm
  have ho'_ne : D.childTile o.1 ≠ D.childTile o'.1 := by
    intro heq
    exact hne (hinjective o.1 o'.1 howner.symm heq).symm
  have htile := side_partner_unique (D.σ.rule α).disjoint homem hopmem ho'mem
    hop_ne ho'_ne o.2 (D.partner o).2 o'.2 hpartner_side hside
  have htyp : (D.partner o).1 = o'.1 := hinjective _ _
    (hpartner_owner.trans howner.symm) htile
  have hside' : D.occSide o' = D.occSide (D.partner o) :=
    hside.trans hpartner_side.symm
  cases o' with
  | mk t' i' =>
      cases hp : D.partner o with
      | mk p ip =>
          simp only [hp] at htyp hside' ⊢
          subst t'
          have hii : i' = ip := by
            apply emcd_polygonalDisk_side_injective
            have hcancel := congrArg (fun e : Set Pt => (-D.anchor p) +ᵥ e) hside'
            simpa only [MacroData.occSide, MacroData.childTile, PlacedTile.side,
              neg_vadd_vadd] using hcancel
          subst i'
          rfl

set_option maxHeartbeats 800000 in
/-- Step 6 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: partner -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step6_partner
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d i, D.IsGenuinePath α d i →
      ∀ o ∈ D.path α d i, D.IsInner o → ¬ D.IsPrint o → D.partner o ∈ D.path α d i) := by
  intro D α d i hgen o ho hinner hnot_print
  classical
  let β := emcdBaseForm g s l α
  let a := emcdParentSide g s l α d
  let ii : Fin 4 := ⟨i.val, hgen.2⟩
  let tiles := (routing β).pathTiles a ii
  let sides := (routing β).pathSides a ii
  have hi : i = ii.castSucc := Fin.ext rfl
  have hpath : D.path α d i = emcdLiftPath D (emcdTemplateChild g s l) α tiles sides := by
    rw [hi]
    change (if hg : D.IsGenuinePath α d ii.castSucc then
      emcdLiftPath D (emcdTemplateChild g s l) α
        ((routing β).pathTiles a ⟨ii.castSucc.val, hg.2⟩)
        ((routing β).pathSides a ⟨ii.castSucc.val, hg.2⟩)
      else (D.port α d ii.castSucc).toList) = _
    rw [dif_pos]
    · rfl
    · simpa only [ii, Fin.castSucc_mk, β, a] using hgen
  rw [hpath] at ho ⊢
  have lift_spec : ∀ (X : PlacedTile s.setup.GS.G.mixed) (e : Set Pt) (q : D.SideOcc),
      q ∈ emcdLiftOccurrence D (emcdTemplateChild g s l) α X e →
      D.owner q.1 = α ∧ emcdTemplateChild g s l q.1 = X ∧ D.occSide q = e := by
    intro X e q hq
    unfold emcdLiftOccurrence at hq
    split_ifs at hq with hex
    · simp only [List.mem_singleton] at hq
      subst q
      exact hex.choose_spec
    · simp only [List.not_mem_nil] at hq
  have lift_exists : ∀ (X : PlacedTile s.setup.GS.G.mixed) (e : Set Pt),
      (∃ q : D.SideOcc, D.owner q.1 = α ∧ emcdTemplateChild g s l q.1 = X ∧
        D.occSide q = e) →
      ∃ q ∈ emcdLiftOccurrence D (emcdTemplateChild g s l) α X e,
        D.owner q.1 = α ∧ emcdTemplateChild g s l q.1 = X ∧ D.occSide q = e := by
    intro X e hex
    unfold emcdLiftOccurrence
    rw [dif_pos hex]
    exact ⟨hex.choose, by simp, hex.choose_spec⟩
  have lift_of_edge : ∀ (X : PlacedTile s.setup.GS.G.mixed),
      X ∈ (s.setup.retained l β).children.tiles → ∀ e, HasEdge X e →
      ∃ q ∈ emcdLiftOccurrence D (emcdTemplateChild g s l) α X e,
        D.owner q.1 = α ∧ emcdTemplateChild g s l q.1 = X ∧ D.occSide q = e := by
    rintro ⟨γ | p, x⟩ hX e ⟨j, hj⟩
    · apply lift_exists
      let X : PlacedTile s.setup.GS.G.mixed := ⟨Sum.inl γ, x⟩
      let t : D.Typ := ⟨α, ⟨X, hX⟩⟩
      have hn : (D.Q.disk (D.form t)).n = (s.setup.GS.G.P'.disk γ).n := by
        change ((emcdQ g s l).disk (emcdChildForm g s l t)).n = _
        rfl
      let j' : D.Side t := Fin.cast hn.symm j
      have hj' : D.occSide (D.occ t j') = e := by
        change (⟨emcdChildForm g s l t, emcdAnchor g s l t⟩ :
          PlacedTile (emcdQ g s l)).side j' = e
        simpa only [emcdChildForm, emcdAnchor, emcdQ, emcdBaseForm, t, X,
          PlacedTile.side, j', Fin.cast_eq_cast, Fin.val_cast] using hj
      exact ⟨D.occ t j', rfl, rfl, hj'⟩
    · apply lift_exists
      let X : PlacedTile s.setup.GS.G.mixed := ⟨Sum.inr p, x⟩
      let t : D.Typ := ⟨α, ⟨X, hX⟩⟩
      have hsing :
          (s.setup.GS.G.dissect (emcdBaseForm g s l (emcdChildForm g s l t))).tiles =
            {⟨p, 0⟩} := by
        have hbase : emcdBaseForm g s l (emcdChildForm g s l t) =
            emcdBaseForm g s l (emcdOriginalForm g s l p) := by
          rfl
        rw [hbase]
        exact existsMacroCertificate_seed2_routing_step3_data_sub4_representation_step4_original
          g s l p
      obtain ⟨j', hj'⟩ := emcd_grouped_singleton_side s.setup.GS.G
        (emcdBaseForm g s l (emcdChildForm g s l t)) p hsing j
      have hj'' : D.occSide (D.occ t j') = e := by
        change (⟨emcdChildForm g s l t, emcdAnchor g s l t⟩ :
          PlacedTile (emcdQ g s l)).side j' = e
        change x +ᵥ
          (s.setup.GS.G.P'.disk (emcdBaseForm g s l (emcdChildForm g s l t))).side j' = e
        rw [hj']
        exact hj
      exact ⟨D.occ t j', rfl, rfl, hj''⟩
  have partner_of_lifts : ∀ (X Y : PlacedTile s.setup.GS.G.mixed) (e : Set Pt)
      (q q' : D.SideOcc),
      q ∈ emcdLiftOccurrence D (emcdTemplateChild g s l) α X e →
      q' ∈ emcdLiftOccurrence D (emcdTemplateChild g s l) α Y e →
      X ≠ Y → D.IsInner q → q' = D.partner q := by
    intro X Y e q q' hq hq' hXY hqin
    have sq := lift_spec X e q hq
    have sq' := lift_spec Y e q' hq'
    apply emcd_path_side_unique τ h g s l hl routing q q' hqin
    · exact sq'.1.trans sq.1.symm
    · intro heq
      apply hXY
      rw [← sq.2.1, ← sq'.2.1, heq]
    · exact sq'.2.2.trans sq.2.2.symm
  unfold emcdLiftPath at ho ⊢
  simp only [List.mem_flatMap, List.mem_append] at ho ⊢
  obtain ⟨⟨X, e₁, e₂⟩, hentry, ho | ho⟩ := ho
  all_goals
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hentry
    have hk_outer := (List.getElem?_zip_eq_some.mp hk)
    have hk_inner := List.getElem?_zip_eq_some.mp hk_outer.2
    have htile_k : tiles[k]? = some X := hk_outer.1
    have hside_k : sides[k]? = some e₁ := hk_inner.1
    have hside_succ : sides[k + 1]? = some e₂ := by
      simpa only [List.getElem?_tail] using hk_inner.2
    have hstep := (routing β).path_step a hgen.1 ii k X e₁ e₂
      htile_k hside_k hside_succ
    obtain ⟨hXmem, hXe₁, hXe₂⟩ := hstep
  · by_cases hk0 : k = 0
    · subst k
      have hhead := (routing β).path_head a hgen.1 ii
      have he₁ : e₁ = (routing β).port a ii.castSucc := by
        change sides.head? = some ((routing β).port a ii.castSucc) at hhead
        rw [List.head?_eq_getElem?, hside_k] at hhead
        exact Option.some.inj hhead
      have hout := ((routing β).port_outer a ii.castSucc).1.2
      have H := existsMacroCertificate_seed2_routing_step3_data_sub1_macroData τ h g s l hl routing
      have hkpow : s.setup.GS.k = g.k := by rw [s.setup_grouped, g.grouped_power]
      have hboundary : D.macroBoundary α = frontier (s.setup.retained l β).region := by
        unfold MacroData.macroBoundary MacroData.macroRegion
        rw [s.setup.region_eq, show D.σ.θ = τ.θ ^ (g.k * l) from H.choose_spec.1, hkpow]
        rfl
      exact (hinner (by
        unfold MacroData.IsOuter
        rw [(lift_spec X e₁ o ho).1, (lift_spec X e₁ o ho).2.2, he₁, hboundary]
        exact hout)).elim
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      obtain ⟨htile_bound, -⟩ := List.getElem?_eq_some_iff.mp htile_k
      obtain ⟨hside_bound, -⟩ := List.getElem?_eq_some_iff.mp hside_k
      have htprev : k - 1 < tiles.length := by omega
      have hsprev : k - 1 < sides.length := by omega
      let Y := tiles[k - 1]'htprev
      let e₀ := sides[k - 1]'hsprev
      have hY : tiles[k - 1]? = some Y := List.getElem?_eq_getElem htprev
      have he₀ : sides[k - 1]? = some e₀ := List.getElem?_eq_getElem hsprev
      have hnext : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)
      have hprev_step := (routing β).path_step a hgen.1 ii (k - 1) Y e₀ e₁
        hY he₀ (hnext ▸ hside_k)
      obtain ⟨hYmem, -, hYe₁⟩ := hprev_step
      obtain ⟨q, hq, -⟩ := lift_of_edge Y hYmem e₁ hYe₁
      have hXY : X ≠ Y := by
        intro hXY
        have hcross := (routing β).path_cross a hgen.1 ii (k - 1) Y X hY
          (hnext ▸ htile_k)
        exact hcross hXY.symm
      have hqeq := partner_of_lifts X Y e₁ o q ho hq hXY hinner
      rw [← hqeq]
      refine ⟨(Y, (e₀, e₁)), ?_, Or.inr hq⟩
      exact List.mem_iff_getElem?.mpr ⟨k - 1,
        List.getElem?_zip_eq_some.mpr ⟨hY,
          List.getElem?_zip_eq_some.mpr ⟨he₀, by simpa [List.getElem?_tail, hnext] using hside_k⟩⟩⟩
  · by_cases hnext_bound : k + 1 < tiles.length
    · have hsnext : k + 2 < sides.length := by
        have hlength := (routing β).path_length a hgen.1 ii
        change tiles.length + 1 = sides.length at hlength
        omega
      let Y := tiles[k + 1]'hnext_bound
      let e₃ := sides[k + 2]'hsnext
      have hY : tiles[k + 1]? = some Y := List.getElem?_eq_getElem hnext_bound
      have he₃ : sides[k + 2]? = some e₃ := List.getElem?_eq_getElem hsnext
      have hnext_step := (routing β).path_step a hgen.1 ii (k + 1) Y e₂ e₃
        hY hside_succ (by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he₃)
      obtain ⟨hYmem, hYe₂, -⟩ := hnext_step
      obtain ⟨q, hq, -⟩ := lift_of_edge Y hYmem e₂ hYe₂
      have hXY := (routing β).path_cross a hgen.1 ii k X Y htile_k hY
      have hqeq := partner_of_lifts X Y e₂ o q ho hq hXY hinner
      rw [← hqeq]
      refine ⟨(Y, (e₂, e₃)), ?_, Or.inl hq⟩
      exact List.mem_iff_getElem?.mpr ⟨k + 1,
        List.getElem?_zip_eq_some.mpr ⟨hY,
          List.getElem?_zip_eq_some.mpr ⟨hside_succ,
            by simpa only [List.getElem?_tail, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he₃⟩⟩⟩
    · have hlast_index : k + 1 = tiles.length := by
        obtain ⟨htile_bound, -⟩ := List.getElem?_eq_some_iff.mp htile_k
        omega
      have hsides_length := (routing β).path_length a hgen.1 ii
      change tiles.length + 1 = sides.length at hsides_length
      have hlast_side : sides.getLast? = some e₂ := by
        rw [List.getLast?_eq_getElem?]
        convert hside_succ using 2 <;> omega
      have he₂print : e₂ =
          (s.setup.central l β).side ((routing β).printIdx a) := by
        have hp := (routing β).path_last a hgen.1 ii
        rw [hlast_side] at hp
        exact Option.some.inj hp
      have hlast_tile : tiles.getLast? = some X := by
        rw [List.getLast?_eq_getElem?]
        convert htile_k using 2 <;> omega
      have hXcentral := (routing β).path_last_tile a hgen.1 ii X hlast_tile
      obtain ⟨hprint_side, -, -, hprint_inner, -⟩ :=
        existsMacroCertificate_seed2_routing_step3_data_sub6_prints_and_special
          τ h g s l hl routing (fun γ => (routing γ).print_partner_injOn)
      have hp_spec : D.occSide (D.printOcc α d) = e₂ := by
        rw [hprint_side, he₂print]
      have so := lift_spec X e₂ o ho
      have htype_ne : o.1 ≠ (D.printOcc α d).1 := by
        intro heq
        apply hXcentral
        rw [← so.2.1]
        exact congrArg (emcdTemplateChild g s l) heq
      have hoeq : o = D.partner (D.printOcc α d) := by
        apply emcd_path_side_unique τ h g s l hl routing (D.printOcc α d) o
          (hprint_inner α d hgen.1)
        · exact so.1
        · exact htype_ne
        · exact so.2.2.trans hp_spec.symm
      have hprint : D.IsPrint o := by
        rw [MacroData.IsPrint, so.1]
        exact ⟨d, hgen.1, Or.inr hoeq⟩
      exact (hnot_print hprint).elim

/-- Step 7 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: trivial -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step7_trivial
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d i, ¬ D.IsGenuinePath α d i → D.path α d i = (D.port α d i).toList) := by
  dsimp only [emcdMacroData]
  intro α d i hi
  simp only [MacroData.IsGenuinePath] at hi ⊢
  simp only [dif_neg hi]
  rfl

/-- Step 8 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: fifth -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step8_fifth
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d, D.path α d (4 : Fin 5) = (D.port α d (4 : Fin 5)).toList) := by
  classical
  intro D α d
  have h_not_genuine : ¬ D.IsGenuinePath α d (4 : Fin 5) := by
    intro h_genuine
    exact (by decide : ¬ (4 < 4)) h_genuine.2
  change (if hi : D.IsGenuinePath α d (4 : Fin 5) then _ else _) = _
  exact dif_neg h_not_genuine

private lemma emcd_paths_step9_expanded_mem
    {A : Type*} {xs : List A} {x : A}
    (h : x ∈ (xs.zip xs.tail).flatMap fun p => [p.1, p.2]) : x ∈ xs := by
  simp only [List.mem_flatMap] at h
  obtain ⟨p, hp, hx⟩ := h
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
  rw [List.getElem?_zip_eq_some] at hk
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact List.mem_iff_getElem?.2 ⟨k, hk.1⟩
  · rcases hx with rfl | hx
    · exact List.mem_of_mem_tail (List.mem_iff_getElem?.2 ⟨k, hk.2⟩)
    · contradiction

private lemma emcd_paths_step9_expanded_positive_mem_tail
    {A : Type*} (xs : List A) (n : ℕ) (x : A)
    (h : ((xs.zip xs.tail).flatMap fun p => [p.1, p.2])[n + 1]? = some x) :
    x ∈ xs.tail := by
  have htail : x ∈ ((xs.zip xs.tail).flatMap fun p => [p.1, p.2]).tail := by
    rw [List.mem_iff_getElem?]
    exact ⟨n, by simpa only [List.getElem?_tail] using h⟩
  cases xs with
  | nil => simp at h
  | cons a xs =>
      cases xs with
      | nil => simp at h
      | cons b ys =>
          simp only [List.tail_cons]
          change x ∈ b :: (((b :: ys).zip (b :: ys).tail).flatMap fun p => [p.1, p.2]) at htail
          rcases List.mem_cons.mp htail with rfl | hrest
          · exact List.mem_cons_self
          · exact emcd_paths_step9_expanded_mem hrest

/-- Step 9 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: inner -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step9_inner
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d i, D.IsGenuinePath α d i →
      ∀ (n : ℕ) (o : D.SideOcc), (D.path α d i)[n + 1]? = some o → D.IsInner o) := by
  classical
  intro D α d i hgen n o ho
  let β := emcdBaseForm g s l α
  let a := emcdParentSide g s l α d
  let j : Fin 4 := ⟨i.val, hgen.2⟩
  let tiles := (routing β).pathTiles a j
  let sides := (routing β).pathSides a j
  have ha : a ∈ s.setup.markedSides β := hgen.1
  have hpath : D.path α d i =
      emcdLiftPath D (emcdTemplateChild g s l) α tiles sides := by
    have hpath' : D.path α d i =
        if hi : D.IsGenuinePath α d i then
          emcdLiftPath D (emcdTemplateChild g s l) α
            ((routing (emcdBaseForm g s l α)).pathTiles
              (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
            ((routing (emcdBaseForm g s l α)).pathSides
              (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
        else (D.port α d i).toList := rfl
    rw [hpath', dif_pos hgen]
  have hmap : (D.path α d i).map D.occSide =
      (sides.zip sides.tail).flatMap fun p => [p.1, p.2] := by
    rw [hpath]
    unfold emcdLiftPath
    rw [List.map_flatMap]
    have hentry : ∀ entry ∈ tiles.zip (sides.zip sides.tail),
        (emcdLiftOccurrence D (emcdTemplateChild g s l) α entry.1 entry.2.1 ++
          emcdLiftOccurrence D (emcdTemplateChild g s l) α entry.1 entry.2.2).map D.occSide =
            [entry.2.1, entry.2.2] := by
      intro entry he
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
      rw [List.getElem?_zip_eq_some] at hk
      obtain ⟨hktile, hksides⟩ := hk
      rw [List.getElem?_zip_eq_some] at hksides
      have hside2 : sides[k + 1]? = some entry.2.2 := by
        simpa only [List.getElem?_tail] using hksides.2
      obtain ⟨hmem, hedge1, hedge2⟩ :=
        (routing β).path_step a ha j k entry.1 entry.2.1 entry.2.2
          hktile hksides.1 hside2
      obtain ⟨u, hu, -, -, huside⟩ :=
        emcd_paths_step4_lift_occurrence τ h g s l hl routing α entry.1 hmem entry.2.1 hedge1
      obtain ⟨v, hv, -, -, hvside⟩ :=
        emcd_paths_step4_lift_occurrence τ h g s l hl routing α entry.1 hmem entry.2.2 hedge2
      rw [hu, hv]
      change [D.occSide u, D.occSide v] = [entry.2.1, entry.2.2]
      rw [huside, hvside]
    rw [List.flatMap_congr hentry]
    have hlen : tiles.length = (sides.zip sides.tail).length := by
      have := (routing β).path_length a ha j
      change tiles.length + 1 = sides.length at this
      simp only [List.length_zip, List.length_tail]
      omega
    calc
      _ = ((tiles.zip (sides.zip sides.tail)).map Prod.snd).flatMap
          (fun p => [p.1, p.2]) := by rw [List.flatMap_map]
      _ = _ := by rw [List.map_snd_zip hlen.ge]
  have hside_index :
      ((D.path α d i).map D.occSide)[n + 1]? = some (D.occSide o) := by
    simpa only [List.getElem?_map] using congrArg (Option.map D.occSide) ho
  rw [hmap] at hside_index
  have hside_tail : D.occSide o ∈ sides.tail :=
    emcd_paths_step9_expanded_positive_mem_tail sides n (D.occSide o) hside_index
  have htemplate_inner :
      (s.setup.retained l β).IsInner (D.occSide o) :=
    (routing β).path_inner a ha j (D.occSide o) hside_tail
  have homem : o ∈ D.path α d i :=
    List.mem_iff_getElem?.2 ⟨n + 1, ho⟩
  have howner : D.owner o.1 = α :=
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step5_owner
      τ h g s l hl routing α d i o homem
  obtain ⟨A, hA, B, hB, hAB, hAe, hBe⟩ := htemplate_inner
  let X := emcdTemplateChild g s l o.1
  obtain ⟨Y, hY, hYX, hYe⟩ : ∃ Y ∈ (s.setup.retained l β).children.tiles,
      Y ≠ X ∧ HasEdge Y (D.occSide o) := by
    by_cases hXA : X = A
    · exact ⟨B, hB, fun hBX => hAB (hXA.symm.trans hBX.symm), hBe⟩
    · exact ⟨A, hA, fun hAX => hXA hAX.symm, hAe⟩
  obtain ⟨o', -, ho'owner, ho'child, ho'side⟩ :=
    emcd_paths_step4_lift_occurrence τ h g s l hl routing α Y hY (D.occSide o) hYe
  have hne : o'.1 ≠ o.1 := by
    intro heq
    apply hYX
    rw [← ho'child]
    exact congrArg (emcdTemplateChild g s l) heq
  exact (emcd_paths_step4_other_is_partner τ h g s l hl routing o o'
    (ho'owner.trans howner.symm) hne ho'side).1

/-- Step 1 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step10_marked`:
"every side is marked (sides of non-large children)": every side of the form of a non-central child
of a retained template (an annular piece or an original singleton) is marked. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step10_marked_step1_noncentral_univ
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l) (t : emcdTyp g s l)
    (ht : t.2.1 ≠ s.setup.central l (emcdBaseForm g s l t.1)) :
    s.setup.markedSides (emcdBaseForm g s l (emcdChildForm g s l t)) = Finset.univ := by
  rcases hform : t.2.1.form with γ | p
  · have hb : emcdBaseForm g s l (emcdChildForm g s l t) = γ :=
      existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_inl g s l _ γ hform
    rw [hb]
    exact s.marked_child l _ hl t.2.1 t.2.2 ht γ hform
  · have hb : emcdBaseForm g s l (emcdChildForm g s l t) =
        emcdBaseForm g s l (emcdOriginalForm g s l p) := by
      show (match t.2.1.form with
        | Sum.inl γ => γ
        | Sum.inr p => s.setup_grouped.symm ▸ g.original p) = _
      rw [hform]
      rfl
    rw [hb]
    exact s.marked_singleton _ p
      (existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_original g s l p)

/-- Step 2 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step10_marked`:
"no central side occurs before the print": every occurrence on a genuine path lies in a non-central
child of its template (the print is recorded in its small owner only). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step10_marked_step2_not_central
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d i, D.IsGenuinePath α d i → ∀ o ∈ D.path α d i, o.1 ≠ D.central α) := by
  intro D α d i hG o ho
  classical
  have hpath : D.path α d i =
      if hi : D.IsGenuinePath α d i then
        emcdLiftPath D (emcdTemplateChild g s l) α
          ((routing (emcdBaseForm g s l α)).pathTiles
            (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
          ((routing (emcdBaseForm g s l α)).pathSides
            (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
      else (D.port α d i).toList := rfl
  rw [hpath] at ho
  split_ifs at ho
  · unfold emcdLiftPath at ho
    simp only [List.mem_flatMap, List.mem_append] at ho
    rcases ho with ⟨⟨X, ⟨e, e'⟩⟩, hmem, ho⟩
    let β := emcdBaseForm g s l α
    let a := emcdParentSide g s l α d
    let j : Fin 4 := ⟨i.val, hG.2⟩
    have ha : a ∈ s.setup.markedSides β := by
      dsimp only [a, β]
      exact hG.1
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
    rw [List.getElem?_zip_eq_some] at hk
    have hk_sides := hk.2
    rw [List.getElem?_zip_eq_some] at hk_sides
    have hk_tile : ((routing β).pathTiles a j)[k]? = some X := hk.1
    have hk_e : ((routing β).pathSides a j)[k]? = some e := hk_sides.1
    have hk_e' : ((routing β).pathSides a j).tail[k]? = some e' := hk_sides.2
    have hk_e'_orig : ((routing β).pathSides a j)[k + 1]? = some e' := by
      simpa only [List.getElem?_tail] using hk_e'
    have hstep := (routing β).path_step a ha j k X e e' hk_tile hk_e hk_e'_orig
    have hlen := (routing β).path_length a ha j
    have hk_tiles := (List.getElem?_eq_some_iff.mp hk_tile).1
    have hk_drop : k < ((routing β).pathSides a j).dropLast.length := by
      rw [List.length_dropLast]
      omega
    have he_drop : e ∈ ((routing β).pathSides a j).dropLast := by
      rw [List.mem_iff_getElem?]
      refine ⟨k, List.getElem?_eq_some_iff.mpr ⟨hk_drop, ?_⟩⟩
      rw [List.getElem_dropLast]
      exact (List.getElem?_eq_some_iff.mp hk_e).2
    have hXne : X ≠ s.setup.central l β := by
      intro hX
      apply (routing β).path_central a ha j e he_drop
      rw [← hX]
      exact hstep.2.1
    cases ho with
    | inl hocc =>
      unfold emcdLiftOccurrence at hocc
      split_ifs at hocc with hex
      · have hoeq : o = Classical.choose hex := by
          simpa only [List.mem_singleton] using hocc
        have hchild := (Classical.choose_spec hex).2.1
        rw [← hoeq] at hchild
        intro hcentral
        apply hXne
        calc
          X = emcdTemplateChild g s l o.1 := hchild.symm
          _ = emcdTemplateChild g s l (D.central α) := congrArg _ hcentral
          _ = s.setup.central l β := rfl
      · simp only [List.not_mem_nil] at hocc
    | inr hocc =>
      unfold emcdLiftOccurrence at hocc
      split_ifs at hocc with hex
      · have hoeq : o = Classical.choose hex := by
          simpa only [List.mem_singleton] using hocc
        have hchild := (Classical.choose_spec hex).2.1
        rw [← hoeq] at hchild
        intro hcentral
        apply hXne
        calc
          X = emcdTemplateChild g s l o.1 := hchild.symm
          _ = emcdTemplateChild g s l (D.central α) := congrArg _ hcentral
          _ = s.setup.central l β := rfl
      · simp only [List.not_mem_nil] at hocc

/-- Step 10 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: marked -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step10_marked
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d i, D.IsGenuinePath α d i → ∀ o ∈ D.path α d i, D.IsMarked o) := by
  intro D α d i hG o ho
  have hnc := existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step10_marked_step2_not_central
    τ h g s l hl routing α d i hG o ho
  have hown := existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step5_owner
    τ h g s l hl routing α d i o ho
  obtain ⟨⟨β, X, hX⟩, j⟩ := o
  change β = α at hown
  subst hown
  have hXc : X ≠ s.setup.central l (emcdBaseForm g s l β) := by
    rintro rfl
    exact hnc rfl
  have hu := existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step10_marked_step1_noncentral_univ
    g s l hl ⟨β, X, hX⟩ hXc
  show emcdParentSide g s l (emcdChildForm g s l ⟨β, X, hX⟩) j ∈
    s.setup.markedSides (emcdBaseForm g s l (emcdChildForm g s l ⟨β, X, hX⟩))
  rw [hu]
  exact Finset.mem_univ _

/-- Step 11 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: not_central -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step11_not_central
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d i, D.IsGenuinePath α d i → ∀ o ∈ D.path α d i, o.1 ≠ D.central α) := by
  intro D α d i hG o ho
  classical
  have hpath : D.path α d i =
      if hi : D.IsGenuinePath α d i then
        emcdLiftPath D (emcdTemplateChild g s l) α
          ((routing (emcdBaseForm g s l α)).pathTiles
            (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
          ((routing (emcdBaseForm g s l α)).pathSides
            (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
      else (D.port α d i).toList := rfl
  rw [hpath] at ho
  split_ifs at ho
  · unfold emcdLiftPath at ho
    simp only [List.mem_flatMap, List.mem_append] at ho
    rcases ho with ⟨⟨X, ⟨e, e'⟩⟩, hmem, ho⟩
    let β := emcdBaseForm g s l α
    let a := emcdParentSide g s l α d
    let j : Fin 4 := ⟨i.val, hG.2⟩
    have ha : a ∈ s.setup.markedSides β := by
      dsimp only [a, β]
      exact hG.1
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
    rw [List.getElem?_zip_eq_some] at hk
    have hk_sides := hk.2
    rw [List.getElem?_zip_eq_some] at hk_sides
    have hk_tile : ((routing β).pathTiles a j)[k]? = some X := hk.1
    have hk_e : ((routing β).pathSides a j)[k]? = some e := hk_sides.1
    have hk_e' : ((routing β).pathSides a j).tail[k]? = some e' := hk_sides.2
    have hk_e'_orig : ((routing β).pathSides a j)[k + 1]? = some e' := by
      simpa only [List.getElem?_tail] using hk_e'
    have hstep := (routing β).path_step a ha j k X e e' hk_tile hk_e hk_e'_orig
    have hlen := (routing β).path_length a ha j
    have hk_tiles := (List.getElem?_eq_some_iff.mp hk_tile).1
    have hk_drop : k < ((routing β).pathSides a j).dropLast.length := by
      rw [List.length_dropLast]
      omega
    have he_drop : e ∈ ((routing β).pathSides a j).dropLast := by
      rw [List.mem_iff_getElem?]
      refine ⟨k, List.getElem?_eq_some_iff.mpr ⟨hk_drop, ?_⟩⟩
      rw [List.getElem_dropLast]
      exact (List.getElem?_eq_some_iff.mp hk_e).2
    have hXne : X ≠ s.setup.central l β := by
      intro hX
      apply (routing β).path_central a ha j e he_drop
      rw [← hX]
      exact hstep.2.1
    cases ho with
    | inl hocc =>
      unfold emcdLiftOccurrence at hocc
      split_ifs at hocc with hex
      · have hoeq : o = Classical.choose hex := by
          simpa only [List.mem_singleton] using hocc
        have hchild := (Classical.choose_spec hex).2.1
        rw [← hoeq] at hchild
        intro hcentral
        apply hXne
        calc
          X = emcdTemplateChild g s l o.1 := hchild.symm
          _ = emcdTemplateChild g s l (D.central α) := congrArg _ hcentral
          _ = s.setup.central l β := rfl
      · simp only [List.not_mem_nil] at hocc
    | inr hocc =>
      unfold emcdLiftOccurrence at hocc
      split_ifs at hocc with hex
      · have hoeq : o = Classical.choose hex := by
          simpa only [List.mem_singleton] using hocc
        have hchild := (Classical.choose_spec hex).2.1
        rw [← hoeq] at hchild
        intro hcentral
        apply hXne
        calc
          X = emcdTemplateChild g s l o.1 := hchild.symm
          _ = emcdTemplateChild g s l (D.central α) := congrArg _ hcentral
          _ = s.setup.central l β := rfl
      · simp only [List.not_mem_nil] at hocc

/-- Step 12 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: penultimate -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step12_penultimate
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d i, D.IsGenuinePath α d i →
      ∀ o : D.SideOcc, (D.path α d i)[(D.path α d i).length - 2]? = some o →
        o.1 = (D.partner (D.printOcc α d)).1 ∧ D.IsOrdinary o) := by
  sorry

/-- Step 1 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup`:
a lifted occurrence of the side `e` in the crossed child `X` is an occurrence of `e` in `X`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step1_lift_occurrence
    {Q : Protoset} (D : MacroData P) (templateChild : D.Typ → PlacedTile Q) (α : D.Q.Form)
    (X : PlacedTile Q) (e : Set Pt) :
    List.Sublist ((emcdLiftOccurrence D templateChild α X e).map (fun o => (templateChild o.1, D.occSide o)))
      [(X, e)] := by
  unfold emcdLiftOccurrence
  split_ifs with hex
  · obtain ⟨-, h1, h2⟩ := hex.choose_spec
    simp [h1, h2]
  · simp

/-- Step 2 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup`:
the occurrence chain `(X₀,e₀),(X₀,e₁),(X₁,e₁),…` projects (child, side) into the list of pairs
`(X_k, e_k), (X_k, e_{k+1})`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step2_lift_path
    {Q : Protoset} (D : MacroData P) (templateChild : D.Typ → PlacedTile Q) (α : D.Q.Form)
    (tiles : List (PlacedTile Q)) (sides : List (Set Pt)) :
    List.Sublist ((emcdLiftPath D templateChild α tiles sides).map (fun o => (templateChild o.1, D.occSide o)))
      ((tiles.zip (sides.zip sides.tail)).flatMap (fun en => [(en.1, en.2.1), (en.1, en.2.2)])) := by
  unfold emcdLiftPath
  induction (tiles.zip (sides.zip sides.tail)) with
  | nil => simp
  | cons en ens ih =>
    simp only [List.flatMap_cons, List.map_append]
    refine List.Sublist.append ?_ ih
    exact (existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step1_lift_occurrence
      D templateChild α en.1 en.2.1).append
      (existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step1_lift_occurrence
      D templateChild α en.1 en.2.2)

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup`:
in the chain of pairs, the side of an entry is a later side, or the entry is the initial pair `(X₀, e₀)`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step3_mem
    {α β : Type*} (tiles : List α) (sides : List β) (Y : α) (e : β)
    (h : (Y, e) ∈ (tiles.zip (sides.zip sides.tail)).flatMap (fun en => [(en.1, en.2.1), (en.1, en.2.2)])) :
    e ∈ sides.tail ∨ (tiles.head? = some Y ∧ sides.head? = some e) := by
  induction tiles generalizing sides with
  | nil => simp at h
  | cons X Xs ih =>
    match sides, h with
    | [], h => simp at h
    | [x], h => simp at h
    | x :: y :: ys, h =>
      have hL : ((X :: Xs).zip ((x :: y :: ys).zip (x :: y :: ys).tail)).flatMap
          (fun en => [(en.1, en.2.1), (en.1, en.2.2)]) =
          (X, x) :: (X, y) :: (Xs.zip ((y :: ys).zip (y :: ys).tail)).flatMap
            (fun en => [(en.1, en.2.1), (en.1, en.2.2)]) := rfl
      rw [hL] at h
      rcases List.mem_cons.1 h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact Or.inr ⟨rfl, rfl⟩
      rcases List.mem_cons.1 h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact Or.inl (by simp)
      rcases ih (y :: ys) h with h' | ⟨-, h'⟩
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · simp only [List.head?_cons, Option.some.injEq] at h'
        subst h'
        exact Or.inl (by simp)

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup`:
if the routed sides are distinct and consecutive crossed children are distinct, the chain of pairs
`(X_k, e_k), (X_k, e_{k+1})` has no repetition. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step4_pairs_nodup
    {α β : Type*} (tiles : List α) (sides : List β) (hs : sides.Nodup)
    (hc : ∀ (k : ℕ) (X Y : α), tiles[k]? = some X → tiles[k + 1]? = some Y → X ≠ Y) :
    ((tiles.zip (sides.zip sides.tail)).flatMap (fun en => [(en.1, en.2.1), (en.1, en.2.2)])).Nodup := by
  induction tiles generalizing sides with
  | nil => simp
  | cons X Xs ih =>
    match sides, hs with
    | [], _ => simp
    | [x], _ => simp
    | x :: y :: ys, hs =>
      have hL : ((X :: Xs).zip ((x :: y :: ys).zip (x :: y :: ys).tail)).flatMap
          (fun en => [(en.1, en.2.1), (en.1, en.2.2)]) =
          (X, x) :: (X, y) :: (Xs.zip ((y :: ys).zip (y :: ys).tail)).flatMap
            (fun en => [(en.1, en.2.1), (en.1, en.2.2)]) := rfl
      rw [hL]
      have hx : x ∉ y :: ys := (List.nodup_cons.1 hs).1
      have hy : y ∉ ys := (List.nodup_cons.1 (List.nodup_cons.1 hs).2).1
      have hc' : ∀ (k : ℕ) (X Y : α), Xs[k]? = some X → Xs[k + 1]? = some Y → X ≠ Y :=
        fun k X Y h1 h2 => hc (k + 1) X Y (by simpa using h1) (by simpa using h2)
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, ih (y :: ys) (List.nodup_cons.1 hs).2 hc'⟩⟩
      · intro hmem
        rcases List.mem_cons.1 hmem with h | h
        · exact hx (by rw [(Prod.mk.inj h).2]; simp)
        rcases existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step3_mem
          Xs (y :: ys) X x h with h' | ⟨-, h'⟩
        · exact hx (List.mem_cons_of_mem _ h')
        · simp only [List.head?_cons, Option.some.injEq] at h'
          exact hx (by simp [h'])
      · intro hmem
        rcases existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step3_mem
          Xs (y :: ys) X y hmem with h' | ⟨h', -⟩
        · exact hy h'
        · cases Xs with
          | nil => simp at h'
          | cons X' Xs' =>
            simp only [List.head?_cons, Option.some.injEq] at h'
            exact hc 0 X X' rfl (by simp) h'.symm

/-- Step 5 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup`:
the routed side list of a marked side has no repetition: its non-terminal sides are distinct
(`path_nodup`) and none of them is a central side (`path_central`), while the terminal print is. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step5_sides_nodup
    {Q : Protoset} {T : Template Q} {par : PolygonalDisk} {sc : ℝ} {central : PlacedTile Q}
    {marked : Finset (Fin par.n)} {cm : Finset ℕ} (R : RoutingData T par sc central marked cm)
    (a : Fin par.n) (ha : a ∈ marked) (i : Fin 4) : (R.pathSides a i).Nodup := by
  have hlast := R.path_last a ha i
  have hnd := R.path_nodup a ha i
  have hc := R.path_central a ha i
  rw [← List.dropLast_append_getLast? _ hlast]
  refine List.nodup_append.2 ⟨hnd, List.nodup_singleton _, ?_⟩
  intro x hx y hy hxy
  rw [List.mem_singleton] at hy
  rw [hxy, hy] at hx
  exact hc _ hx ⟨_, rfl⟩

/-- Step 6 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup`:
the singleton port paths have no repetition. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step6_port
    {α : Type*} (o : Option α) : o.toList.Nodup := by
  cases o <;> simp

/-- Step 13 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: nodup -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d i, (D.path α d i).Nodup) := by
  classical
  intro D α d i
  have hpath : D.path α d i =
      if hi : D.IsGenuinePath α d i then
        emcdLiftPath D (emcdTemplateChild g s l) α
          ((routing (emcdBaseForm g s l α)).pathTiles
            (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
          ((routing (emcdBaseForm g s l α)).pathSides
            (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
      else (D.port α d i).toList := rfl
  rw [hpath]
  split_ifs with hgen
  · have ha : emcdParentSide g s l α d ∈ s.setup.markedSides (emcdBaseForm g s l α) := hgen.1
    set R := routing (emcdBaseForm g s l α)
    set a := emcdParentSide g s l α d
    set j : Fin 4 := ⟨i.val, hgen.2⟩
    apply List.Nodup.of_map (fun o => (emcdTemplateChild g s l o.1, D.occSide o))
    exact List.Nodup.sublist
      (existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step2_lift_path
        D (emcdTemplateChild g s l) α (R.pathTiles a j) (R.pathSides a j))
      (existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step4_pairs_nodup
        (R.pathTiles a j) (R.pathSides a j)
        (existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step5_sides_nodup R a ha j)
        (fun k X Y h1 h2 => R.path_cross a ha j k X Y h1 h2))
  · exact existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup_step6_port _

/-- Step 1 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"no occurrence repeats" (index arithmetic): in a cycle of at least three listed sides, the side two
steps after `j` is not `j`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step1_finRotate_two
    {n : ℕ} (hn : 3 ≤ n) (j : Fin n) : finRotate n (finRotate n j) ≠ j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_succ_apply, finRotate_succ_apply]
  intro h
  rw [Fin.ext_iff, Fin.val_add, Fin.val_add, Fin.val_one', Nat.add_mod_mod] at h
  have hj := j.isLt
  have h1 : 1 % (m + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1] at h
  by_cases hc : j.val + 1 < m + 1
  · rw [Nat.mod_eq_of_lt hc] at h
    by_cases hc2 : j.val + 1 + 1 < m + 1
    · rw [Nat.mod_eq_of_lt hc2] at h; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h; omega
  · have he : j.val + 1 = m + 1 := by omega
    rw [he, Nat.mod_self, Nat.zero_add, h1] at h; omega

/-- Step 1 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"no occurrence repeats": distinct listed sides of one placed tile are distinct segments (the
listed vertices are injective and there are at least three of them). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step1_side_injective
    {Q : Protoset} (A : PlacedTile Q) (i j : Fin (Q.disk A.form).n) (hij : A.side i = A.side j) :
    i = j := by
  have hinj : Function.Injective A.vertex := fun a b hab => by
    simp only [PlacedTile.vertex, vadd_eq_add, add_right_inj] at hab
    exact (Q.disk A.form).vertex_injective hab
  rw [emcg_side_eq_segment, emcg_side_eq_segment] at hij
  rcases emcg_segment_endpoints hij with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact hinj h1
  · exfalso
    have e1 := hinj h1
    have e2 := hinj h2
    subst e1
    exact existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step1_finRotate_two
      (Q.disk A.form).three_le j e2

/-- Step 2 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"the genuine paths are the occurrence chains of the routed side lists": every occurrence on a
genuine path lies in a crossed child `X_k` of the routed tile list and carries the routed side
`e_k` or `e_{k+1}`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step2_lift_mem
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α d (i : Fin 5) (hi : D.IsGenuinePath α d i) (o : D.SideOcc), o ∈ D.path α d i →
      ∃ (k : ℕ) (X : PlacedTile s.setup.GS.G.mixed),
        ((routing (emcdBaseForm g s l α)).pathTiles (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)[k]? =
          some X ∧
        emcdTemplateChild g s l o.1 = X ∧
        (((routing (emcdBaseForm g s l α)).pathSides (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)[k]? =
            some (D.occSide o) ∨
          ((routing (emcdBaseForm g s l α)).pathSides (emcdParentSide g s l α d)
            ⟨i.val, hi.2⟩)[k + 1]? = some (D.occSide o)) := by
  intro D α d i hi o ho
  classical
  have hpath : D.path α d i =
      if hi : D.IsGenuinePath α d i then
        emcdLiftPath D (emcdTemplateChild g s l) α
          ((routing (emcdBaseForm g s l α)).pathTiles
            (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
          ((routing (emcdBaseForm g s l α)).pathSides
            (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)
      else (D.port α d i).toList := rfl
  rw [hpath, dif_pos hi] at ho
  unfold emcdLiftPath at ho
  simp only [List.mem_flatMap, List.mem_append] at ho
  obtain ⟨⟨X, ⟨e, e'⟩⟩, hmem, ho⟩ := ho
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
  rw [List.getElem?_zip_eq_some] at hk
  obtain ⟨hk_tile, hk_sides⟩ := hk
  rw [List.getElem?_zip_eq_some] at hk_sides
  obtain ⟨hk_e, hk_e'⟩ := hk_sides
  rw [List.getElem?_tail] at hk_e'
  refine ⟨k, X, hk_tile, ?_⟩
  rcases ho with hocc | hocc
  · unfold emcdLiftOccurrence at hocc
    split_ifs at hocc with hex
    · have hoeq : o = Classical.choose hex := by
        simpa only [List.mem_singleton] using hocc
      obtain ⟨-, hchild, hside⟩ := Classical.choose_spec hex
      rw [← hoeq] at hchild hside
      exact ⟨hchild, Or.inl (hk_e.trans (congrArg some hside.symm))⟩
    · simp only [List.not_mem_nil] at hocc
  · unfold emcdLiftOccurrence at hocc
    split_ifs at hocc with hex
    · have hoeq : o = Classical.choose hex := by
        simpa only [List.mem_singleton] using hocc
      obtain ⟨-, hchild, hside⟩ := Classical.choose_spec hex
      rw [← hoeq] at hchild hside
      exact ⟨hchild, Or.inr (hk_e'.trans (congrArg some hside.symm))⟩
    · simp only [List.not_mem_nil] at hocc

/-- Step 3 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"no central side occurs before the print, the side before the print is a side of the small owner":
the side of an occurrence of a genuine path is either a nonterminal routed side, or the print
side of the central child, carried by a non-central crossed child. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step3_cases
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α d (i : Fin 5) (hi : D.IsGenuinePath α d i) (o : D.SideOcc), o ∈ D.path α d i →
      D.occSide o ∈
          ((routing (emcdBaseForm g s l α)).pathSides (emcdParentSide g s l α d) ⟨i.val, hi.2⟩).dropLast ∨
        (D.occSide o = (s.setup.central l (emcdBaseForm g s l α)).side
            ((routing (emcdBaseForm g s l α)).printIdx (emcdParentSide g s l α d)) ∧
          emcdTemplateChild g s l o.1 ≠ s.setup.central l (emcdBaseForm g s l α)) := by
  intro D α d i hi o ho
  obtain ⟨k, X, hk_tile, hchild, hside⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step2_lift_mem
      τ h g s l hl routing α d i hi o ho
  have ha : emcdParentSide g s l α d ∈ s.setup.markedSides (emcdBaseForm g s l α) := hi.1
  have hlen := (routing (emcdBaseForm g s l α)).path_length _ ha ⟨i.val, hi.2⟩
  have hlast := (routing (emcdBaseForm g s l α)).path_last _ ha ⟨i.val, hi.2⟩
  have hlastT := (routing (emcdBaseForm g s l α)).path_last_tile _ ha ⟨i.val, hi.2⟩
  have hk := (List.getElem?_eq_some_iff.mp hk_tile).1
  have hdrop : ∀ (m : ℕ) (e : Set Pt),
      m + 1 < ((routing (emcdBaseForm g s l α)).pathSides (emcdParentSide g s l α d)
        ⟨i.val, hi.2⟩).length →
      ((routing (emcdBaseForm g s l α)).pathSides (emcdParentSide g s l α d) ⟨i.val, hi.2⟩)[m]? =
        some e →
      e ∈ ((routing (emcdBaseForm g s l α)).pathSides (emcdParentSide g s l α d)
        ⟨i.val, hi.2⟩).dropLast := by
    intro m e hm he
    rw [List.mem_iff_getElem?]
    refine ⟨m, ?_⟩
    rw [List.getElem?_dropLast, if_pos (by omega)]
    exact he
  rcases hside with hs | hs
  · exact Or.inl (hdrop k _ (by omega) hs)
  · by_cases hkl : k + 2 < ((routing (emcdBaseForm g s l α)).pathSides (emcdParentSide g s l α d)
        ⟨i.val, hi.2⟩).length
    · exact Or.inl (hdrop (k + 1) _ hkl hs)
    · right
      rw [List.getLast?_eq_getElem?, show ((routing (emcdBaseForm g s l α)).pathSides
        (emcdParentSide g s l α d) ⟨i.val, hi.2⟩).length - 1 = k + 1 by omega, hs] at hlast
      refine ⟨Option.some.inj hlast, ?_⟩
      rw [hchild]
      apply hlastT
      rw [List.getLast?_eq_getElem?, show ((routing (emcdBaseForm g s l α)).pathTiles
        (emcdParentSide g s l α d) ⟨i.val, hi.2⟩).length - 1 = k by omega]
      exact hk_tile

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"the central child has the parent's catalogue disk": every listed side of a grouped mixed child is a
listed side of its relabelled catalogue tile. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step4_grouped_side
    {τ : Substitution P} (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (X : PlacedTile s.setup.GS.G.mixed)
    (γ : s.setup.GS.G.P'.Form) (hX : X.form = Sum.inl γ) (hμ : emcdIsRetainedForm g s l X.form)
    (j : Fin (s.setup.GS.G.mixed.disk X.form).n) :
    ∃ i, (⟨⟨X.form, hμ⟩, X.anchor⟩ : PlacedTile (emcdQ g s l)).side i = X.side j := by
  obtain ⟨f, a⟩ := X
  simp only at hX
  subst hX
  exact ⟨j, rfl⟩

/-- Step 4 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"the print of a marked parent side is the routing's print slot": every listed side of the central
child of the retained template is carried by an occurrence of the central type. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step4_central_occ
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α (j : Fin (s.setup.GS.G.mixed.disk (s.setup.central l (emcdBaseForm g s l α)).form).n),
      ∃ i, D.occSide ⟨D.central α, i⟩ = (s.setup.central l (emcdBaseForm g s l α)).side j := by
  intro D α j
  exact existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step4_grouped_side
    g s l (s.setup.central l (emcdBaseForm g s l α)) _
    (s.setup.central_form l (emcdBaseForm g s l α)) _ j

/-- Step 5 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"an inner side has exactly two owners, because the template is side-to-side and three polygons with
disjoint interiors cannot share a whole segment": two non-central occurrences of the same template
carrying the same side of the central child coincide. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step5_unique
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α (o o' : D.SideOcc), D.owner o.1 = α → D.owner o'.1 = α →
      o.1 ≠ D.central α → o'.1 ≠ D.central α → ∀ i : D.Side (D.central α),
        D.occSide o = D.occSide ⟨D.central α, i⟩ → D.occSide o' = D.occSide ⟨D.central α, i⟩ →
          o = o' := by
  intro D α o o' ho ho' hc hc' i h1 h2
  classical
  have H := existsMacroCertificate_seed2_routing_step3_data_sub1_macroData τ h g s l hl routing
  have hrule : (D.σ.rule α).tiles =
      (fun t => (⟨emcdChildForm g s l t, emcdAnchor g s l t⟩ : PlacedTile (emcdQ g s l))) ''
        {t | emcdOwner g s l t = α} := H.choose_spec.2 α
  have hmem : ∀ t : D.Typ, D.owner t = α → D.childTile t ∈ (D.σ.rule α).tiles := by
    intro t ht
    rw [hrule]
    exact ⟨t, ht, rfl⟩
  have hinj : ∀ t t' : D.Typ, D.owner t = D.owner t' → D.childTile t = D.childTile t' → t = t' := by
    rintro ⟨a, X, hX⟩ ⟨a', X', hX'⟩ hown heq
    change a = a' at hown
    subst hown
    have e1 : X.form = X'.form := congrArg Subtype.val (congrArg PlacedTile.form heq)
    have e2 : X.anchor = X'.anchor := by
      have h' := congrArg PlacedTile.anchor heq
      exact h'
    have e3 : X = X' := by
      cases X
      cases X'
      simp only at e1 e2
      subst e1
      subst e2
      rfl
    subst e3
    rfl
  have hcen : D.owner (D.central α) = α := rfl
  have hAo : D.childTile (D.central α) ≠ D.childTile o.1 := fun e =>
    hc (hinj _ _ (hcen.trans ho.symm) e).symm
  have hAo' : D.childTile (D.central α) ≠ D.childTile o'.1 := fun e =>
    hc' (hinj _ _ (hcen.trans ho'.symm) e).symm
  have hBC := side_partner_unique (D.σ.rule α).disjoint (hmem _ hcen) (hmem _ ho) (hmem _ ho')
    hAo hAo' i o.2 o'.2 h1 h2
  have h11 : o.1 = o'.1 := hinj _ _ (ho.trans ho'.symm) hBC
  obtain ⟨t, k⟩ := o
  obtain ⟨t', k'⟩ := o'
  change t = t' at h11
  subst h11
  have hk : k = k' :=
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step1_side_injective
      (D.childTile t) k k' (h1.trans h2.symm)
  subst hk
  rfl

/-- Step 6 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"the partner of an inner side occurrence is the other occurrence of the same geometric side in the
same template": a non-central occurrence carrying the print side is the partner of the print. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step6_print_partner
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α d (o : D.SideOcc), D.owner o.1 = α →
      emcdTemplateChild g s l o.1 ≠ s.setup.central l (emcdBaseForm g s l α) →
      D.occSide o = (s.setup.central l (emcdBaseForm g s l α)).side
          ((routing (emcdBaseForm g s l α)).printIdx (emcdParentSide g s l α d)) →
        o = D.partner (D.printOcc α d) := by
  intro D α d o hown hX hside
  classical
  obtain ⟨i0, hi0⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step4_central_occ
      τ h g s l hl routing α ((routing (emcdBaseForm g s l α)).printIdx (emcdParentSide g s l α d))
  have hp : ∃ i : D.Side (D.central α), D.occSide ⟨D.central α, i⟩ =
      (s.setup.central l (emcdBaseForm g s l α)).side
        ((routing (emcdBaseForm g s l α)).printIdx (emcdParentSide g s l α d)) := ⟨i0, hi0⟩
  have hprintEq : D.print α d = hp.choose := by
    show (if hp : _ then _ else _) = _
    split
    · rfl
    · rename_i hn
      exact absurd hp hn
  have hprint : D.occSide (D.printOcc α d) = (s.setup.central l (emcdBaseForm g s l α)).side
      ((routing (emcdBaseForm g s l α)).printIdx (emcdParentSide g s l α d)) := by
    show D.occSide ⟨D.central α, D.print α d⟩ = _
    rw [hprintEq]
    exact hp.choose_spec
  have hc : o.1 ≠ D.central α := by
    intro e
    apply hX
    rw [e]
    rfl
  have hex : ∃ o' : D.SideOcc, o'.1 ≠ (D.printOcc α d).1 ∧
      D.owner o'.1 = D.owner (D.printOcc α d).1 ∧ D.occSide o' = D.occSide (D.printOcc α d) :=
    ⟨o, hc, hown, hside.trans hprint.symm⟩
  have hpart : D.partner (D.printOcc α d) = hex.choose := by
    show emcdGeometricPartner (emcdGeometryData τ h g s l hl routing) (D.printOcc α d) = _
    unfold emcdGeometricPartner
    split
    · rfl
    · rename_i hn
      exact absurd hex hn
  obtain ⟨e1, e2, e3⟩ := hex.choose_spec
  rw [hpart]
  exact existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step5_unique
    τ h g s l hl routing α o hex.choose hown e2 hc e1 (D.print α d) (hside.trans hprint.symm) e3

/-- Step 7 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"the lists are without repetition, in the lexicographically positive direction of the supporting line":
two repetition-free lists of nonempty segments with the same members, both ordered by the
`LexPositive` order of their points, coincide. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_list_eq
    (L L' : List (Set Pt)) (hmem : ∀ e, e ∈ L ↔ e ∈ L') (hL : L.Nodup) (hL' : L'.Nodup)
    (hs : L.Pairwise (fun e e' => ∀ x ∈ e, ∀ y ∈ e', x = y ∨ LexPositive (y - x)))
    (hs' : L'.Pairwise (fun e e' => ∀ x ∈ e, ∀ y ∈ e', x = y ∨ LexPositive (y - x)))
    (hne : ∀ e ∈ L, e.Nonempty) : L = L' := by
  refine List.Perm.eq_of_pairwise ?_ hs hs' ((List.perm_ext_iff_of_nodup hL hL').2 hmem)
  intro a b ha hb hab hba
  obtain ⟨x0, hx0⟩ := hne a ha
  obtain ⟨y0, hy0⟩ := hne b ((hmem b).2 hb)
  have key : ∀ x ∈ a, ∀ y ∈ b, x = y := by
    intro x hx y hy
    rcases hab x hx y hy with h1 | h1
    · exact h1
    rcases hba y hy x hx with h2 | h2
    · exact h2.symm
    exfalso
    unfold LexPositive at h1 h2
    simp only [PiLp.sub_apply] at h1 h2
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩ <;> linarith
  ext z
  constructor
  · intro hz
    rw [key z hz y0 hy0]
    exact hy0
  · intro hz
    rw [← key x0 hx0 z hz]
    exact hx0

/-- Step 7 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"every original form is a singleton": a grouped form scattering to the single tile `⟨p, 0⟩` has
exactly the listed sides of the original form `p` (its sides are whole sides of `p`, and they cover
the common boundary). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_singleton_side
    (G : GroupedFamily P) (x : G.P'.Form) (p : P.Form) (hx : (G.dissect x).tiles = {⟨p, 0⟩})
    (e : Set Pt) : (∃ i, (G.P'.disk x).side i = e) ↔ (∃ j, (P.disk p).side j = e) := by
  have hdir : ∀ i, ∃ j, (P.disk p).side j = (G.P'.disk x).side i := by
    intro i
    obtain ⟨A, hA, j, hj⟩ := G.side_whole x i
    rw [hx, Set.mem_singleton_iff] at hA
    subst hA
    refine ⟨j, ?_⟩
    simpa [PlacedTile.side] using hj
  constructor
  · rintro ⟨i, rfl⟩
    exact hdir i
  · rintro ⟨j, rfl⟩
    have hcar :=
      existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_singleton_carrier G x p hx
    have hab : (P.disk p).vertex j ≠ (P.disk p).vertex (finRotate _ j) := fun h =>
      emcg_finRotate_ne (by have := (P.disk p).three_le; omega) j ((P.disk p).vertex_injective h).symm
    have hcov : segment ℝ ((P.disk p).vertex j) ((P.disk p).vertex (finRotate _ j)) ⊆
        ⋃ i, (G.P'.disk x).side i := by
      intro y hy
      have hy' : y ∈ frontier (G.P'.disk x).carrier := by
        rw [hcar]
        exact emcg_disk_side_subset_frontier (P.disk p) j hy
      rw [(G.P'.disk x).frontier_eq] at hy'
      exact hy'
    obtain ⟨i, hi⟩ := emcg_exists_overlap (fun i => (G.P'.disk x).side i)
      (fun i => convex_segment _ _) hab hcov
    obtain ⟨k, hk⟩ := hdir i
    refine ⟨i, ?_⟩
    rw [← hk]
    by_cases hkj : k = j
    · rw [hkj]
    · exfalso
      rw [← hk] at hi
      obtain ⟨y, z, hyz, hsub⟩ := hi
      have hfin : (segment ℝ y z).Finite := by
        refine Set.Finite.subset
          (Set.toFinite ({(P.disk p).vertex k, (P.disk p).vertex (finRotate _ k)} : Set Pt)) ?_
        intro w hw
        exact ((P.disk p).simple k j hkj (hsub hw)).1
      exact emcg_segment_infinite hyz hfin

/-- Step 7 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"the listed sides of a type and of its template child are the same segments": a segment is a listed
side of a type iff it is a listed side of its template child. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_child_side
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ (t : D.Typ) (e : Set Pt),
      (∃ i, D.occSide ⟨t, i⟩ = e) ↔ (∃ j, (emcdTemplateChild g s l t).side j = e) := by
  intro D t e
  obtain ⟨α, X, hX⟩ := t
  obtain ⟨f, a⟩ := X
  rcases f with γ | p
  · constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, rfl⟩
  · have key := existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_singleton_side
      s.setup.GS.G (emcdBaseForm g s l (emcdOriginalForm g s l p)) p
      (existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue_step4_base_original g s l p)
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := (key _).1 ⟨i, rfl⟩
      refine ⟨j, ?_⟩
      show a +ᵥ (P.disk p).side j =
        a +ᵥ (s.setup.GS.G.P'.disk (emcdBaseForm g s l (emcdOriginalForm g s l p))).side i
      rw [hj]
    · rintro ⟨j, rfl⟩
      obtain ⟨i, hi⟩ := (key _).2 ⟨j, rfl⟩
      refine ⟨i, ?_⟩
      show a +ᵥ (s.setup.GS.G.P'.disk (emcdBaseForm g s l (emcdOriginalForm g s l p))).side i =
        a +ᵥ (P.disk p).side j
      rw [hi]

/-- Step 7 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"the outer list of a parent declared side is the list of whole outer fine sides of the template
contained in the scaled side": the sides of the certificate outer list are exactly the whole outer
sides of the retained template contained in the scaled parent side (the listed sides of a type and of
its template child are the same segments, and `σ' α` covers the scaled parent disk). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_outer_mem
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α d (e : Set Pt), e ∈ (D.outerList α d).map D.occSide ↔
      (s.setup.retained l (emcdBaseForm g s l α)).IsOuter e ∧
        e ⊆ (τ.θ ^ (s.setup.GS.k * l)) •
          (s.setup.GS.G.P'.disk (emcdBaseForm g s l α)).side (emcdParentSide g s l α d) := by
  intro D α d e
  classical
  have H := existsMacroCertificate_seed2_routing_step3_data_sub1_macroData τ h g s l hl routing
  have hk : s.setup.GS.k = g.k := by rw [s.setup_grouped, g.grouped_power]
  have hθ : D.σ.θ = τ.θ ^ (s.setup.GS.k * l) := by
    rw [hk]
    exact H.choose_spec.1
  have hreg := s.setup.region_eq l (emcdBaseForm g s l α)
  have hmemIff : ∀ o, o ∈ D.outerList α d ↔
      D.owner o.1 = α ∧ D.IsOuter o ∧ D.occSide o ⊆ D.macroSide α d := by
    intro o
    have h_outer : D.outerList α d =
        emcdGeometricOuterList (emcdGeometryData τ h g s l hl routing) α d := rfl
    rw [h_outer]
    unfold emcdGeometricOuterList
    simp only [List.mem_mergeSort, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Iff.rfl
  have hside := existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_child_side
    τ h g s l hl routing
  have hfr : ∀ o : D.SideOcc, D.owner o.1 = α →
      (D.IsOuter o ↔ D.occSide o ⊆ frontier (s.setup.retained l (emcdBaseForm g s l α)).region) := by
    intro o hown
    show D.occSide o ⊆ frontier (D.σ.θ • (D.Q.disk (D.owner o.1)).carrier) ↔ _
    rw [hown, hreg, hθ]
    exact Iff.rfl
  have hms : D.macroSide α d = (τ.θ ^ (s.setup.GS.k * l)) •
      (s.setup.GS.G.P'.disk (emcdBaseForm g s l α)).side (emcdParentSide g s l α d) := by
    show D.σ.θ • _ = _
    rw [hθ]
    rfl
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨⟨β', X, hX⟩, k⟩, ho, rfl⟩
    obtain ⟨hown, hout, hsub⟩ := (hmemIff _).1 ho
    change β' = α at hown
    subst hown
    obtain ⟨j, hj⟩ := (hside _ _).1 ⟨k, rfl⟩
    refine ⟨⟨⟨X, hX, j, hj⟩, (hfr _ rfl).1 hout⟩, ?_⟩
    rw [← hms]
    exact hsub
  · rintro ⟨⟨⟨X, hX, j, rfl⟩, hfr'⟩, hsub⟩
    obtain ⟨i, hi⟩ := (hside ⟨α, ⟨X, hX⟩⟩ (X.side j)).2 ⟨j, rfl⟩
    refine ⟨⟨⟨α, ⟨X, hX⟩⟩, i⟩, (hmemIff _).2 ⟨rfl, (hfr _ rfl).2 ?_, ?_⟩, hi⟩
    · rw [hi]
      exact hfr'
    · rw [hms, hi]
      exact hsub

/-- Step 7 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"without repetition": distinct occurrences of the outer list of a parent side carry distinct
segments (an outer side has a single owner, and the listed sides of one child are distinct). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_outer_nodup
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α d, ((D.outerList α d).map D.occSide).Nodup := by
  intro D α d
  classical
  have H := existsMacroCertificate_seed2_routing_step3_data_sub1_macroData τ h g s l hl routing
  have hrule : (D.σ.rule α).tiles =
      (fun t => (⟨emcdChildForm g s l t, emcdAnchor g s l t⟩ : PlacedTile (emcdQ g s l))) ''
        {t | emcdOwner g s l t = α} := H.choose_spec.2 α
  have hmemR : ∀ t : D.Typ, D.owner t = α → D.childTile t ∈ (D.σ.rule α).tiles := by
    intro t ht
    rw [hrule]
    exact ⟨t, ht, rfl⟩
  have hinj : ∀ t t' : D.Typ, D.owner t = D.owner t' → D.childTile t = D.childTile t' → t = t' := by
    rintro ⟨a, X, hX⟩ ⟨a', X', hX'⟩ hown heq
    change a = a' at hown
    subst hown
    have e1 : X.form = X'.form := congrArg Subtype.val (congrArg PlacedTile.form heq)
    have e2 : X.anchor = X'.anchor := by
      have h' := congrArg PlacedTile.anchor heq
      exact h'
    have e3 : X = X' := by
      cases X
      cases X'
      simp only at e1 e2
      subst e1
      subst e2
      rfl
    subst e3
    rfl
  have hmemL : ∀ o, o ∈ D.outerList α d → D.owner o.1 = α ∧ D.IsOuter o := by
    intro o H1
    have h_outer : D.outerList α d =
        emcdGeometricOuterList (emcdGeometryData τ h g s l hl routing) α d := rfl
    rw [h_outer] at H1
    unfold emcdGeometricOuterList at H1
    simp only [List.mem_mergeSort, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and] at H1
    exact ⟨H1.1, H1.2.1⟩
  have hnd : (D.outerList α d).Nodup := by
    show (emcdGeometricOuterList (emcdGeometryData τ h g s l hl routing) α d).Nodup
    unfold emcdGeometricOuterList
    exact (List.mergeSort_perm _ _).nodup_iff.2 (Finset.nodup_toList _)
  refine List.Nodup.map_on ?_ hnd
  intro o ho o' ho' heq
  obtain ⟨hown, hout⟩ := hmemL o ho
  obtain ⟨hown', -⟩ := hmemL o' ho'
  by_cases h11 : o.1 = o'.1
  · obtain ⟨t, k⟩ := o
    obtain ⟨t', k'⟩ := o'
    change t = t' at h11
    subst h11
    have hk : k = k' :=
      existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step1_side_injective
        (D.childTile t) k k' heq
    subst hk
    rfl
  · exfalso
    have hne : D.childTile o.1 ≠ D.childTile o'.1 := fun e =>
      h11 (hinj _ _ (hown.trans hown'.symm) e)
    have hq : (D.childTile o.1).vertex o.2 + (1 / 2 : ℝ) • ((D.childTile o.1).vertex (finRotate _ o.2) -
        (D.childTile o.1).vertex o.2) ∈
        openSegment ℝ ((D.childTile o.1).vertex o.2) ((D.childTile o.1).vertex (finRotate _ o.2)) :=
      by rw [openSegment_eq_image']; exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
    obtain ⟨r, hr, σ, -, hball⟩ := two_sides (D.σ.rule α).disjoint (hmemR _ hown) (hmemR _ hown')
      hne o.2 o'.2 heq.symm hq
    have hsub : Metric.ball ((D.childTile o.1).vertex o.2 + (1 / 2 : ℝ) •
        ((D.childTile o.1).vertex (finRotate _ o.2) - (D.childTile o.1).vertex o.2)) r ⊆
        D.σ.θ • (D.Q.disk α).carrier := by
      intro x hx
      rw [← D.σ.support_eq α]
      show x ∈ ⋃ B ∈ (D.σ.rule α).tiles, B.carrier
      obtain ⟨-, h2, h3⟩ := hball x hx
      by_cases hs : x ∈ (D.childTile o.1).carrier
      · exact Set.mem_biUnion (hmemR _ hown) hs
      · exact Set.mem_biUnion (hmemR _ hown')
          (interior_subset (h2 (lt_of_not_ge (fun hge => hs (h3 hge)))))
    have hint := mem_interior.2 ⟨_, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
    have hqs : (D.childTile o.1).vertex o.2 + (1 / 2 : ℝ) • ((D.childTile o.1).vertex (finRotate _ o.2) -
        (D.childTile o.1).vertex o.2) ∈ D.occSide o := by
      show _ ∈ (D.childTile o.1).side o.2
      rw [emcg_side_eq_segment]
      exact openSegment_subset_segment ℝ _ _ hq
    have hqf := hout hqs
    unfold MacroData.macroBoundary MacroData.macroRegion at hqf
    rw [hown] at hqf
    exact hqf.2 hint

/-- Step 7 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"for every nonzero direction exactly one of `v`, `-v` is positive": a nonzero direction which is not
lexicographically positive has a lexicographically positive opposite. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_lex_neg
    (v : Pt) (hv : v ≠ 0) (hnp : ¬ LexPositive v) : LexPositive (-v) := by
  unfold LexPositive at hnp ⊢
  simp only [PiLp.neg_apply]
  push_neg at hnp
  obtain ⟨h0, h1⟩ := hnp
  rcases h0.lt_or_eq with h0 | h0
  · left; linarith
  · right
    refine ⟨by rw [h0]; simp, ?_⟩
    rcases (h1 h0).lt_or_eq with h1' | h1'
    · linarith
    · exfalso; apply hv; ext i; fin_cases i <;> simp [h0, h1']

/-- Step 7 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"in the lexicographically positive direction of the supporting line": two non-overlapping
nondegenerate segments of a line with lexicographically positive direction `dir`, whose midpoints are
ordered along `dir`, have all their points ordered in the `LexPositive` order. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_line_order
    (u dir a b a' b' : Pt) (hdir : LexPositive dir)
    (hline : ∀ z ∈ segment ℝ a b ∪ segment ℝ a' b', ∃ t : ℝ, z = u + t • dir)
    (hab : a ≠ b) (hab' : a' ≠ b')
    (hno : ¬ OverlapPos (segment ℝ a b) (segment ℝ a' b'))
    (hmid : (midpoint ℝ a b) 0 * dir 0 + (midpoint ℝ a b) 1 * dir 1 ≤
      (midpoint ℝ a' b') 0 * dir 0 + (midpoint ℝ a' b') 1 * dir 1) :
    ∀ x ∈ segment ℝ a b, ∀ y ∈ segment ℝ a' b', x = y ∨ LexPositive (y - x) := by
  set F : Pt → ℝ := fun z => z 0 * dir 0 + z 1 * dir 1 with hF
  have hFadd : ∀ (z v : Pt) (c : ℝ), F (z + c • v) = F z + c * F v := by
    intro z v c; simp only [hF, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have hFsub : ∀ z z' : Pt, F (z' - z) = F z' - F z := by
    intro z z'; simp only [hF, PiLp.sub_apply]; ring
  have hFd : 0 < F dir := by
    simp only [hF]
    rcases hdir with h | ⟨h0, h1⟩
    · nlinarith [sq_nonneg (dir 1)]
    · rw [h0]; nlinarith
  have hL : ∀ z z' : Pt, (∃ t : ℝ, z = u + t • dir) → (∃ t : ℝ, z' = u + t • dir) →
      z' - z = ((F z' - F z) / F dir) • dir := by
    rintro z z' ⟨t, rfl⟩ ⟨t', rfl⟩
    rw [hFadd, hFadd]
    have : (F u + t' * F dir - (F u + t * F dir)) / F dir = t' - t := by
      field_simp; ring
    rw [this, sub_smul]; abel
  have hlex : ∀ c : ℝ, 0 < c → LexPositive (c • dir) := by
    intro c hc
    rcases hdir with h | ⟨h0, h1⟩
    · left; simp only [PiLp.smul_apply, smul_eq_mul]; positivity
    · right; simp only [PiLp.smul_apply, smul_eq_mul, h0, mul_zero, true_and]; positivity
  have hon1 : ∀ z ∈ segment ℝ a b, ∃ t : ℝ, z = u + t • dir := fun z hz => hline z (Or.inl hz)
  have hon2 : ∀ z ∈ segment ℝ a' b', ∃ t : ℝ, z = u + t • dir := fun z hz => hline z (Or.inr hz)
  have hrange : ∀ p q z : Pt, z ∈ segment ℝ p q →
      min (F p) (F q) ≤ F z ∧ F z ≤ max (F p) (F q) := by
    intro p q z hz
    rw [segment_eq_image'] at hz
    obtain ⟨c, ⟨hc0, hc1⟩, rfl⟩ := hz
    rw [hFadd, hFsub]
    constructor
    · rcases le_total (F p) (F q) with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    · rcases le_total (F p) (F q) with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
  have hmem : ∀ p q z : Pt, (∃ t : ℝ, p = u + t • dir) → (∃ t : ℝ, q = u + t • dir) →
      (∃ t : ℝ, z = u + t • dir) → F p ≠ F q →
      min (F p) (F q) ≤ F z → F z ≤ max (F p) (F q) → z ∈ segment ℝ p q := by
    intro p q z hp hq hz hpq h1 h2
    have e1 := hL p z hp hz
    have e2 := hL p q hp hq
    rw [segment_eq_image']
    refine ⟨(F z - F p) / (F q - F p), ?_, ?_⟩
    · rcases lt_or_gt_of_ne hpq with h | h
      · rw [min_eq_left h.le] at h1; rw [max_eq_right h.le] at h2
        constructor
        · apply div_nonneg <;> linarith
        · rw [div_le_one (by linarith)]; linarith
      · rw [min_eq_right h.le] at h1; rw [max_eq_left h.le] at h2
        constructor
        · apply div_nonneg_of_nonpos <;> linarith
        · rw [div_le_one_of_neg (by linarith)]; linarith
    · have hne : F q - F p ≠ 0 := sub_ne_zero.2 (Ne.symm hpq)
      simp only
      rw [e2, smul_smul]
      have : (F z - F p) / (F q - F p) * ((F q - F p) / F dir) = (F z - F p) / F dir := by
        field_simp
      rw [this, ← e1]; abel
  have hFab : F a ≠ F b := by
    intro h
    apply hab
    have := hL a b (hon1 a (left_mem_segment ℝ a b)) (hon1 b (right_mem_segment ℝ a b))
    rw [h, sub_self, zero_div, zero_smul, sub_eq_zero] at this
    exact this.symm
  have hFab' : F a' ≠ F b' := by
    intro h
    apply hab'
    have := hL a' b' (hon2 a' (left_mem_segment ℝ a' b')) (hon2 b' (right_mem_segment ℝ a' b'))
    rw [h, sub_self, zero_div, zero_smul, sub_eq_zero] at this
    exact this.symm
  have hmid' : F a + F b ≤ F a' + F b' := by
    have e1 : F (midpoint ℝ a b) = (F a + F b) / 2 := by
      rw [midpoint_eq_smul_add]
      simp only [hF, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, invOf_eq_inv]; ring
    have e2 : F (midpoint ℝ a' b') = (F a' + F b') / 2 := by
      rw [midpoint_eq_smul_add]
      simp only [hF, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, invOf_eq_inv]; ring
    have : F (midpoint ℝ a b) ≤ F (midpoint ℝ a' b') := hmid
    rw [e1, e2] at this; linarith
  have key : ∀ x ∈ segment ℝ a b, ∀ y ∈ segment ℝ a' b', F x ≤ F y := by
    intro x hx y hy
    by_contra hlt
    push_neg at hlt
    obtain ⟨hx1, hx2⟩ := hrange a b x hx
    obtain ⟨hy1, hy2⟩ := hrange a' b' y hy
    have hs : max (min (F a) (F b)) (min (F a') (F b')) <
        min (max (F a) (F b)) (max (F a') (F b')) := by
      rcases lt_or_gt_of_ne hFab with h1 | h1 <;> rcases lt_or_gt_of_ne hFab' with h2 | h2 <;>
        simp only [min_def, max_def] at hx1 hx2 hy1 hy2 ⊢ <;>
        split_ifs at * <;> linarith
    set s1 := max (min (F a) (F b)) (min (F a') (F b'))
    set s2 := min (max (F a) (F b)) (max (F a') (F b'))
    have hp : ∀ s : ℝ, F (u + ((s - F u) / F dir) • dir) = s := by
      intro s; rw [hFadd]; field_simp; ring
    have hon : ∀ s : ℝ, ∃ t : ℝ, u + ((s - F u) / F dir) • dir = u + t • dir := fun s => ⟨_, rfl⟩
    have hin : ∀ s, s1 ≤ s → s ≤ s2 →
        u + ((s - F u) / F dir) • dir ∈ segment ℝ a b ∩ segment ℝ a' b' := by
      intro s h1 h2
      refine ⟨hmem a b _ (hon1 a (left_mem_segment ℝ a b)) (hon1 b (right_mem_segment ℝ a b))
        (hon s) hFab ?_ ?_, hmem a' b' _ (hon2 a' (left_mem_segment ℝ a' b'))
        (hon2 b' (right_mem_segment ℝ a' b')) (hon s) hFab' ?_ ?_⟩ <;> rw [hp]
      · exact le_trans (le_max_left _ _) h1
      · exact le_trans h2 (min_le_left _ _)
      · exact le_trans (le_max_right _ _) h1
      · exact le_trans h2 (min_le_right _ _)
    apply hno
    refine ⟨u + ((s1 - F u) / F dir) • dir, u + ((s2 - F u) / F dir) • dir, ?_, ?_⟩
    · intro he
      have := congrArg F he
      rw [hp, hp] at this
      linarith
    · exact ((convex_segment a b).inter (convex_segment a' b')).segment_subset
        (hin s1 le_rfl hs.le) (hin s2 hs.le le_rfl)
  intro x hx y hy
  have h := key x hx y hy
  have e := hL x y (hon1 x hx) (hon2 y hy)
  rcases h.lt_or_eq with h | h
  · right; rw [e]; exact hlex _ (div_pos (by linarith) hFd)
  · left; rw [h, sub_self, zero_div, zero_smul, sub_eq_zero] at e; exact e.symm

/-- Step 7 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"in the lexicographically positive direction of the supporting line": the outer list, sorted by the
midpoint coordinate along the positive direction of the scaled side, lists its (non-overlapping,
collinear) sides in the `LexPositive` order. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_outer_sorted
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α d, ((D.outerList α d).map D.occSide).Pairwise
      (fun e e' => ∀ x ∈ e, ∀ y ∈ e', x = y ∨ LexPositive (y - x)) := by
  intro D α d
  classical
  have hmemIff : ∀ o, o ∈ D.outerList α d ↔
      D.owner o.1 = α ∧ D.IsOuter o ∧ D.occSide o ⊆ D.macroSide α d := by
    intro o
    have h_outer : D.outerList α d =
        emcdGeometricOuterList (emcdGeometryData τ h g s l hl routing) α d := rfl
    rw [h_outer]
    unfold emcdGeometricOuterList
    simp only [List.mem_mergeSort, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Iff.rfl
  have hsort : (D.outerList α d).Pairwise (fun o o' =>
      (D.occMid o) 0 * (D.macroSideDir α d) 0 + (D.occMid o) 1 * (D.macroSideDir α d) 1 ≤
        (D.occMid o') 0 * (D.macroSideDir α d) 0 + (D.occMid o') 1 * (D.macroSideDir α d) 1) := by
    show (emcdGeometricOuterList (emcdGeometryData τ h g s l hl routing) α d).Pairwise _
    unfold emcdGeometricOuterList
    dsimp only
    refine (List.pairwise_mergeSort ?_ ?_ _).imp ?_
    · intro a b c hab hbc
      simp only [decide_eq_true_eq] at hab hbc ⊢
      linarith
    · intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _
    · intro a b hab
      exact of_decide_eq_true hab
  have hdist : (D.outerList α d).Pairwise (fun o o' => D.occSide o ≠ D.occSide o') :=
    List.pairwise_map.1
      (existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_outer_nodup
        τ h g s l hl routing α d)
  have hside := existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_child_side
    τ h g s l hl routing
  have hchild : ∀ t : D.Typ, D.owner t = α →
      emcdTemplateChild g s l t ∈ (s.setup.retained l (emcdBaseForm g s l α)).children.tiles := by
    rintro ⟨β', X, hX⟩ hown
    change β' = α at hown
    subst hown
    exact hX
  have hθ0 : D.σ.θ ≠ 0 := (lt_trans zero_lt_one D.σ.one_lt).ne'
  have hpq : (D.Q.disk α).vertex d ≠ (D.Q.disk α).vertex (finRotate _ d) := fun h' =>
    emcg_finRotate_ne (by have := (D.Q.disk α).three_le; omega) d ((D.Q.disk α).vertex_injective h').symm
  have hdirP : LexPositive (D.macroSideDir α d) ∧ ∀ z ∈ D.macroSide α d,
      ∃ t : ℝ, z = D.σ.θ • (D.Q.disk α).vertex d + t • D.macroSideDir α d := by
    have hmem : ∀ z ∈ D.macroSide α d, ∃ t : ℝ, z = D.σ.θ • (D.Q.disk α).vertex d +
        t • (D.σ.θ • (D.Q.disk α).vertex (finRotate _ d) - D.σ.θ • (D.Q.disk α).vertex d) := by
      intro z hz
      obtain ⟨z0, hz0, rfl⟩ := hz
      unfold PolygonalDisk.side at hz0
      rw [segment_eq_image'] at hz0
      obtain ⟨t, -, rfl⟩ := hz0
      exact ⟨t, by module⟩
    have hne : D.σ.θ • (D.Q.disk α).vertex (finRotate _ d) - D.σ.θ • (D.Q.disk α).vertex d ≠ 0 := by
      rw [sub_ne_zero]
      intro h'
      exact hpq (smul_right_injective Pt hθ0 h').symm
    unfold MacroData.macroSideDir MacroData.posDir
    split_ifs with hpos
    · exact ⟨hpos, hmem⟩
    · refine ⟨?_, fun z hz => ?_⟩
      · rw [← neg_sub]
        exact existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_lex_neg
          _ hne hpos
      · obtain ⟨t, rfl⟩ := hmem z hz
        exact ⟨-t, by module⟩
  have hseg : ∀ o : D.SideOcc, D.occSide o = segment ℝ (D.occStart o) (D.occEnd o) :=
    fun o => emcg_side_eq_segment _ _
  rw [List.pairwise_map]
  refine (hsort.and hdist).imp_of_mem ?_
  rintro o o' ho ho' ⟨hle, hne⟩
  obtain ⟨hown, -, hsub⟩ := (hmemIff o).1 ho
  obtain ⟨hown', -, hsub'⟩ := (hmemIff o').1 ho'
  have hno : ¬ OverlapPos (D.occSide o) (D.occSide o') := by
    intro hov
    apply hne
    obtain ⟨j, hj⟩ := (hside o.1 _).1 ⟨o.2, rfl⟩
    obtain ⟨j', hj'⟩ := (hside o'.1 _).1 ⟨o'.2, rfl⟩
    rw [← hj, ← hj']
    refine (s.setup.retained l (emcdBaseForm g s l α)).sts _ (hchild _ hown) _ (hchild _ hown') j j' ?_
    rw [hj, hj']
    exact hov
  rw [hseg o, hseg o'] at hno ⊢
  refine existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_line_order
    (D.σ.θ • (D.Q.disk α).vertex d) (D.macroSideDir α d) _ _ _ _ hdirP.1 ?_
    (emcg_vertex_ne (D.childTile o.1) o.2) (emcg_vertex_ne (D.childTile o'.1) o'.2) hno hle
  rintro z (hz | hz)
  · exact hdirP.2 z (hsub (by rw [hseg o]; exact hz))
  · exact hdirP.2 z (hsub' (by rw [hseg o']; exact hz))

/-- Step 7 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"each list has at least five entries because the five ports of the routing are distinct entries of it
(they are the quantiles of this very list)": the certificate port `i` of a parent side carries the
routing port `i` of that side (the globally ordered outer list of the certificate is the
`LexPositive`-ordered list of whole outer sides of the routing). -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_port_side
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α d (i : Fin 5) (o : D.SideOcc), D.port α d i = some o →
      D.occSide o = (routing (emcdBaseForm g s l α)).port (emcdParentSide g s l α d) i := by
  intro D α d i o hp
  obtain ⟨L, hLmem, hLnd, hLs, hLport⟩ :=
    (routing (emcdBaseForm g s l α)).port_quantile (emcdParentSide g s l α d)
  have hom := existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_outer_mem
    τ h g s l hl routing α d
  have heq : (D.outerList α d).map D.occSide = L := by
    apply existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_list_eq
    · intro e
      rw [hom, hLmem]
    · exact existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_outer_nodup
        τ h g s l hl routing α d
    · exact hLnd
    · exact existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_outer_sorted
        τ h g s l hl routing α d
    · exact hLs
    · intro e he
      rw [hom] at he
      obtain ⟨⟨⟨A, -, j, rfl⟩, -⟩, -⟩ := he
      exact ⟨A.vertex j, by rw [emcg_side_eq_segment]; exact left_mem_segment ℝ _ _⟩
  have hlen : (D.outerList α d).length = L.length := by
    rw [← heq, List.length_map]
  have h1 := hLport i
  unfold MacroData.port at hp
  rw [← hlen, ← heq, List.getElem?_map, hp] at h1
  exact Option.some.inj h1

private lemma emcd_paths_head_destutter {A : Type*} (R : A → A → Prop)
    [DecidableRel R] (xs : List A) : (xs.destutter R).head? = xs.head? := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      rw [List.destutter_cons']
      induction xs generalizing x with
      | nil => rfl
      | cons y ys ih =>
          rw [List.destutter'_cons]
          split
          · rfl
          · exact ih x

/-- Step 2 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: head -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step2_head
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d i, D.IsGenuinePath α d i → (D.path α d i).head? = D.port α d i) := by
  classical
  intro D α d i hi
  let j : Fin 4 := ⟨i.val, hi.2⟩
  have hji : j.castSucc = i := Fin.ext rfl
  have hfrom :=
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step1_from_routing
      τ h g s l hl routing α d j hi.1
  have hfromHead := congrArg List.head? hfrom
  rw [emcd_paths_head_destutter] at hfromHead
  have hrouteHead :=
    (routing (emcdBaseForm g s l α)).path_head
      (emcdParentSide g s l α d) hi.1 j
  have hpathSide : ((D.path α d i).map D.occSide).head? =
      some ((routing (emcdBaseForm g s l α)).port
        (emcdParentSide g s l α d) i) := by
    rw [← hji]
    exact hfromHead.trans hrouteHead
  obtain ⟨L, hLmem, hLnd, hLs, hLport⟩ :=
    (routing (emcdBaseForm g s l α)).port_quantile
      (emcdParentSide g s l α d)
  have hom :=
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_outer_mem
      τ h g s l hl routing α d
  have heq : (D.outerList α d).map D.occSide = L := by
    apply existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_list_eq
    · intro e
      rw [hom, hLmem]
    · exact
        existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_outer_nodup
          τ h g s l hl routing α d
    · exact hLnd
    · exact
        existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_outer_sorted
          τ h g s l hl routing α d
    · exact hLs
    · intro e he
      rw [hom] at he
      obtain ⟨⟨⟨A, -, k, rfl⟩, -⟩, -⟩ := he
      exact ⟨A.vertex k, by rw [emcg_side_eq_segment]; exact left_mem_segment ℝ _ _⟩
  have hlen : (D.outerList α d).length = L.length := by
    rw [← heq, List.length_map]
  have hportRoute := hLport i
  have hportSome : ∃ o, D.port α d i = some o := by
    unfold MacroData.port
    rw [← hlen, ← heq, List.getElem?_map] at hportRoute
    cases hp : (D.outerList α d)[MacroData.portRank (D.outerList α d).length i - 1]? with
    | none => simp [hp] at hportRoute
    | some o => exact ⟨o, rfl⟩
  obtain ⟨o, ho⟩ := hportSome
  have hoside :=
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_port_side
      τ h g s l hl routing α d i o ho
  cases hhead : (D.path α d i).head? with
  | none =>
      rw [List.head?_map, hhead] at hpathSide
      contradiction
  | some o' =>
      rw [List.head?_map, hhead] at hpathSide
      simp only [Option.map_some, Option.some.injEq] at hpathSide
      have hmem : o' ∈ D.path α d i := List.mem_of_mem_head? hhead
      have howner' :=
        existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step5_owner
          τ h g s l hl routing α d i o' hmem
      have hportMem : o ∈ D.outerList α d := List.mem_of_getElem? ho
      have hportProps :=
        (existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer_step2_orientation_outer
          τ h g s l hl routing).2.1 α d o |>.1 hportMem
      have hsides : D.occSide o' = D.occSide o := hpathSide.trans hoside.symm
      have houter' : D.IsOuter o' := by
        have houter := hportProps.2.1
        unfold MacroData.IsOuter at houter ⊢
        rw [howner', hsides]
        rw [hportProps.1] at houter
        exact houter
      have hoo' : o' = o :=
        emcd_outer_step2_occ_injective τ h g s l hl routing
          (howner'.trans hportProps.1.symm) houter' hportProps.2.1 hsides
      rw [ho, hoo']

/-- Step 8 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"the outer list of a parent declared side is the list of whole outer fine sides of the template
contained in the scaled side": a port of a parent side lies in that scaled side. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step8_port_sub
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α d (i : Fin 5) (o : D.SideOcc), D.port α d i = some o → D.occSide o ⊆ D.macroSide α d := by
  intro D α d i o hp
  classical
  have H1 : o ∈ D.outerList α d := List.mem_of_getElem? hp
  have h_outer : D.outerList α d =
      emcdGeometricOuterList (emcdGeometryData τ h g s l hl routing) α d := rfl
  rw [h_outer] at H1
  unfold emcdGeometricOuterList at H1
  simp only [List.mem_mergeSort, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and] at H1
  exact H1.2.2

/-- Step 9 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint`:
"three polygons with disjoint interiors cannot share a whole segment" (the parent polygon is
simple): a whole fine side contained in two scaled parent sides determines the parent side. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step9_macroSide
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α (d d' : Fin (D.Q.disk α).n) (o : D.SideOcc),
      D.occSide o ⊆ D.macroSide α d → D.occSide o ⊆ D.macroSide α d' → d = d' := by
  intro D α d d' o h1 h2
  by_contra hne
  have hθ : D.σ.θ ≠ 0 := (lt_trans zero_lt_one D.σ.one_lt).ne'
  have hsub : D.occSide o ⊆
      D.σ.θ • ({(D.Q.disk α).vertex d, (D.Q.disk α).vertex (finRotate _ d)} : Set Pt) := by
    intro x hx
    have hx1 := h1 hx
    have hx2 := h2 hx
    unfold MacroData.macroSide at hx1 hx2
    have hx3 : x ∈ D.σ.θ • ((D.Q.disk α).side d ∩ (D.Q.disk α).side d') := by
      rw [Set.smul_set_inter₀ hθ]
      exact ⟨hx1, hx2⟩
    obtain ⟨y, hy, rfl⟩ := hx3
    exact Set.smul_mem_smul_set (((D.Q.disk α).simple d d' hne hy).1)
  rw [Set.smul_set_insert, Set.smul_set_singleton] at hsub
  have hseg : D.occSide o = segment ℝ ((D.childTile o.1).vertex o.2)
      ((D.childTile o.1).vertex (finRotate _ o.2)) := emcg_side_eq_segment _ _
  have hab := emcg_vertex_ne (D.childTile o.1) o.2
  rw [hseg] at hsub
  have ha := hsub (left_mem_segment ℝ _ _)
  have hb := hsub (right_mem_segment ℝ _ _)
  have hm := hsub (midpoint_mem_segment ((D.childTile o.1).vertex o.2)
    ((D.childTile o.1).vertex (finRotate _ o.2)))
  have hma : midpoint ℝ ((D.childTile o.1).vertex o.2) ((D.childTile o.1).vertex (finRotate _ o.2)) ≠
      (D.childTile o.1).vertex o.2 := by
    rw [Ne, midpoint_eq_left_iff]
    exact hab
  have hmb : midpoint ℝ ((D.childTile o.1).vertex o.2) ((D.childTile o.1).vertex (finRotate _ o.2)) ≠
      (D.childTile o.1).vertex (finRotate _ o.2) := by
    rw [Ne, midpoint_eq_right_iff]
    exact hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hm
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hm with hm | hm <;>
    first
    | exact hab (ha.trans hb.symm)
    | exact hma (hm.trans ha.symm)
    | exact hmb (hm.trans hb.symm)

/-- Step 14 of the blueprint proof of `existsMacroCertificate_seed2_routing_step3_data_sub7_paths`: disjoint -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    ∀ α (d d' : Fin (D.Q.disk α).n) (i i' : Fin 5), (d, i) ≠ (d', i') →
      ∀ o, o ∈ D.path α d i → o ∈ D.path α d' i' →
        d = d' ∧ (o = D.printOcc α d ∨ o = D.partner (D.printOcc α d)) := by
  intro D α d d' i i' hne o ho ho'
  classical
  have hsing : ∀ (d : Fin (D.Q.disk α).n) (i : Fin 5), ¬ D.IsGenuinePath α d i →
      o ∈ D.path α d i → D.port α d i = some o := by
    intro d i hg hmem
    rw [existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step7_trivial τ h g s l hl routing
      α d i hg] at hmem
    exact Option.mem_toList.mp hmem
  have hgen_mem : ∀ (d : Fin (D.Q.disk α).n) (i : Fin 5) (hg : D.IsGenuinePath α d i),
      o ∈ D.path α d i → D.occSide o ∈
        (routing (emcdBaseForm g s l α)).pathSides (emcdParentSide g s l α d) ⟨i.val, hg.2⟩ := by
    intro d i hg hmem
    obtain ⟨k, X, -, -, hk | hk⟩ :=
      existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step2_lift_mem
        τ h g s l hl routing α d i hg o hmem
    · exact List.mem_of_getElem? hk
    · exact List.mem_of_getElem? hk
  have hmixed : ∀ (d d' : Fin (D.Q.disk α).n) (i i' : Fin 5), D.IsGenuinePath α d i →
      ¬ D.IsGenuinePath α d' i' → o ∈ D.path α d i → o ∈ D.path α d' i' → False := by
    intro d d' i i' hg hg' hm hm'
    have hp := existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_port_side
      τ h g s l hl routing α d' i' o (hsing d' i' hg' hm')
    have hunm : emcdParentSide g s l α d' ∉ s.setup.markedSides (emcdBaseForm g s l α) ∨ i' = 4 := by
      by_cases hmk : D.marked α d'
      · right
        have : ¬ i'.val < 4 := fun hlt => hg' ⟨hmk, hlt⟩
        have hlt := i'.isLt
        ext
        show (i' : ℕ) = 4
        omega
      · left
        exact hmk
    have hmem := hgen_mem d i hg hm
    rw [hp] at hmem
    exact (routing (emcdBaseForm g s l α)).singleton_disjoint _ i' hunm _ hg.1 ⟨i.val, hg.2⟩ hmem
  by_cases hg : D.IsGenuinePath α d i <;> by_cases hg' : D.IsGenuinePath α d' i'
  · have hne' : (emcdParentSide g s l α d, (⟨i.val, hg.2⟩ : Fin 4)) ≠
        (emcdParentSide g s l α d', (⟨i'.val, hg'.2⟩ : Fin 4)) := by
      intro heq
      apply hne
      simp only [Prod.mk.injEq, Fin.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      have h3 : i = i' := Fin.ext h2
      exact Prod.ext h1 h3
    have hcases := existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step3_cases
      τ h g s l hl routing
    rcases hcases α d i hg o ho with h1 | ⟨h1, h1c⟩ <;>
      rcases hcases α d' i' hg' o ho' with h2 | ⟨h2, h2c⟩
    · exact ((routing (emcdBaseForm g s l α)).path_disjoint _ hg.1 _ hg'.1 _ _ hne' h1 h2).elim
    · exact ((routing (emcdBaseForm g s l α)).path_central _ hg.1 _ _ h1 ⟨_, h2.symm⟩).elim
    · exact ((routing (emcdBaseForm g s l α)).path_central _ hg'.1 _ _ h2 ⟨_, h1.symm⟩).elim
    · have hidx := existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step1_side_injective
        _ _ _ (h1.symm.trans h2)
      have hdd : emcdParentSide g s l α d = emcdParentSide g s l α d' :=
        (routing (emcdBaseForm g s l α)).print_injOn (Finset.mem_coe.2 hg.1) (Finset.mem_coe.2 hg'.1) hidx
      refine ⟨hdd, Or.inr ?_⟩
      exact existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step6_print_partner
        τ h g s l hl routing α d o
        (existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step5_owner τ h g s l hl routing
          α d i o ho) h1c h1
  · exact (hmixed d d' i i' hg hg' ho ho').elim
  · exact (hmixed d' d i' i hg' hg ho' ho).elim
  · have hp := hsing d i hg ho
    have hp' := hsing d' i' hg' ho'
    have hdd : d = d' :=
      existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step9_macroSide
        τ h g s l hl routing α d d' o
        (existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step8_port_sub
          τ h g s l hl routing α d i o hp)
        (existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step8_port_sub
          τ h g s l hl routing α d' i' o hp')
    subst hdd
    have hports := (existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_port_side
      τ h g s l hl routing α d i o hp).symm.trans
      (existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint_step7_port_side
        τ h g s l hl routing α d i' o hp')
    have hii := (routing (emcdBaseForm g s l α)).port_injective _ hports
    exact absurd (by rw [hii]) hne

/-- Step 4 of `lem:certificate-exists`: the path clauses for `emcdMacroData`: lifting each routed
geometric side list `(routing (emcdBaseForm g s l α)).pathSides d i` and tile list `pathTiles d i`
to the alternating entry/exit side-occurrence chain `D.path α d i.castSucc` (ending at
`D.partner (D.printOcc α d)` in its small owner) and setting unmarked and fifth paths to singleton
ports `(D.port α d i).toList` establishes `path_from_routing`, `path_head`, `path_last`,
`path_chain`, `path_owner`, `path_partner`, `path_trivial`, `fifth_path`, `path_inner`,
`path_marked`, `path_not_central`, `path_penultimate`, `path_nodup`, and `path_disjoint`. -/
private lemma existsMacroCertificate_seed2_routing_step3_data_sub7_paths
    (τ : Substitution P) (h : τ.STS) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ) (hl : 0 < l)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    let D := emcdMacroData τ h g s l hl routing
    (∀ α d (i : Fin 4), D.marked α d →
      @List.destutter (Set Pt) (· ≠ ·) (Classical.decRel _)
        ((D.path α d i.castSucc).map D.occSide) =
        (routing (emcdBaseForm g s l α)).pathSides (emcdParentSide g s l α d) i) ∧
    (∀ α d i, D.IsGenuinePath α d i → (D.path α d i).head? = D.port α d i) ∧
    (∀ α d i, D.IsGenuinePath α d i →
      (D.path α d i).getLast? = some (D.partner (D.printOcc α d))) ∧
    (∀ α d i (n : ℕ) (o o' : D.SideOcc),
      (D.path α d i)[n]? = some o → (D.path α d i)[n + 1]? = some o' →
        o.1 = o'.1 ∨ (D.IsInner o ∧ o' = D.partner o)) ∧
    (∀ α d i (o : D.SideOcc), o ∈ D.path α d i → D.owner o.1 = α) ∧
    (∀ α d i, D.IsGenuinePath α d i →
      ∀ o ∈ D.path α d i, D.IsInner o → ¬ D.IsPrint o → D.partner o ∈ D.path α d i) ∧
    (∀ α d i, ¬ D.IsGenuinePath α d i → D.path α d i = (D.port α d i).toList) ∧
    (∀ α d, D.path α d (4 : Fin 5) = (D.port α d (4 : Fin 5)).toList) ∧
    (∀ α d i, D.IsGenuinePath α d i →
      ∀ (n : ℕ) (o : D.SideOcc), (D.path α d i)[n + 1]? = some o → D.IsInner o) ∧
    (∀ α d i, D.IsGenuinePath α d i → ∀ o ∈ D.path α d i, D.IsMarked o) ∧
    (∀ α d i, D.IsGenuinePath α d i → ∀ o ∈ D.path α d i, o.1 ≠ D.central α) ∧
    (∀ α d i, D.IsGenuinePath α d i →
      ∀ o : D.SideOcc, (D.path α d i)[(D.path α d i).length - 2]? = some o →
        o.1 = (D.partner (D.printOcc α d)).1 ∧ D.IsOrdinary o) ∧
    (∀ α d i, (D.path α d i).Nodup) ∧
    ∀ α (d d' : Fin (D.Q.disk α).n) (i i' : Fin 5), (d, i) ≠ (d', i') →
      ∀ o, o ∈ D.path α d i → o ∈ D.path α d' i' →
        d = d' ∧ (o = D.printOcc α d ∨ o = D.partner (D.printOcc α d)) := by
  exact ⟨
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step1_from_routing τ h g s l hl routing,
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step2_head τ h g s l hl routing,
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step3_last τ h g s l hl routing,
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step4_chain τ h g s l hl routing,
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step5_owner τ h g s l hl routing,
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step6_partner τ h g s l hl routing,
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step7_trivial τ h g s l hl routing,
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step8_fifth τ h g s l hl routing,
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step9_inner τ h g s l hl routing,
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step10_marked τ h g s l hl routing,
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step11_not_central τ h g s l hl routing,
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step12_penultimate τ h g s l hl routing,
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step13_nodup τ h g s l hl routing,
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths_step14_disjoint τ h g s l hl routing⟩

/-- Step 4 of `lem:certificate-exists`: the finite packaging.  "Keep the finite labelled groups in
`P'`" (here: the retained catalogue tiles), "the types are the positioned children of the
retained templates", kinds, marking, interface identifiers, special sides, prints, globally
ordered outer lists, the occurrence chains of the routed paths, and the constants; the
representation clauses (`Δσ' = τ^m Δ`, STS of the dissections, singleton originals, supertile
origin, hereditary transfer) and the template clauses (positioned children, STS templates) are
proved for this data.  See the blueprint for the detailed proof. -/
private lemma existsMacroCertificate_seed2_routing_step3_data (τ : Substitution P) (h : τ.STS)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (hl : 0 < l) (hidem : s.setup.c^[2 * l] = s.setup.c^[l])
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)) :
    Nonempty (existsMacroCertificate_CertData τ g s l routing) := by
  obtain ⟨hdisk_c, hdisk_v, hdisk_ccw, hscat, horig_tile, horig_scat, hcat_inj, hgd_dist,
    hkind_o, hkind_l, hkind_s, hbase_f, hbase_o, hcat_f_inj⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub2_catalogue τ h g s l hl routing
  obtain ⟨htmpl, hchild_bij, hchild_c, hchild_s, hcent_c, hcent_f, hcent_o, hchild_f,
    hps_inj, hps_bij, hps_cyc, hps_geom, hmark_setup, hmark_nonl, hmark_l⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub3_children_and_templates τ h g s l hl
      hidem routing
  have hrep := existsMacroCertificate_seed2_routing_step3_data_sub4_representation τ h g s l hl
    routing
  obtain ⟨hpart, hedge, hedge_t, hpos, hout_mem, hout_nodup, hout_sort, hN, hQmax,
    hrank_ge, hrank_max⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub5_interfaces_and_outer τ h g s l hl routing
  obtain ⟨hpr_rout, hpr_inj, hpr_cyc, hpr_in, hpr_sm, hsp_sm, hsp_uniq, hsp_cont, hsp_pr⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub6_prints_and_special τ h g s l hl routing
      (fun β => (routing β).print_partner_injOn)
  obtain ⟨hpa_rout, hpa_head, hpa_last, hpa_chain, hpa_own, hpa_part, hpa_triv, hpa_5,
    hpa_in, hpa_mark, hpa_ncent, hpa_pen, hpa_nodup, hpa_disj⟩ :=
    existsMacroCertificate_seed2_routing_step3_data_sub7_paths τ h g s l hl routing
  exact ⟨{
    l_pos := hl
    central_idempotent := hidem
    D := emcdMacroData τ h g s l hl routing
    rep := hrep
    tmpl := htmpl
    baseForm := emcdBaseForm g s l
    catalogueTile := emcdCatalogueTile g s l
    disk_carrier := hdisk_c
    disk_vertexSet := hdisk_v
    disk_ccw := hdisk_ccw
    scatter_eq := hscat
    originalForm := emcdOriginalForm g s l
    original_tile := horig_tile
    original_scatter := horig_scat
    catalogue_injective := hcat_inj
    grouped_disks_distinct := hgd_dist
    kind_original := hkind_o
    kind_large := hkind_l
    kind_small := hkind_s
    templateChild := emcdTemplateChild g s l
    child_bijective := hchild_bij
    child_carrier := hchild_c
    child_sideSet := hchild_s
    central_child := hcent_c
    central_form := hcent_f
    central_owner := hcent_o
    child_form := hchild_f
    base_form := hbase_f
    base_original := hbase_o
    catalogue_form_injective := hcat_f_inj
    parentSide := emcdParentSide g s l
    parentSide_injective := hps_inj
    parentSide_bijective := hps_bij
    parentSide_cyclic := hps_cyc
    parent_side_geometry := hps_geom
    marked_from_setup := hmark_setup
    marked_rule_nonlarge := hmark_nonl
    marked_rule_large := hmark_l
    partner_spec := hpart
    edge_spec := hedge
    edgeTypes_spec := hedge_t
    positive_eq := hpos
    outerList_mem := hout_mem
    outerList_nodup := hout_nodup
    outerList_sorted := hout_sort
    N_eq := hN
    Qmax_eq := hQmax
    rankBound_ge := hrank_ge
    rankBound_is_max := hrank_max
    print_from_routing := hpr_rout
    print_injective := hpr_inj
    print_cyclic := hpr_cyc
    print_inner := hpr_in
    print_small := hpr_sm
    special_small := hsp_sm
    special_unique := hsp_uniq
    special_contact := hsp_cont
    special_print := hsp_pr
    path_from_routing := hpa_rout
    path_head := hpa_head
    path_last := hpa_last
    path_chain := hpa_chain
    path_owner := hpa_own
    path_partner := hpa_part
    path_trivial := hpa_triv
    fifth_path := hpa_5
    path_inner := hpa_in
    path_marked := hpa_mark
    path_not_central := hpa_ncent
    path_penultimate := hpa_pen
    path_nodup := hpa_nodup
    path_disjoint := hpa_disj }⟩

private lemma emcg_g1_shared_inner
    (D : MacroData P) (tmpl : existsMacroCertificate_TemplateData D)
    {α : D.Q.Form} {t u : D.Typ} (ht : D.owner t = α) (hu : D.owner u = α)
    (hshare : SharesSide (D.childTile t) (D.childTile u)) :
    ∃ (i : D.Side t) (j : D.Side u),
      D.IsInner (D.occ t i) ∧ D.occSide (D.occ t i) = D.occSide (D.occ u j) := by
  rcases hshare with ⟨htu, e, ⟨i, hi⟩, ⟨j, hj⟩⟩
  refine ⟨i, j, ?_, hi.trans hj.symm⟩
  intro hout
  have htmem : D.childTile t ∈ (D.σ.rule α).tiles := by
    rw [tmpl.rule_eq α]
    exact ⟨t, ht, rfl⟩
  have humem : D.childTile u ∈ (D.σ.rule α).tiles := by
    rw [tmpl.rule_eq α]
    exact ⟨u, hu, rfl⟩
  let q := midpoint ℝ ((D.childTile t).vertex i)
    ((D.childTile t).vertex (finRotate _ i))
  have hqopen : q ∈ openSegment ℝ ((D.childTile t).vertex i)
      ((D.childTile t).vertex (finRotate _ i)) := by
    apply mem_openSegment_of_ne_left_right
    · intro h
      exact tile_vertex_ne_next (D.childTile t) i (by
        dsimp [q] at h
        rw [eq_comm, midpoint_eq_left_iff] at h
        exact h)
    · intro h
      exact tile_vertex_ne_next (D.childTile t) i (by
        dsimp [q] at h
        rw [eq_comm, midpoint_eq_right_iff] at h
        exact h)
    · exact midpoint_mem_segment _ _
  obtain ⟨r, hr, σ, -, hlocal⟩ := two_sides (D.σ.rule α).disjoint
    htmem humem htu i j (hj.trans hi.symm) hqopen
  have hqint : q ∈ interior (support (D.σ.rule α).tiles) := by
    rw [mem_interior_iff_mem_nhds]
    apply Filter.mem_of_superset (Metric.ball_mem_nhds q hr)
    intro x hx
    by_cases hnonneg : 0 ≤ σ * jcr
        ((D.childTile t).vertex (finRotate _ i) - (D.childTile t).vertex i)
        (x - (D.childTile t).vertex i)
    · exact carrier_subset_support htmem ((hlocal x hx).2.2 hnonneg)
    · exact carrier_subset_support humem
        (interior_subset ((hlocal x hx).2.1 (lt_of_not_ge hnonneg)))
  have hqfront : q ∈ D.macroBoundary α := by
    have hqfront' : q ∈ D.macroBoundary (D.owner t) := by
      apply hout
      rw [MacroData.occSide, tile_side_eq]
      exact openSegment_subset_segment ℝ _ _ hqopen
    exact ht ▸ hqfront'
  rw [D.σ.support_eq α] at hqint
  exact hqfront.2 hqint

private lemma emcg_g1_connected
    (D : MacroData P) (tmpl : existsMacroCertificate_TemplateData D) :
    ∀ α, (D.innerGraph α).Connected := by
  classical
  intro α
  let V := {t : D.Typ // D.owner t = α}
  have hnonempty : Nonempty V := by
    obtain ⟨x, hx⟩ := (D.Q.disk α).interior_nonempty
    have hx' : D.σ.θ • x ∈ support (D.σ.rule α).tiles := by
      rw [D.σ.support_eq α]
      exact smul_mem_smul_set (interior_subset hx)
    obtain ⟨A, hA, -⟩ := mem_support_iff'.1 hx'
    rw [tmpl.rule_eq α] at hA
    obtain ⟨t, ht, -⟩ := hA
    exact ⟨⟨t, ht⟩⟩
  letI : Nonempty V := hnonempty
  refine ⟨?_⟩
  intro a b
  rw [SimpleGraph.reachable_iff_reflTransGen]
  have hamem : D.childTile a.1 ∈ (D.σ.rule α).tiles := by
    rw [tmpl.rule_eq α]
    exact ⟨a.1, a.2, rfl⟩
  have hbmem : D.childTile b.1 ∈ (D.σ.rule α).tiles := by
    rw [tmpl.rule_eq α]
    exact ⟨b.1, b.2, rfl⟩
  have hpre : IsPreconnected (interior (support (D.σ.rule α).tiles)) := by
    rw [D.σ.support_eq α]
    exact (emcgScaleDisk (D.Q.disk α) D.σ.θ
      (ne_of_gt (zero_lt_one.trans D.σ.one_lt))).interior_pathConnected.isConnected.isPreconnected
  have hchain := existsRoutingAfterPower_step5_discretize_step1_route_step1_perturb_step3_dualChain
    (D.σ.rule α).disjoint (tmpl.template_sts α) (Set.Subset.rfl)
    (D.σ.rule α).finite isOpen_interior hpre interior_subset
    hamem hbmem
    (by
      obtain ⟨x, hx⟩ := (tileDisk (D.childTile a.1)).interior_nonempty
      exact ⟨x, interior_mono (carrier_subset_support hamem) hx, hx⟩)
    (by
      obtain ⟨x, hx⟩ := (tileDisk (D.childTile b.1)).interior_nonempty
      exact ⟨x, interior_mono (carrier_subset_support hbmem) hx, hx⟩)
  have hlift : ∀ (A B : PlacedTile D.Q),
      Relation.ReflTransGen
        (fun X Y => X ∈ (D.σ.rule α).tiles ∧ Y ∈ (D.σ.rule α).tiles ∧ SharesSide X Y) A B →
      ∀ (x y : V), D.childTile x.1 = A → D.childTile y.1 = B →
        Relation.ReflTransGen (D.innerGraph α).Adj x y := by
    intro A B h
    induction h with
    | refl =>
        intro x y hx hy
        have htile : D.childTile x.1 = D.childTile y.1 := hx.trans hy.symm
        have hform : D.form x.1 = D.form y.1 :=
          congrArg (fun Z : PlacedTile D.Q => Z.form) htile
        have hanchor : D.anchor x.1 = D.anchor y.1 :=
          congrArg (fun Z : PlacedTile D.Q => Z.anchor) htile
        have hxy : x.1 = y.1 := tmpl.type_injective x.1 y.1
          (x.2.trans y.2.symm) hform hanchor
        have hxy' : x = y := Subtype.ext hxy
        subst y
        exact Relation.ReflTransGen.refl
    | @tail B C hAB hBC ih =>
        intro x z hx hz
        rw [tmpl.rule_eq α] at hBC
        rcases hBC.1 with ⟨y, hyown, hy⟩
        let y' : V := ⟨y, hyown⟩
        have hy' : D.childTile y = B := by
          simpa only [MacroData.childTile] using hy
        have hshare : SharesSide (D.childTile y) (D.childTile z.1) := by
          rw [hy', hz]
          exact hBC.2.2
        have hadj : (D.innerGraph α).Adj y' z := by
          obtain ⟨i, j, hi, hij⟩ := emcg_g1_shared_inner D tmpl hyown z.2 hshare
          refine ⟨?_, Or.inl ⟨i, j, hi, hij⟩⟩
          intro heq
          exact hshare.1 (congrArg (fun w : V => D.childTile w.1) heq)
        exact Relation.ReflTransGen.tail (ih x y' hx hy') hadj
  exact hlift _ _ hchain a b rfl rfl

private lemma emcg_g1_three_le
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) :
    ∀ α, 3 ≤ Nat.card {t : cd.D.Typ // cd.D.owner t = α} := by
  classical
  intro α
  let j0 : Fin (4 * s.setup.N (cd.baseForm α)) := ⟨0, by
    have := s.setup.N_two (cd.baseForm α)
    omega⟩
  let j1 : Fin (4 * s.setup.N (cd.baseForm α)) := ⟨1, by
    have := s.setup.N_two (cd.baseForm α)
    omega⟩
  obtain ⟨X0, hX0, hX0c, hX0j⟩ :=
    s.setup.piece_child l (cd.baseForm α) cd.l_pos j0
  obtain ⟨X1, hX1, hX1c, hX1j⟩ :=
    s.setup.piece_child l (cd.baseForm α) cd.l_pos j1
  have hX01 : X0 ≠ X1 := by
    intro h
    subst X1
    have heq : ((s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes.piece j0).faces =
        ((s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes.piece j1).faces :=
      hX0j.symm.trans hX1j
    obtain ⟨x, hx⟩ :=
      ((s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes.piece j0).disk.interior_nonempty
    have hx' : x ∈ support
        ((s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes.piece j0).faces := by
      rw [← ((s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes.piece j0).carrier_eq]
      exact interior_subset hx
    obtain ⟨A, hA, -⟩ := mem_support_iff'.1 hx'
    exact sw3_piece_ne (s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes
      (by
        intro hj
        have := congrArg Fin.val hj
        simp [j0, j1] at this)
      hA (heq ▸ hA)
  obtain ⟨tc, htc, htcc⟩ := (cd.child_bijective α).2.2
    (s.setup.central_mem l (cd.baseForm α))
  obtain ⟨t0, ht0, ht0c⟩ := (cd.child_bijective α).2.2 hX0
  obtain ⟨t1, ht1, ht1c⟩ := (cd.child_bijective α).2.2 hX1
  have hct0 : tc ≠ t0 := by
    intro h
    subst t0
    exact hX0c (ht0c.symm.trans htcc)
  have hct1 : tc ≠ t1 := by
    intro h
    subst t1
    exact hX1c (ht1c.symm.trans htcc)
  have ht01 : t0 ≠ t1 := by
    intro h
    subst t1
    exact hX01 (ht0c.symm.trans ht1c)
  let f : Fin 3 → {t : cd.D.Typ // cd.D.owner t = α} := fun i =>
    Fin.cases ⟨tc, htc⟩ (fun i => Fin.cases ⟨t0, ht0⟩ (fun _ => ⟨t1, ht1⟩) i) i
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [f, Fin.cases_zero, Fin.cases_succ] at hij ⊢
    · exact (hct0 (congrArg Subtype.val hij)).elim
    · exact (hct1 (congrArg Subtype.val hij)).elim
    · exact (hct0 (congrArg Subtype.val hij).symm).elim
    · exact (ht01 (congrArg Subtype.val hij)).elim
    · exact (hct1 (congrArg Subtype.val hij).symm).elim
    · exact (ht01 (congrArg Subtype.val hij).symm).elim
  simpa using Nat.card_le_card_of_injective f hf

private lemma emcg_g1_side_unique
    (D : MacroData P) (tmpl : existsMacroCertificate_TemplateData D)
    (o o' : D.SideOcc) (ho : D.IsInner o) (hown : D.owner o'.1 = D.owner o.1)
    (hne : o'.1 ≠ o.1) (hside : D.occSide o' = D.occSide o)
    (hpartner : (D.partner o).1 ≠ o.1 ∧
      D.owner (D.partner o).1 = D.owner o.1 ∧
      D.occSide (D.partner o) = D.occSide o) : o' = D.partner o := by
  have _ := ho
  let α := D.owner o.1
  have homem : D.childTile o.1 ∈ (D.σ.rule α).tiles := by
    rw [tmpl.rule_eq α]
    exact ⟨o.1, rfl, rfl⟩
  have hopmem : D.childTile (D.partner o).1 ∈ (D.σ.rule α).tiles := by
    rw [tmpl.rule_eq α]
    exact ⟨(D.partner o).1, hpartner.2.1, rfl⟩
  have ho'mem : D.childTile o'.1 ∈ (D.σ.rule α).tiles := by
    rw [tmpl.rule_eq α]
    exact ⟨o'.1, hown, rfl⟩
  have hop_ne : D.childTile o.1 ≠ D.childTile (D.partner o).1 := by
    intro htile
    apply hpartner.1
    apply tmpl.type_injective
    · exact hpartner.2.1
    · exact congrArg (fun A : PlacedTile D.Q => A.form) htile.symm
    · exact congrArg (fun A : PlacedTile D.Q => A.anchor) htile.symm
  have ho'_ne : D.childTile o.1 ≠ D.childTile o'.1 := by
    intro htile
    apply hne
    symm
    apply tmpl.type_injective
    · exact hown.symm
    · exact congrArg (fun A : PlacedTile D.Q => A.form) htile
    · exact congrArg (fun A : PlacedTile D.Q => A.anchor) htile
  have htile := side_partner_unique (D.σ.rule α).disjoint homem hopmem ho'mem
    hop_ne ho'_ne o.2 (D.partner o).2 o'.2 hpartner.2.2 hside
  have hform : D.form (D.partner o).1 = D.form o'.1 :=
    congrArg (fun A : PlacedTile D.Q => A.form) htile
  have hanchor : D.anchor (D.partner o).1 = D.anchor o'.1 :=
    congrArg (fun A : PlacedTile D.Q => A.anchor) htile
  have htyp : (D.partner o).1 = o'.1 := tmpl.type_injective _ _
    (hpartner.2.1.trans hown.symm) hform hanchor
  have hsidep : D.occSide o' = D.occSide (D.partner o) :=
    hside.trans hpartner.2.2.symm
  cases o' with
  | mk t' i' =>
      cases hp : D.partner o with
      | mk p ip =>
          simp only [hp] at htyp hsidep ⊢
          subst t'
          have hinj : Function.Injective (D.childTile p).vertex := by
            intro a b hab
            apply (D.Q.disk (D.form p)).vertex_injective
            simpa [PlacedTile.vertex] using hab
          have hii : i' = ip := by
            apply cyc_seg_inj (D.Q.disk (D.form p)).three_le hinj
            simpa only [MacroData.occSide, tile_side_eq] using hsidep
          subst i'
          rfl

/-- Step 5 of `lem:certificate-exists`, (G1): "Disk cellulations with at least the centre and its
ring have connected inner-side duals and at least three children"; every child of a retained
template has an inner side (a child with outer sides only would be the whole template), an inner
side has exactly two owners (`template_sts`), and the interface identifiers are those of
`CertData` (`partner_spec`, `edge_spec`, `edgeTypes_spec`). -/
private lemma existsMacroCertificate_seed2_routing_step4_g1 (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) :
    existsMacroCertificate_G1Data cd.D := by
  classical
  have hconnected : ∀ α, (cd.D.innerGraph α).Connected :=
    emcg_g1_connected cd.D cd.tmpl
  have hthree : ∀ α, 3 ≤ Nat.card {t : cd.D.Typ // cd.D.owner t = α} :=
    emcg_g1_three_le τ g s l routing cd
  have hinner : ∀ t, ∃ i, cd.D.IsInner (cd.D.occ t i) := by
    intro t
    let V := {u : cd.D.Typ // cd.D.owner u = cd.D.owner t}
    have hcard : 1 < Nat.card V := lt_of_lt_of_le (by omega) (hthree (cd.D.owner t))
    letI : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp hcard
    obtain ⟨u, htu⟩ := exists_ne (⟨t, rfl⟩ : V)
    have hreach := hconnected (cd.D.owner t) (⟨t, rfl⟩ : V) u
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨v, hadj, -⟩
    · exact (htu heq.symm).elim
    · rcases hadj with ⟨-, hadj | hadj⟩
      · rcases hadj with ⟨i, j, hi, -⟩
        exact ⟨i, hi⟩
      · rcases hadj with ⟨i, j, hi, hside⟩
        refine ⟨j, ?_⟩
        intro hout
        apply hi
        intro x hx
        rw [hside] at hx
        rw [v.2]
        exact hout hx
  have hpartner_inner : ∀ o : cd.D.SideOcc, cd.D.IsInner o →
      cd.D.IsInner (cd.D.partner o) := by
    intro o ho hout
    apply ho
    intro x hx
    have hp := cd.partner_spec o ho
    rw [← hp.2.2] at hx
    have hown := hp.2.1
    exact hown ▸ hout hx
  have hside_unique : ∀ o o' : cd.D.SideOcc, cd.D.IsInner o →
      cd.D.owner o'.1 = cd.D.owner o.1 → o'.1 ≠ o.1 →
      cd.D.occSide o' = cd.D.occSide o → o' = cd.D.partner o := by
    intro o o' ho hown hne hside
    exact emcg_g1_side_unique cd.D cd.tmpl o o' ho hown hne hside (cd.partner_spec o ho)
  have hpartner_partner : ∀ o : cd.D.SideOcc, cd.D.IsInner o →
      cd.D.partner (cd.D.partner o) = o := by
    intro o ho
    have hp := cd.partner_spec o ho
    have hpi := hpartner_inner o ho
    have hpp := cd.partner_spec (cd.D.partner o) hpi
    symm
    apply hside_unique (cd.D.partner o) o hpi
    · exact hp.2.1.symm
    · exact hp.1.symm
    · exact hp.2.2.symm
  refine {
    connected := hconnected
    three_le := hthree
    inner_side := hinner
    partner := cd.partner_spec
    partner_partner := hpartner_partner
    side_unique := hside_unique
    edge_partner := ?_
    edge_unique := ?_
    edgeTypes := cd.edgeTypes_spec }
  · intro o ho
    exact ((cd.edge_spec o (cd.D.partner o) ho (hpartner_inner o ho)).2 (Or.inr rfl)).symm
  · intro o o' ho ho' hedge
    exact (cd.edge_spec o o' ho ho').1 hedge

/-- Tiles incident with one boundary point of a finite polygonal cellulation form a side-adjacent
fan.  The shared side at every step has that boundary point as an endpoint. -/
private lemma emcg_boundary_fan {Q : Protoset} (S : Patch Q) (hsts : SideToSideSet S.tiles)
    (B : PolygonalDisk) {a : ℝ} (ha : 0 < a)
    (hsupport : support S.tiles = a • B.carrier) {z : Pt}
    (hz : z ∈ frontier (a • B.carrier)) {A₀ A₁ : PlacedTile Q}
    (hA₀ : A₀ ∈ S.tiles) (hA₁ : A₁ ∈ S.tiles)
    (hzA₀ : z ∈ A₀.carrier) (hzA₁ : z ∈ A₁.carrier) :
    Relation.ReflTransGen
      (fun X Y : PlacedTile Q =>
        X ∈ S.tiles ∧ z ∈ X.carrier ∧ Y ∈ S.tiles ∧ z ∈ Y.carrier ∧ X ≠ Y ∧
          ∃ i j, Y.side j = X.side i ∧
            (X.vertex i = z ∨ X.vertex (finRotate _ i) = z)) A₀ A₁ := by
  classical
  let G : Set (PlacedTile Q) := {X ∈ S.tiles | z ∈ X.carrier}
  have hGfin : G.Finite := S.finite.subset fun X hX => hX.1
  let K : Set (Set Pt) :=
    {e | ∃ X ∈ G, ∃ i : Fin (Q.disk X.form).n, z ∉ X.side i ∧ e = X.side i}
  have hKfin : K.Finite := by
    apply (hGfin.biUnion fun X _ => Set.finite_range X.side).subset
    rintro e ⟨X, hX, i, -, rfl⟩
    exact Set.mem_biUnion hX ⟨i, rfl⟩
  have hKclosed : IsClosed (⋃₀ K) := by
    rw [Set.sUnion_eq_biUnion]
    apply hKfin.isClosed_biUnion
    rintro e ⟨X, -, i, -, rfl⟩
    rw [tile_side_eq]
    exact (isCompact_segment_pt _ _).isClosed
  have hzK : z ∉ ⋃₀ K := by
    rintro ⟨e, ⟨X, hX, i, hzi, rfl⟩, hze⟩
    exact hzi hze
  obtain ⟨δ, hδ, hδK⟩ := Metric.isOpen_iff.1 hKclosed.isOpen_compl z hzK
  obtain ⟨r₀, hr₀, hlocal⟩ :=
    existsRoutingAfterPower_step5_discretize_step1_route_step1_perturb_step1_localConnScaled
      B ha hz
  obtain ⟨ρ, hρ, hρinc⟩ :=
    existsRoutingAfterPower_step5_discretize_step1_route_step1_perturb_step2_localNbhd
      S.finite z
  let r := min r₀ (min ρ δ)
  have hr : 0 < r := lt_min hr₀ (lt_min hρ hδ)
  let W := Metric.ball z r ∩ interior (support S.tiles)
  have hWo : IsOpen W := Metric.isOpen_ball.inter isOpen_interior
  have hWc : IsPreconnected W := by
    simpa only [W, hsupport] using hlocal r hr (min_le_left _ _)
  have hWG : W ⊆ support G := by
    rintro x ⟨hxb, hxi⟩
    obtain ⟨X, hXS, hxX⟩ := mem_support_iff'.1 (interior_subset hxi)
    have hzX := hρinc x (Metric.ball_subset_ball
      ((min_le_right r₀ (min ρ δ)).trans (min_le_left ρ δ)) hxb) X hXS hxX
    exact carrier_subset_support (show X ∈ G from ⟨hXS, hzX⟩) hxX
  have meets (X : PlacedTile Q) (hXS : X ∈ S.tiles) (hzX : z ∈ X.carrier) :
      (W ∩ interior X.carrier).Nonempty := by
    have hzcl : z ∈ closure (interior X.carrier) := by
      rw [tile_regular]
      exact hzX
    obtain ⟨x, hxi, hzx⟩ := Metric.mem_closure_iff.1 hzcl r hr
    have hxb : x ∈ Metric.ball z r := by
      rw [Metric.mem_ball, dist_comm]
      exact hzx
    have hxS : x ∈ interior (support S.tiles) :=
      interior_mono (carrier_subset_support hXS) hxi
    exact ⟨x, ⟨hxb, hxS⟩, hxi⟩
  let R := fun X Y : PlacedTile Q =>
    X ∈ S.tiles ∧ z ∈ X.carrier ∧ Y ∈ S.tiles ∧ z ∈ Y.carrier ∧
      X ≠ Y ∧ ∃ i j, Y.side j = X.side i ∧
      (X.vertex i = z ∨ X.vertex (finRotate _ i) = z)
  set C := {X ∈ G | Relation.ReflTransGen R A₀ X}
  by_contra hA₁C
  set D := G \ C
  have hA₀C : A₀ ∈ C := ⟨⟨hA₀, hzA₀⟩, Relation.ReflTransGen.refl⟩
  have hA₁D : A₁ ∈ D := by
    refine ⟨⟨hA₁, hzA₁⟩, fun h => hA₁C ?_⟩
    simpa only [R] using h.2
  have hCD : ∀ X ∈ C, ∀ Y ∈ D, ∀ p ∈ W, p ∈ X.carrier → p ∈ Y.carrier →
      p ∈ gVerts G := by
    intro X hX Y hY p hpW hpX hpY
    by_contra hpv
    have hXY : X ≠ Y := by
      rintro rfl
      exact hY.2 hX
    have hpXi : p ∉ interior X.carrier := fun h =>
      interior_not_mem_other S.disjoint hX.1.1 hY.1.1 hXY h hpY
    have hpf : p ∈ frontier X.carrier := by
      rw [mem_frontier_iff_of_closed (tile_isClosed X)]
      exact ⟨hpX, hpXi⟩
    rw [tile_frontier_eq, Set.mem_iUnion] at hpf
    obtain ⟨i, hpi⟩ := hpf
    have hpo : p ∈ openSegment ℝ (X.vertex i) (X.vertex (finRotate _ i)) := by
      rw [tile_side_eq] at hpi
      apply mem_openSegment_of_ne_left_right
      · intro h
        exact hpv (Set.mem_biUnion hX.1 ⟨i, h⟩)
      · intro h
        exact hpv (Set.mem_biUnion hX.1 ⟨_, h⟩)
      · exact hpi
    obtain ⟨j, hj⟩ := tile_partner S.disjoint hsts hX.1.1 hY.1.1 hXY i hpo hpY
      (fun hv => hpv (Set.mem_biUnion hY.1 hv))
    have hzi : z ∈ X.side i := by
      by_contra hnot
      apply hδK (Metric.ball_subset_ball
        ((min_le_right r₀ (min ρ δ)).trans (min_le_right ρ δ)) hpW.1)
      exact ⟨X.side i, ⟨X, hX.1, i, hnot, rfl⟩, hpi⟩
    have hz_end : X.vertex i = z ∨ X.vertex (finRotate _ i) = z := by
      by_contra hend
      push_neg at hend
      have hzo : z ∈ openSegment ℝ (X.vertex i) (X.vertex (finRotate _ i)) := by
        rw [tile_side_eq] at hzi
        exact mem_openSegment_of_ne_left_right hend.1 hend.2 hzi
      obtain ⟨ε, hε, σ, -, htwo⟩ :=
        two_sides S.disjoint hX.1.1 hY.1.1 hXY i j hj hzo
      have hzint : z ∈ interior (support S.tiles) := by
        rw [mem_interior_iff_mem_nhds]
        apply Filter.mem_of_superset (Metric.ball_mem_nhds z hε)
        intro x hx
        by_cases hsign : 0 ≤ σ * jcr
            (X.vertex (finRotate _ i) - X.vertex i) (x - X.vertex i)
        · exact carrier_subset_support hX.1.1 ((htwo x hx).2.2 hsign)
        · exact carrier_subset_support hY.1.1
            (interior_subset ((htwo x hx).2.1 (lt_of_not_ge hsign)))
      rw [hsupport] at hzint
      exact hz.2 hzint
    apply hY.2
    refine ⟨hY.1, Relation.ReflTransGen.tail hX.2 ?_⟩
    exact ⟨hX.1.1, hX.1.2, hY.1.1, hY.1.2, hXY, i, j, hj, hz_end⟩
  have hCfin : C.Finite := hGfin.subset fun X hX => hX.1
  have hDfin : D.Finite := hGfin.subset fun X hX => hX.1
  apply open_minus_finite_split (W := W) (O1 := W \ support D) (O2 := W \ support C)
    (Z := gVerts G) hWo hWc (hWo.sdiff (support_isClosed hDfin))
      (hWo.sdiff (support_isClosed hCfin))
  · rw [Set.disjoint_left]
    rintro x ⟨hxW, hxD⟩ ⟨-, hxC⟩
    obtain ⟨X, hX, hxX⟩ := mem_support_iff'.1 (hWG hxW)
    by_cases hXC : X ∈ C
    · exact hxC (carrier_subset_support hXC hxX)
    · exact hxD (carrier_subset_support (show X ∈ D from ⟨hX, hXC⟩) hxX)
  · exact gVerts_finite hGfin
  · intro x hxW
    by_cases hxD : x ∈ support D
    · by_cases hxC : x ∈ support C
      · obtain ⟨X, hX, hxX⟩ := mem_support_iff'.1 hxC
        obtain ⟨Y, hY, hxY⟩ := mem_support_iff'.1 hxD
        exact Or.inr (hCD X hX Y hY x hxW hxX hxY)
      · exact Or.inl (Or.inr ⟨hxW, hxC⟩)
    · exact Or.inl (Or.inl ⟨hxW, hxD⟩)
  · obtain ⟨x, hxW, hxA₀⟩ := meets A₀ hA₀ hzA₀
    refine ⟨x, hxW, hxW, ?_⟩
    intro hxD
    obtain ⟨Y, hY, hxY⟩ := mem_support_iff'.1 hxD
    have hne : A₀ ≠ Y := by
      rintro rfl
      exact hY.2 hA₀C
    exact interior_not_mem_other S.disjoint hA₀ hY.1.1 hne hxA₀ hxY
  · obtain ⟨x, hxW, hxA₁⟩ := meets A₁ hA₁ hzA₁
    refine ⟨x, hxW, hxW, ?_⟩
    intro hxC
    obtain ⟨Y, hY, hxY⟩ := mem_support_iff'.1 hxC
    have hne : A₁ ≠ Y := by
      rintro rfl
      exact hA₁D.2 hY
    exact interior_not_mem_other S.disjoint hA₁ hY.1.1 hne hxA₁ hxY

/-- The geometric fan chain at a macroboundary point lifts to reachability in the certificate's
belt graph. -/
private lemma emcg_boundary_fan_reachable
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) (α : cd.D.Q.Form)
    {z : Pt} (hz : z ∈ cd.D.macroBoundary α) (t u : cd.D.Typ)
    (ht : cd.D.owner t = α) (hu : cd.D.owner u = α)
    (hzt : z ∈ (cd.D.childTile t).carrier) (hzu : z ∈ (cd.D.childTile u).carrier) :
    (cd.D.beltGraph α).Reachable
      ⟨t, ht, z, hzt, hz⟩ ⟨u, hu, z, hzu, hz⟩ := by
  classical
  let bt : {v : cd.D.Typ // cd.D.IsBeltType α v} := ⟨t, ht, z, hzt, hz⟩
  let bu : {v : cd.D.Typ // cd.D.IsBeltType α v} := ⟨u, hu, z, hzu, hz⟩
  let R := fun X Y : PlacedTile cd.D.Q =>
    X ∈ (cd.D.σ.rule α).tiles ∧ z ∈ X.carrier ∧
      Y ∈ (cd.D.σ.rule α).tiles ∧ z ∈ Y.carrier ∧ X ≠ Y ∧
        ∃ i j, Y.side j = X.side i ∧
          (X.vertex i = z ∨ X.vertex (finRotate _ i) = z)
  have fan : Relation.ReflTransGen R (cd.D.childTile t) (cd.D.childTile u) := by
    apply emcg_boundary_fan (cd.D.σ.rule α) (cd.tmpl.template_sts α)
      (cd.D.Q.disk α) (a := cd.D.σ.θ) (lt_trans zero_lt_one cd.D.σ.one_lt)
    · exact cd.D.σ.support_eq α
    · exact hz
    · rw [cd.tmpl.rule_eq]
      exact ⟨t, ht, rfl⟩
    · rw [cd.tmpl.rule_eq]
      exact ⟨u, hu, rfl⟩
    · exact hzt
    · exact hzu
  have edge {x y : cd.D.Typ} (hx : cd.D.owner x = α) (hy : cd.D.owner y = α)
      (hrel : R (cd.D.childTile x) (cd.D.childTile y)) :
      (cd.D.beltGraph α).Adj
        ⟨x, hx, z, hrel.2.1, hz⟩ ⟨y, hy, z, hrel.2.2.2.1, hz⟩ := by
    obtain ⟨hxin, hzx, hyin, hzy, hxy, i, j, hside, hend⟩ := hrel
    have hne : x ≠ y := fun h => hxy (congrArg cd.D.childTile h)
    have hinner : cd.D.IsInner (cd.D.occ x i) := by
      intro houter
      let q := midpoint ℝ ((cd.D.childTile x).vertex i)
        ((cd.D.childTile x).vertex (finRotate _ i))
      have hqo : q ∈ openSegment ℝ ((cd.D.childTile x).vertex i)
          ((cd.D.childTile x).vertex (finRotate _ i)) := by
        apply mem_openSegment_of_ne_left_right
        · intro h
          exact tile_vertex_ne_next (cd.D.childTile x) i
            ((midpoint_eq_left_iff ℝ).mp h.symm)
        · intro h
          exact tile_vertex_ne_next (cd.D.childTile x) i
            ((midpoint_eq_right_iff ℝ).mp h.symm)
        · exact midpoint_mem_segment _ _
      obtain ⟨ε, hε, σ, -, htwo⟩ :=
        two_sides (cd.D.σ.rule α).disjoint hxin hyin hxy i j hside hqo
      have hqint : q ∈ interior (support (cd.D.σ.rule α).tiles) := by
        rw [mem_interior_iff_mem_nhds]
        apply Filter.mem_of_superset (Metric.ball_mem_nhds q hε)
        intro w hw
        by_cases hsign : 0 ≤ σ * jcr
            ((cd.D.childTile x).vertex (finRotate _ i) - (cd.D.childTile x).vertex i)
            (w - (cd.D.childTile x).vertex i)
        · exact carrier_subset_support hxin ((htwo w hw).2.2 hsign)
        · exact carrier_subset_support hyin
            (interior_subset ((htwo w hw).2.1 (lt_of_not_ge hsign)))
      have hqside : q ∈ cd.D.occSide (cd.D.occ x i) := by
        rw [MacroData.occSide, tile_side_eq]
        exact openSegment_subset_segment ℝ _ _ hqo
      have hqfront := houter hqside
      rw [MacroData.macroBoundary, MacroData.macroRegion, hx,
        ← cd.D.σ.support_eq α] at hqfront
      exact hqfront.2 hqint
    have hboundary : cd.D.IsBoundary (cd.D.occ x i) := by
      refine ⟨hinner, ?_⟩
      rcases hend with hend | hend
      · left
        rw [show cd.D.occStart (cd.D.occ x i) = z by
          simpa only [MacroData.occStart, MacroData.childTile, PlacedTile.vertex] using hend,
          hx]
        exact hz
      · right
        rw [show cd.D.occEnd (cd.D.occ x i) = z by
          simpa only [MacroData.occEnd, MacroData.childTile, PlacedTile.vertex] using hend,
          hx]
        exact hz
    rw [MacroData.beltGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨i, j, hboundary, ?_⟩⟩
    · intro h
      exact hne (congrArg Subtype.val h)
    · exact hside.symm
  have key : ∀ {X Y : PlacedTile cd.D.Q}, Relation.ReflTransGen R X Y →
      ∀ (x y : cd.D.Typ) (hx : cd.D.owner x = α) (hy : cd.D.owner y = α)
        (hchildx : cd.D.childTile x = X) (hchildy : cd.D.childTile y = Y)
        (hzx : z ∈ (cd.D.childTile x).carrier) (hzy : z ∈ (cd.D.childTile y).carrier),
        (cd.D.beltGraph α).Reachable
          ⟨x, hx, z, hzx, hz⟩ ⟨y, hy, z, hzy, hz⟩ := by
    intro X Y hchain
    induction hchain with
    | refl =>
        intro x y hx hy hchildx hchildy hzx hzy
        have htile : cd.D.childTile x = cd.D.childTile y := hchildx.trans hchildy.symm
        have hform : cd.D.form x = cd.D.form y := congrArg PlacedTile.form htile
        have hanchor : cd.D.anchor x = cd.D.anchor y := congrArg PlacedTile.anchor htile
        have hxy := cd.tmpl.type_injective x y (hx.trans hy.symm) hform hanchor
        subst y
        exact SimpleGraph.Reachable.rfl
    | @tail Y Z _ hYZ ih =>
        intro x zt hx hzt hchildx hchildz hzx hzzt
        have hYmem : Y ∈ (cd.D.σ.rule α).tiles := hYZ.1
        rw [cd.tmpl.rule_eq] at hYmem
        obtain ⟨y, hy, hchildy⟩ := hYmem
        change cd.D.owner y = α at hy
        change cd.D.childTile y = Y at hchildy
        have hzy : z ∈ (cd.D.childTile y).carrier := by
          rw [hchildy]
          exact hYZ.2.1
        have hreach := ih x y hx hy hchildx hchildy hzx hzy
        have hrel : R (cd.D.childTile y) (cd.D.childTile zt) := by
          simpa only [hchildy, hchildz] using hYZ
        exact hreach.trans (edge hy hzt hrel).reachable
  exact key fan t u ht hu rfl rfl hzt hzu

/-- Step 6 of `lem:certificate-exists`, (G2): "Around the macroboundary, consecutive boundary
faces are connected through the finite fan at each boundary vertex ... Faces touching the
boundary only at a vertex must be included in this fan"; every belt type has a boundary side
because it is not the whole macrotile; "The retained centre is strictly interior"
(`RoutingSetup.clearance`). -/
private lemma existsMacroCertificate_seed2_routing_step5_g2_aux_belt_connected
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) :
    ∀ _α, (cd.D.beltGraph _α).Connected := by
  classical
  intro α
  have hθ : 0 < cd.D.σ.θ := lt_trans zero_lt_one cd.D.σ.one_lt
  have hfront_pre : IsPreconnected (cd.D.macroBoundary α) := by
    have hloop := pgLoop_isLoopParam (cd.D.Q.disk α)
    have hpre : IsPreconnected (frontier (cd.D.Q.disk α).carrier) := by
      rw [← hloop.2.2.2]
      exact isPreconnected_Ico.image _ hloop.1.continuousOn
    rw [MacroData.macroBoundary, MacroData.macroRegion,
      existsRoutingAfterPower_step2_ports_step1_intra_step2_clearance_frontier_smul hθ.ne',
      ← Set.image_smul]
    exact hpre.image _ (continuous_const_smul cd.D.σ.θ).continuousOn
  have belt_nonempty : Nonempty {t : cd.D.Typ // cd.D.IsBeltType α t} := by
    let i : Fin (cd.D.Q.disk α).n :=
      ⟨0, by have := (cd.D.Q.disk α).three_le; omega⟩
    let z := cd.D.σ.θ • (cd.D.Q.disk α).vertex i
    have hz : z ∈ cd.D.macroBoundary α := by
      rw [MacroData.macroBoundary, MacroData.macroRegion,
        existsRoutingAfterPower_step2_ports_step1_intra_step2_clearance_frontier_smul hθ.ne']
      exact smul_mem_smul_set (pd_segment_subset_frontier (cd.D.Q.disk α) i
        (left_mem_segment ℝ _ _))
    have hzsupport : z ∈ support (cd.D.σ.rule α).tiles := by
      rw [cd.D.σ.support_eq α]
      exact pd_frontier_subset_carrier (emcgScaleDisk (cd.D.Q.disk α) cd.D.σ.θ hθ.ne') hz
    obtain ⟨A, hA, hzA⟩ := mem_support_iff'.1 hzsupport
    rw [cd.tmpl.rule_eq] at hA
    obtain ⟨t, ht, rfl⟩ := hA
    exact ⟨⟨t, ht, z, hzA, hz⟩⟩
  refine { preconnected := ?_, nonempty := belt_nonempty }
  intro u v
  by_contra huv
  let C : Set {t : cd.D.Typ // cd.D.IsBeltType α t} :=
    {w | (cd.D.beltGraph α).Reachable u w}
  let E : Set {t : cd.D.Typ // cd.D.IsBeltType α t} := Cᶜ
  let KC : Set Pt := ⋃ w : {t : cd.D.Typ // cd.D.IsBeltType α t},
    ⋃ _ : w ∈ C, (cd.D.childTile w.1).carrier ∩ cd.D.macroBoundary α
  let KE : Set Pt := ⋃ w : {t : cd.D.Typ // cd.D.IsBeltType α t},
    ⋃ _ : w ∈ E, (cd.D.childTile w.1).carrier ∩ cd.D.macroBoundary α
  have hKCclosed : IsClosed KC := by
    apply isClosed_iUnion_of_finite
    intro w
    apply isClosed_iUnion_of_finite
    intro hw
    exact (tile_isClosed (cd.D.childTile w.1)).inter isClosed_frontier
  have hKEclosed : IsClosed KE := by
    apply isClosed_iUnion_of_finite
    intro w
    apply isClosed_iUnion_of_finite
    intro hw
    exact (tile_isClosed (cd.D.childTile w.1)).inter isClosed_frontier
  have hcover : cd.D.macroBoundary α ⊆ KC ∪ KE := by
    intro z hz
    have hzsupport : z ∈ support (cd.D.σ.rule α).tiles := by
      rw [cd.D.σ.support_eq α]
      exact pd_frontier_subset_carrier (emcgScaleDisk (cd.D.Q.disk α) cd.D.σ.θ hθ.ne') hz
    obtain ⟨A, hA, hzA⟩ := mem_support_iff'.1 hzsupport
    rw [cd.tmpl.rule_eq] at hA
    obtain ⟨t, ht, rfl⟩ := hA
    let w : {t : cd.D.Typ // cd.D.IsBeltType α t} := ⟨t, ht, z, hzA, hz⟩
    by_cases hw : w ∈ C
    · left
      exact Set.mem_iUnion₂.2 ⟨w, hw, hzA, hz⟩
    · right
      exact Set.mem_iUnion₂.2 ⟨w, hw, hzA, hz⟩
  have hdis : Disjoint KC KE := by
    rw [Set.disjoint_left]
    intro z hzC hzE
    obtain ⟨w, hwC, hzw, hz⟩ := Set.mem_iUnion₂.1 hzC
    obtain ⟨w', hw'E, hzw', -⟩ := Set.mem_iUnion₂.1 hzE
    have hfan := emcg_boundary_fan_reachable τ g s l routing cd α hz w.1 w'.1
      w.2.1 w'.2.1 hzw hzw'
    exact hw'E (hwC.trans hfan)
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 hfront_pre KC KE
      hKCclosed hKEclosed hcover (by
        apply Set.eq_empty_of_forall_notMem
        rintro x ⟨-, hxC, hxE⟩
        exact Set.disjoint_left.1 hdis hxC hxE) with hsub | hsub
  · obtain ⟨z, hzv, hz⟩ := v.2.2
    have hvE : v ∈ E := huv
    have hzKE : z ∈ KE := Set.mem_iUnion₂.2 ⟨v, hvE, hzv, hz⟩
    have hzKC : z ∈ KC := hsub hz
    exact Set.disjoint_left.1 hdis hzKC hzKE
  · obtain ⟨z, hzu, hz⟩ := u.2.2
    have hzKC : z ∈ KC := Set.mem_iUnion₂.2 ⟨u, SimpleGraph.Reachable.rfl, hzu, hz⟩
    have hzKE : z ∈ KE := hsub hz
    exact Set.disjoint_left.1 hdis hzKC hzKE

private lemma existsMacroCertificate_seed2_routing_step5_g2_aux_belt_edge
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) :
    ∀ _t, cd.D.IsBeltType (cd.D.owner _t) _t →
      ∃ _i, cd.D.IsBoundary (cd.D.occ _t _i) := by
  classical
  intro t ht
  let D := cd.D
  have child_mem : D.childTile t ∈ (D.σ.rule (D.owner t)).tiles := by
    rw [cd.tmpl.rule_eq]
    exact ⟨t, rfl, rfl⟩
  have child_subset : (D.childTile t).carrier ⊆ D.macroRegion (D.owner t) := by
    rw [MacroData.macroRegion, ← D.σ.support_eq]
    exact carrier_subset_support child_mem
  obtain ⟨x, hxchild, hxmacro⟩ := ht.2
  have hxnotint : x ∉ interior (D.childTile t).carrier := by
    intro hxint
    exact hxmacro.2 (interior_mono child_subset hxint)
  have hxfront : x ∈ frontier (D.childTile t).carrier := by
    rw [mem_frontier_iff_of_closed (tile_isClosed (D.childTile t))]
    exact ⟨hxchild, hxnotint⟩
  rw [tile_frontier_eq, Set.mem_iUnion] at hxfront
  obtain ⟨i, hxi⟩ := hxfront
  have outer_boundary (a : D.Side t) (ha : D.IsOuter (D.occ t a)) :
      ∃ b, D.IsBoundary (D.occ t b) := by
    obtain ⟨j, hj⟩ :=
      (existsMacroCertificate_seed2_routing_step4_g1 τ g s l routing cd).inner_side t
    have hn : 2 ≤ (D.Q.disk (D.form t)).n := by
      have := (D.Q.disk (D.form t)).three_le
      omega
    letI : NeZero (D.Q.disk (D.form t)).n := ⟨by omega⟩
    have htrans : ∃ k, D.IsOuter (D.occ t k) ∧
        D.IsInner (D.occ t (finRotate _ k)) := by
      by_contra hcon
      push_neg at hcon
      have hall : ∀ r : ℕ, D.IsOuter (D.occ t ((finRotate _)^[r] a)) := by
        intro r
        induction r with
        | zero => simpa using ha
        | succ r ih =>
          rw [Function.iterate_succ_apply']
          exact not_not.mp (hcon _ ih)
      have hr : (finRotate _)^[(j - a).val] a = j := by
        rw [← finCycle_eq_finRotate_iterate]
        change a + (j - a) = j
        simpa [add_comm] using sub_add_cancel j a
      exact hj (hr ▸ hall (j - a).val)
    obtain ⟨k, hk, hk'⟩ := htrans
    refine ⟨finRotate _ k, hk', Or.inl ?_⟩
    apply hk
    change (D.childTile t).anchor +
        (D.Q.disk (D.form t)).vertex (finRotate _ k) ∈ (D.childTile t).side k
    rw [PlacedTile.side, PolygonalDisk.side]
    exact ⟨_, right_mem_segment ℝ _ _, rfl⟩
  rw [tile_side_eq] at hxi
  by_cases hstart : x = (D.childTile t).vertex i
  · by_cases hinner : D.IsInner (D.occ t i)
    · refine ⟨i, hinner, Or.inl ?_⟩
      change (D.childTile t).vertex i ∈ D.macroBoundary (D.owner t)
      rwa [← hstart]
    · exact outer_boundary i (not_not.mp hinner)
  · by_cases hend : x = (D.childTile t).vertex (finRotate _ i)
    · by_cases hinner : D.IsInner (D.occ t i)
      · refine ⟨i, hinner, Or.inr ?_⟩
        change (D.childTile t).vertex (finRotate _ i) ∈ D.macroBoundary (D.owner t)
        rwa [← hend]
      · exact outer_boundary i (not_not.mp hinner)
    · have hxopen : x ∈ openSegment ℝ ((D.childTile t).vertex i)
          ((D.childTile t).vertex (finRotate _ i)) :=
        mem_openSegment_of_ne_left_right (Ne.symm hstart) (Ne.symm hend) hxi
      by_cases hinner : D.IsInner (D.occ t i)
      · obtain ⟨hne, howner, hside⟩ := cd.partner_spec (D.occ t i) hinner
        let o' := D.partner (D.occ t i)
        have partner_mem : D.childTile o'.1 ∈ (D.σ.rule (D.owner t)).tiles := by
          rw [cd.tmpl.rule_eq]
          exact ⟨o'.1, howner, rfl⟩
        have child_ne : D.childTile t ≠ D.childTile o'.1 := by
          intro heq
          apply hne
          apply cd.tmpl.type_injective o'.1 t howner
          · exact congrArg PlacedTile.form heq.symm
          · exact congrArg PlacedTile.anchor heq.symm
        obtain ⟨r, hr, σ, -, hlocal⟩ := two_sides
          (D.σ.rule (D.owner t)).disjoint child_mem partner_mem child_ne i o'.2
          hside hxopen
        have hxint : x ∈ interior (support (D.σ.rule (D.owner t)).tiles) := by
          rw [mem_interior_iff_mem_nhds]
          apply Filter.mem_of_superset (Metric.ball_mem_nhds x hr)
          intro y hy
          rcases le_or_gt 0
              (σ * jcr ((D.childTile t).vertex (finRotate _ i) -
                (D.childTile t).vertex i) (y - (D.childTile t).vertex i)) with h | h
          · exact carrier_subset_support child_mem ((hlocal y hy).2.2 h)
          · exact carrier_subset_support partner_mem
              (interior_subset ((hlocal y hy).2.1 h))
        exfalso
        apply hxmacro.2
        rw [MacroData.macroRegion, ← D.σ.support_eq]
        exact hxint
      · exact outer_boundary i (not_not.mp hinner)

private lemma existsMacroCertificate_seed2_routing_step5_g2_aux_central
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) :
    ∀ _α _i, ¬ cd.D.IsOuter (cd.D.occ (cd.D.central _α) _i) ∧
      ¬ cd.D.IsBoundary (cd.D.occ (cd.D.central _α) _i) := by
  intro α i
  let β := cd.baseForm α
  have hsupport : support (cd.D.σ.rule α).tiles =
      support (s.setup.retained l β).children.tiles := by
    ext x
    constructor
    · intro hx
      obtain ⟨A, hA, hxA⟩ := mem_support_iff'.1 hx
      rw [cd.tmpl.rule_eq α] at hA
      obtain ⟨t, ht, rfl⟩ := hA
      refine mem_support_iff'.2 ⟨cd.templateChild t, ?_, ?_⟩
      · exact (cd.child_bijective α).1 ht
      · rw [← cd.child_carrier t]
        exact hxA
    · intro hx
      obtain ⟨A, hA, hxA⟩ := mem_support_iff'.1 hx
      obtain ⟨t, ht, hAt⟩ := (cd.child_bijective α).2.2 hA
      refine mem_support_iff'.2 ⟨cd.D.childTile t, ?_, ?_⟩
      · rw [cd.tmpl.rule_eq α]
        exact ⟨t, ht, rfl⟩
      · rw [cd.child_carrier t, hAt]
        exact hxA
  have hregion : cd.D.macroRegion α = (s.setup.retained l β).region := by
    calc
      cd.D.macroRegion α = support (cd.D.σ.rule α).tiles := by
        exact (cd.D.σ.support_eq α).symm
      _ = support (s.setup.retained l β).children.tiles := hsupport
      _ = (s.setup.retained l β).region := (s.setup.retained l β).support_eq
  have hboundary : cd.D.macroBoundary α = frontier (s.setup.retained l β).region := by
    rw [MacroData.macroBoundary, hregion]
  have hcentralCarrier : (cd.D.childTile (cd.D.central α)).carrier =
      (s.setup.central l β).carrier := by
    calc
      (cd.D.childTile (cd.D.central α)).carrier =
          (cd.templateChild (cd.D.central α)).carrier := cd.child_carrier _
      _ = (s.setup.central l β).carrier := by rw [cd.central_child]
  obtain ⟨ρ, hρ, hclear⟩ := s.setup.clearance
  have hscale : 0 < τ.θ ^ (s.setup.GS.k * l) :=
    pow_pos (zero_lt_one.trans τ.one_lt) _
  have hpositive : 0 < ρ * τ.θ ^ (s.setup.GS.k * l) := mul_pos hρ hscale
  have hnotfrontier : ∀ x ∈ (s.setup.central l β).carrier,
      x ∉ frontier (s.setup.retained l β).region := by
    intro x hx hxf
    have hle := hclear l β cd.l_pos x hx
    rw [Metric.infDist_zero_of_mem hxf] at hle
    linarith
  have hside : cd.D.occSide (cd.D.occ (cd.D.central α) i) ⊆
      (cd.D.childTile (cd.D.central α)).carrier := by
    exact tile_side_subset _ _
  have hstart : cd.D.occStart (cd.D.occ (cd.D.central α) i) ∈
      cd.D.occSide (cd.D.occ (cd.D.central α) i) := by
    change (cd.D.childTile (cd.D.central α)).vertex i ∈
      (cd.D.childTile (cd.D.central α)).side i
    rw [tile_side_eq]
    exact left_mem_segment ℝ _ _
  have hcentral : cd.D.occStart (cd.D.occ (cd.D.central α) i) ∈
      (s.setup.central l β).carrier := by
    rw [← hcentralCarrier]
    exact hside hstart
  have hnotouter : ¬ cd.D.IsOuter (cd.D.occ (cd.D.central α) i) := by
    intro hout
    have hx := hout hstart
    rw [cd.central_owner α, hboundary] at hx
    exact hnotfrontier _ hcentral hx
  have hnotboundary : ¬ cd.D.IsBoundary (cd.D.occ (cd.D.central α) i) := by
    intro hb
    rcases hb.2 with hx | hx
    · rw [cd.central_owner α, hboundary] at hx
      exact hnotfrontier _ hcentral hx
    · have hend : cd.D.occEnd (cd.D.occ (cd.D.central α) i) ∈
          cd.D.occSide (cd.D.occ (cd.D.central α) i) := by
        change (cd.D.childTile (cd.D.central α)).vertex (finRotate _ i) ∈
          (cd.D.childTile (cd.D.central α)).side i
        rw [tile_side_eq]
        exact right_mem_segment ℝ _ _
      have hcend : cd.D.occEnd (cd.D.occ (cd.D.central α) i) ∈
          (s.setup.central l β).carrier := hcentralCarrier ▸ hside hend
      rw [cd.central_owner α, hboundary] at hx
      exact hnotfrontier _ hcend hx
  exact ⟨hnotouter, hnotboundary⟩

private lemma existsMacroCertificate_seed2_routing_step5_g2 (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) :
    existsMacroCertificate_G2Data cd.D := by
  exact {
    belt_connected := existsMacroCertificate_seed2_routing_step5_g2_aux_belt_connected
      τ g s l routing cd
    belt_edge := existsMacroCertificate_seed2_routing_step5_g2_aux_belt_edge τ g s l routing cd
    central := existsMacroCertificate_seed2_routing_step5_g2_aux_central τ g s l routing cd }

private lemma emcg_crossing_overlap_span {a b x y : Pt}
    (h : OverlapPos (segment ℝ a b) (segment ℝ x y)) :
    affineSpan ℝ ({a, b} : Set Pt) = affineSpan ℝ ({x, y} : Set Pt) := by
  obtain ⟨u, v, huv, huvsub⟩ := h
  have hmem {r s z : Pt} (hz : z ∈ segment ℝ r s) :
      z ∈ affineSpan ℝ ({r, s} : Set Pt) := by
    rw [segment_eq_image'] at hz
    obtain ⟨q, -, rfl⟩ := hz
    simpa [vadd_eq_add, vsub_eq_sub, add_comm] using
      (smul_vsub_vadd_mem_affineSpan_pair q r s)
  have hab : affineSpan ℝ ({u, v} : Set Pt) = affineSpan ℝ ({a, b} : Set Pt) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne
      (hmem (huvsub (left_mem_segment ℝ u v)).1)
      (hmem (huvsub (right_mem_segment ℝ u v)).1) huv
  have hxy : affineSpan ℝ ({u, v} : Set Pt) = affineSpan ℝ ({x, y} : Set Pt) :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne
      (hmem (huvsub (left_mem_segment ℝ u v)).2)
      (hmem (huvsub (right_mem_segment ℝ u v)).2) huv
  exact hab.symm.trans hxy

private lemma emcg_crossing_inside_or_endpoint {p q x y : Pt} (hpq : p ≠ q)
    (hov : OverlapPos (segment ℝ x y) (segment ℝ p q)) :
    segment ℝ x y ⊆ openSegment ℝ p q ∨
      p ∈ segment ℝ x y ∨ q ∈ segment ℝ x y := by
  have hspan := emcg_crossing_overlap_span hov
  obtain ⟨u, v, huv, huvsub⟩ := hov
  have hline : ∀ z ∈ affineSpan ℝ ({p, q} : Set Pt),
      ∃ r : ℝ, z = p + r • (q - p) := by
    intro z hz
    obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hz
    rw [AffineMap.lineMap_apply] at hr
    exact ⟨r, by simpa [vsub_eq_sub, vadd_eq_add, add_comm] using hr.symm⟩
  have hpoint : ∀ {a b t : ℝ}, a < b → a ≤ t → t ≤ b →
      p + t • (q - p) ∈ segment ℝ (p + a • (q - p)) (p + b • (q - p)) := by
    intro a b t hab hat htb
    rw [segment_eq_image']
    let r := (t - a) / (b - a)
    have hr0 : 0 ≤ r := by
      exact div_nonneg (sub_nonneg.mpr hat) (le_of_lt (sub_pos.mpr hab))
    have hr1 : r ≤ 1 := by
      apply (div_le_iff₀ (sub_pos.mpr hab)).2
      dsimp [r]
      linarith
    refine ⟨r, ⟨hr0, hr1⟩, ?_⟩
    have hden : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
    have hscalar : a + (t - a) / (b - a) * (b - a) = t := by
      field_simp [hden]
      ring
    calc
      (p + a • (q - p)) + r • ((p + b • (q - p)) - (p + a • (q - p))) =
          p + (a + (t - a) / (b - a) * (b - a)) • (q - p) := by
        dsimp [r]
        module
      _ = p + t • (q - p) := by rw [hscalar]
  have hpd : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hxline : x ∈ affineSpan ℝ ({p, q} : Set Pt) := by
    rw [← hspan]
    exact left_mem_affineSpan_pair ℝ x y
  have hyline : y ∈ affineSpan ℝ ({p, q} : Set Pt) := by
    rw [← hspan]
    exact right_mem_affineSpan_pair ℝ x y
  obtain ⟨rx, hrx⟩ := hline x hxline
  obtain ⟨ry, hry⟩ := hline y hyline
  have hmem_scalar : ∀ {a b t : ℝ}, a ≤ t → t ≤ b →
      p + t • (q - p) ∈ segment ℝ (p + a • (q - p)) (p + b • (q - p)) := by
    intro a b t hat htb
    by_cases hab : a < b
    · exact hpoint hab hat htb
    · have hba : b ≤ a := le_of_not_gt hab
      have h : a = b := le_antisymm (le_trans hat htb) hba
      subst b
      have ht : t = a := le_antisymm htb hat
      subst t
      rw [segment_same]
      rfl
  by_cases hpE : p ∈ segment ℝ x y
  · exact Or.inr (Or.inl hpE)
  by_cases hqE : q ∈ segment ℝ x y
  · exact Or.inr (Or.inr hqE)
  have huP : u ∈ segment ℝ p q := (huvsub (left_mem_segment ℝ u v)).2
  obtain ⟨t, ht0, ht1, hut⟩ := mem_segment_iff'.1 huP
  have huE : u ∈ segment ℝ x y := (huvsub (left_mem_segment ℝ u v)).1
  rw [segment_eq_image'] at huE
  obtain ⟨r, hr, hur⟩ := huE
  have hscalar : t = rx + r * (ry - rx) := by
    have heq : p + t • (q - p) = p + (rx + r * (ry - rx)) • (q - p) := by
      calc
        p + t • (q - p) = u := hut.symm
        _ = x + r • (y - x) := hur.symm
        _ = p + (rx + r * (ry - rx)) • (q - p) := by rw [hrx, hry]; module
    exact smul_cancel_pt hpd (add_left_cancel heq)
  have hbetween : (rx ≤ t ∧ t ≤ ry) ∨ (ry ≤ t ∧ t ≤ rx) := by
    by_cases hxy : rx ≤ ry
    · left
      constructor <;> nlinarith [hr.1, hr.2]
    · right
      have hyx : ry ≤ rx := le_of_not_ge hxy
      constructor <;> nlinarith [hr.1, hr.2]
  have hzero : ¬ ((rx ≤ 0 ∧ 0 ≤ ry) ∨ (ry ≤ 0 ∧ 0 ≤ rx)) := by
    rintro (h | h)
    · exact hpE (by simpa [hrx, hry] using hmem_scalar h.1 h.2)
    · exact hpE (by simpa [hrx, hry, segment_symm] using hmem_scalar h.1 h.2)
  have hone : ¬ ((rx ≤ 1 ∧ 1 ≤ ry) ∨ (ry ≤ 1 ∧ 1 ≤ rx)) := by
    rintro (h | h)
    · exact hqE (by simpa [hrx, hry] using hmem_scalar h.1 h.2)
    · exact hqE (by simpa [hrx, hry, segment_symm] using hmem_scalar h.1 h.2)
  have hrx0 : 0 < rx := by
    rcases hbetween with h | h
    · by_contra h'
      exact hzero (Or.inl ⟨not_lt.mp h', le_trans ht0 h.2⟩)
    · by_contra h'
      exact hzero (Or.inr ⟨h.1.trans (le_trans h.2 (not_lt.mp h')),
        le_trans ht0 h.2⟩)
  have hry0 : 0 < ry := by
    rcases hbetween with h | h
    · by_contra h'
      exact hzero (Or.inl ⟨h.1.trans (le_trans h.2 (not_lt.mp h')),
        le_trans ht0 h.2⟩)
    · by_contra h'
      exact hzero (Or.inr ⟨not_lt.mp h', le_trans ht0 h.2⟩)
  have hrx1 : rx < 1 := by
    rcases hbetween with h | h
    · by_contra h'
      exact hone (Or.inl ⟨le_trans h.1 ht1,
        le_trans (not_lt.mp h') (le_trans h.1 h.2)⟩)
    · by_contra h'
      exact hone (Or.inr ⟨le_trans h.1 ht1, not_lt.mp h'⟩)
  have hry1 : ry < 1 := by
    rcases hbetween with h | h
    · by_contra h'
      exact hone (Or.inl ⟨le_trans h.1 ht1, not_lt.mp h'⟩)
    · by_contra h'
      exact hone (Or.inr ⟨le_trans h.1 ht1,
        le_trans (not_lt.mp h') (le_trans h.1 h.2)⟩)
  left
  intro z hz
  rw [segment_eq_image'] at hz
  obtain ⟨a, ha, hza⟩ := hz
  rw [openSegment_eq_image']
  refine ⟨rx + a * (ry - rx), ?_, ?_⟩
  · constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (le_of_lt hrx0),
        mul_nonneg ha.1 (le_of_lt hry0)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr (le_of_lt hrx1)),
        mul_nonneg ha.1 (sub_nonneg.mpr (le_of_lt hry1))]
  · rw [hrx, hry] at hza
    symm
    change z = p + (rx + a * (ry - rx)) • (q - p)
    calc
      z = (p + rx • (q - p)) + a • ((p + ry • (q - p)) -
          (p + rx • (q - p))) := hza.symm
      _ = p + (rx + a * (ry - rx)) • (q - p) := by module

private lemma emcg_crossing_common_open {p q r s : Pt} (hpq : p ≠ q)
    (hrp : r ≠ p) (hsp : s ≠ p) (hr : r ∈ segment ℝ p q)
    (hs : s ∈ segment ℝ p q) :
    ∃ z, z ∈ openSegment ℝ p r ∧ z ∈ openSegment ℝ p s := by
  have hpr : Wbtw ℝ p r q := mem_segment_iff_wbtw.mp hr
  have hps : Wbtw ℝ p s q := mem_segment_iff_wbtw.mp hs
  have hsame : SameRay ℝ (r -ᵥ p) (s -ᵥ p) := by
    apply hpr.sameRay_vsub_left.trans hps.sameRay_vsub_left.symm
    intro hqp
    exact False.elim (hpq (sub_eq_zero.mp hqp).symm)
  rcases wbtw_total_of_sameRay_vsub_left hsame with hrs | hsr
  · let z := AffineMap.lineMap p r (1 / 2 : ℝ)
    have hzpr : z ∈ openSegment ℝ p r :=
      lineMap_mem_openSegment (𝕜 := ℝ) p r (by norm_num)
    have hzp : z ≠ p := by
      intro h
      rw [h] at hzpr
      exact hrp (left_mem_openSegment_iff.mp hzpr).symm
    have hzr : z ≠ r := by
      intro h
      rw [h] at hzpr
      exact hrp (right_mem_openSegment_iff.mp hzpr).symm
    have hzstrict : Sbtw ℝ p z r :=
      ⟨mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ p r hzpr), hzp, hzr⟩
    have hzps := hrs.trans_sbtw_left hzstrict
    exact ⟨z, hzpr, mem_openSegment_of_ne_left_right hzps.left_ne hzps.right_ne
      hzps.wbtw.mem_segment⟩
  · let z := AffineMap.lineMap p s (1 / 2 : ℝ)
    have hzps : z ∈ openSegment ℝ p s :=
      lineMap_mem_openSegment (𝕜 := ℝ) p s (by norm_num)
    have hzp : z ≠ p := by
      intro h
      rw [h] at hzps
      exact hsp (left_mem_openSegment_iff.mp hzps).symm
    have hzs : z ≠ s := by
      intro h
      rw [h] at hzps
      exact hsp (right_mem_openSegment_iff.mp hzps).symm
    have hzstrict : Sbtw ℝ p z s :=
      ⟨mem_segment_iff_wbtw.mp (openSegment_subset_segment ℝ p s hzps), hzp, hzs⟩
    have hzpr := hsr.trans_sbtw_left hzstrict
    exact ⟨z, mem_openSegment_of_ne_left_right hzpr.left_ne hzpr.right_ne
      hzpr.wbtw.mem_segment, hzps⟩

private lemma emcg_crossing_occ_unique_at_endpoint
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing)
    (α : cd.D.Q.Form) (p q : Pt) (hpq : p ≠ q)
    (t u : cd.D.Typ) (i : cd.D.Side t) (j : cd.D.Side u)
    (ht : cd.D.owner t = α) (hu : cd.D.owner u = α)
    (hti : cd.D.IsOuter ⟨t, i⟩) (huj : cd.D.IsOuter ⟨u, j⟩)
    (htov : OverlapPos (cd.D.occSide ⟨t, i⟩) (segment ℝ p q))
    (huov : OverlapPos (cd.D.occSide ⟨u, j⟩) (segment ℝ p q))
    (hpt : p ∈ cd.D.occSide ⟨t, i⟩) (hpu : p ∈ cd.D.occSide ⟨u, j⟩) :
    (⟨t, i⟩ : cd.D.SideOcc) = ⟨u, j⟩ := by
  have htseg : cd.D.occSide ⟨t, i⟩ =
      segment ℝ ((cd.D.childTile t).vertex i)
        ((cd.D.childTile t).vertex (finRotate _ i)) :=
    tile_side_eq (cd.D.childTile t) i
  have huseg : cd.D.occSide ⟨u, j⟩ =
      segment ℝ ((cd.D.childTile u).vertex j)
        ((cd.D.childTile u).vertex (finRotate _ j)) :=
    tile_side_eq (cd.D.childTile u) j
  have hcommon : OverlapPos (cd.D.occSide ⟨t, i⟩) (cd.D.occSide ⟨u, j⟩) := by
    obtain ⟨x, y, hxy, hxySub⟩ := htov
    obtain ⟨x', y', hxy', hxySub'⟩ := huov
    have htr : ∃ r, r ≠ p ∧ r ∈ cd.D.occSide ⟨t, i⟩ ∧ r ∈ segment ℝ p q := by
      by_cases hxp : x = p
      · refine ⟨y, ?_, (hxySub (right_mem_segment ℝ x y)).1,
          (hxySub (right_mem_segment ℝ x y)).2⟩
        intro hyp
        exact hxy (hxp.trans hyp.symm)
      · exact ⟨x, hxp, (hxySub (left_mem_segment ℝ x y)).1,
          (hxySub (left_mem_segment ℝ x y)).2⟩
    have hus : ∃ r, r ≠ p ∧ r ∈ cd.D.occSide ⟨u, j⟩ ∧ r ∈ segment ℝ p q := by
      by_cases hxp : x' = p
      · refine ⟨y', ?_, (hxySub' (right_mem_segment ℝ x' y')).1,
          (hxySub' (right_mem_segment ℝ x' y')).2⟩
        intro hyp
        exact hxy' (hxp.trans hyp.symm)
      · exact ⟨x', hxp, (hxySub' (left_mem_segment ℝ x' y')).1,
          (hxySub' (left_mem_segment ℝ x' y')).2⟩
    obtain ⟨r, hrp, hrt, hrpq⟩ := htr
    obtain ⟨r', hr'p, hr'u, hr'pq⟩ := hus
    obtain ⟨z, hzpr, hzpr'⟩ :=
      emcg_crossing_common_open hpq hrp hr'p hrpq hr'pq
    have hpr_t : segment ℝ p r ⊆ cd.D.occSide ⟨t, i⟩ := by
      rw [htseg]
      apply (convex_segment _ _).segment_subset
      · rwa [← htseg]
      · rwa [← htseg]
    have hpr'_u : segment ℝ p r' ⊆ cd.D.occSide ⟨u, j⟩ := by
      rw [huseg]
      apply (convex_segment _ _).segment_subset
      · rwa [← huseg]
      · rwa [← huseg]
    have hpz_r : segment ℝ p z ⊆ segment ℝ p r :=
      (convex_segment _ _).segment_subset (left_mem_segment ℝ p r)
        (openSegment_subset_segment ℝ _ _ hzpr)
    have hpz_r' : segment ℝ p z ⊆ segment ℝ p r' :=
      (convex_segment _ _).segment_subset (left_mem_segment ℝ p r')
        (openSegment_subset_segment ℝ _ _ hzpr')
    have hzp : z ≠ p := by
      intro h
      rw [h] at hzpr
      exact hrp (left_mem_openSegment_iff.mp hzpr).symm
    refine ⟨p, z, hzp.symm, ?_⟩
    intro w hw
    exact ⟨hpr_t (hpz_r hw), hpr'_u (hpz_r' hw)⟩
  have hAt : cd.D.childTile t ∈ (cd.D.σ.rule α).tiles := by
    rw [cd.tmpl.rule_eq α]
    exact ⟨t, ht, rfl⟩
  have hAu : cd.D.childTile u ∈ (cd.D.σ.rule α).tiles := by
    rw [cd.tmpl.rule_eq α]
    exact ⟨u, hu, rfl⟩
  have hside : (cd.D.childTile t).side i = (cd.D.childTile u).side j :=
    cd.tmpl.template_sts α _ hAt _ hAu i j hcommon
  have htile : cd.D.childTile t = cd.D.childTile u := by
    by_contra hne
    let z := AffineMap.lineMap ((cd.D.childTile t).vertex i)
      ((cd.D.childTile t).vertex (finRotate _ i)) (1 / 2 : ℝ)
    have hz : z ∈ openSegment ℝ ((cd.D.childTile t).vertex i)
        ((cd.D.childTile t).vertex (finRotate _ i)) :=
      lineMap_mem_openSegment (𝕜 := ℝ) _ _ (by norm_num)
    obtain ⟨r, hr, σ, hσ, hlocal⟩ := two_sides (cd.D.σ.rule α).disjoint
      hAt hAu hne i j hside.symm hz
    have hzint : z ∈ interior (support (cd.D.σ.rule α).tiles) := by
      rw [mem_interior_iff_mem_nhds]
      apply Filter.mem_of_superset (Metric.ball_mem_nhds z hr)
      intro w hw
      by_cases hval : 0 ≤ σ * jcr
          ((cd.D.childTile t).vertex (finRotate _ i) - (cd.D.childTile t).vertex i)
          (w - (cd.D.childTile t).vertex i)
      · exact carrier_subset_support hAt ((hlocal w hw).2.2 hval)
      · exact carrier_subset_support hAu
          (interior_subset ((hlocal w hw).2.1 (lt_of_not_ge hval)))
    rw [cd.D.σ.support_eq α] at hzint
    have hzfront : z ∈ cd.D.macroBoundary α := by
      rw [← ht]
      apply hti
      rw [htseg]
      exact openSegment_subset_segment ℝ _ _ hz
    exact hzfront.2 hzint
  have hform : cd.D.form t = cd.D.form u :=
    congrArg (fun A : PlacedTile cd.D.Q => A.form) htile
  have hanchor : cd.D.anchor t = cd.D.anchor u :=
    congrArg (fun A : PlacedTile cd.D.Q => A.anchor) htile
  have htu : t = u := cd.tmpl.type_injective t u (ht.trans hu.symm) hform hanchor
  subst u
  have hinj : Function.Injective (cd.D.childTile t).vertex := by
    intro a b hab
    apply (cd.D.Q.disk (cd.D.form t)).vertex_injective
    simpa [PlacedTile.vertex] using hab
  have hij : i = j := by
    apply cyc_seg_inj (cd.D.Q.disk (cd.D.form t)).three_le hinj
    simpa only [tile_side_eq] using hside
  subst j
  rfl

private lemma existsMacroCertificate_seed2_routing_step6_g3_aux_crossing
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) :
    ∀ α (d : Fin (cd.D.Q.disk α).n),
      Set.ncard {o : cd.D.SideOcc | cd.D.owner o.1 = α ∧ cd.D.IsOuter o ∧
        OverlapPos (cd.D.occSide o) (cd.D.macroSide α d) ∧
        ¬ cd.D.occSide o ⊆ cd.D.macroSide α d} ≤ 2 := by
  classical
  intro α d
  let p := cd.D.σ.θ • (cd.D.Q.disk α).vertex d
  let q := cd.D.σ.θ • (cd.D.Q.disk α).vertex (finRotate _ d)
  have hmacro : cd.D.macroSide α d = segment ℝ p q := by
    simp only [MacroData.macroSide, PolygonalDisk.side, emcg_smul_segment, p, q]
  have hpq : p ≠ q := by
    intro h
    have h' := smul_right_injective Pt (ne_of_gt (lt_trans zero_lt_one cd.D.σ.one_lt)) h
    exact emcg_finRotate_ne (by have := (cd.D.Q.disk α).three_le; omega) d
      ((cd.D.Q.disk α).vertex_injective h').symm
  let S := {o : cd.D.SideOcc | cd.D.owner o.1 = α ∧ cd.D.IsOuter o ∧
    OverlapPos (cd.D.occSide o) (cd.D.macroSide α d) ∧
    ¬ cd.D.occSide o ⊆ cd.D.macroSide α d}
  let L := {o ∈ S | p ∈ cd.D.occSide o}
  let R := {o ∈ S | q ∈ cd.D.occSide o}
  have hSfin : S.Finite := Set.toFinite S
  have hLfin : L.Finite := hSfin.sep _
  have hRfin : R.Finite := hSfin.sep _
  have hL : L.ncard ≤ 1 := by
    rw [Set.ncard_le_one hLfin]
    rintro ⟨t, i⟩ hti ⟨u, j⟩ huj
    apply emcg_crossing_occ_unique_at_endpoint τ g s l routing cd α p q hpq
    · exact hti.1.1
    · exact huj.1.1
    · exact hti.1.2.1
    · exact huj.1.2.1
    · simpa [hmacro] using hti.1.2.2.1
    · simpa [hmacro] using huj.1.2.2.1
    · exact hti.2
    · exact huj.2
  have hR : R.ncard ≤ 1 := by
    rw [Set.ncard_le_one hRfin]
    rintro ⟨t, i⟩ hti ⟨u, j⟩ huj
    apply emcg_crossing_occ_unique_at_endpoint τ g s l routing cd α q p hpq.symm
    · exact hti.1.1
    · exact huj.1.1
    · exact hti.1.2.1
    · exact huj.1.2.1
    · simpa [hmacro, segment_symm] using hti.1.2.2.1
    · simpa [hmacro, segment_symm] using huj.1.2.2.1
    · exact hti.2
    · exact huj.2
  have hsub : S ⊆ L ∪ R := by
    rintro o ho
    have hocc : cd.D.occSide o = segment ℝ ((cd.D.childTile o.1).vertex o.2)
        ((cd.D.childTile o.1).vertex (finRotate _ o.2)) :=
      tile_side_eq (cd.D.childTile o.1) o.2
    have hcases := emcg_crossing_inside_or_endpoint hpq (by
      rw [← hocc, ← hmacro]
      exact ho.2.2.1)
    rcases hcases with hopen | hp | hq
    · exfalso
      apply ho.2.2.2
      rw [hmacro, hocc]
      exact hopen.trans (openSegment_subset_segment ℝ p q)
    · exact Or.inl ⟨ho, by rwa [← hocc] at hp⟩
    · exact Or.inr ⟨ho, by rwa [← hocc] at hq⟩
  change S.ncard ≤ 2
  calc
    S.ncard ≤ (L ∪ R).ncard := Set.ncard_le_ncard hsub (hLfin.union hRfin)
    _ ≤ L.ncard + R.ncard := Set.ncard_union_le L R
    _ ≤ 2 := by omega

private lemma existsMacroCertificate_seed2_routing_step6_g3_aux_five
    (τ : Substitution P) (g : existsMacroCertificate_GroupingSeed τ)
    (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) :
    ∀ α d, 5 ≤ (cd.D.outerList α d).length := by
  classical
  intro α d
  have hsupport : support (cd.D.σ.rule α).tiles =
      support (s.setup.retained l (cd.baseForm α)).children.tiles := by
    rw [cd.tmpl.rule_eq]
    ext x
    constructor
    · intro hx
      obtain ⟨A, hA, hxA⟩ := mem_support_iff'.1 hx
      obtain ⟨t, ht, rfl⟩ := hA
      apply mem_support_iff'.2
      refine ⟨cd.templateChild t, (cd.child_bijective α).mapsTo ht, ?_⟩
      rw [← cd.child_carrier t]
      exact hxA
    · intro hx
      obtain ⟨X, hX, hxX⟩ := mem_support_iff'.1 hx
      obtain ⟨t, ht, htx⟩ := (cd.child_bijective α).surjOn hX
      apply mem_support_iff'.2
      refine ⟨cd.D.childTile t, ⟨t, ht, rfl⟩, ?_⟩
      rw [cd.child_carrier t, htx]
      exact hxX
  have hregion : cd.D.macroRegion α =
      (s.setup.retained l (cd.baseForm α)).region := by
    calc
      cd.D.macroRegion α = support (cd.D.σ.rule α).tiles := by
        exact (cd.D.σ.support_eq α).symm
      _ = support (s.setup.retained l (cd.baseForm α)).children.tiles := hsupport
      _ = (s.setup.retained l (cd.baseForm α)).region :=
        (s.setup.retained l (cd.baseForm α)).support_eq
  have hport : ∀ r : Fin 5, ∃ o : cd.D.SideOcc,
      o ∈ cd.D.outerList α d ∧
        cd.D.occSide o = (routing (cd.baseForm α)).port
          (cd.parentSide α d) r := by
    intro r
    let a := cd.parentSide α d
    let rd := routing (cd.baseForm α)
    obtain ⟨X, hX, i, hi⟩ := (rd.port_outer a r).1.1
    obtain ⟨t, ht, htx⟩ := (cd.child_bijective α).surjOn hX
    subst X
    have hmem : (cd.templateChild t).side i ∈
        Set.range (fun j => (cd.templateChild t).side j) := ⟨i, rfl⟩
    rw [← cd.child_sideSet t] at hmem
    obtain ⟨j, hj⟩ := hmem
    have hside : cd.D.occSide ⟨t, j⟩ = rd.port a r := hj.trans hi
    have houter : cd.D.IsOuter ⟨t, j⟩ := by
      change cd.D.occSide ⟨t, j⟩ ⊆ frontier (cd.D.macroRegion (cd.D.owner t))
      rw [ht, hregion, hside]
      exact (rd.port_outer a r).1.2
    have hsub : cd.D.occSide ⟨t, j⟩ ⊆ cd.D.macroSide α d := by
      rw [cd.parent_side_geometry, hside]
      exact (rd.port_outer a r).2
    refine ⟨⟨t, j⟩, (cd.outerList_mem α d ⟨t, j⟩).2 ?_, hside⟩
    exact ⟨ht, houter, hsub⟩
  let f : Fin 5 → (cd.D.outerList α d).toFinset := fun r =>
    ⟨Classical.choose (hport r), List.mem_toFinset.mpr
      (Classical.choose_spec (hport r)).1⟩
  have hf : Function.Injective f := by
    intro r r' hrr'
    apply (routing (cd.baseForm α)).port_injective (cd.parentSide α d)
    calc
      (routing (cd.baseForm α)).port (cd.parentSide α d) r =
          cd.D.occSide (f r).1 := (Classical.choose_spec (hport r)).2.symm
      _ = cd.D.occSide (f r').1 := by rw [hrr']
      _ = (routing (cd.baseForm α)).port (cd.parentSide α d) r' :=
        (Classical.choose_spec (hport r')).2
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe] at hc
  rw [List.toFinset_card_of_nodup (cd.outerList_nodup α d)] at hc
  simpa using hc

/-- Step 7 of `lem:certificate-exists`, (G3): `LexPositive` is a global positive orientation; the
outer lists are those of `CertData`; "at most two endpoint-crossing sides are omitted"
(`lem:whole-ports`, the geometric content of this step); each list has at least five entries
because the routing's five ports are distinct outer sides of the template contained in the scaled
parent side (`RoutingData.port_quantile`, `port_injective`), hence, through `child_sideSet` and
`outerList_mem`, five distinct entries of the list; the lists are bounded by `rankBound`. -/
private lemma existsMacroCertificate_seed2_routing_step6_g3 (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) :
    existsMacroCertificate_G3Data cd.D := by
  refine {
    pos_iff := ?_
    pos_smul := ?_
    outerList_mem := cd.outerList_mem
    outerList_nodup := cd.outerList_nodup
    outerList_sorted := cd.outerList_sorted
    crossing_le_two := ?_
    five_le := ?_
    length_le := cd.rankBound_ge }
  · intro v hv
    rw [cd.positive_eq]
    constructor
    · intro h hneg
      simp only [LexPositive, PiLp.neg_apply] at h hneg
      rcases h with h | ⟨h0, h1⟩ <;> rcases hneg with h' | ⟨h0', h1'⟩ <;>
        linarith
    · intro h
      rcases existsRoutingAfterPower_step2_ports_step1_intra_step2_clearance_lex_neg hv with
        h' | h'
      · exact h'
      · exact False.elim (h h')
  · intro v r hr hv
    rw [cd.positive_eq] at hv ⊢
    exact existsRoutingAfterPower_step2_ports_step1_intra_step2_clearance_lex_smul_pos hv hr
  · exact existsMacroCertificate_seed2_routing_step6_g3_aux_crossing τ g s l routing cd
  · exact existsMacroCertificate_seed2_routing_step6_g3_aux_five τ g s l routing cd

/-- Step 8 of `lem:certificate-exists`, (G4): "The routing lemma gives (G4)".  All clauses are
recorded in `CertData` (the print map is the routing's print slot map; the genuine paths are the
occurrence chains of the routed side lists with the invariants they inherit from `RoutingData`),
so this step is a projection; the content is in Step 4. -/
private lemma existsMacroCertificate_seed2_routing_step7_g4 (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) :
    existsMacroCertificate_G4Data cd.D :=
  { print_injective := cd.print_injective
    print_cyclic := cd.print_cyclic
    print_inner := cd.print_inner
    print_small := cd.print_small
    print_special := cd.special_print
    path_head := cd.path_head
    path_last := cd.path_last
    path_chain := cd.path_chain
    path_owner := cd.path_owner
    path_inner := cd.path_inner
    path_partner := cd.path_partner
    path_marked := cd.path_marked
    path_not_central := cd.path_not_central
    path_penultimate := cd.path_penultimate
    path_trivial := cd.path_trivial
    path_nodup := cd.path_nodup
    path_disjoint := cd.path_disjoint }

/-- Step 9 of the blueprint proof of `existsMacroCertificate_seed2_routing_step8_g5`: "the central child has the parent's own
disk"; two translates of one compact nonempty set coincide only for equal translation vectors. -/
private lemma existsMacroCertificate_seed2_routing_step8_g5_step9_vadd_cancel {K : Set Pt} (hK : IsCompact K)
    (hne : K.Nonempty) {u w : Pt} (h : u +ᵥ K = w +ᵥ K) : u = w := by
  have hδ : (u - w) +ᵥ K = K := by
    have := congrArg (fun S => (-w) +ᵥ S) h
    simpa [vadd_vadd, sub_eq_neg_add, add_comm] using this
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne
    ((continuous_const.inner continuous_id : Continuous fun y : Pt => inner ℝ (u - w) y).continuousOn)
  have hmem : (u - w) + x ∈ K := by
    rw [← hδ]; exact ⟨x, hx, rfl⟩
  have := hmax hmem
  simp only [mem_setOf_eq, inner_add_right, real_inner_self_eq_norm_sq] at this
  have h0 : ‖u - w‖ ^ 2 ≤ 0 := by linarith
  have : ‖u - w‖ = 0 := by nlinarith [norm_nonneg (u - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Step 9 of the blueprint proof of `existsMacroCertificate_seed2_routing_step8_g5`: "the central child has the parent's own
disk"; if the listed sides of one disk, translated by `u` and reindexed surjectively, are the listed sides of the same disk
translated by `w`, then `u = w`. -/
private lemma existsMacroCertificate_seed2_routing_step8_g5_step9_anchor_eq {Z Y : PolygonalDisk} (hZY : Z = Y)
    {ι : Type*} (f : ι → Fin Z.n) (hf : Function.Surjective f) {u w : Pt}
    (h : Set.range (fun i => u +ᵥ Z.side (f i)) = Set.range (fun j => w +ᵥ Y.side j)) : u = w := by
  subst hZY
  have hU : (⋃ k, Z.side k) = frontier Z.carrier := Z.frontier_eq.symm
  apply existsMacroCertificate_seed2_routing_step8_g5_step9_vadd_cancel (K := ⋃ k, Z.side k)
  · rw [hU]
    exact Z.compact.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans Z.compact.isClosed.closure_subset)
  · exact ⟨Z.vertex ⟨0, by have := Z.three_le; omega⟩,
      mem_iUnion.2 ⟨_, left_mem_segment ℝ _ _⟩⟩
  · have h2 := congrArg sUnion h
    simp only [sUnion_range] at h2
    rw [Set.vadd_set_iUnion, Set.vadd_set_iUnion, ← h2]
    exact (hf.iUnion_comp (fun k => u +ᵥ Z.side k)).symm

/-- Step 9 of the blueprint proof of `existsMacroCertificate_seed2_routing_step8_g5`: "the print map is the identity on its
marked sides"; equal translated listed sides of equal disks have equal indices. -/
private lemma existsMacroCertificate_seed2_routing_step8_g5_step9_side_index {Z Y : PolygonalDisk} (hZY : Z = Y)
    (u : Pt) (i : Fin Z.n) (j : Fin Y.n) (h : u +ᵥ Z.side i = u +ᵥ Y.side j) : (i : ℕ) = j := by
  subst hZY
  have h' : Z.side i = Z.side j := by simpa [vadd_vadd] using congrArg (fun S => (-u) +ᵥ S) h
  rw [cyc_seg_inj Z.three_le Z.vertex_injective h']

/-- Step 9 of the blueprint proof of `existsMacroCertificate_seed2_routing_step8_g5`: "For a retained large form `α = c^l β`,
`c^l α = c^{2l} β = c^l β = α`. Thus the central form is fixed." -/
private lemma existsMacroCertificate_seed2_routing_step8_g5_step9_central_fixes (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) (α : cd.D.Q.Form)
    (hk : cd.D.kind α = .large) : cd.D.form (cd.D.central α) = α := by
  obtain ⟨β, hβ⟩ := (cd.kind_large α).1 hk
  apply cd.catalogue_form_injective
  rw [← cd.child_form, cd.central_form, hβ, cd.base_form α _ hβ, ← Function.iterate_add_apply, ← two_mul,
    cd.central_idempotent]

/-- Step 9 of the blueprint proof of `existsMacroCertificate_seed2_routing_step8_g5`: "The central child belongs to its
template and is its unique large child." -/
private lemma existsMacroCertificate_seed2_routing_step8_g5_step9_large_iff (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) (t : cd.D.Typ) :
    cd.D.kind (cd.D.form t) = .large ↔ t = cd.D.central (cd.D.owner t) := by
  constructor
  · intro hk
    obtain ⟨β, hβ⟩ := (cd.kind_large _).1 hk
    have hmem : cd.templateChild t ∈ (s.setup.retained l (cd.baseForm (cd.D.owner t))).children.tiles :=
      (cd.child_bijective (cd.D.owner t)).mapsTo (show t ∈ {u | cd.D.owner u = cd.D.owner t} from rfl)
    by_contra hne
    have hX : cd.templateChild t ≠ s.setup.central l (cd.baseForm (cd.D.owner t)) := by
      intro hX
      apply hne
      apply (cd.child_bijective (cd.D.owner t)).injOn
        (show t ∈ {u | cd.D.owner u = cd.D.owner t} from rfl)
        (show cd.D.central (cd.D.owner t) ∈ {u | cd.D.owner u = cd.D.owner t} from cd.central_owner _)
      rw [hX, cd.central_child]
    obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := ⟨l - 1, by have := cd.l_pos; omega⟩
    apply s.noncentral_not_large l _ cd.l_pos _ hmem hX (s.setup.c^[m] β)
    rw [cd.child_form, hβ, hm, Function.iterate_succ_apply']
  · intro ht
    rw [ht]
    apply (cd.kind_large _).2
    exact ⟨cd.baseForm (cd.D.owner t), by rw [← cd.child_form, cd.central_form]⟩

/-- Step 9 of the blueprint proof of `existsMacroCertificate_seed2_routing_step8_g5`: "the print map is the identity on its
marked sides (the central child has the parent's own disk)", from `RoutingData.print_id`. -/
private lemma existsMacroCertificate_seed2_routing_step8_g5_step9_print_id (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) (α : cd.D.Q.Form) (d : Fin (cd.D.Q.disk α).n)
    (hk : cd.D.kind α = .large) (hm : cd.D.marked α d) : (cd.D.print α d).val = d.val := by
  obtain ⟨β, hβ⟩ := (cd.kind_large α).1 hk
  have hB : cd.baseForm α = s.setup.c^[l] β := cd.base_form α _ hβ
  have hfix : s.setup.c^[l] (cd.baseForm α) = cd.baseForm α := by
    rw [hB, ← Function.iterate_add_apply, ← two_mul, cd.central_idempotent]
  have hfc : cd.D.form (cd.D.central α) = α :=
    existsMacroCertificate_seed2_routing_step8_g5_step9_central_fixes τ g s l routing cd α hk
  have hθ : cd.D.σ.θ = τ.θ ^ (s.setup.GS.k * l) := by
    rw [cd.rep.θ_eq, s.setup_grouped, g.grouped_power]
  have hθpos : (τ.θ ^ (s.setup.GS.k * l)) ≠ 0 := (pow_pos (lt_trans zero_lt_one τ.one_lt) _).ne'
  have hQside : ∀ α' (j : Fin (cd.D.Q.disk α').n), (cd.D.Q.disk α').side j =
      (s.setup.GS.G.P'.disk (cd.baseForm α')).side (cd.parentSide α' j) := by
    intro α' j
    have h := cd.parent_side_geometry α' j
    rw [MacroData.macroSide, hθ] at h
    simpa [smul_smul, hθpos] using congrArg (fun S => (τ.θ ^ (s.setup.GS.k * l))⁻¹ • S) h
  have hZY : s.setup.GS.G.P'.disk (cd.baseForm (cd.D.form (cd.D.central α))) =
      s.setup.GS.G.mixed.disk (s.setup.central l (cd.baseForm α)).form := by
    rw [s.setup.central_form, hfc]
    exact congrArg s.setup.GS.G.P'.disk hfix.symm
  have hside_occ : ∀ j : Fin (cd.D.Q.disk (cd.D.form (cd.D.central α))).n,
      cd.D.occSide ⟨cd.D.central α, j⟩ = cd.D.anchor (cd.D.central α) +ᵥ
        (s.setup.GS.G.P'.disk (cd.baseForm (cd.D.form (cd.D.central α)))).side
          (cd.parentSide (cd.D.form (cd.D.central α)) j) := by
    intro j
    rw [← hQside]
    rfl
  have hanchor : cd.D.anchor (cd.D.central α) = (s.setup.central l (cd.baseForm α)).anchor := by
    apply existsMacroCertificate_seed2_routing_step8_g5_step9_anchor_eq hZY
      (cd.parentSide (cd.D.form (cd.D.central α))) (cd.parentSide_bijective _).2
    have h := cd.child_sideSet (cd.D.central α)
    rw [cd.central_child] at h
    refine Eq.trans ?_ (h.trans rfl)
    congr 1
    funext i
    exact (hside_occ i).symm
  have hpr := cd.print_from_routing α d
  rw [show cd.D.printOcc α d = ⟨cd.D.central α, cd.D.print α d⟩ from rfl, hside_occ, hanchor] at hpr
  have hv := existsMacroCertificate_seed2_routing_step8_g5_step9_side_index hZY _ _ _ hpr
  have hid := (routing (cd.baseForm α)).print_id
    (by rw [s.setup.central_form]; exact congrArg s.setup.GS.G.P'.disk hfix)
    (cd.parentSide α d) ((cd.marked_from_setup α d).1 hm)
  have hC : ∀ α' α'' (_h : α' = α'') (j : Fin (cd.D.Q.disk α').n) (e : Fin (cd.D.Q.disk α'').n),
      (cd.parentSide α' j : ℕ) = cd.parentSide α'' e → (j : ℕ) = e := by
    intro α' α'' h
    subst h
    intro j e hv
    rw [cd.parentSide_injective _ (Fin.ext hv)]
  exact hC _ _ hfc _ _ (hv.trans hid)

/-- Step 9 of the blueprint proof of `existsMacroCertificate_seed2_routing_step8_g5`: the marked sides of a form correspond,
through the bijection `parentSide`, to the marked sides of its grouped base form. -/
private lemma existsMacroCertificate_seed2_routing_step8_g5_step9_card_marked (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) (α : cd.D.Q.Form) :
    Nat.card {d // cd.D.marked α d} = (s.setup.markedSides (cd.baseForm α)).card := by
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  refine Equiv.ofBijective (fun d => ⟨cd.parentSide α d.1, (cd.marked_from_setup α d.1).1 d.2⟩) ⟨?_, ?_⟩
  · intro d e hde
    exact Subtype.ext (cd.parentSide_injective α (congrArg Subtype.val hde))
  · rintro ⟨a, ha⟩
    obtain ⟨d, hd⟩ := (cd.parentSide_bijective α).2 a
    exact ⟨⟨d, (cd.marked_from_setup α d).2 (hd ▸ ha)⟩, Subtype.ext hd⟩

/-- Step 9 of the blueprint proof of `existsMacroCertificate_seed2_routing_step8_g5`: "A large form has exactly `4N` marked
sides (Step 3)". -/
private lemma existsMacroCertificate_seed2_routing_step8_g5_step9_card_large (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) (α : cd.D.Q.Form)
    (hk : cd.D.kind α = .large) : Nat.card {d // cd.D.marked α d} = 4 * cd.D.N := by
  obtain ⟨β, hβ⟩ := (cd.kind_large α).1 hk
  obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := ⟨l - 1, by have := cd.l_pos; omega⟩
  rw [existsMacroCertificate_seed2_routing_step8_g5_step9_card_marked τ g s l routing cd α,
    cd.base_form α _ hβ, cd.N_eq, hm, Function.iterate_succ_apply']
  exact s.marked_large_card _

/-- Step 9 of the blueprint proof of `existsMacroCertificate_seed2_routing_step8_g5`: "a non-large form has at most `Q`
marked sides, because ... an annular piece has at most `Q` sides while an original tile has at most `K₀ ≤ Q` sides". -/
private lemma existsMacroCertificate_seed2_routing_step8_g5_step9_card_small (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) (α : cd.D.Q.Form)
    (hk : cd.D.kind α ≠ .large) : Nat.card {d // cd.D.marked α d} ≤ cd.D.Qmax := by
  have h1 : Nat.card {d // cd.D.marked α d} ≤ (cd.D.Q.disk α).n := by
    simpa using Finite.card_subtype_le (fun d : Fin (cd.D.Q.disk α).n => cd.D.marked α d)
  have h2 : (cd.D.Q.disk α).n = (s.setup.GS.G.P'.disk (cd.baseForm α)).n := by
    simpa using Fintype.card_of_bijective (cd.parentSide_bijective α)
  have h3 : (s.setup.GS.G.P'.disk (cd.baseForm α)).n ≤ g.Qmax := by
    cases hkα : cd.D.kind α with
    | large => exact (hk hkα).elim
    | small =>
      obtain ⟨β, γ, X, hX, hXc, hXf, hγ⟩ := (cd.kind_small α).1 hkα
      rw [cd.base_form α γ hγ]
      exact s.sides_le_Qmax_child l β cd.l_pos X hX hXc γ hXf
    | original =>
      obtain ⟨p, hp⟩ := (cd.kind_original α).1 hkα
      have hα : α = cd.originalForm p := cd.catalogue_form_injective _ _ (by rw [hp, cd.original_tile])
      subst hα
      exact s.sides_le_Qmax_singleton _ p (cd.base_original p)
  rw [cd.Qmax_eq]
  omega

/-- Step 9 of `lem:certificate-exists`, (G5): the central child belongs to its template
(`central_owner`) and is its unique large child (`kind_large`, `child_form`, `child_bijective`,
`SetupSeed.noncentral_not_large`); `central_fixes_large` from `base_form`, `catalogue_form_injective`
and idempotence; the marked-side counts through the bijection `parentSide` (`SetupSeed.marked_large_card`,
`SetupSeed.sides_le_Qmax_child` / `sides_le_Qmax_singleton`, through `kind_small` / `kind_original`,
`base_form` / `base_original`); "For a retained large form `α = c^l β`,
`c^l α = α`" (`central_idempotent`); identity prints for a large parent (`RoutingData.print_id`);
a large form has `4N` marked sides and a non-large form at most `Qmax` (`SetupSeed`,
`g.annular_quantitative`, `MeshConstants.sides_le`); `4N > 3Q`; every original type has a marked
inner side (all its sides are marked). -/
private lemma existsMacroCertificate_seed2_routing_step8_g5 (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) :
    existsMacroCertificate_G5Data cd.D := by
  exact
  { central_owner := cd.central_owner
    large_iff := existsMacroCertificate_seed2_routing_step8_g5_step9_large_iff τ g s l routing cd
    central_fixes_large := existsMacroCertificate_seed2_routing_step8_g5_step9_central_fixes τ g s l routing cd
    print_id_large := existsMacroCertificate_seed2_routing_step8_g5_step9_print_id τ g s l routing cd
    card_marked_large := existsMacroCertificate_seed2_routing_step8_g5_step9_card_large τ g s l routing cd
    card_marked_small := existsMacroCertificate_seed2_routing_step8_g5_step9_card_small τ g s l routing cd
    three_Q_lt := by rw [cd.Qmax_eq, cd.N_eq]; exact g.N_dominates
    original_marked := fun t ht => by
      obtain ⟨i, hi⟩ := (existsMacroCertificate_seed2_routing_step4_g1 τ g s l routing cd).inner_side t
      exact ⟨i, hi, cd.marked_rule_nonlarge _ (Or.inl (by simp [ht]))⟩ }

private noncomputable def existsMacroCertificate_seed2_routing_step9_g6_ordinary (D : MacroData P)
    (t : D.Typ) : Multiset D.Typ := by
  classical
  exact ∑ i ∈ Finset.univ.filter (fun i : D.Side t => D.IsFingerprintSide (D.occ t i)),
    ({(D.partner (D.occ t i)).1} : Multiset D.Typ)

private def existsMacroCertificate_seed2_routing_step9_g6_kind (D : MacroData P)
    (t : D.Typ) : TypeKind :=
  match D.kind (D.form t) with
  | .original => .original
  | .small => .small
  | .large => .central

private def existsMacroCertificate_seed2_routing_step9_g6_data (D : MacroData P) :
    FingerprintData where
  Tag := D.Typ
  decEq := inferInstance
  Tmpl := D.Q.Form
  template := D.owner
  kind := existsMacroCertificate_seed2_routing_step9_g6_kind D
  ordinary := existsMacroCertificate_seed2_routing_step9_g6_ordinary D
  adj := fun t u => t ≠ u ∧ D.owner u = D.owner t ∧ ∃ (i : D.Side t) (j : D.Side u),
    D.IsInner (D.occ t i) ∧ D.occSide (D.occ t i) = D.occSide (D.occ u j)

@[simp] private lemma existsMacroCertificate_seed2_routing_step9_g6_kind_original
    (D : MacroData P) (t : D.Typ) :
    existsMacroCertificate_seed2_routing_step9_g6_kind D t = .original ↔
      D.kind (D.form t) = .original := by
  rcases h : D.kind (D.form t) with _ | _ | _ <;>
    simp [existsMacroCertificate_seed2_routing_step9_g6_kind, h]

@[simp] private lemma existsMacroCertificate_seed2_routing_step9_g6_kind_small
    (D : MacroData P) (t : D.Typ) :
    existsMacroCertificate_seed2_routing_step9_g6_kind D t = .small ↔
      D.kind (D.form t) = .small := by
  rcases h : D.kind (D.form t) with _ | _ | _ <;>
    simp [existsMacroCertificate_seed2_routing_step9_g6_kind, h]

@[simp] private lemma existsMacroCertificate_seed2_routing_step9_g6_kind_central
    (D : MacroData P) (t : D.Typ) :
    existsMacroCertificate_seed2_routing_step9_g6_kind D t = .central ↔
      D.kind (D.form t) = .large := by
  rcases h : D.kind (D.form t) with _ | _ | _ <;>
    simp [existsMacroCertificate_seed2_routing_step9_g6_kind, h]

private lemma existsMacroCertificate_seed2_routing_step9_g6_base
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing) (t : cd.D.Typ) :
    (existsMacroCertificate_seed2_routing_step9_g6_data cd.D).baseFingerprint t =
      cd.D.baseFingerprint t := by
  classical
  let S := Finset.univ.filter
    (fun i : cd.D.Side t => cd.D.IsFingerprintSide (cd.D.occ t i))
  have hinner : ∀ i ∈ S, cd.D.IsInner (cd.D.occ t i) := by
    intro i hi
    exact (Finset.mem_filter.1 hi).2.1
  have hpair : ∀ i ∈ S,
      ({(cd.D.partner (cd.D.occ t i)).1, t} : Multiset cd.D.Typ) =
        {(cd.D.edgeTypes (cd.D.edge (cd.D.occ t i))).1,
          (cd.D.edgeTypes (cd.D.edge (cd.D.occ t i))).2} := by
    intro i hi
    rcases cd.edgeTypes_spec (cd.D.occ t i) (hinner i hi) with h | h
    · rw [h]
      exact Multiset.cons_swap _ _ _
    · rw [h]
  change (∑ i ∈ S, ({(cd.D.partner (cd.D.occ t i)).1} : Multiset cd.D.Typ)) +
      Multiset.replicate
        (Multiset.card (∑ i ∈ S,
          ({(cd.D.partner (cd.D.occ t i)).1} : Multiset cd.D.Typ))) t =
    ∑ i ∈ S,
      ({(cd.D.edgeTypes (cd.D.edge (cd.D.occ t i))).1,
        (cd.D.edgeTypes (cd.D.edge (cd.D.occ t i))).2} : Multiset cd.D.Typ)
  have hcard : Multiset.card
      (∑ i ∈ S, ({(cd.D.partner (cd.D.occ t i)).1} : Multiset cd.D.Typ)) = S.card := by
    simp
  rw [hcard]
  revert hinner hpair
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert i S hi ih =>
      intro hinner hpair
      rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
        Multiset.replicate_succ, Finset.sum_insert hi]
      rw [← Multiset.singleton_add t (Multiset.replicate S.card t)]
      calc
        _ = ({(cd.D.partner (cd.D.occ t i)).1, t} : Multiset cd.D.Typ) +
              ((∑ j ∈ S, ({(cd.D.partner (cd.D.occ t j)).1} : Multiset cd.D.Typ)) +
                Multiset.replicate S.card t) := by
          rw [show ({(cd.D.partner (cd.D.occ t i)).1, t} : Multiset cd.D.Typ) =
              {(cd.D.partner (cd.D.occ t i)).1} + {t} from
            (Multiset.singleton_add (cd.D.partner (cd.D.occ t i)).1 {t}).symm]
          simp only [add_assoc, add_left_comm, add_comm]
        _ = _ := by
          rw [hpair i (Finset.mem_insert_self i S),
            ih (fun j hj => hinner j (Finset.mem_insert_of_mem hj))
              (fun j hj => hpair j (Finset.mem_insert_of_mem hj))]

private lemma existsMacroCertificate_seed2_routing_step9_g6_mem_ordinary
    (D : MacroData P) (t v : D.Typ) :
    v ∈ existsMacroCertificate_seed2_routing_step9_g6_ordinary D t ↔
      ∃ i : D.Side t,
        D.IsFingerprintSide (D.occ t i) ∧ (D.partner (D.occ t i)).1 = v := by
  classical
  simp [existsMacroCertificate_seed2_routing_step9_g6_ordinary, eq_comm]

private lemma existsMacroCertificate_seed2_routing_step9_g6_possible
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing)
    (g5 : existsMacroCertificate_G5Data cd.D) (t : cd.D.Typ)
    (ht : ¬ cd.D.IsCentral t) :
    (existsMacroCertificate_seed2_routing_step9_g6_data cd.D).possibleFingerprints t =
      cd.D.possibleFingerprints t := by
  rcases hk : cd.D.kind (cd.D.form t) with _ | _ | _
  · unfold FingerprintData.possibleFingerprints MacroData.possibleFingerprints
    rw [existsMacroCertificate_seed2_routing_step9_g6_base cd t]
    simp [existsMacroCertificate_seed2_routing_step9_g6_data,
      existsMacroCertificate_seed2_routing_step9_g6_kind, hk]
  · unfold FingerprintData.possibleFingerprints MacroData.possibleFingerprints
    rw [existsMacroCertificate_seed2_routing_step9_g6_base cd t]
    simp [existsMacroCertificate_seed2_routing_step9_g6_data,
      existsMacroCertificate_seed2_routing_step9_g6_kind, hk]
  · exact False.elim (ht (g5.large_iff t |>.mp hk).symm)

private lemma existsMacroCertificate_seed2_routing_step9_g6_original_fingerprint
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing)
    (g5 : existsMacroCertificate_G5Data cd.D) (t : cd.D.Typ)
    (ht : cd.D.kind (cd.D.form t) = .original) (i : cd.D.Side t) :
    cd.D.IsFingerprintSide (cd.D.occ t i) ↔ cd.D.IsInner (cd.D.occ t i) := by
  constructor
  · exact fun h => h.1
  · intro hi
    refine ⟨hi, ⟨?_, ?_⟩, fun hs => (FormKind.noConfusion (ht.symm.trans hs))⟩
    · intro hspecial
      exact FormKind.noConfusion (ht.symm.trans (cd.special_small _ hspecial))
    · rintro ⟨d, hmarked, ho | ho⟩
      · have hcowner : cd.D.owner (cd.D.central (cd.D.owner t)) = cd.D.owner t :=
          cd.central_owner _
        have hlarge : cd.D.kind
            (cd.D.form (cd.D.central (cd.D.owner t))) = .large := by
          apply (g5.large_iff _).2
          rw [hcowner]
        have htc : t = cd.D.central (cd.D.owner t) := congrArg Sigma.fst ho
        rw [htc] at ht
        exact FormKind.noConfusion (ht.symm.trans hlarge)
      · have hsmall := cd.print_small (cd.D.owner t) d hmarked
        have hts : t = (cd.D.partner (cd.D.printOcc (cd.D.owner t) d)).1 :=
          congrArg Sigma.fst ho
        rw [hts] at ht
        exact FormKind.noConfusion (ht.symm.trans hsmall)

private lemma existsMacroCertificate_seed2_routing_step9_g6_adj_original
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing)
    (g1 : existsMacroCertificate_G1Data cd.D)
    (g5 : existsMacroCertificate_G5Data cd.D) (t u : cd.D.Typ)
    (ht : cd.D.kind (cd.D.form t) = .original) :
    (existsMacroCertificate_seed2_routing_step9_g6_data cd.D).adj t u ↔
      u ∈ existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D t := by
  rw [existsMacroCertificate_seed2_routing_step9_g6_mem_ordinary]
  constructor
  · rintro ⟨htu, howner, i, j, hi, hsides⟩
    have heq := g1.side_unique (cd.D.occ t i) (cd.D.occ u j) hi howner htu.symm
      hsides.symm
    refine ⟨i,
      (existsMacroCertificate_seed2_routing_step9_g6_original_fingerprint cd g5 t ht i).2 hi,
      ?_⟩
    exact (congrArg Sigma.fst heq).symm
  · rintro ⟨i, hi, hpartner⟩
    have hp := g1.partner (cd.D.occ t i) hi.1
    rcases heq : cd.D.partner (cd.D.occ t i) with ⟨v, j⟩
    simp only [heq] at hpartner hp
    subst v
    exact ⟨hp.1.symm, hp.2.1, i, j, hi.1, hp.2.2.symm⟩

private def existsMacroCertificate_seed2_routing_step9_g6_partnerIndex
    (D : MacroData P) (t u : D.Typ) (i : D.Side t)
    (h : (D.partner (D.occ t i)).1 = u) : D.Side u := by
  subst u
  exact (D.partner (D.occ t i)).2

private lemma existsMacroCertificate_seed2_routing_step9_g6_partnerOcc
    (D : MacroData P) (t u : D.Typ) (i : D.Side t)
    (h : (D.partner (D.occ t i)).1 = u) :
    D.occ u (existsMacroCertificate_seed2_routing_step9_g6_partnerIndex D t u i h) =
      D.partner (D.occ t i) := by
  subst u
  rfl

private def existsMacroCertificate_seed2_routing_step9_g6_sideOccIndex
    (D : MacroData P) (o : D.SideOcc) : ℕ := o.2

private lemma existsMacroCertificate_seed2_routing_step9_g6_partner_inner
    {D : MacroData P} (g1 : existsMacroCertificate_G1Data D) (o : D.SideOcc)
    (ho : D.IsInner o) : D.IsInner (D.partner o) := by
  have hp := g1.partner o ho
  intro hout
  apply ho
  unfold MacroData.IsOuter at hout ⊢
  rw [hp.2.2, hp.2.1] at hout
  exact hout

private lemma existsMacroCertificate_seed2_routing_step9_g6_partnerIndex_involutive
    {D : MacroData P} (g1 : existsMacroCertificate_G1Data D) (t u : D.Typ)
    (i : D.Side t) (hi : D.IsInner (D.occ t i))
    (h : (D.partner (D.occ t i)).1 = u)
    (h' : (D.partner
      (D.occ u (existsMacroCertificate_seed2_routing_step9_g6_partnerIndex D t u i h))).1 = t) :
    existsMacroCertificate_seed2_routing_step9_g6_partnerIndex D u t
      (existsMacroCertificate_seed2_routing_step9_g6_partnerIndex D t u i h) h' = i := by
  apply Fin.ext
  have hocc := existsMacroCertificate_seed2_routing_step9_g6_partnerOcc D t u i h
  have hocc' := existsMacroCertificate_seed2_routing_step9_g6_partnerOcc D u t
    (existsMacroCertificate_seed2_routing_step9_g6_partnerIndex D t u i h) h'
  have hpp := g1.partner_partner (D.occ t i) hi
  have heq : D.occ t
      (existsMacroCertificate_seed2_routing_step9_g6_partnerIndex D u t
        (existsMacroCertificate_seed2_routing_step9_g6_partnerIndex D t u i h) h') =
      D.occ t i := by
    rw [hocc', hocc, hpp]
  exact congrArg (existsMacroCertificate_seed2_routing_step9_g6_sideOccIndex D) heq

set_option maxHeartbeats 800000 in
private lemma existsMacroCertificate_seed2_routing_step9_g6_original_count
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing)
    (g1 : existsMacroCertificate_G1Data cd.D)
    (g5 : existsMacroCertificate_G5Data cd.D) (t u : cd.D.Typ)
    (ht : cd.D.kind (cd.D.form t) = .original)
    (hu : cd.D.kind (cd.D.form u) = .original) :
    (existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D t).count u =
      (existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D u).count t := by
  classical
  let S := Finset.univ.filter (fun i : cd.D.Side t =>
    cd.D.IsFingerprintSide (cd.D.occ t i) ∧ (cd.D.partner (cd.D.occ t i)).1 = u)
  let T := Finset.univ.filter (fun j : cd.D.Side u =>
    cd.D.IsFingerprintSide (cd.D.occ u j) ∧ (cd.D.partner (cd.D.occ u j)).1 = t)
  have hcount_t :
      (existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D t).count u = S.card := by
    rw [existsMacroCertificate_seed2_routing_step9_g6_ordinary, Multiset.count_sum']
    simp only [Multiset.count_singleton]
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext i
    simp [S, eq_comm]
  have hcount_u :
      (existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D u).count t = T.card := by
    rw [existsMacroCertificate_seed2_routing_step9_g6_ordinary, Multiset.count_sum']
    simp only [Multiset.count_singleton]
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext i
    simp [T, eq_comm]
  rw [hcount_t, hcount_u]
  let f : ∀ i ∈ S, cd.D.Side u := fun i hi =>
    existsMacroCertificate_seed2_routing_step9_g6_partnerIndex cd.D t u i
      (Finset.mem_filter.1 hi).2.2
  let q : ∀ j ∈ T, cd.D.Side t := fun j hj =>
    existsMacroCertificate_seed2_routing_step9_g6_partnerIndex cd.D u t j
      (Finset.mem_filter.1 hj).2.2
  have hf : ∀ i hi, f i hi ∈ T := by
    intro i hi
    have hi' := (Finset.mem_filter.1 hi).2
    have hiInner : cd.D.IsInner (cd.D.occ t i) := hi'.1.1
    have hiPartner : (cd.D.partner (cd.D.occ t i)).1 = u := hi'.2
    dsimp [f]
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · apply (existsMacroCertificate_seed2_routing_step9_g6_original_fingerprint
        cd g5 u hu _).2
      rw [existsMacroCertificate_seed2_routing_step9_g6_partnerOcc cd.D t u i hiPartner]
      exact existsMacroCertificate_seed2_routing_step9_g6_partner_inner g1 _ hiInner
    · rw [existsMacroCertificate_seed2_routing_step9_g6_partnerOcc cd.D t u i hiPartner]
      have hpp := g1.partner_partner (cd.D.occ t i) hiInner
      rw [hpp]
  have hq : ∀ j hj, q j hj ∈ S := by
    intro j hj
    have hj' := (Finset.mem_filter.1 hj).2
    have hjInner : cd.D.IsInner (cd.D.occ u j) := hj'.1.1
    have hjPartner : (cd.D.partner (cd.D.occ u j)).1 = t := hj'.2
    dsimp [q]
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · apply (existsMacroCertificate_seed2_routing_step9_g6_original_fingerprint
        cd g5 t ht _).2
      rw [existsMacroCertificate_seed2_routing_step9_g6_partnerOcc cd.D u t j hjPartner]
      exact existsMacroCertificate_seed2_routing_step9_g6_partner_inner g1 _ hjInner
    · rw [existsMacroCertificate_seed2_routing_step9_g6_partnerOcc cd.D u t j hjPartner]
      have hpp := g1.partner_partner (cd.D.occ u j) hjInner
      rw [hpp]
  refine Finset.card_bij' f q hf hq ?_ ?_
  · intro i hi
    dsimp [q, f]
    apply existsMacroCertificate_seed2_routing_step9_g6_partnerIndex_involutive g1
    exact (Finset.mem_filter.1 hi).2.1.1
  · intro j hj
    dsimp [q, f]
    apply existsMacroCertificate_seed2_routing_step9_g6_partnerIndex_involutive g1
    exact (Finset.mem_filter.1 hj).2.1.1

private lemma existsMacroCertificate_seed2_routing_step9_g6_of_quantitative
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing)
    (hsmall : ∀ t,
      (existsMacroCertificate_seed2_routing_step9_g6_data cd.D).kind t = .small →
      g.M.K0 + 2 ≤ Multiset.card
        ((existsMacroCertificate_seed2_routing_step9_g6_data cd.D).ordinary t))
    (hprivate : ∀ t u,
      (existsMacroCertificate_seed2_routing_step9_g6_data cd.D).kind t = .small →
      (existsMacroCertificate_seed2_routing_step9_g6_data cd.D).kind u = .small →
      t ≠ u → cd.D.owner t = cd.D.owner u →
      3 ≤ Multiset.card
        (((existsMacroCertificate_seed2_routing_step9_g6_data cd.D).ordinary t).filter
          (fun v =>
            (existsMacroCertificate_seed2_routing_step9_g6_data cd.D).kind v = .original ∧
              v ∉ (existsMacroCertificate_seed2_routing_step9_g6_data cd.D).ordinary u))) :
    ∀ t u, t ≠ u → ¬ cd.D.IsCentral t → ¬ cd.D.IsCentral u →
      Disjoint (cd.D.possibleFingerprints t) (cd.D.possibleFingerprints u) := by
  classical
  let F := existsMacroCertificate_seed2_routing_step9_g6_data cd.D
  have g1 := existsMacroCertificate_seed2_routing_step4_g1 τ g s l routing cd
  have g5 := existsMacroCertificate_seed2_routing_step8_g5 τ g s l routing cd
  have htmpl : ∀ t, ∀ v ∈ F.ordinary t, F.template v = F.template t := by
    intro t v hv
    rcases (existsMacroCertificate_seed2_routing_step9_g6_mem_ordinary cd.D t v).1 hv with
      ⟨i, hi, rfl⟩
    exact (g1.partner (cd.D.occ t i) hi.1).2.1
  have hadj_symm : ∀ t u, F.adj t u → F.adj u t := by
    rintro t u ⟨htu, howner, i, j, hi, hsides⟩
    refine ⟨htu.symm, howner.symm, j, i, ?_, hsides.symm⟩
    intro hout
    apply hi
    unfold MacroData.IsOuter at hout ⊢
    rw [hsides, ← howner]
    exact hout
  have hadj_orig : ∀ t u, F.kind t = .original →
      (F.adj t u ↔ u ∈ F.ordinary t) := by
    intro t u ht
    apply existsMacroCertificate_seed2_routing_step9_g6_adj_original cd g1 g5
    change existsMacroCertificate_seed2_routing_step9_g6_kind cd.D t = .original at ht
    exact (existsMacroCertificate_seed2_routing_step9_g6_kind_original cd.D t).1 ht
  have hconn : ∀ t u, F.template t = F.template u →
      Relation.ReflTransGen F.adj t u := by
    intro t u howner
    have hr := g1.connected (cd.D.owner t)
      (⟨t, rfl⟩ : {v // cd.D.owner v = cd.D.owner t})
      (⟨u, howner.symm⟩ : {v // cd.D.owner v = cd.D.owner t})
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    apply Relation.ReflTransGen.lift Subtype.val _ hr
    intro a b hab
    rw [MacroData.innerGraph, SimpleGraph.fromRel_adj] at hab
    have hab' : a.1 ≠ b.1 := fun h => hab.1 (Subtype.ext h)
    rcases hab.2 with h | h
    · exact ⟨hab', b.2.trans a.2.symm, h⟩
    · exact hadj_symm b.1 a.1 ⟨hab'.symm, a.2.trans b.2.symm, h⟩
  have hthree : ∀ t, ∃ a b, a ≠ t ∧ b ≠ t ∧ a ≠ b ∧
      F.template a = F.template t ∧ F.template b = F.template t := by
    intro t
    have hc : 2 < Fintype.card {v : cd.D.Typ // cd.D.owner v = cd.D.owner t} := by
      simpa [Nat.card_eq_fintype_card] using g1.three_le (cd.D.owner t)
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hc
    by_cases hat : a.1 = t
    · refine ⟨b.1, c.1, ?_, ?_, ?_, b.2, c.2⟩
      · exact fun h => hab (Subtype.ext (hat.trans h.symm))
      · exact fun h => hac (Subtype.ext (hat.trans h.symm))
      · exact fun h => hbc (Subtype.ext h)
    · by_cases hbt : b.1 = t
      · refine ⟨a.1, c.1, hat, ?_, ?_, a.2, c.2⟩
        · exact fun h => hbc (Subtype.ext (hbt.trans h.symm))
        · exact fun h => hac (Subtype.ext h)
      · exact ⟨a.1, b.1, hat, hbt, fun h => hab (Subtype.ext h), a.2, b.2⟩
  have horig_ne : ∀ t, F.kind t = .original → F.ordinary t ≠ 0 := by
    intro t ht
    have ht' : cd.D.kind (cd.D.form t) = .original := by
      change existsMacroCertificate_seed2_routing_step9_g6_kind cd.D t = .original at ht
      exact (existsMacroCertificate_seed2_routing_step9_g6_kind_original cd.D t).1 ht
    obtain ⟨i, hi⟩ := g1.inner_side t
    have hv : (cd.D.partner (cd.D.occ t i)).1 ∈ F.ordinary t := by
      change (cd.D.partner (cd.D.occ t i)).1 ∈
        existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D t
      rw [existsMacroCertificate_seed2_routing_step9_g6_mem_ordinary]
      exact ⟨i,
      (existsMacroCertificate_seed2_routing_step9_g6_original_fingerprint
        cd g5 t ht' i).2 hi, rfl⟩
    exact fun hz => by simp [hz] at hv
  have horig_le : ∀ t, F.kind t = .original →
      Multiset.card (F.ordinary t) ≤ g.M.K0 := by
    intro t ht
    have ht' : cd.D.kind (cd.D.form t) = .original := by
      change existsMacroCertificate_seed2_routing_step9_g6_kind cd.D t = .original at ht
      exact (existsMacroCertificate_seed2_routing_step9_g6_kind_original cd.D t).1 ht
    obtain ⟨p, hp⟩ := (cd.kind_original (cd.D.form t)).1 ht'
    have hn : (cd.D.Q.disk (cd.D.form t)).n ≤ g.M.K0 := by
      calc
        (cd.D.Q.disk (cd.D.form t)).n =
            (cd.D.Q.disk (cd.D.form t)).vertexSet.ncard := by
          rw [PolygonalDisk.vertexSet, Set.ncard_range_of_injective
            (cd.D.Q.disk (cd.D.form t)).vertex_injective,
            Nat.card_eq_fintype_card, Fintype.card_fin]
        _ = (pdTranslate
              (s.setup.GS.G.mixed.disk (cd.catalogueTile (cd.D.form t)).form)
              (cd.catalogueTile (cd.D.form t)).anchor).vertexSet.ncard := by
          rw [cd.disk_vertexSet]
        _ = (s.setup.GS.G.mixed.disk (cd.catalogueTile (cd.D.form t)).form).n := by
          rw [PolygonalDisk.vertexSet, Set.ncard_range_of_injective
            (pdTranslate _ _).vertex_injective,
            Nat.card_eq_fintype_card, Fintype.card_fin]
          rfl
        _ = (P.disk p).n := by simp [hp]
        _ ≤ g.M.K0 := g.M.sides_le p
    calc
      Multiset.card (F.ordinary t) ≤ Fintype.card (cd.D.Side t) := by
        change Multiset.card
          (existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D t) ≤ _
        rw [existsMacroCertificate_seed2_routing_step9_g6_ordinary]
        calc
          Multiset.card (∑ i ∈ Finset.univ.filter (fun i : cd.D.Side t =>
              cd.D.IsFingerprintSide (cd.D.occ t i)),
                ({(cd.D.partner (cd.D.occ t i)).1} : Multiset cd.D.Typ)) =
              (Finset.univ.filter (fun i : cd.D.Side t =>
                cd.D.IsFingerprintSide (cd.D.occ t i))).card := by simp
          _ ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = Fintype.card (cd.D.Side t) := Finset.card_univ
      _ = (cd.D.Q.disk (cd.D.form t)).n := Fintype.card_fin _
      _ ≤ g.M.K0 := hn
  have hsep := fingerprintSeparation F g.M.K0 htmpl
    (fun t u ht hu =>
      existsMacroCertificate_seed2_routing_step9_g6_original_count cd g1 g5 t u
        (by
          change existsMacroCertificate_seed2_routing_step9_g6_kind cd.D t = .original at ht
          exact (existsMacroCertificate_seed2_routing_step9_g6_kind_original cd.D t).1 ht)
        (by
          change existsMacroCertificate_seed2_routing_step9_g6_kind cd.D u = .original at hu
          exact (existsMacroCertificate_seed2_routing_step9_g6_kind_original cd.D u).1 hu))
    hadj_symm hadj_orig hconn hthree horig_ne horig_le hsmall hprivate
  intro t u htu ht hu
  rw [← existsMacroCertificate_seed2_routing_step9_g6_possible cd g5 t ht,
    ← existsMacroCertificate_seed2_routing_step9_g6_possible cd g5 u hu]
  exact hsep t u (by
    intro h
    have hl : cd.D.kind (cd.D.form t) = .large := by
      change existsMacroCertificate_seed2_routing_step9_g6_kind cd.D t = .central at h
      exact (existsMacroCertificate_seed2_routing_step9_g6_kind_central cd.D t).1 h
    exact ht ((g5.large_iff t).mp hl).symm)
    (by
      intro h
      have hl : cd.D.kind (cd.D.form u) = .large := by
        change existsMacroCertificate_seed2_routing_step9_g6_kind cd.D u = .central at h
        exact (existsMacroCertificate_seed2_routing_step9_g6_kind_central cd.D u).1 h
      exact hu ((g5.large_iff u).mp hl).symm)
    htu

private lemma existsMacroCertificate_seed2_routing_step9_g6_side_of_template
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing) (t : cd.D.Typ)
    {γ : s.setup.GS.G.P'.Form}
    (hform : (cd.catalogueTile (cd.D.form t)).form = Sum.inl γ)
    {e : Set Pt} (he : HasEdge (cd.templateChild t) e) :
    ∃ i : cd.D.Side t, cd.D.occSide (cd.D.occ t i) = e := by
  have hemem : e ∈ Set.range (fun j => (cd.templateChild t).side j) := by
    rcases he with ⟨j, rfl⟩
    exact Set.mem_range_self j
  rw [← cd.child_sideSet t] at hemem
  exact hemem

private lemma existsMacroCertificate_seed2_routing_step9_g6_side_of_original
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing) (t : cd.D.Typ)
    {p : P.Form} (hform : (cd.catalogueTile (cd.D.form t)).form = Sum.inr p)
    {e : Set Pt} (he : HasEdge (cd.templateChild t) e) :
    ∃ i : cd.D.Side t, cd.D.occSide (cd.D.occ t i) = e := by
  have hemem : e ∈ Set.range (fun j => (cd.templateChild t).side j) := by
    rcases he with ⟨j, rfl⟩
    exact Set.mem_range_self j
  rw [← cd.child_sideSet t] at hemem
  exact hemem

private lemma existsMacroCertificate_seed2_routing_step9_g6_region
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing) (α : cd.D.Q.Form) :
    cd.D.macroRegion α = (s.setup.retained l (cd.baseForm α)).region := by
  unfold MacroData.macroRegion
  rw [← cd.D.σ.support_eq, cd.tmpl.rule_eq,
    ← (s.setup.retained l (cd.baseForm α)).support_eq]
  ext x
  simp only [support, Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨A, ⟨t, ht, rfl⟩, hx⟩
    refine ⟨cd.templateChild t, (cd.child_bijective α).1 ht, ?_⟩
    rw [← cd.child_carrier]
    exact hx
  · rintro ⟨X, hX, hx⟩
    obtain ⟨t, ht, htx⟩ := (cd.child_bijective α).2.2 hX
    refine ⟨cd.D.childTile t, ⟨t, ht, rfl⟩, ?_⟩
    rw [cd.child_carrier, htx]
    exact hx

private lemma existsMacroCertificate_seed2_routing_step9_g6_private_inner
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing) {t : cd.D.Typ}
    {j : Fin (4 * s.setup.N (cd.baseForm (cd.D.owner t)))} {e : Set Pt}
    (he : e ∈ privateOuterEdges
      (s.setup.annulus l (cd.baseForm (cd.D.owner t)) cd.l_pos) j)
    {i : cd.D.Side t} (hi : cd.D.occSide (cd.D.occ t i) = e) :
    cd.D.IsInner (cd.D.occ t i) := by
  intro hout
  have heint : e ⊆ interior
      (s.setup.retained l (cd.baseForm (cd.D.owner t))).region := by
    refine he.2.1.trans ?_
    refine (frontier_subset_closure.trans ?_).trans
      (existsRoutingAfterPower_step2_ports_step1_intra_step2_clearance_H_in_region
        τ g.M s.setup l cd.l_pos (cd.baseForm (cd.D.owner t)))
    change closure
      (s.setup.annulus l (cd.baseForm (cd.D.owner t)) cd.l_pos).H.disk.carrier ⊆ _
    rw [(s.setup.annulus l (cd.baseForm (cd.D.owner t))
      cd.l_pos).H.disk.compact.isClosed.closure_eq]
    exact Set.Subset.rfl
  have hefront : e ⊆ frontier (cd.D.macroRegion (cd.D.owner t)) := by
    rw [← hi]
    exact hout
  have hregion := existsMacroCertificate_seed2_routing_step9_g6_region cd (cd.D.owner t)
  rw [← hregion] at heint
  obtain ⟨A, -, k, hk⟩ := he.1
  have hne : e.Nonempty := by
    rw [← hk, PlacedTile.side]
    exact ⟨_, Set.vadd_mem_vadd_set (left_mem_segment ℝ _ _)⟩
  obtain ⟨x, hx⟩ := hne
  exact Set.disjoint_left.1 disjoint_interior_frontier (heint hx) (hefront hx)

private lemma existsMacroCertificate_seed2_routing_step9_g6_private_occurrence
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing)
    (g1 : existsMacroCertificate_G1Data cd.D)
    (g5 : existsMacroCertificate_G5Data cd.D) (t : cd.D.Typ)
    (ht : cd.D.kind (cd.D.form t) = .small)
    {γ : s.setup.GS.G.P'.Form}
    (hform : (cd.catalogueTile (cd.D.form t)).form = Sum.inl γ)
    {j : Fin (4 * s.setup.N (cd.baseForm (cd.D.owner t)))}
    (hpiece : s.setup.GS.G.mixedScatterTile (cd.templateChild t) =
      ((s.setup.annulus l (cd.baseForm (cd.D.owner t)) cd.l_pos).spokes.piece j).faces)
    {e : Set Pt}
    (he : e ∈ privateOuterEdges
      (s.setup.annulus l (cd.baseForm (cd.D.owner t)) cd.l_pos) j) :
    ∃ (i : cd.D.Side t) (u : cd.D.Typ),
      cd.D.IsFingerprintSide (cd.D.occ t i) ∧
      (cd.D.partner (cd.D.occ t i)).1 = u ∧
      cd.D.kind (cd.D.form u) = .original ∧ cd.D.occSide (cd.D.occ t i) = e ∧
      ∀ k, k ≠ j → Disjoint (cd.templateChild u).carrier
        ((s.setup.annulus l (cd.baseForm (cd.D.owner t)) cd.l_pos).spokes.piece k).carrier := by
  let α := cd.D.owner t
  have htmem : cd.templateChild t ∈
      (s.setup.retained l (cd.baseForm α)).children.tiles :=
    (cd.child_bijective α).1 rfl
  have htcentral : cd.templateChild t ≠ s.setup.central l (cd.baseForm α) := by
    intro h
    have htc : t = cd.D.central α := by
      apply (cd.child_bijective α).2.1 rfl (cd.central_owner α)
      rw [cd.central_child, h]
    have hlarge : cd.D.kind (cd.D.form t) = .large := by
      apply (g5.large_iff t).2
      rw [htc, cd.central_owner]
    exact FormKind.noConfusion (ht.symm.trans hlarge)
  obtain ⟨F, q, hFmem, ⟨p, hp⟩, hFe, hqint, hqout⟩ :=
    existsRoutingAfterPower_step3_entries_step2_outside τ g.M s.setup l cd.l_pos
      (cd.baseForm α) he
  obtain ⟨u, huowner, huF⟩ := (cd.child_bijective α).2.2 hFmem
  have hucatalogue : (cd.catalogueTile (cd.D.form u)).form = Sum.inr p := by
    rw [← cd.child_form u, huF, hp]
  have huorig : cd.D.kind (cd.D.form u) = .original :=
    (cd.kind_original (cd.D.form u)).2 ⟨p, hucatalogue⟩
  have htu : t ≠ u := by
    intro htu
    rw [← htu, hform] at hucatalogue
    cases hucatalogue
  have hte := existsRoutingAfterPower_step3_entries_step3_listed τ g.M s.setup l cd.l_pos
    (cd.baseForm α) htmem hpiece he
  obtain ⟨i, hi⟩ :=
    existsMacroCertificate_seed2_routing_step9_g6_side_of_template cd t hform hte
  obtain ⟨k, hk⟩ :=
    existsMacroCertificate_seed2_routing_step9_g6_side_of_original cd u hucatalogue (huF ▸ hFe)
  have hinner := existsMacroCertificate_seed2_routing_step9_g6_private_inner cd he hi
  have hpartner : cd.D.occ u k = cd.D.partner (cd.D.occ t i) :=
    g1.side_unique (cd.D.occ t i) (cd.D.occ u k) hinner huowner htu.symm
      (hk.trans hi.symm)
  have hnot_special : ¬ cd.D.special (cd.D.occ t i) := by
    intro hs
    have hc := (cd.special_contact (cd.D.occ t i) hs).2
    have huc : u = cd.D.central α := (congrArg Sigma.fst hpartner).trans hc
    have hlarge : cd.D.kind (cd.D.form u) = .large := by
      apply (g5.large_iff u).2
      rw [huc, cd.central_owner]
    exact FormKind.noConfusion (huorig.symm.trans hlarge)
  have hnot_print : ¬ cd.D.IsPrint (cd.D.occ t i) := by
    rintro ⟨d, hd, ho | ho⟩
    · have htc : t = cd.D.central α := congrArg Sigma.fst ho
      have hlarge : cd.D.kind (cd.D.form t) = .large := by
        apply (g5.large_iff t).2
        rw [htc, cd.central_owner]
      exact FormKind.noConfusion (ht.symm.trans hlarge)
    · have hpinner := cd.print_inner α d hd
      have hpp := g1.partner_partner (cd.D.printOcc α d) hpinner
      have hpo : cd.D.partner (cd.D.occ t i) = cd.D.printOcc α d := by
        rw [ho, hpp]
      have huc : u = cd.D.central α := by
        exact (congrArg Sigma.fst hpartner).trans
          (congrArg (fun o : cd.D.SideOcc => o.1) hpo)
      have hlarge : cd.D.kind (cd.D.form u) = .large := by
        apply (g5.large_iff u).2
        rw [huc, cd.central_owner]
      exact FormKind.noConfusion (huorig.symm.trans hlarge)
  refine ⟨i, u, ⟨hinner, ⟨hnot_special, hnot_print⟩, ?_⟩, ?_, huorig, hi, ?_⟩
  · intro _
    exact cd.marked_rule_nonlarge (cd.D.occ t i) (Or.inl (by simp [ht]))
  · rw [← hpartner]
  · intro k hkj
    obtain ⟨A, hApiece, ia, hAe⟩ := he.1
    obtain ⟨F0, hF0S, hF0H, hF0edge, hF0disj⟩ := he.2.2
    obtain ⟨i0, hF0e⟩ := hF0edge
    let S0 := s.setup.GS.G.mixedScatter
      (s.setup.retained l (cd.baseForm α)).children.tiles
    have hAS : A ∈ S0 :=
      (s.setup.annulus l (cd.baseForm α) cd.l_pos).H.faces_sub
        ((s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes.piece_sub j hApiece).1
    have hFPS : (⟨p, F.anchor⟩ : PlacedTile P) ∈ S0 := by
      unfold S0 GroupedFamily.mixedScatter
      exact Set.mem_iUnion.2 ⟨F, Set.mem_iUnion.2 ⟨hFmem, by
        simp [GroupedFamily.mixedScatterTile, hp]⟩⟩
    have hAF0 : A ≠ F0 := fun h => hF0H (h ▸
      ((s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes.piece_sub j hApiece).1)
    have hAFP : A ≠ (⟨p, F.anchor⟩ : PlacedTile P) := by
      intro h
      have hqH : q ∈ (s.setup.annulus l (cd.baseForm α) cd.l_pos).H.carrier := by
        change q ∈ (s.setup.annulus l (cd.baseForm α) cd.l_pos).H.disk.carrier
        rw [(s.setup.annulus l (cd.baseForm α) cd.l_pos).H.carrier_eq]
        have hFPH : (⟨p, F.anchor⟩ : PlacedTile P) ∈
            (s.setup.annulus l (cd.baseForm α) cd.l_pos).H.faces :=
          ((s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes.piece_sub j
            (h ▸ hApiece)).1
        apply carrier_subset_support hFPH
        simpa [PlacedTile.carrier, hp] using interior_subset hqint
      exact hqout ((s.setup.annulus l (cd.baseForm α) cd.l_pos).H_upper hqH)
    have hFPe : HasEdge (⟨p, F.anchor⟩ : PlacedTile P) e := by
      have hFPmixed : F =
          (⟨Sum.inr p, F.anchor⟩ : PlacedTile s.setup.GS.G.mixed) := by
        cases F with
        | mk form anchor => simp_all
      rw [hFPmixed] at hFe
      simpa [PlacedTile.side] using hFe
    obtain ⟨ib, hibe⟩ := hFPe
    have hFPF0 : (⟨p, F.anchor⟩ : PlacedTile P) = F0 :=
      side_partner_unique
        (existsRoutingAfterPower_step3_entries_step2_outside_step2_exterior_step1_disjoint
          s.setup.GS.G (s.setup.retained l (cd.baseForm α)).children) hAS hFPS hF0S
        hAFP hAF0 ia ib i0 (hibe.trans hAe.symm) (hF0e.trans hAe.symm)
    have hcarr : (cd.templateChild u).carrier = F0.carrier := by
      rw [huF, PlacedTile.carrier, hp, ← hFPF0]
      rfl
    rw [hcarr]
    exact hF0disj k hkj

private lemma existsMacroCertificate_seed2_routing_step9_g6_small_piece
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing)
    (g5 : existsMacroCertificate_G5Data cd.D) (t : cd.D.Typ)
    (ht : cd.D.kind (cd.D.form t) = .small) :
    ∃ (γ : s.setup.GS.G.P'.Form)
      (j : Fin (4 * s.setup.N (cd.baseForm (cd.D.owner t)))),
      (cd.catalogueTile (cd.D.form t)).form = Sum.inl γ ∧
      s.setup.GS.G.mixedScatterTile (cd.templateChild t) =
        ((s.setup.annulus l (cd.baseForm (cd.D.owner t)) cd.l_pos).spokes.piece j).faces := by
  obtain ⟨-, γ, -, -, -, -, hform⟩ := (cd.kind_small (cd.D.form t)).1 ht
  have hmem := (cd.child_bijective (cd.D.owner t)).1 rfl
  have hne : cd.templateChild t ≠ s.setup.central l (cd.baseForm (cd.D.owner t)) := by
    intro h
    have htc : t = cd.D.central (cd.D.owner t) := by
      apply (cd.child_bijective (cd.D.owner t)).2.1 rfl (cd.central_owner _)
      rw [cd.central_child, h]
    have hlarge : cd.D.kind (cd.D.form t) = .large := by
      apply (g5.large_iff t).2
      rw [htc, cd.central_owner]
    exact FormKind.noConfusion (ht.symm.trans hlarge)
  have hchildform : (cd.templateChild t).form = Sum.inl γ := cd.child_form t |>.trans hform
  obtain ⟨j, hj⟩ := s.setup.small_scatter l (cd.baseForm (cd.D.owner t)) cd.l_pos
    (cd.templateChild t) hmem hne ⟨γ, hchildform⟩
  exact ⟨γ, j, hform, hj⟩

private lemma existsMacroCertificate_seed2_routing_step9_g6_private_three
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing)
    (g1 : existsMacroCertificate_G1Data cd.D)
    (g5 : existsMacroCertificate_G5Data cd.D) (t u : cd.D.Typ)
    (ht : cd.D.kind (cd.D.form t) = .small)
    (hu : cd.D.kind (cd.D.form u) = .small) (htu : t ≠ u)
    (howner : cd.D.owner t = cd.D.owner u) :
    3 ≤ Multiset.card
      ((existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D t).filter
        (fun v => cd.D.kind (cd.D.form v) = .original ∧
          v ∉ existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D u)) := by
  classical
  obtain ⟨γ, j, hform, hpiece⟩ :=
    existsMacroCertificate_seed2_routing_step9_g6_small_piece cd g5 t ht
  obtain ⟨δ, k, huform, hupiece⟩ :=
    existsMacroCertificate_seed2_routing_step9_g6_small_piece cd g5 u hu
  have hupiece_ex : ∃ k' : Fin (4 * s.setup.N (cd.baseForm (cd.D.owner t))),
      s.setup.GS.G.mixedScatterTile (cd.templateChild u) =
        ((s.setup.annulus l (cd.baseForm (cd.D.owner t)) cd.l_pos).spokes.piece k').faces := by
    rw [howner]
    exact ⟨k, hupiece⟩
  obtain ⟨k', hupiece'⟩ := hupiece_ex
  have hjk : j ≠ k' := by
    intro hjk
    have hscat : s.setup.GS.G.mixedScatterTile (cd.templateChild t) =
        s.setup.GS.G.mixedScatterTile (cd.templateChild u) := by
      rw [hpiece, hupiece', ← hjk]
    have htmem := (cd.child_bijective (cd.D.owner t)).1 rfl
    have humem : cd.templateChild u ∈
        (s.setup.retained l (cd.baseForm (cd.D.owner t))).children.tiles := by
      apply (cd.child_bijective (cd.D.owner t)).1
      exact howner.symm
    have hchild := existsRoutingAfterPower_step3_entries_step4_scatterInj τ g.M s.setup l
      (cd.baseForm (cd.D.owner t)) htmem humem hscat
    exact htu ((cd.child_bijective (cd.D.owner t)).2.1 rfl howner.symm hchild)
  obtain ⟨E, hE, hEsep⟩ := s.setup.windows l (cd.baseForm (cd.D.owner t)) cd.l_pos
  have hocc : ∀ r : Fin 4, ∃ (i : cd.D.Side t) (v : cd.D.Typ),
      cd.D.IsFingerprintSide (cd.D.occ t i) ∧
      (cd.D.partner (cd.D.occ t i)).1 = v ∧
      cd.D.kind (cd.D.form v) = .original ∧ cd.D.occSide (cd.D.occ t i) = E j r ∧
      v ∉ existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D u := by
    intro r
    obtain ⟨i, v, hi, hiv, hvorig, hie, hvdisj⟩ :=
      existsMacroCertificate_seed2_routing_step9_g6_private_occurrence
        cd g1 g5 t ht hform hpiece (hE j r)
    refine ⟨i, v, hi, hiv, hvorig, hie, ?_⟩
    intro hv
    rcases (existsMacroCertificate_seed2_routing_step9_g6_mem_ordinary cd.D u v).1 hv with
      ⟨m, hm, hmv⟩
    have hp := g1.partner (cd.D.occ u m) hm.1
    rcases heq : cd.D.partner (cd.D.occ u m) with ⟨w, n⟩
    simp only [heq] at hmv hp
    subst w
    have hside_u : cd.D.occSide (cd.D.occ v n) = cd.D.occSide (cd.D.occ u m) := hp.2.2
    let x := cd.D.occStart (cd.D.occ u m)
    have hxsideu : x ∈ cd.D.occSide (cd.D.occ u m) := by
      unfold x MacroData.occStart MacroData.occSide MacroData.childTile PlacedTile.side
      exact Set.vadd_mem_vadd_set (left_mem_segment ℝ _ _)
    have hxu : x ∈ (cd.D.childTile u).carrier := by
      apply tile_side_subset (cd.D.childTile u) m
      exact hxsideu
    have hxv : x ∈ (cd.D.childTile v).carrier := by
      apply tile_side_subset (cd.D.childTile v) n
      change x ∈ cd.D.occSide (cd.D.occ v n)
      rw [hside_u]
      exact hxsideu
    have hxvu : x ∈ (cd.templateChild v).carrier := cd.child_carrier v ▸ hxv
    have hxuu : x ∈ (cd.templateChild u).carrier := cd.child_carrier u ▸ hxu
    have hxpiece : x ∈
        ((s.setup.annulus l (cd.baseForm (cd.D.owner t)) cd.l_pos).spokes.piece k').carrier := by
      rw [existsRoutingAfterPower_step2_ports_step1_intra_step2_clearance_scatter_carrier,
        hupiece', ←
        ((s.setup.annulus l (cd.baseForm (cd.D.owner t)) cd.l_pos).spokes.piece k').carrier_eq]
        at hxuu
      exact hxuu
    exact Set.disjoint_left.1 (hvdisj _ hjk.symm) hxvu hxpiece
  choose I V hI using hocc
  have hR : 0 < s.setup.R (cd.baseForm (cd.D.owner t)) := by
    have hlarge := s.setup.R_large (cd.baseForm (cd.D.owner t))
    exact lt_of_lt_of_le (by have := g.M.D_pos; positivity) hlarge
  have hI_ne : ∀ a b : Fin 4, a ≠ b → I a ≠ I b := by
    intro a b hab hIab
    obtain ⟨A, -, ia, hia⟩ := (hE j a).1
    have hx : (E j a).Nonempty := by
      rw [← hia, PlacedTile.side]
      exact ⟨_, Set.vadd_mem_vadd_set (left_mem_segment ℝ _ _)⟩
    obtain ⟨x, hx⟩ := hx
    have hsets : E j a = E j b := by rw [← (hI a).2.2.2.1, ← (hI b).2.2.2.1, hIab]
    have hd := hEsep j a j b (by simp [hab]) x hx x (hsets ▸ hx)
    rw [dist_self] at hd
    linarith
  have hcard : 3 ≤ (Finset.univ.filter fun i : cd.D.Side t =>
      cd.D.IsFingerprintSide (cd.D.occ t i) ∧
        (cd.D.kind (cd.D.form (cd.D.partner (cd.D.occ t i)).1) = .original ∧
          (cd.D.partner (cd.D.occ t i)).1 ∉
            existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D u)).card := by
    rw [show 3 = 2 + 1 by omega, ← Nat.lt_iff_add_one_le, Finset.two_lt_card_iff]
    refine ⟨I 0, I 1, I 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hI 0).2.1]
      exact ⟨(hI 0).1, (hI 0).2.2.1, (hI 0).2.2.2.2⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hI 1).2.1]
      exact ⟨(hI 1).1, (hI 1).2.2.1, (hI 1).2.2.2.2⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hI 2).2.1]
      exact ⟨(hI 2).1, (hI 2).2.2.1, (hI 2).2.2.2.2⟩
    · exact hI_ne 0 1 (by decide)
    · exact hI_ne 0 2 (by decide)
    · exact hI_ne 1 2 (by decide)
  let pred : cd.D.Typ → Prop := fun v =>
    cd.D.kind (cd.D.form v) = .original ∧
      v ∉ existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D u
  have haux : ∀ R : Finset (cd.D.Side t),
      Multiset.card (Multiset.filter pred
        (∑ i ∈ R, ({(cd.D.partner (cd.D.occ t i)).1} : Multiset cd.D.Typ))) =
        (R.filter fun i => pred (cd.D.partner (cd.D.occ t i)).1).card := by
    intro R
    induction R using Finset.induction_on with
    | empty => simp
    | @insert a R ha ih =>
        rw [Finset.sum_insert ha, Multiset.filter_add, Multiset.card_add,
          Finset.filter_insert]
        by_cases hp : pred (cd.D.partner (cd.D.occ t a)).1
        · simp only [Multiset.filter_singleton, if_pos hp, Multiset.card_singleton]
          have hnot : a ∉ R.filter (fun i => pred (cd.D.partner (cd.D.occ t i)).1) :=
            fun hmem => ha (Finset.filter_subset _ _ hmem)
          rw [Finset.card_insert_of_notMem hnot, ih]
          omega
        · simp [hp, ih]
  change 3 ≤ Multiset.card (Multiset.filter pred
    (∑ i ∈ Finset.univ.filter (fun i : cd.D.Side t =>
      cd.D.IsFingerprintSide (cd.D.occ t i)),
        ({(cd.D.partner (cd.D.occ t i)).1} : Multiset cd.D.Typ)))
  rw [haux]
  simpa [pred, Finset.filter_filter, and_assoc] using hcard

private lemma existsMacroCertificate_seed2_routing_step9_g6_hasEdge_of_scatter_boundary
    (G : GroupedFamily P) {X : PlacedTile G.mixed} {F : Set (PlacedTile P)}
    (hX : G.mixedScatterTile X = F) {e : Set Pt}
    (hA : ∃ A ∈ F, HasEdge A e) (hBoundary : e ⊆ frontier X.carrier) : HasEdge X e := by
  obtain ⟨A, hA, i, hAi⟩ := hA
  obtain ⟨form, v⟩ := X
  rcases form with β | p
  · change translateSet v (G.dissect β).tiles = F at hX
    change e ⊆ frontier (v +ᵥ (G.P'.disk β).carrier) at hBoundary
    rw [← hX] at hA
    obtain ⟨A₀, hA₀, rfl⟩ := hA
    have hside : (A₀.translate v).side i = v +ᵥ A₀.side i := by
      simp only [PlacedTile.side, PlacedTile.translate, vadd_vadd, vadd_eq_add]
    subst hAi
    rw [hside] at hBoundary
    have hfr : frontier (v +ᵥ (G.P'.disk β).carrier) =
        v +ᵥ frontier (G.P'.disk β).carrier := by
      have h := (Homeomorph.addLeft v).image_frontier (G.P'.disk β).carrier
      rw [← Set.image_vadd, ← Set.image_vadd]
      exact h.symm
    rw [hfr, vadd_set_subset_vadd_set_iff] at hBoundary
    obtain ⟨k, hk⟩ :=
      existsRoutingAfterPower_step3_entries_step3_listed_step3_hasEdge_step3_groupSide
        G β hA₀ i hBoundary
    refine ⟨k, ?_⟩
    rw [hside]
    change v +ᵥ (G.P'.disk β).side k = _
    rw [hk]
  · change ({⟨p, v⟩} : Set (PlacedTile P)) = F at hX
    rw [← hX, Set.mem_singleton_iff] at hA
    subst hA
    exact ⟨i, hAi⟩

private lemma existsMacroCertificate_seed2_routing_step9_g6_catalogue_occurrence
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing)
    (g1 : existsMacroCertificate_G1Data cd.D)
    (g5 : existsMacroCertificate_G5Data cd.D) (t : cd.D.Typ)
    (ht : cd.D.kind (cd.D.form t) = .small)
    {γ : s.setup.GS.G.P'.Form}
    (hform : (cd.catalogueTile (cd.D.form t)).form = Sum.inl γ)
    {j : Fin (4 * s.setup.N (cd.baseForm (cd.D.owner t)))}
    (hpiece : s.setup.GS.G.mixedScatterTile (cd.templateChild t) =
      ((s.setup.annulus l (cd.baseForm (cd.D.owner t)) cd.l_pos).spokes.piece j).faces)
    (p : P.Form) (v : Pt) (j' : Fin (4 * g.N))
    (hpiece' :
      ((s.setup.annulus l (cd.baseForm (cd.D.owner t)) cd.l_pos).spokes.piece j).faces =
        translateSet v ((g.annular p).spokes.piece j').faces)
    (hcentral : s.setup.GS.G.mixedScatterTile
      (s.setup.central l (cd.baseForm (cd.D.owner t))) =
        translateSet v (g.annular p).L.faces)
    {e : Set Pt} (he : e ∈ privateOuterEdges (g.annular p) j') :
    ∃ i : cd.D.Side t, cd.D.IsFingerprintSide (cd.D.occ t i) ∧
      cd.D.occSide (cd.D.occ t i) = v +ᵥ e := by
  let α := cd.D.owner t
  let K := (g.annular p).spokes.piece j'
  let H := (g.annular p).H
  obtain ⟨A, hAK, k, hke⟩ := he.1
  have heK : e ⊆ frontier K.carrier := by
    intro x hx
    have hxK : x ∈ K.carrier := by
      change x ∈ K.disk.carrier
      rw [K.carrier_eq]
      exact Set.mem_biUnion hAK
        (existsRoutingAfterPower_step3_entries_step3_listed_step2_boundary_step3_side
          ⟨k, hke⟩ hx)
    exact existsRoutingAfterPower_step3_entries_step3_listed_step2_boundary_step4_frontier
      K H (fun B hB => ((g.annular p).spokes.piece_sub j' hB).1) hxK (he.2.1 hx)
  have hchild : (cd.templateChild t).carrier = v +ᵥ K.carrier := by
    change (cd.templateChild t).carrier = v +ᵥ K.disk.carrier
    rw [existsRoutingAfterPower_step2_ports_step1_intra_step2_clearance_scatter_carrier,
      hpiece, hpiece',
      existsRoutingAfterPower_step3_entries_step3_listed_step2_boundary_step1_translate,
      K.carrier_eq]
  have hechild : v +ᵥ e ⊆ frontier (cd.templateChild t).carrier := by
    rw [hchild]
    have hfr : frontier (v +ᵥ K.carrier) = v +ᵥ frontier K.carrier := by
      have h := (Homeomorph.addLeft v).image_frontier K.carrier
      rw [← Set.image_vadd, ← Set.image_vadd]
      exact h.symm
    rw [hfr, vadd_set_subset_vadd_set_iff]
    exact heK
  have hAtranslate : A.translate v ∈
      s.setup.GS.G.mixedScatterTile (cd.templateChild t) := by
    rw [hpiece, hpiece']
    exact ⟨A, hAK, rfl⟩
  have hAinPiece : A.translate v ∈
      ((s.setup.annulus l (cd.baseForm (cd.D.owner t)) cd.l_pos).spokes.piece j).faces := by
    rw [hpiece']
    exact ⟨A, hAK, rfl⟩
  have hAedge : HasEdge (A.translate v) (v +ᵥ e) := by
    refine ⟨k, ?_⟩
    rw [← hke]
    simp only [PlacedTile.side, PlacedTile.translate, vadd_vadd, vadd_eq_add]
  have hte : HasEdge (cd.templateChild t) (v +ᵥ e) :=
    existsMacroCertificate_seed2_routing_step9_g6_hasEdge_of_scatter_boundary
      s.setup.GS.G hpiece ⟨A.translate v, hAinPiece, hAedge⟩ hechild
  obtain ⟨i, hi⟩ :=
    existsMacroCertificate_seed2_routing_step9_g6_side_of_template cd t hform hte
  have hinner : cd.D.IsInner (cd.D.occ t i) := by
    intro hout
    have heint : v +ᵥ e ⊆ interior
        (s.setup.retained l (cd.baseForm α)).region := by
      rw [← hi]
      refine (cd.child_carrier t ▸ tile_side_subset (cd.D.childTile t) i).trans ?_
      rw [existsRoutingAfterPower_step2_ports_step1_intra_step2_clearance_scatter_carrier,
        hpiece, ←
        ((s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes.piece j).carrier_eq]
      have hsub :
          ((s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes.piece j).carrier ⊆
            (s.setup.annulus l (cd.baseForm α) cd.l_pos).H.carrier := by
        change
          ((s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes.piece j).disk.carrier ⊆
            (s.setup.annulus l (cd.baseForm α) cd.l_pos).H.disk.carrier
        rw [((s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes.piece j).carrier_eq,
          (s.setup.annulus l (cd.baseForm α) cd.l_pos).H.carrier_eq]
        intro x hx
        obtain ⟨A, hA, hxA⟩ := mem_support_iff'.1 hx
        exact carrier_subset_support
          ((s.setup.annulus l (cd.baseForm α) cd.l_pos).spokes.piece_sub j hA).1 hxA
      exact hsub.trans
        (existsRoutingAfterPower_step2_ports_step1_intra_step2_clearance_H_in_region
          τ g.M s.setup l cd.l_pos (cd.baseForm α))
    have hefront : v +ᵥ e ⊆ frontier (cd.D.macroRegion (cd.D.owner t)) := by
      rw [← hi]
      exact hout
    rw [← existsMacroCertificate_seed2_routing_step9_g6_region cd α] at heint
    have hne : (v +ᵥ e).Nonempty := by
      rw [← hke, PlacedTile.side]
      exact ⟨_, Set.vadd_mem_vadd_set
        (Set.vadd_mem_vadd_set (left_mem_segment ℝ _ _))⟩
    obtain ⟨x, hx⟩ := hne
    exact Set.disjoint_left.1 disjoint_interior_frontier (heint hx) (hefront hx)
  have hcentralCarrier :
      (s.setup.central l (cd.baseForm α)).carrier = v +ᵥ (g.annular p).L.carrier := by
    change (s.setup.central l (cd.baseForm α)).carrier =
      v +ᵥ (g.annular p).L.disk.carrier
    rw [existsRoutingAfterPower_step2_ports_step1_intra_step2_clearance_scatter_carrier,
      hcentral,
      existsRoutingAfterPower_step3_entries_step3_listed_step2_boundary_step1_translate,
      (g.annular p).L.carrier_eq]
  have hLH : (g.annular p).L.carrier ⊆ interior (g.annular p).H.carrier := by
    have hR : 0 < g.R := by
      have h0 : 0 ≤ (g.M.K0 : ℝ) := Nat.cast_nonneg _
      have := g.R_routes
      have := g.M.D_pos
      nlinarith
    have hD := g.M.D_pos
    have hb : 0 ≤ (g.N : ℝ) * g.R / 2 + g.R := by positivity
    have hnest : square (g.centre p) ((g.N : ℝ) * g.R / 2) + Binf g.M.D ⊆
        interior (square (g.centre p) ((g.N : ℝ) * g.R / 2 + g.R) +
          Binf (2 * g.M.D)) :=
      existsAnnularSpokes_step1_nest (g.centre p) (by linarith) hb (by linarith)
    exact (g.annular p).L_upper.trans
      (hnest.trans (interior_mono (g.annular p).H_lower))
  have hdisj : Disjoint (v +ᵥ e)
      (s.setup.central l (cd.baseForm α)).carrier := by
    rw [hcentralCarrier]
    apply Set.disjoint_vadd_set.2
    exact (disjoint_interior_frontier.mono hLH he.2.1).symm
  have hnot_special : ¬ cd.D.special (cd.D.occ t i) := by
    intro hs
    have hc := (cd.special_contact (cd.D.occ t i) hs).2
    have hp := g1.partner (cd.D.occ t i) hinner
    have hx : (v +ᵥ e).Nonempty := by
      rw [← hke, PlacedTile.side]
      exact ⟨_, Set.vadd_mem_vadd_set
        (Set.vadd_mem_vadd_set (left_mem_segment ℝ _ _))⟩
    obtain ⟨x, hx⟩ := hx
    apply Set.disjoint_left.1 hdisj hx
    have hxside : x ∈ cd.D.occSide (cd.D.partner (cd.D.occ t i)) := by
      rw [hp.2.2, hi]
      exact hx
    have hxcarrier : x ∈
        (cd.templateChild (cd.D.partner (cd.D.occ t i)).1).carrier :=
      cd.child_carrier _ ▸ tile_side_subset _ _ hxside
    rw [hc, cd.central_child] at hxcarrier
    exact hxcarrier
  have hnot_print : ¬ cd.D.IsPrint (cd.D.occ t i) := by
    rintro ⟨d, hd, ho | ho⟩
    · have htc : t = cd.D.central α := congrArg Sigma.fst ho
      have hlarge : cd.D.kind (cd.D.form t) = .large := by
        apply (g5.large_iff t).2
        rw [htc, cd.central_owner]
      exact FormKind.noConfusion (ht.symm.trans hlarge)
    · have hpinner := cd.print_inner α d hd
      have hpp := g1.partner_partner (cd.D.printOcc α d) hpinner
      have hpo : cd.D.partner (cd.D.occ t i) = cd.D.printOcc α d := by
        rw [ho, hpp]
      have hc : (cd.D.partner (cd.D.occ t i)).1 = cd.D.central α := by
        exact congrArg (fun o : cd.D.SideOcc => o.1) hpo
      have hp := g1.partner (cd.D.occ t i) hinner
      have hx : (v +ᵥ e).Nonempty := by
        rw [← hke, PlacedTile.side]
        exact ⟨_, Set.vadd_mem_vadd_set
          (Set.vadd_mem_vadd_set (left_mem_segment ℝ _ _))⟩
      obtain ⟨x, hx⟩ := hx
      apply Set.disjoint_left.1 hdisj hx
      have hxside : x ∈ cd.D.occSide (cd.D.partner (cd.D.occ t i)) := by
        rw [hp.2.2, hi]
        exact hx
      have hxcarrier : x ∈
          (cd.templateChild (cd.D.partner (cd.D.occ t i)).1).carrier :=
        cd.child_carrier _ ▸ tile_side_subset _ _ hxside
      rw [hc, cd.central_child] at hxcarrier
      exact hxcarrier
  refine ⟨i, ⟨hinner, ⟨hnot_special, hnot_print⟩, ?_⟩, hi⟩
  intro _
  exact cd.marked_rule_nonlarge (cd.D.occ t i) (Or.inl (by simp [ht]))

private lemma existsMacroCertificate_seed2_routing_step9_g6_small_many
    {τ : Substitution P} {g : existsMacroCertificate_GroupingSeed τ}
    {s : existsMacroCertificate_SetupSeed τ g} {l : ℕ}
    {routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding)}
    (cd : existsMacroCertificate_CertData τ g s l routing)
    (g1 : existsMacroCertificate_G1Data cd.D)
    (g5 : existsMacroCertificate_G5Data cd.D) (t : cd.D.Typ)
    (ht : cd.D.kind (cd.D.form t) = .small) :
    g.M.K0 + 2 ≤ Multiset.card
      (existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D t) := by
  classical
  obtain ⟨γ, j, hform, hpiece⟩ :=
    existsMacroCertificate_seed2_routing_step9_g6_small_piece cd g5 t ht
  obtain ⟨p, v, hcentral, hpieces⟩ :=
    s.annulus_catalogue l (cd.baseForm (cd.D.owner t)) cd.l_pos
  obtain ⟨j', -, hpiece'⟩ := hpieces j
  let E := privateOuterEdges (g.annular p) j'
  have hocc : ∀ e : E, ∃ i : cd.D.Side t,
      cd.D.IsFingerprintSide (cd.D.occ t i) ∧
        cd.D.occSide (cd.D.occ t i) = v +ᵥ (e : Set Pt) := by
    intro e
    exact existsMacroCertificate_seed2_routing_step9_g6_catalogue_occurrence
      cd g1 g5 t ht hform hpiece p v j' hpiece' hcentral e.property
  choose I hI using hocc
  let T := {i : cd.D.Side t // cd.D.IsFingerprintSide (cd.D.occ t i)}
  let f : E → T := fun e => ⟨I e, (hI e).1⟩
  have hf : Function.Injective f := by
    intro e e' heq
    apply Subtype.ext
    have hsides : v +ᵥ (e : Set Pt) = v +ᵥ (e' : Set Pt) := by
      rw [← (hI e).2, ← (hI e').2]
      exact congrArg (fun i : cd.D.Side t => cd.D.occSide (cd.D.occ t i))
        (congrArg Subtype.val heq)
    exact Set.Subset.antisymm
      (vadd_set_subset_vadd_set_iff.mp hsides.le)
      (vadd_set_subset_vadd_set_iff.mp hsides.ge)
  have hcard : E.ncard ≤ Multiset.card
      (existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D t) := by
    calc
      E.ncard = Nat.card E := by simp
      _ ≤ Nat.card T := Nat.card_le_card_of_injective f hf
      _ = (Finset.univ.filter fun i : cd.D.Side t =>
          cd.D.IsFingerprintSide (cd.D.occ t i)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      _ = Multiset.card
          (existsMacroCertificate_seed2_routing_step9_g6_ordinary cd.D t) := by
        simp [existsMacroCertificate_seed2_routing_step9_g6_ordinary]
  have hreal : (g.M.K0 : ℝ) + 2 ≤ (E.ncard : ℝ) :=
    g.private_edges.trans ((g.annular_quantitative p).2.1 j')
  have hnat : g.M.K0 + 2 ≤ E.ncard := by exact_mod_cast hreal
  exact hnat.trans hcard

/-- Step 10 of `lem:certificate-exists`, (G6): the special sides are those of `CertData`; "The
private-neighbour estimate and `lem:fingerprint` give (G6)": every small type has at least
`K₀ + 2` private outer edges (`g.annular_quantitative`, `g.private_edges`), so the possible
fingerprint multisets of distinct noncentral types are disjoint (`fingerprintSeparation`). -/
private lemma existsMacroCertificate_seed2_routing_step9_g6 (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) :
    existsMacroCertificate_G6Data cd.D := by
  have g1 := existsMacroCertificate_seed2_routing_step4_g1 τ g s l routing cd
  have g5 := existsMacroCertificate_seed2_routing_step8_g5 τ g s l routing cd
  refine {
    special_small := cd.special_small
    special_unique := cd.special_unique
    special_inner := fun o ho => (cd.special_contact o ho).1
    fingerprint := ?_ }
  apply existsMacroCertificate_seed2_routing_step9_g6_of_quantitative cd
  · intro t ht
    apply existsMacroCertificate_seed2_routing_step9_g6_small_many cd g1 g5 t
    change existsMacroCertificate_seed2_routing_step9_g6_kind cd.D t = .small at ht
    exact (existsMacroCertificate_seed2_routing_step9_g6_kind_small cd.D t).1 ht
  · intro t u ht hu htu howner
    have ht' : cd.D.kind (cd.D.form t) = .small := by
      change existsMacroCertificate_seed2_routing_step9_g6_kind cd.D t = .small at ht
      exact (existsMacroCertificate_seed2_routing_step9_g6_kind_small cd.D t).1 ht
    have hu' : cd.D.kind (cd.D.form u) = .small := by
      change existsMacroCertificate_seed2_routing_step9_g6_kind cd.D u = .small at hu
      exact (existsMacroCertificate_seed2_routing_step9_g6_kind_small cd.D u).1 hu
    simpa only [existsMacroCertificate_seed2_routing_step9_g6_data,
      existsMacroCertificate_seed2_routing_step9_g6_kind_original] using
        existsMacroCertificate_seed2_routing_step9_g6_private_three
          cd g1 g5 t u ht' hu' htu howner

/-- Step 11 of `lem:certificate-exists`, (G7): "The marking rule `every side not belonging to the
large central group, plus the prints` gives (G7)": outer and boundary sides belong to non-large
children (the centre is strictly interior), prints are marked, and every occurrence on a genuine
path lies in a non-large child (no central side before the print). -/
private lemma existsMacroCertificate_seed2_routing_step10_g7 (τ : Substitution P)
    (g : existsMacroCertificate_GroupingSeed τ) (s : existsMacroCertificate_SetupSeed τ g) (l : ℕ)
    (routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding))
    (cd : existsMacroCertificate_CertData τ g s l routing) :
    existsMacroCertificate_G7Data cd.D := by
  have g2 := existsMacroCertificate_seed2_routing_step5_g2 τ g s l routing cd
  have g4 := existsMacroCertificate_seed2_routing_step7_g4 τ g s l routing cd
  have g5 := existsMacroCertificate_seed2_routing_step8_g5 τ g s l routing cd
  have nonlarge_of_outer_or_boundary : ∀ o : cd.D.SideOcc, (cd.D.IsOuter o ∨ cd.D.IsBoundary o) →
      cd.D.kind (cd.D.form o.1) ≠ .large := by
    intro o ho hl
    have hc : o.1 = cd.D.central (cd.D.owner o.1) := (g5.large_iff o.1).mp hl
    let j : cd.D.Side (cd.D.central (cd.D.owner o.1)) :=
      Fin.cast (congrArg (fun t => (cd.D.Q.disk (cd.D.form t)).n) hc) o.2
    have hocc : o = cd.D.occ (cd.D.central (cd.D.owner o.1)) j := by
      refine Sigma.ext hc ?_
      apply (Fin.heq_ext_iff (congrArg (fun t => (cd.D.Q.disk (cd.D.form t)).n) hc)).mpr
      simp [j]
    rcases ho with hOuter | hBoundary
    · have hNotOuter := (g2.central (cd.D.owner o.1) j).1
      rw [← hocc] at hNotOuter
      exact hNotOuter hOuter
    · have hNotBoundary := (g2.central (cd.D.owner o.1) j).2
      rw [← hocc] at hNotBoundary
      exact hNotBoundary hBoundary
  constructor
  intro o ho
  rcases ho with hOuter | hBoundary | hPrint | hGenuine
  · exact cd.marked_rule_nonlarge o (Or.inl (nonlarge_of_outer_or_boundary o (Or.inl hOuter)))
  · exact cd.marked_rule_nonlarge o (Or.inl (nonlarge_of_outer_or_boundary o (Or.inr hBoundary)))
  · exact cd.marked_rule_nonlarge o (Or.inr hPrint)
  · rcases hGenuine with ⟨d, i, hi, hoi⟩
    exact g4.path_marked (cd.D.owner o.1) d i hi o hoi

/-- Step 3--9 of `lem:certificate-exists`: choose `l` using `existsRoutingAfterPower`, retain
the fixed central image and its annular neighbours, scatter every other group, and package the
positioned types, global outer lists, print/special slots and routed occurrence paths. -/
private lemma existsMacroCertificate_seed2_routing (τ : Substitution P) (h : τ.STS)
    (g : existsMacroCertificate_GroupingSeed τ) :
    Nonempty (existsMacroCertificate_RoutingSeed τ g) := by
  obtain ⟨s⟩ := existsMacroCertificate_seed2_routing_step1_setup τ h g
  obtain ⟨l, hl, hidem, hr⟩ := existsMacroCertificate_seed2_routing_step2_power τ h g.M s.setup
  let routing : ∀ α, RoutingData (s.setup.retained l α) (s.setup.GS.G.P'.disk α)
      (τ.θ ^ (s.setup.GS.k * l)) (s.setup.central l α) (s.setup.markedSides α)
      ((s.setup.markedSides (s.setup.c^[l] α)).map Fin.valEmbedding) :=
    fun α => Classical.choice (hr α)
  obtain ⟨cd⟩ := existsMacroCertificate_seed2_routing_step3_data τ h g s l hl hidem routing
  have g1 := existsMacroCertificate_seed2_routing_step4_g1 τ g s l routing cd
  have g2 := existsMacroCertificate_seed2_routing_step5_g2 τ g s l routing cd
  have g3 := existsMacroCertificate_seed2_routing_step6_g3 τ g s l routing cd
  have g4 := existsMacroCertificate_seed2_routing_step7_g4 τ g s l routing cd
  have g5 := existsMacroCertificate_seed2_routing_step8_g5 τ g s l routing cd
  have g6 := existsMacroCertificate_seed2_routing_step9_g6 τ g s l routing cd
  have g7 := existsMacroCertificate_seed2_routing_step10_g7 τ g s l routing cd
  let C : MacroCertificate P :=
    { cd.D with
      scatter_support := cd.rep.scatter_support
      rule_eq := cd.tmpl.rule_eq
      type_injective := cd.tmpl.type_injective
      template_sts := cd.tmpl.template_sts
      g1_connected := g1.connected
      g1_three_le := g1.three_le
      g1_inner_side := g1.inner_side
      g1_partner := g1.partner
      g1_partner_partner := g1.partner_partner
      g1_side_unique := g1.side_unique
      g1_edge_partner := g1.edge_partner
      g1_edge_unique := g1.edge_unique
      g1_edgeTypes := g1.edgeTypes
      g2_belt_connected := g2.belt_connected
      g2_belt_edge := g2.belt_edge
      g2_central := g2.central
      g3_pos_iff := g3.pos_iff
      g3_pos_smul := g3.pos_smul
      g3_outerList_mem := g3.outerList_mem
      g3_outerList_nodup := g3.outerList_nodup
      g3_outerList_sorted := g3.outerList_sorted
      g3_crossing_le_two := g3.crossing_le_two
      g3_five_le := g3.five_le
      g3_length_le := g3.length_le
      g4_print_injective := g4.print_injective
      g4_print_cyclic := g4.print_cyclic
      g4_print_inner := g4.print_inner
      g4_print_small := g4.print_small
      g4_print_special := g4.print_special
      g4_path_head := g4.path_head
      g4_path_last := g4.path_last
      g4_path_chain := g4.path_chain
      g4_path_owner := g4.path_owner
      g4_path_inner := g4.path_inner
      g4_path_partner := g4.path_partner
      g4_path_marked := g4.path_marked
      g4_path_not_central := g4.path_not_central
      g4_path_penultimate := g4.path_penultimate
      g4_path_trivial := g4.path_trivial
      g4_path_nodup := g4.path_nodup
      g4_path_disjoint := g4.path_disjoint
      g5_central_owner := g5.central_owner
      g5_large_iff := g5.large_iff
      g5_central_fixes_large := g5.central_fixes_large
      g5_print_id_large := g5.print_id_large
      g5_card_marked_large := g5.card_marked_large
      g5_card_marked_small := g5.card_marked_small
      g5_three_Q_lt := g5.three_Q_lt
      g5_original_marked := g5.original_marked
      g6_special_small := g6.special_small
      g6_special_unique := g6.special_unique
      g6_special_inner := g6.special_inner
      g6_fingerprint := g6.fingerprint
      g7_marking := g7.marking }
  refine ⟨{
    setup := s.setup
    setup_grouped := s.setup_grouped
    l := l
    l_pos := hl
    central_idempotent := hidem
    routing := routing
    C := C
    m := g.k * l
    m_eq := rfl
    represents := {
      m_pos := cd.rep.m_pos
      θ_eq := cd.rep.θ_eq
      compat := cd.rep.compat
      sts := cd.rep.sts
      dualConnected := cd.rep.dualConnected
      side_whole := cd.rep.side_whole
      vertex_retained := cd.rep.vertex_retained
      singleton := cd.rep.singleton
      inside_supertile := cd.rep.inside_supertile
      hereditary := cd.rep.hereditary }
    baseForm := cd.baseForm
    catalogueTile := cd.catalogueTile
    disk_carrier := cd.disk_carrier
    disk_vertexSet := cd.disk_vertexSet
    disk_ccw := cd.disk_ccw
    scatter_eq := cd.scatter_eq
    originalForm := cd.originalForm
    original_tile := cd.original_tile
    original_scatter := cd.original_scatter
    catalogue_injective := cd.catalogue_injective
    grouped_disks_distinct := cd.grouped_disks_distinct
    kind_original := cd.kind_original
    kind_large := cd.kind_large
    kind_small := cd.kind_small
    templateChild := cd.templateChild
    child_bijective := cd.child_bijective
    child_carrier := cd.child_carrier
    central_child := cd.central_child
    central_form := cd.central_form
    parentSide := cd.parentSide
    parentSide_injective := cd.parentSide_injective
    parent_side_geometry := cd.parent_side_geometry
    marked_from_setup := cd.marked_from_setup
    marked_rule_nonlarge := cd.marked_rule_nonlarge
    marked_rule_large := cd.marked_rule_large
    positive_eq := cd.positive_eq
    outerList_global := fun α d => ⟨cd.outerList_nodup α d, cd.outerList_sorted α d⟩
    print_from_routing := cd.print_from_routing
    special_contact := cd.special_contact
    path_from_routing := cd.path_from_routing
    fifth_path := cd.fifth_path
    N_eq := cd.N_eq
    Qmax_eq := cd.Qmax_eq
    rankBound_is_max := cd.rankBound_is_max }⟩

private noncomputable def existsMacroCertificate_groupingSeed (τ : Substitution P) (h : τ.STS) :
    existsMacroCertificate_GroupingSeed τ :=
  Classical.choice (existsMacroCertificate_seed1_grouping τ h)

private noncomputable def existsMacroCertificate_routingSeed (τ : Substitution P) (h : τ.STS) :
    existsMacroCertificate_RoutingSeed τ (existsMacroCertificate_groupingSeed τ h) :=
  Classical.choice (existsMacroCertificate_seed2_routing τ h
    (existsMacroCertificate_groupingSeed τ h))

/-- The raw finite construction of `lem:certificate-exists`.  It chooses the two construction
seeds above; the property lemmas `existsMacroCertificate_step1_groupedFamily` ...
`existsMacroCertificate_step9_g7` are about this same value.  Its intended value, in the
noncircular order of the blueprint:
1. fix mesh constants `M` of `P` (`MeshConstants.nonempty`); choose `R` with
   `R ≥ Csep · D` (`quantitativeAnnularGrouping`) and `R ≥ 10000 (K₀ + 3) D`, then
   `Q = K₀ ⌈4C²R²/a⌉`, then `N ≥ 2` with `4N > 3Q`, then `k` so large that every `τ^k α` contains
   the squares `Q₀, Q₁` of `quantitativeAnnularGrouping` with their margin;
2. group each fixed patch `τ^k α` (`α ∈ P`) into the inside-anchored group `L`, the outside-anchored
   group `H` cut into the `4N` annular groups of `quantitativeAnnularGrouping`, and singleton groups
   for all other tiles; the finitely many labelled groups (every original form included as a
   singleton group) are the forms of `Q`, `Δ` scatters a group into its tiles, and `σ` scatters,
   applies `τ^k` and regroups, so that `Δ σ = τ^k Δ`;
3. with the central form map `c` and the resulting `RoutingSetup` (centres, annular groupings,
   windows in the middle outer intervals, print slots), take `l > 0` from `existsRoutingAfterPower`
   with `c^[2l] = c^[l]`; in every `σ^l`-template retain the central large group (form in the image
   of `c^l`) and its `4N` annular small neighbours and scatter every other group; this is `σ'`,
   and the first component is `m = k l`;
4. the types are the positioned children of the retained templates, `central α` is the retained
   centre, `kind` is large / small / original as in the grouping, every side of a non-large child
   and every print is marked, while in a large form's own template the marked sides of its large
   central child are exactly its prints; `print` and `special` come from the print slots (the print
   in its small owner is its special side), `outerList` lists the whole outer fine
   sides in the global supporting-line direction, `path` converts the `RoutingData` paths into side
   occurrences (both owners of every crossed inner side, the print in its small owner only), and
   `Qmax = Q`, with `N` as chosen and `rankBound` the largest outer-list length. -/
private noncomputable def existsMacroCertificate_raw (τ : Substitution P) (h : τ.STS) :
    ℕ × MacroData P := by
  let s := existsMacroCertificate_routingSeed τ h
  exact (s.m, s.C.toMacroData)

/-- Step 1 of the blueprint proof of `existsMacroCertificate`: construct the grouped family,
scattering map and powered grouped substitution, including singleton original forms and the
supertile-origin/hereditary clauses required by `Represents`. -/
private lemma existsMacroCertificate_step1_groupedFamily (τ : Substitution P) (h : τ.STS) :
    Nonempty (existsMacroCertificate_RepresentationData τ
      (existsMacroCertificate_raw τ h).1 (existsMacroCertificate_raw τ h).2) := by
  let s := existsMacroCertificate_routingSeed τ h
  change Nonempty (existsMacroCertificate_RepresentationData τ s.m s.C.toMacroData)
  exact ⟨{
    m_pos := s.represents.m_pos
    θ_eq := s.represents.θ_eq
    compat := s.represents.compat
    scatter_support := s.C.scatter_support
    sts := s.represents.sts
    dualConnected := s.represents.dualConnected
    side_whole := s.represents.side_whole
    vertex_retained := s.represents.vertex_retained
    singleton := s.represents.singleton
    inside_supertile := s.represents.inside_supertile
    hereditary := s.represents.hereditary }⟩

/-- Step 2 of the blueprint proof of `existsMacroCertificate`: the retained/scattered rules
are finite STS polygonal templates and their positioned type tags enumerate the children. -/
private lemma existsMacroCertificate_step2_templates (τ : Substitution P) (h : τ.STS) :
    Nonempty (existsMacroCertificate_TemplateData (existsMacroCertificate_raw τ h).2) := by
  let s := existsMacroCertificate_routingSeed τ h
  change Nonempty (existsMacroCertificate_TemplateData s.C.toMacroData)
  exact ⟨{
    rule_eq := s.C.rule_eq
    type_injective := s.C.type_injective
    template_sts := s.C.template_sts }⟩

/-- Step 3 of the blueprint proof of `existsMacroCertificate`: "Disk cellulations with at
least the centre and its ring have connected inner-side duals and at least three children",
with the two-owner and interface-identity consequences. -/
private lemma existsMacroCertificate_step3_g1 (τ : Substitution P) (h : τ.STS) :
    Nonempty (existsMacroCertificate_G1Data (existsMacroCertificate_raw τ h).2) := by
  let s := existsMacroCertificate_routingSeed τ h
  change Nonempty (existsMacroCertificate_G1Data s.C.toMacroData)
  exact ⟨{
    connected := s.C.g1_connected
    three_le := s.C.g1_three_le
    inner_side := s.C.g1_inner_side
    partner := s.C.g1_partner
    partner_partner := s.C.g1_partner_partner
    side_unique := s.C.g1_side_unique
    edge_partner := s.C.g1_edge_partner
    edge_unique := s.C.g1_edge_unique
    edgeTypes := s.C.g1_edgeTypes }⟩

/-- Step 4 of the blueprint proof of `existsMacroCertificate`: boundary faces are connected
through the complete finite fan at every macroboundary vertex, while the centre is interior. -/
private lemma existsMacroCertificate_step4_g2 (τ : Substitution P) (h : τ.STS) :
    Nonempty (existsMacroCertificate_G2Data (existsMacroCertificate_raw τ h).2) := by
  let s := existsMacroCertificate_routingSeed τ h
  change Nonempty (existsMacroCertificate_G2Data s.C.toMacroData)
  exact ⟨{
    belt_connected := s.C.g2_belt_connected
    belt_edge := s.C.g2_belt_edge
    central := s.C.g2_central }⟩

/-- Step 5 of the blueprint proof of `existsMacroCertificate`: finite boundary interval
intersections, global supporting-line orientation, five ports, and the finite rank bound give
(G3), with no nested-cut assumption. -/
private lemma existsMacroCertificate_step5_g3 (τ : Substitution P) (h : τ.STS) :
    Nonempty (existsMacroCertificate_G3Data (existsMacroCertificate_raw τ h).2) := by
  let s := existsMacroCertificate_routingSeed τ h
  change Nonempty (existsMacroCertificate_G3Data s.C.toMacroData)
  exact ⟨{
    pos_iff := s.C.g3_pos_iff
    pos_smul := s.C.g3_pos_smul
    outerList_mem := s.C.g3_outerList_mem
    outerList_nodup := s.C.g3_outerList_nodup
    outerList_sorted := s.C.g3_outerList_sorted
    crossing_le_two := s.C.g3_crossing_le_two
    five_le := s.C.g3_five_le
    length_le := s.C.g3_length_le }⟩

/-- Step 6 of the blueprint proof of `existsMacroCertificate`: `lem:routing` supplies (G4),
including inner paths, partner occurrences, the small-owner terminal print and disjointness. -/
private lemma existsMacroCertificate_step6_g4 (τ : Substitution P) (h : τ.STS) :
    Nonempty (existsMacroCertificate_G4Data (existsMacroCertificate_raw τ h).2) := by
  let s := existsMacroCertificate_routingSeed τ h
  change Nonempty (existsMacroCertificate_G4Data s.C.toMacroData)
  exact ⟨{
    print_injective := s.C.g4_print_injective
    print_cyclic := s.C.g4_print_cyclic
    print_inner := s.C.g4_print_inner
    print_small := s.C.g4_print_small
    print_special := s.C.g4_print_special
    path_head := s.C.g4_path_head
    path_last := s.C.g4_path_last
    path_chain := s.C.g4_path_chain
    path_owner := s.C.g4_path_owner
    path_inner := s.C.g4_path_inner
    path_partner := s.C.g4_path_partner
    path_marked := s.C.g4_path_marked
    path_not_central := s.C.g4_path_not_central
    path_penultimate := s.C.g4_path_penultimate
    path_trivial := s.C.g4_path_trivial
    path_nodup := s.C.g4_path_nodup
    path_disjoint := s.C.g4_path_disjoint }⟩

/-- Step 7 of the blueprint proof of `existsMacroCertificate`: fixed central forms, identity
prints for large parents, the retained ring, and `4N > 3Q` give (G5). -/
private lemma existsMacroCertificate_step7_g5 (τ : Substitution P) (h : τ.STS) :
    Nonempty (existsMacroCertificate_G5Data (existsMacroCertificate_raw τ h).2) := by
  let s := existsMacroCertificate_routingSeed τ h
  change Nonempty (existsMacroCertificate_G5Data s.C.toMacroData)
  exact ⟨{
    central_owner := s.C.g5_central_owner
    large_iff := s.C.g5_large_iff
    central_fixes_large := s.C.g5_central_fixes_large
    print_id_large := s.C.g5_print_id_large
    card_marked_large := s.C.g5_card_marked_large
    card_marked_small := s.C.g5_card_marked_small
    three_Q_lt := s.C.g5_three_Q_lt
    original_marked := s.C.g5_original_marked }⟩

/-- Step 8 of the blueprint proof of `existsMacroCertificate`: the quantitative private-neighbour
estimate and `fingerprintSeparation` give the unique-special-side and fingerprint clauses (G6). -/
private lemma existsMacroCertificate_step8_g6 (τ : Substitution P) (h : τ.STS) :
    Nonempty (existsMacroCertificate_G6Data (existsMacroCertificate_raw τ h).2) := by
  let s := existsMacroCertificate_routingSeed τ h
  change Nonempty (existsMacroCertificate_G6Data s.C.toMacroData)
  exact ⟨{
    special_small := s.C.g6_special_small
    special_unique := s.C.g6_special_unique
    special_inner := s.C.g6_special_inner
    fingerprint := s.C.g6_fingerprint }⟩

/-- Step 9 of the blueprint proof of `existsMacroCertificate`: the construction's marking rule
marks every outer side, boundary side, print and genuine-path occurrence, proving (G7). -/
private lemma existsMacroCertificate_step9_g7 (τ : Substitution P) (h : τ.STS) :
    Nonempty (existsMacroCertificate_G7Data (existsMacroCertificate_raw τ h).2) := by
  let s := existsMacroCertificate_routingSeed τ h
  change Nonempty (existsMacroCertificate_G7Data s.C.toMacroData)
  exact ⟨{ marking := s.C.g7_marking }⟩

/-- `lem:certificate-exists`: for every STS polygonal substitution `τ` there
are a macrocertificate `C` with the properties (G1)–(G7) and a power `m > 0`
such that `C` represents `τ` at the power `m`: a finite grouped family
`P'` (the forms `C.Q`) containing every original form as a singleton group,
a scattering map `Δ = C.Δ`, and a grouped substitution `σ' = C.σ` of
expansion `θ^m` with `Δ σ' α = τ^m Δ α` for all `α`. -/
theorem existsMacroCertificate (τ : Substitution P) (h : τ.STS) :
    ∃ (C : MacroCertificate P) (m : ℕ), C.Represents τ m := by
  let m := (existsMacroCertificate_raw τ h).1
  let D := (existsMacroCertificate_raw τ h).2
  obtain ⟨rep⟩ := existsMacroCertificate_step1_groupedFamily τ h
  obtain ⟨tmpl⟩ := existsMacroCertificate_step2_templates τ h
  obtain ⟨g1⟩ := existsMacroCertificate_step3_g1 τ h
  obtain ⟨g2⟩ := existsMacroCertificate_step4_g2 τ h
  obtain ⟨g3⟩ := existsMacroCertificate_step5_g3 τ h
  obtain ⟨g4⟩ := existsMacroCertificate_step6_g4 τ h
  obtain ⟨g5⟩ := existsMacroCertificate_step7_g5 τ h
  obtain ⟨g6⟩ := existsMacroCertificate_step8_g6 τ h
  obtain ⟨g7⟩ := existsMacroCertificate_step9_g7 τ h
  let C : MacroCertificate P :=
    { D with
      scatter_support := rep.scatter_support
      rule_eq := tmpl.rule_eq
      type_injective := tmpl.type_injective
      template_sts := tmpl.template_sts
      g1_connected := g1.connected
      g1_three_le := g1.three_le
      g1_inner_side := g1.inner_side
      g1_partner := g1.partner
      g1_partner_partner := g1.partner_partner
      g1_side_unique := g1.side_unique
      g1_edge_partner := g1.edge_partner
      g1_edge_unique := g1.edge_unique
      g1_edgeTypes := g1.edgeTypes
      g2_belt_connected := g2.belt_connected
      g2_belt_edge := g2.belt_edge
      g2_central := g2.central
      g3_pos_iff := g3.pos_iff
      g3_pos_smul := g3.pos_smul
      g3_outerList_mem := g3.outerList_mem
      g3_outerList_nodup := g3.outerList_nodup
      g3_outerList_sorted := g3.outerList_sorted
      g3_crossing_le_two := g3.crossing_le_two
      g3_five_le := g3.five_le
      g3_length_le := g3.length_le
      g4_print_injective := g4.print_injective
      g4_print_cyclic := g4.print_cyclic
      g4_print_inner := g4.print_inner
      g4_print_small := g4.print_small
      g4_print_special := g4.print_special
      g4_path_head := g4.path_head
      g4_path_last := g4.path_last
      g4_path_chain := g4.path_chain
      g4_path_owner := g4.path_owner
      g4_path_inner := g4.path_inner
      g4_path_partner := g4.path_partner
      g4_path_marked := g4.path_marked
      g4_path_not_central := g4.path_not_central
      g4_path_penultimate := g4.path_penultimate
      g4_path_trivial := g4.path_trivial
      g4_path_nodup := g4.path_nodup
      g4_path_disjoint := g4.path_disjoint
      g5_central_owner := g5.central_owner
      g5_large_iff := g5.large_iff
      g5_central_fixes_large := g5.central_fixes_large
      g5_print_id_large := g5.print_id_large
      g5_card_marked_large := g5.card_marked_large
      g5_card_marked_small := g5.card_marked_small
      g5_three_Q_lt := g5.three_Q_lt
      g5_original_marked := g5.original_marked
      g6_special_small := g6.special_small
      g6_special_unique := g6.special_unique
      g6_special_inner := g6.special_inner
      g6_fingerprint := g6.fingerprint
      g7_marking := g7.marking }
  refine ⟨C, m, ?_⟩
  exact
    { m_pos := rep.m_pos
      θ_eq := rep.θ_eq
      compat := rep.compat
      sts := rep.sts
      dualConnected := rep.dualConnected
      side_whole := rep.side_whole
      vertex_retained := rep.vertex_retained
      singleton := rep.singleton
      inside_supertile := rep.inside_supertile
      hereditary := rep.hereditary }

end Geometry

end Tilings

end
