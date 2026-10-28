import Enforce.Source.Trace

/-!
# Incident forests, power factorisation, and finite headers

Compatible patches retain their actual frames, rather than choosing frames of physical
carriers. Cones in header tuples are direction cones at the origin. Translating an
apex to the origin before supplying the tuple gives exactly the notation of V4 1.17.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- P9, V4 1.14: a finite patch with specified compatible ground frames. -/
structure CompatiblePatch (S : SubstSystem d) where
  /-- P9, V4 1.14: the framed ground tiles. -/
  tiles : Finset (FramedNode S)
  /-- P9, V4 1.14: disjoint interiors of distinct patch members. -/
  disjoint : (tiles : Set (FramedNode S)).PairwiseDisjoint (fun t => interior (t.carrier 0))
  /-- P9, V4 1.14: every specified frame belongs to the compatible group. -/
  compatible : ∀ t ∈ tiles, t.frame.linearIsometryEquiv ∈ S.rotGroup

/-- P9, V4 1.14: conjugated frame under ambient expansion of a compatible tile. -/
def compatibleInflatedFrame (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (n : ℕ) : Iso d :=
  rigidMotion (Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
    t.frame.linearIsometryEquiv ht)) ((S.σ ^ n) (t.frame 0))

namespace CompatiblePatch

variable (P : CompatiblePatch S)

/-- P9, V4 1.14: addresses in the depth-`n` subdivision of the inflated patch. -/
abbrev Address (n : ℕ) := Σ t : {t // t ∈ P.tiles}, S.RoleWord t.val.ty n

/-- P9, V4 1.14: the native tile at an address of `σⁿ Π`. -/
def native (n : ℕ) (a : P.Address n) : FramedNode S :=
  (S.nativeTile a.1.val.ty n a.2).move
    (compatibleInflatedFrame a.1.val (P.compatible a.1.val a.1.property) n)

/-- P9, V4 1.14: every native frame is still compatible. -/
theorem native_compatible (n : ℕ) (a : P.Address n) :
    (P.native n a).frame.linearIsometryEquiv ∈ S.rotGroup := by
  sorry

/-- P9, V4 1.14: incident native tiles, with their unambiguous addresses. -/
abbrev Incident (p : E d) (n : ℕ) :=
  {a : P.Address n // (S.σ ^ n) p ∈ (P.native n a).carrier 0}

/-- P9, V4 1.14: the geometric child relation between consecutive inflated levels.
Containment in `σ t` determines the actual substitution parent. -/
def IncidentChild (p : E d) (n : ℕ) (a : P.Incident p n)
    (b : P.Incident p (n + 1)) : Prop :=
  (P.native (n + 1) b.val).carrier 0 ⊆ S.σ '' (P.native n a.val).carrier 0

/-- P9, V4 1.14: every incident native tile has a unique incident parent.
The original address prevents identifying distinct occurrences by a chosen frame. -/
theorem incident_parent_exists_unique (p : E d) (n : ℕ)
    (b : P.Incident p (n + 1)) :
    ∃! a : P.Incident p n, P.IncidentChild p n a b := by
  sorry

/-- P9, V4 1.14: the incident-forest parent chosen from unique existence. -/
def incidentParent (p : E d) (n : ℕ) (b : P.Incident p (n + 1)) : P.Incident p n :=
  Classical.choose (P.incident_parent_exists_unique p n b)

/-- P9, V4 1.14: specification of the incident parent. -/
theorem incidentParent_spec (p : E d) (n : ℕ) (b : P.Incident p (n + 1)) :
    P.IncidentChild p n (P.incidentParent p n b) b :=
  (Classical.choose_spec (P.incident_parent_exists_unique p n b)).1

/-- P9, V4 1.14: a tail after level `N`, retaining all actual incident tiles. -/
structure IncidentTail (p : E d) (N : ℕ) where
  /-- P9, V4 1.14: the successive incident addresses. -/
  node : ∀ r : ℕ, P.Incident p (N + r)
  /-- P9, V4 1.14: successive nodes are geometric substitution children. -/
  step : ∀ r, (P.native (N + (r + 1)) (node (r + 1)).val).carrier 0 ⊆
    S.σ '' (P.native (N + r) (node r).val).carrier 0

/-- P9, V4 1.14: bounded width, no dying branches, and eventual unique children.
DEVIATION: the exact minimum-angle constant uses the nonempty catalogue, as in D3. -/
theorem incidentForest [Nonempty S.ι] (p : E d) :
    (∀ n, Finite (P.Incident p n) ∧
      Nat.card (P.Incident p n) ≤ multiplicityBound S.proto S.cx) ∧
    (∀ n (a : P.Incident p n),
      ∃ b : P.Incident p (n + 1), P.IncidentChild p n a b) ∧
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ a : P.Incident p n,
      ∃! b : P.Incident p (n + 1), P.IncidentChild p n a b := by
  sorry

/-- P9, V4 1.14: beyond a splitting cutoff, tails are in bijection with the
incident tiles there, so there are at most `M₀` infinite tails.
DEVIATION: the exact `M₀` requires the nonempty angle catalogue, as in D3. -/
theorem incident_tails [Nonempty S.ι] (p : E d) :
    ∃ N : ℕ, Function.Bijective (fun t : P.IncidentTail p N => t.node 0) ∧
      Finite (P.IncidentTail p N) ∧
      Nat.card (P.IncidentTail p N) ≤ multiplicityBound S.proto S.cx := by
  sorry

/-- P9/P5, V4 1.14, 1.5(b): common-listed points in the original patch. -/
def CommonListed (p : E d) : Prop :=
  ∀ t ∈ P.tiles, p ∈ t.carrier 0 → t.Lists 0 p

/-- P9, V4 1.14: listedness persists across every incident child step. -/
theorem incident_listed_step (p : E d) (n : ℕ) (a : P.Incident p n)
    (b : P.Incident p (n + 1)) (hab : P.IncidentChild p n a b)
    (ha : (P.native n a.val).Lists 0 ((S.σ ^ n) p)) :
    (P.native (n + 1) b.val).Lists 0 ((S.σ ^ (n + 1)) p) := by
  sorry

/-- P9/P5, V4 1.14, 1.5(b): a common-listed point is listed at every depth. -/
theorem incident_commonListed (p : E d) (hp : P.CommonListed p)
    (n : ℕ) (a : P.Incident p n) : (P.native n a.val).Lists 0 ((S.σ ^ n) p) := by
  sorry

end CompatiblePatch

/-- P10, V4 1.15: every complex root of the characteristic polynomial is positive
real. This formulation allows Jordan blocks and imposes no self-adjointness. -/
def PositiveRealSpectrum (L : E d ≃ₗ[ℝ] E d) : Prop :=
  ∀ z : ℂ, (L.toLinearMap.charpoly.map (algebraMap ℝ ℂ)).IsRoot z →
    z.im = 0 ∧ 0 < z.re

/-- P10, V4 1.15: the full data of a power factorisation. -/
structure PowerFactorisation (S : SubstSystem d) where
  /-- P10, V4 1.15: positive integral exponent. -/
  power : ℕ
  /-- P10, V4 1.15: nonzero power. -/
  power_pos : 1 ≤ power
  /-- P10, V4 1.15: compatible orthogonal factor. -/
  R : Ortho d
  /-- P10, V4 1.15: membership in the closed compatible group. -/
  R_mem : R ∈ S.rotGroup
  /-- P10, V4 1.15: invertible positive-spectrum factor. -/
  L : E d ≃ₗ[ℝ] E d
  /-- P10, V4 1.15: equality of the actual linear maps. -/
  factor : S.σ ^ power = R.toLinearEquiv * L
  /-- P10, V4 1.15: normalization, as equality of sets of linear equivalences. -/
  normalizes : (fun h : Ortho d => L * h.toLinearEquiv * L⁻¹) ''
      (S.rotGroup : Set (Ortho d)) =
    (fun h : Ortho d => h.toLinearEquiv) '' (S.rotGroup : Set (Ortho d))
  /-- P10, V4 1.15: positive real spectrum without a diagonalizability assumption. -/
  positive : PositiveRealSpectrum L

namespace CompatiblePatch

variable (P : CompatiblePatch S)

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". Finitely many proper affine
subspaces have dense complement. -/
private theorem power_factorisation_aux_step10_dense_avoid
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : Type*} [Finite ι] (L : ι → AffineSubspace ℝ V) (hL : ∀ i, L i ≠ ⊤) :
    Dense (⋂ i, ((L i : Set V)ᶜ)) := by
  apply dense_iInter_of_isOpen (fun i => (L i).closed_of_finiteDimensional.isOpen_compl)
  intro i
  rw [← interior_eq_empty_iff_dense_compl]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have ht := isOpen_interior.affineSpan_eq_top (⟨x, hx⟩ : (interior (L i : Set V)).Nonempty)
  have hle : affineSpan ℝ (interior (L i : Set V)) ≤ L i :=
    affineSpan_le.mpr interior_subset
  rw [ht] at hle
  exact hL i (top_unique hle)

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". A segment from a point
outside an affine subspace avoids that subspace if its other endpoint
avoids the affine span of the subspace and the first point. -/
private theorem power_factorisation_aux_step10_segment_avoid
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : AffineSubspace ℝ V) (x z : V) (hx : x ∉ L)
    (hz : z ∉ affineSpan ℝ (insert x (L : Set V))) :
    Disjoint (segment ℝ x z) (L : Set V) := by
  apply Set.disjoint_left.mpr
  intro w hw hwL
  have hwline : w ∈ line[ℝ, x, z] :=
    (line[ℝ, x, z]).convex.segment_subset (left_mem_affineSpan_pair ℝ x z)
      (right_mem_affineSpan_pair ℝ x z) hw
  have hwx : w ≠ x := by rintro rfl; exact hx hwL
  have hline := affineSpan_pair_eq_of_right_mem_of_ne hwline hwx
  have hle : line[ℝ, x, w] ≤ affineSpan ℝ (insert x (L : Set V)) :=
    affineSpan_pair_le_of_mem_of_mem (mem_affineSpan ℝ (Set.mem_insert _ _))
      (mem_affineSpan ℝ (Set.mem_insert_of_mem _ hwL))
  rw [hline] at hle
  exact hz (hle (right_mem_affineSpan_pair ℝ x z))

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". Removing finitely many
affine subspaces of codimension at least two does not disconnect an
open convex set: two segments through a generic intermediate point suffice. -/
private theorem power_factorisation_aux_step10_avoid_connected
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : Type*} [Finite ι] (L : ι → AffineSubspace ℝ V)
    (hL : ∀ i, Module.finrank ℝ (L i).direction + 1 < Module.finrank ℝ V)
    (U : Set V) (hU : IsOpen U) (hc : Convex ℝ U) :
    IsPreconnected (U ∩ ⋂ i, (L i : Set V)ᶜ) := by
  apply isPreconnected_of_forall_pair
  rintro x ⟨hxU, hx⟩ y ⟨hyU, hy⟩
  let M : Bool × ι → AffineSubspace ℝ V := fun b =>
    affineSpan ℝ (insert (if b.1 then x else y) (L b.2 : Set V))
  have hM (b : Bool × ι) : M b ≠ ⊤ := by
    intro heq
    have hle := finrank_vectorSpan_insert_le (L b.2) (if b.1 then x else y)
    rw [← direction_affineSpan] at hle
    change Module.finrank ℝ (M b).direction ≤ Module.finrank ℝ (L b.2).direction + 1 at hle
    rw [heq, AffineSubspace.direction_top, finrank_top] at hle
    exact (hL b.2).not_ge hle
  obtain ⟨z, hz, hzU⟩ := (power_factorisation_aux_step10_dense_avoid M hM).exists_mem_open hU ⟨x, hxU⟩
  have hsx : segment ℝ x z ⊆ U ∩ ⋂ i, (L i : Set V)ᶜ := by
    intro w hw
    refine ⟨hc.segment_subset hxU hzU hw, Set.mem_iInter.mpr fun i => ?_⟩
    exact Set.disjoint_left.mp (power_factorisation_aux_step10_segment_avoid (L i) x z
      (Set.mem_iInter.mp hx i) (by simpa [M] using Set.mem_iInter.mp hz (true, i))) hw
  have hsy : segment ℝ y z ⊆ U ∩ ⋂ i, (L i : Set V)ᶜ := by
    intro w hw
    refine ⟨hc.segment_subset hyU hzU hw, Set.mem_iInter.mpr fun i => ?_⟩
    exact Set.disjoint_left.mp (power_factorisation_aux_step10_segment_avoid (L i) y z
      (Set.mem_iInter.mp hy i) (by simpa [M] using Set.mem_iInter.mp hz (false, i))) hw
  refine ⟨segment ℝ x z ∪ segment ℝ y z, Set.union_subset hsx hsy,
    Or.inl (left_mem_segment ℝ x z), Or.inr (left_mem_segment ℝ y z), ?_⟩
  exact (convex_segment (𝕜 := ℝ) x z).isPreconnected.union z
    (right_mem_segment ℝ x z) (right_mem_segment ℝ y z)
    (convex_segment (𝕜 := ℝ) y z).isPreconnected


/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". A boundary of a regular
closed set cannot locally lie in finitely many affine subspaces of
codimension at least two: the complement connects the inside to the outside. -/
private theorem power_factorisation_aux_step10_boundary_not_thin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : Set V) (hK : IsClosed K) (hreg : closure (interior K) = K)
    (p : V) (hp : p ∈ frontier K)
    {ι : Type*} [Finite ι] (L : ι → AffineSubspace ℝ V)
    (hL : ∀ i, Module.finrank ℝ (L i).direction + 1 < Module.finrank ℝ V)
    (r : ℝ) (hr : 0 < r) :
    ¬ frontier K ∩ ball p r ⊆ ⋃ i, (L i : Set V) := by
  intro hcover
  have hproper (i : ι) : L i ≠ ⊤ := by
    intro heq
    have h := hL i
    rw [heq, AffineSubspace.direction_top, finrank_top] at h
    omega
  have hdense := power_factorisation_aux_step10_dense_avoid L hproper
  have hxcl : p ∈ closure (interior K) := by
    rw [hreg]
    exact hK.frontier_subset hp
  have hycl : p ∈ closure Kᶜ := by
    rw [frontier_eq_closure_inter_closure] at hp
    exact hp.2
  obtain ⟨x, hx, hxU, hxK⟩ := hdense.exists_mem_open (isOpen_ball.inter isOpen_interior)
    (mem_closure_iff.mp hxcl (ball p r) isOpen_ball (mem_ball_self hr))
  obtain ⟨y, hy, hyU, hyK⟩ := hdense.exists_mem_open (isOpen_ball.inter hK.isOpen_compl)
    (mem_closure_iff.mp hycl (ball p r) isOpen_ball (mem_ball_self hr))
  have hsides : ball p r ∩ ⋂ i, (L i : Set V)ᶜ ⊆ interior K ∪ Kᶜ := by
    rintro z ⟨hzU, hz⟩
    by_cases hzK : z ∈ K
    · left
      by_contra hzi
      have hzf : z ∈ frontier K := by rw [hK.frontier_eq]; exact ⟨hzK, hzi⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ⟨hzf, hzU⟩)
      exact Set.mem_iInter.mp hz i hi
    · exact Or.inr hzK
  have hd : Disjoint (interior K) Kᶜ :=
    Set.disjoint_left.mpr fun z hz hzc => hzc (interior_subset hz)
  rcases (power_factorisation_aux_step10_avoid_connected L hL (ball p r)
      isOpen_ball (convex_ball p r)).subset_or_subset isOpen_interior hK.isOpen_compl hd hsides with h | h
  · exact hyK (interior_subset (h ⟨hyU, hy⟩))
  · exact h ⟨hxU, hx⟩ (interior_subset hxK)

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". In a finite closed covering
of a regular boundary by lower-dimensional pieces, the pieces of
codimension one already cover the whole boundary. -/
private theorem power_factorisation_aux_step10_boundary_facets
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : Set V) (hK : IsClosed K) (hreg : closure (interior K) = K)
    {ι : Type*} [Finite ι] (C : ι → Set V) (hC : ∀ i, IsClosed (C i))
    (hcover : frontier K ⊆ ⋃ i, C i)
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (C i)).direction < Module.finrank ℝ V)
    (p : V) (hp : p ∈ frontier K) :
    ∃ i, p ∈ C i ∧ Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 = Module.finrank ℝ V := by
  classical
  by_contra hn
  let J := {i : ι // Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 = Module.finrank ℝ V}
  let H : Set V := ⋃ i : J, C i.val
  have hH : IsClosed H := isClosed_iUnion_of_finite fun i : J => hC i.val
  have hpH : p ∈ Hᶜ := by
    intro hpH
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpH
    exact hn ⟨i.val, hi, i.property⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hH.isOpen_compl p hpH
  let I := {i : ι // Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 ≠ Module.finrank ℝ V}
  have hlow (i : I) : Module.finrank ℝ (affineSpan ℝ (C i.val)).direction + 1 < Module.finrank ℝ V := by
    have := hdim i.val
    have := i.property
    omega
  apply power_factorisation_aux_step10_boundary_not_thin K hK hreg p hp
    (fun i : I => affineSpan ℝ (C i.val)) hlow r hr
  rintro x ⟨hxK, hxball⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hxK)
  have hiI : Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 ≠ Module.finrank ℝ V := by
    intro heq
    exact hball hxball (Set.mem_iUnion.mpr ⟨⟨i, heq⟩, hi⟩)
  exact Set.mem_iUnion.mpr ⟨⟨i, hiI⟩, mem_affineSpan ℝ hi⟩


/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"facets of that cell". A set with nonempty intrinsic interior but empty
ambient interior has strictly smaller affine dimension than the ambient space. -/
private theorem power_factorisation_aux_step10_rank_lt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (C : Set V) (hi : (intrinsicInterior ℝ C).Nonempty) (he : interior C = ∅) :
    Module.finrank ℝ (affineSpan ℝ C).direction < Module.finrank ℝ V := by
  by_contra hn
  have hdir : (affineSpan ℝ C).direction = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by omega))
  have hne : (affineSpan ℝ C : Set V).Nonempty :=
    (hi.mono intrinsicInterior_subset).mono (subset_affineSpan ℝ C)
  have hs : affineSpan ℝ C = ⊤ := (AffineSubspace.direction_eq_top_iff_of_nonempty hne).mp hdir
  rw [intrinsicInterior, hs] at hi
  have hopen : IsOpenMap ((↑) : (⊤ : AffineSubspace ℝ V) → V) :=
    (show IsOpen ((⊤ : AffineSubspace ℝ V) : Set V) from isOpen_univ).isOpenMap_subtype_val
  have hsub := (hopen.image_interior_subset (((↑) : (⊤ : AffineSubspace ℝ V) → V) ⁻¹' C)).trans
    (interior_mono (Set.image_preimage_subset _ _))
  have hh := hi.mono hsub
  simpa [he] using hh

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"∂A is covered by its facets". Apply the boundary covering lemma to the
finite listed prototype cells. -/
private theorem power_factorisation_aux_step10_prototype_facets
    (A : PolyManifoldDomain d) (K : CellComplex A) (p : E d)
    (hp : p ∈ frontier A.carrier) :
    ∃ e ∈ K.cells, e.dim = d - 1 ∧ p ∈ e.carrier := by
  obtain ⟨e, he, hdim⟩ := power_factorisation_aux_step10_boundary_facets A.carrier
    A.compact.isClosed A.regularClosed (fun e : {e // e ∈ K.cells} => e.val.carrier)
    (fun e => e.val.flat.compact.isClosed) (by
      intro x hx
      rw [← K.carriers_cover] at hx
      obtain ⟨e, he, hx⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hx
      exact Set.mem_iUnion.mpr ⟨⟨e, he⟩, hx⟩)
    (fun e => by
      change Module.finrank ℝ (cellDirection e.val.carrier) < Module.finrank ℝ (E d)
      rw [e.val.flat.dimension]
      simpa using K.dim_lt e.val e.property) p hp
  refine ⟨e.val, e.property, ?_, he⟩
  change Module.finrank ℝ (cellDirection e.val.carrier) + 1 = Module.finrank ℝ (E d) at hdim
  rw [e.val.flat.dimension] at hdim
  have hh : e.val.dim + 1 = d := by simpa using hdim
  omega

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"the relative boundary of each cell is covered by the facets of that
cell". Work in its direction space, using an affine isometry from that
space onto its affine hull. -/
private theorem power_factorisation_aux_step10_cell_facets
    (A : PolyManifoldDomain d) (K : CellComplex A)
    (e : Cell d) (he : e ∈ K.cells) (p : E d) (hp : p ∈ relfrontier e.carrier) :
    ∃ f ∈ K.cells, f.dim + 1 = e.dim ∧ p ∈ f.carrier ∧ f.carrier ⊆ e.carrier := by
  classical
  let H := affineSpan ℝ e.carrier
  have hpe : p ∈ e.carrier := intrinsicFrontier_subset e.flat.compact.isClosed hp
  let q : H := ⟨p, mem_affineSpan ℝ hpe⟩
  letI : Nonempty H := ⟨q⟩
  let ψ : H.direction ≃ᵃⁱ[ℝ] H := AffineIsometryEquiv.vaddConst ℝ q
  let φ : H.direction →ᵃⁱ[ℝ] E d := H.subtypeₐᵢ.comp ψ.toAffineIsometry
  let C : Set H.direction := φ ⁻¹' e.carrier
  have himage (D : Set (E d)) (hD : D ⊆ H) : φ '' (φ ⁻¹' D) = D := by
    apply Set.image_preimage_eq_of_subset
    intro x hx
    exact ⟨ψ.symm ⟨x, hD hx⟩, by
      change (ψ (ψ.symm ⟨x, hD hx⟩) : E d) = x
      rw [ψ.apply_symm_apply]⟩
  have heH : e.carrier ⊆ H := subset_affineSpan ℝ e.carrier
  have hCimage : φ '' C = e.carrier := himage _ heH
  have hinter : φ '' interior C = relint e.carrier := by
    change (((↑) : H → E d) ∘ ψ.toHomeomorph) '' interior (ψ.toHomeomorph ⁻¹' (((↑) : H → E d) ⁻¹' e.carrier)) = _
    rw [Set.image_comp, ψ.toHomeomorph.image_interior, ψ.toHomeomorph.image_preimage]
    rfl
  have hfront : φ '' frontier C = relfrontier e.carrier := by
    change (((↑) : H → E d) ∘ ψ.toHomeomorph) '' frontier (ψ.toHomeomorph ⁻¹' (((↑) : H → E d) ⁻¹' e.carrier)) = _
    rw [Set.image_comp, ψ.toHomeomorph.image_frontier, ψ.toHomeomorph.image_preimage]
    rfl
  have hCclosed : IsClosed C := e.flat.compact.isClosed.preimage φ.continuous
  have hCreg : closure (interior C) = C := by
    apply φ.injective.image_injective
    rw [← φ.isometry.isClosedEmbedding.closure_image_eq, hinter, e.flat.regularClosed, hCimage]
  obtain ⟨b, hb, hboundary⟩ := K.boundary_union e he
  have hbsub (f : {f // f ∈ b}) : f.val.carrier ⊆ relfrontier e.carrier := by
    intro x hx
    rw [hboundary]
    exact Set.mem_iUnion.mpr ⟨f.val, Set.mem_iUnion.mpr ⟨f.property, hx⟩⟩
  have hbH (f : {f // f ∈ b}) : f.val.carrier ⊆ H :=
    (hbsub f).trans ((intrinsicFrontier_subset e.flat.compact.isClosed).trans heH)
  let D (f : {f // f ∈ b}) : Set H.direction := φ ⁻¹' f.val.carrier
  have hDfront (f : {f // f ∈ b}) : D f ⊆ frontier C := by
    intro x hx
    have hh := hbsub f hx
    rw [← hfront] at hh
    exact φ.injective.mem_set_image.mp hh
  have hDdim (f : {f // f ∈ b}) :
      Module.finrank ℝ (affineSpan ℝ (D f)).direction = f.val.dim := by
    have heq : (affineSpan ℝ f.val.carrier).direction =
        ((affineSpan ℝ (D f)).direction).map H.direction.subtype := by
      rw [← himage f.val.carrier (hbH f)]
      change (affineSpan ℝ (φ.toAffineMap '' D f)).direction = _
      rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
      rfl
    have hh := f.val.flat.dimension
    change Module.finrank ℝ (affineSpan ℝ f.val.carrier).direction = f.val.dim at hh
    rw [heq, Submodule.finrank_map_subtype_eq] at hh
    exact hh
  have hDlow (f : {f // f ∈ b}) :
      Module.finrank ℝ (affineSpan ℝ (D f)).direction < Module.finrank ℝ H.direction := by
    apply power_factorisation_aux_step10_rank_lt
    · have hh := f.val.flat.relint_nonempty
      change (intrinsicInterior ℝ f.val.carrier).Nonempty at hh
      rw [← himage f.val.carrier (hbH f), φ.image_intrinsicInterior, Set.image_nonempty] at hh
      exact hh
    · apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hh := interior_mono (hDfront f) hx
      simpa [interior_frontier hCclosed] using hh
  have hpC : ψ.symm q ∈ frontier C := by
    apply φ.injective.mem_set_image.mp
    rw [hfront]
    simpa [φ] using hp
  obtain ⟨f, hpf, hfdim⟩ := power_factorisation_aux_step10_boundary_facets C hCclosed hCreg D
    (fun f => f.val.flat.compact.isClosed.preimage φ.continuous) (by
      intro x hx
      have hh : φ x ∈ relfrontier e.carrier := hfront ▸ Set.mem_image_of_mem φ hx
      rw [hboundary] at hh
      obtain ⟨f, hf, hxf⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hh
      exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hxf⟩) hDlow (ψ.symm q) hpC
  refine ⟨f.val, hb f.property, ?_, ?_,
    (hbsub f).trans (intrinsicFrontier_subset e.flat.compact.isClosed)⟩
  · rw [hDdim] at hfdim
    exact hfdim.trans e.flat.dimension
  · change φ (ψ.symm q) ∈ f.val.carrier at hpf
    simpa [φ] using hpf


/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"each still containing the vertex". A listed vertex in a positive-dimensional
listed cell lies in that cell's relative boundary, since listed relative
interiors are disjoint. -/
private theorem power_factorisation_aux_step10_vertex_boundary
    (A : PolyManifoldDomain d) (K : CellComplex A)
    (v : Cell d) (hv : v ∈ K.vertices) (p : E d) (hp : p ∈ v.carrier)
    (e : Cell d) (he : e ∈ K.cells) (hpe : p ∈ e.carrier) (hdim : 0 < e.dim) :
    p ∈ relfrontier e.carrier := by
  have hvdim : v.dim = 0 := (Finset.mem_filter.mp hv).2
  have hvK : v ∈ K.cells := (Finset.mem_filter.mp hv).1
  have hbot : cellDirection v.carrier = ⊥ :=
    Submodule.finrank_eq_zero.mp (v.flat.dimension.trans hvdim)
  have hsingle : v.carrier.Subsingleton := by
    apply (vectorSpan_eq_bot_iff_subsingleton ℝ).mp
    simpa only [cellDirection, direction_affineSpan] using hbot
  have hvp : v.carrier = {p} := hsingle.eq_singleton_of_mem hp
  have hpv : p ∈ relint v.carrier := by simp [relint, hvp]
  have hne : v ≠ e := by
    intro h
    have := h ▸ hvdim
    omega
  have hnot : p ∉ relint e.carrier := fun hh =>
    Set.disjoint_left.mp (K.relint_disjoint v hvK e he hne) hpv hh
  change p ∈ intrinsicFrontier ℝ e.carrier
  rw [← closure_diff_intrinsicInterior, e.flat.compact.isClosed.closure_eq]
  exact ⟨hpe, hnot⟩

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, used in 1.17):
"starting from a facet through the vertex one descends through incident
facets of facets". Reversing this descending sequence gives the complete
nested flag at the original listed vertex. -/
private theorem power_factorisation_aux_step10_prototype_flag
    (A : PolyManifoldDomain d) (K : CellComplex A)
    (v : Cell d) (hv : v ∈ K.vertices) (p : E d) (hp : p ∈ v.carrier) :
    ∃ f : CellFlag K, ∀ j, p ∈ (f.cell j).carrier := by
  classical
  have hpA : p ∈ frontier A.carrier := by
    rw [← K.carriers_cover]
    exact Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨(Finset.mem_filter.mp hv).1, hp⟩⟩
  obtain ⟨e, he, hdim, hpe⟩ := power_factorisation_aux_step10_prototype_facets A K p hpA
  let I := {e : Cell d // e ∈ K.cells ∧ p ∈ e.carrier}
  have hnext (e : I) (h : 0 < e.val.dim) :
      ∃ f : I, f.val.dim + 1 = e.val.dim ∧ f.val.carrier ⊆ e.val.carrier := by
    obtain ⟨f, hf, hfdim, hpf, hsub⟩ := power_factorisation_aux_step10_cell_facets A K e.val e.property.1 p
      (power_factorisation_aux_step10_vertex_boundary A K v hv p hp e.val e.property.1 e.property.2 h)
    exact ⟨⟨f, hf, hpf⟩, hfdim, hsub⟩
  let next (e : I) : I := if h : 0 < e.val.dim then (hnext e h).choose else e
  have next_dim (e : I) : (next e).val.dim = e.val.dim - 1 := by
    by_cases h : 0 < e.val.dim
    · have hh := (hnext e h).choose_spec.1
      simp only [next, dif_pos h]
      omega
    · have hh : e.val.dim = 0 := by omega
      simp [next, h, hh]
  have next_sub (e : I) : (next e).val.carrier ⊆ e.val.carrier := by
    by_cases h : 0 < e.val.dim
    · simpa only [next, dif_pos h] using (hnext e h).choose_spec.2
    · simp [next, h]
  let c (n : ℕ) : I := next^[n] ⟨e, he, hpe⟩
  have c_succ (n : ℕ) : c (n + 1) = next (c n) := Function.iterate_succ_apply' next n _
  have c_dim (n : ℕ) : (c n).val.dim = d - 1 - n := by
    induction n with
    | zero => simpa [c] using hdim
    | succ n ih => rw [c_succ, next_dim, ih]; omega
  have c_anti : Antitone (fun n => (c n).val.carrier) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [c_succ]
    exact next_sub (c n)
  let f : CellFlag K :=
    { cell := fun j => (c (d - 1 - j.val)).val
      mem := fun j => (c (d - 1 - j.val)).property.1
      dimension := fun j => by rw [c_dim]; omega
      nested := fun i j hij => c_anti (by have := i.isLt; have := j.isLt; omega) }
  exact ⟨f, fun j => (c (d - 1 - j.val)).property.2⟩

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, used in 1.17):
"the boundary complex of a polyhedral manifold has a full flag at every
vertex". This is only the initial flag, before any substitution is applied. -/
private theorem power_factorisation_aux_step10_vertex_flag
    (t : FramedNode S) (p : E d) (hp : t.Lists 0 p) :
    ∃ f : CellFlag (S.cx t.ty), ∀ j, p ∈ t.cell 0 (f.cell j) := by
  obtain ⟨v, hv, x, hx, hxp⟩ := hp
  obtain ⟨f, hf⟩ := power_factorisation_aux_step10_prototype_flag (S.proto t.ty) (S.cx t.ty) v hv x hx
  exact ⟨f, fun j => ⟨x, hf j, hxp⟩⟩


/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". Conjugated frames intertwine successive expansions. -/
private theorem power_factorisation_aux_step11_conjugate_succ
    (R : E d ≃ₗ[ℝ] E d) (n : ℕ) (x : E d) :
    linearConj S.σ ((n + 1 : ℕ) : ℤ) R (S.σ x) =
      S.σ (linearConj S.σ (n : ℤ) R x) := by
  have heq : linearConj S.σ ((n + 1 : ℕ) : ℤ) R * S.σ =
      S.σ * linearConj S.σ (n : ℤ) R := by
    simp only [linearConj, Nat.cast_add, Nat.cast_one]
    group
  exact congrArg (fun L : E d ≃ₗ[ℝ] E d => L x) heq

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". The prescribed role frame has the same covariance. -/
private theorem power_factorisation_aux_step11_placeChild_succ
    {A : S.ι} (i : S.I A) (n : ℕ) (x : E d) :
    S.placeChild (n + 1) i (S.σ x) = S.σ (S.placeChild n i x) := by
  rw [S.placeChild_apply, S.placeChild_apply,
    power_factorisation_aux_step11_conjugate_succ, map_add, pow_succ']
  rfl

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". At height zero the role frame is the prescribed child frame. -/
private theorem power_factorisation_aux_step11_placeChild_zero
    {A : S.ι} (i : S.I A) : S.placeChild 0 i = (S.child A i).frame := by
  apply AffineIsometryEquiv.ext
  intro x
  change linearConj S.σ (0 : ℤ) (S.child A i).rotation.toLinearEquiv x +
      (S.σ ^ 0) (S.child A i).offset =
    (S.child A i).rotation x + (S.child A i).offset
  simp [linearConj]

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". Append a child role to a native address,
leaving its original patch root fixed. -/
private def power_factorisation_aux_step11_append (S : SubstSystem d) :
    (A : S.ι) → (n : ℕ) → (w : S.RoleWord A n) →
      S.I (S.nativeTile A n w).ty → S.RoleWord A (n + 1)
  | A, 0, _, i => ⟨i, ()⟩
  | A, n + 1, w, i => ⟨w.1,
      power_factorisation_aux_step11_append S (S.child A w.1).ty n w.2 i⟩

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the child t_{n+1}". Appending a role retains its prescribed child type. -/
private theorem power_factorisation_aux_step11_append_type
    (A : S.ι) (n : ℕ) (w : S.RoleWord A n) (i : S.I (S.nativeTile A n w).ty) :
    (S.nativeTile A (n + 1) (power_factorisation_aux_step11_append S A n w i)).ty =
      (S.child (S.nativeTile A n w).ty i).ty := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih => exact ih (S.child A w.1).ty w.2 i

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". Appending a role realizes subdivision after
inflation, even though the native-address recursion reads roles from the root. -/
private theorem power_factorisation_aux_step11_append_frame
    (A : S.ι) (n : ℕ) (w : S.RoleWord A n) (i : S.I (S.nativeTile A n w).ty)
    (x : E d) :
    (S.nativeTile A (n + 1) (power_factorisation_aux_step11_append S A n w i)).frame x =
      S.σ ((S.nativeTile A n w).frame (S.σ.symm ((S.child (S.nativeTile A n w).ty i).frame x))) := by
  induction n generalizing A with
  | zero =>
    change S.placeChild 0 i x = S.σ (S.σ.symm ((S.child A i).frame x))
    rw [S.σ.apply_symm_apply, power_factorisation_aux_step11_placeChild_zero]
    rfl
  | succ n ih =>
    change S.placeChild (0 + (n + 1)) w.1
      ((S.nativeTile (S.child A w.1).ty (n + 1)
        (power_factorisation_aux_step11_append S (S.child A w.1).ty n w.2 i)).frame x) =
      S.σ (S.placeChild (0 + n) w.1 ((S.nativeTile (S.child A w.1).ty n w.2).frame
        (S.σ.symm ((S.child (S.nativeTile (S.child A w.1).ty n w.2).ty i).frame x))))
    simp only [Nat.zero_add]
    rw [ih, power_factorisation_aux_step11_placeChild_succ]

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". The patch's specified ground frame obeys the
same covariance as a substitution role frame. -/
private theorem power_factorisation_aux_step11_inflated_frame_succ
    (t : FramedNode S) (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup)
    (n : ℕ) (x : E d) :
    compatibleInflatedFrame t ht (n + 1) (S.σ x) =
      S.σ (compatibleInflatedFrame t ht n x) := by
  have hQ (n : ℕ) (x : E d) :
      (Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
        t.frame.linearIsometryEquiv ht)) x =
      linearConj S.σ (n : ℤ) t.frame.linearIsometryEquiv.toLinearEquiv x :=
    congrArg (fun L : E d ≃ₗ[ℝ] E d => L x)
      (Classical.choose_spec (S.rotGroup_conj_zpow (n : ℤ)
        t.frame.linearIsometryEquiv ht)).2
  change (Classical.choose (S.rotGroup_conj_zpow ((n + 1 : ℕ) : ℤ)
      t.frame.linearIsometryEquiv ht)) (S.σ x) + (S.σ ^ (n + 1)) (t.frame 0) =
    S.σ ((Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
      t.frame.linearIsometryEquiv ht)) x + (S.σ ^ n) (t.frame 0))
  rw [hQ, hQ, power_factorisation_aux_step11_conjugate_succ, map_add, pow_succ']
  rfl

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". The appended address uses exactly the actual
frame of the inflated patch tile followed by the prescribed child frame. -/
private theorem power_factorisation_aux_step11_native_child
    (P : CompatiblePatch S) (n : ℕ) (a : P.Address n) (i : S.I (P.native n a).ty) :
    ∃ b : P.Address (n + 1),
      (P.native (n + 1) b).ty = (S.child (P.native n a).ty i).ty ∧
      ∀ x, (P.native (n + 1) b).frame x =
        S.σ ((P.native n a).frame (S.σ.symm ((S.child (P.native n a).ty i).frame x))) := by
  refine ⟨⟨a.1, power_factorisation_aux_step11_append S a.1.val.ty n a.2 i⟩,
    power_factorisation_aux_step11_append_type a.1.val.ty n a.2 i, ?_⟩
  intro x
  change compatibleInflatedFrame a.1.val (P.compatible _ a.1.property) (n + 1)
    ((S.nativeTile a.1.val.ty (n + 1)
      (power_factorisation_aux_step11_append S a.1.val.ty n a.2 i)).frame x) = _
  rw [power_factorisation_aux_step11_append_frame, power_factorisation_aux_step11_inflated_frame_succ]
  rfl


/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"cells of t_n". A ground cell is placed directly by its tile frame. -/
private theorem power_factorisation_aux_step11_cell_zero (t : FramedNode S) (e : Cell d) :
    t.cell 0 e = t.frame '' e.carrier := rfl

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"cells of t_n". The ground carrier is the isometric prototype carrier. -/
private theorem power_factorisation_aux_step11_carrier_zero (t : FramedNode S) :
    t.carrier 0 = t.frame '' (S.proto t.ty).carrier := by
  simp [FramedNode.carrier, placedSet, SubstSystem.supertile]

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"cells of t_n". A listed cell is contained in its closed tile carrier. -/
private theorem power_factorisation_aux_step11_cell_subset (t : FramedNode S)
    (e : Cell d) (he : e ∈ (S.cx t.ty).cells) : t.cell 0 e ⊆ t.carrier 0 := by
  rw [power_factorisation_aux_step11_cell_zero, power_factorisation_aux_step11_carrier_zero]
  apply Set.image_mono
  intro x hx
  apply (S.proto t.ty).compact.isClosed.frontier_subset
  rw [← (S.cx t.ty).carriers_cover]
  exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he, hx⟩⟩

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"σ e is a union of placed j-cells of the children". An expanded incident
cell has an incident native child cell of the same dimension; its carrier
is contained in the expanded parent cell. No uniqueness is used in this step. -/
private theorem power_factorisation_aux_step11_refinement
    (P : CompatiblePatch S) (p : E d) (n : ℕ) (a : P.Incident p n)
    (e : CellName S (P.native n a.val).ty)
    (he : (S.σ ^ n) p ∈ (P.native n a.val).cell 0 e.val) :
    ∃ (b : P.Incident p (n + 1)) (f : CellName S (P.native (n + 1) b.val).ty),
      P.IncidentChild p n a b ∧ f.val.dim = e.val.dim ∧
      (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b.val).cell 0 f.val ∧
      (P.native (n + 1) b.val).cell 0 f.val ⊆
        S.σ '' (P.native n a.val).cell 0 e.val := by
  classical
  rw [power_factorisation_aux_step11_cell_zero] at he
  obtain ⟨x, hxe, hxp⟩ := he
  obtain ⟨c, hc⟩ := S.heredity (P.native n a.val).ty e.val e.property
  have hsx : S.σ x ∈ ⋃ q ∈ c, placedSet (S.child (P.native n a.val).ty q.1).frame q.2.val.carrier := by
    rw [← hc]
    exact Set.mem_image_of_mem S.σ hxe
  obtain ⟨q, hq, y, hy, hyx⟩ := by
    simpa only [Set.mem_iUnion, exists_prop, placedSet, Set.mem_image] using hsx
  obtain ⟨b, hty, hframe⟩ := power_factorisation_aux_step11_native_child P n a.val q.1
  have hmem : q.2.val ∈ (S.cx (P.native (n + 1) b).ty).cells := by
    rw [hty]
    exact q.2.property.1
  have hpoint : (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b).cell 0 q.2.val := by
    rw [power_factorisation_aux_step11_cell_zero]
    refine ⟨y, hy, ?_⟩
    rw [hframe, hyx, S.σ.symm_apply_apply, hxp, pow_succ']
    rfl
  have hinc : (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b).carrier 0 :=
    power_factorisation_aux_step11_cell_subset _ _ hmem hpoint
  have hsub : ∀ (K L : Set (E d)),
      (S.child (P.native n a.val).ty q.1).frame '' K ⊆ S.σ '' L →
      (P.native (n + 1) b).frame '' K ⊆ S.σ '' ((P.native n a.val).frame '' L) := by
    intro K L h z hz
    obtain ⟨u, hu, rfl⟩ := hz
    obtain ⟨v, hv, hvu⟩ := h (Set.mem_image_of_mem _ hu)
    refine ⟨(P.native n a.val).frame v, Set.mem_image_of_mem _ hv, ?_⟩
    rw [hframe, ← hvu, S.σ.symm_apply_apply]
  refine ⟨⟨b, hinc⟩, ⟨q.2.val, hmem⟩, ?_, q.2.property.2, hpoint, ?_⟩
  · change (P.native (n + 1) b).carrier 0 ⊆ S.σ '' (P.native n a.val).carrier 0
    rw [power_factorisation_aux_step11_carrier_zero, power_factorisation_aux_step11_carrier_zero, hty]
    apply hsub
    rw [S.children_cover]
    exact Set.subset_iUnion (fun i => placedSet (S.child (P.native n a.val).ty i).frame
      (S.proto (S.child (P.native n a.val).ty i).ty).carrier) q.1
  · rw [power_factorisation_aux_step11_cell_zero, power_factorisation_aux_step11_cell_zero]
    apply hsub
    rw [hc]
    intro z hz
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, hz⟩⟩

/-- Step 12 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.17):
"regarded as the tuple of its direction spaces". Taking directions of a
placed cell removes translation and retains the actual orthogonal frame. -/
private theorem power_factorisation_aux_step12_frame_direction
    (t : FramedNode S) (e : Cell d) :
    cellDirection (t.cell 0 e) =
      (cellDirection e.carrier).map t.frame.linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  change (affineSpan ℝ (t.frame.toAffineEquiv.toAffineMap '' e.carrier)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  rfl

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"its affine hull is σ aff e by dimension". Direction spaces commute
with every invertible linear map, including the anisotropic expansion. -/
private theorem power_factorisation_aux_step11_linear_direction
    (L : E d ≃ₗ[ℝ] E d) (K : Set (E d)) :
    cellDirection (L '' K) = (cellDirection K).map L.toLinearMap := by
  change (affineSpan ℝ (L.toAffineEquiv.toAffineMap '' K)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  rfl

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim, used in 1.17):
"some j-cell ... contains [the vertex] and lies in σ e". Heredity at a
unique incident child preserves the direction of one listed cell.
The uniqueness hypothesis excludes branching, and the cell must contain the anchor. -/
private theorem power_factorisation_aux_step11_child_cell
    (P : CompatiblePatch S) (p : E d) (n : ℕ)
    (a : P.Incident p n) (b : P.Incident p (n + 1))
    (hab : P.IncidentChild p n a b)
    (hunique : ∀ b' : P.Incident p (n + 1), P.IncidentChild p n a b' → b' = b)
    (e : CellName S (P.native n a.val).ty)
    (he : (S.σ ^ n) p ∈ (P.native n a.val).cell 0 e.val) :
    ∃ f : CellName S (P.native (n + 1) b.val).ty,
      f.val.dim = e.val.dim ∧
      (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b.val).cell 0 f.val ∧
      cellDirection ((P.native (n + 1) b.val).cell 0 f.val) =
        (cellDirection ((P.native n a.val).cell 0 e.val)).map S.σ.toLinearMap := by
  obtain ⟨b', f, hb', hdim, hf, hsub⟩ := power_factorisation_aux_step11_refinement P p n a e he
  obtain rfl := hunique b' hb'
  refine ⟨f, hdim, hf, ?_⟩
  have hle := AffineSubspace.direction_le (affineSpan_mono ℝ hsub)
  change cellDirection ((P.native (n + 1) b'.val).cell 0 f.val) ≤
    cellDirection (S.σ '' (P.native n a.val).cell 0 e.val) at hle
  rw [power_factorisation_aux_step11_linear_direction] at hle
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [power_factorisation_aux_step12_frame_direction, power_factorisation_aux_step12_frame_direction]
  simp only [LinearEquiv.finrank_map_eq]
  exact f.val.flat.dimension.trans (hdim.trans e.val.flat.dimension.symm)


/-- Step 13 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.17):
"the Claim in the proof of 1.15 ... gives a native flag". Iterate the
single-cell transport along a nonbranching listing tail; the transported
cells need not be nested, but their direction spaces are a complete flag. -/
private theorem power_factorisation_aux_step13_tail_flag
    (P : CompatiblePatch S) (p : E d) (N : ℕ) (t : P.IncidentTail p N)
    (hunique : ∀ m (b : P.Incident p (N + m + 1)),
      P.IncidentChild p (N + m) (t.node m) b → b = t.node (m + 1))
    (hlisted : (P.native N (t.node 0).val).Lists 0 ((S.σ ^ N) p)) :
    ∃ V : ℕ → Submodule ℝ (E d),
      (∀ i ≤ d, Module.finrank ℝ (V i) = i) ∧
      (∀ i < d, V i ≤ V (i + 1)) ∧
      (∀ i ≤ d, V i ∈ S.hPi ∨ V i = ⊤) ∧
      ∀ m i, i ≤ d →
        ((V i).map (S.σ ^ m).toLinearMap).map
          (P.native (N + m) (t.node m).val).frame.linearIsometryEquiv.symm.toLinearEquiv.toLinearMap
          ∈ S.cellDirections ∪ {⊤} := by
  classical
  obtain ⟨f, hf⟩ := power_factorisation_aux_step10_vertex_flag _ _ hlisted
  let V (i : ℕ) : Submodule ℝ (E d) :=
    if hi : i < d then cellDirection ((P.native N (t.node 0).val).cell 0 (f.cell ⟨i, hi⟩))
    else ⊤
  have hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i := by
    intro i hi
    by_cases hid : i < d
    · rw [show V i = cellDirection ((P.native N (t.node 0).val).cell 0 (f.cell ⟨i, hid⟩))
          from dif_pos hid, power_factorisation_aux_step12_frame_direction, LinearEquiv.finrank_map_eq]
      exact (f.cell ⟨i, hid⟩).flat.dimension.trans (f.dimension ⟨i, hid⟩)
    · have heq : i = d := by omega
      rw [show V i = ⊤ from dif_neg hid]
      simp [heq]
  have hmono : ∀ i < d, V i ≤ V (i + 1) := by
    intro i hi
    by_cases hj : i + 1 < d
    · simp only [V, dif_pos hi, dif_pos hj, power_factorisation_aux_step12_frame_direction]
      apply Submodule.map_mono
      exact AffineSubspace.direction_le (affineSpan_mono ℝ
        (f.nested ⟨i, hi⟩ ⟨i + 1, hj⟩ (by simp)))
    · simp [V, hj]
  have hV : ∀ i ≤ d, V i ∈ S.hPi ∨ V i = ⊤ := by
    intro i hi
    by_cases hid : i < d
    · left
      refine ⟨cellDirection (f.cell ⟨i, hid⟩).carrier,
        ⟨(P.native N (t.node 0).val).ty, f.cell ⟨i, hid⟩, f.mem _, rfl⟩,
        (P.native N (t.node 0).val).frame.linearIsometryEquiv,
        P.native_compatible N (t.node 0).val, ?_⟩
      simp only [V, dif_pos hid, power_factorisation_aux_step12_frame_direction]
    · exact Or.inr (by simp [V, hid])
  have hcell (i : ℕ) (hi : i < d) : ∀ m : ℕ,
      ∃ e : CellName S (P.native (N + m) (t.node m).val).ty,
        (S.σ ^ (N + m)) p ∈ (P.native (N + m) (t.node m).val).cell 0 e.val ∧
        cellDirection ((P.native (N + m) (t.node m).val).cell 0 e.val) =
          (V i).map (S.σ ^ m).toLinearMap := by
    intro m
    induction m with
    | zero =>
      refine ⟨⟨f.cell ⟨i, hi⟩, f.mem _⟩, hf _, ?_⟩
      simp [V, hi]
    | succ m ih =>
      obtain ⟨e, he, hdir⟩ := ih
      obtain ⟨e', _, he', hdir'⟩ := power_factorisation_aux_step11_child_cell P p
        (N + m) (t.node m) (t.node (m + 1)) (t.step m) (hunique m) e he
      refine ⟨e', he', ?_⟩
      calc
        _ = (cellDirection ((P.native (N + m) (t.node m).val).cell 0 e.val)).map
            S.σ.toLinearMap := hdir'
        _ = _ := by
          rw [hdir, ← Submodule.map_comp]
          simp [pow_succ', LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp]
  refine ⟨V, hdim, hmono, hV, ?_⟩
  intro m i hi
  by_cases hid : i < d
  · obtain ⟨e, he, hdir⟩ := hcell i hid m
    rw [← hdir, power_factorisation_aux_step12_frame_direction, ← Submodule.map_comp]
    simp only [LinearIsometryEquiv.toLinearEquiv_symm, LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, Submodule.map_id]
    exact Or.inl ⟨(P.native (N + m) (t.node m).val).ty, e.val, e.property, rfl⟩
  · simp [V, hid, Submodule.map_top]

/-- Step 15 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.17):
"beyond all branching". Starting at the unique-child cutoff, recursively
choose the unique children. Every later incident tile belongs to one of
these tails, indexed by the finite set of incident tiles at the cutoff. -/
private theorem power_factorisation_aux_step15_tail_cover
    (P : CompatiblePatch S) [Nonempty S.ι] (p : E d) :
    ∃ (N : ℕ) (t : P.Incident p N → P.IncidentTail p N),
      (∀ m, Function.Surjective (fun a => (t a).node m)) ∧
      ∀ n, N ≤ n → ∀ a : P.Incident p n,
        ∃! b : P.Incident p (n + 1), P.IncidentChild p n a b := by
  classical
  obtain ⟨_, _, N, hN⟩ := P.incidentForest p
  let next (m : ℕ) (a : P.Incident p (N + m)) : P.Incident p (N + (m + 1)) :=
    Classical.choose (hN (N + m) (by omega) a)
  have hnext (m : ℕ) (a : P.Incident p (N + m)) :
      P.IncidentChild p (N + m) a (next m a) :=
    (Classical.choose_spec (hN (N + m) (by omega) a)).1
  let node (a : P.Incident p N) : ∀ m, P.Incident p (N + m) :=
    fun m => Nat.rec a (fun m b => next m b) m
  let t (a : P.Incident p N) : P.IncidentTail p N :=
    ⟨node a, fun m => hnext m (node a m)⟩
  refine ⟨N, t, ?_, hN⟩
  intro m
  induction m with
  | zero => exact fun a => ⟨a, rfl⟩
  | succ m ih =>
    intro b
    let a := P.incidentParent p (N + m) b
    obtain ⟨a₀, ha₀⟩ := ih a
    refine ⟨a₀, ?_⟩
    change next m (node a₀ m) = b
    change node a₀ m = a at ha₀
    rw [ha₀]
    exact ExistsUnique.unique (hN (N + m) (by omega) a)
      (hnext m a) (P.incidentParent_spec p (N + m) b)

end CompatiblePatch

open scoped Topology in
/-- Copy of a step of the V4 proof of `packet_E_equality` (V4 3.12(b)), used for V4 1.15:
"we may take q a vertex". An extreme point in the relative interior of
one of the intersection's cells forces that cell to be a singleton. -/
private theorem power_factorisation_aux_extreme_cell (K L : Set (E d)) (hLK : L ⊆ K)
    (q : E d) (hq : q ∈ K.extremePoints ℝ) (hqL : q ∈ relint L) : L = {q} := by
  obtain ⟨q', hq', rfl⟩ := mem_intrinsicInterior.mp hqL
  have hqL : (q' : E d) ∈ L := (show q' ∈ Subtype.val ⁻¹' L from interior_subset hq')
  apply Set.Subset.antisymm
  · intro x hx
    let γ : ℝ → affineSpan ℝ L := fun t =>
      ⟨AffineMap.lineMap (q' : E d) x t,
        AffineMap.lineMap_mem t q'.property (subset_affineSpan ℝ L hx)⟩
    have hγ : Continuous γ := by fun_prop
    have hsmall : ∀ᶠ t : ℝ in 𝓝 0,
        (γ t : E d) ∈ L ∧ (γ (-t) : E d) ∈ L := by
      have h₁ : Filter.Tendsto γ (𝓝 0) (𝓝 q') := by
        simpa [γ] using hγ.tendsto 0
      have h₂ : Filter.Tendsto (fun t => γ (-t)) (𝓝 0) (𝓝 q') := by
        simpa [γ] using (hγ.comp continuous_neg).tendsto 0
      exact Filter.Eventually.and (h₁ (mem_interior_iff_mem_nhds.mp hq'))
        (h₂ (mem_interior_iff_mem_nhds.mp hq'))
    obtain ⟨ε, hε, hεL⟩ := Metric.eventually_nhds_iff.mp hsmall
    let t := ε / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have htε : dist t 0 < ε := by simp [t, abs_of_pos hε]; linarith
    obtain ⟨hplus, hminus⟩ := hεL htε
    have hseg : (q' : E d) ∈ openSegment ℝ (γ t : E d) (γ (-t) : E d) := by
      refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
      simp only [γ, AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
      module
    have hplus_eq : (γ t : E d) = (q' : E d) := hq.2 (hLK hplus) (hLK hminus) hseg
    have hzero : t • (x - (q' : E d)) = 0 := by
      simpa [γ, AffineMap.lineMap_apply] using hplus_eq
    have hxeq : x = (q' : E d) := sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left ht.ne')
    exact Set.mem_singleton_iff.mpr hxeq
  · exact singleton_subset_iff.mpr hqL

/-- Step 1 of the V4 proof of `power_factorisation` (V4 1.15): "take any prototile `A`
and vertex `v`". An extreme point of a closed set lies on its frontier. -/
private theorem power_factorisation_aux_extreme_frontier (K : Set (E d)) (hK : IsClosed K)
    (q : E d) (hq : q ∈ K.extremePoints ℝ) : q ∈ frontier K := by
  refine ⟨subset_closure hq.1, fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior q hint
  haveI : Nontrivial (E d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [finrank_euclideanSpace_fin]
    have := (Fact.out : 2 ≤ d)
    omega
  obtain ⟨v, hv⟩ := exists_norm_eq (E d) (le_of_lt (half_pos hε))
  have h1 : q + v ∈ K := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hv]
    linarith))
  have h2 : q - v ∈ K := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, hv]
    linarith))
  have hseg : q ∈ openSegment ℝ (q + v) (q - v) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have heq : q + v = q := hq.2 h1 h2 hseg
  have hv0 : v = 0 := by
    have := congrArg (fun x => x - q) heq
    simpa using this
  rw [hv0, norm_zero] at hv
  linarith

/-- Step 1 of the V4 proof of `power_factorisation` (V4 1.15): "take any prototile `A`
and vertex `v`". Every prototype complex lists a vertex, with a point in it. -/
private theorem power_factorisation_aux_vertex (A : PolyManifoldDomain d) (K : CellComplex A) :
    ∃ v ∈ K.vertices, ∃ q : E d, q ∈ v.carrier := by
  obtain ⟨q, hq⟩ := A.compact.extremePoints_nonempty
    (A.interior_nonempty.mono interior_subset)
  have hqP : q ∈ frontier A.carrier :=
    power_factorisation_aux_extreme_frontier _ A.compact.isClosed q hq
  have hv := K.minimalCell_mem q hqP
  have hvsub : (K.minimalCell q hqP).carrier ⊆ A.carrier := by
    intro x hx
    have hx' : x ∈ frontier A.carrier := by
      rw [← K.carriers_cover]
      exact Set.mem_iUnion₂.mpr ⟨_, hv, hx⟩
    exact A.compact.isClosed.frontier_subset hx'
  have hvsing : (K.minimalCell q hqP).carrier = {q} :=
    power_factorisation_aux_extreme_cell A.carrier _ hvsub q hq (K.mem_relint_minimalCell q hqP)
  refine ⟨K.minimalCell q hqP, Finset.mem_filter.mpr ⟨hv, ?_⟩, q, by rw [hvsing]; rfl⟩
  have hdim := (K.minimalCell q hqP).flat.dimension
  rw [cellDirection, hvsing, direction_affineSpan, vectorSpan_singleton, finrank_bot] at hdim
  exact hdim.symm

/-- Step 1 of the V4 proof of `power_factorisation` (V4 1.15, Claim and 1.10(b)):
"apply Lemma 1.14 to `Π = {A}`, `p = v`; choose a tail ... for every `m ≥ 0`,
`σ^m 𝓕 ∈ B_{t_{N₀+m}} 𝔉`". A complete flag of direction spaces whose expansions are,
up to compatible frames, tuples of prototype cell directions. -/
private theorem power_factorisation_step1_tail_flag (S : SubstSystem d) [Nonempty S.ι] :
    ∃ (V : ℕ → Submodule ℝ (E d)) (B : ℕ → Ortho d),
      (∀ i ≤ d, Module.finrank ℝ (V i) = i) ∧ (∀ i < d, V i ≤ V (i + 1)) ∧
      (∀ m, B m ∈ S.rotGroup) ∧
      ∀ m i, i ≤ d →
        ((V i).map (S.σ ^ m).toLinearMap).map (B m).symm.toLinearEquiv.toLinearMap ∈
          S.cellDirections ∪ {⊤} := by
  classical
  let A : S.ι := Classical.arbitrary _
  let t₀ : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have ht₀ : t₀.frame.linearIsometryEquiv ∈ S.rotGroup := by
    have : t₀.frame.linearIsometryEquiv = 1 := by ext x; rfl
    rw [this]
    exact S.rotGroup.one_mem
  let P : CompatiblePatch S :=
    { tiles := {t₀}
      disjoint := by
        rw [Finset.coe_singleton]
        exact Set.pairwiseDisjoint_singleton _ _
      compatible := by
        intro t ht
        rw [Finset.mem_singleton.mp ht]
        exact ht₀ }
  obtain ⟨v, hv, q, hq⟩ := power_factorisation_aux_vertex (S.proto A) (S.cx A)
  have hqA : q ∈ (S.proto A).carrier := by
    have hv' := (Finset.mem_filter.mp hv).1
    have hx' : q ∈ frontier (S.proto A).carrier := by
      rw [← (S.cx A).carriers_cover]
      exact Set.mem_iUnion₂.mpr ⟨_, hv', hq⟩
    exact (S.proto A).compact.isClosed.frontier_subset hx'
  have hlist0 : t₀.Lists 0 q := ⟨v, hv, q, hq, by simp [FramedNode.prototypeFrame, t₀]⟩
  have hp : P.CommonListed q := by
    intro t ht _
    rw [Finset.mem_singleton.mp ht]
    exact hlist0
  have h0 : Nonempty (P.Incident q 0) := by
    let a : P.Address 0 := ⟨⟨t₀, Finset.mem_singleton_self _⟩, ()⟩
    have hg : ∀ y, compatibleInflatedFrame t₀ (P.compatible t₀ (Finset.mem_singleton_self _)) 0 y
        = y := by
      intro y
      have hc := (Classical.choose_spec (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ)
        t₀.frame.linearIsometryEquiv (P.compatible t₀ (Finset.mem_singleton_self _)))).2
      have hy := congrArg (fun e : E d ≃ₗ[ℝ] E d => e y) hc
      simp only [linearConj, Nat.cast_zero, zpow_zero, neg_zero, one_mul, mul_one] at hy
      show (Classical.choose (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ)
        t₀.frame.linearIsometryEquiv (P.compatible t₀ (Finset.mem_singleton_self _)))) y +
          (S.σ ^ 0) (t₀.frame 0) = y
      rw [show t₀.frame 0 = 0 from rfl, map_zero, add_zero]
      exact hy.trans rfl
    refine ⟨⟨a, ?_⟩⟩
    refine ⟨(S.σ ^ 0) q, ⟨q, hqA, rfl⟩, ?_⟩
    change compatibleInflatedFrame t₀ (P.compatible t₀ (Finset.mem_singleton_self _)) 0
      ((AffineIsometryEquiv.refl ℝ (E d)) ((S.σ ^ 0) q)) = (S.σ ^ 0) q
    rw [hg]
    rfl
  have hne : ∀ n, Nonempty (P.Incident q n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      obtain ⟨a⟩ := ih
      obtain ⟨b, _⟩ := (P.incidentForest q).2.1 n a
      exact ⟨b⟩
  obtain ⟨N, t, _, hN⟩ := CompatiblePatch.power_factorisation_aux_step15_tail_cover P q
  obtain ⟨a⟩ := hne N
  have hunique : ∀ m (b : P.Incident q (N + m + 1)),
      P.IncidentChild q (N + m) ((t a).node m) b → b = (t a).node (m + 1) :=
    fun m b hb => ExistsUnique.unique (hN (N + m) (by omega) ((t a).node m)) hb ((t a).step m)
  have hlisted := P.incident_commonListed q hp N ((t a).node 0)
  obtain ⟨V, hdim, hmono, -, hframe⟩ :=
    CompatiblePatch.power_factorisation_aux_step13_tail_flag P q N (t a) hunique hlisted
  exact ⟨V, fun m => (P.native (N + m) ((t a).node m).val).frame.linearIsometryEquiv, hdim,
    hmono, fun m => P.native_compatible (N + m) ((t a).node m).val, hframe⟩

/-- Step 2 of the V4 proof of `power_factorisation` (V4 1.15): "the finite set of native
flags". There are finitely many prototype cell directions. -/
private theorem power_factorisation_step2_cellDirections_finite (S : SubstSystem d) :
    S.cellDirections.Finite := by
  apply (Set.finite_iUnion fun A : S.ι =>
    ((S.cx A).cells.finite_toSet.image (fun e : Cell d => cellDirection e.carrier))).subset
  rintro V ⟨A, e, he, rfl⟩
  exact Set.mem_iUnion.mpr ⟨A, e, he, rfl⟩

/-- Step 3 of the V4 proof of `power_factorisation` (V4 1.15): "there is `p₀ ≥ 1` with
`𝖧 σ^{p₀} 𝓕 = 𝖧 𝓕`, i.e. `σ^{p₀} 𝓕 = R 𝓕` for some `R ∈ 𝖧`" (after replacing `𝓕` by a
later expansion of it). Pigeonhole on the finitely many native flag tuples. -/
private theorem power_factorisation_step3_recurrence (S : SubstSystem d) [Nonempty S.ι] :
    ∃ (W : ℕ → Submodule ℝ (E d)) (p : ℕ) (R : Ortho d), 1 ≤ p ∧ R ∈ S.rotGroup ∧
      (∀ i ≤ d, Module.finrank ℝ (W i) = i) ∧ (∀ i < d, W i ≤ W (i + 1)) ∧
      ∀ i ≤ d, (W i).map (S.σ ^ p).toLinearMap = (W i).map R.toLinearEquiv.toLinearMap := by
  classical
  obtain ⟨V, B, hdim, hmono, hB, hframe⟩ := power_factorisation_step1_tail_flag S
  let T : Set (Submodule ℝ (E d)) := S.cellDirections ∪ {⊤}
  have hT : T.Finite :=
    (power_factorisation_step2_cellDirections_finite S).union (Set.finite_singleton _)
  haveI : Finite T := hT.to_subtype
  let key : ℕ → (Fin (d + 1) → T) := fun m i =>
    ⟨_, hframe m i (Nat.lt_succ_iff.mp i.isLt)⟩
  have hmain : ∀ m n, m < n → key m = key n →
      ∃ (W : ℕ → Submodule ℝ (E d)) (p : ℕ) (R : Ortho d), 1 ≤ p ∧ R ∈ S.rotGroup ∧
        (∀ i ≤ d, Module.finrank ℝ (W i) = i) ∧ (∀ i < d, W i ≤ W (i + 1)) ∧
        ∀ i ≤ d, (W i).map (S.σ ^ p).toLinearMap =
          (W i).map R.toLinearEquiv.toLinearMap := by
    intro m n hmn hkey
    refine ⟨fun i => (V i).map (S.σ ^ m).toLinearMap, n - m, B n * (B m)⁻¹, by omega,
      S.rotGroup.mul_mem (hB n) (S.rotGroup.inv_mem (hB m)), ?_, ?_, ?_⟩
    · intro i hi
      exact (LinearEquiv.finrank_map_eq _ _).trans (hdim i hi)
    · intro i hi
      exact Submodule.map_mono (hmono i hi)
    · intro i hi
      have hk : ((V i).map (S.σ ^ m).toLinearMap).map (B m).symm.toLinearEquiv.toLinearMap =
          ((V i).map (S.σ ^ n).toLinearMap).map (B n).symm.toLinearEquiv.toLinearMap :=
        congrArg (fun f : Fin (d + 1) → T => (f ⟨i, Nat.lt_succ_of_le hi⟩).val) hkey
      have e1 : ((V i).map (S.σ ^ m).toLinearMap).map (S.σ ^ (n - m)).toLinearMap =
          (V i).map (S.σ ^ n).toLinearMap := by
        rw [← Submodule.map_comp]
        congr 1
        refine LinearMap.ext fun x => ?_
        change (S.σ ^ (n - m) * S.σ ^ m) x = (S.σ ^ n) x
        rw [← pow_add, Nat.sub_add_cancel hmn.le]
      have e2 : ((V i).map (S.σ ^ m).toLinearMap).map
          (B n * (B m)⁻¹).toLinearEquiv.toLinearMap = (V i).map (S.σ ^ n).toLinearMap := by
        have h1 : (B n * (B m)⁻¹).toLinearEquiv.toLinearMap =
            (B n).toLinearEquiv.toLinearMap ∘ₗ (B m).symm.toLinearEquiv.toLinearMap :=
          LinearMap.ext fun x => rfl
        have h2 : (B n).toLinearEquiv.toLinearMap ∘ₗ (B n).symm.toLinearEquiv.toLinearMap =
            LinearMap.id := LinearMap.ext fun x => by simp
        rw [h1, Submodule.map_comp, hk, ← Submodule.map_comp, h2, Submodule.map_id]
      change ((V i).map (S.σ ^ m).toLinearMap).map (S.σ ^ (n - m)).toLinearMap =
        ((V i).map (S.σ ^ m).toLinearMap).map (B n * (B m)⁻¹).toLinearEquiv.toLinearMap
      rw [e1, e2]
  obtain ⟨x, y, hxy, hk⟩ := Finite.exists_ne_map_eq_of_infinite key
  rcases lt_or_gt_of_ne hxy with h | h
  · exact hmain x y h hk
  · exact hmain y x h hk.symm

/-- Step 4 of the V4 proof of `power_factorisation` (V4 1.15): "block upper triangular
in a basis adapted to the flag". A complete flag of subspaces has an adapted basis. -/
private theorem power_factorisation_step4_adapted_basis (W : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (W i) = i) (hmono : ∀ i < d, W i ≤ W (i + 1)) :
    ∃ b : Module.Basis (Fin d) ℝ (E d), ∀ k ≤ d,
      W k = Submodule.span ℝ (b '' {i : Fin d | (i : ℕ) < k}) := by
  classical
  have hex : ∀ i : Fin d, ∃ x ∈ W (i + 1), x ∉ W i := by
    intro i
    apply SetLike.exists_of_lt
    refine lt_of_le_of_ne (hmono i i.isLt) ?_
    intro h
    have h1 := hdim i i.isLt.le
    have h2 := hdim (i + 1) i.isLt
    rw [h] at h1
    omega
  choose v hvW hvn using hex
  have hspan : ∀ k ≤ d, Submodule.span ℝ (v '' {i : Fin d | (i : ℕ) < k}) = W k := by
    intro k
    induction k with
    | zero =>
      intro _
      have h0 := hdim 0 (Nat.zero_le _)
      rw [Submodule.finrank_eq_zero] at h0
      rw [h0]
      simp
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hset : {i : Fin d | (i : ℕ) < k + 1} =
          {i : Fin d | (i : ℕ) < k} ∪ {⟨k, by omega⟩} := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
        omega
      rw [hset, Set.image_union, Submodule.span_union, ih', Set.image_singleton]
      have hle : W k ⊔ Submodule.span ℝ {v ⟨k, by omega⟩} ≤ W (k + 1) := by
        refine sup_le (hmono k (by omega)) ?_
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hvW ⟨k, by omega⟩
      apply Submodule.eq_of_le_of_finrank_eq hle
      apply le_antisymm (Submodule.finrank_mono hle)
      rw [hdim (k + 1) hk]
      have hlt : W k < W k ⊔ Submodule.span ℝ {v ⟨k, by omega⟩} := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro h
        apply hvn ⟨k, by omega⟩
        rw [h]
        exact Submodule.mem_sup_right (Submodule.subset_span rfl)
      have := Submodule.finrank_lt_finrank_of_lt hlt
      rw [hdim k (by omega)] at this
      omega
  have htop : W d = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hdim d le_rfl, finrank_euclideanSpace_fin]
  have hle : (⊤ : Submodule ℝ (E d)) ≤ Submodule.span ℝ (Set.range v) := by
    rw [← htop, ← hspan d le_rfl]
    apply Submodule.span_mono
    rintro _ ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩
  let b := basisOfTopLeSpanOfCardEqFinrank v hle (by simp)
  refine ⟨b, fun k hk => ?_⟩
  have hb : (b : Fin d → E d) = v := coe_basisOfTopLeSpanOfCardEqFinrank v hle _
  rw [hb]
  exact (hspan k hk).symm

/-- Step 5 of the V4 proof of `power_factorisation` (V4 1.15): "all its eigenvalues are
real and nonzero ... `L := L_1^2` has positive spectrum". A map that is upper triangular
in some basis has a square with positive real spectrum. -/
private theorem power_factorisation_step5_square_positive (b : Module.Basis (Fin d) ℝ (E d))
    (L₁ : E d ≃ₗ[ℝ] E d)
    (hL : ∀ j : Fin d, L₁ (b j) ∈ Submodule.span ℝ (b '' {i : Fin d | (i : ℕ) < j + 1})) :
    PositiveRealSpectrum (L₁ * L₁) := by
  classical
  let M := LinearMap.toMatrix b b L₁.toLinearMap
  have hM : M.BlockTriangular id := by
    intro i j hji
    change LinearMap.toMatrix b b L₁.toLinearMap i j = 0
    rw [LinearMap.toMatrix_apply]
    have hs := (Module.Basis.mem_span_image b).mp (hL j)
    by_contra hne
    have hi := hs (Finsupp.mem_support_iff.mpr hne)
    simp only [Set.mem_setOf_eq] at hi
    have : (j : ℕ) < i := hji
    omega
  have hmul : LinearMap.toMatrix b b (L₁ * L₁).toLinearMap = M * M := by
    rw [← LinearMap.toMatrix_mul]
    rfl
  have hdiag : ∀ i, (M * M) i i = M i i * M i i := by
    intro i
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single i
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hM h, zero_mul]
      · rw [hM h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hchar : (L₁ * L₁).toLinearMap.charpoly = ∏ i : Fin d, (Polynomial.X -
      Polynomial.C (M i i * M i i)) := by
    rw [← LinearMap.charpoly_toMatrix (L₁ * L₁).toLinearMap b, hmul,
      Matrix.charpoly_of_upperTriangular _ (hM.mul hM)]
    simp only [hdiag]
  have hdet : ∀ i, M i i ≠ 0 := by
    have h1 : M.det ≠ 0 := by
      rw [LinearMap.det_toMatrix]
      exact (LinearEquiv.isUnit_det' L₁).ne_zero
    rw [Matrix.det_of_upperTriangular hM] at h1
    exact fun i => (Finset.prod_ne_zero_iff.mp h1) i (Finset.mem_univ i)
  intro z hz
  rw [hchar, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_finset_prod,
    Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, _, hi⟩ := hz
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at hi
  have hz' : z = ((M i i * M i i : ℝ) : ℂ) := by
    rw [sub_eq_zero] at hi
    simpa using hi
  rw [hz']
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact mul_self_pos.mpr (hdet i)

/-- Step 6 of the V4 proof of `power_factorisation` (V4 1.15, using 1.10(a)):
"`L_1` normalises `H`". A linear map whose conjugations, and those of its inverse,
preserve the compatible group normalises it as a set. -/
private theorem power_factorisation_step6_normalizes (T : E d ≃ₗ[ℝ] E d)
    (h1 : ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup, h'.toLinearEquiv = T * h.toLinearEquiv * T⁻¹)
    (h2 : ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup,
      h'.toLinearEquiv = T⁻¹ * h.toLinearEquiv * T⁻¹⁻¹) :
    (fun h : Ortho d => T * h.toLinearEquiv * T⁻¹) '' (S.rotGroup : Set (Ortho d)) =
      (fun h : Ortho d => h.toLinearEquiv) '' (S.rotGroup : Set (Ortho d)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨h', hh', e⟩ := h1 h hh
    exact ⟨h', hh', e⟩
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨h', hh', e⟩ := h2 h hh
    refine ⟨h', hh', ?_⟩
    show T * h'.toLinearEquiv * T⁻¹ = h.toLinearEquiv
    rw [e, inv_inv]
    group

/-- Step 6 of the V4 proof of `power_factorisation` (V4 1.10(a)): conjugation-invariance
of the compatible group is preserved by products. -/
private theorem power_factorisation_step6_conj_mul (T₁ T₂ : E d ≃ₗ[ℝ] E d)
    (h1 : ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup, h'.toLinearEquiv = T₁ * h.toLinearEquiv * T₁⁻¹)
    (h2 : ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup, h'.toLinearEquiv = T₂ * h.toLinearEquiv * T₂⁻¹) :
    ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup,
      h'.toLinearEquiv = (T₁ * T₂) * h.toLinearEquiv * (T₁ * T₂)⁻¹ := by
  intro h hh
  obtain ⟨h', hh', e'⟩ := h2 h hh
  obtain ⟨h'', hh'', e''⟩ := h1 h' hh'
  refine ⟨h'', hh'', ?_⟩
  rw [e'', e', mul_inv_rev]
  simp only [mul_assoc]

/-- Step 6 of the V4 proof of `power_factorisation` (V4 1.10(a)): compatible rotations
conjugate the compatible group into itself. -/
private theorem power_factorisation_step6_conj_ortho (R : Ortho d) (hR : R ∈ S.rotGroup) :
    ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup,
      h'.toLinearEquiv = R.toLinearEquiv * h.toLinearEquiv * R.toLinearEquiv⁻¹ := by
  intro h hh
  exact ⟨R * h * R⁻¹, S.rotGroup.mul_mem (S.rotGroup.mul_mem hR hh) (S.rotGroup.inv_mem hR),
    LinearEquiv.ext fun x => rfl⟩

/-- Step 6 of the V4 proof of `power_factorisation` (V4 1.10(a)): integral powers of `σ`
conjugate the compatible group into itself. -/
private theorem power_factorisation_step6_conj_zpow (m : ℤ) :
    ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup,
      h'.toLinearEquiv = S.σ ^ m * h.toLinearEquiv * (S.σ ^ m)⁻¹ := by
  intro h hh
  obtain ⟨Q, hQ, e⟩ := S.rotGroup_conj_zpow m h hh
  exact ⟨Q, hQ, by rw [e, linearConj, zpow_neg]⟩

/-- P10, V4 1.15: a power admits the prescribed factorisation.
DEVIATION: `Nonempty S.ι` is explicit because stage 1 allows an empty catalogue.
V4's proof chooses a prototile and vertex; without any tiles an arbitrary expansion
need not have a positive-spectrum power modulo the trivial compatible group. -/
theorem power_factorisation (S : SubstSystem d) [Nonempty S.ι] :
    Nonempty (PowerFactorisation S) := by
  classical
  obtain ⟨W, p, R, hp, hR, hdim, hmono, hinv⟩ := power_factorisation_step3_recurrence S
  obtain ⟨b, hb⟩ := power_factorisation_step4_adapted_basis W hdim hmono
  let L₁ : E d ≃ₗ[ℝ] E d := (R⁻¹ : Ortho d).toLinearEquiv * S.σ ^ (p : ℤ)
  have hL : ∀ j : Fin d,
      L₁ (b j) ∈ Submodule.span ℝ (b '' {i : Fin d | (i : ℕ) < j + 1}) := by
    intro j
    have hj : (j : ℕ) + 1 ≤ d := j.isLt
    rw [← hb _ hj]
    have hbj : b j ∈ W (j + 1) := by
      rw [hb _ hj]
      exact Submodule.subset_span ⟨j, show (j : ℕ) < j + 1 by omega, rfl⟩
    have hs : (S.σ ^ p) (b j) ∈ (W (j + 1)).map R.toLinearEquiv.toLinearMap := by
      rw [← hinv _ hj]
      exact Submodule.mem_map_of_mem hbj
    obtain ⟨w, hw, hRw⟩ := Submodule.mem_map.mp hs
    have h1 : L₁ (b j) = R.symm ((S.σ ^ p) (b j)) := by
      simp only [L₁, zpow_natCast]
      rfl
    rw [h1, ← hRw]
    convert hw
    exact R.symm_apply_apply w
  obtain ⟨Q, hQ, hQe⟩ := S.rotGroup_conj_zpow (p : ℤ) R hR
  have e1 : (Q * R).toLinearEquiv = Q.toLinearEquiv * R.toLinearEquiv :=
    LinearEquiv.ext fun x => rfl
  have e2 : (R⁻¹ : Ortho d).toLinearEquiv = R.toLinearEquiv⁻¹ :=
    LinearEquiv.ext fun x => rfl
  have hfactor : S.σ ^ (p + p) = (Q * R).toLinearEquiv * (L₁ * L₁) := by
    have e3 : S.σ ^ (p + p) = S.σ ^ ((p : ℤ) + (p : ℤ)) := by
      rw [← Nat.cast_add, zpow_natCast]
    rw [e3, e1, hQe, linearConj]
    simp only [L₁, e2]
    group
  have hf1 := power_factorisation_step6_conj_mul (S := S) _ _
    (power_factorisation_step6_conj_ortho R⁻¹ (S.rotGroup.inv_mem hR))
    (power_factorisation_step6_conj_zpow (S := S) (p : ℤ))
  have hb1 := power_factorisation_step6_conj_mul (S := S) _ _
    (power_factorisation_step6_conj_zpow (S := S) (-(p : ℤ)))
    (power_factorisation_step6_conj_ortho R hR)
  have hLinv : L₁⁻¹ = S.σ ^ (-(p : ℤ)) * R.toLinearEquiv := by
    simp only [L₁, mul_inv_rev, zpow_neg, e2, inv_inv]
  have hf2 : ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup,
      h'.toLinearEquiv = L₁⁻¹ * h.toLinearEquiv * L₁⁻¹⁻¹ := by
    rw [hLinv]
    exact hb1
  have hF := power_factorisation_step6_conj_mul (S := S) L₁ L₁ hf1 hf1
  have hB : ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup,
      h'.toLinearEquiv = (L₁ * L₁)⁻¹ * h.toLinearEquiv * (L₁ * L₁)⁻¹⁻¹ := by
    rw [mul_inv_rev]
    exact power_factorisation_step6_conj_mul (S := S) L₁⁻¹ L₁⁻¹ hf2 hf2
  exact ⟨⟨p + p, by omega, Q * R, S.rotGroup.mul_mem hQ hR, L₁ * L₁, hfactor,
    power_factorisation_step6_normalizes (L₁ * L₁) hF hB,
    power_factorisation_step5_square_positive b L₁ hL⟩⟩

/-- P11, V4 1.16(a): the positive factor centralizes the full compatible group. -/
theorem L_commutes (F : PowerFactorisation S) (h : Ortho d) (hh : h ∈ S.rotGroup) :
    F.L * h.toLinearEquiv = h.toLinearEquiv * F.L := by
  sorry

/-- Step 1 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"There is q ≥ 1 with L^q V ∈ H V". Apply the finite permutation of direction
orbits to a multiple of the factorisation exponent, then remove the R factor. -/
private theorem L_fixes_directions_sides_step1_orbit_return (F : PowerFactorisation S)
    (V : Submodule ℝ (E d)) (hV : V ∈ S.hPi) :
    ∃ q : ℕ, 1 ≤ q ∧ ∃ h ∈ S.rotGroup,
      V.map (F.L ^ q).toLinearMap = V.map h.toLinearEquiv.toLinearMap := by
  classical
  obtain ⟨hfinite, _, p, hp⟩ := S.orbits_finite
  letI : Fintype S.directionOrbits := hfinite.fintype
  have hpiter : ∀ (n : ℕ) (O : S.directionOrbits),
      ((p ^ n) O).val = (fun U => U.map (S.σ ^ n).toLinearMap) '' O.val := by
    intro n
    induction n with
    | zero => intro O; simp
    | succ n ih =>
      intro O
      rw [pow_succ', Equiv.Perm.mul_apply, hp, ih, Set.image_image]
      congr 1
      funext U
      simp [pow_succ', LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp,
        ← Submodule.map_comp]
  obtain ⟨U, hU, r, hr, hVU⟩ := hV
  let O : S.directionOrbits := ⟨S.directionOrbit U, U, hU, rfl⟩
  let q := orderOf p
  have hq : 1 ≤ q := orderOf_pos p
  have hpq : p ^ (F.power * q) = 1 := by
    rw [Nat.mul_comm, pow_mul]
    simp [q]
  have hreturn : V.map (S.σ ^ (F.power * q)).toLinearMap ∈ O.val := by
    rw [← show ((p ^ (F.power * q)) O).val = O.val by simp [hpq], hpiter]
    exact ⟨V, ⟨r, hr, hVU⟩, rfl⟩
  obtain ⟨r', hr', hreturn⟩ := hreturn
  have hfac : S.σ ^ (F.power * q) = F.R.toLinearEquiv ^ q * F.L ^ q := by
    rw [pow_mul, F.factor]
    exact (show Commute F.R.toLinearEquiv F.L from
      (L_commutes F F.R F.R_mem).symm).mul_pow q
  refine ⟨q, hq, (F.R ^ q)⁻¹ * r' * r⁻¹,
    S.rotGroup.mul_mem (S.rotGroup.mul_mem
      (S.rotGroup.inv_mem (S.rotGroup.pow_mem F.R_mem q)) hr')
      (S.rotGroup.inv_mem hr), ?_⟩
  have hcancel := congrArg
    (fun W : Submodule ℝ (E d) =>
      W.map ((F.R.toLinearEquiv ^ q)⁻¹).toLinearMap) hreturn
  rw [hfac] at hcancel
  simp only [← Submodule.map_comp, ← Module.End.mul_eq_comp,
    ← LinearEquiv.coe_toLinearMap_mul, inv_mul_cancel_left] at hcancel
  have hRpow : (F.R ^ q).toLinearEquiv = F.R.toLinearEquiv ^ q := by
    induction q with
    | zero => rfl
    | succ n ih =>
      change (F.R ^ n).toLinearEquiv * F.R.toLinearEquiv =
        F.R.toLinearEquiv ^ n * F.R.toLinearEquiv
      rw [ih]
  rw [hcancel, hVU]
  simp only [← Submodule.map_comp, ← Module.End.mul_eq_comp,
    ← LinearEquiv.coe_toLinearMap_mul]
  congr 1
  ext x
  simp [← hRpow]

open scoped BigOperators

/-- Step 1 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"positive real spectrum". Complex roots lie in the image of ℝ, so the
characteristic polynomial splits over ℝ and all its real roots are positive. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step1_real_splitting
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ F] (M : Module.End ℝ F)
    (hpos : ∀ z : ℂ, (M.charpoly.map (algebraMap ℝ ℂ)).IsRoot z →
      z.im = 0 ∧ 0 < z.re) :
    M.charpoly.Splits ∧ ∀ r : ℝ, M.charpoly.IsRoot r → 0 < r := by
  constructor
  · apply Polynomial.Splits.of_splits_map (algebraMap ℝ ℂ) (IsAlgClosed.splits _)
    intro z hz
    have hz' := (Polynomial.mem_roots (Polynomial.map_ne_zero M.charpoly_monic.ne_zero)).mp hz
    refine ⟨z.re, ?_⟩
    apply Complex.ext <;> simp [hpos z hz']
  · intro r hr
    exact (hpos r (Polynomial.IsRoot.map hr)).2

/-- Step 2 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"decompose u into generalised eigenvectors". Factor the characteristic
polynomial into coprime powers of linear factors and decompose its kernel;
Cayley--Hamilton makes that kernel the whole space. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step2_primary_decomposition
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ F] (M : Module.End ℝ F)
    (hsplit : M.charpoly.Splits) (u : F) :
    ∃ v : ℝ → F,
      u = ∑ r ∈ M.charpoly.roots.toFinset, v r ∧
      ∀ r : ℝ, ((M - r • (1 : Module.End ℝ F)) ^ M.charpoly.roots.card) (v r) = 0 := by
  classical
  let p : ℝ → Polynomial ℝ := fun r => (Polynomial.X - Polynomial.C r) ^
    M.charpoly.rootMultiplicity r
  have hc (r t : ℝ) (hrt : r ≠ t) : IsCoprime (p r) (p t) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hrt).isUnit).pow
  have hker (s : Finset ℝ) :
      s.sup (fun r => LinearMap.ker (Polynomial.aeval M (p r))) =
        LinearMap.ker (Polynomial.aeval M (∏ r ∈ s, p r)) := by
    induction s using Finset.induction_on with
    | empty => simp [Module.End.one_eq_id]
    | @insert r s hrs ih =>
      rw [Finset.sup_insert, Finset.prod_insert hrs, ih]
      apply Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime
      exact IsCoprime.prod_right fun t ht => hc r t (by rintro rfl; exact hrs ht)
  have hp : ∏ r ∈ M.charpoly.roots.toFinset, p r = M.charpoly := by
    calc
      _ = (M.charpoly.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod :=
        (Polynomial.prod_multiset_root_eq_finset_root (p := M.charpoly)).symm
      _ = M.charpoly := (hsplit.eq_prod_roots_of_monic M.charpoly_monic).symm
  have hu : u ∈ ⨆ r ∈ M.charpoly.roots.toFinset,
      LinearMap.ker (Polynomial.aeval M (p r)) := by
    rw [← Finset.sup_eq_iSup, hker, hp, LinearMap.aeval_self_charpoly]
    simp
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ u).mp hu
  refine ⟨fun r => v r, hv.symm, ?_⟩
  intro r
  have hr : ((M - r • (1 : Module.End ℝ F)) ^ M.charpoly.rootMultiplicity r)
      (v r : F) = 0 := by
    simpa only [p, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, LinearMap.mem_ker] using (v r).property
  have hle : M.charpoly.rootMultiplicity r ≤ M.charpoly.roots.card := by
    rw [← Polynomial.count_roots]
    exact Multiset.count_le_card _ _
  rw [← Nat.sub_add_cancel hle, pow_add, Module.End.mul_apply, hr, map_zero]

/-- Step 3 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"the largest Jordan index occurring there". On a generalized eigenvector,
the binomial expansion of (r I + N)^n terminates at the nilpotence index. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step3_jordan_binomial
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    (M : Module.End ℝ F) (r : ℝ) (hr : r ≠ 0) (v : F) (m : ℕ)
    (hnil : ((M - r • (1 : Module.End ℝ F)) ^ m) v = 0) (n : ℕ) :
    (M ^ n) v = ∑ j ∈ Finset.range m,
      (r ^ n * ((n.choose j : ℝ) / r ^ j)) •
        ((M - r • (1 : Module.End ℝ F)) ^ j) v := by
  let N := M - r • (1 : Module.End ℝ F)
  have hcomm : Commute N (r • (1 : Module.End ℝ F)) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using Algebra.commute_algebraMap_right r N
  have heq : N + r • (1 : Module.End ℝ F) = M := sub_add_cancel M _
  have hpow := congrArg (fun T : Module.End ℝ F => T v) (hcomm.add_pow n)
  rw [heq] at hpow
  simp only [LinearMap.sum_apply, Module.End.mul_apply, _root_.smul_pow, one_pow,
    LinearMap.smul_apply, Module.End.one_apply, Module.End.natCast_apply,
    map_smul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul] at hpow
  have hsum : (M ^ n) v = ∑ j ∈ Finset.range (n + 1),
      (r ^ n * ((n.choose j : ℝ) / r ^ j)) • (N ^ j) v := by
    rw [hpow]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    rw [pow_sub₀ r hr hjn]
    congr 1
    ring
  rw [hsum]
  rcases le_total m (n + 1) with hmn | hnm
  · symm
    apply Finset.sum_subset (Finset.range_mono hmn)
    intro j hj hjm
    have hzero : (N ^ j) v = 0 :=
      Module.End.pow_map_zero_of_le (by simpa using hjm) hnil
    rw [hzero, smul_zero]
  · apply Finset.sum_subset (Finset.range_mono hnm)
    intro j hj hjn
    have hn : n < j := by simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hjn
    simp [Nat.choose_eq_zero_of_lt hn]

/-- Step 4 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"decompose u into generalised eigenvectors". Expand the binomial
coefficients as polynomials in n to obtain a finite sum of r^n n^j times
constant vectors, with every exponential base r positive. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step4_jordan_expansion
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ F] (M : Module.End ℝ F)
    (hsplit : M.charpoly.Splits)
    (hpos : ∀ r : ℝ, M.charpoly.IsRoot r → 0 < r) (u : F) :
    ∃ (s : Finset ℝ) (m : ℕ) (a : ℝ → ℕ → F),
      (∀ r ∈ s, 0 < r) ∧ ∀ n : ℕ,
        (M ^ n) u = ∑ r ∈ s, ∑ j ∈ Finset.range m,
          (r ^ n * (n : ℝ) ^ j) • a r j := by
  classical
  obtain ⟨v, hv, hnil⟩ := L_fixes_directions_sides_step2_spectral_limit_step2_primary_decomposition M hsplit u
  let m := M.charpoly.roots.card
  let N : ℝ → Module.End ℝ F := fun r => M - r • (1 : Module.End ℝ F)
  let a : ℝ → ℕ → F := fun r j => ∑ t ∈ Finset.range m,
    ((descPochhammer ℝ t).coeff j / ((t.factorial : ℝ) * r ^ t)) • (N r ^ t) (v r)
  have hpos' (r : ℝ) (hr : r ∈ M.charpoly.roots.toFinset) : 0 < r :=
    hpos r ((Polynomial.mem_roots M.charpoly_monic.ne_zero).mp (Multiset.mem_toFinset.mp hr))
  refine ⟨M.charpoly.roots.toFinset, m, a, hpos', ?_⟩
  intro n
  rw [hv, map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [L_fixes_directions_sides_step2_spectral_limit_step3_jordan_binomial M r (hpos' r hr).ne' (v r) m (hnil r) n]
  change (∑ t ∈ Finset.range m,
    (r ^ n * ((n.choose t : ℝ) / r ^ t)) • (N r ^ t) (v r)) = _
  simp only [a, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.sum_smul]
  congr 1
  rw [Nat.cast_choose_eq_descPochhammer_div]
  rw [Polynomial.eval_eq_sum_range' (by simpa using ht :
    (descPochhammer ℝ t).natDegree < m) (n : ℝ)]
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Step 5 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"let μ be the largest eigenvalue with nonzero component". Before choosing
a dominant term, collect all coefficients having the same exponential base
and polynomial degree; this accounts for cancellations. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step5_collect_terms
    {ι F : Type*} [AddCommGroup F] [Module ℝ F]
    (t : Finset ι) (r : ι → ℝ) (j : ι → ℕ) (v : ι → F)
    (hpos : ∀ i ∈ t, 0 < r i) :
    ∃ (s : Finset ℝ) (m : ℕ) (a : ℝ → ℕ → F),
      (∀ μ ∈ s, 0 < μ) ∧ ∀ n : ℕ,
        (∑ i ∈ t, ((r i) ^ n * (n : ℝ) ^ j i) • v i) =
          ∑ μ ∈ s, ∑ k ∈ Finset.range m, (μ ^ n * (n : ℝ) ^ k) • a μ k := by
  classical
  let s := t.image r
  let m := t.sup j + 1
  let a := fun μ k => ∑ i ∈ t.filter (fun i => r i = μ ∧ j i = k), v i
  have hs (i : ι) (hi : i ∈ t) : r i ∈ s := Finset.mem_image_of_mem r hi
  have hm (i : ι) (hi : i ∈ t) : j i ∈ Finset.range m :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hi))
  refine ⟨s, m, a, ?_, ?_⟩
  · intro μ hμ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hμ
    exact hpos i hi
  · intro n
    rw [← Finset.sum_fiberwise_of_maps_to hs]
    apply Finset.sum_congr rfl
    intro μ hμ
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun i hi => hm i (Finset.mem_filter.mp hi).1)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.filter_filter]
    simp only [a, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi, hr, hj⟩ := Finset.mem_filter.mp hi
    rw [hr, hj]

/-- Step 6 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"Λ^{dim V} L^q has positive real spectrum too". The needed consequence
is obtained directly by multilinearity: a wedge of exponential-polynomial
sequences has the same form, and its bases are products of positive bases. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step6_multilinear_expansion
    {ι F G : Type*} [Fintype ι]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
    (f : MultilinearMap ℝ (fun _ : ι => F) G)
    (s : ι → Finset ℝ) (m : ι → ℕ) (a : ι → ℝ → ℕ → F)
    (hpos : ∀ i r, r ∈ s i → 0 < r) :
    ∃ (t : Finset ℝ) (q : ℕ) (b : ℝ → ℕ → G),
      (∀ r ∈ t, 0 < r) ∧ ∀ n : ℕ,
        f (fun i => ∑ r ∈ s i, ∑ j ∈ Finset.range (m i),
          (r ^ n * (n : ℝ) ^ j) • a i r j) =
          ∑ r ∈ t, ∑ j ∈ Finset.range q, (r ^ n * (n : ℝ) ^ j) • b r j := by
  classical
  let A := fun i => (s i) ×ˢ Finset.range (m i)
  let T := Fintype.piFinset A
  let r := fun z : ι → ℝ × ℕ => ∏ i, (z i).1
  let j := fun z : ι → ℝ × ℕ => ∑ i, (z i).2
  let v := fun z : ι → ℝ × ℕ => f (fun i => a i (z i).1 (z i).2)
  have hpos' (z : ι → ℝ × ℕ) (hz : z ∈ T) : 0 < r z := by
    apply Finset.prod_pos
    intro i hi
    exact hpos i _ (Finset.mem_product.mp (Fintype.mem_piFinset.mp hz i)).1
  obtain ⟨t, q, b, hb, heq⟩ := L_fixes_directions_sides_step2_spectral_limit_step5_collect_terms T r j v hpos'
  refine ⟨t, q, b, hb, ?_⟩
  intro n
  rw [← heq]
  have hsum : (fun i => ∑ r ∈ s i, ∑ j ∈ Finset.range (m i),
      (r ^ n * (n : ℝ) ^ j) • a i r j) =
      (fun i => ∑ z ∈ A i, (z.1 ^ n * (n : ℝ) ^ z.2) • a i z.1 z.2) := by
    funext i
    simp only [A, Finset.sum_product]
  rw [hsum, f.map_sum_finset]
  apply Finset.sum_congr rfl
  intro z hz
  rw [f.map_smul_univ]
  congr 1
  simp only [r, j, Finset.prod_mul_distrib, ← Finset.prod_pow, Finset.prod_pow_eq_pow_sum]

open Filter Topology in
/-- Step 7 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"let μ be the largest eigenvalue with nonzero component and s the
largest Jordan index occurring there". After collecting equal bases and
degrees, divide by μ^n n^s; every other term tends to zero and the surviving
coefficient is nonzero. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step7_dominant_term
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Finset ℝ) (m : ℕ) (a : ℝ → ℕ → F)
    (hpos : ∀ r ∈ s, 0 < r)
    (hne : ∃ r ∈ s, ∃ j ∈ Finset.range m, a r j ≠ 0) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ k : ℕ, ∃ w : F, w ≠ 0 ∧
      Tendsto (fun n : ℕ => (μ ^ n * (n : ℝ) ^ k)⁻¹ •
        ∑ r ∈ s, ∑ j ∈ Finset.range m, (r ^ n * (n : ℝ) ^ j) • a r j)
        atTop (𝓝 w) := by
  classical
  let t := s.filter (fun r => ∃ j ∈ Finset.range m, a r j ≠ 0)
  have ht : t.Nonempty := by
    obtain ⟨r, hr, j, hj, ha⟩ := hne
    exact ⟨r, Finset.mem_filter.mpr ⟨hr, j, hj, ha⟩⟩
  let μ := t.max' ht
  have hμt : μ ∈ t := t.max'_mem ht
  have hμs : μ ∈ s := (Finset.mem_filter.mp hμt).1
  have hμ : 0 < μ := hpos μ hμs
  let u := (Finset.range m).filter (fun j => a μ j ≠ 0)
  have hu : u.Nonempty := by
    obtain ⟨j, hj, ha⟩ := (Finset.mem_filter.mp hμt).2
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, ha⟩⟩
  let k := u.max' hu
  have hku : k ∈ u := u.max'_mem hu
  have hkm : k ∈ Finset.range m := (Finset.mem_filter.mp hku).1
  have hak : a μ k ≠ 0 := (Finset.mem_filter.mp hku).2
  refine ⟨μ, hμ, k, a μ k, hak, ?_⟩
  have hratio (r : ℝ) (j : ℕ) (hr : r ∈ s) (ha : a r j ≠ 0)
      (hj : j ∈ Finset.range m) :
      Tendsto (fun n : ℕ => (μ ^ n * (n : ℝ) ^ k)⁻¹ *
        (r ^ n * (n : ℝ) ^ j)) atTop
        (𝓝 (if r = μ ∧ j = k then (1 : ℝ) else 0)) := by
    have hrμ : r ≤ μ := t.le_max' r (Finset.mem_filter.mpr ⟨hr, j, hj, ha⟩)
    rcases hrμ.eq_or_lt with rfl | hrμ
    · have hjk : j ≤ k := u.le_max' j (Finset.mem_filter.mpr ⟨hj, ha⟩)
      rcases hjk.eq_or_lt with rfl | hjk
      · simp only [and_self, ite_true]
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        exact (inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero n hμ.ne') (pow_ne_zero k hn0))).symm
      · simp only [true_and, ne_of_lt hjk, ite_false]
        have ht0 := tendsto_const_div_pow 1 (k - j) (Nat.sub_ne_zero_of_lt hjk)
        apply ht0.congr'
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        have hk : (n : ℝ) ^ k = (n : ℝ) ^ j * (n : ℝ) ^ (k - j) := by
          rw [← pow_add, Nat.add_sub_of_le hjk.le]
        rw [hk]
        field_simp
    · have hlt : r / μ < 1 := (div_lt_one hμ).mpr hrμ
      have hge : 0 ≤ r / μ := (div_pos (hpos r hr) hμ).le
      have ht0 := tendsto_pow_const_mul_const_pow_of_lt_one j hge hlt
      have hnorm : ∃ c : ℝ, Tendsto (fun n : ℕ => ((n : ℝ) ^ k)⁻¹)
          atTop (𝓝 c) := by
        by_cases hk : k = 0
        · exact ⟨1, by simp [hk]⟩
        · exact ⟨0, by simpa using tendsto_const_div_pow 1 k hk⟩
      obtain ⟨c, hc⟩ := hnorm
      have ht := ht0.mul hc
      simp only [zero_mul] at ht
      simp only [ne_of_lt hrμ, false_and, ite_false]
      convert ht using 1
      funext n
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  have hsum := tendsto_finset_sum s (fun r hr =>
    tendsto_finset_sum (Finset.range m) (fun j hj => show
      Tendsto (fun n : ℕ => (μ ^ n * (n : ℝ) ^ k)⁻¹ •
        ((r ^ n * (n : ℝ) ^ j) • a r j)) atTop
        (𝓝 (if r = μ ∧ j = k then a μ k else 0)) from by
      by_cases ha : a r j = 0
      · have hnot : ¬ (r = μ ∧ j = k) := by
          rintro ⟨rfl, rfl⟩
          exact hak ha
        simp [ha, hnot]
      · have ht := (hratio r j hr ha hj).smul_const (a r j)
        by_cases h : r = μ ∧ j = k
        · rcases h with ⟨rfl, rfl⟩
          simpa only [and_self, ite_true, one_smul, smul_smul] using ht
        · simpa only [h, ite_false, zero_smul, smul_smul] using ht))
  simpa [Finset.smul_sum, ite_and, hμs, hkm] using hsum

/-- Step 8 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"in the Plücker embedding" and "any nonzero vector u". The wedge of a
linearly independent frame is nonzero, including the empty frame in degree zero. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step8_plucker_nonzero
    {d k : ℕ} (v : Fin k → E d)
    (hv : LinearIndependent ℝ v) : exteriorPower.ιMulti ℝ k v ≠ 0 := by
  have hi := exteriorPower.ιMulti_family_linearIndependent_field (n := k) hv
  have hn := hi.ne_zero (Set.powersetCard.ofFinEmbEquiv
    (OrderEmbedding.ofStrictMono (fun i : Fin k => i) (fun _ _ h => h)))
  simpa only [exteriorPower.ιMulti_family, Equiv.symm_apply_apply,
    OrderEmbedding.coe_ofStrictMono, Function.comp_id] using hn

/-- Step 9 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"in the Plücker embedding". Choose a nonzero exterior coordinate and
contract against all but one of its covectors. The resulting k linear maps
give an independent frame at that coordinate; on a decomposable vector,
the frame lies in the subspace represented by the vector. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step9_plucker_chart
    {d k : ℕ} (w : ⋀[ℝ]^k (E d)) (hw : w ≠ 0) :
    ∃ B : (⋀[ℝ]^k (E d)) →ₗ[ℝ] (Fin k → E d),
      LinearIndependent ℝ (B w) ∧
      ∀ (v : Fin k → E d) (i : Fin k),
        B (exteriorPower.ιMulti ℝ k v) i ∈ Submodule.span ℝ (Set.range v) := by
  classical
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  have hrepr : (b.exteriorPower k).repr w ≠ 0 :=
    (b.exteriorPower k).repr.map_ne_zero_iff.mpr hw
  obtain ⟨s, hs⟩ : ∃ s, (b.exteriorPower k).repr w s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hrepr (Finsupp.ext h)
  let φ : Fin k → Module.Dual ℝ (E d) := fun i =>
    b.coord (Set.powersetCard.ofFinEmbEquiv.symm s i)
  let A := exteriorPower.alternatingMapToDual ℝ (E d) k
  have hAw : A φ w ≠ 0 := by
    simpa only [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual,
      exteriorPower.ιMulti_family, exteriorPower.pairingDual,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, φ, A] using hs
  let C : Fin k → Module.Dual ℝ (E d) →ₗ[ℝ] Module.Dual ℝ (⋀[ℝ]^k (E d)) :=
    fun i => A.toMultilinearMap.toLinearMap φ i
  let B : (⋀[ℝ]^k (E d)) →ₗ[ℝ] (Fin k → E d) :=
    LinearMap.pi (fun i => (Module.evalEquiv ℝ (E d)).symm.toLinearMap.comp (C i).flip)
  have hB (x : ⋀[ℝ]^k (E d)) (i : Fin k) (ℓ : Module.Dual ℝ (E d)) :
      ℓ (B x i) = A (Function.update φ i ℓ) x := by
    simp only [B, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.apply_evalEquiv_symm_apply, LinearMap.flip_apply, C,
      MultilinearMap.toLinearMap_apply]
    rfl
  refine ⟨B, ?_, ?_⟩
  · apply LinearIndependent.of_pairwise_dual_eq_zero_one _
      (fun i => (A φ w)⁻¹ • φ i)
    · intro i j hij
      rw [LinearMap.smul_apply, hB, A.map_update_self φ hij.symm]
      simp
    · intro i
      rw [LinearMap.smul_apply, hB, Function.update_eq_self]
      exact inv_mul_cancel₀ hAw
  · intro v i
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp
    intro ℓ hℓ
    rw [hB]
    change exteriorPower.alternatingMapToDual ℝ (E d) k
      (Function.update φ i ℓ) (exteriorPower.ιMulti ℝ k v) = 0
    rw [exteriorPower.alternatingMapToDual_apply_ιMulti]
    apply Matrix.det_eq_zero_of_column_eq_zero i
    intro j
    simp only [Matrix.of_apply, Function.update_self]
    exact (Submodule.mem_dualAnnihilator ℓ).mp hℓ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- Step 10 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"converges in the Grassmannian". The Gram operator f* f of an injective
map is invertible, since its kernel equals the kernel of f. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step10_gram_unit
    {d k : ℕ} (f : E k →L[ℝ] E d)
    (hf : Function.Injective f) : IsUnit (f.adjoint.comp f) := by
  have hinj : Function.Injective (f.adjoint.comp f) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change (f.adjoint.comp f) x = 0 at hx
    apply hf
    rw [map_zero]
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [← f.adjoint_inner_right x (f x)]
    change inner ℝ x ((f.adjoint.comp f) x) = 0
    rw [hx, inner_zero_right]
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- Step 11 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"converges in the Grassmannian". In frame coordinates the orthogonal
projection onto the image of f is f (f* f)⁻¹ f*; the formula follows from
its range and orthogonality properties. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step11_projection_gram
    {d k : ℕ} (f : E k →L[ℝ] E d)
    (hf : IsUnit (f.adjoint.comp f)) :
    f.toLinearMap.range.starProjection =
      f.comp ((Ring.inverse (f.adjoint.comp f)).comp f.adjoint) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨_, rfl⟩
  · rintro y ⟨z, rfl⟩
    change inner ℝ (x - f (Ring.inverse (f.adjoint.comp f) (f.adjoint x))) (f z) = 0
    rw [← f.adjoint_inner_left z]
    have hcancel : (f.adjoint.comp f)
        (Ring.inverse (f.adjoint.comp f) (f.adjoint x)) = f.adjoint x := by
      exact congrArg (fun T : E k →L[ℝ] E k => T (f.adjoint x))
        (Ring.mul_inverse_cancel _ hf)
    change f.adjoint (f (Ring.inverse (f.adjoint.comp f) (f.adjoint x))) = f.adjoint x at hcancel
    simp only [map_sub]
    rw [hcancel, sub_self, inner_zero_left]

open Filter Topology in
/-- Step 12 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"converges in the Grassmannian". Invertible Gram operators form an open
set and inversion is continuous there, so projections depend continuously
in operator norm on an injective limiting map. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step12_projection_continuity
    {d k : ℕ}
    (f : ℕ → E k →L[ℝ] E d) (g : E k →L[ℝ] E d)
    (hg : Function.Injective g) (hfg : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => (f n).toLinearMap.range.starProjection) atTop
      (𝓝 g.toLinearMap.range.starProjection) := by
  let G := fun f : E k →L[ℝ] E d => f.adjoint.comp f
  let P := fun f : E k →L[ℝ] E d => f.comp ((Ring.inverse (G f)).comp f.adjoint)
  have hG : Continuous G := ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id
  have hunit : IsUnit (G g) := L_fixes_directions_sides_step2_spectral_limit_step10_gram_unit g hg
  have hinv : ContinuousAt Ring.inverse (G g) := by
    simpa only [hunit.unit_spec] using NormedRing.inverse_continuousAt hunit.unit
  have hP : ContinuousAt P g := continuousAt_id.clm_comp
    ((hinv.comp hG.continuousAt).clm_comp ContinuousLinearMap.adjoint.continuous.continuousAt)
  have hevent : ∀ᶠ n in atTop, IsUnit (G (f n)) :=
    (hG.continuousAt.tendsto.comp hfg).eventually (Units.isOpen.mem_nhds hunit)
  rw [L_fixes_directions_sides_step2_spectral_limit_step11_projection_gram g hunit]
  apply (hP.tendsto.comp hfg).congr'
  filter_upwards [hevent] with n hn
  exact (L_fixes_directions_sides_step2_spectral_limit_step11_projection_gram (f n) hn).symm

open Filter Topology in
/-- Step 13 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"converges in the Grassmannian". Regard a frame as the columns of a
linear map; convergence to an independent frame therefore implies
operator-norm convergence of the projections onto its span. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step13_frame_projection_limit
    {d k : ℕ}
    (v : ℕ → Fin k → E d) (w : Fin k → E d)
    (hw : LinearIndependent ℝ w) (hlim : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => (Submodule.span ℝ (Set.range (v n))).starProjection)
      atTop (𝓝 (Submodule.span ℝ (Set.range w)).starProjection) := by
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let T : (Fin k → E d) ≃ₗ[ℝ] (E k →L[ℝ] E d) :=
    (b.constr ℝ).trans LinearMap.toContinuousLinearMap
  have hinj : Function.Injective (T w) := by
    intro x y h
    apply b.repr.injective
    apply hw.finsuppLinearCombination_injective
    change (b.constr ℝ w) x = (b.constr ℝ w) y at h
    simpa only [Module.Basis.constr_apply, Finsupp.linearCombination_apply] using h
  have hTlim : Tendsto (fun n => T (v n)) atTop (𝓝 (T w)) :=
    T.continuous_of_finiteDimensional.continuousAt.tendsto.comp hlim
  have h := L_fixes_directions_sides_step2_spectral_limit_step12_projection_continuity (fun n => T (v n)) (T w) hinj hTlim
  simpa only [T, LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap,
    Module.Basis.constr_range] using h

open Filter Topology in
/-- Step 14 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"the limit of decomposable vectors is decomposable because the
Grassmannian is closed". Apply a Plücker chart to the nonzero limiting
vector. Its frames converge and are eventually independent; inclusion and
equality of dimensions identify their spans with the original subspaces. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step14_projection_limit
    {d k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : (⋀[ℝ]^k (E d)) ≃ₗ[ℝ] F)
    (v : ℕ → Fin k → E d) (hv : ∀ n, LinearIndependent ℝ (v n))
    (c : ℕ → ℝ) (w : F) (hw : w ≠ 0)
    (hlim : Tendsto (fun n => c n • e (exteriorPower.ιMulti ℝ k (v n)))
      atTop (𝓝 w)) :
    ∃ P : E d →L[ℝ] E d,
      Tendsto (fun n => (Submodule.span ℝ (Set.range (v n))).starProjection)
        atTop (𝓝 P) := by
  classical
  obtain ⟨B, hB, hmem⟩ := L_fixes_directions_sides_step2_spectral_limit_step9_plucker_chart (e.symm w) (e.symm.map_ne_zero_iff.mpr hw)
  let u := fun n => c n • B (exteriorPower.ιMulti ℝ k (v n))
  have hu : Tendsto u atTop (𝓝 (B (e.symm w))) := by
    have h := (B.comp e.symm.toLinearMap).continuous_of_finiteDimensional.continuousAt.tendsto.comp hlim
    simpa only [Function.comp_def, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul,
      LinearEquiv.symm_apply_apply] using h
  have hevent : ∀ᶠ n in atTop, LinearIndependent ℝ (u n) := hu.eventually hB.eventually
  have hspan : ∀ᶠ n in atTop,
      Submodule.span ℝ (Set.range (u n)) = Submodule.span ℝ (Set.range (v n)) := by
    filter_upwards [hevent] with n hn
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (Submodule.span ℝ (Set.range (v n))).smul_mem (c n) (hmem (v n) i)
    · rw [finrank_span_eq_card hn, finrank_span_eq_card (hv n)]
  refine ⟨(Submodule.span ℝ (Set.range (B (e.symm w)))).starProjection, ?_⟩
  apply (L_fixes_directions_sides_step2_spectral_limit_step13_frame_projection_limit u (B (e.symm w)) hB hu).congr'
  filter_upwards [hspan] with n hn
  rw [hn]

set_option maxHeartbeats 1600000 in
omit [Fact (2 ≤ d)] in
open Filter Topology in
/-- Step 2 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"the sequence of subspaces ... converges in the Grassmannian" for positive
real spectrum. This is expressed as operator-norm convergence of orthogonal
projections. The remaining linear-algebra step is the Plücker/generalized-
eigenvector argument: select the largest eigenvalue and Jordan index in a
nonzero exterior-power vector. No group or substitution hypothesis is used. -/
private theorem L_fixes_directions_sides_step2_spectral_limit
    (L : E d ≃ₗ[ℝ] E d) (hpos : PositiveRealSpectrum L)
    (V : Submodule ℝ (E d)) :
    ∃ P : E d →L[ℝ] E d,
      Tendsto (fun n : ℕ => (V.map (L ^ n).toLinearMap).starProjection)
        atTop (𝓝 P) := by
  by_cases hbot : V = ⊥
  · subst V
    exact ⟨0, by simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E d →L[ℝ] E d))
        atTop (𝓝 0))⟩
  by_cases htop : V = ⊤
  · subst V
    exact ⟨ContinuousLinearMap.id ℝ (E d), by simpa [Submodule.starProjection_top] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => ContinuousLinearMap.id ℝ (E d))
        atTop (𝓝 (ContinuousLinearMap.id ℝ (E d))))⟩
  classical
  let k := Module.finrank ℝ V
  let b := Module.finBasis ℝ V
  let v : Fin k → E d := fun i => b i
  have hv : LinearIndependent ℝ v :=
    b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hspan : Submodule.span ℝ (Set.range v) = V := by
    rw [show Set.range v = V.subtype '' Set.range b from Set.range_comp V.subtype b,
      ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  let X := Fin (Module.finrank ℝ (⋀[ℝ]^k (E d))) → ℝ
  let e : (⋀[ℝ]^k (E d)) ≃ₗ[ℝ] X := (Module.finBasis ℝ _).equivFun
  let f : MultilinearMap ℝ (fun _ : Fin k => E d) X :=
    e.toLinearMap.compMultilinearMap (exteriorPower.ιMulti ℝ k).toMultilinearMap
  have hne : f v ≠ 0 := e.map_ne_zero_iff.mpr
    (L_fixes_directions_sides_step2_spectral_limit_step8_plucker_nonzero v hv)
  obtain ⟨hsplit, hreal⟩ := L_fixes_directions_sides_step2_spectral_limit_step1_real_splitting L.toLinearMap hpos
  choose s m a ha hexp using fun i =>
    L_fixes_directions_sides_step2_spectral_limit_step4_jordan_expansion
      L.toLinearMap hsplit hreal (v i)
  obtain ⟨t, q, c, hc, hcexp⟩ := L_fixes_directions_sides_step2_spectral_limit_step6_multilinear_expansion f s m a ha
  have hpow : ∀ n : ℕ, L.toLinearMap ^ n = (L ^ n).toLinearMap := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]
  have heq : ∀ n : ℕ, f (fun i => (L ^ n) (v i)) =
      ∑ r ∈ t, ∑ j ∈ Finset.range q, (r ^ n * (n : ℝ) ^ j) • c r j := by
    intro n
    simpa only [← hexp, hpow] using hcexp n
  have hcne : ∃ r ∈ t, ∃ j ∈ Finset.range q, c r j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    calc
      f v = f (fun i => (L ^ 0) (v i)) := by simp
      _ = ∑ r ∈ t, ∑ j ∈ Finset.range q, (r ^ 0 * ((0 : ℕ) : ℝ) ^ j) • c r j := heq 0
      _ = 0 := Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun j hj => by
        rw [h r hr j hj, smul_zero]
  obtain ⟨μ, hμ, p, w, hw, hlim⟩ := L_fixes_directions_sides_step2_spectral_limit_step7_dominant_term t q c hc hcne
  have hlim' : Tendsto (fun n : ℕ => (μ ^ n * (n : ℝ) ^ p)⁻¹ •
      e (exteriorPower.ιMulti ℝ k (fun i => (L ^ n) (v i)))) atTop (𝓝 w) := by
    simpa only [← heq] using hlim
  obtain ⟨P, hP⟩ := L_fixes_directions_sides_step2_spectral_limit_step14_projection_limit e (fun n i => (L ^ n) (v i))
    (fun n => hv.map' (L ^ n).toLinearMap (LinearEquiv.ker _))
    (fun n => (μ ^ n * (n : ℝ) ^ p)⁻¹) w hw hlim'
  refine ⟨P, ?_⟩
  have hspan' : ∀ n : ℕ, Submodule.span ℝ (Set.range (fun i => (L ^ n) (v i))) =
      V.map (L ^ n).toLinearMap := by
    intro n
    rw [show Set.range (fun i => (L ^ n) (v i)) =
      (L ^ n).toLinearMap '' Set.range v from Set.range_comp _ _,
      ← Submodule.map_span, hspan]
  simpa only [hspan'] using hP

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"the compact orbit H V". In the orthogonal-projection model of the
Grassmannian, every orthogonal transformation preserves distances. -/
private theorem L_fixes_directions_sides_step3_projection_distance
    (U V : Submodule ℝ (E d)) (r : Ortho d) :
    dist (U.map r.toLinearEquiv.toLinearMap).starProjection
      (V.map r.toLinearEquiv.toLinearMap).starProjection =
      dist U.starProjection V.starProjection := by
  rw [dist_eq_norm, dist_eq_norm]
  have heq : (U.map r.toLinearEquiv.toLinearMap).starProjection -
      (V.map r.toLinearEquiv.toLinearMap).starProjection =
      r.toLinearIsometry.toContinuousLinearMap.comp
        ((U.starProjection - V.starProjection).comp
          r.symm.toLinearIsometry.toContinuousLinearMap) := by
    ext x
    simp [Submodule.starProjection_map_apply]
  rw [heq, LinearIsometry.norm_toContinuousLinearMap_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

omit [Fact (2 ≤ d)] in
open Filter Topology in
/-- Step 4 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"h L^q V = h V, hence L^q V = V". Equivalently, a convergent orbit of one
rotation is constant: distances between successive projections are constant
and converge to zero. This avoids choosing a representative of the limit. -/
private theorem L_fixes_directions_sides_step4_convergent_rotation
    (r : Ortho d) (V : Submodule ℝ (E d))
    (P : E d →L[ℝ] E d)
    (hlim : Tendsto (fun n : ℕ =>
      (V.map (r ^ n).toLinearEquiv.toLinearMap).starProjection) atTop (𝓝 P)) :
    V.map r.toLinearEquiv.toLinearMap = V := by
  have hdist : ∀ n : ℕ,
      dist (V.map (r ^ (n + 1)).toLinearEquiv.toLinearMap).starProjection
        (V.map (r ^ n).toLinearEquiv.toLinearMap).starProjection =
        dist (V.map r.toLinearEquiv.toLinearMap).starProjection V.starProjection := by
    intro n
    have heq : V.map (r ^ (n + 1)).toLinearEquiv.toLinearMap =
        (V.map r.toLinearEquiv.toLinearMap).map
          (r ^ n).toLinearEquiv.toLinearMap := by
      rw [← Submodule.map_comp]
      congr 1
    simpa only [heq] using
      L_fixes_directions_sides_step3_projection_distance
        (V.map r.toLinearEquiv.toLinearMap) V (r ^ n)
  have ht := (hlim.comp (tendsto_add_atTop_nat 1)).dist hlim
  simp only [Function.comp_def, hdist, dist_self] at ht
  have hz := tendsto_nhds_unique ht tendsto_const_nhds
  exact Submodule.starProjection_inj.mp (dist_eq_zero.mp hz.symm)

omit [Fact (2 ≤ d)] in
open Filter Topology in
/-- Step 5 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"the orbit (L^m V) is periodic with period q and also convergent ... hence
constant". Commutation identifies the q-step orbit with powers of one
rotation; after that rotation fixes V, the two residue classes 0 and 1
have the same limit. -/
private theorem L_fixes_directions_sides_step5_fixed_of_convergence (L : E d ≃ₗ[ℝ] E d)
    (V : Submodule ℝ (E d)) (P : E d →L[ℝ] E d)
    (hlim : Tendsto (fun n : ℕ => (V.map (L ^ n).toLinearMap).starProjection)
      atTop (𝓝 P)) (q : ℕ) (hq : 1 ≤ q) (r : Ortho d)
    (hcomm : Commute L r.toLinearEquiv)
    (hreturn : V.map (L ^ q).toLinearMap = V.map r.toLinearEquiv.toLinearMap) :
    V.map L.toLinearMap = V := by
  have hiter : ∀ n : ℕ, V.map (L ^ (q * n)).toLinearMap =
      V.map (r ^ n).toLinearEquiv.toLinearMap := by
    intro n
    induction n with
    | zero =>
      change V.map (LinearMap.id) = V.map (LinearMap.id)
      rfl
    | succ n ih =>
      rw [Nat.mul_succ, pow_add, LinearEquiv.coe_toLinearMap_mul,
        Module.End.mul_eq_comp, Submodule.map_comp, hreturn]
      have heq : (V.map r.toLinearEquiv.toLinearMap).map (L ^ (q * n)).toLinearMap =
          (V.map (L ^ (q * n)).toLinearMap).map r.toLinearEquiv.toLinearMap := by
        simp only [← Submodule.map_comp, ← Module.End.mul_eq_comp,
          ← LinearEquiv.coe_toLinearMap_mul]
        rw [(hcomm.pow_left (q * n)).eq]
      rw [heq, ih, ← Submodule.map_comp]
      congr 1
      ext x
      simp [pow_succ']
  have hqn : Tendsto (fun n : ℕ => q * n) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega)
  have hlimr : Tendsto (fun n : ℕ =>
      (V.map (r ^ n).toLinearEquiv.toLinearMap).starProjection) atTop (𝓝 P) := by
    simpa only [Function.comp_def, hiter] using hlim.comp hqn
  have hr := L_fixes_directions_sides_step4_convergent_rotation r V P hlimr
  have hqfix : V.map (L ^ q).toLinearMap = V := hreturn.trans hr
  have hmult : ∀ n : ℕ, V.map (L ^ (q * n)).toLinearMap = V := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, pow_add, LinearEquiv.coe_toLinearMap_mul,
        Module.End.mul_eq_comp, Submodule.map_comp, hqfix, ih]
  have hmult_one : ∀ n : ℕ, V.map (L ^ (q * n + 1)).toLinearMap =
      V.map L.toLinearMap := by
    intro n
    rw [pow_succ', LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp,
      Submodule.map_comp, hmult]
  have hzero : V.starProjection = P := by
    have ht := hlim.comp hqn
    simp only [Function.comp_def, hmult] at ht
    exact tendsto_nhds_unique tendsto_const_nhds ht
  have hone : (V.map L.toLinearMap).starProjection = P := by
    have ht := hlim.comp ((tendsto_add_atTop_nat 1).comp hqn)
    simp only [Function.comp_def, hmult_one] at ht
    exact tendsto_nhds_unique tendsto_const_nhds ht
  exact Submodule.starProjection_inj.mp (hone.trans hzero.symm)

omit [Fact (2 ≤ d)] in
/-- Step 6 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"a scalar which is an eigenvalue of L ... hence positive". Apply
Cayley--Hamilton to a nonzero eigenfunctional on an invariant subspace;
this obtains a root of the ambient characteristic polynomial without
assuming that L is diagonalizable. -/
private theorem L_fixes_directions_sides_step6_functional_positive (L : E d ≃ₗ[ℝ] E d)
    (hpos : PositiveRealSpectrum L) (V : Submodule ℝ (E d))
    (hV : V.map L.toLinearMap = V) (ℓ : E d →ₗ[ℝ] ℝ)
    (u : E d) (hu : u ∈ V) (hℓu : ℓ u = 1)
    (a : ℝ) (ha : ∀ x ∈ V, ℓ (L x) = a * ℓ x) : 0 < a := by
  have hmap : ∀ x ∈ V, L x ∈ V := by
    intro x hx
    rw [← hV]
    exact Submodule.mem_map_of_mem hx
  have hpoly : ∀ p : Polynomial ℝ, ∀ x ∈ V,
      ℓ ((Polynomial.aeval L.toLinearMap p) x) = p.eval a * ℓ x := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      intro x hx
      simp only [map_add, LinearMap.add_apply, hp x hx, hq x hx,
        Polynomial.eval_add, add_mul]
    | monomial n c =>
      intro x hx
      have hpow : ∀ (n : ℕ) (y : E d), y ∈ V →
          ℓ ((L.toLinearMap ^ n) y) = a ^ n * ℓ y := by
        intro n
        induction n with
        | zero => intro y hy; simp
        | succ n ih =>
          intro y hy
          rw [pow_succ, Module.End.mul_apply]
          change ℓ ((L.toLinearMap ^ n) (L y)) = _
          rw [ih (L y) (hmap y hy), ha y hy, pow_succ, mul_assoc]
      simp [Polynomial.aeval_monomial, hpow n x hx, mul_assoc]
  have hroot : L.toLinearMap.charpoly.IsRoot a := by
    have h := hpoly L.toLinearMap.charpoly u hu
    simpa [LinearMap.aeval_self_charpoly, hℓu, Polynomial.IsRoot] using h.symm
  have hc : (L.toLinearMap.charpoly.map (algebraMap ℝ ℂ)).IsRoot (a : ℂ) :=
    Polynomial.IsRoot.map hroot
  exact (hpos a hc).2

omit [Fact (2 ≤ d)] in
/-- Step 7 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"L induces on the one-dimensional quotient V/W a scalar". Normalize the
defining functional on V and use invariance of its kernel W to construct
that scalar; the preceding step proves its strict positivity. -/
private theorem L_fixes_directions_sides_step7_functional_scalar (L : E d ≃ₗ[ℝ] E d)
    (hpos : PositiveRealSpectrum L) (V W : Submodule ℝ (E d))
    (hV : V.map L.toLinearMap = V) (hW : W.map L.toLinearMap = W)
    (hWV : W ≤ V) (hdim : Module.finrank ℝ V = Module.finrank ℝ W + 1)
    (ℓ : E d →ₗ[ℝ] ℝ)
    (hker : {x | x ∈ V ∧ ℓ x = 0} = (W : Set (E d))) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ V, ℓ (L x) = a * ℓ x := by
  have hex : ∃ x ∈ V, ℓ x ≠ 0 := by
    by_contra h
    push_neg at h
    have heq : V = W := le_antisymm (by
      intro x hx
      rw [← SetLike.mem_coe, ← hker]
      exact ⟨hx, h x hx⟩) hWV
    rw [heq] at hdim
    omega
  obtain ⟨x, hx, hℓx⟩ := hex
  let u := (ℓ x)⁻¹ • x
  have hu : u ∈ V := V.smul_mem _ hx
  have hℓu : ℓ u = 1 := by simp [u, hℓx]
  have hscalar : ∀ y ∈ V, ℓ (L y) = ℓ (L u) * ℓ y := by
    intro y hy
    have hz : y - ℓ y • u ∈ W := by
      rw [← SetLike.mem_coe, ← hker]
      exact ⟨V.sub_mem hy (V.smul_mem _ hu), by simp [hℓu]⟩
    have hLz : L (y - ℓ y • u) ∈ W := by
      rw [← hW]
      exact Submodule.mem_map_of_mem hz
    have hzero : ℓ (L (y - ℓ y • u)) = 0 := by
      have := hLz
      rw [← SetLike.mem_coe, ← hker] at this
      exact this.2
    simp only [map_sub, map_smul, smul_eq_mul] at hzero
    nlinarith
  exact ⟨ℓ (L u),
    L_fixes_directions_sides_step6_functional_positive L hpos V hV ℓ u hu hℓu _ hscalar,
    hscalar⟩

omit [Fact (2 ≤ d)] in
/-- Step 8 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"so the two sides of W in V are preserved". Multiplication of a defining
functional by a positive scalar preserves its nonnegative half-space,
and invertibility gives equality of images. -/
private theorem L_fixes_directions_sides_step8_side_image (L : E d ≃ₗ[ℝ] E d)
    (hpos : PositiveRealSpectrum L) (dirs : Set (Submodule ℝ (E d)))
    (hfix : ∀ V ∈ dirs, V.map L.toLinearMap = V)
    (K : Set (E d)) (hK : IsClosedSide dirs K) : L '' K = K := by
  obtain ⟨V, W, hV, hW, hWV, hdim, ℓ, hker, rfl⟩ := hK
  have hinv : ∀ U : Submodule ℝ (E d), U ∈ dirs ∨ U = ⊤ →
      U.map L.toLinearMap = U := by
    intro U hU
    rcases hU with hU | rfl
    · exact hfix U hU
    · simp
  have hV' := hinv V hV
  obtain ⟨a, ha, hscalar⟩ :=
    L_fixes_directions_sides_step7_functional_scalar L hpos V W hV' (hinv W hW)
      hWV hdim ℓ hker
  have hmem : ∀ x, L x ∈ V ↔ x ∈ V := by
    intro x
    nth_rw 1 [← hV']
    constructor
    · rintro ⟨z, hz, heq⟩
      exact L.injective heq ▸ hz
    · intro hx
      exact ⟨x, hx, rfl⟩
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hℓx⟩, rfl⟩
    exact ⟨(hmem x).2 hx, by rw [hscalar x hx]; positivity⟩
  · rintro ⟨hy, hℓy⟩
    have hx : L.symm y ∈ V := (hmem (L.symm y)).1 (by simpa using hy)
    refine ⟨L.symm y, ⟨hx, ?_⟩, L.apply_symm_apply y⟩
    have h := hscalar (L.symm y) hx
    rw [L.apply_symm_apply] at h
    rw [h] at hℓy
    exact nonneg_of_mul_nonneg_right hℓy ha

/-- P11, V4 1.16(b): every direction and every oriented side is fixed. -/
theorem L_fixes_directions_sides (F : PowerFactorisation S) :
    (∀ V ∈ S.hPi, V.map F.L.toLinearMap = V) ∧
      ∀ K : Set (E d), IsClosedSide S.hPi K → F.L '' K = K := by
  have hfix : ∀ V ∈ S.hPi, V.map F.L.toLinearMap = V := by
    intro V hV
    obtain ⟨q, hq, r, hr, hreturn⟩ :=
      L_fixes_directions_sides_step1_orbit_return F V hV
    obtain ⟨P, hlim⟩ := L_fixes_directions_sides_step2_spectral_limit F.L F.positive V
    exact L_fixes_directions_sides_step5_fixed_of_convergence F.L V P hlim q hq r
      (L_commutes F r hr) hreturn
  exact ⟨hfix, L_fixes_directions_sides_step8_side_image F.L F.positive S.hPi hfix⟩

/-- P11, V4 1.16(b): every finite union/intersection `HΠ`-cone is fixed. -/
theorem L_fixes_HPiCones (F : PowerFactorisation S) (K : Set (E d))
    (hK : HPiCone S.hPi K) : F.L '' K = K := by
  sorry

/-- P11, V4 1.16(b'): tangent cones of listed cells of compatible ground tiles
at their listed vertices are `HΠ`-cones. This includes all lower dimensions. -/
theorem tangentCone_isHPiCone (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (C : CellName S t.ty)
    (p : E d) (hp : t.Lists 0 p) (hpC : p ∈ t.cell 0 C.val) :
    HPiCone S.hPi (tangentCone (t.cell 0 C.val) p) := by
  sorry

/-- P11, V4 1.16(b'): cones of finite unions of compatible cells at a listed
anchor are `HΠ`-cones, as are full tile cones at listed vertices. -/
theorem tangentCone_tile_isHPiCone (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (p : E d) (hp : t.Lists 0 p) :
    HPiCone S.hPi (tangentCone (t.carrier 0) p) := by
  sorry

/-- P11, V4 1.16(c): the factors commute. -/
theorem RL_commute (F : PowerFactorisation S) :
    F.R.toLinearEquiv * F.L = F.L * F.R.toLinearEquiv := by
  sorry

/-- P11, V4 1.16(c): power decomposition and compatible residual rotations. -/
theorem power_cone_formula (F : PowerFactorisation S) (a r : ℕ) (hr : r < F.power) :
    S.σ ^ (a * F.power + r) = S.σ ^ r * F.R.toLinearEquiv ^ a * F.L ^ a ∧
      ∃ Q ∈ S.rotGroup, Q.toLinearEquiv =
        linearConj S.σ (r : ℤ) (F.R.toLinearEquiv ^ a) ∧
        ∀ K : Set (E d), HPiCone S.hPi K →
          (S.σ ^ (a * F.power + r)) '' K = Q '' ((S.σ ^ r) '' K) := by
  sorry

/-- P12, V4 1.17: a header is a literal tuple of cones, a type, and a vertex name. -/
structure Header (S : SubstSystem d) (s : ℕ) where
  /-- P12, V4 1.17: type of the listing native tile. -/
  ty : S.ι
  /-- P12, V4 1.17: vertex in that type's boundary complex. -/
  vertex : {e // e ∈ (S.cx ty).vertices}
  /-- P12, V4 1.17: direction cones in the tile's isometric prototype frame. -/
  cones : Fin s → Set (E d)

namespace CompatiblePatch

variable (P : CompatiblePatch S)

/-- P12, V4 1.17: all headers at one anchor, over all depths and listing tiles.
The supplied cones have already been translated from the apex to the origin. -/
def headers (p : E d) {s : ℕ} (G : Fin s → Set (E d)) : Set (Header S s) :=
  {h | ∃ (n : ℕ) (a : P.Incident p n),
    (S.σ ^ n) p ∈ (P.native n a.val).cell 0 h.vertex.val ∧
    h.ty = (P.native n a.val).ty ∧
      ∀ j, h.cones j = (P.native n a.val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ n) '' G j)}

/-- Step 1 of the V4 proof of `header_finiteness` (V4 1.17):
"acting by ±1 on each". On a real
line, fixing the norm of a vector leaves at most the two sign choices. -/
private theorem header_finiteness_step1_line (V : Submodule ℝ (E d))
    (hV : Module.finrank ℝ V = 1) (z : E d) (hz : z ∈ V) :
    {x : E d | x ∈ V ∧ ‖x‖ = ‖z‖}.Finite := by
  apply (Set.toFinite ({z, -z} : Set (E d))).subset
  rintro x ⟨hx, hn⟩
  by_cases hzero : z = 0
  · have hxzero : x = 0 := norm_eq_zero.mp (by simpa [hzero] using hn)
    simp [hzero, hxzero]
  have hz' : (⟨z, hz⟩ : V) ≠ 0 := by simpa using hzero
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨z, hz⟩ : V) hz').mp hV ⟨x, hx⟩
  have heq : c • z = x := congrArg Subtype.val hc
  have hcabs : |c| = 1 := by
    have hnorm : |c| * ‖z‖ = 1 * ‖z‖ := by
      simpa [← heq, norm_smul, Real.norm_eq_abs] using hn
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hzero) hnorm
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hcabs with hc | hc
  · simp [← heq, hc]
  · simp [← heq, hc]

/-- Step 2 of the V4 proof of `header_finiteness` (V4 1.17):
"acting by ±1 on each". An
orthogonal stabilizer of a complete flag has finite orbits on vectors. -/
private theorem header_finiteness_step2_flag_orbit
    (V : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    ∀ k ≤ d, ∀ x ∈ V k,
      {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = V i}.image
        (fun R => R x) |>.Finite := by
  intro k
  induction k with
  | zero =>
      intro hk x hx
      have hV : V 0 = ⊥ := Submodule.finrank_eq_zero.mp (hdim 0 (by omega))
      have hxzero : x = 0 := by simpa [hV] using hx
      subst x
      exact (Set.finite_singleton (0 : E d)).subset
        (by rintro _ ⟨R, hR, rfl⟩; simp)
  | succ k ih =>
      intro hk x hx
      obtain ⟨y, hy, z, hz, hsum⟩ := (V k).exists_add_mem_mem_orthogonal x
      have hle : V k ≤ V (k + 1) := hmono k (by omega)
      have hzV : z ∈ V (k + 1) := by
        have heq : z = x - y := by rw [hsum]; abel
        rw [heq]
        exact (V (k + 1)).sub_mem hx (hle hy)
      have hline : Module.finrank ℝ ((V k)ᗮ ⊓ V (k + 1) : Submodule ℝ (E d)) = 1 := by
        have hh := Submodule.finrank_add_inf_finrank_orthogonal hle
        rw [hdim k (by omega), hdim (k + 1) hk] at hh
        omega
      have hyfinite := ih (by omega) y hy
      have hzfinite := header_finiteness_step1_line ((V k)ᗮ ⊓ V (k + 1)) hline z ⟨hz, hzV⟩
      apply ((hyfinite.prod hzfinite).image (fun yz : E d × E d => yz.1 + yz.2)).subset
      rintro _ ⟨R, hR, rfl⟩
      refine ⟨(R y, R z), ⟨⟨R, hR, rfl⟩, ?_⟩, ?_⟩
      · refine ⟨⟨?_, ?_⟩, R.norm_map z⟩
        · have horth : ((V k)ᗮ).map R.toLinearEquiv.toLinearMap = (V k)ᗮ := by
            rw [Submodule.map_orthogonal_equiv, hR k (by omega)]
          rw [← horth]
          exact Submodule.mem_map_of_mem hz
        · rw [← hR (k + 1) hk]
          exact Submodule.mem_map_of_mem hzV
      · simpa [map_add] using (congrArg R hsum).symm

/-- Step 3 of the V4 proof of `header_finiteness` (V4 1.17):
"acting by ±1 on each". Values on
one basis turn the finite vector orbits into a finite orthogonal stabilizer. -/
private theorem header_finiteness_step3_flag_stabilizer
    (V : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = V i}.Finite := by
  let H := {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = V i}
  let b := stdOrthonormalBasis ℝ (E d)
  have htop : V d = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using hdim d le_rfl)
  have hpoint : ∀ i, (H.image (fun R => R (b i))).Finite := by
    intro i
    exact header_finiteness_step2_flag_orbit V hdim hmono d le_rfl (b i) (by simp [htop])
  have heval : ((fun R : Ortho d => fun i => R (b i)) '' H).Finite :=
    (Set.Finite.pi' hpoint).subset (by rintro _ ⟨R, hR, rfl⟩ i; exact ⟨R, hR, rfl⟩)
  apply Set.Finite.of_finite_image heval
  intro R hR T hT heq
  exact b.toBasis.ext_linearIsometryEquiv (fun i => congrFun heq i)

/-- Step 4 of the V4 proof of `header_finiteness` (V4 1.17):
"the orthogonal maps carrying the complete flag ... to the target form a
coset of the stabiliser". The transporter is a translate of the finite flag stabilizer. -/
private theorem header_finiteness_step4_flag_transporters
    (V W : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = W i}.Finite := by
  classical
  let T := {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = W i}
  by_cases hT : T.Nonempty
  · obtain ⟨R₀, hR₀⟩ := hT
    apply ((header_finiteness_step3_flag_stabilizer V hdim hmono).image
      (fun R => R.trans R₀)).subset
    intro R hR
    refine ⟨R.trans R₀.symm, ?_, ?_⟩
    · intro i hi
      change (V i).map (R₀.symm.toLinearEquiv.toLinearMap.comp
        R.toLinearEquiv.toLinearMap) = V i
      rw [Submodule.map_comp, hR i hi, ← hR₀ i hi, ← Submodule.map_comp]
      simp
    · apply LinearIsometryEquiv.ext
      intro x
      exact R₀.apply_symm_apply (R x)
  · exact Set.finite_empty.subset (by intro R hR; exact (hT ⟨R, hR⟩).elim)

/-- Step 5 of the V4 proof of `header_finiteness` (V4 1.17):
"for fixed r ... and fixed target flag". A finite catalogue for each
component gives only finitely many orthogonal transporters of a complete flag. -/
private theorem header_finiteness_step5_catalogue_transporters
    (C : Set (Submodule ℝ (E d))) (hC : C.Finite)
    (V : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap ∈ C}.Finite := by
  classical
  letI : Finite C := hC
  let W (f : Fin (d + 1) → C) (i : ℕ) : Submodule ℝ (E d) :=
    if hi : i ≤ d then (f ⟨i, by omega⟩).val else ⊤
  have hf := Set.finite_iUnion fun f : Fin (d + 1) → C =>
    header_finiteness_step4_flag_transporters V (W f) hdim hmono
  apply hf.subset
  intro R hR
  let f : Fin (d + 1) → C := fun i =>
    ⟨(V i.val).map R.toLinearEquiv.toLinearMap, hR i.val (by omega)⟩
  apply Set.mem_iUnion.mpr
  refine ⟨f, ?_⟩
  intro i hi
  simp [W, hi, f]

/-- Step 6 of the V4 proof of `header_finiteness` (V4 1.17):
"the finite set of native flags". All their component directions come
from the finite prototype cell catalogue, with the ambient space adjoined. -/
private theorem header_finiteness_step6_directions :
    (S.cellDirections ∪ {⊤}).Finite := by
  have hf : (⋃ A : S.ι, (fun e : Cell d => cellDirection e.carrier) ''
      ((S.cx A).cells : Set (Cell d))).Finite :=
    Set.finite_iUnion fun A : S.ι =>
      (S.cx A).cells.finite_toSet.image (fun e : Cell d => cellDirection e.carrier)
  apply (hf.union (Set.finite_singleton ⊤)).subset
  rintro V (⟨A, e, he, rfl⟩ | hV)
  · exact Or.inl (Set.mem_iUnion.mpr ⟨A, ⟨e, he, rfl⟩⟩)
  · exact Or.inr hV

/-- Step 7 of the V4 proof of `header_finiteness` (V4 1.17):
"by 1.16(c)" applies to flag components as well as cones. A single
allowed subspace is an `HΠ`-cone, including the full ambient space. -/
private theorem header_finiteness_step7_subspace_cone
    (V : Submodule ℝ (E d)) (hV : V ∈ S.hPi ∨ V = ⊤) :
    HPiCone S.hPi (V : Set (E d)) := by
  classical
  refine ⟨{{(V : Set (E d))}}, by simp, ?_⟩
  intro p hp C hC
  simp only [Finset.mem_singleton] at hp
  subst p
  simp only [Finset.mem_singleton] at hC
  subst C
  exact Or.inl ⟨V, hV, rfl⟩

/-- Step 8 of the V4 proof of `header_finiteness` (V4 1.17):
"direction spaces ... in HΠ". The permutation of direction orbits in
1.10(c) also gives invariance under inverse powers of the expansion. -/
private theorem header_finiteness_step8_inverse_directions
    (n : ℕ) (V : Submodule ℝ (E d)) (hV : V ∈ S.hPi) :
    V.map ((S.σ ^ n)⁻¹).toLinearMap ∈ S.hPi := by
  have hone (V : Submodule ℝ (E d)) (hV : V ∈ S.hPi) :
      V.map S.σ.symm.toLinearMap ∈ S.hPi := by
    obtain ⟨_, _, p, hp⟩ := S.orbits_finite
    obtain ⟨U, hU, hVU⟩ := hV
    let O : S.directionOrbits := ⟨S.directionOrbit U, U, hU, rfl⟩
    have hm : V ∈ (p (p.symm O)).val := by simpa using hVU
    rw [hp] at hm
    obtain ⟨W, hW, rfl⟩ := hm
    have hW' : W ∈ S.hPi := by
      obtain ⟨U', hU', hO⟩ := (p.symm O).property
      exact ⟨U', hU', hO ▸ hW⟩
    simpa [← Submodule.map_comp] using hW'
  induction n with
  | zero => simpa using hV
  | succ n ih =>
    have hh := hone _ ih
    simpa only [pow_succ, mul_inv_rev, LinearEquiv.coe_toLinearMap_mul,
      Module.End.mul_eq_comp, Submodule.map_comp] using hh

/-- Step 9 of the V4 proof of `header_finiteness` (V4 1.17):
"Put D_m := B_t⁻¹ R_m ... D_m takes finitely many values". The same
residual rotation acts on the complete flag and every cone in the tuple. -/
private theorem header_finiteness_step9_residual_rotations
    (F : PowerFactorisation S) (N : ℕ) (B : ℕ → Ortho d)
    (V : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1))
    (hV : ∀ i ≤ d, V i ∈ S.hPi ∨ V i = ⊤)
    (hframe : ∀ m i, i ≤ d →
      ((V i).map (S.σ ^ (N + m)).toLinearMap).map
        (B m).symm.toLinearEquiv.toLinearMap ∈ S.cellDirections ∪ {⊤})
    {s : ℕ} (G : Fin s → Set (E d)) (hG : ∀ j, HPiCone S.hPi (G j)) :
    (Set.range (fun m => fun j => (B m).symm '' ((S.σ ^ (N + m)) '' G j))).Finite := by
  classical
  let C := S.cellDirections ∪ {⊤}
  let T (r : Fin F.power) : Set (Ortho d) :=
    {R | ∀ i ≤ d, ((V i).map (S.σ ^ r.val).toLinearMap).map
      R.toLinearEquiv.toLinearMap ∈ C}
  have hT (r : Fin F.power) : (T r).Finite := by
    apply header_finiteness_step5_catalogue_transporters C
      header_finiteness_step6_directions
      (fun i => (V i).map (S.σ ^ r.val).toLinearMap)
    · intro i hi
      rw [LinearEquiv.finrank_map_eq]
      exact hdim i hi
    · intro i hi
      exact Submodule.map_mono (hmono i hi)
  have hf : (⋃ r : Fin F.power,
      (T r).image (fun R : Ortho d => fun j : Fin s => R '' ((S.σ ^ r.val) '' G j))).Finite :=
    Set.finite_iUnion fun r : Fin F.power =>
      (hT r).image (fun R : Ortho d => fun j : Fin s => R '' ((S.σ ^ r.val) '' G j))
  apply hf.subset
  rintro _ ⟨m, rfl⟩
  let r : Fin F.power := ⟨(N + m) % F.power, Nat.mod_lt _ (by have := F.power_pos; omega)⟩
  let a := (N + m) / F.power
  have hn : a * F.power + r.val = N + m := by
    simpa [a, r, Nat.mul_comm] using Nat.div_add_mod (N + m) F.power
  obtain ⟨Q, hQ, _, hformula⟩ := (power_cone_formula F a r.val r.isLt).2
  rw [hn] at hformula
  let D := Q.trans (B m).symm
  refine Set.mem_iUnion.mpr ⟨r, ?_⟩
  refine ⟨D, ?_, ?_⟩
  · intro i hi
    have hm : (V i).map (S.σ ^ (N + m)).toLinearMap =
        ((V i).map (S.σ ^ r.val).toLinearMap).map Q.toLinearEquiv.toLinearMap := by
      apply SetLike.coe_injective
      exact hformula (V i) (header_finiteness_step7_subspace_cone (V i) (hV i hi))
    change (((V i).map (S.σ ^ r.val).toLinearMap).map
      ((B m).symm.toLinearEquiv.toLinearMap.comp Q.toLinearEquiv.toLinearMap)) ∈ C
    rw [Submodule.map_comp, ← hm]
    exact hframe m i hi
  · funext j
    change D '' ((S.σ ^ r.val) '' G j) =
      (B m).symm '' ((S.σ ^ (N + m)) '' G j)
    rw [hformula (G j) (hG j)]
    simp only [Set.image_image]
    rfl

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". Finitely many proper affine
subspaces have dense complement. -/
private theorem header_finiteness_step10_dense_avoid
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : Type*} [Finite ι] (L : ι → AffineSubspace ℝ V) (hL : ∀ i, L i ≠ ⊤) :
    Dense (⋂ i, ((L i : Set V)ᶜ)) := by
  apply dense_iInter_of_isOpen (fun i => (L i).closed_of_finiteDimensional.isOpen_compl)
  intro i
  rw [← interior_eq_empty_iff_dense_compl]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have ht := isOpen_interior.affineSpan_eq_top (⟨x, hx⟩ : (interior (L i : Set V)).Nonempty)
  have hle : affineSpan ℝ (interior (L i : Set V)) ≤ L i :=
    affineSpan_le.mpr interior_subset
  rw [ht] at hle
  exact hL i (top_unique hle)

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". A segment from a point
outside an affine subspace avoids that subspace if its other endpoint
avoids the affine span of the subspace and the first point. -/
private theorem header_finiteness_step10_segment_avoid
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : AffineSubspace ℝ V) (x z : V) (hx : x ∉ L)
    (hz : z ∉ affineSpan ℝ (insert x (L : Set V))) :
    Disjoint (segment ℝ x z) (L : Set V) := by
  apply Set.disjoint_left.mpr
  intro w hw hwL
  have hwline : w ∈ line[ℝ, x, z] :=
    (line[ℝ, x, z]).convex.segment_subset (left_mem_affineSpan_pair ℝ x z)
      (right_mem_affineSpan_pair ℝ x z) hw
  have hwx : w ≠ x := by rintro rfl; exact hx hwL
  have hline := affineSpan_pair_eq_of_right_mem_of_ne hwline hwx
  have hle : line[ℝ, x, w] ≤ affineSpan ℝ (insert x (L : Set V)) :=
    affineSpan_pair_le_of_mem_of_mem (mem_affineSpan ℝ (Set.mem_insert _ _))
      (mem_affineSpan ℝ (Set.mem_insert_of_mem _ hwL))
  rw [hline] at hle
  exact hz (hle (right_mem_affineSpan_pair ℝ x z))

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". Removing finitely many
affine subspaces of codimension at least two does not disconnect an
open convex set: two segments through a generic intermediate point suffice. -/
private theorem header_finiteness_step10_avoid_connected
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : Type*} [Finite ι] (L : ι → AffineSubspace ℝ V)
    (hL : ∀ i, Module.finrank ℝ (L i).direction + 1 < Module.finrank ℝ V)
    (U : Set V) (hU : IsOpen U) (hc : Convex ℝ U) :
    IsPreconnected (U ∩ ⋂ i, (L i : Set V)ᶜ) := by
  apply isPreconnected_of_forall_pair
  rintro x ⟨hxU, hx⟩ y ⟨hyU, hy⟩
  let M : Bool × ι → AffineSubspace ℝ V := fun b =>
    affineSpan ℝ (insert (if b.1 then x else y) (L b.2 : Set V))
  have hM (b : Bool × ι) : M b ≠ ⊤ := by
    intro heq
    have hle := finrank_vectorSpan_insert_le (L b.2) (if b.1 then x else y)
    rw [← direction_affineSpan] at hle
    change Module.finrank ℝ (M b).direction ≤ Module.finrank ℝ (L b.2).direction + 1 at hle
    rw [heq, AffineSubspace.direction_top, finrank_top] at hle
    exact (hL b.2).not_ge hle
  obtain ⟨z, hz, hzU⟩ := (header_finiteness_step10_dense_avoid M hM).exists_mem_open hU ⟨x, hxU⟩
  have hsx : segment ℝ x z ⊆ U ∩ ⋂ i, (L i : Set V)ᶜ := by
    intro w hw
    refine ⟨hc.segment_subset hxU hzU hw, Set.mem_iInter.mpr fun i => ?_⟩
    exact Set.disjoint_left.mp (header_finiteness_step10_segment_avoid (L i) x z
      (Set.mem_iInter.mp hx i) (by simpa [M] using Set.mem_iInter.mp hz (true, i))) hw
  have hsy : segment ℝ y z ⊆ U ∩ ⋂ i, (L i : Set V)ᶜ := by
    intro w hw
    refine ⟨hc.segment_subset hyU hzU hw, Set.mem_iInter.mpr fun i => ?_⟩
    exact Set.disjoint_left.mp (header_finiteness_step10_segment_avoid (L i) y z
      (Set.mem_iInter.mp hy i) (by simpa [M] using Set.mem_iInter.mp hz (false, i))) hw
  refine ⟨segment ℝ x z ∪ segment ℝ y z, Set.union_subset hsx hsy,
    Or.inl (left_mem_segment ℝ x z), Or.inr (left_mem_segment ℝ y z), ?_⟩
  exact (convex_segment (𝕜 := ℝ) x z).isPreconnected.union z
    (right_mem_segment ℝ x z) (right_mem_segment ℝ y z)
    (convex_segment (𝕜 := ℝ) y z).isPreconnected


/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". A boundary of a regular
closed set cannot locally lie in finitely many affine subspaces of
codimension at least two: the complement connects the inside to the outside. -/
private theorem header_finiteness_step10_boundary_not_thin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : Set V) (hK : IsClosed K) (hreg : closure (interior K) = K)
    (p : V) (hp : p ∈ frontier K)
    {ι : Type*} [Finite ι] (L : ι → AffineSubspace ℝ V)
    (hL : ∀ i, Module.finrank ℝ (L i).direction + 1 < Module.finrank ℝ V)
    (r : ℝ) (hr : 0 < r) :
    ¬ frontier K ∩ ball p r ⊆ ⋃ i, (L i : Set V) := by
  intro hcover
  have hproper (i : ι) : L i ≠ ⊤ := by
    intro heq
    have h := hL i
    rw [heq, AffineSubspace.direction_top, finrank_top] at h
    omega
  have hdense := header_finiteness_step10_dense_avoid L hproper
  have hxcl : p ∈ closure (interior K) := by
    rw [hreg]
    exact hK.frontier_subset hp
  have hycl : p ∈ closure Kᶜ := by
    rw [frontier_eq_closure_inter_closure] at hp
    exact hp.2
  obtain ⟨x, hx, hxU, hxK⟩ := hdense.exists_mem_open (isOpen_ball.inter isOpen_interior)
    (mem_closure_iff.mp hxcl (ball p r) isOpen_ball (mem_ball_self hr))
  obtain ⟨y, hy, hyU, hyK⟩ := hdense.exists_mem_open (isOpen_ball.inter hK.isOpen_compl)
    (mem_closure_iff.mp hycl (ball p r) isOpen_ball (mem_ball_self hr))
  have hsides : ball p r ∩ ⋂ i, (L i : Set V)ᶜ ⊆ interior K ∪ Kᶜ := by
    rintro z ⟨hzU, hz⟩
    by_cases hzK : z ∈ K
    · left
      by_contra hzi
      have hzf : z ∈ frontier K := by rw [hK.frontier_eq]; exact ⟨hzK, hzi⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ⟨hzf, hzU⟩)
      exact Set.mem_iInter.mp hz i hi
    · exact Or.inr hzK
  have hd : Disjoint (interior K) Kᶜ :=
    Set.disjoint_left.mpr fun z hz hzc => hzc (interior_subset hz)
  rcases (header_finiteness_step10_avoid_connected L hL (ball p r)
      isOpen_ball (convex_ball p r)).subset_or_subset isOpen_interior hK.isOpen_compl hd hsides with h | h
  · exact hyK (interior_subset (h ⟨hyU, hy⟩))
  · exact h ⟨hxU, hx⟩ (interior_subset hxK)

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". In a finite closed covering
of a regular boundary by lower-dimensional pieces, the pieces of
codimension one already cover the whole boundary. -/
private theorem header_finiteness_step10_boundary_facets
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : Set V) (hK : IsClosed K) (hreg : closure (interior K) = K)
    {ι : Type*} [Finite ι] (C : ι → Set V) (hC : ∀ i, IsClosed (C i))
    (hcover : frontier K ⊆ ⋃ i, C i)
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (C i)).direction < Module.finrank ℝ V)
    (p : V) (hp : p ∈ frontier K) :
    ∃ i, p ∈ C i ∧ Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 = Module.finrank ℝ V := by
  classical
  by_contra hn
  let J := {i : ι // Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 = Module.finrank ℝ V}
  let H : Set V := ⋃ i : J, C i.val
  have hH : IsClosed H := isClosed_iUnion_of_finite fun i : J => hC i.val
  have hpH : p ∈ Hᶜ := by
    intro hpH
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpH
    exact hn ⟨i.val, hi, i.property⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hH.isOpen_compl p hpH
  let I := {i : ι // Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 ≠ Module.finrank ℝ V}
  have hlow (i : I) : Module.finrank ℝ (affineSpan ℝ (C i.val)).direction + 1 < Module.finrank ℝ V := by
    have := hdim i.val
    have := i.property
    omega
  apply header_finiteness_step10_boundary_not_thin K hK hreg p hp
    (fun i : I => affineSpan ℝ (C i.val)) hlow r hr
  rintro x ⟨hxK, hxball⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hxK)
  have hiI : Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 ≠ Module.finrank ℝ V := by
    intro heq
    exact hball hxball (Set.mem_iUnion.mpr ⟨⟨i, heq⟩, hi⟩)
  exact Set.mem_iUnion.mpr ⟨⟨i, hiI⟩, mem_affineSpan ℝ hi⟩


/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"facets of that cell". A set with nonempty intrinsic interior but empty
ambient interior has strictly smaller affine dimension than the ambient space. -/
private theorem header_finiteness_step10_rank_lt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (C : Set V) (hi : (intrinsicInterior ℝ C).Nonempty) (he : interior C = ∅) :
    Module.finrank ℝ (affineSpan ℝ C).direction < Module.finrank ℝ V := by
  by_contra hn
  have hdir : (affineSpan ℝ C).direction = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by omega))
  have hne : (affineSpan ℝ C : Set V).Nonempty :=
    (hi.mono intrinsicInterior_subset).mono (subset_affineSpan ℝ C)
  have hs : affineSpan ℝ C = ⊤ := (AffineSubspace.direction_eq_top_iff_of_nonempty hne).mp hdir
  rw [intrinsicInterior, hs] at hi
  have hopen : IsOpenMap ((↑) : (⊤ : AffineSubspace ℝ V) → V) :=
    (show IsOpen ((⊤ : AffineSubspace ℝ V) : Set V) from isOpen_univ).isOpenMap_subtype_val
  have hsub := (hopen.image_interior_subset (((↑) : (⊤ : AffineSubspace ℝ V) → V) ⁻¹' C)).trans
    (interior_mono (Set.image_preimage_subset _ _))
  have hh := hi.mono hsub
  simpa [he] using hh

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"∂A is covered by its facets". Apply the boundary covering lemma to the
finite listed prototype cells. -/
private theorem header_finiteness_step10_prototype_facets
    (A : PolyManifoldDomain d) (K : CellComplex A) (p : E d)
    (hp : p ∈ frontier A.carrier) :
    ∃ e ∈ K.cells, e.dim = d - 1 ∧ p ∈ e.carrier := by
  obtain ⟨e, he, hdim⟩ := header_finiteness_step10_boundary_facets A.carrier
    A.compact.isClosed A.regularClosed (fun e : {e // e ∈ K.cells} => e.val.carrier)
    (fun e => e.val.flat.compact.isClosed) (by
      intro x hx
      rw [← K.carriers_cover] at hx
      obtain ⟨e, he, hx⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hx
      exact Set.mem_iUnion.mpr ⟨⟨e, he⟩, hx⟩)
    (fun e => by
      change Module.finrank ℝ (cellDirection e.val.carrier) < Module.finrank ℝ (E d)
      rw [e.val.flat.dimension]
      simpa using K.dim_lt e.val e.property) p hp
  refine ⟨e.val, e.property, ?_, he⟩
  change Module.finrank ℝ (cellDirection e.val.carrier) + 1 = Module.finrank ℝ (E d) at hdim
  rw [e.val.flat.dimension] at hdim
  have hh : e.val.dim + 1 = d := by simpa using hdim
  omega

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"the relative boundary of each cell is covered by the facets of that
cell". Work in its direction space, using an affine isometry from that
space onto its affine hull. -/
private theorem header_finiteness_step10_cell_facets
    (A : PolyManifoldDomain d) (K : CellComplex A)
    (e : Cell d) (he : e ∈ K.cells) (p : E d) (hp : p ∈ relfrontier e.carrier) :
    ∃ f ∈ K.cells, f.dim + 1 = e.dim ∧ p ∈ f.carrier ∧ f.carrier ⊆ e.carrier := by
  classical
  let H := affineSpan ℝ e.carrier
  have hpe : p ∈ e.carrier := intrinsicFrontier_subset e.flat.compact.isClosed hp
  let q : H := ⟨p, mem_affineSpan ℝ hpe⟩
  letI : Nonempty H := ⟨q⟩
  let ψ : H.direction ≃ᵃⁱ[ℝ] H := AffineIsometryEquiv.vaddConst ℝ q
  let φ : H.direction →ᵃⁱ[ℝ] E d := H.subtypeₐᵢ.comp ψ.toAffineIsometry
  let C : Set H.direction := φ ⁻¹' e.carrier
  have himage (D : Set (E d)) (hD : D ⊆ H) : φ '' (φ ⁻¹' D) = D := by
    apply Set.image_preimage_eq_of_subset
    intro x hx
    exact ⟨ψ.symm ⟨x, hD hx⟩, by
      change (ψ (ψ.symm ⟨x, hD hx⟩) : E d) = x
      rw [ψ.apply_symm_apply]⟩
  have heH : e.carrier ⊆ H := subset_affineSpan ℝ e.carrier
  have hCimage : φ '' C = e.carrier := himage _ heH
  have hinter : φ '' interior C = relint e.carrier := by
    change (((↑) : H → E d) ∘ ψ.toHomeomorph) '' interior (ψ.toHomeomorph ⁻¹' (((↑) : H → E d) ⁻¹' e.carrier)) = _
    rw [Set.image_comp, ψ.toHomeomorph.image_interior, ψ.toHomeomorph.image_preimage]
    rfl
  have hfront : φ '' frontier C = relfrontier e.carrier := by
    change (((↑) : H → E d) ∘ ψ.toHomeomorph) '' frontier (ψ.toHomeomorph ⁻¹' (((↑) : H → E d) ⁻¹' e.carrier)) = _
    rw [Set.image_comp, ψ.toHomeomorph.image_frontier, ψ.toHomeomorph.image_preimage]
    rfl
  have hCclosed : IsClosed C := e.flat.compact.isClosed.preimage φ.continuous
  have hCreg : closure (interior C) = C := by
    apply φ.injective.image_injective
    rw [← φ.isometry.isClosedEmbedding.closure_image_eq, hinter, e.flat.regularClosed, hCimage]
  obtain ⟨b, hb, hboundary⟩ := K.boundary_union e he
  have hbsub (f : {f // f ∈ b}) : f.val.carrier ⊆ relfrontier e.carrier := by
    intro x hx
    rw [hboundary]
    exact Set.mem_iUnion.mpr ⟨f.val, Set.mem_iUnion.mpr ⟨f.property, hx⟩⟩
  have hbH (f : {f // f ∈ b}) : f.val.carrier ⊆ H :=
    (hbsub f).trans ((intrinsicFrontier_subset e.flat.compact.isClosed).trans heH)
  let D (f : {f // f ∈ b}) : Set H.direction := φ ⁻¹' f.val.carrier
  have hDfront (f : {f // f ∈ b}) : D f ⊆ frontier C := by
    intro x hx
    have hh := hbsub f hx
    rw [← hfront] at hh
    exact φ.injective.mem_set_image.mp hh
  have hDdim (f : {f // f ∈ b}) :
      Module.finrank ℝ (affineSpan ℝ (D f)).direction = f.val.dim := by
    have heq : (affineSpan ℝ f.val.carrier).direction =
        ((affineSpan ℝ (D f)).direction).map H.direction.subtype := by
      rw [← himage f.val.carrier (hbH f)]
      change (affineSpan ℝ (φ.toAffineMap '' D f)).direction = _
      rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
      rfl
    have hh := f.val.flat.dimension
    change Module.finrank ℝ (affineSpan ℝ f.val.carrier).direction = f.val.dim at hh
    rw [heq, Submodule.finrank_map_subtype_eq] at hh
    exact hh
  have hDlow (f : {f // f ∈ b}) :
      Module.finrank ℝ (affineSpan ℝ (D f)).direction < Module.finrank ℝ H.direction := by
    apply header_finiteness_step10_rank_lt
    · have hh := f.val.flat.relint_nonempty
      change (intrinsicInterior ℝ f.val.carrier).Nonempty at hh
      rw [← himage f.val.carrier (hbH f), φ.image_intrinsicInterior, Set.image_nonempty] at hh
      exact hh
    · apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hh := interior_mono (hDfront f) hx
      simpa [interior_frontier hCclosed] using hh
  have hpC : ψ.symm q ∈ frontier C := by
    apply φ.injective.mem_set_image.mp
    rw [hfront]
    simpa [φ] using hp
  obtain ⟨f, hpf, hfdim⟩ := header_finiteness_step10_boundary_facets C hCclosed hCreg D
    (fun f => f.val.flat.compact.isClosed.preimage φ.continuous) (by
      intro x hx
      have hh : φ x ∈ relfrontier e.carrier := hfront ▸ Set.mem_image_of_mem φ hx
      rw [hboundary] at hh
      obtain ⟨f, hf, hxf⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hh
      exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hxf⟩) hDlow (ψ.symm q) hpC
  refine ⟨f.val, hb f.property, ?_, ?_,
    (hbsub f).trans (intrinsicFrontier_subset e.flat.compact.isClosed)⟩
  · rw [hDdim] at hfdim
    exact hfdim.trans e.flat.dimension
  · change φ (ψ.symm q) ∈ f.val.carrier at hpf
    simpa [φ] using hpf


/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"each still containing the vertex". A listed vertex in a positive-dimensional
listed cell lies in that cell's relative boundary, since listed relative
interiors are disjoint. -/
private theorem header_finiteness_step10_vertex_boundary
    (A : PolyManifoldDomain d) (K : CellComplex A)
    (v : Cell d) (hv : v ∈ K.vertices) (p : E d) (hp : p ∈ v.carrier)
    (e : Cell d) (he : e ∈ K.cells) (hpe : p ∈ e.carrier) (hdim : 0 < e.dim) :
    p ∈ relfrontier e.carrier := by
  have hvdim : v.dim = 0 := (Finset.mem_filter.mp hv).2
  have hvK : v ∈ K.cells := (Finset.mem_filter.mp hv).1
  have hbot : cellDirection v.carrier = ⊥ :=
    Submodule.finrank_eq_zero.mp (v.flat.dimension.trans hvdim)
  have hsingle : v.carrier.Subsingleton := by
    apply (vectorSpan_eq_bot_iff_subsingleton ℝ).mp
    simpa only [cellDirection, direction_affineSpan] using hbot
  have hvp : v.carrier = {p} := hsingle.eq_singleton_of_mem hp
  have hpv : p ∈ relint v.carrier := by simp [relint, hvp]
  have hne : v ≠ e := by
    intro h
    have := h ▸ hvdim
    omega
  have hnot : p ∉ relint e.carrier := fun hh =>
    Set.disjoint_left.mp (K.relint_disjoint v hvK e he hne) hpv hh
  change p ∈ intrinsicFrontier ℝ e.carrier
  rw [← closure_diff_intrinsicInterior, e.flat.compact.isClosed.closure_eq]
  exact ⟨hpe, hnot⟩

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15, used in 1.17):
"starting from a facet through the vertex one descends through incident
facets of facets". Reversing this descending sequence gives the complete
nested flag at the original listed vertex. -/
private theorem header_finiteness_step10_prototype_flag
    (A : PolyManifoldDomain d) (K : CellComplex A)
    (v : Cell d) (hv : v ∈ K.vertices) (p : E d) (hp : p ∈ v.carrier) :
    ∃ f : CellFlag K, ∀ j, p ∈ (f.cell j).carrier := by
  classical
  have hpA : p ∈ frontier A.carrier := by
    rw [← K.carriers_cover]
    exact Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨(Finset.mem_filter.mp hv).1, hp⟩⟩
  obtain ⟨e, he, hdim, hpe⟩ := header_finiteness_step10_prototype_facets A K p hpA
  let I := {e : Cell d // e ∈ K.cells ∧ p ∈ e.carrier}
  have hnext (e : I) (h : 0 < e.val.dim) :
      ∃ f : I, f.val.dim + 1 = e.val.dim ∧ f.val.carrier ⊆ e.val.carrier := by
    obtain ⟨f, hf, hfdim, hpf, hsub⟩ := header_finiteness_step10_cell_facets A K e.val e.property.1 p
      (header_finiteness_step10_vertex_boundary A K v hv p hp e.val e.property.1 e.property.2 h)
    exact ⟨⟨f, hf, hpf⟩, hfdim, hsub⟩
  let next (e : I) : I := if h : 0 < e.val.dim then (hnext e h).choose else e
  have next_dim (e : I) : (next e).val.dim = e.val.dim - 1 := by
    by_cases h : 0 < e.val.dim
    · have hh := (hnext e h).choose_spec.1
      simp only [next, dif_pos h]
      omega
    · have hh : e.val.dim = 0 := by omega
      simp [next, h, hh]
  have next_sub (e : I) : (next e).val.carrier ⊆ e.val.carrier := by
    by_cases h : 0 < e.val.dim
    · simpa only [next, dif_pos h] using (hnext e h).choose_spec.2
    · simp [next, h]
  let c (n : ℕ) : I := next^[n] ⟨e, he, hpe⟩
  have c_succ (n : ℕ) : c (n + 1) = next (c n) := Function.iterate_succ_apply' next n _
  have c_dim (n : ℕ) : (c n).val.dim = d - 1 - n := by
    induction n with
    | zero => simpa [c] using hdim
    | succ n ih => rw [c_succ, next_dim, ih]; omega
  have c_anti : Antitone (fun n => (c n).val.carrier) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [c_succ]
    exact next_sub (c n)
  let f : CellFlag K :=
    { cell := fun j => (c (d - 1 - j.val)).val
      mem := fun j => (c (d - 1 - j.val)).property.1
      dimension := fun j => by rw [c_dim]; omega
      nested := fun i j hij => c_anti (by have := i.isLt; have := j.isLt; omega) }
  exact ⟨f, fun j => (c (d - 1 - j.val)).property.2⟩

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15, used in 1.17):
"the boundary complex of a polyhedral manifold has a full flag at every
vertex". This is only the initial flag, before any substitution is applied. -/
private theorem header_finiteness_step10_vertex_flag
    (t : FramedNode S) (p : E d) (hp : t.Lists 0 p) :
    ∃ f : CellFlag (S.cx t.ty), ∀ j, p ∈ t.cell 0 (f.cell j) := by
  obtain ⟨v, hv, x, hx, hxp⟩ := hp
  obtain ⟨f, hf⟩ := header_finiteness_step10_prototype_flag (S.proto t.ty) (S.cx t.ty) v hv x hx
  exact ⟨f, fun j => ⟨x, hf j, hxp⟩⟩


/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". Conjugated frames intertwine successive expansions. -/
private theorem header_finiteness_step11_conjugate_succ
    (R : E d ≃ₗ[ℝ] E d) (n : ℕ) (x : E d) :
    linearConj S.σ ((n + 1 : ℕ) : ℤ) R (S.σ x) =
      S.σ (linearConj S.σ (n : ℤ) R x) := by
  have heq : linearConj S.σ ((n + 1 : ℕ) : ℤ) R * S.σ =
      S.σ * linearConj S.σ (n : ℤ) R := by
    simp only [linearConj, Nat.cast_add, Nat.cast_one]
    group
  exact congrArg (fun L : E d ≃ₗ[ℝ] E d => L x) heq

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". The prescribed role frame has the same covariance. -/
private theorem header_finiteness_step11_placeChild_succ
    {A : S.ι} (i : S.I A) (n : ℕ) (x : E d) :
    S.placeChild (n + 1) i (S.σ x) = S.σ (S.placeChild n i x) := by
  rw [S.placeChild_apply, S.placeChild_apply,
    header_finiteness_step11_conjugate_succ, map_add, pow_succ']
  rfl

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". At height zero the role frame is the prescribed child frame. -/
private theorem header_finiteness_step11_placeChild_zero
    {A : S.ι} (i : S.I A) : S.placeChild 0 i = (S.child A i).frame := by
  apply AffineIsometryEquiv.ext
  intro x
  change linearConj S.σ (0 : ℤ) (S.child A i).rotation.toLinearEquiv x +
      (S.σ ^ 0) (S.child A i).offset =
    (S.child A i).rotation x + (S.child A i).offset
  simp [linearConj]

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". Append a child role to a native address,
leaving its original patch root fixed. -/
private def header_finiteness_step11_append (S : SubstSystem d) :
    (A : S.ι) → (n : ℕ) → (w : S.RoleWord A n) →
      S.I (S.nativeTile A n w).ty → S.RoleWord A (n + 1)
  | A, 0, _, i => ⟨i, ()⟩
  | A, n + 1, w, i => ⟨w.1,
      header_finiteness_step11_append S (S.child A w.1).ty n w.2 i⟩

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the child t_{n+1}". Appending a role retains its prescribed child type. -/
private theorem header_finiteness_step11_append_type
    (A : S.ι) (n : ℕ) (w : S.RoleWord A n) (i : S.I (S.nativeTile A n w).ty) :
    (S.nativeTile A (n + 1) (header_finiteness_step11_append S A n w i)).ty =
      (S.child (S.nativeTile A n w).ty i).ty := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih => exact ih (S.child A w.1).ty w.2 i

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". Appending a role realizes subdivision after
inflation, even though the native-address recursion reads roles from the root. -/
private theorem header_finiteness_step11_append_frame
    (A : S.ι) (n : ℕ) (w : S.RoleWord A n) (i : S.I (S.nativeTile A n w).ty)
    (x : E d) :
    (S.nativeTile A (n + 1) (header_finiteness_step11_append S A n w i)).frame x =
      S.σ ((S.nativeTile A n w).frame (S.σ.symm ((S.child (S.nativeTile A n w).ty i).frame x))) := by
  induction n generalizing A with
  | zero =>
    change S.placeChild 0 i x = S.σ (S.σ.symm ((S.child A i).frame x))
    rw [S.σ.apply_symm_apply, header_finiteness_step11_placeChild_zero]
    rfl
  | succ n ih =>
    change S.placeChild (0 + (n + 1)) w.1
      ((S.nativeTile (S.child A w.1).ty (n + 1)
        (header_finiteness_step11_append S (S.child A w.1).ty n w.2 i)).frame x) =
      S.σ (S.placeChild (0 + n) w.1 ((S.nativeTile (S.child A w.1).ty n w.2).frame
        (S.σ.symm ((S.child (S.nativeTile (S.child A w.1).ty n w.2).ty i).frame x))))
    simp only [Nat.zero_add]
    rw [ih, header_finiteness_step11_placeChild_succ]

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". The patch's specified ground frame obeys the
same covariance as a substitution role frame. -/
private theorem header_finiteness_step11_inflated_frame_succ
    (t : FramedNode S) (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup)
    (n : ℕ) (x : E d) :
    compatibleInflatedFrame t ht (n + 1) (S.σ x) =
      S.σ (compatibleInflatedFrame t ht n x) := by
  have hQ (n : ℕ) (x : E d) :
      (Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
        t.frame.linearIsometryEquiv ht)) x =
      linearConj S.σ (n : ℤ) t.frame.linearIsometryEquiv.toLinearEquiv x :=
    congrArg (fun L : E d ≃ₗ[ℝ] E d => L x)
      (Classical.choose_spec (S.rotGroup_conj_zpow (n : ℤ)
        t.frame.linearIsometryEquiv ht)).2
  change (Classical.choose (S.rotGroup_conj_zpow ((n + 1 : ℕ) : ℤ)
      t.frame.linearIsometryEquiv ht)) (S.σ x) + (S.σ ^ (n + 1)) (t.frame 0) =
    S.σ ((Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
      t.frame.linearIsometryEquiv ht)) x + (S.σ ^ n) (t.frame 0))
  rw [hQ, hQ, header_finiteness_step11_conjugate_succ, map_add, pow_succ']
  rfl

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". The appended address uses exactly the actual
frame of the inflated patch tile followed by the prescribed child frame. -/
private theorem header_finiteness_step11_native_child
    (P : CompatiblePatch S) (n : ℕ) (a : P.Address n) (i : S.I (P.native n a).ty) :
    ∃ b : P.Address (n + 1),
      (P.native (n + 1) b).ty = (S.child (P.native n a).ty i).ty ∧
      ∀ x, (P.native (n + 1) b).frame x =
        S.σ ((P.native n a).frame (S.σ.symm ((S.child (P.native n a).ty i).frame x))) := by
  refine ⟨⟨a.1, header_finiteness_step11_append S a.1.val.ty n a.2 i⟩,
    header_finiteness_step11_append_type a.1.val.ty n a.2 i, ?_⟩
  intro x
  change compatibleInflatedFrame a.1.val (P.compatible _ a.1.property) (n + 1)
    ((S.nativeTile a.1.val.ty (n + 1)
      (header_finiteness_step11_append S a.1.val.ty n a.2 i)).frame x) = _
  rw [header_finiteness_step11_append_frame, header_finiteness_step11_inflated_frame_succ]
  rfl


/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"cells of t_n". A ground cell is placed directly by its tile frame. -/
private theorem header_finiteness_step11_cell_zero (t : FramedNode S) (e : Cell d) :
    t.cell 0 e = t.frame '' e.carrier := rfl

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"cells of t_n". The ground carrier is the isometric prototype carrier. -/
private theorem header_finiteness_step11_carrier_zero (t : FramedNode S) :
    t.carrier 0 = t.frame '' (S.proto t.ty).carrier := by
  simp [FramedNode.carrier, placedSet, SubstSystem.supertile]

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"cells of t_n". A listed cell is contained in its closed tile carrier. -/
private theorem header_finiteness_step11_cell_subset (t : FramedNode S)
    (e : Cell d) (he : e ∈ (S.cx t.ty).cells) : t.cell 0 e ⊆ t.carrier 0 := by
  rw [header_finiteness_step11_cell_zero, header_finiteness_step11_carrier_zero]
  apply Set.image_mono
  intro x hx
  apply (S.proto t.ty).compact.isClosed.frontier_subset
  rw [← (S.cx t.ty).carriers_cover]
  exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he, hx⟩⟩

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"σ e is a union of placed j-cells of the children". An expanded incident
cell has an incident native child cell of the same dimension; its carrier
is contained in the expanded parent cell. No uniqueness is used in this step. -/
private theorem header_finiteness_step11_refinement
    (P : CompatiblePatch S) (p : E d) (n : ℕ) (a : P.Incident p n)
    (e : CellName S (P.native n a.val).ty)
    (he : (S.σ ^ n) p ∈ (P.native n a.val).cell 0 e.val) :
    ∃ (b : P.Incident p (n + 1)) (f : CellName S (P.native (n + 1) b.val).ty),
      P.IncidentChild p n a b ∧ f.val.dim = e.val.dim ∧
      (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b.val).cell 0 f.val ∧
      (P.native (n + 1) b.val).cell 0 f.val ⊆
        S.σ '' (P.native n a.val).cell 0 e.val := by
  classical
  rw [header_finiteness_step11_cell_zero] at he
  obtain ⟨x, hxe, hxp⟩ := he
  obtain ⟨c, hc⟩ := S.heredity (P.native n a.val).ty e.val e.property
  have hsx : S.σ x ∈ ⋃ q ∈ c, placedSet (S.child (P.native n a.val).ty q.1).frame q.2.val.carrier := by
    rw [← hc]
    exact Set.mem_image_of_mem S.σ hxe
  obtain ⟨q, hq, y, hy, hyx⟩ := by
    simpa only [Set.mem_iUnion, exists_prop, placedSet, Set.mem_image] using hsx
  obtain ⟨b, hty, hframe⟩ := header_finiteness_step11_native_child P n a.val q.1
  have hmem : q.2.val ∈ (S.cx (P.native (n + 1) b).ty).cells := by
    rw [hty]
    exact q.2.property.1
  have hpoint : (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b).cell 0 q.2.val := by
    rw [header_finiteness_step11_cell_zero]
    refine ⟨y, hy, ?_⟩
    rw [hframe, hyx, S.σ.symm_apply_apply, hxp, pow_succ']
    rfl
  have hinc : (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b).carrier 0 :=
    header_finiteness_step11_cell_subset _ _ hmem hpoint
  have hsub : ∀ (K L : Set (E d)),
      (S.child (P.native n a.val).ty q.1).frame '' K ⊆ S.σ '' L →
      (P.native (n + 1) b).frame '' K ⊆ S.σ '' ((P.native n a.val).frame '' L) := by
    intro K L h z hz
    obtain ⟨u, hu, rfl⟩ := hz
    obtain ⟨v, hv, hvu⟩ := h (Set.mem_image_of_mem _ hu)
    refine ⟨(P.native n a.val).frame v, Set.mem_image_of_mem _ hv, ?_⟩
    rw [hframe, ← hvu, S.σ.symm_apply_apply]
  refine ⟨⟨b, hinc⟩, ⟨q.2.val, hmem⟩, ?_, q.2.property.2, hpoint, ?_⟩
  · change (P.native (n + 1) b).carrier 0 ⊆ S.σ '' (P.native n a.val).carrier 0
    rw [header_finiteness_step11_carrier_zero, header_finiteness_step11_carrier_zero, hty]
    apply hsub
    rw [S.children_cover]
    exact Set.subset_iUnion (fun i => placedSet (S.child (P.native n a.val).ty i).frame
      (S.proto (S.child (P.native n a.val).ty i).ty).carrier) q.1
  · rw [header_finiteness_step11_cell_zero, header_finiteness_step11_cell_zero]
    apply hsub
    rw [hc]
    intro z hz
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, hz⟩⟩

/-- Step 12 of the V4 proof of `header_finiteness` (V4 1.17):
"regarded as the tuple of its direction spaces". Taking directions of a
placed cell removes translation and retains the actual orthogonal frame. -/
private theorem header_finiteness_step12_frame_direction
    (t : FramedNode S) (e : Cell d) :
    cellDirection (t.cell 0 e) =
      (cellDirection e.carrier).map t.frame.linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  change (affineSpan ℝ (t.frame.toAffineEquiv.toAffineMap '' e.carrier)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  rfl

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"its affine hull is σ aff e by dimension". Direction spaces commute
with every invertible linear map, including the anisotropic expansion. -/
private theorem header_finiteness_step11_linear_direction
    (L : E d ≃ₗ[ℝ] E d) (K : Set (E d)) :
    cellDirection (L '' K) = (cellDirection K).map L.toLinearMap := by
  change (affineSpan ℝ (L.toAffineEquiv.toAffineMap '' K)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  rfl

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim, used in 1.17):
"some j-cell ... contains [the vertex] and lies in σ e". Heredity at a
unique incident child preserves the direction of one listed cell.
The uniqueness hypothesis excludes branching, and the cell must contain the anchor. -/
private theorem header_finiteness_step11_child_cell
    (P : CompatiblePatch S) (p : E d) (n : ℕ)
    (a : P.Incident p n) (b : P.Incident p (n + 1))
    (hab : P.IncidentChild p n a b)
    (hunique : ∀ b' : P.Incident p (n + 1), P.IncidentChild p n a b' → b' = b)
    (e : CellName S (P.native n a.val).ty)
    (he : (S.σ ^ n) p ∈ (P.native n a.val).cell 0 e.val) :
    ∃ f : CellName S (P.native (n + 1) b.val).ty,
      f.val.dim = e.val.dim ∧
      (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b.val).cell 0 f.val ∧
      cellDirection ((P.native (n + 1) b.val).cell 0 f.val) =
        (cellDirection ((P.native n a.val).cell 0 e.val)).map S.σ.toLinearMap := by
  obtain ⟨b', f, hb', hdim, hf, hsub⟩ := header_finiteness_step11_refinement P p n a e he
  obtain rfl := hunique b' hb'
  refine ⟨f, hdim, hf, ?_⟩
  have hle := AffineSubspace.direction_le (affineSpan_mono ℝ hsub)
  change cellDirection ((P.native (n + 1) b'.val).cell 0 f.val) ≤
    cellDirection (S.σ '' (P.native n a.val).cell 0 e.val) at hle
  rw [header_finiteness_step11_linear_direction] at hle
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [header_finiteness_step12_frame_direction, header_finiteness_step12_frame_direction]
  simp only [LinearEquiv.finrank_map_eq]
  exact f.val.flat.dimension.trans (hdim.trans e.val.flat.dimension.symm)


/-- Step 13 of the V4 proof of `header_finiteness` (V4 1.17):
"the Claim in the proof of 1.15 ... gives a native flag". Iterate the
single-cell transport along a nonbranching listing tail; the transported
cells need not be nested, but their direction spaces are a complete flag. -/
private theorem header_finiteness_step13_tail_flag
    (P : CompatiblePatch S) (p : E d) (N : ℕ) (t : P.IncidentTail p N)
    (hunique : ∀ m (b : P.Incident p (N + m + 1)),
      P.IncidentChild p (N + m) (t.node m) b → b = t.node (m + 1))
    (hlisted : (P.native N (t.node 0).val).Lists 0 ((S.σ ^ N) p)) :
    ∃ V : ℕ → Submodule ℝ (E d),
      (∀ i ≤ d, Module.finrank ℝ (V i) = i) ∧
      (∀ i < d, V i ≤ V (i + 1)) ∧
      (∀ i ≤ d, V i ∈ S.hPi ∨ V i = ⊤) ∧
      ∀ m i, i ≤ d →
        ((V i).map (S.σ ^ m).toLinearMap).map
          (P.native (N + m) (t.node m).val).frame.linearIsometryEquiv.symm.toLinearEquiv.toLinearMap
          ∈ S.cellDirections ∪ {⊤} := by
  classical
  obtain ⟨f, hf⟩ := header_finiteness_step10_vertex_flag _ _ hlisted
  let V (i : ℕ) : Submodule ℝ (E d) :=
    if hi : i < d then cellDirection ((P.native N (t.node 0).val).cell 0 (f.cell ⟨i, hi⟩))
    else ⊤
  have hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i := by
    intro i hi
    by_cases hid : i < d
    · rw [show V i = cellDirection ((P.native N (t.node 0).val).cell 0 (f.cell ⟨i, hid⟩))
          from dif_pos hid, header_finiteness_step12_frame_direction, LinearEquiv.finrank_map_eq]
      exact (f.cell ⟨i, hid⟩).flat.dimension.trans (f.dimension ⟨i, hid⟩)
    · have heq : i = d := by omega
      rw [show V i = ⊤ from dif_neg hid]
      simp [heq]
  have hmono : ∀ i < d, V i ≤ V (i + 1) := by
    intro i hi
    by_cases hj : i + 1 < d
    · simp only [V, dif_pos hi, dif_pos hj, header_finiteness_step12_frame_direction]
      apply Submodule.map_mono
      exact AffineSubspace.direction_le (affineSpan_mono ℝ
        (f.nested ⟨i, hi⟩ ⟨i + 1, hj⟩ (by simp)))
    · simp [V, hj]
  have hV : ∀ i ≤ d, V i ∈ S.hPi ∨ V i = ⊤ := by
    intro i hi
    by_cases hid : i < d
    · left
      refine ⟨cellDirection (f.cell ⟨i, hid⟩).carrier,
        ⟨(P.native N (t.node 0).val).ty, f.cell ⟨i, hid⟩, f.mem _, rfl⟩,
        (P.native N (t.node 0).val).frame.linearIsometryEquiv,
        P.native_compatible N (t.node 0).val, ?_⟩
      simp only [V, dif_pos hid, header_finiteness_step12_frame_direction]
    · exact Or.inr (by simp [V, hid])
  have hcell (i : ℕ) (hi : i < d) : ∀ m : ℕ,
      ∃ e : CellName S (P.native (N + m) (t.node m).val).ty,
        (S.σ ^ (N + m)) p ∈ (P.native (N + m) (t.node m).val).cell 0 e.val ∧
        cellDirection ((P.native (N + m) (t.node m).val).cell 0 e.val) =
          (V i).map (S.σ ^ m).toLinearMap := by
    intro m
    induction m with
    | zero =>
      refine ⟨⟨f.cell ⟨i, hi⟩, f.mem _⟩, hf _, ?_⟩
      simp [V, hi]
    | succ m ih =>
      obtain ⟨e, he, hdir⟩ := ih
      obtain ⟨e', _, he', hdir'⟩ := header_finiteness_step11_child_cell P p
        (N + m) (t.node m) (t.node (m + 1)) (t.step m) (hunique m) e he
      refine ⟨e', he', ?_⟩
      calc
        _ = (cellDirection ((P.native (N + m) (t.node m).val).cell 0 e.val)).map
            S.σ.toLinearMap := hdir'
        _ = _ := by
          rw [hdir, ← Submodule.map_comp]
          simp [pow_succ', LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp]
  refine ⟨V, hdim, hmono, hV, ?_⟩
  intro m i hi
  by_cases hid : i < d
  · obtain ⟨e, he, hdir⟩ := hcell i hid m
    rw [← hdir, header_finiteness_step12_frame_direction, ← Submodule.map_comp]
    simp only [LinearIsometryEquiv.toLinearEquiv_symm, LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, Submodule.map_id]
    exact Or.inl ⟨(P.native (N + m) (t.node m).val).ty, e.val, e.property, rfl⟩
  · simp [V, hid, Submodule.map_top]

/-- Step 14 of the V4 proof of `header_finiteness` (V4 1.17):
"the header ... takes finitely many values" on a listing tail. Pulling
the initial flag back by σ^N lets the power formula apply to the original
cone tuple, without assuming that the frames commute with σ. -/
private theorem header_finiteness_step14_listing_tail
    (P : CompatiblePatch S) (F : PowerFactorisation S) (p : E d)
    (N : ℕ) (t : P.IncidentTail p N)
    (hunique : ∀ m (b : P.Incident p (N + m + 1)),
      P.IncidentChild p (N + m) (t.node m) b → b = t.node (m + 1))
    (hlisted : (P.native N (t.node 0).val).Lists 0 ((S.σ ^ N) p))
    {s : ℕ} (G : Fin s → Set (E d)) (hG : ∀ j, HPiCone S.hPi (G j)) :
    (Set.range (fun m => fun j =>
      (P.native (N + m) (t.node m).val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ (N + m)) '' G j))).Finite := by
  obtain ⟨V, hdim, hmono, hV, hframe⟩ :=
    header_finiteness_step13_tail_flag P p N t hunique hlisted
  let W (i : ℕ) := (V i).map ((S.σ ^ N)⁻¹).toLinearMap
  apply header_finiteness_step9_residual_rotations F N
    (fun m => (P.native (N + m) (t.node m).val).frame.linearIsometryEquiv) W
    (fun i hi => (LinearEquiv.finrank_map_eq _ _).trans (hdim i hi))
    (fun i hi => Submodule.map_mono (hmono i hi)) ?_ ?_ G hG
  · intro i hi
    rcases hV i hi with h | h
    · exact Or.inl (header_finiteness_step8_inverse_directions N (V i) h)
    · exact Or.inr (by simp [W, h])
  · intro m i hi
    have heq : (W i).map (S.σ ^ (N + m)).toLinearMap =
        (V i).map (S.σ ^ m).toLinearMap := by
      simp only [W, ← Submodule.map_comp, ← Module.End.mul_eq_comp,
        ← LinearEquiv.coe_toLinearMap_mul]
      rw [Nat.add_comm N m, pow_add, mul_inv_cancel_right]
    rw [heq]
    exact hframe m i hi

/-- Step 15 of the V4 proof of `header_finiteness` (V4 1.17):
"beyond all branching". Starting at the unique-child cutoff, recursively
choose the unique children. Every later incident tile belongs to one of
these tails, indexed by the finite set of incident tiles at the cutoff. -/
private theorem header_finiteness_step15_tail_cover
    (P : CompatiblePatch S) [Nonempty S.ι] (p : E d) :
    ∃ (N : ℕ) (t : P.Incident p N → P.IncidentTail p N),
      (∀ m, Function.Surjective (fun a => (t a).node m)) ∧
      ∀ n, N ≤ n → ∀ a : P.Incident p n,
        ∃! b : P.Incident p (n + 1), P.IncidentChild p n a b := by
  classical
  obtain ⟨_, _, N, hN⟩ := P.incidentForest p
  let next (m : ℕ) (a : P.Incident p (N + m)) : P.Incident p (N + (m + 1)) :=
    Classical.choose (hN (N + m) (by omega) a)
  have hnext (m : ℕ) (a : P.Incident p (N + m)) :
      P.IncidentChild p (N + m) a (next m a) :=
    (Classical.choose_spec (hN (N + m) (by omega) a)).1
  let node (a : P.Incident p N) : ∀ m, P.Incident p (N + m) :=
    fun m => Nat.rec a (fun m b => next m b) m
  let t (a : P.Incident p N) : P.IncidentTail p N :=
    ⟨node a, fun m => hnext m (node a m)⟩
  refine ⟨N, t, ?_, hN⟩
  intro m
  induction m with
  | zero => exact fun a => ⟨a, rfl⟩
  | succ m ih =>
    intro b
    let a := P.incidentParent p (N + m) b
    obtain ⟨a₀, ha₀⟩ := ih a
    refine ⟨a₀, ?_⟩
    change next m (node a₀ m) = b
    change node a₀ m = a at ha₀
    rw [ha₀]
    exact ExistsUnique.unique (hN (N + m) (by omega) a)
      (hnext m a) (P.incidentParent_spec p (N + m) b)

/-- Step 16 of the V4 proof of `header_finiteness` (V4 1.17):
"a tail either never lists ... or lists it from some depth on". A tail
with no listing contributes nothing; otherwise split at a listing depth
and keep the earlier, finite prefix separately. -/
private theorem header_finiteness_step16_tail_listings
    (P : CompatiblePatch S) (F : PowerFactorisation S) (p : E d)
    (N : ℕ) (t : P.IncidentTail p N)
    (hunique : ∀ n, N ≤ n → ∀ a : P.Incident p n,
      ∃! b : P.Incident p (n + 1), P.IncidentChild p n a b)
    {s : ℕ} (G : Fin s → Set (E d)) (hG : ∀ j, HPiCone S.hPi (G j)) :
    {K | ∃ m, (P.native (N + m) (t.node m).val).Lists 0 ((S.σ ^ (N + m)) p) ∧
      K = fun j => (P.native (N + m) (t.node m).val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ (N + m)) '' G j)}.Finite := by
  classical
  let K (m : ℕ) := fun j =>
    (P.native (N + m) (t.node m).val).frame.linearIsometryEquiv.symm ''
      ((S.σ ^ (N + m)) '' G j)
  by_cases h : ∃ k, (P.native (N + k) (t.node k).val).Lists 0 ((S.σ ^ (N + k)) p)
  · obtain ⟨k, hk⟩ := h
    have hcast (n m : ℕ) (h : n = m) (a : P.Incident p m) :
        P.native n (h.symm ▸ a : P.Incident p n).val = P.native m a.val := by
      cases h
      rfl
    let t' : P.IncidentTail p (N + k) :=
      { node := fun r => (Nat.add_assoc N k r).symm ▸ t.node (k + r)
        step := fun r => by
          rw [hcast _ _ (Nat.add_assoc N k (r + 1)), hcast _ _ (Nat.add_assoc N k r)]
          simpa only [Nat.add_assoc] using t.step (k + r) }
    have hu (m : ℕ) (b : P.Incident p (N + k + m + 1))
        (hb : P.IncidentChild p (N + k + m) (t'.node m) b) : b = t'.node (m + 1) :=
      ExistsUnique.unique (hunique _ (by omega) (t'.node m)) hb (t'.step m)
    have hl : (P.native (N + k) (t'.node 0).val).Lists 0 ((S.σ ^ (N + k)) p) := by
      simpa [t'] using hk
    have hf : (Set.range (fun r => K (k + r))).Finite := by
      simpa only [t', K, hcast, Nat.add_assoc] using
        header_finiteness_step14_listing_tail P F p (N + k) t' hu hl G hG
    apply ((Set.finite_range (fun r : Fin k => K r.val)).union hf).subset
    rintro C ⟨m, hm, rfl⟩
    rcases lt_or_ge m k with hmk | hkm
    · exact Or.inl ⟨⟨m, hmk⟩, rfl⟩
    · exact Or.inr ⟨m - k, by simp only [Nat.add_sub_of_le hkm]; rfl⟩
  · apply Set.finite_empty.subset
    rintro C ⟨m, hm, _⟩
    exact (h ⟨m, hm⟩).elim

/-- Step 17 of the V4 proof of `header_finiteness` (V4 1.17):
"Finitely many tails and the finite prefix give the result". Only listed
incident tiles enter the union, so no common-listed assumption is needed. -/
private theorem header_finiteness_step17_cone_tuples
    (P : CompatiblePatch S) [Nonempty S.ι] (p : E d)
    {s : ℕ} (G : Fin s → Set (E d)) (hG : ∀ j, HPiCone S.hPi (G j)) :
    {K | ∃ (n : ℕ) (a : P.Incident p n),
      (P.native n a.val).Lists 0 ((S.σ ^ n) p) ∧
      K = fun j => (P.native n a.val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ n) '' G j)}.Finite := by
  classical
  obtain ⟨F⟩ := power_factorisation S
  obtain ⟨N, t, hcover, hN⟩ := header_finiteness_step15_tail_cover P p
  have hpref : (⋃ n : Fin N, Set.range (fun a : P.Incident p n.val =>
      fun j => (P.native n.val a.val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ n.val) '' G j))).Finite :=
    Set.finite_iUnion fun n => Set.finite_range _
  have ht := Set.finite_iUnion fun a : P.Incident p N =>
    header_finiteness_step16_tail_listings P F p N (t a) hN G hG
  apply (hpref.union ht).subset
  rintro K ⟨n, a, ha, rfl⟩
  rcases lt_or_ge n N with hn | hn
  · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨n, hn⟩, a, rfl⟩)
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    obtain ⟨a₀, rfl⟩ := hcover m a
    exact Or.inr (Set.mem_iUnion.mpr ⟨a₀, m, ha, rfl⟩)

/-- P12, V4 1.17: finite actual header tuples over all listing incident tiles.
No common-listed hypothesis is needed: only tiles listing the anchor contribute. -/
theorem header_finiteness (p : E d) {s : ℕ} (G : Fin s → Set (E d))
    (hG : ∀ j, HPiCone S.hPi (G j)) : (P.headers p G).Finite := by
  classical
  cases isEmpty_or_nonempty S.ι with
  | inl h =>
    letI := h
    exact Set.finite_empty.subset (fun h _ => isEmptyElim h.ty)
  | inr h =>
    letI := h
    let Label := Σ A : S.ι, {e // e ∈ (S.cx A).vertices}
    have hf := (header_finiteness_step17_cone_tuples P p G hG).biUnion
      (fun K _ => Set.finite_range (fun l : Label => (⟨l.1, l.2, K⟩ : Header S s)))
    apply hf.subset
    intro h hh
    obtain ⟨n, a, hv, hty, hc⟩ := hh
    have hlisted : (P.native n a.val).Lists 0 ((S.σ ^ n) p) := by
      refine ⟨h.vertex.val, ?_, hv⟩
      rw [← hty]
      exact h.vertex.property
    refine Set.mem_iUnion.mpr ⟨h.cones, Set.mem_iUnion.mpr
      ⟨⟨n, a, hlisted, funext hc⟩, ?_⟩⟩
    exact ⟨⟨h.ty, h.vertex⟩, by cases h; rfl⟩

/-- P13, V4 1.18: a complete star in a chosen incident tile's isometric frame,
with arbitrary labels from `Y`. Every incident tile and its vertex name is retained. -/
def positionedStar {Y : Type} (p : E d) (n : ℕ) (anchor : P.Incident p n)
    (label : P.Incident p n → Y) : Set (FramedNode S × Cell d × Y) :=
  {z | ∃ (a : P.Incident p n) (v : Cell d),
    v ∈ (S.cx (P.native n a.val).ty).vertices ∧
    (S.σ ^ n) p ∈ (P.native n a.val).cell 0 v ∧
    z = ((P.native n a.val).move (P.native n anchor.val).frame.symm, v, label a)}

/-- P13, V4 1.18: all possible complete positioned stars, allowing every
labelling at every depth and every choice of reference tile. -/
def positionedStars (Y : Type) (p : E d) :
    Set (Set (FramedNode S × Cell d × Y)) :=
  {s | ∃ (n : ℕ) (anchor : P.Incident p n) (label : P.Incident p n → Y),
    s = P.positionedStar p n anchor label}

/-- P13, V4 1.18: finitely many full positioned stars, with an arbitrary finite
label alphabet. This includes the unlabelled case by taking `Y = Unit`. -/
theorem positioned_stars_finite (Y : Type) [Finite Y] (p : E d)
    (hp : P.CommonListed p) : (P.positionedStars Y p).Finite := by
  sorry

/-- P14, V4 1.19: uniform native-scale cone radius and the union formula for
any selected collection of original tiles whose cones form the chosen cone.
A single positive radius works at every depth and for every selected subpatch. -/
theorem uniform_cone_radius (p : E d) (hp : P.CommonListed p) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      (∀ (n : ℕ) (a : P.Incident p n),
        (P.native n a.val).carrier 0 ∩ ball ((S.σ ^ n) p) r₀ =
          ((fun v => (S.σ ^ n) p + v) ''
            tangentCone ((P.native n a.val).carrier 0) ((S.σ ^ n) p)) ∩
              ball ((S.σ ^ n) p) r₀) ∧
      ∀ Q : Finset (FramedNode S), Q ⊆ P.tiles → ∀ n : ℕ,
        (⋃ a : P.Incident p n, ⋃ (_ : a.val.1.val ∈ Q),
          (P.native n a.val).carrier 0) ∩ ball ((S.σ ^ n) p) r₀ =
        ((fun v => (S.σ ^ n) p + v) ''
          ((S.σ ^ n) '' tangentCone (⋃ t ∈ Q, t.carrier 0) p)) ∩
            ball ((S.σ ^ n) p) r₀ := by
  sorry

end CompatiblePatch

/-- P11, V4 1.16(b): the cone language is closed under arbitrary finite unions. -/
theorem HPiCone_finite_union {α : Type} [Finite α] (K : α → Set (E d))
    (hK : ∀ a, HPiCone S.hPi (K a)) : HPiCone S.hPi (⋃ a, K a) := by
  sorry

/-- P11, V4 1.16(b): the cone language is closed under arbitrary finite intersections. -/
theorem HPiCone_finite_inter {α : Type} [Finite α] (K : α → Set (E d))
    (hK : ∀ a, HPiCone S.hPi (K a)) : HPiCone S.hPi (⋂ a, K a) := by
  sorry

/-- P11, V4 1.16(b'): the tangent cone of a finite union of compatible listed
cells at a common listed anchor remains an `HΠ`-cone, in all dimensions. -/
theorem tangentCone_union_isHPiCone (P : CompatiblePatch S)
    (Q : Finset (Σ t : {t // t ∈ P.tiles}, CellName S t.val.ty)) (p : E d)
    (hlisted : ∀ q ∈ Q, q.1.val.Lists 0 p)
    (hcontains : ∀ q ∈ Q, p ∈ q.1.val.cell 0 q.2.val) :
    HPiCone S.hPi (tangentCone (⋃ q ∈ Q, q.1.val.cell 0 q.2.val) p) := by
  sorry

/-- P14, V4 1.19: a single prototype-catalogue radius works for every placed
ground tile at every listed vertex, independently of patches and their depth.
An empty catalogue admits any positive radius. -/
theorem uniform_prototype_cone_radius (S : SubstSystem d) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (t : FramedNode S) (p : E d), t.Lists 0 p →
      t.carrier 0 ∩ ball p r₀ =
        ((fun v => p + v) '' tangentCone (t.carrier 0) p) ∩ ball p r₀ := by
  sorry

namespace CompatiblePatch

variable (P : CompatiblePatch S)

/-- P9, V4 1.14: the native subdivision has no repeated framed tile occurrences. -/
theorem native_injective (n : ℕ) : Function.Injective (P.native n) := by
  sorry

/-- P9, V4 1.14: all native tiles have disjoint interiors, with no side-to-side
hypothesis, and they cover exactly the ambient expansion of the original patch. -/
theorem native_subdivision (n : ℕ) :
    Pairwise (fun a b : P.Address n => Disjoint
      (interior ((P.native n a).carrier 0)) (interior ((P.native n b).carrier 0))) ∧
      (⋃ a : P.Address n, (P.native n a).carrier 0) =
        (S.σ ^ n) '' (⋃ t ∈ P.tiles, t.carrier 0) := by
  sorry

/-- P9, V4 1.14: the number of incident tiles never decreases with depth. -/
theorem incident_width_monotone (p : E d) (n : ℕ) :
    Nat.card (P.Incident p n) ≤ Nat.card (P.Incident p (n + 1)) := by
  sorry

/-- P12, V4 1.17: every incident tile listing the anchor contributes its full
header, with the actual named vertex. This supplies witnesses to the header set. -/
theorem header_occurs (p : E d) {s : ℕ} (G : Fin s → Set (E d)) (n : ℕ)
    (a : P.Incident p n)
    (v : {e // e ∈ (S.cx (P.native n a.val).ty).vertices})
    (hv : (S.σ ^ n) p ∈ (P.native n a.val).cell 0 v.val) :
    (⟨(P.native n a.val).ty, v,
      fun j => (P.native n a.val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ n) '' G j)⟩ : Header S s) ∈ P.headers p G := by
  sorry

end CompatiblePatch

end Enforce
