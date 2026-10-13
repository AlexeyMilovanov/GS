import Mathlib

/-!
# Tilings: the geometric model

Basic objects of the blueprint for arXiv:2606.25005v2 (Vereshchagin,
"Matching rules for substitution and hierarchical tilings for any
substitution with finite local complexity"), revised 12 October 2026.

Everything is formulated in the Euclidean plane `EuclideanSpace ℝ (Fin 2)`.
Only translations act on placed tiles.  Polygonal disks may be nonconvex and
may list collinear ("dummy") vertices.  All tilings in theorem statements
cover the plane (`PlaneTiling`); finite nonoverlapping collections are
`Patch`es.

This file contains definitions only.  No theorem of the paper is proved here.
Blueprint labels are given in the docstrings.
-/

open Set Pointwise

noncomputable section

namespace Tilings

/-- Points of the plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- Two sets of points overlap with positive length: they share a
nondegenerate segment. -/
def OverlapPos (s t : Set Pt) : Prop :=
  ∃ x y : Pt, x ≠ y ∧ segment ℝ x y ⊆ s ∩ t

/-! ## Polygonal disks (`def:polygon`) -/

/-- A compact simple polygonal disk with an indexed cyclic list of boundary
vertices.  Consecutive collinear vertices are permitted.  The carrier is
regular closed with path connected interior; its frontier is the union of the
listed sides, and distinct sides meet only in shared listed endpoints. -/
structure PolygonalDisk where
  /-- the closed region -/
  carrier : Set Pt
  /-- number of listed vertices -/
  n : ℕ
  three_le : 3 ≤ n
  /-- the listed vertices in cyclic order -/
  vertex : Fin n → Pt
  vertex_injective : Function.Injective vertex
  compact : IsCompact carrier
  interior_nonempty : (interior carrier).Nonempty
  regular_closed : closure (interior carrier) = carrier
  interior_pathConnected : IsPathConnected (interior carrier)
  frontier_eq :
    frontier carrier = ⋃ i : Fin n, segment ℝ (vertex i) (vertex (finRotate n i))
  simple : ∀ i j : Fin n, i ≠ j →
    segment ℝ (vertex i) (vertex (finRotate n i)) ∩
        segment ℝ (vertex j) (vertex (finRotate n j)) ⊆
      ({vertex i, vertex (finRotate n i)} : Set Pt) ∩ {vertex j, vertex (finRotate n j)}

namespace PolygonalDisk

variable (B : PolygonalDisk)

/-- The `i`-th listed side: the segment from vertex `i` to the next one. -/
def side (i : Fin B.n) : Set Pt := segment ℝ (B.vertex i) (B.vertex (finRotate B.n i))

/-- The set of listed vertices. -/
def vertexSet : Set Pt := range B.vertex

/-- A listed vertex is *genuine* if the two incident sides are not collinear;
otherwise it is a collinear ("dummy") vertex. -/
def IsGenuineVertex (i : Fin B.n) : Prop :=
  ¬ Collinear ℝ ({B.vertex ((finRotate B.n).symm i), B.vertex i, B.vertex (finRotate B.n i)} : Set Pt)

end PolygonalDisk

/-! ## Protosets, placed tiles, patches (`def:protoset`, `def:placed`) -/

/-- A finite protoset: a finite type of forms, each with a polygonal disk.
Colours belong to the form, so congruent coloured forms remain distinct. -/
structure Protoset where
  Form : Type
  [fintype : Fintype Form]
  [decEq : DecidableEq Form]
  disk : Form → PolygonalDisk

attribute [instance] Protoset.fintype Protoset.decEq

variable {P : Protoset}

/-- A placed tile: a form together with an anchor; its carrier is the
translate of the form's disk by the anchor. -/
@[ext]
structure PlacedTile (P : Protoset) where
  form : P.Form
  anchor : Pt

namespace PlacedTile

variable (A : PlacedTile P)

/-- The carrier (closed region) of a placed tile. -/
def carrier : Set Pt := A.anchor +ᵥ (P.disk A.form).carrier

/-- The `i`-th listed side of a placed tile. -/
def side (i : Fin (P.disk A.form).n) : Set Pt := A.anchor +ᵥ (P.disk A.form).side i

/-- The `i`-th listed vertex of a placed tile. -/
def vertex (i : Fin (P.disk A.form).n) : Pt := A.anchor +ᵥ (P.disk A.form).vertex i

/-- The set of listed vertices of a placed tile. -/
def vertexSet : Set Pt := range A.vertex

/-- Translate a placed tile. -/
def translate (v : Pt) : PlacedTile P := ⟨A.form, v +ᵥ A.anchor⟩

end PlacedTile

/-- Translate a set of placed tiles. -/
def translateSet (v : Pt) (S : Set (PlacedTile P)) : Set (PlacedTile P) :=
  (fun A => A.translate v) '' S

/-- The union of the carriers of a set of placed tiles. -/
def support (S : Set (PlacedTile P)) : Set Pt := ⋃ A ∈ S, A.carrier

/-- Interiors of the tiles in `S` are pairwise disjoint. -/
def DisjointInteriors (S : Set (PlacedTile P)) : Prop :=
  S.PairwiseDisjoint fun A => interior A.carrier

/-- A patch: a finite set of placed tiles with pairwise disjoint interiors. -/
structure Patch (P : Protoset) where
  tiles : Set (PlacedTile P)
  finite : tiles.Finite
  disjoint : DisjointInteriors tiles

/-- `F` occurs in `S` up to translation. -/
def OccursIn (F S : Set (PlacedTile P)) : Prop :=
  ∃ v : Pt, translateSet v F ⊆ S

/-- A set of placed tiles is side-to-side: two sides of its tiles that
overlap with positive length coincide as whole segments. -/
def SideToSideSet (S : Set (PlacedTile P)) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, ∀ (i : Fin (P.disk A.form).n) (j : Fin (P.disk B.form).n),
    OverlapPos (A.side i) (B.side j) → A.side i = B.side j

/-! ## Plane tilings (`def:tiling`) -/

/-- A plane tiling: placed tiles covering the whole plane with pairwise
disjoint interiors.  Plane coverage is part of every theorem statement. -/
structure PlaneTiling (P : Protoset) where
  tiles : Set (PlacedTile P)
  cover : support tiles = univ
  disjoint : DisjointInteriors tiles

namespace PlaneTiling

/-- Side-to-side plane tiling. -/
def SideToSide (T : PlaneTiling P) : Prop := SideToSideSet T.tiles

/-- Membership of a placed tile in a tiling. -/
instance : Membership (PlacedTile P) (PlaneTiling P) := ⟨fun T A => A ∈ T.tiles⟩

end PlaneTiling

/-! ## Substitutions (`def:substitution`) -/

/-- A substitution with common expansion factor `θ > 1`: for each form a
finite patch whose support is the scaled disk `θ • carrier`. -/
structure Substitution (P : Protoset) where
  θ : ℝ
  one_lt : 1 < θ
  rule : P.Form → Patch P
  support_eq : ∀ p, support (rule p).tiles = θ • (P.disk p).carrier

namespace Substitution

variable (τ : Substitution P)

/-- Decomposition of one placed tile: the rule patch translated by `θ • anchor`. -/
def decomposeTile (A : PlacedTile P) : Set (PlacedTile P) :=
  translateSet (τ.θ • A.anchor) (τ.rule A.form).tiles

/-- Decomposition of a set of placed tiles. -/
def decompose (S : Set (PlacedTile P)) : Set (PlacedTile P) :=
  ⋃ A ∈ S, τ.decomposeTile A

/-- `n`-fold decomposition. -/
def decomposeIter (n : ℕ) (S : Set (PlacedTile P)) : Set (PlacedTile P) :=
  Nat.rec S (fun _ T => τ.decompose T) n

/-- The supertile of order `n` on form `p`, anchored at the origin. -/
def supertile (n : ℕ) (p : P.Form) : Set (PlacedTile P) :=
  τ.decomposeIter n {⟨p, 0⟩}

/-- `T'` is a composition of `T` (equivalently `T` is the decomposition of `T'`). -/
def IsComposition (T' T : PlaneTiling P) : Prop := τ.decompose T'.tiles = T.tiles

/-- A substitution tiling: every finite subset occurs, up to translation,
in some supertile (`def:hierarchy`). -/
def IsSubstitutionTiling (T : PlaneTiling P) : Prop :=
  ∀ F ⊆ T.tiles, F.Finite → ∃ (n : ℕ) (p : P.Form), OccursIn F (τ.supertile n p)

/-- A hierarchical tiling: an infinite chain of compositions. -/
def IsHierarchical (T : PlaneTiling P) : Prop :=
  ∃ seq : ℕ → PlaneTiling P, seq 0 = T ∧ ∀ n, τ.IsComposition (seq (n + 1)) (seq n)

/-- A side-to-side hierarchical tiling: an infinite chain of compositions all
of whose members are side-to-side. -/
def IsSideToSideHierarchical (T : PlaneTiling P) : Prop :=
  ∃ seq : ℕ → PlaneTiling P, seq 0 = T ∧ (∀ n, τ.IsComposition (seq (n + 1)) (seq n)) ∧
    ∀ n, (seq n).SideToSide


private lemma pow_finite (m : ℕ) (p : P.Form) : (τ.supertile m p).Finite := by
  induction' m with n ih
  · exact Set.finite_singleton (⟨p, 0⟩ : PlacedTile P)
  · change (τ.decompose (τ.decomposeIter n {⟨p, 0⟩})).Finite
    apply Set.Finite.biUnion ih
    intro A _
    exact Set.Finite.image _ (τ.rule A.form).finite

private lemma pow_iterate_support_translateSet (v : Pt) (S : Set (PlacedTile P)) :
    support (translateSet v S) = v +ᵥ support S := by
  ext x
  simp only [support, translateSet, PlacedTile.translate, PlacedTile.carrier, Set.mem_iUnion,
    Set.mem_image, Set.mem_vadd_set_iff_neg_vadd_mem]
  constructor
  · rintro ⟨A, ⟨B, hB, rfl⟩, hx⟩
    exact ⟨B, hB, by simpa [←add_assoc] using hx⟩
  · rintro ⟨A, hA, hx⟩
    refine ⟨⟨A.form, v +ᵥ A.anchor⟩, ⟨A, hA, rfl⟩, ?_⟩
    simpa [←add_assoc] using hx

private lemma pow_iterate_support_decomposeTile (A : PlacedTile P) :
    support (τ.decomposeTile A) = τ.θ • A.carrier := by
  dsimp [decomposeTile]
  rw [pow_iterate_support_translateSet, τ.support_eq, PlacedTile.carrier]
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

private lemma pow_iterate_support_decompose (S : Set (PlacedTile P)) :
    support (τ.decompose S) = τ.θ • support S := by
  dsimp [decompose, support]
  rw [Set.smul_set_iUnion₂]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨A, ⟨B, hB, hA⟩, hx⟩
    refine ⟨B, hB, ?_⟩
    have h : x ∈ support (τ.decomposeTile B) := by
      simp only [support, Set.mem_iUnion]
      exact ⟨A, hA, hx⟩
    rw [pow_iterate_support_decomposeTile] at h
    exact h
  · rintro ⟨A, hA, hx⟩
    have h : x ∈ support (τ.decomposeTile A) := by
      rw [pow_iterate_support_decomposeTile]
      exact hx
    simp only [support, Set.mem_iUnion] at h
    rcases h with ⟨B, hB, hx'⟩
    exact ⟨B, ⟨A, hA, hB⟩, hx'⟩

private lemma pow_support_eq (m : ℕ) (p : P.Form) :
    support (τ.supertile m p) = τ.θ ^ m • (P.disk p).carrier := by
  induction' m with n ih
  · dsimp [supertile, decomposeIter, support, PlacedTile.carrier]
    ext x
    simp
  · change support (τ.decompose (τ.supertile n p)) = τ.θ ^ (n + 1) • (P.disk p).carrier
    rw [pow_iterate_support_decompose]
    rw [ih, smul_smul, pow_succ']

/-- The power `τ^m` as a substitution (`lem:hierarchy-step`). -/
noncomputable def pow (m : ℕ) (hm : 0 < m) : Substitution P where
  θ := τ.θ ^ m
  one_lt := one_lt_pow₀ τ.one_lt hm.ne'
  rule := fun p =>
    { tiles := τ.supertile m p
      finite := pow_finite τ m p
      disjoint := sorry }
  support_eq := pow_support_eq τ m


/-! ### Crowns, FLC, STS (`def:crown`, `def:flc`, `def:sts`) -/

/-- `v` is a listed vertex of some tile of `S`. -/
def IsVertexOf (S : Set (PlacedTile P)) (v : Pt) : Prop :=
  ∃ A ∈ S, v ∈ A.vertexSet

/-- The full crown of `S` at `v`: all tiles whose closed carrier contains `v`. -/
def crown (S : Set (PlacedTile P)) (v : Pt) : Set (PlacedTile P) :=
  {A ∈ S | v ∈ A.carrier}

/-- `K` is a `τ`-allowed pointed crown with centre `0`: it is the translate to
the origin of the crown at a listed vertex of some supertile.  Incomplete
crowns at supertile boundaries are included. -/
def IsAllowedCrown (K : Set (PlacedTile P)) : Prop :=
  ∃ (n : ℕ) (p : P.Form) (w : Pt), IsVertexOf (τ.supertile n p) w ∧ K = translateSet (-w) (crown (τ.supertile n p) w)

/-- Finite local complexity: finitely many allowed pointed crowns up to
translation. -/
def FLC : Prop := {K | τ.IsAllowedCrown K}.Finite

/-- The STS hypothesis: every supertile is side-to-side. -/
def STS : Prop := ∀ n p, SideToSideSet (τ.supertile n p)

/-- Hereditary listed sides (`def:hereditary`): every scaled listed vertex of
a form is a listed vertex of a child, and every scaled listed side is the
union of the child listed sides it contains.  Not a consequence of STS. -/
def HereditarySides : Prop :=
  (∀ p (i : Fin (P.disk p).n), IsVertexOf (τ.rule p).tiles (τ.θ • (P.disk p).vertex i)) ∧
  ∀ p (i : Fin (P.disk p).n),
    τ.θ • (P.disk p).side i =
      ⋃ (A ∈ (τ.rule p).tiles) (j : Fin (P.disk A.form).n)
        (_ : A.side j ⊆ τ.θ • (P.disk p).side i), A.side j

end Substitution

/-! ## Local rules, decorations, soficity (`def:localrule`, `def:sofic`) -/

/-- A bounded local rule: a (possibly infinite) set of finite forbidden
patches, all of support diameter at most `D`. -/
structure LocalRule (P : Protoset) where
  forbidden : Set (Set (PlacedTile P))
  D : ℝ
  bounded : ∀ F ∈ forbidden, F.Finite ∧ Metric.diam (support F) ≤ D

/-- A plane tiling is proper for a local rule if no forbidden patch occurs in
it up to translation. -/
def LocalRule.Proper (R : LocalRule P) (T : PlaneTiling P) : Prop :=
  ∀ F ∈ R.forbidden, ¬ OccursIn F T.tiles

/-- A decoration of `P`: a finite protoset `P'` with a surjective projection
to the forms of `P` preserving carriers.  Listed vertices of decorated forms
may differ from those of the original form (this is used for clones). -/
structure Decoration (P : Protoset) where
  P' : Protoset
  proj : P'.Form → P.Form
  surj : Function.Surjective proj
  carrier_eq : ∀ q, (P'.disk q).carrier = (P.disk (proj q)).carrier

namespace Decoration

variable (dec : Decoration P)

/-- Projection of a placed decorated tile. -/
def projTile (A : PlacedTile dec.P') : PlacedTile P := ⟨dec.proj A.form, A.anchor⟩

private lemma project_projTile_carrier (A : PlacedTile dec.P') :
    (dec.projTile A).carrier = A.carrier := by
  dsimp [PlacedTile.carrier, projTile]
  rw [dec.carrier_eq]

/-- Projection of a plane tiling. -/
def project (T : PlaneTiling dec.P') : PlaneTiling P where
  tiles := dec.projTile '' T.tiles
  cover := by
    have := T.cover
    dsimp [support] at this ⊢
    rw [biUnion_image]
    simp_rw [project_projTile_carrier]
    exact this
  disjoint := by
    have hd := T.disjoint
    rintro X ⟨A, hA, rfl⟩ Y ⟨B, hB, rfl⟩ hne
    have hd_AB : Disjoint (interior A.carrier) (interior B.carrier) := by
      by_cases h : A = B
      · subst h
        exact (hne rfl).elim
      · exact hd hA hB h
    change Disjoint (interior (dec.projTile A).carrier) (interior (dec.projTile B).carrier)
    rw [project_projTile_carrier, project_projTile_carrier]
    exact hd_AB

end Decoration

/-- A family of plane tilings is sofic if it is exactly the set of projections
of the proper plane tilings for some finite decoration and bounded local rule. -/
def IsSofic (F : Set (PlaneTiling P)) : Prop :=
  ∃ (dec : Decoration P) (R : LocalRule dec.P'),
    ∀ T, T ∈ F ↔ ∃ T' : PlaneTiling dec.P', R.Proper T' ∧ dec.project T' = T

/-- A side decoration: decorated forms have exactly the original polygonal
disks (same listed sides), and each listed side carries a colour from a
finite colour type. -/
structure SideDecoration (P : Protoset) extends Decoration P where
  disk_eq : ∀ q, P'.disk q = P.disk (proj q)
  Colour : Type
  [colourFintype : Fintype Colour]
  colour : ∀ q, Fin (P'.disk q).n → Colour

attribute [instance] SideDecoration.colourFintype

/-- Proper for the side rule: side-to-side, and coincident sides of distinct
tiles carry equal colours. -/
def SideDecoration.Proper (dec : SideDecoration P) (T : PlaneTiling dec.P') : Prop :=
  T.SideToSide ∧
    ∀ A ∈ T.tiles, ∀ B ∈ T.tiles, A ≠ B →
      ∀ (i : Fin (dec.P'.disk A.form).n) (j : Fin (dec.P'.disk B.form).n),
        A.side i = B.side j → dec.colour A.form i = dec.colour B.form j

/-- Side-to-side sofic: sofic via a side decoration and the side rule. -/
def IsSideToSideSofic (F : Set (PlaneTiling P)) : Prop :=
  ∃ dec : SideDecoration P,
    ∀ T, T ∈ F ↔ ∃ T' : PlaneTiling dec.P', dec.Proper T' ∧ dec.toDecoration.project T' = T

end Tilings

end
