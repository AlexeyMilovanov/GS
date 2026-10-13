import Tilings.Control.Decoration

/-!
# A boundary-header repair of coloured composition (statements)

Statements of chapter `composition.tex` of the blueprint, with the planned
Lean names of the manifest.  Every proof is `sorry`.

Every theorem carries the standing hypothesis of the chapter that the
macrotemplate system has hereditary listed sides (`hH : c.Hereditary`).

The first part of the file contains the definitions needed to state the
lemmas: coloured macroblocks (`ColouredBlock`), partitions of a decorated
plane tiling into macroblocks (`MacroPartition`), the reconstructed parent
(`reconstruct`), exact repaired decompositions and compositions, mode
uniformity, and the hypotheses/conclusion of the alignment lemma.
-/

open Set Pointwise

noncomputable section

namespace Tilings

namespace Planned

open Geometry

variable {P : Protoset}

/-! ## Coloured macroblocks -/

/-- A positioned coloured realization of the template `σ' α`: the child of
type `t` (with `owner t = α`) is the decorated tile `⟨t, col t⟩` placed at
`v + anchor t`.  Values of `col` at types of other templates are
irrelevant. -/
structure ColouredBlock (c : MacroCertificate P) where
  /-- the parent form -/
  α : c.Q.Form
  /-- the offset (`θ` times the parent anchor) -/
  v : Pt
  /-- the colours of the children -/
  col : (t : c.Typ) → c.Side t → Fin 5 → U c

namespace ColouredBlock

variable {c : MacroCertificate P} (K : ColouredBlock c)

/-- The decorated child of type `t`. -/
def tileOf (t : c.Typ) : DecTile c := ⟨t, K.col t⟩

/-- The placed decorated child of type `t`. -/
def placed (t : c.Typ) : PlacedTile (typedDecoration c) := ⟨K.tileOf t, K.v + c.anchor t⟩

/-- The tiles of the block. -/
def tiles : Set (PlacedTile (typedDecoration c)) :=
  {X | ∃ t, c.owner t = K.α ∧ X = K.placed t}

/-- The placed segment of a child side occurrence. -/
def childSide (o : c.SideOcc) : Set Pt :=
  (K.v + c.anchor o.1) +ᵥ (c.Q.disk (c.form o.1)).side o.2

/-- The placed scaled parent side `d` (a macroside). -/
def macroSide (d : Fin (c.Q.disk K.α).n) : Set Pt :=
  K.v +ᵥ c.macroSide K.α d

/-- The centre of the block. -/
def centre : DecTile c := K.tileOf (c.central K.α)

end ColouredBlock

/-- A partition of a decorated plane tiling into positioned coloured
macroblocks. -/
structure MacroPartition (c : MacroCertificate P) (T : PlaneTiling (typedDecoration c)) where
  /-- index set of the blocks -/
  ι : Type
  /-- the blocks -/
  block : ι → ColouredBlock c
  /-- distinct blocks are disjoint -/
  disjoint : Pairwise fun j j' => Disjoint (block j).tiles (block j').tiles
  /-- the blocks cover the tiling -/
  cover : ⋃ j, (block j).tiles = T.tiles

/-- A finite coloured realization is *proper*: every nontrivial inner side
of a child has a complete coincident opposing side of another child of the
block with the same five-tuple. -/
def IsProperRealization (c : MacroCertificate P) (K : ColouredBlock c) : Prop :=
  ∀ (t : c.Typ) (i : c.Side t), c.owner t = K.α → c.IsInner (c.occ t i) →
    IsNontrivial c (K.tileOf t) i →
    ∃ (t' : c.Typ) (j : c.Side t'), c.owner t' = K.α ∧ t' ≠ t ∧
      K.childSide (c.occ t' j) = K.childSide (c.occ t i) ∧ ∀ k : Fin 5, K.col t' j k = K.col t i k

/-- The standing situation of `lem:comp/boundary-header`: a proper finite
coloured realization of `σ' α` in which every tile except possibly the
centre is legal. -/
def BlockContext (c : MacroCertificate P) (K : ColouredBlock c) : Prop :=
  IsProperRealization c K ∧
    ∀ t, c.owner t = K.α → t ≠ c.central K.α → headerLegal c (K.tileOf t)

/-- The conclusion of `lem:comp/boundary-header` for a header `h`: every
boundary fourth cell carries `h`, and `form (type h) = α`. -/
def CommonHeader (c : MacroCertificate P) (K : ColouredBlock c)
    (h : HeaderKernel.Header c.Typ c.Side) : Prop :=
  c.form h.1 = K.α ∧
    ∀ (t : c.Typ) (i : c.Side t), c.owner t = K.α → c.IsBoundary (c.occ t i) →
      K.col t i 3 = headerU c h

/-- The reconstructed parent `D` of type `t`: `D_i(d)` is the third cell of
port `i` on `σ'd` (`lem:comp/reconstruction`). -/
def reconstruct (c : MacroCertificate P) (K : ColouredBlock c) (t : c.Typ) : DecTile c where
  typ := t
  cell d k := match c.port (c.form t) d k with
    | some o => K.col o.1 o.2 2
    | none => 0

/-- The block `K` is an exact member of the decomposition of `D` under the
child relation `R`. -/
def IsExactBlockOfWith (c : MacroCertificate P) (R : DecTile c → DecTile c → Prop)
    (K : ColouredBlock c) (D : DecTile c) : Prop :=
  c.form D.typ = K.α ∧ ∀ t, c.owner t = K.α → R D (K.tileOf t)

/-- Exact repaired decomposition of `D` (`lem:comp/exact`). -/
abbrev IsExactBlockOf (c : MacroCertificate P) (K : ColouredBlock c) (D : DecTile c) : Prop :=
  IsExactBlockOfWith c (IsChildOf c) K D

/-- `T` is an exact decomposition of `T'` under the child relation `R`
(equivalently `T'` is an exact composition of `T`). -/
def IsExactCompositionWith (c : MacroCertificate P) (R : DecTile c → DecTile c → Prop)
    (T' T : PlaneTiling (typedDecoration c)) : Prop :=
  ∃ blk : T'.tiles → ColouredBlock c,
    (∀ X : T'.tiles, IsExactBlockOfWith c R (blk X) (tileDec X.1) ∧
      (blk X).v = c.σ.θ • X.1.anchor) ∧
    T.tiles = ⋃ X : T'.tiles, (blk X).tiles

/-- Exact repaired composition. -/
abbrev IsExactComposition (c : MacroCertificate P) (T' T : PlaneTiling (typedDecoration c)) :
    Prop :=
  IsExactCompositionWith c (IsChildOf c) T' T

/-- `T'` is obtained from the macroblocks of `part` by replacing each block
with its reconstructed parent and scaling down by `θ`. -/
def IsReconstruction (c : MacroCertificate P) {T : PlaneTiling (typedDecoration c)}
    (part : MacroPartition c T) (T' : PlaneTiling (typedDecoration c)) : Prop :=
  (∀ X ∈ T'.tiles, ∃ j, (part.block j).v = c.σ.θ • X.anchor ∧
      tileDec X = reconstruct c (part.block j) (tileDec X).typ) ∧
  (∀ j, ∃ X ∈ T'.tiles, (part.block j).v = c.σ.θ • X.anchor ∧
      tileDec X = reconstruct c (part.block j) (tileDec X).typ)

/-- A macroside is *mode-uniform*: either all its child outer sides carry
positive ranks, or all carry zero. -/
def ModeUniform (c : MacroCertificate P) (K : ColouredBlock c) (d : Fin (c.Q.disk K.α).n) :
    Prop :=
  (∀ o ∈ c.outerList K.α d, IsRankU c (K.col o.1 o.2 3)) ∨
    (∀ o ∈ c.outerList K.α d, K.col o.1 o.2 3 = 0)

/-- Hypothesis of `lem:comp/alignment`: every child side of the macroside `d`
of block `j` carries a positive rank and has a complete opposing side (of
another tile) with the same rank. -/
def RankMatched (c : MacroCertificate P) {T : PlaneTiling (typedDecoration c)}
    (part : MacroPartition c T) (j : part.ι) (d : Fin (c.Q.disk (part.block j).α).n) : Prop :=
  ∀ o ∈ c.outerList (part.block j).α d,
    IsRankU c ((part.block j).col o.1 o.2 3) ∧
    ∃ Y ∈ T.tiles, Y ≠ (part.block j).placed o.1 ∧ ∃ j' : c.Side (tileDec Y).typ,
      sideOf c Y j' = (part.block j).childSide o ∧
      (tileDec Y).cell j' 3 = (part.block j).col o.1 o.2 3

/-- Conclusion of `lem:comp/alignment`: the macroside `d` of block `j` has a
complete opposing macroside of another block with the same ordered
subdivision. -/
def OpposingMacroside (c : MacroCertificate P) {T : PlaneTiling (typedDecoration c)}
    (part : MacroPartition c T) (j : part.ι) (d : Fin (c.Q.disk (part.block j).α).n) : Prop :=
  ∃ j' : part.ι, j' ≠ j ∧ ∃ e : Fin (c.Q.disk (part.block j').α).n,
    (part.block j').macroSide e = (part.block j).macroSide d ∧
    List.Forall₂ (fun o o' => (part.block j).childSide o = (part.block j').childSide o')
      (c.outerList (part.block j).α d) (c.outerList (part.block j').α e)

/-! ## Statements -/

/-- Step 1 of the blueprint proof of `boundary_side_of_outer_side`: By (G1) the type
has an inner side. -/
private lemma boundary_side_of_outer_side_step1_inner (c : MacroCertificate P) (t : c.Typ) :
    ∃ j : c.Side t, c.IsInner (c.occ t j) :=
  c.g1_inner_side t

/-- Step 2 of the blueprint proof of `boundary_side_of_outer_side`: Walk around its
boundary polygon from an outer side; the first side that is not outer starts at the
endpoint of the last outer side. This lemma states there is a pair of consecutive
sides where the first is outer and the second is inner. -/
private lemma boundary_side_of_outer_side_step2_transition (c : MacroCertificate P) (t : c.Typ)
    (i : c.Side t) (hi : c.IsOuter (c.occ t i)) (j : c.Side t) (hj : c.IsInner (c.occ t j)) :
    ∃ k : c.Side t, c.IsOuter (c.occ t k) ∧ c.IsInner (c.occ t (finRotate _ k)) := by
  sorry

/-- Step 3 of the blueprint proof of `boundary_side_of_outer_side`: the endpoint of a
side is the start of the next side. -/
private lemma boundary_side_of_outer_side_step3_endpoint (c : MacroCertificate P) (t : c.Typ)
    (k : c.Side t) : c.occEnd (c.occ t k) = c.occStart (c.occ t (finRotate _ k)) := rfl

/-- Step 4 of the blueprint proof of `boundary_side_of_outer_side`: an outer side has
its endpoint on the macroboundary. -/
private lemma boundary_side_of_outer_side_step4_end_mem (c : MacroCertificate P) (t : c.Typ)
    (k : c.Side t) (hk : c.IsOuter (c.occ t k)) :
    c.occEnd (c.occ t k) ∈ c.macroBoundary (c.owner t) := by
  dsimp [MacroData.IsOuter] at hk
  have h_mem : c.occEnd (c.occ t k) ∈ c.occSide (c.occ t k) := by
    dsimp [MacroData.occEnd, MacroData.occSide, MacroData.childTile, PlacedTile.side, PolygonalDisk.side]
    exact ⟨_, right_mem_segment ℝ _ _, rfl⟩
  exact hk h_mem

/-- Step 5 of the blueprint proof of `boundary_side_of_outer_side`: an inner side
starting on the macroboundary is a boundary side. -/
private lemma boundary_side_of_outer_side_step5_boundary (c : MacroCertificate P) (t : c.Typ)
    (k' : c.Side t) (h_in : c.IsInner (c.occ t k'))
    (h_start : c.occStart (c.occ t k') ∈ c.macroBoundary (c.owner t)) :
    c.IsBoundary (c.occ t k') := by
  dsimp [MacroData.IsBoundary]
  exact ⟨h_in, Or.inl h_start⟩

/-- `lem:comp/outer-boundary`: in a macrotemplate every child type with an
outer side also has a boundary side. -/
theorem boundary_side_of_outer_side (c : MacroCertificate P) (hH : c.Hereditary)
    (t : c.Typ) (i : c.Side t) (hi : c.IsOuter (c.occ t i)) :
    ∃ j : c.Side t, c.IsBoundary (c.occ t j) := by
  have _ := hH
  obtain ⟨j, hj⟩ := boundary_side_of_outer_side_step1_inner c t
  obtain ⟨k, hk_out, hk_in⟩ := boundary_side_of_outer_side_step2_transition c t i hi j hj
  use finRotate _ k
  have h_end_mem := boundary_side_of_outer_side_step4_end_mem c t k hk_out
  rw [boundary_side_of_outer_side_step3_endpoint c t k] at h_end_mem
  exact boundary_side_of_outer_side_step5_boundary c t _ hk_in h_end_mem

/-- Step 1 of the blueprint proof of `headerLegal_properties`: a legal tile has a legal parent. -/
private lemma headerLegal_properties_step1_parent (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    ∃ C, headerLegal c C ∧ IsChildOf c C A := by
  sorry

/-- Step 2 of the blueprint proof of `headerLegal_properties`: a legal tile is normal and
identity-correct. -/
private lemma headerLegal_properties_step2_normal_id (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    IsNormal c A ∧ IsIdentityCorrect c A := by
  sorry

/-- Step 3 of the blueprint proof of `headerLegal_properties`: every child of a legal parent is
legal. -/
private lemma headerLegal_properties_step3_child (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    ∀ B, IsChildOf c A B → headerLegal c B := by
  sorry

/-- Step 4 of the blueprint proof of `headerLegal_properties`: all boundary fourth cells of a legal
tile equal one parent header. -/
private lemma headerLegal_properties_step4_boundary (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    ∃ C, headerLegal c C ∧ IsChildOf c C A ∧
      ∀ i : c.Side A.typ, c.IsBoundary (c.occ A.typ i) → A.cell i 3 = headerU c (headerOf c C) := by
  sorry

/-- Step 5 of the blueprint proof of `headerLegal_properties`: third signals belonging to the same
path are equal through a legal tile. -/
private lemma headerLegal_properties_step5_path (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    ∀ (d : Fin (c.Q.disk (c.owner A.typ)).n) (j : Fin 5) (i i' : c.Side A.typ),
      c.occ A.typ i ∈ c.path (c.owner A.typ) d j → c.occ A.typ i' ∈ c.path (c.owner A.typ) d j →
      ¬ c.IsPrint (c.occ A.typ i) → ¬ c.IsPrint (c.occ A.typ i') → A.cell i 2 = A.cell i' 2 := by
  sorry

/-- Step 6 of the blueprint proof of `headerLegal_properties`: every inner side of a legal tile is
nontrivial. -/
private lemma headerLegal_properties_step6_inner (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    InnerActive c A := by
  sorry

/-- Step 7 of the blueprint proof of `headerLegal_properties`: on an outer side, triviality is
equivalent to a zero fourth cell. -/
private lemma headerLegal_properties_step7_outer (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    ∀ i : c.Side A.typ, c.IsOuter (c.occ A.typ i) → (¬ IsNontrivial c A i ↔ A.cell i 3 = 0) := by
  sorry

/-- `lem:comp/legal-properties`: a legal tile has a legal parent, is normal
and identity-correct; every child of a legal tile is legal; all boundary
fourth cells equal the header of one legal parent; third signals of one path
agree; inner sides are nontrivial; on an outer side triviality is
equivalent to a zero fourth cell. -/
theorem headerLegal_properties (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    (∃ C, headerLegal c C ∧ IsChildOf c C A) ∧
    IsNormal c A ∧ IsIdentityCorrect c A ∧
    (∀ B, IsChildOf c A B → headerLegal c B) ∧
    (∃ C, headerLegal c C ∧ IsChildOf c C A ∧
      ∀ i : c.Side A.typ, c.IsBoundary (c.occ A.typ i) → A.cell i 3 = headerU c (headerOf c C)) ∧
    (∀ (d : Fin (c.Q.disk (c.owner A.typ)).n) (j : Fin 5) (i i' : c.Side A.typ),
      c.occ A.typ i ∈ c.path (c.owner A.typ) d j → c.occ A.typ i' ∈ c.path (c.owner A.typ) d j →
      ¬ c.IsPrint (c.occ A.typ i) → ¬ c.IsPrint (c.occ A.typ i') → A.cell i 2 = A.cell i' 2) ∧
    InnerActive c A ∧
    (∀ i : c.Side A.typ, c.IsOuter (c.occ A.typ i) → (¬ IsNontrivial c A i ↔ A.cell i 3 = 0)) := by
  exact ⟨
    headerLegal_properties_step1_parent c hH A hA,
    (headerLegal_properties_step2_normal_id c hH A hA).1,
    (headerLegal_properties_step2_normal_id c hH A hA).2,
    headerLegal_properties_step3_child c hH A hA,
    headerLegal_properties_step4_boundary c hH A hA,
    headerLegal_properties_step5_path c hH A hA,
    headerLegal_properties_step6_inner c hH A hA,
    headerLegal_properties_step7_outer c hH A hA
  ⟩

/-- `lem:comp/assembly`: a proper plane tiling of normal identity-correct
typed tiles in which every inner side is nontrivial admits a partition into
positioned `σ'` macrotemplates. -/
theorem assembleMacrotemplates (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hN : ∀ X ∈ T.tiles, IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
      InnerActive c (tileDec X)) :
    Nonempty (MacroPartition c T) := by
  sorry

/-- `lem:comp/assembly` (final assertion): every proper legal plane tiling
has such a partition. -/
theorem assembleMacrotemplates_of_legal (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X)) :
    Nonempty (MacroPartition c T) := by
  sorry


/-- Step 1 of the blueprint proof of `boundary_header_constant`: a boundary tile is legal. -/
private lemma boundary_header_constant_step1_legal (c : MacroCertificate P)
    (K : ColouredBlock c) (hK : BlockContext c K) (t : c.Typ) (ht : c.owner t = K.α)
    (i : c.Side t) (hi : c.IsBoundary (c.occ t i)) :
    headerLegal c (K.tileOf t) := by
  apply hK.2 t ht
  rintro rfl
  exact (c.g2_central K.α i).2 hi


/-- Step 2 of the blueprint proof of `boundary_header_constant`: the boundary cells of a single
legal tile equal the header of any chosen legal parent, so it is a constant. -/
private lemma boundary_header_constant_step2_header_eq (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K) (t : c.Typ) (ht : c.owner t = K.α)
    (i : c.Side t) (hi : c.IsBoundary (c.occ t i)) :
    ∃ h : HeaderKernel.Header c.Typ c.Side,
      (∀ j : c.Side t, c.IsBoundary (c.occ t j) → K.col t j 3 = headerU c h) ∧
      c.form h.1 = K.α := by
  sorry

/-- Step 4 of the blueprint proof of `boundary_header_constant`: connectedness propagates equality
to every boundary cell of the block. -/
private lemma boundary_header_constant_step4_belt_eq (c : MacroCertificate P)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (u v : {t : c.Typ // c.IsBeltType K.α t})
    (i : c.Side u.1) (hi : c.IsBoundary (c.occ u.1 i))
    (j : c.Side v.1) (hj : c.IsBoundary (c.occ v.1 j)) :
    K.col u.1 i 3 = K.col v.1 j 3 := by
  sorry

/-- Step 5 of the blueprint proof of `boundary_header_constant`: any boundary side owner
is part of the boundary belt type. -/
private lemma boundary_header_constant_step5_is_belt_type (c : MacroCertificate P) (α : c.Q.Form)
    (t : c.Typ) (ht : c.owner t = α) (i : c.Side t) (hi : c.IsBoundary (c.occ t i)) :
    c.IsBeltType α t := by
  sorry

/-- `lem:comp/boundary-header`: in a proper finite coloured realization of
`σ' α` whose noncentral tiles are legal, every boundary fourth cell carries
the same header `h = (t, v)`, and `form t = α`. -/
theorem boundary_header_constant (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K) :
    ∃ h : HeaderKernel.Header c.Typ c.Side, CommonHeader c K h := by
  have h_ne := (c.g2_belt_connected K.α).nonempty
  let u := Classical.choice h_ne
  have hu_owner : c.owner u.1 = K.α := u.property.1
  have hu_belt_own : c.IsBeltType (c.owner u.1) u.1 := by
    rw [hu_owner]
    exact u.property
  obtain ⟨i, hi⟩ := c.g2_belt_edge u.1 hu_belt_own
  obtain ⟨h, hh1, hh2⟩ := boundary_header_constant_step2_header_eq c hH K hK u.1 hu_owner i hi
  use h
  constructor
  · exact hh2
  · intro t j ht hj
    have ht_belt : c.IsBeltType K.α t := boundary_header_constant_step5_is_belt_type c K.α t ht j hj
    let v : {t : c.Typ // c.IsBeltType K.α t} := ⟨t, ht_belt⟩
    have h_eq := boundary_header_constant_step4_belt_eq c K hK v u j hj i hi
    rw [h_eq]
    exact hh1 i hi

/-- Step 1 of the blueprint proof of `reconstructed_header_eq_isNormal`: extracting the legal boundary parent tile. -/
private lemma reconstructed_header_eq_isNormal_aux1 (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (d : c.Side h.1) (i : Fin 5) (hLoc : IsLocal c (c.occ h.1 d) i) :
    ∃ (o : c.SideOcc) (ho : c.port (c.form h.1) d i = some o),
      headerLegal c (K.tileOf o.1) ∧
      (K.tileOf o.1).cell o.2 2 = K.col o.1 o.2 2 := by
  sorry

/-- Step 2 of the blueprint proof of `reconstructed_header_eq_isNormal`: extracting normality from the legal parent tile. -/
private lemma reconstructed_header_eq_isNormal_aux2 (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (d : c.Side h.1) (i : Fin 5) (hLoc : IsLocal c (c.occ h.1 d) i)
    (o : c.SideOcc) (ho : c.port (c.form h.1) d i = some o)
    (hLeg : headerLegal c (K.tileOf o.1)) :
    (K.tileOf o.1).cell o.2 2 = prescribedCell c (c.occ h.1 d) i := by
  sorry

/-- Step 1 of the blueprint proof of `reconstructed_header_eq`: proving normality. -/
private lemma reconstructed_header_eq_isNormal (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) :
    IsNormal c (reconstruct c K h.1) := by
  intro d i hLoc
  obtain ⟨o, ho, hLeg, hCol⟩ := reconstructed_header_eq_isNormal_aux1 c hH K hK h hh d i hLoc
  have hPres := reconstructed_header_eq_isNormal_aux2 c hH K hK h hh d i hLoc o ho hLeg
  change (match c.port (c.form h.1) d i with | some o => K.col o.1 o.2 2 | none => 0) = _
  rw [ho]
  change K.col o.1 o.2 2 = _
  rw [← hCol]
  exact hPres

/-- Step 1 of the blueprint proof of `reconstructed_header_eq_isIdentityCorrect`: For an inner
nonprint side `d`, the first cell of `D` is its prescribed identity. -/
private lemma reconstructed_header_eq_isIdentityCorrect_step1_inner_nonprint (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (i : c.Side h.1)
    (hInner : c.IsInner (c.occ h.1 i)) (hNonprint : ¬ c.IsPrint (c.occ h.1 i)) :
    (reconstruct c K h.1).cell i 0 = identU c (c.edge (c.occ h.1 i)) := by
  sorry

/-- Step 2 of the blueprint proof of `reconstructed_header_eq_isIdentityCorrect`: For a print, the fifth cell of `D` is its prescribed identity. -/
private lemma reconstructed_header_eq_isIdentityCorrect_step2_print (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (i : c.Side h.1)
    (hPrint : c.IsPrint (c.occ h.1 i)) :
    (reconstruct c K h.1).cell i 4 = identU c (c.edge (c.occ h.1 i)) := by
  sorry

/-- Step 2 of the blueprint proof of `reconstructed_header_eq`: proving identity-correctness. -/
private lemma reconstructed_header_eq_isIdentityCorrect (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) :
    IsIdentityCorrect c (reconstruct c K h.1) := by
  intro i
  constructor
  · intro hInner hNonprint
    exact reconstructed_header_eq_isIdentityCorrect_step1_inner_nonprint c hH K hK h hh i hInner hNonprint
  · intro hPrint
    exact reconstructed_header_eq_isIdentityCorrect_step2_print c hH K hK h hh i hPrint

/-- Step 3 of the blueprint proof of `reconstructed_header_eq`: proving exact header. -/
private lemma reconstructed_header_eq_headerOf (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) :
    headerOf c (reconstruct c K h.1) = h := by
  sorry

/-- Step 4.1 of the blueprint proof of `reconstructed_header_eq_innerActive`:
for prints, the fifth cell is nonzero. -/
private lemma reconstructed_header_eq_innerActive_step1_print (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (i : c.Side h.1) (hi : c.IsInner (c.occ h.1 i)) (hp : c.IsPrint (c.occ h.1 i)) :
    (reconstruct c K h.1).cell i 4 ≠ 0 := by
  sorry

/-- Step 4.2 of the blueprint proof of `reconstructed_header_eq_innerActive`:
for nonprints, the fourth cell is nonzero. -/
private lemma reconstructed_header_eq_innerActive_step2_nonprint (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (i : c.Side h.1) (hi : c.IsInner (c.occ h.1 i)) (hnp : ¬ c.IsPrint (c.occ h.1 i)) :
    (reconstruct c K h.1).cell i 3 ≠ 0 := by
  sorry

/-- Step 4 of the blueprint proof of `reconstructed_header_eq`: inner sides are nontrivial. -/
private lemma reconstructed_header_eq_innerActive (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) :
    InnerActive c (reconstruct c K h.1) := by
  intro i hi
  unfold IsNontrivial
  by_cases hp : c.IsPrint (c.occ h.1 i)
  · have h1 := reconstructed_header_eq_innerActive_step1_print c hH K hK h hh i hi hp
    intro h_false
    exact h1 h_false.2
  · have h2 := reconstructed_header_eq_innerActive_step2_nonprint c hH K hK h hh i hi hp
    intro h_false
    exact h2 h_false.1

/-- `lem:comp/reconstruction`: the reconstructed parent `D` of type `t` (with
`D_i(d)` the third cell of port `i` on `σ'd`) is normal and
identity-correct, `H(D) = h`, and every inner side of `D` is nontrivial. -/
theorem reconstructed_header_eq (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) :
    IsNormal c (reconstruct c K h.1) ∧ IsIdentityCorrect c (reconstruct c K h.1) ∧
      headerOf c (reconstruct c K h.1) = h ∧ InnerActive c (reconstruct c K h.1) :=
  ⟨reconstructed_header_eq_isNormal c hH K hK h hh,
   reconstructed_header_eq_isIdentityCorrect c hH K hK h hh,
   reconstructed_header_eq_headerOf c hH K hK h hh,
   reconstructed_header_eq_innerActive c hH K hK h hh⟩

/-- Step 1 of the blueprint proof of `path_and_print_recovery`: every nonprint third signal
on `P_i(d)` equals `D_i(d)`. -/
private lemma path_and_print_recovery_step1_signals (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) :
    ∀ (d : c.Side h.1) (j : Fin 5) (o : c.SideOcc), o ∈ c.path (c.form h.1) d j →
      ¬ c.IsPrint o → K.col o.1 o.2 2 = (reconstruct c K h.1).cell d j := by
  sorry

/-- Step 2 of the blueprint proof of `path_and_print_recovery`: the noncentral (small)
owner of the print of `d` has first four cells `D_1(d), …, D_4(d)` on that print. -/
private lemma path_and_print_recovery_step2_prints (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) :
    ∀ d : c.Side h.1, c.marked (c.form h.1) d → ∀ k : Fin 5, k ≠ 4 →
      K.col (c.partner (c.printOcc (c.form h.1) d)).1 (c.partner (c.printOcc (c.form h.1) d)).2 k =
        (reconstruct c K h.1).cell d k := by
  sorry

/-- `lem:comp/signals`: every nonprint third signal on `P_i(d)` equals
`D_i(d)`, and the noncentral (small) owner of the print of `d` has first four
cells `D_1(d), …, D_4(d)` on that print. -/
theorem path_and_print_recovery (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) :
    (∀ (d : c.Side h.1) (j : Fin 5) (o : c.SideOcc), o ∈ c.path (c.form h.1) d j →
      ¬ c.IsPrint o → K.col o.1 o.2 2 = (reconstruct c K h.1).cell d j) ∧
    (∀ d : c.Side h.1, c.marked (c.form h.1) d → ∀ k : Fin 5, k ≠ 4 →
      K.col (c.partner (c.printOcc (c.form h.1) d)).1 (c.partner (c.printOcc (c.form h.1) d)).2 k =
        (reconstruct c K h.1).cell d k) := by
  exact ⟨path_and_print_recovery_step1_signals c hH K hK h hh,
    path_and_print_recovery_step2_prints c hH K hK h hh⟩

/-- Step 1 of the blueprint proof of `macroblock_is_decomposition`: noncentral tiles have
the required colours as a child of `D`. -/
private lemma macroblock_is_decomposition_noncentral (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (t : c.Typ)
    (ht_owner : c.owner t = K.α) (ht_nc : t ≠ c.central K.α) :
    IsChildOf c (reconstruct c K h.1) (K.tileOf t) := by
  sorry

/-- Step 1 of the blueprint proof of `macroblock_is_decomposition_central`: owner matches. -/
private lemma macroblock_is_decomposition_central_step1_owner (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (t : c.Typ)
    (ht_owner : c.owner t = K.α) (ht_c : t = c.central K.α) :
    c.owner (K.tileOf t).typ = c.form (reconstruct c K h.1).typ := by
  sorry

/-- Step 2 of the blueprint proof of `macroblock_is_decomposition_central`: prints are correct. -/
private lemma macroblock_is_decomposition_central_step2_prints (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (t : c.Typ)
    (ht_owner : c.owner t = K.α) (ht_c : t = c.central K.α) :
    ∀ i : c.Side (K.tileOf t).typ,
      ∀ d : c.Side (reconstruct c K h.1).typ,
        c.IsPrintOf (c.form (reconstruct c K h.1).typ) d (c.occ (K.tileOf t).typ i) →
        (∀ k : Fin 5, k ≠ 4 → (K.tileOf t).cell i k = (reconstruct c K h.1).cell d k) ∧
        (K.tileOf t).cell i 4 = identU c (c.edge (c.occ (K.tileOf t).typ i)) := by
  sorry

/-- Step 3 of the blueprint proof of `macroblock_is_decomposition_central`: nonprints. -/
private lemma macroblock_is_decomposition_central_step3_nonprints (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (t : c.Typ)
    (ht_owner : c.owner t = K.α) (ht_c : t = c.central K.α) :
    ∀ i : c.Side (K.tileOf t).typ,
      ¬ c.IsPrint (c.occ (K.tileOf t).typ i) →
        (K.tileOf t).cell i 0 = prescribedFirst c (c.occ (K.tileOf t).typ i) ∧
        (K.tileOf t).cell i 1 = 0 ∧
        (K.tileOf t).cell i 4 = 0 ∧
        (∀ (d : c.Side (reconstruct c K h.1).typ) (j : Fin 5),
          c.occ (K.tileOf t).typ i ∈ c.path (c.form (reconstruct c K h.1).typ) d j →
            (K.tileOf t).cell i 2 = (reconstruct c K h.1).cell d j) ∧
        ((∀ (d : c.Side (reconstruct c K h.1).typ) (j : Fin 5),
            c.occ (K.tileOf t).typ i ∉ c.path (c.form (reconstruct c K h.1).typ) d j) →
          (K.tileOf t).cell i 2 = 0) ∧
        (c.IsOuter (c.occ (K.tileOf t).typ i) → ∀ d : c.Side (reconstruct c K h.1).typ,
          c.occ (K.tileOf t).typ i ∈ c.outerList (c.form (reconstruct c K h.1).typ) d →
            (K.tileOf t).cell i 3 = if zA c (reconstruct c K h.1) d = true then 0
              else rankU c (c.rankOf (c.form (reconstruct c K h.1).typ) d (c.occ (K.tileOf t).typ i))) ∧
        (c.IsBoundary (c.occ (K.tileOf t).typ i) →
          (K.tileOf t).cell i 3 = headerU c (headerOf c (reconstruct c K h.1))) ∧
        (c.IsInner (c.occ (K.tileOf t).typ i) → ¬ c.IsBoundary (c.occ (K.tileOf t).typ i) →
          (K.tileOf t).cell i 3 = botU c) := by
  sorry

/-- Step 2 of the blueprint proof of `macroblock_is_decomposition`: the central tile has all
the required child cells and is an exact child of `D`. -/
private lemma macroblock_is_decomposition_central (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (t : c.Typ)
    (ht_owner : c.owner t = K.α) (ht_c : t = c.central K.α) :
    IsChildOf c (reconstruct c K h.1) (K.tileOf t) := by
  exact ⟨macroblock_is_decomposition_central_step1_owner c hH K hK h hh t ht_owner ht_c, fun i =>
    ⟨macroblock_is_decomposition_central_step2_prints c hH K hK h hh t ht_owner ht_c i,
     macroblock_is_decomposition_central_step3_nonprints c hH K hK h hh t ht_owner ht_c i⟩⟩

/-- `lem:comp/exact`: the finite patch `M` is an exact member of
`σ̂ D` for the reconstructed parent `D`. -/
theorem macroblock_is_decomposition (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) :
    IsExactBlockOf c K (reconstruct c K h.1) := by
  constructor
  · exact hh.1
  · intro t ht_owner
    by_cases ht : t = c.central K.α
    · exact macroblock_is_decomposition_central c hH K hK h hh t ht_owner ht
    · exact macroblock_is_decomposition_noncentral c hH K hK h hh t ht_owner ht

/-- `lem:comp/cyclic-legal`: if the centre `A` of `M` is legal and the type
`t` of `D` is cyclic, then `D = A` and `D` is legal. -/
theorem reconstructed_cyclic_legal (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hA : headerLegal c K.centre) (hcyc : c.IsCyclic h.1) :
    reconstruct c K h.1 = K.centre ∧ headerLegal c (reconstruct c K h.1) := by
  sorry

/-- Step 1 of the blueprint proof of `reconstructed_noncentral_legal_step1_ancestor`:
A legality chain of `A` with only central types would copy the marked first cell forever,
reaching a contradiction. -/
private lemma reconstructed_noncentral_legal_step1_ancestor_step1_not_all_central {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hnc : ¬ c.IsCentral h.1) (ch : ℕ → DecTile c) (hch0 : ch 0 = K.centre)
    (hch_child : ∀ i, IsChildOf c (ch (i + 1)) (ch i))
    (hleg : ∀ (n : ℕ) (i : c.Side (ch n).typ) (k : Fin 5),
      (copySource c (c.form (ch (n + 1)).typ) (c.occ (ch n).typ i) k).Nonempty →
      ¬ HasOrigin c ch n i k → (ch n).cell i k = 0) :
    ∃ n, ¬ c.IsCentral (ch n).typ := by sorry

/-- Step 2 of the blueprint proof of `reconstructed_noncentral_legal_step1_ancestor`:
Therefore the chain reaches a legal noncentral ancestor. -/
private lemma reconstructed_noncentral_legal_step1_ancestor_step2_min_n {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (ch : ℕ → DecTile c) (hch0 : ch 0 = K.centre)
    (hch_child : ∀ i, IsChildOf c (ch (i + 1)) (ch i))
    (hleg : ∀ (n : ℕ) (i : c.Side (ch n).typ) (k : Fin 5),
      (copySource c (c.form (ch (n + 1)).typ) (c.occ (ch n).typ i) k).Nonempty →
      ¬ HasOrigin c ch n i k → (ch n).cell i k = 0)
    (hn : ∃ n, ¬ c.IsCentral (ch n).typ) :
    ∃ E, headerLegal c E ∧ ¬ c.IsCentral E.typ ∧
      ∃ n, ∃ ch' : ℕ → DecTile c, ch' 0 = K.centre ∧ (∀ i, IsChildOf c (ch' (i + 1)) (ch' i)) ∧
        ch' n = E ∧ ∀ i < n, c.IsCentral (ch' i).typ := by sorry

/-- Step 1 of the blueprint proof of `reconstructed_noncentral_legal`: A legality chain
of `A` with only central types would copy the marked first cell forever ... Therefore the
chain reaches a legal noncentral ancestor. -/
private lemma reconstructed_noncentral_legal_step1_ancestor {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hA : headerLegal c K.centre) (hnc : ¬ c.IsCentral h.1) :
    ∃ E, headerLegal c E ∧ ¬ c.IsCentral E.typ ∧
      ∃ n, ∃ ch : ℕ → DecTile c, ch 0 = K.centre ∧ (∀ i, IsChildOf c (ch (i + 1)) (ch i)) ∧
        ch n = E ∧ ∀ i < n, c.IsCentral (ch i).typ := by
  have ⟨ch, hch0, hch_child, hleg⟩ := hA
  have hn := reconstructed_noncentral_legal_step1_ancestor_step1_not_all_central c hH K hK h hh hnc
    ch hch0 hch_child hleg
  exact reconstructed_noncentral_legal_step1_ancestor_step2_min_n c hH K hK ch hch0 hch_child
    hleg hn

/-- Step 2 of the blueprint proof of `reconstructed_noncentral_legal`: Choose a shortest
central-child chain ending at such an ancestor. ... Thus `A` has a legal noncentral
parent `E` immediately above it. -/
private lemma reconstructed_noncentral_legal_step2_parent {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hA : headerLegal c K.centre) (hnc : ¬ c.IsCentral h.1)
    (E_anc : DecTile c) (hE_leg : headerLegal c E_anc) (hE_nc : ¬ c.IsCentral E_anc.typ)
    (n : ℕ) (ch : ℕ → DecTile c) (hch0 : ch 0 = K.centre)
    (hch_child : ∀ i, IsChildOf c (ch (i + 1)) (ch i))
    (hch_end : ch n = E_anc) (hch_cent : ∀ i < n, c.IsCentral (ch i).typ) :
    ∃ E, headerLegal c E ∧ ¬ c.IsCentral E.typ ∧ IsChildOf c E K.centre := by sorry

/-- Step 1 of the blueprint proof of `reconstructed_noncentral_legal_step3_eq`: The parents `E,D`
have the same form. -/
private lemma reconstructed_noncentral_legal_step3_eq_step1_form {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hA : headerLegal c K.centre) (hnc : ¬ c.IsCentral h.1)
    (E : DecTile c) (hE_leg : headerLegal c E) (hE_nc : ¬ c.IsCentral E.typ)
    (hE_child : IsChildOf c E K.centre) :
    c.form E.typ = c.form h.1 := by sorry

/-- Step 2 of the blueprint proof of `reconstructed_noncentral_legal_step3_eq`: E and D types agree. -/
private lemma reconstructed_noncentral_legal_step3_eq_step2_type {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hA : headerLegal c K.centre) (hnc : ¬ c.IsCentral h.1)
    (E : DecTile c) (hE_leg : headerLegal c E) (hE_nc : ¬ c.IsCentral E.typ)
    (hE_child : IsChildOf c E K.centre)
    (h_form : c.form E.typ = c.form h.1) :
    E.typ = h.1 := by sorry

/-- Step 3 of the blueprint proof of `reconstructed_noncentral_legal_step3_eq`: E and D agree. -/
private lemma reconstructed_noncentral_legal_step3_eq_step3_eq {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hA : headerLegal c K.centre) (hnc : ¬ c.IsCentral h.1)
    (E : DecTile c) (hE_leg : headerLegal c E) (hE_nc : ¬ c.IsCentral E.typ)
    (hE_child : IsChildOf c E K.centre)
    (h_type : E.typ = h.1) :
    E = reconstruct c K h.1 := by sorry

/-- Step 3 of the blueprint proof of `reconstructed_noncentral_legal`: The parents `E,D`
have the same form. ... Hence `E=D`, and `D` is legal. -/
private lemma reconstructed_noncentral_legal_step3_eq {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hA : headerLegal c K.centre) (hnc : ¬ c.IsCentral h.1)
    (E : DecTile c) (hE_leg : headerLegal c E) (hE_nc : ¬ c.IsCentral E.typ)
    (hE_child : IsChildOf c E K.centre) :
    E = reconstruct c K h.1 := by
  have h1 := reconstructed_noncentral_legal_step3_eq_step1_form c hH K hK h hh hA hnc E hE_leg hE_nc hE_child
  have h2 := reconstructed_noncentral_legal_step3_eq_step2_type c hH K hK h hh hA hnc E hE_leg hE_nc hE_child h1
  exact reconstructed_noncentral_legal_step3_eq_step3_eq c hH K hK h hh hA hnc E hE_leg hE_nc hE_child h2

/-- `lem:comp/noncentral-legal`: if the centre `A` is legal and `t` is
noncentral, then `D` is legal. -/
theorem reconstructed_noncentral_legal (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hA : headerLegal c K.centre) (hnc : ¬ c.IsCentral h.1) :
    headerLegal c (reconstruct c K h.1) := by
  obtain ⟨E_anc, hE_anc_leg, hE_anc_nc, n, ch, hch0, hch_child, hch_end, hch_cent⟩ :=
    reconstructed_noncentral_legal_step1_ancestor c hH K hK h hh hA hnc
  obtain ⟨E, hE_leg, hE_nc, hE_child⟩ :=
    reconstructed_noncentral_legal_step2_parent c hH K hK h hh hA hnc E_anc hE_anc_leg hE_anc_nc
      n ch hch0 hch_child hch_end hch_cent
  have h_eq := reconstructed_noncentral_legal_step3_eq c hH K hK h hh hA hnc E hE_leg hE_nc hE_child
  rwa [← h_eq]

/-- Step 1 of the blueprint proof of `alignment_complete`: By tracing the
coinciding segments and using the mode-uniformity hypothesis to prevent the
opposing side from being longer, we find an opposing macroside `e` of block `j'`
that exactly shares the geometric macroside segment. -/
private lemma alignment_complete_step1_macroside_eq (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (part : MacroPartition c T)
    (j : part.ι) (d : Fin (c.Q.disk (part.block j).α).n)
    (hrank : RankMatched c part j d)
    (hmode : ∀ j' : part.ι, j' ≠ j → ∀ e, ModeUniform c (part.block j') e) :
    ∃ (j' : part.ι) (hneq : j' ≠ j) (e : Fin (c.Q.disk (part.block j').α).n),
      (part.block j').macroSide e = (part.block j).macroSide d := by
  sorry

/-- Step 2a of the blueprint proof of `alignment_complete_step2_subdivision_eq`: The length of
the child side subdivision is uniquely determined by the geometric macro side.
Thus coinciding macro sides have subdivisions of the same length. -/
private lemma alignment_complete_step2_subdivision_eq_step1_length (c : MacroCertificate P)
    (hH : c.Hereditary) (T : PlaneTiling (typedDecoration c)) (part : MacroPartition c T)
    (j j' : part.ι) (hneq : j' ≠ j)
    (d : Fin (c.Q.disk (part.block j).α).n) (e : Fin (c.Q.disk (part.block j').α).n)
    (hrank : RankMatched c part j d)
    (hmode : ∀ j'' : part.ι, j'' ≠ j → ∀ e'', ModeUniform c (part.block j'') e'')
    (hmacro : (part.block j').macroSide e = (part.block j).macroSide d) :
    (c.outerList (part.block j).α d).length = (c.outerList (part.block j').α e).length := by
  sorry

/-- Step 2b of the blueprint proof of `alignment_complete_step2_subdivision_eq`: Once the geometric
macrosides coincide and their child side subdivisions have the same length,
their child sides correspond exactly in geometry pointwise. -/
private lemma alignment_complete_step2_subdivision_eq_step2_pointwise (c : MacroCertificate P)
    (hH : c.Hereditary) (T : PlaneTiling (typedDecoration c)) (part : MacroPartition c T)
    (j j' : part.ι) (hneq : j' ≠ j)
    (d : Fin (c.Q.disk (part.block j).α).n) (e : Fin (c.Q.disk (part.block j').α).n)
    (hrank : RankMatched c part j d)
    (hmode : ∀ j'' : part.ι, j'' ≠ j → ∀ e'', ModeUniform c (part.block j'') e'')
    (hmacro : (part.block j').macroSide e = (part.block j).macroSide d)
    (hlen : (c.outerList (part.block j).α d).length = (c.outerList (part.block j').α e).length)
    (k : ℕ) (hk : k < (c.outerList (part.block j).α d).length)
    (hk' : k < (c.outerList (part.block j').α e).length) :
    (part.block j).childSide ((c.outerList (part.block j).α d).get ⟨k, hk⟩) =
    (part.block j').childSide ((c.outerList (part.block j').α e).get ⟨k, hk'⟩) := by
  sorry

/-- Step 2 of the blueprint proof of `alignment_complete`: Complete child-side
matching identifies the whole ordered subdivision. Once the geometric
macrosides coincide, the child sides of the two blocks correspond exactly in
order and geometry. -/
private lemma alignment_complete_step2_subdivision_eq (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (part : MacroPartition c T)
    (j j' : part.ι) (hneq : j' ≠ j)
    (d : Fin (c.Q.disk (part.block j).α).n) (e : Fin (c.Q.disk (part.block j').α).n)
    (hrank : RankMatched c part j d)
    (hmode : ∀ j'' : part.ι, j'' ≠ j → ∀ e'', ModeUniform c (part.block j'') e'')
    (hmacro : (part.block j').macroSide e = (part.block j).macroSide d) :
    List.Forall₂ (fun o o' => (part.block j).childSide o = (part.block j').childSide o')
      (c.outerList (part.block j).α d) (c.outerList (part.block j').α e) := by
  rw [List.forall₂_iff_get]
  have hlen := alignment_complete_step2_subdivision_eq_step1_length c hH T part j j' hneq d e
    hrank hmode hmacro
  refine ⟨hlen, fun k hk hk' => ?_⟩
  exact alignment_complete_step2_subdivision_eq_step2_pointwise c hH T part j j' hneq d e hrank
    hmode hmacro hlen k hk hk'

/-- `lem:comp/alignment` (with the review's mode-uniformity hypothesis): in a
plane partition into macroblocks, if every child side of the macroside `d`
of block `j` has a complete opposing side with the same positive rank, and
every macroside of every other block is mode-uniform, then `d` has a
complete opposing macroside with the same ordered subdivision. -/
theorem alignment_complete (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (part : MacroPartition c T)
    (j : part.ι) (d : Fin (c.Q.disk (part.block j).α).n)
    (hrank : RankMatched c part j d)
    (hmode : ∀ j' : part.ι, j' ≠ j → ∀ e, ModeUniform c (part.block j') e) :
    OpposingMacroside c part j d := by
  obtain ⟨j', hneq, e, hmacro⟩ :=
    alignment_complete_step1_macroside_eq c hH T part j d hrank hmode
  refine ⟨j', hneq, e, hmacro, ?_⟩
  exact alignment_complete_step2_subdivision_eq c hH T part j j' hneq d e hrank hmode hmacro

/-- Step 1 of the blueprint proof of `composed_proper`: reconstruction gives a plane tiling. -/
private lemma composed_proper_step1_reconstruction (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (part : MacroPartition c T) :
    ∃ T' : PlaneTiling (typedDecoration c), IsReconstruction c part T' := by
  have _ := hH
  sorry

/-- Step 2 of the blueprint proof of `composed_proper`: exact repaired decomposition follows
block by block. -/
private lemma composed_proper_step2_exact (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X)) (part : MacroPartition c T)
    (T' : PlaneTiling (typedDecoration c)) (hrec : IsReconstruction c part T') :
    IsExactComposition c T' T := by
  have _ := hH; have _ := hT; have _ := hL; have _ := hrec
  sorry

/-- Step 3 of the blueprint proof of `composed_proper`: normality, identity-correctness,
and activity of inner sides. -/
private lemma composed_proper_step3_properties (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X)) (part : MacroPartition c T)
    (T' : PlaneTiling (typedDecoration c)) (hrec : IsReconstruction c part T') :
    ∀ X ∈ T'.tiles, IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
      InnerActive c (tileDec X) := by
  have _ := hH; have _ := hT; have _ := hL; have _ := hrec
  sorry

/-- Step 4 of the blueprint proof of `composed_proper`: the resulting tiling is proper. -/
private lemma composed_proper_step4_proper (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X)) (part : MacroPartition c T)
    (T' : PlaneTiling (typedDecoration c)) (hrec : IsReconstruction c part T') :
    IsProper c T' := by
  have _ := hH; have _ := hT; have _ := hL; have _ := hrec
  sorry

/-- `lem:comp/proper`: for a proper legal plane tiling `T`, replacing each
assembled macroblock by its reconstructed parent and scaling down gives a
proper tiling `T'` of normal identity-correct decorations with active inner
sides, and `T` is an exact repaired decomposition of `T'`. -/
theorem composed_proper (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X)) :
    ∃ (part : MacroPartition c T) (T' : PlaneTiling (typedDecoration c)),
      IsReconstruction c part T' ∧ IsProper c T' ∧
      (∀ X ∈ T'.tiles, IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
        InnerActive c (tileDec X)) ∧
      IsExactComposition c T' T := by
  have ⟨part⟩ := assembleMacrotemplates_of_legal c hH T hT hL
  have ⟨T', hrec⟩ := composed_proper_step1_reconstruction c hH T part
  exact ⟨part, T', hrec,
    composed_proper_step4_proper c hH T hT hL part T' hrec,
    composed_proper_step3_properties c hH T hT hL part T' hrec,
    composed_proper_step2_exact c hH T hT hL part T' hrec⟩

/-- Step 1 of the blueprint proof of `reconstructed_acyclic_legal`: 
If a block is in the exact decomposition, it is a proper realization and all its
noncentral tiles are legal. -/
private lemma reconstructed_acyclic_legal_step1_block_context {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (part : MacroPartition c T) (T' : PlaneTiling (typedDecoration c))
    (hex : IsExactComposition c T' T)
    (j : part.ι) :
    BlockContext c (part.block j) := by
  have _ := hH; have _ := hT; have _ := hL; have _ := T'; have _ := hex
  sorry

/-- Step 2 of the blueprint proof of `reconstructed_acyclic_legal`: 
Every noncentral tile of `T'` is already legal. -/
private lemma reconstructed_acyclic_legal_step2_noncentral {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (part : MacroPartition c T) (T' : PlaneTiling (typedDecoration c))
    (hrec : IsReconstruction c part T') (hT' : IsProper c T')
    (hN : ∀ X ∈ T'.tiles, IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
      InnerActive c (tileDec X))
    (hex : IsExactComposition c T' T)
    (Y : PlacedTile (typedDecoration c)) (hY : Y ∈ T'.tiles)
    (hnc : ¬ c.IsCentral (tileDec Y).typ)
    (hctx : ∀ j, BlockContext c (part.block j)) :
    headerLegal c (tileDec Y) := by
  have _ := hH; have _ := hT; have _ := hL; have _ := hrec; have _ := hT'; have _ := hN
  have _ := hex; have _ := hY; have _ := hnc; have _ := hctx
  sorry

/-- Step 3 of the blueprint proof of `reconstructed_acyclic_legal`:
Every cyclic tile of `T'` is already legal. -/
private lemma reconstructed_acyclic_legal_step3_cyclic {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (part : MacroPartition c T) (T' : PlaneTiling (typedDecoration c))
    (hrec : IsReconstruction c part T') (hT' : IsProper c T')
    (hN : ∀ X ∈ T'.tiles, IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
      InnerActive c (tileDec X))
    (hex : IsExactComposition c T' T)
    (Y : PlacedTile (typedDecoration c)) (hY : Y ∈ T'.tiles)
    (hcyc : c.IsCyclic (tileDec Y).typ)
    (hctx : ∀ j, BlockContext c (part.block j)) :
    headerLegal c (tileDec Y) := by
  have _ := hH; have _ := hT; have _ := hL; have _ := hrec; have _ := hT'; have _ := hN
  have _ := hex; have _ := hY; have _ := hcyc; have _ := hctx
  sorry

/-- Step 4 of the blueprint proof of `reconstructed_acyclic_legal`:
Applying the full repaired reconstruction and exactness lemmas gives a normal
parent $C$ of type $r$, with $D$ its central child. -/
private lemma reconstructed_acyclic_legal_step4_parent {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (part : MacroPartition c T) (T' : PlaneTiling (typedDecoration c))
    (hrec : IsReconstruction c part T') (hT' : IsProper c T')
    (hN : ∀ X ∈ T'.tiles, IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
      InnerActive c (tileDec X))
    (hex : IsExactComposition c T' T)
    (X : PlacedTile (typedDecoration c)) (hX : X ∈ T'.tiles)
    (hctx : ∀ j, BlockContext c (part.block j)) :
    ∃ (j : part.ι) (h : HeaderKernel.Header c.Typ c.Side),
      CommonHeader c (part.block j) h ∧
      tileDec X = reconstruct c (part.block j) (tileDec X).typ ∧
      IsExactBlockOf c (part.block j) (reconstruct c (part.block j) h.1) ∧
      IsNormal c (reconstruct c (part.block j) h.1) := by
  have _ := hH; have _ := hT; have _ := hL; have _ := hrec; have _ := hT'; have _ := hN
  have _ := hex; have _ := hX; have _ := hctx
  sorry

/-- Step 5 of the blueprint proof of `reconstructed_acyclic_legal`:
The type $r$ of $C$ is noncentral. If it were central, it and its central
child $t$ would have the same large form, making $t$ cyclic, contradicting
the assumption on $D$. -/
private lemma reconstructed_acyclic_legal_step5_parent_noncentral {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (part : MacroPartition c T) (T' : PlaneTiling (typedDecoration c))
    (hrec : IsReconstruction c part T') (hT' : IsProper c T')
    (hN : ∀ X ∈ T'.tiles, IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
      InnerActive c (tileDec X))
    (hex : IsExactComposition c T' T)
    (X : PlacedTile (typedDecoration c)) (hX : X ∈ T'.tiles)
    (hcent : c.IsCentral (tileDec X).typ) (hcyc : ¬ c.IsCyclic (tileDec X).typ)
    (j : part.ι) (h : HeaderKernel.Header c.Typ c.Side)
    (hh : CommonHeader c (part.block j) h)
    (heq : tileDec X = reconstruct c (part.block j) (tileDec X).typ) :
    ¬ c.IsCentral h.1 := by
  have _ := hH; have _ := hT; have _ := hL; have _ := hrec; have _ := hT'; have _ := hN
  have _ := hex; have _ := hX; have _ := hcent; have _ := hcyc; have _ := hh; have _ := heq
  sorry

/-- Step 6 of the blueprint proof of `reconstructed_acyclic_legal`:
The central acyclic reconstructed parent is legal because its ancestry
chain reaches a noncentral type. -/
private lemma reconstructed_acyclic_legal_step6_main {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (part : MacroPartition c T) (T' : PlaneTiling (typedDecoration c))
    (hrec : IsReconstruction c part T') (hT' : IsProper c T')
    (hN : ∀ X ∈ T'.tiles, IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
      InnerActive c (tileDec X))
    (hex : IsExactComposition c T' T)
    (X : PlacedTile (typedDecoration c)) (hX : X ∈ T'.tiles)
    (hcent : c.IsCentral (tileDec X).typ) (hcyc : ¬ c.IsCyclic (tileDec X).typ)
    (j : part.ι) (h : HeaderKernel.Header c.Typ c.Side)
    (hh : CommonHeader c (part.block j) h)
    (h_parent_nc : ¬ c.IsCentral h.1)
    (heq : tileDec X = reconstruct c (part.block j) (tileDec X).typ)
    (hctx : BlockContext c (part.block j))
    (h_other_nc : ∀ Y ∈ T'.tiles, ¬ c.IsCentral (tileDec Y).typ → headerLegal c (tileDec Y))
    (h_other_cyc : ∀ Y ∈ T'.tiles, c.IsCyclic (tileDec Y).typ → headerLegal c (tileDec Y)) :
    headerLegal c (tileDec X) := by
  have _ := hH; have _ := hT; have _ := hL; have _ := hrec; have _ := hT'; have _ := hN
  have _ := hex; have _ := hX; have _ := hcent; have _ := hcyc; have _ := hh
  have _ := h_parent_nc; have _ := heq; have _ := hctx; have _ := h_other_nc; have _ := h_other_cyc
  sorry

/-- `lem:comp/acyclic-legal`: every reconstructed parent of central acyclic
type in `T'` is legal. -/
theorem reconstructed_acyclic_legal (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (part : MacroPartition c T) (T' : PlaneTiling (typedDecoration c))
    (hrec : IsReconstruction c part T') (hT' : IsProper c T')
    (hN : ∀ X ∈ T'.tiles, IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
      InnerActive c (tileDec X))
    (hex : IsExactComposition c T' T) :
    ∀ X ∈ T'.tiles, c.IsCentral (tileDec X).typ → ¬ c.IsCyclic (tileDec X).typ →
      headerLegal c (tileDec X) := by
  intro X hX hcent hcyc
  have hctx : ∀ j, BlockContext c (part.block j) :=
    reconstructed_acyclic_legal_step1_block_context c hH T hT hL part T' hex
  have hparent := reconstructed_acyclic_legal_step4_parent c hH T hT hL part T' hrec hT' hN hex
    X hX hctx
  rcases hparent with ⟨j, h, hh, heq, _hexact, _hnorm⟩
  have h_parent_nc := reconstructed_acyclic_legal_step5_parent_noncentral c hH T hT hL part T'
    hrec hT' hN hex X hX hcent hcyc j h hh heq
  have h_other_nc : ∀ Y ∈ T'.tiles, ¬ c.IsCentral (tileDec Y).typ → headerLegal c (tileDec Y) :=
    fun Y hY hnc => reconstructed_acyclic_legal_step2_noncentral c hH T hT hL part T' hrec hT'
      hN hex Y hY hnc hctx
  have h_other_cyc : ∀ Y ∈ T'.tiles, c.IsCyclic (tileDec Y).typ → headerLegal c (tileDec Y) :=
    fun Y hY hcyc' => reconstructed_acyclic_legal_step3_cyclic c hH T hT hL part T' hrec hT'
      hN hex Y hY hcyc' hctx
  exact reconstructed_acyclic_legal_step6_main c hH T hT hL part T' hrec hT' hN hex X hX hcent
    hcyc j h hh h_parent_nc heq (hctx j) h_other_nc h_other_cyc

/-- `thm:compose` (the repaired composition theorem): for a macrotemplate
system with a certificate and hereditary listed sides, every proper legal
plane tiling has a proper exact repaired composition whose tiles are
legal. -/
theorem compose_legal_exists (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X)) :
    ∃ T' : PlaneTiling (typedDecoration c), IsProper c T' ∧
      (∀ X ∈ T'.tiles, headerLegal c (tileDec X)) ∧ IsExactComposition c T' T := by
  sorry

/-- The side-to-side-supertiling hypothesis of `lem:lift-hierarchy` for a
given `σ'` hierarchy: every finite supertile `σ'^n X`, `X` a tile of level
`n`, is side-to-side. -/
def HierarchySupertilesSTS (c : MacroCertificate P) (seq : ℕ → PlaneTiling c.Q) : Prop :=
  ∀ n, ∀ X ∈ (seq n).tiles, SideToSideSet (c.σ.decomposeIter n {X})

/-- Step 1 of the blueprint proof of `lift_hierarchy`: construct the compatible legal
decorations for the hierarchy. -/
private lemma lift_hierarchy_step1_decorations (c : MacroCertificate P) (hH : c.Hereditary)
    (seq : ℕ → PlaneTiling c.Q) (hseq : ∀ n, c.σ.IsComposition (seq (n + 1)) (seq n))
    (hsts : HierarchySupertilesSTS c seq) :
    ∃ seq' : ℕ → PlaneTiling (typedDecoration c),
      (∀ n, eraseSet c (seq' n).tiles = (seq n).tiles) ∧
      (∀ n, IsExactComposition c (seq' (n + 1)) (seq' n)) ∧
      (∀ n, ∀ X ∈ (seq' n).tiles, headerLegal c (tileDec X)) := by
  sorry

/-- Step 2.1 of the blueprint proof of `lift_hierarchy_step2_proper`: inner sides match. -/
private lemma lift_hierarchy_step2_proper_step1_inner (c : MacroCertificate P) (hH : c.Hereditary)
    (seq : ℕ → PlaneTiling c.Q) (hsts : HierarchySupertilesSTS c seq)
    (seq' : ℕ → PlaneTiling (typedDecoration c))
    (herase : ∀ n, eraseSet c (seq' n).tiles = (seq n).tiles)
    (hexact : ∀ n, IsExactComposition c (seq' (n + 1)) (seq' n))
    (hleg : ∀ n, ∀ X ∈ (seq' n).tiles, headerLegal c (tileDec X))
    (X : PlacedTile (typedDecoration c)) (hX : X ∈ (seq' 0).tiles)
    (i : c.Side (tileDec X).typ) (hInner : c.IsInner (c.occ (tileDec X).typ i))
    (hNontriv : IsNontrivial c (tileDec X) i) :
    ∃ Y ∈ (seq' 0).tiles, Y ≠ X ∧ ∃ j : c.Side (tileDec Y).typ,
      sideOf c Y j = sideOf c X i ∧ ∀ k : Fin 5, (tileDec Y).cell j k = (tileDec X).cell i k := by
  sorry

/-- Step 2.2 of the blueprint proof of `lift_hierarchy_step2_proper`: outer sides match. -/
private lemma lift_hierarchy_step2_proper_step2_outer (c : MacroCertificate P) (hH : c.Hereditary)
    (seq : ℕ → PlaneTiling c.Q) (hsts : HierarchySupertilesSTS c seq)
    (seq' : ℕ → PlaneTiling (typedDecoration c))
    (herase : ∀ n, eraseSet c (seq' n).tiles = (seq n).tiles)
    (hexact : ∀ n, IsExactComposition c (seq' (n + 1)) (seq' n))
    (hleg : ∀ n, ∀ X ∈ (seq' n).tiles, headerLegal c (tileDec X))
    (X : PlacedTile (typedDecoration c)) (hX : X ∈ (seq' 0).tiles)
    (i : c.Side (tileDec X).typ) (hOuter : c.IsOuter (c.occ (tileDec X).typ i))
    (hNontriv : IsNontrivial c (tileDec X) i) :
    ∃ Y ∈ (seq' 0).tiles, Y ≠ X ∧ ∃ j : c.Side (tileDec Y).typ,
      sideOf c Y j = sideOf c X i ∧ ∀ k : Fin 5, (tileDec Y).cell j k = (tileDec X).cell i k := by
  sorry

/-- Step 2 of the blueprint proof of `lift_hierarchy`: properness holds at level zero. -/
private lemma lift_hierarchy_step2_proper (c : MacroCertificate P) (hH : c.Hereditary)
    (seq : ℕ → PlaneTiling c.Q) (hsts : HierarchySupertilesSTS c seq)
    (seq' : ℕ → PlaneTiling (typedDecoration c))
    (herase : ∀ n, eraseSet c (seq' n).tiles = (seq n).tiles)
    (hexact : ∀ n, IsExactComposition c (seq' (n + 1)) (seq' n))
    (hleg : ∀ n, ∀ X ∈ (seq' n).tiles, headerLegal c (tileDec X)) :
    IsProper c (seq' 0) := by
  intro X hX i hNontriv
  by_cases hOuter : c.IsOuter (c.occ (tileDec X).typ i)
  · exact lift_hierarchy_step2_proper_step2_outer c hH seq hsts seq' herase hexact hleg X hX i
      hOuter hNontriv
  · exact lift_hierarchy_step2_proper_step1_inner c hH seq hsts seq' herase hexact hleg X hX i
      hOuter hNontriv

/-- `lem:lift-hierarchy`: with hereditary listed sides, an actual `σ'`
hierarchy whose finite supertiles are side-to-side admits compatible legal
decorations at every level under the repaired substitution, and its
decorated level-zero tiling is proper. -/
theorem lift_hierarchy (c : MacroCertificate P) (hH : c.Hereditary)
    (seq : ℕ → PlaneTiling c.Q) (hseq : ∀ n, c.σ.IsComposition (seq (n + 1)) (seq n))
    (hsts : HierarchySupertilesSTS c seq) :
    ∃ seq' : ℕ → PlaneTiling (typedDecoration c),
      (∀ n, eraseSet c (seq' n).tiles = (seq n).tiles) ∧
      (∀ n, IsExactComposition c (seq' (n + 1)) (seq' n)) ∧
      (∀ n, ∀ X ∈ (seq' n).tiles, headerLegal c (tileDec X)) ∧
      IsProper c (seq' 0) := by
  rcases lift_hierarchy_step1_decorations c hH seq hseq hsts with ⟨seq', herase, hexact, hleg⟩
  exact ⟨seq', herase, hexact, hleg,
    lift_hierarchy_step2_proper c hH seq hsts seq' herase hexact hleg⟩

/-- Step 1 of the blueprint proof of `projects_to_hierarchy`: repeated composition
yields a hierarchical tiling. -/
private lemma projects_to_hierarchy_step1_soundness (c : MacroCertificate P) (hH : c.Hereditary) :
    ∀ T : PlaneTiling (typedDecoration c), IsProper c T →
      (∀ X ∈ T.tiles, headerLegal c (tileDec X)) →
      ∃ T₀ : PlaneTiling c.Q, T₀.tiles = eraseSet c T.tiles ∧ c.σ.IsHierarchical T₀ := by
  sorry

/-- Step 2 of the blueprint proof of `projects_to_hierarchy`: lifting an actual
hierarchy gives a legal decorated proper tiling. -/
private lemma projects_to_hierarchy_step2_completeness (c : MacroCertificate P)
    (hH : c.Hereditary) :
    ∀ T₀ : PlaneTiling c.Q,
      (∃ seq : ℕ → PlaneTiling c.Q, seq 0 = T₀ ∧
        (∀ n, c.σ.IsComposition (seq (n + 1)) (seq n)) ∧ HierarchySupertilesSTS c seq) →
      ∃ T : PlaneTiling (typedDecoration c), IsProper c T ∧
        (∀ X ∈ T.tiles, headerLegal c (tileDec X)) ∧ eraseSet c T.tiles = T₀.tiles := by
  sorry

/-- Step 3 of the blueprint proof of `projects_to_hierarchy`: finiteness of the
legal decorated tile alphabet. -/
private lemma projects_to_hierarchy_step3_finite (c : MacroCertificate P) (hH : c.Hereditary) :
    {A : DecTile c | headerLegal c A}.Finite := by
  sorry

/-- `thm:comp/soundness`: with hereditary listed sides, erasing the colours
of every proper legal tiling gives a `σ'`-hierarchical tiling; conversely
every `σ'` hierarchy with side-to-side finite supertiles is the erasure of a
proper legal tiling; and the set of legal decorated tiles is finite. -/
theorem projects_to_hierarchy (c : MacroCertificate P) (hH : c.Hereditary) :
    (∀ T : PlaneTiling (typedDecoration c), IsProper c T →
      (∀ X ∈ T.tiles, headerLegal c (tileDec X)) →
      ∃ T₀ : PlaneTiling c.Q, T₀.tiles = eraseSet c T.tiles ∧ c.σ.IsHierarchical T₀) ∧
    (∀ T₀ : PlaneTiling c.Q,
      (∃ seq : ℕ → PlaneTiling c.Q, seq 0 = T₀ ∧
        (∀ n, c.σ.IsComposition (seq (n + 1)) (seq n)) ∧ HierarchySupertilesSTS c seq) →
      ∃ T : PlaneTiling (typedDecoration c), IsProper c T ∧
        (∀ X ∈ T.tiles, headerLegal c (tileDec X)) ∧ eraseSet c T.tiles = T₀.tiles) ∧
    {A : DecTile c | headerLegal c A}.Finite := by
  exact ⟨projects_to_hierarchy_step1_soundness c hH,
         projects_to_hierarchy_step2_completeness c hH,
         projects_to_hierarchy_step3_finite c hH⟩

end Planned

end Tilings

end
