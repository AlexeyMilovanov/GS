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

/-- `lem:comp/outer-boundary`: in a macrotemplate every child type with an
outer side also has a boundary side. -/
theorem boundary_side_of_outer_side (c : MacroCertificate P) (hH : c.Hereditary)
    (t : c.Typ) (i : c.Side t) (hi : c.IsOuter (c.occ t i)) :
    ∃ j : c.Side t, c.IsBoundary (c.occ t j) := by
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
  sorry

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

/-- `lem:comp/boundary-header`: in a proper finite coloured realization of
`σ' α` whose noncentral tiles are legal, every boundary fourth cell carries
the same header `h = (t, v)`, and `form t = α`. -/
theorem boundary_header_constant (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K) :
    ∃ h : HeaderKernel.Header c.Typ c.Side, CommonHeader c K h := by
  sorry

/-- `lem:comp/reconstruction`: the reconstructed parent `D` of type `t` (with
`D_i(d)` the third cell of port `i` on `σ'd`) is normal and
identity-correct, `H(D) = h`, and every inner side of `D` is nontrivial. -/
theorem reconstructed_header_eq (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) :
    IsNormal c (reconstruct c K h.1) ∧ IsIdentityCorrect c (reconstruct c K h.1) ∧
      headerOf c (reconstruct c K h.1) = h ∧ InnerActive c (reconstruct c K h.1) := by
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
  sorry

/-- `lem:comp/exact`: the finite patch `M` is an exact member of
`σ̂ D` for the reconstructed parent `D`. -/
theorem macroblock_is_decomposition (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) :
    IsExactBlockOf c K (reconstruct c K h.1) := by
  sorry

/-- `lem:comp/cyclic-legal`: if the centre `A` of `M` is legal and the type
`t` of `D` is cyclic, then `D = A` and `D` is legal. -/
theorem reconstructed_cyclic_legal (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hA : headerLegal c K.centre) (hcyc : c.IsCyclic h.1) :
    reconstruct c K h.1 = K.centre ∧ headerLegal c (reconstruct c K h.1) := by
  sorry

/-- `lem:comp/noncentral-legal`: if the centre `A` is legal and `t` is
noncentral, then `D` is legal. -/
theorem reconstructed_noncentral_legal (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hA : headerLegal c K.centre) (hnc : ¬ c.IsCentral h.1) :
    headerLegal c (reconstruct c K h.1) := by
  sorry

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
  sorry

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
  sorry

end Planned

end Tilings

end
