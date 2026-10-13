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

/-- Step 1 of the blueprint proof of `headerLegal_properties_step2_normal_id`:
a legal tile is normal. -/
private lemma headerLegal_properties_step2_normal_id_step1_normal (c : MacroCertificate P)
    (A : DecTile c) (C : DecTile c) (h : IsChildOf c C A) :
    IsNormal c A := by
  sorry

/-- Step 2 of the blueprint proof of `headerLegal_properties_step2_normal_id`:
a legal tile is identity-correct. -/
private lemma headerLegal_properties_step2_normal_id_step2_identity (c : MacroCertificate P)
    (A : DecTile c) (C : DecTile c) (h : IsChildOf c C A) :
    IsIdentityCorrect c A := by
  sorry

/-- Step 2 of the blueprint proof of `headerLegal_properties`: a legal tile is normal and
identity-correct. -/
private lemma headerLegal_properties_step2_normal_id (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    IsNormal c A ∧ IsIdentityCorrect c A := by
  have _ := hH
  rcases hA with ⟨ch, hch_init, hch_succ, _⟩
  have h_succ_0 := hch_succ 0
  have h_succ_0' : IsChildOf c (ch 1) A := by
    rw [←hch_init]
    exact h_succ_0
  exact ⟨headerLegal_properties_step2_normal_id_step1_normal c A (ch 1) h_succ_0',
    headerLegal_properties_step2_normal_id_step2_identity c A (ch 1) h_succ_0'⟩


/-- Step 1 of the blueprint proof of `headerLegal_properties_step3_child`: A copied cell in the
new first tile either reaches an origin there, or reaches the corresponding parent cell. If the
source chain is infinite, the parent's legality forces its value, and hence the child's value, to
be zero. -/
private lemma headerLegal_properties_step3_child_step1_zero (c : MacroCertificate P)
    (hH : c.Hereditary)
    (A B : DecTile c) (hB : IsChildOf c A B)
    (ch : ℕ → DecTile c) (hch0 : ch 0 = A)
    (hch_orig : ∀ n i k, (copySource c (c.form (ch (n + 1)).typ) (c.occ (ch n).typ i) k).Nonempty →
      ¬ HasOrigin c ch n i k → (ch n).cell i k = 0) :
    ∀ (i : c.Side B.typ) (k : Fin 5),
      (copySource c (c.form (ch 0).typ) (c.occ B.typ i) k).Nonempty →
      ¬ HasOrigin c (fun n => match n with | 0 => B | n + 1 => ch n) 0 i k →
      B.cell i k = 0 := by
  sorry

/-- Step 3 of the blueprint proof of `headerLegal_properties`: every child of a legal parent is
legal. -/
private lemma headerLegal_properties_step3_child (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    ∀ B, IsChildOf c A B → headerLegal c B := by
  intro B hB
  dsimp [headerLegal, IsLegalWith] at *
  rcases hA with ⟨ch, hch0, hch_rel, hch_orig⟩
  let new_ch := fun n => match n with
    | 0 => B
    | n + 1 => ch n
  use new_ch
  constructor
  · rfl
  · constructor
    · intro n
      cases n
      · dsimp [new_ch]
        rw [hch0]
        exact hB
      · dsimp [new_ch]
        exact hch_rel _
    · intro n i k h_nonempty h_no_origin
      cases n
      · exact headerLegal_properties_step3_child_step1_zero c hH A B hB ch hch0 hch_orig i k h_nonempty h_no_origin
      · dsimp [new_ch] at h_nonempty h_no_origin ⊢
        apply hch_orig
        · exact h_nonempty
        · intro h_orig_ch
          apply h_no_origin
          have : ∀ m j l, HasOrigin c ch m j l → HasOrigin c new_ch (m + 1) j l := by
            intro m j l h_orig
            induction h_orig
            case origin m' j' l' h_eq =>
              exact HasOrigin.origin _ _ _ h_eq
            case step m' j' l' d l'' h_mem h_orig ih =>
              exact HasOrigin.step _ _ _ _ _ h_mem ih
          exact this _ _ _ h_orig_ch

/-- Step 4 of the blueprint proof of `headerLegal_properties`: all boundary fourth cells of a legal
tile equal one parent header. -/
private lemma headerLegal_properties_step4_boundary (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    ∃ C, headerLegal c C ∧ IsChildOf c C A ∧
      ∀ i : c.Side A.typ, c.IsBoundary (c.occ A.typ i) → A.cell i 3 = headerU c (headerOf c C) := by
  sorry

/-- Step 1 of the blueprint proof of `headerLegal_properties_step5_path`: paths are invariant under form casting. -/
private lemma headerLegal_properties_step5_path_step1_cast_path (c : MacroCertificate P) (hH : c.Hereditary)
    {F1 F2 : c.Q.Form} (h : F1 = F2) (d : Fin (c.Q.disk F1).n) (j : Fin 5) (occ : c.SideOcc) :
    occ ∈ c.path F1 d j ↔ occ ∈ c.path F2 (cast (congrArg (fun F => Fin (c.Q.disk F).n) h) d) j := by
  have _ := hH
  subst h
  rfl

/-- Step 5 of the blueprint proof of `headerLegal_properties`: third signals belonging to the same
path are equal through a legal tile. -/
private lemma headerLegal_properties_step5_path (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    ∀ (d : Fin (c.Q.disk (c.owner A.typ)).n) (j : Fin 5) (i i' : c.Side A.typ),
      c.occ A.typ i ∈ c.path (c.owner A.typ) d j → c.occ A.typ i' ∈ c.path (c.owner A.typ) d j →
      ¬ c.IsPrint (c.occ A.typ i) → ¬ c.IsPrint (c.occ A.typ i') → A.cell i 2 = A.cell i' 2 := by
  intro d j i i' hi hi' hnp hnp'
  rcases hA with ⟨ch, hch0, hch_child, _⟩
  have h_child_A : IsChildOf c (ch 1) A := by
    have h1 := hch_child 0
    rw [hch0] at h1
    exact h1
  have hd_eq : c.owner A.typ = c.form (ch 1).typ := h_child_A.1
  let d_cast : Fin (c.Q.disk (c.form (ch 1).typ)).n := cast (congrArg (fun F => Fin (c.Q.disk F).n) hd_eq) d
  have h1 : A.cell i 2 = (ch 1).cell d_cast j := by
    have h_child_A_with_i := h_child_A.2 i
    have h_np_i := (h_child_A_with_i.2 hnp).2.2.2.1 d_cast j
    have hi_cast : c.occ A.typ i ∈ c.path (c.form (ch 1).typ) d_cast j := by
      rwa [← headerLegal_properties_step5_path_step1_cast_path c hH hd_eq d j]
    exact h_np_i hi_cast
  have h2 : A.cell i' 2 = (ch 1).cell d_cast j := by
    have h_child_A_with_i' := h_child_A.2 i'
    have h_np_i' := (h_child_A_with_i'.2 hnp').2.2.2.1 d_cast j
    have hi_cast' : c.occ A.typ i' ∈ c.path (c.form (ch 1).typ) d_cast j := by
      rwa [← headerLegal_properties_step5_path_step1_cast_path c hH hd_eq d j]
    exact h_np_i' hi_cast'
  rw [h1, h2]

/-- Step 1 of the blueprint proof of `headerLegal_properties_step6_inner`: at a print, the fifth
cell is a nonzero interface identity. -/
private lemma headerLegal_properties_step6_inner_step1_print (c : MacroCertificate P)
    (hH : c.Hereditary) (A : DecTile c) (hA : headerLegal c A) (i : c.Side A.typ)
    (h_inner : c.IsInner (c.occ A.typ i)) (h_print : c.IsPrint (c.occ A.typ i)) :
    IsNontrivial c A i := by
  sorry

/-- Step 2 of the blueprint proof of `headerLegal_properties_step6_inner`: at a boundary side, the
fourth cell is a nonzero header tag. -/
private lemma headerLegal_properties_step6_inner_step2_nonprint_boundary (c : MacroCertificate P)
    (hH : c.Hereditary) (A : DecTile c) (hA : headerLegal c A) (i : c.Side A.typ)
    (h_inner : c.IsInner (c.occ A.typ i)) (h_nprint : ¬ c.IsPrint (c.occ A.typ i))
    (h_bdry : c.IsBoundary (c.occ A.typ i)) :
    IsNontrivial c A i := by
  sorry

/-- Step 3 of the blueprint proof of `headerLegal_properties_step6_inner`: at any other inner side,
the fourth cell is \bot. -/
private lemma headerLegal_properties_step6_inner_step3_nonprint_nonboundary (c : MacroCertificate P)
    (hH : c.Hereditary) (A : DecTile c) (hA : headerLegal c A) (i : c.Side A.typ)
    (h_inner : c.IsInner (c.occ A.typ i)) (h_nprint : ¬ c.IsPrint (c.occ A.typ i))
    (h_nbdry : ¬ c.IsBoundary (c.occ A.typ i)) :
    IsNontrivial c A i := by
  sorry

/-- Step 6 of the blueprint proof of `headerLegal_properties`: every inner side of a legal tile is
nontrivial. -/
private lemma headerLegal_properties_step6_inner (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    InnerActive c A := by
  intro i hi
  by_cases h_print : c.IsPrint (c.occ A.typ i)
  · exact headerLegal_properties_step6_inner_step1_print c hH A hA i hi h_print
  · by_cases h_bdry : c.IsBoundary (c.occ A.typ i)
    · exact headerLegal_properties_step6_inner_step2_nonprint_boundary c hH A hA i hi h_print h_bdry
    · exact headerLegal_properties_step6_inner_step3_nonprint_nonboundary c hH A hA i hi h_print
        h_bdry

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


/-- Step 2.1 of the blueprint proof of `reconstructed_header_eq_isIdentityCorrect_step2_print`: For a print, its fifth cell is local. -/
private lemma reconstructed_header_eq_isIdentityCorrect_step2_print_step1_isLocal (c : MacroCertificate P) (o : c.SideOcc) (hPrint : c.IsPrint o) :
    IsLocal c o 4 := by
  sorry

/-- Step 2.2 of the blueprint proof of `reconstructed_header_eq_isIdentityCorrect_step2_print`:
For a print, its fifth prescribed cell is the exact interface identity. -/
private lemma reconstructed_header_eq_isIdentityCorrect_step2_print_step2_prescribed (c : MacroCertificate P) (o : c.SideOcc) (hPrint : c.IsPrint o) :
    prescribedCell c o 4 = identU c (c.edge o) := by
  sorry

/-- Step 2 of the blueprint proof of `reconstructed_header_eq_isIdentityCorrect`: For a print, the fifth cell of `D` is its prescribed identity. -/
private lemma reconstructed_header_eq_isIdentityCorrect_step2_print (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (i : c.Side h.1)
    (hPrint : c.IsPrint (c.occ h.1 i)) :
    (reconstruct c K h.1).cell i 4 = identU c (c.edge (c.occ h.1 i)) := by
  have hLoc := reconstructed_header_eq_isIdentityCorrect_step2_print_step1_isLocal c (c.occ h.1 i) hPrint
  have hPres := reconstructed_header_eq_isIdentityCorrect_step2_print_step2_prescribed c (c.occ h.1 i) hPrint
  have hNorm := reconstructed_header_eq_isNormal c hH K hK h hh
  have hCell := hNorm i 4 hLoc
  change _ = prescribedCell c (c.occ h.1 i) 4 at hCell
  rw [hCell]
  exact hPres

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
  have _ := hH
  have _ := hK
  have _ := ht_c
  dsimp [reconstruct, ColouredBlock.tileOf]
  rw [ht_owner]
  exact hh.left.symm

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

/-- Step 1 of the blueprint proof of `macroblock_is_decomposition_central_step3_nonprints`: cell 0 is prescribedFirst. -/
private lemma macroblock_is_decomposition_central_step3_nonprints_cell0 (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (t : c.Typ)
    (ht_owner : c.owner t = K.α) (ht_c : t = c.central K.α) :
    ∀ i : c.Side (K.tileOf t).typ,
      ¬ c.IsPrint (c.occ (K.tileOf t).typ i) →
        (K.tileOf t).cell i 0 = prescribedFirst c (c.occ (K.tileOf t).typ i) := by
  sorry

/-- Step 2 of the blueprint proof of `macroblock_is_decomposition_central_step3_nonprints`: cell 1 is 0. -/
private lemma macroblock_is_decomposition_central_step3_nonprints_cell1 (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (t : c.Typ)
    (ht_owner : c.owner t = K.α) (ht_c : t = c.central K.α) :
    ∀ i : c.Side (K.tileOf t).typ,
      ¬ c.IsPrint (c.occ (K.tileOf t).typ i) →
        (K.tileOf t).cell i 1 = 0 := by
  sorry

/-- Step 3 of the blueprint proof of `macroblock_is_decomposition_central_step3_nonprints`: cell 4 is 0. -/
private lemma macroblock_is_decomposition_central_step3_nonprints_cell4 (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (t : c.Typ)
    (ht_owner : c.owner t = K.α) (ht_c : t = c.central K.α) :
    ∀ i : c.Side (K.tileOf t).typ,
      ¬ c.IsPrint (c.occ (K.tileOf t).typ i) →
        (K.tileOf t).cell i 4 = 0 := by
  sorry

/-- Step 4 of the blueprint proof of `macroblock_is_decomposition_central_step3_nonprints`: cell 2 on path matches parent. -/
private lemma macroblock_is_decomposition_central_step3_nonprints_cell2_path (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (t : c.Typ)
    (ht_owner : c.owner t = K.α) (ht_c : t = c.central K.α) :
    ∀ i : c.Side (K.tileOf t).typ,
      ¬ c.IsPrint (c.occ (K.tileOf t).typ i) →
        (∀ (d : c.Side (reconstruct c K h.1).typ) (j : Fin 5),
          c.occ (K.tileOf t).typ i ∈ c.path (c.form (reconstruct c K h.1).typ) d j →
            (K.tileOf t).cell i 2 = (reconstruct c K h.1).cell d j) := by
  sorry

/-- Step 5 of the blueprint proof of `macroblock_is_decomposition_central_step3_nonprints`: cell 2 off path is 0. -/
private lemma macroblock_is_decomposition_central_step3_nonprints_cell2_nopath (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (t : c.Typ)
    (ht_owner : c.owner t = K.α) (ht_c : t = c.central K.α) :
    ∀ i : c.Side (K.tileOf t).typ,
      ¬ c.IsPrint (c.occ (K.tileOf t).typ i) →
        ((∀ (d : c.Side (reconstruct c K h.1).typ) (j : Fin 5),
            c.occ (K.tileOf t).typ i ∉ c.path (c.form (reconstruct c K h.1).typ) d j) →
          (K.tileOf t).cell i 2 = 0) := by
  sorry

/-- Step 6 of the blueprint proof of `macroblock_is_decomposition_central_step3_nonprints`: cell 3 on outer depends on mode. -/
private lemma macroblock_is_decomposition_central_step3_nonprints_cell3_outer (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (t : c.Typ)
    (ht_owner : c.owner t = K.α) (ht_c : t = c.central K.α) :
    ∀ i : c.Side (K.tileOf t).typ,
      ¬ c.IsPrint (c.occ (K.tileOf t).typ i) →
        (c.IsOuter (c.occ (K.tileOf t).typ i) → ∀ d : c.Side (reconstruct c K h.1).typ,
          c.occ (K.tileOf t).typ i ∈ c.outerList (c.form (reconstruct c K h.1).typ) d →
            (K.tileOf t).cell i 3 = if zA c (reconstruct c K h.1) d = true then 0
              else rankU c (c.rankOf (c.form (reconstruct c K h.1).typ) d (c.occ (K.tileOf t).typ i))) := by
  sorry

/-- Step 7 of the blueprint proof of `macroblock_is_decomposition_central_step3_nonprints`: cell 3 on boundary carries header. -/
private lemma macroblock_is_decomposition_central_step3_nonprints_cell3_boundary (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (t : c.Typ)
    (ht_owner : c.owner t = K.α) (ht_c : t = c.central K.α) :
    ∀ i : c.Side (K.tileOf t).typ,
      ¬ c.IsPrint (c.occ (K.tileOf t).typ i) →
        (c.IsBoundary (c.occ (K.tileOf t).typ i) →
          (K.tileOf t).cell i 3 = headerU c (headerOf c (reconstruct c K h.1))) := by
  sorry

/-- Step 8 of the blueprint proof of `macroblock_is_decomposition_central_step3_nonprints`: cell 3 on remaining inner is bot. -/
private lemma macroblock_is_decomposition_central_step3_nonprints_cell3_inner (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (t : c.Typ)
    (ht_owner : c.owner t = K.α) (ht_c : t = c.central K.α) :
    ∀ i : c.Side (K.tileOf t).typ,
      ¬ c.IsPrint (c.occ (K.tileOf t).typ i) →
        (c.IsInner (c.occ (K.tileOf t).typ i) → ¬ c.IsBoundary (c.occ (K.tileOf t).typ i) →
          (K.tileOf t).cell i 3 = botU c) := by
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
  intro i hi
  exact ⟨macroblock_is_decomposition_central_step3_nonprints_cell0 c hH K hK h hh t ht_owner ht_c i hi,
         macroblock_is_decomposition_central_step3_nonprints_cell1 c hH K hK h hh t ht_owner ht_c i hi,
         macroblock_is_decomposition_central_step3_nonprints_cell4 c hH K hK h hh t ht_owner ht_c i hi,
         macroblock_is_decomposition_central_step3_nonprints_cell2_path c hH K hK h hh t ht_owner ht_c i hi,
         macroblock_is_decomposition_central_step3_nonprints_cell2_nopath c hH K hK h hh t ht_owner ht_c i hi,
         macroblock_is_decomposition_central_step3_nonprints_cell3_outer c hH K hK h hh t ht_owner ht_c i hi,
         macroblock_is_decomposition_central_step3_nonprints_cell3_boundary c hH K hK h hh t ht_owner ht_c i hi,
         macroblock_is_decomposition_central_step3_nonprints_cell3_inner c hH K hK h hh t ht_owner ht_c i hi⟩

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

/-- Step 2 of the blueprint proof of `reconstructed_noncentral_legal_step2_parent`: Delete these repetitions. The chain has length n ≤ 2. -/
private lemma reconstructed_noncentral_legal_step2_parent_step1_n_eq_1_or_2 {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hA : headerLegal c K.centre) (hnc : ¬ c.IsCentral h.1)
    (E_anc : DecTile c) (hE_leg : headerLegal c E_anc) (hE_nc : ¬ c.IsCentral E_anc.typ)
    (n : ℕ) (ch : ℕ → DecTile c) (hch0 : ch 0 = K.centre)
    (hch_child : ∀ i, IsChildOf c (ch (i + 1)) (ch i))
    (hch_end : ch n = E_anc) (hch_cent : ∀ i < n, c.IsCentral (ch i).typ) :
    ∃ (n' : ℕ) (ch' : ℕ → DecTile c),
      ch' 0 = K.centre ∧
      (∀ i < n', IsChildOf c (ch' (i + 1)) (ch' i)) ∧
      ch' n' = E_anc ∧
      (∀ i < n', c.IsCentral (ch' i).typ) ∧
      (n' = 1 ∨ n' = 2) := by sorry

/-- Step 2 of the blueprint proof of `reconstructed_noncentral_legal_step2_parent`: Length two is impossible here. -/
private lemma reconstructed_noncentral_legal_step2_parent_step2_not_n_eq_2 {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hA : headerLegal c K.centre) (hnc : ¬ c.IsCentral h.1)
    (E_anc : DecTile c) (hE_leg : headerLegal c E_anc) (hE_nc : ¬ c.IsCentral E_anc.typ)
    (n' : ℕ) (ch' : ℕ → DecTile c) (hch0 : ch' 0 = K.centre)
    (hch_child : ∀ i < n', IsChildOf c (ch' (i + 1)) (ch' i))
    (hch_end : ch' n' = E_anc) (hch_cent : ∀ i < n', c.IsCentral (ch' i).typ)
    (hn'2 : n' = 2) :
    False := by sorry

/-- Step 2 of the blueprint proof of `reconstructed_noncentral_legal_step2_parent`: Deduce that length is 1 and extract the parent. -/
private lemma reconstructed_noncentral_legal_step2_parent_step3_n_eq_1 {P : Protoset}
    (c : MacroCertificate P)
    (K : ColouredBlock c)
    (E_anc : DecTile c) (hE_leg : headerLegal c E_anc) (hE_nc : ¬ c.IsCentral E_anc.typ)
    (n' : ℕ) (ch' : ℕ → DecTile c) (hch0 : ch' 0 = K.centre)
    (hch_child : ∀ i < n', IsChildOf c (ch' (i + 1)) (ch' i))
    (hch_end : ch' n' = E_anc) (hch_cent : ∀ i < n', c.IsCentral (ch' i).typ)
    (hn' : n' = 1 ∨ n' = 2)
    (hnot2 : n' ≠ 2) :
    ∃ E, headerLegal c E ∧ ¬ c.IsCentral E.typ ∧ IsChildOf c E K.centre := by
  have _ := hch_cent
  have hn'1 : n' = 1 := by omega
  subst hn'1
  use ch' 1
  refine ⟨?_, ?_, ?_⟩
  · rw [hch_end]
    exact hE_leg
  · rw [hch_end]
    exact hE_nc
  · have hc0 := hch_child 0 (by omega)
    rw [hch0] at hc0
    exact hc0

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
    ∃ E, headerLegal c E ∧ ¬ c.IsCentral E.typ ∧ IsChildOf c E K.centre := by
  obtain ⟨n', ch', hch'0, hch'_child, hch'_end, hch'_cent, hn'12⟩ :=
    reconstructed_noncentral_legal_step2_parent_step1_n_eq_1_or_2 c hH K hK h hh hA hnc E_anc hE_leg hE_nc n ch hch0 hch_child hch_end hch_cent
  have hnot2 : n' ≠ 2 := by
    intro h2
    exact reconstructed_noncentral_legal_step2_parent_step2_not_n_eq_2 c hH K hK h hh hA hnc E_anc hE_leg hE_nc n' ch' hch'0 hch'_child hch'_end hch'_cent h2
  exact reconstructed_noncentral_legal_step2_parent_step3_n_eq_1 c K E_anc hE_leg hE_nc n' ch' hch'0 hch'_child hch'_end hch'_cent hn'12 hnot2

/-- Step 1 of the blueprint proof of `reconstructed_noncentral_legal_step3_eq`: The parents `E,D`
have the same form. -/
private lemma reconstructed_noncentral_legal_step3_eq_step1_form {P : Protoset}
    (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hA : headerLegal c K.centre) (hnc : ¬ c.IsCentral h.1)
    (E : DecTile c) (hE_leg : headerLegal c E) (hE_nc : ¬ c.IsCentral E.typ)
    (hE_child : IsChildOf c E K.centre) :
    c.form E.typ = c.form h.1 := by
  have _ := hH
  have _ := hK
  have _ := hA
  have _ := hnc
  have _ := hE_leg
  have _ := hE_nc
  have h1 : c.owner K.centre.typ = c.form E.typ := hE_child.1
  have h2 : c.form h.1 = K.α := hh.1
  have h3 : K.centre.typ = c.central K.α := rfl
  have h4 : c.owner (c.central K.α) = K.α := c.g5_central_owner K.α
  rw [h3] at h1
  rw [h4] at h1
  rw [← h1, h2]

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

/-- Step 1 of the blueprint proof of `reconstructed_acyclic_legal_step5_parent_noncentral`:
If the type `r` of `C` were central, it and its central child `t` would have the same large form. -/
private lemma reconstructed_acyclic_legal_step5_parent_noncentral_step1_same_large_form {P : Protoset}
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
    (heq : tileDec X = reconstruct c (part.block j) (tileDec X).typ)
    (h_parent_cent : c.IsCentral h.1) :
    c.form h.1 = c.form (tileDec X).typ := by sorry

/-- Step 2 of the blueprint proof of `reconstructed_acyclic_legal_step5_parent_noncentral`:
If `r` and `t` have the same large form, then `t` is cyclic. -/
private lemma reconstructed_acyclic_legal_step5_parent_noncentral_step2_cyclic {P : Protoset}
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
    (heq : tileDec X = reconstruct c (part.block j) (tileDec X).typ)
    (h_parent_cent : c.IsCentral h.1)
    (h_same_form : c.form h.1 = c.form (tileDec X).typ) :
    c.IsCyclic (tileDec X).typ := by sorry

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
  intro h_parent_cent
  have h_same_form :=
    reconstructed_acyclic_legal_step5_parent_noncentral_step1_same_large_form c hH T hT hL part T'
      hrec hT' hN hex X hX hcent hcyc j h hh heq h_parent_cent
  have h_is_cyclic :=
    reconstructed_acyclic_legal_step5_parent_noncentral_step2_cyclic c hH T hT hL part T'
      hrec hT' hN hex X hX hcent hcyc j h hh heq h_parent_cent h_same_form
  exact hcyc h_is_cyclic

/-- Step 1 of the blueprint proof of `reconstructed_acyclic_legal_step6_main`:
The origin argument from the noncentral legality lemma shows that a legal
ancestry chain of `A` reaches a noncentral type. Removing cyclic repetitions
and checking forms gives length exactly two: `A <- E <- F`, where `E, F` are
legal, `F` is noncentral, `E` is central, and `E, D` have the same form. -/
private lemma reconstructed_acyclic_legal_step6_main_step1_chain {P : Protoset}
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
    ∃ E F : DecTile c,
      IsChildOf c E ((part.block j).tileOf (c.central (part.block j).α)) ∧
      IsChildOf c F E ∧
      headerLegal c E ∧
      headerLegal c F ∧
      c.IsCentral E.typ ∧
      ¬ c.IsCentral F.typ ∧
      c.form E.typ = c.form (tileDec X).typ := by sorry

/-- Step 2 of the blueprint proof of `reconstructed_acyclic_legal_step6_main`:
The parents `E, D` have the same form and agree in their marked first-four
fields through `A`. A counting argument on the occurrences of `t` in their
identities, using $L-Q > 2Q$, implies that `E` also has type `t`. Normal
local cells and the marked copied cells then identify `E = D`. -/
private lemma reconstructed_acyclic_legal_step6_main_step2_eq {P : Protoset}
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
    (h_other_cyc : ∀ Y ∈ T'.tiles, c.IsCyclic (tileDec Y).typ → headerLegal c (tileDec Y))
    (E F : DecTile c)
    (hE_child : IsChildOf c E ((part.block j).tileOf (c.central (part.block j).α)))
    (hF_child : IsChildOf c F E)
    (hE_legal : headerLegal c E)
    (hF_legal : headerLegal c F)
    (hE_cent : c.IsCentral E.typ)
    (hF_nc : ¬ c.IsCentral F.typ)
    (hE_form : c.form E.typ = c.form (tileDec X).typ) :
    E = tileDec X := by sorry

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
  obtain ⟨E, F, hE_child, hF_child, hE_legal, hF_legal, hE_cent, hF_nc, hE_form⟩ :=
    reconstructed_acyclic_legal_step6_main_step1_chain c hH T hT hL part T' hrec hT' hN hex
      X hX hcent hcyc j h hh h_parent_nc heq hctx h_other_nc h_other_cyc
  have hE_eq_D := reconstructed_acyclic_legal_step6_main_step2_eq c hH T hT hL part T' hrec hT'
    hN hex X hX hcent hcyc j h hh h_parent_nc heq hctx h_other_nc h_other_cyc E F hE_child hF_child
    hE_legal hF_legal hE_cent hF_nc hE_form
  rwa [← hE_eq_D]

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

/-! ### Helpers for `lift_hierarchy_step1_decorations` -/
/-- Prints are inner sides. -/
private lemma lhd_isInner_of_isPrintOf (c : MacroCertificate P) {α : c.Q.Form}
    {d : Fin (c.Q.disk α).n} {o : c.SideOcc} (h : c.IsPrintOf α d o) : c.IsInner o := by
  rcases h with ⟨hm, rfl | rfl⟩
  · exact c.g4_print_inner α d hm
  · have hp := c.g1_partner _ (c.g4_print_inner α d hm)
    have hi := c.g4_print_inner α d hm
    unfold MacroData.IsInner MacroData.IsOuter at hi ⊢
    rw [hp.2.2, hp.2.1]
    exact hi

/-- The parent side of a print is unique. -/
private lemma lhd_printOf_unique (c : MacroCertificate P) {α : c.Q.Form}
    {d d' : Fin (c.Q.disk α).n} {o : c.SideOcc} (h : c.IsPrintOf α d o)
    (h' : c.IsPrintOf α d' o) : d = d' := by
  rcases h with ⟨hm, h1⟩
  rcases h' with ⟨hm', h1'⟩
  have hin := c.g4_print_inner α d hm
  have hin' := c.g4_print_inner α d' hm'
  have hp := (c.g1_partner _ hin).1
  have hp' := (c.g1_partner _ hin').1
  have key : c.printOcc α d = c.printOcc α d' → d = d' := by
    intro he
    apply c.g4_print_injective α d d' hm hm'
    unfold MacroData.printOcc at he
    exact eq_of_heq (Sigma.mk.inj he).2
  rcases h1 with rfl | rfl <;> rcases h1' with h2 | h2
  · exact key h2
  · exact absurd (congrArg Sigma.fst h2) (fun h => hp' h.symm)
  · exact absurd (congrArg Sigma.fst h2) hp
  · apply key
    have := congrArg c.partner h2
    rwa [c.g1_partner_partner _ hin, c.g1_partner_partner _ hin'] at this

private lemma lhd_portRank_inj {L : ℕ} (hL : 5 ≤ L) {i j : Fin 5}
    (h : MacroData.portRank L i = MacroData.portRank L j) : i = j := by
  unfold MacroData.portRank at h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega

private lemma lhd_port_inj (c : MacroCertificate P) {α : c.Q.Form} {d : Fin (c.Q.disk α).n}
    {i j : Fin 5} {o : c.SideOcc} (hi : c.port α d i = some o) (hj : c.port α d j = some o) :
    i = j := by
  unfold MacroData.port at hi hj
  rw [List.getElem?_eq_some_iff] at hi hj
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨hj1, hj2⟩ := hj
  have h5 := c.g3_five_le α d
  have heq := (List.Nodup.getElem_inj_iff (c.g3_outerList_nodup α d)).1 (hi2.trans hj2.symm)
  apply lhd_portRank_inj h5
  have h1 : 1 ≤ MacroData.portRank (c.outerList α d).length i := by
    have : (c.outerList α d).length ≤ (i.val + 1) * (c.outerList α d).length :=
      Nat.le_mul_of_pos_left _ (by omega)
    unfold MacroData.portRank; omega
  have h2 : 1 ≤ MacroData.portRank (c.outerList α d).length j := by
    have : (c.outerList α d).length ≤ (j.val + 1) * (c.outerList α d).length :=
      Nat.le_mul_of_pos_left _ (by omega)
    unfold MacroData.portRank; omega
  omega

/-- The path through a nonprint side is unique. -/
private lemma lhd_path_unique (c : MacroCertificate P) {α : c.Q.Form}
    {d d' : Fin (c.Q.disk α).n} {j j' : Fin 5} {o : c.SideOcc} (h : o ∈ c.path α d j)
    (h' : o ∈ c.path α d' j') (hnp : ¬ c.IsPrint o) : d = d' ∧ j = j' := by
  have hown := c.g4_path_owner α d j o h
  subst hown
  by_contra hne
  have hne' : (d, j) ≠ (d', j') := fun he => hne ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  obtain ⟨rfl, ho⟩ := c.g4_path_disjoint _ d d' j j' hne' o h h'
  by_cases hm : c.marked (c.owner o.1) d
  · exact hnp ⟨d, hm, ho⟩
  · have g1 : ¬ c.IsGenuinePath (c.owner o.1) d j := fun hg => hm hg.1
    have g2 : ¬ c.IsGenuinePath (c.owner o.1) d j' := fun hg => hm hg.1
    rw [c.g4_path_trivial _ _ _ g1, Option.mem_toList] at h
    rw [c.g4_path_trivial _ _ _ g2, Option.mem_toList] at h'
    exact hne ⟨rfl, lhd_port_inj c h h'⟩

private lemma lhd_segment_infinite {x y : Pt} (h : x ≠ y) : (segment ℝ x y).Infinite := by
  rw [segment_eq_image_lineMap]
  exact (Set.Icc_infinite zero_lt_one).image
    ((AffineMap.lineMap_injective ℝ h).injOn)

private lemma lhd_finRotate_ne {n : ℕ} (hn : 3 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hs : i ∈ (finRotate (k + 2)).support := by rw [support_finRotate]; exact Finset.mem_univ _
  exact Equiv.Perm.mem_support.1 hs

/-- An outer side lies in the list of at most one parent side. -/
private lemma lhd_outerList_unique (c : MacroCertificate P) {α : c.Q.Form}
    {d d' : Fin (c.Q.disk α).n} {o : c.SideOcc} (h : o ∈ c.outerList α d)
    (h' : o ∈ c.outerList α d') : d = d' := by
  by_contra hne
  have h1 := ((c.g3_outerList_mem α d o).1 h).2.2
  have h2 := ((c.g3_outerList_mem α d' o).1 h').2.2
  have hθ : c.σ.θ ≠ 0 := by have := c.σ.one_lt; positivity
  have hsub : c.occSide o ⊆ c.σ.θ • (((c.Q.disk α).side d) ∩ ((c.Q.disk α).side d')) := by
    rw [Set.smul_set_inter₀ hθ]
    exact Set.subset_inter h1 h2
  have hfin : (c.σ.θ • (((c.Q.disk α).side d) ∩ ((c.Q.disk α).side d'))).Finite := by
    apply Set.Finite.smul_set
    apply Set.Finite.subset (Set.toFinite (({(c.Q.disk α).vertex d,
      (c.Q.disk α).vertex (finRotate _ d)} : Set Pt) ∩ {(c.Q.disk α).vertex d',
      (c.Q.disk α).vertex (finRotate _ d')}))
    exact (c.Q.disk α).simple d d' hne
  apply (hfin.subset hsub).not_infinite
  unfold MacroData.occSide MacroData.childTile PlacedTile.side PolygonalDisk.side
  apply Set.Infinite.vadd_set
  apply lhd_segment_infinite
  intro he
  exact lhd_finRotate_ne (c.Q.disk (c.form o.1)).three_le o.2
    ((c.Q.disk (c.form o.1)).vertex_injective he).symm

/-- Under `owner t = form u`, prints of `t` are the prints of parent sides of `u`. -/
private lemma lhd_print_iff (c : MacroCertificate P) {t u : c.Typ} (h : c.owner t = c.form u)
    (i : c.Side t) :
    c.IsPrint (c.occ t i) ↔ ∃ d : c.Side u, c.IsPrintOf (c.form u) d (c.occ t i) := by
  unfold MacroData.IsPrint
  show (∃ d, c.IsPrintOf (c.owner t) d (c.occ t i)) ↔ _
  rw [h]

/-- An abstract typed hierarchy: objects of every level, the parent map and the
type of each object inside the template of its parent. -/
private structure TypeChain (c : MacroCertificate P) where
  X : ℕ → Type
  par : ∀ n, X n → X (n + 1)
  typ : ∀ n, X n → c.Typ
  adm : ∀ n x, c.owner (typ n x) = c.form (typ (n + 1) (par n x))

/-- Cell positions of the hierarchy. -/
private def tcSt {c : MacroCertificate P} (H : TypeChain c) : Type :=
  Σ m, Σ y : H.X m, c.Side (H.typ m y) × Fin 5

open Classical in
/-- The (unique) copy source of a cell, if any. -/
private def tcSrc {c : MacroCertificate P} (H : TypeChain c) (m : ℕ) (y : H.X m)
    (i : c.Side (H.typ m y)) (k : Fin 5) : Option (c.Side (H.typ (m + 1) (H.par m y)) × Fin 5) :=
  if h : ∃ d, c.IsPrintOf (c.form (H.typ (m + 1) (H.par m y))) d (c.occ (H.typ m y) i) then
    if k = 4 then none else some (h.choose, k)
  else if h' : k = 2 ∧ ∃ p : c.Side (H.typ (m + 1) (H.par m y)) × Fin 5,
      c.occ (H.typ m y) i ∈ c.path (c.form (H.typ (m + 1) (H.par m y))) p.1 p.2 then
    some h'.2.choose
  else none

private lemma tcSrc_of_mem {c : MacroCertificate P} (H : TypeChain c) (m : ℕ) (y : H.X m)
    (i : c.Side (H.typ m y)) (k : Fin 5) (p : c.Side (H.typ (m + 1) (H.par m y)) × Fin 5)
    (hp : p ∈ copySource c (c.form (H.typ (m + 1) (H.par m y))) (c.occ (H.typ m y) i) k) :
    tcSrc H m y i k = some p := by
  unfold tcSrc
  rcases hp with ⟨hpr, hk, hp2⟩ | ⟨hnp, hk, hpath⟩
  · have h : ∃ d, c.IsPrintOf (c.form (H.typ (m + 1) (H.par m y))) d (c.occ (H.typ m y) i) :=
      ⟨p.1, hpr⟩
    rw [dif_pos h, if_neg hk]
    rw [lhd_printOf_unique c h.choose_spec hpr, ← hp2]
  · have h : ¬ ∃ d, c.IsPrintOf (c.form (H.typ (m + 1) (H.par m y))) d (c.occ (H.typ m y) i) :=
      fun h => hnp ((lhd_print_iff c (H.adm m y) i).2 h)
    have h' : k = 2 ∧ ∃ p : c.Side (H.typ (m + 1) (H.par m y)) × Fin 5,
        c.occ (H.typ m y) i ∈ c.path (c.form (H.typ (m + 1) (H.par m y))) p.1 p.2 := ⟨hk, p, hpath⟩
    rw [dif_neg h, dif_pos h']
    obtain ⟨e1, e2⟩ := lhd_path_unique c h'.2.choose_spec hpath hnp
    exact congrArg some (Prod.ext e1 e2)

private lemma tcSrc_mem {c : MacroCertificate P} (H : TypeChain c) (m : ℕ) (y : H.X m)
    (i : c.Side (H.typ m y)) (k : Fin 5) (p : c.Side (H.typ (m + 1) (H.par m y)) × Fin 5)
    (hp : tcSrc H m y i k = some p) :
    p ∈ copySource c (c.form (H.typ (m + 1) (H.par m y))) (c.occ (H.typ m y) i) k := by
  unfold tcSrc at hp
  split_ifs at hp with h1 h2 h3
  · cases hp
    exact Or.inl ⟨h1.choose_spec, h2, rfl⟩
  · cases hp
    refine Or.inr ⟨fun hpr => h1 ((lhd_print_iff c (H.adm m y) i).1 hpr), h3.1, h3.2.choose_spec⟩

/-- One copy step. -/
private def tcStep {c : MacroCertificate P} (H : TypeChain c) : tcSt H → Option (tcSt H)
  | ⟨m, y, i, k⟩ => (tcSrc H m y i k).map fun p => ⟨m + 1, H.par m y, p.1, p.2⟩

/-- Iterated copy steps. -/
private def tcIter {c : MacroCertificate P} (H : TypeChain c) : ℕ → tcSt H → Option (tcSt H)
  | 0, s => some s
  | j + 1, s => (tcStep H s).bind (tcIter H j)

private lemma tcIter_add {c : MacroCertificate P} (H : TypeChain c) (j l : ℕ) (s : tcSt H) :
    tcIter H (j + l) s = (tcIter H j s).bind (tcIter H l) := by
  induction j generalizing s with
  | zero => simp [tcIter]
  | succ j ih =>
    rw [show j + 1 + l = (j + l) + 1 by omega]
    simp only [tcIter, ih, Option.bind_assoc]

private lemma tcIter_origin_unique {c : MacroCertificate P} (H : TypeChain c) {j j' : ℕ}
    {s a b : tcSt H} (ha : tcIter H j s = some a) (ha' : tcStep H a = none)
    (hb : tcIter H j' s = some b) (hb' : tcStep H b = none) : a = b := by
  have key : ∀ {j j' : ℕ} {a b : tcSt H}, j ≤ j' → tcIter H j s = some a → tcStep H a = none →
      tcIter H j' s = some b → a = b := by
    intro j j' a b hle ha ha' hb
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [tcIter_add, ha] at hb
    cases l with
    | zero => simpa [tcIter] using hb
    | succ l => simp [tcIter, ha'] at hb
  rcases le_total j j' with h | h
  · exact key h ha ha' hb
  · exact (key h hb hb' ha).symm

/-- Whether the copy chain of a cell reaches an origin. -/
private def tcTerm {c : MacroCertificate P} (H : TypeChain c) (s : tcSt H) : Prop :=
  ∃ j a, tcIter H j s = some a ∧ tcStep H a = none

/-- The chain of the outer side `i` of `y` stays outer forever. -/
private def tcZ {c : MacroCertificate P} (H : TypeChain c) (m : ℕ) (y : H.X m)
    (i : c.Side (H.typ m y)) : Prop :=
  ∃ S : (m : ℕ) → (y : H.X m) → c.Side (H.typ m y) → Prop, S m y i ∧
    ∀ m' y' j, S m' y' j → ∃ d, c.occ (H.typ m' y') j ∈
      c.outerList (c.form (H.typ (m' + 1) (H.par m' y'))) d ∧ S (m' + 1) (H.par m' y') d

private lemma tcZ_iff {c : MacroCertificate P} (H : TypeChain c) (m : ℕ) (y : H.X m)
    (i : c.Side (H.typ m y)) :
    tcZ H m y i ↔ ∃ d, c.occ (H.typ m y) i ∈ c.outerList (c.form (H.typ (m + 1) (H.par m y))) d ∧
      tcZ H (m + 1) (H.par m y) d := by
  constructor
  · rintro ⟨S, hS, hcl⟩
    obtain ⟨d, hd, hS'⟩ := hcl m y i hS
    exact ⟨d, hd, S, hS', hcl⟩
  · rintro ⟨d, hd, hZ⟩
    refine ⟨fun m' y' j => tcZ H m' y' j ∨ ∃ d, c.occ (H.typ m' y') j ∈
      c.outerList (c.form (H.typ (m' + 1) (H.par m' y'))) d ∧ tcZ H (m' + 1) (H.par m' y') d,
      Or.inr ⟨d, hd, hZ⟩, ?_⟩
    rintro m' y' j (⟨S, hS, hcl⟩ | ⟨d', hd', hZ'⟩)
    · obtain ⟨d', hd', hS'⟩ := hcl m' y' j hS
      exact ⟨d', hd', Or.inl ⟨S, hS', hcl⟩⟩
    · exact ⟨d', hd', Or.inl hZ'⟩

open Classical in
/-- The fourth cell of an outer side. -/
private def tcFourthOuter {c : MacroCertificate P} (H : TypeChain c) (m : ℕ) (y : H.X m)
    (i : c.Side (H.typ m y)) : U c :=
  if h : ∃ d, c.occ (H.typ m y) i ∈ c.outerList (c.form (H.typ (m + 1) (H.par m y))) d then
    (if tcZ H m y i then 0
      else rankU c (c.rankOf (c.form (H.typ (m + 1) (H.par m y))) h.choose (c.occ (H.typ m y) i)))
  else botU c

open Classical in
/-- The fourth cell of a nonprint side. -/
private def tcFourth {c : MacroCertificate P} (H : TypeChain c) (m : ℕ) (y : H.X m)
    (i : c.Side (H.typ m y)) : U c :=
  if c.IsOuter (c.occ (H.typ m y) i) then tcFourthOuter H m y i
  else if c.IsBoundary (c.occ (H.typ m y) i) then
    headerU c (HeaderKernel.makeHeader c.outerB (H.typ (m + 1) (H.par m y))
      (fun d => tcFourthOuter H (m + 1) (H.par m y) d))
  else botU c

open Classical in
/-- The value of an origin cell. -/
private def tcOrig {c : MacroCertificate P} (H : TypeChain c) : tcSt H → U c
  | ⟨m, y, i, k⟩ =>
    if ∃ d, c.IsPrintOf (c.form (H.typ (m + 1) (H.par m y))) d (c.occ (H.typ m y) i) then
      (if k = 4 then identU c (c.edge (c.occ (H.typ m y) i)) else 0)
    else if k = 0 then prescribedFirst c (c.occ (H.typ m y) i)
    else if k = 3 then tcFourth H m y i
    else 0

open Classical in
/-- The value of a cell: the value of its origin, or zero if there is none. -/
private def tcVal {c : MacroCertificate P} (H : TypeChain c) (s : tcSt H) : U c :=
  if h : tcTerm H s then tcOrig H h.choose_spec.choose else 0

private lemma tcVal_of_step_none {c : MacroCertificate P} (H : TypeChain c) (s : tcSt H)
    (hs : tcStep H s = none) : tcVal H s = tcOrig H s := by
  have h : tcTerm H s := ⟨0, s, rfl, hs⟩
  unfold tcVal
  rw [dif_pos h]
  congr 1
  exact tcIter_origin_unique H (j' := 0) h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2 rfl hs

private lemma tcVal_of_step_some {c : MacroCertificate P} (H : TypeChain c) (s s' : tcSt H)
    (hs : tcStep H s = some s') : tcVal H s = tcVal H s' := by
  have hiff : tcTerm H s ↔ tcTerm H s' := by
    constructor
    · rintro ⟨j, a, ha, ha'⟩
      cases j with
      | zero =>
        simp only [tcIter, Option.some.injEq] at ha
        subst ha; rw [hs] at ha'; cases ha'
      | succ j => exact ⟨j, a, by simpa [tcIter, hs] using ha, ha'⟩
    · rintro ⟨j, a, ha, ha'⟩
      exact ⟨j + 1, a, by simpa [tcIter, hs] using ha, ha'⟩
  unfold tcVal
  by_cases h : tcTerm H s
  · have h' := hiff.1 h
    rw [dif_pos h, dif_pos h']
    congr 1
    apply tcIter_origin_unique H (j := h.choose + 0) (s := s)
    · simpa using h.choose_spec.choose_spec.1
    · exact h.choose_spec.choose_spec.2
    · show tcIter H (h'.choose + 1) s = _
      simpa [tcIter, hs] using h'.choose_spec.choose_spec.1
    · exact h'.choose_spec.choose_spec.2
  · rw [dif_neg h, dif_neg (fun h' => h (hiff.2 h'))]

/-- The decorated tile of an object of the hierarchy. -/
private def tcDec {c : MacroCertificate P} (H : TypeChain c) (m : ℕ) (y : H.X m) : DecTile c :=
  ⟨H.typ m y, fun i k => tcVal H ⟨m, y, i, k⟩⟩

private lemma tcDec_copy {c : MacroCertificate P} (H : TypeChain c) (m : ℕ) (y : H.X m)
    (i : c.Side (H.typ m y)) (k : Fin 5) (p : c.Side (H.typ (m + 1) (H.par m y)) × Fin 5)
    (hp : p ∈ copySource c (c.form (H.typ (m + 1) (H.par m y))) (c.occ (H.typ m y) i) k) :
    (tcDec H m y).cell i k = (tcDec H (m + 1) (H.par m y)).cell p.1 p.2 := by
  apply tcVal_of_step_some
  simp [tcStep, tcSrc_of_mem H m y i k p hp]

private lemma tcDec_orig {c : MacroCertificate P} (H : TypeChain c) (m : ℕ) (y : H.X m)
    (i : c.Side (H.typ m y)) (k : Fin 5)
    (hp : ∀ p, p ∉ copySource c (c.form (H.typ (m + 1) (H.par m y))) (c.occ (H.typ m y) i) k) :
    (tcDec H m y).cell i k = tcOrig H ⟨m, y, i, k⟩ := by
  apply tcVal_of_step_none
  cases h : tcSrc H m y i k with
  | none => simp [tcStep, h]
  | some p => exact absurd (tcSrc_mem H m y i k p h) (hp p)

private lemma lhd_rankU_ne_zero (c : MacroCertificate P) (k : Fin (c.rankBound + 1)) :
    rankU c k ≠ 0 := by
  intro h; cases h

private lemma lhd_botU_ne_zero (c : MacroCertificate P) : botU c ≠ 0 := by
  intro h; cases h

private lemma tcDec_cell3_outer {c : MacroCertificate P} (H : TypeChain c) (m : ℕ) (y : H.X m)
    (i : c.Side (H.typ m y)) (ho : c.IsOuter (c.occ (H.typ m y) i)) :
    (tcDec H m y).cell i 3 = tcFourthOuter H m y i := by
  have hnp : ¬ ∃ d, c.IsPrintOf (c.form (H.typ (m + 1) (H.par m y))) d (c.occ (H.typ m y) i) :=
    fun ⟨d, hd⟩ => lhd_isInner_of_isPrintOf c hd ho
  rw [tcDec_orig]
  · simp only [tcOrig]
    rw [if_neg hnp, if_neg (by decide)]
    simp only [↓reduceIte]
    unfold tcFourth
    rw [if_pos ho]
  · rintro p (⟨hpr, _, _⟩ | ⟨_, hk, _⟩)
    · exact hnp ⟨p.1, hpr⟩
    · exact absurd hk (by decide)

/-- The decorated tiles of the hierarchy satisfy the child relation. -/
private lemma tcDec_child {c : MacroCertificate P} (H : TypeChain c) (m : ℕ) (y : H.X m) :
    IsChildOf c (tcDec H (m + 1) (H.par m y)) (tcDec H m y) := by
  refine ⟨H.adm m y, fun i => ⟨?_, ?_⟩⟩
  · intro d hd
    refine ⟨fun k hk => tcDec_copy H m y i k (d, k) (Or.inl ⟨hd, hk, rfl⟩), ?_⟩
    rw [tcDec_orig]
    · simp only [tcOrig]
      rw [if_pos ⟨d, hd⟩]
      simp only [↓reduceIte]
      rfl
    · rintro p (⟨_, h4, _⟩ | ⟨hnp, _, _⟩)
      · exact h4 rfl
      · exact hnp ((lhd_print_iff c (H.adm m y) i).2 ⟨d, hd⟩)
  · intro hnp
    have hnp' : ¬ ∃ d, c.IsPrintOf (c.form (H.typ (m + 1) (H.par m y))) d
        (c.occ (H.typ m y) i) := fun h => hnp ((lhd_print_iff c (H.adm m y) i).2 h)
    have hno : ∀ k : Fin 5, k ≠ 2 → ∀ p, p ∉ copySource c (c.form (H.typ (m + 1) (H.par m y)))
        (c.occ (H.typ m y) i) k := by
      rintro k hk p (⟨hpr, _, _⟩ | ⟨_, hk2, _⟩)
      · exact hnp' ⟨p.1, hpr⟩
      · exact hk hk2
    have horig : ∀ k : Fin 5, k ≠ 2 → (tcDec H m y).cell i k = tcOrig H ⟨m, y, i, k⟩ :=
      fun k hk => tcDec_orig H m y i k (hno k hk)
    have h3 : (tcDec H m y).cell i 3 = tcFourth H m y i := by
      rw [horig 3 (by decide)]
      simp only [tcOrig]
      rw [if_neg hnp', if_neg (by decide)]
      simp only [↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [horig 0 (by decide)]
      simp only [tcOrig]
      rw [if_neg hnp']
      simp only [↓reduceIte]
      rfl
    · rw [horig 1 (by decide)]
      simp only [tcOrig]
      rw [if_neg hnp', if_neg (by decide), if_neg (by decide)]
    · rw [horig 4 (by decide)]
      simp only [tcOrig]
      rw [if_neg hnp', if_neg (by decide), if_neg (by decide)]
    · intro d j hdj
      exact tcDec_copy H m y i 2 (d, j) (Or.inr ⟨hnp, rfl, hdj⟩)
    · intro hnone
      rw [tcDec_orig]
      · simp only [tcOrig]
        rw [if_neg hnp', if_neg (by decide), if_neg (by decide)]
      · rintro p (⟨hpr, _, _⟩ | ⟨_, _, hpath⟩)
        · exact hnp' ⟨p.1, hpr⟩
        · exact hnone _ _ hpath
    · intro hout d hd
      replace hout : c.IsOuter (c.occ (H.typ m y) i) := hout
      rw [h3]
      unfold tcFourth
      rw [if_pos hout]
      unfold tcFourthOuter
      have hex : ∃ d, c.occ (H.typ m y) i ∈ c.outerList (c.form (H.typ (m + 1) (H.par m y))) d :=
        ⟨d, hd⟩
      rw [dif_pos hex]
      have hch : hex.choose = d := lhd_outerList_unique c hex.choose_spec hd
      rw [hch]
      by_cases hz : tcZ H m y i
      · rw [if_pos hz]
        obtain ⟨d', hd', hZ'⟩ := (tcZ_iff H m y i).1 hz
        obtain rfl : d' = d := lhd_outerList_unique c hd' hd
        have hzA : zA c (tcDec H (m + 1) (H.par m y)) d' = true := by
          unfold zA
          rw [HeaderKernel.zeroMode_eq_true_iff]
          obtain ⟨d'', hd'', hZ''⟩ := (tcZ_iff H (m + 1) (H.par m y) d').1 hZ'
          have hout' := ((c.g3_outerList_mem _ d'' _).1 hd'').2.1
          refine ⟨by simpa [MacroData.outerB] using hout', ?_⟩
          show (tcDec H (m + 1) (H.par m y)).cell d' 3 = 0
          rw [tcDec_cell3_outer H (m + 1) (H.par m y) d' hout']
          unfold tcFourthOuter
          rw [dif_pos ⟨d'', hd''⟩, if_pos hZ']
        rw [if_pos hzA]
      · rw [if_neg hz]
        have hzA : zA c (tcDec H (m + 1) (H.par m y)) d = false := by
          unfold zA
          by_cases ho : c.IsOuter (c.occ (H.typ (m + 1) (H.par m y)) d)
          · apply HeaderKernel.zeroMode_eq_false_of_ne_zero
            show (tcDec H (m + 1) (H.par m y)).cell d 3 ≠ 0
            rw [tcDec_cell3_outer H (m + 1) (H.par m y) d ho]
            unfold tcFourthOuter
            split_ifs with h1 h2
            · exact absurd ((tcZ_iff H m y i).2 ⟨d, hd, h2⟩) hz
            · exact lhd_rankU_ne_zero c _
            · exact lhd_botU_ne_zero c
          · apply HeaderKernel.zeroMode_eq_false_of_inner
            simpa [MacroData.outerB] using ho
        rw [if_neg (by rw [hzA]; decide)]
        rfl
    · intro hb
      replace hb : c.IsBoundary (c.occ (H.typ m y) i) := hb
      rw [h3]
      unfold tcFourth
      rw [if_neg hb.1, if_pos hb]
      congr 1
      unfold headerOf HeaderKernel.makeHeader
      congr 1
      funext d
      unfold HeaderKernel.zeroMode
      by_cases ho : c.outerB (H.typ (m + 1) (H.par m y)) d = true
      · have ho' : c.IsOuter (c.occ (H.typ (m + 1) (H.par m y)) d) := by
          simpa [MacroData.outerB] using ho
        show _ = (_ && decide ((tcDec H (m + 1) (H.par m y)).cell d 3 = 0))
        rw [tcDec_cell3_outer H (m + 1) (H.par m y) d ho']
        rfl
      · simp only [Bool.not_eq_true] at ho
        show (c.outerB (H.typ (m + 1) (H.par m y)) d && _) =
          (c.outerB (H.typ (m + 1) (H.par m y)) d && _)
        rw [ho]
        rfl
    · intro hin hnb
      replace hin : c.IsInner (c.occ (H.typ m y) i) := hin
      replace hnb : ¬ c.IsBoundary (c.occ (H.typ m y) i) := hnb
      rw [h3]
      unfold tcFourth
      rw [if_neg hin, if_neg hnb]

/-- Ancestors in the hierarchy. -/
private def tcAnc {c : MacroCertificate P} (H : TypeChain c) (n : ℕ) (x : H.X n) :
    (j : ℕ) → H.X (n + j)
  | 0 => x
  | j + 1 => H.par (n + j) (tcAnc H n x j)

private lemma tc_hasOrigin {c : MacroCertificate P} (H : TypeChain c) (n : ℕ) (x : H.X n) :
    ∀ (j m : ℕ) (i : c.Side (H.typ (n + m) (tcAnc H n x m))) (k : Fin 5) (a : tcSt H),
      tcIter H j ⟨n + m, tcAnc H n x m, i, k⟩ = some a → tcStep H a = none →
      HasOrigin c (fun j => tcDec H (n + j) (tcAnc H n x j)) m i k := by
  intro j
  induction j with
  | zero =>
    intro m i k a ha ha'
    simp only [tcIter, Option.some.injEq] at ha
    subst ha
    apply HasOrigin.origin
    ext p
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hp
    have := tcSrc_of_mem H (n + m) (tcAnc H n x m) i k p hp
    simp [tcStep, this] at ha'
  | succ j ih =>
    intro m i k a ha ha'
    cases hs : tcSrc H (n + m) (tcAnc H n x m) i k with
    | none => simp [tcIter, tcStep, hs] at ha
    | some p =>
      simp only [tcIter, tcStep, hs, Option.map_some, Option.bind_some] at ha
      exact HasOrigin.step (ch := fun j => tcDec H (n + j) (tcAnc H n x j)) m i k p.1 p.2 (tcSrc_mem _ _ _ _ _ _ hs) (ih (m + 1) p.1 p.2 a ha ha')

/-- The decorated tiles of the hierarchy are legal. -/
private lemma tcDec_legal {c : MacroCertificate P} (H : TypeChain c) (n : ℕ) (x : H.X n) :
    headerLegal c (tcDec H n x) := by
  refine ⟨fun j => tcDec H (n + j) (tcAnc H n x j), rfl,
    fun j => tcDec_child H (n + j) (tcAnc H n x j), ?_⟩
  intro j i k _ hno
  show tcVal H ⟨n + j, tcAnc H n x j, i, k⟩ = 0
  unfold tcVal
  rw [dif_neg]
  rintro ⟨l, a, ha, ha'⟩
  exact hno (tc_hasOrigin H n x l j i k a ha ha')

private lemma lhd_parent_exists (c : MacroCertificate P) {T' T : PlaneTiling c.Q}
    (h : c.σ.IsComposition T' T) {Z : PlacedTile c.Q} (hZ : Z ∈ T.tiles) :
    ∃ Y ∈ T'.tiles, ∃ t, c.owner t = Y.form ∧
      Z = ⟨c.form t, c.σ.θ • Y.anchor +ᵥ c.anchor t⟩ := by
  rw [← h] at hZ
  simp only [Substitution.decompose, Substitution.decomposeTile, translateSet, c.rule_eq,
    Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq] at hZ
  obtain ⟨Y, hY, _, ⟨t, ht, rfl⟩, rfl⟩ := hZ
  exact ⟨Y, hY, t, ht, rfl⟩

private lemma lhd_child_mem (c : MacroCertificate P) {T' T : PlaneTiling c.Q}
    (h : c.σ.IsComposition T' T) {Y : PlacedTile c.Q} (hY : Y ∈ T'.tiles) {t : c.Typ}
    (ht : c.owner t = Y.form) :
    (⟨c.form t, c.σ.θ • Y.anchor +ᵥ c.anchor t⟩ : PlacedTile c.Q) ∈ T.tiles := by
  rw [← h]
  simp only [Substitution.decompose, Substitution.decomposeTile, translateSet, c.rule_eq,
    Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
  exact ⟨Y, hY, _, ⟨t, ht, rfl⟩, rfl⟩

private lemma lhd_child_carrier_subset (c : MacroCertificate P) {Y : PlacedTile c.Q} {t : c.Typ}
    (ht : c.owner t = Y.form) :
    (⟨c.form t, c.σ.θ • Y.anchor +ᵥ c.anchor t⟩ : PlacedTile c.Q).carrier ⊆
      c.σ.θ • Y.carrier := by
  have hmem : (⟨c.form t, c.anchor t⟩ : PlacedTile c.Q) ∈ (c.σ.rule Y.form).tiles := by
    rw [c.rule_eq]; exact ⟨t, ht, rfl⟩
  have hsub : (⟨c.form t, c.anchor t⟩ : PlacedTile c.Q).carrier ⊆
      c.σ.θ • (c.Q.disk Y.form).carrier := by
    rw [← c.σ.support_eq]
    exact Set.subset_biUnion_of_mem (u := fun A => A.carrier) hmem
  intro x hx
  simp only [PlacedTile.carrier, Set.mem_vadd_set] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hz' : c.anchor t +ᵥ z ∈ c.σ.θ • (c.Q.disk Y.form).carrier :=
    hsub (Set.vadd_mem_vadd_set hz)
  obtain ⟨w, hw, hw'⟩ := Set.mem_smul_set.1 hz'
  refine Set.mem_smul_set.2 ⟨Y.anchor +ᵥ w, ?_, ?_⟩
  · exact Set.vadd_mem_vadd_set hw
  · simp only [vadd_eq_add, smul_add] at hw' ⊢
    rw [hw']
    abel

private lemma lhd_parent_unique (c : MacroCertificate P) (T' : PlaneTiling c.Q)
    {Y Y' : PlacedTile c.Q} (hY : Y ∈ T'.tiles) (hY' : Y' ∈ T'.tiles) {t t' : c.Typ}
    (ht : c.owner t = Y.form) (ht' : c.owner t' = Y'.form)
    (he : (⟨c.form t, c.σ.θ • Y.anchor +ᵥ c.anchor t⟩ : PlacedTile c.Q) =
      ⟨c.form t', c.σ.θ • Y'.anchor +ᵥ c.anchor t'⟩) : Y = Y' ∧ t = t' := by
  have hθ : c.σ.θ ≠ 0 := by have := c.σ.one_lt; positivity
  have hYY : Y = Y' := by
    by_contra hne
    set Z : PlacedTile c.Q := ⟨c.form t, c.σ.θ • Y.anchor +ᵥ c.anchor t⟩ with hZ
    have h1 := lhd_child_carrier_subset c ht
    have h2 := lhd_child_carrier_subset c ht'
    rw [← he] at h2
    obtain ⟨z, hz⟩ := (c.Q.disk (c.form t)).interior_nonempty
    have hzi : (c.σ.θ • Y.anchor +ᵥ c.anchor t) +ᵥ z ∈ interior Z.carrier := by
      simp only [Z, PlacedTile.carrier]
      rw [interior_vadd]
      exact Set.vadd_mem_vadd_set hz
    have i1 := interior_mono h1 hzi
    have i2 := interior_mono h2 hzi
    rw [interior_smul₀ hθ] at i1 i2
    obtain ⟨w, hw, hw'⟩ := Set.mem_smul_set.1 i1
    obtain ⟨w', hw2, hw2'⟩ := Set.mem_smul_set.1 i2
    have hww : w = w' := smul_right_injective _ hθ (hw'.trans hw2'.symm)
    subst hww
    exact Set.disjoint_left.1 (T'.disjoint hY hY' hne) hw hw2
  subst hYY
  refine ⟨rfl, c.type_injective t t' (ht.trans ht'.symm) (congrArg PlacedTile.form he) ?_⟩
  have := congrArg PlacedTile.anchor he
  simpa using this

private lemma lhd_dec_carrier (c : MacroCertificate P) (Z : PlacedTile c.Q) (D : DecTile c)
    (hD : c.form D.typ = Z.form) :
    (⟨D, Z.anchor⟩ : PlacedTile (typedDecoration c)).carrier = Z.carrier := by
  show Z.anchor +ᵥ (c.Q.disk (c.form D.typ)).carrier = Z.anchor +ᵥ (c.Q.disk Z.form).carrier
  rw [hD]

/-- A decorated copy of a plane tiling. -/
private def lhdTiling (c : MacroCertificate P) (T : PlaneTiling c.Q) (f : T.tiles → DecTile c)
    (hf : ∀ Z, c.form (f Z).typ = Z.1.form) : PlaneTiling (typedDecoration c) where
  tiles := Set.range fun Z => (⟨f Z, Z.1.anchor⟩ : PlacedTile (typedDecoration c))
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ support T.tiles := by rw [T.cover]; exact Set.mem_univ x
    simp only [support, Set.mem_iUnion] at hx ⊢
    obtain ⟨Z, hZ, hxZ⟩ := hx
    refine ⟨_, ⟨⟨Z, hZ⟩, rfl⟩, ?_⟩
    rw [lhd_dec_carrier c Z _ (hf ⟨Z, hZ⟩)]
    exact hxZ
  disjoint := by
    rintro _ ⟨Z, rfl⟩ _ ⟨Z', rfl⟩ hne
    simp only [Function.onFun]
    rw [lhd_dec_carrier c Z.1 _ (hf Z), lhd_dec_carrier c Z'.1 _ (hf Z')]
    apply T.disjoint Z.2 Z'.2
    intro he
    exact hne (by rw [Subtype.ext he])

/-- Cells of a decorated tile, transported to the type `t`. -/
private def lhdCellsAt (c : MacroCertificate P) (E : DecTile c) (t : c.Typ) :
    c.Side t → Fin 5 → U c :=
  if h : E.typ = t then h ▸ E.cell else fun _ _ => 0

private lemma lhdCellsAt_eq (c : MacroCertificate P) (E : DecTile c) (t : c.Typ) (h : E.typ = t) :
    (⟨t, lhdCellsAt c E t⟩ : DecTile c) = E := by
  obtain ⟨et, ecell⟩ := E
  dsimp only at h
  subst h
  simp [lhdCellsAt]

/-- The typed hierarchy underlying a `σ'` hierarchy. -/
private def lhdChain (c : MacroCertificate P) (seq : ℕ → PlaneTiling c.Q)
    (par : ∀ n, (seq n).tiles → (seq (n + 1)).tiles) (typ : ∀ n, (seq n).tiles → c.Typ)
    (hspec : ∀ n Z, c.owner (typ n Z) = (par n Z).1.form ∧
      Z.1 = ⟨c.form (typ n Z), c.σ.θ • (par n Z).1.anchor +ᵥ c.anchor (typ n Z)⟩) :
    TypeChain c where
  X n := (seq n).tiles
  par := par
  typ := typ
  adm n x := (hspec n x).1.trans (congrArg PlacedTile.form (hspec (n + 1) (par n x)).2)

private lemma lhd_main (c : MacroCertificate P)
    (seq : ℕ → PlaneTiling c.Q) (hseq : ∀ n, c.σ.IsComposition (seq (n + 1)) (seq n))
    (par : ∀ n, (seq n).tiles → (seq (n + 1)).tiles) (typ : ∀ n, (seq n).tiles → c.Typ)
    (hspec : ∀ n Z, c.owner (typ n Z) = (par n Z).1.form ∧
      Z.1 = ⟨c.form (typ n Z), c.σ.θ • (par n Z).1.anchor +ᵥ c.anchor (typ n Z)⟩) :
    ∃ seq' : ℕ → PlaneTiling (typedDecoration c),
      (∀ n, eraseSet c (seq' n).tiles = (seq n).tiles) ∧
      (∀ n, IsExactComposition c (seq' (n + 1)) (seq' n)) ∧
      (∀ n, ∀ X ∈ (seq' n).tiles, headerLegal c (tileDec X)) := by
  set H := lhdChain c seq par typ hspec with hH
  have hform : ∀ n (Z : (seq n).tiles), c.form (tcDec H n Z).typ = Z.1.form :=
    fun n Z => (congrArg PlacedTile.form (hspec n Z).2).symm
  -- the child of type `t` of a tile `Y`
  have hchild : ∀ n (Y : (seq (n + 1)).tiles) (t : c.Typ) (ht : c.owner t = Y.1.form),
      ∃ Z : (seq n).tiles, par n Z = Y ∧ typ n Z = t ∧
        Z.1 = ⟨c.form t, c.σ.θ • Y.1.anchor +ᵥ c.anchor t⟩ := by
    intro n Y t ht
    refine ⟨⟨_, lhd_child_mem c (hseq n) Y.2 ht⟩, ?_⟩
    set Z : (seq n).tiles := ⟨_, lhd_child_mem c (hseq n) Y.2 ht⟩
    obtain ⟨h1, h2⟩ := lhd_parent_unique c (seq (n + 1)) (par n Z).2 Y.2 (hspec n Z).1 ht
      ((hspec n Z).2.symm.trans rfl)
    exact ⟨Subtype.ext h1, h2, rfl⟩
  have hinj : ∀ n (Y Y' : (seq n).tiles),
      (⟨tcDec H n Y, Y.1.anchor⟩ : PlacedTile (typedDecoration c)) = ⟨tcDec H n Y', Y'.1.anchor⟩ →
      Y = Y' := by
    intro n Y Y' he
    apply Subtype.ext
    apply PlacedTile.ext
    · rw [← hform n Y, ← hform n Y']
      exact congrArg (fun A : PlacedTile (typedDecoration c) => c.form (A.form : DecTile c).typ) he
    · exact congrArg (fun A : PlacedTile (typedDecoration c) => A.anchor) he
  refine ⟨fun n => lhdTiling c (seq n) (tcDec H n) (hform n), ?_, ?_, ?_⟩
  · intro n
    ext W
    constructor
    · rintro ⟨_, ⟨Z, rfl⟩, rfl⟩
      convert Z.2 using 1
      exact PlacedTile.ext (hform n Z) rfl
    · intro hW
      refine ⟨_, ⟨⟨W, hW⟩, rfl⟩, ?_⟩
      exact PlacedTile.ext (hform n ⟨W, hW⟩) rfl
  · intro n
    classical
    let par' : (lhdTiling c (seq (n + 1)) (tcDec H (n + 1)) (hform (n + 1))).tiles →
        (seq (n + 1)).tiles := fun X' => Classical.choose X'.2
    have hpar' : ∀ X', (⟨tcDec H (n + 1) (par' X'), (par' X').1.anchor⟩ :
        PlacedTile (typedDecoration c)) = X'.1 := fun X' => Classical.choose_spec X'.2
    let col : (seq (n + 1)).tiles → (t : c.Typ) → c.Side t → Fin 5 → U c := fun Y t =>
      if h : c.owner t = Y.1.form then lhdCellsAt c (tcDec H n (hchild n Y t h).choose) t
      else fun _ _ => 0
    have hcol : ∀ Y t (h : c.owner t = Y.1.form),
        (⟨t, col Y t⟩ : DecTile c) = tcDec H n (hchild n Y t h).choose := by
      intro Y t h
      simp only [col, dif_pos h]
      exact lhdCellsAt_eq c _ t (hchild n Y t h).choose_spec.2.1
    refine ⟨fun X' => ⟨c.form (tcDec H (n + 1) (par' X')).typ, c.σ.θ • X'.1.anchor,
      col (par' X')⟩, fun X' => ⟨⟨?_, ?_⟩, rfl⟩, ?_⟩
    · rw [← hpar' X']
      rfl
    · intro t ht
      have ht' : c.owner t = (par' X').1.form := ht.trans (hform _ _)
      show IsChildOf c (tileDec X'.1) ⟨t, col (par' X') t⟩
      rw [hcol _ t ht', ← hpar' X']
      show IsChildOf c (tcDec H (n + 1) (par' X')) _
      have := tcDec_child H n (hchild n (par' X') t ht').choose
      have hp : H.par n (hchild n (par' X') t ht').choose = par' X' :=
        (hchild n (par' X') t ht').choose_spec.1
      rwa [hp] at this
    · ext W
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨Z, rfl⟩
        set Y := par n Z
        refine ⟨⟨_, ⟨Y, rfl⟩⟩, ?_⟩
        have hY : par' ⟨_, ⟨Y, rfl⟩⟩ = Y := hinj _ _ _ (hpar' ⟨_, ⟨Y, rfl⟩⟩)
        refine ⟨typ n Z, ?_, ?_⟩
        · show c.owner (typ n Z) = c.form (tcDec H (n + 1) (par' ⟨_, ⟨Y, rfl⟩⟩)).typ
          rw [hY, hform]
          exact (hspec n Z).1
        · have ht : c.owner (typ n Z) = (par' ⟨_, ⟨Y, rfl⟩⟩).1.form := by
            rw [hY]; exact (hspec n Z).1
          obtain ⟨hZ1, hZ2, hZ3⟩ := (hchild n _ (typ n Z) ht).choose_spec
          have hZ : (hchild n _ (typ n Z) ht).choose = Z := by
            apply Subtype.ext
            rw [hZ3, (hspec n Z).2, hY]
          show _ = (⟨⟨typ n Z, col _ (typ n Z)⟩, _⟩ : PlacedTile (typedDecoration c))
          rw [hcol _ _ ht, hZ]
          refine PlacedTile.ext rfl ?_
          show Z.1.anchor = _
          rw [(hspec n Z).2]
          simp only [vadd_eq_add]
          congr 2
      · rintro ⟨X', t, ht, rfl⟩
        have ht' : c.owner t = (par' X').1.form := ht.trans (hform _ _)
        show (⟨⟨t, col (par' X') t⟩, _⟩ : PlacedTile (typedDecoration c)) ∈ _
        rw [hcol _ t ht']
        refine ⟨(hchild n (par' X') t ht').choose, ?_⟩
        refine PlacedTile.ext rfl ?_
        show (hchild n (par' X') t ht').choose.1.anchor = _
        rw [(hchild n (par' X') t ht').choose_spec.2.2, ← hpar' X']
        simp [vadd_eq_add]
  · rintro n _ ⟨Z, rfl⟩
    exact tcDec_legal H n Z

/-- Step 1 of the blueprint proof of `lift_hierarchy`: construct the compatible legal
decorations for the hierarchy. -/
private lemma lift_hierarchy_step1_decorations (c : MacroCertificate P) (hH : c.Hereditary)
    (seq : ℕ → PlaneTiling c.Q) (hseq : ∀ n, c.σ.IsComposition (seq (n + 1)) (seq n))
    (hsts : HierarchySupertilesSTS c seq) :
    ∃ seq' : ℕ → PlaneTiling (typedDecoration c),
      (∀ n, eraseSet c (seq' n).tiles = (seq n).tiles) ∧
      (∀ n, IsExactComposition c (seq' (n + 1)) (seq' n)) ∧
      (∀ n, ∀ X ∈ (seq' n).tiles, headerLegal c (tileDec X)) := by
  -- neither heredity nor the side-to-side hypothesis is needed for this step
  have _ := hH
  have _ := hsts
  classical
  have hpar : ∀ n (Z : (seq n).tiles), ∃ Y : (seq (n + 1)).tiles, ∃ t, c.owner t = Y.1.form ∧
      Z.1 = ⟨c.form t, c.σ.θ • Y.1.anchor +ᵥ c.anchor t⟩ := by
    intro n Z
    obtain ⟨Y, hY, t, ht, he⟩ := lhd_parent_exists c (hseq n) Z.2
    exact ⟨⟨Y, hY⟩, t, ht, he⟩
  choose par typ hspec using hpar
  exact lhd_main c seq hseq par typ hspec

/-- Step 2.1.1 of the blueprint proof of `lift_hierarchy_step2_proper_step1_inner`: 
We show that the valid child tile `X` comes from a proper realization block `blk`. -/
private lemma lift_hierarchy_step2_proper_step1_inner_step1_proper_blk (c : MacroCertificate P)
    (hH : c.Hereditary)
    (seq : ℕ → PlaneTiling c.Q) (hsts : HierarchySupertilesSTS c seq)
    (seq' : ℕ → PlaneTiling (typedDecoration c))
    (herase : ∀ n, eraseSet c (seq' n).tiles = (seq n).tiles)
    (hexact : ∀ n, IsExactComposition c (seq' (n + 1)) (seq' n))
    (hleg : ∀ n, ∀ X ∈ (seq' n).tiles, headerLegal c (tileDec X))
    (X : PlacedTile (typedDecoration c)) (hX : X ∈ (seq' 0).tiles)
    (Z : (seq' 1).tiles) (blk : ColouredBlock c)
    (hblk_exact : IsExactBlockOfWith c (IsChildOf c) blk (tileDec Z.1) ∧ blk.v = c.σ.θ • Z.1.anchor)
    (hX_in_blk : X ∈ blk.tiles) :
    IsProperRealization c blk := by
  sorry

/-- Step 2.1.2 of the blueprint proof of `lift_hierarchy_step2_proper_step1_inner`: 
We use the fact that `blk` is a proper realization to find the matching tile `Y` inside `blk`. -/
private lemma lift_hierarchy_step2_proper_step1_inner_step2_match_in_blk (c : MacroCertificate P)
    (hH : c.Hereditary)
    (seq : ℕ → PlaneTiling c.Q) (hsts : HierarchySupertilesSTS c seq)
    (seq' : ℕ → PlaneTiling (typedDecoration c))
    (herase : ∀ n, eraseSet c (seq' n).tiles = (seq n).tiles)
    (hexact : ∀ n, IsExactComposition c (seq' (n + 1)) (seq' n))
    (hleg : ∀ n, ∀ X ∈ (seq' n).tiles, headerLegal c (tileDec X))
    (X : PlacedTile (typedDecoration c)) (hX : X ∈ (seq' 0).tiles)
    (i : c.Side (tileDec X).typ) (hInner : c.IsInner (c.occ (tileDec X).typ i))
    (hNontriv : IsNontrivial c (tileDec X) i)
    (Z : (seq' 1).tiles) (blk : ColouredBlock c)
    (hblk_exact : IsExactBlockOfWith c (IsChildOf c) blk (tileDec Z.1) ∧ blk.v = c.σ.θ • Z.1.anchor)
    (hX_in_blk : X ∈ blk.tiles)
    (hblk_proper : IsProperRealization c blk) :
    ∃ Y ∈ blk.tiles, Y ≠ X ∧ ∃ j : c.Side (tileDec Y).typ,
      sideOf c Y j = sideOf c X i ∧ ∀ k : Fin 5, (tileDec Y).cell j k = (tileDec X).cell i k := by
  sorry

/-- Step 2.1.3 of the blueprint proof of `lift_hierarchy_step2_proper_step1_inner`: 
We map the match `Y` back to `(seq' 0).tiles`. -/
private lemma lift_hierarchy_step2_proper_step1_inner_step3_map (c : MacroCertificate P)
    (hH : c.Hereditary)
    (seq : ℕ → PlaneTiling c.Q) (hsts : HierarchySupertilesSTS c seq)
    (seq' : ℕ → PlaneTiling (typedDecoration c))
    (herase : ∀ n, eraseSet c (seq' n).tiles = (seq n).tiles)
    (hexact : ∀ n, IsExactComposition c (seq' (n + 1)) (seq' n))
    (hleg : ∀ n, ∀ X ∈ (seq' n).tiles, headerLegal c (tileDec X))
    (X : PlacedTile (typedDecoration c)) (hX : X ∈ (seq' 0).tiles)
    (i : c.Side (tileDec X).typ) (hInner : c.IsInner (c.occ (tileDec X).typ i))
    (hNontriv : IsNontrivial c (tileDec X) i)
    (Z : (seq' 1).tiles) (blk : ColouredBlock c)
    (hblk_exact : IsExactBlockOfWith c (IsChildOf c) blk (tileDec Z.1) ∧ blk.v = c.σ.θ • Z.1.anchor)
    (blk_map : (seq' 1).tiles → ColouredBlock c)
    (hblk_union : (seq' 0).tiles = ⋃ W : (seq' 1).tiles, (blk_map W).tiles)
    (hZ_map : blk = blk_map Z)
    (hX_in_blk : X ∈ blk.tiles) :
    ∃ Y ∈ (seq' 0).tiles, Y ≠ X ∧ ∃ j : c.Side (tileDec Y).typ,
      sideOf c Y j = sideOf c X i ∧ ∀ k : Fin 5, (tileDec Y).cell j k = (tileDec X).cell i k := by
  have hblk_proper := lift_hierarchy_step2_proper_step1_inner_step1_proper_blk c hH seq hsts seq'
    herase hexact hleg X hX Z blk hblk_exact hX_in_blk
  have hY := lift_hierarchy_step2_proper_step1_inner_step2_match_in_blk c hH seq hsts seq' herase
    hexact hleg X hX i hInner hNontriv Z blk hblk_exact hX_in_blk hblk_proper
  rcases hY with ⟨Y, hY_blk, hY_ne, j, hY_side, hY_cell⟩
  refine ⟨Y, ?_, hY_ne, j, hY_side, hY_cell⟩
  rw [hblk_union]
  rw [hZ_map] at hY_blk
  exact mem_iUnion_of_mem Z hY_blk

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
  obtain ⟨blk_map, hbe, hbu⟩ := hexact 0
  have hXU : X ∈ ⋃ Z : (seq' 1).tiles, (blk_map Z).tiles := by
    rw [← hbu]
    exact hX
  rcases mem_iUnion.mp hXU with ⟨Z, hZ⟩
  exact lift_hierarchy_step2_proper_step1_inner_step3_map c hH seq hsts seq' herase hexact hleg
    X hX i hInner hNontriv Z (blk_map Z) (hbe Z) blk_map hbu rfl hZ

/-- Step 1 of the blueprint proof of `lift_hierarchy_step2_proper_step2_outer`:
For an outer side with nonzero fourth cell, its ancestor side becomes inner at a finite level.
Both overlapping sides therefore belong to one finite higher supertile.
The assumed STS property makes their descendant sides coincide completely. -/
private lemma lift_hierarchy_step2_proper_step2_outer_step1_supertile (c : MacroCertificate P)
    (hH : c.Hereditary)
    (seq : ℕ → PlaneTiling c.Q) (hsts : HierarchySupertilesSTS c seq)
    (seq' : ℕ → PlaneTiling (typedDecoration c))
    (herase : ∀ n, eraseSet c (seq' n).tiles = (seq n).tiles)
    (hexact : ∀ n, IsExactComposition c (seq' (n + 1)) (seq' n))
    (hleg : ∀ n, ∀ X ∈ (seq' n).tiles, headerLegal c (tileDec X))
    (X : PlacedTile (typedDecoration c)) (hX : X ∈ (seq' 0).tiles)
    (i : c.Side (tileDec X).typ) (hOuter : c.IsOuter (c.occ (tileDec X).typ i))
    (hNontriv : IsNontrivial c (tileDec X) i) :
    ∃ Y ∈ (seq' 0).tiles, Y ≠ X ∧ ∃ j : c.Side (tileDec Y).typ,
      sideOf c Y j = sideOf c X i := by
  sorry

/-- Step 2 of the blueprint proof of `lift_hierarchy_step2_proper_step2_outer`:
Their copied cells either reach the same shared origin, or matching origins on a shared side,
or both have no origin and are zero. The third cell of an outer side is nonzero only when
that side is a port. The coincident side of a port is the port of the same number of the
opposing block. Hence their full colours agree. -/
private lemma lift_hierarchy_step2_proper_step2_outer_step2_cells (c : MacroCertificate P)
    (hH : c.Hereditary)
    (seq : ℕ → PlaneTiling c.Q) (hsts : HierarchySupertilesSTS c seq)
    (seq' : ℕ → PlaneTiling (typedDecoration c))
    (herase : ∀ n, eraseSet c (seq' n).tiles = (seq n).tiles)
    (hexact : ∀ n, IsExactComposition c (seq' (n + 1)) (seq' n))
    (hleg : ∀ n, ∀ X ∈ (seq' n).tiles, headerLegal c (tileDec X))
    (X : PlacedTile (typedDecoration c)) (hX : X ∈ (seq' 0).tiles)
    (i : c.Side (tileDec X).typ) (hOuter : c.IsOuter (c.occ (tileDec X).typ i))
    (hNontriv : IsNontrivial c (tileDec X) i)
    (Y : PlacedTile (typedDecoration c)) (hY : Y ∈ (seq' 0).tiles) (hNeq : Y ≠ X)
    (j : c.Side (tileDec Y).typ) (hCoincide : sideOf c Y j = sideOf c X i) :
    ∀ k : Fin 5, (tileDec Y).cell j k = (tileDec X).cell i k := by
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
  rcases lift_hierarchy_step2_proper_step2_outer_step1_supertile c hH seq hsts seq' herase hexact
    hleg X hX i hOuter hNontriv with ⟨Y, hY, hNeq, j, hCoincide⟩
  exact ⟨Y, hY, hNeq, j, hCoincide, lift_hierarchy_step2_proper_step2_outer_step2_cells c hH seq
    hsts seq' herase hexact hleg X hX i hOuter hNontriv Y hY hNeq j hCoincide⟩

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

/-- Step 1 of the blueprint proof of `projects_to_hierarchy_step1_soundness`: repeated composition
yields a sequence of decorated tilings. -/
private lemma projects_to_hierarchy_step1_soundness_step1_composition
    (c : MacroCertificate P) (hH : c.Hereditary) :
    ∀ T : PlaneTiling (typedDecoration c), IsProper c T →
      (∀ X ∈ T.tiles, headerLegal c (tileDec X)) →
      ∃ seq : ℕ → PlaneTiling (typedDecoration c),
        seq 0 = T ∧
        (∀ n, IsProper c (seq n)) ∧
        (∀ n, ∀ X ∈ (seq n).tiles, headerLegal c (tileDec X)) ∧
        (∀ n, IsExactComposition c (seq (n + 1)) (seq n)) := by
  sorry

/-- Step 2 of the blueprint proof of `projects_to_hierarchy_step1_soundness`: erasure of a valid
decorated tiling gives an undecorated tiling. -/
private lemma projects_to_hierarchy_step1_soundness_step2_erase
    (c : MacroCertificate P) :
    ∀ T : PlaneTiling (typedDecoration c),
      ∃ T₀ : PlaneTiling c.Q, T₀.tiles = eraseSet c T.tiles := by
  sorry

/-- Step 3 of the blueprint proof of `projects_to_hierarchy_step1_soundness`: erasure commutes
with composition. -/
private lemma projects_to_hierarchy_step1_soundness_step3_erase_composition
    (c : MacroCertificate P) :
    ∀ T' T : PlaneTiling (typedDecoration c),
    ∀ T₀' T₀ : PlaneTiling c.Q,
      T₀'.tiles = eraseSet c T'.tiles →
      T₀.tiles = eraseSet c T.tiles →
      IsExactComposition c T' T →
      c.σ.IsComposition T₀' T₀ := by
  sorry

/-- Step 1 of the blueprint proof of `projects_to_hierarchy`: repeated composition
yields a hierarchical tiling. -/
private lemma projects_to_hierarchy_step1_soundness (c : MacroCertificate P) (hH : c.Hereditary) :
    ∀ T : PlaneTiling (typedDecoration c), IsProper c T →
      (∀ X ∈ T.tiles, headerLegal c (tileDec X)) →
      ∃ T₀ : PlaneTiling c.Q, T₀.tiles = eraseSet c T.tiles ∧ c.σ.IsHierarchical T₀ := by
  intro T hT hL
  have ⟨seq, hseq0, hseqP, hseqL, hseqC⟩ :=
    projects_to_hierarchy_step1_soundness_step1_composition c hH T hT hL
  have hseq_erase : ∀ n, ∃ T0 : PlaneTiling c.Q, T0.tiles = eraseSet c (seq n).tiles :=
    fun n ↦ projects_to_hierarchy_step1_soundness_step2_erase c (seq n)
  have ⟨seq0, hseq0_tiles⟩ := Classical.axiomOfChoice hseq_erase
  use seq0 0
  constructor
  · rw [hseq0_tiles 0, hseq0]
  · use seq0
    constructor
    · rfl
    · intro n
      exact projects_to_hierarchy_step1_soundness_step3_erase_composition c
        (seq (n + 1)) (seq n) (seq0 (n + 1)) (seq0 n)
        (hseq0_tiles (n + 1)) (hseq0_tiles n) (hseqC n)

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
