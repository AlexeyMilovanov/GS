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

/-- A cyclic index permutation has no fixed point when there are at least two
indices. -/
private theorem boundary_side_of_outer_side_step2_transition_finRotate_ne_self
    {N : ℕ} (hN : 2 ≤ N) (x : Fin N) : finRotate N x ≠ x := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have := congrArg (· - x) h
  simp at this

/-- The cyclic predicate transition used in Step 2: a predicate holding at one
index and failing at another changes from true to false at some successor. -/
private theorem boundary_side_of_outer_side_step2_transition_exists_rotate_transition
    {N : ℕ} (hN : 2 ≤ N) (p : Fin N → Prop) {i j : Fin N}
    (hi : p i) (hj : ¬ p j) : ∃ k, p k ∧ ¬ p (finRotate N k) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  by_contra hcon
  push_neg at hcon
  have hall : ∀ r : ℕ, p ((finRotate (n + 2) ^ r) i) := by
    intro r
    induction r with
    | zero => simpa using hi
    | succ r ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hcon _ ih
  obtain ⟨r, hr⟩ := isCycle_finRotate.exists_pow_eq
    (boundary_side_of_outer_side_step2_transition_finRotate_ne_self (by omega) i)
    (boundary_side_of_outer_side_step2_transition_finRotate_ne_self (by omega) j)
  exact hj (hr ▸ hall r)

/-- Step 2 of the blueprint proof of `boundary_side_of_outer_side`: Walk around its
boundary polygon from an outer side; the first side that is not outer starts at the
endpoint of the last outer side. This lemma states there is a pair of consecutive
sides where the first is outer and the second is inner. -/
private lemma boundary_side_of_outer_side_step2_transition (c : MacroCertificate P) (t : c.Typ)
    (i : c.Side t) (hi : c.IsOuter (c.occ t i)) (j : c.Side t) (hj : c.IsInner (c.occ t j)) :
    ∃ k : c.Side t, c.IsOuter (c.occ t k) ∧ c.IsInner (c.occ t (finRotate _ k)) := by
  exact boundary_side_of_outer_side_step2_transition_exists_rotate_transition
    (by have := (c.Q.disk (c.form t)).three_le; omega)
    (fun k => c.IsOuter (c.occ t k)) hi hj

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
  have _ := hH
  rcases hA with ⟨ch, hch0, hR, hcell⟩
  use ch 1
  constructor
  · use fun n => ch (n + 1)
    refine ⟨rfl, fun n => hR (n + 1), ?_⟩
    intro n i k hNE hNoOrig
    apply hcell (n + 1) i k hNE
    intro hOrig
    apply hNoOrig
    have h_ind : ∀ (m : ℕ) (j : c.Side (ch m).typ) (l : Fin 5),
        HasOrigin c ch m j l → ∀ (n' : ℕ) (h : m = n' + 1),
        HasOrigin c (fun x => ch (x + 1)) n' (cast (by rw [h]) j) l := by
      intro m j l hOrig
      induction hOrig with
      | origin m' j' l' h_eq =>
        intro n' hn'
        subst hn'
        exact HasOrigin.origin _ _ _ h_eq
      | step m' j' l' d k' h_mem h_orig' ih =>
        intro n' hn'
        subst hn'
        exact HasOrigin.step _ _ _ _ _ h_mem (ih (n' + 1) rfl)
    have := h_ind (n + 1) i k hOrig n rfl
    exact this
  · rw [← hch0]
    exact hR 0

/-- Auxiliary step for `headerLegal_properties_step2_normal_id_step1_normal`: the print
relation transports along an equality of owner forms. -/
private lemma headerLegal_properties_step2_normal_id_step1_normal_aux_cast_print
    (c : MacroCertificate P) {F1 F2 : c.Q.Form} (heq : F1 = F2)
    (d : Fin (c.Q.disk F1).n) (o : c.SideOcc) :
    c.IsPrintOf F1 d o ↔
      c.IsPrintOf F2 (cast (congrArg (fun F => Fin (c.Q.disk F).n) heq) d) o := by
  subst heq
  rfl

/-- Auxiliary step for `headerLegal_properties_step2_normal_id_step1_normal`: every side
occurrence listed on a path (genuine or trivial) is marked. -/
private lemma headerLegal_properties_step2_normal_id_step1_normal_aux_path_marked
    (c : MacroCertificate P) {α : c.Q.Form} {d : Fin (c.Q.disk α).n} {j : Fin 5}
    {o : c.SideOcc} (ho : o ∈ c.path α d j) : c.IsMarked o := by
  by_cases hg : c.IsGenuinePath α d j
  · exact c.g4_path_marked α d j hg o ho
  · rw [c.g4_path_trivial α d j hg, Option.mem_toList] at ho
    have hmem : o ∈ c.outerList α d := List.mem_iff_getElem?.mpr ⟨_, ho⟩
    exact c.g7_marking o (Or.inl ((c.g3_outerList_mem α d o).1 hmem).2.1)

/-- Step 1 of the blueprint proof of `headerLegal_properties_step2_normal_id`:
a legal tile is normal. -/
private lemma headerLegal_properties_step2_normal_id_step1_normal (c : MacroCertificate P)
    (A : DecTile c) (C : DecTile c) (h : IsChildOf c C A) :
    IsNormal c A := by
  intro i k hLoc
  by_cases hp : c.IsPrint (c.occ A.typ i)
  · have hmarked : c.IsMarked (c.occ A.typ i) :=
      c.g7_marking _ (Or.inr (Or.inr (Or.inl hp)))
    have hk4 : k = 4 := by
      rcases hLoc with h1 | h2 | h3
      · exact absurd hmarked h1
      · exact h2.2.2
      · exact absurd hp h3.2.1.2
    subst hk4
    have hpres : prescribedCell c (c.occ A.typ i) 4 = identU c (c.edge (c.occ A.typ i)) := by
      unfold prescribedCell
      simp [hp]
    obtain ⟨d0, hd0⟩ := hp
    have hd : c.IsPrintOf (c.form C.typ)
        (cast (congrArg (fun F => Fin (c.Q.disk F).n) h.1) d0) (c.occ A.typ i) :=
      (headerLegal_properties_step2_normal_id_step1_normal_aux_cast_print c h.1 d0
        (c.occ A.typ i)).1 hd0
    have hcl := ((h.2 i).1 _ hd).2
    show A.cell i 4 = prescribedCell c (c.occ A.typ i) 4
    rw [hpres]
    exact hcl
  · have hnc := (h.2 i).2 hp
    have h0 := hnc.1
    have h1 := hnc.2.1
    have h4 := hnc.2.2.1
    have hpath := hnc.2.2.2.1
    have hnopath := hnc.2.2.2.2.1
    have houter := hnc.2.2.2.2.2.1
    have hbdry := hnc.2.2.2.2.2.2.1
    have hinner := hnc.2.2.2.2.2.2.2
    fin_cases k
    · show A.cell i 0 = prescribedCell c (c.occ A.typ i) 0
      simpa [prescribedCell] using h0
    · show A.cell i 1 = prescribedCell c (c.occ A.typ i) 1
      simpa [prescribedCell] using h1
    · show A.cell i 2 = prescribedCell c (c.occ A.typ i) 2
      have hum : ¬ c.IsMarked (c.occ A.typ i) := by
        rcases hLoc with h' | h' | h'
        · exact h'
        · exact absurd h'.2.2 (by decide)
        · rcases h'.2.2 with h2 | h2
          · exact absurd h2 (by decide)
          · exact absurd h2 (by decide)
      have hnp : ∀ (d : c.Side C.typ) (j : Fin 5), c.occ A.typ i ∉ c.path (c.form C.typ) d j :=
        fun d j hin => hum
          (headerLegal_properties_step2_normal_id_step1_normal_aux_path_marked c hin)
      simpa [prescribedCell] using hnopath hnp
    · show A.cell i 3 = prescribedCell c (c.occ A.typ i) 3
      have hum : ¬ c.IsMarked (c.occ A.typ i) := by
        rcases hLoc with h' | h' | h'
        · exact h'
        · exact absurd h'.2.2 (by decide)
        · rcases h'.2.2 with h2 | h2
          · exact absurd h2 (by decide)
          · exact absurd h2 (by decide)
      have hNotOuter : ¬ c.IsOuter (c.occ A.typ i) :=
        fun hout => hum (c.g7_marking _ (Or.inl hout))
      have hin : c.IsInner (c.occ A.typ i) := hNotOuter
      have hNotBdry : ¬ c.IsBoundary (c.occ A.typ i) :=
        fun hb => hum (c.g7_marking _ (Or.inr (Or.inl hb)))
      have := hinner hin hNotBdry
      simpa [prescribedCell, hin, hNotBdry, hp] using this
    · show A.cell i 4 = prescribedCell c (c.occ A.typ i) 4
      simpa [prescribedCell, hp] using h4

/-- Step 2 of the blueprint proof of `headerLegal_properties_step2_normal_id`:
a legal tile is identity-correct. -/
private lemma headerLegal_properties_step2_normal_id_step2_identity (c : MacroCertificate P)
    (A : DecTile c) (C : DecTile c) (h : IsChildOf c C A) :
    IsIdentityCorrect c A := by
  dsimp [IsChildOf, headerSubstitution, IsChildOfWith] at h
  intro i
  constructor
  · intro h_inner h_nonprint
    have h_nonprint_i := (h.2 i).2 h_nonprint
    rw [h_nonprint_i.1]
    simp [prescribedFirst, h_inner]
  · intro h_print
    rcases h_print with ⟨d, h_print_of⟩
    have transport_print : ∀ {F G : c.Q.Form} (e : F = G)
        (d : Fin (c.Q.disk F).n),
        c.IsPrintOf F d (c.occ A.typ i) →
          c.IsPrintOf G (cast (congrArg (fun F => Fin (c.Q.disk F).n) e) d)
            (c.occ A.typ i) := by
      intro F G e d h_print_of
      cases e
      exact h_print_of
    let d' : c.Side C.typ :=
      cast (congrArg (fun F => Fin (c.Q.disk F).n) h.1) d
    have h_print_of' : c.IsPrintOf (c.form C.typ) d' (c.occ A.typ i) := by
      exact transport_print h.1 d h_print_of
    exact ((h.2 i).1 d' h_print_of').2

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


/-- Helper for `headerLegal_properties_step3_child_step1_zero`: a copied cell of a child equals
the corresponding source cell of the parent. -/
private lemma headerLegal_properties_step3_child_step1_zero_aux_copy (c : MacroCertificate P)
    (A B : DecTile c) (hB : IsChildOf c A B)
    (i : c.Side B.typ) (k : Fin 5) (p : c.Side A.typ × Fin 5)
    (hp : p ∈ copySource c (c.form A.typ) (c.occ B.typ i) k) :
    B.cell i k = A.cell p.1 p.2 := by
  obtain ⟨_, hi⟩ := hB
  obtain ⟨hprint, hnonprint⟩ := hi i
  rcases hp with ⟨hpr, hk4, hp2⟩ | ⟨hnp, hk2, hpath⟩
  · obtain ⟨hall, _⟩ := hprint p.1 hpr
    rw [hall k hk4, hp2]
  · subst hk2
    obtain ⟨_, _, _, hpatheq, _, _, _, _⟩ := hnonprint hnp
    exact hpatheq p.1 p.2 hpath

/-- Helper for `headerLegal_properties_step3_child_step1_zero`: prepending a first tile to a
chain shifts origins of the tail chain into origins of the new chain. -/
private lemma headerLegal_properties_step3_child_step1_zero_aux_shift (c : MacroCertificate P)
    (D0 : DecTile c) (ch : ℕ → DecTile c) (m : ℕ)
    (j : c.Side (ch m).typ) (l : Fin 5) (h_orig : HasOrigin c ch m j l) :
    HasOrigin c (fun n => match n with | 0 => D0 | n + 1 => ch n) (m + 1) j l := by
  induction h_orig with
  | origin m' j' l' h_eq => exact HasOrigin.origin _ _ _ h_eq
  | step m' j' l' d l'' h_mem h_orig' ih => exact HasOrigin.step _ _ _ _ _ h_mem ih

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
  have _ := hH
  subst hch0
  intro i k hcs hno
  obtain ⟨p, hp⟩ := hcs
  have hno1 : ¬ HasOrigin c (fun n => match n with | 0 => B | n + 1 => ch n) 1 p.1 p.2 := by
    intro h
    exact hno (HasOrigin.step (ch := fun n => match n with | 0 => B | n + 1 => ch n) 0 i k
      p.1 p.2 hp h)
  have hno0 : ¬ HasOrigin c ch 0 p.1 p.2 := fun h =>
    hno1 (headerLegal_properties_step3_child_step1_zero_aux_shift c B ch 0 p.1 p.2 h)
  have hcell_eq : B.cell i k = (ch 0).cell p.1 p.2 :=
    headerLegal_properties_step3_child_step1_zero_aux_copy c (ch 0) B hB i k p hp
  rw [hcell_eq]
  by_cases hNE : (copySource c (c.form (ch 1).typ) (c.occ (ch 0).typ p.1) p.2).Nonempty
  · exact hch_orig 0 p.1 p.2 hNE hno0
  · exact absurd (HasOrigin.origin (ch := ch) 0 p.1 p.2 (Set.not_nonempty_iff_eq_empty.mp hNE)) hno0

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

private lemma headerLegal_properties_step4_boundary_step1_print_not_boundary_aux_endpoints
    {a b c d : Pt} (hab : a ≠ b) (h : segment ℝ a b = segment ℝ c d) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  have mem_segment_iff' {x y z : Pt} :
      z ∈ segment ℝ x y ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = x + t • (y - x) := by
    rw [segment_eq_image']
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      exact ⟨t, ht0, ht1, rfl⟩
    · rintro ⟨t, ht0, ht1, rfl⟩
      exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
  have hc : c ∈ segment ℝ a b := h ▸ left_mem_segment ℝ c d
  have hd : d ∈ segment ℝ a b := h ▸ right_mem_segment ℝ c d
  have ha : a ∈ segment ℝ c d := h ▸ left_mem_segment ℝ a b
  have hb : b ∈ segment ℝ c d := h ▸ right_mem_segment ℝ a b
  rw [mem_segment_iff'] at hc hd ha hb
  obtain ⟨s, hs0, hs1, rfl⟩ := hc
  obtain ⟨t, ht0, ht1, rfl⟩ := hd
  obtain ⟨α, ha0, ha1, hα⟩ := ha
  obtain ⟨β, hb0, hb1, hβ⟩ := hb
  have hu : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have k1 : a + s • (b - a) + α • (a + t • (b - a) - (a + s • (b - a))) =
      a + (s + α * (t - s)) • (b - a) := by module
  have k2 : a + s • (b - a) + β • (a + t • (b - a) - (a + s • (b - a))) =
      a + (s + β * (t - s)) • (b - a) := by module
  rw [k1] at hα
  rw [k2] at hβ
  have e1 : (0 : ℝ) • (b - a) = (s + α * (t - s)) • (b - a) := by
    rw [zero_smul]
    exact (add_eq_left.1 hα.symm).symm
  have e2 : (1 : ℝ) • (b - a) = (s + β * (t - s)) • (b - a) := by
    rw [one_smul]
    have h' : a + (b - a) = a + (s + β * (t - s)) • (b - a) := by
      rw [← hβ]
      abel
    exact add_left_cancel h'
  have f1 := smul_left_injective ℝ hu e1
  have f2 := smul_left_injective ℝ hu e2
  have key : (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    have h3 : s * (1 - α) = 0 := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.2 ha1), mul_nonneg ha0 ht0]
    have h4 : α * t = 0 := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.2 ha1), mul_nonneg ha0 ht0]
    rcases mul_eq_zero.1 h3 with h3 | h3
    · subst h3
      have h' : β * t = 1 := by linarith
      left
      refine ⟨rfl, ?_⟩
      nlinarith
    · have hα1 : α = 1 := by linarith
      subst hα1
      have ht : t = 0 := by linarith
      subst ht
      right
      refine ⟨?_, rfl⟩
      nlinarith
  rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    constructor <;> simp
  · right
    constructor <;> simp

/-- Step 1 of the blueprint proof of `headerLegal_properties_step4_boundary`: a print side is
strictly internal to its template and therefore cannot be a boundary side. -/
private lemma headerLegal_properties_step4_boundary_step1_print_not_boundary
  (c : MacroCertificate P) (o : c.SideOcc) (h_print : c.IsPrint o) :
    ¬ c.IsBoundary o := by
  obtain ⟨d, hpd⟩ := h_print
  let α : c.Q.Form := c.owner o.1
  change c.marked α d ∧ (o = c.printOcc α d ∨ o = c.partner (c.printOcc α d)) at hpd
  rcases hpd with ⟨hmarked, hprint | hpartner⟩
  · rw [hprint]
    exact (c.g2_central α (c.print α d)).2
  · have hprint_inner := c.g4_print_inner α d hmarked
    obtain ⟨_hneq, howner, hside⟩ := c.g1_partner (c.printOcc α d) hprint_inner
    intro hboundary
    rw [hpartner] at hboundary
    unfold MacroData.IsBoundary at hboundary
    have howner_print : c.owner (c.printOcc α d).1 = α := by
      change c.owner (c.central α) = α
      exact c.g5_central_owner α
    rw [howner, howner_print] at hboundary
    have hboundary_print : c.IsBoundary (c.printOcc α d) := by
      unfold MacroData.IsBoundary
      rw [howner_print]
      refine ⟨hprint_inner, ?_⟩
      have hne : c.occStart (c.printOcc α d) ≠ c.occEnd (c.printOcc α d) := by
        intro hend
        have hvertex :
            (c.Q.disk (c.form (c.printOcc α d).1)).vertex (c.printOcc α d).2 =
              (c.Q.disk (c.form (c.printOcc α d).1)).vertex
                (finRotate _ (c.printOcc α d).2) := by
          exact vadd_left_cancel (c.anchor (c.printOcc α d).1) hend
        have hindex := (c.Q.disk (c.form (c.printOcc α d).1)).vertex_injective hvertex
        exact boundary_side_of_outer_side_step2_transition_finRotate_ne_self
          (by have := (c.Q.disk (c.form (c.printOcc α d).1)).three_le; omega)
          (c.printOcc α d).2 hindex.symm
      have hside' :
          segment ℝ (c.occStart (c.printOcc α d)) (c.occEnd (c.printOcc α d)) =
            segment ℝ (c.occStart (c.partner (c.printOcc α d)))
              (c.occEnd (c.partner (c.printOcc α d))) := by
        simpa [MacroData.occSide, MacroData.childTile, PlacedTile.side,
          PolygonalDisk.side, MacroData.occStart, MacroData.occEnd, vadd_segment] using hside.symm
      have hends :=
        headerLegal_properties_step4_boundary_step1_print_not_boundary_aux_endpoints hne hside'
      rcases hboundary.2 with hstart | hend
      · rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          rw [← h1]
          exact hstart
        · right
          rw [← h1]
          exact hstart
      · rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · right
          rw [← h2]
          exact hend
        · left
          rw [← h2]
          exact hend
    exact (c.g2_central α (c.print α d)).2 hboundary_print

/-- Step 4 of the blueprint proof of `headerLegal_properties`: all boundary fourth cells of a legal
tile equal one parent header. -/
private lemma headerLegal_properties_step4_boundary (c : MacroCertificate P) (hH : c.Hereditary)
    (A : DecTile c) (hA : headerLegal c A) :
    ∃ C, headerLegal c C ∧ IsChildOf c C A ∧
      ∀ i : c.Side A.typ, c.IsBoundary (c.occ A.typ i) → A.cell i 3 = headerU c (headerOf c C) := by
  obtain ⟨C, hC, hCA⟩ := headerLegal_properties_step1_parent c hH A hA
  refine ⟨C, hC, hCA, ?_⟩
  intro i hi
  have hnp : ¬ c.IsPrint (c.occ A.typ i) := fun hp =>
    headerLegal_properties_step4_boundary_step1_print_not_boundary c _ hp hi
  dsimp [IsChildOf, headerSubstitution, IsChildOfWith] at hCA
  exact (hCA.2 i).2 hnp |>.2.2.2.2.2.2.1 hi

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
  have _ := hH
  have _ := h_inner
  rcases hA with ⟨ch, hch0, hch_succ, _⟩
  have h_child : IsChildOf c (ch 1) A := by
    have h := hch_succ 0
    rw [hch0] at h
    exact h
  rcases h_print with ⟨d, hd⟩
  let d' : c.Side (ch 1).typ :=
    cast (congrArg (fun F => Fin (c.Q.disk F).n) h_child.1) d
  have transport_print : ∀ {F G : c.Q.Form} (e : F = G)
      (d : Fin (c.Q.disk F).n),
      c.IsPrintOf F d (c.occ A.typ i) →
        c.IsPrintOf G (cast (congrArg (fun F => Fin (c.Q.disk F).n) e) d)
          (c.occ A.typ i) := by
    intro F G e d h
    cases e
    exact h
  have hd' : c.IsPrintOf (c.form (ch 1).typ) d' (c.occ A.typ i) := by
    exact transport_print h_child.1 d hd
  have h_fifth : A.cell i 4 = identU c (c.edge (c.occ A.typ i)) :=
    ((h_child.2 i).1 d' hd').2
  unfold IsNontrivial
  intro h_zero
  have h_ident : identU c (c.edge (c.occ A.typ i)) = 0 :=
    h_fifth.symm.trans h_zero.2
  exact (by cases h_ident)

/-- Step 2 of the blueprint proof of `headerLegal_properties_step6_inner`: at a boundary side, the
fourth cell is a nonzero header tag. -/
private lemma headerLegal_properties_step6_inner_step2_nonprint_boundary (c : MacroCertificate P)
    (hH : c.Hereditary) (A : DecTile c) (hA : headerLegal c A) (i : c.Side A.typ)
    (h_inner : c.IsInner (c.occ A.typ i)) (h_nprint : ¬ c.IsPrint (c.occ A.typ i))
    (h_bdry : c.IsBoundary (c.occ A.typ i)) :
    IsNontrivial c A i := by
  have _ := h_inner
  have _ := hH
  rcases hA with ⟨ch, hch0, hch_succ, _⟩
  have hchild : IsChildOf c (ch 1) A := by
    rw [← hch0]
    exact hch_succ 0
  dsimp [IsChildOf, headerSubstitution, IsChildOfWith] at hchild
  have hi : A.cell i 3 = headerU c (headerOf c (ch 1)) :=
    (hchild.2 i).2 h_nprint |>.2.2.2.2.2.2.1 h_bdry
  intro htriv
  exact HeaderKernel.tagged_header_ne_zero (headerOf c (ch 1)) (hi ▸ htriv.1)

/-- Step 3 of the blueprint proof of `headerLegal_properties_step6_inner`: at any other inner side,
the fourth cell is \bot. -/
private lemma headerLegal_properties_step6_inner_step3_nonprint_nonboundary (c : MacroCertificate P)
    (hH : c.Hereditary) (A : DecTile c) (hA : headerLegal c A) (i : c.Side A.typ)
    (h_inner : c.IsInner (c.occ A.typ i)) (h_nprint : ¬ c.IsPrint (c.occ A.typ i))
    (h_nbdry : ¬ c.IsBoundary (c.occ A.typ i)) :
    IsNontrivial c A i := by
  have _ := hH
  rcases hA with ⟨ch, hch0, hch_child, _⟩
  have h_child_A : IsChildOf c (ch 1) A := by
    have h1 := hch_child 0
    rw [hch0] at h1
    exact h1
  have h_cell3 : A.cell i 3 = botU c :=
    ((h_child_A.2 i).2 h_nprint).2.2.2.2.2.2.2 h_inner h_nbdry
  have hne : botU c ≠ 0 := fun h => by cases h
  rintro ⟨h3, -⟩
  exact hne (h_cell3.symm.trans h3)

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
  have _ := hH
  have print_inner : ∀ {o : c.SideOcc}, c.IsPrint o → c.IsInner o := by
    intro o hp
    obtain ⟨d, hmk, ho | ho⟩ := hp
    · rw [ho]
      exact c.g4_print_inner _ d hmk
    · have hin := c.g4_print_inner _ d hmk
      obtain ⟨-, howner, hside⟩ := c.g1_partner _ hin
      rw [ho]
      unfold MacroData.IsInner MacroData.IsOuter at *
      rwa [hside, howner]
  intro i h_outer
  have h_nprint : ¬ c.IsPrint (c.occ A.typ i) := by
    intro h_print
    exact print_inner h_print h_outer
  rcases hA with ⟨ch, hch0, hch_succ, _⟩
  have h_child : IsChildOf c (ch 1) A := by
    have h := hch_succ 0
    rw [hch0] at h
    exact h
  dsimp [IsChildOf, headerSubstitution, IsChildOfWith] at h_child
  have h_fifth : A.cell i 4 = 0 :=
    ((h_child.2 i).2 h_nprint).2.2.1
  unfold IsNontrivial
  rw [h_fifth]
  simp

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

private lemma asm_isCompact_segment (x y : Pt) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

private lemma asm_frontier_vadd (a : Pt) (s : Set Pt) : frontier (a +ᵥ s) = a +ᵥ frontier s := by
  rw [← Set.image_vadd, ← Set.image_vadd]
  exact ((Homeomorph.vadd a).image_frontier s).symm

private lemma asm_vadd_cancel {S : Set Pt} (hS : IsCompact S) (hne : S.Nonempty) {a b : Pt}
    (h : a +ᵥ S = b +ᵥ S) : a = b := by
  obtain ⟨x0, hx0, hmax⟩ := hS.exists_isMaxOn hne
    ((continuous_id.inner continuous_const : Continuous fun x : Pt => inner ℝ x (a - b)).continuousOn)
  have h1 : a +ᵥ x0 ∈ b +ᵥ S := h ▸ Set.vadd_mem_vadd_set hx0
  obtain ⟨y, hy, hxy⟩ := h1
  have hy' : y = (a - b) + x0 := by
    simp only [vadd_eq_add] at hxy
    rw [sub_add_eq_add_sub, ← hxy]
    abel
  have h2 := hmax hy
  simp only [Set.mem_setOf_eq, id] at h2
  rw [hy', inner_add_left, real_inner_self_eq_norm_sq] at h2
  have h3 : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h3)

private lemma asm_half_disk (C : Set Pt) (hC : IsClosed C) (hreg : closure (interior C) = C)
    (ℓ : Pt →L[ℝ] ℝ) (m : Pt) (hm : m ∈ C) (r : ℝ) (hr : 0 < r)
    (hfr : ∀ x ∈ Metric.ball m r, x ∈ frontier C ↔ ℓ x = ℓ m) :
    Metric.ball m r ∩ {x | ℓ m < ℓ x} ⊆ interior C ∨
      Metric.ball m r ∩ {x | ℓ x < ℓ m} ⊆ interior C := by
  have key : ∀ H : Set Pt, H ⊆ Metric.ball m r → Convex ℝ H → (∀ x ∈ H, ℓ x ≠ ℓ m) →
      H ⊆ interior C ∨ H ⊆ Cᶜ := by
    intro H hHb hHc hHl
    apply hHc.isPreconnected.subset_or_subset isOpen_interior hC.isOpen_compl
    · exact Disjoint.mono_left interior_subset disjoint_compl_right
    · intro x hx
      by_cases hxC : x ∈ C
      · left
        by_contra hni
        exact hHl x hx ((hfr x (hHb hx)).1 ⟨subset_closure hxC, hni⟩)
      · exact Or.inr hxC
  have hP := key (Metric.ball m r ∩ {x | ℓ m < ℓ x}) inter_subset_left
    ((convex_ball m r).inter (convex_halfSpace_gt ℓ.toLinearMap.isLinear _))
    (fun x hx => ne_of_gt hx.2)
  have hN := key (Metric.ball m r ∩ {x | ℓ x < ℓ m}) inter_subset_left
    ((convex_ball m r).inter (convex_halfSpace_lt ℓ.toLinearMap.isLinear _))
    (fun x hx => ne_of_lt hx.2)
  rcases hP with hP | hP
  · exact Or.inl hP
  rcases hN with hN | hN
  · exact Or.inr hN
  exfalso
  have hm' : m ∈ closure (interior C) := hreg.symm ▸ hm
  obtain ⟨x, hxi, hxd⟩ := Metric.mem_closure_iff.1 hm' r hr
  have hxb : x ∈ Metric.ball m r := by rw [Metric.mem_ball, dist_comm]; exact hxd
  have hxC : x ∈ C := interior_subset hxi
  have hxf : ℓ x ≠ ℓ m := fun he => ((hfr x hxb).2 he).2 hxi
  rcases lt_or_gt_of_ne hxf with h | h
  · exact hN ⟨hxb, h⟩ hxC
  · exact hP ⟨hxb, h⟩ hxC

private lemma asm_midpoint_ne {E F P Q : Pt} (hPQ : P ≠ Q) (h : segment ℝ E F = segment ℝ P Q) :
    midpoint ℝ P Q ≠ E := by
  intro hm
  have hP : P ∈ segment ℝ E F := h ▸ left_mem_segment ℝ P Q
  have hQ : Q ∈ segment ℝ E F := h ▸ right_mem_segment ℝ P Q
  rw [segment_eq_image'] at hP hQ
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hP
  obtain ⟨u, ⟨hu0, hu1⟩, rfl⟩ := hQ
  have hE : midpoint ℝ (E + s • (F - E)) (E + u • (F - E)) = E := hm
  rw [midpoint_eq_smul_add] at hE
  have h3 : (s + u) • (F - E) = 0 := by
    have h4 : (s + u) • (F - E) =
        (2:ℝ) • ((⅟2 : ℝ) • (E + s • (F - E) + (E + u • (F - E)))) - (2:ℝ) • E := by
      rw [smul_smul]; norm_num; rw [add_smul, two_smul]; abel
    rw [h4, hE, sub_self]
  rcases smul_eq_zero.1 h3 with h5 | h5
  · have hs : s = 0 := by linarith
    have hu : u = 0 := by linarith
    subst hs hu; simp at hPQ
  · simp [h5] at hPQ

/-- A linear functional vanishing exactly on the direction `d`. -/
private def asmNormal (d : Pt) : Pt →L[ℝ] ℝ :=
  (d 0) • EuclideanSpace.proj (1 : Fin 2) - (d 1) • EuclideanSpace.proj (0 : Fin 2)

private lemma asmNormal_apply (d x : Pt) : asmNormal d x = d 0 * x 1 - d 1 * x 0 := by
  simp [asmNormal]

private lemma asmNormal_segment {P Q x : Pt} (hx : x ∈ segment ℝ P Q) :
    asmNormal (Q - P) x = asmNormal (Q - P) P := by
  rw [segment_eq_image'] at hx
  obtain ⟨t, -, rfl⟩ := hx
  simp only [asmNormal_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  ring

private lemma asm_midpoint_apply (P Q : Pt) (i : Fin 2) : (midpoint ℝ P Q) i = (P i + Q i) / 2 := by
  rw [midpoint_eq_smul_add]
  simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  rw [invOf_eq_inv]; ring

private lemma asm_ball_line_real (p0 p1 q0 q1 x0 x1 : ℝ) (hD : 0 < (q0 - p0) ^ 2 + (q1 - p1) ^ 2)
    (hW : (x0 - (p0 + q0) / 2) ^ 2 + (x1 - (p1 + q1) / 2) ^ 2 < ((q0 - p0) ^ 2 + (q1 - p1) ^ 2) / 4)
    (hl : (q0 - p0) * x1 - (q1 - p1) * x0 = (q0 - p0) * ((p1 + q1) / 2) - (q1 - p1) * ((p0 + q0) / 2)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ x0 = p0 + θ * (q0 - p0) ∧ x1 = p1 + θ * (q1 - p1) := by
  obtain ⟨d0, hd0⟩ : ∃ d0, d0 = q0 - p0 := ⟨_, rfl⟩
  obtain ⟨d1, hd1⟩ : ∃ d1, d1 = q1 - p1 := ⟨_, rfl⟩
  obtain ⟨w0, hw0⟩ : ∃ w0, w0 = x0 - (p0 + q0) / 2 := ⟨_, rfl⟩
  obtain ⟨w1, hw1⟩ : ∃ w1, w1 = x1 - (p1 + q1) / 2 := ⟨_, rfl⟩
  rw [← hd0, ← hd1] at hD hW
  rw [← hw0, ← hw1] at hW
  have hl' : d0 * w1 - d1 * w0 = 0 := by rw [hd0, hd1, hw0, hw1]; linear_combination hl
  have hlag : (w0 * d0 + w1 * d1) ^ 2 + (d0 * w1 - d1 * w0) ^ 2 =
      (w0 ^ 2 + w1 ^ 2) * (d0 ^ 2 + d1 ^ 2) := by ring
  rw [hl'] at hlag
  obtain ⟨t, ht⟩ : ∃ t, t = (w0 * d0 + w1 * d1) / (d0 ^ 2 + d1 ^ 2) := ⟨_, rfl⟩
  have htD : t * (d0 ^ 2 + d1 ^ 2) = w0 * d0 + w1 * d1 := by
    rw [ht]; field_simp
  have ht2 : t ^ 2 * (d0 ^ 2 + d1 ^ 2) < (d0 ^ 2 + d1 ^ 2) / 4 := by
    have : (t ^ 2 * (d0 ^ 2 + d1 ^ 2)) * (d0 ^ 2 + d1 ^ 2) = (w0 ^ 2 + w1 ^ 2) * (d0 ^ 2 + d1 ^ 2) := by
      rw [← hlag, ← htD]; ring
    have h5 : t ^ 2 * (d0 ^ 2 + d1 ^ 2) = w0 ^ 2 + w1 ^ 2 := mul_right_cancel₀ hD.ne' this
    linarith
  have ht3 : t ^ 2 < 1 / 4 := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hwt0 : w0 * (d0 ^ 2 + d1 ^ 2) = t * d0 * (d0 ^ 2 + d1 ^ 2) := by
    linear_combination (-d1) * hl' - d0 * htD
  have hwt1 : w1 * (d0 ^ 2 + d1 ^ 2) = t * d1 * (d0 ^ 2 + d1 ^ 2) := by
    linear_combination d0 * hl' - d1 * htD
  have e0 := mul_right_cancel₀ hD.ne' hwt0
  have e1 := mul_right_cancel₀ hD.ne' hwt1
  refine ⟨1 / 2 + t, by nlinarith, by nlinarith, ?_, ?_⟩
  · linear_combination -hw0 + e0 + t * hd0
  · linear_combination -hw1 + e1 + t * hd1

private lemma asm_ball_line {P Q x : Pt} (hPQ : P ≠ Q)
    (hx : dist x (midpoint ℝ P Q) < dist P Q / 2)
    (hl : asmNormal (Q - P) x = asmNormal (Q - P) (midpoint ℝ P Q)) : x ∈ segment ℝ P Q := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq] at hx
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hx
  rw [asmNormal_apply, asmNormal_apply] at hl
  simp only [asm_midpoint_apply, PiLp.sub_apply] at hx hl
  have hD : 0 < (Q 0 - P 0) ^ 2 + (Q 1 - P 1) ^ 2 := by
    by_contra hcon
    apply hPQ
    have h0 : Q 0 - P 0 = 0 := by nlinarith [sq_nonneg (Q 0 - P 0), sq_nonneg (Q 1 - P 1)]
    have h1 : Q 1 - P 1 = 0 := by nlinarith [sq_nonneg (Q 0 - P 0), sq_nonneg (Q 1 - P 1)]
    ext i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; linarith
    · simp only [Fin.mk_one, Fin.isValue]; linarith
  have hW : (x 0 - (P 0 + Q 0) / 2) ^ 2 + (x 1 - (P 1 + Q 1) / 2) ^ 2 <
      ((Q 0 - P 0) ^ 2 + (Q 1 - P 1) ^ 2) / 4 := by
    have h1 := hx
    rw [show (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 = (Q 0 - P 0) ^ 2 + (Q 1 - P 1) ^ 2 by ring] at h1
    have h2 : Real.sqrt ((Q 0 - P 0) ^ 2 + (Q 1 - P 1) ^ 2) / 2 =
        Real.sqrt (((Q 0 - P 0) ^ 2 + (Q 1 - P 1) ^ 2) / 4) := by
      rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4), show (4:ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    rw [h2] at h1
    exact (Real.sqrt_lt_sqrt_iff (by positivity)).1 h1
  obtain ⟨θ, h0, h1, e0, e1⟩ := asm_ball_line_real (P 0) (P 1) (Q 0) (Q 1) (x 0) (x 1) hD hW hl
  rw [segment_eq_image']
  refine ⟨θ, ⟨h0, h1⟩, ?_⟩
  ext i
  fin_cases i
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Fin.zero_eta, Fin.isValue]
    rw [e0]
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Fin.mk_one, Fin.isValue]
    rw [e1]

private lemma asm_local_frontier (B : PolygonalDisk) (k : Fin B.n) (m : Pt) (hm : m ∈ B.side k)
    (h1 : m ≠ B.vertex k) (h2 : m ≠ B.vertex (finRotate B.n k)) :
    ∃ r > 0, Metric.ball m r ∩ frontier B.carrier ⊆ B.side k := by
  set U := ⋃ k' ∈ ({k}ᶜ : Set (Fin B.n)), B.side k' with hUdef
  have hU : IsClosed U :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) (fun k' _ => (asm_isCompact_segment _ _).isClosed)
  have hmU : m ∉ U := by
    rw [hUdef]
    simp only [Set.mem_iUnion]
    rintro ⟨k', hk', hmk'⟩
    have := B.simple k k' (Ne.symm hk') ⟨hm, hmk'⟩
    rcases this.1 with h | h
    · exact h1 h
    · exact h2 h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU.isOpen_compl m hmU
  refine ⟨r, hr, ?_⟩
  rintro x ⟨hxb, hxf⟩
  rw [B.frontier_eq] at hxf
  obtain ⟨k'', hk''⟩ := Set.mem_iUnion.1 hxf
  by_cases hk : k'' = k
  · subst hk; exact hk''
  · exact absurd (Set.mem_biUnion (x := k'') hk hk'') (hball hxb)

private lemma asm_side_sub_carrier (B : PolygonalDisk) (k : Fin B.n) : B.side k ⊆ frontier B.carrier := by
  rw [B.frontier_eq]; exact Set.subset_iUnion (fun i => segment ℝ (B.vertex i) (B.vertex (finRotate B.n i))) k

private lemma asm_finRotate_ne (n : ℕ) (hn : 3 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have h' : (i + 1).val = i.val := congrArg Fin.val h
  rw [Fin.val_add] at h'
  have h1 : (1 : Fin (m + 1)).val = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  rw [h1] at h'
  have := i.isLt
  by_cases hi : i.val + 1 < m + 1
  · rw [Nat.mod_eq_of_lt hi] at h'; omega
  · have : i.val + 1 = m + 1 := by omega
    rw [this, Nat.mod_self] at h'; omega

private lemma asm_halves_nonempty (P Q : Pt) (hPQ : P ≠ Q) (r : ℝ) (hr : 0 < r) :
    (Metric.ball (midpoint ℝ P Q) r ∩
        {x | asmNormal (Q - P) (midpoint ℝ P Q) < asmNormal (Q - P) x}).Nonempty ∧
      (Metric.ball (midpoint ℝ P Q) r ∩
        {x | asmNormal (Q - P) x < asmNormal (Q - P) (midpoint ℝ P Q)}).Nonempty := by
  set ℓ := asmNormal (Q - P)
  set m := midpoint ℝ P Q
  have hne : Q - P ≠ 0 := sub_ne_zero.mpr hPQ.symm
  obtain ⟨w, hw⟩ : ∃ w : Pt, 0 < ℓ w := by
    by_cases h0 : (Q - P) 0 = 0
    · have h1 : (Q - P) 1 ≠ 0 := by
        intro h1; apply hne; ext i; fin_cases i
        · simpa using h0
        · simpa using h1
      refine ⟨(-(Q - P) 1) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ), ?_⟩
      rw [ℓ.map_smul]
      simp only [ℓ, asmNormal_apply, EuclideanSpace.single_apply, smul_eq_mul]
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
      nlinarith [sq_pos_of_ne_zero h1]
    · refine ⟨((Q - P) 0) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ), ?_⟩
      rw [ℓ.map_smul]
      simp only [ℓ, asmNormal_apply, EuclideanSpace.single_apply, smul_eq_mul]
      simp only [Fin.isValue, ↓reduceIte, zero_ne_one]
      nlinarith [sq_pos_of_ne_zero h0]
  set c := r / (2 * (‖w‖ + 1)) with hc
  have hc0 : 0 < c := by positivity
  have hcw : c * ‖w‖ < r := by
    rw [hc, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg w]
  constructor
  · refine ⟨m + c • w, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hc0.le]
      exact hcw
    · show ℓ m < ℓ (m + c • w)
      rw [ℓ.map_add, ℓ.map_smul, smul_eq_mul]; nlinarith
  · refine ⟨m - c • w, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_of_nonneg hc0.le]
      exact hcw
    · show ℓ (m - c • w) < ℓ m
      rw [ℓ.map_sub, ℓ.map_smul, smul_eq_mul]; nlinarith

private lemma asm_tile_half (B : PolygonalDisk) (a : Pt) (k : Fin B.n) {P Q : Pt} (hPQ : P ≠ Q)
    (hS : a +ᵥ B.side k = segment ℝ P Q) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      Metric.ball (midpoint ℝ P Q) r' ∩
          {x | asmNormal (Q - P) (midpoint ℝ P Q) < asmNormal (Q - P) x} ⊆ interior (a +ᵥ B.carrier) ∨
        Metric.ball (midpoint ℝ P Q) r' ∩
          {x | asmNormal (Q - P) x < asmNormal (Q - P) (midpoint ℝ P Q)} ⊆ interior (a +ᵥ B.carrier) := by
  set m := midpoint ℝ P Q with hmdef
  have hS' : segment ℝ (a +ᵥ B.vertex k) (a +ᵥ B.vertex (finRotate B.n k)) = segment ℝ P Q := by
    rw [← vadd_segment]; exact hS
  have hm1 : m ≠ a +ᵥ B.vertex k := asm_midpoint_ne hPQ hS'
  have hm2 : m ≠ a +ᵥ B.vertex (finRotate B.n k) :=
    asm_midpoint_ne hPQ ((segment_symm ℝ _ _).trans hS')
  have hmS : m ∈ a +ᵥ B.side k := hS ▸ midpoint_mem_segment P Q
  obtain ⟨y, hy, hya⟩ := hmS
  have hy1 : y ≠ B.vertex k := fun h => hm1 (by rw [← hya, h])
  have hy2 : y ≠ B.vertex (finRotate B.n k) := fun h => hm2 (by rw [← hya, h])
  obtain ⟨r0, hr0, hloc⟩ := asm_local_frontier B k y hy hy1 hy2
  have hdPQ : 0 < dist P Q := dist_pos.mpr hPQ
  refine ⟨min r0 (dist P Q / 2), lt_min hr0 (by linarith), fun r' hr' hr'le => ?_⟩
  have hBc : IsClosed B.carrier := B.compact.isClosed
  apply asm_half_disk (a +ᵥ B.carrier) (hBc.vadd a)
    (by rw [interior_vadd, closure_vadd, B.regular_closed]) (asmNormal (Q - P)) m
    (by
      rw [← hya]
      exact Set.vadd_mem_vadd_set (hBc.frontier_subset (asm_side_sub_carrier B k hy)))
    r' hr'
  intro x hx
  rw [asm_frontier_vadd]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzb : z ∈ Metric.ball y r0 := by
      have hya' : a +ᵥ y = m := hya
      rw [Metric.mem_ball, ← dist_vadd_cancel_left a z y, hya']
      exact lt_of_lt_of_le (Metric.mem_ball.1 hx) ((min_le_left _ _).trans' hr'le)
    have hzs : a +ᵥ z ∈ segment ℝ P Q := hS ▸ Set.vadd_mem_vadd_set (hloc ⟨hzb, hz⟩)
    rw [asmNormal_segment hzs, asmNormal_segment (midpoint_mem_segment P Q)]
  · intro hl
    have hxs : x ∈ segment ℝ P Q := by
      apply asm_ball_line hPQ _ hl
      exact lt_of_lt_of_le (Metric.mem_ball.1 hx) (hr'le.trans (min_le_right _ _))
    rw [← hS] at hxs
    obtain ⟨z, hz, rfl⟩ := hxs
    exact Set.vadd_mem_vadd_set (asm_side_sub_carrier B k hz)

private lemma asm_no_three (B₁ B₂ B₃ : PolygonalDisk) (a₁ a₂ a₃ : Pt) (k₁ : Fin B₁.n) (k₂ : Fin B₂.n)
    (k₃ : Fin B₃.n) (h₂ : a₂ +ᵥ B₂.side k₂ = a₁ +ᵥ B₁.side k₁) (h₃ : a₃ +ᵥ B₃.side k₃ = a₁ +ᵥ B₁.side k₁)
    (d₁₂ : Disjoint (interior (a₁ +ᵥ B₁.carrier)) (interior (a₂ +ᵥ B₂.carrier)))
    (d₁₃ : Disjoint (interior (a₁ +ᵥ B₁.carrier)) (interior (a₃ +ᵥ B₃.carrier)))
    (d₂₃ : Disjoint (interior (a₂ +ᵥ B₂.carrier)) (interior (a₃ +ᵥ B₃.carrier))) : False := by
  set P := a₁ +ᵥ B₁.vertex k₁
  set Q := a₁ +ᵥ B₁.vertex (finRotate B₁.n k₁)
  have hPQ : P ≠ Q := by
    intro h
    exact asm_finRotate_ne B₁.n B₁.three_le k₁ (B₁.vertex_injective (vadd_left_cancel a₁ h)).symm
  have hS : a₁ +ᵥ B₁.side k₁ = segment ℝ P Q := vadd_segment ℝ a₁ _ _
  obtain ⟨r₁, hr₁, H₁⟩ := asm_tile_half B₁ a₁ k₁ hPQ hS
  obtain ⟨r₂, hr₂, H₂⟩ := asm_tile_half B₂ a₂ k₂ hPQ (h₂.trans hS)
  obtain ⟨r₃, hr₃, H₃⟩ := asm_tile_half B₃ a₃ k₃ hPQ (h₃.trans hS)
  set r := min r₁ (min r₂ r₃)
  have hr : 0 < r := lt_min hr₁ (lt_min hr₂ hr₃)
  obtain ⟨⟨xp, hxp⟩, ⟨xn, hxn⟩⟩ := asm_halves_nonempty P Q hPQ r hr
  rcases H₁ r hr (min_le_left _ _) with A₁ | A₁ <;>
  rcases H₂ r hr ((min_le_right _ _).trans (min_le_left _ _)) with A₂ | A₂ <;>
  rcases H₃ r hr ((min_le_right _ _).trans (min_le_right _ _)) with A₃ | A₃
  · exact Set.disjoint_left.1 d₁₂ (A₁ hxp) (A₂ hxp)
  · exact Set.disjoint_left.1 d₁₂ (A₁ hxp) (A₂ hxp)
  · exact Set.disjoint_left.1 d₁₃ (A₁ hxp) (A₃ hxp)
  · exact Set.disjoint_left.1 d₂₃ (A₂ hxn) (A₃ hxn)
  · exact Set.disjoint_left.1 d₂₃ (A₂ hxp) (A₃ hxp)
  · exact Set.disjoint_left.1 d₁₃ (A₁ hxn) (A₃ hxn)
  · exact Set.disjoint_left.1 d₁₂ (A₁ hxn) (A₂ hxn)
  · exact Set.disjoint_left.1 d₁₂ (A₁ hxn) (A₂ hxn)

private lemma asm_identU_ne_zero (c : MacroCertificate P) (e : c.EdgeId) : identU c e ≠ 0 := by
  intro h; cases h

private lemma asm_identU_inj (c : MacroCertificate P) {e e' : c.EdgeId} (h : identU c e = identU c e') :
    e = e' := by
  simp only [identU] at h
  cases h; rfl

private lemma asm_isLocal_four (c : MacroCertificate P) (o : c.SideOcc) : IsLocal c o 4 := by
  by_cases hm : c.IsMarked o
  · by_cases hs : c.special o ∨ c.IsPrint o
    · exact Or.inr (Or.inl ⟨hm, hs, rfl⟩)
    · push_neg at hs
      exact Or.inr (Or.inr ⟨hm, ⟨hs.1, hs.2⟩, Or.inr rfl⟩)
  · exact Or.inl hm

private lemma asm_cell_four_print (c : MacroCertificate P) {A : DecTile c} (hA : IsNormal c A)
    (i : c.Side A.typ) (hp : c.IsPrint (c.occ A.typ i)) : A.cell i 4 = identU c (c.edge (c.occ A.typ i)) := by
  rw [hA i 4 (asm_isLocal_four c _)]
  simp [prescribedCell, hp]

private lemma asm_cell_four_nonprint (c : MacroCertificate P) {A : DecTile c} (hA : IsNormal c A)
    (i : c.Side A.typ) (hp : ¬ c.IsPrint (c.occ A.typ i)) : A.cell i 4 = 0 := by
  rw [hA i 4 (asm_isLocal_four c _)]
  simp [prescribedCell, hp]

private lemma asm_inner_of_occSide (c : MacroCertificate P) {o o' : c.SideOcc} (ho : c.IsInner o)
    (hown : c.owner o'.1 = c.owner o.1) (hs : c.occSide o' = c.occSide o) : c.IsInner o' := by
  unfold MacroData.IsInner MacroData.IsOuter at *
  rwa [hs, hown]

private lemma asm_print_inner (c : MacroCertificate P) {o : c.SideOcc} (hp : c.IsPrint o) : c.IsInner o := by
  obtain ⟨d, hmk, ho | ho⟩ := hp
  · rw [ho]; exact c.g4_print_inner _ d hmk
  · have hin := c.g4_print_inner _ d hmk
    obtain ⟨-, h2, h3⟩ := c.g1_partner _ hin
    rw [ho]; exact asm_inner_of_occSide c hin h2 h3

private lemma asm_cell_zero_outer (c : MacroCertificate P) {A : DecTile c} (hA : IsNormal c A)
    (i : c.Side A.typ) (ho : c.IsOuter (c.occ A.typ i)) : A.cell i 0 = 0 := by
  have hloc : IsLocal c (c.occ A.typ i) 0 := by
    by_cases hm : c.IsMarked (c.occ A.typ i)
    · exact Or.inr (Or.inr ⟨hm, ⟨fun hs => c.g6_special_inner _ hs ho,
        fun hp => asm_print_inner c hp ho⟩, Or.inl rfl⟩)
    · exact Or.inl hm
  rw [hA i 0 hloc]
  have hni : ¬ c.IsInner (c.occ A.typ i) := fun h => h ho
  simp [prescribedCell, prescribedFirst, hni]

private lemma asm_match (c : MacroCertificate P) {A B : DecTile c} (hA : IsNormal c A ∧ IsIdentityCorrect c A)
    (hB : IsNormal c B ∧ IsIdentityCorrect c B) (i : c.Side A.typ) (j : c.Side B.typ)
    (hi : c.IsInner (c.occ A.typ i)) (hc : ∀ k, B.cell j k = A.cell i k) :
    c.IsInner (c.occ B.typ j) ∧ c.edge (c.occ B.typ j) = c.edge (c.occ A.typ i) := by
  by_cases hp : c.IsPrint (c.occ A.typ i)
  · have h4 : A.cell i 4 = identU c (c.edge (c.occ A.typ i)) := (hA.2 i).2 hp
    by_cases hq : c.IsPrint (c.occ B.typ j)
    · refine ⟨asm_print_inner c hq, asm_identU_inj c ?_⟩
      rw [← asm_cell_four_print c hB.1 j hq, hc 4, h4]
    · exfalso
      have h5 := asm_cell_four_nonprint c hB.1 j hq
      rw [hc 4, h4] at h5
      exact asm_identU_ne_zero c _ h5
  · have h0 : A.cell i 0 = identU c (c.edge (c.occ A.typ i)) := (hA.2 i).1 hi hp
    have hq : ¬ c.IsPrint (c.occ B.typ j) := by
      intro hq
      have h5 := asm_cell_four_print c hB.1 j hq
      rw [hc 4, asm_cell_four_nonprint c hA.1 i hp] at h5
      exact asm_identU_ne_zero c _ h5.symm
    have hin : c.IsInner (c.occ B.typ j) := by
      intro ho
      have h5 := asm_cell_zero_outer c hB.1 j ho
      rw [hc 0, h0] at h5
      exact asm_identU_ne_zero c _ h5
    refine ⟨hin, asm_identU_inj c ?_⟩
    rw [← (hB.2 j).1 hin hq, hc 0, h0]

private lemma asm_tile_unique (c : MacroCertificate P) (T : PlaneTiling (typedDecoration c))
    {X Y : PlacedTile (typedDecoration c)} (hX : X ∈ T.tiles) (hY : Y ∈ T.tiles)
    (ht : (tileDec X).typ = (tileDec Y).typ) (ha : X.anchor = Y.anchor) : X = Y := by
  by_contra hne
  have hd : Disjoint (interior X.carrier) (interior Y.carrier) := T.disjoint hX hY hne
  have hXc : X.carrier = X.anchor +ᵥ (c.Q.disk (c.form (tileDec X).typ)).carrier := rfl
  have hYc : Y.carrier = Y.anchor +ᵥ (c.Q.disk (c.form (tileDec Y).typ)).carrier := rfl
  rw [hXc, hYc, ht, ha] at hd
  obtain ⟨z, hz⟩ := (c.Q.disk (c.form (tileDec Y).typ)).interior_nonempty
  have hz' : Y.anchor +ᵥ z ∈ interior (Y.anchor +ᵥ (c.Q.disk (c.form (tileDec Y).typ)).carrier) := by
    rw [interior_vadd]; exact Set.vadd_mem_vadd_set hz
  exact Set.disjoint_left.1 hd hz' hz'

/-- The placed segment of a side occurrence translated by `a`. -/
private def asmSide (c : MacroCertificate P) (a : Pt) (o : c.SideOcc) : Set Pt :=
  a +ᵥ (c.Q.disk (c.form o.1)).side o.2

private lemma asm_side_cancel (c : MacroCertificate P) {a b : Pt} {o : c.SideOcc}
    (h : asmSide c a o = asmSide c b o) : a = b :=
  asm_vadd_cancel (asm_isCompact_segment _ _) ⟨_, left_mem_segment ℝ _ _⟩ h

private lemma asm_neighbour (c : MacroCertificate P) (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hN : ∀ X ∈ T.tiles, IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
      InnerActive c (tileDec X))
    {X : PlacedTile (typedDecoration c)} (hX : X ∈ T.tiles) (i : c.Side (tileDec X).typ)
    (hi : c.IsInner (c.occ (tileDec X).typ i)) :
    ∃ Y ∈ T.tiles, (tileDec Y).typ = (c.partner (c.occ (tileDec X).typ i)).1 ∧
      Y.anchor = X.anchor - c.anchor (tileDec X).typ + c.anchor (c.partner (c.occ (tileDec X).typ i)).1 := by
  obtain ⟨hNX, hIX, hAX⟩ := hN X hX
  obtain ⟨Y, hY, hYX, j, hside, hcell⟩ := hT X hX i (hAX i hi)
  obtain ⟨hNY, hIY, -⟩ := hN Y hY
  obtain ⟨hjin, hje⟩ := asm_match c ⟨hNX, hIX⟩ ⟨hNY, hIY⟩ i j hi hcell
  have hside' : asmSide c Y.anchor (c.occ (tileDec Y).typ j) =
      asmSide c X.anchor (c.occ (tileDec X).typ i) := hside
  rcases c.g1_edge_unique _ _ hi hjin hje.symm with ho | ho
  · exfalso
    rw [ho] at hside'
    have ha := asm_side_cancel c hside'
    have ht : (tileDec Y).typ = (tileDec X).typ := congrArg Sigma.fst ho
    exact hYX (asm_tile_unique c T hY hX ht ha)
  · refine ⟨Y, hY, congrArg Sigma.fst ho, ?_⟩
    rw [ho] at hside'
    obtain ⟨-, -, hp3⟩ := c.g1_partner _ hi
    have hp3' : asmSide c (c.anchor (c.partner (c.occ (tileDec X).typ i)).1)
        (c.partner (c.occ (tileDec X).typ i)) =
        asmSide c (c.anchor (tileDec X).typ) (c.occ (tileDec X).typ i) := hp3
    apply asm_side_cancel c (o := c.partner (c.occ (tileDec X).typ i))
    rw [hside']
    unfold asmSide at hp3' ⊢
    rw [← vadd_vadd, hp3', vadd_vadd, sub_add_cancel]

private lemma asm_exists_cells {c : MacroCertificate P} {T : PlaneTiling (typedDecoration c)}
    {Y : PlacedTile (typedDecoration c)} (hY : Y ∈ T.tiles) {t : c.Typ} {a : Pt}
    (ht : (tileDec Y).typ = t) (ha : Y.anchor = a) :
    ∃ f, (⟨⟨t, f⟩, a⟩ : PlacedTile (typedDecoration c)) ∈ T.tiles := by
  obtain ⟨⟨ty, g⟩, ya⟩ := Y
  change ty = t at ht
  change ya = a at ha
  subst ht ha
  exact ⟨g, hY⟩

private lemma asm_template_partner (c : MacroCertificate P) {s s' : c.Typ} (i : c.Side s) (j : c.Side s')
    (hown : c.owner s' = c.owner s) (hne : s' ≠ s) (hi : c.IsInner (c.occ s i))
    (hs : c.occSide (c.occ s' j) = c.occSide (c.occ s i)) : s' = (c.partner (c.occ s i)).1 := by
  obtain ⟨hp1, hp2, hp3⟩ := c.g1_partner _ hi
  by_contra hne'
  have hmem : ∀ t, c.owner t = c.owner s →
      (⟨c.form t, c.anchor t⟩ : PlacedTile c.Q) ∈ (c.σ.rule (c.owner s)).tiles := by
    intro t ht; rw [c.rule_eq]; exact ⟨t, ht, rfl⟩
  have hdisj : ∀ t t', c.owner t = c.owner s → c.owner t' = c.owner s → t ≠ t' →
      Disjoint (interior (c.anchor t +ᵥ (c.Q.disk (c.form t)).carrier))
        (interior (c.anchor t' +ᵥ (c.Q.disk (c.form t')).carrier)) := by
    intro t t' ht ht' htt
    have hne2 : (⟨c.form t, c.anchor t⟩ : PlacedTile c.Q) ≠ ⟨c.form t', c.anchor t'⟩ := by
      intro h
      injection h with h1 h2
      exact htt (c.type_injective t t' (ht.trans ht'.symm) h1 h2)
    exact (c.σ.rule (c.owner s)).disjoint (hmem t ht) (hmem t' ht') hne2
  exact asm_no_three (c.Q.disk (c.form s)) (c.Q.disk (c.form s'))
    (c.Q.disk (c.form (c.partner (c.occ s i)).1))
    (c.anchor s) (c.anchor s') (c.anchor (c.partner (c.occ s i)).1) i j (c.partner (c.occ s i)).2 hs hp3
    (hdisj _ _ rfl hown (Ne.symm hne)) (hdisj _ _ rfl hp2 (Ne.symm hp1)) (hdisj _ _ hown hp2 hne')

private lemma asm_all_present (c : MacroCertificate P) (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hN : ∀ X ∈ T.tiles, IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
      InnerActive c (tileDec X))
    {X : PlacedTile (typedDecoration c)} (hX : X ∈ T.tiles) (t : c.Typ)
    (ht : c.owner t = c.owner (tileDec X).typ) :
    ∃ f, (⟨⟨t, f⟩, (X.anchor - c.anchor (tileDec X).typ) + c.anchor t⟩ :
      PlacedTile (typedDecoration c)) ∈ T.tiles := by
  let Pres : {t : c.Typ // c.owner t = c.owner (tileDec X).typ} → Prop := fun u =>
    ∃ f, (⟨⟨u.1, f⟩, (X.anchor - c.anchor (tileDec X).typ) + c.anchor u.1⟩ :
      PlacedTile (typedDecoration c)) ∈ T.tiles
  have step : ∀ u w, (c.innerGraph (c.owner (tileDec X).typ)).Adj u w → Pres u → Pres w := by
    intro u w hadj hu
    obtain ⟨f, hf⟩ := hu
    rw [MacroData.innerGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨hne, hR⟩ := hadj
    have core : ∀ (i : c.Side u.1) (j : c.Side w.1), c.IsInner (c.occ u.1 i) →
        c.occSide (c.occ w.1 j) = c.occSide (c.occ u.1 i) → Pres w := by
      intro i j hi hs
      have hw : w.1 = (c.partner (c.occ u.1 i)).1 :=
        asm_template_partner c i j (w.2.trans u.2.symm) (fun h => hne (Subtype.ext h.symm)) hi hs
      obtain ⟨Y, hY, hYt, hYa⟩ := asm_neighbour c T hT hN hf i hi
      have hYa' : Y.anchor =
          X.anchor - c.anchor (tileDec X).typ + c.anchor (c.partner (c.occ u.1 i)).1 := by
        rw [hYa]
        show X.anchor - c.anchor (tileDec X).typ + c.anchor u.1 - c.anchor u.1 +
          c.anchor (c.partner (c.occ u.1 i)).1 = _
        rw [add_sub_cancel_right]
      obtain ⟨g, hg⟩ := asm_exists_cells (t := (c.partner (c.occ u.1 i)).1) hY hYt hYa'
      show ∃ f, (⟨⟨w.1, f⟩, (X.anchor - c.anchor (tileDec X).typ) + c.anchor w.1⟩ :
        PlacedTile (typedDecoration c)) ∈ T.tiles
      rw [hw]
      exact ⟨g, hg⟩
    rcases hR with ⟨i, j, hi, hs⟩ | ⟨j, i, hj, hs⟩
    · exact core i j hi hs.symm
    · exact core i j (asm_inner_of_occSide c hj (u.2.trans w.2.symm) hs.symm) hs
  have base : Pres ⟨(tileDec X).typ, rfl⟩ := by
    refine ⟨(tileDec X).cell, ?_⟩
    rw [sub_add_cancel]
    exact hX
  obtain ⟨w⟩ := (c.g1_connected (c.owner (tileDec X).typ)).preconnected ⟨(tileDec X).typ, rfl⟩ ⟨t, ht⟩
  suffices H : ∀ u w' (p : (c.innerGraph (c.owner (tileDec X).typ)).Walk u w'), Pres u → Pres w' from
    H _ _ w base
  intro u w' p
  induction p with
  | nil => exact id
  | cons h p ih => exact fun hu => ih (step _ _ h hu)

open Classical in
/-- The candidate block with parent form `α` and offset `v`, coloured by the tiles of `T`. -/
private def asmBlock (c : MacroCertificate P) (T : PlaneTiling (typedDecoration c)) (α : c.Q.Form) (v : Pt) :
    ColouredBlock c where
  α := α
  v := v
  col t := if h : ∃ f, (⟨⟨t, f⟩, v + c.anchor t⟩ : PlacedTile (typedDecoration c)) ∈ T.tiles
    then h.choose else fun _ _ => 0

/-- The candidate block of a tile. -/
private def asmBlockOf (c : MacroCertificate P) (T : PlaneTiling (typedDecoration c))
    (X : PlacedTile (typedDecoration c)) : ColouredBlock c :=
  asmBlock c T (c.owner (tileDec X).typ) (X.anchor - c.anchor (tileDec X).typ)

private lemma asm_block_placed (c : MacroCertificate P) (T : PlaneTiling (typedDecoration c)) (α : c.Q.Form)
    (v : Pt) (t : c.Typ) (h : ∃ f, (⟨⟨t, f⟩, v + c.anchor t⟩ : PlacedTile (typedDecoration c)) ∈ T.tiles) :
    (asmBlock c T α v).placed t ∈ T.tiles := by
  have hcol : (asmBlock c T α v).col t = h.choose := by
    simp only [asmBlock]
    rw [dif_pos h]
  show (⟨⟨t, (asmBlock c T α v).col t⟩, v + c.anchor t⟩ : PlacedTile (typedDecoration c)) ∈ T.tiles
  rw [hcol]
  exact h.choose_spec

/-- `lem:comp/assembly`: a proper plane tiling of normal identity-correct
typed tiles in which every inner side is nontrivial admits a partition into
positioned `σ'` macrotemplates. -/
theorem assembleMacrotemplates (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hN : ∀ X ∈ T.tiles, IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
      InnerActive c (tileDec X)) :
    Nonempty (MacroPartition c T) := by
  -- The hereditary-sides hypothesis is not needed for the assembly.
  have _ := hH
  have hsub : ∀ X ∈ T.tiles, (asmBlockOf c T X).tiles ⊆ T.tiles := by
    rintro X hX Z ⟨t, ht, rfl⟩
    exact asm_block_placed c T _ _ t (asm_all_present c T hT hN hX t ht)
  have hself : ∀ X ∈ T.tiles, X ∈ (asmBlockOf c T X).tiles := by
    intro X hX
    refine ⟨(tileDec X).typ, rfl, ?_⟩
    have hmem := asm_block_placed c T (c.owner (tileDec X).typ) (X.anchor - c.anchor (tileDec X).typ)
      (tileDec X).typ ⟨(tileDec X).cell, by rw [sub_add_cancel]; exact hX⟩
    exact asm_tile_unique c T hX hmem rfl (by
      show X.anchor = X.anchor - c.anchor (tileDec X).typ + c.anchor (tileDec X).typ
      rw [sub_add_cancel])
  have hblk : ∀ X Z, Z ∈ (asmBlockOf c T X).tiles → asmBlockOf c T Z = asmBlockOf c T X := by
    rintro X Z ⟨t, ht, rfl⟩
    change c.owner t = c.owner (tileDec X).typ at ht
    show asmBlock c T (c.owner t) ((X.anchor - c.anchor (tileDec X).typ) + c.anchor t - c.anchor t) =
      asmBlock c T (c.owner (tileDec X).typ) (X.anchor - c.anchor (tileDec X).typ)
    rw [ht, add_sub_cancel_right]
  refine ⟨{ ι := {K : ColouredBlock c // ∃ X ∈ T.tiles, K = asmBlockOf c T X},
            block := Subtype.val,
            disjoint := ?_,
            cover := ?_ }⟩
  · rintro ⟨K, X, hX, rfl⟩ ⟨K', X', hX', rfl⟩ hne
    rw [Set.disjoint_left]
    intro Z hZ hZ'
    apply hne
    exact Subtype.ext ((hblk X Z hZ).symm.trans (hblk X' Z hZ'))
  · apply Set.Subset.antisymm
    · intro Z hZ
      obtain ⟨⟨K, X, hX, rfl⟩, hZK⟩ := Set.mem_iUnion.1 hZ
      exact hsub X hX hZK
    · intro X hX
      exact Set.mem_iUnion.2 ⟨⟨asmBlockOf c T X, X, hX, rfl⟩, hself X hX⟩

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
  dsimp [MacroData.IsBeltType]
  refine ⟨ht, ?_⟩
  dsimp [MacroData.IsBoundary] at hi
  rcases hi with ⟨_, h | h⟩
  · use c.occStart (c.occ t i)
    refine ⟨?_, by rw [← ht]; exact h⟩
    have h_mem_frontier : (c.Q.disk (c.form t)).vertex i ∈
        frontier (c.Q.disk (c.form t)).carrier := by
      rw [(c.Q.disk (c.form t)).frontier_eq]
      simp only [mem_iUnion]
      exact ⟨i, left_mem_segment ℝ _ _⟩
    have h_closed : IsClosed (c.Q.disk (c.form t)).carrier := by
      rw [← (c.Q.disk (c.form t)).regular_closed]
      exact isClosed_closure
    exact vadd_mem_vadd_set_iff.mpr (h_closed.closure_eq ▸ frontier_subset_closure h_mem_frontier)
  · use c.occEnd (c.occ t i)
    refine ⟨?_, by rw [← ht]; exact h⟩
    have h_mem_frontier : (c.Q.disk (c.form t)).vertex (finRotate _ i) ∈
        frontier (c.Q.disk (c.form t)).carrier := by
      rw [(c.Q.disk (c.form t)).frontier_eq]
      simp only [mem_iUnion]
      exact ⟨i, right_mem_segment ℝ _ _⟩
    have h_closed : IsClosed (c.Q.disk (c.form t)).carrier := by
      rw [← (c.Q.disk (c.form t)).regular_closed]
      exact isClosed_closure
    exact vadd_mem_vadd_set_iff.mpr (h_closed.closure_eq ▸ frontier_subset_closure h_mem_frontier)

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
    ∃ (o : c.SideOcc) (_ho : c.port (c.form h.1) d i = some o),
      headerLegal c (K.tileOf o.1) ∧
      (K.tileOf o.1).cell o.2 2 = K.col o.1 o.2 2 := by
  have _ := hH
  have _ := hLoc
  have h_len := c.g3_five_le (c.form h.1) d
  set L := (c.outerList (c.form h.1) d).length
  have h1 : i.val ≤ 4 := by omega
  have h2 : (i.val + 1) * L ≤ 5 * L := Nat.mul_le_mul_right L (by omega)
  have h_bound : (((i.val + 1) * L + 5) / 6) - 1 < L := by omega
  obtain ⟨o, ho⟩ : ∃ o, c.port (c.form h.1) d i = some o := by
    unfold Geometry.MacroData.port Geometry.MacroData.portRank
    exact ⟨_, List.getElem?_eq_getElem h_bound⟩
  use o, ho
  have ho_mem : o ∈ c.outerList (c.form h.1) d := by
    unfold Geometry.MacroData.port at ho
    exact List.mem_of_getElem? ho
  have ho_outer : c.IsOuter o := (c.g3_outerList_mem (c.form h.1) d o).mp ho_mem |>.2.1
  have ho_owner : c.owner o.1 = c.form h.1 := (c.g3_outerList_mem (c.form h.1) d o).mp ho_mem |>.1
  have h_not_cen : o.1 ≠ c.central K.α := by
    intro h_eq
    have h_cen := c.g2_central K.α (cast (by rw [h_eq]) o.2)
    have ho_eq : o = c.occ (c.central K.α) (cast (by rw [h_eq]) o.2) := by
      rcases o with ⟨t, j⟩
      dsimp at h_eq
      subst h_eq
      rfl
    rw [← ho_eq] at h_cen
    exact h_cen.1 ho_outer
  have ho_legal : headerLegal c (K.tileOf o.1) := by
    apply hK.2 o.1
    · rw [ho_owner, hh.1]
    · exact h_not_cen
  constructor
  · exact ho_legal
  · rfl

/-- Step 2 of the blueprint proof of `reconstructed_header_eq_isNormal`: extracting normality from the legal parent tile. -/
private lemma reconstructed_header_eq_isNormal_aux2 (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (d : c.Side h.1) (i : Fin 5) (hLoc : IsLocal c (c.occ h.1 d) i)
    (o : c.SideOcc) (ho : c.port (c.form h.1) d i = some o)
    (hLeg : headerLegal c (K.tileOf o.1)) :
    (K.tileOf o.1).cell o.2 2 = prescribedCell c (c.occ h.1 d) i := by
  have _ := hK
  have _ := hLoc
  obtain ⟨hOwner, hOuter, -⟩ :=
    (c.g3_outerList_mem (c.form h.1) d o).1 (List.mem_of_getElem? ho)
  obtain ⟨C, hCLeg, hChild⟩ :=
    headerLegal_properties_step1_parent c hH (K.tileOf o.1) hLeg
  obtain ⟨j, hBoundary⟩ := boundary_side_of_outer_side c hH o.1 o.2 hOuter
  have hNotPrint : ¬ c.IsPrint (c.occ o.1 j) := fun hp =>
    headerLegal_properties_step4_boundary_step1_print_not_boundary c _ hp hBoundary
  have hChild' := hChild
  dsimp [IsChildOf, headerSubstitution, IsChildOfWith] at hChild'
  have hFromParent : K.col o.1 j 3 = headerU c (headerOf c C) := by
    change (K.tileOf o.1).cell j 3 = headerU c (headerOf c C)
    exact ((hChild'.2 j).2 hNotPrint).2.2.2.2.2.2.1 hBoundary
  have hCommon : K.col o.1 j 3 = headerU c h :=
    hh.2 o.1 j (hOwner.trans hh.1) hBoundary
  have hHeader : headerOf c C = h :=
    HeaderKernel.tagged_header_injective (hFromParent.symm.trans hCommon)
  obtain ⟨tC, colC⟩ := C
  have hCType : tC = h.1 := congrArg Sigma.fst hHeader
  subst tC
  have hPath : o ∈ c.path (c.form h.1) d i := by
    by_cases hGenuine : c.IsGenuinePath (c.form h.1) d i
    · exact List.mem_of_mem_head? ((c.g4_path_head _ _ _ hGenuine).trans ho)
    · rw [c.g4_path_trivial _ _ _ hGenuine, ho]
      simp
  have hPortNotPrint : ¬ c.IsPrint o := fun hp => asm_print_inner c hp hOuter
  have hPathValue : K.col o.1 o.2 2 = colC d i := by
    change (K.tileOf o.1).cell o.2 2 = colC d i
    exact ((hChild'.2 o.2).2 hPortNotPrint).2.2.2.1 d i hPath
  have hParentValue :=
    (headerLegal_properties_step2_normal_id c hH ⟨h.1, colC⟩ hCLeg).1 d i hLoc
  change colC d i = _ at hParentValue
  exact hPathValue.trans hParentValue

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

/-- Step 1 of the blueprint proof of
`reconstructed_header_eq_isIdentityCorrect_step1_inner_nonprint`: the first port of a parent
side `i` of type `h.1` is an outer child side owned by the block `K`, hence (not being the
central child of `K.α`) legal. -/
private lemma reconstructed_header_eq_isIdentityCorrect_step1_inner_nonprint_step1_port
    (c : MacroCertificate P) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (i : c.Side h.1) :
    ∃ o : c.SideOcc, c.port (c.form h.1) i 0 = some o ∧ headerLegal c (K.tileOf o.1) := by
  have h5 := c.g3_five_le (c.form h.1) i
  have hidx : MacroData.portRank (c.outerList (c.form h.1) i).length 0 - 1 <
      (c.outerList (c.form h.1) i).length := by
    unfold MacroData.portRank
    omega
  obtain ⟨o, ho⟩ : ∃ o : c.SideOcc, (c.outerList (c.form h.1) i)[MacroData.portRank
      (c.outerList (c.form h.1) i).length 0 - 1] = o := ⟨_, rfl⟩
  refine ⟨o, ?_, ?_⟩
  · show (c.outerList (c.form h.1) i)[MacroData.portRank
      (c.outerList (c.form h.1) i).length 0 - 1]? = some o
    rw [List.getElem?_eq_some_iff]
    exact ⟨hidx, ho⟩
  · have hmem : o ∈ c.outerList (c.form h.1) i := ho ▸ List.getElem_mem hidx
    obtain ⟨hown, hout, _⟩ := (c.g3_outerList_mem (c.form h.1) i o).1 hmem
    have hown' : c.owner o.1 = K.α := hown.trans hh.1
    obtain ⟨t, j⟩ := o
    refine hK.2 t hown' ?_
    rintro rfl
    exact (c.g2_central K.α j).1 hout

/-- Step 2 of the blueprint proof of
`reconstructed_header_eq_isIdentityCorrect_step1_inner_nonprint`: for an inner nonprint side
`i` of type `h.1`, a legal parent of the first-port tile found in step 1 has `h.1` as the type
of that port owner's template, so the child clauses of the repaired substitution force the
port's third cell to carry forward the prescribed identity of `i`. -/
private lemma reconstructed_header_eq_isIdentityCorrect_step1_inner_nonprint_step2_value
    (c : MacroCertificate P) (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (i : c.Side h.1)
    (hInner : c.IsInner (c.occ h.1 i)) (hNonprint : ¬ c.IsPrint (c.occ h.1 i))
    (o : c.SideOcc) (ho : c.port (c.form h.1) i 0 = some o) (hLeg : headerLegal c (K.tileOf o.1)) :
    K.col o.1 o.2 2 = identU c (c.edge (c.occ h.1 i)) := by
  have _hK := hK
  obtain ⟨hOwner, hOuter, -⟩ :=
    (c.g3_outerList_mem (c.form h.1) i o).1 (List.mem_of_getElem? ho)
  obtain ⟨ch, hChainZero, hChain, -⟩ := hLeg
  let C : DecTile c := ch 1
  have hChild : IsChildOf c C (K.tileOf o.1) := by
    dsimp [C]
    rw [← hChainZero]
    exact hChain 0
  have hCChild : IsChildOf c (ch 2) C := by
    exact hChain 1
  obtain ⟨j, hBoundary⟩ := boundary_side_of_outer_side c hH o.1 o.2 hOuter
  have hNotPrint : ¬ c.IsPrint (c.occ o.1 j) := fun hp =>
    headerLegal_properties_step4_boundary_step1_print_not_boundary c _ hp hBoundary
  have hChild' := hChild
  dsimp [IsChildOf, headerSubstitution, IsChildOfWith] at hChild'
  have hFromParent : K.col o.1 j 3 = headerU c (headerOf c C) := by
    change (K.tileOf o.1).cell j 3 = headerU c (headerOf c C)
    exact ((hChild'.2 j).2 hNotPrint).2.2.2.2.2.2.1 hBoundary
  have hCommon : K.col o.1 j 3 = headerU c h :=
    hh.2 o.1 j (hOwner.trans hh.1) hBoundary
  have hHeader : headerOf c C = h :=
    HeaderKernel.tagged_header_injective (hFromParent.symm.trans hCommon)
  have hCType : C.typ = h.1 := congrArg Sigma.fst hHeader
  have hPath : o ∈ c.path (c.form h.1) i 0 := by
    by_cases hGenuine : c.IsGenuinePath (c.form h.1) i 0
    · exact List.mem_of_mem_head? ((c.g4_path_head _ _ _ hGenuine).trans ho)
    · rw [c.g4_path_trivial _ _ _ hGenuine, ho]
      simp
  have hPortNotPrint : ¬ c.IsPrint o := fun hp => asm_print_inner c hp hOuter
  obtain ⟨tC, colC⟩ := C
  change tC = h.1 at hCType
  subst tC
  have hPathValue : K.col o.1 o.2 2 = colC i 0 := by
    change (K.tileOf o.1).cell o.2 2 = colC i 0
    exact ((hChild'.2 o.2).2 hPortNotPrint).2.2.2.1 i 0 hPath
  dsimp [IsChildOf, headerSubstitution, IsChildOfWith] at hCChild
  have hParentIdentity : colC i 0 = identU c (c.edge (c.occ h.1 i)) := by
    rw [((hCChild.2 i).2 hNonprint).1]
    simp [prescribedFirst, hInner]
  exact hPathValue.trans hParentIdentity

/-- Step 1 of the blueprint proof of `reconstructed_header_eq_isIdentityCorrect`: For an inner
nonprint side `d`, the first cell of `D` is its prescribed identity. -/
private lemma reconstructed_header_eq_isIdentityCorrect_step1_inner_nonprint (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) (i : c.Side h.1)
    (hInner : c.IsInner (c.occ h.1 i)) (hNonprint : ¬ c.IsPrint (c.occ h.1 i)) :
    (reconstruct c K h.1).cell i 0 = identU c (c.edge (c.occ h.1 i)) := by
  obtain ⟨o, ho, hLeg⟩ :=
    reconstructed_header_eq_isIdentityCorrect_step1_inner_nonprint_step1_port c K hK h hh i
  have hval := reconstructed_header_eq_isIdentityCorrect_step1_inner_nonprint_step2_value
    c hH K hK h hh i hInner hNonprint o ho hLeg
  change (match c.port (c.form h.1) i 0 with | some o => K.col o.1 o.2 2 | none => 0) = _
  rw [ho]
  exact hval


/-- Step 2.1 of the blueprint proof of `reconstructed_header_eq_isIdentityCorrect_step2_print`: For a print, its fifth cell is local. -/
private lemma reconstructed_header_eq_isIdentityCorrect_step2_print_step1_isLocal (c : MacroCertificate P) (o : c.SideOcc) (hPrint : c.IsPrint o) :
    IsLocal c o 4 := by
  have _ := hPrint
  exact asm_isLocal_four c o

/-- Step 2.2 of the blueprint proof of `reconstructed_header_eq_isIdentityCorrect_step2_print`:
For a print, its fifth prescribed cell is the exact interface identity. -/
private lemma reconstructed_header_eq_isIdentityCorrect_step2_print_step2_prescribed (c : MacroCertificate P) (o : c.SideOcc) (hPrint : c.IsPrint o) :
    prescribedCell c o 4 = identU c (c.edge o) := by
  unfold prescribedCell
  simp [hPrint]

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
  rcases h with ⟨t, v⟩
  unfold headerOf HeaderKernel.makeHeader
  congr 1
  funext d
  let i : Fin 5 := 3
  have h5 := c.g3_five_le (c.form t) d
  have hidx : MacroData.portRank (c.outerList (c.form t) d).length i - 1 <
      (c.outerList (c.form t) d).length := by
    dsimp [i]
    unfold MacroData.portRank
    omega
  obtain ⟨o, ho⟩ : ∃ o : c.SideOcc,
      (c.outerList (c.form t) d)[MacroData.portRank
        (c.outerList (c.form t) d).length i - 1] = o := ⟨_, rfl⟩
  have hport : c.port (c.form t) d i = some o := by
    show (c.outerList (c.form t) d)[MacroData.portRank
      (c.outerList (c.form t) d).length i - 1]? = some o
    rw [List.getElem?_eq_some_iff]
    exact ⟨hidx, ho⟩
  have hmem : o ∈ c.outerList (c.form t) d := ho ▸ List.getElem_mem hidx
  obtain ⟨hown, hout, -⟩ := (c.g3_outerList_mem (c.form t) d o).1 hmem
  have howner : c.owner o.1 = K.α := hown.trans (by exact (show c.form t = K.α from hh.1))
  have hLeg : headerLegal c (K.tileOf o.1) := by
    obtain ⟨u, j⟩ := o
    apply hK.2 u howner
    rintro rfl
    exact (c.g2_central K.α j).1 hout
  obtain ⟨ch, hChainZero, hChain, -⟩ := hLeg
  let C : DecTile c := ch 1
  have hChild : IsChildOf c C (K.tileOf o.1) := by
    dsimp [C]
    rw [← hChainZero]
    exact hChain 0
  obtain ⟨j, hj⟩ := boundary_side_of_outer_side c hH o.1 o.2 hout
  have hNotPrint : ¬ c.IsPrint (c.occ o.1 j) := fun hp =>
    headerLegal_properties_step4_boundary_step1_print_not_boundary c _ hp hj
  have hFromParent : K.col o.1 j 3 = headerU c (headerOf c C) := by
    change (K.tileOf o.1).cell j 3 = headerU c (headerOf c C)
    have hChild' := hChild
    dsimp [IsChildOf, headerSubstitution, IsChildOfWith] at hChild'
    exact ((hChild'.2 j).2 hNotPrint).2.2.2.2.2.2.1 hj
  have hCommon : K.col o.1 j 3 = headerU c ⟨t, v⟩ :=
    hh.2 o.1 j howner hj
  have hHeader : headerOf c C = ⟨t, v⟩ :=
    HeaderKernel.tagged_header_injective (hFromParent.symm.trans hCommon)
  obtain ⟨tC, colC⟩ := C
  have hHeader' : (⟨tC, HeaderKernel.zeroMode c.outerB tC (fun q => colC q 3)⟩ :
      HeaderKernel.Header c.Typ c.Side) = ⟨t, v⟩ := by
    simpa [headerOf, HeaderKernel.makeHeader, fourthVec] using hHeader
  obtain ⟨hType, hMode⟩ := Sigma.mk.inj_iff.mp hHeader'
  subst tC
  have hPath : o ∈ c.path (c.form t) d i := by
    by_cases hGenuine : c.IsGenuinePath (c.form t) d i
    · exact List.mem_of_mem_head? ((c.g4_path_head _ _ _ hGenuine).trans hport)
    · rw [c.g4_path_trivial _ _ _ hGenuine, hport]
      simp
  have hPortNotPrint : ¬ c.IsPrint o := fun hp => asm_print_inner c hp hout
  have hThird : K.col o.1 o.2 2 = colC d 3 := by
    have hChild' := hChild
    dsimp [IsChildOf, headerSubstitution, IsChildOfWith] at hChild'
    change (K.tileOf o.1).cell o.2 2 = colC d 3
    exact ((hChild'.2 o.2).2 hPortNotPrint).2.2.2.1 d i hPath
  have hFourth : (reconstruct c K t).cell d 3 = colC d 3 := by
    have hport3 : c.port (c.form t) d 3 = some o := by
      simpa [i] using hport
    change (match c.port (c.form t) d 3 with
      | some o => K.col o.1 o.2 2
      | none => 0) = colC d 3
    rw [hport3]
    exact hThird
  have hMode' : HeaderKernel.zeroMode c.outerB t (fun q => colC q 3) d = v d :=
    congrFun (eq_of_heq hMode) d
  change HeaderKernel.zeroMode c.outerB t (fun q => (reconstruct c K t).cell q 3) d = v d
  unfold HeaderKernel.zeroMode at hMode' ⊢
  change (c.outerB t d && decide ((reconstruct c K t).cell d 3 = 0)) = v d
  rw [hFourth]
  exact hMode'

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

/-- A fixed vector cancels in set vadd (used to compare placed and unplaced side
segments). -/
private lemma path_and_print_recovery_step1_signals_aux_vadd_cancel (a : Pt) {S T : Set Pt}
    (h : a +ᵥ S = a +ᵥ T) : S = T := by
  have hinj : Function.Injective (fun x : Pt => a +ᵥ x) := by
    intro x y hxy
    simpa using hxy
  rw [← Set.image_vadd, ← Set.image_vadd] at h
  exact (Set.image_eq_image hinj).mp h

/-- A placed child side is the block offset `v` added to the unplaced side. -/
private lemma path_and_print_recovery_step1_signals_aux_childSide (c : MacroCertificate P)
    (K : ColouredBlock c) (o : c.SideOcc) :
    K.childSide o = K.v +ᵥ c.occSide o := by
  show (K.v + c.anchor o.1) +ᵥ (c.Q.disk (c.form o.1)).side o.2 =
    K.v +ᵥ (c.anchor o.1 +ᵥ (c.Q.disk (c.form o.1)).side o.2)
  rw [add_vadd]

/-- Step 1 of the blueprint proof of `path_and_print_recovery_step1_signals`: a print
occurrence on a genuine path is the path's own terminal print. -/
private lemma path_and_print_recovery_step1_signals_aux1 (c : MacroCertificate P)
    {α : c.Q.Form} {d : Fin (c.Q.disk α).n} {j : Fin 5} (hG : c.IsGenuinePath α d j)
    {o : c.SideOcc} (ho : o ∈ c.path α d j) (hp : c.IsPrint o) :
    o = c.partner (c.printOcc α d) := by
  have hown : c.owner o.1 = α := c.g4_path_owner α d j o ho
  have hp' : ∃ e : Fin (c.Q.disk α).n, c.IsPrintOf α e o := by
    unfold MacroData.IsPrint at hp
    rwa [hown] at hp
  obtain ⟨e, hme, hcase⟩ := hp'
  rcases hcase with rfl | rfl
  · exact absurd rfl (c.g4_path_not_central α d j hG _ ho)
  · by_cases hde : e = d
    · rw [hde]
    · exfalso
      have hlast : (c.path α e 0).getLast? = some (c.partner (c.printOcc α e)) :=
        c.g4_path_last α e 0 ⟨hme, by decide⟩
      rw [List.getLast?_eq_getElem?] at hlast
      have hterm : c.partner (c.printOcc α e) ∈ c.path α e 0 :=
        List.mem_of_getElem? hlast
      have hne' : (d, j) ≠ (e, (0 : Fin 5)) := fun heq => hde (congrArg Prod.fst heq).symm
      obtain ⟨hde', -⟩ := c.g4_path_disjoint α d e j 0 hne' _ ho hterm
      exact hde hde'.symm

/-- Step 2 of the blueprint proof of `path_and_print_recovery_step1_signals`: only the
final position of a genuine path can carry a print occurrence. -/
private lemma path_and_print_recovery_step1_signals_aux2 (c : MacroCertificate P)
    {α : c.Q.Form} {d : Fin (c.Q.disk α).n} {j : Fin 5} (hG : c.IsGenuinePath α d j)
    {n : ℕ} (hn : n + 1 < (c.path α d j).length) {o : c.SideOcc}
    (ho : (c.path α d j)[n]? = some o) : ¬ c.IsPrint o := by
  intro hp
  have hmem : o ∈ c.path α d j := List.mem_of_getElem? ho
  have heq := path_and_print_recovery_step1_signals_aux1 c hG hmem hp
  have hlast : (c.path α d j).getLast? = some o := by
    rw [heq]; exact c.g4_path_last α d j hG
  rw [List.getLast?_eq_getElem?] at hlast
  have hnodup := c.g4_path_nodup α d j
  have hne := (List.nodup_iff_getElem?_ne_getElem?).1 hnodup n ((c.path α d j).length - 1)
    (by omega) (by omega)
  exact hne (ho.trans hlast.symm)

/-- Step 3 of the blueprint proof of `path_and_print_recovery_step1_signals`: consecutive
nonprint occurrences of a path carry equal third signals, whether they share a tile or are
partner occurrences of a common inner side. -/
private lemma path_and_print_recovery_step1_signals_aux3 (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    {α : c.Q.Form} (hα : α = K.α) {d : Fin (c.Q.disk α).n} {j : Fin 5}
    (hG : c.IsGenuinePath α d j) {o o' : c.SideOcc}
    (hmem : o ∈ c.path α d j) (hmem' : o' ∈ c.path α d j)
    (hchain : o.1 = o'.1 ∨ (c.IsInner o ∧ o' = c.partner o))
    (hnp : ¬ c.IsPrint o) (hnp' : ¬ c.IsPrint o') :
    K.col o.1 o.2 2 = K.col o'.1 o'.2 2 := by
  rcases hchain with hsame | ⟨hinner, hpartner⟩
  · obtain ⟨t, i⟩ := o
    subst hsame
    have hown : c.owner o'.1 = α := c.g4_path_owner α d j (c.occ o'.1 i) hmem
    have hnc : o'.1 ≠ c.central α := c.g4_path_not_central α d j hG (c.occ o'.1 i) hmem
    have hownK : c.owner o'.1 = K.α := hown.trans hα
    have hncK : o'.1 ≠ c.central K.α := by rw [← hα]; exact hnc
    have hlegal : headerLegal c (K.tileOf o'.1) := hK.2 o'.1 hownK hncK
    have heqF : α = c.owner o'.1 := hown.symm
    have hcast : c.occ o'.1 i ∈ c.path (c.owner o'.1)
        (cast (congrArg (fun F => Fin (c.Q.disk F).n) heqF) d) j :=
      (headerLegal_properties_step5_path_step1_cast_path c hH heqF d j (c.occ o'.1 i)).1 hmem
    have hcast' : c.occ o'.1 o'.2 ∈ c.path (c.owner o'.1)
        (cast (congrArg (fun F => Fin (c.Q.disk F).n) heqF) d) j :=
      (headerLegal_properties_step5_path_step1_cast_path c hH heqF d j (c.occ o'.1 o'.2)).1 hmem'
    exact headerLegal_properties_step5_path c hH (K.tileOf o'.1) hlegal _ j i o'.2 hcast hcast'
      hnp hnp'
  · subst hpartner
    have hown : c.owner o.1 = α := c.g4_path_owner α d j o hmem
    have hnc : o.1 ≠ c.central α := c.g4_path_not_central α d j hG o hmem
    have hlegal : headerLegal c (K.tileOf o.1) := hK.2 o.1 (hown.trans hα) (by
      rw [← hα]; exact hnc)
    have hNontriv : IsNontrivial c (K.tileOf o.1) o.2 :=
      headerLegal_properties_step6_inner c hH (K.tileOf o.1) hlegal o.2 hinner
    obtain ⟨t2, j2, hown2, hne2, hside2, hcol2⟩ :=
      hK.1 o.1 o.2 (hown.trans hα) hinner hNontriv
    have hsideEq : c.occSide (c.occ t2 j2) = c.occSide o := by
      have e1 := path_and_print_recovery_step1_signals_aux_childSide c K (c.occ t2 j2)
      have e2 := path_and_print_recovery_step1_signals_aux_childSide c K o
      rw [e1, e2] at hside2
      exact path_and_print_recovery_step1_signals_aux_vadd_cancel K.v hside2
    have heqOcc : (c.occ t2 j2 : c.SideOcc) = c.partner o :=
      c.g1_side_unique o (c.occ t2 j2) hinner (hown2.trans (hown.trans hα).symm) hne2 hsideEq
    have hcolEq : K.col t2 j2 2 = K.col (c.partner o).1 (c.partner o).2 2 :=
      congrArg (fun (p : c.SideOcc) => K.col p.1 p.2 2) heqOcc
    exact (hcol2 2).symm.trans hcolEq

/-- Step 4 of the blueprint proof of `path_and_print_recovery_step1_signals`: induction
along a genuine path, from the port to an arbitrary nonprint position. -/
private lemma path_and_print_recovery_step1_signals_aux4 (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    {α : c.Q.Form} (hα : α = K.α) {d : Fin (c.Q.disk α).n} {j : Fin 5}
    (hG : c.IsGenuinePath α d j) :
    ∀ n : ℕ, ∀ o : c.SideOcc, (c.path α d j)[n]? = some o → ¬ c.IsPrint o →
      K.col o.1 o.2 2 =
        (match c.port α d j with | some o0 => K.col o0.1 o0.2 2 | none => 0 : U c) := by
  intro n
  induction n with
  | zero =>
    intro o ho _
    have hhead : (c.path α d j).head? = c.port α d j := c.g4_path_head α d j hG
    have h0 : (c.path α d j)[0]? = c.port α d j := by
      rw [← List.head?_eq_getElem?]; exact hhead
    rw [ho] at h0
    rw [← h0]
  | succ n ih =>
    intro o' ho' hnp'
    obtain ⟨hlt1, -⟩ := (List.getElem?_eq_some_iff).1 ho'
    have hlt0 : n < (c.path α d j).length := by omega
    obtain ⟨o, ho⟩ : ∃ o, (c.path α d j)[n]? = some o :=
      ⟨(c.path α d j)[n], List.getElem?_eq_some_iff.mpr ⟨hlt0, rfl⟩⟩
    have hnp : ¬ c.IsPrint o := path_and_print_recovery_step1_signals_aux2 c hG hlt1 ho
    have heqD := ih o ho hnp
    have hmem : o ∈ c.path α d j := List.mem_of_getElem? ho
    have hmem' : o' ∈ c.path α d j := List.mem_of_getElem? ho'
    have hchain := c.g4_path_chain α d j n o o' ho ho'
    have heq2 := path_and_print_recovery_step1_signals_aux3 c hH K hK hα hG hmem hmem' hchain
      hnp hnp'
    rw [← heq2]
    exact heqD

/-- Step 1 of the blueprint proof of `path_and_print_recovery`: every nonprint third signal
on `P_i(d)` equals `D_i(d)`. -/
private lemma path_and_print_recovery_step1_signals (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) :
    ∀ (d : c.Side h.1) (j : Fin 5) (o : c.SideOcc), o ∈ c.path (c.form h.1) d j →
      ¬ c.IsPrint o → K.col o.1 o.2 2 = (reconstruct c K h.1).cell d j := by
  intro d j o ho hnp
  show K.col o.1 o.2 2 = match c.port (c.form h.1) d j with
    | some o0 => K.col o0.1 o0.2 2 | none => 0
  by_cases hG : c.IsGenuinePath (c.form h.1) d j
  · obtain ⟨n, hlt, hn⟩ := List.getElem_of_mem ho
    have ho2 : (c.path (c.form h.1) d j)[n]? = some o :=
      List.getElem?_eq_some_iff.mpr ⟨hlt, hn⟩
    exact path_and_print_recovery_step1_signals_aux4 c hH K hK hh.1 hG n o ho2 hnp
  · rw [c.g4_path_trivial (c.form h.1) d j hG, Option.mem_toList] at ho
    rw [ho]

/-- Step 1 of the blueprint proof of `path_and_print_recovery_step2_prints`: the parent `C` agrees with `D` on the cell `k`. -/
private lemma path_and_print_recovery_step2_prints_step1_parent_cell (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (d : c.Side h.1) (hd : c.marked (c.form h.1) d)
    (C : DecTile c) (hC : IsChildOf c C (K.tileOf (c.partner (c.printOcc (c.form h.1) d)).1))
    (h_form : c.form h.1 = c.form C.typ)
    (k : Fin 5) (hk : k ≠ 4) :
    C.cell (cast (by change Fin (c.Q.disk (c.form h.1)).n = Fin (c.Q.disk (c.form C.typ)).n; rw [h_form]) d) k = (reconstruct c K h.1).cell d k := by
  sorry

/-- Step 2 of the blueprint proof of `path_and_print_recovery_step2_prints`: the small child tile inherits the cell `k` from its parent `C`. -/
private lemma path_and_print_recovery_step2_prints_step2_print (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (d : c.Side h.1) (hd : c.marked (c.form h.1) d)
    (C : DecTile c) (hC : IsChildOf c C (K.tileOf (c.partner (c.printOcc (c.form h.1) d)).1))
    (h_form : c.form h.1 = c.form C.typ)
    (k : Fin 5) (hk : k ≠ 4) :
    (K.tileOf (c.partner (c.printOcc (c.form h.1) d)).1).cell (c.partner (c.printOcc (c.form h.1) d)).2 k =
      C.cell (cast (by change Fin (c.Q.disk (c.form h.1)).n = Fin (c.Q.disk (c.form C.typ)).n; rw [h_form]) d) k := by
  sorry

/-- Step 2 of the blueprint proof of `path_and_print_recovery`: the noncentral (small)
owner of the print of `d` has first four cells `D_1(d), …, D_4(d)` on that print. -/
private lemma path_and_print_recovery_step2_prints (c : MacroCertificate P)
    (hH : c.Hereditary) (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h) :
    ∀ d : c.Side h.1, c.marked (c.form h.1) d → ∀ k : Fin 5, k ≠ 4 →
      K.col (c.partner (c.printOcc (c.form h.1) d)).1 (c.partner (c.printOcc (c.form h.1) d)).2 k =
        (reconstruct c K h.1).cell d k := by
  intro d hd k hk
  have h_owner1 : c.owner (c.printOcc (c.form h.1) d).1 = c.form h.1 := c.g5_central_owner _
  have h_inner := c.g4_print_inner _ _ hd
  have h_owner2 : c.owner (c.partner (c.printOcc (c.form h.1) d)).1 = c.form h.1 :=
    (c.g1_partner _ h_inner).2.1.trans h_owner1
  have h_owner : c.owner (c.partner (c.printOcc (c.form h.1) d)).1 = K.α :=
    h_owner2.trans hh.1
  have h_nc : (c.partner (c.printOcc (c.form h.1) d)).1 ≠ c.central K.α := by
    intro h_eq
    have h_small := c.g4_print_small _ _ hd
    have h_large : c.kind (c.form (c.central K.α)) = .large := by
      rw [c.g5_large_iff, c.g5_central_owner K.α]
    rw [h_eq] at h_small
    cases h_small.symm.trans h_large
  have h_legal := hK.2 _ h_owner h_nc
  rcases h_legal with ⟨ch, h_ch0, h_ch, h_origin⟩
  let C := ch 1
  have hC : IsChildOf c C (K.tileOf (c.partner (c.printOcc (c.form h.1) d)).1) := by
    have h1 := h_ch 0
    rw [h_ch0] at h1
    exact h1
  have h_form : c.form h.1 = c.form C.typ := by
    have h_own := hC.1
    change c.owner (K.tileOf (c.partner (c.printOcc (c.form h.1) d)).1).typ = c.form C.typ at h_own
    dsimp [ColouredBlock.tileOf] at h_own
    rw [← h_own]
    exact h_owner2.symm
  have eq1 := path_and_print_recovery_step2_prints_step2_print c hH K hK h hh d hd C hC h_form k hk
  have eq2 := path_and_print_recovery_step2_prints_step1_parent_cell c hH K hK h hh d hd C hC h_form k hk
  change (K.tileOf (c.partner (c.printOcc (c.form h.1) d)).1).cell (c.partner (c.printOcc (c.form h.1) d)).2 k = _
  rw [eq1, eq2]

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
/-- Step 1: the central centre `A = ch 0` has a print side carrying a nonzero copied first cell
(the noncentral parent's marked identity), by the separating certificate. -/
private lemma reconstructed_noncentral_legal_step1_ancestor_step1_not_all_central_step1_base
    {P : Protoset} (c : MacroCertificate P) (hH : c.Hereditary)
    (K : ColouredBlock c) (hK : BlockContext c K)
    (h : HeaderKernel.Header c.Typ c.Side) (hh : CommonHeader c K h)
    (hnc : ¬ c.IsCentral h.1) (ch : ℕ → DecTile c) (hch0 : ch 0 = K.centre) :
    ∃ i : c.Side (ch 0).typ, c.IsPrint (c.occ (ch 0).typ i) ∧ (ch 0).cell i 0 ≠ 0 := by
  sorry

/-- Step 2: when the parent `ch (n+1)` is central (large, so its print map is the identity on
marked sides), a print side of `ch n` with nonzero first cell copies it from a print side of
`ch (n+1)` that again has a nonzero first cell. -/
private lemma reconstructed_noncentral_legal_step1_ancestor_step1_not_all_central_step2_propagate
    {P : Protoset} (c : MacroCertificate P) (ch : ℕ → DecTile c)
    (hch_child : ∀ i, IsChildOf c (ch (i + 1)) (ch i))
    (hall : ∀ n, c.IsCentral (ch n).typ)
    (n : ℕ) (i : c.Side (ch n).typ) (hp : c.IsPrint (c.occ (ch n).typ i))
    (hnz : (ch n).cell i 0 ≠ 0) :
    ∃ d : c.Side (ch (n + 1)).typ,
      (d, (0 : Fin 5)) ∈ copySource c (c.form (ch (n + 1)).typ) (c.occ (ch n).typ i) 0 ∧
      c.IsPrint (c.occ (ch (n + 1)).typ d) ∧ (ch (n + 1)).cell d 0 ≠ 0 := by
  sorry

/-- Step 3: a nonzero print cell that, at every level, copies from such a cell again (Step 2) never reaches an origin — the infinite descent. -/
private lemma reconstructed_noncentral_legal_step1_ancestor_step1_not_all_central_step3_no_origin
    {P : Protoset} (c : MacroCertificate P) (ch : ℕ → DecTile c)
    (hstep : ∀ (n : ℕ) (i : c.Side (ch n).typ), c.IsPrint (c.occ (ch n).typ i) →
      (ch n).cell i 0 ≠ 0 → ∃ d : c.Side (ch (n + 1)).typ,
        (d, (0 : Fin 5)) ∈ copySource c (c.form (ch (n + 1)).typ) (c.occ (ch n).typ i) 0 ∧
        c.IsPrint (c.occ (ch (n + 1)).typ d) ∧ (ch (n + 1)).cell d 0 ≠ 0)
    (n : ℕ) (i : c.Side (ch n).typ) (hp : c.IsPrint (c.occ (ch n).typ i))
    (hnz : (ch n).cell i 0 ≠ 0) : ¬ HasOrigin c ch n i 0 := by
  intro h
  have H : ∀ (m : ℕ) (j : c.Side (ch m).typ) (l : Fin 5), HasOrigin c ch m j l →
    l = 0 → c.IsPrint (c.occ (ch m).typ j) → (ch m).cell j 0 ≠ 0 → False := by
    intro m j l ho
    induction ho with
    | origin m j l h_eq =>
      intro hl hp hnz
      subst hl
      have ⟨d, hd, hp_d, hnz_d⟩ := hstep m j hp hnz
      have h_nonempty : (copySource c (c.form (ch (m + 1)).typ) (c.occ (ch m).typ j) 0).Nonempty :=
        ⟨(d, 0), hd⟩
      have h_empty : copySource c (c.form (ch (m + 1)).typ) (c.occ (ch m).typ j) 0 = ∅ := h_eq
      rw [h_empty] at h_nonempty
      exact Set.not_nonempty_empty h_nonempty
    | step m j l d l' h_mem h_orig ih =>
      intro hl hp hnz
      subst hl
      have h_mem' : (d, l') ∈ copySource c (c.form (ch (m + 1)).typ) (c.occ (ch m).typ j) 0 := h_mem
      dsimp [copySource] at h_mem'
      rcases h_mem' with ⟨h_print, h_not_4, h_eq2⟩ | ⟨h_not_print, h_eq_2, h_path⟩
      · subst h_eq2
        have ⟨d_step, hmem_step, hp_d_step, hnz_d_step⟩ := hstep m j hp hnz
        have hd_eq : d = d_step := by
          dsimp [copySource] at hmem_step
          rcases hmem_step with ⟨h_print_step, _, _⟩ | ⟨h_not_print_step, _, _⟩
          · have h1 : c.IsPrintOf (c.form (ch (m + 1)).typ) d (c.occ (ch m).typ j) := h_print
            have h2 : c.IsPrintOf (c.form (ch (m + 1)).typ) d_step (c.occ (ch m).typ j) :=
              h_print_step
            rcases h1 with ⟨hm, h1⟩
            rcases h2 with ⟨hm', h1'⟩
            have hin := c.g4_print_inner (c.form (ch (m + 1)).typ) d hm
            have hin' := c.g4_print_inner (c.form (ch (m + 1)).typ) d_step hm'
            have hp1 := (c.g1_partner _ hin).1
            have hp' := (c.g1_partner _ hin').1
            have key : c.printOcc (c.form (ch (m + 1)).typ) d =
              c.printOcc (c.form (ch (m + 1)).typ) d_step → d = d_step := by
              intro he
              apply c.g4_print_injective (c.form (ch (m + 1)).typ) d d_step hm hm'
              unfold Geometry.MacroData.printOcc at he
              exact eq_of_heq (Sigma.mk.inj he).2
            rcases h1 with h1 | h1 <;> rcases h1' with h2' | h2'
            · exact key (h1.symm.trans h2')
            · exact absurd (congrArg Sigma.fst (h1.symm.trans h2')) (fun h => hp' h.symm)
            · exact absurd (congrArg Sigma.fst (h1.symm.trans h2').symm) (fun h => hp1 h.symm)
            · have h_eq := c.g1_partner_partner _ hin
              have h_eq_part : c.partner (c.occ (ch m).typ j) =
                c.printOcc (c.form (ch (m + 1)).typ) d := by
                rw [h1, h_eq]
              have h_eq2_part : c.partner (c.occ (ch m).typ j) =
                c.printOcc (c.form (ch (m + 1)).typ) d_step := by
                rw [h2', c.g1_partner_partner _ hin']
              exact key (h_eq_part.symm.trans h_eq2_part)
          · exact absurd hp h_not_print_step
        subst hd_eq
        exact ih rfl hp_d_step hnz_d_step
      · exact absurd hp h_not_print
  exact H n i 0 h rfl hp hnz

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
    ∃ n, ¬ c.IsCentral (ch n).typ := by
  by_contra hall
  push_neg at hall
  have ⟨i₀, hp, hnz⟩ := reconstructed_noncentral_legal_step1_ancestor_step1_not_all_central_step1_base c hH K hK h hh hnc ch hch0
  have hstep := reconstructed_noncentral_legal_step1_ancestor_step1_not_all_central_step2_propagate c ch hch_child hall
  have hno := reconstructed_noncentral_legal_step1_ancestor_step1_not_all_central_step3_no_origin c ch hstep 0 i₀ hp hnz
  have ⟨d, hd_mem, _, _⟩ := hstep 0 i₀ hp hnz
  have hcs_nonempty : (copySource c (c.form (ch 1).typ) (c.occ (ch 0).typ i₀) 0).Nonempty := ⟨(d, 0), hd_mem⟩
  have hz := hleg 0 i₀ 0 hcs_nonempty hno
  exact hnz hz

/-- Step 2 of the blueprint proof of `reconstructed_noncentral_legal_step1_ancestor`:
Choose a shortest central-child chain ending at such an ancestor. -/
private lemma reconstructed_noncentral_legal_step1_ancestor_step2_min_n_find_min {P : Protoset}
    (c : MacroCertificate P) (ch : ℕ → DecTile c)
    (hn : ∃ n, ¬ c.IsCentral (ch n).typ) :
    ∃ m, ¬ c.IsCentral (ch m).typ ∧ ∀ i < m, c.IsCentral (ch i).typ := by
  have : DecidablePred (fun n => ¬ c.IsCentral (ch n).typ) := Classical.decPred _
  have hX := Nat.findX hn
  use hX.1
  rcases hX.2 with ⟨h1, h2⟩
  refine ⟨h1, fun i hi => ?_⟩
  have hni := h2 i hi
  exact of_not_not hni

private lemma reconstructed_noncentral_legal_step1_ancestor_step2_min_n_hasOrigin_shift_aux {P : Protoset}
    (c : MacroCertificate P) (ch : ℕ → DecTile c) (m N : ℕ)
    (i : c.Side (ch N).typ) (k : Fin 5)
    (h : HasOrigin c ch N i k) :
    ∀ n, (hn : N = m + n) → HasOrigin c (fun x => ch (m + x)) n (cast (by rw [hn]) i) k := by
  induction h with
  | origin N' i' k' he =>
    intro n hn
    cases hn
    apply HasOrigin.origin
    exact he
  | step N' i' k' d k'' hc ho ih =>
    intro n hn
    cases hn
    have H : (m + n + 1) = m + (n + 1) := by omega
    apply @HasOrigin.step _ c (fun x => ch (m + x)) n i' k' (cast (by rw [H]) d) k''
    · have h_eq : (m + n + 1) = m + (n + 1) := H
      cases h_eq
      exact hc
    · exact (ih (n + 1) H)

/-- Step 2 of the blueprint proof of `reconstructed_noncentral_legal_step1_ancestor`:
Shift the origin. -/
private lemma reconstructed_noncentral_legal_step1_ancestor_step2_min_n_hasOrigin_shift {P : Protoset}
    (c : MacroCertificate P) (ch : ℕ → DecTile c) (m n : ℕ)
    (i : c.Side (ch (m + n)).typ) k :
      HasOrigin c ch (m + n) i k →
      HasOrigin c (fun x => ch (m + x)) n i k := by
  intro h
  have h_aux := reconstructed_noncentral_legal_step1_ancestor_step2_min_n_hasOrigin_shift_aux c ch m (m + n) i k h n rfl
  exact h_aux

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
        ch' n = E ∧ ∀ i < n, c.IsCentral (ch' i).typ := by
  have _ := hH; have _ := hK
  rcases reconstructed_noncentral_legal_step1_ancestor_step2_min_n_find_min c ch hn with ⟨m, hnm, hcent⟩
  use ch m
  constructor
  · refine ⟨fun x => ch (m + x), ?_, ?_, ?_⟩
    · exact rfl
    · intro i
      have heq : m + (i + 1) = m + i + 1 := by omega
      have hc := hch_child (m + i)
      rwa [← heq] at hc
    · intro n i k hNonempty hNoOrig
      dsimp at hNonempty hNoOrig ⊢
      have heq : m + (n + 1) = m + n + 1 := by omega
      have hNonempty' : (copySource c (c.form (ch (m + n + 1)).typ) (c.occ (ch (m + n)).typ i) k).Nonempty := by
        rwa [← heq]
      have hNoOrig' : ¬ HasOrigin c ch (m + n) i k := by
        intro h
        apply hNoOrig
        exact reconstructed_noncentral_legal_step1_ancestor_step2_min_n_hasOrigin_shift c ch m n i k h
      exact hleg (m + n) i k hNonempty' hNoOrig'
  · refine ⟨hnm, m, ch, hch0, hch_child, rfl, hcent⟩

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
    False := by
  have _ := hH
  have _ := hK
  have _ := hA
  have _ := hE_leg
  have _ := hch_end
  have _ := hE_nc
  subst hn'2
  have hch_child0 : IsChildOf c (ch' 1) (ch' 0) := hch_child 0 (by decide)
  have hcent1 : c.IsCentral (ch' 1).typ := hch_cent 1 (by decide)
  
  have H5 : (ch' 0).typ = c.central K.α := by
    rw [hch0]
    rfl
    
  have H6 : c.owner (ch' 0).typ = K.α := by
    rw [H5]
    exact c.g5_central_owner K.α

  have H7 : c.form (ch' 1).typ = K.α := by
    dsimp [IsChildOf, headerSubstitution, IsChildOfWith] at hch_child0
    rw [← hch_child0.1, H6]

  have H11 : c.kind (c.form (ch' 1).typ) = Geometry.FormKind.large := by
    have H11_aux := (c.g5_large_iff (ch' 1).typ).mpr
    dsimp [Geometry.MacroData.IsCentral] at hcent1
    apply H11_aux
    exact hcent1.symm

  have HK_not_large : c.kind K.α ≠ Geometry.FormKind.large := by
    have Hh_form : c.form h.1 = K.α := hh.1
    rw [← Hh_form]
    intro H
    apply hnc
    dsimp [Geometry.MacroData.IsCentral]
    have Haux := (c.g5_large_iff h.1).mp H
    exact Haux.symm
    
  rw [H7] at H11
  exact HK_not_large H11

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

/-- Step 1 of the blueprint proof of `alignment_complete_step1_macroside_eq`: Rank
matching and legality find a different block and a rank-one child side on one
of its macrosides that coincides with the first listed child side of `d`. -/
private lemma alignment_complete_step1_macroside_eq_step1_rank_one (c : MacroCertificate P)
    (hH : c.Hereditary) (T : PlaneTiling (typedDecoration c))
    (part : MacroPartition c T) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (j : part.ι) (d : Fin (c.Q.disk (part.block j).α).n)
    (hrank : RankMatched c part j d)
    (hmode : ∀ j' : part.ι, j' ≠ j → ∀ e, ModeUniform c (part.block j') e) :
    ∃ (j' : part.ι) (_hneq : j' ≠ j)
      (e : Fin (c.Q.disk (part.block j').α).n),
      ∃ (o₀ o : c.SideOcc),
        (c.outerList (part.block j).α d).head? = some o₀ ∧
        o₀ ∈ c.outerList (part.block j).α d ∧
        o ∈ c.outerList (part.block j').α e ∧
        c.rankIn (part.block j').α e o = 1 ∧
        IsRankU c ((part.block j').col o.1 o.2 3) ∧
        (part.block j').childSide o = (part.block j).childSide o₀ ∧
        (part.block j').col o.1 o.2 3 = (part.block j).col o₀.1 o₀.2 3 := by
  sorry

/-- Step 2 of the blueprint proof of `alignment_complete_step1_macroside_eq`: An
 opposing macroside cannot end inside a completely matched child segment or
 between consecutive segments, so all listed sides of `d` stay on the same `e`.
 -/
private lemma alignment_complete_step1_macroside_eq_step2_same_opposing_macroside
    (c : MacroCertificate P) (hH : c.Hereditary) (T : PlaneTiling (typedDecoration c))
    (part : MacroPartition c T) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (j j' : part.ι) (hneq : j' ≠ j)
    (d : Fin (c.Q.disk (part.block j).α).n)
    (e : Fin (c.Q.disk (part.block j').α).n)
    (hrank : RankMatched c part j d)
    (hmode : ∀ j'' : part.ι, j'' ≠ j → ∀ e'', ModeUniform c (part.block j'') e'')
    (hfirst : ∃ (o₀ o : c.SideOcc),
      (c.outerList (part.block j).α d).head? = some o₀ ∧
      o₀ ∈ c.outerList (part.block j).α d ∧
      o ∈ c.outerList (part.block j').α e ∧
      c.rankIn (part.block j').α e o = 1 ∧
      IsRankU c ((part.block j').col o.1 o.2 3) ∧
      (part.block j').childSide o = (part.block j).childSide o₀ ∧
      (part.block j').col o.1 o.2 3 = (part.block j).col o₀.1 o₀.2 3) :
    ∀ o ∈ c.outerList (part.block j).α d, ∃ o' ∈ c.outerList (part.block j').α e,
      (part.block j').childSide o' = (part.block j).childSide o ∧
      c.rankIn (part.block j').α e o' = c.rankIn (part.block j).α d o ∧
      (part.block j').col o'.1 o'.2 3 = (part.block j).col o.1 o.2 3 := by
  sorry

/-- Step 3 of the blueprint proof of `alignment_complete_step1_macroside_eq`: If
 the trace reaches every child of `d`, mode-uniformity prevents the opposing
 macroside `e` from having a further ranked child beyond the end of `d`. -/
private lemma alignment_complete_step1_macroside_eq_step3_not_longer
    (c : MacroCertificate P) (hH : c.Hereditary) (T : PlaneTiling (typedDecoration c))
    (part : MacroPartition c T) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (j j' : part.ι) (hneq : j' ≠ j)
    (d : Fin (c.Q.disk (part.block j).α).n)
    (e : Fin (c.Q.disk (part.block j').α).n)
    (hrank : RankMatched c part j d)
    (hmode : ∀ j'' : part.ι, j'' ≠ j → ∀ e'', ModeUniform c (part.block j'') e'')
    (htrace : ∀ o ∈ c.outerList (part.block j).α d,
      ∃ o' ∈ c.outerList (part.block j').α e,
        (part.block j').childSide o' = (part.block j).childSide o ∧
        c.rankIn (part.block j').α e o' = c.rankIn (part.block j).α d o ∧
        (part.block j').col o'.1 o'.2 3 = (part.block j).col o.1 o.2 3) :
    (c.outerList (part.block j').α e).length ≤
      (c.outerList (part.block j).α d).length := by
  sorry

/-- Step 1 of the blueprint proof of
`alignment_complete_step1_macroside_eq_step4_endpoints`: express a translated
macroside as the union of the translated outer child sides listed on it. -/
private lemma alignment_complete_step1_macroside_eq_step4_endpoints_step1_union
    (c : MacroCertificate P) (hH : c.Hereditary) (K : ColouredBlock c)
    (d : Fin (c.Q.disk K.α).n) :
    K.macroSide d = ⋃ o ∈ c.outerList K.α d, K.childSide o := by
  sorry

/-- Step 2 of the blueprint proof of
`alignment_complete_step1_macroside_eq_step4_endpoints`: a forward trace of
the ordered outer-side lists, together with the non-longer bound, is also
surjective onto the opposing list. -/
private lemma alignment_complete_step1_macroside_eq_step4_endpoints_step2_trace_surjective
    (c : MacroCertificate P) (K K' : ColouredBlock c)
    (d : Fin (c.Q.disk K.α).n) (e : Fin (c.Q.disk K'.α).n)
    (htrace : ∀ o ∈ c.outerList K.α d,
      ∃ o' ∈ c.outerList K'.α e,
        K'.childSide o' = K.childSide o ∧
        c.rankIn K'.α e o' = c.rankIn K.α d o ∧
        K'.col o'.1 o'.2 3 = K.col o.1 o.2 3)
    (hlen : (c.outerList K'.α e).length ≤ (c.outerList K.α d).length) :
    ∀ o' ∈ c.outerList K'.α e, ∃ o ∈ c.outerList K.α d,
      K'.childSide o' = K.childSide o ∧
      c.rankIn K'.α e o' = c.rankIn K.α d o ∧
      K'.col o'.1 o'.2 3 = K.col o.1 o.2 3 := by
  sorry

/-- Step 4 of the blueprint proof of `alignment_complete_step1_macroside_eq`:
 Once the trace is fixed and the opposing side is not longer, coverage and
 disjoint interiors force both endpoints to agree, hence the macrosides agree.
 -/
private lemma alignment_complete_step1_macroside_eq_step4_endpoints
    (c : MacroCertificate P) (hH : c.Hereditary) (T : PlaneTiling (typedDecoration c))
    (part : MacroPartition c T) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (j j' : part.ι) (hneq : j' ≠ j)
    (d : Fin (c.Q.disk (part.block j).α).n)
    (e : Fin (c.Q.disk (part.block j').α).n)
    (hrank : RankMatched c part j d)
    (hmode : ∀ j'' : part.ι, j'' ≠ j → ∀ e'', ModeUniform c (part.block j'') e'')
    (htrace : ∀ o ∈ c.outerList (part.block j).α d,
      ∃ o' ∈ c.outerList (part.block j').α e,
        (part.block j').childSide o' = (part.block j).childSide o ∧
        c.rankIn (part.block j').α e o' = c.rankIn (part.block j).α d o ∧
        (part.block j').col o'.1 o'.2 3 = (part.block j).col o.1 o.2 3)
    (hlen : (c.outerList (part.block j').α e).length ≤
      (c.outerList (part.block j).α d).length) :
    (part.block j').macroSide e = (part.block j).macroSide d := by
  have _ := T
  have _ := hT
  have _ := hL
  have _ := hneq
  have _ := hrank
  have _ := hmode
  have hforward := htrace
  have hreverse :=
    alignment_complete_step1_macroside_eq_step4_endpoints_step2_trace_surjective
      c (part.block j) (part.block j') d e htrace hlen
  rw [alignment_complete_step1_macroside_eq_step4_endpoints_step1_union
    c hH (part.block j') e,
    alignment_complete_step1_macroside_eq_step4_endpoints_step1_union
      c hH (part.block j) d]
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨o', ho'⟩ := Set.mem_iUnion.1 hx
    obtain ⟨ho'mem, hx⟩ := Set.mem_iUnion.1 ho'
    obtain ⟨o, homem, hside, _, _⟩ := hreverse o' ho'mem
    refine Set.mem_iUnion.2 ⟨o, Set.mem_iUnion.2 ⟨homem, ?_⟩⟩
    rw [← hside]
    exact hx
  · intro x hx
    obtain ⟨o, ho⟩ := Set.mem_iUnion.1 hx
    obtain ⟨homem, hx⟩ := Set.mem_iUnion.1 ho
    obtain ⟨o', ho'mem, hside, _, _⟩ := hforward o homem
    refine Set.mem_iUnion.2 ⟨o', Set.mem_iUnion.2 ⟨ho'mem, ?_⟩⟩
    rw [hside]
    exact hx

/-- Step 1 of the blueprint proof of `alignment_complete`: By tracing the
coinciding segments and using the mode-uniformity hypothesis to prevent the
opposing side from being longer, we find an opposing macroside `e` of block `j'`
that exactly shares the geometric macroside segment. -/
private lemma alignment_complete_step1_macroside_eq (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (part : MacroPartition c T)
    (hT : IsProper c T) (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (j : part.ι) (d : Fin (c.Q.disk (part.block j).α).n)
    (hrank : RankMatched c part j d)
    (hmode : ∀ j' : part.ι, j' ≠ j → ∀ e, ModeUniform c (part.block j') e) :
    ∃ (j' : part.ι) (_hneq : j' ≠ j) (e : Fin (c.Q.disk (part.block j').α).n),
      (part.block j').macroSide e = (part.block j).macroSide d := by
  obtain ⟨j', hneq, e, o₀, o, hfirst, ho₀, ho, hrank_one, hpositive, hside, hcell⟩ :=
    alignment_complete_step1_macroside_eq_step1_rank_one c hH T part hT hL j d hrank hmode
  have htrace := alignment_complete_step1_macroside_eq_step2_same_opposing_macroside c hH T part
    hT hL j j' hneq d e hrank hmode
    ⟨o₀, o, hfirst, ho₀, ho, hrank_one, hpositive, hside, hcell⟩
  have hlen := alignment_complete_step1_macroside_eq_step3_not_longer c hH T part hT hL j j'
    hneq d e hrank hmode htrace
  refine ⟨j', hneq, e, ?_⟩
  exact alignment_complete_step1_macroside_eq_step4_endpoints c hH T part hT hL j j' hneq d e
    hrank hmode htrace hlen

/-- Step 2a of the blueprint proof of `alignment_complete_step2_subdivision_eq`: The length of
the child side subdivision is uniquely determined by the geometric macro side.
Thus coinciding macro sides have subdivisions of the same length. -/
private lemma alignment_complete_step2_subdivision_eq_step1_length (c : MacroCertificate P)
    (hH : c.Hereditary) (T : PlaneTiling (typedDecoration c)) (part : MacroPartition c T)
    (hT : IsProper c T) (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
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
    (hT : IsProper c T) (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
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
    (hT : IsProper c T) (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (j j' : part.ι) (hneq : j' ≠ j)
    (d : Fin (c.Q.disk (part.block j).α).n) (e : Fin (c.Q.disk (part.block j').α).n)
    (hrank : RankMatched c part j d)
    (hmode : ∀ j'' : part.ι, j'' ≠ j → ∀ e'', ModeUniform c (part.block j'') e'')
    (hmacro : (part.block j').macroSide e = (part.block j).macroSide d) :
    List.Forall₂ (fun o o' => (part.block j).childSide o = (part.block j').childSide o')
      (c.outerList (part.block j).α d) (c.outerList (part.block j').α e) := by
  rw [List.forall₂_iff_get]
  have hlen := alignment_complete_step2_subdivision_eq_step1_length c hH T part hT hL j j' hneq d e
    hrank hmode hmacro
  refine ⟨hlen, fun k hk hk' => ?_⟩
  exact alignment_complete_step2_subdivision_eq_step2_pointwise c hH T part hT hL j j' hneq d e hrank
    hmode hmacro hlen k hk hk'

/-- `lem:comp/alignment` (with the review's mode-uniformity hypothesis): in a
proper plane tiling of legal typed tiles (so that every outer fourth cell is
zero or the generated rank of its side, review addition of 13 October 2026:
without properness and legality a constant colouring satisfies the
hypotheses on the three-block counterexample), partitioned into macroblocks,
if every child side of the macroside `d` of block `j` has a complete opposing
side with the same positive rank, and every macroside of every other block is
mode-uniform, then `d` has a complete opposing macroside with the same
ordered subdivision. -/
theorem alignment_complete (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (part : MacroPartition c T)
    (hT : IsProper c T) (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (j : part.ι) (d : Fin (c.Q.disk (part.block j).α).n)
    (hrank : RankMatched c part j d)
    (hmode : ∀ j' : part.ι, j' ≠ j → ∀ e, ModeUniform c (part.block j') e) :
    OpposingMacroside c part j d := by
  obtain ⟨j', hneq, e, hmacro⟩ :=
    alignment_complete_step1_macroside_eq c hH T part hT hL j d hrank hmode
  refine ⟨j', hneq, e, hmacro, ?_⟩
  exact alignment_complete_step2_subdivision_eq c hH T part hT hL j j' hneq d e hrank hmode hmacro

private lemma recon_exists_interior_meet {ι : Type*} [Countable ι] (F : ι → Set Pt)
    (hF : ∀ i, IsClosed (F i)) {U : Set Pt} (hU : IsOpen U) (hne : U.Nonempty)
    (hsub : U ⊆ ⋃ i, F i) : ∃ i, (U ∩ interior (F i)).Nonempty := by
  let G : Option ι → Set Pt := fun o => o.elim Uᶜ F
  have hG : ∀ o, IsClosed (G o) := by
    rintro (_ | i)
    · exact hU.isClosed_compl
    · exact hF i
  have hcov : ⋃ o, G o = univ := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ U
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (hsub hx)
      exact mem_iUnion.2 ⟨some i, hi⟩
    · exact mem_iUnion.2 ⟨none, hx⟩
  have hd := dense_iUnion_interior_of_closed hG hcov
  obtain ⟨x, hxU, hx⟩ := hd.inter_open_nonempty U hU hne
  obtain ⟨o, ho⟩ := mem_iUnion.1 hx
  rcases o with _ | i
  · exact absurd (interior_subset ho) (fun h => h hxU)
  · exact ⟨i, x, hxU, ho⟩

private lemma recon_isClosed_carrier {Q : Protoset} (A : PlacedTile Q) : IsClosed A.carrier := by
  unfold PlacedTile.carrier
  exact ((Q.disk A.form).compact.vadd A.anchor).isClosed

private lemma recon_mem_support_block (c : MacroCertificate P) (K : ColouredBlock c) (x : Pt) :
    x ∈ support K.tiles ↔ x - K.v ∈ c.σ.θ • (c.Q.disk K.α).carrier := by
  rw [← c.σ.support_eq K.α, c.rule_eq K.α]
  simp only [support, ColouredBlock.tiles, ColouredBlock.placed, ColouredBlock.tileOf,
    PlacedTile.carrier, mem_iUnion, mem_image, mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨X, ⟨t, ht, rfl⟩, hx⟩
    refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
    rw [mem_vadd_set_iff_neg_vadd_mem] at hx ⊢
    simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hx
  · rintro ⟨X, ⟨t, ht, rfl⟩, hx⟩
    refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
    rw [mem_vadd_set_iff_neg_vadd_mem] at hx ⊢
    simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hx

private lemma recon_interior_meet_block (c : MacroCertificate P) (K : ColouredBlock c) {U : Set Pt}
    (hU : IsOpen U) (hne : U.Nonempty) (hsub : U ⊆ support K.tiles) :
    ∃ A ∈ K.tiles, (U ∩ interior A.carrier).Nonempty := by
  obtain ⟨⟨t, ht⟩, hmeet⟩ := recon_exists_interior_meet
    (fun s : {t : c.Typ // c.owner t = K.α} => (K.placed s.1).carrier)
    (fun s => recon_isClosed_carrier _) hU hne (by
      intro x hx
      obtain ⟨A, hA, hxA⟩ := mem_iUnion₂.1 (hsub hx)
      obtain ⟨t, ht, rfl⟩ := hA
      exact mem_iUnion.2 ⟨⟨t, ht⟩, hxA⟩)
  exact ⟨K.placed t, ⟨t, ht, rfl⟩, hmeet⟩

private lemma recon_exists_type (c : MacroCertificate P) (T : PlaneTiling (typedDecoration c))
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X)) (part : MacroPartition c T) (j : part.ι) :
    ∃ t : c.Typ, c.form t = (part.block j).α := by
  have hmem : (part.block j).placed (c.central (part.block j).α) ∈ T.tiles := by
    rw [← part.cover]
    exact mem_iUnion.2 ⟨j, c.central (part.block j).α, c.g5_central_owner _, rfl⟩
  obtain ⟨ch, h0, hR, -⟩ := hL _ hmem
  refine ⟨(ch 1).typ, ?_⟩
  have h := (hR 0).1
  rw [h0] at h
  rw [← h]
  exact c.g5_central_owner _

/-- Step 1 of the blueprint proof of `composed_proper`: reconstruction gives a plane tiling.
("Assembly partitions the plane into the macroblocks.  Their underlying polygons are scaled
parent polygons, so replacing and scaling them preserves coverage and disjoint interiors.")
Properness and legality of `T` make every block a `BlockContext`, so `boundary_header_constant`
gives each block a common header whose type has the block's form; the reconstructed parent of
that type has the scaled-down block polygon. -/
private lemma composed_proper_step1_reconstruction (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X)) (part : MacroPartition c T) :
    ∃ T' : PlaneTiling (typedDecoration c), IsReconstruction c part T' := by
  have _ := hH; have _ := hT
  choose t ht using recon_exists_type c T hL part
  set θ := c.σ.θ with hθdef
  have hθ : θ ≠ 0 := (zero_lt_one.trans c.σ.one_lt).ne'
  let X : part.ι → PlacedTile (typedDecoration c) := fun j =>
    ⟨reconstruct c (part.block j) (t j), θ⁻¹ • (part.block j).v⟩
  have hcar : ∀ j x, x ∈ (X j).carrier ↔ θ • x ∈ support (part.block j).tiles := by
    intro j x
    rw [recon_mem_support_block, mem_smul_set_iff_inv_smul_mem₀ hθ]
    simp only [PlacedTile.carrier, X, reconstruct, ht, mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, smul_sub, inv_smul_smul₀ hθ]
    rw [neg_add_eq_sub]
  have hsupp : ∀ y, ∃ j, y ∈ support (part.block j).tiles := by
    intro y
    have hy : y ∈ support T.tiles := by rw [T.cover]; trivial
    obtain ⟨A, hA, hyA⟩ := mem_iUnion₂.1 hy
    rw [← part.cover] at hA
    obtain ⟨j, hj⟩ := mem_iUnion.1 hA
    exact ⟨j, mem_iUnion₂.2 ⟨A, hj, hyA⟩⟩
  refine ⟨⟨range X, ?_, ?_⟩, ?_, ?_⟩
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨j, hj⟩ := hsupp (θ • x)
    exact mem_iUnion₂.2 ⟨X j, mem_range_self j, (hcar j x).2 hj⟩
  · rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ hjk
    rw [Function.onFun, Set.disjoint_iff]
    rintro y ⟨hyj, hyk⟩
    have hjk' : j ≠ k := fun h => hjk (h ▸ rfl)
    set W := θ • (interior (X j).carrier ∩ interior (X k).carrier) with hW
    have hWo : IsOpen W := (isOpen_interior.inter isOpen_interior).smul₀ hθ
    have hWj : W ⊆ support (part.block j).tiles := by
      rintro _ ⟨z, hz, rfl⟩; exact (hcar j z).1 (interior_subset hz.1)
    have hWk : W ⊆ support (part.block k).tiles := by
      rintro _ ⟨z, hz, rfl⟩; exact (hcar k z).1 (interior_subset hz.2)
    obtain ⟨A, hA, hWA⟩ := recon_interior_meet_block c _ hWo ⟨θ • y, y, ⟨hyj, hyk⟩, rfl⟩ hWj
    obtain ⟨B, hB, z, ⟨-, hzA⟩, hzB⟩ := recon_interior_meet_block c _ (hWo.inter isOpen_interior) hWA
      (inter_subset_left.trans hWk)
    have hAT : A ∈ T.tiles := part.cover ▸ mem_iUnion.2 ⟨j, hA⟩
    have hBT : B ∈ T.tiles := part.cover ▸ mem_iUnion.2 ⟨k, hB⟩
    have hAB : A ≠ B := by
      rintro rfl
      exact Set.disjoint_left.1 (part.disjoint hjk') hA hB
    exact Set.disjoint_left.1 (T.disjoint hAT hBT hAB) hzA hzB
  · rintro _ ⟨j, rfl⟩
    exact ⟨j, (smul_inv_smul₀ hθ _).symm, rfl⟩
  · intro j
    exact ⟨X j, mem_range_self j, (smul_inv_smul₀ hθ _).symm, rfl⟩

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
  have ⟨T', hrec⟩ := composed_proper_step1_reconstruction c hH T hT hL part
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
  let K := part.block j
  have hmem : ∀ t, c.owner t = K.α → K.placed t ∈ T.tiles := by
    intro t ht
    rw [← part.cover]
    exact Set.mem_iUnion.2 ⟨j, ⟨t, ht, rfl⟩⟩
  have hprops : ∀ X ∈ T.tiles,
      IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
        InnerActive c (tileDec X) := by
    intro X hX
    have hlegal := hL X hX
    exact ⟨(headerLegal_properties_step2_normal_id c hH (tileDec X) hlegal).1,
      (headerLegal_properties_step2_normal_id c hH (tileDec X) hlegal).2,
      headerLegal_properties_step6_inner c hH (tileDec X) hlegal⟩
  constructor
  · intro t i ht hi hnon
    have hX : K.placed t ∈ T.tiles := hmem t ht
    have hXactive : IsNontrivial c (tileDec (K.placed t)) i := by
      exact hnon
    obtain ⟨Y, hY, hYX, l, hside, hcell⟩ := hT (K.placed t) hX i hXactive
    have hmatch := asm_match c
      ⟨(hprops _ hX).1, (hprops _ hX).2.1⟩
      ⟨(hprops _ hY).1, (hprops _ hY).2.1⟩ i l hi hcell
    obtain ⟨hinner, hedge⟩ := hmatch
    let p : c.SideOcc := c.partner (c.occ t i)
    obtain ⟨hpne, hpowner, hpside⟩ := c.g1_partner _ hi
    rcases c.g1_edge_unique _ _ hi hinner hedge.symm with hsame | hpartner_eq
    · have hside' : asmSide c Y.anchor (c.occ (tileDec Y).typ l) =
          asmSide c (K.placed t).anchor (c.occ t i) := hside
      rw [hsame] at hside'
      have hanchor := asm_side_cancel c hside'
      exfalso
      exact hYX (asm_tile_unique c T hY hX (congrArg Sigma.fst hsame) hanchor)
    · let s : c.Typ := (tileDec Y).typ
      have hs : (tileDec Y).typ = s := rfl
      change c.Side s at l
      have hsp : s = p.1 := hs.symm.trans (congrArg Sigma.fst hpartner_eq)
      have hsowner : c.owner s = K.α := by
        rw [hsp, hpowner, ht]
      have hownerY : c.owner (tileDec Y).typ = K.α := by
        rw [hs, hsowner]
      have hsne : s ≠ t := by
        intro hst
        exact hpne (hsp.symm.trans (hs.trans hst))
      refine ⟨(tileDec Y).typ, l, hownerY, hsne, ?_, ?_⟩
      · unfold ColouredBlock.childSide
        rw [← vadd_vadd, ← vadd_vadd]
        change K.v +ᵥ c.occSide (c.occ (tileDec Y).typ l) =
          K.v +ᵥ c.occSide (c.occ t i)
        rw [hpartner_eq, hpside]
      · have hanchor : Y.anchor = (K.placed t).anchor - c.anchor t + c.anchor p.1 := by
          have hside' : asmSide c Y.anchor (c.occ (tileDec Y).typ l) =
              asmSide c (K.placed t).anchor (c.occ t i) := hside
          rw [hpartner_eq] at hside'
          have hside_partner' : asmSide c (c.anchor p.1) p =
              asmSide c (c.anchor t) (c.occ t i) := hpside
          apply asm_side_cancel c (o := p)
          rw [hside']
          unfold asmSide at hside_partner' ⊢
          rw [← vadd_vadd, hside_partner', vadd_vadd, sub_add_cancel]
        have hY' : K.placed (tileDec Y).typ ∈ T.tiles := hmem _ hownerY
        have hYeq : Y = K.placed (tileDec Y).typ := by
          apply asm_tile_unique c T hY hY'
          · rfl
          · change Y.anchor = K.v + c.anchor (tileDec Y).typ
            have hps : p.1 = (tileDec Y).typ := hsp.symm.trans hs.symm
            rw [hanchor, hps]
            change (K.v + c.anchor t) - c.anchor t + c.anchor (tileDec Y).typ = _
            rw [add_sub_cancel_right]
        intro k
        have hform : tileDec Y = K.tileOf (tileDec Y).typ :=
          congrArg PlacedTile.form hYeq
        have hcell' : (K.tileOf (tileDec Y).typ).cell l k =
            (tileDec (K.placed t)).cell i k := by
          have hform' := congrArg (decTileEquiv c) hform
          change (⟨(tileDec Y).typ, (tileDec Y).cell⟩ :
            Σ t, c.Side t → Fin 5 → U c) =
            ⟨(tileDec Y).typ, (K.tileOf (tileDec Y).typ).cell⟩ at hform'
          have hcells : (tileDec Y).cell = (K.tileOf (tileDec Y).typ).cell :=
            eq_of_heq (Sigma.mk.inj hform').2
          exact (congrFun (congrFun hcells l) k).symm.trans (hcell k)
        exact hcell'
  · intro t ht htc
    apply hL (K.placed t) (hmem t ht)

/-- Step 1 of the blueprint proof of `reconstructed_acyclic_legal_step2_noncentral`:
Recover the common header of the block that reconstructs a noncentral tile. -/
private lemma reconstructed_acyclic_legal_step2_noncentral_step1_common_header
    {P : Protoset} (c : MacroCertificate P) (hH : c.Hereditary)
    (T : PlaneTiling (typedDecoration c)) (hT : IsProper c T)
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X))
    (part : MacroPartition c T) (T' : PlaneTiling (typedDecoration c))
    (hrec : IsReconstruction c part T') (hT' : IsProper c T')
    (hN : ∀ X ∈ T'.tiles, IsNormal c (tileDec X) ∧ IsIdentityCorrect c (tileDec X) ∧
      InnerActive c (tileDec X))
    (hex : IsExactComposition c T' T)
    (Y : PlacedTile (typedDecoration c)) (hY : Y ∈ T'.tiles)
    (j : part.ι) (hj : (part.block j).v = c.σ.θ • Y.anchor)
    (heq : tileDec Y = reconstruct c (part.block j) (tileDec Y).typ)
    (hctx : BlockContext c (part.block j)) :
    CommonHeader c (part.block j) (headerOf c (tileDec Y)) := by
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
  obtain ⟨j, hj, heq⟩ := hrec.1 Y hY
  have hh := reconstructed_acyclic_legal_step2_noncentral_step1_common_header c hH T hT hL part T'
    hrec hT' hN hex Y hY j hj heq (hctx j)
  have hA : headerLegal c (part.block j).centre := by
    have hmem : (part.block j).placed (c.central (part.block j).α) ∈ T.tiles := by
      rw [← part.cover]
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      change ∃ t, c.owner t = (part.block j).α ∧
        (part.block j).placed (c.central (part.block j).α) = (part.block j).placed t
      exact ⟨c.central (part.block j).α, c.g5_central_owner _, rfl⟩
    exact hL _ hmem
  have hleg := reconstructed_noncentral_legal c hH (part.block j) (hctx j)
    (headerOf c (tileDec Y)) hh hA hnc
  rw [heq]
  exact hleg

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

/-- Step 4 of the blueprint proof of `reconstructed_acyclic_legal`: "Let `D` be such a parent,
of type `t`, and let `A` be its original legal central child."  By exactness of the composition
(`hex`, `lem:comp/exact`), the child of `D = tileDec X` of the central type of its form is a
tile of `T`, hence legal, and it is a child of `D` under the repaired substitution.  (The
second-level parent `C` of type `r` of the blueprint enters the argument only through its
form, which is the owner form of `t`: see step 5.) -/
private lemma reconstructed_acyclic_legal_step4_parent {P : Protoset}
    (c : MacroCertificate P) (T : PlaneTiling (typedDecoration c))
    (hL : ∀ X ∈ T.tiles, headerLegal c (tileDec X)) (T' : PlaneTiling (typedDecoration c))
    (hex : IsExactComposition c T' T) (X : PlacedTile (typedDecoration c)) (hX : X ∈ T'.tiles) :
    ∃ A : DecTile c, IsChildOf c (tileDec X) A ∧ A.typ = c.central (c.form (tileDec X).typ) ∧
      headerLegal c A := by
  obtain ⟨blk, hblk, hcov⟩ := hex
  obtain ⟨⟨hform, hchild⟩, -⟩ := hblk ⟨X, hX⟩
  refine ⟨(blk ⟨X, hX⟩).tileOf (c.central (blk ⟨X, hX⟩).α),
    hchild _ (c.g5_central_owner _), congrArg c.central hform.symm, ?_⟩
  have hmem : (blk ⟨X, hX⟩).placed (c.central (blk ⟨X, hX⟩).α) ∈ T.tiles := by
    rw [hcov]
    exact Set.mem_iUnion.2 ⟨⟨X, hX⟩, c.central _, c.g5_central_owner _, rfl⟩
  exact hL _ hmem

/-- Step 1 of the blueprint proof of `reconstructed_acyclic_legal_step5_parent_noncentral`:
"If it were central, its large form would be fixed by the central-child form map.  It and its
central child `t` would have the same large form": if the owner form of the central type `t`
(the form of the parent `C`) were large, then `form t = owner t`. -/
private lemma reconstructed_acyclic_legal_step5_parent_noncentral_step1_same_large_form
    {P : Protoset} (c : MacroCertificate P) {t : c.Typ} (hcent : c.IsCentral t)
    (h_large : c.kind (c.owner t) = .large) : c.form t = c.owner t := by
  have h1 := c.g5_central_fixes_large _ h_large
  rw [hcent] at h1
  exact h1

/-- Step 2 of the blueprint proof of `reconstructed_acyclic_legal_step5_parent_noncentral`:
"and hence the same central child type, making `t` cyclic": a central type whose form is its
owner form is cyclic. -/
private lemma reconstructed_acyclic_legal_step5_parent_noncentral_step2_cyclic
    {P : Protoset} (c : MacroCertificate P) {t : c.Typ} (hcent : c.IsCentral t)
    (h_same_form : c.form t = c.owner t) : c.IsCyclic t := by
  show c.central (c.form t) = t
  rw [h_same_form]
  exact hcent

/-- Step 5 of the blueprint proof of `reconstructed_acyclic_legal`: "The type `r` is
noncentral.  If it were central, its large form would be fixed by the central-child form map.
It and its central child `t` would have the same large form, and hence the same central child
type, making `t` cyclic.  This contradicts the assumption on `D`."  The parent `C` of `D` has
form `owner t`, and by `g5_large_iff` its type `r` is noncentral exactly when this form is not
large; the step is therefore the statement that the owner form of the central acyclic type `t`
is not large. -/
private lemma reconstructed_acyclic_legal_step5_parent_noncentral {P : Protoset}
    (c : MacroCertificate P) {t : c.Typ} (hcent : c.IsCentral t) (hcyc : ¬ c.IsCyclic t) :
    c.kind (c.owner t) ≠ .large := by
  intro h_large
  exact hcyc (reconstructed_acyclic_legal_step5_parent_noncentral_step2_cyclic c hcent
    (reconstructed_acyclic_legal_step5_parent_noncentral_step1_same_large_form c hcent h_large))

/-- Step 1 of the blueprint proof of `reconstructed_acyclic_legal_step6_main`:
The origin argument from the noncentral legality lemma shows that a legal
ancestry chain of `A` (the legal central child of `D = tileDec X`, step 4) reaches a noncentral
type. Removing cyclic repetitions and checking forms gives length exactly two: `A <- E <- F`,
where `E, F` are legal, `F` is noncentral, `E` is central, and `E, D` have the same form. -/
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
    (A : DecTile c) (hXA : IsChildOf c (tileDec X) A)
    (hAtyp : A.typ = c.central (c.form (tileDec X).typ)) (hAleg : headerLegal c A)
    (hown : c.kind (c.owner (tileDec X).typ) ≠ .large)
    (h_other_nc : ∀ Y ∈ T'.tiles, ¬ c.IsCentral (tileDec Y).typ → headerLegal c (tileDec Y))
    (h_other_cyc : ∀ Y ∈ T'.tiles, c.IsCyclic (tileDec Y).typ → headerLegal c (tileDec Y)) :
    ∃ E F : DecTile c,
      IsChildOf c E A ∧
      IsChildOf c F E ∧
      headerLegal c E ∧
      headerLegal c F ∧
      c.IsCentral E.typ ∧
      ¬ c.IsCentral F.typ ∧
      c.form E.typ = c.form (tileDec X).typ := by sorry

private lemma step2_eq_central_no_outer (c : MacroCertificate P) {s : c.Typ} (hs : c.IsCentral s)
    (i : c.Side s) : ¬ c.IsOuter (c.occ s i) ∧ ¬ c.IsBoundary (c.occ s i) := by
  have h := c.g2_central (c.owner s)
  unfold MacroData.IsCentral at hs
  rw [hs] at h
  exact h i

private lemma step2_eq_central_large (c : MacroCertificate P) {s : c.Typ} (hs : c.IsCentral s) :
    c.kind (c.form s) = .large :=
  (c.g5_large_iff s).2 hs.symm

open Classical in
private lemma step2_eq_print_card (c : MacroCertificate P) {s : c.Typ} (hs : c.IsCentral s) :
    (Finset.univ.filter (fun d : c.Side s => c.IsPrint (c.occ s d))).card ≤
      Nat.card {e // c.marked (c.owner s) e} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_image_of_injective _ (sigma_mk_injective (i := s))]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le
    (f := c.printOcc (c.owner s)) (s := Finset.univ.filter (fun e => c.marked (c.owner s) e)))
  intro o ho
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ho ⊢
  obtain ⟨d, ⟨e, hm, h | h⟩, rfl⟩ := ho
  · exact ⟨e, hm, h.symm⟩
  · exfalso
    have h1 := c.g4_print_small _ e hm
    rw [← h] at h1
    rw [step2_eq_central_large c hs] at h1
    cases h1

private lemma step2_eq_isPrintOf_congr (c : MacroCertificate P) {β γ : c.Q.Form} (h : β = γ)
    (x : Fin (c.Q.disk β).n) (y : Fin (c.Q.disk γ).n) (hxy : x.val = y.val) (o : c.SideOcc) :
    c.IsPrintOf β x o ↔ c.IsPrintOf γ y o := by
  subst h
  rw [Fin.ext hxy]

private lemma step2_eq_identU_inj (c : MacroCertificate P) {e e' : c.EdgeId}
    (h : identU c e = identU c e') : e = e' := by
  simpa [identU] using h

private lemma step2_eq_not_on_path (c : MacroCertificate P) {s : c.Typ} (hs : c.IsCentral s)
    (i : c.Side s) (hm : ¬ c.IsMarked (c.occ s i)) (d : Fin (c.Q.disk (c.owner s)).n) (j : Fin 5) :
    c.occ s i ∉ c.path (c.owner s) d j := by
  intro hmem
  by_cases hg : c.IsGenuinePath (c.owner s) d j
  · exact hm (c.g7_marking _ (Or.inr (Or.inr (Or.inr ⟨d, j, hg, hmem⟩))))
  · rw [c.g4_path_trivial _ _ _ hg] at hmem
    have hp : c.port (c.owner s) d j = some (c.occ s i) := Option.mem_toList.1 hmem
    unfold MacroData.port at hp
    have hmem' := List.mem_of_getElem? hp
    exact (step2_eq_central_no_outer c hs i).1 (((c.g3_outerList_mem _ _ _).1 hmem').2.1)

private lemma step2_eq_cells (c : MacroCertificate P) (t : c.Typ) (cD cE : c.Side t → Fin 5 → U c)
    (cA : c.Side (c.central (c.form t)) → Fin 5 → U c) (F : DecTile c) (hcent : c.IsCentral t)
    (hnorm : IsNormal c ⟨t, cD⟩) (hXA : IsChildOf c ⟨t, cD⟩ ⟨c.central (c.form t), cA⟩)
    (hE_child : IsChildOf c ⟨t, cE⟩ ⟨c.central (c.form t), cA⟩) (hF_child : IsChildOf c F ⟨t, cE⟩) :
    cE = cD := by
  funext i k
  have hno := step2_eq_central_no_outer c hcent i
  have hownF : c.owner t = c.form F.typ := hF_child.1
  have h4 : cE i 4 = cD i 4 := by
    have hloc : IsLocal c (c.occ t i) 4 := by
      by_cases hm : c.IsMarked (c.occ t i)
      · by_cases hsp : c.special (c.occ t i) ∨ c.IsPrint (c.occ t i)
        · exact Or.inr (Or.inl ⟨hm, hsp, rfl⟩)
        · push_neg at hsp
          exact Or.inr (Or.inr ⟨hm, hsp, Or.inr rfl⟩)
      · exact Or.inl hm
    refine Eq.trans ?_ (hnorm i 4 hloc).symm
    simp only [prescribedCell, Fin.reduceEq, if_false, if_true]
    by_cases hp : c.IsPrint (c.occ t i)
    · rw [if_pos hp]
      obtain ⟨e, he⟩ := hp
      exact ((hF_child.2 i).1 (Fin.cast (by rw [hownF]) e)
        ((step2_eq_isPrintOf_congr c hownF e _ rfl _).1 he)).2
    · rw [if_neg hp]
      exact ((hF_child.2 i).2 hp).2.2.1
  by_cases hk : k = 4
  · subst hk
    exact h4
  by_cases hm : c.marked (c.form t) i
  · exact (((hE_child.2 (c.print (c.form t) i)).1 i ⟨hm, Or.inl rfl⟩).1 k hk).symm.trans
      (((hXA.2 _).1 i ⟨hm, Or.inl rfl⟩).1 k hk)
  · have hp : ¬ c.IsPrint (c.occ t i) := fun h => hm (c.g7_marking _ (Or.inr (Or.inr (Or.inl h))))
    obtain ⟨h0, h1, -, -, hnp, -, -, h3⟩ := (hF_child.2 i).2 hp
    refine Eq.trans ?_ (hnorm i k (Or.inl hm)).symm
    fin_cases k
    · simpa [prescribedCell] using h0
    · simpa [prescribedCell] using h1
    · have hnot := step2_eq_not_on_path c hcent i hm
      rw [hownF] at hnot
      simpa [prescribedCell] using hnp hnot
    · have h3' := h3 hno.1 hno.2
      show cE i 3 = prescribedCell c (c.occ t i) 3
      rw [prescribedCell, if_neg (by decide), if_pos rfl, if_pos ⟨hno.1, hno.2, hp⟩]
      exact h3'
    · exact absurd rfl hk

private lemma step2_eq_core (c : MacroCertificate P) (D E A F : DecTile c)
    (hcent : c.IsCentral D.typ) (hnorm : IsNormal c D) (hidc : IsIdentityCorrect c D)
    (hXA : IsChildOf c D A) (hAtyp : A.typ = c.central (c.form D.typ))
    (hown : c.kind (c.owner D.typ) ≠ .large)
    (hE_child : IsChildOf c E A) (hF_child : IsChildOf c F E)
    (hE_cent : c.IsCentral E.typ) (hF_nc : ¬ c.IsCentral F.typ)
    (hE_form : c.form E.typ = c.form D.typ) : E = D := by
  obtain ⟨t, cD⟩ := D
  obtain ⟨t', cE⟩ := E
  obtain ⟨a, cA⟩ := A
  dsimp only at *
  subst hAtyp
  have hownE : c.owner t' = c.form F.typ := hF_child.1
  have hQ' : c.kind (c.owner t') ≠ .large := by
    rw [hownE]
    exact fun h => hF_nc ((c.g5_large_iff _).1 h).symm
  have hEt : t' = t := by
    classical
    have hn : (c.Q.disk (c.form t)).n = (c.Q.disk (c.form t')).n := by rw [hE_form]
    let S1 := Finset.univ.filter (fun d : c.Side t => c.IsPrint (c.occ t d))
    let S2 := (Finset.univ.filter (fun d : c.Side t' => c.IsPrint (c.occ t' d))).image
      (Fin.cast hn.symm)
    let M := Finset.univ.filter (fun d : c.Side t => c.marked (c.form t) d)
    have hM : M.card = 4 * c.N := by
      rw [← c.g5_card_marked_large _ (step2_eq_central_large c hcent), Nat.card_eq_fintype_card,
        Fintype.card_subtype]
    have h1 : S1.card ≤ c.Qmax :=
      (step2_eq_print_card c hcent).trans (c.g5_card_marked_small _ hown)
    have h2 : S2.card ≤ c.Qmax :=
      Finset.card_image_le.trans ((step2_eq_print_card c hE_cent).trans
        (c.g5_card_marked_small _ hQ'))
    obtain ⟨d, hdM, hdS⟩ : ∃ d ∈ M, d ∉ S1 ∪ S2 := by
      by_contra hcon
      push_neg at hcon
      have := Finset.card_le_card (fun x hx => hcon x hx)
      have := Finset.card_union_le S1 S2
      have := c.g5_three_Q_lt
      omega
    simp only [M, S1, S2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, not_or] at hdM hdS
    obtain ⟨hd1, hd2⟩ := hdS
    set d' : c.Side t' := Fin.cast hn d with hd'
    have hd2' : ¬ c.IsPrint (c.occ t' d') := fun h => hd2 ⟨d', h, by ext; simp [hd']⟩
    have hin : c.IsInner (c.occ t d) := (step2_eq_central_no_outer c hcent d).1
    have hin' : c.IsInner (c.occ t' d') := (step2_eq_central_no_outer c hE_cent d').1
    have hD0 : cD d 0 = identU c (c.edge (c.occ t d)) := (hidc d).1 hin hd1
    have hE0 : cE d' 0 = identU c (c.edge (c.occ t' d')) := by
      have h := ((hF_child.2 d').2 hd2').1
      rw [prescribedFirst, if_pos hin'] at h
      exact h
    have hAD : cA (c.print (c.form t) d) 0 = cD d 0 :=
      ((hXA.2 (c.print (c.form t) d)).1 d ⟨hdM, Or.inl rfl⟩).1 0 (by decide)
    have hAE : cA (c.print (c.form t) d) 0 = cE d' 0 :=
      ((hE_child.2 (c.print (c.form t) d)).1 d'
        ((step2_eq_isPrintOf_congr c hE_form.symm d d' rfl _).1 ⟨hdM, Or.inl rfl⟩)).1 0 (by decide)
    have hedge : c.edge (c.occ t d) = c.edge (c.occ t' d') :=
      step2_eq_identU_inj c (hD0.symm.trans (hAD.symm.trans (hAE.trans hE0)))
    rcases c.g1_edge_unique _ _ hin hin' hedge with h | h
    · exact congrArg Sigma.fst h
    · exfalso
      obtain ⟨hne, hown', -⟩ := c.g1_partner _ hin
      have hp1 : (c.partner (c.occ t d)).1 = t' := (congrArg Sigma.fst h).symm
      rw [hp1] at hne hown'
      have e1 : c.central (c.owner t') = t' := hE_cent
      have e2 : c.central (c.owner t) = t := hcent
      have hne' : t' ≠ t := hne
      have hown'' : c.owner t' = c.owner t := hown'
      exact hne' (e1.symm.trans ((congrArg c.central hown'').trans e2))
  subst hEt
  exact congrArg (DecTile.mk _) (step2_eq_cells c _ cD cE cA F hcent hnorm hXA hE_child hF_child)

/-- Step 2 of the blueprint proof of `reconstructed_acyclic_legal_step6_main`:
The parents `E, D` have the same form and agree in their marked first-four
fields through `A`. A counting argument on the occurrences of `t` in their
identities, using $L-Q > 2Q$, implies that `E` also has type `t`. Normal
local cells and the marked copied cells then identify `E = D`.  Here `D = tileDec X` and `E`
are both parents of the central child `A` of `D`; at most `Q` sides of `t` are prints because
the owner form of `t` (the form of the parent `C`) is not large (`hown`, step 5), and `E` is
acyclic because its parent `F` is noncentral. -/
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
    (A : DecTile c) (hXA : IsChildOf c (tileDec X) A)
    (hAtyp : A.typ = c.central (c.form (tileDec X).typ)) (hAleg : headerLegal c A)
    (hown : c.kind (c.owner (tileDec X).typ) ≠ .large)
    (h_other_nc : ∀ Y ∈ T'.tiles, ¬ c.IsCentral (tileDec Y).typ → headerLegal c (tileDec Y))
    (h_other_cyc : ∀ Y ∈ T'.tiles, c.IsCyclic (tileDec Y).typ → headerLegal c (tileDec Y))
    (E F : DecTile c)
    (hE_child : IsChildOf c E A)
    (hF_child : IsChildOf c F E)
    (hE_legal : headerLegal c E)
    (hF_legal : headerLegal c F)
    (hE_cent : c.IsCentral E.typ)
    (hF_nc : ¬ c.IsCentral F.typ)
    (hE_form : c.form E.typ = c.form (tileDec X).typ) :
    E = tileDec X := by
  have _ := hH; have _ := hT; have _ := hL; have _ := hrec; have _ := hT'; have _ := hex
  have _ := hcyc; have _ := hAleg; have _ := h_other_nc; have _ := h_other_cyc
  have _ := hE_legal; have _ := hF_legal
  exact step2_eq_core c (tileDec X) E A F hcent (hN X hX).1 (hN X hX).2.1 hXA hAtyp hown hE_child
    hF_child hE_cent hF_nc hE_form

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
    (A : DecTile c) (hXA : IsChildOf c (tileDec X) A)
    (hAtyp : A.typ = c.central (c.form (tileDec X).typ)) (hAleg : headerLegal c A)
    (hown : c.kind (c.owner (tileDec X).typ) ≠ .large)
    (h_other_nc : ∀ Y ∈ T'.tiles, ¬ c.IsCentral (tileDec Y).typ → headerLegal c (tileDec Y))
    (h_other_cyc : ∀ Y ∈ T'.tiles, c.IsCyclic (tileDec Y).typ → headerLegal c (tileDec Y)) :
    headerLegal c (tileDec X) := by
  obtain ⟨E, F, hE_child, hF_child, hE_legal, hF_legal, hE_cent, hF_nc, hE_form⟩ :=
    reconstructed_acyclic_legal_step6_main_step1_chain c hH T hT hL part T' hrec hT' hN hex
      X hX hcent hcyc A hXA hAtyp hAleg hown h_other_nc h_other_cyc
  have hE_eq_D := reconstructed_acyclic_legal_step6_main_step2_eq c hH T hT hL part T' hrec hT'
    hN hex X hX hcent hcyc A hXA hAtyp hAleg hown h_other_nc h_other_cyc E F hE_child hF_child
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
  obtain ⟨A, hXA, hAtyp, hAleg⟩ := reconstructed_acyclic_legal_step4_parent c T hL T' hex X hX
  have hown := reconstructed_acyclic_legal_step5_parent_noncentral c hcent hcyc
  have h_other_nc : ∀ Y ∈ T'.tiles, ¬ c.IsCentral (tileDec Y).typ → headerLegal c (tileDec Y) :=
    fun Y hY hnc => reconstructed_acyclic_legal_step2_noncentral c hH T hT hL part T' hrec hT'
      hN hex Y hY hnc hctx
  have h_other_cyc : ∀ Y ∈ T'.tiles, c.IsCyclic (tileDec Y).typ → headerLegal c (tileDec Y) :=
    fun Y hY hcyc' => reconstructed_acyclic_legal_step3_cyclic c hH T hT hL part T' hrec hT'
      hN hex Y hY hcyc' hctx
  exact reconstructed_acyclic_legal_step6_main c hH T hT hL part T' hrec hT' hN hex X hX hcent
    hcyc A hXA hAtyp hAleg hown h_other_nc h_other_cyc

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
  intro T
  have Hcov : support (eraseSet c T.tiles) = Set.univ := by
    rw [← T.cover]
    ext x
    simp only [support, eraseSet, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨A, hA, rfl⟩, hx⟩
      use A, hA
      exact hx
    · rintro ⟨A, hA, hx⟩
      use erase c A
      refine ⟨⟨A, hA, rfl⟩, hx⟩
  have Hdisj : DisjointInteriors (eraseSet c T.tiles) := by
    intros A hA B hB hNeq
    simp only [eraseSet, Set.mem_image] at hA hB
    rcases hA with ⟨A', hA', rfl⟩
    rcases hB with ⟨B', hB', rfl⟩
    have hNeq' : A' ≠ B' := by
      intro h
      subst h
      contradiction
    have H := T.disjoint hA' hB' hNeq'
    exact H
  use {
    tiles := eraseSet c T.tiles,
    cover := Hcov,
    disjoint := Hdisj
  }

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
  intro T' T T₀' T₀ h1 h2 h3
  rw [Substitution.IsComposition]
  rw [h1, h2]
  unfold IsExactComposition at h3
  unfold IsExactCompositionWith at h3
  rcases h3 with ⟨blk, hblk, hT⟩
  rw [hT]
  unfold Substitution.decompose
  unfold eraseSet
  rw [Set.biUnion_image]
  rw [Set.image_iUnion]
  rw [Set.biUnion_eq_iUnion]
  congr 1
  ext X Z
  have hX := hblk X
  rcases hX with ⟨hblkX, hXv⟩
  unfold IsExactBlockOfWith at hblkX
  rcases hblkX with ⟨hblkX_form, hblkX_child⟩
  unfold Substitution.decomposeTile
  unfold erase
  simp only [translateSet]
  rw [c.rule_eq]
  rw [ColouredBlock.tiles]
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · intro h
    rcases h with ⟨Z1, hZ1, hZ2⟩
    rcases hZ1 with ⟨Z2, hZ2_1, hZ2_2⟩
    use (blk X).placed Z2
    constructor
    · use Z2
      constructor
      · rw [← hblkX_form]
        exact hZ2_1
      · rfl
    · rw [← hZ2_2] at hZ2
      unfold ColouredBlock.placed
      unfold ColouredBlock.tileOf
      simp only [PlacedTile.translate, vadd_eq_add] at hZ2
      rw [← hXv] at hZ2
      exact hZ2
  · intro h
    rcases h with ⟨Z1, hZ1, hZ2⟩
    rcases hZ1 with ⟨Z2, hZ2_1, hZ2_2⟩
    use { form := c.form Z2, anchor := c.anchor Z2 }
    constructor
    · use Z2
      constructor
      · rw [hblkX_form]
        exact hZ2_1
      · rfl
    · rw [hZ2_2] at hZ2
      unfold ColouredBlock.placed at hZ2
      unfold ColouredBlock.tileOf at hZ2
      simp only [PlacedTile.translate, vadd_eq_add]
      rw [hXv] at hZ2
      exact hZ2

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
  have _ := hH
  exact Set.toFinite _

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
