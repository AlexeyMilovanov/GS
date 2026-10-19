import Tilings.HeaderKernel
import Tilings.Control.Certificate

/-!
# Typed decorations, the repaired header substitution, origins, legality

Blueprint nodes (chapter `composition.tex`):

* `def:control/typed-decoration` — `Tilings.Planned.typedDecoration`,
  `DecTile`, `IsNormal`, `IsIdentityCorrect`;
* `def:control/header` — `HeaderKernel.makeHeader` (applied as `headerOf`);
* `def:control/substitution` — `Tilings.Planned.headerSubstitution`
  (`IsChildOf`), with the four-case fourth-cell rule and print precedence;
* `def:control/origin` — `Tilings.Planned.copySource`, `HasOrigin`;
* `def:control/legal` — `Tilings.Planned.headerLegal`, `IsNontrivial`,
  `IsProper`.

Cell positions `1, …, 5` of the blueprint are `0, …, 4 : Fin 5` here.
The child relation is defined for an arbitrary boundary-fourth rule
(`IsChildOfWith`), so that the article's old rule (boundary fourth cell =
parent type) could be stated with the same machinery (the regression file that
used it was removed, see `docs/removed-regressions.md`).

This file contains definitions and their basic lemmas.
-/

open Set Pointwise

noncomputable section

namespace Tilings

namespace Planned

open Geometry

variable {P : Protoset}

/-! ## The index alphabet -/

/-- The ordinary (non-header, nonzero) index tags: positive alignment ranks
(bounded), type labels, exact interface identities, and `⊥`. -/
abbrev OrdIndex (c : MacroCertificate P) : Type :=
  Fin (c.rankBound + 1) ⊕ (c.Typ ⊕ (c.EdgeId ⊕ Unit))

/-- The finite tagged index alphabet `U`: zero, ordinary tags, and headers. -/
abbrev U (c : MacroCertificate P) : Type :=
  HeaderKernel.TaggedIndex c.Typ c.Side (OrdIndex c)

/-- The tagged alphabet is equivalent to a sum type. -/
def taggedEquiv (T : Type) (Side : T → Type) (Other : Type) :
    HeaderKernel.TaggedIndex T Side Other ≃ Unit ⊕ (Other ⊕ HeaderKernel.Header T Side) where
  toFun x := match x with
    | .zero => Sum.inl ()
    | .ordinary o => Sum.inr (Sum.inl o)
    | .header h => Sum.inr (Sum.inr h)
  invFun y := match y with
    | Sum.inl _ => .zero
    | Sum.inr (Sum.inl o) => .ordinary o
    | Sum.inr (Sum.inr h) => .header h
  left_inv x := by cases x <;> rfl
  right_inv y := by rcases y with _ | _ | _ <;> rfl

noncomputable instance instFintypeU (c : MacroCertificate P) : Fintype (U c) :=
  Fintype.ofEquiv _ (taggedEquiv c.Typ c.Side (OrdIndex c)).symm

noncomputable instance instDecEqU (c : MacroCertificate P) : DecidableEq (U c) :=
  Classical.decEq _

/-- A positive alignment rank. -/
def rankU (c : MacroCertificate P) (k : Fin (c.rankBound + 1)) : U c :=
  .ordinary (Sum.inl k)

/-- A type label. -/
def typeU (c : MacroCertificate P) (t : c.Typ) : U c :=
  .ordinary (Sum.inr (Sum.inl t))

/-- An exact interface identity `(s, r, e)`, named by its edge `e`. -/
def identU (c : MacroCertificate P) (e : c.EdgeId) : U c :=
  .ordinary (Sum.inr (Sum.inr (Sum.inl e)))

/-- The symbol `⊥`. -/
def botU (c : MacroCertificate P) : U c :=
  .ordinary (Sum.inr (Sum.inr (Sum.inr ())))

/-- A header value. -/
def headerU (c : MacroCertificate P) (h : HeaderKernel.Header c.Typ c.Side) : U c :=
  .header h

/-- `u` is a positive alignment rank. -/
def IsRankU (c : MacroCertificate P) (u : U c) : Prop :=
  ∃ k : Fin (c.rankBound + 1), 0 < k.val ∧ u = rankU c k

/-! ## Decorated tiles (`def:control/typed-decoration`) -/

/-- A decorated tile of type `t`: the type (stored in the centre) and a
five-tuple `c_A(d) ∈ U^5` on every listed side `d ∈ S(t)`. -/
structure DecTile (c : MacroCertificate P) where
  typ : c.Typ
  cell : c.Side typ → Fin 5 → U c

/-- Decorated tiles as a sigma type. -/
def decTileEquiv (c : MacroCertificate P) :
    DecTile c ≃ Σ t : c.Typ, (c.Side t → Fin 5 → U c) where
  toFun A := ⟨A.typ, A.cell⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instFintypeDecTile (c : MacroCertificate P) : Fintype (DecTile c) :=
  Fintype.ofEquiv _ (decTileEquiv c).symm

noncomputable instance instDecEqDecTile (c : MacroCertificate P) : DecidableEq (DecTile c) :=
  Classical.decEq _

/-- **Typed decorations** (`def:control/typed-decoration`): the finite
protoset of decorated tiles; the geometric polygon of a tile of type `t` is
that of `form t`. -/
abbrev typedDecoration (c : MacroCertificate P) : Protoset where
  Form := DecTile c
  disk A := c.Q.disk (c.form A.typ)

/-- The decorated tile of a placed decorated tile. -/
def tileDec {c : MacroCertificate P} (X : PlacedTile (typedDecoration c)) : DecTile c := X.form

/-- The placed `i`-th side of a placed decorated tile. -/
def sideOf (c : MacroCertificate P) (X : PlacedTile (typedDecoration c))
    (i : c.Side (tileDec X).typ) : Set Pt :=
  X.anchor +ᵥ (c.Q.disk (c.form (tileDec X).typ)).side i

/-- Erasure of the colours of a placed decorated tile. -/
def erase (c : MacroCertificate P) (X : PlacedTile (typedDecoration c)) : PlacedTile c.Q :=
  ⟨c.form (tileDec X).typ, X.anchor⟩

/-- Erasure of a set of placed decorated tiles. -/
def eraseSet (c : MacroCertificate P) (S : Set (PlacedTile (typedDecoration c))) :
    Set (PlacedTile c.Q) :=
  erase c '' S

/-! ### Local cells, normality, identity-correctness -/

/-- The *local* cells of a side occurrence: all cells of an unmarked side;
the fifth cell of a special side or of a print; the first and fifth cells of
a marked ordinary side.  (By (G7) an unmarked side is inner, nonprint,
nonboundary and on no path.) -/
def IsLocal (c : MacroCertificate P) (o : c.SideOcc) (k : Fin 5) : Prop :=
  ¬ c.IsMarked o ∨
    (c.IsMarked o ∧ (c.special o ∨ c.IsPrint o) ∧ k = 4) ∨
    (c.IsMarked o ∧ c.IsOrdinary o ∧ (k = 0 ∨ k = 4))

open Classical in
/-- The prescribed first cell of a nonprint side: its interface identity if
it is inner (including special nonprint sides), zero on outer sides. -/
def prescribedFirst (c : MacroCertificate P) (o : c.SideOcc) : U c :=
  if c.IsInner o then identU c (c.edge o) else 0

open Classical in
/-- The type-determined value of a cell, used on local cells: first cell as
`prescribedFirst`; second and third cells zero; fourth cell `⊥` on an inner
nonprint nonboundary side; fifth cell the interface identity on a print and
zero otherwise. -/
def prescribedCell (c : MacroCertificate P) (o : c.SideOcc) (k : Fin 5) : U c :=
  if k = 0 then prescribedFirst c o
  else if k = 3 then
    (if c.IsInner o ∧ ¬ c.IsBoundary o ∧ ¬ c.IsPrint o then botU c else 0)
  else if k = 4 then (if c.IsPrint o then identU c (c.edge o) else 0)
  else 0

/-- **Normality**: every local cell has the value prescribed by the type. -/
def IsNormal (c : MacroCertificate P) (A : DecTile c) : Prop :=
  ∀ (i : c.Side A.typ) (k : Fin 5), IsLocal c (c.occ A.typ i) k →
    A.cell i k = prescribedCell c (c.occ A.typ i) k

/-- **Identity-correctness**: every inner nonprint side carries its identity
in position 1, and every print carries it in position 5. -/
def IsIdentityCorrect (c : MacroCertificate P) (A : DecTile c) : Prop :=
  ∀ i : c.Side A.typ,
    (c.IsInner (c.occ A.typ i) → ¬ c.IsPrint (c.occ A.typ i) →
      A.cell i 0 = identU c (c.edge (c.occ A.typ i))) ∧
    (c.IsPrint (c.occ A.typ i) → A.cell i 4 = identU c (c.edge (c.occ A.typ i)))

/-- A side is *nontrivial* if its fourth and fifth cells are not both zero. -/
def IsNontrivial (c : MacroCertificate P) (A : DecTile c) (i : c.Side A.typ) : Prop :=
  ¬ (A.cell i 3 = 0 ∧ A.cell i 4 = 0)

/-- Every inner side is nontrivial ("active"). -/
def InnerActive (c : MacroCertificate P) (A : DecTile c) : Prop :=
  ∀ i : c.Side A.typ, c.IsInner (c.occ A.typ i) → IsNontrivial c A i

/-! ## The parent header (`def:control/header`) -/

/-- The fourth-index vector of a decorated tile. -/
def fourthVec (c : MacroCertificate P) (A : DecTile c) : c.Side A.typ → U c :=
  fun d => A.cell d 3

/-- The header `H(A) = ⟨t, z_{t,a}⟩` computed from the type and the fourth
vector (kernel `makeHeader`). -/
def headerOf (c : MacroCertificate P) (A : DecTile c) : HeaderKernel.Header c.Typ c.Side :=
  HeaderKernel.makeHeader c.outerB A.typ (fourthVec c A)

/-- The zero mode `z_A(d) = o_t(d) ∧ [A_4(d) = 0]`. -/
def zA (c : MacroCertificate P) (A : DecTile c) (d : c.Side A.typ) : Bool :=
  HeaderKernel.zeroMode c.outerB A.typ (fourthVec c A) d

/-! ## The repaired substitution (`def:control/substitution`) -/

/-- The child clauses of the decorated substitution, for a parent `A` and a
child `B` (of type `B.typ`, owned by `form A.typ`), with an arbitrary rule
`bdry` for the fourth cell of boundary sides.

* print of a marked parent side `d` (both owners; precedence): cells 1–4
  copy `A(d)`, cell 5 is the interface identity;
* nonprint side `b`: prescribed first identity cell, zero second and fifth
  cells, third cell `A_i(d)` on the path `P_i(d)` and zero otherwise, and
  fourth cell
  `0` if `b ⊂ σ'd` is outer and `z_A(d)`, `rank b` if outer and not `z_A(d)`,
  `bdry A` if `b` is boundary, `⊥` on the remaining inner nonprint sides. -/
def IsChildOfWith (c : MacroCertificate P) (bdry : DecTile c → U c) (A B : DecTile c) : Prop :=
  c.owner B.typ = c.form A.typ ∧
  ∀ i : c.Side B.typ,
    (∀ d : c.Side A.typ, c.IsPrintOf (c.form A.typ) d (c.occ B.typ i) →
        (∀ k : Fin 5, k ≠ 4 → B.cell i k = A.cell d k) ∧
        B.cell i 4 = identU c (c.edge (c.occ B.typ i))) ∧
    (¬ c.IsPrint (c.occ B.typ i) →
        B.cell i 0 = prescribedFirst c (c.occ B.typ i) ∧
        B.cell i 1 = 0 ∧
        B.cell i 4 = 0 ∧
        (∀ (d : c.Side A.typ) (j : Fin 5),
          c.occ B.typ i ∈ c.path (c.form A.typ) d j → B.cell i 2 = A.cell d j) ∧
        ((∀ (d : c.Side A.typ) (j : Fin 5), c.occ B.typ i ∉ c.path (c.form A.typ) d j) →
          B.cell i 2 = 0) ∧
        (c.IsOuter (c.occ B.typ i) → ∀ d : c.Side A.typ,
          c.occ B.typ i ∈ c.outerList (c.form A.typ) d →
            B.cell i 3 = if zA c A d = true then 0
              else rankU c (c.rankOf (c.form A.typ) d (c.occ B.typ i))) ∧
        (c.IsBoundary (c.occ B.typ i) → B.cell i 3 = bdry A) ∧
        (c.IsInner (c.occ B.typ i) → ¬ c.IsBoundary (c.occ B.typ i) → B.cell i 3 = botU c))

/-- **The repaired header substitution** (`def:control/substitution`): `B` is
a child of `A` in the repaired decomposition `σ̂ A`; the boundary clause
carries the entire parent header `H(A)`. -/
def headerSubstitution (c : MacroCertificate P) (A B : DecTile c) : Prop :=
  IsChildOfWith c (fun A => headerU c (headerOf c A)) A B

/-- `B` is a child of `A` under the repaired substitution. -/
abbrev IsChildOf (c : MacroCertificate P) (A B : DecTile c) : Prop := headerSubstitution c A B

/-- `B` is the child of type `t` of `A`. -/
def IsChildOfType (c : MacroCertificate P) (A : DecTile c) (t : c.Typ) (B : DecTile c) : Prop :=
  B.typ = t ∧ IsChildOf c A B

/-! ## Copy sources and origins (`def:control/origin`) -/

/-- **Copy sources** (`def:control/origin`): the parent cells copied by the
cell `k` of the child side occurrence `o` under a parent of form `α`.
Copied cells are positions 1–4 on prints (source: the same position of the
printed parent side) and position 3 on nonprint sides assigned to a path
`P_j(d)` (source: position `j` of `d`).  All other cells — the centre type,
the synthesized boundary header and all fixed cells — are origins (empty
source set).  By (G4) the source set has at most one element. -/
def copySource (c : MacroCertificate P) (α : c.Q.Form) (o : c.SideOcc) (k : Fin 5) :
    Set (Fin (c.Q.disk α).n × Fin 5) :=
  {p | (c.IsPrintOf α p.1 o ∧ k ≠ 4 ∧ p.2 = k) ∨
    (¬ c.IsPrint o ∧ k = 2 ∧ o ∈ c.path α p.1 p.2)}

/-- Along an ancestor chain `ch` (with `ch n` a child of `ch (n+1)`), the
cell `(i, k)` of `ch n` reaches an origin by repeatedly following copy
sources. -/
inductive HasOrigin (c : MacroCertificate P) (ch : ℕ → DecTile c) :
    (n : ℕ) → c.Side (ch n).typ → Fin 5 → Prop
  | origin (n : ℕ) (i : c.Side (ch n).typ) (k : Fin 5) :
      copySource c (c.form (ch (n + 1)).typ) (c.occ (ch n).typ i) k = ∅ →
      HasOrigin c ch n i k
  | step (n : ℕ) (i : c.Side (ch n).typ) (k : Fin 5)
      (d : c.Side (ch (n + 1)).typ) (k' : Fin 5) :
      (d, k') ∈ copySource c (c.form (ch (n + 1)).typ) (c.occ (ch n).typ i) k →
      HasOrigin c ch (n + 1) d k' → HasOrigin c ch n i k

/-! ## Legality and properness (`def:control/legal`) -/

/-- Legality with respect to a child relation `R` (`R parent child`): an
infinite ancestor chain in which every copied cell with no origin is zero. -/
def IsLegalWith (c : MacroCertificate P) (R : DecTile c → DecTile c → Prop)
    (A : DecTile c) : Prop :=
  ∃ ch : ℕ → DecTile c, ch 0 = A ∧ (∀ n, R (ch (n + 1)) (ch n)) ∧
    ∀ (n : ℕ) (i : c.Side (ch n).typ) (k : Fin 5),
      (copySource c (c.form (ch (n + 1)).typ) (c.occ (ch n).typ i) k).Nonempty →
      ¬ HasOrigin c ch n i k → (ch n).cell i k = 0

/-- **Legality** (`def:control/legal`) for the repaired substitution. -/
def headerLegal (c : MacroCertificate P) (A : DecTile c) : Prop :=
  IsLegalWith c (IsChildOf c) A

/-- Alias of `headerLegal`. -/
abbrev IsLegal (c : MacroCertificate P) (A : DecTile c) : Prop := headerLegal c A

/-- **Properness** for the flexible rule (`def:control/legal`): every
nontrivial side of a tile has a complete, coincident opposing side of another
tile with the same full five-tuple.  Trivial sides impose nothing (shifted
contacts of trivial outer sides are allowed). -/
def IsProper (c : MacroCertificate P) (T : PlaneTiling (typedDecoration c)) : Prop :=
  ∀ X ∈ T.tiles, ∀ i : c.Side (tileDec X).typ, IsNontrivial c (tileDec X) i →
    ∃ Y ∈ T.tiles, Y ≠ X ∧ ∃ j : c.Side (tileDec Y).typ,
      sideOf c Y j = sideOf c X i ∧ ∀ k : Fin 5, (tileDec Y).cell j k = (tileDec X).cell i k

end Planned

end Tilings

end
