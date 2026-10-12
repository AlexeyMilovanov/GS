import Tilings.Basic

/-!
# The finite geometric macrocertificate (`def:certificate`)

This file states, as a Lean structure, the finite data and the properties
(G1)–(G7) of `def:certificate` (blueprint chapter "grouping"), in the form
used by the composition chapter (`composition.tex`), including the review
additions of 12 October 2026:

* (G3) one global positive orientation per unoriented line direction, used
  for ranks and port numbers;
* (G4) every side of a genuine path other than its initial port is an inner
  side; all path sides are marked; the terminal print is exempt from
  path-disjointness in both of its owners;
* (G7) the marking discipline.

The structure is split in two layers.

* `MacroData` contains the raw finite data: the grouped protoset `Q`, the
  scattering `Δ`, the macrotemplate substitution `σ` (written `σ'` in the
  blueprint), the positioned child types, the interface identities, the
  marking, the special sides, the print map, the global orientation, the
  ordered outer-side lists and the paths.  Derived notions (outer / inner /
  boundary sides, ports, ranks, fingerprints, …) are definitions on it.
* `MacroCertificate` extends `MacroData` with the properties (G1)–(G7) as
  fields.

The hereditary-sides hypothesis of the composition chapter is *not* a field
of `MacroCertificate`: (G3) explicitly makes no hereditary-cut assumption,
and the strict-schedule chapter uses the certificate without it.  It is the
separate predicate `MacroData.Hereditary`, bundled as the field `hereditary`
of `HereditaryMacroCertificate`, and it is an explicit hypothesis of every
theorem of the composition chapter.

In accordance with the blueprint acceptance criteria, the certificate does
**not** contain "a legal parent exists", "a proper composition exists" or
"the family is sofic" as a field.
-/

open Set Pointwise

noncomputable section

namespace Tilings

namespace Geometry

/-- The kind of a grouped form (G5): an original form, a small group, or a
large (central) group. -/
inductive FormKind where
  | original
  | small
  | large
  deriving DecidableEq

/-- Cyclic order of three natural numbers (used for indices of listed sides):
`a, b, c` occur in this cyclic order. -/
def CycLt3 (a b c : ℕ) : Prop :=
  (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b)

/-- The raw finite data of a macrocertificate over the original protoset `P`.
No property is imposed here; see `MacroCertificate`. -/
structure MacroData (P : Protoset) where
  /-- The finite protoset of grouped forms (original, small and large forms). -/
  Q : Protoset
  /-- Scattering of a grouped form into a finite patch of original placed
  tiles. -/
  Δ : Q.Form → Patch P
  /-- The uncoloured macrotemplate substitution `σ'` on grouped forms. -/
  σ : Substitution Q
  /-- The kind of each grouped form (G5). -/
  kind : Q.Form → FormKind
  /-- The finite set of positioned child types. -/
  Typ : Type
  [typFintype : Fintype Typ]
  [typDecEq : DecidableEq Typ]
  /-- The own form of a child type. -/
  form : Typ → Q.Form
  /-- The owner template of a child type: the form of its parent. -/
  owner : Typ → Q.Form
  /-- The position (anchor) of the child type inside its owner template
  `σ' (owner t)`, which is anchored at the origin. -/
  anchor : Typ → Pt
  /-- The central child type of each template (G2, G5). -/
  central : Q.Form → Typ
  /-- Finite set of internal template edges (interfaces). -/
  EdgeId : Type
  [edgeFintype : Fintype EdgeId]
  [edgeDecEq : DecidableEq EdgeId]
  /-- The interface identifier of a side occurrence (meaningful on inner
  sides). -/
  edge : (Σ t : Typ, Fin (Q.disk (form t)).n) → EdgeId
  /-- The opposite side occurrence across an inner side (meaningful on inner
  sides). -/
  partner : (Σ t : Typ, Fin (Q.disk (form t)).n) → (Σ t : Typ, Fin (Q.disk (form t)).n)
  /-- The canonically ordered pair of type tags `(s, r)` recorded by an
  interface; the identity datum is the triple `(s, r, e)`. -/
  edgeTypes : EdgeId → Typ × Typ
  /-- Marked listed sides of a form.  Marking depends only on the form. -/
  marked : (α : Q.Form) → Fin (Q.disk α).n → Prop
  /-- Special side occurrences (the unique special side of a small type). -/
  special : (Σ t : Typ, Fin (Q.disk (form t)).n) → Prop
  /-- The print map of a parent form: a marked parent side `d` of `α` has
  its print on the side `print α d` of the central child of `σ' α`. -/
  print : (α : Q.Form) → Fin (Q.disk α).n → Fin (Q.disk (form (central α))).n
  /-- The global positive orientation (G3): for every nonzero direction
  exactly one of `v`, `-v` is positive. -/
  IsPositive : Pt → Prop
  /-- For each parent declared side `d` of `α`, the ordered list of whole
  fine outer sides of `σ' α` contained in the scaled side (G3). -/
  outerList : (α : Q.Form) → Fin (Q.disk α).n → List (Σ t : Typ, Fin (Q.disk (form t)).n)
  /-- The paths `P_i(d)`, `i = 1, …, 5` (here `Fin 5`, zero based), as lists
  of side occurrences of `σ' α` (G4). -/
  path : (α : Q.Form) → Fin (Q.disk α).n → Fin 5 → List (Σ t : Typ, Fin (Q.disk (form t)).n)
  /-- `L = 4N` is the number of marked sides of a large form (G5). -/
  N : ℕ
  /-- `Q` of the blueprint: the maximal number of marked sides of a
  noncentral form (G5). -/
  Qmax : ℕ
  /-- A bound on the length of all outer-side lists (bounds the ranks, so
  that the index alphabet is finite). -/
  rankBound : ℕ

attribute [instance] MacroData.typFintype MacroData.typDecEq MacroData.edgeFintype
  MacroData.edgeDecEq

namespace MacroData

variable {P : Protoset} (D : MacroData P)

/-- The indexed listed sides `S(t)` of a child type: the listed sides of its
own form.  Side identifiers are kept even for collinear consecutive sides. -/
abbrev Side (t : D.Typ) : Type := Fin (D.Q.disk (D.form t)).n

/-- A side occurrence: a child type together with one of its listed sides. -/
abbrev SideOcc : Type := Σ t : D.Typ, D.Side t

/-- The side occurrence `(t, i)`. -/
abbrev occ (t : D.Typ) (i : D.Side t) : D.SideOcc := ⟨t, i⟩

/-- The placed tile of a child type inside its owner template. -/
def childTile (t : D.Typ) : PlacedTile D.Q := ⟨D.form t, D.anchor t⟩

/-- The segment of a side occurrence inside its owner template. -/
def occSide (o : D.SideOcc) : Set Pt := (D.childTile o.1).side o.2

/-- The first endpoint of a side occurrence. -/
def occStart (o : D.SideOcc) : Pt := D.anchor o.1 + (D.Q.disk (D.form o.1)).vertex o.2

/-- The second endpoint of a side occurrence. -/
def occEnd (o : D.SideOcc) : Pt :=
  D.anchor o.1 + (D.Q.disk (D.form o.1)).vertex (finRotate _ o.2)

/-- The midpoint of a side occurrence. -/
def occMid (o : D.SideOcc) : Pt := midpoint ℝ (D.occStart o) (D.occEnd o)

/-- The scaled parent disk `θ · α` covered by the template `σ' α`. -/
def macroRegion (α : D.Q.Form) : Set Pt := D.σ.θ • (D.Q.disk α).carrier

/-- The macroboundary of the template `σ' α`. -/
def macroBoundary (α : D.Q.Form) : Set Pt := frontier (D.macroRegion α)

/-- The scaled parent declared side `θ · d` of `α`. -/
def macroSide (α : D.Q.Form) (d : Fin (D.Q.disk α).n) : Set Pt := D.σ.θ • (D.Q.disk α).side d

/-- An *outer* side: a side occurrence lying on the macroboundary. -/
def IsOuter (o : D.SideOcc) : Prop := D.occSide o ⊆ D.macroBoundary (D.owner o.1)

/-- An *inner* side: a side occurrence that is not outer (it is shared by two
children of the template). -/
def IsInner (o : D.SideOcc) : Prop := ¬ D.IsOuter o

/-- A *boundary* side: an inner side with an endpoint on the macroboundary. -/
def IsBoundary (o : D.SideOcc) : Prop :=
  D.IsInner o ∧ (D.occStart o ∈ D.macroBoundary (D.owner o.1) ∨
    D.occEnd o ∈ D.macroBoundary (D.owner o.1))

open Classical in
/-- The Boolean outer-side predicate `o_t` used by the header kernel. -/
def outerB (t : D.Typ) (i : D.Side t) : Bool := decide (D.IsOuter (D.occ t i))

/-- The marking of a side occurrence is the marking of the side of its form. -/
def IsMarked (o : D.SideOcc) : Prop := D.marked (D.form o.1) o.2

/-- The central side occurrence carrying the print of the parent side `d`. -/
def printOcc (α : D.Q.Form) (d : Fin (D.Q.disk α).n) : D.SideOcc :=
  ⟨D.central α, D.print α d⟩

/-- `o` is the print of the marked parent side `d` of `α`, in either of its
two owners (the central child and the small child sharing it). -/
def IsPrintOf (α : D.Q.Form) (d : Fin (D.Q.disk α).n) (o : D.SideOcc) : Prop :=
  D.marked α d ∧ (o = D.printOcc α d ∨ o = D.partner (D.printOcc α d))

/-- `o` is a print in its owner template. -/
def IsPrint (o : D.SideOcc) : Prop := ∃ d, D.IsPrintOf (D.owner o.1) d o

/-- An *ordinary* side: neither special nor a print. -/
def IsOrdinary (o : D.SideOcc) : Prop := ¬ D.special o ∧ ¬ D.IsPrint o

/-- The paths `P_1(d), …, P_4(d)` of a marked side are *genuine*; the fifth
path and all paths of unmarked sides are singleton ports. -/
def IsGenuinePath (α : D.Q.Form) (d : Fin (D.Q.disk α).n) (i : Fin 5) : Prop :=
  D.marked α d ∧ i.val < 4

/-- `o` lies on a genuine path of its owner template. -/
def OnGenuinePath (o : D.SideOcc) : Prop :=
  ∃ d i, D.IsGenuinePath (D.owner o.1) d i ∧ o ∈ D.path (D.owner o.1) d i

/-- The fixed interior-quantile convention (G3): in a list of length `L`
port `i` (zero based) has the one-based position `⌈(i+1) L / 6⌉`. -/
def portRank (L : ℕ) (i : Fin 5) : ℕ := ((i.val + 1) * L + 5) / 6

/-- Port `i` of the parent side `d` of `α`. -/
def port (α : D.Q.Form) (d : Fin (D.Q.disk α).n) (i : Fin 5) : Option D.SideOcc :=
  (D.outerList α d)[portRank (D.outerList α d).length i - 1]?

/-- The positive alignment rank of a fine outer side in the ordered list of
the parent side `d` (one based). -/
def rankIn (α : D.Q.Form) (d : Fin (D.Q.disk α).n) (o : D.SideOcc) : ℕ :=
  (D.outerList α d).idxOf o + 1

/-- The rank as an element of the bounded rank alphabet. -/
def rankOf (α : D.Q.Form) (d : Fin (D.Q.disk α).n) (o : D.SideOcc) : Fin (D.rankBound + 1) :=
  ⟨min (D.rankIn α d o) D.rankBound, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

open Classical in
/-- The positive one of the two directions of the segment from `u` to `v`. -/
def posDir (u v : Pt) : Pt := if D.IsPositive (v - u) then v - u else u - v

/-- The positive direction of the scaled parent side `d` of `α`. -/
def macroSideDir (α : D.Q.Form) (d : Fin (D.Q.disk α).n) : Pt :=
  D.posDir (D.σ.θ • (D.Q.disk α).vertex d) (D.σ.θ • (D.Q.disk α).vertex (finRotate _ d))

/-- A central child type: the central child of its owner template. -/
def IsCentral (t : D.Typ) : Prop := D.central (D.owner t) = t

/-- A cyclic type: the central child type in the template of its own form. -/
def IsCyclic (t : D.Typ) : Prop := D.central (D.form t) = t

/-- The full inner-side dual graph of the template `σ' α`. -/
def innerGraph (α : D.Q.Form) : SimpleGraph {t : D.Typ // D.owner t = α} :=
  SimpleGraph.fromRel fun s s' =>
    ∃ (i : D.Side s.1) (j : D.Side s'.1),
      D.IsInner (D.occ s.1 i) ∧ D.occSide (D.occ s.1 i) = D.occSide (D.occ s'.1 j)

/-- A type of the boundary belt of `σ' α`: it has a point (possibly only a
vertex) on the macroboundary. -/
def IsBeltType (α : D.Q.Form) (t : D.Typ) : Prop :=
  D.owner t = α ∧ ((D.childTile t).carrier ∩ D.macroBoundary α).Nonempty

/-- The boundary belt graph (G2): vertices are the belt types, edges are the
boundary sides. -/
def beltGraph (α : D.Q.Form) : SimpleGraph {t : D.Typ // D.IsBeltType α t} :=
  SimpleGraph.fromRel fun s s' =>
    ∃ (i : D.Side s.1) (j : D.Side s'.1),
      D.IsBoundary (D.occ s.1 i) ∧ D.occSide (D.occ s.1 i) = D.occSide (D.occ s'.1 j)

/-- The sides contributing to the fingerprint of a type (G6): ordinary inner
sides for original types; ordinary marked inner sides for small types. -/
def IsFingerprintSide (o : D.SideOcc) : Prop :=
  D.IsInner o ∧ D.IsOrdinary o ∧ (D.kind (D.form o.1) = .small → D.IsMarked o)

open Classical in
/-- The base fingerprint (G6): the multiset of type components of the identity
pairs of the fingerprint sides. -/
def baseFingerprint (t : D.Typ) : Multiset D.Typ :=
  ∑ i ∈ Finset.univ.filter (fun i : D.Side t => D.IsFingerprintSide (D.occ t i)),
    ({(D.edgeTypes (D.edge (D.occ t i))).1, (D.edgeTypes (D.edge (D.occ t i))).2} :
      Multiset D.Typ)

/-- The possible fingerprints of a type (G6): for a small type at most two
further arbitrary type components may come from its unique special side. -/
def possibleFingerprints (t : D.Typ) : Set (Multiset D.Typ) :=
  if D.kind (D.form t) = .small then
    {m | ∃ X : Multiset D.Typ, Multiset.card X ≤ 2 ∧ m = D.baseFingerprint t + X}
  else {D.baseFingerprint t}

/-- Hereditary listed sides for the macrotemplate system (`def:hereditary`).
Standing hypothesis of the composition chapter; not part of the
certificate. -/
def Hereditary : Prop := D.σ.HereditarySides

end MacroData

/-- **The finite geometric macrocertificate** (`def:certificate`).

The raw data of `MacroData` together with the properties (G1)–(G7). -/
structure MacroCertificate (P : Protoset) extends MacroData P where
  -- Templates (preamble and G1)
  /-- Each grouped form scatters into original tiles covering exactly its disk. -/
  scatter_support : ∀ α, support (Δ α).tiles = (Q.disk α).carrier
  /-- The template `σ' α` consists exactly of the child types owned by `α`,
  placed at their anchors.  (Covering of the scaled parent disk and disjoint
  interiors are part of `σ : Substitution Q`.) -/
  rule_eq : ∀ α, (σ.rule α).tiles =
    (fun t => (⟨form t, anchor t⟩ : PlacedTile Q)) '' {t | owner t = α}
  /-- Distinct types of one template are distinct placed tiles (types are
  positioned children). -/
  type_injective : ∀ t t', owner t = owner t' → form t = form t' →
    anchor t = anchor t' → t = t'
  /-- (preamble) Every template is a finite side-to-side polygonal template. -/
  template_sts : ∀ α, SideToSideSet (σ.rule α).tiles
  /-- (G1) The full inner-side dual graph of every template is connected. -/
  g1_connected : ∀ α, (toMacroData.innerGraph α).Connected
  /-- (G1) Every template has at least three children. -/
  g1_three_le : ∀ α, 3 ≤ Nat.card {t : Typ // owner t = α}
  /-- (G1) Every type has an inner side. -/
  g1_inner_side : ∀ t, ∃ i, toMacroData.IsInner (toMacroData.occ t i)
  /-- (G1) Across an inner side lies a different type of the same template,
  with the same side segment. -/
  g1_partner : ∀ o : toMacroData.SideOcc, toMacroData.IsInner o →
    (partner o).1 ≠ o.1 ∧ owner (partner o).1 = owner o.1 ∧
      toMacroData.occSide (partner o) = toMacroData.occSide o
  /-- (G1) The partner of the partner is the side itself. -/
  g1_partner_partner : ∀ o : toMacroData.SideOcc, toMacroData.IsInner o →
    partner (partner o) = o
  /-- (G1) The interface identifier is carried by both incident owners. -/
  g1_edge_partner : ∀ o : toMacroData.SideOcc, toMacroData.IsInner o →
    edge (partner o) = edge o
  /-- (G1) Each internal template edge has its own unique interface
  identifier: equal identifiers of inner sides name the same edge.  Since
  types are positioned, the identifier determines the template, the two type
  tags, their side slots and their relative placement. -/
  g1_edge_unique : ∀ o o' : toMacroData.SideOcc, toMacroData.IsInner o →
    toMacroData.IsInner o' → edge o = edge o' → o' = o ∨ o' = partner o
  /-- (G1) The identity datum `(s, r, e)` records the two type tags of the
  edge, in a fixed order common to both owners. -/
  g1_edgeTypes : ∀ o : toMacroData.SideOcc, toMacroData.IsInner o →
    edgeTypes (edge o) = (o.1, (partner o).1) ∨ edgeTypes (edge o) = ((partner o).1, o.1)
  -- (G2) boundary belt
  /-- (G2) The boundary belt graph is connected. -/
  g2_belt_connected : ∀ α, (toMacroData.beltGraph α).Connected
  /-- (G2) Each boundary-belt type has a boundary side. -/
  g2_belt_edge : ∀ t, toMacroData.IsBeltType (owner t) t →
    ∃ i, toMacroData.IsBoundary (toMacroData.occ t i)
  /-- (G2) The central child has neither outer nor boundary sides. -/
  g2_central : ∀ α i, ¬ toMacroData.IsOuter (toMacroData.occ (central α) i) ∧
    ¬ toMacroData.IsBoundary (toMacroData.occ (central α) i)
  -- (G3) ordered outer-side lists, ranks and ports
  /-- (G3) Exactly one of `v`, `-v` is positive, for each nonzero `v`. -/
  g3_pos_iff : ∀ v : Pt, v ≠ 0 → (IsPositive v ↔ ¬ IsPositive (-v))
  /-- (G3) Positivity depends only on the oriented direction. -/
  g3_pos_smul : ∀ (v : Pt) (r : ℝ), 0 < r → IsPositive v → IsPositive (r • v)
  /-- (G3) The list of the parent side `d` consists exactly of the whole fine
  outer sides of `σ' α` contained in the scaled side `θ · d`. -/
  g3_outerList_mem : ∀ α (d : Fin (Q.disk α).n) (o : toMacroData.SideOcc),
    o ∈ outerList α d ↔ (owner o.1 = α ∧ toMacroData.IsOuter o ∧
      toMacroData.occSide o ⊆ toMacroData.macroSide α d)
  /-- (G3) The list has no repetitions. -/
  g3_outerList_nodup : ∀ α d, (outerList α d).Nodup
  /-- (G3) The list is ordered in the *global* positive direction of the
  supporting line, never in the boundary traversal order of the owner. -/
  g3_outerList_sorted : ∀ α d, (outerList α d).Pairwise fun o o' =>
    ∃ r : ℝ, 0 < r ∧ toMacroData.occMid o' - toMacroData.occMid o = r • toMacroData.macroSideDir α d
  /-- (G3) At most two fine outer sides are omitted for crossing the endpoints
  of the scaled side. -/
  g3_crossing_le_two : ∀ α (d : Fin (Q.disk α).n),
    Set.ncard {o : toMacroData.SideOcc | owner o.1 = α ∧ toMacroData.IsOuter o ∧
      OverlapPos (toMacroData.occSide o) (toMacroData.macroSide α d) ∧
      ¬ toMacroData.occSide o ⊆ toMacroData.macroSide α d} ≤ 2
  /-- (G3) Each list is long enough to carry five distinct ports under the
  quantile convention `portRank`. -/
  g3_five_le : ∀ α d, 5 ≤ (outerList α d).length
  /-- (G3) The lists are bounded (finite rank alphabet). -/
  g3_length_le : ∀ α d, (outerList α d).length ≤ rankBound
  -- (G4) prints and routing
  /-- (G4) Marked parent sides have distinct prints. -/
  g4_print_injective : ∀ α (d d' : Fin (Q.disk α).n), marked α d → marked α d' →
    print α d = print α d' → d = d'
  /-- (G4) The prints are in cyclic order. -/
  g4_print_cyclic : ∀ α (a b e : Fin (Q.disk α).n), marked α a → marked α b → marked α e →
    CycLt3 a b e → CycLt3 (print α a) (print α b) (print α e)
  /-- (G4) Prints are inner sides (strictly inside the macrotemplate). -/
  g4_print_inner : ∀ α d, marked α d → toMacroData.IsInner (toMacroData.printOcc α d)
  /-- (G4) The noncentral owner of a print is a small child. -/
  g4_print_small : ∀ α d, marked α d →
    kind (form (partner (toMacroData.printOcc α d)).1) = .small
  /-- (G4/G6, review addition, 12 October 2026) In its small owner the print
  is the unique special side of that owner: the only side of a small type
  whose cells are copied from the parent, so that the fingerprint exception
  of (G6) covers exactly it.  Without this clause a small type could carry a
  nonspecial print with unconstrained copied cells, two distinct noncentral
  parents could agree on everything visible in their common central child,
  and `lem:comp/noncentral-legal` fails (found by codex). -/
  g4_print_special : ∀ α d, marked α d → special (partner (toMacroData.printOcc α d))
  /-- (G4) A genuine path starts at its port. -/
  g4_path_head : ∀ α d i, toMacroData.IsGenuinePath α d i →
    (path α d i).head? = toMacroData.port α d i
  /-- (G4) A genuine path ends at the print, in its small owner. -/
  g4_path_last : ∀ α d i, toMacroData.IsGenuinePath α d i →
    (path α d i).getLast? = some (partner (toMacroData.printOcc α d))
  /-- (G4) Consecutive sides of a path belong to the same tile, or are the two
  occurrences of a common inner side. -/
  g4_path_chain : ∀ α d i (n : ℕ) (o o' : toMacroData.SideOcc),
    (path α d i)[n]? = some o → (path α d i)[n + 1]? = some o' →
      o.1 = o'.1 ∨ (toMacroData.IsInner o ∧ o' = partner o)
  /-- (G4) Paths stay in their template. -/
  g4_path_owner : ∀ α d i (o : toMacroData.SideOcc), o ∈ path α d i → owner o.1 = α
  /-- (G4, review addition) Every side of a genuine path other than its
  initial port is an inner side of the template. -/
  g4_path_inner : ∀ α d i, toMacroData.IsGenuinePath α d i →
    ∀ (n : ℕ) (o : toMacroData.SideOcc), (path α d i)[n + 1]? = some o → toMacroData.IsInner o
  /-- (G4, review addition, 12 October 2026) Paths are sequences of geometric
  sides, so a genuine path contains both occurrences of every inner side it
  uses, the terminal print excepted (the path records it in its small owner
  only).  Without this clause the third cell `A_i(d)` would sit on one
  occurrence of a crossed side and `0` on its partner, and `lift_hierarchy`
  fails (Aristotle, project 7fa31fe7). -/
  g4_path_partner : ∀ α d i, toMacroData.IsGenuinePath α d i →
    ∀ o ∈ path α d i, toMacroData.IsInner o → ¬ toMacroData.IsPrint o →
      partner o ∈ path α d i
  /-- (G4) Every path uses marked sides only. -/
  g4_path_marked : ∀ α d i, toMacroData.IsGenuinePath α d i →
    ∀ o ∈ path α d i, toMacroData.IsMarked o
  /-- (G4) The only central side on a genuine path is its final print (which
  the path records in its small owner). -/
  g4_path_not_central : ∀ α d i, toMacroData.IsGenuinePath α d i →
    ∀ o ∈ path α d i, o.1 ≠ central α
  /-- (G4) The side preceding the print is an ordinary side of the small child
  sharing that print. -/
  g4_path_penultimate : ∀ α d i, toMacroData.IsGenuinePath α d i →
    ∀ o : toMacroData.SideOcc, (path α d i)[(path α d i).length - 2]? = some o →
      o.1 = (partner (toMacroData.printOcc α d)).1 ∧ toMacroData.IsOrdinary o
  /-- (G4) The fifth path and all five paths of unmarked parent sides are
  singleton ports. -/
  g4_path_trivial : ∀ α d i, ¬ toMacroData.IsGenuinePath α d i →
    path α d i = (toMacroData.port α d i).toList
  /-- (G4) A path uses each side occurrence at most once. -/
  g4_path_nodup : ∀ α d i, (path α d i).Nodup
  /-- (G4) Every side occurrence is used by at most one path, except the
  terminal print, in either of its two owners. -/
  g4_path_disjoint : ∀ α (d d' : Fin (Q.disk α).n) (i i' : Fin 5), (d, i) ≠ (d', i') →
    ∀ o, o ∈ path α d i → o ∈ path α d' i' →
      d = d' ∧ (o = toMacroData.printOcc α d ∨ o = partner (toMacroData.printOcc α d))
  -- (G5) central forms and counting
  /-- (G5) The central child belongs to its template. -/
  g5_central_owner : ∀ α, owner (central α) = α
  /-- (G5) There is a unique large child in each template, the central one;
  all other children are original or small. -/
  g5_large_iff : ∀ t, kind (form t) = .large ↔ t = central (owner t)
  /-- (G5) The central-form map fixes every retained large form. -/
  g5_central_fixes_large : ∀ α, kind α = .large → form (central α) = α
  /-- (G5) For a large parent the print map is the identity on marked sides. -/
  g5_print_id_large : ∀ α d, kind α = .large → marked α d → (print α d).val = d.val
  /-- (G5) A large form has `L = 4N` marked sides. -/
  g5_card_marked_large : ∀ α, kind α = .large → Nat.card {d // marked α d} = 4 * N
  /-- (G5) A noncentral form has at most `Q` marked sides. -/
  g5_card_marked_small : ∀ α, kind α ≠ .large → Nat.card {d // marked α d} ≤ Qmax
  /-- (G5) `L > 3Q`. -/
  g5_three_Q_lt : 3 * Qmax < 4 * N
  /-- (G5) Every original type has a marked inner side. -/
  g5_original_marked : ∀ t, kind (form t) = .original →
    ∃ i, toMacroData.IsInner (toMacroData.occ t i) ∧ toMacroData.IsMarked (toMacroData.occ t i)
  -- (G6) fingerprints
  /-- (G6) Special sides belong to small types. -/
  g6_special_small : ∀ o : toMacroData.SideOcc, special o → kind (form o.1) = .small
  /-- (G6) A small type has a unique special side. -/
  g6_special_unique : ∀ t, kind (form t) = .small → ∃! i, special (toMacroData.occ t i)
  /-- (G6) The possible fingerprint multisets of two distinct noncentral
  types are disjoint. -/
  g6_fingerprint : ∀ t t', t ≠ t' → ¬ toMacroData.IsCentral t → ¬ toMacroData.IsCentral t' →
    Disjoint (toMacroData.possibleFingerprints t) (toMacroData.possibleFingerprints t')
  -- (G7) marking discipline
  /-- (G7) Every outer side, every boundary side, every print and every side
  occurring on a genuine path is marked. -/
  g7_marking : ∀ o : toMacroData.SideOcc,
    (toMacroData.IsOuter o ∨ toMacroData.IsBoundary o ∨ toMacroData.IsPrint o ∨
      toMacroData.OnGenuinePath o) → toMacroData.IsMarked o

/-- A macrocertificate together with the hereditary-sides hypothesis of the
composition chapter (`def:hereditary`), as the separate field `hereditary`. -/
structure HereditaryMacroCertificate (P : Protoset) extends MacroCertificate P where
  /-- Hereditary listed sides of the macrotemplate system. -/
  hereditary : σ.HereditarySides

end Geometry

end Tilings

end
