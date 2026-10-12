import Tilings.Basic
import Tilings.Control.Certificate

/-!
# The repaired grouping construction (statements only)

Skeleton for the chapter `grouping.tex` of the blueprint: mesh constants
(`def:mesh`), the anchored inside/outside groupings
(`lem:regular-grouping`, `lem:outside-grouping`), disjoint skeletal spokes
(`lem:annular-spokes`), quantitative sector localization
(`lem:quantitative-sector`), the fingerprint criterion (`lem:fingerprint`) and
wide routing after a power (`lem:routing`).

The existence of the macrocertificate (`lem:certificate-exists`) is stated at
the end, against `Tilings.Geometry.MacroCertificate` from
`Tilings/Control/Certificate.lean` (which imports only `Tilings.Basic`).

All theorems are `sorry`.  The two classical polygonal-topology helpers
`polygonalJordanBoundary` and `plAnnulusRouting` are stated separately; they
must be *proved* (or obtained from a proved polygonal topology API), never
assumed.

Planar notation: `Binf r` is the closed sup-norm ball `[-r,r]^2`,
`square c h` the closed axis-parallel square with centre `c` and half side `h`;
Minkowski sums `Q + Binf r` are the square buffers of the blueprint.
-/

open Set Pointwise

noncomputable section

namespace Tilings

namespace Geometry

variable {P : Protoset}

/-! ## Planar notation -/

/-- The point with coordinates `(x, y)`. -/
def mkPt (x y : ℝ) : Pt := !₂[x, y]

/-- The closed sup-norm ball `B∞(r) = [-r, r]²`. -/
def Binf (r : ℝ) : Set Pt := {x | |x 0| ≤ r ∧ |x 1| ≤ r}

/-- The closed axis-parallel square with centre `c` and half side `h`. -/
def square (c : Pt) (h : ℝ) : Set Pt := {x | |x 0 - c 0| ≤ h ∧ |x 1 - c 1| ≤ h}

/-! ## Mesh constants (`def:mesh`) -/

/-- Mesh constants of a finite protoset (`def:mesh`): every form has diameter
at most `D`, area at least `a`, every listed side has length at least `γ`,
and every form has at most `K0` listed sides.  Only finiteness of `P` is used
to obtain them; neither FLC nor the crown-cover lemma is involved. -/
structure MeshConstants (P : Protoset) where
  D : ℝ
  a : ℝ
  γ : ℝ
  K0 : ℕ
  D_pos : 0 < D
  a_pos : 0 < a
  γ_pos : 0 < γ
  diam_le : ∀ p : P.Form, Metric.diam (P.disk p).carrier ≤ D
  area_ge : ∀ p : P.Form, ENNReal.ofReal a ≤ MeasureTheory.volume (P.disk p).carrier
  side_ge : ∀ (p : P.Form) (i : Fin (P.disk p).n),
    γ ≤ dist ((P.disk p).vertex i) ((P.disk p).vertex (finRotate _ i))
  sides_le : ∀ p : P.Form, (P.disk p).n ≤ K0

/-- Mesh constants exist for every finite protoset. -/
theorem MeshConstants.nonempty (P : Protoset) : Nonempty (MeshConstants P) := by
  sorry

/-! ## The finite cellulation view of a patch (`def:mesh`) -/

/-- The original skeleton: the union of all listed sides of tiles of `S`. -/
def skeleton (S : Set (PlacedTile P)) : Set Pt :=
  ⋃ A ∈ S, ⋃ i : Fin (P.disk A.form).n, A.side i

/-- The edges of the cellulation: the listed sides of tiles of `S`. -/
def edges (S : Set (PlacedTile P)) : Set (Set Pt) :=
  {e | ∃ A ∈ S, ∃ i : Fin (P.disk A.form).n, A.side i = e}

/-- The vertices of the cellulation: the listed vertices of tiles of `S`. -/
def vertices (S : Set (PlacedTile P)) : Set Pt := {v | Substitution.IsVertexOf S v}

/-- `e` is one of the listed sides of the placed tile `A`. -/
def HasEdge (A : PlacedTile P) (e : Set Pt) : Prop :=
  ∃ i : Fin (P.disk A.form).n, A.side i = e

/-- Two distinct faces share a complete listed side. -/
def SharesSide (A B : PlacedTile P) : Prop :=
  A ≠ B ∧ ∃ e, HasEdge A e ∧ HasEdge B e

/-- The face-dual graph of `S` (faces adjacent across complete sides) is
connected. -/
def DualConnected (S : Set (PlacedTile P)) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S,
    Relation.ReflTransGen (fun X Y => X ∈ S ∧ Y ∈ S ∧ SharesSide X Y) A B

/-- A group of faces of the cellulation `S`: a finite set of complete
original faces whose union is a polygonal disk, whose listed boundary sides
are complete original sides, which retains every original vertex on its
boundary, and whose face-dual graph is connected.  Being a polygonal disk is
a *field* that must be established through `polygonalJordanBoundary`; it is
never declared for a filled union without proof. -/
structure FaceGroup (S : Set (PlacedTile P)) where
  faces : Set (PlacedTile P)
  faces_sub : faces ⊆ S
  finite : faces.Finite
  disk : PolygonalDisk
  carrier_eq : disk.carrier = support faces
  side_whole : ∀ i : Fin disk.n, ∃ A ∈ faces, HasEdge A (disk.side i)
  vertex_retained : ∀ v, Substitution.IsVertexOf S v → v ∈ frontier disk.carrier → v ∈ disk.vertexSet
  dualConnected : DualConnected faces

namespace FaceGroup

variable {S : Set (PlacedTile P)}

/-- The closed region of a group. -/
def carrier (L : FaceGroup S) : Set Pt := L.disk.carrier

/-- Inside anchoring: every listed boundary side of `L` adjoins on its inside
a face of `L` whose interior meets the interior of `Q`. -/
def InsideAnchored (L : FaceGroup S) (Q : Set Pt) : Prop :=
  ∀ i : Fin L.disk.n, ∃ F ∈ L.faces,
    HasEdge F (L.disk.side i) ∧ (interior F.carrier ∩ interior Q).Nonempty

/-- Outside anchoring: every listed boundary side of `L` adjoins on its
outside a face of `S`, not in `L`, whose interior meets the open exterior of
`K`. -/
def OutsideAnchored (L : FaceGroup S) (K : Set Pt) : Prop :=
  ∀ i : Fin L.disk.n, ∃ F ∈ S, F ∉ L.faces ∧
    HasEdge F (L.disk.side i) ∧ (interior F.carrier ∩ Kᶜ).Nonempty

end FaceGroup

/-! ## Classical polygonal topology helpers -/

/-- **Polygonal Jordan boundary** (classical helper; must be proved, never
assumed).  In a side-to-side cellulation `S`, a finite nonempty union of
complete faces lying in the interior of the covered region, with connected
interior and connected open complement, has a single simple polygonal
boundary consisting of complete original sides; i.e. it is a `FaceGroup`. -/
theorem polygonalJordanBoundary (S : Set (PlacedTile P)) (hdisj : DisjointInteriors S)
    (hsts : SideToSideSet S) (G : Set (PlacedTile P)) (hG : G ⊆ S) (hfin : G.Finite)
    (hne : G.Nonempty) (hcov : support G ⊆ interior (support S))
    (hint : IsConnected (interior (support G))) (hcompl : IsConnected (support G)ᶜ) :
    ∃ L : FaceGroup S, L.faces = G := by
  sorry

/-- A polygonal arc given by its list of `n + 2` breakpoints. -/
structure PolyArc where
  n : ℕ
  pt : Fin (n + 2) → Pt

namespace PolyArc

variable (α : PolyArc)

/-- The `i`-th segment of the arc. -/
def seg (i : Fin (α.n + 1)) : Set Pt := segment ℝ (α.pt i.castSucc) (α.pt i.succ)

/-- The carrier of the arc. -/
def carrier : Set Pt := ⋃ i, α.seg i

/-- Initial point. -/
def start : Pt := α.pt 0

/-- Final point. -/
def stop : Pt := α.pt (Fin.last (α.n + 1))

/-- The arc is simple: distinct breakpoints, and two segments meet only in
shared breakpoints. -/
def IsSimple : Prop :=
  Function.Injective α.pt ∧
    ∀ i j : Fin (α.n + 1), i ≠ j →
      α.seg i ∩ α.seg j ⊆
        ({α.pt i.castSucc, α.pt i.succ} : Set Pt) ∩ {α.pt j.castSucc, α.pt j.succ}

/-- The arc runs in the original skeleton of `S`: each of its segments is a
complete listed side of a tile of `S`. -/
def IsSkeletal (S : Set (PlacedTile P)) : Prop :=
  ∀ i, ∃ A ∈ S, HasEdge A (α.seg i)

end PolyArc

/-- `γ` is a period-one parametrization of the simple closed curve `K`. -/
def IsLoopParam (K : Set Pt) (γ : ℝ → Pt) : Prop :=
  Continuous γ ∧ Function.Periodic γ 1 ∧ InjOn γ (Ico 0 1) ∧ γ '' Ico 0 1 = K

/-- The points `x 0, …, x (k-1)` appear in this cyclic order along the loop
`γ` (in its direction of traversal). -/
def PointsInOrder (γ : ℝ → Pt) {k : ℕ} (x : Fin k → Pt) : Prop :=
  ∃ t : Fin k → ℝ, StrictMono t ∧ (∀ i j, t j < t i + 1) ∧ ∀ i, γ (t i) = x i

/-- Two period-one loops are freely homotopic inside `U`. -/
def LoopsHomotopicIn (U : Set Pt) (γ₀ γ₁ : ℝ → Pt) : Prop :=
  ∃ F : ℝ × ℝ → Pt, Continuous F ∧ (∀ s t, F (s, t + 1) = F (s, t)) ∧
    (∀ t, F (0, t) = γ₀ t) ∧ (∀ t, F (1, t) = γ₁ t) ∧
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, F (s, t) ∈ U

/-- Matching cyclic order on the two boundary curves of an annulus `U`: the
outer points `x` and the inner points `y` appear in the same cyclic order for
compatible (freely homotopic in `U`) orientations of the two curves. -/
def MatchingCyclicOrder (U Kout Kin : Set Pt) {k : ℕ} (x y : Fin k → Pt) : Prop :=
  ∃ γo γi : ℝ → Pt, IsLoopParam Kout γo ∧ IsLoopParam Kin γi ∧
    LoopsHomotopicIn U γo γi ∧ PointsInOrder γo x ∧ PointsInOrder γi y

/-- **PL annulus routing** (classical helper; must be proved, never assumed).
In the polygonal annulus `A \ int C`, distinct outer points and distinct inner
points in matching cyclic order are joined by pairwise disjoint simple
polygonal arcs meeting the boundary only at their endpoints. -/
theorem plAnnulusRouting (A C : PolygonalDisk) (hC : C.carrier ⊆ interior A.carrier)
    {k : ℕ} (x y : Fin k → Pt) (hx : ∀ i, x i ∈ frontier A.carrier)
    (hy : ∀ i, y i ∈ frontier C.carrier) (hxi : Function.Injective x)
    (hyi : Function.Injective y)
    (horder : MatchingCyclicOrder (A.carrier \ interior C.carrier) (frontier A.carrier)
      (frontier C.carrier) x y) :
    ∃ α : Fin k → PolyArc, ∀ i,
      (α i).IsSimple ∧ (α i).start = x i ∧ (α i).stop = y i ∧
      (α i).carrier ⊆ A.carrier \ interior C.carrier ∧
      (α i).carrier \ {x i, y i} ⊆ interior A.carrier \ C.carrier ∧
      ∀ j, j ≠ i → Disjoint (α i).carrier (α j).carrier := by
  sorry

/-! ## Inside- and outside-anchored groupings -/

/-- `lem:regular-grouping`: a finite STS patch of mesh `D` covering `Ω`, and a
square `Q` with `Q + B∞(3D) ⊂ int Ω`.  There is a group `L` of complete faces,
a polygonal disk with connected face-dual graph, with
`Q ⊂ L ⊂ Q + B∞(D)`, inside-anchored at `Q`. -/
theorem regularGrouping (M : MeshConstants P) (S : Patch P) (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h) (hQ : square c h + Binf (3 * M.D) ⊆ interior Ω.carrier) :
    ∃ L : FaceGroup S.tiles, square c h ⊆ L.carrier ∧ L.carrier ⊆ square c h + Binf M.D ∧
      L.InsideAnchored (square c h) := by
  sorry

/-- `lem:outside-grouping`: with `Q₁ + B∞(10D) ⊂ int Ω` and `K₁ = Q₁ + B∞(3D)`
there is a group `H` with `Q₁ + B∞(2D) ⊂ H ⊂ K₁`, outside-anchored at `K₁`,
whose open complement is connected. -/
theorem outsideAnchoredGrouping (M : MeshConstants P) (S : Patch P) (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier) :
    ∃ H : FaceGroup S.tiles, square c h + Binf (2 * M.D) ⊆ H.carrier ∧
      H.carrier ⊆ square c h + Binf (3 * M.D) ∧
      H.OutsideAnchored (square c h + Binf (3 * M.D)) ∧ IsConnected (H.carrier)ᶜ := by
  sorry

/-! ## Spokes and annular groups -/

/-- A system of `4N` skeletal spokes in the annulus `H \ int L` and the `4N`
annular groups obtained by cutting along them (`lem:annular-spokes`).  The
`j`-th group lies between spokes `j` and `j + 1` (cyclically). -/
structure SpokeSystem (S : Set (PlacedTile P)) (L H : FaceGroup S) (N : ℕ) where
  spoke : Fin (4 * N) → PolyArc
  simple : ∀ j, (spoke j).IsSimple
  skeletal : ∀ j, (spoke j).IsSkeletal S
  in_annulus : ∀ j, (spoke j).carrier ⊆ H.carrier \ interior L.carrier
  meets_L : ∀ j, (spoke j).carrier ∩ frontier L.carrier = {(spoke j).start}
  meets_H : ∀ j, (spoke j).carrier ∩ frontier H.carrier = {(spoke j).stop}
  disjoint : ∀ i j, i ≠ j → Disjoint (spoke i).carrier (spoke j).carrier
  order : MatchingCyclicOrder (H.carrier \ interior L.carrier) (frontier H.carrier)
    (frontier L.carrier) (fun j => (spoke j).stop) (fun j => (spoke j).start)
  piece : Fin (4 * N) → FaceGroup S
  piece_partition : ∀ A ∈ S, (A ∈ H.faces ∧ A ∉ L.faces) ↔ ∃! j, A ∈ (piece j).faces
  piece_between : ∀ j,
    (spoke j).carrier ⊆ (piece j).carrier ∧
      (spoke (finRotate (4 * N) j)).carrier ⊆ (piece j).carrier
  contact_connected : ∀ j, IsConnected ((piece j).carrier ∩ L.carrier)
  contact_nondegenerate : ∀ j, ((piece j).carrier ∩ L.carrier).Nontrivial

/-- The full annular grouping around the centre `c`: `Q₀ = square c (NR/2)`,
`Q₁ = square c (NR/2 + R)`, `K₁ = Q₁ + B∞(3D)`, the inside-anchored group `L`,
the outside-anchored group `H`, and a spoke system between them. -/
structure AnnularGrouping (M : MeshConstants P) (S : Set (PlacedTile P)) (c : Pt) (N : ℕ)
    (R : ℝ) where
  L : FaceGroup S
  H : FaceGroup S
  L_lower : square c ((N : ℝ) * R / 2) ⊆ L.carrier
  L_upper : L.carrier ⊆ square c ((N : ℝ) * R / 2) + Binf M.D
  L_anchor : L.InsideAnchored (square c ((N : ℝ) * R / 2))
  H_lower : square c ((N : ℝ) * R / 2 + R) + Binf (2 * M.D) ⊆ H.carrier
  H_upper : H.carrier ⊆ square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D)
  H_anchor : H.OutsideAnchored (square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D))
  spokes : SpokeSystem S L H N

/-- `lem:annular-spokes`: for `N ≥ 2` and `R` large compared with `D`, any
inside-anchored `L` and outside-anchored `H` as above admit `4N` disjoint
simple skeletal spokes in matching cyclic order, cutting the annulus into `4N`
polygonal disks of complete faces with connected duals, each sharing one
connected nondegenerate arc with `∂L`. -/
theorem existsAnnularSpokes (M : MeshConstants P) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (S : Patch P) (Ω : PolygonalDisk), support S.tiles = Ω.carrier →
        SideToSideSet S.tiles → ∀ (c : Pt) (N : ℕ) (R : ℝ), 2 ≤ N → C₀ * M.D ≤ R →
        square c ((N : ℝ) * R / 2 + R) + Binf (10 * M.D) ⊆ interior Ω.carrier →
        ∀ L H : FaceGroup S.tiles,
          square c ((N : ℝ) * R / 2) ⊆ L.carrier →
          L.carrier ⊆ square c ((N : ℝ) * R / 2) + Binf M.D →
          L.InsideAnchored (square c ((N : ℝ) * R / 2)) →
          square c ((N : ℝ) * R / 2 + R) + Binf (2 * M.D) ⊆ H.carrier →
          H.carrier ⊆ square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D) →
          H.OutsideAnchored (square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D)) →
          Nonempty (SpokeSystem S.tiles L H N) := by
  sorry

/-! ## Quantitative sector localization (`lem:quantitative-sector`) -/

/-- The point at arclength parameter `t ∈ [0, 8A)` on the boundary of the
square `[-A, A]²`, starting at the corner `(A, -A)` and running
counterclockwise. -/
def squarePerimeterPoint (A t : ℝ) : Pt :=
  if t ≤ 2 * A then mkPt A (-A + t)
  else if t ≤ 4 * A then mkPt (A - (t - 2 * A)) A
  else if t ≤ 6 * A then mkPt (-A) (A - (t - 4 * A))
  else mkPt (-A + (t - 6 * A)) (-A)

/-- The ideal radial trapezoid `T_j` between the radial segments through the
successive length-`R` positions `v_j, v_{j+1}` of `∂Q₀` (half side
`A = NR/2`), between `∂Q₀` and `∂K₁` (half side `h = A + R + 3D`). -/
def idealTrapezoid (c : Pt) (N : ℕ) (R D : ℝ) (j : ℕ) : Set Pt :=
  {x | ∃ t ∈ Icc ((j : ℝ) * R) (((j : ℝ) + 1) * R),
    ∃ μ ∈ Icc (1 : ℝ) (((N : ℝ) * R / 2 + R + 3 * D) / ((N : ℝ) * R / 2)),
      x = c + μ • squarePerimeterPoint ((N : ℝ) * R / 2) t}

/-- Private outer edges of the `j`-th annular group: its listed sides on `∂H`
whose outside neighbouring original face meets no other annular group. -/
def privateOuterEdges {M : MeshConstants P} {S : Set (PlacedTile P)} {c : Pt} {N : ℕ}
    {R : ℝ} (G : AnnularGrouping M S c N R) (j : Fin (4 * N)) : Set (Set Pt) :=
  {e | (∃ A ∈ (G.spokes.piece j).faces, HasEdge A e) ∧ e ⊆ frontier G.H.carrier ∧
    ∃ F ∈ S, F ∉ G.H.faces ∧ HasEdge F e ∧
      ∀ t, t ≠ j → Disjoint F.carrier (G.spokes.piece t).carrier}

/-- `lem:quantitative-sector`: there are constants `C_sep, C_loc, C_len,
C_err, C`, independent of `N`, of the substitution power and of the patch,
such that for `R ≥ C_sep D` the groupings can be chosen with every annular
group in the `C_loc D`-neighbourhood of its ideal trapezoid, with at least
`⌊R/(C_len D)⌋ - C_err` private outer edges, of diameter at most `C R`, and
with at most `Q(P,R) = K0 ⌈4C²R²/a⌉` listed sides. -/
theorem quantitativeAnnularGrouping (M : MeshConstants P) :
    ∃ Csep Cloc Clen Cerr C : ℝ, 0 < Csep ∧ 0 < Cloc ∧ 0 < Clen ∧ 0 ≤ Cerr ∧ 0 < C ∧
      ∀ (S : Patch P) (Ω : PolygonalDisk), support S.tiles = Ω.carrier →
        SideToSideSet S.tiles → ∀ (c : Pt) (N : ℕ) (R : ℝ), 2 ≤ N → Csep * M.D ≤ R →
        square c ((N : ℝ) * R / 2 + R) + Binf (10 * M.D) ⊆ interior Ω.carrier →
        ∃ G : AnnularGrouping M S.tiles c N R,
          (∀ j : Fin (4 * N), (G.spokes.piece j).carrier ⊆
              Metric.cthickening (Cloc * M.D) (idealTrapezoid c N R M.D (j : ℕ))) ∧
          (∀ j : Fin (4 * N),
              (⌊R / (Clen * M.D)⌋₊ : ℝ) - Cerr ≤ ((privateOuterEdges G j).ncard : ℝ)) ∧
          (∀ j : Fin (4 * N), Metric.diam (G.spokes.piece j).carrier ≤ C * R) ∧
          (∀ j : Fin (4 * N),
              (G.spokes.piece j).disk.n ≤ M.K0 * ⌈4 * C ^ 2 * R ^ 2 / M.a⌉₊) := by
  sorry

/-! ## The fingerprint criterion (`lem:fingerprint`) -/

/-- Kinds of types in a macrotemplate. -/
inductive TypeKind where
  | original
  | small
  | central
  deriving DecidableEq

/-- Abstract fingerprint data of a finite family of templates: type tags, the
template of each tag, its kind, the multiset `ordinary t` of neighbouring
type tags across its ordinary inner sides (for a small type: its ordinary
marked inner sides), and the full inner-side adjacency of the template dual
graphs. -/
structure FingerprintData where
  Tag : Type
  [decEq : DecidableEq Tag]
  Tmpl : Type
  template : Tag → Tmpl
  kind : Tag → TypeKind
  ordinary : Tag → Multiset Tag
  adj : Tag → Tag → Prop

attribute [instance] FingerprintData.decEq

namespace FingerprintData

variable (F : FingerprintData)

/-- The multiset of type components of the ordinary identity pairs of `t`:
each ordinary side towards `v` contributes the two components `t` and `v`. -/
def baseFingerprint (t : F.Tag) : Multiset F.Tag :=
  F.ordinary t + Multiset.replicate (Multiset.card (F.ordinary t)) t

/-- Possible fingerprints: an original type has exactly its base fingerprint;
a small type may add at most two further components from its special side. -/
def possibleFingerprints (t : F.Tag) : Set (Multiset F.Tag) :=
  match F.kind t with
  | .original => {F.baseFingerprint t}
  | .small => {f | ∃ X : Multiset F.Tag, Multiset.card X ≤ 2 ∧ f = F.baseFingerprint t + X}
  | .central => ∅

/-- (G6): possible fingerprints of distinct noncentral types are disjoint. -/
def Separates : Prop :=
  ∀ t u, F.kind t ≠ .central → F.kind u ≠ .central → t ≠ u →
    Disjoint (F.possibleFingerprints t) (F.possibleFingerprints u)

end FingerprintData

/-- `lem:fingerprint`: under (G1) (neighbours in the same template, symmetric
original adjacency counts, connected template dual graphs with at least three
children), with original types having nonempty fingerprints of at most `K0`
sides, small types having at least `K0 + 2` ordinary marked sides, and every
small type having at least three ordinary occurrences of original neighbours
which are not ordinary neighbours of any other small type of its template,
the fingerprints separate types (G6). -/
theorem fingerprintSeparation (F : FingerprintData) (K0 : ℕ)
    (h_tmpl : ∀ t, ∀ v ∈ F.ordinary t, F.template v = F.template t)
    (h_symm : ∀ u v, F.kind u = .original → F.kind v = .original →
      (F.ordinary u).count v = (F.ordinary v).count u)
    (h_adj_symm : ∀ u v, F.adj u v → F.adj v u)
    (h_adj_orig : ∀ u w, F.kind u = .original → (F.adj u w ↔ w ∈ F.ordinary u))
    (h_conn : ∀ t w, F.template t = F.template w → Relation.ReflTransGen F.adj t w)
    (h_three : ∀ t, ∃ a b, a ≠ t ∧ b ≠ t ∧ a ≠ b ∧
      F.template a = F.template t ∧ F.template b = F.template t)
    (h_orig_ne : ∀ u, F.kind u = .original → F.ordinary u ≠ 0)
    (h_orig_le : ∀ u, F.kind u = .original → Multiset.card (F.ordinary u) ≤ K0)
    (h_small_ge : ∀ t, F.kind t = .small → K0 + 2 ≤ Multiset.card (F.ordinary t))
    (h_private : ∀ t u, F.kind t = .small → F.kind u = .small → t ≠ u →
      F.template t = F.template u →
      3 ≤ Multiset.card ((F.ordinary t).filter
        (fun v => F.kind v = .original ∧ v ∉ F.ordinary u))) :
    F.Separates := by
  sorry

/-! ## Grouped families and grouped substitutions -/

/-- A finite grouped family over `P`: grouped forms `P'`, each with a
scattering patch `dissect α` (the map `Δ` of the blueprint) of original tiles
whose support is the grouped carrier.  Each group is STS, has a connected
face-dual graph, has as listed sides complete original sides, and retains
every original vertex on its boundary. -/
structure GroupedFamily (P : Protoset) where
  P' : Protoset
  dissect : P'.Form → Patch P
  support_eq : ∀ α, support (dissect α).tiles = (P'.disk α).carrier
  sts : ∀ α, SideToSideSet (dissect α).tiles
  dualConnected : ∀ α, DualConnected (dissect α).tiles
  side_whole : ∀ α (i : Fin (P'.disk α).n), ∃ A ∈ (dissect α).tiles, HasEdge A ((P'.disk α).side i)
  vertex_retained : ∀ α v, Substitution.IsVertexOf (dissect α).tiles v →
    v ∈ frontier (P'.disk α).carrier → v ∈ (P'.disk α).vertexSet

namespace GroupedFamily

variable (G : GroupedFamily P)

/-- Scattering of a placed grouped tile into its original constituents. -/
def scatterTile (A : PlacedTile G.P') : Set (PlacedTile P) :=
  translateSet A.anchor (G.dissect A.form).tiles

/-- Scattering of a set of placed grouped tiles. -/
def scatter (S : Set (PlacedTile G.P')) : Set (PlacedTile P) := ⋃ A ∈ S, G.scatterTile A

/-- Mixed protoset: grouped forms together with original forms (used for
templates in which only some groups are retained and the others are
scattered). -/
abbrev mixed : Protoset where
  Form := G.P'.Form ⊕ P.Form
  fintype := inferInstance
  decEq := inferInstance
  disk := Sum.elim G.P'.disk P.disk

/-- Scattering of a placed mixed tile. -/
def mixedScatterTile (A : PlacedTile G.mixed) : Set (PlacedTile P) :=
  Sum.elim (fun α => translateSet A.anchor (G.dissect α).tiles)
    (fun p => ({⟨p, A.anchor⟩} : Set (PlacedTile P))) A.form

/-- Scattering of a set of placed mixed tiles. -/
def mixedScatter (S : Set (PlacedTile G.mixed)) : Set (PlacedTile P) :=
  ⋃ A ∈ S, G.mixedScatterTile A

end GroupedFamily

/-- A grouped substitution for `τ^k`: a grouped family with a substitution
`σ` on grouped forms, of expansion `θ^k`, with `Δ σ α = τ^k Δ α`. -/
structure GroupedSubstitution (τ : Substitution P) where
  G : GroupedFamily P
  k : ℕ
  k_pos : 0 < k
  σ : Substitution G.P'
  θ_eq : σ.θ = τ.θ ^ k
  compat : ∀ α, G.scatter (σ.rule α).tiles = τ.decomposeIter k (G.dissect α).tiles

/-! ## Templates and routing data (`lem:routing`) -/

/-- A finite side-to-side template: a patch of children covering a region. -/
structure Template (Q : Protoset) where
  children : Patch Q
  region : Set Pt
  support_eq : support children.tiles = region
  sts : SideToSideSet children.tiles

namespace Template

variable {Q : Protoset} (T : Template Q)

/-- Inner side: a complete side of two distinct children. -/
def IsInner (e : Set Pt) : Prop :=
  ∃ A ∈ T.children.tiles, ∃ B ∈ T.children.tiles, A ≠ B ∧ HasEdge A e ∧ HasEdge B e

/-- Outer side: a side of a child contained in the boundary of the region. -/
def IsOuter (e : Set Pt) : Prop :=
  e ∈ edges T.children.tiles ∧ e ⊆ frontier T.region

end Template

/-- `f` preserves cyclic order on `s` up to a rotation of the target and up
to a global reversal of orientation (polygonal disks carry no orientation in
`Basic.lean`). -/
def CyclicOrderPreservingOn {n m : ℕ} (s : Finset (Fin n)) (f : Fin n → Fin m) : Prop :=
  ∃ r : ℕ, StrictMonoOn (fun a : Fin n => ((f a : ℕ) + r) % m) (s : Set (Fin n)) ∨
    StrictAntiOn (fun a : Fin n => ((f a : ℕ) + r) % m) (s : Set (Fin n))

/-- Routing data (G4) for one template `T` of a parent disk `par` scaled by
`s`, with central child `central` and marked parent sides `marked`.  For a
marked side `a` the paths `i = 0,…,3` run from port `i` to the print
`central.side (printIdx a)`.  Paths are lists of sides; `pathTiles` lists the
crossed children (`k`-th tile contains sides `k` and `k+1`). -/
structure RoutingData {Q : Protoset} (T : Template Q) (par : PolygonalDisk) (s : ℝ)
    (central : PlacedTile Q) (marked : Finset (Fin par.n)) where
  marking : Set (Set Pt)
  port : Fin par.n → Fin 5 → Set Pt
  printIdx : Fin par.n → Fin (Q.disk central.form).n
  pathSides : Fin par.n → Fin 4 → List (Set Pt)
  pathTiles : Fin par.n → Fin 4 → List (PlacedTile Q)
  central_mem : central ∈ T.children.tiles
  port_outer : ∀ a r, T.IsOuter (port a r) ∧ port a r ⊆ s • par.side a
  port_injective : ∀ a, Function.Injective (port a)
  print_inner : ∀ a ∈ marked, T.IsInner (central.side (printIdx a))
  print_injOn : Set.InjOn printIdx (marked : Set (Fin par.n))
  print_cyclic : CyclicOrderPreservingOn marked printIdx
  path_head : ∀ a ∈ marked, ∀ i : Fin 4, (pathSides a i).head? = some (port a i.castSucc)
  path_last : ∀ a ∈ marked, ∀ i : Fin 4,
    (pathSides a i).getLast? = some (central.side (printIdx a))
  path_length : ∀ a ∈ marked, ∀ i : Fin 4, (pathTiles a i).length + 1 = (pathSides a i).length
  path_step : ∀ a ∈ marked, ∀ i : Fin 4, ∀ (k : ℕ) (X : PlacedTile Q) (e e' : Set Pt),
    (pathTiles a i)[k]? = some X → (pathSides a i)[k]? = some e →
    (pathSides a i)[k + 1]? = some e' →
    X ∈ T.children.tiles ∧ HasEdge X e ∧ HasEdge X e'
  path_cross : ∀ a ∈ marked, ∀ i : Fin 4, ∀ (k : ℕ) (X Y : PlacedTile Q),
    (pathTiles a i)[k]? = some X → (pathTiles a i)[k + 1]? = some Y → X ≠ Y
  /-- the side preceding the print is a side of the small child sharing it -/
  path_last_tile : ∀ a ∈ marked, ∀ i : Fin 4, ∀ X, (pathTiles a i).getLast? = some X →
    X ≠ central
  /-- every side of a genuine path other than its initial port is inner -/
  path_inner : ∀ a ∈ marked, ∀ i : Fin 4, ∀ e ∈ (pathSides a i).tail, T.IsInner e
  path_marked : ∀ a ∈ marked, ∀ i : Fin 4, ∀ e ∈ pathSides a i, e ∈ marking
  /-- the only central side on a genuine path is its final print -/
  path_central : ∀ a ∈ marked, ∀ i : Fin 4, ∀ e ∈ (pathSides a i).dropLast, ¬ HasEdge central e
  /-- every nonterminal side occurrence is used at most once -/
  path_nodup : ∀ a ∈ marked, ∀ i : Fin 4, ((pathSides a i).dropLast).Nodup
  path_disjoint : ∀ a ∈ marked, ∀ b ∈ marked, ∀ i j : Fin 4, (a, i) ≠ (b, j) →
    List.Disjoint (pathSides a i).dropLast (pathSides b j).dropLast
  /-- the fifth port and all ports of unmarked sides are singleton paths,
  disjoint from the genuine paths -/
  singleton_disjoint : ∀ (a : Fin par.n) (r : Fin 5), (a ∉ marked ∨ r = 4) →
    ∀ b ∈ marked, ∀ i : Fin 4, port a r ∉ pathSides b i

/-- Input of the wide-routing lemma: a grouped substitution, the central-form
map `c`, the marked sides of each grouped form, and for each power `l` the
retained `σ^l`-templates (central child and its annular small neighbours
retained, all other groups scattered), together with the properties the
grouping construction guarantees: uniform normalized clearance of the central
child, at least four private outer edges of every small neighbour, and an
injective cyclically ordered choice of print slots on distinct small
neighbours. -/
structure RoutingSetup (τ : Substitution P) where
  GS : GroupedSubstitution τ
  c : GS.G.P'.Form → GS.G.P'.Form
  markedSides : ∀ α : GS.G.P'.Form, Finset (Fin (GS.G.P'.disk α).n)
  retained : ℕ → GS.G.P'.Form → Template GS.G.mixed
  central : ℕ → GS.G.P'.Form → PlacedTile GS.G.mixed
  region_eq : ∀ l α, (retained l α).region = (τ.θ ^ (GS.k * l)) • (GS.G.P'.disk α).carrier
  scatter_eq : ∀ l α, GS.G.mixedScatter (retained l α).children.tiles =
    τ.decomposeIter (GS.k * l) (GS.G.dissect α).tiles
  central_mem : ∀ l α, central l α ∈ (retained l α).children.tiles
  central_form : ∀ l α, (central l α).form = Sum.inl (c^[l] α)
  others : ∀ l α, ∀ X ∈ (retained l α).children.tiles, X ≠ central l α →
    (∃ p, X.form = Sum.inr p) ∨ SharesSide X (central l α)
  clearance : ∃ ρ : ℝ, 0 < ρ ∧ ∀ l α, ∀ x ∈ (central l α).carrier,
    ρ * τ.θ ^ (GS.k * l) ≤ Metric.infDist x (frontier (retained l α).region)
  small_private : ∀ l α, ∀ X ∈ (retained l α).children.tiles, X ≠ central l α →
    SharesSide X (central l α) →
    4 ≤ {e | HasEdge X e ∧ ∃ Y ∈ (retained l α).children.tiles, (∃ p, Y.form = Sum.inr p) ∧
      HasEdge Y e ∧ ∀ Z ∈ (retained l α).children.tiles, Z ≠ X →
        (∃ β, Z.form = Sum.inl β) → Disjoint Y.carrier Z.carrier}.ncard
  print_slots : ∀ l α, ∃ (f : Fin (GS.G.P'.disk α).n → Fin (GS.G.mixed.disk (central l α).form).n)
    (g : Fin (GS.G.P'.disk α).n → PlacedTile GS.G.mixed),
    Set.InjOn f (markedSides α : Set _) ∧ Set.InjOn g (markedSides α : Set _) ∧
    CyclicOrderPreservingOn (markedSides α) f ∧
    ∀ a ∈ markedSides α, g a ∈ (retained l α).children.tiles ∧ g a ≠ central l α ∧
      HasEdge (g a) ((central l α).side (f a))

/-- `lem:routing`: there are arbitrarily large powers `l` with `c^[2l] = c^[l]`
for which every retained `σ^l`-template carries routing data (G4), including
the inner-side clause. -/
theorem existsRoutingAfterPower (τ : Substitution P) (hτ : τ.STS) (M : MeshConstants P)
    (Rs : RoutingSetup τ) :
    ∀ n₀ : ℕ, ∃ l ≥ n₀, Rs.c^[2 * l] = Rs.c^[l] ∧
      ∀ α, Nonempty (RoutingData (Rs.retained l α) (Rs.GS.G.P'.disk α)
        (τ.θ ^ (Rs.GS.k * l)) (Rs.central l α) (Rs.markedSides α)) := by
  sorry

/-! ## Existence of the macrocertificate (`lem:certificate-exists`) -/

/-- `lem:certificate-exists`: for every STS polygonal substitution `τ` there
are a finite grouped family `P'` (the forms `C.Q`), a scattering map
`Δ = C.Δ`, a power `m > 0` and a grouped substitution `σ' = C.σ` of
expansion `θ^m` with `Δ σ' α = τ^m Δ α` for all `α`, together with the
macrocertificate properties (G1)–(G7) (the fields of `MacroCertificate`). -/
theorem existsMacroCertificate (τ : Substitution P) (h : τ.STS) :
    ∃ (C : MacroCertificate P) (m : ℕ), 0 < m ∧ C.σ.θ = τ.θ ^ m ∧
      ∀ α, (⋃ A ∈ (C.σ.rule α).tiles, translateSet A.anchor (C.Δ A.form).tiles) =
        τ.decomposeIter m (C.Δ α).tiles := by
  sorry

end Geometry

end Tilings

end
