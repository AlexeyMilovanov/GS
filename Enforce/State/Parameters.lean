import Enforce.Source.Routing

/-!
# Parameters for the finite source state

Q1--Q2, V4 §2.1 (P1)--(P6), with the replacements of V4 8.3.
Roles are the existing globally distinct `S.Role`. There are exactly `N = M` sites;
no selected site arms occur. Principal components use the normalized coordinates
of `Source/Routing` (D4).

Cones in every state header are sets of directions at the origin. At a point `v`
of a height-`n` node with frame `Q σⁿ · + t`, first translate the apex to zero and
then apply `(Q σⁿ)⁻¹`. At native height this is the inverse orthogonal tile frame.
In particular positive-height normalization is not restricted to similarities.

DEVIATION: stage 2's `PrimitiveIncidence` has ordered sides. A finite transversal
of equality of the parent type and positioned facet represents the unordered
incidences of (P2). A separate Boolean side selects an actual globally distinct
role. `incidence_complete` requires exactly one representative of every occurrence;
it does not discard either side or identify different parent types.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- Q1, V4 §2.1 (P2): positive dimensions of a full facet flag. -/
abbrev FlagIndex (d : ℕ) := {j : ℕ // 1 ≤ j ∧ j < d}

/-- Q1, V4 §2.1 (P2): consecutive dimensions in a full facet flag. -/
abbrev FlagStep (d : ℕ) := {j : ℕ // 1 ≤ j ∧ j + 1 < d}

/-- Q1, V4 §2.1 (P2): the edge index, valid also when `d = 2`. -/
def edgeIndex : FlagIndex d :=
  ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩

/-- Q1, V4 §2.1 (P2): the top, facet index. -/
def facetIndex : FlagIndex d :=
  ⟨d - 1, by have := (Fact.out : 2 ≤ d); omega,
    by have := (Fact.out : 2 ≤ d); omega⟩

/-- Q1, V4 §2.1 (P2): an interior anchor of a listed cell, for its local side.
Nonemptiness is supplied by the definition of a flat cell. -/
def cellAnchor (e : Cell d) : E d := e.flat.relint_nonempty.choose

omit [Fact (2 ≤ d)] in
/-- Q1, V4 §2.1 (P2): the anchor lies in the relative interior. -/
theorem cellAnchor_mem (e : Cell d) : cellAnchor e ∈ relint e.carrier :=
  e.flat.relint_nonempty.choose_spec

/-- Q1, V4 §2.1 (P2): the side of the next coface along a full flag.
It is its local tangent half-space at a relative-interior point of the lower cell.
Thus the listed cells record the successive sides without an ambient orientation. -/
def flagSide {A : S.ι} (F : FacetFlag S A) (j : FlagStep d) : Set (E d) :=
  tangentCone (F.cell ⟨j.val + 1, by omega, j.property.2⟩).val.carrier
    (cellAnchor (F.cell ⟨j.val, j.property.1, by omega⟩).val)

/-- Q1, V4 §2.1 (P2): the positioned facet of an ordered stage-2 incidence. -/
def PrimitiveIncidence.positioned (ι : PrimitiveIncidence S) : Set (E d) :=
  placedSet (S.child ι.ty ι.left).frame ι.leftFacet.val.carrier

/-- Q1, V4 §2.1 (P2): side-independent equality, retaining the birth-parent type. -/
def SameIncidence (ι η : PrimitiveIncidence S) : Prop :=
  ι.ty = η.ty ∧ ι.positioned = η.positioned

/-- Q1, V4 §2.1 (P2): the actual role selected by a side (`false` is left). -/
def PrimitiveIncidence.sideIndex (ι : PrimitiveIncidence S) (b : Bool) : S.I ι.ty :=
  if b then ι.right else ι.left

/-- Q1, V4 §2.1 (P1)--(P2): a side is an actual globally distinct role. -/
def PrimitiveIncidence.sideRole (ι : PrimitiveIncidence S) (b : Bool) : S.Role :=
  ⟨ι.ty, ι.sideIndex b⟩

/-- Q1, V4 §2.1 (P2): prototype on a selected side of an incidence. -/
def PrimitiveIncidence.sideType (ι : PrimitiveIncidence S) (b : Bool) : S.ι :=
  (S.child ι.ty (ι.sideIndex b)).ty

/-- Q1, V4 §2.1 (P2): provider name on the selected side. -/
def PrimitiveIncidence.sideFacet (ι : PrimitiveIncidence S) (b : Bool) :
    FacetName S (ι.sideType b) := by
  cases b with
  | false => exact ι.leftFacet
  | true => exact ι.rightFacet

/-- Q1, V4 §2.1 (P2): the geometric full flag with an oriented edge.
The successive side choices are the actual local sides `flagSide` of its cofaces.
The initial and terminal points name listed vertices, including flat vertices. -/
structure OrientedFullFlag (ι : PrimitiveIncidence S) where
  /-- Q1, V4 §2.1 (P2): flag in the canonical left prototype. -/
  flag : FacetFlag S (S.child ι.ty ι.left).ty
  /-- Q1, V4 §2.1 (P2): its top cell is the named provider facet. -/
  top : (flag.cell facetIndex).val = ι.leftFacet.val
  /-- Q1, V4 §2.1 (P2): initial endpoint in that prototype. -/
  initial : E d
  /-- Q1, V4 §2.1 (P2): terminal endpoint in that prototype. -/
  terminal : E d
  /-- Q1, V4 §2.1 (P2): a nondegenerate orientation. -/
  distinct : initial ≠ terminal
  /-- Q1, V4 §2.1 (P2): the entire edge is the oriented closed segment. -/
  edge_eq : (flag.cell edgeIndex).val.carrier = segment ℝ initial terminal
  /-- Q1, V4 §2.1 (P2): initial endpoint is a listed vertex. -/
  initial_listed : ∃ v ∈ (S.cx (S.child ι.ty ι.left).ty).vertices,
    v.carrier = {initial}
  /-- Q1, V4 §2.1 (P2): terminal endpoint is a listed vertex. -/
  terminal_listed : ∃ v ∈ (S.cx (S.child ι.ty ι.left).ty).vertices,
    v.carrier = {terminal}
  /-- Q1, V4 §2.1 (P2): explicit successive local side cones. -/
  sides : FlagStep d → Set (E d)
  /-- Q1, V4 §2.1 (P2): side choices are determined by the positioned cofaces. -/
  sides_eq : ∀ j, sides j = flagSide flag j

/-- Q1, V4 §2.1 (P2): direction of the selected orientation, before normalization. -/
def OrientedFullFlag.direction {ι : PrimitiveIncidence S} (F : OrientedFullFlag ι) :
    E d := F.terminal - F.initial

/-- Q10, V4 §2.4 (frame marker): fixed labelled balls pinning a prototype frame. -/
structure MarkerData (S : SubstSystem d) (A : S.ι) where
  /-- Q10, V4 §2.4: `d+1` labelled centres. -/
  centre : Fin (d + 1) → E d
  /-- Q10, V4 §2.4: affine independence pins the full Euclidean isometry. -/
  independent : AffineIndependent ℝ centre
  /-- Q10, V4 §2.4: common radius within this prototype. -/
  radius : ℝ
  /-- Q10, V4 §2.4: positive marker balls. -/
  radius_pos : 0 < radius
  /-- Q10, V4 §2.4: all closed balls lie in the interior. -/
  inside : ∀ a, closedBall (centre a) radius ⊆ interior (S.proto A).carrier
  /-- Q10, V4 §2.4: closed marker balls are pairwise disjoint. -/
  disjoint : Pairwise (fun a b => Disjoint
    (closedBall (centre a) radius) (closedBall (centre b) radius))

/-- Q10, V4 §2.4: markers exist because each prototype has nonempty interior.
This is conditional on an actual prototype and imposes no source nonemptiness. -/
theorem markerData_exist (A : S.ι) : Nonempty (MarkerData S A) := by
  sorry

/-- Q1, V4 §2.1 (P1)--(P6), V4 8.3: data and admissibility of all parameters.
The incidence catalogue is exhaustive even if there is no honest source. For an
empty type catalogue the choices indexed by prototypes are empty functions. -/
structure Params (S : SubstSystem d) where
  /-- Q1, V4 §2.1 (P2): one representative for each unordered primitive incidence. -/
  incidences : Finset (PrimitiveIncidence S)
  /-- Q1, V4 §2.1 (P2): exactly one representative of every ordered occurrence. -/
  incidence_complete : ∀ ι : PrimitiveIncidence S,
    ∃! η : {η // η ∈ incidences}, SameIncidence ι η.val
  /-- Q1, V4 §2.1 (P2): the selected oriented full flags. -/
  flag : ∀ ι : {ι // ι ∈ incidences}, OrientedFullFlag ι.val
  /-- Q1, V4 §2.1 (P2): the same flag named in either child's complex. -/
  sideFlag : ∀ ι : {ι // ι ∈ incidences}, ∀ b : Bool,
    FacetFlag S (ι.val.sideType b)
  /-- Q1, V4 §2.1 (P2): both names have the identical positioned cells. -/
  sideFlag_eq : ∀ ι b j,
    placedSet (S.child ι.val.ty (ι.val.sideIndex b)).frame
        ((sideFlag ι b).cell j).val.carrier =
      placedSet (S.child ι.val.ty ι.val.left).frame
        ((flag ι).flag.cell j).val.carrier
  /-- Q1, V4 §2.1 (P3), V4 1.20: fixed hereditary edge bounds. -/
  edgeBounds : EdgeBounds S
  /-- Q1, V4 §2.1 (P3), V4 1.21: global opposite-root bound. -/
  M : ℕ
  /-- Q1, V4 §2.1 (P3): the exact floor bound. -/
  M_eq : M = oppositeRootBound edgeBounds
  /-- Q1, V4 8.3: the number of sites, with no selected arms. -/
  N : ℕ
  /-- Q1, V4 8.3: the sharpened site count. -/
  N_eq : N = M
  /-- Q1, V4 §2.1 (P3): positivity whenever an incidence needs sites. -/
  N_pos : incidences.Nonempty → 0 < N
  /-- Q1, V4 §2.1 (P3): depth of each separate side's site system. -/
  siteDepth : {ι // ι ∈ incidences} → Bool → ℕ
  /-- Q1, V4 §2.1 (P3): site points in the unexpanded serving prototype. -/
  sites : {ι // ι ∈ incidences} → Bool → Fin N → E d
  /-- Q1, V4 §2.1 (P3): sites really occur in the depth-r recursive trace.
  Applying `σ^r` gives exactly the native-scale sites of V4 1.23. -/
  sites_valid : ∀ ι b a, IsSite (ι.val.sideType b) (sideFlag ι b) (siteDepth ι b)
    ((S.σ ^ siteDepth ι b) (sites ι b a))
  /-- Q1, V4 §2.1 (P3): the original site points lie in the relative-open edge. -/
  sites_relint : ∀ ι b a,
    sites ι b a ∈ relint ((sideFlag ι b).cell edgeIndex).val.carrier
  /-- Q1, V4 §2.1 (P3): strict order in the common oriented positioned edge. -/
  sites_order : ∀ ι b (a a' : Fin N), a < a' →
    inner ℝ ((S.child ι.val.ty ι.val.left).rotation (flag ι).direction)
      ((S.child ι.val.ty (ι.val.sideIndex b)).frame (sites ι b a') -
        (S.child ι.val.ty (ι.val.sideIndex b)).frame (sites ι b a)) > 0
  /-- Q1, V4 §2.1 (P3): one more than the maximum site depth. -/
  H_site : ℕ
  /-- Q1, V4 §2.1 (P3): exact maximum, with empty maximum zero. -/
  H_site_eq : H_site = 1 +
    (incidences.attach.product (Finset.univ : Finset Bool)).sup
      (fun z => siteDepth z.1 z.2)
  /-- Q1, V4 §2.1 (P3): each depth is strictly below `H_site`. -/
  siteDepth_lt : ∀ ι b, siteDepth ι b < H_site
  /-- Q1, V4 §2.1 (P4): residue modulus. -/
  L : ℕ
  /-- Q1, V4 §2.1 (P4): exact residue modulus. -/
  L_eq : L = H_site + 1
  /-- Q1, V4 1.28, §2.1 (P5): maximal placeholder run. -/
  p : ℕ
  /-- Q1, V4 1.28: exact catalogue bound, using natural subtraction. -/
  p_eq : p = Fintype.card S.ι - 1
  /-- Q1, V4 §2.1 (P5): the actual replacement required lists. -/
  required : ∀ A, Finset (PrimitiveFacet S A)
  /-- Q1, V4 8.3: exactly first generation, `F(A)`, and every `iF(A_i)`. -/
  required_eq : ∀ A, required A = required_list A
  /-- Q1, V4 §2.1 (P5): common skeleton and address depth. -/
  k : ℕ
  /-- Q1, V4 §2.1 (P5): required lower bound, retained under V4 8.3. -/
  k_lower : p + H_site + 3 ≤ k
  /-- Q1, V4 §2.1 (P5): chosen connected component in prototype coordinates. -/
  component : S.ι → Set (E d)
  /-- Q1, V4 1.24: an actual connected component of `Sk_k(A)`. -/
  component_valid : ∀ A, IsSkeletonComponent S A k (component A)
  /-- Q1, V4 §2.1 (P5): all required supports lie wholly in that component. -/
  required_inside : ∀ A f, f ∈ required A → f.carrier ⊆ component A
  /-- Q1, V4 §2.1 (P5): finite principal components of primitive facets. -/
  E_A : ∀ A, Finset (PrimitiveFacet S A)
  /-- Q1, V4 1.24: all, and only, primitive facets at depth at most `k-1`
  meeting the chosen connected component are recorded. -/
  E_A_eq : ∀ A, (E_A A : Set (PrimitiveFacet S A)) =
    principalFacets S A k (component A)
  /-- Q1, V4 §2.1 (P6): age cap. -/
  C : ℕ
  /-- Q1, V4 §2.1 (P6): exact cap. -/
  C_eq : C = k + H_site + 1
  /-- Q1, V4 §2.1 (P6): future window. -/
  w : ℕ
  /-- Q1, V4 §2.1 (P6): exact future window. -/
  w_eq : w = k
  /-- Q1, V4 §2.1 (P6): observer floor. -/
  H : ℕ
  /-- Q1, V4 §2.1 (P6): exact observer floor. -/
  H_eq : H = k
  /-- Q1, V4 §2.1 (P6): certificate height. -/
  K : ℕ
  /-- Q1, V4 §2.1 (P6): exact certificate height. -/
  K_eq : K = 3 * k + p + 2
  /-- Q1, V4 §2.1 (P6): observer window fits inside the certificate. -/
  K_window : H + w ≤ K
  /-- Q1, V4 §2.1 (P6): certificates exceed every placeholder run. -/
  K_placeholder : p + 1 < K
  /-- Q1, V4 §2.1 (P6): enough room for site depths. -/
  K_sites : H_site + 1 ≤ K
  /-- Q1, V4 §2.1 (P6): enough room for the full address. -/
  K_address : k ≤ K
  /-- Q10, V4 §2.4: fixed marker balls, chosen once per prototype. -/
  marker : ∀ A, MarkerData S A

namespace Params

variable (P : Params S)

/-- Q1, V4 §2.1 (P2): the finite side-independent incidence alphabet. -/
abbrev Incidence := {ι // ι ∈ P.incidences}

/-- Q1, V4 §2.1 (P2): canonicalization of a stage-2 ordered incidence. -/
def canonical (ι : PrimitiveIncidence S) : P.Incidence :=
  Classical.choose (P.incidence_complete ι)

/-- Q1, V4 §2.1 (P2): canonicalization preserves the positioned provider. -/
theorem canonical_spec (ι : PrimitiveIncidence S) :
    SameIncidence ι (P.canonical ι).val :=
  (Classical.choose_spec (P.incidence_complete ι)).1

/-- Q1, V4 §2.1 (P3)--(P4): site horizon is positive. -/
theorem H_site_pos : 0 < P.H_site := by
  rw [P.H_site_eq]
  omega

/-- Q1, V4 §2.1 (P4): the residue modulus is positive. -/
theorem L_pos : 0 < P.L := by
  rw [P.L_eq]
  omega

/-- Q1, V4 §2.1 (P5): addresses have a first letter. -/
theorem k_pos : 0 < P.k := by
  have := P.k_lower
  omega

/-- Q1, V4 §2.1 (P6): age one is never capped. -/
theorem C_gt_one : 1 < P.C := by
  have := P.k_pos
  rw [P.C_eq]
  omega

/-- Q1, V4 §2.1 (P2): place a canonical incidence's left prototype in a node.
The node is its birth parent; the formula uses its full affine prototype frame. -/
def incidencePlacement (B : FramedNode S) (n : ℕ) (ι : P.Incidence) :
    E d ≃ᵃ[ℝ] E d :=
  (S.child ι.val.ty ι.val.left).frame.toAffineEquiv.trans
    (S.σ.symm.toAffineEquiv.trans (B.prototypeFrame n))

/-- Q1, V4 §2.1 (P3): the site in the common left-prototype coordinates. -/
def canonicalSite (ι : P.Incidence) (b : Bool) (a : Fin P.N) : E d :=
  (S.child ι.val.ty ι.val.left).frame.symm
    ((S.child ι.val.ty (ι.val.sideIndex b)).frame (P.sites ι b a))

/-- Q1/Q8, V4 §2.1 (P5): geometric principal membership in a placed node.
The existential matches actual positioned primitive facets; `E_A` is finite. -/
def InPrincipal (B : FramedNode S) (n : ℕ) (g : Set (E d)) : Prop :=
  ∃ f ∈ P.E_A B.ty, B.prototypeFrame n '' f.carrier = g

/-- Q1, V4 §2.1 (P5): the required list belongs to the selected principal set. -/
theorem required_mem (A : S.ι) (f : PrimitiveFacet S A) (hf : f ∈ P.required A) :
    f ∈ P.E_A A := by
  sorry

/-- Q1, V4 §2.1 (P5): the principal set has the exact depth cap. -/
theorem principal_depth (A : S.ι) (f : PrimitiveFacet S A) (hf : f ∈ P.E_A A) :
    f.depth < P.k := by
  rw [← Finset.mem_coe, P.E_A_eq] at hf
  exact hf.1

/-- Q1, V4 §2.1 (P2): the transversal chooses the unique equivalent incidence. -/
theorem canonical_unique (ι : PrimitiveIncidence S) (η : P.Incidence)
    (hη : SameIncidence ι η.val) : P.canonical ι = η :=
  ((Classical.choose_spec (P.incidence_complete ι)).2 η hη).symm

/-- Q1, V4 §2.1 (P2): canonical representatives are fixed by canonicalization. -/
theorem canonical_idempotent (ι : P.Incidence) : P.canonical ι.val = ι :=
  P.canonical_unique ι.val ι ⟨rfl, rfl⟩

/-- Q1, V4 §2.1 (P3): the N chosen sites are distinct on each separate side.
Their strict oriented order, rather than an arbitrary enumeration, ensures this. -/
theorem sites_injective (ι : P.Incidence) (b : Bool) :
    Function.Injective (P.sites ι b) := by
  sorry

end Params

/-- Q2, V4 §2.1 (P1)--(P6), V4 8.3: admissible parameters exist.
For a nonempty catalogue the geometric existence results of Part I supply the
choices; for the empty catalogue all prototype-indexed choices are vacuous.
This theorem assumes no honest source and does not assert that the species is nonempty. -/
theorem params_exist (S : SubstSystem d) : Nonempty (Params S) := by
  sorry

end Enforce
