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
  rw [← Finset.mem_coe, P.E_A_eq]
  have h_req : f ∈ required_list A := by
    rwa [← P.required_eq]
  have h_depth : f.depth ≤ (Fintype.card S.ι - 1) + 1 :=
    (requiredSet_finite A).2 f (mem_required_list A f |>.mp h_req)
  have h_p : P.p = Fintype.card S.ι - 1 := P.p_eq
  have h_k : P.p + P.H_site + 3 ≤ P.k := P.k_lower
  have h1 : f.depth < P.k := by omega
  have h_sub : f.carrier ⊆ P.component A := P.required_inside A f hf
  have h_nonempty : f.carrier.Nonempty := by
    obtain ⟨i, f', hc, _⟩ := f.realization
    dsimp [PrimitiveFacet.carrier]
    rw [hc]
    have h_cell_ne : f'.val.carrier.Nonempty :=
      f'.val.flat.relint_nonempty.mono intrinsicInterior_subset
    exact h_cell_ne.image _ |>.image _ |>.image _
  exact ⟨h1, h_nonempty.mono (Set.subset_inter Set.Subset.rfl h_sub)⟩

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
  intro a a' h
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · have ho := P.sites_order ι b a a' hlt
    rw [h] at ho
    simp at ho
  · exact heq
  · have ho := P.sites_order ι b a' a hgt
    rw [h.symm] at ho
    simp at ho

end Params

/-- Step 1 of the V4 proof of `params_exist` (V4 §2.1 (P2)):
"The pair is unordered: ι is side-independent. There are finitely many
primitive incidences." Take one representative of each positioned incidence. -/
private theorem params_exist_step1_transversal (S : SubstSystem d) :
    ∃ I : Finset (PrimitiveIncidence S), ∀ ι : PrimitiveIncidence S,
      ∃! η : {η // η ∈ I}, SameIncidence ι η.val := by
  classical
  let R : Setoid (PrimitiveIncidence S) :=
    ⟨SameIncidence, ⟨fun _ => ⟨rfl, rfl⟩,
      fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩⟩
  letI := primitiveIncidence_finite S
  let I := (Set.finite_range (@Quotient.out _ R)).toFinset
  refine ⟨I, fun ι => ?_⟩
  let q : Quotient R := Quotient.mk R ι
  have hq : q.out ∈ I := by
    change q.out ∈ (Set.finite_range (@Quotient.out _ R)).toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨q, rfl⟩
  refine ⟨⟨q.out, hq⟩, ?_, ?_⟩
  · exact R.symm (Quotient.mk_out ι)
  · rintro ⟨η, hη⟩ hιη
    have hη' : η ∈ Set.range (@Quotient.out _ R) := by
      simpa only [I, Set.Finite.mem_toFinset] using hη
    obtain ⟨r, rfl⟩ := hη'
    apply Subtype.ext
    have hqr : q = r := (Quotient.sound hιη).trans r.out_eq
    exact congrArg Quotient.out hqr.symm

omit [Fact (2 ≤ d)] in
/-- Step 2 of the V4 proof of `params_exist` (V4 §2.1 (P2)):
"the boundary complex of a polyhedral manifold cell has full flags".
A cell contained in another cell's relative boundary has strictly smaller dimension. -/
private theorem params_exist_step2_boundary_dimension (e f : Cell d)
    (hfe : f.carrier ⊆ relfrontier e.carrier) : f.dim < e.dim := by
  have hsub : f.carrier ⊆ e.carrier :=
    hfe.trans (intrinsicFrontier_subset e.flat.compact.isClosed)
  have hspan := affineSpan_mono ℝ hsub
  have hdir := AffineSubspace.direction_le hspan
  have hdim : f.dim ≤ e.dim := by
    rw [← f.flat.dimension, ← e.flat.dimension]
    exact Submodule.finrank_mono hdir
  by_contra hnot
  have heq : f.dim = e.dim := by omega
  have hspaneq : affineSpan ℝ f.carrier = affineSpan ℝ e.carrier := by
    apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le _ _ hspan
    · apply Submodule.eq_of_le_of_finrank_eq hdir
      exact f.flat.dimension.trans (heq.trans e.flat.dimension.symm)
    · exact f.flat.connected.nonempty.mono (subset_affineSpan ℝ _)
  have hrel : relint f.carrier ⊆ relint e.carrier := by
    unfold relint intrinsicInterior
    rw [hspaneq]
    exact image_mono (interior_mono (preimage_mono hsub))
  obtain ⟨x, hx⟩ := f.flat.relint_nonempty
  have hxb := hfe (intrinsicInterior_subset hx)
  change x ∈ intrinsicFrontier ℝ e.carrier at hxb
  rw [← closure_diff_intrinsicInterior] at hxb
  exact hxb.2 (hrel hx)

omit [Fact (2 ≤ d)] in
/-- Step 2 of the V4 proof of `params_exist` (V4 §2.1 (P2)):
"the boundary complex of a polyhedral manifold cell has full flags".
The complement of a smaller affine subspace is dense in the cell's affine span. -/
private theorem params_exist_step2_avoid_affine_subspace (A B : AffineSubspace ℝ (E d))
    (hA : (A : Set (E d)).Nonempty)
    (hdim : Module.finrank ℝ B.direction < Module.finrank ℝ A.direction) :
    Dense {x : A | (x : E d) ∉ B} := by
  letI : Nonempty A := hA.to_subtype
  let C := B.comap A.subtype
  change Dense (C : Set A)ᶜ
  apply interior_eq_empty_iff_dense_compl.mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have htop : affineSpan ℝ (interior (C : Set A)) = ⊤ :=
    isOpen_interior.affineSpan_eq_top ⟨x, hx⟩
  have hC : C = ⊤ := top_unique (htop ▸ affineSpan_le.mpr interior_subset)
  have hAB : A ≤ B := by
    intro y hy
    have hh : (⟨y, hy⟩ : A) ∈ C := by rw [hC]; trivial
    exact hh
  exact (not_lt_of_ge (Submodule.finrank_mono (AffineSubspace.direction_le hAB))) hdim

omit [Fact (2 ≤ d)] in
/-- Step 2 of the V4 proof of `params_exist` (V4 §2.1 (P2)):
"the boundary complex of a polyhedral manifold cell has full flags".
Two points can be joined by two segments avoiding a finite family of cells
whose dimensions are at least two below the ambient affine dimension. -/
private theorem params_exist_step2_avoid_cells (A : AffineSubspace ℝ (E d))
    (L : Finset (Cell d))
    (hL : ∀ e ∈ L, e.dim + 1 < Module.finrank ℝ A.direction)
    (a b : E d) (haA : a ∈ A) (hbA : b ∈ A)
    (ha : ∀ e ∈ L, a ∉ e.carrier) (hb : ∀ e ∈ L, b ∉ e.carrier) :
    ∃ J : Set (E d), IsPreconnected J ∧ a ∈ J ∧ b ∈ J ∧ J ⊆ A ∧
      ∀ e ∈ L, Disjoint J e.carrier := by
  letI : Nonempty A := ⟨⟨a, haA⟩⟩
  letI : CompleteSpace A := A.closed_of_finiteDimensional.completeSpace_coe
  have hspan (e : Cell d) (he : e ∈ L) (x : E d) :
      Dense {z : A | (z : E d) ∉ affineSpan ℝ (insert x e.carrier)} := by
    apply params_exist_step2_avoid_affine_subspace A _ ⟨a, haA⟩
    have hh := finrank_vectorSpan_insert_le_set ℝ e.carrier x
    have hed : Module.finrank ℝ (vectorSpan ℝ e.carrier) = e.dim := by
      rw [← direction_affineSpan]
      exact e.flat.dimension
    rw [direction_affineSpan]
    rw [hed] at hh
    exact hh.trans_lt (hL e he)
  have hsegment (e : Cell d) {x z : E d} (hx : x ∉ e.carrier)
      (hz : z ∉ affineSpan ℝ (insert x e.carrier)) :
      Disjoint (segment ℝ x z) e.carrier := by
    apply Set.disjoint_left.mpr
    intro q hq hqe
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    have hr0 : r ≠ 0 := by
      intro hr0
      subst r
      exact hx (by simpa using hqe)
    have hxA : x ∈ affineSpan ℝ (insert x e.carrier) := mem_affineSpan ℝ (mem_insert x _)
    have hqA : AffineMap.lineMap x z r ∈ affineSpan ℝ (insert x e.carrier) :=
      mem_affineSpan ℝ (mem_insert_of_mem _ hqe)
    have hzA := AffineMap.lineMap_mem (r⁻¹) hxA hqA
    rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ hr0, AffineMap.lineMap_apply_one] at hzA
    exact hz hzA
  have hopen (x : E d) (e : Cell d) :
      IsOpen {z : A | (z : E d) ∉ affineSpan ℝ (insert x e.carrier)} :=
    (affineSpan ℝ (insert x e.carrier)).closed_of_finiteDimensional.isOpen_compl.preimage
      continuous_subtype_val
  have hdense (x : E d) : Dense (⋂ e ∈ L,
      {z : A | (z : E d) ∉ affineSpan ℝ (insert x e.carrier)}) := by
    apply dense_biInter_of_isOpen (fun e _ => hopen x e) L.finite_toSet.countable
    intro e he
    exact hspan e he x
  obtain ⟨z, hz⟩ := ((hdense a).inter_of_isOpen_left (hdense b)
    (isOpen_biInter_finset (fun e _ => hopen a e))).nonempty
  refine ⟨segment ℝ a z.val ∪ segment ℝ b z.val,
    IsPreconnected.union' ⟨z.val, right_mem_segment ℝ _ _, right_mem_segment ℝ _ _⟩
      (convex_segment (𝕜 := ℝ) a z.val).isPreconnected
      (convex_segment (𝕜 := ℝ) b z.val).isPreconnected,
    Or.inl (left_mem_segment ℝ _ _), Or.inr (left_mem_segment ℝ _ _),
    union_subset (A.convex.segment_subset haA z.property)
      (A.convex.segment_subset hbA z.property), ?_⟩
  intro e he
  exact disjoint_union_left.mpr
    ⟨hsegment e (ha e he) (Set.mem_iInter₂.mp hz.1 e he),
      hsegment e (hb e he) (Set.mem_iInter₂.mp hz.2 e he)⟩

omit [Fact (2 ≤ d)] in
/-- Step 2 of the V4 proof of `params_exist` (V4 §2.1 (P2)):
"the boundary complex of a polyhedral manifold cell has full flags".
The listed cells covering the relative boundary include a cell of codimension
one: otherwise an interior point could be joined to an exterior point while
avoiding the entire boundary. -/
private theorem params_exist_step2_boundary_subcell (P : PolyManifoldDomain d) (K : CellComplex P)
    (e : Cell d) (he : e ∈ K.cells) (hpos : 0 < e.dim) :
    ∃ f ∈ K.cells, f.dim + 1 = e.dim ∧ f.carrier ⊆ e.carrier := by
  classical
  obtain ⟨L, hLK, hcover⟩ := K.boundary_union e he
  have hfront (f : Cell d) (hf : f ∈ L) : f.carrier ⊆ relfrontier e.carrier := by
    rw [hcover]
    exact subset_iUnion₂_of_subset f hf Subset.rfl
  have hsub (f : Cell d) (hf : f ∈ L) : f.carrier ⊆ e.carrier :=
    (hfront f hf).trans (intrinsicFrontier_subset e.flat.compact.isClosed)
  by_contra hnot
  have hdim (f : Cell d) (hf : f ∈ L) : f.dim + 1 < e.dim := by
    have hlt := params_exist_step2_boundary_dimension e f (hfront f hf)
    have hne : f.dim + 1 ≠ e.dim := fun h => hnot ⟨f, hLK hf, h, hsub f hf⟩
    omega
  let A := affineSpan ℝ e.carrier
  obtain ⟨a, ha, _⟩ := mem_intrinsicInterior.mp e.flat.relint_nonempty.choose_spec
  letI : Nonempty A := ⟨a⟩
  have hdimA : Module.finrank ℝ A.direction = e.dim := e.flat.dimension
  letI : Nontrivial A.direction := Module.nontrivial_of_finrank_pos (hdimA.symm ▸ hpos)
  letI : NoncompactSpace A :=
    (AffineIsometryEquiv.vaddConst ℝ a).toHomeomorph.isClosedEmbedding.noncompactSpace
  let T : Set A := Subtype.val ⁻¹' e.carrier
  have hTclosed : IsClosed T := e.flat.compact.isClosed.preimage continuous_subtype_val
  have hTcompact : IsCompact T :=
    A.closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isCompact_preimage e.flat.compact
  obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem T).mp hTcompact.ne_univ
  have haL (f : Cell d) (hf : f ∈ L) : (a : E d) ∉ f.carrier := by
    intro haf
    have hh := hfront f hf haf
    change (a : E d) ∈ intrinsicFrontier ℝ e.carrier at hh
    rw [← closure_diff_intrinsicInterior] at hh
    exact hh.2 ⟨a, ha, rfl⟩
  have hbL (f : Cell d) (hf : f ∈ L) : (b : E d) ∉ f.carrier :=
    fun hbf => hb (hsub f hf hbf)
  obtain ⟨J, hJ, haJ, hbJ, hJA, hJL⟩ := params_exist_step2_avoid_cells A L
    (fun f hf => hdimA.symm ▸ hdim f hf) a b a.property b.property haL hbL
  let J' : Set A := Subtype.val ⁻¹' J
  have hJ' : IsPreconnected J' := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have hh : Subtype.val '' J' = J :=
      Set.image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hJA hx⟩, rfl⟩)
    exact hh.symm ▸ hJ
  have hno : ∀ x ∈ J', x ∉ frontier T := by
    intro x hx hxf
    have hh : (x : E d) ∈ relfrontier e.carrier := ⟨x, hxf, rfl⟩
    rw [hcover] at hh
    obtain ⟨f, hf, hxf'⟩ := Set.mem_iUnion₂.mp hh
    exact Set.disjoint_left.mp (hJL f hf) hx hxf'
  have hsplit : J' ⊆ interior T ∪ Tᶜ := by
    intro x hx
    by_cases hxT : x ∈ T
    · left
      by_contra hxi
      exact hno x hx ⟨hTclosed.closure_eq.symm ▸ hxT, hxi⟩
    · exact Or.inr hxT
  obtain ⟨x, _, hxi, hxo⟩ := hJ' (interior T) Tᶜ isOpen_interior hTclosed.isOpen_compl
    hsplit ⟨a, haJ, ha⟩ ⟨b, hbJ, hb⟩
  exact hxo (interior_subset hxi)

omit [Fact (2 ≤ d)] in
/-- Step 2 of the V4 proof of `params_exist` (V4 §2.1 (P2)):
"the boundary complex of a polyhedral manifold cell has full flags".
Repeatedly descend to a listed boundary cell of codimension one. -/
private theorem params_exist_step2_cell_chain (P : PolyManifoldDomain d) (K : CellComplex P)
    (n : ℕ) (e : Cell d) (he : e ∈ K.cells) (hdim : e.dim = n) :
    ∃ c : Fin (n + 1) → Cell d,
      (∀ j, c j ∈ K.cells) ∧ (∀ j, (c j).dim = j.val) ∧
      (∀ i j, i ≤ j → (c i).carrier ⊆ (c j).carrier) ∧ c (Fin.last n) = e := by
  induction n generalizing e with
  | zero =>
    refine ⟨fun _ => e, fun _ => he, ?_, fun _ _ _ => Subset.rfl, rfl⟩
    intro j
    simpa using hdim
  | succ n ih =>
    obtain ⟨f, hf, hfdim, hfe⟩ := params_exist_step2_boundary_subcell P K e he (by omega)
    obtain ⟨c, hc, hcdim, hnest, htop⟩ := ih f hf (by omega)
    let c' : Fin (n + 1 + 1) → Cell d := Fin.lastCases e c
    refine ⟨c', ?_, ?_, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa [c'] using he
      · simpa [c'] using hc i
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa [c'] using hdim
      · simpa [c'] using hcdim i
    · intro i j hij
      revert hij
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · refine Fin.lastCases ?_ (fun j' => ?_) j
        · intro _
          exact Subset.rfl
        · intro hij
          have := j'.isLt
          simp only [Fin.le_iff_val_le_val, Fin.val_last, Fin.val_castSucc] at hij
          omega
      · refine Fin.lastCases ?_ (fun j' => ?_) j
        · intro _
          simpa [c'] using ((hnest i' (Fin.last n) (Fin.le_last i')).trans (htop ▸ hfe))
        · intro hij
          simpa [c'] using hnest i' j' (by simpa using hij)
    · simp [c']

/-- Step 2 of the V4 proof of `params_exist` (V4 §2.1 (P2)):
"Such a flag exists (the boundary complex of a polyhedral manifold cell
has full flags)." The prescribed listed facet is the top of the flag. -/
private theorem params_exist_step2_full_flag (A : S.ι) (f : FacetName S A) :
    ∃ F : FacetFlag S A, (F.cell facetIndex).val = f.val := by
  have hd : 2 ≤ d := Fact.out
  obtain ⟨c, hc, hdim, hnest, htop⟩ := params_exist_step2_cell_chain (S.proto A) (S.cx A) (d - 1)
    f.val (Finset.mem_filter.mp f.property).1 (Finset.mem_filter.mp f.property).2
  let F : FacetFlag S A := {
    cell := fun j => ⟨c ⟨j.val, by omega⟩, hc _⟩
    dimension := fun j => hdim _
    nested := fun i j hij => hnest _ _ hij }
  refine ⟨F, ?_⟩
  change c ⟨d - 1, _⟩ = f.val
  exact htop

/-- Step 3 of the V4 proof of `params_exist` (V4 §2.1 (P2)):
"an orientation of h". A nondegenerate real interval has the expected
relative interior. -/
private theorem params_exist_step3_interval_relint (a b : ℝ) (hab : a < b) :
    intrinsicInterior ℝ (Icc a b) = Ioo a b := by
  have hspan : affineSpan ℝ (Icc a b) = ⊤ :=
    (convex_Icc a b).interior_nonempty_iff_affineSpan_eq_top.mp
      (by rw [interior_Icc]; exact nonempty_Ioo.mpr hab)
  rw [intrinsicInterior, hspan]
  change (Homeomorph.Set.univ ℝ) ''
    interior ((Homeomorph.Set.univ ℝ) ⁻¹' Icc a b) = Ioo a b
  rw [(Homeomorph.Set.univ ℝ).image_interior]
  simp

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `params_exist` (V4 §2.1 (P2)):
"the initial vertex of h". The relative boundary of a nondegenerate
closed segment consists exactly of its endpoints. -/
private theorem params_exist_step3_segment_boundary (p q : E d) (hpq : p ≠ q) :
    relfrontier (segment ℝ p q) = {p, q} := by
  let L := ‖q - p‖
  have hL : 0 < L := norm_pos_iff.mpr (sub_ne_zero.mpr hpq.symm)
  let u := L⁻¹ • (q - p)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    exact inv_mul_cancel₀ hL.ne'
  let φ : ℝ →ᵃⁱ[ℝ] E d := {
    toAffineMap := {
      toFun := fun t => t • u + p
      linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight u
      map_vadd' := by
        intro t s
        change (s + t) • u + p = s • u + (t • u + p)
        rw [add_smul, add_assoc] }
    norm_map := by
      intro t
      change ‖t • u‖ = ‖t‖
      rw [norm_smul, hu, mul_one] }
  have hφ0 : φ 0 = p := by change (0 : ℝ) • u + p = p; simp
  have hφL : φ L = q := by
    change L • (L⁻¹ • (q - p)) + p = q
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul, sub_add_cancel]
  have hseg : segment ℝ p q = φ '' Icc 0 L := by
    simpa only [AffineIsometry.coe_toAffineMap, hφ0, hφL, segment_eq_Icc hL.le] using
      (image_segment ℝ φ.toAffineMap 0 L).symm
  have hrel : relint (segment ℝ p q) = φ '' Ioo 0 L := by
    rw [hseg, relint, φ.image_intrinsicInterior, params_exist_step3_interval_relint 0 L hL]
  have hclosed : IsClosed (segment ℝ p q) := by
    rw [hseg]
    exact (isCompact_Icc.image φ.continuous).isClosed
  rw [relfrontier, ← closure_diff_intrinsicInterior, hclosed.closure_eq]
  change segment ℝ p q \ relint (segment ℝ p q) = _
  rw [hrel, hseg, ← Set.image_diff φ.injective]
  have hd : Icc (0 : ℝ) L \ Ioo 0 L = {0, L} := by
    ext x
    simp only [mem_diff, mem_Icc, mem_Ioo, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hn⟩
      by_cases h : x = 0
      · exact Or.inl h
      · exact Or.inr (by push_neg at hn; have := hn (lt_of_le_of_ne hx.1 (Ne.symm h)); linarith)
    · rintro (rfl | rfl)
      · exact ⟨⟨le_rfl, hL.le⟩, by simp⟩
      · exact ⟨⟨hL.le, le_rfl⟩, by simp⟩
  rw [hd, Set.image_pair, hφ0, hφL]

/-- Step 3 of the V4 proof of `params_exist` (V4 §2.1 (P2)):
"an orientation of h" and "translation by the initial vertex of h".
Both endpoints of a listed closed edge are listed vertices. -/
private theorem params_exist_step3_listed_endpoints (A : S.ι)
    (e : {e // e ∈ (S.cx A).edges}) (a b : E d) (hab : a ≠ b)
    (he : e.val.carrier = segment ℝ a b) :
    (∃ v ∈ (S.cx A).vertices, v.carrier = {a}) ∧
      (∃ v ∈ (S.cx A).vertices, v.carrier = {b}) := by
  classical
  have hfront : relfrontier e.val.carrier = {a, b} := by
    rw [he, params_exist_step3_segment_boundary a b hab]
  obtain ⟨cs, hcs, hcover⟩ := (S.cx A).boundary_union e.val
    (Finset.mem_filter.mp e.property).1
  have hvertex (p : E d) (hp : p ∈ ({a, b} : Set (E d))) :
      ∃ v ∈ (S.cx A).vertices, v.carrier = {p} := by
    have hp' : p ∈ ⋃ c ∈ cs, c.carrier := by rwa [← hcover, hfront]
    obtain ⟨c, hc, hpc⟩ := Set.mem_iUnion₂.mp hp'
    have hsub : c.carrier ⊆ {a, b} := by
      intro x hx
      rw [← hfront, hcover]
      exact Set.mem_iUnion₂.mpr ⟨c, hc, hx⟩
    have hfinite : c.carrier.Finite := (Set.toFinite {a, b}).subset hsub
    have hsingle : c.carrier.Subsingleton := by
      by_contra h
      exact (c.flat.connected.isPreconnected.infinite_of_nontrivial
        (Set.not_subsingleton_iff.mp h)) hfinite
    have hcp : c.carrier = {p} := Set.Subset.antisymm
      (fun x hx => mem_singleton_iff.mpr (hsingle hx hpc)) (singleton_subset_iff.mpr hpc)
    have hz : c.dim = 0 := by
      rw [← c.flat.dimension, cellDirection, hcp]
      simp [direction_affineSpan]
    exact ⟨c, Finset.mem_filter.mpr ⟨hcs hc, hz⟩, hcp⟩
  exact ⟨hvertex a (by simp), hvertex b (by simp)⟩

/-- Step 4 of the V4 proof of `params_exist` (V4 §2.1 (P2)):
"choose one oriented full flag". Orient its edge and record the actual
local sides of the successive cofaces. -/
private theorem params_exist_step4_oriented_flag (ι : PrimitiveIncidence S) :
    Nonempty (OrientedFullFlag ι) := by
  obtain ⟨F, hF⟩ := params_exist_step2_full_flag _ ι.leftFacet
  let e : {e // e ∈ (S.cx (S.child ι.ty ι.left).ty).edges} :=
    ⟨(F.cell edgeIndex).val,
      Finset.mem_filter.mpr ⟨(F.cell edgeIndex).property, F.dimension edgeIndex⟩⟩
  obtain ⟨⟨a, b⟩, hab, he⟩ := edge_endpoints_exist (⟨_, e⟩ : EdgeName S)
  obtain ⟨ha, hb⟩ := params_exist_step3_listed_endpoints _ e a b hab he
  exact ⟨⟨F, hF, a, b, hab, he, ha, hb, flagSide F, fun _ => rfl⟩⟩

/-- Step 5 of the V4 proof of `params_exist` (V4 §2.1 (P2), 1.4(a)):
"the two children's complexes agree on g". Sibling conformity supplies
the lower cell names, while the top cells are the paired provider facets. -/
private theorem params_exist_step5_paired_flag (ι : PrimitiveIncidence S)
    (F : OrientedFullFlag ι) (b : Bool) :
    ∃ G : FacetFlag S (ι.sideType b), ∀ j,
      placedSet (S.child ι.ty (ι.sideIndex b)).frame (G.cell j).val.carrier =
        placedSet (S.child ι.ty ι.left).frame (F.flag.cell j).val.carrier := by
  classical
  cases b with
  | false => exact ⟨F.flag, fun _ => rfl⟩
  | true =>
    have hinside (A : S.ι) (e : CellName S A) :
        e.val.carrier ⊆ (S.proto A).carrier := by
      intro x hx
      apply (S.proto A).compact.isClosed.frontier_subset
      rw [← (S.cx A).carriers_cover]
      exact Set.mem_iUnion₂.mpr ⟨e.val, e.property, hx⟩
    have hdim (g : Iso d) (K : Set (E d)) :
        Module.finrank ℝ (cellDirection (placedSet g K)) =
          Module.finrank ℝ (cellDirection K) := by
      change Module.finrank ℝ (affineSpan ℝ (g.toAffineEquiv.toAffineMap '' K)).direction = _
      rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
      exact LinearEquiv.finrank_map_eq g.toAffineEquiv.linear (cellDirection K)
    have hmatch (j : FlagIndex d) :
        ∃ g : CellName S (S.child ι.ty ι.right).ty,
          g.val.dim = j.val ∧
          placedSet (S.child ι.ty ι.right).frame g.val.carrier =
            placedSet (S.child ι.ty ι.left).frame (F.flag.cell j).val.carrier := by
      by_cases hj : j.val = d - 1
      · have hj' : j = facetIndex := Subtype.ext hj
        refine ⟨⟨ι.rightFacet.val, (Finset.mem_filter.mp ι.rightFacet.property).1⟩,
          (Finset.mem_filter.mp ι.rightFacet.property).2.trans hj.symm, ?_⟩
        rw [hj', F.top]
        exact ι.paired.symm
      · let e := F.flag.cell j
        let p := (S.child ι.ty ι.left).frame (cellAnchor e.val)
        have hp : cellAnchor e.val ∈ e.val.carrier :=
          intrinsicInterior_subset (cellAnchor_mem e.val)
        have hpl : p ∈ placedSet (S.child ι.ty ι.left).frame
            (S.proto (S.child ι.ty ι.left).ty).carrier :=
          ⟨_, hinside _ e hp, rfl⟩
        have hpf : p ∈ placedSet (S.child ι.ty ι.right).frame ι.rightFacet.val.carrier := by
          rw [← ι.paired, ← F.top]
          exact ⟨_, F.flag.nested j facetIndex (by dsimp [facetIndex]; omega) hp, rfl⟩
        have hpr : p ∈ placedSet (S.child ι.ty ι.right).frame
            (S.proto (S.child ι.ty ι.right).ty).carrier :=
          Set.image_mono (hinside _ ⟨ι.rightFacet.val,
            (Finset.mem_filter.mp ι.rightFacet.property).1⟩) hpf
        obtain ⟨g, hg, hge⟩ := S.sibling_conformity ι.ty ι.left ι.right ι.distinct
          p hpl hpr e.val e.property
          (by simpa [p] using cellAnchor_mem e.val)
          (by have := F.flag.dimension j; change e.val.dim = j.val at this; omega)
        refine ⟨⟨g, hg⟩, ?_, hge.symm⟩
        calc
          g.dim = Module.finrank ℝ (cellDirection g.carrier) := g.flat.dimension.symm
          _ = Module.finrank ℝ
              (cellDirection (placedSet (S.child ι.ty ι.right).frame g.carrier)) :=
            (hdim _ _).symm
          _ = Module.finrank ℝ
              (cellDirection (placedSet (S.child ι.ty ι.left).frame e.val.carrier)) :=
            congrArg (fun K => Module.finrank ℝ (cellDirection K)) hge.symm
          _ = Module.finrank ℝ (cellDirection e.val.carrier) := hdim _ _
          _ = j.val := e.val.flat.dimension.trans (F.flag.dimension j)
    choose cell hcell hplaced using hmatch
    refine ⟨⟨cell, hcell, ?_⟩, hplaced⟩
    intro i j hij x hx
    have himg : (S.child ι.ty ι.right).frame x ∈
        placedSet (S.child ι.ty ι.right).frame (cell j).val.carrier := by
      rw [hplaced j]
      apply Set.image_mono (F.flag.nested i j hij)
      change (S.child ι.ty ι.right).frame x ∈
        placedSet (S.child ι.ty ι.left).frame (F.flag.cell i).val.carrier
      rw [← hplaced i]
      exact ⟨x, hx, rfl⟩
    exact (S.child ι.ty ι.right).frame.injective.mem_set_image.mp himg

omit [Fact (2 ≤ d)] in
/-- Step 6 of the V4 proof of `params_exist` (V4 §2.1 (P3)):
"all in relint h". Relative interiors commute with the invertible affine
changes from native scale to prototype coordinates. -/
private theorem params_exist_step6_relint_image (e : E d ≃ᵃ[ℝ] E d)
    (K : Set (E d)) : relint (e '' K) = e '' relint K := by
  let h := e.toHomeomorphOfFiniteDimensional
  have hspan : h '' (affineSpan ℝ K : Set (E d)) =
      (affineSpan ℝ (e '' K) : Set (E d)) := by
    exact congrArg (fun A : AffineSubspace ℝ (E d) => (A : Set (E d)))
      (AffineSubspace.map_span e.toAffineMap K)
  let f : (affineSpan ℝ K) ≃ₜ (affineSpan ℝ (e '' K)) :=
    (h.image _).trans (Homeomorph.setCongr hspan)
  have hf (x : affineSpan ℝ K) : (f x).val = e x.val := rfl
  have hp : (f ⁻¹' ((↑) ⁻¹' (e '' K) : Set (affineSpan ℝ (e '' K)))) =
      ((↑) ⁻¹' K : Set (affineSpan ℝ K)) := by
    ext x
    change e x.val ∈ e '' K ↔ x.val ∈ K
    exact e.injective.mem_set_image
  have hi := f.preimage_interior ((↑) ⁻¹' (e '' K) : Set (affineSpan ℝ (e '' K)))
  rw [hp] at hi
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hm : f.symm y ∈ interior ((↑) ⁻¹' K : Set (affineSpan ℝ K)) := by
      rw [← hi]
      simpa using hy
    refine ⟨(f.symm y).val, ⟨f.symm y, hm, rfl⟩, ?_⟩
    simpa only [f.apply_symm_apply] using (hf (f.symm y)).symm
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨f w, ?_, hf w⟩
    change w ∈ f ⁻¹' interior ((↑) ⁻¹' (e '' K) : Set (affineSpan ℝ (e '' K)))
    rwa [hi]

omit [Fact (2 ≤ d)] in
/-- Step 6 of the V4 proof of `params_exist` (V4 §2.1 (P3)):
"q₁ < ⋯ < q_N in the orientation of h". Projection onto a nonzero
segment direction distinguishes all points of that segment. -/
private theorem params_exist_step6_projection_injective (p q : E d) (hpq : p ≠ q) :
    Set.InjOn (fun x => inner ℝ (q - p) x) (segment ℝ p q) := by
  intro x hx y hy hxy
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  have hpos : 0 < inner ℝ (q - p) (q - p) :=
    real_inner_self_pos.mpr (sub_ne_zero.mpr hpq.symm)
  have hst : s = t := by
    simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub,
      inner_add_right, inner_smul_right] at hxy
    nlinarith
  rw [hst]

/-- Step 6 of the V4 proof of `params_exist` (V4 §2.1 (P3)):
"choose N of them, q₁ < ⋯ < q_N". Sort a finite set by an injective
real coordinate and retain its first N elements, also allowing N = 0. -/
private theorem params_exist_step6_sort {α : Type*} (Q : Finset α)
    (c : α → ℝ) (hc : Set.InjOn c (Q : Set α)) (N : ℕ) (hN : N ≤ Q.card) :
    ∃ q : Fin N → α, (∀ a, q a ∈ Q) ∧ StrictMono (fun a => c (q a)) := by
  classical
  let R := Q.image c
  have hcard : N ≤ R.card := by
    simpa only [R, Finset.card_image_of_injOn hc] using hN
  let f := R.orderEmbOfCardLe hcard
  have hmem (a : Fin N) : ∃ x ∈ Q, c x = f a :=
    Finset.mem_image.mp (R.orderEmbOfCardLe_mem hcard a)
  choose q hq heq using hmem
  refine ⟨q, hq, ?_⟩
  intro a b hab
  change c (q a) < c (q b)
  rw [heq a, heq b]
  exact f.strictMono hab

/-- Step 6 of the V4 proof of `params_exist` (V4 1.23(a), §2.1 (P3)):
"there is r(ι,s) such that h carries at least N sites". Pull back a
finite witness set from native scale and sort it in the common orientation. -/
private theorem params_exist_step6_ordered_sites (ι : PrimitiveIncidence S)
    (F : OrientedFullFlag ι) (b : Bool) (G : FacetFlag S (ι.sideType b))
    (hG : ∀ j,
      placedSet (S.child ι.ty (ι.sideIndex b)).frame (G.cell j).val.carrier =
        placedSet (S.child ι.ty ι.left).frame (F.flag.cell j).val.carrier)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (r : ℕ) (q : Fin N → E d),
      (∀ a, IsSite (ι.sideType b) G r ((S.σ ^ r) (q a))) ∧
      (∀ a, q a ∈ relint (G.cell edgeIndex).val.carrier) ∧
      ∀ a a', a < a' →
        inner ℝ ((S.child ι.ty ι.left).rotation F.direction)
          ((S.child ι.ty (ι.sideIndex b)).frame (q a') -
            (S.child ι.ty (ι.sideIndex b)).frame (q a)) > 0 := by
  classical
  obtain ⟨r, hr⟩ := sites_exist (ι.sideType b) G N hN
  obtain ⟨Q, hQcard, hQ⟩ := hr r le_rfl
  let Q₀ := Q.image (S.σ ^ r).symm
  have hQ₀card : N ≤ Q₀.card := by
    simpa only [Q₀, Finset.card_image_of_injective Q (S.σ ^ r).symm.injective] using hQcard
  have hvalid (x : E d) (hx : x ∈ Q₀) : IsSite (ι.sideType b) G r ((S.σ ^ r) x) := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using hQ y hy
  have hrelint (x : E d) (hx : x ∈ Q₀) : x ∈ relint (G.cell edgeIndex).val.carrier := by
    have hh := (hvalid x hx).1
    change (S.σ ^ r) x ∈ relint ((S.σ ^ r).toAffineEquiv ''
      (G.cell edgeIndex).val.carrier) at hh
    rw [params_exist_step6_relint_image] at hh
    exact (S.σ ^ r).injective.mem_set_image.mp hh
  let g := (S.child ι.ty (ι.sideIndex b)).frame
  let l := (S.child ι.ty ι.left).frame
  let v := (S.child ι.ty ι.left).rotation F.direction
  have hv : v = l F.terminal - l F.initial := by
    change (S.child ι.ty ι.left).rotation (F.terminal - F.initial) =
      ((S.child ι.ty ι.left).rotation F.terminal + (S.child ι.ty ι.left).offset) -
        ((S.child ι.ty ι.left).rotation F.initial + (S.child ι.ty ι.left).offset)
    rw [map_sub]
    abel
  have hseg (x : E d) (hx : x ∈ Q₀) :
      g x ∈ segment ℝ (l F.initial) (l F.terminal) := by
    have hh : g x ∈ placedSet g (G.cell edgeIndex).val.carrier :=
      ⟨x, intrinsicInterior_subset (hrelint x hx), rfl⟩
    rw [hG edgeIndex, F.edge_eq] at hh
    exact (image_segment ℝ l.toAffineEquiv.toAffineMap F.initial F.terminal) ▸ hh
  let c := fun x : E d => inner ℝ v (g x)
  have hc : Set.InjOn c (Q₀ : Set (E d)) := by
    intro x hx y hy hxy
    apply g.injective
    apply params_exist_step6_projection_injective (l F.initial) (l F.terminal)
      (l.injective.ne F.distinct) (hseg x hx) (hseg y hy)
    simpa only [c, hv] using hxy
  obtain ⟨q, hq, hmono⟩ := params_exist_step6_sort Q₀ c hc N hQ₀card
  refine ⟨r, q, (fun a => hvalid _ (hq a)), (fun a => hrelint _ (hq a)), ?_⟩
  intro a a' haa'
  change 0 < inner ℝ v (g (q a') - g (q a))
  rw [inner_sub_right]
  exact sub_pos.mpr (hmono haa')

/-- Step 7 of the V4 proof of `params_exist` (V4 8.3):
"Choose a common k ... further refinement preserves the connections
already obtained by heredity." A finite maximum works even for no prototypes. -/
private theorem params_exist_step7_common_components (S : SubstSystem d) (k₀ : ℕ) :
    ∃ k : ℕ, k₀ ≤ k ∧ ∃ E₀ : S.ι → Set (E d),
      (∀ A, IsSkeletonComponent S A k (E₀ A)) ∧
      (∀ A f, f ∈ required_list A → f.carrier ⊆ E₀ A) := by
  classical
  choose depth hdepth component hcomponent hrequired using
    (fun A : S.ι => required_principal_component A k₀)
  let k := max k₀ (Finset.univ.sup depth)
  have hle (A : S.ι) : depth A ≤ k :=
    (Finset.le_sup (f := depth) (Finset.mem_univ A)).trans (le_max_right _ _)
  choose E₀ hE₀ hsub using
    (fun A : S.ι => principal_component_refines A (depth A) k (hle A)
      (component A) (hcomponent A))
  refine ⟨k, le_max_left _ _, E₀, hE₀, ?_⟩
  intro A f hf
  exact ((principalFacets_spec A (depth A) (component A)
    (hcomponent A)).2.1 f (hrequired A f hf)).trans (hsub A)

/-- Q2, V4 §2.1 (P1)--(P6), V4 8.3: admissible parameters exist.
For a nonempty catalogue the geometric existence results of Part I supply the
choices; for the empty catalogue all prototype-indexed choices are vacuous.
This theorem assumes no honest source and does not assert that the species is nonempty. -/
theorem params_exist (S : SubstSystem d) : Nonempty (Params S) := by
  classical
  obtain ⟨I, hI⟩ := params_exist_step1_transversal S
  let F (ι : {ι // ι ∈ I}) := Classical.choice (params_exist_step4_oriented_flag ι.val)
  choose G hG using (fun (ι : {ι // ι ∈ I}) (b : Bool) =>
    params_exist_step5_paired_flag ι.val (F ι) b)
  obtain ⟨B⟩ := edge_ratio_bounds S
  let M := oppositeRootBound B
  have hM (ι : {ι // ι ∈ I}) : 1 ≤ M := by
    apply oppositeRootBound_pos B
    exact ⟨(S.child ι.val.ty ι.val.left).ty,
      ((F ι).flag.cell edgeIndex).val,
      Finset.mem_filter.mpr
        ⟨((F ι).flag.cell edgeIndex).property, (F ι).flag.dimension edgeIndex⟩⟩
  choose r q hvalid hrelint horder using
    (fun (ι : {ι // ι ∈ I}) (b : Bool) =>
      params_exist_step6_ordered_sites ι.val (F ι) b (G ι b) (hG ι b) M (hM ι))
  let Hsite := 1 + (I.attach.product (Finset.univ : Finset Bool)).sup
    (fun z => r z.1 z.2)
  have hdepth (ι : {ι // ι ∈ I}) (b : Bool) : r ι b < Hsite := by
    have hle : r ι b ≤ (I.attach.product (Finset.univ : Finset Bool)).sup
        (fun z => r z.1 z.2) := Finset.le_sup (f := fun z => r z.1 z.2) (b := (ι, b))
      (Finset.mem_product.mpr ⟨Finset.mem_attach I ι, Finset.mem_univ b⟩)
    exact lt_of_le_of_lt hle (Nat.lt_add_of_pos_left (by omega))
  let p := Fintype.card S.ι - 1
  obtain ⟨k, hk, component, hcomponent, hrequired⟩ :=
    params_exist_step7_common_components S (p + Hsite + 3)
  let E_A (A : S.ι) := (principalFacets_spec A k (component A) (hcomponent A)).1.toFinset
  refine ⟨{
    incidences := I
    incidence_complete := hI
    flag := F
    sideFlag := G
    sideFlag_eq := hG
    edgeBounds := B
    M := M
    M_eq := rfl
    N := M
    N_eq := rfl
    N_pos := ?_
    siteDepth := r
    sites := q
    sites_valid := hvalid
    sites_relint := hrelint
    sites_order := horder
    H_site := Hsite
    H_site_eq := rfl
    siteDepth_lt := hdepth
    L := Hsite + 1
    L_eq := rfl
    p := p
    p_eq := rfl
    required := required_list
    required_eq := fun _ => rfl
    k := k
    k_lower := hk
    component := component
    component_valid := hcomponent
    required_inside := hrequired
    E_A := E_A
    E_A_eq := ?_
    C := k + Hsite + 1
    C_eq := rfl
    w := k
    w_eq := rfl
    H := k
    H_eq := rfl
    K := 3 * k + p + 2
    K_eq := rfl
    K_window := by omega
    K_placeholder := by omega
    K_sites := by omega
    K_address := by omega
    marker := fun A => Classical.choice (markerData_exist A) }⟩
  · rintro ⟨ι, hι⟩
    exact hM ⟨ι, hι⟩
  · intro A
    exact Set.Finite.coe_toFinset _

end Enforce
