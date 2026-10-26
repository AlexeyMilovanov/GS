import Enforce.Source.Sites

/-!
# Internal skeletons, principal components, birth-ascent routing, and Req′

DEVIATION: the standard skeleton and primitive facets in this file are expressed
in the unexpanded prototype `A`. Applying `σ^k` gives precisely the sets in `σ^k A`
of V4 1.24--1.25. This common invertible linear change of coordinates preserves
all inclusions, incidences, connected components, and recorded role words.
-/

open Set

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- P19, V4 1.24, preceding definition: a descendant's full prototype frame
in the unexpanded root, obtained by pulling its native placement back by `σ⁻ʲ`. -/
def prototypeDescendantFrame (A : S.ι) (j : ℕ) (w : S.RoleWord A j) :
    E d ≃ᵃ[ℝ] E d :=
  (S.nativeTile A j w).frame.toAffineEquiv.trans (S.σ ^ j).symm.toAffineEquiv

/-- P19, V4 1.24, preceding definition: a primitive facet with its birth address.
The local carrier has an existential owning side, so the two paired sides represent
one facet. No arbitrary orientation or duplicate side is built into facet identity.
DEVIATION: its root carrier is normalized in the unexpanded prototype, as above. -/
structure PrimitiveFacet (S : SubstSystem d) (A : S.ι) where
  /-- P19, V4 1.24: depth of the birth parent within the root. -/
  depth : ℕ
  /-- P19, V4 1.24: complete role word to that birth parent. -/
  word : S.RoleWord A depth
  /-- P19, V4 1.24: provider carrier in the standard expanded birth-parent prototype. -/
  localCarrier : Set (E d)
  /-- P19, V4 1.24: an actual first-generation internal facet, with an owning cell name. -/
  realization : ∃ (i : S.I (S.nativeTile A depth word).ty)
    (f : FacetName S (S.child (S.nativeTile A depth word).ty i).ty),
    localCarrier = placedSet (S.child (S.nativeTile A depth word).ty i).frame
      f.val.carrier ∧
    relint localCarrier ⊆ interior (S.supertile 1 (S.nativeTile A depth word).ty)

namespace PrimitiveFacet

variable {A : S.ι}

/-- P19, V4 1.24: birth-parent type. -/
def birthType (f : PrimitiveFacet S A) : S.ι := (S.nativeTile A f.depth f.word).ty

/-- P19, V4 1.24: the tree address of the birth parent. -/
def birthAddress (f : PrimitiveFacet S A) : Σ j : ℕ, S.RoleWord A j := ⟨f.depth, f.word⟩

/-- P19, V4 1.24: the birth-parent prototype frame in root coordinates. -/
def birthFrame (f : PrimitiveFacet S A) : E d ≃ᵃ[ℝ] E d :=
  prototypeDescendantFrame A f.depth f.word

/-- P19, V4 1.24: normalized carrier of the primitive facet. -/
def carrier (f : PrimitiveFacet S A) : Set (E d) :=
  f.birthFrame '' (S.σ.symm '' f.localCarrier)

/-- P21, V4 1.25: birth-parent node in the standard height-`k` root.
All routing statements require `f.depth < k`, so this height is positive. -/
def birthNode (f : PrimitiveFacet S A) (k : ℕ) : FramedNode S :=
  S.descendantNode A (k - f.depth) f.depth f.word

/-- P21, V4 1.25: a birth-parent cell in root coordinates. -/
def birthCell (f : PrimitiveFacet S A) (e : Cell d) : Set (E d) :=
  f.birthFrame '' e.carrier

/-- P21, V4 1.25: a cell of an immediate child of the birth parent. -/
def childCell (f : PrimitiveFacet S A) (i : S.I f.birthType) (e : Cell d) : Set (E d) :=
  f.birthFrame '' (S.σ.symm '' placedSet (S.child f.birthType i).frame e.carrier)

/-- P21, V4 1.25: the immediate child's entire support in root coordinates. -/
def childSupport (f : PrimitiveFacet S A) (i : S.I f.birthType) : Set (E d) :=
  f.birthFrame '' (S.σ.symm '' placedSet (S.child f.birthType i).frame
    (S.proto (S.child f.birthType i).ty).carrier)

/-- P21, V4 1.25: listedness in a named child of the birth parent. -/
def ChildLists (f : PrimitiveFacet S A) (i : S.I f.birthType) (q : E d) : Prop :=
  ∃ v ∈ (S.cx (S.child f.birthType i).ty).vertices, q ∈ f.childCell i v

/-- P21, V4 1.25: a vertex of the primitive facet, named in an owning child's complex. -/
def IsVertex (f : PrimitiveFacet S A) (q : E d) : Prop :=
  q ∈ f.carrier ∧ ∃ (i : S.I f.birthType)
    (e : FacetName S (S.child f.birthType i).ty),
      f.localCarrier = placedSet (S.child f.birthType i).frame e.val.carrier ∧
        f.ChildLists i q

/-- P21, V4 1.25: common-listed seed in the complete immediate subdivision. -/
def CommonListed (f : PrimitiveFacet S A) (q : E d) : Prop :=
  ∀ i : S.I f.birthType, q ∈ f.childSupport i → f.ChildLists i q

end PrimitiveFacet

/-- P19, V4 1.24, preceding definition: primitive facets born at depth `j`. -/
def primitiveFacetAtDepth (S : SubstSystem d) (A : S.ι) (j : ℕ) :
    Set (PrimitiveFacet S A) := {f | f.depth = j}

/-- P19, V4 1.24: finitely many primitive facets through any fixed finite depth. -/
theorem primitiveFacets_finite (S : SubstSystem d) (A : S.ι) (k : ℕ) :
    {f : PrimitiveFacet S A | f.depth < k}.Finite := by
  sorry

/-- P19, V4 1.24, preceding definition: the depth-`k` internal skeleton,
normalized in `A`; only native facets not contained in the root boundary enter it.
DEVIATION: apply `σ^k` to recover the printed ambient skeleton in `σ^k A`. -/
def internalSkeleton (S : SubstSystem d) (A : S.ι) (k : ℕ) : Set (E d) :=
  {x | ∃ (w : S.RoleWord A k) (f : FacetName S (S.nativeTile A k w).ty),
    ¬ (S.nativeTile A k w).cell 0 f.val ⊆ frontier (S.supertile k A) ∧
      (S.σ ^ k) x ∈ (S.nativeTile A k w).cell 0 f.val}

/-- P19, V4 1.24, preceding definition: the internal skeleton is exactly the
union of primitive facets born before depth `k`. -/
theorem internalSkeleton_eq_primitives (S : SubstSystem d) (A : S.ι) (k : ℕ) :
    internalSkeleton S A k = ⋃ f : {f : PrimitiveFacet S A // f.depth < k},
      f.val.carrier := by
  sorry

/-- P20, V4 1.24: a nonempty actual connected component of the internal skeleton. -/
def IsSkeletonComponent (S : SubstSystem d) (A : S.ι) (k : ℕ)
    (E₀ : Set (E d)) : Prop :=
  ∃ x ∈ internalSkeleton S A k, E₀ = connectedComponentIn (internalSkeleton S A k) x

/-- P20, V4 1.24: the set `E_A` includes every primitive facet meeting the
chosen connected component, at all birth depths smaller than `k`. -/
def principalFacets (S : SubstSystem d) (A : S.ι) (k : ℕ)
    (E₀ : Set (E d)) : Set (PrimitiveFacet S A) :=
  {f | f.depth < k ∧ (f.carrier ∩ E₀).Nonempty}

/-- P20, V4 1.24: every finite prescribed list lies in one component after
sufficient refinement. A prototype supplies nonempty geometry even for an empty list. -/
theorem principal_component (A : S.ι) (r : ℕ) (Φ : Finset (PrimitiveFacet S A))
    (hΦ : ∀ f ∈ Φ, f.depth < r) :
    ∃ k : ℕ, r ≤ k ∧ 1 ≤ k ∧ ∃ E₀ : Set (E d),
      IsSkeletonComponent S A k E₀ ∧ ∀ f ∈ Φ, f.carrier ⊆ E₀ := by
  sorry

/-- P20, V4 1.24: all facets meeting the component are wholly contained in it,
and their union is the entire component. -/
theorem principalFacets_spec (A : S.ι) (k : ℕ) (E₀ : Set (E d))
    (hE : IsSkeletonComponent S A k E₀) :
    (principalFacets S A k E₀).Finite ∧
      (∀ f ∈ principalFacets S A k E₀, f.carrier ⊆ E₀) ∧
      E₀ = ⋃ f ∈ principalFacets S A k E₀, f.carrier := by
  sorry

/-- P20, V4 1.24: principal-component choices persist under further refinement. -/
theorem principal_component_refines (A : S.ι) (k l : ℕ) (hkl : k ≤ l)
    (E₀ : Set (E d)) (hE : IsSkeletonComponent S A k E₀) :
    ∃ E₁ : Set (E d), IsSkeletonComponent S A l E₁ ∧ E₀ ⊆ E₁ := by
  sorry

/-- P21, V4 1.25: same-parent links include a common-listed vertex of both facets. -/
def SameParentLink {A : S.ι} (f g : PrimitiveFacet S A) : Prop :=
  f.birthAddress = g.birthAddress ∧ ∃ q : E d,
    f.IsVertex q ∧ g.IsVertex q ∧ f.CommonListed q

/-- P21, V4 1.25: ascent links include the exact birth-tree ancestry, a facet
of the lower birth node in the higher provider, a common-listed seed, and an
`e`-facing port. Thus zero-trace sectors are retained without inventing a port. -/
def AscentLink {A : S.ι} (k : ℕ) (f g : PrimitiveFacet S A) : Prop :=
  g.depth < f.depth ∧
    (f.birthNode k).IsDescendant (k - f.depth) (g.birthNode k) (k - g.depth) ∧
    ∃ e : FacetName S f.birthType, f.birthCell e.val ⊆ g.carrier ∧
      ∃ q : E d, f.IsVertex q ∧ q ∈ f.birthCell e.val ∧ f.CommonListed q ∧
        ∃ (i : S.I f.birthType) (c : FacetName S (S.child f.birthType i).ty),
          q ∈ f.childCell i c.val ∧ f.childCell i c.val ⊆ f.birthCell e.val

/-- P21, V4 1.25: the undirected routing links. -/
def RoutingLink {A : S.ι} (k : ℕ) (f g : PrimitiveFacet S A) : Prop :=
  SameParentLink f g ∨ AscentLink k f g ∨ AscentLink k g f

/-- P21, V4 1.25: restrict any link to principal facets passing through `p`. -/
def ThroughLink {A : S.ι} (Q : Set (PrimitiveFacet S A)) (p : E d)
    (R : PrimitiveFacet S A → PrimitiveFacet S A → Prop)
    (f g : PrimitiveFacet S A) : Prop :=
  f ∈ Q ∧ p ∈ f.carrier ∧ g ∈ Q ∧ p ∈ g.carrier ∧ R f g

/-- P21, V4 1.25: primitive facets of the principal component through a common
point are connected by exactly the same-parent and ascent links. -/
theorem birth_ascent_routing (A : S.ι) (k : ℕ) (E₀ : Set (E d))
    (hE : IsSkeletonComponent S A k E₀) (p : E d)
    (f g : PrimitiveFacet S A) (hf : f ∈ principalFacets S A k E₀)
    (hg : g ∈ principalFacets S A k E₀) (hpf : p ∈ f.carrier) (hpg : p ∈ g.carrier) :
    Relation.ReflTransGen (ThroughLink (principalFacets S A k E₀) p (RoutingLink k))
      f g := by
  sorry

/-- P21, V4 1.25: the least standard ancestor containing every root-owned native
tile through the point, with minimal birth height among all such common ancestors. -/
def IsTopBirth (A : S.ι) (k : ℕ) (p : E d) (b : ℕ) (P : FramedNode S) : Prop :=
  S.IsStandardNode A k b P ∧
    (∀ w : S.RoleWord A k, (S.σ ^ k) p ∈ (S.nativeTile A k w).carrier 0 →
      (S.nativeTile A k w).IsDescendant 0 P b) ∧
    ∀ (b' : ℕ) (P' : FramedNode S), S.IsStandardNode A k b' P' →
      (∀ w : S.RoleWord A k, (S.σ ^ k) p ∈ (S.nativeTile A k w).carrier 0 →
        (S.nativeTile A k w).IsDescendant 0 P' b') → b ≤ b'

/-- P21, V4 1.25: top-class facets, with their actual least common birth parent. -/
def topClass (A : S.ι) (k : ℕ) (E₀ : Set (E d)) (p : E d)
    (b : ℕ) (P : FramedNode S) : Set (PrimitiveFacet S A) :=
  {f | f ∈ principalFacets S A k E₀ ∧ p ∈ f.carrier ∧
    k - f.depth = b ∧ f.birthNode k = P}

/-- P21, V4 1.25: number of strict ascent links in a finite route. -/
def routeAscents {A : S.ι} (k : ℕ) (path : List (PrimitiveFacet S A)) : ℕ := by
  classical
  exact ((path.zip path.tail).filter (fun q => AscentLink k q.1 q.2)).length

/-- P21, V4 1.25 (moreover): from every facet through `p`, an upward route
reaches the nonempty top class with at most `k` ascents. The top class itself is
connected by same-parent links. Two distinct facets ensure a positive birth height. -/
theorem birth_ascent_top (A : S.ι) (k : ℕ) (E₀ : Set (E d))
    (hE : IsSkeletonComponent S A k E₀) (p : E d)
    (f g : PrimitiveFacet S A) (hfg : f ≠ g)
    (hf : f ∈ principalFacets S A k E₀) (hg : g ∈ principalFacets S A k E₀)
    (hpf : p ∈ f.carrier) (hpg : p ∈ g.carrier) :
    ∃ (b : ℕ) (P : FramedNode S), 1 ≤ b ∧ b ≤ k ∧ IsTopBirth A k p b P ∧
      (topClass A k E₀ p b P).Nonempty ∧
      (∀ u ∈ topClass A k E₀ p b P, ∀ v ∈ topClass A k E₀ p b P,
        Relation.ReflTransGen (ThroughLink (topClass A k E₀ p b P) p SameParentLink)
          u v) ∧
      ∀ u ∈ principalFacets S A k E₀, p ∈ u.carrier →
        ∃ (v : PrimitiveFacet S A) (path : List (PrimitiveFacet S A)),
          v ∈ topClass A k E₀ p b P ∧ path.head? = some u ∧
          path.getLast? = some v ∧
          (∀ z ∈ path, z ∈ principalFacets S A k E₀ ∧ p ∈ z.carrier) ∧
          path.IsChain (fun a c => SameParentLink a c ∨ AscentLink k a c) ∧
          routeAscents k path ≤ k := by
  sorry

/-- P22, V4 8.3: a role word follows the unique child at every step. -/
def OnlyChildWord (S : SubstSystem d) :
    (A : S.ι) → (n : ℕ) → S.RoleWord A n → Prop
  | _, 0, _ => True
  | A, n + 1, w => Fintype.card (S.I A) = 1 ∧
      OnlyChildWord S (S.child A w.1).ty n w.2

/-- P22, V4 8.3: first branching address, uniquely determined by the one-child
run. Existence and the bound are supplied by stage-1 C3, V4 1.28. -/
theorem firstBranching_exists_unique (A : S.ι) :
    ∃! a : Σ n : ℕ, S.RoleWord A n,
      OnlyChildWord S A a.1 a.2 ∧
        2 ≤ Fintype.card (S.I (S.nativeTile A a.1 a.2).ty) ∧
        a.1 ≤ Fintype.card S.ι - 1 := by
  sorry

/-- P22, V4 8.3: the actual first branching address, without an arbitrary
branching-descendant choice. -/
def firstBranching (A : S.ι) : Σ n : ℕ, S.RoleWord A n :=
  Classical.choose (firstBranching_exists_unique A)

/-- P22, V4 8.3: characterization and depth bound of the first branching node. -/
theorem firstBranching_spec (A : S.ι) :
    OnlyChildWord S A (firstBranching A).1 (firstBranching A).2 ∧
      2 ≤ Fintype.card (S.I (S.nativeTile A (firstBranching A).1
        (firstBranching A).2).ty) ∧
      (firstBranching A).1 ≤ Fintype.card S.ι - 1 :=
  (Classical.choose_spec (firstBranching_exists_unique A)).1

/-- P22, V4 8.3: `F(A)`, all first-generation internal facets at the first
branching descendant, including their positions and complete role words relative to A. -/
def firstBranchingFacets (A : S.ι) : Set (PrimitiveFacet S A) :=
  {f | f.birthAddress = firstBranching A}

/-- P22, V4 8.3: the first branching descendant has an internal facet.
This explicit nonemptiness prevents a vacuous required-list construction. -/
theorem firstBranchingFacets_nonempty (A : S.ι) :
    (firstBranchingFacets A).Nonempty := by
  sorry

/-- P22, V4 8.3: placement of the child's first branching address in the parent.
The initial role is retained, so different child occurrences stay distinguished. -/
def childFirstBranchingAddress (A : S.ι) (i : S.I A) : Σ n : ℕ, S.RoleWord A n :=
  ⟨(firstBranching (S.child A i).ty).1 + 1, ⟨i, (firstBranching (S.child A i).ty).2⟩⟩

/-- P22, V4 8.3: the three required families as a set of positioned primitive
facets: first generation, `F(A)`, and `iF(A_i)` for every child role. -/
def requiredSet (A : S.ι) : Set (PrimitiveFacet S A) :=
  {f | f.depth = 0 ∨ f ∈ firstBranchingFacets A ∨
    ∃ i : S.I A, f.birthAddress = childFirstBranchingAddress A i}

/-- P22, V4 8.3: the required set is finite and every required facet has birth
depth at most `p+1`, where `p = |T|-1`. -/
theorem requiredSet_finite (A : S.ι) :
    (requiredSet A).Finite ∧
      ∀ f ∈ requiredSet A, f.depth ≤ (Fintype.card S.ι - 1) + 1 := by
  sorry

/-- P22, V4 8.3: the actual finite required list `Req′(A)`.
No selected site arm and no propagation of a selected arm through placeholders occurs. -/
def required_list (A : S.ι) : Finset (PrimitiveFacet S A) :=
  (requiredSet_finite A).1.toFinset

/-- P22, V4 8.3: exact membership specification of `Req′(A)`. -/
theorem mem_required_list (A : S.ι) (f : PrimitiveFacet S A) :
    f ∈ required_list A ↔ f.depth = 0 ∨ f ∈ firstBranchingFacets A ∨
      ∃ i : S.I A, f.birthAddress = childFirstBranchingAddress A i := by
  simp only [required_list, Set.Finite.mem_toFinset, requiredSet, Set.mem_setOf_eq]

/-- P22/P20, V4 8.3, 1.24: the replacement list fits a principal component
at any prescribed lower bound on `k`. Existence uses the nonempty `F(A)`. -/
theorem required_principal_component (A : S.ι) (k₀ : ℕ) :
    ∃ k : ℕ, k₀ ≤ k ∧ ∃ E₀ : Set (E d), IsSkeletonComponent S A k E₀ ∧
      ∀ f ∈ required_list A, f ∈ principalFacets S A k E₀ := by
  sorry

/-- P19, V4 1.24: normalized skeletons increase under further subdivision. -/
theorem internalSkeleton_mono (A : S.ι) (k l : ℕ) (hkl : k ≤ l) :
    internalSkeleton S A k ⊆ internalSkeleton S A l := by
  sorry

/-- P19/P21, V4 1.24--1.25: the normalized birth frame is exactly the full
prototype frame of the actual standard birth node pulled back by `σ⁻ᵏ`. -/
theorem PrimitiveFacet.birthFrame_spec {A : S.ι} (f : PrimitiveFacet S A)
    (k : ℕ) (hf : f.depth ≤ k) :
    (f.birthNode k).ty = f.birthType ∧
      ((f.birthNode k).prototypeFrame (k - f.depth)).trans
        (S.σ ^ k).symm.toAffineEquiv = f.birthFrame := by
  sorry

/-- P21, V4 1.25: meeting first-generation facets of one birth node always
have the common-listed vertex needed for a same-parent link. -/
theorem sameParent_seed {A : S.ι} (f g : PrimitiveFacet S A)
    (hparent : f.birthAddress = g.birthAddress)
    (hmeet : (f.carrier ∩ g.carrier).Nonempty) : SameParentLink f g := by
  sorry

/-- P21, V4 1.25: each same-parent intersection is a union of cells common
to the owning child complexes; at every point one can name such a minimal cell. -/
theorem sameParent_intersection_cells {A : S.ι} (f g : PrimitiveFacet S A)
    (hparent : f.birthAddress = g.birthAddress) (p : E d)
    (hp : p ∈ f.carrier ∩ g.carrier) :
    ∃ (i : S.I f.birthType) (e : CellName S (S.child f.birthType i).ty),
      p ∈ relint (f.childCell i e.val) ∧ f.childCell i e.val ⊆ f.carrier ∩ g.carrier := by
  sorry

/-- P21, V4 1.25: a directed ascent strictly increases the actual birth height. -/
theorem AscentLink.birthHeight_lt {A : S.ι} (k : ℕ) (f g : PrimitiveFacet S A)
    (hf : f.depth < k) (hlink : AscentLink k f g) : k - f.depth < k - g.depth := by
  have hdepth := hlink.1
  omega

/-- P22, V4 8.3: first branching occurs at depth zero precisely when the
original type already has at least two children. -/
theorem firstBranching_zero_iff (A : S.ι) :
    (firstBranching A).1 = 0 ↔ 2 ≤ Fintype.card (S.I A) := by
  sorry

/-- P22, V4 8.3: the replacement required list is never empty for an actual type. -/
theorem required_list_nonempty (A : S.ι) : (required_list A).Nonempty := by
  sorry

/-- P22, V4 8.3: every child contributes its own positioned first-branching
facets to the parent's list, retaining the initial role of that child. -/
theorem required_child_firstBranching (A : S.ι) (i : S.I A) :
    ∃ f ∈ required_list A, f.birthAddress = childFirstBranchingAddress A i := by
  sorry

end Enforce
