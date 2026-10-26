import Enforce.Geometry.CellComplex

/-!
# Substitution data, native frames and the compatible rotation group

One structure carries (H1)--(H6). The species (H7) is defined in `Tiling`.
Children are indexed: a role remembers the parent type and the child index.
The rotation group is the infimum of closed subgroups containing the generators;
closedness is measured in the finite-dimensional space of continuous linear maps.
-/

open Set

noncomputable section

namespace Enforce

variable {d : ℕ}

/-- S1, V4 §1.0 (H3): one prescribed child, with its type and rigid placement. -/
structure Child (d : ℕ) (ι : Type) where
  /-- S1, V4 §1.0 (H3): child type. -/
  ty : ι
  /-- S1, V4 §1.0 (H3): orthogonal part; reflections are permitted. -/
  rotation : Ortho d
  /-- S1, V4 §1.0 (H3): translation in the expanded parent. -/
  offset : E d

/-- S1, V4 §1.0 (H3): the prescribed isometric child frame. -/
def Child.frame {ι : Type} (b : Child d ι) : Iso d :=
  rigidMotion b.rotation b.offset

/-- S1, V4 §1.0 (H1)--(H6): a finite polyhedral substitution system.
There is no primitivity, finite local complexity, recognizability or side-to-side
hypothesis. Empty catalogues are permitted; no existence of a source is assumed. -/
structure SubstSystem (d : ℕ) [Fact (2 ≤ d)] where
  /-- S1, V4 §1.0 (H1): the type catalogue. -/
  ι : Type
  /-- S1, V4 §1.0 (H1): finiteness of the catalogue. -/
  [types_finite : Fintype ι]
  /-- S1, V4 §1.0 (H1): polyhedral manifold prototiles. -/
  proto : ι → PolyManifoldDomain d
  /-- S1, V4 §1.0 (H2): the proper boundary complex of each prototile. -/
  cx : ∀ A, CellComplex (proto A)
  /-- S1, V4 §1.0 (H3): the general invertible linear expansion. -/
  σ : E d ≃ₗ[ℝ] E d
  /-- S1, V4 §1.0 (H3): a lower expansion factor. -/
  c : ℝ
  /-- S1, V4 §1.0 (H3): strict one-step expansion. -/
  c_gt_one : 1 < c
  /-- S1, V4 §1.0 (H3): the least singular value is bounded below by `c`. -/
  expand : ∀ x : E d, c * ‖x‖ ≤ ‖σ x‖
  /-- S1, V4 §1.0 (H3): roles of children, indexed by parent type. -/
  I : ι → Type
  /-- S1, V4 §1.0 (H3): each prescribed list is finite. -/
  [roles_finite : ∀ A, Fintype (I A)]
  /-- S1, V4 §1.0 (H3): the prescribed child data. -/
  child : ∀ A, I A → Child d ι
  /-- S1, V4 §1.0 (H3): the children cover the expanded parent. -/
  children_cover : ∀ A,
    σ '' (proto A).carrier = ⋃ i : I A,
      placedSet (child A i).frame (proto (child A i).ty).carrier
  /-- S1, V4 §1.0 (H3): distinct roles have disjoint child interiors. -/
  children_disjoint : ∀ A, Pairwise (fun i j : I A =>
    Disjoint (interior (placedSet (child A i).frame (proto (child A i).ty).carrier))
      (interior (placedSet (child A j).frame (proto (child A j).ty).carrier)))
  /-- S1, V4 §1.0 (H4): every nonnegative conjugate is orthogonal.
  Norm preservation is an equivalent formulation for these linear equivalences. -/
  h4 : ∀ (m : ℕ) A (i : I A) (x : E d),
    ‖linearConj σ (m : ℤ) (child A i).rotation.toLinearEquiv x‖ = ‖x‖
  /-- S1, V4 §1.0 (H5): every expanded `j`-cell is covered by child `j`-cells.
  The finite set of pairs records which placed cells make up the union. -/
  heredity : ∀ A e, e ∈ (cx A).cells →
    ∃ f : Finset (Σ i : I A, {e' : Cell d //
        e' ∈ (cx (child A i).ty).cells ∧ e'.dim = e.dim}),
      σ '' e.carrier = ⋃ q ∈ f, placedSet (child A q.1).frame q.2.val.carrier
  /-- S1, V4 §1.0 (H6): relative-incidence sibling conformity.
  Membership in a listed relative interior names the minimal cell without making
  an arbitrary choice at a point outside a boundary. -/
  sibling_conformity : ∀ A (i j : I A), i ≠ j → ∀ p : E d,
    p ∈ placedSet (child A i).frame (proto (child A i).ty).carrier →
    p ∈ placedSet (child A j).frame (proto (child A j).ty).carrier →
    ∀ e ∈ (cx (child A i).ty).cells,
      (child A i).frame.symm p ∈ relint e.carrier → e.dim ≤ d - 2 →
      ∃ f ∈ (cx (child A j).ty).cells,
        placedSet (child A i).frame e.carrier = placedSet (child A j).frame f.carrier

attribute [instance] SubstSystem.types_finite SubstSystem.roles_finite

variable [Fact (2 ≤ d)]

namespace SubstSystem

variable (S : SubstSystem d)

/-- S2, V4 §1.0 (H3): a role retains its parent type as well as its index. -/
abbrev Role := Σ A : S.ι, S.I A

/-- S2, V4 §1.0, Frames: the carrier of the standard height-`n` supertile. -/
def supertile (n : ℕ) (A : S.ι) : Set (E d) := (S.σ ^ n) '' (S.proto A).carrier

/-- S2, V4 §1.0 (H3)--(H4): orthogonal conjugate at a specified height. -/
def childRotation (n : ℕ) {A : S.ι} (i : S.I A) : Ortho d :=
  { linearConj S.σ (n : ℤ) (S.child A i).rotation.toLinearEquiv with
    norm_map' := S.h4 n A i }

/-- S2, V4 §1.0, Frames: the placed-child map
`x ↦ σ^n R_i σ^(-n) x + σ^n t_i`, as an affine isometry. -/
def placeChild (n : ℕ) {A : S.ι} (i : S.I A) : Iso d :=
  rigidMotion (S.childRotation n i) ((S.σ ^ n) (S.child A i).offset)

/-- S2, V4 §1.0, Frames: the affine formula underlying the placed-child map. -/
theorem placeChild_apply (n : ℕ) {A : S.ι} (i : S.I A) (x : E d) :
    S.placeChild n i x =
      linearConj S.σ (n : ℤ) (S.child A i).rotation.toLinearEquiv x +
        (S.σ ^ n) (S.child A i).offset := rfl

/-- S2, V4 §1.0 (H3): a well-typed role word of exact length `n`.
The next letter is indexed by the type of the preceding child. -/
def RoleWord : S.ι → ℕ → Type
  | _, 0 => Unit
  | A, n + 1 => Σ i : S.I A, RoleWord (S.child A i).ty n

/-- S2, V4 §1.0 (H3): there are finitely many role words of each fixed depth. -/
theorem roleWord_finite (A : S.ι) (n : ℕ) : Finite (S.RoleWord A n) := by
  sorry

/-- S2, V4 §1.0 (H3): a finite enumeration of well-typed role words. -/
instance roleWordFintype (A : S.ι) (n : ℕ) : Fintype (S.RoleWord A n) := by
  letI := S.roleWord_finite A n
  exact Fintype.ofFinite _

end SubstSystem

/-- S2/T5, V4 §1.0, Hierarchies and Frames: a type and an isometric frame.
The height is supplied when taking its carrier, so no casts of frames are needed. -/
@[ext]
structure FramedNode (S : SubstSystem d) where
  /-- S2/T5, V4 §1.0: prototype type. -/
  ty : S.ι
  /-- S2/T5, V4 §1.0: the isometric frame acting on `σ^n A`. -/
  frame : Iso d

namespace FramedNode

variable {S : SubstSystem d}

/-- T5, V4 §1.0, Hierarchies: the support at a specified height. -/
def carrier (N : FramedNode S) (n : ℕ) : Set (E d) :=
  placedSet N.frame (S.supertile n N.ty)

/-- T5, V4 §1.0, Frames: the full affine frame from the unexpanded prototype. -/
def prototypeFrame (N : FramedNode S) (n : ℕ) : E d ≃ᵃ[ℝ] E d :=
  (S.σ ^ n).toAffineEquiv.trans N.frame.toAffineEquiv

/-- T5, V4 §1.0, Hierarchies: applying a common Euclidean isometry to a node. -/
def move (N : FramedNode S) (g : Iso d) : FramedNode S :=
  ⟨N.ty, N.frame.trans g⟩

/-- T5, V4 §1.0, Frames: child of role `i` of a height-`n+1` node. -/
def child (N : FramedNode S) (n : ℕ) (i : S.I N.ty) : FramedNode S :=
  ⟨(S.child N.ty i).ty, (S.placeChild n i).trans N.frame⟩

end FramedNode

namespace SubstSystem

variable (S : SubstSystem d)

/-- S2, V4 §1.0 (H3): the height-`h` descendant at the given role word,
inside the standard supertile of height `h + depth`. This is the actual recursive
placement, including all anisotropic conjugates. -/
def descendantNode : (A : S.ι) → (h depth : ℕ) → S.RoleWord A depth → FramedNode S
  | A, _, 0, _ => ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  | A, h, depth + 1, w =>
    (descendantNode (S.child A w.1).ty h depth w.2).move (S.placeChild (h + depth) w.1)

/-- S2, V4 §1.0 (H3): the native ground tile named by a role word. -/
def nativeTile (A : S.ι) (n : ℕ) (w : S.RoleWord A n) : FramedNode S :=
  S.descendantNode A 0 n w

/-- S2, V4 §1.0 (H3): all native ground tiles, as a finite set of framed tiles. -/
def descendants (A : S.ι) (n : ℕ) : Finset (FramedNode S) := by
  classical
  exact Finset.univ.image (S.nativeTile A n)

/-- S3, V4 §1.0 (H4): native frames, and hence their restrictions to every
listed cell, are isometric. The proof is immediate from the frame construction. -/
theorem native_isometric (A : S.ι) (n : ℕ) (w : S.RoleWord A n) :
    Isometry (S.nativeTile A n w).frame :=
  (S.nativeTile A n w).frame.isometry

/-- S3, V4 §1.0 (H4): the same native frame is isometric on every listed
cell, in every dimension. No new choice of cell placement is made. -/
theorem native_cells_isometric (A : S.ι) (n : ℕ) (w : S.RoleWord A n)
    (e : Cell d) (_he : e ∈ (S.cx (S.nativeTile A n w).ty).cells) :
    ∀ x ∈ e.carrier, ∀ y ∈ e.carrier,
      dist ((S.nativeTile A n w).frame x) ((S.nativeTile A n w).frame y) = dist x y := by
  intro x _ y _
  exact (S.nativeTile A n w).frame.isometry.dist_eq x y

/-- S3, V4 §1.0 (H3)--(H4): native tiles cover the standard supertile. -/
theorem native_cover (A : S.ι) (n : ℕ) :
    (⋃ w : S.RoleWord A n, (S.nativeTile A n w).carrier 0) = S.supertile n A := by
  sorry

/-- S3, V4 §1.0 (H3)--(H4): distinct role words have disjoint native interiors. -/
theorem native_disjoint (A : S.ι) (n : ℕ) :
    Pairwise (fun v w : S.RoleWord A n => Disjoint
      (interior ((S.nativeTile A n v).carrier 0))
      (interior ((S.nativeTile A n w).carrier 0))) := by
  sorry

/-- S4, V4 §1.0 (H5): iterated heredity in every boundary dimension. -/
theorem heredity_iter (A : S.ι) (n : ℕ) (e : Cell d) (he : e ∈ (S.cx A).cells) :
    ∃ f : Finset (Σ w : S.RoleWord A n, {e' : Cell d //
        e' ∈ (S.cx (S.nativeTile A n w).ty).cells ∧ e'.dim = e.dim}),
      (S.σ ^ n) '' e.carrier =
        ⋃ q ∈ f, placedSet (S.nativeTile A n q.1).frame q.2.val.carrier := by
  sorry

/-- S5, V4 1.9: the prescribed compatible orthogonal generators. -/
def rotationGenerators : Set (Ortho d) :=
  {R | ∃ (n : ℕ) (A : S.ι) (i : S.I A), R = S.childRotation n i}

/-- S5, V4 1.9: the closed subgroup generated by all nonnegative conjugates.
Closedness is expressed through the operator topology, avoiding a redundant
global topology instance on `LinearIsometryEquiv`. This is the usual closed hull. -/
def rotGroup : Subgroup (Ortho d) :=
  sInf {G : Subgroup (Ortho d) | S.rotationGenerators ⊆ (G : Set (Ortho d)) ∧
    IsClosed ((fun R : Ortho d => R.toLinearIsometry.toContinuousLinearMap) ''
      (G : Set (Ortho d)))}

/-- S5, V4 1.9: the closed hull contains the generators and is closed. -/
theorem rotGroup_spec : S.rotationGenerators ⊆ (S.rotGroup : Set (Ortho d)) ∧
    IsClosed ((fun R : Ortho d => R.toLinearIsometry.toContinuousLinearMap) ''
      (S.rotGroup : Set (Ortho d))) := by
  sorry

/-- S6, V4 1.10(a): conjugation by `σ` permutes the compact rotation group. -/
theorem rotGroup_conj :
    (fun R : Ortho d => linearConj S.σ 1 R.toLinearEquiv) ''
        (S.rotGroup : Set (Ortho d)) =
      (fun R : Ortho d => R.toLinearEquiv) '' (S.rotGroup : Set (Ortho d)) := by
  sorry

/-- S6, V4 1.10(a): all integral conjugates of group elements are orthogonal
and remain in the same group, including the negative powers used in coarsening. -/
theorem rotGroup_conj_zpow (m : ℤ) (R : Ortho d) (hR : R ∈ S.rotGroup) :
    ∃ Q ∈ S.rotGroup, Q.toLinearEquiv = linearConj S.σ m R.toLinearEquiv := by
  sorry

/-- S6, V4 1.10(b): descendants in a node have orthogonal parts in `Q H`. -/
theorem descendant_frames (A : S.ι) (h depth : ℕ) (w : S.RoleWord A depth)
    (φ : Iso d) :
    ∃ R ∈ S.rotGroup,
      ((S.descendantNode A h depth w).move φ).frame.linearIsometryEquiv =
        φ.linearIsometryEquiv * R := by
  sorry

/-- S6, V4 1.10(c): the finite catalogue `Π` of prototype cell directions. -/
def cellDirections : Set (Submodule ℝ (E d)) :=
  {V | ∃ A e, e ∈ (S.cx A).cells ∧ V = cellDirection e.carrier}

/-- S6, V4 1.10(c): the orbit of a direction under the compatible group. -/
def directionOrbit (V : Submodule ℝ (E d)) : Set (Submodule ℝ (E d)) :=
  {W | ∃ R ∈ S.rotGroup, W = V.map R.toLinearEquiv.toLinearMap}

/-- G9/S6, V4 1.10(c), 1.16(b): the invariant family `HΠ` of direction spaces. -/
def hPi : Set (Submodule ℝ (E d)) :=
  {W | ∃ V ∈ S.cellDirections, W ∈ S.directionOrbit V}

/-- S6, V4 1.10(c): the finite set of direction orbits occurring in `HΠ`. -/
def directionOrbits : Set (Set (Submodule ℝ (E d))) :=
  {O | ∃ V ∈ S.cellDirections, O = S.directionOrbit V}

/-- S6, V4 1.10(c): `σ` preserves `HΠ` and permutes its finitely many orbits. -/
theorem orbits_finite : S.directionOrbits.Finite ∧
    (∀ V ∈ S.hPi, V.map S.σ.toLinearMap ∈ S.hPi) ∧
    ∃ p : S.directionOrbits ≃ S.directionOrbits, ∀ O,
      (p O).val = (fun V => V.map S.σ.toLinearMap) '' O.val := by
  sorry

/-- S6, V4 1.10(c): both oriented sides of every prototype facet direction.
Scaling a nonzero defining functional by a positive scalar gives the same side,
so this catalogue has only two sides per distinct facet direction. -/
def facetSides : Set (Set (E d)) :=
  {K | ∃ (A : S.ι) (e : Cell d), e ∈ (S.cx A).facets ∧
    ∃ ℓ : E d →ₗ[ℝ] ℝ, LinearMap.ker ℓ = cellDirection e.carrier ∧
      K = {x | 0 ≤ ℓ x}}

/-- S6, V4 1.10(c): the rotation-group orbit of an oriented geometric side. -/
def sideOrbit (K : Set (E d)) : Set (Set (E d)) :=
  {C | ∃ R ∈ S.rotGroup, C = R '' K}

/-- S6, V4 1.10(c): all oriented facet-side orbits in the prototype catalogue. -/
def facetSideOrbits : Set (Set (Set (E d))) :=
  {O | ∃ K ∈ S.facetSides, O = S.sideOrbit K}

/-- S6, V4 1.10(c): the oriented supplement to `orbits_finite`.
There are finitely many prototype sides and finitely many group orbits, and `σ`
permutes those orbits with their orientations, as required for half-space cones. -/
theorem oriented_orbits_finite : S.facetSides.Finite ∧ S.facetSideOrbits.Finite ∧
    ∃ p : S.facetSideOrbits ≃ S.facetSideOrbits, ∀ O,
      (p O).val = (fun K => S.σ '' K) '' O.val := by
  sorry

/-- C3, V4 1.28: a chain of one-child roles has at most `|ι|-1` steps.
The role data identify the actual successive child types; no acyclicity is assumed. -/
theorem one_child_runs (s : ℕ) (A : Fin (s + 1) → S.ι)
    (i : ∀ j : Fin s, S.I (A j.castSucc))
    (hunique : ∀ j : Fin s, Fintype.card (S.I (A j.castSucc)) = 1)
    (hchild : ∀ j : Fin s, (S.child (A j.castSucc) (i j)).ty = A j.succ) :
    s ≤ Fintype.card S.ι - 1 := by
  sorry

/-- C3, V4 1.28: every type reaches a branching type within `|ι|-1` roles. -/
theorem reaches_branching (A : S.ι) :
    ∃ n ≤ Fintype.card S.ι - 1, ∃ w : S.RoleWord A n,
      2 ≤ Fintype.card (S.I (S.nativeTile A n w).ty) := by
  sorry

end SubstSystem

omit [Fact (2 ≤ d)] in
/-- S7, V4 7.5: the finite test for all-power compatibility, independent of
any substitution system. The test uses exponents `1,...,d(d+1)/2-1`. -/
theorem h4_finite_test (σ : E d ≃ₗ[ℝ] E d) (R : Ortho d) :
    (∀ (m : ℕ) (x : E d), ‖linearConj σ (m : ℤ) R.toLinearEquiv x‖ = ‖x‖) ↔
      (∀ m : ℕ, 1 ≤ m → m < d * (d + 1) / 2 →
        ∀ x : E d, ‖linearConj σ (m : ℤ) R.toLinearEquiv x‖ = ‖x‖) := by
  sorry

end Enforce
