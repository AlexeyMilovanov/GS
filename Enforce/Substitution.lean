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
  induction' n with n ih generalizing A
  · dsimp [RoleWord]
    exact inferInstance
  · dsimp [RoleWord]
    haveI (B : S.ι) : Finite (S.RoleWord B n) := ih B
    exact inferInstance

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
  induction' n with n ih generalizing A
  · dsimp [nativeTile, descendantNode, supertile, FramedNode.carrier, placedSet, RoleWord]
    ext x
    simp
  · dsimp [supertile]
    have h1 : ⇑(S.σ ^ (n + 1)) = (S.σ ^ n) ∘ S.σ := rfl
    rw [h1]
    rw [Set.image_comp]
    rw [S.children_cover]
    rw [Set.image_iUnion]
    change (⋃ w : Σ i : S.I A, S.RoleWord (S.child A i).ty n, (S.nativeTile A (n + 1) w).carrier 0) = _
    rw [Set.iUnion_sigma]
    apply congr_arg
    funext i
    have h2 := ih (S.child A i).ty
    have h3 : ∀ (w : S.RoleWord (S.child A i).ty n),
        (S.nativeTile A (n + 1) ⟨i, w⟩).carrier 0 =
        (S.placeChild n i) '' ((S.nativeTile (S.child A i).ty n w).carrier 0) := by
      intro w
      dsimp [nativeTile, descendantNode, FramedNode.carrier, placedSet, FramedNode.move]
      rw [← Set.image_comp]
      have hz : 0 + n = n := by omega
      rw [hz]
    simp_rw [h3]
    rw [← Set.image_iUnion]
    rw [h2]
    dsimp [supertile, placedSet]
    rw [← Set.image_comp]
    rw [← Set.image_comp]
    congr 1
    ext x
    dsimp
    rw [placeChild_apply]
    have hz : (S.child A i).frame = S.placeChild 0 i := rfl
    rw [hz, placeChild_apply]
    simp
    dsimp [linearConj]
    simp

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

private theorem rotGroup_op_injective (d : ℕ) :
    Function.Injective (fun R : Ortho d => R.toLinearIsometry.toContinuousLinearMap) := by
  intro R Q h
  ext x : 1
  exact congrArg (fun f : E d →L[ℝ] E d => f x) h

private theorem ortho_range_isClosed (d : ℕ) : IsClosed (Set.range (fun R : Ortho d => R.toLinearIsometry.toContinuousLinearMap)) := by
  have hC : IsClosed {f : E d →L[ℝ] E d | ∀ x, ‖f x‖ = ‖x‖} := by
    have : {f : E d →L[ℝ] E d | ∀ x, ‖f x‖ = ‖x‖} = ⋂ x, {f | ‖f x‖ = ‖x‖} := by ext f; simp
    rw [this]
    refine isClosed_iInter fun x => isClosed_eq ?_ continuous_const
    exact continuous_norm.comp (ContinuousLinearMap.apply ℝ (E d) x).continuous
  convert hC using 1
  ext f
  constructor
  · rintro ⟨R, rfl⟩ x; exact R.norm_map x
  · intro h
    let li : E d →ₗᵢ[ℝ] E d := ⟨f.toLinearMap, h⟩
    exact ⟨li.toLinearIsometryEquiv rfl, by ext x; rfl⟩

/-- S5, V4 1.9: the closed hull contains the generators and is closed. -/
theorem rotGroup_spec : S.rotationGenerators ⊆ (S.rotGroup : Set (Ortho d)) ∧
    IsClosed ((fun R : Ortho d => R.toLinearIsometry.toContinuousLinearMap) ''
      (S.rotGroup : Set (Ortho d))) := by
  set op : Ortho d → (E d →L[ℝ] E d) := fun R => R.toLinearIsometry.toContinuousLinearMap with hop
  set F : Set (Subgroup (Ortho d)) := {G | S.rotationGenerators ⊆ (G : Set (Ortho d)) ∧ IsClosed (op '' (G : Set (Ortho d)))} with hF
  have key : (S.rotGroup : Set (Ortho d)) = ⋂ G ∈ F, (G : Set (Ortho d)) := by
    show ((sInf F : Subgroup (Ortho d)) : Set (Ortho d)) = _
    exact Subgroup.coe_sInf F
  refine ⟨?_, ?_⟩
  · intro x hx; rw [key]; simp only [Set.mem_iInter]; exact fun G hG => hG.1 hx
  · rw [key]
    rcases F.eq_empty_or_nonempty with h | hne
    · simp only [h, Set.mem_empty_iff_false, Set.iInter_of_empty, Set.iInter_univ, Set.image_univ]
      exact ortho_range_isClosed d
    · haveI : Nonempty F := hne.to_subtype
      have e : (⋂ G ∈ F, (G : Set (Ortho d))) = ⋂ G : F, ((G : Subgroup (Ortho d)) : Set (Ortho d)) := by
        ext x; simp only [Set.mem_iInter, SetCoe.forall]
      rw [e, Set.InjOn.image_iInter_eq ((rotGroup_op_injective d).injOn)]
      exact isClosed_iInter fun G => G.2.2

/-- The forward inclusion in V4 1.10(a), using minimality of the closed hull. -/
private theorem rotGroup_conj_forward :
    ∀ R ∈ S.rotGroup, ∃ Q ∈ S.rotGroup,
      linearConj S.σ 1 R.toLinearEquiv = Q.toLinearEquiv := by
  let ρ : Ortho d →* (E d ≃ₗ[ℝ] E d) :=
    { toFun := LinearIsometryEquiv.toLinearEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let c : (E d ≃ₗ[ℝ] E d) ≃* (E d ≃ₗ[ℝ] E d) := MulAut.conj S.σ
  let G : Subgroup (Ortho d) := S.rotGroup ⊓ (S.rotGroup.map ρ).comap (c.toMonoidHom.comp ρ)
  let op : Ortho d → (E d →L[ℝ] E d) :=
    fun R => R.toLinearIsometry.toContinuousLinearMap
  let C := S.σ.toContinuousLinearEquiv.conjContinuousAlgEquiv
  have hclosed : IsClosed (op '' (G : Set (Ortho d))) := by
    have heq : op '' (G : Set (Ortho d)) =
        (op '' (S.rotGroup : Set (Ortho d))) ∩
          C ⁻¹' (op '' (S.rotGroup : Set (Ortho d))) := by
      ext f
      constructor
      · rintro ⟨R, hR, rfl⟩
        rcases hR with ⟨hR, hconj⟩
        rcases hconj with ⟨Q, hQ, heq⟩
        refine ⟨⟨R, hR, rfl⟩, Q, hQ, ?_⟩
        ext x : 1
        exact congrArg (fun e : E d ≃ₗ[ℝ] E d => e x) heq
      · rintro ⟨⟨R, hR, rfl⟩, Q, hQ, heq⟩
        refine ⟨R, ⟨hR, Q, hQ, ?_⟩, rfl⟩
        ext x : 1
        exact congrArg (fun f : E d →L[ℝ] E d => f x) heq
    rw [heq]
    exact S.rotGroup_spec.2.inter (S.rotGroup_spec.2.preimage C.continuous)
  have hgen : S.rotationGenerators ⊆ (G : Set (Ortho d)) := by
    rintro R ⟨n, A, i, rfl⟩
    refine ⟨S.rotGroup_spec.1 ⟨n, A, i, rfl⟩,
      S.childRotation (n + 1) i, S.rotGroup_spec.1 ⟨n + 1, A, i, rfl⟩, ?_⟩
    change linearConj S.σ ((n + 1 : ℕ) : ℤ) (S.child A i).rotation.toLinearEquiv =
      S.σ * linearConj S.σ (n : ℤ) (S.child A i).rotation.toLinearEquiv * S.σ⁻¹
    simp only [linearConj, Nat.cast_add, Nat.cast_one, zpow_add, zpow_one, zpow_neg]
    group
  have hle : S.rotGroup ≤ G := sInf_le ⟨hgen, hclosed⟩
  intro R hR
  rcases (hle hR).2 with ⟨Q, hQ, heq⟩
  refine ⟨Q, hQ, ?_⟩
  simpa [c, ρ, linearConj, MulAut.conj_apply] using heq.symm

/-- Operator columns in a Hilbert sum, whose norm is the Frobenius norm. -/
private def rotGroup_conj_columns (d : ℕ) :
    (E d →L[ℝ] E d) →ₗ[ℝ] PiLp 2 (fun _ : Fin d => E d) where
  toFun f := WithLp.toLp 2 (fun i => f (EuclideanSpace.basisFun (Fin d) ℝ i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fact (2 ≤ d)] in
/-- An operator is determined by its values on the standard orthonormal basis. -/
private theorem rotGroup_conj_columns_injective : Function.Injective (rotGroup_conj_columns d) := by
  intro f g h
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext
  intro i
  exact congrArg (fun v : PiLp 2 (fun _ : Fin d => E d) => v i) h

omit [Fact (2 ≤ d)] in
/-- Squared Frobenius distance of orthogonal operators, expressed by a trace. -/
private theorem rotGroup_conj_columns_dist_sq (R Q : Ortho d) :
    dist (rotGroup_conj_columns d R.toLinearIsometry.toContinuousLinearMap)
      (rotGroup_conj_columns d Q.toLinearIsometry.toContinuousLinearMap) ^ 2 =
        2 * (d : ℝ) - 2 * LinearMap.trace ℝ (E d)
          (R.symm.toLinearEquiv.toLinearMap.comp Q.toLinearEquiv.toLinearMap) := by
  rw [PiLp.dist_sq_eq_of_L2,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [rotGroup_conj_columns, LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.toLp_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    dist_eq_norm, norm_sub_sq_real, LinearIsometryEquiv.norm_map,
    (EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one, one_pow,
    LinearIsometryEquiv.inner_map_eq_flip, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

omit [Fact (2 ≤ d)] in
/-- Conjugation preserves Frobenius distances whenever the conjugates are orthogonal. -/
private theorem rotGroup_conj_columns_conj_dist (σ : E d ≃ₗ[ℝ] E d) (R Q R' Q' : Ortho d)
    (hR : R'.toLinearEquiv = linearConj σ 1 R.toLinearEquiv)
    (hQ : Q'.toLinearEquiv = linearConj σ 1 Q.toLinearEquiv) :
    dist (rotGroup_conj_columns d R'.toLinearIsometry.toContinuousLinearMap)
      (rotGroup_conj_columns d Q'.toLinearIsometry.toContinuousLinearMap) =
    dist (rotGroup_conj_columns d R.toLinearIsometry.toContinuousLinearMap)
      (rotGroup_conj_columns d Q.toLinearIsometry.toContinuousLinearMap) := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [rotGroup_conj_columns_dist_sq, rotGroup_conj_columns_dist_sq]
  congr 2
  have heq : R'.symm.toLinearEquiv.toLinearMap.comp Q'.toLinearEquiv.toLinearMap =
      σ.conj (R.symm.toLinearEquiv.toLinearMap.comp Q.toLinearEquiv.toLinearMap) := by
    change (R'.toLinearEquiv⁻¹ * Q'.toLinearEquiv).toLinearMap =
      (σ * (R.toLinearEquiv⁻¹ * Q.toLinearEquiv) * σ⁻¹).toLinearMap
    congr 1
    rw [hR, hQ]
    simp only [linearConj, zpow_one, zpow_neg]
    group
  rw [heq, LinearMap.trace_conj']

/-- An isometry from a compact metric space to itself is surjective. -/
private theorem rotGroup_conj_compact_isometry_surjective {X : Type*} [MetricSpace X] [CompactSpace X]
    {f : X → X} (hf : Isometry f) : Function.Surjective f := by
  have hiter : ∀ n : ℕ, Isometry f^[n] := by
    intro n
    induction n with
    | zero => exact isometry_id
    | succ n ih => simpa only [Function.iterate_succ'] using hf.comp ih
  intro x
  have hcl : IsClosed (range f) := (isCompact_range hf.continuous).isClosed
  suffices hx : x ∈ closure (range f) from hcl.closure_subset hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y, φ, hφ, ht⟩ := CompactSpace.tendsto_subseq (fun n => f^[n] x)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 ht.cauchySeq ε hε
  have hnear := hN N le_rfl (N + 1) (Nat.le_succ N)
  let k := φ (N + 1) - φ N
  have hk : 0 < k := Nat.sub_pos_of_lt (hφ (Nat.lt_succ_self N))
  have heq : φ (N + 1) = φ N + k := (Nat.add_sub_of_le (hφ.monotone (Nat.le_succ N))).symm
  have hd : dist (f^[φ N] x) (f^[φ (N + 1)] x) = dist x (f^[k] x) := by
    rw [heq, Function.iterate_add_apply, (hiter (φ N)).dist_eq]
  refine ⟨f^[k] x, ?_, ?_⟩
  · refine ⟨f^[k - 1] x, ?_⟩
    simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel hk] using
      (Function.iterate_succ_apply' f (k - 1) x).symm
  · exact hd ▸ hnear

/-- A distance-preserving self-map of a compact subset has that subset as its image. -/
private theorem rotGroup_conj_compact_image_eq {X : Type*} [MetricSpace X] {K : Set X}
    (hK : IsCompact K) {f : X → X} (hmaps : MapsTo f K K)
    (hdist : ∀ x ∈ K, ∀ y ∈ K, dist (f x) (f y) = dist x y) : f '' K = K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let g : K → K := fun x => ⟨f x, hmaps x.property⟩
  have hg : Isometry g := Isometry.of_dist_eq fun x y => hdist x x.property y y.property
  apply Set.Subset.antisymm hmaps.image_subset
  intro y hy
  obtain ⟨x, hx⟩ := rotGroup_conj_compact_isometry_surjective hg ⟨y, hy⟩
  exact ⟨x, x.property, congrArg Subtype.val hx⟩

/-- S6, V4 1.10(a): conjugation by `σ` permutes the compact rotation group. -/
theorem rotGroup_conj :
    (fun R : Ortho d => linearConj S.σ 1 R.toLinearEquiv) ''
        (S.rotGroup : Set (Ortho d)) =
      (fun R : Ortho d => R.toLinearEquiv) '' (S.rotGroup : Set (Ortho d)) := by
  let op : Ortho d → (E d →L[ℝ] E d) :=
    fun R => R.toLinearIsometry.toContinuousLinearMap
  let C := S.σ.toContinuousLinearEquiv.conjContinuousAlgEquiv
  let K := op '' (S.rotGroup : Set (Ortho d))
  have hK : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded S.rotGroup_spec.2
    rw [isBounded_iff_forall_norm_le]
    refine ⟨1, ?_⟩
    rintro f ⟨R, hR, rfl⟩
    exact R.toLinearIsometry.norm_toContinuousLinearMap_le
  have hmaps : MapsTo C K K := by
    rintro f ⟨R, hR, rfl⟩
    obtain ⟨Q, hQ, heq⟩ := rotGroup_conj_forward S R hR
    refine ⟨Q, hQ, ?_⟩
    ext x : 1
    simpa [C, op, linearConj] using congrArg (fun e : E d ≃ₗ[ℝ] E d => e x) heq.symm
  -- Work in the Frobenius metric to obtain surjectivity from compactness.
  let reconstruct : PiLp 2 (fun _ : Fin d => E d) → (E d →L[ℝ] E d) :=
    fun v => ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.constr ℝ (fun i => v i)).toContinuousLinearMap
  have hrec (f : E d →L[ℝ] E d) : reconstruct (rotGroup_conj_columns d f) = f := by
    apply ContinuousLinearMap.coe_injective
    exact (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.constr_self ℝ f.toLinearMap
  let F : PiLp 2 (fun _ : Fin d => E d) → PiLp 2 (fun _ : Fin d => E d) :=
    fun v => rotGroup_conj_columns d (C (reconstruct v))
  have hF (f : E d →L[ℝ] E d) : F (rotGroup_conj_columns d f) = rotGroup_conj_columns d (C f) := by
    dsimp only [F]
    rw [hrec]
  have hsurj : F '' (rotGroup_conj_columns d '' K) = rotGroup_conj_columns d '' K := by
    apply rotGroup_conj_compact_image_eq (hK.image (rotGroup_conj_columns d).continuous_of_finiteDimensional)
    · rintro _ ⟨f, hf, rfl⟩
      rw [hF]
      exact ⟨C f, hmaps hf, rfl⟩
    · rintro _ ⟨_, ⟨R, hR, rfl⟩, rfl⟩ _ ⟨_, ⟨Q, hQ, rfl⟩, rfl⟩
      rw [hF, hF]
      obtain ⟨R', hR', heqR⟩ := rotGroup_conj_forward S R hR
      obtain ⟨Q', hQ', heqQ⟩ := rotGroup_conj_forward S Q hQ
      have hCR : C (op R) = op R' := by
        ext x : 1
        simpa [C, op, linearConj] using congrArg (fun e : E d ≃ₗ[ℝ] E d => e x) heqR
      have hCQ : C (op Q) = op Q' := by
        ext x : 1
        simpa [C, op, linearConj] using congrArg (fun e : E d ≃ₗ[ℝ] E d => e x) heqQ
      rw [hCR, hCQ]
      exact rotGroup_conj_columns_conj_dist S.σ R Q R' Q' heqR.symm heqQ.symm
  apply Set.Subset.antisymm
  · rintro _ ⟨R, hR, rfl⟩
    obtain ⟨Q, hQ, heq⟩ := rotGroup_conj_forward S R hR
    exact ⟨Q, hQ, heq.symm⟩
  · rintro _ ⟨R, hR, rfl⟩
    have hm : rotGroup_conj_columns d (op R) ∈ F '' (rotGroup_conj_columns d '' K) := by
      rw [hsurj]
      exact ⟨op R, ⟨R, hR, rfl⟩, rfl⟩
    obtain ⟨_, ⟨_, ⟨Q, hQ, rfl⟩, rfl⟩, heq⟩ := hm
    rw [hF] at heq
    have heq' := rotGroup_conj_columns_injective heq
    refine ⟨Q, hQ, ?_⟩
    ext x : 1
    simpa [C, op, linearConj] using congrArg (fun f : E d →L[ℝ] E d => f x) heq'

private lemma linearConj_add {d : ℕ} (σ : E d ≃ₗ[ℝ] E d) (a b : ℤ) (R : E d ≃ₗ[ℝ] E d) :
  linearConj σ (a + b) R = linearConj σ a (linearConj σ b R) := by
  dsimp [linearConj]
  rw [zpow_add, neg_add]
  have h1 : σ ^ (-a + -b) = σ ^ (-b) * σ ^ (-a) := by
    rw [add_comm, zpow_add]
  rw [h1]
  ext x
  simp

private lemma linearConj_zero {d : ℕ} (σ : E d ≃ₗ[ℝ] E d) (R : E d ≃ₗ[ℝ] E d) :
    linearConj σ 0 R = R := by
  dsimp [linearConj]
  ext x
  simp

private lemma linearConj_neg1_1 {d : ℕ} (σ : E d ≃ₗ[ℝ] E d) (R : E d ≃ₗ[ℝ] E d) :
    linearConj σ (-1) (linearConj σ 1 R) = R := by
  dsimp [linearConj]
  ext x
  simp

/-- S6, V4 1.10(a): all integral conjugates of group elements are orthogonal
and remain in the same group, including the negative powers used in coarsening. -/
theorem rotGroup_conj_zpow (m : ℤ) (R : Ortho d) (hR : R ∈ S.rotGroup) :
    ∃ Q ∈ S.rotGroup, Q.toLinearEquiv = linearConj S.σ m R.toLinearEquiv := by
  have H1 (R' : Ortho d) (hR' : R' ∈ S.rotGroup) : ∃ Q ∈ S.rotGroup, Q.toLinearEquiv = linearConj S.σ 1 R'.toLinearEquiv := by
    have hc := S.rotGroup_conj
    have h1 : linearConj S.σ 1 R'.toLinearEquiv ∈ (fun (x : Ortho d) => linearConj S.σ 1 x.toLinearEquiv) '' S.rotGroup := by
      exact Set.mem_image_of_mem (fun x => linearConj S.σ 1 x.toLinearEquiv) hR'
    rw [hc] at h1
    rcases h1 with ⟨Q, hQ, hQ_eq⟩
    exact ⟨Q, hQ, hQ_eq⟩
  have H2 (R' : Ortho d) (hR' : R' ∈ S.rotGroup) : ∃ Q ∈ S.rotGroup, Q.toLinearEquiv = linearConj S.σ (-1) R'.toLinearEquiv := by
    have hc := S.rotGroup_conj
    have h1 : R'.toLinearEquiv ∈ (fun (x : Ortho d) => x.toLinearEquiv) '' S.rotGroup := by
      exact Set.mem_image_of_mem (fun x => x.toLinearEquiv) hR'
    rw [← hc] at h1
    rcases h1 with ⟨Q, hQ, hQ_eq⟩
    refine ⟨Q, hQ, ?_⟩
    have heq : linearConj S.σ (-1) R'.toLinearEquiv = linearConj S.σ (-1) (linearConj S.σ 1 Q.toLinearEquiv) := by
      rw [← hQ_eq]
    rw [heq, linearConj_neg1_1]
  induction m using Int.induction_on with
  | zero =>
    rw [linearConj_zero]
    exact ⟨R, hR, rfl⟩
  | succ i hi =>
    rcases hi with ⟨Q, hQ, hQ_eq⟩
    have heq : (i : ℤ) + 1 = 1 + (i : ℤ) := add_comm _ _
    rw [heq, linearConj_add, ← hQ_eq]
    exact H1 Q hQ
  | pred i hi =>
    rcases hi with ⟨Q, hQ, hQ_eq⟩
    have heq2 : (-↑i - 1 : ℤ) = (-1 + -↑i : ℤ) := by omega
    have heq3 : linearConj S.σ (-↑i - 1 : ℤ) R.toLinearEquiv = linearConj S.σ (-1 + -↑i : ℤ) R.toLinearEquiv := by
      rw [heq2]
    rw [heq3, linearConj_add, ← hQ_eq]
    exact H2 Q hQ

/-- S6, V4 1.10(b): descendants in a node have orthogonal parts in `Q H`. -/
theorem descendant_frames (A : S.ι) (h depth : ℕ) (w : S.RoleWord A depth)
    (φ : Iso d) :
    ∃ R ∈ S.rotGroup,
      ((S.descendantNode A h depth w).move φ).frame.linearIsometryEquiv =
        φ.linearIsometryEquiv * R := by
  induction depth generalizing A h φ
  case zero =>
    use 1
    constructor
    · exact Subgroup.one_mem S.rotGroup
    · rfl
  case succ depth ih =>
    obtain ⟨w_head, w_tail⟩ := w
    obtain ⟨R, hR, ih_eq⟩ := ih (S.child A w_head).ty h w_tail ((S.placeChild (h + depth) w_head).trans φ)
    use S.childRotation (h + depth) w_head * R
    constructor
    · apply Subgroup.mul_mem S.rotGroup
      · apply S.rotGroup_spec.1
        exact ⟨h + depth, A, w_head, rfl⟩
      · exact hR
    · dsimp [descendantNode]
      have step1 : ((S.descendantNode (S.child A w_head).ty h depth w_tail).move (S.placeChild (h + depth) w_head)).move φ = (S.descendantNode (S.child A w_head).ty h depth w_tail).move ((S.placeChild (h + depth) w_head).trans φ) := rfl
      rw [step1, ih_eq]
      rfl

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

/-- V4 1.10(c), finiteness of the oriented sides: two functionals with the same
kernel define the same closed side, the opposite side, or (zero functional) everything. -/
private theorem oriented_orbits_finite_side_trichotomy (ℓ ℓ₀ : E d →ₗ[ℝ] ℝ)
    (h : LinearMap.ker ℓ = LinearMap.ker ℓ₀) :
    {x | 0 ≤ ℓ x} = Set.univ ∨ {x | 0 ≤ ℓ x} = {x | 0 ≤ ℓ₀ x} ∨
      {x | 0 ≤ ℓ x} = {x | ℓ₀ x ≤ 0} := by
  by_cases hz : ∀ v, ℓ₀ v = 0
  · left
    ext x
    have hx : x ∈ LinearMap.ker ℓ := by rw [h]; exact hz x
    simp [LinearMap.mem_ker.mp hx]
  · push_neg at hz
    obtain ⟨v, hv⟩ := hz
    set c : ℝ := ℓ v / ℓ₀ v with hc
    have hlin : ∀ x, ℓ x = c * ℓ₀ x := by
      intro x
      have hy : x - (ℓ₀ x / ℓ₀ v) • v ∈ LinearMap.ker ℓ₀ := by
        rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv, sub_self]
      rw [← h, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hy
      rw [hy, hc]
      field_simp
    rcases lt_trichotomy c 0 with hneg | hzero | hpos
    · right; right
      ext x
      simp only [Set.mem_setOf_eq, hlin]
      constructor
      · intro hx; by_contra hx'; push_neg at hx'; nlinarith
      · intro hx; nlinarith
    · left
      ext x
      simp [hlin, hzero]
    · right; left
      ext x
      simp only [Set.mem_setOf_eq, hlin]
      constructor
      · intro hx; by_contra hx'; push_neg at hx'; nlinarith
      · intro hx; positivity

/-- V4 1.10(c): "Π is the finite set ... for facets include the two oriented sides";
the prototype catalogue has finitely many oriented facet sides. -/
private theorem oriented_orbits_finite_sides_finite : S.facetSides.Finite := by
  let T : S.ι → Cell d → Set (Set (E d)) := fun _ e =>
    {K | ∃ ℓ : E d →ₗ[ℝ] ℝ, LinearMap.ker ℓ = cellDirection e.carrier ∧ K = {x | 0 ≤ ℓ x}}
  have hT : ∀ A e, (T A e).Finite := by
    intro A e
    by_cases hne : (T A e).Nonempty
    · obtain ⟨_, ℓ₀, hℓ₀, -⟩ := hne
      refine Set.Finite.subset (Set.toFinite ({Set.univ, {x | 0 ≤ ℓ₀ x}, {x | ℓ₀ x ≤ 0}} :
        Set (Set (E d)))) ?_
      rintro K ⟨ℓ, hℓ, rfl⟩
      rcases oriented_orbits_finite_side_trichotomy ℓ ℓ₀ (hℓ.trans hℓ₀.symm) with h1 | h1 | h1 <;>
        simp [h1]
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.finite_empty
  have hsub : S.facetSides ⊆ ⋃ A, ⋃ e ∈ ((S.cx A).facets : Set (Cell d)), T A e := by
    rintro K ⟨A, e, he, ℓ, hℓ, rfl⟩
    simp only [Set.mem_iUnion]
    exact ⟨A, e, he, ℓ, hℓ, rfl⟩
  refine Set.Finite.subset (Set.finite_iUnion fun A => ?_) hsub
  exact (Finset.finite_toSet _).biUnion fun e _ => hT A e

/-- V4 1.10(c), the transport of one side: "by (H5) σe is a union of placed cells
R_i e' + t_i; one of them has affine hull equal to aff σe, so σV = R_i V'"; the
expanded side of a prototype facet is a group image of a prototype side. -/
private theorem oriented_orbits_finite_side_transport {K : Set (E d)} (hK : K ∈ S.facetSides) :
    ∃ R ∈ S.rotGroup, ∃ K' ∈ S.facetSides, S.σ '' K = R '' K' := by
  obtain ⟨A, e, he, ℓ, hℓ, rfl⟩ := hK
  have he' : e ∈ (S.cx A).cells ∧ e.dim = d - 1 := by
    simpa [CellComplex.facets] using he
  have hd : 2 ≤ d := Fact.out
  obtain ⟨f, hf⟩ := S.heredity A e he'.1
  have hne : e.carrier.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hdim := e.flat.dimension
    rw [h, he'.2] at hdim
    rw [cellDirection, direction_affineSpan, vectorSpan_empty, finrank_bot] at hdim
    omega
  obtain ⟨x, hx⟩ := hne
  have hσx : S.σ x ∈ ⋃ q ∈ f, placedSet (S.child A q.1).frame q.2.val.carrier := by
    rw [← hf]; exact ⟨x, hx, rfl⟩
  simp only [Set.mem_iUnion] at hσx
  obtain ⟨q, hq, -⟩ := hσx
  obtain ⟨i, e', he'c, he'd⟩ := q
  set R : Ortho d := (S.child A i).rotation with hRdef
  set t : E d := (S.child A i).offset
  have hR : R ∈ S.rotGroup := by
    apply S.rotGroup_spec.1
    refine ⟨0, A, i, ?_⟩
    refine LinearIsometryEquiv.ext fun y => ?_
    change R y = linearConj S.σ ((0 : ℕ) : ℤ) R.toLinearEquiv y
    simp [linearConj]
  have hsub : placedSet (S.child A i).frame e'.carrier ⊆ S.σ '' e.carrier := by
    rw [hf]
    intro z hz
    exact Set.mem_iUnion₂.mpr ⟨_, hq, hz⟩
  let g : E d →ᵃ[ℝ] E d := R.toLinearEquiv.toLinearMap.toAffineMap + AffineMap.const ℝ (E d) t
  have hg : placedSet (S.child A i).frame e'.carrier = g '' e'.carrier := by
    apply Set.image_congr
    intro y _
    simp [g, Child.frame, rigidMotion, hRdef, t]
  have hgl : g.linear = R.toLinearEquiv.toLinearMap := by
    ext v
    simp [g]
  have hσimg : (cellDirection e.carrier).map S.σ.toLinearMap =
      cellDirection (S.σ '' e.carrier) := by
    simp only [cellDirection, direction_affineSpan]
    have := AffineMap.map_vectorSpan (k := ℝ) S.σ.toLinearMap.toAffineMap (s := e.carrier)
    simpa using this
  have hgimg : (cellDirection e'.carrier).map R.toLinearEquiv.toLinearMap =
      cellDirection (placedSet (S.child A i).frame e'.carrier) := by
    rw [hg]
    simp only [cellDirection, direction_affineSpan]
    rw [← hgl, AffineMap.map_vectorSpan]
  have hdir : (cellDirection e'.carrier).map R.toLinearEquiv.toLinearMap =
      (cellDirection e.carrier).map S.σ.toLinearMap := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [hgimg, hσimg]
      simp only [cellDirection, direction_affineSpan]
      exact vectorSpan_mono ℝ hsub
    · rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq, e'.flat.dimension,
        e.flat.dimension, he'd]
  let ℓ' : E d →ₗ[ℝ] ℝ := ℓ ∘ₗ (S.σ.symm.toLinearMap ∘ₗ R.toLinearEquiv.toLinearMap)
  refine ⟨R, hR, {y | 0 ≤ ℓ' y}, ⟨(S.child A i).ty, e', ?_, ℓ', ?_, rfl⟩, ?_⟩
  · simp only [CellComplex.facets, Finset.mem_filter]
    exact ⟨he'c, he'd.trans he'.2⟩
  · ext y
    have key : y ∈ cellDirection e'.carrier ↔ S.σ.symm (R y) ∈ cellDirection e.carrier := by
      rw [← Submodule.mem_map_equiv (e := S.σ)]
      change _ ↔ R y ∈ (cellDirection e.carrier).map S.σ.toLinearMap
      rw [← hdir]
      rw [Submodule.mem_map_equiv]
      simp
    rw [key, ← hℓ, LinearMap.mem_ker, LinearMap.mem_ker]
    simp [ℓ']
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨R.symm (S.σ y), ?_, by simp⟩
      simpa [ℓ'] using hy
    · rintro ⟨y, hy, rfl⟩
      refine ⟨S.σ.symm (R y), ?_, by simp⟩
      simpa [ℓ'] using hy

/-- V4 1.10(c): "σ(𝖧V) = (σ𝖧σ⁻¹)σV = 𝖧R_iV' = 𝖧V'", for oriented sides: the
expanded orbit of a prototype side is again a prototype side orbit. -/
private theorem oriented_orbits_finite_orbit_transport {K : Set (E d)} (hK : K ∈ S.facetSides) :
    ∃ K' ∈ S.facetSides, (fun C => S.σ '' C) '' S.sideOrbit K = S.sideOrbit K' := by
  obtain ⟨R, hR, K', hK', hσK⟩ := oriented_orbits_finite_side_transport S hK
  refine ⟨K', hK', ?_⟩
  have hconj : ∀ (Q : Ortho d) (C : Set (E d)),
      S.σ '' (Q '' C) = (fun y => linearConj S.σ 1 Q.toLinearEquiv y) '' (S.σ '' C) := by
    intro Q C
    rw [Set.image_image, Set.image_image]
    apply Set.image_congr
    intro y _
    simp [linearConj]
  ext C
  constructor
  · rintro ⟨_, ⟨Q, hQ, rfl⟩, rfl⟩
    obtain ⟨Q₁, hQ₁, hQeq⟩ : ∃ Q₁ ∈ S.rotGroup,
        linearConj S.σ 1 Q.toLinearEquiv = Q₁.toLinearEquiv := by
      have : linearConj S.σ 1 Q.toLinearEquiv ∈
          (fun R : Ortho d => R.toLinearEquiv) '' (S.rotGroup : Set (Ortho d)) := by
        rw [← S.rotGroup_conj]; exact ⟨Q, hQ, rfl⟩
      obtain ⟨Q₁, hQ₁, h⟩ := this
      exact ⟨Q₁, hQ₁, h.symm⟩
    refine ⟨Q₁ * R, S.rotGroup.mul_mem hQ₁ hR, ?_⟩
    change S.σ '' (Q '' K) = _
    rw [hconj, hQeq, hσK, Set.image_image]
    rfl
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨Q, hQ, hQeq⟩ : ∃ Q ∈ S.rotGroup,
        linearConj S.σ 1 Q.toLinearEquiv = (P * R⁻¹).toLinearEquiv := by
      have : (P * R⁻¹).toLinearEquiv ∈
          (fun R : Ortho d => linearConj S.σ 1 R.toLinearEquiv) '' (S.rotGroup : Set (Ortho d)) := by
        rw [S.rotGroup_conj]
        exact ⟨P * R⁻¹, S.rotGroup.mul_mem hP (S.rotGroup.inv_mem hR), rfl⟩
      obtain ⟨Q, hQ, h⟩ := this
      exact ⟨Q, hQ, h⟩
    refine ⟨Q '' K, ⟨Q, hQ, rfl⟩, ?_⟩
    change S.σ '' (Q '' K) = _
    rw [hconj, hQeq, hσK, Set.image_image]
    apply Set.image_congr
    intro y _
    change P (R⁻¹ (R y)) = P y
    congr 1
    exact LinearIsometryEquiv.symm_apply_apply R y

/-- S6, V4 1.10(c): the oriented supplement to `orbits_finite`.
There are finitely many prototype sides and finitely many group orbits, and `σ`
permutes those orbits with their orientations, as required for half-space cones. -/
theorem oriented_orbits_finite : S.facetSides.Finite ∧ S.facetSideOrbits.Finite ∧
    ∃ p : S.facetSideOrbits ≃ S.facetSideOrbits, ∀ O,
      (p O).val = (fun K => S.σ '' K) '' O.val := by
  have hfin := oriented_orbits_finite_sides_finite S
  have hOfin : S.facetSideOrbits.Finite := by
    refine (hfin.image S.sideOrbit).subset ?_
    rintro O ⟨K, hK, rfl⟩
    exact ⟨K, hK, rfl⟩
  refine ⟨hfin, hOfin, ?_⟩
  have hmem : ∀ O : S.facetSideOrbits, (fun K => S.σ '' K) '' O.val ∈ S.facetSideOrbits := by
    rintro ⟨O, K, hK, rfl⟩
    obtain ⟨K', hK', h⟩ := oriented_orbits_finite_orbit_transport S hK
    exact ⟨K', hK', h⟩
  let g : S.facetSideOrbits → S.facetSideOrbits := fun O => ⟨_, hmem O⟩
  have hσinj : Function.Injective (fun K : Set (E d) => S.σ '' K) :=
    Set.image_injective.mpr S.σ.injective
  have hginj : Function.Injective g := by
    intro O₁ O₂ h
    apply Subtype.ext
    exact Set.image_injective.mpr hσinj (congrArg Subtype.val h)
  haveI : Finite S.facetSideOrbits := hOfin.to_subtype
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hginj), fun O => rfl⟩

/-- Step 1 of the V4 proof of `one_child_runs` (V4 1.28): an isometric child frame
preserves volume, so the placed child prototype has the volume of the prototype. -/
private theorem one_child_runs_step1_placed_volume (R : Ortho d) (t : E d) (K : Set (E d)) :
    MeasureTheory.volume (placedSet (rigidMotion R t) K) = MeasureTheory.volume K := by
  have h1 : placedSet (rigidMotion R t) K = (fun x => x + t) '' (R '' K) := by
    ext x; simp [placedSet, rigidMotion, Set.image_image]
  have h2 : R '' K = R.symm ⁻¹' K := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨_, hx, by simp⟩
  rw [h1, Set.image_add_right, MeasureTheory.measure_preimage_add_right, h2]
  exact R.symm.measurePreserving.measure_preimage_emb R.symm.toHomeomorph.measurableEmbedding K

/-- Step 2 of the V4 proof of `one_child_runs` (V4 1.28): `|det σ| ≥ c^d > 1`. -/
private theorem one_child_runs_step2_det_gt_one :
    1 < |LinearMap.det (S.σ : E d →ₗ[ℝ] E d)| := by
  have hd : 2 ≤ d := Fact.out
  have hc := S.c_gt_one
  have hc0 : 0 ≤ S.c := by linarith
  haveI : Nontrivial (E d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hsub : Metric.ball (0 : E d) S.c ⊆ (S.σ : E d →ₗ[ℝ] E d) '' Metric.ball 0 1 := by
    intro y hy
    refine ⟨S.σ.symm y, ?_, by simp⟩
    rw [mem_ball_zero_iff] at hy ⊢
    have := S.expand (S.σ.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    by_contra h
    push_neg at h
    nlinarith
  have hm := MeasureTheory.measure_mono (μ := (MeasureTheory.volume : MeasureTheory.Measure (E d))) hsub
  rw [MeasureTheory.Measure.addHaar_image_linearMap, MeasureTheory.Measure.addHaar_ball _ _ hc0,
    finrank_euclideanSpace_fin] at hm
  have hB0 : MeasureTheory.volume (Metric.ball (0 : E d) 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hBt : MeasureTheory.volume (Metric.ball (0 : E d) 1) ≠ ⊤ :=
    MeasureTheory.measure_ball_lt_top.ne
  have hle : ENNReal.ofReal (S.c ^ d) ≤ ENNReal.ofReal |LinearMap.det (S.σ : E d →ₗ[ℝ] E d)| :=
    (ENNReal.mul_le_mul_iff_left hB0 hBt).mp hm
  rw [ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)] at hle
  have : 1 < S.c ^ d := one_lt_pow₀ hc (by omega)
  linarith

/-- Step 3 of the V4 proof of `one_child_runs` (V4 1.28): if `A'` is the unique child type
of `A`, then `vol A' = |det σ| vol A > vol A`. -/
private theorem one_child_runs_step3_volume_lt (A : S.ι) (j : S.I A)
    (h : Fintype.card (S.I A) = 1) :
    MeasureTheory.volume (S.proto A).carrier <
      MeasureTheory.volume (S.proto (S.child A j).ty).carrier := by
  have hall : ∀ k : S.I A, k = j := fun k =>
    Fintype.card_le_one_iff.mp (le_of_eq h) k j
  have hcov := S.children_cover A
  have hU : (⋃ k : S.I A, placedSet (S.child A k).frame (S.proto (S.child A k).ty).carrier) =
      placedSet (S.child A j).frame (S.proto (S.child A j).ty).carrier := by
    ext x; simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩; rw [hall k] at hk; exact hk
    · intro hx; exact ⟨j, hx⟩
  rw [hU] at hcov
  have hvol := congrArg (MeasureTheory.volume : Set (E d) → ENNReal) hcov
  have hσ : S.σ '' (S.proto A).carrier = (S.σ : E d →ₗ[ℝ] E d) '' (S.proto A).carrier := rfl
  rw [hσ, MeasureTheory.Measure.addHaar_image_linearMap, Child.frame,
    one_child_runs_step1_placed_volume] at hvol
  rw [← hvol]
  have h0 : MeasureTheory.volume (S.proto A).carrier ≠ 0 := by
    have := (S.proto A).interior_nonempty
    exact (lt_of_lt_of_le (isOpen_interior.measure_pos _ this)
      (MeasureTheory.measure_mono interior_subset)).ne'
  have ht : MeasureTheory.volume (S.proto A).carrier ≠ ⊤ := (S.proto A).compact.measure_lt_top.ne
  calc MeasureTheory.volume (S.proto A).carrier
      = 1 * MeasureTheory.volume (S.proto A).carrier := (one_mul _).symm
    _ < _ := (ENNReal.mul_lt_mul_iff_left h0 ht).mpr (by simpa using S.one_child_runs_step2_det_gt_one)

/-- C3, V4 1.28: a chain of one-child roles has at most `|ι|-1` steps.
The role data identify the actual successive child types; no acyclicity is assumed. -/
theorem one_child_runs (s : ℕ) (A : Fin (s + 1) → S.ι)
    (i : ∀ j : Fin s, S.I (A j.castSucc))
    (hunique : ∀ j : Fin s, Fintype.card (S.I (A j.castSucc)) = 1)
    (hchild : ∀ j : Fin s, (S.child (A j.castSucc) (i j)).ty = A j.succ) :
    s ≤ Fintype.card S.ι - 1 := by
  have hmono : StrictMono (fun j => MeasureTheory.volume (S.proto (A j)).carrier) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro j
    have := S.one_child_runs_step3_volume_lt (A j.castSucc) (i j) (hunique j)
    simp only [hchild j] at this
    exact this
  have hinj : Function.Injective A := fun a b hab => hmono.injective (by simp only [hab])
  have := Fintype.card_le_of_injective A hinj
  simp only [Fintype.card_fin] at this
  omega

private theorem I_nonempty (A : S.ι) : Nonempty (S.I A) := by
  obtain ⟨x, hx⟩ := (S.proto A).interior_nonempty
  have h : S.σ x ∈ S.σ '' (S.proto A).carrier := ⟨x, interior_subset hx, rfl⟩
  rw [S.children_cover A] at h
  obtain ⟨i, -⟩ := Set.mem_iUnion.mp h
  exact ⟨i⟩

private theorem nativeTile_ty_zero (A : S.ι) (w : S.RoleWord A 0) :
    (S.nativeTile A 0 w).ty = A := rfl

private theorem nativeTile_ty_succ (A : S.ι) (n : ℕ) (i : S.I A) (w : S.RoleWord (S.child A i).ty n) :
    (S.nativeTile A (n+1) ⟨i, w⟩).ty = (S.nativeTile (S.child A i).ty n w).ty := rfl

private theorem exists_one_child_chain (s : ℕ) : ∀ (A : S.ι),
    (∀ m < s, ∀ w : S.RoleWord A m, Fintype.card (S.I (S.nativeTile A m w).ty) = 1) →
    ∃ (T : ℕ → S.ι) (i : ∀ j, S.I (T j)),
      T 0 = A ∧ (∀ j < s, Fintype.card (S.I (T j)) = 1) ∧
      (∀ j < s, (S.child (T j) (i j)).ty = T (j+1)) := by
  induction s with
  | zero =>
    intro A _
    use (fun _ => A), (fun _ => Classical.choice (I_nonempty S A))
    refine ⟨rfl, fun j hj => by omega, fun j hj => by omega⟩
  | succ s ih =>
    intro A h
    have hcard : Fintype.card (S.I A) = 1 := by
      have H := h 0 (by omega) ()
      exact H
    obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.mp hcard
    let A' := (S.child A i0).ty
    have h' : ∀ m < s, ∀ w : S.RoleWord A' m, Fintype.card (S.I (S.nativeTile A' m w).ty) = 1 := by
      intro m hm w
      have H := h (m+1) (by omega) ⟨i0, w⟩
      exact H
    obtain ⟨T', i', hT'0, hT'card, hT'child⟩ := ih A' h'
    let T : ℕ → S.ι := fun j => match j with
      | 0 => A
      | j+1 => T' j
    let i : ∀ j, S.I (T j) := fun j => match j with
      | 0 => i0
      | j+1 => i' j
    use T, i
    refine ⟨rfl, ?_, ?_⟩
    · intro j hj
      cases j
      · exact hcard
      · exact hT'card _ (by omega)
    · intro j hj
      cases j
      · change (S.child A i0).ty = T' 0
        rw [hT'0]
      · change (S.child (T' _) (i' _)).ty = T' _
        exact hT'child _ (by omega)

private theorem exists_one_child_chain_Fin (s : ℕ) (A : S.ι)
    (h : ∀ m < s, ∀ w : S.RoleWord A m, Fintype.card (S.I (S.nativeTile A m w).ty) = 1) :
    ∃ (T : Fin (s+1) → S.ι) (i : ∀ j : Fin s, S.I (T j.castSucc)),
      T 0 = A ∧ (∀ j : Fin s, Fintype.card (S.I (T j.castSucc)) = 1) ∧
      (∀ j : Fin s, (S.child (T j.castSucc) (i j)).ty = T j.succ) := by
  obtain ⟨T', i', hT'0, hT'card, hT'child⟩ := exists_one_child_chain S s A h
  let T : Fin (s+1) → S.ι := fun j => T' j.val
  let i : ∀ j : Fin s, S.I (T j.castSucc) := fun j => i' j.val
  use T, i
  refine ⟨?_, ?_, ?_⟩
  · exact hT'0
  · intro j
    exact hT'card j.val j.isLt
  · intro j
    exact hT'child j.val j.isLt

/-- C3, V4 1.28: every type reaches a branching type within `|ι|-1` roles. -/
theorem reaches_branching (A : S.ι) :
    ∃ n ≤ Fintype.card S.ι - 1, ∃ w : S.RoleWord A n,
      2 ≤ Fintype.card (S.I (S.nativeTile A n w).ty) := by
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < Fintype.card S.ι := Fintype.card_pos_iff.mpr ⟨A⟩
  obtain ⟨T, i, hT0, hu, hc⟩ := exists_one_child_chain_Fin S (Fintype.card S.ι) A (fun m hm w => by
    have h1 := hcon m (by omega) w
    have h2 := Fintype.card_pos_iff.mpr (I_nonempty S (S.nativeTile A m w).ty)
    omega)
  have hc2 : ∀ j : Fin (Fintype.card S.ι), (S.child (T j.castSucc) (i j)).ty = T j.succ := hc
  have := S.one_child_runs (Fintype.card S.ι) T i hu hc
  omega

end SubstSystem

omit [Fact (2 ≤ d)] in
/-- Step 1 of the V4 proof of `h4_finite_test` (V4 7.5): "Cayley–Hamilton, applied to
`𝒜^m(I)`, gives `P_{m+s} + ∑_{j<s} c_j P_{m+j} = 0`".  In abstract form: for a linear
operator `A` on a space of dimension at most `s`, every Krylov vector `A^m v` lies in the
span of `v, A v, …, A^{s-1} v`. -/
private theorem h4_finite_test_step1_krylov {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (A : V →ₗ[ℝ] V) (v : V) (s : ℕ)
    (hs : Module.finrank ℝ V ≤ s) (m : ℕ) :
    (A ^ m) v ∈ Submodule.span ℝ (Set.range fun j : Fin s => (A ^ (j : ℕ)) v) := by
  classical
  have hp : A.charpoly.Monic := LinearMap.charpoly_monic A
  have hdeg : A.charpoly.natDegree = Module.finrank ℝ V := LinearMap.charpoly_natDegree A
  have hAm : A ^ m = Polynomial.aeval A ((Polynomial.X ^ m : Polynomial ℝ) %ₘ A.charpoly) := by
    have h0 := Polynomial.modByMonic_add_div (Polynomial.X ^ m : Polynomial ℝ) hp
    have h1 : Polynomial.aeval A (Polynomial.X ^ m : Polynomial ℝ) = A ^ m := by simp
    rw [← h1]
    conv_lhs => rw [← h0]
    rw [map_add, map_mul, LinearMap.aeval_self_charpoly, zero_mul, add_zero]
  by_cases hr : (Polynomial.X ^ m : Polynomial ℝ) %ₘ A.charpoly = 0
  · rw [hAm, hr, map_zero, LinearMap.zero_apply]
    exact zero_mem _
  · have hp1 : A.charpoly ≠ 1 := by
      intro h1
      exact hr (by rw [h1, Polynomial.modByMonic_one])
    have hlt : ((Polynomial.X ^ m : Polynomial ℝ) %ₘ A.charpoly).natDegree < s := by
      have := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ m : Polynomial ℝ) hp hp1
      omega
    rw [hAm, Polynomial.aeval_eq_sum_range' hlt, LinearMap.coe_sum, Finset.sum_apply]
    refine Submodule.sum_mem _ (fun i hi => ?_)
    rw [LinearMap.smul_apply]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩)

omit [Fact (2 ≤ d)] in
/-- Step 2 of the V4 proof of `h4_finite_test` (V4 7.5): "On the `s`-dimensional real space
`Sym_d` of symmetric matrices define `𝒜(X) = σᵀ X σ`, `P_m = 𝒜^m(I) = (σ^m)ᵀ σ^m`".
Here `Sym_d` is realized as a finite-dimensional space of (symmetric bilinear) forms on
`E d` of dimension at most `d(d+1)/2` (e.g. the forms `(x, y) ↦ ⟪x, M y⟫` with `M`
self-adjoint), `A` is the pullback `B ↦ B(σ ·, σ ·)` and `v` is the inner product, so that
the diagonal of `A^m v` is the quadratic form `x ↦ ‖σ^m x‖²`. -/
private theorem h4_finite_test_step2_sym_model (σ : E d ≃ₗ[ℝ] E d) :
    ∃ (V : Submodule ℝ (E d → E d → ℝ)) (_ : FiniteDimensional ℝ V) (A : V →ₗ[ℝ] V) (v : V),
      Module.finrank ℝ V ≤ d * (d + 1) / 2 ∧
        ∀ (m : ℕ) (x : E d), ((A ^ m) v : E d → E d → ℝ) x x = ‖(σ ^ m) x‖ ^ 2 := by
  classical
  -- the symmetric monomial forms `x_i y_j + x_j y_i`, indexed by unordered pairs
  let g : Sym2 (Fin d) → (E d → E d → ℝ) :=
    Sym2.lift ⟨fun i j => fun x y => x i * y j + x j * y i, by
      intro i j; funext x y; ring⟩
  have hg : ∀ i j : Fin d, g s(i, j) = fun x y => x i * y j + x j * y i := fun i j => rfl
  let V : Submodule ℝ (E d → E d → ℝ) := Submodule.span ℝ (Set.range g)
  -- the pullback `B ↦ B(σ ·, σ ·)`
  let P : (E d → E d → ℝ) →ₗ[ℝ] (E d → E d → ℝ) :=
    { toFun := fun B x y => B (σ x) (σ y)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hσ : ∀ (x : E d) (i : Fin d),
      (σ x) i = ∑ k, x k * (σ (EuclideanSpace.single k 1)) i := by
    intro x i
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
    simp [map_sum, map_smul]
  have hinv : ∀ B ∈ V, P B ∈ V := by
    intro B hB
    have hle : V ≤ V.comap P := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨z, rfl⟩
      induction z using Sym2.ind with
      | _ i j =>
        show P (g s(i, j)) ∈ V
        have heq : P (g s(i, j)) = ∑ k, ∑ l,
            ((σ (EuclideanSpace.single k 1)) i * (σ (EuclideanSpace.single l 1)) j) •
              g s(k, l) := by
          funext x y
          simp only [P, LinearMap.coe_mk, AddHom.coe_mk, hg, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul]
          rw [hσ x i, hσ y j, hσ x j, hσ y i, Finset.sum_mul_sum, Finset.sum_mul_sum]
          simp only [mul_add, Finset.sum_add_distrib]
          congr 1
          · refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
            ring
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
            ring
        rw [heq]
        exact Submodule.sum_mem _ (fun k _ => Submodule.sum_mem _ (fun l _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨s(k, l), rfl⟩)))
    exact hle hB
  have hv : (fun x y : E d => inner ℝ x y) ∈ V := by
    have heq : (fun x y : E d => inner ℝ x y) = ∑ i, (1 / 2 : ℝ) • g s(i, i) := by
      funext x y
      simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [heq]
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨s(i, i), rfl⟩))
  refine ⟨V, FiniteDimensional.span_of_finite ℝ (Set.finite_range g), P.restrict hinv,
    ⟨_, hv⟩, ?_, ?_⟩
  · have h1 := finrank_range_le_card (R := ℝ) g
    rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right] at h1
    have h2 : (d + 1) * (d + 1 - 1) / 2 = d * (d + 1) / 2 := by
      rw [Nat.add_sub_cancel, Nat.mul_comm]
    rw [h2] at h1
    exact h1
  · have hpow : ∀ m : ℕ, (((P.restrict hinv) ^ m) ⟨_, hv⟩ : E d → E d → ℝ) =
        fun x y => inner ℝ ((σ ^ m) x) ((σ ^ m) y) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, LinearMap.restrict_coe_apply, ih]
        rfl
    intro m x
    rw [hpow m]
    exact real_inner_self_eq_norm_sq _

omit [Fact (2 ≤ d)] in
/-- S7, V4 7.5: the finite test for all-power compatibility, independent of
any substitution system. The test uses exponents `1,...,d(d+1)/2-1`. -/
theorem h4_finite_test (σ : E d ≃ₗ[ℝ] E d) (R : Ortho d) :
    (∀ (m : ℕ) (x : E d), ‖linearConj σ (m : ℤ) R.toLinearEquiv x‖ = ‖x‖) ↔
      (∀ m : ℕ, 1 ≤ m → m < d * (d + 1) / 2 →
        ∀ x : E d, ‖linearConj σ (m : ℤ) R.toLinearEquiv x‖ = ‖x‖) := by
  have conj_apply : ∀ (j : ℕ) (y : E d),
      linearConj σ (j : ℤ) R.toLinearEquiv ((σ ^ j) y) = (σ ^ j) (R y) := by
    intro j y
    simp only [linearConj, zpow_neg, zpow_natCast]
    show (σ ^ j) (R ((σ ^ j).symm ((σ ^ j) y))) = (σ ^ j) (R y)
    rw [LinearEquiv.symm_apply_apply]
  constructor
  · intro h m _ _ x
    exact h m x
  · intro h m x
    -- the tests, rewritten as invariance of the quadratic forms `‖σ^j ·‖²`
    have hkey : ∀ j : ℕ, j < d * (d + 1) / 2 → ∀ y : E d,
        ‖(σ ^ j) (R y)‖ ^ 2 = ‖(σ ^ j) y‖ ^ 2 := by
      intro j hj y
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · simp
      · rw [← conj_apply j y, h j hpos hj]
    obtain ⟨V, hV, A, v, hdim, hev⟩ := h4_finite_test_step2_sym_model σ
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
      (h4_finite_test_step1_krylov A v _ hdim m)
    have hq : ∀ y : E d, ‖(σ ^ m) y‖ ^ 2 =
        ∑ i : Fin (d * (d + 1) / 2), c i * ‖(σ ^ (i : ℕ)) y‖ ^ 2 := by
      intro y
      rw [← hev m y, ← hc]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, hev]
    set y := (σ ^ (m : ℤ))⁻¹ x with hy
    have hx : x = (σ ^ m) y := by
      rw [hy, zpow_natCast]
      show x = (σ ^ m) ((σ ^ m).symm x)
      rw [LinearEquiv.apply_symm_apply]
    rw [hx, conj_apply]
    have h2 : ‖(σ ^ m) (R y)‖ ^ 2 = ‖(σ ^ m) y‖ ^ 2 := by
      rw [hq, hq]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hkey i i.isLt]
    have := congrArg Real.sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

end Enforce
