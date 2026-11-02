import Enforce.Source.Trace

/-!
# Incident forests, power factorisation, and finite headers

Compatible patches retain their actual frames, rather than choosing frames of physical
carriers. Cones in header tuples are direction cones at the origin. Translating an
apex to the origin before supplying the tuple gives exactly the notation of V4 1.17.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- P9, V4 1.14: a finite patch with specified compatible ground frames. -/
structure CompatiblePatch (S : SubstSystem d) where
  /-- P9, V4 1.14: the framed ground tiles. -/
  tiles : Finset (FramedNode S)
  /-- P9, V4 1.14: disjoint interiors of distinct patch members. -/
  disjoint : (tiles : Set (FramedNode S)).PairwiseDisjoint (fun t => interior (t.carrier 0))
  /-- P9, V4 1.14: every specified frame belongs to the compatible group. -/
  compatible : ∀ t ∈ tiles, t.frame.linearIsometryEquiv ∈ S.rotGroup

/-- P9, V4 1.14: conjugated frame under ambient expansion of a compatible tile. -/
def compatibleInflatedFrame (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (n : ℕ) : Iso d :=
  rigidMotion (Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
    t.frame.linearIsometryEquiv ht)) ((S.σ ^ n) (t.frame 0))

namespace CompatiblePatch

variable (P : CompatiblePatch S)

/-- P9, V4 1.14: addresses in the depth-`n` subdivision of the inflated patch. -/
abbrev Address (n : ℕ) := Σ t : {t // t ∈ P.tiles}, S.RoleWord t.val.ty n

/-- P9, V4 1.14: the native tile at an address of `σⁿ Π`. -/
def native (n : ℕ) (a : P.Address n) : FramedNode S :=
  (S.nativeTile a.1.val.ty n a.2).move
    (compatibleInflatedFrame a.1.val (P.compatible a.1.val a.1.property) n)

/-- P9, V4 1.14: every native frame is still compatible. -/
theorem native_compatible (n : ℕ) (a : P.Address n) :
    (P.native n a).frame.linearIsometryEquiv ∈ S.rotGroup := by
  dsimp [native, SubstSystem.nativeTile]
  obtain ⟨R, hR, h_eq⟩ := S.descendant_frames a.1.val.ty 0 n a.2 (compatibleInflatedFrame a.1.val (P.compatible a.1.val a.1.property) n)
  rw [h_eq]
  exact Subgroup.mul_mem S.rotGroup (Classical.choose_spec (S.rotGroup_conj_zpow (n : ℤ) a.1.val.frame.linearIsometryEquiv (P.compatible a.1.val a.1.property))).1 hR

/-- P9, V4 1.14: incident native tiles, with their unambiguous addresses. -/
abbrev Incident (p : E d) (n : ℕ) :=
  {a : P.Address n // (S.σ ^ n) p ∈ (P.native n a).carrier 0}

/-- P9, V4 1.14: the geometric child relation between consecutive inflated levels.
Containment in `σ t` determines the actual substitution parent. -/
def IncidentChild (p : E d) (n : ℕ) (a : P.Incident p n)
    (b : P.Incident p (n + 1)) : Prop :=
  (P.native (n + 1) b.val).carrier 0 ⊆ S.σ '' (P.native n a.val).carrier 0

/-- Step 1 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, "native tiles of
`σⁿΠ` are placed prototiles"): a ground carrier is the isometric image of its prototype. -/
private theorem incident_parent_exists_unique_step1_carrier_zero (t : FramedNode S) :
    t.carrier 0 = t.frame '' (S.proto t.ty).carrier := by
  simp [FramedNode.carrier, placedSet, SubstSystem.supertile]

/-- Step 1 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, Lemma 1.10 frames):
conjugated frames intertwine successive expansions. -/
private theorem incident_parent_exists_unique_step1_conjugate_succ
    (R : E d ≃ₗ[ℝ] E d) (n : ℕ) (x : E d) :
    linearConj S.σ ((n + 1 : ℕ) : ℤ) R (S.σ x) =
      S.σ (linearConj S.σ (n : ℤ) R x) := by
  have heq : linearConj S.σ ((n + 1 : ℕ) : ℤ) R * S.σ =
      S.σ * linearConj S.σ (n : ℤ) R := by
    simp only [linearConj, Nat.cast_add, Nat.cast_one]
    group
  exact congrArg (fun L : E d ≃ₗ[ℝ] E d => L x) heq

/-- Step 1 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, Lemma 1.10 frames):
the prescribed role frame has the same covariance. -/
private theorem incident_parent_exists_unique_step1_placeChild_succ
    {A : S.ι} (i : S.I A) (n : ℕ) (x : E d) :
    S.placeChild (n + 1) i (S.σ x) = S.σ (S.placeChild n i x) := by
  rw [S.placeChild_apply, S.placeChild_apply,
    incident_parent_exists_unique_step1_conjugate_succ, map_add, pow_succ']
  rfl

/-- Step 1 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, Lemma 1.10 frames):
at height zero the role frame is the prescribed child frame. -/
private theorem incident_parent_exists_unique_step1_placeChild_zero
    {A : S.ι} (i : S.I A) : S.placeChild 0 i = (S.child A i).frame := by
  apply AffineIsometryEquiv.ext
  intro x
  change linearConj S.σ (0 : ℤ) (S.child A i).rotation.toLinearEquiv x +
      (S.σ ^ 0) (S.child A i).offset =
    (S.child A i).rotation x + (S.child A i).offset
  simp [linearConj]

/-- Step 1 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, "split the finer
address"): a role word of length `n + 1` is a role word of length `n` followed by one
child role of its native tile, and the native tile of the longer word is that child
of the expanded shorter native tile. -/
private theorem incident_parent_exists_unique_step1_split (A : S.ι) (n : ℕ)
    (w : S.RoleWord A (n + 1)) :
    ∃ (v : S.RoleWord A n) (i : S.I (S.nativeTile A n v).ty),
      (S.nativeTile A (n + 1) w).ty = (S.child (S.nativeTile A n v).ty i).ty ∧
      ∀ x, (S.nativeTile A (n + 1) w).frame x =
        S.σ ((S.nativeTile A n v).frame
          (S.σ.symm ((S.child (S.nativeTile A n v).ty i).frame x))) := by
  induction n generalizing A with
  | zero =>
    refine ⟨(), w.1, rfl, fun x => ?_⟩
    change S.placeChild 0 w.1 x = S.σ (S.σ.symm ((S.child A w.1).frame x))
    rw [S.σ.apply_symm_apply, incident_parent_exists_unique_step1_placeChild_zero]
  | succ n ih =>
    obtain ⟨v, i, hty, hfr⟩ := ih (S.child A w.1).ty w.2
    refine ⟨⟨w.1, v⟩, i, hty, fun x => ?_⟩
    change S.placeChild (0 + (n + 1)) w.1
        ((S.nativeTile (S.child A w.1).ty (n + 1) w.2).frame x) =
      S.σ (S.placeChild (0 + n) w.1 ((S.nativeTile (S.child A w.1).ty n v).frame
        (S.σ.symm ((S.child (S.nativeTile (S.child A w.1).ty n v).ty i).frame x))))
    rw [Nat.zero_add, Nat.zero_add, hfr, incident_parent_exists_unique_step1_placeChild_succ]

/-- Step 2 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, Lemma 1.10):
the patch's specified ground frame obeys the same covariance under expansion. -/
private theorem incident_parent_exists_unique_step2_inflated_frame_succ
    (t : FramedNode S) (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup)
    (n : ℕ) (x : E d) :
    compatibleInflatedFrame t ht (n + 1) (S.σ x) =
      S.σ (compatibleInflatedFrame t ht n x) := by
  have hQ (n : ℕ) (x : E d) :
      (Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
        t.frame.linearIsometryEquiv ht)) x =
      linearConj S.σ (n : ℤ) t.frame.linearIsometryEquiv.toLinearEquiv x :=
    congrArg (fun L : E d ≃ₗ[ℝ] E d => L x)
      (Classical.choose_spec (S.rotGroup_conj_zpow (n : ℤ)
        t.frame.linearIsometryEquiv ht)).2
  change (Classical.choose (S.rotGroup_conj_zpow ((n + 1 : ℕ) : ℤ)
      t.frame.linearIsometryEquiv ht)) (S.σ x) + (S.σ ^ (n + 1)) (t.frame 0) =
    S.σ ((Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
      t.frame.linearIsometryEquiv ht)) x + (S.σ ^ n) (t.frame 0))
  rw [hQ, hQ, incident_parent_exists_unique_step1_conjugate_succ, map_add, pow_succ']
  rfl

/-- Step 2 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, "split the finer
address to obtain a parent"): every depth-`n+1` address of `σⁿ⁺¹Π` is a child, of some
role `i`, of a depth-`n` address, with the prescribed child frame. -/
private theorem incident_parent_exists_unique_step2_native_split (n : ℕ)
    (b : P.Address (n + 1)) :
    ∃ (a : P.Address n) (i : S.I (P.native n a).ty),
      (P.native (n + 1) b).ty = (S.child (P.native n a).ty i).ty ∧
      ∀ x, (P.native (n + 1) b).frame x =
        S.σ ((P.native n a).frame (S.σ.symm ((S.child (P.native n a).ty i).frame x))) := by
  obtain ⟨v, i, hty, hfr⟩ := incident_parent_exists_unique_step1_split b.1.val.ty n b.2
  refine ⟨⟨b.1, v⟩, i, hty, fun x => ?_⟩
  change compatibleInflatedFrame b.1.val (P.compatible _ b.1.property) (n + 1)
    ((S.nativeTile b.1.val.ty (n + 1) b.2).frame x) = _
  rw [hfr, incident_parent_exists_unique_step2_inflated_frame_succ]
  rfl

/-- Step 3 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, Proof: "the
children of `t` cover `σ t`"): every native tile of `σⁿ⁺¹Π` lies in `σ t` for a
native tile `t` of `σⁿΠ`. -/
private theorem incident_parent_exists_unique_step3_child_subset (n : ℕ)
    (b : P.Address (n + 1)) :
    ∃ a : P.Address n, (P.native (n + 1) b).carrier 0 ⊆ S.σ '' (P.native n a).carrier 0 := by
  obtain ⟨a, i, hty, hframe⟩ := incident_parent_exists_unique_step2_native_split P n b
  refine ⟨a, ?_⟩
  rw [incident_parent_exists_unique_step1_carrier_zero,
    incident_parent_exists_unique_step1_carrier_zero, hty]
  rintro z ⟨u, hu, rfl⟩
  have hu' : (S.child (P.native n a).ty i).frame u ∈
      S.σ '' (S.proto (P.native n a).ty).carrier := by
    rw [S.children_cover]
    exact Set.mem_iUnion.mpr ⟨i, ⟨u, hu, rfl⟩⟩
  obtain ⟨v, hv, hvu⟩ := hu'
  exact ⟨(P.native n a).frame v, Set.mem_image_of_mem _ hv,
    by rw [hframe, ← hvu, S.σ.symm_apply_apply]⟩

/-- Step 4 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, "disjoint
interiors"): a homeomorphism preserves disjointness of interiors. -/
private theorem incident_parent_exists_unique_step4_disjoint_homeo (e : E d ≃ₜ E d)
    {X Y : Set (E d)} (h : Disjoint (interior X) (interior Y)) :
    Disjoint (interior (e '' X)) (interior (e '' Y)) := by
  rw [← e.image_interior, ← e.image_interior]
  exact (Set.disjoint_image_iff e.injective).2 h

/-- Step 4 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, "disjoint
interiors"): a linear expansion preserves disjointness of interiors. -/
private theorem incident_parent_exists_unique_step4_disjoint_linear (L : E d ≃ₗ[ℝ] E d)
    {X Y : Set (E d)} (h : Disjoint (interior X) (interior Y)) :
    Disjoint (interior (L '' X)) (interior (L '' Y)) :=
  incident_parent_exists_unique_step4_disjoint_homeo L.toContinuousLinearEquiv.toHomeomorph h

/-- Step 4 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, "disjoint
interiors"): an isometry preserves disjointness of interiors. -/
private theorem incident_parent_exists_unique_step4_disjoint_iso (g : Iso d)
    {X Y : Set (E d)} (h : Disjoint (interior X) (interior Y)) :
    Disjoint (interior (g '' X)) (interior (g '' Y)) :=
  incident_parent_exists_unique_step4_disjoint_homeo g.toHomeomorph h

/-- Step 4 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, Lemma 1.10 frames):
the inflated patch frame intertwines `σⁿ` with the original ground frame. -/
private theorem incident_parent_exists_unique_step4_inflated_pow (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (n : ℕ) (x : E d) :
    compatibleInflatedFrame t ht n ((S.σ ^ n) x) = (S.σ ^ n) (t.frame x) := by
  induction n with
  | zero =>
    have hQ : (Classical.choose (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ)
        t.frame.linearIsometryEquiv ht)) x =
        linearConj S.σ ((0 : ℕ) : ℤ) t.frame.linearIsometryEquiv.toLinearEquiv x :=
      congrArg (fun L : E d ≃ₗ[ℝ] E d => L x)
        (Classical.choose_spec (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ)
          t.frame.linearIsometryEquiv ht)).2
    have hv := t.frame.map_vadd 0 x
    simp only [vadd_eq_add, add_zero] at hv
    change (Classical.choose (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ)
      t.frame.linearIsometryEquiv ht)) ((S.σ ^ 0) x) + (S.σ ^ 0) (t.frame 0) =
        (S.σ ^ 0) (t.frame x)
    simp only [pow_zero, LinearEquiv.coe_one, id_eq]
    rw [hQ, hv]
    simp [linearConj]
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      incident_parent_exists_unique_step2_inflated_frame_succ, ih]

/-- Step 4 of the V4 proof of `incident_parent_exists_unique` (V4 1.14): a native tile of
`σⁿΠ` lies in the inflation `σⁿ t` of its patch tile. -/
private theorem incident_parent_exists_unique_step4_native_subset (n : ℕ) (a : P.Address n) :
    (P.native n a).carrier 0 ⊆ (S.σ ^ n) '' a.1.val.carrier 0 := by
  rw [incident_parent_exists_unique_step1_carrier_zero,
    incident_parent_exists_unique_step1_carrier_zero]
  have hc : (S.nativeTile a.1.val.ty n a.2).frame ''
      (S.proto (S.nativeTile a.1.val.ty n a.2).ty).carrier ⊆
      (S.σ ^ n) '' (S.proto a.1.val.ty).carrier := by
    rw [← incident_parent_exists_unique_step1_carrier_zero]
    have := S.native_cover a.1.val.ty n
    change _ ⊆ S.supertile n _
    rw [← this]
    exact Set.subset_iUnion (fun w => (S.nativeTile a.1.val.ty n w).carrier 0) a.2
  change (compatibleInflatedFrame a.1.val (P.compatible a.1.val a.1.property) n) ∘
    (S.nativeTile a.1.val.ty n a.2).frame '' _ ⊆ _
  rw [Set.image_comp]
  refine (Set.image_mono hc).trans ?_
  rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨a.1.val.frame x, ⟨x, hx, rfl⟩,
    (incident_parent_exists_unique_step4_inflated_pow a.1.val _ n x).symm⟩

/-- Step 4 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, with Lemma 1.10):
the native tiles of `σⁿΠ` are "placed prototiles with disjoint interiors": distinct
depth-`n` addresses give native tiles with disjoint interiors. -/
private theorem incident_parent_exists_unique_step4_native_disjoint (n : ℕ) :
    Pairwise (fun a b : P.Address n => Disjoint
      (interior ((P.native n a).carrier 0)) (interior ((P.native n b).carrier 0))) := by
  rintro ⟨⟨t, ht⟩, w⟩ ⟨⟨t', ht'⟩, w'⟩ hne
  by_cases htt : t = t'
  · subst htt
    have hw : w ≠ w' := fun h => hne (h ▸ rfl)
    have himg : ∀ u : S.RoleWord t.ty n,
        (P.native n ⟨⟨t, ht⟩, u⟩).carrier 0 =
          compatibleInflatedFrame t (P.compatible t ht) n ''
            (S.nativeTile t.ty n u).carrier 0 := by
      intro u
      change (compatibleInflatedFrame t (P.compatible t ht) n) ∘
        (S.nativeTile t.ty n u).frame '' S.supertile 0 (S.nativeTile t.ty n u).ty = _
      rw [Set.image_comp]
      rfl
    rw [himg, himg]
    exact incident_parent_exists_unique_step4_disjoint_iso _ (S.native_disjoint t.ty n hw)
  · have h := P.disjoint ht ht' htt
    simp only [Function.onFun] at h
    exact (incident_parent_exists_unique_step4_disjoint_linear (S.σ ^ n) h).mono
      (interior_mono (incident_parent_exists_unique_step4_native_subset P n ⟨⟨t, ht⟩, w⟩))
      (interior_mono (incident_parent_exists_unique_step4_native_subset P n ⟨⟨t', ht'⟩, w'⟩))

/-- Step 5 of the V4 proof of `incident_parent_exists_unique` (V4 1.14, "nonempty tile
interior"): every ground carrier of a framed node has nonempty interior. -/
private theorem incident_parent_exists_unique_step5_interior_nonempty (t : FramedNode S) :
    (interior (t.carrier 0)).Nonempty := by
  have hi := t.frame.toHomeomorph.image_interior (S.proto t.ty).carrier
  change t.frame '' interior (S.proto t.ty).carrier =
    interior (t.frame '' (S.proto t.ty).carrier) at hi
  rw [incident_parent_exists_unique_step1_carrier_zero, ← hi]
  exact (S.proto t.ty).interior_nonempty.image _

/-- P9, V4 1.14: every incident native tile has a unique incident parent.
The original address prevents identifying distinct occurrences by a chosen frame. -/
theorem incident_parent_exists_unique (p : E d) (n : ℕ)
    (b : P.Incident p (n + 1)) :
    ∃! a : P.Incident p n, P.IncidentChild p n a b := by
  obtain ⟨a, ha⟩ := incident_parent_exists_unique_step3_child_subset P n b.val
  have hpa : (S.σ ^ n) p ∈ (P.native n a).carrier 0 := by
    obtain ⟨y, hy, hyp⟩ := ha b.property
    have hy' : y = (S.σ ^ n) p := by
      apply S.σ.injective
      rw [hyp, pow_succ']
      rfl
    exact hy' ▸ hy
  refine ⟨⟨a, hpa⟩, ha, ?_⟩
  intro a' ha'
  have ha'' : (P.native (n + 1) b.val).carrier 0 ⊆ S.σ '' (P.native n a'.val).carrier 0 := ha'
  apply Subtype.ext
  by_contra hne
  obtain ⟨x, hx⟩ := incident_parent_exists_unique_step5_interior_nonempty
    (P.native (n + 1) b.val)
  have hd := incident_parent_exists_unique_step4_disjoint_linear S.σ
    (incident_parent_exists_unique_step4_native_disjoint P n hne)
  exact Set.disjoint_left.mp hd (interior_mono ha'' hx) (interior_mono ha hx)

/-- P9, V4 1.14: the incident-forest parent chosen from unique existence. -/
def incidentParent (p : E d) (n : ℕ) (b : P.Incident p (n + 1)) : P.Incident p n :=
  Classical.choose (P.incident_parent_exists_unique p n b)

/-- P9, V4 1.14: specification of the incident parent. -/
theorem incidentParent_spec (p : E d) (n : ℕ) (b : P.Incident p (n + 1)) :
    P.IncidentChild p n (P.incidentParent p n b) b :=
  (Classical.choose_spec (P.incident_parent_exists_unique p n b)).1

/-- P9, V4 1.14: a tail after level `N`, retaining all actual incident tiles. -/
structure IncidentTail (p : E d) (N : ℕ) where
  /-- P9, V4 1.14: the successive incident addresses. -/
  node : ∀ r : ℕ, P.Incident p (N + r)
  /-- P9, V4 1.14: successive nodes are geometric substitution children. -/
  step : ∀ r, (P.native (N + (r + 1)) (node (r + 1)).val).carrier 0 ⊆
    S.σ '' (P.native (N + r) (node r).val).carrier 0

/-- Step 2 of the V4 proof of `incidentForest` (V4 1.14, Proof: "the children of `t`"):
conjugated frames intertwine successive expansions. -/
private theorem incidentForest_step2_conjugate_succ
    (R : E d ≃ₗ[ℝ] E d) (n : ℕ) (x : E d) :
    linearConj S.σ ((n + 1 : ℕ) : ℤ) R (S.σ x) =
      S.σ (linearConj S.σ (n : ℤ) R x) := by
  have heq : linearConj S.σ ((n + 1 : ℕ) : ℤ) R * S.σ =
      S.σ * linearConj S.σ (n : ℤ) R := by
    simp only [linearConj, Nat.cast_add, Nat.cast_one]
    group
  exact congrArg (fun L : E d ≃ₗ[ℝ] E d => L x) heq

/-- Step 2 of the V4 proof of `incidentForest` (V4 1.14, Proof: "the children of `t`"):
the prescribed role frame has the same covariance. -/
private theorem incidentForest_step2_placeChild_succ
    {A : S.ι} (i : S.I A) (n : ℕ) (x : E d) :
    S.placeChild (n + 1) i (S.σ x) = S.σ (S.placeChild n i x) := by
  rw [S.placeChild_apply, S.placeChild_apply,
    incidentForest_step2_conjugate_succ, map_add, pow_succ']
  rfl

/-- Step 2 of the V4 proof of `incidentForest` (V4 1.14, Proof: "the children of `t`"):
at height zero the role frame is the prescribed child frame. -/
private theorem incidentForest_step2_placeChild_zero
    {A : S.ι} (i : S.I A) : S.placeChild 0 i = (S.child A i).frame := by
  apply AffineIsometryEquiv.ext
  intro x
  change linearConj S.σ (0 : ℤ) (S.child A i).rotation.toLinearEquiv x +
      (S.σ ^ 0) (S.child A i).offset =
    (S.child A i).rotation x + (S.child A i).offset
  simp [linearConj]

/-- Step 2 of the V4 proof of `incidentForest` (V4 1.14, Proof: "the children of `t`"):
append a child role to a native address (depth-`n+1` descendants). -/
private def incidentForest_step2_append (S : SubstSystem d) :
    (A : S.ι) → (n : ℕ) → (w : S.RoleWord A n) →
      S.I (S.nativeTile A n w).ty → S.RoleWord A (n + 1)
  | A, 0, _, i => ⟨i, ()⟩
  | A, n + 1, w, i => ⟨w.1,
      incidentForest_step2_append S (S.child A w.1).ty n w.2 i⟩

/-- Step 2 of the V4 proof of `incidentForest` (V4 1.14, Proof: "the children of `t`"):
appending a role retains its prescribed child type. -/
private theorem incidentForest_step2_append_type
    (A : S.ι) (n : ℕ) (w : S.RoleWord A n) (i : S.I (S.nativeTile A n w).ty) :
    (S.nativeTile A (n + 1) (incidentForest_step2_append S A n w i)).ty =
      (S.child (S.nativeTile A n w).ty i).ty := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih => exact ih (S.child A w.1).ty w.2 i

/-- Step 2 of the V4 proof of `incidentForest` (V4 1.14, Proof: "the children of `t`"):
appending a role realizes subdivision after inflation. -/
private theorem incidentForest_step2_append_frame
    (A : S.ι) (n : ℕ) (w : S.RoleWord A n) (i : S.I (S.nativeTile A n w).ty)
    (x : E d) :
    (S.nativeTile A (n + 1) (incidentForest_step2_append S A n w i)).frame x =
      S.σ ((S.nativeTile A n w).frame (S.σ.symm ((S.child (S.nativeTile A n w).ty i).frame x))) := by
  induction n generalizing A with
  | zero =>
    change S.placeChild 0 i x = S.σ (S.σ.symm ((S.child A i).frame x))
    rw [S.σ.apply_symm_apply, incidentForest_step2_placeChild_zero]
    rfl
  | succ n ih =>
    change S.placeChild (0 + (n + 1)) w.1
      ((S.nativeTile (S.child A w.1).ty (n + 1)
        (incidentForest_step2_append S (S.child A w.1).ty n w.2 i)).frame x) =
      S.σ (S.placeChild (0 + n) w.1 ((S.nativeTile (S.child A w.1).ty n w.2).frame
        (S.σ.symm ((S.child (S.nativeTile (S.child A w.1).ty n w.2).ty i).frame x))))
    simp only [Nat.zero_add]
    rw [ih, incidentForest_step2_placeChild_succ]

/-- Step 2 of the V4 proof of `incidentForest` (V4 1.14, Proof: "the children of `t`"):
the patch's specified ground frame obeys the same covariance. -/
private theorem incidentForest_step2_inflated_frame_succ
    (t : FramedNode S) (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup)
    (n : ℕ) (x : E d) :
    compatibleInflatedFrame t ht (n + 1) (S.σ x) =
      S.σ (compatibleInflatedFrame t ht n x) := by
  have hQ (n : ℕ) (x : E d) :
      (Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
        t.frame.linearIsometryEquiv ht)) x =
      linearConj S.σ (n : ℤ) t.frame.linearIsometryEquiv.toLinearEquiv x :=
    congrArg (fun L : E d ≃ₗ[ℝ] E d => L x)
      (Classical.choose_spec (S.rotGroup_conj_zpow (n : ℤ)
        t.frame.linearIsometryEquiv ht)).2
  change (Classical.choose (S.rotGroup_conj_zpow ((n + 1 : ℕ) : ℤ)
      t.frame.linearIsometryEquiv ht)) (S.σ x) + (S.σ ^ (n + 1)) (t.frame 0) =
    S.σ ((Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
      t.frame.linearIsometryEquiv ht)) x + (S.σ ^ n) (t.frame 0))
  rw [hQ, hQ, incidentForest_step2_conjugate_succ, map_add, pow_succ']
  rfl

/-- Step 1 of the V4 proof of `incidentForest` (V4 1.14): a ground carrier is the
isometric image of its prototype ("native tiles ... are placed prototiles"). -/
private theorem incidentForest_step1_carrier_zero (t : FramedNode S) :
    t.carrier 0 = t.frame '' (S.proto t.ty).carrier := by
  simp [FramedNode.carrier, placedSet, SubstSystem.supertile]

/-- Step 1 of the V4 proof of `incidentForest` (V4 1.14, "disjoint interiors"):
a homeomorphism preserves disjointness of interiors. -/
private theorem incidentForest_step1_disjoint_homeo (e : E d ≃ₜ E d) {X Y : Set (E d)}
    (h : Disjoint (interior X) (interior Y)) :
    Disjoint (interior (e '' X)) (interior (e '' Y)) := by
  rw [← e.image_interior, ← e.image_interior]
  exact (Set.disjoint_image_iff e.injective).2 h

/-- Step 1 of the V4 proof of `incidentForest` (V4 1.14, "disjoint interiors"):
the expansion `σⁿ` preserves disjointness of interiors. -/
private theorem incidentForest_step1_disjoint_linear (L : E d ≃ₗ[ℝ] E d) {X Y : Set (E d)}
    (h : Disjoint (interior X) (interior Y)) :
    Disjoint (interior (L '' X)) (interior (L '' Y)) :=
  incidentForest_step1_disjoint_homeo L.toContinuousLinearEquiv.toHomeomorph h

/-- Step 1 of the V4 proof of `incidentForest` (V4 1.14, "disjoint interiors"):
an isometry preserves disjointness of interiors. -/
private theorem incidentForest_step1_disjoint_iso (g : Iso d) {X Y : Set (E d)}
    (h : Disjoint (interior X) (interior Y)) :
    Disjoint (interior (g '' X)) (interior (g '' Y)) :=
  incidentForest_step1_disjoint_homeo g.toHomeomorph h

/-- Step 1 of the V4 proof of `incidentForest` (V4 1.14, Lemma 1.10 frames):
the height-`n` role frame intertwines `σⁿ` with the prescribed child frame. -/
private theorem incidentForest_step1_placeChild_pow {A : S.ι} (i : S.I A) (n : ℕ) (x : E d) :
    S.placeChild n i ((S.σ ^ n) x) = (S.σ ^ n) ((S.child A i).frame x) := by
  induction n with
  | zero => simp [incidentForest_step2_placeChild_zero]
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      incidentForest_step2_placeChild_succ, ih]

/-- Step 1 of the V4 proof of `incidentForest` (V4 1.14, Lemma 1.10 frames):
the inflated patch frame intertwines `σⁿ` with the original ground frame. -/
private theorem incidentForest_step1_inflated_pow (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (n : ℕ) (x : E d) :
    compatibleInflatedFrame t ht n ((S.σ ^ n) x) = (S.σ ^ n) (t.frame x) := by
  induction n with
  | zero =>
    have hQ : (Classical.choose (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ)
        t.frame.linearIsometryEquiv ht)) x =
        linearConj S.σ ((0 : ℕ) : ℤ) t.frame.linearIsometryEquiv.toLinearEquiv x :=
      congrArg (fun L : E d ≃ₗ[ℝ] E d => L x)
        (Classical.choose_spec (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ)
          t.frame.linearIsometryEquiv ht)).2
    have hv := t.frame.map_vadd 0 x
    simp only [vadd_eq_add, add_zero] at hv
    change (Classical.choose (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ)
      t.frame.linearIsometryEquiv ht)) ((S.σ ^ 0) x) + (S.σ ^ 0) (t.frame 0) =
        (S.σ ^ 0) (t.frame x)
    simp only [pow_zero, LinearEquiv.coe_one, id_eq]
    rw [hQ, hv]
    simp [linearConj]
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      incidentForest_step2_inflated_frame_succ, ih]

/-- Step 1 of the V4 proof of `incidentForest` (V4 1.14, with (H3)): native tiles of one
prototype at a fixed depth have pairwise disjoint interiors ("distinct roles have
disjoint child interiors", iterated). -/
private theorem incidentForest_step1_nativeTile_disjoint :
    ∀ (n : ℕ) (A : S.ι), Pairwise (fun w w' : S.RoleWord A n => Disjoint
      (interior ((S.nativeTile A n w).frame '' (S.proto (S.nativeTile A n w).ty).carrier))
      (interior ((S.nativeTile A n w').frame '' (S.proto (S.nativeTile A n w').ty).carrier)))
  | 0, A => fun w w' h => absurd (Subsingleton.elim (α := Unit) w w') h
  | n + 1, A => by
    rintro ⟨i, v⟩ ⟨j, v'⟩ hne
    have himg : ∀ (k : S.I A) (u : S.RoleWord (S.child A k).ty n),
        (S.nativeTile A (n + 1) ⟨k, u⟩).frame ''
            (S.proto (S.nativeTile A (n + 1) ⟨k, u⟩).ty).carrier =
          S.placeChild n k '' ((S.nativeTile (S.child A k).ty n u).frame ''
            (S.proto (S.nativeTile (S.child A k).ty n u).ty).carrier) := by
      intro k u
      change (S.placeChild (0 + n) k) ∘ (S.nativeTile (S.child A k).ty n u).frame '' _ = _
      rw [Nat.zero_add, Set.image_comp]
      rfl
    rw [himg, himg]
    by_cases hij : i = j
    · subst hij
      have hv : v ≠ v' := fun h => hne (h ▸ rfl)
      exact incidentForest_step1_disjoint_iso _
        (incidentForest_step1_nativeTile_disjoint n (S.child A i).ty hv)
    · have hsub : ∀ (k : S.I A) (u : S.RoleWord (S.child A k).ty n),
          S.placeChild n k '' ((S.nativeTile (S.child A k).ty n u).frame ''
            (S.proto (S.nativeTile (S.child A k).ty n u).ty).carrier) ⊆
          (S.σ ^ n) '' placedSet (S.child A k).frame (S.proto (S.child A k).ty).carrier := by
        intro k u
        have hc : (S.nativeTile (S.child A k).ty n u).frame ''
            (S.proto (S.nativeTile (S.child A k).ty n u).ty).carrier ⊆
            (S.σ ^ n) '' (S.proto (S.child A k).ty).carrier := by
          rw [← incidentForest_step1_carrier_zero]
          have := S.native_cover (S.child A k).ty n
          change _ ⊆ S.supertile n _
          rw [← this]
          exact Set.subset_iUnion (fun w => (S.nativeTile (S.child A k).ty n w).carrier 0) u
        refine (Set.image_mono hc).trans ?_
        rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨(S.child A k).frame x, ⟨x, hx, rfl⟩,
          (incidentForest_step1_placeChild_pow k n x).symm⟩
      exact (incidentForest_step1_disjoint_linear (S.σ ^ n)
        (S.children_disjoint A hij)).mono (interior_mono (hsub i v)) (interior_mono (hsub j v'))

/-- Step 1 of the V4 proof of `incidentForest` (V4 1.14): a native tile of `σⁿΠ` lies in
the inflation `σⁿ t` of its patch tile. -/
private theorem incidentForest_step1_native_subset (n : ℕ) (a : P.Address n) :
    (P.native n a).frame '' (S.proto (P.native n a).ty).carrier ⊆
      (S.σ ^ n) '' (a.1.val.frame '' (S.proto a.1.val.ty).carrier) := by
  have hc : (S.nativeTile a.1.val.ty n a.2).frame ''
      (S.proto (S.nativeTile a.1.val.ty n a.2).ty).carrier ⊆
      (S.σ ^ n) '' (S.proto a.1.val.ty).carrier := by
    rw [← incidentForest_step1_carrier_zero]
    have := S.native_cover a.1.val.ty n
    change _ ⊆ S.supertile n _
    rw [← this]
    exact Set.subset_iUnion (fun w => (S.nativeTile a.1.val.ty n w).carrier 0) a.2
  change (compatibleInflatedFrame a.1.val (P.compatible a.1.val a.1.property) n) ∘
    (S.nativeTile a.1.val.ty n a.2).frame '' _ ⊆ _
  rw [Set.image_comp]
  refine (Set.image_mono hc).trans ?_
  rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨a.1.val.frame x, ⟨x, hx, rfl⟩,
    (incidentForest_step1_inflated_pow a.1.val _ n x).symm⟩

/-- Step 1 of the V4 proof of `incidentForest` (V4 1.14, with Lemma 1.10): the native
tiles of `σⁿΠ` are "placed prototiles with disjoint interiors": distinct depth-`n`
addresses of the compatible patch give native tiles with disjoint interiors. -/
private theorem incidentForest_step1_native_disjoint (n : ℕ) :
    Pairwise (fun a b : P.Address n => Disjoint
      (interior (placedSet (P.native n a).frame (S.proto (P.native n a).ty).carrier))
      (interior (placedSet (P.native n b).frame (S.proto (P.native n b).ty).carrier))) := by
  rintro ⟨⟨t, ht⟩, w⟩ ⟨⟨t', ht'⟩, w'⟩ hne
  by_cases htt : t = t'
  · subst htt
    have hw : w ≠ w' := fun h => hne (h ▸ rfl)
    have himg : ∀ u : S.RoleWord t.ty n,
        placedSet (P.native n ⟨⟨t, ht⟩, u⟩).frame
            (S.proto (P.native n ⟨⟨t, ht⟩, u⟩).ty).carrier =
          compatibleInflatedFrame t (P.compatible t ht) n ''
            ((S.nativeTile t.ty n u).frame '' (S.proto (S.nativeTile t.ty n u).ty).carrier) := by
      intro u
      change (compatibleInflatedFrame t (P.compatible t ht) n) ∘
        (S.nativeTile t.ty n u).frame '' _ = _
      rw [Set.image_comp]
      rfl
    rw [himg, himg]
    exact incidentForest_step1_disjoint_iso _ (incidentForest_step1_nativeTile_disjoint n t.ty hw)
  · have h := P.disjoint ht ht' htt
    simp only [Function.onFun, incidentForest_step1_carrier_zero] at h
    exact (incidentForest_step1_disjoint_linear (S.σ ^ n) h).mono
      (interior_mono (incidentForest_step1_native_subset P n ⟨⟨t, ht⟩, w⟩))
      (interior_mono (incidentForest_step1_native_subset P n ⟨⟨t', ht'⟩, w'⟩))

/-- Step 1 of the V4 proof of `incidentForest` (V4 1.14): "`|I_n| ≤ M₀` (Lemma 1.0(b))",
the native tiles at depth `n` containing `σⁿ p` are finitely many and at most `M₀`. -/
private theorem incidentForest_step1_bound [Nonempty S.ι] (p : E d) (n : ℕ) :
    Finite (P.Incident p n) ∧
      Nat.card (P.Incident p n) ≤ multiplicityBound S.proto S.cx := by
  have hpc := point_count_le S.proto S.cx (fun a : P.Address n => (P.native n a).ty)
    (fun a => (P.native n a).frame) (incidentForest_step1_native_disjoint P n) ((S.σ ^ n) p)
  have hset : {a : P.Address n | (S.σ ^ n) p ∈
      placedSet (P.native n a).frame (S.proto (P.native n a).ty).carrier} =
      {a | (S.σ ^ n) p ∈ (P.native n a).carrier 0} := by
    ext a
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, incidentForest_step1_carrier_zero]
    rfl
  rw [hset] at hpc
  refine ⟨hpc.1.to_subtype, ?_⟩
  have h2 := hpc.2
  rw [← Nat.card_coe_set_eq] at h2
  exact h2

/-- Step 2 of the V4 proof of `incidentForest` (V4 1.14, Proof: "the children of `t`"):
the appended address is the native child with the prescribed child frame. -/
private theorem incidentForest_step2_native_child
    (n : ℕ) (a : P.Address n) (i : S.I (P.native n a).ty) :
    ∃ b : P.Address (n + 1),
      (P.native (n + 1) b).ty = (S.child (P.native n a).ty i).ty ∧
      ∀ x, (P.native (n + 1) b).frame x =
        S.σ ((P.native n a).frame (S.σ.symm ((S.child (P.native n a).ty i).frame x))) := by
  refine ⟨⟨a.1, incidentForest_step2_append S a.1.val.ty n a.2 i⟩,
    incidentForest_step2_append_type a.1.val.ty n a.2 i, ?_⟩
  intro x
  change compatibleInflatedFrame a.1.val (P.compatible _ a.1.property) (n + 1)
    ((S.nativeTile a.1.val.ty (n + 1)
      (incidentForest_step2_append S a.1.val.ty n a.2 i)).frame x) = _
  rw [incidentForest_step2_append_frame, incidentForest_step2_inflated_frame_succ]
  rfl

/-- Step 2 of the V4 proof of `incidentForest` (V4 1.14, Proof): "`σ^{n+1}p ∈ σ(t)`
for `t ∈ I_n` and the children of `t` cover `σ t`, so a child contains the point". -/
private theorem incidentForest_step2_child_exists (p : E d) (n : ℕ) (a : P.Incident p n) :
    ∃ b : P.Incident p (n + 1), P.IncidentChild p n a b := by
  have ha := a.property
  rw [incidentForest_step1_carrier_zero] at ha
  obtain ⟨x, hx, hxp⟩ := ha
  have hsx : S.σ x ∈ S.σ '' (S.proto (P.native n a.val).ty).carrier :=
    Set.mem_image_of_mem _ hx
  rw [S.children_cover] at hsx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hsx
  obtain ⟨y, hy, hyx⟩ := hi
  obtain ⟨b, hty, hframe⟩ := incidentForest_step2_native_child P n a.val i
  have hinc : (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b).carrier 0 := by
    rw [incidentForest_step1_carrier_zero, hty]
    refine ⟨y, hy, ?_⟩
    rw [hframe, hyx, S.σ.symm_apply_apply, hxp, pow_succ']
    rfl
  refine ⟨⟨b, hinc⟩, ?_⟩
  change (P.native (n + 1) b).carrier 0 ⊆ S.σ '' (P.native n a.val).carrier 0
  rw [incidentForest_step1_carrier_zero, incidentForest_step1_carrier_zero, hty]
  rintro z ⟨u, hu, rfl⟩
  have hu' : (S.child (P.native n a.val).ty i).frame u ∈
      S.σ '' (S.proto (P.native n a.val).ty).carrier := by
    rw [S.children_cover]
    exact Set.mem_iUnion.mpr ⟨i, ⟨u, hu, rfl⟩⟩
  obtain ⟨v, hv, hvu⟩ := hu'
  exact ⟨(P.native n a.val).frame v, Set.mem_image_of_mem _ hv,
    by rw [hframe, ← hvu, S.σ.symm_apply_apply]⟩

/-- P9, V4 1.14: bounded width, no dying branches, and eventual unique children.
DEVIATION: the exact minimum-angle constant uses the nonempty catalogue, as in D3. -/
theorem incidentForest [Nonempty S.ι] (p : E d) :
    (∀ n, Finite (P.Incident p n) ∧
      Nat.card (P.Incident p n) ≤ multiplicityBound S.proto S.cx) ∧
    (∀ n (a : P.Incident p n),
      ∃ b : P.Incident p (n + 1), P.IncidentChild p n a b) ∧
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ a : P.Incident p n,
      ∃! b : P.Incident p (n + 1), P.IncidentChild p n a b := by
  classical
  have h1 : ∀ n, Finite (P.Incident p n) ∧
      Nat.card (P.Incident p n) ≤ multiplicityBound S.proto S.cx :=
    fun n => incidentForest_step1_bound P p n
  have h2 : ∀ n (a : P.Incident p n), ∃ b : P.Incident p (n + 1), P.IncidentChild p n a b :=
    fun n a => incidentForest_step2_child_exists P p n a
  refine ⟨h1, h2, ?_⟩
  choose f hf using h2
  have hinj : ∀ n, Function.Injective (f n) := by
    intro n a a' h
    have hb := hf n a
    have hb' := hf n a'
    rw [h] at hb
    exact (P.incident_parent_exists_unique p n (f n a')).unique hb hb'
  haveI : ∀ n, Finite (P.Incident p n) := fun n => (h1 n).1
  have hmono : Monotone (fun n => Nat.card (P.Incident p n)) :=
    monotone_nat_of_le_succ fun n => Nat.card_le_card_of_injective (f n) (hinj n)
  have hbdd : BddAbove (Set.range fun n => Nat.card (P.Incident p n)) :=
    ⟨multiplicityBound S.proto S.cx, by rintro _ ⟨n, rfl⟩; exact (h1 n).2⟩
  obtain ⟨N, hN⟩ := Nat.sSup_mem (Set.range_nonempty _) hbdd
  refine ⟨N, fun n hn a => ⟨f n a, hf n a, fun b hb => ?_⟩⟩
  have hle : Nat.card (P.Incident p (n + 1)) ≤ Nat.card (P.Incident p n) := by
    have h3 : Nat.card (P.Incident p (n + 1)) ≤
        sSup (Set.range fun n => Nat.card (P.Incident p n)) := le_csSup hbdd ⟨n + 1, rfl⟩
    have h4 := hmono hn
    dsimp only at hN h4
    omega
  obtain ⟨a', rfl⟩ := ((hinj n).bijective_of_nat_card_le hle).2 b
  have := (P.incident_parent_exists_unique p n (f n a')).unique hb (hf n a')
  rw [this]

/-- P9, V4 1.14: beyond a splitting cutoff, tails are in bijection with the
incident tiles there, so there are at most `M₀` infinite tails.
DEVIATION: the exact `M₀` requires the nonempty angle catalogue, as in D3. -/
theorem incident_tails [Nonempty S.ι] (p : E d) :
    ∃ N : ℕ, Function.Bijective (fun t : P.IncidentTail p N => t.node 0) ∧
      Finite (P.IncidentTail p N) ∧
      Nat.card (P.IncidentTail p N) ≤ multiplicityBound S.proto S.cx := by
  classical
  obtain ⟨hbound, _, N, hN⟩ := P.incidentForest p
  let next (r : ℕ) (a : P.Incident p (N + r)) : P.Incident p (N + (r + 1)) :=
    Classical.choose (hN (N + r) (by omega) a)
  have hnext (r : ℕ) (a : P.Incident p (N + r)) :
      P.IncidentChild p (N + r) a (next r a) :=
    (Classical.choose_spec (hN (N + r) (by omega) a)).1
  let node (a : P.Incident p N) : ∀ r, P.Incident p (N + r) :=
    fun r => Nat.rec a (fun r b => next r b) r
  let tail (a : P.Incident p N) : P.IncidentTail p N :=
    ⟨node a, fun r => hnext r (node a r)⟩
  have hinj : Function.Injective (fun t : P.IncidentTail p N => t.node 0) := by
    intro t u h
    have hn : t.node = u.node := by
      funext r
      induction r with
      | zero => exact h
      | succ r ih =>
        exact (hN (N + r) (by omega) (t.node r)).unique (t.step r)
          (by rw [ih]; exact u.step r)
    cases t
    cases u
    dsimp only at hn
    cases hn
    rfl
  have hsurj : Function.Surjective (fun t : P.IncidentTail p N => t.node 0) :=
    fun a => ⟨tail a, rfl⟩
  haveI : Finite (P.Incident p N) := (hbound N).1
  haveI : Finite (P.IncidentTail p N) := Finite.of_injective _ hinj
  exact ⟨N, ⟨hinj, hsurj⟩, inferInstance,
    (Nat.card_le_card_of_injective _ hinj).trans (hbound N).2⟩

/-- P9/P5, V4 1.14, 1.5(b): common-listed points in the original patch. -/
def CommonListed (p : E d) : Prop :=
  ∀ t ∈ P.tiles, p ∈ t.carrier 0 → t.Lists 0 p

/-- P9, V4 1.14: listedness persists across every incident child step. -/
theorem incident_listed_step (p : E d) (n : ℕ) (a : P.Incident p n)
    (b : P.Incident p (n + 1)) (hab : P.IncidentChild p n a b)
    (ha : (P.native n a.val).Lists 0 ((S.σ ^ n) p)) :
    (P.native (n + 1) b.val).Lists 0 ((S.σ ^ (n + 1)) p) := by
  sorry

/-- Step 0 of the V4 proof of `incident_commonListed`: native identity at depth 0. -/
private lemma incident_commonListed_step0_native_zero_eq (a : P.Address 0) : P.native 0 a = a.1.val := by
  have H_frame : (P.native 0 a).frame = a.1.val.frame := by
    dsimp [CompatiblePatch.native, SubstSystem.nativeTile, SubstSystem.descendantNode, FramedNode.move]
    apply AffineIsometryEquiv.ext
    intro x
    dsimp [compatibleInflatedFrame]
    have hc := (Classical.choose_spec (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ) a.1.val.frame.linearIsometryEquiv (P.compatible a.1.val a.1.property))).2
    have hy := congrArg (fun e : E d ≃ₗ[ℝ] E d => e x) hc
    simp only [linearConj, Nat.cast_zero, zpow_zero, neg_zero, one_mul, mul_one] at hy
    have hdec : a.1.val.frame x = a.1.val.frame.linearIsometryEquiv x + a.1.val.frame 0 := by
      have h := a.1.val.frame.map_vadd (0 : E d) x
      rw [vadd_eq_add, add_zero, vadd_eq_add] at h
      exact h
    show (Classical.choose (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ) a.1.val.frame.linearIsometryEquiv (P.compatible a.1.val a.1.property))) ((S.σ ^ 0) x) + (S.σ ^ 0) (a.1.val.frame 0) = a.1.val.frame x
    rw [pow_zero]
    change (Classical.choose (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ) a.1.val.frame.linearIsometryEquiv (P.compatible a.1.val a.1.property))) x + (a.1.val.frame 0) = a.1.val.frame x
    rw [hdec]
    exact congrArg (· + a.1.val.frame 0) hy
  have H_ty : (P.native 0 a).ty = a.1.val.ty := rfl
  exact FramedNode.ext H_ty H_frame

/-- P9/P5, V4 1.14, 1.5(b): a common-listed point is listed at every depth. -/
theorem incident_commonListed (p : E d) (hp : P.CommonListed p)
    (n : ℕ) (a : P.Incident p n) : (P.native n a.val).Lists 0 ((S.σ ^ n) p) := by
  induction' n with n ih
  · have h0 : P.native 0 a.val = a.val.1.val := incident_commonListed_step0_native_zero_eq P a.val
    have h1 : (S.σ ^ 0) p = p := rfl
    have a_prop : p ∈ a.val.1.val.carrier 0 := by
      have h := a.property
      change p ∈ (P.native 0 a.val).carrier 0 at h
      rw [h0] at h
      exact h
    have h_listed := hp a.val.1.val a.val.1.property a_prop
    change (P.native 0 a.val).Lists 0 p
    rw [h0]
    exact h_listed
  · let a_parent := P.incidentParent p n a
    have h_parent_child := P.incidentParent_spec p n a
    have h_parent_listed := ih a_parent
    exact P.incident_listed_step p n a_parent a h_parent_child h_parent_listed

end CompatiblePatch

/-- P10, V4 1.15: every complex root of the characteristic polynomial is positive
real. This formulation allows Jordan blocks and imposes no self-adjointness. -/
def PositiveRealSpectrum (L : E d ≃ₗ[ℝ] E d) : Prop :=
  ∀ z : ℂ, (L.toLinearMap.charpoly.map (algebraMap ℝ ℂ)).IsRoot z →
    z.im = 0 ∧ 0 < z.re

/-- P10, V4 1.15: the full data of a power factorisation. -/
structure PowerFactorisation (S : SubstSystem d) where
  /-- P10, V4 1.15: positive integral exponent. -/
  power : ℕ
  /-- P10, V4 1.15: nonzero power. -/
  power_pos : 1 ≤ power
  /-- P10, V4 1.15: compatible orthogonal factor. -/
  R : Ortho d
  /-- P10, V4 1.15: membership in the closed compatible group. -/
  R_mem : R ∈ S.rotGroup
  /-- P10, V4 1.15: invertible positive-spectrum factor. -/
  L : E d ≃ₗ[ℝ] E d
  /-- P10, V4 1.15: equality of the actual linear maps. -/
  factor : S.σ ^ power = R.toLinearEquiv * L
  /-- P10, V4 1.15: normalization, as equality of sets of linear equivalences. -/
  normalizes : (fun h : Ortho d => L * h.toLinearEquiv * L⁻¹) ''
      (S.rotGroup : Set (Ortho d)) =
    (fun h : Ortho d => h.toLinearEquiv) '' (S.rotGroup : Set (Ortho d))
  /-- P10, V4 1.15: positive real spectrum without a diagonalizability assumption. -/
  positive : PositiveRealSpectrum L

namespace CompatiblePatch

variable (P : CompatiblePatch S)

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". Finitely many proper affine
subspaces have dense complement. -/
private theorem power_factorisation_aux_step10_dense_avoid
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : Type*} [Finite ι] (L : ι → AffineSubspace ℝ V) (hL : ∀ i, L i ≠ ⊤) :
    Dense (⋂ i, ((L i : Set V)ᶜ)) := by
  apply dense_iInter_of_isOpen (fun i => (L i).closed_of_finiteDimensional.isOpen_compl)
  intro i
  rw [← interior_eq_empty_iff_dense_compl]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have ht := isOpen_interior.affineSpan_eq_top (⟨x, hx⟩ : (interior (L i : Set V)).Nonempty)
  have hle : affineSpan ℝ (interior (L i : Set V)) ≤ L i :=
    affineSpan_le.mpr interior_subset
  rw [ht] at hle
  exact hL i (top_unique hle)

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". A segment from a point
outside an affine subspace avoids that subspace if its other endpoint
avoids the affine span of the subspace and the first point. -/
private theorem power_factorisation_aux_step10_segment_avoid
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : AffineSubspace ℝ V) (x z : V) (hx : x ∉ L)
    (hz : z ∉ affineSpan ℝ (insert x (L : Set V))) :
    Disjoint (segment ℝ x z) (L : Set V) := by
  apply Set.disjoint_left.mpr
  intro w hw hwL
  have hwline : w ∈ line[ℝ, x, z] :=
    (line[ℝ, x, z]).convex.segment_subset (left_mem_affineSpan_pair ℝ x z)
      (right_mem_affineSpan_pair ℝ x z) hw
  have hwx : w ≠ x := by rintro rfl; exact hx hwL
  have hline := affineSpan_pair_eq_of_right_mem_of_ne hwline hwx
  have hle : line[ℝ, x, w] ≤ affineSpan ℝ (insert x (L : Set V)) :=
    affineSpan_pair_le_of_mem_of_mem (mem_affineSpan ℝ (Set.mem_insert _ _))
      (mem_affineSpan ℝ (Set.mem_insert_of_mem _ hwL))
  rw [hline] at hle
  exact hz (hle (right_mem_affineSpan_pair ℝ x z))

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". Removing finitely many
affine subspaces of codimension at least two does not disconnect an
open convex set: two segments through a generic intermediate point suffice. -/
private theorem power_factorisation_aux_step10_avoid_connected
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : Type*} [Finite ι] (L : ι → AffineSubspace ℝ V)
    (hL : ∀ i, Module.finrank ℝ (L i).direction + 1 < Module.finrank ℝ V)
    (U : Set V) (hU : IsOpen U) (hc : Convex ℝ U) :
    IsPreconnected (U ∩ ⋂ i, (L i : Set V)ᶜ) := by
  apply isPreconnected_of_forall_pair
  rintro x ⟨hxU, hx⟩ y ⟨hyU, hy⟩
  let M : Bool × ι → AffineSubspace ℝ V := fun b =>
    affineSpan ℝ (insert (if b.1 then x else y) (L b.2 : Set V))
  have hM (b : Bool × ι) : M b ≠ ⊤ := by
    intro heq
    have hle := finrank_vectorSpan_insert_le (L b.2) (if b.1 then x else y)
    rw [← direction_affineSpan] at hle
    change Module.finrank ℝ (M b).direction ≤ Module.finrank ℝ (L b.2).direction + 1 at hle
    rw [heq, AffineSubspace.direction_top, finrank_top] at hle
    exact (hL b.2).not_ge hle
  obtain ⟨z, hz, hzU⟩ := (power_factorisation_aux_step10_dense_avoid M hM).exists_mem_open hU ⟨x, hxU⟩
  have hsx : segment ℝ x z ⊆ U ∩ ⋂ i, (L i : Set V)ᶜ := by
    intro w hw
    refine ⟨hc.segment_subset hxU hzU hw, Set.mem_iInter.mpr fun i => ?_⟩
    exact Set.disjoint_left.mp (power_factorisation_aux_step10_segment_avoid (L i) x z
      (Set.mem_iInter.mp hx i) (by simpa [M] using Set.mem_iInter.mp hz (true, i))) hw
  have hsy : segment ℝ y z ⊆ U ∩ ⋂ i, (L i : Set V)ᶜ := by
    intro w hw
    refine ⟨hc.segment_subset hyU hzU hw, Set.mem_iInter.mpr fun i => ?_⟩
    exact Set.disjoint_left.mp (power_factorisation_aux_step10_segment_avoid (L i) y z
      (Set.mem_iInter.mp hy i) (by simpa [M] using Set.mem_iInter.mp hz (false, i))) hw
  refine ⟨segment ℝ x z ∪ segment ℝ y z, Set.union_subset hsx hsy,
    Or.inl (left_mem_segment ℝ x z), Or.inr (left_mem_segment ℝ y z), ?_⟩
  exact (convex_segment (𝕜 := ℝ) x z).isPreconnected.union z
    (right_mem_segment ℝ x z) (right_mem_segment ℝ y z)
    (convex_segment (𝕜 := ℝ) y z).isPreconnected


/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". A boundary of a regular
closed set cannot locally lie in finitely many affine subspaces of
codimension at least two: the complement connects the inside to the outside. -/
private theorem power_factorisation_aux_step10_boundary_not_thin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : Set V) (hK : IsClosed K) (hreg : closure (interior K) = K)
    (p : V) (hp : p ∈ frontier K)
    {ι : Type*} [Finite ι] (L : ι → AffineSubspace ℝ V)
    (hL : ∀ i, Module.finrank ℝ (L i).direction + 1 < Module.finrank ℝ V)
    (r : ℝ) (hr : 0 < r) :
    ¬ frontier K ∩ ball p r ⊆ ⋃ i, (L i : Set V) := by
  intro hcover
  have hproper (i : ι) : L i ≠ ⊤ := by
    intro heq
    have h := hL i
    rw [heq, AffineSubspace.direction_top, finrank_top] at h
    omega
  have hdense := power_factorisation_aux_step10_dense_avoid L hproper
  have hxcl : p ∈ closure (interior K) := by
    rw [hreg]
    exact hK.frontier_subset hp
  have hycl : p ∈ closure Kᶜ := by
    rw [frontier_eq_closure_inter_closure] at hp
    exact hp.2
  obtain ⟨x, hx, hxU, hxK⟩ := hdense.exists_mem_open (isOpen_ball.inter isOpen_interior)
    (mem_closure_iff.mp hxcl (ball p r) isOpen_ball (mem_ball_self hr))
  obtain ⟨y, hy, hyU, hyK⟩ := hdense.exists_mem_open (isOpen_ball.inter hK.isOpen_compl)
    (mem_closure_iff.mp hycl (ball p r) isOpen_ball (mem_ball_self hr))
  have hsides : ball p r ∩ ⋂ i, (L i : Set V)ᶜ ⊆ interior K ∪ Kᶜ := by
    rintro z ⟨hzU, hz⟩
    by_cases hzK : z ∈ K
    · left
      by_contra hzi
      have hzf : z ∈ frontier K := by rw [hK.frontier_eq]; exact ⟨hzK, hzi⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ⟨hzf, hzU⟩)
      exact Set.mem_iInter.mp hz i hi
    · exact Or.inr hzK
  have hd : Disjoint (interior K) Kᶜ :=
    Set.disjoint_left.mpr fun z hz hzc => hzc (interior_subset hz)
  rcases (power_factorisation_aux_step10_avoid_connected L hL (ball p r)
      isOpen_ball (convex_ball p r)).subset_or_subset isOpen_interior hK.isOpen_compl hd hsides with h | h
  · exact hyK (interior_subset (h ⟨hyU, hy⟩))
  · exact h ⟨hxU, hx⟩ (interior_subset hxK)

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". In a finite closed covering
of a regular boundary by lower-dimensional pieces, the pieces of
codimension one already cover the whole boundary. -/
private theorem power_factorisation_aux_step10_boundary_facets
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : Set V) (hK : IsClosed K) (hreg : closure (interior K) = K)
    {ι : Type*} [Finite ι] (C : ι → Set V) (hC : ∀ i, IsClosed (C i))
    (hcover : frontier K ⊆ ⋃ i, C i)
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (C i)).direction < Module.finrank ℝ V)
    (p : V) (hp : p ∈ frontier K) :
    ∃ i, p ∈ C i ∧ Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 = Module.finrank ℝ V := by
  classical
  by_contra hn
  let J := {i : ι // Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 = Module.finrank ℝ V}
  let H : Set V := ⋃ i : J, C i.val
  have hH : IsClosed H := isClosed_iUnion_of_finite fun i : J => hC i.val
  have hpH : p ∈ Hᶜ := by
    intro hpH
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpH
    exact hn ⟨i.val, hi, i.property⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hH.isOpen_compl p hpH
  let I := {i : ι // Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 ≠ Module.finrank ℝ V}
  have hlow (i : I) : Module.finrank ℝ (affineSpan ℝ (C i.val)).direction + 1 < Module.finrank ℝ V := by
    have := hdim i.val
    have := i.property
    omega
  apply power_factorisation_aux_step10_boundary_not_thin K hK hreg p hp
    (fun i : I => affineSpan ℝ (C i.val)) hlow r hr
  rintro x ⟨hxK, hxball⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hxK)
  have hiI : Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 ≠ Module.finrank ℝ V := by
    intro heq
    exact hball hxball (Set.mem_iUnion.mpr ⟨⟨i, heq⟩, hi⟩)
  exact Set.mem_iUnion.mpr ⟨⟨i, hiI⟩, mem_affineSpan ℝ hi⟩


/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"facets of that cell". A set with nonempty intrinsic interior but empty
ambient interior has strictly smaller affine dimension than the ambient space. -/
private theorem power_factorisation_aux_step10_rank_lt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (C : Set V) (hi : (intrinsicInterior ℝ C).Nonempty) (he : interior C = ∅) :
    Module.finrank ℝ (affineSpan ℝ C).direction < Module.finrank ℝ V := by
  by_contra hn
  have hdir : (affineSpan ℝ C).direction = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by omega))
  have hne : (affineSpan ℝ C : Set V).Nonempty :=
    (hi.mono intrinsicInterior_subset).mono (subset_affineSpan ℝ C)
  have hs : affineSpan ℝ C = ⊤ := (AffineSubspace.direction_eq_top_iff_of_nonempty hne).mp hdir
  rw [intrinsicInterior, hs] at hi
  have hopen : IsOpenMap ((↑) : (⊤ : AffineSubspace ℝ V) → V) :=
    (show IsOpen ((⊤ : AffineSubspace ℝ V) : Set V) from isOpen_univ).isOpenMap_subtype_val
  have hsub := (hopen.image_interior_subset (((↑) : (⊤ : AffineSubspace ℝ V) → V) ⁻¹' C)).trans
    (interior_mono (Set.image_preimage_subset _ _))
  have hh := hi.mono hsub
  simpa [he] using hh

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"∂A is covered by its facets". Apply the boundary covering lemma to the
finite listed prototype cells. -/
private theorem power_factorisation_aux_step10_prototype_facets
    (A : PolyManifoldDomain d) (K : CellComplex A) (p : E d)
    (hp : p ∈ frontier A.carrier) :
    ∃ e ∈ K.cells, e.dim = d - 1 ∧ p ∈ e.carrier := by
  obtain ⟨e, he, hdim⟩ := power_factorisation_aux_step10_boundary_facets A.carrier
    A.compact.isClosed A.regularClosed (fun e : {e // e ∈ K.cells} => e.val.carrier)
    (fun e => e.val.flat.compact.isClosed) (by
      intro x hx
      rw [← K.carriers_cover] at hx
      obtain ⟨e, he, hx⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hx
      exact Set.mem_iUnion.mpr ⟨⟨e, he⟩, hx⟩)
    (fun e => by
      change Module.finrank ℝ (cellDirection e.val.carrier) < Module.finrank ℝ (E d)
      rw [e.val.flat.dimension]
      simpa using K.dim_lt e.val e.property) p hp
  refine ⟨e.val, e.property, ?_, he⟩
  change Module.finrank ℝ (cellDirection e.val.carrier) + 1 = Module.finrank ℝ (E d) at hdim
  rw [e.val.flat.dimension] at hdim
  have hh : e.val.dim + 1 = d := by simpa using hdim
  omega

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"the relative boundary of each cell is covered by the facets of that
cell". Work in its direction space, using an affine isometry from that
space onto its affine hull. -/
private theorem power_factorisation_aux_step10_cell_facets
    (A : PolyManifoldDomain d) (K : CellComplex A)
    (e : Cell d) (he : e ∈ K.cells) (p : E d) (hp : p ∈ relfrontier e.carrier) :
    ∃ f ∈ K.cells, f.dim + 1 = e.dim ∧ p ∈ f.carrier ∧ f.carrier ⊆ e.carrier := by
  classical
  let H := affineSpan ℝ e.carrier
  have hpe : p ∈ e.carrier := intrinsicFrontier_subset e.flat.compact.isClosed hp
  let q : H := ⟨p, mem_affineSpan ℝ hpe⟩
  letI : Nonempty H := ⟨q⟩
  let ψ : H.direction ≃ᵃⁱ[ℝ] H := AffineIsometryEquiv.vaddConst ℝ q
  let φ : H.direction →ᵃⁱ[ℝ] E d := H.subtypeₐᵢ.comp ψ.toAffineIsometry
  let C : Set H.direction := φ ⁻¹' e.carrier
  have himage (D : Set (E d)) (hD : D ⊆ H) : φ '' (φ ⁻¹' D) = D := by
    apply Set.image_preimage_eq_of_subset
    intro x hx
    exact ⟨ψ.symm ⟨x, hD hx⟩, by
      change (ψ (ψ.symm ⟨x, hD hx⟩) : E d) = x
      rw [ψ.apply_symm_apply]⟩
  have heH : e.carrier ⊆ H := subset_affineSpan ℝ e.carrier
  have hCimage : φ '' C = e.carrier := himage _ heH
  have hinter : φ '' interior C = relint e.carrier := by
    change (((↑) : H → E d) ∘ ψ.toHomeomorph) '' interior (ψ.toHomeomorph ⁻¹' (((↑) : H → E d) ⁻¹' e.carrier)) = _
    rw [Set.image_comp, ψ.toHomeomorph.image_interior, ψ.toHomeomorph.image_preimage]
    rfl
  have hfront : φ '' frontier C = relfrontier e.carrier := by
    change (((↑) : H → E d) ∘ ψ.toHomeomorph) '' frontier (ψ.toHomeomorph ⁻¹' (((↑) : H → E d) ⁻¹' e.carrier)) = _
    rw [Set.image_comp, ψ.toHomeomorph.image_frontier, ψ.toHomeomorph.image_preimage]
    rfl
  have hCclosed : IsClosed C := e.flat.compact.isClosed.preimage φ.continuous
  have hCreg : closure (interior C) = C := by
    apply φ.injective.image_injective
    rw [← φ.isometry.isClosedEmbedding.closure_image_eq, hinter, e.flat.regularClosed, hCimage]
  obtain ⟨b, hb, hboundary⟩ := K.boundary_union e he
  have hbsub (f : {f // f ∈ b}) : f.val.carrier ⊆ relfrontier e.carrier := by
    intro x hx
    rw [hboundary]
    exact Set.mem_iUnion.mpr ⟨f.val, Set.mem_iUnion.mpr ⟨f.property, hx⟩⟩
  have hbH (f : {f // f ∈ b}) : f.val.carrier ⊆ H :=
    (hbsub f).trans ((intrinsicFrontier_subset e.flat.compact.isClosed).trans heH)
  let D (f : {f // f ∈ b}) : Set H.direction := φ ⁻¹' f.val.carrier
  have hDfront (f : {f // f ∈ b}) : D f ⊆ frontier C := by
    intro x hx
    have hh := hbsub f hx
    rw [← hfront] at hh
    exact φ.injective.mem_set_image.mp hh
  have hDdim (f : {f // f ∈ b}) :
      Module.finrank ℝ (affineSpan ℝ (D f)).direction = f.val.dim := by
    have heq : (affineSpan ℝ f.val.carrier).direction =
        ((affineSpan ℝ (D f)).direction).map H.direction.subtype := by
      rw [← himage f.val.carrier (hbH f)]
      change (affineSpan ℝ (φ.toAffineMap '' D f)).direction = _
      rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
      rfl
    have hh := f.val.flat.dimension
    change Module.finrank ℝ (affineSpan ℝ f.val.carrier).direction = f.val.dim at hh
    rw [heq, Submodule.finrank_map_subtype_eq] at hh
    exact hh
  have hDlow (f : {f // f ∈ b}) :
      Module.finrank ℝ (affineSpan ℝ (D f)).direction < Module.finrank ℝ H.direction := by
    apply power_factorisation_aux_step10_rank_lt
    · have hh := f.val.flat.relint_nonempty
      change (intrinsicInterior ℝ f.val.carrier).Nonempty at hh
      rw [← himage f.val.carrier (hbH f), φ.image_intrinsicInterior, Set.image_nonempty] at hh
      exact hh
    · apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hh := interior_mono (hDfront f) hx
      simpa [interior_frontier hCclosed] using hh
  have hpC : ψ.symm q ∈ frontier C := by
    apply φ.injective.mem_set_image.mp
    rw [hfront]
    simpa [φ] using hp
  obtain ⟨f, hpf, hfdim⟩ := power_factorisation_aux_step10_boundary_facets C hCclosed hCreg D
    (fun f => f.val.flat.compact.isClosed.preimage φ.continuous) (by
      intro x hx
      have hh : φ x ∈ relfrontier e.carrier := hfront ▸ Set.mem_image_of_mem φ hx
      rw [hboundary] at hh
      obtain ⟨f, hf, hxf⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hh
      exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hxf⟩) hDlow (ψ.symm q) hpC
  refine ⟨f.val, hb f.property, ?_, ?_,
    (hbsub f).trans (intrinsicFrontier_subset e.flat.compact.isClosed)⟩
  · rw [hDdim] at hfdim
    exact hfdim.trans e.flat.dimension
  · change φ (ψ.symm q) ∈ f.val.carrier at hpf
    simpa [φ] using hpf


/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15):
"each still containing the vertex". A listed vertex in a positive-dimensional
listed cell lies in that cell's relative boundary, since listed relative
interiors are disjoint. -/
private theorem power_factorisation_aux_step10_vertex_boundary
    (A : PolyManifoldDomain d) (K : CellComplex A)
    (v : Cell d) (hv : v ∈ K.vertices) (p : E d) (hp : p ∈ v.carrier)
    (e : Cell d) (he : e ∈ K.cells) (hpe : p ∈ e.carrier) (hdim : 0 < e.dim) :
    p ∈ relfrontier e.carrier := by
  have hvdim : v.dim = 0 := (Finset.mem_filter.mp hv).2
  have hvK : v ∈ K.cells := (Finset.mem_filter.mp hv).1
  have hbot : cellDirection v.carrier = ⊥ :=
    Submodule.finrank_eq_zero.mp (v.flat.dimension.trans hvdim)
  have hsingle : v.carrier.Subsingleton := by
    apply (vectorSpan_eq_bot_iff_subsingleton ℝ).mp
    simpa only [cellDirection, direction_affineSpan] using hbot
  have hvp : v.carrier = {p} := hsingle.eq_singleton_of_mem hp
  have hpv : p ∈ relint v.carrier := by simp [relint, hvp]
  have hne : v ≠ e := by
    intro h
    have := h ▸ hvdim
    omega
  have hnot : p ∉ relint e.carrier := fun hh =>
    Set.disjoint_left.mp (K.relint_disjoint v hvK e he hne) hpv hh
  change p ∈ intrinsicFrontier ℝ e.carrier
  rw [← closure_diff_intrinsicInterior, e.flat.compact.isClosed.closure_eq]
  exact ⟨hpe, hnot⟩

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, used in 1.17):
"starting from a facet through the vertex one descends through incident
facets of facets". Reversing this descending sequence gives the complete
nested flag at the original listed vertex. -/
private theorem power_factorisation_aux_step10_prototype_flag
    (A : PolyManifoldDomain d) (K : CellComplex A)
    (v : Cell d) (hv : v ∈ K.vertices) (p : E d) (hp : p ∈ v.carrier) :
    ∃ f : CellFlag K, ∀ j, p ∈ (f.cell j).carrier := by
  classical
  have hpA : p ∈ frontier A.carrier := by
    rw [← K.carriers_cover]
    exact Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨(Finset.mem_filter.mp hv).1, hp⟩⟩
  obtain ⟨e, he, hdim, hpe⟩ := power_factorisation_aux_step10_prototype_facets A K p hpA
  let I := {e : Cell d // e ∈ K.cells ∧ p ∈ e.carrier}
  have hnext (e : I) (h : 0 < e.val.dim) :
      ∃ f : I, f.val.dim + 1 = e.val.dim ∧ f.val.carrier ⊆ e.val.carrier := by
    obtain ⟨f, hf, hfdim, hpf, hsub⟩ := power_factorisation_aux_step10_cell_facets A K e.val e.property.1 p
      (power_factorisation_aux_step10_vertex_boundary A K v hv p hp e.val e.property.1 e.property.2 h)
    exact ⟨⟨f, hf, hpf⟩, hfdim, hsub⟩
  let next (e : I) : I := if h : 0 < e.val.dim then (hnext e h).choose else e
  have next_dim (e : I) : (next e).val.dim = e.val.dim - 1 := by
    by_cases h : 0 < e.val.dim
    · have hh := (hnext e h).choose_spec.1
      simp only [next, dif_pos h]
      omega
    · have hh : e.val.dim = 0 := by omega
      simp [next, h, hh]
  have next_sub (e : I) : (next e).val.carrier ⊆ e.val.carrier := by
    by_cases h : 0 < e.val.dim
    · simpa only [next, dif_pos h] using (hnext e h).choose_spec.2
    · simp [next, h]
  let c (n : ℕ) : I := next^[n] ⟨e, he, hpe⟩
  have c_succ (n : ℕ) : c (n + 1) = next (c n) := Function.iterate_succ_apply' next n _
  have c_dim (n : ℕ) : (c n).val.dim = d - 1 - n := by
    induction n with
    | zero => simpa [c] using hdim
    | succ n ih => rw [c_succ, next_dim, ih]; omega
  have c_anti : Antitone (fun n => (c n).val.carrier) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [c_succ]
    exact next_sub (c n)
  let f : CellFlag K :=
    { cell := fun j => (c (d - 1 - j.val)).val
      mem := fun j => (c (d - 1 - j.val)).property.1
      dimension := fun j => by rw [c_dim]; omega
      nested := fun i j hij => c_anti (by have := i.isLt; have := j.isLt; omega) }
  exact ⟨f, fun j => (c (d - 1 - j.val)).property.2⟩

/-- Step 10 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, used in 1.17):
"the boundary complex of a polyhedral manifold has a full flag at every
vertex". This is only the initial flag, before any substitution is applied. -/
private theorem power_factorisation_aux_step10_vertex_flag
    (t : FramedNode S) (p : E d) (hp : t.Lists 0 p) :
    ∃ f : CellFlag (S.cx t.ty), ∀ j, p ∈ t.cell 0 (f.cell j) := by
  obtain ⟨v, hv, x, hx, hxp⟩ := hp
  obtain ⟨f, hf⟩ := power_factorisation_aux_step10_prototype_flag (S.proto t.ty) (S.cx t.ty) v hv x hx
  exact ⟨f, fun j => ⟨x, hf j, hxp⟩⟩


/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". Conjugated frames intertwine successive expansions. -/
private theorem power_factorisation_aux_step11_conjugate_succ
    (R : E d ≃ₗ[ℝ] E d) (n : ℕ) (x : E d) :
    linearConj S.σ ((n + 1 : ℕ) : ℤ) R (S.σ x) =
      S.σ (linearConj S.σ (n : ℤ) R x) := by
  have heq : linearConj S.σ ((n + 1 : ℕ) : ℤ) R * S.σ =
      S.σ * linearConj S.σ (n : ℤ) R := by
    simp only [linearConj, Nat.cast_add, Nat.cast_one]
    group
  exact congrArg (fun L : E d ≃ₗ[ℝ] E d => L x) heq

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". The prescribed role frame has the same covariance. -/
private theorem power_factorisation_aux_step11_placeChild_succ
    {A : S.ι} (i : S.I A) (n : ℕ) (x : E d) :
    S.placeChild (n + 1) i (S.σ x) = S.σ (S.placeChild n i x) := by
  rw [S.placeChild_apply, S.placeChild_apply,
    power_factorisation_aux_step11_conjugate_succ, map_add, pow_succ']
  rfl

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". At height zero the role frame is the prescribed child frame. -/
private theorem power_factorisation_aux_step11_placeChild_zero
    {A : S.ι} (i : S.I A) : S.placeChild 0 i = (S.child A i).frame := by
  apply AffineIsometryEquiv.ext
  intro x
  change linearConj S.σ (0 : ℤ) (S.child A i).rotation.toLinearEquiv x +
      (S.σ ^ 0) (S.child A i).offset =
    (S.child A i).rotation x + (S.child A i).offset
  simp [linearConj]

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". Append a child role to a native address,
leaving its original patch root fixed. -/
private def power_factorisation_aux_step11_append (S : SubstSystem d) :
    (A : S.ι) → (n : ℕ) → (w : S.RoleWord A n) →
      S.I (S.nativeTile A n w).ty → S.RoleWord A (n + 1)
  | A, 0, _, i => ⟨i, ()⟩
  | A, n + 1, w, i => ⟨w.1,
      power_factorisation_aux_step11_append S (S.child A w.1).ty n w.2 i⟩

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the child t_{n+1}". Appending a role retains its prescribed child type. -/
private theorem power_factorisation_aux_step11_append_type
    (A : S.ι) (n : ℕ) (w : S.RoleWord A n) (i : S.I (S.nativeTile A n w).ty) :
    (S.nativeTile A (n + 1) (power_factorisation_aux_step11_append S A n w i)).ty =
      (S.child (S.nativeTile A n w).ty i).ty := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih => exact ih (S.child A w.1).ty w.2 i

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". Appending a role realizes subdivision after
inflation, even though the native-address recursion reads roles from the root. -/
private theorem power_factorisation_aux_step11_append_frame
    (A : S.ι) (n : ℕ) (w : S.RoleWord A n) (i : S.I (S.nativeTile A n w).ty)
    (x : E d) :
    (S.nativeTile A (n + 1) (power_factorisation_aux_step11_append S A n w i)).frame x =
      S.σ ((S.nativeTile A n w).frame (S.σ.symm ((S.child (S.nativeTile A n w).ty i).frame x))) := by
  induction n generalizing A with
  | zero =>
    change S.placeChild 0 i x = S.σ (S.σ.symm ((S.child A i).frame x))
    rw [S.σ.apply_symm_apply, power_factorisation_aux_step11_placeChild_zero]
    rfl
  | succ n ih =>
    change S.placeChild (0 + (n + 1)) w.1
      ((S.nativeTile (S.child A w.1).ty (n + 1)
        (power_factorisation_aux_step11_append S (S.child A w.1).ty n w.2 i)).frame x) =
      S.σ (S.placeChild (0 + n) w.1 ((S.nativeTile (S.child A w.1).ty n w.2).frame
        (S.σ.symm ((S.child (S.nativeTile (S.child A w.1).ty n w.2).ty i).frame x))))
    simp only [Nat.zero_add]
    rw [ih, power_factorisation_aux_step11_placeChild_succ]

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". The patch's specified ground frame obeys the
same covariance as a substitution role frame. -/
private theorem power_factorisation_aux_step11_inflated_frame_succ
    (t : FramedNode S) (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup)
    (n : ℕ) (x : E d) :
    compatibleInflatedFrame t ht (n + 1) (S.σ x) =
      S.σ (compatibleInflatedFrame t ht n x) := by
  have hQ (n : ℕ) (x : E d) :
      (Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
        t.frame.linearIsometryEquiv ht)) x =
      linearConj S.σ (n : ℤ) t.frame.linearIsometryEquiv.toLinearEquiv x :=
    congrArg (fun L : E d ≃ₗ[ℝ] E d => L x)
      (Classical.choose_spec (S.rotGroup_conj_zpow (n : ℤ)
        t.frame.linearIsometryEquiv ht)).2
  change (Classical.choose (S.rotGroup_conj_zpow ((n + 1 : ℕ) : ℤ)
      t.frame.linearIsometryEquiv ht)) (S.σ x) + (S.σ ^ (n + 1)) (t.frame 0) =
    S.σ ((Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
      t.frame.linearIsometryEquiv ht)) x + (S.σ ^ n) (t.frame 0))
  rw [hQ, hQ, power_factorisation_aux_step11_conjugate_succ, map_add, pow_succ']
  rfl

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". The appended address uses exactly the actual
frame of the inflated patch tile followed by the prescribed child frame. -/
private theorem power_factorisation_aux_step11_native_child
    (P : CompatiblePatch S) (n : ℕ) (a : P.Address n) (i : S.I (P.native n a).ty) :
    ∃ b : P.Address (n + 1),
      (P.native (n + 1) b).ty = (S.child (P.native n a).ty i).ty ∧
      ∀ x, (P.native (n + 1) b).frame x =
        S.σ ((P.native n a).frame (S.σ.symm ((S.child (P.native n a).ty i).frame x))) := by
  refine ⟨⟨a.1, power_factorisation_aux_step11_append S a.1.val.ty n a.2 i⟩,
    power_factorisation_aux_step11_append_type a.1.val.ty n a.2 i, ?_⟩
  intro x
  change compatibleInflatedFrame a.1.val (P.compatible _ a.1.property) (n + 1)
    ((S.nativeTile a.1.val.ty (n + 1)
      (power_factorisation_aux_step11_append S a.1.val.ty n a.2 i)).frame x) = _
  rw [power_factorisation_aux_step11_append_frame, power_factorisation_aux_step11_inflated_frame_succ]
  rfl


/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"cells of t_n". A ground cell is placed directly by its tile frame. -/
private theorem power_factorisation_aux_step11_cell_zero (t : FramedNode S) (e : Cell d) :
    t.cell 0 e = t.frame '' e.carrier := rfl

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"cells of t_n". The ground carrier is the isometric prototype carrier. -/
private theorem power_factorisation_aux_step11_carrier_zero (t : FramedNode S) :
    t.carrier 0 = t.frame '' (S.proto t.ty).carrier := by
  simp [FramedNode.carrier, placedSet, SubstSystem.supertile]

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"cells of t_n". A listed cell is contained in its closed tile carrier. -/
private theorem power_factorisation_aux_step11_cell_subset (t : FramedNode S)
    (e : Cell d) (he : e ∈ (S.cx t.ty).cells) : t.cell 0 e ⊆ t.carrier 0 := by
  rw [power_factorisation_aux_step11_cell_zero, power_factorisation_aux_step11_carrier_zero]
  apply Set.image_mono
  intro x hx
  apply (S.proto t.ty).compact.isClosed.frontier_subset
  rw [← (S.cx t.ty).carriers_cover]
  exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he, hx⟩⟩

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"σ e is a union of placed j-cells of the children". An expanded incident
cell has an incident native child cell of the same dimension; its carrier
is contained in the expanded parent cell. No uniqueness is used in this step. -/
private theorem power_factorisation_aux_step11_refinement
    (P : CompatiblePatch S) (p : E d) (n : ℕ) (a : P.Incident p n)
    (e : CellName S (P.native n a.val).ty)
    (he : (S.σ ^ n) p ∈ (P.native n a.val).cell 0 e.val) :
    ∃ (b : P.Incident p (n + 1)) (f : CellName S (P.native (n + 1) b.val).ty),
      P.IncidentChild p n a b ∧ f.val.dim = e.val.dim ∧
      (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b.val).cell 0 f.val ∧
      (P.native (n + 1) b.val).cell 0 f.val ⊆
        S.σ '' (P.native n a.val).cell 0 e.val := by
  classical
  rw [power_factorisation_aux_step11_cell_zero] at he
  obtain ⟨x, hxe, hxp⟩ := he
  obtain ⟨c, hc⟩ := S.heredity (P.native n a.val).ty e.val e.property
  have hsx : S.σ x ∈ ⋃ q ∈ c, placedSet (S.child (P.native n a.val).ty q.1).frame q.2.val.carrier := by
    rw [← hc]
    exact Set.mem_image_of_mem S.σ hxe
  obtain ⟨q, hq, y, hy, hyx⟩ := by
    simpa only [Set.mem_iUnion, exists_prop, placedSet, Set.mem_image] using hsx
  obtain ⟨b, hty, hframe⟩ := power_factorisation_aux_step11_native_child P n a.val q.1
  have hmem : q.2.val ∈ (S.cx (P.native (n + 1) b).ty).cells := by
    rw [hty]
    exact q.2.property.1
  have hpoint : (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b).cell 0 q.2.val := by
    rw [power_factorisation_aux_step11_cell_zero]
    refine ⟨y, hy, ?_⟩
    rw [hframe, hyx, S.σ.symm_apply_apply, hxp, pow_succ']
    rfl
  have hinc : (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b).carrier 0 :=
    power_factorisation_aux_step11_cell_subset _ _ hmem hpoint
  have hsub : ∀ (K L : Set (E d)),
      (S.child (P.native n a.val).ty q.1).frame '' K ⊆ S.σ '' L →
      (P.native (n + 1) b).frame '' K ⊆ S.σ '' ((P.native n a.val).frame '' L) := by
    intro K L h z hz
    obtain ⟨u, hu, rfl⟩ := hz
    obtain ⟨v, hv, hvu⟩ := h (Set.mem_image_of_mem _ hu)
    refine ⟨(P.native n a.val).frame v, Set.mem_image_of_mem _ hv, ?_⟩
    rw [hframe, ← hvu, S.σ.symm_apply_apply]
  refine ⟨⟨b, hinc⟩, ⟨q.2.val, hmem⟩, ?_, q.2.property.2, hpoint, ?_⟩
  · change (P.native (n + 1) b).carrier 0 ⊆ S.σ '' (P.native n a.val).carrier 0
    rw [power_factorisation_aux_step11_carrier_zero, power_factorisation_aux_step11_carrier_zero, hty]
    apply hsub
    rw [S.children_cover]
    exact Set.subset_iUnion (fun i => placedSet (S.child (P.native n a.val).ty i).frame
      (S.proto (S.child (P.native n a.val).ty i).ty).carrier) q.1
  · rw [power_factorisation_aux_step11_cell_zero, power_factorisation_aux_step11_cell_zero]
    apply hsub
    rw [hc]
    intro z hz
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, hz⟩⟩

/-- Step 12 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.17):
"regarded as the tuple of its direction spaces". Taking directions of a
placed cell removes translation and retains the actual orthogonal frame. -/
private theorem power_factorisation_aux_step12_frame_direction
    (t : FramedNode S) (e : Cell d) :
    cellDirection (t.cell 0 e) =
      (cellDirection e.carrier).map t.frame.linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  change (affineSpan ℝ (t.frame.toAffineEquiv.toAffineMap '' e.carrier)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  rfl

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"its affine hull is σ aff e by dimension". Direction spaces commute
with every invertible linear map, including the anisotropic expansion. -/
private theorem power_factorisation_aux_step11_linear_direction
    (L : E d ≃ₗ[ℝ] E d) (K : Set (E d)) :
    cellDirection (L '' K) = (cellDirection K).map L.toLinearMap := by
  change (affineSpan ℝ (L.toAffineEquiv.toAffineMap '' K)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  rfl

/-- Step 11 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.15, Claim, used in 1.17):
"some j-cell ... contains [the vertex] and lies in σ e". Heredity at a
unique incident child preserves the direction of one listed cell.
The uniqueness hypothesis excludes branching, and the cell must contain the anchor. -/
private theorem power_factorisation_aux_step11_child_cell
    (P : CompatiblePatch S) (p : E d) (n : ℕ)
    (a : P.Incident p n) (b : P.Incident p (n + 1))
    (hab : P.IncidentChild p n a b)
    (hunique : ∀ b' : P.Incident p (n + 1), P.IncidentChild p n a b' → b' = b)
    (e : CellName S (P.native n a.val).ty)
    (he : (S.σ ^ n) p ∈ (P.native n a.val).cell 0 e.val) :
    ∃ f : CellName S (P.native (n + 1) b.val).ty,
      f.val.dim = e.val.dim ∧
      (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b.val).cell 0 f.val ∧
      cellDirection ((P.native (n + 1) b.val).cell 0 f.val) =
        (cellDirection ((P.native n a.val).cell 0 e.val)).map S.σ.toLinearMap := by
  obtain ⟨b', f, hb', hdim, hf, hsub⟩ := power_factorisation_aux_step11_refinement P p n a e he
  obtain rfl := hunique b' hb'
  refine ⟨f, hdim, hf, ?_⟩
  have hle := AffineSubspace.direction_le (affineSpan_mono ℝ hsub)
  change cellDirection ((P.native (n + 1) b'.val).cell 0 f.val) ≤
    cellDirection (S.σ '' (P.native n a.val).cell 0 e.val) at hle
  rw [power_factorisation_aux_step11_linear_direction] at hle
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [power_factorisation_aux_step12_frame_direction, power_factorisation_aux_step12_frame_direction]
  simp only [LinearEquiv.finrank_map_eq]
  exact f.val.flat.dimension.trans (hdim.trans e.val.flat.dimension.symm)


/-- Step 13 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.17):
"the Claim in the proof of 1.15 ... gives a native flag". Iterate the
single-cell transport along a nonbranching listing tail; the transported
cells need not be nested, but their direction spaces are a complete flag. -/
private theorem power_factorisation_aux_step13_tail_flag
    (P : CompatiblePatch S) (p : E d) (N : ℕ) (t : P.IncidentTail p N)
    (hunique : ∀ m (b : P.Incident p (N + m + 1)),
      P.IncidentChild p (N + m) (t.node m) b → b = t.node (m + 1))
    (hlisted : (P.native N (t.node 0).val).Lists 0 ((S.σ ^ N) p)) :
    ∃ V : ℕ → Submodule ℝ (E d),
      (∀ i ≤ d, Module.finrank ℝ (V i) = i) ∧
      (∀ i < d, V i ≤ V (i + 1)) ∧
      (∀ i ≤ d, V i ∈ S.hPi ∨ V i = ⊤) ∧
      ∀ m i, i ≤ d →
        ((V i).map (S.σ ^ m).toLinearMap).map
          (P.native (N + m) (t.node m).val).frame.linearIsometryEquiv.symm.toLinearEquiv.toLinearMap
          ∈ S.cellDirections ∪ {⊤} := by
  classical
  obtain ⟨f, hf⟩ := power_factorisation_aux_step10_vertex_flag _ _ hlisted
  let V (i : ℕ) : Submodule ℝ (E d) :=
    if hi : i < d then cellDirection ((P.native N (t.node 0).val).cell 0 (f.cell ⟨i, hi⟩))
    else ⊤
  have hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i := by
    intro i hi
    by_cases hid : i < d
    · rw [show V i = cellDirection ((P.native N (t.node 0).val).cell 0 (f.cell ⟨i, hid⟩))
          from dif_pos hid, power_factorisation_aux_step12_frame_direction, LinearEquiv.finrank_map_eq]
      exact (f.cell ⟨i, hid⟩).flat.dimension.trans (f.dimension ⟨i, hid⟩)
    · have heq : i = d := by omega
      rw [show V i = ⊤ from dif_neg hid]
      simp [heq]
  have hmono : ∀ i < d, V i ≤ V (i + 1) := by
    intro i hi
    by_cases hj : i + 1 < d
    · simp only [V, dif_pos hi, dif_pos hj, power_factorisation_aux_step12_frame_direction]
      apply Submodule.map_mono
      exact AffineSubspace.direction_le (affineSpan_mono ℝ
        (f.nested ⟨i, hi⟩ ⟨i + 1, hj⟩ (by simp)))
    · simp [V, hj]
  have hV : ∀ i ≤ d, V i ∈ S.hPi ∨ V i = ⊤ := by
    intro i hi
    by_cases hid : i < d
    · left
      refine ⟨cellDirection (f.cell ⟨i, hid⟩).carrier,
        ⟨(P.native N (t.node 0).val).ty, f.cell ⟨i, hid⟩, f.mem _, rfl⟩,
        (P.native N (t.node 0).val).frame.linearIsometryEquiv,
        P.native_compatible N (t.node 0).val, ?_⟩
      simp only [V, dif_pos hid, power_factorisation_aux_step12_frame_direction]
    · exact Or.inr (by simp [V, hid])
  have hcell (i : ℕ) (hi : i < d) : ∀ m : ℕ,
      ∃ e : CellName S (P.native (N + m) (t.node m).val).ty,
        (S.σ ^ (N + m)) p ∈ (P.native (N + m) (t.node m).val).cell 0 e.val ∧
        cellDirection ((P.native (N + m) (t.node m).val).cell 0 e.val) =
          (V i).map (S.σ ^ m).toLinearMap := by
    intro m
    induction m with
    | zero =>
      refine ⟨⟨f.cell ⟨i, hi⟩, f.mem _⟩, hf _, ?_⟩
      simp [V, hi]
    | succ m ih =>
      obtain ⟨e, he, hdir⟩ := ih
      obtain ⟨e', _, he', hdir'⟩ := power_factorisation_aux_step11_child_cell P p
        (N + m) (t.node m) (t.node (m + 1)) (t.step m) (hunique m) e he
      refine ⟨e', he', ?_⟩
      calc
        _ = (cellDirection ((P.native (N + m) (t.node m).val).cell 0 e.val)).map
            S.σ.toLinearMap := hdir'
        _ = _ := by
          rw [hdir, ← Submodule.map_comp]
          simp [pow_succ', LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp]
  refine ⟨V, hdim, hmono, hV, ?_⟩
  intro m i hi
  by_cases hid : i < d
  · obtain ⟨e, he, hdir⟩ := hcell i hid m
    rw [← hdir, power_factorisation_aux_step12_frame_direction, ← Submodule.map_comp]
    simp only [LinearIsometryEquiv.toLinearEquiv_symm, LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, Submodule.map_id]
    exact Or.inl ⟨(P.native (N + m) (t.node m).val).ty, e.val, e.property, rfl⟩
  · simp [V, hid, Submodule.map_top]

/-- Step 15 (copied for `power_factorisation`) of the V4 proof of `header_finiteness` (V4 1.17):
"beyond all branching". Starting at the unique-child cutoff, recursively
choose the unique children. Every later incident tile belongs to one of
these tails, indexed by the finite set of incident tiles at the cutoff. -/
private theorem power_factorisation_aux_step15_tail_cover
    (P : CompatiblePatch S) [Nonempty S.ι] (p : E d) :
    ∃ (N : ℕ) (t : P.Incident p N → P.IncidentTail p N),
      (∀ m, Function.Surjective (fun a => (t a).node m)) ∧
      ∀ n, N ≤ n → ∀ a : P.Incident p n,
        ∃! b : P.Incident p (n + 1), P.IncidentChild p n a b := by
  classical
  obtain ⟨_, _, N, hN⟩ := P.incidentForest p
  let next (m : ℕ) (a : P.Incident p (N + m)) : P.Incident p (N + (m + 1)) :=
    Classical.choose (hN (N + m) (by omega) a)
  have hnext (m : ℕ) (a : P.Incident p (N + m)) :
      P.IncidentChild p (N + m) a (next m a) :=
    (Classical.choose_spec (hN (N + m) (by omega) a)).1
  let node (a : P.Incident p N) : ∀ m, P.Incident p (N + m) :=
    fun m => Nat.rec a (fun m b => next m b) m
  let t (a : P.Incident p N) : P.IncidentTail p N :=
    ⟨node a, fun m => hnext m (node a m)⟩
  refine ⟨N, t, ?_, hN⟩
  intro m
  induction m with
  | zero => exact fun a => ⟨a, rfl⟩
  | succ m ih =>
    intro b
    let a := P.incidentParent p (N + m) b
    obtain ⟨a₀, ha₀⟩ := ih a
    refine ⟨a₀, ?_⟩
    change next m (node a₀ m) = b
    change node a₀ m = a at ha₀
    rw [ha₀]
    exact ExistsUnique.unique (hN (N + m) (by omega) a)
      (hnext m a) (P.incidentParent_spec p (N + m) b)

end CompatiblePatch

open scoped Topology in
/-- Copy of a step of the V4 proof of `packet_E_equality` (V4 3.12(b)), used for V4 1.15:
"we may take q a vertex". An extreme point in the relative interior of
one of the intersection's cells forces that cell to be a singleton. -/
private theorem power_factorisation_aux_extreme_cell (K L : Set (E d)) (hLK : L ⊆ K)
    (q : E d) (hq : q ∈ K.extremePoints ℝ) (hqL : q ∈ relint L) : L = {q} := by
  obtain ⟨q', hq', rfl⟩ := mem_intrinsicInterior.mp hqL
  have hqL : (q' : E d) ∈ L := (show q' ∈ Subtype.val ⁻¹' L from interior_subset hq')
  apply Set.Subset.antisymm
  · intro x hx
    let γ : ℝ → affineSpan ℝ L := fun t =>
      ⟨AffineMap.lineMap (q' : E d) x t,
        AffineMap.lineMap_mem t q'.property (subset_affineSpan ℝ L hx)⟩
    have hγ : Continuous γ := by fun_prop
    have hsmall : ∀ᶠ t : ℝ in 𝓝 0,
        (γ t : E d) ∈ L ∧ (γ (-t) : E d) ∈ L := by
      have h₁ : Filter.Tendsto γ (𝓝 0) (𝓝 q') := by
        simpa [γ] using hγ.tendsto 0
      have h₂ : Filter.Tendsto (fun t => γ (-t)) (𝓝 0) (𝓝 q') := by
        simpa [γ] using (hγ.comp continuous_neg).tendsto 0
      exact Filter.Eventually.and (h₁ (mem_interior_iff_mem_nhds.mp hq'))
        (h₂ (mem_interior_iff_mem_nhds.mp hq'))
    obtain ⟨ε, hε, hεL⟩ := Metric.eventually_nhds_iff.mp hsmall
    let t := ε / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have htε : dist t 0 < ε := by simp [t, abs_of_pos hε]; linarith
    obtain ⟨hplus, hminus⟩ := hεL htε
    have hseg : (q' : E d) ∈ openSegment ℝ (γ t : E d) (γ (-t) : E d) := by
      refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
      simp only [γ, AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
      module
    have hplus_eq : (γ t : E d) = (q' : E d) := hq.2 (hLK hplus) (hLK hminus) hseg
    have hzero : t • (x - (q' : E d)) = 0 := by
      simpa [γ, AffineMap.lineMap_apply] using hplus_eq
    have hxeq : x = (q' : E d) := sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left ht.ne')
    exact Set.mem_singleton_iff.mpr hxeq
  · exact singleton_subset_iff.mpr hqL

/-- Step 1 of the V4 proof of `power_factorisation` (V4 1.15): "take any prototile `A`
and vertex `v`". An extreme point of a closed set lies on its frontier. -/
private theorem power_factorisation_aux_extreme_frontier (K : Set (E d)) (hK : IsClosed K)
    (q : E d) (hq : q ∈ K.extremePoints ℝ) : q ∈ frontier K := by
  refine ⟨subset_closure hq.1, fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior q hint
  haveI : Nontrivial (E d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [finrank_euclideanSpace_fin]
    have := (Fact.out : 2 ≤ d)
    omega
  obtain ⟨v, hv⟩ := exists_norm_eq (E d) (le_of_lt (half_pos hε))
  have h1 : q + v ∈ K := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hv]
    linarith))
  have h2 : q - v ∈ K := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, hv]
    linarith))
  have hseg : q ∈ openSegment ℝ (q + v) (q - v) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have heq : q + v = q := hq.2 h1 h2 hseg
  have hv0 : v = 0 := by
    have := congrArg (fun x => x - q) heq
    simpa using this
  rw [hv0, norm_zero] at hv
  linarith

/-- Step 1 of the V4 proof of `power_factorisation` (V4 1.15): "take any prototile `A`
and vertex `v`". Every prototype complex lists a vertex, with a point in it. -/
private theorem power_factorisation_aux_vertex (A : PolyManifoldDomain d) (K : CellComplex A) :
    ∃ v ∈ K.vertices, ∃ q : E d, q ∈ v.carrier := by
  obtain ⟨q, hq⟩ := A.compact.extremePoints_nonempty
    (A.interior_nonempty.mono interior_subset)
  have hqP : q ∈ frontier A.carrier :=
    power_factorisation_aux_extreme_frontier _ A.compact.isClosed q hq
  have hv := K.minimalCell_mem q hqP
  have hvsub : (K.minimalCell q hqP).carrier ⊆ A.carrier := by
    intro x hx
    have hx' : x ∈ frontier A.carrier := by
      rw [← K.carriers_cover]
      exact Set.mem_iUnion₂.mpr ⟨_, hv, hx⟩
    exact A.compact.isClosed.frontier_subset hx'
  have hvsing : (K.minimalCell q hqP).carrier = {q} :=
    power_factorisation_aux_extreme_cell A.carrier _ hvsub q hq (K.mem_relint_minimalCell q hqP)
  refine ⟨K.minimalCell q hqP, Finset.mem_filter.mpr ⟨hv, ?_⟩, q, by rw [hvsing]; rfl⟩
  have hdim := (K.minimalCell q hqP).flat.dimension
  rw [cellDirection, hvsing, direction_affineSpan, vectorSpan_singleton, finrank_bot] at hdim
  exact hdim.symm

/-- Step 1 of the V4 proof of `power_factorisation` (V4 1.15, Claim and 1.10(b)):
"apply Lemma 1.14 to `Π = {A}`, `p = v`; choose a tail ... for every `m ≥ 0`,
`σ^m 𝓕 ∈ B_{t_{N₀+m}} 𝔉`". A complete flag of direction spaces whose expansions are,
up to compatible frames, tuples of prototype cell directions. -/
private theorem power_factorisation_step1_tail_flag (S : SubstSystem d) [Nonempty S.ι] :
    ∃ (V : ℕ → Submodule ℝ (E d)) (B : ℕ → Ortho d),
      (∀ i ≤ d, Module.finrank ℝ (V i) = i) ∧ (∀ i < d, V i ≤ V (i + 1)) ∧
      (∀ m, B m ∈ S.rotGroup) ∧
      ∀ m i, i ≤ d →
        ((V i).map (S.σ ^ m).toLinearMap).map (B m).symm.toLinearEquiv.toLinearMap ∈
          S.cellDirections ∪ {⊤} := by
  classical
  let A : S.ι := Classical.arbitrary _
  let t₀ : FramedNode S := ⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩
  have ht₀ : t₀.frame.linearIsometryEquiv ∈ S.rotGroup := by
    have : t₀.frame.linearIsometryEquiv = 1 := by ext x; rfl
    rw [this]
    exact S.rotGroup.one_mem
  let P : CompatiblePatch S :=
    { tiles := {t₀}
      disjoint := by
        rw [Finset.coe_singleton]
        exact Set.pairwiseDisjoint_singleton _ _
      compatible := by
        intro t ht
        rw [Finset.mem_singleton.mp ht]
        exact ht₀ }
  obtain ⟨v, hv, q, hq⟩ := power_factorisation_aux_vertex (S.proto A) (S.cx A)
  have hqA : q ∈ (S.proto A).carrier := by
    have hv' := (Finset.mem_filter.mp hv).1
    have hx' : q ∈ frontier (S.proto A).carrier := by
      rw [← (S.cx A).carriers_cover]
      exact Set.mem_iUnion₂.mpr ⟨_, hv', hq⟩
    exact (S.proto A).compact.isClosed.frontier_subset hx'
  have hlist0 : t₀.Lists 0 q := ⟨v, hv, q, hq, by simp [FramedNode.prototypeFrame, t₀]⟩
  have hp : P.CommonListed q := by
    intro t ht _
    rw [Finset.mem_singleton.mp ht]
    exact hlist0
  have h0 : Nonempty (P.Incident q 0) := by
    let a : P.Address 0 := ⟨⟨t₀, Finset.mem_singleton_self _⟩, ()⟩
    have hg : ∀ y, compatibleInflatedFrame t₀ (P.compatible t₀ (Finset.mem_singleton_self _)) 0 y
        = y := by
      intro y
      have hc := (Classical.choose_spec (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ)
        t₀.frame.linearIsometryEquiv (P.compatible t₀ (Finset.mem_singleton_self _)))).2
      have hy := congrArg (fun e : E d ≃ₗ[ℝ] E d => e y) hc
      simp only [linearConj, Nat.cast_zero, zpow_zero, neg_zero, one_mul, mul_one] at hy
      show (Classical.choose (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ)
        t₀.frame.linearIsometryEquiv (P.compatible t₀ (Finset.mem_singleton_self _)))) y +
          (S.σ ^ 0) (t₀.frame 0) = y
      rw [show t₀.frame 0 = 0 from rfl, map_zero, add_zero]
      exact hy.trans rfl
    refine ⟨⟨a, ?_⟩⟩
    refine ⟨(S.σ ^ 0) q, ⟨q, hqA, rfl⟩, ?_⟩
    change compatibleInflatedFrame t₀ (P.compatible t₀ (Finset.mem_singleton_self _)) 0
      ((AffineIsometryEquiv.refl ℝ (E d)) ((S.σ ^ 0) q)) = (S.σ ^ 0) q
    rw [hg]
    rfl
  have hne : ∀ n, Nonempty (P.Incident q n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      obtain ⟨a⟩ := ih
      obtain ⟨b, _⟩ := (P.incidentForest q).2.1 n a
      exact ⟨b⟩
  obtain ⟨N, t, _, hN⟩ := CompatiblePatch.power_factorisation_aux_step15_tail_cover P q
  obtain ⟨a⟩ := hne N
  have hunique : ∀ m (b : P.Incident q (N + m + 1)),
      P.IncidentChild q (N + m) ((t a).node m) b → b = (t a).node (m + 1) :=
    fun m b hb => ExistsUnique.unique (hN (N + m) (by omega) ((t a).node m)) hb ((t a).step m)
  have hlisted := P.incident_commonListed q hp N ((t a).node 0)
  obtain ⟨V, hdim, hmono, -, hframe⟩ :=
    CompatiblePatch.power_factorisation_aux_step13_tail_flag P q N (t a) hunique hlisted
  exact ⟨V, fun m => (P.native (N + m) ((t a).node m).val).frame.linearIsometryEquiv, hdim,
    hmono, fun m => P.native_compatible (N + m) ((t a).node m).val, hframe⟩

/-- Step 2 of the V4 proof of `power_factorisation` (V4 1.15): "the finite set of native
flags". There are finitely many prototype cell directions. -/
private theorem power_factorisation_step2_cellDirections_finite (S : SubstSystem d) :
    S.cellDirections.Finite := by
  apply (Set.finite_iUnion fun A : S.ι =>
    ((S.cx A).cells.finite_toSet.image (fun e : Cell d => cellDirection e.carrier))).subset
  rintro V ⟨A, e, he, rfl⟩
  exact Set.mem_iUnion.mpr ⟨A, e, he, rfl⟩

/-- Step 3 of the V4 proof of `power_factorisation` (V4 1.15): "there is `p₀ ≥ 1` with
`𝖧 σ^{p₀} 𝓕 = 𝖧 𝓕`, i.e. `σ^{p₀} 𝓕 = R 𝓕` for some `R ∈ 𝖧`" (after replacing `𝓕` by a
later expansion of it). Pigeonhole on the finitely many native flag tuples. -/
private theorem power_factorisation_step3_recurrence (S : SubstSystem d) [Nonempty S.ι] :
    ∃ (W : ℕ → Submodule ℝ (E d)) (p : ℕ) (R : Ortho d), 1 ≤ p ∧ R ∈ S.rotGroup ∧
      (∀ i ≤ d, Module.finrank ℝ (W i) = i) ∧ (∀ i < d, W i ≤ W (i + 1)) ∧
      ∀ i ≤ d, (W i).map (S.σ ^ p).toLinearMap = (W i).map R.toLinearEquiv.toLinearMap := by
  classical
  obtain ⟨V, B, hdim, hmono, hB, hframe⟩ := power_factorisation_step1_tail_flag S
  let T : Set (Submodule ℝ (E d)) := S.cellDirections ∪ {⊤}
  have hT : T.Finite :=
    (power_factorisation_step2_cellDirections_finite S).union (Set.finite_singleton _)
  haveI : Finite T := hT.to_subtype
  let key : ℕ → (Fin (d + 1) → T) := fun m i =>
    ⟨_, hframe m i (Nat.lt_succ_iff.mp i.isLt)⟩
  have hmain : ∀ m n, m < n → key m = key n →
      ∃ (W : ℕ → Submodule ℝ (E d)) (p : ℕ) (R : Ortho d), 1 ≤ p ∧ R ∈ S.rotGroup ∧
        (∀ i ≤ d, Module.finrank ℝ (W i) = i) ∧ (∀ i < d, W i ≤ W (i + 1)) ∧
        ∀ i ≤ d, (W i).map (S.σ ^ p).toLinearMap =
          (W i).map R.toLinearEquiv.toLinearMap := by
    intro m n hmn hkey
    refine ⟨fun i => (V i).map (S.σ ^ m).toLinearMap, n - m, B n * (B m)⁻¹, by omega,
      S.rotGroup.mul_mem (hB n) (S.rotGroup.inv_mem (hB m)), ?_, ?_, ?_⟩
    · intro i hi
      exact (LinearEquiv.finrank_map_eq _ _).trans (hdim i hi)
    · intro i hi
      exact Submodule.map_mono (hmono i hi)
    · intro i hi
      have hk : ((V i).map (S.σ ^ m).toLinearMap).map (B m).symm.toLinearEquiv.toLinearMap =
          ((V i).map (S.σ ^ n).toLinearMap).map (B n).symm.toLinearEquiv.toLinearMap :=
        congrArg (fun f : Fin (d + 1) → T => (f ⟨i, Nat.lt_succ_of_le hi⟩).val) hkey
      have e1 : ((V i).map (S.σ ^ m).toLinearMap).map (S.σ ^ (n - m)).toLinearMap =
          (V i).map (S.σ ^ n).toLinearMap := by
        rw [← Submodule.map_comp]
        congr 1
        refine LinearMap.ext fun x => ?_
        change (S.σ ^ (n - m) * S.σ ^ m) x = (S.σ ^ n) x
        rw [← pow_add, Nat.sub_add_cancel hmn.le]
      have e2 : ((V i).map (S.σ ^ m).toLinearMap).map
          (B n * (B m)⁻¹).toLinearEquiv.toLinearMap = (V i).map (S.σ ^ n).toLinearMap := by
        have h1 : (B n * (B m)⁻¹).toLinearEquiv.toLinearMap =
            (B n).toLinearEquiv.toLinearMap ∘ₗ (B m).symm.toLinearEquiv.toLinearMap :=
          LinearMap.ext fun x => rfl
        have h2 : (B n).toLinearEquiv.toLinearMap ∘ₗ (B n).symm.toLinearEquiv.toLinearMap =
            LinearMap.id := LinearMap.ext fun x => by simp
        rw [h1, Submodule.map_comp, hk, ← Submodule.map_comp, h2, Submodule.map_id]
      change ((V i).map (S.σ ^ m).toLinearMap).map (S.σ ^ (n - m)).toLinearMap =
        ((V i).map (S.σ ^ m).toLinearMap).map (B n * (B m)⁻¹).toLinearEquiv.toLinearMap
      rw [e1, e2]
  obtain ⟨x, y, hxy, hk⟩ := Finite.exists_ne_map_eq_of_infinite key
  rcases lt_or_gt_of_ne hxy with h | h
  · exact hmain x y h hk
  · exact hmain y x h hk.symm

/-- Step 4 of the V4 proof of `power_factorisation` (V4 1.15): "block upper triangular
in a basis adapted to the flag". A complete flag of subspaces has an adapted basis. -/
private theorem power_factorisation_step4_adapted_basis (W : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (W i) = i) (hmono : ∀ i < d, W i ≤ W (i + 1)) :
    ∃ b : Module.Basis (Fin d) ℝ (E d), ∀ k ≤ d,
      W k = Submodule.span ℝ (b '' {i : Fin d | (i : ℕ) < k}) := by
  classical
  have hex : ∀ i : Fin d, ∃ x ∈ W (i + 1), x ∉ W i := by
    intro i
    apply SetLike.exists_of_lt
    refine lt_of_le_of_ne (hmono i i.isLt) ?_
    intro h
    have h1 := hdim i i.isLt.le
    have h2 := hdim (i + 1) i.isLt
    rw [h] at h1
    omega
  choose v hvW hvn using hex
  have hspan : ∀ k ≤ d, Submodule.span ℝ (v '' {i : Fin d | (i : ℕ) < k}) = W k := by
    intro k
    induction k with
    | zero =>
      intro _
      have h0 := hdim 0 (Nat.zero_le _)
      rw [Submodule.finrank_eq_zero] at h0
      rw [h0]
      simp
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hset : {i : Fin d | (i : ℕ) < k + 1} =
          {i : Fin d | (i : ℕ) < k} ∪ {⟨k, by omega⟩} := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
        omega
      rw [hset, Set.image_union, Submodule.span_union, ih', Set.image_singleton]
      have hle : W k ⊔ Submodule.span ℝ {v ⟨k, by omega⟩} ≤ W (k + 1) := by
        refine sup_le (hmono k (by omega)) ?_
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hvW ⟨k, by omega⟩
      apply Submodule.eq_of_le_of_finrank_eq hle
      apply le_antisymm (Submodule.finrank_mono hle)
      rw [hdim (k + 1) hk]
      have hlt : W k < W k ⊔ Submodule.span ℝ {v ⟨k, by omega⟩} := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro h
        apply hvn ⟨k, by omega⟩
        rw [h]
        exact Submodule.mem_sup_right (Submodule.subset_span rfl)
      have := Submodule.finrank_lt_finrank_of_lt hlt
      rw [hdim k (by omega)] at this
      omega
  have htop : W d = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hdim d le_rfl, finrank_euclideanSpace_fin]
  have hle : (⊤ : Submodule ℝ (E d)) ≤ Submodule.span ℝ (Set.range v) := by
    rw [← htop, ← hspan d le_rfl]
    apply Submodule.span_mono
    rintro _ ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩
  let b := basisOfTopLeSpanOfCardEqFinrank v hle (by simp)
  refine ⟨b, fun k hk => ?_⟩
  have hb : (b : Fin d → E d) = v := coe_basisOfTopLeSpanOfCardEqFinrank v hle _
  rw [hb]
  exact (hspan k hk).symm

/-- Step 5 of the V4 proof of `power_factorisation` (V4 1.15): "all its eigenvalues are
real and nonzero ... `L := L_1^2` has positive spectrum". A map that is upper triangular
in some basis has a square with positive real spectrum. -/
private theorem power_factorisation_step5_square_positive (b : Module.Basis (Fin d) ℝ (E d))
    (L₁ : E d ≃ₗ[ℝ] E d)
    (hL : ∀ j : Fin d, L₁ (b j) ∈ Submodule.span ℝ (b '' {i : Fin d | (i : ℕ) < j + 1})) :
    PositiveRealSpectrum (L₁ * L₁) := by
  classical
  let M := LinearMap.toMatrix b b L₁.toLinearMap
  have hM : M.BlockTriangular id := by
    intro i j hji
    change LinearMap.toMatrix b b L₁.toLinearMap i j = 0
    rw [LinearMap.toMatrix_apply]
    have hs := (Module.Basis.mem_span_image b).mp (hL j)
    by_contra hne
    have hi := hs (Finsupp.mem_support_iff.mpr hne)
    simp only [Set.mem_setOf_eq] at hi
    have : (j : ℕ) < i := hji
    omega
  have hmul : LinearMap.toMatrix b b (L₁ * L₁).toLinearMap = M * M := by
    rw [← LinearMap.toMatrix_mul]
    rfl
  have hdiag : ∀ i, (M * M) i i = M i i * M i i := by
    intro i
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single i
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hM h, zero_mul]
      · rw [hM h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hchar : (L₁ * L₁).toLinearMap.charpoly = ∏ i : Fin d, (Polynomial.X -
      Polynomial.C (M i i * M i i)) := by
    rw [← LinearMap.charpoly_toMatrix (L₁ * L₁).toLinearMap b, hmul,
      Matrix.charpoly_of_upperTriangular _ (hM.mul hM)]
    simp only [hdiag]
  have hdet : ∀ i, M i i ≠ 0 := by
    have h1 : M.det ≠ 0 := by
      rw [LinearMap.det_toMatrix]
      exact (LinearEquiv.isUnit_det' L₁).ne_zero
    rw [Matrix.det_of_upperTriangular hM] at h1
    exact fun i => (Finset.prod_ne_zero_iff.mp h1) i (Finset.mem_univ i)
  intro z hz
  rw [hchar, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_finset_prod,
    Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, _, hi⟩ := hz
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at hi
  have hz' : z = ((M i i * M i i : ℝ) : ℂ) := by
    rw [sub_eq_zero] at hi
    simpa using hi
  rw [hz']
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact mul_self_pos.mpr (hdet i)

/-- Step 6 of the V4 proof of `power_factorisation` (V4 1.15, using 1.10(a)):
"`L_1` normalises `H`". A linear map whose conjugations, and those of its inverse,
preserve the compatible group normalises it as a set. -/
private theorem power_factorisation_step6_normalizes (T : E d ≃ₗ[ℝ] E d)
    (h1 : ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup, h'.toLinearEquiv = T * h.toLinearEquiv * T⁻¹)
    (h2 : ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup,
      h'.toLinearEquiv = T⁻¹ * h.toLinearEquiv * T⁻¹⁻¹) :
    (fun h : Ortho d => T * h.toLinearEquiv * T⁻¹) '' (S.rotGroup : Set (Ortho d)) =
      (fun h : Ortho d => h.toLinearEquiv) '' (S.rotGroup : Set (Ortho d)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨h', hh', e⟩ := h1 h hh
    exact ⟨h', hh', e⟩
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨h', hh', e⟩ := h2 h hh
    refine ⟨h', hh', ?_⟩
    show T * h'.toLinearEquiv * T⁻¹ = h.toLinearEquiv
    rw [e, inv_inv]
    group

/-- Step 6 of the V4 proof of `power_factorisation` (V4 1.10(a)): conjugation-invariance
of the compatible group is preserved by products. -/
private theorem power_factorisation_step6_conj_mul (T₁ T₂ : E d ≃ₗ[ℝ] E d)
    (h1 : ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup, h'.toLinearEquiv = T₁ * h.toLinearEquiv * T₁⁻¹)
    (h2 : ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup, h'.toLinearEquiv = T₂ * h.toLinearEquiv * T₂⁻¹) :
    ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup,
      h'.toLinearEquiv = (T₁ * T₂) * h.toLinearEquiv * (T₁ * T₂)⁻¹ := by
  intro h hh
  obtain ⟨h', hh', e'⟩ := h2 h hh
  obtain ⟨h'', hh'', e''⟩ := h1 h' hh'
  refine ⟨h'', hh'', ?_⟩
  rw [e'', e', mul_inv_rev]
  simp only [mul_assoc]

/-- Step 6 of the V4 proof of `power_factorisation` (V4 1.10(a)): compatible rotations
conjugate the compatible group into itself. -/
private theorem power_factorisation_step6_conj_ortho (R : Ortho d) (hR : R ∈ S.rotGroup) :
    ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup,
      h'.toLinearEquiv = R.toLinearEquiv * h.toLinearEquiv * R.toLinearEquiv⁻¹ := by
  intro h hh
  exact ⟨R * h * R⁻¹, S.rotGroup.mul_mem (S.rotGroup.mul_mem hR hh) (S.rotGroup.inv_mem hR),
    LinearEquiv.ext fun x => rfl⟩

/-- Step 6 of the V4 proof of `power_factorisation` (V4 1.10(a)): integral powers of `σ`
conjugate the compatible group into itself. -/
private theorem power_factorisation_step6_conj_zpow (m : ℤ) :
    ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup,
      h'.toLinearEquiv = S.σ ^ m * h.toLinearEquiv * (S.σ ^ m)⁻¹ := by
  intro h hh
  obtain ⟨Q, hQ, e⟩ := S.rotGroup_conj_zpow m h hh
  exact ⟨Q, hQ, by rw [e, linearConj, zpow_neg]⟩

/-- P10, V4 1.15: a power admits the prescribed factorisation.
DEVIATION: `Nonempty S.ι` is explicit because stage 1 allows an empty catalogue.
V4's proof chooses a prototile and vertex; without any tiles an arbitrary expansion
need not have a positive-spectrum power modulo the trivial compatible group. -/
theorem power_factorisation (S : SubstSystem d) [Nonempty S.ι] :
    Nonempty (PowerFactorisation S) := by
  classical
  obtain ⟨W, p, R, hp, hR, hdim, hmono, hinv⟩ := power_factorisation_step3_recurrence S
  obtain ⟨b, hb⟩ := power_factorisation_step4_adapted_basis W hdim hmono
  let L₁ : E d ≃ₗ[ℝ] E d := (R⁻¹ : Ortho d).toLinearEquiv * S.σ ^ (p : ℤ)
  have hL : ∀ j : Fin d,
      L₁ (b j) ∈ Submodule.span ℝ (b '' {i : Fin d | (i : ℕ) < j + 1}) := by
    intro j
    have hj : (j : ℕ) + 1 ≤ d := j.isLt
    rw [← hb _ hj]
    have hbj : b j ∈ W (j + 1) := by
      rw [hb _ hj]
      exact Submodule.subset_span ⟨j, show (j : ℕ) < j + 1 by omega, rfl⟩
    have hs : (S.σ ^ p) (b j) ∈ (W (j + 1)).map R.toLinearEquiv.toLinearMap := by
      rw [← hinv _ hj]
      exact Submodule.mem_map_of_mem hbj
    obtain ⟨w, hw, hRw⟩ := Submodule.mem_map.mp hs
    have h1 : L₁ (b j) = R.symm ((S.σ ^ p) (b j)) := by
      simp only [L₁, zpow_natCast]
      rfl
    rw [h1, ← hRw]
    convert hw
    exact R.symm_apply_apply w
  obtain ⟨Q, hQ, hQe⟩ := S.rotGroup_conj_zpow (p : ℤ) R hR
  have e1 : (Q * R).toLinearEquiv = Q.toLinearEquiv * R.toLinearEquiv :=
    LinearEquiv.ext fun x => rfl
  have e2 : (R⁻¹ : Ortho d).toLinearEquiv = R.toLinearEquiv⁻¹ :=
    LinearEquiv.ext fun x => rfl
  have hfactor : S.σ ^ (p + p) = (Q * R).toLinearEquiv * (L₁ * L₁) := by
    have e3 : S.σ ^ (p + p) = S.σ ^ ((p : ℤ) + (p : ℤ)) := by
      rw [← Nat.cast_add, zpow_natCast]
    rw [e3, e1, hQe, linearConj]
    simp only [L₁, e2]
    group
  have hf1 := power_factorisation_step6_conj_mul (S := S) _ _
    (power_factorisation_step6_conj_ortho R⁻¹ (S.rotGroup.inv_mem hR))
    (power_factorisation_step6_conj_zpow (S := S) (p : ℤ))
  have hb1 := power_factorisation_step6_conj_mul (S := S) _ _
    (power_factorisation_step6_conj_zpow (S := S) (-(p : ℤ)))
    (power_factorisation_step6_conj_ortho R hR)
  have hLinv : L₁⁻¹ = S.σ ^ (-(p : ℤ)) * R.toLinearEquiv := by
    simp only [L₁, mul_inv_rev, zpow_neg, e2, inv_inv]
  have hf2 : ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup,
      h'.toLinearEquiv = L₁⁻¹ * h.toLinearEquiv * L₁⁻¹⁻¹ := by
    rw [hLinv]
    exact hb1
  have hF := power_factorisation_step6_conj_mul (S := S) L₁ L₁ hf1 hf1
  have hB : ∀ h ∈ S.rotGroup, ∃ h' ∈ S.rotGroup,
      h'.toLinearEquiv = (L₁ * L₁)⁻¹ * h.toLinearEquiv * (L₁ * L₁)⁻¹⁻¹ := by
    rw [mul_inv_rev]
    exact power_factorisation_step6_conj_mul (S := S) L₁⁻¹ L₁⁻¹ hf2 hf2
  exact ⟨⟨p + p, by omega, Q * R, S.rotGroup.mul_mem hQ hR, L₁ * L₁, hfactor,
    power_factorisation_step6_normalizes (L₁ * L₁) hF hB,
    power_factorisation_step5_square_positive b L₁ hL⟩⟩

section L_commutes_aux

open Polynomial Module Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! Auxiliary linear algebra for `L_commutes` (V4 1.16(a)). Instead of the polar decomposition
and the spectrum of `Ad_L` we argue directly with generalized eigenspaces of `L`: on
`G_ν ⊗ G_μ` the conjugates `L^n h L^{-n}` are `(μ/ν)^n` times a polynomial in `n`; boundedness
for `n ≥ 0` and `n ≤ 0` kills the off-diagonal blocks and makes the diagonal ones constant. -/

private theorem L_commutes_aux_poly_bdd_const (P : ℝ[X]) (M : ℝ) (hb : ∀ n : ℕ, |P.eval (n : ℝ)| ≤ M) :
    P = Polynomial.C (P.coeff 0) := by
  by_contra hne
  have hdeg : 0 < P.degree := by
    by_contra h
    push_neg at h
    exact hne (Polynomial.eq_C_of_degree_le_zero h)
  have ht := (Polynomial.abs_tendsto_atTop P hdeg).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop M).exists
  exact absurd (hb n) (not_le.mpr hn)

private theorem L_commutes_aux_scalar_key (r : ℝ) (hr : 0 < r) (P : ℝ[X]) (M : ℝ)
    (hb : ∀ n : ℕ, |r ^ n * P.eval (n : ℝ)| ≤ M) :
    (1 < r → P.eval 0 = 0) ∧ (r = 1 → P.eval 1 = P.eval 0) := by
  constructor
  · intro h1
    have hb' : ∀ n : ℕ, |P.eval (n : ℝ)| ≤ M := by
      intro n
      have h1n : 1 ≤ r ^ n := one_le_pow₀ h1.le
      calc |P.eval (n : ℝ)| = 1 * |P.eval (n : ℝ)| := by ring
        _ ≤ r ^ n * |P.eval (n : ℝ)| := by gcongr
        _ = |r ^ n * P.eval (n : ℝ)| := by
          rw [abs_mul, abs_of_pos (pow_pos hr n)]
        _ ≤ M := hb n
    have hP := L_commutes_aux_poly_bdd_const P M hb'
    set c := P.coeff 0
    by_contra hc
    have hc0 : c ≠ 0 := by
      intro h0; apply hc; rw [hP]; simp [h0]
    have ht := tendsto_pow_atTop_atTop_of_one_lt h1
    obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop (M / |c|)).exists
    have := hb n
    rw [hP, Polynomial.eval_C, abs_mul, abs_of_pos (pow_pos hr n)] at this
    have hcpos : 0 < |c| := abs_pos.mpr hc0
    rw [div_lt_iff₀ hcpos] at hn
    linarith
  · intro h1
    subst h1
    have hb' : ∀ n : ℕ, |P.eval (n : ℝ)| ≤ M := by
      intro n; simpa using hb n
    rw [L_commutes_aux_poly_bdd_const P M hb']
    simp

private theorem L_commutes_aux_choose_poly (a : ℕ) : ∃ Q : ℝ[X], ∀ n : ℕ, Q.eval (n : ℝ) = (n.choose a : ℝ) := by
  refine ⟨Polynomial.C ((a.factorial : ℝ)⁻¹) * descPochhammer ℝ a, fun n => ?_⟩
  rw [Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  have : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  push_cast
  field_simp

private theorem L_commutes_aux_exp_lemma (A : Module.End ℝ V) (c : ℝ) (hc : c ≠ 0) (D : ℕ) (x : V)
    (hx : ((A - c • 1) ^ D) x = 0) (n : ℕ) :
    (A ^ n) x = c ^ n • ∑ k ∈ Finset.range D,
      ((n.choose k : ℝ) * c⁻¹ ^ k) • ((A - c • 1) ^ k) x := by
  set N := A - c • (1 : Module.End ℝ V) with hN
  have hA : A = N + c • 1 := by simp [hN]
  have hcomm : Commute N (c • (1 : Module.End ℝ V)) := (Commute.one_right N).smul_right c
  have hzero : ∀ k, D ≤ k → (N ^ k) x = 0 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [add_comm, pow_add, Module.End.mul_apply, hx, map_zero]
  set T : ℕ → V := fun k => ((n.choose k : ℝ) * c ^ (n - k)) • (N ^ k) x with hT
  have key : (A ^ n) x = ∑ k ∈ Finset.range (n + 1), T k := by
    rw [hA, hcomm.add_pow, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hT, _root_.smul_pow, one_pow, Module.End.mul_apply, Module.End.natCast_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_smul, map_nsmul]
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    module
  have hT0 : ∀ k, (n + 1 ≤ k ∨ D ≤ k) → T k = 0 := by
    intro k hk
    rcases hk with hk | hk
    · simp [hT, Nat.choose_eq_zero_of_lt (by omega : n < k)]
    · simp [hT, hzero k hk]
  have hTeq : ∀ k, ((c ^ n * ((n.choose k : ℝ) * c⁻¹ ^ k)) • (N ^ k) x) = T k := by
    intro k
    by_cases hk : k ≤ n
    · simp only [hT]
      congr 1
      rw [pow_sub₀ c hc hk, inv_pow]
      ring
    · simp [hT, Nat.choose_eq_zero_of_lt (by omega : n < k)]
  rw [key, Finset.smul_sum]
  simp_rw [smul_smul, hTeq]
  have h1 : ∑ k ∈ Finset.range (n + 1), T k = ∑ k ∈ Finset.range (max (n + 1) D), T k := by
    apply Finset.sum_subset
    · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    · intro k _ hk; simp only [Finset.mem_range] at hk; exact hT0 k (Or.inl (by omega))
  have h2 : ∑ k ∈ Finset.range D, T k = ∑ k ∈ Finset.range (max (n + 1) D), T k := by
    apply Finset.sum_subset
    · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    · intro k _ hk; simp only [Finset.mem_range] at hk; exact hT0 k (Or.inr (by omega))
  rw [h1, h2]


private theorem L_commutes_aux_fam (A B Pi h : Module.End ℝ V) (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hαβ : 0 < α * β) (D : ℕ)
    (hPi : ∀ u, ((A - α • 1) ^ D) (Pi u) = 0)
    (hcomm : ∀ n : ℕ, ∀ u, Pi ((A ^ n) u) = (A ^ n) (Pi u))
    (x : V) (hx : ((B - β • 1) ^ D) x = 0) (M : ℝ)
    (hM : ∀ n : ℕ, ‖Pi ((A ^ n) (h ((B ^ n) x)))‖ ≤ M) :
    (1 < α * β → Pi (h x) = 0) ∧ (α * β = 1 → Pi (A (h (B x))) = Pi (h x)) := by
  have hpoly : ∀ y : V, ∃ P : ℝ[X], ∀ n : ℕ,
      inner ℝ y (Pi ((A ^ n) (h ((B ^ n) x)))) = (α * β) ^ n * P.eval (n : ℝ) := by
    intro y
    choose Q hQ using L_commutes_aux_choose_poly
    refine ⟨∑ b ∈ Finset.range D, ∑ a ∈ Finset.range D,
      Polynomial.C (β⁻¹ ^ b * α⁻¹ ^ a *
        inner ℝ y (((A - α • 1) ^ a) (Pi (h (((B - β • 1) ^ b) x))))) * Q b * Q a, ?_⟩
    intro n
    have hexpA : ∀ u, (A ^ n) (Pi u) = α ^ n • ∑ k ∈ Finset.range D,
        ((n.choose k : ℝ) * α⁻¹ ^ k) • ((A - α • 1) ^ k) (Pi u) :=
      fun u => L_commutes_aux_exp_lemma A α hα D _ (hPi u) n
    rw [hcomm, L_commutes_aux_exp_lemma B β hβ D x hx n]
    simp only [map_smul, map_sum, hexpA]
    simp only [inner_smul_right, inner_sum, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, hQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hbd : ∀ y : V, ∀ n : ℕ, |inner ℝ y (Pi ((A ^ n) (h ((B ^ n) x))))| ≤ ‖y‖ * M := by
    intro y n
    calc _ ≤ ‖y‖ * ‖Pi ((A ^ n) (h ((B ^ n) x)))‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖y‖ * M := by gcongr; exact hM n
  have hval : ∀ y : V, (1 < α * β → inner ℝ y (Pi (h x)) = 0) ∧
      (α * β = 1 → inner ℝ y (Pi (A (h (B x)))) = inner ℝ y (Pi (h x))) := by
    intro y
    obtain ⟨P, hP⟩ := hpoly y
    have hb : ∀ n : ℕ, |(α * β) ^ n * P.eval (n : ℝ)| ≤ ‖y‖ * M := by
      intro n; rw [← hP n]; exact hbd y n
    obtain ⟨k1, k2⟩ := L_commutes_aux_scalar_key (α * β) hαβ P _ hb
    have h0 := hP 0
    have h1 := hP 1
    simp only [pow_zero, Module.End.one_apply, one_mul, Nat.cast_zero] at h0
    simp only [pow_one, Nat.cast_one] at h1
    refine ⟨fun hr => by rw [h0]; exact k1 hr, fun hr => ?_⟩
    rw [h1, h0, hr, one_mul]
    exact k2 hr
  constructor
  · intro hr
    have := (hval (Pi (h x))).1 hr
    exact inner_self_eq_zero.mp this
  · intro hr
    exact ext_inner_left ℝ fun y => (hval y).2 hr

private theorem L_commutes_aux_card_roots_eq (p : ℝ[X])
    (hp : ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0) (hp0 : p ≠ 0) :
    p.roots.card = p.natDegree := by
  apply le_antisymm (Polynomial.card_roots' p)
  have hsplit : (p.map (algebraMap ℝ ℂ)).roots.card = p.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map]
  have hle : (p.map (algebraMap ℝ ℂ)).roots ≤ p.roots.map (algebraMap ℝ ℂ) := by
    rw [Multiset.le_iff_count]
    intro z
    by_cases hz : z ∈ (p.map (algebraMap ℝ ℂ)).roots
    · have hmap0 : p.map (algebraMap ℝ ℂ) ≠ 0 :=
        Polynomial.map_ne_zero hp0
      have hroot := (Polynomial.mem_roots hmap0).mp hz
      have him := hp z hroot
      have hzr : z = algebraMap ℝ ℂ z.re := by
        apply Complex.ext <;> simp [him]
      rw [hzr, Multiset.count_map_eq_count' _ _ (algebraMap ℝ ℂ).injective,
        Polynomial.count_roots, Polynomial.count_roots,
        ← Polynomial.eq_rootMultiplicity_map (algebraMap ℝ ℂ).injective]
    · rw [Multiset.count_eq_zero_of_notMem hz]; exact Nat.zero_le _
  have := Multiset.card_le_card hle
  rw [Multiset.card_map, hsplit] at this
  exact this

private theorem L_commutes_aux_finrank_biSup_le (G : ℝ → Submodule ℝ V) (hG : iSupIndep G) (s : Finset ℝ) :
    ∑ μ ∈ s, finrank ℝ (G μ) ≤ finrank ℝ (⨆ μ ∈ s, G μ : Submodule ℝ V) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hdisj : Disjoint (G a) (⨆ μ ∈ s, G μ) := by
      have := hG.disjoint_biSup (y := (s : Set ℝ)) (x := a) (by simpa using ha)
      simpa using this
    have hsup : (⨆ μ ∈ insert a s, G μ) = G a ⊔ ⨆ μ ∈ s, G μ := by
      rw [Finset.iSup_insert]
    rw [hsup]
    have h := Submodule.finrank_sup_add_finrank_inf_eq (G a) (⨆ μ ∈ s, G μ)
    rw [hdisj.eq_bot, finrank_bot, add_zero] at h
    omega

private theorem L_commutes_aux_core (f g h : Module.End ℝ V) (hfg : f * g = 1) (hgf : g * f = 1)
    (hL : ∀ z : ℂ, (f.charpoly.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0 ∧ 0 < z.re)
    (h1 : ∀ n : ℕ, ∀ x, ‖(f ^ n) (h ((g ^ n) x))‖ ≤ ‖x‖)
    (h2 : ∀ n : ℕ, ∀ x, ‖(g ^ n) (h ((f ^ n) x))‖ ≤ ‖x‖) : f * h = h * f := by
  classical
  set s : Finset ℝ := f.charpoly.roots.toFinset with hs
  set G : ℝ → Submodule ℝ V := fun μ => f.maxGenEigenspace μ with hGdef
  set D : ℕ := finrank ℝ V with hD
  have hcfg : Commute f g := hfg.trans hgf.symm
  -- positivity of the eigenvalues
  have hpos : ∀ μ ∈ s, 0 < μ := by
    intro μ hμ
    have hne : f.charpoly ≠ 0 := (LinearMap.charpoly_monic f).ne_zero
    rw [hs, Multiset.mem_toFinset, Polynomial.mem_roots hne] at hμ
    have hr : (f.charpoly.map (algebraMap ℝ ℂ)).IsRoot (algebraMap ℝ ℂ μ) := hμ.map
    simpa using (hL _ hr).2
  -- the generalized eigenspaces span
  have hspan : (⨆ μ ∈ s, G μ) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    have hne : f.charpoly ≠ 0 := (LinearMap.charpoly_monic f).ne_zero
    have hcard := L_commutes_aux_card_roots_eq f.charpoly (fun z hz => (hL z hz).1) hne
    rw [LinearMap.charpoly_natDegree] at hcard
    calc finrank ℝ V = f.charpoly.roots.card := hcard.symm
      _ = ∑ μ ∈ s, f.charpoly.roots.count μ := (Multiset.toFinset_sum_count_eq _).symm
      _ = ∑ μ ∈ s, finrank ℝ (G μ) := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Polynomial.count_roots]
        exact (LinearMap.finrank_maxGenEigenspace_eq f μ).symm
      _ ≤ _ := L_commutes_aux_finrank_biSup_le G (Module.End.independent_maxGenEigenspace f) s
  have hGker : ∀ μ, ∀ x ∈ G μ, ((f - μ • 1) ^ D) x = 0 := by
    intro μ x hx
    simp only [hGdef] at hx
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.mem_genEigenspace_nat] at hx
    exact LinearMap.mem_ker.mp hx
  have hGg : ∀ μ, μ ≠ 0 → ∀ x ∈ G μ, ((g - μ⁻¹ • 1) ^ D) x = 0 := by
    intro μ hμ x hx
    have heq : g - μ⁻¹ • (1 : Module.End ℝ V) = (-μ⁻¹) • (g * (f - μ • 1)) := by
      rw [mul_sub, hgf, mul_smul_comm, mul_one, smul_sub, smul_smul, neg_mul,
        inv_mul_cancel₀ hμ]
      simp only [neg_smul, one_smul]
      abel
    have hc : Commute g (f - μ • 1) := hcfg.symm.sub_right ((Commute.one_right g).smul_right μ)
    rw [heq, _root_.smul_pow, hc.mul_pow, LinearMap.smul_apply, Module.End.mul_apply, hGker μ x hx,
      map_zero, smul_zero]
  have hmapf : ∀ μ, ∀ x ∈ G μ, f x ∈ G μ := fun μ x hx =>
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ hx
  have hmapg : ∀ μ, ∀ x ∈ G μ, g x ∈ G μ := fun μ x hx =>
    Module.End.mapsTo_maxGenEigenspace_of_comm hcfg μ hx
  have ext_on : ∀ A B : Module.End ℝ V, (∀ μ ∈ s, ∀ x ∈ G μ, A x = B x) → A = B := by
    intro A B hAB
    have hle : (⨆ μ ∈ s, G μ) ≤ LinearMap.ker (A - B) :=
      iSup₂_le fun μ hμ x hx => by
        simp [LinearMap.mem_ker, sub_eq_zero, hAB μ hμ x hx]
    rw [hspan] at hle
    ext x
    have := hle (Submodule.mem_top (x := x))
    simpa [LinearMap.mem_ker, sub_eq_zero] using this
  -- projections
  have hproj : ∀ μ ∈ s, ∃ π : Module.End ℝ V, (∀ x ∈ G μ, π x = x) ∧
      (∀ ν ∈ s, ν ≠ μ → ∀ x ∈ G ν, π x = 0) ∧ (∀ u, π u ∈ G μ) := by
    intro μ hμ
    have hcompl : IsCompl (G μ) (⨆ ν ∈ s.erase μ, G ν) := by
      constructor
      · have := (Module.End.independent_maxGenEigenspace f).disjoint_biSup
          (y := ((s.erase μ : Finset ℝ) : Set ℝ)) (x := μ) (by simp)
        simpa [hGdef, and_comm] using this
      · rw [codisjoint_iff, eq_top_iff, ← hspan]
        refine iSup₂_le fun ν hν => ?_
        by_cases hνμ : ν = μ
        · subst hνμ; exact le_sup_left
        · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun ν (_ : ν ∈ s.erase μ) => G ν) ν
            (Finset.mem_erase.mpr ⟨hνμ, hν⟩) le_rfl)
    refine ⟨(G μ).subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ hcompl, ?_, ?_, ?_⟩
    · intro x hx
      have := Submodule.linearProjOfIsCompl_apply_left hcompl ⟨x, hx⟩
      exact congrArg Subtype.val this
    · intro ν hν hνμ x hx
      have hxq : x ∈ (⨆ ν ∈ s.erase μ, G ν) :=
        (le_iSup₂_of_le (f := fun ν (_ : ν ∈ s.erase μ) => G ν) ν
          (Finset.mem_erase.mpr ⟨hνμ, hν⟩) le_rfl) hx
      simp only [LinearMap.comp_apply, Submodule.linearProjOfIsCompl_apply_right' hcompl x hxq,
        map_zero]
    · intro u; exact (Submodule.linearProjOfIsCompl _ _ hcompl u).2
  choose! π hπ1 hπ2 hπ3 using hproj
  have hsum : ∀ u, ∑ μ ∈ s, π μ u = u := by
    have : (∑ μ ∈ s, π μ) = 1 := by
      apply ext_on
      intro ν hν x hx
      rw [LinearMap.sum_apply, Finset.sum_eq_single ν]
      · simp [hπ1 ν hν x hx]
      · intro μ hμ hμν; exact hπ2 μ hμ ν hν (Ne.symm hμν) x hx
      · intro h; exact absurd hν h
    intro u
    have := LinearMap.congr_fun this u
    simpa [LinearMap.sum_apply] using this
  have hcommA : ∀ μ ∈ s, ∀ A : Module.End ℝ V, (∀ ν, ∀ x ∈ G ν, A x ∈ G ν) →
      π μ * A = A * π μ := by
    intro μ hμ A hA
    apply ext_on
    intro ν hν x hx
    simp only [Module.End.mul_apply]
    by_cases hνμ : ν = μ
    · subst hνμ; rw [hπ1 ν hμ x hx, hπ1 ν hμ _ (hA ν x hx)]
    · rw [hπ2 μ hμ ν hν hνμ x hx, hπ2 μ hμ ν hν hνμ _ (hA ν x hx), map_zero]
  have hcf : ∀ μ ∈ s, Commute (π μ) f := fun μ hμ => hcommA μ hμ f hmapf
  have hcg : ∀ μ ∈ s, Commute (π μ) g := fun μ hμ => hcommA μ hμ g hmapg
  have hbound : ∀ μ ∈ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖π μ u‖ ≤ C * ‖u‖ := fun μ _ =>
    ⟨‖LinearMap.toContinuousLinearMap (π μ)‖, norm_nonneg _, fun u =>
      (LinearMap.toContinuousLinearMap (π μ)).le_opNorm u⟩
  -- off-diagonal blocks vanish
  have hoff : ∀ ν ∈ s, ∀ x ∈ G ν, ∀ μ ∈ s, μ ≠ ν → π μ (h x) = 0 := by
    intro ν hν x hx μ hμ hμν
    have hν0 := hpos ν hν
    have hμ0 := hpos μ hμ
    obtain ⟨C, hC0, hC⟩ := hbound μ hμ
    rcases lt_or_gt_of_ne hμν with hlt | hgt
    · -- μ < ν : use g
      have := (L_commutes_aux_fam g f (π μ) h μ⁻¹ ν (inv_ne_zero hμ0.ne') hν0.ne'
        (mul_pos (inv_pos.mpr hμ0) hν0) D
        (fun u => hGg μ hμ0.ne' _ (hπ3 μ hμ u))
        (fun n u => LinearMap.congr_fun ((hcg μ hμ).pow_right n).eq u)
        x (hGker ν x hx) (C * ‖x‖)
        (fun n => (hC _).trans (mul_le_mul_of_nonneg_left (h2 n x) hC0))).1
      apply this
      rw [inv_mul_eq_div, one_lt_div hμ0]; exact hlt
    · -- μ > ν : use f
      have := (L_commutes_aux_fam f g (π μ) h μ ν⁻¹ hμ0.ne' (inv_ne_zero hν0.ne')
        (mul_pos hμ0 (inv_pos.mpr hν0)) D
        (fun u => hGker μ _ (hπ3 μ hμ u))
        (fun n u => LinearMap.congr_fun ((hcf μ hμ).pow_right n).eq u)
        x (hGg ν hν0.ne' x hx) (C * ‖x‖)
        (fun n => (hC _).trans (mul_le_mul_of_nonneg_left (h1 n x) hC0))).1
      apply this
      rw [← div_eq_mul_inv, one_lt_div hν0]; exact hgt
  have hinv : ∀ ν ∈ s, ∀ x ∈ G ν, h x ∈ G ν := by
    intro ν hν x hx
    rw [← hsum (h x), Finset.sum_eq_single ν]
    · exact hπ3 ν hν _
    · intro μ hμ hμν; exact hoff ν hν x hx μ hμ hμν
    · intro h'; exact absurd hν h'
  have hdiag : f * h * g = h := by
    apply ext_on
    intro ν hν x hx
    have hν0 := hpos ν hν
    obtain ⟨C, hC0, hC⟩ := hbound ν hν
    have := (L_commutes_aux_fam f g (π ν) h ν ν⁻¹ hν0.ne' (inv_ne_zero hν0.ne')
        (mul_pos hν0 (inv_pos.mpr hν0)) D
        (fun u => hGker ν _ (hπ3 ν hν u))
        (fun n u => LinearMap.congr_fun ((hcf ν hν).pow_right n).eq u)
        x (hGg ν hν0.ne' x hx) (C * ‖x‖)
        (fun n => (hC _).trans (mul_le_mul_of_nonneg_left (h1 n x) hC0))).2 (mul_inv_cancel₀ hν0.ne')
    have hm1 : f (h (g x)) ∈ G ν := hmapf ν _ (hinv ν hν _ (hmapg ν x hx))
    rw [hπ1 ν hν _ hm1, hπ1 ν hν _ (hinv ν hν x hx)] at this
    simpa [Module.End.mul_apply] using this
  calc f * h = f * h * (g * f) := by rw [hgf, mul_one]
    _ = (f * h * g) * f := by simp only [mul_assoc]
    _ = h * f := by rw [hdiag]

end L_commutes_aux

private theorem L_commutes_conj_mem (F : PowerFactorisation S) (h : Ortho d)
    (hh : h ∈ S.rotGroup) (n : ℕ) :
    (∃ k ∈ S.rotGroup, ∀ x, ((F.L.toLinearMap) ^ n) (h ((F.L.symm.toLinearMap ^ n) x)) = k x) ∧
    (∃ k ∈ S.rotGroup, ∀ x, ((F.L.symm.toLinearMap) ^ n) (h ((F.L.toLinearMap ^ n) x)) = k x) := by
  induction n with
  | zero => exact ⟨⟨h, hh, fun x => by simp⟩, ⟨h, hh, fun x => by simp⟩⟩
  | succ n ih =>
    obtain ⟨⟨k, hk, hkx⟩, ⟨k', hk', hk'x⟩⟩ := ih
    constructor
    · have hmem : F.L * k.toLinearEquiv * F.L⁻¹ ∈
          (fun h : Ortho d => h.toLinearEquiv) '' (S.rotGroup : Set (Ortho d)) := by
        rw [← F.normalizes]; exact ⟨k, hk, rfl⟩
      obtain ⟨j, hj, hjeq⟩ := hmem
      refine ⟨j, hj, fun x => ?_⟩
      rw [pow_succ' F.L.toLinearMap n, pow_succ F.L.symm.toLinearMap n, Module.End.mul_apply,
        Module.End.mul_apply, hkx]
      have := congrArg (fun e : E d ≃ₗ[ℝ] E d => e x) hjeq
      change j x = F.L (k (F.L.symm x)) at this
      rw [this]
      rfl
    · have hmem : k'.toLinearEquiv ∈
          (fun h : Ortho d => F.L * h.toLinearEquiv * F.L⁻¹) '' (S.rotGroup : Set (Ortho d)) := by
        rw [F.normalizes]; exact ⟨k', hk', rfl⟩
      obtain ⟨j, hj, hjeq⟩ := hmem
      refine ⟨j, hj, fun x => ?_⟩
      rw [pow_succ' F.L.symm.toLinearMap n, pow_succ F.L.toLinearMap n, Module.End.mul_apply,
        Module.End.mul_apply, hk'x]
      have := congrArg (fun e : E d ≃ₗ[ℝ] E d => e (F.L x)) hjeq
      change F.L (j (F.L.symm (F.L x))) = k' (F.L x) at this
      rw [LinearEquiv.symm_apply_apply] at this
      change F.L.symm (k' (F.L x)) = j x
      rw [← this, LinearEquiv.symm_apply_apply]

/-- P11, V4 1.16(a): the positive factor centralizes the full compatible group. -/
theorem L_commutes (F : PowerFactorisation S) (h : Ortho d) (hh : h ∈ S.rotGroup) :
    F.L * h.toLinearEquiv = h.toLinearEquiv * F.L := by
  have hc := L_commutes_aux_core F.L.toLinearMap F.L.symm.toLinearMap
    h.toLinearEquiv.toLinearMap
    (by ext x; simp) (by ext x; simp) F.positive
    (fun n x => by
      obtain ⟨⟨k, _, hkx⟩, _⟩ := L_commutes_conj_mem F h hh n
      exact le_of_eq ((congrArg norm (hkx x)).trans (k.norm_map x)))
    (fun n x => by
      obtain ⟨_, ⟨k, _, hkx⟩⟩ := L_commutes_conj_mem F h hh n
      exact le_of_eq ((congrArg norm (hkx x)).trans (k.norm_map x)))
  exact LinearEquiv.ext fun x => LinearMap.congr_fun hc x

/-- Step 1 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"There is q ≥ 1 with L^q V ∈ H V". Apply the finite permutation of direction
orbits to a multiple of the factorisation exponent, then remove the R factor. -/
private theorem L_fixes_directions_sides_step1_orbit_return (F : PowerFactorisation S)
    (V : Submodule ℝ (E d)) (hV : V ∈ S.hPi) :
    ∃ q : ℕ, 1 ≤ q ∧ ∃ h ∈ S.rotGroup,
      V.map (F.L ^ q).toLinearMap = V.map h.toLinearEquiv.toLinearMap := by
  classical
  obtain ⟨hfinite, _, p, hp⟩ := S.orbits_finite
  letI : Fintype S.directionOrbits := hfinite.fintype
  have hpiter : ∀ (n : ℕ) (O : S.directionOrbits),
      ((p ^ n) O).val = (fun U => U.map (S.σ ^ n).toLinearMap) '' O.val := by
    intro n
    induction n with
    | zero => intro O; simp
    | succ n ih =>
      intro O
      rw [pow_succ', Equiv.Perm.mul_apply, hp, ih, Set.image_image]
      congr 1
      funext U
      simp [pow_succ', LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp,
        ← Submodule.map_comp]
  obtain ⟨U, hU, r, hr, hVU⟩ := hV
  let O : S.directionOrbits := ⟨S.directionOrbit U, U, hU, rfl⟩
  let q := orderOf p
  have hq : 1 ≤ q := orderOf_pos p
  have hpq : p ^ (F.power * q) = 1 := by
    rw [Nat.mul_comm, pow_mul]
    simp [q]
  have hreturn : V.map (S.σ ^ (F.power * q)).toLinearMap ∈ O.val := by
    rw [← show ((p ^ (F.power * q)) O).val = O.val by simp [hpq], hpiter]
    exact ⟨V, ⟨r, hr, hVU⟩, rfl⟩
  obtain ⟨r', hr', hreturn⟩ := hreturn
  have hfac : S.σ ^ (F.power * q) = F.R.toLinearEquiv ^ q * F.L ^ q := by
    rw [pow_mul, F.factor]
    exact (show Commute F.R.toLinearEquiv F.L from
      (L_commutes F F.R F.R_mem).symm).mul_pow q
  refine ⟨q, hq, (F.R ^ q)⁻¹ * r' * r⁻¹,
    S.rotGroup.mul_mem (S.rotGroup.mul_mem
      (S.rotGroup.inv_mem (S.rotGroup.pow_mem F.R_mem q)) hr')
      (S.rotGroup.inv_mem hr), ?_⟩
  have hcancel := congrArg
    (fun W : Submodule ℝ (E d) =>
      W.map ((F.R.toLinearEquiv ^ q)⁻¹).toLinearMap) hreturn
  rw [hfac] at hcancel
  simp only [← Submodule.map_comp, ← Module.End.mul_eq_comp,
    ← LinearEquiv.coe_toLinearMap_mul, inv_mul_cancel_left] at hcancel
  have hRpow : (F.R ^ q).toLinearEquiv = F.R.toLinearEquiv ^ q := by
    induction q with
    | zero => rfl
    | succ n ih =>
      change (F.R ^ n).toLinearEquiv * F.R.toLinearEquiv =
        F.R.toLinearEquiv ^ n * F.R.toLinearEquiv
      rw [ih]
  rw [hcancel, hVU]
  simp only [← Submodule.map_comp, ← Module.End.mul_eq_comp,
    ← LinearEquiv.coe_toLinearMap_mul]
  congr 1
  ext x
  simp [← hRpow]

open scoped BigOperators

/-- Step 1 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"positive real spectrum". Complex roots lie in the image of ℝ, so the
characteristic polynomial splits over ℝ and all its real roots are positive. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step1_real_splitting
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ F] (M : Module.End ℝ F)
    (hpos : ∀ z : ℂ, (M.charpoly.map (algebraMap ℝ ℂ)).IsRoot z →
      z.im = 0 ∧ 0 < z.re) :
    M.charpoly.Splits ∧ ∀ r : ℝ, M.charpoly.IsRoot r → 0 < r := by
  constructor
  · apply Polynomial.Splits.of_splits_map (algebraMap ℝ ℂ) (IsAlgClosed.splits _)
    intro z hz
    have hz' := (Polynomial.mem_roots (Polynomial.map_ne_zero M.charpoly_monic.ne_zero)).mp hz
    refine ⟨z.re, ?_⟩
    apply Complex.ext <;> simp [hpos z hz']
  · intro r hr
    exact (hpos r (Polynomial.IsRoot.map hr)).2

/-- Step 2 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"decompose u into generalised eigenvectors". Factor the characteristic
polynomial into coprime powers of linear factors and decompose its kernel;
Cayley--Hamilton makes that kernel the whole space. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step2_primary_decomposition
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ F] (M : Module.End ℝ F)
    (hsplit : M.charpoly.Splits) (u : F) :
    ∃ v : ℝ → F,
      u = ∑ r ∈ M.charpoly.roots.toFinset, v r ∧
      ∀ r : ℝ, ((M - r • (1 : Module.End ℝ F)) ^ M.charpoly.roots.card) (v r) = 0 := by
  classical
  let p : ℝ → Polynomial ℝ := fun r => (Polynomial.X - Polynomial.C r) ^
    M.charpoly.rootMultiplicity r
  have hc (r t : ℝ) (hrt : r ≠ t) : IsCoprime (p r) (p t) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hrt).isUnit).pow
  have hker (s : Finset ℝ) :
      s.sup (fun r => LinearMap.ker (Polynomial.aeval M (p r))) =
        LinearMap.ker (Polynomial.aeval M (∏ r ∈ s, p r)) := by
    induction s using Finset.induction_on with
    | empty => simp [Module.End.one_eq_id]
    | @insert r s hrs ih =>
      rw [Finset.sup_insert, Finset.prod_insert hrs, ih]
      apply Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime
      exact IsCoprime.prod_right fun t ht => hc r t (by rintro rfl; exact hrs ht)
  have hp : ∏ r ∈ M.charpoly.roots.toFinset, p r = M.charpoly := by
    calc
      _ = (M.charpoly.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod :=
        (Polynomial.prod_multiset_root_eq_finset_root (p := M.charpoly)).symm
      _ = M.charpoly := (hsplit.eq_prod_roots_of_monic M.charpoly_monic).symm
  have hu : u ∈ ⨆ r ∈ M.charpoly.roots.toFinset,
      LinearMap.ker (Polynomial.aeval M (p r)) := by
    rw [← Finset.sup_eq_iSup, hker, hp, LinearMap.aeval_self_charpoly]
    simp
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ u).mp hu
  refine ⟨fun r => v r, hv.symm, ?_⟩
  intro r
  have hr : ((M - r • (1 : Module.End ℝ F)) ^ M.charpoly.rootMultiplicity r)
      (v r : F) = 0 := by
    simpa only [p, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, LinearMap.mem_ker] using (v r).property
  have hle : M.charpoly.rootMultiplicity r ≤ M.charpoly.roots.card := by
    rw [← Polynomial.count_roots]
    exact Multiset.count_le_card _ _
  rw [← Nat.sub_add_cancel hle, pow_add, Module.End.mul_apply, hr, map_zero]

/-- Step 3 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"the largest Jordan index occurring there". On a generalized eigenvector,
the binomial expansion of (r I + N)^n terminates at the nilpotence index. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step3_jordan_binomial
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    (M : Module.End ℝ F) (r : ℝ) (hr : r ≠ 0) (v : F) (m : ℕ)
    (hnil : ((M - r • (1 : Module.End ℝ F)) ^ m) v = 0) (n : ℕ) :
    (M ^ n) v = ∑ j ∈ Finset.range m,
      (r ^ n * ((n.choose j : ℝ) / r ^ j)) •
        ((M - r • (1 : Module.End ℝ F)) ^ j) v := by
  let N := M - r • (1 : Module.End ℝ F)
  have hcomm : Commute N (r • (1 : Module.End ℝ F)) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using Algebra.commute_algebraMap_right r N
  have heq : N + r • (1 : Module.End ℝ F) = M := sub_add_cancel M _
  have hpow := congrArg (fun T : Module.End ℝ F => T v) (hcomm.add_pow n)
  rw [heq] at hpow
  simp only [LinearMap.sum_apply, Module.End.mul_apply, _root_.smul_pow, one_pow,
    LinearMap.smul_apply, Module.End.one_apply, Module.End.natCast_apply,
    map_smul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul] at hpow
  have hsum : (M ^ n) v = ∑ j ∈ Finset.range (n + 1),
      (r ^ n * ((n.choose j : ℝ) / r ^ j)) • (N ^ j) v := by
    rw [hpow]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    rw [pow_sub₀ r hr hjn]
    congr 1
    ring
  rw [hsum]
  rcases le_total m (n + 1) with hmn | hnm
  · symm
    apply Finset.sum_subset (Finset.range_mono hmn)
    intro j hj hjm
    have hzero : (N ^ j) v = 0 :=
      Module.End.pow_map_zero_of_le (by simpa using hjm) hnil
    rw [hzero, smul_zero]
  · apply Finset.sum_subset (Finset.range_mono hnm)
    intro j hj hjn
    have hn : n < j := by simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hjn
    simp [Nat.choose_eq_zero_of_lt hn]

/-- Step 4 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"decompose u into generalised eigenvectors". Expand the binomial
coefficients as polynomials in n to obtain a finite sum of r^n n^j times
constant vectors, with every exponential base r positive. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step4_jordan_expansion
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ F] (M : Module.End ℝ F)
    (hsplit : M.charpoly.Splits)
    (hpos : ∀ r : ℝ, M.charpoly.IsRoot r → 0 < r) (u : F) :
    ∃ (s : Finset ℝ) (m : ℕ) (a : ℝ → ℕ → F),
      (∀ r ∈ s, 0 < r) ∧ ∀ n : ℕ,
        (M ^ n) u = ∑ r ∈ s, ∑ j ∈ Finset.range m,
          (r ^ n * (n : ℝ) ^ j) • a r j := by
  classical
  obtain ⟨v, hv, hnil⟩ := L_fixes_directions_sides_step2_spectral_limit_step2_primary_decomposition M hsplit u
  let m := M.charpoly.roots.card
  let N : ℝ → Module.End ℝ F := fun r => M - r • (1 : Module.End ℝ F)
  let a : ℝ → ℕ → F := fun r j => ∑ t ∈ Finset.range m,
    ((descPochhammer ℝ t).coeff j / ((t.factorial : ℝ) * r ^ t)) • (N r ^ t) (v r)
  have hpos' (r : ℝ) (hr : r ∈ M.charpoly.roots.toFinset) : 0 < r :=
    hpos r ((Polynomial.mem_roots M.charpoly_monic.ne_zero).mp (Multiset.mem_toFinset.mp hr))
  refine ⟨M.charpoly.roots.toFinset, m, a, hpos', ?_⟩
  intro n
  rw [hv, map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [L_fixes_directions_sides_step2_spectral_limit_step3_jordan_binomial M r (hpos' r hr).ne' (v r) m (hnil r) n]
  change (∑ t ∈ Finset.range m,
    (r ^ n * ((n.choose t : ℝ) / r ^ t)) • (N r ^ t) (v r)) = _
  simp only [a, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Finset.sum_smul]
  congr 1
  rw [Nat.cast_choose_eq_descPochhammer_div]
  rw [Polynomial.eval_eq_sum_range' (by simpa using ht :
    (descPochhammer ℝ t).natDegree < m) (n : ℝ)]
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Step 5 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"let μ be the largest eigenvalue with nonzero component". Before choosing
a dominant term, collect all coefficients having the same exponential base
and polynomial degree; this accounts for cancellations. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step5_collect_terms
    {ι F : Type*} [AddCommGroup F] [Module ℝ F]
    (t : Finset ι) (r : ι → ℝ) (j : ι → ℕ) (v : ι → F)
    (hpos : ∀ i ∈ t, 0 < r i) :
    ∃ (s : Finset ℝ) (m : ℕ) (a : ℝ → ℕ → F),
      (∀ μ ∈ s, 0 < μ) ∧ ∀ n : ℕ,
        (∑ i ∈ t, ((r i) ^ n * (n : ℝ) ^ j i) • v i) =
          ∑ μ ∈ s, ∑ k ∈ Finset.range m, (μ ^ n * (n : ℝ) ^ k) • a μ k := by
  classical
  let s := t.image r
  let m := t.sup j + 1
  let a := fun μ k => ∑ i ∈ t.filter (fun i => r i = μ ∧ j i = k), v i
  have hs (i : ι) (hi : i ∈ t) : r i ∈ s := Finset.mem_image_of_mem r hi
  have hm (i : ι) (hi : i ∈ t) : j i ∈ Finset.range m :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hi))
  refine ⟨s, m, a, ?_, ?_⟩
  · intro μ hμ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hμ
    exact hpos i hi
  · intro n
    rw [← Finset.sum_fiberwise_of_maps_to hs]
    apply Finset.sum_congr rfl
    intro μ hμ
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun i hi => hm i (Finset.mem_filter.mp hi).1)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.filter_filter]
    simp only [a, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi, hr, hj⟩ := Finset.mem_filter.mp hi
    rw [hr, hj]

/-- Step 6 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"Λ^{dim V} L^q has positive real spectrum too". The needed consequence
is obtained directly by multilinearity: a wedge of exponential-polynomial
sequences has the same form, and its bases are products of positive bases. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step6_multilinear_expansion
    {ι F G : Type*} [Fintype ι]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]
    (f : MultilinearMap ℝ (fun _ : ι => F) G)
    (s : ι → Finset ℝ) (m : ι → ℕ) (a : ι → ℝ → ℕ → F)
    (hpos : ∀ i r, r ∈ s i → 0 < r) :
    ∃ (t : Finset ℝ) (q : ℕ) (b : ℝ → ℕ → G),
      (∀ r ∈ t, 0 < r) ∧ ∀ n : ℕ,
        f (fun i => ∑ r ∈ s i, ∑ j ∈ Finset.range (m i),
          (r ^ n * (n : ℝ) ^ j) • a i r j) =
          ∑ r ∈ t, ∑ j ∈ Finset.range q, (r ^ n * (n : ℝ) ^ j) • b r j := by
  classical
  let A := fun i => (s i) ×ˢ Finset.range (m i)
  let T := Fintype.piFinset A
  let r := fun z : ι → ℝ × ℕ => ∏ i, (z i).1
  let j := fun z : ι → ℝ × ℕ => ∑ i, (z i).2
  let v := fun z : ι → ℝ × ℕ => f (fun i => a i (z i).1 (z i).2)
  have hpos' (z : ι → ℝ × ℕ) (hz : z ∈ T) : 0 < r z := by
    apply Finset.prod_pos
    intro i hi
    exact hpos i _ (Finset.mem_product.mp (Fintype.mem_piFinset.mp hz i)).1
  obtain ⟨t, q, b, hb, heq⟩ := L_fixes_directions_sides_step2_spectral_limit_step5_collect_terms T r j v hpos'
  refine ⟨t, q, b, hb, ?_⟩
  intro n
  rw [← heq]
  have hsum : (fun i => ∑ r ∈ s i, ∑ j ∈ Finset.range (m i),
      (r ^ n * (n : ℝ) ^ j) • a i r j) =
      (fun i => ∑ z ∈ A i, (z.1 ^ n * (n : ℝ) ^ z.2) • a i z.1 z.2) := by
    funext i
    simp only [A, Finset.sum_product]
  rw [hsum, f.map_sum_finset]
  apply Finset.sum_congr rfl
  intro z hz
  rw [f.map_smul_univ]
  congr 1
  simp only [r, j, Finset.prod_mul_distrib, ← Finset.prod_pow, Finset.prod_pow_eq_pow_sum]

open Filter Topology in
/-- Step 7 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"let μ be the largest eigenvalue with nonzero component and s the
largest Jordan index occurring there". After collecting equal bases and
degrees, divide by μ^n n^s; every other term tends to zero and the surviving
coefficient is nonzero. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step7_dominant_term
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Finset ℝ) (m : ℕ) (a : ℝ → ℕ → F)
    (hpos : ∀ r ∈ s, 0 < r)
    (hne : ∃ r ∈ s, ∃ j ∈ Finset.range m, a r j ≠ 0) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ k : ℕ, ∃ w : F, w ≠ 0 ∧
      Tendsto (fun n : ℕ => (μ ^ n * (n : ℝ) ^ k)⁻¹ •
        ∑ r ∈ s, ∑ j ∈ Finset.range m, (r ^ n * (n : ℝ) ^ j) • a r j)
        atTop (𝓝 w) := by
  classical
  let t := s.filter (fun r => ∃ j ∈ Finset.range m, a r j ≠ 0)
  have ht : t.Nonempty := by
    obtain ⟨r, hr, j, hj, ha⟩ := hne
    exact ⟨r, Finset.mem_filter.mpr ⟨hr, j, hj, ha⟩⟩
  let μ := t.max' ht
  have hμt : μ ∈ t := t.max'_mem ht
  have hμs : μ ∈ s := (Finset.mem_filter.mp hμt).1
  have hμ : 0 < μ := hpos μ hμs
  let u := (Finset.range m).filter (fun j => a μ j ≠ 0)
  have hu : u.Nonempty := by
    obtain ⟨j, hj, ha⟩ := (Finset.mem_filter.mp hμt).2
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, ha⟩⟩
  let k := u.max' hu
  have hku : k ∈ u := u.max'_mem hu
  have hkm : k ∈ Finset.range m := (Finset.mem_filter.mp hku).1
  have hak : a μ k ≠ 0 := (Finset.mem_filter.mp hku).2
  refine ⟨μ, hμ, k, a μ k, hak, ?_⟩
  have hratio (r : ℝ) (j : ℕ) (hr : r ∈ s) (ha : a r j ≠ 0)
      (hj : j ∈ Finset.range m) :
      Tendsto (fun n : ℕ => (μ ^ n * (n : ℝ) ^ k)⁻¹ *
        (r ^ n * (n : ℝ) ^ j)) atTop
        (𝓝 (if r = μ ∧ j = k then (1 : ℝ) else 0)) := by
    have hrμ : r ≤ μ := t.le_max' r (Finset.mem_filter.mpr ⟨hr, j, hj, ha⟩)
    rcases hrμ.eq_or_lt with rfl | hrμ
    · have hjk : j ≤ k := u.le_max' j (Finset.mem_filter.mpr ⟨hj, ha⟩)
      rcases hjk.eq_or_lt with rfl | hjk
      · simp only [and_self, ite_true]
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        exact (inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero n hμ.ne') (pow_ne_zero k hn0))).symm
      · simp only [true_and, ne_of_lt hjk, ite_false]
        have ht0 := tendsto_const_div_pow 1 (k - j) (Nat.sub_ne_zero_of_lt hjk)
        apply ht0.congr'
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
        have hk : (n : ℝ) ^ k = (n : ℝ) ^ j * (n : ℝ) ^ (k - j) := by
          rw [← pow_add, Nat.add_sub_of_le hjk.le]
        rw [hk]
        field_simp
    · have hlt : r / μ < 1 := (div_lt_one hμ).mpr hrμ
      have hge : 0 ≤ r / μ := (div_pos (hpos r hr) hμ).le
      have ht0 := tendsto_pow_const_mul_const_pow_of_lt_one j hge hlt
      have hnorm : ∃ c : ℝ, Tendsto (fun n : ℕ => ((n : ℝ) ^ k)⁻¹)
          atTop (𝓝 c) := by
        by_cases hk : k = 0
        · exact ⟨1, by simp [hk]⟩
        · exact ⟨0, by simpa using tendsto_const_div_pow 1 k hk⟩
      obtain ⟨c, hc⟩ := hnorm
      have ht := ht0.mul hc
      simp only [zero_mul] at ht
      simp only [ne_of_lt hrμ, false_and, ite_false]
      convert ht using 1
      funext n
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  have hsum := tendsto_finset_sum s (fun r hr =>
    tendsto_finset_sum (Finset.range m) (fun j hj => show
      Tendsto (fun n : ℕ => (μ ^ n * (n : ℝ) ^ k)⁻¹ •
        ((r ^ n * (n : ℝ) ^ j) • a r j)) atTop
        (𝓝 (if r = μ ∧ j = k then a μ k else 0)) from by
      by_cases ha : a r j = 0
      · have hnot : ¬ (r = μ ∧ j = k) := by
          rintro ⟨rfl, rfl⟩
          exact hak ha
        simp [ha, hnot]
      · have ht := (hratio r j hr ha hj).smul_const (a r j)
        by_cases h : r = μ ∧ j = k
        · rcases h with ⟨rfl, rfl⟩
          simpa only [and_self, ite_true, one_smul, smul_smul] using ht
        · simpa only [h, ite_false, zero_smul, smul_smul] using ht))
  simpa [Finset.smul_sum, ite_and, hμs, hkm] using hsum

/-- Step 8 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"in the Plücker embedding" and "any nonzero vector u". The wedge of a
linearly independent frame is nonzero, including the empty frame in degree zero. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step8_plucker_nonzero
    {d k : ℕ} (v : Fin k → E d)
    (hv : LinearIndependent ℝ v) : exteriorPower.ιMulti ℝ k v ≠ 0 := by
  have hi := exteriorPower.ιMulti_family_linearIndependent_field (n := k) hv
  have hn := hi.ne_zero (Set.powersetCard.ofFinEmbEquiv
    (OrderEmbedding.ofStrictMono (fun i : Fin k => i) (fun _ _ h => h)))
  simpa only [exteriorPower.ιMulti_family, Equiv.symm_apply_apply,
    OrderEmbedding.coe_ofStrictMono, Function.comp_id] using hn

/-- Step 9 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"in the Plücker embedding". Choose a nonzero exterior coordinate and
contract against all but one of its covectors. The resulting k linear maps
give an independent frame at that coordinate; on a decomposable vector,
the frame lies in the subspace represented by the vector. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step9_plucker_chart
    {d k : ℕ} (w : ⋀[ℝ]^k (E d)) (hw : w ≠ 0) :
    ∃ B : (⋀[ℝ]^k (E d)) →ₗ[ℝ] (Fin k → E d),
      LinearIndependent ℝ (B w) ∧
      ∀ (v : Fin k → E d) (i : Fin k),
        B (exteriorPower.ιMulti ℝ k v) i ∈ Submodule.span ℝ (Set.range v) := by
  classical
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  have hrepr : (b.exteriorPower k).repr w ≠ 0 :=
    (b.exteriorPower k).repr.map_ne_zero_iff.mpr hw
  obtain ⟨s, hs⟩ : ∃ s, (b.exteriorPower k).repr w s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hrepr (Finsupp.ext h)
  let φ : Fin k → Module.Dual ℝ (E d) := fun i =>
    b.coord (Set.powersetCard.ofFinEmbEquiv.symm s i)
  let A := exteriorPower.alternatingMapToDual ℝ (E d) k
  have hAw : A φ w ≠ 0 := by
    simpa only [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual,
      exteriorPower.ιMulti_family, exteriorPower.pairingDual,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, φ, A] using hs
  let C : Fin k → Module.Dual ℝ (E d) →ₗ[ℝ] Module.Dual ℝ (⋀[ℝ]^k (E d)) :=
    fun i => A.toMultilinearMap.toLinearMap φ i
  let B : (⋀[ℝ]^k (E d)) →ₗ[ℝ] (Fin k → E d) :=
    LinearMap.pi (fun i => (Module.evalEquiv ℝ (E d)).symm.toLinearMap.comp (C i).flip)
  have hB (x : ⋀[ℝ]^k (E d)) (i : Fin k) (ℓ : Module.Dual ℝ (E d)) :
      ℓ (B x i) = A (Function.update φ i ℓ) x := by
    simp only [B, LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.apply_evalEquiv_symm_apply, LinearMap.flip_apply, C,
      MultilinearMap.toLinearMap_apply]
    rfl
  refine ⟨B, ?_, ?_⟩
  · apply LinearIndependent.of_pairwise_dual_eq_zero_one _
      (fun i => (A φ w)⁻¹ • φ i)
    · intro i j hij
      rw [LinearMap.smul_apply, hB, A.map_update_self φ hij.symm]
      simp
    · intro i
      rw [LinearMap.smul_apply, hB, Function.update_eq_self]
      exact inv_mul_cancel₀ hAw
  · intro v i
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp
    intro ℓ hℓ
    rw [hB]
    change exteriorPower.alternatingMapToDual ℝ (E d) k
      (Function.update φ i ℓ) (exteriorPower.ιMulti ℝ k v) = 0
    rw [exteriorPower.alternatingMapToDual_apply_ιMulti]
    apply Matrix.det_eq_zero_of_column_eq_zero i
    intro j
    simp only [Matrix.of_apply, Function.update_self]
    exact (Submodule.mem_dualAnnihilator ℓ).mp hℓ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- Step 10 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"converges in the Grassmannian". The Gram operator f* f of an injective
map is invertible, since its kernel equals the kernel of f. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step10_gram_unit
    {d k : ℕ} (f : E k →L[ℝ] E d)
    (hf : Function.Injective f) : IsUnit (f.adjoint.comp f) := by
  have hinj : Function.Injective (f.adjoint.comp f) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change (f.adjoint.comp f) x = 0 at hx
    apply hf
    rw [map_zero]
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [← f.adjoint_inner_right x (f x)]
    change inner ℝ x ((f.adjoint.comp f) x) = 0
    rw [hx, inner_zero_right]
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- Step 11 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"converges in the Grassmannian". In frame coordinates the orthogonal
projection onto the image of f is f (f* f)⁻¹ f*; the formula follows from
its range and orthogonality properties. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step11_projection_gram
    {d k : ℕ} (f : E k →L[ℝ] E d)
    (hf : IsUnit (f.adjoint.comp f)) :
    f.toLinearMap.range.starProjection =
      f.comp ((Ring.inverse (f.adjoint.comp f)).comp f.adjoint) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨_, rfl⟩
  · rintro y ⟨z, rfl⟩
    change inner ℝ (x - f (Ring.inverse (f.adjoint.comp f) (f.adjoint x))) (f z) = 0
    rw [← f.adjoint_inner_left z]
    have hcancel : (f.adjoint.comp f)
        (Ring.inverse (f.adjoint.comp f) (f.adjoint x)) = f.adjoint x := by
      exact congrArg (fun T : E k →L[ℝ] E k => T (f.adjoint x))
        (Ring.mul_inverse_cancel _ hf)
    change f.adjoint (f (Ring.inverse (f.adjoint.comp f) (f.adjoint x))) = f.adjoint x at hcancel
    simp only [map_sub]
    rw [hcancel, sub_self, inner_zero_left]

open Filter Topology in
/-- Step 12 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"converges in the Grassmannian". Invertible Gram operators form an open
set and inversion is continuous there, so projections depend continuously
in operator norm on an injective limiting map. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step12_projection_continuity
    {d k : ℕ}
    (f : ℕ → E k →L[ℝ] E d) (g : E k →L[ℝ] E d)
    (hg : Function.Injective g) (hfg : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => (f n).toLinearMap.range.starProjection) atTop
      (𝓝 g.toLinearMap.range.starProjection) := by
  let G := fun f : E k →L[ℝ] E d => f.adjoint.comp f
  let P := fun f : E k →L[ℝ] E d => f.comp ((Ring.inverse (G f)).comp f.adjoint)
  have hG : Continuous G := ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id
  have hunit : IsUnit (G g) := L_fixes_directions_sides_step2_spectral_limit_step10_gram_unit g hg
  have hinv : ContinuousAt Ring.inverse (G g) := by
    simpa only [hunit.unit_spec] using NormedRing.inverse_continuousAt hunit.unit
  have hP : ContinuousAt P g := continuousAt_id.clm_comp
    ((hinv.comp hG.continuousAt).clm_comp ContinuousLinearMap.adjoint.continuous.continuousAt)
  have hevent : ∀ᶠ n in atTop, IsUnit (G (f n)) :=
    (hG.continuousAt.tendsto.comp hfg).eventually (Units.isOpen.mem_nhds hunit)
  rw [L_fixes_directions_sides_step2_spectral_limit_step11_projection_gram g hunit]
  apply (hP.tendsto.comp hfg).congr'
  filter_upwards [hevent] with n hn
  exact (L_fixes_directions_sides_step2_spectral_limit_step11_projection_gram (f n) hn).symm

open Filter Topology in
/-- Step 13 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"converges in the Grassmannian". Regard a frame as the columns of a
linear map; convergence to an independent frame therefore implies
operator-norm convergence of the projections onto its span. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step13_frame_projection_limit
    {d k : ℕ}
    (v : ℕ → Fin k → E d) (w : Fin k → E d)
    (hw : LinearIndependent ℝ w) (hlim : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => (Submodule.span ℝ (Set.range (v n))).starProjection)
      atTop (𝓝 (Submodule.span ℝ (Set.range w)).starProjection) := by
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let T : (Fin k → E d) ≃ₗ[ℝ] (E k →L[ℝ] E d) :=
    (b.constr ℝ).trans LinearMap.toContinuousLinearMap
  have hinj : Function.Injective (T w) := by
    intro x y h
    apply b.repr.injective
    apply hw.finsuppLinearCombination_injective
    change (b.constr ℝ w) x = (b.constr ℝ w) y at h
    simpa only [Module.Basis.constr_apply, Finsupp.linearCombination_apply] using h
  have hTlim : Tendsto (fun n => T (v n)) atTop (𝓝 (T w)) :=
    T.continuous_of_finiteDimensional.continuousAt.tendsto.comp hlim
  have h := L_fixes_directions_sides_step2_spectral_limit_step12_projection_continuity (fun n => T (v n)) (T w) hinj hTlim
  simpa only [T, LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap,
    Module.Basis.constr_range] using h

open Filter Topology in
/-- Step 14 of the V4 proof of `L_fixes_directions_sides_step2_spectral_limit` (V4 1.16(b)):
"the limit of decomposable vectors is decomposable because the
Grassmannian is closed". Apply a Plücker chart to the nonzero limiting
vector. Its frames converge and are eventually independent; inclusion and
equality of dimensions identify their spans with the original subspaces. -/
private theorem L_fixes_directions_sides_step2_spectral_limit_step14_projection_limit
    {d k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : (⋀[ℝ]^k (E d)) ≃ₗ[ℝ] F)
    (v : ℕ → Fin k → E d) (hv : ∀ n, LinearIndependent ℝ (v n))
    (c : ℕ → ℝ) (w : F) (hw : w ≠ 0)
    (hlim : Tendsto (fun n => c n • e (exteriorPower.ιMulti ℝ k (v n)))
      atTop (𝓝 w)) :
    ∃ P : E d →L[ℝ] E d,
      Tendsto (fun n => (Submodule.span ℝ (Set.range (v n))).starProjection)
        atTop (𝓝 P) := by
  classical
  obtain ⟨B, hB, hmem⟩ := L_fixes_directions_sides_step2_spectral_limit_step9_plucker_chart (e.symm w) (e.symm.map_ne_zero_iff.mpr hw)
  let u := fun n => c n • B (exteriorPower.ιMulti ℝ k (v n))
  have hu : Tendsto u atTop (𝓝 (B (e.symm w))) := by
    have h := (B.comp e.symm.toLinearMap).continuous_of_finiteDimensional.continuousAt.tendsto.comp hlim
    simpa only [Function.comp_def, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul,
      LinearEquiv.symm_apply_apply] using h
  have hevent : ∀ᶠ n in atTop, LinearIndependent ℝ (u n) := hu.eventually hB.eventually
  have hspan : ∀ᶠ n in atTop,
      Submodule.span ℝ (Set.range (u n)) = Submodule.span ℝ (Set.range (v n)) := by
    filter_upwards [hevent] with n hn
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (Submodule.span ℝ (Set.range (v n))).smul_mem (c n) (hmem (v n) i)
    · rw [finrank_span_eq_card hn, finrank_span_eq_card (hv n)]
  refine ⟨(Submodule.span ℝ (Set.range (B (e.symm w)))).starProjection, ?_⟩
  apply (L_fixes_directions_sides_step2_spectral_limit_step13_frame_projection_limit u (B (e.symm w)) hB hu).congr'
  filter_upwards [hspan] with n hn
  rw [hn]

set_option maxHeartbeats 1600000 in
omit [Fact (2 ≤ d)] in
open Filter Topology in
/-- Step 2 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"the sequence of subspaces ... converges in the Grassmannian" for positive
real spectrum. This is expressed as operator-norm convergence of orthogonal
projections. The remaining linear-algebra step is the Plücker/generalized-
eigenvector argument: select the largest eigenvalue and Jordan index in a
nonzero exterior-power vector. No group or substitution hypothesis is used. -/
private theorem L_fixes_directions_sides_step2_spectral_limit
    (L : E d ≃ₗ[ℝ] E d) (hpos : PositiveRealSpectrum L)
    (V : Submodule ℝ (E d)) :
    ∃ P : E d →L[ℝ] E d,
      Tendsto (fun n : ℕ => (V.map (L ^ n).toLinearMap).starProjection)
        atTop (𝓝 P) := by
  by_cases hbot : V = ⊥
  · subst V
    exact ⟨0, by simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E d →L[ℝ] E d))
        atTop (𝓝 0))⟩
  by_cases htop : V = ⊤
  · subst V
    exact ⟨ContinuousLinearMap.id ℝ (E d), by simpa [Submodule.starProjection_top] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => ContinuousLinearMap.id ℝ (E d))
        atTop (𝓝 (ContinuousLinearMap.id ℝ (E d))))⟩
  classical
  let k := Module.finrank ℝ V
  let b := Module.finBasis ℝ V
  let v : Fin k → E d := fun i => b i
  have hv : LinearIndependent ℝ v :=
    b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hspan : Submodule.span ℝ (Set.range v) = V := by
    rw [show Set.range v = V.subtype '' Set.range b from Set.range_comp V.subtype b,
      ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  let X := Fin (Module.finrank ℝ (⋀[ℝ]^k (E d))) → ℝ
  let e : (⋀[ℝ]^k (E d)) ≃ₗ[ℝ] X := (Module.finBasis ℝ _).equivFun
  let f : MultilinearMap ℝ (fun _ : Fin k => E d) X :=
    e.toLinearMap.compMultilinearMap (exteriorPower.ιMulti ℝ k).toMultilinearMap
  have hne : f v ≠ 0 := e.map_ne_zero_iff.mpr
    (L_fixes_directions_sides_step2_spectral_limit_step8_plucker_nonzero v hv)
  obtain ⟨hsplit, hreal⟩ := L_fixes_directions_sides_step2_spectral_limit_step1_real_splitting L.toLinearMap hpos
  choose s m a ha hexp using fun i =>
    L_fixes_directions_sides_step2_spectral_limit_step4_jordan_expansion
      L.toLinearMap hsplit hreal (v i)
  obtain ⟨t, q, c, hc, hcexp⟩ := L_fixes_directions_sides_step2_spectral_limit_step6_multilinear_expansion f s m a ha
  have hpow : ∀ n : ℕ, L.toLinearMap ^ n = (L ^ n).toLinearMap := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]
  have heq : ∀ n : ℕ, f (fun i => (L ^ n) (v i)) =
      ∑ r ∈ t, ∑ j ∈ Finset.range q, (r ^ n * (n : ℝ) ^ j) • c r j := by
    intro n
    simpa only [← hexp, hpow] using hcexp n
  have hcne : ∃ r ∈ t, ∃ j ∈ Finset.range q, c r j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    calc
      f v = f (fun i => (L ^ 0) (v i)) := by simp
      _ = ∑ r ∈ t, ∑ j ∈ Finset.range q, (r ^ 0 * ((0 : ℕ) : ℝ) ^ j) • c r j := heq 0
      _ = 0 := Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun j hj => by
        rw [h r hr j hj, smul_zero]
  obtain ⟨μ, hμ, p, w, hw, hlim⟩ := L_fixes_directions_sides_step2_spectral_limit_step7_dominant_term t q c hc hcne
  have hlim' : Tendsto (fun n : ℕ => (μ ^ n * (n : ℝ) ^ p)⁻¹ •
      e (exteriorPower.ιMulti ℝ k (fun i => (L ^ n) (v i)))) atTop (𝓝 w) := by
    simpa only [← heq] using hlim
  obtain ⟨P, hP⟩ := L_fixes_directions_sides_step2_spectral_limit_step14_projection_limit e (fun n i => (L ^ n) (v i))
    (fun n => hv.map' (L ^ n).toLinearMap (LinearEquiv.ker _))
    (fun n => (μ ^ n * (n : ℝ) ^ p)⁻¹) w hw hlim'
  refine ⟨P, ?_⟩
  have hspan' : ∀ n : ℕ, Submodule.span ℝ (Set.range (fun i => (L ^ n) (v i))) =
      V.map (L ^ n).toLinearMap := by
    intro n
    rw [show Set.range (fun i => (L ^ n) (v i)) =
      (L ^ n).toLinearMap '' Set.range v from Set.range_comp _ _,
      ← Submodule.map_span, hspan]
  simpa only [hspan'] using hP

omit [Fact (2 ≤ d)] in
/-- Step 3 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"the compact orbit H V". In the orthogonal-projection model of the
Grassmannian, every orthogonal transformation preserves distances. -/
private theorem L_fixes_directions_sides_step3_projection_distance
    (U V : Submodule ℝ (E d)) (r : Ortho d) :
    dist (U.map r.toLinearEquiv.toLinearMap).starProjection
      (V.map r.toLinearEquiv.toLinearMap).starProjection =
      dist U.starProjection V.starProjection := by
  rw [dist_eq_norm, dist_eq_norm]
  have heq : (U.map r.toLinearEquiv.toLinearMap).starProjection -
      (V.map r.toLinearEquiv.toLinearMap).starProjection =
      r.toLinearIsometry.toContinuousLinearMap.comp
        ((U.starProjection - V.starProjection).comp
          r.symm.toLinearIsometry.toContinuousLinearMap) := by
    ext x
    simp [Submodule.starProjection_map_apply]
  rw [heq, LinearIsometry.norm_toContinuousLinearMap_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

omit [Fact (2 ≤ d)] in
open Filter Topology in
/-- Step 4 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"h L^q V = h V, hence L^q V = V". Equivalently, a convergent orbit of one
rotation is constant: distances between successive projections are constant
and converge to zero. This avoids choosing a representative of the limit. -/
private theorem L_fixes_directions_sides_step4_convergent_rotation
    (r : Ortho d) (V : Submodule ℝ (E d))
    (P : E d →L[ℝ] E d)
    (hlim : Tendsto (fun n : ℕ =>
      (V.map (r ^ n).toLinearEquiv.toLinearMap).starProjection) atTop (𝓝 P)) :
    V.map r.toLinearEquiv.toLinearMap = V := by
  have hdist : ∀ n : ℕ,
      dist (V.map (r ^ (n + 1)).toLinearEquiv.toLinearMap).starProjection
        (V.map (r ^ n).toLinearEquiv.toLinearMap).starProjection =
        dist (V.map r.toLinearEquiv.toLinearMap).starProjection V.starProjection := by
    intro n
    have heq : V.map (r ^ (n + 1)).toLinearEquiv.toLinearMap =
        (V.map r.toLinearEquiv.toLinearMap).map
          (r ^ n).toLinearEquiv.toLinearMap := by
      rw [← Submodule.map_comp]
      congr 1
    simpa only [heq] using
      L_fixes_directions_sides_step3_projection_distance
        (V.map r.toLinearEquiv.toLinearMap) V (r ^ n)
  have ht := (hlim.comp (tendsto_add_atTop_nat 1)).dist hlim
  simp only [Function.comp_def, hdist, dist_self] at ht
  have hz := tendsto_nhds_unique ht tendsto_const_nhds
  exact Submodule.starProjection_inj.mp (dist_eq_zero.mp hz.symm)

omit [Fact (2 ≤ d)] in
open Filter Topology in
/-- Step 5 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"the orbit (L^m V) is periodic with period q and also convergent ... hence
constant". Commutation identifies the q-step orbit with powers of one
rotation; after that rotation fixes V, the two residue classes 0 and 1
have the same limit. -/
private theorem L_fixes_directions_sides_step5_fixed_of_convergence (L : E d ≃ₗ[ℝ] E d)
    (V : Submodule ℝ (E d)) (P : E d →L[ℝ] E d)
    (hlim : Tendsto (fun n : ℕ => (V.map (L ^ n).toLinearMap).starProjection)
      atTop (𝓝 P)) (q : ℕ) (hq : 1 ≤ q) (r : Ortho d)
    (hcomm : Commute L r.toLinearEquiv)
    (hreturn : V.map (L ^ q).toLinearMap = V.map r.toLinearEquiv.toLinearMap) :
    V.map L.toLinearMap = V := by
  have hiter : ∀ n : ℕ, V.map (L ^ (q * n)).toLinearMap =
      V.map (r ^ n).toLinearEquiv.toLinearMap := by
    intro n
    induction n with
    | zero =>
      change V.map (LinearMap.id) = V.map (LinearMap.id)
      rfl
    | succ n ih =>
      rw [Nat.mul_succ, pow_add, LinearEquiv.coe_toLinearMap_mul,
        Module.End.mul_eq_comp, Submodule.map_comp, hreturn]
      have heq : (V.map r.toLinearEquiv.toLinearMap).map (L ^ (q * n)).toLinearMap =
          (V.map (L ^ (q * n)).toLinearMap).map r.toLinearEquiv.toLinearMap := by
        simp only [← Submodule.map_comp, ← Module.End.mul_eq_comp,
          ← LinearEquiv.coe_toLinearMap_mul]
        rw [(hcomm.pow_left (q * n)).eq]
      rw [heq, ih, ← Submodule.map_comp]
      congr 1
      ext x
      simp [pow_succ']
  have hqn : Tendsto (fun n : ℕ => q * n) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega)
  have hlimr : Tendsto (fun n : ℕ =>
      (V.map (r ^ n).toLinearEquiv.toLinearMap).starProjection) atTop (𝓝 P) := by
    simpa only [Function.comp_def, hiter] using hlim.comp hqn
  have hr := L_fixes_directions_sides_step4_convergent_rotation r V P hlimr
  have hqfix : V.map (L ^ q).toLinearMap = V := hreturn.trans hr
  have hmult : ∀ n : ℕ, V.map (L ^ (q * n)).toLinearMap = V := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, pow_add, LinearEquiv.coe_toLinearMap_mul,
        Module.End.mul_eq_comp, Submodule.map_comp, hqfix, ih]
  have hmult_one : ∀ n : ℕ, V.map (L ^ (q * n + 1)).toLinearMap =
      V.map L.toLinearMap := by
    intro n
    rw [pow_succ', LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp,
      Submodule.map_comp, hmult]
  have hzero : V.starProjection = P := by
    have ht := hlim.comp hqn
    simp only [Function.comp_def, hmult] at ht
    exact tendsto_nhds_unique tendsto_const_nhds ht
  have hone : (V.map L.toLinearMap).starProjection = P := by
    have ht := hlim.comp ((tendsto_add_atTop_nat 1).comp hqn)
    simp only [Function.comp_def, hmult_one] at ht
    exact tendsto_nhds_unique tendsto_const_nhds ht
  exact Submodule.starProjection_inj.mp (hone.trans hzero.symm)

omit [Fact (2 ≤ d)] in
/-- Step 6 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"a scalar which is an eigenvalue of L ... hence positive". Apply
Cayley--Hamilton to a nonzero eigenfunctional on an invariant subspace;
this obtains a root of the ambient characteristic polynomial without
assuming that L is diagonalizable. -/
private theorem L_fixes_directions_sides_step6_functional_positive (L : E d ≃ₗ[ℝ] E d)
    (hpos : PositiveRealSpectrum L) (V : Submodule ℝ (E d))
    (hV : V.map L.toLinearMap = V) (ℓ : E d →ₗ[ℝ] ℝ)
    (u : E d) (hu : u ∈ V) (hℓu : ℓ u = 1)
    (a : ℝ) (ha : ∀ x ∈ V, ℓ (L x) = a * ℓ x) : 0 < a := by
  have hmap : ∀ x ∈ V, L x ∈ V := by
    intro x hx
    rw [← hV]
    exact Submodule.mem_map_of_mem hx
  have hpoly : ∀ p : Polynomial ℝ, ∀ x ∈ V,
      ℓ ((Polynomial.aeval L.toLinearMap p) x) = p.eval a * ℓ x := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      intro x hx
      simp only [map_add, LinearMap.add_apply, hp x hx, hq x hx,
        Polynomial.eval_add, add_mul]
    | monomial n c =>
      intro x hx
      have hpow : ∀ (n : ℕ) (y : E d), y ∈ V →
          ℓ ((L.toLinearMap ^ n) y) = a ^ n * ℓ y := by
        intro n
        induction n with
        | zero => intro y hy; simp
        | succ n ih =>
          intro y hy
          rw [pow_succ, Module.End.mul_apply]
          change ℓ ((L.toLinearMap ^ n) (L y)) = _
          rw [ih (L y) (hmap y hy), ha y hy, pow_succ, mul_assoc]
      simp [Polynomial.aeval_monomial, hpow n x hx, mul_assoc]
  have hroot : L.toLinearMap.charpoly.IsRoot a := by
    have h := hpoly L.toLinearMap.charpoly u hu
    simpa [LinearMap.aeval_self_charpoly, hℓu, Polynomial.IsRoot] using h.symm
  have hc : (L.toLinearMap.charpoly.map (algebraMap ℝ ℂ)).IsRoot (a : ℂ) :=
    Polynomial.IsRoot.map hroot
  exact (hpos a hc).2

omit [Fact (2 ≤ d)] in
/-- Step 7 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"L induces on the one-dimensional quotient V/W a scalar". Normalize the
defining functional on V and use invariance of its kernel W to construct
that scalar; the preceding step proves its strict positivity. -/
private theorem L_fixes_directions_sides_step7_functional_scalar (L : E d ≃ₗ[ℝ] E d)
    (hpos : PositiveRealSpectrum L) (V W : Submodule ℝ (E d))
    (hV : V.map L.toLinearMap = V) (hW : W.map L.toLinearMap = W)
    (hWV : W ≤ V) (hdim : Module.finrank ℝ V = Module.finrank ℝ W + 1)
    (ℓ : E d →ₗ[ℝ] ℝ)
    (hker : {x | x ∈ V ∧ ℓ x = 0} = (W : Set (E d))) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ V, ℓ (L x) = a * ℓ x := by
  have hex : ∃ x ∈ V, ℓ x ≠ 0 := by
    by_contra h
    push_neg at h
    have heq : V = W := le_antisymm (by
      intro x hx
      rw [← SetLike.mem_coe, ← hker]
      exact ⟨hx, h x hx⟩) hWV
    rw [heq] at hdim
    omega
  obtain ⟨x, hx, hℓx⟩ := hex
  let u := (ℓ x)⁻¹ • x
  have hu : u ∈ V := V.smul_mem _ hx
  have hℓu : ℓ u = 1 := by simp [u, hℓx]
  have hscalar : ∀ y ∈ V, ℓ (L y) = ℓ (L u) * ℓ y := by
    intro y hy
    have hz : y - ℓ y • u ∈ W := by
      rw [← SetLike.mem_coe, ← hker]
      exact ⟨V.sub_mem hy (V.smul_mem _ hu), by simp [hℓu]⟩
    have hLz : L (y - ℓ y • u) ∈ W := by
      rw [← hW]
      exact Submodule.mem_map_of_mem hz
    have hzero : ℓ (L (y - ℓ y • u)) = 0 := by
      have := hLz
      rw [← SetLike.mem_coe, ← hker] at this
      exact this.2
    simp only [map_sub, map_smul, smul_eq_mul] at hzero
    nlinarith
  exact ⟨ℓ (L u),
    L_fixes_directions_sides_step6_functional_positive L hpos V hV ℓ u hu hℓu _ hscalar,
    hscalar⟩

omit [Fact (2 ≤ d)] in
/-- Step 8 of the V4 proof of `L_fixes_directions_sides` (V4 1.16(b)):
"so the two sides of W in V are preserved". Multiplication of a defining
functional by a positive scalar preserves its nonnegative half-space,
and invertibility gives equality of images. -/
private theorem L_fixes_directions_sides_step8_side_image (L : E d ≃ₗ[ℝ] E d)
    (hpos : PositiveRealSpectrum L) (dirs : Set (Submodule ℝ (E d)))
    (hfix : ∀ V ∈ dirs, V.map L.toLinearMap = V)
    (K : Set (E d)) (hK : IsClosedSide dirs K) : L '' K = K := by
  obtain ⟨V, W, hV, hW, hWV, hdim, ℓ, hker, rfl⟩ := hK
  have hinv : ∀ U : Submodule ℝ (E d), U ∈ dirs ∨ U = ⊤ →
      U.map L.toLinearMap = U := by
    intro U hU
    rcases hU with hU | rfl
    · exact hfix U hU
    · simp
  have hV' := hinv V hV
  obtain ⟨a, ha, hscalar⟩ :=
    L_fixes_directions_sides_step7_functional_scalar L hpos V W hV' (hinv W hW)
      hWV hdim ℓ hker
  have hmem : ∀ x, L x ∈ V ↔ x ∈ V := by
    intro x
    nth_rw 1 [← hV']
    constructor
    · rintro ⟨z, hz, heq⟩
      exact L.injective heq ▸ hz
    · intro hx
      exact ⟨x, hx, rfl⟩
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hℓx⟩, rfl⟩
    exact ⟨(hmem x).2 hx, by rw [hscalar x hx]; positivity⟩
  · rintro ⟨hy, hℓy⟩
    have hx : L.symm y ∈ V := (hmem (L.symm y)).1 (by simpa using hy)
    refine ⟨L.symm y, ⟨hx, ?_⟩, L.apply_symm_apply y⟩
    have h := hscalar (L.symm y) hx
    rw [L.apply_symm_apply] at h
    rw [h] at hℓy
    exact nonneg_of_mul_nonneg_right hℓy ha

/-- P11, V4 1.16(b): every direction and every oriented side is fixed. -/
theorem L_fixes_directions_sides (F : PowerFactorisation S) :
    (∀ V ∈ S.hPi, V.map F.L.toLinearMap = V) ∧
      ∀ K : Set (E d), IsClosedSide S.hPi K → F.L '' K = K := by
  have hfix : ∀ V ∈ S.hPi, V.map F.L.toLinearMap = V := by
    intro V hV
    obtain ⟨q, hq, r, hr, hreturn⟩ :=
      L_fixes_directions_sides_step1_orbit_return F V hV
    obtain ⟨P, hlim⟩ := L_fixes_directions_sides_step2_spectral_limit F.L F.positive V
    exact L_fixes_directions_sides_step5_fixed_of_convergence F.L V P hlim q hq r
      (L_commutes F r hr) hreturn
  exact ⟨hfix, L_fixes_directions_sides_step8_side_image F.L F.positive S.hPi hfix⟩

/-- P11, V4 1.16(b): every finite union/intersection `HΠ`-cone is fixed. -/
theorem L_fixes_HPiCones (F : PowerFactorisation S) (K : Set (E d))
    (hK : HPiCone S.hPi K) : F.L '' K = K := by
  obtain ⟨s, rfl, h_prop⟩ := hK
  have h_inner : ∀ p ∈ s, F.L '' ⋂ C ∈ p, C = ⋂ C ∈ p, C := by
    intro p hp
    have h_eq : (F.L '' ⋂ C ∈ p, C) = ⋂ C ∈ p, F.L '' C := by
      ext x
      simp only [Set.mem_image, Set.mem_iInter]
      constructor
      · rintro ⟨y, hy, rfl⟩ C hC
        exact ⟨y, hy C hC, rfl⟩
      · intro h
        exact ⟨F.L.symm x, fun C hC => by
          have h_mem := h C hC
          rcases h_mem with ⟨y, hy, hy_eq⟩
          have h_eq2 : y = F.L.symm x := by
            apply F.L.injective
            simp [hy_eq]
          rwa [← h_eq2], by simp⟩
    rw [h_eq]
    apply le_antisymm
    · intro x hx
      simp only [Set.mem_iInter] at hx ⊢
      intro C hC
      have hxC := hx C hC
      rcases h_prop p hp C hC with ⟨V, hV, rfl⟩ | hC_side
      · rcases hV with hV_in | rfl
        · have hfix := (L_fixes_directions_sides F).1 V hV_in
          have h_eq : Submodule.map F.L.toLinearMap V = V := hfix
          rcases hxC with ⟨y, hy, rfl⟩
          have h_mem : F.L y ∈ V := by
            rw [← h_eq]
            exact Submodule.mem_map_of_mem hy
          exact h_mem
        · trivial
      · have hfix := (L_fixes_directions_sides F).2 C hC_side
        have hxC2 : x ∈ F.L '' C := hxC
        rwa [hfix] at hxC2
    · intro x hx
      simp only [Set.mem_iInter] at hx ⊢
      intro C hC
      have hxC := hx C hC
      rcases h_prop p hp C hC with ⟨V, hV, rfl⟩ | hC_side
      · rcases hV with hV_in | rfl
        · have hfix := (L_fixes_directions_sides F).1 V hV_in
          have h_eq : Submodule.map F.L.toLinearMap V = V := hfix
          have hx_map : x ∈ Submodule.map F.L.toLinearMap V := by
            rw [h_eq]
            exact hxC
          rcases hx_map with ⟨y, hy, hy_eq⟩
          exact ⟨y, hy, hy_eq⟩
        · exact ⟨F.L.symm x, trivial, F.L.apply_symm_apply x⟩
      · have hfix := (L_fixes_directions_sides F).2 C hC_side
        have hxC2 : x ∈ C := hxC
        rw [← hfix] at hxC2
        exact hxC2
  have h_eq : (F.L '' ⋃ p ∈ s, ⋂ C ∈ p, C) = ⋃ p ∈ s, F.L '' ⋂ C ∈ p, C := by
    ext x
    simp only [Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨y, ⟨p, hp, hy_in⟩, rfl⟩
      exact ⟨p, hp, ⟨y, hy_in, rfl⟩⟩
    · rintro ⟨p, hp, y, hy, rfl⟩
      exact ⟨y, ⟨p, hp, hy⟩, rfl⟩
  rw [h_eq]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨p, hp, hx⟩
    have h_p := h_inner p hp
    have hx_in : x ∈ F.L '' ⋂ C ∈ p, C := hx
    rw [h_p] at hx_in
    exact ⟨p, hp, hx_in⟩
  · rintro ⟨p, hp, hx⟩
    have h_p := h_inner p hp
    have hx_in : x ∈ ⋂ C ∈ p, C := hx
    rw [← h_p] at hx_in
    exact ⟨p, hp, hx_in⟩

/-- Step 0 of the V4 proof of `tangentCone_isHPiCone` (V4 1.16(b')): "the tangent cone
at a vertex `p` of a cell `C` of a placed prototile ..., translated to the origin":
placing by an isometric frame moves the tangent cone by the linear part of the frame. -/
private theorem tangentCone_isHPiCone_step0_transport (φ : Iso d) (X : Set (E d)) (q : E d) :
    tangentCone (φ '' X) (φ q) = φ.toAffineEquiv.linear '' tangentCone X q := by
  set L := φ.toAffineEquiv.linear
  have key : ∀ (s : ℝ) (v : E d), φ (q + s • v) = φ q + s • L v := by
    intro s v
    have h := φ.toAffineEquiv.map_vadd q (s • v)
    simp only [vadd_eq_add, map_smul, AffineIsometryEquiv.coe_toAffineEquiv] at h
    rw [add_comm, h, add_comm]
  ext w
  constructor
  · rintro ⟨ε, hε, h⟩
    refine ⟨L.symm w, ⟨ε, hε, fun s hs hsε => ?_⟩, L.apply_symm_apply w⟩
    obtain ⟨x, hx, hxe⟩ := h s hs hsε
    have : φ x = φ (q + s • L.symm w) := by rw [hxe, key, L.apply_symm_apply]
    exact φ.injective this ▸ hx
  · rintro ⟨v, ⟨ε, hε, h⟩, rfl⟩
    exact ⟨ε, hε, fun s hs hsε => ⟨q + s • v, h s hs hsε, key s v⟩⟩

/-- Step 1a of the V4 proof of `tangentCone_isHPiCone` (V4 1.16(b')): "the facets of `C`
through `p`": only finitely many listed cells exist and they are closed, so near `q` every
listed prototype cell that meets a small ball around `q` passes through `q`. -/
private theorem tangentCone_isHPiCone_step1a_local (A : S.ι) (q : E d) :
    ∃ r : ℝ, 0 < r ∧ ∀ g ∈ (S.cx A).cells, ∀ x ∈ g.carrier, dist x q < r →
      q ∈ g.carrier := by
  classical
  let B : Set (E d) :=
    ⋃ g ∈ (S.cx A).cells.filter (fun g => q ∉ g.carrier), g.carrier
  have hB : IsClosed B := isClosed_biUnion_finset fun g _ => g.flat.compact.isClosed
  have hqB : q ∉ B := by
    simp only [B, Set.mem_iUnion, Finset.mem_filter, exists_prop, not_exists, not_and]
    intro g hg hq
    exact hg.2 hq
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hB.isOpen_compl q hqB
  refine ⟨r, hr, fun g hg x hx hxq => ?_⟩
  by_contra hqg
  have hxB : x ∈ B := Set.mem_iUnion₂.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, hqg⟩, hx⟩
  exact hball (mem_ball.mpr hxq) hxB

/-- Step 1b-i of the V4 proof of `tangentCone_isHPiCone` (V4 1.16(b'), §1.0 (H2)): "the
regular closed polyhedron `C` (within `aff C`)": a cell of the same dimension as `C`
cannot lie in the relative boundary of `C`, since its relative interior would be open in
`aff C` and hence inside the relative interior of `C`. -/
private theorem tangentCone_isHPiCone_step1b_no_full {e g : Cell d}
    (hge : g.carrier ⊆ relfrontier e.carrier) (hdim : g.dim = e.dim) : False := by
  have hsub : g.carrier ⊆ e.carrier :=
    hge.trans (intrinsicFrontier_subset e.flat.compact.isClosed)
  obtain ⟨y, hy⟩ := g.flat.relint_nonempty
  have hyg : y ∈ g.carrier := intrinsicInterior_subset hy
  have hspan : affineSpan ℝ g.carrier = affineSpan ℝ e.carrier := by
    apply AffineSubspace.eq_of_direction_eq_of_nonempty_of_le _
      ⟨y, subset_affineSpan ℝ _ hyg⟩ (affineSpan_mono ℝ hsub)
    apply Submodule.eq_of_le_of_finrank_eq
      (AffineSubspace.direction_le (affineSpan_mono ℝ hsub))
    change Module.finrank ℝ (cellDirection g.carrier) =
      Module.finrank ℝ (cellDirection e.carrier)
    rw [g.flat.dimension, e.flat.dimension, hdim]
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z ∈ affineSpan ℝ g.carrier, dist z y < ρ → z ∈ g.carrier := by
    obtain ⟨y', hy', rfl⟩ := mem_intrinsicInterior.mp hy
    obtain ⟨ρ, hρ, hb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy')
    exact ⟨ρ, hρ, fun z hz hdist =>
      hb (show (⟨z, hz⟩ : affineSpan ℝ g.carrier) ∈ ball y' ρ from hdist)⟩
  have hyrel : y ∈ relint e.carrier := by
    refine mem_intrinsicInterior.mpr ⟨⟨y, subset_affineSpan ℝ _ (hsub hyg)⟩, ?_, rfl⟩
    refine mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨ρ, hρ, fun z hz => ?_⟩)
    exact hsub (hball z.1 (by rw [hspan]; exact z.2) hz)
  have hyf := hge hyg
  unfold relfrontier at hyf
  rw [← intrinsicClosure_diff_intrinsicInterior] at hyf
  exact hyf.2 hyrel

/-- Step 1b-ii' of the V4 proof of `tangentCone_isHPiCone` (V4 1.16(b')): "membership
... is constant on the chambers" (connectedness): a segment in `aff K` from a point of a
closed set `K` to a point outside `K` meets the relative boundary of `K`. -/
private theorem tangentCone_isHPiCone_step1b_segment {K : Set (E d)} (hK : IsClosed K)
    {a b : E d} (ha : a ∈ K) (hb : b ∈ affineSpan ℝ K) (hbK : b ∉ K) :
    ∃ w ∈ segment ℝ a b, w ∈ relfrontier K := by
  classical
  by_contra hno
  push_neg at hno
  have hrel : ∀ x ∈ K, x ∉ relfrontier K → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z ∈ affineSpan ℝ K, dist z x < ρ → z ∈ K := by
    intro x hx hnf
    have hx' : x ∈ closure K \ intrinsicFrontier ℝ K := ⟨subset_closure hx, hnf⟩
    rw [closure_diff_intrinsicFrontier] at hx'
    obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.mp hx'
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
    exact ⟨ρ, hρ, fun z hz hdist => hball (show (⟨z, hz⟩ : affineSpan ℝ K) ∈ ball y ρ from hdist)⟩
  have hsegP : segment ℝ a b ⊆ affineSpan ℝ K :=
    (AffineSubspace.convex _).segment_subset (subset_affineSpan ℝ K ha) hb
  let O : Set (E d) := {y | ∃ x ∈ K, ∃ ρ : ℝ, 0 < ρ ∧
    (∀ z ∈ affineSpan ℝ K, dist z x < ρ → z ∈ K) ∧ dist y x < ρ}
  have hO : IsOpen O := by
    rw [Metric.isOpen_iff]
    rintro y ⟨x, hx, ρ, hρ, hball, hyx⟩
    refine ⟨ρ - dist y x, by linarith, fun z hz => ⟨x, hx, ρ, hρ, hball, ?_⟩⟩
    have := dist_triangle z y x
    rw [mem_ball] at hz
    linarith
  have hOK : ∀ y ∈ O, y ∈ affineSpan ℝ K → y ∈ K := by
    rintro y ⟨x, hx, ρ, hρ, hball, hyx⟩ hy
    exact hball y hy hyx
  have hcover : segment ℝ a b ⊆ O ∪ Kᶜ := by
    intro x hx
    by_cases hxK : x ∈ K
    · obtain ⟨ρ, hρ, hball⟩ := hrel x hxK (hno x hx)
      exact Or.inl ⟨x, hxK, ρ, hρ, hball, by rw [dist_self]; exact hρ⟩
    · exact Or.inr hxK
  obtain ⟨x, hx, hxO, hxK⟩ := (convex_segment a b).isPreconnected O Kᶜ hO hK.isOpen_compl
    hcover ⟨a, left_mem_segment ℝ a b,
      (hcover (left_mem_segment ℝ a b)).resolve_right (fun h => h ha)⟩
    ⟨b, right_mem_segment ℝ a b, hbK⟩
  exact hxK (hOK x hxO (hsegP hx))

/-- Step 1b-ii of the V4 proof of `tangentCone_isHPiCone` (V4 1.16(b'), §1.0 (H2)(iii)):
"the regular closed polyhedron `C` (within `aff C`)": subsets of codimension at least two
do not separate, so near a relative boundary point of a set which is the closure of its
relative interior, the relative boundary is not covered by finitely many affine subspaces
of codimension `≥ 2` in `aff C`. -/
private theorem tangentCone_isHPiCone_step1b_codim_two {K : Set (E d)}
    (hreg : closure (relint K) = K) {x : E d} (hx : x ∈ relfrontier K) {m : ℕ}
    (M : Fin m → AffineSubspace ℝ (E d)) (_hM : ∀ k, M k ≤ affineSpan ℝ K)
    (hMdim : ∀ k, Module.finrank ℝ (M k).direction + 2 ≤
      Module.finrank ℝ (cellDirection K))
    {r : ℝ} (hr : 0 < r) (hcov : ∀ y ∈ relfrontier K, dist y x < r → ∃ k, y ∈ M k) :
    False := by
  classical
  have hKc : IsClosed K := by
    rw [← hreg]
    exact isClosed_closure
  have hxK : x ∈ K := intrinsicFrontier_subset hKc hx
  have hxcl : x ∈ closure (relint K) := by
    rw [hreg]
    exact hxK
  obtain ⟨z, hzrel, hxz⟩ := Metric.mem_closure_iff.mp hxcl (r / 2) (by linarith)
  have hzK : z ∈ K := intrinsicInterior_subset hzrel
  obtain ⟨y0, hy0P, hy0K, hy0x⟩ : ∃ y0 ∈ affineSpan ℝ K, y0 ∉ K ∧ dist y0 x < r / 2 := by
    obtain ⟨x', hx', rfl⟩ := mem_intrinsicFrontier.mp hx
    rw [frontier_eq_closure_inter_closure] at hx'
    obtain ⟨b', hb', hdist⟩ := Metric.mem_closure_iff.mp hx'.2 (r / 2) (by linarith)
    exact ⟨b'.1, b'.2, hb', by rw [dist_comm]; exact hdist⟩
  obtain ⟨ε0, hε0, hball0⟩ := Metric.isOpen_iff.mp hKc.isOpen_compl y0 hy0K
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = min ε0 (r / 2 - dist y0 x) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδ_def]; exact lt_min hε0 (by linarith)
  let p : Fin m → E d := fun k => if h : (M k : Set (E d)).Nonempty then h.some else z
  let D : Fin m → Submodule ℝ (E d) := fun k =>
    (M k).direction ⊔ Submodule.span ℝ {p k - z}
  have hDdim : ∀ k, Module.finrank ℝ (D k) + 1 ≤ Module.finrank ℝ (cellDirection K) := by
    intro k
    have h1 := Submodule.finrank_add_le_finrank_add_finrank (M k).direction
      (Submodule.span ℝ {p k - z})
    have h2 : Module.finrank ℝ (Submodule.span ℝ ({p k - z} : Set (E d))) ≤ 1 := by
      have := finrank_span_le_card (R := ℝ) ({p k - z} : Set (E d))
      simpa using this
    have := hMdim k
    have h3 : Module.finrank ℝ (D k) ≤ Module.finrank ℝ (M k).direction +
        Module.finrank ℝ (Submodule.span ℝ ({p k - z} : Set (E d))) := h1
    omega
  obtain ⟨u, huV, hu⟩ : ∃ u ∈ cellDirection K, ∀ k, u ∉ D k := by
    let q' : Fin m → Submodule ℝ (cellDirection K) := fun k =>
      (D k).comap (cellDirection K).subtype
    have h1 : ∀ k, q' k ≠ ⊤ := by
      intro k htop
      have hle : cellDirection K ≤ D k := by
        intro v hv
        have : (⟨v, hv⟩ : cellDirection K) ∈ q' k := htop ▸ Submodule.mem_top
        exact this
      have := Submodule.finrank_mono hle
      have := hDdim k
      omega
    have h2 : (Finset.univ : Finset (Fin m)).card < ENat.card ℝ := by
      rw [ENat.card_eq_top_of_infinite]
      exact ENat.coe_lt_top _
    have h3 := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ q' h1 h2
    obtain ⟨u, hu⟩ := (Set.ne_univ_iff_exists_notMem _).mp (Set.ssubset_univ_iff.mp h3)
    refine ⟨u.1, u.2, fun k hk => hu ?_⟩
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨k, Finset.mem_univ _, hk⟩
  let sk : Fin m → ℝ := fun k =>
    if h : ∃ s : ℝ, y0 + s • u - z ∈ D k then h.choose else 0
  obtain ⟨s, hs, hsB⟩ := (Set.Ioo_infinite (div_pos hδ
    (by positivity : (0 : ℝ) < ‖u‖ + 1))).exists_notMem_finset (Finset.univ.image sk)
  obtain ⟨y, hy_def⟩ : ∃ y : E d, y = y0 + s • u := ⟨_, rfl⟩
  have hyD : ∀ k, y - z ∉ D k := by
    intro k hk
    rw [hy_def] at hk
    have hex : ∃ s : ℝ, y0 + s • u - z ∈ D k := ⟨s, hk⟩
    have hsk : sk k = hex.choose := dif_pos hex
    have hspec := hex.choose_spec
    by_cases heq : s = hex.choose
    · exact hsB (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, by rw [hsk, heq]⟩)
    · have hdiff : (s - hex.choose) • u ∈ D k := by
        have := (D k).sub_mem hk hspec
        have e : y0 + s • u - z - (y0 + hex.choose • u - z) = (s - hex.choose) • u := by
          rw [sub_smul]
          abel
        rwa [e] at this
      exact hu k ((Submodule.smul_mem_iff (D k) (sub_ne_zero.mpr heq)).mp hdiff)
  have hyy0 : dist y y0 < δ := by
    rw [hy_def, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1.le]
    have h1 : s * (‖u‖ + 1) < δ := by
      calc s * (‖u‖ + 1) < δ / (‖u‖ + 1) * (‖u‖ + 1) := by gcongr; exact hs.2
        _ = δ := div_mul_cancel₀ _ (ne_of_gt (by positivity))
    nlinarith [hs.1, norm_nonneg u]
  have hyK : y ∉ K := hball0 (lt_of_lt_of_le hyy0 (by rw [hδ_def]; exact min_le_left _ _))
  have hyx : dist y x < r / 2 := by
    have h1 := dist_triangle y y0 x
    have h2 : δ ≤ r / 2 - dist y0 x := by rw [hδ_def]; exact min_le_right _ _
    linarith
  have hyP : y ∈ affineSpan ℝ K := by
    have := AffineSubspace.vadd_mem_of_mem_direction ((cellDirection K).smul_mem s huV) hy0P
    rw [hy_def, add_comm]
    simpa only [vadd_eq_add] using this
  obtain ⟨w, hwseg, hwf⟩ := tangentCone_isHPiCone_step1b_segment hKc hzK hyP hyK
  have hwx : dist w x < r / 2 := by
    have hz' : z ∈ ball x (r / 2) := by rw [mem_ball, dist_comm]; exact hxz
    have hy' : y ∈ ball x (r / 2) := hyx
    exact (convex_ball x (r / 2)).segment_subset hz' hy' hwseg
  obtain ⟨k, hwk⟩ := hcov w hwf (by linarith)
  obtain ⟨a', b', ha', hb', hab', hw_eq⟩ := hwseg
  have hwrel : w ∉ relint K := by
    have hwf' := hwf
    unfold relfrontier at hwf'
    rw [← intrinsicClosure_diff_intrinsicInterior] at hwf'
    exact hwf'.2
  have hb0 : b' ≠ 0 := by
    intro h0
    apply hwrel
    have ha1 : a' = 1 := by linarith
    rw [← hw_eq, h0, ha1, one_smul, zero_smul, add_zero]
    exact hzrel
  have hwz : w - z = b' • (y - z) := by
    rw [← hw_eq, show a' = 1 - b' by linarith]
    module
  have hne : (M k : Set (E d)).Nonempty := ⟨w, hwk⟩
  have hpk : p k ∈ M k := by
    simp only [p, dif_pos hne]
    exact hne.some_mem
  have hwD : w - z ∈ D k := by
    have e : w - z = (w - p k) + (p k - z) := by abel
    rw [e]
    exact (D k).add_mem (le_sup_left (a := (M k).direction)
        (AffineSubspace.vsub_mem_direction hwk hpk))
      (le_sup_right (b := Submodule.span ℝ {p k - z}) (Submodule.mem_span_singleton_self _))
  apply hyD k
  have : y - z = b'⁻¹ • (w - z) := by
    rw [hwz, smul_smul, inv_mul_cancel₀ hb0, one_smul]
  rw [this]
  exact (D k).smul_mem _ hwD

/-- Step 1b of the V4 proof of `tangentCone_isHPiCone` (V4 1.16(b'), with V4 §1.0 (H2)):
"the facets of `C` through `p`" (relative facet purity): the relative boundary of a listed
`j`-cell `C` is a `(j-1)`-manifold which is a union of listed cells (H2(ii)), so every
point of it lies on a listed codimension-one cell of `C`. -/
private theorem tangentCone_isHPiCone_step1b_facet_purity (A : S.ι) (e : Cell d)
    (he : e ∈ (S.cx A).cells) (x : E d) (hx : x ∈ relfrontier e.carrier) :
    ∃ f ∈ (S.cx A).cells, f.carrier ⊆ e.carrier ∧ f.dim + 1 = e.dim ∧ x ∈ f.carrier := by
  classical
  by_contra hno
  push_neg at hno
  obtain ⟨b, hb, hbu⟩ := (S.cx A).boundary_union e he
  let bs : Finset (Cell d) := b.filter (fun g => x ∈ g.carrier)
  let eqv := bs.equivFin
  have hgsub : ∀ g ∈ b, g.carrier ⊆ relfrontier e.carrier := fun g hg y hy => by
    rw [hbu]
    exact Set.mem_iUnion₂.mpr ⟨g, hg, hy⟩
  have hfrontsub : relfrontier e.carrier ⊆ e.carrier :=
    intrinsicFrontier_subset e.flat.compact.isClosed
  obtain ⟨r, hr, hloc⟩ := tangentCone_isHPiCone_step1a_local A x
  refine tangentCone_isHPiCone_step1b_codim_two e.flat.regularClosed hx
    (fun k => affineSpan ℝ (eqv.symm k).1.carrier)
    (fun k => affineSpan_mono ℝ
      ((hgsub _ (Finset.mem_filter.mp (eqv.symm k).2).1).trans hfrontsub))
    (fun k => ?_) hr (fun y hy hyx => ?_)
  · obtain ⟨hgb, hxg⟩ := Finset.mem_filter.mp (eqv.symm k).2
    have hge : (eqv.symm k).1.carrier ⊆ e.carrier := (hgsub _ hgb).trans hfrontsub
    have hle : (eqv.symm k).1.dim ≤ e.dim := by
      rw [← (eqv.symm k).1.flat.dimension, ← e.flat.dimension]
      exact Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hge))
    have hne : (eqv.symm k).1.dim ≠ e.dim := fun h =>
      tangentCone_isHPiCone_step1b_no_full (hgsub _ hgb) h
    have hne' : (eqv.symm k).1.dim + 1 ≠ e.dim := fun h => hno _ (hb hgb) hge h hxg
    change Module.finrank ℝ (cellDirection (eqv.symm k).1.carrier) + 2 ≤
      Module.finrank ℝ (cellDirection e.carrier)
    rw [e.flat.dimension, (eqv.symm k).1.flat.dimension]
    omega
  · have hy' := hy
    rw [hbu] at hy'
    obtain ⟨g, hgb, hyg⟩ := Set.mem_iUnion₂.mp hy'
    have hxg : x ∈ g.carrier := hloc g (hb hgb) y hyg hyx
    have hgbs : g ∈ bs := Finset.mem_filter.mpr ⟨hgb, hxg⟩
    refine ⟨eqv ⟨g, hgbs⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact subset_affineSpan ℝ _ hyg

/-- Step 1c of the V4 proof of `tangentCone_isHPiCone` (V4 1.16(b')): "the direction
spaces of the facets of `C`" are codimension-one subspaces `W ≤ V`, each cut out in `V`
by a linear functional. -/
private theorem tangentCone_isHPiCone_step1c_functional {V W : Submodule ℝ (E d)}
    (hWV : W ≤ V) (hdim : Module.finrank ℝ V = Module.finrank ℝ W + 1) :
    ∃ ℓ : E d →ₗ[ℝ] ℝ, {x | x ∈ V ∧ ℓ x = 0} = (W : Set (E d)) := by
  have hlt : W < V := lt_of_le_of_ne hWV (by
    intro h
    rw [h] at hdim
    omega)
  obtain ⟨u, huV, huW⟩ := SetLike.exists_of_lt hlt
  obtain ⟨f, hfu, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem huW inferInstance
  have hWker : ∀ w ∈ W, f w = 0 := by
    intro w hw
    have h : f w ∈ W.map f := Submodule.mem_map_of_mem hw
    rw [hfW] at h
    exact (Submodule.mem_bot ℝ).mp h
  have hsup : W ⊔ Submodule.span ℝ {u} = V := by
    apply Submodule.eq_of_le_of_finrank_le
      (sup_le hWV ((Submodule.span_singleton_le_iff_mem _ _).mpr huV))
    have hlt' : W < W ⊔ Submodule.span ℝ {u} := lt_of_le_of_ne le_sup_left (by
      intro h
      apply huW
      rw [h]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self u))
    have := Submodule.finrank_lt_finrank_of_lt hlt'
    omega
  refine ⟨f, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨hxV, hx0⟩
    rw [← hsup] at hxV
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hxV
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_add, map_smul, hWker w hw, zero_add, smul_eq_mul] at hx0
    have hc : c = 0 := by
      rcases mul_eq_zero.mp hx0 with h | h
      · exact h
      · exact absurd h hfu
    subst hc
    simpa using hw
  · intro hxW
    exact ⟨hWV hxW, hWker x hxW⟩

/-- Step 1 of the V4 proof of `tangentCone_isHPiCone` (V4 1.16(b')): "with `V` the
direction space of `C`, membership in the regular closed polyhedron `C` (within `aff C`)
is constant on the chambers of the arrangement in `V` of the direction spaces of the
facets of `C` through `p`". Geometric input: near a point `q` of a listed prototype cell
`e`, the relative boundary of `e` lies on the walls `q + W`, where `W` runs over the
direction spaces of the listed codimension-one cells of `e` through `q`; each wall is cut
out in `V` by a linear functional. Assembled from Steps 1a--1c. -/
private theorem tangentCone_isHPiCone_step1_walls (A : S.ι) (e : Cell d)
    (he : e ∈ (S.cx A).cells) (q : E d) (_hq : q ∈ e.carrier) :
    ∃ (n : ℕ) (f : Fin n → Cell d) (ℓ : Fin n → E d →ₗ[ℝ] ℝ),
      (∀ i, f i ∈ (S.cx A).cells ∧ (f i).carrier ⊆ e.carrier ∧ q ∈ (f i).carrier ∧
        (f i).dim + 1 = e.dim ∧
        {x | x ∈ cellDirection e.carrier ∧ ℓ i x = 0} =
          (cellDirection (f i).carrier : Set (E d))) ∧
      ∃ r : ℝ, 0 < r ∧ ∀ x ∈ relfrontier e.carrier, dist x q < r →
        ∃ i, ℓ i (x - q) = 0 := by
  classical
  let Fs : Finset (Cell d) := (S.cx A).cells.filter
    (fun f => f.carrier ⊆ e.carrier ∧ q ∈ f.carrier ∧ f.dim + 1 = e.dim)
  let eqv := Fs.equivFin
  let f : Fin Fs.card → Cell d := fun i => (eqv.symm i).1
  have hfmem : ∀ i, f i ∈ Fs := fun i => (eqv.symm i).2
  have hwall : ∀ i, ∃ ℓ : E d →ₗ[ℝ] ℝ, {x | x ∈ cellDirection e.carrier ∧ ℓ x = 0} =
      (cellDirection (f i).carrier : Set (E d)) := by
    intro i
    obtain ⟨_, hsub, _, hdim⟩ := Finset.mem_filter.mp (hfmem i)
    exact tangentCone_isHPiCone_step1c_functional
      (AffineSubspace.direction_le (affineSpan_mono ℝ hsub))
      (by rw [e.flat.dimension, (f i).flat.dimension]; omega)
  choose ℓ hℓ using hwall
  obtain ⟨r, hr, hloc⟩ := tangentCone_isHPiCone_step1a_local A q
  refine ⟨Fs.card, f, ℓ, fun i => ?_, r, hr, fun x hx hxq => ?_⟩
  · obtain ⟨hcell, hsub, hq', hdim⟩ := Finset.mem_filter.mp (hfmem i)
    exact ⟨hcell, hsub, hq', hdim, hℓ i⟩
  · obtain ⟨g, hg, hsub, hdim, hxg⟩ :=
      tangentCone_isHPiCone_step1b_facet_purity A e he x hx
    have hqg : q ∈ g.carrier := hloc g hg x hxg hxq
    have hgF : g ∈ Fs := Finset.mem_filter.mpr ⟨hg, hsub, hqg, hdim⟩
    refine ⟨eqv ⟨g, hgF⟩, ?_⟩
    have hfi : f (eqv ⟨g, hgF⟩) = g := by simp [f]
    have hmem : x - q ∈ cellDirection (f (eqv ⟨g, hgF⟩)).carrier := by
      rw [hfi]
      exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hxg)
        (subset_affineSpan ℝ _ hqg)
    have : x - q ∈ ({x | x ∈ cellDirection e.carrier ∧
        ℓ (eqv ⟨g, hgF⟩) x = 0} : Set (E d)) := by
      rw [hℓ]
      exact hmem
    exact this.2

/-- Step 2 of the V4 proof of `tangentCone_isHPiCone` (V4 1.16(b')): "membership in
the regular closed polyhedron `C` (within `aff C`) is constant on the chambers".
Generic form: if near `q` the relative boundary of a closed set `K ∋ q` lies on the
walls `ℓ i (x - q) = 0`, then membership of `q + v` in `K` is the same for all `v`
of norm `< r` in one open chamber of the direction space of `K`. -/
private theorem tangentCone_isHPiCone_step2_chamber_const {K : Set (E d)}
    (hK : IsClosed K) {q : E d} (hq : q ∈ K) {n : ℕ} (ℓ : Fin n → E d →ₗ[ℝ] ℝ) {r : ℝ}
    (hwall : ∀ x ∈ relfrontier K, dist x q < r → ∃ i, ℓ i (x - q) = 0)
    (σ : Fin n → Bool) {v w : E d} (hv : v ∈ cellDirection K) (hw : w ∈ cellDirection K)
    (hvσ : ∀ i, 0 < (if σ i then (1 : ℝ) else -1) * ℓ i v)
    (hwσ : ∀ i, 0 < (if σ i then (1 : ℝ) else -1) * ℓ i w)
    (hvr : ‖v‖ < r) (hwr : ‖w‖ < r) : q + v ∈ K ↔ q + w ∈ K := by
  classical
  have hrel : ∀ x ∈ K, x ∉ relfrontier K → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ z ∈ affineSpan ℝ K, dist z x < ρ → z ∈ K := by
    intro x hx hnf
    have hx' : x ∈ closure K \ intrinsicFrontier ℝ K := ⟨subset_closure hx, hnf⟩
    rw [closure_diff_intrinsicFrontier] at hx'
    obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.mp hx'
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
    exact ⟨ρ, hρ, fun z hz hdist => hball (show (⟨z, hz⟩ : affineSpan ℝ K) ∈ ball y ρ from hdist)⟩
  have hseg : ∀ x ∈ segment ℝ (q + v) (q + w), x ∈ affineSpan ℝ K ∧ x ∉ relfrontier K := by
    rintro x ⟨a, b, ha, hb, hab, rfl⟩
    have hxq : a • (q + v) + b • (q + w) = (a • v + b • w) + q := by
      have h1 : a • (q + v) + b • (q + w) = (a • v + b • w) + (a + b) • q := by module
      rw [h1, hab, one_smul]
    have huV : a • v + b • w ∈ cellDirection K :=
      (cellDirection K).add_mem ((cellDirection K).smul_mem a hv) ((cellDirection K).smul_mem b hw)
    have hur : ‖a • v + b • w‖ < r := by
      have := (convex_ball (0 : E d) r) (mem_ball_zero_iff.mpr hvr) (mem_ball_zero_iff.mpr hwr)
        ha hb hab
      exact mem_ball_zero_iff.mp this
    have huσ : ∀ i, ℓ i (a • v + b • w) ≠ 0 := by
      intro i h0
      have h1 := hvσ i
      have h2 := hwσ i
      have hlin : (if σ i then (1 : ℝ) else -1) * ℓ i (a • v + b • w) =
          a * ((if σ i then (1 : ℝ) else -1) * ℓ i v) +
            b * ((if σ i then (1 : ℝ) else -1) * ℓ i w) := by
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        ring
      rw [h0, mul_zero] at hlin
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        rw [ha0, hb1] at hlin
        linarith
      · have := mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) h1
        nlinarith [mul_nonneg hb h2.le]
    refine ⟨?_, fun hf => ?_⟩
    · rw [hxq]
      have := AffineSubspace.vadd_mem_of_mem_direction huV (subset_affineSpan ℝ K hq)
      simpa only [vadd_eq_add] using this
    · obtain ⟨i, hi⟩ := hwall _ hf (by rw [hxq, dist_eq_norm, add_sub_cancel_right]; exact hur)
      rw [hxq, add_sub_cancel_right] at hi
      exact huσ i hi
  let O : Set (E d) := {y | ∃ x ∈ K, ∃ ρ : ℝ, 0 < ρ ∧
    (∀ z ∈ affineSpan ℝ K, dist z x < ρ → z ∈ K) ∧ dist y x < ρ}
  have hO : IsOpen O := by
    rw [Metric.isOpen_iff]
    rintro y ⟨x, hx, ρ, hρ, hball, hyx⟩
    refine ⟨ρ - dist y x, by linarith, fun z hz => ⟨x, hx, ρ, hρ, hball, ?_⟩⟩
    have := dist_triangle z y x
    rw [mem_ball] at hz
    linarith
  have hOK : ∀ y ∈ O, y ∈ affineSpan ℝ K → y ∈ K := by
    rintro y ⟨x, hx, ρ, hρ, hball, hyx⟩ hy
    exact hball y hy hyx
  have hT := (convex_segment (q + v) (q + w)).isPreconnected
  have hcover : segment ℝ (q + v) (q + w) ⊆ O ∪ Kᶜ := by
    intro x hx
    by_cases hxK : x ∈ K
    · obtain ⟨ρ, hρ, hball⟩ := hrel x hxK (hseg x hx).2
      exact Or.inl ⟨x, hxK, ρ, hρ, hball, by rw [dist_self]; exact hρ⟩
    · exact Or.inr hxK
  have key : ∀ x ∈ segment ℝ (q + v) (q + w), x ∈ O → x ∈ Kᶜ → False :=
    fun x hx hxO hxK => hxK (hOK x hxO (hseg x hx).1)
  have hvs := left_mem_segment ℝ (q + v) (q + w)
  have hws := right_mem_segment ℝ (q + v) (q + w)
  constructor
  · intro hvK
    by_contra hwK
    obtain ⟨x, hx, hxO, hxK⟩ := hT O Kᶜ hO hK.isOpen_compl hcover
      ⟨q + v, hvs, (hcover hvs).resolve_right (fun h => h hvK)⟩ ⟨q + w, hws, hwK⟩
    exact key x hx hxO hxK
  · intro hwK
    by_contra hvK
    obtain ⟨x, hx, hxO, hxK⟩ := hT O Kᶜ hO hK.isOpen_compl hcover
      ⟨q + w, hws, (hcover hws).resolve_right (fun h => h hwK)⟩ ⟨q + v, hvs, hvK⟩
    exact key x hx hxO hxK

/-- Step 3 of the V4 proof of `tangentCone_isHPiCone` (V4 1.16(b')): "so near `p` the
cell is a union of such chambers, each a finite intersection of closed sides in `V`".
Generic form: for a closed set `K ∋ q`, regular closed in its affine span, whose
membership is constant on the open chambers (of radius `r`) of finitely many walls
nondegenerate on the direction space `V`, the tangent cone at `q` is the union of the
closed chambers whose open chamber meets `K - q` near `0`. -/
private theorem tangentCone_isHPiCone_step3_cone_eq {K : Set (E d)} (hK : IsClosed K)
    (hreg : closure (relint K) = K) {q : E d} (hq : q ∈ K) {n : ℕ}
    (ℓ : Fin n → E d →ₗ[ℝ] ℝ) (hnd : ∀ i, ∃ u ∈ cellDirection K, ℓ i u ≠ 0)
    {r : ℝ} (hr : 0 < r)
    (hconst : ∀ (σ : Fin n → Bool) (v w : E d), v ∈ cellDirection K →
      w ∈ cellDirection K →
      (∀ i, 0 < (if σ i then (1 : ℝ) else -1) * ℓ i v) →
      (∀ i, 0 < (if σ i then (1 : ℝ) else -1) * ℓ i w) →
      ‖v‖ < r → ‖w‖ < r → (q + v ∈ K ↔ q + w ∈ K)) :
    tangentCone K q = ⋃ (σ : Fin n → Bool) (_ : ∃ v ∈ cellDirection K,
        (∀ i, 0 < (if σ i then (1 : ℝ) else -1) * ℓ i v) ∧ ‖v‖ < r ∧ q + v ∈ K),
      {v | v ∈ cellDirection K ∧ ∀ i, 0 ≤ (if σ i then (1 : ℝ) else -1) * ℓ i v} := by
  classical
  have hdirK : ∀ x ∈ K, x - q ∈ cellDirection K := fun x hx =>
    AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K hx) (subset_affineSpan ℝ K hq)
  have hgen : ∃ u ∈ cellDirection K, ∀ i, ℓ i u ≠ 0 := by
    let p : Fin n → Submodule ℝ (cellDirection K) := fun i =>
      LinearMap.ker ((ℓ i).comp (cellDirection K).subtype)
    have h1 : ∀ i, p i ≠ ⊤ := by
      intro i htop
      obtain ⟨u, hu, hne⟩ := hnd i
      have : (⟨u, hu⟩ : cellDirection K) ∈ p i := htop ▸ Submodule.mem_top
      exact hne (by simpa [p] using this)
    have h2 : (Finset.univ : Finset (Fin n)).card < ENat.card ℝ := by
      rw [ENat.card_eq_top_of_infinite]
      exact ENat.coe_lt_top _
    have h3 := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ p h1 h2
    obtain ⟨u, hu⟩ := (Set.ne_univ_iff_exists_notMem _).mp (Set.ssubset_univ_iff.mp h3)
    refine ⟨u.1, u.2, fun i hi => hu ?_⟩
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨i, Finset.mem_univ _, by simpa [p] using hi⟩
  ext v
  constructor
  · rintro ⟨ε, hε, h⟩
    have hvV : v ∈ cellDirection K := by
      have h1 := hdirK _ (h (ε / 2) (by linarith) (by linarith))
      rw [add_sub_cancel_left] at h1
      have h2 := (cellDirection K).smul_mem (ε / 2)⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at h2
    obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = min (ε / 2) (r / (2 * (‖v‖ + 1))) := ⟨_, rfl⟩
    have ht0 : 0 < t := by rw [ht_def]; exact lt_min (by linarith) (by positivity)
    have htε : t < ε := by
      rw [ht_def]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htv : ‖t • v‖ < r := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le]
      have h1 : t ≤ r / (2 * (‖v‖ + 1)) := by rw [ht_def]; exact min_le_right _ _
      have h2 : t * (2 * (‖v‖ + 1)) ≤ r := by
        calc t * (2 * (‖v‖ + 1)) ≤ r / (2 * (‖v‖ + 1)) * (2 * (‖v‖ + 1)) := by gcongr
          _ = r := div_mul_cancel₀ _ (ne_of_gt (by positivity))
      nlinarith [norm_nonneg v]
    have hxK : q + t • v ∈ K := h t ht0 htε
    let U : Set (E d) := ball q r ∩ ⋂ i, {y | ℓ i v ≠ 0 → 0 < ℓ i (y - q) * ℓ i v}
    have hUo : IsOpen U := by
      refine isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
      by_cases hi : ℓ i v = 0
      · simp [hi]
      · simp only [ne_eq, hi, not_false_eq_true, true_implies]
        exact isOpen_lt continuous_const
          (((ℓ i).continuous_of_finiteDimensional.comp
            (continuous_id.sub continuous_const)).mul continuous_const)
    have hxU : q + t • v ∈ U := by
      refine ⟨by rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact htv, ?_⟩
      simp only [Set.mem_iInter, Set.mem_setOf_eq, add_sub_cancel_left, map_smul, smul_eq_mul]
      intro i hi
      have : 0 < ℓ i v * ℓ i v := mul_self_pos.mpr hi
      nlinarith
    rw [← hreg] at hxK
    obtain ⟨y, hyU, hyrel⟩ := mem_closure_iff.mp hxK U hUo hxU
    obtain ⟨ρ, hρ, hball⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ affineSpan ℝ K, dist z y < ρ → z ∈ K := by
      obtain ⟨y', hy', rfl⟩ := mem_intrinsicInterior.mp hyrel
      obtain ⟨ρ, hρ, hb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy')
      exact ⟨ρ, hρ, fun z hz hdist =>
        hb (show (⟨z, hz⟩ : affineSpan ℝ K) ∈ ball y' ρ from hdist)⟩
    have hyK : y ∈ K := intrinsicInterior_subset hyrel
    obtain ⟨ρ', hρ', hball'⟩ := Metric.isOpen_iff.mp hUo y hyU
    obtain ⟨u, huV, hu⟩ := hgen
    obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = min ρ ρ' / (‖u‖ + 1) := ⟨_, rfl⟩
    have hη : 0 < η := by rw [hη_def]; exact div_pos (lt_min hρ hρ') (by positivity)
    obtain ⟨s, hs, hsB⟩ := (Set.Ioo_infinite hη).exists_notMem_finset
      (Finset.univ.image fun i => -ℓ i (y - q) / ℓ i u)
    obtain ⟨z, hz_def⟩ : ∃ z : E d, z = y + s • u := ⟨_, rfl⟩
    have hsu : s * ‖u‖ < min ρ ρ' := by
      have h1 : s * (‖u‖ + 1) < min ρ ρ' := by
        calc s * (‖u‖ + 1) < η * (‖u‖ + 1) := by gcongr; exact hs.2
          _ = min ρ ρ' := by rw [hη_def]; exact div_mul_cancel₀ _ (ne_of_gt (by positivity))
      nlinarith [hs.1]
    have hzy : dist z y < min ρ ρ' := by
      rw [hz_def, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1.le]
      exact hsu
    have hzspan : z ∈ affineSpan ℝ K := by
      have := AffineSubspace.vadd_mem_of_mem_direction ((cellDirection K).smul_mem s huV)
        (subset_affineSpan ℝ K hyK)
      rw [hz_def, add_comm]
      simpa only [vadd_eq_add] using this
    have hzK : z ∈ K := hball z hzspan (lt_of_lt_of_le hzy (min_le_left _ _))
    have hzU : z ∈ U := hball' (lt_of_lt_of_le hzy (min_le_right _ _))
    have hzne : ∀ i, ℓ i (z - q) ≠ 0 := by
      intro i h0
      apply hsB
      refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
      have h1 : ℓ i (z - q) = ℓ i (y - q) + s * ℓ i u := by
        rw [hz_def, show y + s • u - q = (y - q) + s • u by abel, map_add, map_smul, smul_eq_mul]
      rw [div_eq_iff (hu i)]
      linarith
    let σ' : Fin n → Bool := fun i => decide (0 < ℓ i (z - q))
    have hσ' : ∀ i, 0 < (if σ' i then (1 : ℝ) else -1) * ℓ i (z - q) := by
      intro i
      by_cases hpos : 0 < ℓ i (z - q)
      · rw [if_pos (show decide (0 < ℓ i (z - q)) = true from decide_eq_true hpos)]
        linarith
      · have hneg : ℓ i (z - q) < 0 := lt_of_le_of_ne (not_lt.mp hpos) (hzne i)
        rw [if_neg (show ¬ (decide (0 < ℓ i (z - q)) = true) by
          rw [decide_eq_true_eq]; exact hpos)]
        linarith
    simp only [Set.mem_iUnion]
    refine ⟨σ', ⟨z - q, hdirK z hzK, hσ', ?_, by rwa [add_sub_cancel]⟩, hvV, fun i => ?_⟩
    · have := hzU.1
      rwa [mem_ball, dist_eq_norm] at this
    · by_cases hi : ℓ i v = 0
      · simp [hi]
      · have h1 : 0 < ℓ i (z - q) * ℓ i v := by
          have := hzU.2
          simp only [Set.mem_iInter, Set.mem_setOf_eq] at this
          exact this i hi
        have h2 := hσ' i
        nlinarith [mul_pos h2 h1, sq_nonneg (ℓ i (z - q))]
  · simp only [Set.mem_iUnion]
    rintro ⟨σ, ⟨w0, hw0V, hw0σ, hw0r, hw0K⟩, hvV, hvσ⟩
    refine ⟨r / (‖v‖ + 1), by positivity, fun t ht htε => ?_⟩
    have htv : t * ‖v‖ < r := by
      have : t * (‖v‖ + 1) < r := by
        calc t * (‖v‖ + 1) < r / (‖v‖ + 1) * (‖v‖ + 1) := by gcongr
          _ = r := div_mul_cancel₀ _ (ne_of_gt (by positivity))
      nlinarith
    obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = (r - t * ‖v‖) / (‖w0‖ + 1) := ⟨_, rfl⟩
    have hδ : 0 < δ := by rw [hδ_def]; exact div_pos (by linarith) (by positivity)
    have hev : ∀ s ∈ Ioo (0 : ℝ) δ, q + (t • v + s • w0) ∈ K := by
      rintro s ⟨hs0, hsδ⟩
      have hmem : t • v + s • w0 ∈ cellDirection K :=
        (cellDirection K).add_mem ((cellDirection K).smul_mem t hvV)
          ((cellDirection K).smul_mem s hw0V)
      have hσs : ∀ i, 0 < (if σ i then (1 : ℝ) else -1) * ℓ i (t • v + s • w0) := by
        intro i
        have hlin : (if σ i then (1 : ℝ) else -1) * ℓ i (t • v + s • w0) =
            t * ((if σ i then (1 : ℝ) else -1) * ℓ i v) +
              s * ((if σ i then (1 : ℝ) else -1) * ℓ i w0) := by
          rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          ring
        rw [hlin]
        exact add_pos_of_nonneg_of_pos (mul_nonneg ht.le (hvσ i)) (mul_pos hs0 (hw0σ i))
      have hnorm : ‖t • v + s • w0‖ < r := by
        have hs1 : s * (‖w0‖ + 1) < r - t * ‖v‖ := by
          calc s * (‖w0‖ + 1) < δ * (‖w0‖ + 1) := by gcongr
            _ = r - t * ‖v‖ := by rw [hδ_def]; exact div_mul_cancel₀ _ (ne_of_gt (by positivity))
        calc ‖t • v + s • w0‖ ≤ ‖t • v‖ + ‖s • w0‖ := norm_add_le _ _
          _ = t * ‖v‖ + s * ‖w0‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ht.le, Real.norm_of_nonneg hs0.le]
          _ < r := by nlinarith
      exact (hconst σ _ w0 hmem hw0V hσs hw0σ hnorm hw0r).mpr hw0K
    have hlim : Filter.Tendsto (fun s : ℝ => q + (t • v + s • w0))
        (nhdsWithin 0 (Ioi 0)) (nhds (q + t • v)) := by
      have hc : Continuous (fun s : ℝ => q + (t • v + s • w0)) := by fun_prop
      have := hc.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact hK.mem_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) hev)

/-- Step 4 of the V4 proof of `tangentCone_isHPiCone` (V4 1.16(b')): "each a finite
intersection of closed sides in `V` of these codimension-one subspaces, all in `HΠ` by
Lemma 1.10(b)": after the compatible frame, a finite union of closed chambers cut in a
prototype cell direction by prototype codimension-one cell directions is an `HΠ`-cone. -/
private theorem tangentCone_isHPiCone_step4_assemble (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) {V : Submodule ℝ (E d)}
    (hV : V ∈ S.cellDirections) {n : ℕ} (W : Fin n → Submodule ℝ (E d))
    (hW : ∀ i, W i ∈ S.cellDirections) (ℓ : Fin n → E d →ₗ[ℝ] ℝ)
    (hℓ : ∀ i, {x | x ∈ V ∧ ℓ i x = 0} = (W i : Set (E d)))
    (hdim : ∀ i, Module.finrank ℝ V = Module.finrank ℝ (W i) + 1)
    (P : (Fin n → Bool) → Prop) :
    HPiCone S.hPi (t.frame.toAffineEquiv.linear '' ⋃ (σ : Fin n → Bool) (_ : P σ),
      {v | v ∈ V ∧ ∀ i, 0 ≤ (if σ i then (1 : ℝ) else -1) * ℓ i v}) := by
  classical
  set L := t.frame.toAffineEquiv.linear
  have hmem : ∀ U : Submodule ℝ (E d), U ∈ S.cellDirections →
      U.map L.toLinearMap ∈ S.hPi := by
    intro U hU
    exact ⟨U, hU, t.frame.linearIsometryEquiv, ht, rfl⟩
  let fn : (Fin n → Bool) → Fin n → E d →ₗ[ℝ] ℝ := fun σ i =>
    ((if σ i then (1 : ℝ) else -1) • ℓ i).comp L.symm.toLinearMap
  have hfn : ∀ σ i v, fn σ i (L v) = (if σ i then (1 : ℝ) else -1) * ℓ i v := by
    intro σ i v
    simp only [fn, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hc : ∀ (σ : Fin n → Bool) i, (if σ i then (1 : ℝ) else -1) ≠ 0 := by
    intro σ i
    split_ifs <;> norm_num
  let side : (Fin n → Bool) → Fin n → Set (E d) := fun σ i =>
    {y | y ∈ V.map L.toLinearMap ∧ 0 ≤ fn σ i y}
  let piece : (Fin n → Bool) → Finset (Set (E d)) := fun σ =>
    insert ((V.map L.toLinearMap : Submodule ℝ (E d)) : Set (E d))
      (Finset.univ.image (side σ))
  refine ⟨(Finset.univ.filter P).image piece, ?_, ?_⟩
  · rw [Finset.set_biUnion_finset_image]
    ext y
    simp only [piece, Finset.set_biInter_insert, Finset.set_biInter_finset_image,
      Set.mem_image, Set.mem_iUnion, Set.mem_iInter, Finset.mem_filter, Finset.mem_univ,
      true_and, exists_prop, Set.mem_inter_iff, Set.mem_setOf_eq, side, SetLike.mem_coe,
      forall_const]
    constructor
    · rintro ⟨v, ⟨σ, hσ, hvV, hv⟩, rfl⟩
      refine ⟨σ, hσ, Submodule.mem_map_of_mem hvV, fun i => ?_⟩
      exact ⟨Submodule.mem_map_of_mem hvV, by rw [hfn]; exact hv i⟩
    · rintro ⟨σ, hσ, hyV, hy⟩
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hyV
      refine ⟨v, ⟨σ, hσ, hv, fun i => ?_⟩, rfl⟩
      have := (hy i).2
      simpa only [LinearEquiv.coe_coe, hfn] using this
  · intro pc hpc K hK
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hpc
    rcases Finset.mem_insert.mp hK with hK | hK
    · exact Or.inl ⟨V.map L.toLinearMap, Or.inl (hmem V hV), hK⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK
      have hWV : W i ≤ V := by
        intro x hx
        have : x ∈ {x | x ∈ V ∧ ℓ i x = 0} := by
          rw [hℓ i]
          exact hx
        exact this.1
      refine Or.inr ⟨V.map L.toLinearMap, (W i).map L.toLinearMap, Or.inl (hmem V hV),
        Or.inl (hmem (W i) (hW i)), Submodule.map_mono hWV, ?_, fn σ i, ?_, rfl⟩
      · rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq, hdim i]
      · ext y
        have h := Set.ext_iff.mp (hℓ i) (L.symm y)
        simp only [Set.mem_setOf_eq, SetLike.mem_coe] at h
        simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_map_equiv]
        rw [← h]
        simp only [fn, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul,
          LinearEquiv.coe_coe, mul_eq_zero, hc σ i, false_or]

/-- P11, V4 1.16(b'): tangent cones of listed cells of compatible ground tiles
at their listed vertices are `HΠ`-cones. This includes all lower dimensions. -/
theorem tangentCone_isHPiCone (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (C : CellName S t.ty)
    (p : E d) (hp : t.Lists 0 p) (hpC : p ∈ t.cell 0 C.val) :
    HPiCone S.hPi (tangentCone (t.cell 0 C.val) p) := by
  classical
  have hcell : t.cell 0 C.val = t.frame '' C.val.carrier := by
    ext x
    simp [FramedNode.cell, FramedNode.prototypeFrame]
  rw [hcell] at hpC ⊢
  obtain ⟨q, hq, rfl⟩ := hpC
  rw [tangentCone_isHPiCone_step0_transport]
  obtain ⟨n, f, ℓ, hf, r, hr, hwall⟩ :=
    tangentCone_isHPiCone_step1_walls t.ty C.val C.property q hq
  have hdimf : ∀ i, Module.finrank ℝ (cellDirection C.val.carrier) =
      Module.finrank ℝ (cellDirection (f i).carrier) + 1 := by
    intro i
    rw [C.val.flat.dimension, (f i).flat.dimension]
    exact ((hf i).2.2.2.1).symm
  have hnd : ∀ i, ∃ u ∈ cellDirection C.val.carrier, ℓ i u ≠ 0 := by
    intro i
    by_contra hcon
    push_neg at hcon
    have hsub : cellDirection C.val.carrier = cellDirection (f i).carrier := by
      apply SetLike.coe_injective
      rw [← (hf i).2.2.2.2]
      ext x
      simp only [SetLike.mem_coe, Set.mem_setOf_eq]
      exact ⟨fun hx => ⟨hx, hcon x hx⟩, fun hx => hx.1⟩
    have := hdimf i
    rw [hsub] at this
    omega
  rw [tangentCone_isHPiCone_step3_cone_eq C.val.flat.compact.isClosed
    C.val.flat.regularClosed hq ℓ hnd hr
    (fun σ v w hv hw hvσ hwσ hvr hwr => tangentCone_isHPiCone_step2_chamber_const
      C.val.flat.compact.isClosed hq ℓ hwall σ hv hw hvσ hwσ hvr hwr)]
  exact tangentCone_isHPiCone_step4_assemble t ht ⟨t.ty, C.val, C.property, rfl⟩
    (fun i => cellDirection (f i).carrier) (fun i => ⟨t.ty, f i, (hf i).1, rfl⟩) ℓ
    (fun i => (hf i).2.2.2.2) hdimf _

/-- Step 0 of the V4 proof of `tangentCone_tile_isHPiCone`
(V4 1.16(b')): the full tile is regular closed in ambient space. -/
private theorem tangentCone_tile_isHPiCone_step0_ambient (A : S.ι) :
    cellDirection (S.proto A).carrier = ⊤ ∧
    closure (relint (S.proto A).carrier) = (S.proto A).carrier ∧
    relfrontier (S.proto A).carrier = frontier (S.proto A).carrier := by
  let K : Set (E d) := (S.proto A).carrier
  have hspan : affineSpan ℝ K = ⊤ := by
    apply top_unique
    rw [← isOpen_interior.affineSpan_eq_top (S.proto A).interior_nonempty]
    exact affineSpan_mono ℝ interior_subset
  have hopen : IsOpen (affineSpan ℝ K : Set (E d)) := by
    simp [hspan]
  have hop : IsOpenMap ((↑) : affineSpan ℝ K → E d) :=
    hopen.isOpenMap_subtype_val
  have hI : relint K = interior K := by
    change intrinsicInterior ℝ K = interior K
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hop.interior_preimage_subset_preimage_interior hy
    · exact interior_subset_intrinsicInterior
  have hF : relfrontier K = frontier K := by
    calc
      relfrontier K = closure K \ relint K :=
        (closure_diff_intrinsicInterior (𝕜 := ℝ) K).symm
      _ = closure K \ interior K := by rw [hI]
      _ = frontier K := rfl
  change cellDirection K = ⊤ ∧
    closure (relint K) = K ∧ relfrontier K = frontier K
  refine ⟨?_, ?_, hF⟩
  · simp only [cellDirection, hspan, AffineSubspace.direction_top]
  · rw [hI]
    exact (S.proto A).regularClosed


/-- Step 1a of the V4 proof of `tangentCone_tile_isHPiCone_step1_walls` (V4 1.16(b')):
collect all facets containing `q`. -/
private lemma tangentCone_tile_isHPiCone_step1_walls_step1_facets
    (A : S.ι) (q : E d) :
    ∃ (n : ℕ) (f : Fin n → Cell d) (ℓ : Fin n → E d →ₗ[ℝ] ℝ),
      (∀ i, f i ∈ (S.cx A).cells ∧ q ∈ (f i).carrier ∧ (f i).dim + 1 = d ∧
        {x | ℓ i x = 0} = (cellDirection (f i).carrier : Set (E d))) ∧
      (∀ F ∈ (S.cx A).cells, q ∈ F.carrier → F.dim + 1 = d → ∃ i, f i = F) := by
  sorry

/-- Step 1b of the V4 proof of `tangentCone_tile_isHPiCone_step1_walls` (V4 1.16(b')):
find a neighborhood where no non-incident cell enters. -/
private lemma tangentCone_tile_isHPiCone_step1_walls_step2_radius
    (A : S.ι) (q : E d) :
    ∃ r : ℝ, 0 < r ∧
      ∀ e ∈ (S.cx A).cells, q ∉ e.carrier → ∀ x ∈ e.carrier, r ≤ dist x q := by
  sorry

/-- Step 1c of the V4 proof of `tangentCone_tile_isHPiCone_step1_walls` (V4 1.16(b')):
every cell is contained in a facet. -/
private lemma tangentCone_tile_isHPiCone_step1_walls_step3_cell_in_facet
    (A : S.ι) (e : Cell d) (he : e ∈ (S.cx A).cells) :
    ∃ F ∈ (S.cx A).cells, F.dim + 1 = d ∧ e.carrier ⊆ F.carrier := by
  sorry

/-- Step 1d of the V4 proof of `tangentCone_tile_isHPiCone_step1_walls` (V4 1.16(b')):
two points in a cell's carrier define a vector in its direction. -/
private lemma tangentCone_tile_isHPiCone_step1_walls_step4_direction
    (e : Cell d) {x q : E d} (hx : x ∈ e.carrier) (hq : q ∈ e.carrier) :
    x - q ∈ (cellDirection e.carrier : Set (E d)) := by
  have hx_span : x ∈ affineSpan ℝ e.carrier := subset_affineSpan _ _ hx
  have hq_span : q ∈ affineSpan ℝ e.carrier := subset_affineSpan _ _ hq
  exact AffineSubspace.vsub_mem_direction hx_span hq_span

/-- Step 1 of the V4 proof of `tangentCone_tile_isHPiCone`
(V4 1.16(b')): near the anchor, the boundary lies on the
hyperplanes of incident listed facets. -/
private theorem tangentCone_tile_isHPiCone_step1_walls
    (A : S.ι) (q : E d) :
    ∃ (n : ℕ) (f : Fin n → Cell d)
      (ℓ : Fin n → E d →ₗ[ℝ] ℝ),
      (∀ i, f i ∈ (S.cx A).cells ∧ q ∈ (f i).carrier ∧
        (f i).dim + 1 = d ∧
        {x | ℓ i x = 0} =
          (cellDirection (f i).carrier : Set (E d))) ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ frontier (S.proto A).carrier, dist x q < r →
          ∃ i, ℓ i (x - q) = 0 := by
  obtain ⟨n, f, ℓ, hf, hF⟩ := tangentCone_tile_isHPiCone_step1_walls_step1_facets A q
  obtain ⟨r, hr, hdist⟩ := tangentCone_tile_isHPiCone_step1_walls_step2_radius A q
  refine ⟨n, f, ℓ, hf, r, hr, ?_⟩
  intro x hx hxr
  have h_cov := CellComplex.carriers_cover (S.cx A)
  rw [← h_cov] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  rcases hx with ⟨e, he, hxe⟩
  have hqe : q ∈ e.carrier := by
    by_contra hqn
    have := hdist e he hqn x hxe
    linarith
  obtain ⟨F, hFc, hFdim, hsub⟩ := tangentCone_tile_isHPiCone_step1_walls_step3_cell_in_facet A e he
  have hqF : q ∈ F.carrier := hsub hqe
  have hxF : x ∈ F.carrier := hsub hxe
  obtain ⟨i, hi⟩ := hF F hFc hqF hFdim
  use i
  have hdir := tangentCone_tile_isHPiCone_step1_walls_step4_direction F hxF hqF
  have H := (hf i).2.2.2
  rw [hi] at H
  have h_eq : x - q ∈ {x | (ℓ i) x = 0} := by
    rw [H]
    exact hdir
  exact h_eq

/-- Step 2 of the V4 proof of `tangentCone_tile_isHPiCone`
(V4 1.16(b')): finite unions of ambient closed chambers
bounded by compatible facet directions are HΠ-cones. -/
private theorem tangentCone_tile_isHPiCone_step2_assemble
    (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup)
    {n : ℕ} (W : Fin n → Submodule ℝ (E d))
    (hW : ∀ i, W i ∈ S.cellDirections)
    (ℓ : Fin n → E d →ₗ[ℝ] ℝ)
    (hℓ : ∀ i, {x | ℓ i x = 0} = (W i : Set (E d)))
    (hdim : ∀ i, d = Module.finrank ℝ (W i) + 1)
    (P : (Fin n → Bool) → Prop) :
    HPiCone S.hPi (t.frame.toAffineEquiv.linear ''
      ⋃ (σ : Fin n → Bool) (_ : P σ),
        {v | ∀ i,
          0 ≤ (if σ i then (1 : ℝ) else -1) * ℓ i v}) := by
  classical
  set L := t.frame.toAffineEquiv.linear
  have hmem : ∀ U : Submodule ℝ (E d), U ∈ S.cellDirections →
      U.map L.toLinearMap ∈ S.hPi := by
    intro U hU
    exact ⟨U, hU, t.frame.linearIsometryEquiv, ht, rfl⟩
  let fn : (Fin n → Bool) → Fin n → E d →ₗ[ℝ] ℝ := fun σ i =>
    ((if σ i then (1 : ℝ) else -1) • ℓ i).comp L.symm.toLinearMap
  have hfn : ∀ σ i v, fn σ i (L v) = (if σ i then (1 : ℝ) else -1) * ℓ i v := by
    intro σ i v
    simp only [fn, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hc : ∀ (σ : Fin n → Bool) i, (if σ i then (1 : ℝ) else -1) ≠ (0 : ℝ) := by
    intro σ i
    split_ifs <;> norm_num
  let side : (Fin n → Bool) → Fin n → Set (E d) := fun σ i =>
    {y | 0 ≤ fn σ i y}
  let piece : (Fin n → Bool) → Finset (Set (E d)) := fun σ =>
    insert (⊤ : Set (E d)) (Finset.univ.image (side σ))
  refine ⟨(Finset.univ.filter P).image piece, ?_, ?_⟩
  · rw [Finset.set_biUnion_finset_image]
    ext y
    simp only [piece, Finset.set_biInter_insert, Finset.set_biInter_finset_image,
      Set.mem_image, Set.mem_iUnion, Set.mem_iInter, Finset.mem_filter, Finset.mem_univ,
      true_and, exists_prop, Set.mem_setOf_eq, side,
      forall_const, Set.top_eq_univ, Set.univ_inter]
    constructor
    · rintro ⟨v, ⟨σ, hσ, hv⟩, rfl⟩
      refine ⟨σ, hσ, fun i => ?_⟩
      exact by rw [hfn]; exact hv i
    · rintro ⟨σ, hσ, hy⟩
      obtain ⟨v, rfl⟩ := L.surjective y
      refine ⟨v, ⟨σ, hσ, fun i => ?_⟩, rfl⟩
      have := hy i
      simpa only [LinearEquiv.coe_coe, hfn] using this
  · intro pc hpc K hK
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hpc
    rcases Finset.mem_insert.mp hK with hK | hK
    · exact Or.inl ⟨⊤, Or.inr rfl, hK⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK
      have H : side σ i = {x | x ∈ (⊤ : Submodule ℝ (E d)) ∧ 0 ≤ fn σ i x} := by
        ext x
        simp only [side, Set.mem_setOf_eq, Submodule.mem_top, true_and]
      refine Or.inr ⟨⊤, (W i).map L.toLinearMap, Or.inr rfl,
        Or.inl (hmem (W i) (hW i)), le_top, ?_, fn σ i, ?_, H⟩
      · rw [LinearEquiv.finrank_map_eq, finrank_top ℝ (E d), finrank_euclideanSpace_fin, ← hdim i]
      · ext y
        have h := Set.ext_iff.mp (hℓ i) (L.symm y)
        simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_map_equiv]
        simp only [fn, LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul,
          LinearEquiv.coe_coe, mul_eq_zero, hc σ i, false_or, Submodule.mem_top, true_and]
        exact h

/-- P11, V4 1.16(b'): cones of finite unions of compatible cells at a listed
anchor are `HΠ`-cones, as are full tile cones at listed vertices. -/
theorem tangentCone_tile_isHPiCone (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (p : E d) (hp : t.Lists 0 p) :
    HPiCone S.hPi (tangentCone (t.carrier 0) p) := by
  classical
  obtain ⟨e, he, hp_in_e⟩ := hp
  have h_carrier : t.carrier 0 = t.frame '' (S.proto t.ty).carrier := by
    dsimp [FramedNode.carrier, placedSet, SubstSystem.supertile]
    ext x
    simp only [Set.mem_image, _root_.pow_zero]
    constructor
    · rintro ⟨y, ⟨z, hz, h1⟩, rfl⟩
      have : z = y := by 
        change (S.σ ^ 0).toAffineEquiv z = y at h1
        exact h1
      rw [← this]
      exact ⟨z, hz, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, ⟨y, hy, rfl⟩, rfl⟩
  rw [h_carrier]
  have hp_in : p ∈ t.frame '' (S.proto t.ty).carrier := by
    dsimp [FramedNode.cell] at hp_in_e
    rcases hp_in_e with ⟨x, hx, rfl⟩
    have hsub : e.carrier ⊆ frontier (S.proto t.ty).carrier := by
      have hc := (S.cx t.ty).carriers_cover
      intro y hy
      rw [← hc]
      simp only [Set.mem_iUnion, exists_prop]
      have he_cells : e ∈ (S.cx t.ty).cells := by
        have := Finset.mem_filter.mp he
        exact this.1
      exact ⟨e, he_cells, hy⟩
    have hsub2 : frontier (S.proto t.ty).carrier ⊆ (S.proto t.ty).carrier := by
      exact (S.proto t.ty).compact.isClosed.frontier_subset
    exact ⟨x, hsub2 (hsub hx), rfl⟩
  obtain ⟨q, hq, rfl⟩ := hp_in
  rw [tangentCone_isHPiCone_step0_transport]
  obtain ⟨n, f, ℓ, hf, r, hr, hwall⟩ :=
    tangentCone_tile_isHPiCone_step1_walls t.ty q
  have h0 := tangentCone_tile_isHPiCone_step0_ambient t.ty
  have hnd : ∀ i, ∃ u ∈ cellDirection (S.proto t.ty).carrier, ℓ i u ≠ 0 := by
    intro i
    rcases hf i with ⟨hmem, hinc, hcodim, hker⟩
    rw [h0.1]
    by_contra hcon
    push_neg at hcon
    have htop : cellDirection (f i).carrier = ⊤ := by
      apply SetLike.coe_injective
      rw [← hker]
      ext x
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_top, iff_true]
      exact hcon x (Submodule.mem_top)
    have hdim : (f i).dim = d := by
      calc
        (f i).dim = Module.finrank ℝ (cellDirection (f i).carrier) := (f i).flat.dimension.symm
        _ = d := by
          rw [htop, finrank_top]
          exact finrank_euclideanSpace_fin
    omega
  have hwall' : ∀ x ∈ relfrontier (S.proto t.ty).carrier, dist x q < r → ∃ i, ℓ i (x - q) = 0 := by
    intro x hx hdist
    rw [h0.2.2] at hx
    exact hwall x hx hdist
  rw [tangentCone_isHPiCone_step3_cone_eq (S.proto t.ty).compact.isClosed h0.2.1 hq ℓ hnd hr]
  · have h_assemble := tangentCone_tile_isHPiCone_step2_assemble t ht (fun i => cellDirection (f i).carrier) 
      (fun i => ⟨t.ty, f i, (hf i).1, rfl⟩) ℓ (fun i => (hf i).2.2.2) (fun i => by
        have hd1 := (hf i).2.2.1
        have hd2 : Module.finrank ℝ (cellDirection (f i).carrier) = (f i).dim := (f i).flat.dimension
        rw [hd2]
        exact hd1.symm) (fun σ => ∃ v ∈ cellDirection (S.proto t.ty).carrier, (∀ i, 0 < (if σ i then (1 : ℝ) else -1) * ℓ i v) ∧ ‖v‖ < r ∧ q + v ∈ (S.proto t.ty).carrier)
    have heq_ambient : (cellDirection (S.proto t.ty).carrier : Set (E d)) = (⊤ : Set (E d)) := by
      rw [h0.1]
      rfl
    have h_convert : (⋃ (σ : Fin n → Bool) (H : ∃ v ∈ cellDirection (S.proto t.ty).carrier, (∀ (i : Fin n), 0 < (if σ i = true then 1 else -1) * (ℓ i) v) ∧ ‖v‖ < r ∧ q + v ∈ (S.proto t.ty).carrier), {v | v ∈ cellDirection (S.proto t.ty).carrier ∧ ∀ (i : Fin n), 0 ≤ (if σ i = true then 1 else -1) * (ℓ i) v}) = ⋃ (σ : Fin n → Bool) (x : ∃ v ∈ cellDirection (S.proto t.ty).carrier, (∀ (i : Fin n), 0 < (if σ i = true then 1 else -1) * (ℓ i) v) ∧ ‖v‖ < r ∧ q + v ∈ (S.proto t.ty).carrier), {v | ∀ (i : Fin n), 0 ≤ (if σ i = true then 1 else -1) * (ℓ i) v} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      apply exists_congr
      intro σ
      apply exists_congr
      intro H
      have hx_top : x ∈ (⊤ : Set (E d)) := Set.mem_univ x
      rw [← heq_ambient] at hx_top
      exact ⟨fun h => h.2, fun h => ⟨hx_top, h⟩⟩
    rw [h_convert]
    exact h_assemble
  · intro σ v w hv hw hvσ hwσ hvr hwr
    exact tangentCone_isHPiCone_step2_chamber_const (S.proto t.ty).compact.isClosed hq ℓ hwall' σ hv hw hvσ hwσ hvr hwr

/-- P11, V4 1.16(c): the factors commute. -/
theorem RL_commute (F : PowerFactorisation S) :
    F.R.toLinearEquiv * F.L = F.L * F.R.toLinearEquiv := by
  exact (L_commutes F F.R F.R_mem).symm

/-- Step 1 of the V4 proof of `power_cone_formula` (V4 1.16(c)): "$\sigma^{ap_0}=R^aL^a$ and $\sigma^n=\sigma^rR^aL^a$". -/
private theorem power_cone_formula_step1_expansion (F : PowerFactorisation S) (a r : ℕ) :
    S.σ ^ (a * F.power + r) = S.σ ^ r * F.R.toLinearEquiv ^ a * F.L ^ a := by
  have h1 : a * F.power + r = r + F.power * a := by
    rw [Nat.mul_comm, Nat.add_comm]
  rw [h1, pow_add, pow_mul, F.factor]
  have hcomm : Commute F.R.toLinearEquiv F.L := RL_commute F
  rw [Commute.mul_pow hcomm a]
  rw [mul_assoc]

/-- Step 2 of the V4 proof of `power_cone_formula` (V4 1.16(c)): "$\sigma^rR^a\sigma^{-r}\in\mathsf H$, so that $\sigma^nG=R_n\sigma^rG$". -/
private theorem power_cone_formula_step2_rotation (F : PowerFactorisation S) (a r : ℕ) :
    ∃ Q ∈ S.rotGroup, Q.toLinearEquiv = linearConj S.σ (r : ℤ) (F.R.toLinearEquiv ^ a) := by
  obtain ⟨Q, hQ, hQeq⟩ := S.rotGroup_conj_zpow (r : ℤ) (F.R ^ a) (Subgroup.pow_mem S.rotGroup F.R_mem a)
  use Q, hQ
  rw [hQeq]
  congr 1
  clear hQeq hQ Q r
  induction a with
  | zero =>
    ext x
    rfl
  | succ a ih =>
    ext x
    have h : (F.R ^ (a + 1)).toLinearEquiv x = (F.R ^ a).toLinearEquiv (F.R.toLinearEquiv x) := by rfl
    rw [h]
    have ih_eq : ∀ y, (F.R ^ a).toLinearEquiv y = (F.R.toLinearEquiv ^ a) y := by
      intro y
      exact LinearEquiv.congr_fun ih y
    rw [ih_eq]
    rfl

/-- Step 3 of the V4 proof of `power_cone_formula` (V4 1.16(c)): "$\sigma^nG=\sigma^rR^aG=(\sigma^rR^a\sigma^{-r})\sigma^rG$". -/
private theorem power_cone_formula_step3_image (F : PowerFactorisation S) (a r : ℕ)
    (Q : Ortho d) (hQ_eq : Q.toLinearEquiv = linearConj S.σ (r : ℤ) (F.R.toLinearEquiv ^ a))
    (K : Set (E d)) (hK : HPiCone S.hPi K) :
    (S.σ ^ (a * F.power + r)) '' K = Q '' ((S.σ ^ r) '' K) := by
  have L_fixes : ⇑(F.L ^ a) '' K = K := by
    clear hQ_eq Q
    induction' a with n ih
    · simp
    · change ⇑(F.L ^ n * F.L) '' K = K
      have heq : ⇑(F.L ^ n * F.L) = ⇑(F.L ^ n) ∘ ⇑(F.L) := rfl
      rw [heq, Set.image_comp]
      rw [L_fixes_HPiCones F K hK]
      exact ih
  rw [power_cone_formula_step1_expansion F a r]
  have hcomp2 : ⇑(S.σ ^ r * F.R.toLinearEquiv ^ a * F.L ^ a) = ⇑(S.σ ^ r * F.R.toLinearEquiv ^ a) ∘ ⇑(F.L ^ a) := rfl
  rw [hcomp2, Set.image_comp, L_fixes]
  have hQ : Q.toLinearEquiv * (S.σ ^ r) = S.σ ^ r * F.R.toLinearEquiv ^ a := by
    have eq1 : Q.toLinearEquiv * (S.σ ^ r) = linearConj S.σ (r : ℤ) (F.R.toLinearEquiv ^ a) * (S.σ ^ r) := by rw [hQ_eq]
    rw [eq1]
    change S.σ ^ (r : ℤ) * F.R.toLinearEquiv ^ a * S.σ ^ (-(r : ℤ)) * S.σ ^ r = _
    have eq2 : S.σ ^ (-(r : ℤ)) * S.σ ^ r = 1 := by
      rw [← zpow_natCast]
      rw [← zpow_add]
      have : -(r : ℤ) + (r : ℤ) = 0 := by omega
      rw [this, zpow_zero]
    rw [mul_assoc (S.σ ^ (r : ℤ) * _), eq2, mul_one, zpow_natCast]
  have hcomp3 : ⇑(Q.toLinearEquiv * (S.σ ^ r)) = ⇑(S.σ ^ r * F.R.toLinearEquiv ^ a) := by rw [hQ]
  have hcomp4 : ⇑(Q.toLinearEquiv * (S.σ ^ r)) = ⇑Q ∘ ⇑(S.σ ^ r) := rfl
  rw [← hcomp3, hcomp4, Set.image_comp]

/-- P11, V4 1.16(c): power decomposition and compatible residual rotations. -/
theorem power_cone_formula (F : PowerFactorisation S) (a r : ℕ) (hr : r < F.power) :
    S.σ ^ (a * F.power + r) = S.σ ^ r * F.R.toLinearEquiv ^ a * F.L ^ a ∧
      ∃ Q ∈ S.rotGroup, Q.toLinearEquiv =
        linearConj S.σ (r : ℤ) (F.R.toLinearEquiv ^ a) ∧
        ∀ K : Set (E d), HPiCone S.hPi K →
          (S.σ ^ (a * F.power + r)) '' K = Q '' ((S.σ ^ r) '' K) := by
  have h1 := power_cone_formula_step1_expansion F a r
  refine ⟨h1, ?_⟩
  have ⟨Q, hQ, hQ_eq⟩ := power_cone_formula_step2_rotation F a r
  refine ⟨Q, hQ, hQ_eq, ?_⟩
  intro K hK
  exact power_cone_formula_step3_image F a r Q hQ_eq K hK

/-- P12, V4 1.17: a header is a literal tuple of cones, a type, and a vertex name. -/
structure Header (S : SubstSystem d) (s : ℕ) where
  /-- P12, V4 1.17: type of the listing native tile. -/
  ty : S.ι
  /-- P12, V4 1.17: vertex in that type's boundary complex. -/
  vertex : {e // e ∈ (S.cx ty).vertices}
  /-- P12, V4 1.17: direction cones in the tile's isometric prototype frame. -/
  cones : Fin s → Set (E d)

namespace CompatiblePatch

variable (P : CompatiblePatch S)

/-- P12, V4 1.17: all headers at one anchor, over all depths and listing tiles.
The supplied cones have already been translated from the apex to the origin. -/
def headers (p : E d) {s : ℕ} (G : Fin s → Set (E d)) : Set (Header S s) :=
  {h | ∃ (n : ℕ) (a : P.Incident p n),
    (S.σ ^ n) p ∈ (P.native n a.val).cell 0 h.vertex.val ∧
    h.ty = (P.native n a.val).ty ∧
      ∀ j, h.cones j = (P.native n a.val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ n) '' G j)}

/-- Step 1 of the V4 proof of `header_finiteness` (V4 1.17):
"acting by ±1 on each". On a real
line, fixing the norm of a vector leaves at most the two sign choices. -/
private theorem header_finiteness_step1_line (V : Submodule ℝ (E d))
    (hV : Module.finrank ℝ V = 1) (z : E d) (hz : z ∈ V) :
    {x : E d | x ∈ V ∧ ‖x‖ = ‖z‖}.Finite := by
  apply (Set.toFinite ({z, -z} : Set (E d))).subset
  rintro x ⟨hx, hn⟩
  by_cases hzero : z = 0
  · have hxzero : x = 0 := norm_eq_zero.mp (by simpa [hzero] using hn)
    simp [hzero, hxzero]
  have hz' : (⟨z, hz⟩ : V) ≠ 0 := by simpa using hzero
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨z, hz⟩ : V) hz').mp hV ⟨x, hx⟩
  have heq : c • z = x := congrArg Subtype.val hc
  have hcabs : |c| = 1 := by
    have hnorm : |c| * ‖z‖ = 1 * ‖z‖ := by
      simpa [← heq, norm_smul, Real.norm_eq_abs] using hn
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hzero) hnorm
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hcabs with hc | hc
  · simp [← heq, hc]
  · simp [← heq, hc]

/-- Step 2 of the V4 proof of `header_finiteness` (V4 1.17):
"acting by ±1 on each". An
orthogonal stabilizer of a complete flag has finite orbits on vectors. -/
private theorem header_finiteness_step2_flag_orbit
    (V : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    ∀ k ≤ d, ∀ x ∈ V k,
      {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = V i}.image
        (fun R => R x) |>.Finite := by
  intro k
  induction k with
  | zero =>
      intro hk x hx
      have hV : V 0 = ⊥ := Submodule.finrank_eq_zero.mp (hdim 0 (by omega))
      have hxzero : x = 0 := by simpa [hV] using hx
      subst x
      exact (Set.finite_singleton (0 : E d)).subset
        (by rintro _ ⟨R, hR, rfl⟩; simp)
  | succ k ih =>
      intro hk x hx
      obtain ⟨y, hy, z, hz, hsum⟩ := (V k).exists_add_mem_mem_orthogonal x
      have hle : V k ≤ V (k + 1) := hmono k (by omega)
      have hzV : z ∈ V (k + 1) := by
        have heq : z = x - y := by rw [hsum]; abel
        rw [heq]
        exact (V (k + 1)).sub_mem hx (hle hy)
      have hline : Module.finrank ℝ ((V k)ᗮ ⊓ V (k + 1) : Submodule ℝ (E d)) = 1 := by
        have hh := Submodule.finrank_add_inf_finrank_orthogonal hle
        rw [hdim k (by omega), hdim (k + 1) hk] at hh
        omega
      have hyfinite := ih (by omega) y hy
      have hzfinite := header_finiteness_step1_line ((V k)ᗮ ⊓ V (k + 1)) hline z ⟨hz, hzV⟩
      apply ((hyfinite.prod hzfinite).image (fun yz : E d × E d => yz.1 + yz.2)).subset
      rintro _ ⟨R, hR, rfl⟩
      refine ⟨(R y, R z), ⟨⟨R, hR, rfl⟩, ?_⟩, ?_⟩
      · refine ⟨⟨?_, ?_⟩, R.norm_map z⟩
        · have horth : ((V k)ᗮ).map R.toLinearEquiv.toLinearMap = (V k)ᗮ := by
            rw [Submodule.map_orthogonal_equiv, hR k (by omega)]
          rw [← horth]
          exact Submodule.mem_map_of_mem hz
        · rw [← hR (k + 1) hk]
          exact Submodule.mem_map_of_mem hzV
      · simpa [map_add] using (congrArg R hsum).symm

/-- Step 3 of the V4 proof of `header_finiteness` (V4 1.17):
"acting by ±1 on each". Values on
one basis turn the finite vector orbits into a finite orthogonal stabilizer. -/
private theorem header_finiteness_step3_flag_stabilizer
    (V : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = V i}.Finite := by
  let H := {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = V i}
  let b := stdOrthonormalBasis ℝ (E d)
  have htop : V d = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using hdim d le_rfl)
  have hpoint : ∀ i, (H.image (fun R => R (b i))).Finite := by
    intro i
    exact header_finiteness_step2_flag_orbit V hdim hmono d le_rfl (b i) (by simp [htop])
  have heval : ((fun R : Ortho d => fun i => R (b i)) '' H).Finite :=
    (Set.Finite.pi' hpoint).subset (by rintro _ ⟨R, hR, rfl⟩ i; exact ⟨R, hR, rfl⟩)
  apply Set.Finite.of_finite_image heval
  intro R hR T hT heq
  exact b.toBasis.ext_linearIsometryEquiv (fun i => congrFun heq i)

/-- Step 4 of the V4 proof of `header_finiteness` (V4 1.17):
"the orthogonal maps carrying the complete flag ... to the target form a
coset of the stabiliser". The transporter is a translate of the finite flag stabilizer. -/
private theorem header_finiteness_step4_flag_transporters
    (V W : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = W i}.Finite := by
  classical
  let T := {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = W i}
  by_cases hT : T.Nonempty
  · obtain ⟨R₀, hR₀⟩ := hT
    apply ((header_finiteness_step3_flag_stabilizer V hdim hmono).image
      (fun R => R.trans R₀)).subset
    intro R hR
    refine ⟨R.trans R₀.symm, ?_, ?_⟩
    · intro i hi
      change (V i).map (R₀.symm.toLinearEquiv.toLinearMap.comp
        R.toLinearEquiv.toLinearMap) = V i
      rw [Submodule.map_comp, hR i hi, ← hR₀ i hi, ← Submodule.map_comp]
      simp
    · apply LinearIsometryEquiv.ext
      intro x
      exact R₀.apply_symm_apply (R x)
  · exact Set.finite_empty.subset (by intro R hR; exact (hT ⟨R, hR⟩).elim)

/-- Step 5 of the V4 proof of `header_finiteness` (V4 1.17):
"for fixed r ... and fixed target flag". A finite catalogue for each
component gives only finitely many orthogonal transporters of a complete flag. -/
private theorem header_finiteness_step5_catalogue_transporters
    (C : Set (Submodule ℝ (E d))) (hC : C.Finite)
    (V : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap ∈ C}.Finite := by
  classical
  letI : Finite C := hC
  let W (f : Fin (d + 1) → C) (i : ℕ) : Submodule ℝ (E d) :=
    if hi : i ≤ d then (f ⟨i, by omega⟩).val else ⊤
  have hf := Set.finite_iUnion fun f : Fin (d + 1) → C =>
    header_finiteness_step4_flag_transporters V (W f) hdim hmono
  apply hf.subset
  intro R hR
  let f : Fin (d + 1) → C := fun i =>
    ⟨(V i.val).map R.toLinearEquiv.toLinearMap, hR i.val (by omega)⟩
  apply Set.mem_iUnion.mpr
  refine ⟨f, ?_⟩
  intro i hi
  simp [W, hi, f]

/-- Step 6 of the V4 proof of `header_finiteness` (V4 1.17):
"the finite set of native flags". All their component directions come
from the finite prototype cell catalogue, with the ambient space adjoined. -/
private theorem header_finiteness_step6_directions :
    (S.cellDirections ∪ {⊤}).Finite := by
  have hf : (⋃ A : S.ι, (fun e : Cell d => cellDirection e.carrier) ''
      ((S.cx A).cells : Set (Cell d))).Finite :=
    Set.finite_iUnion fun A : S.ι =>
      (S.cx A).cells.finite_toSet.image (fun e : Cell d => cellDirection e.carrier)
  apply (hf.union (Set.finite_singleton ⊤)).subset
  rintro V (⟨A, e, he, rfl⟩ | hV)
  · exact Or.inl (Set.mem_iUnion.mpr ⟨A, ⟨e, he, rfl⟩⟩)
  · exact Or.inr hV

/-- Step 7 of the V4 proof of `header_finiteness` (V4 1.17):
"by 1.16(c)" applies to flag components as well as cones. A single
allowed subspace is an `HΠ`-cone, including the full ambient space. -/
private theorem header_finiteness_step7_subspace_cone
    (V : Submodule ℝ (E d)) (hV : V ∈ S.hPi ∨ V = ⊤) :
    HPiCone S.hPi (V : Set (E d)) := by
  classical
  refine ⟨{{(V : Set (E d))}}, by simp, ?_⟩
  intro p hp C hC
  simp only [Finset.mem_singleton] at hp
  subst p
  simp only [Finset.mem_singleton] at hC
  subst C
  exact Or.inl ⟨V, hV, rfl⟩

/-- Step 8 of the V4 proof of `header_finiteness` (V4 1.17):
"direction spaces ... in HΠ". The permutation of direction orbits in
1.10(c) also gives invariance under inverse powers of the expansion. -/
private theorem header_finiteness_step8_inverse_directions
    (n : ℕ) (V : Submodule ℝ (E d)) (hV : V ∈ S.hPi) :
    V.map ((S.σ ^ n)⁻¹).toLinearMap ∈ S.hPi := by
  have hone (V : Submodule ℝ (E d)) (hV : V ∈ S.hPi) :
      V.map S.σ.symm.toLinearMap ∈ S.hPi := by
    obtain ⟨_, _, p, hp⟩ := S.orbits_finite
    obtain ⟨U, hU, hVU⟩ := hV
    let O : S.directionOrbits := ⟨S.directionOrbit U, U, hU, rfl⟩
    have hm : V ∈ (p (p.symm O)).val := by simpa using hVU
    rw [hp] at hm
    obtain ⟨W, hW, rfl⟩ := hm
    have hW' : W ∈ S.hPi := by
      obtain ⟨U', hU', hO⟩ := (p.symm O).property
      exact ⟨U', hU', hO ▸ hW⟩
    simpa [← Submodule.map_comp] using hW'
  induction n with
  | zero => simpa using hV
  | succ n ih =>
    have hh := hone _ ih
    simpa only [pow_succ, mul_inv_rev, LinearEquiv.coe_toLinearMap_mul,
      Module.End.mul_eq_comp, Submodule.map_comp] using hh

/-- Step 9 of the V4 proof of `header_finiteness` (V4 1.17):
"Put D_m := B_t⁻¹ R_m ... D_m takes finitely many values". The same
residual rotation acts on the complete flag and every cone in the tuple. -/
private theorem header_finiteness_step9_residual_rotations
    (F : PowerFactorisation S) (N : ℕ) (B : ℕ → Ortho d)
    (V : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1))
    (hV : ∀ i ≤ d, V i ∈ S.hPi ∨ V i = ⊤)
    (hframe : ∀ m i, i ≤ d →
      ((V i).map (S.σ ^ (N + m)).toLinearMap).map
        (B m).symm.toLinearEquiv.toLinearMap ∈ S.cellDirections ∪ {⊤})
    {s : ℕ} (G : Fin s → Set (E d)) (hG : ∀ j, HPiCone S.hPi (G j)) :
    (Set.range (fun m => fun j => (B m).symm '' ((S.σ ^ (N + m)) '' G j))).Finite := by
  classical
  let C := S.cellDirections ∪ {⊤}
  let T (r : Fin F.power) : Set (Ortho d) :=
    {R | ∀ i ≤ d, ((V i).map (S.σ ^ r.val).toLinearMap).map
      R.toLinearEquiv.toLinearMap ∈ C}
  have hT (r : Fin F.power) : (T r).Finite := by
    apply header_finiteness_step5_catalogue_transporters C
      header_finiteness_step6_directions
      (fun i => (V i).map (S.σ ^ r.val).toLinearMap)
    · intro i hi
      rw [LinearEquiv.finrank_map_eq]
      exact hdim i hi
    · intro i hi
      exact Submodule.map_mono (hmono i hi)
  have hf : (⋃ r : Fin F.power,
      (T r).image (fun R : Ortho d => fun j : Fin s => R '' ((S.σ ^ r.val) '' G j))).Finite :=
    Set.finite_iUnion fun r : Fin F.power =>
      (hT r).image (fun R : Ortho d => fun j : Fin s => R '' ((S.σ ^ r.val) '' G j))
  apply hf.subset
  rintro _ ⟨m, rfl⟩
  let r : Fin F.power := ⟨(N + m) % F.power, Nat.mod_lt _ (by have := F.power_pos; omega)⟩
  let a := (N + m) / F.power
  have hn : a * F.power + r.val = N + m := by
    simpa [a, r, Nat.mul_comm] using Nat.div_add_mod (N + m) F.power
  obtain ⟨Q, hQ, _, hformula⟩ := (power_cone_formula F a r.val r.isLt).2
  rw [hn] at hformula
  let D := Q.trans (B m).symm
  refine Set.mem_iUnion.mpr ⟨r, ?_⟩
  refine ⟨D, ?_, ?_⟩
  · intro i hi
    have hm : (V i).map (S.σ ^ (N + m)).toLinearMap =
        ((V i).map (S.σ ^ r.val).toLinearMap).map Q.toLinearEquiv.toLinearMap := by
      apply SetLike.coe_injective
      exact hformula (V i) (header_finiteness_step7_subspace_cone (V i) (hV i hi))
    change (((V i).map (S.σ ^ r.val).toLinearMap).map
      ((B m).symm.toLinearEquiv.toLinearMap.comp Q.toLinearEquiv.toLinearMap)) ∈ C
    rw [Submodule.map_comp, ← hm]
    exact hframe m i hi
  · funext j
    change D '' ((S.σ ^ r.val) '' G j) =
      (B m).symm '' ((S.σ ^ (N + m)) '' G j)
    rw [hformula (G j) (hG j)]
    simp only [Set.image_image]
    rfl

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". Finitely many proper affine
subspaces have dense complement. -/
private theorem header_finiteness_step10_dense_avoid
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : Type*} [Finite ι] (L : ι → AffineSubspace ℝ V) (hL : ∀ i, L i ≠ ⊤) :
    Dense (⋂ i, ((L i : Set V)ᶜ)) := by
  apply dense_iInter_of_isOpen (fun i => (L i).closed_of_finiteDimensional.isOpen_compl)
  intro i
  rw [← interior_eq_empty_iff_dense_compl]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have ht := isOpen_interior.affineSpan_eq_top (⟨x, hx⟩ : (interior (L i : Set V)).Nonempty)
  have hle : affineSpan ℝ (interior (L i : Set V)) ≤ L i :=
    affineSpan_le.mpr interior_subset
  rw [ht] at hle
  exact hL i (top_unique hle)

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". A segment from a point
outside an affine subspace avoids that subspace if its other endpoint
avoids the affine span of the subspace and the first point. -/
private theorem header_finiteness_step10_segment_avoid
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : AffineSubspace ℝ V) (x z : V) (hx : x ∉ L)
    (hz : z ∉ affineSpan ℝ (insert x (L : Set V))) :
    Disjoint (segment ℝ x z) (L : Set V) := by
  apply Set.disjoint_left.mpr
  intro w hw hwL
  have hwline : w ∈ line[ℝ, x, z] :=
    (line[ℝ, x, z]).convex.segment_subset (left_mem_affineSpan_pair ℝ x z)
      (right_mem_affineSpan_pair ℝ x z) hw
  have hwx : w ≠ x := by rintro rfl; exact hx hwL
  have hline := affineSpan_pair_eq_of_right_mem_of_ne hwline hwx
  have hle : line[ℝ, x, w] ≤ affineSpan ℝ (insert x (L : Set V)) :=
    affineSpan_pair_le_of_mem_of_mem (mem_affineSpan ℝ (Set.mem_insert _ _))
      (mem_affineSpan ℝ (Set.mem_insert_of_mem _ hwL))
  rw [hline] at hle
  exact hz (hle (right_mem_affineSpan_pair ℝ x z))

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". Removing finitely many
affine subspaces of codimension at least two does not disconnect an
open convex set: two segments through a generic intermediate point suffice. -/
private theorem header_finiteness_step10_avoid_connected
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : Type*} [Finite ι] (L : ι → AffineSubspace ℝ V)
    (hL : ∀ i, Module.finrank ℝ (L i).direction + 1 < Module.finrank ℝ V)
    (U : Set V) (hU : IsOpen U) (hc : Convex ℝ U) :
    IsPreconnected (U ∩ ⋂ i, (L i : Set V)ᶜ) := by
  apply isPreconnected_of_forall_pair
  rintro x ⟨hxU, hx⟩ y ⟨hyU, hy⟩
  let M : Bool × ι → AffineSubspace ℝ V := fun b =>
    affineSpan ℝ (insert (if b.1 then x else y) (L b.2 : Set V))
  have hM (b : Bool × ι) : M b ≠ ⊤ := by
    intro heq
    have hle := finrank_vectorSpan_insert_le (L b.2) (if b.1 then x else y)
    rw [← direction_affineSpan] at hle
    change Module.finrank ℝ (M b).direction ≤ Module.finrank ℝ (L b.2).direction + 1 at hle
    rw [heq, AffineSubspace.direction_top, finrank_top] at hle
    exact (hL b.2).not_ge hle
  obtain ⟨z, hz, hzU⟩ := (header_finiteness_step10_dense_avoid M hM).exists_mem_open hU ⟨x, hxU⟩
  have hsx : segment ℝ x z ⊆ U ∩ ⋂ i, (L i : Set V)ᶜ := by
    intro w hw
    refine ⟨hc.segment_subset hxU hzU hw, Set.mem_iInter.mpr fun i => ?_⟩
    exact Set.disjoint_left.mp (header_finiteness_step10_segment_avoid (L i) x z
      (Set.mem_iInter.mp hx i) (by simpa [M] using Set.mem_iInter.mp hz (true, i))) hw
  have hsy : segment ℝ y z ⊆ U ∩ ⋂ i, (L i : Set V)ᶜ := by
    intro w hw
    refine ⟨hc.segment_subset hyU hzU hw, Set.mem_iInter.mpr fun i => ?_⟩
    exact Set.disjoint_left.mp (header_finiteness_step10_segment_avoid (L i) y z
      (Set.mem_iInter.mp hy i) (by simpa [M] using Set.mem_iInter.mp hz (false, i))) hw
  refine ⟨segment ℝ x z ∪ segment ℝ y z, Set.union_subset hsx hsy,
    Or.inl (left_mem_segment ℝ x z), Or.inr (left_mem_segment ℝ y z), ?_⟩
  exact (convex_segment (𝕜 := ℝ) x z).isPreconnected.union z
    (right_mem_segment ℝ x z) (right_mem_segment ℝ y z)
    (convex_segment (𝕜 := ℝ) y z).isPreconnected


/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". A boundary of a regular
closed set cannot locally lie in finitely many affine subspaces of
codimension at least two: the complement connects the inside to the outside. -/
private theorem header_finiteness_step10_boundary_not_thin
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : Set V) (hK : IsClosed K) (hreg : closure (interior K) = K)
    (p : V) (hp : p ∈ frontier K)
    {ι : Type*} [Finite ι] (L : ι → AffineSubspace ℝ V)
    (hL : ∀ i, Module.finrank ℝ (L i).direction + 1 < Module.finrank ℝ V)
    (r : ℝ) (hr : 0 < r) :
    ¬ frontier K ∩ ball p r ⊆ ⋃ i, (L i : Set V) := by
  intro hcover
  have hproper (i : ι) : L i ≠ ⊤ := by
    intro heq
    have h := hL i
    rw [heq, AffineSubspace.direction_top, finrank_top] at h
    omega
  have hdense := header_finiteness_step10_dense_avoid L hproper
  have hxcl : p ∈ closure (interior K) := by
    rw [hreg]
    exact hK.frontier_subset hp
  have hycl : p ∈ closure Kᶜ := by
    rw [frontier_eq_closure_inter_closure] at hp
    exact hp.2
  obtain ⟨x, hx, hxU, hxK⟩ := hdense.exists_mem_open (isOpen_ball.inter isOpen_interior)
    (mem_closure_iff.mp hxcl (ball p r) isOpen_ball (mem_ball_self hr))
  obtain ⟨y, hy, hyU, hyK⟩ := hdense.exists_mem_open (isOpen_ball.inter hK.isOpen_compl)
    (mem_closure_iff.mp hycl (ball p r) isOpen_ball (mem_ball_self hr))
  have hsides : ball p r ∩ ⋂ i, (L i : Set V)ᶜ ⊆ interior K ∪ Kᶜ := by
    rintro z ⟨hzU, hz⟩
    by_cases hzK : z ∈ K
    · left
      by_contra hzi
      have hzf : z ∈ frontier K := by rw [hK.frontier_eq]; exact ⟨hzK, hzi⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ⟨hzf, hzU⟩)
      exact Set.mem_iInter.mp hz i hi
    · exact Or.inr hzK
  have hd : Disjoint (interior K) Kᶜ :=
    Set.disjoint_left.mpr fun z hz hzc => hzc (interior_subset hz)
  rcases (header_finiteness_step10_avoid_connected L hL (ball p r)
      isOpen_ball (convex_ball p r)).subset_or_subset isOpen_interior hK.isOpen_compl hd hsides with h | h
  · exact hyK (interior_subset (h ⟨hyU, hy⟩))
  · exact h ⟨hxU, hx⟩ (interior_subset hxK)

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"the boundary ... is covered by its facets". In a finite closed covering
of a regular boundary by lower-dimensional pieces, the pieces of
codimension one already cover the whole boundary. -/
private theorem header_finiteness_step10_boundary_facets
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (K : Set V) (hK : IsClosed K) (hreg : closure (interior K) = K)
    {ι : Type*} [Finite ι] (C : ι → Set V) (hC : ∀ i, IsClosed (C i))
    (hcover : frontier K ⊆ ⋃ i, C i)
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (C i)).direction < Module.finrank ℝ V)
    (p : V) (hp : p ∈ frontier K) :
    ∃ i, p ∈ C i ∧ Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 = Module.finrank ℝ V := by
  classical
  by_contra hn
  let J := {i : ι // Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 = Module.finrank ℝ V}
  let H : Set V := ⋃ i : J, C i.val
  have hH : IsClosed H := isClosed_iUnion_of_finite fun i : J => hC i.val
  have hpH : p ∈ Hᶜ := by
    intro hpH
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpH
    exact hn ⟨i.val, hi, i.property⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hH.isOpen_compl p hpH
  let I := {i : ι // Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 ≠ Module.finrank ℝ V}
  have hlow (i : I) : Module.finrank ℝ (affineSpan ℝ (C i.val)).direction + 1 < Module.finrank ℝ V := by
    have := hdim i.val
    have := i.property
    omega
  apply header_finiteness_step10_boundary_not_thin K hK hreg p hp
    (fun i : I => affineSpan ℝ (C i.val)) hlow r hr
  rintro x ⟨hxK, hxball⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hxK)
  have hiI : Module.finrank ℝ (affineSpan ℝ (C i)).direction + 1 ≠ Module.finrank ℝ V := by
    intro heq
    exact hball hxball (Set.mem_iUnion.mpr ⟨⟨i, heq⟩, hi⟩)
  exact Set.mem_iUnion.mpr ⟨⟨i, hiI⟩, mem_affineSpan ℝ hi⟩


/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"facets of that cell". A set with nonempty intrinsic interior but empty
ambient interior has strictly smaller affine dimension than the ambient space. -/
private theorem header_finiteness_step10_rank_lt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (C : Set V) (hi : (intrinsicInterior ℝ C).Nonempty) (he : interior C = ∅) :
    Module.finrank ℝ (affineSpan ℝ C).direction < Module.finrank ℝ V := by
  by_contra hn
  have hdir : (affineSpan ℝ C).direction = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by omega))
  have hne : (affineSpan ℝ C : Set V).Nonempty :=
    (hi.mono intrinsicInterior_subset).mono (subset_affineSpan ℝ C)
  have hs : affineSpan ℝ C = ⊤ := (AffineSubspace.direction_eq_top_iff_of_nonempty hne).mp hdir
  rw [intrinsicInterior, hs] at hi
  have hopen : IsOpenMap ((↑) : (⊤ : AffineSubspace ℝ V) → V) :=
    (show IsOpen ((⊤ : AffineSubspace ℝ V) : Set V) from isOpen_univ).isOpenMap_subtype_val
  have hsub := (hopen.image_interior_subset (((↑) : (⊤ : AffineSubspace ℝ V) → V) ⁻¹' C)).trans
    (interior_mono (Set.image_preimage_subset _ _))
  have hh := hi.mono hsub
  simpa [he] using hh

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"∂A is covered by its facets". Apply the boundary covering lemma to the
finite listed prototype cells. -/
private theorem header_finiteness_step10_prototype_facets
    (A : PolyManifoldDomain d) (K : CellComplex A) (p : E d)
    (hp : p ∈ frontier A.carrier) :
    ∃ e ∈ K.cells, e.dim = d - 1 ∧ p ∈ e.carrier := by
  obtain ⟨e, he, hdim⟩ := header_finiteness_step10_boundary_facets A.carrier
    A.compact.isClosed A.regularClosed (fun e : {e // e ∈ K.cells} => e.val.carrier)
    (fun e => e.val.flat.compact.isClosed) (by
      intro x hx
      rw [← K.carriers_cover] at hx
      obtain ⟨e, he, hx⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hx
      exact Set.mem_iUnion.mpr ⟨⟨e, he⟩, hx⟩)
    (fun e => by
      change Module.finrank ℝ (cellDirection e.val.carrier) < Module.finrank ℝ (E d)
      rw [e.val.flat.dimension]
      simpa using K.dim_lt e.val e.property) p hp
  refine ⟨e.val, e.property, ?_, he⟩
  change Module.finrank ℝ (cellDirection e.val.carrier) + 1 = Module.finrank ℝ (E d) at hdim
  rw [e.val.flat.dimension] at hdim
  have hh : e.val.dim + 1 = d := by simpa using hdim
  omega

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"the relative boundary of each cell is covered by the facets of that
cell". Work in its direction space, using an affine isometry from that
space onto its affine hull. -/
private theorem header_finiteness_step10_cell_facets
    (A : PolyManifoldDomain d) (K : CellComplex A)
    (e : Cell d) (he : e ∈ K.cells) (p : E d) (hp : p ∈ relfrontier e.carrier) :
    ∃ f ∈ K.cells, f.dim + 1 = e.dim ∧ p ∈ f.carrier ∧ f.carrier ⊆ e.carrier := by
  classical
  let H := affineSpan ℝ e.carrier
  have hpe : p ∈ e.carrier := intrinsicFrontier_subset e.flat.compact.isClosed hp
  let q : H := ⟨p, mem_affineSpan ℝ hpe⟩
  letI : Nonempty H := ⟨q⟩
  let ψ : H.direction ≃ᵃⁱ[ℝ] H := AffineIsometryEquiv.vaddConst ℝ q
  let φ : H.direction →ᵃⁱ[ℝ] E d := H.subtypeₐᵢ.comp ψ.toAffineIsometry
  let C : Set H.direction := φ ⁻¹' e.carrier
  have himage (D : Set (E d)) (hD : D ⊆ H) : φ '' (φ ⁻¹' D) = D := by
    apply Set.image_preimage_eq_of_subset
    intro x hx
    exact ⟨ψ.symm ⟨x, hD hx⟩, by
      change (ψ (ψ.symm ⟨x, hD hx⟩) : E d) = x
      rw [ψ.apply_symm_apply]⟩
  have heH : e.carrier ⊆ H := subset_affineSpan ℝ e.carrier
  have hCimage : φ '' C = e.carrier := himage _ heH
  have hinter : φ '' interior C = relint e.carrier := by
    change (((↑) : H → E d) ∘ ψ.toHomeomorph) '' interior (ψ.toHomeomorph ⁻¹' (((↑) : H → E d) ⁻¹' e.carrier)) = _
    rw [Set.image_comp, ψ.toHomeomorph.image_interior, ψ.toHomeomorph.image_preimage]
    rfl
  have hfront : φ '' frontier C = relfrontier e.carrier := by
    change (((↑) : H → E d) ∘ ψ.toHomeomorph) '' frontier (ψ.toHomeomorph ⁻¹' (((↑) : H → E d) ⁻¹' e.carrier)) = _
    rw [Set.image_comp, ψ.toHomeomorph.image_frontier, ψ.toHomeomorph.image_preimage]
    rfl
  have hCclosed : IsClosed C := e.flat.compact.isClosed.preimage φ.continuous
  have hCreg : closure (interior C) = C := by
    apply φ.injective.image_injective
    rw [← φ.isometry.isClosedEmbedding.closure_image_eq, hinter, e.flat.regularClosed, hCimage]
  obtain ⟨b, hb, hboundary⟩ := K.boundary_union e he
  have hbsub (f : {f // f ∈ b}) : f.val.carrier ⊆ relfrontier e.carrier := by
    intro x hx
    rw [hboundary]
    exact Set.mem_iUnion.mpr ⟨f.val, Set.mem_iUnion.mpr ⟨f.property, hx⟩⟩
  have hbH (f : {f // f ∈ b}) : f.val.carrier ⊆ H :=
    (hbsub f).trans ((intrinsicFrontier_subset e.flat.compact.isClosed).trans heH)
  let D (f : {f // f ∈ b}) : Set H.direction := φ ⁻¹' f.val.carrier
  have hDfront (f : {f // f ∈ b}) : D f ⊆ frontier C := by
    intro x hx
    have hh := hbsub f hx
    rw [← hfront] at hh
    exact φ.injective.mem_set_image.mp hh
  have hDdim (f : {f // f ∈ b}) :
      Module.finrank ℝ (affineSpan ℝ (D f)).direction = f.val.dim := by
    have heq : (affineSpan ℝ f.val.carrier).direction =
        ((affineSpan ℝ (D f)).direction).map H.direction.subtype := by
      rw [← himage f.val.carrier (hbH f)]
      change (affineSpan ℝ (φ.toAffineMap '' D f)).direction = _
      rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
      rfl
    have hh := f.val.flat.dimension
    change Module.finrank ℝ (affineSpan ℝ f.val.carrier).direction = f.val.dim at hh
    rw [heq, Submodule.finrank_map_subtype_eq] at hh
    exact hh
  have hDlow (f : {f // f ∈ b}) :
      Module.finrank ℝ (affineSpan ℝ (D f)).direction < Module.finrank ℝ H.direction := by
    apply header_finiteness_step10_rank_lt
    · have hh := f.val.flat.relint_nonempty
      change (intrinsicInterior ℝ f.val.carrier).Nonempty at hh
      rw [← himage f.val.carrier (hbH f), φ.image_intrinsicInterior, Set.image_nonempty] at hh
      exact hh
    · apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hh := interior_mono (hDfront f) hx
      simpa [interior_frontier hCclosed] using hh
  have hpC : ψ.symm q ∈ frontier C := by
    apply φ.injective.mem_set_image.mp
    rw [hfront]
    simpa [φ] using hp
  obtain ⟨f, hpf, hfdim⟩ := header_finiteness_step10_boundary_facets C hCclosed hCreg D
    (fun f => f.val.flat.compact.isClosed.preimage φ.continuous) (by
      intro x hx
      have hh : φ x ∈ relfrontier e.carrier := hfront ▸ Set.mem_image_of_mem φ hx
      rw [hboundary] at hh
      obtain ⟨f, hf, hxf⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hh
      exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hxf⟩) hDlow (ψ.symm q) hpC
  refine ⟨f.val, hb f.property, ?_, ?_,
    (hbsub f).trans (intrinsicFrontier_subset e.flat.compact.isClosed)⟩
  · rw [hDdim] at hfdim
    exact hfdim.trans e.flat.dimension
  · change φ (ψ.symm q) ∈ f.val.carrier at hpf
    simpa [φ] using hpf


/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15):
"each still containing the vertex". A listed vertex in a positive-dimensional
listed cell lies in that cell's relative boundary, since listed relative
interiors are disjoint. -/
private theorem header_finiteness_step10_vertex_boundary
    (A : PolyManifoldDomain d) (K : CellComplex A)
    (v : Cell d) (hv : v ∈ K.vertices) (p : E d) (hp : p ∈ v.carrier)
    (e : Cell d) (he : e ∈ K.cells) (hpe : p ∈ e.carrier) (hdim : 0 < e.dim) :
    p ∈ relfrontier e.carrier := by
  have hvdim : v.dim = 0 := (Finset.mem_filter.mp hv).2
  have hvK : v ∈ K.cells := (Finset.mem_filter.mp hv).1
  have hbot : cellDirection v.carrier = ⊥ :=
    Submodule.finrank_eq_zero.mp (v.flat.dimension.trans hvdim)
  have hsingle : v.carrier.Subsingleton := by
    apply (vectorSpan_eq_bot_iff_subsingleton ℝ).mp
    simpa only [cellDirection, direction_affineSpan] using hbot
  have hvp : v.carrier = {p} := hsingle.eq_singleton_of_mem hp
  have hpv : p ∈ relint v.carrier := by simp [relint, hvp]
  have hne : v ≠ e := by
    intro h
    have := h ▸ hvdim
    omega
  have hnot : p ∉ relint e.carrier := fun hh =>
    Set.disjoint_left.mp (K.relint_disjoint v hvK e he hne) hpv hh
  change p ∈ intrinsicFrontier ℝ e.carrier
  rw [← closure_diff_intrinsicInterior, e.flat.compact.isClosed.closure_eq]
  exact ⟨hpe, hnot⟩

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15, used in 1.17):
"starting from a facet through the vertex one descends through incident
facets of facets". Reversing this descending sequence gives the complete
nested flag at the original listed vertex. -/
private theorem header_finiteness_step10_prototype_flag
    (A : PolyManifoldDomain d) (K : CellComplex A)
    (v : Cell d) (hv : v ∈ K.vertices) (p : E d) (hp : p ∈ v.carrier) :
    ∃ f : CellFlag K, ∀ j, p ∈ (f.cell j).carrier := by
  classical
  have hpA : p ∈ frontier A.carrier := by
    rw [← K.carriers_cover]
    exact Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨(Finset.mem_filter.mp hv).1, hp⟩⟩
  obtain ⟨e, he, hdim, hpe⟩ := header_finiteness_step10_prototype_facets A K p hpA
  let I := {e : Cell d // e ∈ K.cells ∧ p ∈ e.carrier}
  have hnext (e : I) (h : 0 < e.val.dim) :
      ∃ f : I, f.val.dim + 1 = e.val.dim ∧ f.val.carrier ⊆ e.val.carrier := by
    obtain ⟨f, hf, hfdim, hpf, hsub⟩ := header_finiteness_step10_cell_facets A K e.val e.property.1 p
      (header_finiteness_step10_vertex_boundary A K v hv p hp e.val e.property.1 e.property.2 h)
    exact ⟨⟨f, hf, hpf⟩, hfdim, hsub⟩
  let next (e : I) : I := if h : 0 < e.val.dim then (hnext e h).choose else e
  have next_dim (e : I) : (next e).val.dim = e.val.dim - 1 := by
    by_cases h : 0 < e.val.dim
    · have hh := (hnext e h).choose_spec.1
      simp only [next, dif_pos h]
      omega
    · have hh : e.val.dim = 0 := by omega
      simp [next, h, hh]
  have next_sub (e : I) : (next e).val.carrier ⊆ e.val.carrier := by
    by_cases h : 0 < e.val.dim
    · simpa only [next, dif_pos h] using (hnext e h).choose_spec.2
    · simp [next, h]
  let c (n : ℕ) : I := next^[n] ⟨e, he, hpe⟩
  have c_succ (n : ℕ) : c (n + 1) = next (c n) := Function.iterate_succ_apply' next n _
  have c_dim (n : ℕ) : (c n).val.dim = d - 1 - n := by
    induction n with
    | zero => simpa [c] using hdim
    | succ n ih => rw [c_succ, next_dim, ih]; omega
  have c_anti : Antitone (fun n => (c n).val.carrier) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [c_succ]
    exact next_sub (c n)
  let f : CellFlag K :=
    { cell := fun j => (c (d - 1 - j.val)).val
      mem := fun j => (c (d - 1 - j.val)).property.1
      dimension := fun j => by rw [c_dim]; omega
      nested := fun i j hij => c_anti (by have := i.isLt; have := j.isLt; omega) }
  exact ⟨f, fun j => (c (d - 1 - j.val)).property.2⟩

/-- Step 10 of the V4 proof of `header_finiteness` (V4 1.15, used in 1.17):
"the boundary complex of a polyhedral manifold has a full flag at every
vertex". This is only the initial flag, before any substitution is applied. -/
private theorem header_finiteness_step10_vertex_flag
    (t : FramedNode S) (p : E d) (hp : t.Lists 0 p) :
    ∃ f : CellFlag (S.cx t.ty), ∀ j, p ∈ t.cell 0 (f.cell j) := by
  obtain ⟨v, hv, x, hx, hxp⟩ := hp
  obtain ⟨f, hf⟩ := header_finiteness_step10_prototype_flag (S.proto t.ty) (S.cx t.ty) v hv x hx
  exact ⟨f, fun j => ⟨x, hf j, hxp⟩⟩


/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". Conjugated frames intertwine successive expansions. -/
private theorem header_finiteness_step11_conjugate_succ
    (R : E d ≃ₗ[ℝ] E d) (n : ℕ) (x : E d) :
    linearConj S.σ ((n + 1 : ℕ) : ℤ) R (S.σ x) =
      S.σ (linearConj S.σ (n : ℤ) R x) := by
  have heq : linearConj S.σ ((n + 1 : ℕ) : ℤ) R * S.σ =
      S.σ * linearConj S.σ (n : ℤ) R := by
    simp only [linearConj, Nat.cast_add, Nat.cast_one]
    group
  exact congrArg (fun L : E d ≃ₗ[ℝ] E d => L x) heq

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". The prescribed role frame has the same covariance. -/
private theorem header_finiteness_step11_placeChild_succ
    {A : S.ι} (i : S.I A) (n : ℕ) (x : E d) :
    S.placeChild (n + 1) i (S.σ x) = S.σ (S.placeChild n i x) := by
  rw [S.placeChild_apply, S.placeChild_apply,
    header_finiteness_step11_conjugate_succ, map_add, pow_succ']
  rfl

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". At height zero the role frame is the prescribed child frame. -/
private theorem header_finiteness_step11_placeChild_zero
    {A : S.ι} (i : S.I A) : S.placeChild 0 i = (S.child A i).frame := by
  apply AffineIsometryEquiv.ext
  intro x
  change linearConj S.σ (0 : ℤ) (S.child A i).rotation.toLinearEquiv x +
      (S.σ ^ 0) (S.child A i).offset =
    (S.child A i).rotation x + (S.child A i).offset
  simp [linearConj]

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". Append a child role to a native address,
leaving its original patch root fixed. -/
private def header_finiteness_step11_append (S : SubstSystem d) :
    (A : S.ι) → (n : ℕ) → (w : S.RoleWord A n) →
      S.I (S.nativeTile A n w).ty → S.RoleWord A (n + 1)
  | A, 0, _, i => ⟨i, ()⟩
  | A, n + 1, w, i => ⟨w.1,
      header_finiteness_step11_append S (S.child A w.1).ty n w.2 i⟩

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the child t_{n+1}". Appending a role retains its prescribed child type. -/
private theorem header_finiteness_step11_append_type
    (A : S.ι) (n : ℕ) (w : S.RoleWord A n) (i : S.I (S.nativeTile A n w).ty) :
    (S.nativeTile A (n + 1) (header_finiteness_step11_append S A n w i)).ty =
      (S.child (S.nativeTile A n w).ty i).ty := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih => exact ih (S.child A w.1).ty w.2 i

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". Appending a role realizes subdivision after
inflation, even though the native-address recursion reads roles from the root. -/
private theorem header_finiteness_step11_append_frame
    (A : S.ι) (n : ℕ) (w : S.RoleWord A n) (i : S.I (S.nativeTile A n w).ty)
    (x : E d) :
    (S.nativeTile A (n + 1) (header_finiteness_step11_append S A n w i)).frame x =
      S.σ ((S.nativeTile A n w).frame (S.σ.symm ((S.child (S.nativeTile A n w).ty i).frame x))) := by
  induction n generalizing A with
  | zero =>
    change S.placeChild 0 i x = S.σ (S.σ.symm ((S.child A i).frame x))
    rw [S.σ.apply_symm_apply, header_finiteness_step11_placeChild_zero]
    rfl
  | succ n ih =>
    change S.placeChild (0 + (n + 1)) w.1
      ((S.nativeTile (S.child A w.1).ty (n + 1)
        (header_finiteness_step11_append S (S.child A w.1).ty n w.2 i)).frame x) =
      S.σ (S.placeChild (0 + n) w.1 ((S.nativeTile (S.child A w.1).ty n w.2).frame
        (S.σ.symm ((S.child (S.nativeTile (S.child A w.1).ty n w.2).ty i).frame x))))
    simp only [Nat.zero_add]
    rw [ih, header_finiteness_step11_placeChild_succ]

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". The patch's specified ground frame obeys the
same covariance as a substitution role frame. -/
private theorem header_finiteness_step11_inflated_frame_succ
    (t : FramedNode S) (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup)
    (n : ℕ) (x : E d) :
    compatibleInflatedFrame t ht (n + 1) (S.σ x) =
      S.σ (compatibleInflatedFrame t ht n x) := by
  have hQ (n : ℕ) (x : E d) :
      (Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
        t.frame.linearIsometryEquiv ht)) x =
      linearConj S.σ (n : ℤ) t.frame.linearIsometryEquiv.toLinearEquiv x :=
    congrArg (fun L : E d ≃ₗ[ℝ] E d => L x)
      (Classical.choose_spec (S.rotGroup_conj_zpow (n : ℤ)
        t.frame.linearIsometryEquiv ht)).2
  change (Classical.choose (S.rotGroup_conj_zpow ((n + 1 : ℕ) : ℤ)
      t.frame.linearIsometryEquiv ht)) (S.σ x) + (S.σ ^ (n + 1)) (t.frame 0) =
    S.σ ((Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
      t.frame.linearIsometryEquiv ht)) x + (S.σ ^ n) (t.frame 0))
  rw [hQ, hQ, header_finiteness_step11_conjugate_succ, map_add, pow_succ']
  rfl

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"the children of σ t_n". The appended address uses exactly the actual
frame of the inflated patch tile followed by the prescribed child frame. -/
private theorem header_finiteness_step11_native_child
    (P : CompatiblePatch S) (n : ℕ) (a : P.Address n) (i : S.I (P.native n a).ty) :
    ∃ b : P.Address (n + 1),
      (P.native (n + 1) b).ty = (S.child (P.native n a).ty i).ty ∧
      ∀ x, (P.native (n + 1) b).frame x =
        S.σ ((P.native n a).frame (S.σ.symm ((S.child (P.native n a).ty i).frame x))) := by
  refine ⟨⟨a.1, header_finiteness_step11_append S a.1.val.ty n a.2 i⟩,
    header_finiteness_step11_append_type a.1.val.ty n a.2 i, ?_⟩
  intro x
  change compatibleInflatedFrame a.1.val (P.compatible _ a.1.property) (n + 1)
    ((S.nativeTile a.1.val.ty (n + 1)
      (header_finiteness_step11_append S a.1.val.ty n a.2 i)).frame x) = _
  rw [header_finiteness_step11_append_frame, header_finiteness_step11_inflated_frame_succ]
  rfl


/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"cells of t_n". A ground cell is placed directly by its tile frame. -/
private theorem header_finiteness_step11_cell_zero (t : FramedNode S) (e : Cell d) :
    t.cell 0 e = t.frame '' e.carrier := rfl

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"cells of t_n". The ground carrier is the isometric prototype carrier. -/
private theorem header_finiteness_step11_carrier_zero (t : FramedNode S) :
    t.carrier 0 = t.frame '' (S.proto t.ty).carrier := by
  simp [FramedNode.carrier, placedSet, SubstSystem.supertile]

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"cells of t_n". A listed cell is contained in its closed tile carrier. -/
private theorem header_finiteness_step11_cell_subset (t : FramedNode S)
    (e : Cell d) (he : e ∈ (S.cx t.ty).cells) : t.cell 0 e ⊆ t.carrier 0 := by
  rw [header_finiteness_step11_cell_zero, header_finiteness_step11_carrier_zero]
  apply Set.image_mono
  intro x hx
  apply (S.proto t.ty).compact.isClosed.frontier_subset
  rw [← (S.cx t.ty).carriers_cover]
  exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he, hx⟩⟩

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"σ e is a union of placed j-cells of the children". An expanded incident
cell has an incident native child cell of the same dimension; its carrier
is contained in the expanded parent cell. No uniqueness is used in this step. -/
private theorem header_finiteness_step11_refinement
    (P : CompatiblePatch S) (p : E d) (n : ℕ) (a : P.Incident p n)
    (e : CellName S (P.native n a.val).ty)
    (he : (S.σ ^ n) p ∈ (P.native n a.val).cell 0 e.val) :
    ∃ (b : P.Incident p (n + 1)) (f : CellName S (P.native (n + 1) b.val).ty),
      P.IncidentChild p n a b ∧ f.val.dim = e.val.dim ∧
      (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b.val).cell 0 f.val ∧
      (P.native (n + 1) b.val).cell 0 f.val ⊆
        S.σ '' (P.native n a.val).cell 0 e.val := by
  classical
  rw [header_finiteness_step11_cell_zero] at he
  obtain ⟨x, hxe, hxp⟩ := he
  obtain ⟨c, hc⟩ := S.heredity (P.native n a.val).ty e.val e.property
  have hsx : S.σ x ∈ ⋃ q ∈ c, placedSet (S.child (P.native n a.val).ty q.1).frame q.2.val.carrier := by
    rw [← hc]
    exact Set.mem_image_of_mem S.σ hxe
  obtain ⟨q, hq, y, hy, hyx⟩ := by
    simpa only [Set.mem_iUnion, exists_prop, placedSet, Set.mem_image] using hsx
  obtain ⟨b, hty, hframe⟩ := header_finiteness_step11_native_child P n a.val q.1
  have hmem : q.2.val ∈ (S.cx (P.native (n + 1) b).ty).cells := by
    rw [hty]
    exact q.2.property.1
  have hpoint : (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b).cell 0 q.2.val := by
    rw [header_finiteness_step11_cell_zero]
    refine ⟨y, hy, ?_⟩
    rw [hframe, hyx, S.σ.symm_apply_apply, hxp, pow_succ']
    rfl
  have hinc : (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b).carrier 0 :=
    header_finiteness_step11_cell_subset _ _ hmem hpoint
  have hsub : ∀ (K L : Set (E d)),
      (S.child (P.native n a.val).ty q.1).frame '' K ⊆ S.σ '' L →
      (P.native (n + 1) b).frame '' K ⊆ S.σ '' ((P.native n a.val).frame '' L) := by
    intro K L h z hz
    obtain ⟨u, hu, rfl⟩ := hz
    obtain ⟨v, hv, hvu⟩ := h (Set.mem_image_of_mem _ hu)
    refine ⟨(P.native n a.val).frame v, Set.mem_image_of_mem _ hv, ?_⟩
    rw [hframe, ← hvu, S.σ.symm_apply_apply]
  refine ⟨⟨b, hinc⟩, ⟨q.2.val, hmem⟩, ?_, q.2.property.2, hpoint, ?_⟩
  · change (P.native (n + 1) b).carrier 0 ⊆ S.σ '' (P.native n a.val).carrier 0
    rw [header_finiteness_step11_carrier_zero, header_finiteness_step11_carrier_zero, hty]
    apply hsub
    rw [S.children_cover]
    exact Set.subset_iUnion (fun i => placedSet (S.child (P.native n a.val).ty i).frame
      (S.proto (S.child (P.native n a.val).ty i).ty).carrier) q.1
  · rw [header_finiteness_step11_cell_zero, header_finiteness_step11_cell_zero]
    apply hsub
    rw [hc]
    intro z hz
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq, hz⟩⟩

/-- Step 12 of the V4 proof of `header_finiteness` (V4 1.17):
"regarded as the tuple of its direction spaces". Taking directions of a
placed cell removes translation and retains the actual orthogonal frame. -/
private theorem header_finiteness_step12_frame_direction
    (t : FramedNode S) (e : Cell d) :
    cellDirection (t.cell 0 e) =
      (cellDirection e.carrier).map t.frame.linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  change (affineSpan ℝ (t.frame.toAffineEquiv.toAffineMap '' e.carrier)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  rfl

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim):
"its affine hull is σ aff e by dimension". Direction spaces commute
with every invertible linear map, including the anisotropic expansion. -/
private theorem header_finiteness_step11_linear_direction
    (L : E d ≃ₗ[ℝ] E d) (K : Set (E d)) :
    cellDirection (L '' K) = (cellDirection K).map L.toLinearMap := by
  change (affineSpan ℝ (L.toAffineEquiv.toAffineMap '' K)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  rfl

/-- Step 11 of the V4 proof of `header_finiteness` (V4 1.15, Claim, used in 1.17):
"some j-cell ... contains [the vertex] and lies in σ e". Heredity at a
unique incident child preserves the direction of one listed cell.
The uniqueness hypothesis excludes branching, and the cell must contain the anchor. -/
private theorem header_finiteness_step11_child_cell
    (P : CompatiblePatch S) (p : E d) (n : ℕ)
    (a : P.Incident p n) (b : P.Incident p (n + 1))
    (hab : P.IncidentChild p n a b)
    (hunique : ∀ b' : P.Incident p (n + 1), P.IncidentChild p n a b' → b' = b)
    (e : CellName S (P.native n a.val).ty)
    (he : (S.σ ^ n) p ∈ (P.native n a.val).cell 0 e.val) :
    ∃ f : CellName S (P.native (n + 1) b.val).ty,
      f.val.dim = e.val.dim ∧
      (S.σ ^ (n + 1)) p ∈ (P.native (n + 1) b.val).cell 0 f.val ∧
      cellDirection ((P.native (n + 1) b.val).cell 0 f.val) =
        (cellDirection ((P.native n a.val).cell 0 e.val)).map S.σ.toLinearMap := by
  obtain ⟨b', f, hb', hdim, hf, hsub⟩ := header_finiteness_step11_refinement P p n a e he
  obtain rfl := hunique b' hb'
  refine ⟨f, hdim, hf, ?_⟩
  have hle := AffineSubspace.direction_le (affineSpan_mono ℝ hsub)
  change cellDirection ((P.native (n + 1) b'.val).cell 0 f.val) ≤
    cellDirection (S.σ '' (P.native n a.val).cell 0 e.val) at hle
  rw [header_finiteness_step11_linear_direction] at hle
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [header_finiteness_step12_frame_direction, header_finiteness_step12_frame_direction]
  simp only [LinearEquiv.finrank_map_eq]
  exact f.val.flat.dimension.trans (hdim.trans e.val.flat.dimension.symm)


/-- Step 13 of the V4 proof of `header_finiteness` (V4 1.17):
"the Claim in the proof of 1.15 ... gives a native flag". Iterate the
single-cell transport along a nonbranching listing tail; the transported
cells need not be nested, but their direction spaces are a complete flag. -/
private theorem header_finiteness_step13_tail_flag
    (P : CompatiblePatch S) (p : E d) (N : ℕ) (t : P.IncidentTail p N)
    (hunique : ∀ m (b : P.Incident p (N + m + 1)),
      P.IncidentChild p (N + m) (t.node m) b → b = t.node (m + 1))
    (hlisted : (P.native N (t.node 0).val).Lists 0 ((S.σ ^ N) p)) :
    ∃ V : ℕ → Submodule ℝ (E d),
      (∀ i ≤ d, Module.finrank ℝ (V i) = i) ∧
      (∀ i < d, V i ≤ V (i + 1)) ∧
      (∀ i ≤ d, V i ∈ S.hPi ∨ V i = ⊤) ∧
      ∀ m i, i ≤ d →
        ((V i).map (S.σ ^ m).toLinearMap).map
          (P.native (N + m) (t.node m).val).frame.linearIsometryEquiv.symm.toLinearEquiv.toLinearMap
          ∈ S.cellDirections ∪ {⊤} := by
  classical
  obtain ⟨f, hf⟩ := header_finiteness_step10_vertex_flag _ _ hlisted
  let V (i : ℕ) : Submodule ℝ (E d) :=
    if hi : i < d then cellDirection ((P.native N (t.node 0).val).cell 0 (f.cell ⟨i, hi⟩))
    else ⊤
  have hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i := by
    intro i hi
    by_cases hid : i < d
    · rw [show V i = cellDirection ((P.native N (t.node 0).val).cell 0 (f.cell ⟨i, hid⟩))
          from dif_pos hid, header_finiteness_step12_frame_direction, LinearEquiv.finrank_map_eq]
      exact (f.cell ⟨i, hid⟩).flat.dimension.trans (f.dimension ⟨i, hid⟩)
    · have heq : i = d := by omega
      rw [show V i = ⊤ from dif_neg hid]
      simp [heq]
  have hmono : ∀ i < d, V i ≤ V (i + 1) := by
    intro i hi
    by_cases hj : i + 1 < d
    · simp only [V, dif_pos hi, dif_pos hj, header_finiteness_step12_frame_direction]
      apply Submodule.map_mono
      exact AffineSubspace.direction_le (affineSpan_mono ℝ
        (f.nested ⟨i, hi⟩ ⟨i + 1, hj⟩ (by simp)))
    · simp [V, hj]
  have hV : ∀ i ≤ d, V i ∈ S.hPi ∨ V i = ⊤ := by
    intro i hi
    by_cases hid : i < d
    · left
      refine ⟨cellDirection (f.cell ⟨i, hid⟩).carrier,
        ⟨(P.native N (t.node 0).val).ty, f.cell ⟨i, hid⟩, f.mem _, rfl⟩,
        (P.native N (t.node 0).val).frame.linearIsometryEquiv,
        P.native_compatible N (t.node 0).val, ?_⟩
      simp only [V, dif_pos hid, header_finiteness_step12_frame_direction]
    · exact Or.inr (by simp [V, hid])
  have hcell (i : ℕ) (hi : i < d) : ∀ m : ℕ,
      ∃ e : CellName S (P.native (N + m) (t.node m).val).ty,
        (S.σ ^ (N + m)) p ∈ (P.native (N + m) (t.node m).val).cell 0 e.val ∧
        cellDirection ((P.native (N + m) (t.node m).val).cell 0 e.val) =
          (V i).map (S.σ ^ m).toLinearMap := by
    intro m
    induction m with
    | zero =>
      refine ⟨⟨f.cell ⟨i, hi⟩, f.mem _⟩, hf _, ?_⟩
      simp [V, hi]
    | succ m ih =>
      obtain ⟨e, he, hdir⟩ := ih
      obtain ⟨e', _, he', hdir'⟩ := header_finiteness_step11_child_cell P p
        (N + m) (t.node m) (t.node (m + 1)) (t.step m) (hunique m) e he
      refine ⟨e', he', ?_⟩
      calc
        _ = (cellDirection ((P.native (N + m) (t.node m).val).cell 0 e.val)).map
            S.σ.toLinearMap := hdir'
        _ = _ := by
          rw [hdir, ← Submodule.map_comp]
          simp [pow_succ', LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp]
  refine ⟨V, hdim, hmono, hV, ?_⟩
  intro m i hi
  by_cases hid : i < d
  · obtain ⟨e, he, hdir⟩ := hcell i hid m
    rw [← hdir, header_finiteness_step12_frame_direction, ← Submodule.map_comp]
    simp only [LinearIsometryEquiv.toLinearEquiv_symm, LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, Submodule.map_id]
    exact Or.inl ⟨(P.native (N + m) (t.node m).val).ty, e.val, e.property, rfl⟩
  · simp [V, hid, Submodule.map_top]

/-- Step 14 of the V4 proof of `header_finiteness` (V4 1.17):
"the header ... takes finitely many values" on a listing tail. Pulling
the initial flag back by σ^N lets the power formula apply to the original
cone tuple, without assuming that the frames commute with σ. -/
private theorem header_finiteness_step14_listing_tail
    (P : CompatiblePatch S) (F : PowerFactorisation S) (p : E d)
    (N : ℕ) (t : P.IncidentTail p N)
    (hunique : ∀ m (b : P.Incident p (N + m + 1)),
      P.IncidentChild p (N + m) (t.node m) b → b = t.node (m + 1))
    (hlisted : (P.native N (t.node 0).val).Lists 0 ((S.σ ^ N) p))
    {s : ℕ} (G : Fin s → Set (E d)) (hG : ∀ j, HPiCone S.hPi (G j)) :
    (Set.range (fun m => fun j =>
      (P.native (N + m) (t.node m).val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ (N + m)) '' G j))).Finite := by
  obtain ⟨V, hdim, hmono, hV, hframe⟩ :=
    header_finiteness_step13_tail_flag P p N t hunique hlisted
  let W (i : ℕ) := (V i).map ((S.σ ^ N)⁻¹).toLinearMap
  apply header_finiteness_step9_residual_rotations F N
    (fun m => (P.native (N + m) (t.node m).val).frame.linearIsometryEquiv) W
    (fun i hi => (LinearEquiv.finrank_map_eq _ _).trans (hdim i hi))
    (fun i hi => Submodule.map_mono (hmono i hi)) ?_ ?_ G hG
  · intro i hi
    rcases hV i hi with h | h
    · exact Or.inl (header_finiteness_step8_inverse_directions N (V i) h)
    · exact Or.inr (by simp [W, h])
  · intro m i hi
    have heq : (W i).map (S.σ ^ (N + m)).toLinearMap =
        (V i).map (S.σ ^ m).toLinearMap := by
      simp only [W, ← Submodule.map_comp, ← Module.End.mul_eq_comp,
        ← LinearEquiv.coe_toLinearMap_mul]
      rw [Nat.add_comm N m, pow_add, mul_inv_cancel_right]
    rw [heq]
    exact hframe m i hi

/-- Step 15 of the V4 proof of `header_finiteness` (V4 1.17):
"beyond all branching". Starting at the unique-child cutoff, recursively
choose the unique children. Every later incident tile belongs to one of
these tails, indexed by the finite set of incident tiles at the cutoff. -/
private theorem header_finiteness_step15_tail_cover
    (P : CompatiblePatch S) [Nonempty S.ι] (p : E d) :
    ∃ (N : ℕ) (t : P.Incident p N → P.IncidentTail p N),
      (∀ m, Function.Surjective (fun a => (t a).node m)) ∧
      ∀ n, N ≤ n → ∀ a : P.Incident p n,
        ∃! b : P.Incident p (n + 1), P.IncidentChild p n a b := by
  classical
  obtain ⟨_, _, N, hN⟩ := P.incidentForest p
  let next (m : ℕ) (a : P.Incident p (N + m)) : P.Incident p (N + (m + 1)) :=
    Classical.choose (hN (N + m) (by omega) a)
  have hnext (m : ℕ) (a : P.Incident p (N + m)) :
      P.IncidentChild p (N + m) a (next m a) :=
    (Classical.choose_spec (hN (N + m) (by omega) a)).1
  let node (a : P.Incident p N) : ∀ m, P.Incident p (N + m) :=
    fun m => Nat.rec a (fun m b => next m b) m
  let t (a : P.Incident p N) : P.IncidentTail p N :=
    ⟨node a, fun m => hnext m (node a m)⟩
  refine ⟨N, t, ?_, hN⟩
  intro m
  induction m with
  | zero => exact fun a => ⟨a, rfl⟩
  | succ m ih =>
    intro b
    let a := P.incidentParent p (N + m) b
    obtain ⟨a₀, ha₀⟩ := ih a
    refine ⟨a₀, ?_⟩
    change next m (node a₀ m) = b
    change node a₀ m = a at ha₀
    rw [ha₀]
    exact ExistsUnique.unique (hN (N + m) (by omega) a)
      (hnext m a) (P.incidentParent_spec p (N + m) b)

/-- Step 16 of the V4 proof of `header_finiteness` (V4 1.17):
"a tail either never lists ... or lists it from some depth on". A tail
with no listing contributes nothing; otherwise split at a listing depth
and keep the earlier, finite prefix separately. -/
private theorem header_finiteness_step16_tail_listings
    (P : CompatiblePatch S) (F : PowerFactorisation S) (p : E d)
    (N : ℕ) (t : P.IncidentTail p N)
    (hunique : ∀ n, N ≤ n → ∀ a : P.Incident p n,
      ∃! b : P.Incident p (n + 1), P.IncidentChild p n a b)
    {s : ℕ} (G : Fin s → Set (E d)) (hG : ∀ j, HPiCone S.hPi (G j)) :
    {K | ∃ m, (P.native (N + m) (t.node m).val).Lists 0 ((S.σ ^ (N + m)) p) ∧
      K = fun j => (P.native (N + m) (t.node m).val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ (N + m)) '' G j)}.Finite := by
  classical
  let K (m : ℕ) := fun j =>
    (P.native (N + m) (t.node m).val).frame.linearIsometryEquiv.symm ''
      ((S.σ ^ (N + m)) '' G j)
  by_cases h : ∃ k, (P.native (N + k) (t.node k).val).Lists 0 ((S.σ ^ (N + k)) p)
  · obtain ⟨k, hk⟩ := h
    have hcast (n m : ℕ) (h : n = m) (a : P.Incident p m) :
        P.native n (h.symm ▸ a : P.Incident p n).val = P.native m a.val := by
      cases h
      rfl
    let t' : P.IncidentTail p (N + k) :=
      { node := fun r => (Nat.add_assoc N k r).symm ▸ t.node (k + r)
        step := fun r => by
          rw [hcast _ _ (Nat.add_assoc N k (r + 1)), hcast _ _ (Nat.add_assoc N k r)]
          simpa only [Nat.add_assoc] using t.step (k + r) }
    have hu (m : ℕ) (b : P.Incident p (N + k + m + 1))
        (hb : P.IncidentChild p (N + k + m) (t'.node m) b) : b = t'.node (m + 1) :=
      ExistsUnique.unique (hunique _ (by omega) (t'.node m)) hb (t'.step m)
    have hl : (P.native (N + k) (t'.node 0).val).Lists 0 ((S.σ ^ (N + k)) p) := by
      simpa [t'] using hk
    have hf : (Set.range (fun r => K (k + r))).Finite := by
      simpa only [t', K, hcast, Nat.add_assoc] using
        header_finiteness_step14_listing_tail P F p (N + k) t' hu hl G hG
    apply ((Set.finite_range (fun r : Fin k => K r.val)).union hf).subset
    rintro C ⟨m, hm, rfl⟩
    rcases lt_or_ge m k with hmk | hkm
    · exact Or.inl ⟨⟨m, hmk⟩, rfl⟩
    · exact Or.inr ⟨m - k, by simp only [Nat.add_sub_of_le hkm]; rfl⟩
  · apply Set.finite_empty.subset
    rintro C ⟨m, hm, _⟩
    exact (h ⟨m, hm⟩).elim

/-- Step 17 of the V4 proof of `header_finiteness` (V4 1.17):
"Finitely many tails and the finite prefix give the result". Only listed
incident tiles enter the union, so no common-listed assumption is needed. -/
private theorem header_finiteness_step17_cone_tuples
    (P : CompatiblePatch S) [Nonempty S.ι] (p : E d)
    {s : ℕ} (G : Fin s → Set (E d)) (hG : ∀ j, HPiCone S.hPi (G j)) :
    {K | ∃ (n : ℕ) (a : P.Incident p n),
      (P.native n a.val).Lists 0 ((S.σ ^ n) p) ∧
      K = fun j => (P.native n a.val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ n) '' G j)}.Finite := by
  classical
  obtain ⟨F⟩ := power_factorisation S
  obtain ⟨N, t, hcover, hN⟩ := header_finiteness_step15_tail_cover P p
  have hpref : (⋃ n : Fin N, Set.range (fun a : P.Incident p n.val =>
      fun j => (P.native n.val a.val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ n.val) '' G j))).Finite :=
    Set.finite_iUnion fun n => Set.finite_range _
  have ht := Set.finite_iUnion fun a : P.Incident p N =>
    header_finiteness_step16_tail_listings P F p N (t a) hN G hG
  apply (hpref.union ht).subset
  rintro K ⟨n, a, ha, rfl⟩
  rcases lt_or_ge n N with hn | hn
  · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨n, hn⟩, a, rfl⟩)
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    obtain ⟨a₀, rfl⟩ := hcover m a
    exact Or.inr (Set.mem_iUnion.mpr ⟨a₀, m, ha, rfl⟩)

/-- P12, V4 1.17: finite actual header tuples over all listing incident tiles.
No common-listed hypothesis is needed: only tiles listing the anchor contribute. -/
theorem header_finiteness (p : E d) {s : ℕ} (G : Fin s → Set (E d))
    (hG : ∀ j, HPiCone S.hPi (G j)) : (P.headers p G).Finite := by
  classical
  cases isEmpty_or_nonempty S.ι with
  | inl h =>
    letI := h
    exact Set.finite_empty.subset (fun h _ => isEmptyElim h.ty)
  | inr h =>
    letI := h
    let Label := Σ A : S.ι, {e // e ∈ (S.cx A).vertices}
    have hf := (header_finiteness_step17_cone_tuples P p G hG).biUnion
      (fun K _ => Set.finite_range (fun l : Label => (⟨l.1, l.2, K⟩ : Header S s)))
    apply hf.subset
    intro h hh
    obtain ⟨n, a, hv, hty, hc⟩ := hh
    have hlisted : (P.native n a.val).Lists 0 ((S.σ ^ n) p) := by
      refine ⟨h.vertex.val, ?_, hv⟩
      rw [← hty]
      exact h.vertex.property
    refine Set.mem_iUnion.mpr ⟨h.cones, Set.mem_iUnion.mpr
      ⟨⟨n, a, hlisted, funext hc⟩, ?_⟩⟩
    exact ⟨⟨h.ty, h.vertex⟩, by cases h; rfl⟩

/-- P13, V4 1.18: a complete star in a chosen incident tile's isometric frame,
with arbitrary labels from `Y`. Every incident tile and its vertex name is retained. -/
def positionedStar {Y : Type} (p : E d) (n : ℕ) (anchor : P.Incident p n)
    (label : P.Incident p n → Y) : Set (FramedNode S × Cell d × Y) :=
  {z | ∃ (a : P.Incident p n) (v : Cell d),
    v ∈ (S.cx (P.native n a.val).ty).vertices ∧
    (S.σ ^ n) p ∈ (P.native n a.val).cell 0 v ∧
    z = ((P.native n a.val).move (P.native n anchor.val).frame.symm, v, label a)}

/-- P13, V4 1.18: all possible complete positioned stars, allowing every
labelling at every depth and every choice of reference tile. -/
def positionedStars (Y : Type) (p : E d) :
    Set (Set (FramedNode S × Cell d × Y)) :=
  {s | ∃ (n : ℕ) (anchor : P.Incident p n) (label : P.Incident p n → Y),
    s = P.positionedStar p n anchor label}

/-- Step 1 of the V4 proof of `positioned_stars_finite` (V4 1.18): "the relative
orthogonal placement `B_{t^{i₀}_n}⁻¹ B_{t^i_n}` carries this native flag to
`B_{t^{i₀}_n}⁻¹ σ^{n-N} 𝓕_i`, which lies in a finite set; so the relative placement
lies in a finite set". Along two fixed nonbranching listing tails, the relative
linear placements take finitely many values. -/
private theorem positioned_stars_finite_step1_tail_rotations
    (F : PowerFactorisation S) (p : E d) (N : ℕ) (t₀ t₁ : P.IncidentTail p N)
    (hunique₀ : ∀ m (b : P.Incident p (N + m + 1)),
      P.IncidentChild p (N + m) (t₀.node m) b → b = t₀.node (m + 1))
    (hlisted₀ : (P.native N (t₀.node 0).val).Lists 0 ((S.σ ^ N) p))
    (hunique₁ : ∀ m (b : P.Incident p (N + m + 1)),
      P.IncidentChild p (N + m) (t₁.node m) b → b = t₁.node (m + 1))
    (hlisted₁ : (P.native N (t₁.node 0).val).Lists 0 ((S.σ ^ N) p)) :
    (Set.range (fun m => (P.native (N + m) (t₁.node m).val).frame.linearIsometryEquiv.trans
      (P.native (N + m) (t₀.node m).val).frame.linearIsometryEquiv.symm)).Finite := by
  classical
  obtain ⟨V, hdim, hmono, hV, hframe⟩ :=
    header_finiteness_step13_tail_flag P p N t₁ hunique₁ hlisted₁
  let B₀ : ℕ → Ortho d := fun m => (P.native (N + m) (t₀.node m).val).frame.linearIsometryEquiv
  let B₁ : ℕ → Ortho d := fun m => (P.native (N + m) (t₁.node m).val).frame.linearIsometryEquiv
  let W (i : ℕ) := (V i).map ((S.σ ^ N)⁻¹).toLinearMap
  let G : Fin (d + 1) → Set (E d) := fun j => (W j.val : Set (E d))
  have hG : ∀ j, HPiCone S.hPi (G j) := by
    intro j
    apply header_finiteness_step7_subspace_cone
    rcases hV j.val (by omega) with h | h
    · exact Or.inl (header_finiteness_step8_inverse_directions N (V j.val) h)
    · exact Or.inr (by simp [W, h])
  have hK := header_finiteness_step14_listing_tail P F p N t₀ hunique₀ hlisted₀ G hG
  have heq : ∀ m i, (W i).map (S.σ ^ (N + m)).toLinearMap =
      (V i).map (S.σ ^ m).toLinearMap := by
    intro m i
    simp only [W, ← Submodule.map_comp, ← Module.End.mul_eq_comp,
      ← LinearEquiv.coe_toLinearMap_mul]
    rw [Nat.add_comm N m, pow_add, mul_inv_cancel_right]
  let Z (m i : ℕ) : Submodule ℝ (E d) :=
    ((V i).map (S.σ ^ m).toLinearMap).map (B₀ m).symm.toLinearEquiv.toLinearMap
  have hZ : ∀ m (j : Fin (d + 1)), ((Z m j.val : Submodule ℝ (E d)) : Set (E d)) =
      (B₀ m).symm '' ((S.σ ^ (N + m)) '' G j) := by
    intro m j
    have h1 : ((S.σ ^ (N + m)) '' G j) = (((W j.val).map (S.σ ^ (N + m)).toLinearMap :
        Submodule ℝ (E d)) : Set (E d)) := (Submodule.map_coe _ _).symm
    rw [h1, heq]
    exact Submodule.map_coe _ _
  let Ztr (m : ℕ) (i : ℕ) : Submodule ℝ (E d) := if i ≤ d then Z m i else ⊥
  let Φ : (Fin (d + 1) → Set (E d)) → ℕ → Submodule ℝ (E d) := fun K i =>
    if h : i ≤ d then Submodule.span ℝ (K ⟨i, by omega⟩) else ⊥
  have hZfin : (Set.range Ztr).Finite := by
    apply (hK.image Φ).subset
    rintro _ ⟨m, rfl⟩
    refine ⟨_, ⟨m, rfl⟩, ?_⟩
    funext i
    by_cases h : i ≤ d
    · rw [show Ztr m i = Z m i from if_pos h]
      change (if h : i ≤ d then Submodule.span ℝ _ else ⊥) = _
      rw [dif_pos h]
      show Submodule.span ℝ ((B₀ m).symm '' ((S.σ ^ (N + m)) '' G ⟨i, by omega⟩)) = Z m i
      rw [← hZ m ⟨i, by omega⟩, Submodule.span_eq]
    · rw [show Ztr m i = ⊥ from if_neg h]
      change (if h : i ≤ d then Submodule.span ℝ _ else ⊥) = _
      rw [dif_neg h]
  have hdim' : ∀ m, ∀ i ≤ d, Module.finrank ℝ (Ztr m i) = i := by
    intro m i hi
    rw [show Ztr m i = Z m i from if_pos hi]
    rw [LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]
    exact hdim i hi
  have hmono' : ∀ m, ∀ i < d, Ztr m i ≤ Ztr m (i + 1) := by
    intro m i hi
    rw [show Ztr m i = Z m i from if_pos (show i ≤ d by omega),
      show Ztr m (i + 1) = Z m (i + 1) from if_pos (show i + 1 ≤ d by omega)]
    exact Submodule.map_mono (Submodule.map_mono (hmono i hi))
  let Q (m : ℕ) : Ortho d := (B₀ m).trans (B₁ m).symm
  have hQ : ∀ m, Q m ∈ {R : Ortho d | ∀ i ≤ d,
      (Ztr m i).map R.toLinearEquiv.toLinearMap ∈ S.cellDirections ∪ {⊤}} := by
    intro m i hi
    rw [show Ztr m i = Z m i from if_pos hi]
    change Submodule.map _ (Submodule.map _ _) ∈ _
    rw [← Submodule.map_comp]
    convert hframe m i hi using 2
    ext x
    simp [Q, B₀, B₁]
  have hU := Set.Finite.biUnion hZfin (t := fun Zf => {R : Ortho d | ∀ i ≤ d,
      (Zf i).map R.toLinearEquiv.toLinearMap ∈ S.cellDirections ∪ {⊤}}) (by
    rintro _ ⟨m, rfl⟩
    exact header_finiteness_step5_catalogue_transporters _ header_finiteness_step6_directions
      (Ztr m) (hdim' m) (hmono' m))
  apply (hU.image (fun R : Ortho d => R.symm)).subset
  rintro _ ⟨m, rfl⟩
  exact ⟨Q m, Set.mem_iUnion₂.mpr ⟨Ztr m, ⟨m, rfl⟩, hQ m⟩, rfl⟩

/-- Step 2 of the V4 proof of `positioned_stars_finite` (V4 1.18): "Choose `N` as in
the proof of 1.17 (all tails list `σⁿp` since `p` is common-listed)". The finite prefix
below the splitting cutoff and the finitely many pairs of tails beyond it give finitely
many relative linear placements of two incident tiles at a common depth. -/
private theorem positioned_stars_finite_step2_rotations [Nonempty S.ι] (p : E d)
    (hp : P.CommonListed p) :
    {L : Ortho d | ∃ (n : ℕ) (a b : P.Incident p n),
      L = (P.native n a.val).frame.linearIsometryEquiv.trans
        (P.native n b.val).frame.linearIsometryEquiv.symm}.Finite := by
  classical
  obtain ⟨F⟩ := power_factorisation S
  obtain ⟨N, t, hcover, hN⟩ := header_finiteness_step15_tail_cover P p
  have hfin : ∀ n, Finite (P.Incident p n) := fun n => ((P.incidentForest p).1 n).1
  have hpref : (⋃ n : Fin N, Set.range (fun ab : P.Incident p n.val × P.Incident p n.val =>
      (P.native n.val ab.1.val).frame.linearIsometryEquiv.trans
        (P.native n.val ab.2.val).frame.linearIsometryEquiv.symm)).Finite := by
    refine Set.finite_iUnion fun n => ?_
    haveI := hfin n.val
    exact Set.finite_range _
  have hunique : ∀ (a : P.Incident p N) m (b : P.Incident p (N + m + 1)),
      P.IncidentChild p (N + m) ((t a).node m) b → b = (t a).node (m + 1) :=
    fun a m b hb => ExistsUnique.unique (hN (N + m) (by omega) ((t a).node m)) hb ((t a).step m)
  have hlisted : ∀ a : P.Incident p N,
      (P.native N ((t a).node 0).val).Lists 0 ((S.σ ^ N) p) :=
    fun a => P.incident_commonListed p hp N ((t a).node 0)
  have htail : (⋃ ab : P.Incident p N × P.Incident p N, Set.range (fun m =>
      (P.native (N + m) ((t ab.1).node m).val).frame.linearIsometryEquiv.trans
        (P.native (N + m) ((t ab.2).node m).val).frame.linearIsometryEquiv.symm)).Finite := by
    haveI := hfin N
    exact Set.finite_iUnion fun ab =>
      positioned_stars_finite_step1_tail_rotations P F p N (t ab.2) (t ab.1)
        (hunique ab.2) (hlisted ab.2) (hunique ab.1) (hlisted ab.1)
  apply (hpref.union htail).subset
  rintro L ⟨n, a, b, rfl⟩
  rcases lt_or_ge n N with hn | hn
  · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨n, hn⟩, ⟨(a, b), rfl⟩⟩)
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    obtain ⟨a₀, rfl⟩ := hcover m a
    obtain ⟨b₀, rfl⟩ := hcover m b
    exact Or.inr (Set.mem_iUnion.mpr ⟨(a₀, b₀), ⟨m, rfl⟩⟩)

/-- Step 3 of the V4 proof of `positioned_stars_finite` (V4 1.18): "Translations are
fixed because every `t ∈ I_n` has its named vertex at the common point". A relative
frame is determined by its finitely many linear parts and by the two prototype
vertex points sent to each other. -/
private theorem positioned_stars_finite_step3_frames [Nonempty S.ι] (p : E d)
    (hp : P.CommonListed p) :
    {g : Iso d | ∃ (n : ℕ) (a b : P.Incident p n),
      g = (P.native n a.val).frame.trans (P.native n b.val).frame.symm}.Finite := by
  classical
  have hsing : ∀ (A : S.ι) (v : Cell d), v ∈ (S.cx A).vertices → v.carrier.Subsingleton := by
    intro A v hv
    have hvdim : v.dim = 0 := (Finset.mem_filter.mp hv).2
    have hbot : cellDirection v.carrier = ⊥ :=
      Submodule.finrank_eq_zero.mp (v.flat.dimension.trans hvdim)
    apply (vectorSpan_eq_bot_iff_subsingleton ℝ).mp
    simpa only [cellDirection, direction_affineSpan] using hbot
  let Pts : Set (E d) := ⋃ A : S.ι, ⋃ v ∈ (S.cx A).vertices, v.carrier
  have hPts : Pts.Finite := Set.finite_iUnion fun A =>
    (S.cx A).vertices.finite_toSet.biUnion fun v hv => (hsing A v hv).finite
  have hL := positioned_stars_finite_step2_rotations P p hp
  have hT := (hL.prod (hPts.prod hPts)).image
    (fun z : Ortho d × E d × E d => z.2.2 - z.1 z.2.1)
  have hinj : Function.Injective (fun g : Iso d => (g.linearIsometryEquiv, g 0)) := by
    intro g h hgh
    simp only [Prod.mk.injEq] at hgh
    ext z
    have hg := g.map_vsub z 0
    have hh := h.map_vsub z 0
    simp only [vsub_eq_sub, sub_zero] at hg hh
    have h1 : g z = g.linearIsometryEquiv z + g 0 := by rw [hg]; abel
    have h2 : h z = h.linearIsometryEquiv z + h 0 := by rw [hh]; abel
    rw [h1, h2, hgh.1, hgh.2]
  refine Set.Finite.of_finite_image ((hL.prod hT).subset ?_) hinj.injOn
  rintro _ ⟨g, ⟨n, a, b, rfl⟩, rfl⟩
  obtain ⟨v, hv, hpv⟩ := P.incident_commonListed p hp n a
  obtain ⟨w, hw, hpw⟩ := P.incident_commonListed p hp n b
  rw [header_finiteness_step11_cell_zero] at hpv hpw
  obtain ⟨x, hx, hxp⟩ := hpv
  obtain ⟨y, hy, hyp⟩ := hpw
  have hlin : ((P.native n a.val).frame.trans (P.native n b.val).frame.symm).linearIsometryEquiv =
      (P.native n a.val).frame.linearIsometryEquiv.trans
        (P.native n b.val).frame.linearIsometryEquiv.symm := rfl
  have hgx : ((P.native n a.val).frame.trans (P.native n b.val).frame.symm) x = y := by
    simp only [AffineIsometryEquiv.coe_trans, Function.comp_apply, hxp, ← hyp,
      AffineIsometryEquiv.symm_apply_apply]
  have hvs := ((P.native n a.val).frame.trans (P.native n b.val).frame.symm).map_vsub x 0
  simp only [vsub_eq_sub, sub_zero] at hvs
  refine ⟨⟨n, a, b, hlin⟩, ⟨((P.native n a.val).frame.linearIsometryEquiv.trans
        (P.native n b.val).frame.linearIsometryEquiv.symm, x, y),
      ⟨⟨n, a, b, rfl⟩, Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion₂.mpr ⟨v, hv, hx⟩⟩,
        Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion₂.mpr ⟨w, hw, hy⟩⟩⟩, ?_⟩⟩
  change y - ((P.native n a.val).frame.trans (P.native n b.val).frame.symm).linearIsometryEquiv x =
    ((P.native n a.val).frame.trans (P.native n b.val).frame.symm) 0
  rw [hvs, hgx]
  abel

/-- P13, V4 1.18: finitely many full positioned stars, with an arbitrary finite
label alphabet. This includes the unlabelled case by taking `Y = Unit`. -/
theorem positioned_stars_finite (Y : Type) [Finite Y] (p : E d)
    (hp : P.CommonListed p) : (P.positionedStars Y p).Finite := by
  classical
  cases isEmpty_or_nonempty S.ι with
  | inl h =>
    letI := h
    refine Set.finite_empty.subset ?_
    rintro s ⟨n, anchor, label, rfl⟩
    exact isEmptyElim anchor.val.1.val.ty
  | inr h =>
    letI := h
    have hFr := positioned_stars_finite_step3_frames P p hp
    have hVs : (⋃ A : S.ι, ((S.cx A).vertices : Set (Cell d))).Finite :=
      Set.finite_iUnion fun A => (S.cx A).vertices.finite_toSet
    have hU := (((Set.finite_univ : (Set.univ : Set S.ι).Finite).prod hFr).prod
      (hVs.prod (Set.finite_univ : (Set.univ : Set Y).Finite))).image
      (fun z : (S.ι × Iso d) × Cell d × Y =>
        ((⟨z.1.1, z.1.2⟩ : FramedNode S), z.2.1, z.2.2))
    apply hU.finite_subsets.subset
    rintro s ⟨n, anchor, label, rfl⟩ z ⟨a, v, hv, -, rfl⟩
    exact ⟨(((P.native n a.val).ty,
        (P.native n a.val).frame.trans (P.native n anchor.val).frame.symm), v, label a),
      ⟨⟨trivial, n, a, anchor, rfl⟩, Set.mem_iUnion.mpr ⟨_, hv⟩, trivial⟩, rfl⟩

open private tangentCone_polyhedral_step2_halfspace_presentation
  tangentCone_polyhedral_step3_local_cone tangentCone_polyhedral_step5_radial_germ
  from Enforce.Geometry.Polyhedral in
/-- Step 1 of the V4 proof of `uniform_cone_radius_step1_catalogue` (V4 1.19):
"For a prototile A and a vertex v there is ρ(A,v)>0 with
A∩B(v,ρ)=(v+T_vA)∩B(v,ρ)". A polyhedron agrees near any point with its
radial tangent cone placed at that point. -/
private lemma uniform_cone_radius_step1_catalogue_step1_local_cone
    {k : ℕ} {K : Set (E k)} (hK : Polyhedron K) (v : E k) :
    ∃ ρ : ℝ, 0 < ρ ∧
      K ∩ ball v ρ = ((fun x => v + x) '' tangentCone K v) ∩ ball v ρ := by
  obtain ⟨s, hs⟩ := tangentCone_polyhedral_step2_halfspace_presentation hK
  obtain ⟨C, hC, hloc⟩ := tangentCone_polyhedral_step3_local_cone s v
  rw [← hs] at hloc
  have ht := tangentCone_polyhedral_step5_radial_germ v hC hloc
  obtain ⟨ρ, hρ, hnear⟩ := Metric.eventually_nhds_iff.mp hloc
  refine ⟨ρ, hρ, ?_⟩
  have himage (x : E k) :
      x ∈ (fun u => v + u) '' tangentCone K v ↔ x - v ∈ C := by
    rw [ht]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa only [add_sub_cancel_left] using hu
    · intro hx
      exact ⟨x - v, hx, add_sub_cancel _ _⟩
  ext x
  by_cases hx : x ∈ ball v ρ
  · simpa only [Set.mem_inter_iff, himage, hx, and_true] using
      (hnear (Metric.mem_ball.mp hx))
  · simp only [Set.mem_inter_iff, hx, and_false]

open scoped Topology in
/-- Step 2 of the V4 proof of `uniform_cone_radius_step1_catalogue` (V4 1.19):
"take r₀ the minimum over the finite catalogue". A finite family of positive
radii has a common positive lower bound, also when the family is empty. -/
private lemma uniform_cone_radius_step1_catalogue_step2_finite_min
    {J : Type*} [Finite J] (ρ : J → ℝ) (hρ : ∀ j, 0 < ρ j) :
    ∃ r : ℝ, 0 < r ∧ ∀ j, r < ρ j := by
  have he : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ), ∀ j, r < ρ j :=
    Filter.eventually_all.mpr (fun j => eventually_lt_nhds (hρ j))
  obtain ⟨δ, hδ, hall⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ / 2, by positivity, ?_⟩
  apply hall
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < δ / 2)]
  linarith

/-- Step 3 of the V4 proof of `uniform_cone_radius_step1_catalogue` (V4 1.19):
"take r₀ the minimum over the finite catalogue". Listed vertices are single
points, so finitely many pairs of a prototile and a listed vertex occur, and
the radius `ρ(A,v)` of Step 1 is shrunk to a common one. -/
private lemma uniform_cone_radius_step1_catalogue_step3_catalogue
    {k : ℕ} [Fact (2 ≤ k)] (T : SubstSystem k) :
    ∃ r : ℝ, 0 < r ∧ ∀ (A : T.ι) (e : Cell k), e ∈ (T.cx A).vertices →
      ∀ v ∈ e.carrier,
        (T.proto A).carrier ∩ ball v r =
          ((fun x => v + x) '' tangentCone (T.proto A).carrier v) ∩ ball v r := by
  classical
  have hsing : ∀ (A : T.ι) (e : Cell k),
      e ∈ (T.cx A).vertices → e.carrier.Subsingleton := by
    intro A e he
    have hd : e.dim = 0 := (Finset.mem_filter.mp he).2
    have hb : cellDirection e.carrier = ⊥ :=
      Submodule.finrank_eq_zero.mp (e.flat.dimension.trans hd)
    apply (vectorSpan_eq_bot_iff_subsingleton ℝ).mp
    simpa only [cellDirection, direction_affineSpan] using hb
  let Pts : Set (E k) := ⋃ A : T.ι, ⋃ e ∈ (T.cx A).vertices, e.carrier
  have hf : Pts.Finite := Set.finite_iUnion fun A =>
    (T.cx A).vertices.finite_toSet.biUnion fun e he => (hsing A e he).finite
  letI : Fintype Pts := hf.fintype
  have hex (j : T.ι × Pts) :=
    uniform_cone_radius_step1_catalogue_step1_local_cone
      (T.proto j.1).polyhedral j.2.val
  choose ρ hρ hc using hex
  obtain ⟨r, hr, hb⟩ :=
    uniform_cone_radius_step1_catalogue_step2_finite_min ρ hρ
  refine ⟨r, hr, ?_⟩
  intro A e he v hv
  have hvPts : v ∈ Pts :=
    Set.mem_iUnion.mpr ⟨A, Set.mem_iUnion₂.mpr ⟨e, he, hv⟩⟩
  let j : T.ι × Pts := ⟨A, ⟨v, hvPts⟩⟩
  have hj : (T.proto A).carrier ∩ ball v (ρ j) =
      ((fun x => v + x) '' tangentCone (T.proto A).carrier v) ∩ ball v (ρ j) := hc j
  ext x
  by_cases hx : x ∈ ball v r
  · have hlarge : x ∈ ball v (ρ j) := ball_subset_ball (hb j).le hx
    have hh := Set.ext_iff.mp hj x
    simpa only [Set.mem_inter_iff, hx, hlarge, and_true] using hh
  · simp only [Set.mem_inter_iff, hx, and_false]

/-- Step 4 of the V4 proof of `uniform_cone_radius_step1_catalogue` (V4 1.19):
"Every t ∈ I_n is a placed prototile"; the cone equality on a ball is
invariant under an isometric affine placement, with the same radius. -/
private lemma uniform_cone_radius_step1_catalogue_step4_placed
    {k : ℕ} {K : Set (E k)} {v : E k} {r : ℝ}
    (h : K ∩ ball v r = ((fun x => v + x) '' tangentCone K v) ∩ ball v r)
    (g : E k ≃ᵃ[ℝ] E k) (hg : Isometry g) :
    (g '' K) ∩ ball (g v) r =
      ((fun x => g v + x) '' tangentCone (g '' K) (g v)) ∩ ball (g v) r := by
  have h1 : tangentCone (g '' K) (g v) = g.linear '' tangentCone K v := by
    ext u
    simp only [tangentCone, mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨ε, hε, hu⟩
      refine ⟨g.linear.symm u, ⟨ε, hε, ?_⟩, g.linear.apply_symm_apply u⟩
      intro t ht htε
      have h1 := hu t ht htε
      rcases h1 with ⟨y, hy, hy2⟩
      have hy3 : y = v + t • g.linear.symm u := by
        apply g.injective
        rw [hy2]
        have hmap (y u : E k) (t : ℝ) : g (y + t • u) = g y + t • g.linear u := by
          simpa only [vadd_eq_add, add_comm, map_smul] using g.map_vadd y (t • u)
        rw [hmap v (g.linear.symm u) t, g.linear.apply_symm_apply u]
      rwa [hy3] at hy
    · rintro ⟨u', ⟨ε, hε, hu⟩, rfl⟩
      refine ⟨ε, hε, ?_⟩
      intro t ht htε
      have h1 := hu t ht htε
      use v + t • u'
      refine ⟨h1, ?_⟩
      have hmap (y u : E k) (t : ℝ) : g (y + t • u) = g y + t • g.linear u := by
        simpa only [vadd_eq_add, add_comm, map_smul] using g.map_vadd y (t • u)
      exact hmap v u' t
  rw [h1]
  ext x
  simp only [mem_inter_iff, mem_image, mem_ball]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hdist⟩
    have hdist2 : dist y v < r := by
      rwa [← hg.dist_eq y v]
    have hy2 : y ∈ K ∩ ball v r := ⟨hy, hdist2⟩
    rw [h] at hy2
    rcases hy2.1 with ⟨z, hz, hz2⟩
    refine ⟨⟨g.linear z, ⟨z, hz, rfl⟩, ?_⟩, hdist⟩
    have hmap (y u : E k) : g (y + u) = g y + g.linear u := by
      simpa only [vadd_eq_add, add_comm] using g.map_vadd y u
    rw [← hmap, ← hz2]
  · rintro ⟨⟨y, ⟨z, hz, rfl⟩, rfl⟩, hdist⟩
    have hmap (y u : E k) : g (y + u) = g y + g.linear u := by
      simpa only [vadd_eq_add, add_comm] using g.map_vadd y u
    have hz3 : g v + g.linear z = g (v + z) := (hmap v z).symm
    have hdist2 : dist (v + z) v < r := by
      rw [← hg.dist_eq (v + z) v]
      rw [← hz3]
      exact hdist
    have hz4 : v + z ∈ K ∩ ball v r := by
      rw [h]
      exact ⟨⟨z, hz, rfl⟩, hdist2⟩
    refine ⟨⟨v + z, hz4.1, hz3.symm⟩, hdist⟩

/-- Step 1 of the V4 proof of `uniform_cone_radius` (V4 1.19):
"take r₀ the minimum over the finite catalogue";
isometric placement preserves the radius. -/
private theorem uniform_cone_radius_step1_catalogue
    {k : ℕ} [hk : Fact (2 ≤ k)] (T : SubstSystem k) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (t : FramedNode T) (q : E k), t.Lists 0 q →
        t.carrier 0 ∩ ball q r =
          ((fun v => q + v) '' tangentCone (t.carrier 0) q)
            ∩ ball q r := by
  obtain ⟨r, hr, hmin⟩ := uniform_cone_radius_step1_catalogue_step3_catalogue T
  refine ⟨r, hr, fun t q hlists => ?_⟩
  rcases hlists with ⟨e, he, hq⟩
  have hc : t.carrier 0 = t.prototypeFrame 0 '' (T.proto t.ty).carrier := by
    simp [FramedNode.carrier, FramedNode.prototypeFrame, placedSet, SubstSystem.supertile]
  have hce : t.cell 0 e = t.prototypeFrame 0 '' e.carrier := rfl
  rw [hce] at hq
  rcases hq with ⟨y, hy, hy_eq⟩
  have h_base := hmin t.ty e he _ hy
  have h_iso : Isometry (t.prototypeFrame 0) := by
    have : t.prototypeFrame 0 = (T.σ ^ 0).toAffineEquiv.trans t.frame.toAffineEquiv := rfl
    rw [this, pow_zero]
    exact t.frame.isometry
  have h_trans :=
    uniform_cone_radius_step1_catalogue_step4_placed h_base (t.prototypeFrame 0) h_iso
  rw [hy_eq] at h_trans
  rwa [hc]

/-- Step 2 of the V4 proof of `uniform_cone_radius` (V4 1.19):
"its tangent cone ... is σⁿG = ⋃ T ... over the descendants";
nonincident descendants contribute no germ. -/
private theorem uniform_cone_radius_step2_union
    {k : ℕ} [hk : Fact (2 ≤ k)] {T : SubstSystem k}
    (R : CompatiblePatch T)
    (q : E k) (Q : Finset (FramedNode T))
    (hQ : Q ⊆ R.tiles) (n : ℕ) :
    (⋃ a : R.Incident q n, ⋃ (_ : a.val.1.val ∈ Q),
      tangentCone ((R.native n a.val).carrier 0) ((T.σ ^ n) q)) =
        (T.σ ^ n) '' tangentCone (⋃ t ∈ Q, t.carrier 0) q := by
  sorry

/-- P14, V4 1.19: uniform native-scale cone radius and the union formula for
any selected collection of original tiles whose cones form the chosen cone.
A single positive radius works at every depth and for every selected subpatch. -/
theorem uniform_cone_radius (p : E d) (hp : P.CommonListed p) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      (∀ (n : ℕ) (a : P.Incident p n),
        (P.native n a.val).carrier 0 ∩ ball ((S.σ ^ n) p) r₀ =
          ((fun v => (S.σ ^ n) p + v) ''
            tangentCone ((P.native n a.val).carrier 0) ((S.σ ^ n) p)) ∩
              ball ((S.σ ^ n) p) r₀) ∧
      ∀ Q : Finset (FramedNode S), Q ⊆ P.tiles → ∀ n : ℕ,
        (⋃ a : P.Incident p n, ⋃ (_ : a.val.1.val ∈ Q),
          (P.native n a.val).carrier 0) ∩ ball ((S.σ ^ n) p) r₀ =
        ((fun v => (S.σ ^ n) p + v) ''
          ((S.σ ^ n) '' tangentCone (⋃ t ∈ Q, t.carrier 0) p)) ∩
            ball ((S.σ ^ n) p) r₀ := by
  classical
  obtain ⟨r, hr, hcat⟩ :=
    uniform_cone_radius_step1_catalogue (k := d) S
  have hlocal : ∀ (n : ℕ) (a : P.Incident p n),
      (P.native n a.val).carrier 0 ∩ ball ((S.σ ^ n) p) r =
        ((fun v => (S.σ ^ n) p + v) ''
          tangentCone ((P.native n a.val).carrier 0) ((S.σ ^ n) p)) ∩
            ball ((S.σ ^ n) p) r := by
    intro n a
    exact hcat _ _ (P.incident_commonListed p hp n a)
  refine ⟨r, hr, hlocal, ?_⟩
  intro Q hQ n
  rw [← uniform_cone_radius_step2_union (k := d) P p Q hQ n]
  simp_rw [Set.image_iUnion, Set.iUnion_inter, hlocal]

end CompatiblePatch

/-- P11, V4 1.16(b): the cone language is closed under arbitrary finite unions. -/
theorem HPiCone_finite_union {α : Type} [Finite α] (K : α → Set (E d))
    (hK : ∀ a, HPiCone S.hPi (K a)) : HPiCone S.hPi (⋃ a, K a) := by
  classical
  cases nonempty_fintype α
  choose s_f s_eq s_prop using hK
  let big_s := Finset.biUnion (Finset.univ : Finset α) s_f
  use big_s
  constructor
  · ext x
    simp only [big_s, Set.mem_iUnion, Finset.mem_biUnion, Set.mem_iInter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨a, ha⟩
      rw [s_eq a] at ha
      simp only [Set.mem_iUnion, Set.mem_iInter] at ha
      rcases ha with ⟨p, hp1, hp2⟩
      exact ⟨p, ⟨a, hp1⟩, hp2⟩
    · intro ⟨p, ⟨a, hp1⟩, hp2⟩
      use a
      rw [s_eq a]
      simp only [Set.mem_iUnion, Set.mem_iInter]
      exact ⟨p, hp1, hp2⟩
  · intro p hp C hC
    simp only [big_s, Finset.mem_biUnion, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨a, ha⟩
    exact s_prop a p ha C hC


/-- P11, V4 1.16(b): the cone language is closed under arbitrary finite intersections. -/
theorem HPiCone_finite_inter {α : Type} [Finite α] (K : α → Set (E d))
    (hK : ∀ a, HPiCone S.hPi (K a)) : HPiCone S.hPi (⋂ a, K a) := by
  classical
  cases nonempty_fintype α
  choose s_f s_eq s_prop using hK
  let big_s := Fintype.piFinset s_f
  use big_s.image (fun g => Finset.biUnion Finset.univ (fun a => g a))
  constructor
  · ext x
    simp only [Set.mem_iInter, Set.mem_iUnion, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and, exists_prop, exists_exists_and_eq_and]
    constructor
    · intro hx
      have hx' : ∀ a, ∃ p ∈ s_f a, ∀ C ∈ p, x ∈ C := by
        intro a
        have h1 := hx a
        rw [s_eq a] at h1
        simp only [Set.mem_iUnion, Set.mem_iInter] at h1
        rcases h1 with ⟨p, hp1, hp2⟩
        exact ⟨p, hp1, hp2⟩
      choose g hg hg_prop using hx'
      use g
      constructor
      · rw [Fintype.mem_piFinset]
        exact hg
      · intro C hC
        rcases hC with ⟨a, ha⟩
        exact hg_prop a C ha
    · intro ⟨g, hg, hg_prop⟩ a
      rw [s_eq a]
      simp only [Set.mem_iUnion, Set.mem_iInter]
      use g a
      rw [Fintype.mem_piFinset] at hg
      exact ⟨hg a, fun C hC => hg_prop C ⟨a, hC⟩⟩
  · intro p hp C hC
    simp only [Finset.mem_image] at hp
    rcases hp with ⟨g, hg, rfl⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hC
    rcases hC with ⟨a, ha⟩
    rw [Fintype.mem_piFinset] at hg
    exact s_prop a (g a) (hg a) C ha

private lemma tangentCone_union_isHPiCone_step1_union_cone_step0_tangent_mono {K L : Set (E d)}
    (h : K ⊆ L) (p : E d) : tangentCone K p ⊆ tangentCone L p := by
  rintro v ⟨ε, hε, hv⟩
  exact ⟨ε, hε, fun t ht htε => h (hv t ht htε)⟩

open scoped Topology in
private lemma tangentCone_union_isHPiCone_step1_union_cone_step1_convex_union {ι : Type*} [Finite ι]
    (K : ι → Set (E d)) (hclosed : ∀ i, IsClosed (K i)) (hconv : ∀ i, Convex ℝ (K i))
    (p : E d) : tangentCone (⋃ i, K i) p = ⋃ i, tangentCone (K i) p := by
  classical
  ext v
  constructor
  · rintro ⟨ε, hε, hv⟩
    have hgood : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, p ∉ K i → p + t • v ∉ K i := by
      rw [Filter.eventually_all]
      intro i
      by_cases hi : p ∈ K i
      · exact Filter.Eventually.of_forall (fun _ h => (h hi).elim)
      · have hcont : Continuous (fun t : ℝ => p + t • v) := by fun_prop
        have hnbd : (K i)ᶜ ∈ 𝓝 p := (hclosed i).isOpen_compl.mem_nhds hi
        have hlim : Filter.Tendsto (fun t : ℝ => p + t • v) (𝓝 0) (𝓝 p) := by
          simpa using (hcont.continuousAt (x := 0)).tendsto
        have h := hlim.eventually hnbd
        exact h.mono (fun t ht _ => ht)
    have hgood' : ∀ᶠ t : ℝ in 𝓝[>] 0,
        0 < t ∧ t < ε ∧ ∀ i, p ∉ K i → p + t • v ∉ K i := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds,
        hgood.filter_mono nhdsWithin_le_nhds] with t ht htε hg
      exact ⟨ht, htε, hg⟩
    obtain ⟨t, ht, htε, hg⟩ := hgood'.exists
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hv t ht htε)
    have hp : p ∈ K i := by by_contra h; exact hg i h hi
    apply Set.mem_iUnion.mpr
    refine ⟨i, t, ht, ?_⟩
    intro u hu hut
    have hfrac : u / t ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_of_lt (div_pos hu ht), (div_le_one ht).mpr hut.le⟩
    have hc := (hconv i).add_smul_mem hp hi hfrac
    simpa only [smul_smul, div_mul_cancel₀ u ht.ne'] using hc
  · rintro hv
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hv
    exact tangentCone_union_isHPiCone_step1_union_cone_step0_tangent_mono (Set.subset_iUnion K i) p hi

private lemma tangentCone_union_isHPiCone_step1_union_cone_step2_polyhedral_union {ι : Type*} [Finite ι]
    (K : ι → Set (E d)) (hK : ∀ i, Polyhedron (K i)) (p : E d) :
    tangentCone (⋃ i, K i) p = ⋃ i, tangentCone (K i) p := by
  classical
  choose s hs using hK
  let J := Σ i : ι, {t // t ∈ s i}
  let C : J → Set (E d) := fun a => convexHull ℝ (a.2.val : Set (E d))
  have hU : (⋃ i, K i) = ⋃ a : J, C a := by
    simp only [hs, C, J, Set.iUnion_sigma, Set.iUnion_subtype]
  rw [hU, tangentCone_union_isHPiCone_step1_union_cone_step1_convex_union C
    (fun a => a.2.val.finite_toSet.isClosed_convexHull) (fun _ => convex_convexHull _ _) p]
  ext v
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, t, ht⟩, hv⟩
    refine ⟨i, tangentCone_union_isHPiCone_step1_union_cone_step0_tangent_mono ?_ p hv⟩
    rw [hs i]
    exact Set.subset_iUnion_of_subset t (Set.subset_iUnion_of_subset ht Set.Subset.rfl)
  · rintro ⟨i, hv⟩
    have hKi : K i = ⋃ t : {t // t ∈ s i}, convexHull ℝ (t.val : Set (E d)) := by
      simp only [hs i, Set.iUnion_subtype]
    have h_hv : v ∈ tangentCone (K i) p := hv
    rw [hKi, tangentCone_union_isHPiCone_step1_union_cone_step1_convex_union] at h_hv
    · obtain ⟨⟨t, ht⟩, hv'⟩ := Set.mem_iUnion.mp h_hv
      exact ⟨⟨i, t, ht⟩, hv'⟩
    · exact fun (t : {t // t ∈ s i}) => t.val.finite_toSet.isClosed_convexHull
    · exact fun _ => convex_convexHull _ _

private lemma tangentCone_union_isHPiCone_step1_union_cone_step3_polyhedron_image (e : E d ≃ᵃ[ℝ] E d)
    {K : Set (E d)} (hK : Polyhedron K) : Polyhedron (e '' K) := by
  classical
  obtain ⟨s, rfl⟩ := hK
  refine ⟨s.image (fun t => t.image e), ?_⟩
  simp only [Set.image_iUnion]
  ext x
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, hx⟩
    refine ⟨t.image e, ⟨t, ht, rfl⟩, ?_⟩
    rw [Finset.coe_image]
    exact (AffineMap.image_convexHull e.toAffineMap (t : Set (E d))) ▸ hx
  · rintro ⟨_, ⟨t, ht, rfl⟩, hx⟩
    refine ⟨t, ht, ?_⟩
    rw [Finset.coe_image] at hx
    exact (AffineMap.image_convexHull e.toAffineMap (t : Set (E d))).symm ▸ hx

/-- Step 1 of the V4 proof of `tangentCone_union_isHPiCone` (V4 1.16(b')): "finite unions of `HΠ`-cones (e.g. tangent cones of unions of such cells)".
The tangent cone of a finite union of sets is the finite union of their tangent cones. -/
private lemma tangentCone_union_isHPiCone_step1_union_cone
    (P : CompatiblePatch S)
    (Q : Finset (Σ t : {t // t ∈ P.tiles}, CellName S t.val.ty)) (p : E d) :
    tangentCone (⋃ q ∈ Q, q.1.val.cell 0 q.2.val) p =
    ⋃ q : Q, tangentCone (q.val.1.val.cell 0 q.val.2.val) p := by
  let J := Q
  let K (q : J) := q.1.1.val.cell 0 q.1.2.val
  have hK : ∀ q : J, Polyhedron (K q) := by
    intro q
    dsimp [K, FramedNode.cell, placedSet]
    exact tangentCone_union_isHPiCone_step1_union_cone_step3_polyhedron_image _ (q.1.2.val.flat.polyhedral)
  have h := tangentCone_union_isHPiCone_step1_union_cone_step2_polyhedral_union K hK p
  have h_eq : (⋃ q : Q, q.1.1.val.cell 0 q.1.2.val) = ⋃ q ∈ Q, q.1.val.cell 0 q.2.val := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨q, hx⟩
      exact ⟨q.val, q.property, hx⟩
    · rintro ⟨q, hq, hx⟩
      exact ⟨⟨q, hq⟩, hx⟩
  rw [h_eq] at h
  exact h

/-- P11, V4 1.16(b'): the tangent cone of a finite union of compatible listed
cells at a common listed anchor remains an `HΠ`-cone, in all dimensions. -/
theorem tangentCone_union_isHPiCone (P : CompatiblePatch S)
    (Q : Finset (Σ t : {t // t ∈ P.tiles}, CellName S t.val.ty)) (p : E d)
    (hlisted : ∀ q ∈ Q, q.1.val.Lists 0 p)
    (hcontains : ∀ q ∈ Q, p ∈ q.1.val.cell 0 q.2.val) :
    HPiCone S.hPi (tangentCone (⋃ q ∈ Q, q.1.val.cell 0 q.2.val) p) := by
  rw [tangentCone_union_isHPiCone_step1_union_cone P Q p]
  let K (q : Q) := tangentCone (q.val.1.val.cell 0 q.val.2.val) p
  have hK : ∀ (q : Q), HPiCone S.hPi (K q) := by
    intro q
    have h_rot := P.compatible q.val.1.val q.val.1.property
    have hp := hlisted q.val q.property
    have hC := hcontains q.val q.property
    exact tangentCone_isHPiCone q.val.1.val h_rot q.val.2 p hp hC
  have h_eq : (⋃ q : Q, K q) = ⋃ q : Q, K q := rfl
  exact HPiCone_finite_union K hK

open private tangentCone_polyhedral_step2_halfspace_presentation
  tangentCone_polyhedral_step3_local_cone tangentCone_polyhedral_step5_radial_germ
  from Enforce.Geometry.Polyhedral in
/-- Step 1 of the V4 proof of `uniform_prototype_cone_radius_step1_min_radius`
(V4 1.19): "For a prototile A and a vertex v there is ρ(A,v)>0".
In fact, local agreement with the radial tangent cone holds at every point. -/
private lemma uniform_prototype_cone_radius_step1_min_radius_step1_vertex
    (S : SubstSystem d) (A : S.ι) (v : E d) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (S.proto A).carrier ∩ ball v ρ =
        ((fun x => v + x) '' tangentCone (S.proto A).carrier v) ∩ ball v ρ := by
  obtain ⟨s, hs⟩ :=
    tangentCone_polyhedral_step2_halfspace_presentation (S.proto A).polyhedral
  obtain ⟨C, hC, hloc⟩ := tangentCone_polyhedral_step3_local_cone s v
  rw [← hs] at hloc
  have ht := tangentCone_polyhedral_step5_radial_germ v hC hloc
  obtain ⟨ρ, hρ, hnear⟩ := Metric.eventually_nhds_iff.mp hloc
  refine ⟨ρ, hρ, ?_⟩
  have himage (x : E d) :
      x ∈ (fun u => v + u) '' tangentCone (S.proto A).carrier v ↔ x - v ∈ C := by
    rw [ht]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa only [add_sub_cancel_left] using hu
    · intro hx
      exact ⟨x - v, hx, add_sub_cancel _ _⟩
  ext x
  by_cases hx : x ∈ ball v ρ
  · simpa only [Set.mem_inter_iff, himage, hx, and_true] using
      (hnear (Metric.mem_ball.mp hx))
  · simp only [Set.mem_inter_iff, hx, and_false]

open scoped Topology in
/-- Step 2 of the V4 proof of `uniform_prototype_cone_radius_step1_min_radius`
(V4 1.19): "take r₀ the minimum over the finite catalogue".
A finite family of positive radii has a common positive lower bound, even when empty. -/
private lemma uniform_prototype_cone_radius_step1_min_radius_step2_finite
    {J : Type*} [Finite J] (ρ : J → ℝ) (hρ : ∀ j, 0 < ρ j) :
    ∃ r : ℝ, 0 < r ∧ ∀ j, r < ρ j := by
  have he : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ), ∀ j, r < ρ j :=
    Filter.eventually_all.mpr (fun j => eventually_lt_nhds (hρ j))
  obtain ⟨δ, hδ, hall⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ / 2, by positivity, ?_⟩
  apply hall
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < δ / 2)]
  linarith

/-- Step 1 of the V4 proof of `uniform_prototype_cone_radius` (V4 1.19): For a prototile A
and a vertex v there is ρ>0 with exact cone intersection; take r₀ the minimum over the finite catalogue. -/
private lemma uniform_prototype_cone_radius_step1_min_radius (S : SubstSystem d) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (A : S.ι) (e : Cell d), e ∈ (S.cx A).vertices → ∀ v ∈ e.carrier,
      (S.proto A).carrier ∩ ball v r₀ =
        ((fun x => v + x) '' tangentCone (S.proto A).carrier v) ∩ ball v r₀ := by
  classical
  have hsing : ∀ (A : S.ι) (e : Cell d),
      e ∈ (S.cx A).vertices → e.carrier.Subsingleton := by
    intro A e he
    have hd : e.dim = 0 := (Finset.mem_filter.mp he).2
    have hb : cellDirection e.carrier = ⊥ :=
      Submodule.finrank_eq_zero.mp (e.flat.dimension.trans hd)
    apply (vectorSpan_eq_bot_iff_subsingleton ℝ).mp
    simpa only [cellDirection, direction_affineSpan] using hb
  let Pts : Set (E d) := ⋃ A : S.ι, ⋃ e ∈ (S.cx A).vertices, e.carrier
  have hf : Pts.Finite := Set.finite_iUnion fun A =>
    (S.cx A).vertices.finite_toSet.biUnion fun e he => (hsing A e he).finite
  letI : Fintype Pts := hf.fintype
  have hex (j : S.ι × Pts) :=
    uniform_prototype_cone_radius_step1_min_radius_step1_vertex S j.1 j.2.val
  choose ρ hρ hc using hex
  obtain ⟨r, hr, hb⟩ :=
    uniform_prototype_cone_radius_step1_min_radius_step2_finite ρ hρ
  refine ⟨r, hr, ?_⟩
  intro A e he v hv
  have hvPts : v ∈ Pts :=
    Set.mem_iUnion.mpr ⟨A, Set.mem_iUnion₂.mpr ⟨e, he, hv⟩⟩
  let j : S.ι × Pts := ⟨A, ⟨v, hvPts⟩⟩
  have hj : (S.proto A).carrier ∩ ball v (ρ j) =
      ((fun x => v + x) '' tangentCone (S.proto A).carrier v) ∩ ball v (ρ j) := hc j
  ext x
  by_cases hx : x ∈ ball v r
  · have hlarge : x ∈ ball v (ρ j) := ball_subset_ball (hb j).le hx
    have hh := Set.ext_iff.mp hj x
    simpa only [Set.mem_inter_iff, hx, hlarge, and_true] using hh
  · simp only [Set.mem_inter_iff, hx, and_false]

/-- Step 2 of the V4 proof of `uniform_prototype_cone_radius` (V4 1.19): the cone equality
is invariant under isometric placement. -/
private lemma uniform_prototype_cone_radius_step2_placed {K : Set (E d)} {v : E d} {r : ℝ}
    (h : K ∩ ball v r = ((fun x => v + x) '' tangentCone K v) ∩ ball v r) (g : E d ≃ᵃ[ℝ] E d)
    (hg : Isometry g) :
    (g '' K) ∩ ball (g v) r =
      ((fun x => g v + x) '' tangentCone (g '' K) (g v)) ∩ ball (g v) r := by
  have h1 : tangentCone (g '' K) (g v) = g.linear '' tangentCone K v := by
    ext u
    simp only [tangentCone, mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨ε, hε, hu⟩
      refine ⟨g.linear.symm u, ⟨ε, hε, ?_⟩, g.linear.apply_symm_apply u⟩
      intro t ht htε
      have h1 := hu t ht htε
      rcases h1 with ⟨y, hy, hy2⟩
      have hy3 : y = v + t • g.linear.symm u := by
        apply g.injective
        rw [hy2]
        have hmap (y u : E d) (t : ℝ) : g (y + t • u) = g y + t • g.linear u := by
          simpa only [vadd_eq_add, add_comm, map_smul] using g.map_vadd y (t • u)
        rw [hmap v (g.linear.symm u) t, g.linear.apply_symm_apply u]
      rwa [hy3] at hy
    · rintro ⟨u', ⟨ε, hε, hu⟩, rfl⟩
      refine ⟨ε, hε, ?_⟩
      intro t ht htε
      have h1 := hu t ht htε
      use v + t • u'
      refine ⟨h1, ?_⟩
      have hmap (y u : E d) (t : ℝ) : g (y + t • u) = g y + t • g.linear u := by
        simpa only [vadd_eq_add, add_comm, map_smul] using g.map_vadd y (t • u)
      exact hmap v u' t
  rw [h1]
  ext x
  simp only [mem_inter_iff, mem_image, mem_ball]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hdist⟩
    have hdist2 : dist y v < r := by
      rwa [← hg.dist_eq y v]
    have hy2 : y ∈ K ∩ ball v r := ⟨hy, hdist2⟩
    rw [h] at hy2
    rcases hy2.1 with ⟨z, hz, hz2⟩
    refine ⟨⟨g.linear z, ⟨z, hz, rfl⟩, ?_⟩, hdist⟩
    have hmap (y u : E d) : g (y + u) = g y + g.linear u := by
      simpa only [vadd_eq_add, add_comm] using g.map_vadd y u
    rw [← hmap, ← hz2]
  · rintro ⟨⟨y, ⟨z, hz, rfl⟩, rfl⟩, hdist⟩
    have hmap (y u : E d) : g (y + u) = g y + g.linear u := by
      simpa only [vadd_eq_add, add_comm] using g.map_vadd y u
    have hz3 : g v + g.linear z = g (v + z) := (hmap v z).symm
    have hdist2 : dist (v + z) v < r := by
      rw [← hg.dist_eq (v + z) v]
      rw [← hz3]
      exact hdist
    have hz4 : v + z ∈ K ∩ ball v r := by
      rw [h]
      exact ⟨⟨z, hz, rfl⟩, hdist2⟩
    refine ⟨⟨v + z, hz4.1, hz3.symm⟩, hdist⟩

/-- P14, V4 1.19: a single prototype-catalogue radius works for every placed
ground tile at every listed vertex, independently of patches and their depth.
An empty catalogue admits any positive radius. -/
theorem uniform_prototype_cone_radius (S : SubstSystem d) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (t : FramedNode S) (p : E d), t.Lists 0 p →
      t.carrier 0 ∩ ball p r₀ =
        ((fun v => p + v) '' tangentCone (t.carrier 0) p) ∩ ball p r₀ := by
  obtain ⟨r₀, hr₀, hmin⟩ := uniform_prototype_cone_radius_step1_min_radius S
  refine ⟨r₀, hr₀, fun t p hlists => ?_⟩
  rcases hlists with ⟨e, he, hp⟩
  have hc : t.carrier 0 = t.prototypeFrame 0 '' (S.proto t.ty).carrier := by
    simp [FramedNode.carrier, FramedNode.prototypeFrame, placedSet, SubstSystem.supertile]
  have hce : t.cell 0 e = t.prototypeFrame 0 '' e.carrier := rfl
  rw [hce] at hp
  rcases hp with ⟨y, hy, hy_eq⟩
  have h_base := hmin t.ty e he _ hy
  have h_iso : Isometry (t.prototypeFrame 0) := by
    have : t.prototypeFrame 0 = (S.σ ^ 0).toAffineEquiv.trans t.frame.toAffineEquiv := rfl
    rw [this, pow_zero]
    exact t.frame.isometry
  have h_trans := uniform_prototype_cone_radius_step2_placed h_base (t.prototypeFrame 0) h_iso
  rw [hy_eq] at h_trans
  rwa [hc]

namespace CompatiblePatch

variable (P : CompatiblePatch S)

/-- Step 1 of the V4 proof of `native_injective` (V4 1.14): "σⁿΠ consists of placed
prototiles with frames in H": the inflated frame of a compatible tile intertwines `σⁿ`
with the original frame. -/
private theorem native_injective_step1_inflated_frame (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (n : ℕ) (x : E d) :
    compatibleInflatedFrame t ht n ((S.σ ^ n) x) = (S.σ ^ n) (t.frame x) := by
  induction n with
  | zero =>
    have hc := (Classical.choose_spec (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ)
      t.frame.linearIsometryEquiv ht)).2
    have hy := congrArg (fun e : E d ≃ₗ[ℝ] E d => e x) hc
    simp only [linearConj, Nat.cast_zero, zpow_zero, neg_zero, one_mul, mul_one] at hy
    have hdec : t.frame x = t.frame.linearIsometryEquiv x + t.frame 0 := by
      have h := t.frame.map_vadd (0 : E d) x
      rw [vadd_eq_add, add_zero, vadd_eq_add] at h
      exact h
    show (Classical.choose (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ)
      t.frame.linearIsometryEquiv ht)) ((S.σ ^ 0) x) + (S.σ ^ 0) (t.frame 0) =
        (S.σ ^ 0) (t.frame x)
    rw [pow_zero]
    change (Classical.choose (S.rotGroup_conj_zpow ((0 : ℕ) : ℤ)
      t.frame.linearIsometryEquiv ht)) x + (t.frame 0) = t.frame x
    rw [hdec]
    exact congrArg (· + t.frame 0) hy
  | succ n ih =>
    rw [pow_succ']
    change compatibleInflatedFrame t ht (n + 1) (S.σ ((S.σ ^ n) x)) =
      S.σ ((S.σ ^ n) (t.frame x))
    rw [power_factorisation_aux_step11_inflated_frame_succ, ih]

/-- Step 2 of the V4 proof of `native_injective` (V4 1.14): "the native tiles of σⁿΠ":
every native tile at an address lies in the expansion `σⁿ t` of its base tile. -/
private theorem native_injective_step2_subset (P : CompatiblePatch S) (n : ℕ)
    (a : P.Address n) :
    (P.native n a).carrier 0 ⊆ (S.σ ^ n) '' (a.1.val.carrier 0) := by
  rintro x ⟨y, hy, rfl⟩
  have hy' : (S.nativeTile a.1.val.ty n a.2).frame y ∈ S.supertile n a.1.val.ty := by
    rw [← S.native_cover a.1.val.ty n]
    refine Set.mem_iUnion.mpr ⟨a.2, ?_⟩
    exact Set.mem_image_of_mem _ hy
  obtain ⟨z, hz, hzeq⟩ := hy'
  rw [power_factorisation_aux_step11_carrier_zero]
  refine ⟨a.1.val.frame z, ⟨z, hz, rfl⟩, ?_⟩
  change (S.σ ^ n) (a.1.val.frame z) = compatibleInflatedFrame a.1.val
    (P.compatible a.1.val a.1.property) n ((S.nativeTile a.1.val.ty n a.2).frame y)
  rw [← hzeq, native_injective_step1_inflated_frame]

/-- Step 3 of the V4 proof of `native_injective` (V4 1.14): "placed prototiles":
every framed ground tile has nonempty interior. -/
private theorem native_injective_step3_interior (N : FramedNode S) :
    (interior (N.carrier 0)).Nonempty := by
  rw [power_factorisation_aux_step11_carrier_zero]
  change (interior (N.frame.toHomeomorph '' (S.proto N.ty).carrier)).Nonempty
  rw [← N.frame.toHomeomorph.image_interior]
  exact (S.proto N.ty).interior_nonempty.image _

/-- P9, V4 1.14: the native subdivision has no repeated framed tile occurrences. -/
theorem native_injective (n : ℕ) : Function.Injective (P.native n) := by
  rintro ⟨t, v⟩ ⟨s, w⟩ hab
  by_cases hts : t = s
  · subst hts
    by_contra hvw
    have hne : v ≠ w := fun h => hvw (h ▸ rfl)
    have hN : S.nativeTile t.val.ty n v = S.nativeTile t.val.ty n w := by
      have hfr := congrArg FramedNode.frame hab
      have hty := congrArg FramedNode.ty hab
      refine FramedNode.ext hty ?_
      refine AffineIsometryEquiv.ext fun y => ?_
      have h1 := congrArg (fun φ : Iso d => φ y) hfr
      have h2 : compatibleInflatedFrame t.val (P.compatible t.val t.property) n
            ((S.nativeTile t.val.ty n v).frame y) =
          compatibleInflatedFrame t.val (P.compatible t.val t.property) n
            ((S.nativeTile t.val.ty n w).frame y) := h1
      exact congrArg (fun z : E d => z)
        ((compatibleInflatedFrame t.val (P.compatible t.val t.property) n).injective h2)
    have hd : Disjoint (interior ((S.nativeTile t.val.ty n v).carrier 0))
        (interior ((S.nativeTile t.val.ty n w).carrier 0)) := S.native_disjoint t.val.ty n hne
    rw [hN] at hd
    obtain ⟨y, hy⟩ := native_injective_step3_interior (S.nativeTile t.val.ty n w)
    exact Set.disjoint_left.mp hd hy hy
  · exfalso
    obtain ⟨x, hx⟩ := native_injective_step3_interior (P.native n ⟨t, v⟩)
    have hne : t.val ≠ s.val := fun h => hts (Subtype.ext h)
    have hd : Disjoint (interior (t.val.carrier 0)) (interior (s.val.carrier 0)) :=
      P.disjoint t.property s.property hne
    let h : E d ≃ₜ E d := (S.σ ^ n).toContinuousLinearEquiv.toHomeomorph
    have himg : ∀ C : Set (E d), (S.σ ^ n) '' C = h '' C := fun C => rfl
    have hxt : x ∈ interior ((S.σ ^ n) '' (t.val.carrier 0)) :=
      interior_mono (native_injective_step2_subset P n ⟨t, v⟩) hx
    have hxs : x ∈ interior ((S.σ ^ n) '' (s.val.carrier 0)) := by
      rw [hab] at hx
      exact interior_mono (native_injective_step2_subset P n ⟨s, w⟩) hx
    rw [himg, ← h.image_interior] at hxt
    rw [himg, ← h.image_interior] at hxs
    obtain ⟨y₁, hy₁, rfl⟩ := hxt
    obtain ⟨y₂, hy₂, hy⟩ := hxs
    have : y₂ = y₁ := h.injective hy
    subst this
    exact Set.disjoint_left.mp hd hy₁ hy₂

/-- P9, V4 1.14: all native tiles have disjoint interiors, with no side-to-side
hypothesis, and they cover exactly the ambient expansion of the original patch. -/
theorem native_subdivision (n : ℕ) :
    Pairwise (fun a b : P.Address n => Disjoint
      (interior ((P.native n a).carrier 0)) (interior ((P.native n b).carrier 0))) ∧
      (⋃ a : P.Address n, (P.native n a).carrier 0) =
        (S.σ ^ n) '' (⋃ t ∈ P.tiles, t.carrier 0) := by
  refine ⟨?_, Set.Subset.antisymm ?_ ?_⟩
  · simpa only [incidentForest_step1_carrier_zero, placedSet] using
      incidentForest_step1_native_disjoint P n
  · intro x hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    rw [incidentForest_step1_carrier_zero] at ha
    obtain ⟨y, hy, rfl⟩ := incidentForest_step1_native_subset P n a ha
    rw [← incidentForest_step1_carrier_zero] at hy
    exact Set.mem_image_of_mem _
      (Set.mem_iUnion.mpr ⟨a.1.val, Set.mem_iUnion.mpr ⟨a.1.property, hy⟩⟩)
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨t, hyt⟩ := Set.mem_iUnion.mp hy
    obtain ⟨ht, hytile⟩ := Set.mem_iUnion.mp hyt
    rw [incidentForest_step1_carrier_zero] at hytile
    obtain ⟨z, hz, rfl⟩ := hytile
    have hcov : (S.σ ^ n) z ∈
        ⋃ w : S.RoleWord t.ty n, (S.nativeTile t.ty n w).carrier 0 := by
      rw [S.native_cover]
      exact Set.mem_image_of_mem _ hz
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hcov
    rw [incidentForest_step1_carrier_zero] at hw
    obtain ⟨u, hu, hzu⟩ := hw
    refine Set.mem_iUnion.mpr ⟨⟨⟨t, ht⟩, w⟩, ?_⟩
    rw [incidentForest_step1_carrier_zero]
    refine ⟨u, hu, ?_⟩
    change compatibleInflatedFrame t (P.compatible t ht) n
      ((S.nativeTile t.ty n w).frame u) = (S.σ ^ n) (t.frame z)
    rw [hzu, incidentForest_step1_inflated_pow]

/-- Step 1 of the V4 proof of `incident_width_monotone` (V4 1.14):
"every element of I_n has at least one child in I_{n+1}" -/
private theorem incident_width_monotone_step1_child_exists
    (P : CompatiblePatch S) (p : E d) (n : ℕ) (a : P.Incident p n) :
    ∃ b : P.Incident p (n + 1), P.IncidentChild p n a b := by
  have hs_hp : (S.σ ^ (n + 1)) p ∈ S.σ '' (P.native n a.val).carrier 0 := by
    rw [pow_succ']
    exact Set.mem_image_of_mem _ a.property
  have hcov : S.σ '' (P.native n a.val).carrier 0 ⊆ ⋃ (i : S.I (P.native n a.val).ty), (P.native (n + 1) (power_factorisation_aux_step11_native_child P n a.val i).choose).carrier 0 := by
    rw [power_factorisation_aux_step11_carrier_zero]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := hy
    have h_child_cover : S.σ z ∈ ⋃ i, placedSet (S.child (P.native n a.val).ty i).frame (S.proto (S.child (P.native n a.val).ty i).ty).carrier := by
      rw [← S.children_cover (P.native n a.val).ty]
      exact Set.mem_image_of_mem _ hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h_child_cover
    obtain ⟨u, hu, hu_eq⟩ := hi
    rw [Set.mem_iUnion]
    use i
    let b := (power_factorisation_aux_step11_native_child P n a.val i).choose
    have hb := (power_factorisation_aux_step11_native_child P n a.val i).choose_spec
    rw [power_factorisation_aux_step11_carrier_zero]
    have hu2 : u ∈ (S.proto (P.native (n + 1) b).ty).carrier := by
      rw [hb.1]
      exact hu
    refine ⟨u, hu2, ?_⟩
    rw [hb.2 u, hu_eq]
    simp
  have h_child := hcov hs_hp
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h_child
  let b := (power_factorisation_aux_step11_native_child P n a.val i).choose
  use ⟨b, hi⟩
  change (P.native (n + 1) b).carrier 0 ⊆ S.σ '' (P.native n a.val).carrier 0
  have hb := (power_factorisation_aux_step11_native_child P n a.val i).choose_spec
  rw [power_factorisation_aux_step11_carrier_zero, power_factorisation_aux_step11_carrier_zero]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [hb.2 y]
  have hy2 : y ∈ (S.proto (S.child (P.native n a.val).ty i).ty).carrier := by
    rw [← hb.1]
    exact hy
  have h_child_cover2 : placedSet (S.child (P.native n a.val).ty i).frame (S.proto (S.child (P.native n a.val).ty i).ty).carrier ⊆ S.σ '' (S.proto (P.native n a.val).ty).carrier := by
    rw [S.children_cover (P.native n a.val).ty]
    exact Set.subset_iUnion (fun i => placedSet (S.child (P.native n a.val).ty i).frame (S.proto (S.child (P.native n a.val).ty i).ty).carrier) i
  have hy3 := h_child_cover2 ⟨y, hy2, rfl⟩
  obtain ⟨z, hz, hz_eq⟩ := hy3
  use (P.native n a.val).frame z
  constructor
  · exact ⟨z, hz, rfl⟩
  · rw [← hz_eq]
    simp

/-- P9, V4 1.14: the number of incident tiles never decreases with depth. -/
theorem incident_width_monotone (p : E d) (n : ℕ) :
    Nat.card (P.Incident p n) ≤ Nat.card (P.Incident p (n + 1)) := by
  by_cases h : IsEmpty (P.Incident p n)
  · have h0 : Nat.card (P.Incident p n) = 0 := Nat.card_eq_zero.mpr (Or.inl h)
    rw [h0]
    exact Nat.zero_le _
  · haveI : Nonempty (P.Incident p n) := not_isEmpty_iff.mp h
    let f : P.Incident p (n + 1) → P.Incident p n := fun b => P.incidentParent p n b
    have hsurj : Function.Surjective f := fun a =>
      let ⟨b, hb⟩ := incident_width_monotone_step1_child_exists P p n a
      ⟨b, ExistsUnique.unique (P.incident_parent_exists_unique p n b) (P.incidentParent_spec p n b) hb⟩
    exact Nat.card_le_card_of_surjective f hsurj

/-- P12, V4 1.17: every incident tile listing the anchor contributes its full
header, with the actual named vertex. This supplies witnesses to the header set. -/
theorem header_occurs (p : E d) {s : ℕ} (G : Fin s → Set (E d)) (n : ℕ)
    (a : P.Incident p n)
    (v : {e // e ∈ (S.cx (P.native n a.val).ty).vertices})
    (hv : (S.σ ^ n) p ∈ (P.native n a.val).cell 0 v.val) :
    (⟨(P.native n a.val).ty, v,
      fun j => (P.native n a.val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ n) '' G j)⟩ : Header S s) ∈ P.headers p G := by
  exact ⟨n, a, hv, rfl, fun _ => rfl⟩

end CompatiblePatch

end Enforce
