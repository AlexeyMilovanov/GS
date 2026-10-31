import Enforce.State.Rows
import Enforce.Rules

/-!
# Geometric clusters and the augmented alphabet

M2, V4 2.10, with the frame marker of V4 §2.4. Choices are explicit fields,
including all clearances and the common microball radius. No source is assumed
nonempty. Honest ranges supply the finite alphabets, even for an empty species.

DEVIATION: the optional state-ball encoding and the enclosing cluster balls are
chosen together here, since stage 3 records pre-pattern symbols without a state
ball. The state ball is fixed per prototype and carries the entire honest
pre-pattern symbol. The same symbol colours the remaining interior, as specified
in Construction 2.10. This retains all state and packet data.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

attribute [local instance] Classical.decEq

/-- M2, V4 2.10: the finite alphabet of actual pre-pattern symbols. -/
abbrev PrePatternSymbol (S : SubstSystem d) (P : Params S) :=
  {w // w ∈ honestPrePatterns S P}

/-- M2, V4 2.10: the finite alphabet of actual certificate blocks. -/
abbrev CertificateSymbol (S : SubstSystem d) (P : Params S) :=
  {D // D ∈ honestCerts S P}

/-- M2, V4 2.10: enumeration of the honest pre-pattern alphabet. -/
instance prePatternSymbolFintype (P : Params S) : Fintype (PrePatternSymbol S P) :=
  (prePatterns_finite S P).fintype

/-- M2, V4 2.10: enumeration of the honest certificate alphabet. -/
instance certificateSymbolFintype (P : Params S) : Fintype (CertificateSymbol S P) :=
  (certs_finite S P).fintype

/-- M2, V4 2.10: enumeration of the finite leaf alphabet from stage 3. -/
instance leafTypeFintype (P : Params S) : Fintype (LeafType P) := by
  letI := leafTypes_finite P
  exact Fintype.ofFinite _

/-- M2, V4 2.10: enumeration of all slots of a fixed leaf. -/
instance eventSlotFintype {P : Params S} (l : LeafType P) : Fintype (EventSlot l) := by
  letI := eventSlots_finite P l
  exact Fintype.ofFinite _

/-- M2, V4 2.10: enclosing regions, one CORE, one RO and one TRIG per slot. -/
inductive ClusterKind {P : Params S} (l : LeafType P)
  /-- M2, V4 2.10: certificate pinning. -/
  | core : ClusterKind l
  /-- M2, V4 2.10: template readout pinning. -/
  | readout : ClusterKind l
  /-- M2, V4 2.10: pinning the central tile of an event. -/
  | trigger : EventSlot l → ClusterKind l

/-- M2, V4 2.10: the enclosing-region index type is finite. -/
theorem clusterKinds_finite {P : Params S} (l : LeafType P) :
    Finite (ClusterKind l) := by
  let f : Option (Option (EventSlot l)) → ClusterKind l := fun x =>
    match x with
    | none => .core
    | some none => .readout
    | some (some j) => .trigger j
  have hf : Function.Surjective f := by
    intro y
    cases y
    · exact ⟨none, rfl⟩
    · exact ⟨some none, rfl⟩
    · exact ⟨some (some ‹_›), rfl⟩
  exact Finite.of_surjective f hf

/-- M2, V4 2.10: enumeration of enclosing-region kinds. -/
instance clusterKindFintype {P : Params S} (l : LeafType P) :
    Fintype (ClusterKind l) := by
  letI := clusterKinds_finite l
  exact Fintype.ofFinite _

/-- M2, V4 2.10: the genuine global choices of balls, anchors and small constants.
The fields give the printed order-of-choices inequalities. Additional containment
fields spell out their geometric consequences, rather than assuming rigidity.
DEVIATION: state balls are chosen here with the compiler balls, as explained above.
Existence is `clusterData_exists`; an actual source is not required. -/
structure ClusterData (S : SubstSystem d) (P : Params S) where
  /-- M2, V4 2.10: centre of the further small state ball for each prototype. -/
  stateCentre : S.ι → E d
  /-- M2, V4 2.10: state-ball radii, chosen before cluster regions. -/
  stateRadius : S.ι → ℝ
  /-- M2, V4 2.10: nondegenerate state balls. -/
  stateRadius_pos : ∀ A, 0 < stateRadius A
  /-- M2, V4 2.10: closed state balls are strictly inside their prototypes. -/
  state_inside : ∀ A, closedBall (stateCentre A) (stateRadius A) ⊆
    interior (S.proto A).carrier
  /-- M2, V4 2.10: state balls avoid all fixed frame-marker balls. -/
  state_marker_disjoint : ∀ A a, Disjoint
    (closedBall (stateCentre A) (stateRadius A))
    (closedBall ((P.marker A).centre a) (P.marker A).radius)
  /-- M2, V4 2.10: centres of closed enclosing balls. -/
  enclosingCentre : ∀ l : LeafType P, ClusterKind l → E d
  /-- M2, V4 2.10: radii of the enclosing balls. -/
  enclosingRadius : ∀ l : LeafType P, ClusterKind l → ℝ
  /-- M2, V4 2.10: every enclosing ball has positive radius. -/
  enclosingRadius_pos : ∀ l κ, 0 < enclosingRadius l κ
  /-- M2, V4 2.10: closed enclosing balls lie in the leaf interior. -/
  enclosing_inside : ∀ l κ, closedBall (enclosingCentre l κ) (enclosingRadius l κ) ⊆
    interior (S.proto l.prototype).carrier
  /-- M2, V4 2.10: different enclosing balls of one leaf are disjoint. -/
  enclosing_disjoint : ∀ l, Pairwise (fun κ η : ClusterKind l => Disjoint
    (closedBall (enclosingCentre l κ) (enclosingRadius l κ))
    (closedBall (enclosingCentre l η) (enclosingRadius l η)))
  /-- M2, V4 2.10: enclosing balls avoid the fixed labelled frame markers. -/
  enclosing_marker_disjoint : ∀ l κ a, Disjoint
    (closedBall (enclosingCentre l κ) (enclosingRadius l κ))
    (closedBall ((P.marker l.prototype).centre a) (P.marker l.prototype).radius)
  /-- M2, V4 2.10: enclosing balls avoid the state ball. -/
  enclosing_state_disjoint : ∀ l κ, Disjoint
    (closedBall (enclosingCentre l κ) (enclosingRadius l κ))
    (closedBall (stateCentre l.prototype) (stateRadius l.prototype))
  /-- M2, V4 2.10: cluster anchors, chosen before the clearance constant. -/
  anchor : ∀ l : LeafType P, ClusterKind l → E d
  /-- M2, V4 2.10: each anchor lies strictly inside its enclosing ball. -/
  anchor_inside : ∀ l κ, anchor l κ ∈ ball (enclosingCentre l κ) (enclosingRadius l κ)
  /-- M2, V4 2.10: uniform clearance constant. -/
  δ : ℝ
  /-- M2, V4 2.10: strictly positive clearance. -/
  δ_pos : 0 < δ
  /-- M2, V4 2.10: delta is less than half every anchor-to-boundary distance. -/
  anchor_boundary : ∀ l κ x, x ∈ frontier (S.proto l.prototype).carrier →
    δ < dist (anchor l κ) x / 2
  /-- M2, V4 2.10: delta is less than a quarter of inter-anchor distances. -/
  anchor_separation : ∀ l κ η, κ ≠ η → δ < dist (anchor l κ) (anchor l η) / 4
  /-- M2, V4 2.10: uniform upper bound on complete cluster diameters. -/
  ε : ℝ
  /-- M2, V4 2.10: positive diameter budget. -/
  ε_pos : 0 < ε
  /-- M2, V4 2.10: the printed epsilon/delta inequality. -/
  ε_lt : ε < δ / 4
  /-- M2, V4 2.10: all d+1 labelled microball centres. -/
  centre : ∀ l : LeafType P, ClusterKind l → Fin (d + 1) → E d
  /-- M2, V4 2.10: centres are chosen within epsilon/2 of their anchor. -/
  centre_near : ∀ l κ a, dist (centre l κ a) (anchor l κ) < ε / 2
  /-- M2, V4 2.10: each complete labelled cluster fixes a full affine frame. -/
  independent : ∀ l κ, AffineIndependent ℝ (centre l κ)
  /-- M2, V4 2.10: one common microball radius throughout the finite catalogue. -/
  ρ : ℝ
  /-- M2, V4 2.10: positive microball radius. -/
  ρ_pos : 0 < ρ
  /-- M2, V4 2.10: radius is chosen after epsilon. -/
  ρ_lt : ρ < ε / 4
  /-- M2, V4 2.10: closed microballs lie strictly inside the enclosing ball. -/
  micro_inside : ∀ l κ a, closedBall (centre l κ a) ρ ⊆
    ball (enclosingCentre l κ) (enclosingRadius l κ)
  /-- M2, V4 2.10: microballs in one cluster are pairwise disjoint. -/
  micro_disjoint : ∀ l κ, Pairwise (fun a b : Fin (d + 1) => Disjoint
    (closedBall (centre l κ a) ρ) (closedBall (centre l κ b) ρ))
  /-- M2, V4 2.10: diameter bound for the entire union, including microball radii. -/
  cluster_diameter : ∀ l κ, diam (⋃ a, closedBall (centre l κ a) ρ) < ε
  /-- M2, V4 2.10: the resulting centres have strict delta-clearance. -/
  centre_boundary : ∀ l κ a x, x ∈ frontier (S.proto l.prototype).carrier →
    δ < dist (centre l κ a) x
  /-- M2, V4 2.10: clearance stated also as a neighbourhood containment. -/
  centre_clearance : ∀ l κ a, closedBall (centre l κ a) δ ⊆
    interior (S.proto l.prototype).carrier

/-- Step 1 of the V4 proof of `clusterData_exists` (V4 2.10, with the frame marker of
V4 §2.4): "In int A choose pairwise disjoint closed balls, all disjoint from the
frame-marker balls". Since the finitely many closed marker balls lie in the open
interior and are pairwise at positive distance, the interior of each prototype
contains a closed ball of positive radius avoiding all marker balls. -/
private theorem clusterData_exists_step1_room (S : SubstSystem d) (P : Params S) (A : S.ι) :
    ∃ p : E d, ∃ r : ℝ, 0 < r ∧ closedBall p r ⊆ interior (S.proto A).carrier ∧
      ∀ a, Disjoint (closedBall p r)
        (closedBall ((P.marker A).centre a) (P.marker A).radius) := by
  classical
  set M := P.marker A with hM
  have hd : 0 < d := lt_of_lt_of_le two_pos (Fact.out : 2 ≤ d)
  let u : E d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)
  have hu : ‖u‖ = 1 := by simp [u]
  have hR := M.radius_pos
  let y : E d := M.centre 0 + M.radius • u
  have hy0 : y ∈ closedBall (M.centre 0) M.radius := by
    rw [mem_closedBall, dist_eq_norm]
    simp only [y]
    rw [add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_of_nonneg hR.le]
  let V : Set (E d) := interior (S.proto A).carrier ∩
    ⋂ a ∈ {a : Fin (d + 1) | a ≠ 0}, (closedBall (M.centre a) M.radius)ᶜ
  have hVo : IsOpen V := isOpen_interior.inter
    ((Set.toFinite _).isOpen_biInter fun a _ => isClosed_closedBall.isOpen_compl)
  have hyV : y ∈ V := by
    refine ⟨M.inside 0 hy0, Set.mem_iInter₂.2 fun a ha hya => ?_⟩
    exact Set.disjoint_left.1 (M.disjoint (Ne.symm ha)) hy0 hya
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hVo y hyV
  have hk : (0 : ℝ) ≤ M.radius + ε / 2 := by linarith
  have hsub : closedBall (M.centre 0 + (M.radius + ε / 2) • u) (ε / 4) ⊆ V := by
    intro z hz
    apply hball
    rw [mem_ball]
    rw [mem_closedBall] at hz
    have h1 : dist (M.centre 0 + (M.radius + ε / 2) • u) y = ε / 2 := by
      rw [dist_eq_norm]
      simp only [y]
      rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hu, mul_one,
        show M.radius + ε / 2 - M.radius = ε / 2 by ring, Real.norm_of_nonneg (by positivity)]
    have := dist_triangle z (M.centre 0 + (M.radius + ε / 2) • u) y
    linarith
  refine ⟨M.centre 0 + (M.radius + ε / 2) • u, ε / 4, by positivity,
    hsub.trans Set.inter_subset_left, ?_⟩
  intro a
  by_cases ha : a = 0
  · subst ha
    apply closedBall_disjoint_closedBall
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_of_nonneg hk]
    linarith
  · rw [Set.disjoint_left]
    intro z hz hz'
    exact Set.mem_iInter₂.1 (hsub hz).2 a ha hz'

/-- Step 2 of the V4 proof of `clusterData_exists` (V4 2.10): "choose pairwise
disjoint closed balls" — a closed ball of positive radius in `E d` contains, for any
finite index type, a family of pairwise disjoint closed balls of one common positive
radius (one for the state ball and the CORE, READOUT and TRIGGER balls). -/
private theorem clusterData_exists_step2_disjointBalls (K : Type) [Finite K] (p : E d)
    (r : ℝ) (hr : 0 < r) :
    ∃ c : K → E d, ∃ s : ℝ, 0 < s ∧ (∀ k, closedBall (c k) s ⊆ closedBall p r) ∧
      Pairwise (fun k k' => Disjoint (closedBall (c k) s) (closedBall (c k') s)) := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin K
  have hd : 0 < d := lt_of_lt_of_le two_pos (Fact.out : 2 ≤ d)
  let u : E d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)
  have hu : ‖u‖ = 1 := by simp [u]
  set s : ℝ := r / (4 * ((n : ℝ) + 1)) with hs_def
  have hn : (0 : ℝ) < 4 * ((n : ℝ) + 1) := by positivity
  have hs : 0 < s := by positivity
  have hrs : r = 4 * ((n : ℝ) + 1) * s := by rw [hs_def]; field_simp
  refine ⟨fun k => p + (((e k : ℕ) : ℝ) * (4 * s)) • u, s, hs, ?_, ?_⟩
  · intro k y hy
    rw [mem_closedBall] at hy ⊢
    have hk : ((e k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt (e k).isLt
    have h1 : dist (p + (((e k : ℕ) : ℝ) * (4 * s)) • u) p = ((e k : ℕ) : ℝ) * (4 * s) := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
        Real.norm_of_nonneg (by positivity)]
    have h2 := dist_triangle y (p + (((e k : ℕ) : ℝ) * (4 * s)) • u) p
    have h3 : ((e k : ℕ) : ℝ) * (4 * s) ≤ ((n : ℝ) - 1) * (4 * s) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  · intro k k' hkk'
    apply closedBall_disjoint_closedBall
    have hne : (e k : ℕ) ≠ e k' := fun h => hkk' (e.injective (Fin.ext h))
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hu, mul_one,
      Real.norm_eq_abs]
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h' : ((e k : ℕ) : ℝ) + 1 ≤ ((e k' : ℕ) : ℝ) := by exact_mod_cast h
      rw [lt_abs]; right
      nlinarith [mul_le_mul_of_nonneg_right h' (by positivity : (0 : ℝ) ≤ 4 * s)]
    · have h' : ((e k' : ℕ) : ℝ) + 1 ≤ ((e k : ℕ) : ℝ) := by exact_mod_cast h
      rw [lt_abs]; left
      nlinarith [mul_le_mul_of_nonneg_right h' (by positivity : (0 : ℝ) ≤ 4 * s)]

/-- Step 3 of the V4 proof of `clusterData_exists` (V4 2.10): "the d+1 affinely
independent microball centres of each cluster within distance ε/2 of its anchor" —
for every anchor `q` and scale `t > 0` there are `d+1` affinely independent points
within distance `t` of `q`, pairwise at distance at least `t`. -/
private theorem clusterData_exists_step3_affineCluster (q : E d) (t : ℝ) (ht : 0 < t) :
    ∃ c : Fin (d + 1) → E d, AffineIndependent ℝ c ∧ (∀ a, dist (c a) q ≤ t) ∧
      ∀ a b, a ≠ b → t ≤ dist (c a) (c b) := by
  classical
  let v : Fin (d + 1) → E d := fun a =>
    if h : a = 0 then 0 else EuclideanSpace.single (a.pred h) (1 : ℝ)
  refine ⟨fun a => q + t • v a, ?_, ?_, ?_⟩
  · rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin (d + 1))]
    have hb := ((EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.linearIndependent.comp
      (fun x : {x : Fin (d + 1) // x ≠ 0} => x.1.pred x.2)
      (fun x y hxy => Subtype.ext (Fin.pred_inj.1 hxy))).units_smul
      (fun _ => Units.mk0 t ht.ne')
    convert hb using 1
    funext x
    simp [v, x.2, Units.smul_def, Units.val_mk0, EuclideanSpace.basisFun_apply]
  · intro a
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
    have : ‖v a‖ ≤ 1 := by
      by_cases h : a = 0 <;> simp [v, h]
    exact mul_le_of_le_one_right ht.le this
  · intro a b hab
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
      Real.norm_of_nonneg ht.le]
    suffices h1 : 1 ≤ ‖v a - v b‖ by nlinarith
    by_cases ha : a = 0
    · have hb : b ≠ 0 := fun h => hab (ha.trans h.symm)
      have := PiLp.norm_apply_le (v a - v b) (b.pred hb)
      simpa [v, ha, hb] using this
    · have := PiLp.norm_apply_le (v a - v b) (a.pred ha)
      by_cases hb : b = 0
      · simpa [v, ha, hb] using this
      · have hne : a.pred ha ≠ b.pred hb := fun h => hab (Fin.pred_inj.1 h)
        simpa [v, ha, hb, EuclideanSpace.single_apply, hne, hab] using this

/-- Step 4 of the V4 proof of `clusterData_exists` (V4 2.10): "smaller than ... (over
the finite catalogue)" — a finite family of positive reals has a positive lower bound;
an empty family is bounded below by `1`. -/
private theorem clusterData_exists_step4_lowerBound {α : Type*} [Finite α] (f : α → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ R : ℝ, 0 < R ∧ ∀ i, R ≤ f i := by
  rcases isEmpty_or_nonempty α with h | h
  · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i, hi⟩ := Finite.exists_min f
    exact ⟨f i, hf i, hi⟩

/-- Step 5 of the V4 proof of `clusterData_exists` (V4 2.10): "every microball centre
has clearance > δ from the leaf boundary" — a closed ball inside the interior is
strictly closer to its centre than any frontier point. -/
private theorem clusterData_exists_step5_frontier {s : Set (E d)} {x y : E d} {R : ℝ}
    (hsub : closedBall x R ⊆ interior s) (hy : y ∈ frontier s) : R < dist x y := by
  by_contra h
  push_neg at h
  exact hy.2 (hsub (mem_closedBall.2 (by rw [dist_comm]; exact h)))

/-- M2, V4 2.10: all geometric choices exist over the finite catalogues.
Prototype interiors provide room outside the finitely many disjoint marker balls;
empty source catalogues cause no difficulty and require no extra hypotheses. -/
theorem clusterData_exists (S : SubstSystem d) (P : Params S) :
    Nonempty (ClusterData S P) := by
  classical
  choose p r hr hin hmk using clusterData_exists_step1_room S P
  choose c₀ s₀ hs₀ hsub₀ hdisj₀ using
    fun A => clusterData_exists_step2_disjointBalls Bool (p A) (r A) (hr A)
  choose c₁ s₁ hs₁ hsub₁ hdisj₁ using
    fun l : LeafType P => clusterData_exists_step2_disjointBalls (ClusterKind l)
      (c₀ l.prototype false) (s₀ l.prototype) (hs₀ _)
  obtain ⟨R, hR, hRle⟩ := clusterData_exists_step4_lowerBound (fun l : LeafType P => s₁ l) hs₁
  have ht : (0 : ℝ) < R / 256 := by positivity
  choose m hmind hmnear hmsep using
    fun (l : LeafType P) (κ : ClusterKind l) =>
      clusterData_exists_step3_affineCluster (c₁ l κ) (R / 256) ht
  -- the enclosing ball of radius `R` lies in the room ball of its prototype
  have hbig : ∀ (l : LeafType P) (κ : ClusterKind l),
      closedBall (c₁ l κ) R ⊆ closedBall (c₀ l.prototype false) (s₀ l.prototype) :=
    fun l κ => (closedBall_subset_closedBall (hRle l)).trans (hsub₁ l κ)
  have hint : ∀ (l : LeafType P) (κ : ClusterKind l),
      closedBall (c₁ l κ) R ⊆ interior (S.proto l.prototype).carrier :=
    fun l κ => ((hbig l κ).trans (hsub₀ _ false)).trans (hin _)
  have hcen : ∀ (l : LeafType P) (κ : ClusterKind l) (a : Fin (d + 1)),
      closedBall (m l κ a) (R / 8) ⊆ closedBall (c₁ l κ) R := by
    intro l κ a y hy
    rw [mem_closedBall] at hy ⊢
    have := dist_triangle y (m l κ a) (c₁ l κ)
    have := hmnear l κ a
    linarith
  refine ⟨{
    stateCentre := fun A => c₀ A true
    stateRadius := s₀
    stateRadius_pos := hs₀
    state_inside := fun A => ((hsub₀ A true).trans (hin A))
    state_marker_disjoint := fun A a => (hmk A a).mono_left (hsub₀ A true)
    enclosingCentre := c₁
    enclosingRadius := fun _ _ => R
    enclosingRadius_pos := fun _ _ => hR
    enclosing_inside := hint
    enclosing_disjoint := fun l κ η hκη =>
      ((hdisj₁ l hκη).mono_left (closedBall_subset_closedBall (hRle l))).mono_right
        (closedBall_subset_closedBall (hRle l))
    enclosing_marker_disjoint := fun l κ a =>
      (hmk l.prototype a).mono_left ((hbig l κ).trans (hsub₀ _ false))
    enclosing_state_disjoint := fun l κ =>
      ((hdisj₀ l.prototype (show (false : Bool) ≠ true by decide)).mono_left (hbig l κ))
    anchor := c₁
    anchor_inside := fun l κ => mem_ball_self hR
    δ := R / 8
    δ_pos := by positivity
    anchor_boundary := fun l κ x hx => by
      have := clusterData_exists_step5_frontier (hint l κ) hx
      linarith
    anchor_separation := fun l κ η hκη => by
      have hd := (hdisj₁ l hκη).mono_left (closedBall_subset_closedBall (hRle l))
      have hd' := hd.mono_right (closedBall_subset_closedBall (hRle l))
      have : R < dist (c₁ l κ) (c₁ l η) := by
        by_contra h
        push_neg at h
        exact Set.disjoint_left.1 hd'
          (mem_closedBall.2 (by rw [dist_comm]; exact h)) (mem_closedBall_self hR.le)
      linarith
    ε := R / 64
    ε_pos := by positivity
    ε_lt := by linarith
    centre := m
    centre_near := fun l κ a => by
      have := hmnear l κ a
      linarith
    independent := hmind
    ρ := R / 1024
    ρ_pos := by positivity
    ρ_lt := by linarith
    micro_inside := fun l κ a y hy => by
      rw [mem_closedBall] at hy
      rw [mem_ball]
      have := dist_triangle y (m l κ a) (c₁ l κ)
      have := hmnear l κ a
      linarith
    micro_disjoint := fun l κ a b hab => by
      apply closedBall_disjoint_closedBall
      have := hmsep l κ a b hab
      linarith
    cluster_diameter := fun l κ => by
      have hsub : (⋃ a, closedBall (m l κ a) (R / 1024)) ⊆
          closedBall (c₁ l κ) (R / 256 + R / 1024) := by
        refine Set.iUnion_subset fun a y hy => ?_
        rw [mem_closedBall] at hy ⊢
        have := dist_triangle y (m l κ a) (c₁ l κ)
        have := hmnear l κ a
        linarith
      have h1 := diam_mono hsub isBounded_closedBall
      have h2 := diam_closedBall (x := c₁ l κ) (show (0 : ℝ) ≤ R / 256 + R / 1024 by positivity)
      linarith
    centre_boundary := fun l κ a x hx =>
      clusterData_exists_step5_frontier ((hcen l κ a).trans (hint l κ)) hx
    centre_clearance := fun l κ a => (hcen l κ a).trans (hint l κ) }⟩

namespace ClusterData

variable {P : Params S} (C : ClusterData S P)

/-- M2, V4 2.10: a closed enclosing ball in prototype coordinates. -/
def enclosing (l : LeafType P) (κ : ClusterKind l) : Set (E d) :=
  closedBall (C.enclosingCentre l κ) (C.enclosingRadius l κ)

/-- M2, V4 2.10: the open hole omitted from a CORE carrier. -/
def openTrigger (l : LeafType P) (j : EventSlot l) : Set (E d) :=
  ball (C.enclosingCentre l (.trigger j)) (C.enclosingRadius l (.trigger j))

/-- M2, V4 2.10: one closed microball. -/
def microball (l : LeafType P) (κ : ClusterKind l) (a : Fin (d + 1)) : Set (E d) :=
  closedBall (C.centre l κ a) C.ρ

/-- M2, V4 2.10: an entire cluster is the union of its d+1 closed microballs. -/
def cluster (l : LeafType P) (κ : ClusterKind l) : Set (E d) :=
  ⋃ a, C.microball l κ a

/-- M2, V4 2.10: all cluster points lie in the physical leaf interior. -/
theorem cluster_inside (l : LeafType P) (κ : ClusterKind l) :
    C.cluster l κ ⊆ interior (S.proto l.prototype).carrier := by
  intro x hx
  dsimp [cluster, microball] at hx
  obtain ⟨a, hx_ball⟩ := Set.mem_iUnion.mp hx
  have h1 := C.micro_inside l κ a hx_ball
  have h2 := ball_subset_closedBall h1
  exact C.enclosing_inside l κ h2

/-- M2, V4 2.10: all microballs in a leaf, across all kinds, are disjoint. -/
theorem all_microballs_disjoint (l : LeafType P) :
    Pairwise (fun u v : ClusterKind l × Fin (d + 1) =>
      Disjoint (C.microball l u.1 u.2) (C.microball l v.1 v.2)) := by
  rintro ⟨k1, a1⟩ ⟨k2, a2⟩ hneq
  by_cases hk : k1 = k2
  · subst hk
    have ha : a1 ≠ a2 := fun ha => hneq (Prod.ext rfl ha)
    exact C.micro_disjoint l k1 ha
  · have hd := C.enclosing_disjoint l hk
    have hsub1 : C.microball l k1 a1 ⊆ C.enclosing l k1 := (C.micro_inside l k1 a1).trans Metric.ball_subset_closedBall
    have hsub2 : C.microball l k2 a2 ⊆ C.enclosing l k2 := (C.micro_inside l k2 a2).trans Metric.ball_subset_closedBall
    exact hd.mono hsub1 hsub2



end ClusterData

/-- M2, V4 2.10: the honest pre-pattern component of an admissible leaf. -/
def LeafType.symbol {P : Params S} (l : LeafType P) : PrePatternSymbol S P :=
  ⟨l.prePattern, (certificate_components_honest P l.1.val l.1.property).1 l.2⟩

/-- M2, V4 2.10: the full finite colour alphabet, with disjoint tagged families.
Frame colours retain the prototype. State and background colours retain the honest
pre-pattern, which includes the prototype, state and every facet packet. -/
inductive Colour (S : SubstSystem d) (P : Params S)
  /-- M2, V4 2.10: interior colour (type, pre-pattern), with type stored in the symbol. -/
  | inside : PrePatternSymbol S P → Colour S P
  /-- M2, V4 §2.4, 2.10: fixed labelled frame-marker colour. -/
  | frame : S.ι → Fin (d + 1) → Colour S P
  /-- M2, V4 2.10: encoding of the same pre-pattern on the further state ball. -/
  | state : PrePatternSymbol S P → Colour S P
  /-- M2, V4 2.10: CORE microball colour. -/
  | core : LeafType P → Fin (d + 1) → Colour S P
  /-- M2, V4 2.10: READOUT microball colour. -/
  | readout : LeafType P → Fin (d + 1) → Colour S P
  /-- M2, V4 2.10: TRIGGER colour includes its exact slot. -/
  | trigger : (l : LeafType P) → EventSlot l → Fin (d + 1) → Colour S P
  /-- M2, V4 2.10: the common boundary colour @. -/
  | boundary : Colour S P

/-- M2, V4 2.10: finiteness follows from pre-patterns, leaf types and slot finiteness. -/
theorem colours_finite (S : SubstSystem d) (P : Params S) : Finite (Colour S P) := by
  let f : PrePatternSymbol S P ⊕ (S.ι × Fin (d+1)) ⊕ PrePatternSymbol S P ⊕ (LeafType P × Fin (d+1)) ⊕ (LeafType P × Fin (d+1)) ⊕ (Σ (l : LeafType P), EventSlot l × Fin (d+1)) ⊕ Unit → Colour S P :=
    fun x => match x with
      | Sum.inl a => Colour.inside a
      | Sum.inr (Sum.inl (A, i)) => Colour.frame A i
      | Sum.inr (Sum.inr (Sum.inl a)) => Colour.state a
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl (l, i)))) => Colour.core l i
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (l, i))))) => Colour.readout l i
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨l, j, i⟩))))) => Colour.trigger l j i
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))) => Colour.boundary
  apply Finite.of_surjective f
  intro c
  cases c
  · exact ⟨Sum.inl ‹_›, rfl⟩
  · exact ⟨Sum.inr (Sum.inl (‹_›, ‹_›)), rfl⟩
  · exact ⟨Sum.inr (Sum.inr (Sum.inl ‹_›)), rfl⟩
  · exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl (‹_›, ‹_›)))), rfl⟩
  · exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (‹_›, ‹_›))))), rfl⟩
  · exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨‹_›, ‹_›, ‹_›⟩))))), rfl⟩
  · exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))), rfl⟩

/-- M2, V4 2.10: a noncomputable finite enumeration of all tagged colours. -/
instance colourFintype (S : SubstSystem d) (P : Params S) : Fintype (Colour S P) := by
  letI := colours_finite S P
  exact Fintype.ofFinite _

/-- M2, V4 2.10: colour of one labelled microball of the indicated kind. -/
def microColour {P : Params S} (l : LeafType P) (κ : ClusterKind l)
    (a : Fin (d + 1)) : Colour S P :=
  match κ with
  | .core => .core l a
  | .readout => .readout l a
  | .trigger j => .trigger l j a

/-- M2, V4 2.10: exact native projection; only @ projects to the boundary symbol. -/
def π (S : SubstSystem d) (P : Params S) : Colour S P → Option S.ι
  | .inside w => some w.val.ty
  | .frame A _ => some A
  | .state w => some w.val.ty
  | .core l _ => some l.prototype
  | .readout l _ => some l.prototype
  | .trigger l _ _ => some l.prototype
  | .boundary => none

/-- M2, V4 2.10: ambient extension of the augmented leaf marking by @.
On the interior the disjoint microballs override the pre-pattern, followed by
frame markers, the state ball, and the background symbol. On the whole complement
of the interior the extension is @; physical markings restrict to the closed leaf. -/
def augmentedColour {P : Params S} (C : ClusterData S P) (l : LeafType P)
    (x : E d) : Colour S P := by
  classical
  exact if x ∈ interior (S.proto l.prototype).carrier then
    if hm : ∃ z : ClusterKind l × Fin (d + 1), x ∈ C.microball l z.1 z.2 then
      microColour l (Classical.choose hm).1 (Classical.choose hm).2
    else if hf : ∃ a, x ∈ closedBall ((P.marker l.prototype).centre a)
        (P.marker l.prototype).radius then
      .frame l.prototype (Classical.choose hf)
    else if x ∈ closedBall (C.stateCentre l.prototype) (C.stateRadius l.prototype) then
      .state l.symbol
    else .inside l.symbol
    else .boundary

/-- M2, V4 2.10: the genuine marking function on the closed prototype carrier. -/
def augmentedMarking {P : Params S} (C : ClusterData S P) (l : LeafType P) :
    (S.proto l.prototype).carrier → Colour S P := fun x => augmentedColour C l x

/-- M2, V4 2.10: every point of a closed microball has its exact tagged colour. -/
theorem augmentedMarking_microball {P : Params S} (C : ClusterData S P)
    (l : LeafType P) (κ : ClusterKind l) (a : Fin (d + 1)) (x : E d)
    (hx : x ∈ C.microball l κ a) : augmentedColour C l x = microColour l κ a := by
  sorry

/-- M2, V4 2.10: a microball colour occurs precisely on that one closed microball.
The statement includes all points of the ambient extension and all source leaves. -/
theorem augmentedColour_micro_iff {P : Params S} (C : ClusterData S P)
    (l u : LeafType P) (κ : ClusterKind l) (a : Fin (d + 1)) (x : E d) :
    augmentedColour C u x = microColour l κ a ↔ u = l ∧ x ∈ C.microball l κ a := by
  sorry

/-- M2, V4 §2.4, 2.10: the prescribed frame-marker balls retain their colours. -/
theorem augmentedMarking_frame {P : Params S} (C : ClusterData S P)
    (l : LeafType P) (a : Fin (d + 1)) (x : E d)
    (hx : x ∈ closedBall ((P.marker l.prototype).centre a) (P.marker l.prototype).radius) :
    augmentedColour C l x = Colour.frame l.prototype a := by
  sorry

/-- M2, V4 2.10: the small state ball encodes the complete pre-pattern. -/
theorem augmentedMarking_state {P : Params S} (C : ClusterData S P)
    (l : LeafType P) (x : E d)
    (hx : x ∈ closedBall (C.stateCentre l.prototype) (C.stateRadius l.prototype)) :
    augmentedColour C l x = Colour.state l.symbol := by
  dsimp [augmentedColour]
  have hint : x ∈ interior (S.proto l.prototype).carrier := by
    exact C.state_inside l.prototype hx
  rw [if_pos hint]
  have hf : ¬ ∃ a, x ∈ closedBall ((P.marker l.prototype).centre a) (P.marker l.prototype).radius := by
    intro ⟨a, ha⟩
    have hd := C.state_marker_disjoint l.prototype a
    exact Set.disjoint_left.mp hd hx ha
  have hm : ¬ ∃ z : ClusterKind l × Fin (d + 1), x ∈ C.microball l z.1 z.2 := by
    intro ⟨⟨κ, a⟩, h_micro⟩
    have hd := C.enclosing_state_disjoint l κ
    have h_micro_sub := C.micro_inside l κ a
    have h_enc : x ∈ closedBall (C.enclosingCentre l κ) (C.enclosingRadius l κ) := by
      exact Metric.ball_subset_closedBall (h_micro_sub h_micro)
    exact Set.disjoint_left.mp hd h_enc hx
  rw [dif_neg hm, dif_neg hf, if_pos hx]

/-- M2, V4 2.10: projection is the native type at every interior point. -/
theorem augmentedMarking_projection {P : Params S} (C : ClusterData S P)
    (l : LeafType P) (x : E d) (hx : x ∈ interior (S.proto l.prototype).carrier) :
    π S P (augmentedColour C l x) = some l.prototype := by
  sorry

/-- M2, V4 2.10: all physical boundary points have the common colour @. -/
theorem augmentedMarking_boundary {P : Params S} (C : ClusterData S P)
    (l : LeafType P) (x : E d) (hx : x ∈ frontier (S.proto l.prototype).carrier) :
    augmentedColour C l x = Colour.boundary := by
  unfold augmentedColour
  split_ifs with h1 _ _ _
  · exfalso
    exact Set.disjoint_left.mp disjoint_interior_frontier h1 hx
  · exfalso
    exact Set.disjoint_left.mp disjoint_interior_frontier h1 hx
  · exfalso
    exact Set.disjoint_left.mp disjoint_interior_frontier h1 hx
  · exfalso
    exact Set.disjoint_left.mp disjoint_interior_frontier h1 hx
  · rfl

/-- M2/M3, V4 2.10--2.11: an augmented physical prototype has the native carrier. -/
def augmentedLeaf {P : Params S} (C : ClusterData S P) (l : LeafType P) :
    MarkedPrototile d (Colour S P) where
  carrier := (S.proto l.prototype).carrier
  mark := augmentedMarking C l
  compact := (S.proto l.prototype).compact
  regularClosed := (S.proto l.prototype).regularClosed

/-- M2, V4 §2.4, 2.10: the complete marked carrier pins both label and frame.
The CORE colours identify the leaf type, and the affinely independent labelled
frame markers identify the isometry, including possible reflections. -/
theorem augmentedLeaf_rigid {P : Params S} (C : ClusterData S P)
    (l u : LeafType P) (φ ψ : Iso d)
    (h : (augmentedLeaf C l).toMarkedSet.move φ =
      (augmentedLeaf C u).toMarkedSet.move ψ) : l = u ∧ φ = ψ := by
  sorry

variable {P : Params S}

namespace ClusterData

variable (C : ClusterData S P)

/-- M2/M5, V4 2.10, 2.13: the full cluster diameter is below the separation scale. -/
theorem cluster_diam_lt_two_delta (l : LeafType P) (κ : ClusterKind l) :
    diam (C.cluster l κ) < 2 * C.δ := by
  have hε := C.ε_lt
  have hδ := C.δ_pos
  have hdiam := C.cluster_diameter l κ
  change diam (⋃ a, closedBall (C.centre l κ a) C.ρ) < 2 * C.δ
  linarith

/-- M2, V4 2.10: an entire closed microball lies in its enclosing region. -/
theorem microball_subset_enclosing (l : LeafType P) (κ : ClusterKind l)
    (a : Fin (d + 1)) : C.microball l κ a ⊆ C.enclosing l κ :=
  (C.micro_inside l κ a).trans ball_subset_closedBall

/-- M2, V4 2.10: every complete cluster lies in its enclosing region. -/
theorem cluster_subset_enclosing (l : LeafType P) (κ : ClusterKind l) :
    C.cluster l κ ⊆ C.enclosing l κ := by
  intro x hx
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  exact C.microball_subset_enclosing l κ a ha

/-- M2/M4, V4 2.10, 2.12(ii): a TRIG cluster is wholly inside the open CORE hole. -/
theorem trigger_cluster_subset_open (l : LeafType P) (j : EventSlot l) :
    C.cluster l (.trigger j) ⊆ C.openTrigger l j := by
  intro x hx
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  exact C.micro_inside l (.trigger j) a ha

/-- M2/M4, V4 2.10, 2.12: each closed cluster is disjoint from the enclosing
regions of all different kinds, so reading a whole RO ball introduces no CORE or TRIG. -/
theorem cluster_disjoint_enclosing (l : LeafType P) (κ η : ClusterKind l)
    (hne : κ ≠ η) : Disjoint (C.cluster l κ) (C.enclosing l η) := by
  exact (C.enclosing_disjoint l hne).mono_left (C.cluster_subset_enclosing l κ)

/-- M2/M4, V4 2.10, 2.12(iii): a delta-neighbourhood of every centre is interior. -/
theorem centre_ball_inside (l : LeafType P) (κ : ClusterKind l) (a : Fin (d + 1)) :
    ball (C.centre l κ a) C.δ ⊆ interior (S.proto l.prototype).carrier :=
  ball_subset_closedBall.trans (C.centre_clearance l κ a)

end ClusterData

/-- M2, V4 2.10: only the boundary colour projects to the boundary symbol. -/
theorem colour_projection_none_iff (c : Colour S P) :
    π S P c = none ↔ c = Colour.boundary := by
  cases c <;> simp only [π, reduceCtorEq, iff_self]

/-- M2, V4 2.10: every microcolour projects to exactly its native prototype. -/
theorem microColour_projection (l : LeafType P) (κ : ClusterKind l)
    (a : Fin (d + 1)) : π S P (microColour l κ a) = some l.prototype := by
  cases κ <;> rfl

/-- M2/M5, V4 2.10, 2.13: equal microcolours identify the full leaf, kind and label.
Heterogeneous kind equality retains the dependent slot index when the kind is TRIG. -/
theorem microColour_injective (l u : LeafType P) (κ : ClusterKind l) (η : ClusterKind u)
    (a b : Fin (d + 1)) (h : microColour l κ a = microColour u η b) :
    l = u ∧ HEq κ η ∧ a = b := by
  sorry

end Enforce
