import Enforce.Source.Trace

/-!
# Hereditary edge graph and the opposite-root bound

Graph vertices include the prototype type and its listed edge name. Edge vectors
are chosen endpoints of actual listed segments, with no preferred orientation.
The bounds apply to every reachable ordered pair and every common expansion power.
-/

open Set

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- P15, V4 1.20: a graph vertex is a prototype and one of its listed edges. -/
abbrev EdgeName (S : SubstSystem d) := Σ A : S.ι, {e // e ∈ (S.cx A).edges}

/-- P15, V4 1.20: a listed one-cell is a nondegenerate closed segment.
Connectedness and regular closedness in its one-dimensional affine span give this. -/
theorem edge_endpoints_exist (e : EdgeName S) :
    ∃ ab : E d × E d, ab.1 ≠ ab.2 ∧ e.2.val.carrier = segment ℝ ab.1 ab.2 := by
  let K := e.2.val.carrier
  have hdim1 : e.2.val.dim = 1 := by
    have h := e.2.property
    unfold CellComplex.edges at h
    simpa [Finset.mem_filter] using (Finset.mem_filter.mp h).2
  have hdim : Module.finrank ℝ (affineSpan ℝ K).direction = 1 := by
    have h2 := e.2.val.flat.dimension
    rwa [hdim1] at h2
  have hd := hdim
  have hne : K.Nonempty := e.2.val.flat.connected.nonempty
  have hc : IsCompact K := e.2.val.flat.compact
  have hconn : IsConnected K := e.2.val.flat.connected
  obtain ⟨p, hp⟩ := hne
  obtain ⟨u, hu0, hu⟩ := finrank_eq_one_iff'.mp hd
  set u' : E d := (u : E d)
  have hu' : u' ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hcoord : ∀ x ∈ K, ∃ c : ℝ, x = p + c • u' := by
    intro x hx
    have h := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K hx) (subset_affineSpan ℝ K hp)
    rw [vsub_eq_sub] at h
    obtain ⟨c, hc_eq⟩ := hu ⟨x - p, h⟩
    exact ⟨c, by have := congrArg Subtype.val hc_eq; simp at this; rw [this]; abel⟩
  let f : ℝ →ᵃ[ℝ] E d := AffineMap.lineMap p (p + u')
  have hf : ∀ t, f t = p + t • u' := by
    intro t; simp [f, AffineMap.lineMap_apply, add_comm]
  let ℓ : E d → ℝ := fun x => inner ℝ u' (x - p) / ‖u'‖ ^ 2
  have hn : ‖u'‖ ≠ 0 := norm_ne_zero_iff.mpr hu'
  have hℓ : ∀ t, ℓ (f t) = t := by
    intro t
    dsimp [ℓ]
    have H : (p + t • u') - p = t • u' := by
      exact add_sub_cancel_left p (t • u')
    rw [hf, H, inner_smul_right, real_inner_self_eq_norm_sq]
    have H2 : t * ‖u'‖ ^ 2 / ‖u'‖ ^ 2 = t := by
      exact mul_div_cancel_right₀ t (pow_ne_zero 2 hn)
    exact H2
  have hcont : Continuous ℓ := by fun_prop
  have hfl : ∀ x ∈ K, f (ℓ x) = x := by
    intro x hx; obtain ⟨c, rfl⟩ := hcoord x hx; rw [← hf, hℓ]
  set T := ℓ '' K
  have hTc : IsCompact T := hc.image hcont
  have hTp : IsPreconnected T := hconn.isPreconnected.image ℓ hcont.continuousOn
  have hTo : T.OrdConnected := isPreconnected_iff_ordConnected.mp hTp
  have hne : T.Nonempty := hconn.nonempty.image ℓ
  obtain ⟨a, ha⟩ := hTc.exists_isLeast hne
  obtain ⟨b, hb⟩ := hTc.exists_isGreatest hne
  have hTI : T = Set.Icc a b :=
    Set.Subset.antisymm (fun t ht => ⟨ha.2 ht, hb.2 ht⟩) (hTo.out ha.1 hb.1)
  have hab : a ≤ b := ha.2 hb.1
  have hKT : K = f '' T := by
    ext x; constructor
    · intro hx; exact ⟨ℓ x, ⟨x, hx, rfl⟩, hfl x hx⟩
    · rintro ⟨t, ⟨y, hy, rfl⟩, rfl⟩; rw [hfl y hy]; exact hy
  have hseg : K = segment ℝ (f a) (f b) := by
    have H : f '' Set.Icc a b = segment ℝ (f a) (f b) := by
      rw [← segment_eq_Icc hab]
      exact image_segment ℝ f a b
    rw [hKT, hTI, H]
  refine ⟨(f a, f b), ?_, hseg⟩
  intro hEq
  simp only at hEq
  have hsub : K ⊆ {f a} := by
    rw [hseg, hEq, segment_same]
  have h0 : (affineSpan ℝ K).direction = ⊥ := by
    rw [direction_affineSpan]
    have h1 : vectorSpan ℝ K ≤ vectorSpan ℝ {f a} := vectorSpan_mono ℝ hsub
    rw [vectorSpan_singleton] at h1
    exact le_bot_iff.mp h1
  have h_bot : Module.finrank ℝ (affineSpan ℝ K).direction = 0 := by
    rw [h0]
    exact finrank_bot ℝ (E d)
  rw [h_bot] at hdim
  contradiction

/-- P15, V4 1.20: an arbitrary orientation of the actual edge vector. -/
def edgeVector (e : EdgeName S) : E d :=
  (Classical.choose (edge_endpoints_exist e)).2 -
    (Classical.choose (edge_endpoints_exist e)).1

/-- P15, V4 1.20: the selected endpoints represent the listed edge and are distinct. -/
theorem edgeVector_spec (e : EdgeName S) :
    edgeVector e ≠ 0 ∧
      Metric.diam e.2.val.carrier = ‖edgeVector e‖ := by
  obtain ⟨hne, hcar⟩ := Classical.choose_spec (edge_endpoints_exist e)
  refine ⟨?_, ?_⟩
  · unfold edgeVector
    exact sub_ne_zero.mpr (Ne.symm hne)
  · unfold edgeVector
    have key : ∀ a b : E d, Metric.diam (segment ℝ a b) = ‖b - a‖ := fun a b => by
      rw [← convexHull_pair, convexHull_diam, Metric.diam_pair, dist_comm, dist_eq_norm]
    exact (congrArg Metric.diam hcar).trans (key _ _)

/-- P15, V4 1.20: the finite directed hereditary graph `Γ`.
An arrow records an actual child edge occurrence in the expanded source edge. -/
def edgeGraph (S : SubstSystem d) (e f : EdgeName S) : Prop :=
  ∃ i : S.I e.1, (S.child e.1 i).ty = f.1 ∧
    placedSet (S.child e.1 i).frame f.2.val.carrier ⊆ S.σ '' e.2.val.carrier

/-- P15, V4 1.20: finite graph vertex set, including the empty-catalogue case. -/
theorem edgeNames_finite (S : SubstSystem d) : Finite (EdgeName S) := by
  infer_instance

/-- P15, V4 1.20: the length of an edge after a common power of the expansion. -/
def expandedEdgeLength (r : ℕ) (e : EdgeName S) : ℝ := ‖(S.σ ^ r) (edgeVector e)‖

/-- P15, V4 1.20: constants controlling all reachable edge pairs. -/
structure EdgeBounds (S : SubstSystem d) where
  /-- P15, V4 1.20: positive lower ratio bound. -/
  lower : ℝ
  /-- P15, V4 1.20: finite upper ratio bound. -/
  upper : ℝ
  /-- P15, V4 1.20: strict positivity. -/
  lower_pos : 0 < lower
  /-- P15, V4 1.20: ordered bounds. -/
  lower_le_upper : lower ≤ upper
  /-- P15, V4 1.20: the same bounds for every path and every power. -/
  bounds : ∀ e f : EdgeName S, Relation.ReflTransGen (edgeGraph S) e f →
    ∀ r : ℕ, lower ≤ expandedEdgeLength r f / expandedEdgeLength r e ∧
      expandedEdgeLength r f / expandedEdgeLength r e ≤ upper

/-- Step 1 of the V4 proof of `edge_ratio_bounds` (V4 1.20, (H4)):
"`|σ^r R x| = |σ^r R σ^{-r} σ^r x| = |σ^r x|`". -/
private theorem edge_ratio_bounds_step1_norm_conj (S : SubstSystem d) (r : ℕ) (A : S.ι)
    (i : S.I A) (x : E d) :
    ‖(S.σ ^ r) ((S.child A i).rotation x)‖ = ‖(S.σ ^ r) x‖ := by
  have h := S.h4 r A i ((S.σ ^ r) x)
  have hinv : (S.σ ^ r)⁻¹ ((S.σ ^ r) x) = x := by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  rw [linearConj, zpow_neg, zpow_natCast, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    hinv] at h
  exact h

/-- Step 2 of the V4 proof of `edge_ratio_bounds` (V4 1.20):
"For an arrow `e → f` realised by a child with placement `R` and length ratio
`c_ef > 0`: `R v_f = ± c_ef σ v_e`; ... `|σ^r v_f| = c_ef |σ^{r+1} v_e|`". -/
private theorem edge_ratio_bounds_step2_arrow {e f : EdgeName S} (h : edgeGraph S e f) :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ,
      expandedEdgeLength r f = c * expandedEdgeLength (r + 1) e := by
  obtain ⟨i, -, hsub⟩ := h
  have hf := Classical.choose_spec (edge_endpoints_exist f)
  have he := Classical.choose_spec (edge_endpoints_exist e)
  set a := (Classical.choose (edge_endpoints_exist f)).1 with ha
  set b := (Classical.choose (edge_endpoints_exist f)).2 with hb
  set a' := (Classical.choose (edge_endpoints_exist e)).1 with ha'
  set b' := (Classical.choose (edge_endpoints_exist e)).2 with hb'
  have hvf : edgeVector f = b - a := rfl
  have hve : edgeVector e = b' - a' := rfl
  set R := (S.child e.1 i).rotation with hR
  set φ := (S.child e.1 i).frame with hφ
  have hφapp : ∀ x, φ x = R x + (S.child e.1 i).offset := fun x => rfl
  -- images of endpoints lie in `σ '' segment a' b'`
  have hmem : ∀ x ∈ segment ℝ a b, ∃ t : ℝ, φ x = S.σ a' + t • S.σ (b' - a') := by
    intro x hx
    have : φ x ∈ S.σ '' e.2.val.carrier := hsub ⟨x, by rw [hf.2]; exact hx, rfl⟩
    rw [he.2, segment_eq_image'] at this
    obtain ⟨y, ⟨t, -, rfl⟩, hy⟩ := this
    exact ⟨t, by rw [← hy, map_add, map_smul]⟩
  obtain ⟨t1, h1⟩ := hmem a (left_mem_segment ℝ a b)
  obtain ⟨t2, h2⟩ := hmem b (right_mem_segment ℝ a b)
  have hRv : R (edgeVector f) = (t2 - t1) • S.σ (edgeVector e) := by
    have : φ b - φ a = R (b - a) := by rw [hφapp, hφapp, map_sub]; abel
    rw [hvf, ← this, h1, h2, hve, sub_smul]; abel
  have hvf0 : edgeVector f ≠ 0 := sub_ne_zero.mpr (Ne.symm hf.1)
  have hlam : t2 - t1 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hRv
    exact hvf0 (R.map_eq_zero_iff.mp hRv)
  refine ⟨|t2 - t1|, abs_pos.mpr hlam, fun r => ?_⟩
  have := edge_ratio_bounds_step1_norm_conj S r e.1 i (edgeVector f)
  rw [← hR, hRv, map_smul, norm_smul, Real.norm_eq_abs] at this
  rw [expandedEdgeLength, expandedEdgeLength, ← this, pow_succ, LinearEquiv.mul_apply]

/-- Step 3 of the V4 proof of `edge_ratio_bounds` (V4 1.20):
"Along a path `e = e_0 → ⋯ → e_s = f`: `|σ^r v_f| = C |σ^{r+s} v_e|` with
`C = ∏ c_{e_i e_{i+1}}`" (the empty path gives `C = 1`, `s = 0`). -/
private theorem edge_ratio_bounds_step3_path {e f : EdgeName S}
    (h : Relation.ReflTransGen (edgeGraph S) e f) :
    ∃ C : ℝ, 0 < C ∧ ∃ s : ℕ, ∀ r : ℕ,
      expandedEdgeLength r f = C * expandedEdgeLength (r + s) e := by
  induction h with
  | refl => exact ⟨1, one_pos, 0, fun r => by simp⟩
  | tail _ hgf ih =>
    obtain ⟨C, hC, s, hs⟩ := ih
    obtain ⟨c, hc, hcr⟩ := edge_ratio_bounds_step2_arrow hgf
    refine ⟨c * C, mul_pos hc hC, s + 1, fun r => ?_⟩
    rw [hcr, hs, mul_assoc]
    congr 3
    omega

/-- Step 4 of the V4 proof of `edge_ratio_bounds` (V4 1.20):
"`C a^s ≤ |σ^r v_f| / |σ^r v_e| ≤ C b^s` with `a = s_min(σ)`, `b = ‖σ‖`"
(here `a ≥ c > 1`, so the lower bound `C` suffices). -/
private theorem edge_ratio_bounds_step4_growth (S : SubstSystem d) :
    ∃ β : ℝ, 0 < β ∧ ∀ (e : EdgeName S) (r s : ℕ),
      expandedEdgeLength r e ≤ expandedEdgeLength (r + s) e ∧
        expandedEdgeLength (r + s) e ≤ β ^ s * expandedEdgeLength r e := by
  set T := LinearMap.toContinuousLinearMap (S.σ : E d →ₗ[ℝ] E d)
  have hT : (0 : ℝ) ≤ ‖T‖ := norm_nonneg T
  refine ⟨‖T‖ + 1, by linarith, fun e r s => ?_⟩
  have hup : ∀ x : E d, ‖S.σ x‖ ≤ (‖T‖ + 1) * ‖x‖ := fun x =>
    (T.le_opNorm x).trans (by nlinarith [norm_nonneg x])
  have hlo : ∀ x : E d, ‖x‖ ≤ ‖S.σ x‖ := fun x =>
    le_trans (le_mul_of_one_le_left (norm_nonneg x) S.c_gt_one.le) (S.expand x)
  have key : ∀ (s : ℕ) (y : E d), ‖y‖ ≤ ‖(S.σ ^ s) y‖ ∧
      ‖(S.σ ^ s) y‖ ≤ (‖T‖ + 1) ^ s * ‖y‖ := by
    intro s
    induction s with
    | zero =>
      intro y
      rw [pow_zero, pow_zero, one_mul]
      exact ⟨le_rfl, le_rfl⟩
    | succ s ih =>
      intro y
      rw [pow_succ', LinearEquiv.mul_apply]
      refine ⟨(ih y).1.trans (hlo _), (hup _).trans ?_⟩
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih y).2 (by linarith)
  have hsplit : (S.σ ^ (r + s)) (edgeVector e) = (S.σ ^ s) ((S.σ ^ r) (edgeVector e)) := by
    rw [add_comm, pow_add, LinearEquiv.mul_apply]
  unfold expandedEdgeLength
  rw [hsplit]
  exact key s _

/-- Step 5 of the V4 proof of `edge_ratio_bounds` (V4 1.20): edge lengths stay positive,
since the edge vector is nonzero and `σ^r` is invertible. -/
private theorem edge_ratio_bounds_step5_pos (r : ℕ) (e : EdgeName S) :
    0 < expandedEdgeLength r e := by
  have he := Classical.choose_spec (edge_endpoints_exist e)
  have hv : edgeVector e ≠ 0 := sub_ne_zero.mpr (Ne.symm he.1)
  unfold expandedEdgeLength
  exact norm_pos_iff.mpr (fun h0 => hv ((S.σ ^ r).map_eq_zero_iff.mp h0))

/-- Step 6 of the V4 proof of `edge_ratio_bounds` (V4 1.20): for one reachable pair,
the chosen path gives `C ≤ |σ^r v_f| / |σ^r v_e| ≤ C β^s` for all `r`. -/
private theorem edge_ratio_bounds_step6_pair (S : SubstSystem d) (e f : EdgeName S) :
    ∃ lo hi : ℝ, 0 < lo ∧ (Relation.ReflTransGen (edgeGraph S) e f → ∀ r : ℕ,
      lo ≤ expandedEdgeLength r f / expandedEdgeLength r e ∧
        expandedEdgeLength r f / expandedEdgeLength r e ≤ hi) := by
  by_cases h : Relation.ReflTransGen (edgeGraph S) e f
  · obtain ⟨C, hC, s, hs⟩ := edge_ratio_bounds_step3_path h
    obtain ⟨β, -, hβ⟩ := edge_ratio_bounds_step4_growth S
    refine ⟨C, C * β ^ s, hC, fun _ r => ?_⟩
    have hpos := edge_ratio_bounds_step5_pos r e
    obtain ⟨h1, h2⟩ := hβ e r s
    rw [hs, le_div_iff₀ hpos, div_le_iff₀ hpos]
    constructor
    · exact mul_le_mul_of_nonneg_left h1 hC.le
    · rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 hC.le
  · exact ⟨1, 1, one_pos, fun h' => absurd h' h⟩

/-- P15, V4 1.20: uniform hereditary edge ratio bounds exist.
Even an empty graph admits positive constants; no source tiling is assumed. -/
theorem edge_ratio_bounds (S : SubstSystem d) : Nonempty (EdgeBounds S) := by
  choose lo hi hlo hb using edge_ratio_bounds_step6_pair S
  have hfin : Finite (EdgeName S × EdgeName S) := inferInstance
  obtain ⟨M, hM⟩ := (Set.finite_range (fun p : EdgeName S × EdgeName S => hi p.1 p.2)).bddAbove
  obtain ⟨K, hK⟩ :=
    (Set.finite_range (fun p : EdgeName S × EdgeName S => 1 / lo p.1 p.2)).bddAbove
  have hK1 : (0 : ℝ) < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hle : 1 / max K 1 ≤ max M 1 :=
    calc 1 / max K 1 ≤ 1 := by rw [div_le_one hK1]; exact le_max_right _ _
      _ ≤ max M 1 := le_max_right _ _
  have hbd : ∀ e f : EdgeName S, Relation.ReflTransGen (edgeGraph S) e f →
      ∀ r : ℕ, 1 / max K 1 ≤ expandedEdgeLength r f / expandedEdgeLength r e ∧
        expandedEdgeLength r f / expandedEdgeLength r e ≤ max M 1 := by
    intro e f hef r
    obtain ⟨h1, h2⟩ := hb e f hef r
    refine ⟨le_trans ?_ h1, h2.trans ((hM ⟨(e, f), rfl⟩).trans (le_max_left _ _))⟩
    have hk : 1 / lo e f ≤ max K 1 := (hK ⟨(e, f), rfl⟩).trans (le_max_left _ _)
    rw [div_le_iff₀ hK1]
    rw [div_le_iff₀ (hlo e f)] at hk
    linarith [mul_comm (lo e f) (max K 1)]
  exact ⟨⟨1 / max K 1, max M 1, div_pos one_pos hK1, hle, hbd⟩⟩

/-- P16, V4 1.21: the exact paper bound `M = floor (1 / ℓ)`. -/
def oppositeRootBound (B : EdgeBounds S) : ℕ := ⌊1 / B.lower⌋₊

/-- Step 1 of the V4 proof of `opposite_root_edges_bound` (V4 1.21):
"disjoint relative interiors". A nondegenerate real interval has its usual
open interval as relative interior. -/
private theorem opposite_root_edges_bound_step1_interval_relint (a b : ℝ) (hab : a < b) :
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
/-- Step 1 of the V4 proof of `opposite_root_edges_bound` (V4 1.21):
"`∑ |t_i| ≤ |h|`". The relative interior of a nondegenerate segment is measurable
and has the same one-dimensional Hausdorff measure as the closed segment. -/
private theorem opposite_root_edges_bound_step1_segment_measure (p q : E d) (hpq : p ≠ q) :
    MeasurableSet (relint (segment ℝ p q)) ∧
      MeasureTheory.Measure.hausdorffMeasure 1 (relint (segment ℝ p q)) =
        ENNReal.ofReal ‖q - p‖ ∧
      MeasureTheory.Measure.hausdorffMeasure 1 (segment ℝ p q) =
        ENNReal.ofReal ‖q - p‖ := by
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
    rw [hseg, relint, φ.image_intrinsicInterior,
      opposite_root_edges_bound_step1_interval_relint 0 L hL]
  refine ⟨?_, ?_, ?_⟩
  · rw [hrel]
    exact φ.isometry.isClosedEmbedding.measurableEmbedding.measurableSet_image.mpr
      measurableSet_Ioo
  · rw [hrel, φ.isometry.hausdorffMeasure_image (Or.inl zero_le_one),
      MeasureTheory.hausdorffMeasure_real, Real.volume_Ioo, sub_zero]
  · rw [hseg, φ.isometry.hausdorffMeasure_image (Or.inl zero_le_one),
      MeasureTheory.hausdorffMeasure_real, Real.volume_Icc, sub_zero]

/-- Step 2 of the V4 proof of `opposite_root_edges_bound` (V4 1.21):
"`|h| = |σ^n v_{h_0}|`". An arbitrary node frame is isometric, so the measure
of its expanded edge and of its relative interior is the expanded edge length. -/
private theorem opposite_root_edges_bound_step2_cell_measure (N : FramedNode S) (n : ℕ)
    (e : {e // e ∈ (S.cx N.ty).edges}) :
    MeasurableSet (relint (N.cell n e.val)) ∧
      MeasureTheory.Measure.hausdorffMeasure 1 (relint (N.cell n e.val)) =
        ENNReal.ofReal (expandedEdgeLength n ⟨N.ty, e⟩) ∧
      MeasureTheory.Measure.hausdorffMeasure 1 (N.cell n e.val) =
        ENNReal.ofReal (expandedEdgeLength n ⟨N.ty, e⟩) := by
  let ab := Classical.choose (edge_endpoints_exist (⟨N.ty, e⟩ : EdgeName S))
  have hab : ab.1 ≠ ab.2 ∧ e.val.carrier = segment ℝ ab.1 ab.2 :=
    Classical.choose_spec (edge_endpoints_exist (⟨N.ty, e⟩ : EdgeName S))
  let f := N.prototypeFrame n
  have hseg : N.cell n e.val = segment ℝ (f ab.1) (f ab.2) := by
    change f '' e.val.carrier = _
    rw [hab.2]
    exact image_segment ℝ f.toAffineMap ab.1 ab.2
  have hlen : ‖f ab.2 - f ab.1‖ = expandedEdgeLength n ⟨N.ty, e⟩ := by
    change ‖N.frame ((S.σ ^ n) ab.2) - N.frame ((S.σ ^ n) ab.1)‖ =
      ‖(S.σ ^ n) (ab.2 - ab.1)‖
    rw [← dist_eq_norm, N.frame.isometry.dist_eq, dist_eq_norm, map_sub]
  rw [hseg, ← hlen]
  exact opposite_root_edges_bound_step1_segment_measure _ _ (fun h => hab.1 (f.injective h))

/-- P16, V4 1.21: disjoint reachable root edges at a common height inside one
edge are bounded in number by the reciprocal lower ratio. The nodes need not be
siblings or form a side-to-side patch. -/
theorem opposite_root_edges_bound (B : EdgeBounds S) (n : ℕ)
    (H : FramedNode S) (h : {e // e ∈ (S.cx H.ty).edges})
    {α : Type} [Fintype α] (t : α → FramedNode S)
    (e : ∀ a, {e // e ∈ (S.cx (t a).ty).edges})
    (hsub : ∀ a, (t a).cell n (e a).val ⊆ H.cell n h.val)
    (hdisj : Pairwise (fun a b => Disjoint
      (relint ((t a).cell n (e a).val)) (relint ((t b).cell n (e b).val))))
    (hreach : ∀ a, Relation.ReflTransGen (edgeGraph S) ⟨H.ty, h⟩ ⟨(t a).ty, e a⟩) :
    Fintype.card α ≤ oppositeRootBound B := by
  classical
  let μ : MeasureTheory.Measure (E d) := MeasureTheory.Measure.hausdorffMeasure 1
  have hmeas := fun a => opposite_root_edges_bound_step2_cell_measure (t a) n (e a)
  have hhost := (opposite_root_edges_bound_step2_cell_measure H n h).2.2
  have hfinite : ∀ a, μ (relint ((t a).cell n (e a).val)) ≠ ⊤ := by
    intro a
    change MeasureTheory.Measure.hausdorffMeasure 1 _ ≠ ⊤
    rw [(hmeas a).2.1]
    exact ENNReal.ofReal_ne_top
  have hpos : 0 < expandedEdgeLength n (⟨H.ty, h⟩ : EdgeName S) :=
    edge_ratio_bounds_step5_pos n _
  have hsum : ∑ a, expandedEdgeLength n (⟨(t a).ty, e a⟩ : EdgeName S) ≤
      expandedEdgeLength n (⟨H.ty, h⟩ : EdgeName S) := by
    calc
      _ = ∑ a, (μ (relint ((t a).cell n (e a).val))).toReal := by
        apply Finset.sum_congr rfl
        intro a _
        rw [show μ (relint ((t a).cell n (e a).val)) =
          ENNReal.ofReal (expandedEdgeLength n ⟨(t a).ty, e a⟩) from (hmeas a).2.1,
          ENNReal.toReal_ofReal (edge_ratio_bounds_step5_pos n _).le]
      _ = (μ (⋃ a ∈ (Finset.univ : Finset α), relint ((t a).cell n (e a).val))).toReal := by
        rw [MeasureTheory.measure_biUnion_finset
          (fun a _ b _ hab => hdisj hab) (fun a _ => (hmeas a).1),
          ENNReal.toReal_sum (fun a _ => hfinite a)]
      _ ≤ (μ (H.cell n h.val)).toReal := by
        apply ENNReal.toReal_mono
        · change MeasureTheory.Measure.hausdorffMeasure 1 _ ≠ ⊤
          rw [hhost]
          exact ENNReal.ofReal_ne_top
        · exact MeasureTheory.measure_mono
            (iUnion₂_subset fun a _ => intrinsicInterior_subset.trans (hsub a))
      _ = _ := by
        change (MeasureTheory.Measure.hausdorffMeasure 1 _).toReal = _
        rw [hhost, ENNReal.toReal_ofReal hpos.le]
  have hlower : ∀ a, B.lower * expandedEdgeLength n (⟨H.ty, h⟩ : EdgeName S) ≤
      expandedEdgeLength n (⟨(t a).ty, e a⟩ : EdgeName S) := by
    intro a
    exact (le_div_iff₀ hpos).mp (B.bounds _ _ (hreach a) n).1
  have hcount : (Fintype.card α : ℝ) *
      (B.lower * expandedEdgeLength n (⟨H.ty, h⟩ : EdgeName S)) ≤
      expandedEdgeLength n (⟨H.ty, h⟩ : EdgeName S) := by
    calc
      _ = ∑ _a : α, B.lower * expandedEdgeLength n (⟨H.ty, h⟩ : EdgeName S) := by simp
      _ ≤ ∑ a, expandedEdgeLength n (⟨(t a).ty, e a⟩ : EdgeName S) :=
        Finset.sum_le_sum (fun a _ => hlower a)
      _ ≤ _ := hsum
  apply Nat.le_floor
  apply (le_div_iff₀ B.lower_pos).mpr
  apply (mul_le_mul_iff_left₀ hpos).mp
  simpa only [mul_assoc, one_mul] using hcount

/-- P16, V4 1.21: the bound is positive whenever a root edge is present. -/
theorem oppositeRootBound_pos (B : EdgeBounds S) (e : EdgeName S) :
    1 ≤ oppositeRootBound B := by
  dsimp [oppositeRootBound]
  have h_bound := (B.bounds e e Relation.ReflTransGen.refl 0).1
  have h_len_pos : expandedEdgeLength 0 e ≠ 0 := by
    dsimp [expandedEdgeLength]
    intro h_eq
    have h_ne := (edgeVector_spec e).1
    have h1 : (S.σ ^ 0) (edgeVector e) = edgeVector e := rfl
    rw [h1] at h_eq
    exact h_ne (norm_eq_zero.mp h_eq)
  have h_eq : expandedEdgeLength 0 e / expandedEdgeLength 0 e = 1 := div_self h_len_pos
  rw [h_eq] at h_bound
  have h1 : 1 ≤ 1 / B.lower := one_le_div B.lower_pos |>.mpr h_bound
  exact Nat.le_floor (by exact_mod_cast h1)

end Enforce
