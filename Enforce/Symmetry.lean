import Enforce.Recognition

/-!
# Finite Euclidean symmetry groups

Y1, V4 5.6--5.7. The proof uses the intrinsic native hierarchy, general expanding
linear σ, and every Euclidean isometry, including reflections. It does not use
the geometric fitting compiler. The polyhedral stabilizer lemma Sym1 already lives
in Geometry/Polyhedral; the obligations below expose the component, torsion and
Schur steps of 5.7 separately from the final assembly.
-/

open Set Filter Topology

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d} {P : Params S}
variable {C : ClusterData S P}

namespace Symmetry

/-- Y1, V4 5.7, Step 1: the component of a parsed node is the union of all
its ancestors' closed supports. It retains arbitrarily high ancestors and does
not assume a bounded window or a single component for the whole tiling. -/
def component (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) : Set (E d) :=
  ⋃ r : ℕ, ((parsedHierarchy Y hY).ancestor q r).2.val.carrier
    ((parsedHierarchy Y hY).ancestor q r).1

/-- Y1, V4 5.7, Step 1: a translated closed solid cone lies in a component.
Closure and positive-scalar stability describe a cone; nonempty interior excludes
a lower-dimensional or empty cone. The apex is an arbitrary actual point. -/
def ContainsSolidCone (D : Set (E d)) : Prop :=
  ∃ (q : E d) (K : Set (E d)), IsClosed K ∧ (interior K).Nonempty ∧
    (∀ t : ℝ, 0 ≤ t → ∀ v ∈ K, t • v ∈ K) ∧ (fun v => q + v) '' K ⊆ D

/-- Y1, V4 5.7, Step 1: components of ground tiles coincide precisely when
they have a common ancestor. An actual ground tile supplies nonempty geometry. -/
theorem component_eq_iff (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q r : (parsedHierarchy Y hY).Node) (hq : q.1 = 0) (hr : r.1 = 0) :
    component Y hY q = component Y hY r ↔
      ∃ n : ℕ, (parsedHierarchy Y hY).ancestor q n =
        (parsedHierarchy Y hY).ancestor r n := by
  sorry

/-- Y1, V4 5.7, Step 1: different ground components have disjoint interiors. -/
theorem components_disjoint (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q r : (parsedHierarchy Y hY).Node) (hq : q.1 = 0) (hr : r.1 = 0)
    (hne : component Y hY q ≠ component Y hY r) :
    Disjoint (interior (component Y hY q)) (interior (component Y hY r)) := by
  sorry

/-- Step 1 of the V4 proof of `component_contains_cone` (V4 5.7):
"invertible linear maps preserve the given finite facet lists". More generally,
every affine image of a listed cell of dimension less than d lies in a hyperplane. -/
private theorem component_contains_cone_step1_cell_plane
    (e : Cell d) (hd : e.dim < d) (f : E d ≃ᵃ[ℝ] E d) :
    ∃ (u : E d) (b : ℝ), ‖u‖ = 1 ∧ f '' e.carrier ⊆ {x | inner ℝ u x = b} := by
  let V := (affineSpan ℝ (f '' e.carrier)).direction
  have hdim : Module.finrank ℝ V = e.dim := by
    dsimp [V]
    change Module.finrank ℝ (affineSpan ℝ (f.toAffineMap '' e.carrier)).direction = e.dim
    rw [← AffineSubspace.map_span f.toAffineMap, AffineSubspace.map_direction]
    exact (f.linear.submoduleMap (cellDirection e.carrier)).finrank_eq.symm.trans e.flat.dimension
  have htop : V ≠ ⊤ := by
    intro h
    rw [h, finrank_top, finrank_euclideanSpace, Fintype.card_fin] at hdim
    omega
  obtain ⟨u, hu, hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (mt Submodule.orthogonal_eq_bot_iff.mp htop)
  obtain ⟨p, hp⟩ := e.flat.relint_nonempty
  have hp' : p ∈ e.carrier := by
    rw [← e.flat.regularClosed]
    exact subset_closure hp
  refine ⟨‖u‖⁻¹ • u, inner ℝ (‖u‖⁻¹ • u) (f p), ?_, ?_⟩
  · simp [norm_smul, hune]
  · intro x hx
    have hsub : x - f p ∈ V := AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ _ hx) (subset_affineSpan ℝ _ ⟨p, hp', rfl⟩)
    have hz := Submodule.inner_left_of_mem_orthogonal hsub hu
    change inner ℝ (‖u‖⁻¹ • u) x = inner ℝ (‖u‖⁻¹ • u) (f p)
    rw [inner_sub_right, sub_eq_zero] at hz
    simp only [real_inner_smul_left, hz]

/-- Step 1 of the V4 proof of `component_contains_cone` (V4 5.7):
"the number of supporting hyperplanes of facets ... is at most F".
Using all listed boundary cells instead of just facets gives a uniform finite
bound as well, and does not require convexity. -/
private theorem component_contains_cone_step1_frontiers (S : SubstSystem d) :
    ∃ F : ℕ, ∀ (n : ℕ) (N : FramedNode S),
      ∃ (u : Fin F → E d) (b : Fin F → ℝ),
        (∀ j, ‖u j‖ = 1) ∧
        frontier (N.carrier n) ⊆ {x | ∃ j, inner ℝ (u j) x = b j} := by
  classical
  let J := Σ A : S.ι, CellName S A
  let eJ := Fintype.equivFin J
  refine ⟨Fintype.card J, ?_⟩
  intro n N
  have hcell (j : J) := component_contains_cone_step1_cell_plane j.2.val
    ((S.cx j.1).dim_lt j.2.val j.2.property) (N.prototypeFrame n)
  choose u b hu hsub using hcell
  refine ⟨fun j => u (eJ.symm j), fun j => b (eJ.symm j), fun j => hu _, ?_⟩
  intro x hx
  have hfront : frontier (N.carrier n) =
      N.prototypeFrame n '' frontier (S.proto N.ty).carrier := by
    have h := (N.prototypeFrame n).toHomeomorphOfFiniteDimensional.image_frontier
      (S.proto N.ty).carrier
    simpa only [FramedNode.carrier, placedSet, SubstSystem.supertile,
      FramedNode.prototypeFrame, image_image, AffineEquiv.coe_trans,
      LinearEquiv.coe_toAffineEquiv, AffineIsometryEquiv.coe_toAffineEquiv,
      Function.comp_def] using h.symm
  rw [hfront, ← (S.cx N.ty).cover] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨e, he, hy⟩ := mem_iUnion₂.mp hy
  have hy' : y ∈ e.carrier := by
    rw [← e.flat.regularClosed]
    exact subset_closure hy
  refine ⟨eJ ⟨N.ty, e, he⟩, ?_⟩
  simpa only [Equiv.symm_apply_apply] using
    hsub ⟨N.ty, e, he⟩ ⟨y, hy', rfl⟩

/-- Step 2 of the V4 proof of `component_contains_cone` (V4 5.7):
"by nestedness (A_n ⊆ A_{n+1})". The conjugated child placement commutes
with inflation, so the substitution cover implies containment at every height. -/
private theorem component_contains_cone_step2_child_subset
    (N : FramedNode S) (n : ℕ) (i : S.I N.ty) :
    (N.child n i).carrier n ⊆ N.carrier (n + 1) := by
  have hplace (x : E d) : S.placeChild n i ((S.σ ^ n) x) =
      (S.σ ^ n) ((S.child N.ty i).frame x) := by
    change linearConj S.σ (n : ℤ) (S.child N.ty i).rotation.toLinearEquiv
        ((S.σ ^ n) x) + (S.σ ^ n) (S.child N.ty i).offset =
      (S.σ ^ n) ((S.child N.ty i).rotation x + (S.child N.ty i).offset)
    simp [linearConj, zpow_neg, LinearEquiv.mul_apply]
  rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hmem : (S.child N.ty i).frame x ∈ S.σ '' (S.proto N.ty).carrier := by
    rw [S.children_cover]
    exact mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩
  obtain ⟨y, hy, he⟩ := hmem
  refine ⟨(S.σ ^ (n + 1)) y, ⟨y, hy, rfl⟩, ?_⟩
  change N.frame ((S.σ ^ (n + 1)) y) = N.frame (S.placeChild n i ((S.σ ^ n) x))
  rw [hplace, ← he, pow_succ]
  rfl

/-- Step 2 of the V4 proof of `component_contains_cone` (V4 5.7):
"by nestedness (A_n ⊆ A_{n+1})". These are the actual ancestor supports. -/
private theorem component_contains_cone_step2_nested
    {T : Tiling S} (H : CoherentHierarchy S T) (q : H.Node) :
    Monotone (fun n => (H.ancestor q n).2.val.carrier (H.ancestor q n).1) := by
  apply monotone_nat_of_le_succ
  intro n
  have he : H.ancestor q (n + 1) = H.parentNode (H.ancestor q n) :=
    Function.iterate_succ_apply' H.parentNode n q
  rw [he]
  let a := H.ancestor q n
  change a.2.val.carrier a.1 ⊆ (H.parent a.1 a.2).val.carrier (a.1 + 1)
  rw [H.child_eq a.1 a.2]
  exact component_contains_cone_step2_child_subset _ _ _

/-- Step 3 of the V4 proof of `component_contains_cone` (V4 5.7):
"C(t) contains balls of arbitrarily large radius". Strict expansion is used
only here; the centres may depend on the radius. -/
private theorem component_contains_cone_step3_inballs
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : q.1 = 0) :
    ∀ R : ℝ, 0 < R → ∃ v : E d, Metric.ball v R ⊆ component Y hY q := by
  classical
  letI : Nonempty S.ι := ⟨q.2.val.ty⟩
  have hproto (A : S.ι) : ∃ (v : E d) (r : ℝ), 0 < r ∧
      Metric.ball v r ⊆ (S.proto A).carrier := by
    obtain ⟨v, hv⟩ := (S.proto A).interior_nonempty
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior v hv
    exact ⟨v, r, hr, hball.trans interior_subset⟩
  choose centre radius hpos hball using hproto
  let ρ : ℝ := Finset.univ.inf' Finset.univ_nonempty radius
  have hρ : 0 < ρ := (Finset.lt_inf'_iff _).mpr (fun A _ => hpos A)
  have hρle (A : S.ι) : ρ ≤ radius A := Finset.inf'_le radius (Finset.mem_univ A)
  have hc : 0 < S.c := lt_trans zero_lt_one S.c_gt_one
  have hexpand (n : ℕ) (x : E d) : S.c ^ n * ‖x‖ ≤ ‖(S.σ ^ n) x‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        S.c ^ (n + 1) * ‖x‖ = S.c * (S.c ^ n * ‖x‖) := by ring
        _ ≤ S.c * ‖(S.σ ^ n) x‖ := mul_le_mul_of_nonneg_left ih hc.le
        _ ≤ ‖S.σ ((S.σ ^ n) x)‖ := S.expand _
        _ = ‖(S.σ ^ (n + 1)) x‖ := by rw [pow_succ']; rfl
  have hinball (n : ℕ) (N : FramedNode S) :
      Metric.ball (N.frame ((S.σ ^ n) (centre N.ty))) (ρ * S.c ^ n) ⊆ N.carrier n := by
    intro z hz
    let w := (S.σ ^ n).symm (N.frame.symm z)
    have hw : (S.σ ^ n) (w - centre N.ty) =
        N.frame.symm z - (S.σ ^ n) (centre N.ty) := by simp [w]
    have hdist : ‖(S.σ ^ n) (w - centre N.ty)‖ < ρ * S.c ^ n := by
      rw [hw, ← dist_eq_norm]
      rw [← N.frame.isometry.dist_eq, N.frame.apply_symm_apply]
      exact hz
    have hsmall : ‖w - centre N.ty‖ < ρ := by
      have := lt_of_le_of_lt (hexpand n (w - centre N.ty)) hdist
      nlinarith [pow_pos hc n]
    have hmem : w ∈ (S.proto N.ty).carrier :=
      hball N.ty (lt_of_lt_of_le hsmall (hρle N.ty))
    exact ⟨N.frame.symm z, ⟨w, hmem, by simp [w]⟩, N.frame.apply_symm_apply z⟩
  intro R hR
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / ρ) S.c_gt_one
  have hRn : R < ρ * S.c ^ n := by
    have := (div_lt_iff₀ hρ).mp hn
    nlinarith
  let a := (parsedHierarchy Y hY).ancestor q n
  have ha : a.1 = n := by
    have hheight (k : ℕ) : ((parsedHierarchy Y hY).ancestor q k).1 = q.1 + k := by
      induction k with
      | zero => rfl
      | succ k ih =>
        change (((parsedHierarchy Y hY).parentNode^[k + 1]) q).1 = _
        rw [Function.iterate_succ_apply']
        change ((parsedHierarchy Y hY).ancestor q k).1 + 1 = q.1 + (k + 1)
        omega
    simpa [a, hq] using hheight n
  refine ⟨a.2.val.frame ((S.σ ^ a.1) (centre a.2.val.ty)), ?_⟩
  apply Subset.trans (Metric.ball_subset_ball (show R ≤ ρ * S.c ^ a.1 by simpa [ha] using hRn.le))
  exact (hinball a.1 a.2.val).trans (subset_iUnion_of_subset n Subset.rfl)

/-- Step 4 of the V4 proof of `component_contains_cone` (V4 5.7):
"membership ... is constant on each chamber of the arrangement".
The chamber is convex and avoids the frontier, so it lies entirely in the
interior of the set or entirely in the interior of its complement. -/
private theorem component_contains_cone_step4_same_chamber
    (A : Set (E d)) {m : ℕ} (u : Fin m → E d) (b : Fin m → ℝ)
    (hplanes : frontier A ⊆ {x | ∃ j, inner ℝ (u j) x = b j})
    (x y : E d)
    (hxy : ∀ j, 0 < (inner ℝ (u j) x - b j) * (inner ℝ (u j) y - b j)) :
    (x ∈ A ↔ y ∈ A) := by
  let a : Fin m → ℝ := fun j => inner ℝ (u j) x - b j
  let Ω : Set (E d) := {z | ∀ j, 0 < a j * (inner ℝ (u j) z - b j)}
  have hx : x ∈ Ω := by
    intro j
    have ha : a j ≠ 0 := by
      intro ha
      have h := hxy j
      change 0 < a j * _ at h
      simp [ha] at h
    exact mul_self_pos.mpr ha
  have hy : y ∈ Ω := hxy
  have hconv : Convex ℝ Ω := by
    intro p hp q hq s t hs ht hst j
    change 0 < a j * (inner ℝ (u j) (s • p + t • q) - b j)
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have h1 := hp j
    have h2 := hq j
    have hpos : 0 < s * (a j * (inner ℝ (u j) p - b j)) +
        t * (a j * (inner ℝ (u j) q - b j)) := by
      rcases lt_or_eq_of_le hs with hs | rfl
      · exact add_pos_of_pos_of_nonneg (mul_pos hs h1) (mul_nonneg ht h2.le)
      · simp only [zero_add] at hst
        simp [hst, h2]
    calc
      0 < s * (a j * (inner ℝ (u j) p - b j)) +
          t * (a j * (inner ℝ (u j) q - b j)) := hpos
      _ = a j * (s * inner ℝ (u j) p + t * inner ℝ (u j) q - (s + t) * b j) := by ring
      _ = a j * (s * inner ℝ (u j) p + t * inner ℝ (u j) q - b j) := by rw [hst, one_mul]
  have hcover : Ω ⊆ interior A ∪ interior Aᶜ := by
    rw [← compl_frontier_eq_union_interior]
    intro z hz hf
    obtain ⟨j, hj⟩ := hplanes hf
    have h := hz j
    simp [hj] at h
  have hdisj : Disjoint (interior A) (interior Aᶜ) :=
    disjoint_left.mpr fun z hz hz' => (interior_subset hz') (interior_subset hz)
  rcases hconv.isPreconnected.subset_or_subset isOpen_interior isOpen_interior hdisj hcover with h | h
  · exact iff_of_true (interior_subset (h hx)) (interior_subset (h hy))
  · exact iff_of_false (interior_subset (h hx)) (interior_subset (h hy))

/-- Step 4 of the V4 proof of `component_contains_cone` (V4 5.7):
"off finitely many hyperplanes, C(t) is a union of chambers of a finite
hyperplane arrangement". This is a compactness statement for an increasing
sequence of sets with a uniformly bounded number of boundary planes;
it makes no inball or cone assumption. -/
private theorem component_contains_cone_step4_limit_chambers
    (A : ℕ → Set (E d)) (hmono : Monotone A)
    (F : ℕ)
    (hplanes : ∀ n, ∃ (u : Fin F → E d) (b : Fin F → ℝ),
      (∀ j, ‖u j‖ = 1) ∧ frontier (A n) ⊆ {x | ∃ j, inner ℝ (u j) x = b j}) :
    ∃ (m : ℕ) (u : Fin m → E d) (b : Fin m → ℝ),
      (∀ j, ‖u j‖ = 1) ∧
      ∀ x y : E d,
        (∀ j, 0 < (inner ℝ (u j) x - b j) * (inner ℝ (u j) y - b j)) →
        (x ∈ ⋃ n, A n ↔ y ∈ ⋃ n, A n) := by
  classical
  choose u b hu hboundary using hplanes
  -- Normalizing the entire affine coefficient pair compactifies also the planes
  -- whose offsets escape to infinity. A limit with zero normal is a nonzero constant.
  let p : ℕ → Fin F → E d × ℝ := fun n j =>
    ‖(u n j, b n j)‖⁻¹ • (u n j, b n j)
  have hpair (n : ℕ) (j : Fin F) : (u n j, b n j) ≠ 0 := by
    intro h
    have hz := congrArg Prod.fst h
    change u n j = 0 at hz
    have := hu n j
    simp [hz] at this
  have hp (n : ℕ) (j : Fin F) : ‖p n j‖ = 1 := by
    dsimp only [p]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hpair n j))]
  have hcompact : IsCompact (Set.univ.pi (fun _ : Fin F =>
      Metric.sphere (0 : E d × ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_sphere _ _
  obtain ⟨p₀, hp₀, φ, hφ, hlim⟩ := hcompact.tendsto_subseq (x := p)
    (fun n j _ => by simpa only [Metric.mem_sphere, dist_zero_right] using hp n j)
  have hunit (j : Fin F) : ‖p₀ j‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hp₀ j (mem_univ j)
  have hpn (n : ℕ) : frontier (A n) ⊆
      {x | ∃ j, inner ℝ (p n j).1 x = (p n j).2} := by
    intro x hx
    obtain ⟨j, hj⟩ := hboundary n hx
    exact ⟨j, by simp [p, inner_smul_left, hj]⟩
  let J := {j : Fin F // (p₀ j).1 ≠ 0}
  let eJ := Fintype.equivFin J
  let v : J → E d := fun j => ‖(p₀ j.val).1‖⁻¹ • (p₀ j.val).1
  let c : J → ℝ := fun j => ‖(p₀ j.val).1‖⁻¹ * (p₀ j.val).2
  refine ⟨Fintype.card J, fun j => v (eJ.symm j), fun j => c (eJ.symm j), ?_, ?_⟩
  · intro j
    simp [v, norm_smul, (eJ.symm j).property]
  · intro x y hxy
    have hsign (j : Fin F) :
        0 < (inner ℝ (p₀ j).1 x - (p₀ j).2) *
          (inner ℝ (p₀ j).1 y - (p₀ j).2) := by
      by_cases hj : (p₀ j).1 = 0
      · have hb : (p₀ j).2 ≠ 0 := by
          intro hb
          have hz : p₀ j = 0 := Prod.ext hj hb
          have := hunit j
          simp [hz] at this
        simpa [hj] using mul_self_pos.mpr hb
      · have h := hxy (eJ ⟨j, hj⟩)
        simp only [Equiv.symm_apply_apply] at h
        have he (z : E d) : inner ℝ (v ⟨j, hj⟩) z - c ⟨j, hj⟩ =
            ‖(p₀ j).1‖⁻¹ * (inner ℝ (p₀ j).1 z - (p₀ j).2) := by
          simp only [v, c, real_inner_smul_left]
          ring
        rw [he x, he y, mul_mul_mul_comm] at h
        exact (mul_pos_iff_of_pos_left (mul_pos (inv_pos.mpr (norm_pos_iff.mpr hj))
          (inv_pos.mpr (norm_pos_iff.mpr hj)))).mp h
    have heval (j : Fin F) (z : E d) :
        Tendsto (fun n => inner ℝ (p (φ n) j).1 z - (p (φ n) j).2)
          atTop (𝓝 (inner ℝ (p₀ j).1 z - (p₀ j).2)) := by
      have h : Tendsto (fun n => p (φ n) j) atTop (𝓝 (p₀ j)) :=
        ((continuous_apply j).tendsto p₀).comp hlim
      exact (((continuous_fst.tendsto _).comp h).inner tendsto_const_nhds).sub
        ((continuous_snd.tendsto _).comp h)
    have hevent : ∀ᶠ n in atTop, x ∈ A (φ n) ↔ y ∈ A (φ n) := by
      have hprod : ∀ᶠ n in atTop, ∀ j,
          0 < (inner ℝ (p (φ n) j).1 x - (p (φ n) j).2) *
            (inner ℝ (p (φ n) j).1 y - (p (φ n) j).2) := by
        apply eventually_all.mpr
        intro j
        exact ((heval j x).mul (heval j y)).eventually (isOpen_Ioi.mem_nhds (hsign j))
      filter_upwards [hprod] with n hn
      exact component_contains_cone_step4_same_chamber (A (φ n))
        (fun j => (p (φ n) j).1) (fun j => (p (φ n) j).2) (hpn (φ n)) x y hn
    constructor
    · intro hx
      obtain ⟨N, hN⟩ := mem_iUnion.mp hx
      obtain ⟨n, hn, hxy'⟩ := ((hφ.tendsto_atTop.eventually_ge_atTop N).and hevent).exists
      exact mem_iUnion.mpr ⟨φ n, hxy'.mp (hmono hn hN)⟩
    · intro hy
      obtain ⟨N, hN⟩ := mem_iUnion.mp hy
      obtain ⟨n, hn, hxy'⟩ := ((hφ.tendsto_atTop.eventually_ge_atTop N).and hevent).exists
      exact mem_iUnion.mpr ⟨φ n, hxy'.mpr (hmono hn hN)⟩

/-- Step 5 of the V4 proof of `component_contains_cone` (V4 5.7):
"some sub-ball ... avoids all of them". For one plane, moving half a radius
in the normal direction leaves a quarter-radius ball strictly on one side. -/
private theorem component_contains_cone_step5_one_plane
    (u : E d) (b : ℝ) (hu : ‖u‖ = 1) (x : E d) (R : ℝ) (hR : 0 < R) :
    ∃ v, Metric.ball v (R / 4) ⊆ Metric.ball x R ∧
      ∀ z ∈ Metric.ball v (R / 4), inner ℝ u z ≠ b := by
  have hone (u : E d) (b : ℝ) (hu : ‖u‖ = 1) (hx : b ≤ inner ℝ u x) :
      ∃ v, Metric.ball v (R / 4) ⊆ Metric.ball x R ∧
        ∀ z ∈ Metric.ball v (R / 4), b < inner ℝ u z := by
    let v := x + (R / 2) • u
    have hv : dist v x = R / 2 := by
      simp [v, dist_eq_norm, norm_smul, hu, abs_of_pos hR]
    refine ⟨v, ?_, ?_⟩
    · intro z hz
      have := dist_triangle z v x
      rw [Metric.mem_ball] at hz ⊢
      linarith
    · intro z hz
      have hb := abs_real_inner_le_norm u (z - v)
      rw [hu, one_mul] at hb
      have hd : ‖z - v‖ < R / 4 := hz
      have hl := neg_abs_le (inner ℝ u (z - v))
      have hv' : inner ℝ u v = inner ℝ u x + R / 2 := by
        simp [v, inner_add_right, inner_smul_right, hu]
      rw [inner_sub_right, hv'] at hb hl
      linarith
  rcases le_total b (inner ℝ u x) with hx | hx
  · obtain ⟨v, hsub, hside⟩ := hone u b hu hx
    exact ⟨v, hsub, fun z hz => ne_of_gt (hside z hz)⟩
  · obtain ⟨v, hsub, hside⟩ := hone (-u) (-b) (by simpa using hu) (by simpa using hx)
    refine ⟨v, hsub, ?_⟩
    intro z hz he
    have := hside z hz
    simp [inner_neg_left, he] at this

/-- Step 5 of the V4 proof of `component_contains_cone` (V4 5.7):
"some sub-ball of radius ε_F R avoids all of them". Iterating the elementary
quarter-ball construction proves the uniform estimate without a volume argument. -/
private theorem component_contains_cone_step5_subball
    {m : ℕ} (u : Fin m → E d) (b : Fin m → ℝ) (hu : ∀ j, ‖u j‖ = 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x : E d) (R : ℝ), 0 < R →
      ∃ v, Metric.ball v (ε * R) ⊆ Metric.ball x R ∧
        ∀ j z, z ∈ Metric.ball v (ε * R) → inner ℝ (u j) z ≠ b j := by
  classical
  have hfinite (J : Finset (Fin m)) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ (x : E d) (R : ℝ), 0 < R →
        ∃ v, Metric.ball v (ε * R) ⊆ Metric.ball x R ∧
          ∀ j ∈ J, ∀ z ∈ Metric.ball v (ε * R), inner ℝ (u j) z ≠ b j := by
    induction J using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, fun x R _ => ⟨x, by simp, by simp⟩⟩
    | @insert j J hj ih =>
      obtain ⟨ε, hε, hεball⟩ := ih
      refine ⟨ε / 4, by positivity, ?_⟩
      intro x R hR
      obtain ⟨v, hv, hplanes⟩ := hεball x R hR
      obtain ⟨w, hw, hnew⟩ := component_contains_cone_step5_one_plane
        (u j) (b j) (hu j) v (ε * R) (mul_pos hε hR)
      have he : ε / 4 * R = ε * R / 4 := by ring
      refine ⟨w, ?_, ?_⟩
      · rw [he]
        exact hw.trans hv
      · intro k hk z hz
        rw [he] at hz
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hnew z hz
        · exact hplanes k hk z (hw hz)
  obtain ⟨ε, hε, h⟩ := hfinite Finset.univ
  exact ⟨ε, hε, fun x R hR => (h x R hR).imp fun v hv =>
    ⟨hv.1, fun j z hz => hv.2 j (Finset.mem_univ j) z hz⟩⟩

/-- Step 5 of the V4 proof of `component_contains_cone` (V4 5.7):
"some sub-ball ... avoids all of them" and "u_j · v > 0 for all j".
A sufficiently large ball supplies a point whose affine and homogeneous signs
agree for every plane. Empty arrangements are allowed. -/
private theorem component_contains_cone_step5_escape
    {D : Set (E d)} (hballs : ∀ R : ℝ, 0 < R → ∃ v, Metric.ball v R ⊆ D)
    {m : ℕ} (u : Fin m → E d) (b : Fin m → ℝ) (hu : ∀ j, ‖u j‖ = 1) :
    ∃ v ∈ D, ∀ j, 0 < (inner ℝ (u j) v - b j) * inner ℝ (u j) v := by
  classical
  obtain ⟨ε, hε, hsubball⟩ := component_contains_cone_step5_subball u b hu
  let B : ℝ := (∑ j, |b j|) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨x, hx⟩ := hballs (B / ε) (div_pos hB hε)
  obtain ⟨v, hv, hplanes⟩ := hsubball x (B / ε) (div_pos hB hε)
  have he : ε * (B / ε) = B := by field_simp
  rw [he] at hv hplanes
  refine ⟨v, hx (hv (Metric.mem_ball_self hB)), ?_⟩
  intro j
  have hmargin : B ≤ |inner ℝ (u j) v - b j| := by
    by_contra! hlt
    let z := v - (inner ℝ (u j) v - b j) • u j
    have hz : z ∈ Metric.ball v B := by
      simpa [z, dist_eq_norm, norm_smul, hu j] using hlt
    have hzero : inner ℝ (u j) z = b j := by
      simp [z, inner_sub_right, inner_smul_right, hu j]
    exact hplanes j z hz hzero
  have hbj : |b j| < B := by
    have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => abs_nonneg (b k))
      (Finset.mem_univ j)
    dsimp [B]
    linarith
  have habs := hbj.trans_le hmargin
  rcases le_total 0 (inner ℝ (u j) v - b j) with h | h
  · rw [abs_of_nonneg h] at habs
    exact mul_pos (by linarith [abs_nonneg (b j)]) (by linarith [neg_le_abs (b j)])
  · rw [abs_of_nonpos h] at habs
    exact mul_pos_of_neg_of_neg (by linarith [abs_nonneg (b j)]) (by linarith [le_abs_self (b j)])

/-- Step 6 of the V4 proof of `component_contains_cone` (V4 5.7):
"q + K ⊆ Ω for every q ∈ Ω". The closed homogeneous half-spaces already
give a solid cone when there is a direction satisfying every inequality strictly. -/
private theorem component_contains_cone_step6_cone
    {D : Set (E d)} {m : ℕ} (u : Fin m → E d) (b : Fin m → ℝ)
    (hchamber : ∀ x y : E d,
      (∀ j, 0 < (inner ℝ (u j) x - b j) * (inner ℝ (u j) y - b j)) →
      (x ∈ D ↔ y ∈ D))
    (v : E d) (hv : v ∈ D)
    (hdir : ∀ j, 0 < (inner ℝ (u j) v - b j) * inner ℝ (u j) v) :
    ContainsSolidCone D := by
  let a : Fin m → ℝ := fun j => inner ℝ (u j) v - b j
  let K : Set (E d) := {w | ∀ j, 0 ≤ a j * inner ℝ (u j) w}
  have hcont (j : Fin m) : Continuous (fun w : E d => a j * inner ℝ (u j) w) :=
    continuous_const.mul (continuous_const.inner continuous_id)
  refine ⟨v, K, ?_, ?_, ?_, ?_⟩
  · simpa only [K, setOf_forall] using
      (isClosed_iInter fun j => isClosed_le continuous_const (hcont j))
  · have hopen : IsOpen {w : E d | ∀ j, 0 < a j * inner ℝ (u j) w} := by
      simpa only [setOf_forall] using
        (isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (hcont j))
    have hsub : {w : E d | ∀ j, 0 < a j * inner ℝ (u j) w} ⊆ K :=
      fun w hw j => (hw j).le
    refine ⟨v, interior_mono hsub ?_⟩
    rw [hopen.interior_eq]
    exact hdir
  · intro t ht w hw j
    change 0 ≤ a j * inner ℝ (u j) (t • w)
    rw [inner_smul_right]
    nlinarith [mul_nonneg ht (hw j)]
  · rintro _ ⟨w, hw, rfl⟩
    apply (hchamber v (v + w) ?_).mp hv
    intro j
    have ha : a j ≠ 0 := by
      intro ha
      have h := hdir j
      change 0 < a j * _ at h
      simp [ha] at h
    have hs : 0 < (a j) ^ 2 := sq_pos_of_ne_zero ha
    have hk := hw j
    change 0 < a j * (inner ℝ (u j) (v + w) - b j)
    rw [inner_add_right]
    dsimp [a] at *
    nlinarith

/-- Y1, V4 5.7, Step 1: every ground component contains a translated solid cone.
The bounded number of facet hyperplanes and strict expansion apply to anisotropic
σ as well; convexity of the prototypes or components is not assumed. -/
theorem component_contains_cone (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : q.1 = 0) :
    ContainsSolidCone (component Y hY q) := by
  let H := parsedHierarchy Y hY
  let A : ℕ → Set (E d) := fun n => (H.ancestor q n).2.val.carrier (H.ancestor q n).1
  obtain ⟨F, hF⟩ := component_contains_cone_step1_frontiers S
  obtain ⟨m, u, b, hu, hchamber⟩ := component_contains_cone_step4_limit_chambers
    A (component_contains_cone_step2_nested H q) F
    (fun n => hF (H.ancestor q n).1 (H.ancestor q n).2.val)
  obtain ⟨v, hv, hdir⟩ := component_contains_cone_step5_escape
    (component_contains_cone_step3_inballs Y hY q hq) u b hu
  exact component_contains_cone_step6_cone u b hchamber v hv hdir

/-- Step 1 of the V4 proof of `power_fixes_component` (V4 5.7, Step 2):
"Write g(x)=Rx+τ". The orthogonal part of a product of isometries is the
product of their orthogonal parts. -/
private theorem power_fixes_component_step1_linear_mul (e e' : Iso d) (v : E d) :
    (e * e').linearIsometryEquiv v =
      e.linearIsometryEquiv (e'.linearIsometryEquiv v) := by
  have h1 := (e * e').map_vsub v 0
  have h2 := e'.map_vsub v 0
  have h3 := e.map_vsub (e' v) (e' 0)
  simp only [vsub_eq_sub, sub_zero, AffineIsometryEquiv.coe_mul,
    Function.comp_apply] at h1 h2 h3
  rw [h1, h2, h3]

/-- Step 2 of the V4 proof of `power_fixes_component` (V4 5.7, Step 2):
"The powers of R in the compact group O(d) have a subsequence converging to the
identity, so some R^k (k ≥ 1) is close enough to I". Here only the orbit of one
direction is needed: it lies in a compact sphere. -/
private theorem power_fixes_component_step2_recurrence (g : Iso d) (w : E d)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, 1 ≤ k ∧ ‖(g ^ k).linearIsometryEquiv w - w‖ < δ := by
  let a : ℕ → E d := fun n => (g ^ n).linearIsometryEquiv w
  have ha : ∀ n, a n ∈ Metric.closedBall (0 : E d) ‖w‖ := by
    intro n
    simp [a, Metric.mem_closedBall, dist_zero_right]
  obtain ⟨b, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : E d) ‖w‖).tendsto_subseq ha
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq δ hδ
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  refine ⟨φ (N + 1) - φ N, by omega, ?_⟩
  have hd := hN (N + 1) (Nat.le_succ N)
  have hsplit : g ^ φ (N + 1) = g ^ φ N * g ^ (φ (N + 1) - φ N) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [Function.comp_apply, a, hsplit, power_fixes_component_step1_linear_mul,
    dist_eq_norm] at hd
  rw [← map_sub, LinearIsometryEquiv.norm_map] at hd
  exact hd

/-- Step 3 of the V4 proof of `power_fixes_component` (V4 5.7): "g maps nodes to
nodes of the same height; it preserves containment, hence parents". -/
private theorem power_fixes_component_step3_parent_move
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) (h : Iso d)
    (hh : Y.IsSymmetry h) (n : ℕ) (a b : {N // N ∈ (parsedHierarchy Y hY).nodes n})
    (hab : b.val = a.val.move h) :
    ((parsedHierarchy Y hY).parent n b).val =
      ((parsedHierarchy Y hY).parent n a).val.move h := by
  symm
  refine (parsedHierarchy Y hY).parent_unique n b _
    (parsed_node_move_mem Y hY h hh (n + 1) _ ((parsedHierarchy Y hY).parent n a).property)
    ⟨(parsedHierarchy Y hY).role n a, ?_⟩
  rw [hab]
  conv_lhs => rw [(parsedHierarchy Y hY).child_eq n a]
  exact FramedNode.move_child _ _ _ _

/-- Step 4 of the V4 proof of `power_fixes_component` (V4 5.7, Step 2):
"g^k maps the ancestor chain of t to that of g^k t". -/
private theorem power_fixes_component_step4_ancestor_move
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) (h : Iso d)
    (hh : Y.IsSymmetry h) (q q' : (parsedHierarchy Y hY).Node) (h1 : q'.1 = q.1)
    (h2 : q'.2.val = q.2.val.move h) (r : ℕ) :
    ((parsedHierarchy Y hY).ancestor q' r).1 = ((parsedHierarchy Y hY).ancestor q r).1 ∧
      ((parsedHierarchy Y hY).ancestor q' r).2.val =
        ((parsedHierarchy Y hY).ancestor q r).2.val.move h := by
  induction r with
  | zero => exact ⟨h1, h2⟩
  | succ r ih =>
    obtain ⟨i1, i2⟩ := ih
    simp only [CoherentHierarchy.ancestor] at i1 i2 ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    generalize (parsedHierarchy Y hY).parentNode^[r] q' = A at i1 i2 ⊢
    generalize (parsedHierarchy Y hY).parentNode^[r] q = B at i1 i2 ⊢
    obtain ⟨m, A⟩ := A
    obtain ⟨n, B⟩ := B
    simp only at i1 i2
    subst i1
    exact ⟨rfl, power_fixes_component_step3_parent_move Y hY h hh m B A i2⟩

/-- Step 5 of the V4 proof of `power_fixes_component` (V4 5.7, Step 2):
"g^k C(t) is the component of g^k t". -/
private theorem power_fixes_component_step5_component_move
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) (h : Iso d)
    (hh : Y.IsSymmetry h) (q q' : (parsedHierarchy Y hY).Node) (h1 : q'.1 = q.1)
    (h2 : q'.2.val = q.2.val.move h) :
    component Y hY q' = h '' component Y hY q := by
  simp only [component, Set.image_iUnion]
  refine Set.iUnion_congr fun r => ?_
  obtain ⟨e1, e2⟩ := power_fixes_component_step4_ancestor_move Y hY h hh q q' h1 h2 r
  generalize (parsedHierarchy Y hY).ancestor q' r = A at e1 e2 ⊢
  generalize (parsedHierarchy Y hY).ancestor q r = B at e1 e2 ⊢
  obtain ⟨m, A⟩ := A
  obtain ⟨n, B⟩ := B
  simp only at e1 e2 ⊢
  subst e1
  rw [e2]
  simp only [FramedNode.carrier, FramedNode.move, placedSet,
    AffineIsometryEquiv.coe_trans, Set.image_comp]

/-- Y1, V4 5.7, Step 2: a positive power of any symmetry fixes a ground component.
Compact recurrence of its orthogonal part produces intersecting solid cones;
translations of the cone apices do not affect the large-distance intersection. -/
theorem power_fixes_component (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Iso d) (hg : Y.IsSymmetry g) (q : (parsedHierarchy Y hY).Node)
    (hq : q.1 = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ (g ^ k) '' component Y hY q = component Y hY q := by
  obtain ⟨p, K, -, ⟨w, hw⟩, hcone, hsub⟩ := component_contains_cone Y hY q hq
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hw)
  obtain ⟨k, hk, hrec⟩ :=
    power_fixes_component_step2_recurrence g w (by positivity : (0 : ℝ) < ε / 4)
  refine ⟨k, hk, ?_⟩
  set h := g ^ k with hh_def
  have hh : Y.IsSymmetry h :=
    (Y.mem_symmetryGroup h).1 (Subgroup.pow_mem _ ((Y.mem_symmetryGroup g).2 hg) k)
  let q' : (parsedHierarchy Y hY).Node :=
    ⟨q.1, ⟨q.2.val.move h, parsed_node_move_mem Y hY h hh q.1 q.2.val q.2.property⟩⟩
  have hcomp : component Y hY q' = h '' component Y hY q :=
    power_fixes_component_step5_component_move Y hY h hh q q' rfl rfl
  rw [← hcomp]
  by_contra hne
  have hdis := components_disjoint Y hY q q' hq hq (fun e => hne e.symm)
  set L := h.linearIsometryEquiv
  set c := dist p (h p) with hc
  have hc0 : 0 ≤ c := dist_nonneg
  set s : ℝ := 4 * (c + 1) / ε with hs_def
  have hs : 0 < s := by positivity
  have hsε : s * ε = 4 * (c + 1) := by
    rw [hs_def]
    field_simp
  set x0 : E d := p + s • w with hx0_def
  have hx0 : h x0 = s • L w + h p := by
    have : x0 = (s • w) +ᵥ p := by rw [vadd_eq_add, add_comm]
    rw [this, h.map_vadd, vadd_eq_add, map_smul]
  have hdist : dist x0 (h x0) < s * ε / 2 := by
    rw [dist_eq_norm, hx0]
    have e : p + s • w - (s • L w + h p) = (p - h p) - s • (L w - w) := by
      rw [smul_sub]
      abel
    rw [e]
    calc ‖(p - h p) - s • (L w - w)‖ ≤ ‖p - h p‖ + ‖s • (L w - w)‖ := norm_sub_le _ _
      _ = c + s * ‖L w - w‖ := by
        rw [norm_smul, Real.norm_of_nonneg hs.le, ← dist_eq_norm]
      _ < c + s * (ε / 4) := by gcongr
      _ ≤ s * ε / 2 := by nlinarith
  have hB : Metric.ball x0 (s * ε) ⊆ component Y hY q := by
    intro z hz
    rw [Metric.mem_ball] at hz
    have hv : s⁻¹ • (z - p) ∈ K := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have e : s⁻¹ • (z - x0) = s⁻¹ • (z - p) - w := by
        rw [show z - x0 = (z - p) - s • w by rw [hx0_def]; abel, smul_sub, smul_smul,
          inv_mul_cancel₀ hs.ne', one_smul]
      rw [← e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), ← dist_eq_norm,
        inv_mul_lt_iff₀ hs]
      linarith
    have hv' := hcone s hs.le _ hv
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul] at hv'
    exact hsub ⟨z - p, hv', by simp⟩
  have hx1 : x0 ∈ interior (component Y hY q) :=
    mem_interior.2 ⟨_, hB, Metric.isOpen_ball, Metric.mem_ball_self (by positivity)⟩
  have hB' : Metric.ball x0 (s * ε / 2) ⊆ component Y hY q' := by
    intro z hz
    rw [Metric.mem_ball] at hz
    rw [hcomp]
    refine ⟨h.symm z, hB ?_, h.apply_symm_apply z⟩
    rw [Metric.mem_ball, ← h.dist_map, h.apply_symm_apply]
    linarith [dist_triangle z x0 (h x0)]
  have hx2 : x0 ∈ interior (component Y hY q') :=
    mem_interior.2 ⟨_, hB', Metric.isOpen_ball, Metric.mem_ball_self (by positivity)⟩
  exact Set.disjoint_left.1 hdis hx1 hx2

/-- Y1, V4 5.7, Step 3: a positive power of any symmetry preserves an actual
bounded full-dimensional hierarchy node. Common ancestry is obtained from the
component argument; no finite-order hypothesis is inserted here. -/
theorem power_fixes_node (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Iso d) (hg : Y.IsSymmetry g) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ (n : ℕ) (N : FramedNode S),
      N ∈ (parsedHierarchy Y hY).nodes n ∧ (g ^ k) '' N.carrier n = N.carrier n := by
  sorry

/-- Y1/Sym1, V4 5.6, 5.7: every placed node is a full-dimensional polyhedron.
Invertible linear powers of σ and arbitrary isometric frames preserve these facts. -/
theorem node_polyhedron_full (n : ℕ) (N : FramedNode S) :
    Polyhedron (N.carrier n) ∧ (interior (N.carrier n)).Nonempty := by
  sorry

/-- Y1/Sym1, V4 5.6: the full setwise stabilizer of a node is finite. -/
theorem node_stabilizer_finite (n : ℕ) (N : FramedNode S) :
    {g : Iso d | g '' N.carrier n = N.carrier n}.Finite :=
  polyhedron_symmetries_finite _ (node_polyhedron_full n N).1
    (node_polyhedron_full n N).2

/-- Y1/Sym1, V4 5.6, 5.7, Step 3: any isometry preserving a node has finite order.
This is the group-theoretic consequence of its finite setwise stabilizer. -/
theorem finite_order_of_fixes_node (n : ℕ) (N : FramedNode S) (g : Iso d)
    (hg : g '' N.carrier n = N.carrier n) : IsOfFinOrder g := by
  have h_stab_fin : {h : Iso d | h '' N.carrier n = N.carrier n}.Finite :=
    node_stabilizer_finite n N
  have h_pow_mem : ∀ k : ℕ, (g ^ k) '' N.carrier n = N.carrier n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, AffineIsometryEquiv.coe_mul, Set.image_comp, hg, ih]
  have h_pow_in_stab : ∀ k : ℕ, g ^ k ∈ {h : Iso d | h '' N.carrier n = N.carrier n} := h_pow_mem
  have h_not_inj : ¬ Function.Injective (fun k : ℕ => g ^ k) := by
    intro h_inj
    have h_inf := Set.infinite_range_of_injective h_inj
    have h_sub : Set.range (fun k : ℕ => g ^ k) ⊆ {h : Iso d | h '' N.carrier n = N.carrier n} := by
      rintro _ ⟨k, rfl⟩
      exact h_pow_in_stab k
    have h_fin := Set.Finite.subset h_stab_fin h_sub
    exact h_inf h_fin
  rw [Function.Injective] at h_not_inj
  push_neg at h_not_inj
  obtain ⟨a, b, hab, hneq⟩ := h_not_inj
  wlog hlt : a < b generalizing a b
  · rcases lt_or_eq_of_le (not_lt.mp hlt) with hlt' | heq
    · exact this b a hab.symm hneq.symm hlt'
    · exact False.elim (hneq heq.symm)
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨b - a, by omega, by
      have h_eq : g ^ a * g ^ (b - a) = g ^ a * 1 := by
        calc g ^ a * g ^ (b - a) = g ^ (a + (b - a)) := (pow_add g a (b - a)).symm
          _ = g ^ b := by rw [add_tsub_cancel_of_le (by omega)]
          _ = g ^ a := hab.symm
          _ = g ^ a * 1 := (mul_one (g ^ a)).symm
      exact mul_left_cancel h_eq⟩

/-- Y1, V4 5.7, Steps 1--3: every symmetry is periodic, before the group finiteness
argument. A positive power preserves a node and lies in its finite stabilizer. -/
theorem periodic (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Iso d) (hg : Y.IsSymmetry g) : IsOfFinOrder g := by
  obtain ⟨k, hk, n, N, _, hfix⟩ := power_fixes_node Y hY g hg
  have hp := finite_order_of_fixes_node n N (g ^ k) hfix
  rcases isOfFinOrder_pow.mp hp with h | h
  · exact h
  · omega

/-- Y1, V4 5.7, Step 4(i): the tile-and-marking symmetry group is countable.
The stronger local statement is discreteness: the labelled frame marker in one
tile isolates the identity. This countability consequence is used in Step 4(iii). -/
theorem symmetry_countable (Y : MarkedTiling (systemM S P C)) :
    Countable Y.symmetryGroup := by
  sorry

/-- Y1, V4 5.7, Step 4(ii): every finitely generated subgroup is finite. -/
def IsLocallyFiniteGroup (G : Subgroup (Iso d)) : Prop :=
  ∀ F : Finset (Iso d), (F : Set (Iso d)) ⊆ G →
    (Subgroup.closure (F : Set (Iso d)) : Set (Iso d)).Finite

section Schur

open Polynomial IntermediateField
open scoped Matrix

/- Schur's argument can be specialized to orthogonal matrices here. The linear
part is faithful on a periodic isometry subgroup because the translation kernel
has no torsion. Finite generation supplies a finitely generated coefficient
field, which bounds the possible roots of unity among eigenvalues. This makes
the traces finite; the positive trace pairing then makes the matrix image finite. -/

/-- Step 1 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"viewed as a subgroup of the affine group". We use the orthogonal linear
part; its translation kernel will be trivial on a periodic subgroup. -/
private def schur_locally_finite_step1_rotation {d : ℕ} :
    Iso d →* Matrix (Fin d) (Fin d) ℝ :=
  (LinearMap.toMatrixAlgEquiv (EuclideanSpace.basisFun (Fin d) ℝ).toBasis).toMonoidHom.comp
    { toFun := fun g => g.linear.toLinearMap
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/-- Step 1 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"a periodic linear group". The matrix of the inverse linear isometry is
the transpose, in the standard orthonormal basis. -/
private theorem schur_locally_finite_step1_transpose {d : ℕ} (g : Iso d) :
    (schur_locally_finite_step1_rotation g)ᵀ =
      schur_locally_finite_step1_rotation g⁻¹ := by
  change (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis g.linearIsometryEquiv.toLinearMap)ᵀ = _
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [← LinearMap.toMatrix_adjoint, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
  rfl

/-- Step 1 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"Every element ... has finite order". A translation of finite order is
the identity, since a real vector space has no nonzero additive torsion. -/
private theorem schur_locally_finite_step1_translation {d : ℕ} (g : Iso d)
    (hg : IsOfFinOrder g) (hrot : schur_locally_finite_step1_rotation g = 1) : g = 1 := by
  have hlinear : g.linear.toLinearMap = LinearMap.id := by
    apply (LinearMap.toMatrixAlgEquiv (EuclideanSpace.basisFun (Fin d) ℝ).toBasis).injective
    simpa only [LinearMap.toMatrixAlgEquiv_id] using hrot
  have happly (x : E d) : g x = x + g 0 := by
    have hx : g.linear x = x := congrArg (fun f : E d →ₗ[ℝ] E d => f x) hlinear
    have h := g.toAffineEquiv.map_vadd (0 : E d) x
    change g (x + 0) = g.linear x + g 0 at h
    rwa [add_zero, hx] at h
  have hpow (n : ℕ) (x : E d) : (g ^ n) x = x + n • g 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', AffineIsometryEquiv.coe_mul, Function.comp_apply, happly, ih,
        succ_nsmul]
      abel
  obtain ⟨n, hn, hgn⟩ := hg.exists_pow_eq_one
  have hz : n • g 0 = 0 := by
    simpa [hgn] using (hpow n 0).symm
  have hz' : (n : ℝ) • g 0 = 0 := by simpa only [Nat.cast_smul_eq_nsmul] using hz
  have hzero : g 0 = 0 := (smul_eq_zero.mp hz').resolve_left (Nat.cast_ne_zero.mpr hn.ne')
  apply AffineIsometryEquiv.ext
  intro x
  change g x = x
  rw [happly, hzero, add_zero]

/-- Step 1 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"a periodic linear group". The linear-part representation is faithful
on a periodic subgroup: equal linear parts have a torsion translation as quotient. -/
private theorem schur_locally_finite_step1_faithful {d : ℕ} (G : Subgroup (Iso d))
    (hperiodic : ∀ g : G, IsOfFinOrder (g.val : Iso d)) :
    Set.InjOn schur_locally_finite_step1_rotation (G : Set (Iso d)) := by
  intro g hg h hh he
  have hrot : schur_locally_finite_step1_rotation (g⁻¹ * h) = 1 := by
    rw [map_mul, ← he, ← map_mul, inv_mul_cancel, map_one]
  have hid := schur_locally_finite_step1_translation (g⁻¹ * h)
    (hperiodic ⟨g⁻¹ * h, G.mul_mem (G.inv_mem hg) hh⟩) hrot
  exact inv_mul_eq_one.mp hid

/-- Step 2 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"every finitely generated periodic linear group". Finitely many generator
entries generate a field over ℚ containing every matrix entry; inversion is transpose. -/
private theorem schur_locally_finite_step2_coefficients
    {Γ : Type*} [Group Γ] {n : ℕ} (ρ : Γ →* Matrix (Fin n) (Fin n) ℝ)
    (htranspose : ∀ g, (ρ g)ᵀ = ρ g⁻¹) (F : Finset Γ) :
    ∃ K : IntermediateField ℚ ℂ, K.FG ∧
      ∀ g ∈ Subgroup.closure (F : Set Γ), ∀ i j, (ρ g i j : ℂ) ∈ K := by
  let s : Set ℂ := Set.range (fun p : F × Fin n × Fin n => (ρ p.1.val p.2.1 p.2.2 : ℂ))
  let K := IntermediateField.adjoin ℚ s
  refine ⟨K, IntermediateField.fg_adjoin_of_finite (Set.finite_range _), ?_⟩
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    intro i j
    exact IntermediateField.subset_adjoin ℚ s ⟨(⟨g, hg⟩, i, j), rfl⟩
  | one =>
    intro i j
    simp only [map_one, Matrix.one_apply]
    split_ifs <;> simp
  | mul g h _ _ hg hh =>
    intro i j
    rw [map_mul, Matrix.mul_apply, Complex.ofReal_sum]
    exact K.sum_mem (fun k _ => by simpa only [Complex.ofReal_mul] using K.mul_mem (hg i k) (hh k j))
  | inv g _ hg =>
    intro i j
    rw [← htranspose]
    exact hg j i

/-- Step 3 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"By Schur's theorem". In the field-theoretic degree bound, adjoining
an algebraic element costs at most the degree of that finite field extension. -/
private theorem schur_locally_finite_step3_finite_extension
    {F K E : Type*} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]
    [Module.Finite F K] (z : E) (hz : IsAlgebraic F z) :
    (minpoly F z).natDegree ≤ Module.finrank F K * (minpoly K z).natDegree := by
  let L := IntermediateField.adjoin K ({z} : Set E)
  haveI : Module.Finite K L := IntermediateField.adjoin.finiteDimensional hz.isIntegral.tower_top
  haveI : Module.Finite F L := Module.Finite.trans K L
  have h := minpoly.natDegree_le (K := F) (AdjoinSimple.gen K z)
  rw [← minpoly.algHom_eq (L.val.restrictScalars F) Subtype.val_injective] at h
  change (minpoly F z).natDegree ≤ Module.finrank F L at h
  rw [← Module.finrank_mul_finrank F K L,
    IntermediateField.adjoin.finrank hz.isIntegral.tower_top] at h
  exact h

/-- Step 3 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"By Schur's theorem". Adjoining a transcendental element preserves the
degree of an algebraic element: Gauss's lemma preserves its irreducible minimal
polynomial over the rational function field. -/
private theorem schur_locally_finite_step3_transcendental_extension
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (t z : E) (ht : Transcendental K t) (hz : IsAlgebraic K z) :
    (minpoly (IntermediateField.adjoin K ({t} : Set E)) z).natDegree =
      (minpoly K z).natDegree := by
  let i : RatFunc K →ₐ[K] E := IsFractionRing.liftAlgHom
    (K := RatFunc K) (transcendental_iff_injective.mp ht)
  have hi : i.fieldRange = IntermediateField.adjoin K ({t} : Set E) := by
    exact IsFractionRing.liftAlgHom_fieldRange_eq_of_range_eq
      (transcendental_iff_injective.mp ht)
      (Algebra.adjoin_singleton_eq_range_aeval K t).symm
  let e : RatFunc K ≃ₐ[K] IntermediateField.adjoin K ({t} : Set E) :=
    (AlgEquiv.ofInjectiveField i).trans (IntermediateField.equivOfEq hi)
  let q := minpoly K z
  have hq : q.Monic := minpoly.monic hz.isIntegral
  have hirr : Irreducible q := minpoly.irreducible hz.isIntegral
  have hC : Irreducible (q.map (Polynomial.C : K →+* K[X])) := by
    rw [← Polynomial.Bivariate.swap_C, MulEquiv.irreducible_iff]
    exact (Polynomial.prime_C_iff.mpr hirr.prime).irreducible
  have hrat : Irreducible (q.map (algebraMap K (RatFunc K))) := by
    have h := (hq.map (Polynomial.C : K →+* K[X])).irreducible_iff_irreducible_map_fraction_map
      (K := RatFunc K) |>.mp hC
    simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K K[X] (RatFunc K),
      Polynomial.algebraMap_eq] using h
  have hadjoin : Irreducible (q.map (algebraMap K (IntermediateField.adjoin K ({t} : Set E)))) := by
    have h : Irreducible (Polynomial.mapEquiv e.toRingEquiv
        (q.map (algebraMap K (RatFunc K)))) := by
      rwa [MulEquiv.irreducible_iff]
    have hmap : Polynomial.mapEquiv e.toRingEquiv (q.map (algebraMap K (RatFunc K))) =
        q.map (algebraMap K (IntermediateField.adjoin K ({t} : Set E))) := by
      apply Polynomial.ext
      intro j
      simp only [Polynomial.mapEquiv_apply, Polynomial.coeff_map]
      exact e.commutes (q.coeff j)
    rwa [hmap] at h
  have heq : q.map (algebraMap K (IntermediateField.adjoin K ({t} : Set E))) =
      minpoly (IntermediateField.adjoin K ({t} : Set E)) z := by
    apply minpoly.eq_of_irreducible_of_monic hadjoin
    · simp only [Polynomial.aeval_map_algebraMap, q, minpoly.aeval]
    · exact hq.map _
  rw [← heq, Polynomial.natDegree_map]

/-- Step 3 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"By Schur's theorem". For a finitely generated field K/ℚ, rational
algebraic degrees are bounded by a fixed multiple of degrees over K. Induction
on the field generators separates algebraic and transcendental adjunctions. -/
private theorem schur_locally_finite_step3_degree_bound
    (K : IntermediateField ℚ ℂ) (hK : K.FG) :
    ∃ N : ℕ, ∀ z : ℂ, IsAlgebraic ℚ z →
      (minpoly ℚ z).natDegree ≤ N * (minpoly K z).natDegree := by
  apply IntermediateField.induction_on_adjoin_fg
    (P := fun K : IntermediateField ℚ ℂ => ∃ N : ℕ, ∀ z : ℂ, IsAlgebraic ℚ z →
      (minpoly ℚ z).natDegree ≤ N * (minpoly K z).natDegree) ?_ ?_ K hK
  · refine ⟨1, ?_⟩
    intro z hz
    have hs : Function.Surjective (algebraMap ℚ (⊥ : IntermediateField ℚ ℂ)) := by
      intro x
      obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp x.property
      exact ⟨r, Subtype.ext hr⟩
    have hm := minpoly.map_algebraMap (E := (⊥ : IntermediateField ℚ ℂ)) hz.isIntegral
      ((Polynomial.mem_lifts _).mpr (Polynomial.map_surjective _ hs (minpoly _ z)))
    rw [one_mul, ← hm, Polynomial.natDegree_map]
  · intro L x hL
    obtain ⟨N, hN⟩ := hL
    by_cases hx : IsAlgebraic L x
    · haveI : Module.Finite L (IntermediateField.adjoin L ({x} : Set ℂ)) :=
        IntermediateField.adjoin.finiteDimensional hx.isIntegral
      refine ⟨N * Module.finrank L (IntermediateField.adjoin L ({x} : Set ℂ)), ?_⟩
      intro z hz
      calc
        (minpoly ℚ z).natDegree ≤ N * (minpoly L z).natDegree := hN z hz
        _ ≤ N * (Module.finrank L (IntermediateField.adjoin L ({x} : Set ℂ)) *
            (minpoly (IntermediateField.adjoin L ({x} : Set ℂ)) z).natDegree) :=
          Nat.mul_le_mul_left N (schur_locally_finite_step3_finite_extension
            (K := IntermediateField.adjoin L ({x} : Set ℂ)) z (hz.tower_top L))
        _ = _ := by rw [Nat.mul_assoc]; rfl
    · refine ⟨N, ?_⟩
      intro z hz
      change (minpoly ℚ z).natDegree ≤ N *
        (minpoly (IntermediateField.adjoin L ({x} : Set ℂ)) z).natDegree
      rw [schur_locally_finite_step3_transcendental_extension x z hx (hz.tower_top L)]
      exact hN z hz

/-- Step 4 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"a periodic linear group". Only finitely many complex roots of unity
have bounded rational degree: their cyclotomic polynomials have bounded degree
and Mahler measure one, so polynomial Northcott finiteness applies. -/
private theorem schur_locally_finite_step4_rational_roots (N : ℕ) :
    {z : ℂ | IsOfFinOrder z ∧ (minpoly ℚ z).natDegree ≤ N}.Finite := by
  let P : Set ℤ[X] := {p | p.natDegree ≤ N ∧
    (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ (1 : ℝ)}
  have hP : P.Finite := Polynomial.finite_mahlerMeasure_le N 1
  have hf : (⋃ p ∈ P, p.rootSet ℂ).Finite :=
    hP.biUnion (fun p _ => p.rootSet_finite ℂ)
  apply hf.subset
  intro z hz
  let m := orderOf z
  have hm : 0 < m := hz.1.orderOf_pos
  have hprim : IsPrimitiveRoot z m := IsPrimitiveRoot.orderOf z
  refine Set.mem_iUnion₂.mpr ⟨Polynomial.cyclotomic m ℤ, ?_, ?_⟩
  · constructor
    · simpa only [← Polynomial.cyclotomic_eq_minpoly_rat hprim hm,
        Polynomial.natDegree_cyclotomic] using hz.2
    · exact (Polynomial.cyclotomic_mahlerMeasure_eq_one (R := ℤ) m).le
  · rw [Polynomial.mem_rootSet_of_ne (Polynomial.cyclotomic.monic m ℤ).ne_zero]
    simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic, Polynomial.IsRoot.def] using hprim.isRoot_cyclotomic hm

/-- Step 4 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"By Schur's theorem". The degree comparison reduces roots of unity of
bounded degree over the coefficient field to bounded rational degree. -/
private theorem schur_locally_finite_step4_field_roots
    (K : IntermediateField ℚ ℂ) (hK : K.FG) (n : ℕ) :
    {z : ℂ | IsOfFinOrder z ∧ (minpoly K z).natDegree ≤ n}.Finite := by
  obtain ⟨N, hN⟩ := schur_locally_finite_step3_degree_bound K hK
  apply (schur_locally_finite_step4_rational_roots (N * n)).subset
  intro z hz
  refine ⟨hz.1, (hN z ?_).trans (Nat.mul_le_mul_left N hz.2)⟩
  exact ((IsPrimitiveRoot.orderOf z).isIntegral hz.1.orderOf_pos).tower_top.isAlgebraic

/-- Step 5 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"a periodic linear group". An eigenvalue of a torsion n-by-n matrix is
a root of unity and satisfies its degree-n characteristic polynomial. This
also handles n = 0, when the characteristic polynomial has no roots. -/
private theorem schur_locally_finite_step5_matrix_roots
    (K : IntermediateField ℚ ℂ) {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hA : IsOfFinOrder A) {z : ℂ} (hz : z ∈ (A.map K.val).charpoly.roots) :
    IsOfFinOrder z ∧ (minpoly K z).natDegree ≤ n := by
  have hroot : (A.map K.val).charpoly.IsRoot z :=
    (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hz
  have heval : aeval z A.charpoly = 0 := by
    simpa only [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      ← Matrix.charpoly_map] using hroot
  constructor
  · cases n with
    | zero => simp at hz
    | succ n =>
      obtain ⟨m, hm, hpow⟩ := hA.exists_pow_eq_one
      have hpow' : (A.map K.val) ^ m = 1 := by
        simpa only [map_pow, map_one] using congrArg K.val.toRingHom.mapMatrix hpow
      have h := spectrum.pow_mem_pow (A.map K.val) m
        (Matrix.mem_spectrum_of_isRoot_charpoly hroot)
      rw [hpow', spectrum.one_eq, Set.mem_singleton_iff] at h
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, h⟩
  · simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using
      Polynomial.natDegree_le_natDegree (minpoly.min K z A.charpoly_monic heval)

/-- Step 6 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"By Schur's theorem". Sums of a fixed number of elements of a finite
set form a finite set, including the empty sum. -/
private theorem schur_locally_finite_step6_finite_sums
    (s : Set ℂ) (hs : s.Finite) (n : ℕ) :
    {z : ℂ | ∃ t : Multiset ℂ, t.card = n ∧ (∀ x ∈ t, x ∈ s) ∧ t.sum = z}.Finite := by
  classical
  induction n with
  | zero =>
    apply (Set.finite_singleton 0).subset
    rintro z ⟨t, ht, _, rfl⟩
    simp_all
  | succ n ih =>
    apply (hs.add ih).subset
    rintro z ⟨t, ht, hts, rfl⟩
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < t.card)
    obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hx
    exact ⟨x, hts x (by simp), u.sum,
      ⟨u, by simpa using ht, fun y hy => hts y (by simp [hy]), rfl⟩, by simp⟩

/-- Step 6 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"every finitely generated periodic linear group is finite". Traces
of torsion matrices over the coefficient field are sums of n eigenvalues from
one finite set, hence take only finitely many values. -/
private theorem schur_locally_finite_step6_matrix_traces
    (K : IntermediateField ℚ ℂ) (hK : K.FG) (n : ℕ) :
    {z : ℂ | ∃ A : Matrix (Fin n) (Fin n) K,
      IsOfFinOrder A ∧ Matrix.trace (A.map K.val) = z}.Finite := by
  let s : Set ℂ := {z | IsOfFinOrder z ∧ (minpoly K z).natDegree ≤ n}
  apply (schur_locally_finite_step6_finite_sums s
    (schur_locally_finite_step4_field_roots K hK n) n).subset
  rintro z ⟨A, hA, rfl⟩
  refine ⟨(A.map K.val).charpoly.roots, ?_, ?_, ?_⟩
  · rw [← (IsAlgClosed.splits (A.map K.val).charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  · intro z hz
    exact schur_locally_finite_step5_matrix_roots K A hA hz
  · exact (Matrix.trace_eq_sum_roots_charpoly _).symm

/-- Step 6 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"viewed as a subgroup ... of GL". Lift the real matrices to their
complex coefficient field and transport finiteness of traces back to ℝ. -/
private theorem schur_locally_finite_step6_real_traces
    {Γ : Type*} [Group Γ] {n : ℕ} (ρ : Γ →* Matrix (Fin n) (Fin n) ℝ)
    (K : IntermediateField ℚ ℂ) (hK : K.FG)
    (hcoeff : ∀ g i j, (ρ g i j : ℂ) ∈ K)
    (hperiodic : ∀ g, IsOfFinOrder (ρ g)) :
    (Set.range fun g => Matrix.trace (ρ g)).Finite := by
  have hc : (Set.range fun g => ((Matrix.trace (ρ g) : ℝ) : ℂ)).Finite := by
    apply (schur_locally_finite_step6_matrix_traces K hK n).subset
    rintro z ⟨g, rfl⟩
    let A : Matrix (Fin n) (Fin n) K := fun i j => ⟨(ρ g i j : ℂ), hcoeff g i j⟩
    have he : A.map K.val = (ρ g).map Complex.ofRealHom := rfl
    refine ⟨A, ?_, ?_⟩
    · apply (Matrix.map_injective K.val.injective).isOfFinOrder_iff.mp
        (show IsOfFinOrder (K.val.toRingHom.mapMatrix A) from ?_)
      change IsOfFinOrder (A.map K.val)
      rw [he]
      exact Complex.ofRealHom.mapMatrix.toMonoidHom.isOfFinOrder (hperiodic g)
    · rw [he, ← AddMonoidHom.map_trace]
      rfl
  apply Set.Finite.of_finite_image (f := Complex.ofReal) ?_ Complex.ofReal_injective.injOn
  rw [← Set.range_comp]
  exact hc

/-- Step 7 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"By Schur's theorem". The trace pairings against a finite spanning
set distinguish real matrices in the span: the pairing of their difference
with itself is the sum of the squares of its entries. -/
private theorem schur_locally_finite_step7_trace_separates {n : ℕ}
    (s : Set (Matrix (Fin n) (Fin n) ℝ))
    (t : Finset (Matrix (Fin n) (Fin n) ℝ))
    (ht : Submodule.span ℝ (t : Set _) = Submodule.span ℝ s)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ s) (hB : B ∈ s)
    (he : ∀ C ∈ t, Matrix.trace (A * Cᵀ) = Matrix.trace (B * Cᵀ)) : A = B := by
  have hall (C : Matrix (Fin n) (Fin n) ℝ) (hC : C ∈ Submodule.span ℝ s) :
      Matrix.trace (A * Cᵀ) = Matrix.trace (B * Cᵀ) := by
    rw [← ht] at hC
    induction hC using Submodule.span_induction with
    | mem C hC => exact he C hC
    | zero => simp
    | add C D _ _ hC hD => simp [Matrix.transpose_add, Matrix.mul_add, hC, hD]
    | smul r C _ hC => simp [Matrix.transpose_smul, hC]
  have hzero : Matrix.trace ((A - B) * (A - B)ᵀ) = 0 := by
    rw [Matrix.sub_mul, Matrix.trace_sub,
      hall (A - B) (Submodule.sub_mem _ (Submodule.subset_span hA) (Submodule.subset_span hB)),
      sub_self]
  have hsum : ∑ i, ∑ j, (A i j - B i j) ^ 2 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two] using hzero
  have hrow (i : Fin n) : ∑ j, (A i j - B i j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))).mp
      hsum i (Finset.mem_univ _)
  ext i j
  have hentry : (A i j - B i j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)).mp
      (hrow i) j (Finset.mem_univ _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hentry)

/-- Step 7 of the V4 proof of `schur_locally_finite` (V4 5.7, Step 4(ii)):
"every finitely generated periodic linear group is finite". For an
orthogonal representation with finitely many traces, pairings against finitely
many spanning matrices give an injection into a finite product. -/
private theorem schur_locally_finite_step7_finite_image {Γ : Type*} [Group Γ] {n : ℕ}
    (ρ : Γ →* Matrix (Fin n) (Fin n) ℝ)
    (htranspose : ∀ g, (ρ g)ᵀ = ρ g⁻¹)
    (htrace : (Set.range fun g => Matrix.trace (ρ g)).Finite) :
    (Set.range ρ).Finite := by
  classical
  obtain ⟨t, hts, _, hspan, _⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℝ (Set.range ρ)
  let f : Matrix (Fin n) (Fin n) ℝ → (t → ℝ) := fun A C => Matrix.trace (A * C.valᵀ)
  apply Set.Finite.of_injOn (t := {v : t → ℝ | ∀ C, v C ∈ Set.range (fun g => Matrix.trace (ρ g))})
    (f := f)
  · rintro _ ⟨g, rfl⟩ C
    obtain ⟨h, hh⟩ := hts C.property
    refine ⟨g * h⁻¹, ?_⟩
    change Matrix.trace (ρ (g * h⁻¹)) = Matrix.trace (ρ g * C.valᵀ)
    rw [map_mul, ← hh, htranspose]
  · intro A hA B hB he
    apply schur_locally_finite_step7_trace_separates (Set.range ρ) t hspan hA hB
    intro C hC
    exact congrFun he ⟨C, hC⟩
  · exact Set.Finite.pi' (fun _ => htrace)

/-- Y1, V4 5.7, Step 4(ii), Schur: a periodic Euclidean isometry group is locally
finite. Its faithful affine matrix representation has dimension d+1; no
orientation, bounded-orbit or finite-generation hypothesis on the whole group is used. -/
theorem schur_locally_finite (G : Subgroup (Iso d))
    (hperiodic : ∀ g : G, IsOfFinOrder (g.val : Iso d)) : IsLocallyFiniteGroup G := by
  intro F hF
  let H := Subgroup.closure (F : Set (Iso d))
  have hHG : H ≤ G := (Subgroup.closure_le G).mpr hF
  let ρ := schur_locally_finite_step1_rotation (d := d)
  obtain ⟨K, hK, hcoeff⟩ := schur_locally_finite_step2_coefficients ρ
    schur_locally_finite_step1_transpose F
  let ψ : H →* Matrix (Fin d) (Fin d) ℝ := ρ.comp H.subtype
  have htrace := schur_locally_finite_step6_real_traces ψ K hK
    (fun g => hcoeff g.val g.property)
    (fun g => ρ.isOfFinOrder (hperiodic ⟨g.val, hHG g.property⟩))
  have himage := schur_locally_finite_step7_finite_image ψ
    (fun g => schur_locally_finite_step1_transpose g.val) htrace
  have hinj : Function.Injective ψ := by
    intro g h he
    exact Subtype.ext (schur_locally_finite_step1_faithful G hperiodic
      (hHG g.property) (hHG h.property) he)
  haveI : Finite H := (Set.finite_range_iff hinj).mp himage
  exact Set.toFinite (H : Set (Iso d))

end Schur

/-- V4 5.7, Step 4(iii) (affine glue): the linear part of an isometry maps
differences of points to differences of images. -/
private lemma locally_finite_fixed_point_linear_sub (f : Iso d) (x y : E d) :
    f.toAffineEquiv.toAffineMap.linear (x - y) = f x - f y := by
  have := AffineMap.linearMap_vsub f.toAffineEquiv.toAffineMap x y
  simpa [vsub_eq_sub] using this

/-- V4 5.7, Step 4(iii): "Each finite isometry group G_i fixes a point (the
barycentre of any orbit)" -- here the barycentre of the orbit of 0. -/
private lemma locally_finite_fixed_point_finite_fixed (H : Subgroup (Iso d))
    (hH : (H : Set (Iso d)).Finite) : ∃ c : E d, ∀ h ∈ H, h c = c := by
  classical
  haveI : Finite H := hH.to_subtype
  letI : Fintype H := Fintype.ofFinite H
  refine ⟨(Fintype.card H : ℝ)⁻¹ • ∑ h : H, h.val 0, fun g hg => ?_⟩
  set L := g.toAffineEquiv.toAffineMap.linear
  have hdec : ∀ x : E d, g x = L x + g 0 := by
    intro x
    have := locally_finite_fixed_point_linear_sub g x 0
    rw [sub_zero] at this
    rw [this]; abel
  have hcard : (Fintype.card H : ℝ) ≠ 0 := by
    have : 0 < Fintype.card H := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsum : ∑ h : H, g (h.val 0) = ∑ h : H, h.val 0 := by
    have := Equiv.sum_comp (Equiv.mulLeft (⟨g, hg⟩ : H)) (fun h : H => h.val 0)
    rw [← this]
    rfl
  rw [hdec, map_smul, map_sum]
  have h2 : ∑ h : H, g (h.val 0) = ∑ h : H, L (h.val 0) + (Fintype.card H : ℝ) • g 0 := by
    rw [Finset.sum_congr rfl (fun h _ => hdec (h.val 0)), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [← hsum, h2, smul_add, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- Y1, V4 5.7, Step 4(iii): a countable locally finite Euclidean isometry group
has a common fixed point. Finite subgroup barycentres give nested nonempty affine
fixed spaces, which stabilize in finite dimension. -/
theorem locally_finite_fixed_point (G : Subgroup (Iso d)) [Countable G]
    (hlocal : IsLocallyFiniteGroup G) :
    ∃ c : E d, ∀ g : G, g.val c = c := by
  -- Stabilization of the fixed spaces: choose a finite generating set whose
  -- common linear fixed space has minimal dimension.
  classical
  let D : Finset (Iso d) → Submodule ℝ (E d) := fun F =>
    ⨅ f ∈ F, LinearMap.ker (f.toAffineEquiv.toAffineMap.linear - LinearMap.id)
  have hmemD : ∀ F x, x ∈ D F ↔ ∀ f ∈ F, f.toAffineEquiv.toAffineMap.linear x = x := by
    intro F x
    simp [D, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]
  have hex : ∃ n, ∃ F : Finset (Iso d), (F : Set (Iso d)) ⊆ G ∧
      Module.finrank ℝ (D F) = n := ⟨_, ∅, by simp, rfl⟩
  obtain ⟨F, hFG, hFmin⟩ := Nat.find_spec hex
  obtain ⟨c, hc⟩ := locally_finite_fixed_point_finite_fixed (Subgroup.closure (F : Set (Iso d))) (hlocal F hFG)
  refine ⟨c, fun g => ?_⟩
  set F' := insert g.val F
  have hF'G : (F' : Set (Iso d)) ⊆ G := by
    simp only [F', Finset.coe_insert, Set.insert_subset_iff]
    exact ⟨g.property, hFG⟩
  obtain ⟨c', hc'⟩ := locally_finite_fixed_point_finite_fixed (Subgroup.closure (F' : Set (Iso d))) (hlocal F' hF'G)
  have hle : D F' ≤ D F := by
    intro x hx
    rw [hmemD] at hx ⊢
    exact fun f hf => hx f (Finset.mem_insert_of_mem hf)
  have heq : D F' = D F := by
    apply Submodule.eq_of_le_of_finrank_le hle
    by_contra h
    push_neg at h
    exact Nat.find_min hex (hFmin ▸ h) ⟨F', hF'G, rfl⟩
  have hmem : c - c' ∈ D F := by
    rw [hmemD]
    intro f hf
    rw [locally_finite_fixed_point_linear_sub, hc f (Subgroup.subset_closure hf),
      hc' f (Subgroup.subset_closure (Finset.mem_insert_of_mem hf))]
  rw [← heq, hmemD] at hmem
  have h1 := hmem g.val (Finset.mem_insert_self _ _)
  rw [locally_finite_fixed_point_linear_sub, hc' g.val (Subgroup.subset_closure (Finset.mem_insert_self _ _))] at h1
  simpa using h1

/-- Y1, V4 5.7, Step 4(iii): all symmetries of a proper output fix one point.
The point is obtained from the periodic-group and countability arguments, not
assumed as an additional constraint on the tiling. -/
theorem common_fixed_point (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    ∃ c : E d, ∀ g : Iso d, Y.IsSymmetry g → g c = c := by
  letI := symmetry_countable Y
  obtain ⟨c, hc⟩ := locally_finite_fixed_point Y.symmetryGroup
    (schur_locally_finite Y.symmetryGroup (fun g => periodic Y hY g.val g.property))
  exact ⟨c, fun g hg => hc ⟨g, hg⟩⟩

/-- Y1, V4 5.7, Step 4(i),(iv): the symmetry stabilizer of any fixed point is finite.
The marked tile frame isolates the identity; the point stabilizer in the full
Euclidean group is compact. This holds even without properness. -/
theorem point_stabilizer_finite (Y : MarkedTiling (systemM S P C)) (c : E d) :
    {g : Iso d | Y.IsSymmetry g ∧ g c = c}.Finite := by
  sorry

end Symmetry

/-- Y1, V4 5.7: the full Euclidean symmetry group of every proper marked output
is finite, including reflections. Symmetries preserve both physical tiles and
markings. This conclusion uses the C1 system alone and no fitting construction. -/
theorem symmetry_finite (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    Y.symmetries.Finite := by
  obtain ⟨c, hc⟩ := Symmetry.common_fixed_point Y hY
  exact (Symmetry.point_stabilizer_finite Y c).subset (fun g hg => ⟨hg, hc g hg⟩)

/-- Y1, V4 5.7: finiteness of the symmetry group implies finite order of each
symmetry. This is also available for arbitrary enforcement data in Main.lean. -/
theorem symmetry_finite_order (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Iso d) (hg : Y.IsSymmetry g) : IsOfFinOrder g := by
  letI : Fintype Y.symmetryGroup := (symmetry_finite Y hY).fintype
  exact Y.symmetryGroup.subtype.isOfFinOrder
    (isOfFinOrder_of_finite (⟨g, hg⟩ : Y.symmetryGroup))

end Enforce
