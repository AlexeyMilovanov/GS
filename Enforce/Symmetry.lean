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

/-- Y1, V4 5.7, Step 2: a positive power of any symmetry fixes a ground component.
Compact recurrence of its orthogonal part produces intersecting solid cones;
translations of the cone apices do not affect the large-distance intersection. -/
theorem power_fixes_component (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Iso d) (hg : Y.IsSymmetry g) (q : (parsedHierarchy Y hY).Node)
    (hq : q.1 = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ (g ^ k) '' component Y hY q = component Y hY q := by
  sorry

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
  sorry

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

/-- Y1, V4 5.7, Step 4(ii), Schur: a periodic Euclidean isometry group is locally
finite. Its faithful affine matrix representation has dimension d+1; no
orientation, bounded-orbit or finite-generation hypothesis on the whole group is used. -/
theorem schur_locally_finite (G : Subgroup (Iso d))
    (hperiodic : ∀ g : G, IsOfFinOrder (g.val : Iso d)) : IsLocallyFiniteGroup G := by
  sorry

/-- Y1, V4 5.7, Step 4(iii): a countable locally finite Euclidean isometry group
has a common fixed point. Finite subgroup barycentres give nested nonempty affine
fixed spaces, which stabilize in finite dimension. -/
theorem locally_finite_fixed_point (G : Subgroup (Iso d)) [Countable G]
    (hlocal : IsLocallyFiniteGroup G) :
    ∃ c : E d, ∀ g : G, g.val c = c := by
  sorry

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
