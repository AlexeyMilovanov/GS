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
  sorry

/-- P9, V4 1.14: incident native tiles, with their unambiguous addresses. -/
abbrev Incident (p : E d) (n : ℕ) :=
  {a : P.Address n // (S.σ ^ n) p ∈ (P.native n a).carrier 0}

/-- P9, V4 1.14: the geometric child relation between consecutive inflated levels.
Containment in `σ t` determines the actual substitution parent. -/
def IncidentChild (p : E d) (n : ℕ) (a : P.Incident p n)
    (b : P.Incident p (n + 1)) : Prop :=
  (P.native (n + 1) b.val).carrier 0 ⊆ S.σ '' (P.native n a.val).carrier 0

/-- P9, V4 1.14: every incident native tile has a unique incident parent.
The original address prevents identifying distinct occurrences by a chosen frame. -/
theorem incident_parent_exists_unique (p : E d) (n : ℕ)
    (b : P.Incident p (n + 1)) :
    ∃! a : P.Incident p n, P.IncidentChild p n a b := by
  sorry

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

/-- P9, V4 1.14: bounded width, no dying branches, and eventual unique children.
DEVIATION: the exact minimum-angle constant uses the nonempty catalogue, as in D3. -/
theorem incidentForest [Nonempty S.ι] (p : E d) :
    (∀ n, Finite (P.Incident p n) ∧
      Nat.card (P.Incident p n) ≤ multiplicityBound S.proto S.cx) ∧
    (∀ n (a : P.Incident p n),
      ∃ b : P.Incident p (n + 1), P.IncidentChild p n a b) ∧
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ a : P.Incident p n,
      ∃! b : P.Incident p (n + 1), P.IncidentChild p n a b := by
  sorry

/-- P9, V4 1.14: beyond a splitting cutoff, tails are in bijection with the
incident tiles there, so there are at most `M₀` infinite tails.
DEVIATION: the exact `M₀` requires the nonempty angle catalogue, as in D3. -/
theorem incident_tails [Nonempty S.ι] (p : E d) :
    ∃ N : ℕ, Function.Bijective (fun t : P.IncidentTail p N => t.node 0) ∧
      Finite (P.IncidentTail p N) ∧
      Nat.card (P.IncidentTail p N) ≤ multiplicityBound S.proto S.cx := by
  sorry

/-- P9/P5, V4 1.14, 1.5(b): common-listed points in the original patch. -/
def CommonListed (p : E d) : Prop :=
  ∀ t ∈ P.tiles, p ∈ t.carrier 0 → t.Lists 0 p

/-- P9, V4 1.14: listedness persists across every incident child step. -/
theorem incident_listed_step (p : E d) (n : ℕ) (a : P.Incident p n)
    (b : P.Incident p (n + 1)) (hab : P.IncidentChild p n a b)
    (ha : (P.native n a.val).Lists 0 ((S.σ ^ n) p)) :
    (P.native (n + 1) b.val).Lists 0 ((S.σ ^ (n + 1)) p) := by
  sorry

/-- P9/P5, V4 1.14, 1.5(b): a common-listed point is listed at every depth. -/
theorem incident_commonListed (p : E d) (hp : P.CommonListed p)
    (n : ℕ) (a : P.Incident p n) : (P.native n a.val).Lists 0 ((S.σ ^ n) p) := by
  sorry

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

/-- P10, V4 1.15: a power admits the prescribed factorisation.
DEVIATION: `Nonempty S.ι` is explicit because stage 1 allows an empty catalogue.
V4's proof chooses a prototile and vertex; without any tiles an arbitrary expansion
need not have a positive-spectrum power modulo the trivial compatible group. -/
theorem power_factorisation (S : SubstSystem d) [Nonempty S.ι] :
    Nonempty (PowerFactorisation S) := by
  sorry

/-- P11, V4 1.16(a): the positive factor centralizes the full compatible group. -/
theorem L_commutes (F : PowerFactorisation S) (h : Ortho d) (hh : h ∈ S.rotGroup) :
    F.L * h.toLinearEquiv = h.toLinearEquiv * F.L := by
  sorry

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
  sorry

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
  sorry

/-- P11, V4 1.16(b'): tangent cones of listed cells of compatible ground tiles
at their listed vertices are `HΠ`-cones. This includes all lower dimensions. -/
theorem tangentCone_isHPiCone (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (C : CellName S t.ty)
    (p : E d) (hp : t.Lists 0 p) (hpC : p ∈ t.cell 0 C.val) :
    HPiCone S.hPi (tangentCone (t.cell 0 C.val) p) := by
  sorry

/-- P11, V4 1.16(b'): cones of finite unions of compatible cells at a listed
anchor are `HΠ`-cones, as are full tile cones at listed vertices. -/
theorem tangentCone_tile_isHPiCone (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (p : E d) (hp : t.Lists 0 p) :
    HPiCone S.hPi (tangentCone (t.carrier 0) p) := by
  sorry

/-- P11, V4 1.16(c): the factors commute. -/
theorem RL_commute (F : PowerFactorisation S) :
    F.R.toLinearEquiv * F.L = F.L * F.R.toLinearEquiv := by
  sorry

/-- P11, V4 1.16(c): power decomposition and compatible residual rotations. -/
theorem power_cone_formula (F : PowerFactorisation S) (a r : ℕ) (hr : r < F.power) :
    S.σ ^ (a * F.power + r) = S.σ ^ r * F.R.toLinearEquiv ^ a * F.L ^ a ∧
      ∃ Q ∈ S.rotGroup, Q.toLinearEquiv =
        linearConj S.σ (r : ℤ) (F.R.toLinearEquiv ^ a) ∧
        ∀ K : Set (E d), HPiCone S.hPi K →
          (S.σ ^ (a * F.power + r)) '' K = Q '' ((S.σ ^ r) '' K) := by
  sorry

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

/-- P12, V4 1.17: finite actual header tuples over all listing incident tiles.
No common-listed hypothesis is needed: only tiles listing the anchor contribute. -/
theorem header_finiteness (p : E d) {s : ℕ} (G : Fin s → Set (E d))
    (hG : ∀ j, HPiCone S.hPi (G j)) : (P.headers p G).Finite := by
  sorry

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

/-- P13, V4 1.18: finitely many full positioned stars, with an arbitrary finite
label alphabet. This includes the unlabelled case by taking `Y = Unit`. -/
theorem positioned_stars_finite (Y : Type) [Finite Y] (p : E d)
    (hp : P.CommonListed p) : (P.positionedStars Y p).Finite := by
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
  sorry

end CompatiblePatch

/-- P11, V4 1.16(b): the cone language is closed under arbitrary finite unions. -/
theorem HPiCone_finite_union {α : Type} [Finite α] (K : α → Set (E d))
    (hK : ∀ a, HPiCone S.hPi (K a)) : HPiCone S.hPi (⋃ a, K a) := by
  sorry

/-- P11, V4 1.16(b): the cone language is closed under arbitrary finite intersections. -/
theorem HPiCone_finite_inter {α : Type} [Finite α] (K : α → Set (E d))
    (hK : ∀ a, HPiCone S.hPi (K a)) : HPiCone S.hPi (⋂ a, K a) := by
  sorry

/-- P11, V4 1.16(b'): the tangent cone of a finite union of compatible listed
cells at a common listed anchor remains an `HΠ`-cone, in all dimensions. -/
theorem tangentCone_union_isHPiCone (P : CompatiblePatch S)
    (Q : Finset (Σ t : {t // t ∈ P.tiles}, CellName S t.val.ty)) (p : E d)
    (hlisted : ∀ q ∈ Q, q.1.val.Lists 0 p)
    (hcontains : ∀ q ∈ Q, p ∈ q.1.val.cell 0 q.2.val) :
    HPiCone S.hPi (tangentCone (⋃ q ∈ Q, q.1.val.cell 0 q.2.val) p) := by
  sorry

/-- P14, V4 1.19: a single prototype-catalogue radius works for every placed
ground tile at every listed vertex, independently of patches and their depth.
An empty catalogue admits any positive radius. -/
theorem uniform_prototype_cone_radius (S : SubstSystem d) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (t : FramedNode S) (p : E d), t.Lists 0 p →
      t.carrier 0 ∩ ball p r₀ =
        ((fun v => p + v) '' tangentCone (t.carrier 0) p) ∩ ball p r₀ := by
  sorry

namespace CompatiblePatch

variable (P : CompatiblePatch S)

/-- P9, V4 1.14: the native subdivision has no repeated framed tile occurrences. -/
theorem native_injective (n : ℕ) : Function.Injective (P.native n) := by
  sorry

/-- P9, V4 1.14: all native tiles have disjoint interiors, with no side-to-side
hypothesis, and they cover exactly the ambient expansion of the original patch. -/
theorem native_subdivision (n : ℕ) :
    Pairwise (fun a b : P.Address n => Disjoint
      (interior ((P.native n a).carrier 0)) (interior ((P.native n b).carrier 0))) ∧
      (⋃ a : P.Address n, (P.native n a).carrier 0) =
        (S.σ ^ n) '' (⋃ t ∈ P.tiles, t.carrier 0) := by
  sorry

/-- P9, V4 1.14: the number of incident tiles never decreases with depth. -/
theorem incident_width_monotone (p : E d) (n : ℕ) :
    Nat.card (P.Incident p n) ≤ Nat.card (P.Incident p (n + 1)) := by
  sorry

/-- P12, V4 1.17: every incident tile listing the anchor contributes its full
header, with the actual named vertex. This supplies witnesses to the header set. -/
theorem header_occurs (p : E d) {s : ℕ} (G : Fin s → Set (E d)) (n : ℕ)
    (a : P.Incident p n)
    (v : {e // e ∈ (S.cx (P.native n a.val).ty).vertices})
    (hv : (S.σ ^ n) p ∈ (P.native n a.val).cell 0 v.val) :
    (⟨(P.native n a.val).ty, v,
      fun j => (P.native n a.val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ n) '' G j)⟩ : Header S s) ∈ P.headers p G := by
  sorry

end CompatiblePatch

end Enforce
