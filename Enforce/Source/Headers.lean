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
